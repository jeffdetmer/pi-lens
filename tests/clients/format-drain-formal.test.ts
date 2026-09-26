/**
 * Replays of the `formal/format-drain` counterexamples (#3527, #3528, #3529)
 * against the real deferred drain: `handleAgentEnd`, `runFormatPhase`, the
 * real `FormatService` and `formatters.formatFile` (contentBefore, spawn,
 * contentAfter), `holdFileMutationQueue` over pi's real
 * `withFileMutationQueue`, `RuntimeCoordinator`, `ReadGuard`, `CacheManager`,
 * and for the LSP cases the real `LSPService` notify queue down to a mock
 * connection. Doubled: the formatter PROCESS (`safeSpawnAsync`), the
 * formatter selection, the LSP server registry and client construction.
 *
 * No wall clock: every interleaving is pinned with a gate that a double
 * opens or waits on, and the hook bounds run under fake timers. Each case
 * names the TLC config whose trace it replays.
 */
import * as fs from "node:fs";
import * as path from "node:path";
// pi's real per-file queue, the one its `edit`/`write` tools run under.
import { withFileMutationQueue } from "@earendil-works/pi-coding-agent";
import { afterEach, beforeEach, describe, expect, it, vi } from "vitest";
import type { BiomeClient } from "../../clients/biome-client.js";
import { CacheManager } from "../../clients/cache-manager.js";
import {
	getDegradationSummary,
	resetDegradationLedger,
} from "../../clients/degradation-ledger.js";
import { setHostFileMutationQueueLoader } from "../../clients/file-mutation-queue.js";
import { FormatService } from "../../clients/format-service.js";
import { HOOK_WALL_BUDGET_MS } from "../../clients/hook-budgets.js";
import * as clientModule from "../../clients/lsp/client.js";
import {
	getLSPService,
	LSPService,
	resetLSPService,
} from "../../clients/lsp/index.js";
import { handleAgentEnd } from "../../clients/runtime-agent-end.js";
import { RuntimeCoordinator } from "../../clients/runtime-coordinator.js";
import { setAmbientAbortSignal } from "../../clients/safe-spawn.js";
import { waitFor } from "./interleaving-kit.js";
import { createMockState } from "./lsp/mock-client-state.js";
import { setupTestEnvironment } from "./test-utils.js";

function gate() {
	let open!: () => void;
	const p = new Promise<void>((resolve) => {
		open = resolve;
	});
	return { p, open };
}

/**
 * The in-place formatter child, at the process boundary formatters.ts
 * `formatFile` spawns through: it reads F, parks, and writes its format of
 * what it READ, whatever the drain decided meanwhile (the `--write` shape).
 * No case holds a spawned child past its 15 s spawn timeout, so the kill is
 * not modelled.
 */
const child = vi.hoisted(() => ({
	command: "format-drain-child",
	resolving: undefined as undefined | (() => void),
	resolved: undefined as undefined | Promise<void>,
	spawned: undefined as undefined | (() => void),
	read: undefined as undefined | Promise<void>,
	didRead: undefined as undefined | (() => void),
	write: undefined as undefined | Promise<void>,
	wrote: undefined as undefined | (() => void),
	removeAfterWrite: false,
}));

vi.mock("../../clients/safe-spawn.js", async (importOriginal) => {
	const actual =
		await importOriginal<typeof import("../../clients/safe-spawn.js")>();
	return {
		...actual,
		safeSpawnAsync: async (
			command: string,
			args: string[],
			options?: Parameters<typeof actual.safeSpawnAsync>[2],
		) => {
			if (command !== child.command)
				return actual.safeSpawnAsync(command, args, options);
			const file = args[0] as string;
			child.spawned?.();
			await child.read;
			const content = fs.readFileSync(file, "utf8");
			child.didRead?.();
			await child.write;
			fs.writeFileSync(file, content.replace(/[ \t]*=[ \t]*/g, " = "));
			if (child.removeAfterWrite) fs.rmSync(file);
			child.wrote?.();
			return { stdout: "", stderr: "", status: 0 };
		},
	};
});

// The formatter selection: one formatter whose command is the child above.
// Its command resolution can park (`child.resolved`), the #3558 shape.
vi.mock("../../clients/formatters-lazy.js", async (importOriginal) => {
	const actual =
		await importOriginal<typeof import("../../clients/formatters-lazy.js")>();
	return {
		...actual,
		loadFormatters: async () => {
			const real = await actual.loadFormatters();
			const formatter = {
				name: "prettier",
				command: [child.command],
				extensions: [".ts"],
				detect: async () => true,
				resolveCommand: async (fp: string) => {
					child.resolving?.();
					await child.resolved;
					return [child.command, fp];
				},
			};
			return { ...real, getFormattersForFile: async () => [formatter] };
		},
	};
});

// The LSP half: the REAL LSPService and notify queue over a mock connection
// (the harness of tests/clients/lsp/notify-read-order.test.ts). The drain's
// touches pass through a gate: `drainTouch` lets a case order the drain's
// resync after the next edit's own sync, and `drainTouchesWaiting` says when
// the drain's touch has been issued.
const lsp = vi.hoisted(() => ({
	service: undefined as unknown,
	drainTouch: Promise.resolve() as Promise<void>,
	drainTouchesWaiting: 0,
	/** Serve the drain the real `getLSPService()` singleton instead of the gate. */
	realService: undefined as undefined | (() => unknown),
	getServersForFileWithConfig: vi.fn(),
	createLSPClient: vi.fn(),
}));
vi.mock("../../clients/lsp/config.js", async (importOriginal) => ({
	...(await importOriginal<typeof import("../../clients/lsp/config.js")>()),
	getServersForFileWithConfig: lsp.getServersForFileWithConfig,
	getServerInitOverride: vi.fn().mockReturnValue(undefined),
}));
vi.mock("../../clients/lsp/client.js", async (importOriginal) => ({
	...(await importOriginal<typeof import("../../clients/lsp/client.js")>()),
	createLSPClient: lsp.createLSPClient,
}));
const { logLatency } = vi.hoisted(() => ({ logLatency: vi.fn() }));
vi.mock("../../clients/latency-logger.js", async (importOriginal) => ({
	...(await importOriginal<typeof import("../../clients/latency-logger.js")>()),
	logLatency,
}));
// `resyncLspFile` reaches the service through the lazy seam
// (clients/lsp-lazy.ts); measured on this branch, a mock of `lsp/index.js`
// does not reach that dynamic import, which then serves a second, real
// service instance.
vi.mock("../../clients/lsp-lazy.js", async (importOriginal) => {
	const actual =
		await importOriginal<typeof import("../../clients/lsp-lazy.js")>();
	const { makeLspServiceDouble } =
		await import("../support/lsp-service-double.js");
	return {
		...actual,
		loadLspService: async () => ({
			...(await actual.loadLspService()),
			getLSPService: () => {
				if (lsp.realService) return lsp.realService() as LSPService;
				const service = lsp.service as LSPService;
				return makeLspServiceDouble({
					supportsLSP: (fp: string) => service.supportsLSP(fp),
					touchFile: async (...args: Parameters<LSPService["touchFile"]>) => {
						lsp.drainTouchesWaiting++;
						await lsp.drainTouch;
						return service.touchFile(...args);
					},
				}) as unknown as LSPService;
			},
		}),
	};
});

let env: ReturnType<typeof setupTestEnvironment>;
let runtime: RuntimeCoordinator;
let filePath: string;
let notices: string[];
let flags: Set<string>;
let cacheManager: CacheManager;

/** Arms the child's gates; each step is open unless the case parks it. */
function armChild(parked: { read?: boolean; write?: boolean } = {}) {
	const spawned = gate();
	const read = gate();
	const didRead = gate();
	const write = gate();
	const wrote = gate();
	child.spawned = spawned.open;
	child.read = read.p;
	child.didRead = didRead.open;
	child.write = write.p;
	child.wrote = wrote.open;
	if (!parked.read) read.open();
	if (!parked.write) write.open();
	return {
		spawned: spawned.p,
		didRead: didRead.p,
		wrote: wrote.p,
		openRead: read.open,
		openWrite: write.open,
	};
}

function drainDeps(
	over: Partial<Parameters<typeof handleAgentEnd>[0]> = {},
): Parameters<typeof handleAgentEnd>[0] {
	return {
		ctxCwd: env.tmpDir,
		getFlag: (name: string) => flags.has(name),
		notify: (msg: string) => notices.push(msg),
		dbg: () => {},
		runtime,
		cacheManager,
		getFormatService: () => new FormatService("format-drain", true),
		...over,
	} as Parameters<typeof handleAgentEnd>[0];
}

/**
 * The next run's edit, the way pi's edit tool runs it: a read-modify-write
 * inside pi's mutation queue. `sync` also sends the edit's own pipeline
 * sync to the LSP, stamped before its read (#3481).
 */
function agentAppend(line: string, sync?: LSPService) {
	let wrote = false;
	const done = withFileMutationQueue(filePath, async () => {
		const readStamp = performance.now();
		const content = `${fs.readFileSync(filePath, "utf8")}${line}`;
		fs.writeFileSync(filePath, content);
		wrote = true;
		return { content, readStamp };
	}).then(async ({ content, readStamp }) => {
		await sync?.touchFile(filePath, content, {
			diagnostics: "none",
			source: "test",
			readStamp,
		});
	});
	return { done, wrote: () => wrote };
}

/**
 * Resolves once every queue call made before it has registered: pi chains
 * registrations through one module-wide promise, so a call on another path
 * registers after them. An earlier call whose file is free has run by then.
 */
function afterQueueRegistration(): Promise<void> {
	return withFileMutationQueue(
		path.join(env.tmpDir, "registration-barrier"),
		async () => {},
	);
}

/** An edit of F with no read this session: what the read guard decides. */
function blindEditVerdict(): string | undefined {
	// Take #3520's mtime fallback out of play: F predates session 2.
	const old = new Date(Date.now() - 3_600_000);
	fs.utimesSync(filePath, old, old);
	return (runtime.readGuard.checkEdit(filePath, [1, 1]) as { action?: string })
		.action;
}

/** The drain's post-exit resync records (latency.log). */
const postExitRows = () =>
	logLatency.mock.calls
		.map(([row]) => row as { phase?: string; metadata?: unknown })
		.filter((row) => row.phase === "deferred_format_post_exit_resync");
const tick = () => new Promise<void>((resolve) => setImmediate(resolve));

/**
 * A case whose bound gave up on the phase waits for the drain's detached
 * post-exit task to settle, so its ledger and latency rows cannot land in
 * the next case.
 */
function postExitSettled() {
	return waitFor(postExitRows, (rows) => rows.length > 0, {
		yieldControl: tick,
		timeoutMs: 2_000,
	});
}

function staleWriteSubjects(): string[] {
	return getDegradationSummary()
		.filter((group) => group.kind === "generation-guard-stale-write")
		.flatMap((group) => group.latestReasons.map((r) => r.subject));
}

beforeEach(() => {
	logLatency.mockClear();
	setHostFileMutationQueueLoader(async () => ({ withFileMutationQueue }));
	setAmbientAbortSignal(undefined);
	resetDegradationLedger();
	notices = [];
	flags = new Set(["no-lsp"]);
	child.resolving = undefined;
	child.resolved = undefined;
	child.removeAfterWrite = false;
	env = setupTestEnvironment("pi-lens-format-drain-");
	// Project evidence for the "prettier" tool agreement (tool-agreement.ts).
	fs.writeFileSync(
		path.join(env.tmpDir, "package.json"),
		JSON.stringify({ devDependencies: { prettier: "3.3.3" } }),
	);
	fs.writeFileSync(
		path.join(env.tmpDir, "package-lock.json"),
		JSON.stringify({
			packages: { "node_modules/prettier": { version: "3.3.3" } },
		}),
	);
	runtime = new RuntimeCoordinator();
	runtime.projectRoot = env.tmpDir;
	cacheManager = new CacheManager(false);
	filePath = path.join(env.tmpDir, "f.ts");
	fs.writeFileSync(filePath, "const x=1\n");
	runtime.deferMutation(filePath, env.tmpDir, "edit", env.tmpDir, "format");
});

afterEach(() => {
	vi.useRealTimers();
	setHostFileMutationQueueLoader(undefined);
	env.cleanup();
});

describe("#3527: the drain's format runs inside pi's mutation queue", () => {
	it("OverlapLostEdit (#3527): a next-run edit made after the child read F waits for the child, so the format does not erase it", async () => {
		const c = armChild({ write: true });
		const drain = handleAgentEnd(drainDeps());
		await c.didRead;
		const agent = agentAppend("const y=2\n");
		await afterQueueRegistration();
		expect(agent.wrote()).toBe(false);
		c.openWrite();
		const summary = await drain;
		await agent.done;
		expect(fs.readFileSync(filePath, "utf8")).toBe("const x = 1\nconst y=2\n");
		expect(summary?.changed).toEqual([filePath]);
	});

	it("OverlapClaim (#3527): a next-run edit never lands inside the drain's before/after window, so what it reports as its format is formatting only", async () => {
		const c = armChild({ read: true });
		const drain = handleAgentEnd(drainDeps());
		// contentBefore is read before the spawn.
		await c.spawned;
		const agent = agentAppend("const y=2\n");
		await afterQueueRegistration();
		expect(agent.wrote()).toBe(false);
		c.openRead();
		const summary = await drain;
		await agent.done;
		// The agent's line is outside the claimed diff: the child never
		// formatted it, and the drain's claim is its own format of line 1.
		expect(fs.readFileSync(filePath, "utf8")).toBe("const x = 1\nconst y=2\n");
		expect(summary?.changed).toEqual([filePath]);
		expect(notices).toEqual([
			"pi-lens deferred format applied to 1 file(s): f.ts",
		]);
	});

	it("OrphanLostEdit (#3527): the child the hook's 10 s bound gave up on keeps pi's queue until it writes", async () => {
		vi.useFakeTimers({ toFake: ["setTimeout", "clearTimeout"] });
		const c = armChild({ write: true });
		const drain = handleAgentEnd(drainDeps());
		await c.didRead;
		await vi.advanceTimersByTimeAsync(HOOK_WALL_BUDGET_MS.agent_settled + 1);
		// The hook returned: an interactive pi now takes the next prompt.
		const summary = await drain;
		expect(summary?.failed).toEqual([
			{
				filePath,
				errors: ["deferred formatter exceeded agent_settled budget"],
			},
		]);
		const agent = agentAppend("const y=2\n");
		await afterQueueRegistration();
		expect(agent.wrote()).toBe(false);
		c.openWrite();
		await agent.done;
		expect(fs.readFileSync(filePath, "utf8")).toBe("const x = 1\nconst y=2\n");
		await postExitSettled();
	});
});

describe("#3528: a drain that outlives its session writes nothing into the next", () => {
	it("Straddle (#3528): a session-1 drain's recordWritten does not admit a never-read session-2 edit", async () => {
		flags.add("lens-turn-summary");
		const addModifiedRange = vi.spyOn(cacheManager, "addModifiedRange");
		const c = armChild({ write: true });
		const drain = handleAgentEnd(drainDeps());
		await c.didRead;
		// `/new` in the editor while the drain awaits its formatter.
		runtime.resetForSession(Date.now());
		c.openWrite();
		const summary = await drain;
		// The format itself ran: the file is the project's, not the session's.
		expect(summary?.changed).toEqual([filePath]);
		expect(fs.readFileSync(filePath, "utf8")).toBe("const x = 1\n");
		expect(blindEditVerdict()).toBe("block");
		expect(runtime.getFileSeq(filePath)).toBe(0);
		expect(runtime.projectSeq).toBe(0);
		expect(addModifiedRange).not.toHaveBeenCalled();
		expect(runtime.turnSummary.peek()).toEqual([]);
		expect(staleWriteSubjects()).toEqual([`runtime-session:${filePath}`]);
	});

	it("StraddleState (#3528): an abandoned session-1 format is not requeued into session 2's cleared queue", async () => {
		vi.useFakeTimers({ toFake: ["setTimeout", "clearTimeout"] });
		const c = armChild({ write: true });
		const drain = handleAgentEnd(drainDeps());
		await c.didRead;
		runtime.resetForSession(Date.now());
		expect(runtime.pendingDeferredMutationCount).toBe(0);
		await vi.advanceTimersByTimeAsync(HOOK_WALL_BUDGET_MS.agent_settled + 1);
		await drain;
		expect(runtime.pendingDeferredMutationCount).toBe(0);
		expect(staleWriteSubjects()).toEqual([`runtime-session:${filePath}`]);
		c.openWrite();
		await c.wrote;
		await postExitSettled();
		expect(postExitRows()).toEqual([
			expect.objectContaining({ metadata: { outcome: "stale-session" } }),
		]);
	});

	it("StraddleAutofix (#3528): the drain's autofix bookkeeping does not land in session 2", async () => {
		const { fixer, parked, resume } = gatedBiome();
		writeBiomeAgreement();
		runtime.deferMutation(filePath, env.tmpDir, "edit", env.tmpDir, "autofix");
		flags.add("no-autoformat");
		const addModifiedRange = vi.spyOn(cacheManager, "addModifiedRange");
		const drain = handleAgentEnd(
			drainDeps({ biomeClient: fixer, ruffClient: noRuff }),
		);
		await parked.p;
		runtime.resetForSession(Date.now());
		resume.open();
		await drain;
		expect(fs.readFileSync(filePath, "utf8")).toBe("let x=1\n");
		expect(blindEditVerdict()).toBe("block");
		expect(runtime.getFileSeq(filePath)).toBe(0);
		expect(addModifiedRange).not.toHaveBeenCalled();
		expect(staleWriteSubjects()).toEqual([`runtime-session:${filePath}`]);
	});

	describe("a drain whose session was replaced starts no new in-place write (#3528 r1 F1)", () => {
		// FormatDrain FixNoStartGen: the old drain's write could not be synced to
		// the next session's LSP document (its resync is skipped), so it must not
		// start one.
		it("the format phase does not start after /new during the autofix phase", async () => {
			const { fixer, parked, resume } = gatedBiome();
			writeBiomeAgreement();
			runtime.deferMutation(
				filePath,
				env.tmpDir,
				"edit",
				env.tmpDir,
				"autofix",
			);
			let spawned = false;
			armChild();
			child.spawned = () => {
				spawned = true;
			};
			const drain = handleAgentEnd(
				drainDeps({ biomeClient: fixer, ruffClient: noRuff }),
			);
			await parked.p;
			runtime.resetForSession(Date.now());
			resume.open();
			await drain;
			expect(spawned).toBe(false);
			expect(fs.readFileSync(filePath, "utf8")).toBe("let x=1\n");
			expect(staleWriteSubjects()).toContain(`runtime-session:${filePath}`);
		});

		it("every claimed file it did not start is named in summary.skipped (#3528 r2)", async () => {
			const { fixer, parked, resume } = gatedBiome();
			writeBiomeAgreement();
			runtime.deferMutation(
				filePath,
				env.tmpDir,
				"edit",
				env.tmpDir,
				"autofix",
			);
			const formatOnly = ["b.ts", "c.ts", "d.ts", "e.ts"].map((name) => {
				const fp = path.join(env.tmpDir, name);
				fs.writeFileSync(fp, "const z=3\n");
				runtime.deferMutation(fp, env.tmpDir, "edit", env.tmpDir, "format");
				return fp;
			});
			// Its own project, so Biome's project scope does not dedupe it.
			const otherRoot = path.join(env.tmpDir, "other");
			fs.mkdirSync(otherRoot);
			writeBiomeAgreement(otherRoot);
			const bothKinds = path.join(otherRoot, "g.ts");
			fs.writeFileSync(bothKinds, "const y=2\n");
			runtime.deferMutation(bothKinds, otherRoot, "edit", otherRoot, "autofix");
			// Both kinds, neither started: named once, not by each loop.
			runtime.deferMutation(bothKinds, otherRoot, "edit", otherRoot, "format");
			// Autofix only, in a third project: only the autofix loop can name it.
			const thirdRoot = path.join(env.tmpDir, "third");
			fs.mkdirSync(thirdRoot);
			writeBiomeAgreement(thirdRoot);
			const autofixOnly = path.join(thirdRoot, "h.ts");
			fs.writeFileSync(autofixOnly, "const w=4\n");
			runtime.deferMutation(
				autofixOnly,
				thirdRoot,
				"edit",
				thirdRoot,
				"autofix",
			);
			const drain = handleAgentEnd(
				drainDeps({ biomeClient: fixer, ruffClient: noRuff }),
			);
			await parked.p;
			runtime.resetForSession(Date.now());
			resume.open();
			const summary = await drain;
			// f.ts: its autofix ran, its format was never started. g.ts: neither
			// its autofix nor its format was started. h.ts: its autofix was never
			// started. b-e.ts: never formatted.
			expect(
				summary?.skipped
					.filter((entry) => entry.reason === "session-replaced")
					.map((entry) => path.basename(entry.filePath))
					.sort(),
			).toEqual(["b.ts", "c.ts", "d.ts", "e.ts", "f.ts", "g.ts", "h.ts"]);
			for (const fp of formatOnly)
				expect(fs.readFileSync(fp, "utf8")).toBe("const z=3\n");
		});

		it("the autofix loop does not start the next file after /new", async () => {
			const { fixer, parked, resume } = gatedBiome();
			const fixFileAsync = vi.spyOn(
				fixer as unknown as { fixFileAsync: () => unknown },
				"fixFileAsync",
			);
			writeBiomeAgreement();
			flags.add("no-autoformat");
			// Its own project: Biome's fix scope is the project, so a second file
			// of the same project would be deduped rather than started.
			const otherRoot = path.join(env.tmpDir, "other");
			fs.mkdirSync(otherRoot);
			writeBiomeAgreement(otherRoot);
			const second = path.join(otherRoot, "g.ts");
			fs.writeFileSync(second, "const y=2\n");
			runtime.deferMutation(
				filePath,
				env.tmpDir,
				"edit",
				env.tmpDir,
				"autofix",
			);
			runtime.deferMutation(second, otherRoot, "edit", otherRoot, "autofix");
			const drain = handleAgentEnd(
				drainDeps({ biomeClient: fixer, ruffClient: noRuff }),
			);
			await parked.p;
			runtime.resetForSession(Date.now());
			resume.open();
			await drain;
			expect(fixFileAsync).toHaveBeenCalledTimes(1);
			expect(fs.readFileSync(second, "utf8")).toBe("const y=2\n");
		});
	});

	describe("no-drop (#3528, shape 54): a drain that stays in its session still records", () => {
		it("the format's recordWritten, change log, modified range and turn summary land in its own session", async () => {
			flags.add("lens-turn-summary");
			const addModifiedRange = vi.spyOn(cacheManager, "addModifiedRange");
			armChild();
			const summary = await handleAgentEnd(drainDeps());
			expect(summary?.changed).toEqual([filePath]);
			expect(blindEditVerdict()).toBe("allow");
			expect(runtime.getFileSeq(filePath)).toBe(1);
			expect(addModifiedRange).toHaveBeenCalledTimes(1);
			expect(runtime.turnSummary.peek()).toEqual([
				expect.objectContaining({
					filePath,
					events: [{ kind: "format", tool: "prettier" }],
				}),
			]);
			expect(staleWriteSubjects()).toEqual([]);
		});

		it("an abandoned format is requeued in its own session", async () => {
			vi.useFakeTimers({ toFake: ["setTimeout", "clearTimeout"] });
			const c = armChild({ write: true });
			const drain = handleAgentEnd(drainDeps());
			await c.didRead;
			await vi.advanceTimersByTimeAsync(HOOK_WALL_BUDGET_MS.agent_settled + 1);
			await drain;
			expect(runtime.pendingDeferredMutationCount).toBe(1);
			c.openWrite();
			await c.wrote;
			await postExitSettled();
		});

		it("the autofix's recordWritten, change log and modified range land in its own session", async () => {
			const { fixer, resume } = gatedBiome();
			resume.open();
			writeBiomeAgreement();
			runtime.deferMutation(
				filePath,
				env.tmpDir,
				"edit",
				env.tmpDir,
				"autofix",
			);
			flags.add("no-autoformat");
			const addModifiedRange = vi.spyOn(cacheManager, "addModifiedRange");
			await handleAgentEnd(
				drainDeps({ biomeClient: fixer, ruffClient: noRuff }),
			);
			expect(blindEditVerdict()).toBe("allow");
			expect(runtime.getFileSeq(filePath)).toBe(1);
			expect(addModifiedRange).toHaveBeenCalledTimes(1);
		});
	});
});

/** The Biome agreement evidence the autofix gate needs, and a biome.json. */
function writeBiomeAgreement(root = env.tmpDir): void {
	fs.writeFileSync(
		path.join(root, "package.json"),
		JSON.stringify({
			devDependencies: { "@biomejs/biome": "^2.4.10", prettier: "3.3.3" },
		}),
	);
	fs.writeFileSync(
		path.join(root, "package-lock.json"),
		JSON.stringify({
			lockfileVersion: 3,
			packages: {
				"": {},
				"node_modules/@biomejs/biome": { version: "2.4.10" },
				"node_modules/prettier": { version: "3.3.3" },
			},
		}),
	);
	fs.writeFileSync(path.join(root, "biome.json"), "{}\n");
}

const noRuff = {
	isPythonFile: () => false,
	ensureAvailable: async () => false,
} as never;

/**
 * A `BiomeClient.fixFileAsync` double with the real one's shape
 * (biome-client.ts): read, let `lint --write` rewrite what it read, read it
 * back, report a fix only when the bytes moved. Parks between read and write.
 */
function gatedBiome() {
	const parked = gate();
	const resume = gate();
	const fixer = {
		isSupportedFile: () => true,
		ensureAvailable: async () => true,
		fixFileAsync: async (fp: string) => {
			const before = fs.readFileSync(fp, "utf8");
			parked.open();
			await resume.p;
			fs.writeFileSync(fp, before.replace("const ", "let "));
			const after = fs.readFileSync(fp, "utf8");
			return {
				success: true,
				changed: before !== after,
				fixed: before !== after ? 1 : 0,
			};
		},
	} as unknown as BiomeClient;
	return { fixer, parked, resume };
}

describe("#3529: the drain's LSP sync ends on the bytes on disk", () => {
	/** didOpen/didChange texts the server received, in order. */
	let wire: string[];
	let service: LSPService;

	beforeEach(async () => {
		flags.delete("no-lsp");
		wire = [];
		const state = createMockState({
			root: env.tmpDir,
			serverId: "typescript",
		});
		vi.mocked(state.connection.sendNotification).mockImplementation(
			async (method: unknown, params: unknown) => {
				const m = String(method).replace("textDocument/", "");
				if (m !== "didOpen" && m !== "didChange") return;
				const p = params as {
					textDocument?: { text?: string };
					contentChanges?: Array<{ text: string }>;
				};
				wire.push(
					p?.textDocument?.text ?? p?.contentChanges?.at(-1)?.text ?? "",
				);
			},
		);
		const client = {
			serverId: "typescript",
			root: env.tmpDir,
			customServer: false,
			isAlive: () => true,
			shutdown: async () => {},
			getWorkspaceDiagnosticsSupport: () => ({
				advertised: false,
				mode: "push-only" as const,
				diagnosticProviderKind: "none",
			}),
			getOperationSupport: () => ({}),
			getAdvertisedCommands: () => [],
			getRawCapabilityKeys: () => [],
			getLaunchVariant: () => undefined,
			diagnosticsVersion: 0,
			getDiagnosticsVersionForPath: vi.fn(() => 0),
			getDiagnostics: vi.fn(() => []),
			getAllDiagnostics: vi.fn(() => new Map()),
			getDiagnosticBinding: vi.fn(() => undefined),
			notify: {
				open: (
					fp: string,
					content: string,
					languageId: string,
					preserveDiagnostics?: boolean,
					silent?: boolean,
					saved?: boolean,
					readStamp?: number,
				) =>
					clientModule.handleNotifyOpen(
						state,
						fp,
						content,
						languageId,
						preserveDiagnostics,
						silent,
						saved,
						readStamp,
					),
				change: vi.fn(async () => {}),
				close: vi.fn(async () => {}),
			},
			pingLiveness: vi.fn().mockResolvedValue(true),
			waitForDiagnostics: vi.fn(async () => {}),
		};
		lsp.getServersForFileWithConfig.mockReturnValue([
			{
				id: "typescript",
				name: "typescript",
				extensions: [".ts"],
				root: async () => env.tmpDir,
				spawn: vi.fn(async () => ({ process: {}, source: "test" })),
			},
		]);
		lsp.createLSPClient.mockResolvedValue(client);
		service = new LSPService();
		lsp.service = service;
		lsp.drainTouch = Promise.resolve();
		lsp.drainTouchesWaiting = 0;
		lsp.realService = undefined;
		// The queued edit's own pipeline sync of the unformatted bytes.
		await service.touchFile(filePath, "const x=1\n", {
			diagnostics: "none",
			source: "test",
			readStamp: performance.now(),
		});
	});

	afterEach(() => {
		if (lsp.realService) resetLSPService({ reason: "session_shutdown" });
		lsp.realService = undefined;
		lsp.getServersForFileWithConfig.mockReset();
		lsp.createLSPClient.mockReset();
	});

	const disk = () => fs.readFileSync(filePath, "utf8");
	/** The drain's post-exit resync records (latency.log). */

	it("OverlapLsp (#3529): the drain's resync of bytes read before a next-run edit does not replace that edit's newer sync", async () => {
		const drainTouch = gate();
		lsp.drainTouch = drainTouch.p;
		const c = armChild({ write: true });
		const drain = handleAgentEnd(drainDeps());
		await c.didRead;
		const agent = agentAppend("const y=2\n", service);
		c.openWrite();
		// The drain read its fileContent inside the hold; the edit lands when
		// the hold is released, and its own sync goes out first.
		await agent.done;
		drainTouch.open();
		await drain;
		expect(disk()).toBe("const x = 1\nconst y=2\n");
		expect(wire.at(-1)).toBe(disk());
	});

	it("OverlapLsp (#3529): the drain's autofix resync of bytes read before a next-run edit does not replace that edit's newer sync", async () => {
		const drainTouch = gate();
		lsp.drainTouch = drainTouch.p;
		const { fixer, resume } = gatedBiome();
		resume.open();
		writeBiomeAgreement();
		runtime.deferMutation(filePath, env.tmpDir, "edit", env.tmpDir, "autofix");
		flags.add("no-autoformat");
		const drain = handleAgentEnd(
			drainDeps({ biomeClient: fixer, ruffClient: noRuff }),
		);
		// The drain has read the fixed bytes and issued its resync.
		await waitFor(
			() => lsp.drainTouchesWaiting,
			(waiting) => waiting === 1,
			{ yieldControl: tick, timeoutMs: 2_000 },
		);
		const agent = agentAppend("const y=2\n", service);
		await agent.done;
		drainTouch.open();
		await drain;
		expect(disk()).toBe("let x=1\nconst y=2\n");
		expect(wire.at(-1)).toBe(disk());
	});

	it("no-drop (#3529, shape 54): with no newer edit, the drain's stamped autofix resync still sends its fixed bytes", async () => {
		const { fixer, resume } = gatedBiome();
		resume.open();
		writeBiomeAgreement();
		runtime.deferMutation(filePath, env.tmpDir, "edit", env.tmpDir, "autofix");
		flags.add("no-autoformat");
		await handleAgentEnd(drainDeps({ biomeClient: fixer, ruffClient: noRuff }));
		expect(disk()).toBe("let x=1\n");
		expect(wire.at(-1)).toBe(disk());
	});

	it("no-drop (#3529, shape 54): with no newer edit, the drain's stamped resync still sends its formatted bytes", async () => {
		armChild();
		await handleAgentEnd(drainDeps());
		expect(disk()).toBe("const x = 1\n");
		expect(wire.at(-1)).toBe(disk());
		// A phase that settled inside the bound needs no post-exit resync.
		expect(postExitRows()).toEqual([]);
	});

	it("OrphanLsp (#3529): the child the hook's 10 s bound gave up on is synced after it writes", async () => {
		vi.useFakeTimers({ toFake: ["setTimeout", "clearTimeout"] });
		const c = armChild({ write: true });
		const drain = handleAgentEnd(drainDeps());
		await c.didRead;
		await vi.advanceTimersByTimeAsync(HOOK_WALL_BUDGET_MS.agent_settled + 1);
		await drain;
		expect(wire.at(-1)).toBe("const x=1\n");
		c.openWrite();
		await c.wrote;
		await waitFor(
			() => wire.at(-1),
			(last) => last === "const x = 1\n",
			{ yieldControl: tick, timeoutMs: 2_000 },
		);
		expect(disk()).toBe("const x = 1\n");
		expect(postExitRows()).toEqual([
			expect.objectContaining({
				filePath,
				metadata: expect.objectContaining({ outcome: "synced" }),
			}),
		]);
	});

	it("OrphanLsp (#3529): the child the writer's own 30 s aggregate gave up on is synced after it writes, not before", async () => {
		vi.useFakeTimers({ toFake: ["setTimeout", "clearTimeout"] });
		const resolving = gate();
		const resolution = gate();
		child.resolving = resolving.open;
		child.resolved = resolution.p;
		const c = armChild();
		const drain = handleAgentEnd(drainDeps());
		// The service's own bound is armed once the formatter run starts (the
		// hold's queue entry is real I/O); both bounds then give up while the
		// command resolution is in flight.
		await resolving.p;
		await vi.advanceTimersByTimeAsync(30_000);
		await drain;
		resolution.open();
		await c.wrote;
		await waitFor(
			() => wire.at(-1),
			(last) => last === "const x = 1\n",
			{ yieldControl: tick, timeoutMs: 2_000 },
		);
		expect(disk()).toBe("const x = 1\n");
		expect(postExitRows()).toEqual([
			expect.objectContaining({
				filePath,
				metadata: expect.objectContaining({ outcome: "synced" }),
			}),
		]);
	});

	it("OrphanLsp (#3529): the post-exit resync of a read taken before a next-run edit does not replace that edit's newer sync", async () => {
		vi.useFakeTimers({ toFake: ["setTimeout", "clearTimeout"] });
		const drainTouch = gate();
		lsp.drainTouch = drainTouch.p;
		const c = armChild({ write: true });
		const drain = handleAgentEnd(drainDeps());
		await c.didRead;
		await vi.advanceTimersByTimeAsync(HOOK_WALL_BUDGET_MS.agent_settled + 1);
		await drain;
		// Another queued mutation of F holds the queue past the child's exit,
		// so the post-exit read is taken before the next-run edit lands.
		const other = gate();
		const holder = withFileMutationQueue(filePath, () => other.p);
		const agent = agentAppend("const y=2\n", service);
		c.openWrite();
		await waitFor(
			() => lsp.drainTouchesWaiting,
			(waiting) => waiting === 1,
			{ yieldControl: tick, timeoutMs: 2_000 },
		);
		other.open();
		await holder;
		await agent.done;
		drainTouch.open();
		await waitFor(postExitRows, (rows) => rows.length > 0, {
			yieldControl: tick,
			timeoutMs: 2_000,
		});
		expect(disk()).toBe("const x = 1\nconst y=2\n");
		expect(wire.at(-1)).toBe(disk());
		// #3528 r2: the queue dropped the older read, so the row does not say synced.
		expect(postExitRows()).toEqual([
			expect.objectContaining({ metadata: { outcome: "superseded" } }),
		]);
	});

	it("the post-exit row says not-sent when the language server could not start (#3528 r2)", async () => {
		vi.useFakeTimers({ toFake: ["setTimeout", "clearTimeout"] });
		lsp.realService = getLSPService;
		resetLSPService({ reason: "session_shutdown" });
		lsp.createLSPClient.mockRejectedValue(new Error("spawn failed"));
		const c = armChild({ write: true });
		const drain = handleAgentEnd(drainDeps());
		await c.didRead;
		await vi.advanceTimersByTimeAsync(HOOK_WALL_BUDGET_MS.agent_settled + 1);
		await drain;
		c.openWrite();
		await c.wrote;
		await postExitSettled();
		expect(postExitRows()).toEqual([
			expect.objectContaining({ metadata: { outcome: "not-sent" } }),
		]);
	});

	describe("a drain whose session was replaced touches no language server (#3528 r1 F1)", () => {
		/**
		 * `/new` or quit while the drain runs: session_start / session_shutdown
		 * bump the generation and retire the LSP service, so the next
		 * `getLSPService()` builds a fresh one and a touch spawns its server.
		 */
		function replaceSession(): number {
			runtime.resetForSession(Date.now());
			resetLSPService({ reason: "session_shutdown" });
			return lsp.createLSPClient.mock.calls.length;
		}

		it("the post-exit resync is skipped and recorded as stale-session", async () => {
			vi.useFakeTimers({ toFake: ["setTimeout", "clearTimeout"] });
			lsp.realService = getLSPService;
			const c = armChild({ write: true });
			const drain = handleAgentEnd(drainDeps());
			await c.didRead;
			await vi.advanceTimersByTimeAsync(HOOK_WALL_BUDGET_MS.agent_settled + 1);
			await drain;
			const spawnsBefore = replaceSession();
			c.openWrite();
			await c.wrote;
			await waitFor(postExitRows, (rows) => rows.length > 0, {
				yieldControl: tick,
				timeoutMs: 2_000,
			});
			expect(lsp.createLSPClient.mock.calls.length - spawnsBefore).toBe(0);
			expect(postExitRows()).toEqual([
				expect.objectContaining({
					metadata: { outcome: "stale-session" },
				}),
			]);
			expect(staleWriteSubjects()).toContain(`runtime-session:${filePath}`);
		});

		it("no-drop: in its own session the post-exit resync runs and spawns the server", async () => {
			vi.useFakeTimers({ toFake: ["setTimeout", "clearTimeout"] });
			lsp.realService = getLSPService;
			resetLSPService({ reason: "session_shutdown" });
			const spawnsBefore = lsp.createLSPClient.mock.calls.length;
			const c = armChild({ write: true });
			const drain = handleAgentEnd(drainDeps());
			await c.didRead;
			await vi.advanceTimersByTimeAsync(HOOK_WALL_BUDGET_MS.agent_settled + 1);
			await drain;
			c.openWrite();
			await c.wrote;
			await waitFor(postExitRows, (rows) => rows.length > 0, {
				yieldControl: tick,
				timeoutMs: 2_000,
			});
			expect(lsp.createLSPClient.mock.calls.length - spawnsBefore).toBe(1);
			expect(postExitRows()).toEqual([
				expect.objectContaining({ metadata: { outcome: "synced" } }),
			]);
		});

		it("the in-hook format resync is skipped", async () => {
			lsp.realService = getLSPService;
			const c = armChild({ write: true });
			const drain = handleAgentEnd(drainDeps());
			await c.didRead;
			const spawnsBefore = replaceSession();
			c.openWrite();
			await drain;
			expect(fs.readFileSync(filePath, "utf8")).toBe("const x = 1\n");
			expect(lsp.createLSPClient.mock.calls.length - spawnsBefore).toBe(0);
		});

		it("the in-hook autofix resync is skipped", async () => {
			lsp.realService = getLSPService;
			const { fixer, parked, resume } = gatedBiome();
			writeBiomeAgreement();
			runtime.deferMutation(
				filePath,
				env.tmpDir,
				"edit",
				env.tmpDir,
				"autofix",
			);
			flags.add("no-autoformat");
			const drain = handleAgentEnd(
				drainDeps({ biomeClient: fixer, ruffClient: noRuff }),
			);
			await parked.p;
			const spawnsBefore = replaceSession();
			resume.open();
			await drain;
			expect(fs.readFileSync(filePath, "utf8")).toBe("let x=1\n");
			expect(lsp.createLSPClient.mock.calls.length - spawnsBefore).toBe(0);
		});
	});

	it("the post-exit row names resyncLspFile's early return, not synced (#3528 r1 F1)", async () => {
		vi.useFakeTimers({ toFake: ["setTimeout", "clearTimeout"] });
		flags.add("no-lsp");
		const c = armChild({ write: true });
		const drain = handleAgentEnd(drainDeps());
		await c.didRead;
		await vi.advanceTimersByTimeAsync(HOOK_WALL_BUDGET_MS.agent_settled + 1);
		await drain;
		c.openWrite();
		await c.wrote;
		await waitFor(postExitRows, (rows) => rows.length > 0, {
			yieldControl: tick,
			timeoutMs: 2_000,
		});
		expect(postExitRows()).toEqual([
			expect.objectContaining({ metadata: { outcome: "no-lsp" } }),
		]);
	});

	it("the post-exit resync of a file the child removed records the failure instead of rejecting (#3529)", async () => {
		vi.useFakeTimers({ toFake: ["setTimeout", "clearTimeout"] });
		child.removeAfterWrite = true;
		const c = armChild({ write: true });
		const drain = handleAgentEnd(drainDeps());
		await c.didRead;
		await vi.advanceTimersByTimeAsync(HOOK_WALL_BUDGET_MS.agent_settled + 1);
		await drain;
		c.openWrite();
		await c.wrote;
		await waitFor(postExitRows, (rows) => rows.length > 0, {
			yieldControl: tick,
			timeoutMs: 2_000,
		});
		expect(postExitRows()).toEqual([
			expect.objectContaining({
				filePath,
				metadata: expect.objectContaining({ outcome: "read-failed" }),
			}),
		]);
	});
});
