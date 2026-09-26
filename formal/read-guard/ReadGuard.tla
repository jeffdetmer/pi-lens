------------------------------ MODULE ReadGuard ------------------------------
(***************************************************************************)
(* The read-before-edit guard (clients/read-guard.ts) for one file F, seen *)
(* from a POSITIONAL edit tool (oldRange / edits[].range / hashline): the  *)
(* class of edit the guard fully enforces. An oldText edit is content-     *)
(* validated by the host and skips FileTime, snapshot and (as a block)     *)
(* coverage (runtime-tool-call.ts ~1545 skipSnapshotCheck/oldTextResolved),*)
(* so it is out of scope.                                                  *)
(*                                                                         *)
(* A file is a sequence of line tokens. Every write mints fresh tokens, so *)
(* token equality is content equality (lineContentHash is whitespace-      *)
(* stripped; a whitespace-only rewrite is modelled as no change).          *)
(*                                                                         *)
(* Actors:                                                                 *)
(*  - the agent (one tool at a time; pi awaits each handler):              *)
(*      read   : tool_call provisional record (runtime-tool-call.ts ~1017, *)
(*               hashes + FileTime taken at tool_call), host read, then    *)
(*               the tool_result record (runtime-tool-result.ts ~1797)     *)
(*               that supersedes it (from the delivered bytes when the     *)
(*               file moved after the tool_call's stamp, #3524);           *)
(*      edit   : positional edit of 1 or 2 lines; checkEdit at tool_call   *)
(*               (runtime-tool-call.ts ~1543), optional relocation (~1560) *)
(*               then host apply, then recordWritten at tool_result        *)
(*               (runtime-tool-result.ts ~2305), with the written lines    *)
(*               recorded as read when not relocated (#3523, ~2254);       *)
(*      write  : noteCreatedFile at tool_call (~1123), host write,         *)
(*               recordWritten (injects the creation read, read-guard.ts   *)
(*               ~1305-1331), the turn's first write runs the immediate    *)
(*               autofix (pipeline.ts ~1527), recordWritten again          *)
(*               (runtime-tool-result.ts ~1083-1094), and the post-fix     *)
(*               bytes are attached as "authoritative" (~2814) and         *)
(*               recorded as a whole-file read (#3519, ~2874).             *)
(*  - another writer (external editor, second pi-lens instance, git):      *)
(*    changes F between any two steps.                                     *)
(*  - pi-lens' deferred agent_end format drain (runtime-agent-end.ts ~710):*)
(*    rewrites F, then recordWritten.                                      *)
(*  - boundaries: user turn (kTurn = what the agent knew before the        *)
(*    prompt), /new (fresh guard), /fork (fresh guard + importState of the *)
(*    parent's read-set, index.ts ~2510-2525; the conversation restarts    *)
(*    BEFORE a chosen user message), /tree (conversation moves, guard      *)
(*    untouched: no pi-lens handler).                                      *)
(*                                                                         *)
(* The agent's knowledge `know` is what the conversation shows it: read    *)
(* results, its own edits and writes, the authoritative attachment.        *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    N0,             \* initial line count
    MaxLen,         \* longest file
    AgentOps,       \* bound on agent tool calls
    Ops,            \* agent tool kinds: subset of {"read","rread","edit","write"}
    Spans,          \* edit spans: subset of {1,2}
    ExtWrites,      \* bound on other-writer writes
    ExtKinds,       \* subset of {"replace","delete","insert"}
    ExtPhases,      \* where the other writer may land: subset of {"idle","inflight"}
    FixKind,        \* immediate autofix: "none" | "replace" | "delete" | "insert" (at line 1)
    FormatDrain,    \* agent_end format: "none" | "replace" | "delete" | "insert" (at line 1)
    Bounds,         \* boundaries: subset of {"turn","new","fork","tree"}
    MaxBounds,      \* bound on boundaries
    Hashes,         \* TRUE: read records carry line hashes (file <= READ_HASH_MAX_LINES)
    Ctx,            \* contextLines (DEFAULT_CONFIG: 3)
    \* ---- current-code switches ----
    HandlerEvidence,\* TRUE (pre-#3524 code): a native read's hashes, range and FileTime come from disk at tool_result
    CreationHandlerEvidence, \* TRUE (code): the injected creation read is hashed from disk at tool_result
    MtimeAuthored,  \* TRUE (code): zero-read allow when mtime >= guard construction
    OwnEditRescue,  \* TRUE (code): canTreatStalenessAsOwnPriorEdit
    ForkImport,     \* TRUE (code): a fork imports the parent's whole read-set
    SuppressByNewerContext, \* TRUE (code): a newer context-only candidate cancels a snapshot mismatch
    FormatStamp,    \* TRUE (code): the agent_end format drain calls recordWritten
    \* ---- candidate fixes ----
    RecordAuthoritative, \* record the attached post-autofix bytes as a full read (code since #3519)
    RecordOwnEdit,       \* record the lines an allowed positional edit wrote as read (code since #3523)
    OwnEditSkipsReloc,   \* TRUE (code): ... but not when the edit was relocated
    SpanSnapshot,        \* check each line of the range against the newest read that delivered it
    RelocFromLatest,     \* relocate only from a read that is the agent's latest view of every line
    ForkAtBoundary,      \* fork/tree: forget reads made after the fork point
    \* ---- existing guards (FALSE = mutant with the guard removed) ----
    FileTimeCheck, CoverageCheck, SnapshotCheck

Lines == 1..MaxLen
NoH == [l \in Lines |-> 0]
Min(a, b) == IF a < b THEN a ELSE b

\* A hash map of `c` over lo..hi (0 = no hash).
MkH(c, lo, hi) ==
    [l \in Lines |-> IF Hashes /\ lo <= l /\ l <= hi /\ l <= Len(c) THEN c[l] ELSE 0]


Replace(s, l, t) == [s EXCEPT ![l] = t]
Delete(s, l) == SubSeq(s, 1, l - 1) \o SubSeq(s, l + 1, Len(s))
Insert(s, l, t) == SubSeq(s, 1, l - 1) \o <<t>> \o SubSeq(s, l, Len(s))
Mod(kind, s, l, t) ==
    CASE kind = "replace" -> Replace(s, l, t)
      [] kind = "delete"  -> Delete(s, l)
      [] kind = "insert"  -> Insert(s, l, t)
ModOk(kind, s, l) ==
    CASE kind = "replace" -> l <= Len(s)
      [] kind = "delete"  -> l <= Len(s) /\ Len(s) >= 2
      [] kind = "insert"  -> l <= Len(s) + 1 /\ Len(s) < MaxLen

VARIABLES
    disk, rev, tok,             \* file content, write counter (= mtime clock), fresh-token source
    know, kTurn,                \* agent knowledge; knowledge before the current prompt
    reads, ft, written, pendCreate, lastEditOk, born, turnNo,  \* guard state
    pc, pend, ops, ext, nb, fixedTurn, mutatedTurn,
    staleAllow, blindAllow, falseBlock  \* ghost verdict flags

vars == <<disk, rev, tok, know, kTurn, reads, ft, written, pendCreate, lastEditOk,
          born, turnNo, pc, pend, ops, ext, nb, fixedTurn, mutatedTurn,
          staleAllow, blindAllow, falseBlock>>

guardVars == <<reads, ft, written, pendCreate, lastEditOk, born, turnNo>>

\* g = turn the record was made in (ReadRecord.turnIndex); whole = whole-file view.
Rec(lo, hi, h, prov) == [lo |-> lo, hi |-> hi, h |-> h, prov |-> prov, g |-> turnNo, whole |-> FALSE]

Init ==
    /\ disk = [l \in 1..N0 |-> l] /\ rev = 0 /\ tok = N0 + 1
    /\ know = [l \in Lines |-> 0] /\ kTurn = know
    /\ reads = <<>> /\ ft = -1 /\ written = FALSE /\ pendCreate = FALSE
    /\ lastEditOk = FALSE /\ born = 0 /\ turnNo = 0
    /\ pc = "idle" /\ pend = [k |-> "none"] /\ ops = 0 /\ ext = 0 /\ nb = 0
    /\ fixedTurn = FALSE /\ mutatedTurn = FALSE
    /\ staleAllow = FALSE /\ blindAllow = FALSE /\ falseBlock = FALSE

KnowAll(c) == [l \in Lines |-> IF l <= Len(c) THEN c[l] ELSE 0]

\* A whole-file view (full read, creation read, attachment) is the agent's view
\* of every line, including "no such line" past its end (fix 4, part 3).
AddRec(S, r, whole) == Append(S, [r EXCEPT !.whole = whole])

----------------------------------------------------------------------------
\* Guard predicates (read-guard.ts). Record order in `reads` is timestamp order.
Max(a, b) == IF a > b THEN a ELSE b
\* readCoversRange (~1600): the effective range widened by contextLines.
CtxCovers(r, lo, hi) == Max(1, r.lo - Ctx) <= lo /\ hi <= r.hi + Ctx
EffCovers(r, lo, hi) == r.lo <= lo /\ hi <= r.hi
HashesMatch(r, lo, hi) ==                                       \* readRangeHashesStillMatch
    \A l \in lo..hi : r.lo <= l /\ l <= r.hi /\ r.h[l] # 0 /\ l <= Len(disk) /\ r.h[l] = disk[l]
AllHashesMatch(r) ==                                            \* readHashesStillMatch
    /\ \E l \in Lines : r.h[l] # 0
    /\ \A l \in Lines : r.h[l] # 0 => (l <= Len(disk) /\ r.h[l] = disk[l])
Idx(S) == 1..Len(S)
LastIdx(S) == IF S = {} THEN 0 ELSE CHOOSE i \in S : \A j \in S : j <= i

\* checkCoverage (~1867): the union of non-provisional, context-widened ranges.
Covered(lo, hi) ==
    \A l \in lo..hi : \E i \in Idx(reads) :
        ~reads[i].prov /\ Max(1, reads[i].lo - Ctx) <= l /\ l <= reads[i].hi + Ctx

\* canIgnoreStalenessByHashes (~1567).
HashRescueCode(lo, hi) == \E i \in Idx(reads) : CtxCovers(reads[i], lo, hi) /\ HashesMatch(reads[i], lo, hi)

\* validateRangeSnapshot (~1618). A candidate is "checked" when it delivered
\* and hashed every line of the range (currentLinesMatchReadSnapshot);
\* otherwise it is "unavailable". The block is suppressed when an unavailable
\* candidate is newer than the newest mismatch (~1690-1697).
Cands(lo, hi) == {i \in Idx(reads) : CtxCovers(reads[i], lo, hi)}
Checked(lo, hi) ==
    {i \in Cands(lo, hi) : EffCovers(reads[i], lo, hi) /\ \A l \in lo..hi : reads[i].h[l] # 0}
Unavail(lo, hi) == Cands(lo, hi) \ Checked(lo, hi)
HashUnavail(lo, hi) == {i \in Unavail(lo, hi) : EffCovers(reads[i], lo, hi)}
SnapMatch(lo, hi) == \E i \in Checked(lo, hi) : HashesMatch(reads[i], lo, hi)
SnapBlock(lo, hi) ==
    /\ SnapshotCheck
    /\ Checked(lo, hi) # {}
    /\ ~SnapMatch(lo, hi)
    /\ (SuppressByNewerContext => LastIdx(Unavail(lo, hi)) <= LastIdx(Checked(lo, hi)))
    /\ HashUnavail(lo, hi) = {}

\* Candidate fix (SpanSnapshot): every line of the range is compared with the
\* newest read that DELIVERED it (the agent's latest view of that line).
NewestDeliv(l) == LastIdx({i \in Idx(reads) : ~reads[i].prov
                              /\ ((reads[i].lo <= l /\ l <= reads[i].hi /\ reads[i].h[l] # 0)
                                  \/ reads[i].whole)})
SpanBlock(lo, hi) ==
    /\ SnapshotCheck
    /\ \E l \in lo..hi : NewestDeliv(l) # 0
         /\ (l > Len(disk) \/ reads[NewestDeliv(l)].h[l] # disk[l])
StaleRange(lo, hi) == IF SpanSnapshot THEN SpanBlock(lo, hi) ELSE SnapBlock(lo, hi)
\* ... and the FileTime rescue asks the same per-line question.
HashRescue(lo, hi) ==
    IF SpanSnapshot
      THEN \A l \in lo..hi : NewestDeliv(l) # 0 /\ l <= Len(disk) /\ reads[NewestDeliv(l)].h[l] # 0
                             /\ reads[NewestDeliv(l)].h[l] = disk[l]
      ELSE HashRescueCode(lo, hi)

\* findRelocation (~1770): newest read with hashes for the whole range; its
\* sequence must occur exactly once in the current file (the window is wider
\* than the file here).
HasSeq(i, lo, hi) == \A l \in lo..hi : reads[i].h[l] # 0
RelocSrc(lo, hi) ==
    LET W == {i \in Idx(reads) : HasSeq(i, lo, hi)
                 /\ (RelocFromLatest => \A l \in lo..hi : NewestDeliv(l) = i)}
    IN IF W = {} THEN 0 ELSE CHOOSE i \in W : \A j \in W : j <= i
MatchAt(i, lo, hi, s) ==
    s + (hi - lo) <= Len(disk) /\ \A d \in 0..(hi - lo) : disk[s + d] = reads[i].h[lo + d]
Reloc(lo, hi) ==
    IF hi - lo < 1 THEN 0
    ELSE LET i == RelocSrc(lo, hi)
         IN IF i = 0 THEN 0
            ELSE LET M == {s \in 1..Len(disk) : MatchAt(i, lo, hi, s)}
                 IN IF Cardinality(M) = 1 /\ (CHOOSE s \in M : TRUE) # lo
                      THEN CHOOSE s \in M : TRUE ELSE 0

\* checkEdit (~927) for a positional edit of lo..hi.
\* Returns [act |-> "allow"|"block"|"reloc", to |-> start, inject |-> BOOLEAN].
Verdict(lo, hi) ==
    IF Len(reads) = 0
    THEN IF written \/ (MtimeAuthored /\ rev > born)            \* wasWrittenThisSession
           THEN [act |-> "allow", to |-> lo, inject |-> TRUE, why |-> "session_authored"]
           ELSE [act |-> "block", to |-> lo, inject |-> FALSE, why |-> "zero_read"]
    ELSE IF FileTimeCheck /\ ft # rev
             /\ ~(OwnEditRescue /\ lastEditOk)
             /\ ~HashRescue(lo, hi)
    THEN [act |-> "block", to |-> lo, inject |-> FALSE, why |-> "file_modified"]
    ELSE IF CoverageCheck /\ ~Covered(lo, hi)
    THEN [act |-> "block", to |-> lo, inject |-> FALSE, why |-> "out_of_range"]
    ELSE IF StaleRange(lo, hi)
    THEN IF Reloc(lo, hi) # 0
           THEN [act |-> "reloc", to |-> Reloc(lo, hi), inject |-> FALSE, why |-> "range_stale_relocated"]
           ELSE [act |-> "block", to |-> lo, inject |-> FALSE, why |-> "range_stale"]
    ELSE [act |-> "allow", to |-> lo, inject |-> FALSE, why |-> "range_coverage"]

----------------------------------------------------------------------------
Idle == pc = "idle"
CanOp(k) == Idle /\ ops < AgentOps /\ k \in Ops

\* ---- read (full: "read", ranged: "rread") ----
\* tool_call: provisional record; a full read with no limit records line 1.
ReadCall(full, lo, hi) ==
    /\ CanOp(IF full THEN "read" ELSE "rread")
    /\ IF full THEN lo = 1 /\ hi = MaxLen ELSE lo <= hi /\ hi <= Len(disk)
    /\ LET plo == lo
           phi == IF full THEN 1 ELSE hi
       IN reads' = Append(reads, Rec(plo, phi, MkH(disk, plo, phi), TRUE))
    /\ ft' = rev
    /\ lastEditOk' = FALSE
    /\ pc' = "readExec" /\ pend' = [k |-> "read", full |-> full, lo |-> lo, hi |-> hi]
    /\ ops' = ops + 1
    /\ UNCHANGED <<disk, rev, tok, know, kTurn, written, pendCreate, born, turnNo,
                   ext, nb, fixedTurn, mutatedTurn, staleAllow, blindAllow, falseBlock>>

\* host read: the bytes delivered to the agent.
ReadExec ==
    /\ pc = "readExec"
    /\ LET hi == IF pend.full THEN Len(disk) ELSE Min(pend.hi, Len(disk))
       IN pend' = [k |-> "read", full |-> pend.full, lo |-> pend.lo, hi |-> hi,
                   view |-> KnowAll(disk)]
    /\ pc' = "readResult"
    /\ UNCHANGED <<disk, rev, tok, know, kTurn, guardVars, ops, ext, nb, fixedTurn,
                   mutatedTurn, staleAllow, blindAllow, falseBlock>>

\* tool_result: supersede the provisional record with the delivered range.
\* HandlerEvidence (pre-#3524): range (countFileLines), hashes and FileTime
\* taken from disk NOW.
\* Code since #3524: when the file moved after the tool_call's FileTime stamp
\* (ft # rev), hashes and range come from the delivered bytes (pi's own line
\* count), and FileTime keeps the tool_call stamp. Otherwise the disk still
\* holds the delivered bytes, and the record re-stamps.
ReadResult ==
    /\ pc = "readResult"
    /\ LET lo == pend.lo
           nowHi == IF pend.full THEN Len(disk) ELSE Min(pend.hi, Len(disk))
           hi == IF HandlerEvidence THEN nowHi ELSE pend.hi
           h == IF HandlerEvidence THEN MkH(disk, lo, hi) ELSE MkH(pend.view, lo, hi)
           provIdx == CHOOSE i \in Idx(reads) : reads[i].prov
                        /\ \A j \in Idx(reads) : reads[j].prov => j <= i
           rest == [j \in 1..(Len(reads) - 1) |->
                      IF j < provIdx THEN reads[j] ELSE reads[j + 1]]
       IN /\ reads' = IF lo <= hi THEN AddRec(rest, Rec(lo, hi, h, FALSE), pend.full) ELSE rest
          /\ ft' = IF HandlerEvidence \/ ft = rev THEN rev ELSE ft
    /\ know' = [l \in Lines |->
                  IF pend.lo <= l /\ l <= pend.hi THEN pend.view[l]
                  ELSE IF pend.full THEN 0 ELSE know[l]]
    /\ lastEditOk' = FALSE
    /\ pc' = "idle" /\ pend' = [k |-> "none"]
    /\ UNCHANGED <<disk, rev, tok, kTurn, written, pendCreate, born, turnNo,
                   ops, ext, nb, fixedTurn, mutatedTurn, staleAllow, blindAllow, falseBlock>>

\* ---- positional edit of lo..lo+span-1 (checkEdit at tool_call, host apply) ----
Edit(lo, span) ==
    /\ CanOp("edit") /\ span \in Spans
    /\ lo + span - 1 <= MaxLen
    \* know[l] = 0 is a blind edit (line numbers the agent never saw): any
    \* allow of it is a false allow.
    /\ LET hi == lo + span - 1
           v == Verdict(lo, hi)
           tg == v.to
           inDisk == tg + span - 1 <= Len(disk)
           ok == inDisk /\ \A d \in 0..(span - 1) : disk[tg + d] = know[lo + d]
           exact == hi <= Len(disk) /\ \A l \in lo..hi : know[l] = disk[l]
           new == [d \in 0..(span - 1) |-> tok + d]
           injected == IF v.inject THEN AddRec(reads, Rec(1, Len(disk), MkH(disk, 1, Len(disk)), FALSE), TRUE)
                       ELSE reads
           relocRead == IF v.act = "reloc"
                          THEN Append(injected, Rec(tg, tg + span - 1, MkH(disk, tg, tg + span - 1), FALSE))
                          ELSE injected
           blind == \E l \in lo..hi : know[l] = 0
       \* An allowed edit past EOF fails in the host, so only edits that land count.
       IN /\ staleAllow' = (staleAllow \/ (v.act # "block" /\ inDisk /\ ~blind /\ ~ok))
          /\ blindAllow' = (blindAllow \/ (v.act # "block" /\ inDisk /\ blind))
          /\ falseBlock' = (falseBlock \/ (v.act = "block" /\ exact))
          /\ IF v.act # "block" /\ inDisk
               THEN /\ disk' = [l \in 1..Len(disk) |->
                                   IF tg <= l /\ l <= tg + span - 1 THEN new[l - tg] ELSE disk[l]]
                    /\ rev' = rev + 1 /\ tok' = tok + span
                    /\ know' = [l \in Lines |-> IF lo <= l /\ l <= hi THEN new[l - lo] ELSE know[l]]
                    /\ reads' = relocRead
                    /\ lastEditOk' = TRUE
                    /\ pc' = "editRW"
                    /\ pend' = [k |-> "edit", lo |-> tg, hi |-> tg + span - 1, reloc |-> (v.act = "reloc"),
                                toks |-> [l \in Lines |-> IF tg <= l /\ l <= tg + span - 1
                                                          THEN new[l - tg] ELSE 0]]
                    /\ mutatedTurn' = TRUE
               ELSE /\ UNCHANGED <<disk, rev, tok, know, pend, mutatedTurn>>
                    /\ reads' = IF v.act # "block" THEN relocRead ELSE reads
                    /\ lastEditOk' = (v.act # "block")
                    /\ pc' = "idle"
    /\ ops' = ops + 1
    /\ UNCHANGED <<kTurn, ft, written, pendCreate, born, turnNo, ext, nb, fixedTurn>>

\* tool_result of the edit: recordWritten (FileTime from disk now).
EditRW ==
    /\ pc = "editRW"
    /\ ft' = rev /\ written' = TRUE /\ pendCreate' = FALSE
    /\ reads' = LET r0 == IF pendCreate
                            THEN AddRec(reads, Rec(1, Len(disk), MkH(disk, 1, Len(disk)), FALSE), TRUE)
                            ELSE reads
                IN IF RecordOwnEdit /\ (~pend.reloc \/ ~OwnEditSkipsReloc)
                     THEN Append(r0, Rec(pend.lo, pend.hi,
                                         [l \in Lines |-> IF Hashes THEN pend.toks[l] ELSE 0], FALSE))
                     ELSE r0
    /\ pc' = "idle" /\ pend' = [k |-> "none"]
    /\ UNCHANGED <<disk, rev, tok, know, kTurn, lastEditOk, born, turnNo, ops, ext,
                   nb, fixedTurn, mutatedTurn, staleAllow, blindAllow, falseBlock>>

\* ---- write (whole file) ----
Write ==
    /\ CanOp("write")
    /\ LET c == [l \in 1..N0 |-> tok + l - 1]
       IN /\ disk' = c /\ know' = KnowAll(c)
          /\ pend' = [k |-> "write", c |-> KnowAll(c), n |-> N0]
    /\ rev' = rev + 1 /\ tok' = tok + N0
    /\ pendCreate' = TRUE                              \* noteCreatedFile at tool_call
    /\ pc' = "writeRW1" /\ ops' = ops + 1 /\ mutatedTurn' = TRUE
    /\ UNCHANGED <<kTurn, reads, ft, written, lastEditOk, born, turnNo, ext, nb,
                   fixedTurn, staleAllow, blindAllow, falseBlock>>

\* recordWritten before the pipeline: stamps FileTime, injects the creation read.
WriteRW1 ==
    /\ pc = "writeRW1"
    /\ ft' = rev /\ written' = TRUE /\ pendCreate' = FALSE
    /\ reads' = IF pendCreate
                  THEN AddRec(reads, Rec(1, IF CreationHandlerEvidence THEN Len(disk) ELSE pend.n,
                                         IF CreationHandlerEvidence THEN MkH(disk, 1, Len(disk))
                                         ELSE MkH(pend.c, 1, pend.n), FALSE), TRUE)
                  ELSE reads
    /\ pc' = IF FixKind # "none" /\ ~fixedTurn THEN "fix" ELSE "idle"
    /\ pend' = IF FixKind # "none" /\ ~fixedTurn THEN pend ELSE [k |-> "none"]
    /\ UNCHANGED <<disk, rev, tok, know, kTurn, lastEditOk, born, turnNo, ops, ext,
                   nb, fixedTurn, mutatedTurn, staleAllow, blindAllow, falseBlock>>

\* The turn's first write: immediate autofix rewrites line 1.
Fix ==
    /\ pc = "fix"
    /\ fixedTurn' = TRUE
    /\ IF ModOk(FixKind, disk, 1)
         THEN /\ disk' = Mod(FixKind, disk, 1, tok) /\ rev' = rev + 1 /\ tok' = tok + 1
              /\ pc' = "writeRW2"
              /\ pend' = [k |-> "fixed", c |-> KnowAll(Mod(FixKind, disk, 1, tok)),
                          n |-> Len(Mod(FixKind, disk, 1, tok))]
         ELSE /\ UNCHANGED <<disk, rev, tok>> /\ pc' = "idle" /\ pend' = [k |-> "none"]
    /\ UNCHANGED <<know, kTurn, guardVars, ops, ext, nb, mutatedTurn, staleAllow, blindAllow, falseBlock>>

\* recordWritten after the pipeline; the tool result attaches the post-fix bytes.
WriteRW2 ==
    /\ pc = "writeRW2"
    /\ ft' = rev /\ written' = TRUE
    /\ know' = pend.c
    /\ reads' = IF RecordAuthoritative
                  THEN AddRec(reads, Rec(1, pend.n, MkH(pend.c, 1, pend.n), FALSE), TRUE)
                  ELSE reads
    /\ pc' = "idle" /\ pend' = [k |-> "none"]
    /\ UNCHANGED <<disk, rev, tok, kTurn, pendCreate, lastEditOk, born, turnNo, ops,
                   ext, nb, fixedTurn, mutatedTurn, staleAllow, blindAllow, falseBlock>>

----------------------------------------------------------------------------
\* Another writer (external editor, second pi-lens instance, git checkout).
External ==
    /\ ext < ExtWrites
    /\ (IF pc = "idle" THEN "idle" ELSE "inflight") \in ExtPhases
    /\ \E kind \in ExtKinds, l \in 1..MaxLen :
         /\ ModOk(kind, disk, l)
         /\ disk' = Mod(kind, disk, l, tok)
    /\ rev' = rev + 1 /\ tok' = tok + 1 /\ ext' = ext + 1
    /\ UNCHANGED <<know, kTurn, guardVars, pc, pend, ops, nb, fixedTurn, mutatedTurn,
                   staleAllow, blindAllow, falseBlock>>

\* A user turn boundary: agent_end's deferred format drain, then the next prompt.
Turn ==
    /\ Idle /\ "turn" \in Bounds /\ nb < MaxBounds
    /\ IF FormatDrain # "none" /\ mutatedTurn /\ ModOk(FormatDrain, disk, 1)
         THEN /\ disk' = Mod(FormatDrain, disk, 1, tok) /\ rev' = rev + 1 /\ tok' = tok + 1
              /\ IF FormatStamp                               \* recordWritten after the format
                   THEN ft' = rev + 1 /\ written' = TRUE
                   ELSE UNCHANGED <<ft, written>>
         ELSE UNCHANGED <<disk, rev, tok, ft, written>>
    /\ kTurn' = know /\ turnNo' = turnNo + 1
    /\ fixedTurn' = FALSE /\ mutatedTurn' = FALSE /\ nb' = nb + 1
    /\ UNCHANGED <<know, reads, pendCreate, lastEditOk, born, pc, pend, ops, ext,
                   staleAllow, blindAllow, falseBlock>>

FreshGuard ==
    /\ ft' = -1 /\ written' = FALSE /\ pendCreate' = FALSE /\ lastEditOk' = FALSE
    /\ born' = rev

\* /new: fresh guard, empty conversation.
New ==
    /\ Idle /\ "new" \in Bounds /\ nb < MaxBounds
    /\ reads' = <<>> /\ FreshGuard /\ UNCHANGED turnNo
    /\ know' = [l \in Lines |-> 0] /\ kTurn' = know'
    /\ nb' = nb + 1 /\ fixedTurn' = FALSE /\ mutatedTurn' = FALSE
    /\ UNCHANGED <<disk, rev, tok, pc, pend, ops, ext, staleAllow, blindAllow, falseBlock>>

\* /fork: the conversation restarts before the current prompt (kTurn); the new
\* guard imports the parent's read-set, reconciled against disk only.
Kept(S) == SelectSeq(S, AllHashesMatch)
BeforePrompt(r) == r.g < turnNo
Fork ==
    /\ Idle /\ "fork" \in Bounds /\ nb < MaxBounds
    /\ LET src == IF ForkAtBoundary THEN SelectSeq(reads, BeforePrompt) ELSE reads
           imp == IF ForkImport THEN Kept(src) ELSE <<>>
       IN /\ reads' = imp
          /\ ft' = IF Len(imp) > 0 THEN rev ELSE -1      \* recordRead stamps FileTime
    /\ UNCHANGED turnNo
    /\ written' = FALSE /\ pendCreate' = FALSE /\ lastEditOk' = FALSE /\ born' = rev
    /\ know' = kTurn
    /\ nb' = nb + 1 /\ fixedTurn' = FALSE /\ mutatedTurn' = FALSE
    /\ UNCHANGED <<disk, rev, tok, kTurn, pc, pend, ops, ext, staleAllow, blindAllow, falseBlock>>

\* /tree: the conversation moves to an earlier point; pi-lens has no handler.
Tree ==
    /\ Idle /\ "tree" \in Bounds /\ nb < MaxBounds
    /\ know' = kTurn
    /\ reads' = IF ForkAtBoundary THEN SelectSeq(reads, BeforePrompt) ELSE reads
    /\ UNCHANGED turnNo
    /\ written' = IF ForkAtBoundary THEN FALSE ELSE written   \* writtenThisSession
    /\ nb' = nb + 1
    /\ UNCHANGED <<disk, rev, tok, kTurn, ft, pendCreate, lastEditOk, born,
                   pc, pend, ops, ext, fixedTurn, mutatedTurn,
                   staleAllow, blindAllow, falseBlock>>

Next ==
    \/ \E lo \in 1..MaxLen, hi \in 1..MaxLen : ReadCall(FALSE, lo, hi)
    \/ ReadCall(TRUE, 1, MaxLen)
    \/ ReadExec \/ ReadResult
    \/ \E lo \in 1..MaxLen, s \in Spans : Edit(lo, s)
    \/ EditRW
    \/ Write \/ WriteRW1 \/ Fix \/ WriteRW2
    \/ External \/ Turn \/ New \/ Fork \/ Tree

Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------
\* False allow: an allowed (or relocated) positional edit of lines the agent
\* was shown lands on lines whose current content is what it was shown.
NoStaleAllow == ~staleAllow

\* False allow: an edit of lines this conversation never showed the agent is
\* refused (with contextLines > 0 the guard admits +-Ctx lines by design).
NoBlindAllow == ~blindAllow

\* False block: with hashes available, an edit whose target lines hold
\* exactly what the agent was shown is never refused.
NoFalseBlock == ~falseBlock
=============================================================================
