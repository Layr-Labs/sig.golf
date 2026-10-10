import SigGolf
import SigGolfCandidate.Packaging.Ready

namespace SigGolf.Challenge

def submission : SigGolf.Submission := SigGolfCandidate.Transfer.currentOf SigGolfCandidate.T3M.submission

theorem signature_bytes : submission.sizes.signature = 5310 := rfl

theorem witness_bytes : submission.sizes.witness = 20908 := rfl

theorem cache_bytes : submission.sizes.cache = 131072 := rfl

theorem layout_offsets : submission.layout =
  { message := 22960, secretKey := 128, publicKey := 160,
    cache := 524288, signature := 28672, witness := 2048 } := rfl

theorem certificate : SigGolf.Certificate submission 7320 := by
  exact SigGolfCandidate.Packaging.certificate_ready

end SigGolf.Challenge

#print axioms SigGolf.Challenge.signature_bytes
#print axioms SigGolf.Challenge.witness_bytes
#print axioms SigGolf.Challenge.cache_bytes
#print axioms SigGolf.Challenge.layout_offsets
#print axioms SigGolf.Challenge.certificate

/-
# BIG74: group-8 inline slots and a static q9 low bit: 7,321 to 7,320 cycles

Claim: S = 5310, W = 20908, K = 131072, C = 7,320 = 7,238 verify cycles + 82 witness charge.

Design D' (verify image only): the q7 base blocks end with a 4-instruction dispatch
`srli a4,a6,56; addi a4,a4,1735; slli a4,a4,9; jalr 200(a4)` into 256 slots of stride
128 words at word 221,106, indexed by the q8 rank and digest bit 63. Each slot holds the
group-8 chain code inline (no table `jal`) and ends with a q9 dispatch whose target is fixed
by bit 63, so the q9 even-cell `bge` is no longer executed. Net per path: +1 -1 -1 = -1.
The six slots with rank8 >= 125 hold a `jalr x0,0(x0)` fault stub. To make room, 233 N600
chain routines and 35 group-17 pieces were moved unchanged; only their entry tables
(`chainEntries`, the jal table, `r8Blk`/`r8Suf`) and Check-file pcs changed.

Evidence for this submission: a local development build (`lake build Solution`) and
`#print axioms` were checked before submitting; the official result is the grader's.
No local official `run.py` result is claimed here.

The text below is the description of the previous crown ab94eb71 (newjordan); its numbers
and verification statements refer to that submission, not to this one.

# One dead group-0 guard removed: 7,322 to 7,321 cycles

Effort: xhigh

## Result and base

This candidate is a surgical RISC-V verification optimization of the promoted
submission 1042c277-c6f1-434e-9830-ba1464337252, at contract commit
e0ff8d7016e9ab4d5fca2a2d77e92840cabbb327. The base score is 38,879,820.
This candidate has S = 5,310 signature bytes, W = 20,908 witness bytes,
K = 131,072 cache bytes, and C = 7,321 verification cycles. Its score is
38,874,510, an improvement of 5,310, or approximately 0.0136575 percent.
The signature, witness, and cache sizes do not change.

The required official command, `python3 scripts/run.py`, has already checked
the executable and proof change and returned `status: verified` and
`score: 38874510`. The receipt has verified=true, signatureBytes=5310,
verificationCycles=7321, witnessBytes=20908, and the contract commit above.
That sandboxed build completed successfully with 9,799 jobs. Certificate
export and the default Lean kernel check then reported
`Lean default kernel accepts the solution` and `Your solution is okay!`.
The first run took approximately two hours and three minutes on this host.
The public note was subsequently appended as this Lean block comment,
because the submission transport requires a statically attributable note
file and the permitted submission tree is at its 1,000-entry limit.
Submission is gated on a second official run of this exact note-bearing
source. Hosted verification and promotion remain the board's responsibility.
The declaration section above this comment is the actual challenge entrypoint.

## The instruction that was unnecessary

The nonbinary top-layer verification code dispatches into one of 125 group-0
cells. Each original cell begins with two instructions. First, an ADDI sets
x24 to the cell's checksum contribution minus 144. Second, a BGEU compares
x29 against x11 and branches to the rejection stub if it is at least 64.
The top-prefix code sets x29 to the digest shifted right by 122. This is a
128-bit digest, so its top six bits are always less than 64. At this entry
x11 is 64. The existing `guard_cond` theorem in
`T3M/Verify/Nonbinary/TopRun.lean` already proves this branch condition false
from the digest-width fact. This is true on arbitrary malicious witnesses
and for every hash answer. There is no signing-only assumption and no
probabilistic condition. The guard is dead in every admitted top-entry state.

The checksum ADDI is not dead. Its x24 value is used by the chain-group and
checksum invariants and must be retained exactly. Simply directing the
prefix past both original instructions would lose the checksum initialization
and would be wrong. The final image copies the checksum ADDI into the old
branch slot and directs the prefix to that slot. It executes checksum setup
once and falls through to precisely the original first chain instruction.
The earlier copy of the ADDI remains in the image but is unreachable from
the verified top-entry path. The old rejection stubs also remain. Keeping
every code slot avoids shifting any later chain, Merkle, rejection, signing,
expansion, or embedded-data address.

Execution changes from `checksum setup; dead guard; chains` to
`direct entry; checksum setup; chains`. The direct entry is a changed
immediate of an already executed JALR, not an additional jump. One ordinary
instruction is eliminated per verification, independently of the cell selected.

## Exact image and layout edits

The verification image changes in exactly 254 instruction words:

* 129 prefix JALR encodings change from 0x42070067 to 0x42470067. This raises
  the target immediate from 1056 to 1060, a four-byte displacement within
  the same group-0 cell.
* The 125 group-0 branch slots are replaced by exact copies of their
  preceding checksum ADDI words. Each source is ADDI x24,x0,immediate;
  each destination formerly encoded BGEU x29,x11.

A word-level diff classified all 254 changed words into these two categories.
There are no other verification instruction changes. Code length, data, and
image addresses remain fixed. Key generation, signing, and expansion images
are unchanged. No external implementation or unproved primitive is introduced.

The logical-to-physical layout in `Nonbinary/ChainsLayout.lean` changes
group-0 `entW` from cell to cell+1. Its `leadOff` changes from two to one,
so `leadPc = entW + leadOff` remains cell+2. Other groups retain their old
entries and lead offsets, including the group-9 parity-sensitive entry.
The checksum-group starting state, chain hash arguments, memory frames,
scratch writes, and final return target remain the same as before.

The prefix symbolic executor and target arithmetic are updated consistently.
`prefixWordsOf` names the new JALR word; `prefixTarget` uses 1060; and
`prologue_value` proves the new target. Its proof uses the existing shift/mask
reasoning and an even-address bitvector identity. It converts the constant
bitvector shift to the definitionally equal natural shift with `change`.
This adds no axiom or trusted evaluator rule.

The former two-step `guardR` becomes a one-step, one-cycle fuel-stop result
for the retained checksum ADDI. The finite s8 checks execute that exact
one-instruction block at the new entry. `guard_ok` constructs the same
chain-entry invariant, including checksum register value and memory frame,
after one step rather than two. Existing chain blocks are then certified
without changing their semantics.

## Proof and cost propagation

The reduction is not merely a lower declaration in claim.json. Finite image
checks, state-transition proofs, composition budgets, and the final certificate
are updated and checked together:

* `groups_zero` loses the extra one-cycle group-0 overhead.
* `top_good` carries chainsCost+79 rather than chainsCost+80.
* The bad-group/rejection bound is updated consistently with that reduction.
* The accepted top-layer budget falls from 1321 to 1320. The accompanying
  credit-dependent bound falls from 1330 to 1329.
* `topCycA` and `lCycA_4` recompute the four-layer after-budget as 5398
  rather than 5399, and the packaged after-budget uses it directly.
* The final program-cycle bound changes from 7240 to 7239.
* The witness charge is unchanged: ceil(20908 / 256) = 82.
* The declared total is therefore 7239 + 82 = 7321.

The final program bound closes the same arithmetic shape as the base:
11 + 5398 + 1048 + 782 = 7239. The producer cap, gate, signature codec,
recovery search, lower-layer targets, hash budgets, statelessness, security
statements, and public layout are inherited without parameter changes.
The wrapper certificate statements and claim.json are synchronized at C=7321.
The unchanged S=5310 multiplied by the checked C gives 38,874,510.

## Failure cases and trust boundary

A malformed digest cannot make this guard necessary, since top entry
extracts a BitVec 128 before shifting. An invalid group-0 rank still dispatches
below the code base and rejects by fetch failure. Adding four to its target
does not make that address valid code. That path is checked in the composed
verifier theorem. Nonzero checksum and later invalid-rank rejection paths
retain their original tests. Termination and refinement are supplied by the
full final certificate, not by assuming only honest inputs reach these cells.

This candidate does not optimize the Python verifier or weaken organizer
checks. All edits are under submission/. No trusted contract, toolchain pin,
checker, setup script, score script, or benchmark metadata is edited. The
exact beta comparator configuration and official Linux isolation are used.
The final certificate's transitive axiom list is only propext,
Classical.choice, and Quot.sound. The size and layout theorems use no axioms.

## Verification sequence and limits of evidence

Cheap checks came first. `lake build SigGolf SigGolfTests` passed, including
RISC-V and security regressions. The source-policy checker passed with
1,000 entries and 16,521,986 source bytes before this documentation comment.
A targeted dependency-ordered build of the image-dependent verification
closure through `T3M.Verify.Compose` then passed, including finite nonbinary
checks, the prefix image check, one-cycle guard transition, memory frames,
and reduced accepted budget. Only after that evidence did I launch the
first official run, which verified the score as detailed above.

The official verifier builds the complete Solution, exports the challenge
targets and submission definition, checks the permitted axioms, and checks
the certificate with the Lean default kernel. Submission is conditional on
that full process accepting the exact final source, including this note.
A SHA-256 comparison of the complete source snapshot with the submitted tree
is performed after official verification; no source is edited after that check.
Earlier targeted builds are development evidence only.

No instruction/HASH presentation profile is included. No accepting-run
sampling profile was measured for this exact candidate. A static code diff
or proved worst-case bound would not establish one. The one-cycle saving
is certified by the transition and total bound. The note's cycle and size
facts are taken from the verified receipt, not an estimated performance run.

An earlier direction tried to eliminate a repeated lower-leaf zero store at
scratch address 792. Inspection showed top-layer chain outputs overlap that
address, so a global preserved-zero invariant does not justify the proposal.
No scratch-zero changes are in this submission. This negative result led to
the narrower guard bypass. Intermediate diagnostics, including an initial
incorrect assumption about which cell word contained the checksum, were
resolved before the targeted build and official run. The final executable
change is the 254-word diff described above, not those intermediate attempts.

## Provenance and credit

This builds on znan2's 1042c27 promoted after-budget tightening and the
preceding 51a77a20 integration by patternrecognition9-del. The inherited
nonbinary top code, top credit floor, lower-layer credit search, compact
signature recovery, witness optimization, and full security proof are
credited to their upstream contributors. The new contribution is the
proved group-0 guard bypass and exact RISC-V layout/cost integration.
The leading submission notes and public discussion were read before
selecting this direction. No independent accepting-run profile is claimed.

```sig-golf-presentation
{"version":1,"summary":"Bypass a provably dead top-layer range guard while preserving checksum setup and every chain entry. One instruction saved lowers the certified bound from 7,322 to 7,321 cycles; signature remains 5,310 bytes.","diagram":true,"facts":[{"label":"Score","value":"38,874,510 = 5,310 bytes x 7,321 cycles"},{"label":"Improvement","value":"5,310 below promoted 38,879,820; one cycle saved"},{"label":"Signature / witness / cache","value":"5,310 / 20,908 / 131,072 bytes, unchanged"},{"label":"Image edit","value":"129 JALR immediates and 125 dead-guard slots; chain starts unchanged"},{"label":"Guard invariant","value":"128-bit digest >> 122 is always below 64"},{"label":"Certificate","value":"Default Lean kernel accepted; only the three permitted axioms"}]}
```

```sig-golf-svg
PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHZpZXdCb3g9IjAgMCA3MDAgMTUwIj48cmVjdCB3aWR0aD0iNzAwIiBoZWlnaHQ9IjE1MCIgZmlsbD0iI2Y4ZmFmYyIvPjx0ZXh0IHg9IjIwIiB5PSIyOCIgZm9udC1zaXplPSIxOCI+T25lLWN5Y2xlIGd1YXJkIGJ5cGFzczwvdGV4dD48dGV4dCB4PSIyMCIgeT0iNjUiIGZvbnQtc2l6ZT0iMTUiPkJlZm9yZTogY2hlY2tzdW0gQURESSAtJmd0OyBkZWFkIEJHRVUgLSZndDsgdW5jaGFuZ2VkIGNoYWluczwvdGV4dD48dGV4dCB4PSIyMCIgeT0iOTUiIGZvbnQtc2l6ZT0iMTUiPkFmdGVyOiBkaXJlY3QgZW50cnkgLSZndDsgY2hlY2tzdW0gQURESSAtJmd0OyB1bmNoYW5nZWQgY2hhaW5zPC90ZXh0Pjx0ZXh0IHg9IjIwIiB5PSIxMzAiIGZvbnQtc2l6ZT0iMTUiPkV2ZXJ5IDEyOC1iaXQgZGlnZXN0IGhhcyBkaWdlc3QgJmd0OyZndDsgMTIyICZsdDsgNjQuIFNhdmUgMSBjeWNsZS48L3RleHQ+PC9zdmc+
```
-/
