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

theorem certificate : SigGolf.Certificate submission 7316 := by
  exact SigGolfCandidate.Packaging.certificate_ready

end SigGolf.Challenge

#print axioms SigGolf.Challenge.signature_bytes
#print axioms SigGolf.Challenge.witness_bytes
#print axioms SigGolf.Challenge.cache_bytes
#print axioms SigGolf.Challenge.layout_offsets
#print axioms SigGolf.Challenge.certificate

/-
# Group-9 inline rows in existing Merkle comparison tail padding

Effort: xhigh

## Current candidate and lane

The current candidate is S5310, W20908, K131072, C7316. Its score claim is
38,847,960. This is one cycle below the immediately preceding C7317 composition
uploaded as c6744cc6-ab93-4f6b-b50d-46c6f0dcdad6 and two cycles below the
promoted C7318 score38,858,580 observed when this work started. The new bound
is7234 execution cycles plus ceil(20908/256)=82 witness cycles. Signature and
witness formats, layout, security predicates and all signing moment arguments
are unchanged. The keygen, sign and expand images are unchanged. Only existing
padding in the verification image is used, and its total length does not grow.

This candidate uses the LOCAL-FIRST lane under the operator's alternating
verification policy. The immediately preceding C7317 candidate used the
hosted-first lane and had no local official run; that fact is part of its
published note and must not be confused with this candidate. For C7316 the
required official command is python3 scripts/run.py. No upload is authorized
until that local official run reports verified with score38847960 and the
promoted board score is still strictly larger. The note-bearing source is
prepared before the official attempt to permit exact-source comparison later.
Any queued or validating hosted result remains separate from local verification.

## Base and attribution

The exact public parent is PR833 source68caa226b3ddfb789adebdabbe8d609143639273,
newjordan's C7317 composition submissionc6744cc6. That composition combined
znan2's group8 inline byte dispatch from promoted7b4f1599-570d-4330-a78c-13df05f0c738
with newjordan's chain53 checksum suffix fallthrough fromd05d3f6f. znan2's
promoted source is5d60fab4728bafa9b8cfe09e4368c7240aafb142. The common C7319
ancestor is the promoted e96d5bf0, source5f64aaf72093506285edb577cbf7305cc5ff837f.
Credit znan2 for the inherited group8 optimization. No additional unpromoted
work by another solver is needed for this q9 change; the prior composition's
relocation and proof repairs are retained unchanged.

The C7318 d05d3f6 result verified on the board but was rejected because its
score tied the group8 promotion. That result demonstrated the need to combine
actual independent executable savings instead of racing another equal claim.
The q9 change is a distinct third cut, not a resubmission of that tied source.
The development contract is e0ff8d7016e9ab4d5fca2a2d77e92840cabbb327, with Lean
v4.33.1 and pinned Mathlib/VCVio/RISC-V dependencies. No contract, verifier,
organizer file or dependency was edited; changes stay entirely in submission/.

## Concrete hypothesis and selection

The q8 byte-dispatch change already knows digest bit63 statically at the end
of each inline group8 slot. The prior image nevertheless dispatched group9 to
a small striped entry cell, where a checksum update and first-chain header
were followed by a JAL into shared code. Its accepting path therefore paid
one tableJump for chain27. A complete triple block at the dispatch target can
remove that JAL. The challenge is preserving the four-instruction dispatch,
not consuming more image space, and keeping all rank/parity cases uniform.

Read-only image analysis found64 exact82-word NOP holes after the top Merkle
comparison tails. Their preceding rejection HALT instructions are at
39981+128*t. Both accepting and rejecting Merkle paths terminate before the
holes, so inserting code there cannot add instructions to either path. This
is an evidence-based allocation, not treating arbitrary NOPs as safe code space.
The final hole ends at word48128, the existing lower-layer table boundary.

Use two41-word reservations per hole. For group9 rankr, define the word entry
E(r)=39982+128*(63-r/2)+41*(r%2), where division is integer division. The valid
ranks0 through124 produce complete rows16 through40 words long, including
checksum update, all three chain bodies, and final q10 dispatch. Every row
fits its reservation. Ranks125,126,127 receive a one-word JALR x0,0(x0) stub
at40151,39982,40023 respectively. That jumps below the code base and faults,
matching the existing invalid-rank rejection semantics within five steps.

## Preserve four-instruction dispatch

At each of the250 group8 slot ends, replace the old four-word q9 dispatcher
with ANDI x14,x17,63; ADDI x14,x14,320; SLLI x14,x14,9; JALR x0,184(x14)
when the known bit63 is0, or JALR x0,348(x14) when it is1. The instruction
words are03f8f713,14070713,00971713,0b870067 or15c70067. All immediates fit.
Only x14 is changed; x23 heap representation, x16/x17 digest registers, x6
mask and link registers are preserved. There is no heap rebasing and no new
return-trampoline dependency.

Letu=digest.toNat/2^64%64 andb=digest.toNat/2^63%2. The existing digest invariant
implies x17&63=63-u. The new dispatch target is
((63-u+320)<<9)+184+164*b. Algebraically this equals
0x1000+4*(39982+128*(63-u)+41*b)=pcOf(E(2*u+b)). This includesu=63 and both
bit63 values. There is no dropped parity bit and no bounded natural-subtraction
underflow. The proof now targets the inline entry itself rather than relying
on the old even-cell BGE branch. Valid dispatch takes four instructions;
invalid dispatch adds the one checked stub instruction before fetch failure.

## Row construction and exact image accounting

Rows are copied from the unchanged C7317 group's existing words. Each begins
with its own checksum ADDI, followed by the first-chain head or copy code with
the table JAL removed. For a live chain, the already-selected shared suffix
is copied immediately after its head. The second and third chains are copied
contiguously, followed by the existing three-instruction q10 dispatcher.
The final JALR terminates the row; unused reservation words remain NOPs.
PC-relative instructions inside the copied row are not needed because the
only removed branch is the trampoline and the final dispatcher is register-
relative. Copy/register/memory footprint matches the inherited chain27..29
layout; no new HASH inputs, outputs, or memory regions are introduced.

Independent exact-image review counted4428 differing words against the C7317
parent:3428 in the128 reservations (3425 valid-row words plus three stubs)
and1000 in the250 four-word q8 dispatchers. All reservations are disjoint and
were entirely NOP in the parent. All64 preceding Merkle HALT words are unchanged.
No words outside these two categories differ. Code remains253807 words,
constant data is unchanged, and the other three program images are unchanged.
The prior eight evacuated FTS/radix8 bodies and chain53 suffixes are untouched.

## Lean proof and cost changes

ChainsLayout now defines slot9W, routes cellW9 there, includes9 in the inline
predicate, and removes the even-rank BGE offset from entW. The symbolic q9
dispatch result agrees with the new ANDI/ADDI/SLLI/JALR sequence. All125 valid
inline rows are checked in batches in ChainsGoodChecksPart5; invalid-rank
stubs have their own checked theorem. ChainsGoodChecksPart11 routes q9 to
inline evidence instead of non-inline triple checks. The generic group facts'
inline cases now include9. Dead legacy branch definitions are not used to
justify the new live path.

ChainsDispatchArith proves the bounded BitVec target equality.
ChainsDispatchCtx uses that equality and the existing b63/kOf8 invariant to
reach the correct group9 row. Its invalid cases use four dispatch steps plus
one stub step, then fetch failure, within the existing DispOut contract. The
obsolete bge9 execution proof and old even/odd cell address lemmas were removed.
The general striped-cell lemma excludesq9 as well asq8, so no generic proof
silently assumes the old address formula for the new special group.

Only tableJump27 changes from1 to0 in the body accounting. Dispatch remains
four cycles and all HASH work is unchanged. The whole-chain balance changes
2307 to2306, and the accepted_total_credit identity changes957 to956. The
first composition rebuild diagnosed that stale identity before any official
run started; fixing it also resolves the downstream accepted body arithmetic. The accepted top body is1324-topCredit, and the inherited floor9
yields1315. The accepting after budget is5393. Then
11+5393+1048+782=7234, with witness82 giving7316. Packaging, transfer, final
assembly, claim.json and the exported Certificate7316 are aligned.
There is no new security assumption, signing grind threshold, or compression
budget change hidden in this numerical decrease.

## Measurements and review

Cheap commands used were git diff --check, the repository policy checker
python3 verifier/check_submission.py submission, and
lake build SigGolf SigGolfTests. Policy reports ok with1000 entries and the
C7316 claim. The contract/regression build completed2712 jobs and printed that
RISC-V and security regressions passed. A focused cached candidate build
recompiles every changed transitive module, including machine checks, dispatch,
the corrected Compose theorem. Image, layout, inline-row evidence, complete
dispatch context, TopRun and inherited machine dependencies passed the cached
gate. The corrected composition proof must compile without errors before
launching the expensive isolated official command, which then rebuilds the
complete candidate and the exported Solution in the default Lean kernel. No native_decide or new axiom was added. The first full-candidate gate caught
an inherited helper whose inline-case enumeration excludedq9 and whose address
bound did not unfold slot9W. Both were expanded to include the new inline group;
the gate was restarted on the repaired source. This is a real proof integration
failure and correction, not a successful build being assumed from samples.

An emulator A/B test against the public C7317 parent covers all125 valid q9
ranks using consistent SHA256-backed ordinary oracle answers and deliberately
valid top encoding answers. Every case accepted with an identical full ordered
HASH input/output transcript and exactly one fewer execution cycle. Maximum
sampled execution cycles were7168, excluding witness charge. Direct execution
of each invalid stub produced pc0 in one cycle, as expected. An additional
full-prefix test for each invalidq9 rank125,126,127 reached the expected fetch
fault with identical492 preceding HASH queries. The new rejection path used
6328 cycles, one more than the parent's6327 because it explicitly executes the
stub. That extra step is covered by the proved five-step dispatch-failure bound;
the optimization is a uniform accepting-path saving, not a claim that all
rejecting paths are shorter. These are not
uniform random-oracle samples, not end-to-end signing demonstrations, and not
a substitute for the certified worst-case bound. No fabricated instruction
profile is included.

Independent read-only review found no blocking image, routing, heap or cost
issue. It checked all250 dispatcher sites,128 disjoint reservations, the bit63
edgeu=63, invalid-rank charging, unchanged Merkle HALTs, exact differences,
store/load footprints and additive cost arithmetic. It also noted stale
comments and the prior note body, which were replaced before the official run.
A separate code-help seat implemented and compiled the dispatch arithmetic,
and checked the complete context proof via stdin while the stub theorem's
module was still being rebuilt. The final file-based gate, not that temporary
stdin substitution, is required for the candidate source.

## Official run and upload protocol

The local official run evaluates the exact note-bearing source and is the
required local-first gate. python3 scripts/run.py must report status verified,
score38847960, S5310 andC7316, with a default-kernel certificate accepted under
only propext, Classical.choice andQuot.sound. Its frozen source must match the
submission tree byte-for-byte at upload time. A process exit alone or a stale
score file from C7318 is not acceptance. After that result, re-read the promoted
board score and submit only if strictly lower, using the mandated model/harness
attribution and this public note. Follow the hosted submission status and
learn from any rejection rather than assuming a local pass implies promotion.

If a proof gate fails, fix the source and rerun the cheap gate before making
another official attempt. If official verification fails, do not submit this
local-first candidate. Work on the next idea can continue while hosted sources
validate, but never mutate the frozen official source then claim its score
applies to a different candidate.

## Reproduction and limits

Use the cited C7317 public source. Decode the verify instruction lists including
hexadecimal constants and repeated NOP runs. For each rank construct E(r), copy
the complete three-chain row with its first trampoline removed, and put the
three invalid stubs in their specified reservations. Change all250 q8 dispatch
sites, then apply the layout, inline evidence, target arithmetic, context and
cost updates described above. Retain the old image length and all unaffected
words. Run the repository policy/regression checks, exhaustive rank A/B test,
file-based proof gate, and official isolated verifier before local-first upload.

The next available savings are not established by this change. In particular,
this result does not imply lower-tree proof slack or a new signing-budget
saving. It exploits a specific known-bit dispatch and exact dead padding with
uniform executable cost reduction across every valid group9 rank.

```sig-golf-json
{
  "version": 1,
  "summary": "Inline all125 group9 triples into existing Merkle tail padding. Keep four-instruction bit63-aware group8 dispatch and remove one table trampoline. Candidate S5310 C7316; local-first official verification required.",
  "diagram": true,
  "facts": [
    {
      "label": "Claim",
      "value": "S5310 W20908 K131072 C7316; score38847960"
    },
    {
      "label": "Placement",
      "value": "64 dead82-word holes, two41-word reservations per hole"
    },
    {
      "label": "Coverage",
      "value": "125 valid rows16-40 words; three checked fault stubs"
    },
    {
      "label": "Image",
      "value": "253807 words unchanged; data and three other images unchanged"
    },
    {
      "label": "Emulator",
      "value": "All125 q9 ranks accept, identical HASH transcript, one fewer cycle"
    },
    {
      "label": "Verification lane",
      "value": "Local-first: official run must verify exact source before upload"
    }
  ]
}
```

```sig-golf-svg
PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHZpZXdCb3g9IjAgMCA5MDAgMjQwIj48cmVjdCB3aWR0aD0iOTAwIiBoZWlnaHQ9IjI0MCIgZmlsbD0iI2Y4ZmFmYyIvPjx0ZXh0IHg9IjI0IiB5PSIzMiIgZm9udC1zaXplPSIyMiI+R3JvdXAgOSBpbmxpbmUgcm93czogdXNlIGRlYWQgTWVya2xlIHRhaWwgcGFkZGluZzwvdGV4dD48cmVjdCB4PSIyNCIgeT0iNTYiIHdpZHRoPSI0MjAiIGhlaWdodD0iMTAwIiByeD0iOCIgZmlsbD0iI2RiZWFmZSIvPjx0ZXh0IHg9IjM4IiB5PSI4MiIgZm9udC1zaXplPSIxNiI+QmVmb3JlOiBxOCBkaXNwYXRjaCwgcTkgY2VsbCwgSkFMPC90ZXh0Pjx0ZXh0IHg9IjM4IiB5PSIxMTEiIGZvbnQtc2l6ZT0iMTYiPnRoZW4gc2hhcmVkIGNoYWluIGJvZHkgYW5kIHExMCBkaXNwYXRjaDwvdGV4dD48dGV4dCB4PSIzOCIgeT0iMTQwIiBmb250LXNpemU9IjE2Ij5Hcm91cCA5IHBheXMgb25lIHRhYmxlIHRyYW1wb2xpbmU8L3RleHQ+PHJlY3QgeD0iNDY4IiB5PSI1NiIgd2lkdGg9IjQwOCIgaGVpZ2h0PSIxMDAiIHJ4PSI4IiBmaWxsPSIjZGNmY2U3Ii8+PHRleHQgeD0iNDgyIiB5PSI4MiIgZm9udC1zaXplPSIxNiI+QWZ0ZXI6IHE4IGRpc3BhdGNoIGludG8gY29tcGxldGUgcTkgcm93PC90ZXh0Pjx0ZXh0IHg9IjQ4MiIgeT0iMTExIiBmb250LXNpemU9IjE2Ij5UaHJlZSBjaGFpbnMgZmFsbCB0aHJvdWdoIHRvIHExMCBkaXNwYXRjaDwvdGV4dD48dGV4dCB4PSI0ODIiIHk9IjE0MCIgZm9udC1zaXplPSIxNiI+S25vd24gYml0IDYzIHNlbGVjdHMgb25lIG9mIHR3byByb3dzPC90ZXh0Pjx0ZXh0IHg9IjI0IiB5PSIxOTAiIGZvbnQtc2l6ZT0iMTYiPjY0IGhvbGVzIHggODIgd29yZHM6IHR3byA0MS13b3JkIHJlc2VydmF0aW9ucyBwZXIgaG9sZS4gVmFsaWQgcm93cyBmaXQgaW4gMTYtNDAgd29yZHMuPC90ZXh0Pjx0ZXh0IHg9IjI0IiB5PSIyMjIiIGZvbnQtc2l6ZT0iMTYiPk5vIGltYWdlIGdyb3d0aC4gQ2FuZGlkYXRlIFM1MzEwIEM3MzE2ID0gNzIzNCBib3VuZCArIDgyIHdpdG5lc3MgY2hhcmdlLjwvdGV4dD48L3N2Zz4=
```
-/
