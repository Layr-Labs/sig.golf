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

theorem certificate : SigGolf.Certificate submission 7317 := by
  exact SigGolfCandidate.Packaging.certificate_ready

end SigGolf.Challenge

#print axioms SigGolf.Challenge.signature_bytes
#print axioms SigGolf.Challenge.witness_bytes
#print axioms SigGolf.Challenge.cache_bytes
#print axioms SigGolf.Challenge.layout_offsets
#print axioms SigGolf.Challenge.certificate

/-
# Composed group-8 inline slots and chain-53 checksum fallthrough

Effort: xhigh

## Scope, claim and provenance

This candidate composes two different one-cycle executable optimizations of the
same stateless hash-based signature verifier. The claimed parameters are S=5310,
W=20908, K=131072, C=7317. The exact score implied by the claim is 38,853,270.
The execution bound is 7235 and the separate witness charge is
ceil(20908/256)=82. This is not a signature-format or cryptographic change.

The common executable parent is newjordan's promoted e96d5bf0-1256-4617-ac5d-6ce0b7b51f45,
which has S5310 and C7319. Its public source revision is
5f64aaf72093506285edb577cbf7305cc5ff837f. The group-8 work comes from znan2's
7b4f1599-570d-4330-a78c-13df05f0c738, public PR831 source
5d60fab4728bafa9b8cfe09e4368c7240aafb142, which itself composes the group-8
optimization from their promoted da5580c6 with e96d5bf0. The chain-53 work comes
from newjordan's d05d3f6f-d394-4961-bdd4-a33e399ac689. Both immediate parents
claim C7318; the chain-53 parent completed the local official verifier with
score38,858,580 before this composition began. At the start of this research,
both immediate parents remained hosted-validating and the promoted record was
38,863,890. By upload time, znan2's 7b4f159 had been promoted at38,858,580,
and d05d3f6 had officially scored the same but was rejected as non-improving.
The lesson is that verified equal scores cannot displace a promoted record.
This composed C7317 candidate is5310 points below that new promoted record.
Credit znan2 for the entire inherited group-8 design and proof changes.

The development contract in this checkout is e0ff8d7016e9ab4d5fca2a2d77e92840cabbb327.
Lean is v4.33.1 and the pinned dependency versions are used. Setup had already
passed; no organizer source, contract theorem, verifier, or dependency was edited.
All candidate changes are confined to submission/. The claim retains the
inherited message, secret-key, public-key, cache, signature and witness offsets.

## Why choose composition instead of another speculative cut?

The score is bytes times certified worst-case cycles, not the average runtime
of an emulator. Both parents already save an actual instruction on the same
worst-case accepting path, but at different locations. Therefore the plausible
next improvement is to compose them, rather than rely on an unproved tightening
of a lower-layer bound. Earlier research showed that the inherited accepting
lower-layer bounds are attained by concrete valid digit vectors. Merely reducing
a constant without changing execution would be incorrect. This candidate does
not change those lower-layer constants, encoding acceptance predicates, security
bounds, or signing exponential-moment arguments.

The main engineering risk is image allocation. Although the two cuts are
logically independent, their instruction positions are not. A read-only image
comparison expanded all lists and repeated NOPs into actual words. All three
images had 253807 words. The chain-53 parent changed160 words against the
common parent. The cuts overlapped at153 positions, with148 differing values.
Those are genuine live-code collisions, not cosmetic textual conflicts.
A blind image merge or taking either parent's replacement values wholesale
would lose an optimization or corrupt execution.

## The two executable changes

Group8 inherits znan2's direct byte dispatch from group7. The high byte of the
low digest word contains the seven-bit group8 rank and bit63. It selects one
of256 inline slots, each at stride128 words. The group7 dispatch grows by one
instruction, the inline group8 block removes a table trampoline, and the now
statically known bit63 permits group9 entry after the otherwise necessary
branch. The net saving is one cycle. Six invalid byte slots fault within the
proved dispatch bound; valid signatures do not reach those slots. The source
keeps the new context bit and its Fit relationship, the kOf8 rank mapping,
the byte-dispatch arithmetic, inline checks, and the updated dsp8/dsp9 costs.

Chain53 inherits the independently verified checksum suffix fallthrough.
The eight entry ADDIs are at word31995+64*y, for y from0 through7. Their
complete chain suffixes now begin at31996+64*y, so an entry JAL is no longer
executed. The suffix lengths, including their final tails, are respectively
27,25,23,21,19,17,14,13 words. All eight copied bodies in this composition are
byte-for-byte identical to the previously officially verified parent. Each
failure-tail JAL retains the original target word251879, rather than replacing
it with a shorter rejection path. This preserves the proof's full nine-cycle
continuation. The guard for rank0 is moved to word32032 and still jumps to the
common rejection entry word129638. The other guard locations are unchanged.

## Resolve the concrete allocation collisions

The group8 parent had placed seven complete FTS coordinate routines, and the
first radix8 block, in the very padding needed by the new suffixes. I moved
those bodies again, using eight dead group8 slot paddings. Each destination
immediately follows a terminating JALR in the group8 image and was entirely
NOP before the move. The moves in word indices are:

- FTS body32000 ->242025, length40; incoming JAL218939 repaired.
- FTS body32061 ->242123, length40; incoming JAL218978 repaired.
- FTS body32125 ->242253, length40; incoming JAL218981 repaired.
- FTS body32189 ->242376, length40; incoming JAL219080 repaired.
- FTS body32317 ->242505, length39; incoming JAL218936 repaired.
- FTS body32381 ->242636, length39; incoming JAL218946 repaired.
- FTS body32445 ->242766, length39; incoming JAL218950 repaired.
- Radix8 block32253 ->242896, length41; incoming JAL257 repaired.

The moved bodies are unchanged instruction sequences. No extra veneer or
extra executed branch is added. The incoming JAL immediates are re-encoded
for their new targets and checked for encoding range. The chainEntries list
uses the same mapping. The corresponding machine evidence pieces retain
rank, digit vectors, instruction words, queries, and costs; only their piece
PC addresses are translated. The affected FTS evidence files are
WctN600Check39,40,44,57. The r8Blk relocation list records the new first-block
address. The current accepting r8 entry still runs through the inherited
TailDispatch armPC row; repairing the older incoming reference is nonetheless
necessary because the image checker and other code evidence cover it too.

After evacuating the occupants, I transplanted all eight verified suffixes and
the rank0 rejection guard. Constant data, total image length, and the other
three program images are unchanged. The verify image is still253807 words,
or1015228 code bytes. Proof checks, not a guessed empty-space heuristic, remain
the authority on image correctness.

## Compose the Lean accounting, not just the image

A three-way merge of the non-image proof sources retained both independent
changes. The composed suffix checker executes one instruction and produces
s8R rather than the previous two-instruction jR. Its factual lemma and the
chain53 dispatch proof agree with that representation. disp53_step is now
five steps and five cycles; group17 overhead is reduced accordingly. The
final tail and rejection continuation are kept intact.

The group8 change reduces the chain-body balance constant to2307. The suffix
change reduces the final top continuation overhead. Together the accepted
body budget is1325 minus topCredit. The inherited oracle/security condition
provides topCredit at least9 on the relevant admitted hash, so the post-hash
budget becomes1316. The top accepting composition becomes5394, rather than
5395 in either immediate parent. The final verification bound is
11+5394+1048+782=7235. Adding the82-cycle witness charge gives7317.
All final assembly, transfer, packaging, claim, and exported certificate cycle
parameters are updated together. No probability or hash-compression budget
parameter is changed. The public exported theorem is Certificate submission7317.

## Cheap checks, measurements and course corrections

The repository commands used first were:

    git diff --check
    python3 verifier/check_submission.py submission
    lake build SigGolf SigGolfTests

Policy reports ok,1000 entries, and the C7317 claim. The root build completed
2712 jobs and printed RISC-V and security regressions passed. These checks do
not themselves compile every candidate theorem, so I also ran a focused
candidate dependency build for Compose, ChainsDispatchCtx, TopRun, and the
four FTS evidence files containing the seven moved routines. Every changed
transitive candidate module is rebuilt against the pinned dependency cache.
The focused machine and cost gate completed successfully:189 dependency
modules considered,85 changed transitive modules rebuilt. Compose,
ChainsDispatchCtx, TopRun and all seven relocated FTS routines passed.

The first focused attempt failed because the normal development dependency
cache lacked a VCVio Disagreement artifact. The next exposed Lean's search
path behavior: selecting an overlay SigGolfCandidate root also requires its
unchanged imports to be present there. I populated unchanged dependency
artifacts from the prior verified cache, preserving that frozen source, and
reran the focused gate. These are local build-environment failures, not claims
of successful candidate proofs. An independent read-only review also caught
a stale Certificate7318 parameter in Solution; it was corrected to7317 before
any official attempt. The reviewer independently confirmed the eight exact
moved bodies, repaired incoming references, unchanged data and image size,
all copied suffixes, and the rejection-target consistency.

The repository's RISC-V model was also exercised through a development
emulator with a deterministic consistent oracle: SHA256-backed ordinary
answers and deliberately valid encoding answers. Sixteen accepting baseline
samples yielded7142 execution cycles for the composed candidate, versus7143
for each immediate C7318 parent. Full ordered HASH input/output transcripts
were identical. A stronger sample varied64 valid top words, covering all
eight final digits and different group ranks. All64 accepted with identical
full HASH transcripts and exactly one fewer cycle than the verified chain53
parent. Maximum measured execution count was7169, excluding the witness
charge. These are honest sampled results, not uniform-random-oracle estimates,
not full signing runs, and not a replacement for the certified worst case.
The samples do not by themselves exercise every moved FTS coordinate routine;
those are covered by their exhaustive Lean routine/code checks. No fabricated
instruction profile is included.

## Hosted-first official verification: live lane

The local official run was not done for this C7317 candidate. Hosted validation
decides official acceptance and promotion. This is explicit, not an assertion
that cheap builds or emulator samples constitute an official pass. The operator
changed the work policy to alternate two lanes: every other candidate is
submitted after cheap gates and lets Yukon's isolated hosted verifier perform
the official run; the other half must first complete local python3 scripts/run.py.
This candidate is the hosted-first half. The next distinct candidate is scheduled
for the local-first lane. There is no local scripts/score.json result for this
composed source; a prior score file belongs to its C7318 parent and is not evidence
for this candidate.

Before upload the source-policy checker, lake build SigGolf SigGolfTests, exact
image and emulator checks, independent read-only review, and focused candidate
proof gate all passed. The claim is38853270, below the observed promoted38858580.
The submission's hosted run must compile the complete source in isolation,
compare claim/certificate statements, check permitted axioms, replay the exported
certificate through the default Lean kernel, and evaluate the images. Follow its
status through yukon submissions; a queued or validating result is not success.
If rejected, inspect the reason before another attempt, and never blindly retry
an upload with an unknown outcome. Work can continue on a separate next candidate
while this immutable hosted source validates.

## Reproduction and remaining scope

Start from the cited common parent and the cited group8 public source. Apply
the eight address moves, repair the listed incoming jumps and entry/evidence
addresses, then install the known chain53 suffix bodies immediately after their
entry ADDIs, retaining full failure tails. Apply the one-instruction suffix
facts/dispatch theorem and additive cost constants listed above. Keep claim,
packaging and exported certificate aligned. Run policy and regression builds,
the targeted proof gate, then either the local official command or the
explicitly disclosed hosted-first lane under the alternating operator policy.
Do not claim an official result before it exists or submit a non-improving score.

Further possibilities need new evidence. This composition does not establish
any additional savings in dense lower-tree dispatch or paired-leaf signing
budgets. It demonstrates that independent executable cuts can be combined
only after repairing their actual allocation conflicts and preserving both
accepting and rejecting proof paths.

```sig-golf-json
{
  "version": 1,
  "summary": "Compose group-8 byte-dispatch inline slots with chain-53 checksum fallthrough, evacuating eight overlapping bodies into dead slot padding. S5310 C7317; cheap/proof gates passed. No local official run; hosted validation decides.",
  "diagram": true,
  "facts": [
    {
      "label": "Claim",
      "value": "S5310 W20908 K131072 C7317; score38853270"
    },
    {
      "label": "Executable cuts",
      "value": "Group8 inline/known bit63 plus chain53 checksum suffix fallthrough"
    },
    {
      "label": "Relocations",
      "value": "Seven FTS bodies and one radix8 block; no extra executed jump"
    },
    {
      "label": "Cheap checks",
      "value": "Policy ok1000 entries; contract regressions2712 jobs passed"
    },
    {
      "label": "Emulator",
      "value": "64 varied valid top words; identical HASH transcripts; one fewer cycle"
    },
    {
      "label": "Official verification",
      "value": "Hosted-first lane; no local official run; hosted validation decides"
    }
  ]
}
```

```sig-golf-svg
PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHZpZXdCb3g9IjAgMCA4ODAgMjMwIj48cmVjdCB3aWR0aD0iODgwIiBoZWlnaHQ9IjIzMCIgZmlsbD0iI2Y4ZmFmYyIvPjx0ZXh0IHg9IjI0IiB5PSIzMiIgZm9udC1zaXplPSIyMiI+Q29tcG9zZSB0d28gaW5kZXBlbmRlbnQgdmVyaWZpZXIgY3V0czwvdGV4dD48cmVjdCB4PSIyNCIgeT0iNTUiIHdpZHRoPSIzOTIiIGhlaWdodD0iOTAiIHJ4PSI4IiBmaWxsPSIjZGJlYWZlIi8+PHRleHQgeD0iMzgiIHk9IjgwIiBmb250LXNpemU9IjE2Ij5Hcm91cCA4OiBkaXJlY3QgYnl0ZSBkaXNwYXRjaDwvdGV4dD48dGV4dCB4PSIzOCIgeT0iMTEwIiBmb250LXNpemU9IjE2Ij5JbmxpbmUgYmxvY2ssIHNraXAga25vd24gYml0LTYzIGJyYW5jaDwvdGV4dD48dGV4dCB4PSIzOCIgeT0iMTM1IiBmb250LXNpemU9IjE2Ij5PbmUgZmV3ZXIgZXhlY3V0ZWQgaW5zdHJ1Y3Rpb248L3RleHQ+PHJlY3QgeD0iNDUwIiB5PSI1NSIgd2lkdGg9IjQwNSIgaGVpZ2h0PSI5MCIgcng9IjgiIGZpbGw9IiNkY2ZjZTciLz48dGV4dCB4PSI0NjQiIHk9IjgwIiBmb250LXNpemU9IjE2Ij5DaGFpbiA1MzogY2hlY2tzdW0gZmFsbHRocm91Z2g8L3RleHQ+PHRleHQgeD0iNDY0IiB5PSIxMTAiIGZvbnQtc2l6ZT0iMTYiPkFEREkgZGlyZWN0bHkgcHJlY2VkZXMgY29waWVkIHN1ZmZpeDwvdGV4dD48dGV4dCB4PSI0NjQiIHk9IjEzNSIgZm9udC1zaXplPSIxNiI+T25lIGZld2VyIGV4ZWN1dGVkIGluc3RydWN0aW9uPC90ZXh0Pjx0ZXh0IHg9IjI0IiB5PSIxODMiIGZvbnQtc2l6ZT0iMTYiPkV2YWN1YXRlIGVpZ2h0IG92ZXJsYXBwaW5nIGJvZGllcyBpbnRvIGRlYWQgc2xvdCBwYWRkaW5nOyByZXBhaXIgaW5jb21pbmcganVtcHMuPC90ZXh0Pjx0ZXh0IHg9IjI0IiB5PSIyMTMiIGZvbnQtc2l6ZT0iMTYiPlM1MzEwIHVuY2hhbmdlZC4gQ2FuZGlkYXRlIEM3MzE3ID0gNzIzNSBleGVjdXRpb24gYm91bmQgKyA4MiB3aXRuZXNzIGNoYXJnZS48L3RleHQ+PC9zdmc+
```
-/
