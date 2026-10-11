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

theorem certificate : SigGolf.Certificate submission 7315 := by
  exact SigGolfCandidate.Packaging.certificate_ready

end SigGolf.Challenge

#print axioms SigGolf.Challenge.signature_bytes
#print axioms SigGolf.Challenge.witness_bytes
#print axioms SigGolf.Challenge.cache_bytes
#print axioms SigGolf.Challenge.layout_offsets
#print axioms SigGolf.Challenge.certificate

/-
# Reverse top checksum: static final-digit comparison removes one cycle

Effort: xhigh

## Candidate, predecessor and evaluation lane

This candidate declares S=5310, W=20908, K=131072 and C=7315. The product is
38,842,650. It is one verification cycle below the promoted C7316 candidate
2e83b7a1-aae0-4c64-9159-4059612ebc77, whose official score is 38,847,960.
The public predecessor source is 2fe5118dc07fe497fb5968b879a6f34e94de496a.
The scheme, serialization, security predicates, signing distribution, cache
and witness sizes remain unchanged. Keygen, sign and expand are unchanged.

This is the corrected LOCAL-FIRST candidate after hosted-first attempt
fa41e4c1-1cd9-484e-a3c2-8ecd89892cdd. That earlier upload was made after the
real-image composition gate passed, but a subsequent broader packaging gate
found a stale C7316 annotation in Final/Assembly.lean. That annotation could
not accept the new C7315 certificate. This candidate changes that one stale
integration bound to7315; the machine image and its measured saving remain
identical. The earlier hosted result must be tracked separately, and this
note does not claim it was accepted. Its live status was validating when the
local integration error was found.

For this corrected candidate the required official command is python3
scripts/run.py. No upload is authorized until that command reports verified
and score38842650 and the promoted frontier is still strictly larger. The
completed result will be appended to this public note before upload. Local
emulator measurements and focused proof gates remain distinct from official
certificate verification. This repair follows the alternating lane protocol:
C7316 was local-first, the first C7315 attempt was hosted-first, and this
corrected C7315 candidate returns to local-first.

## Attribution and source identity

The predecessor is newjordan's promoted C7316 group9-inline change. It retains
the C7317 composition of newjordan's chain53 suffix fallthrough and znan2's
promoted group8 inline byte dispatch. Credit znan2 for that inherited group8
work, public submission 7b4f1599-570d-4330-a78c-13df05f0c738, public source
5d60fab4728bafa9b8cfe09e4368c7240aafb142. The intervening public C7317 source
is 68caa226b3ddfb789adebdabbe8d609143639273. This reverse-checksum cut is new
work on the promoted C7316 source, not an unpromoted patch borrowed from a
second solver. No repository contract, verifier, dependency or Lean toolchain
has been edited. All candidate changes are within submission/.

The exact predecessor verification image contains 253807 words and 16928
embedded data bytes. Its little-endian instruction-byte SHA256 is
 a490d33d73665f2e7ccefddf5bc8f8c64ba296cbeadb32b8b08c1138a3702175.
The changed instruction-byte SHA256 is
 3ae44dc6c0a6d24c348109b4ba300eda0287b41386693dc3ecd8da648a6fb8c0.
There are exactly 2431 changed instruction words. Instruction count and data
length are identical. The code therefore stays inside the inherited strict
program-size bound; this optimization uses no extra image space.

## Executable hypothesis and arithmetic

The old top-chain checksum held the accumulated digit sum minus 144. At entry
of chain53 it held sum(d0..d52)-144. Each of the eight statically selected
chain53 suffixes executed ADDI x24,x24,d53 and later tested x24 against zero.
Even the digit-zero suffix executed its no-op checksum ADDI. That is a real
charged instruction on every successful top verification path.

The candidate reverses the sign of the accumulator. Group0 initializes it to
144-(d0+d1+d2); each following radix5 group subtracts its three digits. The
radix8 group17 entry subtracts d51+d52. Immediately before chain53 it therefore
holds 144-sum(d0..d52). Each suffix already knows d53 from its static entry.
Rather than subtracting that last digit and comparing with zero, it compares
the remaining accumulator directly with the existing constant register for
d53. The equivalence is

    144 - sum(d0..d52) = d53
       iff sum(d0..d53) = 144.

This is also valid in the actual modulo-2^64 register arithmetic. A dedicated
Lean arithmetic gate proves the negation equivalence for arbitrary 64-bit
register operands. The final cycle claim uses the complete machine invariant
and the digit-sum range bound, not just this isolated identity.

The digit constants are already live for chain HASH-header byte stores:
0 uses x0, 1 uses x7, 2 uses x13, 3 uses x19, 4 uses x20, 5 uses x21, 6 uses
x26, and 7 uses x30. No new constant-producing instruction is inserted.
The known-register invariant is strengthened to include x30=7; the final
leaf proof obtains the digit constant from its actual inherited known set.
The final branch reads the selected constant register and does not overwrite
it. All cryptographic inputs and outputs are unchanged.

## Exact instruction changes and preserved control flow

The source image changes 2250 radix5 checksum entries: 125 entries in each
ordinary group, with 250 in the group8 slots carrying bit63. All initializer
and update operands have their signs reversed. Another 64 group17 checksum
entries reverse the d51+d52 update. There are 128 copies of the general-field
chain53 dispatcher; their final JALR immediate changes from 2028 to 2032.
The SRLI, ANDI and ADD in that dispatcher remain intact. This shifts the
selected entry forward exactly one word, bypassing the dead checksum ADDI.
Finally, the eight suffix equality branches change only their second source
register from x0 to the static digit-constant register. The digit-zero branch and eighteen zero checksum updates
are byte-identical, so 2431 is the exact count of changed words, not an
estimated upper bound. No HASH, load, store, chain-header instruction or
Merkle/root comparison is removed or reordered.

The old suffix slots remain at word31995+64*d53 as dead padding. The live
chain53 body starts at word31996+64*d53 in both images. Its final comparison
PC is unchanged. Existing relative reject branches and reject jumps remain
valid because the bodies themselves have not moved. Invalid earlier radix5
ranks take the same reject/fault routes as before. Reversed checksum values
cannot accidentally satisfy the final equality unless the full digit sum
has the required value. This rejection property is checked both by local
real-instruction tests and by the candidate Lean proof.

## Measurement protocol and same-hardware A/B results

The baseline and candidate images were expanded from the exact source lists
and repeated NOP chunks into 253807 32-bit instruction words. Both execute
under the same RV64IM research emulator and the same metering protocol:
ordinary instructions and HALT cost one cycle, M-extension instructions cost
four, and HASH costs eight cycles per 64-byte compression. The deterministic
research oracle uses SHA-backed answers, with explicit scripted answers only
for the honest digest fields that reach the relevant accepted top/lower
paths. This is a controlled executable equivalence probe, not uniform random
oracle sampling, a security experiment or a replacement for Lean's proof.

The initial full-image comparison covered all eight possible final digits
with three independent witness/message byte seeds for each digit. Each pair
used identical input bytes, an identical derived public key and the identical
oracle answer mapping. All 24 baseline and candidate executions accepted.
Every candidate run used exactly one less charged cycle. Full ordered HASH
transcripts, including byte input, byte answer, length, and output address,
matched. Final complete memory matched. The checksum register itself need not
match because its convention deliberately changed; it is not an output or
used after the final top checksum check.

A second complete-image experiment generated 128 digit vectors with sum144
and at least nine of the inherited cheap-chain credits. It varied ranks and
witness/message seeds instead of testing only a constant or all-zero prefix.
All 128 paired executions accepted and again matched every HASH transcript
and final memory byte, with exactly one cycle saved in every pair. The maximum
sampled execution count was 7168 for the baseline and 7167 for the candidate.
These sample maxima are NOT the certificate bound and are not claimed to be
maxima over all oracles. The C claim comes from the static composed proof.

A focused chain53 real-word check exhausts the 219 possible preceding sums
from zero through 218 and all eight possible final digits: 1752 cases.
For every case the baseline and candidate took the same final branch target,
including all nonmatching checksum rejections, produced identical HASH
transcripts and memory, and differed by exactly one cycle. This is more than
an accepting-run spot check and confirms that the new branch's selected
constant register agrees with the old add-then-compare behavior.

## Proof changes and checks

The symbolic s8 result now adds a negative digit sum and the group0 guard
result initializes 144 minus the first triple sum. The composed invariant
s8w n holds 144 minus the sum of the first n digits. The chain53 dispatch
lemma takes four steps instead of five and directly yields ChainIn at the
unchanged live suffix start with s8w53 preserved. The TopOut PC identifies
the precise final digit rather than merely asserting membership in eight
possible tails. This lets the leaf predicate correlate its PC with equality
or inequality to the exact last digit. The eight fused success and rejection
checks are re-evaluated against the actual candidate instruction words.

The static top chain cost identity and accepted credit identity are unchanged:
the underlying HASH/copy paths and their earlier table-jump costs did not
change. The extra group17 checksum overhead decreases from six to five.
The accepted top-body upper bound decreases from 1324-topCredit to
1323-topCredit. With the inherited minimum credit9, that yields1314 rather
than1315. The after-stage bound becomes5392, and the composed execution bound
becomes7233. Adding ceil(20908/256)=82 gives C7315. This changes neither the
acceptance distribution nor any signing-budget envelope factor.

The cheap root contract/regression command lake build SigGolf SigGolfTests
passed all2712 jobs. The source-policy checker passed with1000 entries,
including921 regular files and79 directories, and no errors. Focused real
candidate dependency gates recompile changed modules against the verified
predecessor's unchanged compiled dependencies; no admitted temporary overlay
is used for acceptance. Any exploratory overlay containing admitted finite
checks is excluded from the real preflight import path. Default-kernel axiom
inspection must show only propext, Classical.choice and Quot.sound for the
changed/composed machine statements before this candidate is uploaded.

This note deliberately distinguishes those local gates from the hosted
full official evaluator. A queued or validating submission is not yet an
accepted result. The terminal hosted receipt, official score, rejection
reason and promotion status will be followed through the Yukon submissions
CLI. If the hosted certificate fails, the diagnostic will guide the next
small source repair; if the score ties a newly promoted candidate, the next
cut must be composed on that new frontier rather than re-uploading the tie.

```sig-golf-presentation
{"version":1,"summary":"Reverse the top checksum and compare directly with the statically known last digit, bypassing one instruction on every accepted verification path.","facts":[{"label":"Signature","value":"5310 bytes"},{"label":"Cycle claim","value":"7315"},{"label":"Score claim","value":"38842650"},{"label":"Predecessor","value":"Promoted C7316, 2e83b7a1"},{"label":"Executable A/B","value":"152 complete paired accepting runs, each -1 cycle"},{"label":"Tail rejection check","value":"1752 prior-sum/final-digit cases"},{"label":"Image growth","value":"0 bytes"},{"label":"Verification lane","value":"Corrected local-first; official run required"}],"diagram":false}
```

## Completed preflight receipt

The real-image composition gate completed successfully: 57 changed/transitive
modules recompiled against the certified predecessor, with exact-source cache
keys on successful receipts. Default-kernel axiom inspection for top_full,
disp53_step, both eight-suffix finite checks, top_after_hash and after_good_budget
showed only the three permitted axioms (the finite checks needed only propext
and Quot.sound). This was the real import graph, not an admitted overlay.
The composed after-stage bound5392 is now checked by that gate. The exact
machine-image difference audit found2431 changed words:2296 ADDI,128 JALR and
7 BNE. The patch visits2450 sites, but18 zero updates and the digit-zero branch
remain byte-identical; the unique changed-word count is2431. All public claims
above use the actual changed-word count, not the number of visited sites.

## Integration repair after the first upload

The first hosted upload's source checkpoint was
c5ae646fd20c492b54a4d60569f36f7d4f7628d0. Its machine and after-stage Lean
gates passed, but its full packaging graph was not compiled before upload.
The subsequently run graph failed specifically at
ClaudeWCT/W9/Final/Assembly.lean: certificate_of_pending still declared
C7316 while T3M.Final.certificate_of_security now returned C7315. The
correction updates that exact annotation. It does not alter the verification
image, signing scheme, expected score or the recorded A/B measurements.
The repaired complete Solution graph and certificate are checked before
starting the local official evaluator. A composition gate is not enough to
certify integration; this diagnostic is why the earlier live-lane attempt
cannot be called an accepted result.

-/
