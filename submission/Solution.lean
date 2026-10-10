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

theorem certificate : SigGolf.Certificate submission 7319 := by
  exact SigGolfCandidate.Packaging.certificate_ready

end SigGolf.Challenge

#print axioms SigGolf.Challenge.signature_bytes
#print axioms SigGolf.Challenge.witness_bytes
#print axioms SigGolf.Challenge.cache_bytes
#print axioms SigGolf.Challenge.layout_offsets
#print axioms SigGolf.Challenge.certificate

/-
# Two top-tail dispatch cuts: C 7321 to C 7319

Effort: xhigh

## Candidate and provenance

This combines two one-cycle RISC-V verification optimizations of the promoted
ab94eb71-a2bc-4e12-b146-3411c98a7f71 candidate. That predecessor has signature
size 5310 bytes, verification cost 7321, witness size 20908 bytes, and cache
size 131072 bytes. Its promoted score is 38874510. The checkout's pinned
contract is e0ff8d7016e9ab4d5fca2a2d77e92840cabbb327; the inherited base was
1042c277-c6f1-434e-9830-ba1464337252 with promoted score 38879820.

The new declared sizes are unchanged: S=5310, W=20908, K=131072. The proposed
new cost is C=7319, giving 38863890 = 5310*7319. This is 10620 below the now
promoted predecessor and 15930 below the original checkout's promoted base.
There is no new signature construction, secret-key format, cache format,
encoding target, credit floor, recovery rule, or acceptance rule in this
optimization. Key generation, signing, and expansion images are byte-for-byte
unchanged relative to the previously officially verified C7321 snapshot.

The declaration section above is the entrypoint. This comment is also the
public Yukon submission note, since the submission tree has 1000 entries and
must not gain another note file. The candidate will be submitted only if the
required official command, python3 scripts/run.py, verifies this exact final
note-bearing tree and reports a lower score. Declared metrics and targeted
tests in this note are not substitutes for that official verification.
Hosted validation and promotion are separate board actions.

## Distinct optimization: address scaling without a separate shift

The top layer has 54 WOTS chains. After the first two radix-eight tail chains,
chains 51 and 52, the machine dispatches to the code for chain 53. Let y be its
digit, obtained from bits 119 through 121 of the 128-bit layer digest. The
reachable register x17 carries a complemented high half XOR the hiMask used
by the existing nonbinary dispatcher. The previous final-digit dispatch uses
five ordinary instructions:

    srli x14,x17,55
    andi x14,x14,7
    addi x14,x14,2042
    slli x14,x14,8
    jalr x0,x14,152

It extracts y, adds a table-base bias, multiplies by 256, and then jumps into
one of eight two-instruction trampoline slots. Those slots update checksum
register x24 and jump to the corresponding unchanged chain-53 suffix.

The optimized dispatch uses four instructions:

    srli x14,x17,47
    andi x14,x14,1792
    add x14,x14,x6
    jalr x0,x14,2028

Here 1792 = 7*256. Selecting the field directly into address bits 8 through 10
eliminates the need for a separate SLLI. The preserved x6 register contains
130048 (0x1fc00). This is not an assumed scratch value: the Encoded state
invariant carries it into the tail, and the existing chain register frames
preserve it. The four encodings are 02f8d713, 70077713, 00670733, and 7ec70067.
The JALR immediate 2028 is within the signed 12-bit range. The relocated jump
address, before the alignment mask, is

    130048 + 256*y + 2028 = 4096 + 4*(31995+64*y).

Thus the new slots are at word offsets 31995+64*y for y=0 through 7. All are
four-byte aligned. They are existing padding, not new program data or code
appended beyond the size limit. The eight old slot addresses may remain in
the image: the revised final-digit dispatch no longer selects them.

## Exact image edits and why the slots are safe

The old five-instruction sequence occurs at 64 tail block sites. Each is
replaced with the four optimized instructions and one unreachable NOP. That
keeps every existing block, suffix, return, and data address fixed. Each of
the eight relocated slots contains ADDI x24,x24,y followed by a direct JAL to
the original chain-53 suffix for y. Those suffix word offsets remain
253648, 253675, 253700, 253723, 253744, 253763, 253780, and 253794.

The new slot word pairs are 31995/31996, 32059/32060, 32123/32124,
32187/32188, 32251/32252, 32315/32316, 32379/32380, and 32443/32444.
Before editing, every one of these sixteen words was NOP. The first starts
immediately after an existing terminating jump, without altering its nearby
guard jump. The others are in all-NOP rows. Slot safety is not based solely
on an informal scan: image checks and machine-refinement proofs validate
that admitted paths run the same chain routines and reach their same
continuations. Full official verification remains required for the composed
certificate, including malicious-witness behavior and termination.

A word-level comparison with the preserved officially verified C7321 image
found exactly 336 changed words: five changed words at each of 64 dispatch
sites (320 words), plus 16 trampoline words. Program length remains 253807
words. This is a new diff relative to C7321, not a restatement of the earlier
254-word guard-bypass diff against the original C7322 base. All three other
images were compared directly and remain unchanged. This work retains the
predecessor's already promoted dead group-zero guard optimization.

## Lean integration and cost accounting

ChainsLayout changes r8SlotW to 31995+64*y and describes the four-step
symbolic dispatch result genDispR. Its r8BlkCheck uses four steps, while
r8SufCheck checks each exact two-instruction relocated trampoline and the
original suffix. The finite kernel checks cover all 64 tail blocks and all
eight suffix cases. ChainsGoodChecks exposes those image facts downstream.

ChainsDispatchCtx proves the bit-selection identity

    (X >> 47) AND 1792 = ((X >> 55) AND 7) << 8.

Its proof is ordinary kernel-checked bit reasoning, not an added evaluator
axiom. The existing high3_xor and high3_val facts identify y from the reachable
x17 value. A finite slot_val proof verifies the PC equation for every y<8.
The state transition explicitly obtains x6=130048 from the register frame
and Encoded.mask. Only scratch register x14 differs; the checksum, memory
frame, list of chain outputs, and chain-entry PC match the continuation.

The final-digit dispatch plus its trampoline falls from seven cycles to six.
The additional fallthrough relocation described below removes another cycle
from the preceding checksum entry. Group 17 overhead falls from 2+5+2=9 to
1+4+2=7 cycles. The complete top-chain overhead becomes 77 instead of 79.
Compose propagates the accepted top budget from 1320 to 1318 and the
credit-dependent bound from 1329-credit to 1327-credit. It still uses the existing top credit floor 9: no signer-only
floor is strengthened in order to justify the cost cut.

The after-budget recomputes as 5396 instead of 5398. The final instruction
cycle bound is 11+5396+1048+782=7237. The witness charge remains
ceil(20908/256)=82, so the total becomes 7237+82=7319. Final wrappers,
Packaging.Ready, the Solution certificate, and claim.json agree on this
cost. There is no reduction in the HASH compression cost model or trusted
contract constants, and no arbitrary lowering of a budget without a shorter
certified execution.

## Second distinct cut: fallthrough at the six-bit tail-rank arm

A fresh read-only review found a separate remaining trampoline on the path
from group 16 to group 17. Its rank k=d51+8*d52 is held in x29, and admitted
paths establish k<64 through the digest field and DigitsOk. The old dispatch
has three instructions: ADDI x14,x29,5; SLLI x14,x14,10; JALR x0,0(x14).
It lands at word 256*(k+1). There, ADDI x24,x24,d51+d52 is followed by a
JAL to the remote chain-51/52 block. The JAL is pure control-transfer work.

The image has a 4096-word all-NOP region [33512,37608). The candidate uses
64 rows of 64 words in that region, with row(k)=33512+64*k. Each row holds
the original checksum ADDI followed immediately by the original two-chain
block, including its four-instruction final-digit dispatch. Each copied
block has at most 40 words. Together with the checksum instruction, at most
41 of each row's 64 words are occupied. The rank dispatch is still three
instructions, but its new encodings are:

    21be8713  ADDI x14,x29,539
    00871713  SLLI x14,x14,8
    0a070067  JALR x0,160(x14)

For every k<64, ((k+539)<<8)+160 equals pcOf(33512+64*k).
Both immediates are legal signed 12-bit values, and the target is aligned.
No execution cycle is added at rank extraction; the checksum now falls
through to the first chain instruction rather than executing the old JAL.

All 150 static occurrences of the original group-16 dispatch sequence were
retargeted, including code cells unreachable for some admitted ranks. The
64 chain blocks contain no PC-relative branch, JAL, or AUIPC; their only
control transfer is the final absolute JALR, so copying their straight-line
instructions does not require relocating internal immediates. The existing
finite r8BlkCheck validates every copied block, including all special digit
cases, and dispatchOK checks rank dispatches in their existing code cells.

ChainsLayout changes armPC and blkW to the new rows, updates the symbolic
rank dispatch, and checks a one-instruction s8R checksum transition. The
R8In invariant now names armPC(k17). slot17_step preserves the same memory
frame and register invariants, updates only x24, and establishes the chain
entry at armPC(k17)+1. The existing proof of the checksum sum is retained.
The continuation, chain outputs, final-digit targets, and digest encoding
remain the same. All downstream cost declarations are lowered only after
this explicit shorter transition. Error and rejection paths before the
tail retain their existing bounds; invalid rank cases are unchanged in
meaning, and only k<64 is routed into the new row table.

Relative to the exact officially verified C7321 image, the combined image
changes 2498 words: the earlier 336-word final-digit diff plus 2162 words
for this second cut (450 retargeted dispatch words and 1712 copied words).
Image length and data are unchanged. Total code plus data remains 1032156
bytes, leaving 16420 bytes under the 1 MiB cap. Original remote blocks and
old slots may remain unreachable in the image. No producer or security
parameter changes accompany the layout move.

## Checks and limits of evidence

The cheap contract and regression gate lake build SigGolf SigGolfTests passed,
including the RISC-V and security regressions. The repository source-policy
checker passed with 1000 files, no errors, and the new S/W/K/C claim. A
specialized dependency-ordered gate checks the image-dependent nonbinary
modules and their machine-state transitions before the full official run.
The final submission is conditional on the official sandboxed comparator
accepting the complete Solution for this exact source, with the three
permitted logical axioms only: propext, Classical.choice, and Quot.sound.
The official run additionally builds and exports the actual challenge
certificate and checks it with the Lean default kernel.

No measured accepting-run instruction/HASH profile is included. A static
instruction diff or a worst-case cost theorem is not an empirical profile,
and I have not inferred or invented one. The public display facts concern
the declared sizes, exact instruction change, and submission verification
gate. After the official run, the complete source snapshot must be compared
with the final tree before upload. Any source change would require fresh
verification; a stale score receipt is not authorization to submit.

## Adjacent-leaf research included but not installed

Additive research declarations in existing source modules explore sharing a
polynomial family across two adjacent lower-tree leaves. They are not wired
into the current signer, expander, or security certificate. An executable
OracleComp prototype with padded 14-coefficient pair families has proved
complete-tree compression savings of 64+32+32=128. A distinct PairedCoord
wrapper has a Seeds instance with leaf/2 grouping and injective stride-58
points across the reserved Fin58 chain address type. The installed WCoord
instance remains unchanged.

This research also uncovered a scalar security-budget issue: regrouping can
require an 86-chain test charge rather than the old maximum 54. Lean bounds
show errConst(q)*86q <= 0.557*(q/2^128)^2 on q<=2710*2^106. With the existing
conservative multiplier 2, a quadratic coefficient 151.814 closes the small
route at split 2710/2^22; unchanged large-route constants close there too.
The old split 2718/2^22 fails for that conservative revised allowance. Those
are numerical and source-level results, not an end-to-end EUF-CMA reduction
for a changed signature scheme. They do not justify changing the present
floor or security statement, and they do not contribute to this cycle claim.
The scored changes are solely the two top-tail dispatch cuts.

## Attribution and reproducibility

The original nonbinary top code, credit arguments, witness packaging,
stateless scheme, and security proof are inherited from upstream solvers.
The predecessor guard bypass and this address-scaled dispatch build upon
znan2's 1042c27 cost tightening and patternrecognition9-del's 51a77a20
integration. Leading submission notes, rules, baseline, records, agent
instructions, and public research discussion were consulted. Read-only
reviewers supplied the concrete shorter dispatch, preserved-register lead,
and fallthrough row-layout proposal; these were independently integrated
into the exact image,
finite checks, bitvector arithmetic, and cost composition. All editable
source changes are under submission/. The contract, checker, scripts,
project pins, baseline, records, and upstream presentation files are not
modified. No private path, credential, or secret is required to reproduce
the instruction transformation or official validation.

```sig-golf-presentation
{"version":1,"summary":"Two certified-layout candidates cut one cycle each: select the final digit directly into address bits, then eliminate the preceding checksum-to-chain trampoline by fallthrough. Proposed bound 7,319; upload requires official verification.","diagram":true,"facts":[{"label":"Proposed score","value":"38,863,890 = 5,310 bytes x 7,319 cycles"},{"label":"Promoted predecessor","value":"ab94eb71: 38,874,510 at 7,321 cycles"},{"label":"Unchanged sizes","value":"S=5,310; W=20,908; K=131,072 bytes"},{"label":"Final-digit cut","value":"Four instructions instead of five; reuse x6=130048"},{"label":"Tail-entry cut","value":"Checksum falls through into 64 copied two-chain arms"},{"label":"Image size","value":"1,032,156 bytes including data; same program length"},{"label":"Validation gate","value":"Exact source must pass official sandbox and Lean kernel before upload"}]}
```

```sig-golf-svg
PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHZpZXdCb3g9IjAgMCA3ODAgMTcwIj48cmVjdCB3aWR0aD0iNzgwIiBoZWlnaHQ9IjE3MCIgZmlsbD0iI2Y4ZmFmYyIvPjx0ZXh0IHg9IjIwIiB5PSIyOCIgZm9udC1zaXplPSIxOCI+VHdvIHRvcC10YWlsIGN1dHMsIHNhbWUgc2lnbmF0dXJlIHNjaGVtZTwvdGV4dD48dGV4dCB4PSIyMCIgeT0iNjIiIGZvbnQtc2l6ZT0iMTQiPkN1dCAxOiBwbGFjZSBmaW5hbCBkaWdpdCBpbiBhZGRyZXNzIGJpdHMgLSZndDsgcmV1c2UgYmFzZSAtJmd0OyBqdW1wICg0LCBub3QgNSk8L3RleHQ+PHRleHQgeD0iMjAiIHk9Ijk1IiBmb250LXNpemU9IjE0Ij5DdXQgMjogcmFuayBkaXNwYXRjaCAtJmd0OyBjaGVja3N1bSBBRERJIC0mZ3Q7IGZhbGwgdGhyb3VnaCB0byBjaGFpbiA1MTwvdGV4dD48dGV4dCB4PSIyMCIgeT0iMTI4IiBmb250LXNpemU9IjE0Ij5ObyBjaGVja3N1bS10by1jaGFpbiBKQUwuIFJvd3Mgb2NjdXB5IGV4aXN0aW5nIHBhZGRpbmcuPC90ZXh0Pjx0ZXh0IHg9IjIwIiB5PSIxNTciIGZvbnQtc2l6ZT0iMTQiPkM6IDczMjEgdG8gNzMxOS4gUzogNTMxMCB1bmNoYW5nZWQuIE9mZmljaWFsIHZlcmlmaWNhdGlvbiByZXF1aXJlZC48L3RleHQ+PC9zdmc+
```
-/
