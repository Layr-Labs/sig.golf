import SigGolf
import SigGolfCandidate.Packaging.Ready

namespace SigGolf.Challenge

def submission : SigGolf.Submission := SigGolfCandidate.Transfer.currentOf SigGolfCandidate.T3M.submission

theorem signature_bytes : submission.sizes.signature = 5310 := rfl

theorem witness_bytes : submission.sizes.witness = 24908 := rfl

theorem cache_bytes : submission.sizes.cache = 131072 := rfl

theorem layout_offsets : submission.layout =
  { message := 26128, secretKey := 128, publicKey := 160,
    cache := 524288, signature := 28672, witness := 1216 } := rfl

theorem certificate : SigGolf.Certificate submission 7045 := by
  exact SigGolfCandidate.Packaging.certificate_ready

end SigGolf.Challenge

#print axioms SigGolf.Challenge.signature_bytes
#print axioms SigGolf.Challenge.witness_bytes
#print axioms SigGolf.Challenge.cache_bytes
#print axioms SigGolf.Challenge.layout_offsets
#print axioms SigGolf.Challenge.certificate

/-
FTS child-tree node tweak repack (Claude Opus 5.5, base d9d1ad90 = slot table, C 7310):
packed FTS node headers for heaps 8..127 carry the heap in the low word (`nodeLow - heap`,
byte0 = 257 - heap >= 130, byte1 = 5), so they are marked and `canonicalHeader` ignores
their high word (honest 0). The verifier writes the low word with one `addi gp,a5,-heap`
and, only when the computed child is the left input, `sd zero,24(a0)`; on right-input
levels the high word stays witness memory. Per-child saves rise (max 3 -> 5); joint cap
782 -> 785 keeps J above the old J (gate and layer targets unchanged).
C 7310 -> 7295; S, W, K unchanged.
Plus newjordan's chain-53 suffix fallthrough (c6744cc6) ported: r8 slots hold the copied
chain-53 suffix (guard k=0 at 32032). C 7295 -> 7294.
Plus newjordan's reverse top checksum (b9a59a77) ported: s8 accumulates the negated digit
sum, the r8 test is `bne s8,reg_y`, genDisp jumps straight past the dead slot addi. C 7293.

Mixed absolute-address dispatch (GPT 6 Astra, Codex): allocate lower triples at
1024-byte strides, retaining 512-byte strides for columns 1 and 8. Producer search
requires rank >= 3, or >= 5 in those two columns. Failed verification ranks stop
at the corresponding fetch fault; the source models the exact preceding queries.
The upper table uses 4096-byte strides and inlines group 9. C 7293 -> 7182.

Current submission compared with accepted cfc0c669 (C 7256): lower-layer digest-half
selection and copy-credit thresholds support the denser absolute-address dispatch.
A lookup-table precheck rejects impossible producer candidates before full unpacking;
the exact sign/expand cycle bounds and selected-half security bounds are certified.
S = 5310, W = 24028, K = 131072, C = 7182; score 38136420.

Nested FTS commitment (Claude Opus 5.5, base 05f6eb8, C 7182): each FTS tree's top pair
(L_c, R_c) is bound into tree c+1 instead of a 5-block forest hash. L_c fills every leaf's pad
slot of tree c+1 and R_c the pad slot of its two top folds (heaps 2/3, whose values are the high
half of their hash); tree 8's pair is the L3 message `.pair L8 R8`. The verifier drops the
forest hash and the nine sibling copies (FTS fixed part -85 cycles) and copies R9 into the L3
block (+4) and points a2 at the witness base (+1). The FTS region stride grows to 896 bytes, so
the witness starts at 1216 (W 24028 -> 24860, charge 94 -> 98). Joint cap 785 -> 789.
Verify bound 7088 -> 7008; C 7182 -> 7106.
S = 5310, W = 24860, K = 131072, C = 7106; score 37732860.

Spill-down Merkle children (Claude Opus 5.5, base 926c9bce, C 7106): every left child of the lower
(L1..L3) and top Merkle trees is the high half (bytes 16..32) of its hash answer and is written 16
bytes lower, so the unused half lands on consumed bytes instead of the parent's label. Each fold keeps
a single verifier-written label word (lower: t3 + heap - 1, root word t3; top: heap) and the 768 top
tag stores disappear; lower leaf chain 0 ends on the high half (header `sd zero` gone). FTS words take
coord+1 so every 64-byte query format stays disjoint for all pads; node projections are position-only,
so keygen/sign/expand/verify share one canonical tree and the Merkle proofs are projection-generic.
The L3 encoding header's high word becomes a witness pad and its answer is written where `a2`
already points (coordinate 8's last heap output; same elision as the parallel 5971a2fb). Net -29.
W 24860 -> 24908 (charge 98). Verify bound 7008 -> 6979; C 7106 -> 7077.
S = 5310, W = 24908, K = 131072, C = 7077; score 37578870.

Integrated top-layer bit-127 encoding and prefix changes (GPT 6 Astra / Codex),
following public ab5c824c and its cited top-layer dependencies: -8 cycles on S2.
S = 5310, W = 24908, K = 131072, C = 7069; score 37536390.

Combined S2 with public C1 (25d6f18f) FTS Merkle half selection and shifted child mask.
S2's already-present L3 a2 elision is counted once. Fixed FTS cost 918 and joint cap 776.
S = 5310, W = 24908, K = 131072, C = 7045; score 37408950.
Cap/gate retune on top of 8388f21d: joint cap 776 -> 775 (child table J re-derived, envelope
p0 = 1360 * J / 2^167) and gate 1353 -> 1360. Net -1 cycle; witness size unchanged.
S = 5310, W = 24908, K = 131072, C = 7045; score 37408950.
Integration: GPT 6 Astra / Codex; source authors and dependencies credited in the public note.
-/
