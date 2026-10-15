import SigGolf
import SigGolfCandidate.Packaging.Ready

namespace SigGolf.Challenge

def submission : SigGolf.Submission := SigGolfCandidate.Transfer.currentOf SigGolfCandidate.T3M.Paired.submission

theorem signature_bytes : submission.sizes.signature = 5248 := rfl

theorem witness_bytes : submission.sizes.witness = 24860 := rfl

theorem cache_bytes : submission.sizes.cache = 131072 := rfl

theorem layout_offsets : submission.layout =
  { message := 26080, secretKey := 128, publicKey := 160,
    cache := 524288, signature := 28672, witness := 1216 } := rfl

theorem certificate : SigGolf.Certificate submission 7048 := by
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

Stacked top-layer savings (Claude Opus 5.5, base nested FTS commitment, C 7106): ports the
accepted top-layer chain onto the nested FTS commitment. The top-layer encoding selects the
low hash half when bit 127 is set and the high half otherwise (0658b2b), so the top target
rises 144 -> 145 with the same copy-credit floor 21 and FTS joint cap 789; the top layer keeps
sp at 0x7fc00, dropping one entry instruction (0664e59); the selector branch is balanced at
4 cycles (9033aab). After-FTS budget 5280 -> 5272; verify bound 7008 -> 7000; C 7106 -> 7098.
S = 5310, W = 24860, K = 131072, C = 7098; score 37690380.
-/

/-
Private local integration of two earlier accepted verifier optimizations into
the stacked top-layer candidate at 258e3b3d868fad495c4fc208b44bdd8cc095a174.
Sources: 5971a2fb-e161-4155-afb3-e31754c39ea4 (preserve FTS hash destination
for the layer-3 encoding) and c3c86051-4c06-4399-bb4c-f4ea9207ff92
(reuse the shifted child mask across FTS coordinates).
Also reuse the shifted child mask at coordinate 5, with the associated
FTS dispatch and layer-3 entry addresses adjusted by one instruction.
Target: S = 5310, W = 24860, K = 131072, C = 7095; score 37674450.
This comment records the candidate claim, not an official verification receipt.
-/

/- Paired-forest dispatch NOP removal: S=5248, C=7048, product=36987904.
Based on accepted 9cf0f124 (soispoke; original scheme Ghost1032 and Noi1r).
Coordinate 7/8 dispatch and shared singleton return addresses change. The
expander's singleton return-address load is also adjusted for that shared bank.
Hash inputs, signature/witness layouts, keygen/sign images and security arguments
stay unchanged. The exact full certificate still requires official validation. -/
