import SigGolf
import SigGolfCandidate.Packaging.Ready

namespace SigGolf.Challenge

def submission : SigGolf.Submission := SigGolfCandidate.Transfer.currentOf SigGolfCandidate.T3M.submission

theorem signature_bytes : submission.sizes.signature = 5310 := rfl

theorem witness_bytes : submission.sizes.witness = 24828 := rfl

theorem cache_bytes : submission.sizes.cache = 131072 := rfl

theorem layout_offsets : submission.layout =
  { message := 26048, secretKey := 128, publicKey := 160,
    cache := 524288, signature := 28672, witness := 1216 } := rfl

theorem certificate : SigGolf.Certificate submission 7095 := by
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

Compact leaf buffers (Claude Opus 5.5, base 2e294772, C 7098): the layer-3 and layer-2 leaf buffers
drop their 16-byte tail pads (stride 736 -> 720; a lower-layer leaf hash reads 704 bytes and its last
chain hash spills 16), so the layer-1 and top buffers, the tail `rho | 0 | dc` and the message move
down by 32 bytes (message 26080 -> 26048). The verifier changes only the 128 lower-layer transition
immediates `addi tp,tp,736 -> 720` and the digest-block data word; verify cycles are unchanged
(bound 7000) and the witness charge drops 98 -> 97.
S = 5310, W = 24828, K = 131072, C = 7097; score 37685070.

Plus the layer-3 entry hand-off (leader fca15315, ported): coordinate 8 leaves the fold hand-off
`a2 = 1200 or 1344` (FtsOut.a2), nothing reads those bytes after the L3 encoding, so the L3 entry
drops `addi a2,s0,-176` and the L3 encoding hash writes there; the digest is read a2-relatively.
After-FTS budget 5272 -> 5271; verify bound 7000 -> 6999.
S = 5310, W = 24828, K = 131072, C = 7096; score 37679760.

Plus a shorter coordinate-8 dispatch: coordinate 2's `lui tp, 127 <<< 20` replaces its `andi` and computes
`t6 = (a6 >> 1) & tp` (the child index already at bit 20) with the child routine at `(t6 >> 12) + t4`; coordinates
3..7 keep the child index in `s7` instead of `tp`, so `tp` still holds the mask at coordinate 8, which drops its
`andi`/`slli` pair to 10 words. Its children return to word 850 and the layer-3 entry run moves 851 -> 850 (trap
870). The chain/child routines never read `tp`, so their contracts drop the child-index field. FTS fixed cost
928 -> 927; verify bound 6999 -> 6998.
S = 5310, W = 24828, K = 131072, C = 7095; score 37674450.
-/
