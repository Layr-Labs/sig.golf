import SigGolf
import SigGolfCandidate.Packaging_Ready

namespace SigGolf.Challenge

def submission : SigGolf.Submission := SigGolfCandidate.Transfer.currentOf SigGolfCandidate.T3M.submission

theorem signature_bytes : submission.sizes.signature = 5310 := rfl

theorem witness_bytes : submission.sizes.witness = 24828 := rfl

theorem cache_bytes : submission.sizes.cache = 131072 := rfl

theorem layout_offsets : submission.layout =
  { message := 26048, secretKey := 128, publicKey := 160,
    cache := 524288, signature := 28672, witness := 1216 } := rfl

theorem certificate : SigGolf.Certificate submission 7031 := by
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

L3 a2 elision (0xFredrik's 5971a2f, ported): the nested FTS already leaves `a2` at coordinate 8's last
heap output (`1200` or `1344`), so the L3 entry drops `addi a2,s0,-176` and the L3 encoding hash writes
there. Verify bound 7000 -> 6999; C 7098 -> 7097.
S = 5310, W = 24860, K = 131072, C = 7097; score 37684070.

Shifted child-index masking (Th0rgal's c3c8605, ported): coordinate 2 loads 0x7f00000 into x27, which
no FTS routine touches, so coordinate 8 extracts the child index already shifted left by 20 with
`srli x4,dig,1; and x4,x4,x27` and drops one shift. Coordinate 8 shrinks by one word, the L3 entry moves
to 850..868. FTS accept cost 928 -> 927; verify bound 6999 -> 6998; C 7097 -> 7096.
S = 5310, W = 24860, K = 131072, C = 7096; score 37679760.

FTS Merkle half-swap (C1): in each FTS tree a node at an even heap 16..255 (a left input of a packed fold
window, including the even leaves) takes the high 16 bytes of its hash output. A verifier child writes such a
node's hash at slot - 16, so the junk low half lands on a dead slot and the packed window's high tweak word is
never dirtied: every `sd zero,24(a0)` goes (new per-child windows in [0,320)). Child cost 27 - skips, child
saving 4 + skips (max 6), per-coordinate fixed part dispatchLen + 89, joint cap 776. FTS accept cost
927 -> 918; verify bound 6998 -> 6976; C 7096 -> 7074.

Lower-tree half-swap and witness pads (C2 + C3): in the lower trees (L1..L3) a left child (even heap, leaves
included) is the HIGH half of its hash and is written 16 bytes below its slot; each fold writes one marked tweak
word `hyperWord + 1407 + heap` whose high word is a witness pad (honest 0). The top leaf's leading 16 bytes, every
leaf tweak's high word and every encoding row tweak's high word (honest 1) are witness pads, and lower chain 0's
last step keeps the high half. W 24860 -> 24924 (message at 26144); after-FTS cost 5271 -> 5251; verify bound
6976 -> 6956; C 7074 -> 7054 (stacked on C1). Mechanism also certified in b3cc11b (credited dependency).
S = 5310, W = 24924, K = 131072, C = 7054; score 37456740.

Top-tree spill-down (C4): each of the 12 top Merkle folds writes one label word, its heap (in [1, 4096)); the
label's high word is witness memory (honest 0). A top left child (even heap, even leaf) is the HIGH half of its
hash and is written 16 bytes below its slot, as in the lower trees; the root (heap 1) stays the low half. The top
windows follow a 48-slot plan in two lines (levels 0..5 by leaf % 64, levels 6..11 by leaf / 64 % 64), and the
junk halves land on dead slots. One store fewer per fold (-12). Because a one-word top label has a small low word,
every FTS word takes the coordinate nibble c + 1 (one `add` in the verify prologue, +1), and the L3 encoding block
reloads s2 itself (`ld s2,-304(s1)`). After-FTS cost 5251 -> 5240; verify bound 6956 -> 6945; C 7054 -> 7043.
Design, keygen image and Lean templates from b3cc11b (nconsigny), which certified the same top design on its own
base (credited dependency); adapted to the C1 + C2/C3 base.
S = 5310, W = 24828, K = 131072, C = 7043; score 37398330.
-/

/-
Restricted top-layer digest-half choice (GPT 6 Astra, Codex), rebased from the
accepted #867 implementation onto C4 commit aac8166a. Top target 146, copy-credit
floor 22, FTS joint cap 775 and top search limit 2^21. The canonical selection
hint occupies an existing witness word; compact signature size stays 5310.
The arbitrary-hint verifier, canonical extraction condition and both producers
are connected through the merged proof interfaces. The certificate target is
raw bound 6934 plus witness charge 97, C = 7031, score 37334610. Validation
status is reported separately in the public submission note.
-/
