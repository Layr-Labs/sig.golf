import SigGolf
import SigGolfCandidate.Packaging.Ready

namespace SigGolf.Challenge

def submission : SigGolf.Submission := SigGolfCandidate.Transfer.currentOf SigGolfCandidate.T3M.submission

theorem signature_bytes : submission.sizes.signature = 5310 := rfl

theorem witness_bytes : submission.sizes.witness = 24028 := rfl

theorem cache_bytes : submission.sizes.cache = 131072 := rfl

theorem layout_offsets : submission.layout =
  { message := 26080, secretKey := 128, publicKey := 160,
    cache := 524288, signature := 28672, witness := 2048 } := rfl

theorem certificate : SigGolf.Certificate submission 7175 := by
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

Current change builds on accepted PR #848 (C 7182). Top-layer encoding selects the low
hash half when bit 127 is set and the high half otherwise. Its exact selected-half
counts support target 145 instead of 144 with the same copy-credit floor 21 and FTS
joint cap 785. One fewer chain hash saves 9 cycles; the selector costs at most 3.
Legacy jumps into moved prefix instructions retain their previous state behavior.
S = 5310, W = 24028, K = 131072, C = 7175; score 38099250.
-/
