import SigGolfCandidate.T3M.Mem

set_option autoImplicit false
namespace SigGolfCandidate.T3M
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
theorem codeAt_slice {image : Image} {b : Nat} {code : List (BitVec 32)}
    (hb : 0x1000 + 4 * b + 4 * code.length < 2 ^ 64)
    (h : (image.code.drop b).take code.length = code) :
    CodeAt image (pcOf b) code := by
  simp only [CodeAt, pcOf, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 4096 + 4 * b < 2 ^ 64 by omega)]
  refine ⟨by omega, by omega, hb, ?_⟩
  rw [show (4096 + 4 * b - 4096) / 4 = b by omega, ← h]; exact List.take_prefix _ _
end SigGolfCandidate.T3M

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv

/-- Equal bounded instruction windows give equal interior slices. -/
theorem image_slice_of_window {source target : Image} {start count base len : Nat}
    (hlo : start ≤ base) (hhi : base + len ≤ start + count)
    (hw : (source.code.drop start).take count = (target.code.drop start).take count) :
    (source.code.drop base).take len = (target.code.drop base).take len := by
  have h := congrArg (fun xs : List (BitVec 32) => (xs.drop (base - start)).take len) hw
  simp only [List.drop_take, List.take_take, List.drop_drop] at h
  have hm : min len (count - (base - start)) = len := Nat.min_eq_left (by omega)
  simpa only [hm, Nat.add_sub_of_le hlo] using h

/-- Transport a symbolic block to another image with the same instruction window. -/
theorem codeAt_of_window_eq {source target : Image} {start count base : Nat}
    {code : List (BitVec 32)} (hlo : start ≤ base)
    (hhi : base + code.length ≤ start + count)
    (haddr : 4096 + 4 * (start + count) < 2 ^ 64)
    (hw : (source.code.drop start).take count = (target.code.drop start).take count)
    (hc : CodeAt source (pcOf base) code) : CodeAt target (pcOf base) code := by
  have hn : 4096 + 4 * base < 2 ^ 64 := by omega
  have hp : (pcOf base).toNat = 4096 + 4 * base := by
    simp only [pcOf, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  have hb : 4096 + 4 * base + 4 * code.length < 2 ^ 64 := by
    simpa only [hp] using hc.2.2.1
  have hs : (source.code.drop base).take code.length = code := by
    have hs := hc.2.2.2
    rw [hp, show (4096 + 4 * base - 4096) / 4 = base by omega] at hs
    exact (List.prefix_iff_eq_take.mp hs).symm
  apply codeAt_slice hb
  rw [← image_slice_of_window hlo hhi hw]
  exact hs

end SigGolfCandidate.T3M
