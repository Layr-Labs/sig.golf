import SigGolfCandidate.T3M_Verify_MerkleRuns

set_option Elab.async false

section
namespace SigGolfCandidate.T3M.BC
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
def mkShp (lay ci sh : Nat) : Nat :=
  T3M.mkShp lay ci sh
def mkEntSpec (lay ci sh : Nat) : Spec :=
  let st := if lay = 0 ∧ ci = 1 then 2 else 1
  ⟨[], [], mkShp lay ci sh + 1, true, st, [], none, st⟩
def mkEntCheck (lay ci sh : Nat) : Bool :=
  mkSpecB [] [] baseK (mkEntK lay ci) [] (mkTabW lay ci sh) []
    (mkEntSpec lay ci sh) [] (mkEntPost lay ci sh) mkEntKeep
def mkLvlSpecN (lay ci sh kk : Nat) : Spec :=
  { T3M.mkLvlSpecN lay ci sh kk with
    pc := mkShp lay ci sh + mkOff lay ci (kk + 1) + mkMove lay (mkLo lay ci + kk) }
def mkLvlCheckN (lay ci sh kk : Nat) : Bool :=
  mkSpecB (mkLvlAllow lay (mkLeafOf lay ci sh) (mkLo lay ci + kk)) [] baseK
    (mkLvlKN lay ci sh kk) [] (mkShp lay ci sh + mkOff lay ci kk + 2) []
    (mkLvlSpecN lay ci sh kk) [] (mkLvlPostN lay ci sh kk)
    (mkKeep ++ (.x14 :: mkLvlKeep lay (mkLo lay ci + kk)))
def mkLvlCheck (lay ci sh kk : Nat) : Bool :=
  if mkIsDisp lay ci kk then T3M.mkLvlCheckD lay ci sh kk
  else mkLvlCheckN lay ci sh kk
def childReturn (lay sh : Nat) : Nat :=
  mkShp lay 0 sh + mkOff lay 0 (hL lay - 1) + 2
def mkBlockCheck (lay ci sh : Nat) : Bool :=
  mkEntCheck lay ci sh &&
  (List.range (mkBits lay ci - if lay = 0 then 0 else 1)).all (mkLvlCheck lay ci sh) &&
  (lay == 0 || childReturn lay sh == trPc (lay - 1) sh)
def mkChunkCheck (lay ci lo n : Nat) : Bool :=
  (List.range' lo n).all (mkBlockCheck lay ci)
end SigGolfCandidate.T3M.BC
end
section
namespace SigGolfCandidate.T3M.BC
set_option maxRecDepth 100000
theorem mkChunkCheck_add {lay ci lo left right : Nat}
    (hleft : mkChunkCheck lay ci lo left = true)
    (hright : mkChunkCheck lay ci (lo + left) right = true) :
    mkChunkCheck lay ci lo (left + right) = true := by
  unfold mkChunkCheck at *
  rw [← List.range'_append_1, List.all_append, hleft, hright]
  rfl
private theorem mkCheck_part_3_0_0 : mkChunkCheck 3 0 0 4 = true := by decide +kernel
private theorem mkCheck_part_3_0_4 : mkChunkCheck 3 0 4 4 = true := by decide +kernel
private theorem mkCheck_part_3_0_8 : mkChunkCheck 3 0 8 4 = true := by decide +kernel
private theorem mkCheck_part_3_0_12 : mkChunkCheck 3 0 12 4 = true := by decide +kernel
private theorem mkCheck_part_3_0_16 : mkChunkCheck 3 0 16 4 = true := by decide +kernel
private theorem mkCheck_part_3_0_20 : mkChunkCheck 3 0 20 4 = true := by decide +kernel
private theorem mkCheck_part_3_0_24 : mkChunkCheck 3 0 24 4 = true := by decide +kernel
private theorem mkCheck_part_3_0_28 : mkChunkCheck 3 0 28 4 = true := by decide +kernel
private theorem mkCheck_part_3_0_32 : mkChunkCheck 3 0 32 4 = true := by decide +kernel
private theorem mkCheck_part_3_0_36 : mkChunkCheck 3 0 36 4 = true := by decide +kernel
private theorem mkCheck_part_3_0_40 : mkChunkCheck 3 0 40 4 = true := by decide +kernel
private theorem mkCheck_part_3_0_44 : mkChunkCheck 3 0 44 4 = true := by decide +kernel
private theorem mkCheck_part_3_0_48 : mkChunkCheck 3 0 48 4 = true := by decide +kernel
private theorem mkCheck_part_3_0_52 : mkChunkCheck 3 0 52 4 = true := by decide +kernel
private theorem mkCheck_part_3_0_56 : mkChunkCheck 3 0 56 4 = true := by decide +kernel
private theorem mkCheck_part_3_0_60 : mkChunkCheck 3 0 60 4 = true := by decide +kernel
theorem mkCheck_3 : mkChunkCheck 3 0 0 64 = true := by
  exact @mkChunkCheck_add 3 0 0 4 60 mkCheck_part_3_0_0 (@mkChunkCheck_add 3 0 4 4 56 mkCheck_part_3_0_4 (@mkChunkCheck_add 3 0 8 4 52 mkCheck_part_3_0_8 (@mkChunkCheck_add 3 0 12 4 48 mkCheck_part_3_0_12 (@mkChunkCheck_add 3 0 16 4 44 mkCheck_part_3_0_16 (@mkChunkCheck_add 3 0 20 4 40 mkCheck_part_3_0_20 (@mkChunkCheck_add 3 0 24 4 36 mkCheck_part_3_0_24 (@mkChunkCheck_add 3 0 28 4 32 mkCheck_part_3_0_28 (@mkChunkCheck_add 3 0 32 4 28 mkCheck_part_3_0_32 (@mkChunkCheck_add 3 0 36 4 24 mkCheck_part_3_0_36 (@mkChunkCheck_add 3 0 40 4 20 mkCheck_part_3_0_40 (@mkChunkCheck_add 3 0 44 4 16 mkCheck_part_3_0_44 (@mkChunkCheck_add 3 0 48 4 12 mkCheck_part_3_0_48 (@mkChunkCheck_add 3 0 52 4 8 mkCheck_part_3_0_52 (@mkChunkCheck_add 3 0 56 4 4 mkCheck_part_3_0_56 (mkCheck_part_3_0_60)))))))))))))))
private theorem mkCheck_part_2_0_0 : mkChunkCheck 2 0 0 4 = true := by decide +kernel
private theorem mkCheck_part_2_0_4 : mkChunkCheck 2 0 4 4 = true := by decide +kernel
private theorem mkCheck_part_2_0_8 : mkChunkCheck 2 0 8 4 = true := by decide +kernel
private theorem mkCheck_part_2_0_12 : mkChunkCheck 2 0 12 4 = true := by decide +kernel
private theorem mkCheck_part_2_0_16 : mkChunkCheck 2 0 16 4 = true := by decide +kernel
private theorem mkCheck_part_2_0_20 : mkChunkCheck 2 0 20 4 = true := by decide +kernel
private theorem mkCheck_part_2_0_24 : mkChunkCheck 2 0 24 4 = true := by decide +kernel
private theorem mkCheck_part_2_0_28 : mkChunkCheck 2 0 28 4 = true := by decide +kernel
private theorem mkCheck_part_2_0_32 : mkChunkCheck 2 0 32 4 = true := by decide +kernel
private theorem mkCheck_part_2_0_36 : mkChunkCheck 2 0 36 4 = true := by decide +kernel
private theorem mkCheck_part_2_0_40 : mkChunkCheck 2 0 40 4 = true := by decide +kernel
private theorem mkCheck_part_2_0_44 : mkChunkCheck 2 0 44 4 = true := by decide +kernel
private theorem mkCheck_part_2_0_48 : mkChunkCheck 2 0 48 4 = true := by decide +kernel
private theorem mkCheck_part_2_0_52 : mkChunkCheck 2 0 52 4 = true := by decide +kernel
private theorem mkCheck_part_2_0_56 : mkChunkCheck 2 0 56 4 = true := by decide +kernel
private theorem mkCheck_part_2_0_60 : mkChunkCheck 2 0 60 4 = true := by decide +kernel
theorem mkCheck_2 : mkChunkCheck 2 0 0 64 = true := by
  exact @mkChunkCheck_add 2 0 0 4 60 mkCheck_part_2_0_0 (@mkChunkCheck_add 2 0 4 4 56 mkCheck_part_2_0_4 (@mkChunkCheck_add 2 0 8 4 52 mkCheck_part_2_0_8 (@mkChunkCheck_add 2 0 12 4 48 mkCheck_part_2_0_12 (@mkChunkCheck_add 2 0 16 4 44 mkCheck_part_2_0_16 (@mkChunkCheck_add 2 0 20 4 40 mkCheck_part_2_0_20 (@mkChunkCheck_add 2 0 24 4 36 mkCheck_part_2_0_24 (@mkChunkCheck_add 2 0 28 4 32 mkCheck_part_2_0_28 (@mkChunkCheck_add 2 0 32 4 28 mkCheck_part_2_0_32 (@mkChunkCheck_add 2 0 36 4 24 mkCheck_part_2_0_36 (@mkChunkCheck_add 2 0 40 4 20 mkCheck_part_2_0_40 (@mkChunkCheck_add 2 0 44 4 16 mkCheck_part_2_0_44 (@mkChunkCheck_add 2 0 48 4 12 mkCheck_part_2_0_48 (@mkChunkCheck_add 2 0 52 4 8 mkCheck_part_2_0_52 (@mkChunkCheck_add 2 0 56 4 4 mkCheck_part_2_0_56 (mkCheck_part_2_0_60)))))))))))))))
private theorem mkCheck_part_1_0_0 : mkChunkCheck 1 0 0 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_4 : mkChunkCheck 1 0 4 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_8 : mkChunkCheck 1 0 8 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_12 : mkChunkCheck 1 0 12 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_16 : mkChunkCheck 1 0 16 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_20 : mkChunkCheck 1 0 20 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_24 : mkChunkCheck 1 0 24 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_28 : mkChunkCheck 1 0 28 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_32 : mkChunkCheck 1 0 32 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_36 : mkChunkCheck 1 0 36 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_40 : mkChunkCheck 1 0 40 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_44 : mkChunkCheck 1 0 44 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_48 : mkChunkCheck 1 0 48 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_52 : mkChunkCheck 1 0 52 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_56 : mkChunkCheck 1 0 56 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_60 : mkChunkCheck 1 0 60 4 = true := by decide +kernel
theorem mkCheck_1a : mkChunkCheck 1 0 0 64 = true := by
  exact @mkChunkCheck_add 1 0 0 4 60 mkCheck_part_1_0_0 (@mkChunkCheck_add 1 0 4 4 56 mkCheck_part_1_0_4 (@mkChunkCheck_add 1 0 8 4 52 mkCheck_part_1_0_8 (@mkChunkCheck_add 1 0 12 4 48 mkCheck_part_1_0_12 (@mkChunkCheck_add 1 0 16 4 44 mkCheck_part_1_0_16 (@mkChunkCheck_add 1 0 20 4 40 mkCheck_part_1_0_20 (@mkChunkCheck_add 1 0 24 4 36 mkCheck_part_1_0_24 (@mkChunkCheck_add 1 0 28 4 32 mkCheck_part_1_0_28 (@mkChunkCheck_add 1 0 32 4 28 mkCheck_part_1_0_32 (@mkChunkCheck_add 1 0 36 4 24 mkCheck_part_1_0_36 (@mkChunkCheck_add 1 0 40 4 20 mkCheck_part_1_0_40 (@mkChunkCheck_add 1 0 44 4 16 mkCheck_part_1_0_44 (@mkChunkCheck_add 1 0 48 4 12 mkCheck_part_1_0_48 (@mkChunkCheck_add 1 0 52 4 8 mkCheck_part_1_0_52 (@mkChunkCheck_add 1 0 56 4 4 mkCheck_part_1_0_56 (mkCheck_part_1_0_60)))))))))))))))
private theorem mkCheck_part_1_0_64 : mkChunkCheck 1 0 64 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_68 : mkChunkCheck 1 0 68 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_72 : mkChunkCheck 1 0 72 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_76 : mkChunkCheck 1 0 76 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_80 : mkChunkCheck 1 0 80 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_84 : mkChunkCheck 1 0 84 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_88 : mkChunkCheck 1 0 88 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_92 : mkChunkCheck 1 0 92 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_96 : mkChunkCheck 1 0 96 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_100 : mkChunkCheck 1 0 100 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_104 : mkChunkCheck 1 0 104 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_108 : mkChunkCheck 1 0 108 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_112 : mkChunkCheck 1 0 112 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_116 : mkChunkCheck 1 0 116 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_120 : mkChunkCheck 1 0 120 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_124 : mkChunkCheck 1 0 124 4 = true := by decide +kernel
theorem mkCheck_1b : mkChunkCheck 1 0 64 64 = true := by
  exact @mkChunkCheck_add 1 0 64 4 60 mkCheck_part_1_0_64 (@mkChunkCheck_add 1 0 68 4 56 mkCheck_part_1_0_68 (@mkChunkCheck_add 1 0 72 4 52 mkCheck_part_1_0_72 (@mkChunkCheck_add 1 0 76 4 48 mkCheck_part_1_0_76 (@mkChunkCheck_add 1 0 80 4 44 mkCheck_part_1_0_80 (@mkChunkCheck_add 1 0 84 4 40 mkCheck_part_1_0_84 (@mkChunkCheck_add 1 0 88 4 36 mkCheck_part_1_0_88 (@mkChunkCheck_add 1 0 92 4 32 mkCheck_part_1_0_92 (@mkChunkCheck_add 1 0 96 4 28 mkCheck_part_1_0_96 (@mkChunkCheck_add 1 0 100 4 24 mkCheck_part_1_0_100 (@mkChunkCheck_add 1 0 104 4 20 mkCheck_part_1_0_104 (@mkChunkCheck_add 1 0 108 4 16 mkCheck_part_1_0_108 (@mkChunkCheck_add 1 0 112 4 12 mkCheck_part_1_0_112 (@mkChunkCheck_add 1 0 116 4 8 mkCheck_part_1_0_116 (@mkChunkCheck_add 1 0 120 4 4 mkCheck_part_1_0_120 (mkCheck_part_1_0_124)))))))))))))))
private theorem mkCheck_part_0_0_0 : mkChunkCheck 0 0 0 4 = true := by decide +kernel
private theorem mkCheck_part_0_0_4 : mkChunkCheck 0 0 4 4 = true := by decide +kernel
private theorem mkCheck_part_0_0_8 : mkChunkCheck 0 0 8 4 = true := by decide +kernel
private theorem mkCheck_part_0_0_12 : mkChunkCheck 0 0 12 4 = true := by decide +kernel
private theorem mkCheck_part_0_0_16 : mkChunkCheck 0 0 16 4 = true := by decide +kernel
private theorem mkCheck_part_0_0_20 : mkChunkCheck 0 0 20 4 = true := by decide +kernel
private theorem mkCheck_part_0_0_24 : mkChunkCheck 0 0 24 4 = true := by decide +kernel
private theorem mkCheck_part_0_0_28 : mkChunkCheck 0 0 28 4 = true := by decide +kernel
private theorem mkCheck_part_0_0_32 : mkChunkCheck 0 0 32 4 = true := by decide +kernel
private theorem mkCheck_part_0_0_36 : mkChunkCheck 0 0 36 4 = true := by decide +kernel
private theorem mkCheck_part_0_0_40 : mkChunkCheck 0 0 40 4 = true := by decide +kernel
private theorem mkCheck_part_0_0_44 : mkChunkCheck 0 0 44 4 = true := by decide +kernel
private theorem mkCheck_part_0_0_48 : mkChunkCheck 0 0 48 4 = true := by decide +kernel
private theorem mkCheck_part_0_0_52 : mkChunkCheck 0 0 52 4 = true := by decide +kernel
private theorem mkCheck_part_0_0_56 : mkChunkCheck 0 0 56 4 = true := by decide +kernel
private theorem mkCheck_part_0_0_60 : mkChunkCheck 0 0 60 4 = true := by decide +kernel
theorem mkCheck_00 : mkChunkCheck 0 0 0 64 = true := by
  exact @mkChunkCheck_add 0 0 0 4 60 mkCheck_part_0_0_0 (@mkChunkCheck_add 0 0 4 4 56 mkCheck_part_0_0_4 (@mkChunkCheck_add 0 0 8 4 52 mkCheck_part_0_0_8 (@mkChunkCheck_add 0 0 12 4 48 mkCheck_part_0_0_12 (@mkChunkCheck_add 0 0 16 4 44 mkCheck_part_0_0_16 (@mkChunkCheck_add 0 0 20 4 40 mkCheck_part_0_0_20 (@mkChunkCheck_add 0 0 24 4 36 mkCheck_part_0_0_24 (@mkChunkCheck_add 0 0 28 4 32 mkCheck_part_0_0_28 (@mkChunkCheck_add 0 0 32 4 28 mkCheck_part_0_0_32 (@mkChunkCheck_add 0 0 36 4 24 mkCheck_part_0_0_36 (@mkChunkCheck_add 0 0 40 4 20 mkCheck_part_0_0_40 (@mkChunkCheck_add 0 0 44 4 16 mkCheck_part_0_0_44 (@mkChunkCheck_add 0 0 48 4 12 mkCheck_part_0_0_48 (@mkChunkCheck_add 0 0 52 4 8 mkCheck_part_0_0_52 (@mkChunkCheck_add 0 0 56 4 4 mkCheck_part_0_0_56 (mkCheck_part_0_0_60)))))))))))))))
private theorem mkCheck_part_0_1_0 : mkChunkCheck 0 1 0 4 = true := by decide +kernel
private theorem mkCheck_part_0_1_4 : mkChunkCheck 0 1 4 4 = true := by decide +kernel
private theorem mkCheck_part_0_1_8 : mkChunkCheck 0 1 8 4 = true := by decide +kernel
private theorem mkCheck_part_0_1_12 : mkChunkCheck 0 1 12 4 = true := by decide +kernel
private theorem mkCheck_part_0_1_16 : mkChunkCheck 0 1 16 4 = true := by decide +kernel
private theorem mkCheck_part_0_1_20 : mkChunkCheck 0 1 20 4 = true := by decide +kernel
private theorem mkCheck_part_0_1_24 : mkChunkCheck 0 1 24 4 = true := by decide +kernel
private theorem mkCheck_part_0_1_28 : mkChunkCheck 0 1 28 4 = true := by decide +kernel
private theorem mkCheck_part_0_1_32 : mkChunkCheck 0 1 32 4 = true := by decide +kernel
private theorem mkCheck_part_0_1_36 : mkChunkCheck 0 1 36 4 = true := by decide +kernel
private theorem mkCheck_part_0_1_40 : mkChunkCheck 0 1 40 4 = true := by decide +kernel
private theorem mkCheck_part_0_1_44 : mkChunkCheck 0 1 44 4 = true := by decide +kernel
private theorem mkCheck_part_0_1_48 : mkChunkCheck 0 1 48 4 = true := by decide +kernel
private theorem mkCheck_part_0_1_52 : mkChunkCheck 0 1 52 4 = true := by decide +kernel
private theorem mkCheck_part_0_1_56 : mkChunkCheck 0 1 56 4 = true := by decide +kernel
private theorem mkCheck_part_0_1_60 : mkChunkCheck 0 1 60 4 = true := by decide +kernel
theorem mkCheck_01 : mkChunkCheck 0 1 0 64 = true := by
  exact @mkChunkCheck_add 0 1 0 4 60 mkCheck_part_0_1_0 (@mkChunkCheck_add 0 1 4 4 56 mkCheck_part_0_1_4 (@mkChunkCheck_add 0 1 8 4 52 mkCheck_part_0_1_8 (@mkChunkCheck_add 0 1 12 4 48 mkCheck_part_0_1_12 (@mkChunkCheck_add 0 1 16 4 44 mkCheck_part_0_1_16 (@mkChunkCheck_add 0 1 20 4 40 mkCheck_part_0_1_20 (@mkChunkCheck_add 0 1 24 4 36 mkCheck_part_0_1_24 (@mkChunkCheck_add 0 1 28 4 32 mkCheck_part_0_1_28 (@mkChunkCheck_add 0 1 32 4 28 mkCheck_part_0_1_32 (@mkChunkCheck_add 0 1 36 4 24 mkCheck_part_0_1_36 (@mkChunkCheck_add 0 1 40 4 20 mkCheck_part_0_1_40 (@mkChunkCheck_add 0 1 44 4 16 mkCheck_part_0_1_44 (@mkChunkCheck_add 0 1 48 4 12 mkCheck_part_0_1_48 (@mkChunkCheck_add 0 1 52 4 8 mkCheck_part_0_1_52 (@mkChunkCheck_add 0 1 56 4 4 mkCheck_part_0_1_56 (mkCheck_part_0_1_60)))))))))))))))
end SigGolfCandidate.T3M.BC
end
section
namespace SigGolfCandidate.T3M.BC
theorem mkBlockCheck_at (lay ci sh : Nat) (hlay : lay < 4) (hci : ci < mkNch lay) (hsh : sh < 2 ^ mkBits lay ci) :
    mkBlockCheck lay ci sh = true := by
  have hall : ∀ lo n, mkChunkCheck lay ci lo n = true → lo ≤ sh → sh < lo + n → mkBlockCheck lay ci sh = true :=
    fun lo n h h1 h2 => List.all_eq_true.mp h sh (List.mem_range'_1.mpr ⟨h1, h2⟩)
  interval_cases lay
  · have hci' : ci < 2 := by simpa [mkNch] using hci
    interval_cases ci
    · exact hall 0 64 mkCheck_00 (by omega) (by simpa [mkBits] using hsh)
    · exact hall 0 64 mkCheck_01 (by omega) (by simpa [mkBits] using hsh)
  all_goals (have hci0 : ci = 0 := by simp [mkNch] at hci; omega); subst hci0
  · have : sh < 128 := by simpa [mkBits, hL] using hsh
    by_cases h64 : sh < 64
    · exact hall 0 64 mkCheck_1a (by omega) (by omega)
    · exact hall 64 64 mkCheck_1b (by omega) (by omega)
  · exact hall 0 64 mkCheck_2 (by omega) (by simpa [mkBits, hL] using hsh)
  · exact hall 0 64 mkCheck_3 (by omega) (by simpa [mkBits, hL] using hsh)
theorem mkEnt_of {lay ci sh : Nat} (h : mkBlockCheck lay ci sh = true) : mkEntCheck lay ci sh = true := by
  simp only [mkBlockCheck, Bool.and_eq_true] at h; exact h.1.1
theorem mkLvl_of {lay ci sh : Nat} (h : mkBlockCheck lay ci sh = true) (kk : Nat) (hkk : kk < mkBits lay ci - (if lay = 0 then 0 else 1)) :
    mkLvlCheck lay ci sh kk = true := by
  simp only [mkBlockCheck, Bool.and_eq_true] at h
  exact List.all_eq_true.mp h.1.2 kk (List.mem_range.mpr hkk)
end SigGolfCandidate.T3M.BC
end

section
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
/-! ### Merkle routes (window plans): what a fold still needs and what each write hits
C4: the top route is checked like the lower ones (its plan has two lines, so all 4096 leaves are checked); a top left
child at window slot 0 writes its junk low half at slot -1 (the end of the FTS area), so the `1 ≤ plan` fact is only
claimed for the lower layers, where slot -1 is the layer below. -/
def mkPS (lay : Nat) : Nat := [42,25,20,20].getD lay 0
def mkSib (lay leaf j : Nat) : Nat := plan lay leaf j + 3 * (1 - leaf / 2 ^ j % 2)
def mkCs (lay leaf j : Nat) : Nat := plan lay leaf j + 3 * (leaf / 2 ^ j % 2)
/-- Slots the fold window of level `j` still needs from the witness: the pad and the sibling. -/
def mkKS (lay leaf k : Nat) : List Nat :=
  ((List.range (hL lay)).filter (fun j => decide (k ≤ j))).flatMap (fun j => [plan lay leaf j + 2, mkSib lay leaf j])
/-- C2: slots whose HIGH word (the fold's witness high tweak word) a fold at level `≥ k` still needs. -/
def mkKH (lay leaf k : Nat) : List Nat :=
  ((List.range (hL lay)).filter (fun j => decide (k ≤ j))).map (fun j => plan lay leaf j + 1)
/-- C2: slots written by the hash that produces the level-`j` input (a left node 16 bytes low). -/
def mkWs (lay leaf j : Nat) : List Nat :=
  if leaf / 2 ^ j % 2 = 0 then [plan lay leaf j - 1, plan lay leaf j] else [plan lay leaf j + 3, plan lay leaf j + 4]
def mkRouteOk (lay leaf : Nat) : Bool :=
  (List.range (hL lay)).all (fun k => decide (plan lay leaf k + 4 ≤ mkPS lay ∧
    (lay ≠ 0 → leaf / 2 ^ k % 2 = 0 → 1 ≤ plan lay leaf k))) &&
  (mkKS lay leaf 0 ++ mkKH lay leaf 0).all (fun s => decide (s + 1 ≤ mkPS lay ∧ s ∉ mkWs lay leaf 0)) &&
  (List.range (hL lay - 1)).all (fun k => (mkKS lay leaf (k + 1) ++ mkKH lay leaf (k + 1)).all (fun s =>
    decide (s ≠ plan lay leaf k + 1 ∧ s ∉ mkWs lay leaf (k + 1))))
def mkLowOk : Bool :=
  (List.range 128).all (mkRouteOk 1) && (List.range 64).all (mkRouteOk 2) && (List.range 64).all (mkRouteOk 3)
set_option maxRecDepth 100000 in
theorem mkLowOk_true : mkLowOk = true := by decide +kernel
def mkTopOk (lo n : Nat) : Bool := (List.range' lo n).all (mkRouteOk 0)
theorem mkTopOk_add {lo left right : Nat} (hleft : mkTopOk lo left = true)
    (hright : mkTopOk (lo + left) right = true) : mkTopOk lo (left + right) = true := by
  unfold mkTopOk at *
  rw [← List.range'_append_1, List.all_append, hleft, hright]
  rfl
set_option maxRecDepth 100000
private theorem mkTop_part_0 : mkTopOk 0 64 = true := by decide +kernel
private theorem mkTop_part_64 : mkTopOk 64 64 = true := by decide +kernel
private theorem mkTop_part_128 : mkTopOk 128 64 = true := by decide +kernel
private theorem mkTop_part_192 : mkTopOk 192 64 = true := by decide +kernel
private theorem mkTop_part_256 : mkTopOk 256 64 = true := by decide +kernel
private theorem mkTop_part_320 : mkTopOk 320 64 = true := by decide +kernel
private theorem mkTop_part_384 : mkTopOk 384 64 = true := by decide +kernel
private theorem mkTop_part_448 : mkTopOk 448 64 = true := by decide +kernel
private theorem mkTop_part_512 : mkTopOk 512 64 = true := by decide +kernel
private theorem mkTop_part_576 : mkTopOk 576 64 = true := by decide +kernel
private theorem mkTop_part_640 : mkTopOk 640 64 = true := by decide +kernel
private theorem mkTop_part_704 : mkTopOk 704 64 = true := by decide +kernel
private theorem mkTop_part_768 : mkTopOk 768 64 = true := by decide +kernel
private theorem mkTop_part_832 : mkTopOk 832 64 = true := by decide +kernel
private theorem mkTop_part_896 : mkTopOk 896 64 = true := by decide +kernel
private theorem mkTop_part_960 : mkTopOk 960 64 = true := by decide +kernel
private theorem mkTop_part_1024 : mkTopOk 1024 64 = true := by decide +kernel
private theorem mkTop_part_1088 : mkTopOk 1088 64 = true := by decide +kernel
private theorem mkTop_part_1152 : mkTopOk 1152 64 = true := by decide +kernel
private theorem mkTop_part_1216 : mkTopOk 1216 64 = true := by decide +kernel
private theorem mkTop_part_1280 : mkTopOk 1280 64 = true := by decide +kernel
private theorem mkTop_part_1344 : mkTopOk 1344 64 = true := by decide +kernel
private theorem mkTop_part_1408 : mkTopOk 1408 64 = true := by decide +kernel
private theorem mkTop_part_1472 : mkTopOk 1472 64 = true := by decide +kernel
private theorem mkTop_part_1536 : mkTopOk 1536 64 = true := by decide +kernel
private theorem mkTop_part_1600 : mkTopOk 1600 64 = true := by decide +kernel
private theorem mkTop_part_1664 : mkTopOk 1664 64 = true := by decide +kernel
private theorem mkTop_part_1728 : mkTopOk 1728 64 = true := by decide +kernel
private theorem mkTop_part_1792 : mkTopOk 1792 64 = true := by decide +kernel
private theorem mkTop_part_1856 : mkTopOk 1856 64 = true := by decide +kernel
private theorem mkTop_part_1920 : mkTopOk 1920 64 = true := by decide +kernel
private theorem mkTop_part_1984 : mkTopOk 1984 64 = true := by decide +kernel
private theorem mkTop_part_2048 : mkTopOk 2048 64 = true := by decide +kernel
private theorem mkTop_part_2112 : mkTopOk 2112 64 = true := by decide +kernel
private theorem mkTop_part_2176 : mkTopOk 2176 64 = true := by decide +kernel
private theorem mkTop_part_2240 : mkTopOk 2240 64 = true := by decide +kernel
private theorem mkTop_part_2304 : mkTopOk 2304 64 = true := by decide +kernel
private theorem mkTop_part_2368 : mkTopOk 2368 64 = true := by decide +kernel
private theorem mkTop_part_2432 : mkTopOk 2432 64 = true := by decide +kernel
private theorem mkTop_part_2496 : mkTopOk 2496 64 = true := by decide +kernel
private theorem mkTop_part_2560 : mkTopOk 2560 64 = true := by decide +kernel
private theorem mkTop_part_2624 : mkTopOk 2624 64 = true := by decide +kernel
private theorem mkTop_part_2688 : mkTopOk 2688 64 = true := by decide +kernel
private theorem mkTop_part_2752 : mkTopOk 2752 64 = true := by decide +kernel
private theorem mkTop_part_2816 : mkTopOk 2816 64 = true := by decide +kernel
private theorem mkTop_part_2880 : mkTopOk 2880 64 = true := by decide +kernel
private theorem mkTop_part_2944 : mkTopOk 2944 64 = true := by decide +kernel
private theorem mkTop_part_3008 : mkTopOk 3008 64 = true := by decide +kernel
private theorem mkTop_part_3072 : mkTopOk 3072 64 = true := by decide +kernel
private theorem mkTop_part_3136 : mkTopOk 3136 64 = true := by decide +kernel
private theorem mkTop_part_3200 : mkTopOk 3200 64 = true := by decide +kernel
private theorem mkTop_part_3264 : mkTopOk 3264 64 = true := by decide +kernel
private theorem mkTop_part_3328 : mkTopOk 3328 64 = true := by decide +kernel
private theorem mkTop_part_3392 : mkTopOk 3392 64 = true := by decide +kernel
private theorem mkTop_part_3456 : mkTopOk 3456 64 = true := by decide +kernel
private theorem mkTop_part_3520 : mkTopOk 3520 64 = true := by decide +kernel
private theorem mkTop_part_3584 : mkTopOk 3584 64 = true := by decide +kernel
private theorem mkTop_part_3648 : mkTopOk 3648 64 = true := by decide +kernel
private theorem mkTop_part_3712 : mkTopOk 3712 64 = true := by decide +kernel
private theorem mkTop_part_3776 : mkTopOk 3776 64 = true := by decide +kernel
private theorem mkTop_part_3840 : mkTopOk 3840 64 = true := by decide +kernel
private theorem mkTop_part_3904 : mkTopOk 3904 64 = true := by decide +kernel
private theorem mkTop_part_3968 : mkTopOk 3968 64 = true := by decide +kernel
private theorem mkTop_part_4032 : mkTopOk 4032 64 = true := by decide +kernel
theorem mkTopOk_all : mkTopOk 0 4096 = true := (@mkTopOk_add 0 64 4032 mkTop_part_0 (@mkTopOk_add 64 64 3968 mkTop_part_64 (@mkTopOk_add 128 64 3904 mkTop_part_128 (@mkTopOk_add 192 64 3840 mkTop_part_192 (@mkTopOk_add 256 64 3776 mkTop_part_256 (@mkTopOk_add 320 64 3712 mkTop_part_320 (@mkTopOk_add 384 64 3648 mkTop_part_384 (@mkTopOk_add 448 64 3584 mkTop_part_448 (@mkTopOk_add 512 64 3520 mkTop_part_512 (@mkTopOk_add 576 64 3456 mkTop_part_576 (@mkTopOk_add 640 64 3392 mkTop_part_640 (@mkTopOk_add 704 64 3328 mkTop_part_704 (@mkTopOk_add 768 64 3264 mkTop_part_768 (@mkTopOk_add 832 64 3200 mkTop_part_832 (@mkTopOk_add 896 64 3136 mkTop_part_896 (@mkTopOk_add 960 64 3072 mkTop_part_960 (@mkTopOk_add 1024 64 3008 mkTop_part_1024 (@mkTopOk_add 1088 64 2944 mkTop_part_1088 (@mkTopOk_add 1152 64 2880 mkTop_part_1152 (@mkTopOk_add 1216 64 2816 mkTop_part_1216 (@mkTopOk_add 1280 64 2752 mkTop_part_1280 (@mkTopOk_add 1344 64 2688 mkTop_part_1344 (@mkTopOk_add 1408 64 2624 mkTop_part_1408 (@mkTopOk_add 1472 64 2560 mkTop_part_1472 (@mkTopOk_add 1536 64 2496 mkTop_part_1536 (@mkTopOk_add 1600 64 2432 mkTop_part_1600 (@mkTopOk_add 1664 64 2368 mkTop_part_1664 (@mkTopOk_add 1728 64 2304 mkTop_part_1728 (@mkTopOk_add 1792 64 2240 mkTop_part_1792 (@mkTopOk_add 1856 64 2176 mkTop_part_1856 (@mkTopOk_add 1920 64 2112 mkTop_part_1920 (@mkTopOk_add 1984 64 2048 mkTop_part_1984 (@mkTopOk_add 2048 64 1984 mkTop_part_2048 (@mkTopOk_add 2112 64 1920 mkTop_part_2112 (@mkTopOk_add 2176 64 1856 mkTop_part_2176 (@mkTopOk_add 2240 64 1792 mkTop_part_2240 (@mkTopOk_add 2304 64 1728 mkTop_part_2304 (@mkTopOk_add 2368 64 1664 mkTop_part_2368 (@mkTopOk_add 2432 64 1600 mkTop_part_2432 (@mkTopOk_add 2496 64 1536 mkTop_part_2496 (@mkTopOk_add 2560 64 1472 mkTop_part_2560 (@mkTopOk_add 2624 64 1408 mkTop_part_2624 (@mkTopOk_add 2688 64 1344 mkTop_part_2688 (@mkTopOk_add 2752 64 1280 mkTop_part_2752 (@mkTopOk_add 2816 64 1216 mkTop_part_2816 (@mkTopOk_add 2880 64 1152 mkTop_part_2880 (@mkTopOk_add 2944 64 1088 mkTop_part_2944 (@mkTopOk_add 3008 64 1024 mkTop_part_3008 (@mkTopOk_add 3072 64 960 mkTop_part_3072 (@mkTopOk_add 3136 64 896 mkTop_part_3136 (@mkTopOk_add 3200 64 832 mkTop_part_3200 (@mkTopOk_add 3264 64 768 mkTop_part_3264 (@mkTopOk_add 3328 64 704 mkTop_part_3328 (@mkTopOk_add 3392 64 640 mkTop_part_3392 (@mkTopOk_add 3456 64 576 mkTop_part_3456 (@mkTopOk_add 3520 64 512 mkTop_part_3520 (@mkTopOk_add 3584 64 448 mkTop_part_3584 (@mkTopOk_add 3648 64 384 mkTop_part_3648 (@mkTopOk_add 3712 64 320 mkTop_part_3712 (@mkTopOk_add 3776 64 256 mkTop_part_3776 (@mkTopOk_add 3840 64 192 mkTop_part_3840 (@mkTopOk_add 3904 64 128 mkTop_part_3904 (@mkTopOk_add 3968 64 64 mkTop_part_3968 mkTop_part_4032)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem mkTop_route (leaf : Nat) (hleaf : leaf < 4096) : mkRouteOk 0 leaf = true :=
  List.all_eq_true.mp mkTopOk_all leaf (List.mem_range'_1.mpr ⟨Nat.zero_le _, by omega⟩)
end SigGolfCandidate.T3M
end
