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
  mkSpecB [] [] (gkL lay) (mkEntK lay ci) [] (mkTabW lay ci sh) []
    (mkEntSpec lay ci sh) [] (mkEntPost lay ci sh) mkEntKeep
def mkLvlSpecN (lay ci sh kk : Nat) : Spec :=
  { T3M.mkLvlSpecN lay ci sh kk with
    pc := mkShp lay ci sh + mkOff lay ci (kk + 1) + mkMove lay (mkLo lay ci + kk) }
def mkLvlCheckN (lay ci sh kk : Nat) : Bool :=
  mkSpecB (mkLvlAllow lay (mkLeafOf lay ci sh) (mkLo lay ci + kk)) [] (gkL lay)
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
private def need (p d : Nat) : List Nat := [p + 2, p + 3 * (1-d), p+1]
private def writes (p d : Nat) : List Nat := if d=0 then [p-1,p] else [p+3,p+4]
private def pA (r j : Nat) := (topPlanA.getD r []).getD j 0
private def pB (r j : Nat) := (topPlanB.getD r []).getD j 0
private def bit (r j : Nat) := r / 2^j % 2
private theorem checkA : ∀ r < 64,
    (∀ j < 6, 21 ≤ pA r j ∧ pA r j ≤ 38) ∧
    (∀ i < 6, ∀ j < 6, i ≤ j → ∀ s ∈ need (pA r j) (bit r j), s ∉ writes (pA r i) (bit r i)) ∧
    (∀ i < 6, ∀ j < 6, i < j → ∀ s ∈ need (pA r j) (bit r j), s ≠ pA r i + 1) := by
  have h : ∀ r : Fin 64,
    (∀ j : Fin 6, 21 ≤ pA r j ∧ pA r j ≤ 38) ∧
    (∀ i : Fin 6, ∀ j : Fin 6, i ≤ j → ∀ s ∈ need (pA r j) (bit r j), s ∉ writes (pA r i) (bit r i)) ∧
    (∀ i : Fin 6, ∀ j : Fin 6, i < j → ∀ s ∈ need (pA r j) (bit r j), s ≠ pA r i + 1) := by
    simp only [need, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    decide +kernel
  simpa only [Fin.forall_iff, Fin.mk_le_mk, Fin.mk_lt_mk] using h
private theorem checkB : ∀ r < 64,
    (∀ j < 6, pB r j ≤ 16) ∧
    (∀ i < 6, ∀ j < 6, i ≤ j → ∀ s ∈ need (pB r j) (bit r j), s ∉ writes (pB r i) (bit r i)) ∧
    (∀ i < 6, ∀ j < 6, i < j → ∀ s ∈ need (pB r j) (bit r j), s ≠ pB r i + 1) := by
  have h : ∀ r : Fin 64,
    (∀ j : Fin 6, pB r j ≤ 16) ∧
    (∀ i : Fin 6, ∀ j : Fin 6, i ≤ j → ∀ s ∈ need (pB r j) (bit r j), s ∉ writes (pB r i) (bit r i)) ∧
    (∀ i : Fin 6, ∀ j : Fin 6, i < j → ∀ s ∈ need (pB r j) (bit r j), s ≠ pB r i + 1) := by
    simp only [need, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    decide +kernel
  simpa only [Fin.forall_iff, Fin.mk_le_mk, Fin.mk_lt_mk] using h
private theorem bit_low (r j : Nat) (hj : j < 6) : bit r j = bit (r % 64) j := by
  unfold bit
  interval_cases j <;> norm_num <;> omega
private theorem bit_high (r j : Nat) (hj : j < 6) : bit r (6+j) = bit (r / 64 % 64) j := by
  unfold bit
  interval_cases j <;> norm_num <;> omega
private theorem need_bounds (p d s : Nat) (h : s ∈ need p d) : p ≤ s ∧ s ≤ p+3 := by
  simp only [need, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> omega
private theorem plan_low (r j : Nat) (hj : j<6) : plan 0 r j = pA (r%64) j := by
  simp [plan, topPlan, pA, hj]
private theorem plan_high (r j : Nat) (hj : 6≤j) : plan 0 r j = pB (r/64%64) (j-6) := by
  simp [plan, topPlan, pB, show ¬j<6 by omega]
private theorem bit_high' (r j : Nat) (hj : 6≤j) (hj' : j<12) : bit r j = bit (r/64%64) (j-6) := by
  have h := bit_high r (j-6) (by omega)
  simpa only [show 6+(j-6)=j by omega] using h
private theorem plan_bounds (r j : Nat) (hj : j<12) : plan 0 r j ≤ 38 := by
  by_cases h : j<6
  · rw [plan_low r j h]
    exact ((checkA _ (Nat.mod_lt _ (by decide))).1 j h).2
  · rw [plan_high r j (by omega)]
    have := (checkB (r/64%64) (Nat.mod_lt _ (by decide))).1 (j-6) (by omega)
    omega
private theorem separation (r i j s : Nat) (hi : i<12) (hj : j<12) (hij : i≤j)
    (hs : s∈need (plan 0 r j) (bit r j)) :
    s∉writes (plan 0 r i) (bit r i) ∧ (i<j → s≠plan 0 r i + 1) := by
  by_cases ha : i<6
  · by_cases hb : j<6
    · rw [plan_low r j hb, bit_low r j hb] at hs
      rw [plan_low r i ha, bit_low r i ha]
      exact ⟨(checkA _ (Nat.mod_lt _ (by decide))).2.1 i ha j hb hij s hs,
        fun h => (checkA _ (Nat.mod_lt _ (by decide))).2.2 i ha j hb h s hs⟩
    · have hsmall : s≤19 := by
        have hbnd := (need_bounds _ _ _ hs).2
        rw [plan_high r j (by omega)] at hbnd
        have := (checkB (r/64%64) (Nat.mod_lt _ (by decide))).1 (j-6) (by omega)
        omega
      have hlarge : 21≤plan 0 r i := by
        rw [plan_low r i ha]
        exact ((checkA _ (Nat.mod_lt _ (by decide))).1 i ha).1
      constructor
      · intro hw
        simp only [writes] at hw
        split at hw <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hw <;> omega
      · omega
  · have hb : 6≤j := by omega
    rw [plan_high r j hb, bit_high' r j hb hj] at hs
    rw [plan_high r i (by omega), bit_high' r i (by omega) hi]
    exact ⟨(checkB _ (Nat.mod_lt _ (by decide))).2.1 (i-6) (by omega) (j-6) (by omega) (by omega) s hs,
      fun h => (checkB _ (Nat.mod_lt _ (by decide))).2.2 (i-6) (by omega) (j-6) (by omega) (by omega) s hs⟩
private theorem need_mem (r k s : Nat) (hs : s∈mkKS 0 r k ++ mkKH 0 r k) :
    ∃ j, j<12 ∧ k≤j ∧ s∈need (plan 0 r j) (bit r j) := by
  simp only [List.mem_append, mkKS, mkKH, List.mem_flatMap, List.mem_map,
    List.mem_filter, List.mem_range, decide_eq_true_eq] at hs
  rcases hs with ⟨j, ⟨hj, hk⟩, hs⟩ | ⟨j, ⟨hj,hk⟩, hs⟩
  · refine ⟨j, hj, hk, ?_⟩
    simpa only [need, mkSib, bit, List.mem_cons, List.not_mem_nil, or_false] using
      (show s=plan 0 r j+2 ∨ s=mkSib 0 r j ∨ s=plan 0 r j+1 from by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with h|h
        · exact Or.inl h
        · exact Or.inr (Or.inl h))
  · refine ⟨j,hj,hk,?_⟩
    simp only [need, List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inr (Or.inr hs.symm)
private theorem route_fast (r : Nat) : mkRouteOk 0 r = true := by
  simp only [mkRouteOk, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq]
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro k hk
    refine ⟨?_, by simp⟩
    have h := plan_bounds r k hk
    change plan 0 r k+4 ≤42
    omega
  · intro s hs
    obtain ⟨j,hj,_,hsj⟩ := need_mem r 0 s hs
    constructor
    · have h := (need_bounds _ _ _ hsj).2
      have hp := plan_bounds r j hj
      change s+1≤42
      omega
    · exact (separation r 0 j s (by decide) hj (Nat.zero_le _) hsj).1
  · intro k hk s hs
    obtain ⟨j,hj,hkj,hsj⟩ := need_mem r (k+1) s hs
    exact ⟨(separation r k j s (by change k<12; change k<12-1 at hk; omega)
      hj (by omega) hsj).2 (by omega),
      (separation r (k+1) j s (by omega) hj hkj hsj).1⟩

theorem mkTopOk_all : mkTopOk 0 4096 = true := by
  exact List.all_eq_true.mpr (fun leaf _ => route_fast leaf)
theorem mkTop_route (leaf : Nat) (hleaf : leaf < 4096) : mkRouteOk 0 leaf = true :=
  List.all_eq_true.mp mkTopOk_all leaf (List.mem_range'_1.mpr ⟨Nat.zero_le _, by omega⟩)
end SigGolfCandidate.T3M
end
