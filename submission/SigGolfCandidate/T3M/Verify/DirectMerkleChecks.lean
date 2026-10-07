import SigGolfCandidate.T3M.Verify.MerkleRuns

section
namespace SigGolfCandidate.T3M.BC
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
def mkShp (lay ci sh : Nat) : Nat :=
  T3M.mkShp lay ci sh
def mkEntSpec (lay ci sh : Nat) : Spec :=
  ⟨[], [], mkShp lay ci sh + 1, true, 1, [], none, 1⟩
def mkEntCheck (lay ci sh : Nat) : Bool :=
  mkSpecB [] [] baseK (mkEntK lay ci) [] (mkTabW lay ci sh) []
    (mkEntSpec lay ci sh) [] (mkEntPost lay ci sh) mkEntKeep
def mkLvlSpecN (lay ci sh kk : Nat) : Spec :=
  { T3M.mkLvlSpecN lay ci sh kk with
    pc := mkShp lay ci sh + mkOff lay ci (kk + 1) + mkMove lay (mkLo lay ci + kk) }
def mkLvlCheckN (lay ci sh kk : Nat) : Bool :=
  mkSpecB (mkLvlAllow lay sh (mkLo lay ci + kk)) [] baseK
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
