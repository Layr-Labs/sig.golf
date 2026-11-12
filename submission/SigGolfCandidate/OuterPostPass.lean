import SigGolfCandidate.OuterImageTransfers
import SigGolfCandidate.Merge071
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterPostPass
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand.PostPass
theorem code_DA : CodeAt OuterImages.expandImage (pcOf 50055) cDA := OuterImageTransfers.code (b:=50055) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PostPass.code_DA
theorem code_DB : CodeAt OuterImages.expandImage (pcOf 50070) cDB := OuterImageTransfers.code (b:=50070) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PostPass.code_DB
theorem code_J : CodeAt OuterImages.expandImage (pcOf 50077) cJ := OuterImageTransfers.code (b:=50077) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PostPass.code_J
theorem code_cpA : CodeAt OuterImages.expandImage (pcOf 49246) cCpA := OuterImageTransfers.code (b:=49246) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PostPass.code_cpA
theorem code_cpC : CodeAt OuterImages.expandImage (pcOf 49257) cCpC := OuterImageTransfers.code (b:=49257) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PostPass.code_cpC
theorem code_cpE : CodeAt OuterImages.expandImage (pcOf 49268) cCpE := OuterImageTransfers.code (b:=49268) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PostPass.code_cpE
theorem code_dg : CodeAt OuterImages.expandImage (pcOf 49279) cDg := OuterImageTransfers.code (b:=49279) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PostPass.code_dg
theorem code_dgb : CodeAt OuterImages.expandImage (pcOf 49282) dBody := OuterImageTransfers.code (b:=49282) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PostPass.code_dgb
theorem code_f1 : CodeAt OuterImages.expandImage (pcOf 49406) fBody := OuterImageTransfers.code (b:=49406) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PostPass.code_f1
theorem code_f2 : CodeAt OuterImages.expandImage (pcOf 49417) fBody := OuterImageTransfers.code (b:=49417) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PostPass.code_f2
theorem code_fA : CodeAt OuterImages.expandImage (pcOf 49252) fBody := OuterImageTransfers.code (b:=49252) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PostPass.code_fA
theorem code_fC : CodeAt OuterImages.expandImage (pcOf 49263) fBody := OuterImageTransfers.code (b:=49263) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PostPass.code_fC
theorem code_fE : CodeAt OuterImages.expandImage (pcOf 49274) fBody := OuterImageTransfers.code (b:=49274) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PostPass.code_fE
theorem code_fsv : CodeAt OuterImages.expandImage (pcOf 49428) fBody := OuterImageTransfers.code (b:=49428) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PostPass.code_fsv
theorem code_jA : CodeAt OuterImages.expandImage (pcOf 49444) cJA := OuterImageTransfers.code (b:=49444) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PostPass.code_jA
theorem code_jB : CodeAt OuterImages.expandImage (pcOf 49286) cJB := OuterImageTransfers.code (b:=49286) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PostPass.code_jB
theorem code_m4 : CodeAt OuterImages.expandImage (pcOf 49457) mBody := OuterImageTransfers.code (b:=49457) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PostPass.code_m4
theorem code_mB : CodeAt OuterImages.expandImage (pcOf 49241) mBody := OuterImageTransfers.code (b:=49241) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PostPass.code_mB
theorem code_mD : CodeAt OuterImages.expandImage (pcOf 49231) mBody := OuterImageTransfers.code (b:=49231) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PostPass.code_mD
theorem code_mFG : CodeAt OuterImages.expandImage (pcOf 49439) mBody := OuterImageTransfers.code (b:=49439) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PostPass.code_mFG
theorem code_mv4 : CodeAt OuterImages.expandImage (pcOf 49452) cMv4 := OuterImageTransfers.code (b:=49452) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PostPass.code_mv4
theorem code_mvB : CodeAt OuterImages.expandImage (pcOf 49236) cMvB := OuterImageTransfers.code (b:=49236) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PostPass.code_mvB
theorem code_mvD : CodeAt OuterImages.expandImage (pcOf 49226) cMvD := OuterImageTransfers.code (b:=49226) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PostPass.code_mvD
theorem code_mvFG : CodeAt OuterImages.expandImage (pcOf 49433) cMvFG := OuterImageTransfers.code (b:=49433) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PostPass.code_mvFG
theorem code_pro1 : CodeAt OuterImages.expandImage (pcOf 49400) cPro1 := OuterImageTransfers.code (b:=49400) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PostPass.code_pro1
theorem code_pro2 : CodeAt OuterImages.expandImage (pcOf 49411) cPro2 := OuterImageTransfers.code (b:=49411) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PostPass.code_pro2
theorem code_rowA (r : Nat) (hr : r<64) : CodeAt OuterImages.expandImage (pcOf (50078+32*r)) (rowCodeA.getD r []) := by
  have hb : ∀ i : Fin 64,OuterImageTransfers.Clean (50078+32*i.val) (rowCodeA.getD i.val []).length := by decide +kernel
  have h:=hb ⟨r,hr⟩
  dsimp only at h
  exact OuterImageTransfers.code (b:=50078+32*r) h (ClaudeWCT.W9.Machine.Expand.PostPass.code_rowA r hr)
theorem code_rowB (r : Nat) (hr : r<64) : CodeAt OuterImages.expandImage (pcOf (52126+32*r)) (rowCodeB.getD r []) := by
  have hb : ∀ i : Fin 64,OuterImageTransfers.Clean (52126+32*i.val) (rowCodeB.getD i.val []).length := by decide +kernel
  have h:=hb ⟨r,hr⟩
  dsimp only at h
  exact OuterImageTransfers.code (b:=52126+32*r) h (ClaudeWCT.W9.Machine.Expand.PostPass.code_rowB r hr)
theorem code_sv : CodeAt OuterImages.expandImage (pcOf 49422) cSv := OuterImageTransfers.code (b:=49422) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PostPass.code_sv
theorem code_vals : CodeAt OuterImages.expandImage (pcOf 49469) cVals := OuterImageTransfers.code (b:=49469) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PostPass.code_vals
theorem code_z : CodeAt OuterImages.expandImage (pcOf 49466) zBody := OuterImageTransfers.code (b:=49466) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PostPass.code_z
theorem code_zpro : CodeAt OuterImages.expandImage (pcOf 49462) cZPro := OuterImageTransfers.code (b:=49462) (by decide +kernel) ClaudeWCT.W9.Machine.Expand.PostPass.code_zpro
theorem pp_spec (s : MachineState) (hpc : s.pc = pcOf 49400) :
    ∃ t, Steps OuterImages.expandImage s 17535 ppCycles t ∧ t.pc = pcOf 54174 ∧
      RegsExcept s t [.x6, .x7, .x10, .x28, .x29, .x30] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        ppMem (leafOf (s.getMem (BitVec.ofNat 64 0x20160))) (fun B => s.getMem (BitVec.ofNat 64 B)) A := by
  -- save 1
  obtain ⟨t1, st1, pt1, a1, b1, c1, rt1, mt1⟩ := pro_spec run_pro1 code_pro1 (Or.inl rfl) s hpc
  obtain ⟨u1, su1, ru1, I1⟩ := f_loop (by decide) code_f1 t1 (fun B => s.getMem (BitVec.ofNat 64 B)) 11768 0x300000
    432 (by decide) pt1 a1 b1 c1 (fun A _ => by rw [mt1]) (by decide) (by decide) (by decide) (by decide) (by decide)
    432 le_rfl
  have pu1 : u1.pc = pcOf 49411 := by rw [I1.pc, if_neg (by decide)]
  -- save 2
  obtain ⟨t2, st2, pt2, a2, b2, c2, rt2, mt2⟩ := pro_spec run_pro2 code_pro2 (Or.inl rfl) u1 pu1
  obtain ⟨u2, su2, ru2, I2⟩ := f_loop (by decide) code_f2 t2 (PS1 (fun B => s.getMem (BitVec.ofNat 64 B))) 11000 0x301000 96
    (by decide) pt2 a2 b2 c2 (fun A hA => by rw [mt2, I1.mem A hA]) (by decide) (by decide) (by decide) (by decide)
    (by decide) 96 le_rfl
  have pu2 : u2.pc = pcOf 49422 := by rw [I2.pc, if_neg (by decide)]
  -- T1: save the lower leaf buffers
  obtain ⟨t3, st3, pt3, a3, b3, c3, rt3, mt3⟩ := pro_spec run_sv code_sv (Or.inl rfl) u2 pu2
  obtain ⟨u3, su3, ru3, I3⟩ := f_loop (by decide) code_fsv t3 (PS2 (fun B => s.getMem (BitVec.ofNat 64 B))) 23744 SCR 284
    (by decide) pt3 a3 b3 c3 (fun A hA => by rw [mt3, I2.mem A hA]) (by decide) (by decide) (by decide) (by decide)
    (by decide) 284 le_rfl
  have pu3 : u3.pc = pcOf 49433 := by rw [I3.pc, if_neg (by decide)]
  -- move region3|buf3
  obtain ⟨t4, st4, pt4, a4, b4, c4, rt4, mt4⟩ := pro_spec run_mvFG code_mvFG (Or.inr rfl) u3 pu3
  obtain ⟨u4, su4, ru4, I4⟩ := m_loop (by decide) code_mFG t4 (PS3 (fun B => s.getMem (BitVec.ofNat 64 B))) 23688 2256 20432 407
    (by decide) (by decide) pt4 a4 b4 c4 (fun A hA => by rw [mt4, I3.mem A hA]) (by decide) (by decide) (by decide)
    (by decide) (by decide) 407 le_rfl
  have pu4 : u4.pc = pcOf 49444 := by rw [I4.pc, if_neg (by decide)]
  obtain ⟨v4, sv4, pv4, rv4, mv4⟩ := jA_spec code_jA u4 pu4
  -- move region2
  obtain ⟨t5, st5, pt5, a5, b5, c5, rt5, mt5⟩ := pro_spec run_mvD code_mvD (Or.inr rfl) v4 pv4
  obtain ⟨u5, su5, ru5, I5⟩ := m_loop (by decide) code_mD t5 (PS4 (fun B => s.getMem (BitVec.ofNat 64 B))) 20432 1568 17864 321
    (by decide) (by decide) pt5 a5 b5 c5 (fun A hA => by rw [mt5, mv4, I4.mem A hA]) (by decide) (by decide)
    (by decide) (by decide) (by decide) 321 le_rfl
  have pu5 : u5.pc = pcOf 49236 := by rw [I5.pc, if_neg (by decide)]
  -- move region1
  obtain ⟨t6, st6, pt6, a6, b6, c6, rt6, mt6⟩ := pro_spec run_mvB code_mvB (Or.inr rfl) u5 pu5
  obtain ⟨u6, su6, ru6, I6⟩ := m_loop (by decide) code_mB t6 (PS5 (fun B => s.getMem (BitVec.ofNat 64 B))) 17864 880 15216 331
    (by decide) (by decide) pt6 a6 b6 c6 (fun A hA => by rw [mt6, I5.mem A hA]) (by decide) (by decide)
    (by decide) (by decide) (by decide) 331 le_rfl
  have pu6 : u6.pc = pcOf 49246 := by rw [I6.pc, if_neg (by decide)]
  -- copy buf0 / buf1 / buf2 back
  obtain ⟨t7, st7, pt7, a7, b7, c7, rt7, mt7⟩ := pro_spec run_cpA code_cpA (Or.inl rfl) u6 pu6
  obtain ⟨u7, su7, ru7, I7⟩ := f_loop (by decide) code_fA t7 (PS6 (fun B => s.getMem (BitVec.ofNat 64 B))) (SCR + 1456) 15288 102
    (by decide) pt7 a7 b7 c7 (fun A hA => by rw [mt7, I6.mem A hA]) (by decide) (by decide) (by decide) (by decide)
    (by decide) 102 le_rfl
  have pu7 : u7.pc = pcOf 49257 := by rw [I7.pc, if_neg (by decide)]
  obtain ⟨t8, st8, pt8, a8, b8, c8, rt8, mt8⟩ := pro_spec run_cpC code_cpC (Or.inl rfl) u7 pu7
  obtain ⟨u8, su8, ru8, I8⟩ := f_loop (by decide) code_fC t8 (PS7 (fun B => s.getMem (BitVec.ofNat 64 B))) (SCR + 736) 18752 86
    (by decide) pt8 a8 b8 c8 (fun A hA => by rw [mt8, I7.mem A hA]) (by decide) (by decide) (by decide) (by decide)
    (by decide) 86 le_rfl
  have pu8 : u8.pc = pcOf 49268 := by rw [I8.pc, if_neg (by decide)]
  obtain ⟨t9, st9, pt9, a9, b9, c9, rt9, mt9⟩ := pro_spec run_cpE code_cpE (Or.inl rfl) u8 pu8
  obtain ⟨u9, su9, ru9, I9⟩ := f_loop (by decide) code_fE t9 (PS8 (fun B => s.getMem (BitVec.ofNat 64 B))) SCR 22008 86
    (by decide) pt9 a9 b9 c9 (fun A hA => by rw [mt9, I8.mem A hA]) (by decide) (by decide) (by decide) (by decide)
    (by decide) 86 le_rfl
  have pu9 : u9.pc = pcOf 49279 := by rw [I9.pc, if_neg (by decide)]
  -- zero tail band
  obtain ⟨t10, st10, pt10, rt10, rr10, mt10⟩ := dpro_spec code_dg u9 pu9
  obtain ⟨u10, su10, ru10, I10⟩ := d_loop code_dgb t10 (PS9 (fun B => s.getMem (BitVec.ofNat 64 B))) 26136 26072 8
    (by decide) (by decide) pt10 rt10.1 rt10.2 (fun A hA => by rw [mt10, I9.mem A hA]) (by decide) (by decide)
    (by decide) (by decide) 8 le_rfl
  have pu10 : u10.pc = pcOf 49286 := by rw [I10.pc, if_neg (by decide)]
  obtain ⟨v10, sv10, pv10, rv10, mv10⟩ := jB_spec code_jB u10 pu10
  -- move 4 (FTS block)
  obtain ⟨t11, st11, pt11, a11, b11, c11, rt11, mt11⟩ := pro_spec run_mv4 code_mv4 (Or.inr rfl) v10 pv10
  obtain ⟨u11, su11, ru11, I11⟩ := m_loop (by decide) code_m4 t11 (PS10 (fun B => s.getMem (BitVec.ofNat 64 B))) 10560 1352 2896 958 (by decide)
    (by decide) pt11 a11 b11 c11 (fun A hA => by rw [mt11, mv10, I10.mem A hA]) (by decide) (by decide) (by decide)
    (by decide) (by decide) 958 le_rfl
  have pu11 : u11.pc = pcOf 49462 := by rw [I11.pc, if_neg (by decide)]
  -- zero
  obtain ⟨t12, st12, pt12, rt12, rr12, mt12⟩ := zpro_spec run_zpro code_zpro u11 pu11
  obtain ⟨u12, su12, ru12, pu12', _, mu12⟩ := z_loop rfl code_z t12 (PS11 (fun B => s.getMem (BitVec.ofNat 64 B))) 11920 421 (by decide) pt12 rt12.1
    rt12.2 (fun A hA => by rw [mt12, I11.mem A hA]) (by decide) (by decide) 421 le_rfl
  have pu12 : u12.pc = pcOf 49469 := by rw [pu12', if_neg (by decide)]
  -- values
  obtain ⟨u13, su13, pu13, ru13, _, mu13⟩ := vals_spec code_vals u12 pu12
  -- dispatch A
  obtain ⟨u14, su14, pu14, u14_10, u14_29, u14_30, ru14, mu14⟩ := dA_spec code_DA u13 pu13
  have hleaf : u13.getMem (BitVec.ofNat 64 0x20160) = s.getMem (BitVec.ofNat 64 0x20160) := by
    rw [mu13 _ (by decide), vFun_20160, mu12 _ (by decide)]
    exact stages_20160 _
  rw [hleaf] at pu14 u14_10
  have hlt := leafOf_lt (s.getMem (BitVec.ofNat 64 0x20160))
  -- row A
  obtain ⟨R, hRrun, hRok⟩ := rowA_ok (leafOf (s.getMem (BitVec.ofNat 64 0x20160)) % 64) (by omega)
  obtain ⟨u15, su15, pu15, ru15, mu15⟩ := row_spec hRrun (code_rowA _ (by omega)) hRok
    (rowsA_bounds _ (by omega)) u14 pu14 u14_29 u14_30
  -- dispatch B
  obtain ⟨u16, su16, pu16, ru16, mu16⟩ := dB_spec code_DB u15 pu15 _ hlt (by rw [ru15.get (by decide), u14_10])
  -- row B
  obtain ⟨R', hR'run, hR'ok⟩ := rowB_ok (leafOf (s.getMem (BitVec.ofNat 64 0x20160)) / 64 % 64) (by omega)
  obtain ⟨u17, su17, pu17, ru17, mu17⟩ := row_spec hR'run (code_rowB _ (by omega)) hR'ok
    (rowsB_bounds _ (by omega)) u16 pu16 (by rw [ru16.get (by decide), ru15.get (by decide), u14_29])
    (by rw [ru16.get (by decide), ru15.get (by decide), u14_30])
  -- jump to the pad writer hook
  obtain ⟨u18, su18, pu18, ru18, mu18⟩ := j_spec code_J u17 pu17
  refine ⟨u18, ?_, pu18, ?_, ?_⟩
  · have hS := ((((((((((((((((((((((((((((((st1.trans su1).trans st2).trans su2).trans st3).trans su3).trans st4).trans su4).trans sv4).trans st5).trans su5).trans st6).trans su6).trans st7).trans su7).trans st8).trans su8).trans st9).trans su9).trans st10).trans su10).trans sv10).trans st11).trans su11).trans st12).trans su12).trans su13).trans su14).trans su15).trans su16).trans su17).trans su18
    have hk : 6 + 5 * 432 + 6 + 5 * 96 + 6 + 5 * 284 + 6 + 5 * 407 + RJA.res.steps + 5 + 5 * 321 + 5 + 5 * 331 +
        6 + 5 * 102 + 6 + 5 * 86 + 6 + 5 * 86 + 3 + 4 * 8 + RJB.res.steps + 5 + 5 * 958 + 4 + 3 * 421 + 586 +
        RDA.res.steps + 25 + RDB.res.steps + 25 + RJ.res.steps = 17535 := by
      rw [show RDA.res.steps = 15 from rfl, show RDB.res.steps = 7 from rfl, show RJ.res.steps = 1 from rfl,
        show RJA.res.steps = 1 from rfl, show RJB.res.steps = 1 from rfl]
    have hc : 6 + 5 * 432 + 6 + 5 * 96 + 6 + 5 * 284 + 6 + 5 * 407 + RJA.res.cycles + 5 + 5 * 321 + 5 + 5 * 331 +
        6 + 5 * 102 + 6 + 5 * 86 + 6 + 5 * 86 + 3 + 4 * 8 + RJB.res.cycles + 5 + 5 * 958 + 4 + 3 * 421 + 586 +
        RDA.res.cycles + 25 + RDB.res.cycles + 25 + RJ.res.cycles = ppCycles := rfl
    exact Steps.of_eq hS hk hc
  · exact (((((((((((((((((((((((((((((((rt1.trans ru1).trans rt2).trans ru2).trans rt3).trans ru3).trans rt4).trans ru4).trans rv4).trans rt5).trans ru5).trans rt6).trans ru6).trans rt7).trans ru7).trans rt8).trans ru8).trans rt9).trans ru9).trans rr10).trans ru10).trans rv10).trans rt11).trans ru11).trans rr12).trans ru12).trans ru13).trans ru14).trans ru15).trans ru16).trans ru17).trans ru18).mono (by decide)
  · intro A hA
    rw [mu18, mu17 A hA]
    dsimp only [ppMem]
    apply rowFun_congr _ (rowsB_bounds _ (by omega)) _ _ _ A hA
    intro B hB
    rw [mu16, mu15 B hB]
    apply rowFun_congr _ (rowsA_bounds _ (by omega)) _ _ _ B hB
    intro C hC
    rw [mu14, mu13 C hC]
    apply vFun_congr _ _ _ C hC
    intro D hD
    rw [mu12 D hD, stage7]


#print axioms pp_spec
end OuterPostPass
