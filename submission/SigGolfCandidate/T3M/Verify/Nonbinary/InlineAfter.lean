import SigGolfCandidate.T3M.Verify.Nonbinary.InlineLowerBridge
import SigGolfCandidate.W9Drv.Fts
import SigGolfCandidate.T3M.Verify.Nonbinary.InlineTopFinal
import SigGolfCandidate.T3M.Verify.Nonbinary.InlineTopCost

/- Source and budget boundary for the new image's post-FTS continuation.
   No old fixed-image GoodQ is aliased. The physical lower3 induction and
   top decoder/setup attachment must supply this exact image-parametric
   conclusion before the final certificate may select it. -/
namespace SigGolfCandidate.T3M.Nonbinary.InlineTail.After
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv OracleComp SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route counterLimit encodingInput pad64
  decode shortHash leafHash target height chainCount dataDigits width maxDigit)
open ClaudeWCT.WCT9 (LayerMsg)
open SigGolfCandidate.T3M.Verify.Nonbinary
open SigGolfCandidate.T3M.Nonbinary (NCtx)
set_option autoImplicit false

-- Concrete five-instruction post-forest caller. Its symbolic run is
-- evaluated on the safe lookup; the old check is used only to identify the
-- identical pure postconditions, never to infer new-image execution.
def ld3Check : Bool := specB [] [] baseK (Lower.runAt ld3In [210] 205 []) ld3Spec [] ld3In
  [.x22, .x12, .x26, .x7, .x13, .x30, .x19, .x20, .x21, .x6]
set_option maxRecDepth 100000 in
theorem ld3_check : ld3Check = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem ld3_run_equal : Verify.runAt ld3In [210] 205 [] = Lower.runAt ld3In [210] 205 [] := by
  rfl

theorem layerIn_of_fts (w : WBytes) (pk : Digest) (idx : Nat) (root : Digest) (u : MachineState)
    (hidx : idx < 2 ^ 31) (hglob : Glob baseK w pk u) (hreg : u.getReg .x22 = BitVec.ofNat 64 idx)
    (hpc : u.pc = pcOf 205) (hroot : DigAt u 0x100 root)
    (hwit : Verify.Orig w (fun o => o < 64 ∨ 9288 ≤ o) u) (ha2 : u.getReg .x12 = BitVec.ofNat 64 0x100)
    (hs10 : u.getReg .x26 = 6) (hOne : u.getReg .x7 = 1) (hTwo : u.getReg .x13 = 2) (hSeven : u.getReg .x30 = 7)
    (hThree : u.getReg .x19 = 3) (hFour : u.getReg .x20 = 4) (hFive : u.getReg .x21 = 5)
    (hCoord : u.getReg .x6 = 0x10000)
    (hbase : u.getReg .x28 = BitVec.ofNat 64 TOPBASE)
    (htop : ∀ k, k < 5 → u.getMem (BitVec.ofNat 64 (TOPLOAD + 8 * k)) =
      BitVec.ofNat 64 (topWords.getD k 0))
    (htop8 : u.getMem (BitVec.ofNat 64 (TOPLOAD - 8)) = BitVec.ofNat 64 23304) :
    ∃ t, Steps InlineTail.image u 5 5 t ∧ LayerIn w pk idx 3 (.forest root) t := by
  have hk0 : KnownOK ld3In u := by
    intro p hp
    simp only [ld3In, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with hp | rfl
    · exact hglob.1 p hp
    · exact hbase
  obtain ⟨t, ht⟩ := Lower.dual_spec_run ld3_check ld3_run_equal u hpc hk0 (by simp [ld3Spec]) (by simp)
  have hm : ∀ A, t.getMem A = u.getMem A := fun A => by rw [ht.mem]; rfl
  have r19 : t.getReg .x8 = (kw 0x400000).eval u := ht.regs (.x8, kw 0x400000) (by simp [ld3Spec])
  have r21 : t.getReg .x24 = (E.ld (kw TOPLOAD)).eval u := ht.regs (.x24, .ld (kw TOPLOAD)) (by simp [ld3Spec])
  have r20 : t.getReg .x9 = (E.ld (kw (TOPLOAD + 8))).eval u :=
    ht.regs (.x9, .ld (kw (TOPLOAD + 8))) (by simp [ld3Spec])
  have r27 : t.getReg .x27 = (E.ld (kw (TOPLOAD + 16))).eval u :=
    ht.regs (.x27, .ld (kw (TOPLOAD + 16))) (by simp [ld3Spec])
  have r2 : t.getReg .x2 = (E.ld (kw (TOPLOAD + 24))).eval u :=
    ht.regs (.x2, .ld (kw (TOPLOAD + 24))) (by simp [ld3Spec])
  have e19 : t.getReg .x8 = BitVec.ofNat 64 0x400000 := r19
  have e21 : t.getReg .x24 = BitVec.ofNat 64 M2c := by
    rw [r21]
    change u.getMem (BitVec.ofNat 64 TOPLOAD) = _
    exact (htop 0 (by decide)).trans (by decide +kernel)
  have e20 : t.getReg .x9 = BitVec.ofNat 64 M1c := by
    rw [r20]
    change u.getMem (BitVec.ofNat 64 (TOPLOAD + 8)) = _
    exact (htop 1 (by decide)).trans (by decide +kernel)
  have e27 : t.getReg .x27 = BitVec.ofNat 64 (hw 4 3) := by
    rw [r27]
    change u.getMem (BitVec.ofNat 64 (TOPLOAD + 16)) = _
    exact (htop 2 (by decide)).trans (by decide +kernel)
  have e2 : t.getReg .x2 = BitVec.ofNat 64 0x3fe00 := by
    rw [r2]
    change u.getMem (BitVec.ofNat 64 (TOPLOAD + 24)) = _
    exact (htop 3 (by decide)).trans (by decide +kernel)
  have hG0 : Glob baseK w pk t := ht.glob _ _ _ hglob (RelOK.nil u)
  have hpk : preK 3 = baseK ++ [(.x8, BitVec.ofNat 64 0x400000), (.x24, BitVec.ofNat 64 M2c),
      (.x9, BitVec.ofNat 64 M1c), (.x27, BitVec.ofNat 64 (hw 4 3)), (.x2, BitVec.ofNat 64 0x3fe00),
      (.x12, BitVec.ofNat 64 256), (.x26, 6), (.x7, 1), (.x13, 2), (.x30, 7), (.x28, BitVec.ofNat 64 TOPBASE), (.x19, 3), (.x20, 4), (.x21, 5), (.x6, 0x10000)] := rfl
  have e28 : t.getReg .x28 = BitVec.ofNat 64 TOPBASE :=
    ht.known (.x28, BitVec.ofNat 64 TOPBASE) (by rw [ld3In]; exact List.mem_append_right _ (List.mem_singleton_self _))
  have e12 : t.getReg .x12 = BitVec.ofNat 64 256 := (ht.keep .x12 (by simp)).trans ha2
  have e26 : t.getReg .x26 = 6 := (ht.keep .x26 (by simp)).trans hs10
  have eOne : t.getReg .x7 = 1 := (ht.keep .x7 (by simp)).trans hOne
  have eTwo : t.getReg .x13 = 2 := (ht.keep .x13 (by simp)).trans hTwo
  have eSeven : t.getReg .x30 = 7 := (ht.keep .x30 (by simp)).trans hSeven
  have eThree : t.getReg .x19 = 3 := (ht.keep .x19 (by simp)).trans hThree
  have eFour : t.getReg .x20 = 4 := (ht.keep .x20 (by simp)).trans hFour
  have eFive : t.getReg .x21 = 5 := (ht.keep .x21 (by simp)).trans hFive
  have eCoord : t.getReg .x6 = 0x10000 := (ht.keep .x6 (by simp)).trans hCoord
  have hk : ∀ p ∈ preK 3, t.getReg p.1 = p.2 := by
    intro p hp
    rw [hpk] at hp
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with hp | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ht.known p (by rw [ld3In]; exact List.mem_append_left _ hp)
    · exact e19
    · exact e21
    · exact e20
    · exact e27
    · exact e2
    · exact e12
    · exact e26
    · exact eOne
    · exact eTwo
    · exact eSeven
    · exact e28
    · exact eThree
    · exact eFour
    · exact eFive
    · exact eCoord
  refine ⟨t, ht.steps, ⟨by norm_num, hidx, ⟨0, by rw [BC.nCopy_eq.1]; norm_num, by rw [ht.pc rfl]; rfl⟩, ⟨hk, hG0.2⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [show rReg 3 = .x22 from rfl, show BC.below 3 = 0 from rfl, pow_zero, Nat.div_one,
      ht.keep .x22 (by simp), hreg]
  · exact ⟨rfl, (hm _).trans hroot.1, (hm _).trans hroot.2⟩
  · exact (hwit.mono (fun o ho => Or.inr ho.1)).frame (fun j _ _ => hm _)
  · intro _
    exact ⟨(hm _).trans ((htop 4 (by decide)).trans (by decide +kernel)), (hm _).trans htop8⟩
  · intro h
    exact absurd h (by decide)
  · intro h
    exact absurd h (by decide)

-- Actual finite caller run equalities. Only symbolic fetches are replayed;
-- HASH answers and resulting lower-source outcomes are never assumed.
theorem setup_run_equal (lay : Layer) (c : Nat) (hc : c < nCopy lay.val) (d : Bool) :
    Verify.runAt (BC.preK lay.val) [] (setupPc lay.val (trPc lay.val c)) [.br d] =
      Lower.runAt (BC.preK lay.val) [] (setupPc lay.val (trPc lay.val c)) [.br d] := by
  fin_cases lay
  all_goals norm_num [nCopy, xtrTab] at hc
  all_goals interval_cases c <;> cases d <;> rfl

theorem decoder_run_equal (lay : Layer) (hlay : lay ≠ 0) (c : Nat) (hc : c < nCopy lay.val)
    (dirs : List Dir) (hd : dirs = [.br false, .br false, .jmp] ∨
      dirs = [.br false, .br true] ∨ dirs = [.br true]) :
    Verify.runAt (BC.bKB lay.val) [] (trPc lay.val c + stepsA lay.val + 1) dirs =
      Lower.runAt (BC.bKB lay.val) [] (trPc lay.val c + stepsA lay.val + 1) dirs := by
  rcases hd with rfl | rfl | rfl
  all_goals fin_cases lay
  all_goals try exact False.elim (hlay rfl)
  all_goals norm_num [nCopy, xtrTab] at hc
  all_goals interval_cases c <;> rfl

theorem leaf_run_equal (lay : Layer) (c : Nat) (hc : c < nCopy lay.val) :
    Verify.runAt (leafK lay.val) [] (trPc lay.val c + retOff lay.val) (lfDirs lay.val) =
      Lower.runAt (leafK lay.val) [] (trPc lay.val c + retOff lay.val) (lfDirs lay.val) := by
  fin_cases lay
  all_goals norm_num [nCopy, xtrTab] at hc
  all_goals interval_cases c <;> rfl

def EncodingRun : Prop := ∀ (w : WBytes) (pk : Digest) (index : Nat) (lay : Layer)
  (msg : LayerMsg) (s : MachineState), LayerIn w pk index lay.val msg s →
  (ClaudeWCT.W9.T3M.wbcCtr w lay).toNat < counterLimit →
  ∃ c, c < nCopy lay.val ∧ ∃ t,
    Lower.DualSpecRes (BC.allowed lay.val) [] baseK (BC.specA lay.val (trPc lay.val c))
      (BC.bK lay.val) keepA s t
def EncodingSetup : Prop :=
  ∀ (w : WBytes) (pk : Digest) (index : Nat) (lay : Layer)
    (msg : LayerMsg) (s : MachineState), LayerIn w pk index lay.val msg s →
  ((ClaudeWCT.W9.T3M.wbcCtr w lay).toNat ≥ T3.counterLimit →
    ∃ u, Steps InlineTail.image s (BC.rejectSteps lay.val) (BC.rejectSteps lay.val) u ∧
      fetch InlineTail.image u = some (.base .ECALL) ∧ u.getReg .x5 = 1 ∧ u.getReg .x10 = 1) ∧
  ((ClaudeWCT.W9.T3M.wbcCtr w lay).toNat < T3.counterLimit →
    ∃ t, Steps InlineTail.image s (stepsA lay.val) (stepsA lay.val) t ∧
      fetch InlineTail.image t = some (.base .ECALL) ∧ t.getReg .x5 = 0 ∧
      hashArgumentsValid t = true ∧
      hashInput t = toQ (T3.pad64 (ClaudeWCT.W9.T3M.layerEncodingInputP lay
        (route index lay).2 (route index lay).1 msg
        (ClaudeWCT.W9.T3M.wbcCtr w lay) (ClaudeWCT.W9.T3M.wbcPad w lay))) ∧
      ∃ c, c < nCopy lay.val ∧ EncPre w pk index lay.val c t)
theorem encoding_reject (w : WBytes) (pk : Digest) (index : Nat) (lay : Layer)
    (msg : LayerMsg) (s : MachineState) (hs : LayerIn w pk index lay.val msg s)
    (hge : (ClaudeWCT.W9.T3M.wbcCtr w lay).toNat ≥ counterLimit) :
    ∃ u, Steps InlineTail.image s (BC.rejectSteps lay.val) (BC.rejectSteps lay.val) u ∧
      fetch InlineTail.image u = some (.base .ECALL) ∧ u.getReg .x5 = 1 ∧ u.getReg .x10 = 1 := by
  obtain ⟨c, hc, hpc⟩ := hs.copy
  have hcc := (T3M.copy_parts lay.val (trPc lay.val c)
    (BC.copyCheck_at lay.val c lay.isLt hc)).2.1
  have hbrs : (BC.rejA lay.val (trPc lay.val c)).brs = [BC.ctrBr lay.val (!setupAcceptDir lay.val)] := by
    fin_cases lay <;> rfl
  obtain ⟨u, hu⟩ := Lower.dual_spec_run (by rw [← setup_run_equal lay c hc (!setupAcceptDir lay.val)]; exact hcc)
    (setup_run_equal lay c hc (!setupAcceptDir lay.val)) s hpc hs.glob.1 (by
    intro b hb
    rw [hbrs, List.mem_singleton] at hb
    subst b
    exact (BC.counter_branch w pk index lay msg s hs (!setupAcceptDir lay.val)).mpr (by by_cases h3 : lay.val = 3 <;> simp [setupAcceptDir, h3, hge, Nat.not_lt.mpr hge]))
    (by simp)
  exact ⟨u, (by fin_cases lay <;> exact hu.steps),
    hu.ecall (by fin_cases lay <;> rfl),
    hu.regs (.x5, kw 1) (by fin_cases lay <;> simp [BC.rejA, T3M.rejA]),
    hu.regs (.x10, kw 1) (by fin_cases lay <;> simp [BC.rejA, T3M.rejA])⟩

theorem encoding_run : EncodingRun := fun w pk index lay msg s hs hlt => by
  obtain ⟨c, hc, hpc⟩ := hs.copy
  have hcc := (T3M.copy_parts lay.val (trPc lay.val c)
    (BC.copyCheck_at lay.val c lay.isLt hc)).1
  have hbrs : (BC.specA lay.val (trPc lay.val c)).brs = [BC.ctrBr lay.val (setupAcceptDir lay.val)] := by
    fin_cases lay <;> rfl
  obtain ⟨t, ht⟩ := Lower.dual_spec_run (by rw [← setup_run_equal lay c hc (setupAcceptDir lay.val)]; exact hcc)
    (setup_run_equal lay c hc (setupAcceptDir lay.val)) s hpc hs.glob.1 (by
    intro b hb
    rw [hbrs, List.mem_singleton] at hb
    subst b
    exact (BC.counter_branch w pk index lay msg s hs (setupAcceptDir lay.val)).mpr (by by_cases h3 : lay.val = 3 <;> simp [setupAcceptDir, h3, hlt, Nat.not_le.mpr hlt])) (by simp)
  exact ⟨c, hc, t, ht⟩

theorem encoding_setup : EncodingSetup := fun w pk index lay msg s hs => by
  refine ⟨encoding_reject w pk index lay msg s hs, fun hlt => ?_⟩
  obtain ⟨c, hc, t, ht⟩ := encoding_run w pk index lay msg s hs hlt
  have hh : t.getReg .x5 = 0 ∧ hashArgumentsValid t = true ∧
      hashInput t = toQ (pad64 (ClaudeWCT.W9.T3M.layerEncodingInputP lay
        (route index lay).2 (route index lay).1 msg
        (ClaudeWCT.W9.T3M.wbcCtr w lay) (ClaudeWCT.W9.T3M.wbcPad w lay))) := by
    cases msg with
    | forest root => exact BC.forest_setup_hash w pk index lay root s hs c t ht.toOld
    | pair left right => exact BC.pair_setup_hash w pk index lay left right s hs c t ht.toOld
  exact ⟨t, (by fin_cases lay <;> exact ht.steps), ht.ecall (by fin_cases lay <;> rfl),
    hh.1, hh.2.1, hh.2.2, c, hc, BC.setup_post w pk index lay msg s hs c t ht.toOld⟩

theorem encB_step (w : WBytes) (pk : Digest) (index : Nat) (lay : Layer) (hlay : lay ≠ 0) (c : Nat) (hc : c < nCopy lay.val)
    (hidx : index < 2 ^ 31) (t : MachineState) (ht : EncPre w pk index lay.val c t) (a : BitVec 256) :
    (decode lay (a.extractLsb' 0 128) = none → ∃ v k cy, Steps InlineTail.image (writeHash t a) k cy v ∧
        fetch InlineTail.image v = some (.base .ECALL) ∧ v.getReg .x5 = 1 ∧ v.getReg .x10 = 1 ∧ k ≤ 23 ∧ cy ≤ 26) ∧
    (decode lay (a.extractLsb' 0 128) ≠ none → ∃ s0, Steps InlineTail.image (writeHash t a) (bSt lay.val) (bCy lay.val) s0 ∧
        (lctxOf w index lay a (trPc lay.val c)).ok ∧
        (∀ p ∈ (lctxOf w index lay a (trPc lay.val c)).known, s0.getReg p.1 = p.2) ∧
        (lctxOf w index lay a (trPc lay.val c)).Orig0 s0 ∧
        (lctxOf w index lay a (trPc lay.val c)).ChainIn s0 0 [] s0 ∧ Glob (chainK lay.val) w pk s0 ∧
        Verify.Orig w (fun o => 9288 ≤ o ∧ o < layerEnd lay.val) s0 ∧
        s0.getReg .x23 = BitVec.ofNat 64 (dispatchHeap lay.val (route index lay).1) ∧
        s0.getReg .x31 = BitVec.ofNat 64 (route index lay).2) := by
  set u := writeHash t a with hu
  have hcc := copy_parts lay.val (trPc lay.val c) (BC.copyCheck_at lay.val c lay.isLt hc)
  have hB := (hcc.2.2.2.1 (fun h => hlay (Fin.ext h)))
  have hkt : KnownOK (BC.bK lay.val) t := ht.glob.1
  obtain ⟨d, h12, hdc⟩ : ∃ d, t.getReg .x12 = BitVec.ofNat 64 d ∧
      (if lay.val = 3 then d = 256 else (d = x10In lay.val ∨ d = x10In lay.val + 48)) := by
    by_cases h3 : lay.val = 3
    · refine ⟨256, hkt (.x12, 256) ?_, by rw [if_pos h3]⟩
      unfold BC.bK; rw [if_pos h3]; simp [bK, h3]
    · have h12' : lay.val = 1 ∨ lay.val = 2 := by
        have := lay.isLt; have h0 : lay.val ≠ 0 := fun h => hlay (Fin.ext h); omega
      obtain ⟨d, hd, hdd⟩ := ht.dstL h12'
      exact ⟨d, hd, by rw [if_neg h3]; exact hdd⟩
  have hdv : d = 256 ∨ d = 18760 ∨ d = 18808 ∨ d = 21896 ∨ d = 21944 := by
    fin_cases lay
    · exact absurd rfl hlay
    all_goals simp [x10In] at hdc; omega
  have hku : KnownOK (BC.bK lay.val) u := fun p hp => by rw [hu, writeHash_getReg]; exact hkt p hp
  have hkuB : KnownOK (BC.bKB lay.val) u := fun p hp => hku p (List.mem_of_mem_filter hp)
  have hx12u : u.getReg .x12 = BitVec.ofNat 64 d := by rw [hu, writeHash_getReg]; exact h12
  have hobl : ∀ o ∈ BC.oblB, o.holds u := by
    intro o ho
    simp only [BC.oblB, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;>
      simp only [Oblig.holds, Addr.eval, E.eval, hx12u] <;>
      rcases hdv with rfl | rfl | rfl | rfl | rfl <;> decide
  have hpcu : u.pc = pcOf (trPc lay.val c + stepsA lay.val + 1) := by
    rw [hu, writeHash_pc, ht.pc, show (4 : Word) = BitVec.ofNat 64 4 from rfl, ofNat_add_ofNat]
    congr 1
  have hans : AnsAt u a := by
    constructor
    · simp only [a6E, E.eval]
      rw [hx12u, hu]
      exact writeHash_at0 t a d h12 (by omega)
    · simp only [a7E, E.eval, BinOp.eval, kw]
      rw [hx12u, hu, ofNat_add_ofNat]
      exact writeHash_at8 t a d h12 (by omega)
  have hdec := decode_lower lay hlay (a.extractLsb' 0 128)
  have hS := lowSum_lt (ansV a)
  constructor
  · intro hnone
    by_cases hr : (a.extractLsb' 64 64).toNat / 2 ^ 62 ≠ 0
    · obtain ⟨v, hv⟩ := Lower.dual_spec_run (by rw [← decoder_run_equal lay hlay c hc _ (Or.inr (Or.inr rfl))]; exact hB.2.2)
      (decoder_run_equal lay hlay c hc _ (Or.inr (Or.inr rfl))) u hpcu hkuB (by
        intro b hb; simp only [rejRng, List.mem_singleton] at hb; subst hb
        exact (rngBr_iff hans 62 (by norm_num) true).mpr (by rw [decide_eq_true hr])) hobl
      exact ⟨v, 7, 7, hv.steps, hv.ecall rfl, hv.regs (.x5, kw 1) (by simp [rejRng]),
        hv.regs (.x10, kw 1) (by simp [rejRng]), by norm_num, by norm_num⟩
    · have hr' : ansV a / 2 ^ 64 < 2 ^ 62 := by rw [ansV_hi]; omega
      have hck : ¬ (tgtL lay.val + 2 ^ 64 - lowSum (ansV a)) % 2 ^ 64 < 8 := by
        intro hck
        rw [hdec, if_neg (by rw [ansV_hi]; simpa using hr)] at hnone
        rw [if_pos (by rw [← tgtL_eq]; exact hck)] at hnone
        cases hnone
      obtain ⟨v, hv⟩ := Lower.dual_spec_run (by rw [← decoder_run_equal lay hlay c hc _ (Or.inr (Or.inl rfl))]; exact hB.2.1)
      (decoder_run_equal lay hlay c hc _ (Or.inr (Or.inl rfl))) u hpcu hkuB (by
        intro b hb; simp only [rejCk, List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · exact (ckBr_iff hans hr' lay true).mpr (by rw [decide_eq_true hck])
        · exact (rngBr_iff hans 62 (by norm_num) false).mpr (by rw [decide_eq_false hr])) hobl
      exact ⟨v, 21, 24, hv.steps, hv.ecall rfl, hv.regs (.x5, kw 1) (by simp [rejCk]),
        hv.regs (.x10, kw 1) (by simp [rejCk]), by norm_num, by norm_num⟩
  · intro hsome
    have hr0 : (a.extractLsb' 64 64).toNat / 2 ^ 62 = 0 := by
      by_contra hne
      apply hsome; rw [hdec, if_pos (by rw [ansV_hi]; exact hne)]
    have hr' : ansV a / 2 ^ 64 < 2 ^ 62 := by rw [ansV_hi]; omega
    have hck : (tgtL lay.val + 2 ^ 64 - lowSum (ansV a)) % 2 ^ 64 < 8 := by
      by_contra hck
      apply hsome
      rw [hdec, if_neg (by rw [ansV_hi]; simpa using hr0), if_neg (by rw [← tgtL_eq]; exact hck)]
    obtain ⟨s0, hs0⟩ := Lower.dual_spec_run (by rw [← decoder_run_equal lay hlay c hc _ (Or.inl rfl)]; exact hB.1)
      (decoder_run_equal lay hlay c hc _ (Or.inl rfl)) u hpcu hkuB (by
      intro b hb; simp only [specBl, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact (ckBr_iff hans hr' lay false).mpr (by rw [decide_eq_false (not_not_intro hck)])
      · exact (rngBr_iff hans 62 (by norm_num) false).mpr (by rw [decide_eq_false (fun h => h hr0)])) hobl
    set L := lctxOf w index lay a (trPc lay.val c) with hL
    have htp := trPc_lt lay.val c
    have hko : KnownOK (postBl lay.val (trPc lay.val c)) s0 := by
      have hk0 := hs0.known
      by_cases h3 : lay.val = 3
      · rw [postBlC, if_pos h3] at hk0
        have e22 : s0.getReg .x22 = BitVec.ofNat 64 (s6v lay.val) := by
          rw [hs0.regs (.x22, .ld (kw (TOPLOAD - 8))) (by simp [specBl, h3]), h3]
          change u.getMem (BitVec.ofNat 64 (TOPLOAD - 8)) = _
          have hd3 : d = 256 := by rw [if_pos h3] at hdc; exact hdc
          rw [hu, writeHash_frame t a d (TOPLOAD - 8) h12 (by unfold TOPLOAD; omega)
            (by omega) (Or.inr (by unfold TOPLOAD; omega))]
          exact (ht.hdr3 h3).2
        intro q hq
        simp only [postBl, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with hq | rfl | rfl | rfl
        · exact hk0 q (List.mem_append_left _ hq)
        · exact e22
        · exact hk0 _ (by simp)
        · exact hk0 _ (by simp)
      · rw [postBlC, if_neg h3] at hk0
        exact hk0
    have hkeep := hs0.keep
    have e17 : (a7lE.eval u) = a7lW a := by
      simp only [a7lE, b1E, E.eval, BinOp.eval, a7E_eval hans, a6E_eval hans, kw, a7lW]
      rfl
    have e29 : ((t4E lay.val).eval u) = 7#64 - BitVec.ofNat 64 (ckOf lay a) := by
      have hT : tgtL lay.val ≤ 198 := by fin_cases lay <;> decide
      have hT7 : 7 ≤ tgtL lay.val := by fin_cases lay <;> decide
      have hS' : lowSum (ansV a) < 4095 := lowSum_lt (ansV a)
      have hle : lowSum (ansV a) ≤ tgtL lay.val ∧ tgtL lay.val - lowSum (ansV a) < 8 := by omega
      have hcv : ckOf lay a = tgtL lay.val - lowSum (ansV a) := by unfold ckOf; omega
      rw [hcv]
      apply BitVec.eq_of_toNat_eq
      simp only [t4E, E.eval, BinOp.eval, kw]
      rw [BitVec.toNat_add, sumE_eval hans hr', BitVec.toNat_sub]
      simp only [BitVec.toNat_ofNat]
      omega
    have hLok : L.ok := by
      refine ⟨tree_lt index lay hidx, leaf_lt32 index lay, by simp [hL, lctxOf], ?_, ?_, ?_, ?_, ?_,
        by simp [hL, lctxOf], tree_actual_lt index lay hidx, ?_⟩
      · simp only [hL, lctxOf]; fin_cases lay <;> decide
      · simp only [hL, lctxOf]; fin_cases lay <;> simp [s6v]
      · simp only [hL, lctxOf]; fin_cases lay <;> decide
      · simp only [hL, lctxOf]; unfold ckOf at hck ⊢; omega
      · simp only [hL, lctxOf]; unfold retOff; split_ifs <;> omega
      · simpa only [hL, lctxOf, hL_eq] using leaf_lt index lay
    have hGu : Glob (BC.bK lay.val) w pk u := by
      have := Glob_writeHash ht.glob a d h12 (by rcases hdv with rfl | rfl | rfl | rfl | rfl <;> decide)
      exact this
    have hGs0 := hs0.glob _ w pk hGu (RelOK.nil u)
    have hOu : Verify.Orig w (fun o => 9288 ≤ o ∧ o < layerEnd lay.val) u := by
      have := Orig_writeHash ht.orig a d h12 (by omega)
      have hxl : lay.val ≠ 3 → x10In lay.val = WIT + layerEnd lay.val := by
        fin_cases lay <;> decide
      have hL8 : layerEnd lay.val % 8 = 0 := by
        fin_cases lay <;> decide
      intro j hj hp
      refine this j hj ⟨hp, ?_⟩
      have hp2 := hp.2
      by_cases h3 : lay.val = 3
      · rw [if_pos h3] at hdc
        exact Or.inr (by unfold WIT; omega)
      · rw [if_neg h3] at hdc
        have hx := hxl h3
        exact Or.inl (by omega)
    have hOs0 : Verify.Orig w (fun o => 9288 ≤ o ∧ o < layerEnd lay.val) s0 := by
      have := hs0.toOld.orig_const hOu
      exact this.mono (fun o ho => ⟨ho, by simp⟩)
    have hpc0 : s0.pc = pcOf (L.startPc 0) := by
      rw [hs0.spc tgtl rfl]
      simp only [tgtl, E.eval, BinOp.eval, a6E_eval hans, kw]
      have hk0 : L.kOf 0 = (a.extractLsb' 0 64).toNat % 512 := by
        rw [L.kOf_eq 0 (by norm_num), if_pos (by norm_num)]
        show (a.extractLsb' 0 64).toNat / 2 ^ (9 * (0 % 7)) % 512 = _
        rw [show 9 * (0 % 7) = 0 from rfl, pow_zero, Nat.div_one]
      have hm : ((a.extractLsb' 0 64) <<< ((BitVec.ofNat 64 9).toNat % 64) &&& BitVec.ofNat 64 0x3fe00) =
          BitVec.ofNat 64 (512 * L.kOf 0) := by
        apply BitVec.eq_of_toNat_eq
        rw [toNat_andc _ _ (by norm_num), toNat_sll _ 9 (by norm_num), show (0x3fe00 : Nat) = 512 * (2 ^ 9 - 1) by norm_num,
          land_mask _ _ (le_refl _), field_shl _ _ _ (le_refl _) (le_refl _), hk0, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (show 512 * ((a.extractLsb' 0 64).toNat % 512) < 2 ^ 64 by omega)]
        rw [Nat.sub_self, pow_zero, Nat.div_one]
        rfl
      rw [hm]
      have e2 : BitVec.ofNat 64 (512 * L.kOf 0) + BitVec.ofNat 64 448800 =
          BitVec.ofNat 64 (0x1000 + 4 * entW 0 (L.kOf 0)) := by
        rw [ofNat_add_ofNat]; congr 1; unfold entW ttabIdx; omega
      rw [e2, even_andNot1' _ (by omega)]
      unfold LCtx.startPc; simp
    have hkL : ∀ q ∈ chainK lay.val, s0.getReg q.1 = q.2 := fun q hq => hko q (by simp [postBl, hq])
    refine ⟨s0, hs0.steps, hLok, ?_, ?_, ⟨⟨fun _ _ => rfl, Frame.refl _ _, fun j hj => by simp at hj⟩, rfl,
      hGs0.2.2.2.2.2, hpc0⟩, ⟨hkL, hGs0.2.1, hGs0.2.2.1, hGs0.2.2.2.1, hGs0.2.2.2.2⟩, hOs0, ?_, ?_⟩
    ·
      apply lctxOf_known w index lay a (trPc lay.val c) s0 hko
      · rw [hs0.regs (.x28, packedRouteE lay.val) (by simp [specBl])]
        simpa only [Nat.add_zero] using packedRouteE_eval lay _ _ u
          (tree_lt index lay hidx) (by simpa only [hL_eq] using leaf_lt index lay)
          (routed_lt index lay hidx)
          (by rw [hu, writeHash_getReg, ht.tp lay rfl]) (by
            intro h1
            obtain rfl : lay = 1 := Fin.ext h1
            rw [route_snd, show below (1 : Layer).val = 12 from rfl,
              show T3M.hL (1 : Layer).val = 7 from rfl]
            norm_num
            omega)
          (by rw [hu, writeHash_getReg, ht.t5 lay rfl (fun h => hlay (Fin.ext h))]) (by
            intro h3
            rw [hu, writeHash_getReg, ht.index3 h3]
            congr 1
            obtain rfl : lay = 3 := Fin.ext h3
            rw [route_fst, route_snd, ← hL_eq (3 : Layer),
              show below (3 : Layer).val = 0 from rfl]
            simp only [Nat.zero_add, pow_zero, Nat.div_one]
            simpa only [Nat.add_comm, Nat.mul_comm] using
              (Nat.mod_add_div index (2 ^ T3M.hL (3 : Layer).val)).symm) (by
            intro h12'
            rw [hu, writeHash_getReg, ht.packed12 h12']
            have he : (route index lay).2 * 2 ^ height lay + (route index lay).1 =
                index / 2 ^ T3M.below lay.val := by
              rw [route_fst, route_snd, ← hL_eq, Nat.pow_add, ← Nat.div_div_eq_div_mul]
              simpa only [Nat.add_comm, Nat.mul_comm] using
                (Nat.mod_add_div (index / 2 ^ T3M.below lay.val) (2 ^ T3M.hL lay.val))
            simpa only [BC.below, T3M.below] using
              congrArg (fun q : Nat => BitVec.ofNat 64 (q * 65536)) he.symm) (by
            by_cases h3 : lay.val = 3
            · have hd3 : d = 256 := by rw [if_pos h3] at hdc; exact hdc
              rw [hdrA, if_pos h3, hu, writeHash_frame t a d (TOPLOAD + 32) h12 (by unfold TOPLOAD; omega)
                (by omega) (Or.inr (by unfold TOPLOAD; omega)), h3]
              exact (ht.hdr3 h3).1
            · rw [hdrA, if_neg h3]
              exact hGu.2.2.2.2.2.prefix lay.val lay.isLt)
      · rw [hkeep .x4 (by simp [keepB]), hu, writeHash_getReg, ht.tp lay rfl]
      · rw [hs0.regs (.x16, a6E) (by simp [specBl]), a6E_eval hans]
      · rw [hs0.regs (.x17, a7lE) (by simp [specBl]), e17]
      · rw [hs0.regs (.x29, t4E lay.val) (by simp [specBl]), e29]
    ·
      intro i hi hi' k hk
      have hb := L.blk_props hLok i hi'
      have hS6 : L.S6 = s6v lay.val := rfl
      have hlb : 0x800 + (layerEnd lay.val) = L.S6 + 64 + 64 * 0 + 0 ∨ True := Or.inr trivial
      apply origW_of hOs0 _ (by unfold WIT; omega) (by
          unfold WIT; simp only [LCtx.blk, hS6]; fin_cases lay <;> simp [s6v] <;> omega)
        (by unfold WIT WX; omega)
      simp only [LCtx.blk, hS6]
      unfold WIT
      fin_cases lay <;> simp [s6v, layerEnd] <;> omega
    · rw [hkeep .x23 (by simp [keepB]), hu, writeHash_getReg, ht.s7 lay rfl]
    · rw [hkeep .x31 (by simp [keepB]), hu, writeHash_getReg, ht.t5 lay rfl (fun h => hlay (Fin.ext h))]

theorem leafL_step (w : WBytes) (pk : Digest) (index : Nat) (lay : Layer) (hlay : lay ≠ 0) (c : Nat)
    (hc : c < nCopy lay.val) (hidx : index < 2 ^ 31) (a : BitVec 256) (s0 : MachineState)
    (hk : ∀ p ∈ (lctxOf w index lay a (trPc lay.val c)).known, s0.getReg p.1 = p.2)
    (hG : Glob (chainK lay.val) w pk s0) (hO : Verify.Orig w (fun o => 9288 ≤ o ∧ o < layerEnd lay.val) s0)
    (h23 : s0.getReg .x23 = BitVec.ofNat 64 (dispatchHeap lay.val (route index lay).1))
    (h30 : s0.getReg .x31 = BitVec.ofNat 64 (route index lay).2)
    (ends : List Digest) (t : MachineState)
    (ht : (lctxOf w index lay a (trPc lay.val c)).ChainOut s0 43 ends t) :
    ∃ u, Steps InlineTail.image t (lfSteps lay.val) (lfSteps lay.val) u ∧ LeafOut w pk index lay ends u := by
  set L := lctxOf w index lay a (trPc lay.val c) with hLd
  have h0 : lay.val ≠ 0 := fun h => hlay (Fin.ext h)
  obtain ⟨⟨hR, hF, hS⟩, hlen, hpc⟩ := ht
  have hkL : ∀ q ∈ chainK lay.val, s0.getReg q.1 = q.2 := hG.1
  have hknown : KnownOK (leafK lay.val) t := by
    intro p hp
    simp only [leafK, baseK, if_neg h0, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with ((rfl | rfl) | rfl) | rfl | rfl
    · rw [hR .x5 (by simp [chainRegs])]; exact hkL (_, _) (by simp [chainK, baseK])
    · rw [hR .x18 (by simp [chainRegs])]; exact hkL (_, _) (by simp [chainK, baseK])
    · rw [hR .x27 (by simp [chainRegs])]; exact hkL (_, _) (by simp [chainK])
    · rw [hR .x7 (by simp [chainRegs])]; exact hkL (_, _) (by simp [chainK])
    · rw [hR .x15 (by simp [chainRegs])]; exact hk (.x15, 0x6e000) (by simp [LCtx.known])
  obtain ⟨u, hu⟩ := Lower.dual_spec_run (by rw [← leaf_run_equal lay c hc]; exact leafCheck_at lay.val c lay.isLt hc)
    (leaf_run_equal lay c hc) t (by rw [hpc]; rfl) hknown
    (by intro b hb; simp [specLf, h0] at hb) (by simp)
  have hst := hu.steps
  rw [show (specLf lay.val).steps = lfSteps lay.val by simp [specLf, lfSteps, h0],
    show (specLf lay.val).cycles = lfSteps lay.val by simp [specLf, lfSteps, h0]] at hst
  refine ⟨u, hst, ?_⟩
  have hku : KnownOK (postLf lay.val) u := hu.known
  have hkeep := hu.keep
  have hmem : ∀ A, u.getMem A = memEval t [(⟨none, BitVec.ofNat 64 792⟩, .reg .x4),
      (⟨none, BitVec.ofNat 64 784⟩, kw (hw 2 lay.val))] A := by
    intro A; rw [hu.mem]; simp [specLf, h0]
  have hfr : ∀ A, A < 2 ^ 64 → A ≠ 792 → A ≠ 784 → u.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1 h2
    rw [hmem]
    apply memEval_frame_ofNat t _ A hA
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp <;> omega
  have htr := tree_lt index lay hidx
  have hlf := leaf_lt index lay
  obtain ⟨hg1, hg2, hg3, hg4⟩ := geomL lay hlay
  have hS6 : L.S6 = s6v lay.val := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun h => absurd h hlay, ?_⟩
  ·
    rw [hu.spc (tgtLf lay.val) (by simp [specLf, h0])]
    have := hL_le lay
    exact tgtLf_lower_eval lay hlay t _ hlf
      (by rw [hR .x23 (by simp [chainRegs]), h23])
  ·
    have hGt : Glob baseK w pk t := glob_frame hG hF (fun A hA => by
        unfold LCtx.Wr LCtx.blk at hA; rw [hS6] at hA
        have : slotL L.i0 = 768 := rfl
        rw [this] at hA
        rcases hA with hA | hA <;> omega)
      (fun p hp => hknown p (by simp [leafK, hp]))
    have hGu := hu.glob _ w pk hGt (RelOK.nil t)
    refine ⟨fun p hp => ?_, hGu.2.1, hGu.2.2.1, hGu.2.2.2.1, hGu.2.2.2.2⟩
    rcases List.mem_append.mp hp with hp | hp
    · exact hku p hp
    · have h22 : s0.getReg .x22 = BitVec.ofNat 64 (s6v lay.val) :=
        hk (.x22, BitVec.ofNat 64 L.S6) (by simp [LCtx.known])
      have m6 : ((.x7 : Reg), (1 : Word)) ∈ postLf lay.val := by
        simp [postLf, leafK, h0]
      simp only [lfKeepK, if_neg h0, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)
      all_goals first
        | exact hku _ m6
        | rw [hkeep _ (by simp [keepLfAll, h0]), hR _ (by simp [chainRegs])]; exact h22
        | rw [hkeep _ (by simp [keepLfAll, h0]), hR _ (by simp [chainRegs])]; exact hkL (_, _) (by simp [chainK])
  · rw [hkeep .x23 (by simp [keepLfAll, h0]), hR .x23 (by simp [chainRegs]), h23]
  · intro _; rw [hkeep .x31 (by simp [keepLfAll, h0]), hR .x31 (by simp [chainRegs]), h30]
  · rw [hlen, LCtx.chainCount_lower lay hlay]; rfl
  · intro j hj
    rw [LCtx.chainCount_lower lay hlay] at hj
    have e := hS j (by rw [hlen]; exact hj)
    have hj0 : slotL (L.i0 + j) = slotL j := by rw [show L.i0 = 0 from rfl, Nat.zero_add]
    rw [hj0] at e
    simp only [lfSlot, if_neg h0]
    have hsl : slotL j = 768 ∨ 800 ≤ slotL j := by unfold slotL; split <;> omega
    have hsl' : slotL j < 2 ^ 32 := by unfold slotL; split <;> omega
    exact ⟨(hfr (slotL j) (by omega) (by omega) (by omega)).trans e.1,
      (hfr (slotL j + 8) (by omega) (by omega) (by omega)).trans e.2⟩
  · rw [show lfBase lay.val + 16 = 784 by simp [lfBase, h0], hmem,
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_neg (by norm_num),
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_pos rfl]
    simp only [E.eval, kw]
    rw [hw2_hdr0 lay _ htr]
  · rw [show lfBase lay.val + 24 = 792 by simp [lfBase, h0], hmem,
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_pos rfl]
    simp only [E.eval]
    rw [hR .x4 (by simp [chainRegs]), hk (.x4, BitVec.ofNat 64 L.w1) (by simp [LCtx.known])]
    rfl
  ·
    have hOt : Verify.Orig w (fun o => 9288 ≤ o ∧ o < layerBase lay + 64 * height lay) t :=
      (hO.mono (fun o ho => ⟨ho.1, by omega⟩)).frame (fun j hj hp => hF.get (by unfold WIT WX at *; omega)
        (fun hw => by
          unfold LCtx.Wr at hw; rw [hS6] at hw
          unfold WIT at hw
          rcases hw with hw | hw <;> omega))
    exact (hu.toOld.orig_const hOt).mono (fun o ho => ⟨ho, by simp⟩)
structure TopLeafReady (w : WBytes) (pk : Digest) (index c : Nat) (ends : List Digest)
    (t : MachineState) : Prop where
  pc : ∃ dB dC, dB < 4 ∧ dC < 4 ∧ t.pc = pcOf (Nonbinary.pcX 17 dB dC)
  glob : Glob (leafK 0) w pk t
  keep : KnownOK (lfKeepK 0) t
  s7 : t.getReg .x23 = BitVec.ofNat 64 (2 ^ hL 0 + (route index 0).1)
  t5 : True
  tp : t.getReg .x4 = BitVec.ofNat 64 (hdr1 (route index 0).2 (route index 0).1)
  len : ends.length = 54
  ends : ∀ j < 54, DigAt t (slotT j) (ends.getD j 0)
  orig : Verify.Orig w (fun o => 9288 ≤ o ∧ o < layerBase 0 + 64 * height 0) t

theorem layer_good_low (w : WBytes) (pk : Digest) (index : Nat) (lay : Layer) (hlay : lay ≠ 0) (M : ClaudeWCT.WCT9.LayerMsg)
    (s : MachineState) (hs : LayerIn w pk index lay.val M s) {β : Type} (R : List Digest → T3.M (Option β))
    (K : Option β → OracleComp HashSpec Obs) (hK0 : K none = pure (false, 0)) (N C A : Nat) (Q : Prop)
    (hR : ∀ ends u, LeafOut w pk index lay ends u → W9Machine.GoodQFor InlineTail.image u N C Q A (ccM (R ends) K)) :
    W9Machine.GoodQFor InlineTail.image s (N + layerFuel lay.val) (C + layerCost lay.val 0) Q (A + layerCost lay.val 0)
      (ccM (layerHead w index lay M R) K) := by
  have h0 : lay.val ≠ 0 := fun h => hlay (Fin.ext h)
  have hidx := hs.idx
  have hA := encoding_setup w pk index lay M s hs
  have hT : 9 * tgtL lay.val ≤ 2950 := by fin_cases lay <;> decide
  have hfuel : layerFuel lay.val = stepsA lay.val + 1 + bSt lay.val + 1720 + lfSteps lay.val := by
    simp [layerFuel, stB, chainFuel, h0]
  have hcost : layerCost lay.val 0 = stepsA lay.val + 8 + bCy lay.val + lfSteps lay.val + (2950 - 9 * tgtL lay.val) := by
    simp only [layerCost, cyB, chainCost0, if_neg h0]; omega
  have hbS : 27 ≤ bSt lay.val := by unfold bSt; split_ifs <;> omega
  have hbC : 30 ≤ bCy lay.val := by unfold bCy; split_ifs <;> omega
  have hrej : BC.rejectSteps lay.val ≤ stepsA lay.val + 3 := by
    unfold BC.rejectSteps; split_ifs <;> omega
  unfold layerHead
  by_cases hctr : (ClaudeWCT.W9.T3M.wbcCtr w lay).toNat ≥ counterLimit
  · rw [if_pos hctr, ccM_pure, hK0]
    obtain ⟨u, hst, hf, h5, h10⟩ := hA.1 hctr
    exact W9Machine.GoodQFor.steps' hst (W9Machine.GoodQFor.reject (Q := Q) (A := 0) hf h5 h10) (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
  · rw [if_neg hctr]
    obtain ⟨t, hst, hf, h5, hv, hin, c, hc, hpre⟩ := hA.2 (by omega)
    have hblk := BC.encoding_blocks w lay (route index lay).2 (route index lay).1 M
    have H : ∀ a : BitVec 256, W9Machine.GoodQFor InlineTail.image (writeHash t a) (N + lfSteps lay.val + 1720 + bSt lay.val)
        (C + lfSteps lay.val + (2950 - 9 * tgtL lay.val) + bCy lay.val)
        Q (A + lfSteps lay.val + (2950 - 9 * tgtL lay.val) + bCy lay.val)
        (ccM (match decode lay (a.extractLsb' 0 128) with
          | none => pure none
          | some digits => chainsP w lay (route index lay).2 (route index lay).1 digits >>= R) K) := by
      intro a
      have hB := encB_step w pk index lay hlay c hc hidx t hpre a
      cases hds : decode lay (a.extractLsb' 0 128) with
      | none =>
        dsimp only
        rw [ccM_pure, hK0]
        obtain ⟨v, k, cy, hst', hf', h5', h10', hk, hcy⟩ := hB.1 hds
        exact W9Machine.GoodQFor.steps' hst' (W9Machine.GoodQFor.reject (Q := Q) (A := 0) hf' h5' h10') (by omega) (by omega)
          (fun hq => ⟨hq, by omega⟩)
      | some ds =>
        dsimp only
        obtain ⟨s0, hst0, hLok, hkn, hO0, hIn, hG0, hOr0, h23, h30⟩ := hB.2 (by rw [hds]; simp)
        set L := lctxOf w index lay a (trPc lay.val c) with hLd
        have hD := lctx_digits w index lay a (trPc lay.val c) hlay ds hds
        have hsum := LCtx.decode_lower_sum lay hlay _ ds hds
        have hck : L.ck < 8 := ckOf_lt lay hlay a ds hds
        have hacc := L.lowCost_accept hck ds hD hsum.1 (target lay) hsum.2
        rw [← tgtL_eq] at hacc
        have hP := L.lowP_eq hlay rfl ds hD (s6v_chainBlock lay hlay)
        have hG : W9Machine.GoodQFor InlineTail.image s0
            ((N + lfSteps lay.val) + 1720) ((C + lfSteps lay.val) + L.lowCost) Q
            ((A + lfSteps lay.val) + L.lowCost) (Verify.ccM L.lowP (fun ends => ccM (R ends) K)) :=
          L.inline_lower_good hLok rfl rfl hck hkn hO0 (fun ends => ccM (R ends) K)
            (N + lfSteps lay.val) (C + lfSteps lay.val) (A + lfSteps lay.val) Q
            (fun ends t ht => by
              obtain ⟨u, hstu, hu⟩ := leafL_step w pk index lay hlay c hc hidx a s0 hkn hG0 hOr0 h23 h30 ends t ht
              exact W9Machine.GoodQFor.steps' hstu (hR ends u hu) (by omega) (by omega) (fun hq => ⟨hq, by omega⟩))
            s0 hIn
        have e : chainsP w lay (route index lay).2 (route index lay).1 ds = L.lowP := by
          rw [hP]; unfold chainsP; rw [LCtx.chainCount_lower lay hlay]; rfl
        rw [ccM_bind, e]
        exact W9Machine.GoodQFor.steps' hst0 hG (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
    have := W9Machine.GoodQFor.shortHash_bind (f := fun answer => match decode lay answer with
      | none => pure none
      | some digits => chainsP w lay (route index lay).2 (route index lay).1 digits >>= R) hf h5 hv hin H
    rw [hblk] at this
    exact W9Machine.GoodQFor.steps' hst this (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)

-- Real native top128 decoder on the unchanged prefix. All actual c7 raw
-- table consumers retain their original three-byte/packed/raw predicates.
-- Only execution-image bindings change; no old completed decoder result is
-- assumed. Private literal witnesses are rechecked in this namespace.
theorem head_spec (s : MachineState) (v : Digest) (d : Nat)
    (hpc : s.pc = pcOf 96160) (h12 : s.getReg .x12=BitVec.ofNat 64 d)
    (hd : d=15560 ∨ d=15608) (hv : DigAt s d v) :
    ∃ t, Steps InlineTail.image s 4 4 t ∧
      t.pc = (if v.toNat < 2 ^ 125 then pcOf 96164 else pcOf 96230) ∧
      t.getReg .x16 = v.extractLsb' 0 64 ∧ t.getReg .x17 = v.extractLsb' 64 64 ∧
      RegsExcept s t [.x16,.x17,.x14] ∧ Frame s t (fun _ => False) := by
  rcases hd with rfl | rfl
  all_goals
    have h0 : s.getMem (s.getReg .x12)=v.extractLsb' 0 64 := by rw [h12]; exact hv.1
    have h1 : s.getMem (s.getReg .x12+8)=v.extractLsb' 64 64 := by
      rw [h12,show (8 : Word)=BitVec.ofNat 64 8 from rfl,ofNat_add_ofNat]; exact hv.2
    refine ⟨_, symRun_sound headBase (Lower.prefix_codeAt_transfer 96160 headCode head_at (by decide)) s hpc
      (by simp [headBase.res,rv_simp,h12] <;> decide), ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Result.toState_pc,headBase.res,E.eval,CmpOp.eval,BinOp.eval,h12,
        ofNat_add_ofNat,hv.2,
        BitVec.toNat_ofNat,Nat.reduceMod,bne_iff_ne,ne_eq,
        v4_ext64_shr_eq_zero v 61 (by decide),show (64+61 : Nat)=125 from rfl]
      split_ifs <;> first | rfl | omega
    · simpa only [Result.toState_getReg,headBase.res,rv_simp] using h0
    · simpa only [Result.toState_getReg,headBase.res,rv_simp] using h1
    · intro r hr; cases r <;> simp at hr <;> simp [headBase.res,rv_simp] <;> rfl
    · intro A _ _; simp [headBase.res,rv_simp]
#print axioms head_at
#print axioms head_spec

private theorem pf_96164 : CodeAt InlineTail.image (pcOf 96164) pairInitCode := by
  apply Lower.prefix_codeAt_transfer 96164 _ ?_ (by decide)
  have h := codeAt_from 96164 (by decide)
  have hp : pairInitCode <+: codeFrom 96164 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96166 : CodeAt InlineTail.image (pcOf 96166) pairPtr0Code := by
  apply Lower.prefix_codeAt_transfer 96166 _ ?_ (by decide)
  have h := codeAt_from 96166 (by decide)
  have hp : pairPtr0Code <+: codeFrom 96166 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96168 : CodeAt InlineTail.image (pcOf 96168) [0x00074c83] := by
  apply Lower.prefix_codeAt_transfer 96168 _ ?_ (by decide)
  have h := codeAt_from 96168 (by decide)
  have hp : [0x00074c83] <+: codeFrom 96168 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96169 : CodeAt InlineTail.image (pcOf 96169) pairShift0Code := by
  apply Lower.prefix_codeAt_transfer 96169 _ ?_ (by decide)
  have h := codeAt_from 96169 (by decide)
  have hp : pairShift0Code <+: codeFrom 96169 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96170 : CodeAt InlineTail.image (pcOf 96170) pairPtrCode := by
  apply Lower.prefix_codeAt_transfer 96170 _ ?_ (by decide)
  have h := codeAt_from 96170 (by decide)
  have hp : pairPtrCode <+: codeFrom 96170 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96172 : CodeAt InlineTail.image (pcOf 96172) [0x00074703] := by
  apply Lower.prefix_codeAt_transfer 96172 _ ?_ (by decide)
  have h := codeAt_from 96172 (by decide)
  have hp : [0x00074703] <+: codeFrom 96172 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96173 : CodeAt InlineTail.image (pcOf 96173) pairTailCode := by
  apply Lower.prefix_codeAt_transfer 96173 _ ?_ (by decide)
  have h := codeAt_from 96173 (by decide)
  have hp : pairTailCode <+: codeFrom 96173 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96175 : CodeAt InlineTail.image (pcOf 96175) pairPtrCode := by
  apply Lower.prefix_codeAt_transfer 96175 _ ?_ (by decide)
  have h := codeAt_from 96175 (by decide)
  have hp : pairPtrCode <+: codeFrom 96175 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96177 : CodeAt InlineTail.image (pcOf 96177) [0x00074703] := by
  apply Lower.prefix_codeAt_transfer 96177 _ ?_ (by decide)
  have h := codeAt_from 96177 (by decide)
  have hp : [0x00074703] <+: codeFrom 96177 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96178 : CodeAt InlineTail.image (pcOf 96178) pairTailCode := by
  apply Lower.prefix_codeAt_transfer 96178 _ ?_ (by decide)
  have h := codeAt_from 96178 (by decide)
  have hp : pairTailCode <+: codeFrom 96178 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96180 : CodeAt InlineTail.image (pcOf 96180) pairPtrCode := by
  apply Lower.prefix_codeAt_transfer 96180 _ ?_ (by decide)
  have h := codeAt_from 96180 (by decide)
  have hp : pairPtrCode <+: codeFrom 96180 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96182 : CodeAt InlineTail.image (pcOf 96182) [0x00074703] := by
  apply Lower.prefix_codeAt_transfer 96182 _ ?_ (by decide)
  have h := codeAt_from 96182 (by decide)
  have hp : [0x00074703] <+: codeFrom 96182 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96183 : CodeAt InlineTail.image (pcOf 96183) pairTailCode := by
  apply Lower.prefix_codeAt_transfer 96183 _ ?_ (by decide)
  have h := codeAt_from 96183 (by decide)
  have hp : pairTailCode <+: codeFrom 96183 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96185 : CodeAt InlineTail.image (pcOf 96185) singlePtrCode := by
  apply Lower.prefix_codeAt_transfer 96185 _ ?_ (by decide)
  have h := codeAt_from 96185 (by decide)
  have hp : singlePtrCode <+: codeFrom 96185 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96186 : CodeAt InlineTail.image (pcOf 96186) [0xe4074703] := by
  apply Lower.prefix_codeAt_transfer 96186 _ ?_ (by decide)
  have h := codeAt_from 96186 (by decide)
  have hp : [0xe4074703] <+: codeFrom 96186 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96187 : CodeAt InlineTail.image (pcOf 96187) singleTailCode := by
  apply Lower.prefix_codeAt_transfer 96187 _ ?_ (by decide)
  have h := codeAt_from 96187 (by decide)
  have hp : singleTailCode <+: codeFrom 96187 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96189 : CodeAt InlineTail.image (pcOf 96189) pairCrossCode := by
  apply Lower.prefix_codeAt_transfer 96189 _ ?_ (by decide)
  have h := codeAt_from 96189 (by decide)
  have hp : pairCrossCode <+: codeFrom 96189 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96191 : CodeAt InlineTail.image (pcOf 96191) pairPtrXCode := by
  apply Lower.prefix_codeAt_transfer 96191 _ ?_ (by decide)
  have h := codeAt_from 96191 (by decide)
  have hp : pairPtrXCode <+: codeFrom 96191 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96193 : CodeAt InlineTail.image (pcOf 96193) [0x00074703] := by
  apply Lower.prefix_codeAt_transfer 96193 _ ?_ (by decide)
  have h := codeAt_from 96193 (by decide)
  have hp : [0x00074703] <+: codeFrom 96193 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96194 : CodeAt InlineTail.image (pcOf 96194) pairTailXCode := by
  apply Lower.prefix_codeAt_transfer 96194 _ ?_ (by decide)
  have h := codeAt_from 96194 (by decide)
  have hp : pairTailXCode <+: codeFrom 96194 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96196 : CodeAt InlineTail.image (pcOf 96196) pairPtrCode := by
  apply Lower.prefix_codeAt_transfer 96196 _ ?_ (by decide)
  have h := codeAt_from 96196 (by decide)
  have hp : pairPtrCode <+: codeFrom 96196 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96198 : CodeAt InlineTail.image (pcOf 96198) [0x00074703] := by
  apply Lower.prefix_codeAt_transfer 96198 _ ?_ (by decide)
  have h := codeAt_from 96198 (by decide)
  have hp : [0x00074703] <+: codeFrom 96198 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96199 : CodeAt InlineTail.image (pcOf 96199) pairTailCode := by
  apply Lower.prefix_codeAt_transfer 96199 _ ?_ (by decide)
  have h := codeAt_from 96199 (by decide)
  have hp : pairTailCode <+: codeFrom 96199 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96201 : CodeAt InlineTail.image (pcOf 96201) pairPtrCode := by
  apply Lower.prefix_codeAt_transfer 96201 _ ?_ (by decide)
  have h := codeAt_from 96201 (by decide)
  have hp : pairPtrCode <+: codeFrom 96201 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96203 : CodeAt InlineTail.image (pcOf 96203) [0x00074703] := by
  apply Lower.prefix_codeAt_transfer 96203 _ ?_ (by decide)
  have h := codeAt_from 96203 (by decide)
  have hp : [0x00074703] <+: codeFrom 96203 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96204 : CodeAt InlineTail.image (pcOf 96204) pairTailCode := by
  apply Lower.prefix_codeAt_transfer 96204 _ ?_ (by decide)
  have h := codeAt_from 96204 (by decide)
  have hp : pairTailCode <+: codeFrom 96204 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96206 : CodeAt InlineTail.image (pcOf 96206) pairPtrCode := by
  apply Lower.prefix_codeAt_transfer 96206 _ ?_ (by decide)
  have h := codeAt_from 96206 (by decide)
  have hp : pairPtrCode <+: codeFrom 96206 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96208 : CodeAt InlineTail.image (pcOf 96208) [0x00074703] := by
  apply Lower.prefix_codeAt_transfer 96208 _ ?_ (by decide)
  have h := codeAt_from 96208 (by decide)
  have hp : [0x00074703] <+: codeFrom 96208 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96209 : CodeAt InlineTail.image (pcOf 96209) pairTailCode := by
  apply Lower.prefix_codeAt_transfer 96209 _ ?_ (by decide)
  have h := codeAt_from 96209 (by decide)
  have hp : pairTailCode <+: codeFrom 96209 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem tail_ptr_at : CodeAt InlineTail.image (pcOf 96211) ptrCode := by
  apply Lower.prefix_codeAt_transfer 96211 _ ?_ (by decide)
  have h := codeAt_from 96211 (by decide)
  have hp : ptrCode <+: codeFrom 96211 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem tail_load_at : CodeAt InlineTail.image (pcOf 96212) [0xfb874703] := by
  apply Lower.prefix_codeAt_transfer 96212 _ ?_ (by decide)
  have h := codeAt_from 96212 (by decide)
  have hp : [0xfb874703] <+: codeFrom 96212 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem tail_sum_at : CodeAt InlineTail.image (pcOf 96213) sumCode := by
  apply Lower.prefix_codeAt_transfer 96213 _ ?_ (by decide)
  have h := codeAt_from 96213 (by decide)
  have hp : sumCode <+: codeFrom 96213 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem tail_reject_at : CodeAt InlineTail.image (pcOf 96214) tailRejectJumpCode := by
  apply Lower.prefix_codeAt_transfer 96214 _ ?_ (by decide)
  have h := codeAt_from 96214 (by decide)
  have hp : tailRejectJumpCode <+: codeFrom 96214 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

theorem singleStep_spec (s : MachineState) (v : Digest) (sum : Nat)
    (hpc : s.pc = pcOf 96185) (hw : s.getReg .x29 = topWindow v 8)
    (hs : s.getReg .x25 = BitVec.ofNat 64 sum)
    (hb : s.getReg .x8 = BitVec.ofNat 64 PAIR_DATA) (ht : PackedTables s) :
    ∃ t, Steps InlineTail.image s 4 4 t ∧ t.pc = pcOf 96189 ∧
      t.getReg .x29 = v.extractLsb' 0 64 >>> 63 ∧
      t.getReg .x25 = BitVec.ofNat 64 (sum + rankLookup (topRank v 8)) ∧
      RegsExcept s t [.x25,.x29,.x14] ∧ Frame s t (fun _ => False) := by
  obtain ⟨s1,e1,p1,a1,r1,f1⟩ := singlePtr_spec s _ pf_96185 hpc v hw hb
  obtain ⟨s2,e2,p2,a2,r2,f2⟩ := raw_lbu_spec s1 _ 0xe4074703 .x14 pf_96186 p1 (by rfl) (by decide)
    _ (rawRank_lt v) (by simpa [RAW_DATA,PAIR_DATA] using a1) (ht.frame f1).raw
  obtain ⟨s3,e3,p3,w3,a3,r3,f3⟩ := singleTail_spec s2 _ pf_96187 p2 _ sum _
    (by rw [r2.get (by decide),r1.get (by decide),hw])
    (by rw [r2.get (by decide),r1.get (by decide),hs]) a2
  rw [rawRank_mod] at a3
  refine ⟨s3,(e1.trans e2).trans e3,p3,?_,a3,
    ((r1.trans r2).trans r3).mono (by decide),((f1.trans f2).trans f3).mono (by simp)⟩
  simpa [topWindow,← BitVec.shiftRight_add] using w3

theorem pairedFold_spec (s : MachineState) (v : Digest)
    (hpc : s.pc = pcOf 96164) (h16 : s.getReg .x16 = v.extractLsb' 0 64)
    (h17 : s.getReg .x17 = v.extractLsb' 64 64) (h10 : s.getReg .x10 = 15560#64) (ht : PackedTables s) :
    ∃ t, Steps InlineTail.image s 47 47 t ∧ t.pc = pcOf 96211 ∧
      t.getReg .x29 = topWindow v 17 ∧ t.getReg .x25 = BitVec.ofNat 64 (compressedSum (topRank v)) ∧
      t.getReg .x17 = v.extractLsb' 63 64 ∧
      t.getReg .x8 = BitVec.ofNat 64 PAIR_DATA ∧ t.getReg .x6 = 16383#64 ∧
      RegsExcept s t packedFoldRegs ∧ Frame s t (fun _ => False) := by
  obtain ⟨u0,e0,p0,b0,m0,r0,f0⟩ := pairInit_spec s _ pf_96164 hpc h10
  obtain ⟨u1,e1,p1,a1,r1,f1⟩ := pairPtr0_spec u0 _ pf_96166 p0 v 0 (by decide)
    (by rw [r0.get (by decide),h16]; simp [topWindow]) b0 m0
  obtain ⟨u2,e2,p2,a2,r2,f2⟩ := pair_lbu_spec u1 _ 0x00074c83 .x25 pf_96168 p1
    (by rfl) (by decide) _ (pairRank_lt v 0) a1 ((ht.frame f0).frame f1).pair
  obtain ⟨t0,e3,p3,w0,r3,f3⟩ := pairShift0_spec u2 _ pf_96169 p2 v
    (by rw [r2.get (by decide),r1.get (by decide),r0.get (by decide),h16])
  have E0 : Steps InlineTail.image s 6 6 t0 := ((e0.trans e1).trans e2).trans e3
  have R0 : RegsExcept s t0 packedFoldRegs := (((r0.trans r1).trans r2).trans r3).mono (by decide)
  have F0 : Frame s t0 (fun _ => False) := (((f0.trans f1).trans f2).trans f3).mono (by simp)
  have S0 : t0.getReg .x25 = BitVec.ofNat 64 (pairLookup (pairRank v 0)) := by rw [r3.get (by decide),a2]
  have B0 : t0.getReg .x8 = BitVec.ofNat 64 PAIR_DATA := by rw [r3.get (by decide),r2.get (by decide),r1.get (by decide),b0]
  have M0 : t0.getReg .x6 = 16383#64 := by rw [r3.get (by decide),r2.get (by decide),r1.get (by decide),m0]
  have H0 : t0.getReg .x17 = v.extractLsb' 64 64 := by rw [r3.get (by decide),r2.get (by decide),r1.get (by decide),r0.get (by decide),h17]
  obtain ⟨t1,e1p,p1p,w1,a1,r1p,f1p⟩ := pairStep_spec t0 (pcOf 96170) v 2 _
    pf_96170 pf_96172 pf_96173 p3 (by decide) w0 S0 B0 M0 (ht.frame F0)
  have E1 : Steps InlineTail.image s 11 11 t1 := E0.trans e1p
  have R1 : RegsExcept s t1 packedFoldRegs := (R0.trans r1p).mono (by decide)
  have F1 : Frame s t1 (fun _ => False) := (F0.trans f1p).mono (by simp)
  have S1 : t1.getReg .x25 = BitVec.ofNat 64 (pairLookup (pairRank v 0) + pairLookup (pairRank v 2)) := a1
  have B1 : t1.getReg .x8 = BitVec.ofNat 64 PAIR_DATA := by rw [r1p.get (by decide),B0]
  have M1 : t1.getReg .x6 = 16383#64 := by rw [r1p.get (by decide),M0]
  have H1 : t1.getReg .x17 = v.extractLsb' 64 64 := by rw [r1p.get (by decide),H0]
  obtain ⟨t2,e2p,p2p,w2,a2,r2p,f2p⟩ := pairStep_spec t1 (pcOf 96175) v 4 _
    pf_96175 pf_96177 pf_96178 p1p (by decide) w1 S1 B1 M1 (ht.frame F1)
  have E2 : Steps InlineTail.image s 16 16 t2 := E1.trans e2p
  have R2 : RegsExcept s t2 packedFoldRegs := (R1.trans r2p).mono (by decide)
  have F2 : Frame s t2 (fun _ => False) := (F1.trans f2p).mono (by simp)
  have S2 : t2.getReg .x25 = BitVec.ofNat 64 ((pairLookup (pairRank v 0) + pairLookup (pairRank v 2)) + pairLookup (pairRank v 4)) := a2
  have B2 : t2.getReg .x8 = BitVec.ofNat 64 PAIR_DATA := by rw [r2p.get (by decide),B1]
  have M2 : t2.getReg .x6 = 16383#64 := by rw [r2p.get (by decide),M1]
  have H2 : t2.getReg .x17 = v.extractLsb' 64 64 := by rw [r2p.get (by decide),H1]
  obtain ⟨t3,e3p,p3p,w3,a3,r3p,f3p⟩ := pairStep_spec t2 (pcOf 96180) v 6 _
    pf_96180 pf_96182 pf_96183 p2p (by decide) w2 S2 B2 M2 (ht.frame F2)
  have E3 : Steps InlineTail.image s 21 21 t3 := E2.trans e3p
  have R3 : RegsExcept s t3 packedFoldRegs := (R2.trans r3p).mono (by decide)
  have F3 : Frame s t3 (fun _ => False) := (F2.trans f3p).mono (by simp)
  have S3 : t3.getReg .x25 = BitVec.ofNat 64 (((pairLookup (pairRank v 0) + pairLookup (pairRank v 2)) + pairLookup (pairRank v 4)) + pairLookup (pairRank v 6)) := a3
  have B3 : t3.getReg .x8 = BitVec.ofNat 64 PAIR_DATA := by rw [r3p.get (by decide),B2]
  have M3 : t3.getReg .x6 = 16383#64 := by rw [r3p.get (by decide),M2]
  have H3 : t3.getReg .x17 = v.extractLsb' 64 64 := by rw [r3p.get (by decide),H2]
  obtain ⟨us,es,ps,ws,ass,rs,fs⟩ := singleStep_spec t3 v _ p3p w3 S3 B3 (ht.frame F3)
  obtain ⟨t4,ec,pc,wc,wwc,rc,fc⟩ := pairCross_spec us _ pf_96189 ps v ws
    (by rw [rs.get (by decide),H3])
  have E4 : Steps InlineTail.image s 27 27 t4 := (E3.trans es).trans ec
  have R4 : RegsExcept s t4 packedFoldRegs := ((R3.trans rs).trans rc).mono (by decide)
  have F4 : Frame s t4 (fun _ => False) := ((F3.trans fs).trans fc).mono (by simp)
  have S4 : t4.getReg .x25 = BitVec.ofNat 64 ((((pairLookup (pairRank v 0) + pairLookup (pairRank v 2)) + pairLookup (pairRank v 4)) + pairLookup (pairRank v 6)) + rankLookup (topRank v 8)) := by rw [rc.get (by decide),ass]
  have B4 : t4.getReg .x8 = BitVec.ofNat 64 PAIR_DATA := by rw [rc.get (by decide),rs.get (by decide),B3]
  have M4 : t4.getReg .x6 = 16383#64 := by rw [rc.get (by decide),rs.get (by decide),M3]
  have H4 : t4.getReg .x17 = v.extractLsb' 63 64 := wc
  obtain ⟨t5,e5p,p5p,w5,a5,r5p,f5p⟩ := pairStepX_spec t4 (pcOf 96191) v 9 _
    pf_96191 pf_96193 pf_96194 pc (by decide) wwc S4 B4 M4 (ht.frame F4)
  have E5 : Steps InlineTail.image s 32 32 t5 := E4.trans e5p
  have R5 : RegsExcept s t5 packedFoldRegs := (R4.trans r5p).mono (by decide)
  have F5 : Frame s t5 (fun _ => False) := (F4.trans f5p).mono (by simp)
  have S5 : t5.getReg .x25 = BitVec.ofNat 64 (((((pairLookup (pairRank v 0) + pairLookup (pairRank v 2)) + pairLookup (pairRank v 4)) + pairLookup (pairRank v 6)) + rankLookup (topRank v 8)) + pairLookup (pairRank v 9)) := a5
  have B5 : t5.getReg .x8 = BitVec.ofNat 64 PAIR_DATA := by rw [r5p.get (by decide),B4]
  have M5 : t5.getReg .x6 = 16383#64 := by rw [r5p.get (by decide),M4]
  have H5 : t5.getReg .x17 = v.extractLsb' 63 64 := by rw [r5p.get (by decide),H4]
  obtain ⟨t6,e6p,p6p,w6,a6,r6p,f6p⟩ := pairStep_spec t5 (pcOf 96196) v 11 _
    pf_96196 pf_96198 pf_96199 p5p (by decide) w5 S5 B5 M5 (ht.frame F5)
  have E6 : Steps InlineTail.image s 37 37 t6 := E5.trans e6p
  have R6 : RegsExcept s t6 packedFoldRegs := (R5.trans r6p).mono (by decide)
  have F6 : Frame s t6 (fun _ => False) := (F5.trans f6p).mono (by simp)
  have S6 : t6.getReg .x25 = BitVec.ofNat 64 ((((((pairLookup (pairRank v 0) + pairLookup (pairRank v 2)) + pairLookup (pairRank v 4)) + pairLookup (pairRank v 6)) + rankLookup (topRank v 8)) + pairLookup (pairRank v 9)) + pairLookup (pairRank v 11)) := a6
  have B6 : t6.getReg .x8 = BitVec.ofNat 64 PAIR_DATA := by rw [r6p.get (by decide),B5]
  have M6 : t6.getReg .x6 = 16383#64 := by rw [r6p.get (by decide),M5]
  have H6 : t6.getReg .x17 = v.extractLsb' 63 64 := by rw [r6p.get (by decide),H5]
  obtain ⟨t7,e7p,p7p,w7,a7,r7p,f7p⟩ := pairStep_spec t6 (pcOf 96201) v 13 _
    pf_96201 pf_96203 pf_96204 p6p (by decide) w6 S6 B6 M6 (ht.frame F6)
  have E7 : Steps InlineTail.image s 42 42 t7 := E6.trans e7p
  have R7 : RegsExcept s t7 packedFoldRegs := (R6.trans r7p).mono (by decide)
  have F7 : Frame s t7 (fun _ => False) := (F6.trans f7p).mono (by simp)
  have S7 : t7.getReg .x25 = BitVec.ofNat 64 (((((((pairLookup (pairRank v 0) + pairLookup (pairRank v 2)) + pairLookup (pairRank v 4)) + pairLookup (pairRank v 6)) + rankLookup (topRank v 8)) + pairLookup (pairRank v 9)) + pairLookup (pairRank v 11)) + pairLookup (pairRank v 13)) := a7
  have B7 : t7.getReg .x8 = BitVec.ofNat 64 PAIR_DATA := by rw [r7p.get (by decide),B6]
  have M7 : t7.getReg .x6 = 16383#64 := by rw [r7p.get (by decide),M6]
  have H7 : t7.getReg .x17 = v.extractLsb' 63 64 := by rw [r7p.get (by decide),H6]
  obtain ⟨t8,e8p,p8p,w8,a8,r8p,f8p⟩ := pairStep_spec t7 (pcOf 96206) v 15 _
    pf_96206 pf_96208 pf_96209 p7p (by decide) w7 S7 B7 M7 (ht.frame F7)
  have E8 : Steps InlineTail.image s 47 47 t8 := E7.trans e8p
  have R8 : RegsExcept s t8 packedFoldRegs := (R7.trans r8p).mono (by decide)
  have F8 : Frame s t8 (fun _ => False) := (F7.trans f8p).mono (by simp)
  have S8 : t8.getReg .x25 = BitVec.ofNat 64 ((((((((pairLookup (pairRank v 0) + pairLookup (pairRank v 2)) + pairLookup (pairRank v 4)) + pairLookup (pairRank v 6)) + rankLookup (topRank v 8)) + pairLookup (pairRank v 9)) + pairLookup (pairRank v 11)) + pairLookup (pairRank v 13)) + pairLookup (pairRank v 15)) := a8
  have B8 : t8.getReg .x8 = BitVec.ofNat 64 PAIR_DATA := by rw [r8p.get (by decide),B7]
  have M8 : t8.getReg .x6 = 16383#64 := by rw [r8p.get (by decide),M7]
  have H8 : t8.getReg .x17 = v.extractLsb' 63 64 := by rw [r8p.get (by decide),H7]
  refine ⟨t8,E8,p8p,w8,?_,H8,B8,M8,R8,F8⟩
  simpa only [pairLookup_pairRank,Nat.reduceAdd,compressedSum] using S8

theorem tail_spec (s : MachineState) (v : Digest) (sum : Nat) (hsum : sum ≤ 4335)
    (hv : v.toNat < 2 ^ 125) (hpc : s.pc = pcOf 96211)
    (h29 : s.getReg .x29 = topWindow v 17) (h25 : s.getReg .x25 = BitVec.ofNat 64 sum)
    (h19 : s.getReg .x8 = BitVec.ofNat 64 PAIR_DATA)
    (ht : PackedTables s) :
    ∃ t, Steps InlineTail.image s (if sum + tailWeight v = 128 then 3 else 4)
      (if sum + tailWeight v = 128 then 3 else 4) t ∧
      t.pc = (if sum + tailWeight v = 128 then pcOf 96218 else pcOf 96230) ∧
      t.getReg .x8 = BitVec.ofNat 64 PAIR_DATA ∧
      RegsExcept s t [.x14,.x8] ∧ Frame s t (fun _ => False) := by
  obtain ⟨s2,e2,p2,r2,f2⟩ := tail_compare_spec s v sum tail_ptr_at tail_load_at tail_sum_at tail_reject_at hsum hv hpc
    h29 h25 h19 ht
  exact ⟨s2,e2,p2,by rw [r2.get (by decide)]; exact h19,r2.mono (by decide),f2⟩

theorem decode_ok (s : MachineState) (v : Digest)
    (hpc : s.pc = pcOf 96160) (d : Nat) (h12 : s.getReg .x12=BitVec.ofNat 64 d)
    (hd : d=15560 ∨ d=15608) (hv : DigAt s d v) (ht : PackedTables s)
    (h10 : s.getReg .x10 = 15560#64)
    (hvalid : T3.decode 0 v = some (topDigits v)) :
    ∃ t, Steps InlineTail.image s 54 54 t ∧ t.pc = pcOf 96218 ∧
      t.getReg .x16 = v.extractLsb' 0 64 ∧ t.getReg .x17 = v.extractLsb' 63 64 ∧
      t.getReg .x29 = topWindow v 17 ∧ t.getReg .x6 = 16383#64 ∧
      t.getReg .x8 = BitVec.ofNat 64 PAIR_DATA ∧
      RegsExcept s t [.x16,.x17,.x14,.x25,.x29,.x8,.x6] ∧ Frame s t (fun _ => False) := by
  have hh : v.toNat < 2 ^ 125 ∧ pairedLookupSum v = 128 := by
    rw [decode_top_paired] at hvalid
    split_ifs at hvalid with hh
    exact hh
  obtain ⟨t1,e1,p1,a1,b1,r1,f1⟩ := head_spec s v d hpc h12 hd hv
  rw [if_pos hh.1] at p1
  obtain ⟨t2,e2,p2,w2,a2,h172,b192,b242,r2,f2⟩ := pairedFold_spec t1 v p1 a1 b1
    (by rw [r1.get (by decide)]; exact h10) (ht.frame f1)
  have hb : compressedSum (topRank v) + tailWeight v = 128 := hh.2
  obtain ⟨t3,e3,p3,b3,r3,f3⟩ := tail_spec t2 v _ (compressedSum_le v) hh.1 p2 w2 a2 b192 ((ht.frame f1).frame f2)
  rw [if_pos hb] at p3 e3
  refine ⟨t3,(e1.trans e2).trans e3,p3,?_,?_,?_,?_,b3,
    ((r1.trans r2).trans r3).mono (by decide),((f1.trans f2).trans f3).mono (by simp)⟩
  · rw [r3.get (by decide),r2.get (by decide),a1]
  · rw [r3.get (by decide),h172]
  · rw [r3.get (by decide),w2]
  · rw [r3.get (by decide),b242]

theorem decode_reject (s : MachineState) (v : Digest)
    (hpc : s.pc = pcOf 96160) (d : Nat) (h12 : s.getReg .x12=BitVec.ofNat 64 d)
    (hd : d=15560 ∨ d=15608) (hv : DigAt s d v) (ht : PackedTables s)
    (h10 : s.getReg .x10 = 15560#64)
    (hbad : T3.decode 0 v = none) :
    ∃ k t, Steps InlineTail.image s k k t ∧ k ≤ 60 ∧ t.pc = pcOf 96230 ∧
      RegsExcept s t [.x16,.x17,.x14,.x25,.x29,.x8,.x6] ∧ Frame s t (fun _ => False) := by
  obtain ⟨t1, e1, p1, a1, b1, r1, f1⟩ := head_spec s v d hpc h12 hd hv
  by_cases hr : v.toNat < 2 ^ 125
  · rw [if_pos hr] at p1
    obtain ⟨t2,e2,p2,w2,a2,h172,b192,b242,r2,f2⟩ := pairedFold_spec t1 v p1 a1 b1
      (by rw [r1.get (by decide)]; exact h10) (ht.frame f1)
    have hn : pairedLookupSum v ≠ 128 := by
      intro he
      rw [decode_top_paired,if_pos ⟨hr,he⟩] at hbad
      contradiction
    have hb : compressedSum (topRank v) + tailWeight v ≠ 128 := hn
    obtain ⟨t3,e3,p3,-,r3,f3⟩ := tail_spec t2 v _ (compressedSum_le v) hr p2 w2 a2 b192 ((ht.frame f1).frame f2)
    rw [if_neg hb] at p3 e3
    exact ⟨55,t3,(e1.trans e2).trans e3,by decide,p3,
      ((r1.trans r2).trans r3).mono (by decide),((f1.trans f2).trans f3).mono (by simp)⟩
  · rw [if_neg hr] at p1
    exact ⟨4, t1, e1, by decide, p1, r1.mono (by decide), f1⟩

theorem reject_halt (s : MachineState) (hpc : s.pc = pcOf 96230) :
    ∃ t, Steps InlineTail.image s 3 3 t ∧ fetch InlineTail.image t = some (.base .ECALL) ∧
      t.getReg .x5 = 1 ∧ t.getReg .x10 = 1 := by
  have e1 := symRun_sound rejectJumpBase (Lower.prefix_codeAt_transfer 96230 rejectJumpCode rejectJump_at (by decide)) s hpc (by simp [rejectJumpBase.res, rv_simp])
  have p1 : (rejectJumpBase.res.toState s).pc = pcOf 741 := by simp [rejectJumpBase.res, rv_simp, pcOf]
  have e2 := symRun_sound rejectExitBase (Lower.prefix_codeAt_transfer 741 rejectExitCode rejectExit_at (by decide)) (rejectJumpBase.res.toState s) p1
    (by simp [rejectExitBase.res, rv_simp])
  refine ⟨_, e1.trans e2, ?_, ?_, ?_⟩
  · have h : CodeAt InlineTail.image (pcOf 743) [0x00000073] := by
      apply Lower.prefix_codeAt_transfer 743 _ ?_ (by decide)
      have h := codeAt_from 743 (by decide)
      have hp : [0x00000073] <+: codeFrom 743 := by decide +kernel
      exact ⟨by decide, by decide, by decide +kernel, hp.trans h.2.2.2⟩
    exact h.fetch _ (by simp [rejectExitBase.res, rv_simp, pcOf])
  · simp [rejectExitBase.res, rv_simp]
  · simp [rejectExitBase.res, rv_simp]

theorem prologue_spec (s : MachineState) (v : Digest)
    (hpc : s.pc = pcOf 96218)
    (h16 : s.getReg .x16 = v.extractLsb' 0 64) (h17 : s.getReg .x17 = v.extractLsb' 63 64)
    (h19 : s.getReg .x8 = BitVec.ofNat 64 PAIR_DATA)
    (hmask : s.getMem (BitVec.ofNat 64 (TAIL_DATA + 64)) = 130048#64) (h10 : s.getReg .x10 = 15560#64)
    (hmem : s.getMem (BitVec.ofNat 64 0xffbf90) = BitVec.ofNat 64 (128 + 193 * 2 ^ 56)) :
    ∃ t, Steps InlineTail.image s 10 10 t ∧ t.pc = prologueTarget v ∧
      t.getReg .x16 = v.extractLsb' 0 64 ∧
      t.getReg .x17 = v.extractLsb' 63 64 ∧
      t.getReg .x8 = 13768#64 ∧ t.getReg .x6 = 130048#64 ∧
      t.getReg .x15 = 712704#64 ∧
      t.getReg .x28 = topPrefixWord (s.getReg .x4) ∧
      RegsExcept s t [.x3,.x17,.x8,.x6,.x15,.x14,.x28] ∧ Frame s t (fun _ => False) := by
  have h19' : s.getReg .x8 = 0xffc000#64 := h19
  have hm : s.getMem 0xffbff8#64 = 130048#64 := hmask
  refine ⟨_, symRun_sound prologueBase (Lower.prefix_codeAt_transfer 96218 prologueCode prologue_at (by decide)) s hpc
    (by simp [prologueBase.res, rv_simp, accessValid_iff, MEMORY_BYTES, h19']),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hx24 : (prologueBase.res.toState s).getReg .x6 = 130048#64 := by
      simp [prologueBase.res, rv_simp, h19', hm]
    simp only [Result.toState_getReg, prologueBase.res, rv_simp] at hx24
    simp only [Result.toState_pc, prologueBase.res, rv_simp, h16, hx24, prologueTarget, pcOf]
    rfl
  · simpa [prologueBase.res, rv_simp] using h16
  · simp [prologueBase.res, rv_simp, h16, h17]
  · simp [prologueBase.res, rv_simp, h10]
  · simp [prologueBase.res, rv_simp, h19', hm]
  · simp [prologueBase.res, rv_simp, pcOf]
  · simp [prologueBase.res, rv_simp, topPrefixWord, h19', hmem]
  · intro r hr; cases r <;> simp at hr <;> simp [prologueBase.res, rv_simp] <;> rfl
  · intro A _ _; simp [prologueBase.res, rv_simp]

theorem top_call_run_equal (c : Nat) (hc : c < nCopy 0) :
    Verify.runAt [] [96160] (trPc 0 c + 10) [] = Lower.runAt [] [96160] (trPc 0 c + 10) [] := by
  norm_num [nCopy, xtrTab] at hc
  interval_cases c <;> rfl

theorem topCall_jumps (c : Nat) (hc : c < nCopy 0) (u : MachineState)
    (hpc : u.pc = pcOf (trPc 0 c + 10)) (hk : KnownOK (BC.bK 0) u) :
    ∃ s, Steps InlineTail.image u 1 1 s ∧ s.pc = pcOf 96160 ∧ s.getReg .x1 = pcOf (trPc 0 c + 11) ∧
      RegsExcept u s [.x1] ∧ Frame u s (fun _ => False) := by
  have hcc := (copy_parts 0 (trPc 0 c) (BC.copyCheck_at 0 c (by decide) hc)).2.2.1 rfl
  obtain ⟨s, hs⟩ := Lower.dual_spec_run (by rw [← top_call_run_equal c hc]; exact hcc)
    (top_call_run_equal c hc) u hpc (by simp [KnownOK]) (by simp [specTopCall]) (by simp)
  refine ⟨s, hs.steps, hs.pc rfl, ?_, ?_, ?_⟩
  · exact hs.regs (.x1, kw (0x1000 + 4 * (trPc 0 c + 11))) (by simp [specTopCall])
  · intro r hr
    cases r
    case x0 => simp [MachineState.getReg]
    case x1 => simp at hr
    all_goals exact hs.keep _ (by simp [keepTopCall])
  · intro A hA _
    rw [hs.mem]
    rfl

theorem topTransition_reject (w : WBytes) (pk : Digest) (index c : Nat) (hc : c < nCopy 0)
    (t : MachineState) (ht : EncPre w pk index 0 c t) (a : BitVec 256)
    (hbad : T3.decode 0 (a.extractLsb' 0 128) = none) :
    ∃ k s, Steps InlineTail.image (writeHash t a) k k s ∧ k ≤ 70 ∧
      fetch InlineTail.image s = some (.base .ECALL) ∧ s.getReg .x5 = 1 ∧ s.getReg .x10 = 1 := by
  obtain ⟨d, h12, hd⟩ := ht.dst0 rfl
  have hk : KnownOK (BC.bK 0) (writeHash t a) := fun p hp => by rw [writeHash_getReg]; exact ht.glob.1 p hp
  have hpc : (writeHash t a).pc = pcOf (trPc 0 c + 10) := by
    rw [writeHash_pc, ht.pc]
    change pcOf (trPc 0 c + 9) + 4 = pcOf (trPc 0 c + 10)
    simpa only [Nat.add_assoc] using pcOf_add4 (trPc 0 c + 9)
  have hglob := Glob_writeHash ht.glob a d h12 (by rcases hd with rfl | rfl <;> decide)
  obtain ⟨s, e, ps, ra, rs, fs⟩ := topCall_jumps c hc _ hpc hk
  have hv := (DigAt.writeHash_lo t a d h12 (by omega)).frame fs (by omega) (by simp) (by simp)
  have h12s : s.getReg .x12 = BitVec.ofNat 64 d := by
    rw [rs.get (by decide), writeHash_getReg]; exact h12
  have hdT := hglob.2.2.2.2.2.packed.frame fs
  have h10 : s.getReg .x10 = 15560#64 := by
    rw [rs.get (by decide)]
    exact hk (.x10, BitVec.ofNat 64 (x10In 0)) (by simp [BC.bK])
  obtain ⟨k, r, er, hk, pr, rr, fr⟩ := decode_reject s _ ps d h12s hd hv hdT h10 hbad
  obtain ⟨z, ez, hz, h5, h10⟩ := reject_halt r pr
  refine ⟨1 + k + 3, z, (e.trans er).trans ez, by omega, hz, h5, h10⟩

theorem topTransition_ok (w : WBytes) (pk : Digest) (index c : Nat) (hc : c < nCopy 0)
    (t : MachineState) (ht : EncPre w pk index 0 c t) (a : BitVec 256)
    (hgood : T3.decode 0 (a.extractLsb' 0 128) = some (Search.topDigits (a.extractLsb' 0 128))) :
    ∃ s, Steps InlineTail.image (writeHash t a) 65 65 s ∧
      TopEntry (writeHash t a) (a.extractLsb' 0 128) (trPc 0 c) s := by
  obtain ⟨d, h12, hd⟩ := ht.dst0 rfl
  have hk : KnownOK (BC.bK 0) (writeHash t a) := fun p hp => by rw [writeHash_getReg]; exact ht.glob.1 p hp
  have hpc : (writeHash t a).pc = pcOf (trPc 0 c + 10) := by
    rw [writeHash_pc, ht.pc]
    change pcOf (trPc 0 c + 9) + 4 = pcOf (trPc 0 c + 10)
    simpa only [Nat.add_assoc] using pcOf_add4 (trPc 0 c + 9)
  have hglob := Glob_writeHash ht.glob a d h12 (by rcases hd with rfl | rfl <;> decide)
  obtain ⟨s, e, ps, ra, rs, fs⟩ := topCall_jumps c hc _ hpc hk
  have hv := (DigAt.writeHash_lo t a d h12 (by omega)).frame fs (by omega) (by simp) (by simp)
  have h12s : s.getReg .x12 = BitVec.ofNat 64 d := by
    rw [rs.get (by decide), writeHash_getReg]; exact h12
  have hdT := hglob.2.2.2.2.2.packed.frame fs
  have h10 : s.getReg .x10 = 15560#64 := by
    rw [rs.get (by decide)]
    exact hk (.x10, BitVec.ofNat 64 (x10In 0)) (by simp [BC.bK])
  obtain ⟨r, er, pr, h16, h17, h29, -, h19, rr, fr⟩ := decode_ok s _ ps d h12s hd hv hdT h10 hgood
  have hmem0 : (writeHash t a).getMem (BitVec.ofNat 64 0xffbf90) = BitVec.ofNat 64 (128 + 193 * 2 ^ 56) :=
    hglob.2.2.2.2.2.prefix 0 (by decide)
  have hmem : r.getMem (BitVec.ofNat 64 0xffbf90) = BitVec.ofNat 64 (128 + 193 * 2 ^ 56) := by
    rw [fr.get (by decide) (by simp), fs.get (by decide) (by simp), hmem0]
  obtain ⟨z, ez, pz, lo, hi, s3, mask, tab, px, rz, fz⟩ := prologue_spec r _ pr h16 h17 h19
    (hdT.frame fr).mask (by rw [rr.get (by decide)]; exact h10) hmem
  refine ⟨z, (e.trans er).trans ez, ⟨?_, ?_, lo, ?_, ?_, s3, mask, tab, ?_, ?_, ?_⟩⟩
  · rw [pz]
    exact Nonbinary.prologue_target _
  · rw [rz.get (by decide), rr.get (by decide), ra]
  · rw [hi]; exact (Search.topWindow_cross _).symm
  · rw [rz.get (by decide), h29]
  · rw [px, rr.get (by decide), rs.get (by decide)]
  · exact ((rs.trans rr).trans rz).mono (by decide)
  · exact ((fs.trans fr).trans fz).mono (by simp)

-- Reuse the actual new-image Merkle steps and their invariant. Only the
-- judgment binder is weakened to the pinned HashOk-conditional contract;
-- no old-image execution or desired root is supplied as a premise.
namespace NativeMerkle
open InlineTail.Merkle
theorem merkle_rest (w : WBytes) (pk : Digest) (index : Nat) (lay : Layer) (u : MachineState) (hidx : index < 2 ^ 31)
    (hs7 : u.getReg .x23 = BitVec.ofNat 64 (dispatchHeap lay.val (route index lay).1))
    (ht5 : lay.val ≠ 0 → u.getReg .x31 = BitVec.ofNat 64 (route index lay).2)
    (K : Digest → OracleComp HashSpec Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ root t, MkStop w pk lay.val (route index lay).1 u root t → W9Machine.GoodQFor InlineTail.image t N C Q A (K root)) :
    ∀ n k v s, k + n = mkStop lay.val → k < hL lay.val → MAfter w pk lay.val (route index lay).1 u k v s →
      W9Machine.GoodQFor InlineTail.image s (N + mkFuelR lay.val k n) (C + mkCycR lay.val k n) Q (A + mkCycR lay.val k n)
        (Verify.ccM ((List.range' k n).foldlM (mkStep w index lay) v) K) := by
  intro n
  induction n with
  | zero =>
    intro k v s hkn hk hs
    have h0 : lay.val ≠ 0 := by intro h; simp [mkStop, h] at hkn; rw [h] at hk; omega
    simp only [List.range'_zero, List.foldlM_nil, Verify.ccM_pure, mkFuelR, mkCycR, Nat.add_zero]
    apply hK v s
    simpa [MkStop, h0, ← hkn] using hs
  | succ m ih =>
    intro k v s hkn hk hs
    have hlive : k < hL lay.val - (if lay.val = 0 then 0 else 1) := by change k < mkStop lay.val; omega
    obtain ⟨t, hst, hf, h5, hv, hin, hpost⟩ := lvl_step w pk index lay u hidx hs7 ht5 k hk hlive v s hs
    rw [List.range'_succ, List.foldlM_cons, mkStep_eq]
    have H : ∀ a : BitVec 256, W9Machine.GoodQFor InlineTail.image (writeHash t a) (N + mkFuelR lay.val (k + 1) m) (C + mkCycR lay.val (k + 1) m) Q
        (A + mkCycR lay.val (k + 1) m)
        (Verify.ccM ((fun v' => (List.range' (k + 1) m).foldlM (mkStep w index lay) v') (a.extractLsb' 0 128)) K) := by
      intro a
      by_cases he : k + 1 = hL lay.val
      · have hm : m = 0 := by unfold mkStop at hkn; split_ifs at hkn <;> omega
        subst m
        have h0 : lay.val = 0 := by unfold mkStop at hkn; split_ifs at hkn <;> omega
        simp only [List.range'_zero, List.foldlM_nil, Verify.ccM_pure, mkFuelR, mkCycR, Nat.add_zero]
        apply hK
        simpa [MkStop, h0] using (hpost a).2 he
      · exact ih (k + 1) _ _ (by omega) (by omega) ((hpost a).1 (by omega))
    have hg := W9Machine.GoodQFor.shortHash_bind (f := fun v' => (List.range' (k + 1) m).foldlM (mkStep w index lay) v') hf h5 hv hin H
    rw [mkIn_blocks] at hg
    simp only [mkFuelR, mkCycR]
    exact W9Machine.GoodQFor.steps' hst hg (by omega) (by omega) (fun q => ⟨q, by omega⟩)

theorem merkle_good (w : WBytes) (pk : Digest) (index : Nat) (lay : Layer) (ends : List Digest) (u : MachineState)
    (hidx : index < 2 ^ 31) (hu : LeafOut w pk index lay ends u)
    (K : Digest → OracleComp HashSpec Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ root t, MkStop w pk lay.val (route index lay).1 u root t → W9Machine.GoodQFor InlineTail.image t N C Q A (K root)) :
    W9Machine.GoodQFor InlineTail.image u (N + mkFuel lay.val) (C + mkCyc lay.val) Q (A + mkCyc lay.val)
      (Verify.ccM (leafHash lay (route index lay).2 (route index lay).1 ends >>= merklePrefix w index lay) K) := by
  have hlay := lay.isLt
  have hleaf : (route index lay).1 < 2 ^ hL lay.val := leaf_lt index lay
  have hkU : KnownOK (lfK lay.val) u := hu.glob.1
  have hknown : KnownOK (mkKc lay.val) u := fun p hp => hkU p (lfK_mkK _ p (mkKc_mkK _ p hp))
  have hhL : 0 < hL lay.val := by interval_cases lay.val <;> decide
  have hent := BC.mkEnt_of (BC.mkBlockCheck_at lay.val 0 (mkSh lay.val 0 (route index lay).1) hlay
    (by unfold mkNch; split <;> omega) (mkSh_lt _ _ _))
  have hpc : u.pc = pcOf (mkTabW lay.val 0 (mkSh lay.val 0 (route index lay).1)) := by
    rw [hu.pc]
    have e2 : mkSh lay.val 0 (route index lay).1 = (route index lay).1 % 2 ^ stabBits lay.val := by
      simp only [mkSh, show mkLo lay.val 0 = 0 by simp [mkLo], Nat.pow_zero, Nat.div_one, mkBits_stabBits _ hlay]
    rw [e2]; simp [mkTabW]
  have hEntKnown : KnownOK (mkEntK lay.val 0) u := by
    simpa [mkEntK] using hknown
  obtain ⟨t, ht⟩ := mkSpec_run hent u hpc hEntKnown (by simp [BC.mkEntSpec]) (by simp)
  have hmem : ∀ A, t.getMem A = u.getMem A := fun A => by rw [ht.mem]; rfl
  have h10u : u.getReg .x10 = BitVec.ofNat 64 (lfBase lay.val) :=
    hkU (.x10, BitVec.ofNat 64 (if lay.val = 0 then 512 else 768)) (by simp [lfK, postLf])
  have h11u : u.getReg .x11 = BitVec.ofNat 64 (lfBytes lay.val) :=
    hkU (.x11, BitVec.ofNat 64 (if lay.val = 0 then 896 else 704)) (by simp [lfK, postLf])
  have h10 : t.getReg .x10 = u.getReg .x10 := ht.keep .x10 (by simp [mkEntKeep])
  have h11 : t.getReg .x11 = u.getReg .x11 := ht.keep .x11 (by simp [mkEntKeep])
  have hkt : KnownOK (mkEntPost lay.val 0 (mkSh lay.val 0 (route index lay).1)) t := ht.known
  have hb0 : mkSh lay.val 0 (route index lay).1 % 2 = (route index lay).1 / 2 ^ 0 % 2 := by
    have := mkSh_bit lay.val 0 (route index lay).1 0 (by unfold mkBits; split <;> [decide; (interval_cases lay.val <;> decide)])
    simpa [mkLo] using this
  have h12 : t.getReg .x12 = BitVec.ofNat 64 (mkCur lay.val 0 ((route index lay).1 / 2 ^ 0 % 2)) := by
    rw [hkt (.x12, BitVec.ofNat 64 (mkCur lay.val (mkLo lay.val 0) (mkSh lay.val 0 (route index lay).1 % 2)))
      (by simp [mkEntPost]), hb0, show mkLo lay.val 0 = 0 by simp [mkLo]]
  obtain ⟨hB8, hBlo, hBhi, hBase, -, -, hBtop⟩ := mkBo_facts lay.val 0 hlay hhL
  have hb := mkBit_lt (route index lay).1 0
  have hd : mkCur lay.val 0 ((route index lay).1 / 2 ^ 0 % 2) + 32 < 2 ^ 64 := by unfold mkCur mkBlk; omega
  have hin : hashInput t = toQ (pad64 (leafInput lay (route index lay).2 (route index lay).1 ends)) := by
    rw [mkHashInput_congr h10 h11 hmem]; exact hu.hashInput.1
  have hv : hashArgumentsValid t = true := by
    refine hashArgs_of t (lfBase lay.val) (lfBytes lay.val) _ (h10.trans h10u) (h11.trans h11u) h12
      (by unfold lfBase; split <;> decide) (by unfold lfBytes; split <;> decide) (by unfold lfBase lfBytes; split <;> decide)
      (by unfold mkCur mkBlk; omega) (by unfold mkCur mkBlk; omega)
  have hG : Glob baseK w pk t := ht.glob _ _ _ hu.glob (RelOK.nil u)
  have H : ∀ a : BitVec 256, W9Machine.GoodQFor InlineTail.image (writeHash t a) (N + mkFuelR lay.val 0 (mkStop lay.val))
      (C + mkCycR lay.val 0 (mkStop lay.val)) Q (A + mkCycR lay.val 0 (mkStop lay.val))
      (Verify.ccM (merklePrefix w index lay (a.extractLsb' 0 128)) K) := by
    intro a
    have hA : MAfter w pk lay.val (route index lay).1 u 0 (a.extractLsb' 0 128) (writeHash t a) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun h => absurd rfl h⟩
      · rw [writeHash_pc, ht.pc rfl, pcOf_add4]
        simp only [BC.mkEntSpec, mkEc, show mkCi lay.val 0 = 0 by simp [mkCi], show mkLo lay.val 0 = 0 by simp [mkLo]]
        rfl
      · exact Glob_writeHash hG a _ h12 (safeDest_hi _ (by unfold mkCur mkBlk WLO WIT; omega)
          (by unfold mkCur mkBlk; omega) (by unfold mkCur mkBlk; omega))
      · intro p hp
        rw [writeHash_getReg]
        have hp' : p ∈ mkK lay.val := by simpa [mkLvlK] using hp
        rcases mkK_cases _ p hp' with hp'' | hp''
        · exact hkt p (List.mem_append_left _ hp'')
        ·
          rw [ht.keep p.1 (by rw [hp'']; simp [mkEntKeep])]
          exact hkU p (lfK_mkK _ p hp')
      · intro r hr; rw [writeHash_getReg]; exact ht.keep r (mkKeep_sub _ r hr)
      · exact DigAt.writeHash_lo t a _ h12 hd
      · have hO : Orig w (fun o => 9288 ≤ o ∧ o < layerBase lay + 64 * height lay) t :=
          hu.orig.frame (fun j _ _ => hmem _)
        have hw2 := Orig_writeHash hO a _ h12 hd
        exact hw2.mono (fun o ⟨h1, h2, h3⟩ => ⟨⟨h1, by rw [layerBase_add]; omega⟩, by unfold WIT; omega⟩)
      · rw [writeHash_getReg]; exact h12
    rw [merklePrefix, List.range_eq_range']
    exact merkle_rest w pk index lay u hidx hu.s7 hu.t5 K N C A Q hK (mkStop lay.val) 0 _ _ (by omega) hhL hA
  have h5 : t.getReg .x5 = 0 := hkt (.x5, 0) (by simp [mkEntPost, mkKc, baseK])
  have hg := W9Machine.GoodQFor.shortHash_bind (f := merklePrefix w index lay) (K := K) (ht.ecall rfl) h5 hv hin H
  rw [hu.hashInput.2] at hg
  rw [leafHash_eq]
  have hst := ht.steps
  simp only [BC.mkEntSpec] at hst
  exact W9Machine.GoodQFor.steps' hst hg (by unfold mkFuel; omega) (by unfold mkCyc; omega) (fun q => ⟨q, by unfold mkCyc; omega⟩)

-- The new Merkle invariant has the same concrete fields on lower layers.
-- Construct the original PURE boundary invariant explicitly; this does
-- not transport an execution judgment or any HASH answer.
theorem next_lower (w : WBytes) (pk : Digest) (index : Nat) (hidx : index < 2 ^ 31)
    (lay : Layer) (h0 : lay.val ≠ 0) (ends : List Digest) (u : MachineState)
    (hu : LeafOut w pk index lay ends u) (v : Digest) (t : MachineState)
    (ht : InlineTail.Merkle.MkStop w pk lay.val (route index lay).1 u v t) :
    LayerIn w pk index (lay.val - 1) (mkMessage w index lay v) t := by
  have ha : InlineTail.Merkle.MAfter w pk lay.val (route index lay).1 u
      (InlineTail.Merkle.mkStop lay.val) v t := by
    simpa [InlineTail.Merkle.MkStop, h0] using ht
  have old : SigGolfCandidate.T3M.MAfter w pk lay.val (route index lay).1 u
      (SigGolfCandidate.T3M.mkStop lay.val) v t :=
    ⟨ha.pc, ha.glob, ha.known, ha.keep, ha.node, ha.orig, ha.dstReg, ha.x4⟩
  apply SigGolfCandidate.T3M.mkStop_next_lower w pk index hidx lay h0 ends u hu v t
  simpa [SigGolfCandidate.T3M.MkStop, h0] using old
end NativeMerkle

-- Pure identification of the actual decoded top source and the new
-- literal54/Merkle/compare program. Neither side resamples the encoding.
def topRest (w : WBytes) (index : Nat) (v : Digest) : T3.M (Option Digest) :=
  match decode 0 v with
  | none => pure none
  | some ds => chainsP w 0 (route index 0).2 (route index 0).1 ds >>= fun ends =>
      leafHash 0 (route index 0).2 (route index 0).1 ends >>= fun root =>
      merkleMsg w index 0 root >>= BC.layerLoop w index 0

theorem topRest_source (w : WBytes) (pk : Digest) (index c : Nat) (v : Digest)
    (ds : List Nat) (hd : decode 0 v = some ds) :
    ccM (topRest w index v) (kFin pk) =
      Judg.ccM (topBoolSource (nctxOf w index v (trPc 0 c)) index pk) Judg.Kb := by
  have hd' := (decode_top_sum v ds hd).1
  have he := nctx_topP_eq w index v (trPc 0 c)
  change all54Source (nctxOf w index v (trPc 0 c)) =
    chainsP w 0 (route index 0).2 (route index 0).1 (dataDigits 0 v) at he
  have hm (root : Digest) : merkleP w index 0 root =
      InlineTail.Merkle.merklePrefix w index 0 root := by
    rw [merkleP_eq]
    rfl
  simp only [topRest, hd, topBoolSource, topSource, he, hd', ccM_bind,
    Judg.ccM_bind, Judg.ccM_map, merkleMsg_top, hm, ccM_pure, BC.layerLoop, kFin_some,
    Judg.ccM_pure, Judg.Kb]
  rfl

theorem topCost_credit (w : WBytes) (index c : Nat) (v : Digest) (ds : List Nat)
    (hd : decode 0 v = some ds) :
    all54Cost (nctxOf w index v (trPc 0 c)) + T3.topCredit v = 1065 := by
  let L := nctxOf w index v (trPc 0 c)
  have hfit : L.Fit v := fun i hi => rfl
  have hs := all54_cost_saved_one L (L.fit_digits hfit)
  have he : L.chainsCost 0 54 = NCtx.totalCost (T3.coreDigit 0 v) := by
    unfold NCtx.chainsCost NCtx.totalCost
    rw [← List.range_eq_range']
    congr 1
    apply List.map_congr_left
    intro i hi
    rw [hfit i (List.mem_range.mp hi)]
  have hb := NCtx.source_accepted_total_credit hd
  rw [he] at hs
  omega

def topAnswerBudget (w : WBytes) (index c : Nat) (a : BitVec 256) : Nat :=
  match decode 0 (a.extractLsb' 0 128) with
  | none => 70
  | some _ => 65 + 8 + all54Cost (nctxOf w index (a.extractLsb' 0 128) (trPc 0 c)) +
      12 + InlineTail.Merkle.mkCyc 0

-- Bind the exact answer of the one encoding query to Byte's physical
-- top stage. The credit value remains a pure property of that SAME answer.
theorem top_answer_good (w : WBytes) (pk : Digest) (index c : Nat) (hc : c < nCopy 0)
    (t : MachineState) (hpre : EncPre w pk index 0 c t) (hidx : index < 2^31)
    (a : BitVec 256) (Q : Prop) (hQ : Q) :
    W9Machine.GoodQFor InlineTail.image (writeHash t a)
      (lFuel 1 - 10) (lCyc 1 - 17) Q (topAnswerBudget w index c a)
      (ccM (topRest w index (a.extractLsb' 0 128)) (kFin pk)) := by
  cases hd : decode 0 (a.extractLsb' 0 128) with
  | none =>
    simp only [topRest, hd, ccM_pure, kFin_none, topAnswerBudget]
    obtain ⟨k,z,st,hk,hz,h5,h10⟩ := topTransition_reject w pk index c hc t hpre a hd
    exact W9Machine.GoodQFor.steps' st
      (W9Machine.GoodQFor.reject (Q := Q) (A := 0) hz h5 h10)
      (by have hn : lFuel 1 = 2544 := by decide; rw [hn]; omega)
      (by have hcy : lCyc 1 = 1436 := by decide; rw [hcy]; omega)
      (fun hq => ⟨hq, by omega⟩)
  | some ds =>
    have hcan : decode 0 (a.extractLsb' 0 128) = some (Search.topDigits (a.extractLsb' 0 128)) := by
      rw [hd,(decode_top_sum _ _ hd).1]; rfl
    obtain ⟨s0,st0,he⟩ := topTransition_ok w pk index c hc t hpre a hcan
    let L := nctxOf w index (a.extractLsb' 0 128) (trPc 0 c)
    have hLok : L.ok := nctx_ok w index _ c hidx
    have hkn : KnownOK L.known s0 := nctx_known w pk index c t s0 a hidx hpre he
    obtain ⟨d,h12,hdst⟩ := hpre.dst0 rfl
    have hglob := Glob_writeHash hpre.glob a d h12 (by rcases hdst with rfl | rfl <;> decide)
    have hGs : Glob baseK w pk s0 := glob_frame hglob he.frame
      (by intro A h; simp at h) (by
        intro p hp
        rw [he.regs.get (by simp [baseK,topEntryRegs] at hp ⊢; tauto),writeHash_getReg]
        exact hpre.glob.1 p (by simpa [BC.bK,bK,layK,baseK] using hp))
    have hDs0 : DataOK s0 := hGs.2.2.2.2.2
    have ho := topEntry_orig w pk index c t s0 a hpre he
    have hO := nctx_orig w index _ (trPc 0 c) s0 ho hDs0
    have hfit : L.Fit (a.extractLsb' 0 128) := fun i hi => rfl
    have hdec := NCtx.decode_facts hd
    have hIn := nctx_initial w index _ (trPc 0 c) _ s0 he hdec.2.1
    have hEnc := nctx_encoded _ s0 _ (trPc 0 c) he hdec.1
    have hkeep : KnownOK (lfKeepK 0) s0 := by
      intro p hp
      simp [lfKeepK] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact he.s3
      all_goals rw [he.regs.get (by simp [topEntryRegs]),writeHash_getReg]
      all_goals exact hpre.glob.1 _ (by simp [BC.bK,bK,layK,baseK,lfT3,t3In])
    have h23 : s0.getReg .x23=BitVec.ofNat 64 (4096+L.leaf) := by
      rw [he.regs.get (by simp [topEntryRegs]),writeHash_getReg]
      simpa [L,nctxOf,dispatchHeap,s7Bias,hL] using hpre.s7 0 rfl
    have ho' : Orig w (fun o => 9288≤o ∧ o<layerBase 0+64*height 0) s0 :=
      ho.mono (fun o h => ⟨h.1, by norm_num [layerBase,height,layerEnd] at *; omega⟩)
    have H := top_bool_good L pk index hLok hidx rfl rfl s0 _ hkn hGs hkeep h23 ho' hO hEnc
      hfit hdec.1 hdec.2.1 Q hQ s0 hIn
    have H' : W9Machine.GoodQFor InlineTail.image s0
        (9+2231+12+InlineTail.Merkle.mkFuel 0)
        (8+all54Cost L+12+InlineTail.Merkle.mkCyc 0) Q
        (8+all54Cost L+12+InlineTail.Merkle.mkCyc 0)
        (Judg.ccM (topBoolSource L index pk) Judg.Kb) := by
      intro F hF
      obtain ⟨hx,heval⟩ := H F hF
      exact ⟨hx,fun hash => ⟨(heval hash).1,(heval hash).2.1,
        fun hs _ => (heval hash).2.2 hs⟩⟩
    rw [← topRest_source w pk index c _ ds hd] at H'
    have hb := topCost_credit w index c _ ds hd
    have hn : lFuel 1 = 2544 := by decide
    have hcy : lCyc 1 = 1436 := by decide
    have hmf : InlineTail.Merkle.mkFuel 0 = 73 := by decide
    have hmc : InlineTail.Merkle.mkCyc 0 = 268 := by decide
    apply W9Machine.GoodQFor.steps' st0 H'
    · rw [hn,hmf]; omega
    · rw [hcy,hmc]; dsimp only [L] at *; omega
    · intro hq
      refine ⟨hq,?_⟩
      simp only [topAnswerBudget,hd]
      dsimp only [L]
      omega

-- Complete top layer including compare and HALT. HashOk's credit premise
-- is applied only to the actual queried encoding; arbitrary answers still
-- have a valid unconditional execution bound.
theorem top_layer_good (w : WBytes) (pk : Digest) (index : Nat) (msg : LayerMsg)
    (s : MachineState) (hs : LayerIn w pk index 0 msg s) (Q : Prop) (hQ : Q) :
    W9Machine.GoodQFor InlineTail.image s (lFuel 1) (lCyc 1) Q (lCycA 1 - 1)
      (ccM (BC.layerLoop w index 1 msg) (kFin pk)) := by
  have hA := encoding_setup w pk index 0 msg s hs
  rw [layerLoop_succ w index 0 (by decide) msg]
  unfold layerHead
  by_cases hctr : (ClaudeWCT.W9.T3M.wbcCtr w 0).toNat ≥ counterLimit
  · rw [if_pos hctr,ccM_pure,kFin_none]
    obtain ⟨u,hst,hf,h5,h10⟩ := hA.1 hctr
    exact W9Machine.GoodQFor.steps' hst
      (W9Machine.GoodQFor.reject (Q := Q) (A := 0) hf h5 h10)
      (by decide) (by decide) (fun hq => ⟨hq,by decide⟩)
  · rw [if_neg hctr]
    obtain ⟨t,hst,hf,h5,hv,hin,c,hc,hpre⟩ := hA.2 (by omega)
    have hst' : Steps InlineTail.image s 9 9 t := by simpa [stepsA] using hst
    let inp := ClaudeWCT.W9.T3M.layerEncodingInputP 0 (route index 0).2 (route index 0).1 msg
      (ClaudeWCT.W9.T3M.wbcCtr w 0) (ClaudeWCT.W9.T3M.wbcPad w 0)
    have hblk : (toQ (pad64 inp)).blocks = 1 := BC.encoding_blocks w 0 _ _ msg
    have hq := topEncQ_layer (route index 0).2 (route index 0).1 msg
      (ClaudeWCT.W9.T3M.wbcCtr w 0) (ClaudeWCT.W9.T3M.wbcPad w 0)
    have H := Lower.hash_accept (q := toQ (pad64 inp))
      (K := fun a => ccM (topRest w index (a.extractLsb' 0 128)) (kFin pk))
      (topAnswerBudget w index c) hf h5 hv hin
      (fun a => top_answer_good w pk index c hc t hpre hs.idx a Q hQ) (A := lCycA 1 - 10)
      (by
        intro hash hok
        cases hd : decode 0 ((hash (toQ (pad64 inp))).extractLsb' 0 128) with
        | none =>
          simp only [topAnswerBudget,hd,hblk]
          decide
        | some ds =>
          have hcr := hok _ hq ds hd
          have hcost := topCost_credit w index c _ ds hd
          simp only [topAnswerBudget,hd,hblk]
          have hca : lCycA 1 = 1427 := by decide
          have hm : InlineTail.Merkle.mkCyc 0 = 268 := by decide
          rw [hca,hm]
          omega)
    rw [hblk] at H
    have he : ccM (shortHash inp >>= fun v => topRest w index v) (kFin pk) =
        cc (liftM (HashSpec.query (toQ (pad64 inp))) : OracleComp HashSpec _)
          (fun a => ccM (topRest w index (a.extractLsb' 0 128)) (kFin pk)) := by
      rw [ccM_shortHash_bind]
      rfl
    rw [← he] at H
    change W9Machine.GoodQFor InlineTail.image s (lFuel 1) (lCyc 1) Q (lCycA 1-1)
      (ccM (shortHash inp >>= fun v => topRest w index v) (kFin pk))
    exact W9Machine.GoodQFor.steps' hst' H (by have : 10≤lFuel 1 := by decide; omega)
      (by have : 17≤lCyc 1 := by decide; omega)
      (fun hq => ⟨hq,by have : 10≤lCycA 1 := by decide; omega⟩)

-- Top compare is closed above, so the induction starts at one. Each
-- successor executes a genuine lower43 layer and its actual Merkle prefix.
theorem layers_good (w : WBytes) (pk : Digest) (index : Nat) (hidx : index<2^31)
    (Q : Prop) (hQ : Q) :
    ∀ n, 1≤n → n≤4 → ∀ msg s, LayerIn w pk index (n-1) msg s →
      W9Machine.GoodQFor InlineTail.image s (lFuel n) (lCyc n) Q (lCycA n-1)
        (ccM (BC.layerLoop w index n msg) (kFin pk)) := by
  intro n
  induction n with
  | zero => intro hn; omega
  | succ n ih =>
    intro hn hn4 msg s hs
    by_cases hz : n=0
    · subst n
      simpa using top_layer_good w pk index msg s (by simpa using hs) Q hQ
    · have hv : (Fin.ofNat 4 n : Layer).val=n := by
        simp [Fin.val_ofNat,Nat.mod_eq_of_lt (show n<4 by omega)]
      have hlay : (Fin.ofNat 4 n : Layer)≠0 := by
        intro h; have := congrArg Fin.val h; rw [hv] at this; simpa using hz this
      rw [layerLoop_succ w index n (by omega) msg]
      have hg := layer_good_low w pk index (Fin.ofNat 4 n) hlay msg s (by simpa [hv] using hs)
        (fun ends => leafHash (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2
          (route index (Fin.ofNat 4 n)).1 ends >>= fun v =>
          merkleMsg w index (Fin.ofNat 4 n) v >>= BC.layerLoop w index n)
        (kFin pk) (kFin_none pk) (lFuel n+InlineTail.Merkle.mkFuel n)
        (lCyc n+InlineTail.Merkle.mkCyc n) (lCycA n-1+InlineTail.Merkle.mkCyc n) Q
        (fun ends u hu => by
          have hm := NativeMerkle.merkle_good w pk index (Fin.ofNat 4 n) ends u hidx hu
            (fun v => ccM (BC.layerLoop w index n (mkMessage w index (Fin.ofNat 4 n) v)) (kFin pk))
            (lFuel n) (lCyc n) (lCycA n-1) Q
            (fun v t ht => ih (by omega) (by omega) _ t (by
              have h := NativeMerkle.next_lower w pk index hidx (Fin.ofNat 4 n)
                (by rw [hv]; exact hz) ends u hu v t ht
              simpa [hv] using h))
          simp only [ccM_bind,merkleMsg,ccM_pure,hv] at hm ⊢
          exact hm)
      rw [hv] at hg
      have he : InlineTail.Merkle.mkFuel n=SigGolfCandidate.T3M.mkFuel n := rfl
      have he' : InlineTail.Merkle.mkCyc n=SigGolfCandidate.T3M.mkCyc n := rfl
      rw [he,he'] at hg
      exact hg.mono (by simp only [lFuel]; omega) (by simp only [lCyc]; omega)
        (fun hq => ⟨hq,by simp only [lCycA,layerCostA]; rw [if_neg hz];
          have : 1≤lCycA n := by interval_cases n <;> decide
          omega⟩)

-- Same oracle program and witness as the original afterFts; the image
-- parameter belongs in the execution judgment, never in the source program.
theorem source_eq (pk : Digest) (w : WBytes) (index : Nat) (root : Digest) :
    ccM (afterFts pk w index (some root)) Kb =
      ccM (BC.layerLoop w index 4 (.forest root)) (kFin pk) := by
  unfold afterFts
  rw [ccM_bind]
  rfl

-- The inline terminal macro removes exactly one accepting top-stage cycle.
-- These are arithmetic identities, not accepting measurements. The
-- execution theorem below still requires kernel checking on this context.
def acceptCycles : Nat := 5600
theorem accept_budget : lCycA 4 + 5 - 1 = acceptCycles := by
  rw [lCycA_4]
  rfl
theorem fuel_budget : lFuel 4 + 5 ≤ 8050 := by rw [lFuel_4]; decide
theorem all_budget : lCyc 4 + 5 ≤ 8050 := by rw [lCyc_4]; decide

-- Full four-layer provider on the actual inline image. The final top
-- comparison is already included in top_layer_good; no outcome callback
-- or old fixed-image after_good theorem occurs in this composition.
theorem after_good (pk : Digest) (w : WBytes) (Q : Prop) (hQ : Q)
    (a : HashOutput) (root : Digest) (u : MachineState)
    (h : FtsOut ⟨pk,w,a⟩ root u) :
    W9Machine.GoodQFor Images.InlineNative.image u 8050 8050 Q 5600
      (ccM (afterFts pk w (a.toNat % 2^31) (some root)) Kb) := by
  have hidx : a.toNat % 2^31 < 2^31 := Nat.mod_lt _ (by decide)
  obtain ⟨t,hst,hL3⟩ := layerIn_of_fts w pk _ root u hidx h.glob h.idx h.pc h.root h.wit
    h.a2 h.s10 h.heapOne h.heapTwo h.heapSeven h.heapThree h.heapFour h.heapFive
    h.coordStep h.topBase h.top h.top8
  have hg := layers_good w pk _ hidx Q hQ 4 (by decide) le_rfl (.forest root) t
    (by simpa using hL3)
  rw [source_eq pk w _ root]
  rw [← InlineNativeBinding.image_eq]
  rw [lFuel_4,lCyc_4,lCycA_4] at hg
  exact W9Machine.GoodQFor.steps' hst hg (by omega) (by omega)
    (fun hq => ⟨hq,by omega⟩)

-- Public closed provider type for the new native FINAL driver.
def AfterGoodBudget : Prop :=
  ∀ (pk : Digest) (w : WBytes) (Q : Prop), Q →
    ∀ (a : HashOutput) (root : Digest) (u : MachineState),
      FtsOut ⟨pk, w, a⟩ root u →
      W9Machine.GoodQFor Images.InlineNative.image u 8050 8050 Q acceptCycles
        (ccM (afterFts pk w (a.toNat % 2^31) (some root)) Kb)

theorem afterGoodBudget : AfterGoodBudget := after_good

#print axioms NativeMerkle.merkle_good
#print axioms top_layer_good
#print axioms layers_good
#print axioms after_good
#print axioms ld3_check
#print axioms layerIn_of_fts
#print axioms source_eq
#print axioms accept_budget
end SigGolfCandidate.T3M.Nonbinary.InlineTail.After
