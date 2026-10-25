import SigGolfCandidate.T3M_Verify_Nonbinary_TopCost
import SigGolfCandidate.T3M_Verify_Nonbinary_TopRun
import SigGolfCandidate.T3M_Verify_Nonbinary_LayerContext
import SigGolfCandidate.T3M_Verify_MerkleSem
import SigGolfCandidate.T3M_Verify_AfterDefs
import SigGolfCandidate.T3M_Verify_TopSource

set_option Elab.async false

section
namespace SigGolfCandidate.T3M
variable {floors : SigGolfCandidate.T3.Layer → Nat}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest Layer route)
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
end SigGolfCandidate.T3M
end
section
namespace SigGolfCandidate.T3M
variable {floors : SigGolfCandidate.T3.Layer → Nat}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest route coreDigit dataDigits maxDigit)
open Nonbinary (NCtx)
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
theorem nctx_prefix_eq (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p : Nat) (ds : List Nat)
    (m : Nat) (hm : m ≤ 51) (hds : ∀ j, j < m → ds.getD j 0 = (nctxOf w index v p).dig j) :
    (List.range' 0 m).foldlM (nctxOf w index v p).chainF [] =
      (List.range' 0 m).mapM (srcChain w index ds) := by
  unfold NCtx.chainF
  rw [foldlM_app_mapM]
  simp only [List.nil_append, id_map']
  apply mapM_congr'
  intro i hi
  have hi' := List.mem_range'_1.mp hi
  exact nctx_chain_eq w index v p ds i (by omega) (fun j hj => hds j (by omega))
theorem chainsP_top_eq (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (ds : List Nat) :
    chainsP w 0 (route index 0).2 (route index 0).1 ds =
      (List.range' 0 51).mapM (srcChain w index ds) := by
  unfold chainsP
  rw [← TopSource.take_mapM (srcChain w index ds) 51 (le_refl _)]
  rw [show (List.finRange (T3.chainCount 0)).take 51 = List.finRange (T3.chainCount 0) by
    rw [List.take_of_length_le]; simp [TopSource.chainCount0]]
  rfl
theorem nctx_fit6 (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p : Nat) :
    (nctxOf w index v p).Fit6 v := fun i hi => by
  rw [nctxOf_dig]; simp [topDig, hi]
/-- Campaign T51: a valid g0 field takes the head's dispatch to group 0's cell. -/
theorem nctx_group0 (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p : Nat) (u s : MachineState)
    (he : TopEntry u v p s) (hv0 : Nonbinary.NCtx.gValid v 0) :
    (nctxOf w index v p).GroupIn s 0 [] s :=
  ⟨⟨fun _ _ => rfl, Frame.refl s _, by simp⟩, rfl,
    ((nctxOf w index v p).g0_group (nctx_fit6 w index v p) s he.pc).1 hv0⟩
/-- Campaign T51: an invalid g0 field faults at the head's dispatch. -/
theorem nctx_group0_bad (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p : Nat) (u s : MachineState)
    (he : TopEntry u v p s) (hv0 : ¬ Nonbinary.NCtx.gValid v 0) : fetch vimage s = none :=
  ((nctxOf w index v p).g0_group (nctx_fit6 w index v p) s he.pc).2 hv0
/-- Campaign T51: chain 50's digit is the checksum whenever it is in range. -/
theorem nctx_ck (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p : Nat) :
    (nctxOf w index v p).CkOk := by
  intro ds hds h1 h2
  rw [nctx_dataSum] at hds
  have ht : T3.target 0 = 152 := rfl
  rw [nctxOf_dig]
  unfold topDig
  rw [if_neg (by omega), if_pos rfl, ht, hds]
  unfold Nonbinary.topT at h1 h2 ⊢
  omega
theorem top_chain_frame (c : NCtx) (hc : c.S3 = 14128) {s t : MachineState}
    (hf : Frame s t (c.Wr 51)) : Frame s t topChainWrites := by
  apply hf.mono
  intro A _ hA
  unfold NCtx.Wr NCtx.bufferEnd Nonbinary.slot at hA
  rw [hc] at hA
  unfold topChainWrites
  split_ifs at hA <;> omega
end SigGolfCandidate.T3M
end
section
set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.T3M
variable {floors : SigGolfCandidate.T3.Layer → Nat}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest)
theorem cmpDig_eq_iff (d e : Digest) :
    d = e ↔ (d.extractLsb' 0 64 = e.extractLsb' 0 64 ∧ d.extractLsb' 64 64 = e.extractLsb' 64 64) := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    apply BitVec.eq_of_toNat_eq
    have e1 := congrArg BitVec.toNat h1
    have e2 := congrArg BitVec.toNat h2
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one] at e1 e2
    have hd : d.toNat / 2 ^ 64 < 2 ^ 64 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]; exact d.isLt
    have he : e.toNat / 2 ^ 64 < 2 ^ 64 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]; exact e.isLt
    rw [Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt he] at e2
    rw [← Nat.mod_add_div d.toNat (2 ^ 64), ← Nat.mod_add_div e.toNat (2 ^ 64), e1, e2]
structure CmpIn (pk root : Digest) (t : MachineState) : Prop where
  copy : ∃ c, c < 64 ∧ t.pc = pcOf (cmpPc c) ∧ KnownOK (cmpK c) t ∧ DigAt t (cmpDst c) root
  pk : PkOK pk t
theorem cmpBr1_holds (c : Nat) (t : MachineState) (x y : Word) (hx : t.getMem (BitVec.ofNat 64 (cmpDst c)) = x)
    (hy : t.getMem (BitVec.ofNat 64 160) = y) (d : Bool) : Br.holds t (cmpBr1 c d) ↔ decide (x ≠ y) = d := by
  simp only [Br.holds, cmpBr1, CmpOp.eval, E.eval, kw, hx, hy]
  cases d <;> simp [bne_iff_ne]
theorem cmpBr2_holds (c : Nat) (t : MachineState) (x y : Word) (hx : t.getMem (BitVec.ofNat 64 (cmpDst c + 8)) = x)
    (hy : t.getMem (BitVec.ofNat 64 168) = y) (d : Bool) : Br.holds t (cmpBr2 c d) ↔ decide (x ≠ y) = d := by
  simp only [Br.holds, cmpBr2, CmpOp.eval, E.eval, kw, hx, hy]
  cases d <;> simp [bne_iff_ne]
set_option maxRecDepth 100000
theorem cmpCheck_all : (List.range 64).all cmpCheck = true := by decide +kernel
theorem cmpCheck_at (c : Nat) (hc : c < 64) : cmpCheck c = true :=
  List.all_eq_true.mp cmpCheck_all c (List.mem_range.mpr hc)
theorem cmp_good {P : Hash → Prop} (pk root : Digest) (t : MachineState) (h : CmpIn pk root t) (Q : Prop) (hQ : Q) :
    GoodQP P t 9 8 Q 8 (pure (root == pk, 0)) := by
  obtain ⟨c, hc, hpc, hknown, hroot⟩ := h.copy
  have hck := cmpCheck_at c hc
  simp only [cmpCheck, Bool.and_eq_true] at hck
  obtain ⟨hA, hR1⟩ := hck
  have hr0 : t.getMem (BitVec.ofNat 64 (cmpDst c)) = root.extractLsb' 0 64 := hroot.1
  have hr8 : t.getMem (BitVec.ofNat 64 (cmpDst c + 8)) = root.extractLsb' 64 64 := hroot.2
  have hp0 : t.getMem (BitVec.ofNat 64 160) = pk.extractLsb' 0 64 := h.pk.1
  have hp8 : t.getMem (BitVec.ofNat 64 168) = pk.extractLsb' 64 64 := h.pk.2
  have b1 := cmpBr1_holds c t _ _ hr0 hp0
  by_cases hlo : root.extractLsb' 0 64 = pk.extractLsb' 0 64
  · obtain ⟨u, hu⟩ := spec_run hA t hpc hknown (by
      intro b hb
      simp only [cmpAcc, List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb
      exact (b1 false).mpr (by simp [hlo])) (by simp)
    have h5 : u.getReg .x5 = 1 := hu.regs (.x5, kw 1) (by simp [cmpAcc])
    have h10 : u.getReg .x10 = root.extractLsb' 64 64 - pk.extractLsb' 64 64 := by
      simpa only [cmpDelta, E.eval, BinOp.eval, kw, hr8, hp8] using
        hu.regs (.x10, cmpDelta c) (by simp [cmpAcc])
    have heq : u.getReg .x10 = 0 ↔ root = pk := by
      rw [h10]
      change root.extractLsb' 64 64 - pk.extractLsb' 64 64 = 0#64 ↔ root = pk
      rw [BitVec.sub_eq_iff_eq_add, BitVec.zero_add, cmpDig_eq_iff]
      simp only [hlo, true_and]
    have hg := GoodQP.halt (P := P) (Q := Q) (A := 1) (hu.ecall rfl) h5 (fun _ => ⟨hQ, le_refl 1⟩)
    have hb : decide (u.getReg .x10 = 0) = (root == pk) := by
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, beq_iff_eq, heq]
    rw [hb] at hg
    exact GoodQP.stepsQ hu.steps hg (by simp [cmpAcc]) (by simp [cmpAcc])
      (fun q => ⟨q, by simp [cmpAcc]⟩)
  · have hne : root ≠ pk := fun e => hlo (by rw [e])
    rw [show (root == pk) = false from beq_eq_false_iff_ne.mpr hne]
    obtain ⟨u, hu⟩ := spec_run hR1 t hpc hknown (by
      intro b hb
      simp only [cmpRej1, List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb
      exact (b1 true).mpr (by simp [hlo])) (by simp)
    have h5 : u.getReg .x5 = 1 := hu.regs (.x5, kw 1) (by simp [cmpRej1])
    have h10 : u.getReg .x10 = 1 := hu.regs (.x10, kw 1) (by simp [cmpRej1])
    exact GoodQP.stepsQ hu.steps (GoodQP.reject (Q := Q) (A := 0) (hu.ecall rfl) h5 h10)
      (by simp [cmpRej1]) (by simp [cmpRej1]) (fun q => ⟨q, by simp [cmpRej1]⟩)
end SigGolfCandidate.T3M
end
section
namespace SigGolfCandidate.T3M
variable {floors : SigGolfCandidate.T3.Layer → Nat}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest route)
set_option maxHeartbeats 800000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
end SigGolfCandidate.T3M
end
section
namespace SigGolfCandidate.T3M
variable {floors : SigGolfCandidate.T3.Layer → Nat}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height pad64 shortHash leafHash)
def kFin (pk : Digest) : Option Digest → OracleComp HashSpec Obs := fun x =>
  ccM (match x with
    | some r => pure (r == pk)
    | _ => pure false) Kb
theorem kFin_none (pk : Digest) : kFin pk none = pure (false, 0) := by simp [kFin, Kb]
theorem kFin_some (pk r : Digest) : kFin pk (some r) = pure (r == pk, 0) := by simp [kFin, Kb]
open ClaudeWCT.WCT9 (LayerMsg)
def RestIn (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index n : Nat) (msg : LayerMsg) (s : MachineState) : Prop :=
  if n = 0 then match msg with
    | .forest root => CmpIn pk root s
    | .pair _ _ => False
  else LayerIn w pk index (n - 1) msg s
theorem mkEnd_top (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (u : MachineState) (root : Digest)
    (t : MachineState) (ht : MkEnd w pk 0 (route index 0).1 u root t) : CmpIn pk root t := by
  have hl4 : (route index 0).1 < 4096 := by simpa [hL] using leaf_lt index 0
  have hpc : t.pc = pcOf (cmpPc (mkSh 0 1 (route index 0).1)) := by
    rw [ht.pc]
    congr 1
    simp [mkFin, cmpPc, show mkNch 0 - 1 = 1 from rfl, show mkBits 0 1 = 6 from rfl,
      show mkOff 0 1 6 = 27 from rfl, BC.mkShp, mkShp]
    omega
  refine ⟨⟨mkSh 0 1 (route index 0).1, mkSh_lt _ _ _, ?_, ?_, ?_⟩, ht.glob.2.2.1⟩
  · exact hpc
  · intro p hp
    simp only [cmpK, List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact ht.glob.1 p hp
    · rw [ht.dstReg, mkDst_cmp _ hl4]
  · rw [mkDst_cmp _ hl4]; exact ht.root
theorem mkStop_next (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (hidx : index < 2 ^ 31)
    (lay : Layer) (ends : List Digest) (u : MachineState) (hu : LeafOut w pk index lay ends u)
    (v : Digest) (t : MachineState) (ht : MkStop w pk lay.val (route index lay).1 u v t) :
    RestIn w pk index lay.val (mkMessage w index lay v) t := by
  by_cases h0 : lay.val = 0
  · have hz : lay = 0 := Fin.ext h0
    subst lay
    exact mkEnd_top w pk index u v t ht
  · simpa [RestIn, h0] using mkStop_next_lower w pk index hidx lay h0 ends u hu v t ht
end SigGolfCandidate.T3M
end
section
namespace SigGolfCandidate.T3M
variable {floors : SigGolfCandidate.T3.Layer → Nat}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput route coreDigit dataDigits)
open Nonbinary (NCtx)
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
theorem chainsCost_mono (c : NCtx) (m : Nat) (hm : m ≤ 51) : c.chainsCost 0 m ≤ c.chainsCost 0 51 := by
  have := Nonbinary.NCtx.chainsCost_add' c 0 m (51-m)
  rw [show m+(51-m)=51 by omega] at this
  omega
/-- Path-aware top accounting contract: the selector cost plus the verifier-side top path bonus is at most the
worst-case selector cost `selMax = 6`. d6b: hint clear (`verificationLow 0 high _ = !high`) costs 4 and earns the
top bonus 2; hint set costs 6 (HIGH, or LOW forced) and earns nothing. -/
theorem top_sel_bonus_le (high : Bool) (a : BitVec 256) :
    Verify.Nonbinary.selCost high a +
      ClaudeWCT.WCT9.CanonicalPolicy.pathBonus 0 (ClaudeWCT.WCT9.verificationLow 0 high a) ≤ 6 := by
  unfold Verify.Nonbinary.selCost
  cases high <;> simp [ClaudeWCT.WCT9.CanonicalPolicy.pathBonus, ClaudeWCT.WCT9.verificationLow] <;>
    split_ifs <;> omega
/-- Campaign T51: the verifier's group check is the spec's `topGroupValid`. -/
theorem topGroupValid_iff (v : Digest) (q : Nat) :
    ClaudeWCT.WCT9.topGroupValid v q = true ↔ Nonbinary.NCtx.gValid v q := by
  unfold ClaudeWCT.WCT9.topGroupValid Nonbinary.NCtx.gValid
  split_ifs <;> simp
/-- Campaign T51: the first invalid group. -/
theorem first_invalid (V : Digest) (h : ¬ ∀ q, q < 17 → Nonbinary.NCtx.gValid V q) :
    ∃ j, j < 17 ∧ (∀ q, q < j → Nonbinary.NCtx.gValid V q) ∧ ¬ Nonbinary.NCtx.gValid V j := by
  classical
  have hex : ∃ j, j < 17 ∧ ¬ Nonbinary.NCtx.gValid V j := by
    by_contra hn; push Not at hn; exact h (fun q hq => hn q hq)
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, fun q hq => ?_, (Nat.find_spec hex).2⟩
  have := Nat.find_min hex hq
  push Not at this
  exact this (by have := (Nat.find_spec hex).1; omega)
theorem topGroupBad_before (v : Digest) (j : Nat) (hval : ∀ q, q < j → Nonbinary.NCtx.gValid v q) (i : Nat)
    (hi : i < 3 * j) (hi50 : i < 50) : ClaudeWCT.WCT9.topGroupBad v i = false := by
  cases h : ClaudeWCT.WCT9.topGroupBad v i
  · rfl
  · rw [TopSource.topGroupBad_iff] at h
    rcases h with ⟨-, -, hg⟩ | ⟨h50, -⟩
    · have := (topGroupValid_iff v (i/3)).mpr (hval (i/3) (by omega))
      rw [hg] at this; cases this
    · omega
/-- Campaign T51: the first invalid group `j` (16 = the r7 pair at chain 48) stops the verifier after `3 j` chains. -/
theorem topRejectLength_group (v : Digest) (j : Nat) (hj : j < 17)
    (hval : ∀ q, q < j → Nonbinary.NCtx.gValid v q) (hbad : ¬ Nonbinary.NCtx.gValid v j) :
    ClaudeWCT.WCT9.topRejectLength v = 3 * j := by
  apply TopSource.topRejectLength_bad v (3*j) (by omega)
  · intro i hi
    exact topGroupBad_before v j hval i hi (by omega)
  · rw [TopSource.topGroupBad_iff]
    left
    refine ⟨by omega, by omega, ?_⟩
    rw [show 3 * j / 3 = j by omega]
    cases h : ClaudeWCT.WCT9.topGroupValid v j
    · rfl
    · exact absurd ((topGroupValid_iff v j).mp h) hbad
/-- Campaign T51: all 17 groups valid but the checksum out of range: the verifier runs the 50 data chains. -/
theorem topRejectLength_ck (v : Digest) (hval : ∀ q, q < 17 → Nonbinary.NCtx.gValid v q)
    (hout : ¬ ((dataDigits 0 v).sum ≤ T3.target 0 ∧ T3.target 0 - (dataDigits 0 v).sum < 6)) :
    ClaudeWCT.WCT9.topRejectLength v = 50 := by
  apply TopSource.topRejectLength_bad v 50 (by omega)
  · intro i hi
    exact topGroupBad_before v 17 hval i (by omega) hi
  · rw [TopSource.topGroupBad_iff]
    right
    refine ⟨rfl, ?_⟩
    unfold ClaudeWCT.WCT9.topChecksumOk
    simp only [decide_eq_false_iff_not]
    exact hout
/-- Campaign T51: a decoded word's digits (data digits, then the checksum) are the chain context's digits. -/
theorem nctx_top_digits (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p : Nat)
    (hs2 : T3.target 0 - (dataDigits 0 v).sum < 6) :
    ∀ j, j < 51 → (dataDigits 0 v ++ [T3.target 0 - (dataDigits 0 v).sum]).getD j 0 = (nctxOf w index v p).dig j := by
  intro j hj
  have hl := ClaudeWCT.WCT9.dataDigits_top_length v
  by_cases h50 : j < 50
  · rw [List.getD_append _ _ _ _ (by rw [hl]; exact h50)]
    exact nctx_data_digits w index v p j h50
  · have hj50 : j = 50 := by omega
    subst hj50
    rw [nctxOf_dig, List.getD_append_right _ _ _ _ (by rw [hl]), hl]
    unfold topDig
    rw [if_neg (by omega), if_pos rfl]
    simp only [Nat.sub_self, List.getD_cons_zero]
    omega
/-- Campaign T51: the verify data words (masks, gate) survive the top entry. -/
theorem topEntry_data (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index c : Nat) (hc : c < nCopy 0)
    (t s0 : MachineState) (a : BitVec 256) (hpre : BC.EncPre w pk index 0 c t)
    (he : TopEntry (writeHash t a) (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a) (trPc 0 c) s0) :
    DataOK s0 := by
  have hc' : c < 128 := by have := BC.nCopy_eq; omega
  have ha := topRowA_mem c hc'
  have hal : 15272 ≤ topRowA c ∧ topRowA c ≤ 15528 ∧ topRowA c % 8 = 0 := by
    simp only [Nonbinary.aVals, List.mem_cons, List.not_mem_nil, or_false] at ha; omega
  obtain ⟨d, h12, hd⟩ := hpre.dst (by decide +kernel)
  change (d + 16 = topRowA c ∧ WIT + BC.layerEnd 0 + 16 ≤ topRowA c) ∨ d = topRowA c + 48 at hd
  exact (Glob_writeHash hpre.glob a d h12
    (safeDest_hi d (by unfold WLO WIT; omega) (by omega) (by omega))).2.2.2.2.2.congr
    (fun A hlo hA => he.frame.get (by omega) (by unfold TAB at hlo; omega))
/-- Campaign T51: after the 51 top chains: the top leaf (7 cycles), the 12 folds and the root compare. -/
theorem top_leaf_tail (floors : T3.Layer → Nat) (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index c : Nat)
    (hc : c < nCopy 0) (hidx : index < 2 ^ 31) (t s0 : MachineState) (a : BitVec 256)
    (hpre : BC.EncPre w pk index 0 c t)
    (he : TopEntry (writeHash t a) (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a) (trPc 0 c) s0)
    (Q : Prop) (hQ : Q) (ends : List Digest) (z : MachineState)
    (hz : (nctxOf w index (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a) (trPc 0 c)).TopOut s0 ends z) :
    GoodQP (HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w)) z 77 263 Q 263
      (ccM (ClaudeWCT.WCT9.leafHashW 0 (route index 0).2 (route index 0).1 (ClaudeWCT.W9.T3M.wtopLeafPad w)
        (ClaudeWCT.W9.T3M.wleafHigh w 0) ends >>= merkleP w index 0)
        (fun r => kFin pk (some r))) := by
  obtain ⟨hr, hfz, hlen, hend, hpc, -⟩ := hz
  have hregs : RegsExcept s0 z topChainRegs := by
    intro r hrn
    have h24 : r ≠ .x24 := by intro hh; subst hh; exact hrn (by decide +kernel)
    have h29 : r ≠ .x29 := by intro hh; subst hh; exact hrn (by decide +kernel)
    have h18 : r ≠ .x18 := by intro hh; subst hh; exact hrn (by decide +kernel)
    exact hr r (fun hh => hrn ((by decide +kernel : chainRegs ⊆ topChainRegs) hh)) h24 h29 h18
  have hframe : Frame s0 z topChainWrites := top_chain_frame _ rfl hfz
  have h15 : z.getReg .x9 = 0x7fc00#64 := by
    rw [hregs.get (by decide +kernel)]; exact he.table
  have hready := topLeafReady_of w pk index c hc t s0 z a ends hpre he hpc hregs hframe h15 hlen
    (fun j hj => by have h := hend j (by omega); exact h)
  obtain ⟨u, st, hu⟩ := leafT_step w pk index c hc hidx ends z hready
  have hm := merkle_good (P := HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w)) w pk index 0 ends u hidx hu
    (fun r => kFin pk (some r)) 9 8 8 Q
    (fun root t ht => by
      rw [kFin_some]
      exact cmp_good pk root t (mkEnd_top w pk index u root t (by simpa [MkStop] using ht)) Q hQ)
  have hmP : merkleP w index 0 = merklePrefix w index 0 := by
    funext x; rw [merkleP_eq]; rfl
  rw [hmP]
  have := GoodQP.steps st hm
  refine this.mono ?_ ?_ (fun h => ⟨h, ?_⟩) <;> simp [mkFuel_vals, mkCyc_vals]
/-- Campaign T51 top layer after its encoding hash: selector + head (`selCost + 5`), the 16 groups, the r7 pair and
the checksum chain (`chainsCost 0 51 + 78`), leaf/folds/compare (263): accepted cost
`chainsCost 0 51 + 346 + selCost <= 1322 - floor` by the cost law (970 + penalty) and the policy's floor. -/
theorem top_after_hash (floors : T3.Layer → Nat) (hbound : ∀ lay, floors lay ≤ 301) (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index c : Nat) (hc : c < nCopy 0) (hidx : index < 2 ^ 31)
    (t : MachineState) (hpre : BC.EncPre w pk index 0 c t) (Q : Prop) (hQ : Q) (q : Query) (hq : EncQ 0 q)
    (a : BitVec 256) :
    GoodQP (fun hash => hash q = a ∧ HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w) hash) (writeHash t a) 2372 2693 Q
      (1322 - floors 0)
      (ccM (ClaudeWCT.W9.T3M.topLayerP w index (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a)) (kFin pk)) := by
  have hfloor := hbound 0
  obtain ⟨n0, s0, st0, hn0, hn0e, he⟩ := topTransition w pk index c hc t hpre a
  set v := T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a with hvdef
  have hsel := top_sel_bonus_le (ClaudeWCT.W9.T3M.wtopHigh w) a
  set L := nctxOf w index v (trPc 0 c) with hLdef
  have hLok : L.ok := nctx_ok w index v c hidx
  have hkn : ∀ p ∈ L.known, s0.getReg p.1 = p.2 := nctx_known w pk index c t s0 a hpre he
  have hD := topEntry_data w pk index c hc t s0 a hpre he
  have hO := nctx_orig w index v (trPc 0 c) s0 (topEntry_orig w pk index c hc t s0 a hpre he)
    (topEntry_bufferOrig w pk index c hc t s0 a hpre he) hD
  have hds := nctx_digits w index v (trPc 0 c)
  have hf := nctx_fit6 w index v (trPc 0 c)
  have hEnc : Nonbinary.NCtx.Encoded0 v s0 := ⟨he.lo, he.hi, he.mask⟩
  have hmask : s0.getMem 0xffbdf0#64 = 65280#64 := hD.mask6
  have hck := nctx_ck w index v (trPc 0 c)
  have hcc : L.chainsCost 0 51 ≤ 2341 := L.chainsCost_any hds
  cases hdec : T3.decode 0 v with
  | some ds =>
    obtain ⟨-, hrv, ⟨hs1, hs2⟩, rfl⟩ := ClaudeWCT.WCT9.decode_top_some hdec
    have hval : ∀ q, q < 17 → Nonbinary.NCtx.gValid v q := (Nonbinary.NCtx.topRanksValid_iff v).mp hrv
    have hin : Nonbinary.topT - 5 ≤ ((List.range 50).map L.dig).sum ∧
        ((List.range 50).map L.dig).sum ≤ Nonbinary.topT := by
      rw [hLdef, nctx_dataSum]
      have ht : T3.target 0 = 152 := rfl
      unfold Nonbinary.topT; omega
    have hdig := nctx_top_digits w index v (trPc 0 c) hs2
    rw [ClaudeWCT.W9.T3M.topLayerP_of_decode w index hdec, ccM_map, layerP_eq, ccM_bind, chainsP_top_eq,
      ← nctx_prefix_eq w index v (trPc 0 c) _ 51 (le_refl _) (fun j hj => hdig j hj)]
    have hg0 := nctx_group0 w index v (trPc 0 c) _ s0 he (hval 0 (by omega))
    have body : GoodQP (HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w)) (writeHash t a) 2372 2693 Q
        (L.chainsCost 0 51 + 346 + Verify.Nonbinary.selCost (ClaudeWCT.W9.T3M.wtopHigh w) a)
        (ccM ((List.range' 0 51).foldlM L.chainF [])
          (fun ends => ccM (ClaudeWCT.WCT9.leafHashW 0 (route index 0).2 (route index 0).1 (ClaudeWCT.W9.T3M.wtopLeafPad w)
            (ClaudeWCT.W9.T3M.wleafHigh w 0) ends >>= merkleP w index 0)
            (fun r => kFin pk (some r)))) := by
      have H := L.top_full (P := HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w)) hLok hds hck hkn hO hEnc hf hmask hval hin
        (fun ends => ccM (ClaudeWCT.WCT9.leafHashW 0 (route index 0).2 (route index 0).1 (ClaudeWCT.W9.T3M.wtopLeafPad w)
            (ClaudeWCT.W9.T3M.wleafHigh w 0) ends >>= merkleP w index 0)
          (fun r => kFin pk (some r))) 77 263 263 Q
        (fun ends z hz => top_leaf_tail floors w pk index c hc hidx t s0 a hpre he Q hQ ends z hz)
        s0 hg0
      have H2 := GoodQP.steps st0 H
      refine H2.mono ?_ ?_ (fun h => ⟨h, ?_⟩) <;> omega
    by_cases hcr : L.chainsCost 0 51 + Verify.Nonbinary.selCost (ClaudeWCT.W9.T3M.wtopHigh w) a ≤ 976 - floors 0
    · exact (body.mono (le_refl _) (le_refl _) (fun h => ⟨h, by omega⟩)).pre_mono (fun _ h => h.2)
    · refine GoodQP.of_false_pre body ?_
      rintro hash ⟨hea, hok⟩
      have h7 := hok 0 q hq (dataDigits 0 v ++ [T3.target 0 - (dataDigits 0 v).sum]) (by rw [hea]; exact hdec)
      simp only [ClaudeWCT.WCT9.CanonicalPolicy.pathReward, ClaudeWCT.WCT9.CanonicalPolicy.reward, hea] at h7
      rw [ClaudeWCT.WCT9.wordCredit_top hdec] at h7
      have hbalance := L.chainsCost_accepted hds v _ hdec (fun i hi => hdig i hi)
      exact hcr (by omega)
  | none =>
    refine GoodQP.pre_mono (P := HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w)) ?_ (fun _ h => h.2)
    refine Nonbinary.NCtx.goodQ_vacuous (A := 0) ?_ Q (1322 - floors 0)
    rw [ClaudeWCT.W9.T3M.topLayerP_of_decode_none w index hdec, ccM_map]
    simp only [kFin_none]
    have hv' : v.toNat < 2 ^ T3.encodedBits 0 := by simpa [T3.encodedBits] using v.isLt
    by_cases hall : ∀ q, q < 17 → Nonbinary.NCtx.gValid v q
    · have hout : ¬ ((dataDigits 0 v).sum ≤ T3.target 0 ∧ T3.target 0 - (dataDigits 0 v).sum < 6) := by
        intro h
        rw [ClaudeWCT.WCT9.decode_top_of hv' ((Nonbinary.NCtx.topRanksValid_iff v).mpr hall) h.1 h.2] at hdec
        cases hdec
      rw [topRejectChains_eq w index v 50 (le_refl _) (topRejectLength_ck v hall hout),
        ← nctx_prefix_eq w index v (trPc 0 c) _ 50 (by omega)
          (fun j hj => nctx_data_digits w index v (trPc 0 c) j hj)]
      have hg0 := nctx_group0 w index v (trPc 0 c) _ s0 he (hall 0 (by omega))
      have hout' : ¬ (Nonbinary.topT - 5 ≤ ((List.range 50).map L.dig).sum ∧
          ((List.range 50).map L.dig).sum ≤ Nonbinary.topT) := by
        rw [hLdef, nctx_dataSum]
        have ht : T3.target 0 = 152 := rfl
        unfold Nonbinary.topT; omega
      have H := L.top_bad_ck (P := HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w)) hLok hds hkn hO hEnc hf hmask hall
        hout' (fun _ => pure (false, 0)) (fun _ => rfl) False 0 s0 hg0
      have hm := chainsCost_mono L 50 (by omega)
      have hov := Nonbinary.NCtx.ov_le 16 (le_refl _)
      exact (GoodQP.steps st0 H).mono (by omega) (by omega) (fun h => h.elim)
    · obtain ⟨j, hj, hjmin, hjbad⟩ := first_invalid v hall
      by_cases hj0 : j = 0
      · subst hj0
        rw [topRejectChains_eq w index v 0 (by omega) (by rw [topRejectLength_group v 0 (by omega) hjmin hjbad])]
        simp only [List.range'_zero, List.mapM_nil, ccM_pure]
        have hf0 := nctx_group0_bad w index v (trPc 0 c) _ s0 he hjbad
        exact (GoodQP.steps st0 (Nonbinary.NCtx.goodQ_fault (P := HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w))
          (Q := False) (A := 0) hf0)).mono (by omega) (by omega) (fun h => h.elim)
      · rw [topRejectChains_eq w index v (3 * j) (by omega) (topRejectLength_group v j hj hjmin hjbad),
          ← nctx_prefix_eq w index v (trPc 0 c) _ (3 * j) (by omega)
            (fun i hi => nctx_data_digits w index v (trPc 0 c) i (by omega))]
        have hg0 := nctx_group0 w index v (trPc 0 c) _ s0 he (hjmin 0 (by omega))
        have H := L.top_bad_group (P := HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w)) hLok hds hkn hO hEnc hf hmask
          j (by omega) (by omega) hjmin hjbad (fun _ => pure (false, 0)) (fun _ => rfl) False 0 s0 hg0
        have hm := chainsCost_mono L (3 * j) (by omega)
        have hov := Nonbinary.NCtx.ov_le j (by omega)
        exact (GoodQP.steps st0 H).mono (by omega) (by omega) (fun h => h.elim)
end SigGolfCandidate.T3M
end
section
namespace SigGolfCandidate.T3M
variable {floors : SigGolfCandidate.T3.Layer → Nat}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route leafHash)
open ClaudeWCT.WCT9 (LayerMsg)
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
/-- Stage 2 (C2 + C3, as #866): top head 5 steps (row high-word pad), top leaf without the 16-byte pad stores and the
leaf tweak high-word store. Configuration (1)+(2): target 146 (accepted chains 936 -> 927) and the e7b
top-half selector (worst path 7 instead of 4, the honest LOW path's 3 cycles are credited by the top path bonus):
1292 -> 1286, fuel/cycles +3. d6b head (img-v4/v6): HIGH path 6 instead of 7, top bonus 2: 1286 -> 1285. -/
def topFuel : Nat := 5 + 1 + 2372
def topCyc : Nat := 5 + 8 + 2693
def topCycA (floors : T3.Layer → Nat) : Nat := 5 + 8 + (1322 - floors 0)
theorem top_layer_good (floors : T3.Layer → Nat) (hbound : ∀ lay, floors lay ≤ 301) (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (hidx : index < 2 ^ 31) (Q : Prop) (hQ : Q)
    (M : LayerMsg) (s : MachineState) (hs : LayerIn w pk index 0 M s) :
    GoodQP (HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w)) s topFuel topCyc Q (topCycA floors)
      (ccM (BC.layerLoop w index 1 M) (kFin pk)) := by
  rw [layerLoop_one]
  have hA := BC.encoding_setup w pk index 0 M s hs
  have hsA : stepsA (0 : Layer).val = 5 := rfl
  by_cases hctr : (ClaudeWCT.W9.T3M.wbcCtr w index 0).toNat ≥ ClaudeWCT.WCT9.verifyWindow
  · exact absurd hctr (ClaudeWCT.WCT9.ctr_not_ge_verifyWindow _)
  · rw [if_neg hctr]
    obtain ⟨t, hst, hf, h5, hv, hin, hpre⟩ := hA.2 (by omega)
    set c := BC.cpIdx index (0 : Layer).val with hcdef
    have hc : c < nCopy 0 := by
      have h := BC.nCopy_eq
      have : c < 128 := by
        show (if (0 : Nat) = 3 then 0 else index / 2 ^ below (0 + 1) % 2 ^ hL (0 + 1)) < 128
        rw [if_neg (by decide +kernel)]
        exact lt_of_lt_of_le (Nat.mod_lt _ (by decide +kernel)) (by decide +kernel)
      omega
    rw [hsA] at hst
    have hblk := BC.encoding_blocks w index 0 (route index 0).2 (route index 0).1 M (ClaudeWCT.W9.T3M.wbcHigh w index 0)
    have hq := encQ_layer 0 (route index 0).2 (route index 0).1 M (ClaudeWCT.W9.T3M.wbcCtr w index 0)
      (ClaudeWCT.W9.T3M.wbcPad w index 0) (ClaudeWCT.W9.T3M.wbcRight w) (ClaudeWCT.W9.T3M.wbcHigh w index 0)
    have := GoodQP.verificationHash_bind_pre (lay := 0) (high := ClaudeWCT.W9.T3M.wtopHigh w)
      (f := ClaudeWCT.W9.T3M.topLayerP w index) hf h5 hv hin
      (fun a => by
        rw [show ClaudeWCT.WCT9.verificationAnswer 0 (ClaudeWCT.W9.T3M.wtopHigh w) a =
          T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a from rfl]
        exact top_after_hash floors hbound w pk index c hc hidx t hpre Q hQ _ hq a)
    rw [hblk] at this
    exact (GoodQP.steps' hst this (by simp [topFuel]) (by simp [topCyc]) (by simp [topCycA]; omega))
def lCyc : Nat → Nat
  | 0 => 8
  | 1 => topCyc
  | n + 2 => layerCost (n + 1) 0 + mkCyc (n + 1) + lCyc (n + 1)
def lCycA (floors : T3.Layer → Nat) : Nat → Nat
  | 0 => 8
  | 1 => topCycA floors
  | n + 2 => layerCostA floors (n + 1) + mkCyc (n + 1) + lCycA floors (n + 1)
def lFuel : Nat → Nat
  | 0 => 9
  | 1 => topFuel
  | n + 2 => layerFuel (n + 1) + mkFuel (n + 1) + lFuel (n + 1)
theorem lCyc_4 : lCyc 4 = 6704 := by decide +kernel
/-- Stage 2: floor-free constant 5303 (stage 1: 5334; C2 −13, C3 −7). Configuration (1)+(2): 5297 (top −9 + 3); d6b 5296. -/
theorem lCycA_4 (floors : T3.Layer → Nat) (hbound : ∀ lay, floors lay ≤ 301) :
    lCycA floors 4 = 5333 - ((List.finRange 4).map floors).sum := by
  have h0 := hbound 0
  have h1 := hbound 1
  have h2 := hbound 2
  have h3 := hbound 3
  change (1181 - floors 3) + 153 + ((1173 - floors 2) + 153 +
    ((1173 - floors 1) + 165 + (5 + 8 + (1322 - floors 0)))) =
      5333 - (floors 0 + (floors 1 + (floors 2 + (floors 3 + 0))))
  omega
theorem lFuel_4 : lFuel 4 = 7755 := by decide +kernel
theorem layers_good (floors : T3.Layer → Nat) (hbound : ∀ lay, floors lay ≤ 301) (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (hidx : index < 2 ^ 31) (Q : Prop) (hQ : Q) :
    ∀ n, n ≤ 4 → ∀ msg s, RestIn w pk index n msg s →
      GoodQP (HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w)) s (lFuel n) (lCyc n) Q (lCycA floors n)
        (ccM (BC.layerLoop w index n msg) (kFin pk)) := by
  intro n
  induction n with
  | zero =>
    intro _ msg s hs
    cases msg with
    | forest root =>
      simp only [BC.layerLoop, ccM_pure, kFin_some]
      exact cmp_good pk root s hs Q hQ
    | pair left right => exact False.elim hs
  | succ n ih =>
    intro hn msg s hs
    have hs' : LayerIn w pk index n msg s := by simpa [RestIn] using hs
    by_cases hn0 : n = 0
    · subst hn0
      exact top_layer_good floors hbound w pk index hidx Q hQ msg s hs'
    have hv : (Fin.ofNat 4 n : Layer).val = n := by simp [Fin.val_ofNat, Nat.mod_eq_of_lt (show n < 4 by omega)]
    have hlay : (Fin.ofNat 4 n : Layer) ≠ 0 := fun h => hn0 (by rw [← hv, h]; rfl)
    rw [layerLoop_succ w index n (by omega) hn0 msg]
    have hg := layer_good_low floors hbound (ClaudeWCT.W9.T3M.wtopHigh w) w pk index (Fin.ofNat 4 n) hlay msg s (by rwa [hv])
      (fun ends => ClaudeWCT.WCT9.leafHashW (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1
          (ClaudeWCT.W9.T3M.wtopLeafPad w) (ClaudeWCT.W9.T3M.wleafHigh w (Fin.ofNat 4 n)) ends >>=
        fun v => merkleMsg w index (Fin.ofNat 4 n) v >>= BC.layerLoop w index n)
      (kFin pk) (kFin_none pk) (lFuel n + mkFuel n) (lCyc n + mkCyc n) (lCycA floors n + mkCyc n) Q
      (fun ends u hu => by
        have hm := merkle_good (P := HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w)) w pk index (Fin.ofNat 4 n) ends u hidx hu
          (fun v => ccM (BC.layerLoop w index n (mkMessage w index (Fin.ofNat 4 n) v)) (kFin pk))
          (lFuel n) (lCyc n) (lCycA floors n) Q
          (fun v t ht => ih (by omega) _ t (by
            have h := mkStop_next w pk index hidx (Fin.ofNat 4 n) ends u hu v t ht
            rw [hv] at h
            exact h))
        simp only [ccM_bind, merkleMsg, ccM_pure, hv] at hm ⊢
        exact hm)
    rw [hv] at hg
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [show m + 1 + 1 = m + 2 from rfl]
    exact hg.mono (by simp only [lFuel]; omega) (by simp only [lCyc]; omega)
      (fun q => ⟨q, by simp only [lCycA]; omega⟩)
theorem after_good (floors : T3.Layer → Nat) (hcredit : CreditFloors floors) (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (Q : Prop) (hQ : Q) (a : HashOutput)
    (top : Digest × Digest) (u : MachineState)
    (h : FtsOut ⟨pk, w, a⟩ top u) :
    GoodQP (HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w)) u 8050 8050 Q 5264
      (ccM (afterFts pk w (ClaudeWCT.WCT9.digestIndex a) (some top)) Kb) := by
  have hidx : ClaudeWCT.WCT9.digestIndex a < 2 ^ 31 := ClaudeWCT.WCT9.digestIndex_lt a
  obtain ⟨t, hst, hL3⟩ := layerIn_of_fts w pk _ top.1 top.2 u hidx h.glob h.idx h.pc h.left h.right h.wit h.base h.a1
    h.s10 h.heapOne h.heapTwo h.heapSeven h.heapThree h.heapFour h.heapFive h.coordStep h.topBase h.top h.top8 h.a2 h.d0
  have hg := layers_good floors hcredit.1 w pk _ hidx Q hQ 4 le_rfl (.pair top.1 top.2) t (by simpa [RestIn] using hL3)
  have e : ccM (afterFts pk w (ClaudeWCT.WCT9.digestIndex a) (some top)) Kb =
      ccM (BC.layerLoop w (ClaudeWCT.WCT9.digestIndex a) 4 (.pair top.1 top.2)) (kFin pk) := by
    unfold afterFts
    rw [ccM_bind]
    rfl
  rw [e]
  rw [lFuel_4, lCyc_4, lCycA_4 floors hcredit.1] at hg
  have htotal := hcredit.2
  exact GoodQP.stepsQ hst hg (by omega) (by omega) (fun q => ⟨q, by omega⟩)
theorem after_good_budget : AfterGoodBudget 5264 :=
  fun floors hcredit pk w Q hQ a top u h => after_good floors hcredit pk w Q hQ a top u h
end SigGolfCandidate.T3M
end
