import SigGolfCandidate.T3M_Expand_LayerBlocks
import SigGolfCandidate.T3M_Expand_Basic

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest chain chainInput shortHash pad64 zero16 header)
open SphincsSecurity (bytesLE bytesLE_length)
open SigGolfCandidate.T3M.Search (DIGITS)
set_option autoImplicit false
theorem chainInput_length' (lay : Layer) (tree leaf i step : Nat) (v : Digest) :
    (chainInput lay tree leaf i step v).length = 64 := by
  simp [chainInput, bytesLE_length, T3.zero16]
theorem wordsOf_chainInput' (lay : Layer) (tree leaf i step : Nat) (v : Digest) :
    wordsOf (pad64 (chainInput lay tree leaf i step v)) =
      [0, 0, (T3.chainHeader lay tree leaf i step).extractLsb' 0 64,
        (T3.chainHeader lay tree leaf i step).extractLsb' 64 64,
        0, 0, v.extractLsb' 0 64, v.extractLsb' 64 64] := by
  rw [pad64_of_aligned _ (by rw [chainInput_length'])]
  exact Keygen.Packed.wordsOf_chainInput lay tree leaf i step v
theorem blocks_chainInput' (lay : Layer) (tree leaf i step : Nat) (v : Digest) :
    (toQ (pad64 (chainInput lay tree leaf i step v))).blocks = 1 := by
  rw [pad64_of_aligned _ (by rw [chainInput_length']), blocks_toQ ⟨by rw [chainInput_length']; omega,
    by rw [chainInput_length']⟩, chainInput_length']
structure ChainCtx (lay tree leaf i : Nat) (t : MachineState) : Prop where
  x5 : t.getReg .x5 = 0
  x8 : t.getReg .x8 = BitVec.ofNat 64 lay
  x9 : t.getReg .x9 = BitVec.ofNat 64 tree
  x18 : t.getReg .x18 = BitVec.ofNat 64 leaf
  x19 : t.getReg .x19 = BitVec.ofNat 64 i
  z0 : t.getMem (BitVec.ofNat 64 CHAIN) = 0
  z8 : t.getMem (BitVec.ofNat 64 (CHAIN + 8)) = 0
def stepRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x20, .x28, .x30]
/-- Pairing stage 1: a chain step writes the header words and `CHAIN+32 .. CHAIN+112` (G: pads, header copy and the
interior output at `CHAIN+32`; F: the pad `CHAIN+32/40`, the output at `CHAIN+48`). -/
def StepW (A : Nat) : Prop := (A = CHAIN + 16 ∨ A = CHAIN + 24) ∨ (CHAIN + 32 ≤ A ∧ A < CHAIN + 112)
theorem ChainCtx.frame {lay tree leaf i : Nat} {t u : MachineState} (h : ChainCtx lay tree leaf i t)
    {l : List Reg} (hl : Reg.x5 ∉ l ∧ Reg.x8 ∉ l ∧ Reg.x9 ∉ l ∧ Reg.x18 ∉ l ∧ Reg.x19 ∉ l) (hr : RegsExcept t u l) (hf : Frame t u StepW) :
    ChainCtx lay tree leaf i u where
  x5 := by rw [hr.get hl.1]; exact h.x5
  x8 := by rw [hr.get hl.2.1]; exact h.x8
  x9 := by rw [hr.get hl.2.2.1]; exact h.x9
  x18 := by rw [hr.get hl.2.2.2.1]; exact h.x18
  x19 := by rw [hr.get hl.2.2.2.2]; exact h.x19
  z0 := by rw [hf.get (by simp only [CHAIN]; omega) (by unfold StepW; simp only [CHAIN]; omega)]; exact h.z0
  z8 := by rw [hf.get (by simp only [CHAIN]; omega) (by unfold StepW; simp only [CHAIN]; omega)]; exact h.z8
theorem not_mem_of_sub {r : Reg} {l l' : List Reg} (hl : ∀ x ∈ l, x ∈ l') (hr : r ∉ l') : r ∉ l :=
  fun hm => hr (hl r hm)
section chain
variable {sk : BitVec 256}
def oneRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x19, .x20, .x21, .x23, .x28, .x29, .x30]
def OneW (lay : T3.Layer) (i W : Nat) (A : Nat) : Prop :=
  StepW A ∨ A = LEAFPK + slotOff lay i ∨ A = LEAFPK + slotOff lay i + 8 ∨ A = W + 48 ∨ A = W + 56
/-- T51: the top chain caps of KMAX (`maxDigit 0 i`; `n4` is unused), lower layers 7. -/
def endpoint (lay : Layer) (i _n4 : Nat) : Nat :=
  if lay = 0 then (if i < 27 then 5 else if i < 48 then 4 else if i < 50 then 6 else 5) else 7
/-- Extra cycles of the cap selection on the top (1030 `j 1158`, KMAX). -/
def endpointExtra (lay : Layer) (i _n4 : Nat) : Nat :=
  if lay = 0 then 1 + SharedRecover.kmaxSteps i else 0
/-- Cycle budget of one chain step: the T51 top G step runs GT (+7 cycles). -/
def stepW (lay : Layer) : Nat := if lay = 0 then 67 else 60
def ChW (lay : T3.Layer) (WC k : Nat) (A : Nat) : Prop :=
  StepW A ∨ (∃ c < k, A = LEAFPK + slotOff lay c ∨ A = LEAFPK + slotOff lay c + 8) ∨
    (∃ c < k, A = WC - 64 * c + 48 ∨ A = WC - 64 * c + 56)
theorem not_ChW_of {lay : T3.Layer} {WC k A : Nat} (hk : k ≤ 58) (h1 : WC + 64 ≤ A) (h2 : A < CHAIN + 16 ∨ CHAIN + 112 ≤ A)
    (h3 : A < LEAFPK ∨ LEAFPK + 16 * 60 ≤ A) : ¬ ChW lay WC k A := by
  unfold ChW StepW
  rintro (h | ⟨c, hc, h | h⟩ | ⟨c, _, h | h⟩) <;> simp only [CHAIN, LEAFPK] at h h2 h3 <;>
    first | omega | (unfold slotOff at h; split_ifs at h <;> omega)
theorem not_ChW_hdr {lay : T3.Layer} {WC k A : Nat} (hW : WC + 64 ≤ LEAFPK) (h : A = LEAFPK + 16 ∨ A = LEAFPK + 24)
    (hk : k ≤ 54) : ¬ ChW lay WC k A := by
  rcases h with h | h
  · unfold ChW StepW
    rintro (h' | ⟨c, hc, h' | h'⟩ | ⟨c, _, h' | h'⟩) <;> simp only [CHAIN, LEAFPK] at h h' hW <;>
      first | omega | (unfold slotOff at h'; split_ifs at h' <;> omega)
  · unfold ChW StepW
    rintro (h' | ⟨c, hc, h' | h'⟩ | ⟨c, _, h' | h'⟩) <;> simp only [CHAIN, LEAFPK] at h h' hW <;>
      first | omega | (unfold slotOff at h'; split_ifs at h' <;> omega)
structure ChainsInv (t0 : MachineState) (lay : Layer) (tree leaf P WC n n4 : Nat) (vals : Nat → Digest)
    (ends : List Digest) (t : MachineState) : Prop where
  pc : t.pc = pcOf 1010
  ctx : ChainCtx lay.val tree leaf ends.length t
  x23 : t.getReg .x23 = BitVec.ofNat 64 (WC - 64 * ends.length)
  slots : ∀ j < ends.length, DigAt t (LEAFPK + slotOff lay j) (ends.getD j 0)
  wvals : ∀ j < ends.length, DigAt t (WC - 64 * j + 48) (vals j)
  regs : RegsExcept t0 t oneRegs
  frame : Frame t0 t (ChW lay WC ends.length)
end chain
end SigGolfCandidate.T3M.Expand

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3
open SigGolfCandidate.T3M.Expand
open SphincsSecurity (bytesLE bytesLE_length)
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC)
open ClaudeWCT
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable {im : Image} [Code im] [BCBlocks.Code im] [PackedBlocks.Code im] {sk : BitVec 256}
theorem tb_halfHash_bind' {β : Type} {s : MachineState} {input : List UInt8} {W : Nat} (high : Bool)
    {f : Digest → T3.M β} {Q : β → MachineState → Prop}
    (hf : fetch im s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (pad64 input))
    (h : ∀ a : BitVec 256, TBSim im sk (writeHash s a) W (f (ClaudeWCT.WCT9.halfOf high a)) Q) :
    TBSim im sk s (8 * (toQ (pad64 input)).blocks + W) (ClaudeWCT.WCT9.halfHash high input >>= f) Q := by
  rw [ClaudeWCT.WCT9.halfHash_eq, bind_assoc]
  simp only [pure_bind]
  unfold TBSim; rw [mrealize_bind, mrealize_publicHash]
  exact Sim.query_bind hf ht0 hv hq h
theorem wordsOf_chainInputW_G {lay : Layer} {i : Nat} (hG : ClaudeWCT.WCT9.isG lay i = true) (tree leaf step : Nat)
    (v : Digest) :
    wordsOf (ClaudeWCT.WCT9.chainInputW lay tree leaf i step v) =
      [v.extractLsb' 0 64, v.extractLsb' 64 64, (chainHeader lay tree leaf i step).extractLsb' 0 64,
        (chainHeader lay tree leaf i step).extractLsb' 64 64, 0, 0, 0, 0] := by
  rw [ClaudeWCT.WCT9.chainInputW_G hG]
  rw [wordsOf_append _ _ (by simp [bytesLE_length, zero16]),
    wordsOf_append _ _ (by simp [bytesLE_length, zero16]),
    wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_zero16, wordsOf_bytesLE16,
    wordsOf_bytesLE16]
  rfl
theorem chainInputW_blocks (lay : Layer) (tree leaf i step : Nat) (v : Digest) :
    (toQ (pad64 (ClaudeWCT.WCT9.chainInputW lay tree leaf i step v))).blocks = 1 := by
  rw [pad64_of_aligned _ (by rw [ClaudeWCT.WCT9.chainInputW_length]),
    blocks_toQ ⟨by rw [ClaudeWCT.WCT9.chainInputW_length]; omega, by rw [ClaudeWCT.WCT9.chainInputW_length]⟩,
    ClaudeWCT.WCT9.chainInputW_length]
/-- The step at which a G chain writes LOW (T51 top: `gTerm`; lower: 6). -/
def gTermL (lay : Layer) (i : Nat) : Nat := if lay = 0 then SharedRecover.gTerm i else SigGolfCandidate.T3.maxDigit lay i - 1
/-- Witness stack: on a G chain (lower odd, or top even `≤ 50`) the step keeps the high half exactly when it is not the
step `gTermL` (T51: `maxDigit - 1`; top chain 0 keeps the high half on every step). -/
theorem gHigh_eq {lay : Layer} {i m : Nat} (hG : ClaudeWCT.WCT9.isG lay i = true)
    (hm : m < SigGolfCandidate.T3.maxDigit lay i) :
    ClaudeWCT.WCT9.chainHigh lay i m = decide (m ≠ gTermL lay i) := by
  apply Bool.eq_iff_iff.mpr
  rw [ClaudeWCT.WCT9.chainHigh_eq_true, decide_eq_true_iff]
  rcases ClaudeWCT.WCT9.isG_eq_true.mp hG with ⟨hl, hi⟩ | ⟨hl, hi, hi50⟩
  · have hmd : SigGolfCandidate.T3.maxDigit lay i = 7 := by simp [SigGolfCandidate.T3.maxDigit, hl]
    have hg : gTermL lay i = 6 := by simp [gTermL, hl, hmd]
    rw [hmd] at hm
    rw [hg]
    constructor
    · rintro (⟨_, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ | ⟨h, _, _⟩)
      · omega
      · omega
      · exact absurd h hl
    · intro h; exact Or.inl ⟨hl, Or.inr ⟨hi, by omega⟩⟩
  · subst hl
    have hg : gTermL 0 i = SharedRecover.gTerm i := by simp [gTermL]
    rw [hg]
    unfold SharedRecover.gTerm
    constructor
    · rintro (⟨h, _⟩ | ⟨_, _, h⟩)
      · exact absurd rfl h
      · by_cases h0 : i = 0
        · rw [if_pos h0]
          have : SigGolfCandidate.T3.maxDigit 0 i = 5 := by subst h0; rfl
          omega
        · rw [if_neg h0]; omega
    · intro h
      refine Or.inr ⟨rfl, ⟨hi, hi50⟩, ?_⟩
      by_cases h0 : i = 0
      · exact Or.inr h0
      · rw [if_neg h0] at h; exact Or.inl (by omega)

/-- Witness stack: one chain step (loop head 1031, header 1032..1040, the step block 49300..49337 and, on the F
path, the C3 tail) computes `halfHash (chainHigh) (chainInputW)`; at most 60 instructions + HASH. -/
theorem chain_step (lay : Layer) (tree leaf i st e : Nat)
    (hr : tree * 2 ^ T3.height lay + leaf < 2 ^ 31) (hf : leaf < 2 ^ T3.height lay) (hst : st < e) (he : e ≤ 7)
    (hcap : e ≤ SigGolfCandidate.T3.maxDigit lay i)
    (hi : i < 64) (hiT : lay = 0 → i ≤ 50) (v : Digest) (t : MachineState) (hpc : t.pc = pcOf 1031)
    (hc : ChainCtx lay.val tree leaf i t) (h20 : t.getReg .x20 = BitVec.ofNat 64 st)
    (h21 : t.getReg .x21 = BitVec.ofNat 64 e) (hv : DigAt t (CHAIN + 48) v) :
    TBSim im sk t (stepW lay) (ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i st)
        (ClaudeWCT.WCT9.chainInputW lay tree leaf i st v))
      (fun v' u => u.pc = pcOf 1031 ∧ u.getReg .x20 = BitVec.ofNat 64 (st + 1) ∧ u.getReg .x21 = BitVec.ofNat 64 e ∧
        ChainCtx lay.val tree leaf i u ∧ DigAt u (CHAIN + 48) v' ∧ RegsExcept t u stepRegs ∧ Frame t u StepW) := by
  have hlay := lay.isLt
  obtain ⟨t1, s1, p1, r1, f1⟩ := rl1031_spec (im := im) t hpc st e (by omega) (by omega) h20 h21
  rw [if_neg (by omega)] at p1
  obtain ⟨t2, s2, p2, a28, m16, m24, r2, f2⟩ := rl1032_spec (im := im) t1 p1 lay tree leaf i st hr hf hi (by omega)
    (by rw [r1.get (by simp)]; exact hc.x8) (by rw [r1.get (by simp)]; exact hc.x19)
    (by rw [r1.get (by simp)]; exact hc.x9) (by rw [r1.get (by simp)]; exact hc.x18)
    (by rw [r1.get (by simp)]; exact h20)
  have f12 : Frame t t2 (fun A => A = CHAIN + 16 ∨ A = CHAIN + 24) := (f1.trans f2).mono (fun A _ h => by
    rcases h with h | h; exact h.elim; exact h)
  have r12 : RegsExcept t t2 [.x6, .x7, .x10, .x11, .x12, .x28, .x30] := (r1.trans r2).mono (by simp)
  have g2 : ∀ r, r ∉ stepRegs → t2.getReg r = t.getReg r := fun r hr =>
    r12.get (not_mem_of_sub (by simp [stepRegs]) hr)
  obtain ⟨u0, s0, p0, r0, f0⟩ := sel_spec (im := im) t2 p2 lay.val (by omega)
    (by rw [g2 _ (by simp [stepRegs])]; exact hc.x8)
  have g19 : u0.getReg .x19 = BitVec.ofNat 64 i := by
    rw [r0.get (by simp), g2 _ (by simp [stepRegs])]; exact hc.x19
  have hK := expHdrK_le lay
  have fin_frame : ∀ {w : MachineState}, Frame t2 w (fun A => CHAIN + 32 ≤ A ∧ A < CHAIN + 112) →
      Frame t w StepW := fun hw => (f12.trans hw).mono (fun A _ h => by
        unfold StepW; rcases h with h | h
        · exact Or.inl h
        · exact Or.inr h)
  rw [show ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i st) (ClaudeWCT.WCT9.chainInputW lay tree leaf i st v) =
    (ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i st) (ClaudeWCT.WCT9.chainInputW lay tree leaf i st v)
      >>= pure) by rw [bind_pure]]
  by_cases hGb : ClaudeWCT.WCT9.isG lay i = true
  · -- G path: `value | header | 0 | 0` at CHAIN+48
    obtain ⟨u, k1, su, hk1, upc, u6, u7, ur, uf⟩ : ∃ u k1, Steps im t2 k1 k1 u ∧ expHdrK lay + k1 + 23 ≤ stepW lay ∧
        u.pc = pcOf 49316 ∧ u.getReg .x6 = BitVec.ofNat 64 (gTermL lay i) ∧
        u.getReg .x7 = (T3.chainHeader lay tree leaf i st).extractLsb' 64 64 ∧
        RegsExcept t2 u [.x6, .x7] ∧ Frame t2 u (fun _ => False) := by
      rcases ClaudeWCT.WCT9.isG_eq_true.mp hGb with ⟨hl, hi2⟩ | ⟨hl, hi2, hi52⟩
      · have hl' : lay.val ≠ 0 := fun h => hl (Fin.ext h)
        rw [if_neg hl'] at p0
        obtain ⟨u1, q1, p1', r1', f1'⟩ := lsel_spec (im := im) u0 p0 i g19
        rw [if_neg (by omega)] at p1'
        obtain ⟨u2, q2, p2', x6', x7', r2', f2'⟩ := lg_spec (im := im) u1 p1'
        refine ⟨u2, 7, s0.trans (q1.trans q2), by unfold stepW; rw [if_neg hl]; have := expHdrK_le lay; unfold expHdrK at this ⊢; split_ifs at this ⊢ <;> omega, p2', ?_, ?_, ?_, ?_⟩
        · rw [x6']; simp [gTermL, SigGolfCandidate.T3.maxDigit, hl]
        · rw [x7', Keygen.PackedBlocks.source_high_actual lay tree leaf i st hr hf hi (by omega)]
        · exact ((r0.trans r1').trans r2').mono (by simp)
        · exact ((f0.trans f1').trans f2').mono (fun A _ h => by simp_all)
      · have hl' : lay.val = 0 := by rw [hl]; rfl
        rw [if_pos hl'] at p0
        obtain ⟨u1, q1, p1', r1', f1'⟩ := tsel_spec (im := im) u0 p0 i (by omega) g19
        rw [if_pos hi2] at p1'
        obtain ⟨u2, q2, p2', r2', f2'⟩ := tle_spec (im := im) u1 p1' i (by omega)
          (by rw [r1'.get (by simp)]; exact g19)
        rw [if_neg (by omega)] at p2'
        obtain ⟨u3, q3, p3', x6', x7', r3', f3'⟩ := tcap_spec (im := im) u2 p2' i (by omega) hi2
          (by rw [r2'.get (by simp), r1'.get (by simp)]; exact g19)
          (by rw [r2'.get (by simp), r1'.get (by simp), r0.get (by simp)]; exact a28)
        have hK0 : expHdrK lay = 25 := by unfold expHdrK; rw [if_pos hl']
        refine ⟨u3, _, ((s0.trans q1).trans q2).trans q3, by rw [hK0]; unfold stepW gtK; rw [if_pos hl]; split_ifs <;> omega,
          p3', ?_, ?_, ?_, ?_⟩
        · rw [x6', hl]; simp [gTermL]
        · have f02 : Frame t2 u2 (fun _ => False) :=
            ((f0.trans f1').trans f2').mono (fun A _ h => by simp_all)
          rw [x7', f02.get (by decide) (by simp), m24]
        · exact (((r0.trans r1').trans r2').trans r3').mono (by simp)
        · exact (((f0.trans f1').trans f2').trans f3').mono (fun A _ h => by simp_all)
    have g1 : ∀ r, r ∉ [Reg.x6, .x7] → u.getReg r = t2.getReg r := fun r hr => ur.get hr
    have hT : gTermL lay i < 2 ^ 63 := by
      unfold gTermL SharedRecover.gTerm SigGolfCandidate.T3.maxDigit; split_ifs <;> omega
    obtain ⟨u2, su2, u2pc, u210, u211, u212, u264, u272, u280, u288, u296, u2104, u2r, u2f⟩ :=
      g_spec (im := im) u upc st (gTermL lay i) _ (by omega) hT u6 u7
        (by rw [g1 _ (by simp), r12.get (by simp)]; exact h20) (by rw [g1 _ (by simp)]; exact a28)
    have f02 : Frame t2 u2 (fun A => CHAIN + 64 ≤ A ∧ A < CHAIN + 112) :=
      (uf.trans u2f).mono (fun A _ h => by rcases h with h | h <;> simp_all)
    have r02 : RegsExcept t2 u2 [.x6, .x7, .x10, .x11, .x12, .x30] := (ur.trans u2r).mono (by simp)
    have v2 := (hv.frame f12 (by decide) (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega)).frame f02
      (by decide) (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega)
    have hq : hashInput u2 = toQ (pad64 (ClaudeWCT.WCT9.chainInputW lay tree leaf i st v)) := by
      have hl := ClaudeWCT.WCT9.chainInputW_length lay tree leaf i st v
      rw [pad64_of_aligned _ (by rw [hl])]
      refine hashInput_toQ u2 _ 0 (CHAIN + 48) hl u210 (by decide) (by decide) u211 (by decide) ?_
      rw [wordsOf_chainInputW_G hGb, readWords_eight]
      rw [show CHAIN + 48 + 8 = CHAIN + 56 from rfl, show CHAIN + 48 + 16 = CHAIN + 64 from rfl,
        show CHAIN + 48 + 24 = CHAIN + 72 from rfl, show CHAIN + 48 + 32 = CHAIN + 80 from rfl,
        show CHAIN + 48 + 40 = CHAIN + 88 from rfl, show CHAIN + 48 + 48 = CHAIN + 96 from rfl,
        show CHAIN + 48 + 56 = CHAIN + 104 from rfl]
      rw [v2.1, v2.2, u264, u272, u280, u288, u296, u2104, uf.get (A := CHAIN + 16) (by decide) (by simp), m16]
    have hvalid : hashArgumentsValid u2 = true := by
      by_cases hm6 : st = gTermL lay i
      · rw [if_pos hm6] at u212
        exact hashArgs_const u2 (CHAIN + 48) 64 (CHAIN + 48) u210 u211 u212 (by decide) (by decide) (by decide)
          (by decide) (by decide)
      · rw [if_neg hm6] at u212
        exact hashArgs_const u2 (CHAIN + 48) 64 (CHAIN + 32) u210 u211 u212 (by decide) (by decide) (by decide)
          (by decide) (by decide)
    have h5' : u2.getReg .x5 = 0 := by rw [r02.get (by simp), g2 _ (by simp [stepRegs])]; exact hc.x5
    refine (TBSim.steps (((s1.trans s2).trans su).trans su2)
      (tb_halfHash_bind' (im := im) (W := 2) _ (fetch_49328 (im := im) u2 u2pc) h5' hvalid hq (fun a => ?_))).mono
      (by rw [chainInputW_blocks]; split_ifs <;> omega) (fun _ _ h => h)
    have hw20 : (writeHash u2 a).getReg .x20 = BitVec.ofNat 64 st := by
      rw [getReg_writeHash, r02.get (by simp), r12.get (by simp)]
      exact h20
    obtain ⟨w, sw, wpc, w20, wr, wf⟩ := gtail_spec (im := im) (writeHash u2 a)
      (by rw [pc_writeHash, u2pc, pcOf_add4]) st hw20
    have hB : ∀ B, u2.getReg .x12 = BitVec.ofNat 64 B → B = CHAIN + 32 ∨ B = CHAIN + 48 →
        Frame u2 (writeHash u2 a) (fun A => CHAIN + 32 ≤ A ∧ A < CHAIN + 112) := fun B h12 hB =>
      (Frame.writeHash u2 a B h12 (by rcases hB with rfl | rfl <;> decide)).mono
        (fun A _ h => by simp only [CHAIN] at hB ⊢; omega)
    have hwf : Frame u2 (writeHash u2 a) (fun A => CHAIN + 32 ≤ A ∧ A < CHAIN + 112) := by
      by_cases hm6 : st = gTermL lay i
      · rw [if_pos hm6] at u212; exact hB _ u212 (Or.inr rfl)
      · rw [if_neg hm6] at u212; exact hB _ u212 (Or.inl rfl)
    have hval : DigAt (writeHash u2 a) (CHAIN + 48)
        (ClaudeWCT.WCT9.halfOf (ClaudeWCT.WCT9.chainHigh lay i st) a) := by
      rw [gHigh_eq hGb (by omega)]
      by_cases hm6 : st = gTermL lay i
      · rw [if_pos hm6] at u212
        rw [decide_eq_false (fun h => h hm6)]
        exact DigAt.writeHash_lo u2 a (CHAIN + 48) u212 (by decide)
      · rw [if_neg hm6] at u212
        rw [decide_eq_true hm6]
        exact DigAt.writeHash_hi u2 a (CHAIN + 32) u212 (by decide)
    have fall : Frame t w StepW := fin_frame (((f02.trans hwf).trans wf).mono (fun A _ h => by
      simp only [CHAIN] at h ⊢; rcases h with (h | h) | h <;> first | omega | exact h.elim))
    have rall : RegsExcept t w stepRegs := fun r hr => by
      have rr : RegsExcept u2 (writeHash u2 a) [] := fun r _ => getReg_writeHash u2 a r
      rw [((r02.trans rr).trans wr).get (by simp [stepRegs] at hr ⊢; tauto), g2 r hr]
    refine TBSim.steps (W := 0) sw (TBSim.pure ⟨wpc, w20, ?_, ?_, hval.frame wf (by decide) (by simp) (by simp),
      rall, fall⟩)
    · rw [rall.get (by simp [stepRegs])]; exact h21
    · exact hc.frame (l := stepRegs) (by simp [stepRegs]) rall fall
  · -- F path: `T3.chainInput` at CHAIN
    have hGf : ClaudeWCT.WCT9.isG lay i = false := by simpa using hGb
    rw [ClaudeWCT.WCT9.chainInputW_F hGf]
    obtain ⟨u1, k1, su1, hk1, u1pc, u1r, u1f⟩ : ∃ u1 k1, Steps im t2 k1 k1 u1 ∧
        expHdrK lay + k1 + trXE lay.val i st ≤ 43 ∧ u1.pc = pcOf 49331 ∧ RegsExcept t2 u1 [.x6, .x7] ∧
        Frame t2 u1 (fun _ => False) := by
      by_cases hl0 : lay.val = 0
      · rw [if_pos hl0] at p0
        have hl : lay = 0 := Fin.ext hl0
        have hK0 : expHdrK lay = 25 := by unfold expHdrK; rw [if_pos hl0]
        obtain ⟨u1, q1, p1', r1', f1'⟩ := tsel_spec (im := im) u0 p0 i (by omega) g19
        by_cases hi2 : i % 2 = 0
        · rw [if_pos hi2] at p1'
          obtain ⟨u2, q2, p2', r2', f2'⟩ := tle_spec (im := im) u1 p1' i (by omega)
            (by rw [r1'.get (by simp)]; exact g19)
          exact absurd (ClaudeWCT.WCT9.isG_eq_true.mpr (Or.inr ⟨hl, hi2, hiT hl⟩)) hGb
        · rw [if_neg hi2] at p1'
          have hX : trXE lay.val i st = 2 := by unfold trXE; rw [if_pos (by omega)]
          exact ⟨u1, 5, s0.trans q1, by omega, p1', (r0.trans r1').mono (by simp),
            (f0.trans f1').mono (fun A _ h => by simp_all)⟩
      · rw [if_neg hl0] at p0
        obtain ⟨u1, q1, p1', r1', f1'⟩ := lsel_spec (im := im) u0 p0 i g19
        have hi2 : i % 2 = 0 := by
          by_contra h
          exact hGb (ClaudeWCT.WCT9.isG_eq_true.mpr (Or.inl ⟨fun h' => hl0 (by rw [h']; rfl), by omega⟩))
        rw [if_pos hi2] at p1'
        have := trXE_le lay.val i st
        exact ⟨u1, 4, s0.trans q1, by omega, p1', (r0.trans r1').mono (by simp),
          (f0.trans f1').mono (fun A _ h => by simp_all)⟩
    obtain ⟨u2, su2, u2pc, u210, u211, u212, u232, u240, u2r, u2f⟩ :=
      f_spec (im := im) u1 u1pc (by rw [u1r.get (by simp)]; exact a28)
    have f02 : Frame t2 u2 (fun A => A = CHAIN + 32 ∨ A = CHAIN + 40) :=
      (u1f.trans u2f).mono (fun A _ h => by rcases h with h | h <;> simp_all)
    have r02 : RegsExcept t2 u2 [.x6, .x7, .x10, .x11, .x12] := (u1r.trans u2r).mono (by simp)
    have v2 := (hv.frame f12 (by decide) (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega)).frame f02
      (by decide) (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega)
    have z0 : u2.getMem (BitVec.ofNat 64 CHAIN) = 0 := by
      rw [f02.get (by decide) (by simp only [CHAIN]; omega), f12.get (by decide) (by simp only [CHAIN]; omega)]
      exact hc.z0
    have z8 : u2.getMem (BitVec.ofNat 64 (CHAIN + 8)) = 0 := by
      rw [f02.get (by decide) (by simp only [CHAIN]; omega), f12.get (by decide) (by simp only [CHAIN]; omega)]
      exact hc.z8
    have hq : hashInput u2 = toQ (pad64 (chainInput lay tree leaf i st v)) := by
      refine hashInput_toQ u2 _ 0 CHAIN (by rw [pad64_of_aligned _ (by rw [chainInput_length']), chainInput_length'])
        u210 (by simp only [CHAIN]) (by simp only [CHAIN]; omega) u211 (by norm_num) ?_
      rw [readWords_eight, wordsOf_chainInput', z0, z8,
        f02.get (A := CHAIN + 16) (by decide) (by simp only [CHAIN]; omega),
        f02.get (A := CHAIN + 24) (by decide) (by simp only [CHAIN]; omega), m16, m24, u232, u240, v2.1,
        show CHAIN + 48 + 8 = CHAIN + 56 from rfl, v2.2]
    have hvalid : hashArgumentsValid u2 = true :=
      hashArgs_const u2 CHAIN 64 (CHAIN + 48) u210 u211 u212 (by simp only [CHAIN]) (by norm_num)
        (by simp only [CHAIN]; omega) (by simp only [CHAIN]) (by simp only [CHAIN]; omega)
    have h5' : u2.getReg .x5 = 0 := by rw [r02.get (by simp), g2 _ (by simp [stepRegs])]; exact hc.x5
    refine (TBSim.steps (((s1.trans s2).trans su1).trans su2)
      (tb_halfHash_bind' (im := im) (W := 2 + trXE lay.val i st) _ (fetch_49336 (im := im) u2 u2pc) h5' hvalid hq
        (fun a => ?_))).mono
      (by rw [blocks_chainInput']; unfold stepW; split_ifs <;> omega) (fun _ _ h => h)
    have gw : ∀ r, r ∉ stepRegs → (writeHash u2 a).getReg r = t.getReg r := fun r hr => by
      rw [getReg_writeHash, r02.get (by simp [stepRegs] at hr ⊢; tauto), g2 r hr]
    have p3 : (writeHash u2 a).pc = pcOf 49337 := by rw [pc_writeHash, u2pc, pcOf_add4]
    have hlo := DigAt.writeHash_lo u2 a (CHAIN + 48) u212 (by simp only [CHAIN]; omega)
    have hhi : DigAt (writeHash u2 a) (CHAIN + 64) (a.extractLsb' 128 128) :=
      DigAt.writeHash_hi u2 a (CHAIN + 48) u212 (by simp only [CHAIN]; omega)
    obtain ⟨w, s4, p4, w20, hd, r4, f4⟩ := rl1047_spec (im := im) (writeHash u2 a) p3 lay i st (by omega) (by omega)
      hGf (by rw [gw _ (by simp [stepRegs])]; exact hc.x8) (by rw [gw _ (by simp [stepRegs])]; exact hc.x19)
      (by rw [getReg_writeHash, r02.get (by simp), r12.get (by simp)]; exact h20) _ _ hlo hhi
    have fw := Frame.writeHash u2 a (CHAIN + 48) u212 (by simp only [CHAIN]; omega)
    have fall : Frame t w StepW := fin_frame (((f02.trans fw).trans f4).mono (fun A _ h => by
      simp only [CHAIN] at h ⊢; omega))
    have rall : RegsExcept t w stepRegs := fun r hr => by
      rw [r4.get (not_mem_of_sub (by simp [stepRegs]) hr), gw r hr]
    refine TBSim.steps (W := 0) s4 (TBSim.pure ⟨p4, w20, ?_, ?_, ?_, rall, fall⟩)
    · rw [rall.get (by simp [stepRegs])]; exact h21
    · exact hc.frame (l := stepRegs) (by simp [stepRegs]) rall fall
    · unfold ClaudeWCT.WCT9.halfOf; exact hd

theorem chain_loop (lay : Layer) (tree leaf i d e : Nat)
    (hr : tree * 2 ^ T3.height lay + leaf < 2 ^ 31) (hf : leaf < 2 ^ T3.height lay) (hd : d ≤ e) (he : e ≤ 7)
    (hcap : e ≤ SigGolfCandidate.T3.maxDigit lay i)
    (hi : i < 64) (hiT : lay = 0 → i ≤ 50) (v : Digest) (t : MachineState) (hpc : t.pc = pcOf 1031)
    (hc : ChainCtx lay.val tree leaf i t) (h20 : t.getReg .x20 = BitVec.ofNat 64 d)
    (h21 : t.getReg .x21 = BitVec.ofNat 64 e) (hv : DigAt t (CHAIN + 48) v) :
    TBSim im sk t ((e - d) * stepW lay + 1) (ClaudeWCT.WCT9.chainW lay tree leaf i d (e - d) v)
      (fun v' u => u.pc = pcOf 1049 ∧ u.getReg .x21 = BitVec.ofNat 64 e ∧
        ChainCtx lay.val tree leaf i u ∧ DigAt u (CHAIN + 48) v' ∧ RegsExcept t u stepRegs ∧ Frame t u StepW) := by
  let Inv : Nat → Digest → MachineState → Prop := fun j w u =>
    u.pc = pcOf 1031 ∧ u.getReg .x20 = BitVec.ofNat 64 (d + j) ∧ u.getReg .x21 = BitVec.ofNat 64 e ∧
      ChainCtx lay.val tree leaf i u ∧ DigAt u (CHAIN + 48) w ∧ RegsExcept t u stepRegs ∧ Frame t u StepW
  have hloop := TBSim.foldlM_range' (image := im) (sk := sk) d (e - d)
    (fun value step => ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i step) (ClaudeWCT.WCT9.chainInputW lay tree leaf i step value)) v Inv (stepW lay)
    (fun j hj w u hu => by
      obtain ⟨p, x20, x21, cc, dv, rr, ff⟩ := hu
      refine (chain_step (im := im) lay tree leaf i (d + j) e hr hf (by omega) he hcap hi hiT w u p cc x20 x21 dv).mono le_rfl ?_
      rintro w' u' ⟨p', y20, y21, cc', dv', rr', ff'⟩
      refine ⟨p', by rw [y20]; congr 1, y21, cc', dv', ?_, ?_⟩
      · exact (rr.trans rr').mono (fun r hr => by
          rcases List.mem_append.mp hr with h | h <;> exact h)
      · exact (ff.trans ff').mono (fun A _ h => by rcases h with h | h <;> exact h))
    (s := t) ⟨hpc, by simpa using h20, h21, hc, hv, RegsExcept.refl _ _, Frame.refl _ _⟩
  have hprog : ClaudeWCT.WCT9.chainW lay tree leaf i d (e - d) v = ((List.range' d (e - d)).foldlM
      (fun value step => ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i step) (ClaudeWCT.WCT9.chainInputW lay tree leaf i step value)) v >>= pure) := by
    rw [bind_pure]; rfl
  rw [hprog]
  refine (TBSim.bind (W₂ := 1) hloop (fun w u hu => ?_)).mono (by omega) (fun _ _ h => h)
  obtain ⟨p, x20, x21, cc, dv, rr, ff⟩ := hu
  obtain ⟨u1, s1, p1, r1, f1⟩ := rl1031_spec (im := im) u p (d + (e - d)) e (by omega) (by omega) x20 x21
  rw [if_pos (by omega)] at p1
  exact (TBSim.steps s1 (TBSim.pure ⟨p1, by rw [r1.get (by simp)]; exact x21, cc.frame (l := []) (by simp) r1
      (f1.mono (fun _ _ h => h.elim)), dv.frame f1 (by simp only [CHAIN]; omega) (by simp) (by simp),
    (rr.trans r1).mono (by simp), (ff.trans f1).mono (fun A _ h => by rcases h with h | h; exact h; exact h.elim)⟩)).mono
    (by omega) (fun _ _ h => h)

theorem endpoint_top (i n4 : Nat) : SigGolfCandidate.T3.maxDigit 0 i = endpoint 0 i n4 := by
  simp [SigGolfCandidate.T3.maxDigit, endpoint]

theorem rl_one (lay : Layer) (tree leaf i d P W n n4 : Nat)
    (hr : tree * 2 ^ T3.height lay + leaf < 2 ^ 31) (hf : leaf < 2 ^ T3.height lay) (hi : i < n) (hn : n ≤ 58)
    (hiT : lay = 0 → i ≤ 50)
    (hn4 : n4 ≤ n) (hP : 0x7000 ≤ P) (hPi : P + 16 * i + 16 ≤ 0x7000 + 5616) (hP8 : P % 8 = 0)
    (hW8 : W % 8 = 0) (hW : 64 ≤ W) (hW' : W + 64 ≤ 0x7000) (hd : d ≤ (endpoint lay i n4))
    (hcap : endpoint lay i n4 ≤ SigGolfCandidate.T3.maxDigit lay i)
    (v : Digest) (t : MachineState) (hpc : t.pc = pcOf 1010)
    (hc : ChainCtx lay.val tree leaf i t) (h26 : t.getReg .x26 = BitVec.ofNat 64 n)
    (h27 : t.getReg .x27 = BitVec.ofNat 64 n4) (h16 : t.getReg .x16 = BitVec.ofNat 64 P)
    (h23 : t.getReg .x23 = BitVec.ofNat 64 W) (hv : DigAt t (P + 16 * i) v)
    (hdig : t.getByte (BitVec.ofNat 64 (DIGITS + i)) = BitVec.ofNat 8 d) :
    TBSim im sk t 461 (ClaudeWCT.WCT9.chainW lay tree leaf i d ((endpoint lay i n4) - d) v)
      (fun v' u => u.pc = pcOf 1010 ∧ u.getReg .x19 = BitVec.ofNat 64 (i + 1) ∧
        u.getReg .x23 = BitVec.ofNat 64 (W - 64) ∧ ChainCtx lay.val tree leaf (i + 1) u ∧
        DigAt u (LEAFPK + slotOff lay i) v' ∧ DigAt u (W + 48) v ∧ RegsExcept t u oneRegs ∧ Frame t u (OneW lay i W)) := by
  have hlay := lay.isLt
  set e := (endpoint lay i n4) with he
  have he7 : e ≤ 7 := by rw [he]; unfold endpoint; split_ifs <;> omega
  obtain ⟨t1, s1, p1, r1, f1⟩ := rl1010_spec (im := im) t hpc i n (by omega) (by omega) hc.x19 h26
  rw [if_neg (by omega)] at p1
  obtain ⟨t2, s2, p2, c48, c56, w48, w56, x23, x28, r2, f2⟩ := rl1011_spec (im := im) t1 p1 i P W hP hPi hP8 hW8 hW hW'
    (by rw [r1.get (by simp)]; exact hc.x19) (by rw [r1.get (by simp)]; exact h16)
    (by rw [r1.get (by simp)]; exact h23)
  have f12 : Frame t t2 (fun A => A = CHAIN + 48 ∨ A = CHAIN + 56 ∨ A = W + 48 ∨ A = W + 56) :=
    (f1.trans f2).mono (fun A _ h => by rcases h with h | h; exact h.elim; exact h)
  have hb2 : t2.getByte (BitVec.ofNat 64 (DIGITS + i)) = BitVec.ofNat 8 d := by
    rw [Frame.getByte f12 (by simp only [DIGITS]; omega) (by simp only [DIGITS, CHAIN]; omega), hdig]
  obtain ⟨t3, s3, p3, x20, r3, f3⟩ := rl1027_spec (im := im) t2 p2 i d (by omega) (by omega) x28 hb2
  obtain ⟨t4, s4, p4, x21, r4, f4⟩ := rl1028_spec (im := im) t3 p3 lay.val (by omega)
    (by rw [r3.get (by simp), r2.get (by simp), r1.get (by simp)]; exact hc.x8)
  obtain ⟨t5, s5, p5, x21', r5, f5⟩ : ∃ t5, Steps im t4 (endpointExtra lay i n4) (endpointExtra lay i n4) t5 ∧
      t5.pc = pcOf 1031 ∧ t5.getReg .x21 = BitVec.ofNat 64 e ∧ RegsExcept t4 t5 [.x21, .x28] ∧
      Frame t4 t5 (fun _ => False) := by
    have hl0 : lay.val = 0 ↔ lay = 0 := by simp
    by_cases hl : lay = 0
    · rw [if_pos (hl0.mpr hl)] at p4
      obtain ⟨ta, qa, pa, ra, fa⟩ := rl1030_spec (im := im) t4 p4
      have rr := (((r1.trans r2).trans r3).trans r4).trans ra
      obtain ⟨tb, qb, pb, xb, rb, fb⟩ := rl1158_spec (im := im) ta pa i (by omega)
        (by rw [rr.get (by simp)]; exact hc.x19)
      refine ⟨tb, ?_, pb, ?_, ?_, ?_⟩
      · simpa only [endpointExtra, if_pos hl] using qa.trans qb
      · rw [xb, he, hl, ← endpoint_top i n4]
      · exact (ra.trans rb).mono (by simp)
      · exact (fa.trans fb).mono (by simp)
    · rw [if_neg (fun hv => hl (hl0.mp hv))] at p4
      exact ⟨t4, by simpa [endpointExtra, hl] using Steps.refl t4, p4,
        by simpa [he, endpoint, hl] using x21, RegsExcept.refl _ _, Frame.refl _ _⟩
  have f15 : Frame t t5 (fun A => A = CHAIN + 48 ∨ A = CHAIN + 56 ∨ A = W + 48 ∨ A = W + 56) :=
    (((f12.trans f3).trans f4).trans f5).mono (fun A _ h => by
      rcases h with ((h | h) | h) | h
      · exact h
      · exact h.elim
      · exact h.elim
      · exact h.elim)
  have r15 : RegsExcept t t5 ([] ++ [.x6, .x7, .x23, .x28, .x29, .x30] ++ [.x20] ++ [.x21] ++ [.x21, .x28]) :=
    (((r1.trans r2).trans r3).trans r4).trans r5
  have g5 : ∀ r, r ∉ [Reg.x6, .x7, .x20, .x21, .x23, .x28, .x29, .x30] → t5.getReg r = t.getReg r :=
    fun r hr => r15.get (fun hm => hr (by simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢; tauto))
  have hc5 : ChainCtx lay.val tree leaf i t5 :=
    { x5 := by rw [g5 _ (by simp)]; exact hc.x5
      x8 := by rw [g5 _ (by simp)]; exact hc.x8
      x9 := by rw [g5 _ (by simp)]; exact hc.x9
      x18 := by rw [g5 _ (by simp)]; exact hc.x18
      x19 := by rw [g5 _ (by simp)]; exact hc.x19
      z0 := by rw [f15.get (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega)]; exact hc.z0
      z8 := by rw [f15.get (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega)]; exact hc.z8 }
  have hv5 : DigAt t5 (CHAIN + 48) v := by
    constructor
    · rw [f5.get (by simp only [CHAIN]; omega) (by simp), f4.get (by simp only [CHAIN]; omega) (by simp),
        f3.get (by simp only [CHAIN]; omega) (by simp), c48, f1.get (by omega) (by simp)]; exact hv.1
    · rw [f5.get (by simp only [CHAIN]; omega) (by simp), f4.get (by simp only [CHAIN]; omega) (by simp),
        f3.get (by simp only [CHAIN]; omega) (by simp), c56, f1.get (by omega) (by simp)]; exact hv.2
  have x20' : t5.getReg .x20 = BitVec.ofNat 64 d := by rw [r5.get (by simp), r4.get (by simp)]; exact x20
  have hloop := chain_loop (im := im) (sk := sk) lay tree leaf i d e hr hf hd he7 hcap (by omega) hiT v t5 p5 hc5 x20' x21' hv5
  have hprog : ClaudeWCT.WCT9.chainW lay tree leaf i d (e - d) v =
      (ClaudeWCT.WCT9.chainW lay tree leaf i d (e - d) v >>= pure) := by rw [bind_pure]
  rw [hprog]
  have total_cost : (1 + 16 + 1 + 2 + endpointExtra lay i n4) + ((e - d) * stepW lay + 1 + 17) ≤ 461 := by
    rw [he]; unfold endpointExtra endpoint stepW SharedRecover.kmaxSteps
    split_ifs <;> omega
  refine (TBSim.steps (((((s1.trans s2).trans s3).trans s4).trans s5)) (TBSim.bind (W₂ := 17) hloop
    (fun v' u hu => ?_))).mono (by
      simpa only [Nat.add_assoc] using total_cost) (fun _ _ h => h)
  obtain ⟨pu, u21, cu, du, ru, fu⟩ := hu
  obtain ⟨u2, q2, pu2, z28, ry2, fy2⟩ := rl1049_spec (im := im) u pu lay i (by omega) cu.x8 cu.x19
  have hslot8 : slotOff lay i % 8 = 0 := by unfold slotOff; split_ifs <;> omega
  have hslot : LEAFPK + slotOff lay i + 16 ≤ 2 ^ 24 := by unfold slotOff; simp only [LEAFPK]; split_ifs <;> omega
  obtain ⟨u3, q3, pu3, w19, m0, m8, ry3, fy3⟩ := rl1052_spec (im := im) u2 pu2 i (slotOff lay i) hslot8 hslot z28
    (by rw [ry2.get (by simp)]; exact cu.x19)
  have fy12 : Frame u u2 (fun _ => False) := fy2
  have hslotC : ∀ A, (A = LEAFPK + slotOff lay i ∨ A = LEAFPK + slotOff lay i + 8) → ¬ StepW A := by
    intro A hA hS; unfold StepW at hS; unfold slotOff at hA; simp only [LEAFPK, CHAIN] at hA hS; split_ifs at hA <;> omega
  refine (TBSim.steps (q2.trans q3) (TBSim.pure ⟨pu3, w19, ?_, ?_, ?_, ?_, ?_, ?_⟩)).mono
    (by unfold slK; split_ifs <;> omega) (fun _ _ h => h)
  · rw [ry3.get (by simp), ry2.get (by simp), ru.get (by simp [stepRegs]),
      r5.get (by simp), r4.get (by simp), r3.get (by simp)]; exact x23
  · refine
      { x5 := by rw [ry3.get (by simp), ry2.get (by simp)]; exact cu.x5
        x8 := by rw [ry3.get (by simp), ry2.get (by simp)]; exact cu.x8
        x9 := by rw [ry3.get (by simp), ry2.get (by simp)]; exact cu.x9
        x18 := by rw [ry3.get (by simp), ry2.get (by simp)]; exact cu.x18
        x19 := w19
        z0 := ?_, z8 := ?_ } <;>
    · rw [fy3.get (by simp only [CHAIN]; omega) (by unfold slotOff; simp only [LEAFPK, CHAIN]; split_ifs <;> omega),
        fy12.get (by simp only [CHAIN]; omega) (by simp)]
      first | exact cu.z0 | exact cu.z8
  · constructor
    · rw [m0, fy12.get (by simp only [CHAIN]; omega) (by simp)]; exact du.1
    · rw [m8, fy12.get (by simp only [CHAIN]; omega) (by simp)]; exact du.2
  · have hW : ∀ A, (A = W + 48 ∨ A = W + 56) → A < 2 ^ 64 ∧ ¬ StepW A ∧ ¬ (A = LEAFPK + slotOff lay i ∨ A = LEAFPK + slotOff lay i + 8) := by
      intro A hA; unfold StepW slotOff; simp only [LEAFPK, CHAIN]; split_ifs <;> omega
    constructor
    · obtain ⟨h1, h2, h3⟩ := hW (W + 48) (Or.inl rfl)
      rw [fy3.get h1 h3, fy12.get h1 (by simp), fu.get h1 h2, f5.get h1 (by simp), f4.get h1 (by simp),
        f3.get h1 (by simp), w48, f1.get (by omega) (by simp)]; exact hv.1
    · obtain ⟨h1, h2, h3⟩ := hW (W + 56) (Or.inr rfl)
      rw [fy3.get h1 h3, fy12.get h1 (by simp), fu.get h1 h2, f5.get h1 (by simp), f4.get h1 (by simp),
        f3.get h1 (by simp), w56, f1.get (by omega) (by simp)]; exact hv.2
  · intro r hr
    have hr' : r ∉ [Reg.x6, .x7, .x10, .x11, .x12, .x19, .x20, .x21, .x23, .x28, .x29, .x30] := hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    rw [ry3.get (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; tauto),
      ry2.get (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; tauto),
      ru.get (by simp only [stepRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]; tauto),
      g5 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; tauto)]
  · intro A hA hn
    unfold OneW at hn
    simp only [not_or] at hn
    rw [fy3.get hA (by tauto), fy12.get hA (by simp), fu.get hA hn.1,
      f15.get hA (by simp only [CHAIN] at hn ⊢; unfold StepW at hn; simp only [CHAIN] at hn; omega)]

end SigGolfCandidate.T3M.Expand.SharedRecover
