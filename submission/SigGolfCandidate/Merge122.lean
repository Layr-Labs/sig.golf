import SigGolfCandidate.Merge055
import SigGolfCandidate.Merge093
import SigGolfCandidate.Merge112
import SigGolfCandidate.Merge120
import SigGolfCandidate.Merge121

-- ==== merged from T3M_Verify_LayerLower ====
section

set_option Elab.async false
set_option maxRecDepth 100000

section


section
set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3
namespace LCtx
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
def lowP (c : LCtx) : M (List Digest) := (List.range' 0 42).foldlM c.chainF [] >>= fun e => c.chainF e 42
def lowCost (c : LCtx) : Nat := c.chainsCost 0 42 + chainCost 42 c.ck
theorem lower_good (c : LCtx) (hc : c.ok) (hi0 : c.i0 = 0) (hko : c.koff = 0) (hck : c.ck < 8) (hRanks : ∀ j, j < 42 → c.headOK j) {s0 : MachineState}
    (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2) (h0 : c.Orig0 s0)
    (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ ends t, c.ChainOut s0 43 ends t → Verify.GoodQP P t N C Q A (K ends))
    (s : MachineState) (hs : c.ChainIn s0 0 [] s) :
    Verify.GoodQP P s (N + 1720) (C + c.lowCost) Q (A + c.lowCost) (Verify.ccM c.lowP K) := by
  unfold lowP
  rw [Verify.ccM_bind]
  have H := c.chains_good hc hk h0 (fun _ => hko) 42 (by omega) (fun j _ hj => hRanks j hj) (fun e => Verify.ccM (c.chainF e 42) K)
    (N + 40) (C + chainCost 42 c.ck) (A + chainCost 42 c.ck) Q
    (fun ends t ht => c.ck_good hc hk h0 (fun _ => hko) hck K N C A Q hK ends t ht) 42 0 (by omega) (by omega) [] s hs
  refine H.mono (by omega) ?_ (fun hq => ⟨hq, ?_⟩)
  · unfold lowCost; omega
  · unfold lowCost; omega
/-- The image's projected hash is the spec's `WCT9.halfHash`. -/
theorem vHash_eq_halfHash (high : Bool) (input : List UInt8) :
    Verify.vHash high input = ClaudeWCT.WCT9.halfHash high input := by
  rw [ClaudeWCT.WCT9.halfHash_eq]; unfold Verify.vHash; cases high <;> rfl
/-- C3: on a lower layer (`koff = 0`) the image's chain run is the spec's `chainPW` (chain 0's last step high). -/
theorem rest_chainPW (c : LCtx) (hlay : c.lay ≠ 0) (hko : c.koff = 0) (i d : Nat) (v : Digest) :
    c.rest i d v = ClaudeWCT.W9.T3M.chainPW c.lay c.tree c.leaf i d (7 - d) (c.pad0 i) (c.pad1 i) (c.padHeader i) v := by
  unfold LCtx.rest ClaudeWCT.W9.T3M.chainPW
  rw [hko, Nat.add_zero]
  congr 1
  funext v step
  rw [vHash_eq_halfHash, chainInputL_eq _ hlay]
  congr 1
  unfold LCtx.stepHigh ClaudeWCT.WCT9.chainHigh lowerG
  by_cases h6 : step = 6 <;> by_cases h0 : i = 0 <;> simp [h6, h0, hlay]
def coreChain (c : LCtx) (D : List Nat) (i : Nat) : M Digest :=
  ClaudeWCT.W9.T3M.chainPW c.lay c.tree c.leaf i (D.getD i 0) (maxDigit c.lay i - D.getD i 0)
    (ClaudeWCT.W9.T3M.wchainPads c.w c.lay i).1 (ClaudeWCT.W9.T3M.wchainPads c.w c.lay i).2
    (ClaudeWCT.W9.T3M.wchainHeaderPad c.w c.lay i) (ClaudeWCT.W9.T3M.wvalueFor c.w c.lay D i)
theorem fit_chain (c : LCtx) (hlay : c.lay ≠ 0) (hko : c.koff = 0) (D : List Nat)
    (hD : ∀ i < 43, c.dig i = D.getD i 0)
    (hS6 : c.S6 = Verify.WIT + ClaudeWCT.W9.T3M.layerBase c.lay + 16 * ClaudeWCT.W9.T3M.pathSlots c.lay + 520)
    (i : Nat) (hi : i < 43) :
    c.rest i (c.dig i) (c.bufferVal i) = c.coreChain D i := by
  rw [c.rest_chainPW hlay hko]
  unfold coreChain
  have hw : maxDigit c.lay i = 7 := by simp [maxDigit, hlay]
  rw [← hD i hi, hw, c.bufferVal_eq hlay D hD hS6 i hi]
  have e : c.blk i - Verify.WIT = ClaudeWCT.W9.T3M.chainBlock c.lay i := by
    unfold blk ClaudeWCT.W9.T3M.chainBlock; rw [chainSlot_lower hlay, hS6]; omega
  have hg : ClaudeWCT.WCT9.isG c.lay i = lowerG i := by simp [ClaudeWCT.WCT9.isG, lowerG, hlay]
  unfold pad0 pad1 pad0At pad1At padHeader ClaudeWCT.W9.T3M.wchainPads ClaudeWCT.W9.T3M.wchainHeaderPad
    ClaudeWCT.W9.T3M.pad0Off ClaudeWCT.W9.T3M.pad1Off
  rw [hg, show c.blk i + (if lowerG i then 32 else 0) - Verify.WIT = c.blk i - Verify.WIT + (if lowerG i then 32 else 0)
      by unfold blk; rw [hS6]; unfold Verify.WIT; omega,
    show c.blk i + (if lowerG i then 48 else 32) - Verify.WIT = c.blk i - Verify.WIT + (if lowerG i then 48 else 32)
      by unfold blk; rw [hS6]; unfold Verify.WIT; omega,
    show c.blk i - Verify.WIT + 24 = ClaudeWCT.W9.T3M.chainBlock c.lay i + 16 + 8 by omega, e, wdig_hi]
theorem lowP_eq (c : LCtx) (hlay : c.lay ≠ 0) (hko : c.koff = 0) (D : List Nat)
    (hD : ∀ i < 43, c.dig i = D.getD i 0)
    (hS6 : c.S6 = Verify.WIT + ClaudeWCT.W9.T3M.layerBase c.lay + 16 * ClaudeWCT.W9.T3M.pathSlots c.lay + 520) :
    c.lowP = (List.finRange 43).mapM fun i => c.coreChain D i.val := by
  rw [finRange_mapM, List.range_eq_range', show (43 : Nat) = 42 + 1 from rfl, List.range'_append_1.symm,
    List.mapM_append]
  unfold lowP
  have hF : (List.range' 0 42).foldlM c.chainF [] = (fun l => [] ++ l) <$> (List.range' 0 42).mapM
      (fun i => c.rest i (c.dig i) (c.bufferVal i)) :=
    foldlM_app_mapM _ 42 0 []
  rw [hF, mapM_congr' (List.range' 0 42) (fun i hi => c.fit_chain hlay hko D hD hS6 i (by
    have := List.mem_range'_1.mp hi; omega))]
  have h42 := c.fit_chain hlay hko D hD hS6 42 (by omega)
  unfold chainF
  rw [h42]
  simp [List.range'_one]
theorem lowCost_accept (c : LCtx) (hck : c.ck < 8) (D : List Nat) (hD : ∀ i < 43, c.dig i = D.getD i 0)
    (hl : D.length = 43) (T : Nat) (hT : D.sum = T) : c.lowCost + c.zSum 0 43 + 9 * T + 4*c.savedCopies 0 43 = 2935 := by
  have := c.chainsCost_lower hck T (by rw [c.sum_dig D hD hl, hT])
  unfold lowCost
  omega
end LCtx
end SigGolfCandidate.T3M
end
section
set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64)
theorem geomL (lay : Layer) (h : lay ≠ 0) :
    s6v lay.val = 4128 + ClaudeWCT.W9.T3M.layerBase lay + 16 * ClaudeWCT.W9.T3M.pathSlots lay + 520 ∧
      ClaudeWCT.W9.T3M.layerBase lay + 16 * ClaudeWCT.W9.T3M.pathSlots lay + 2248 ≤ layerEnd lay.val ∧
      7664 ≤ ClaudeWCT.W9.T3M.layerBase lay ∧ layerEnd lay.val < 18929 := by
  fin_cases lay
  · exact absurd rfl h
  all_goals decide +kernel
/-- C2 (FULL): the per-leaf blocks start one word later (entry offset 16). -/
theorem lfS7_pc (lay : Layer) (hlay : lay ≠ 0) (leaf : Nat) (hl : leaf < 2 ^ hL lay.val) :
    (BitVec.ofNat 64 (lfS7 lay.val leaf) + 16) &&& ~~~1#64 = pcOf (stabW lay.val (leaf % 2 ^ stabBits lay.val)) := by
  have e : lfS7 lay.val leaf + 16 = 0x1000 + 4 * stabW lay.val (leaf % 2 ^ stabBits lay.val) := by
    fin_cases lay
    · exact absurd rfl hlay
    all_goals
      simp only [lfS7, dispatchHeap, s7Bias, s7Sh, stabW, stabBits, hL] at hl ⊢
      norm_num at hl ⊢
      rw [Nat.mod_eq_of_lt hl]
      omega
  rw [show (16 : Word) = BitVec.ofNat 64 16 from rfl, ofNat_add_ofNat, e, even_andNot1' _ (by omega)]
theorem leafL_step (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer) (hlay : lay ≠ 0)
    (hidx : index < 2 ^ 31) (a : BitVec 256) (s0 : MachineState)
    (hk : ∀ p ∈ (lctxOf w index lay a).known, s0.getReg p.1 = p.2) (hck : (lctxOf w index lay a).ck < 8)
    (hG : Glob (chainK lay.val) w pk s0) (hO : Verify.Orig w (fun o => 7664 ≤ o ∧ o < layerEnd lay.val) s0)
    (h23 : s0.getReg .x23 = BitVec.ofNat 64 (lfS7 lay.val (route index lay).1))
    (h30 : s0.getReg .x31 = BitVec.ofNat 64 (route index lay).2)
    (h1 : s0.getReg .x2 = BitVec.ofNat 64 0xffbde0)
    (hBuffer : Verify.Orig w (fun o => BC.bufferStart lay.val ≤ o ∧ o < 21984) s0)
    (ends : List Digest) (t : MachineState)
    (ht : (lctxOf w index lay a).ChainOut s0 43 ends t) :
    ∃ u, Steps image t 4 4 u ∧ LeafOut w pk index lay ends u := by
  set L := lctxOf w index lay a with hLd
  have h0 : lay.val ≠ 0 := fun h => hlay (Fin.ext h)
  obtain ⟨⟨hR, hF, hS⟩, hlen, hpc⟩ := ht
  have hkL : ∀ q ∈ chainK lay.val, s0.getReg q.1 = q.2 := hG.1
  have hknown : KnownOK (leafK lay.val) t := by
    intro p hp
    simp only [leafK, gkL_low h0, baseK, if_neg h0, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with ((rfl | rfl) | rfl | rfl) | rfl
    · rw [hR .x5 (by simp [chainRegs])]; exact hkL (_, _) (by simp [chainK, baseK])
    · rw [hR .x18 (by simp [chainRegs])]; exact hkL (_, _) (by simp [chainK, baseK])
    · rw [hR .x7 (by simp [chainRegs])]; exact hkL (_, _) (by simp [chainK])
    · rw [hR .x5 (by simp [chainRegs])]; exact hkL (_, _) (by simp [chainK, baseK])
    · rw [hR .x4 (by simp [chainRegs])]
      exact hkL (.x4, _) (by simp [chainK])
  have hBias : L.bufferOffset = bufferBias lay.val := by
    fin_cases lay
    · exact absurd rfl hlay
    all_goals rfl
  have hBB : bufferBase lay.val = bufferBias lay.val + 768 := by
    fin_cases lay
    · exact absurd rfl hlay
    all_goals rfl
  have hBb : bufferBase lay.val % 8 = 0 ∧ 23056 ≤ bufferBase lay.val ∧ bufferBase lay.val ≤ 25216 := by
    fin_cases lay <;> decide +kernel
  have hBi : 22288 ≤ bufferBias lay.val ∧ bufferBias lay.val ≤ 24704 := by fin_cases lay <;> decide +kernel
  obtain ⟨u, hu⟩ := spec_run (lfSlotCheck_at lay.val L.ck h0 lay.isLt hck) t (by rw [hpc]; rfl) hknown
    (by intro b hb; simp [specLf, h0] at hb) (by simp)
  have hst := hu.steps
  rw [show (specLf lay.val).steps = 4 by simp [specLf, h0],
    show (specLf lay.val).cycles = 4 by simp [specLf, h0]] at hst
  refine ⟨u, hst, ?_⟩
  have hku : KnownOK (postLf lay.val) u := hu.known
  have hkeep := hu.keep
  have hmem : ∀ A, u.getMem A = memEval t [(⟨none, BitVec.ofNat 64 (bufferBase lay.val+16)⟩, .reg .x28)] A := by
    intro A; rw [hu.mem]; simp [specLf, h0]
  have hfr : ∀ A, A < 2 ^ 64 → A ≠ bufferBase lay.val+24 → A ≠ bufferBase lay.val+16 → u.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := by
    intro A hA _ h2
    rw [hmem]
    apply memEval_frame_ofNat t _ A hA
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl
    simp; omega
  have htr := tree_lt index lay hidx
  have hlf := leaf_lt index lay
  obtain ⟨hg1, hg2, hg3, hg4⟩ := geomL lay hlay
  have hS6 : L.S6 = s6v lay.val := rfl
  refine ⟨?_, ?_, fun h => absurd h hlay, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hu.spc (tgtLf lay.val) (by simp [specLf, h0])]
    simp only [tgtLf, if_neg h0, E.eval, BinOp.eval, addC_eval]
    rw [hR .x23 (by simp [chainRegs]), h23]
    exact lfS7_pc lay hlay _ hlf
  · have hGt : Glob baseK w pk t := glob_frame hG hF (fun A hA => by
        replace hA := L.Wr_range (by omega) hA
        unfold LCtx.bufferEnd LCtx.bufferSlot at hA; rw [hS6, hBias] at hA
        have : slotL L.i0 = 768 := rfl
        rw [this] at hA
        simp only [show L.i0 = 0 from rfl, slotL, if_neg (by omega : ¬43=0), if_pos rfl] at hA
        split_ifs at hA <;> rcases hA with hA | hA <;> omega)
      (fun p hp => hknown p (by simp [leafK, gkL_low h0, hp]))
    have hGu := hu.glob _ w pk hGt (RelOK.nil t)
    refine ⟨fun p hp => ?_, hGu.2.1, hGu.2.2.1, hGu.2.2.2.1, hGu.2.2.2.2⟩
    rcases List.mem_append.mp hp with hp | hp
    · exact hku p hp
    · have h22 : s0.getReg .x22 = BitVec.ofNat 64 (s6v lay.val) :=
        hk (.x22, BitVec.ofNat 64 L.S6) (by simp [LCtx.known])
      have m6 : ((.x7 : Reg), (1 : Word)) ∈ postLf lay.val := by
        simp [postLf, leafK, h0]
      simp only [lfKeepK, if_neg h0, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)
      all_goals first
        | exact hku _ m6
        | rw [hkeep _ (by simp [keepLfL]), hR _ (by simp [chainRegs])]; exact h22
        | rw [hkeep _ (by simp [keepLfL]), hR _ (by simp [chainRegs])]; exact h1
        | rw [hkeep _ (by simp [keepLfL]), hR _ (by simp [chainRegs])]; exact hkL (_, _) (by simp [chainK])
  · intro _; rw [hkeep .x31 (by simp [keepLfL]), hR .x31 (by simp [chainRegs]), h30]
  · rw [hlen, LCtx.chainCount_lower lay hlay]; rfl
  · intro j hj
    rw [LCtx.chainCount_lower lay hlay] at hj
    have e := hS j (by rw [hlen]; exact hj)
    have hj0 : slotL (L.i0 + j) = slotL j := by rw [show L.i0 = 0 from rfl, Nat.zero_add]
    simp only [LCtx.bufferSlot, hBias, hj0] at e
    simp only [lfSlot, if_neg h0]
    have hsl : slotL j = 768 ∨ 800 ≤ slotL j := by unfold slotL; split <;> omega
    have hsl' : slotL j < 2 ^ 32 := by unfold slotL; split <;> omega
    exact ⟨(hfr (bufferBias lay.val + slotL j) (by omega) (by omega) (by omega)).trans e.1,
      (hfr (bufferBias lay.val + slotL j + 8) (by omega) (by omega) (by omega)).trans e.2⟩
  · rw [show lfBase lay.val + 16 = bufferBase lay.val+16 from rfl, hmem,
      memEval_cons_ofNat _ _ _ _ _ (by omega) (by omega), if_pos rfl]
    simp only [E.eval]
    rw [hR .x28 (by simp [chainRegs]), hk (.x28, BitVec.ofNat 64 L.x28v) (by simp [LCtx.known]), routed_eq,
      show below lay.val = BC.below lay.val from rfl, ← hyperWord_x28v w index lay a]
    rfl
  · -- C3: the leaf tweak's high word is witness memory (no chain or setup write reaches it)
    have hlb : ClaudeWCT.W9.T3M.leafBufferBase lay = bufferBase lay.val - WIT := by
      fin_cases lay
      · exact absurd rfl hlay
      all_goals rfl
    have hbs : BC.bufferStart lay.val = ClaudeWCT.W9.T3M.leafBufferBase lay := by
      fin_cases lay
      · exact absurd rfl hlay
      all_goals rfl
    have hu24 : u.getMem (BitVec.ofNat 64 (bufferBase lay.val + 24)) =
        t.getMem (BitVec.ofNat 64 (bufferBase lay.val + 24)) := by
      rw [hmem]; apply memEval_frame_ofNat t _ _ (by omega)
      intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl; simp; omega
    have ht24 : t.getMem (BitVec.ofNat 64 (bufferBase lay.val + 24)) =
        s0.getMem (BitVec.ofNat 64 (bufferBase lay.val + 24)) := by
      apply hF.get (by omega)
      intro hw
      have hb0 := L.bufferBound_slot
      have hs0 : L.bufferSlot 0 = bufferBase lay.val := by
        unfold LCtx.bufferSlot; rw [hBias, hBB]; rfl
      have hs1 : L.bufferSlot 1 = L.bufferSlot 0 + 32 := by unfold LCtx.bufferSlot slotL; simp
      have hi0 : L.i0 = 0 := rfl
      replace hw := L.Wr_range (by omega) hw
      rw [hi0] at hw
      have harea := L.bufferArea_slot
      omega
    have hw := (hBuffer.mono (fun o (ho : o = bufferBase lay.val - WIT + 24) => ⟨by rw [ho, ← hlb, ← hbs]; omega,
      by rw [ho]; unfold WIT; omega⟩)).hi (bufferBase lay.val - WIT + 16) (by unfold WIT; omega)
      (by unfold WIT WX; omega) (by omega)
    rw [show lfBase lay.val + 24 = bufferBase lay.val+24 from rfl, hu24, ht24,
      show bufferBase lay.val + 24 = WIT + (bufferBase lay.val - WIT + 16) + 8 by unfold WIT; omega, hw]
    unfold ClaudeWCT.W9.T3M.wleafHigh; rw [hlb]
  · have hOt : Verify.Orig w (fun o => 7664 ≤ o ∧
        o < ClaudeWCT.W9.T3M.layerBase lay + 16 * ClaudeWCT.W9.T3M.pathSlots lay) t :=
      (hO.mono (fun o ho => ⟨ho.1, by omega⟩)).frame (fun j hj hp => hF.get (by unfold WIT WX at *; omega)
        (fun hw => by
          replace hw := L.Wr_range (by omega) hw
          unfold LCtx.bufferEnd LCtx.bufferSlot at hw; rw [hS6, hBias] at hw
          simp only [show L.i0 = 0 from rfl, slotL, if_neg (by omega : ¬43=0), if_pos rfl] at hw
          unfold WIT at hw
          split_ifs at hw <;> rcases hw with hw | hw <;> omega))
    exact (hu.orig_const hOt).mono (fun o ho => ⟨ho, by simp only [lfAllowed, List.mem_cons, List.not_mem_nil, or_false]; unfold WIT; omega⟩)
  · intro hLay
    have hfut : BC.bufferStart lay.val ≤ BC.bufferStart (lay.val-1) ∧
        bufferBase lay.val + 720 ≤ WIT + BC.bufferStart (lay.val-1) ∧
        s6v lay.val - 520 + 2264 ≤ WIT + BC.bufferStart (lay.val-1) := by
      fin_cases lay
      · exact absurd rfl hlay
      all_goals decide +kernel
    have hBt : Verify.Orig w (fun o => BC.bufferStart (lay.val-1) ≤ o ∧ o < 21984) t :=
      (hBuffer.mono (fun o ho => ⟨by omega,ho.2⟩)).frame (fun j hj hp =>
        hF.get (by unfold WIT WX at *; omega) (fun hw => by
          replace hw := L.Wr_range (by omega) hw
          unfold LCtx.bufferEnd LCtx.bufferSlot at hw
          rw [hS6,hBias] at hw
          simp only [show L.i0=0 from rfl, slotL, if_neg (by omega : ¬43=0), if_pos rfl] at hw
          unfold WIT at *
          split_ifs at hw <;> rcases hw with hw | hw <;> omega))
    exact (hu.orig_const hBt).mono (fun o ho => ⟨ho, by
      simp only [lfAllowed,List.mem_cons,List.not_mem_nil,or_false]
      unfold WIT at *; omega⟩)
end SigGolfCandidate.T3M
end
end

section

section
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest Layer route height)
theorem plan_eq : planL1 = ClaudeWCT.W9.T3M.lowerPlanL1 ∧ planL32 = ClaudeWCT.W9.T3M.lowerPlanL32 := ⟨rfl, rfl⟩
set_option maxRecDepth 100000 in
theorem rowA_tab : ∀ lay : Fin 3, ∀ c < 2 ^ hL (lay.val + 1),
    rowA lay.val c = WIT + ClaudeWCT.W9.T3M.merkleBlock (ClaudeWCT.W9.T3M.upLayer lay.castSucc) c
      (height (ClaudeWCT.W9.T3M.upLayer lay.castSucc) - 1) := by decide +kernel
theorem upLayer_val (lay : Layer) (h3 : lay.val ≠ 3) : (ClaudeWCT.W9.T3M.upLayer lay).val = lay.val + 1 := by
  unfold ClaudeWCT.W9.T3M.upLayer; simp only [Fin.val_ofNat]; have := lay.isLt; omega
theorem cpIdx_route (index : Nat) (lay : Layer) (h3 : lay.val ≠ 3) :
    BC.cpIdx index lay.val = (route index (ClaudeWCT.W9.T3M.upLayer lay)).1 := by
  rw [route_fst, upLayer_val lay h3]; unfold BC.cpIdx; rw [if_neg h3]; rfl
theorem rowA_eq (index : Nat) (lay : Layer) (h3 : lay.val ≠ 3) :
    rowA lay.val (BC.cpIdx index lay.val) = WIT + ClaudeWCT.W9.T3M.rowBlock index lay := by
  have hl := leaf_lt index (ClaudeWCT.W9.T3M.upLayer lay)
  rw [upLayer_val lay h3] at hl
  rw [cpIdx_route index lay h3]
  unfold ClaudeWCT.W9.T3M.rowBlock; rw [if_neg h3]
  have := lay.isLt
  obtain ⟨l, hl3⟩ := lay
  have hl3' : l < 3 := by simp at h3; omega
  exact rowA_tab ⟨l, hl3'⟩ _ hl
theorem rowBlock_mod8 (index : Nat) (lay : Layer) : ClaudeWCT.W9.T3M.rowBlock index lay % 8 = 0 := by
  by_cases h3 : lay.val = 3
  · unfold ClaudeWCT.W9.T3M.rowBlock; rw [if_pos h3]
  · have e := rowA_eq index lay h3
    obtain ⟨r16, -⟩ := rowA_facts lay.val (BC.cpIdx index lay.val) (by have := lay.isLt; omega)
      (cpIdx_lt index lay.val lay.isLt)
    unfold WIT at e; omega
theorem hdrA_eq (l : Nat) (hl : l < 4) : hdrA l = hdrAddr l := by
  interval_cases l <;> decide +kernel
theorem hyper_or (lay r : Nat) (hl : lay < 4) (hr : r < 2 ^ 32) :
    BitVec.ofNat 64 (hyperBase lay) ||| BitVec.ofNat 64 (r * 2 ^ 16) = T3.hyperWord lay r := by
  have e1 : BitVec.ofNat 64 (hyperBase lay) =
      BitVec.ofNat 64 ((lay + 193 * 256) * 2 ^ 48) ||| BitVec.ofNat 64 0x201 := by
    rw [ofNat_or_add 0x201 (lay + 193 * 256) 48 (by norm_num)]; unfold hyperBase; apply congrArg (BitVec.ofNat 64); ring
  rw [e1, BitVec.or_assoc, BitVec.or_comm (BitVec.ofNat 64 0x201), ofNat_or_add 0x201 r 16 (by norm_num),
    ofNat_or_add (r * 2 ^ 16 + 0x201) (lay + 193 * 256) 48 (by omega)]
  unfold T3.hyperWord
  rw [Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt (by omega : lay < 256)]
  apply congrArg (BitVec.ofNat 64)
  ring
theorem rowTweak_lo (lay : Layer) (tree leaf : Nat) :
    dlo (T3.rowTweak lay tree leaf) = T3.hyperWord lay.val (tree * 2 ^ height lay + leaf) :=
  BitVec.extractLsb'_append_eq_right
theorem rowTweak_hi (lay : Layer) (tree leaf : Nat) : dhi (T3.rowTweak lay tree leaf) = 1#64 :=
  BitVec.extractLsb'_append_eq_left
/-- C3 (FULL): the row tweak's high word `hi` is read from memory (a witness pad, honest 1). -/
theorem row_hash (t : MachineState) (A : Nat) (hA8 : A % 8 = 0) (hA : A + 64 < 2 ^ 64) (lay : Layer)
    (tree leaf : Nat) (left right cp : Digest) (hi : BitVec 64) (h10 : t.getReg .x10 = BitVec.ofNat 64 A)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 64) (h0 : DigAt t A left)
    (h2 : t.getMem (BitVec.ofNat 64 (A + 16)) = T3.hyperWord lay.val (tree * 2 ^ height lay + leaf))
    (h3 : t.getMem (BitVec.ofNat 64 (A + 24)) = hi) (h4 : t.getMem (BitVec.ofNat 64 (A + 32)) = dlo cp)
    (h5 : t.getMem (BitVec.ofNat 64 (A + 40)) = dhi cp) (h6 : DigAt t (A + 48) right) :
    hashInput t = toQ (T3.pad64 (blk4 left (hi ++ T3.hyperWord lay.val (tree * 2 ^ height lay + leaf)) cp right)) := by
  rw [pad64_blk4]
  apply hashInput_words8 t _ A (blk4_length _ _ _ _) h10 hA8 hA h11
  rw [wordsOf_blk4, show dlo (hi ++ T3.hyperWord lay.val (tree * 2 ^ height lay + leaf)) =
      T3.hyperWord lay.val (tree * 2 ^ height lay + leaf) from BitVec.extractLsb'_append_eq_right,
    show dhi (hi ++ T3.hyperWord lay.val (tree * 2 ^ height lay + leaf)) = hi from BitVec.extractLsb'_append_eq_left,
    h0.1, h0.2, h2, h3, h4, h5, h6.1,
    show A + 48 + 8 = A + 56 by omega] at *
  all_goals (try rw [h6.2])
  all_goals (try rfl)
end SigGolfCandidate.T3M
end
section
namespace SigGolfCandidate.T3M.BC
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest Layer route height counterLimit encodingInput pad64)
open ClaudeWCT.WCT9 (LayerMsg)
def CounterEval : Prop := ∀ (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer)
  (msg : LayerMsg) (s : MachineState), LayerIn w pk index lay.val msg s →
  (ctrE lay.val (cpIdx index lay.val)).eval s = BitVec.ofNat 64 (ClaudeWCT.W9.T3M.wbcCtr w index lay).toNat
theorem counter_eval : CounterEval := fun w pk index lay msg s hs => by
  by_cases h3 : lay.val = 3
  case neg =>
    cases msg with
    | forest root => exact hs.msg.elim
    | pair left right =>
      have hm := (hs.msg.pair_low h3).2.2.2 4 (Or.inr (Or.inl rfl))
      simp only [ctrE, if_neg h3, E.eval, kw, UnOp.eval, hm]
      rw [counterWord]
      have e := T3M.rowA_eq index lay h3
      have h8 := T3M.rowBlock_mod8 index lay
      unfold ClaudeWCT.W9.T3M.wbcCtr ClaudeWCT.W9.T3M.bcCounterOff
      rw [show 8 * ((rowA lay.val (cpIdx index lay.val) - WIT) / 8 + 4) =
        ClaudeWCT.W9.T3M.rowBlock index lay + 32 by rw [e]; unfold WIT; omega]
  case pos =>
    obtain rfl : lay = 3 := Fin.ext h3
    exact T3M.ctrE_eval w index s hs.glob.2.1
/-- The verify machine's encoding-counter branch compares against its literal `0x400000 = 2^22` (independent of the
scheme's search windows `T3.counterLimit` / `WCT9.searchLimit`). -/
def CounterBranch : Prop := ∀ (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer)
    (msg : LayerMsg) (s : MachineState), LayerIn w pk index lay.val msg s →
  ∀ d, Br.holds s (ctrBr lay.val (cpIdx index lay.val) d) ↔
    d = decide (if lay.val = 3 then (ClaudeWCT.W9.T3M.wbcCtr w index lay).toNat < 2 ^ 22
      else (ClaudeWCT.W9.T3M.wbcCtr w index lay).toNat ≥ 2 ^ 22)
theorem counter_branch : CounterBranch := fun w pk index lay msg s hs d => by
  have h64 : (ClaudeWCT.W9.T3M.wbcCtr w index lay).toNat < 2 ^ 64 :=
    lt_of_lt_of_le (ClaudeWCT.W9.T3M.wbcCtr w index lay).isLt (by decide +kernel)
  norm_num at h64
  unfold ctrBr Br.holds
  rw [counter_eval w pk index lay msg s hs]
  by_cases h3 : lay.val = 3 <;>
    simp [h3, CmpOp.eval, E.eval, kw, BitVec.ult, Nat.mod_eq_of_lt h64,
      ← decide_not, eq_comm]
theorem encoding_reject (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer)
    (msg : LayerMsg) (s : MachineState) (_hs : LayerIn w pk index lay.val msg s)
    (hge : (ClaudeWCT.W9.T3M.wbcCtr w index lay).toNat ≥ ClaudeWCT.WCT9.verifyWindow) :
    ∃ u, Steps image s (rejectSteps lay.val) (rejectSteps lay.val) u ∧
      fetch image u = some (.base .ECALL) ∧ u.getReg .x5 = 1 ∧ u.getReg .x10 = 1 :=
  absurd hge (ClaudeWCT.WCT9.ctr_not_ge_verifyWindow _)
def PairInputBlock : Prop := ∀ (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (tree leaf : Nat)
  (left right : Digest) (hi : BitVec 64), ClaudeWCT.WCT9.pairEncodingInputH lay tree leaf left right
    (ClaudeWCT.W9.T3M.wbcCtr w index lay) (ClaudeWCT.W9.T3M.wbcPad w index lay) hi =
  blk4 left (hi ++ T3.hyperWord lay.val (tree * 2 ^ height lay + leaf))
    (ClaudeWCT.W9.T3M.wdig w (ClaudeWCT.W9.T3M.bcCounterOff index lay)) right
theorem pair_input_block : PairInputBlock := fun w index lay tree leaf left right hi => by
  unfold ClaudeWCT.WCT9.pairEncodingInputH blk4
  simp only [List.append_assoc]
  rw [← List.append_assoc (SphincsSecurity.bytesLE 4 (ClaudeWCT.W9.T3M.wbcCtr w index lay)), counterPadBytes]
  rw [show ClaudeWCT.W9.T3M.wbcPad w index lay ++ ClaudeWCT.W9.T3M.wbcCtr w index lay =
    ClaudeWCT.W9.T3M.wdig w (ClaudeWCT.W9.T3M.bcCounterOff index lay) from counterPadExtract w _]
def EncodingRun : Prop := ∀ (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer)
  (msg : LayerMsg) (s : MachineState), LayerIn w pk index lay.val msg s →
  (ClaudeWCT.W9.T3M.wbcCtr w index lay).toNat < ClaudeWCT.WCT9.verifyWindow →
  ∃ t, SpecRes (allowed lay.val (cpIdx index lay.val)) [] (setupGk lay.val) (specA lay.val (cpIdx index lay.val))
      (bKS lay.val (cpIdx index lay.val)) (keepA lay.val) s t
theorem encoding_run : EncodingRun := fun w pk index lay msg s hs _ => by
  have hcc := (T3M.copy_parts lay.val (cpIdx index lay.val)
    (copyCheck_at lay.val _ lay.isLt (T3M.cpIdx_lt index lay.val lay.isLt))).1
  have hbrs : (specA lay.val (cpIdx index lay.val)).brs = [] := by
    fin_cases lay <;> rfl
  exact spec_run hcc s hs.copy hs.glob.1 (by rw [hbrs]; simp) (by simp)
theorem t3E3_eval (s : MachineState) (index : Nat) (hidx : index < 2 ^ 31)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 index)
    (hm : s.getMem (BitVec.ofNat 64 (TOPLOAD + 32)) = BitVec.ofNat 64 (hyperBase 3)) :
    t3E3.eval s = T3.hyperWord 3 index := by
  simp only [t3E3, E.eval, BinOp.eval, kw, h22]
  rw [show hdrA 3 = TOPLOAD + 32 from rfl, hm, ofNat_shl',
    show (16 : Nat) % 2 ^ 64 % 64 = 16 by norm_num]
  exact hyper_or 3 index (by norm_num) (by omega)
def SetupPost : Prop := ∀ (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer)
  (msg : LayerMsg) (s : MachineState), LayerIn w pk index lay.val msg s →
  ∀ t, SpecRes (allowed lay.val (cpIdx index lay.val)) [] (setupGk lay.val) (specA lay.val (cpIdx index lay.val))
    (bKS lay.val (cpIdx index lay.val)) (keepA lay.val) s t → EncPre w pk index lay.val (cpIdx index lay.val) t
theorem setup_writes_bounds (lay c : Nat) (hl : lay < 4) (hc : c < nCopy lay) :
    ∀ A ∈ allowed lay c, (A < WIT+7664 ∨ WIT+layerEnd lay ≤ A) ∧ A < WIT+bufferStart lay := by
  have H : ((List.range 4).all fun l => (List.range (nCopy l)).all fun c =>
    (allowed l c).all fun A => decide ((A < WIT+7664 ∨ WIT+layerEnd l ≤ A) ∧ A < WIT+bufferStart l)) = true := by
    decide +kernel
  intro A hA
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp H lay
    (List.mem_range.mpr hl)) c (List.mem_range.mpr hc)) A hA)
/-- C4 (D7): the L3 block's run starts without `x18`; its `ld s2,-304(s1)` restores `x18 = 0xFFF` from `d0`. -/
theorem setup_known (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer) (msg : LayerMsg)
    (s : MachineState) (hs : LayerIn w pk index lay.val msg s) (t : MachineState)
    (ht : SpecRes (allowed lay.val (cpIdx index lay.val)) [] (setupGk lay.val) (specA lay.val (cpIdx index lay.val))
      (bKS lay.val (cpIdx index lay.val)) (keepA lay.val) s t) :
    KnownOK (bK lay.val (cpIdx index lay.val)) t := by
  intro p hp
  by_cases h3 : lay.val = 3
  · obtain rfl : lay = 3 := Fin.ext h3
    rcases p with ⟨r, v⟩
    by_cases h18 : r = .x18
    · subst h18
      have hv : v = 0xFFF := by
        simp [bK, T3M.bK, layK, baseK] at hp; exact hp
      subst hv
      rw [ht.regs (.x18, x18E3) (by simp [specA, T3M.specA])]
      exact hs.d0 rfl
    · exact ht.known _ (by
        simp only [bKS, if_pos (show (3 : Layer).val = 3 from rfl)]
        exact List.mem_filter.mpr ⟨hp, by simpa using h18⟩)
  · exact ht.known p (by simp only [bKS, if_neg h3]; exact hp)
theorem setup_post : SetupPost := fun w pk index lay msg s hs t ht => by
  obtain ⟨hlE, htE, -, hs7E⟩ := T3M.route_evals index lay hs.idx s hs.route
  refine ⟨?_, ⟨setup_known w pk index lay msg s hs t ht, (ht.glob _ w pk hs.glob (RelOK.nil s)).2⟩, ?_, ?_, ?_,
    (ht.orig_const hs.orig).mono (fun o ho => ⟨ho, by
      intro hm
      have H := setup_writes_bounds lay.val _ lay.isLt (T3M.cpIdx_lt index lay.val lay.isLt) _ hm
      rcases H.1 with H | H <;> omega⟩), ?_, ?_, ?_, ?_, ?_⟩
  case refine_1 => fin_cases lay <;> exact ht.pc rfl
  case refine_2 =>
    by_cases h3 : lay.val = 3
    · obtain rfl : lay = 3 := Fin.ext h3
      rw [ht.regs (.x28, t3E3) (by simp [specA, T3M.specA])]
      have h22 : s.getReg .x22 = BitVec.ofNat 64 index := by
        simpa [rReg, below] using hs.route
      rw [t3E3_eval s index hs.idx h22 (hs.hdr3 rfl).1, show below (3 : Layer).val = 0 from rfl, pow_zero,
        Nat.div_one]
      try rfl
    · rw [ht.keep .x28 (by fin_cases lay <;> simp_all [keepA])]
      exact hs.word (by have := lay.isLt; omega)
  case refine_3 =>
    intro L hL hl3
    obtain rfl : L = lay := Fin.ext hL
    have h3 : L.val ≠ 3 := by omega
    exact (ht.regs (.x23, s7E L.val) (by fin_cases L <;> simp_all [specA, T3M.specA])).trans hs7E
  case refine_4 =>
    intro L hL
    obtain rfl : L = lay := Fin.ext hL
    refine ⟨fun h0 hl3 => ?_, fun h0 => ?_⟩
    · have h3 : L.val ≠ 3 := by omega
      exact (ht.regs (.x31, treeE L.val) (by fin_cases L <;> simp_all [specA, T3M.specA])).trans htE
    · obtain rfl : L = 0 := Fin.ext h0
      rw [ht.keep .x31 (by simp [keepA])]
      simpa [leafE, E.eval] using hlE
  case refine_5 =>
    intro h3
    obtain rfl : lay = 3 := Fin.ext h3
    have hm (A : Word) : t.getMem A = memEval s (T3M.specA 3 (trPc 3 (cpIdx index 3))).mem A := ht.mem A
    have hf (A : Nat) (hA : A < 2 ^ 64) (h1 : A ≠ 4144) (h3 : A ≠ 4176) (h4 : A ≠ 4184) :
        t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
      rw [hm]
      apply memEval_frame_ofNat s _ A hA
      intro p hp
      simp only [T3M.specA, T3M.l3Writes, ↓reduceIte, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at hp
      rcases hp with rfl <;> simp <;> omega
    refine ⟨?_, ?_, fun k hk => ?_⟩
    · rw [hf _ (by unfold TOPLOAD; omega) (by unfold TOPLOAD; omega) (by unfold TOPLOAD; omega)
        (by unfold TOPLOAD; omega)]
      exact (hs.hdr3 rfl).1
    · rw [hf _ (by unfold TOPLOAD; omega) (by unfold TOPLOAD; omega) (by unfold TOPLOAD; omega)
        (by unfold TOPLOAD; omega)]
      exact (hs.hdr3 rfl).2.1
    · rw [hf _ (by unfold TOPLOAD; omega) (by unfold TOPLOAD; omega) (by unfold TOPLOAD; omega)
        (by unfold TOPLOAD; omega)]
      exact (hs.hdr3 rfl).2.2 k hk
  case refine_6 =>
    intro h3
    obtain rfl : lay = 3 := Fin.ext h3
    exact (ht.keep .x22 (by simp [keepA])).trans (by simpa [rReg, below] using hs.route)
  case refine_7 =>
    intro hl3
    obtain ⟨d, hd, hdd⟩ := hs.dst hl3
    refine ⟨d, ?_, hdd⟩
    have h3 : lay.val ≠ 3 := by omega
    rw [ht.regs (.x12, .reg .x12) (by fin_cases lay <;> simp_all [specA])]
    simpa [E.eval] using hd
  case refine_8 =>
    exact (ht.orig_const hs.bufferOrig).mono (fun o ho => ⟨ho, by
      intro hm
      have H := (setup_writes_bounds lay.val _ lay.isLt (T3M.cpIdx_lt index lay.val lay.isLt) _ hm).2
      omega⟩)
  case refine_9 =>
    intro h3
    obtain rfl : lay = 3 := Fin.ext h3
    rw [ht.regs (.x12, .reg .x12) (by simp [specA, T3M.specA])]
    simpa [E.eval] using hs.dst3 rfl
def SetupHash : Prop := ∀ (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer)
  (msg : LayerMsg) (s : MachineState), LayerIn w pk index lay.val msg s →
  ∀ t, SpecRes (allowed lay.val (cpIdx index lay.val)) [] (setupGk lay.val) (specA lay.val (cpIdx index lay.val))
    (bKS lay.val (cpIdx index lay.val)) (keepA lay.val) s t →
  t.getReg .x5 = 0 ∧ hashArgumentsValid t = true ∧
  hashInput t = toQ (T3.pad64 (ClaudeWCT.W9.T3M.layerEncodingInputP lay
    (route index lay).2 (route index lay).1 msg
    (ClaudeWCT.W9.T3M.wbcCtr w index lay) (ClaudeWCT.W9.T3M.wbcPad w index lay) (ClaudeWCT.W9.T3M.wbcRight w)
    (ClaudeWCT.W9.T3M.wbcHigh w index lay)))
theorem setup_hash : SetupHash := fun w pk index lay msg s hs t ht => by
  have hpost := setup_post w pk index lay msg s hs t ht
  have hkB := setup_known w pk index lay msg s hs t ht
  have h5 : t.getReg .x5 = 0 := hkB (.x5, 0) (by fin_cases lay <;> simp [bK, T3M.bK, layK, baseK])
  have h11 : t.getReg .x11 = BitVec.ofNat 64 64 := hkB (.x11, _) (by fin_cases lay <;> simp [bK, T3M.bK, layK])
  have hrw := T3M.routed_eq index lay
  by_cases h3 : lay.val = 3
  · obtain rfl : lay = 3 := Fin.ext h3
    cases msg with
    | forest root => exact hs.msg.elim
    | pair left right =>
    have hm3 := hs.msg.pair_top
    have h10 : t.getReg .x10 = BitVec.ofNat 64 4128 := hkB (.x10, _) (by simp [bK, T3M.bK])
    have h12d : t.getReg .x12 = BitVec.ofNat 64 4112 ∨ t.getReg .x12 = BitVec.ofNat 64 4176 := hpost.dst3 rfl
    have hm (A : Word) : t.getMem A = memEval s (T3M.specA 3 (trPc 3 (cpIdx index 3))).mem A := ht.mem A
    have hf : ∀ A, A < 2 ^ 64 → A ≠ 4144 →
        t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
      intro A hA h1
      rw [hm]
      apply memEval_frame_ofNat s _ A hA
      intro p hp
      simp only [T3M.specA, T3M.l3Writes, ↓reduceIte, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at hp
      rcases hp with rfl <;> simp <;> omega
    have hH : WitHdr w s := hs.glob.2.1
    refine ⟨h5, ?_, ?_⟩
    · rcases h12d with h12 | h12
      · exact hashArgs_of t 4128 64 4112 h10 h11 h12 (by decide +kernel) (by decide +kernel) (by decide +kernel)
          (by decide +kernel) (by decide +kernel)
      · exact hashArgs_of t 4128 64 4176 h10 h11 h12 (by decide +kernel) (by decide +kernel) (by decide +kernel)
          (by decide +kernel) (by decide +kernel)
    change hashInput t = toQ (pad64 (ClaudeWCT.WCT9.pairEncodingInputH 3 (route index 3).2 (route index 3).1 left
      right (ClaudeWCT.W9.T3M.wbcCtr w index 3) (ClaudeWCT.W9.T3M.wbcPad w index 3) (ClaudeWCT.W9.T3M.wbcHigh w index 3)))
    rw [pair_input_block, show ClaudeWCT.W9.T3M.bcCounterOff index 3 = 8 * 4 from rfl]
    apply T3M.row_hash t 4128 (by decide +kernel) (by decide +kernel) 3 _ _ left _ _ _ h10 h11
    · exact ⟨(hf _ (by decide +kernel) (by decide +kernel)).trans hm3.1.1,
        (hf _ (by decide +kernel) (by decide +kernel)).trans hm3.1.2⟩
    · rw [hm]; simp only [T3M.specA, T3M.l3Writes, ↓reduceIte, List.cons_append, List.nil_append]
      rw [memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_pos rfl]
      rw [t3E3_eval s index hs.idx (by simpa [rReg, below] using hs.route) (hs.hdr3 rfl).1, hrw,
        show T3M.below (3 : Layer).val = 0 from rfl, pow_zero, Nat.div_one]
      try rfl
    · -- C3 (stage 2): word 857 of stage 1 (`sd t2,-152(s0)`) is gone; the high word is the witness word at offset 24
      refine (hf _ (by decide +kernel) (by decide +kernel)).trans ?_
      refine (hm3.2.2 : s.getMem (BitVec.ofNat 64 (4128 + 24)) = wword w 3).trans ?_
      unfold ClaudeWCT.W9.T3M.wbcHigh ClaudeWCT.W9.T3M.rowBlock
      rw [if_pos (show (3 : Layer).val = 3 from rfl)]
      exact (Verify.wdig_hi w 2).symm
    · rw [hf _ (by decide +kernel) (by decide +kernel), Verify.wdig_lo]; exact hH 4 (by decide +kernel) (by decide +kernel)
    · rw [hf _ (by decide +kernel) (by decide +kernel), Verify.wdig_hi]; exact hH 5 (by decide +kernel) (by decide +kernel)
    · -- the merged singleton leaves the right top value at `WIT + 48`; the entry does not copy it
      exact ⟨(hf _ (by decide +kernel) (by decide +kernel)).trans hm3.2.1.1,
        (hf _ (by decide +kernel) (by decide +kernel)).trans hm3.2.1.2⟩
  · cases msg with
    | forest root => exact hs.msg.elim
    | pair left right =>
    have hmsg := hs.msg.pair_low h3
    have hl3 : lay.val < 3 := hmsg.1
    set c := cpIdx index lay.val with hcd
    have hc := T3M.cpIdx_lt index lay.val lay.isLt
    obtain ⟨r16, rlo, rhi, rend⟩ := T3M.rowA_facts lay.val c hl3 hc
    have h10 : t.getReg .x10 = BitVec.ofNat 64 (rowA lay.val c) :=
      hkB (.x10, _) (by rw [bK, if_neg h3]; exact List.mem_append_right _ (List.mem_singleton_self _))
    obtain ⟨d, h12, hdd⟩ := hpost.dst hl3
    have hm (A : Word) : t.getMem A = memEval s (headerWrites lay.val c) A := by
      simpa [specA, h3] using ht.mem A
    have hrowpad : rowA lay.val c + 64 < 25216 := by
      have H : ((List.range 3).all fun l => (List.range (nCopy l)).all fun c =>
        decide (rowA l c + 64 < 25216)) = true := by decide +kernel
      exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp H lay.val
        (List.mem_range.mpr hl3)) c (List.mem_range.mpr hc))
    have hf : ∀ q, q < 64 → q ≠ 16 →
        t.getMem (BitVec.ofNat 64 (rowA lay.val c + q)) = s.getMem (BitVec.ofNat 64 (rowA lay.val c + q)) := by
      intro q hq h16
      rw [hm]
      apply memEval_frame_ofNat s _ _ (by omega)
      intro p hp
      simp only [headerWrites, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl
      simp; omega
    refine ⟨h5, hashArgs_of t (rowA lay.val c) 64 d h10 h11 h12 (by omega) (by decide +kernel) (by omega)
      (by rcases hdd with ⟨hd1, hd2⟩ | rfl <;> omega) (by rcases hdd with ⟨hd1, hd2⟩ | rfl <;> omega), ?_⟩
    change hashInput t = toQ (pad64 (ClaudeWCT.WCT9.pairEncodingInputH lay (route index lay).2 (route index lay).1
      left right (ClaudeWCT.W9.T3M.wbcCtr w index lay) (ClaudeWCT.W9.T3M.wbcPad w index lay)
      (ClaudeWCT.W9.T3M.wbcHigh w index lay)))
    rw [pair_input_block]
    have e := T3M.rowA_eq index lay h3
    have h8 := T3M.rowBlock_mod8 index lay
    have hcoff : ClaudeWCT.W9.T3M.bcCounterOff index lay = 8 * ((rowA lay.val c - WIT) / 8 + 4) := by
      unfold ClaudeWCT.W9.T3M.bcCounterOff; rw [e]; unfold WIT at *; omega
    have hm3 := hmsg.2.2.2 3 (Or.inl rfl)
    have hm4 := hmsg.2.2.2 4 (Or.inr (Or.inl rfl))
    have hm5 := hmsg.2.2.2 5 (Or.inr (Or.inr rfl))
    have hhoff : ClaudeWCT.W9.T3M.rowBlock index lay + 16 = 8 * ((rowA lay.val c - WIT) / 8 + 2) := by
      rw [e]; unfold WIT at *; omega
    apply T3M.row_hash t (rowA lay.val c) (by omega) (by omega) lay _ _ left right _ _ h10 h11
    · exact ⟨(hf 0 (by decide +kernel) (by decide +kernel)).trans hmsg.2.1.1,
        (hf 8 (by decide +kernel) (by decide +kernel)).trans hmsg.2.1.2⟩
    · rw [hm]; unfold headerWrites
      rw [memEval_cons_ofNat _ _ _ _ _ (by omega) (by omega), if_pos rfl]
      simp only [E.eval]
      rw [hs.word hl3, show BC.below lay.val = T3M.below lay.val from rfl, ← hrw]
    · -- C2/C3 (FULL): the root window's high word is witness memory (`wbcHigh`)
      rw [hf 24 (by decide +kernel) (by decide +kernel)]
      unfold ClaudeWCT.W9.T3M.wbcHigh; rw [hhoff]
      have h3' : s.getMem (BitVec.ofNat 64 (rowA lay.val c + 24)) = wword w ((rowA lay.val c - WIT) / 8 + 2 + 1) := by
        simpa using hm3
      rw [h3']; exact (Verify.wdig_hi w _).symm
    · rw [hf 32 (by decide +kernel) (by decide +kernel), hcoff, Verify.wdig_lo]; simpa using hm4
    · rw [hf 40 (by decide +kernel) (by decide +kernel), hcoff, Verify.wdig_hi]; simpa using hm5
    · exact ⟨(hf 48 (by decide +kernel) (by decide +kernel)).trans hmsg.2.2.1.1,
        by rw [show rowA lay.val c + 48 + 8 = rowA lay.val c + 56 by omega,
          hf 56 (by decide +kernel) (by decide +kernel)]; simpa [Nat.add_assoc] using hmsg.2.2.1.2⟩
theorem encoding_setup : EncodingSetup := fun w pk index lay msg s hs => by
  refine ⟨encoding_reject w pk index lay msg s hs, fun hlt => ?_⟩
  obtain ⟨t, ht⟩ := encoding_run w pk index lay msg s hs hlt
  obtain ⟨h5, hv, hin⟩ := setup_hash w pk index lay msg s hs t ht
  exact ⟨t, (by fin_cases lay <;> exact ht.steps), ht.ecall (by fin_cases lay <;> rfl),
    h5, hv, hin, setup_post w pk index lay msg s hs t ht⟩
def EncodingBlocks : Prop := ∀ (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (tree leaf : Nat)
  (msg : LayerMsg) (hi : BitVec 64), (toQ (pad64 (ClaudeWCT.W9.T3M.layerEncodingInputP lay tree leaf msg
    (ClaudeWCT.W9.T3M.wbcCtr w index lay) (ClaudeWCT.W9.T3M.wbcPad w index lay) (ClaudeWCT.W9.T3M.wbcRight w) hi))).blocks = 1
theorem encoding_blocks : EncodingBlocks := fun w index lay tree leaf msg hi => by
  cases msg with
  | forest root =>
    change (toQ (pad64 (ClaudeWCT.WCT9.pairEncodingInputH lay tree leaf root (ClaudeWCT.W9.T3M.wbcRight w)
      (ClaudeWCT.W9.T3M.wbcCtr w index lay) (ClaudeWCT.W9.T3M.wbcPad w index lay) hi))).blocks = 1
    rw [pair_input_block]
    exact blocks_blk4 _ _ _ _
  | pair left right =>
    change (toQ (pad64 (ClaudeWCT.WCT9.pairEncodingInputH lay tree leaf left right
      (ClaudeWCT.W9.T3M.wbcCtr w index lay) (ClaudeWCT.W9.T3M.wbcPad w index lay) hi))).blocks = 1
    rw [pair_input_block]
    exact blocks_blk4 _ _ _ _
end SigGolfCandidate.T3M.BC
end
section
set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64 width maxDigit shortHash leafHash)
def chainsP (w : ClaudeWCT.W9.T3M.WBytes) (lay : Layer) (tree leaf : Nat) (digits : List Nat) : T3.M (List Digest) :=
  (List.finRange (chainCount lay)).mapM fun i =>
    ClaudeWCT.W9.T3M.chainPW lay tree leaf i.val (digits.getD i.val 0) (maxDigit lay i.val - digits.getD i.val 0)
      (ClaudeWCT.W9.T3M.wchainPads w lay i.val).1 (ClaudeWCT.W9.T3M.wchainPads w lay i.val).2
      (ClaudeWCT.W9.T3M.wchainHeaderPad w lay i.val) (ClaudeWCT.W9.T3M.wvalueFor w lay digits i.val)
theorem lctx_rank_eq (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (a : BitVec 256)
    (t : Nat) (ht : t < 14) :
    (lctxOf w index lay a).kOf t = SigGolfCandidate.T3.lowerWord (ansD a) / 2 ^ (9 * t) % 512 := by
  rw [LCtx.kOf_eq _ t ht]
  simp only [lctxOf]
  by_cases h7 : t < 7
  · rw [if_pos h7, Nat.mod_eq_of_lt h7, ← ansD_lo]
    rw [lowerWord_eq]
    have h1 := mod_pow_div_mod (ansD a).toNat 64 (9 * t) 9 (by omega)
    have h2 := mod_pow_div_mod (ansD a).toNat 63 (9 * t) 9 (by omega)
    have h3 := div_mod_add_pow ((ansD a).toNat % 2 ^ 63) ((ansD a).toNat / 2 ^ 64 % 2 ^ 63)
      (9 * t) 63 9 (by omega)
    rw [show (2 : Nat) ^ 9 = 512 from rfl] at h1 h2 h3
    rw [h1, h3, h2]
  · rw [if_neg h7, show t % 7 = t - 7 by omega, ← ansD_hi]
    rw [lowerWord_eq]
    rw [show 9 * t = 63 + 9 * (t - 7) by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul,
      div_add_pow _ _ _ _ (le_refl _), Nat.div_eq_of_lt (Nat.mod_lt _ (by norm_num)), Nat.sub_self,
      Nat.pow_zero, Nat.one_mul, Nat.zero_add]
    have h2 := mod_pow_div_mod ((ansD a).toNat / 2 ^ 64) 63 (9 * (t - 7)) 9 (by omega)
    rw [show (2 : Nat) ^ 9 = 512 from rfl] at h2
    exact h2.symm
theorem lctx_headOK (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (a : BitVec 256)
    (hgood : ClaudeWCT.WCT9.lowerRankGood (ansD a)) (i : Nat) (hi : i < 42) :
    (lctxOf w index lay a).headOK i := by
  intro _ _
  rw [lctx_rank_eq w index lay a (i / 3) (by omega)]
  exact hgood ⟨i / 3, by omega⟩
def guardedChainsP {β : Type} (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer)
    (answer : Digest) (digits : List Nat) (R : List Digest → T3.M (Option β)) : T3.M (Option β) := do
  let some ends ← ClaudeWCT.WCT9.lowerGuardedRun
    (ClaudeWCT.W9.T3M.layerChainP w index lay digits)
    (chainsP w lay (route index lay).2 (route index lay).1 digits) answer | pure none
  R ends
/-- C4: the top fold of the spec (`topFinishP`): the one-word label with the witness high pad and the half by heap
parity (`WCT9.lowerNodeHashP 0`). -/
def merkleP (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (value : Digest) : T3.M Digest :=
  (List.finRange (height lay)).foldlM (fun value j => do
    let other := ClaudeWCT.W9.T3M.wpath w lay (route index lay).1 j.val
    let pair := if (route index lay).1 / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
    ClaudeWCT.WCT9.lowerNodeHashP lay.val (route index lay).2
      (2 ^ (height lay - j.val - 1) + (route index lay).1 / 2 ^ (j.val + 1)) pair.1
      (ClaudeWCT.W9.T3M.wmerkleHigh w lay (route index lay).1 j.val)
      (ClaudeWCT.W9.T3M.wmerklePad w lay (route index lay).1 j.val) pair.2) value
theorem layerP_eq (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (digits : List Nat) :
    ClaudeWCT.W9.T3M.layerP w index 0 digits = chainsP w 0 (route index 0).2 (route index 0).1 digits >>= fun ends =>
      ClaudeWCT.WCT9.leafHashW 0 (route index 0).2 (route index 0).1 (ClaudeWCT.W9.T3M.wtopLeafPad w)
        (ClaudeWCT.W9.T3M.wleafHigh w 0) ends >>= merkleP w index 0 := by
  unfold ClaudeWCT.W9.T3M.layerP chainsP merkleP
  generalize route index 0 = p
  obtain ⟨leaf, tree⟩ := p
  rfl
def layerHead {β : Type} (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (M : ClaudeWCT.WCT9.LayerMsg)
    (R : List Digest → T3.M (Option β)) : T3.M (Option β) :=
  if (ClaudeWCT.W9.T3M.wbcCtr w index lay).toNat ≥ ClaudeWCT.WCT9.verifyWindow then pure none else
  ClaudeWCT.WCT9.encodingHash lay (ClaudeWCT.W9.T3M.layerEncodingInputP lay (route index lay).2 (route index lay).1 M
    (ClaudeWCT.W9.T3M.wbcCtr w index lay) (ClaudeWCT.W9.T3M.wbcPad w index lay) (ClaudeWCT.W9.T3M.wbcRight w)
    (ClaudeWCT.W9.T3M.wbcHigh w index lay)) >>= fun answer =>
    match canonicalDecode lay answer with
    | none => pure none
    | some digits => guardedChainsP w index lay answer digits R
def stB (lay : Nat) : Nat := if lay = 0 then 122 else bSt lay+4
def cyB (lay : Nat) : Nat := if lay = 0 then 68 else bCy lay+4
def lfStepsL : Nat := 4
def chainCost0 (lay : Nat) : Nat := if lay = 0 then 1066 else 2935 - 9 * tgtL lay
def chainFuel (lay : Nat) : Nat := if lay = 0 then 2320 else 1720
def layerCost (lay Z : Nat) : Nat := stepsA lay + 8 + cyB lay + lfStepsL + chainCost0 lay - Z
def layerFuel (lay : Nat) : Nat := stepsA lay + 1 + stB lay + chainFuel lay + lfStepsL
def layerCostA (floors : Layer → Nat) (lay : Nat) : Nat :=
  layerCost lay 0 - floors (Fin.ofNat 4 lay)
theorem layerCostA_low (floors : Layer → Nat) (lay : Layer) (h : lay ≠ 0) :
    layerCostA floors lay.val = layerCost lay.val 0 - floors lay := by
  fin_cases lay <;> rfl
/-- Stage 2 (C2 + C3): one head step (L3: the row high-word store; L1/L2: the row high-word store) and one leaf
setup step (the leaf tweak high-word clear) fewer than stage 1 (1182/1175/1175). -/
theorem layerCost_vals : layerCost 3 0 = 1181 ∧ layerCost 2 0 = 1173 ∧ layerCost 1 0 = 1173 := by decide +kernel
theorem layerFuel_vals : layerFuel 3 = 1765 ∧ layerFuel 2 = 1757 ∧ layerFuel 1 = 1757 := by decide +kernel
theorem ckOf_lt (lay : Layer) (hlay : lay ≠ 0) (a : BitVec 256) (ds : List Nat)
    (hds : canonicalDecode lay (ansD a) = some ds) : ckOf lay a < 8 := by
  rw [canonical_decode_lower_v6 lay hlay] at hds
  split_ifs at hds with h1 h2
  unfold ckOf; rw [tgtL_eq]; exact h2
theorem s6v_chainBlock (lay : Layer) (h : lay ≠ 0) :
    s6v lay.val = Verify.WIT + ClaudeWCT.W9.T3M.layerBase lay + 16 * ClaudeWCT.W9.T3M.pathSlots lay + 520 := by
  fin_cases lay
  · exact absurd rfl h
  all_goals decide +kernel
theorem lctx_prefix_eq (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (a : BitVec 256)
    (hlay : lay ≠ 0) (ds : List Nat) (hds : canonicalDecode lay (ansD a) = some ds) (n : Nat) (hn : n ≤ 42) :
    (List.range' 0 n).foldlM (lctxOf w index lay a).chainF [] =
      (List.range n).mapM (ClaudeWCT.W9.T3M.layerChainP w index lay ds) := by
  set L := lctxOf w index lay a
  have hD := lctx_digits w index lay a hlay ds hds
  have hF : (List.range' 0 n).foldlM L.chainF [] = (fun xs => [] ++ xs) <$>
      (List.range' 0 n).mapM (fun i => L.rest i (L.dig i) (L.bufferVal i)) := foldlM_app_mapM _ n 0 []
  rw [hF]
  simp only [List.nil_append, id_map']
  rw [List.range_eq_range']
  apply mapM_congr'
  intro i hi
  have hi' : i < 43 := by have := List.mem_range'_1.mp hi; omega
  have hc : i < chainCount lay := by rw [LCtx.chainCount_lower lay hlay]; omega
  rw [L.fit_chain hlay rfl ds hD (s6v_chainBlock lay hlay) i hi']
  unfold LCtx.coreChain ClaudeWCT.W9.T3M.layerChainP
  rw [Nat.mod_eq_of_lt hc]
  rfl
theorem chainCount_top : chainCount (0 : Layer) = 51 := by decide +kernel
theorem layerCost_low (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (hlay : lay ≠ 0) (a : BitVec 256)
    (ds : List Nat) (hds : canonicalDecode lay (ansD a) = some ds) :
    stepsA lay.val + 8 + (bCy lay.val+4) + (lctxOf w index lay a).lowCost + lfStepsL =
      layerCost lay.val ((lctxOf w index lay a).zSum 0 43 + 4*(lctxOf w index lay a).savedCopies 0 43) := by
  have h0 : lay.val ≠ 0 := fun h => hlay (Fin.ext h)
  have hD := lctx_digits w index lay a hlay ds hds
  have hsum := LCtx.canonical_decode_lower_sum lay hlay _ ds hds
  have hck : (lctxOf w index lay a).ck < 8 := ckOf_lt lay hlay a ds hds
  have hacc := (lctxOf w index lay a).lowCost_accept hck ds hD hsum.1 (canonicalTarget lay) hsum.2
  rw [← tgtL_eq] at hacc
  simp only [layerCost, cyB, chainCost0, if_neg h0]
  omega
theorem count_range'_eq (f : Nat → Nat) (P : Nat → Prop) [DecidablePred P] (hf : ∀ j, f j = if P j then 1 else 0) :
    ∀ n a, ((List.range' a n).map f).sum = ((List.range' a n).filter fun j => decide (P j)).length := by
  intro n
  induction n with
  | zero => intro a; simp
  | succ n ih =>
    intro a
    rw [List.range'_succ, List.map_cons, List.sum_cons, List.filter_cons, ih (a + 1), hf a]
    by_cases h : P a <;> simp [h] <;> omega
theorem zSum_eq_wordCredit (c : LCtx) (lay : Layer) (hlay : lay ≠ 0) (D : List Nat)
    (hD : ∀ i < 43, c.dig i = D.getD i 0) : c.zSum 0 43 = ClaudeWCT.WCT9.wordCredit lay D := by
  have hn := LCtx.chainCount_lower lay hlay
  have hw : ∀ i, maxDigit lay i = 7 := fun i => by simp [maxDigit, hlay]
  unfold LCtx.zSum ClaudeWCT.WCT9.wordCredit
  rw [hn, List.range_eq_range', count_range'_eq _ (fun j => c.dig j = 6) (fun j => by simp [LCtx.zc])]
  congr 1
  apply List.filter_congr
  intro j hj
  have hj' := (List.mem_range'_1.mp hj).2
  rw [hw j, hD j (by omega)]
  simp only [decide_eq_decide]
  omega
theorem savedCopies_eq (c : LCtx) (hlay : c.lay ≠ 0) (D : List Nat)
    (hD : ∀ i < 43, c.dig i = D.getD i 0) :
    c.savedCopies 0 43 = ClaudeWCT.WCT9.savedCopies c.lay D := by
  unfold LCtx.savedCopies ClaudeWCT.WCT9.savedCopies
  rw [LCtx.chainCount_lower c.lay hlay, List.range_eq_range',
    count_range'_eq _ (fun j => c.bufferSafe j) (fun j => by simp [LCtx.savedCopy])]
  congr 1
  apply List.filter_congr
  intro j hj
  rw [decide_eq_decide]
  exact c.bufferSafe_iff hlay D hD j (by have := List.mem_range'_1.mp hj; omega)
open SphincsSecurity (bytesLE bytesLE_length) in
theorem encQ_of_row (lay : Layer) (a : Digest) (tr lf : Nat) (hi : BitVec 64) (rest : List UInt8)
    (hl : (bytesLE 16 a ++ bytesLE 16 (hi ++ T3.hyperWord lay.val (tr * 2 ^ height lay + lf)) ++ rest).length ≤ 64) :
    EncQ lay.val (toQ (pad64 (bytesLE 16 a ++ bytesLE 16 (hi ++ T3.hyperWord lay.val (tr * 2 ^ height lay + lf)) ++
      rest))) := by
  unfold EncQ
  refine ⟨pad64 (bytesLE 16 a ++ bytesLE 16 (hi ++ T3.hyperWord lay.val (tr * 2 ^ height lay + lf)) ++ rest), ?_, rfl,
    ⟨tr * 2 ^ height lay + lf, hi, ?_⟩⟩
  · simp only [pad64, List.length_append, List.length_replicate, bytesLE_length] at hl ⊢
    omega
  · unfold pad64
    rw [List.append_assoc, List.append_assoc, List.drop_left' (bytesLE_length 16 a),
      List.take_left' (bytesLE_length 16 _)]
    try rfl
open SphincsSecurity (bytesLE bytesLE_length) in
theorem encQ_layer (lay : Layer) (tree leaf : Nat) (M : ClaudeWCT.WCT9.LayerMsg) (c : BitVec 32) (pad : BitVec 96)
    (padR : Digest) (hi : BitVec 64) :
    EncQ lay.val (toQ (pad64 (ClaudeWCT.W9.T3M.layerEncodingInputP lay tree leaf M c pad padR hi))) := by
  cases M with
  | forest root =>
    change EncQ lay.val (toQ (pad64 (bytesLE 16 root ++
      bytesLE 16 (hi ++ T3.hyperWord lay.val (tree * 2 ^ height lay + leaf)) ++
      bytesLE 4 c ++ bytesLE 12 pad ++ bytesLE 16 padR)))
    simp only [List.append_assoc]
    rw [← List.append_assoc (bytesLE 16 root)]
    exact encQ_of_row lay root tree leaf hi _ (by simp only [List.length_append, bytesLE_length]; omega)
  | pair left right =>
    change EncQ lay.val (toQ (pad64 (bytesLE 16 left ++
      bytesLE 16 (hi ++ T3.hyperWord lay.val (tree * 2 ^ height lay + leaf)) ++
      bytesLE 4 c ++ bytesLE 12 pad ++ bytesLE 16 right)))
    simp only [List.append_assoc]
    rw [← List.append_assoc (bytesLE 16 left)]
    exact encQ_of_row lay left tree leaf hi _ (by simp only [List.length_append, bytesLE_length]; omega)
/-- Configuration (1)+(2): the hash hypothesis `HashOkBy floors high` is path-aware; a LOW selection costs `bCy`
(4 less than HIGH) and earns the `pathBonus` 4, so the accepted cost stays `layerCost - floors`. -/
theorem layer_good_low (floors : Layer → Nat) (hbound : ∀ lay, floors lay ≤ 301) (high : Bool) (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer) (hlay : lay ≠ 0) (M : ClaudeWCT.WCT9.LayerMsg)
    (s : MachineState) (hs : LayerIn w pk index lay.val M s) {β : Type} (R : List Digest → T3.M (Option β))
    (K : Option β → OracleComp HashSpec Obs) (hK0 : K none = pure (false, 0)) (N C A : Nat) (Q : Prop)
    (hR : ∀ ends u, LeafOut w pk index lay ends u → GoodQP (HashOkBy floors high) u N C Q A (ccM (R ends) K)) :
    GoodQP (HashOkBy floors high) s (N + layerFuel lay.val) (C + layerCost lay.val 0) Q (A + layerCostA floors lay.val)
      (ccM (layerHead w index lay M R) K) := by
  have h0 : lay.val ≠ 0 := fun h => hlay (Fin.ext h)
  have hlf : lfStepsL = 4 := rfl
  have hidx := hs.idx
  have hA := BC.encoding_setup w pk index lay M s hs
  have hT : 9 * tgtL lay.val ≤ 2935 := by fin_cases lay <;> decide +kernel
  have hF : floors lay + 9 * tgtL lay.val ≤ 2935 := by
    have hb := hbound lay
    have ht : tgtL lay.val ≤ 201 := by fin_cases lay <;> decide +kernel
    omega
  have hfuel : layerFuel lay.val = stepsA lay.val + 1 + (bSt lay.val+4) + 1720 + lfStepsL := by
    simp [layerFuel, stB, chainFuel, h0]
  have hcost : layerCost lay.val 0 = stepsA lay.val + 8 + (bCy lay.val+4) + lfStepsL + (2935 - 9 * tgtL lay.val) := by
    simp only [layerCost, cyB, chainCost0, if_neg h0]; omega
  have hcostA : layerCostA floors lay.val = stepsA lay.val + 8 + (bCy lay.val+4) + lfStepsL +
      (2935 - 9 * tgtL lay.val - floors lay) := by
    rw [layerCostA_low floors lay hlay, hcost]; omega
  have hbS : 25 ≤ (bSt lay.val+4) := by unfold bSt; split_ifs <;> omega
  have hbC : 28 ≤ (bCy lay.val+4) := by unfold bCy; split_ifs <;> omega
  have hrej : BC.rejectSteps lay.val ≤ stepsA lay.val + 21 := by
    unfold BC.rejectSteps; split_ifs <;> omega
  unfold layerHead
  by_cases hctr : (ClaudeWCT.W9.T3M.wbcCtr w index lay).toNat ≥ ClaudeWCT.WCT9.verifyWindow
  · rw [if_pos hctr, ccM_pure, hK0]
    obtain ⟨u, hst, hf, h5, h10⟩ := hA.1 hctr
    exact GoodQP.stepsQ hst (GoodQP.reject (Q := Q) (A := 0) hf h5 h10) (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
  · rw [if_neg hctr]
    obtain ⟨t, hst, hf, h5, hv, hin, hpre⟩ := hA.2 (by omega)
    have hblk := BC.encoding_blocks w index lay (route index lay).2 (route index lay).1 M
      (ClaudeWCT.W9.T3M.wbcHigh w index lay)
    have hq := encQ_layer lay (route index lay).2 (route index lay).1 M (ClaudeWCT.W9.T3M.wbcCtr w index lay)
      (ClaudeWCT.W9.T3M.wbcPad w index lay) (ClaudeWCT.W9.T3M.wbcRight w) (ClaudeWCT.W9.T3M.wbcHigh w index lay)
    have H : ∀ a : BitVec 256, GoodQP (fun hash => hash (toQ (pad64 (ClaudeWCT.W9.T3M.layerEncodingInputP lay
        (route index lay).2 (route index lay).1 M (ClaudeWCT.W9.T3M.wbcCtr w index lay) (ClaudeWCT.W9.T3M.wbcPad w index lay)
        (ClaudeWCT.W9.T3M.wbcRight w) (ClaudeWCT.W9.T3M.wbcHigh w index lay)))) = a ∧
          HashOkBy floors high hash) (writeHash t a) (N + lfStepsL + 1720 + (bSt lay.val+4))
        (C + lfStepsL + (2935 - 9 * tgtL lay.val) + (bCy lay.val+4))
        Q (A + lfStepsL + (2935 - 9 * tgtL lay.val - floors lay) + (bCy lay.val+4))
        (ccM (match canonicalDecode lay (ansD (selectedView a)) with
          | none => pure none
          | some digits => guardedChainsP w index lay (ansD (selectedView a)) digits R) K) := by
      intro a
      have hB := encB_step w pk index lay hlay _ (cpIdx_lt index lay.val lay.isLt) hidx t hpre a
      cases hds : canonicalDecode lay (ansD (selectedView a)) with
      | none =>
        dsimp only
        rw [ccM_pure, hK0]
        obtain ⟨v, k, cy, hst', hrejected, hk, hcy⟩ := hB.1 hds
        have hrej : GoodQP (HashOkBy floors high) v 1 1 Q 0 (pure (false,0)) := by
          rcases hrejected with hf' | ⟨hf',h5',h10'⟩
          · exact (GoodQP.fetch_none (Q := Q) (A := 0) hf').mono (by omega) (by omega) (fun h => ⟨h,by omega⟩)
          · exact GoodQP.reject hf' h5' h10'
        exact (GoodQP.stepsQ hst' hrej (by omega) (by omega)
          (fun hq => ⟨hq, by omega⟩)).pre_mono (fun _ h => h.2)
      | some ds =>
        dsimp only
        obtain ⟨s0, k0, cy0, hst0, hk0, hcy0, hLok, hkn, hO0, hIn, hG0, hOr0, h23, h30, h1, hBuf0⟩ := hB.2 (by rw [hds]; simp)
        set L := lctxOf w index lay (selectedView a) with hLd
        have hD := lctx_digits w index lay (selectedView a) hlay ds hds
        have hsum := LCtx.canonical_decode_lower_sum lay hlay _ ds hds
        have hck : L.ck < 8 := ckOf_lt lay hlay (selectedView a) ds hds
        have hacc := L.lowCost_accept hck ds hD hsum.1 (canonicalTarget lay) hsum.2
        rw [← tgtL_eq] at hacc
        have hcr : L.zSum 0 43 = ClaudeWCT.WCT9.wordCredit lay ds := zSum_eq_wordCredit L lay hlay ds hD
        have hsave : L.savedCopies 0 43 = ClaudeWCT.WCT9.savedCopies lay ds := savedCopies_eq L hlay ds hD
        have hP := L.lowP_eq hlay rfl ds hD (s6v_chainBlock lay hlay)
        by_cases hgood : ClaudeWCT.WCT9.lowerRankGood (ansD (selectedView a))
        · simp only [guardedChainsP, ClaudeWCT.WCT9.lowerGuardedRun_of_good _ _ _ hgood, bind_map_left]
          have hG := L.lower_good hLok rfl rfl hck (lctx_headOK w index lay (selectedView a) hgood) hkn hO0 (fun ends => ccM (R ends) K) (N + lfStepsL) (C + lfStepsL) (A + lfStepsL) Q
            (fun ends t ht => by
              obtain ⟨u, hstu, hu⟩ := leafL_step w pk index lay hlay hidx (selectedView a) s0 hkn hck hG0 hOr0 h23 h30 h1 hBuf0 ends t ht
              exact GoodQP.stepsQ hstu (hR ends u hu) (by unfold lfStepsL; omega) (by unfold lfStepsL; omega)
                (fun hq => ⟨hq, by unfold lfStepsL; omega⟩))
            s0 hIn
          have e : chainsP w lay (route index lay).2 (route index lay).1 ds = L.lowP := by
            rw [hP]; unfold chainsP; rw [LCtx.chainCount_lower lay hlay]; rfl
          rw [ccM_bind, e]
          have body : ∀ k, k ≤ L.zSum 0 43 + 4*L.savedCopies 0 43 + (if T3.lowerSpare (ansD a) then 4 else 0) →
              GoodQP (HashOkBy floors high) (writeHash t a) (N + lfStepsL + 1720 + (bSt lay.val+4))
                (C + lfStepsL + (2935 - 9 * tgtL lay.val) + (bCy lay.val+4))
                Q (A + lfStepsL + (2935 - 9 * tgtL lay.val - k) + (bCy lay.val+4))
                (ccM L.lowP (fun ends => ccM (R ends) K)) := fun k hk =>
            GoodQP.stepsQ hst0 hG (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
          by_cases hcf : floors lay ≤ ClaudeWCT.WCT9.wordCredit lay ds + 4*ClaudeWCT.WCT9.savedCopies lay ds +
              (if T3.lowerSpare (ansD a) then 4 else 0)
          · exact (body _ (by omega)).pre_mono (fun _ h => h.2)
          · refine GoodQP.of_false_pre (body 0 (Nat.zero_le _)) ?_
            rintro hash ⟨hea, hok⟩
            have hh := hok lay _ hq ds (by
              rw [hea, ClaudeWCT.WCT9.verificationAnswer_lower lay hlay, ← selectedView_answer lay hlay]; exact hds)
            rw [hea, ClaudeWCT.WCT9.verificationLow_lower lay hlay] at hh
            apply hcf
            by_cases hsp : T3.lowerSpare (ansD a)
            · simpa [ClaudeWCT.WCT9.dispatchPenalty, ClaudeWCT.WCT9.CanonicalPolicy.pathReward,
                ClaudeWCT.WCT9.CanonicalPolicy.pathBonus, ClaudeWCT.WCT9.CanonicalPolicy.reward, ClaudeWCT.WCT9.lowSelected,
                hlay, hsp] using hh
            · simpa [ClaudeWCT.WCT9.dispatchPenalty, ClaudeWCT.WCT9.CanonicalPolicy.pathReward,
                ClaudeWCT.WCT9.CanonicalPolicy.pathBonus, ClaudeWCT.WCT9.CanonicalPolicy.reward, ClaudeWCT.WCT9.lowSelected,
                hlay, hsp] using hh
        · have hj := ClaudeWCT.WCT9.lowerFirstBad_lt (ansD (selectedView a)) hgood
          have hbad : L.kOf (ClaudeWCT.WCT9.lowerFirstBad (ansD (selectedView a))) <
              rankFloor (ClaudeWCT.WCT9.lowerFirstBad (ansD (selectedView a))) := by
            rw [lctx_rank_eq w index lay (selectedView a) _ hj]
            exact ClaudeWCT.WCT9.lowerFirstBad_bad (ansD (selectedView a)) hgood
          have hranks : ∀ i, i < 3 * ClaudeWCT.WCT9.lowerFirstBad (ansD (selectedView a)) → L.headOK i := by
            intro i hi _ _
            rw [lctx_rank_eq w index lay (selectedView a) _ (by omega)]
            exact ClaudeWCT.WCT9.lowerFirstBad_before (ansD (selectedView a)) hgood (i / 3) (by omega)
          have hpref := L.chains_prefix_fault (P := HashOkBy floors high) hLok rfl rfl hkn hO0 _ hj hbad hranks s0 hIn
          have hpcost := L.chainsCost_prefix_le (3 * ClaudeWCT.WCT9.lowerFirstBad (ansD (selectedView a))) (by omega)
          have hle : L.chainsCost 0 42 ≤ L.lowCost := by unfold LCtx.lowCost; omega
          simp only [guardedChainsP, ClaudeWCT.WCT9.lowerGuardedRun, if_neg hgood, bind_assoc, pure_bind,
            ccM_bind, ccM_pure, hK0]
          rw [← lctx_prefix_eq w index lay (selectedView a) hlay ds hds _ (by omega)]
          exact (GoodQP.stepsQ hst0 hpref (by omega) (by omega) (fun hf => hf.elim)).pre_mono
            (fun _ h => h.2)
    have := GoodQP.encodingHash_bind_pre (f := fun answer => match canonicalDecode lay answer with
      | none => pure none
      | some digits => guardedChainsP w index lay answer digits R) hf h5 hv hin (fun a => by simpa only [selectedView_answer lay hlay] using H a)
    rw [hblk] at this
    exact (GoodQP.steps' hst this (by omega) (by omega) (by omega))
theorem layerIn_of_fts (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (idx : Nat) (left right : Digest) (u : MachineState)
    (hidx : idx < 2 ^ 31) (hglob : Glob [(.x5, 0)] w pk u) (hreg : u.getReg .x22 = BitVec.ofNat 64 idx)
    (hpc : u.pc = pcOf 854) (hleft : DigAt u WIT left) (hright : DigAt u (WIT + 48) right)
    (hwit : Verify.Orig w (fun o => (24 ≤ o ∧ o < 48) ∨ (7664 ≤ o ∧ o < 21984)) u)
    (hbase8 : u.getReg .x8 = BitVec.ofNat 64 (WIT + 80)) (ha1 : u.getReg .x11 = 64)
    (hs10 : u.getReg .x26 = 6) (hOne : u.getReg .x7 = 1) (hTwo : u.getReg .x13 = 2) (hSeven : u.getReg .x30 = 7)
    (hThree : u.getReg .x19 = 3) (hFour : u.getReg .x20 = 4) (hFive : u.getReg .x21 = 5)
    (hCoord : u.getReg .x6 = 0x10000)
    (hbase : u.getReg .x2 = BitVec.ofNat 64 0xffbde0)
    (htop : ∀ k, k < 5 → u.getMem (BitVec.ofNat 64 (TOPLOAD + 8 * k)) =
      BitVec.ofNat 64 (topWords.getD k 0))
    (htop8 : u.getMem (BitVec.ofNat 64 (TOPLOAD - 8)) = BitVec.ofNat 64 21328)
    (ha2 : u.getReg .x12 = BitVec.ofNat 64 4112 ∨ u.getReg .x12 = BitVec.ofNat 64 4176)
    (hd0 : u.getMem (BitVec.ofNat 64 (TOPB9 - 304)) = 0xFFF) :
    ∃ t, Steps image u 0 0 t ∧ LayerIn w pk idx 3 (.pair left right) t := by
  have hpk : preK 3 = [(.x5, 0)] ++ [(.x8, BitVec.ofNat 64 4208), (.x11, 64), (.x26, 6), (.x7, 1), (.x13, 2), (.x30, 7),
      (.x2, BitVec.ofNat 64 0xffbde0), (.x19, 3), (.x20, 4), (.x21, 5), (.x6, 0x10000)] := rfl
  have hk : ∀ p ∈ preK 3, u.getReg p.1 = p.2 := by
    intro p hp
    rw [hpk] at hp
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hglob.1 _ (by simp)
    · exact hbase8
    · exact ha1
    · exact hs10
    · exact hOne
    · exact hTwo
    · exact hSeven
    · exact hbase
    · exact hThree
    · exact hFour
    · exact hFive
    · exact hCoord
  refine ⟨u, Steps.refl u, ⟨by norm_num, hidx, hpc, ⟨hk, hglob.2⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ => ha2, fun _ => hd0⟩⟩
  · rw [show rReg 3 = .x22 from rfl, show BC.below 3 = 0 from rfl, pow_zero, Nat.div_one, hreg]
  · intro h
    exact absurd h (by decide +kernel)
  · exact ⟨hleft, hright, hwit.word 24 (by decide) (by unfold WX; decide) (Or.inl ⟨le_refl _, by decide⟩)⟩
  · exact hwit.mono (fun o ho => Or.inr ⟨ho.1, lt_of_lt_of_le ho.2 (by decide +kernel)⟩)
  · intro _
    exact ⟨(htop 4 (by decide +kernel)).trans (by decide +kernel), htop8, htop⟩
  · intro h
    exact absurd h (by decide +kernel)
  · exact hwit.mono (fun o ho => Or.inr ⟨by have hh : 18928 ≤ o := ho.1; omega,ho.2⟩)
theorem tree_next (index : Nat) (L : Layer) (h : L ≠ 0) : (route index L).2 = index / 2 ^ below (L.val - 1) := by
  rw [route_snd]
  fin_cases L
  · exact absurd rfl h
  all_goals rfl
theorem layerEnd_prev (L : Layer) (h : L ≠ 0) : layerEnd (L.val - 1) = ClaudeWCT.W9.T3M.layerBase L := by
  fin_cases L
  · exact absurd rfl h
  all_goals decide +kernel
end SigGolfCandidate.T3M
end
end
end
-- ==== merged from T3M_Verify_MerkleSem ====
section

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

section
set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.T3M
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount pad64 shortHash leafHash header)
theorem mkSpec_run {allow : List Nat} {rel : List Reg} {gk known post : List (Reg × Word)}
    {stops : List Nat} {n : Nat} {dirs : List Dir} {sp : Spec} {obl : List Oblig} {keep : List Reg}
    (h : mkSpecB allow rel gk known stops n dirs sp obl post keep = true)
    (s : MachineState) (hpc : s.pc = pcOf n) (hk : KnownOK known s)
    (hbr : ∀ b ∈ sp.brs, b.holds s) (hob : ∀ o ∈ obl, o.holds s) :
    ∃ t, SpecRes allow rel gk sp post keep s t := by
  obtain ⟨t, ht⟩ := spec_run h s hpc hk hbr hob
  refine ⟨t, { ht with known := ?_, keep := ?_ }⟩
  · intro p hp
    exact ht.known p (List.mem_append_left _ hp)
  · intro r hr
    by_cases he : ∃ p ∈ known, p.1 = r
    · obtain ⟨p, hp, er⟩ := he
      have hpk : p ∈ mkKnownKeep known keep := by simp [mkKnownKeep, hp, er, hr]
      have ht' := ht.known p (List.mem_append_right _ hpk)
      rw [← er]
      exact ht'.trans (hk p hp).symm
    · have hany : known.any (fun p => p.1 == r) = false := by
        apply Bool.eq_false_iff.mpr
        intro h
        obtain ⟨p, hp, hpr⟩ := List.any_eq_true.mp h
        exact he ⟨p, hp, by simpa using hpr⟩
      exact ht.keep r (by simp [mkUnknownKeep, hr, hany])
/-- Heap of the fold at level `j` of the path of `index` in layer `lay`. -/
abbrev mkHp (index : Nat) (lay : Layer) (j : Nat) : Nat := 2 ^ (height lay - j - 1) + (route index lay).1 / 2 ^ (j + 1)
/-- C2: the witness high tweak word of a lower fold window (bytes 24..32 of the window, `wmerkleHigh`). -/
def mkHw (w : ClaudeWCT.W9.T3M.WBytes) (lay : Layer) (leaf j : Nat) : BitVec 64 :=
  (ClaudeWCT.W9.T3M.wdig w (mkBo lay.val leaf j + 16)).extractLsb' 64 64
/-- The fold tweak: the one-word label `merkleWord` (C2 lower: `lowerNodeWord`; C4 top: `topNodeWord heap`) with the
witness high word. -/
def mkTw (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (j : Nat) : BitVec 128 :=
  mkHw w lay (route index lay).1 j ++ ClaudeWCT.WCT9.merkleWord lay.val (route index lay).2 (mkHp index lay j)
def mkIn (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (value : Digest) (j : Nat) : List UInt8 :=
  let other := ClaudeWCT.W9.T3M.wpath w lay (route index lay).1 j
  let pair := if (route index lay).1 / 2 ^ j % 2 = 0 then (value, other) else (other, value)
  blk4 pair.1 (mkTw w index lay j) (ClaudeWCT.W9.T3M.wmerklePad w lay (route index lay).1 j) pair.2
/-- One fold of the image: C2 lower folds keep the half `lowerHigh lay heap` (HIGH for even heaps). -/
def mkStep (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (value : Digest) (j : Nat) : T3.M Digest :=
  Verify.vHash (ClaudeWCT.WCT9.lowerHigh lay.val (mkHp index lay j)) (mkIn w index lay value j)
theorem mkFinRange_map_val (n : Nat) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp
theorem mkStep_eq (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (value : Digest) (j : Nat) :
    mkStep w index lay value j = Verify.vHash (ClaudeWCT.WCT9.lowerHigh lay.val (mkHp index lay j)) (mkIn w index lay value j) := rfl
theorem mkIn_length (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (value : Digest) (j : Nat) :
    (mkIn w index lay value j).length = 64 := blk4_length _ _ _ _
theorem mkIn_blocks (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (value : Digest) (j : Nat) :
    (toQ (pad64 (mkIn w index lay value j))).blocks = 1 := blocks_blk4 _ _ _ _
def mkCi (lay k : Nat) : Nat := if lay = 0 ∧ 6 ≤ k then 1 else 0
def mkSh (lay ci leaf : Nat) : Nat := leaf / 2 ^ mkLo lay ci % 2 ^ mkBits lay ci
def mkEc (lay leaf k : Nat) : Nat :=
  BC.mkShp lay (mkCi lay k) (mkSh lay (mkCi lay k) leaf) + mkOff lay (mkCi lay k) (k - mkLo lay (mkCi lay k)) + 1
def mkFin (lay leaf : Nat) : Nat :=
  BC.mkShp lay (mkNch lay - 1) (mkSh lay (mkNch lay - 1) leaf) + mkOff lay (mkNch lay - 1) (mkBits lay (mkNch lay - 1)) + (if lay = 0 then 0 else 1)
def mkLvlSt (lay k : Nat) : Nat := mkBody lay k + mkMove lay k + (if lay = 0 ∧ k = 5 then 2 else 0)
theorem mk_facts (lay k : Nat) (hlay : lay < 4) (hk : k < hL lay) :
    mkCi lay k < mkNch lay ∧ mkLo lay (mkCi lay k) ≤ k ∧ k - mkLo lay (mkCi lay k) < mkBits lay (mkCi lay k) ∧
    mkIsDisp lay (mkCi lay k) (k - mkLo lay (mkCi lay k)) = decide (lay = 0 ∧ k = 5) ∧
    (k + 1 < hL lay → ¬ (lay = 0 ∧ k = 5) → mkCi lay (k + 1) = mkCi lay k ∧
      k + 1 - mkLo lay (mkCi lay k) = k - mkLo lay (mkCi lay k) + 1 ∧
      k - mkLo lay (mkCi lay k) + 1 < mkBits lay (mkCi lay k)) ∧
    (k + 1 = hL lay → mkCi lay k = mkNch lay - 1 ∧ ¬ (k - mkLo lay (mkCi lay k) + 1 < mkBits lay (mkCi lay k)) ∧
      k - mkLo lay (mkCi lay k) + 1 = mkBits lay (mkCi lay k)) := by
  interval_cases lay
  · change k < 12 at hk; interval_cases k <;> decide +kernel
  · change k < 7 at hk; interval_cases k <;> decide +kernel
  · change k < 6 at hk; interval_cases k <;> decide +kernel
  · change k < 6 at hk; interval_cases k <;> decide +kernel
theorem mk_disp_facts : mkCi 0 5 = 0 ∧ mkLo 0 0 = 0 ∧ mkCi 0 6 = 1 ∧ mkLo 0 1 = 6 ∧ mkBits 0 0 = 6 ∧ mkBits 0 1 = 6 ∧
    mkNch 0 = 2 := by decide +kernel
theorem mkLvlSt_ne (lay k : Nat) (h : ¬ (lay = 0 ∧ k = 5)) : mkLvlSt lay k = mkBody lay k + mkMove lay k := by
  simp [mkLvlSt, h]
theorem mkBlk_bit (E b n k : Nat) (hk : k < n) : E / 2 ^ b % 2 ^ n / 2 ^ k % 2 = E / 2 ^ (b + k) % 2 := by
  have h1 : 2 ^ n = 2 ^ k * 2 ^ (n - k) := by rw [← Nat.pow_add]; congr 1; omega
  rw [h1, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega)), Nat.div_div_eq_div_mul,
    ← Nat.pow_add]
theorem mkSh_bit (lay ci leaf kk : Nat) (hkk : kk < mkBits lay ci) :
    mkSh lay ci leaf / 2 ^ kk % 2 = leaf / 2 ^ (mkLo lay ci + kk) % 2 := mkBlk_bit _ _ _ _ hkk
theorem mkSh_lt (lay ci leaf : Nat) : mkSh lay ci leaf < 2 ^ mkBits lay ci := Nat.mod_lt _ (Nat.two_pow_pos _)
theorem mkBit_lt (x k : Nat) : x / 2 ^ k % 2 < 2 := Nat.mod_lt _ (by decide +kernel)
theorem mkBase_eq (lay : Layer) : mkBase lay.val = ClaudeWCT.W9.T3M.layerBase lay := by fin_cases lay <;> rfl
theorem mkPS_eq (lay : Layer) : mkPS lay.val = ClaudeWCT.W9.T3M.pathSlots lay := by fin_cases lay <;> rfl
theorem mkBase_ge (lay : Nat) (hlay : lay < 4) : 7664 ≤ mkBase lay ∧ mkBase lay % 8 = 0 := by
  interval_cases lay <;> decide +kernel
theorem mkBo_low (lay leaf k : Nat) (_h0 : lay ≠ 0) : mkBo lay leaf k = mkBase lay + 16 * plan lay leaf k := rfl
theorem mkBo_plan (lay leaf k : Nat) : mkBo lay leaf k = mkBase lay + 16 * plan lay leaf k := rfl
theorem topPlanA_eq : topPlanA = ClaudeWCT.W9.T3M.topPlanA := rfl
theorem topPlanB_eq : topPlanB = ClaudeWCT.W9.T3M.topPlanB := rfl
theorem topPlan_eq (leaf j : Nat) : topPlan leaf j = ClaudeWCT.W9.T3M.topPlanSlot leaf j := by
  unfold topPlan ClaudeWCT.W9.T3M.topPlanSlot; rw [topPlanA_eq, topPlanB_eq]
theorem mkBo_eq (lay : Layer) (leaf k : Nat) (hleaf : leaf < 2 ^ hL lay.val) :
    mkBo lay.val leaf k = ClaudeWCT.W9.T3M.merkleBlock lay leaf k := by
  unfold ClaudeWCT.W9.T3M.merkleBlock
  rw [← mkBase_eq]
  by_cases h0 : lay.val = 0
  · rw [if_pos h0, mkBo_plan]; unfold plan; rw [if_pos h0, topPlan_eq]
  · rw [if_neg h0, mkBo_low _ _ _ h0]
    congr 2
    unfold plan ClaudeWCT.W9.T3M.lowerPlan
    rw [if_neg h0]
    fin_cases lay
    · exact absurd rfl h0
    · simp only [hL, List.getD_cons_succ, List.getD_cons_zero] at hleaf
      simp [Nat.mod_eq_of_lt (show leaf < 128 by simpa using hleaf), planL1, ClaudeWCT.W9.T3M.lowerPlanL1]
    · simp only [hL, List.getD_cons_succ, List.getD_cons_zero] at hleaf
      simp [Nat.mod_eq_of_lt (show leaf < 64 by simpa using hleaf), planL32, ClaudeWCT.W9.T3M.lowerPlanL32]
    · simp only [hL, List.getD_cons_succ, List.getD_cons_zero] at hleaf
      simp [Nat.mod_eq_of_lt (show leaf < 64 by simpa using hleaf), planL32, ClaudeWCT.W9.T3M.lowerPlanL32]
theorem mkCi_ok (lay k : Nat) : lay = 0 ∨ mkCi lay k = 0 := by
  by_cases h : lay = 0
  · exact Or.inl h
  · exact Or.inr (by simp [mkCi, h])
/-- C4: the chunk's representative leaf (`mkLeafOf`) has the window of `leaf` on every level of the chunk. -/
theorem mkPlan_sh (lay leaf k : Nat) (hlay : lay < 4) (hleaf : leaf < 2 ^ hL lay) (hk : k < hL lay) :
    plan lay (mkLeafOf lay (mkCi lay k) (mkSh lay (mkCi lay k) leaf)) k = plan lay leaf k := by
  by_cases hl : lay = 0
  · subst hl
    have hl4 : leaf < 4096 := by simpa [hL] using hleaf
    have hk12 : k < 12 := by simpa [hL] using hk
    unfold plan topPlan; rw [if_pos rfl, if_pos rfl]
    by_cases h6 : k < 6
    · have hc : mkCi 0 k = 0 := by simp [mkCi]; omega
      rw [hc, if_pos h6, if_pos h6]
      congr 2
      simp only [mkLeafOf, mkSh, mkLo, mkBits]; norm_num
    · have hc : mkCi 0 k = 1 := by simp [mkCi]; omega
      rw [hc, if_neg h6, if_neg h6]
      congr 2
      simp only [mkLeafOf, mkSh, mkLo, mkBits]; norm_num
  · have hc : mkCi lay k = 0 := by simp [mkCi, hl]
    rw [hc]
    have : mkSh lay 0 leaf = leaf := by
      simp only [mkSh, mkLo, mkBits, hl, false_and, if_false, Nat.pow_zero, Nat.div_one]
      exact Nat.mod_eq_of_lt hleaf
    simp only [mkLeafOf, mkLo, hl, false_and, if_false, Nat.pow_zero, Nat.mul_one, this]
theorem mkBo_sh (lay leaf k : Nat) (hlay : lay < 4) (hleaf : leaf < 2 ^ hL lay) (hk : k < hL lay) :
    mkBo lay (mkLeafOf lay (mkCi lay k) (mkSh lay (mkCi lay k) leaf)) k = mkBo lay leaf k := by
  rw [mkBo_plan, mkBo_plan, mkPlan_sh _ _ _ hlay hleaf hk]
theorem mkBlk_sh (lay leaf k : Nat) (hlay : lay < 4) (hleaf : leaf < 2 ^ hL lay) (hk : k < hL lay) :
    mkBlk lay (mkLeafOf lay (mkCi lay k) (mkSh lay (mkCi lay k) leaf)) k = mkBlk lay leaf k := by
  unfold mkBlk; rw [mkBo_sh _ _ _ hlay hleaf hk]
theorem mkCur_sh (lay leaf k b : Nat) (hlay : lay < 4) (hleaf : leaf < 2 ^ hL lay) (hk : k < hL lay) :
    mkCur lay (mkLeafOf lay (mkCi lay k) (mkSh lay (mkCi lay k) leaf)) k b = mkCur lay leaf k b := by
  unfold mkCur mkVal; rw [mkBlk_sh _ _ _ hlay hleaf hk]
theorem mkCur_next (lay leaf k b : Nat) (hlay : lay < 4) (hleaf : leaf < 2 ^ hL lay) (hk1 : k + 1 < hL lay)
    (hc : mkCi lay (k + 1) = mkCi lay k) :
    mkCur lay (mkLeafOf lay (mkCi lay k) (mkSh lay (mkCi lay k) leaf)) (k + 1) b = mkCur lay leaf (k + 1) b := by
  rw [← hc]; exact mkCur_sh lay leaf (k + 1) b hlay hleaf hk1
/-- C4: every line-A row places window 5 at slot 21 (the upper copies start from it). -/
theorem mkPlan_top5 (x : Nat) : plan 0 x 5 = 21 := by
  have h : (List.range 64).all (fun r => (topPlanA.getD r []).getD 5 0 == 21) = true := by decide +kernel
  have := List.all_eq_true.mp h (x % 64) (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  simp only [beq_iff_eq] at this
  unfold plan topPlan
  rw [if_pos rfl, if_pos (show (5 : Nat) < 6 by decide)]
  exact this
/-- Route facts of every layer (C4: the top too, checked leaf by leaf in `DirectMerkleChecks`). -/
theorem route_facts (lay leaf : Nat) (hlay : lay < 4) (hleaf : leaf < 2 ^ hL lay) :
    (∀ k < hL lay, plan lay leaf k + 4 ≤ mkPS lay ∧ (lay ≠ 0 → leaf / 2 ^ k % 2 = 0 → 1 ≤ plan lay leaf k)) ∧
    (∀ s ∈ mkKS lay leaf 0 ++ mkKH lay leaf 0, s + 1 ≤ mkPS lay ∧ s ∉ mkWs lay leaf 0) ∧
    (∀ k, k + 1 < hL lay → ∀ s ∈ mkKS lay leaf (k + 1) ++ mkKH lay leaf (k + 1),
      s ≠ plan lay leaf k + 1 ∧ s ∉ mkWs lay leaf (k + 1)) := by
  have h : mkRouteOk lay leaf = true := by
    have hA := mkLowOk_true
    simp only [mkLowOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hA
    interval_cases lay
    · exact mkTop_route leaf (by simpa [hL] using hleaf)
    · exact hA.1.1 leaf (by simpa [hL] using hleaf)
    · exact hA.1.2 leaf (by simpa [hL] using hleaf)
    · exact hA.2 leaf (by simpa [hL] using hleaf)
  simp only [mkRouteOk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, fun k hk s hs => h.2 k (by omega) s hs⟩
/-- Membership in the write slots, as arithmetic. -/
theorem mkWs_not (lay leaf j s : Nat) (h : s ∉ mkWs lay leaf j) :
    (leaf / 2 ^ j % 2 = 0 → s ≠ plan lay leaf j - 1 ∧ s ≠ plan lay leaf j) ∧
    (leaf / 2 ^ j % 2 = 1 → s ≠ plan lay leaf j + 3 ∧ s ≠ plan lay leaf j + 4) := by
  unfold mkWs at h
  refine ⟨fun hb => ?_, fun hb => ?_⟩
  · rw [if_pos hb] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    omega
  · rw [if_neg (by omega)] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    omega
theorem mkKH_mem (lay leaf k j : Nat) (hj : j < hL lay) (hkj : k ≤ j) : plan lay leaf j + 1 ∈ mkKH lay leaf k := by
  simp only [mkKH, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨j, ⟨hj, hkj⟩, rfl⟩
theorem mkKH_succ (lay leaf k s : Nat) (h : s ∈ mkKH lay leaf (k + 1)) : s ∈ mkKH lay leaf k := by
  simp only [mkKH, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at h ⊢
  obtain ⟨j, ⟨hj, hkj⟩, hs⟩ := h
  exact ⟨j, ⟨hj, by omega⟩, hs⟩
theorem mkKS_mem (lay leaf k j s : Nat) (hj : j < hL lay) (hkj : k ≤ j)
    (hs : s = plan lay leaf j + 2 ∨ s = mkSib lay leaf j) : s ∈ mkKS lay leaf k := by
  simp only [mkKS, List.mem_flatMap, List.mem_filter, List.mem_range, decide_eq_true_eq, List.mem_cons,
    List.not_mem_nil, or_false]
  exact ⟨j, ⟨hj, hkj⟩, hs⟩
theorem mkKS_succ (lay leaf k s : Nat) (h : s ∈ mkKS lay leaf (k + 1)) : s ∈ mkKS lay leaf k := by
  simp only [mkKS, List.mem_flatMap, List.mem_filter, List.mem_range, decide_eq_true_eq] at h ⊢
  obtain ⟨j, ⟨hj, hkj⟩, hs⟩ := h
  exact ⟨j, ⟨hj, by omega⟩, hs⟩
theorem mkBo_facts (lay leaf k : Nat) (hlay : lay < 4) (hleaf : leaf < 2 ^ hL lay) (hk : k < hL lay) :
    mkBo lay leaf k % 8 = 0 ∧ 7664 ≤ mkBo lay leaf k ∧ mkBo lay leaf k + 80 ≤ 16856 ∧ mkBase lay ≤ mkBo lay leaf k ∧
      mkBo lay leaf k + 64 ≤ mkBase lay + 16 * mkPS lay := by
  have hp := ((route_facts lay leaf hlay hleaf).1 k hk).1
  rw [mkBo_plan]
  interval_cases lay <;> simp only [mkBase, mkPS, List.getD_cons_succ, List.getD_cons_zero] at hp ⊢ <;> omega
theorem mkPow_add_div (h k x : Nat) (hk : k < h) :
    (2 ^ h + x) / 2 ^ (k + 1) = 2 ^ (h - k - 1) + x / 2 ^ (k + 1) := by
  have : 2 ^ h = 2 ^ (k + 1) * 2 ^ (h - k - 1) := by rw [← Nat.pow_add]; congr 1; omega
  rw [this, Nat.mul_add_div (Nat.two_pow_pos _)]
theorem mkDiv64_mul_div (leaf k : Nat) (hk : 6 ≤ k) : leaf / 64 * 64 / 2 ^ (k + 1) = leaf / 2 ^ (k + 1) := by
  have e : 2 ^ (k + 1) = 64 * 2 ^ (k - 5) := by
    rw [show (64 : Nat) = 2 ^ 6 by rfl, ← Nat.pow_add]; congr 1; omega
  rw [e, Nat.mul_comm 64 (2 ^ (k - 5)), Nat.mul_div_mul_right _ _ (by decide +kernel : 0 < 64), Nat.div_div_eq_div_mul,
    Nat.mul_comm 64]
theorem mkHeap_eq (lay leaf k : Nat) (hlay : lay < 4) (hleaf : leaf < 2 ^ hL lay) (hk : k < hL lay)
    (hci : ¬ (lay = 0 ∧ mkCi lay k = 0)) :
    mkHeap lay (mkCi lay k) (mkSh lay (mkCi lay k) leaf) k = 2 ^ (hL lay - k - 1) + leaf / 2 ^ (k + 1) := by
  unfold mkHeap
  by_cases h0 : lay = 0
  · subst h0
    have hk6 : 6 ≤ k := by
      by_contra hk6; exact hci ⟨rfl, by simp [mkCi]; omega⟩
    have hci1 : mkCi 0 k = 1 := by simp [mkCi]; omega
    rw [hci1]
    have hl : leaf < 4096 := by simpa [hL] using hleaf
    have hsh : mkSh 0 1 leaf = leaf / 64 := by
      simp only [mkSh, mkLo, mkBits]; norm_num; omega
    rw [hsh, show mkLo 0 1 = 6 by rfl, show hL 0 = 12 by rfl, show (2 : Nat) ^ 6 = 64 by rfl,
      mkPow_add_div 12 k _ (by simpa [hL] using hk), mkDiv64_mul_div leaf k hk6]
  · have hci0 : mkCi lay k = 0 := by simp [mkCi, h0]
    rw [hci0]
    have hsh : mkSh lay 0 leaf = leaf := by
      simp only [mkSh, mkLo, mkBits, h0, false_and, if_false, Nat.pow_zero, Nat.div_one]
      exact Nat.mod_eq_of_lt hleaf
    rw [hsh, show mkLo lay 0 = 0 by simp [mkLo], Nat.pow_zero, Nat.mul_one, mkPow_add_div _ k _ hk]
theorem mkHeapE_eval (lay leaf k : Nat) (hlay : lay < 4) (hleaf : leaf < 2 ^ hL lay) (hk : k < hL lay)
    (s : MachineState) (h23 : lay = 0 → s.getReg .x23 = BitVec.ofNat 64 (dispatchHeap lay leaf)) :
    (mkHeapE lay (mkCi lay k) (mkSh lay (mkCi lay k) leaf) k).eval s =
      BitVec.ofNat 64 (2 ^ (hL lay - k - 1) + leaf / 2 ^ (k + 1)) := by
  have hh : hL lay ≤ 12 := by interval_cases lay <;> decide +kernel
  have hpow : 2 ^ hL lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide +kernel) hh
  unfold mkHeapE
  split_ifs with hc
  · have h0 : lay = 0 := hc.1
    have hd : dispatchHeap lay leaf = 16 * (2 ^ hL lay + leaf) := by
      simp [dispatchHeap, s7Bias, hL, h0]
    apply BitVec.eq_of_toNat_eq
    simp only [E.eval, BinOp.eval, kw, h23 h0, hd]
    have h1 : 2 ^ (hL lay - k - 1) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide +kernel) (by omega)
    have h2 : leaf / 2 ^ (k + 1) ≤ leaf := Nat.div_le_self _ _
    have hdiv : 16 * (2 ^ hL lay + leaf) / 2 ^ (k + 5) = (2 ^ hL lay + leaf) / 2 ^ (k + 1) := by
      rw [show (k + 5 : Nat) = 4 + (k + 1) by omega, Nat.pow_add, show (2 : Nat) ^ 4 = 16 by rfl,
        ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel_left _ (by decide : 0 < 16)]
    rw [toNat_srl _ _ (by omega), BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show 16 * (2 ^ hL lay + leaf) < 2 ^ 64 by omega), hdiv, mkPow_add_div _ k _ hk]
    exact (Nat.mod_eq_of_lt (by omega)).symm
  · simp only [E.eval, kw]
    rw [mkHeap_eq lay leaf k hlay hleaf hk hc]
/-- Witness words still needed at level `k` and above (lower layers): below the layer, the pad and sibling slots
(`mkKS`), and C2's high tweak words (upper half of the `mkKH` slots). -/
def mkPL (lay leaf k o : Nat) : Prop :=
  (7664 ≤ o ∧ o < mkBase lay) ∨ (mkBase lay ≤ o ∧ (o - mkBase lay) / 16 ∈ mkKS lay leaf k) ∨
    (mkBase lay ≤ o ∧ (o - mkBase lay) % 16 = 8 ∧ (o - mkBase lay) / 16 ∈ mkKH lay leaf k)
/-- C4: the top uses the plan predicate of the lower layers (its region below, `[7664, mkBase 0)`, is empty). -/
def mkP (lay leaf k _b : Nat) (o : Nat) : Prop := mkPL lay leaf k o
theorem mkP_low (lay leaf k b o : Nat) (_h0 : lay ≠ 0) : mkP lay leaf k b o ↔ mkPL lay leaf k o := Iff.rfl
theorem mkP_eq (lay leaf k b o : Nat) : mkP lay leaf k b o ↔ mkPL lay leaf k o := Iff.rfl
theorem mkPL_slot (lay leaf k o j : Nat) (hj : j < hL lay) (hkj : k ≤ j) (hb : mkBase lay ≤ o)
    (hs : (o - mkBase lay) / 16 = plan lay leaf j + 2 ∨ (o - mkBase lay) / 16 = mkSib lay leaf j) : mkPL lay leaf k o :=
  Or.inr (Or.inl ⟨hb, mkKS_mem lay leaf k j _ hj hkj hs⟩)
theorem mkPL_hi (lay leaf k o j : Nat) (hj : j < hL lay) (hkj : k ≤ j) (hb : mkBase lay ≤ o)
    (h8 : (o - mkBase lay) % 16 = 8) (hs : (o - mkBase lay) / 16 = plan lay leaf j + 1) : mkPL lay leaf k o :=
  Or.inr (Or.inr ⟨hb, h8, hs ▸ mkKH_mem lay leaf k j hj hkj⟩)
theorem mkCur_low (lay leaf l b : Nat) (_h0 : lay ≠ 0) : mkCur lay leaf l b = mkBlk lay leaf l + 48 * b + 16 * b - 16 := rfl
theorem mkCur_eq (lay leaf l b : Nat) : mkCur lay leaf l b = mkBlk lay leaf l + 48 * b + 16 * b - 16 := rfl
theorem mkP_rd (lay leaf k : Nat) (hlay : lay < 4) (hleaf : leaf < 2 ^ hL lay) (hk : k < hL lay) :
    mkP lay leaf k (leaf / 2 ^ k % 2) (mkBo lay leaf k + 32) ∧ mkP lay leaf k (leaf / 2 ^ k % 2) (mkBo lay leaf k + 40) ∧
    mkP lay leaf k (leaf / 2 ^ k % 2) (mkBo lay leaf k + 48 * (1 - leaf / 2 ^ k % 2)) ∧
    mkP lay leaf k (leaf / 2 ^ k % 2) (mkBo lay leaf k + 48 * (1 - leaf / 2 ^ k % 2) + 8) ∧
    mkP lay leaf k (leaf / 2 ^ k % 2) (mkBo lay leaf k + 24) := by
  have hb := mkBit_lt leaf k
  obtain ⟨hB16, hBlo, hBhi, hBase, hBtop⟩ := mkBo_facts lay leaf k hlay hleaf hk
  simp only [mkP_eq]
  rw [mkBo_plan] at hBase ⊢
  exact ⟨mkPL_slot _ _ _ _ k hk le_rfl (by omega) (Or.inl (by omega)),
    mkPL_slot _ _ _ _ k hk le_rfl (by omega) (Or.inl (by omega)),
    mkPL_slot _ _ _ _ k hk le_rfl (by omega) (Or.inr (by unfold mkSib; omega)),
    mkPL_slot _ _ _ _ k hk le_rfl (by omega) (Or.inr (by unfold mkSib; omega)),
    mkPL_hi _ _ _ _ k hk le_rfl (by omega) (by omega) (by omega)⟩
theorem mkP_step (lay leaf k : Nat) (hlay : lay < 4) (hleaf : leaf < 2 ^ hL lay) (hk1 : k + 1 < hL lay) (o : Nat)
    (h8 : o % 8 = 0) (ho : mkP lay leaf (k + 1) (leaf / 2 ^ (k + 1) % 2) o) :
    (mkP lay leaf k (leaf / 2 ^ k % 2) o ∧ o ≠ mkBo lay leaf k + 16 ∧ o ≠ mkBo lay leaf k + 24) ∧
      (0x1020 + o + 8 ≤ mkCur lay leaf (k + 1) (leaf / 2 ^ (k + 1) % 2) ∨
        mkCur lay leaf (k + 1) (leaf / 2 ^ (k + 1) % 2) + 32 ≤ 0x1020 + o) := by
  have hb := mkBit_lt leaf k
  have hb' := mkBit_lt leaf (k + 1)
  obtain ⟨hB16, hBlo, hBhi, hBase, hBtop⟩ := mkBo_facts lay leaf k hlay hleaf (by omega)
  obtain ⟨hB16', hBlo', hBhi', hBase', hBtop'⟩ := mkBo_facts lay leaf (k + 1) hlay hleaf hk1
  have hg := mkBase_ge lay hlay
  · rw [mkP_eq] at ho; rw [mkP_eq]
    obtain ⟨hF1, -, hF⟩ := route_facts lay leaf hlay hleaf
    rw [mkCur_eq]
    unfold mkBlk
    rw [mkBo_plan] at hBase hBase' ⊢
    rw [mkBo_plan]
    rcases ho with ho | ⟨hge, hs⟩ | ⟨hge, h16, hs⟩
    · have h0 : lay ≠ 0 := by intro h; subst h; have : mkBase 0 = 7664 := rfl; omega
      have hp1 := (hF1 (k + 1) hk1).2 h0
      exact ⟨⟨Or.inl ho, by omega, by omega⟩, Or.inl (by omega)⟩
    · obtain ⟨n1, n2⟩ := hF k hk1 _ (List.mem_append_left _ hs)
      have hw := mkWs_not lay leaf (k + 1) _ n2
      exact ⟨⟨Or.inr (Or.inl ⟨hge, mkKS_succ _ _ _ _ hs⟩), by omega, by omega⟩, by omega⟩
    · obtain ⟨n1, n2⟩ := hF k hk1 _ (List.mem_append_right _ hs)
      have hw := mkWs_not lay leaf (k + 1) _ n2
      exact ⟨⟨Or.inr (Or.inr ⟨hge, h16, mkKH_succ _ _ _ _ hs⟩), by omega, by omega⟩, by omega⟩
theorem mkP_leaf (lay leaf : Nat) (hlay : lay < 4) (hleaf : leaf < 2 ^ hL lay) (o : Nat) (h8 : o % 8 = 0)
    (ho : mkP lay leaf 0 (leaf / 2 ^ 0 % 2) o) :
    (7664 ≤ o ∧ o < mkBase lay + 16 * mkPS lay) ∧
      (0x1020 + o + 8 ≤ mkCur lay leaf 0 (leaf / 2 ^ 0 % 2) ∨ mkCur lay leaf 0 (leaf / 2 ^ 0 % 2) + 32 ≤ 0x1020 + o) := by
  have hhL : 0 < hL lay := by interval_cases lay <;> decide +kernel
  have hb := mkBit_lt leaf 0
  obtain ⟨hB16, hBlo, hBhi, hBase, hBtop⟩ := mkBo_facts lay leaf 0 hlay hleaf hhL
  have hg := mkBase_ge lay hlay
  · rw [mkP_eq] at ho
    obtain ⟨hF1, hF, -⟩ := route_facts lay leaf hlay hleaf
    rw [mkCur_eq]
    unfold mkBlk
    rw [mkBo_plan] at hBase ⊢
    rcases ho with ho | ⟨hge, hs⟩ | ⟨hge, h16, hs⟩
    · have h0 : lay ≠ 0 := by intro h; subst h; have : mkBase 0 = 7664 := rfl; omega
      have hp1 := (hF1 0 hhL).2 h0
      exact ⟨⟨ho.1, by omega⟩, Or.inl (by omega)⟩
    · obtain ⟨n1, n2⟩ := hF _ (List.mem_append_left _ hs)
      have hw := mkWs_not lay leaf 0 _ n2
      exact ⟨⟨by omega, by omega⟩, by omega⟩
    · obtain ⟨n1, n2⟩ := hF _ (List.mem_append_right _ hs)
      have hw := mkWs_not lay leaf 0 _ n2
      exact ⟨⟨by omega, by omega⟩, by omega⟩
theorem Verify.Orig.mono8 {w : ClaudeWCT.W9.T3M.WBytes} {s : MachineState} {P P' : Nat → Prop} (h : Orig w P s)
    (hP : ∀ o, o % 8 = 0 → P' o → P o) : Orig w P' s :=
  fun j h1 h2 => h j h1 (hP _ (Nat.mul_mod_right 8 j) h2)
def mkW0 (lay tree : Nat) : Word := if lay = 0 then 64#64 else T3.hyperWord (lay - 1) tree
structure MAfter (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (lay leaf : Nat) (u : MachineState) (k : Nat) (v : Digest)
    (s : MachineState) : Prop where
  pc : s.pc = pcOf (mkEc lay leaf k + 1)
  glob : Glob (gkL lay) w pk s
  known : KnownOK (mkLvlK lay k) s
  keep : ∀ r ∈ mkKeep, s.getReg r = u.getReg r
  /-- The level-`k` input sits at its value slot (C2: a lower left node was written 16 bytes low). -/
  node : DigAt s (mkVal lay leaf k (leaf / 2 ^ k % 2)) v
  orig : Orig w (mkP lay leaf k (leaf / 2 ^ k % 2)) s
  dstReg : s.getReg .x12 = BitVec.ofNat 64 (mkCur lay leaf k (leaf / 2 ^ k % 2))
  x28 : k ≠ 0 → lay ≠ 0 → s.getReg .x28 = T3.hyperWord (lay - 1) (u.getReg .x31).toNat
  bufferOrig : lay ≠ 0 → Orig w (fun o => BC.bufferStart (lay-1) ≤ o ∧ o < 21984) s
structure MkEnd (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (lay leaf : Nat) (u : MachineState) (root : Digest) (t : MachineState) :
    Prop where
  pc : t.pc = pcOf (mkFin lay leaf + 1)
  glob : Glob (gkL lay) w pk t
  known : KnownOK (mkKc lay ++ [(.x11, 64)]) t
  keep : ∀ r ∈ mkKeep, t.getReg r = u.getReg r
  root : DigAt t (mkDst lay leaf) root
  orig : Orig w (fun o => 7664 ≤ o ∧ o < mkBase lay) t
  dstReg : t.getReg .x12 = BitVec.ofNat 64 (mkDst lay leaf)
  x10 : t.getReg .x10 = BitVec.ofNat 64 (mkBlk lay leaf (hL lay - 1))
def mkHashInputOf (a b : Word) (f : Word → BitVec 8) : Query :=
  ⟨b.toNat / 64 - 1, BitVec.ofNat (8 * (64 * (b.toNat / 64 - 1 + 1))) ((List.range (64 * (b.toNat / 64 - 1 + 1))).foldl
    (fun acc i => acc + (f (a + BitVec.ofNat 64 i)).toNat * 2 ^ (8 * i)) 0)⟩
theorem mkHashInput_eq_of (s : MachineState) : hashInput s = mkHashInputOf (s.getReg .x10) (s.getReg .x11) s.getByte := rfl
theorem mkHashInput_congr {s t : MachineState} (h10 : t.getReg .x10 = s.getReg .x10)
    (h11 : t.getReg .x11 = s.getReg .x11) (hm : ∀ A, t.getMem A = s.getMem A) : hashInput t = hashInput s := by
  have hb : t.getByte = s.getByte := funext fun a => by simp only [MachineState.getByte, hm]
  rw [mkHashInput_eq_of, mkHashInput_eq_of, h10, h11, hb]
theorem mkK_sub (lay : Nat) (l : List (Reg × Word)) : ∀ p ∈ mkK lay, p ∈ mkK lay ++ l :=
  fun p hp => List.mem_append_left _ hp
theorem mkKeep_sub (l : List Reg) : ∀ r ∈ mkKeep, r ∈ mkKeep ++ l := fun r hr => List.mem_append_left _ hr
theorem mkKc_mkK (lay : Nat) : ∀ p ∈ mkKc lay, p ∈ mkK lay := by
  intro p hp; unfold mkK; unfold mkKc at hp; exact List.mem_append_left _ hp
theorem mkK_cases (lay : Nat) (p : Reg × Word) (hp : p ∈ mkK lay) :
    p ∈ mkKc lay ∨ p = (.x2, BitVec.ofNat 64 0xffbde0) := by
  unfold mkK at hp; unfold mkKc
  rcases List.mem_append.mp hp with h | h
  · exact Or.inl h
  · right; split_ifs at h with h0 <;> simp_all
/-- C2 + C4: a fold writes only its one-word label (`mkLabE`) at window + 16. -/
theorem lvlMem_read (lay ci sh l : Nat) (s : MachineState) (A : Nat) (hA : A < 2 ^ 64)
    (hB : mkBlk lay (mkLeafOf lay ci sh) l + 24 < 2 ^ 64) :
    memEval s (mkLvlMem lay ci sh l) (BitVec.ofNat 64 A) =
      if A = mkBlk lay (mkLeafOf lay ci sh) l + 16 then (mkLabE lay ci sh l).eval s
      else s.getMem (BitVec.ofNat 64 A) := by
  unfold mkLvlMem
  rw [memEval_cons_ofNat _ _ _ _ _ hA (by omega), memEval_nil]
theorem lvlMem_frame (lay ci sh l : Nat) (s : MachineState) (A : Nat) (hA : A < 2 ^ 64)
    (hB : mkBlk lay (mkLeafOf lay ci sh) l + 24 < 2 ^ 64) (h16 : A ≠ mkBlk lay (mkLeafOf lay ci sh) l + 16) :
    memEval s (mkLvlMem lay ci sh l) (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
  rw [lvlMem_read _ _ _ _ s A hA hB, if_neg h16]
theorem mk_buffer_ge (lay o : Nat) (hlay : lay < 4)
    (ho : BC.bufferStart (lay-1) ≤ o ∧ o < 21984) : 18928 ≤ o := by
  interval_cases lay <;> simp [BC.bufferStart] at ho <;> omega

theorem mk_buffer_writeHash {w : ClaudeWCT.W9.T3M.WBytes} {s : MachineState}
    (lay : Nat) (hlay : lay < 4)
    (hO : Orig w (fun o => BC.bufferStart (lay-1) ≤ o ∧ o < 21984) s)
    (a : BitVec 256) (d : Nat) (h12 : s.getReg .x12 = BitVec.ofNat 64 d)
    (hd : d + 32 ≤ WIT + 18928) :
    Orig w (fun o => BC.bufferStart (lay-1) ≤ o ∧ o < 21984) (writeHash s a) := by
  apply (Orig_writeHash hO a d h12 (by unfold WIT at hd; omega)).mono
  intro o ho
  exact ⟨ho, Or.inr (by have := mk_buffer_ge lay o hlay ho; omega)⟩

theorem lvl_bufferOrig {w : ClaudeWCT.W9.T3M.WBytes} (lay : Layer) (leaf k : Nat)
    (hleaf : leaf < 2 ^ hL lay.val) (hk : k < hL lay.val) (s t : MachineState)
    (hO : lay.val ≠ 0 → Orig w (fun o => BC.bufferStart (lay.val-1) ≤ o ∧ o < 21984) s)
    (hmem : ∀ A, t.getMem A =
      memEval s (mkLvlMem lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) leaf) k) A) :
    lay.val ≠ 0 → Orig w (fun o => BC.bufferStart (lay.val-1) ≤ o ∧ o < 21984) t := by
  intro h0
  apply (hO h0).frame
  intro j hj ho
  have hmin := mk_buffer_ge lay.val (8*j) lay.isLt ho
  obtain ⟨_, _, hhi, _, _⟩ := mkBo_facts lay.val leaf k lay.isLt hleaf hk
  have he := mkBlk_sh lay.val leaf k lay.isLt hleaf hk
  rw [hmem, lvlMem_frame _ _ _ _ s (WIT+8*j) (by unfold WIT WX at *; omega)
    (by rw [he]; unfold mkBlk; omega) (by rw [he]; unfold WIT mkBlk; omega)]

theorem t3E_eval (l' tree : Nat) (hl : l' < 4) (htr : tree < 2 ^ 32) (s : MachineState)
    (h31 : s.getReg .x31 = BitVec.ofNat 64 tree) (hD : DataOK s) :
    (t3E l').eval s = T3.hyperWord l' tree := by
  simp only [t3E, E.eval, BinOp.eval, kw, h31]
  rw [hdrA_eq l' hl, hD.header l' hl, ofNat_shl', show (16 : Nat) % 2 ^ 64 % 64 = 16 by norm_num, BitVec.or_comm]
  exact hyper_or l' tree hl htr
theorem mkHdrE_eval (lay l tree : Nat) (hlay : lay < 4) (htr : tree < 2 ^ 32) (s : MachineState)
    (h31 : lay ≠ 0 → l = 0 → s.getReg .x31 = BitVec.ofNat 64 tree) (hD : DataOK s)
    (h28 : lay ≠ 0 → l ≠ 0 → s.getReg .x28 = T3.hyperWord (lay - 1) tree) :
    (mkHdrE lay l).eval s = mkW0 lay tree := by
  unfold mkHdrE mkW0
  by_cases hl0 : lay = 0
  · simp [hl0, kw, E.eval]
  · rw [if_neg hl0, if_neg hl0]
    by_cases hl : l = 0
    · rw [if_pos hl]; exact t3E_eval _ _ (by omega) htr s (h31 hl0 hl) hD
    · rw [if_neg hl]; exact h28 hl0 hl
theorem wpath_eq (w : ClaudeWCT.W9.T3M.WBytes) (lay : Layer) (leaf j : Nat) (hleaf : leaf < 2 ^ hL lay.val) :
    ClaudeWCT.W9.T3M.wpath w lay leaf j =
      ClaudeWCT.W9.T3M.wdig w (mkBo lay.val leaf j + sibOff (leaf / 2 ^ j % 2)) := by
  unfold ClaudeWCT.W9.T3M.wpath; rw [mkBo_eq lay leaf j hleaf]
theorem wpad_eq (w : ClaudeWCT.W9.T3M.WBytes) (lay : Layer) (leaf j : Nat) (hleaf : leaf < 2 ^ hL lay.val) :
    ClaudeWCT.W9.T3M.wmerklePad w lay leaf j = ClaudeWCT.W9.T3M.wdig w (mkBo lay.val leaf j + 32) := by
  unfold ClaudeWCT.W9.T3M.wmerklePad; rw [mkBo_eq lay leaf j hleaf]
theorem mkTw_lo (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (k : Nat) :
    dlo (mkTw w index lay k) = ClaudeWCT.WCT9.merkleWord lay.val (route index lay).2 (mkHp index lay k) := by
  unfold mkTw; exact BitVec.extractLsb'_append_eq_right
theorem mkTw_hi (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (k : Nat) :
    dhi (mkTw w index lay k) = mkHw w lay (route index lay).1 k := by
  unfold mkTw; exact BitVec.extractLsb'_append_eq_left
theorem lvl_input (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer) (u : MachineState) (hidx : index < 2 ^ 31)
    (hs7 : lay.val = 0 → u.getReg .x23 = BitVec.ofNat 64 (dispatchHeap lay.val (route index lay).1))
    (ht5 : lay.val ≠ 0 → u.getReg .x31 = BitVec.ofNat 64 (route index lay).2)
    (k : Nat) (hk : k < hL lay.val) (v : Digest) (s t : MachineState)
    (hs : MAfter w pk lay.val (route index lay).1 u k v s)
    (hmem : ∀ A, t.getMem A =
      memEval s (mkLvlMem lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1) k) A)
    (h10 : t.getReg .x10 = BitVec.ofNat 64 (mkBlk lay.val (route index lay).1 k))
    (h11 : t.getReg .x11 = BitVec.ofNat 64 64) :
    hashInput t = toQ (pad64 (mkIn w index lay v k)) ∧
      Orig w (fun o => mkP lay.val (route index lay).1 k ((route index lay).1 / 2 ^ k % 2) o ∧
        o ≠ mkBo lay.val (route index lay).1 k + 16 ∧ o ≠ mkBo lay.val (route index lay).1 k + 24) t := by
  have hlay := lay.isLt
  have hleaf : (route index lay).1 < 2 ^ hL lay.val := leaf_lt index lay
  have htree : (route index lay).2 < 2 ^ 32 := tree_lt index lay hidx
  obtain ⟨hB16, hBlo, hBhi, hBase, -⟩ := mkBo_facts lay.val (route index lay).1 k hlay hleaf hk
  have hsh : mkBlk lay.val (mkLeafOf lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1)) k =
      mkBlk lay.val (route index lay).1 k := mkBlk_sh _ _ _ hlay hleaf hk
  have hfr : ∀ A, A < 2 ^ 64 →
      A ≠ mkBlk lay.val (route index lay).1 k + 16 → t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA h2
    rw [hmem, lvlMem_frame _ _ _ _ s A hA (by rw [hsh]; unfold mkBlk; omega) (by rw [hsh]; exact h2)]
  have h23 : lay.val = 0 → s.getReg .x23 = BitVec.ofNat 64 (dispatchHeap lay.val (route index lay).1) :=
    fun h => (hs.keep .x23 (by simp [mkKeep])).trans (hs7 h)
  have hO := hs.orig
  obtain ⟨rp0, rp1, rs0, rs1, rhi⟩ := mkP_rd lay.val (route index lay).1 k hlay hleaf hk
  have hT1 : t.getMem (BitVec.ofNat 64 (mkBlk lay.val (route index lay).1 k + 24)) = dhi (mkTw w index lay k) := by
    rw [mkTw_hi, hfr _ (by unfold mkBlk; omega) (by omega)]
    have := hO.hi (mkBo lay.val (route index lay).1 k + 16) (by omega) (by unfold WX; omega)
      (by rw [show mkBo lay.val (route index lay).1 k + 16 + 8 = mkBo lay.val (route index lay).1 k + 24 by omega]
          exact rhi)
    rw [show WIT + (mkBo lay.val (route index lay).1 k + 16) + 8 = mkBlk lay.val (route index lay).1 k + 24 by
      unfold WIT mkBlk; omega] at this
    rw [this]; rfl
  have hT0 : t.getMem (BitVec.ofNat 64 (mkBlk lay.val (route index lay).1 k + 16)) = dlo (mkTw w index lay k) := by
    rw [mkTw_lo, hmem, lvlMem_read _ _ _ _ s _ (by unfold mkBlk; omega) (by rw [hsh]; unfold mkBlk; omega), hsh,
      if_pos rfl]
    by_cases h0 : lay.val = 0
    · have hev := mkHeapE_eval lay.val (route index lay).1 k hlay hleaf hk s h23
      rw [hL_eq] at hev
      have hp1 : 1 ≤ mkHp index lay k ∧ mkHp index lay k < 4096 := by
        have hk12 : k < 12 := by rw [h0] at hk; simpa [hL] using hk
        have hl4 : (route index lay).1 < 4096 := by rw [h0] at hleaf; simpa [hL] using hleaf
        have hh : height lay = 12 := by rw [← hL_eq, h0]; rfl
        unfold mkHp; rw [hh]
        have e1 : 1 ≤ 2 ^ (12 - k - 1) := Nat.one_le_two_pow
        have e2 : 2 ^ (12 - k - 1) * 2 ^ (k + 1) = 4096 := by
          rw [← Nat.pow_add, show 12 - k - 1 + (k + 1) = 12 by omega]
        have e3 : (route index lay).1 / 2 ^ (k + 1) < 2 ^ (12 - k - 1) := by
          rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), e2]; exact hl4
        have e4 : 2 ^ (12 - k - 1) ≤ 2 ^ 11 := Nat.pow_le_pow_right (by decide) (by omega)
        generalize (route index lay).1 / 2 ^ (k + 1) = q at e3 ⊢
        generalize 2 ^ (12 - k - 1) = p at e1 e3 e4 ⊢
        omega
      unfold mkLabE
      rw [if_pos h0, hev, ClaudeWCT.WCT9.merkleWord, if_pos h0, T3.topNodeWord_eq hp1.1 hp1.2]
    · have hh := mkHdrE_eval lay.val k _ hlay htree s
        (fun h0 _ => (hs.keep .x31 (by simp [mkKeep])).trans (ht5 h0)) hs.glob.2.2.2.2.2
        (fun h0 hk0 => by rw [hs.x28 hk0 h0, ht5 h0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
      unfold mkLabE
      rw [if_neg h0, addC_eval, hh, mkHeap_eq lay.val (route index lay).1 k hlay hleaf hk (by omega), hL_eq,
        ClaudeWCT.WCT9.merkleWord_lower h0]
      simp only [mkW0, if_neg h0]
      unfold ClaudeWCT.WCT9.lowerNodeWord ClaudeWCT.WCT9.lowerK
      rfl
  have hlen := mkIn_length w index lay v k
  refine ⟨?_, ?_⟩
  · rw [pad64_of_aligned _ (by rw [hlen])]
    apply hashInput_words8 t _ (mkBlk lay.val (route index lay).1 k) hlen h10 (by unfold mkBlk; omega)
      (by unfold mkBlk; omega) h11
    have hpad := hO.dig (mkBo lay.val (route index lay).1 k + 32) (by omega) (by unfold WX; omega) rp0 rp1
    have e32 : WIT + (mkBo lay.val (route index lay).1 k + 32) = mkBlk lay.val (route index lay).1 k + 32 := by
      unfold WIT mkBlk; omega
    rw [e32, show mkBlk lay.val (route index lay).1 k + 32 + 8 = mkBlk lay.val (route index lay).1 k + 40 by omega] at hpad
    have f32 := hfr (mkBlk lay.val (route index lay).1 k + 32) (by unfold mkBlk; omega) (by omega)
    have f40 := hfr (mkBlk lay.val (route index lay).1 k + 40) (by unfold mkBlk; omega) (by omega)
    have f0 := hfr (mkBlk lay.val (route index lay).1 k) (by unfold mkBlk; omega) (by omega)
    have f8 := hfr (mkBlk lay.val (route index lay).1 k + 8) (by unfold mkBlk; omega) (by omega)
    have f48 := hfr (mkBlk lay.val (route index lay).1 k + 48) (by unfold mkBlk; omega) (by omega)
    have f56 := hfr (mkBlk lay.val (route index lay).1 k + 56) (by unfold mkBlk; omega) (by omega)
    have hnode := hs.node
    unfold mkIn
    rw [wpath_eq w lay _ _ hleaf, wpad_eq w lay _ _ hleaf]
    rcases (show (route index lay).1 / 2 ^ k % 2 = 0 ∨ (route index lay).1 / 2 ^ k % 2 = 1 by omega) with hb | hb
    · rw [hb] at hnode hO rs0 rs1
      simp only [hb, if_true, sibOff, show (0 : Nat) ≠ 1 by decide +kernel, if_false]
      have hsib := hO.dig (mkBo lay.val (route index lay).1 k + 48) (by omega) (by unfold WX; omega)
        (by simpa using rs0) (by simpa using rs1)
      have e48 : WIT + (mkBo lay.val (route index lay).1 k + 48) = mkBlk lay.val (route index lay).1 k + 48 := by
        unfold WIT mkBlk; omega
      rw [e48, show mkBlk lay.val (route index lay).1 k + 48 + 8 = mkBlk lay.val (route index lay).1 k + 56 by omega] at hsib
      have hn0 : s.getMem (BitVec.ofNat 64 (mkBlk lay.val (route index lay).1 k)) = v.extractLsb' 0 64 := by
        have := hnode.1; simpa [mkVal] using this
      have hn8 : s.getMem (BitVec.ofNat 64 (mkBlk lay.val (route index lay).1 k + 8)) = v.extractLsb' 64 64 := by
        have := hnode.2; simpa [mkVal] using this
      rw [wordsOf_blk4, f0, f8, hT0, hT1, f32, f40, f48, f56, hn0, hn8, hpad.1, hpad.2, hsib.1, hsib.2]
    · rw [hb] at hnode hO rs0 rs1
      simp only [hb, show (1 : Nat) ≠ 0 by decide +kernel, if_false, sibOff, if_true, Nat.add_zero]
      have hsib := hO.dig (mkBo lay.val (route index lay).1 k) (by omega) (by unfold WX; omega)
        (by simpa using rs0) (by simpa using rs1)
      have e0 : WIT + mkBo lay.val (route index lay).1 k = mkBlk lay.val (route index lay).1 k := by unfold WIT mkBlk; omega
      rw [e0] at hsib
      have hn48 : s.getMem (BitVec.ofNat 64 (mkBlk lay.val (route index lay).1 k + 48)) = v.extractLsb' 0 64 := by
        have := hnode.1; simpa [mkVal] using this
      have hn56 : s.getMem (BitVec.ofNat 64 (mkBlk lay.val (route index lay).1 k + 56)) = v.extractLsb' 64 64 := by
        have := hnode.2; simpa [mkVal, Nat.add_assoc] using this
      rw [wordsOf_blk4, f0, f8, hT0, hT1, f32, f40, f48, f56, hn48, hn56, hpad.1, hpad.2, hsib.1, hsib.2]
  · intro j hj ⟨h1, h2, h3⟩
    rw [hfr _ (by unfold WIT WX at *; omega) (by unfold WIT mkBlk; omega)]
    exact hO j hj h1
/-- C4: the top root answer address, as the compare reads it (`cmpDst`, from `topRootSlot`). -/
theorem mkDst_cmp_all : (List.range 64).all (fun c => mkCur 0 (c * 64) 11 (c / 32 % 2) == cmpDst c) = true := by
  decide +kernel
theorem mkDst_cmp (leaf : Nat) (hleaf : leaf < 4096) : cmpDst (mkSh 0 1 leaf) = mkDst 0 leaf := by
  have hsh : mkSh 0 1 leaf = leaf / 64 := by simp only [mkSh, mkLo, mkBits]; norm_num; omega
  have h := List.all_eq_true.mp mkDst_cmp_all (leaf / 64) (List.mem_range.mpr (by omega))
  simp only [beq_iff_eq] at h
  have e0 : leaf / 64 * 64 / 64 % 64 = leaf / 64 % 64 := by omega
  have e1 : plan 0 leaf 11 = plan 0 (leaf / 64 * 64) 11 := by simp [plan, topPlan, e0]
  have e2 : leaf / 2048 % 2 = leaf / 64 / 32 % 2 := by omega
  rw [hsh, ← h]
  unfold mkDst mkCur mkVal mkBlk mkBo
  rw [if_pos rfl, e1, e2]
theorem mkDst_bound (lay leaf : Nat) (hleaf : lay = 0 → leaf < 4096) :
    mkDst lay leaf % 8 = 0 ∧ mkDst lay leaf + 32 ≤ 2^23 ∧ (lay = 0 → WLO ≤ mkDst lay leaf) := by
  by_cases h : lay = 0
  · subst h
    have hl := hleaf rfl
    have hb := mkBit_lt leaf 11
    obtain ⟨hB16, hBlo, hBhi, -, -⟩ := mkBo_facts 0 leaf 11 (by decide) (by simpa [hL] using hl) (by decide)
    unfold mkDst mkCur mkVal mkBlk WLO WIT
    rw [if_pos rfl]
    refine ⟨by omega, by omega, fun _ => by omega⟩
  · unfold mkDst; rw [if_neg h]; exact ⟨by decide, by decide, fun h' => absurd h' h⟩
theorem safeDest_dst (lay leaf : Nat) (hlay : lay < 4) (hleaf : lay = 0 → leaf < 4096) :
    safeDest (mkDst lay leaf) = true := by
  by_cases h : lay = 0
  · obtain ⟨h8, h23, hlo⟩ := mkDst_bound lay leaf hleaf
    exact safeDest_hi _ (hlo h) h8 h23
  · simp [mkDst,h,safeDest,pSlots,CTRW,WIT,MEMORY_BYTES]
    intro x hx; right; omega
theorem mkMove_next (lay k : Nat) (hk : k+1 < hL lay) : mkMove lay k = 1 := by
  by_cases h : lay = 0
  · subst lay
    have : k < 11 := by change k+1<12 at hk; omega
    simp [mkMove]; omega
  · simp [mkMove,h]
theorem mkMove_last (lay k : Nat) (hk : k+1 = hL lay) :
    mkMove lay k = if lay = 0 then 0 else 1 := by
  by_cases h : lay = 0
  · subst lay
    have : k = 11 := by change k+1=12 at hk; omega
    simp [mkMove,this]
  · simp [mkMove,h]
/-- C2: the level-`j` input of a lower path keeps the HIGH half iff it is a left child. -/
def mkHB (_lay leaf j : Nat) : Bool := decide (leaf / 2 ^ j % 2 = 0)
theorem mk_node_at (lay leaf j : Nat) (hlay : lay < 4) (hleaf : leaf < 2 ^ hL lay) (hj : j < hL lay)
    (t : MachineState) (a : BitVec 256)
    (h12 : t.getReg .x12 = BitVec.ofNat 64 (mkCur lay leaf j (leaf / 2 ^ j % 2))) :
    DigAt (writeHash t a) (mkVal lay leaf j (leaf / 2 ^ j % 2)) (Verify.vHalf (mkHB lay leaf j) a) := by
  obtain ⟨hB16, hBlo, hBhi, -, -⟩ := mkBo_facts lay leaf j hlay hleaf hj
  have hb := mkBit_lt leaf j
  · rw [mkCur_eq] at h12
    rcases (show leaf / 2 ^ j % 2 = 0 ∨ leaf / 2 ^ j % 2 = 1 by omega) with hb0 | hb1
    · have e : mkHB lay leaf j = true := by simp [mkHB, hb0]
      rw [e, Verify.vHalf_true]
      rw [hb0] at h12 ⊢
      have h := DigAt.writeHash_hi t a _ h12 (by unfold mkBlk; omega)
      rwa [show mkBlk lay leaf j + 48 * 0 + 16 * 0 - 16 + 16 = mkVal lay leaf j 0 by unfold mkVal mkBlk; omega] at h
    · have e : mkHB lay leaf j = false := by simp [mkHB, hb1]
      rw [e, Verify.vHalf_false]
      rw [hb1] at h12 ⊢
      have h := DigAt.writeHash_lo t a _ h12 (by unfold mkBlk; omega)
      rwa [show mkBlk lay leaf j + 48 * 1 + 16 * 1 - 16 = mkVal lay leaf j 1 by unfold mkVal mkBlk; omega] at h
theorem mkCur_bounds (lay leaf j b : Nat) (hlay : lay < 4) (hleaf : leaf < 2 ^ hL lay) (hj : j < hL lay)
    (hb : b < 2) :
    WLO ≤ mkCur lay leaf j b ∧ mkCur lay leaf j b % 8 = 0 ∧ mkCur lay leaf j b + 32 ≤ 0x1020 + 16856 := by
  obtain ⟨hB16, hBlo, hBhi, -, -⟩ := mkBo_facts lay leaf j hlay hleaf hj
  unfold mkCur mkVal mkBlk WLO WIT
  omega
theorem lvl_after (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (lay leaf : Nat) (u : MachineState) (hlay : lay < 4)
    (hleaf : leaf < 2 ^ hL lay) (k : Nat) (hk : k < hL lay) (t : MachineState)
    (hglob : Glob (gkL lay) w pk t) (hknown : KnownOK (mkKc lay ++ [(.x11, 64)]) t)
    (hkeep : ∀ r ∈ mkKeep, t.getReg r = u.getReg r)
    (h28 : lay ≠ 0 → t.getReg .x28 = T3.hyperWord (lay - 1) (u.getReg .x31).toNat)
    (horig : Orig w (fun o => mkP lay leaf k (leaf / 2 ^ k % 2) o ∧ o ≠ mkBo lay leaf k + 16 ∧
      o ≠ mkBo lay leaf k + 24) t)
    (hbuffer : lay ≠ 0 → Orig w (fun o => BC.bufferStart (lay-1) ≤ o ∧ o < 21984) t)
    (h10 : t.getReg .x10 = BitVec.ofNat 64 (mkBlk lay leaf k)) (a : BitVec 256) :
    (k + 1 < hL lay → t.pc = pcOf (mkEc lay leaf (k + 1)) →
      t.getReg .x12 = BitVec.ofNat 64 (mkCur lay leaf (k + 1) (leaf / 2 ^ (k + 1) % 2)) →
      MAfter w pk lay leaf u (k + 1) (Verify.vHalf (mkHB lay leaf (k + 1)) a) (writeHash t a)) ∧
    (lay = 0 → k + 1 = hL lay → t.pc = pcOf (mkFin lay leaf) → t.getReg .x12 = BitVec.ofNat 64 (mkDst lay leaf) →
      MkEnd w pk lay leaf u (a.extractLsb' 0 128) (writeHash t a)) := by
  refine ⟨fun hk1 hpc h12 => ?_, fun hl0 hk1 hpc h12 => ?_⟩
  · obtain ⟨hB16', hBlo', hBhi', -, -⟩ := mkBo_facts lay leaf (k + 1) hlay hleaf hk1
    have hb := mkBit_lt leaf (k + 1)
    obtain ⟨hcw, hc8, hc32⟩ := mkCur_bounds lay leaf (k + 1) _ hlay hleaf hk1 hb
    have hd : mkCur lay leaf (k + 1) (leaf / 2 ^ (k + 1) % 2) + 32 < 2 ^ 64 := by omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [writeHash_pc, hpc, pcOf_add4]
    · exact Glob_writeHash hglob a _ h12 (safeDest_hi _ hcw hc8 (by omega))
    · intro p hp
      rw [writeHash_getReg]
      exact hknown p (by simpa [mkLvlK] using hp)
    · intro r hr; rw [writeHash_getReg]; exact hkeep r hr
    · exact mk_node_at lay leaf (k + 1) hlay hleaf hk1 t a h12
    · have hw2 := Orig_writeHash horig a _ h12 hd
      refine hw2.mono8 (fun o h8 ho => ?_)
      obtain ⟨hA, hB⟩ := mkP_step lay leaf k hlay hleaf hk1 o h8 ho
      exact ⟨hA, by unfold WIT; omega⟩
    · rw [writeHash_getReg]; exact h12
    · intro _ h0; rw [writeHash_getReg]; exact h28 h0
    · intro h0
      exact mk_buffer_writeHash lay hlay (hbuffer h0) a _ h12
        (by unfold WIT; omega)
  · subst hl0
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [writeHash_pc, hpc, pcOf_add4]
    · exact Glob_writeHash hglob a _ h12 (safeDest_dst 0 leaf hlay (fun _ => by simpa [hL] using hleaf))
    · intro p hp; rw [writeHash_getReg]; exact hknown p hp
    · intro r hr; rw [writeHash_getReg]; exact hkeep r hr
    · exact DigAt.writeHash_lo t a _ h12
        (by have := (mkDst_bound 0 leaf (fun _ => by simpa [hL] using hleaf)).2.1; omega)
    · intro j _ hj
      have h1 := hj.1
      have h2 := hj.2
      simp only [mkBase, List.getD_cons_zero] at h2
      omega
    · rw [writeHash_getReg]; exact h12
    · rw [writeHash_getReg, h10, show k = hL 0 - 1 by omega]
theorem dispTgt_eval (leaf : Nat) (hleaf : leaf < 4096) (s : MachineState)
    (h23 : s.getReg .x23 = BitVec.ofNat 64 (16 * (2 ^ hL 0 + leaf))) :
    (mkDispTgt (mkSh 0 0 leaf)).eval s = pcOf (mkTabW 0 1 (mkSh 0 1 leaf)) := by
  have hsh0 : mkSh 0 0 leaf = leaf % 64 := by simp only [mkSh, mkLo, mkBits]; norm_num
  have hsh1 : mkSh 0 1 leaf = leaf / 64 := by simp only [mkSh, mkLo, mkBits]; norm_num; omega
  rw [hsh0, hsh1]
  unfold mkDispTgt
  simp only [E.eval, BinOp.eval, addC_eval, h23, show hL 0 = 12 from rfl, mkTabW, Nat.reduceEqDiff, and_self, if_true, pcOf]
  have hm : BitVec.ofNat 64 (16 * (2 ^ 12 + leaf)) + (BitVec.ofNat 64 1432 - BitVec.ofNat 64 (16 * (leaf % 64))) =
      BitVec.ofNat 64 (0x1000 + 4 * (15718 + 256 * (leaf / 64))) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  rw [hm, even_andNot1' _ (by omega)]
theorem lfK_mkK (lay : Nat) : ∀ p ∈ mkK lay, p ∈ lfK lay := by
  intro p hp
  by_cases h0 : lay = 0
  · subst h0
    simp only [mkK, gkL, ↓reduceIte, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    repeat' first | subst p | rcases hp with hp | hp
    all_goals simp [lfK, postLf, leafK, lfKeepK, gkL]
  · simp only [mkK, gkL_low h0, h0, if_false, baseK, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    repeat' first | subst p | rcases hp with hp | hp
    all_goals simp [lfK, postLf, leafK, lfKeepK, h0, gkL_low h0, baseK]
theorem lvl_step (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer) (u : MachineState) (hidx : index < 2 ^ 31)
    (hs7 : lay.val = 0 → u.getReg .x23 = BitVec.ofNat 64 (dispatchHeap lay.val (route index lay).1))
    (hx6 : lay.val = 0 → u.getReg .x6 = 520192)
    (ht5 : lay.val ≠ 0 → u.getReg .x31 = BitVec.ofNat 64 (route index lay).2)
    (k : Nat) (hk : k < hL lay.val) (hlive : k < hL lay.val - (if lay.val = 0 then 0 else 1)) (v : Digest) (s : MachineState)
    (hs : MAfter w pk lay.val (route index lay).1 u k v s) :
    ∃ t, Steps image s (mkLvlSt lay.val k) (mkLvlSt lay.val k) t ∧ fetch image t = some (.base .ECALL) ∧
      t.getReg .x5 = 0 ∧ hashArgumentsValid t = true ∧ hashInput t = toQ (pad64 (mkIn w index lay v k)) ∧
      ∀ a : BitVec 256,
        (k + 1 < hL lay.val →
          MAfter w pk lay.val (route index lay).1 u (k + 1) (Verify.vHalf (mkHB lay.val (route index lay).1 (k + 1)) a)
            (writeHash t a)) ∧
        (k + 1 = hL lay.val → MkEnd w pk lay.val (route index lay).1 u (a.extractLsb' 0 128) (writeHash t a)) := by
  have hlay := lay.isLt
  have hleaf : (route index lay).1 < 2 ^ hL lay.val := leaf_lt index lay
  obtain ⟨hci, hlo, hkk, hdisp, hnext, hlast⟩ := mk_facts lay.val k hlay hk
  obtain ⟨hB8, hBlo, hBhi, hBase, -⟩ := mkBo_facts lay.val (route index lay).1 k hlay hleaf hk
  have hlk : mkLo lay.val (mkCi lay.val k) + (k - mkLo lay.val (mkCi lay.val k)) = k := by omega
  have hblk := BC.mkBlockCheck_at lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1) hlay hci
    (mkSh_lt _ _ _)
  have hliveChunk : k - mkLo lay.val (mkCi lay.val k) <
      mkBits lay.val (mkCi lay.val k) - (if lay.val = 0 then 0 else 1) := by
    by_cases h0 : lay.val = 0
    · simpa [h0] using hkk
    · simpa [mkCi, mkLo, mkBits, h0] using hlive
  have hlvl := BC.mkLvl_of hblk _ hliveChunk
  have hpc0 : s.pc = pcOf (BC.mkShp lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1) +
      mkOff lay.val (mkCi lay.val k) (k - mkLo lay.val (mkCi lay.val k)) + 2) := by rw [hs.pc]; rfl
  have hkn0 : KnownOK (mkLvlK lay.val (mkLo lay.val (mkCi lay.val k) + (k - mkLo lay.val (mkCi lay.val k)))) s := by
    rw [hlk]; exact hs.known
  have hknAddr : KnownOK (mkLvlKN lay.val (mkCi lay.val k)
      (mkSh lay.val (mkCi lay.val k) (route index lay).1) (k - mkLo lay.val (mkCi lay.val k))) s := by
    intro p hp
    simp only [mkLvlKN, List.mem_append] at hp
    rcases hp with hp | hp
    · exact hkn0 p hp
    · split_ifs at hp with h0
      · simp only [List.mem_singleton] at hp
        subst p
        dsimp only
        rw [mkSh_bit _ _ _ _ hkk, hlk, mkCur_sh _ _ _ _ hlay hleaf hk]
        exact hs.dstReg
      · simp at hp
  have h23 : lay.val = 0 → s.getReg .x23 = BitVec.ofNat 64 (dispatchHeap lay.val (route index lay).1) :=
    fun h => (hs.keep .x23 (by simp [mkKeep])).trans (hs7 h)
  by_cases hd : lay.val = 0 ∧ k = 5
  ·
    obtain ⟨hl0, hk5⟩ := hd
    have hdt : mkIsDisp lay.val (mkCi lay.val k) (k - mkLo lay.val (mkCi lay.val k)) = true := by
      rw [hdisp]; simp [hl0, hk5]
    have hD : mkLvlCheckD lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1)
        (k - mkLo lay.val (mkCi lay.val k)) = true := by
      simp only [BC.mkLvlCheck, hdt, if_true] at hlvl; exact hlvl
    obtain ⟨t1, ht1⟩ := mkSpec_run hD s (by simpa [BC.mkShp, hl0] using hpc0) hknAddr (by simp [mkLvlSpecD]) (by simp)
    have hleaf0 : (route index lay).1 < 4096 := by rw [hl0] at hleaf; simpa [hL] using hleaf
    have hpc1 : t1.pc = pcOf (mkTabW 0 1 (mkSh 0 1 (route index lay).1)) := by
      rw [ht1.spc (mkDispTgt (mkSh 0 0 (route index lay).1)) (by simp [mkLvlSpecD, hl0, hk5, mkCi]),
        dispTgt_eval _ hleaf0 s (by simpa [dispatchHeap, s7Bias, hL, hl0] using h23 hl0)]
    have hkn1 : KnownOK (mkEntK 0 1) t1 := by
      intro p hp
      simp only [mkEntK, Nat.reduceEqDiff, and_self, if_true, List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · exact ht1.known p (List.mem_append_left _ (by rw [hl0]; exact hp))
      · exact ht1.known (.x10, BitVec.ofNat 64 (mkBlk 0 0 5))
          (by simp [mkLvlPostD, hl0, hk5, mkCi, mkLo, mkBlk, mkBo, mkPlan_top5])
    have hent := BC.mkEnt_of (BC.mkBlockCheck_at 0 1 (mkSh 0 1 (route index lay).1) (by decide +kernel) (by decide +kernel) (mkSh_lt _ _ _))
    obtain ⟨t, ht⟩ := mkSpec_run hent t1 hpc1 hkn1 (by simp [BC.mkEntSpec]) (by simp)
    have hst : Steps image s (mkLvlSt lay.val k) (mkLvlSt lay.val k) t := by
      have := ht1.steps.trans ht.steps
      simp only [mkLvlSpecD, BC.mkEntSpec, Nat.reduceEqDiff, and_self, if_true, hlk] at this
      rw [show mkLvlSt lay.val k = mkBody lay.val k + 1 + 2 by simp [mkLvlSt,hl0,hk5,mkMove]]
      exact this
    have hmem : ∀ A, t.getMem A =
        memEval s (mkLvlMem lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1) k) A := by
      intro A
      rw [ht.mem]
      show memEval t1 [] A = _
      rw [memEval_nil, ht1.mem]
      show memEval s (mkLvlMem _ _ _ (mkLo lay.val (mkCi lay.val k) + (k - mkLo lay.val (mkCi lay.val k)))) A = _
      rw [hlk]
    have hkt1 : KnownOK (mkLvlPostD lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1)
      (k - mkLo lay.val (mkCi lay.val k))) t1 := ht1.known
    have h10 : t.getReg .x10 = BitVec.ofNat 64 (mkBlk lay.val (route index lay).1 k) := by
      rw [ht.keep .x10 (by simp [mkEntKeep])]
      have := hkt1 (.x10, BitVec.ofNat 64 (mkBlk lay.val
        (mkLeafOf lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1))
        (mkLo lay.val (mkCi lay.val k) + (k - mkLo lay.val (mkCi lay.val k))))) (by simp [mkLvlPostD])
      rw [this, hlk, mkBlk_sh _ _ _ hlay hleaf hk]
    have h11 : t.getReg .x11 = BitVec.ofNat 64 64 := by
      rw [ht.keep .x11 (by simp [mkEntKeep])]
      exact hkt1 (.x11, 64) (by simp [mkLvlPostD])
    have hkt : KnownOK (mkEntPost 0 1 (mkSh 0 1 (route index lay).1)) t := ht.known
    have h12 : t.getReg .x12 = BitVec.ofNat 64 (mkCur lay.val (route index lay).1 (k + 1) ((route index lay).1 / 2 ^ (k + 1) % 2)) := by
      have hb : mkSh 0 1 (route index lay).1 % 2 = (route index lay).1 / 64 % 2 := by
        have := mkSh_bit 0 1 (route index lay).1 0 (by decide +kernel)
        rw [show mkLo 0 1 = 6 from rfl] at this
        simpa using this
      have hc6 := mkCur_sh 0 (route index lay).1 6 ((route index lay).1 / 64 % 2) (by decide)
        (by rw [hl0] at hleaf; exact hleaf) (by decide)
      rw [show mkCi 0 6 = 1 from rfl] at hc6
      rw [hkt (.x12, BitVec.ofNat 64 (mkCur 0 (mkLeafOf 0 1 (mkSh 0 1 (route index lay).1)) (mkLo 0 1)
        (mkSh 0 1 (route index lay).1 % 2))) (by simp [mkEntPost]),
        hl0, hk5, show mkLo 0 1 = 6 from rfl, hb, hc6]
      rfl
    obtain ⟨hinp, horig⟩ := lvl_input w pk index lay u hidx hs7 ht5 k hk v s t hs hmem h10 h11
    have hglob : Glob (gkL lay.val) w pk t := by
      rw [hl0]; exact ht.glob _ _ _ (ht1.glob _ _ _ hs.glob (RelOK.nil s)) (RelOK.nil t1)
    have hknown : KnownOK (mkKc lay.val ++ [(.x11, 64)]) t := by
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hkt p (by rw [← hl0]; simp [mkEntPost, hp])
      · simp only [List.mem_singleton] at hp; subst hp; exact h11
    have hkeep : ∀ r ∈ mkKeep, t.getReg r = u.getReg r := by
      intro r hr
      rw [ht.keep r (mkKeep_sub _ r hr), ht1.keep r (mkKeep_sub _ r hr)]; exact hs.keep r hr
    have h28 : lay.val ≠ 0 → t.getReg .x28 = T3.hyperWord (lay.val - 1) (u.getReg .x31).toNat :=
      fun h => absurd hl0 h
    have hk6 : k + 1 < hL lay.val := by rw [hl0, hk5]; decide +kernel
    refine ⟨t, hst, ht.ecall rfl, hknown (.x5, 0) (by simp [mkKc, baseK]),
      hashArgs_of t _ 64 _ h10 h11 h12 (by unfold mkBlk; omega) (by decide +kernel) (by unfold mkBlk; omega)
        (mkCur_bounds lay.val (route index lay).1 (k + 1) ((route index lay).1 / 2 ^ (k + 1) % 2) hlay hleaf hk6
          (mkBit_lt _ _)).2.1
        (by have := (mkCur_bounds lay.val (route index lay).1 (k + 1) ((route index lay).1 / 2 ^ (k + 1) % 2) hlay
              hleaf hk6 (mkBit_lt _ _)).2.2
            omega), hinp, fun a => ?_⟩
    obtain ⟨hA1, -⟩ := lvl_after w pk lay.val (route index lay).1 u hlay hleaf k hk t hglob hknown hkeep h28 horig (lvl_bufferOrig lay _ k hleaf hk s t hs.bufferOrig hmem) h10 a
    refine ⟨fun _ => hA1 hk6 ?_ h12, fun h => absurd h (by omega)⟩
    rw [ht.pc rfl]
    simp only [BC.mkEntSpec, mkEc, hl0, hk5, show mkCi 0 6 = 1 from rfl, show mkLo 0 1 = 6 from rfl]
    rfl
  ·
    have hdf : mkIsDisp lay.val (mkCi lay.val k) (k - mkLo lay.val (mkCi lay.val k)) = false := by
      rw [hdisp]; exact decide_eq_false hd
    have hN : BC.mkLvlCheckN lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1)
        (k - mkLo lay.val (mkCi lay.val k)) = true := by
      simp only [BC.mkLvlCheck, hdf, Bool.false_eq_true, if_false] at hlvl; exact hlvl
    have hknN := hknAddr
    obtain ⟨t, ht⟩ := mkSpec_run hN s hpc0 hknN (by simp [BC.mkLvlSpecN, mkLvlSpecN]) (by simp)
    have hst : Steps image s (mkLvlSt lay.val k) (mkLvlSt lay.val k) t := by
      have := ht.steps
      simp only [BC.mkLvlSpecN, mkLvlSpecN, hlk] at this
      rw [mkLvlSt_ne _ _ hd]; exact this
    have hmem : ∀ A, t.getMem A =
        memEval s (mkLvlMem lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1) k) A := by
      intro A; rw [ht.mem]; simp only [BC.mkLvlSpecN, mkLvlSpecN, hlk]
    have hkt : KnownOK (mkLvlPostN lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1)
        (k - mkLo lay.val (mkCi lay.val k))) t := ht.known
    have h10 : t.getReg .x10 = BitVec.ofNat 64 (mkBlk lay.val (route index lay).1 k) := by
      have := hkt (.x10, BitVec.ofNat 64 (mkBlk lay.val
        (mkLeafOf lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1))
        (mkLo lay.val (mkCi lay.val k) + (k - mkLo lay.val (mkCi lay.val k))))) (by simp [mkLvlPostN])
      rw [this, hlk, mkBlk_sh _ _ _ hlay hleaf hk]
    have h11 : t.getReg .x11 = BitVec.ofNat 64 64 := hkt (.x11, 64) (by simp [mkLvlPostN])
    have h12 : t.getReg .x12 = BitVec.ofNat 64 (mkNextA2 lay.val (mkCi lay.val k)
        (mkSh lay.val (mkCi lay.val k) (route index lay).1) (k - mkLo lay.val (mkCi lay.val k))) :=
      hkt (.x12, BitVec.ofNat 64 (mkNextA2 lay.val (mkCi lay.val k)
        (mkSh lay.val (mkCi lay.val k) (route index lay).1) (k - mkLo lay.val (mkCi lay.val k)))) (by simp [mkLvlPostN])
    obtain ⟨hinp, horig⟩ := lvl_input w pk index lay u hidx hs7 ht5 k hk v s t hs hmem h10 h11
    have hglob : Glob (gkL lay.val) w pk t := ht.glob _ _ _ hs.glob (RelOK.nil s)
    have hknown : KnownOK (mkKc lay.val ++ [(.x11, 64)]) t := by
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hkt p (by simp [mkLvlPostN, hp])
      · simp only [List.mem_singleton] at hp; subst hp; exact h11
    have hkeep : ∀ r ∈ mkKeep, t.getReg r = u.getReg r := by
      intro r hr; rw [ht.keep r (mkKeep_sub _ r hr)]; exact hs.keep r hr
    have h28 : lay.val ≠ 0 → t.getReg .x28 = T3.hyperWord (lay.val - 1) (u.getReg .x31).toNat := by
      intro hl0
      by_cases hk0 : k = 0
      · have hreg : mkLvlRegs lay.val (mkLo lay.val (mkCi lay.val k) + (k - mkLo lay.val (mkCi lay.val k))) =
            [(.x28, t3E (lay.val - 1))] := by
          rw [hlk, hk0]; simp [mkLvlRegs, hl0]
        have hr : t.getReg .x28 = (t3E (lay.val - 1)).eval s :=
          ht.regs (.x28, t3E (lay.val - 1)) (by simp only [BC.mkLvlSpecN, mkLvlSpecN]; rw [hreg]; exact List.mem_singleton.mpr rfl)
        have htr := tree_lt index lay hidx
        rw [hr, ht5 hl0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        exact t3E_eval _ _ (by omega) htr s ((hs.keep .x31 (by simp [mkKeep])).trans (ht5 hl0)) hs.glob.2.2.2.2.2
      · have hkp : Reg.x28 ∈ mkLvlKeep lay.val (mkLo lay.val (mkCi lay.val k) + (k - mkLo lay.val (mkCi lay.val k))) := by
          rw [hlk]; simp [mkLvlKeep, hk0]
        rw [ht.keep .x28 (List.mem_append_right _ (List.mem_cons_of_mem _ hkp))]
        exact hs.x28 hk0 hl0
    have hpcT : t.pc = pcOf (BC.mkShp lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1) +
        mkOff lay.val (mkCi lay.val k) (k - mkLo lay.val (mkCi lay.val k) + 1) + mkMove lay.val k) := by
      have h := ht.pc rfl
      simpa only [BC.mkLvlSpecN, mkLvlSpecN,hlk] using h
    have hdst : ∃ d, t.getReg .x12 = BitVec.ofNat 64 d ∧ d % 8 = 0 ∧ d + 32 ≤ 2 ^ 24 := by
      by_cases hk1 : k + 1 < hL lay.val
      · obtain ⟨hn1, hn2, hn3⟩ := hnext hk1 hd
        refine ⟨_, h12, ?_⟩
        have := mkBo_facts lay.val (route index lay).1 (k + 1) hlay hleaf hk1
        simp only [mkNextA2, if_pos hn3]
        rw [show mkLo lay.val (mkCi lay.val k) + (k - mkLo lay.val (mkCi lay.val k)) + 1 = k + 1 by omega,
          mkCur_next _ _ _ _ hlay hleaf hk1 hn1]
        have := mkCur_bounds lay.val (route index lay).1 (k + 1) _ hlay hleaf hk1
          (mkBit_lt (mkSh lay.val (mkCi lay.val k) (route index lay).1) (k - mkLo lay.val (mkCi lay.val k) + 1))
        omega
      · have hk1' : k + 1 = hL lay.val := by omega
        obtain ⟨-, hn2, -⟩ := hlast hk1'
        refine ⟨_, h12, ?_⟩
        simp only [mkNextA2, if_neg hn2]
        split
        · rw [hlk, mkCur_sh _ _ _ _ hlay hleaf hk]
          have := mkCur_bounds lay.val (route index lay).1 k _ hlay hleaf hk
            (mkBit_lt (mkSh lay.val (mkCi lay.val k) (route index lay).1) (k - mkLo lay.val (mkCi lay.val k)))
          omega
        · omega
    obtain ⟨d, hd12, hd8, hd32⟩ := hdst
    refine ⟨t, hst, ht.ecall rfl, hknown (.x5, 0) (by simp [mkKc, baseK]),
      hashArgs_of t _ 64 _ h10 h11 hd12 (by unfold mkBlk; omega) (by decide +kernel) (by unfold mkBlk; omega) hd8 hd32,
      hinp, fun a => ?_⟩
    obtain ⟨hA1, hA2⟩ := lvl_after w pk lay.val (route index lay).1 u hlay hleaf k hk t hglob hknown hkeep h28 horig (lvl_bufferOrig lay _ k hleaf hk s t hs.bufferOrig hmem) h10 a
    refine ⟨fun hk1 => hA1 hk1 ?_ ?_, fun hk1 => hA2 (by by_contra h0; rw [if_neg h0] at hlive; omega) hk1 ?_ ?_⟩
    · obtain ⟨hn1, hn2, hn3⟩ := hnext hk1 hd
      rw [hpcT,mkMove_next _ _ hk1]; unfold mkEc; rw [hn1, hn2]
    · obtain ⟨hn1, hn2, hn3⟩ := hnext hk1 hd
      rw [h12]; simp only [mkNextA2, if_pos hn3]
      rw [mkSh_bit _ _ _ _ hn3, show mkLo lay.val (mkCi lay.val k) + (k - mkLo lay.val (mkCi lay.val k)) + 1 = k + 1 by omega,
        show mkLo lay.val (mkCi lay.val k) + (k - mkLo lay.val (mkCi lay.val k) + 1) = k + 1 by omega,
        mkCur_next _ _ _ _ hlay hleaf hk1 hn1]
    · obtain ⟨hl1, hl2, hl3⟩ := hlast hk1
      rw [hpcT,mkMove_last _ _ hk1]; unfold mkFin; rw [← hl1, hl3]
    · obtain ⟨hl1, hl2, hl3⟩ := hlast hk1
      rw [h12]; simp only [mkNextA2, if_neg hl2]
      by_cases h0 : lay.val = 0
      · have hk11 : k = 11 := by rw [h0] at hk1; simp [hL] at hk1; omega
        subst hk11
        rw [if_pos h0, mkSh_bit _ _ _ _ hkk, hlk, mkCur_sh _ _ _ _ hlay hleaf hk]
        unfold mkDst; rw [if_pos h0, h0]; rfl
      · simp [h0,mkDst]
/-- C2: the half a fold keeps is its output node's side (`2 ^ (h-k-1)` is even below the root). -/
theorem mkHi_eq (index : Nat) (lay : Layer) (k : Nat) (hk1 : k + 1 < hL lay.val) :
    ClaudeWCT.WCT9.lowerHigh lay.val (mkHp index lay k) = mkHB lay.val (route index lay).1 (k + 1) := by
  have hl := lay.isLt
  have hpar : (2 ^ (height lay - k - 1) + (route index lay).1 / 2 ^ (k + 1)) % 2 =
      (route index lay).1 / 2 ^ (k + 1) % 2 := by
    rw [← hL_eq]
    obtain ⟨m, hm⟩ : ∃ m, hL lay.val - k - 1 = m + 1 := ⟨hL lay.val - k - 2, by omega⟩
    rw [hm, pow_succ]; omega
  unfold mkHp mkHB ClaudeWCT.WCT9.lowerHigh
  rw [hpar]
  simp [hl]
theorem mkHi_leaf (lay : Layer) (leaf : Nat) :
    ClaudeWCT.WCT9.lowerHigh lay.val leaf = mkHB lay.val leaf 0 := by
  have hl := lay.isLt
  unfold mkHB ClaudeWCT.WCT9.lowerHigh
  simp [hl]
def mkStop (lay : Nat) : Nat := hL lay - (if lay = 0 then 0 else 1)
def MkStop (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (lay leaf : Nat) (u : MachineState)
    (v : Digest) (s : MachineState) : Prop :=
  if lay = 0 then MkEnd w pk lay leaf u v s else MAfter w pk lay leaf u (mkStop lay) v s
def mkCycR (lay : Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | k, n + 1 => mkLvlSt lay k + 8 + mkCycR lay (k + 1) n
def mkFuelR (lay : Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | k, n + 1 => mkLvlSt lay k + 1 + mkFuelR lay (k + 1) n
theorem merkle_rest (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer) (u : MachineState) (hidx : index < 2 ^ 31)
    (hs7 : lay.val = 0 → u.getReg .x23 = BitVec.ofNat 64 (dispatchHeap lay.val (route index lay).1))
    (hx6 : lay.val = 0 → u.getReg .x6 = 520192)
    (ht5 : lay.val ≠ 0 → u.getReg .x31 = BitVec.ofNat 64 (route index lay).2)
    (K : Digest → OracleComp HashSpec Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ root t, MkStop w pk lay.val (route index lay).1 u root t → GoodQP P t N C Q A (K root)) :
    ∀ n k v s, k + n = mkStop lay.val → k < hL lay.val → MAfter w pk lay.val (route index lay).1 u k v s →
      GoodQP P s (N + mkFuelR lay.val k n) (C + mkCycR lay.val k n) Q (A + mkCycR lay.val k n)
        (ccM ((List.range' k n).foldlM (mkStep w index lay) v) K) := by
  intro n
  induction n with
  | zero =>
    intro k v s hkn hk hs
    have h0 : lay.val ≠ 0 := by intro h; simp [mkStop, h] at hkn; rw [h] at hk; omega
    simp only [List.range'_zero, List.foldlM_nil, ccM_pure, mkFuelR, mkCycR, Nat.add_zero]
    apply hK v s
    simpa [MkStop, h0, ← hkn] using hs
  | succ m ih =>
    intro k v s hkn hk hs
    have hlive : k < hL lay.val - (if lay.val = 0 then 0 else 1) := by change k < mkStop lay.val; omega
    obtain ⟨t, hst, hf, h5, hv, hin, hpost⟩ := lvl_step w pk index lay u hidx hs7 hx6 ht5 k hk hlive v s hs
    rw [List.range'_succ, List.foldlM_cons, mkStep_eq]
    have H : ∀ a : BitVec 256, GoodQP P (writeHash t a) (N + mkFuelR lay.val (k + 1) m) (C + mkCycR lay.val (k + 1) m) Q
        (A + mkCycR lay.val (k + 1) m)
        (ccM ((fun v' => (List.range' (k + 1) m).foldlM (mkStep w index lay) v')
          (Verify.vHalf (ClaudeWCT.WCT9.lowerHigh lay.val (mkHp index lay k)) a)) K) := by
      intro a
      by_cases he : k + 1 = hL lay.val
      · have hm : m = 0 := by unfold mkStop at hkn; split_ifs at hkn <;> omega
        subst m
        have h0 : lay.val = 0 := by unfold mkStop at hkn; split_ifs at hkn <;> omega
        have e : ClaudeWCT.WCT9.lowerHigh lay.val (mkHp index lay k) = false := by
          have hl4 := leaf_lt index lay
          have h1 : mkHp index lay k = 1 := by
            unfold mkHp
            rw [← hL_eq, ← he]
            rw [← he] at hl4
            simp [Nat.div_eq_of_lt hl4]
          rw [h1]; exact ClaudeWCT.WCT9.lowerHigh_one _
        rw [e, Verify.vHalf_false]
        simp only [List.range'_zero, List.foldlM_nil, ccM_pure, mkFuelR, mkCycR, Nat.add_zero]
        apply hK
        simpa [MkStop, h0] using (hpost a).2 he
      · rw [mkHi_eq index lay k (by omega)]
        exact ih (k + 1) _ _ (by omega) (by omega) ((hpost a).1 (by omega))
    have hg := GoodQP.vHash_bind _ (f := fun v' => (List.range' (k + 1) m).foldlM (mkStep w index lay) v') hf h5 hv hin H
    rw [mkIn_blocks] at hg
    simp only [mkFuelR, mkCycR]
    exact GoodQP.stepsQ hst hg (by omega) (by omega) (fun q => ⟨q, by omega⟩)
def merklePrefix (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (value : Digest) : T3.M Digest :=
  (List.range (mkStop lay.val)).foldlM (mkStep w index lay) value
def mkFuel (lay : Nat) : Nat := 2 + mkFuelR lay 0 (mkStop lay)
def mkCyc (lay : Nat) : Nat := 1 + 8 * lfBlocks lay + mkCycR lay 0 (mkStop lay)
/-- C4: the top path is 12 instructions shorter (one label store per fold): 268 -> 256 cycles, 73 -> 61 fuel.
Campaign T51: the top leaf has 13 blocks (832 B), one fewer than #938: 248 cycles. -/
theorem mkCyc_vals : mkCyc 0 = 248 ∧ mkCyc 1 = 165 ∧ mkCyc 2 = 153 ∧ mkCyc 3 = 153 := by decide +kernel
theorem mkFuel_vals : mkFuel 0 = 61 ∧ mkFuel 1 = 36 ∧ mkFuel 2 = 31 ∧ mkFuel 3 = 31 := by decide +kernel
theorem mkBits_stabBits (lay : Nat) (hlay : lay < 4) : mkBits lay 0 = stabBits lay := by
  interval_cases lay <;> decide +kernel
theorem merkle_good (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer) (ends : List Digest) (u : MachineState)
    (hidx : index < 2 ^ 31) (hu : LeafOut w pk index lay ends u)
    (K : Digest → OracleComp HashSpec Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ root t, MkStop w pk lay.val (route index lay).1 u root t → GoodQP P t N C Q A (K root)) :
    GoodQP P u (N + mkFuel lay.val) (C + mkCyc lay.val) Q (A + mkCyc lay.val)
      (ccM (ClaudeWCT.WCT9.leafHashW lay (route index lay).2 (route index lay).1 (ClaudeWCT.W9.T3M.wtopLeafPad w)
        (ClaudeWCT.W9.T3M.wleafHigh w lay) ends >>= merklePrefix w index lay) K) := by
  have hlay := lay.isLt
  have hleaf : (route index lay).1 < 2 ^ hL lay.val := leaf_lt index lay
  have hkU : KnownOK (lfK lay.val) u := hu.glob.1
  have hknown : KnownOK (mkKc lay.val) u := fun p hp => hkU p (lfK_mkK _ p (mkKc_mkK _ p hp))
  have hhL : 0 < hL lay.val := by interval_cases lay.val <;> decide +kernel
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
    hkU (.x10, BitVec.ofNat 64 (lfBase lay.val)) (by simp [lfK, postLf, lfBase])
  have h11u : u.getReg .x11 = BitVec.ofNat 64 (lfBytes lay.val) :=
    hkU (.x11, BitVec.ofNat 64 (if lay.val = 0 then 832 else 704)) (by simp [lfK, postLf])
  have h10 : t.getReg .x10 = u.getReg .x10 := ht.keep .x10 (by simp [mkEntKeep])
  have h11 : t.getReg .x11 = u.getReg .x11 := ht.keep .x11 (by simp [mkEntKeep])
  have hkt : KnownOK (mkEntPost lay.val 0 (mkSh lay.val 0 (route index lay).1)) t := ht.known
  have hb0 : mkSh lay.val 0 (route index lay).1 % 2 = (route index lay).1 / 2 ^ 0 % 2 := by
    have := mkSh_bit lay.val 0 (route index lay).1 0 (by unfold mkBits; split <;> [decide; (interval_cases lay.val <;> decide +kernel)])
    simpa [mkLo] using this
  have h12 : t.getReg .x12 = BitVec.ofNat 64 (mkCur lay.val (route index lay).1 0 ((route index lay).1 / 2 ^ 0 % 2)) := by
    have hc0 := mkCur_sh lay.val (route index lay).1 0 ((route index lay).1 / 2 ^ 0 % 2) hlay hleaf
      (by interval_cases lay.val <;> decide +kernel)
    rw [show mkCi lay.val 0 = 0 by simp [mkCi]] at hc0
    rw [hkt (.x12, BitVec.ofNat 64 (mkCur lay.val (mkLeafOf lay.val 0 (mkSh lay.val 0 (route index lay).1)) (mkLo lay.val 0)
      (mkSh lay.val 0 (route index lay).1 % 2)))
      (by simp [mkEntPost]), hb0, show mkLo lay.val 0 = 0 by simp [mkLo], hc0]
  obtain ⟨hB8, hBlo, hBhi, hBase, hBtop⟩ := mkBo_facts lay.val (route index lay).1 0 hlay hleaf hhL
  have hb := mkBit_lt (route index lay).1 0
  obtain ⟨hcw, hc8, hc32⟩ := mkCur_bounds lay.val (route index lay).1 0 _ hlay hleaf hhL hb
  have hd : mkCur lay.val (route index lay).1 0 ((route index lay).1 / 2 ^ 0 % 2) + 32 < 2 ^ 64 := by omega
  have hin : hashInput t = toQ (pad64 (lfIn w lay (route index lay).2 (route index lay).1 ends)) := by
    rw [mkHashInput_congr h10 h11 hmem]; exact hu.hashInput.1
  have hv : hashArgumentsValid t = true := by
    refine hashArgs_of t (lfBase lay.val) (lfBytes lay.val) _ (h10.trans h10u) (h11.trans h11u) h12
      (by fin_cases lay <;> decide +kernel) (by fin_cases lay <;> decide +kernel) (by fin_cases lay <;> decide +kernel)
      hc8 (by omega)
  have hG : Glob (gkL lay.val) w pk t := ht.glob _ _ _ hu.glob (RelOK.nil u)
  have H : ∀ a : BitVec 256, GoodQP P (writeHash t a) (N + mkFuelR lay.val 0 (mkStop lay.val))
      (C + mkCycR lay.val 0 (mkStop lay.val)) Q (A + mkCycR lay.val 0 (mkStop lay.val))
      (ccM (merklePrefix w index lay (Verify.vHalf (ClaudeWCT.WCT9.lowerHigh lay.val (route index lay).1) a)) K) := by
    intro a
    rw [mkHi_leaf]
    have hA : MAfter w pk lay.val (route index lay).1 u 0 (Verify.vHalf (mkHB lay.val (route index lay).1 0) a)
        (writeHash t a) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun h => absurd rfl h, ?_⟩
      · rw [writeHash_pc, ht.pc rfl, pcOf_add4]
        simp only [BC.mkEntSpec, mkEc, show mkCi lay.val 0 = 0 by simp [mkCi], show mkLo lay.val 0 = 0 by simp [mkLo]]
        rfl
      · exact Glob_writeHash hG a _ h12 (safeDest_hi _ hcw hc8 (by omega))
      · intro p hp
        rw [writeHash_getReg]
        have hp' : p ∈ mkK lay.val := by simpa [mkLvlK] using hp
        rcases mkK_cases _ p hp' with hp'' | hp''
        · exact hkt p (List.mem_append_left _ hp'')
        ·
          rw [ht.keep p.1 (by rw [hp'']; simp [mkEntKeep, mkKeep])]
          exact hkU p (lfK_mkK _ p hp')
      · intro r hr; rw [writeHash_getReg]; exact ht.keep r (mkKeep_sub _ r hr)
      · exact mk_node_at lay.val (route index lay).1 0 hlay hleaf hhL t a h12
      · have hO : Orig w (fun o => 7664 ≤ o ∧
            o < ClaudeWCT.W9.T3M.layerBase lay + 16 * ClaudeWCT.W9.T3M.pathSlots lay) t :=
          hu.orig.frame (fun j _ _ => hmem _)
        have hw2 := Orig_writeHash hO a _ h12 hd
        refine hw2.mono8 (fun o h8 ho => ?_)
        obtain ⟨⟨h1, h2⟩, h3⟩ := mkP_leaf lay.val (route index lay).1 hlay hleaf o h8 ho
        exact ⟨⟨h1, by rw [← mkBase_eq, ← mkPS_eq]; exact h2⟩, by unfold WIT; omega⟩
      · rw [writeHash_getReg]; exact h12
      · intro h0
        have h0' : lay ≠ 0 := by intro he; apply h0; rw [he]; rfl
        have hbuf := (hu.bufferOrig h0').frame (fun j _ _ => hmem _)
        exact mk_buffer_writeHash lay.val hlay hbuf a _ h12
          (by unfold WIT; omega)
    rw [merklePrefix, List.range_eq_range']
    have hs7 : lay.val = 0 → u.getReg .x23 = BitVec.ofNat 64 (dispatchHeap lay.val (route index lay).1) := by
      intro h
      rw [hu.s7 (Fin.ext h), h]
    have hx6 : lay.val = 0 → u.getReg .x6 = 520192 := by
      intro h
      exact hkU (.x6, 520192) (by simp [lfK, postLf, leafK, h])
    exact merkle_rest w pk index lay u hidx hs7 hx6 hu.t5 K N C A Q hK (mkStop lay.val) 0 _ _ (by omega) hhL hA
  have h5 : t.getReg .x5 = 0 := hkt (.x5, 0) (by simp [mkEntPost, mkKc, baseK])
  have hg := GoodQP.vHash_bind _ (f := merklePrefix w index lay) (K := K) (ht.ecall rfl) h5 hv hin H
  rw [hu.hashInput.2] at hg
  rw [show ClaudeWCT.WCT9.leafHashW lay (route index lay).2 (route index lay).1 (ClaudeWCT.W9.T3M.wtopLeafPad w)
      (ClaudeWCT.W9.T3M.wleafHigh w lay) ends = Verify.vHash (ClaudeWCT.WCT9.lowerHigh lay.val (route index lay).1)
        (lfIn w lay (route index lay).2 (route index lay).1 ends) from (LCtx.vHash_eq_halfHash _ _).symm]
  have hst := ht.steps
  simp only [BC.mkEntSpec, Nat.reduceEqDiff, and_false, if_false] at hst
  exact GoodQP.stepsQ hst hg (by unfold mkFuel; omega) (by unfold mkCyc; omega) (fun q => ⟨q, by unfold mkCyc; omega⟩)
open ClaudeWCT.WCT9 (LayerMsg)
def mkMessage (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (v : Digest) : LayerMsg :=
  if lay.val = 0 then .forest v else
  let other := ClaudeWCT.W9.T3M.wpath w lay (route index lay).1 (height lay - 1)
  if (route index lay).1 / 2 ^ (height lay - 1) % 2 = 0 then .pair v other else .pair other v
def merkleMsg (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (v : Digest) : T3.M LayerMsg :=
  merklePrefix w index lay v >>= fun root => pure (mkMessage w index lay root)
theorem layerPairP_eq (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (h0 : lay.val ≠ 0) (digits : List Nat) :
    (ClaudeWCT.W9.T3M.layerPairP w index lay digits >>= fun p => pure (LayerMsg.pair p.1 p.2)) =
      (chainsP w lay (route index lay).2 (route index lay).1 digits >>= fun ends =>
        ClaudeWCT.WCT9.leafHashW lay (route index lay).2 (route index lay).1 (ClaudeWCT.W9.T3M.wtopLeafPad w)
          (ClaudeWCT.W9.T3M.wleafHigh w lay) ends >>= merkleMsg w index lay) := by
  have hleaf := leaf_lt index lay
  have hfun : (fun x (j : Fin (height lay - 1)) => mkStep w index lay x j.val) = (fun value j =>
      let other := ClaudeWCT.W9.T3M.wpath w lay (route index lay).1 j.val
      let pair := if (route index lay).1 / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
      ClaudeWCT.WCT9.lowerNodeHashP lay.val (route index lay).2
        (2 ^ (height lay - j.val - 1) + (route index lay).1 / 2 ^ (j.val + 1)) pair.1
        (ClaudeWCT.W9.T3M.wmerkleHigh w lay (route index lay).1 j.val)
        (ClaudeWCT.W9.T3M.wmerklePad w lay (route index lay).1 j.val) pair.2) := by
    funext x j
    have hw : mkHw w lay (route index lay).1 j.val = ClaudeWCT.W9.T3M.wmerkleHigh w lay (route index lay).1 j.val := by
      unfold mkHw ClaudeWCT.W9.T3M.wmerkleHigh; rw [mkBo_eq lay _ j.val hleaf]
    unfold mkStep mkIn mkTw
    rw [LCtx.vHash_eq_halfHash, hw]
    dsimp only
    split_ifs <;> rfl
  unfold ClaudeWCT.W9.T3M.layerPairP chainsP merkleMsg merklePrefix
  rw [mkStop, if_neg h0, hL_eq, ← mkFinRange_map_val]
  simp only [List.foldlM_map]
  rw [hfun]
  unfold mkMessage
  generalize route index lay = pair
  rcases pair with ⟨leaf, tree⟩
  simp only [bind_assoc, pure_bind]
  congr 1
  funext ends
  congr 1
  funext v
  congr 1
  funext root
  simp only [h0, if_false]
  split_ifs <;> rfl
/-- C4: the top fold of the spec (`lowerNodeHashP 0` with the witness high pad) is the image's `mkStep`. -/
theorem merkleP_eq (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (value : Digest) :
    merkleP w index 0 value = (List.range (height 0)).foldlM (mkStep w index 0) value := by
  have hleaf := leaf_lt index 0
  rw [← mkFinRange_map_val, List.foldlM_map]
  unfold merkleP
  congr 1
  funext x j
  have hw : mkHw w 0 (route index 0).1 j.val = ClaudeWCT.W9.T3M.wmerkleHigh w 0 (route index 0).1 j.val := by
    unfold mkHw ClaudeWCT.W9.T3M.wmerkleHigh; rw [mkBo_eq 0 _ j.val hleaf]
  unfold mkStep mkIn mkTw
  rw [LCtx.vHash_eq_halfHash, hw]
  dsimp only
  split_ifs <;> rfl
theorem merkleMsg_top (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) :
    merkleMsg w index 0 v = merkleP w index 0 v >>= fun root => pure (LayerMsg.forest root) := by
  rw [merkleP_eq]
  rfl
theorem layerLoop_succ (w : ClaudeWCT.W9.T3M.WBytes) (index n : Nat) (hn : n < 4) (hn0 : n ≠ 0) (msg : LayerMsg) :
    BC.layerLoop w index (n + 1) msg =
      layerHead w index (Fin.ofNat 4 n) msg (fun ends =>
        ClaudeWCT.WCT9.leafHashW (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1
          (ClaudeWCT.W9.T3M.wtopLeafPad w) (ClaudeWCT.W9.T3M.wleafHigh w (Fin.ofNat 4 n)) ends >>=
          fun v => merkleMsg w index (Fin.ofNat 4 n) v >>= BC.layerLoop w index n) := by
  change ClaudeWCT.W9.T3M.layersCanonicalBC w index (n + 1) msg = _
  rw [ClaudeWCT.W9.T3M.layersCanonicalBC, layerHead]
  dsimp only
  simp only [hn0, ↓reduceIte]
  have hlay0 : (Fin.ofNat 4 n : Layer) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp [Fin.val_ofNat, Nat.mod_eq_of_lt hn] at this
    exact hn0 this
  rw [ClaudeWCT.WCT9.verificationHash_lower _ hlay0]
  split_ifs with hc
  · rfl
  · congr 1
    funext answer
    simp only [canonicalDecode]
    cases ClaudeWCT.WCT9.CanonicalPolicy.decode (Fin.ofNat 4 n) answer with
    | none => rfl
    | some digits =>
      unfold guardedChainsP ClaudeWCT.W9.T3M.layerGuardedPairP ClaudeWCT.WCT9.lowerGuardedRun
      by_cases hgood : ClaudeWCT.WCT9.lowerRankGood answer
      · simp only [if_pos hgood, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
        have hv : (Fin.ofNat 4 n : Layer).val ≠ 0 := by simpa [Fin.val_ofNat, Nat.mod_eq_of_lt hn] using hn0
        have h := congrArg (fun p => p >>= BC.layerLoop w index n) (layerPairP_eq w index (Fin.ofNat 4 n) hv digits)
        cases n with
        | zero => contradiction
        | succ m => simpa only [bind_assoc, pure_bind, BC.layerLoop] using h
      · simp only [if_neg hgood, bind_assoc, pure_bind]
theorem layerLoop_one (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (msg : LayerMsg) :
    BC.layerLoop w index 1 msg =
      if (ClaudeWCT.W9.T3M.wbcCtr w index 0).toNat ≥ ClaudeWCT.WCT9.verifyWindow then pure none else
      ClaudeWCT.WCT9.verificationHash 0 (ClaudeWCT.W9.T3M.wtopHigh w)
        (ClaudeWCT.W9.T3M.layerEncodingInputP 0 (route index 0).2 (route index 0).1 msg
        (ClaudeWCT.W9.T3M.wbcCtr w index 0) (ClaudeWCT.W9.T3M.wbcPad w index 0) (ClaudeWCT.W9.T3M.wbcRight w)
        (ClaudeWCT.W9.T3M.wbcHigh w index 0)) >>=
        ClaudeWCT.W9.T3M.topLayerP w index := by
  change ClaudeWCT.W9.T3M.layersCanonicalBC w index 1 msg = _
  rw [ClaudeWCT.W9.T3M.layersCanonicalBC]
  rfl
set_option maxRecDepth 10000
theorem mAfter_pair (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer) (u : MachineState)
    (k : Nat) (hk : k < hL lay.val) (v : Digest) (s : MachineState)
    (hs : MAfter w pk lay.val (route index lay).1 u k v s) :
    let other := ClaudeWCT.W9.T3M.wpath w lay (route index lay).1 k
    let pair := if (route index lay).1 / 2 ^ k % 2 = 0 then (v, other) else (other, v)
    DigAt s (mkBlk lay.val (route index lay).1 k) pair.1 ∧ DigAt s (mkBlk lay.val (route index lay).1 k + 48) pair.2 := by
  dsimp only
  have hleaf : (route index lay).1 < 2 ^ hL lay.val := leaf_lt index lay
  obtain ⟨hB16, hBlo, hBhi, -, -⟩ := mkBo_facts lay.val (route index lay).1 k lay.isLt hleaf hk
  obtain ⟨-, -, rs0, rs1, -⟩ := mkP_rd lay.val (route index lay).1 k lay.isLt hleaf hk
  have hb := mkBit_lt (route index lay).1 k
  have hO := hs.orig
  have hnode := hs.node
  rw [wpath_eq w lay _ _ hleaf]
  rcases (show (route index lay).1 / 2 ^ k % 2 = 0 ∨ (route index lay).1 / 2 ^ k % 2 = 1 by omega) with hb | hb
  · rw [hb] at hnode hO rs0 rs1
    simp only [hb, if_true, sibOff, show (0 : Nat) ≠ 1 by decide +kernel, if_false]
    have hsib := hO.dig (mkBo lay.val (route index lay).1 k + 48) (by omega) (by unfold WX; omega)
      (by simpa using rs0) (by simpa using rs1)
    exact ⟨by simpa [mkVal] using hnode, by simpa [DigAt, dlo, dhi, WIT, mkBlk, Nat.add_assoc] using hsib⟩
  · rw [hb] at hnode hO rs0 rs1
    simp only [hb, show (1 : Nat) ≠ 0 by decide +kernel, if_false, sibOff, if_true, Nat.add_zero]
    have hsib := hO.dig (mkBo lay.val (route index lay).1 k) (by omega) (by unfold WX; omega)
      (by simpa using rs0) (by simpa using rs1)
    exact ⟨by simpa [DigAt, dlo, dhi, WIT, mkBlk] using hsib, by simpa [mkVal] using hnode⟩
theorem mAfter_pad (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer) (u : MachineState)
    (k : Nat) (hk : k < hL lay.val) (v : Digest) (s : MachineState)
    (hs : MAfter w pk lay.val (route index lay).1 u k v s) (j : Nat) (hj : (lay.val ≠ 0 ∧ j = 3) ∨ j = 4 ∨ j = 5) :
    s.getMem (BitVec.ofNat 64 (mkBlk lay.val (route index lay).1 k + 8 * j)) =
      wword w ((mkBlk lay.val (route index lay).1 k - WIT) / 8 + j) := by
  have hleaf : (route index lay).1 < 2 ^ hL lay.val := leaf_lt index lay
  obtain ⟨hB16, hBlo, hBhi, -, -⟩ := mkBo_facts lay.val (route index lay).1 k lay.isLt hleaf hk
  obtain ⟨rp0, rp1, -, -, rhi⟩ := mkP_rd lay.val (route index lay).1 k lay.isLt hleaf hk
  have hm : 8 * (mkBo lay.val (route index lay).1 k / 8 + j) = mkBo lay.val (route index lay).1 k + 8 * j := by omega
  have h := hs.orig (mkBo lay.val (route index lay).1 k / 8 + j) (by unfold WX; omega) (by
    rw [hm]
    rcases hj with ⟨h0, rfl⟩ | rfl | rfl
    · simpa using rhi
    · simpa using rp0
    · simpa using rp1)
  simpa only [mkBlk, WIT, Nat.add_sub_cancel_left, hm, Nat.add_assoc] using h
theorem rowA_mk (index : Nat) (lay : Layer) (h0 : lay.val ≠ 0) :
    rowA (lay.val - 1) (BC.cpIdx index (lay.val - 1)) = mkBlk lay.val (route index lay).1 (mkStop lay.val) := by
  have hcp : BC.cpIdx index (lay.val - 1) = (route index lay).1 := by
    rw [route_fst]; unfold BC.cpIdx; rw [if_neg (by have := lay.isLt; omega), show lay.val - 1 + 1 = lay.val by omega]
    rfl
  rw [hcp]; unfold rowA mkBlk
  rw [mkBo_low _ _ _ h0, show lay.val - 1 + 1 = lay.val by omega, mkStop, if_neg h0]
  omega
theorem mkStop_msg (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer) (h0 : lay.val ≠ 0)
    (u : MachineState) (v : Digest) (s : MachineState)
    (hs : MkStop w pk lay.val (route index lay).1 u v s) :
    BC.MsgAt w index (lay.val - 1) (mkMessage w index lay v) s := by
  have hS : mkStop lay.val = height lay - 1 := by rw [mkStop, if_neg h0, hL_eq]
  have hk : mkStop lay.val < hL lay.val := by fin_cases lay <;> first | contradiction | decide
  have ha : MAfter w pk lay.val (route index lay).1 u (mkStop lay.val) v s := by
    simpa [MkStop, h0] using hs
  have hp := mAfter_pair w pk index lay u _ hk v s ha
  have hpad := mAfter_pad w pk index lay u _ hk v s ha
  rw [← rowA_mk index lay h0] at hp hpad
  rw [hS] at hp
  have hlt : lay.val - 1 < 3 := by omega
  unfold mkMessage
  rw [if_neg h0]
  have h3 : lay.val - 1 ≠ 3 := by omega
  have hpad' : ∀ j, j = 3 ∨ j = 4 ∨ j = 5 → s.getMem (BitVec.ofNat 64 (rowA (lay.val - 1) (BC.cpIdx index (lay.val - 1)) + 8 * j)) =
      wword w ((rowA (lay.val - 1) (BC.cpIdx index (lay.val - 1)) - WIT) / 8 + j) := fun j hj =>
    hpad j (by rcases hj with h | h | h
               · exact Or.inl ⟨h0, h⟩
               · exact Or.inr (Or.inl h)
               · exact Or.inr (Or.inr h))
  split_ifs with hb
  · simp only [hb, if_true] at hp
    simp only [BC.MsgAt, if_neg h3]
    exact ⟨hlt, hp.1, hp.2, hpad'⟩
  · simp only [hb, if_false] at hp
    simp only [BC.MsgAt, if_neg h3]
    exact ⟨hlt, hp.1, hp.2, hpad'⟩
theorem mkStop_known_next (n : Nat) (hn : n < 4) (hn0 : n ≠ 0) (u t : MachineState)
    (hu : KnownOK (lfK n) u) (ht : KnownOK (mkLvlK n (mkStop n)) t)
    (keep : ∀ r ∈ mkKeep, t.getReg r = u.getReg r) : KnownOK (BC.preK (n - 1)) t := by
  intro p hp
  interval_cases n
  · contradiction
  all_goals
    simp only [BC.preK, preK, baseK] at hp
    dsimp at hp
    simp only [List.mem_append, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with ⟨hp, hf⟩ | hp
    all_goals
      repeat' first | subst p | rcases hp with hp | hp
      all_goals first
      | exact ht _ (by decide +kernel)
      | (rw [keep _ (by decide +kernel)]; exact hu _ (by decide +kernel))
      | contradiction
theorem mkStop_pc (n leaf : Nat) (hn : n < 4) (h0 : n ≠ 0) (hleaf : leaf < 2 ^ hL n) :
    mkEc n leaf (mkStop n) + 1 = trPc (n - 1) leaf := by
  have hbits : mkBits n 0 = hL n := by simp [mkBits, h0]
  have hc := BC.mkBlockCheck_at n 0 leaf hn (by simp [mkNch, h0]) (by rwa [hbits])
  simp only [BC.mkBlockCheck, Bool.and_eq_true] at hc
  have hr : BC.childReturn n leaf = trPc (n - 1) leaf := by simpa [h0] using hc.2
  rw [← hr]
  simp only [mkEc, mkCi, h0, false_and, if_false, mkSh, mkLo, Nat.pow_zero, Nat.div_one,
    hbits, Nat.mod_eq_of_lt hleaf, mkStop, BC.childReturn, Nat.sub_zero]
theorem mkStop_next_lower (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (hidx : index < 2 ^ 31)
    (lay : Layer) (h0 : lay.val ≠ 0) (ends : List Digest) (u : MachineState)
    (hu : LeafOut w pk index lay ends u) (v : Digest) (t : MachineState)
    (ht : MkStop w pk lay.val (route index lay).1 u v t) :
    LayerIn w pk index (lay.val - 1) (mkMessage w index lay v) t := by
  have ha : MAfter w pk lay.val (route index lay).1 u (mkStop lay.val) v t := by
    simpa [MkStop, h0] using ht
  have hleaf := leaf_lt index lay
  have hL0 : lay ≠ 0 := by intro h; apply h0; rw [h]; rfl
  have hk0 : mkStop lay.val ≠ 0 := by fin_cases lay <;> first | contradiction | decide
  have hcp : BC.cpIdx index (lay.val - 1) = (route index lay).1 := by
    rw [route_fst]; unfold BC.cpIdx; rw [if_neg (by have := lay.isLt; omega), show lay.val - 1 + 1 = lay.val by omega]
    rfl
  have he : BC.below (lay.val - 1) = below (lay.val - 1) := by
    fin_cases lay <;> rfl
  refine ⟨by omega, hidx, ?_, ⟨mkStop_known_next _ lay.isLt h0 u t hu.glob.1 ha.known ha.keep, ha.glob.2⟩, ?_, ?_,
    mkStop_msg w pk index lay h0 u v t ht, ?_, fun h => absurd h (by have := lay.isLt; omega), ?_, ha.bufferOrig h0,
    fun h => absurd h (by have := lay.isLt; omega), fun h => absurd h (by have := lay.isLt; omega)⟩
  · rw [ha.pc, mkStop_pc _ _ lay.isLt h0 hleaf, hcp]
    simp only [setupPc, if_neg (show lay.val - 1 ≠ 3 by have := lay.isLt; omega)]
  · rw [show rReg (lay.val - 1) = .x31 by simp [rReg]; omega,
      ha.keep .x31 (by simp [mkKeep]), hu.t5 h0, tree_next index lay hL0, he]
  · intro _
    have htr := tree_lt index lay hidx
    rw [ha.x28 hk0 h0, hu.t5 h0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), tree_next index lay hL0, he]
  · have hle : BC.layerEnd (lay.val - 1) = mkBase lay.val := by
      fin_cases lay <;> first | contradiction | rfl
    refine ha.orig.mono (fun o ho => ?_)
    rw [mkP_low _ _ _ _ _ h0]
    exact Or.inl ⟨ho.1, by rw [← hle]; exact ho.2⟩
  · intro _
    refine ⟨_, ha.dstReg, ?_⟩
    have hb := mkBit_lt (route index lay).1 (mkStop lay.val)
    have hk : mkStop lay.val < hL lay.val := by fin_cases lay <;> first | contradiction | decide
    have hle : BC.layerEnd (lay.val - 1) = mkBase lay.val := by
      fin_cases lay <;> first | contradiction | rfl
    have hp1 := ((route_facts lay.val (route index lay).1 lay.isLt hleaf).1 (mkStop lay.val) hk).2 h0
    rw [rowA_mk index lay h0, mkCur_low _ _ _ _ h0, hle]
    unfold mkBlk WIT; rw [mkBo_low _ _ _ h0]
    omega
end SigGolfCandidate.T3M
end
end
-- ==== merged from T3M_Verify_Compose ====
section

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
end
-- ==== merged from T3M_Verify_Init ====
section

set_option Elab.async false

set_option linter.unusedSimpArgs false
set_option maxRecDepth 65536
set_option maxHeartbeats 1600000
namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
def leNat8 : List (BitVec 8) → Nat
  | [] => 0
  | b :: l => b.toNat + 256 * leNat8 l
theorem shl_or (X y k : Nat) (hX : X < 2 ^ k) : X ||| y * 2 ^ k = X + 2 ^ k * y := by
  rw [Nat.or_comm, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt hX]; ring
theorem zext_shl_toNat (b : BitVec 8) (k : Nat) (hk : k ≤ 56) :
    ((b.zeroExtend 64 : Word) <<< (BitVec.ofNat 64 k)).toNat = b.toNat * 2 ^ k := by
  rw [BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
  have := b.isLt
  rw [Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show b.toNat < 2 ^ 64 by omega)]
  apply Nat.mod_eq_of_lt
  calc b.toNat * 2 ^ k < 2 ^ 8 * 2 ^ k := Nat.mul_lt_mul_of_pos_right this (Nat.two_pow_pos _)
    _ = 2 ^ (8 + k) := by rw [Nat.pow_add]
    _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide +kernel) (by omega)
theorem leNat8_lt : ∀ l : List (BitVec 8), leNat8 l < 256 ^ l.length
  | [] => by simp [leNat8]
  | b :: l => by
    have := leNat8_lt l
    have hb := b.isLt
    simp only [leNat8, List.length_cons, pow_succ]
    have : b.toNat < 256 := by simpa using hb
    nlinarith
theorem bytesToWordLE8_toNat (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (bytesToWordLE [b0, b1, b2, b3, b4, b5, b6, b7]).toNat =
      leNat8 [b0, b1, b2, b3, b4, b5, b6, b7] := by
  simp only [bytesToWordLE, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    BitVec.toNat_or, leNat8]
  rw [show (8 : Word) = BitVec.ofNat 64 8 from rfl, show (16 : Word) = BitVec.ofNat 64 16 from rfl,
    show (24 : Word) = BitVec.ofNat 64 24 from rfl, show (32 : Word) = BitVec.ofNat 64 32 from rfl,
    show (40 : Word) = BitVec.ofNat 64 40 from rfl, show (48 : Word) = BitVec.ofNat 64 48 from rfl,
    show (56 : Word) = BitVec.ofNat 64 56 from rfl]
  rw [zext_shl_toNat _ _ (by decide +kernel), zext_shl_toNat _ _ (by decide +kernel), zext_shl_toNat _ _ (by decide +kernel),
    zext_shl_toNat _ _ (by decide +kernel), zext_shl_toNat _ _ (by decide +kernel), zext_shl_toNat _ _ (by decide +kernel),
    zext_shl_toNat _ _ (by decide +kernel)]
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
  have := b0.isLt; have := b1.isLt; have := b2.isLt; have := b3.isLt
  have := b4.isLt; have := b5.isLt; have := b6.isLt; have := b7.isLt
  generalize b0.toNat = x0 at *; generalize b1.toNat = x1 at *; generalize b2.toNat = x2 at *
  generalize b3.toNat = x3 at *; generalize b4.toNat = x4 at *; generalize b5.toNat = x5 at *
  generalize b6.toNat = x6 at *; generalize b7.toNat = x7 at *
  rw [Nat.mod_eq_of_lt (show x0 < 2 ^ 64 by omega), shl_or x0 x1 8 (by omega),
    shl_or _ x2 16 (by omega), shl_or _ x3 24 (by omega), shl_or _ x4 32 (by omega),
    shl_or _ x5 40 (by omega), shl_or _ x6 48 (by omega), shl_or _ x7 56 (by omega)]
  norm_num
  omega
theorem bytesToWordLE8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    bytesToWordLE [b0, b1, b2, b3, b4, b5, b6, b7] =
      BitVec.ofNat 64 (leNat8 [b0, b1, b2, b3, b4, b5, b6, b7]) := by
  apply BitVec.eq_of_toNat_eq
  have hlt := leNat8_lt [b0, b1, b2, b3, b4, b5, b6, b7]
  simp only [List.length_cons, List.length_nil] at hlt
  rw [bytesToWordLE8_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by norm_num at hlt ⊢; exact hlt)]
theorem bytesToWordLE_len8 (l : List (BitVec 8)) (hl : l.length = 8) :
    bytesToWordLE l = BitVec.ofNat 64 (leNat8 l) := by
  match l, hl with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ => exact bytesToWordLE8 b0 b1 b2 b3 b4 b5 b6 b7
theorem length_bytes {n : Nat} (x : Bytes n) : (bytes x).length = n := by simp [bytes]
theorem leNat8_slice {n : Nat} (x : Bytes n) : ∀ k a, a + k ≤ n →
    leNat8 (((bytes x).drop a).take k) = x.toNat / 2 ^ (8 * a) % 2 ^ (8 * k) := by
  intro k
  induction k with
  | zero => intro a _; simp only [List.take_zero, leNat8, Nat.mul_zero, pow_zero, Nat.mod_one]
  | succ k ih =>
    intro a h
    have ha : a < (bytes x).length := by rw [length_bytes]; omega
    rw [List.drop_eq_getElem_cons ha, List.take_succ_cons, leNat8, ih (a + 1) (by omega)]
    have hb : ((bytes x)[a]'ha).toNat = x.toNat / 2 ^ (8 * a) % 2 ^ 8 := by
      simp only [bytes, List.getElem_map, List.getElem_range, BitVec.extractLsb'_toNat,
        Nat.shiftRight_eq_div_pow]
    rw [hb, show 8 * (a + 1) = 8 * a + 8 by ring, Nat.pow_add, ← Nat.div_div_eq_div_mul,
      show 8 * (k + 1) = 8 + 8 * k by ring, Nat.pow_add 2 8 (8 * k), Nat.mod_mul]
theorem bytes_word {n : Nat} (x : Bytes n) (j : Nat) (h : 8 * j + 8 ≤ n) :
    bytesToWordLE (((bytes x).drop (8 * j)).take 8) = x.extractLsb' (64 * j) 64 := by
  rw [bytesToWordLE_len8 _ (by simp [length_bytes]; omega), leNat8_slice x 8 (8 * j) h]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow,
    show 8 * (8 * j) = 64 * j by ring, show 8 * 8 = 64 by rfl, Nat.mod_mod]
theorem bytesToWordLE_len4 (l : List (BitVec 8)) (hl : l.length = 4) :
    bytesToWordLE l = BitVec.ofNat 64 (leNat8 l) := by
  match l, hl with
  | [b0, b1, b2, b3], _ =>
    have e : bytesToWordLE [b0, b1, b2, b3] = bytesToWordLE [b0, b1, b2, b3, 0, 0, 0, 0] := rfl
    rw [e, bytesToWordLE8]
    simp [leNat8]
/-- The last, half-filled word of a buffer whose length is 4 mod 8: the loader zero-pads it. -/
theorem bytes_word_tail {n : Nat} (x : Bytes n) (j : Nat) (h : 8 * j + 4 = n) :
    bytesToWordLE (((bytes x).drop (8 * j)).take 8) = x.extractLsb' (64 * j) 64 := by
  have hd : ((bytes x).drop (8 * j)).length = 4 := by
    rw [List.length_drop, length_bytes]; omega
  have ht : ((bytes x).drop (8 * j)).take 8 = ((bytes x).drop (8 * j)).take 4 := by
    rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
  rw [ht, bytesToWordLE_len4 _ (by rw [List.length_take, hd]; rfl), leNat8_slice x 4 (8 * j) (by omega)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow,
    show 8 * (8 * j) = 64 * j by ring]
  have hx : x.toNat / 2 ^ (64 * j) < 2 ^ (8 * 4) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]
    calc x.toNat < 2 ^ (8 * n) := x.isLt
      _ = 2 ^ (8 * 4 + 64 * j) := by congr 1; omega
  rw [Nat.mod_eq_of_lt hx]
theorem bytes_word_lt {n : Nat} (x : Bytes n) (j : Nat) (hn : n % 8 = 4) (h : 8 * j < n) :
    bytesToWordLE (((bytes x).drop (8 * j)).take 8) = x.extractLsb' (64 * j) 64 := by
  rcases Nat.lt_or_ge (8 * j + 8) (n + 1) with h1 | h1
  · exact bytes_word x j (by omega)
  · exact bytes_word_tail x j (by omega)
theorem extractByte_or8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) (j : Nat) (hj : j < 8) :
    extractByte (b0.zeroExtend 64 ||| (b1.zeroExtend 64 <<< (8 : Word)) |||
      (b2.zeroExtend 64 <<< (16 : Word)) ||| (b3.zeroExtend 64 <<< (24 : Word)) |||
      (b4.zeroExtend 64 <<< (32 : Word)) ||| (b5.zeroExtend 64 <<< (40 : Word)) |||
      (b6.zeroExtend 64 <<< (48 : Word)) ||| (b7.zeroExtend 64 <<< (56 : Word))) j =
      [b0, b1, b2, b3, b4, b5, b6, b7].getD j 0 := by
  interval_cases j <;> (simp only [extractByte]; ext i hi; interval_cases i <;> simp)
theorem extractByte_bytesToWordLE (bs : List (BitVec 8)) (j : Nat) (hj : j < 8) :
    extractByte (bytesToWordLE bs) j = bs.getD j 0 := by
  simp only [bytesToWordLE]
  rw [extractByte_or8 _ _ _ _ _ _ _ _ j hj]
  simp only [List.getD_eq_getElem?_getD]
  interval_cases j <;> rfl
def k0 : List (Reg × Word) :=
  [(.x1, 0), (.x3, 0), (.x4, 0), (.x5, 0), (.x6, 0), (.x7, 0), (.x8, 0), (.x9, 0), (.x10, 0), (.x11, 0),
   (.x12, 0), (.x13, 0), (.x14, 0), (.x15, 0), (.x16, 0), (.x17, 0), (.x18, 0), (.x19, 0), (.x20, 0),
   (.x21, 0), (.x22, 0), (.x23, 0), (.x24, 0), (.x25, 0), (.x26, 0), (.x27, 0), (.x28, 0), (.x29, 0),
   (.x30, 0), (.x31, 0)]
def VERIFY_DATA : Nat := 0xffbde0
def MSGADDR : Nat := 26144
structure InitOK (m : T3.Message) (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (s : MachineState) : Prop where
  known : KnownOK k0 s
  pc : s.pc = pcOf 0
  msg : ∀ k, k < 4 → s.getMem (BitVec.ofNat 64 (MSGADDR + 8 * k)) = m.extractLsb' (64 * k) 64
  pk : PkOK pk s
  wit : WitAll w s
  zero : ∀ A, A < WIT → (A < 0xA0 ∨ 0xB0 ≤ A) → s.getMem (BitVec.ofNat 64 A) = 0
  data : DataOK s
  sp : s.getReg .x2 = BitVec.ofNat 64 VERIFY_DATA
theorem verifyData_length : (submission.image .verify).data.length = 16928 := Images.verifyData_length
theorem dataBase_verify : dataBase (submission.image .verify) = VERIFY_DATA := by
  unfold dataBase; rw [verifyData_length]; decide +kernel
theorem verifyData_mask :
    bytesToWordLE ((((submission.image .verify).data).drop 536).take 8) = 520192#64 := by
  decide +kernel
theorem verifyData_header (lay : Nat) (hl : lay < 4) :
    bytesToWordLE ((((submission.image .verify).data).drop (424 + 8 * ((lay + 1) % 4))).take 8) =
      BitVec.ofNat 64 (hyperBase lay) := by
  interval_cases lay <;> decide +kernel
theorem verifyData_buffer3 :
    bytesToWordLE ((((submission.image .verify).data).drop 360).take 8) = 22288#64 := by
  decide +kernel
/-- Campaign T51: verify data word 16 is the r6 field mask 0xFF00. -/
theorem verifyData_mask6 :
    bytesToWordLE ((((submission.image .verify).data).drop 16).take 8) = 65280#64 := by
  decide +kernel
theorem verifyData_initialMask :
    bytesToWordLE ((((submission.image .verify).data).take 8)) = 0xfff#64 := by
  decide +kernel
set_option maxRecDepth 200000 in
theorem init_ok (m : Legacy.Message) (pk : PublicKey) (w : Bytes 22012) (s : MachineState)
    (h : initialState submission .verify (m, pk, w) = some s) : InitOK m pk w s := by
  unfold initialState at h
  simp only [submission_admissible.2 .verify, if_true, Option.some.injEq] at h
  subst h
  have hl : inputBuffers submission.sizes submission.layout .verify (m, pk, w) =
      [(MSGADDR, bytes m), (0xA0, bytes pk), (0x1020, bytes w)] := rfl
  rw [hl]
  simp only [List.foldl_cons, List.foldl_nil]
  have lm : (bytes m).length = 32 := length_bytes m
  have lp : (bytes pk).length = 16 := length_bytes pk
  have lw : (bytes w).length = 22012 := length_bytes w
  have lD := verifyData_length
  have eD := dataBase_verify
  set blank : MachineState := { regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 }
  set s0 := blank.writeBytesAsWords (BitVec.ofNat 64 (dataBase (submission.image .verify)))
    (submission.image .verify).data
  set s1 := s0.writeBytesAsWords (BitVec.ofNat 64 MSGADDR) (bytes m)
  set s2 := s1.writeBytesAsWords (BitVec.ofNat 64 0xA0) (bytes pk)
  set s3 := s2.writeBytesAsWords (BitVec.ofNat 64 0x1020) (bytes w)
  have gm : ∀ A, (s3.setReg .x2 (BitVec.ofNat 64 (dataBase (submission.image .verify)))).getMem A =
      s3.getMem A := fun A => by simp [MachineState.setReg, MachineState.getMem]
  have g0 : ∀ A, A < 2 ^ 64 → s0.getMem (BitVec.ofNat 64 A) =
      if VERIFY_DATA ≤ A ∧ A < VERIFY_DATA + 8 * ((16928 + 7) / 8) ∧ (A - VERIFY_DATA) % 8 = 0 then
        bytesToWordLE ((((submission.image .verify).data).drop (A - VERIFY_DATA)).take 8) else 0 := by
    intro A hA
    rw [getMem_writeBytesAsWords (submission.image .verify).data blank (dataBase (submission.image .verify)) A
      (by rw [lD, eD]; unfold VERIFY_DATA; omega) hA, lD, eD]; rfl
  have g0z : ∀ A, A < VERIFY_DATA → s0.getMem (BitVec.ofNat 64 A) = 0 := by
    intro A hA
    rw [g0 A (by unfold VERIFY_DATA at hA; omega), if_neg (by omega)]
  have g1 : ∀ A, A < 2 ^ 64 → s1.getMem (BitVec.ofNat 64 A) =
      if MSGADDR ≤ A ∧ A < MSGADDR + 8 * ((32 + 7) / 8) ∧ (A - MSGADDR) % 8 = 0 then
        bytesToWordLE (((bytes m).drop (A - MSGADDR)).take 8) else s0.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [getMem_writeBytesAsWords _ s0 MSGADDR A (by rw [lm]; unfold MSGADDR; omega) hA, lm]
  have g2 : ∀ A, A < 2 ^ 64 → s2.getMem (BitVec.ofNat 64 A) =
      if 0xA0 ≤ A ∧ A < 0xA0 + 8 * ((16 + 7) / 8) ∧ (A - 0xA0) % 8 = 0 then
        bytesToWordLE (((bytes pk).drop (A - 0xA0)).take 8) else s1.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [getMem_writeBytesAsWords _ s1 0xA0 A (by rw [lp]; omega) hA, lp]
  have g3 : ∀ A, A < 2 ^ 64 → s3.getMem (BitVec.ofNat 64 A) =
      if 0x1020 ≤ A ∧ A < 0x1020 + 8 * ((22012 + 7) / 8) ∧ (A - 0x1020) % 8 = 0 then
        bytesToWordLE (((bytes w).drop (A - 0x1020)).take 8) else s2.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [getMem_writeBytesAsWords _ s2 0x1020 A (by rw [lw]; omega) hA, lw]
  have gb : ∀ A, VERIFY_DATA ≤ A → A < 2 ^ 24 →
      (s3.setReg .x2 (BitVec.ofNat 64 (dataBase (submission.image .verify)))).getByte
        (BitVec.ofNat 64 A) = (submission.image .verify).data.getD (A - VERIFY_DATA) 0 := by
    intro A hA hA'
    rw [T3M.getByte_eq_word _ _ (by omega), gm,
      g3 _ (by omega), if_neg (by unfold VERIFY_DATA at hA; omega),
      g2 _ (by omega), if_neg (by unfold VERIFY_DATA at hA; omega),
      g1 _ (by omega), if_neg (by unfold VERIFY_DATA MSGADDR at *; omega),
      g0 _ (by omega), if_pos (by unfold VERIFY_DATA at *; omega),
      extractByte_bytesToWordLE _ _ (Nat.mod_lt _ (by decide +kernel))]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop,
      if_pos (Nat.mod_lt A (show 0 < 8 by decide +kernel))]
    have hidx : A / 8 * 8 - VERIFY_DATA + A % 8 = A - VERIFY_DATA := by
      unfold VERIFY_DATA at hA ⊢
      omega
    rw [hidx]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    have hr1 : ∀ (st : MachineState) (base : Word) (l : List (BitVec 8)),
        (st.writeBytesAsWords base l).regs = st.regs := by
      intro st base l
      induction l using WellFounded.induction (r := fun x y : List (BitVec 8) => x.length < y.length)
        generalizing st base with
      | hwf => exact (measure List.length).wf
      | h l ih =>
        match l with
        | [] => simp
        | b :: bs =>
          unfold MachineState.writeBytesAsWords
          rw [ih _ (by simp only [List.length_drop, List.length_cons]; omega)]
          rfl
    have hr : s3.regs = blank.regs := by simp only [s3, s2, s1, s0, hr1]
    simp only [k0, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [MachineState.setReg, MachineState.getReg, hr, blank]
  · have hp1 : ∀ (st : MachineState) (base : Word) (l : List (BitVec 8)),
        (st.writeBytesAsWords base l).pc = st.pc := by
      intro st base l
      induction l using WellFounded.induction (r := fun x y : List (BitVec 8) => x.length < y.length)
        generalizing st base with
      | hwf => exact (measure List.length).wf
      | h l ih =>
        match l with
        | [] => simp
        | b :: bs =>
          unfold MachineState.writeBytesAsWords
          rw [ih _ (by simp only [List.length_drop, List.length_cons]; omega)]
          rfl
    simp only [MachineState.pc_setReg, s3, s2, s1, s0, hp1, blank]
    rfl
  · intro k hk
    unfold MSGADDR
    rw [gm, g3 _ (by omega), if_neg (by omega), g2 _ (by omega), if_neg (by omega), g1 _ (by omega),
      if_pos (by unfold MSGADDR; omega), show 26144 + 8 * k - MSGADDR = 8 * k by unfold MSGADDR; omega,
      bytes_word m k (by omega)]
  · refine ⟨?_, ?_⟩
    · show (s3.setReg .x2 _).getMem (BitVec.ofNat 64 0xA0) = _
      rw [gm, g3 _ (by omega), if_neg (by omega), g2 _ (by omega), if_pos (by omega),
        show (0xA0 : Nat) - 0xA0 = 8 * 0 by rfl, bytes_word pk 0 (by omega)]
    · show (s3.setReg .x2 _).getMem (BitVec.ofNat 64 0xA8) = _
      rw [gm, g3 _ (by omega), if_neg (by omega), g2 _ (by omega), if_pos (by omega),
        show (0xA8 : Nat) - 0xA0 = 8 * 1 by rfl, bytes_word pk 1 (by omega)]
  · intro j hj
    unfold WX at hj
    rw [gm, g3 _ (by unfold WIT; omega), if_pos (by unfold WIT; omega),
      show WIT + 8 * j - 0x1020 = 8 * j by unfold WIT; omega, bytes_word_lt w j (by norm_num) (by omega)]
    rfl
  · intro A hA hz
    unfold WIT at hA
    rw [gm, g3 _ (by omega), if_neg (by omega), g2 _ (by omega), if_neg (by omega), g1 _ (by omega),
      if_neg (by unfold MSGADDR; omega), g0z A (by unfold VERIFY_DATA; omega)]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [gm, g3 _ (by unfold TOPBASE; omega), if_neg (by unfold TOPBASE; omega),
        g2 _ (by unfold TOPBASE; omega), if_neg (by unfold TOPBASE; omega),
        g1 _ (by unfold TOPBASE; omega), if_neg (by unfold TOPBASE MSGADDR; omega),
        g0 _ (by unfold TOPBASE; omega), if_pos (by unfold TOPBASE VERIFY_DATA; omega),
        show TOPBASE - 8 - VERIFY_DATA = 536 by unfold TOPBASE VERIFY_DATA; omega,
        verifyData_mask]
    · intro lay hl
      have hb := hdrAddr_bounds lay
      unfold TOPBASE at hb
      rw [gm, g3 _ (by omega), if_neg (by omega),
        g2 _ (by omega), if_neg (by omega),
        g1 _ (by omega), if_neg (by unfold MSGADDR; omega),
        g0 _ (by omega), if_pos (by unfold hdrAddr TOPBASE VERIFY_DATA; omega),
        show hdrAddr lay - VERIFY_DATA = 424 + 8 * ((lay + 1) % 4) by unfold hdrAddr TOPBASE VERIFY_DATA; omega,
        verifyData_header lay hl]
    · rw [gm, g3 _ (by unfold TOPB9; omega), if_neg (by unfold TOPB9; omega),
        g2 _ (by unfold TOPB9; omega), if_neg (by unfold TOPB9; omega),
        g1 _ (by unfold TOPB9; omega), if_neg (by unfold TOPB9 MSGADDR; omega),
        g0 _ (by unfold TOPB9; omega), if_pos (by unfold TOPB9 VERIFY_DATA; omega),
        show TOPB9 + 56 - VERIFY_DATA = 360 by unfold TOPB9 VERIFY_DATA; omega,
        verifyData_buffer3]
    · rw [gm, g3 _ (by unfold TOPB9; omega), if_neg (by unfold TOPB9; omega),
        g2 _ (by unfold TOPB9; omega), if_neg (by unfold TOPB9; omega),
        g1 _ (by unfold TOPB9; omega), if_neg (by unfold TOPB9 MSGADDR; omega),
        g0 _ (by unfold TOPB9; omega), if_pos (by unfold TOPB9 VERIFY_DATA; omega),
        show TOPB9 - 288 - VERIFY_DATA = 16 by unfold TOPB9 VERIFY_DATA; omega,
        verifyData_mask6]
  · simp [MachineState.setReg, MachineState.getReg]
    exact congrArg (BitVec.ofNat 64) eD
end SigGolfCandidate.T3M.Verify
end
