import SigGolfCandidate.T3M.Verify.LeafSem

set_option Elab.async false
set_option maxRecDepth 100000

section


section
set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3
namespace LCtx
def lowP (c : LCtx) : M (List Digest) := (List.range' 0 42).foldlM c.chainF [] >>= fun e => c.chainF e 42
def lowCost (c : LCtx) : Nat := c.chainsCost 0 42 + chainCost 42 c.ck
theorem lower_good (c : LCtx) (hc : c.ok) (hi0 : c.i0 = 0) (hko : c.koff = 0) (hck : c.ck < 8) (hRanks : ∀ j, j < 42 → c.headOK j) {s0 : MachineState}
    (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2) (h0 : c.Orig0 s0)
    (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ ends t, c.ChainOut s0 43 ends t → Verify.GoodQ t N C Q A (K ends))
    (s : MachineState) (hs : c.ChainIn s0 0 [] s) :
    Verify.GoodQ s (N + 1720) (C + c.lowCost) Q (A + c.lowCost) (Verify.ccM c.lowP K) := by
  unfold lowP
  rw [Verify.ccM_bind]
  have H := c.chains_good hc hk h0 (fun _ => hko) 42 (by omega) (fun j _ hj => hRanks j hj) (fun e => Verify.ccM (c.chainF e 42) K)
    (N + 40) (C + chainCost 42 c.ck) (A + chainCost 42 c.ck) Q
    (fun ends t ht => c.ck_good hc hk h0 (fun _ => hko) hck K N C A Q hK ends t ht) 42 0 (by omega) (by omega) [] s hs
  refine H.mono (by omega) ?_ (fun hq => ⟨hq, ?_⟩)
  · unfold lowCost; omega
  · unfold lowCost; omega
def coreChain (c : LCtx) (D : List Nat) (i : Nat) : M Digest :=
  chainP c.lay c.tree c.leaf i (D.getD i 0) (maxDigit c.lay i - D.getD i 0)
    (ClaudeWCT.W9.T3M.wchainPads c.w c.lay i).1 (ClaudeWCT.W9.T3M.wchainPads c.w c.lay i).2
    (ClaudeWCT.W9.T3M.wchainHeaderPad c.w c.lay i) (ClaudeWCT.W9.T3M.wvalueFor c.w c.lay D i)
theorem fit_chain (c : LCtx) (hlay : c.lay ≠ 0) (hko : c.koff = 0) (D : List Nat)
    (hD : ∀ i < 43, c.dig i = D.getD i 0) (hS6 : c.S6 = 0x4c0 + ClaudeWCT.W9.T3M.chainBlock c.lay 42 + 1024)
    (i : Nat) (hi : i < 43) :
    chainP c.lay c.tree c.leaf (i + c.koff) (c.dig i) (7 - c.dig i) (c.pad0 i) (c.pad1 i) (c.padHeader i) (c.bufferVal i) =
      c.coreChain D i := by
  unfold coreChain
  have hw : maxDigit c.lay i = 7 := by simp [maxDigit, hlay]
  rw [← hD i hi, hw, hko, Nat.add_zero, c.bufferVal_eq hlay D hD hS6 i hi]
  have hn := chainCount_lower c.lay hlay
  have e : c.blk i - 0x4c0 = ClaudeWCT.W9.T3M.chainBlock c.lay i := by
    unfold blk ClaudeWCT.W9.T3M.chainBlock at *; rw [hS6]; rw [hn] at *; simp only at *; omega
  unfold pad0 pad1 padHeader ClaudeWCT.W9.T3M.wchainPads ClaudeWCT.W9.T3M.wchainHeaderPad
  rw [e, wdig_hi, show ClaudeWCT.W9.T3M.chainBlock c.lay i + 16 + 8 = ClaudeWCT.W9.T3M.chainBlock c.lay i + 24 by omega]
theorem lowP_eq (c : LCtx) (hlay : c.lay ≠ 0) (hko : c.koff = 0) (D : List Nat)
    (hD : ∀ i < 43, c.dig i = D.getD i 0) (hS6 : c.S6 = 0x4c0 + ClaudeWCT.W9.T3M.chainBlock c.lay 42 + 1024) :
    c.lowP = (List.finRange 43).mapM fun i => c.coreChain D i.val := by
  rw [finRange_mapM, List.range_eq_range', show (43 : Nat) = 42 + 1 from rfl, List.range'_append_1.symm,
    List.mapM_append]
  unfold lowP
  have hF : (List.range' 0 42).foldlM c.chainF [] = (fun l => [] ++ l) <$> (List.range' 0 42).mapM
      (fun i => chainP c.lay c.tree c.leaf (i + c.koff) (c.dig i) (7 - c.dig i) (c.pad0 i) (c.pad1 i) (c.padHeader i) (c.bufferVal i)) :=
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
    s6v lay.val = 1216 + ClaudeWCT.W9.T3M.layerBase lay + 16 * ClaudeWCT.W9.T3M.pathSlots lay + 1024 ∧
      ClaudeWCT.W9.T3M.layerBase lay + 16 * ClaudeWCT.W9.T3M.pathSlots lay ≤ layerEnd lay.val ∧
      8256 ≤ ClaudeWCT.W9.T3M.layerBase lay ∧ layerEnd lay.val < 21713 := by
  fin_cases lay
  · exact absurd rfl h
  all_goals decide +kernel
theorem lfS7_pc (lay : Layer) (hlay : lay ≠ 0) (leaf : Nat) (hl : leaf < 2 ^ hL lay.val) :
    BitVec.ofNat 64 (lfS7 lay.val leaf) &&& ~~~1#64 = pcOf (stabW lay.val (leaf % 2 ^ stabBits lay.val)) := by
  have e : lfS7 lay.val leaf = 0x1000 + 4 * stabW lay.val (leaf % 2 ^ stabBits lay.val) := by
    fin_cases lay
    · exact absurd rfl hlay
    all_goals
      simp only [lfS7, dispatchHeap, s7Bias, s7Sh, stabW, stabBits, hL] at hl ⊢
      norm_num at hl ⊢
      rw [Nat.mod_eq_of_lt hl]
      omega
  rw [e, even_andNot1' _ (by omega)]
theorem leafL_step (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer) (hlay : lay ≠ 0)
    (hidx : index < 2 ^ 31) (a : BitVec 256) (s0 : MachineState)
    (hk : ∀ p ∈ (lctxOf w index lay a).known, s0.getReg p.1 = p.2) (hck : (lctxOf w index lay a).ck < 8)
    (hG : Glob (chainK lay.val) w pk s0) (hO : Verify.Orig w (fun o => 8256 ≤ o ∧ o < layerEnd lay.val) s0)
    (h23 : s0.getReg .x23 = BitVec.ofNat 64 (lfS7 lay.val (route index lay).1))
    (h30 : s0.getReg .x31 = BitVec.ofNat 64 (route index lay).2)
    (h1 : s0.getReg .x9 = BitVec.ofNat 64 TOPB9)
    (hBuffer : Verify.Orig w (fun o => BC.bufferStart lay.val ≤ o ∧ o < 24800) s0)
    (ends : List Digest) (t : MachineState)
    (ht : (lctxOf w index lay a).ChainOut s0 43 ends t) :
    ∃ u, Steps image t 5 5 u ∧ LeafOut w pk index lay ends u := by
  set L := lctxOf w index lay a with hLd
  have h0 : lay.val ≠ 0 := fun h => hlay (Fin.ext h)
  obtain ⟨⟨hR, hF, hS⟩, hlen, hpc⟩ := ht
  have hkL : ∀ q ∈ chainK lay.val, s0.getReg q.1 = q.2 := hG.1
  have hknown : KnownOK (leafK lay.val) t := by
    intro p hp
    simp only [leafK, baseK, if_neg h0, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
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
  have hBb : bufferBase lay.val % 8 = 0 ∧ 22928 ≤ bufferBase lay.val ∧ bufferBase lay.val ≤ 25104 := by
    fin_cases lay <;> decide +kernel
  have hBi : 22160 ≤ bufferBias lay.val ∧ bufferBias lay.val ≤ 24592 := by fin_cases lay <;> decide +kernel
  obtain ⟨u, hu⟩ := spec_run (lfSlotCheck_at lay.val L.ck h0 lay.isLt hck) t (by rw [hpc]; rfl) hknown
    (by intro b hb; simp [specLf, h0] at hb) (by simp)
  have hst := hu.steps
  rw [show (specLf lay.val).steps = 5 by simp [specLf, h0],
    show (specLf lay.val).cycles = 5 by simp [specLf, h0]] at hst
  refine ⟨u, hst, ?_⟩
  have hku : KnownOK (postLf lay.val) u := hu.known
  have hkeep := hu.keep
  have hmem : ∀ A, u.getMem A = memEval t [(⟨none, BitVec.ofNat 64 (bufferBase lay.val+24)⟩, kw 0),
      (⟨none, BitVec.ofNat 64 (bufferBase lay.val+16)⟩, .reg .x28)] A := by
    intro A; rw [hu.mem]; simp [specLf, h0]
  have hfr : ∀ A, A < 2 ^ 64 → A ≠ bufferBase lay.val+24 → A ≠ bufferBase lay.val+16 → u.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := by
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
  refine ⟨?_, ?_, fun h => absurd h hlay, ?_, ?_, ?_, ?_, ?_, ?_, fun h => absurd h hlay, ?_⟩
  · rw [hu.spc (tgtLf lay.val) (by simp [specLf, h0])]
    simp only [tgtLf, if_neg h0, E.eval, BinOp.eval]
    rw [hR .x23 (by simp [chainRegs]), h23]
    exact lfS7_pc lay hlay _ hlf
  · have hGt : Glob baseK w pk t := glob_frame hG hF (fun A hA => by
        unfold LCtx.Wr LCtx.bufferWr LCtx.bufferEnd LCtx.bufferSlot LCtx.blk at hA; rw [hS6, hBias] at hA
        have : slotL L.i0 = 768 := rfl
        rw [this] at hA
        simp only [show L.i0 = 0 from rfl, slotL, if_neg (by omega : ¬43=0), if_pos rfl] at hA
        split_ifs at hA <;> rcases hA with hA | hA <;> omega)
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
      memEval_cons_ofNat _ _ _ _ _ (by omega) (by omega), if_neg (by omega),
      memEval_cons_ofNat _ _ _ _ _ (by omega) (by omega), if_pos rfl]
    simp only [E.eval]
    rw [hR .x28 (by simp [chainRegs]), hk (.x28, BitVec.ofNat 64 L.x28v) (by simp [LCtx.known]), routed_eq,
      show below lay.val = BC.below lay.val from rfl, ← hyperWord_x28v w index lay a]
    rfl
  · rw [show lfBase lay.val + 24 = bufferBase lay.val+24 from rfl, hmem,
      memEval_cons_ofNat _ _ _ _ _ (by omega) (by omega), if_pos rfl]
    rfl
  · have hOt : Verify.Orig w (fun o => 8256 ≤ o ∧
        o < ClaudeWCT.W9.T3M.layerBase lay + 16 * ClaudeWCT.W9.T3M.pathSlots lay) t :=
      (hO.mono (fun o ho => ⟨ho.1, by omega⟩)).frame (fun j hj hp => hF.get (by unfold WIT WX at *; omega)
        (fun hw => by
          unfold LCtx.Wr LCtx.bufferWr LCtx.bufferEnd LCtx.bufferSlot LCtx.blk at hw; rw [hS6, hBias] at hw
          simp only [show L.i0 = 0 from rfl, slotL, if_neg (by omega : ¬43=0), if_pos rfl] at hw
          unfold WIT at hw
          split_ifs at hw <;> rcases hw with hw | hw <;> omega))
    exact (hu.orig_const hOt).mono (fun o ho => ⟨ho, by simp only [lfAllowed, List.mem_cons, List.not_mem_nil, or_false]; unfold WIT; omega⟩)
  · intro hLay
    have hfut : BC.bufferStart lay.val ≤ BC.bufferStart (lay.val-1) ∧
        bufferBase lay.val + 720 ≤ WIT + BC.bufferStart (lay.val-1) ∧
        s6v lay.val - 1024 + 64*42 + 80 ≤ WIT + BC.bufferStart (lay.val-1) := by
      fin_cases lay
      · exact absurd rfl hlay
      all_goals decide +kernel
    have hBt : Verify.Orig w (fun o => BC.bufferStart (lay.val-1) ≤ o ∧ o < 24800) t :=
      (hBuffer.mono (fun o ho => ⟨by omega,ho.2⟩)).frame (fun j hj hp =>
        hF.get (by unfold WIT WX at *; omega) (fun hw => by
          unfold LCtx.Wr LCtx.bufferWr LCtx.bufferEnd LCtx.bufferSlot LCtx.blk at hw
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
theorem row_hash (t : MachineState) (A : Nat) (hA8 : A % 8 = 0) (hA : A + 64 < 2 ^ 64) (lay : Layer)
    (tree leaf : Nat) (left right cp : Digest) (h10 : t.getReg .x10 = BitVec.ofNat 64 A)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 64) (h0 : DigAt t A left)
    (h2 : t.getMem (BitVec.ofNat 64 (A + 16)) = T3.hyperWord lay.val (tree * 2 ^ height lay + leaf))
    (h3 : t.getMem (BitVec.ofNat 64 (A + 24)) = 1) (h4 : t.getMem (BitVec.ofNat 64 (A + 32)) = dlo cp)
    (h5 : t.getMem (BitVec.ofNat 64 (A + 40)) = dhi cp) (h6 : DigAt t (A + 48) right) :
    hashInput t = toQ (T3.pad64 (blk4 left (T3.rowTweak lay tree leaf) cp right)) := by
  rw [pad64_blk4]
  apply hashInput_words8 t _ A (blk4_length _ _ _ _) h10 hA8 hA h11
  rw [wordsOf_blk4, rowTweak_lo, rowTweak_hi, h0.1, h0.2, h2, h3, h4, h5, h6.1,
    show A + 48 + 8 = A + 56 by omega] at *
  rw [h6.2]
  rfl
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
      have hm := (hs.msg.pair_low h3).2.2.2 4 (Or.inl rfl)
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
def CounterBranch : Prop := ∀ (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer)
    (msg : LayerMsg) (s : MachineState), LayerIn w pk index lay.val msg s →
  ∀ d, Br.holds s (ctrBr lay.val (cpIdx index lay.val) d) ↔
    d = decide (if lay.val = 3 then (ClaudeWCT.W9.T3M.wbcCtr w index lay).toNat < counterLimit
      else (ClaudeWCT.W9.T3M.wbcCtr w index lay).toNat ≥ counterLimit)
theorem counter_branch : CounterBranch := fun w pk index lay msg s hs d => by
  have h64 : (ClaudeWCT.W9.T3M.wbcCtr w index lay).toNat < 2 ^ 64 :=
    lt_of_lt_of_le (ClaudeWCT.W9.T3M.wbcCtr w index lay).isLt (by decide +kernel)
  norm_num at h64
  unfold ctrBr Br.holds
  rw [counter_eval w pk index lay msg s hs]
  by_cases h3 : lay.val = 3 <;>
    simp [h3, CmpOp.eval, E.eval, kw, BitVec.ult, Nat.mod_eq_of_lt h64,
      counterLimit, ← decide_not, eq_comm]
theorem encoding_reject (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer)
    (msg : LayerMsg) (s : MachineState) (_hs : LayerIn w pk index lay.val msg s)
    (hge : (ClaudeWCT.W9.T3M.wbcCtr w index lay).toNat ≥ ClaudeWCT.WCT9.verifyWindow) :
    ∃ u, Steps image s (rejectSteps lay.val) (rejectSteps lay.val) u ∧
      fetch image u = some (.base .ECALL) ∧ u.getReg .x5 = 1 ∧ u.getReg .x10 = 1 :=
  absurd hge (ClaudeWCT.WCT9.ctr_not_ge_verifyWindow _)
def PairInputBlock : Prop := ∀ (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (tree leaf : Nat)
  (left right : Digest), ClaudeWCT.WCT9.pairEncodingInputP lay tree leaf left right
    (ClaudeWCT.W9.T3M.wbcCtr w index lay) (ClaudeWCT.W9.T3M.wbcPad w index lay) =
  blk4 left (T3.rowTweak lay tree leaf) (ClaudeWCT.W9.T3M.wdig w (ClaudeWCT.W9.T3M.bcCounterOff index lay)) right
theorem pair_input_block : PairInputBlock := fun w index lay tree leaf left right => by
  unfold ClaudeWCT.WCT9.pairEncodingInputP blk4
  simp only [List.append_assoc]
  rw [← List.append_assoc (SphincsSecurity.bytesLE 4 (ClaudeWCT.W9.T3M.wbcCtr w index lay)), counterPadBytes]
  rw [show ClaudeWCT.W9.T3M.wbcPad w index lay ++ ClaudeWCT.W9.T3M.wbcCtr w index lay =
    ClaudeWCT.W9.T3M.wdig w (ClaudeWCT.W9.T3M.bcCounterOff index lay) from counterPadExtract w _]
def EncodingRun : Prop := ∀ (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer)
  (msg : LayerMsg) (s : MachineState), LayerIn w pk index lay.val msg s →
  (ClaudeWCT.W9.T3M.wbcCtr w index lay).toNat < ClaudeWCT.WCT9.verifyWindow →
  ∃ t, SpecRes (allowed lay.val (cpIdx index lay.val)) [] baseK (specA lay.val (cpIdx index lay.val))
      (bK lay.val (cpIdx index lay.val)) (keepA lay.val) s t
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
  ∀ t, SpecRes (allowed lay.val (cpIdx index lay.val)) [] baseK (specA lay.val (cpIdx index lay.val))
    (bK lay.val (cpIdx index lay.val)) (keepA lay.val) s t → EncPre w pk index lay.val (cpIdx index lay.val) t
theorem setup_writes_bounds (lay c : Nat) (hl : lay < 4) (hc : c < nCopy lay) :
    ∀ A ∈ allowed lay c, (A < WIT+8256 ∨ WIT+layerEnd lay ≤ A) ∧ A < WIT+bufferStart lay := by
  have H : ((List.range 4).all fun l => (List.range (nCopy l)).all fun c =>
    (allowed l c).all fun A => decide ((A < WIT+8256 ∨ WIT+layerEnd l ≤ A) ∧ A < WIT+bufferStart l)) = true := by
    decide +kernel
  intro A hA
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp H lay
    (List.mem_range.mpr hl)) c (List.mem_range.mpr hc)) A hA)
theorem setup_post : SetupPost := fun w pk index lay msg s hs t ht => by
  obtain ⟨hlE, htE, -, hs7E⟩ := T3M.route_evals index lay hs.idx s hs.route
  refine ⟨?_, ⟨ht.known, (ht.glob _ w pk hs.glob (RelOK.nil s)).2⟩, ?_, ?_, ?_,
    (ht.orig_const hs.orig).mono (fun o ho => ⟨ho, by
      intro hm
      have H := setup_writes_bounds lay.val _ lay.isLt (T3M.cpIdx_lt index lay.val lay.isLt) _ hm
      rcases H.1 with H | H <;> omega⟩), ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    have hf (A : Nat) (hA : A < 2 ^ 64) (h1 : A ≠ 1232) (h2 : A ≠ 1240) (h3 : A ≠ 1264) (h4 : A ≠ 1272) :
        t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
      rw [hm]
      apply memEval_frame_ofNat s _ A hA
      intro p hp
      simp only [T3M.specA, T3M.l3Writes, ↓reduceIte, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> simp <;> omega
    refine ⟨?_, ?_, fun k hk => ?_⟩
    · rw [hf _ (by unfold TOPLOAD; omega) (by unfold TOPLOAD; omega) (by unfold TOPLOAD; omega)
        (by unfold TOPLOAD; omega) (by unfold TOPLOAD; omega)]
      exact (hs.hdr3 rfl).1
    · rw [hf _ (by unfold TOPLOAD; omega) (by unfold TOPLOAD; omega) (by unfold TOPLOAD; omega)
        (by unfold TOPLOAD; omega) (by unfold TOPLOAD; omega)]
      exact (hs.hdr3 rfl).2.1
    · rw [hf _ (by unfold TOPLOAD; omega) (by unfold TOPLOAD; omega) (by unfold TOPLOAD; omega)
        (by unfold TOPLOAD; omega) (by unfold TOPLOAD; omega)]
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
    intro h3
    obtain ⟨d, hd, hdd⟩ := hs.dst3 h3
    refine ⟨d, ?_, hdd⟩
    obtain rfl : lay = 3 := Fin.ext h3
    rw [ht.regs (.x12, .reg .x12) (by simp [specA, T3M.specA])]
    simpa [E.eval] using hd
  case refine_9 =>
    exact (ht.orig_const hs.bufferOrig).mono (fun o ho => ⟨ho, by
      intro hm
      have H := (setup_writes_bounds lay.val _ lay.isLt (T3M.cpIdx_lt index lay.val lay.isLt) _ hm).2
      omega⟩)
  case refine_10 =>
    intro h0 A hA
    obtain rfl : lay = 0 := Fin.ext h0
    have hr : rowA 0 (cpIdx index 0) + 24 < 25104 := by
      have H : ((List.range (nCopy 0)).all fun c => decide (rowA 0 c + 24 < 25104)) = true := by decide +kernel
      exact of_decide_eq_true (List.all_eq_true.mp H _ (List.mem_range.mpr (T3M.cpIdx_lt index 0 (by decide))))
    have hne (A q : Nat) (hlo : 25104 ≤ A) (hhi : A < 2^64) (hq : q ≤ 24) :
        BitVec.ofNat 64 A ≠ BitVec.ofNat 64 (rowA 0 (cpIdx index 0)+q) := by
      intro he
      have he' := congrArg BitVec.toNat he
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hhi,
        Nat.mod_eq_of_lt (by omega : rowA 0 (cpIdx index 0)+q < 2^64)] at he'
      omega
    have hA' : A = 25104 ∨ A = 25112 := by simpa using hA
    rcases hA' with rfl | rfl <;> rw [ht.mem] <;>
      simp [specA,headerWrites,memEval,Addr.eval,E.eval,kw]
    · rw [if_neg (hne 25104 24 (by omega) (by omega) (by omega)),
        if_neg (hne 25104 16 (by omega) (by omega) (by omega))]
    · rw [if_neg (hne 25112 24 (by omega) (by omega) (by omega)),
        if_neg (hne 25112 16 (by omega) (by omega) (by omega))]
def SetupHash : Prop := ∀ (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer)
  (msg : LayerMsg) (s : MachineState), LayerIn w pk index lay.val msg s →
  ∀ t, SpecRes (allowed lay.val (cpIdx index lay.val)) [] baseK (specA lay.val (cpIdx index lay.val))
    (bK lay.val (cpIdx index lay.val)) (keepA lay.val) s t →
  t.getReg .x5 = 0 ∧ hashArgumentsValid t = true ∧
  hashInput t = toQ (T3.pad64 (ClaudeWCT.W9.T3M.layerEncodingInputP lay
    (route index lay).2 (route index lay).1 msg
    (ClaudeWCT.W9.T3M.wbcCtr w index lay) (ClaudeWCT.W9.T3M.wbcPad w index lay) (ClaudeWCT.W9.T3M.wbcRight w)))
theorem setup_hash : SetupHash := fun w pk index lay msg s hs t ht => by
  have hpost := setup_post w pk index lay msg s hs t ht
  have h5 : t.getReg .x5 = 0 := ht.known (.x5, 0) (by fin_cases lay <;> simp [bK, T3M.bK, layK, baseK])
  have h11 : t.getReg .x11 = BitVec.ofNat 64 64 := ht.known (.x11, _) (by fin_cases lay <;> simp [bK, T3M.bK, layK])
  have hrw := T3M.routed_eq index lay
  by_cases h3 : lay.val = 3
  · obtain rfl : lay = 3 := Fin.ext h3
    cases msg with
    | forest root => exact hs.msg.elim
    | pair left right =>
    have hm3 := hs.msg.pair_top
    have h10 : t.getReg .x10 = BitVec.ofNat 64 1216 := ht.known (.x10, _) (by simp [bK, T3M.bK])
    obtain ⟨d, h12, hd⟩ := hpost.dst3 rfl
    have hm (A : Word) : t.getMem A = memEval s (T3M.specA 3 (trPc 3 (cpIdx index 3))).mem A := ht.mem A
    have hf : ∀ A, A < 2 ^ 64 → A ≠ 1232 → A ≠ 1240 → A ≠ 1264 → A ≠ 1272 →
        t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
      intro A hA h1 h2 h3' h4
      rw [hm]
      apply memEval_frame_ofNat s _ A hA
      intro p hp
      simp only [T3M.specA, T3M.l3Writes, ↓reduceIte, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> simp <;> omega
    have hH : WitHdr w s := hs.glob.2.1
    refine ⟨h5, ?_, ?_⟩
    · rcases hd with rfl | rfl
      · exact hashArgs_of t 1216 64 1200 h10 h11 h12 (by decide +kernel) (by decide +kernel) (by decide +kernel)
          (by decide +kernel) (by decide +kernel)
      · exact hashArgs_of t 1216 64 1344 h10 h11 h12 (by decide +kernel) (by decide +kernel) (by decide +kernel)
          (by decide +kernel) (by decide +kernel)
    change hashInput t = toQ (pad64 (ClaudeWCT.WCT9.pairEncodingInputP 3 (route index 3).2 (route index 3).1 left
      right (ClaudeWCT.W9.T3M.wbcCtr w index 3) (ClaudeWCT.W9.T3M.wbcPad w index 3)))
    rw [pair_input_block, show ClaudeWCT.W9.T3M.bcCounterOff index 3 = 8 * 4 from rfl]
    apply T3M.row_hash t 1216 (by decide +kernel) (by decide +kernel) 3 _ _ left _ _ h10 h11
    · exact ⟨(hf _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans hm3.1.1,
        (hf _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans hm3.1.2⟩
    · rw [hm]; simp only [T3M.specA, T3M.l3Writes, ↓reduceIte, List.cons_append, List.nil_append]
      rw [memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_neg (by norm_num),
        memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_pos rfl]
      rw [t3E3_eval s index hs.idx (by simpa [rReg, below] using hs.route) (hs.hdr3 rfl).1, hrw,
        show T3M.below (3 : Layer).val = 0 from rfl, pow_zero, Nat.div_one]
      try rfl
    · rw [hm]; simp only [T3M.specA, T3M.l3Writes, ↓reduceIte, List.cons_append, List.nil_append]
      rw [memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_pos rfl]; rfl
    · rw [hf _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel), Verify.wdig_lo]; exact hH 4 (by decide +kernel) (by decide +kernel)
    · rw [hf _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel), Verify.wdig_hi]; exact hH 5 (by decide +kernel) (by decide +kernel)
    · refine ⟨?_, ?_⟩
      · rw [hm]; simp only [T3M.specA, T3M.l3Writes, ↓reduceIte, List.cons_append, List.nil_append]
        rw [memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_neg (by norm_num),
          memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_neg (by norm_num),
          memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_neg (by norm_num),
          memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_pos rfl]
        exact hm3.2.1
      · rw [hm]; simp only [T3M.specA, T3M.l3Writes, ↓reduceIte, List.cons_append, List.nil_append]
        rw [memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_neg (by norm_num),
          memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_neg (by norm_num),
          memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_pos rfl]
        exact hm3.2.2
  · cases msg with
    | forest root => exact hs.msg.elim
    | pair left right =>
    have hmsg := hs.msg.pair_low h3
    have hl3 : lay.val < 3 := hmsg.1
    set c := cpIdx index lay.val with hcd
    have hc := T3M.cpIdx_lt index lay.val lay.isLt
    obtain ⟨r16, rlo, rhi, rend⟩ := T3M.rowA_facts lay.val c hl3 hc
    have h10 : t.getReg .x10 = BitVec.ofNat 64 (rowA lay.val c) :=
      ht.known (.x10, _) (by rw [bK, if_neg h3]; exact List.mem_append_right _ (List.mem_singleton_self _))
    obtain ⟨d, h12, hdd⟩ := hpost.dst hl3
    have hm (A : Word) : t.getMem A = memEval s (headerWrites lay.val c) A := by
      simpa [specA, h3] using ht.mem A
    have hrowpad : rowA lay.val c + 64 < 25104 := by
      have H : ((List.range 3).all fun l => (List.range (nCopy l)).all fun c =>
        decide (rowA l c + 64 < 25104)) = true := by decide +kernel
      exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp H lay.val
        (List.mem_range.mpr hl3)) c (List.mem_range.mpr hc))
    have hf : ∀ q, q < 64 → q ≠ 16 → q ≠ 24 →
        t.getMem (BitVec.ofNat 64 (rowA lay.val c + q)) = s.getMem (BitVec.ofNat 64 (rowA lay.val c + q)) := by
      intro q hq h16 h24
      rw [hm]
      apply memEval_frame_ofNat s _ _ (by omega)
      intro p hp
      by_cases h0 : lay.val = 0
      · simp only [headerWrites, if_pos h0, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with (rfl | rfl) | (rfl | rfl) <;> simp <;> omega
      · simp only [headerWrites, if_neg h0, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> simp <;> omega
    refine ⟨h5, hashArgs_of t (rowA lay.val c) 64 d h10 h11 h12 (by omega) (by decide +kernel) (by omega)
      (by rcases hdd with rfl | rfl <;> omega) (by rcases hdd with rfl | rfl <;> omega), ?_⟩
    change hashInput t = toQ (pad64 (ClaudeWCT.WCT9.pairEncodingInputP lay (route index lay).2 (route index lay).1
      left right (ClaudeWCT.W9.T3M.wbcCtr w index lay) (ClaudeWCT.W9.T3M.wbcPad w index lay)))
    rw [pair_input_block]
    have e := T3M.rowA_eq index lay h3
    have h8 := T3M.rowBlock_mod8 index lay
    have hcoff : ClaudeWCT.W9.T3M.bcCounterOff index lay = 8 * ((rowA lay.val c - WIT) / 8 + 4) := by
      unfold ClaudeWCT.W9.T3M.bcCounterOff; rw [e]; unfold WIT at *; omega
    have hm4 := hmsg.2.2.2 4 (Or.inl rfl)
    have hm5 := hmsg.2.2.2 5 (Or.inr rfl)
    apply T3M.row_hash t (rowA lay.val c) (by omega) (by omega) lay _ _ left right _ h10 h11
    · exact ⟨(hf 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans hmsg.2.1.1,
        (hf 8 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans hmsg.2.1.2⟩
    · rw [hm]; unfold headerWrites
      simp only [List.cons_append, List.nil_append]
      rw [memEval_cons_ofNat _ _ _ _ _ (by omega) (by omega), if_neg (by omega),
        memEval_cons_ofNat _ _ _ _ _ (by omega) (by omega), if_pos rfl]
      simp only [E.eval]
      rw [hs.word hl3, show BC.below lay.val = T3M.below lay.val from rfl, ← hrw]
    · rw [hm]; unfold headerWrites
      simp only [List.cons_append, List.nil_append]
      rw [memEval_cons_ofNat _ _ _ _ _ (by omega) (by omega), if_pos rfl]; rfl
    · rw [hf 32 (by decide +kernel) (by decide +kernel) (by decide +kernel), hcoff, Verify.wdig_lo]; simpa using hm4
    · rw [hf 40 (by decide +kernel) (by decide +kernel) (by decide +kernel), hcoff, Verify.wdig_hi]; simpa using hm5
    · exact ⟨(hf 48 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans hmsg.2.2.1.1,
        by rw [show rowA lay.val c + 48 + 8 = rowA lay.val c + 56 by omega,
          hf 56 (by decide +kernel) (by decide +kernel) (by decide +kernel)]; simpa [Nat.add_assoc] using hmsg.2.2.1.2⟩
theorem encoding_setup : EncodingSetup := fun w pk index lay msg s hs => by
  refine ⟨encoding_reject w pk index lay msg s hs, fun hlt => ?_⟩
  obtain ⟨t, ht⟩ := encoding_run w pk index lay msg s hs hlt
  obtain ⟨h5, hv, hin⟩ := setup_hash w pk index lay msg s hs t ht
  exact ⟨t, (by fin_cases lay <;> exact ht.steps), ht.ecall (by fin_cases lay <;> rfl),
    h5, hv, hin, setup_post w pk index lay msg s hs t ht⟩
def EncodingBlocks : Prop := ∀ (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (tree leaf : Nat)
  (msg : LayerMsg), (toQ (pad64 (ClaudeWCT.W9.T3M.layerEncodingInputP lay tree leaf msg
    (ClaudeWCT.W9.T3M.wbcCtr w index lay) (ClaudeWCT.W9.T3M.wbcPad w index lay) (ClaudeWCT.W9.T3M.wbcRight w)))).blocks = 1
theorem encoding_blocks : EncodingBlocks := fun w index lay tree leaf msg => by
  cases msg with
  | forest root =>
    change (toQ (pad64 (ClaudeWCT.WCT9.pairEncodingInputP lay tree leaf root (ClaudeWCT.W9.T3M.wbcRight w)
      (ClaudeWCT.W9.T3M.wbcCtr w index lay) (ClaudeWCT.W9.T3M.wbcPad w index lay)))).blocks = 1
    rw [pair_input_block]
    exact blocks_blk4 _ _ _ _
  | pair left right =>
    change (toQ (pad64 (ClaudeWCT.WCT9.pairEncodingInputP lay tree leaf left right
      (ClaudeWCT.W9.T3M.wbcCtr w index lay) (ClaudeWCT.W9.T3M.wbcPad w index lay)))).blocks = 1
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
    chainP lay tree leaf i.val (digits.getD i.val 0) (maxDigit lay i.val - digits.getD i.val 0)
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
def merkleP (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (value : Digest) : T3.M Digest :=
  (List.finRange (height lay)).foldlM (fun value j => do
    let other := ClaudeWCT.W9.T3M.wpath w lay (route index lay).1 j.val
    let pair := if (route index lay).1 / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
    nodeHashP 3 lay.val (route index lay).2 (2 ^ (height lay - j.val - 1) + (route index lay).1 / 2 ^ (j.val + 1))
      pair.1 (ClaudeWCT.W9.T3M.wmerklePad w lay (route index lay).1 j.val) pair.2) value
theorem layerP_eq (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (digits : List Nat) :
    ClaudeWCT.W9.T3M.layerP w index lay digits = chainsP w lay (route index lay).2 (route index lay).1 digits >>= fun ends =>
      leafHash lay (route index lay).2 (route index lay).1 ends >>= merkleP w index lay := by
  unfold ClaudeWCT.W9.T3M.layerP chainsP merkleP
  generalize route index lay = p
  obtain ⟨leaf, tree⟩ := p
  rfl
def layerHead {β : Type} (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (M : ClaudeWCT.WCT9.LayerMsg)
    (R : List Digest → T3.M (Option β)) : T3.M (Option β) :=
  if (ClaudeWCT.W9.T3M.wbcCtr w index lay).toNat ≥ ClaudeWCT.WCT9.verifyWindow then pure none else
  ClaudeWCT.WCT9.encodingHash lay (ClaudeWCT.W9.T3M.layerEncodingInputP lay (route index lay).2 (route index lay).1 M
    (ClaudeWCT.W9.T3M.wbcCtr w index lay) (ClaudeWCT.W9.T3M.wbcPad w index lay) (ClaudeWCT.W9.T3M.wbcRight w)) >>= fun answer =>
    match decode lay answer with
    | none => pure none
    | some digits => guardedChainsP w index lay answer digits R
def stB (lay : Nat) : Nat := if lay = 0 then 122 else bSt lay+4
def cyB (lay : Nat) : Nat := if lay = 0 then 68 else bCy lay+4
def lfStepsL : Nat := 5
def chainCost0 (lay : Nat) : Nat := if lay = 0 then 1066 else 2935 - 9 * tgtL lay
def chainFuel (lay : Nat) : Nat := if lay = 0 then 2320 else 1720
def layerCost (lay Z : Nat) : Nat := stepsA lay + 8 + cyB lay + lfStepsL + chainCost0 lay - Z
def layerFuel (lay : Nat) : Nat := stepsA lay + 1 + stB lay + chainFuel lay + lfStepsL
def layerCostA (lay : Nat) : Nat := layerCost lay 0 - [21, 10, 9, 9].getD lay 0
theorem layerCostA_low (lay : Layer) (h : lay ≠ 0) :
    layerCostA lay.val = layerCost lay.val 0 - ClaudeWCT.WCT9.producerFloor lay := by
  fin_cases lay
  · exact absurd rfl h
  all_goals rfl
theorem layerCost_vals : layerCost 3 0 = 1177 ∧ layerCost 2 0 = 1166 ∧ layerCost 1 0 = 1175 := by decide +kernel
theorem layerCostA_vals : layerCostA 3 = 1168 ∧ layerCostA 2 = 1157 ∧ layerCostA 1 = 1165 := by decide +kernel
theorem layerFuel_vals : layerFuel 3 = 1770 ∧ layerFuel 2 = 1759 ∧ layerFuel 1 = 1759 := by decide +kernel
theorem ckOf_lt (lay : Layer) (hlay : lay ≠ 0) (a : BitVec 256) (ds : List Nat)
    (hds : decode lay (ansD a) = some ds) : ckOf lay a < 8 := by
  rw [decode_lower_v6 lay hlay] at hds
  split_ifs at hds with h1 h2
  unfold ckOf; rw [tgtL_eq]; exact h2
theorem s6v_chainBlock (lay : Layer) (h : lay ≠ 0) : s6v lay.val = 0x4c0 + ClaudeWCT.W9.T3M.chainBlock lay 42 + 1024 := by
  fin_cases lay
  · exact absurd rfl h
  all_goals decide +kernel
theorem lctx_prefix_eq (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (a : BitVec 256)
    (hlay : lay ≠ 0) (ds : List Nat) (hds : decode lay (ansD a) = some ds) (n : Nat) (hn : n ≤ 42) :
    (List.range' 0 n).foldlM (lctxOf w index lay a).chainF [] =
      (List.range n).mapM (ClaudeWCT.W9.T3M.layerChainP w index lay ds) := by
  set L := lctxOf w index lay a
  have hD := lctx_digits w index lay a hlay ds hds
  have hF : (List.range' 0 n).foldlM L.chainF [] = (fun xs => [] ++ xs) <$>
      (List.range' 0 n).mapM (fun i => chainP L.lay L.tree L.leaf (i + L.koff) (L.dig i) (7 - L.dig i)
        (L.pad0 i) (L.pad1 i) (L.padHeader i) (L.bufferVal i)) := foldlM_app_mapM _ n 0 []
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
theorem chainCount_top : chainCount (0 : Layer) = 54 := by decide +kernel
theorem layerCost_low (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (hlay : lay ≠ 0) (a : BitVec 256)
    (ds : List Nat) (hds : decode lay (ansD a) = some ds) :
    stepsA lay.val + 8 + (bCy lay.val+4) + (lctxOf w index lay a).lowCost + lfStepsL =
      layerCost lay.val ((lctxOf w index lay a).zSum 0 43 + 4*(lctxOf w index lay a).savedCopies 0 43) := by
  have h0 : lay.val ≠ 0 := fun h => hlay (Fin.ext h)
  have hD := lctx_digits w index lay a hlay ds hds
  have hsum := LCtx.decode_lower_sum lay hlay _ ds hds
  have hck : (lctxOf w index lay a).ck < 8 := ckOf_lt lay hlay a ds hds
  have hacc := (lctxOf w index lay a).lowCost_accept hck ds hD hsum.1 (target lay) hsum.2
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
theorem encQ_of_row (lay : Layer) (a : Digest) (tr lf : Nat) (rest : List UInt8)
    (hl : (bytesLE 16 a ++ bytesLE 16 (T3.rowTweak lay tr lf) ++ rest).length ≤ 64) :
    EncQ lay.val (toQ (pad64 (bytesLE 16 a ++ bytesLE 16 (T3.rowTweak lay tr lf) ++ rest))) := by
  unfold EncQ
  refine ⟨pad64 (bytesLE 16 a ++ bytesLE 16 (T3.rowTweak lay tr lf) ++ rest), ?_, rfl,
    ⟨tr * 2 ^ height lay + lf, ?_⟩⟩
  · simp only [pad64, List.length_append, List.length_replicate, bytesLE_length] at hl ⊢
    omega
  · unfold pad64
    rw [List.append_assoc, List.append_assoc, List.drop_left' (bytesLE_length 16 a),
      List.take_left' (bytesLE_length 16 _)]
    try rfl
open SphincsSecurity (bytesLE bytesLE_length) in
theorem encQ_layer (lay : Layer) (tree leaf : Nat) (M : ClaudeWCT.WCT9.LayerMsg) (c : BitVec 32) (pad : BitVec 96)
    (padR : Digest) :
    EncQ lay.val (toQ (pad64 (ClaudeWCT.W9.T3M.layerEncodingInputP lay tree leaf M c pad padR))) := by
  cases M with
  | forest root =>
    change EncQ lay.val (toQ (pad64 (bytesLE 16 root ++ bytesLE 16 (T3.rowTweak lay tree leaf) ++
      bytesLE 4 c ++ bytesLE 12 pad ++ bytesLE 16 padR)))
    simp only [List.append_assoc]
    rw [← List.append_assoc (bytesLE 16 root)]
    exact encQ_of_row lay root tree leaf _ (by simp only [List.length_append, bytesLE_length]; omega)
  | pair left right =>
    change EncQ lay.val (toQ (pad64 (bytesLE 16 left ++ bytesLE 16 (T3.rowTweak lay tree leaf) ++
      bytesLE 4 c ++ bytesLE 12 pad ++ bytesLE 16 right)))
    simp only [List.append_assoc]
    rw [← List.append_assoc (bytesLE 16 left)]
    exact encQ_of_row lay left tree leaf _ (by simp only [List.length_append, bytesLE_length]; omega)
theorem layer_good_low (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer) (hlay : lay ≠ 0) (M : ClaudeWCT.WCT9.LayerMsg)
    (s : MachineState) (hs : LayerIn w pk index lay.val M s) {β : Type} (R : List Digest → T3.M (Option β))
    (K : Option β → OracleComp HashSpec Obs) (hK0 : K none = pure (false, 0)) (N C A : Nat) (Q : Prop)
    (hR : ∀ ends u, LeafOut w pk index lay ends u → GoodQ u N C Q A (ccM (R ends) K)) :
    GoodQ s (N + layerFuel lay.val) (C + layerCost lay.val 0) Q (A + layerCostA lay.val)
      (ccM (layerHead w index lay M R) K) := by
  have h0 : lay.val ≠ 0 := fun h => hlay (Fin.ext h)
  have hlf : lfStepsL = 5 := rfl
  have hidx := hs.idx
  have hA := BC.encoding_setup w pk index lay M s hs
  have hT : 9 * tgtL lay.val ≤ 2935 := by fin_cases lay <;> decide +kernel
  have hF : ClaudeWCT.WCT9.producerFloor lay + 9 * tgtL lay.val ≤ 2935 := by fin_cases lay <;> decide +kernel
  have hfuel : layerFuel lay.val = stepsA lay.val + 1 + (bSt lay.val+4) + 1720 + lfStepsL := by
    simp [layerFuel, stB, chainFuel, h0]
  have hcost : layerCost lay.val 0 = stepsA lay.val + 8 + (bCy lay.val+4) + lfStepsL + (2935 - 9 * tgtL lay.val) := by
    simp only [layerCost, cyB, chainCost0, if_neg h0]; omega
  have hcostA : layerCostA lay.val = stepsA lay.val + 8 + (bCy lay.val+4) + lfStepsL +
      (2935 - 9 * tgtL lay.val - ClaudeWCT.WCT9.producerFloor lay) := by
    rw [layerCostA_low lay hlay, hcost]; omega
  have hbS : 25 ≤ (bSt lay.val+4) := by unfold bSt; split_ifs <;> omega
  have hbC : 28 ≤ (bCy lay.val+4) := by unfold bCy; split_ifs <;> omega
  have hrej : BC.rejectSteps lay.val ≤ stepsA lay.val + 21 := by
    unfold BC.rejectSteps; split_ifs <;> omega
  unfold layerHead
  by_cases hctr : (ClaudeWCT.W9.T3M.wbcCtr w index lay).toNat ≥ ClaudeWCT.WCT9.verifyWindow
  · rw [if_pos hctr, ccM_pure, hK0]
    obtain ⟨u, hst, hf, h5, h10⟩ := hA.1 hctr
    exact GoodQ.steps' hst (GoodQ.reject (Q := Q) (A := 0) hf h5 h10) (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
  · rw [if_neg hctr]
    obtain ⟨t, hst, hf, h5, hv, hin, hpre⟩ := hA.2 (by omega)
    have hblk := BC.encoding_blocks w index lay (route index lay).2 (route index lay).1 M
    have hq := encQ_layer lay (route index lay).2 (route index lay).1 M (ClaudeWCT.W9.T3M.wbcCtr w index lay)
      (ClaudeWCT.W9.T3M.wbcPad w index lay) (ClaudeWCT.W9.T3M.wbcRight w)
    have H : ∀ a : BitVec 256, GoodQP (fun hash => hash (toQ (pad64 (ClaudeWCT.W9.T3M.layerEncodingInputP lay
        (route index lay).2 (route index lay).1 M (ClaudeWCT.W9.T3M.wbcCtr w index lay) (ClaudeWCT.W9.T3M.wbcPad w index lay)
        (ClaudeWCT.W9.T3M.wbcRight w)))) = a ∧
          HashOk hash) (writeHash t a) (N + lfStepsL + 1720 + (bSt lay.val+4))
        (C + lfStepsL + (2935 - 9 * tgtL lay.val) + (bCy lay.val+4))
        Q (A + lfStepsL + (2935 - 9 * tgtL lay.val - ClaudeWCT.WCT9.producerFloor lay) + (bCy lay.val+4))
        (ccM (match decode lay (ansD (selectedView a)) with
          | none => pure none
          | some digits => guardedChainsP w index lay (ansD (selectedView a)) digits R) K) := by
      intro a
      have hB := encB_step w pk index lay hlay _ (cpIdx_lt index lay.val lay.isLt) hidx t hpre a
      cases hds : decode lay (ansD (selectedView a)) with
      | none =>
        dsimp only
        rw [ccM_pure, hK0]
        obtain ⟨v, k, cy, hst', hrejected, hk, hcy⟩ := hB.1 hds
        have hrej : GoodQ v 1 1 Q 0 (pure (false,0)) := by
          rcases hrejected with hf' | ⟨hf',h5',h10'⟩
          · exact (GoodQ.fetch_none (Q := Q) (A := 0) hf').mono (by omega) (by omega) (fun h => ⟨h,by omega⟩)
          · exact GoodQ.reject hf' h5' h10'
        exact (GoodQ.steps' hst' hrej (by omega) (by omega)
          (fun hq => ⟨hq, by omega⟩)).toP.pre_mono (fun _ h => h.2)
      | some ds =>
        dsimp only
        obtain ⟨s0, k0, cy0, hst0, hk0, hcy0, hLok, hkn, hO0, hIn, hG0, hOr0, h23, h30, h1, hBuf0⟩ := hB.2 (by rw [hds]; simp)
        set L := lctxOf w index lay (selectedView a) with hLd
        have hD := lctx_digits w index lay (selectedView a) hlay ds hds
        have hsum := LCtx.decode_lower_sum lay hlay _ ds hds
        have hck : L.ck < 8 := ckOf_lt lay hlay (selectedView a) ds hds
        have hacc := L.lowCost_accept hck ds hD hsum.1 (target lay) hsum.2
        rw [← tgtL_eq] at hacc
        have hcr : L.zSum 0 43 = ClaudeWCT.WCT9.wordCredit lay ds := zSum_eq_wordCredit L lay hlay ds hD
        have hsave : L.savedCopies 0 43 = ClaudeWCT.WCT9.savedCopies lay ds := savedCopies_eq L hlay ds hD
        have hP := L.lowP_eq hlay rfl ds hD (s6v_chainBlock lay hlay)
        by_cases hgood : ClaudeWCT.WCT9.lowerRankGood (ansD (selectedView a))
        · simp only [guardedChainsP, ClaudeWCT.WCT9.lowerGuardedRun_of_good _ _ _ hgood, bind_map_left]
          have hG := L.lower_good hLok rfl rfl hck (lctx_headOK w index lay (selectedView a) hgood) hkn hO0 (fun ends => ccM (R ends) K) (N + lfStepsL) (C + lfStepsL) (A + lfStepsL) Q
            (fun ends t ht => by
              obtain ⟨u, hstu, hu⟩ := leafL_step w pk index lay hlay hidx (selectedView a) s0 hkn hck hG0 hOr0 h23 h30 h1 hBuf0 ends t ht
              exact GoodQ.steps' hstu (hR ends u hu) (by unfold lfStepsL; omega) (by unfold lfStepsL; omega)
                (fun hq => ⟨hq, by unfold lfStepsL; omega⟩))
            s0 hIn
          have e : chainsP w lay (route index lay).2 (route index lay).1 ds = L.lowP := by
            rw [hP]; unfold chainsP; rw [LCtx.chainCount_lower lay hlay]; rfl
          rw [ccM_bind, e]
          have body : ∀ k, k ≤ L.zSum 0 43 + 4*L.savedCopies 0 43 →
              GoodQ (writeHash t a) (N + lfStepsL + 1720 + (bSt lay.val+4))
                (C + lfStepsL + (2935 - 9 * tgtL lay.val) + (bCy lay.val+4))
                Q (A + lfStepsL + (2935 - 9 * tgtL lay.val - k) + (bCy lay.val+4))
                (ccM L.lowP (fun ends => ccM (R ends) K)) := fun k hk =>
            GoodQ.steps' hst0 hG (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
          by_cases hcf : ClaudeWCT.WCT9.producerFloor lay ≤ ClaudeWCT.WCT9.wordCredit lay ds + 4*ClaudeWCT.WCT9.savedCopies lay ds
          · exact (body _ (by omega)).toP.pre_mono (fun _ h => h.2)
          · refine GoodQP.of_false (body 0 (Nat.zero_le _)) ?_
            rintro hash ⟨hea, hok⟩
            have hh := hok lay _ hq ds (by rw [hea, ← selectedView_answer lay hlay]; exact hds)
            apply hcf
            simpa [ClaudeWCT.WCT9.dispatchPenalty,hlay] using hh
        · have hj := ClaudeWCT.WCT9.lowerFirstBad_lt (ansD (selectedView a)) hgood
          have hbad : L.kOf (ClaudeWCT.WCT9.lowerFirstBad (ansD (selectedView a))) <
              rankFloor (ClaudeWCT.WCT9.lowerFirstBad (ansD (selectedView a))) := by
            rw [lctx_rank_eq w index lay (selectedView a) _ hj]
            exact ClaudeWCT.WCT9.lowerFirstBad_bad (ansD (selectedView a)) hgood
          have hranks : ∀ i, i < 3 * ClaudeWCT.WCT9.lowerFirstBad (ansD (selectedView a)) → L.headOK i := by
            intro i hi _ _
            rw [lctx_rank_eq w index lay (selectedView a) _ (by omega)]
            exact ClaudeWCT.WCT9.lowerFirstBad_before (ansD (selectedView a)) hgood (i / 3) (by omega)
          have hpref := L.chains_prefix_fault hLok rfl rfl hkn hO0 _ hj hbad hranks s0 hIn
          have hpcost := L.chainsCost_prefix_le (3 * ClaudeWCT.WCT9.lowerFirstBad (ansD (selectedView a))) (by omega)
          have hle : L.chainsCost 0 42 ≤ L.lowCost := by unfold LCtx.lowCost; omega
          simp only [guardedChainsP, ClaudeWCT.WCT9.lowerGuardedRun, if_neg hgood, bind_assoc, pure_bind,
            ccM_bind, ccM_pure, hK0]
          rw [← lctx_prefix_eq w index lay (selectedView a) hlay ds hds _ (by omega)]
          exact (GoodQ.steps' hst0 hpref (by omega) (by omega) (fun hf => hf.elim)).toP.pre_mono
            (fun _ h => h.2)
    have := GoodQP.encodingHash_bind_pre (f := fun answer => match decode lay answer with
      | none => pure none
      | some digits => guardedChainsP w index lay answer digits R) hf h5 hv hin (fun a => by simpa only [selectedView_answer lay hlay] using H a)
    rw [hblk] at this
    exact (GoodQP.steps' hst this (by omega) (by omega) (by omega)).toGoodQ
theorem layerIn_of_fts (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (idx : Nat) (left right : Digest) (u : MachineState)
    (hidx : idx < 2 ^ 31) (hglob : Glob baseK w pk u) (hreg : u.getReg .x22 = BitVec.ofNat 64 idx)
    (hpc : u.pc = pcOf 850) (hleft : DigAt u WIT left) (hright : DigAt u (WIT + 144) right)
    (hwit : Verify.Orig w (fun o => (32 ≤ o ∧ o < 48) ∨ (8256 ≤ o ∧ o < 24800)) u)
    (hbase8 : u.getReg .x8 = BitVec.ofNat 64 (WIT + 176)) (ha1 : u.getReg .x11 = 64)
    (ha2 : u.getReg .x12 = BitVec.ofNat 64 1200 ∨ u.getReg .x12 = BitVec.ofNat 64 1344)
    (hs10 : u.getReg .x26 = 6) (hOne : u.getReg .x7 = 1) (hTwo : u.getReg .x13 = 2) (hSeven : u.getReg .x30 = 7)
    (hThree : u.getReg .x19 = 3) (hFour : u.getReg .x20 = 4) (hFive : u.getReg .x21 = 5)
    (hCoord : u.getReg .x6 = 0x10000)
    (hbase : u.getReg .x9 = BitVec.ofNat 64 TOPB9)
    (htop : ∀ k, k < 5 → u.getMem (BitVec.ofNat 64 (TOPLOAD + 8 * k)) =
      BitVec.ofNat 64 (topWords.getD k 0))
    (htop8 : u.getMem (BitVec.ofNat 64 (TOPLOAD - 8)) = BitVec.ofNat 64 21200) :
    ∃ t, Steps image u 0 0 t ∧ LayerIn w pk idx 3 (.pair left right) t := by
  have hpk : preK 3 = baseK ++ [(.x8, BitVec.ofNat 64 1392), (.x11, 64), (.x26, 6), (.x7, 1), (.x13, 2), (.x30, 7),
      (.x9, BitVec.ofNat 64 TOPB9), (.x19, 3), (.x20, 4), (.x21, 5), (.x6, 0x10000)] := rfl
  have hk : ∀ p ∈ preK 3, u.getReg p.1 = p.2 := by
    intro p hp
    rw [hpk] at hp
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with hp | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hglob.1 p hp
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
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [show rReg 3 = .x22 from rfl, show BC.below 3 = 0 from rfl, pow_zero, Nat.div_one, hreg]
  · intro h
    exact absurd h (by decide +kernel)
  · exact ⟨hleft, hright⟩
  · exact hwit.mono (fun o ho => Or.inr ⟨ho.1, lt_of_lt_of_le ho.2 (by decide +kernel)⟩)
  · intro _
    exact ⟨(htop 4 (by decide +kernel)).trans (by decide +kernel), htop8, htop⟩
  · intro h
    exact absurd h (by decide +kernel)
  · intro _
    rcases ha2 with h | h
    · exact ⟨1200, h, Or.inl rfl⟩
    · exact ⟨1344, h, Or.inr rfl⟩
  · exact hwit.mono (fun o ho => Or.inr ⟨by have hh : 21712 ≤ o := ho.1; omega,ho.2⟩)
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
