import SigGolfCandidate.T3.Nonbinary.Cost
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsDispatchCtx
import SigGolfCandidate.T3M.Verify.Nonbinary.LayerContext
import SigGolfCandidate.T3M.Verify.MerkleSem
import SigGolfCandidate.T3M.Verify.Init
import SigGolfCandidate.W9Drv.GateDefs
import SigGolfCandidate.W9Drv.SourceBridge

section












section
namespace SigGolfCandidate.T3.Nonbinary
open SigGolfResearch.NonbinaryTop
theorem decode_top_credit {value : Digest} {digits : List Nat}
    (h : T3.decode 0 value = some digits) :
    ∃ w : Codec.Word, Decoder.decodeBV value = some w ∧ digits = wordDigits w ∧
      Counting.weight w = 128 ∧ 11 ≤ Cost.credit w := by
  rw [decode_top_eq_map] at h
  cases hw : Decoder.decodeBV value with
  | none => simp [hw] at h
  | some w =>
    have hd : wordDigits w = digits := by simpa only [hw,Option.map_some,Option.some.injEq] using h
    have hs := (Decoder.decode_some_iff value.toFin w).mp hw
    have hc := Cost.weight_le_credit w
    exact ⟨w, rfl, hd.symm, hs.2, by omega⟩
end SigGolfCandidate.T3.Nonbinary
#print axioms SigGolfCandidate.T3.Nonbinary.decode_top_credit
end
section
namespace SigGolfCandidate.T3M.Nonbinary.NCtx
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SigGolfResearch.NonbinaryTop
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
def digitCredit (i d : Nat) : Nat := if last i≤d then 1 else 0
def digitSum (f : Nat → Nat) : Nat := ((List.range 54).map f).sum
def creditSum (f : Nat → Nat) : Nat := ((List.range 54).map fun i => digitCredit i (f i)).sum
def liveCredit (i d : Nat) : Nat := if d < topMax i then 1 else 0
def liveSum (f : Nat → Nat) : Nat := ((List.range 54).map fun i => liveCredit i (f i)).sum
def totalCost (f : Nat → Nat) : Nat := ((List.range 54).map fun i => chainCost i (f i)).sum
theorem chainCost_balance (i d : Nat) (hd : d≤topMax i) :
    chainCost i d+9*d+digitCredit i d+liveCredit i d=5+tableJump i+9*topMax i := by
  have hm := topMax_bounds i
  have hl : last i+1=topMax i := by unfold last;omega
  unfold chainCost digitCredit liveCredit
  split_ifs <;> omega
theorem total_balance (f : Nat → Nat) (hd : ∀i,i<54 → f i≤topMax i) :
    totalCost f+9*digitSum f+creditSum f+liveSum f=2205 := by
  have H : ∀ l : List Nat,(∀i∈l,f i≤topMax i) →
      (l.map fun i => chainCost i (f i)).sum+9*(l.map f).sum+
        (l.map fun i => digitCredit i (f i)).sum+(l.map fun i => liveCredit i (f i)).sum=
        (l.map fun i => 5+tableJump i+9*topMax i).sum := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
      intro h
      have hi := chainCost_balance i (f i) (h i (by simp))
      have ht := ih (fun j hj => h j (by simp [hj]))
      simp only [List.map_cons,List.sum_cons]
      omega
  have hs := H (List.range 54) (fun i hi => hd i (List.mem_range.mp hi))
  have he : ((List.range 54).map fun i => 5+tableJump i+9*topMax i).sum=2205 := by decide +kernel
  exact hs.trans he
theorem total_cost_credit (f : Nat → Nat) (hd : ∀i,i<54 → f i≤topMax i)
    (hs : digitSum f=128) : totalCost f+17*4+1+creditSum f+liveSum f=1122 := by
  have h := total_balance f hd
  omega
theorem packed_credit_floor (f : Nat → Nat) (hd : ∀i,i<54 → f i≤topMax i) :
    54 ≤ creditSum f + liveSum f := by
  have H : ∀ l : List Nat, (∀ i ∈ l, f i ≤ topMax i) →
      l.length ≤ (l.map fun i => digitCredit i (f i)).sum +
        (l.map fun i => liveCredit i (f i)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
      intro h
      have hi := h i (by simp)
      have ht := ih (fun j hj => h j (by simp [hj]))
      have hcredit : 1 ≤ digitCredit i (f i) + liveCredit i (f i) := by
        unfold digitCredit liveCredit last
        split_ifs <;> omega
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      omega
  simpa only [creditSum, liveSum, List.length_range] using
    H (List.range 54) (fun i hi => hd i (List.mem_range.mp hi))
def exactSum (f : Nat → Nat) : Nat := ((List.range 54).map fun i => if f i = last i then 1 else 0).sum
theorem credit_live_exact (f : Nat → Nat) (hd : ∀i,i<54 → f i≤topMax i) :
    creditSum f + liveSum f = 54 + exactSum f := by
  have H : ∀ l : List Nat, (∀ i ∈ l, f i ≤ topMax i) →
      (l.map fun i => digitCredit i (f i)).sum + (l.map fun i => liveCredit i (f i)).sum =
        l.length + (l.map fun i => if f i = last i then 1 else 0).sum := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
      intro h
      have hi := h i (by simp)
      have ht := ih (fun j hj => h j (by simp [hj]))
      have hm := topMax_bounds i
      have hcredit : digitCredit i (f i) + liveCredit i (f i) = 1 + (if f i = last i then 1 else 0) := by
        unfold digitCredit liveCredit last
        split_ifs <;> omega
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      omega
  simpa only [creditSum, liveSum, exactSum, List.length_range] using
    H (List.range 54) (fun i hi => hd i (List.mem_range.mp hi))
theorem topCredit_exact (v : Digest) : T3.topCredit v = exactSum (coreDigit 0 v) := by
  unfold T3.topCredit exactSum
  congr 1
theorem range_map_ofFn (f : Nat → Nat) :
    (List.range 54).map f=List.ofFn (fun i : Fin 54 => f i.val) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj;simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
theorem source_credit_parse {v : Digest} {w : Codec.Word}
    (hp : Decoder.parse 17 v.toNat=some w) : creditSum (coreDigit 0 v)=Cost.credit w := by
  unfold creditSum
  rw [range_map_ofFn,List.ofFn_add (n:=51) (m:=3),List.sum_append]
  change (List.ofFn fun i : Fin (17*3) => digitCredit i.val (coreDigit 0 v i.val)).sum+
      (List.ofFn fun k : Fin 3 => digitCredit (51+k.val) (coreDigit 0 v (51+k.val))).sum=Cost.credit w
  rw [List.ofFn_mul]
  simp only [List.sum_flatten,List.map_ofFn,List.sum_ofFn,Function.comp_def]
  unfold Cost.credit Cost.credit5 Cost.credit4
  apply congrArg₂ Nat.add
  · apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    have he := T3.Nonbinary.coreDigit_parse5 hp j k
    have hl : last (j.val*3+k.val)=3 := by
      unfold last topMax mx
      rw [if_pos (by have := j.isLt;have := k.isLt;omega)]
    simpa only [digitCredit,hl,Nat.mul_comm] using congrArg (fun d => if 3≤d then (1:Nat) else 0) he
  · apply Finset.sum_congr rfl
    intro k hk
    have he := T3.Nonbinary.coreDigit_parse4 hp k
    have hl : last (51+k.val)=2 := by
      unfold last topMax mx
      rw [if_neg (by have := k.isLt;omega)]
    simpa only [digitCredit,hl] using congrArg (fun d => if 2≤d then (1:Nat) else 0) he
theorem source_accepted_credit {v : Digest} {digits : List Nat}
    (h : T3.decode 0 v=some digits) : 11≤creditSum (coreDigit 0 v) := by
  obtain ⟨w,hw,_,_,hc⟩ := T3.Nonbinary.decode_top_credit h
  have hp : Decoder.parse 17 v.toNat=some w := by
    change ((Decoder.parse 17 v.toNat).filter fun w => decide (Counting.weight w=128))=some w at hw
    exact (Option.filter_eq_some_iff.mp hw).1
  rw [source_credit_parse hp]
  exact hc
theorem source_accepted_sum {v : Digest} {digits : List Nat}
    (h : T3.decode 0 v=some digits) : digitSum (coreDigit 0 v)=128 := by
  obtain ⟨w,hw,_,hs,_⟩ := T3.Nonbinary.decode_top_credit h
  have hp : Decoder.parse 17 v.toNat=some w := by
    change ((Decoder.parse 17 v.toNat).filter fun w => decide (Counting.weight w=128))=some w at hw
    exact (Option.filter_eq_some_iff.mp hw).1
  change (dataDigits 0 v).sum=128
  rw [T3.Nonbinary.dataDigits_parse hp,T3.Nonbinary.wordDigits_sum,hs]
theorem source_accepted_total {v : Digest} {digits : List Nat}
    (h : T3.decode 0 v=some digits) : totalCost (coreDigit 0 v)+17*4≤1067 := by
  have hd : ∀i,i<54 → coreDigit 0 v i≤topMax i := by
    intro i hi
    have hc := T3.Nonbinary.coreDigit_le (0:Layer) v i
    have he : maxDigit 0 i=topMax i := by
      unfold maxDigit topMax mx
      simp only [ite_true]
      split_ifs <;> omega
    rw [he] at hc
    exact hc
  have hb := total_cost_credit (coreDigit 0 v) hd (source_accepted_sum h)
  have hc := packed_credit_floor (coreDigit 0 v) hd
  omega
theorem source_accepted_total_credit {v : Digest} {digits : List Nat}
    (h : T3.decode 0 v=some digits) : totalCost (coreDigit 0 v)+17*4+T3.topCredit v=1067 := by
  have hd : ∀i,i<54 → coreDigit 0 v i≤topMax i := by
    intro i hi
    have hc := T3.Nonbinary.coreDigit_le (0:Layer) v i
    have he : maxDigit 0 i=topMax i := by
      unfold maxDigit topMax mx
      simp only [ite_true]
      split_ifs <;> omega
    rw [he] at hc
    exact hc
  have hb := total_cost_credit (coreDigit 0 v) hd (source_accepted_sum h)
  have hc := credit_live_exact (coreDigit 0 v) hd
  rw [topCredit_exact]
  omega
#print axioms total_cost_credit
#print axioms source_accepted_total
end SigGolfCandidate.T3M.Nonbinary.NCtx
end
section
namespace SigGolfCandidate.T3M.Nonbinary.NCtx
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Nonbinary SigGolfCandidate.T3
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
def TopOut (c : NCtx) (s0 : MachineState) (acc : List Digest) (s : MachineState) : Prop :=
  (∀ x, x ∉ chainRegs → x ≠ .x15 → s.getReg x=s0.getReg x) ∧
  Frame s0 s (c.Wr 54) ∧ acc.length=54 ∧
  (∀ j < acc.length, DigAt s (slot j) (acc.getD j 0)) ∧ (∃ dB dC, dB < 4 ∧ dC < 4 ∧ s.pc = pcOf (pcX 17 dB dC)) ∧ s.getReg .x15 = 712704#64
theorem end_return (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 b : MachineState}
    (hk : ∀ p ∈ c.known, s0.getReg p.1=p.2) (hb : b.getReg .x15 = 712704#64)
    (acc : List Digest) (s : MachineState) (hs : c.EndInv (tailInitial s0 b) 53 acc s) :
    ∃ t, Steps vimage s 0 0 t ∧ c.TopOut s0 acc t := by
  obtain ⟨⟨hR,hF,hS⟩,hlen,hpc⟩ := hs
  have hB := c.dig_group_le hds 17 1 (by decide) (by decide)
  have hC := c.dig_group_le hds 17 2 (by decide) (by decide)
  refine ⟨s, Steps.refl s, ⟨fun x hx hx15 => ?_, ?_, hlen, ?_, ?_, ?_⟩⟩
  · exact (hR x hx).trans (tailInitial_regs _ _ _ hx15)
  · exact hF
  · intro j hj; exact hS j hj
  · refine ⟨c.dig 52, c.dig 53, ?_, ?_, ?_⟩
    · simpa [mx] using Nat.lt_succ_of_le hB
    · simpa [mx] using Nat.lt_succ_of_le hC
    · simpa [endPc, qX] using hpc
  · exact (hR .x15 (by decide)).trans ((tailInitial_15 _ _).trans hb)

theorem chainsCost_add (c : NCtx) (i n k : Nat) :
    c.chainsCost i (n+k)=c.chainsCost i n+c.chainsCost (i+n) k := by
  unfold chainsCost
  rw [← List.range'_append_1,List.map_append,List.sum_append]
theorem prefix_good (c : NCtx) (hc : c.ok) {s0 : MachineState} {v : Digest}
    (hk : ∀ p ∈ c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0)
    (he : Encoded v s0) (hf : c.Fit v) (hv : topRanksValid v=true)
    (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ acc t,c.EndInv s0 50 acc t → Verify.GoodQ t N C Q A (K acc)) :
    ∀ n q, n+q=17 → 0<n → ∀ acc s,c.ChainIn s0 (3*q) acc s →
      Verify.GoodQ s (N+124*n) (C+c.chainsCost (3*q) (3*n)+4*(n-1)) Q
        (A+c.chainsCost (3*q) (3*n)+4*(n-1))
        (Verify.ccM ((List.range' (3*q) (3*n)).foldlM c.chainF acc) K) := by
  intro n
  induction n with
  | zero => intro q _ h;omega
  | succ n ih =>
    intro q hn _ acc s hs
    have hd := c.fit_digits hf
    by_cases hz : n=0
    · subst n
      have hq : q=16 := by omega
      subst q
      have H := c.group_good hc hd hk h0 16 (by decide) K N C A Q hK 3 48 (by decide) (by decide) (by decide) acc s hs
      exact H.mono (by omega) (by simp) (fun h => ⟨h,by simp⟩)
    · rw [show 3*(n+1)=3+3*n by omega,← List.range'_append_1,List.foldlM_append,Verify.ccM_bind]
      have H := c.group_good hc hd hk h0 q (by omega)
        (fun ends => Verify.ccM ((List.range' (3*q+3) (3*n)).foldlM c.chainF ends) K)
        (N+124*n+4) (C+c.chainsCost (3*(q+1)) (3*n)+4*(n-1)+4)
        (A+c.chainsCost (3*(q+1)) (3*n)+4*(n-1)+4) Q
        (fun ends t ht => by
          obtain ⟨u,st,hu⟩ := c.end_dispatch hc hd he hf hv q (by omega) ends t ht
          have H := ih (q+1) (by omega) (by omega) ends u hu
          rw [show 3*(q+1)=3*q+3 by omega] at H
          exact Verify.GoodQ.steps st H)
        3 (3*q) (le_refl _) (by omega) (by decide) acc s hs
      have ec := c.chainsCost_add (3*q) 3 (3*n)
      rw [show 3*q+3=3*(q+1) by omega] at ec
      exact H.mono (by omega) (by omega) (fun h => ⟨h,by omega⟩)
def topP (c : NCtx) : M (List Digest) := (List.range' 0 54).foldlM c.chainF []
theorem top_good_exact (c : NCtx) (hc : c.ok) {s0 : MachineState} {v : Digest}
    (hk : ∀ p ∈ c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0)
    (he : Encoded v s0) (hf : c.Fit v) (hv : v.toNat<2^125) (hr : topRanksValid v=true)
    (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ acc t,c.TopOut s0 acc t → Verify.GoodQ t N C Q A (K acc))
    (s : MachineState) (hs : c.ChainIn s0 0 [] s) :
    Verify.GoodQ s (N+2320) (C+c.chainsCost 0 54+67) Q (A+c.chainsCost 0 54+67)
      (Verify.ccM c.topP K) := by
  have hd := c.fit_digits hf
  unfold topP
  rw [show (54:Nat)=51+3 from rfl,← List.range'_append_1,List.foldlM_append,Verify.ccM_bind]
  have H := c.prefix_good hc hk h0 he hf hr
    (fun ends => Verify.ccM ((List.range' 51 3).foldlM c.chainF ends) K)
    (N+124) (C+c.chainsCost 51 3+3) (A+c.chainsCost 51 3+3) Q
    (fun ends t ht => by
      obtain ⟨u,st,hu,hu15⟩ := c.end_tail hc hd he hf hv ends t ht
      have H := c.group_good hc hd (c.tailInitial_known hk) (c.tailInitial_orig h0) 17 (by decide)
        K N C A Q
        (fun acc t ht => by
          obtain ⟨u,st,hu⟩ := c.end_return hc hd hk hu15 acc t ht
          exact Verify.GoodQ.steps st (hK acc u hu))
        3 51 (by decide) (by decide) (by decide) ends u hu
      have H := Verify.GoodQ.steps st H
      exact H.mono (by omega) (by omega) (fun h => ⟨h,by omega⟩))
    17 0 (by decide) (by decide) [] s hs
  have ec := c.chainsCost_add 0 51 3
  norm_num only [Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub] at ec H ⊢
  exact H.mono (by omega) (by omega) (fun h => ⟨h,by omega⟩)
theorem top_good (c : NCtx) (hc : c.ok) {s0 : MachineState} {v : Digest} {ds : List Nat}
    (hk : ∀ p ∈ c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0)
    (he : Encoded v s0) (hf : c.Fit v) (hv : decode 0 v=some ds)
    (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ acc t,c.TopOut s0 acc t → Verify.GoodQ t N C Q A (K acc))
    (s : MachineState) (hs : c.ChainIn s0 0 [] s) :
    Verify.GoodQ s (N+2320) (C+1066) Q (A+1066) (Verify.ccM c.topP K) := by
  have hd := decode_facts hv
  have H := c.top_good_exact hc hk h0 he hf hd.1 hd.2.1 K N C A Q hK s hs
  have e : c.chainsCost 0 54=totalCost (coreDigit 0 v) := by
    unfold chainsCost totalCost
    rw [← List.range_eq_range']
    congr 1
    apply List.map_congr_left
    intro i hi
    rw [hf i (List.mem_range.mp hi)]
  have hb := source_accepted_total hv
  rw [e] at H
  exact H.mono (le_refl _) (by omega) (fun h => ⟨h,by omega⟩)
theorem top_good_k (c : NCtx) (hc : c.ok) {s0 : MachineState} {v : Digest} {ds : List Nat}
    (hk : ∀ p ∈ c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0)
    (he : Encoded v s0) (hf : c.Fit v) (hv : decode 0 v=some ds) (k : Nat) (hkc : k ≤ T3.topCredit v)
    (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ acc t,c.TopOut s0 acc t → Verify.GoodQ t N C Q A (K acc))
    (s : MachineState) (hs : c.ChainIn s0 0 [] s) :
    Verify.GoodQ s (N+2320) (C+1066) Q (A+(1066-k)) (Verify.ccM c.topP K) := by
  have hd := decode_facts hv
  have H := c.top_good_exact hc hk h0 he hf hd.1 hd.2.1 K N C A Q hK s hs
  have e : c.chainsCost 0 54=totalCost (coreDigit 0 v) := by
    unfold chainsCost totalCost
    rw [← List.range_eq_range']
    congr 1
    apply List.map_congr_left
    intro i hi
    rw [hf i (List.mem_range.mp hi)]
  have hb := source_accepted_total_credit hv
  rw [e] at H
  exact H.mono (le_refl _) (by omega) (fun h => ⟨h,by omega⟩)
#print axioms top_good
end SigGolfCandidate.T3M.Nonbinary.NCtx
end
section
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest route)
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
def topChainRegs : List Reg := [.x10,.x12,.x25,.x3,.x14,.x15]
def topChainWrites (A : Nat) : Prop := (512 ≤ A ∧ A < 1488) ∨ (12104 ≤ A ∧ A < 15576)
theorem topLeafReady_of (w : WBytes) (pk : Digest) (index c : Nat) (t s0 s : MachineState)
    (a : BitVec 256) (ends : List Digest) (ht : EncPre w pk index 0 c t)
    (he : TopEntry (writeHash t a) (a.extractLsb' 0 128) (trPc 0 c) s0)
    (hp : ∃ dB dC, dB < 4 ∧ dC < 4 ∧ s.pc = pcOf (Nonbinary.pcX 17 dB dC))
    (hr : RegsExcept s0 s topChainRegs) (hf : Frame s0 s topChainWrites) (h15 : s.getReg .x15 = 712704#64)
    (hlen : ends.length = 54) (hend : ∀j<54, DigAt s (slotT j) (ends.getD j 0)) :
    TopLeafReady w pk index c ends s := by
  have hk : KnownOK (leafK 0) s := by
    intro p hp
    simp [leafK,baseK] at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals try exact h15
    all_goals rw [hr.get (by simp [topChainRegs]), he.regs.get (by simp [topEntryRegs]),writeHash_getReg]
    all_goals exact ht.glob.1 _ (by simp [BC.bK, bK,layK,baseK,hw])
  obtain ⟨d, h12, hd⟩ := ht.dst0 rfl
  have hg := Glob_writeHash ht.glob a d h12 (by rcases hd with rfl | rfl <;> decide)
  have hfr : Frame (writeHash t a) s topChainWrites :=
    (he.frame.trans hf).mono (by intro A h; simpa using h)
  have hglob : Glob (leafK 0) w pk s := glob_frame hg hfr (by
    intro A h
    unfold topChainWrites at h
    rcases h with h | h <;> omega) hk
  refine ⟨hp,hglob,?_,?_,?_,?_,hlen,hend,?_⟩
  · intro p hp
    simp [lfKeepK] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rw [hr.get (by simp [topChainRegs])]
    all_goals try exact he.s3
    all_goals rw [he.regs.get (by simp [topEntryRegs]),writeHash_getReg]
    all_goals exact ht.glob.1 _ (by simp [BC.bK, bK,layK,baseK,lfT3,t3In])
  · rw [hr.get (by simp [topChainRegs]),he.regs.get (by simp [topEntryRegs]),writeHash_getReg]
    simpa [dispatchHeap, s7Bias, hL] using ht.s7 0 rfl
  · trivial
  · rw [hr.get (by simp [topChainRegs]),he.regs.get (by simp [topEntryRegs]),writeHash_getReg]
    exact ht.tp 0 rfl
  · have ho := topEntry_orig w pk index c t s0 a ht he
    apply (ho.mono (fun o h => ⟨h.1, by norm_num [layerBase,T3.height,layerEnd] at *;omega⟩)).frame
    intro j hj hp
    exact hf.get (by unfold WIT WX at *;omega) (by
      norm_num [layerBase,T3.height] at hp
      unfold topChainWrites WIT
      omega)
end SigGolfCandidate.T3M
end
section
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest route coreDigit dataDigits maxDigit)
open Nonbinary (NCtx)
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
theorem nctx_block (w : WBytes) (index : Nat) (v : Digest) (p i : Nat) :
    (nctxOf w index v p).blk i - 0x800 = chainBlock 0 i := by
  change 13768 - 1664 + 64 * (53 - i) - 2048 = 9288 + 64 * 12 + 64 * (54 - 1 - i)
  omega
theorem nctx_chain_eq (w : WBytes) (index : Nat) (v : Digest) (p i : Nat) (hi : i < 54) :
    let c := nctxOf w index v p
    chainP 0 c.tree c.leaf i (c.dig i) (NCtx.topMax i - c.dig i) (c.pad0 i) (c.pad1 i) (c.padHeader i) (c.val i) =
      chainP 0 (route index 0).2 (route index 0).1 i ((dataDigits 0 v).getD i 0)
        (maxDigit 0 i - (dataDigits 0 v).getD i 0) (wchainPads w 0 i).1 (wchainPads w 0 i).2 (wchainHeaderPad w 0 i) (wvalue w 0 i) := by
  have hm : NCtx.topMax i = maxDigit 0 i := by
    simp [NCtx.topMax, Nonbinary.mx, maxDigit, show (i / 3 < 17) ↔ i < 51 by omega]
  dsimp only
  rw [T3.dataDigits_getD 0 v i hi, hm]
  unfold NCtx.pad0 NCtx.pad1 NCtx.padHeader NCtx.val
  rw [nctx_block]
  rfl
theorem nctx_mapM_eq (w : WBytes) (index : Nat) (v : Digest) (p : Nat) :
    let c := nctxOf w index v p
    (List.finRange 54).mapM (fun i => chainP 0 c.tree c.leaf i.val (c.dig i.val)
      (NCtx.topMax i.val - c.dig i.val) (c.pad0 i.val) (c.pad1 i.val) (c.padHeader i.val) (c.val i.val)) =
    chainsP w 0 (route index 0).2 (route index 0).1 (dataDigits 0 v) := by
  unfold chainsP
  apply congrArg (fun f => (List.finRange 54).mapM f)
  funext i
  exact nctx_chain_eq w index v p i.val i.isLt
end SigGolfCandidate.T3M
end
section
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64 shortHash leafHash)
open Nonbinary (NCtx)
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
theorem nctx_topP_eq (w : WBytes) (index : Nat) (v : Digest) (p : Nat) :
    (nctxOf w index v p).topP = chainsP w 0 (route index 0).2 (route index 0).1 (dataDigits 0 v) := by
  unfold NCtx.topP NCtx.chainF
  rw [foldlM_app_mapM]
  simp only [List.nil_append, id_map']
  rw [← List.range_eq_range', ← finRange_mapM]
  exact nctx_mapM_eq w index v p
theorem nctx_initial (w : WBytes) (index : Nat) (v : Digest) (p : Nat) (u s : MachineState)
    (he : TopEntry u v p s) (hvalid : T3.topRanksValid v = true) :
    (nctxOf w index v p).ChainIn s 0 [] s := by
  let c := nctxOf w index v p
  have hf : c.Fit v := fun i hi => rfl
  refine ⟨⟨fun r hr => rfl, Frame.refl s _, by simp⟩,rfl,?_⟩
  rw [he.pc]
  change pcOf (176744 + 256 * (v.toNat % 128)) = pcOf (c.startPc 0)
  rw [NCtx.startPc, if_pos (by decide), c.fit_rank hf hvalid 0 (by decide)]
  simp [Nonbinary.entW,Search.topRank]
theorem nctx_encoded (u s : MachineState) (v : Digest) (p : Nat) (he : TopEntry u v p s)
    (hv : v.toNat < 2 ^ 125) : NCtx.Encoded v s := by
  refine ⟨he.lo,?_,?_,he.mask,he.table⟩
  · rw [he.hi]
    exact Search.topWindow_cross v
  · rw [he.tail,Search.topWindow_tail v hv]
theorem top_chain_frame (c : NCtx) (hc : c.S3 = 13768) {s t : MachineState}
    (hf : Frame s t (c.Wr 54)) : Frame s t topChainWrites := by
  apply hf.mono
  intro A _ hA
  simpa only [NCtx.Wr, NCtx.blk, hc, topChainWrites] using hA
open SphincsSecurity (bytesLE bytesLE_length) in
theorem topEncQ_of (a : Digest) (tr p ix : Nat) (rest : List UInt8)
    (hl : (bytesLE 16 a ++ bytesLE 16 (T3.header 4 0 tr p ix) ++ rest).length ≤ 64) :
    TopEncQ (toQ (pad64 (bytesLE 16 a ++ bytesLE 16 (T3.header 4 0 tr p ix) ++ rest))) := by
  unfold TopEncQ
  refine ⟨pad64 (bytesLE 16 a ++ bytesLE 16 (T3.header 4 0 tr p ix) ++ rest), ?_, rfl, ⟨tr, p, ix, ?_⟩⟩
  · simp only [pad64, List.length_append, List.length_replicate, bytesLE_length] at hl ⊢
    omega
  · unfold pad64
    rw [List.append_assoc, List.append_assoc, List.drop_left' (bytesLE_length 16 a),
      List.take_left' (bytesLE_length 16 _)]
open SphincsSecurity (bytesLE bytesLE_length) in
theorem topEncQ_layer (tree leaf : Nat) (M : ClaudeWCT.WCT9.LayerMsg) (c : BitVec 32) (pad : BitVec 96) :
    TopEncQ (toQ (pad64 (ClaudeWCT.W9.T3M.layerEncodingInputP 0 tree leaf M c pad))) := by
  cases M with
  | forest root =>
    exact topEncQ_of root tree 0 leaf _ (by simp only [List.length_append, bytesLE_length]; omega)
  | pair left right =>
    change TopEncQ (toQ (pad64 (bytesLE 16 left ++ bytesLE 16 (T3.header 4 (0 : Layer).val tree 0 leaf) ++
      bytesLE 4 c ++ bytesLE 12 pad ++ bytesLE 16 right)))
    simp only [List.append_assoc]
    rw [← List.append_assoc (bytesLE 16 left)]
    exact topEncQ_of left tree 0 leaf _ (by simp only [List.length_append, bytesLE_length]; omega)
theorem layer_good_top (w : WBytes) (pk : Digest) (index : Nat) (M : ClaudeWCT.WCT9.LayerMsg)
    (s : MachineState) (hs : LayerIn w pk index 0 M s) {β : Type} (R : List Digest → T3.M (Option β))
    (K : Option β → OracleComp HashSpec Obs) (hK0 : K none = pure (false, 0)) (N C A : Nat) (Q : Prop)
    (hR : ∀ ends u, LeafOut w pk index 0 ends u → GoodQ u N C Q A (ccM (R ends) K)) :
    GoodQ s (N + layerFuel 0) (C + layerCost 0 0) Q (A + (layerCost 0 0 - 9)) (ccM (layerHead w index 0 M R) K) := by
  have hidx := hs.idx
  have hA := BC.encoding_setup w pk index 0 M s hs
  have hfuel : layerFuel 0 = 9 + 1 + 120 + 2320 + 12 := by decide
  have hcost : layerCost 0 0 = 9 + 8 + 64 + 12 + 1066 := by decide
  have hsA : stepsA (0 : Layer).val = 9 := rfl
  unfold layerHead
  by_cases hctr : (ClaudeWCT.W9.T3M.wbcCtr w 0).toNat ≥ counterLimit
  · rw [if_pos hctr, ccM_pure, hK0]
    obtain ⟨u, hst, hf, h5, h10⟩ := hA.1 hctr
    change Steps image s 12 12 u at hst
    exact GoodQ.steps' hst (GoodQ.reject (Q := Q) (A := 0) hf h5 h10) (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
  · rw [if_neg hctr]
    obtain ⟨t, hst, hf, h5, hv, hin, c, hc, hpre⟩ := hA.2 (by omega)
    rw [hsA] at hst
    have hblk := BC.encoding_blocks w 0 (route index 0).2 (route index 0).1 M
    have hq := topEncQ_layer (route index 0).2 (route index 0).1 M (ClaudeWCT.W9.T3M.wbcCtr w 0)
      (ClaudeWCT.W9.T3M.wbcPad w 0)
    have H : ∀ a : BitVec 256, GoodQP (fun hash => hash (toQ (pad64 (ClaudeWCT.W9.T3M.layerEncodingInputP 0
        (route index 0).2 (route index 0).1 M (ClaudeWCT.W9.T3M.wbcCtr w 0) (ClaudeWCT.W9.T3M.wbcPad w 0)))) = a ∧
          HashOk hash) (writeHash t a) (N + 12 + 2320 + 120) (C + 12 + 1066 + 64) Q (A + 12 + 1057 + 64)
        (ccM (match decode 0 (a.extractLsb' 0 128) with
          | none => pure none
          | some digits => chainsP w 0 (route index 0).2 (route index 0).1 digits >>= R) K) := by
      intro a
      cases hds : decode 0 (a.extractLsb' 0 128) with
      | none =>
        dsimp only
        rw [ccM_pure,hK0]
        obtain ⟨k,z,st,hk,hz,h5z,h10z⟩ := topTransition_reject w pk index c hc t hpre a hds
        exact (GoodQ.steps' st (GoodQ.reject (Q := Q) (A := 0) hz h5z h10z) (by omega) (by omega)
          (fun hq => ⟨hq,by omega⟩)).toP.pre_mono (fun _ h => h.2)
      | some ds =>
        dsimp only
        have body : ∀ k, k ≤ T3.topCredit (a.extractLsb' 0 128) →
            GoodQ (writeHash t a) (N + 12 + 2320 + 120) (C + 12 + 1066 + 64) Q (A + 12 + (1066 - k) + 64)
              (ccM (chainsP w 0 (route index 0).2 (route index 0).1 ds >>= R) K) := by
          intro k hkc
          have hcan : decode 0 (a.extractLsb' 0 128) = some (Search.topDigits (a.extractLsb' 0 128)) := by
            rw [hds,(decode_top_sum _ _ hds).1]
            rfl
          obtain ⟨s0,st0,he⟩ := topTransition_ok w pk index c hc t hpre a hcan
          let L := nctxOf w index (a.extractLsb' 0 128) (trPc 0 c)
          have hLok : L.ok := nctx_ok w index _ c hidx
          have hkn : KnownOK L.known s0 := nctx_known w pk index c t s0 a hidx hpre he
          obtain ⟨d, h12, hd⟩ := hpre.dst0 rfl
          have hDs0 : DataOK s0 := (Glob_writeHash hpre.glob a d h12 (by rcases hd with rfl | rfl <;> decide)).2.2.2.2.2.congr
            (fun A _ hA => he.frame.get (by omega) (by simp))
          have hO := nctx_orig w index (a.extractLsb' 0 128) (trPc 0 c) s0
            (topEntry_orig w pk index c t s0 a hpre he) hDs0
          have hfit : L.Fit (a.extractLsb' 0 128) := fun i hi => rfl
          have hdec := NCtx.decode_facts hds
          have hIn := nctx_initial w index _ (trPc 0 c) _ s0 he hdec.2.1
          have hEnc := nctx_encoded _ s0 _ (trPc 0 c) he hdec.1
          have hG := L.top_good_k hLok hkn hO hEnc hfit hds k hkc (fun ends => ccM (R ends) K)
            (N+12) (C+12) (A+12) Q (fun ends z hz => by
              obtain ⟨hr,hf,hlen,hend,hpc,h15⟩ := hz
              have hregs : RegsExcept s0 z topChainRegs := by
                intro r hrn
                apply hr r
                · intro hh;exact hrn ((by decide : chainRegs ⊆ topChainRegs) hh)
                · intro hh;subst r;exact hrn (by decide)
              have hframe : Frame s0 z topChainWrites := by
                exact top_chain_frame L rfl hf
              have hready := topLeafReady_of w pk index c t s0 z a ends hpre he hpc hregs hframe h15 hlen
                (fun j hj => by have h := hend j (by omega);exact h)
              obtain ⟨u,st,hu⟩ := leafT_step w pk index c hc hidx ends z hready
              exact GoodQ.steps' st (hR ends u hu) (by omega) (by omega) (fun hq => ⟨hq,by omega⟩)) s0 hIn
          have e : chainsP w 0 (route index 0).2 (route index 0).1 ds = L.topP := by
            rw [(decode_top_sum _ _ hds).1]
            exact (nctx_topP_eq w index _ (trPc 0 c)).symm
          rw [ccM_bind,e]
          exact GoodQ.steps' st0 hG (by omega) (by omega) (fun hq => ⟨hq,by omega⟩)
        by_cases hcr : 9 ≤ T3.topCredit (a.extractLsb' 0 128)
        · exact (body 9 hcr).toP.pre_mono (fun _ h => h.2)
        · refine GoodQP.of_false (body 0 (Nat.zero_le _)) ?_
          rintro hash ⟨hea, hok⟩
          have := hok _ hq ds (by rw [hea]; exact hds)
          rw [hea] at this
          exact hcr this
    have := GoodQP.shortHash_bind_pre (f := fun answer => match decode 0 answer with
      | none => pure none
      | some digits => chainsP w 0 (route index 0).2 (route index 0).1 digits >>= R) hf h5 hv hin H
    rw [hblk] at this
    exact (GoodQP.steps' hst this (by omega) (by omega) (by omega)).toGoodQ
end SigGolfCandidate.T3M
end
section
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64 shortHash leafHash)
theorem layer_good (w : WBytes) (pk : Digest) (index : Nat) (lay : Layer) (M : ClaudeWCT.WCT9.LayerMsg)
    (s : MachineState) (hs : LayerIn w pk index lay.val M s) {β : Type} (R : List Digest → T3.M (Option β))
    (K : Option β → OracleComp HashSpec Obs) (hK0 : K none = pure (false, 0)) (N C A : Nat) (Q : Prop)
    (hR : ∀ ends u, LeafOut w pk index lay ends u → GoodQ u N C Q A (ccM (R ends) K)) :
    GoodQ s (N + layerFuel lay.val) (C + layerCost lay.val 0) Q (A + layerCostA lay.val)
      (ccM (layerHead w index lay M R) K) := by
  by_cases h0 : lay = 0
  · subst h0
    exact layer_good_top w pk index M s hs R K hK0 N C A Q hR
  · have := layer_good_low w pk index lay h0 M s hs R K hK0 N C A Q hR
    have e : layerCostA lay.val = layerCost lay.val 0 := by
      have hv : lay.val ≠ 0 := fun h => h0 (Fin.ext h)
      unfold layerCostA
      simp [hv]
    rw [e]
    exact this
end SigGolfCandidate.T3M
end
section
set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.T3M
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
theorem cmp_good (pk root : Digest) (t : MachineState) (h : CmpIn pk root t) (Q : Prop) (hQ : Q) :
    GoodQ t 9 8 Q 8 (pure (root == pk, 0)) := by
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
    have hg := GoodQ.halt (Q := Q) (A := 1) (hu.ecall rfl) h5 (fun _ => ⟨hQ, le_refl 1⟩)
    have hb : decide (u.getReg .x10 = 0) = (root == pk) := by
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, beq_iff_eq, heq]
    rw [hb] at hg
    exact GoodQ.steps' hu.steps hg (by simp [cmpAcc]) (by simp [cmpAcc])
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
    exact GoodQ.steps' hu.steps (GoodQ.reject (Q := Q) (A := 0) (hu.ecall rfl) h5 h10)
      (by simp [cmpRej1]) (by simp [cmpRej1]) (fun q => ⟨q, by simp [cmpRej1]⟩)
end SigGolfCandidate.T3M
end
section
set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Digest HashOutput Selection selections)
abbrev selC (a : HashOutput) (c : Nat) : Selection := (selections a).getD c ⟨0, []⟩
end SigGolfCandidate.T3M.Verify
namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest HashOutput Selection selections header)
structure FCtx where
  pk : Digest
  w : WBytes
  a : HashOutput
namespace FCtx
def idx (F : FCtx) : Nat := F.a.toNat % 2 ^ 31
def sel (F : FCtx) (c : Nat) : Selection := selC F.a c
def g (F : FCtx) (s : Nat) : Nat := T3M.selLeaf (F.sel (s / 3)) (s % 3)
theorem idx_lt (F : FCtx) : F.idx < 2 ^ 31 := Nat.mod_lt _ (by decide)
end FCtx
end SigGolfCandidate.T3M.Verify
namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
def layerPc : Nat := 205
end SigGolfCandidate.T3M.Verify
namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest HashOutput Selection selections header)
structure FtsOut (F : FCtx) (root : Digest) (u : MachineState) : Prop where
  glob : Glob baseK F.w F.pk u
  idx : u.getReg .x22 = BitVec.ofNat 64 F.idx
  pc : u.pc = pcOf layerPc
  root : DigAt u 0x100 root
  wit : Orig F.w (fun o => o < 64 ∨ 9288 ≤ o) u
  a2 : u.getReg .x12 = BitVec.ofNat 64 0x100
  s10 : u.getReg .x26 = 6
  heapOne : u.getReg .x7 = 1
  heapTwo : u.getReg .x13 = 2
  heapSeven : u.getReg .x30 = 7
  heapThree : u.getReg .x19 = 3
  heapFour : u.getReg .x20 = 4
  heapFive : u.getReg .x21 = 5
  coordStep : u.getReg .x6 = 0x10000
  topBase : u.getReg .x28 = BitVec.ofNat 64 TOPBASE
  top : ∀ k, k < 5 → u.getMem (BitVec.ofNat 64 (TOPLOAD + 8 * k)) =
    BitVec.ofNat 64 (topWords.getD k 0)
  top8 : u.getMem (BitVec.ofNat 64 (TOPLOAD - 8)) = BitVec.ofNat 64 23304
end SigGolfCandidate.T3M.Verify
namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Digest HashOutput Selection selections)
def afterFts (pk : Digest) (w : WBytes) (index : Nat) (r : Option Digest) : T3.M Bool :=
  match r with
  | some root => do
      let __x ← ClaudeWCT.W9.T3M.layersBC w index 4 (.forest root)
      match __x with
      | some root => pure (root == pk)
      | _ => pure false
  | _ => pure false
end SigGolfCandidate.T3M.Verify
namespace SigGolfCandidate.T3M
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
def RestIn (w : WBytes) (pk : Digest) (index n : Nat) (msg : LayerMsg) (s : MachineState) : Prop :=
  if n = 0 then match msg with
    | .forest root => CmpIn pk root s
    | .pair _ _ => False
  else LayerIn w pk index (n - 1) msg s
theorem mkEnd_top (w : WBytes) (pk : Digest) (index : Nat) (u : MachineState) (root : Digest)
    (t : MachineState) (ht : MkEnd w pk 0 (route index 0).1 u root t) : CmpIn pk root t := by
  have hpc : t.pc = pcOf (7202 + 128 * mkSh 0 1 (route index 0).1) := by
    rw [ht.pc]
    congr 1
    simp [mkFin, show mkNch 0 - 1 = 1 from rfl, show mkBits 0 1 = 6 from rfl,
      show mkOff 0 1 6 = 33 from rfl, BC.mkShp, mkShp]
    omega
  refine ⟨⟨mkSh 0 1 (route index 0).1, mkSh_lt _ _ _, ?_, ?_, ?_⟩, ht.glob.2.2.1⟩
  · rw [hpc]; rfl
  · intro p hp
    simp only [cmpK, List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact ht.glob.1 p hp
    · rw [ht.dstReg]
      congr 1
      exact (mkDst_chunk _).symm
  · change DigAt t (11336 + 48 * (mkSh 0 1 (route index 0).1 / 32 % 2)) root
    rw [mkDst_chunk]
    exact ht.root
theorem mkStop_next (w : WBytes) (pk : Digest) (index : Nat) (hidx : index < 2 ^ 31)
    (lay : Layer) (ends : List Digest) (u : MachineState) (hu : LeafOut w pk index lay ends u)
    (v : Digest) (t : MachineState) (ht : MkStop w pk lay.val (route index lay).1 u v t) :
    RestIn w pk index lay.val (mkMessage w index lay v) t := by
  by_cases h0 : lay.val = 0
  · have hz : lay = 0 := Fin.ext h0
    subst lay
    exact mkEnd_top w pk index u v t ht
  · simpa [RestIn, h0] using mkStop_next_lower w pk index hidx lay h0 ends u hu v t ht
def lCyc : Nat → Nat
  | 0 => 8
  | n + 1 => layerCost n 0 + mkCyc n + lCyc n
def lCycA : Nat → Nat
  | 0 => 8
  | n + 1 => layerCostA n + mkCyc n + lCycA n
def lFuel : Nat → Nat
  | 0 => 9
  | n + 1 => layerFuel n + mkFuel n + lFuel n
theorem lCyc_4 : lCyc 4 = 5604 := by decide
theorem lCycA_4 : lCycA 4 = 5595 := by decide
theorem lCycA_le (n : Nat) : lCycA n ≤ lCyc n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => simp only [lCycA, lCyc, layerCostA]; split_ifs <;> omega
theorem lFuel_4 : lFuel 4 = 7957 := by decide
theorem layers_good (w : WBytes) (pk : Digest) (index : Nat) (hidx : index < 2 ^ 31) (Q : Prop) (hQ : Q) :
    ∀ n, n ≤ 4 → ∀ msg s, RestIn w pk index n msg s →
      GoodQ s (lFuel n) (lCyc n) Q (lCycA n) (ccM (BC.layerLoop w index n msg) (kFin pk)) := by
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
    have hv : (Fin.ofNat 4 n : Layer).val = n := by simp [Fin.val_ofNat, Nat.mod_eq_of_lt (show n < 4 by omega)]
    rw [layerLoop_succ w index n (by omega) msg]
    have hg := layer_good w pk index (Fin.ofNat 4 n) msg s (by rwa [hv])
      (fun ends => leafHash (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 ends >>=
        fun v => merkleMsg w index (Fin.ofNat 4 n) v >>= BC.layerLoop w index n)
      (kFin pk) (kFin_none pk) (lFuel n + mkFuel n) (lCyc n + mkCyc n) (lCycA n + mkCyc n) Q
      (fun ends u hu => by
        have hm := merkle_good w pk index (Fin.ofNat 4 n) ends u hidx hu
          (fun v => ccM (BC.layerLoop w index n (mkMessage w index (Fin.ofNat 4 n) v)) (kFin pk))
          (lFuel n) (lCyc n) (lCycA n) Q
          (fun v t ht => ih (by omega) _ t (by
            have h := mkStop_next w pk index hidx (Fin.ofNat 4 n) ends u hu v t ht
            rw [hv] at h
            exact h))
        simp only [ccM_bind, merkleMsg, ccM_pure, hv] at hm ⊢
        exact hm)
    rw [hv] at hg
    exact hg.mono (by simp only [lFuel]; omega) (by simp only [lCyc]; omega) (fun q => ⟨q, by simp only [lCycA]; omega⟩)
theorem after_good (pk : Digest) (w : WBytes) (Q : Prop) (hQ : Q) (a : HashOutput) (root : Digest) (u : MachineState)
    (h : FtsOut ⟨pk, w, a⟩ root u) :
    GoodQ u 8050 8050 Q 5600 (ccM (afterFts pk w (a.toNat % 2 ^ 31) (some root)) Kb) := by
  have hidx : a.toNat % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by decide)
  obtain ⟨t, hst, hL3⟩ := layerIn_of_fts w pk _ root u hidx h.glob h.idx h.pc h.root h.wit h.a2 h.s10 h.heapOne h.heapTwo h.heapSeven h.heapThree h.heapFour h.heapFive h.coordStep h.topBase h.top h.top8
  have hg := layers_good w pk _ hidx Q hQ 4 le_rfl (.forest root) t (by simpa [RestIn] using hL3)
  have e : ccM (afterFts pk w (a.toNat % 2 ^ 31) (some root)) Kb =
      ccM (BC.layerLoop w (a.toNat % 2 ^ 31) 4 (.forest root)) (kFin pk) := by
    unfold afterFts
    rw [ccM_bind]
    rfl
  rw [e]
  rw [lFuel_4, lCyc_4, lCycA_4] at hg
  exact GoodQ.steps' hst hg (by omega) (by omega) (fun q => ⟨q, by omega⟩)
end SigGolfCandidate.T3M
end
end

section




namespace W9Drv
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open W9Machine
def dispatchPc (n : Nat) : Nat := [47,62,79,96,113,130,147,164,180,197].getD n 197
def cachedWord (n : Nat) : Nat := [0,0,1,1,1,2,2,2,2,2].getD n 2
structure CoordPre (pk : Digest) (w : WBytes) (a : HashOutput) (n : Nat)
    (pairs : List (Digest × Digest)) (u : MachineState) : Prop where
  le : n ≤ 9
  length : pairs.length = n
  pc : u.pc = pcOf (dispatchPc n)
  glob : Glob baseK w pk u
  digest : DigestAt a u
  bank : HeaderBank u
  index : u.getReg .x22 = BitVec.ofNat 64 (idxOf a)
  heaps : ∀ h, 2 ≤ h → h ≤ 7 → u.getReg (Child.heapReg h) = BitVec.ofNat 64 h
  stepOne : u.getReg .x7 = 1
  stepTwo : u.getReg .x13 = 2
  hashLen : u.getReg .x11 = 64
  coordStep : u.getReg .x6 = 65536
  prefixReg : u.getReg .x15 = BitVec.ofNat 64 (idxOf a * 2^27 + 65536 * (n-1))
  cached3 : u.getReg .x17 = a.extractLsb' 192 64
  cached : u.getReg .x16 = a.extractLsb' (64 * cachedWord n) 64
  nodeReg : n ≠ 0 → u.getReg .x27 = BitVec.ofNat 64 (V3.nodeLow (n-1) (idxOf a))
  nodeZero : n = 0 → u.getReg .x27 = BitVec.ofNat 64 (1 + 3 * 256 + 4 * 65536)
  zero : u.getMem (BitVec.ofNat 64 1024) = 0 ∧ u.getMem (BitVec.ofNat 64 1032) = 0
  mask : u.getReg .x2 = BitVec.ofNat 64 0xfffc
  jt : u.getReg .x24 = BitVec.ofNat 64 0xd6800
  childBlock : u.getReg .x29 = BitVec.ofNat 64 0xce800
  baseReg : u.getReg .x8 = BitVec.ofNat 64 (2112 + 1024 * (n-1))
  headerZero : n = 0 → u.getReg .x28 = BitVec.ofNat 64 (idxOf a * 2^32)
  headerReg : n ≠ 0 → u.getReg .x28 = BitVec.ofNat 64 (1537 + 65536 * (n-1))
  pairs : ∀ i, i < n → DigAt u (1056 + 32*i) (pairs.getD i (0,0)).1 ∧
    DigAt u (1056 + 32*i + 16) (pairs.getD i (0,0)).2
  coords : ∀ k : Fin 9, n ≤ k.val → ∀ off, off < 1024 → off % 8 = 0 →
    OrigW w u (coordinateBase k + off)
  layer : Orig w (fun o => o < 64 ∨ 9288 ≤ o) u
end W9Drv
end

section



section
namespace W9Drv
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
open W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def gJumpWords : List (BitVec 32) := [0xc0006f]
def gCheckWords : List (BitVec 32) :=
  [0x2181b13,0x7803883,0x2d8d193,0x1011b393,0x2039863]
def gSetupWords : List (BitVec 32) :=
  [0x21b5b13,0x1bb1793,0x10337,0x200693,0x300993,0x400a13,0x500a93,0x600d13,0x700f13,0x20b1e13,0x84190413,0x21813d83,0x22013e83,0x22813c03,0xffc30113]
def gRejectWords : List (BitVec 32) := [1049235,1049875,115]
def gateE : E := .bin .sltu
  (.bin .srl (.ld (.c (BitVec.ofNat 64 120)))
    (.c (BitVec.ofNat 64 45))) (.c (BitVec.ofNat 64 257))
def idxE : E := .bin .srl (.reg .x22) (.c (BitVec.ofNat 64 33))
def gJump : Result := ⟨SymState.init, .c (pcOf 24), .jump, 1, 1⟩
def gCheck : Result :=
  ⟨⟨(((RegFile.init.set .x3
    (.bin .srl (.ld (.c (BitVec.ofNat 64 120))) (.c 45))).set .x7 gateE).set
    .x17 (.ld (.c (BitVec.ofNat 64 120)))).set
    .x22 (.bin .sll (.reg .x16) (.c (BitVec.ofNat 64 33))), [], []⟩,
    .ite .ne gateE (.c 0) (.c (pcOf 32)) (.c (pcOf 21)), .branch, 5, 5⟩
def gSetup : Result :=
  ⟨⟨(((((((((((((((RegFile.init).set .x2 (.c (BitVec.ofNat 64 0xfffc))).set .x6 (.c 65536)).set .x8 (.bin .add (.reg .x18) (.c (BitVec.ofNat 64 (2 ^ 64 - 1983))))).set .x13 (.c 2)).set .x15 (.bin .sll idxE (.c 27))).set .x19 (.c 3)).set .x20 (.c 4)).set .x21 (.c 5)).set .x22 (idxE)).set .x24 (.ld (addC (.reg .x2) 552))).set .x26 (.c 6)).set .x27 (.ld (addC (.reg .x2) 536))).set .x28 (.bin .sll idxE (.c 32))).set .x29 (.ld (addC (.reg .x2) 544))).set .x30 (.c 7), [],
    [.valid ⟨some (.reg .x2), 552⟩ 8, .valid ⟨some (.reg .x2), 544⟩ 8, .valid ⟨some (.reg .x2), 536⟩ 8]⟩,
    .c (pcOf 47), .fuel, 15, 15⟩
def gReject : Result :=
  ⟨⟨(RegFile.init.set .x5 (.c 1)).set .x10 (.c 1), [], []⟩, .c (pcOf 26), .ecall, 2, 2⟩
theorem gJump_checked : rOK (symRun {} gJumpWords (pcOf 21) 1) gJump = true := by decide +kernel
theorem gJump_linked : sliceChecked 21 gJumpWords = true := by decide +kernel
theorem gCheck_checked : rOK (symRun {} gCheckWords (pcOf 16) 5) gCheck = true := by decide +kernel
theorem gCheck_linked : sliceChecked 16 gCheckWords = true := by decide +kernel
theorem gSetup_checked : rOK (symRun {} gSetupWords (pcOf 32) 15) gSetup = true := by decide +kernel
theorem gSetup_linked : sliceChecked 32 gSetupWords = true := by decide +kernel
theorem gReject_checked : rOK (symRun {} gRejectWords (pcOf 24) 3) gReject = true := by decide +kernel
theorem gReject_linked : sliceChecked 24 gRejectWords = true := by decide +kernel
end W9Drv
end
section
namespace W9Drv
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput M)
open W9Machine
theorem block_steps {words : List (BitVec 32)} {p n : Nat} {r : Result}
    (hc : rOK (symRun {} words (pcOf p) n) r = true) (hl : sliceChecked p words = true)
    (hob : r.st.obl = []) (s : MachineState) (hpc : s.pc = pcOf p) :
    Steps Frozen.image s r.steps r.cycles (r.toState s) :=
  symRun_sound (rOK_eq hc) (slice_at p words hl) s hpc (by simp [Result.obligs, hob, Oblig.all])
theorem block_ecall {words : List (BitVec 32)} {p n : Nat} {r : Result}
    (hc : rOK (symRun {} words (pcOf p) n) r = true) (hl : sliceChecked p words = true)
    (hob : r.st.obl = []) (s : MachineState) (hstop : r.stop = .ecall) :
    fetch Frozen.image (r.toState s) = some (.base .ECALL) :=
  symRun_ecall (rOK_eq hc) (slice_at p words hl) s (by simp [Result.obligs, hob, Oblig.all]) hstop
theorem toState_mem_nil (r : Result) (s : MachineState) (h : r.st.mem = []) :
    (r.toState s).mem = s.mem := by
  show memEval s r.st.mem = s.mem
  rw [h]; rfl
theorem init_getReg (s : MachineState) (x : Reg) : (RegFile.init.get x).eval s = s.getReg x := by
  cases x <;> rfl
theorem glob_congr {w : WBytes} {pk : Digest} {s t : MachineState} (h : Glob baseK w pk s)
    (hm : t.mem = s.mem) (h5 : t.getReg .x5 = 0) (h18 : t.getReg .x18 = 0xFFF) :
    Glob baseK w pk t := by
  obtain ⟨-, h0, h2, h3, h4, h5'⟩ := h
  have e : ∀ A, t.getMem A = s.getMem A := fun A => congrFun hm A
  refine ⟨?_, fun j hj => (e _).trans (h0 j hj), ⟨(e _).trans h2.1, (e _).trans h2.2⟩,
    fun a ha => (e _).trans (h3 a ha), ?_, h5'.congr (fun A _ _ => e _)⟩
  · intro p hp
    simp only [baseK, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact h5
    · exact h18
  · show (t.getMem _).toNat / 2 ^ 32 = 0
    rw [e]; exact h4
theorem digest_gate_val (a : BitVec 256) :
    (a.extractLsb' 192 64 >>> 45).toNat = (a.toNat / 2 ^ 234 % 2 ^ 22) / 8 := by
  rw [BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  omega
theorem idx_val (x : Word) :
    (x <<< 33) >>> 33 = BitVec.ofNat 64 (x.toNat % 2 ^ 31) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq, BitVec.toNat_ofNat]
  have := x.isLt
  omega
theorem heap_val (i h : Nat) (hi : i < 2 ^ 31) :
    BitVec.ofNat 64 (2 ^ 32 * h) ||| BitVec.ofNat 64 i = BitVec.ofNat 64 (i + 2 ^ 32 * h) := by
  rw [ofNat_or_disjoint i (2 ^ 32 * h) 32 (by omega) (by simp), Nat.add_comm]
theorem idxE_eval (s : MachineState) :
    idxE.eval s = s.getReg .x22 >>> 33 := rfl
theorem gateE_eval (s : MachineState) (a : BitVec 256)
    (hw : s.getMem (BitVec.ofNat 64 120) = a.extractLsb' 192 64) :
    gateE.eval s = if decide (a.toNat / 2 ^ 234 % 2 ^ 22 < 2056) then 1 else 0 := by
  change (if BitVec.ult (s.getMem (BitVec.ofNat 64 120) >>> 45)
    (BitVec.ofNat 64 257) then (1 : BitVec 64) else 0) = _
  rw [hw]
  simp only [BitVec.ult, digest_gate_val, BitVec.toNat_ofNat]
  have he : (a.toNat / 2 ^ 234 % 2 ^ 22) / 8 < 257 ↔
      a.toNat / 2 ^ 234 % 2 ^ 22 < 2056 := by omega
  simp only [he]
theorem word0_toNat (a : HashOutput) : (a.extractLsb' 0 64).toNat = a.toNat % 2 ^ 64 := by
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
theorem index_eq (a : HashOutput) : (a.extractLsb' 0 64).toNat % 2 ^ 31 = idxOf a := by
  rw [word0_toNat]; unfold idxOf; omega
theorem gate_good (pk : Digest) (w : WBytes) (a : HashOutput)
    (u : MachineState) (N C A : Nat) (Q : Prop)
    (K : Bool → OracleComp HashSpec Obs)
    (hu : GatePre pk w a u) (hnone : K false = pure (false, 0))
    (hnext : ∀ t, CoordPre pk w a 0 [] t →
      GoodQFor Frozen.image t N C Q A (K true)) :
    GoodQFor Frozen.image u (N + 20) (C + 20) Q (A + 20) (K (ClaudeWCT.W9.T3M.gateOk a)) := by
  let s1 := u
  have m1 : s1.mem = u.mem := rfl
  have r1 : ∀ x, s1.getReg x = u.getReg x := fun _ => rfl
  have pc1 : s1.pc = pcOf 16 := hu.pc
  have st2 := block_steps gCheck_checked gCheck_linked rfl s1 pc1
  set s2 := gCheck.toState s1 with hs2
  have m2 : s2.mem = u.mem := (toState_mem_nil _ _ rfl).trans m1
  have hw3 : s1.getMem (BitVec.ofNat 64 120) = a.extractLsb' 192 64 := by
    have := hu.digest 3 (by decide)
    simpa [MachineState.getMem, m1] using this
  have pc2 : s2.pc = if gateE.eval s1 != 0 then pcOf 32 else pcOf 21 := by
    show (E.ite .ne gateE (.c 0) (.c (pcOf 32)) (.c (pcOf 21))).eval s1 = _
    rfl
  have hg : gateE.eval s1 = if ClaudeWCT.W9.T3M.gateOk a then 1 else 0 :=
    gateE_eval s1 a hw3
  have st2' : Steps Frozen.image s1 5 5 s2 := st2
  by_cases hok : ClaudeWCT.W9.T3M.gateOk a = true
  ·
    rw [hok]
    have hz : gateE.eval s1 = 1 := by simpa [hok] using hg
    have pc2' : s2.pc = pcOf 32 := by rw [pc2, hz]; rfl
    have hsp2 : s2.getReg .x2 = BitVec.ofNat 64 0xffbd30 := by
      rw [hs2, Result.toState_getReg]
      show s1.getReg .x2 = _
      rw [r1]; exact hu.sp
    have hob : gSetup.obligs s2 := by
      apply (Oblig.all_iff s2 _).mpr
      intro o ho
      simp only [gSetup, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl
      all_goals
        change accessValid (s2.getReg .x2 + _) 8 = true
        rw [hsp2]
        decide +kernel
    have st3 := symRun_sound (rOK_eq gSetup_checked) (slice_at _ _ gSetup_linked) s2 pc2' hob
    set s3 := gSetup.toState s2 with hs3
    have st3' : Steps Frozen.image s2 15 15 s3 := st3
    have m2' : ∀ A, s2.getMem A = u.getMem A := fun A => congrFun m2 A
    have hchild : s3.getReg .x29 = BitVec.ofNat 64 0xce800 := by
      rw [hs3, Result.toState_getReg]
      change s2.getMem ((addC (.reg .x2) 544).eval s2) = _
      rw [addC_eval]
      change s2.getMem (s2.getReg .x2 + 544) = _
      rw [hsp2]
      change s2.getMem (BitVec.ofNat 64 (setupMaskAddr + 16)) = _
      rw [m2']
      exact hu.setupMask.child
    have hjt : s3.getReg .x24 = BitVec.ofNat 64 0xd6800 := by
      rw [hs3, Result.toState_getReg]
      change s2.getMem ((addC (.reg .x2) 552).eval s2) = _
      rw [addC_eval]
      change s2.getMem (s2.getReg .x2 + 552) = _
      rw [hsp2]
      change s2.getMem (BitVec.ofNat 64 (setupMaskAddr + 24)) = _
      rw [m2']
      exact hu.setupMask.jt
    have hnode0 : s3.getReg .x27 = BitVec.ofNat 64 (1 + 3 * 256 + 4 * 65536) := by
      rw [hs3, Result.toState_getReg]
      change s2.getMem ((addC (.reg .x2) 536).eval s2) = _
      rw [addC_eval]
      change s2.getMem (s2.getReg .x2 + 536) = _
      rw [hsp2]
      change s2.getMem (BitVec.ofNat 64 (0xffbf40 + 512 * (0 : Fin 9).val + 8)) =
        BitVec.ofNat 64 (1 + 3 * 256 + (4 + (0 : Fin 9).val) * 65536)
      rw [m2']
      exact hu.bank.node
    have m3 : s3.mem = u.mem := (toState_mem_nil _ _ rfl).trans m2
    have e3 : ∀ A, s3.getMem A = u.getMem A := fun A => congrFun m3 A
    have r22 : s2.getReg .x22 = a.extractLsb' 0 64 <<< 33 := by
      rw [hs2, Result.toState_getReg]
      show s1.getReg .x16 <<< 33 = _
      rw [r1, hu.cached0]
    have hidx : idxE.eval s2 = BitVec.ofNat 64 (idxOf a) := by
      rw [idxE_eval, r22, idx_val, index_eq]
    have h18s : s2.getReg .x18 = 0xFFF := by
      rw [hs2, Result.toState_getReg]
      show s1.getReg .x18 = 0xFFF
      rw [r1]; exact hu.glob.1 (.x18, 0xFFF) (by simp [baseK])
    have hia : idxOf a < 2 ^ 31 := Nat.mod_lt _ (by decide)
    have h5 : s3.getReg .x5 = 0 := by
      rw [hs3, Result.toState_getReg]
      show s2.getReg .x5 = 0
      rw [hs2, Result.toState_getReg]
      show s1.getReg .x5 = 0
      rw [r1]; exact hu.glob.1 (.x5, 0) (by simp [baseK])
    have h18 : s3.getReg .x18 = 0xFFF := by
      rw [hs3, Result.toState_getReg]
      show s2.getReg .x18 = 0xFFF
      rw [hs2, Result.toState_getReg]
      show s1.getReg .x18 = 0xFFF
      rw [r1]; exact hu.glob.1 (.x18, 0xFFF) (by simp [baseK])
    have hpre : CoordPre pk w a 0 [] s3 := by
      refine {
        le := (by decide), length := rfl, pc := rfl,
        glob := glob_congr hu.glob m3 h5 h18,
        digest := ?_, bank := ?_, index := ?_, heaps := ?_,
        stepOne := ?_, stepTwo := rfl, hashLen := ?_, coordStep := rfl,
        prefixReg := ?_, cached3 := ?_, cached := ?_, nodeReg := fun h => absurd rfl h,
        nodeZero := fun _ => hnode0,
        zero := ⟨(e3 _).trans hu.zero.1, (e3 _).trans hu.zero.2⟩,
        mask := rfl, jt := hjt, childBlock := hchild, baseReg := ?_, headerZero := ?_, headerReg := fun h => absurd rfl h,
        pairs := fun i hi => absurd hi (Nat.not_lt_zero _), coords := ?_, layer := ?_ }
      · intro k hk; rw [e3]; exact hu.digest k hk
      · exact ⟨(e3 _).trans hu.bank.node, fun k hk => (e3 _).trans (hu.bank.top k hk),
          (e3 _).trans hu.bank.top8⟩
      · rw [hs3, Result.toState_getReg]; exact hidx
      · intro h h2 h7
        interval_cases h <;> rfl
      · rw [hs3, Result.toState_getReg]
        show s2.getReg .x7 = 1
        rw [hs2, Result.toState_getReg]
        exact hz
      · rw [hs3, Result.toState_getReg]
        show s2.getReg .x11 = 64
        rw [hs2, Result.toState_getReg]
        show s1.getReg .x11 = 64
        rw [r1]; exact hu.len64
      · change idxE.eval s2 <<< 27 = _
        rw [hidx]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
        rw [Nat.mod_eq_of_lt (by omega : idxOf a < 2^64)]
        simp
      · rw [hs3, Result.toState_getReg]
        show s2.getReg .x17 = _
        rw [hs2, Result.toState_getReg]
        exact hw3
      · rw [hs3, Result.toState_getReg]
        show s2.getReg .x16 = _
        rw [hs2, Result.toState_getReg]
        show s1.getReg .x16 = _
        rw [r1]; exact hu.cached0
      · rw [hs3, Result.toState_getReg]
        show s2.getReg .x18 + BitVec.ofNat 64 (2 ^ 64 - 1983) = _
        rw [h18s]; rfl
      · intro _
        change idxE.eval s2 <<< 32 = _
        rw [hidx]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
        rw [Nat.mod_eq_of_lt (by omega : idxOf a < 2^64)]
      · intro k _ off hoff h8
        unfold OrigW
        rw [e3]
        have hw := hu.wit ((64 + 1024 * k.val + off) / 8) (by unfold WX; have := k.isLt; omega)
        rw [show WIT + 8 * ((64 + 1024 * k.val + off) / 8) = coordinateBase k + off by
          unfold WIT coordinateBase; omega] at hw
        have e : 8 * (coordinateBase k + off - 0x800) = 64 * ((64 + 1024 * k.val + off) / 8) := by
          unfold coordinateBase; omega
        rw [hw, wword, e]
      · exact (hu.wit.orig _).frame (fun j _ _ => e3 _)
    have := (((hnext s3 hpre).steps st3').steps st2')
    exact this.mono (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
  ·
    have hok' : ClaudeWCT.W9.T3M.gateOk a = false := by simpa using hok
    rw [hok', hnone]
    have hz : gateE.eval s1 = 0 := by simpa [hok'] using hg
    have pc2' : s2.pc = pcOf 21 := by
      rw [pc2, hz]; rfl
    have sj := block_steps gJump_checked gJump_linked rfl s2 pc2'
    let sr := gJump.toState s2
    have sj' : Steps Frozen.image s2 1 1 sr := sj
    have st3 := block_steps gReject_checked gReject_linked rfl sr rfl
    have st3' : Steps Frozen.image sr 2 2 (gReject.toState sr) := st3
    have hf := block_ecall gReject_checked gReject_linked rfl sr rfl
    have hr : GoodQFor Frozen.image (gReject.toState sr) 1 1 Q A (pure (false, 0)) :=
      GoodQFor.reject hf (by rw [Result.toState_getReg]; rfl) (by rw [Result.toState_getReg]; rfl)
    have := ((hr.steps st3').steps sj').steps st2'
    exact this.mono (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
#print axioms gate_good
end W9Drv
end
end

section


namespace W9Drv
open W9Machine SigGolfCandidate.T3M SigGolfCandidate.Rv
set_option maxRecDepth 200000
set_option maxHeartbeats 0
def jtStart : Nat := 218624
def jtReject : Nat := 24
def chainEntries : List Nat := Frozen.chainEntries
def jtTarget (field : Nat) : Nat :=
  if field < 16200 then Frozen.layout.chainWord (N600.embed ⟨field % 600, Nat.mod_lt _ (by decide)⟩)
  else jtReject
def jtCheck (start : Nat) (words : List (BitVec 32)) : Bool :=
  words.zipIdx.all fun wi =>
    rOK (symRun {} [wi.1] (pcOf (jtStart + start + wi.2)) 1)
      ⟨SymState.init, .c (pcOf (jtTarget (start + wi.2))), .jump, 1, 1⟩
end W9Drv
namespace W9Drv
open W9Machine SigGolfCandidate.T3M SigGolfCandidate.Rv
set_option maxRecDepth 200000
set_option maxHeartbeats 0
def jtChunk (c : Fin 64) : List (BitVec 32) :=
  (W9Machine.Frozen.codeFrom (jtStart + 256 * c.val)).take 256
theorem jtChunk_length (c : Fin 64) : (jtChunk c).length = 256 := by
  fin_cases c <;> decide +kernel
theorem jtChunk_checked (c : Fin 64) : jtCheck (256 * c.val) (jtChunk c) = true := by
  fin_cases c <;> decide +kernel
theorem jtChunk_linked (c : Fin 64) : CodeAt Frozen.image (pcOf (jtStart + 256 * c.val)) (jtChunk c) := by
  apply slice_at
  fin_cases c <;> decide +kernel
end W9Drv
end

section







section
set_option autoImplicit false
namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
def coordDispatch (p bit coord : Nat) (advance reload : Bool) : Result :=
  let dig : E := if coord ≥ 7 then .reg .x17 else if reload then .ld (.c (BitVec.ofNat 64 (96 + 8 * (bit / 64)))) else .reg .x16
  let child := mkBin .and (if bit % 64 = 0 then dig else
    mkBin .srl dig (.c (BitVec.ofNat 64 (bit % 64)))) (.c 127)
  let route := mkBin .or (mkBin .sll child (.c 32)) (.reg .x22)
  let pre := if advance then mkAdd (.reg .x15) (.reg .x6) else .reg .x15
  let packed := mkBin .or (mkBin .sll child (.c 20)) pre
  let childPc := mkAdd (mkBin .sll child (.c 8)) (.reg .x29)
  let hb := if advance then mkAdd (.reg .x28) (.reg .x6) else .c (BitVec.ofNat 64 1537)
  let field := mkAdd (mkBin .and
    (mkBin .srl dig (.c (BitVec.ofNat 64 (bit % 64 + 5)))) (.reg .x2)) (.reg .x24)
  let n := if !advance then 15 else if coord = 7 then 16 else 17
  let regs := if reload then RegFile.init.set .x16 dig else RegFile.init
  let regs := (regs.set .x3 child).set .x4 route
  let regs := if advance then regs.set .x15 pre else regs
  let regs := (regs.set .x31 packed).set .x23 childPc
  let regs := if advance then (regs.set .x8 (addC (.reg .x8) 1024)).set .x28 hb else regs.set .x28 hb
  let node := if advance then mkAdd (.reg .x27) (.reg .x6) else mkBin .or (.reg .x27) (.reg .x28)
  let regs := (((regs.set .x27 node).set
    .x14 field).set .x9 (.c (BitVec.ofNat 64 (0x420 + 32 * coord)))).set
    .x1 (.c (pcOf (p + n)))
  ⟨⟨regs, [], []⟩, mkBin .and field (.c (~~~1#64)), .jump, n, n⟩
end W9Machine
end
section
namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWords8 : List (BitVec 32) := [0x158d193,0x7f1f193,0x2019213,0x1626233,0x6787b3,0x1419f93,0xffefb3,0x819b93,0x1db8bb3,0x40040413,0x6e0e33,0x6d8db3,0x1a8d713,0x277733,0x1870733,0x52000493,0x700e7]
theorem dispatch8_checked : rOK (symRun {} dispatchWords8 (pcOf 180) 17) (coordDispatch 180 213 8 true false) = true := by decide +kernel
theorem dispatch8_linked : sliceChecked 180 dispatchWords8 = true := by decide +kernel
end W9Machine
end
section
namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWords6 : List (BitVec 32) := [0x2a85193,0x7f1f193,0x2019213,0x1626233,0x6787b3,0x1419f93,0xffefb3,0x819b93,0x1db8bb3,0x40040413,0x6e0e33,0x6d8db3,0x2f85713,0x277733,0x1870733,0x4e000493,0x700e7]
theorem dispatch6_checked : rOK (symRun {} dispatchWords6 (pcOf 147) 17) (coordDispatch 147 170 6 true false) = true := by decide +kernel
theorem dispatch6_linked : sliceChecked 147 dispatchWords6 = true := by decide +kernel
end W9Machine
end
section
namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWords5 : List (BitVec 32) := [0x1585193,0x7f1f193,0x2019213,0x1626233,0x6787b3,0x1419f93,0xffefb3,0x819b93,0x1db8bb3,0x40040413,0x6e0e33,0x6d8db3,0x1a85713,0x277733,0x1870733,0x4c000493,0x700e7]
theorem dispatch5_checked : rOK (symRun {} dispatchWords5 (pcOf 130) 17) (coordDispatch 130 149 5 true false) = true := by decide +kernel
theorem dispatch5_linked : sliceChecked 130 dispatchWords5 = true := by decide +kernel
end W9Machine
end
section
namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWords3 : List (BitVec 32) := [0x2a85193,0x7f1f193,0x2019213,0x1626233,0x6787b3,0x1419f93,0xffefb3,0x819b93,0x1db8bb3,0x40040413,0x6e0e33,0x6d8db3,0x2f85713,0x277733,0x1870733,0x48000493,0x700e7]
theorem dispatch3_checked : rOK (symRun {} dispatchWords3 (pcOf 96) 17) (coordDispatch 96 106 3 true false) = true := by decide +kernel
theorem dispatch3_linked : sliceChecked 96 dispatchWords3 = true := by decide +kernel
end W9Machine
end
section
namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWords7 : List (BitVec 32) := [0x7f8f193,0x2019213,0x1626233,0x6787b3,0x1419f93,0xffefb3,0x819b93,0x1db8bb3,0x40040413,0x6e0e33,0x6d8db3,0x58d713,0x277733,0x1870733,0x50000493,0x700e7]
theorem dispatch7_checked : rOK (symRun {} dispatchWords7 (pcOf 164) 16) (coordDispatch 164 192 7 true false) = true := by decide +kernel
theorem dispatch7_linked : sliceChecked 164 dispatchWords7 = true := by decide +kernel
end W9Machine
end
section
namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWords4 : List (BitVec 32) := [0x7003803,0x7f87193,0x2019213,0x1626233,0x6787b3,0x1419f93,0xffefb3,0x819b93,0x1db8bb3,0x40040413,0x6e0e33,0x6d8db3,0x585713,0x277733,0x1870733,0x4a000493,0x700e7]
theorem dispatch4_checked : rOK (symRun {} dispatchWords4 (pcOf 113) 17) (coordDispatch 113 128 4 true true) = true := by decide +kernel
theorem dispatch4_linked : sliceChecked 113 dispatchWords4 = true := by decide +kernel
end W9Machine
end
section
namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWords2 : List (BitVec 32) := [0x1585193,0x7f1f193,0x2019213,0x1626233,0x6787b3,0x1419f93,0xffefb3,0x819b93,0x1db8bb3,0x40040413,0x6e0e33,0x6d8db3,0x1a85713,0x277733,0x1870733,0x46000493,0x700e7]
theorem dispatch2_checked : rOK (symRun {} dispatchWords2 (pcOf 79) 17) (coordDispatch 79 85 2 true false) = true := by decide +kernel
theorem dispatch2_linked : sliceChecked 79 dispatchWords2 = true := by decide +kernel
end W9Machine
end
section
namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWords1 : List (BitVec 32) := [0x6803803,0x7f87193,0x2019213,0x1626233,0x6787b3,0x1419f93,0xffefb3,0x819b93,0x1db8bb3,0x40040413,0x6e0e33,0x6d8db3,0x585713,0x277733,0x1870733,0x44000493,0x700e7]
theorem dispatch1_checked : rOK (symRun {} dispatchWords1 (pcOf 62) 17) (coordDispatch 62 64 1 true true) = true := by decide +kernel
theorem dispatch1_linked : sliceChecked 62 dispatchWords1 = true := by decide +kernel
end W9Machine
end
section
namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWords0 : List (BitVec 32) := [0x2b85193,0x7f1f193,0x2019213,0x1626233,0x1419f93,0xffefb3,0x819b93,0x1db8bb3,0x1cdedb3,0x60100e13,0x3085713,0x277733,0x1870733,0x42000493,0x700e7]
theorem dispatch0_checked : rOK (symRun {} dispatchWords0 (pcOf 47) 15) (coordDispatch 47 43 0 false false) = true := by decide +kernel
theorem dispatch0_linked : sliceChecked 47 dispatchWords0 = true := by decide +kernel
end W9Machine
end
section
end
section
namespace W9Drv
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open W9Machine
def dispatchCode (k : Fin 9) : List (BitVec 32) :=
  [dispatchWords0, dispatchWords1, dispatchWords2, dispatchWords3, dispatchWords4,
    dispatchWords5, dispatchWords6, dispatchWords7, dispatchWords8].getD k.val []
def dispatchBit (k : Fin 9) : Nat := [43,64,85,106,128,149,170,192,213].getD k.val 0
def dispatchLen (k : Fin 9) : Nat := if k.val = 0 then 15 else if k.val = 7 then 16 else 17
def dispatchResult (k : Fin 9) : Result :=
  coordDispatch (dispatchPc k.val) (dispatchBit k) k.val (decide (k.val ≠ 0))
    (decide (k.val = 1 ∨ k.val = 4))
theorem dispatch_checked (k : Fin 9) :
    rOK (symRun {} (dispatchCode k) (pcOf (dispatchPc k.val)) (dispatchLen k))
      (dispatchResult k) = true := by
  fin_cases k
  · exact dispatch0_checked
  · exact dispatch1_checked
  · exact dispatch2_checked
  · exact dispatch3_checked
  · exact dispatch4_checked
  · exact dispatch5_checked
  · exact dispatch6_checked
  · exact dispatch7_checked
  · exact dispatch8_checked
theorem dispatch_linked (k : Fin 9) :
    sliceChecked (dispatchPc k.val) (dispatchCode k) = true := by
  fin_cases k
  · exact dispatch0_linked
  · exact dispatch1_linked
  · exact dispatch2_linked
  · exact dispatch3_linked
  · exact dispatch4_linked
  · exact dispatch5_linked
  · exact dispatch6_linked
  · exact dispatch7_linked
  · exact dispatch8_linked
theorem dispatch_mem (k : Fin 9) (u : MachineState) (A : Word) :
    ((dispatchResult k).toState u).getMem A = u.getMem A := by
  rfl
theorem dispatch_steps (pk : Digest) (w : WBytes) (a : HashOutput) (k : Fin 9)
    (roots : List (Digest × Digest)) (u : MachineState) (hu : CoordPre pk w a k.val roots u) :
    Steps Frozen.image u (dispatchLen k) (dispatchLen k) ((dispatchResult k).toState u) := by
  have hs := symRun_sound (rOK_eq (dispatch_checked k))
    (slice_at _ _ (dispatch_linked k)) u hu.pc
  have hcost : (dispatchResult k).steps = dispatchLen k ∧
      (dispatchResult k).cycles = dispatchLen k := by
    fin_cases k <;> exact ⟨rfl, rfl⟩
  rw [hcost.1, hcost.2] at hs
  apply hs
  change Oblig.all u (dispatchResult k).st.obl
  rw [Oblig.all_iff]
  intro o ho
  have hobl : (dispatchResult k).st.obl = [] := by
    fin_cases k <;> rfl
  rw [hobl] at ho
  simp at ho
end W9Drv
end
section
set_option maxRecDepth 10000
namespace W9Drv
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open W9Machine
def chainEntryState (a : HashOutput) (k : Fin 9) (u : MachineState) : MachineState :=
  { (dispatchResult k).toState u with
    pc := pcOf (Frozen.layout.chainWord (N600.embed (ClaudeWCT.WCT9.rank a k))) }
theorem dispatch_child (a : HashOutput) (k : Fin 9) :
    (a.extractLsb' (64 * (dispatchBit k / 64)) 64 >>> (dispatchBit k % 64)) &&& 127#64 =
      BitVec.ofNat 64 (ClaudeWCT.WCT9.child a k).val := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow]
  change _ &&& (2 ^ 7 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]
  fin_cases k <;> simp [dispatchBit, ClaudeWCT.WCT9.child, ClaudeWCT.WCT9.coordBase,
    BitVec.toNat_ofNat] <;> omega
def dispatchDig (k : Fin 9) : E :=
  if k.val ≥ 7 then .reg .x17 else
  if decide (k.val = 1 ∨ k.val = 4) then
    .ld (.c (BitVec.ofNat 64 (96 + 8*(dispatchBit k/64)))) else .reg .x16
theorem dispatchDig_eval (pk : Digest) (w : WBytes) (a : HashOutput) (k : Fin 9)
    (pairs : List (Digest × Digest)) (u : MachineState) (hu : CoordPre pk w a k.val pairs u) :
    (dispatchDig k).eval u = a.extractLsb' (64*(dispatchBit k/64)) 64 := by
  have hd := hu.digest (dispatchBit k/64) (by fin_cases k <;> decide)
  fin_cases k <;> first | exact hd | exact hu.cached | exact hu.cached3
def dispatchChild (k : Fin 9) : E := mkBin .and
  (if dispatchBit k % 64 = 0 then dispatchDig k else
    mkBin .srl (dispatchDig k) (.c (BitVec.ofNat 64 (dispatchBit k % 64)))) (.c 127)
theorem dispatchChild_eval (pk : Digest) (w : WBytes) (a : HashOutput) (k : Fin 9)
    (pairs : List (Digest × Digest)) (u : MachineState) (hu : CoordPre pk w a k.val pairs u) :
    (dispatchChild k).eval u = BitVec.ofNat 64 (ClaudeWCT.WCT9.child a k).val := by
  have hd := dispatchDig_eval pk w a k pairs u hu
  have hs : (BitVec.ofNat 64 (dispatchBit k % 64)).toNat % 64 = dispatchBit k % 64 := by
    simp only [BitVec.toNat_ofNat]; omega
  unfold dispatchChild
  split
  · rename_i he
    simp only [mkBin_eval, E.eval, BinOp.eval, hd]
    have hc := dispatch_child a k
    simp only [he, BitVec.ushiftRight_zero] at hc
    exact hc
  · simp only [mkBin_eval, E.eval, BinOp.eval, hd, hs]
    exact dispatch_child a k
theorem dispatch_keep (k : Fin 9) (u : MachineState) (r : Reg)
    (hr : r ∉ [.x1,.x3,.x4,.x8,.x9,.x14,.x15,.x16,.x23,.x27,.x28,.x31]) :
    ((dispatchResult k).toState u).getReg r = u.getReg r := by
  rw [Result.toState_getReg]
  fin_cases k <;> cases r <;> first | rfl | exact False.elim (hr (by decide))
theorem dispatch_route (k : Fin 9) (u : MachineState) :
    ((dispatchResult k).toState u).getReg .x4 =
      ((dispatchChild k).eval u <<< 32) ||| u.getReg .x22 := by
  fin_cases k <;> rfl
theorem dispatch_childPC (k : Fin 9) (u : MachineState) :
    ((dispatchResult k).toState u).getReg .x23 =
      ((dispatchChild k).eval u <<< 8) + u.getReg .x29 := by
  fin_cases k <;> rfl
theorem dispatch_prefix (k : Fin 9) (u : MachineState) :
    ((dispatchResult k).toState u).getReg .x31 =
      ((dispatchChild k).eval u <<< 20) |||
        (if k.val = 0 then u.getReg .x15 else u.getReg .x15 + u.getReg .x6) := by
  fin_cases k <;> rfl
theorem packedPrefix_eval (i k j : Nat) (hk : k < 9) :
    (BitVec.ofNat 64 j <<< 20) ||| BitVec.ofNat 64 (i*2^27 + 65536*k) =
      BitVec.ofNat 64 (V3.chainPrefix i k j) := by
  have hc : 65536*k < 2^27 := by omega
  have hp : i*2^27 + 65536*k = (i <<< 27) ||| (k <<< 16) := by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (by simpa [Nat.shiftLeft_eq, Nat.mul_comm] using hc)]
    simp [Nat.shiftLeft_eq, Nat.mul_comm]
  rw [hp, BitVec.ofNat_or]
  have hs (x n : Nat) : BitVec.ofNat 64 x <<< n = BitVec.ofNat 64 (x <<< n) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_mod]
  rw [hs, ← BitVec.ofNat_or, ← BitVec.ofNat_or]
  unfold V3.chainPrefix
  rw [Nat.or_comm]
theorem nodeLow_step (k : Nat) (hk : k < 8) (index : Nat) :
    BitVec.ofNat 64 (V3.nodeLow k index) + 65536 = BitVec.ofNat 64 (V3.nodeLow (k + 1) index) := by
  have h1 := nodeLow_add ⟨k, by omega⟩ index
  have h2 := nodeLow_add ⟨k + 1, by omega⟩ index
  simp only [Fin.val_mk] at h1 h2
  rw [h1, h2, show (65536 : BitVec 64) = BitVec.ofNat 64 65536 from rfl, ← BitVec.ofNat_add]
  congr 1
  omega
theorem dispatch_x28 (pk : Digest) (w : WBytes) (a : HashOutput) (k : Fin 9)
    (pairs : List (Digest × Digest)) (u : MachineState) (hu : CoordPre pk w a k.val pairs u) :
    ((dispatchResult k).toState u).getReg .x28 = BitVec.ofNat 64 (1537 + 65536 * k.val) := by
  by_cases hk0 : k.val = 0
  · have hkz : k = 0 := Fin.ext hk0
    subst hkz
    rfl
  · have he : ((dispatchResult k).toState u).getReg .x28 = u.getReg .x28 + u.getReg .x6 := by
      fin_cases k <;> first | exact absurd rfl hk0 | rfl
    rw [he, hu.headerReg hk0, hu.coordStep, show (65536 : BitVec 64) = BitVec.ofNat 64 65536 from rfl,
      ← BitVec.ofNat_add]
    congr 1
    omega
theorem dispatch_chain_pre (pk : Digest) (w : WBytes) (a : HashOutput) (k : Fin 9)
    (pairs : List (Digest × Digest)) (u : MachineState) (hu : CoordPre pk w a k.val pairs u) :
    N600.Pre Frozen.layout w (idxOf a) k (ClaudeWCT.WCT9.child a k) (ClaudeWCT.WCT9.rank a k)
      (chainEntryState a k u) := by
  have hm (A : Word) : (chainEntryState a k u).getMem A = u.getMem A := rfl
  have hr (r : Reg) (h : r ∉ [.x1,.x3,.x4,.x8,.x9,.x14,.x15,.x16,.x23,.x27,.x28,.x31]) :
      (chainEntryState a k u).getReg r = u.getReg r := dispatch_keep k u r h
  have hc := dispatchChild_eval pk w a k pairs u hu
  have hi : idxOf a < 2^31 := Nat.mod_lt _ (by decide)
  have hj := (ClaudeWCT.WCT9.child a k).isLt
  refine {
    indexBound := hi
    pc := rfl
    baseReg := ?_
    headerReg := ?_
    prefixReg := ?_
    route := ?_
    hashMode := (hr .x5 (by decide)).trans (hu.glob.1 (.x5, 0) (by simp [baseK]))
    stepOne := (hr .x7 (by decide)).trans hu.stepOne
    stepTwo := (hr .x13 (by decide)).trans hu.stepTwo
    hashLen := (hr .x11 (by decide)).trans hu.hashLen
    childPC := ?_
    returnPC := ?_
    indexReg := (hr .x22 (by decide)).trans hu.index
    nodeHeader := ?_
    forestPointer := ?_
    heaps := ?_
    witness := by
      intro off ho h8
      have hw := hu.coords k (Nat.le_refl _) off ho h8
      rw [hm]
      simpa only [OrigW, Chain.base, coordinateBase, V3.regionOffset,
        show 2112 + 1024*k.val + off - 2048 = 64 + 1024*k.val + off by omega] using hw }
  · change ((dispatchResult k).toState u).getReg .x8 = _
    fin_cases k <;> simp [dispatchResult, coordDispatch, Result.toState_getReg,
      RegFile.get, RegFile.set, RegFile.init, addC_eval, E.eval, hu.baseReg, Chain.base, coordinateBase]
  · change ((dispatchResult k).toState u).getReg .x28 = _
    rw [dispatch_x28 pk w a k pairs u hu, header_lo, if_neg (by decide)]
    rw [hdr0_eq 6 k.val (idxOf a) 0 (by decide) (by have := k.isLt; omega)
      (by omega) (by decide)]
    congr 1 <;> omega
  · change ((dispatchResult k).toState u).getReg .x31 = _
    rw [dispatch_prefix, hc, hu.prefixReg, hu.coordStep]
    have he : (if k.val = 0 then BitVec.ofNat 64 (idxOf a*2^27+65536*(k.val-1))
        else BitVec.ofNat 64 (idxOf a*2^27+65536*(k.val-1)) + 65536) =
        BitVec.ofNat 64 (idxOf a*2^27+65536*k.val) := by
      fin_cases k <;> simp [← BitVec.ofNat_add, Nat.add_assoc]
    rw [he]
    exact packedPrefix_eval _ _ _ k.isLt
  · change ((dispatchResult k).toState u).getReg .x4 = _
    rw [dispatch_route, hc, hu.index]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by omega : (ClaudeWCT.WCT9.child a k).val < 2^64),
      Nat.mod_eq_of_lt (by omega : (ClaudeWCT.WCT9.child a k).val * 2^32 < 2^64),
      Nat.mod_eq_of_lt (by omega : idxOf a < 2^64)]
    rw [Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt (by omega : idxOf a < 2^32)]
    omega
  · change ((dispatchResult k).toState u).getReg .x23 = _
    rw [dispatch_childPC, hc, hu.childBlock]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
      Frozen.layout, pcOf]
    omega
  · change ((dispatchResult k).toState u).getReg .x1 = _
    fin_cases k <;> rfl
  · change ((dispatchResult k).toState u).getReg .x27 = _
    by_cases hk0 : k.val = 0
    · have hkz : k = 0 := Fin.ext hk0
      subst hkz
      have he : ((dispatchResult 0).toState u).getReg .x27 =
          BitVec.ofNat 64 (1+3*256+(4+(0 : Fin 9).val)*65536) ||| BitVec.ofNat 64 (idxOf a*2^32) := by
        have h27 : ((dispatchResult 0).toState u).getReg .x27 = u.getReg .x27 ||| u.getReg .x28 := rfl
        rw [h27, hu.nodeZero rfl, hu.headerZero rfl]
        all_goals rfl
      rw [he, nodeLow_add]
      rw [BitVec.or_comm, ofNat_or_disjoint _ _ 32 (by simp) (by simp)]
      rw [Nat.add_comm]
    · have he : ((dispatchResult k).toState u).getReg .x27 = u.getReg .x27 + u.getReg .x6 := by
        fin_cases k <;> first | exact absurd rfl hk0 | rfl
      rw [he, hu.nodeReg hk0, hu.coordStep]
      have hs := nodeLow_step (k.val - 1) (by have := k.isLt; omega) (idxOf a)
      rwa [show k.val - 1 + 1 = k.val by omega] at hs
  · change ((dispatchResult k).toState u).getReg .x9 = _
    fin_cases k <;> rfl
  · intro h h2 h7
    exact (hr (Child.heapReg h) (by interval_cases h <;> decide)).trans (hu.heaps h h2 h7)
end W9Drv
end
section
namespace W9Drv
set_option maxRecDepth 10000
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open W9Machine
theorem aligned_clear_low (n : Nat) (h : n % 2 = 0) :
    BitVec.ofNat 64 n &&& ~~~1#64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_one]
  by_cases h0 : j = 0
  · subst h0
    simp
    rw [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat, Nat.testBit_zero]
    simp [h]
  · simp [h0, hj]
theorem field_mask (x : BitVec 64) :
    x &&& 65532#64 = ((x >>> 2) &&& 16383#64) <<< 2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp
theorem dispatch_field (a : HashOutput) (k : Fin 9) :
    (a.extractLsb' (64 * (dispatchBit k / 64)) 64 >>> (dispatchBit k % 64 + 5)) &&&
      65532#64 = BitVec.ofNat 64 (4 * ClaudeWCT.WCT9.field a k) := by
  rw [field_mask]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_and, BitVec.toNat_ushiftRight,
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  change (_ &&& (2 ^ 14 - 1)) * 4 % 2 ^ 64 = _
  rw [Nat.and_two_pow_sub_one_eq_mod]
  fin_cases k <;> simp [dispatchBit, ClaudeWCT.WCT9.field, ClaudeWCT.WCT9.coordBase,
    BitVec.toNat_ofNat] <;> omega
theorem dispatch_pc (pk : Digest) (w : WBytes) (a : HashOutput) (k : Fin 9)
    (roots : List (Digest × Digest)) (u : MachineState) (hu : CoordPre pk w a k.val roots u) :
    ((dispatchResult k).toState u).pc = pcOf (jtStart + ClaudeWCT.WCT9.field a k) := by
  have he : ((dispatchResult k).toState u).pc =
      (mkBin .and (mkAdd (mkBin .and
    (mkBin .srl (dispatchDig k)
      (.c (BitVec.ofNat 64 (dispatchBit k % 64 + 5)))) (.reg .x2)) (.reg .x24))
      (.c (~~~1#64))).eval u := by
    fin_cases k <;> rfl
  rw [he]
  simp only [mkBin_eval, mkAdd_eval, E.eval, BinOp.eval, hu.mask, hu.jt]
  rw [dispatchDig_eval pk w a k roots u hu]
  have hshift : (BitVec.ofNat 64 (dispatchBit k % 64 + 5)).toNat % 64 =
      dispatchBit k % 64 + 5 := by fin_cases k <;> decide
  rw [hshift]
  change (((a.extractLsb' (64 * (dispatchBit k / 64)) 64 >>>
    (dispatchBit k % 64 + 5)) &&& 65532#64) + 878592#64) &&& ~~~1#64 = _
  rw [dispatch_field a k]
  rw [ofNat_add_ofNat, aligned_clear_low _ (by omega)]
  congr 1
  unfold jtStart
  omega
theorem codeAt_single (pc : Nat) (words : List (BitVec 32))
    (hb : pc + words.length < 242393)
    (hc : CodeAt Frozen.image (pcOf pc) words) (i : Nat) (hi : i < words.length) :
    CodeAt Frozen.image (pcOf (pc + i)) [words[i]] := by
  have hp : (pcOf pc).toNat = 4096 + 4 * pc := by
    simp only [pcOf, BitVec.toNat_ofNat]
    omega
  have hpi : (pcOf (pc + i)).toNat = 4096 + 4 * (pc + i) := by
    simp only [pcOf, BitVec.toNat_ofNat]
    omega
  refine ⟨by rw [hpi]; omega, by rw [hpi]; omega, by rw [hpi]; simp; omega, ?_⟩
  have hpre := hc.2.2.2.drop i
  have hs : [words[i]] <+: words.drop i := by
    rw [List.singleton_prefix_iff_head?_eq_some]
    simp [List.head?_drop, hi]
  have ht := hs.trans hpre
  simpa [hp, hpi, List.drop_drop, Nat.add_comm] using ht
theorem jt_steps (field : Fin 16384) (u : MachineState)
    (hu : u.pc = pcOf (jtStart + field.val)) :
    Steps Frozen.image u 1 1 {u with pc := pcOf (jtTarget field.val)} := by
  let c : Fin 64 := ⟨field.val / 256, by omega⟩
  let i : Nat := field.val % 256
  have hi : i < (jtChunk c).length := by rw [jtChunk_length]; exact Nat.mod_lt _ (by decide)
  have he : 256 * c.val + i = field.val := by dsimp [c, i]; omega
  have hcode := codeAt_single (jtStart + 256 * c.val) (jtChunk c)
    (by rw [jtChunk_length]; have := c.isLt; unfold jtStart; omega)
    (jtChunk_linked c) i hi
  have hcheck := jtChunk_checked c
  unfold jtCheck at hcheck
  have hmem : ((jtChunk c)[i], i) ∈ (jtChunk c).zipIdx := by
    have hx := List.getElem_mem (l := (jtChunk c).zipIdx) (n := i) (by simpa using hi)
    simpa using hx
  have hrun := List.all_eq_true.mp hcheck _ hmem
  simp only at hrun
  rw [Nat.add_assoc, he] at hrun
  rw [Nat.add_assoc, he] at hcode
  have hs := symRun_sound (rOK_eq hrun) hcode u hu (by trivial)
  convert hs using 1
  apply MachineState.ext' <;> try rfl
  funext r
  cases r <;> rfl
end W9Drv
end
section
set_option maxHeartbeats 400000
namespace W9Drv
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest M)
open W9Machine
theorem coord_core_good (chains : N600.AllGood Frozen.layout)
    (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128) (rank : Fin 600)
    (u : MachineState) (N C A : Nat) (Q : Prop)
    (K : (Digest × Digest) → OracleComp HashSpec Obs)
    (hu : N600.Pre Frozen.layout w index k j rank u)
    (hnext : ∀ ends entry, Chain.Post Frozen.layout w index k j u ends entry →
      ∀ pair t, Child.Post Frozen.layout k entry pair t →
        GoodQFor Frozen.image t N C Q A (K (pair.left, pair.right))) :
    GoodQFor Frozen.image u (N + 131) (C + 188) Q (A + (N600.rankCost rank + 99))
      (ccM (ClaudeWCT.W9.T3M.wctCoordP w index k j rank) K) := by
  rw [wctCoordP_split w index k j rank hu.indexBound, ccM_bind]
  have hcont (ends : List Digest) (entry : MachineState)
      (hp : Chain.Post Frozen.layout w index k j u ends entry) :
      GoodQFor Frozen.layout.image entry (N+42) (C+99) Q (A+99)
        (ccM (coordTail w index k j ends) K) := by
    have hg := ChildProof.child_good j w index k ends entry N C A Q
      (fun pair => K (pair.left, pair.right)) hp.child (hnext ends entry hp)
    rw [← childProgram_canonical w index k j ends hp.length hu.indexBound]
    simp only [ccM_bind, ccM_pure]
    exact hg
  have hc := chains rank w index k j u (N+42) (C+99) (A+99) Q
    (fun ends => ccM (coordTail w index k j ends) K) hu hcont
  convert hc using 1 <;> first | rfl | omega
#print axioms coord_core_good
end W9Drv
end
section
namespace W9Drv
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open W9Machine
theorem coord_frame (w : WBytes) (a : HashOutput) (k : Fin 9) (u entry t : MachineState)
    (ends : List Digest) (pair : V3.RootPair)
    (hp : Chain.Post Frozen.layout w (idxOf a) k (ClaudeWCT.WCT9.child a k)
      (chainEntryState a k u) ends entry)
    (ht : Child.Post Frozen.layout k entry pair t) :
    Frame u t (fun A => (coordinateBase k ≤ A ∧ A < coordinateBase k + 1024) ∨
      (pairAddress k ≤ A ∧ A < pairAddress k + 48)) := by
  intro A hA hn
  rw [ht.frame A hA (by unfold Child.writes; dsimp at hn; omega)]
  exact hp.frame A hA (by unfold Chain.writes Chain.base; dsimp at hn; omega)
theorem coord_next (pk : Digest) (w : WBytes) (a : HashOutput) (k : Fin 9)
    (pairs : List (Digest × Digest)) (u entry t : MachineState) (ends : List Digest)
    (pair : V3.RootPair) (hu : CoordPre pk w a k.val pairs u)
    (hp : Chain.Post Frozen.layout w (idxOf a) k (ClaudeWCT.WCT9.child a k)
      (chainEntryState a k u) ends entry)
    (ht : Child.Post Frozen.layout k entry pair t) :
    CoordPre pk w a (k.val+1) (pairs ++ [(pair.left,pair.right)]) t := by
  have hk := k.isLt
  have hc := dispatch_chain_pre pk w a k pairs u hu
  have hf := coord_frame w a k u entry t ends pair hp ht
  have hm (A : Nat) (hA : A < 2^64)
      (hs : A < 1056 ∨ (1360 ≤ A ∧ A < 2112) ∨ 11328 ≤ A) :
      t.getMem (BitVec.ofNat 64 A) = u.getMem (BitVec.ofNat 64 A) := by
    apply hf A hA
    unfold coordinateBase pairAddress
    omega
  have hr (r : Reg) (h : r ∉ [.x3,.x10,.x11,.x12,.x14,.x25]) :
      t.getReg r = (chainEntryState a k u).getReg r := by
    rw [ht.keep r (by
      simp only [Child.clobbers, List.mem_cons, List.not_mem_nil, or_false] at *
      tauto)]
    exact hp.keep r h
  have hd (r : Reg) (h : r ∉ [.x1,.x3,.x4,.x8,.x9,.x14,.x15,.x16,.x23,.x27,.x28,.x31]) :
      (chainEntryState a k u).getReg r = u.getReg r := dispatch_keep k u r h
  have hg : Glob baseK w pk t := by
    obtain ⟨hreg, hh, hpk, hz, hhalf, hdata⟩ := hu.glob
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro p hp
      simp only [baseK, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact (hr .x5 (by decide)).trans ((hd .x5 (by decide)).trans (hreg (.x5, 0) (by simp [baseK])))
      · exact (hr .x18 (by decide)).trans ((hd .x18 (by decide)).trans (hreg (.x18, 4095) (by simp [baseK])))
    · intro j hj
      rw [hm _ (by unfold WIT; omega) (by unfold WIT; omega)]
      exact hh j hj
    · exact ⟨(hm 160 (by decide) (by omega)).trans hpk.1,
        (hm 168 (by decide) (by omega)).trans hpk.2⟩
    · intro A hA
      have hb : A < 1056 := by simp [pSlots] at hA; omega
      exact (hm A (by omega) (Or.inl hb)).trans (hz A hA)
    · change (t.getMem (BitVec.ofNat 64 CTRW)).toNat / 2 ^ 32 = 0
      rw [hm CTRW (by decide) (Or.inl (by decide))]
      exact hhalf
    · exact hdata.congr (fun A hA hB => hm A (by omega) (Or.inr (Or.inr (by unfold TAB at hA; omega))))
  refine {
    le := by omega
    length := by simp [hu.length]
    pc := ?_
    glob := hg
    digest := fun i hi => (hm _ (by omega) (Or.inl (by omega))).trans (hu.digest i hi)
    bank := ?_
    index := (hr .x22 (by decide)).trans hc.indexReg
    heaps := ?_
    stepOne := (hr .x7 (by decide)).trans hc.stepOne
    stepTwo := (hr .x13 (by decide)).trans hc.stepTwo
    hashLen := ht.hashLen
    coordStep := (hr .x6 (by decide)).trans ((hd .x6 (by decide)).trans hu.coordStep)
    prefixReg := ?_
    cached3 := (hr .x17 (by decide)).trans ((hd .x17 (by decide)).trans hu.cached3)
    cached := ?_
    nodeReg := fun _ => by
      rw [show k.val + 1 - 1 = k.val by omega]
      exact (hr .x27 (by decide)).trans hc.nodeHeader
    nodeZero := fun h => absurd h (by omega)
    headerZero := fun h => absurd h (by omega)
    zero := ⟨(hm 1024 (by decide) (Or.inl (by omega))).trans hu.zero.1,
      (hm 1032 (by decide) (Or.inl (by omega))).trans hu.zero.2⟩
    mask := (hr .x2 (by decide)).trans ((hd .x2 (by decide)).trans hu.mask)
    jt := (hr .x24 (by decide)).trans ((hd .x24 (by decide)).trans hu.jt)
    childBlock := (hr .x29 (by decide)).trans ((hd .x29 (by decide)).trans hu.childBlock)
    baseReg := by simpa [Chain.base, coordinateBase] using (hr .x8 (by decide)).trans hc.baseReg
    headerReg := fun _ => by
      rw [hr .x28 (by decide), show k.val + 1 - 1 = k.val by omega]
      exact dispatch_x28 pk w a k pairs u hu
    pairs := ?_
    coords := ?_
    layer := ?_ }
  · rw [ht.pc]
    fin_cases k <;> rfl
  · refine ⟨?_, ?_, ?_⟩
    · exact (hm _ (by omega) (Or.inr (Or.inr (by omega)))).trans hu.bank.node
    · intro i hi
      exact (hm _ (by unfold TOPLOAD; omega) (Or.inr (Or.inr (by unfold TOPLOAD; omega)))).trans
        (hu.bank.top i hi)
    · exact (hm _ (by unfold TOPLOAD; omega) (Or.inr (Or.inr (by unfold TOPLOAD; omega)))).trans hu.bank.top8
  · intro h h2 h7
    exact (hr (Child.heapReg h) (by interval_cases h <;> decide)).trans (hc.heaps h h2 h7)
  · rw [hr .x15 (by decide)]
    change ((dispatchResult k).toState u).getReg .x15 = _
    fin_cases k <;> simp [dispatchResult, coordDispatch, Result.toState_getReg,
      RegFile.get, RegFile.set, RegFile.init, mkAdd_eval, E.eval, hu.prefixReg, hu.coordStep,
      ← BitVec.ofNat_add, Nat.add_assoc]
  · rw [hr .x16 (by decide)]
    have hd1 := hu.digest 1 (by decide)
    have hd2 := hu.digest 2 (by decide)
    have hcache := hu.cached
    fin_cases k <;> first | exact hcache | exact hd1 | exact hd2
  · intro i hi
    by_cases he : i = k.val
    · subst i
      rw [List.getD_append_right _ _ _ _ (by rw [hu.length]), hu.length, Nat.sub_self]
      exact ⟨ht.left, ht.right⟩
    · rw [List.getD_append _ _ _ _ (by rw [hu.length]; omega)]
      have old := hu.pairs i (by omega)
      refine ⟨ChildProof.DigAt.of_eq old.1 ?_ ?_, ChildProof.DigAt.of_eq old.2 ?_ ?_⟩
      all_goals apply hf _ (by omega); unfold coordinateBase pairAddress; omega
  · intro l hl off hoff halign
    unfold OrigW
    rw [hf _ (by have := l.isLt; unfold coordinateBase; omega) (by
      have := l.isLt
      unfold coordinateBase pairAddress
      omega)]
    exact hu.coords l (by omega) off hoff halign
  · exact hu.layer.frame (fun j hj h => hm _ (by unfold WIT WX at *; omega)
      (by unfold WIT; omega))
theorem coord_good (chains : N600.AllGood Frozen.layout) (pk : Digest) (w : WBytes) (a : HashOutput)
    (k : Fin 9) (roots : List (Digest × Digest)) (u : MachineState) (N C A : Nat) (Q : Prop)
    (K : Option (List (Digest × Digest)) → OracleComp HashSpec Obs)
    (hu : CoordPre pk w a k.val roots u) (hnone : K none = pure (false, 0))
    (hnext : ∀ root t, CoordPre pk w a (k.val + 1) (roots ++ [root]) t →
      GoodQFor Frozen.image t N C Q A (K (some (roots ++ [root])))) :
    GoodQFor Frozen.image u (N + (if k.val = 0 then 204 else if k.val = 7 then 205 else 206))
      (C + (if k.val = 0 then 204 else if k.val = 7 then 205 else 206)) Q (A + ((if k.val = 0 then 115 else if k.val = 7 then 116 else 117) + N600.rankCost (ClaudeWCT.WCT9.rank a k)))
      (ccM (ClaudeWCT.W9.T3M.wctStep w a (some roots) k) K) := by
  have ds := dispatch_steps pk w a k roots u hu
  let f : Fin 16384 := ⟨ClaudeWCT.WCT9.field a k, Nat.mod_lt _ (by decide)⟩
  have js := jt_steps f ((dispatchResult k).toState u) (dispatch_pc pk w a k roots u hu)
  by_cases hok : ClaudeWCT.W9.T3M.fieldOk a k = true
  · have hfield : ClaudeWCT.WCT9.field a k < 16200 := by
      exact of_decide_eq_true hok
    have he : jtTarget f.val = Frozen.layout.chainWord (N600.embed (ClaudeWCT.WCT9.rank a k)) := by
      simp only [jtTarget, f, if_pos hfield, ClaudeWCT.WCT9.rank]
    rw [he] at js
    change Steps Frozen.image ((dispatchResult k).toState u) 1 1 (chainEntryState a k u) at js
    have core := coord_core_good chains w (idxOf a) k (ClaudeWCT.WCT9.child a k)
      (ClaudeWCT.WCT9.rank a k) (chainEntryState a k u) N C A Q
      (fun root => K (some (roots ++ [root]))) (dispatch_chain_pre pk w a k roots u hu)
      (fun ends entry hp pair t ht => hnext _ _ (coord_next pk w a k roots u entry t ends pair hu hp ht))
    have full := (core.steps js).steps ds
    simp only [ClaudeWCT.W9.T3M.wctStep, hok, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, ccM_bind, ccM_pure]
    exact full.mono (by unfold dispatchLen; split_ifs <;> omega)
      (by unfold dispatchLen; split_ifs <;> omega)
      (fun hq => ⟨hq, by unfold dispatchLen; split_ifs <;> omega⟩)
  · have hfield : ¬ ClaudeWCT.WCT9.field a k < 16200 := by
      intro hh
      exact hok (show decide (ClaudeWCT.WCT9.field a k < 16200) = true from decide_eq_true hh)
    have he : jtTarget f.val = 24 := by simp only [jtTarget, f, if_neg hfield, jtReject]
    rw [he] at js
    let s : MachineState := { (dispatchResult k).toState u with pc := pcOf 24 }
    have rs := block_steps gReject_checked gReject_linked rfl s (by rfl)
    have rf := block_ecall gReject_checked gReject_linked rfl s rfl
    have rr : GoodQFor Frozen.image (gReject.toState s) 1 1 Q 0 (pure (false, 0)) :=
      GoodQFor.reject rf rfl rfl
    have full := ((rr.steps rs).steps js).steps ds
    dsimp only [gReject] at full
    have hfalse : ClaudeWCT.W9.T3M.fieldOk a k = false := Bool.eq_false_iff.mpr hok
    simp only [ClaudeWCT.W9.T3M.wctStep, hfalse, Bool.not_false, ↓reduceIte, ccM_pure, hnone]
    exact full.mono (by unfold dispatchLen; split_ifs <;> omega)
      (by unfold dispatchLen; split_ifs <;> omega)
      (fun hq => ⟨hq, by unfold dispatchLen; split_ifs <;> omega⟩)
end W9Drv
end
end

section



section
namespace W9Drv
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64 W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def fPrepWords : List (BitVec 32) := [0xffce37,0xf0290193,0x40303823,0x41603c23,0x40000513,335545747,268437011,115]
def fTailWords : List (BitVec 32) := []
def gpE : E := .bin .add (.reg .x18) (.c (BitVec.ofNat 64 (2 ^ 64 - 254)))
def fPrep : Result :=
  ⟨⟨((((RegFile.init.set .x28 (.c (BitVec.ofNat 64 0xffc000))).set .x3 gpE).set .x10 (.c 1024)).set
      .x11 (.c 320)).set .x12 (.c 256),
    [(⟨none, 1048⟩, .reg .x22), (⟨none, 1040⟩, gpE)], []⟩, .c (pcOf 204), .ecall, 7, 7⟩
def fTail : Result := ⟨SymState.init, .c (pcOf 205), .fuel, 0, 0⟩
theorem fPrep_checked : rOK (symRun {} fPrepWords (pcOf 197) 8) fPrep = true := by decide +kernel
theorem fPrep_linked : sliceChecked 197 fPrepWords = true := by decide +kernel
theorem fTail_checked : rOK (symRun {} fTailWords (pcOf 205) 0) fTail = true := by decide +kernel
theorem fTail_linked : sliceChecked 205 fTailWords = true := by decide +kernel
end W9Drv
end
section
namespace W9Drv
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput M HashInput pad64 shortHash)
open SphincsSecurity (bytesLE bytesLE_length)
open W9Machine
abbrev forestIn := ClaudeWCT.WCT9.forestInput
theorem forestIn_length (index : Nat) (pairs : List (Digest × Digest)) (h : pairs.length = 9) :
    (forestIn index pairs).length = 320 := by
  simp only [forestIn, ClaudeWCT.WCT9.forestInput, List.length_append, bytesLE_length,
    SigGolfCandidate.T3.zero16, List.length_replicate, List.length_flatMap]
  simp [h]
theorem wordsOf_forestIn (index : Nat) (pairs : List (Digest × Digest)) :
    wordsOf (forestIn index pairs) =
      [0, 0, BitVec.ofNat 64 (hdr0 15 0 index 0), BitVec.ofNat 64 (hdr1 index 0)] ++
        pairs.flatMap (fun p => [dlo p.1, dhi p.1, dlo p.2, dhi p.2]) := by
  unfold forestIn ClaudeWCT.WCT9.forestInput
  rw [wordsOf_append _ _ (by simp [bytesLE_length, SigGolfCandidate.T3.zero16]), wordsOf_append _ _ (by simp [SigGolfCandidate.T3.zero16]), wordsOf_header]
  have hp : ∀ ps : List (Digest × Digest),
      wordsOf (ps.flatMap (fun p => bytesLE 16 p.1 ++ bytesLE 16 p.2)) =
        ps.flatMap (fun p => [dlo p.1, dhi p.1, dlo p.2, dhi p.2]) := by
    intro ps
    induction ps with
    | nil => rfl
    | cons p ps ih =>
      simp only [List.flatMap_cons]
      rw [wordsOf_append _ _ (by simp [bytesLE_length]),
        wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_bytesLE16, wordsOf_bytesLE16, ih]
      rfl
  rw [hp]
  rfl
theorem pad64_forestIn (index : Nat) (pairs : List (Digest × Digest)) (h : pairs.length = 9) :
    pad64 (forestIn index pairs) = forestIn index pairs := by
  simp [pad64, forestIn_length index pairs h]
theorem blocks_forestIn (index : Nat) (pairs : List (Digest × Digest)) (h : pairs.length = 9) :
    (toQ (pad64 (forestIn index pairs))).blocks = 5 := by
  rw [pad64_forestIn index pairs h,
    blocks_toQ (by rw [Aligned, forestIn_length index pairs h]; omega), forestIn_length index pairs h]
theorem hdr0_forest15 (idx : Nat) (hi : idx < 2^32) : hdr0 15 0 idx 0 = 3841 := by
  rw [hdr0_eq 15 0 idx 0 (by decide) (by decide) hi (by decide)]; norm_num
theorem hdr1_forest15 (idx : Nat) (hi : idx < 2^32) : hdr1 idx 0 = idx := by
  unfold hdr1; rw [Nat.mod_eq_of_lt hi]; simp
theorem fPrep_mem (u : MachineState) (B : Nat) (hB : B < 2^64) :
    (fPrep.toState u).getMem (BitVec.ofNat 64 B) =
      if B = 1048 then u.getReg .x22 else if B = 1040 then gpE.eval u
      else u.getMem (BitVec.ofNat 64 B) := by
  rw [Result.toState_getMem]
  change memEval u [(⟨none, BitVec.ofNat 64 1048⟩, .reg .x22), (⟨none, BitVec.ofNat 64 1040⟩, gpE)] (BitVec.ofNat 64 B) = _
  rw [memEval_cons_ofNat _ _ _ _ _ hB (by norm_num),
    memEval_cons_ofNat _ _ _ _ _ hB (by norm_num), memEval_nil]
  rfl
theorem fPrep_frame (u : MachineState) (B : Nat) (hB : B < 2^64)
    (h : B ≠ 1048 ∧ B ≠ 1040) :
    (fPrep.toState u).getMem (BitVec.ofNat 64 B) = u.getMem (BitVec.ofNat 64 B) := by
  rw [fPrep_mem u B hB, if_neg h.1, if_neg h.2]
theorem forest_words (u : MachineState) (idx : Nat) (pairs : List (Digest × Digest))
    (hlen : pairs.length = 9) (hi : idx < 2^31)
    (h22 : u.getReg .x22 = BitVec.ofNat 64 idx) (h18 : u.getReg .x18 = 0xFFF)
    (hz : u.getMem (BitVec.ofNat 64 1024) = 0 ∧ u.getMem (BitVec.ofNat 64 1032) = 0)
    (hr : ∀ i, i < 9 → DigAt u (1056+32*i) (pairs.getD i (0,0)).1 ∧
      DigAt u (1056+32*i+16) (pairs.getD i (0,0)).2) :
    (fPrep.toState u).readWords (BitVec.ofNat 64 1024) 40 =
      wordsOf (pad64 (forestIn idx pairs)) := by
  have hp : ∀ i, i < 9 → DigAt (fPrep.toState u) (1056+32*i) (pairs.getD i (0,0)).1 ∧
      DigAt (fPrep.toState u) (1056+32*i+16) (pairs.getD i (0,0)).2 := by
    intro i hi9
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (fPrep_frame u _ (by omega) (by omega)).trans (hr i hi9).1.1
    · exact (fPrep_frame u _ (by omega) (by omega)).trans (hr i hi9).1.2
    · exact (fPrep_frame u _ (by omega) (by omega)).trans (hr i hi9).2.1
    · exact (fPrep_frame u _ (by omega) (by omega)).trans (hr i hi9).2.2
  rw [readWords_ofNat _ 1024 40 (by norm_num), pad64_forestIn idx pairs hlen,
    wordsOf_forestIn, show List.range 40 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39] from rfl]
  match pairs, hlen, hp with
  | [p0,p1,p2,p3,p4,p5,p6,p7,p8], _, hp =>
    have d0 := hp 0 (by decide)
    have d1 := hp 1 (by decide)
    have d2 := hp 2 (by decide)
    have d3 := hp 3 (by decide)
    have d4 := hp 4 (by decide)
    have d5 := hp 5 (by decide)
    have d6 := hp 6 (by decide)
    have d7 := hp 7 (by decide)
    have d8 := hp 8 (by decide)
    norm_num [List.getD_cons_zero, List.getD_cons_succ] at d0 d1 d2 d3 d4 d5 d6 d7 d8
    have h16 : (fPrep.toState u).getMem (BitVec.ofNat 64 1040) =
        BitVec.ofNat 64 (hdr0 15 0 idx 0) := by
      rw [fPrep_mem u _ (by norm_num), hdr0_forest15 idx (by omega)]
      show u.getReg .x18 + BitVec.ofNat 64 (2 ^ 64 - 254) = _
      rw [h18]; rfl
    have h24 : (fPrep.toState u).getMem (BitVec.ofNat 64 1048) =
        BitVec.ofNat 64 (hdr1 idx 0) := by
      rw [fPrep_mem u _ (by norm_num), hdr1_forest15 idx (by omega)]; exact h22
    have z0 : (fPrep.toState u).getMem (BitVec.ofNat 64 1024) = 0 :=
      (fPrep_frame u _ (by norm_num) (by omega)).trans hz.1
    have z1 : (fPrep.toState u).getMem (BitVec.ofNat 64 1032) = 0 :=
      (fPrep_frame u _ (by norm_num) (by omega)).trans hz.2
    simp only [List.map_cons, List.map_nil, Nat.reduceMul, Nat.reduceAdd, d0.1.1, d0.1.2, d0.2.1, d0.2.2, d1.1.1, d1.1.2, d1.2.1, d1.2.2, d2.1.1, d2.1.2, d2.2.1, d2.2.2, d3.1.1, d3.1.2, d3.2.1, d3.2.2, d4.1.1, d4.1.2, d4.2.1, d4.2.2, d5.1.1, d5.1.2, d5.2.1, d5.2.2, d6.1.1, d6.1.2, d6.2.1, d6.2.2, d7.1.1, d7.1.2, d7.2.1, d7.2.2, d8.1.1, d8.1.2, d8.2.1, d8.2.2,
      h16, h24, z0, z1, List.flatMap_cons, List.flatMap_nil, List.cons_append,
      List.nil_append, List.append_nil]
theorem forest_good (pk : Digest) (w : WBytes) (a : HashOutput)
    (roots : List (Digest × Digest)) (u : MachineState) (N C A : Nat) (Q : Prop)
    (K : Digest → OracleComp HashSpec Obs)
    (hu : CoordPre pk w a 9 roots u)
    (hnext : ∀ root t, FtsOut ⟨pk, w, a⟩ root t →
      GoodQFor Frozen.image t N C Q A (K root)) :
    GoodQFor Frozen.image u (N + 8) (C + 47) Q (A + 47)
      (ccM (ClaudeWCT.WCT9.forestPk (a.toNat % 2 ^ 31) roots) K) := by
  have hi : idxOf a < 2 ^ 31 := Nat.mod_lt _ (by decide)
  have st1 := block_steps fPrep_checked fPrep_linked rfl u hu.pc
  have st1' : Steps Frozen.image u 7 7 (fPrep.toState u) := st1
  set s1 := fPrep.toState u with hs1
  have hf := block_ecall fPrep_checked fPrep_linked rfl u rfl
  have r1 : ∀ x, x ≠ .x3 → x ≠ .x10 → x ≠ .x11 → x ≠ .x12 → x ≠ .x28 → s1.getReg x = u.getReg x := by
    intro x h3 h10 h11 h12 h28
    rw [hs1, Result.toState_getReg]
    cases x <;> first | exact absurd rfl ‹_› | rfl
  have h5 : s1.getReg .x5 = 0 :=
    (r1 .x5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hu.glob.1 (.x5, 0) (by simp [baseK]))
  have h10 : s1.getReg .x10 = BitVec.ofNat 64 0x400 := by rw [hs1, Result.toState_getReg]; rfl
  have h11 : s1.getReg .x11 = BitVec.ofNat 64 (64 * (4 + 1)) := by rw [hs1, Result.toState_getReg]; rfl
  have h12 : s1.getReg .x12 = BitVec.ofNat 64 0x100 := by rw [hs1, Result.toState_getReg]; rfl
  have h22 : s1.getReg .x22 = BitVec.ofNat 64 (idxOf a) :=
    (r1 .x22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hu.index
  have hv : hashArgumentsValid s1 = true :=
    hashArgs_of s1 0x400 320 0x100 h10 h11 h12 (by decide) (by decide) (by norm_num) (by decide)
      (by norm_num)
  have hin : hashInput s1 = toQ (pad64 (forestIn (idxOf a) roots)) :=
    hashInput_toQ s1 _ 4 0x400 (by rw [pad64_forestIn _ _ hu.length, forestIn_length _ _ hu.length]) h10 (by decide) (by norm_num)
      h11 (by norm_num) (forest_words u (idxOf a) roots hu.length hi hu.index
        (hu.glob.1 (.x18, 0xFFF) (by simp [baseK])) hu.zero hu.pairs)
  have g1 : Glob [] w pk s1 :=
    Glob_toState hu.glob fPrep.st (fPrep.pc.eval u) (by decide) rfl
  have o1 : Orig w (fun o => o < 64 ∨ 9288 ≤ o) s1 :=
    hu.layer.frame (fun j hj _ => fPrep_frame u _ (by unfold WIT WX at *; omega)
      (by unfold WIT; omega))
  have hpost : ∀ ans : BitVec 256, GoodQFor Frozen.image (writeHash s1 ans) (N + 0) (C + 0) Q (A + 0)
      (ccM (pure (ans.extractLsb' 0 128) : M Digest) K) := by
    intro ans
    rw [ccM_pure]
    have hpc : (writeHash s1 ans).pc = pcOf 205 := by
      rw [writeHash_pc]
      show pcOf 204 + 4 = pcOf 205
      exact SigGolfCandidate.T3M.pcOf_add4 204
    have st2 := block_steps fTail_checked fTail_linked rfl (writeHash s1 ans) hpc
    have st2' : Steps Frozen.image (writeHash s1 ans) 0 0 (fTail.toState (writeHash s1 ans)) := st2
    set t := fTail.toState (writeHash s1 ans) with ht
    have mt : t.mem = (writeHash s1 ans).mem := toState_mem_nil _ _ rfl
    have et : ∀ A, t.getMem A = (writeHash s1 ans).getMem A := fun A => congrFun mt A
    have hout : FtsOut ⟨pk, w, a⟩ (ans.extractLsb' 0 128) t := by
      refine ⟨?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have gg := Glob_writeHash g1 ans 0x100 h12 (by decide)
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro p hp
          simp only [baseK, List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl
          · change (writeHash s1 ans).getReg .x5 = 0
            rw [writeHash_getReg]; exact h5
          · change (writeHash s1 ans).getReg .x18 = 4095
            rw [writeHash_getReg, r1 .x18 (by decide) (by decide) (by decide) (by decide) (by decide)]
            exact hu.glob.1 (.x18,4095) (by simp [baseK])
        · exact fun j hj => (et _).trans (gg.2.1 j hj)
        · exact ⟨(et _).trans gg.2.2.1.1, (et _).trans gg.2.2.1.2⟩
        · exact fun A hA => (et _).trans (gg.2.2.2.1 A hA)
        · change (t.getMem _).toNat / 2^32 = 0
          rw [et]; exact gg.2.2.2.2.1
        · exact gg.2.2.2.2.2.congr (fun A _ _ => et _)
      · rw [ht, Result.toState_getReg]
        show (writeHash s1 ans).getReg .x22 = _
        rw [writeHash_getReg]; exact h22
      · obtain ⟨e0, e1⟩ := writeHash_lo s1 ans 0x100 h12 (by norm_num)
        exact ⟨(et _).trans e0, (et _).trans e1⟩
      · have o2 := Orig_writeHash o1 ans 0x100 h12 (by norm_num)
        have o3 : Orig w (fun o => o < 64 ∨ 9288 ≤ o) (writeHash s1 ans) :=
          o2.mono (fun o ho => ⟨ho, Or.inr (by unfold WIT; omega)⟩)
        exact o3.frame (fun j _ _ => et _)
      · rw [ht, Result.toState_getReg]
        show (writeHash s1 ans).getReg .x12 = _
        rw [writeHash_getReg]
        exact h12
      · rw [ht, Result.toState_getReg]
        show (writeHash s1 ans).getReg .x26 = _
        rw [writeHash_getReg, r1 .x26 (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hu.heaps 6 (by decide) (by decide)
      · rw [ht, Result.toState_getReg]
        show (writeHash s1 ans).getReg .x7 = _
        rw [writeHash_getReg, r1 .x7 (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hu.stepOne
      · rw [ht, Result.toState_getReg]
        show (writeHash s1 ans).getReg .x13 = _
        rw [writeHash_getReg, r1 .x13 (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hu.stepTwo
      · rw [ht, Result.toState_getReg]
        show (writeHash s1 ans).getReg .x30 = _
        rw [writeHash_getReg, r1 .x30 (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hu.heaps 7 (by decide) (by decide)
      · rw [ht, Result.toState_getReg]
        show (writeHash s1 ans).getReg .x19 = _
        rw [writeHash_getReg, r1 .x19 (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hu.heaps 3 (by decide) (by decide)
      · rw [ht, Result.toState_getReg]
        show (writeHash s1 ans).getReg .x20 = _
        rw [writeHash_getReg, r1 .x20 (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hu.heaps 4 (by decide) (by decide)
      · rw [ht, Result.toState_getReg]
        show (writeHash s1 ans).getReg .x21 = _
        rw [writeHash_getReg, r1 .x21 (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hu.heaps 5 (by decide) (by decide)
      · rw [ht, Result.toState_getReg]
        show (writeHash s1 ans).getReg .x6 = _
        rw [writeHash_getReg, r1 .x6 (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hu.coordStep
      · rw [ht, Result.toState_getReg]
        show (writeHash s1 ans).getReg .x28 = _
        rw [writeHash_getReg, hs1, Result.toState_getReg]
        rfl
      · intro k hk
        rw [et, writeHash_frame s1 ans 0x100 (TOPLOAD + 8 * k) h12
          (by unfold TOPLOAD; omega) (by norm_num) (Or.inr (by unfold TOPLOAD; omega))]
        exact (fPrep_frame u _ (by unfold TOPLOAD; omega) (by unfold TOPLOAD; omega)).trans
          (hu.bank.top k hk)
      · rw [et, writeHash_frame s1 ans 0x100 (TOPLOAD - 8) h12
          (by unfold TOPLOAD; omega) (by norm_num) (Or.inr (by unfold TOPLOAD; omega))]
        exact (fPrep_frame u _ (by unfold TOPLOAD; omega) (by unfold TOPLOAD; omega)).trans
          hu.bank.top8
    exact (hnext _ t hout).steps st2'
  have hq := GoodQFor.shortHash_bind (f := fun d : Digest => (pure d : M Digest)) (K := K)
    hf h5 hv hin hpost
  rw [blocks_forestIn _ _ hu.length, bind_pure] at hq
  have := hq.steps st1'
  change GoodQFor Frozen.image u (N+8) (C+47) Q (A+47) (ccM (shortHash (forestIn (idxOf a) roots)) K)
  exact this.mono (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
#print axioms forest_good
end W9Drv
end
end

section




namespace W9Drv
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open W9Machine
def FtsGoodByCost (acceptCost : HashOutput → Nat) : Prop :=
  ∀ (pk : Digest) (w : WBytes) (a : HashOutput) (u : MachineState)
    (N C A : Nat) (Q : Prop) (K : Option Digest → OracleComp HashSpec Obs),
    GatePre pk w a u → K none = pure (false, 0) →
    (∀ root t, FtsOut ⟨pk,w,a⟩ root t →
      GoodQFor Frozen.image t N C Q A (K (some root))) →
    GoodQFor Frozen.image u (N+2023) (C+2023) Q (A+acceptCost a)
      (ccM (if ClaudeWCT.W9.T3M.gateOk a then ClaudeWCT.W9.T3M.wctP w a else pure none) K)
def ftsAcceptCost (a : HashOutput) : Nat := 1117 + ClaudeWCT.WCT9.jointCost a
end W9Drv
end

section



section
namespace W9Drv
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput M)
open W9Machine
def finishFts (a : HashOutput) (state : Option (List (Digest × Digest))) : M (Option Digest) :=
  match state with
  | none => pure none
  | some roots => some <$> ClaudeWCT.WCT9.forestPk (idxOf a) roots
def coordsCost (ks : List (Fin 9)) : Nat :=
  (ks.map (fun k => if k.val = 0 then 204 else if k.val = 7 then 205 else 206)).sum
def coordsAccept (a : HashOutput) (ks : List (Fin 9)) : Nat :=
  (ks.map (fun k => (if k.val = 0 then 115 else if k.val = 7 then 116 else 117) + N600.rankCost (ClaudeWCT.WCT9.rank a k))).sum
theorem fold_none (w : WBytes) (a : HashOutput) (ks : List (Fin 9)) :
    ks.foldlM (ClaudeWCT.W9.T3M.wctStep w a) none = pure none := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simpa only [List.foldlM_cons, ClaudeWCT.W9.T3M.wctStep, pure_bind] using ih
theorem coordinates_good (chains : N600.AllGood Frozen.layout) (pk : Digest) (w : WBytes) (a : HashOutput)
    (ks : List (Fin 9)) (n : Nat) (roots : List (Digest × Digest)) (u : MachineState)
    (N C A : Nat) (Q : Prop) (K : Option Digest → OracleComp HashSpec Obs)
    (horder : ks.map Fin.val = List.range' n ks.length) (hend : n + ks.length = 9)
    (hu : CoordPre pk w a n roots u) (hnone : K none = pure (false, 0))
    (hnext : ∀ root t, FtsOut ⟨pk,w,a⟩ root t →
      GoodQFor Frozen.image t N C Q A (K (some root))) :
    GoodQFor Frozen.image u (N + (coordsCost ks + 47)) (C + (coordsCost ks + 47)) Q
      (A + (coordsAccept a ks + 47))
      (ccM (ks.foldlM (ClaudeWCT.W9.T3M.wctStep w a) (some roots) >>= finishFts a) K) := by
  induction ks generalizing n roots u with
  | nil =>
    have hn : n = 9 := by simpa using hend
    subst n
    simp only [List.foldlM_nil, pure_bind, finishFts]
    have hf := forest_good pk w a roots u N C A Q (fun root => K (some root)) hu hnext
    rw [map_eq_bind_pure_comp, ccM_bind]
    simp only [Function.comp_apply, ccM_pure]
    exact hf.mono (by change N + 8 ≤ N + 47; omega) (by rfl) (fun hq => ⟨hq, by rfl⟩)
  | cons k ks ih =>
    simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at horder
    obtain ⟨hn, ht⟩ := horder
    subst n
    let K' : Option (List (Digest × Digest)) → OracleComp HashSpec Obs := fun state =>
      ccM (ks.foldlM (ClaudeWCT.W9.T3M.wctStep w a) state >>= finishFts a) K
    have hkNone : K' none = pure (false, 0) := by
      simp only [K', fold_none, pure_bind, finishFts, ccM_pure, hnone]
    have hstep := coord_good chains pk w a k roots u (N + (coordsCost ks + 47))
      (C + (coordsCost ks + 47)) (A + (coordsAccept a ks + 47)) Q K' hu hkNone
      (fun root t hh => ih (k.val + 1) (roots ++ [root]) t ht (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hend) hh)
    simp only [List.foldlM_cons, bind_assoc, ccM_bind]
    convert hstep using 1 <;> simp [coordsCost, coordsAccept, Nat.add_left_comm, Nat.add_comm,
      K', ccM_bind]
theorem coordsAccept_all (a : HashOutput) :
    coordsAccept a (List.finRange 9) = 1050 + ClaudeWCT.WCT9.jointCost a := by
  unfold coordsAccept
  rw [List.sum_map_add]
  have hfixed : ((List.finRange 9).map (fun k => if k.val = 0 then 115 else if k.val = 7 then 116 else 117)).sum = 1050 := by decide
  rw [hfixed]
  congr 1
  simp only [ClaudeWCT.WCT9.jointCost, (show N600.rankCost = ClaudeWCT.WCT9.routineCost from N600.rankCost_eq_c1)]
theorem fts_good (chains : N600.AllGood Frozen.layout) : FtsGoodByCost ftsAcceptCost := by
  intro pk w a u N C A Q K hu hnone hnext
  let KG : Bool → OracleComp HashSpec Obs := fun b =>
    if b then ccM (ClaudeWCT.W9.T3M.wctP w a) K else K none
  have hg := gate_good pk w a u (N + 1898) (C + 1898) (A + (1097 + ClaudeWCT.WCT9.jointCost a)) Q KG hu
    (by simpa only [KG, Bool.false_eq_true, ↓reduceIte] using hnone)
    (fun t ht => by
      have hc := coordinates_good chains pk w a (List.finRange 9) 0 [] t N C A Q K
        (by decide)
        (by simp) ht hnone hnext
      rw [show coordsCost (List.finRange 9) + 47 = 1898 by decide,
        show coordsAccept a (List.finRange 9) + 47 = 1097 + ClaudeWCT.WCT9.jointCost a by
          rw [coordsAccept_all]; omega] at hc
      apply hc.congr
      change ccM (_ >>= finishFts a) K = ccM (ClaudeWCT.W9.T3M.wctP w a) K
      apply congrArg (fun p : M (Option Digest) => ccM p K)
      unfold ClaudeWCT.W9.T3M.wctP
      apply congrArg (fun f : Option (List (Digest × Digest)) → M (Option Digest) =>
        (List.finRange 9).foldlM (ClaudeWCT.W9.T3M.wctStep w a) (some []) >>= f)
      funext state
      cases state <;> rfl)
  change GoodQFor Frozen.image u (N + 1918) (C + 1918) Q (A + (1097 + ClaudeWCT.WCT9.jointCost a) + 20)
    (KG (ClaudeWCT.W9.T3M.gateOk a)) at hg
  apply (hg.mono (by omega) (by omega) (fun hq => ⟨hq, by simp only [ftsAcceptCost]; omega⟩)).congr
  cases ClaudeWCT.W9.T3M.gateOk a <;> simp [KG, ccM_pure]
#print axioms fts_good
end W9Drv
end
end
