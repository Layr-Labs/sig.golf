import SigGolfCandidate.T3M.Verify.Nonbinary.InlinePrefixMachine
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsDispatchCtx

/- Connected first51 source induction and genuine local dispatch on the inline
   image. Attributed finite proofs are adapted from ChainsDispatchCtx/Fts;
   only actual finite CodeAt laws appear as hardware hypotheses. -/
namespace SigGolfCandidate.T3M.Nonbinary.NCtx
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Nonbinary SigGolfCandidate.T3
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

theorem prefix_dispatch_step {p q : Nat} (hq : q<17) (hp : p<251927)
    (hrun : vrun p 5=some (dispatchR q)) (hwin : CodeAt InlineTail.image (pcOf p) ((lcode p).take 5)) (s : MachineState) (v : Digest)
    (hpc : s.pc=pcOf p) (h16 : s.getReg .x16=v.extractLsb' 0 64)
    (h17 : s.getReg .x17=v.extractLsb' 63 64)
    (h24 : s.getReg .x6=130048#64) (h15 : s.getReg .x15=712704#64) :
    ∃t, Steps InlineTail.image s 4 4 t ∧ t.pc=pcOf (entW q (Search.topRank v q)) ∧
      RegsExcept s t [.x14] ∧ Frame s t (fun _ => False) := by
  have hW : s.getReg (if q<9 then .x16 else .x17)=sourceWord v q := by
    unfold sourceWord
    split_ifs <;> assumption
  have hb : sourceBit q<64 := by unfold sourceBit;split_ifs <;> omega
  refine ⟨(dispatchR q).toState s,prefix_window_steps hrun hwin s hpc (by simp [dispatchR]),?_,?_,?_⟩
  · change (((shift10 (if q<9 then .x16 else .x17) (sourceBit q)).eval s &&& s.getReg .x6)+
      s.getReg .x15+(BitVec.ofNat 64 (32*q)+18446744073709549984#64)) &&& ~~~1#64=pcOf (entW q (Search.topRank v q))
    rw [h24,h15,dispatch_window,shift10_eval s _ _ hW _ hb,dispatch_target _ _ q hb hq,source_field v q hq]
  · intro r hr
    rw [Result.toState_getReg]
    simp only [dispatchR]
    rw [RegFile.get_set_ne _ _ (show r≠.x14 by simpa using hr),RegFile.init_get_eval]
  · intro A _ _
    simp [dispatchR,rv_simp]

theorem prefix_tail_dispatch_step {p : Nat} (hp : p<251927)
    (hrun : vrun p 5=some tailDispatchR) (hwin : CodeAt InlineTail.image (pcOf p) ((lcode p).take 5)) (s : MachineState) (k : Nat) (hk : k<64)
    (hpc : s.pc=pcOf p) (h29 : s.getReg .x29=BitVec.ofNat 64 k)
    (h15 : s.getReg .x15=712704#64) :
    ∃t, Steps InlineTail.image s 3 3 t ∧ t.pc=pcOf (entW 17 k) ∧
      RegsExcept s t [.x14,.x15] ∧ Frame s t (fun _ => False) ∧ t.getReg .x15 = 712704#64 := by
  refine ⟨tailDispatchR.toState s,prefix_window_steps hrun hwin s hpc
    (by simp [tailDispatchR,TailDispatch.dispatchR]),?_,?_,?_,?_⟩
  · simp only [Result.toState_pc,tailDispatchR,TailDispatch.dispatchR,E.eval,BinOp.eval,h29,h15]
    change (((BitVec.ofNat 64 k <<< 10)+712704#64+18446744073709550752#64) &&& ~~~1#64) = _
    simpa only [TailDispatch.pcOf,TailDispatch.armPC,entW,pcOf,if_false,Nat.reduceLT] using
      TailDispatch.dispatch_target k hk
  · intro r hr
    rw [Result.toState_getReg]
    simp only [tailDispatchR,TailDispatch.dispatchR]
    rw [RegFile.get_set_ne _ _ (ne_of_not_mem hr (by simp)),RegFile.init_get_eval]
  · intro A _ _
    simp [tailDispatchR,TailDispatch.dispatchR,rv_simp]
  · rw [Result.toState_getReg]
    simp only [tailDispatchR,TailDispatch.dispatchR]
    rw [RegFile.get_set_ne _ _ (by decide),RegFile.init_get_eval,h15]

theorem prefix_end_dispatch (c : NCtx) (hw : c.PrefixWindows) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState} {v : Digest}
    (he : Encoded v s0) (hf : c.Fit v) (hv : topRanksValid v=true)
    (q : Nat) (hq : q<16) (acc : List Digest) (s : MachineState)
    (hs : c.EndInv s0 (3*q+2) acc s) :
    ∃t,Steps InlineTail.image s 4 4 t ∧ c.ChainIn s0 (3*(q+1)) acc t := by
  obtain ⟨⟨hR,hF,hS⟩,hlen,hpc⟩ := hs
  have hr := c.dispatch_at hds q (by omega)
  rw [if_pos hq] at hr
  have hbound : c.endPc (3*q+2)<251927 := by
    have := c.qX_lt (3*q+2)
    simpa only [endPc,show (3*q+2)%3=2 by omega,if_false,Nat.reduceEqDiff] using (show c.qX (3*q+2)<251927 by omega)
  obtain ⟨t,st,pt,rt,ft⟩ := prefix_dispatch_step (by omega) hbound hr (by
      simpa only [endPc,show (3*q+2)%3=2 by omega,if_false,Nat.reduceEqDiff] using hw.dispatch (3*q+2) (by omega) 5 (by decide)) s v hpc
    ((hR _ (by decide)).trans he.lo) ((hR _ (by decide)).trans he.hi)
    ((hR _ (by decide)).trans he.mask) ((hR _ (by decide)).trans he.table)
  refine ⟨t,st,⟨⟨fun x hx => ?_,(hF.trans ft).mono (by intro A hA h;rcases h with h|h;simpa only [show 3*q+2+1=3*(q+1) by omega] using h;contradiction),fun j hj => ?_⟩,by omega,?_⟩⟩
  · rw [rt.get (by intro h;simp only [List.mem_singleton] at h;subst x;exact hx (by decide))]
    exact hR x hx
  · exact (hS j hj).frame ft (by have := slot_props j (by omega);omega) (by simp) (by simp)
  · rw [pt]
    unfold startPc
    rw [if_pos (show 3*(q+1)%3=0 by omega),show 3*(q+1)/3=q+1 by omega,c.fit_rank hf hv (q+1) (by omega)]

theorem prefix_end_tail (c : NCtx) (hw : c.PrefixWindows) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState} {v : Digest}
    (he : Encoded v s0) (hf : c.Fit v) (hv : v.toNat<2^125)
    (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 50 acc s) :
    ∃t,Steps InlineTail.image s 3 3 t ∧ c.ChainIn (tailInitial s0 t) 51 acc t ∧ t.getReg .x15 = 712704#64 := by
  obtain ⟨⟨hR,hF,hS⟩,hlen,hpc⟩ := hs
  have hr := c.dispatch_at hds 16 (by decide)
  norm_num at hr
  have hbound : c.endPc 50<251927 := by
    have := c.qX_lt 50
    simpa only [endPc,Nat.reduceMod,if_false,Nat.reduceEqDiff] using (show c.qX 50<251927 by omega)
  obtain ⟨t,st,pt,rt,ft,r15⟩ := prefix_tail_dispatch_step hbound hr (by
      simpa only [endPc,Nat.reduceMod,if_false,Nat.reduceEqDiff] using hw.dispatch 50 (by decide) 5 (by decide)) s (v.toNat/2^119) (by omega) hpc
    ((hR _ (by decide)).trans he.tail) ((hR _ (by decide)).trans he.table)
  refine ⟨t,st,⟨⟨fun x hx => ?_,?_,fun j hj => ?_⟩,by omega,?_⟩,r15⟩
  · by_cases hx15 : x=.x15
    · subst x;rw [tailInitial_15]
    · rw [tailInitial_regs _ _ _ hx15,rt.get (by simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,not_or];exact ⟨fun h => hx (by rw [h];decide),hx15⟩)]
      exact hR x hx
  · intro A hA hn
    rw [tailInitial_mem]
    exact ft.get hA (by simp) |>.trans (hF.get hA hn)
  · exact (hS j hj).frame ft (by have := slot_props j (by omega);omega) (by simp) (by simp)
  · rw [pt]
    change pcOf (entW 17 (v.toNat/2^119))=pcOf (entW 17 (c.kOf 17))
    rw [c.fit_tail hf hv]

theorem prefix_group_good (c : NCtx) (hw : c.PrefixWindows) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0)
    (q : Nat) (hq : q<17) (K : List Digest → OracleComp Legacy.HashSpec InlineTail.Judg.Obs)
    (N C A : Nat) (Q : Prop)
    (hK : ∀ ends t,c.EndInv s0 (3*q+2) ends t → InlineTail.Judg.GoodQ InlineTail.image t N C Q A (K ends)) :
    ∀ k i, 3*q ≤ i → i+k = 3*q+3 → 0 < k → ∀ acc s, c.ChainIn s0 i acc s →
      InlineTail.Judg.GoodQ InlineTail.image s (N+40*k) (C+c.chainsCost i k) Q (A+c.chainsCost i k)
        (InlineTail.Judg.ccM ((List.range' i k).foldlM c.chainF acc) K) := by
  intro k
  induction k with
  | zero => intro i _ _ h;omega
  | succ k ih =>
    intro i hi hik _ acc s hs
    rw [List.range'_succ,List.foldlM_cons]
    simp only [chainF,bind_assoc,pure_bind,InlineTail.Judg.ccM_bind]
    have H := c.prefix_chain_good hw hc hds hk h0 i (by omega) (by omega) acc
      (fun ends => InlineTail.Judg.ccM ((List.range' (i+1) k).foldlM c.chainF ends) K)
      (N+40*k) (C+c.chainsCost (i+1) k) (A+c.chainsCost (i+1) k) Q
      (fun v t ht => by
        by_cases hk0 : k=0
        · subst hk0
          have he : i=3*q+2 := by omega
          rw [he] at ht
          simpa [chainsCost] using hK _ t ht
        · have ht' : c.ChainIn s0 (i+1) (acc++[v]) t := c.next_inline s0 i (by omega) (by omega) (acc++[v]) t ht
          exact ih (i+1) (by omega) (by omega) (by omega) (acc++[v]) t ht') s hs
    refine H.mono (by omega) ?_ (fun hq => ⟨hq,?_⟩)
    · simp only [chainsCost,List.range'_succ,List.map_cons,List.sum_cons];omega
    · simp only [chainsCost,List.range'_succ,List.map_cons,List.sum_cons];omega

theorem prefix_chainsCost_add (c : NCtx) (i n k : Nat) :
    c.chainsCost i (n+k)=c.chainsCost i n+c.chainsCost (i+n) k := by
  unfold chainsCost
  rw [← List.range'_append_1,List.map_append,List.sum_append]

theorem prefix_fiftyone_good (c : NCtx) (hw : c.PrefixWindows) (hc : c.ok) {s0 : MachineState} {v : Digest}
    (hk : ∀ p ∈ c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0)
    (he : Encoded v s0) (hf : c.Fit v) (hv : topRanksValid v=true)
    (K : List Digest → OracleComp Legacy.HashSpec InlineTail.Judg.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ acc t,c.EndInv s0 50 acc t → InlineTail.Judg.GoodQ InlineTail.image t N C Q A (K acc)) :
    ∀ n q, n+q=17 → 0<n → ∀ acc s,c.ChainIn s0 (3*q) acc s →
      InlineTail.Judg.GoodQ InlineTail.image s (N+124*n) (C+c.chainsCost (3*q) (3*n)+4*(n-1)) Q
        (A+c.chainsCost (3*q) (3*n)+4*(n-1))
        (InlineTail.Judg.ccM ((List.range' (3*q) (3*n)).foldlM c.chainF acc) K) := by
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
      have H := c.prefix_group_good hw hc hd hk h0 16 (by decide) K N C A Q hK 3 48 (by decide) (by decide) (by decide) acc s hs
      exact H.mono (by omega) (by simp) (fun h => ⟨h,by simp⟩)
    · rw [show 3*(n+1)=3+3*n by omega,← List.range'_append_1,List.foldlM_append,InlineTail.Judg.ccM_bind]
      have H := c.prefix_group_good hw hc hd hk h0 q (by omega)
        (fun ends => InlineTail.Judg.ccM ((List.range' (3*q+3) (3*n)).foldlM c.chainF ends) K)
        (N+124*n+4) (C+c.chainsCost (3*(q+1)) (3*n)+4*(n-1)+4)
        (A+c.chainsCost (3*(q+1)) (3*n)+4*(n-1)+4) Q
        (fun ends t ht => by
          obtain ⟨u,st,hu⟩ := c.prefix_end_dispatch hw hc hd he hf hv q (by omega) ends t ht
          have H := ih (q+1) (by omega) (by omega) ends u hu
          rw [show 3*(q+1)=3*q+3 by omega] at H
          exact InlineTail.Judg.GoodQ.steps st H)
        3 (3*q) (le_refl _) (by omega) (by decide) acc s hs
      have ec := c.prefix_chainsCost_add (3*q) 3 (3*n)
      rw [show 3*q+3=3*(q+1) by omega] at ec
      exact H.mono (by omega) (by omega) (fun h => ⟨h,by omega⟩)

#print axioms prefix_fiftyone_good
#print axioms prefix_end_tail
end SigGolfCandidate.T3M.Nonbinary.NCtx
