import SigGolfCandidate.T3M.Search.TopWindow
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsGoodOne
import SigGolfCandidate.T3M.Verify.LayerSem

section



namespace SigGolfCandidate.T3M.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
theorem land_mask10 (n k : Nat) (hk : k≤7) :
    n &&& (1024*(2^k-1))=1024*(n/1024%2^k) := by
  apply Nat.eq_of_testBit_eq;intro j
  rw [Nat.testBit_and,show (1024 : Nat)=2^10 by norm_num,Nat.testBit_two_pow_mul,Nat.testBit_two_pow_mul,
    Nat.testBit_two_pow_sub_one,Nat.testBit_mod_two_pow,Nat.testBit_div_two_pow]
  by_cases h : 10≤j
  · simp only [h,decide_true,Bool.true_and,show j-10+10=j by omega]
    by_cases hj : j-10<k <;> simp [hj]
  · simp [h]
theorem field_shl10 (W s k : Nat) (hs : s≤10) (hk : k≤7) :
    W*2^s%2^64/1024%2^k=W/2^(10-s)%2^k := by
  apply Nat.eq_of_testBit_eq;intro j
  rw [Nat.testBit_mod_two_pow,Nat.testBit_mod_two_pow,show (1024 : Nat)=2^10 by norm_num,
    Nat.testBit_div_two_pow,Nat.testBit_div_two_pow,Nat.testBit_mod_two_pow,Nat.testBit_mul_two_pow]
  by_cases hj : j<k
  · simp only [hj,decide_true,Bool.true_and,show j+10<64 by omega,show s≤j+10 by omega]
    rw [show j+10-s=j+(10-s) by omega]
  · simp [hj]
def shiftWord10 (W : Word) (b : Nat) : Word := if b<10 then W<<<(10-b) else W>>>(b-10)
theorem word_mask10 (W : Word) (b : Nat) (hb : b<64) :
    shiftWord10 W b &&& 130048#64=BitVec.ofNat 64 (1024*(W.toNat/2^b%128)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and,show (130048#64).toNat=1024*(2^7-1) by rfl,land_mask10 _ _ (by decide)]
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show 1024*(W.toNat/2^b%128)<2^64 by omega)]
  apply congrArg (fun x => 1024*x)
  unfold shiftWord10
  split_ifs with h
  · simp only [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq]
    rw [field_shl10 _ _ _ (by omega) (by decide),show 10-(10-b)=b by omega]
    rfl
  · simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
    rw [Nat.div_div_eq_div_mul,
      show 2^(b-10)*1024=2^b by rw [show (1024 : Nat)=2^10 by rfl,←pow_add];congr 1;omega]
    rfl
theorem shift10_eval (s : MachineState) (w : Reg) (W : Word) (hw : s.getReg w=W)
    (b : Nat) (hb : b<64) : (shift10 w b).eval s=shiftWord10 W b := by
  unfold shift10 shiftWord10
  split_ifs with h <;> simp only [E.eval,BinOp.eval,hw,BitVec.toNat_ofNat]
  · rw [Nat.mod_eq_of_lt (show 10-b<2^64 by omega),Nat.mod_eq_of_lt (show 10-b<64 by omega)]
  · rw [Nat.mod_eq_of_lt (show b-10<2^64 by omega),Nat.mod_eq_of_lt (show b-10<64 by omega)]
theorem dispatch_window (X : Word) (q : Nat) :
    X + 712704#64 + (BitVec.ofNat 64 (4*entOff q) + 18446744073709549984#64) =
      X + pcOf 176744 + BitVec.ofNat 64 (4*entOff q) := by
  calc X + 712704#64 + (BitVec.ofNat 64 (4*entOff q) + 18446744073709549984#64) =
      X + (712704#64 + 18446744073709549984#64) + BitVec.ofNat 64 (4*entOff q) := by ac_rfl
    _ = _ := by rfl
theorem entOff_le (q : Nat) (hq : q<17) : entOff q ≤ 194 := by unfold entOff; split_ifs <;> omega
theorem dispatch_target (W : Word) (b q : Nat) (hb : b<64) (hq : q<17) :
    ((shiftWord10 W b &&& 130048#64)+pcOf 176744+BitVec.ofNat 64 (4*entOff q)) &&& ~~~1#64 =
      pcOf (entW q (W.toNat/2^b%128)) := by
  have he := entOff_le q hq
  rw [word_mask10 W b hb,ofNat_add_ofNat,ofNat_add_ofNat,
    even_andNot1' _ (by omega)]
  unfold pcOf entW
  apply congrArg (BitVec.ofNat 64)
  omega
theorem prologue_target (v : Digest) :
    (((v.extractLsb' 0 64 <<< 10) &&& 130048#64)+pcOf 176744) &&& ~~~1#64 =
      pcOf (176744+256*(v.toNat%128)) := by
  have h := dispatch_target (v.extractLsb' 0 64) 0 0 (by decide) (by decide)
  simpa [shiftWord10,entW,entOff,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,
    Nat.mod_mod_of_dvd _ (show 128∣2^64 by decide)] using h
end SigGolfCandidate.T3M.Nonbinary
end

section




section
namespace SigGolfCandidate.T3M.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
def sourceWord (v : Digest) (q : Nat) : Word := if q<9 then v.extractLsb' 0 64 else v.extractLsb' 63 64
def sourceBit (q : Nat) : Nat := if q<9 then 7*q else 7*(q-9)
theorem extract_field (v : Digest) (a b : Nat) (h : b+7≤64) :
    (v.extractLsb' a 64).toNat/2^b%128=v.toNat/2^(a+b)%128 := by
  have hr := Search.ext_shr_mask v a b 7 h
  have hl : (v.extractLsb' a 64 >>> b) &&& 127#64=
      BitVec.ofNat 64 ((v.extractLsb' a 64).toNat/2^b%128) := by
    have he : v.extractLsb' a 64=BitVec.ofNat 64 (v.extractLsb' a 64).toNat := by
      apply BitVec.eq_of_toNat_eq; simp
    conv_lhs => rw [he]
    rw [ofNat_shr _ _ (v.extractLsb' a 64).isLt,Search.ofNat_and127]
  have hh := hl.symm.trans hr
  exact (ofNat_inj (by omega) (by omega)).mp hh
theorem source_field (v : Digest) (q : Nat) (hq : q<17) :
    (sourceWord v q).toNat/2^(sourceBit q)%128=Search.topRank v q := by
  unfold sourceWord sourceBit Search.topRank
  split_ifs with h
  · simpa using extract_field v 0 (7*q) (by omega)
  · rw [extract_field v 63 (7*(q-9)) (by omega),show 63+7*(q-9)=7*q by omega]
theorem dispatch_step {p q : Nat} (hq : q<17) (hp : p<251927)
    (hrun : vrun p 5=some (dispatchR q)) (s : MachineState) (v : Digest)
    (hpc : s.pc=pcOf p) (h16 : s.getReg .x16=v.extractLsb' 0 64)
    (h17 : s.getReg .x17=v.extractLsb' 63 64)
    (h24 : s.getReg .x6=130048#64) (h15 : s.getReg .x15=712704#64) :
    ∃t, Steps Images.verifyImage s 4 4 t ∧ t.pc=pcOf (entW q (Search.topRank v q)) ∧
      RegsExcept s t [.x14] ∧ Frame s t (fun _ => False) := by
  have hW : s.getReg (if q<9 then .x16 else .x17)=sourceWord v q := by
    unfold sourceWord
    split_ifs <;> assumption
  have hb : sourceBit q<64 := by unfold sourceBit;split_ifs <;> omega
  refine ⟨(dispatchR q).toState s,piece_steps45 hrun hp s hpc (by simp [dispatchR]),?_,?_,?_⟩
  · change (((shift10 (if q<9 then .x16 else .x17) (sourceBit q)).eval s &&& s.getReg .x6)+
      s.getReg .x15+(BitVec.ofNat 64 (4*entOff q)+18446744073709549984#64)) &&& ~~~1#64=pcOf (entW q (Search.topRank v q))
    rw [h24,h15,dispatch_window,shift10_eval s _ _ hW _ hb,dispatch_target _ _ q hb hq,source_field v q hq]
  · intro r hr
    rw [Result.toState_getReg]
    simp only [dispatchR]
    rw [RegFile.get_set_ne _ _ (show r≠.x14 by simpa using hr),RegFile.init_get_eval]
  · intro A _ _
    simp [dispatchR,rv_simp]
theorem tail_dispatch_step {p : Nat} (hp : p<251927)
    (hrun : vrun p 5=some tailDispatchR) (s : MachineState) (k : Nat) (hk : k<64)
    (hpc : s.pc=pcOf p) (h29 : s.getReg .x29=BitVec.ofNat 64 k)
    (h15 : s.getReg .x15=712704#64) :
    ∃t, Steps Images.verifyImage s 3 3 t ∧ t.pc=pcOf (entW 17 k) ∧
      RegsExcept s t [.x14,.x15] ∧ Frame s t (fun _ => False) ∧ t.getReg .x15 = 712704#64 := by
  refine ⟨tailDispatchR.toState s,piece_steps45 hrun hp s hpc
    (by simp [tailDispatchR,TailDispatch.dispatchR]),?_,?_,?_,?_⟩
  · simp only [Result.toState_pc,tailDispatchR,TailDispatch.dispatchR,E.eval,BinOp.eval,h29,h15]
    change (((BitVec.ofNat 64 k <<< 10)+712704#64+18446744073709550924#64) &&& ~~~1#64) = _
    have he : entW 17 k=TailDispatch.armPC k := by unfold entW entOff TailDispatch.armPC; simp; omega
    rw [he]
    exact TailDispatch.dispatch_target k hk
  · intro r hr
    rw [Result.toState_getReg]
    simp only [tailDispatchR,TailDispatch.dispatchR]
    rw [RegFile.get_set_ne _ _ (ne_of_not_mem hr (by simp)),RegFile.init_get_eval]
  · intro A _ _
    simp [tailDispatchR,TailDispatch.dispatchR,rv_simp]
  · rw [Result.toState_getReg]
    simp only [tailDispatchR,TailDispatch.dispatchR]
    rw [RegFile.get_set_ne _ _ (by decide),RegFile.init_get_eval,h15]
#print axioms dispatch_step
#print axioms tail_dispatch_step
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary.NCtx
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Nonbinary SigGolfCandidate.T3
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
theorem next_inline (c : NCtx) (s0 : MachineState) (i : Nat) (hi : i<54) (h2 : i%3≠2)
    (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 i acc s) :
    c.ChainIn s0 (i+1) acc s := by
  obtain ⟨hB,hlen,hpc⟩ := hs
  refine ⟨hB,hlen,?_⟩
  rw [hpc]
  unfold endPc startPc
  have e : (i+1)/3=i/3 := by omega
  by_cases h0 : i%3=0
  · rw [if_pos h0,if_neg (show (i+1)%3≠0 by omega),if_pos (show (i+1)%3=1 by omega)]
    unfold qB;rw [e]
  · rw [if_neg h0,if_pos (show i%3=1 by omega),if_neg (show (i+1)%3≠0 by omega),
      if_neg (show (i+1)%3≠1 by omega)]
    unfold qC;rw [e]
def chainF (c : NCtx) (ends : List Digest) (i : Nat) : M (List Digest) := do
  let v ← chainP 0 c.tree c.leaf i (c.dig i) (topMax i-c.dig i) (c.pad0 i) (c.pad1 i) (c.padHeader i) (c.val i)
  pure (ends++[v])
def chainsCost (c : NCtx) (i k : Nat) : Nat :=
  ((List.range' i k).map fun j => chainCost j (c.dig j)).sum
theorem group_good (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0)
    (q : Nat) (hq : q<18) (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs)
    (N C A : Nat) (Q : Prop)
    (hK : ∀ ends t,c.EndInv s0 (3*q+2) ends t → Verify.GoodQ t N C Q A (K ends)) :
    ∀ k i, 3*q ≤ i → i+k = 3*q+3 → 0 < k → ∀ acc s, c.ChainIn s0 i acc s →
      Verify.GoodQ s (N+40*k) (C+c.chainsCost i k) Q (A+c.chainsCost i k)
        (Verify.ccM ((List.range' i k).foldlM c.chainF acc) K) := by
  intro k
  induction k with
  | zero => intro i _ _ h;omega
  | succ k ih =>
    intro i hi hik _ acc s hs
    rw [List.range'_succ,List.foldlM_cons]
    simp only [chainF,bind_assoc,pure_bind,Verify.ccM_bind]
    have H := c.chain_good hc hds hk h0 i (by omega) acc
      (fun ends => Verify.ccM ((List.range' (i+1) k).foldlM c.chainF ends) K)
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
end SigGolfCandidate.T3M.Nonbinary.NCtx
end
section
namespace SigGolfCandidate.T3M.Nonbinary.NCtx
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Nonbinary SigGolfCandidate.T3
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
def Fit (c : NCtx) (v : Digest) : Prop := ∀i,i<54 → c.dig i=coreDigit 0 v i
theorem fit_digits (c : NCtx) {v : Digest} (hf : c.Fit v) : c.DigitsOk := by
  intro i hi
  rw [hf i hi]
  have h := T3.Nonbinary.coreDigit_le 0 v i
  simpa [maxDigit,topMax,mx,show (i/3<17)↔i<51 by omega] using h
theorem fit_rank (c : NCtx) {v : Digest} (hf : c.Fit v) (hv : topRanksValid v=true)
    (q : Nat) (hq : q<17) : c.kOf q=Search.topRank v q := by
  have hr := T3.Nonbinary.top_rank_lt v hv q hq
  unfold kOf
  rw [hf (3*q) (by omega),hf (3*q+1) (by omega),hf (3*q+2) (by omega)]
  have h0 := T3.Nonbinary.top_core_triple v q 0 hq (by decide)
  have h1 := T3.Nonbinary.top_core_triple v q 1 hq (by decide)
  have h2 := T3.Nonbinary.top_core_triple v q 2 hq (by decide)
  simp only [Nat.add_zero] at h0
  rw [h0,h1,h2]
  simp only [mx,if_pos hq,Nat.reduceAdd,Nat.reducePow,Nat.div_one]
  unfold Search.topRank
  omega
theorem fit_rank' (c : NCtx) {v : Digest} (hf : c.Fit v) (q : Nat) (hq : q<17) (hv : Search.topRank v q<125) :
    c.kOf q=Search.topRank v q := by
  unfold kOf
  rw [hf (3*q) (by omega),hf (3*q+1) (by omega),hf (3*q+2) (by omega)]
  have h0 := T3.Nonbinary.top_core_triple v q 0 hq (by decide)
  have h1 := T3.Nonbinary.top_core_triple v q 1 hq (by decide)
  have h2 := T3.Nonbinary.top_core_triple v q 2 hq (by decide)
  simp only [Nat.add_zero] at h0
  rw [h0,h1,h2]
  simp only [mx,if_pos hq,Nat.reduceAdd,Nat.reducePow,Nat.div_one]
  unfold Search.topRank at hv ⊢
  omega
theorem fit_tail (c : NCtx) {v : Digest} (hf : c.Fit v) (hv : v.toNat<2^125) :
    c.kOf 17=v.toNat/2^119 := by
  unfold kOf
  rw [hf 51 (by decide),hf 52 (by decide),hf 53 (by decide)]
  norm_num [mx,coreDigit]
  omega
theorem decode_facts {v : Digest} {ds : List Nat} (h : decode 0 v=some ds) :
    v.toNat<2^125 ∧ topRanksValid v=true ∧ (Search.topDigits v).sum=129 := by
  rw [Search.decode_top] at h
  split_ifs at h with hgood
  · exact hgood
end SigGolfCandidate.T3M.Nonbinary.NCtx
end
section
namespace SigGolfCandidate.T3M.Nonbinary.NCtx
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Nonbinary SigGolfCandidate.T3
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
structure Encoded (v : Digest) (s : MachineState) : Prop where
  lo : s.getReg .x16=v.extractLsb' 0 64
  hi : s.getReg .x17=v.extractLsb' 63 64
  tail : s.getReg .x29=BitVec.ofNat 64 (v.toNat/2^119)
  mask : s.getReg .x6=130048#64
  table : s.getReg .x15=712704#64
theorem dispatch_at (c : NCtx) (hds : c.DigitsOk) (q : Nat) (hq : q<17) :
    vrun (c.endPc (3*q+2)) 5=some (if q<16 then dispatchR (q+1) else tailDispatchR) := by
  have h := (c.groupFacts hds q (by omega)).disp hq
  have eq : (3*q+2)/3=q := by omega
  simpa only [endPc,qX,eq,show (3*q+2)%3=2 by omega,if_false,Nat.reduceEqDiff] using h
def GroupIn (c : NCtx) (s0 : MachineState) (q : Nat) (acc : List Digest) (s : MachineState) : Prop :=
  c.Base s0 (c.Wr (3*q)) acc s ∧ acc.length=3*q ∧ s.pc=pcOf (c.entPc q)
theorem end_dispatch_raw (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState} {v : Digest}
    (he : Encoded v s0) (q : Nat) (hq : q<16) (acc : List Digest) (s : MachineState)
    (hs : c.EndInv s0 (3*q+2) acc s) :
    ∃t,Steps vimage s 4 4 t ∧ c.Base s0 (c.Wr (3*(q+1))) acc t ∧ acc.length=3*(q+1) ∧
      t.pc=pcOf (entW (q+1) (Search.topRank v (q+1))) := by
  obtain ⟨⟨hR,hF,hS⟩,hlen,hpc⟩ := hs
  have hr := c.dispatch_at hds q (by omega)
  rw [if_pos hq] at hr
  have hbound : c.endPc (3*q+2)<251927 := by
    have := c.qX_lt hds (3*q+2) (by omega)
    simp only [endPc,show (3*q+2)%3=2 by omega,if_false,Nat.reduceEqDiff]; omega
  obtain ⟨t,st,pt,rt,ft⟩ := dispatch_step (by omega) hbound hr s v hpc
    ((hR _ (by decide)).trans he.lo) ((hR _ (by decide)).trans he.hi)
    ((hR _ (by decide)).trans he.mask) ((hR _ (by decide)).trans he.table)
  refine ⟨t,st,⟨fun x hx => ?_,(hF.trans ft).mono (by intro A hA h;rcases h with h|h;simpa only [show 3*q+2+1=3*(q+1) by omega] using h;contradiction),fun j hj => ?_⟩,by omega,pt⟩
  · rw [rt.get (by intro h;simp only [List.mem_singleton] at h;subst x;exact hx (by decide))]
    exact hR x hx
  · exact (hS j hj).frame ft (by have := slot_props j (by omega);omega) (by simp) (by simp)
theorem end_dispatch (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState} {v : Digest}
    (he : Encoded v s0) (hf : c.Fit v) (q : Nat) (hq : q<16) (hv : Search.topRank v (q+1)<125)
    (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 (3*q+2) acc s) :
    ∃t,Steps vimage s 4 4 t ∧ c.GroupIn s0 (q+1) acc t := by
  obtain ⟨t,st,hB,hl,pt⟩ := c.end_dispatch_raw hc hds he q hq acc s hs
  refine ⟨t,st,hB,hl,?_⟩
  rw [pt]
  unfold entPc
  rw [c.fit_rank' hf (q+1) (by omega) hv]
def tailInitial (s0 t : MachineState) : MachineState := s0.setReg .x15 (t.getReg .x15)
theorem tailInitial_mem (s0 t : MachineState) (a : Word) :
    (tailInitial s0 t).getMem a=s0.getMem a := rfl
theorem tailInitial_regs (s0 t : MachineState) (r : Reg) (hr : r≠.x15) :
    (tailInitial s0 t).getReg r=s0.getReg r := by
  unfold tailInitial
  rw [setReg_of_ne s0 _ (by decide)]
  cases r <;> simp_all [MachineState.getReg]
theorem tailInitial_15 (s0 t : MachineState) :
    (tailInitial s0 t).getReg .x15=t.getReg .x15 := by
  unfold tailInitial
  rw [setReg_of_ne s0 _ (by decide)]
  rfl
theorem tailInitial_known (c : NCtx) {s0 t : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) :
    ∀p∈c.known,(tailInitial s0 t).getReg p.1=p.2 := by
  intro p hp
  rw [tailInitial_regs _ _ _ (by rcases p with ⟨r,w⟩;simp only [known,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hp;rcases hp with h|h|h|h|h|h|h|h|h|h|h|h <;> obtain ⟨rfl,_⟩ := h <;> simp)]
  exact hk p hp
theorem tailInitial_orig (c : NCtx) {s0 t : MachineState} (h0 : c.Orig0 s0) :
    c.Orig0 (tailInitial s0 t) := by
  refine ⟨fun i hi k hk => h0.1 i hi k hk, h0.2.congr (fun A _ _ => tailInitial_mem s0 t _)⟩
theorem end_tail (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState} {v : Digest}
    (he : Encoded v s0) (hf : c.Fit v) (hv : v.toNat<2^125)
    (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 50 acc s) :
    ∃t,Steps vimage s 3 3 t ∧ c.GroupIn (tailInitial s0 t) 17 acc t ∧ t.getReg .x15 = 712704#64 := by
  obtain ⟨⟨hR,hF,hS⟩,hlen,hpc⟩ := hs
  have hr := c.dispatch_at hds 16 (by decide)
  norm_num at hr
  have hbound : c.endPc 50<251927 := by
    have := c.qX_lt hds 50 (by decide)
    simp only [endPc,Nat.reduceMod,if_false,Nat.reduceEqDiff]; omega
  obtain ⟨t,st,pt,rt,ft,r15⟩ := tail_dispatch_step hbound hr s (v.toNat/2^119) (by omega) hpc
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
def s8v (c : NCtx) (q : Nat) : Word := BitVec.ofNat 64 (((List.range (3*q+3)).map c.dig).sum)-129#64
def set24 (b : MachineState) (x : Word) : MachineState := b.setReg .x24 x
theorem set24_regs (b : MachineState) (x : Word) (r : Reg) (hr : r≠.x24) : (set24 b x).getReg r=b.getReg r := by
  unfold set24
  rw [setReg_of_ne b _ (by decide)]
  cases r <;> simp_all [MachineState.getReg]
theorem set24_24 (b : MachineState) (x : Word) : (set24 b x).getReg .x24=x := by
  unfold set24
  rw [setReg_of_ne b _ (by decide)]
  rfl
theorem set24_mem (b : MachineState) (x : Word) (a : Word) : (set24 b x).getMem a=b.getMem a := rfl
theorem set24_known (c : NCtx) {b : MachineState} (x : Word) (hk : ∀p∈c.known,b.getReg p.1=p.2) :
    ∀p∈c.known,(set24 b x).getReg p.1=p.2 := by
  intro p hp
  rw [set24_regs _ _ _ (by rcases p with ⟨r,w⟩;simp only [known,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hp;rcases hp with h|h|h|h|h|h|h|h|h|h|h|h <;> obtain ⟨rfl,_⟩ := h <;> simp)]
  exact hk p hp
theorem set24_orig (c : NCtx) {b : MachineState} (x : Word) (h0 : c.Orig0 b) : c.Orig0 (set24 b x) :=
  ⟨fun i hi k hk => h0.1 i hi k hk, h0.2.congr (fun A _ _ => set24_mem b x _)⟩
theorem set24_encoded {v : Digest} {b : MachineState} (x : Word) (he : Encoded v b) : Encoded v (set24 b x) :=
  ⟨(set24_regs _ _ _ (by decide)).trans he.lo,(set24_regs _ _ _ (by decide)).trans he.hi,
    (set24_regs _ _ _ (by decide)).trans he.tail,(set24_regs _ _ _ (by decide)).trans he.mask,
    (set24_regs _ _ _ (by decide)).trans he.table⟩
theorem sum_range_three (f : Nat → Nat) (n : Nat) :
    ((List.range (n+3)).map f).sum=((List.range n).map f).sum+(f n+f (n+1)+f (n+2)) := by
  simp only [List.range_succ,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  omega
theorem kss_kOf (c : NCtx) (hds : c.DigitsOk) (q : Nat) (hq : q<18) :
    kss q (c.kOf q)=c.dig (3*q)+c.dig (3*q+1)+c.dig (3*q+2) := by
  obtain ⟨k1,k2,k3⟩ := c.kdig_kOf hds q hq
  simp only [kss,k1,k2,k3]
theorem s8v_succ (c : NCtx) (hds : c.DigitsOk) (q : Nat) (hq : q<17) :
    c.s8v q+BitVec.ofNat 64 (kss (q+1) (c.kOf (q+1)))=c.s8v (q+1) := by
  have hS : ((List.range (3*(q+1)+3)).map c.dig).sum =
      ((List.range (3*q+3)).map c.dig).sum+kss (q+1) (c.kOf (q+1)) := by
    rw [c.kss_kOf hds (q+1) (by omega),show 3*(q+1)+3=(3*q+3)+3 by ring,sum_range_three]
    simp only [show 3*(q+1)=3*q+3 by ring]
  unfold s8v
  rw [hS,BitVec.ofNat_add]
  simp only [BitVec.sub_eq_add_neg]
  ac_rfl
theorem entry_step (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {b : MachineState} (q : Nat) (hq : q<17)
    (h24 : b.getReg .x24=c.s8v q) (acc : List Digest) (s : MachineState) (hs : c.GroupIn b (q+1) acc s) :
    ∃t,Steps vimage s 1 1 t ∧ c.ChainIn (set24 b (c.s8v (q+1))) (3*(q+1)) acc t := by
  obtain ⟨⟨hR,hF,hS⟩,hlen,hpc⟩ := hs
  have hfacts := c.groupFacts hds (q+1) (by omega)
  have hchk := hfacts.s8
  simp only [s8Check,show q+1≠0 by omega,if_false] at hchk
  have hrun := rOK_eq hchk
  obtain ⟨h1,h2⟩ := c.kOf_bounds hds (q+1) (by omega)
  have hl := (group_bounds (q+1) (c.kOf (q+1)) (by omega) h1 h2).2.2.1
  have hp : entW (q+1) (c.kOf (q+1))<251927 := by unfold leadPc at hl; omega
  have hst := piece_steps45 hrun hp s hpc (by simp [s8R])
  set r := s8R (kss (q+1) (c.kOf (q+1))) (entW (q+1) (c.kOf (q+1))) with hr
  have h24s : s.getReg .x24=c.s8v q := (hR .x24 (by decide)).trans h24
  refine ⟨r.toState s,hst,⟨⟨fun x hx => ?_,fun A hA hn => ?_,fun j hj => ?_⟩,hlen,?_⟩⟩
  · rw [Result.toState_getReg]
    by_cases hx : x=.x24
    · subst x
      simp only [hr,s8R]
      rw [RegFile.get_set_self _ _ (by decide),addC_eval,set24_24]
      simp only [E.eval,h24s]
      exact c.s8v_succ hds q hq
    · simp only [hr,s8R]
      rw [RegFile.get_set_ne _ _ hx,RegFile.init_get_eval,set24_regs _ _ _ hx]
      exact hR x (by assumption)
  · rw [Result.toState_getMem,set24_mem]
    simp only [hr,s8R]
    rw [memEval_nil]
    exact hF A hA hn
  · have hfr : Frame s (r.toState s) (fun _ => False) := fun A _ _ => by
      rw [Result.toState_getMem]; simp [hr,s8R,memEval_nil]
    exact (hS j hj).frame hfr (by have := slot_props j (by omega);omega) (by simp) (by simp)
  · rw [Result.toState_pc]
    simp only [hr,s8R,E.eval]
    unfold startPc leadPc leadOff
    simp only [show 3*(q+1)%3=0 by omega,if_true,show 3*(q+1)/3=q+1 by omega,show q+1≠0 by omega,if_false]
end SigGolfCandidate.T3M.Nonbinary.NCtx
end
end

section






section
namespace SigGolfCandidate.T3M.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
def topPrefixWord (tp : Word) : Word :=
  BitVec.ofNat 64 (128 + 193 * 2 ^ 56) ||| (tp >>> (16 : Word))
def fusedPrefixCode : List (BitVec 32) :=
  [407555,8796291,58252947,66605459,1611923,3729587,0xf9033e03,16929171,4091443,0xff833303,0x90050413,714679,0xa81713,6780723,0xf70733,0x9a070067]
sym_block fusedPrefixBase := symRun { noAlias := true } fusedPrefixCode (pcOf 96160) 200
set_option maxRecDepth 2000000 in
theorem fusedPrefix_run_check :
    ((List.range 128).all fun c =>
      T3M.rOK
        (symRun { noAlias := true } fusedPrefixCode (pcOf (T3M.trPc 0 c + 9)) 200)
        fusedPrefixBase.res) = true := by
  decide +kernel
theorem fusedPrefix_run (c : Nat) (hc : c < 128) :
    symRun { noAlias := true } fusedPrefixCode (pcOf (T3M.trPc 0 c + 9)) 200 = some fusedPrefixBase.res :=
  T3M.rOK_eq (List.all_eq_true.mp fusedPrefix_run_check c (List.mem_range.mpr hc))
def isPfx : List (BitVec 32) → List (BitVec 32) → Bool
  | [], _ => true
  | a :: as, b :: bs => (a == b) && isPfx as bs
  | _, [] => false
theorem isPfx_prefix : ∀ l₁ l₂, isPfx l₁ l₂ = true → l₁ <+: l₂
  | [], l₂, _ => ⟨l₂, rfl⟩
  | _ :: _, [], h => by cases h
  | a :: as, b :: bs, h => by
    simp only [isPfx, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨t, ht⟩ := isPfx_prefix as bs h.2
    exact ⟨t, by simp [h.1, ht]⟩
set_option maxRecDepth 2000000 in
theorem fusedPrefix_check :
    ((List.range 128).all fun c => isPfx fusedPrefixCode (codeFrom (T3M.trPc 0 c + 9))) = true := by
  decide +kernel
theorem fusedPrefix_at (c : Nat) (hc : c < 128) :
    CodeAt Verify.image (pcOf (T3M.trPc 0 c + 9)) fusedPrefixCode := by
  have ht := T3M.trPc_lt 0 c
  have h := codeAt_from (T3M.trPc 0 c + 9) (by omega)
  change CodeAt Verify.image (pcOf (T3M.trPc 0 c + 9)) (codeFrom (T3M.trPc 0 c + 9)) at h
  have hp : fusedPrefixCode <+: codeFrom (T3M.trPc 0 c + 9) :=
    isPfx_prefix _ _ (List.all_eq_true.mp fusedPrefix_check c (List.mem_range.mpr hc))
  have hl := hp.length_le
  have h3 := h.2.2.1
  exact ⟨h.1, h.2.1, by omega, hp.trans h.2.2.2⟩
theorem tail_field (v : Digest) : (v.extractLsb' 64 64 >>> 55) = BitVec.ofNat 64 (v.toNat / 2 ^ 119) := by
  apply BitVec.eq_of_toNat_eq
  have hv := v.isLt
  simp only [BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  omega
theorem prefix_spec (s : MachineState) (v : Digest) (c d : Nat) (hc : c < 128)
    (hpc : s.pc = pcOf (T3M.trPc 0 c + 9)) (h12 : s.getReg .x12 = BitVec.ofNat 64 d) (hd : d = 15560 ∨ d = 15608)
    (hv : DigAt s d v) (h6 : s.getReg .x6 = 0xffc000#64)
    (hmask : s.getMem 0xffbff8#64 = 130048#64) (h10 : s.getReg .x10 = 15560#64)
    (hmem : s.getMem (BitVec.ofNat 64 0xffbf90) = BitVec.ofNat 64 (128 + 193 * 2 ^ 56)) :
    ∃ t, Steps Verify.image s 16 16 t ∧ t.pc = pcOf (176744 + 256 * (v.toNat % 128)) ∧
      t.getReg .x16 = v.extractLsb' 0 64 ∧
      t.getReg .x17 = (v.extractLsb' 64 64 <<< (1 : Word)) ||| (v.extractLsb' 0 64 >>> (63 : Word)) ∧
      t.getReg .x29 = BitVec.ofNat 64 (v.toNat / 2 ^ 119) ∧
      t.getReg .x8 = 13768#64 ∧ t.getReg .x6 = 130048#64 ∧ t.getReg .x15 = 712704#64 ∧
      t.getReg .x28 = topPrefixWord (s.getReg .x4) ∧
      RegsExcept s t [.x16,.x17,.x29,.x3,.x6,.x28,.x8,.x15,.x14] ∧ Frame s t (fun _ => False) := by
  have hm : s.getMem 0xffbff8#64 = 130048#64 := hmask
  have h0 : s.getMem (s.getReg .x12) = v.extractLsb' 0 64 := by rw [h12]; exact hv.1
  have h1 : s.getMem (s.getReg .x12 + 8#64) = v.extractLsb' 64 64 := by
    rw [h12, show (8#64 : Word) = BitVec.ofNat 64 8 from rfl, ofNat_add_ofNat]; exact hv.2
  refine ⟨_, symRun_sound (fusedPrefix_run c hc) (fusedPrefix_at c hc) s hpc
    (by rcases hd with rfl | rfl <;> simp [fusedPrefixBase.res, rv_simp, accessValid_iff, MEMORY_BYTES, h12, h6] <;> decide),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hx6 : (fusedPrefixBase.res.toState s).getReg .x6 = 130048#64 := by
      simp [fusedPrefixBase.res, rv_simp, h6, hm]
    simp only [Result.toState_getReg, fusedPrefixBase.res, rv_simp] at hx6
    simp only [Result.toState_pc, fusedPrefixBase.res, rv_simp, h0, hx6, pcOf]
    have h := SigGolfCandidate.T3M.Nonbinary.prologue_target v
    simp only [pcOf] at h
    rw [← h]
    congr 1
  · simpa [fusedPrefixBase.res, rv_simp] using h0
  · simp [fusedPrefixBase.res, rv_simp, h0, h1]
  · simp only [Result.toState_getReg, fusedPrefixBase.res, rv_simp]
    simp [h1, tail_field]
  · simp [fusedPrefixBase.res, rv_simp, h10]
  · simp [fusedPrefixBase.res, rv_simp, h6, hm]
  · simp [fusedPrefixBase.res, rv_simp, pcOf]
  · simp [fusedPrefixBase.res, rv_simp, topPrefixWord, h6, hmem]
  · intro r hr; cases r <;> simp at hr <;> simp [fusedPrefixBase.res, rv_simp] <;> rfl
  · intro A _ _; simp [fusedPrefixBase.res, rv_simp]
end SigGolfCandidate.T3M.Verify.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
theorem topPrefixWord_hdr1 (tree leaf : Nat) (ht : tree < 2 ^ 32) (hl : leaf < 2 ^ 32) (h0 : tree = 0) :
    topPrefixWord (BitVec.ofNat 64 (hdr1 tree leaf)) =
      BitVec.ofNat 64 (128 + 193 * 2 ^ 56 + leaf * 2 ^ 16) := by
  rw [hdr1_eq tree leaf ht hl]
  unfold topPrefixWord
  change BitVec.ofNat 64 (128 + 193 * 2 ^ 56) |||
    (BitVec.ofNat 64 (tree + 2 ^ 32 * leaf) >>> (16 : Nat)) = _
  rw [ofNat_shr _ _ (by omega)]
  rw [show (tree + 2 ^ 32 * leaf) / 2 ^ 16 = leaf * 2 ^ 16 by subst h0; omega]
  rw [show 128 + 193 * 2 ^ 56 = 193 * 2 ^ 56 + 128 by omega,
    ← ofNat_or_add 128 193 56 (by decide), BitVec.or_assoc,
    ofNat_or_disjoint' 128 (leaf * 2 ^ 16) 16 (by decide) (by omega),
    ofNat_or_add _ 193 56 (by omega)]
  congr 1
  omega
end SigGolfCandidate.T3M.Verify.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
def rejectJumpCode : List (BitVec 32) := [0xbfda206f]
sym_block rejectJumpBase := symRun { noAlias := true } rejectJumpCode (pcOf 96230) 20
theorem rejectJump_at : CodeAt Verify.image (pcOf 96230) rejectJumpCode := by
  have h := codeAt_from 96230 (by decide)
  have hp : rejectJumpCode <+: codeFrom 96230 := by decide +kernel
  exact ⟨by decide, by decide, by decide +kernel, hp.trans h.2.2.2⟩
def rejectExitCode : List (BitVec 32) := [1049235,1049875]
sym_block rejectExitBase := symRun { noAlias := true } rejectExitCode (pcOf 741) 20
theorem rejectExit_at : CodeAt Verify.image (pcOf 741) rejectExitCode := by
  have h := codeAt_from 741 (by decide)
  have hp : rejectExitCode <+: codeFrom 741 := by decide +kernel
  exact ⟨by decide, by decide, by decide +kernel, hp.trans h.2.2.2⟩
theorem reject_halt (s : MachineState) (hpc : s.pc = pcOf 96230) :
    ∃ t, Steps Verify.image s 3 3 t ∧ fetch Verify.image t = some (.base .ECALL) ∧
      t.getReg .x5 = 1 ∧ t.getReg .x10 = 1 := by
  have e1 := symRun_sound rejectJumpBase rejectJump_at s hpc (by simp [rejectJumpBase.res, rv_simp])
  have p1 : (rejectJumpBase.res.toState s).pc = pcOf 741 := by simp [rejectJumpBase.res, rv_simp, pcOf]
  have e2 := symRun_sound rejectExitBase rejectExit_at (rejectJumpBase.res.toState s) p1
    (by simp [rejectExitBase.res, rv_simp])
  refine ⟨_, e1.trans e2, ?_, ?_, ?_⟩
  · have h : CodeAt Verify.image (pcOf 743) [0x00000073] := by
      have h := codeAt_from 743 (by decide)
      have hp : [0x00000073] <+: codeFrom 743 := by decide +kernel
      exact ⟨by decide, by decide, by decide +kernel, hp.trans h.2.2.2⟩
    exact h.fetch _ (by simp [rejectExitBase.res, rv_simp, pcOf])
  · simp [rejectExitBase.res, rv_simp]
  · simp [rejectExitBase.res, rv_simp]
end SigGolfCandidate.T3M.Verify.Nonbinary
end
section
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
def topEntryRegs : List Reg := [.x1,.x3,.x16,.x17,.x14,.x25,.x29,.x8,.x22,.x6,.x15,.x28]
structure TopEntry (u : MachineState) (v : Digest) (p : Nat) (s : MachineState) : Prop where
  pc : s.pc = pcOf (176744 + 256 * (v.toNat % 128))
  ra : True
  lo : s.getReg .x16 = v.extractLsb' 0 64
  hi : s.getReg .x17 = (v.extractLsb' 64 64 <<< (1 : Word)) ||| (v.extractLsb' 0 64 >>> (63 : Word))
  tail : s.getReg .x29 = BitVec.ofNat 64 (v.toNat / 2 ^ 119)
  s3 : s.getReg .x8 = 13768#64
  mask : s.getReg .x6 = 130048#64
  table : s.getReg .x15 = 712704#64
  «prefix» : s.getReg .x28 = Nonbinary.topPrefixWord (u.getReg .x4)
  regs : RegsExcept u s topEntryRegs
  frame : Frame u s (fun _ => False)
theorem topTransition (w : WBytes) (pk : Digest) (index c : Nat) (hc : c < nCopy 0)
    (t : MachineState) (ht : EncPre w pk index 0 c t) (a : BitVec 256) :
    ∃ s, Steps image (writeHash t a) 16 16 s ∧
      TopEntry (writeHash t a) (a.extractLsb' 0 128) (trPc 0 c) s := by
  obtain ⟨d, h12, hd⟩ := ht.dst0 rfl
  have hk : KnownOK (BC.bK 0) (writeHash t a) := fun p hp => by rw [writeHash_getReg]; exact ht.glob.1 p hp
  have hpc : (writeHash t a).pc = pcOf (trPc 0 c + 9) := by
    rw [writeHash_pc, ht.pc]
    change pcOf (trPc 0 c + 8) + 4 = pcOf (trPc 0 c + 9)
    simpa only [Nat.add_assoc] using pcOf_add4 (trPc 0 c + 8)
  have hglob := Glob_writeHash ht.glob a d h12 (by rcases hd with rfl | rfl <;> decide)
  have hv := DigAt.writeHash_lo t a d h12 (by omega)
  have h12s : (writeHash t a).getReg .x12 = BitVec.ofNat 64 d := by
    rw [writeHash_getReg]; exact h12
  have hD := hglob.2.2.2.2.2
  have h10 : (writeHash t a).getReg .x10 = 15560#64 :=
    hk (.x10, BitVec.ofNat 64 (x10In 0)) (by simp [BC.bK])
  have hmem : (writeHash t a).getMem (BitVec.ofNat 64 0xffbf90) = BitVec.ofNat 64 (128 + 193 * 2 ^ 56) :=
    hD.prefix 0 (by decide)
  have hmask : (writeHash t a).getMem 0xffbff8#64 = 130048#64 :=
    hD.mask
  have h6 : (writeHash t a).getReg .x6 = 0xffc000#64 :=
    hk (.x6, BitVec.ofNat 64 TOPBASE) (by simp [BC.bK, bK, layK])
  obtain ⟨z, ez, pz, lo, hi, tl, s3, mask, tab, px, rz, fz⟩ :=
    Verify.Nonbinary.prefix_spec (writeHash t a) _ c d hc hpc h12s hd hv h6 hmask h10 hmem
  refine ⟨z, ez, ⟨pz, trivial, lo, hi, tl, s3, mask, tab, px, ?_, ?_⟩⟩
  · exact rz.mono (by decide)
  · exact fz.mono (by simp)
end SigGolfCandidate.T3M
end
section
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest route coreDigit)
open Nonbinary (NCtx)
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
def nctxOf (w : WBytes) (index : Nat) (v : Digest) (p : Nat) : NCtx :=
  ⟨w, (route index 0).2, (route index 0).1, 13768, coreDigit 0 v, p + 10⟩
theorem nctx_ok (w : WBytes) (index : Nat) (v : Digest) (c : Nat) (hidx : index < 2 ^ 31) :
    (nctxOf w index v (trPc 0 c)).ok := by
  have hp := trPc_lt 0 c
  have ht : (route index 0).2 = 0 := by rw [route_snd]; exact Nat.div_eq_of_lt hidx
  exact ⟨ht, leaf_lt index 0, by norm_num [nctxOf], by norm_num [nctxOf], by norm_num [nctxOf], by dsimp [nctxOf]; omega⟩
theorem nctx_known (w : WBytes) (pk : Digest) (index c : Nat) (t s : MachineState) (a : BitVec 256)
    (hidx : index < 2 ^ 31)
    (ht : EncPre w pk index 0 c t)
    (he : TopEntry (writeHash t a) (a.extractLsb' 0 128) (trPc 0 c) s) :
    KnownOK (nctxOf w index (a.extractLsb' 0 128) (trPc 0 c)).known s := by
  have htree : (route index 0).2 = 0 := by
    rw [route_snd]
    exact Nat.div_eq_of_lt hidx
  have hleaf := leaf_lt32 index 0
  have hprefix : s.getReg .x28 = BitVec.ofNat 64
      (nctxOf w index (a.extractLsb' 0 128) (trPc 0 c)).prefix := by
    rw [he.prefix, writeHash_getReg, ht.tp 0 rfl,
      Nonbinary.topPrefixWord_hdr1 _ _ (tree_lt index 0 hidx) hleaf htree]
    simp only [nctxOf, NCtx.prefix, htree, Nat.zero_mul, Nat.zero_add,
      Nat.mod_eq_of_lt hleaf]
  intro p hp
  simp only [NCtx.known, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact he.s3
  all_goals try exact hprefix
  all_goals rw [he.regs.get (by simp [topEntryRegs]), writeHash_getReg]
  all_goals try exact ht.tp 0 rfl
  all_goals exact ht.glob.1 _ (by simp [BC.bK, bK, layK, baseK, nctxOf, NCtx.w1, hw, t3In])
theorem topEntry_orig (w : WBytes) (pk : Digest) (index c : Nat) (t s : MachineState) (a : BitVec 256)
    (ht : EncPre w pk index 0 c t)
    (he : TopEntry (writeHash t a) (a.extractLsb' 0 128) (trPc 0 c) s) :
    Verify.Orig w (fun o => 9288 ≤ o ∧ o < layerEnd 0) s := by
  obtain ⟨d, h12, hd⟩ := ht.dst0 rfl
  have ho := Orig_writeHash ht.orig a d h12 (by omega)
  have hu : Verify.Orig w (fun o => 9288 ≤ o ∧ o < layerEnd 0) (writeHash t a) :=
    fun j hj hp => ho j hj ⟨hp, Or.inl (by
      have hp2 := hp.2
      have hle : layerEnd 0 = 13512 := rfl
      rw [hle] at hp2
      unfold WIT; omega)⟩
  exact hu.frame (fun j hj hp => he.frame.get (by unfold WIT WX at *; omega) (by simp))
theorem nctx_orig (w : WBytes) (index : Nat) (v : Digest) (p : Nat) (s : MachineState)
    (ho : Verify.Orig w (fun o => 9288 ≤ o ∧ o < layerEnd 0) s) (hD : DataOK s) :
    (nctxOf w index v p).Orig0 s := by
  refine ⟨fun i hi k hk => ?_, hD⟩
  clear hD
  apply origW_of ho _
  all_goals simp only [NCtx.blk, nctxOf]
  all_goals norm_num [WIT, WX, layerEnd] at *
  all_goals omega
end SigGolfCandidate.T3M
end
end

section


section
namespace SigGolfCandidate.T3M.Nonbinary.NCtx
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Nonbinary SigGolfCandidate.T3
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
theorem set24_set24 (b : MachineState) (x y : Word) : set24 (set24 b x) y=set24 b y := by
  unfold set24
  rw [setReg_of_ne _ _ (by decide),setReg_of_ne b _ (by decide),setReg_of_ne b _ (by decide)]
  simp only
  congr 1
  funext r
  by_cases h : r=.x24 <;> simp [h]
theorem chainsCost_add' (c : NCtx) (i n k : Nat) :
    c.chainsCost i (n+k)=c.chainsCost i n+c.chainsCost (i+n) k := by
  unfold chainsCost
  rw [← List.range'_append_1,List.map_append,List.sum_append]
def bq (c : NCtx) (s0 : MachineState) (q : Nat) : MachineState := if q=0 then s0 else set24 s0 (c.s8v (q-1))
theorem guard_cond (v : Digest) :
    CmpOp.eval .geu (BitVec.ofNat 64 (v.toNat/2^119)) 64#64=decide (2^125 ≤ v.toNat) := by
  have hv := v.isLt
  simp only [CmpOp.eval,BitVec.ult,BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]
  by_cases h : 2^125 ≤ v.toNat
  · rw [decide_eq_true h]; simp; omega
  · rw [decide_eq_false h]; simp; omega
theorem guard_ok (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) {v : Digest} (he : Encoded v s0) (hv : v.toNat<2^125)
    (acc : List Digest) (s : MachineState) (hs : c.GroupIn s0 0 acc s) :
    ∃t,Steps vimage s 2 2 t ∧ c.ChainIn (set24 s0 (c.s8v 0)) 0 acc t := by
  obtain ⟨⟨hR,hF,hS⟩,hlen,hpc⟩ := hs
  have hchk := (c.groupFacts hds 0 (by decide)).s8
  simp only [s8Check,if_true] at hchk
  have hrun := rOK_eq hchk
  have hp : entW 0 (c.kOf 0)<251927 := by
    have := (c.kOf_bounds hds 0 (by decide)).2 (by decide)
    unfold entW entOff; simp; omega
  have hst := piece_steps45 hrun hp s hpc (by simp [guardR])
  set r := guardR (c.kOf 0) with hr
  have h29 : s.getReg .x29=BitVec.ofNat 64 (v.toNat/2^119) := (hR .x29 (by decide)).trans he.tail
  have h11 : s.getReg .x11=64#64 := (hR .x11 (by decide)).trans (hk (.x11,64) (by simp [known]))
  have hcond := guard_cond v
  have hfr : Frame s (r.toState s) (fun _ => False) := fun A _ _ => by
    rw [Result.toState_getMem]; simp [hr,guardR,memEval_nil]
  refine ⟨r.toState s,hst,⟨⟨fun x hx => ?_,fun A hA hn => ?_,fun j hj => ?_⟩,hlen,?_⟩⟩
  · rw [Result.toState_getReg]
    by_cases hx : x=.x24
    · subst x
      simp only [hr,guardR]
      rw [RegFile.get_set_self _ _ (by decide),set24_24]
      simp only [E.eval,s8v,kss]
      obtain ⟨k1,k2,k3⟩ := c.kdig_kOf hds 0 (by decide)
      rw [k1,k2,k3]
      simp [List.range_succ]
      congr 1
      omega
    · simp only [hr,guardR]
      rw [RegFile.get_set_ne _ _ hx,RegFile.init_get_eval,set24_regs _ _ _ hx]
      exact hR x (by assumption)
  · rw [set24_mem]; exact (hfr A hA (by simp)).trans (hF A hA hn)
  · exact (hS j hj).frame hfr (by have := slot_props j (by omega);omega) (by simp) (by simp)
  · rw [Result.toState_pc]
    simp only [hr,guardR,E.eval,h29,h11,hcond,decide_eq_false (show ¬ 2^125 ≤ v.toNat by omega)]
    unfold startPc leadPc leadOff entW entOff
    simp
theorem guard_rej (c : NCtx) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) {v : Digest} (he : Encoded v s0) (hv : 2^125 ≤ v.toNat)
    (acc : List Digest) (s : MachineState) (hs : c.GroupIn s0 0 acc s) :
    ∃t,Steps vimage s 3 3 t ∧ t.pc=pcOf 96230 := by
  obtain ⟨⟨hR,hF,hS⟩,hlen,hpc⟩ := hs
  have hchk := (c.groupFacts hds 0 (by decide)).s8
  simp only [s8Check,if_true] at hchk
  have hrun := rOK_eq hchk
  have hk125 := (c.kOf_bounds hds 0 (by decide)).2 (by decide)
  have hp : entW 0 (c.kOf 0)<251927 := by unfold entW entOff; simp; omega
  have hst := piece_steps45 hrun hp s hpc (by simp [guardR])
  have h29 : s.getReg .x29=BitVec.ofNat 64 (v.toNat/2^119) := (hR .x29 (by decide)).trans he.tail
  have h11 : s.getReg .x11=64#64 := (hR .x11 (by decide)).trans (hk (.x11,64) (by simp [known]))
  have hcond := guard_cond v
  set t := (guardR (c.kOf 0)).toState s with ht
  have hpt : t.pc=pcOf (176744+256*c.kOf 0+250) := by
    rw [ht,Result.toState_pc]
    simp only [guardR,E.eval,h29,h11,hcond,decide_eq_true hv,if_true]
  have hstub := stub_at (c.kOf 0) hk125
  have hst2 := piece_steps45 hstub (by omega) t hpt (by intro o ho; simp [rejJ,SymState.init] at ho)
  refine ⟨rejJ.toState t,(hst.trans hst2).of_eq (by simp [guardR,rejJ]) (by simp [guardR,rejJ]),?_⟩
  rw [Result.toState_pc]; rfl
theorem row_rej (q k : Nat) (hq : q<17) (hk : 125 ≤ k) (hk' : k<128) (s : MachineState)
    (hpc : s.pc=pcOf (entW q k)) : ∃t,Steps vimage s 1 1 t ∧ t.pc=pcOf 96230 := by
  have h := rej_at q k hq hk hk'
  have hp : entW q k<251927 := by unfold entW entOff; split_ifs <;> omega
  exact ⟨rejJ.toState s,piece_steps45 h hp s hpc (by intro o ho; simp [rejJ,SymState.init] at ho),
    by rw [Result.toState_pc]; rfl⟩
theorem groups_from (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0) {v : Digest} (he : Encoded v s0) (hf : c.Fit v)
    (n : Nat) (hn : n ≤ 17) (hval : ∀ q, q<n → Search.topRank v q<125)
    (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ acc t,c.EndInv (set24 s0 (c.s8v (n-1))) (3*(n-1)+2) acc t → Verify.GoodQ t N C Q A (K acc)) :
    ∀ k q, 1 ≤ q → q+k=n → 0<k → ∀ acc s,c.GroupIn (set24 s0 (c.s8v (q-1))) q acc s →
      Verify.GoodQ s (N+126*k) (C+c.chainsCost (3*q) (3*k)+5*k-4) Q (A+c.chainsCost (3*q) (3*k)+5*k-4)
        (Verify.ccM ((List.range' (3*q) (3*k)).foldlM c.chainF acc) K) := by
  intro k
  induction k with
  | zero => intro q _ _ h; omega
  | succ k ih =>
    intro q hq1 hqk _ acc s hs
    have hq : q<17 := by omega
    obtain ⟨q',rfl⟩ : ∃q',q=q'+1 := ⟨q-1,by omega⟩
    obtain ⟨t,hst,hin⟩ := c.entry_step hc hds q' (by omega) (set24_24 _ _) acc s (by simpa using hs)
    rw [set24_set24] at hin
    have hkB := set24_known c (c.s8v (q'+1)) hk
    have h0B := set24_orig c (c.s8v (q'+1)) h0
    have heB := set24_encoded (c.s8v (q'+1)) he
    rw [show 3*(k+1)=3+3*k by ring,← List.range'_append_1,List.foldlM_append,Verify.ccM_bind]
    have ec := c.chainsCost_add' (3*(q'+1)) 3 (3*k)
    by_cases hk0 : k=0
    · subst hk0
      have hqn : q'+1=n-1 := by omega
      have H := c.group_good hc hds hkB h0B (q'+1) (by omega) K N C A Q (by rw [← hqn] at hK; exact hK)
        3 (3*(q'+1)) (le_refl _) (by omega) (by decide) acc t hin
      have H' := Verify.GoodQ.steps hst H
      simp only [Nat.mul_zero,Nat.add_zero,List.range'_zero,List.foldlM_nil,bind_pure,Verify.ccM_pure] at H' ⊢
      refine H'.mono ?_ ?_ (fun h => ⟨h,?_⟩) <;> omega
    · have H := c.group_good hc hds hkB h0B (q'+1) (by omega)
        (fun ends => Verify.ccM ((List.range' (3*(q'+1)+3) (3*k)).foldlM c.chainF ends) K)
        (N+126*k+4) (C+c.chainsCost (3*(q'+1)+3) (3*k)+5*k-4+4) (A+c.chainsCost (3*(q'+1)+3) (3*k)+5*k-4+4) Q
        (fun ends u hu => by
          obtain ⟨u',st,hu'⟩ := c.end_dispatch hc hds heB hf (q'+1) (by omega) (hval (q'+2) (by omega)) ends u hu
          have H := ih (q'+2) (by omega) (by omega) (by omega) ends u' (by simpa using hu')
          rw [show 3*(q'+2)=3*(q'+1)+3 by omega] at H
          refine (Verify.GoodQ.steps st H).mono ?_ ?_ (fun h => ⟨h,?_⟩) <;> omega)
        3 (3*(q'+1)) (le_refl _) (by omega) (by decide) acc t hin
      have H' := Verify.GoodQ.steps hst H
      rw [ec]
      refine H'.mono ?_ ?_ (fun h => ⟨h,?_⟩) <;> omega
theorem groups_zero (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0) {v : Digest} (he : Encoded v s0) (hf : c.Fit v)
    (hv : v.toNat<2^125) (n : Nat) (hn : n ≤ 17) (hn1 : 1 ≤ n) (hval : ∀ q, q<n → Search.topRank v q<125)
    (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ acc t,c.EndInv (set24 s0 (c.s8v (n-1))) (3*(n-1)+2) acc t → Verify.GoodQ t N C Q A (K acc))
    (s : MachineState) (hs : c.GroupIn s0 0 [] s) :
    Verify.GoodQ s (N+126*n) (C+c.chainsCost 0 (3*n)+5*n-3) Q (A+c.chainsCost 0 (3*n)+5*n-3)
      (Verify.ccM ((List.range' 0 (3*n)).foldlM c.chainF []) K) := by
  obtain ⟨t,hst,hin⟩ := c.guard_ok hc hds hk he hv [] s hs
  have hkB := set24_known c (c.s8v 0) hk
  have h0B := set24_orig c (c.s8v 0) h0
  have heB := set24_encoded (c.s8v 0) he
  obtain ⟨m,rfl⟩ : ∃m,n=m+1 := ⟨n-1,by omega⟩
  rw [show 3*(m+1)=3+3*m by ring,← List.range'_append_1,List.foldlM_append,Verify.ccM_bind]
  have ec := c.chainsCost_add' 0 3 (3*m)
  by_cases hm0 : m=0
  · subst hm0
    have H := c.group_good hc hds hkB h0B 0 (by omega) K N C A Q (by simpa using hK)
      3 0 (le_refl _) (by omega) (by decide) [] t (by simpa using hin)
    have H' := Verify.GoodQ.steps hst H
    simp only [Nat.mul_zero,Nat.add_zero,List.range'_zero,List.foldlM_nil,bind_pure,Verify.ccM_pure] at H' ⊢
    refine H'.mono ?_ ?_ (fun h => ⟨h,?_⟩) <;> omega
  · have H := c.group_good hc hds hkB h0B 0 (by omega)
      (fun ends => Verify.ccM ((List.range' (0+3) (3*m)).foldlM c.chainF ends) K)
      (N+126*m+4) (C+c.chainsCost 3 (3*m)+5*m-4+4) (A+c.chainsCost 3 (3*m)+5*m-4+4) Q
      (fun ends u hu => by
        obtain ⟨u',st,hu'⟩ := c.end_dispatch hc hds heB hf 0 (by omega) (hval 1 (by omega)) ends u hu
        have H := c.groups_from hc hds hk h0 he hf (m+1) hn hval K N C A Q hK m 1 (le_refl _) (by omega)
          (by omega) ends u' (by simpa using hu')
        simp only [Nat.mul_one] at H
        refine (Verify.GoodQ.steps st H).mono ?_ ?_ (fun h => ⟨h,?_⟩) <;> omega)
      3 0 (le_refl _) (by omega) (by decide) [] t (by simpa using hin)
    have H' := Verify.GoodQ.steps hst H
    simp only [Nat.zero_add] at H' ec ⊢
    rw [ec]
    refine H'.mono ?_ ?_ (fun h => ⟨h,?_⟩) <;> omega
def topP (c : NCtx) : M (List Digest) := (List.range' 0 54).foldlM c.chainF []
def TopOut (c : NCtx) (s0 : MachineState) (acc : List Digest) (s : MachineState) : Prop :=
  (∀ x, x ∉ chainRegs → x ≠ .x15 → x ≠ .x24 → s.getReg x=s0.getReg x) ∧
  Frame s0 s (c.Wr 54) ∧ acc.length=54 ∧
  (∀ j < acc.length, DigAt s (slot j) (acc.getD j 0)) ∧
  (∃ dB dC, dB < 4 ∧ dC < 4 ∧ s.pc = pcOf (pcX 17 dB dC)) ∧ s.getReg .x15 = 712704#64 ∧
  s.getReg .x24=c.s8v 17
theorem end_return (c : NCtx) (hds : c.DigitsOk) {s0 b : MachineState}
    (hb : b.getReg .x15 = 712704#64)
    (acc : List Digest) (s : MachineState)
    (hs : c.EndInv (set24 (tailInitial (set24 s0 (c.s8v 16)) b) (c.s8v 17)) 53 acc s) :
    c.TopOut s0 acc s := by
  obtain ⟨⟨hR,hF,hS⟩,hlen,hpc⟩ := hs
  have hB := c.dig_group_le hds 17 1 (by decide) (by decide)
  have hC := c.dig_group_le hds 17 2 (by decide) (by decide)
  have hreg : ∀ x, x ∉ chainRegs → x ≠ .x15 → x ≠ .x24 → s.getReg x=s0.getReg x := by
    intro x hx h15 h24
    rw [hR x hx,set24_regs _ _ _ h24,tailInitial_regs _ _ _ h15,set24_regs _ _ _ h24]
  refine ⟨hreg,?_,hlen,fun j hj => hS j hj,?_,?_,?_⟩
  · intro A hA hn
    exact (hF A hA hn).trans (by rw [set24_mem,tailInitial_mem,set24_mem])
  · refine ⟨c.dig 52, c.dig 53, ?_, ?_, ?_⟩
    · simpa [mx] using Nat.lt_succ_of_le hB
    · simpa [mx] using Nat.lt_succ_of_le hC
    · rw [hpc]
      have eB := c.gB_noninl hds 17 (by decide) (by decide)
      have eC : gC 17 (c.kOf 17) = pcC 17 (c.dig 52) (c.dig 53) := by rw [c.gC_eq hds 17 (by decide), eB]; rfl
      have eE : c.endPc 53 = gX 17 (c.kOf 17) := by simp [endPc, qX]
      rw [eE, c.gX_eq hds 17 (by decide), eC]; rfl
  · rw [hR .x15 (by decide),set24_regs _ _ _ (by decide),tailInitial_15,hb]
  · rw [hR .x24 (by decide),set24_24]
theorem top_full (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0) {v : Digest} (he : Encoded v s0) (hf : c.Fit v)
    (hv : v.toNat<2^125) (hval : ∀ q, q<17 → Search.topRank v q<125)
    (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ acc t,c.TopOut s0 acc t → Verify.GoodQ t N C Q A (K acc))
    (s : MachineState) (hs : c.GroupIn s0 0 [] s) :
    Verify.GoodQ s (N+2268) (C+c.chainsCost 0 54+86) Q (A+c.chainsCost 0 54+86) (Verify.ccM c.topP K) := by
  unfold topP
  rw [show (54:Nat)=3*17+3 from rfl,← List.range'_append_1,List.foldlM_append,Verify.ccM_bind]
  have ec := c.chainsCost_add' 0 (3*17) 3
  have H := c.groups_zero hc hds hk h0 he hf hv 17 (le_refl _) (by decide) hval
    (fun ends => Verify.ccM ((List.range' (0+3*17) 3).foldlM c.chainF ends) K)
    (N+126) (C+c.chainsCost 51 3+4) (A+c.chainsCost 51 3+4) Q
    (fun acc t ht => by
      obtain ⟨u,st,hu,hu15⟩ := c.end_tail hc hds (set24_encoded _ he) hf hv acc t (by simpa using ht)
      have h24 : (tailInitial (set24 s0 (c.s8v 16)) u).getReg .x24=c.s8v 16 := by
        rw [tailInitial_regs _ _ _ (by decide),set24_24]
      obtain ⟨u2,st2,hu2⟩ := c.entry_step hc hds 16 (by decide) h24 acc u hu
      have hkB : ∀p∈c.known,(set24 (tailInitial (set24 s0 (c.s8v 16)) u) (c.s8v 17)).getReg p.1=p.2 :=
        set24_known c _ (tailInitial_known c (set24_known c _ hk))
      have h0B := set24_orig c (c.s8v 17) (tailInitial_orig c (t := u) (set24_orig c (c.s8v 16) h0))
      have H := c.group_good hc hds hkB h0B 17 (by decide) K N C A Q
        (fun ends z hz => hK ends z (c.end_return hds hu15 ends z hz))
        3 51 (by decide) (by decide) (by decide) acc u2 (by simpa using hu2)
      have H2 := Verify.GoodQ.steps st (Verify.GoodQ.steps st2 H)
      simp only [Nat.zero_add]
      refine H2.mono ?_ ?_ (fun h => ⟨h,?_⟩) <;> omega)
    s hs
  simp only [Nat.zero_add] at H ec ⊢
  rw [show (3*17 : Nat)=51 from rfl] at ec H ⊢
  rw [ec]
  refine H.mono ?_ ?_ (fun h => ⟨h,?_⟩) <;> omega
theorem goodQ_vacuous {s : MachineState} {N C A : Nat} {X : OracleComp Legacy.HashSpec Verify.Obs}
    (h : Verify.GoodQ s N C False A X) (Q' : Prop) (A' : Nat) : Verify.GoodQ s N C Q' A' X := by
  intro F hF
  obtain ⟨h1,h2⟩ := h F hF
  exact ⟨h1,fun hash => ⟨(h2 hash).1,(h2 hash).2.1,fun hs hok => ((h2 hash).2.2 hs hok).1.elim⟩⟩
theorem top_bad_group (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0) {v : Digest} (he : Encoded v s0) (hf : c.Fit v)
    (hv : v.toNat<2^125) (j : Nat) (hj1 : 1 ≤ j) (hj : j ≤ 16) (hval : ∀ q, q<j → Search.topRank v q<125)
    (hbad : 125 ≤ Search.topRank v j) (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs)
    (hK : ∀ acc, K acc=pure (false,0)) (Q : Prop) (A : Nat)
    (s : MachineState) (hs : c.GroupIn s0 0 [] s) :
    Verify.GoodQ s (126*j+9) (c.chainsCost 0 (3*j)+5*j+6) Q A
      (Verify.ccM ((List.range' 0 (3*j)).foldlM c.chainF []) K) := by
  refine goodQ_vacuous (A := 0+c.chainsCost 0 (3*j)+5*j-3) ?_ Q A
  have H := c.groups_zero hc hds hk h0 he hf hv j (by omega) hj1 hval K 9 9 0 False
    (fun acc t ht => by
      rw [hK acc]
      obtain ⟨u,st,-,-,pu⟩ := c.end_dispatch_raw hc hds (set24_encoded _ he) (j-1) (by omega) acc t ht
      rw [show j-1+1=j by omega] at pu
      have hr : Search.topRank v j<128 := by unfold Search.topRank; omega
      obtain ⟨z,stz,pz⟩ := row_rej j (Search.topRank v j) (by omega) hbad hr u pu
      obtain ⟨z',stz',fz,h5,h10⟩ := Verify.Nonbinary.reject_halt z pz
      have R := Verify.GoodQ.reject (Q := False) (A := 0) fz h5 h10
      refine (Verify.GoodQ.steps st (Verify.GoodQ.steps stz (Verify.GoodQ.steps stz' R))).mono ?_ ?_ ?_
      · omega
      · omega
      · intro h; exact h.elim)
    s hs
  exact H.mono (by omega) (by omega) (fun h => ⟨h,le_refl _⟩)
end SigGolfCandidate.T3M.Nonbinary.NCtx
end
end
