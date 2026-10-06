import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsDispatchArith
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsGoodOne

section




section
namespace SigGolfCandidate.T3M.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
def sourceWord (v : Digest) (q : Nat) : Word := if q<9 then v.extractLsb' 0 64 else v.extractLsb' 64 64
def sourceBit (q : Nat) : Nat := if q<9 then 7*q else 7*q-64
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
theorem source_field (v : Digest) (q : Nat) (hq : q<17) (h9 : q≠9) :
    (sourceWord v q).toNat/2^(sourceBit q)%128=Search.topRank v q := by
  unfold sourceWord sourceBit Search.topRank
  split_ifs with h
  · simpa using extract_field v 0 (7*q) (by omega)
  · rw [extract_field v 64 (7*q-64) (by omega),show 64+(7*q-64)=7*q by omega]
theorem sourceBit_lt (q : Nat) (hq : q<17) (h9 : q≠9) : sourceBit q+7 ≤ 64 := by
  unfold sourceBit; split_ifs <;> omega
theorem dispatch_step {p q : Nat} (hq : q<17) (h9 : q≠9) (hp : p<251927)
    (hrun : vrun p 5=some (dispatchR q)) (s : MachineState) (v : Digest)
    (hpc : s.pc=pcOf p) (h16 : s.getReg .x16= ~~~(v.extractLsb' 0 64))
    (h17 : s.getReg .x17= ~~~(v.extractLsb' 64 64)) (h6 : s.getReg .x6=130048#64) :
    ∃t, Steps Images.verifyImage s 3 3 t ∧
      t.pc=BitVec.ofNat 64 (1024*(127-Search.topRank v q)+1024+4*entOff q) ∧
      RegsExcept s t [.x14] ∧ Frame s t (fun _ => False) := by
  have hW : s.getReg (if q<9 then .x16 else .x17)= ~~~(sourceWord v q) := by
    unfold sourceWord
    split_ifs <;> assumption
  have hb := sourceBit_lt q hq h9
  refine ⟨(dispatchR q).toState s,piece_steps45 hrun hp s hpc (by simp [dispatchR]),?_,?_,?_⟩
  · change (((shift10 (if q<9 then .x16 else .x17) (sourceBit q)).eval s &&& s.getReg .x6)+
      BitVec.ofNat 64 (1024+4*entOff q)) &&& ~~~1#64=_
    rw [h6,shift10_eval s _ _ hW _ (by omega),dispatch_value _ _ q (by omega) hq,not_field _ _ hb,
      source_field v q hq h9]
  · intro r hr
    rw [Result.toState_getReg]
    simp only [dispatchR]
    rw [RegFile.get_set_ne _ _ (show r≠.x14 by simpa using hr),RegFile.init_get_eval]
  · intro A _ _
    simp [dispatchR,rv_simp]
theorem dispatch9_step {p : Nat} (hp : p<251927)
    (hrun : vrun p 5=some dispatch9R) (s : MachineState) (v : Digest)
    (hpc : s.pc=pcOf p) (h17 : s.getReg .x17= ~~~(v.extractLsb' 64 64)) (h6 : s.getReg .x6=130048#64)
    (h15 : s.getReg .x15=4096#64) :
    ∃t, Steps Images.verifyImage s 4 4 t ∧
      t.pc=BitVec.ofNat 64 (2048*(63-v.toNat/2^64%64)+2300) ∧
      RegsExcept s t [.x14] ∧ Frame s t (fun _ => False) := by
  refine ⟨dispatch9R.toState s,piece_steps45 hrun hp s hpc (by simp [dispatch9R]),?_,?_,?_⟩
  · change ((((s.getReg .x17 <<< (BitVec.ofNat 64 11).toNat) &&& s.getReg .x6)+s.getReg .x15)+
      BitVec.ofNat 64 (2^64-1796)) &&& ~~~1#64=_
    rw [h6,h15,h17,g9_value]
    congr 2
    have := not_field (v.extractLsb' 64 64) 0 (by decide)
    have e1 : (~~~(v.extractLsb' 64 64)).toNat%64=((~~~(v.extractLsb' 64 64)).toNat/2^0%128)%64 := by
      simp [Nat.mod_mod_of_dvd _ (show 64 ∣ 128 by decide)]
    have e2 : v.toNat/2^64%64=((v.extractLsb' 64 64).toNat/2^0%128)%64 := by
      rw [extract_field v 64 0 (by decide)]
      simp [Nat.mod_mod_of_dvd _ (show 64 ∣ 128 by decide)]
    rw [e1,e2,this]
    have hlt : (v.extractLsb' 64 64).toNat/2^0%128 < 128 := Nat.mod_lt _ (by decide)
    omega
  · intro r hr
    rw [Result.toState_getReg]
    simp only [dispatch9R]
    rw [RegFile.get_set_ne _ _ (show r≠.x14 by simpa using hr),RegFile.init_get_eval]
  · intro A _ _
    simp [dispatch9R,rv_simp]
theorem bge9_step (k : Nat) (hk : k<125) (he : k%2=0) (s : MachineState) (v : Digest)
    (hpc : s.pc=pcOf (cellW 9 k)) (h16 : s.getReg .x16= ~~~(v.extractLsb' 0 64)) :
    ∃t, Steps Images.verifyImage s 1 1 t ∧
      t.pc=(if v.toNat/2^63%2=1 then BitVec.ofNat 64 (0x1000+4*cellW 9 k-1024) else pcOf (cellW 9 k+1)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := bge9_at k hk he
  have hp : cellW 9 k<251927 := by unfold cellW entOff; simp; omega
  refine ⟨(bge9R (cellW 9 k)).toState s,piece_steps45 hrun hp s hpc (by simp [bge9R,SymState.init]),?_,?_,?_⟩
  · rw [Result.toState_pc]
    simp only [bge9R,E.eval,h16]
    have hb : v.getLsbD 63=decide (v.toNat/2^63%2=1) := by
      rw [← BitVec.testBit_toNat, Nat.testBit_eq_decide_div_mod_eq]
    have hsign : CmpOp.eval .ge (~~~(v.extractLsb' 0 64)) 0=decide (v.toNat/2^63%2=1) := by
      have hz : (0 : BitVec 64)=0#64 := rfl
      simp only [CmpOp.eval]
      rw [hz, BitVec.slt_zero_eq_msb, BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_not, BitVec.getLsbD_extractLsb', hb]
      simp
    rw [hsign]
    by_cases hb' : v.toNat/2^63%2=1 <;> simp [hb']
  · intro r _; rw [Result.toState_getReg]; simp [bge9R,SymState.init,RegFile.init_get_eval]
  · intro A _ _
    simp [bge9R,rv_simp,SymState.init]
theorem tail_dispatch_step {p : Nat} (hp : p<251927)
    (hrun : vrun p 5=some tailDispatchR) (s : MachineState) (k : Nat) (hk : k<64)
    (hpc : s.pc=pcOf p) (h29 : s.getReg .x29=BitVec.ofNat 64 k)
    (h15 : s.getReg .x15=4096#64) :
    ∃t, Steps Images.verifyImage s 3 3 t ∧ t.pc=pcOf (entW 17 k) ∧
      RegsExcept s t [.x14,.x15] ∧ Frame s t (fun _ => False) ∧ t.getReg .x15 = 4096#64 := by
  refine ⟨tailDispatchR.toState s,piece_steps45 hrun hp s hpc
    (by simp [tailDispatchR,TailDispatch.dispatchR]),?_,?_,?_,?_⟩
  · simp only [Result.toState_pc,tailDispatchR,TailDispatch.dispatchR,E.eval,BinOp.eval,h29,h15]
    change (((BitVec.ofNat 64 k <<< 10)+4096#64+1024#64) &&& ~~~1#64) = _
    have he : entW 17 k=TailDispatch.armPC k := by unfold entW cellW TailDispatch.armPC; simp
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
#print axioms dispatch9_step
#print axioms bge9_step
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
  lo : s.getReg .x16= ~~~(v.extractLsb' 0 64)
  hi : s.getReg .x17= ~~~(v.extractLsb' 64 64)
  tail : s.getReg .x29=BitVec.ofNat 64 (v.toNat/2^119)
  mask : s.getReg .x6=130048#64
  table : s.getReg .x15=4096#64
theorem dispatch_at (c : NCtx) (hds : c.DigitsOk) (q : Nat) (hq : q<17) :
    vrun (c.endPc (3*q+2)) 5=some (if q=8 then dispatch9R else if q<16 then dispatchR (q+1) else tailDispatchR) := by
  have h := (c.groupFacts hds q (by omega)).disp hq
  have eq : (3*q+2)/3=q := by omega
  simpa only [endPc,qX,eq,show (3*q+2)%3=2 by omega,if_false,Nat.reduceEqDiff] using h
def GroupIn (c : NCtx) (s0 : MachineState) (q : Nat) (acc : List Digest) (s : MachineState) : Prop :=
  c.Base s0 (c.Wr (3*q)) acc s ∧ acc.length=3*q ∧ s.pc=pcOf (c.entPc q)
def dsp (j : Nat) : Nat := if j=9 then 5 else 3
theorem fetch_fault (s : MachineState) (h : s.pc.toNat<0x1000) : fetch vimage s=none := by
  unfold fetch; simp [h]
def DispOut (c : NCtx) (s0 : MachineState) (v : Digest) (q : Nat) (acc : List Digest) (s : MachineState) : Prop :=
  (Search.topRank v (q+1)<125 → ∃t,Steps vimage s (dsp (q+1)) (dsp (q+1)) t ∧
      c.Base s0 (c.Wr (3*(q+1))) acc t ∧ acc.length=3*(q+1) ∧ t.pc=pcOf (entW (q+1) (Search.topRank v (q+1)))) ∧
  (125 ≤ Search.topRank v (q+1) → ∃k t,Steps vimage s k k t ∧ k ≤ 5 ∧ fetch vimage t=none)
theorem topRank_lt (v : Digest) (q : Nat) : Search.topRank v q<128 := by
  unfold Search.topRank; omega
theorem topRank9 (v : Digest) : Search.topRank v 9=v.toNat/2^63%2+2*(v.toNat/2^64%64) := by
  unfold Search.topRank
  rw [show 7*9=63 from rfl]
  have h : v.toNat/2^64=v.toNat/2^63/2 := by rw [Nat.div_div_eq_div_mul, ← pow_succ]
  rw [h]; omega
theorem end_dispatch_raw (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState} {v : Digest}
    (he : Encoded v s0) (q : Nat) (hq : q<16) (acc : List Digest) (s : MachineState)
    (hs : c.EndInv s0 (3*q+2) acc s) : c.DispOut s0 v q acc s := by
  obtain ⟨⟨hR,hF,hS⟩,hlen,hpc⟩ := hs
  have hr := c.dispatch_at hds q (by omega)
  have hbound : c.endPc (3*q+2)<251927 := by
    have := c.qX_lt hds (3*q+2) (by omega)
    simp only [endPc,show (3*q+2)%3=2 by omega,if_false,Nat.reduceEqDiff]; omega
  have h16 : s.getReg .x16= ~~~(v.extractLsb' 0 64) := (hR _ (by decide)).trans he.lo
  have h17 : s.getReg .x17= ~~~(v.extractLsb' 64 64) := (hR _ (by decide)).trans he.hi
  have h6 : s.getReg .x6=130048#64 := (hR _ (by decide)).trans he.mask
  have h15 : s.getReg .x15=4096#64 := (hR _ (by decide)).trans he.table
  have base_of : ∀ t, RegsExcept s t [.x14] → Frame s t (fun _ => False) →
      c.Base s0 (c.Wr (3*(q+1))) acc t := by
    intro t rt ft
    refine ⟨fun x hx => ?_,(hF.trans ft).mono (by intro A hA h;rcases h with h|h;simpa only [show 3*q+2+1=3*(q+1) by omega] using h;contradiction),fun j hj => ?_⟩
    · rw [rt.get (by intro h;simp only [List.mem_singleton] at h;subst x;exact hx (by decide))]
      exact hR x hx
    · exact (hS j hj).frame ft (by have := slot_props j (by omega);omega) (by simp) (by simp)
  unfold DispOut
  by_cases h8 : q=8
  · subst q
    rw [if_pos rfl] at hr
    obtain ⟨t,st,pt,rt,ft⟩ := dispatch9_step hbound hr s v hpc h17 h6 h15
    have hr9 : Search.topRank v (8+1)=v.toNat/2^63%2+2*(v.toNat/2^64%64) := topRank9 v
    have hd9 : dsp (8+1)=5 := rfl
    rw [hr9,hd9]
    have hb2 : v.toNat/2^63%2<2 := Nat.mod_lt _ (by decide)
    have hu : v.toNat/2^64%64<64 := Nat.mod_lt _ (by decide)
    by_cases hu63 : v.toNat/2^64%64=63
    ·
      refine ⟨fun hv => by omega,fun _ => ⟨4,t,st,by omega,fetch_fault t ?_⟩⟩
      rw [pt,hu63]; exact g9_fault
    · set u := v.toNat/2^64%64 with hudef
      have hpc9 : t.pc=pcOf (cellW 9 (2*u)) := by rw [pt]; exact g9_cell u (by omega)
      have h16t : t.getReg .x16= ~~~(v.extractLsb' 0 64) := (rt.get (by decide)).trans h16
      obtain ⟨z,sz,pz,rz,fz⟩ := bge9_step (2*u) (by omega) (by omega) t v hpc9 h16t
      have rtz : RegsExcept s z [.x14] := fun x hx => (rz.get (by simp)).trans (rt x hx)
      have ftz : Frame s z (fun _ => False) := (ft.trans fz).mono (by intro A _ h; simpa using h)
      have st5 : Steps vimage s 5 5 z := st.trans sz
      by_cases hb : v.toNat/2^63%2=1
      · rw [if_pos hb] at pz
        rw [hb]
        by_cases hu62 : u=62
        · refine ⟨fun hv => by omega,fun _ => ⟨5,z,st5,le_refl _,fetch_fault z ?_⟩⟩
          rw [pz,hu62]; unfold cellW entOff; decide
        · refine ⟨fun _ => ⟨z,st5,base_of z rtz ftz,by omega,?_⟩,fun hv => by omega⟩
          rw [pz]
          have he9 : entW (8+1) (1+2*u)=cellW 9 (1+2*u) := by
            unfold entW; rw [if_neg (by omega)]; rfl
          rw [he9]
          unfold pcOf cellW entOff
          simp only [show (9:Nat)<17 by decide, if_true, show ¬ (9:Nat)=14 by decide, show ¬ (9:Nat)=15 by decide,
            show ¬ (9:Nat)=16 by decide, if_false]
          congr 1; omega
      · have hb0 : v.toNat/2^63%2=0 := by omega
        rw [if_neg hb] at pz
        rw [hb0]
        refine ⟨fun _ => ⟨z,st5,base_of z rtz ftz,by omega,?_⟩,fun hv => by omega⟩
        rw [pz]
        have he9 : entW (8+1) (0+2*u)=cellW 9 (2*u)+1 := by
          unfold entW; rw [if_pos (by omega)]; simp
        rw [he9]
  · have hq' : q<16 := hq
    rw [if_neg h8,if_pos hq'] at hr
    obtain ⟨t,st,pt,rt,ft⟩ := dispatch_step (by omega) (by omega) hbound hr s v hpc h16 h17 h6
    have hd : dsp (q+1)=3 := by unfold dsp; rw [if_neg (by omega)]
    rw [hd]
    have hk := topRank_lt v (q+1)
    refine ⟨fun hv => ⟨t,st,base_of t rt ft,by omega,?_⟩,fun hv => ⟨3,t,st,by omega,fetch_fault t ?_⟩⟩
    · rw [pt,cell_value _ _ (by omega) (by omega)]
      unfold entW; rw [if_neg (by omega)]; rfl
    · rw [pt]; exact fault_value _ _ (by omega) hv hk
theorem end_dispatch (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState} {v : Digest}
    (he : Encoded v s0) (hf : c.Fit v) (q : Nat) (hq : q<16) (hv : Search.topRank v (q+1)<125)
    (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 (3*q+2) acc s) :
    ∃t,Steps vimage s (dsp (q+1)) (dsp (q+1)) t ∧ c.GroupIn s0 (q+1) acc t := by
  obtain ⟨t,st,hB,hl,pt⟩ := (c.end_dispatch_raw hc hds he q hq acc s hs).1 hv
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
  rw [tailInitial_regs _ _ _ (by rcases p with ⟨r,w⟩;simp only [known,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hp;rcases hp with h|h|h|h|h|h|h|h|h|h|h|h|h <;> obtain ⟨rfl,_⟩ := h <;> simp)]
  exact hk p hp
theorem tailInitial_orig (c : NCtx) {s0 t : MachineState} (h0 : c.Orig0 s0) :
    c.Orig0 (tailInitial s0 t) := by
  refine ⟨fun i hi k hk => h0.1 i hi k hk, h0.2.congr (fun A _ _ => tailInitial_mem s0 t _)⟩
theorem end_tail (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState} {v : Digest}
    (he : Encoded v s0) (hf : c.Fit v) (hv : v.toNat<2^125)
    (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 50 acc s) :
    ∃t,Steps vimage s 3 3 t ∧ c.GroupIn (tailInitial s0 t) 17 acc t ∧ t.getReg .x15 = 4096#64 := by
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
  rw [set24_regs _ _ _ (by rcases p with ⟨r,w⟩;simp only [known,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hp;rcases hp with h|h|h|h|h|h|h|h|h|h|h|h|h <;> obtain ⟨rfl,_⟩ := h <;> simp)]
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
  have hchk := s8Run_at (q+1) (c.kOf (q+1)) (by omega) (c.kOf_lt hds (q+1) (by omega))
  rw [if_neg (show q+1≠0 by omega)] at hchk
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
  have hchk := s8Run_at 0 (c.kOf 0) (by decide) (c.kOf_lt hds 0 (by decide))
  rw [if_pos rfl] at hchk
  have hrun := rOK_eq hchk
  have hp : entW 0 (c.kOf 0)<251927 := by
    have := (c.kOf_bounds hds 0 (by decide)).2 (by decide)
    unfold entW cellW entOff; simp; omega
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
    unfold startPc leadPc leadOff entW
    simp
theorem guard_rej (c : NCtx) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) {v : Digest} (he : Encoded v s0) (hv : 2^125 ≤ v.toNat)
    (acc : List Digest) (s : MachineState) (hs : c.GroupIn s0 0 acc s) :
    ∃t,Steps vimage s 3 3 t ∧ t.pc=pcOf 129638 := by
  obtain ⟨⟨hR,hF,hS⟩,hlen,hpc⟩ := hs
  have hchk := s8Run_at 0 (c.kOf 0) (by decide) (c.kOf_lt hds 0 (by decide))
  rw [if_pos rfl] at hchk
  have hrun := rOK_eq hchk
  have hk125 := (c.kOf_bounds hds 0 (by decide)).2 (by decide)
  have hp : entW 0 (c.kOf 0)<251927 := by unfold entW cellW entOff; simp; omega
  have hst := piece_steps45 hrun hp s hpc (by simp [guardR])
  have h29 : s.getReg .x29=BitVec.ofNat 64 (v.toNat/2^119) := (hR .x29 (by decide)).trans he.tail
  have h11 : s.getReg .x11=64#64 := (hR .x11 (by decide)).trans (hk (.x11,64) (by simp [known]))
  have hcond := guard_cond v
  set t := (guardR (c.kOf 0)).toState s with ht
  have hpt : t.pc=pcOf (guardW (c.kOf 0)) := by
    rw [ht,Result.toState_pc]
    simp only [guardR,E.eval,h29,h11,hcond,decide_eq_true hv,if_true]
  have hstub := stub_at (c.kOf 0) hk125
  have hst2 := piece_steps45 hstub (by unfold guardW; omega) t hpt (by intro o ho; simp [rejJ,SymState.init] at ho)
  refine ⟨rejJ.toState t,(hst.trans hst2).of_eq (by simp [guardR,rejJ]) (by simp [guardR,rejJ]),?_⟩
  rw [Result.toState_pc]; rfl
theorem goodQ_fault {s : MachineState} {Q : Prop} {A : Nat} (hf : fetch vimage s=none) :
    Verify.GoodQ s 1 0 Q A (pure (false, 0)) := by
  intro F hF
  have hF' : F=(F-1)+1 := by omega
  refine ⟨?_,fun hash => ?_⟩
  · rw [hF',execute_fetch_none (F-1) hf,map_pure]; rfl
  · have he : evalWithAnswerFn hash (Riscv.execute (F-1+1) vimage s)=⟨.failure,s,0,0,0⟩ := by
      rw [execute_fetch_none (F-1) hf]; rfl
    rw [hF',he]
    exact ⟨by simp,Nat.zero_le _,fun h _ => by simp at h⟩
def ov : Nat → Nat → Nat
  | _, 0 => 0
  | _, 1 => 1
  | q, k+2 => 1+dsp (q+1)+ov (q+1) (k+1)
theorem ov_succ (q k : Nat) (hk : 1 ≤ k) : ov q (k+1)=1+dsp (q+1)+ov (q+1) k := by
  obtain ⟨j,rfl⟩ : ∃j,k=j+1 := ⟨k-1,by omega⟩; rfl
theorem dsp_le (j : Nat) : dsp j ≤ 5 := by unfold dsp; split <;> omega
theorem groups_from (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0) {v : Digest} (he : Encoded v s0) (hf : c.Fit v)
    (n : Nat) (hn : n ≤ 17) (hval : ∀ q, q<n → Search.topRank v q<125)
    (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ acc t,c.EndInv (set24 s0 (c.s8v (n-1))) (3*(n-1)+2) acc t → Verify.GoodQ t N C Q A (K acc)) :
    ∀ k q, 1 ≤ q → q+k=n → 0<k → ∀ acc s,c.GroupIn (set24 s0 (c.s8v (q-1))) q acc s →
      Verify.GoodQ s (N+126*k) (C+c.chainsCost (3*q) (3*k)+ov q k) Q (A+c.chainsCost (3*q) (3*k)+ov q k)
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
      have h1 : ov (q'+1) (0+1)=1 := rfl
      refine H'.mono ?_ ?_ (fun h => ⟨h,?_⟩) <;> omega
    · have hov := ov_succ (q'+1) k (by omega)
      simp only [show q'+1+1=q'+2 from rfl] at hov
      have hd := dsp_le (q'+2)
      have H := c.group_good hc hds hkB h0B (q'+1) (by omega)
        (fun ends => Verify.ccM ((List.range' (3*(q'+1)+3) (3*k)).foldlM c.chainF ends) K)
        (N+126*k+dsp (q'+2)) (C+c.chainsCost (3*(q'+1)+3) (3*k)+ov (q'+2) k+dsp (q'+2))
        (A+c.chainsCost (3*(q'+1)+3) (3*k)+ov (q'+2) k+dsp (q'+2)) Q
        (fun ends u hu => by
          obtain ⟨u',st,hu'⟩ := c.end_dispatch hc hds heB hf (q'+1) (by omega) (hval (q'+2) (by omega)) ends u hu
          have e2 : dsp (q'+1+1)=dsp (q'+2) := rfl
          rw [e2] at st
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
    Verify.GoodQ s (N+126*n) (C+c.chainsCost 0 (3*n)+1+ov 0 n) Q (A+c.chainsCost 0 (3*n)+1+ov 0 n)
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
    have h1 : ov 0 (0+1)=1 := rfl
    refine H'.mono ?_ ?_ (fun h => ⟨h,?_⟩) <;> omega
  · have hov := ov_succ 0 m (by omega)
    simp only [Nat.zero_add] at hov
    have hd1 : dsp 1=3 := rfl
    have H := c.group_good hc hds hkB h0B 0 (by omega)
      (fun ends => Verify.ccM ((List.range' (0+3) (3*m)).foldlM c.chainF ends) K)
      (N+126*m+3) (C+c.chainsCost 3 (3*m)+ov 1 m+3) (A+c.chainsCost 3 (3*m)+ov 1 m+3) Q
      (fun ends u hu => by
        obtain ⟨u',st,hu'⟩ := c.end_dispatch hc hds heB hf 0 (by omega) (hval 1 (by omega)) ends u hu
        have H := c.groups_from hc hds hk h0 he hf (m+1) hn hval K N C A Q hK m 1 (le_refl _) (by omega)
          (by omega) ends u' (by simpa using hu')
        simp only [Nat.mul_one] at H
        have e1 : dsp (0+1)=3 := rfl
        rw [e1] at st
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
  (∃ dB dC, dB < 4 ∧ dC < 4 ∧ s.pc = pcOf (pcX 17 dB dC)) ∧ s.getReg .x15 = 4096#64 ∧
  s.getReg .x24=c.s8v 17
theorem end_return (c : NCtx) (hds : c.DigitsOk) {s0 b : MachineState}
    (hb : b.getReg .x15 = 4096#64)
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
    Verify.GoodQ s (N+2268) (C+c.chainsCost 0 54+72) Q (A+c.chainsCost 0 54+72) (Verify.ccM c.topP K) := by
  unfold topP
  rw [show (54:Nat)=3*17+3 from rfl,← List.range'_append_1,List.foldlM_append,Verify.ccM_bind]
  have ec := c.chainsCost_add' 0 (3*17) 3
  have hov : ov 0 17=67 := by decide
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
theorem ov_le (j : Nat) (hj : j ≤ 17) : ov 0 j ≤ 67 := by interval_cases j <;> decide
theorem top_bad_group (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0) {v : Digest} (he : Encoded v s0) (hf : c.Fit v)
    (hv : v.toNat<2^125) (j : Nat) (hj1 : 1 ≤ j) (hj : j ≤ 16) (hval : ∀ q, q<j → Search.topRank v q<125)
    (hbad : 125 ≤ Search.topRank v j) (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs)
    (hK : ∀ acc, K acc=pure (false,0)) (Q : Prop) (A : Nat)
    (s : MachineState) (hs : c.GroupIn s0 0 [] s) :
    Verify.GoodQ s (126*j+6) (c.chainsCost 0 (3*j)+1+ov 0 j+5) Q A
      (Verify.ccM ((List.range' 0 (3*j)).foldlM c.chainF []) K) := by
  refine goodQ_vacuous (A := 0+c.chainsCost 0 (3*j)+1+ov 0 j) ?_ Q A
  have H := c.groups_zero hc hds hk h0 he hf hv j (by omega) hj1 hval K 6 5 0 False
    (fun acc t ht => by
      rw [hK acc]
      have hb' : 125 ≤ Search.topRank v (j-1+1) := by rw [show j-1+1=j by omega]; exact hbad
      obtain ⟨k,z,stz,hk5,fz⟩ := (c.end_dispatch_raw hc hds (set24_encoded _ he) (j-1) (by omega) acc t ht).2 hb'
      have R := goodQ_fault (Q := False) (A := 0) fz
      refine (Verify.GoodQ.steps stz R).mono ?_ ?_ ?_
      · omega
      · omega
      · intro h; exact h.elim)
    s hs
  exact H.mono (by omega) (by omega) (fun h => ⟨h,le_refl _⟩)
end SigGolfCandidate.T3M.Nonbinary.NCtx
end
end
