import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsDispatchArith
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsGoodOne

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
def hiMask : Word := BitVec.ofNat 64 (2 ^ 64 - 2 ^ 55)
theorem field_xor_hiMask (X : Word) (b : Nat) (hb : b + 7 ≤ 55) :
    (X ^^^ hiMask).toNat / 2 ^ b % 128 = X.toNat / 2 ^ b % 128 := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [show (128 : Nat) = 2 ^ 7 by norm_num, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow, Nat.testBit_div_two_pow, BitVec.toNat_xor, Nat.testBit_xor]
  by_cases hj : j < 7
  · have hm : hiMask.toNat.testBit (j + b) = false := by
      unfold hiMask
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by norm_num),
        show (2 : Nat) ^ 64 - 2 ^ 55 = 2 ^ 55 * (2 ^ 9 - 1) by norm_num, Nat.testBit_two_pow_mul]
      simp; omega
    simp [hj, hm]
  · simp [hj]
theorem mod64_xor_hiMask (X : Word) : (X ^^^ hiMask).toNat % 64 = X.toNat % 64 := by
  have h := field_xor_hiMask X 0 (by decide +kernel)
  simp only [pow_zero, Nat.div_one] at h
  rw [← Nat.mod_mod_of_dvd (X ^^^ hiMask).toNat (show 64 ∣ 128 by decide +kernel), h,
    Nat.mod_mod_of_dvd _ (show 64 ∣ 128 by decide +kernel)]
theorem dispatch_step {p q : Nat} (hq : q<17) (h9 : q≠9) (hp : p<253807)
    (hrun : vrun p 5=some (dispatchR q)) (s : MachineState) (v : Digest)
    (hpc : s.pc=pcOf p) (h16 : s.getReg .x16= ~~~(v.extractLsb' 0 64))
    (h17 : s.getReg .x17= ~~~(v.extractLsb' 64 64) ^^^ hiMask) (h6 : s.getReg .x6=130048#64) :
    ∃t, Steps Images.verifyImage s 3 3 t ∧
      t.pc=BitVec.ofNat 64 (1024*(127-Search.topRank v q)+1024+4*entOff q) ∧
      RegsExcept s t [.x14] ∧ Frame s t (fun _ => False) := by
  have hW : s.getReg (if q<9 then .x16 else .x17)= ~~~(sourceWord v q) ^^^ (if q<9 then 0 else hiMask) := by
    unfold sourceWord
    split_ifs
    · rw [h16]; exact BitVec.xor_zero.symm
    · exact h17
  have hb := sourceBit_lt q hq h9
  have hf : (~~~(sourceWord v q) ^^^ (if q<9 then 0 else hiMask)).toNat/2^(sourceBit q)%128 =
      (~~~(sourceWord v q)).toNat/2^(sourceBit q)%128 := by
    split_ifs with h
    · rw [show (~~~(sourceWord v q) ^^^ (0 : Word)) = ~~~(sourceWord v q) from BitVec.xor_zero]
    · apply field_xor_hiMask
      unfold sourceBit; rw [if_neg h]; omega
  refine ⟨(dispatchR q).toState s,piece_steps45 hrun hp s hpc (by simp [dispatchR]),?_,?_,?_⟩
  · change (((shift10 (if q<9 then .x16 else .x17) (sourceBit q)).eval s &&& s.getReg .x6)+
      BitVec.ofNat 64 (1024+4*entOff q)) &&& ~~~1#64=_
    rw [h6,shift10_eval s _ _ hW _ (by omega),dispatch_value _ _ q (by omega) hq,hf,not_field _ _ hb,
      source_field v q hq h9]
  · intro r hr
    rw [Result.toState_getReg]
    simp only [dispatchR]
    rw [RegFile.get_set_ne _ _ (show r≠.x14 by simpa using hr),RegFile.init_get_eval]
  · intro A _ _
    simp [dispatchR,rv_simp]
theorem dispatch9_step {p : Nat} (hp : p<253807)
    (hrun : vrun p 5=some dispatch9R) (s : MachineState) (v : Digest)
    (hpc : s.pc=pcOf p) (h17 : s.getReg .x17= ~~~(v.extractLsb' 64 64) ^^^ hiMask) (h6 : s.getReg .x6=130048#64)
    (h15 : s.getReg .x2=0x3fe00#64) :
    ∃t, Steps Images.verifyImage s 4 4 t ∧
      t.pc=BitVec.ofNat 64 (2048*(63-v.toNat/2^64%64)+2300) ∧
      RegsExcept s t [.x14] ∧ Frame s t (fun _ => False) := by
  refine ⟨dispatch9R.toState s,piece_steps45 hrun hp s hpc (by simp [dispatch9R]),?_,?_,?_⟩
  · change (((s.getReg .x17 <<< (BitVec.ofNat 64 11).toNat) &&& s.getReg .x6)+2300#64) &&& ~~~1#64=_
    rw [h6,h17,g9_value,mod64_xor_hiMask]
    congr 2
    have := not_field (v.extractLsb' 64 64) 0 (by decide +kernel)
    have e1 : (~~~(v.extractLsb' 64 64)).toNat%64=((~~~(v.extractLsb' 64 64)).toNat/2^0%128)%64 := by
      simp [Nat.mod_mod_of_dvd _ (show 64 ∣ 128 by decide +kernel)]
    have e2 : v.toNat/2^64%64=((v.extractLsb' 64 64).toNat/2^0%128)%64 := by
      rw [extract_field v 64 0 (by decide +kernel)]
      simp [Nat.mod_mod_of_dvd _ (show 64 ∣ 128 by decide +kernel)]
    rw [e1,e2,this]
    have hlt : (v.extractLsb' 64 64).toNat/2^0%128 < 128 := Nat.mod_lt _ (by decide +kernel)
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
  have hp : cellW 9 k<253807 := by unfold cellW entOff; simp; omega
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
theorem tail_dispatch_step {p : Nat} (hp : p<253807)
    (hrun : vrun p 5=some tailDispatchR) (s : MachineState) (k : Nat) (hk : k<64)
    (hpc : s.pc=pcOf p) (h29 : s.getReg .x29=BitVec.ofNat 64 k)
    (h15 : s.getReg .x2=0x3fe00#64) :
    ∃t, Steps Images.verifyImage s 3 3 t ∧ t.pc=pcOf (entW 17 k) ∧
      RegsExcept s t [.x14,.x15] ∧ Frame s t (fun _ => False) ∧ t.getReg .x2 = 0x3fe00#64 := by
  refine ⟨tailDispatchR.toState s,piece_steps45 hrun hp s hpc
    (by simp [tailDispatchR,TailDispatch.dispatchR]),?_,?_,?_,?_⟩
  · simp only [Result.toState_pc,tailDispatchR,TailDispatch.dispatchR,E.eval,BinOp.eval,h29]
    change (((BitVec.ofNat 64 k + 5#64) <<< 10) &&& ~~~1#64) = _
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
    rw [RegFile.get_set_ne _ _ (by decide +kernel),RegFile.init_get_eval,h15]
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
theorem next_inline (c : NCtx) (s0 : MachineState) (i : Nat) (hi : i<51) (h2 : i%3≠2)
    (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 i acc s) :
    c.ChainIn s0 (i+1) acc s := by
  obtain ⟨hB,hlen,hpc⟩ := hs
  refine ⟨hB,hlen,?_⟩
  rw [hpc]
  unfold endPc startPc
  rw [if_pos hi, if_pos (show i+1<51 by omega)]
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
theorem next_51 (c : NCtx) (s0 : MachineState) (acc : List Digest) (s : MachineState)
    (hs : c.EndInv s0 51 acc s) : c.ChainIn s0 52 acc s := by
  obtain ⟨hB,hlen,hpc⟩ := hs
  refine ⟨hB,hlen,?_⟩
  rw [hpc]
  simp [endPc, startPc, r8Start]
theorem group_good (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0)
    (q : Nat) (hq : q<17) (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs)
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
def rawDigit (v : Digest) (i : Nat) : Nat :=
  if i < 51 then (v.toNat / 2 ^ (7 * (i / 3)) % 128) / 5 ^ (i % 3) % 5 else v.toNat / 2 ^ T3.topRawShift i % 8
def Fit (c : NCtx) (v : Digest) : Prop := ∀i,i<54 → c.dig i=rawDigit v i
theorem fit_digits (c : NCtx) {v : Digest} (hf : c.Fit v) : c.DigitsOk := by
  intro i hi
  rw [hf i hi]
  unfold rawDigit topMax mx
  by_cases h : i < 51
  · rw [if_pos h, if_pos (by omega)]; have := Nat.mod_lt ((v.toNat / 2 ^ (7 * (i / 3)) % 128) / 5 ^ (i % 3)) (show 0 < 5 by decide +kernel); omega
  · rw [if_neg h, if_neg (by omega)]; have := Nat.mod_lt (v.toNat / 2 ^ T3.topRawShift i) (show 0 < 8 by decide +kernel); omega
theorem raw_triple (v : Digest) (j k : Nat) (hj : j<17) (hk : k<3) :
    rawDigit v (3*j+k)=(v.toNat/2^(7*j)%128)/5^k%5 := by
  have hi : 3*j+k<51 := by omega
  have hd : (3*j+k)/3=j := by omega
  have hm : (3*j+k)%3=k := by omega
  simp [rawDigit,hi,hd,hm]
theorem fit_rank' (c : NCtx) {v : Digest} (hf : c.Fit v) (q : Nat) (hq : q<17) (hv : Search.topRank v q<125) :
    c.kOf q=Search.topRank v q := by
  unfold kOf
  rw [hf (3*q) (by omega),hf (3*q+1) (by omega),hf (3*q+2) (by omega)]
  have h0 := raw_triple v q 0 hq (by decide +kernel)
  have h1 := raw_triple v q 1 hq (by decide +kernel)
  have h2 := raw_triple v q 2 hq (by decide +kernel)
  simp only [Nat.add_zero] at h0
  rw [h0,h1,h2]
  simp only [mx,if_pos hq,Nat.reduceAdd,Nat.reducePow,Nat.div_one]
  unfold Search.topRank at hv ⊢
  omega
theorem fit_k17 (c : NCtx) {v : Digest} (hf : c.Fit v) : c.k17=v.toNat/2^122 := by
  have hv := v.isLt
  unfold k17
  rw [hf 51 (by decide +kernel),hf 52 (by decide +kernel)]
  norm_num [rawDigit,T3.topRawShift]
  omega
theorem fit_d53 (c : NCtx) {v : Digest} (hf : c.Fit v) : c.dig 53=v.toNat/2^119%8 := by
  rw [hf 53 (by decide +kernel)]
  norm_num [rawDigit,T3.topRawShift]
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
  hi : s.getReg .x17= ~~~(v.extractLsb' 64 64) ^^^ hiMask
  tail : s.getReg .x29=BitVec.ofNat 64 (v.toNat/2^122)
  mask : s.getReg .x6=130048#64
  table : s.getReg .x2=0x3fe00#64
theorem dispatch_at (c : NCtx) (hds : c.DigitsOk) (q : Nat) (hq : q<17) :
    vrun (c.endPc (3*q+2)) 5=some (if q=8 then dispatch9R else if q<16 then dispatchR (q+1) else tailDispatchR) := by
  have h := (c.groupFacts hds q (by omega)).disp hq
  have eq : (3*q+2)/3=q := by omega
  simpa only [endPc,qX,eq,show 3*q+2<51 by omega,if_true,show (3*q+2)%3=2 by omega,if_false,Nat.reduceEqDiff] using h
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
  have hbound : c.endPc (3*q+2)<253807 := by
    have := c.qX_lt hds (3*q+2) (by omega)
    simp only [endPc,show 3*q+2<51 by omega,if_true,show (3*q+2)%3=2 by omega,if_false,Nat.reduceEqDiff]; omega
  have h16 : s.getReg .x16= ~~~(v.extractLsb' 0 64) := (hR _ (by decide +kernel)).trans he.lo
  have h17 : s.getReg .x17= ~~~(v.extractLsb' 64 64) ^^^ hiMask := (hR _ (by decide +kernel)).trans he.hi
  have h6 : s.getReg .x6=130048#64 := (hR _ (by decide +kernel)).trans he.mask
  have h15 : s.getReg .x2=0x3fe00#64 := (hR _ (by decide +kernel)).trans he.table
  have base_of : ∀ t, RegsExcept s t [.x14] → Frame s t (fun _ => False) →
      c.Base s0 (c.Wr (3*(q+1))) acc t := by
    intro t rt ft
    refine ⟨fun x hx => ?_,(hF.trans ft).mono (by intro A hA h;rcases h with h|h;simpa only [show 3*q+2+1=3*(q+1) by omega] using h;contradiction),fun j hj => ?_⟩
    · rw [rt.get (by intro h;simp only [List.mem_singleton] at h;subst x;exact hx (by decide +kernel))]
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
    have hb2 : v.toNat/2^63%2<2 := Nat.mod_lt _ (by decide +kernel)
    have hu : v.toNat/2^64%64<64 := Nat.mod_lt _ (by decide +kernel)
    by_cases hu63 : v.toNat/2^64%64=63
    ·
      refine ⟨fun hv => by omega,fun _ => ⟨4,t,st,by omega,fetch_fault t ?_⟩⟩
      rw [pt,hu63]; exact g9_fault
    · set u := v.toNat/2^64%64 with hudef
      have hpc9 : t.pc=pcOf (cellW 9 (2*u)) := by rw [pt]; exact g9_cell u (by omega)
      have h16t : t.getReg .x16= ~~~(v.extractLsb' 0 64) := (rt.get (by decide +kernel)).trans h16
      obtain ⟨z,sz,pz,rz,fz⟩ := bge9_step (2*u) (by omega) (by omega) t v hpc9 h16t
      have rtz : RegsExcept s z [.x14] := fun x hx => (rz.get (by simp)).trans (rt x hx)
      have ftz : Frame s z (fun _ => False) := (ft.trans fz).mono (by intro A _ h; simpa using h)
      have st5 : Steps vimage s 5 5 z := st.trans sz
      by_cases hb : v.toNat/2^63%2=1
      · rw [if_pos hb] at pz
        rw [hb]
        by_cases hu62 : u=62
        · refine ⟨fun hv => by omega,fun _ => ⟨5,z,st5,le_refl _,fetch_fault z ?_⟩⟩
          rw [pz,hu62]; unfold cellW entOff; decide +kernel
        · refine ⟨fun _ => ⟨z,st5,base_of z rtz ftz,by omega,?_⟩,fun hv => by omega⟩
          rw [pz]
          have he9 : entW (8+1) (1+2*u)=cellW 9 (1+2*u) := by
            unfold entW; rw [if_neg (by omega)]; rfl
          rw [he9]
          unfold pcOf cellW entOff
          simp only [show (9:Nat)<17 by decide +kernel, if_true, show ¬ (9:Nat)=14 by decide +kernel, show ¬ (9:Nat)=15 by decide +kernel,
            show ¬ (9:Nat)=16 by decide +kernel, if_false]
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
  rw [setReg_of_ne s0 _ (by decide +kernel)]
  cases r <;> simp_all [MachineState.getReg]
theorem tailInitial_15 (s0 t : MachineState) :
    (tailInitial s0 t).getReg .x15=t.getReg .x15 := by
  unfold tailInitial
  rw [setReg_of_ne s0 _ (by decide +kernel)]
  rfl
theorem tailInitial_known (c : NCtx) {s0 t : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) :
    ∀p∈c.known,(tailInitial s0 t).getReg p.1=p.2 := by
  intro p hp
  rw [tailInitial_regs _ _ _ (by rcases p with ⟨r,w⟩;simp only [known,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hp;rcases hp with h|h|h|h|h|h|h|h|h|h|h <;> obtain ⟨rfl,_⟩ := h <;> simp)]
  exact hk p hp
theorem tailInitial_orig (c : NCtx) {s0 t : MachineState} (h0 : c.Orig0 s0) :
    c.Orig0 (tailInitial s0 t) := by
  refine ⟨fun i hi k hk => h0.1 i hi k hk, h0.2.congr (fun A _ _ => tailInitial_mem s0 t _)⟩
/-- Entry of group 17 (campaign T8D): pc at the top-field slot `256 (k17 + 1)`. -/
def R8In (c : NCtx) (s0 : MachineState) (acc : List Digest) (s : MachineState) : Prop :=
  c.Base s0 (c.Wr 51) acc s ∧ acc.length=51 ∧ s.pc=pcOf (256*(c.k17+1))
theorem end_tail (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState} {v : Digest}
    (he : Encoded v s0) (hf : c.Fit v)
    (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 50 acc s) :
    ∃t,Steps vimage s 3 3 t ∧ c.R8In (tailInitial s0 t) acc t ∧ t.getReg .x2 = 0x3fe00#64 := by
  obtain ⟨⟨hR,hF,hS⟩,hlen,hpc⟩ := hs
  have hr := c.dispatch_at hds 16 (by decide +kernel)
  norm_num at hr
  have hbound : c.endPc 50<253807 := by
    have := c.qX_lt hds 50 (by decide +kernel)
    simp only [endPc,show (50:Nat)<51 by decide,if_true,Nat.reduceMod,if_false,Nat.reduceEqDiff]; omega
  have hv := v.isLt
  obtain ⟨t,st,pt,rt,ft,r15⟩ := tail_dispatch_step hbound hr s (v.toNat/2^122) (by omega) hpc
    ((hR _ (by decide +kernel)).trans he.tail) ((hR _ (by decide +kernel)).trans he.table)
  refine ⟨t,st,⟨⟨fun x hx => ?_,?_,fun j hj => ?_⟩,by omega,?_⟩,r15⟩
  · by_cases hx15 : x=.x15
    · subst x;rw [tailInitial_15]
    · rw [tailInitial_regs _ _ _ hx15,rt.get (by simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,not_or];exact ⟨fun h => hx (by rw [h];decide),hx15⟩)]
      exact hR x hx
  · intro A hA hn
    rw [tailInitial_mem]
    exact ft.get hA (by simp) |>.trans (hF.get hA hn)
  · exact (hS j hj).frame ft (by have := slot_props j (by omega);omega) (by simp) (by simp)
  · rw [pt, c.fit_k17 hf]
    simp [entW, cellW]
def s8v (c : NCtx) (q : Nat) : Word := BitVec.ofNat 64 (((List.range (3*q+3)).map c.dig).sum)-144#64
def set24 (b : MachineState) (x : Word) : MachineState := b.setReg .x24 x
theorem set24_regs (b : MachineState) (x : Word) (r : Reg) (hr : r≠.x24) : (set24 b x).getReg r=b.getReg r := by
  unfold set24
  rw [setReg_of_ne b _ (by decide +kernel)]
  cases r <;> simp_all [MachineState.getReg]
theorem set24_24 (b : MachineState) (x : Word) : (set24 b x).getReg .x24=x := by
  unfold set24
  rw [setReg_of_ne b _ (by decide +kernel)]
  rfl
theorem set24_mem (b : MachineState) (x : Word) (a : Word) : (set24 b x).getMem a=b.getMem a := rfl
theorem set24_known (c : NCtx) {b : MachineState} (x : Word) (hk : ∀p∈c.known,b.getReg p.1=p.2) :
    ∀p∈c.known,(set24 b x).getReg p.1=p.2 := by
  intro p hp
  rw [set24_regs _ _ _ (by rcases p with ⟨r,w⟩;simp only [known,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hp;rcases hp with h|h|h|h|h|h|h|h|h|h|h <;> obtain ⟨rfl,_⟩ := h <;> simp)]
  exact hk p hp
theorem set24_orig (c : NCtx) {b : MachineState} (x : Word) (h0 : c.Orig0 b) : c.Orig0 (set24 b x) :=
  ⟨fun i hi k hk => h0.1 i hi k hk, h0.2.congr (fun A _ _ => set24_mem b x _)⟩
theorem set24_encoded {v : Digest} {b : MachineState} (x : Word) (he : Encoded v b) : Encoded v (set24 b x) :=
  ⟨(set24_regs _ _ _ (by decide +kernel)).trans he.lo,(set24_regs _ _ _ (by decide +kernel)).trans he.hi,
    (set24_regs _ _ _ (by decide +kernel)).trans he.tail,(set24_regs _ _ _ (by decide +kernel)).trans he.mask,
    (set24_regs _ _ _ (by decide +kernel)).trans he.table⟩
theorem sum_range_three (f : Nat → Nat) (n : Nat) :
    ((List.range (n+3)).map f).sum=((List.range n).map f).sum+(f n+f (n+1)+f (n+2)) := by
  simp only [List.range_succ,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  omega
theorem kss_kOf (c : NCtx) (hds : c.DigitsOk) (q : Nat) (hq : q<17) :
    kss q (c.kOf q)=c.dig (3*q)+c.dig (3*q+1)+c.dig (3*q+2) := by
  obtain ⟨k1,k2,k3⟩ := c.kdig_kOf hds q (by omega)
  simp only [kss,k1,k2,k3]
theorem s8v_succ (c : NCtx) (hds : c.DigitsOk) (q : Nat) (hq : q<16) :
    c.s8v q+BitVec.ofNat 64 (kss (q+1) (c.kOf (q+1)))=c.s8v (q+1) := by
  have hS : ((List.range (3*(q+1)+3)).map c.dig).sum =
      ((List.range (3*q+3)).map c.dig).sum+kss (q+1) (c.kOf (q+1)) := by
    rw [c.kss_kOf hds (q+1) (by omega),show 3*(q+1)+3=(3*q+3)+3 by ring,sum_range_three]
    simp only [show 3*(q+1)=3*q+3 by ring]
  unfold s8v
  rw [hS,BitVec.ofNat_add]
  simp only [BitVec.sub_eq_add_neg]
  ac_rfl
theorem entry_step (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {b : MachineState} (q : Nat) (hq : q<16)
    (h24 : b.getReg .x24=c.s8v q) (acc : List Digest) (s : MachineState) (hs : c.GroupIn b (q+1) acc s) :
    ∃t,Steps vimage s 1 1 t ∧ c.ChainIn (set24 b (c.s8v (q+1))) (3*(q+1)) acc t := by
  obtain ⟨⟨hR,hF,hS⟩,hlen,hpc⟩ := hs
  have hfacts := c.groupFacts hds (q+1) (by omega)
  have hchk := s8Run_at (q+1) (c.kOf (q+1)) (by omega) (c.kOf_lt hds (q+1) (by omega))
  rw [if_neg (show q+1≠0 by omega)] at hchk
  have hrun := rOK_eq hchk
  obtain ⟨h1,h2⟩ := c.kOf_bounds hds (q+1) (by omega)
  have hl := (group_bounds (q+1) (c.kOf (q+1)) (by omega) h1 h2).2.2.1
  have hp : entW (q+1) (c.kOf (q+1))<253807 := by unfold leadPc at hl; omega
  have hst := piece_steps45 hrun hp s hpc (by simp [s8R])
  set r := s8R (kss (q+1) (c.kOf (q+1))) (entW (q+1) (c.kOf (q+1))) with hr
  have h24s : s.getReg .x24=c.s8v q := (hR .x24 (by decide +kernel)).trans h24
  refine ⟨r.toState s,hst,⟨⟨fun x hx => ?_,fun A hA hn => ?_,fun j hj => ?_⟩,hlen,?_⟩⟩
  · rw [Result.toState_getReg]
    by_cases hx : x=.x24
    · subst x
      simp only [hr,s8R]
      rw [RegFile.get_set_self _ _ (by decide +kernel),addC_eval,set24_24]
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
    simp only [show 3*(q+1)<51 by omega,show 3*(q+1)%3=0 by omega,if_true,show 3*(q+1)/3=q+1 by omega,show q+1≠0 by omega,if_false]
/-! ### Group 17 (campaign T8D, TOP2 NF17): slot, chains 51/52, general-field dispatch, slot, chain 53 -/
def s8w (c : NCtx) (n : Nat) : Word := BitVec.ofNat 64 (((List.range n).map c.dig).sum)-144#64
theorem s8v_eq (c : NCtx) (q : Nat) : c.s8v q=c.s8w (3*q+3) := rfl
theorem sum_range_add (f : Nat → Nat) (n k : Nat) :
    ((List.range (n+k)).map f).sum = ((List.range n).map f).sum + ((List.range' n k).map f).sum := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← Nat.add_assoc, List.range_succ, List.map_append, List.sum_append, ih, List.range'_concat]
    simp; omega
theorem s8w_add (c : NCtx) (n k : Nat) :
    c.s8w n+BitVec.ofNat 64 (((List.range' n k).map c.dig).sum)=c.s8w (n+k) := by
  unfold s8w
  rw [sum_range_add, BitVec.ofNat_add]
  simp only [BitVec.sub_eq_add_neg]
  ac_rfl
theorem slot17_step (c : NCtx) (hds : c.DigitsOk) {b : MachineState}
    (h24 : b.getReg .x24=c.s8v 16) (acc : List Digest) (s : MachineState) (hs : c.R8In b acc s) :
    ∃t,Steps vimage s 2 2 t ∧ c.ChainIn (set24 b (c.s8w 53)) 51 acc t := by
  obtain ⟨⟨hR,hF,hS⟩,hlen,hpc⟩ := hs
  obtain ⟨hrun,-,-,-⟩ := c.r8Blk_facts hds
  have hk := c.k17_lt hds
  have hp : 256*(c.k17+1)<253807 := by omega
  have hst := piece_steps45 hrun hp s hpc (by simp [jR])
  set r := jR (c.dig 51+c.dig 52) (blkW c.k17) with hr
  have h24s : s.getReg .x24=c.s8v 16 := (hR .x24 (by decide +kernel)).trans h24
  refine ⟨r.toState s,hst,⟨⟨fun x hx => ?_,fun A hA hn => ?_,fun j hj => ?_⟩,hlen,?_⟩⟩
  · rw [Result.toState_getReg]
    by_cases hx : x=.x24
    · subst x
      simp only [hr,jR]
      rw [RegFile.get_set_self _ _ (by decide +kernel),addC_eval,set24_24]
      simp only [E.eval,h24s,s8v_eq]
      have := c.s8w_add 51 2
      simp only [List.range'_succ, List.range'_zero, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, Nat.add_zero] at this
      exact this
    · simp only [hr,jR]
      rw [RegFile.get_set_ne _ _ hx,RegFile.init_get_eval,set24_regs _ _ _ hx]
      exact hR x (by assumption)
  · rw [Result.toState_getMem,set24_mem]
    simp only [hr,jR]
    rw [memEval_nil]
    exact hF A hA hn
  · have hfr : Frame s (r.toState s) (fun _ => False) := fun A _ _ => by
      rw [Result.toState_getMem]; simp [hr,jR,memEval_nil]
    exact (hS j hj).frame hfr (by have := slot_props j (by omega);omega) (by simp) (by simp)
  · rw [Result.toState_pc]
    simp [hr,jR,startPc,r8Start,E.eval]
theorem high3_xor (X : Word) : ((~~~X ^^^ hiMask) >>> 55) &&& 7#64 = (X >>> 55) &&& 7#64 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  by_cases h3 : j < 3
  · have hm : hiMask.getLsbD (55 + j) = true := by
      unfold hiMask
      rw [BitVec.getLsbD_ofNat, show (2:Nat)^64-2^55=2^55*(2^9-1) by norm_num, Nat.testBit_two_pow_mul,
        Nat.testBit_two_pow_sub_one]
      simp; omega
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_xor, BitVec.getLsbD_not, hm]
    cases X.getLsbD (55 + j) <;> simp [show 55 + j < 64 by omega]
  · have h7 : (7#64).getLsbD j = false := by
      rw [BitVec.getLsbD_ofNat, show (7:Nat)=2^3-1 by norm_num, Nat.testBit_two_pow_sub_one]; simp; omega
    simp [h7]
theorem high3_val (v : Digest) :
    (v.extractLsb' 64 64 >>> 55) &&& 7#64 = BitVec.ofNat 64 (v.toNat / 2 ^ 119 % 8) := by
  apply BitVec.eq_of_toNat_eq
  have hv := v.isLt
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat]
  have e : (7 : Nat) % 2^64 = 2^3 - 1 := by norm_num
  rw [e, Nat.and_two_pow_sub_one_eq_mod]
  omega
theorem slot_val (y : Nat) (hy : y < 8) :
    ((((BitVec.ofNat 64 y : Word)+2042#64) <<< 8)+152#64) &&& ~~~1#64 = pcOf (r8SlotW y) := by
  interval_cases y <;> decide +kernel
theorem genDisp_value (v : Digest) :
    (((((~~~(v.extractLsb' 64 64) ^^^ hiMask) >>> ((55#64 : Word).toNat % 64)) &&& 7#64)+2042#64) <<<
      ((8#64 : Word).toNat % 64)+152#64) &&& ~~~1#64=pcOf (r8SlotW (v.toNat/2^119%8)) := by
  rw [show (55#64 : Word).toNat % 64 = 55 from rfl, show (8#64 : Word).toNat % 64 = 8 from rfl, high3_xor,
    high3_val]
  exact slot_val _ (Nat.mod_lt _ (by decide))
theorem disp53_step (c : NCtx) (hds : c.DigitsOk) {b : MachineState} {v : Digest}
    (he : Encoded v b) (hf : c.Fit v) (h24 : b.getReg .x24=c.s8w 53)
    (acc : List Digest) (s : MachineState) (hs : c.EndInv b 52 acc s) :
    ∃t,Steps vimage s 7 7 t ∧ c.ChainIn (set24 b (c.s8v 17)) 53 acc t := by
  obtain ⟨⟨hR,hF,hS⟩,hlen,hpc⟩ := hs
  obtain ⟨-,-,-,hrun⟩ := c.r8Blk_facts hds
  obtain ⟨hrun2,-⟩ := c.r8Suf_facts hds
  have hk := c.k17_lt hds
  have hb := blkW_lt c.k17 hk
  have p1 := partLen_le 17 (c.dig 51)
  have p2 := partLen_le 17 (c.dig 52)
  have he52 : c.endPc 52=blkW c.k17+partLen 17 (c.dig 51)+partLen 17 (c.dig 52) := by
    simp [endPc, r8Start]
  rw [he52] at hpc
  have hst1 := piece_steps45 hrun (by omega) s hpc (by simp [genDispR])
  set r1 := genDispR with hr1
  have h17 : s.getReg .x17= ~~~(v.extractLsb' 64 64) ^^^ hiMask := (hR _ (by decide +kernel)).trans he.hi
  have hpc1 : (r1.toState s).pc=pcOf (r8SlotW (c.dig 53)) := by
    rw [Result.toState_pc, c.fit_d53 hf]
    simp only [hr1,genDispR,genDispE,E.eval,BinOp.eval,h17]
    exact genDisp_value v
  have hy := hds 53 (by decide +kernel)
  rw [topMax_hi 53 (by decide +kernel)] at hy
  have hfin := finW_lt (c.dig 53) (by omega)
  have hsl : r8SlotW (c.dig 53)<253807 := by unfold r8SlotW; omega
  have hst2 := piece_steps45 hrun2 hsl (r1.toState s) hpc1 (by simp [jR])
  set r2 := jR (c.dig 53) (sufW (c.dig 53)) with hr2
  have hfr1 : Frame s (r1.toState s) (fun _ => False) := fun A _ _ => by
    rw [Result.toState_getMem]; simp [hr1,genDispR,memEval_nil]
  have hfr2 : Frame (r1.toState s) (r2.toState (r1.toState s)) (fun _ => False) := fun A _ _ => by
    rw [Result.toState_getMem]; simp [hr2,jR,memEval_nil]
  have hreg1 : ∀ x, x ≠ .x14 → (r1.toState s).getReg x=s.getReg x := by
    intro x hx
    rw [Result.toState_getReg]; simp only [hr1,genDispR]
    rw [RegFile.get_set_ne _ _ hx,RegFile.init_get_eval]
  have h24s : (r1.toState s).getReg .x24=c.s8w 53 :=
    (hreg1 .x24 (by decide +kernel)).trans ((hR .x24 (by decide +kernel)).trans h24)
  refine ⟨r2.toState (r1.toState s),(hst1.trans hst2).of_eq (by simp [hr1,genDispR,hr2,jR]) (by simp [hr1,genDispR,hr2,jR]),
    ⟨⟨fun x hxc => ?_,fun A hA hn => ?_,fun j hj => ?_⟩,hlen,?_⟩⟩
  · rw [Result.toState_getReg]
    by_cases hx : x=.x24
    · subst x
      simp only [hr2,jR]
      rw [RegFile.get_set_self _ _ (by decide +kernel),addC_eval,set24_24]
      simp only [E.eval,h24s,s8v_eq]
      have := c.s8w_add 53 1
      simp only [List.range'_succ, List.range'_zero, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, Nat.add_zero] at this
      exact this
    · simp only [hr2,jR]
      have h14 : x ≠ .x14 := by rintro rfl; exact hxc (by decide +kernel)
      rw [RegFile.get_set_ne _ _ hx,RegFile.init_get_eval,set24_regs _ _ _ hx,hreg1 x h14]
      exact hR x hxc
  · rw [set24_mem]
    exact (hfr2.get hA (by simp)).trans ((hfr1.get hA (by simp)).trans (hF.get hA hn))
  · exact ((hS j hj).frame hfr1 (by have := slot_props j (by omega);omega) (by simp) (by simp)).frame hfr2
      (by have := slot_props j (by omega);omega) (by simp) (by simp)
  · rw [Result.toState_pc]
    simp [hr2,jR,startPc,r8Start,E.eval]
end SigGolfCandidate.T3M.Nonbinary.NCtx
end
