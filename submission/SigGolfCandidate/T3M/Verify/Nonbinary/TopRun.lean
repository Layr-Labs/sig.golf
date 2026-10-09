import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsDispatchCtx

section
namespace SigGolfCandidate.T3M.Nonbinary.NCtx
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Nonbinary SigGolfCandidate.T3
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
theorem set24_set24 (b : MachineState) (x y : Word) : set24 (set24 b x) y=set24 b y := by
  unfold set24
  rw [setReg_of_ne _ _ (by decide +kernel),setReg_of_ne b _ (by decide +kernel),setReg_of_ne b _ (by decide +kernel)]
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
  have hchk := s8Run_at 0 (c.kOf 0) (by decide +kernel) (c.kOf_lt hds 0 (by decide +kernel))
  rw [if_pos rfl] at hchk
  have hrun := rOK_eq hchk
  have hp : entW 0 (c.kOf 0)<251927 := by
    have := (c.kOf_bounds hds 0 (by decide +kernel)).2 (by decide +kernel)
    unfold entW cellW entOff; simp; omega
  have hst := piece_steps45 hrun hp s hpc (by simp [guardR])
  set r := guardR (c.kOf 0) with hr
  have h29 : s.getReg .x29=BitVec.ofNat 64 (v.toNat/2^119) := (hR .x29 (by decide +kernel)).trans he.tail
  have h11 : s.getReg .x11=64#64 := (hR .x11 (by decide +kernel)).trans (hk (.x11,64) (by simp [known]))
  have hcond := guard_cond v
  have hfr : Frame s (r.toState s) (fun _ => False) := fun A _ _ => by
    rw [Result.toState_getMem]; simp [hr,guardR,memEval_nil]
  refine ⟨r.toState s,hst,⟨⟨fun x hx => ?_,fun A hA hn => ?_,fun j hj => ?_⟩,hlen,?_⟩⟩
  · rw [Result.toState_getReg]
    by_cases hx : x=.x24
    · subst x
      simp only [hr,guardR]
      rw [RegFile.get_set_self _ _ (by decide +kernel),set24_24]
      simp only [E.eval,s8v,kss]
      obtain ⟨k1,k2,k3⟩ := c.kdig_kOf hds 0 (by decide +kernel)
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
  have hchk := s8Run_at 0 (c.kOf 0) (by decide +kernel) (c.kOf_lt hds 0 (by decide +kernel))
  rw [if_pos rfl] at hchk
  have hrun := rOK_eq hchk
  have hk125 := (c.kOf_bounds hds 0 (by decide +kernel)).2 (by decide +kernel)
  have hp : entW 0 (c.kOf 0)<251927 := by unfold entW cellW entOff; simp; omega
  have hst := piece_steps45 hrun hp s hpc (by simp [guardR])
  have h29 : s.getReg .x29=BitVec.ofNat 64 (v.toNat/2^119) := (hR .x29 (by decide +kernel)).trans he.tail
  have h11 : s.getReg .x11=64#64 := (hR .x11 (by decide +kernel)).trans (hk (.x11,64) (by simp [known]))
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
        3 (3*(q'+1)) (le_refl _) (by omega) (by decide +kernel) acc t hin
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
        3 (3*(q'+1)) (le_refl _) (by omega) (by decide +kernel) acc t hin
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
      3 0 (le_refl _) (by omega) (by decide +kernel) [] t (by simpa using hin)
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
      3 0 (le_refl _) (by omega) (by decide +kernel) [] t (by simpa using hin)
    have H' := Verify.GoodQ.steps hst H
    simp only [Nat.zero_add] at H' ec ⊢
    rw [ec]
    refine H'.mono ?_ ?_ (fun h => ⟨h,?_⟩) <;> omega
def topP (c : NCtx) : M (List Digest) := (List.range' 0 54).foldlM c.chainF []
def TopOut (c : NCtx) (s0 : MachineState) (acc : List Digest) (s : MachineState) : Prop :=
  (∀ x, x ∉ chainRegs → x ≠ .x15 → x ≠ .x24 → s.getReg x=s0.getReg x) ∧
  Frame s0 s (c.Wr 54) ∧ acc.length=54 ∧
  (∀ j < acc.length, DigAt s (slot j) (acc.getD j 0)) ∧
  (∃ k, k < 64 ∧ s.pc = pcOf (gX 17 k)) ∧ s.getReg .x2 = 0x3fe00#64 ∧
  s.getReg .x24=c.s8v 17
theorem end_return (c : NCtx) (hds : c.DigitsOk) {s0 b : MachineState}
    (hb : s0.getReg .x2 = 0x3fe00#64)
    (acc : List Digest) (s : MachineState)
    (hs : c.EndInv (set24 (tailInitial (set24 s0 (c.s8v 16)) b) (c.s8v 17)) 53 acc s) :
    c.TopOut s0 acc s := by
  obtain ⟨⟨hR,hF,hS⟩,hlen,hpc⟩ := hs
  have hreg : ∀ x, x ∉ chainRegs → x ≠ .x15 → x ≠ .x24 → s.getReg x=s0.getReg x := by
    intro x hx h15 h24
    rw [hR x hx,set24_regs _ _ _ h24,tailInitial_regs _ _ _ h15,set24_regs _ _ _ h24]
  refine ⟨hreg,?_,hlen,fun j hj => hS j hj,?_,?_,?_⟩
  · intro A hA hn
    exact (hF A hA hn).trans (by rw [set24_mem,tailInitial_mem,set24_mem])
  · refine ⟨c.kOf 17, ?_, ?_⟩
    · simpa [mx] using c.kOf_lt hds 17 (by decide +kernel)
    · rw [hpc]; simp [endPc, qX]
  · rw [hR .x2 (by decide +kernel),set24_regs _ _ _ (by decide +kernel),tailInitial_regs _ _ _ (by decide +kernel),set24_regs _ _ _ (by decide +kernel),hb]
  · rw [hR .x24 (by decide +kernel),set24_24]
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
  have hov : ov 0 17=67 := by decide +kernel
  have H := c.groups_zero hc hds hk h0 he hf hv 17 (le_refl _) (by decide +kernel) hval
    (fun ends => Verify.ccM ((List.range' (0+3*17) 3).foldlM c.chainF ends) K)
    (N+126) (C+c.chainsCost 51 3+4) (A+c.chainsCost 51 3+4) Q
    (fun acc t ht => by
      obtain ⟨u,st,hu,hu15⟩ := c.end_tail hc hds (set24_encoded _ he) hf hv acc t (by simpa using ht)
      have h24 : (tailInitial (set24 s0 (c.s8v 16)) u).getReg .x24=c.s8v 16 := by
        rw [tailInitial_regs _ _ _ (by decide +kernel),set24_24]
      obtain ⟨u2,st2,hu2⟩ := c.entry_step hc hds 16 (by decide +kernel) h24 acc u hu
      have hkB : ∀p∈c.known,(set24 (tailInitial (set24 s0 (c.s8v 16)) u) (c.s8v 17)).getReg p.1=p.2 :=
        set24_known c _ (tailInitial_known c (set24_known c _ hk))
      have h0B := set24_orig c (c.s8v 17) (tailInitial_orig c (t := u) (set24_orig c (c.s8v 16) h0))
      have H := c.group_good hc hds hkB h0B 17 (by decide +kernel) K N C A Q
        (fun ends z hz => hK ends z (c.end_return hds he.table ends z hz))
        3 51 (by decide +kernel) (by decide +kernel) (by decide +kernel) acc u2 (by simpa using hu2)
      have H2 := Verify.GoodQ.steps st (Verify.GoodQ.steps st2 H)
      simp only [Nat.zero_add]
      refine H2.mono ?_ ?_ (fun h => ⟨h,?_⟩) <;> omega)
    s hs
  simp only [Nat.zero_add] at H ec ⊢
  rw [show (3*17 : Nat)=51 from rfl] at ec H ⊢
  rw [hov] at H
  rw [ec]
  refine H.mono ?_ ?_ (fun h => ⟨h,?_⟩) <;> omega
theorem goodQ_vacuous {s : MachineState} {N C A : Nat} {X : OracleComp Legacy.HashSpec Verify.Obs}
    (h : Verify.GoodQ s N C False A X) (Q' : Prop) (A' : Nat) : Verify.GoodQ s N C Q' A' X := by
  intro F hF
  obtain ⟨h1,h2⟩ := h F hF
  exact ⟨h1,fun hash => ⟨(h2 hash).1,(h2 hash).2.1,fun hs hok => ((h2 hash).2.2 hs hok).1.elim⟩⟩
theorem ov_le (j : Nat) (hj : j ≤ 17) : ov 0 j ≤ 67 := by interval_cases j <;> decide +kernel
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
