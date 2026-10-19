import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsDispatchCtx

section
namespace SigGolfCandidate.T3M.Nonbinary.NCtx
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
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
theorem goodQ_fault {s : MachineState} {Q : Prop} {A : Nat} (hf : fetch vimage s=none) :
    Verify.GoodQP P s 1 0 Q A (pure (false, 0)) := by
  intro F hF
  have hF' : F=(F-1)+1 := by omega
  refine ⟨?_,fun hash => ?_⟩
  · rw [hF',execute_fetch_none (F-1) hf,map_pure]; rfl
  · have he : evalWithAnswerFn hash (Riscv.execute (F-1+1) vimage s)=⟨.failure,s,0,0,0⟩ := by
      rw [execute_fetch_none (F-1) hf]; rfl
    rw [hF',he]
    exact ⟨by simp,Nat.zero_le _,fun h _ => by simp at h⟩
/-- Campaign R6: dispatch overhead of groups `q+1 .. q+k-1` (entry word + dispatch per transition). -/
def ov : Nat → Nat → Nat
  | _, 0 => 0
  | _, 1 => 1
  | q, k+2 => 1+dspR6 (q+1)+ov (q+1) (k+1)
theorem ov_succ (q k : Nat) (hk : 1 ≤ k) : ov q (k+1)=1+dspR6 (q+1)+ov (q+1) k := by
  obtain ⟨j,rfl⟩ : ∃j,k=j+1 := ⟨k-1,by omega⟩; rfl
theorem groups_from (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0) {V : Digest} (he : Encoded6 V s0) (hf : c.Fit6 V)
    (n : Nat) (hn : n ≤ 17) (hval : ∀ q, q<n → gValid V q)
    (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ acc t,c.EndInv (set24 s0 (c.s8v (n-1))) (3*(n-1)+2) acc t → Verify.GoodQP P t N C Q A (K acc)) :
    ∀ k q, 1 ≤ q → q+k=n → 0<k → ∀ acc s,c.GroupIn (set24 s0 (c.s8v (q-1))) q acc s →
      Verify.GoodQP P s (N+126*k) (C+c.chainsCost (3*q) (3*k)+ov q k) Q (A+c.chainsCost (3*q) (3*k)+ov q k)
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
    have heB := set24_encoded6 (c.s8v (q'+1)) he
    rw [show 3*(k+1)=3+3*k by ring,← List.range'_append_1,List.foldlM_append,Verify.ccM_bind]
    have ec := c.chainsCost_add' (3*(q'+1)) 3 (3*k)
    by_cases hk0 : k=0
    · subst hk0
      have hqn : q'+1=n-1 := by omega
      have H := c.group_good hc hds hkB h0B (q'+1) (by omega) K N C A Q (by rw [← hqn] at hK; exact hK)
        3 (3*(q'+1)) (le_refl _) (by omega) (by decide +kernel) acc t hin
      have H' := Verify.GoodQP.steps hst H
      simp only [Nat.mul_zero,Nat.add_zero,List.range'_zero,List.foldlM_nil,bind_pure,Verify.ccM_pure] at H' ⊢
      have h1 : ov (q'+1) (0+1)=1 := rfl
      refine H'.mono ?_ ?_ (fun h => ⟨h,?_⟩) <;> omega
    · have hov := ov_succ (q'+1) k (by omega)
      simp only [show q'+1+1=q'+2 from rfl] at hov
      have hd := dspR6_le (q'+2)
      have H := c.group_good hc hds hkB h0B (q'+1) (by omega)
        (fun ends => Verify.ccM ((List.range' (3*(q'+1)+3) (3*k)).foldlM c.chainF ends) K)
        (N+126*k+dspR6 (q'+2)) (C+c.chainsCost (3*(q'+1)+3) (3*k)+ov (q'+2) k+dspR6 (q'+2))
        (A+c.chainsCost (3*(q'+1)+3) (3*k)+ov (q'+2) k+dspR6 (q'+2)) Q
        (fun ends u hu => by
          obtain ⟨u',st,hu'⟩ := c.end_dispatchR6_in hc hds heB hf (q'+1) (by omega) (hval (q'+2) (by omega)) ends u hu
          have e2 : dspR6 (q'+1+1)=dspR6 (q'+2) := rfl
          rw [e2] at st
          have H := ih (q'+2) (by omega) (by omega) (by omega) ends u' (by simpa using hu')
          rw [show 3*(q'+2)=3*(q'+1)+3 by omega] at H
          refine (Verify.GoodQP.steps st H).mono ?_ ?_ (fun h => ⟨h,?_⟩) <;> omega)
        3 (3*(q'+1)) (le_refl _) (by omega) (by decide +kernel) acc t hin
      have H' := Verify.GoodQP.steps hst H
      rw [ec]
      refine H'.mono ?_ ?_ (fun h => ⟨h,?_⟩) <;> omega
theorem groups_zero (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0) {V : Digest} (he : Encoded6 V s0) (hf : c.Fit6 V)
    (n : Nat) (hn : n ≤ 17) (hn1 : 1 ≤ n) (hval : ∀ q, q<n → gValid V q)
    (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ acc t,c.EndInv (set24 s0 (c.s8v (n-1))) (3*(n-1)+2) acc t → Verify.GoodQP P t N C Q A (K acc))
    (s : MachineState) (hs : c.GroupIn s0 0 [] s) :
    Verify.GoodQP P s (N+126*n) (C+c.chainsCost 0 (3*n)+ov 0 n) Q (A+c.chainsCost 0 (3*n)+ov 0 n)
      (Verify.ccM ((List.range' 0 (3*n)).foldlM c.chainF []) K) := by
  obtain ⟨t,hst,hin⟩ := c.g0_entry hds [] s hs
  have hkB := set24_known c (c.s8v 0) hk
  have h0B := set24_orig c (c.s8v 0) h0
  have heB := set24_encoded6 (c.s8v 0) he
  obtain ⟨m,rfl⟩ : ∃m,n=m+1 := ⟨n-1,by omega⟩
  rw [show 3*(m+1)=3+3*m by ring,← List.range'_append_1,List.foldlM_append,Verify.ccM_bind]
  have ec := c.chainsCost_add' 0 3 (3*m)
  by_cases hm0 : m=0
  · subst hm0
    have H := c.group_good hc hds hkB h0B 0 (by omega) K N C A Q (by simpa using hK)
      3 0 (le_refl _) (by omega) (by decide +kernel) [] t (by simpa using hin)
    have H' := Verify.GoodQP.steps hst H
    simp only [Nat.mul_zero,Nat.add_zero,List.range'_zero,List.foldlM_nil,bind_pure,Verify.ccM_pure] at H' ⊢
    have h1 : ov 0 (0+1)=1 := rfl
    refine H'.mono ?_ ?_ (fun h => ⟨h,?_⟩) <;> omega
  · have hov := ov_succ 0 m (by omega)
    simp only [Nat.zero_add] at hov
    have hd1 : dspR6 1=3 := rfl
    have H := c.group_good hc hds hkB h0B 0 (by omega)
      (fun ends => Verify.ccM ((List.range' (0+3) (3*m)).foldlM c.chainF ends) K)
      (N+126*m+3) (C+c.chainsCost 3 (3*m)+ov 1 m+3) (A+c.chainsCost 3 (3*m)+ov 1 m+3) Q
      (fun ends u hu => by
        obtain ⟨u',st,hu'⟩ := c.end_dispatchR6_in hc hds heB hf 0 (by omega) (hval 1 (by omega)) ends u hu
        have H := c.groups_from hc hds hk h0 he hf (m+1) hn hval K N C A Q hK m 1 (le_refl _) (by omega)
          (by omega) ends u' (by simpa using hu')
        simp only [Nat.mul_one] at H
        have e1 : dspR6 (0+1)=3 := rfl
        rw [e1] at st
        refine (Verify.GoodQP.steps st H).mono ?_ ?_ (fun h => ⟨h,?_⟩) <;> omega)
      3 0 (le_refl _) (by omega) (by decide +kernel) [] t (by simpa using hin)
    have H' := Verify.GoodQP.steps hst H
    simp only [Nat.zero_add] at H' ec ⊢
    rw [ec]
    refine H'.mono ?_ ?_ (fun h => ⟨h,?_⟩) <;> omega
def topP (c : NCtx) : M (List Digest) := (List.range' 0 52).foldlM c.chainF []
/-- After the 52 top chains (campaign R6): pc at the final tail `ckTail d51` of the checksum arm. -/
def TopOut (c : NCtx) (s0 : MachineState) (acc : List Digest) (s : MachineState) : Prop :=
  (∀ x, x ∉ chainRegs → x ≠ .x24 → s.getReg x=s0.getReg x) ∧
  Frame s0 s (c.Wr 52) ∧ acc.length=52 ∧
  (∀ j < acc.length, DigAt s (slot j) (acc.getD j 0)) ∧
  s.pc = pcOf (ckTail (c.dig 51)) ∧ s.getReg .x24=c.s8v 16
/-- The checksum digit of a context: chain 51's digit is `topT - (data digit sum)` whenever that lies in `0..7`. -/
def CkOk (c : NCtx) : Prop :=
  ∀ ds, ((List.range 51).map c.dig).sum = ds → topT-7 ≤ ds → ds ≤ topT → c.dig 51 = topT-ds
theorem s8v16_eq (c : NCtx) : c.s8v 16 = BitVec.ofNat 64 topT - BitVec.ofNat 64 (((List.range 51).map c.dig).sum) := rfl
/-- Campaign R6: the checksum chain 51 after the 17 groups (checksum dispatch 3 cycles, then chain 51). -/
theorem ck_good (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) (hck : c.CkOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0)
    (hin : topT-7 ≤ ((List.range 51).map c.dig).sum ∧ ((List.range 51).map c.dig).sum ≤ topT)
    (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ acc t,c.TopOut (set24 s0 (c.s8v 16)) acc t → Verify.GoodQP P t N C Q A (K acc))
    (acc : List Digest) (s : MachineState) (hs : c.EndInv (set24 s0 (c.s8v 16)) 50 acc s) :
    Verify.GoodQP P s (N+43) (C+c.chainsCost 51 1+3) Q (A+c.chainsCost 51 1+3)
      (Verify.ccM ((List.range' 51 1).foldlM c.chainF acc) K) := by
  have hkB := set24_known c (c.s8v 16) hk
  have h0B := set24_orig c (c.s8v 16) h0
  have h24 : s.getReg .x24 = BitVec.ofNat 64 topT - BitVec.ofNat 64 (((List.range 51).map c.dig).sum) := by
    rw [hs.1.1 .x24 (by decide +kernel), set24_24]; rfl
  obtain ⟨t,st,hB,hlen,pt⟩ := (c.end_ck hds acc s hs _ rfl h24).1 hin
  have hd51 := hck _ rfl hin.1 hin.2
  have hcin : c.ChainIn (set24 s0 (c.s8v 16)) 51 acc t := ⟨hB,hlen,by rw [pt,c.startPc_51,hd51]⟩
  rw [List.range'_succ,List.foldlM_cons]
  simp only [chainF,bind_assoc,pure_bind,Verify.ccM_bind,List.range'_zero,List.foldlM_nil,Verify.ccM_pure]
  have H := c.chain_good hc hds hkB h0B 51 (by omega) acc K N C A Q
    (fun v t' ht' => hK _ t' (by
      obtain ⟨⟨hR,hF,hS⟩,hl,hp⟩ := ht'
      refine ⟨fun x hx _ => hR x hx,hF,hl,hS,?_,?_⟩
      · rw [hp]; simp [endPc]
      · rw [hR .x24 (by decide +kernel),set24_24]))
    t hcin
  have e1 : c.chainsCost 51 1=c.chainCost 51 (c.dig 51) := by simp [chainsCost]
  have H2 := Verify.GoodQP.steps st H
  rw [e1]
  refine H2.mono ?_ ?_ (fun h => ⟨h,?_⟩) <;> omega
theorem top_full (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) (hck : c.CkOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0) {V : Digest} (he : Encoded6 V s0) (hf : c.Fit6 V)
    (hval : ∀ q, q<17 → gValid V q)
    (hin : topT-7 ≤ ((List.range 51).map c.dig).sum ∧ ((List.range 51).map c.dig).sum ≤ topT)
    (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ acc t,c.TopOut (set24 s0 (c.s8v 16)) acc t → Verify.GoodQP P t N C Q A (K acc))
    (s : MachineState) (hs : c.GroupIn s0 0 [] s) :
    Verify.GoodQP P s (N+2185) (C+c.chainsCost 0 52+ov 0 17+3) Q (A+c.chainsCost 0 52+ov 0 17+3)
      (Verify.ccM c.topP K) := by
  unfold topP
  rw [show (52:Nat)=3*17+1 from rfl,← List.range'_append_1,List.foldlM_append,Verify.ccM_bind]
  have ec := c.chainsCost_add' 0 (3*17) 1
  have H := c.groups_zero hc hds hk h0 he hf 17 (le_refl _) (by decide +kernel) hval
    (fun ends => Verify.ccM ((List.range' (0+3*17) 1).foldlM c.chainF ends) K)
    (N+43) (C+c.chainsCost 51 1+3) (A+c.chainsCost 51 1+3) Q
    (fun acc t ht => c.ck_good hc hds hck hk h0 hin K N C A Q hK acc t (by simpa using ht))
    s hs
  simp only [Nat.zero_add] at H ec ⊢
  rw [show (3*17 : Nat)=51 from rfl] at ec H ⊢
  rw [ec]
  refine H.mono ?_ ?_ (fun h => ⟨h,?_⟩) <;> omega
theorem goodQ_vacuous {s : MachineState} {N C A : Nat} {X : OracleComp Legacy.HashSpec Verify.Obs}
    (h : Verify.GoodQP P s N C False A X) (Q' : Prop) (A' : Nat) : Verify.GoodQP P s N C Q' A' X := by
  intro F hF
  obtain ⟨h1,h2⟩ := h F hF
  exact ⟨h1,fun hash => ⟨(h2 hash).1,(h2 hash).2.1,fun hs hok => ((h2 hash).2.2 hs hok).1.elim⟩⟩
theorem ov_le (j : Nat) (hj : j ≤ 17) : ov 0 j ≤ 72 := by interval_cases j <;> decide +kernel
theorem ov_17 : ov 0 17 = 72 := by decide +kernel
/-- Campaign R6: an invalid group `j` (1..16) after valid groups faults at its dispatch. -/
theorem top_bad_group (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0) {V : Digest} (he : Encoded6 V s0) (hf : c.Fit6 V)
    (j : Nat) (hj1 : 1 ≤ j) (hj : j ≤ 16) (hval : ∀ q, q<j → gValid V q)
    (hbad : ¬ gValid V j) (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs)
    (hK : ∀ acc, K acc=pure (false,0)) (Q : Prop) (A : Nat)
    (s : MachineState) (hs : c.GroupIn s0 0 [] s) :
    Verify.GoodQP P s (126*j+6) (c.chainsCost 0 (3*j)+ov 0 j+5) Q A
      (Verify.ccM ((List.range' 0 (3*j)).foldlM c.chainF []) K) := by
  refine goodQ_vacuous (A := 0+c.chainsCost 0 (3*j)+ov 0 j) ?_ Q A
  have H := c.groups_zero hc hds hk h0 he hf j (by omega) hj1 hval K 6 5 0 False
    (fun acc t ht => by
      rw [hK acc]
      have hb' : ¬ gValid V (j-1+1) := by rw [show j-1+1=j by omega]; exact hbad
      obtain ⟨k,z,stz,hk5,fz⟩ := c.end_dispatchR6_bad hc hds (set24_encoded6 _ he) (j-1) (by omega) hb' acc t ht
      have R := goodQ_fault (P := P) (Q := False) (A := 0) fz
      refine (Verify.GoodQP.steps stz R).mono ?_ ?_ ?_
      · omega
      · omega
      · intro h; exact h.elim)
    s hs
  exact H.mono (by omega) (by omega) (fun h => ⟨h,le_refl _⟩)
/-- Campaign R6: all 17 groups valid but the checksum out of range: the checksum dispatch faults. -/
theorem top_bad_ck (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0) {V : Digest} (he : Encoded6 V s0) (hf : c.Fit6 V)
    (hval : ∀ q, q<17 → gValid V q)
    (hout : ¬ (topT-7 ≤ ((List.range 51).map c.dig).sum ∧ ((List.range 51).map c.dig).sum ≤ topT))
    (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs)
    (hK : ∀ acc, K acc=pure (false,0)) (Q : Prop) (A : Nat)
    (s : MachineState) (hs : c.GroupIn s0 0 [] s) :
    Verify.GoodQP P s (126*17+4) (c.chainsCost 0 (3*17)+ov 0 17+3) Q A
      (Verify.ccM ((List.range' 0 (3*17)).foldlM c.chainF []) K) := by
  refine goodQ_vacuous (A := 0+c.chainsCost 0 (3*17)+ov 0 17) ?_ Q A
  have H := c.groups_zero hc hds hk h0 he hf 17 (le_refl _) (by omega) hval K 4 3 0 False
    (fun acc t ht => by
      rw [hK acc]
      have h24 : t.getReg .x24 = BitVec.ofNat 64 topT - BitVec.ofNat 64 (((List.range 51).map c.dig).sum) := by
        rw [ht.1.1 .x24 (by decide +kernel), set24_24]; rfl
      obtain ⟨z,stz,fz⟩ := (c.end_ck hds acc t (by simpa using ht) _ rfl h24).2 hout
      have R := goodQ_fault (P := P) (Q := False) (A := 0) fz
      refine (Verify.GoodQP.steps stz R).mono ?_ ?_ ?_
      · omega
      · omega
      · intro h; exact h.elim)
    s hs
  exact H.mono (by omega) (by omega) (fun h => ⟨h,le_refl _⟩)
end SigGolfCandidate.T3M.Nonbinary.NCtx
end
