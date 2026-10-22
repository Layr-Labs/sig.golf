import SigGolfCandidate.T3M_Verify_Nonbinary_ChainsDispatchCtx

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
/-- `setTab` (x29, x18) and `set24` (x24) commute. -/
theorem setTab_set24 (b : MachineState) (x : Word) : setTab (set24 b x) = set24 (setTab b) x := by
  unfold setTab set24
  rw [setReg_of_ne _ _ (by decide +kernel), setReg_of_ne _ _ (by decide +kernel), setReg_of_ne b _ (by decide +kernel),
    setReg_of_ne _ _ (by decide +kernel), setReg_of_ne _ _ (by decide +kernel), setReg_of_ne b _ (by decide +kernel)]
  simp only
  congr 1
  funext r
  by_cases h24 : r=.x24 <;> by_cases h18 : r=.x18 <;> simp_all
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
/-- Dispatch overhead of groups `q+1 .. q+k-1` (entry word + dispatch per transition; T51 `dspR6`). -/
def ov : Nat → Nat → Nat
  | _, 0 => 0
  | _, 1 => 1
  | q, k+2 => 1+dspR6 (q+1)+ov (q+1) (k+1)
theorem ov_succ (q k : Nat) (hk : 1 ≤ k) : ov q (k+1)=1+dspR6 (q+1)+ov (q+1) k := by
  obtain ⟨j,rfl⟩ : ∃j,k=j+1 := ⟨k-1,by omega⟩; rfl
theorem nCh_lt (q : Nat) (hq : q < 16) : nCh q = 3 := by unfold nCh; rw [if_neg (by omega)]
/-- Base state of group `q`'s chains: group 0 runs on `s0`, the later groups on `setTab s0` (t4/s2 loaded by group 0's
dispatch); x24 holds the reverse checksum after the group's cell. -/
def bq (c : NCtx) (s0 : MachineState) (q : Nat) : MachineState :=
  if q = 0 then set24 s0 (c.s8v 0) else set24 (setTab s0) (c.s8v q)
/-- Groups `q .. n-1` (1 <= q, n <= 16: all triples) on the base `S = setTab s0`. -/
theorem groups_from (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {S : MachineState}
    (hk : ∀p∈c.known,S.getReg p.1=p.2) (h0 : c.Orig0 S) {V : Digest} (he : Encoded6 V S) (hf : c.Fit6 V)
    (n : Nat) (hn : n ≤ 16) (hval : ∀ q, q<n → gValid V q)
    (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ acc t,c.EndInv (set24 S (c.s8v (n-1))) (3*(n-1)+2) acc t → Verify.GoodQP P t N C Q A (K acc)) :
    ∀ k q, 1 ≤ q → q+k=n → 0<k → ∀ acc s,c.GroupIn (set24 S (c.s8v (q-1))) q acc s →
      Verify.GoodQP P s (N+126*k) (C+c.chainsCost (3*q) (3*k)+ov q k) Q (A+c.chainsCost (3*q) (3*k)+ov q k)
        (Verify.ccM ((List.range' (3*q) (3*k)).foldlM c.chainF acc) K) := by
  intro k
  induction k with
  | zero => intro q _ _ h; omega
  | succ k ih =>
    intro q hq1 hqk _ acc s hs
    have hq : q<16 := by omega
    obtain ⟨q',rfl⟩ : ∃q',q=q'+1 := ⟨q-1,by omega⟩
    obtain ⟨t,hst,hin⟩ := c.entry_step hc hds q' (by omega) (set24_24 _ _) acc s (by simpa using hs)
    rw [set24_set24] at hin
    have hkB := set24_known c (c.s8v (q'+1)) hk
    have h0B := set24_orig c (c.s8v (q'+1)) h0
    have heB := set24_encoded6 (c.s8v (q'+1)) he
    have hn3 := nCh_lt (q'+1) (by omega)
    rw [show 3*(k+1)=3+3*k by ring,← List.range'_append_1,List.foldlM_append,Verify.ccM_bind]
    have ec := c.chainsCost_add' (3*(q'+1)) 3 (3*k)
    by_cases hk0 : k=0
    · subst hk0
      have hqn : q'+1=n-1 := by omega
      have H := c.group_good hc hds hkB h0B (q'+1) (by omega) K N C A Q
        (by rw [hn3, show 3*(q'+1)+3-1 = 3*(q'+1)+2 by omega]; rw [← hqn] at hK; exact hK)
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
          rw [hn3, show 3*(q'+1)+3-1 = 3*(q'+1)+2 by omega] at hu
          obtain ⟨u',st,hu'⟩ := c.end_dispatchR6_in hc hds heB hf (q'+1) (by omega) (by omega)
            (hval (q'+2) (by omega)) ends u hu
          have e2 : dspR6 (q'+1+1)=dspR6 (q'+2) := rfl
          rw [e2] at st
          have H := ih (q'+2) (by omega) (by omega) (by omega) ends u' (by simpa using hu')
          rw [show 3*(q'+2)=3*(q'+1)+3 by omega] at H
          refine (Verify.GoodQP.steps st H).mono ?_ ?_ (fun h => ⟨h,?_⟩) <;> omega)
        3 (3*(q'+1)) (le_refl _) (by omega) (by decide +kernel) acc t hin
      have H' := Verify.GoodQP.steps hst H
      rw [ec]
      refine H'.mono ?_ ?_ (fun h => ⟨h,?_⟩) <;> omega
/-- Groups `0 .. n-1` (1 <= n <= 16) from group 0's entry (base `s0`; group 0's dispatch switches to `setTab`). -/
theorem groups_zero (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0) {V : Digest} (he : Encoded0 V s0) (hf : c.Fit6 V)
    (hmask : s0.getMem 0xffbdf0#64 = 65280#64)
    (n : Nat) (hn : n ≤ 16) (hn1 : 1 ≤ n) (hval : ∀ q, q<n → gValid V q)
    (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ acc t,c.EndInv (c.bq s0 (n-1)) (3*(n-1)+2) acc t → Verify.GoodQP P t N C Q A (K acc))
    (s : MachineState) (hs : c.GroupIn s0 0 [] s) :
    Verify.GoodQP P s (N+126*n) (C+c.chainsCost 0 (3*n)+ov 0 n) Q (A+c.chainsCost 0 (3*n)+ov 0 n)
      (Verify.ccM ((List.range' 0 (3*n)).foldlM c.chainF []) K) := by
  obtain ⟨t,hst,hin⟩ := c.g0_entry hds [] s hs
  have hkB := set24_known c (c.s8v 0) hk
  have h0B := set24_orig c (c.s8v 0) h0
  have heB := set24_encoded0 (c.s8v 0) he
  have hn0 := nCh_lt 0 (by omega)
  obtain ⟨m,rfl⟩ : ∃m,n=m+1 := ⟨n-1,by omega⟩
  rw [show 3*(m+1)=3+3*m by ring,← List.range'_append_1,List.foldlM_append,Verify.ccM_bind]
  have ec := c.chainsCost_add' 0 3 (3*m)
  by_cases hm0 : m=0
  · subst hm0
    have H := c.group_good hc hds hkB h0B 0 (by omega) K N C A Q
      (by rw [hn0]; simpa [bq] using hK)
      3 0 (le_refl _) (by rw [hn0]) (by decide) [] t (by simpa using hin)
    have H' := Verify.GoodQP.steps hst H
    simp only [Nat.mul_zero,Nat.add_zero,List.range'_zero,List.foldlM_nil,bind_pure,Verify.ccM_pure] at H' ⊢
    have h1 : ov 0 (0+1)=1 := rfl
    refine H'.mono ?_ ?_ (fun h => ⟨h,?_⟩) <;> omega
  · have hov := ov_succ 0 m (by omega)
    simp only [Nat.zero_add] at hov
    have hd1 : dspR6 1=5 := rfl
    have hmB : (set24 s0 (c.s8v 0)).getMem 0xffbdf0#64 = 65280#64 := by rw [set24_mem]; exact hmask
    have hkS := setTab_known c hk
    have h0S := setTab_orig c h0
    have heS := setTab_encoded he
    have H := c.group_good hc hds hkB h0B 0 (by omega)
      (fun ends => Verify.ccM ((List.range' (0+3) (3*m)).foldlM c.chainF ends) K)
      (N+126*m+5) (C+c.chainsCost 3 (3*m)+ov 1 m+5) (A+c.chainsCost 3 (3*m)+ov 1 m+5) Q
      (fun ends u hu => by
        rw [hn0] at hu
        obtain ⟨u',st,hu'⟩ := c.end_dispatch0_in hc hds heB hkB hmB hf (hval 1 (by omega)) ends u hu
        rw [setTab_set24] at hu'
        have hK' : ∀ acc t, c.EndInv (set24 (setTab s0) (c.s8v (m+1-1))) (3*(m+1-1)+2) acc t →
            Verify.GoodQP P t N C Q A (K acc) := by
          intro acc t ht; apply hK; unfold bq; rw [if_neg (by omega)]; exact ht
        have H := c.groups_from hc hds hkS h0S heS hf (m+1) hn hval K N C A Q hK' m 1 (le_refl _) (by omega)
          (by omega) ends u' (by simpa using hu')
        simp only [Nat.mul_one] at H
        rw [hd1] at st
        refine (Verify.GoodQP.steps st H).mono ?_ ?_ (fun h => ⟨h,?_⟩) <;> omega)
      3 0 (le_refl _) (by rw [hn0]) (by decide) [] t (by simpa using hin)
    have H' := Verify.GoodQP.steps hst H
    simp only [Nat.zero_add] at H' ec ⊢
    rw [ec]
    refine H'.mono ?_ ?_ (fun h => ⟨h,?_⟩) <;> omega
def topP (c : NCtx) : M (List Digest) := (List.range' 0 51).foldlM c.chainF []
/-- After the 51 top chains (campaign T51): pc at the final tail `ckTail d50` of the checksum arm. Registers outside
`chainRegs`, x24 (reverse checksum) and x29/x18 (loaded by group 0's dispatch) are kept. -/
def TopOut (c : NCtx) (s0 : MachineState) (acc : List Digest) (s : MachineState) : Prop :=
  (∀ x, x ∉ chainRegs → x ≠ .x24 → x ≠ .x29 → x ≠ .x18 → s.getReg x=s0.getReg x) ∧
  Frame s0 s (c.Wr 51) ∧ acc.length=51 ∧
  (∀ j < acc.length, DigAt s (slot j) (acc.getD j 0)) ∧
  s.pc = pcOf (ckTail (c.dig 50)) ∧ s.getReg .x24=c.s8v 16 ∧ s.getReg .x29=65280#64 ∧ s.getReg .x18=856064#64
/-- The checksum digit of a context: chain 50's digit is `topT - (data digit sum)` whenever that lies in `0..5`. -/
def CkOk (c : NCtx) : Prop :=
  ∀ ds, ((List.range 50).map c.dig).sum = ds → topT-5 ≤ ds → ds ≤ topT → c.dig 50 = topT-ds
theorem s8v16_eq (c : NCtx) : c.s8v 16 = BitVec.ofNat 64 topT - BitVec.ofNat 64 (((List.range 50).map c.dig).sum) := rfl
/-- The r7 pair (entered from the end of group 15) and the checksum chain 50: q15's dispatch (3), the pair's cell
word (1), chains 48/49, the checksum dispatch (3), chain 50. -/
theorem pair_ck_good (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) (hck : c.CkOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0) {V : Digest} (he : Encoded0 V s0) (hf : c.Fit6 V)
    (hv16 : gValid V 16)
    (hin : topT-5 ≤ ((List.range 50).map c.dig).sum ∧ ((List.range 50).map c.dig).sum ≤ topT)
    (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ acc t,c.TopOut s0 acc t → Verify.GoodQP P t N C Q A (K acc))
    (acc : List Digest) (s : MachineState) (hs : c.EndInv (c.bq s0 15) 47 acc s) :
    Verify.GoodQP P s (N+130) (C+c.chainsCost 48 3+7) Q (A+c.chainsCost 48 3+7)
      (Verify.ccM ((List.range' 48 3).foldlM c.chainF acc) K) := by
  have hkS := setTab_known c hk
  have h0S := setTab_orig c h0
  have heS := setTab_encoded he
  have hb15 : c.bq s0 15 = set24 (setTab s0) (c.s8v 15) := by unfold bq; rw [if_neg (by omega)]
  rw [hb15] at hs
  have hk15 := set24_known c (c.s8v 15) hkS
  have h015 := set24_orig c (c.s8v 15) h0S
  have he15 := set24_encoded6 (c.s8v 15) heS
  -- q15 -> the pair's cell (3 steps), the cell's s8 word (1 step)
  obtain ⟨u,st1,hu⟩ := c.end_dispatchR6_in hc hds he15 hf 15 (by omega) (by omega) hv16 acc s
    (by simpa using hs)
  obtain ⟨w,st2,hw⟩ := c.entry_step hc hds 15 (by omega) (set24_24 _ _) acc u hu
  rw [set24_set24] at hw
  have hd16 : dspR6 (15+1) = 3 := rfl
  rw [hd16] at st1
  set B := set24 (setTab s0) (c.s8v 16) with hB
  have hkB : ∀p∈c.known,B.getReg p.1=p.2 := set24_known c (c.s8v 16) hkS
  have h0B : c.Orig0 B := set24_orig c (c.s8v 16) h0S
  have hn16 : nCh 16 = 2 := rfl
  rw [show (3:Nat) = 2+1 from rfl, ← List.range'_append_1, List.foldlM_append, Verify.ccM_bind,
    show (48+2:Nat) = 50 from rfl]
  have ec := c.chainsCost_add' 48 2 1
  rw [show (48+2:Nat) = 50 from rfl] at ec
  have H := c.group_good hc hds hkB h0B 16 (by omega)
    (fun ends => Verify.ccM ((List.range' 50 1).foldlM c.chainF ends) K)
    (N+46) (C+c.chainsCost 50 1+3) (A+c.chainsCost 50 1+3) Q
    (fun ends u2 hu2 => by
      rw [hn16] at hu2
      have h24 : u2.getReg .x24 = BitVec.ofNat 64 topT - BitVec.ofNat 64 (((List.range 50).map c.dig).sum) := by
        rw [hu2.1.1 .x24 (by decide +kernel), hB, set24_24]; rfl
      obtain ⟨t3,st3,hB3,hlen3,pt3⟩ := (c.end_ck hds ends u2 (by simpa using hu2) _ rfl h24).1 hin
      have hd50 := hck _ rfl hin.1 hin.2
      have hcin : c.ChainIn B 50 ends t3 :=
        ⟨hB3, hlen3, by rw [pt3]; simp [startPc, hd50]⟩
      rw [List.range'_succ,List.foldlM_cons]
      simp only [chainF,bind_assoc,pure_bind,Verify.ccM_bind,List.range'_zero,List.foldlM_nil,Verify.ccM_pure]
      have H := c.chain_good hc hds hkB h0B 50 (by omega) ends K N C A Q
        (fun v t' ht' => hK _ t' (by
          obtain ⟨⟨hR,hF,hS⟩,hl,hp⟩ := ht'
          refine ⟨fun x hx h24 h29 h18 => ?_, ?_, hl, hS, ?_, ?_, ?_, ?_⟩
          · rw [hR x hx, hB, set24_regs _ _ _ h24, setTab_regs _ _ h29 h18]
          · intro A hA hn
            rw [hF A hA hn, hB, set24_mem, setTab_mem]
          · rw [hp]; simp [endPc]
          · rw [hR .x24 (by decide +kernel), hB, set24_24]
          · rw [hR .x29 (by decide +kernel), hB, set24_regs _ _ _ (by decide), setTab_29]
          · rw [hR .x18 (by decide +kernel), hB, set24_regs _ _ _ (by decide), setTab_18]))
        t3 hcin
      have e1 : c.chainsCost 50 1=c.chainCost 50 (c.dig 50) := by simp [chainsCost]
      have H2 := Verify.GoodQP.steps st3 H
      rw [e1]
      refine H2.mono ?_ ?_ (fun h => ⟨h,?_⟩) <;> omega)
    2 48 (le_refl _) (by omega) (by omega) acc w (by simpa using hw)
  have H' := Verify.GoodQP.steps (st1.trans st2) H
  rw [ec]
  refine H'.mono ?_ ?_ (fun h => ⟨h,?_⟩) <;> omega
theorem ov_16 : ov 0 16 = 71 := by decide +kernel
/-- The whole T51 top region for a valid word: 16 groups, the r7 pair, the checksum chain. -/
theorem top_full (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) (hck : c.CkOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0) {V : Digest} (he : Encoded0 V s0) (hf : c.Fit6 V)
    (hmask : s0.getMem 0xffbdf0#64 = 65280#64)
    (hval : ∀ q, q<17 → gValid V q)
    (hin : topT-5 ≤ ((List.range 50).map c.dig).sum ∧ ((List.range 50).map c.dig).sum ≤ topT)
    (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ acc t,c.TopOut s0 acc t → Verify.GoodQP P t N C Q A (K acc))
    (s : MachineState) (hs : c.GroupIn s0 0 [] s) :
    Verify.GoodQP P s (N+2146) (C+c.chainsCost 0 51+78) Q (A+c.chainsCost 0 51+78)
      (Verify.ccM c.topP K) := by
  unfold topP
  rw [show (51:Nat)=3*16+3 from rfl,← List.range'_append_1,List.foldlM_append,Verify.ccM_bind]
  have ec := c.chainsCost_add' 0 (3*16) 3
  have H := c.groups_zero hc hds hk h0 he hf hmask 16 (le_refl _) (by decide +kernel) (fun q hq => hval q (by omega))
    (fun ends => Verify.ccM ((List.range' (0+3*16) 3).foldlM c.chainF ends) K)
    (N+130) (C+c.chainsCost 48 3+7) (A+c.chainsCost 48 3+7) Q
    (fun acc t ht => c.pair_ck_good hc hds hck hk h0 he hf (hval 16 (by omega)) hin K N C A Q hK acc t
      (by simpa using ht))
    s hs
  simp only [Nat.zero_add] at H ec ⊢
  rw [show (3*16 : Nat)=48 from rfl] at ec H ⊢
  rw [ov_16] at H
  rw [ec]
  refine H.mono ?_ ?_ (fun h => ⟨h,?_⟩) <;> omega
theorem goodQ_vacuous {s : MachineState} {N C A : Nat} {X : OracleComp Legacy.HashSpec Verify.Obs}
    (h : Verify.GoodQP P s N C False A X) (Q' : Prop) (A' : Nat) : Verify.GoodQP P s N C Q' A' X := by
  intro F hF
  obtain ⟨h1,h2⟩ := h F hF
  exact ⟨h1,fun hash => ⟨(h2 hash).1,(h2 hash).2.1,fun hs hok => ((h2 hash).2.2 hs hok).1.elim⟩⟩
theorem ov_le (j : Nat) (hj : j ≤ 16) : ov 0 j ≤ 71 := by interval_cases j <;> decide +kernel
/-- Campaign T51: an invalid group `j` (1..16; 16 = the r7 pair) after valid groups faults at its dispatch. -/
theorem top_bad_group (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0) {V : Digest} (he : Encoded0 V s0) (hf : c.Fit6 V)
    (hmask : s0.getMem 0xffbdf0#64 = 65280#64)
    (j : Nat) (hj1 : 1 ≤ j) (hj : j ≤ 16) (hval : ∀ q, q<j → gValid V q)
    (hbad : ¬ gValid V j) (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs)
    (hK : ∀ acc, K acc=pure (false,0)) (Q : Prop) (A : Nat)
    (s : MachineState) (hs : c.GroupIn s0 0 [] s) :
    Verify.GoodQP P s (126*j+6) (c.chainsCost 0 (3*j)+ov 0 j+5) Q A
      (Verify.ccM ((List.range' 0 (3*j)).foldlM c.chainF []) K) := by
  refine goodQ_vacuous (A := 0+c.chainsCost 0 (3*j)+ov 0 j) ?_ Q A
  have H := c.groups_zero hc hds hk h0 he hf hmask j (by omega) hj1 hval K 6 5 0 False
    (fun acc t ht => by
      rw [hK acc]
      have hb' : ¬ gValid V (j-1+1) := by rw [show j-1+1=j by omega]; exact hbad
      obtain ⟨k,z,stz,hk5,fz⟩ : ∃ k z, Steps vimage t k k z ∧ k ≤ 5 ∧ fetch vimage z = none := by
        by_cases hj0 : j-1 = 0
        · have ht' : c.EndInv (set24 s0 (c.s8v 0)) 2 acc t := by
            have : c.bq s0 (j-1) = set24 s0 (c.s8v 0) := by unfold bq; rw [if_pos hj0]
            rw [this, hj0] at ht; simpa using ht
          exact (c.end_dispatch0 hc hds (set24_encoded0 _ he) (set24_known c _ hk) (by rw [set24_mem]; exact hmask)
            acc t ht').2 (by rw [hj0] at hb'; simpa using hb')
        · have ht' : c.EndInv (set24 (setTab s0) (c.s8v (j-1))) (3*(j-1)+2) acc t := by
            have : c.bq s0 (j-1) = set24 (setTab s0) (c.s8v (j-1)) := by unfold bq; rw [if_neg hj0]
            rw [this] at ht; exact ht
          exact c.end_dispatchR6_bad hc hds (set24_encoded6 _ (setTab_encoded he)) (j-1) (by omega) (by omega) hb' acc t ht'
      have R := goodQ_fault (P := P) (Q := False) (A := 0) fz
      refine (Verify.GoodQP.steps stz R).mono ?_ ?_ ?_
      · omega
      · omega
      · intro h; exact h.elim)
    s hs
  exact H.mono (by omega) (by omega) (fun h => ⟨h,le_refl _⟩)
/-- Campaign T51: all 17 groups valid but the checksum digit out of range: the checksum dispatch faults. -/
theorem top_bad_ck (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0) {V : Digest} (he : Encoded0 V s0) (hf : c.Fit6 V)
    (hmask : s0.getMem 0xffbdf0#64 = 65280#64)
    (hval : ∀ q, q<17 → gValid V q)
    (hout : ¬ (topT-5 ≤ ((List.range 50).map c.dig).sum ∧ ((List.range 50).map c.dig).sum ≤ topT))
    (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs)
    (hK : ∀ acc, K acc=pure (false,0)) (Q : Prop) (A : Nat)
    (s : MachineState) (hs : c.GroupIn s0 0 [] s) :
    Verify.GoodQP P s (126*16+88) (c.chainsCost 0 50+ov 0 16+7) Q A
      (Verify.ccM ((List.range' 0 50).foldlM c.chainF []) K) := by
  refine goodQ_vacuous (A := 0+c.chainsCost 0 50+ov 0 16+7) ?_ Q A
  have hkS := setTab_known c hk
  have h0S := setTab_orig c h0
  have heS := setTab_encoded he
  rw [show (50:Nat)=48+2 from rfl,← List.range'_append_1,List.foldlM_append,Verify.ccM_bind,
    show (0+48:Nat)=48 from rfl]
  have ec : c.chainsCost 0 (48+2) = c.chainsCost 0 48 + c.chainsCost 48 2 := c.chainsCost_add' 0 48 2
  have H := c.groups_zero hc hds hk h0 he hf hmask 16 (le_refl _) (by decide +kernel) (fun q hq => hval q (by omega))
    (fun ends => Verify.ccM ((List.range' 48 2).foldlM c.chainF ends) K)
    (88) (c.chainsCost 48 2+7) (0+c.chainsCost 48 2+7) False
    (fun acc t ht => by
      have hb15 : c.bq s0 (16-1) = set24 (setTab s0) (c.s8v 15) := by unfold bq; rw [if_neg (by omega)]
      rw [hb15] at ht
      have he15 := set24_encoded6 (c.s8v 15) heS
      obtain ⟨u,st1,hu⟩ := c.end_dispatchR6_in hc hds he15 hf 15 (by omega) (by omega) (hval 16 (by omega)) acc t
        (by simpa using ht)
      obtain ⟨w,st2,hw⟩ := c.entry_step hc hds 15 (by omega) (set24_24 _ _) acc u hu
      rw [set24_set24] at hw
      have hd16 : dspR6 (15+1) = 3 := rfl
      rw [hd16] at st1
      set B := set24 (setTab s0) (c.s8v 16) with hB
      have hkB : ∀p∈c.known,B.getReg p.1=p.2 := set24_known c (c.s8v 16) hkS
      have h0B : c.Orig0 B := set24_orig c (c.s8v 16) h0S
      have hn16 : nCh 16 = 2 := rfl
      have H := c.group_good hc hds hkB h0B 16 (by omega) K 4 3 0 False
        (fun ends u2 hu2 => by
          rw [hn16] at hu2
          rw [hK ends]
          have h24 : u2.getReg .x24 = BitVec.ofNat 64 topT - BitVec.ofNat 64 (((List.range 50).map c.dig).sum) := by
            rw [hu2.1.1 .x24 (by decide +kernel), hB, set24_24]; rfl
          obtain ⟨z,stz,fz⟩ := (c.end_ck hds ends u2 (by simpa using hu2) _ rfl h24).2 hout
          have R := goodQ_fault (P := P) (Q := False) (A := 0) fz
          refine (Verify.GoodQP.steps stz R).mono ?_ ?_ ?_
          · omega
          · omega
          · intro h; exact h.elim)
        2 48 (le_refl _) (by omega) (by omega) acc w (by simpa using hw)
      have H' := Verify.GoodQP.steps (st1.trans st2) H
      simp only [Nat.zero_add]
      refine H'.mono ?_ ?_ (fun h => ⟨h,?_⟩) <;> omega)
    s hs
  rw [show (3*16 : Nat)=48 from rfl] at H
  rw [ec]
  refine H.mono ?_ ?_ (fun h => ⟨h,?_⟩) <;> omega
end SigGolfCandidate.T3M.Nonbinary.NCtx
end
