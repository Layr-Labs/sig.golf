import SigGolfCandidate.Choice.ProducerSelectorControl

namespace SigGolfCandidate.Choice.ProducerSelector
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Search SigGolfCandidate.T3M.Search.Reward
open SigGolfCandidate.T3 (Digest)
open ClaudeWCT.WCT9
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
attribute [local irreducible] words

theorem runningSum_le (v : Digest) (n : Nat) : runningSum v n≤n*255 := by
  induction n with
  | zero => simp [runningSum]
  | succ n ih =>
    rw [runningSum_succ]
    have := rankLookup_le (topRank v n)
    omega

theorem runningScore_le (v : Digest) (n : Nat) : runningScore v n≤n*16 := by
  induction n with
  | zero => simp [runningScore]
  | succ n ih =>
    rw [runningScore_succ]
    have := topLookup_le (topKind n) (topRank v n)
    omega

theorem sum_total (v : Digest) : runningSum v 17+tailWeight v=topLookupSum v := by
  simp only [topLookupSum,rankDigits,List.map_map,Function.comp_def,runningSum]

theorem score_total (v : Digest) :
    runningScore v 17+tailLookup (tailIndex v)=packedTopScore v := by
  unfold packedTopScore runningScore
  rw [show v.toNat/2^119%512=tailIndex v from Nat.mod_eq_of_lt (tailIndex_lt v)]

theorem accumulator_bounds (v : Digest) : topLookupSum v≤4356 ∧ packedTopScore v≤283 := by
  have hs := runningSum_le v 17
  have hr := runningScore_le v 17
  have ht : tailWeight v≤21 := by unfold tailWeight; omega
  have hv := tailLookup_le (tailIndex v)
  rw [← sum_total,← score_total]
  omega

theorem accumulators_spec {image : Image} {b : Nat} (hb : Allowed b) (hc : At image b)
    (s : MachineState) (v : Digest) (hsum : SumTableOK s) (hrew : RewardTablesOK s)
    (hpc : s.pc=pcOf (b+10))
    (h6 : s.getReg .x6=v.extractLsb' 0 64) (h7 : s.getReg .x7=v.extractLsb' 64 64)
    (h11 : s.getReg .x11=BitVec.ofNat 64 (TOP_DATA+2048))
    (h25 : s.getReg .x25=0) (h20 : s.getReg .x20=0) :
    ∃ t, Steps image s 133 133 t ∧ t.pc=pcOf (b+143) ∧
      t.getReg .x25=BitVec.ofNat 64 (topLookupSum v) ∧
      t.getReg .x20=BitVec.ofNat 64 (packedTopScore v) ∧
      RegsExcept s t [.x10,.x20,.x25,.x28,.x29] ∧ Frame s t (fun _=>False) := by
  obtain ⟨t1,s1,p1,g25,g20,r1,f1⟩ := iter hb hc s v 17 (by decide) hsum hrew hpc h6 h7 h11 h25 h20
  obtain ⟨t2,s2,p2,g10,g28,r2,f2⟩ := tailPrefix_spec hb hc t1 v (by simpa [start] using p1)
    (by rw [r1.get (by decide),h7]) (by rw [r1.get (by decide),h11])
  obtain ⟨t3,s3,p3,g29,r3,f3⟩ := tailLoad_spec hc t2 v (hrew.frame (f1.trans f2) (by simp)) p2 g28
  obtain ⟨t4,s4,p4,g25',g20',r4,f4⟩ := tailEnd_spec hb hc t3 v (BitVec.ofNat 64 (runningSum v 17)) (BitVec.ofNat 64 (runningScore v 17)) p3
    (by rw [r3.get (by decide)]; exact g10) g29
    (by rw [r3.get (by decide),r2.get (by decide)]; exact g25)
    (by rw [r3.get (by decide),r2.get (by decide)]; exact g20)
  refine ⟨t4,?_,p4,?_,?_,(((r1.trans r2).trans r3).trans r4).mono (by decide),
    (((f1.trans f2).trans f3).trans f4).mono (by simp)⟩
  · simpa only [show start 17-10+3+1+8=133 from rfl] using ((s1.trans s2).trans s3).trans s4
  · simpa only [ofNat_add_ofNat,sum_total] using g25'
  · simpa only [ofNat_add_ofNat,score_total] using g20'

theorem body_spec {image : Image} {b : Nat} (hb : Allowed b) (hc : At image b)
    (s : MachineState) (v : Digest) (hsum : SumTableOK s) (hrew : RewardTablesOK s)
    (hpc : s.pc=pcOf (b+2))
    (h6 : s.getReg .x6=v.extractLsb' 0 64) (h7 : s.getReg .x7=v.extractLsb' 64 64) :
    ∃ t, Steps image s 141 141 t ∧ t.pc=pcOf (b+143) ∧
      t.getReg .x25=BitVec.ofNat 64 (topLookupSum (T3.topFlip v)) ∧
      t.getReg .x20=BitVec.ofNat 64 (packedTopScore (T3.topFlip v)) ∧
      RegsExcept s t [.x6,.x7,.x10,.x11,.x20,.x25,.x28,.x29] ∧ Frame s t (fun _=>False) := by
  obtain ⟨t1,s1,p1,g6,g7,g11,g25,g20,r1,f1⟩ := init_spec hb hc s v hpc h6 h7
  obtain ⟨t2,s2,p2,g25',g20',r2,f2⟩ := accumulators_spec hb hc t1 (T3.topFlip v)
    (hsum.frame f1 (by simp)) (hrew.frame f1 (by simp)) p1 g6 g7 g11 g25 g20
  exact ⟨t2,s1.trans s2,p2,g25',g20',(r1.trans r2).mono (by decide),(f1.trans f2).mono (by simp)⟩

def sumBranchCode : List (BitVec 32) := (words.drop 143).take 2
sym_block sumBranchBase := symRun {noAlias:=true} sumBranchCode 0#64 3
def sumBranchResult (b : Nat) : Result :=
  ⟨sumBranchBase.res.st,.ite .ne (.reg .x25) (.c 146)
    (.c (pcOf (b+151))) (.c (pcOf (b+145))),.branch,2,2⟩
theorem sumBranch_run (b : Nat) (hb : Allowed b) :
    symRun {noAlias:=true} sumBranchCode (pcOf (b+143)) 3=some (sumBranchResult b) := by
  rcases hb with rfl|rfl <;> kernel_rfl

theorem sumBranch_spec {image : Image} {b : Nat} (hb : Allowed b) (hc : At image b)
    (s : MachineState) (sum : Nat) (hs : sum<2^64)
    (hpc : s.pc=pcOf (b+143)) (h25 : s.getReg .x25=BitVec.ofNat 64 sum) :
    ∃ t, Steps image s 2 2 t ∧ t.pc=(if sum=146 then pcOf (b+145) else pcOf (b+151)) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound (sumBranch_run b hb) (slice hc 143 2 (by decide)) s hpc
    (by simp [sumBranchResult,sumBranchBase.res,rv_simp]),?_,?_,?_⟩
  · have he : BitVec.ofNat 64 sum=146#64 ↔ sum=146 := ofNat_inj hs (by decide)
    by_cases h : sum=146
    all_goals simp [sumBranchResult,sumBranchBase.res,rv_simp,h25,he,h]
  · intro r hr; cases r <;> simp_all [sumBranchResult,sumBranchBase.res,rv_simp] <;> rfl
  · intro A _ _; rfl

def scoreBranchCode : List (BitVec 32) := (words.drop 145).take 2
sym_block scoreBranchBase := symRun {noAlias:=true} scoreBranchCode 0#64 3
def scoreBranchResult (b : Nat) : Result :=
  ⟨scoreBranchBase.res.st,.ite .ltu (.reg .x20) (.c 34)
    (.c (pcOf (b+151))) (.c (pcOf (b+147))),.branch,2,2⟩
theorem scoreBranch_run (b : Nat) (hb : Allowed b) :
    symRun {noAlias:=true} scoreBranchCode (pcOf (b+145)) 3=some (scoreBranchResult b) := by
  rcases hb with rfl|rfl <;> kernel_rfl

theorem scoreBranch_spec {image : Image} {b : Nat} (hb : Allowed b) (hc : At image b)
    (s : MachineState) (score : Nat) (hs : score<2^64)
    (hpc : s.pc=pcOf (b+145)) (h20 : s.getReg .x20=BitVec.ofNat 64 score) :
    ∃ t, Steps image s 2 2 t ∧ t.pc=(if score<34 then pcOf (b+151) else pcOf (b+147)) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound (scoreBranch_run b hb) (slice hc 145 2 (by decide)) s hpc
    (by simp [scoreBranchResult,scoreBranchBase.res,rv_simp]),?_,?_,?_⟩
  · change (if (s.getReg .x20).ult 34#64 then _ else _) = _
    rw [h20,ofNat_ult score 34 hs (by decide)]
    simp [E.eval]
  · intro r hr; cases r <;> simp_all [scoreBranchResult,scoreBranchBase.res,rv_simp] <;> rfl
  · intro A _ _; rfl

theorem decision_spec {image : Image} {b : Nat} (hb : Allowed b) (hc : At image b)
    (s : MachineState) (sum score : Nat) (hs : sum<2^64) (hr : score<2^64)
    (hpc : s.pc=pcOf (b+143))
    (h25 : s.getReg .x25=BitVec.ofNat 64 sum) (h20 : s.getReg .x20=BitVec.ofNat 64 score) :
    ∃ k t, Steps image s k k t ∧ k≤4 ∧
      t.pc=(if sum=146 ∧ 34 ≤ score then pcOf (b+147) else pcOf (b+151)) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _=>False) := by
  obtain ⟨u,su,pu,ru,fu⟩ := sumBranch_spec hb hc s sum hs hpc h25
  by_cases h : sum=146
  · obtain ⟨t,st,pt,rt,ft⟩ := scoreBranch_spec hb hc u score hr (by simpa [h] using pu)
      (by rw [ru.get (by decide),h20])
    refine ⟨4,t,su.trans st,by decide,?_,(ru.trans rt).mono (by decide),(fu.trans ft).mono (by simp)⟩
    by_cases hscore : score<34 <;> simp_all
  · exact ⟨2,u,su,by decide,by simpa [h] using pu,ru,fu⟩

def HINT : Nat := DIGITS+56
def storeCode : List (BitVec 32) := (words.drop 154).take 2
sym_block storeBase := symRun {noAlias:=true} storeCode 0#64 3
def storeResult (b : Nat) : Result := {storeBase.res with pc:=.c (pcOf (b+156))}
theorem store_run (b : Nat) (hb : Allowed b) :
    symRun {noAlias:=true} storeCode (pcOf (b+154)) 3=some (storeResult b) := by
  rcases hb with rfl|rfl <;> kernel_rfl

theorem store_spec {image : Image} {b : Nat} (hb : Allowed b) (hc : At image b)
    (s : MachineState) (hint : Word) (hpc : s.pc=pcOf (b+154)) (h29 : s.getReg .x29=hint) :
    ∃ t, Steps image s 2 2 t ∧ t.pc=pcOf (b+156) ∧
      t.getMem (BitVec.ofNat 64 HINT)=hint ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun A=>A=HINT) := by
  refine ⟨_,symRun_sound (store_run b hb) (slice hc 154 2 (by decide)) s hpc
    (by simp [storeResult,storeBase.res,rv_simp,accessValid_iff,MEMORY_BYTES]),rfl,?_,?_,?_⟩
  · simp [storeResult,storeBase.res,rv_simp,HINT,DIGITS,h29]
  · intro r hr; cases r <;> simp_all [storeResult,storeBase.res,rv_simp] <;> rfl
  · intro A hA hn
    simp only [storeResult,storeBase.res,rv_simp]
    have he : BitVec.ofNat 64 A≠132184#64 := by
      intro h
      have hh := (ofNat_inj hA (by decide)).mp h
      exact hn hh
    simp [he]

end SigGolfCandidate.Choice.ProducerSelector
#print axioms SigGolfCandidate.Choice.ProducerSelector.body_spec
#print axioms SigGolfCandidate.Choice.ProducerSelector.decision_spec
#print axioms SigGolfCandidate.Choice.ProducerSelector.store_spec
