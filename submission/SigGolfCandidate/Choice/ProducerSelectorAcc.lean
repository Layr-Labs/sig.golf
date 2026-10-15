import SigGolfCandidate.Choice.ProducerSelector

namespace SigGolfCandidate.Choice.ProducerSelector
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Search SigGolfCandidate.T3M.Search.Reward
open SigGolfCandidate.T3 (Digest)
open ClaudeWCT.WCT9
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

def accReg (r : Bool) : Reg := if r then .x20 else .x25
def addCode (r : Bool) : List (BitVec 32) := (words.drop (if r then 16 else 14)).take 1
def addState (r : Bool) : SymState :=
  ⟨if r then {RegFile.init with r20:=mkAdd (.reg .x20) (.reg .x29)}
    else {RegFile.init with r25:=mkAdd (.reg .x25) (.reg .x29)},[],[]⟩
def addResult (p : Word) (r : Bool) : Result := ⟨addState r,.c (p+4),.endOfCode,1,1⟩
theorem add_run (pc : Word) (r : Bool) :
    symRun {noAlias:=true} (addCode r) pc 2 = some (addResult pc r) := by
  cases r <;> rfl

theorem add_spec {image : Image} {b : Nat} (hc : At image b)
    (s : MachineState) (q : Nat) (hq : q<17) (r : Bool) (a z : Word)
    (hpc : s.pc=pcOf (b+loadIndex q r+1))
    (ha : s.getReg (accReg r)=a) (hz : s.getReg .x29=z) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf (b+loadIndex q r+2) ∧
      t.getReg (accReg r)=a+z ∧ RegsExcept s t [accReg r] ∧ Frame s t (fun _=>False) := by
  have hcode : CodeAt image (pcOf (b+loadIndex q r+1)) (addCode r) := by
    have h := slice hc (loadIndex q r+1) 1 (by unfold loadIndex start plen; split_ifs <;> omega)
    have he : (words.drop (loadIndex q r+1)).take 1=addCode r := by
      cases r <;> interval_cases q <;> kernel_rfl
    simpa only [Nat.add_assoc,he] using h
  refine ⟨_,symRun_sound (add_run _ r) hcode s hpc (by cases r <;> simp [addResult,addState,rv_simp]),?_,?_,?_,?_⟩
  · simp only [addResult,Result.toState_pc,E.eval,pcOf_add4,Nat.add_assoc,Nat.reduceAdd]
  · cases r <;> simpa [accReg,addResult,addState,rv_simp,mkAdd_eval] using congrArg₂ (fun x y : Word => x+y) ha hz
  · intro reg hr; cases r <;> cases reg <;> simp_all [accReg,addResult,addState,RegFile.init,rv_simp] <;> rfl
  · intro A _ _; cases r <;> rfl

theorem start_succ (q : Nat) : start (q+1)=start q+plen q+4 := by
  unfold start plen; split_ifs <;> omega

theorem group_spec {image : Image} {b : Nat} (hb : Allowed b) (hc : At image b)
    (s : MachineState) (v : Digest) (q : Nat) (hq : q<17) (sum score : Nat)
    (hsum : SumTableOK s) (hrew : RewardTablesOK s)
    (hpc : s.pc=pcOf (b+start q))
    (h6 : s.getReg .x6=v.extractLsb' 0 64) (h7 : s.getReg .x7=v.extractLsb' 64 64)
    (h11 : s.getReg .x11=BitVec.ofNat 64 (TOP_DATA+2048))
    (h25 : s.getReg .x25=BitVec.ofNat 64 sum) (h20 : s.getReg .x20=BitVec.ofNat 64 score) :
    ∃ t, Steps image s (plen q+4) (plen q+4) t ∧ t.pc=pcOf (b+start (q+1)) ∧
      t.getReg .x25=BitVec.ofNat 64 (sum+rankLookup (topRank v q)) ∧
      t.getReg .x20=BitVec.ofNat 64 (score+topLookup (topKind q) (topRank v q)) ∧
      RegsExcept s t [.x10,.x20,.x25,.x28,.x29] ∧ Frame s t (fun _=>False) := by
  obtain ⟨t1,s1,p1,g1,r1,f1⟩ := prefix_spec hb hc s v q hq hpc h6 h7 h11
  obtain ⟨t2,s2,p2,g2,r2,f2⟩ := load_spec hb hc t1 v q hq false
    (hsum.frame f1 (by simp)) (hrew.frame f1 (by simp)) (by simpa [loadIndex,Nat.add_assoc] using p1) g1
  obtain ⟨t3,s3,p3,g3,r3,f3⟩ := add_spec hc t2 q hq false _ _ p2
    (by rw [show accReg false=.x25 from rfl,r2.get (by decide),r1.get (by decide),h25]) g2
  have f13 := (f1.trans f2).trans f3
  obtain ⟨t4,s4,p4,g4,r4,f4⟩ := load_spec hb hc t3 v q hq true
    (hsum.frame f13 (by simp)) (hrew.frame f13 (by simp))
    (by simpa [loadIndex,Nat.add_assoc] using p3)
    (by rw [r3.get (by decide),r2.get (by decide)]; exact g1)
  obtain ⟨t5,s5,p5,g5,r5,f5⟩ := add_spec hc t4 q hq true _ _ p4
    (by rw [show accReg true=.x20 from rfl,r4.get (by decide),r3.get (by decide),r2.get (by decide),r1.get (by decide),h20]) g4
  refine ⟨t5,by simpa only [Nat.add_assoc] using (((s1.trans s2).trans s3).trans s4).trans s5,?_,?_,?_,
    ((((r1.trans r2).trans r3).trans r4).trans r5).mono (by decide),
    ((((f1.trans f2).trans f3).trans f4).trans f5).mono (by simp)⟩
  · simpa [start_succ,loadIndex,Nat.add_assoc] using p5
  · rw [r5.get (by decide),r4.get (by decide)]
    simpa [accReg,lookupValue,ofNat_add_ofNat] using g3
  · simpa [accReg,lookupValue,ofNat_add_ofNat] using g5

def runningSum (v : Digest) (n : Nat) : Nat := ((List.range n).map (fun q => rankLookup (topRank v q))).sum
def runningScore (v : Digest) (n : Nat) : Nat := ((List.range n).map (fun q => topLookup (topKind q) (topRank v q))).sum

theorem runningSum_succ (v : Digest) (n : Nat) :
    runningSum v (n+1)=runningSum v n+rankLookup (topRank v n) := by simp [runningSum,List.range_succ]
theorem runningScore_succ (v : Digest) (n : Nat) :
    runningScore v (n+1)=runningScore v n+topLookup (topKind n) (topRank v n) := by simp [runningScore,List.range_succ]

theorem iter {image : Image} {b : Nat} (hb : Allowed b) (hc : At image b)
    (s : MachineState) (v : Digest) (n : Nat) (hn : n≤17)
    (hsum : SumTableOK s) (hrew : RewardTablesOK s)
    (hpc : s.pc=pcOf (b+10))
    (h6 : s.getReg .x6=v.extractLsb' 0 64) (h7 : s.getReg .x7=v.extractLsb' 64 64)
    (h11 : s.getReg .x11=BitVec.ofNat 64 (TOP_DATA+2048))
    (h25 : s.getReg .x25=0) (h20 : s.getReg .x20=0) :
    ∃ t, Steps image s (start n-10) (start n-10) t ∧ t.pc=pcOf (b+start n) ∧
      t.getReg .x25=BitVec.ofNat 64 (runningSum v n) ∧
      t.getReg .x20=BitVec.ofNat 64 (runningScore v n) ∧
      RegsExcept s t [.x10,.x20,.x25,.x28,.x29] ∧ Frame s t (fun _=>False) := by
  induction n with
  | zero => exact ⟨s,Steps.refl _,hpc,h25,h20,RegsExcept.refl _ _,Frame.refl _ _⟩
  | succ n ih =>
    obtain ⟨t1,s1,p1,g25,g20,r1,f1⟩ := ih (by omega)
    obtain ⟨t2,s2,p2,g25',g20',r2,f2⟩ := group_spec hb hc t1 v n (by omega)
      (runningSum v n) (runningScore v n) (hsum.frame f1 (by simp)) (hrew.frame f1 (by simp)) p1
      (by rw [r1.get (by decide),h6]) (by rw [r1.get (by decide),h7])
      (by rw [r1.get (by decide),h11]) g25 g20
    refine ⟨t2,?_,p2,?_,?_,(r1.trans r2).mono (by decide),(f1.trans f2).mono (by simp)⟩
    · have he : start n-10+(plen n+4)=start (n+1)-10 := by
        rw [start_succ]
        have : 10 ≤ start n := by unfold start; omega
        omega
      simpa only [he] using s1.trans s2
    · simpa only [runningSum_succ] using g25'
    · simpa only [runningScore_succ] using g20'

end SigGolfCandidate.Choice.ProducerSelector
#print axioms SigGolfCandidate.Choice.ProducerSelector.iter
