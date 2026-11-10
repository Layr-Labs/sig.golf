import SigGolfCandidate.Merge055
set_option debug.skipKernelTC false
namespace SigGolfCandidate.T3M.AllRoutePath
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
 def lookOf (base : Nat) (code : List (BitVec 32)) (n : Nat) : Option (BitVec 32) :=
  if base ≤ n then code[n-base]? else none
 theorem lookOK_of_codeAt {image : Image} {base : Nat} {code : List (BitVec 32)}
    (hb : (pcOf base).toNat = 4096+4*base) (hc : CodeAt image (pcOf base) code) : LookOK image (lookOf base code) := by
  have hoff : ((pcOf base).toNat-4096)/4 = base := by rw [hb]; omega
  have hp := hc.2.2.2
  rw [hoff] at hp
  intro n w hw
  unfold lookOf at hw
  split_ifs at hw with hn
  · obtain ⟨hi,he⟩ := List.getElem?_eq_some_iff.mp hw
    have hdrop : (image.code.drop base)[n-base]? = some w :=
      List.getElem?_eq_some_iff.mpr ⟨lt_of_lt_of_le hi hp.length_le, (hp.getElem hi).symm.trans he⟩
    simpa only [List.getElem?_drop, Nat.add_sub_of_le hn] using hdrop

 def pureCheck (out : Option PRes) (post : List (Reg × Word)) (keep : List Reg) (stop bound : Nat) : Bool :=
  match out with
  | none => false
  | some r => knownB post r && keepB keep r && decide (r.pc = pcOf stop) &&
      decide (r.steps ≤ bound) && decide (r.cycles = r.steps) &&
      r.st.mem.isEmpty && r.st.obl.isEmpty && r.brs.isEmpty && r.spc.isNone
 theorem pure_run {cfg : Config} {image : Image} {look : Nat → Option (BitVec 32)}
    {stops : List Word} {fuel : Nat} {pc : Word} {dirs : List Dir} {known post : List (Reg × Word)}
    {keep : List Reg} {stop bound : Nat}
    (hl : LookOK image look)
    (hcheck : pureCheck (pathAux cfg look stops fuel pc dirs (σK known) []) post keep stop bound = true)
    (s : MachineState) (hpc : s.pc=pc) (hk : KnownOK known s) :
    ∃ t n, Steps image s n n t ∧ n≤bound ∧ t.pc=pcOf stop ∧ KnownOK post t ∧
      (∀ r∈keep, t.getReg r=s.getReg r) ∧ Frame s t (fun _=>False) := by
  cases hr : pathAux cfg look stops fuel pc dirs (σK known) [] with
  | none => simp [hr,pureCheck] at hcheck
  | some r =>
    simp only [hr,pureCheck,Bool.and_eq_true,decide_eq_true_eq,List.isEmpty_iff,Option.isNone_iff_eq_none] at hcheck
    have hp : knownB post r=true := by tauto
    have hkeep : keepB keep r=true := by tauto
    have hstop : r.pc=pcOf stop := by tauto
    have hn : r.steps≤bound := by tauto
    have hcy : r.cycles=r.steps := by tauto
    have hm : r.st.mem=[] := by tauto
    have ho : r.st.obl=[] := by tauto
    have hb : r.brs=[] := by tauto
    have hs : r.spc=none := by tauto
    obtain ⟨hex,_⟩ := pathRun_sound hr hl s hpc hk (by simp [ho]) (by simp [hb])
    rw [hcy] at hex
    refine ⟨r.toState s,r.steps,hex,hn,?_,knownB_ok hp s,keepB_ok hkeep s,?_⟩
    · rw [PRes.toState_pc _ _ hs,hstop]
    · intro A hA hnot
      change memEval s r.st.mem A=s.getMem A
      rw [hm]
      rfl
#print axioms lookOK_of_codeAt
#print axioms pure_run
end SigGolfCandidate.T3M.AllRoutePath
