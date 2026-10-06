import SigGolfCandidate.T3M.Verify.Nonbinary.InlinePrefixCode
import SigGolfCandidate.T3M.Verify.Post

/- The exact real lookup for unchanged native words. Modified tail-JT rows
   are outside this partial lookup; no soundness for their old bytes is claimed.
   Merkle guards must execute this real partial lookup when instantiated. -/
namespace SigGolfCandidate.T3M.Nonbinary.InlineTail
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def prefixLook (n : Nat) : Option (BitVec 32) := if n<176896 then vlook n else none

theorem prefixLook_ok : LookOK InlineTail.image prefixLook := by
  intro n w hw
  unfold prefixLook at hw
  split at hw
  · rename_i hn
    have h:=vlook_ok n w hw
    have he:=congrArg (fun ws : List (BitVec 32)=>ws[0]?)
      (prefix_window_equal n 1 (by omega))
    simp only [List.getElem?_take,List.getElem?_drop,Nat.add_zero,
      show (0<1 : Prop) from by decide,if_true] at he
    exact he.trans h
  · cases hw

def prefixRunAt (known : List (Reg × Word)) (stops : List Nat)
    (n : Nat) (dirs : List Dir) : Option PRes :=
  pathAux cfg0 prefixLook (stops.map pcOf) 2000 (pcOf n) dirs (σK known) []

theorem prefix_path_sound {known : List (Reg × Word)} {stops : List Nat}
    {n : Nat} {dirs : List Dir} {r : PRes}
    (hr : prefixRunAt known stops n dirs=some r)
    (s : MachineState) (hp : s.pc=pcOf n) (hk : KnownOK known s)
    (ho : ∀ o∈r.st.obl,o.holds s) (hb : ∀ b∈r.brs,b.holds s) :
    Steps InlineTail.image s r.steps r.cycles (r.toState s) ∧
      (r.ecall=true → fetch InlineTail.image (r.toState s)=some (.base .ECALL)) :=
  pathRun_sound hr prefixLook_ok s hp hk ho hb

#print axioms prefixLook_ok
#print axioms prefix_path_sound
end SigGolfCandidate.T3M.Nonbinary.InlineTail
