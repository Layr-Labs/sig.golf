import SigGolfCandidate.PathBlock
import SigGolfCandidate.OneLabelArithmetic
import SigGolfCandidate.Merge054
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace SigGolfCandidate.T3M.KeygenLabel
open _root_.SigGolfCandidate.T3M.OneLabelArithmetic (arithmetic arithmetic_eq arithmetic_seven)
def pre : List (BitVec 32) := [0x5c1e13,0x2e0e33,0x20f37,0x200f0f13,0xe3303,0x8e3383,0x6f3023,0x7f3423,0x20f37,0x230f0f13,0x10e3303,0x18e3383,0x6f3023,0x7f3423,0x2049e13,0x1cae333,0x6710006f,0xfe6f3023,0xfe0f3423,0x1c7e93]
def stub : List (BitVec 32) := [0x1830333,0xfff30193,0x11b193,0xd13b7,0xfff38393,0x403001b3,0x71f1b3,0x330333,0xff930193,0x19663,0x7f337,0x968ff06f,0x13,0x960ff06f]
def look (n : Nat) : Option (BitVec 32) :=
  if 237 ≤ n ∧ n < 257 then pre[n-237]? else if 1177 ≤ n ∧ n < 1191 then stub[n-1177]? else none
def run (nz : Bool) : Option PRes := pathAux {noAlias := true} look [pcOf 257] 100 (pcOf 237) [.br nz] (σK []) []
def fallback : PRes := ⟨SymState.init, 0, false, 0, 0, [], none⟩
path_block frozenEq := (run false).getD fallback
path_block frozenNe := (run true).getD fallback
theorem run_eq : run false = some frozenEq.res := by kernel_rfl
theorem run_ne : run true = some frozenNe.res := by kernel_rfl
theorem count_eq : frozenEq.res.steps = 32 ∧ frozenEq.res.cycles = 32 := by decide
theorem count_ne : frozenNe.res.steps = 32 ∧ frozenNe.res.cycles = 32 := by decide

def result (nz : Bool) : PRes := if nz then frozenNe.res else frozenEq.res

theorem run_result (nz : Bool) : run nz = some (result nz) := by
  cases nz
  · exact run_eq
  · exact run_ne

theorem result_count (nz : Bool) : (result nz).steps = 32 ∧ (result nz).cycles = 32 := by
  cases nz
  · exact count_eq
  · exact count_ne

theorem look_ok : LookOK Images.keygenImage look := by
  intro n w hw
  unfold look at hw
  split_ifs at hw with h1 h2
  · rcases h1 with ⟨hn0, hn1⟩
    interval_cases n <;> norm_num [pre] at hw <;> subst w <;> decide +kernel
  · rcases h2 with ⟨hn0, hn1⟩
    interval_cases n <;> norm_num [stub] at hw <;> subst w <;> decide +kernel

def remapWord (x : Word) : Word := if x = 1#64 then 856064#64 else if x = 7#64 then 520192#64 else x

def rawWord (s : MachineState) : Word := (s.getReg .x21 ||| (s.getReg .x9 <<< 32)) + s.getReg .x24

theorem branches_hold (nz : Bool) (s : MachineState) (hb : (rawWord s ≠ 7#64) ↔ nz = true) :
    ∀ b ∈ (result nz).brs, b.holds s := by
  have he : arithmetic (rawWord s)+18446744073709551609#64=0#64 ↔ rawWord s=7#64 := by
    have hk : 18446744073709551609#64 = -(7#64) := by decide
    rw [hk,←BitVec.sub_eq_add_neg,BitVec.sub_eq_iff_eq_add]
    simpa using arithmetic_seven (rawWord s)
  cases nz <;> simp only [result, Bool.false_eq_true, if_false, if_true,
    frozenEq.res, frozenNe.res, List.mem_cons, List.not_mem_nil, or_false]
  all_goals
    intro b hm
    subst b
    change ((arithmetic (rawWord s)+18446744073709551609#64) != 0#64) = _
    simp_all

theorem steps {im : Image} (hl : LookOK im look) (nz : Bool) (s : MachineState)
    (hpc : s.pc = pcOf 237)
    (hobl : ∀ o ∈ (result nz).st.obl, o.holds s)
    (hb : (rawWord s ≠ 7#64) ↔ nz = true) :
    Steps im s 32 32 ((result nz).toState s) := by
  have hh := pathRun_sound (known := []) (run_result nz) hl s hpc
    (by intro p hp; cases hp) hobl (branches_hold nz s hb)
  exact hh.1.of_eq (result_count nz).1 (result_count nz).2

theorem post_pc (nz : Bool) (s : MachineState) : ((result nz).toState s).pc = pcOf 257 := by
  cases nz <;> rfl

theorem post_low (nz : Bool) (s : MachineState) :
    ((result nz).toState s).getMem 131600#64 =
      if nz then (if rawWord s=1#64 then 856064#64 else rawWord s) else 520192#64 := by
  cases nz
  · rfl
  · change arithmetic (rawWord s) = _
    exact arithmetic_eq _

theorem post_high (nz : Bool) (s : MachineState) :
    ((result nz).toState s).getMem 131608#64 = 0#64 := by
  cases nz <;> rfl

theorem post_left_lo (nz : Bool) (s : MachineState) :
    ((result nz).toState s).getMem 131584#64 = s.getMem ((s.getReg .x24 <<< 5) + s.getReg .x2) := by
  cases nz <;> rfl

theorem post_left_hi (nz : Bool) (s : MachineState) :
    ((result nz).toState s).getMem 131592#64 = s.getMem (((s.getReg .x24 <<< 5) + s.getReg .x2) + 8) := by
  cases nz <;> rfl

theorem post_right_lo (nz : Bool) (s : MachineState) :
    ((result nz).toState s).getMem 131632#64 = s.getMem (((s.getReg .x24 <<< 5) + s.getReg .x2) + 16) := by
  cases nz <;> rfl

theorem post_right_hi (nz : Bool) (s : MachineState) :
    ((result nz).toState s).getMem 131640#64 = s.getMem (((s.getReg .x24 <<< 5) + s.getReg .x2) + 24) := by
  cases nz <;> rfl

theorem post_half (nz : Bool) (s : MachineState) :
    ((result nz).toState s).getReg .x29 = s.getReg .x24 &&& 1#64 := by
  cases nz <;> rfl

theorem post_pointer (nz : Bool) (s : MachineState) :
    ((result nz).toState s).getReg .x30 = 131632#64 := by
  cases nz <;> rfl

theorem post_regs (nz : Bool) (s : MachineState) :
    RegsExcept s ((result nz).toState s) [.x3, .x6, .x7, .x28, .x29, .x30] := by
  cases nz <;> intro r hr <;> cases r <;> try (simp at hr) <;> rfl

theorem post_frame (nz : Bool) (s : MachineState) :
    Frame s ((result nz).toState s)
      (fun A => A = 131584 ∨ A = 131592 ∨ A = 131600 ∨ A = 131608 ∨ A = 131632 ∨ A = 131640) := by
  cases nz
  · intro A hA hn
    change memEval s frozenEq.res.st.mem (BitVec.ofNat 64 A) = _
    simp only [frozenEq.res]
    t3n [memEval, Addr.eval, E.eval]
    split_ifs <;> first | omega | rfl
  · intro A hA hn
    change memEval s frozenNe.res.st.mem (BitVec.ofNat 64 A) = _
    simp only [frozenNe.res]
    t3n [memEval, Addr.eval, E.eval]
    split_ifs <;> first | omega | rfl

end SigGolfCandidate.T3M.KeygenLabel
