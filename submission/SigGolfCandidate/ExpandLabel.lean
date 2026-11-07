import SigGolfCandidate.PathBlock
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace SigGolfCandidate.T3M.ExpandLabel
def window : List (BitVec 32) := [0x100006f,0xff930193,0xfe019ce3,0x7f337]
def jump : BitVec 32 := 0xd38d706f
def look (n : Nat) : Option (BitVec 32) :=
  if 1125 ≤ n ∧ n < 1129 then window[n-1125]? else if n = 42776 then some jump else none
def run (nz : Bool) : Option PRes := pathAux {noAlias := true} look [pcOf 1129] 20 (pcOf 42776) [.br nz] (σK []) []
def fallback : PRes := ⟨SymState.init, 0, false, 0, 0, [], none⟩
path_block frozenEq := (run false).getD fallback
path_block frozenNe := (run true).getD fallback
theorem run_eq : run false = some frozenEq.res := by kernel_rfl
theorem run_ne : run true = some frozenNe.res := by kernel_rfl
def result (nz : Bool) : PRes := if nz then frozenNe.res else frozenEq.res
theorem run_result (nz : Bool) : run nz = some (result nz) := by
  cases nz
  · exact run_eq
  · exact run_ne
theorem result_count (nz : Bool) : (result nz).steps = 4 ∧ (result nz).cycles = 4 := by
  cases nz <;> decide

theorem look_ok {im : Image} (hw : window <+: im.code.drop 1125)
    (hj : [jump] <+: im.code.drop 42776) : LookOK im look := by
  intro n w h
  unfold look at h
  split_ifs at h with h1 h2
  · obtain ⟨rest, hr⟩ := hw
    have hi : n - 1125 < window.length := (List.getElem?_eq_some_iff.mp h).1
    have he : (im.code.drop 1125)[n-1125]? = some w := by
      rw [← hr, List.getElem?_append_left hi]
      exact h
    rwa [List.getElem?_drop, Nat.add_sub_cancel' h1.1] at he
  · subst n
    simp only [Option.some.injEq] at h
    subst w
    obtain ⟨rest, hr⟩ := hj
    have he : (im.code.drop 42776)[0]? = some jump := by rw [← hr]; rfl
    simpa only [List.getElem?_drop, Nat.add_zero] using he

theorem branches_hold (nz : Bool) (s : MachineState) (hb : (s.getReg .x6 ≠ 7#64) ↔ nz = true) :
    ∀ b ∈ (result nz).brs, b.holds s := by
  have he : s.getReg .x6 + 18446744073709551609#64 = 0#64 ↔ s.getReg .x6 = 7#64 := by
    have hk : 18446744073709551609#64 = -(7#64) := by decide
    rw [hk, ← BitVec.sub_eq_add_neg, BitVec.sub_eq_iff_eq_add]
    rfl
  cases nz <;> simp only [result, Bool.false_eq_true, if_false, if_true,
    frozenEq.res, frozenNe.res, List.mem_cons, List.not_mem_nil, or_false]
  all_goals
    intro b hm
    subst b
    change ((s.getReg .x6 + 18446744073709551609#64) != 0#64) = _
    simp_all

theorem steps {im : Image} (hl : LookOK im look) (nz : Bool) (s : MachineState)
    (hpc : s.pc = pcOf 42776)
    (hobl : ∀ o ∈ (result nz).st.obl, o.holds s)
    (hb : (s.getReg .x6 ≠ 7#64) ↔ nz = true) :
    Steps im s 4 4 ((result nz).toState s) := by
  have hh := pathRun_sound (known := []) (run_result nz) hl s hpc
    (by intro p hp; cases hp) hobl (branches_hold nz s hb)
  exact hh.1.of_eq (result_count nz).1 (result_count nz).2

theorem post_pc (nz : Bool) (s : MachineState) : ((result nz).toState s).pc = pcOf 1129 := by
  cases nz <;> rfl

theorem post_word (nz : Bool) (s : MachineState) :
    ((result nz).toState s).getReg .x6 = if nz then s.getReg .x6 else 520192#64 := by
  cases nz <;> rfl

theorem post_regs (nz : Bool) (s : MachineState) :
    RegsExcept s ((result nz).toState s) [.x3, .x6] := by
  cases nz <;> intro r hr <;> cases r <;> try (simp at hr) <;> rfl

theorem post_frame (nz : Bool) (s : MachineState) :
    Frame s ((result nz).toState s) (fun _ => False) := by
  intro A hA hn
  cases nz <;> rfl

theorem post_word_ofNat (s : MachineState) (heapNat : Nat) (hheap : heapNat < 2^64)
    (x6 : s.getReg .x6 = BitVec.ofNat 64 heapNat) :
    let heap := heapNat
    let nz := decide (s.getReg .x6 ≠ 7#64)
    ((result nz).toState s).getReg .x6 = BitVec.ofNat 64 (if heap = 7 then 520192 else heap) := by
  intro heap nz
  rw [post_word]
  by_cases hh7 : heap = 7
  · have hx : s.getReg .x6 = 7#64 := by
      rw [x6]
      change BitVec.ofNat 64 heap = 7#64
      rw [hh7]
    rw [show nz = false by simp [nz, hx]]
    simp only [if_neg (by decide : false ≠ true), if_pos hh7]
  · have hx : s.getReg .x6 ≠ 7#64 := by
      rw [x6]
      change BitVec.ofNat 64 heap ≠ 7#64
      exact fun he => hh7 ((ofNat_inj hheap (by decide)).mp he)
    rw [show nz = true by simp [nz, hx]]
    simpa only [if_pos (rfl : true = true), if_true, if_neg hh7] using x6

end SigGolfCandidate.T3M.ExpandLabel
