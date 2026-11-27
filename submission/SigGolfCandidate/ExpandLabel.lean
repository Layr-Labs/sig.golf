import SigGolfCandidate.PathBlock
import SigGolfCandidate.OneLabelArithmetic
set_option debug.skipKernelTC true
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
namespace SigGolfCandidate.T3M.ExpandLabel
open _root_.SigGolfCandidate.T3M.OneLabelArithmetic (arithmetic arithmetic_eq arithmetic_seven)
/-- C40: `1125: jal zero,88600` (was `jal zero,1129`) enters the heap 8..15 label chain. -/
def window : List (BitVec 32) := [0x6cc5506f,0xff930193,0xfe019ce3,0x7f337]
def remapCode : List (BitVec 32) := [0xfff30193,0x11b193,0x33b7,0x7ff38393,0x403001b3,0x71f1b3,0x330333,0x393,0xed51e06f]
def jump : BitVec 32 := 0x644b806f
/-- C40: the label chain of the height-9 heaps 8..15 (expand words 88600..88646), every `jal` back to 1129. -/
def chain : List (BitVec 32) := [0xff830193,0x19863,0x40337,0xe0030313,0x935aa06f,0xff730193,0x2019463,0x71c72337,0xc7130313,0xb31313,0x63830313,0xb31313,0x71c30313,0xa31313,0x1c730313,0x909aa06f,0xff630193,0x19863,0x3337,0xf2030313,0x8f5aa06f,0xff530193,0x19863,0x3337,0xfd030313,0x8e1aa06f,0xff430193,0x19863,0x3337,0xef030313,0x8cdaa06f,0xff330193,0x19863,0x3337,0xec030313,0x8b9aa06f,0xff230193,0x19863,0x3337,0xf8030313,0x8a5aa06f,0xff130193,0x19863,0x3337,0xf5030313,0x891aa06f,0x88daa06f]
def look (n : Nat) : Option (BitVec 32) :=
  if 1125 ≤ n ∧ n < 1129 then window[n-1125]?
  else if 231593 ≤ n ∧ n < 231602 then remapCode[n-231593]?
  else if n=42776 then some jump
  else if 88600 ≤ n ∧ n < 88647 then chain[n-88600]? else none
/-- Path class of the heap word: `0` heap 7, `1 + k` heap `8 + k` (`k < 8`), `9` every other word. -/
def cls (x : Word) : Nat :=
  if x = 7#64 then 0 else if x = 8#64 then 1 else if x = 9#64 then 2 else if x = 10#64 then 3
  else if x = 11#64 then 4 else if x = 12#64 then 5 else if x = 13#64 then 6 else if x = 14#64 then 7
  else if x = 15#64 then 8 else 9
/-- Branch directions of class `c`: the `bne` at 1127, then the chain's `bne`s. -/
def dirs : Nat → List Dir
  | 0 => [.br false]
  | 1 => [.br true, .br false]
  | 2 => [.br true, .br true, .br false]
  | 3 => [.br true, .br true, .br true, .br false]
  | 4 => [.br true, .br true, .br true, .br true, .br false]
  | 5 => [.br true, .br true, .br true, .br true, .br true, .br false]
  | 6 => [.br true, .br true, .br true, .br true, .br true, .br true, .br false]
  | 7 => [.br true, .br true, .br true, .br true, .br true, .br true, .br true, .br false]
  | 8 => [.br true, .br true, .br true, .br true, .br true, .br true, .br true, .br true, .br false]
  | _ => [.br true, .br true, .br true, .br true, .br true, .br true, .br true, .br true, .br true]
def run (c : Nat) : Option PRes := pathAux {noAlias:=true} look [pcOf 1129] 100 (pcOf 42776) (dirs c) (σK []) []
def fallback : PRes := ⟨SymState.init,0,false,0,0,[],none⟩
path_block frozen0 := (run 0).getD fallback
path_block frozen1 := (run 1).getD fallback
path_block frozen2 := (run 2).getD fallback
path_block frozen3 := (run 3).getD fallback
path_block frozen4 := (run 4).getD fallback
path_block frozen5 := (run 5).getD fallback
path_block frozen6 := (run 6).getD fallback
path_block frozen7 := (run 7).getD fallback
path_block frozen8 := (run 8).getD fallback
path_block frozen9 := (run 9).getD fallback
theorem run_0 : run 0 = some frozen0.res := by kernel_rfl
theorem run_1 : run 1 = some frozen1.res := by kernel_rfl
theorem run_2 : run 2 = some frozen2.res := by kernel_rfl
theorem run_3 : run 3 = some frozen3.res := by kernel_rfl
theorem run_4 : run 4 = some frozen4.res := by kernel_rfl
theorem run_5 : run 5 = some frozen5.res := by kernel_rfl
theorem run_6 : run 6 = some frozen6.res := by kernel_rfl
theorem run_7 : run 7 = some frozen7.res := by kernel_rfl
theorem run_8 : run 8 = some frozen8.res := by kernel_rfl
theorem run_9 : run 9 = some frozen9.res := by kernel_rfl
def result : Nat → PRes
  | 0 => frozen0.res
  | 1 => frozen1.res
  | 2 => frozen2.res
  | 3 => frozen3.res
  | 4 => frozen4.res
  | 5 => frozen5.res
  | 6 => frozen6.res
  | 7 => frozen7.res
  | 8 => frozen8.res
  | _ => frozen9.res
theorem run_result (c : Nat) : run c = some (result c) := by
  rcases c with _|_|_|_|_|_|_|_|_|c
  · exact run_0
  · exact run_1
  · exact run_2
  · exact run_3
  · exact run_4
  · exact run_5
  · exact run_6
  · exact run_7
  · exact run_8
  · exact run_9
theorem count_0 : frozen0.res.steps = frozen0.res.cycles ∧ frozen0.res.steps ≤ 32 := by decide
theorem count_1 : frozen1.res.steps = frozen1.res.cycles ∧ frozen1.res.steps ≤ 32 := by decide
theorem count_2 : frozen2.res.steps = frozen2.res.cycles ∧ frozen2.res.steps ≤ 32 := by decide
theorem count_3 : frozen3.res.steps = frozen3.res.cycles ∧ frozen3.res.steps ≤ 32 := by decide
theorem count_4 : frozen4.res.steps = frozen4.res.cycles ∧ frozen4.res.steps ≤ 32 := by decide
theorem count_5 : frozen5.res.steps = frozen5.res.cycles ∧ frozen5.res.steps ≤ 32 := by decide
theorem count_6 : frozen6.res.steps = frozen6.res.cycles ∧ frozen6.res.steps ≤ 32 := by decide
theorem count_7 : frozen7.res.steps = frozen7.res.cycles ∧ frozen7.res.steps ≤ 32 := by decide
theorem count_8 : frozen8.res.steps = frozen8.res.cycles ∧ frozen8.res.steps ≤ 32 := by decide
theorem count_9 : frozen9.res.steps = frozen9.res.cycles ∧ frozen9.res.steps ≤ 32 := by decide
/-- Every class runs at most 32 steps (one cycle each): 13 (heap 7), 18..32 (heaps 8..15), 30 (other words). -/
theorem result_count (c : Nat) : (result c).steps = (result c).cycles ∧ (result c).steps ≤ 32 := by
  rcases c with _|_|_|_|_|_|_|_|_|c
  · exact count_0
  · exact count_1
  · exact count_2
  · exact count_3
  · exact count_4
  · exact count_5
  · exact count_6
  · exact count_7
  · exact count_8
  · exact count_9
theorem obl_nil (c : Nat) : (result c).st.obl = [] := by
  rcases c with _|_|_|_|_|_|_|_|_|c <;> rfl
private theorem prefix_get {im : Image} {xs : List (BitVec 32)} {base n : Nat} {w : BitVec 32}
    (hp : xs <+: im.code.drop base) (hn : base ≤ n) (hg : xs[n-base]?=some w) :
    im.code[n]?=some w := by
  obtain ⟨rest,hr⟩ := hp
  have hi : n-base<xs.length := (List.getElem?_eq_some_iff.mp hg).1
  have he : (im.code.drop base)[n-base]?=some w := by
    rw [←hr,List.getElem?_append_left hi]
    exact hg
  rwa [List.getElem?_drop,Nat.add_sub_cancel' hn] at he
 theorem look_ok {im : Image} (hw : window <+: im.code.drop 1125)
    (hj : [jump] <+: im.code.drop 42776) (hp : remapCode <+: im.code.drop 231593)
    (hc : chain <+: im.code.drop 88600) :
    LookOK im look := by
  intro n w h
  unfold look at h
  split_ifs at h with h1 h2 h3 h4
  · exact prefix_get hw h1.1 h
  · exact prefix_get hp h2.1 h
  · subst n
    simp only [Option.some.injEq] at h
    subst w
    exact prefix_get hj (by omega) (by rfl)
  · exact prefix_get hc h4.1 h
 theorem post_pc (c : Nat) (s : MachineState) : ((result c).toState s).pc=pcOf 1129 := by
  rcases c with _|_|_|_|_|_|_|_|_|c <;> rfl
 theorem post_seven (c : Nat) (s : MachineState) : ((result c).toState s).getReg .x7=0#64 := by
  rcases c with _|_|_|_|_|_|_|_|_|c <;> rfl
 theorem post_regs (c : Nat) (s : MachineState) :
    RegsExcept s ((result c).toState s) [.x3,.x6,.x7] := by
  rcases c with _|_|_|_|_|_|_|_|_|c <;> intro r hr <;> cases r <;> try (simp at hr) <;> rfl
 theorem post_frame (c : Nat) (s : MachineState) :
    Frame s ((result c).toState s) (fun _ => False) := by
  intro A hA hn
  rcases c with _|_|_|_|_|_|_|_|_|c <;> rfl

theorem cls_val {x : Word} {c : Nat} (hc : cls x = c) (h : c ≤ 8) : x = BitVec.ofNat 64 (7 + c) := by
  unfold cls at hc
  split_ifs at hc <;> subst c <;> first | assumption | omega
theorem nine_raw {x : Word} {c : Nat} (hc : cls x = c) (h : 9 ≤ c) :
    x ≠ 7#64 ∧ x ≠ 8#64 ∧ x ≠ 9#64 ∧ x ≠ 10#64 ∧ x ≠ 11#64 ∧ x ≠ 12#64 ∧ x ≠ 13#64 ∧ x ≠ 14#64 ∧
      x ≠ 15#64 := by
  unfold cls at hc
  split_ifs at hc with h7 h8 h9 h10 h11 h12 h13 h14 h15
  all_goals try omega
  exact ⟨h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
theorem arith_ne {x m : Word} (h : x ≠ m) (hm : (14336#64 : Word) ≠ m) : arithmetic x ≠ m := by
  rw [arithmetic_eq]
  split_ifs
  · exact hm
  · exact h
theorem nine_facts {x : Word} {c : Nat} (hc : cls x = c) (h : 9 ≤ c) :
    arithmetic x ≠ 7#64 ∧ arithmetic x ≠ 8#64 ∧ arithmetic x ≠ 9#64 ∧ arithmetic x ≠ 10#64 ∧
      arithmetic x ≠ 11#64 ∧ arithmetic x ≠ 12#64 ∧ arithmetic x ≠ 13#64 ∧ arithmetic x ≠ 14#64 ∧
      arithmetic x ≠ 15#64 := by
  obtain ⟨h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := nine_raw hc h
  exact ⟨arith_ne h7 (by decide), arith_ne h8 (by decide), arith_ne h9 (by decide), arith_ne h10 (by decide),
    arith_ne h11 (by decide), arith_ne h12 (by decide), arith_ne h13 (by decide), arith_ne h14 (by decide),
    arith_ne h15 (by decide)⟩
theorem ne_true (y K m : Word) (hy : y ≠ m) (hK : m + K = 0#64) : (y + K != 0#64) = true := by
  have h : y + K ≠ 0#64 := by
    intro he
    apply hy
    have e1 : y = (y + K) - K := by rw [BitVec.add_sub_cancel]
    have e2 : m = (m + K) - K := by rw [BitVec.add_sub_cancel]
    rw [e1, e2, he, hK]
  simpa using h
theorem holds_of (s : MachineState) (T : E) (K : Word) (d : Bool)
    (hT : T.eval s = arithmetic (s.getReg .x6)) (h : (arithmetic (s.getReg .x6) + K != 0#64) = d) :
    Br.holds s ⟨.ne, .bin .add T (.c K), .c 0#64, d⟩ := by
  simp only [Br.holds, E.eval, BinOp.eval, CmpOp.eval, hT]
  exact h
 theorem branches_hold (c : Nat) (s : MachineState) (hc : cls (s.getReg .x6) = c) :
    ∀ b ∈ (result c).brs,b.holds s := by
  rcases c with _|_|_|_|_|_|_|_|_|c
  all_goals
    simp only [result, frozen0.res, frozen1.res, frozen2.res, frozen3.res, frozen4.res, frozen5.res, frozen6.res,
      frozen7.res, frozen8.res, frozen9.res, List.forall_mem_cons, List.forall_mem_nil, and_true]
    and_intros
  all_goals try (intro _ hnil; cases hnil)
  all_goals
    refine holds_of s _ _ _ ?_ ?_
    · rfl
  all_goals first
    | (have hx := cls_val hc (by omega)
       rw [hx, arithmetic_eq]
       decide)
    | (obtain ⟨a7, a8, a9, a10, a11, a12, a13, a14, a15⟩ := nine_facts hc (by omega)
       first
        | exact ne_true _ _ _ a7 (by decide)
        | exact ne_true _ _ _ a8 (by decide)
        | exact ne_true _ _ _ a9 (by decide)
        | exact ne_true _ _ _ a10 (by decide)
        | exact ne_true _ _ _ a11 (by decide)
        | exact ne_true _ _ _ a12 (by decide)
        | exact ne_true _ _ _ a13 (by decide)
        | exact ne_true _ _ _ a14 (by decide)
        | exact ne_true _ _ _ a15 (by decide))
 theorem steps {im : Image} (hl : LookOK im look) (c : Nat) (s : MachineState)
    (hpc : s.pc=pcOf 42776) (hc : cls (s.getReg .x6) = c) :
    ∃ n, n ≤ 32 ∧ Steps im s n n ((result c).toState s) := by
  have hh := pathRun_sound (known:=[]) (run_result c) hl s hpc
    (by intro p hp;cases hp) (by rw [obl_nil]; intro o ho; cases ho) (branches_hold c s hc)
  obtain ⟨he, hle⟩ := result_count c
  exact ⟨_, hle, hh.1.of_eq rfl he.symm⟩
/-- C40: the label word is `T3.topNodeWord heap` on the heaps `1..4095`. -/
 theorem post_word_ofNat (s : MachineState) (heap : Nat) (h1 : 1 ≤ heap) (h : heap < 4096)
    (x6 : s.getReg .x6=BitVec.ofNat 64 heap) :
    ((result (cls (s.getReg .x6))).toState s).getReg .x6 = BitVec.ofNat 64 (T3.topNodeWord heap) := by
  generalize hc : cls (s.getReg .x6) = c
  by_cases h16 : heap < 16
  · rcases c with _|_|_|_|_|_|_|_|_|c
    all_goals first
      | (have hx := cls_val hc (by omega)
         rw [x6] at hx
         have hh := (ofNat_inj (by omega) (by omega)).mp hx
         subst hh
         rfl)
      | (obtain ⟨h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := nine_raw hc (by omega)
         change arithmetic (s.getReg .x6) = _
         rw [arithmetic_eq, x6]
         rw [x6] at h7 h8 h9 h10 h11 h12 h13 h14 h15
         interval_cases heap <;> first | contradiction | decide)
  · have hne : ∀ k, k < 16 → BitVec.ofNat 64 heap ≠ BitVec.ofNat 64 k := fun k hk he =>
      absurd ((ofNat_inj (by omega) (by omega)).mp he) (by omega)
    have h9 : 9 ≤ c := by
      rw [← hc, x6]
      unfold cls
      rw [if_neg (hne 7 (by omega)), if_neg (hne 8 (by omega)), if_neg (hne 9 (by omega)),
        if_neg (hne 10 (by omega)), if_neg (hne 11 (by omega)), if_neg (hne 12 (by omega)),
        if_neg (hne 13 (by omega)), if_neg (hne 14 (by omega)), if_neg (hne 15 (by omega))]
    rcases c with _|_|_|_|_|_|_|_|_|c
    all_goals try omega
    change arithmetic (s.getReg .x6) = _
    rw [arithmetic_eq, x6, if_neg (hne 1 (by omega)), T3.topNodeWord_ge16 (by omega) h]

end SigGolfCandidate.T3M.ExpandLabel
