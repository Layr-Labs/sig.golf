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
def chain : List (BitVec 32) := [0xff830193,0x19863,0x337,0x30313,0x935aa06f,0xff730193,0x2019463,0x71c72337,0xc7130313,0xb31313,0x63830313,0xb31313,0x71c30313,0xa31313,0x1c730313,0x909aa06f,0xff630193,0x19863,0x3337,0xf2030313,0x8f5aa06f,0xff530193,0x19863,0x3337,0xfd030313,0x8e1aa06f,0xff430193,0x19863,0x3337,0xef030313,0x8cdaa06f,0xff330193,0x19863,0x3337,0xec030313,0x8b9aa06f,0xff230193,0x19863,0x3337,0xf8030313,0x8a5aa06f,0xff130193,0x19863,0x3337,0xf5030313,0x891aa06f,0x2680006f]
/-- C42: the label chain of heaps 4/5/6 (expand words 88800..88817, entered from `88646: jal 88800`), C46: then heap 2
(88818..88823), every `jal` back to 1129; C47: heap 5's label is `0xffbde0`. -/
def chain2 : List (BitVec 32) := [0xffc30193,0x19863,0xe3337,0x30430313,0xe14aa06f,0xffb30193,0x19863,0xffc337,0xde030313,0xe00aa06f,0xffa30193,0x19e63,0x60060337,0x831313,0x330313,0x1231313,0x630313,0xde0aa06f,0xffe30193,0x19863,0xf2337,0xb0230313,0xdccaa06f,0x200006f]
/-- C47: the heap-3 label (expand words 88831..88838, entered from `88823: jal 88831`): `addi gp,t1,-3;
bne gp,zero,88838; t1 := 0xe7404003 (lui; addi; slli; addi); jal 1129`, then `jal 1129`. -/
def chain3 : List (BitVec 32) := [0xffd30193,0x19c63,0x73a02337,0x130313,0x131313,0x130313,0xd90aa06f,0xd8caa06f]
def look (n : Nat) : Option (BitVec 32) :=
  if 1125 ≤ n ∧ n < 1129 then window[n-1125]?
  else if 231593 ≤ n ∧ n < 231602 then remapCode[n-231593]?
  else if n=42776 then some jump
  else if 88600 ≤ n ∧ n < 88647 then chain[n-88600]?
  else if 88800 ≤ n ∧ n < 88824 then chain2[n-88800]?
  else if 88831 ≤ n ∧ n < 88839 then chain3[n-88831]? else none
/-- Path class of the heap word: `0` heap 7, `1 + k` heap `8 + k` (`k < 8`), (C42) `9`, `10`, `11` heaps 4, 5, 6,
(C46) `12` heap 2, (C47) `13` heap 3, `14` every other word. -/
def clsTbl : List Word := [7#64, 8#64, 9#64, 10#64, 11#64, 12#64, 13#64, 14#64, 15#64, 4#64, 5#64, 6#64, 2#64, 3#64]
def cls (x : Word) : Nat := clsTbl.idxOf x
/-- Branch directions of class `c`: the `bne` at 1127, then the chains' `bne`s. -/
def dirs (c : Nat) : List Dir :=
  if c < 14 then List.replicate c (.br true) ++ [.br false] else List.replicate 14 (.br true)
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
path_block frozen10 := (run 10).getD fallback
path_block frozen11 := (run 11).getD fallback
path_block frozen12 := (run 12).getD fallback
path_block frozen13 := (run 13).getD fallback
path_block frozen14 := (run 14).getD fallback
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
theorem run_10 : run 10 = some frozen10.res := by kernel_rfl
theorem run_11 : run 11 = some frozen11.res := by kernel_rfl
theorem run_12 : run 12 = some frozen12.res := by kernel_rfl
theorem run_13 : run 13 = some frozen13.res := by kernel_rfl
theorem run_14 : run 14 = some frozen14.res := by kernel_rfl
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
  | 9 => frozen9.res
  | 10 => frozen10.res
  | 11 => frozen11.res
  | 12 => frozen12.res
  | 13 => frozen13.res
  | _ => frozen14.res
theorem run_result (c : Nat) : run c = some (result c) := by
  rcases c with _|_|_|_|_|_|_|_|_|_|_|_|_|_|c
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
  · exact run_10
  · exact run_11
  · exact run_12
  · exact run_13
  · exact run_14
theorem count_0 : frozen0.res.steps = frozen0.res.cycles ∧ frozen0.res.steps ≤ 46 := by decide
theorem count_1 : frozen1.res.steps = frozen1.res.cycles ∧ frozen1.res.steps ≤ 46 := by decide
theorem count_2 : frozen2.res.steps = frozen2.res.cycles ∧ frozen2.res.steps ≤ 46 := by decide
theorem count_3 : frozen3.res.steps = frozen3.res.cycles ∧ frozen3.res.steps ≤ 46 := by decide
theorem count_4 : frozen4.res.steps = frozen4.res.cycles ∧ frozen4.res.steps ≤ 46 := by decide
theorem count_5 : frozen5.res.steps = frozen5.res.cycles ∧ frozen5.res.steps ≤ 46 := by decide
theorem count_6 : frozen6.res.steps = frozen6.res.cycles ∧ frozen6.res.steps ≤ 46 := by decide
theorem count_7 : frozen7.res.steps = frozen7.res.cycles ∧ frozen7.res.steps ≤ 46 := by decide
theorem count_8 : frozen8.res.steps = frozen8.res.cycles ∧ frozen8.res.steps ≤ 46 := by decide
theorem count_9 : frozen9.res.steps = frozen9.res.cycles ∧ frozen9.res.steps ≤ 46 := by decide
theorem count_10 : frozen10.res.steps = frozen10.res.cycles ∧ frozen10.res.steps ≤ 46 := by decide
theorem count_11 : frozen11.res.steps = frozen11.res.cycles ∧ frozen11.res.steps ≤ 46 := by decide
theorem count_12 : frozen12.res.steps = frozen12.res.cycles ∧ frozen12.res.steps ≤ 46 := by decide
theorem count_13 : frozen13.res.steps = frozen13.res.cycles ∧ frozen13.res.steps ≤ 46 := by decide
theorem count_14 : frozen14.res.steps = frozen14.res.cycles ∧ frozen14.res.steps ≤ 46 := by decide
/-- Every class runs at most 46 steps (one cycle each): 13 (heap 7), 18..32 (heaps 8..15), (C42) 35, 37, 42 (heaps 4, 5,
6), (C46) 41 (heap 2), (C47) 46 (heap 3), 42 (other words). -/
theorem result_count (c : Nat) : (result c).steps = (result c).cycles ∧ (result c).steps ≤ 46 := by
  rcases c with _|_|_|_|_|_|_|_|_|_|_|_|_|_|c
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
  · exact count_10
  · exact count_11
  · exact count_12
  · exact count_13
  · exact count_14
theorem obl_nil (c : Nat) : (result c).st.obl = [] := by
  rcases c with _|_|_|_|_|_|_|_|_|_|_|_|_|_|c <;> rfl
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
    (hc : chain <+: im.code.drop 88600) (hc2 : chain2 <+: im.code.drop 88800)
    (hc3 : chain3 <+: im.code.drop 88831) :
    LookOK im look := by
  intro n w h
  unfold look at h
  split_ifs at h with h1 h2 h3 h4 h5 h6
  · exact prefix_get hw h1.1 h
  · exact prefix_get hp h2.1 h
  · subst n
    simp only [Option.some.injEq] at h
    subst w
    exact prefix_get hj (by omega) (by rfl)
  · exact prefix_get hc h4.1 h
  · exact prefix_get hc2 h5.1 h
  · exact prefix_get hc3 h6.1 h
 theorem post_pc (c : Nat) (s : MachineState) : ((result c).toState s).pc=pcOf 1129 := by
  rcases c with _|_|_|_|_|_|_|_|_|_|_|_|_|_|c <;> rfl
 theorem post_seven (c : Nat) (s : MachineState) : ((result c).toState s).getReg .x7=0#64 := by
  rcases c with _|_|_|_|_|_|_|_|_|_|_|_|_|_|c <;> rfl
 theorem post_regs (c : Nat) (s : MachineState) :
    RegsExcept s ((result c).toState s) [.x3,.x6,.x7] := by
  rcases c with _|_|_|_|_|_|_|_|_|_|_|_|_|_|c <;> intro r hr <;> cases r <;> try (simp at hr) <;> rfl
 theorem post_frame (c : Nat) (s : MachineState) :
    Frame s ((result c).toState s) (fun _ => False) := by
  intro A hA hn
  rcases c with _|_|_|_|_|_|_|_|_|_|_|_|_|_|c <;> rfl

/-- C46: `cls` is the index in `clsTbl` (C47: 14 for every other word); no `split_ifs` over the long chain. -/
theorem cls_get {x : Word} {c : Nat} (hc : cls x = c) (h : c < 14) : x = clsTbl.getD c 0#64 := by
  have hl : clsTbl.idxOf x < clsTbl.length := by unfold cls at hc; rw [hc]; exact h
  have hx := List.getElem_idxOf hl
  unfold cls at hc
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [← hc]; exact hl)]
  simp only [Option.getD_some]
  subst hc
  exact hx.symm
theorem cls_val {x : Word} {c : Nat} (hc : cls x = c) (h : c ≤ 8) : x = BitVec.ofNat 64 (7 + c) := by
  rw [cls_get hc (by omega)]
  interval_cases c <;> rfl
/-- C42: the classes `9..11` are the heaps `4..6`. -/
theorem cls_val2 {x : Word} {c : Nat} (hc : cls x = c) (h9 : 9 ≤ c) (h : c ≤ 11) : x = BitVec.ofNat 64 (c - 5) := by
  rw [cls_get hc (by omega)]
  interval_cases c <;> rfl
/-- C46: the class `12` is the heap `2`. -/
theorem cls_val3 {x : Word} {c : Nat} (hc : cls x = c) (h12 : 12 ≤ c) (h : c ≤ 12) : x = 2#64 := by
  rw [cls_get hc (by omega)]
  interval_cases c
  rfl
/-- C47: the class `13` is the heap `3`. -/
theorem cls_val4 {x : Word} {c : Nat} (hc : cls x = c) (h13 : 13 ≤ c) (h : c ≤ 13) : x = 3#64 := by
  rw [cls_get hc (by omega)]
  interval_cases c
  rfl
theorem cls_other {x : Word} (hx : x ∉ clsTbl) : 14 ≤ cls x := by
  unfold cls
  rw [List.idxOf_eq_length_iff.mpr hx]
  decide
theorem nine_raw {x : Word} {c : Nat} (hc : cls x = c) (h : 14 ≤ c) :
    x ≠ 7#64 ∧ x ≠ 8#64 ∧ x ≠ 9#64 ∧ x ≠ 10#64 ∧ x ≠ 11#64 ∧ x ≠ 12#64 ∧ x ≠ 13#64 ∧ x ≠ 14#64 ∧
      x ≠ 15#64 ∧ x ≠ 4#64 ∧ x ≠ 5#64 ∧ x ≠ 6#64 ∧ x ≠ 2#64 ∧ x ≠ 3#64 := by
  have hn : x ∉ clsTbl := List.idxOf_eq_length_iff.mp
    (Nat.le_antisymm List.idxOf_le_length (by unfold cls at hc; rw [hc]; exact h))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> exact hn (by decide)
theorem arith_ne {x m : Word} (h : x ≠ m) (hm : (14336#64 : Word) ≠ m) : arithmetic x ≠ m := by
  rw [arithmetic_eq]
  split_ifs
  · exact hm
  · exact h
theorem nine_facts {x : Word} {c : Nat} (hc : cls x = c) (h : 14 ≤ c) :
    arithmetic x ≠ 7#64 ∧ arithmetic x ≠ 8#64 ∧ arithmetic x ≠ 9#64 ∧ arithmetic x ≠ 10#64 ∧
      arithmetic x ≠ 11#64 ∧ arithmetic x ≠ 12#64 ∧ arithmetic x ≠ 13#64 ∧ arithmetic x ≠ 14#64 ∧
      arithmetic x ≠ 15#64 ∧ arithmetic x ≠ 4#64 ∧ arithmetic x ≠ 5#64 ∧ arithmetic x ≠ 6#64 ∧ arithmetic x ≠ 2#64 ∧
      arithmetic x ≠ 3#64 := by
  obtain ⟨h7, h8, h9, h10, h11, h12, h13, h14, h15, h4, h5, h6, h2, h3⟩ := nine_raw hc h
  exact ⟨arith_ne h7 (by decide), arith_ne h8 (by decide), arith_ne h9 (by decide), arith_ne h10 (by decide),
    arith_ne h11 (by decide), arith_ne h12 (by decide), arith_ne h13 (by decide), arith_ne h14 (by decide),
    arith_ne h15 (by decide), arith_ne h4 (by decide), arith_ne h5 (by decide), arith_ne h6 (by decide),
    arith_ne h2 (by decide), arith_ne h3 (by decide)⟩
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
  rcases c with _|_|_|_|_|_|_|_|_|_|_|_|_|_|c
  all_goals
    simp only [result, frozen0.res, frozen1.res, frozen2.res, frozen3.res, frozen4.res, frozen5.res, frozen6.res,
      frozen7.res, frozen8.res, frozen9.res, frozen10.res, frozen11.res, frozen12.res, frozen13.res, frozen14.res, List.forall_mem_cons, List.forall_mem_nil, and_true]
    and_intros
  all_goals try (intro _ hnil; cases hnil)
  all_goals
    refine holds_of s _ _ _ ?_ ?_
    · rfl
  all_goals first
    | (have hx := cls_val hc (by omega)
       rw [hx, arithmetic_eq]
       decide)
    | (have hx := cls_val2 hc (by omega) (by omega)
       rw [hx, arithmetic_eq]
       decide)
    | (have hx := cls_val3 hc (by omega) (by omega)
       rw [hx, arithmetic_eq]
       decide)
    | (have hx := cls_val4 hc (by omega) (by omega)
       rw [hx, arithmetic_eq]
       decide)
    | (obtain ⟨a7, a8, a9, a10, a11, a12, a13, a14, a15, a4, a5, a6, a2, a3⟩ := nine_facts hc (by omega)
       first
        | exact ne_true _ _ _ a7 (by decide)
        | exact ne_true _ _ _ a8 (by decide)
        | exact ne_true _ _ _ a9 (by decide)
        | exact ne_true _ _ _ a10 (by decide)
        | exact ne_true _ _ _ a11 (by decide)
        | exact ne_true _ _ _ a12 (by decide)
        | exact ne_true _ _ _ a13 (by decide)
        | exact ne_true _ _ _ a14 (by decide)
        | exact ne_true _ _ _ a15 (by decide)
        | exact ne_true _ _ _ a4 (by decide)
        | exact ne_true _ _ _ a5 (by decide)
        | exact ne_true _ _ _ a6 (by decide)
        | exact ne_true _ _ _ a2 (by decide)
        | exact ne_true _ _ _ a3 (by decide))
 theorem steps {im : Image} (hl : LookOK im look) (c : Nat) (s : MachineState)
    (hpc : s.pc=pcOf 42776) (hc : cls (s.getReg .x6) = c) :
    ∃ n, n ≤ 46 ∧ Steps im s n n ((result c).toState s) := by
  have hh := pathRun_sound (known:=[]) (run_result c) hl s hpc
    (by intro p hp;cases hp) (by rw [obl_nil]; intro o ho; cases ho) (branches_hold c s hc)
  obtain ⟨he, hle⟩ := result_count c
  exact ⟨_, hle, hh.1.of_eq rfl he.symm⟩
/-- C40/C42 (C47: heaps 3/5 -> K/0xffbde0): the label word is `T3.topNodeWord heap` on the heaps `1..4095`. -/
 theorem post_word_ofNat (s : MachineState) (heap : Nat) (h1 : 1 ≤ heap) (h : heap < 4096)
    (x6 : s.getReg .x6=BitVec.ofNat 64 heap) :
    ((result (cls (s.getReg .x6))).toState s).getReg .x6 = BitVec.ofNat 64 (T3.topNodeWord heap) := by
  generalize hc : cls (s.getReg .x6) = c
  by_cases h16 : heap < 16
  · rcases c with _|_|_|_|_|_|_|_|_|_|_|_|_|_|c
    all_goals first
      | (have hx := cls_val hc (by omega)
         rw [x6] at hx
         have hh := (ofNat_inj (by omega) (by omega)).mp hx
         subst hh
         rfl)
      | (have hx := cls_val2 hc (by omega) (by omega)
         rw [x6] at hx
         have hh := (ofNat_inj (by omega) (by omega)).mp hx
         subst hh
         rfl)
      | (have hx := cls_val3 hc (by omega) (by omega)
         rw [x6] at hx
         have hh := (ofNat_inj (by omega) (by omega)).mp (hx.trans (by rfl : (2#64 : Word) = BitVec.ofNat 64 2))
         subst hh
         rfl)
      | (have hx := cls_val4 hc (by omega) (by omega)
         rw [x6] at hx
         have hh := (ofNat_inj (by omega) (by omega)).mp (hx.trans (by rfl : (3#64 : Word) = BitVec.ofNat 64 3))
         subst hh
         rfl)
      | (obtain ⟨h7, h8, h9, h10, h11, h12, h13, h14, h15, h4, h5, h6, h2, h3⟩ := nine_raw hc (by omega)
         change arithmetic (s.getReg .x6) = _
         rw [arithmetic_eq, x6]
         rw [x6] at h7 h8 h9 h10 h11 h12 h13 h14 h15 h4 h5 h6 h2 h3
         interval_cases heap <;> first | contradiction | decide)
  · have hne : ∀ k, k < 16 → BitVec.ofNat 64 heap ≠ BitVec.ofNat 64 k := fun k hk he =>
      absurd ((ofNat_inj (by omega) (by omega)).mp he) (by omega)
    have h9 : 14 ≤ c := by
      rw [← hc, x6]
      apply cls_other
      intro hm
      simp only [clsTbl, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> exact hne _ (by omega) h
    rcases c with _|_|_|_|_|_|_|_|_|_|_|_|_|_|c
    all_goals try omega
    change arithmetic (s.getReg .x6) = _
    rw [arithmetic_eq, x6, if_neg (hne 1 (by omega)), T3.topNodeWord_ge16 (by omega) h]

/-! ### C47: the chain header code-swap stub (expand)

`1266: jal 88839` (was `andi t2,s4,255`) enters the stub 88839..88849 (the same words as keygen's 1262..1272, last
`jal 1038`): the header's step byte is `T3.lowerStepCode step`. Path classes: `0` step 5 (8 steps), `1` step 0 (11),
`2` every other step (10). -/
def hdrStub : List (BitVec 32) := [0xffa7393,0xffb38393,0x38863,0x538393,0x39463,0x500393,0x839393,0x736333,0x809e393,0x736333,0xbf4aa06f]
def hlook (n : Nat) : Option (BitVec 32) := if 88839 ≤ n ∧ n < 88850 then hdrStub[n-88839]? else none
def hdirs (c : Nat) : List Dir :=
  if c = 0 then [.br true] else if c = 1 then [.br false, .br false] else [.br false, .br true]
def hrun (c : Nat) : Option PRes := pathAux {noAlias := true} hlook [pcOf 1038] 30 (pcOf 88839) (hdirs c) (σK []) []
path_block hfrozen0 := (hrun 0).getD fallback
path_block hfrozen1 := (hrun 1).getD fallback
path_block hfrozen2 := (hrun 2).getD fallback
theorem hrun_0 : hrun 0 = some hfrozen0.res := by kernel_rfl
theorem hrun_1 : hrun 1 = some hfrozen1.res := by kernel_rfl
theorem hrun_2 : hrun 2 = some hfrozen2.res := by kernel_rfl
/-- C47: extra header steps of the code-swap stub over the C46 tail (6 words): step 5 -> 9, 0 -> 12, else 11. -/
def hdrX (step : Nat) : Nat := if step = 5 then 3 else if step = 0 then 6 else 5
theorem and255_ofNat {step : Nat} (hs : step < 256) : BitVec.ofNat 64 step &&& 255#64 = BitVec.ofNat 64 step := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, show (255#64).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega
theorem add_m5_ne {step : Nat} (hs : step < 256) (h5 : step ≠ 5) :
    BitVec.ofNat 64 step + 18446744073709551611#64 ≠ 0#64 := by
  intro h
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_add, BitVec.toNat_ofNat] at this
  change (step % 2 ^ 64 + 18446744073709551611) % 2 ^ 64 = 0 at this
  omega
theorem ofNat_ne0 {step : Nat} (hs : step < 256) (h0 : step ≠ 0) : BitVec.ofNat 64 step ≠ 0#64 := by
  intro h
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat] at this
  change step % 2 ^ 64 = 0 at this
  omega
theorem hdr_steps {im : Image} (hl : LookOK im hlook) (s : MachineState) (hpc : s.pc = pcOf 88839)
    (step : Nat) (hs : step < 256) (h20 : s.getReg .x20 = BitVec.ofNat 64 step) :
    ∃ t, Steps im s (5 + hdrX step) (5 + hdrX step) t ∧ t.pc = pcOf 1038 ∧
      t.getReg .x6 = (s.getReg .x6 ||| (BitVec.ofNat 64 (SigGolfCandidate.T3.lowerStepCode step) <<< 8)) |||
        (s.getReg .x19 ||| 128#64) ∧
      t.getReg .x7 = s.getReg .x19 ||| 128#64 ∧ RegsExcept s t [.x6, .x7] ∧ (∀ a, t.getMem a = s.getMem a) := by
  have ha := and255_ofNat hs
  rcases (show step = 5 ∨ step = 0 ∨ (step ≠ 5 ∧ step ≠ 0) by omega) with h | h | ⟨h5, h0⟩
  · subst h
    have hh := pathRun_sound (known := []) hrun_0 hl s hpc (by intro p hp; cases hp) (by intro o ho; cases ho) (by
      intro b hb
      simp only [hfrozen0.res, List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb
      simp only [Br.holds, E.eval, BinOp.eval, CmpOp.eval, h20]
      decide)
    refine ⟨_, hh.1, rfl, ?_, rfl, ?_, fun a => rfl⟩
    · change (s.getReg .x6 ||| ((s.getReg .x20 &&& 255#64) + 18446744073709551611#64) <<< ((8#64).toNat % 64)) |||
        (s.getReg .x19 ||| 128#64) = _
      rw [h20]
      rfl
    · intro r hr; cases r <;> first | rfl | simp at hr
  · subst h
    have hh := pathRun_sound (known := []) hrun_1 hl s hpc (by intro p hp; cases hp) (by intro o ho; cases ho) (by
      intro b hb
      simp only [hfrozen1.res, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      all_goals simp only [Br.holds, E.eval, BinOp.eval, CmpOp.eval, h20]
      all_goals decide)
    refine ⟨_, hh.1, rfl, ?_, rfl, ?_, fun a => rfl⟩
    · rfl
    · intro r hr; cases r <;> first | rfl | simp at hr
  · have hh := pathRun_sound (known := []) hrun_2 hl s hpc (by intro p hp; cases hp) (by intro o ho; cases ho) (by
      intro b hb
      simp only [hfrozen2.res, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · simp only [Br.holds, E.eval, BinOp.eval, CmpOp.eval, h20, ha]
        simpa using ofNat_ne0 hs h0
      · simp only [Br.holds, E.eval, BinOp.eval, CmpOp.eval, h20, ha]
        simpa using add_m5_ne hs h5)
    have hx : hdrX step = 5 := by unfold hdrX; rw [if_neg h5, if_neg h0]
    have hc : SigGolfCandidate.T3.lowerStepCode step = step := by
      unfold SigGolfCandidate.T3.lowerStepCode; rw [if_neg h0, if_neg h5]
    rw [hx]
    refine ⟨_, hh.1, rfl, ?_, rfl, ?_, fun a => rfl⟩
    · change (s.getReg .x6 ||| (s.getReg .x20 &&& 255#64) <<< ((8#64).toNat % 64)) ||| (s.getReg .x19 ||| 128#64) = _
      rw [h20, ha, hc]
      rfl
    · intro r hr; cases r <;> first | rfl | simp at hr
theorem hlook_ok {im : Image} (h : hdrStub <+: im.code.drop 88839) : LookOK im hlook := by
  intro n w hw
  unfold hlook at hw
  split_ifs at hw with h1
  exact prefix_get h h1.1 hw

end SigGolfCandidate.T3M.ExpandLabel
