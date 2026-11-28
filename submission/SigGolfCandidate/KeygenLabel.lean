import SigGolfCandidate.PathBlock
import SigGolfCandidate.OneLabelArithmetic
import SigGolfCandidate.Merge054
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option debug.skipKernelTC true
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace SigGolfCandidate.T3M.KeygenLabel
open _root_.SigGolfCandidate.T3M.OneLabelArithmetic (arithmetic arithmetic_eq arithmetic_seven)
def pre : List (BitVec 32) := [0x5c1e13,0x2e0e33,0x20f37,0x200f0f13,0xe3303,0x8e3383,0x6f3023,0x7f3423,0x20f37,0x230f0f13,0x10e3303,0x18e3383,0x6f3023,0x7f3423,0x2049e13,0x1cae333,0x6710006f,0xfe6f3023,0xfe0f3423,0x1c7e93]
def stub : List (BitVec 32) := [0x1830333,0xfff30193,0x11b193,0x33b7,0x7ff38393,0x403001b3,0x71f1b3,0x330333,0xff930193,0x19663,0x7f337,0x968ff06f,0x80006f,0x960ff06f]
/-- C40: the label chain of the height-9 heaps 8..15 (keygen words 1191..1237, entered from `1189: jal 1191`): for
`k < 8`, `addi gp,t1,-(8+k); bne gp,zero,next; t1 := label (8+k); jal 254`, then `jal 254`. -/
def chain : List (BitVec 32) := [0xff830193,0x19863,0x337,0x30313,0x94cff06f,0xff730193,0x2019463,0x71c72337,0xc7130313,0xb31313,0x63830313,0xb31313,0x71c30313,0xa31313,0x1c730313,0x920ff06f,0xff630193,0x19863,0x3337,0xf2030313,0x90cff06f,0xff530193,0x19863,0x3337,0xfd030313,0x8f8ff06f,0xff430193,0x19863,0x3337,0xef030313,0x8e4ff06f,0xff330193,0x19863,0x3337,0xec030313,0x8d0ff06f,0xff230193,0x19863,0x3337,0xf8030313,0x8bcff06f,0xff130193,0x19863,0x3337,0xf5030313,0x8a8ff06f,0x40006f]
/-- C42: the label chain of heaps 4/5/6 (keygen words 1238..1255, entered from `1237: jal 1238`), C46: then heap 2
(1256..1261): for `h = 4, 5, 6, 2`, `addi gp,t1,-h; bne gp,zero,next; t1 := topNodeWord h; jal 254`, then `jal 254`. -/
def chain2 : List (BitVec 32) := [0xffc30193,0x19863,0xe3337,0x30430313,0x890ff06f,0xffb30193,0x19863,0xf2337,0xb0530313,0x87cff06f,0xffa30193,0x19e63,0x60060337,0x831313,0x330313,0x1231313,0x630313,0x85cff06f,0xffe30193,0x19863,0xf2337,0xb0230313,0x848ff06f,0x844ff06f]
def look (n : Nat) : Option (BitVec 32) :=
  if 237 ≤ n ∧ n < 257 then pre[n-237]? else if 1177 ≤ n ∧ n < 1262 then (stub ++ chain ++ chain2)[n-1177]? else none
/-- Path class of the raw label word: `0` heap 7, `1 + k` heap `8 + k` (`k < 8`), (C42) `9`, `10`, `11` heaps 4, 5, 6,
(C46) `12` heap 2, `13` every other word. -/
def clsTbl : List Word := [7#64, 8#64, 9#64, 10#64, 11#64, 12#64, 13#64, 14#64, 15#64, 4#64, 5#64, 6#64, 2#64]
def cls (x : Word) : Nat := clsTbl.idxOf x
/-- Branch directions of class `c`: the `bne` at 1186, then the chains' `bne`s. -/
def dirs (c : Nat) : List Dir :=
  if c < 13 then List.replicate c (.br true) ++ [.br false] else List.replicate 13 (.br true)
def run (c : Nat) : Option PRes := pathAux {noAlias := true} look [pcOf 257] 100 (pcOf 237) (dirs c) (σK []) []
def fallback : PRes := ⟨SymState.init, 0, false, 0, 0, [], none⟩
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
  | _ => frozen13.res

theorem run_result (c : Nat) : run c = some (result c) := by
  rcases c with _|_|_|_|_|_|_|_|_|_|_|_|_|c
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

theorem count_0 : frozen0.res.steps = frozen0.res.cycles ∧ frozen0.res.steps ≤ 60 := by decide
theorem count_1 : frozen1.res.steps = frozen1.res.cycles ∧ frozen1.res.steps ≤ 60 := by decide
theorem count_2 : frozen2.res.steps = frozen2.res.cycles ∧ frozen2.res.steps ≤ 60 := by decide
theorem count_3 : frozen3.res.steps = frozen3.res.cycles ∧ frozen3.res.steps ≤ 60 := by decide
theorem count_4 : frozen4.res.steps = frozen4.res.cycles ∧ frozen4.res.steps ≤ 60 := by decide
theorem count_5 : frozen5.res.steps = frozen5.res.cycles ∧ frozen5.res.steps ≤ 60 := by decide
theorem count_6 : frozen6.res.steps = frozen6.res.cycles ∧ frozen6.res.steps ≤ 60 := by decide
theorem count_7 : frozen7.res.steps = frozen7.res.cycles ∧ frozen7.res.steps ≤ 60 := by decide
theorem count_8 : frozen8.res.steps = frozen8.res.cycles ∧ frozen8.res.steps ≤ 60 := by decide
theorem count_9 : frozen9.res.steps = frozen9.res.cycles ∧ frozen9.res.steps ≤ 60 := by decide
theorem count_10 : frozen10.res.steps = frozen10.res.cycles ∧ frozen10.res.steps ≤ 60 := by decide
theorem count_11 : frozen11.res.steps = frozen11.res.cycles ∧ frozen11.res.steps ≤ 60 := by decide
theorem count_12 : frozen12.res.steps = frozen12.res.cycles ∧ frozen12.res.steps ≤ 60 := by decide
theorem count_13 : frozen13.res.steps = frozen13.res.cycles ∧ frozen13.res.steps ≤ 60 := by decide

/-- Every class runs at most 60 steps (one cycle each): 32 (heap 7), 36..50 (heaps 8..15), (C42) 53, 55, 60 (heaps
4, 5, 6), (C46) 59 (heap 2), 57 (other words). -/
theorem result_count (c : Nat) : (result c).steps = (result c).cycles ∧ (result c).steps ≤ 60 := by
  rcases c with _|_|_|_|_|_|_|_|_|_|_|_|_|c
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

/-- The chain touches no memory: every class has the obligations of class 0. -/
theorem obl_eq (c : Nat) : (result c).st.obl = frozen0.res.st.obl := by
  rcases c with _|_|_|_|_|_|_|_|_|_|_|_|_|c <;> rfl

private theorem prefix_get {im : Image} {xs : List (BitVec 32)} {base n : Nat} {w : BitVec 32}
    (hp : xs <+: im.code.drop base) (hn : base ≤ n) (hg : xs[n-base]?=some w) :
    im.code[n]?=some w := by
  obtain ⟨rest,hr⟩ := hp
  have hi : n-base<xs.length := (List.getElem?_eq_some_iff.mp hg).1
  have he : (im.code.drop base)[n-base]?=some w := by
    rw [←hr,List.getElem?_append_left hi]
    exact hg
  rwa [List.getElem?_drop,Nat.add_sub_cancel' hn] at he

theorem tail_prefix : stub ++ chain ++ chain2 <+: Images.keygenImage.code.drop 1177 := by
  rw [show Images.keygenImage.code.drop 1177 = stub ++ chain ++ chain2 by decide +kernel]

theorem look_ok : LookOK Images.keygenImage look := by
  intro n w hw
  unfold look at hw
  split_ifs at hw with h1 h2
  · rcases h1 with ⟨hn0, hn1⟩
    interval_cases n <;> norm_num [pre] at hw <;> subst w <;> decide +kernel
  · exact prefix_get tail_prefix h2.1 hw

/-- The label word stored at `NODE + 16` (C41: heap 8 -> 0; C42: heaps 4/5/6): `T3.topNodeWord` on the heaps `1..4095`
(`remapWord_ofNat`). -/
def remapWord (x : Word) : Word :=
  if x = 1#64 then 14336#64 else if x = 7#64 then 520192#64 else if x = 8#64 then 0#64
  else if x = 9#64 then 8198552921648689607#64 else if x = 10#64 then 12064#64 else if x = 11#64 then 12240#64
  else if x = 12#64 then 12016#64 else if x = 13#64 then 11968#64 else if x = 14#64 then 12160#64
  else if x = 15#64 then 12112#64 else if x = 4#64 then 930564#64 else if x = 5#64 then 989957#64
  else if x = 6#64 then 108112779336744966#64 else if x = 2#64 then 989954#64 else x

theorem remapWord_ofNat (heap : Nat) (h1 : 1 ≤ heap) (h : heap < 4096) :
    remapWord (BitVec.ofNat 64 heap) = BitVec.ofNat 64 (T3.topNodeWord heap) := by
  by_cases h16 : heap < 16
  · interval_cases heap <;> decide
  · rw [T3.topNodeWord_ge16 (by omega) h]
    have hne : ∀ k, k < 16 → BitVec.ofNat 64 heap ≠ BitVec.ofNat 64 k := fun k hk he =>
      absurd ((ofNat_inj (by omega) (by omega)).mp he) (by omega)
    unfold remapWord
    rw [if_neg (hne 1 (by omega)), if_neg (hne 7 (by omega)), if_neg (hne 8 (by omega)), if_neg (hne 9 (by omega)),
      if_neg (hne 10 (by omega)), if_neg (hne 11 (by omega)), if_neg (hne 12 (by omega)),
      if_neg (hne 13 (by omega)), if_neg (hne 14 (by omega)), if_neg (hne 15 (by omega)), if_neg (hne 4 (by omega)),
      if_neg (hne 5 (by omega)), if_neg (hne 6 (by omega)), if_neg (hne 2 (by omega))]

def rawWord (s : MachineState) : Word := (s.getReg .x21 ||| (s.getReg .x9 <<< 32)) + s.getReg .x24

/-- C46: `cls` is the index in `clsTbl` (13 for every other word); no `split_ifs` over the long chain. -/
theorem cls_get {x : Word} {c : Nat} (hc : cls x = c) (h : c < 13) : x = clsTbl.getD c 0#64 := by
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
theorem cls_other {x : Word} (hx : x ∉ clsTbl) : 13 ≤ cls x := by
  unfold cls
  rw [List.idxOf_eq_length_iff.mpr hx]
  decide
theorem nine_raw {x : Word} {c : Nat} (hc : cls x = c) (h : 13 ≤ c) :
    x ≠ 7#64 ∧ x ≠ 8#64 ∧ x ≠ 9#64 ∧ x ≠ 10#64 ∧ x ≠ 11#64 ∧ x ≠ 12#64 ∧ x ≠ 13#64 ∧ x ≠ 14#64 ∧
      x ≠ 15#64 ∧ x ≠ 4#64 ∧ x ≠ 5#64 ∧ x ≠ 6#64 ∧ x ≠ 2#64 := by
  have hn : x ∉ clsTbl := List.idxOf_eq_length_iff.mp
    (Nat.le_antisymm List.idxOf_le_length (by unfold cls at hc; rw [hc]; exact h))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> exact hn (by decide)
theorem arith_ne {x m : Word} (h : x ≠ m) (hm : (14336#64 : Word) ≠ m) : arithmetic x ≠ m := by
  rw [arithmetic_eq]
  split_ifs
  · exact hm
  · exact h
theorem nine_facts {x : Word} {c : Nat} (hc : cls x = c) (h : 13 ≤ c) :
    arithmetic x ≠ 7#64 ∧ arithmetic x ≠ 8#64 ∧ arithmetic x ≠ 9#64 ∧ arithmetic x ≠ 10#64 ∧
      arithmetic x ≠ 11#64 ∧ arithmetic x ≠ 12#64 ∧ arithmetic x ≠ 13#64 ∧ arithmetic x ≠ 14#64 ∧
      arithmetic x ≠ 15#64 ∧ arithmetic x ≠ 4#64 ∧ arithmetic x ≠ 5#64 ∧ arithmetic x ≠ 6#64 ∧ arithmetic x ≠ 2#64 := by
  obtain ⟨h7, h8, h9, h10, h11, h12, h13, h14, h15, h4, h5, h6, h2⟩ := nine_raw hc h
  exact ⟨arith_ne h7 (by decide), arith_ne h8 (by decide), arith_ne h9 (by decide), arith_ne h10 (by decide),
    arith_ne h11 (by decide), arith_ne h12 (by decide), arith_ne h13 (by decide), arith_ne h14 (by decide),
    arith_ne h15 (by decide), arith_ne h4 (by decide), arith_ne h5 (by decide), arith_ne h6 (by decide),
    arith_ne h2 (by decide)⟩
theorem ne_true (y K m : Word) (hy : y ≠ m) (hK : m + K = 0#64) : (y + K != 0#64) = true := by
  have h : y + K ≠ 0#64 := by
    intro he
    apply hy
    have e1 : y = (y + K) - K := by rw [BitVec.add_sub_cancel]
    have e2 : m = (m + K) - K := by rw [BitVec.add_sub_cancel]
    rw [e1, e2, he, hK]
  simpa using h
theorem holds_of (s : MachineState) (T : E) (K : Word) (d : Bool)
    (hT : T.eval s = arithmetic (rawWord s)) (h : (arithmetic (rawWord s) + K != 0#64) = d) :
    Br.holds s ⟨.ne, .bin .add T (.c K), .c 0#64, d⟩ := by
  simp only [Br.holds, E.eval, BinOp.eval, CmpOp.eval, hT]
  exact h

theorem branches_hold (c : Nat) (s : MachineState) (hc : cls (rawWord s) = c) :
    ∀ b ∈ (result c).brs, b.holds s := by
  rcases c with _|_|_|_|_|_|_|_|_|_|_|_|_|c
  all_goals
    simp only [result, frozen0.res, frozen1.res, frozen2.res, frozen3.res, frozen4.res, frozen5.res, frozen6.res,
      frozen7.res, frozen8.res, frozen9.res, frozen10.res, frozen11.res, frozen12.res, frozen13.res, List.forall_mem_cons, List.forall_mem_nil, and_true]
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
    | (obtain ⟨a7, a8, a9, a10, a11, a12, a13, a14, a15, a4, a5, a6, a2⟩ := nine_facts hc (by omega)
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
        | exact ne_true _ _ _ a2 (by decide))

theorem steps {im : Image} (hl : LookOK im look) (c : Nat) (s : MachineState)
    (hpc : s.pc = pcOf 237)
    (hobl : ∀ o ∈ frozen0.res.st.obl, o.holds s)
    (hc : cls (rawWord s) = c) :
    ∃ n, n ≤ 60 ∧ Steps im s n n ((result c).toState s) := by
  have hh := pathRun_sound (known := []) (run_result c) hl s hpc
    (by intro p hp; cases hp) (by rw [obl_eq]; exact hobl) (branches_hold c s hc)
  obtain ⟨he, hle⟩ := result_count c
  exact ⟨_, hle, hh.1.of_eq rfl he.symm⟩

theorem post_pc (c : Nat) (s : MachineState) : ((result c).toState s).pc = pcOf 257 := by
  rcases c with _|_|_|_|_|_|_|_|_|_|_|_|_|c <;> rfl

theorem post_low (c : Nat) (s : MachineState) (hc : cls (rawWord s) = c) :
    ((result c).toState s).getMem 131600#64 = remapWord (rawWord s) := by
  rcases c with _|_|_|_|_|_|_|_|_|_|_|_|_|c
  all_goals first
    | (have hx := cls_val hc (by omega)
       rw [hx]
       rfl)
    | (have hx := cls_val2 hc (by omega) (by omega)
       rw [hx]
       rfl)
    | (have hx := cls_val3 hc (by omega) (by omega)
       rw [hx]
       rfl)
    | (obtain ⟨h7, h8, h9, h10, h11, h12, h13, h14, h15, h4, h5, h6, h2⟩ := nine_raw hc (by omega)
       change arithmetic (rawWord s) = _
       rw [arithmetic_eq]
       by_cases h1 : rawWord s = 1#64
       · rw [h1]
         decide
       · rw [if_neg h1]
         unfold remapWord
         rw [if_neg h1, if_neg h7, if_neg h8, if_neg h9, if_neg h10, if_neg h11, if_neg h12, if_neg h13, if_neg h14,
           if_neg h15, if_neg h4, if_neg h5, if_neg h6, if_neg h2])

theorem post_high (c : Nat) (s : MachineState) :
    ((result c).toState s).getMem 131608#64 = 0#64 := by
  rcases c with _|_|_|_|_|_|_|_|_|_|_|_|_|c <;> rfl

theorem post_left_lo (c : Nat) (s : MachineState) :
    ((result c).toState s).getMem 131584#64 = s.getMem ((s.getReg .x24 <<< 5) + s.getReg .x2) := by
  rcases c with _|_|_|_|_|_|_|_|_|_|_|_|_|c <;> rfl

theorem post_left_hi (c : Nat) (s : MachineState) :
    ((result c).toState s).getMem 131592#64 = s.getMem (((s.getReg .x24 <<< 5) + s.getReg .x2) + 8) := by
  rcases c with _|_|_|_|_|_|_|_|_|_|_|_|_|c <;> rfl

theorem post_right_lo (c : Nat) (s : MachineState) :
    ((result c).toState s).getMem 131632#64 = s.getMem (((s.getReg .x24 <<< 5) + s.getReg .x2) + 16) := by
  rcases c with _|_|_|_|_|_|_|_|_|_|_|_|_|c <;> rfl

theorem post_right_hi (c : Nat) (s : MachineState) :
    ((result c).toState s).getMem 131640#64 = s.getMem (((s.getReg .x24 <<< 5) + s.getReg .x2) + 24) := by
  rcases c with _|_|_|_|_|_|_|_|_|_|_|_|_|c <;> rfl

theorem post_half (c : Nat) (s : MachineState) :
    ((result c).toState s).getReg .x29 = s.getReg .x24 &&& 1#64 := by
  rcases c with _|_|_|_|_|_|_|_|_|_|_|_|_|c <;> rfl

theorem post_pointer (c : Nat) (s : MachineState) :
    ((result c).toState s).getReg .x30 = 131632#64 := by
  rcases c with _|_|_|_|_|_|_|_|_|_|_|_|_|c <;> rfl

theorem post_regs (c : Nat) (s : MachineState) :
    RegsExcept s ((result c).toState s) [.x3, .x6, .x7, .x28, .x29, .x30] := by
  rcases c with _|_|_|_|_|_|_|_|_|_|_|_|_|c <;> intro r hr <;> cases r <;> try (simp at hr) <;> rfl

theorem post_frame (c : Nat) (s : MachineState) :
    Frame s ((result c).toState s)
      (fun A => A = 131584 ∨ A = 131592 ∨ A = 131600 ∨ A = 131608 ∨ A = 131632 ∨ A = 131640) := by
  intro A hA hn
  change memEval s (result c).st.mem (BitVec.ofNat 64 A) = _
  rcases c with _|_|_|_|_|_|_|_|_|_|_|_|_|c
  all_goals
    simp only [result, frozen0.res, frozen1.res, frozen2.res, frozen3.res, frozen4.res, frozen5.res, frozen6.res,
      frozen7.res, frozen8.res, frozen9.res, frozen10.res, frozen11.res, frozen12.res, frozen13.res]
    t3n [memEval, Addr.eval, E.eval]
    split_ifs <;> first | omega | rfl

end SigGolfCandidate.T3M.KeygenLabel
