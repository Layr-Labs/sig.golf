import SigGolfCandidate.T3M.Sign.Basic
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.Search

section

namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
def seedHookCode : List (BitVec 32) := [985739375]
theorem codeAt_seedHookCode : CodeAt image (pcOf 1055) seedHookCode := by
  exact codeAt_sign_slice (by decide +kernel) (by decide +kernel)
def packedSeedCode : List (BitVec 32) := [67374691,19500595,1998355,68032099,45092371,63508019,20844083,1990163,17044243,34479891,31679283,1270547,295827,134711,7223331,8272931,132407,67110291,132663,67503635,115,3603,0xc49ec06f,1700627,0xbf9ec06f]
theorem codeAt_packedSeedCode : CodeAt image (pcOf 20746) packedSeedCode := by
  exact codeAt_sign_slice (by decide +kernel) (by decide +kernel)
end SigGolfCandidate.T3M.Sign
end

section


namespace ClaudeWCT.W9.Machine.Sign.PackedLeaf
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.Sign ClaudeWCT.W9.Machine.Sign.SearchM
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS)
set_option maxRecDepth 100000
theorem lookOK_of_codeAt {im : Image} {base : Nat} {code : List (BitVec 32)} (h : CodeAt im (pcOf base) code)
    (hb : 0x1000 + 4 * base < 2 ^ 64) :
    LookOK im (fun n => if base ≤ n then code[n - base]? else none) := by
  intro n w hw
  dsimp only at hw
  split at hw
  · rename_i hle
    obtain ⟨-, -, -, hpre⟩ := h
    have hp : ((pcOf base).toNat - 0x1000) / 4 = base := by simp only [pcOf, BitVec.toNat_ofNat]; omega
    rw [hp] at hpre
    obtain ⟨rest, hrest⟩ := hpre
    have hlen : n - base < code.length := (List.getElem?_eq_some_iff.mp hw).1
    have h2 : (im.code.drop base)[n - base]? = some w := by rw [← hrest, List.getElem?_append_left hlen]; exact hw
    rwa [List.getElem?_drop, show base + (n - base) = n by omega] at h2
  · cases hw
def hkLook (n : Nat) : Option (BitVec 32) := if 1055 ≤ n then Sign.seedHookCode[n - 1055]? else none
def hLook (n : Nat) : Option (BitVec 32) := if 20746 ≤ n then Sign.packedSeedCode[n - 20746]? else none
theorem and_one_ofNat (x : Nat) (hx : x < 2 ^ 64) :
    BitVec.ofNat 64 x &&& BitVec.ofNat 64 1 = BitVec.ofNat 64 (x % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, toNat_ofNat_lt hx, toNat_ofNat_lt (by norm_num), toNat_ofNat_lt (by omega),
    Nat.and_one_is_mod]
theorem hkLook_ok : LookOK Sign.image hkLook := lookOK_of_codeAt Sign.codeAt_seedHookCode (by decide)
theorem hLook_ok : LookOK Sign.image hLook := lookOK_of_codeAt Sign.codeAt_packedSeedCode (by decide)
def parE : E := .bin .and (.bin .add (.reg .x19) (.reg .x18)) (cst 1)
def pairE : E := .bin .srl (.bin .add (.bin .mul (.reg .x18) (cst 43)) (.reg .x19)) (cst 1)
def hdrE : E := .bin .or (.bin .or (.bin .sll (.reg .x8) (cst 16)) (.bin .sll pairE (cst 32))) (cst 1)
def resHk : PRes := ⟨⟨RegFile.init, [], []⟩, pcOf 20746, false, 1, 1, [], none⟩
def resTop : PRes :=
  ⟨⟨rfs [(.x6, .bin .and (.reg .x19) (cst 1))], [], []⟩, pcOf 1056, false, 3, 3, [⟨.eq, .reg .x8, cst 0, true⟩],
    none⟩
def resOdd : PRes :=
  ⟨⟨rfs [(.x28, parE)], [], []⟩, pcOf 1074, false, 5, 5, [⟨.ne, parE, cst 0, true⟩, ⟨.eq, .reg .x8, cst 0, false⟩],
    none⟩
def resEven : PRes :=
  ⟨⟨rfs [(.x6, hdrE), (.x7, .reg .x9), (.x10, cst 0x20000), (.x11, cst 64), (.x12, cst 0x20040), (.x28, cst 0x20000),
      (.x30, .bin .sll pairE (cst 32))],
    [mw 0x20018 (.reg .x9), mw 0x20010 hdrE], []⟩, pcOf 20766, true, 20, 23,
    [⟨.ne, parE, cst 0, false⟩, ⟨.eq, .reg .x8, cst 0, false⟩], none⟩
def resTail : PRes := ⟨⟨rfs [(.x28, cst 0)], [], []⟩, pcOf 1074, false, 2, 2, [], none⟩
theorem chk_helper : (optBeq (run hkLook [20746] 1055 []) resHk &&
    optBeq (run hLook [1056] 20746 [.br true]) resTop &&
    optBeq (run hLook [1074] 20746 [.br false, .br true]) resOdd &&
    optBeq (run hLook [] 20746 [.br false, .br false]) resEven &&
    optBeq (run hLook [1074] 20767 []) resTail) = true := by decide +kernel
theorem run_hk : run hkLook [20746] 1055 [] = some resHk := by
  have h := chk_helper; simp only [Bool.and_eq_true] at h; exact optBeq_eq h.1.1.1.1
theorem run_top : run hLook [1056] 20746 [.br true] = some resTop := by
  have h := chk_helper; simp only [Bool.and_eq_true] at h; exact optBeq_eq h.1.1.1.2
theorem run_odd : run hLook [1074] 20746 [.br false, .br true] = some resOdd := by
  have h := chk_helper; simp only [Bool.and_eq_true] at h; exact optBeq_eq h.1.1.2
theorem run_even : run hLook [] 20746 [.br false, .br false] = some resEven := by
  have h := chk_helper; simp only [Bool.and_eq_true] at h; exact optBeq_eq h.1.2
theorem run_tail : run hLook [1074] 20767 [] = some resTail := by
  have h := chk_helper; simp only [Bool.and_eq_true] at h; exact optBeq_eq h.2
theorem hook_spec (s : MachineState) (hpc : s.pc = pcOf 1055) :
    ∃ t, Steps Sign.image s 1 1 t ∧ t.pc = pcOf 20746 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  obtain ⟨hs, hp, -, hr, hm⟩ := piece hkLook_ok run_hk s hpc rfl (by intro b hb; cases hb) rfl
  exact ⟨_, hs, hp, fun x _ => by rw [hr x]; exact RegFile.init_get_eval s x, fun A _ _ => by rw [hm]; rfl⟩
theorem eval_par (s : MachineState) {leaf j : Nat} (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 j) (hl : leaf < 2 ^ 32) (hj : j < 2 ^ 32) :
    parE.eval s = BitVec.ofNat 64 ((j + leaf) % 2) := by
  show BinOp.eval .and (s.getReg .x19 + s.getReg .x18) (BitVec.ofNat 64 1) = _
  rw [h18, h19, ofNat_add_ofNat]
  exact and_one_ofNat _ (by omega)
theorem top_spec (s : MachineState) (hpc : s.pc = pcOf 20746) (h8 : s.getReg .x8 = BitVec.ofNat 64 0) {j : Nat}
    (h19 : s.getReg .x19 = BitVec.ofNat 64 j) (hj : j < 2 ^ 32) :
    ∃ t, Steps Sign.image s 3 3 t ∧ t.pc = pcOf 1056 ∧ t.getReg .x6 = BitVec.ofNat 64 (j % 2) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  obtain ⟨hs, hp, -, hr, hm⟩ := piece hLook_ok run_top s hpc rfl (by
    intro b hb
    simp only [resTop, List.mem_singleton] at hb
    subst hb
    simp only [Br.holds, CmpOp.eval, E.eval, cst, h8]; decide) rfl
  refine ⟨_, hs, hp, ?_, regs_rfs hr, fun A _ _ => by rw [hm]; rfl⟩
  rw [hr]; show s.getReg .x19 &&& BitVec.ofNat 64 1 = _
  rw [h19]; exact and_one_ofNat _ (by omega)
theorem odd_spec (s : MachineState) (hpc : s.pc = pcOf 20746) {lay leaf j : Nat} (hlay : lay ≠ 0)
    (hlay' : lay < 256) (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 j) (hl : leaf < 2 ^ 32) (hj : j < 2 ^ 32)
    (hodd : (j + leaf) % 2 = 1) :
    ∃ t, Steps Sign.image s 5 5 t ∧ t.pc = pcOf 1074 ∧ t.getReg .x28 = BitVec.ofNat 64 1 ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  have hp := eval_par s h18 h19 hl hj
  obtain ⟨hs, hpc', -, hr, hm⟩ := piece hLook_ok run_odd s hpc rfl (by
    intro b hb
    simp only [resOdd, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · simp only [Br.holds, CmpOp.eval, hp, hodd, cst, E.eval]; decide
    · simp only [Br.holds, CmpOp.eval, E.eval, cst, h8]
      rw [beq_eq_false_iff_ne]; intro he; exact hlay ((ofNat_inj (by omega) (by norm_num)).mp he)) rfl
  refine ⟨_, hs, hpc', ?_, regs_rfs hr, fun A _ _ => by rw [hm]; rfl⟩
  rw [hr]; show parE.eval s = _; rw [hp, hodd]
theorem hdr_or (lay pair : Nat) (hlay : lay < 256) (hp : pair < 2 ^ 32) :
    BitVec.ofNat 64 (lay * 2 ^ 16) ||| BitVec.ofNat 64 (pair * 2 ^ 32) ||| BitVec.ofNat 64 1 =
      BitVec.ofNat 64 (1 + 65536 * lay + 2 ^ 32 * pair) := by
  rw [BitVec.or_comm (BitVec.ofNat 64 (lay * 2 ^ 16)), ofNat_or_add (lay * 2 ^ 16) pair 32 (by omega),
    show pair * 2 ^ 32 + lay * 2 ^ 16 = (pair * 2 ^ 16 + lay) * 2 ^ 16 by ring, ofNat_or_add 1 _ 16 (by norm_num)]
  congr 1; ring
theorem even_spec (s : MachineState) (hpc : s.pc = pcOf 20746) {lay tree leaf j : Nat} (hlay : lay ≠ 0)
    (hlay' : lay < 256) (htree : tree < 2 ^ 32) (hl : leaf < 2 ^ 7) (hj : j < 64)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) (h9 : s.getReg .x9 = BitVec.ofNat 64 tree)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) (h19 : s.getReg .x19 = BitVec.ofNat 64 j)
    (heven : (j + leaf) % 2 = 0) :
    ∃ t, Steps Sign.image s 20 23 t ∧ fetch Sign.image t = some (.base .ECALL) ∧ t.pc = pcOf 20766 ∧
      t.getReg .x10 = BitVec.ofNat 64 PRIV ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 SEEDS ∧
      t.getMem (BitVec.ofNat 64 (PRIV + 16)) = BitVec.ofNat 64 (hdr0 0 lay tree ((43 * leaf + j) / 2)) ∧
      t.getMem (BitVec.ofNat 64 (PRIV + 24)) = BitVec.ofNat 64 (hdr1 tree 0) ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x28, .x30] ∧
      Frame s t (fun A => A = PRIV + 24 ∨ A = PRIV + 16) := by
  have hp := eval_par s h18 h19 (by omega) (by omega)
  obtain ⟨hs, hpc', he, hr, hm⟩ := piece hLook_ok run_even s hpc rfl (by
    intro b hb
    simp only [resEven, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · simp only [Br.holds, CmpOp.eval, hp, heven, cst, E.eval]; decide
    · simp only [Br.holds, CmpOp.eval, E.eval, cst, h8]
      rw [beq_eq_false_iff_ne]; intro he; exact hlay ((ofNat_inj (by omega) (by norm_num)).mp he)) rfl
  have hpair : pairE.eval s = BitVec.ofNat 64 ((43 * leaf + j) / 2) := by
    show BinOp.eval .srl (BinOp.eval .add (BinOp.eval .mul (s.getReg .x18) (BitVec.ofNat 64 43)) (s.getReg .x19))
      (BitVec.ofNat 64 1) = _
    rw [h18, h19, srl_eval _ 1 (by norm_num)]
    simp only [BinOp.eval]
    rw [BitVec.ofNat_mul_ofNat, ofNat_add_ofNat, ofNat_shr _ _ (by omega), pow_one, Nat.mul_comm leaf 43]
  have hhdr : hdrE.eval s = BitVec.ofNat 64 (hdr0 0 lay tree ((43 * leaf + j) / 2)) := by
    show BinOp.eval .or (BinOp.eval .or (BinOp.eval .sll (s.getReg .x8) (BitVec.ofNat 64 16))
      (BinOp.eval .sll (pairE.eval s) (BitVec.ofNat 64 32))) (BitVec.ofNat 64 1) = _
    rw [h8, hpair, sll_eval _ 16 (by norm_num), sll_eval _ 32 (by norm_num), ofNat_shl, ofNat_shl]
    simp only [BinOp.eval]
    rw [hdr_or lay _ hlay' (by omega), hdr0_eq 0 lay tree _ (by norm_num) hlay' htree (by omega)]
  refine ⟨_, hs, he rfl, hpc', by rw [hr]; rfl, by rw [hr]; rfl, by rw [hr]; rfl, ?_, ?_, regs_rfs hr, ?_⟩
  · rw [hm]; simp only [resEven, mw]
    rw [memEval_cons_ofNat _ _ _ _ _ (by decide) (by decide), if_neg (by decide),
      memEval_cons_ofNat _ _ _ _ _ (by decide) (by decide), if_pos rfl, hhdr]
  · rw [hm]; simp only [resEven, mw]
    rw [memEval_cons_ofNat _ _ _ _ _ (by decide) (by decide), if_pos rfl, hdr1_eq tree 0 htree (by norm_num)]
    show s.getReg .x9 = _; rw [h9]; congr 1
  · intro A hA hn
    simp only [not_or] at hn
    rw [hm]; simp only [resEven, mw]
    rw [memEval_cons_ofNat _ _ _ _ _ hA (by decide), if_neg hn.1, memEval_cons_ofNat _ _ _ _ _ hA (by decide),
      if_neg hn.2]; rfl
theorem tail_spec (s : MachineState) (hpc : s.pc = pcOf 20767) :
    ∃ t, Steps Sign.image s 2 2 t ∧ t.pc = pcOf 1074 ∧ t.getReg .x28 = BitVec.ofNat 64 0 ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  obtain ⟨hs, hpc', -, hr, hm⟩ := piece hLook_ok run_tail s hpc rfl (by intro b hb; cases hb) rfl
  exact ⟨_, hs, hpc', by rw [hr]; rfl, regs_rfs hr, fun A _ _ => by rw [hm]; rfl⟩
end ClaudeWCT.W9.Machine.Sign.PackedLeaf
end
