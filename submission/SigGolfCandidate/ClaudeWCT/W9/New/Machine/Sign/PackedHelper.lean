import SigGolfCandidate.T3M.Sign.Basic
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.Search

section

namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
def seedHookCode : List (BitVec 32) := [985739375]
theorem codeAt_seedHookCode : CodeAt image (pcOf 1055) seedHookCode := by
  exact codeAt_sign_slice (by decide +kernel) (by decide +kernel)
def packedSeedCode : List (BitVec 32) := [67374691,623715,0xb91f706f,335543,0x800e8e93,619411,233059,134711,84817155,93205891,11448355,12497955,17731219,8389395,40436531,7537459,1266451,33755923,17044755,10707763,1270547,0xf69f606f,19,0xbd0ed06f,0xbf9ec06f]
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
def resHk : PRes := ⟨⟨RegFile.init, [], []⟩, pcOf 20746, false, 1, 1, [], none⟩
/-- Campaign T8D: the top branch `20746 beq s0` lands on `20769 j TOPSEED (1557)`. -/
def resTop : PRes :=
  ⟨⟨RegFile.init, [], []⟩, pcOf 1557, false, 2, 2, [⟨.eq, .reg .x8, cst 0, true⟩], none⟩
theorem chk_helper : (optBeq (run hkLook [20746] 1055 []) resHk &&
    optBeq (run hLook [1557] 20746 [.br true]) resTop) = true := by decide +kernel
theorem run_hk : run hkLook [20746] 1055 [] = some resHk := by
  have h := chk_helper; simp only [Bool.and_eq_true] at h; exact optBeq_eq h.1
theorem run_top : run hLook [1557] 20746 [.br true] = some resTop := by
  have h := chk_helper; simp only [Bool.and_eq_true] at h; exact optBeq_eq h.2
theorem hook_spec (s : MachineState) (hpc : s.pc = pcOf 1055) :
    ∃ t, Steps Sign.image s 1 1 t ∧ t.pc = pcOf 20746 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  obtain ⟨hs, hp, -, hr, hm⟩ := piece hkLook_ok run_hk s hpc rfl (by intro b hb; cases hb) rfl
  exact ⟨_, hs, hp, fun x _ => by rw [hr x]; exact RegFile.init_get_eval s x, fun A _ _ => by rw [hm]; rfl⟩
theorem top_spec (s : MachineState) (hpc : s.pc = pcOf 20746) (h8 : s.getReg .x8 = BitVec.ofNat 64 0) :
    ∃ t, Steps Sign.image s 2 2 t ∧ t.pc = pcOf 1557 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  obtain ⟨hs, hp, -, hr, hm⟩ := piece hLook_ok run_top s hpc rfl (by
    intro b hb
    simp only [resTop, List.mem_singleton] at hb
    subst hb
    simp only [Br.holds, CmpOp.eval, E.eval, cst, h8]; decide) rfl
  exact ⟨_, hs, hp, fun x _ => by rw [hr x]; exact RegFile.init_get_eval s x, fun A _ _ => by rw [hm]; rfl⟩
theorem hdr_or (lay pair : Nat) (hlay : lay < 256) (hp : pair < 2 ^ 32) :
    BitVec.ofNat 64 (lay * 2 ^ 16) ||| BitVec.ofNat 64 (pair * 2 ^ 32) ||| BitVec.ofNat 64 1 =
      BitVec.ofNat 64 (1 + 65536 * lay + 2 ^ 32 * pair) := by
  rw [BitVec.or_comm (BitVec.ofNat 64 (lay * 2 ^ 16)), ofNat_or_add (lay * 2 ^ 16) pair 32 (by omega),
    show pair * 2 ^ 32 + lay * 2 ^ 16 = (pair * 2 ^ 16 + lay) * 2 ^ 16 by ring, ofNat_or_add 1 _ 16 (by norm_num)]
  congr 1; ring
end ClaudeWCT.W9.Machine.Sign.PackedLeaf
end
