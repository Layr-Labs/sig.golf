import SigGolfCandidate.ExpandLabel
import SigGolfCandidate.Merge011
import SigGolfCandidate.Merge045
import SigGolfCandidate.Merge051
import SigGolfCandidate.Merge052
import SigGolfCandidate.Merge058
import SigGolfCandidate.Merge059
import SigGolfCandidate.Merge060
import SigGolfCandidate.Merge070
import SigGolfCandidate.Merge075
import SigGolfCandidate.Merge076.P1

set_option debug.skipKernelTC false
set_option linter.all false

-- ==== merged from T3M_Expand_LayerBlocks ====
section

section
namespace SigGolfCandidate.T3M.Expand.BCBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
end SigGolfCandidate.T3M.Expand.BCBlocks
end
section
namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC)
theorem ex_slt (a b : Nat) (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    BitVec.slt (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a < b) := ofNat_slt a b ha hb
section blocks
variable (s : MachineState)
theorem ex_valid (x : Nat) (h1 : x % 8 = 0) (h2 : x + 8 ≤ 2 ^ 24) : accessValid (BitVec.ofNat 64 x) 8 = true := by
  rw [accessValid_iff, toNat_ofNat_lt (by omega)]; simp only [MEMORY_BYTES]; omega
end blocks
end SigGolfCandidate.T3M.Expand
end

namespace SigGolfCandidate.T3M.Expand.SharedRecover.BCBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Expand.BCBlocks
variable {im : Image}          
end SigGolfCandidate.T3M.Expand.SharedRecover.BCBlocks

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Expand
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC)
/-! img-v6 top-node nonce routine (words 43195 .. 43249, hooked at 1139 `jal 43195`; topfold-v6, NOTES V49). -/
def nonce_D : List (BitVec 32) := [0x800e13,0x80006f]
variable {im : Image}          
variable                    [PackedBlocks.Code im]
variable (s : MachineState)
theorem pe_and1 (x : Nat) : BitVec.ofNat 64 x &&& 1#64 = BitVec.ofNat 64 (x % 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (1 : Nat) % 2 ^ 64 = 1 by norm_num, Nat.and_one_is_mod]
  omega

end SigGolfCandidate.T3M.Expand.SharedRecover

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Expand
variable {im : Image}           (s : MachineState)
end SigGolfCandidate.T3M.Expand.SharedRecover

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace Grind
open SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Search (NODE NOUT)
open SigGolfCandidate.T3 (Digest nonceBytes pad64 zero16)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.WCT9 (lowerZeroBits lowerNonceCap lowerZeroOk lowerNodeInputN lowerNodeHashN lowerNonceSearch
  lowerNodeAt)
theorem tb_pure_steps {α : Type} {image : Image} {sk : BitVec 256} {s t : MachineState} {k c : Nat} {a : α}
    {Q : α → MachineState → Prop} (h : Steps image s k c t) (hQ : Q a t) : TBSim image sk s c (Pure.pure a) Q :=
  Sim.pure_steps h hQ
/-- L-hyper A: the layer the decode trampolines compute from a node word (normal form of the symbolic run). -/
def decW (w : Word) : Word :=
  (if (0#64).ult (w >>> 35) = true then 1#64 else 0#64) + (if (0#64).ult (w >>> 41) = true then 1#64 else 0#64) +
    w >>> 47
section blocks
variable {im : Image}           (s : MachineState)

/-- `SAVE` (the stub's register save area `[1000, 1040)`). -/
def SaveW (A : Nat) : Prop := 1000 ≤ A ∧ A < 1040

end blocks

/-! U16b grind stub: tweak-word arithmetic. -/

/-- The record table base of lower layer `lay` (`0x700000 + 32 (lay - 1)`). -/
def recB (lay : Nat) : Nat := 0x700000 + 32 * (lay - 1)
/-- Fold-0 parent heaps start at `2 ^ (height - 1)`: 64 on layer 1, 32 on layers 2, 3. -/
def recThr (lay : Nat) : Nat := if lay = 1 then 64 else 32
/-- The nonce slot of class `heap` (2..3 -> +0, 4..7 -> +8, 8..15 -> +16; E11: 16..31 -> +0x100). -/
def recA (lay heap : Nat) : Nat := recB lay + (if heap < 4 then 0 else if heap < 8 then 8 else if heap < 16 then 16 else 256)

section cls
variable {im : Image}          

end cls

/-! U16b grind stub: loop setup and the zero test. -/

/-- The used half's top byte (`t5`): `NOUT + 31` for even heaps (high half), `NOUT + 15` for odd ones. -/
def topByteA (heap : Nat) : Nat := NOUT + 15 + 16 * (1 - heap % 2)

section setup
variable {im : Image}          

end setup

/-! U16b grind stub: node input, zero test, trial invariant. -/

section sim
variable {im : Image} {sk : BitVec 256}
end sim

/-- What follows the trial-`n` hash in `lowerNonceSearch` (fuel = trials left). -/
def gTail (lay tree heap : Nat) (l r : Digest) : Nat → Nat → Digest → SigGolfCandidate.T3.M (Nat × Digest)
  | 0, n, v => pure (n, v)
  | fuel + 1, n, v => if lowerZeroOk lay heap v then pure (n, v) else lowerNonceSearch lay tree heap l r fuel (n + 1)
theorem search_eq (lay tree heap : Nat) (l r : Digest) (fuel n : Nat) :
    lowerNonceSearch lay tree heap l r fuel n =
      ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.lowerHigh lay heap) (lowerNodeInputN lay tree heap n l r) >>=
        gTail lay tree heap l r fuel n := by
  cases fuel <;> rfl

/-- Back at 1139 after a lower node: value kept, nonce and fold-0 heap recorded, pad and `SAVE` cleared. -/
structure StubOut (t : MachineState) (lay heap : Nat) (res : Nat × Digest) (w : MachineState) : Prop where
  pc : w.pc = pcOf 1139
  regs : RegsExcept t w []
  out : DigAt w (NOUT + if ClaudeWCT.WCT9.lowerHigh lay heap then 16 else 0) res.2
  pad : w.getMem (BitVec.ofNat 64 (NODE + 32)) = 0
  save : ∀ k, k < 5 → w.getMem (BitVec.ofNat 64 (1000 + 8 * k)) = 0
  nonce : lowerZeroBits lay heap ≠ 0 → w.getMem (BitVec.ofNat 64 (recA lay heap)) = BitVec.ofNat 64 res.1
  hrec : recThr lay ≤ heap → w.getMem (BitVec.ofNat 64 (recB lay + 24)) = BitVec.ofNat 64 heap
  frame : Frame t w (fun A => (NOUT ≤ A ∧ A < NOUT + 32) ∨ SaveW A ∨ (lowerZeroBits lay heap ≠ 0 ∧ A = recA lay heap) ∨
    (recThr lay ≤ heap ∧ A = recB lay + 24))

/-- At 54847 after the trial-`n` hash (answer `a`). -/
structure GTrial (t : MachineState) (lay heap n : Nat) (a : BitVec 256) (u : MachineState) : Prop where
  pc : u.pc = pcOf 54847
  regs : RegsExcept t u [.x7, .x28, .x29, .x30, .x31]
  x29 : u.getReg .x29 = BitVec.ofNat 64 (8 - lowerZeroBits lay heap)
  x30 : u.getReg .x30 = BitVec.ofNat 64 (topByteA heap)
  x31 : u.getReg .x31 = BitVec.ofNat 64 (lowerNonceCap lay heap)
  pad : u.getMem (BitVec.ofNat 64 (NODE + 32)) = BitVec.ofNat 64 n
  s0 : u.getMem (BitVec.ofNat 64 1000) = t.getReg .x7
  s1 : u.getMem (BitVec.ofNat 64 1008) = t.getReg .x28
  s2 : u.getMem (BitVec.ofNat 64 1016) = t.getReg .x29
  s3 : u.getMem (BitVec.ofNat 64 1024) = t.getReg .x30
  s4 : u.getMem (BitVec.ofNat 64 1032) = t.getReg .x31
  frame : Frame t u (fun A => A = NODE + 32 ∨ (NOUT ≤ A ∧ A < NOUT + 32) ∨ SaveW A)
  out : DigAt u (NOUT + if ClaudeWCT.WCT9.lowerHigh lay heap then 16 else 0)
    (ClaudeWCT.WCT9.halfOf (ClaudeWCT.WCT9.lowerHigh lay heap) a)

theorem recA_cases (lay heap : Nat) (h1 : 1 ≤ lay) (h3 : lay ≤ 3) :
    recA lay heap % 8 = 0 ∧ 0x700000 ≤ recA lay heap ∧ recA lay heap < 0x700160 ∧ recA lay heap ≠ recB lay + 24 := by
  unfold recA recB; split_ifs <;> omega

section found
variable {im : Image}          

end found

/-! U16b grind stub: the search loop and the whole stub (word 1138 -> 1139). -/

theorem high_eq (lay heap : Nat) (h3 : lay ≤ 3) :
    (NOUT + if ClaudeWCT.WCT9.lowerHigh lay heap then 16 else 0) + 15 = topByteA heap := by
  unfold ClaudeWCT.WCT9.lowerHigh topByteA
  rcases Nat.mod_two_eq_zero_or_one heap with h | h <;> simp [h, show lay < 4 by omega]

section loop
variable {im : Image}           (sk : BitVec 256)

end loop

/-! U16b grind stub: the pass-through of a non-lower node (top tree). -/

/-- Back at 1139 after a pass-through: the hash answer `a` written, registers restored, `SAVE` cleared. -/
structure PassOut (t : MachineState) (a : BitVec 256) (w : MachineState) : Prop where
  pc : w.pc = pcOf 1139
  regs : RegsExcept t w []
  mem : ∀ A, A < 2 ^ 64 → ¬ SaveW A → w.getMem (BitVec.ofNat 64 A) = (writeHash t a).getMem (BitVec.ofNat 64 A)
  save : ∀ k, k < 5 → w.getMem (BitVec.ofNat 64 (1000 + 8 * k)) = 0

section pass
variable {im : Image}           {sk : BitVec 256}

end pass

end Grind


end SigGolfCandidate.T3M.Expand.SharedRecover
end
-- ==== merged from T3M_Expand_Basic ====
section

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
theorem finRange_map_val (n : Nat) : (List.finRange n).map Fin.val = List.range' 0 n := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp
section tb
variable {image : Image} {sk : BitVec 256}
theorem tb_mapM_idx {γ δ : Type} (f : γ → T3.M δ) (idx : γ → Nat) (W : Nat) (Inv : List δ → MachineState → Prop) :
    ∀ (xs : List γ) (pre : List δ) {s : MachineState}, xs.map idx = List.range' pre.length xs.length →
    (∀ x ∈ xs, ∀ (pre' : List δ) t, pre'.length = idx x → Inv pre' t →
      TBSim image sk t W (f x) (fun d u => Inv (pre' ++ [d]) u)) →
    Inv pre s → TBSim image sk s (xs.length * W) (xs.mapM f) (fun ds u => ds.length = xs.length ∧ Inv (pre ++ ds) u)
  | [], pre, s, _, _, h0 => by
    simpa using TBSim.pure (image := image) (sk := sk) (Q := fun ds u => ds.length = 0 ∧ Inv (pre ++ ds) u)
      (a := []) (by simpa using h0)
  | x :: xs, pre, s, hidx, hb, h0 => by
    rw [List.mapM_cons]
    simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at hidx
    have h1 := hb x (by simp) pre s hidx.1.symm h0
    have key : ∀ d t, Inv (pre ++ [d]) t → TBSim image sk t (xs.length * W)
        (do let ds ← xs.mapM f; Pure.pure (d :: ds)) (fun ds u => ds.length = xs.length + 1 ∧ Inv (pre ++ ds) u) := by
      intro d t ht
      have h2 := tb_mapM_idx f idx W Inv xs (pre ++ [d]) (by simpa using hidx.2) (fun y hy => hb y (by simp [hy])) ht
      exact (TBSim.bind (W₂ := 0) h2 (f := fun ds => Pure.pure (d :: ds))
        (fun ds u hu => TBSim.pure ⟨by simp [hu.1], by simpa using hu.2⟩)).mono (by omega) (fun _ _ h => h)
    exact (TBSim.bind h1 key).mono (by rw [List.length_cons, Nat.succ_mul]; omega) (fun _ _ h => h)
theorem tb_foldlM_finRange {γ : Type} (n : Nat) (f : γ → Fin n → T3.M γ) (init : γ) (W : Nat)
    (Inv : Nat → γ → MachineState → Prop)
    (hbody : ∀ (i : Fin n) acc t, Inv i.val acc t → TBSim image sk t W (f acc i) (Inv (i.val + 1)))
    {s : MachineState} (h0 : Inv 0 init s) :
    TBSim image sk s (n * W) ((List.finRange n).foldlM f init) (Inv n) := by
  have gen : ∀ (xs : List (Fin n)) (k : Nat) (acc : γ) (t : MachineState), xs.map Fin.val = List.range' k xs.length →
      Inv k acc t → TBSim image sk t (xs.length * W) (xs.foldlM f acc) (Inv (k + xs.length)) := by
    intro xs
    induction xs with
    | nil => intro k acc t _ ht; simpa using TBSim.pure (image := image) (sk := sk) ht
    | cons x xs ih =>
      intro k acc t hidx ht
      simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at hidx
      rw [List.foldlM_cons]
      have h1 := hbody x acc t (by rw [hidx.1]; exact ht)
      rw [hidx.1] at h1
      refine (TBSim.bind (W₂ := xs.length * W) h1 (fun acc' t' ht' => ?_)).mono
        (by rw [List.length_cons, Nat.succ_mul]; omega) (fun _ _ h => by
        simpa [Nat.add_assoc, Nat.add_comm 1] using h)
      have := ih (k + 1) acc' t' (by simpa using hidx.2) ht'
      rwa [show k + 1 + xs.length = k + (xs.length + 1) by omega] at this
  have := gen (List.finRange n) 0 init s (by rw [finRange_map_val]; simp) h0
  simpa using this
end tb
end SigGolfCandidate.T3M.Expand
end
-- ==== merged from T3M_Expand_LayerChain ====
section

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest chain chainInput shortHash pad64 zero16 header)
open SphincsSecurity (bytesLE bytesLE_length)
open SigGolfCandidate.T3M.Search (DIGITS)
set_option autoImplicit false
def stepRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x20, .x28, .x30]
theorem not_mem_of_sub {r : Reg} {l l' : List Reg} (hl : ∀ x ∈ l, x ∈ l') (hr : r ∉ l') : r ∉ l :=
  fun hm => hr (hl r hm)
section chain
variable {sk : BitVec 256}
end chain
end SigGolfCandidate.T3M.Expand

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3
open SigGolfCandidate.T3M.Expand
open SphincsSecurity (bytesLE bytesLE_length)
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC)
open ClaudeWCT
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable {im : Image}                              [PackedBlocks.Code im] {sk : BitVec 256}
end SigGolfCandidate.T3M.Expand.SharedRecover
end
-- ==== merged from T3M_Expand_LayersBlocks ====
section

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Layer route height chainCount target)
open SigGolfCandidate.T3M.Search (ENC csN4 ofNat_and_mask)
set_option autoImplicit false
set_option maxRecDepth 8192
section blocks
variable (s : MachineState)
-- [h2 lane] removed c342_spec: a fact about the record's original expand word 0 / 342, which H2 replaces
end blocks
def lK (lay : Layer) : Nat := ![14, 13, 13, 13] lay
def lk (lay : Layer) : Nat := ![0, 0, 0, 0] lay
end SigGolfCandidate.T3M.Expand

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Layer route height chainCount target)
open SigGolfCandidate.T3M.Search (ENC csN4 ofNat_and_mask)
open SigGolfCandidate.T3M.Expand
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable {im : Image}               
section
variable (s : MachineState)
end
end SigGolfCandidate.T3M.Expand.SharedRecover

namespace SigGolfCandidate.T3M.Expand.SharedRecover
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
end SigGolfCandidate.T3M.Expand.SharedRecover

/-! ## T51 KCOPY (54522..54531, from 331 `jal ra, 54522`): copy the 1,896-byte shared kernel table window
`0xFF9E00 .. 0xFFA568` (237 doublewords; the 1,892-byte block + 4 bytes) to RAM `0xA0000`, then `j 457`. -/
namespace SigGolfCandidate.T3M.Expand.KCopy
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def headWords : List (BitVec 32) := [0x000a0eb7,0x00ffae37,0xe00e0e13,0x768e0f13]
def loopWords : List (BitVec 32) := [0xe3303,0x6eb023,0x8e0e13,0x8e8e93,0xffee68e3]
def tailWords : List (BitVec 32) := [0xb18cb06f]

sym_block loopRun := symRun { noAlias := true } loopWords (pcOf 54526) 50
sym_block headRun := symRun { noAlias := true } headWords (pcOf 54522) 10
sym_block tailRun := symRun { noAlias := true } tailWords (pcOf 54531) 10

theorem loop_regs (s : MachineState) :
    RegsExcept s (loopRun.res.toState s) [.x6,.x28,.x29] := by
  intro r hr; simp at hr; cases r <;> simp_all [loopRun.res, rv_simp] <;> rfl

theorem head_spec {im : Image} (hc : CodeAt im (pcOf 54522) headWords) (s : MachineState) (hpc : s.pc = pcOf 54522) :
    ∃ t, Steps im s 4 4 t ∧ t.pc = pcOf 54526 ∧ t.getReg .x28 = BitVec.ofNat 64 0xFF9E00 ∧
      t.getReg .x29 = BitVec.ofNat 64 0xA0000 ∧ t.getReg .x30 = BitVec.ofNat 64 0xFFA568 ∧
      RegsExcept s t [.x28,.x29,.x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound headRun hc s hpc (by simp [headRun.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [headRun.res, rv_simp]
  · simp [headRun.res, rv_simp]
  · simp [headRun.res, rv_simp]
  · intro r hr; cases r <;> first | rfl | exact (hr (by decide)).elim
  · intro A _ _; simp [headRun.res, rv_simp]

theorem tail_spec {im : Image} (hc : CodeAt im (pcOf 54531) tailWords) (s : MachineState) (hpc : s.pc = pcOf 54531) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 457 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound tailRun hc s hpc (by simp [tailRun.res, rv_simp]), ?_, ?_, ?_⟩
  · rfl
  · intro r hr; cases r <;> rfl
  · intro A _ _; simp [tailRun.res, rv_simp]

/-- KCOPY's code (a class, so the layer-recovery sections can take it as an instance like `EntryCode`). -/
class Code (im : Image) : Prop where
  head : CodeAt im (pcOf 54522) headWords
  loop : CodeAt im (pcOf 54526) loopWords
  tail : CodeAt im (pcOf 54531) tailWords

end SigGolfCandidate.T3M.Expand.KCopy
end
-- ==== merged from T3M_Search_DigestSearch ====
section

section
namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
section blocks
variable {image : Image} {b : Nat}
theorem so7_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 7)) (c : Nat)
    (hc : c ≤ 7) (h20 : s.getReg .x20 = BitVec.ofNat 64 c) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if c < 7 then pcOf (b + 9) else pcOf (b + 97)) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_7 hK.2.1) (codeAt_k_7 hK) s hpc (by simp [st_7, blk354_7.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_7, rebase, blk354_7.res, E.eval, CmpOp.eval, h20]
    rw [ofNat_slt c 7 (by omega) (by omega)]
    by_cases h : c < 7 <;> simp [h]
  · intro r hr; simp at hr; cases r <;> simp_all [st_7, blk354_7.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_7, blk354_7.res, rv_simp]
theorem so31_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 31))
    (u : Nat) (hu : u < 2 ^ 25) (h28 : s.getReg .x28 = BitVec.ofNat 64 u) :
    ∃ t, Steps image s 9 9 t ∧
      t.pc = (if u / 16 % 128 ≤ u / 2 ^ 11 % 128 then pcOf (b + 43) else pcOf (b + 40)) ∧
      t.getReg .x6 = BitVec.ofNat 64 (u % 16 * 128) ∧
      t.getReg .x22 = BitVec.ofNat 64 (u / 16 % 128) ∧
      t.getReg .x23 = BitVec.ofNat 64 (u / 2 ^ 11 % 128) ∧
      t.getReg .x24 = BitVec.ofNat 64 (u / 2 ^ 18 % 128) ∧
      RegsExcept s t [.x6, .x22, .x23, .x24] ∧ Frame s t (fun _ => False) := by
  have hu' : u < 2 ^ 64 := by omega
  refine ⟨_, symRun_sound (run_31 hK.2.1) (codeAt_k_31 hK) s hpc (by simp [st_31, blk354_31.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_31, rebase, blk354_31.res, E.eval, CmpOp.eval, h28, BinOp.eval,
      ofNat_shr _ _ hu', ofNat_and127]
    rw [ofNat_slt _ _ (by omega) (by omega)]
    by_cases h : u / 16 % 128 ≤ u / 2 ^ 11 % 128 <;> simp [h]
  · simp only [Result.toState_getReg, st_31, blk354_31.res]
    t3n [h28, ofNat_shr _ _ hu', ofNat_and15, ofNat_and127]
  · simp only [Result.toState_getReg, st_31, blk354_31.res]
    t3n [h28, ofNat_shr _ _ hu', ofNat_and15, ofNat_and127]
  · simp only [Result.toState_getReg, st_31, blk354_31.res]
    t3n [h28, ofNat_shr _ _ hu', ofNat_and15, ofNat_and127]
  · simp only [Result.toState_getReg, st_31, blk354_31.res]
    t3n [h28, ofNat_shr _ _ hu', ofNat_and15, ofNat_and127]
  · intro r hr; simp at hr; cases r <;> simp_all [st_31, blk354_31.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_31, blk354_31.res, rv_simp]
theorem so43_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 43)) (x y : Nat)
    (hx : x < 2 ^ 63) (hy : y < 2 ^ 63) (hhi : s.getReg .x24 = BitVec.ofNat 64 x)
    (hlo : s.getReg .x23 = BitVec.ofNat 64 y) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if y ≤ x then pcOf (b + 47) else pcOf (b + 44)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_43 hK.2.1) (codeAt_k_43 hK) s hpc (by simp [st_43, blk354_43.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_43, rebase, blk354_43.res, E.eval, CmpOp.eval, hhi, hlo]
    rw [ofNat_slt _ _ hx hy]
    by_cases h : y ≤ x
    · simp [h, show ¬ x < y by omega]
    · simp [h, show x < y by omega]
  · intro r hr; simp at hr; cases r <;> simp_all [st_43, blk354_43.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_43, blk354_43.res, rv_simp]
theorem so44_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 44)) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf (b + 47) ∧ t.getReg .x23 = s.getReg .x24 ∧
      t.getReg .x24 = s.getReg .x23 ∧ RegsExcept s t [.x7, .x23, .x24] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_44 hK.2.1) (codeAt_k_44 hK) s hpc (by simp [st_44, blk354_44.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_44, blk354_44.res, E.eval]
  · simp [st_44, blk354_44.res, rv_simp]
  · simp [st_44, blk354_44.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_44, blk354_44.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_44, blk354_44.res, rv_simp]
theorem so97_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 97)) (S : Nat)
    (hS : S < 2 ^ 63) (h21 : s.getReg .x21 = BitVec.ofNat 64 S) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if 116 ≤ S then pcOf (b + 101) else pcOf (b + 99)) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_97 hK.2.1) (codeAt_k_97 hK) s hpc (by simp [st_97, blk354_97.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_97, rebase, blk354_97.res, E.eval, CmpOp.eval, h21]
    rw [ofNat_slt _ _ hS (by omega)]
    by_cases h : 116 ≤ S
    · simp [h, show ¬ S < 116 by omega]
    · simp [h, show S < 116 by omega]
  · intro r hr; simp at hr; cases r <;> simp_all [st_97, blk354_97.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_97, blk354_97.res, rv_simp]
end blocks
section sort
variable {image : Image} {b : Nat}
end sort
def RowAt (t : MachineState) (N : BitVec 256) (c : Nat) : Prop :=
  ∀ j < 3, t.getMem (BitVec.ofNat 64 (SEL + 24 * c + 8 * j)) =
    BitVec.ofNat 64 (selBucket N c * 128 + (selRow N c).getD j 0)
abbrev selRegs : List Reg := [.x6, .x7, .x13, .x20, .x21, .x22, .x23, .x24, .x25, .x28, .x29]
section loop
variable {image : Image} {b : Nat}
theorem regs_mono {s t : MachineState} {l : List Reg} (h : RegsExcept s t l)
    (hl : l.all (fun r => decide (r ∈ selRegs)) = true) : RegsExcept s t selRegs :=
  h.mono (fun r hr => by simpa using List.all_eq_true.1 hl r hr)
end loop
end SigGolfCandidate.T3M.Search
end
section
namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option linter.unusedSimpArgs false
theorem gate_word (N : BitVec 256) :
    N.extractLsb' 192 64 >>> 14 &&& 7#64 = BitVec.ofNat 64 (N.toNat / 2 ^ 206 % 8) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_ofNat, show (7 : Nat) = 2 ^ 3 - 1 from rfl,
    show (8 : Nat) = 2 ^ 3 from rfl, Nat.testBit_two_pow_sub_one,
    Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases h : i < 3
  · simp [h, hi, show 14 + i < 64 by omega, BitVec.testBit_toNat,
      show 192 + (14 + i) = i + 206 by omega]
  · simp [h]
end SigGolfCandidate.T3M.Search
end
section
namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer HashOutput)
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
theorem digestInput_length (rho : Digest) (m : T3.Message) (c : BitVec 32) : (T3.digestInput rho m c).length = 64 := by
  simp only [T3.digestInput, List.length_append, SphincsSecurity.bytesLE_length]
theorem pad64_digestInput (rho : Digest) (m : T3.Message) (c : BitVec 32) :
    T3.pad64 (T3.digestInput rho m c) = T3.digestInput rho m c := by
  unfold T3.pad64
  rw [digestInput_length]
  simp
theorem TBSim.publicHash_bind {β : Type} {image : Image} {sk : BitVec 256} {s : MachineState}
    {input : List UInt8} {W : Nat} {f : HashOutput → T3.M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (T3.pad64 input))
    (h : ∀ a, TBSim image sk (writeHash s a) W (f a) Q) :
    TBSim image sk s (8 * (toQ (T3.pad64 input)).blocks + W) (T3.publicHash input >>= f) Q := by
  unfold TBSim; rw [mrealize_bind, mrealize_publicHash]
  exact Sim.query_bind hf ht0 hv hq h
section blocks
variable {image : Image} {d b : Nat}
theorem ds0_spec (hD : DsAt image d b) (s : MachineState) (hpc : s.pc = pcOf (d + 0)) (i : Nat)
    (hi : i ≤ 2 ^ 20) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if i = 2 ^ 20 then pcOf (b + 0) else pcOf (d + 2)) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_ds0 hD.2) (codeAt_ds_0 hD) s hpc (by simp [stds_0, blkds30_0.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcEds_0, rebase, blkds30_0.res, E.eval, CmpOp.eval, h19]
    by_cases h : i = 2 ^ 20
    · subst h; simp
    · have : (BitVec.ofNat 64 i == 1048576#64) = false := by
        rw [beq_eq_false_iff_ne, ne_eq, ofNat_eq_iff]; omega
      rw [this, if_neg (by simp), if_neg h]
  · intro r hr; simp at hr; cases r <;> simp_all [stds_0, blkds30_0.res, rv_simp] <;> rfl
  · intro A _ _; simp [stds_0, blkds30_0.res, rv_simp]
theorem ds16_spec (hD : DsAt image d b) (s : MachineState) (hpc : s.pc = pcOf (d + 16)) (ok : Bool)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 (if ok then 1 else 0)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if ok then pcOf (d + 19) else pcOf (d + 17)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_ds16 hD.2) (codeAt_ds_16 hD) s hpc
    (by simp [stds_16, blkds30_16.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcEds_16, rebase, blkds30_16.res, E.eval, CmpOp.eval, h13]
    cases ok <;> simp
  · intro r hr; simp at hr; cases r <;> simp_all [stds_16, blkds30_16.res, rv_simp] <;> rfl
  · intro A _ _; simp [stds_16, blkds30_16.res, rv_simp]
end blocks
def dsCostS : Nat := T3.attemptLimit * 700 + 100
section loop
variable {image : Image} {d b : Nat} {sk : BitVec 256}
end loop
end SigGolfCandidate.T3M.Search
end
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_Defs ====
section

namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M)
open SigGolfCandidate.T3M.Search (DIG NBUF ENC FailedAt KernAt)
-- (open dropped: nothing it names is in this part)
end ClaudeWCT.W9.Machine.Expand
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_ExpSearch ====
section

section
namespace ClaudeWCT.W9.Machine.Expand.ESearch
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3M.Search (DIG NBUF)
-- (open dropped: nothing it names is in this part)
open ClaudeWCT.W9.Machine.Sign (run)
open ClaudeWCT.W9.Machine.Sign.SearchM (cst rfs mw ctrE grpE fieldE fieldLen idxE)
set_option maxRecDepth 100000
end ClaudeWCT.W9.Machine.Expand.ESearch
end
section
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.T3M.Search (DIG NBUF FailedAt)
-- (open dropped: nothing it names is in this part)
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand.ESearch
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.T3M.Search (DIG NBUF FailedAt)
-- (open dropped: nothing it names is in this part)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.Machine.Sign (run memEval_cons_ofNat)
open ClaudeWCT.W9.Machine.Sign.SearchM (cst rfs mw ctrE grpE fieldE fieldLen idxE costByte costChk
  costChk_getD costByte_lt piece regs_rfs shl0_shr33 sll_eval srl_eval fieldE_eval psum psum_succ psum_le fieldN_lt
  psum_nine digestInput_length' pad64_digestInput' wordsOf_digestInput' blocks_digestInput' childN childN_lt childE_eval)
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
section pieces
variable {im : Image}
end pieces
section loop
variable {im : Image} {sk : BitVec 256}
end loop
end ClaudeWCT.W9.Machine.Expand.ESearch
end
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
end ClaudeWCT.W9.Machine.Expand
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_Base ====
section

section
namespace ClaudeWCT.W9.Machine.Expand
open Lean Meta Elab Tactic
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.VLib
end ClaudeWCT.W9.Machine.Expand
end
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_DrvBits ====
section

section
namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search (DIG NBUF ENC)
set_option autoImplicit false
set_option maxRecDepth 8192
section blocks
variable (s : MachineState)
-- [h2 lane] removed s0_spec: a fact about the record's original expand word 0 / 342, which H2 replaces
end blocks
end SigGolfCandidate.T3M.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest HashOutput)
-- (open dropped: nothing it names is in this part)
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 8192
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand.Driver
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M ClaudeWCT.W9.Machine.Expand
set_option maxRecDepth 16384
end ClaudeWCT.W9.Machine.Expand.Driver
end
section
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput)
set_option linter.unusedSimpArgs false
end ClaudeWCT.W9.Machine.Expand
end
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Merkle_ChildDefs ====
section

namespace ClaudeWCT.W9.Machine.Merkle
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.VLib
open SigGolfCandidate.T3 (Digest HashOutput M header shortHash pad64)
open SphincsSecurity (bytesLE)
def bitAt (j l : Nat) : Nat := j / 2 ^ l % 2
def blkO (l : Nat) : Nat := 64 * (6 - l)
def curO (l j : Nat) : Nat := blkO l + 48 * bitAt j l
def sibO (l j : Nat) : Nat := blkO l + 48 * (1 - bitAt j l)
def padO (l : Nat) : Nat := blkO l + 32
def heapOf (l j : Nat) : Nat := 2 ^ (6 - l) + j / 2 ^ (l + 1)
/-- C4: FTS node words carry the coordinate nibble `k + 1`. -/
def nodeLo (k index : Nat) : Nat := 1537 + 65536 * (k + 1) + 2 ^ 27 * index
def heapReg (h : Nat) : Reg :=
  match h with
  | 2 => .x13 | 3 => .x19 | 4 => .x20 | 5 => .x21 | 6 => .x26 | _ => .x30
def leafBytes (leaf : Nat → Digest) : List UInt8 := (List.range 8).flatMap fun i => bytesLE 16 (leaf i)
def childLevel (k index j : Nat) (sibs : Nat → Digest) (value : Digest) (l : Nat) : M Digest :=
  let pair := if bitAt j l = 0 then (value, sibs l) else (sibs l, value)
  WCT9.wctNodeHash k index (heapOf l j) pair.1 pair.2
def pairOf (j : Nat) (top sib : Digest) : Digest × Digest := if bitAt j 6 = 0 then (top, sib) else (sib, top)
def childProgC (k index j : Nat) (leaf sibs : Nat → Digest) : M (Digest × Digest) := do
  let v ← shortHash (leafBytes leaf)
  let top ← (List.range 6).foldlM (childLevel k index j sibs) v
  pure (pairOf j top (sibs 6))
def stageW (j l : Nat) : List Nat :=
  [curO l j, curO l j + 8, curO l j + 16, curO l j + 24, blkO l + 16, blkO l + 24]
def stagesW (j n : Nat) : List Nat := (List.range n).flatMap (stageW j)
def childWrites (j : Nat) : List Nat := stagesW j 6
def finPath (path : Fin 7 → Digest) (l : Nat) : Digest := if h : l < 7 then path ⟨l, h⟩ else 0
end ClaudeWCT.W9.Machine.Merkle
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_Region ====
section

namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput readDigest readLE)
open SigGolfCandidate.T3M (window window_append_left window_append_right window_full window_zeros zeros)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.T3M (chainBytes leafBytes)
set_option linter.unusedSimpArgs false
section windows
variable (c : Nat) (op : WCT9.Opening)
end windows
end ClaudeWCT.W9.Machine.Expand
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_LayoutCode ====
section

/-! Pairing stage 1: code tables of the leaf / digest layout block 48100 .. 49225 (proofs in `LayoutBlock`). -/
namespace ClaudeWCT.W9.Machine.Expand.Layout
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
/-! Generated by pair1-expand (from sol-pair1/img-candidate/expand.code, words 48119 .. 49224).
T51 (VERA2, round 2; regenerated from the T51 expand image t51/sign/img/t51e, words 48119 .. 49225): the top group
keeps the 51 items of values 0..50 (item 129, value 0: `sd t1,-32(a1)`, so `xK 129 = 2^64 - 32` and its slot is
`(dK + xK) % 2^64 = 25200`; item 129 + i: `X = 16 (i - 1)`). #938's items 180..182 (values 51..53) lost their
stores (`nop`): with the return word they form the straight tail `cRet` (49207 .. 49225, 19 words). -/
def lbCodes : List (List (BitVec 32)) := [[25911,2634351891,340739,6664227,8729347,6665251],[25911,2491745555,340739,40218659,8729347,40219683],[25911,2567243027,340739,40220707,8729347,40221731],[25911,2382693651,340739,73773091,8729347,73774115],[25911,2458191123,340739,73775139,8729347,73776163],[25911,2273641747,340739,107327523,8729347,107328547],[25911,2349139219,340739,107329571,8729347,107330595],[25911,2164589843,340739,140881955,8729347,140882979],[25911,2240087315,340739,140884003,8729347,140885027],[21815,2055537939,340739,174436387,8729347,174437411],[21815,2131035411,340739,174438435,8729347,174439459],[21815,1946486035,340739,207990819,8729347,207991843],[21815,2021983507,340739,207992867,8729347,207993891],[21815,1837434131,340739,241545251,8729347,241546275],[21815,1912931603,340739,241547299,8729347,241548323],[21815,1728382227,340739,275099683,8729347,275100707],[21815,1803879699,340739,275101731,8729347,275102755],[21815,1619330323,340739,308654115,8729347,308655139],[21815,1694827795,340739,308656163,8729347,308657187],[21815,1510278419,340739,342208547,8729347,342209571],[21815,1585775891,340739,342210595,8729347,342211619],[21815,1401226515,340739,375762979,8729347,375764003],[21815,1476723987,340739,375765027,8729347,375766051],[21815,1292174611,340739,409317411,8729347,409318435],[21815,1367672083,340739,409319459,8729347,409320483],[21815,1183122707,340739,442871843,8729347,442872867],[21815,1258620179,340739,442873891,8729347,442874915],[21815,1074070803,340739,476426275,8729347,476427299],[21815,1149568275,340739,476428323,8729347,476429347],[21815,965018899,340739,509980707,8729347,509981731],[21815,1040516371,340739,509982755,8729347,509983779],[21815,855966995,340739,543535139,8729347,543536163],[21815,931464467,340739,543537187,8729347,543538211],[21815,746915091,340739,577089571,8729347,577090595],[21815,822412563,340739,577091619,8729347,577092643],[21815,637863187,340739,610644003,8729347,610645027],[21815,713360659,340739,610646051,8729347,610647075],[21815,528811283,340739,644198435,8729347,644199459],[21815,604308755,340739,644200483,8729347,644201507],[21815,419759379,340739,677752867,8729347,677753891],[21815,495256851,340739,677754915,8729347,677755939],[21815,310707475,340739,711307299,8729347,711308323],[21815,386204947,340739,711309347,8729347,711310371],[21815,4236576019,340739,6664227,8729347,6665251],[21815,4093969683,340739,40218659,8729347,40219683],[21815,4169467155,340739,40220707,8729347,40221731],[21815,3984917779,340739,73773091,8729347,73774115],[21815,4060415251,340739,73775139,8729347,73776163],[21815,3875865875,340739,107327523,8729347,107328547],[21815,3951363347,340739,107329571,8729347,107330595],[21815,3766813971,340739,140881955,8729347,140882979],[21815,3842311443,340739,140884003,8729347,140885027],[21815,3657762067,340739,174436387,8729347,174437411],[21815,3733259539,340739,174438435,8729347,174439459],[21815,3548710163,340739,207990819,8729347,207991843],[21815,3624207635,340739,207992867,8729347,207993891],[21815,3439658259,340739,241545251,8729347,241546275],[21815,3515155731,340739,241547299,8729347,241548323],[21815,3330606355,340739,275099683,8729347,275100707],[21815,3406103827,340739,275101731,8729347,275102755],[21815,3221554451,340739,308654115,8729347,308655139],[21815,3297051923,340739,308656163,8729347,308657187],[21815,3112502547,340739,342208547,8729347,342209571],[21815,3188000019,340739,342210595,8729347,342211619],[21815,3003450643,340739,375762979,8729347,375764003],[21815,3078948115,340739,375765027,8729347,375766051],[21815,2894398739,340739,409317411,8729347,409318435],[21815,2969896211,340739,409319459,8729347,409320483],[21815,2785346835,340739,442871843,8729347,442872867],[21815,2860844307,340739,442873891,8729347,442874915],[21815,2676294931,340739,476426275,8729347,476427299],[21815,2751792403,340739,476428323,8729347,476429347],[21815,2567243027,340739,509980707,8729347,509981731],[21815,2642740499,340739,509982755,8729347,509983779],[21815,2458191123,340739,543535139,8729347,543536163],[21815,2533688595,340739,543537187,8729347,543538211],[21815,2349139219,340739,577089571,8729347,577090595],[21815,2424636691,340739,577091619,8729347,577092643],[21815,2240087315,340739,610644003,8729347,610645027],[21815,2315584787,340739,610646051,8729347,610647075],[17719,2131035411,340739,644198435,8729347,644199459],[21815,2206532883,340739,644200483,8729347,644201507],[17719,2021983507,340739,677752867,8729347,677753891],[17719,2097480979,340739,677754915,8729347,677755939],[17719,1912931603,340739,711307299,8729347,711308323],[17719,1988429075,340739,711309347,8729347,711310371],[17719,1543832851,340739,6664227,8729347,6665251],[17719,1401226515,340739,40218659,8729347,40219683],[17719,1476723987,340739,40220707,8729347,40221731],[17719,1292174611,340739,73773091,8729347,73774115],[17719,1367672083,340739,73775139,8729347,73776163],[17719,1183122707,340739,107327523,8729347,107328547],[17719,1258620179,340739,107329571,8729347,107330595],[17719,1074070803,340739,140881955,8729347,140882979],[17719,1149568275,340739,140884003,8729347,140885027],[17719,965018899,340739,174436387,8729347,174437411],[17719,1040516371,340739,174438435,8729347,174439459],[17719,855966995,340739,207990819,8729347,207991843],[17719,931464467,340739,207992867,8729347,207993891],[17719,746915091,340739,241545251,8729347,241546275],[17719,822412563,340739,241547299,8729347,241548323],[17719,637863187,340739,275099683,8729347,275100707],[17719,713360659,340739,275101731,8729347,275102755],[17719,528811283,340739,308654115,8729347,308655139],[17719,604308755,340739,308656163,8729347,308657187],[17719,419759379,340739,342208547,8729347,342209571],[17719,495256851,340739,342210595,8729347,342211619],[17719,310707475,340739,375762979,8729347,375764003],[17719,386204947,340739,375765027,8729347,375766051],[17719,201655571,340739,409317411,8729347,409318435],[17719,277153043,340739,409319459,8729347,409320483],[17719,92603667,340739,442871843,8729347,442872867],[17719,168101139,340739,442873891,8729347,442874915],[17719,4278519059,340739,476426275,8729347,476427299],[17719,59049235,340739,476428323,8729347,476429347],[17719,4169467155,340739,509980707,8729347,509981731],[17719,4244964627,340739,509982755,8729347,509983779],[17719,4060415251,340739,543535139,8729347,543536163],[17719,4135912723,340739,543537187,8729347,543538211],[17719,3951363347,340739,577089571,8729347,577090595],[17719,4026860819,340739,577091619,8729347,577092643],[17719,3842311443,340739,610644003,8729347,610645027],[17719,3917808915,340739,610646051,8729347,610647075],[17719,3733259539,340739,644198435,8729347,644199459],[17719,3808757011,340739,644200483,8729347,644201507],[17719,3624207635,340739,677752867,8729347,677753891],[17719,3699705107,340739,677754915,8729347,677755939],[17719,3515155731,340739,711307299,8729347,711308323],[17719,3590653203,340739,711309347,8729347,711310371],[17719,3062170899,340739,4268077091,8729347,4268078115],[17719,2995062035,340739,6664227,8729347,6665251],[17719,2927953171,340739,6666275,8729347,6667299],[17719,2860844307,340739,40218659,8729347,40219683],[17719,2793735443,340739,40220707,8729347,40221731],[17719,2726626579,340739,73773091,8729347,73774115],[17719,2659517715,340739,73775139,8729347,73776163],[17719,2592408851,340739,107327523,8729347,107328547],[17719,2525299987,340739,107329571,8729347,107330595],[17719,2458191123,340739,140881955,8729347,140882979],[17719,2391082259,340739,140884003,8729347,140885027],[17719,2323973395,340739,174436387,8729347,174437411],[17719,2256864531,340739,174438435,8729347,174439459],[17719,2189755667,340739,207990819,8729347,207991843],[13623,2122646803,340739,207992867,8729347,207993891],[13623,2055537939,340739,241545251,8729347,241546275],[13623,1988429075,340739,241547299,8729347,241548323],[13623,1921320211,340739,275099683,8729347,275100707],[13623,1854211347,340739,275101731,8729347,275102755],[13623,1787102483,340739,308654115,8729347,308655139],[13623,1719993619,340739,308656163,8729347,308657187],[13623,1652884755,340739,342208547,8729347,342209571],[13623,1585775891,340739,342210595,8729347,342211619],[13623,1518667027,340739,375762979,8729347,375764003],[13623,1451558163,340739,375765027,8729347,375766051],[13623,1384449299,340739,409317411,8729347,409318435],[13623,1317340435,340739,409319459,8729347,409320483],[13623,1250231571,340739,442871843,8729347,442872867],[13623,1183122707,340739,442873891,8729347,442874915],[13623,1116013843,340739,476426275,8729347,476427299],[13623,1048904979,340739,476428323,8729347,476429347],[13623,981796115,340739,509980707,8729347,509981731],[13623,914687251,340739,509982755,8729347,509983779],[13623,847578387,340739,543535139,8729347,543536163],[13623,780469523,340739,543537187,8729347,543538211],[13623,713360659,340739,577089571,8729347,577090595],[13623,646251795,340739,577091619,8729347,577092643],[13623,579142931,340739,610644003,8729347,610645027],[13623,512034067,340739,610646051,8729347,610647075],[13623,444925203,340739,644198435,8729347,644199459],[13623,377816339,340739,644200483,8729347,644201507],[13623,310707475,340739,677752867,8729347,677753891],[13623,243598611,340739,677754915,8729347,677755939],[13623,176489747,340739,711307299,8729347,711308323],[13623,109380883,340739,711309347,8729347,711310371],[13623,42272019,340739,744861731,8729347,744862755],[13623,4270130451,340739,744863779,8729347,744864803],[13623,4203021587,340739,778416163,8729347,778417187],[13623,4135912723,340739,778418211,8729347,778419235],[13623,4068803859,340739,811970595,8729347,811971619],[13623,4001694995,340739,811972643,8729347,811973667]]
def cRet : List (BitVec 32) := [0x00003537,0xea850513,0x00053303,0x00000013,0x00853303,0x00000013,0x00003537,0xe6850513,0x00053303,0x00000013,0x00853303,0x00000013,0x00003537,0xe2850513,0x00053303,0x00000013,0x00853303,0x00000013,0xe8cfa06f]
end ClaudeWCT.W9.Machine.Expand.Layout
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_CompactCode ====
section

namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.VLib

namespace PairCopy
/-! Pairing stage 1: the lower-chain pair copy block at 48000 (outside the compact lookup scope). -/
def cPC0 : List (BitVec 32) := [0x01500613]
def cPCL : List (BitVec 32) := [0x03053303,0x0465bc23,0x03853303,0x0665b023,0x07053303,0x0065b823,0x07853303,
  0x0065bc23,0x08050513,0x06858593,0xfff60613,0xfc061ae3]
def cPCT : List (BitVec 32) := [0x03053303,0x0265b823,0x03853303,0x0265bc23,0x00008067]
/-- The pair copy block's code (head, loop body, tail). -/
structure Code (im : Image) : Prop where
  c0 : CodeAt im (pcOf 48000) cPC0
  cL : CodeAt im (pcOf 48001) cPCL
  cT : CodeAt im (pcOf 48013) cPCT
end PairCopy
end ClaudeWCT.W9.Machine.Expand

namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
section code
variable {im : Image}                        
-- (include dropped in this part)
end code
end ClaudeWCT.W9.Machine.Expand.Compact

namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.VLib
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
end ClaudeWCT.W9.Machine.Expand
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_Compact2Lv ====
section

section

namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
-- (open dropped: nothing it names is in this part)
def cZero2 : List (BitVec 32) := [1463,1208321427,5687,3276146195,4229951727]  -- nested FTS: zero 2718 words from 1216
/-- Nested FTS (r1-1): the header copy is replaced by `jal zero,P_final` (P_final at words 33117..33284). -/
def cHdr : List (BitVec 32) := [2899275887]
def holdPc (c : Nat) : Nat := 33176 + 12 * c
def cCh3 : List (BitVec 32) := [3233079,2827289875,21943,293963155,1591,361104915,1329615087]
section code
variable {im : Image}                                                    
-- (include dropped in this part)
end code
end ClaudeWCT.W9.Machine.Expand.Compact2
end

section


namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
-- (open dropped: nothing it names is in this part)
set_option linter.unusedSimpArgs false
/-- Lower-layer path area in the final witness (pairing stage 1: abs `2904 + layerBase` = 15224 / 17872 / 20440). -/
def lvDst (lay : Nat) : Nat := 0x800 + (if lay = 1 then 13176 else if lay = 2 then 15824 else 18392)
section eval
variable {s : MachineState} {r : Nat} (h19 : s.getReg .x19 = BitVec.ofNat 64 r) (hr : r < 2 ^ 7)
include h19 hr
end eval
section
variable {im : Image}                                                    
-- (include dropped in this part)
end
end ClaudeWCT.W9.Machine.Expand.Compact2
end

section
namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
-- (open dropped: nothing it names is in this part)
set_option linter.unusedSimpArgs false
/-! C3 (FULL, E6): the root level of each lower layer runs in three pieces: `cLvA` (Z low word copy, then
`jal rtAt`), the trampoline `cRT` (Z high word copy, LE64(1) at window + 24, `jal` back) and `cLvB` (sibling copy). -/
section
variable {im : Image}                                                    
-- (include dropped in this part)
end
end ClaudeWCT.W9.Machine.Expand.Compact2
end
end
