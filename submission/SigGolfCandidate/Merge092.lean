import SigGolfCandidate.Merge052
import SigGolfCandidate.Merge054
import SigGolfCandidate.Merge056
import SigGolfCandidate.Merge058
import SigGolfCandidate.Merge061
import SigGolfCandidate.Merge076
import SigGolfCandidate.Merge078
import SigGolfCandidate.Merge080
import SigGolfCandidate.Merge084
import SigGolfCandidate.Merge090
import SigGolfCandidate.Merge091

-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_Routine ====
section

section
namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.VLib
open SigGolfCandidate.T3 (Digest HashOutput M header shortHash pad64 zero16)
open SphincsSecurity (bytesLE)
set_option linter.unusedSimpArgs false
def keepC (s u : MachineState) : Prop :=
  ∀ r, r ≠ .x3 → r ≠ .x10 → r ≠ .x12 → r ≠ .x14 → r ≠ .x25 → u.getReg r = s.getReg r
theorem keepC.refl (s : MachineState) : keepC s s := fun _ _ _ _ _ _ => rfl
theorem keepC.trans {s u w : MachineState} (h1 : keepC s u) (h2 : keepC u w) : keepC s w :=
  fun r a b c d e => (h2 r a b c d e).trans (h1 r a b c d e)
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.VLib
open SigGolfCandidate.T3 (Digest HashOutput M shortHash)
set_option linter.unusedSimpArgs false
def jalTo (w : BitVec 32) (n : Nat) : Option Nat :=
  match decodeInstruction w with
  | some (.base (.JAL .x0 imm)) =>
    let a := (0x1000 + 4 * n + (signExtend21 imm).toNat) % 2 ^ 64
    if 0x1000 ≤ a ∧ a % 4 = 0 then some ((a - 0x1000) / 4) else none
  | _ => none
theorem jalTo_sound {w : BitVec 32} {n m : Nat} (h : jalTo w n = some m) :
    ∃ imm, decodeInstruction w = some (.base (.JAL .x0 imm)) ∧
      (0x1000 + 4 * n + (signExtend21 imm).toNat) % 2 ^ 64 = (0x1000 + 4 * m) % 2 ^ 64 := by
  unfold jalTo at h
  split at h
  · rename_i imm hd
    refine ⟨imm, hd, ?_⟩
    simp only at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      subst h
      have : (0x1000 + 4 * n + (signExtend21 imm).toNat) % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by positivity)
      rw [Nat.mod_eq_of_lt (a := 0x1000 + 4 * _) (by omega)]
      omega
    · cases h
  · cases h
end ClaudeWCT.W9.Machine.Expand
end

namespace ClaudeWCT.W9.Machine.Expand.SharedCore
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest M)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

def Post (L : W9Machine.Layout) (w : W9Machine.WBytes) (index : Nat) (k : Fin 9) (raw : Fin 128)
    (entry : MachineState) (computed : Digest) (result : MachineState) : Prop :=
  ∃ ends childEntry,Chain.Post L w index k raw entry ends childEntry ∧
    SharedChild.Post L k raw childEntry computed result

theorem core_tbsim (L : W9Machine.Layout) (sk : BitVec 256)
    (hwindow : (Frozen.image.code.drop 195584).take 59072=(L.image.code.drop 195584).take 59072)
    (k : Fin 9) (raw : Fin 128) (rank : Fin 563)
    (hchild : ∀j,L.childWord j=(SharedLayout.layout k).childWord j)
    (hchain : ∀w index u,N600.Pre L w index k raw rank u→
      TBSim L.image sk u 89 (N600.program w index k raw rank) (N600.Post L w index k raw u))
    (w : W9Machine.WBytes) (index : Nat) (snapshot u : MachineState) (padL padR : Digest)
    (hu : N600.Pre L (SharedV3.viewWB 2904 w k.val snapshot) index k raw rank u)
    (hL : DigAt snapshot (2904+V3.regionOffset k.val+672) padL)
    (hR : DigAt snapshot (2904+V3.regionOffset k.val+160) padR) :
    TBSim L.image sk u (89+SharedChild.cost k raw)
      (N600.program w index k raw rank >>=fun ends=>SharedV3.childN w index k raw ends padL padR)
      (Post L (SharedV3.viewWB 2904 w k.val snapshot) index k raw u) := by
  have hspec : (N600.program w index k raw rank >>= fun ends=>SharedV3.childN w index k raw ends padL padR)=
      (N600.program (SharedV3.viewWB 2904 w k.val snapshot) index k raw rank >>=fun ends=>
        SharedV3.childProgram (SharedV3.viewWB 2904 w k.val snapshot) index k raw ends) := by
    unfold N600.program
    rw [SharedV3.chainProgram_viewB]
    simp only [fun ends=>SharedV3.childProgram_viewB 2904 w index k snapshot raw ends padL padR hL hR]
  rw [hspec]
  refine TBSim.bind (hchain _ _ _ hu) ?_
  intro ends childEntry hp
  exact (W9Drv.SharedBank.child_tbsim L sk k raw hwindow hchild _ index ends childEntry
    (hp.sharedChild hu)).mono le_rfl (fun computed t ht=>⟨ends,childEntry,hp,ht⟩)

end ClaudeWCT.W9.Machine.Expand.SharedCore

namespace ClaudeWCT.W9.Machine.Expand.SharedDispatch
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest HashOutput)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def start (k : Nat) : Nat := [46513,46551,46590,46629,46668,46707,46746,46785,46824].getD k 0
def endWord (k : Nat) : Nat := [46551,46590,46629,46668,46707,46746,46785,46824,46862].getD k 0
def length (k : Nat) : Nat := endWord k-start k
/-- Dispatch code of coordinate `k` (`expandSharedDriver` offsets 1457..1805). Stage 2: coordinate 8 sets
`ra = pcOf (endWord 8 - 78)` (`addi ra,ra,-284`, was `-280`), since the merged singleton returns with
`jalr zero,312(ra)` (was 308) to the same word 46862. -/
def words (k : Nat) : List (BitVec 32) := [
[0x208b7,0x16088893,0x8b203,0x10337,0x7f27213,0x8b703,0xd75713,0x3ff77713,0x2437,0x62840413,0x66e37,0xe0e13,0x10e3783,0x1b79793,0x60130313,0x6787b3,0x1421f93,0xff8fb3,0x721b93,0xe3337,0x30030313,0x6b8bb3,0x293,0x100393,0x200693,0x300993,0x400a13,0x500a93,0x600d13,0x700f13,0x4000593,0x97,0xef408093,0x871713,0xc0337,0x30313,0x670733,0x70067],
[0x208b7,0x16088893,0x8b203,0x625213,0x7f27213,0x88b703,0xd75713,0x3ff77713,0x2437,0x2d840413,0x66e37,0xe0e13,0x10e3783,0x1b79793,0x20337,0x60130313,0x6787b3,0x1421f93,0xff8fb3,0x821b93,0xf2337,0xb0030313,0x6b8bb3,0x293,0x100393,0x200693,0x300993,0x400a13,0x500a93,0x600d13,0x700f13,0x4000593,0x97,0xef408093,0x871713,0xc0337,0x30313,0x670733,0x70067],
[0x208b7,0x16088893,0x88b203,0x25213,0x7f27213,0x88b703,0x1975713,0x3ff77713,0x2437,0xf8840413,0x66e37,0xe0e13,0x10e3783,0x1b79793,0x30337,0x60130313,0x6787b3,0x1421f93,0xff8fb3,0x721b93,0xe3337,0x30030313,0x6b8bb3,0x293,0x100393,0x200693,0x300993,0x400a13,0x500a93,0x600d13,0x700f13,0x4000593,0x97,0xef408093,0x871713,0xc0337,0x30313,0x670733,0x70067],
[0x208b7,0x16088893,0x88b203,0x625213,0x7f27213,0x88b703,0x2575713,0x3ff77713,0x2437,0xc3840413,0x66e37,0xe0e13,0x10e3783,0x1b79793,0x40337,0x60130313,0x6787b3,0x1421f93,0xff8fb3,0x821b93,0xf2337,0xb0030313,0x6b8bb3,0x293,0x100393,0x200693,0x300993,0x400a13,0x500a93,0x600d13,0x700f13,0x4000593,0x97,0xef408093,0x871713,0xc0337,0x30313,0x670733,0x70067],
[0x208b7,0x16088893,0x108b203,0x25213,0x7f27213,0x108b703,0xd75713,0x3ff77713,0x2437,0x8e840413,0x66e37,0xe0e13,0x10e3783,0x1b79793,0x50337,0x60130313,0x6787b3,0x1421f93,0xff8fb3,0x721b93,0xe3337,0x30030313,0x6b8bb3,0x293,0x100393,0x200693,0x300993,0x400a13,0x500a93,0x600d13,0x700f13,0x4000593,0x97,0xef408093,0x871713,0xc0337,0x30313,0x670733,0x70067],
[0x208b7,0x16088893,0x108b203,0x625213,0x7f27213,0x108b703,0x1975713,0x3ff77713,0x1437,0x59840413,0x66e37,0xe0e13,0x10e3783,0x1b79793,0x60337,0x60130313,0x6787b3,0x1421f93,0xff8fb3,0x821b93,0xf2337,0xb0030313,0x6b8bb3,0x293,0x100393,0x200693,0x300993,0x400a13,0x500a93,0x600d13,0x700f13,0x4000593,0x97,0xef408093,0x871713,0xc0337,0x30313,0x670733,0x70067],
[0x208b7,0x16088893,0x188b203,0x25213,0x7f27213,0x108b703,0x2575713,0x3ff77713,0x1437,0x24840413,0x66e37,0xe0e13,0x10e3783,0x1b79793,0x70337,0x60130313,0x6787b3,0x1421f93,0xff8fb3,0x721b93,0xe3337,0x30030313,0x6b8bb3,0x293,0x100393,0x200693,0x300993,0x400a13,0x500a93,0x600d13,0x700f13,0x4000593,0x97,0xef408093,0x871713,0xc0337,0x30313,0x670733,0x70067],
[0x208b7,0x16088893,0x188b203,0x625213,0x7f27213,0x188b703,0xd75713,0x3ff77713,0x1437,0xef840413,0x66e37,0xe0e13,0x10e3783,0x1b79793,0x80337,0x60130313,0x6787b3,0x1421f93,0xff8fb3,0x821b93,0xf2337,0xb0030313,0x6b8bb3,0x293,0x100393,0x200693,0x300993,0x400a13,0x500a93,0x600d13,0x700f13,0x4000593,0x97,0xef408093,0x871713,0xc0337,0x30313,0x670733,0x70067],
[0x208b7,0x16088893,0x188b203,0x2525213,0x7f27213,0x188b703,0x1975713,0x3ff77713,0xcb040413,0x66e37,0xe0e13,0x10e3783,0x1b79793,0x90337,0x60130313,0x6787b3,0x1421f93,0xff8fb3,0x821b93,0xe7337,0x40030313,0x6b8bb3,0x293,0x100393,0x200693,0x300993,0x400a13,0x500a93,0x600d13,0x700f13,0x4000593,0x97,0xedc08093,0x871713,0xc0337,0x30313,0x670733,0x70067]].getD k []
def rawPosition (k : Nat) : Nat := [0,6,0,6,0,6,0,6,37].getD k 0
def rawWord (k : Nat) : Nat := [0,0,1,1,2,2,3,3,3].getD k 0
def rankPosition (k : Nat) : Nat := [13,13,25,37,13,25,37,13,25].getD k 0
def rankWord (k : Nat) : Nat := [0,1,1,1,2,2,2,3,3].getD k 0
def rawRead (k : Nat) (u : MachineState) : Word :=
  (u.getMem (BitVec.ofNat 64 (0x20160+8*rawWord k)) >>> rawPosition k) &&& 127#64
def rankRead (k : Nat) (u : MachineState) : Word :=
  (u.getMem (BitVec.ofNat 64 (0x20160+8*rankWord k)) >>> rankPosition k) &&& 1023#64

def result (k : Nat) : Result :=
  -- C4: coordinate 0 replaces its `srli tp,tp,0` no-op by the label `lui`, so its raw read has no shift.
  let raw := if k = 0 then mkBin .and (.ld (.c (BitVec.ofNat 64 (0x20160+8*rawWord k)))) (.c 127)
    else mkBin .and (mkBin .srl (.ld (.c (BitVec.ofNat 64 (0x20160+8*rawWord k)))) (.c (BitVec.ofNat 64 (rawPosition k)))) (.c 127)
  let rank := mkBin .and (mkBin .srl (.ld (.c (BitVec.ofNat 64 (0x20160+8*rankWord k)))) (.c (BitVec.ofNat 64 (rankPosition k)))) (.c 1023)
  let node := mkAdd (mkBin .sll (.ld (.c 0x66010)) (.c 27)) (.c (BitVec.ofNat 64 (1537+65536*(k+1))))
  let chainPC := mkAdd (mkBin .sll rank (.c 8)) (.c 0xc0000)
  let childPC := mkAdd (mkBin .sll raw (.c (if k<8 ∧ k%2=0 then 7 else 8)))
    (.c (BitVec.ofNat 64 (4096+4*(if k<8 ∧ k%2=0 then 231616 else if k=8 then 235776 else 246464))))
  let regs := RegFile.init.set .x17 (.c 0x20160)
  let regs := (regs.set .x4 raw).set .x14 chainPC
  -- Pairing stage 1: coordinate 8 derives its base from the incoming `s0` (r3w: `addi s0,s0,-848`; the banks run at
  -- `coordinateBase k - 1224`, the expand FTS frame).
  let regs := (regs.set .x8 (if k = 8 then .bin .add (.reg .x8) (.c (BitVec.ofNat 64 (2^64-848)))
    else .c (BitVec.ofNat 64 (9768-848*k)))).set .x28 (.c 0x66000)
  let regs := (regs.set .x15 node).set .x6 (.c 0xc0000)
  let regs := (regs.set .x31 (mkAdd (mkBin .sll raw (.c 20)) node)).set .x23 childPC
  let regs := (regs.set .x5 (.c 0)).set .x7 (.c 1)
  let regs := (regs.set .x13 (.c 2)).set .x19 (.c 3)
  let regs := (regs.set .x20 (.c 4)).set .x21 (.c 5)
  let regs := (regs.set .x26 (.c 6)).set .x30 (.c 7)
  let regs := (regs.set .x11 (.c 64)).set .x1 (.c (pcOf (endWord k-(if k=8 then 80 else 74))))
  ⟨⟨regs,[],[]⟩,mkBin .and chainPC (.c (~~~1#64)),.jump,length k,length k⟩
theorem checked0 : rOK (symRun {} (words 0) (pcOf (start 0)) (length 0)) (result 0)=true := by decide +kernel
theorem checked1 : rOK (symRun {} (words 1) (pcOf (start 1)) (length 1)) (result 1)=true := by decide +kernel
theorem checked2 : rOK (symRun {} (words 2) (pcOf (start 2)) (length 2)) (result 2)=true := by decide +kernel
theorem checked3 : rOK (symRun {} (words 3) (pcOf (start 3)) (length 3)) (result 3)=true := by decide +kernel
theorem checked4 : rOK (symRun {} (words 4) (pcOf (start 4)) (length 4)) (result 4)=true := by decide +kernel
theorem checked5 : rOK (symRun {} (words 5) (pcOf (start 5)) (length 5)) (result 5)=true := by decide +kernel
theorem checked6 : rOK (symRun {} (words 6) (pcOf (start 6)) (length 6)) (result 6)=true := by decide +kernel
theorem checked7 : rOK (symRun {} (words 7) (pcOf (start 7)) (length 7)) (result 7)=true := by decide +kernel
theorem checked8 : rOK (symRun {} (words 8) (pcOf (start 8)) (length 8)) (result 8)=true := by decide +kernel
theorem checked (k : Fin 9) : symRun {} (words k.val) (pcOf (start k.val)) (length k.val)=some (result k.val) := by
  apply rOK_eq
  fin_cases k
  · exact checked0
  · exact checked1
  · exact checked2
  · exact checked3
  · exact checked4
  · exact checked5
  · exact checked6
  · exact checked7
  · exact checked8

theorem result_mem (k : Fin 9) (u : MachineState) (a : Word) :
    ((result k.val).toState u).getMem a=u.getMem a := by fin_cases k <;> rfl

theorem result_raw (k : Fin 9) (u : MachineState) :
    ((result k.val).toState u).getReg .x4=rawRead k.val u := by fin_cases k <;> rfl

theorem result_node (k : Fin 9) (u : MachineState) :
    ((result k.val).toState u).getReg .x15=
      (u.getMem 0x66010 <<< 27)+BitVec.ofNat 64 (1537+65536*(k.val+1)) := by fin_cases k <;> rfl

theorem result_leaf (k : Fin 9) (u : MachineState) :
    ((result k.val).toState u).getReg .x31=
      (rawRead k.val u <<< 20)+((result k.val).toState u).getReg .x15 := by fin_cases k <;> simp [result,rawRead,rawWord,rawPosition,Result.toState_getReg,RegFile.get,RegFile.set,mkAdd,addC,mkBin,E.eval,BinOp.eval,BitVec.add_assoc]

theorem result_base (k : Fin 9) (u : MachineState)
    (h8 : k.val = 8 → u.getReg .x8 = BitVec.ofNat 64 3832) :
    ((result k.val).toState u).getReg .x8=BitVec.ofNat 64 (coordinateBase k - 1224) := by
  by_cases hk : k.val = 8
  · obtain rfl : k = 8 := Fin.ext hk
    rw [Result.toState_getReg, show (result (8 : Fin 9).val).st.regs.get .x8 =
      E.bin .add (.reg .x8) (.c (BitVec.ofNat 64 (2^64-848))) from rfl]
    simp only [E.eval, BinOp.eval, h8 rfl]
    decide
  · fin_cases k <;> first | exact absurd rfl hk | rfl

theorem result_return (k : Fin 9) (u : MachineState) :
    ((result k.val).toState u).getReg .x1=pcOf (endWord k.val-(if k.val=8 then 80 else 74)) := by fin_cases k <;> rfl

theorem result_pc (k : Fin 9) (u : MachineState) :
    ((result k.val).toState u).pc=((rankRead k.val u <<< 8)+0xc0000#64) &&& ~~~1#64 := by fin_cases k <;> rfl

end ClaudeWCT.W9.Machine.Expand.SharedDispatch

namespace ClaudeWCT.W9.Machine.Expand.SharedDispatch
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest M)
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- r3w: the expander runs the shared banks 1224 bytes below verify (`delta8 = 153`). -/
noncomputable def layout (image : Image) (k : Fin 9) : W9Machine.Layout :=
  ⟨image,Frozen.layout.chainWord,(SharedLayout.layout k).childWord,
    fun _=>endWord k.val-(if k.val=8 then 80 else 74),153⟩
theorem layout_shift (image : Image) (k : Fin 9) : (layout image k).shift = 1224 := rfl
theorem layout_base (image : Image) (k k' : Fin 9) : Chain.base (layout image k) k' = coordinateBase k' - 1224 := by
  unfold Chain.base; rw [layout_shift]

theorem steps (image : Image) (k : Fin 9) (u : MachineState)
    (hrun : symRun {} (words k.val) (pcOf (start k.val)) (length k.val)=some (result k.val))
    (hcode : CodeAt image (pcOf (start k.val)) (words k.val)) (hpc : u.pc=pcOf (start k.val)) :
    Steps image u (length k.val) (length k.val) ((result k.val).toState u) := by
  have h:=symRun_sound hrun hcode u hpc (by exact True.intro)
  exact h

theorem result_child_raw (k : Fin 9) (u : MachineState) : ((result k.val).toState u).getReg .x23=
      (rawRead k.val u <<< (if k.val<8 ∧ k.val%2=0 then 7 else 8))+
        BitVec.ofNat 64 (4096+4*(if k.val<8 ∧ k.val%2=0 then 231616 else if k.val=8 then 235776 else 246464)) := by
  fin_cases k <;> rfl


theorem result_child (k : Fin 9) (u : MachineState) (raw : Fin 128)
    (hraw : rawRead k.val u=BitVec.ofNat 64 raw.val) :
    ((result k.val).toState u).getReg .x23=pcOf ((SharedLayout.layout k).childWord raw) := by
  change _=pcOf (SharedLayout.childWord k.val raw.val)
  rw [result_child_raw,hraw]
  unfold SharedLayout.childWord
  split_ifs <;> rw [BitVec.shiftLeft_eq_mul_twoPow]
  all_goals change BitVec.ofNat 64 raw.val * BitVec.ofNat 64 _ + BitVec.ofNat 64 _ = BitVec.ofNat 64 _
  all_goals rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add]; congr 1 <;> norm_num [Nat.shiftLeft_eq] <;> omega

theorem result_node_value (k : Fin 9) (u : MachineState) (index : Nat)
  (hi : index<2^31) (hindex : u.getMem 0x66010=BitVec.ofNat 64 index) : ((result k.val).toState u).getReg .x15=BitVec.ofNat 64 (V3.nodeLow k.val index) := by
  rw [result_node,hindex]
  apply BitVec.eq_of_toNat_eq
  simp only [V3.nodeLow,ClaudeWCT.WCT9.ftsLeafLow,Nat.mod_eq_of_lt hi,
    Nat.mod_eq_of_lt (show k.val<16 by have := k.isLt; omega)]
  simp [BitVec.toNat_add,BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,Nat.shiftLeft_eq]
  omega

theorem result_hashMode (k : Fin 9) (u : MachineState) : ((result k.val).toState u).getReg .x5=0 := by fin_cases k <;> rfl
theorem result_stepOne (k : Fin 9) (u : MachineState) : ((result k.val).toState u).getReg .x7=1 := by fin_cases k <;> rfl
theorem result_stepTwo (k : Fin 9) (u : MachineState) : ((result k.val).toState u).getReg .x13=2 := by fin_cases k <;> rfl
theorem result_hashLen (k : Fin 9) (u : MachineState) : ((result k.val).toState u).getReg .x11=64 := by fin_cases k <;> rfl
theorem result_heaps (k : Fin 9) (u : MachineState) (h : Nat) (h2 : 2≤h) (h7 : h≤7) :
    ((result k.val).toState u).getReg (Child.heapReg h)=BitVec.ofNat 64 h := by
  interval_cases h <;> fin_cases k <;> rfl

theorem result_pc_value (k : Fin 9) (u : MachineState) (rank : Nat)
    (hrank : rankRead k.val u=BitVec.ofNat 64 rank) :
    ((result k.val).toState u).pc=pcOf (195584+64*rank) := by
  have he : (BitVec.ofNat 64 rank <<< 8)+0xc0000#64=pcOf (195584+64*rank) := by
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 rank * BitVec.ofNat 64 256 + BitVec.ofNat 64 786432 = BitVec.ofNat 64 _
    rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add]
    congr 1
    omega
  exact (result_pc k u).trans ((congrArg (fun x : Word=>((x <<< 8)+0xc0000#64) &&& ~~~1#64) hrank).trans
    ((congrArg (fun x : Word=>x &&& ~~~1#64) he).trans (pcOf_and_not1 _)))

theorem result_leaf_value (k : Fin 9) (u : MachineState) (index : Nat) (raw : Fin 128)
    (hi : index<2^31) (hindex : u.getMem 0x66010=BitVec.ofNat 64 index)
    (hraw : rawRead k.val u=BitVec.ofNat 64 raw.val) :
    ((result k.val).toState u).getReg .x31=BitVec.ofNat 64 (V3.leafLow index k.val raw.val) := by
  have hp : (BitVec.ofNat 64 raw.val <<< 20)+BitVec.ofNat 64 (V3.nodeLow k.val index)=
      BitVec.ofNat 64 (V3.leafLow index k.val raw.val) := by
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 raw.val * BitVec.ofNat 64 1048576 + BitVec.ofNat 64 _ = BitVec.ofNat 64 _
    rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add]
    congr 1
    simp only [V3.leafLow,V3.nodeLow,ClaudeWCT.WCT9.ftsLeafLow,Nat.zero_mod,Nat.zero_mul,Nat.add_zero,
      Nat.mod_eq_of_lt raw.isLt]
    omega
  exact (result_leaf k u).trans ((congrArg₂ (fun a b : Word=>(a <<< 20)+b) hraw
    (result_node_value k u index hi hindex)).trans hp)


theorem chain_pre (image : Image) (k : Fin 9) (u : MachineState)
    (w : W9Machine.WBytes) (index : Nat) (raw : Fin 128) (rank : Fin 563)
    (hi : index<2^31) (hindex : u.getMem 0x66010=BitVec.ofNat 64 index)
    (hraw : rawRead k.val u=BitVec.ofNat 64 raw.val)
    (hrank : rankRead k.val u=BitVec.ofNat 64 rank.val)
    (hslot : Frozen.layout.chainWord (N600.embed rank)=195584+64*rank.val)
    (hW : ∀off,off<848 → off%8=0 → u.getMem (BitVec.ofNat 64 (coordinateBase k - 1224+off))=
      w.extractLsb' (8*(V3.regionOffset k.val+off)) 64)
    (h8 : k.val = 8 → u.getReg .x8 = BitVec.ofNat 64 3832) :
    N600.Pre (layout image k) w index k raw rank ((result k.val).toState u) := by
  have hk:=k.isLt
  have hj:=raw.isLt
  have hnode := result_node_value k u index hi hindex
  constructor
  all_goals try (case childIdx => exact (result_raw k u).trans hraw)
  case indexBound => exact hi
  case baseReg => rw [result_base k u h8, layout_base]
  case nodeWord => exact hnode
  case childPC => exact result_child k u raw hraw
  case returnPC => exact result_return k u
  case pc =>
    exact (result_pc_value k u rank.val hrank).trans (congrArg pcOf hslot.symm)
  case leafWord => exact result_leaf_value k u index raw hi hindex hraw
  case hashMode => exact result_hashMode k u
  case stepOne => exact result_stepOne k u
  case stepTwo => exact result_stepTwo k u
  case hashLen => exact result_hashLen k u
  case heaps =>
    exact result_heaps k u
  case witness =>
    intro off ho h8
    rw [result_mem, layout_base]
    exact hW off ho h8
end ClaudeWCT.W9.Machine.Expand.SharedDispatch

namespace ClaudeWCT.W9.Machine.Expand.SharedForestRun
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest M)
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def writes (addr : Nat) : Prop := 1152≤addr ∧ addr<11000
def isHand (n off : Nat) : Prop :=
  if n=9 then (752≤off ∧ off<784) ∨ (816≤off ∧ off<848) else SharedV3.isHand off
/-- r3w: absolute base of FTS region `n` in the expander (the verify region `regionAddr n` moved down 1224 bytes). -/
def eRegion (n : Nat) : Nat := 9768-848*n
def pcWord (n : Nat) : Nat := if n<9 then SharedDispatch.start n else 46862
structure Fields (index : Nat) (raw : Fin 9 → Fin 128) (ranks : Fin 9 → Fin 563) (u : MachineState) : Prop where
  index : u.getMem 0x66010=BitVec.ofNat 64 index
  raw : ∀k,SharedDispatch.rawRead k.val u=BitVec.ofNat 64 (raw k).val
  rank : ∀k,SharedDispatch.rankRead k.val u=BitVec.ofNat 64 (ranks k).val
structure Inv (w : W9Machine.WBytes) (index : Nat) (raw : Fin 9 → Fin 128) (ranks : Fin 9 → Fin 563)
    (initial : MachineState) (n : Nat) (prev : Digest×Digest) (u : MachineState) : Prop where
  le : n≤9
  pc : u.pc=pcOf (pcWord n)
  fields : Fields index raw ranks u
  prevL : DigAt u (eRegion n+SharedV3.handL n) prev.1
  prevR : DigAt u (eRegion n+SharedV3.handR n) prev.2
  /-- Original witness words of the coordinates not yet run. Stage 2 (C3): region 9 (the L3 encoding row,
  `WIT + 0 .. WIT + 80`; witness trim) excludes its offset `840` = `WIT + 24`, the row tweak's high word (a witness pad, honest
  LE64 1). No FTS routine reads it, and in the expander's first forest pass the cleared witness prefix still holds 0
  there (the final pass restores it, `SharedScatter.finishCode`). -/
  coords : ∀ (m : Nat), n ≤ m → m ≤ 9 → ∀ (off : Nat), off < 848 → off % 8 = 0 →
    (m = 9 → 768 ≤ off ∧ off ≠ 792) → (m = n → ¬ isHand n off) →
    W9Machine.OrigWD 1224 w u (eRegion m + off)
  frame : Frame initial u writes
  /-- Pairing stage 1: `s0` holds the previous coordinate's base (coordinate 8's dispatch derives its base from it;
  after coordinate 8 it is `coordinateBase 8 = 2984`, read by the hand-off). -/
  x8 : 0 < n → u.getReg .x8 = BitVec.ofNat 64 (2984 + 848 * (9 - n))

theorem child_writes_bounds {image : Image} (k : Fin 9) (raw : Fin 128) (addr : Nat)
    (h : SharedChild.writes (SharedDispatch.layout image k) k raw addr) : writes addr := by
  have hk:=k.isLt
  simp only [SharedChild.writes, SharedChild.outputAddr, SharedChild.handAddr, SharedDispatch.layout_base] at h
  unfold coordinateBase at h
  unfold writes
  split_ifs at h <;> omega

theorem fields_frame {index : Nat} {raw : Fin 9 → Fin 128} {ranks : Fin 9 → Fin 563}
    {u t : MachineState} (hf : Frame u t writes) (hu : Fields index raw ranks u) :
    Fields index raw ranks t := by
  have hm (addr : Nat) (ha : 11000≤addr) (hb : addr<2^64) :
      t.getMem (BitVec.ofNat 64 addr)=u.getMem (BitVec.ofNat 64 addr) :=
    hf addr hb (by unfold writes;omega)
  refine ⟨(hm 0x66010 (by decide) (by decide)).trans hu.index,?_,?_⟩
  · intro k
    rw [SharedDispatch.rawRead,hm _ (by fin_cases k <;> decide) (by fin_cases k <;> decide)]
    exact hu.raw k
  · intro k
    rw [SharedDispatch.rankRead,hm _ (by fin_cases k <;> decide) (by fin_cases k <;> decide)]
    exact hu.rank k

theorem witness_view {w : W9Machine.WBytes} {index : Nat} {raw : Fin 9 → Fin 128}
    {ranks : Fin 9 → Fin 563} {initial u : MachineState} {k : Fin 9} {prev : Digest×Digest}
    (hu : Inv w index raw ranks initial k.val prev u) :
    ∀off,off<848 → off%8=0 → u.getMem (BitVec.ofNat 64 (coordinateBase k - 1224+off))=
      (SharedV3.viewWB 2904 w k.val u).extractLsb' (8*(V3.regionOffset k.val+off)) 64 := by
  intro off ho h8
  have hk:=k.isLt
  have hr8:=V3.regionOffset_mod k.val
  rw [SharedV3.view_wordB 2904 w k.val u _ (by omega) (by unfold V3.regionOffset;omega)]
  by_cases hh:SharedV3.isHand off
  · rw [if_pos ⟨by omega,by simpa only [Nat.add_sub_cancel_left] using hh⟩]
    congr 2
    unfold coordinateBase V3.regionOffset
    omega
  · rw [if_neg (fun h=>hh (by simpa only [Nat.add_sub_cancel_left] using h.2))]
    have hw:=hu.coords k.val (by omega) (by omega) off ho h8 (by omega)
      (fun _=>by simpa only [isHand,if_neg (by omega : k.val≠9)] using hh)
    have he:eRegion k.val+off+1224-0x1020=V3.regionOffset k.val+off := by
      unfold eRegion V3.regionOffset;omega
    have hb:coordinateBase k - 1224+off=eRegion k.val+off := by unfold coordinateBase eRegion;omega
    rw [hb]
    simpa only [W9Machine.OrigWD,he] using hw

theorem core_frame {L : W9Machine.Layout} {w : W9Machine.WBytes} {index : Nat} {k : Fin 9}
    {raw : Fin 128} {u entry t : MachineState} {ends : List Digest} {computed : Digest}
    (hp : Chain.Post L w index k raw u ends entry) (ht : SharedChild.Post L k raw entry computed t) :
    Frame u t (SharedChild.writes L k raw) := by
  intro addr ha hn
  rw [ht.frame addr ha hn]
  apply hp.frame addr ha
  intro h
  apply hn
  left
  unfold Chain.writes at h
  simp only [Chain.base] at h ⊢
  split <;> omega

theorem core_frame_dispatch {L : W9Machine.Layout} {w : W9Machine.WBytes} {index : Nat} {k : Fin 9}
    {raw : Fin 128} {u entry t : MachineState} {ends : List Digest} {computed : Digest}
    (hp : Chain.Post L w index k raw ((SharedDispatch.result k.val).toState u) ends entry)
    (ht : SharedChild.Post L k raw entry computed t) : Frame u t (SharedChild.writes L k raw) := by
  intro addr ha hn
  exact (core_frame hp ht addr ha hn).trans (SharedDispatch.result_mem k u _)

theorem hand_address (image : Image) (k : Fin 9) (raw : Fin 128) :
    SharedChild.handAddr (SharedDispatch.layout image k) k raw=eRegion (k.val+1)+
      (if SharedV3.direction k.val (SharedV3.physical k.val raw.val)=0 then SharedV3.handL (k.val+1) else SharedV3.handR (k.val+1)) := by
  have hk:=k.isLt
  simp only [SharedChild.handAddr, SharedDispatch.layout_base]
  unfold coordinateBase eRegion SharedV3.handR SharedV3.handL
  split_ifs <;> omega

theorem next_other {image : Image} (w : W9Machine.WBytes) (k : Fin 9) (raw : Fin 128)
    (u t : MachineState) (hf : Frame u t (SharedChild.writes (SharedDispatch.layout image k) k raw)) (off : Nat)
    (hoff : off=SharedV3.handL (k.val+1) ∨ off=SharedV3.handR (k.val+1))
    (hsel : if SharedV3.direction k.val (SharedV3.physical k.val raw.val)=0
      then off=SharedV3.handR (k.val+1) else off=SharedV3.handL (k.val+1))
    (h0 : W9Machine.OrigWD 1224 w u (eRegion (k.val+1)+off))
    (h1 : W9Machine.OrigWD 1224 w u (eRegion (k.val+1)+(off+8))) :
    DigAt t (eRegion (k.val+1)+off)
      (SharedV3.topOther w k.val (SharedV3.physical k.val raw.val)) := by
  have hk:=k.isLt
  have h1':W9Machine.OrigWD 1224 w u (eRegion (k.val+1)+off+8) := by rw [Nat.add_assoc];exact h1
  have hlo:0x1020≤eRegion (k.val+1)+off+1224 := by
    unfold SharedV3.handR SharedV3.handL at hoff
    unfold eRegion
    split_ifs at hoff <;> omega
  have hd:=W9Machine.DigAt_origWD h0 h1' hlo
  have he:eRegion (k.val+1)+off+1224-0x1020=SharedV3.topOtherOff k.val (SharedV3.physical k.val raw.val) := by
    unfold SharedV3.topOtherOff V3.regionOffset eRegion
    unfold SharedV3.handR SharedV3.handL at hsel ⊢
    split_ifs at hsel ⊢ <;> omega
  rw [he] at hd
  refine hd.frame hf (by unfold SharedV3.handR SharedV3.handL at hoff;unfold eRegion;split_ifs at hoff <;> omega) ?_ ?_
  all_goals
    intro hw
    simp only [SharedChild.writes, SharedChild.outputAddr, SharedChild.handAddr, SharedDispatch.layout_base] at hw
    unfold coordinateBase at hw
    unfold SharedV3.handR SharedV3.handL at hoff hsel
    unfold eRegion at hw
    split_ifs at hsel hw <;> omega

end ClaudeWCT.W9.Machine.Expand.SharedForestRun

namespace ClaudeWCT.W9.Machine.Expand.SharedForestRun
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest M)
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem next {image : Image} {w : W9Machine.WBytes} {index : Nat} {raw : Fin 9 → Fin 128}
    {ranks : Fin 9 → Fin 563} {initial u entry t : MachineState} {k : Fin 9} {prev : Digest×Digest}
    {ends : List Digest} {computed : Digest} (hu : Inv w index raw ranks initial k.val prev u)
    (hp : Chain.Post (SharedDispatch.layout image k) (SharedV3.viewWB 2904 w k.val u) index k (raw k)
      ((SharedDispatch.result k.val).toState u) ends entry)
    (ht : SharedChild.Post (SharedDispatch.layout image k) k (raw k) entry computed t) :
    Inv w index raw ranks initial (k.val+1)
      (SharedV3.orderPair k.val (SharedV3.physical k.val (raw k).val) computed
        (SharedV3.topOther w k.val (SharedV3.physical k.val (raw k).val))) t := by
  have hk:=k.isLt
  have hf:=core_frame_dispatch hp ht
  have hfg:Frame u t writes:=hf.mono (fun addr _ hw=>child_writes_bounds (image:=image) k (raw k) addr hw)
  have hother:∀off,(off=SharedV3.handL (k.val+1) ∨ off=SharedV3.handR (k.val+1)) → 
      (if SharedV3.direction k.val (SharedV3.physical k.val (raw k).val)=0
        then off=SharedV3.handR (k.val+1) else off=SharedV3.handL (k.val+1)) → 
      DigAt t (eRegion (k.val+1)+off) (SharedV3.topOther w k.val (SharedV3.physical k.val (raw k).val)) := by
    intro off hoff hsel
    have ho:off≤816 ∧ off%8=0 ∧ (k.val+1=9 → off=768 ∨ off=816) := by
      unfold SharedV3.handR SharedV3.handL at hoff;split_ifs at hoff <;> omega
    exact next_other w k (raw k) u t hf off hoff hsel
      (hu.coords (k.val+1) (by omega) (by omega) off (by omega) (by omega)
        (fun h=>by have:=ho.2.2 h;omega) (fun h=>by omega))
      (hu.coords (k.val+1) (by omega) (by omega) (off+8) (by omega) (by omega)
        (fun h=>by have:=ho.2.2 h;omega) (fun h=>by omega))
  refine ⟨by omega,?_,fields_frame hfg hu.fields,?_,?_,?_,?_,?_⟩
  · rw [ht.pc]
    fin_cases k <;> rfl
  · unfold SharedV3.orderPair
    by_cases hd:SharedV3.direction k.val (SharedV3.physical k.val (raw k).val)=0
    · rw [if_pos hd]
      have he:SharedChild.handAddr (SharedDispatch.layout image k) k (raw k)=eRegion (k.val+1)+SharedV3.handL (k.val+1):=by rw [hand_address,if_pos hd]
      rw [←he]
      exact ht.top
    · rw [if_neg hd]
      exact hother (SharedV3.handL (k.val+1)) (Or.inl rfl) (by rw [if_neg hd])
  · unfold SharedV3.orderPair
    by_cases hd:SharedV3.direction k.val (SharedV3.physical k.val (raw k).val)=0
    · rw [if_pos hd]
      exact hother (SharedV3.handR (k.val+1)) (Or.inr rfl) (by rw [if_pos hd])
    · rw [if_neg hd]
      have he:SharedChild.handAddr (SharedDispatch.layout image k) k (raw k)=eRegion (k.val+1)+SharedV3.handR (k.val+1):=by
        rw [hand_address,if_neg hd]
      rw [←he]
      exact ht.top
  · intro m hm1 hm9 off hoff h8 hv hh
    have h0:=hu.coords m (by omega) hm9 off hoff h8 hv (fun h=>by omega)
    unfold W9Machine.OrigWD at h0 ⊢
    rw [←h0]
    apply hf _ (by unfold eRegion;omega)
    intro hw
    simp only [SharedChild.writes, SharedChild.outputAddr, SharedChild.handAddr, SharedDispatch.layout_base] at hw
    unfold coordinateBase at hw
    have hmk:eRegion m+848≤eRegion k.val:=by unfold eRegion;omega
    rcases Nat.lt_or_ge (k.val+1) m with hgt|hle
    · have :eRegion m+848≤eRegion (k.val+1):=by unfold eRegion;omega
      unfold eRegion at *
      split_ifs at hw <;> omega
    · have hm':m=k.val+1:=by omega
      subst hm'
      have hn:=hh rfl
      unfold isHand SharedV3.isHand at hn
      unfold eRegion at *
      split_ifs at hn <;> split_ifs at hw <;> omega
  · intro addr ha hn
    exact (hfg addr ha hn).trans (hu.frame addr ha hn)
  · intro _
    rw [ht.keep .x8 (by decide), hp.child.baseReg, SharedDispatch.layout_base]
    simp only [coordinateBase]
    congr 2
    omega
end ClaudeWCT.W9.Machine.Expand.SharedForestRun

namespace ClaudeWCT.W9.Machine.Expand.SharedDispatch
open SigGolfCandidate.T3M SigGolfCandidate.Rv SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
 theorem code_of_driver {im : Image} (hc : CodeAt im (pcOf 45056) Images.expandSharedDriver)
    (k : Fin 9) : CodeAt im (pcOf (start k.val)) (words k.val) := by
  fin_cases k
  · exact SharedCounterHooks.code_slice (off:=1457) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1495) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1534) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1573) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1612) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1651) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1690) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1729) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1768) hc (by decide +kernel) (by decide +kernel)
theorem installed_code (k : Fin 9) : CodeAt Images.expandImage (pcOf (start k.val)) (words k.val) :=
  code_of_driver codeAt_expand_shared_driver k
end ClaudeWCT.W9.Machine.Expand.SharedDispatch

namespace ClaudeWCT.W9.Machine.Expand.SharedForestRun
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest M)
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem step_tbsim (image : Image) (sk : BitVec 256)
    (hwindow : (Frozen.image.code.drop 195584).take 59072=(image.code.drop 195584).take 59072)
    (hchecked : ∀k:Fin 9,symRun {} (SharedDispatch.words k.val) (pcOf (SharedDispatch.start k.val))
      (SharedDispatch.length k.val)=some (SharedDispatch.result k.val))
    (hcode : ∀k:Fin 9,CodeAt image (pcOf (SharedDispatch.start k.val)) (SharedDispatch.words k.val))
    (hslot : ∀rank:Fin 563,Frozen.layout.chainWord (N600.embed rank)=195584+64*rank.val)
    (hcore : ∀ (L:W9Machine.Layout) (k:Fin 9) (j:Fin 128) (rank:Fin 563),
      (Frozen.image.code.drop 195584).take 59072=(L.image.code.drop 195584).take 59072 → 
      (∀i,L.childWord i=(SharedLayout.layout k).childWord i) → 
      (∀r,L.chainWord r=Frozen.layout.chainWord r) → 
      ∀w index snapshot u padL padR,
      N600.Pre L (SharedV3.viewWB 2904 w k.val snapshot) index k j rank u → 
      DigAt snapshot (2904+V3.regionOffset k.val+672) padL → 
      DigAt snapshot (2904+V3.regionOffset k.val+160) padR → 
      TBSim L.image sk u (89+SharedChild.cost k j)
        (N600.program w index k j rank >>=fun ends=>SharedV3.childN w index k j ends padL padR)
        (SharedCore.Post L (SharedV3.viewWB 2904 w k.val snapshot) index k j u))
    (w : W9Machine.WBytes) (index : Nat) (hi : index<2^31) (raw : Fin 9 → Fin 128)
    (ranks : Fin 9 → Fin 563) (initial : MachineState) (k : Fin 9) (prev : Digest×Digest)
    (u : MachineState) (hu : Inv w index raw ranks initial k.val prev u) :
    TBSim image sk u 224 (SharedV3.coordinate w index k (raw k) (N600.embed (ranks k)) prev)
      (Inv w index raw ranks initial (k.val+1)) := by
  let L:=SharedDispatch.layout image k
  let v:=(SharedDispatch.result k.val).toState u
  have hs:=SharedDispatch.steps image k u (hchecked k) (hcode k)
    (by simpa only [pcWord,if_pos k.isLt] using hu.pc)
  have hc:=SharedDispatch.chain_pre image k u (SharedV3.viewWB 2904 w k.val u) index (raw k) (ranks k)
    hi hu.fields.index (hu.fields.raw k) (hu.fields.rank k) (hslot _) (witness_view hu) (fun h => by rw [hu.x8 (by omega), h])
  have hL:DigAt u (2904+V3.regionOffset k.val+672) prev.1 := by
    convert hu.prevL using 1 <;> unfold V3.regionOffset eRegion SharedV3.handL <;>
      have:=k.isLt <;> simp only [if_neg (by omega : k.val≠9)] <;> omega
  have hR:DigAt u (2904+V3.regionOffset k.val+160) prev.2 := by
    convert hu.prevR using 1 <;> unfold V3.regionOffset eRegion SharedV3.handR <;>
      have:=k.isLt <;> simp only [if_neg (by omega : k.val≠9)] <;> omega
  have hb:=hcore L k (raw k) (ranks k) hwindow (fun _=>rfl) (fun _=>rfl)
    w index u v prev.1 prev.2 hc hL hR
  -- Use the explicit existential postcondition to attach the hand-off pair.
  have hj' : TBSim image sk v ((89+SharedChild.cost k (raw k))+0)
      ((N600.program w index k (raw k) (ranks k) >>=fun ends=>
        SharedV3.childN w index k (raw k) ends prev.1 prev.2) >>=fun computed=>
        pure (SharedV3.orderPair k.val (SharedV3.physical k.val (raw k).val) computed
          (SharedV3.topOther w k.val (SharedV3.physical k.val (raw k).val))))
      (Inv w index raw ranks initial (k.val+1)) := by
    refine TBSim.bind hb ?_
    intro computed t ht
    obtain ⟨ends,entry,hp,ht⟩:=ht
    exact TBSim.pure (next hu hp ht)
  have hh:=TBSim.steps hs hj'
  have hlen:SharedDispatch.length k.val≤39:=by fin_cases k <;> decide
  have hcost:SharedChild.cost k (raw k)≤96:=by
    unfold SharedChild.cost SharedChild.spill
    split_ifs <;> omega
  simpa only [SharedV3.coordinate,N600.program,bind_assoc] using
    hh.mono (show SharedDispatch.length k.val+((89+SharedChild.cost k (raw k))+0)≤224 by omega)
      (fun _ _ h=>h)


 theorem forest_tbsim (image : Image) (sk : BitVec 256)
    (w : W9Machine.WBytes) (index : Nat) (raw : Fin 9 → Fin 128) (ranks : Fin 9 → Fin 563)
    (initial : MachineState)
    (hstep : ∀k:Fin 9,∀prev u,Inv w index raw ranks initial k.val prev u → 
      TBSim image sk u 224 (SharedV3.coordinate w index k (raw k) (N600.embed (ranks k)) prev)
        (Inv w index raw ranks initial (k.val+1)))
    (h0 : Inv w index raw ranks initial 0 (SharedV3.initialPair w) initial) :
    TBSim image sk initial 2016 (SharedV3.forest w index raw (fun k=>N600.embed (ranks k)))
      (fun pair t=>t.pc=pcOf 46862 ∧ DigAt t 2904 pair.1 ∧ DigAt t 2952 pair.2 ∧
        Frame initial t writes ∧ Fields index raw ranks t ∧ t.getReg .x8=BitVec.ofNat 64 2984) := by
  have he {α:Type} (f:α → Fin 9 → M α) (init:α) :
      (List.finRange 9).foldlM f init=(List.range' 0 9).foldlM
        (fun st n=>if h:n<9 then f st ⟨n,h⟩ else pure st) init := by
    rw [show List.finRange 9=[0,1,2,3,4,5,6,7,8] from rfl,
      show List.range' 0 9=[0,1,2,3,4,5,6,7,8] from rfl]
    simp only [List.foldlM_cons,List.foldlM_nil]
    rfl
  unfold SharedV3.forest
  rw [he]
  have hs:=TBSim.foldlM_range' (image:=image) (sk:=sk) 0 9
    (fun (prev:Digest×Digest) (n:Nat)=>if h:n<9 then
      SharedV3.coordinate w index ⟨n,h⟩ (raw ⟨n,h⟩) (N600.embed (ranks ⟨n,h⟩)) prev else pure prev)
    (SharedV3.initialPair w)
    (fun n prev u=>Inv w index raw ranks initial n prev u) 224
    (fun n hn prev u hu=>by simpa only [Nat.zero_add,dif_pos hn] using hstep ⟨n,hn⟩ prev u hu) h0
  exact hs.mono (by decide) (fun pair t ht=>⟨ht.pc,ht.prevL,ht.prevR,ht.frame,ht.fields,ht.x8 (by decide)⟩)

end ClaudeWCT.W9.Machine.Expand.SharedForestRun

namespace ClaudeWCT.W9.Machine.Expand.SharedForestRun
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest M)
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem forest_tbsim_of_bank (image : Image) (sk : BitVec 256)
    (hwindow : (Frozen.image.code.drop 195584).take 59072=(image.code.drop 195584).take 59072)
    (hcode : ∀k:Fin 9,CodeAt image (pcOf (SharedDispatch.start k.val)) (SharedDispatch.words k.val))
    (hslot : ∀rank:Fin 563,Frozen.layout.chainWord (N600.embed rank)=195584+64*rank.val)
    (hchain : ∀ (L : W9Machine.Layout),
      (Frozen.image.code.drop 195584).take 59072=(L.image.code.drop 195584).take 59072 →
      (∀ rank,L.chainWord rank=Frozen.layout.chainWord rank) →
      ∀ (rank:Fin 563) (w:W9Machine.WBytes) (index:Nat) (k:Fin 9) (j:Fin 128) (u:MachineState),
      N600.Pre L w index k j rank u →
      TBSim L.image sk u 89 (N600.program w index k j rank) (N600.Post L w index k j u))
    (w : W9Machine.WBytes) (index : Nat) (hi:index<2^31) (raw : Fin 9 → Fin 128)
    (ranks : Fin 9 → Fin 563) (initial : MachineState)
    (h0 : Inv w index raw ranks initial 0 (SharedV3.initialPair w) initial) :
    TBSim image sk initial 2016 (SharedV3.forest w index raw (fun k=>N600.embed (ranks k)))
      (fun pair t=>t.pc=pcOf 46862 ∧ DigAt t 2904 pair.1 ∧ DigAt t 2952 pair.2 ∧
        Frame initial t writes ∧ Fields index raw ranks t ∧ t.getReg .x8=BitVec.ofNat 64 2984) := by
  apply forest_tbsim image sk w index raw ranks initial ?_ h0
  intro k prev u hu
  apply step_tbsim image sk hwindow SharedDispatch.checked hcode hslot ?_ w index hi raw ranks initial k prev u hu
  intro L k j rank hw hc hcw w index snapshot u padL padR hpre hL hR
  exact SharedCore.core_tbsim L sk hw k j rank hc
    (fun w index u hu=>hchain L hw hcw rank w index k j u hu) w index snapshot u padL padR hpre hL hR
end ClaudeWCT.W9.Machine.Expand.SharedForestRun

namespace SigGolfCandidate.T3M.Expand.SharedLayers
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest route height chainCount target width maxDigit)
open SigGolfCandidate.T3M.Search (ENC EOUT DIGITS NODE NOUT csN4)
open SigGolfCandidate.T3M.Search.CanonicalExpand (CsArgs CsPre CsPost CsW csRegs csCost)
open SigGolfCandidate.T3M.Search.CanonicalExpandHooks (creditAddr CreditW hintFloor hintFloor_lt creditAddr_lt)
open ClaudeWCT
open SigGolfCandidate.T3M.Expand.BC
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
structure LInv (sig : WCT9.Signature) (hints : BitVec 16) (index n : Nat) (value : WCT9.LayerMsg) (s : MachineState) extends BC.LInv sig index n value s where
  hintsLt : hints.toNat<8000
  hintsMem : s.getMem (0x66000#64)=BitVec.ofNat 64 hints.toNat
  zt : SigGolfCandidate.T3M.Search.ZeroCap.ZtOK 354 s
  /-- T51: the packed top tables in the expand data at `0xFF9E00` (KCOPY's source, copied to `0xA0000`). -/
  t51src : SigGolfCandidate.T3M.Search.T51.T51TableW 0xFF9E00 s

def stage (sig : WCT9.Signature) (hints : BitVec 16) (index n : Nat) (value : WCT9.LayerMsg) :
    SigGolfCandidate.T3.M (Option (BitVec 32 × List Nat × Bool × WCT9.LayerMsg × Digest × List Nat)) := do
  let lay : Layer := Fin.ofNat 4 n
  let some (c,ds,low) ← WCT9.CanonicalPolicy.layerCounterSearchAt lay (hintFloor hints lay)
    (route index lay).2 (route index lay).1 value 0 (WCT9.searchLimit lay) | pure none
  let mv ← BC.recoverMsg sig index lay ds
  pure (some (c,ds,low,mv.1,mv.2.1,mv.2.2))
/-- T51: the top stage runs KCOPY (54522 -> 457, 1,190 steps) between the layer entry and the search. -/
def kcCost (lay : Layer) : Nat := if lay=0 then 1190 else 0
def stageCost (lay : Layer) : Nat := lK lay+kcCost lay+csCost lay+10+rlCost lay

def StagePost (im : Image) (s : MachineState) (sig : WCT9.Signature) (hints : BitVec 16) (index n : Nat) :
    Option (BitVec 32 × List Nat × Bool × WCT9.LayerMsg × Digest × List Nat) → MachineState → Prop
  | none,t => t.pc=pcOf 356 ∧ t.getReg .x5=1 ∧ t.getReg .x10=1 ∧ fetch im t=some (.base .ECALL)
  | some (c,ds,low,msg,v,nn),t =>
    let lay : Layer := Fin.ofNat 4 n
    LInv sig hints index n msg t ∧
    (∀ i<chainCount lay,DigAt t (lWC lay-64*i+48) (lval (WCT9.toT3Signature sig) lay i)) ∧
    (∀ j<height lay,DigAt t (lWM lay-64*j+sideOff (route index lay).1 j) (lpath (WCT9.toT3Signature sig) lay j)) ∧
    Frame s t (fun A=>CsW lay A ∨ A=lD lay ∨ BC.RlScratch A ∨ RlWit lay (route index lay).1 (lWC lay) (lWM lay) A) ∧
    RegsExcept s t lRegs ∧
    t.getMem (BitVec.ofNat 64 (creditAddr lay))=BitVec.ofNat 64 (WCT9.CanonicalPolicy.credit lay low ds) ∧
    ds.length=chainCount lay ∧ (∃ a,WCT9.CanonicalPolicy.decode lay a=some ds) ∧
    (lay=0 → TopBlkG (WCT9.toT3Signature sig) index lay v t) ∧
    t.getMem (BitVec.ofNat 64 (lD lay))=replaceWord32 (s.getMem (BitVec.ofNat 64 (lD lay))) (lk lay) (BitVec.ofNat 32 c.toNat) ∧
    hintFloor hints lay ≤ WCT9.CanonicalPolicy.credit lay low ds ∧
    (lay=0 → t.getMem (BitVec.ofNat 64 Search.FLAG)=BitVec.ofNat 64 (if low then 0 else 128)) ∧
    (lay=0 → NoncesAt t nn (route index lay).1)

theorem decode_digit_le {lay : Layer} {v : Digest} {ds : List Nat} (h : WCT9.CanonicalPolicy.decode lay v = some ds) :
    ∀ i<chainCount lay,ds.getD i 0 ≤ maxDigit lay i := by
  fin_cases lay <;> exact fun i hi=>T3.decode_digit_max h i hi

variable {im : Image} [SharedRecover.EntryCode im] [SharedRecover.Code im]
  [SharedRecover.BCBlocks.Code im] [SharedRecover.PackedBlocks.Code im] [KCopy.Code im] {sk : BitVec 256}
variable (hSearch : ∀ (A : CsArgs) (s0 : MachineState),CsPre 354 A s0 →
  TBSim im sk s0 (csCost A.lay)
    (WCT9.CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg 0 (WCT9.searchLimit A.lay))
    (CsPost im 354 A s0))
include hSearch in
theorem stage_good {sig : WCT9.Signature} {hints : BitVec 16} {index n : Nat} {value : WCT9.LayerMsg} {s : MachineState}
    (hn : n<4) (hI : LInv sig hints index (n+1) value s) :
    TBSim im sk s (stageCost (Fin.ofNat 4 n)) (stage sig hints index n value) (StagePost im s sig hints index n) := by
  set lay : Layer := Fin.ofNat 4 n with hlay
  have hlv : lay.val = n := fin_ofNat_val n hn
  have htab := ltable lay
  set tree := (route index lay).2 with htree_def
  set leaf := (route index lay).1 with hleaf_def
  have htree : tree < 2 ^ 32 := route_tree_lt index lay hI.hidx
  have hleaf : leaf < 2 ^ height lay := route_lt index lay
  have hH := height_le lay
  have hleaf32 : leaf < 2 ^ 32 := lt_of_lt_of_le hleaf (Nat.pow_le_pow_right (by norm_num) (by omega))
  obtain ⟨t0, s0', p0, x1', x8', x15', x26', x27', x17', x18', x9', r0, f0⟩ :=
    SharedRecover.lentry_spec (im := im) lay s (by rw [hI.pc]; rfl) index hI.hidx hI.idx
  -- Campaign T51: the top entry calls KCOPY (54522 -> 457, 1190 steps), which copies the packed T51 block
  -- 0xFF9E00 to RAM 0xA0000 (R6 pattern).
  obtain ⟨t1, s1, p1, r01, f01, tab1⟩ : ∃ t1, Steps im s (lK lay + kcCost lay) (lK lay + kcCost lay) t1 ∧
      t1.pc = pcOf 457 ∧ RegsExcept t0 t1 [.x6, .x28, .x29, .x30] ∧
      Frame t0 t1 (fun A => lay = 0 ∧ 0xA0000 ≤ A ∧ A < 0xA0768) ∧
      (lay = 0 → Search.T51.T51TableW 0xA0000 t1) := by
    by_cases h0 : lay = 0
    · have hp0 : t0.pc = pcOf 54522 := by rw [p0, if_pos h0]
      have hsrc : Search.T51.T51TableW 0xFF9E00 t0 :=
        hI.t51src.frame f0 (by decide) (by decide) (fun _ _ h => h)
      obtain ⟨u, su, pu, cu, ru, fu⟩ := KCopy.kcopy_spec (im := im) t0 hp0
      have hk : kcCost lay = 1190 := by unfold kcCost; rw [if_pos h0]
      exact ⟨u, (s0'.trans su).of_eq (by rw [hk]) (by rw [hk]), pu, ru,
        fu.mono (fun A _ h => ⟨h0, h⟩),
        fun _ => hsrc.of_copy (by decide) (by decide) (by decide) (by decide) cu⟩
    · have hk : kcCost lay = 0 := by unfold kcCost; rw [if_neg h0]
      exact ⟨t0, s0'.of_eq (by rw [hk, Nat.add_zero]) (by rw [hk, Nat.add_zero]), by rw [p0, if_neg h0],
        RegsExcept.refl _ _, Frame.refl _ _, fun h => absurd h h0⟩
  have tr : ∀ r, r ∉ [Reg.x6, .x28, .x29, .x30] → t1.getReg r = t0.getReg r := fun r h => r01.get h
  have x1 : t1.getReg .x1 = pcOf (lR1 lay) := (tr _ (by decide)).trans x1'
  have x8 := (tr _ (by decide)).trans x8'
  have x15 := (tr _ (by decide)).trans x15'
  have x26 := (tr _ (by decide)).trans x26'
  have x27 := (tr _ (by decide)).trans x27'
  have x17 := (tr _ (by decide)).trans x17'
  have x18 := (tr _ (by decide)).trans x18'
  have x9 := (tr _ (by decide)).trans x9'
  have r1 : RegsExcept s t1 ([Reg.x1, .x6, .x7, .x8, .x9, .x15, .x17, .x18, .x26, .x27, .x28] ++
      [.x6, .x28, .x29, .x30]) := r0.trans r01
  have f1 : Frame s t1 (fun A => lay = 0 ∧ 0xA0000 ≤ A ∧ A < 0xA0768) :=
    (f0.trans f01).mono (fun A _ h => by rcases h with h | h; exact h.elim; exact h)
  have g1 : ∀ A, A < 0xA0000 → t1.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) :=
    fun A hA => f1.get (by omega) (fun h => by omega)
  obtain ⟨x, hx, hx32⟩ := hI.c32
  have hcs : CsPre 354 ⟨lay, tree, leaf, value, lR1 lay, hintFloor hints lay, hints⟩ t1 :=
    { pc := p1, x1 := x1, x5 := by rw [r1.get (by decide)]; exact hI.x5, x8 := x8, x9 := x9, x18 := x18,
      x17 := by convert x17 using 2; clear_value lay; fin_cases lay <;> rfl,
      x26 := x26, x27 := x27, htree := htree, hleaf := hleaf32, hroute := route_routed index lay hI.hidx,
      x15 := Or.inr x15,
      m0 := by rw [g1 _ (by decide)]; exact hI.enc.1,
      m8 := by rw [g1 _ (by decide)]; exact hI.enc.2,
      c32 := ⟨x, hx, by rw [g1 _ (by decide)]; exact hx32⟩,
      z40 := by rw [g1 _ (by decide)]; exact hI.z.e40,
      r48 := by rw [g1 _ (by decide)]; exact (hI.right (by omega)).1,
      r56 := by rw [g1 _ (by decide)]; exact (hI.right (by omega)).2,
      table := hI.table.frame f1 (by intro i hi h; simp only [Search.TOP_DATA] at h; omega),
      cf := hI.cf.frame f1 (by intro i hi hi' h; simp only [Search.TOP_DATA] at h; omega),
      reward := hI.reward.frame f1 (by intro i hi hi' h; simp only [Search.TOP_DATA] at h; omega),
      zt := hI.zt.frame f1 (by
        intro r hr h; rw [show SigGolfCandidate.T3M.Search.ZeroCap.ZT 354 = 16747280 from rfl] at h; omega),
      floorLt := hintFloor_lt hints lay,
      floorTop := fun he => by change lay = 0 at he; change hintFloor hints lay = 14; rw [he]; rfl,
      hintsLt := hI.hintsLt, floorEq := rfl,
      floorMem := by rw [g1 _ (by decide)]; exact hI.hintsMem,
      t51table := tab1 }
  unfold stage
  change TBSim im sk s _ (_ >>= _) _
  refine (TBSim.steps s1 (TBSim.bind (W₂ := 10 + rlCost lay)
    (hSearch _ _ hcs) (fun r t2 h2 => ?_))).mono
    (by simp only [stageCost, ← hlay]; omega) (fun _ _ h => h)
  rcases r with _ | ⟨c, ds, low⟩
  · exact (TBSim.pure (Q := StagePost im s sig hints index n) (a := none) h2).mono (by omega) (fun _ _ h => h)
  · obtain ⟨p2, hc, x19, e32, ⟨v, hdec⟩, hlen, hdig, r2, f2, _, credit2, creditFloor2, flag2⟩ := h2
    dsimp only at p2 hc x19 e32 hdec hlen hdig
    change Frame t1 t2 (CsW lay) at f2
    obtain ⟨t3, s3, p3, x1', hD, x16, x23, x24, r3, f3⟩ := SharedRecover.lpost_spec (im := im) lay t2 p2 c.toNat x19
    have g3 : ∀ r, r ∉ [Reg.x1, .x6, .x7, .x8, .x9, .x15, .x17, .x18, .x26, .x27, .x28] ++ [.x6, .x28, .x29, .x30] →
        r ∉ csRegs →
        r ∉ [Reg.x1, .x16, .x23, .x24, .x28] → t3.getReg r = s.getReg r :=
      fun r h1 h2 h3 => by rw [r3.get h3, r2.get h2, r1.get h1]
    have g3' : ∀ r, r ∉ csRegs → r ∉ [Reg.x1, .x16, .x23, .x24, .x28] → t3.getReg r = t1.getReg r :=
      fun r h2 h3 => by rw [r3.get h3, r2.get h2]
    have m3 : ∀ A, A < 0xA0000 → ¬ CsW lay A → A ≠ lD lay → t3.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) :=
      fun A hA h1 h2 => by rw [f3.get (by omega) h2, f2.get (by omega) h1, g1 A hA]
    have hcsw : ∀ A, (A < 0x20260 ∨ (0x20460 ≤ A ∧ A < 0x66040)) → ¬ CsW lay A := by
      intro A hA h; unfold CsW Search.DigW CreditW creditAddr at h; simp only [ENC, EOUT, DIGITS, Search.FLAG] at h; omega
    have hrl : RlPre t3 (WCT9.toT3Signature sig) index lay ds (lP lay) (lWC lay) (lWM lay) (lR2 lay) := by
      refine ⟨p3, x1', by rw [g3 _ (by decide) (by decide) (by decide)]; exact hI.x5,
        by rw [g3' _ (by decide) (by decide)]; exact x8, by rw [g3' _ (by decide) (by decide)]; exact x9,
        by rw [g3' _ (by decide) (by decide)]; exact x18, by rw [g3' _ (by decide) (by decide)]; exact x15,
        by rw [g3' _ (by decide) (by decide)]; exact x26, by rw [g3' _ (by decide) (by decide)]; exact x27,
        x16, x23, x24, hI.hidx, htab.1, htab.2.1, htab.2.2.1, htab.2.2.2.1, htab.2.2.2.2.1, htab.2.2.2.2.2.1,
        htab.2.2.2.2.2.2.1, htab.2.2.2.2.2.2.2.1, ?_, decode_digit_le hdec, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi
        rw [Frame.getByte f3 (by simp only [DIGITS]; omega)
          (by have := htab.2.2.2.2.2.2.2.2.1; simp only [DIGITS]; omega)]
        exact hdig i hi
      · intro i hi
        have hv := (hI.sigl lay).1 i hi
        have hb := htab.2.1
        exact ⟨(m3 _ (by omega) (hcsw _ (by omega)) (by omega)).trans hv.1,
          (m3 _ (by omega) (hcsw _ (by omega)) (by omega)).trans hv.2⟩
      · intro j hj
        have hv := (hI.sigl lay).2 j hj
        have hb := htab.2.1
        exact ⟨(m3 _ (by omega) (hcsw _ (by omega)) (by omega)).trans hv.1,
          (m3 _ (by omega) (hcsw _ (by omega)) (by omega)).trans hv.2⟩
      all_goals
        first
          | (rw [m3 _ (by decide) (hcsw _ (by simp only [CHAIN, NODE, LEAFPK]; omega))
              (by have := htab.2.2.2.2.2.2.2.2.1; simp only [CHAIN, NODE, LEAFPK]; omega)]
             first | exact hI.z.c0 | exact hI.z.c8 | exact hI.z.n32 |
               exact hI.z.n40)
    refine (TBSim.steps s3 (TBSim.bind (W₂ := 0) (SharedRecover.recoverMsg_tbsim (im := im) (sk := sk) hrl)
      (fun mv t4 h4 => ?_))).mono (by omega) (fun _ _ h => h)
    obtain ⟨p4, e4, er4, form4, cv4, pv4, r4, f4, blk4, non4⟩ := h4
    have hfar4 : ∀ A, A < 0xA0000 → ¬ CsW lay A → A ≠ lD lay → (A < 0x2c48 ∨ 0x7000 ≤ A) → ¬ BC.RlScratch A →
        t4.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
      intro A hA h1 h2 h3 h4
      have hw : ¬ (BC.RlScratch A ∨ RlWit lay (route index lay).1 (lWC lay) (lWM lay) A) := by
        rintro (h | h)
        · exact h4 h
        · have := rlWit_range h; have := ltable_lo lay; omega
      rw [f4.get (by omega) hw, m3 A hA h1 h2]
    have hd8 := htab.2.2.2.2.2.2.2.2.1
    have hd0 := htab.2.2.2.2.2.2.2.2.2.1
    have ncs : ∀ A, (A < 0x20260 ∨ (0x20260 + 40 ≤ A ∧ A < EOUT) ∨ (0x20460 ≤ A ∧ A < 0x66040)) → ¬ CsW lay A := by
      intro A hA h; unfold CsW Search.DigW CreditW creditAddr at h; simp only [ENC, EOUT, DIGITS, Search.FLAG] at h hA; omega
    have nrl : ∀ A, ((A < CHAIN + 16 ∨ CHAIN + 112 ≤ A) ∧
        (A < NODE ∨ (NODE + 32 ≤ A ∧ A < NODE + 48) ∨ NOUT + 32 ≤ A) ∧ (A < LEAFPK ∨ LEAFPK + 896 ≤ A) ∧
        A ≠ ENC ∧ A ≠ ENC + 8 ∧ A ≠ ENC + 48 ∧ A ≠ ENC + 56 ∧ (A % 8 = 0) ∧ A < 0x66700) → ¬ BC.RlScratch A := by
      intro A hA h; unfold BC.RlScratch Expand.RlScratch at h; simp only [CHAIN, NODE, NOUT, LEAFPK, ENC] at h hA; omega
    have hI4base : BC.LInv sig index n mv.1 t4 := by
      have hx5 : t4.getReg .x5 = 0 := by
        rw [r4.get (by decide), g3 _ (by decide) (by decide) (by decide)]; exact hI.x5
      refine ⟨by rw [p4, hlay, lR2_eq n hn], by omega, hx5, hI.hidx, ?_, e4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hfar4 IDXV (by decide) (ncs _ (by decide)) (by simp only [IDXV, CHAIN, NODE, LEAFPK, ENC]; omega) (by decide) (nrl _ (by decide))]
        exact hI.idx
      · intro hn0
        exact er4 (by intro he; have hv := congrArg Fin.val he; change lay.val = 0 at hv; omega)
      · intro hn0
        exact form4 (Fin.ext (by simpa only [Fin.val_zero] using hlv.trans hn0))
      · refine ⟨c.toNat, by omega, ?_⟩
        have hw : ¬ (BC.RlScratch (ENC + 32) ∨ RlWit lay (route index lay).1 (lWC lay) (lWM lay) (ENC + 32)) := by
          rintro (h | h)
          · exact nrl _ (by decide) h
          · have h1 := rlWit_range h; have := ltable_lo lay; have := htab.2.2.2.2.2.2.2.1
            simp only [ENC] at h1; omega
        rw [f4.get (by decide) hw, f3.get (by decide) (by simp only [ENC]; omega), e32]
      · intro lay'
        have htab' := ltable lay'
        have hb := htab'.2.1
        have hb0 := htab'.1
        have hb8 := htab'.2.2.1
        refine ⟨fun i hi => ⟨?_, ?_⟩, fun j hj => ⟨?_, ?_⟩⟩
        · rw [hfar4 (lP lay' + 16 * i) (by omega) (ncs _ (by omega)) (by omega) (by omega)
            (nrl _ (by simp only [CHAIN, NODE, NOUT, LEAFPK, ENC]; omega))]
          exact ((hI.sigl lay').1 i hi).1
        · rw [hfar4 (lP lay' + 16 * i + 8) (by omega) (ncs _ (by omega)) (by omega) (by omega)
            (nrl _ (by simp only [CHAIN, NODE, NOUT, LEAFPK, ENC]; omega))]
          exact ((hI.sigl lay').1 i hi).2
        · rw [hfar4 (lP lay' + 16 * chainCount lay' + 16 * j) (by omega) (ncs _ (by omega)) (by omega) (by omega)
            (nrl _ (by simp only [CHAIN, NODE, NOUT, LEAFPK, ENC]; omega))]
          exact ((hI.sigl lay').2 j hj).1
        · rw [hfar4 (lP lay' + 16 * chainCount lay' + 16 * j + 8) (by omega) (ncs _ (by omega)) (by omega)
            (by omega) (nrl _ (by simp only [CHAIN, NODE, NOUT, LEAFPK, ENC]; omega))]
          exact ((hI.sigl lay').2 j hj).2
      · refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [hfar4 CHAIN (by decide) (ncs _ (by decide)) (by simp only [IDXV, CHAIN, NODE, LEAFPK, ENC]; omega) (by decide) (nrl _ (by decide))]
          exact hI.z.c0
        · rw [hfar4 (CHAIN + 8) (by decide) (ncs _ (by decide)) (by simp only [IDXV, CHAIN, NODE, LEAFPK, ENC]; omega) (by decide) (nrl _ (by decide))]
          exact hI.z.c8
        · rw [hfar4 (NODE + 32) (by decide) (ncs _ (by decide)) (by simp only [IDXV, CHAIN, NODE, LEAFPK, ENC]; omega) (by decide) (nrl _ (by decide))]
          exact hI.z.n32
        · rw [hfar4 (NODE + 40) (by decide) (ncs _ (by decide)) (by simp only [IDXV, CHAIN, NODE, LEAFPK, ENC]; omega) (by decide) (nrl _ (by decide))]
          exact hI.z.n40
        · rw [hfar4 (ENC + 40) (by decide) (ncs _ (by decide)) (by simp only [IDXV, CHAIN, NODE, LEAFPK, ENC]; omega) (by decide) (nrl _ (by decide))]
          exact hI.z.e40
      · apply hI.table.frame (((f1.trans f2).trans f3).trans f4)
        intro i hi h
        rcases h with ((h | h) | h) | h
        · simp only [Search.TOP_DATA] at h; omega
        · unfold CsW Search.DigW CreditW creditAddr at h
          simp only [Search.TOP_DATA, ENC, EOUT, DIGITS, Search.FLAG] at h
          omega
        · have := htab.2.2.2.2.2.2.2.2.1
          simp only [Search.TOP_DATA] at h
          omega
        · rcases h with h | h
          · unfold BC.RlScratch Expand.RlScratch at h
            simp only [Search.TOP_DATA, CHAIN, NODE, NOUT, LEAFPK, ENC] at h
            omega
          · have hh := rlWit_range h
            have hb := htab.2.2.2.2.2.2.2.1
            simp only [Search.TOP_DATA] at hh
            omega
      · apply hI.cf.frame (((f1.trans f2).trans f3).trans f4)
        intro i hi hi' h
        rcases h with ((h | h) | h) | h
        · simp only [Search.TOP_DATA] at h; omega
        · unfold CsW Search.DigW CreditW creditAddr at h
          simp only [Search.TOP_DATA, ENC, EOUT, DIGITS, Search.FLAG] at h
          omega
        · have := htab.2.2.2.2.2.2.2.2.1
          simp only [Search.TOP_DATA] at h
          omega
        · rcases h with h | h
          · unfold BC.RlScratch Expand.RlScratch at h
            simp only [Search.TOP_DATA, CHAIN, NODE, NOUT, LEAFPK, ENC] at h
            omega
          · have hh := rlWit_range h
            have hb := htab.2.2.2.2.2.2.2.1
            simp only [Search.TOP_DATA] at hh
            omega
      · apply hI.reward.frame (((f1.trans f2).trans f3).trans f4)
        intro i hi hi' h
        rcases h with ((h | h) | h) | h
        · simp only [Search.TOP_DATA] at h; omega
        · unfold CsW Search.DigW CreditW creditAddr at h
          simp only [Search.TOP_DATA, ENC, EOUT, DIGITS, Search.FLAG] at h
          omega
        · have := htab.2.2.2.2.2.2.2.2.1
          simp only [Search.TOP_DATA] at h
          omega
        · rcases h with h | h
          · unfold BC.RlScratch Expand.RlScratch at h
            simp only [Search.TOP_DATA, CHAIN, NODE, NOUT, LEAFPK, ENC] at h
            omega
          · have hh := rlWit_range h
            have hb := htab.2.2.2.2.2.2.2.1
            simp only [Search.TOP_DATA] at hh
            omega
    have frame4 : Frame s t4 (fun A => CsW lay A ∨ A=lD lay ∨ BC.RlScratch A ∨ RlWit lay (route index lay).1 (lWC lay) (lWM lay) A) :=
      (((f1.trans f2).trans f3).trans f4).mono (fun A _ h=>by
        rcases h with ((h|h)|h)|h|h
        · -- T51: KCOPY's window is part of `Expand.RlScratch`
          exact Or.inr (Or.inr (Or.inl (Or.inl (by
            unfold Expand.RlScratch; simp only [CHAIN, NODE, NOUT, LEAFPK, ENC]; omega))))
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h)))
    have hint4 : t4.getMem (0x66000#64)=BitVec.ofNat 64 hints.toNat := by
      rw [frame4.get (by decide) ?_]
      · exact hI.hintsMem
      · intro h
        rcases h with h|h|h|h
        · unfold CsW Search.DigW CreditW creditAddr at h
          have := lay.isLt
          simp only [ENC,EOUT,DIGITS,Search.FLAG] at h
          omega
        · have := ltable lay; omega
        · unfold BC.RlScratch Expand.RlScratch at h
          simp only [ENC,NODE,NOUT,CHAIN,LEAFPK] at h
          omega
        · have := rlWit_range h; have := ltable lay; omega
    have credit4 : t4.getMem (BitVec.ofNat 64 (creditAddr lay))=BitVec.ofNat 64 (WCT9.CanonicalPolicy.credit lay low ds) := by
      have ha := creditAddr_lt lay
      have hr : 0x66040≤creditAddr lay ∧ creditAddr lay<0x66060 := by unfold creditAddr;have:=lay.isLt;omega
      rw [f4.get ha ?_, f3.get ha ?_]
      · exact credit2
      · have := ltable lay; omega
      · rintro (h|h)
        · unfold BC.RlScratch Expand.RlScratch at h
          simp only [ENC,NODE,NOUT,CHAIN,LEAFPK] at h
          omega
        · have := rlWit_range h;have:=ltable lay;omega
    have flag4 : lay=0 → t4.getMem (BitVec.ofNat 64 Search.FLAG)=BitVec.ofNat 64 (if low then 0 else 128) := by
      intro hl0
      rw [f4.get (by decide) ?_, f3.get (by decide) ?_]
      · exact flag2 hl0
      · have := ltable lay; simp only [Search.FLAG]; omega
      · rintro (h|h)
        · unfold BC.RlScratch Expand.RlScratch at h
          simp only [ENC,NODE,NOUT,CHAIN,LEAFPK,Search.FLAG] at h
          omega
        · have hr := rlWit_range h;have:=ltable lay;simp only [Search.FLAG] at hr;omega
    have zt4 : SigGolfCandidate.T3M.Search.ZeroCap.ZtOK 354 t4 := by
      refine hI.zt.frame frame4 ?_
      intro r hr h
      rw [show SigGolfCandidate.T3M.Search.ZeroCap.ZT 354=16747280 from rfl] at h
      rcases h with h|h|h|h
      · unfold CsW Search.DigW CreditW creditAddr at h
        have := lay.isLt
        simp only [ENC,EOUT,DIGITS,Search.FLAG] at h
        omega
      · have := ltable lay; omega
      · unfold BC.RlScratch Expand.RlScratch at h
        simp only [ENC,NODE,NOUT,CHAIN,LEAFPK] at h
        omega
      · have := rlWit_range h; have := ltable lay; omega
    have t51src4 : Search.T51.T51TableW 0xFF9E00 t4 := by
      refine hI.t51src.frame frame4 (by decide) (by decide) ?_
      intro k hk h
      rcases h with h|h|h|h
      · unfold CsW Search.DigW CreditW creditAddr at h
        have := lay.isLt
        simp only [ENC,EOUT,DIGITS,Search.FLAG] at h
        omega
      · have := ltable lay; omega
      · unfold BC.RlScratch Expand.RlScratch at h
        simp only [ENC,NODE,NOUT,CHAIN,LEAFPK] at h
        omega
      · have := rlWit_range h; have := ltable lay; omega
    refine TBSim.pure ⟨⟨hI4base,hI.hintsLt,hint4,zt4,t51src4⟩,cv4,pv4,frame4,?_,credit4,hlen,⟨v,hdec⟩,blk4,?_,creditFloor2,flag4,non4⟩
    · exact (((r1.trans r2).trans r3).trans r4).mono (by decide)
    · have hw : ¬ (BC.RlScratch (lD lay) ∨ RlWit lay (route index lay).1 (lWC lay) (lWM lay) (lD lay)) := by
        rintro (h|h)
        · unfold BC.RlScratch Expand.RlScratch at h; simp only [CHAIN,NODE,NOUT,LEAFPK,ENC] at h;omega
        · exact counter_ne_wit lay lay _ h
      rw [f4.get (by omega) hw,hD,f2.get (by omega) (ncs _ (by omega)),g1 _ (by omega)]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp

end SigGolfCandidate.T3M.Expand.SharedLayers

namespace SigGolfCandidate.T3M.Expand.SharedLayers
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest route height chainCount)
open SigGolfCandidate.T3M.Search (ENC EOUT DIGITS NODE NOUT)
open SigGolfCandidate.T3M.Search.CanonicalExpand (CsArgs CsPre CsPost CsW csRegs csCost)
open SigGolfCandidate.T3M.Search.CanonicalExpandHooks (creditAddr CreditW hintFloor)
open ClaudeWCT
open SigGolfCandidate.T3M.Expand.BC
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
abbrev Recovered := SigGolfCandidate.Research.SharedForest.RecoveredLayers
def run (sig : WCT9.Signature) (hints : BitVec 16) (index : Nat) :
    Nat → WCT9.LayerMsg → Digest → List Nat → SigGolfCandidate.T3.M (Option Recovered)
  | 0,.forest root,v,nn => pure (some ⟨v,root,[],[],[],nn⟩)
  | 0,.pair _ _,_,_ => pure none
  | n+1,msg,_,_ => do
    let some (c,ds,low,msg',v',nn') ← stage sig hints index n msg | pure none
    let some previous ← run sig hints index n msg' v' nn' | pure none
    pure (some {previous with counters:=previous.counters++[c],digits:=previous.digits++[ds],lows:=previous.lows++[low]})
def cost : Nat → Nat
  | 0 => 0
  | n+1 => stageCost (Fin.ofNat 4 n)+cost n

def LW (index n : Nat) (A : Nat) : Prop :=
  Search.CsW A ∨ BC.RlScratch A ∨ ∃ lay : Layer,lay.val<n ∧
    (A=lD lay ∨ RlWit lay (route index lay).1 (lWC lay) (lWM lay) A ∨ (CreditW lay A ∨ A=Search.FLAG))
def Post (im : Image) (s : MachineState) (sig : WCT9.Signature) (hints : BitVec 16) (index n : Nat) (vin : Digest)
    (nin : List Nat) :
    Option Recovered → MachineState → Prop
  | none,t => t.pc=pcOf 356 ∧ t.getReg .x5=1 ∧ t.getReg .x10=1 ∧ fetch im t=some (.base .ECALL)
  | some r,t => t.pc=pcOf 342 ∧ t.getReg .x5=0 ∧ DigAt t ENC r.root ∧
    r.counters.length=n ∧ r.digits.length=n ∧
    (∀ lay : Layer,lay.val<n → LayerOut t sig index lay (r.counters.getD lay.val 0)) ∧
    (∀ lay : Layer,lay.val<n → t.getMem (BitVec.ofNat 64 (creditAddr lay))=
      BitVec.ofNat 64 (WCT9.CanonicalPolicy.credit lay (r.lows.getD lay.val true) (r.digits.getD lay.val []))) ∧
    HalfFrame s t n ∧ RegsExcept s t lRegs ∧ Frame s t (LW index n) ∧
    (n=0 → t=s ∧ r.foldedTop=vin) ∧
    (n≠0 → TopBlkG (WCT9.toT3Signature sig) index 0 r.foldedTop t) ∧
    t.getMem (0x66000#64)=BitVec.ofNat 64 hints.toNat ∧
    (∀ lay : Layer,lay.val<n → hintFloor hints lay ≤
      WCT9.CanonicalPolicy.credit lay (r.lows.getD lay.val true) (r.digits.getD lay.val [])) ∧
    r.lows.length=n ∧
    (n≠0 → t.getMem (BitVec.ofNat 64 Search.FLAG)=BitVec.ofNat 64 (if r.lows.getD 0 true then 0 else 128)) ∧
    (n=0 → r.nonces=nin) ∧
    (n≠0 → NoncesAt t r.nonces (route index 0).1)

theorem scoped_write {lay : Layer} {A : Nat} :
    CsW lay A ↔ Search.CsW A ∨ (CreditW lay A ∨ A=Search.FLAG) := by
  unfold CsW Search.CsW
  tauto

theorem stage_half {im : Image} {s t : MachineState} {sig : WCT9.Signature} {hints : BitVec 16}
    {index n : Nat} {c : BitVec 32} {ds : List Nat} {low : Bool} {msg : WCT9.LayerMsg} {v : Digest} {nn : List Nat}
    (h : StagePost im s sig hints index n (some (c,ds,low,msg,v,nn)) t) :
    ∀D k,(D=0x3ce8 ∨ D=0x4968 ∨ D=0x55a8 ∨ D=0x820 ∨ D=0x810 ∨ D=0x818) → k<2 →
      ¬(lD (Fin.ofNat 4 n)=D ∧ lk (Fin.ofNat 4 n)=k) →
      (t.getMem (BitVec.ofNat 64 D)).extractLsb' (32*k) 32=(s.getMem (BitVec.ofNat 64 D)).extractLsb' (32*k) 32 := by
  intro D k hD hk hn
  let lay : Layer:=Fin.ofNat 4 n
  obtain ⟨hi,cv,pv,ff,rr,credit,len,dec,blk,ctr,floor⟩:=h
  have ht:=ltable lay
  by_cases he : D=lD lay
  · rw [he,ctr,replaceWord32_other _ _ _ ht.2.2.2.2.2.2.2.2.2.2 hk (fun h=>hn ⟨he.symm,h⟩)]
  · rw [ff.get (by omega) ?_]
    rintro (hs|hd|hs|hw)
    · unfold CsW Search.DigW CreditW creditAddr at hs
      simp only [ENC,EOUT,DIGITS,Search.FLAG] at hs
      omega
    · exact he hd
    · unfold BC.RlScratch Expand.RlScratch at hs
      simp only [CHAIN,NODE,NOUT,LEAFPK,ENC] at hs
      omega
    · rcases hD with rfl|rfl|rfl|rfl|rfl|rfl
      · exact counter_ne_wit 0 lay _ hw
      · exact counter_ne_wit 1 lay _ hw
      · exact counter_ne_wit 2 lay _ hw
      · exact counter_ne_wit 3 lay _ hw
      · have:=rlWit_range hw;have:=ltable_lo (Fin.ofNat 4 n);omega
      · have:=rlWit_range hw;have:=ltable_lo (Fin.ofNat 4 n);omega

theorem old_wit_preserved {index n : Nat} {lay : Layer} (hn : n≤lay.val) {A : Nat}
    (hw : RlWit lay (route index lay).1 (lWC lay) (lWM lay) A) : ¬LW index n A := by
  have hr:=rlWit_range hw
  have ht:=ltable lay
  intro h
  rcases h with h|h|⟨lay',hl,h|h|h⟩
  · unfold Search.CsW Search.DigW at h; simp only [ENC,EOUT,DIGITS] at h;omega
  · unfold BC.RlScratch Expand.RlScratch at h;simp only [CHAIN,NODE,NOUT,LEAFPK,ENC] at h
    have:=ltable_lo lay;omega
  · rw [h] at hw;exact counter_ne_wit lay' lay _ hw
  · have hne : lay'≠lay := by intro he;subst he;omega
    have hr':=rlWit_range h
    rcases ltable_disj lay' lay hne with hd|hd <;> omega
  · unfold CreditW creditAddr at h;simp only [Search.FLAG] at h;omega

theorem old_credit_preserved {index n : Nat} {lay : Layer} (hn : n≤lay.val) : ¬LW index n (creditAddr lay) := by
  have ha : 0x66040≤creditAddr lay ∧ creditAddr lay<0x66060 := by unfold creditAddr;have:=lay.isLt;omega
  intro h
  rcases h with h|h|⟨lay',hl,h|h|h⟩
  · unfold Search.CsW Search.DigW at h;simp only [ENC,EOUT,DIGITS] at h;omega
  · unfold BC.RlScratch Expand.RlScratch at h;simp only [CHAIN,NODE,NOUT,LEAFPK,ENC] at h;omega
  · have:=ltable lay';omega
  · have:=rlWit_range h;have:=ltable lay';omega
  · unfold CreditW creditAddr at h;unfold creditAddr at ha;simp only [Search.FLAG] at h;omega
end SigGolfCandidate.T3M.Expand.SharedLayers

namespace SigGolfCandidate.T3M.Expand.SharedLayers
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest route height chainCount)
open SigGolfCandidate.T3M.Search (ENC)
open SigGolfCandidate.T3M.Search.CanonicalExpand (CsArgs CsPre CsPost CsW csRegs csCost)
open SigGolfCandidate.T3M.Search.CanonicalExpandHooks (creditAddr CreditW hintFloor creditAddr_lt)
open ClaudeWCT
open SigGolfCandidate.T3M.Expand.BC
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
variable {im : Image} [SharedRecover.EntryCode im] [SharedRecover.Code im]
  [SharedRecover.BCBlocks.Code im] [SharedRecover.PackedBlocks.Code im] [KCopy.Code im] {sk : BitVec 256}
variable (hSearch : ∀ (A : CsArgs) (s0 : MachineState),CsPre 354 A s0 →
  TBSim im sk s0 (csCost A.lay)
    (WCT9.CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg 0 (WCT9.searchLimit A.lay))
    (CsPost im 354 A s0))
include hSearch in
theorem run_good {sig : WCT9.Signature} {hints : BitVec 16} {index : Nat} :
    ∀n value vin nin s,LInv sig hints index n value s →
      TBSim im sk s (cost n) (run sig hints index n value vin nin) (Post im s sig hints index n vin nin)
  | 0,value,vin,nin,s,hI => by
    obtain ⟨root,rfl⟩:=hI.terminal rfl
    exact TBSim.pure ⟨hI.pc,hI.x5,hI.enc,rfl,rfl,
      (fun lay h=>False.elim (by omega)),(fun lay h=>False.elim (by omega)),
      (fun _ _ _ _ _=>rfl),RegsExcept.refl _ _,Frame.refl _ _,
      (fun _=>⟨rfl,rfl⟩),(fun h=>False.elim (h rfl)),hI.hintsMem,(fun lay h=>False.elim (by omega)),rfl,
      (fun h=>False.elim (h rfl)),(fun _=>rfl),(fun h=>False.elim (h rfl))⟩
  | n+1,value,vin,nin,s,hI => by
    have hn : n<4 := by have:=hI.hn;omega
    set lay : Layer:=Fin.ofNat 4 n with hlay
    have hlv : lay.val=n := fin_ofNat_val n hn
    have ht:=ltable lay
    unfold run
    refine (TBSim.bind (W₂:=cost n) (stage_good hSearch hn hI) (fun r t hstage=>?_)).mono (by rfl) (fun _ _ h=>h)
    rcases r with _|⟨c,ds,low,msg,v,nn⟩
    · exact (TBSim.pure (Q:=Post im s sig hints index (n+1) vin nin) (a:=none) hstage).mono (Nat.zero_le _) (fun _ _ h=>h)
    · have hs:=hstage
      simp only [StagePost,←hlay] at hstage
      obtain ⟨hIt,cv,pv,ff,rr,credit,len,dec,blk,ctr,floor,flagS,nonS⟩:=hstage
      refine (TBSim.bind (W₂:=0) (run_good n msg v nn t hIt) (fun r' u hpost=>?_)).mono (by omega) (fun _ _ h=>h)
      cases r' with
      | none => exact TBSim.pure hpost
      | some out =>
        obtain ⟨pc,x5,enc,clen,dlen,outs,credits,half,regs,frame,base,top,hintsEq,floors,llen,flagP,nbase,ntop⟩:=hpost
        have hD : lD lay=0x3ce8 ∨ lD lay=0x4968 ∨ lD lay=0x55a8 ∨ lD lay=0x820 ∨ lD lay=0x810 ∨ lD lay=0x818 := by
          clear_value lay;fin_cases lay <;> simp [lD]
        have hk:=ht.2.2.2.2.2.2.2.2.2.2
        refine TBSim.pure ⟨pc,x5,enc,by simpa using clen,
          by simpa using dlen,?_,?_,?_,(rr.trans regs).mono (by decide),?_,
          (fun h=>False.elim (by omega)),?_,hintsEq,?_,by simpa using llen,fun _=>?_,
          (fun h=>False.elim (by omega)),fun _=>?_⟩
        · intro lay' hl
          by_cases hlt : lay'.val<n
          · rw [List.getD_append _ _ _ _ (by omega)]
            exact outs lay' hlt
          · have he : lay'=lay := Fin.ext (by omega)
            subst lay'
            rw [List.getD_append_right _ _ _ _ (by omega),show lay.val-out.counters.length=0 by omega]
            simp only [List.getD_cons_zero]
            refine ⟨?_,?_,?_⟩
            · unfold BC.HalfAt
              rw [half (lD lay) (lk lay) hD hk (fun other hother ⟨hd,hk'⟩=>by
                have he:=lhalf_inj _ _ hd hk';rw [he] at hother;omega),ctr,replaceWord32_get _ _ hk]
              exact BitVec.eq_of_toNat_eq (by simp)
            · intro i hi
              exact (cv i hi).frame frame (by omega)
                (old_wit_preserved (by omega) (Or.inl ⟨i,hi,Or.inl rfl⟩))
                (old_wit_preserved (by omega) (Or.inl ⟨i,hi,Or.inr (by omega)⟩))
            · intro j hj
              have hside:=sideOff_le (route index lay).1 j
              exact (pv j hj).frame frame (by omega)
                (old_wit_preserved (by omega) (Or.inr ⟨j,hj,Or.inl rfl⟩))
                (old_wit_preserved (by omega) (Or.inr ⟨j,hj,Or.inr rfl⟩))
        · intro lay' hl
          by_cases hlt : lay'.val<n
          · rw [List.getD_append out.digits [ds] [] lay'.val (by omega),
              List.getD_append out.lows [low] true lay'.val (by omega)]
            exact credits lay' hlt
          · have he : lay'=lay := Fin.ext (by omega)
            subst lay'
            rw [List.getD_append_right out.digits [ds] [] lay.val (by omega),show lay.val-out.digits.length=0 by omega,
              List.getD_append_right out.lows [low] true lay.val (by omega),show lay.val-out.lows.length=0 by omega]
            simp only [List.getD_cons_zero]
            rw [frame.get (creditAddr_lt lay) (old_credit_preserved (by omega))]
            exact credit
        · intro D k hD' hk' hnot
          rw [half D k hD' hk' (fun other ho=>hnot other (by omega))]
          exact stage_half hs D k hD' hk' (hnot lay (by omega))
        · refine (ff.trans frame).mono (fun A hA h=>?_)
          rcases h with h|h
          · rcases h with h|h|h|h
            · rcases scoped_write.mp h with h|h
              · exact Or.inl h
              · exact Or.inr (Or.inr ⟨lay,by omega,Or.inr (Or.inr h)⟩)
            · exact Or.inr (Or.inr ⟨lay,by omega,Or.inl h⟩)
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr ⟨lay,by omega,Or.inr (Or.inl h)⟩)
          · rcases h with h|h|⟨other,ho,h⟩
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr ⟨other,by omega,h⟩)
        · intro _
          by_cases hn0 : n=0
          · obtain ⟨rfl,hfold⟩:=base hn0
            have hl0 : lay=0 := Fin.ext (by omega)
            rw [hfold]
            simpa only [hl0] using blk hl0
          · exact top hn0
        · intro lay' hl
          by_cases hlt : lay'.val<n
          · rw [List.getD_append out.digits [ds] [] lay'.val (by omega),
              List.getD_append out.lows [low] true lay'.val (by omega)]
            exact floors lay' hlt
          · have he : lay'=lay := Fin.ext (by omega)
            subst lay'
            rw [List.getD_append_right out.digits [ds] [] lay.val (by omega),show lay.val-out.digits.length=0 by omega,
              List.getD_append_right out.lows [low] true lay.val (by omega),show lay.val-out.lows.length=0 by omega]
            simp only [List.getD_cons_zero]
            exact floor
        · by_cases hn0 : n=0
          · obtain ⟨rfl,_⟩:=base hn0
            have hl0 : lay=0 := Fin.ext (by omega)
            subst hn0
            rw [List.getD_append_right out.lows [low] true 0 (by omega)]
            simpa [show out.lows.length=0 by omega] using flagS hl0
          · rw [List.getD_append out.lows [low] true 0 (by omega)]
            exact flagP hn0
        · by_cases hn0 : n=0
          · obtain ⟨rfl,_⟩:=base hn0
            have hl0 : lay=0 := Fin.ext (by omega)
            rw [nbase hn0]
            simpa only [hl0] using nonS hl0
          · exact ntop hn0
end SigGolfCandidate.T3M.Expand.SharedLayers

namespace SigGolfCandidate.T3M.Expand.SharedLayers
open OracleComp SigGolfCandidate.T3 ClaudeWCT
open SigGolfCandidate.Research
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem run_eq_recover (sig : SharedForest.Signature) (index : Nat) :
    ∀n,n<4 → ∀msg vin nin,
      run (SharedForest.mainSignature sig) sig.policyHints index (n+1) msg vin nin=
        SharedForest.recoverHintedLayers sig index (WCT9.topSib (SharedForest.mainSignature sig)) (n+1) msg := by
  intro n
  induction n with
  | zero =>
    intro hn msg vin nin
    conv_lhs => unfold run;unfold stage
    conv_rhs => unfold SharedForest.recoverHintedLayers
    simp only [bind_assoc]
    congr 1
    funext r
    rcases r with _|⟨c,ds,low⟩
    · rfl
    · simp only [BC.recoverMsg,Fin.ofNat_zero,ite_true,Nat.zero_eq,bind_assoc,pure_bind,run,List.nil_append]
      all_goals (congr 1; funext vn; rcases vn with ⟨f,nn⟩; rfl)
  | succ n ih =>
    intro hn msg vin nin
    have hl : (Fin.ofNat 4 (n+1) : Layer)≠0 := by
      intro he
      have hv:=congrArg Fin.val he
      change (n+1)%4=0 at hv
      rw [Nat.mod_eq_of_lt hn] at hv
      omega
    conv_lhs => unfold run;unfold stage
    conv_rhs => unfold SharedForest.recoverHintedLayers
    simp only [bind_assoc]
    congr 1
    funext r
    rcases r with _|⟨c,ds,low⟩
    · rfl
    · simp only [BC.recoverMsg,if_neg hl,Nat.succ_ne_zero,ite_false,bind_assoc,pure_bind]
      congr 1
      funext pair
      rw [ih (by omega)]
      rfl

theorem cost_four : cost 4≤3767000000 := by decide +kernel
end SigGolfCandidate.T3M.Expand.SharedLayers

namespace ClaudeWCT.W9.Machine.Expand.SharedValidate
open SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.Research
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- img-v6 machine policy check: pool 69, hints `484·f1 + 22·f2 + f3`; L1 residual < 56, L2 < 41, L3 < 22. -/
def policyCondition (hints : BitVec 16) (digits : List (List Nat)) (lows : List Bool) : Prop :=
  let r1:=69-CanonicalPolicy.credit 0 (lows.getD 0 true) (digits.getD 0 [])
  let r2:=r1-CanonicalPolicy.credit 1 (lows.getD 1 true) (digits.getD 1 [])
  let r3:=r2-CanonicalPolicy.credit 2 (lows.getD 2 true) (digits.getD 2 [])
  r1<56 ∧ r2<41 ∧ r3<22 ∧
    hints.toNat/484=CanonicalPolicy.threshold 1 r1 ∧
    hints.toNat/22%22=CanonicalPolicy.threshold 2 r2 ∧ hints.toNat%22=r3

theorem policyCondition_iff (hints : BitVec 16) (digits : List (List Nat)) (lows : List Bool)
    (hh : hints.toNat<8000) (hlen : digits.length=4)
    (hc0 : 14≤CanonicalPolicy.credit 0 (lows.getD 0 true) (digits.getD 0 []))
    (hc1 : SharedForest.hintFloor hints 1≤CanonicalPolicy.credit 1 (lows.getD 1 true) (digits.getD 1 []))
    (hc2 : SharedForest.hintFloor hints 2≤CanonicalPolicy.credit 2 (lows.getD 2 true) (digits.getD 2 [])) :
    policyCondition hints digits lows ↔ SharedForest.policyHintsValid hints digits lows=true := by
  have h1 : SharedForest.hintFloor hints 1=hints.toNat/484%22 := by
    simp only [SharedForest.hintFloor,show (1:Layer)≠0 by decide,ite_false]; rfl
  have h2 : SharedForest.hintFloor hints 2=hints.toNat/22%22 := by
    simp only [SharedForest.hintFloor,show (2:Layer)≠0 by decide,ite_false]; rfl
  have h3 : SharedForest.hintFloor hints 3=hints.toNat%22 := by
    simp only [SharedForest.hintFloor,show (3:Layer)≠0 by decide,ite_false]
    show hints.toNat/1%22=_
    rw [Nat.div_one]
  rw [h1] at hc1
  rw [h2] at hc2
  simp only [SharedForest.policyHintsValid,decide_eq_true_eq,CanonicalPolicy.nextResidual,
    CanonicalPolicy.totalCredit,hlen,true_and,and_true,h1,h2,h3]
  unfold policyCondition
  constructor
  · rintro ⟨hR1,hR2,hR3,he1,he2,he3⟩
    have hlt := CanonicalPolicy.lower_one_floor_lt ⟨_,hR1⟩
    simp only [Fin.val_mk] at hlt
    refine ⟨by omega,by omega,he2,?_⟩
    rw [CanonicalPolicy.lower_three_progress _ hR3]
    exact he3
  · rintro ⟨hH,he1,he2,he3⟩
    have hr1 : 69-CanonicalPolicy.credit 0 (lows.getD 0 true) (digits.getD 0 [])<56 := by omega
    have ht1 := (CanonicalPolicy.lower_one_progress ⟨_,hr1⟩).2
    simp only [Fin.val_mk] at ht1
    have hr2 : 69-CanonicalPolicy.credit 0 (lows.getD 0 true) (digits.getD 0 [])-
        CanonicalPolicy.credit 1 (lows.getD 1 true) (digits.getD 1 [])<41 := by
      rw [←he1] at ht1
      omega
    have ht2 := (CanonicalPolicy.lower_two_progress ⟨_,hr2⟩).2
    simp only [Fin.val_mk] at ht2
    have hr3 : 69-CanonicalPolicy.credit 0 (lows.getD 0 true) (digits.getD 0 [])-
        CanonicalPolicy.credit 1 (lows.getD 1 true) (digits.getD 1 [])-
        CanonicalPolicy.credit 2 (lows.getD 2 true) (digits.getD 2 [])<22 := by
      rw [←he2] at ht2
      omega
    refine ⟨hr1,hr2,hr3,by omega,he2,?_⟩
    rw [CanonicalPolicy.lower_three_progress _ hr3] at he3
    exact he3
end ClaudeWCT.W9.Machine.Expand.SharedValidate

namespace SigGolfCandidate.T3M.Expand.SharedLayers
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest)
open SigGolfCandidate.T3M.Search.CanonicalExpand (CsArgs CsPre CsPost csCost)
open SigGolfCandidate.Research
open ClaudeWCT
variable {im : Image} [SharedRecover.EntryCode im] [SharedRecover.Code im]
  [SharedRecover.BCBlocks.Code im] [SharedRecover.PackedBlocks.Code im] [KCopy.Code im] {sk : BitVec 256}
variable (hSearch : ∀ (A : CsArgs) (s0 : MachineState),CsPre 354 A s0 →
  TBSim im sk s0 (csCost A.lay)
    (WCT9.CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg 0 (WCT9.searchLimit A.lay))
    (CsPost im 354 A s0))
include hSearch in
theorem recover_good {sig : SharedForest.Signature} {index : Nat} {msg : WCT9.LayerMsg} {vin : Digest}
    {s : MachineState}
    (hI : LInv (SharedForest.mainSignature sig) sig.policyHints index 4 msg s) :
    TBSim im sk s 3767000000
      (SharedForest.recoverHintedLayers sig index (WCT9.topSib (SharedForest.mainSignature sig)) 4 msg)
      (Post im s (SharedForest.mainSignature sig) sig.policyHints index 4 vin []) := by
  rw [←run_eq_recover sig index 3 (by decide) msg vin []]
  exact (run_good hSearch 4 msg vin [] s hI).mono cost_four (fun _ _ h=>h)
end SigGolfCandidate.T3M.Expand.SharedLayers

namespace ClaudeWCT.W9.Machine.Expand.SharedValidate
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.WCT9
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option Elab.async false

def Tables (s : MachineState) : Prop :=
  ∀i,i<2160 → s.getByte (BitVec.ofNat 64 (16747408+i))=Images.expandSharedData.getD i 0

theorem data1 (r : Fin 56) : Images.expandSharedData.getD (2048+r.val) 0=
    BitVec.ofNat 8 (CanonicalPolicy.threshold 1 r.val) := by
  fin_cases r <;> decide +kernel
theorem data2 (r : Fin 41) : Images.expandSharedData.getD (2112+r.val) 0=
    BitVec.ofNat 8 (CanonicalPolicy.threshold 2 r.val) := by
  fin_cases r <;> decide +kernel
theorem threshold1_lt (r : Nat) (hr : r<56) : CanonicalPolicy.threshold 1 r<22 := by
  have h : ∀r:Fin 56,CanonicalPolicy.threshold 1 r.val<22 := by decide +kernel
  exact h ⟨r,hr⟩
theorem threshold2_lt (r : Nat) (hr : r<41) : CanonicalPolicy.threshold 2 r<22 := by
  have h : ∀r:Fin 41,CanonicalPolicy.threshold 2 r.val<22 := by decide +kernel
  exact h ⟨r,hr⟩
theorem Tables.first {s : MachineState} (h : Tables s) (r : Nat) (hr : r<56) :
    s.getByte (BitVec.ofNat 64 (16749456+r))=BitVec.ofNat 8 (CanonicalPolicy.threshold 1 r) := by
  have he:=h (2048+r) (by omega)
  rw [data1 ⟨r,hr⟩] at he
  rw [show 16747408+(2048+r)=16749456+r by omega] at he
  exact he
theorem Tables.second {s : MachineState} (h : Tables s) (r : Nat) (hr : r<41) :
    s.getByte (BitVec.ofNat 64 (16749520+r))=BitVec.ofNat 8 (CanonicalPolicy.threshold 2 r) := by
  have he:=h (2112+r) (by omega)
  rw [data2 ⟨r,hr⟩] at he
  rw [show 16747408+(2112+r)=16749520+r by omega] at he
  exact he
end ClaudeWCT.W9.Machine.Expand.SharedValidate

namespace SigGolfCandidate.T3M.Expand.SharedLayers
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
open SigGolfCandidate.Research ClaudeWCT
/-- Exact installed recovery entry, including all four dynamic canonical searches. -/
theorem installed_recover_good {sk : BitVec 256} {sig : SharedForest.Signature} {index : Nat}
    {msg : WCT9.LayerMsg} {vin : Digest} {s : MachineState}
    (hI : LInv (SharedForest.mainSignature sig) sig.policyHints index 4 msg s) :
    TBSim Images.expandImage sk s 3767000000
      (SharedForest.recoverHintedLayers sig index (WCT9.topSib (SharedForest.mainSignature sig)) 4 msg)
      (Post Images.expandImage s (SharedForest.mainSignature sig) sig.policyHints index 4 vin []) := by
  letI := SharedRecover.installed_entry
  letI := SharedRecover.installed_code
  letI := SharedRecover.installed_bc
  letI := SharedRecover.installed_packed
  letI := KCopy.installed_code
  exact recover_good (fun _ _ hp => Search.CanonicalExpand.counterSearch_good
    ClaudeWCT.W9.Machine.Expand.SharedSearchCode.installed_searchKernel hp) hI
end SigGolfCandidate.T3M.Expand.SharedLayers

namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_compact_chunks (c : Nat) (hc : compactChunkAllowed c) :
    CodeAt Images.expandImage (pcOf (256*c+compactChunkLo c))
      (((expChunks.getD (c-4) []).take (compactChunkLen c)).drop (compactChunkLo c)) := by
  rcases hc with rfl|rfl|rfl|hc|rfl|rfl|rfl|rfl
  · apply codeAt_expand_current_chunk <;> decide +kernel
  · apply codeAt_expand_current_chunk <;> decide +kernel
  · apply codeAt_expand_current_chunk <;> decide +kernel
  · obtain ⟨hlo,hhi⟩ := hc
    interval_cases c <;> apply codeAt_expand_current_chunk <;> decide +kernel
  · apply codeAt_expand_current_chunk <;> decide +kernel
  · apply codeAt_expand_current_chunk <;> decide +kernel
  · apply codeAt_expand_current_chunk <;> decide +kernel
  · apply codeAt_expand_current_chunk <;> decide +kernel
/-! Pairing stage 1: the pair copy block 48000 .. 48017 and the layout block 48100 .. 49225 in the installed image,
checked by ONE kernel walk over all their code windows (T51 round 2, VERA1). The image words past 44032 sit inside
literals under ~60 left-nested `++`, so each separate `codeAt_expand_last` check pays a traversal from 44032 (2-5 s);
`LayoutWalk.walk` pays it once for every window, and the `CodeAt` facts follow logically. -/
namespace LayoutWalk
/-- One pass over the image suffix `img` (it starts at word `pc`) along the code windows `(p, c)` in increasing `p`:
each window fits under `2 ^ 64` and matches the image. -/
def walk : List (BitVec 32) → Nat → List (Nat × List (BitVec 32)) → Bool
  | img, pc, (p, c) :: ws =>
      decide (pc ≤ p) && decide (0x1000 + 4 * p + 4 * c.length < 2 ^ 64) &&
        decide ((img.drop (p - pc)).take c.length = c) && walk (img.drop (p - pc)) p ws
  | _, _, [] => true
theorem walk_sound : ∀ (ws : List (Nat × List (BitVec 32))) (img : List (BitVec 32)) (pc : Nat),
    walk img pc ws = true → ∀ w ∈ ws, pc ≤ w.1 ∧ 0x1000 + 4 * w.1 + 4 * w.2.length < 2 ^ 64 ∧
      (img.drop (w.1 - pc)).take w.2.length = w.2
  | [], _, _, _, _, hw => absurd hw List.not_mem_nil
  | (p, c) :: ws, img, pc, h, w, hw => by
    simp only [walk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    rcases List.mem_cons.1 hw with rfl | hw
    · exact ⟨h1, h2, h3⟩
    · obtain ⟨i1, i2, i3⟩ := walk_sound ws _ p h4 w hw
      refine ⟨by omega, i2, ?_⟩
      rwa [List.drop_drop, show p - pc + (w.1 - p) = w.1 - pc by omega] at i3
theorem codeAt_of_walk {ws : List (Nat × List (BitVec 32))} {b : Nat} {code : List (BitVec 32)}
    (h : walk Images.expandCode_172 44032 ws = true) (hw : (b, code) ∈ ws) :
    CodeAt Images.expandImage (pcOf b) code := by
  obtain ⟨h1, h2, h3⟩ := walk_sound ws _ _ h _ hw
  exact SigGolfCandidate.T3M.codeAt_expand_last h1 h2 h3
theorem mem_seg {α : Type} (l : List α) (s n k : Nat) (h1 : s ≤ k) (h2 : k < s + n) (hk : k < l.length) :
    l[k] ∈ (l.drop s).take n := by
  rw [List.mem_iff_getElem]
  refine ⟨k - s, by simp; omega, ?_⟩
  simp only [List.getElem_take, List.getElem_drop]
  congr 1; omega
end LayoutWalk
private def layoutZ : List (Nat × List (BitVec 32)) := Layout.lbPc.zip Layout.lbCodes
private def layoutHd (g : Nat) : Nat × List (BitVec 32) := (Layout.lbHeadPc.getD g 0, Layout.lbHeadCodes.getD g [])
/-- All code windows of 48000 .. 49225 in pc order: the pair copy block, the layout top / clears, per group its head
`li a1,D` and its items (L3 0..42, L2 43..85, L1 86..128, top 129..179), the straight return tail. -/
private def layoutWins : List (Nat × List (BitVec 32)) :=
  [(48000, PairCopy.cPC0), (48001, PairCopy.cPCL), (48013, PairCopy.cPCT), (48100, Layout.cTop),
    (48112, Layout.cClr0), (48116, Layout.cClrL)] ++
  (layoutHd 0 :: (layoutZ.drop 0).take 43 ++ (layoutHd 1 :: (layoutZ.drop 43).take 43 ++
  (layoutHd 2 :: (layoutZ.drop 86).take 43 ++ (layoutHd 3 :: (layoutZ.drop 129).take 51 ++ [(49207, Layout.cRet)]))))
private theorem layout_walk : LayoutWalk.walk Images.expandCode_172 44032 layoutWins = true := by decide +kernel
private theorem pre_mem {w : Nat × List (BitVec 32)}
    (hw : w ∈ [(48000, PairCopy.cPC0), (48001, PairCopy.cPCL), (48013, PairCopy.cPCT), (48100, Layout.cTop),
      (48112, Layout.cClr0), (48116, Layout.cClrL)]) : w ∈ layoutWins := List.mem_append_left _ hw
private theorem item_mem (k : Nat) (hk : k < 180) : (Layout.pcK k, Layout.lbCodes.getD k []) ∈ layoutWins := by
  have h1 : Layout.lbPc.length = 180 := by decide +kernel
  have h2 : Layout.lbCodes.length = 180 := by decide +kernel
  have hz : k < layoutZ.length := by simp only [layoutZ, List.length_zip, h1, h2]; omega
  have he : (Layout.pcK k, Layout.lbCodes.getD k []) = layoutZ[k] := by
    simp only [layoutZ, List.getElem_zip, Layout.pcK, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega : k < Layout.lbPc.length),
      List.getElem?_eq_getElem (by omega : k < Layout.lbCodes.length), Option.getD_some]
  rw [he]
  refine List.mem_append_right _ ?_
  rcases (by omega : k < 43 ∨ (43 ≤ k ∧ k < 86) ∨ (86 ≤ k ∧ k < 129) ∨ 129 ≤ k) with h | h | h | h
  · exact List.mem_cons_of_mem _ (List.mem_append_left _ (LayoutWalk.mem_seg _ 0 43 k (by omega) (by omega) hz))
  · refine List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ ?_))
    exact List.mem_append_left _ (LayoutWalk.mem_seg _ 43 43 k (by omega) (by omega) hz)
  · refine List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ ?_))
    refine List.mem_append_right _ (List.mem_cons_of_mem _ ?_)
    exact List.mem_append_left _ (LayoutWalk.mem_seg _ 86 43 k (by omega) (by omega) hz)
  · refine List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ ?_))
    refine List.mem_append_right _ (List.mem_cons_of_mem _ ?_)
    refine List.mem_append_right _ (List.mem_cons_of_mem _ ?_)
    exact List.mem_append_left _ (LayoutWalk.mem_seg _ 129 51 k (by omega) (by omega) hz)
private theorem head_mem (g : Nat) (hg : g < 4) : layoutHd g ∈ layoutWins := by
  refine List.mem_append_right _ ?_
  interval_cases g
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self)
  · exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _
      List.mem_cons_self)))
  · exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _
      (List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self)))))
private theorem ret_mem : (49207, Layout.cRet) ∈ layoutWins := by
  refine List.mem_append_right _ ?_
  refine List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ ?_))
  refine List.mem_append_right _ (List.mem_cons_of_mem _ ?_)
  refine List.mem_append_right _ (List.mem_cons_of_mem _ ?_)
  exact List.mem_append_right _ List.mem_cons_self
/-- Pairing stage 1: the pair copy block 48000 .. 48017 in the installed image (beyond the reference chunks). -/
theorem installed_pairCopy : PairCopy.Code Images.expandImage :=
  ⟨LayoutWalk.codeAt_of_walk layout_walk (pre_mem (by simp)), LayoutWalk.codeAt_of_walk layout_walk (pre_mem (by simp)),
    LayoutWalk.codeAt_of_walk layout_walk (pre_mem (by simp))⟩
/-- Pairing stage 1: the layout block 48100 .. 49225 in the installed image. -/
theorem installed_layout_chunks : ∀ k < 180, 44032 ≤ Layout.pcK k ∧
    0x1000 + 4 * Layout.pcK k + 4 * (Layout.lbCodes.getD k []).length < 2 ^ 64 ∧
    (Images.expandCode_172.drop (Layout.pcK k - 44032)).take (Layout.lbCodes.getD k []).length =
      Layout.lbCodes.getD k [] := fun k hk => LayoutWalk.walk_sound _ _ _ layout_walk _ (item_mem k hk)
theorem installed_layout_heads : ∀ g < 4, 44032 ≤ Layout.lbHeadPc.getD g 0 ∧
    0x1000 + 4 * Layout.lbHeadPc.getD g 0 + 4 * (Layout.lbHeadCodes.getD g []).length < 2 ^ 64 ∧
    (Images.expandCode_172.drop (Layout.lbHeadPc.getD g 0 - 44032)).take (Layout.lbHeadCodes.getD g []).length =
      Layout.lbHeadCodes.getD g [] := fun g hg => LayoutWalk.walk_sound _ _ _ layout_walk _ (head_mem g hg)
theorem installed_layout : Layout.Code Images.expandImage := by
  refine ⟨?_, ?_, ?_, fun g hg => ?_, fun k hk => ?_, ?_⟩
  · exact LayoutWalk.codeAt_of_walk layout_walk (pre_mem (by simp))
  · exact LayoutWalk.codeAt_of_walk layout_walk (pre_mem (by simp))
  · exact LayoutWalk.codeAt_of_walk layout_walk (pre_mem (by simp))
  · obtain ⟨h1, h2, h3⟩ := installed_layout_heads g hg
    exact SigGolfCandidate.T3M.codeAt_expand_last h1 h2 h3
  · obtain ⟨h1, h2, h3⟩ := installed_layout_chunks k hk
    exact SigGolfCandidate.T3M.codeAt_expand_last h1 h2 h3
  · exact LayoutWalk.codeAt_of_walk layout_walk ret_mem
theorem installed_compact : CompactCodeAt Images.expandImage :=
  compactCode_of_chunks installed_compact_chunks installed_pairCopy installed_layout
end ClaudeWCT.W9.Machine.Expand

namespace ClaudeWCT.W9.Machine.Expand.SharedDigestCode
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.Sign.SharedDigest
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
theorem of_driver {im : Image} (hc : CodeAt im (pcOf 45056) Images.expandSharedDriver) :
    CodeAt im (pcOf (base true)) (words true) := by
  exact SharedCounterHooks.code_slice (off:=0) hc (by decide +kernel) (by decide +kernel)
theorem installed_code : CodeAt Images.expandImage (pcOf (base true)) (words true) := of_driver codeAt_expand_shared_driver
theorem installed_look : LookOK Images.expandImage (look true) := look_of_code true installed_code
end ClaudeWCT.W9.Machine.Expand.SharedDigestCode

namespace ClaudeWCT.W9.Machine.Expand.SharedForestRun
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

theorem initial_of_original (w : W9Machine.WBytes) (index : Nat)
    (raw : Fin 9→Fin 128) (ranks : Fin 9→Fin 563) (s : MachineState)
    (hp:s.pc=pcOf 46513) (hf:Fields index raw ranks s)
    (hw:∀A,2904≤A→A+8≤10616→A%8=0→A≠2928→W9Machine.OrigWD 1224 w s A) :
    Inv w index raw ranks s 0 (SharedV3.initialPair w) s := by
  refine ⟨by decide,hp,hf,?_,?_,?_,Frame.refl _ _,fun h=>absurd h (by decide)⟩
  · have h:=W9Machine.DigAt_origWD (A:=10440) (hw 10440 (by decide) (by decide) (by decide) (by decide))
      (hw 10448 (by decide) (by decide) (by decide) (by decide)) (by decide)
    have e1:eRegion 0+SharedV3.handL 0=10440:=by unfold eRegion SharedV3.handL; rfl
    have e2:10440+1224-0x1020=V3.regionOffset 0+672:=by unfold V3.regionOffset; rfl
    rw [e2] at h
    show DigAt s (eRegion 0+SharedV3.handL 0) (SharedV3.leafPad w 0)
    unfold SharedV3.leafPad V3.leafPad
    rw [e1]; exact h
  · have h:=W9Machine.DigAt_origWD (A:=9928) (hw 9928 (by decide) (by decide) (by decide) (by decide))
      (hw 9936 (by decide) (by decide) (by decide) (by decide)) (by decide)
    have e1:eRegion 0+SharedV3.handR 0=9928:=by unfold eRegion SharedV3.handR; rfl
    have e2:9928+1224-0x1020=V3.regionOffset 0+160:=by unfold V3.regionOffset; rfl
    rw [e2] at h
    show DigAt s (eRegion 0+SharedV3.handR 0) (W9Machine.wdig w (V3.regionOffset 0+160))
    rw [e1]; exact h
  · intro m hm hm9 off ho ha h9 hhand
    rcases (show m=9 ∨ m<9 by omega) with he|he
    · have hh:=h9 he
      subst he
      apply hw <;> unfold eRegion <;> omega
    · apply hw <;> unfold eRegion <;> omega
end ClaudeWCT.W9.Machine.Expand.SharedForestRun

namespace ClaudeWCT.W9.Machine.Expand.SharedDispatch
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Research
open ClaudeWCT.W9.Machine.Sign
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem raw_output (u : MachineState) (a : HashOutput) (ha : OutAt u NBUF a) (k : Fin 9) :
    rawRead k.val u=BitVec.ofNat 64 (SharedForest.rawChildFromOutput a k).val := by
  have hm:=ha (rawWord k.val) (by fin_cases k <;> decide)
  unfold rawRead
  rw[hm]
  convert W9Drv.SharedDispatch.child_field a k using 1 <;> fin_cases k <;> rfl

theorem rank_output (u : MachineState) (a : HashOutput) (ha : OutAt u NBUF a) (k : Fin 9)
    (hr : SharedForest.rawForestRank a k.val<563) :
    rankRead k.val u=BitVec.ofNat 64 (SharedForest.forestRank a k.val).val := by
  have hm:=ha (rankWord k.val) (by fin_cases k <;> decide)
  unfold rankRead
  rw[hm]
  have hv:(SharedForest.forestRank a k.val).val=SharedForest.rawForestRank a k.val:=
    Nat.mod_eq_of_lt hr
  rw[hv]
  convert W9Drv.SharedDispatch.rank_field a k using 1 <;> fin_cases k <;> rfl
end ClaudeWCT.W9.Machine.Expand.SharedDispatch

namespace ClaudeWCT.W9.Machine.Expand.SharedForestRun
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Research
open ClaudeWCT.W9.Machine.Sign

theorem fields_of_output (u : MachineState) (a : HashOutput) (index : Nat)
    (hi : u.getMem 0x66010=BitVec.ofNat 64 index) (ha : OutAt u NBUF a)
    (hr : ∀k:Fin 9,SharedForest.rawForestRank a k.val<563) :
    Fields index (SharedForest.rawChildFromOutput a) (fun k=>SharedForest.forestRank a k.val) u :=
  ⟨hi,SharedDispatch.raw_output u a ha,fun k=>SharedDispatch.rank_output u a ha k (hr k)⟩
end ClaudeWCT.W9.Machine.Expand.SharedForestRun

namespace ClaudeWCT.W9.Machine.Expand.SharedForestRun
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.Research.SharedForest ClaudeWCT.W9.T3M
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem installed_forest_good (sk : BitVec 256) (output : HashOutput)
    (witness : SigGolfCandidate.Research.SharedForest.Witness) (index : Nat) (hi : index<2^31)
    (s : MachineState)
    (h0 : Inv (Paired.witEnc output witness) index (rawChildFromOutput output)
      (fun k=>forestRank output k.val) s 0 (SharedV3.initialPair (Paired.witEnc output witness)) s) :
    TBSim Images.expandImage sk s 2016
      (recoverForest index (forestSelectionFromOutput output) (forestWordsFromOutput output) witness.signature.forest)
      (fun pair t=>t.pc=pcOf 46862 ∧ DigAt t 2904 pair.1 ∧ DigAt t 2952 pair.2 ∧
        Frame s t writes ∧ Fields index (rawChildFromOutput output) (fun k=>forestRank output k.val) t ∧
        t.getReg .x8=BitVec.ofNat 64 2984) := by
  have hwin : (Frozen.image.code.drop 195584).take 59072=(Images.expandImage.code.drop 195584).take 59072 := by
    rw [W9Machine.Frozen.image_eq]
    exact Images.expand_banks_eq_verify.symm
  have hm:=forest_tbsim_of_bank Images.expandImage sk hwin
    SharedDispatch.installed_code W9Drv.slot_entry
    (fun L hw hc rank w index k j u hu=>N600.tbsim_sharedBank L sk hw hc rank w index k j u hu)
    (Paired.witEnc output witness) index hi (rawChildFromOutput output)
    (fun k=>forestRank output k.val) s h0
  rw[show N600.embed=ClaudeWCT.WCT9.embed from N600.embed_eq_c1] at hm
  rw[W9Drv.SharedCanonical.forest_witEnc output witness index hi] at hm
  exact hm
end ClaudeWCT.W9.Machine.Expand.SharedForestRun
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_H2FrontA ====
section

/-! # H2 expander prologue: the compact signature, un-shifted in place

Word 0 jumps to the prologue (words 42777..42794): it keeps the 14 tail bytes (sig 5296..5311, read as two words;
bytes 5310/5311 are zero), moves sig [2928, 5296) up by 16 bytes (backwards, one word per step), stores the kept
words at sig 2928 (the top sibling with its two omitted bytes zero), clears its scratch registers and jumps to word
1. The machine is then exactly in the old expander's state after word 0, for the full-layout bytes
`sigB (sigDecC b)`. -/

section
namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Expand (ex_valid ex_ne bytesToWordLE_bytes_e bytes_length_e extractByte_bytesToWordLE_e extractByte_toNat_e word_ext_bytes_e)
open SigGolfCandidate.T3 (Digest HashOutput M)
open SigGolfCandidate.T3M.Search (DIG)
open ClaudeWCT.W9.T3M (sigDig sigDec sigDigests)
set_option linter.unusedSimpArgs false
set_option maxRecDepth 10000

def frontTail : List (BitVec 32) := SigGolfCandidate.T3M.Expand.seg_0.drop 1

sym_block h2_front := symRun { noAlias := true } frontTail (pcOf 1) 200

theorem ofNat_sub8 (X : Nat) (hX : 8 ≤ X) (hX' : X < 2 ^ 64) :
    BitVec.ofNat 64 X + BitVec.ofNat 64 (2 ^ 64 - 8) = BitVec.ofNat 64 (X - 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have h16 : 16 ≤ 2 ^ 64 := le_trans (by norm_num : (16 : Nat) ≤ 2 ^ 4) (Nat.pow_le_pow_right (by norm_num) (by norm_num))
  generalize (2 : Nat) ^ 64 = P at *
  rw [Nat.mod_eq_of_lt hX', Nat.mod_eq_of_lt (show P - 8 < P by omega), Nat.mod_eq_of_lt (show X - 8 < P by omega),
    show X + (P - 8) = (X - 8) + P by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (show X - 8 < P by omega)]

/-- r3w: unconditional form of a 64-bit subtraction of `ofNat`s (the sixth block stores at `-48(t3)`, `-40(t3)`). -/
theorem ofNat_sub_ofNat_u (x y : Nat) :
    BitVec.ofNat 64 x - BitVec.ofNat 64 y = BitVec.ofNat 64 (x + (18446744073709551616 - y % 18446744073709551616)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-! ### The move loop -/

/-! ### The un-shifted memory is the old expander's initial memory for `sigFull b` -/


end ClaudeWCT.W9.Machine.Expand
end

/-! T51: #938's compact-layout adapter (words 44096.., the second decode pass) is dead -- word 0 jumps to DEC
(Expand_PrePassInit), which writes the inflated slot layout directly; its lemmas (AdapterCodeAt .. front_readout,
installed_adapter_codeAt) are deleted. Only the hint address is kept. -/
namespace ClaudeWCT.W9.Machine.Expand.SharedCompact
/-- The policy-hint word (`0x66000`), written by DEC. -/
def policyAddress : Nat := 417792
end ClaudeWCT.W9.Machine.Expand.SharedCompact

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
abbrev destination (region slot child : Nat) : Nat :=
  region + 16 * slot + 48 * (1 - child % 2)

def pathCode0 : List (BitVec 32) := [0x4e1e13,0x8e0e33,0x85313,0x137313,0x100393,0x40638333,0x3000393,0x2730333,0x6e0e33,0x608b303,0x688b383,0x6e3023,0x7e3423]
sym_block path0 := symRun { noAlias := true } pathCode0 (pcOf 45307) 100
theorem path0_obligs (s : MachineState) (region source child slot : Nat)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region % 8 = 0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128) (hb : slot < 53)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 region)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 slot) :
    Oblig.all s path0.res.st.obl := by
  rcases Nat.mod_two_eq_zero_or_one child with hbit | hbit
  all_goals
    simp only [path0.res]
    t3n [h8,h16,h17,h28,ofNat_and1,hbit]
    norm_num
    omega

def pathCode1 : List (BitVec 32) := [0x4e1e13,0x8e0e33,0x185313,0x137313,0x100393,0x40638333,0x3000393,0x2730333,0x6e0e33,0x708b303,0x788b383,0x6e3023,0x7e3423]
sym_block path1 := symRun { noAlias := true } pathCode1 (pcOf 45321) 100
theorem path1_obligs (s : MachineState) (region source child slot : Nat)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region % 8 = 0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128) (hb : slot < 53)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 region)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 slot) :
    Oblig.all s path1.res.st.obl := by
  have hj64 : child < 2^64 := by omega
  rcases Nat.mod_two_eq_zero_or_one (child / 2) with hbit | hbit
  all_goals
    simp only [path1.res]
    t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64]
    norm_num
    omega

def pathCode2 : List (BitVec 32) := [0x4e1e13,0x8e0e33,0x285313,0x137313,0x100393,0x40638333,0x3000393,0x2730333,0x6e0e33,0x808b303,0x888b383,0x6e3023,0x7e3423]
sym_block path2 := symRun { noAlias := true } pathCode2 (pcOf 45335) 100
theorem path2_obligs (s : MachineState) (region source child slot : Nat)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region % 8 = 0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128) (hb : slot < 53)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 region)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 slot) :
    Oblig.all s path2.res.st.obl := by
  have hj64 : child < 2^64 := by omega
  rcases Nat.mod_two_eq_zero_or_one (child / 4) with hbit | hbit
  all_goals
    simp only [path2.res]
    t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64]
    norm_num
    omega

def pathCode3 : List (BitVec 32) := [0x4e1e13,0x8e0e33,0x385313,0x137313,0x100393,0x40638333,0x3000393,0x2730333,0x6e0e33,0x908b303,0x988b383,0x6e3023,0x7e3423]
sym_block path3 := symRun { noAlias := true } pathCode3 (pcOf 45349) 100
theorem path3_obligs (s : MachineState) (region source child slot : Nat)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region % 8 = 0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128) (hb : slot < 53)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 region)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 slot) :
    Oblig.all s path3.res.st.obl := by
  have hj64 : child < 2^64 := by omega
  rcases Nat.mod_two_eq_zero_or_one (child / 8) with hbit | hbit
  all_goals
    simp only [path3.res]
    t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64]
    norm_num
    omega

def pathCode4 : List (BitVec 32) := [0x4e1e13,0x8e0e33,0x485313,0x137313,0x100393,0x40638333,0x3000393,0x2730333,0x6e0e33,0xa08b303,0xa88b383,0x6e3023,0x7e3423]
sym_block path4 := symRun { noAlias := true } pathCode4 (pcOf 45363) 100
theorem path4_obligs (s : MachineState) (region source child slot : Nat)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region % 8 = 0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128) (hb : slot < 53)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 region)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 slot) :
    Oblig.all s path4.res.st.obl := by
  have hj64 : child < 2^64 := by omega
  rcases Nat.mod_two_eq_zero_or_one (child / 16) with hbit | hbit
  all_goals
    simp only [path4.res]
    t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64]
    norm_num
    omega

end ClaudeWCT.W9.Machine.Expand.SharedScatter


namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
sym_block rebased0_0 := symRun { noAlias := true } pathCode0 (pcOf 45307) 100
sym_block rebased0_1 := symRun { noAlias := true } pathCode0 (pcOf 45441) 100
sym_block rebased0_2 := symRun { noAlias := true } pathCode0 (pcOf 45584) 100
sym_block rebased0_3 := symRun { noAlias := true } pathCode0 (pcOf 45718) 100
sym_block rebased0_4 := symRun { noAlias := true } pathCode0 (pcOf 45861) 100
sym_block rebased0_5 := symRun { noAlias := true } pathCode0 (pcOf 45995) 100
sym_block rebased0_6 := symRun { noAlias := true } pathCode0 (pcOf 46138) 100
sym_block rebased0_7 := symRun { noAlias := true } pathCode0 (pcOf 46272) 100
sym_block rebased0_8 := symRun { noAlias := true } pathCode0 (pcOf 46417) 100
theorem run_path0 {b : Nat} (hb : b = 45307 ∨ b = 45441 ∨ b = 45584 ∨ b = 45718 ∨ b = 45861 ∨ b = 45995 ∨ b = 46138 ∨ b = 46272 ∨ b = 46417) :
    symRun { noAlias := true } pathCode0 (pcOf b) 100 =
      some ⟨path0.res.st, .c (pcOf (b + 13)), path0.res.stop, path0.res.steps, path0.res.cycles⟩ := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rebased0_0.trans (congrArg some (by kernel_rfl))
  · exact rebased0_1.trans (congrArg some (by kernel_rfl))
  · exact rebased0_2.trans (congrArg some (by kernel_rfl))
  · exact rebased0_3.trans (congrArg some (by kernel_rfl))
  · exact rebased0_4.trans (congrArg some (by kernel_rfl))
  · exact rebased0_5.trans (congrArg some (by kernel_rfl))
  · exact rebased0_6.trans (congrArg some (by kernel_rfl))
  · exact rebased0_7.trans (congrArg some (by kernel_rfl))
  · exact rebased0_8.trans (congrArg some (by kernel_rfl))
theorem path0_steps_rebased {im : Image} {b : Nat} (hbpc : b = 45307 ∨ b = 45441 ∨ b = 45584 ∨ b = 45718 ∨ b = 45861 ∨ b = 45995 ∨ b = 46138 ∨ b = 46272 ∨ b = 46417) (hc : CodeAt im (pcOf b) pathCode0)
    (s : MachineState) (hp : s.pc = pcOf b) (region source child slot : Nat)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region % 8 = 0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128) (hb : slot < 53)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 region)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 slot) :
    ∃ t, Steps im s 13 16 t ∧ t.pc = pcOf (b + 13) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot child)) =
        s.getMem (BitVec.ofNat 64 (source + 96)) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot child + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 104)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = destination region slot child ∨
        A = destination region slot child + 8) := by
  have ho := path0_obligs s region source child slot hr0 hr1 hra hs0 hs1 hsa hj hb h8 h16 h17 h28
  refine ⟨_, symRun_sound (run_path0 hbpc) hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [path0.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one child with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path0.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,destination]
      norm_num [ofNat_and1,hbit,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)
  · rcases Nat.mod_two_eq_zero_or_one child with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path0.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,destination]
      norm_num [ofNat_and1,hbit,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)
  · intro r hr; simp at hr; cases r <;> simp_all [path0.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one child with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path0.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,destination]
      simp only [destination,hbit] at hn
      norm_num [ofNat_and1,hbit,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)

sym_block rebased1_0 := symRun { noAlias := true } pathCode1 (pcOf 45321) 100
sym_block rebased1_1 := symRun { noAlias := true } pathCode1 (pcOf 45455) 100
sym_block rebased1_2 := symRun { noAlias := true } pathCode1 (pcOf 45598) 100
sym_block rebased1_3 := symRun { noAlias := true } pathCode1 (pcOf 45732) 100
sym_block rebased1_4 := symRun { noAlias := true } pathCode1 (pcOf 45875) 100
sym_block rebased1_5 := symRun { noAlias := true } pathCode1 (pcOf 46009) 100
sym_block rebased1_6 := symRun { noAlias := true } pathCode1 (pcOf 46152) 100
sym_block rebased1_7 := symRun { noAlias := true } pathCode1 (pcOf 46286) 100
sym_block rebased1_8 := symRun { noAlias := true } pathCode1 (pcOf 46431) 100
theorem run_path1 {b : Nat} (hb : b = 45321 ∨ b = 45455 ∨ b = 45598 ∨ b = 45732 ∨ b = 45875 ∨ b = 46009 ∨ b = 46152 ∨ b = 46286 ∨ b = 46431) :
    symRun { noAlias := true } pathCode1 (pcOf b) 100 =
      some ⟨path1.res.st, .c (pcOf (b + 13)), path1.res.stop, path1.res.steps, path1.res.cycles⟩ := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rebased1_0.trans (congrArg some (by kernel_rfl))
  · exact rebased1_1.trans (congrArg some (by kernel_rfl))
  · exact rebased1_2.trans (congrArg some (by kernel_rfl))
  · exact rebased1_3.trans (congrArg some (by kernel_rfl))
  · exact rebased1_4.trans (congrArg some (by kernel_rfl))
  · exact rebased1_5.trans (congrArg some (by kernel_rfl))
  · exact rebased1_6.trans (congrArg some (by kernel_rfl))
  · exact rebased1_7.trans (congrArg some (by kernel_rfl))
  · exact rebased1_8.trans (congrArg some (by kernel_rfl))
theorem path1_steps_rebased {im : Image} {b : Nat} (hbpc : b = 45321 ∨ b = 45455 ∨ b = 45598 ∨ b = 45732 ∨ b = 45875 ∨ b = 46009 ∨ b = 46152 ∨ b = 46286 ∨ b = 46431) (hc : CodeAt im (pcOf b) pathCode1)
    (s : MachineState) (hp : s.pc = pcOf b) (region source child slot : Nat)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region % 8 = 0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128) (hb : slot < 53)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 region)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 slot) :
    ∃ t, Steps im s 13 16 t ∧ t.pc = pcOf (b + 13) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child / 2))) =
        s.getMem (BitVec.ofNat 64 (source + 112)) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child / 2) + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 120)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = destination region slot (child / 2) ∨
        A = destination region slot (child / 2) + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := path1_obligs s region source child slot hr0 hr1 hra hs0 hs1 hsa hj hb h8 h16 h17 h28
  refine ⟨_, symRun_sound (run_path1 hbpc) hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [path1.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 2) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path1.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)
  · rcases Nat.mod_two_eq_zero_or_one (child / 2) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path1.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)
  · intro r hr; simp at hr; cases r <;> simp_all [path1.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 2) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path1.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      simp only [destination,hbit] at hn
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)

sym_block rebased2_0 := symRun { noAlias := true } pathCode2 (pcOf 45335) 100
sym_block rebased2_1 := symRun { noAlias := true } pathCode2 (pcOf 45469) 100
sym_block rebased2_2 := symRun { noAlias := true } pathCode2 (pcOf 45612) 100
sym_block rebased2_3 := symRun { noAlias := true } pathCode2 (pcOf 45746) 100
sym_block rebased2_4 := symRun { noAlias := true } pathCode2 (pcOf 45889) 100
sym_block rebased2_5 := symRun { noAlias := true } pathCode2 (pcOf 46023) 100
sym_block rebased2_6 := symRun { noAlias := true } pathCode2 (pcOf 46166) 100
sym_block rebased2_7 := symRun { noAlias := true } pathCode2 (pcOf 46300) 100
sym_block rebased2_8 := symRun { noAlias := true } pathCode2 (pcOf 46445) 100
theorem run_path2 {b : Nat} (hb : b = 45335 ∨ b = 45469 ∨ b = 45612 ∨ b = 45746 ∨ b = 45889 ∨ b = 46023 ∨ b = 46166 ∨ b = 46300 ∨ b = 46445) :
    symRun { noAlias := true } pathCode2 (pcOf b) 100 =
      some ⟨path2.res.st, .c (pcOf (b + 13)), path2.res.stop, path2.res.steps, path2.res.cycles⟩ := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rebased2_0.trans (congrArg some (by kernel_rfl))
  · exact rebased2_1.trans (congrArg some (by kernel_rfl))
  · exact rebased2_2.trans (congrArg some (by kernel_rfl))
  · exact rebased2_3.trans (congrArg some (by kernel_rfl))
  · exact rebased2_4.trans (congrArg some (by kernel_rfl))
  · exact rebased2_5.trans (congrArg some (by kernel_rfl))
  · exact rebased2_6.trans (congrArg some (by kernel_rfl))
  · exact rebased2_7.trans (congrArg some (by kernel_rfl))
  · exact rebased2_8.trans (congrArg some (by kernel_rfl))
theorem path2_steps_rebased {im : Image} {b : Nat} (hbpc : b = 45335 ∨ b = 45469 ∨ b = 45612 ∨ b = 45746 ∨ b = 45889 ∨ b = 46023 ∨ b = 46166 ∨ b = 46300 ∨ b = 46445) (hc : CodeAt im (pcOf b) pathCode2)
    (s : MachineState) (hp : s.pc = pcOf b) (region source child slot : Nat)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region % 8 = 0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128) (hb : slot < 53)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 region)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 slot) :
    ∃ t, Steps im s 13 16 t ∧ t.pc = pcOf (b + 13) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child / 4))) =
        s.getMem (BitVec.ofNat 64 (source + 128)) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child / 4) + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 136)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = destination region slot (child / 4) ∨
        A = destination region slot (child / 4) + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := path2_obligs s region source child slot hr0 hr1 hra hs0 hs1 hsa hj hb h8 h16 h17 h28
  refine ⟨_, symRun_sound (run_path2 hbpc) hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [path2.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 4) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path2.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)
  · rcases Nat.mod_two_eq_zero_or_one (child / 4) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path2.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)
  · intro r hr; simp at hr; cases r <;> simp_all [path2.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 4) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path2.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      simp only [destination,hbit] at hn
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)

sym_block rebased3_0 := symRun { noAlias := true } pathCode3 (pcOf 45349) 100
sym_block rebased3_1 := symRun { noAlias := true } pathCode3 (pcOf 45483) 100
sym_block rebased3_2 := symRun { noAlias := true } pathCode3 (pcOf 45626) 100
sym_block rebased3_3 := symRun { noAlias := true } pathCode3 (pcOf 45760) 100
sym_block rebased3_4 := symRun { noAlias := true } pathCode3 (pcOf 45903) 100
sym_block rebased3_5 := symRun { noAlias := true } pathCode3 (pcOf 46037) 100
sym_block rebased3_6 := symRun { noAlias := true } pathCode3 (pcOf 46180) 100
sym_block rebased3_7 := symRun { noAlias := true } pathCode3 (pcOf 46314) 100
sym_block rebased3_8 := symRun { noAlias := true } pathCode3 (pcOf 46459) 100
theorem run_path3 {b : Nat} (hb : b = 45349 ∨ b = 45483 ∨ b = 45626 ∨ b = 45760 ∨ b = 45903 ∨ b = 46037 ∨ b = 46180 ∨ b = 46314 ∨ b = 46459) :
    symRun { noAlias := true } pathCode3 (pcOf b) 100 =
      some ⟨path3.res.st, .c (pcOf (b + 13)), path3.res.stop, path3.res.steps, path3.res.cycles⟩ := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rebased3_0.trans (congrArg some (by kernel_rfl))
  · exact rebased3_1.trans (congrArg some (by kernel_rfl))
  · exact rebased3_2.trans (congrArg some (by kernel_rfl))
  · exact rebased3_3.trans (congrArg some (by kernel_rfl))
  · exact rebased3_4.trans (congrArg some (by kernel_rfl))
  · exact rebased3_5.trans (congrArg some (by kernel_rfl))
  · exact rebased3_6.trans (congrArg some (by kernel_rfl))
  · exact rebased3_7.trans (congrArg some (by kernel_rfl))
  · exact rebased3_8.trans (congrArg some (by kernel_rfl))
theorem path3_steps_rebased {im : Image} {b : Nat} (hbpc : b = 45349 ∨ b = 45483 ∨ b = 45626 ∨ b = 45760 ∨ b = 45903 ∨ b = 46037 ∨ b = 46180 ∨ b = 46314 ∨ b = 46459) (hc : CodeAt im (pcOf b) pathCode3)
    (s : MachineState) (hp : s.pc = pcOf b) (region source child slot : Nat)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region % 8 = 0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128) (hb : slot < 53)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 region)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 slot) :
    ∃ t, Steps im s 13 16 t ∧ t.pc = pcOf (b + 13) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child / 8))) =
        s.getMem (BitVec.ofNat 64 (source + 144)) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child / 8) + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 152)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = destination region slot (child / 8) ∨
        A = destination region slot (child / 8) + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := path3_obligs s region source child slot hr0 hr1 hra hs0 hs1 hsa hj hb h8 h16 h17 h28
  refine ⟨_, symRun_sound (run_path3 hbpc) hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [path3.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 8) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path3.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)
  · rcases Nat.mod_two_eq_zero_or_one (child / 8) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path3.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)
  · intro r hr; simp at hr; cases r <;> simp_all [path3.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 8) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path3.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      simp only [destination,hbit] at hn
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)

sym_block rebased4_0 := symRun { noAlias := true } pathCode4 (pcOf 45363) 100
sym_block rebased4_1 := symRun { noAlias := true } pathCode4 (pcOf 45497) 100
sym_block rebased4_2 := symRun { noAlias := true } pathCode4 (pcOf 45640) 100
sym_block rebased4_3 := symRun { noAlias := true } pathCode4 (pcOf 45774) 100
sym_block rebased4_4 := symRun { noAlias := true } pathCode4 (pcOf 45917) 100
sym_block rebased4_5 := symRun { noAlias := true } pathCode4 (pcOf 46051) 100
sym_block rebased4_6 := symRun { noAlias := true } pathCode4 (pcOf 46194) 100
sym_block rebased4_7 := symRun { noAlias := true } pathCode4 (pcOf 46328) 100
sym_block rebased4_8 := symRun { noAlias := true } pathCode4 (pcOf 46473) 100
theorem run_path4 {b : Nat} (hb : b = 45363 ∨ b = 45497 ∨ b = 45640 ∨ b = 45774 ∨ b = 45917 ∨ b = 46051 ∨ b = 46194 ∨ b = 46328 ∨ b = 46473) :
    symRun { noAlias := true } pathCode4 (pcOf b) 100 =
      some ⟨path4.res.st, .c (pcOf (b + 13)), path4.res.stop, path4.res.steps, path4.res.cycles⟩ := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rebased4_0.trans (congrArg some (by kernel_rfl))
  · exact rebased4_1.trans (congrArg some (by kernel_rfl))
  · exact rebased4_2.trans (congrArg some (by kernel_rfl))
  · exact rebased4_3.trans (congrArg some (by kernel_rfl))
  · exact rebased4_4.trans (congrArg some (by kernel_rfl))
  · exact rebased4_5.trans (congrArg some (by kernel_rfl))
  · exact rebased4_6.trans (congrArg some (by kernel_rfl))
  · exact rebased4_7.trans (congrArg some (by kernel_rfl))
  · exact rebased4_8.trans (congrArg some (by kernel_rfl))
theorem path4_steps_rebased {im : Image} {b : Nat} (hbpc : b = 45363 ∨ b = 45497 ∨ b = 45640 ∨ b = 45774 ∨ b = 45917 ∨ b = 46051 ∨ b = 46194 ∨ b = 46328 ∨ b = 46473) (hc : CodeAt im (pcOf b) pathCode4)
    (s : MachineState) (hp : s.pc = pcOf b) (region source child slot : Nat)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region % 8 = 0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128) (hb : slot < 53)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 region)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 slot) :
    ∃ t, Steps im s 13 16 t ∧ t.pc = pcOf (b + 13) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child / 16))) =
        s.getMem (BitVec.ofNat 64 (source + 160)) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child / 16) + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 168)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = destination region slot (child / 16) ∨
        A = destination region slot (child / 16) + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := path4_obligs s region source child slot hr0 hr1 hra hs0 hs1 hsa hj hb h8 h16 h17 h28
  refine ⟨_, symRun_sound (run_path4 hbpc) hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [path4.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 16) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path4.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)
  · rcases Nat.mod_two_eq_zero_or_one (child / 16) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path4.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)
  · intro r hr; simp at hr; cases r <;> simp_all [path4.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 16) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path4.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      simp only [destination,hbit] at hn
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)

end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- Load one validated path-plan byte without changing the source or witness memory. -/
theorem load_plan_step {im : Image} {w : BitVec 32} (pc : Word)
    (hc : CodeAt im pc [w]) (level : Fin 5)
    (hd : decodeInstruction w = some (.base (.LBU .x28 .x18 (BitVec.ofNat 12 level.val))))
    (s : MachineState) (hp : s.pc = pc) (table slot : Nat)
    (ht : table + 5 < 2^24) (hs : slot < 53)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 table)
    (hbyte : s.getByte (BitVec.ofNat 64 (table + level.val)) = BitVec.ofNat 8 slot) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pc + 4 ∧
      t.getReg .x28 = BitVec.ofNat 64 slot ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  have hoff : signExtend12 (BitVec.ofNat 12 level.val) = BitVec.ofNat 64 level.val := by
    fin_cases level <;> decide +kernel
  have haddr : s.getReg .x18 + signExtend12 (BitVec.ofNat 12 level.val) =
      BitVec.ofNat 64 (table + level.val) := by rw [h18, hoff, ofNat_add_ofNat]
  have hv : accessValid (s.getReg .x18 + signExtend12 (BitVec.ofNat 12 level.val)) 1 = true := by
    rw [haddr]; simp only [accessValid_iff, BitVec.toNat_ofNat, MEMORY_BYTES]
    have := level.isLt
    omega
  have hz : (BitVec.ofNat 8 slot).zeroExtend 64 = BitVec.ofNat 64 slot := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  have st := steps_lbu hc hp hd hv
  rw [haddr, hbyte, hz] at st
  refine ⟨_, st, ?_, ?_, ?_, ?_⟩
  · change s.pc + 4 = pc + 4; rw [hp]
  · rfl
  · intro r hr; simp at hr; cases r <;> simp_all [MachineState.setReg, MachineState.getReg, MachineState.setPC]
  · intro A hA hn; simp [rv_simp]
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def sixthCode : List (BitVec 32) := [0x34000e13,0x8e0e33,0x585313,0x137313,0x100393,0x40638333,0x3000393,0x2730333,0x6e0e33,0xb08b303,0xb88b383,0xfc6e3823,0xfc7e3c23]
sym_block sixth := symRun { noAlias := true } sixthCode (pcOf 45510) 100
theorem sixth_obligs (s : MachineState) (region source child : Nat)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region % 8 = 0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 region)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    Oblig.all s sixth.res.st.obl := by
  have hj64 : child < 2^64 := by omega
  rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
  all_goals
    simp only [sixth.res]
    t3n [h8,h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64]
    norm_num
    omega
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
private theorem low_slot_sub : (2952#64 - 48#64) = 2904#64 := rfl

abbrev topDest0 (child : Nat) : Nat := 9080 + 512 * (child / 32 % 2)
def topCode0 : List (BitVec 32) := [0x585313,0x137313,0x20000393,0x2730333,0x2e37,0x378e0e13,0x6e0e33,0xb08b303,0xb88b383,0x6e3023,0x7e3423]
sym_block top0 := symRun { noAlias := true } topCode0 (pcOf 45376) 100
theorem top0_obligs (s : MachineState) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    Oblig.all s top0.res.st.obl := by
  have hj64 : child < 2^64 := by omega
  rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
  all_goals
    simp only [top0.res]
    t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64]
    norm_num
    omega
theorem top0_steps {im : Image} (hc : CodeAt im (pcOf 45376) topCode0)
    (s : MachineState) (hp : s.pc = pcOf 45376) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    ∃ t, Steps im s 11 14 t ∧ t.pc = pcOf 45387 ∧
      t.getMem (BitVec.ofNat 64 (topDest0 child)) =
        s.getMem (BitVec.ofNat 64 (source + 176)) ∧
      t.getMem (BitVec.ofNat 64 (topDest0 child + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 184)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = topDest0 child ∨
        A = topDest0 child + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := top0_obligs s source child hs0 hs1 hsa hj h16 h17
  refine ⟨_, symRun_sound top0 hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [top0.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top0.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest0]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top0.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest0]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · intro r hr; simp at hr; cases r <;> simp_all [top0.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top0.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest0]
      simp only [topDest0,hbit] at hn
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)


abbrev topDest1 (child : Nat) : Nat := 8232 + 512 * (child / 64 % 2)
def topCode1 : List (BitVec 32) := [0x685313,0x137313,0x20000393,0x2730333,0x2e37,0x28e0e13,0x6e0e33,0xc08b303,0xc88b383,0x6e3023,0x7e3423]
sym_block top1 := symRun { noAlias := true } topCode1 (pcOf 45523) 100
theorem top1_obligs (s : MachineState) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    Oblig.all s top1.res.st.obl := by
  have hj64 : child < 2^64 := by omega
  rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
  all_goals
    simp only [top1.res]
    t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64]
    norm_num
    omega
theorem top1_steps {im : Image} (hc : CodeAt im (pcOf 45523) topCode1)
    (s : MachineState) (hp : s.pc = pcOf 45523) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    ∃ t, Steps im s 11 14 t ∧ t.pc = pcOf 45534 ∧
      t.getMem (BitVec.ofNat 64 (topDest1 child)) =
        s.getMem (BitVec.ofNat 64 (source + 192)) ∧
      t.getMem (BitVec.ofNat 64 (topDest1 child + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 200)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = topDest1 child ∨
        A = topDest1 child + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := top1_obligs s source child hs0 hs1 hsa hj h16 h17
  refine ⟨_, symRun_sound top1 hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [top1.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top1.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest1]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top1.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest1]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · intro r hr; simp at hr; cases r <;> simp_all [top1.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top1.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest1]
      simp only [topDest1,hbit] at hn
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)


abbrev topDest2 (child : Nat) : Nat := 7384 + 512 * (child / 32 % 2)
def topCode2 : List (BitVec 32) := [0x585313,0x137313,0x20000393,0x2730333,0x2e37,0xcd8e0e13,0x6e0e33,0xb08b303,0xb88b383,0x6e3023,0x7e3423]
sym_block top2 := symRun { noAlias := true } topCode2 (pcOf 45653) 100
theorem top2_obligs (s : MachineState) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    Oblig.all s top2.res.st.obl := by
  have hj64 : child < 2^64 := by omega
  rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
  all_goals
    simp only [top2.res]
    t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64]
    norm_num
    omega
theorem top2_steps {im : Image} (hc : CodeAt im (pcOf 45653) topCode2)
    (s : MachineState) (hp : s.pc = pcOf 45653) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    ∃ t, Steps im s 11 14 t ∧ t.pc = pcOf 45664 ∧
      t.getMem (BitVec.ofNat 64 (topDest2 child)) =
        s.getMem (BitVec.ofNat 64 (source + 176)) ∧
      t.getMem (BitVec.ofNat 64 (topDest2 child + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 184)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = topDest2 child ∨
        A = topDest2 child + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := top2_obligs s source child hs0 hs1 hsa hj h16 h17
  refine ⟨_, symRun_sound top2 hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [top2.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top2.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest2]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top2.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest2]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · intro r hr; simp at hr; cases r <;> simp_all [top2.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top2.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest2]
      simp only [topDest2,hbit] at hn
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)


abbrev topDest3 (child : Nat) : Nat := 6536 + 512 * (child / 64 % 2)
def topCode3 : List (BitVec 32) := [0x685313,0x137313,0x20000393,0x2730333,0x2e37,0x988e0e13,0x6e0e33,0xc08b303,0xc88b383,0x6e3023,0x7e3423]
sym_block top3 := symRun { noAlias := true } topCode3 (pcOf 45800) 100
theorem top3_obligs (s : MachineState) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    Oblig.all s top3.res.st.obl := by
  have hj64 : child < 2^64 := by omega
  rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
  all_goals
    simp only [top3.res]
    t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64]
    norm_num
    omega
theorem top3_steps {im : Image} (hc : CodeAt im (pcOf 45800) topCode3)
    (s : MachineState) (hp : s.pc = pcOf 45800) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    ∃ t, Steps im s 11 14 t ∧ t.pc = pcOf 45811 ∧
      t.getMem (BitVec.ofNat 64 (topDest3 child)) =
        s.getMem (BitVec.ofNat 64 (source + 192)) ∧
      t.getMem (BitVec.ofNat 64 (topDest3 child + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 200)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = topDest3 child ∨
        A = topDest3 child + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := top3_obligs s source child hs0 hs1 hsa hj h16 h17
  refine ⟨_, symRun_sound top3 hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [top3.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top3.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest3]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top3.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest3]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · intro r hr; simp at hr; cases r <;> simp_all [top3.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top3.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest3]
      simp only [topDest3,hbit] at hn
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)


abbrev topDest4 (child : Nat) : Nat := 5688 + 512 * (child / 32 % 2)
def topCode4 : List (BitVec 32) := [0x585313,0x137313,0x20000393,0x2730333,0x1e37,0x638e0e13,0x6e0e33,0xb08b303,0xb88b383,0x6e3023,0x7e3423]
sym_block top4 := symRun { noAlias := true } topCode4 (pcOf 45930) 100
theorem top4_obligs (s : MachineState) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    Oblig.all s top4.res.st.obl := by
  have hj64 : child < 2^64 := by omega
  rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
  all_goals
    simp only [top4.res]
    t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64]
    norm_num
    omega
theorem top4_steps {im : Image} (hc : CodeAt im (pcOf 45930) topCode4)
    (s : MachineState) (hp : s.pc = pcOf 45930) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    ∃ t, Steps im s 11 14 t ∧ t.pc = pcOf 45941 ∧
      t.getMem (BitVec.ofNat 64 (topDest4 child)) =
        s.getMem (BitVec.ofNat 64 (source + 176)) ∧
      t.getMem (BitVec.ofNat 64 (topDest4 child + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 184)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = topDest4 child ∨
        A = topDest4 child + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := top4_obligs s source child hs0 hs1 hsa hj h16 h17
  refine ⟨_, symRun_sound top4 hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [top4.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top4.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest4]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top4.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest4]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · intro r hr; simp at hr; cases r <;> simp_all [top4.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top4.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest4]
      simp only [topDest4,hbit] at hn
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)


abbrev topDest5 (child : Nat) : Nat := 4840 + 512 * (child / 64 % 2)
def topCode5 : List (BitVec 32) := [0x685313,0x137313,0x20000393,0x2730333,0x1e37,0x2e8e0e13,0x6e0e33,0xc08b303,0xc88b383,0x6e3023,0x7e3423]
sym_block top5 := symRun { noAlias := true } topCode5 (pcOf 46077) 100
theorem top5_obligs (s : MachineState) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    Oblig.all s top5.res.st.obl := by
  have hj64 : child < 2^64 := by omega
  rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
  all_goals
    simp only [top5.res]
    t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64]
    norm_num
    omega
theorem top5_steps {im : Image} (hc : CodeAt im (pcOf 46077) topCode5)
    (s : MachineState) (hp : s.pc = pcOf 46077) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    ∃ t, Steps im s 11 14 t ∧ t.pc = pcOf 46088 ∧
      t.getMem (BitVec.ofNat 64 (topDest5 child)) =
        s.getMem (BitVec.ofNat 64 (source + 192)) ∧
      t.getMem (BitVec.ofNat 64 (topDest5 child + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 200)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = topDest5 child ∨
        A = topDest5 child + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := top5_obligs s source child hs0 hs1 hsa hj h16 h17
  refine ⟨_, symRun_sound top5 hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [top5.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top5.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest5]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top5.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest5]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · intro r hr; simp at hr; cases r <;> simp_all [top5.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top5.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest5]
      simp only [topDest5,hbit] at hn
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)


abbrev topDest6 (child : Nat) : Nat := 3992 + 512 * (child / 32 % 2)
def topCode6 : List (BitVec 32) := [0x585313,0x137313,0x20000393,0x2730333,0x1e37,0xf98e0e13,0x6e0e33,0xb08b303,0xb88b383,0x6e3023,0x7e3423]
sym_block top6 := symRun { noAlias := true } topCode6 (pcOf 46207) 100
theorem top6_obligs (s : MachineState) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    Oblig.all s top6.res.st.obl := by
  have hj64 : child < 2^64 := by omega
  rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
  all_goals
    simp only [top6.res]
    t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64]
    norm_num
    omega
theorem top6_steps {im : Image} (hc : CodeAt im (pcOf 46207) topCode6)
    (s : MachineState) (hp : s.pc = pcOf 46207) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    ∃ t, Steps im s 11 14 t ∧ t.pc = pcOf 46218 ∧
      t.getMem (BitVec.ofNat 64 (topDest6 child)) =
        s.getMem (BitVec.ofNat 64 (source + 176)) ∧
      t.getMem (BitVec.ofNat 64 (topDest6 child + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 184)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = topDest6 child ∨
        A = topDest6 child + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := top6_obligs s source child hs0 hs1 hsa hj h16 h17
  refine ⟨_, symRun_sound top6 hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [top6.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top6.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest6]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top6.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest6]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · intro r hr; simp at hr; cases r <;> simp_all [top6.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top6.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest6]
      simp only [topDest6,hbit] at hn
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)


abbrev topDest7 (child : Nat) : Nat := 3144 + 512 * (child / 64 % 2)
def topCode7 : List (BitVec 32) := [0x685313,0x137313,0x20000393,0x2730333,0xd5040e13,0x6e0e33,0xc08b303,0xc88b383,0x6e3023,0x7e3423]
sym_block top7 := symRun { noAlias := true } topCode7 (pcOf 46354) 100
theorem top7_obligs (s : MachineState) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 3832) :
    Oblig.all s top7.res.st.obl := by
  have hj64 : child < 2^64 := by omega
  rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
  all_goals
    simp only [top7.res]
    t3n [h8,h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64]
    norm_num
    omega
theorem top7_steps {im : Image} (hc : CodeAt im (pcOf 46354) topCode7)
    (s : MachineState) (hp : s.pc = pcOf 46354) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 3832) :
    ∃ t, Steps im s 10 13 t ∧ t.pc = pcOf 46364 ∧
      t.getMem (BitVec.ofNat 64 (topDest7 child)) =
        s.getMem (BitVec.ofNat 64 (source + 192)) ∧
      t.getMem (BitVec.ofNat 64 (topDest7 child + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 200)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = topDest7 child ∨
        A = topDest7 child + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := top7_obligs s source child hs0 hs1 hsa hj h16 h17 h8
  refine ⟨_, symRun_sound top7 hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [top7.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top7.res]
      t3n [h8,h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest7]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top7.res]
      t3n [h8,h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest7]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · intro r hr; simp at hr; cases r <;> simp_all [top7.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top7.res]
      t3n [h8,h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest7]
      simp only [topDest7,hbit] at hn
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)


abbrev topDest8 (child : Nat) : Nat := 2952 - 48 * (child / 64 % 2)
def topCode8 : List (BitVec 32) := [0x685313,0x137313,0x3000393,0x2730333,0xfe040e13,0x406e0e33,0xc08b303,0xc88b383,0x6e3023,0x7e3423]
sym_block top8 := symRun { noAlias := true } topCode8 (pcOf 46499) 100
theorem top8_obligs (s : MachineState) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 2984) :
    Oblig.all s top8.res.st.obl := by
  have hj64 : child < 2^64 := by omega
  rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
  all_goals
    simp only [top8.res]
    t3n [h8,h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64]
    norm_num
    omega
theorem top8_steps {im : Image} (hc : CodeAt im (pcOf 46499) topCode8)
    (s : MachineState) (hp : s.pc = pcOf 46499) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 2984) :
    ∃ t, Steps im s 10 13 t ∧ t.pc = pcOf 46509 ∧
      t.getMem (BitVec.ofNat 64 (topDest8 child)) =
        s.getMem (BitVec.ofNat 64 (source + 192)) ∧
      t.getMem (BitVec.ofNat 64 (topDest8 child + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 200)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = topDest8 child ∨
        A = topDest8 child + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := top8_obligs s source child hs0 hs1 hsa hj h16 h17 h8
  refine ⟨_, symRun_sound top8 hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [top8.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top8.res]
      t3n [h8,h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest8]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals (try simp only [BitVec.reduceSub, BitVec.reduceAdd] at *) <;> (try norm_num [ofNat_eq_iff] at *) <;> split_ifs <;> (first | rfl | omega | simp_all)
  · rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top8.res]
      t3n [h8,h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest8]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals (try simp only [BitVec.reduceSub, BitVec.reduceAdd] at *) <;> (try norm_num [ofNat_eq_iff] at *) <;> split_ifs <;> (first | rfl | omega | simp_all)
  · intro r hr; simp at hr; cases r <;> simp_all [top8.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top8.res]
      t3n [h8,h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest8]
      simp only [topDest8,hbit] at hn
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals (try simp only [BitVec.reduceSub, BitVec.reduceAdd] at *) <;> (try norm_num [ofNat_eq_iff] at *) <;> split_ifs <;> (first | rfl | omega | simp_all)


end ClaudeWCT.W9.Machine.Expand.SharedScatter


namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
sym_block sixthRebase0 := symRun { noAlias := true } sixthCode (pcOf 45510) 100
sym_block sixthRebase1 := symRun { noAlias := true } sixthCode (pcOf 45787) 100
sym_block sixthRebase2 := symRun { noAlias := true } sixthCode (pcOf 46064) 100
sym_block sixthRebase3 := symRun { noAlias := true } sixthCode (pcOf 46341) 100
sym_block sixthRebase4 := symRun { noAlias := true } sixthCode (pcOf 46486) 100
theorem run_sixth {b : Nat} (hb : b = 45510 ∨ b = 45787 ∨ b = 46064 ∨ b = 46341 ∨ b = 46486) :
    symRun { noAlias := true } sixthCode (pcOf b) 100 =
      some ⟨sixth.res.st, .c (pcOf (b + 13)), sixth.res.stop, sixth.res.steps, sixth.res.cycles⟩ := by
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · exact sixthRebase0.trans (congrArg some (by kernel_rfl))
  · exact sixthRebase1.trans (congrArg some (by kernel_rfl))
  · exact sixthRebase2.trans (congrArg some (by kernel_rfl))
  · exact sixthRebase3.trans (congrArg some (by kernel_rfl))
  · exact sixthRebase4.trans (congrArg some (by kernel_rfl))
theorem sixth_steps_rebased {im : Image} {b : Nat} (hbpc : b = 45510 ∨ b = 45787 ∨ b = 46064 ∨ b = 46341 ∨ b = 46486) (hc : CodeAt im (pcOf b) sixthCode)
    (s : MachineState) (hp : s.pc = pcOf b) (region source child : Nat)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region % 8 = 0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 region)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    ∃ t, Steps im s 13 16 t ∧ t.pc = pcOf (b+13) ∧
      t.getMem (BitVec.ofNat 64 (destination region 49 (child / 32))) =
        s.getMem (BitVec.ofNat 64 (source + 176)) ∧
      t.getMem (BitVec.ofNat 64 (destination region 49 (child / 32) + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 184)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = destination region 49 (child / 32) ∨
        A = destination region 49 (child / 32) + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := sixth_obligs s region source child hr0 hr1 hra hs0 hs1 hsa hj h8 h16 h17
  refine ⟨_, symRun_sound (run_sixth hbpc) hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [sixth.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,sixth.res]
      t3n [h8,h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      norm_num [ofNat_sub_ofNat_u,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals first | rfl | (intro h; exfalso; omega) | (split_ifs <;> (first | rfl | omega))
  · rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,sixth.res]
      t3n [h8,h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      norm_num [ofNat_sub_ofNat_u,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals first | rfl | (intro h; exfalso; omega) | (split_ifs <;> (first | rfl | omega))
  · intro r hr; simp at hr; cases r <;> simp_all [sixth.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,sixth.res]
      t3n [h8,h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      simp only [destination,hbit] at hn
      norm_num [ofNat_sub_ofNat_u,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals first | rfl | (intro h; exfalso; omega) | (split_ifs <;> (first | rfl | omega))

end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
def value0Code : List (BitVec 32) := bv_list% 32 [0x8b303,0x88b383,0x28643023,0x28743423]
sym_block value0_0 := symRun { noAlias := true } value0Code (pcOf 45266) 20
sym_block value0_1 := symRun { noAlias := true } value0Code (pcOf 45400) 20
sym_block value0_2 := symRun { noAlias := true } value0Code (pcOf 45543) 20
sym_block value0_3 := symRun { noAlias := true } value0Code (pcOf 45677) 20
sym_block value0_4 := symRun { noAlias := true } value0Code (pcOf 45820) 20
sym_block value0_5 := symRun { noAlias := true } value0Code (pcOf 45954) 20
sym_block value0_6 := symRun { noAlias := true } value0Code (pcOf 46097) 20
sym_block value0_7 := symRun { noAlias := true } value0Code (pcOf 46231) 20
sym_block value0_8 := symRun { noAlias := true } value0Code (pcOf 46376) 20
theorem value0_run {b : Nat} (hb : b=45266 ∨ b=45400 ∨ b=45543 ∨ b=45677 ∨ b=45820 ∨ b=45954 ∨ b=46097 ∨ b=46231 ∨ b=46376) :
    symRun { noAlias := true } value0Code (pcOf b) 20 =
      some ⟨value0_0.res.st,.c (pcOf (b+4)),value0_0.res.stop,value0_0.res.steps,value0_0.res.cycles⟩ := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact value0_0.trans (congrArg some (by kernel_rfl))
  · exact value0_1.trans (congrArg some (by kernel_rfl))
  · exact value0_2.trans (congrArg some (by kernel_rfl))
  · exact value0_3.trans (congrArg some (by kernel_rfl))
  · exact value0_4.trans (congrArg some (by kernel_rfl))
  · exact value0_5.trans (congrArg some (by kernel_rfl))
  · exact value0_6.trans (congrArg some (by kernel_rfl))
  · exact value0_7.trans (congrArg some (by kernel_rfl))
  · exact value0_8.trans (congrArg some (by kernel_rfl))
theorem value0_steps {im : Image} {b : Nat} (hb : b=45266 ∨ b=45400 ∨ b=45543 ∨ b=45677 ∨ b=45820 ∨ b=45954 ∨ b=46097 ∨ b=46231 ∨ b=46376)
    (hc : CodeAt im (pcOf b) value0Code) (s : MachineState) (hp : s.pc=pcOf b)
    (region source : Nat) (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h17 : s.getReg .x17=BitVec.ofNat 64 source) :
    ∃ t, Steps im s 4 4 t ∧ t.pc=pcOf (b+4) ∧
      t.getMem (BitVec.ofNat 64 (region+640))=s.getMem (BitVec.ofNat 64 (source+0)) ∧
      t.getMem (BitVec.ofNat 64 (region+648))=s.getMem (BitVec.ofNat 64 (source+8)) ∧
      RegsExcept s t [.x6,.x7] ∧ Frame s t (fun A => A=region+640 ∨ A=region+648) := by
  have ho : Oblig.all s value0_0.res.st.obl := by
    simp only [value0_0.res]
    t3n [h8,h17]
    omega
  refine ⟨_,symRun_sound (value0_run hb) hc s hp ho,?_,?_,?_,?_,?_⟩
  · simp [Result.toState_pc,E.eval]
  · simp only [Result.toState_getMem,value0_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value0_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn
    simp only [Result.toState_getMem,value0_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
def value1Code : List (BitVec 32) := bv_list% 32 [0x108b303,0x188b383,0x1e643c23,0x20743023,0x2a643823,0x2a743c23]
sym_block value1_0 := symRun { noAlias := true } value1Code (pcOf 45270) 20
sym_block value1_1 := symRun { noAlias := true } value1Code (pcOf 45404) 20
sym_block value1_2 := symRun { noAlias := true } value1Code (pcOf 45547) 20
sym_block value1_3 := symRun { noAlias := true } value1Code (pcOf 45681) 20
sym_block value1_4 := symRun { noAlias := true } value1Code (pcOf 45824) 20
sym_block value1_5 := symRun { noAlias := true } value1Code (pcOf 45958) 20
sym_block value1_6 := symRun { noAlias := true } value1Code (pcOf 46101) 20
sym_block value1_7 := symRun { noAlias := true } value1Code (pcOf 46235) 20
sym_block value1_8 := symRun { noAlias := true } value1Code (pcOf 46380) 20
theorem value1_run {b : Nat} (hb : b=45270 ∨ b=45404 ∨ b=45547 ∨ b=45681 ∨ b=45824 ∨ b=45958 ∨ b=46101 ∨ b=46235 ∨ b=46380) :
    symRun { noAlias := true } value1Code (pcOf b) 20 =
      some ⟨value1_0.res.st,.c (pcOf (b+6)),value1_0.res.stop,value1_0.res.steps,value1_0.res.cycles⟩ := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact value1_0.trans (congrArg some (by kernel_rfl))
  · exact value1_1.trans (congrArg some (by kernel_rfl))
  · exact value1_2.trans (congrArg some (by kernel_rfl))
  · exact value1_3.trans (congrArg some (by kernel_rfl))
  · exact value1_4.trans (congrArg some (by kernel_rfl))
  · exact value1_5.trans (congrArg some (by kernel_rfl))
  · exact value1_6.trans (congrArg some (by kernel_rfl))
  · exact value1_7.trans (congrArg some (by kernel_rfl))
  · exact value1_8.trans (congrArg some (by kernel_rfl))
theorem value1_steps {im : Image} {b : Nat} (hb : b=45270 ∨ b=45404 ∨ b=45547 ∨ b=45681 ∨ b=45824 ∨ b=45958 ∨ b=46101 ∨ b=46235 ∨ b=46380)
    (hc : CodeAt im (pcOf b) value1Code) (s : MachineState) (hp : s.pc=pcOf b)
    (region source : Nat) (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h17 : s.getReg .x17=BitVec.ofNat 64 source) :
    ∃ t, Steps im s 6 6 t ∧ t.pc=pcOf (b+6) ∧
      t.getMem (BitVec.ofNat 64 (region+504))=s.getMem (BitVec.ofNat 64 (source+16)) ∧
      t.getMem (BitVec.ofNat 64 (region+512))=s.getMem (BitVec.ofNat 64 (source+24)) ∧
      t.getMem (BitVec.ofNat 64 (region+688))=s.getMem (BitVec.ofNat 64 (source+16)) ∧
      t.getMem (BitVec.ofNat 64 (region+696))=s.getMem (BitVec.ofNat 64 (source+24)) ∧
      RegsExcept s t [.x6,.x7] ∧ Frame s t (fun A => A=region+504 ∨ A=region+512 ∨ A=region+688 ∨ A=region+696) := by
  have ho : Oblig.all s value1_0.res.st.obl := by
    simp only [value1_0.res]
    t3n [h8,h17]
    omega
  refine ⟨_,symRun_sound (value1_run hb) hc s hp ho,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [Result.toState_pc,E.eval]
  · simp only [Result.toState_getMem,value1_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value1_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value1_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value1_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn
    simp only [Result.toState_getMem,value1_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
def value2Code : List (BitVec 32) := bv_list% 32 [0x208b303,0x288b383,0x24643023,0x24743423,0x2c643023,0x2c743423]
sym_block value2_0 := symRun { noAlias := true } value2Code (pcOf 45276) 20
sym_block value2_1 := symRun { noAlias := true } value2Code (pcOf 45410) 20
sym_block value2_2 := symRun { noAlias := true } value2Code (pcOf 45553) 20
sym_block value2_3 := symRun { noAlias := true } value2Code (pcOf 45687) 20
sym_block value2_4 := symRun { noAlias := true } value2Code (pcOf 45830) 20
sym_block value2_5 := symRun { noAlias := true } value2Code (pcOf 45964) 20
sym_block value2_6 := symRun { noAlias := true } value2Code (pcOf 46107) 20
sym_block value2_7 := symRun { noAlias := true } value2Code (pcOf 46241) 20
sym_block value2_8 := symRun { noAlias := true } value2Code (pcOf 46386) 20
theorem value2_run {b : Nat} (hb : b=45276 ∨ b=45410 ∨ b=45553 ∨ b=45687 ∨ b=45830 ∨ b=45964 ∨ b=46107 ∨ b=46241 ∨ b=46386) :
    symRun { noAlias := true } value2Code (pcOf b) 20 =
      some ⟨value2_0.res.st,.c (pcOf (b+6)),value2_0.res.stop,value2_0.res.steps,value2_0.res.cycles⟩ := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact value2_0.trans (congrArg some (by kernel_rfl))
  · exact value2_1.trans (congrArg some (by kernel_rfl))
  · exact value2_2.trans (congrArg some (by kernel_rfl))
  · exact value2_3.trans (congrArg some (by kernel_rfl))
  · exact value2_4.trans (congrArg some (by kernel_rfl))
  · exact value2_5.trans (congrArg some (by kernel_rfl))
  · exact value2_6.trans (congrArg some (by kernel_rfl))
  · exact value2_7.trans (congrArg some (by kernel_rfl))
  · exact value2_8.trans (congrArg some (by kernel_rfl))
theorem value2_steps {im : Image} {b : Nat} (hb : b=45276 ∨ b=45410 ∨ b=45553 ∨ b=45687 ∨ b=45830 ∨ b=45964 ∨ b=46107 ∨ b=46241 ∨ b=46386)
    (hc : CodeAt im (pcOf b) value2Code) (s : MachineState) (hp : s.pc=pcOf b)
    (region source : Nat) (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h17 : s.getReg .x17=BitVec.ofNat 64 source) :
    ∃ t, Steps im s 6 6 t ∧ t.pc=pcOf (b+6) ∧
      t.getMem (BitVec.ofNat 64 (region+576))=s.getMem (BitVec.ofNat 64 (source+32)) ∧
      t.getMem (BitVec.ofNat 64 (region+584))=s.getMem (BitVec.ofNat 64 (source+40)) ∧
      t.getMem (BitVec.ofNat 64 (region+704))=s.getMem (BitVec.ofNat 64 (source+32)) ∧
      t.getMem (BitVec.ofNat 64 (region+712))=s.getMem (BitVec.ofNat 64 (source+40)) ∧
      RegsExcept s t [.x6,.x7] ∧ Frame s t (fun A => A=region+576 ∨ A=region+584 ∨ A=region+704 ∨ A=region+712) := by
  have ho : Oblig.all s value2_0.res.st.obl := by
    simp only [value2_0.res]
    t3n [h8,h17]
    omega
  refine ⟨_,symRun_sound (value2_run hb) hc s hp ho,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [Result.toState_pc,E.eval]
  · simp only [Result.toState_getMem,value2_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value2_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value2_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value2_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn
    simp only [Result.toState_getMem,value2_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
def value3Code : List (BitVec 32) := bv_list% 32 [0x308b303,0x388b383,0x18643823,0x18743c23,0x2c643823,0x2c743c23]
sym_block value3_0 := symRun { noAlias := true } value3Code (pcOf 45282) 20
sym_block value3_1 := symRun { noAlias := true } value3Code (pcOf 45416) 20
sym_block value3_2 := symRun { noAlias := true } value3Code (pcOf 45559) 20
sym_block value3_3 := symRun { noAlias := true } value3Code (pcOf 45693) 20
sym_block value3_4 := symRun { noAlias := true } value3Code (pcOf 45836) 20
sym_block value3_5 := symRun { noAlias := true } value3Code (pcOf 45970) 20
sym_block value3_6 := symRun { noAlias := true } value3Code (pcOf 46113) 20
sym_block value3_7 := symRun { noAlias := true } value3Code (pcOf 46247) 20
sym_block value3_8 := symRun { noAlias := true } value3Code (pcOf 46392) 20
theorem value3_run {b : Nat} (hb : b=45282 ∨ b=45416 ∨ b=45559 ∨ b=45693 ∨ b=45836 ∨ b=45970 ∨ b=46113 ∨ b=46247 ∨ b=46392) :
    symRun { noAlias := true } value3Code (pcOf b) 20 =
      some ⟨value3_0.res.st,.c (pcOf (b+6)),value3_0.res.stop,value3_0.res.steps,value3_0.res.cycles⟩ := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact value3_0.trans (congrArg some (by kernel_rfl))
  · exact value3_1.trans (congrArg some (by kernel_rfl))
  · exact value3_2.trans (congrArg some (by kernel_rfl))
  · exact value3_3.trans (congrArg some (by kernel_rfl))
  · exact value3_4.trans (congrArg some (by kernel_rfl))
  · exact value3_5.trans (congrArg some (by kernel_rfl))
  · exact value3_6.trans (congrArg some (by kernel_rfl))
  · exact value3_7.trans (congrArg some (by kernel_rfl))
  · exact value3_8.trans (congrArg some (by kernel_rfl))
theorem value3_steps {im : Image} {b : Nat} (hb : b=45282 ∨ b=45416 ∨ b=45559 ∨ b=45693 ∨ b=45836 ∨ b=45970 ∨ b=46113 ∨ b=46247 ∨ b=46392)
    (hc : CodeAt im (pcOf b) value3Code) (s : MachineState) (hp : s.pc=pcOf b)
    (region source : Nat) (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h17 : s.getReg .x17=BitVec.ofNat 64 source) :
    ∃ t, Steps im s 6 6 t ∧ t.pc=pcOf (b+6) ∧
      t.getMem (BitVec.ofNat 64 (region+400))=s.getMem (BitVec.ofNat 64 (source+48)) ∧
      t.getMem (BitVec.ofNat 64 (region+408))=s.getMem (BitVec.ofNat 64 (source+56)) ∧
      t.getMem (BitVec.ofNat 64 (region+720))=s.getMem (BitVec.ofNat 64 (source+48)) ∧
      t.getMem (BitVec.ofNat 64 (region+728))=s.getMem (BitVec.ofNat 64 (source+56)) ∧
      RegsExcept s t [.x6,.x7] ∧ Frame s t (fun A => A=region+400 ∨ A=region+408 ∨ A=region+720 ∨ A=region+728) := by
  have ho : Oblig.all s value3_0.res.st.obl := by
    simp only [value3_0.res]
    t3n [h8,h17]
    omega
  refine ⟨_,symRun_sound (value3_run hb) hc s hp ho,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [Result.toState_pc,E.eval]
  · simp only [Result.toState_getMem,value3_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value3_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value3_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value3_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn
    simp only [Result.toState_getMem,value3_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
def value4Code : List (BitVec 32) := bv_list% 32 [0x408b303,0x488b383,0x1c643c23,0x1e743023,0x2e643023,0x2e743423]
sym_block value4_0 := symRun { noAlias := true } value4Code (pcOf 45288) 20
sym_block value4_1 := symRun { noAlias := true } value4Code (pcOf 45422) 20
sym_block value4_2 := symRun { noAlias := true } value4Code (pcOf 45565) 20
sym_block value4_3 := symRun { noAlias := true } value4Code (pcOf 45699) 20
sym_block value4_4 := symRun { noAlias := true } value4Code (pcOf 45842) 20
sym_block value4_5 := symRun { noAlias := true } value4Code (pcOf 45976) 20
sym_block value4_6 := symRun { noAlias := true } value4Code (pcOf 46119) 20
sym_block value4_7 := symRun { noAlias := true } value4Code (pcOf 46253) 20
sym_block value4_8 := symRun { noAlias := true } value4Code (pcOf 46398) 20
theorem value4_run {b : Nat} (hb : b=45288 ∨ b=45422 ∨ b=45565 ∨ b=45699 ∨ b=45842 ∨ b=45976 ∨ b=46119 ∨ b=46253 ∨ b=46398) :
    symRun { noAlias := true } value4Code (pcOf b) 20 =
      some ⟨value4_0.res.st,.c (pcOf (b+6)),value4_0.res.stop,value4_0.res.steps,value4_0.res.cycles⟩ := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact value4_0.trans (congrArg some (by kernel_rfl))
  · exact value4_1.trans (congrArg some (by kernel_rfl))
  · exact value4_2.trans (congrArg some (by kernel_rfl))
  · exact value4_3.trans (congrArg some (by kernel_rfl))
  · exact value4_4.trans (congrArg some (by kernel_rfl))
  · exact value4_5.trans (congrArg some (by kernel_rfl))
  · exact value4_6.trans (congrArg some (by kernel_rfl))
  · exact value4_7.trans (congrArg some (by kernel_rfl))
  · exact value4_8.trans (congrArg some (by kernel_rfl))
theorem value4_steps {im : Image} {b : Nat} (hb : b=45288 ∨ b=45422 ∨ b=45565 ∨ b=45699 ∨ b=45842 ∨ b=45976 ∨ b=46119 ∨ b=46253 ∨ b=46398)
    (hc : CodeAt im (pcOf b) value4Code) (s : MachineState) (hp : s.pc=pcOf b)
    (region source : Nat) (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h17 : s.getReg .x17=BitVec.ofNat 64 source) :
    ∃ t, Steps im s 6 6 t ∧ t.pc=pcOf (b+6) ∧
      t.getMem (BitVec.ofNat 64 (region+472))=s.getMem (BitVec.ofNat 64 (source+64)) ∧
      t.getMem (BitVec.ofNat 64 (region+480))=s.getMem (BitVec.ofNat 64 (source+72)) ∧
      t.getMem (BitVec.ofNat 64 (region+736))=s.getMem (BitVec.ofNat 64 (source+64)) ∧
      t.getMem (BitVec.ofNat 64 (region+744))=s.getMem (BitVec.ofNat 64 (source+72)) ∧
      RegsExcept s t [.x6,.x7] ∧ Frame s t (fun A => A=region+472 ∨ A=region+480 ∨ A=region+736 ∨ A=region+744) := by
  have ho : Oblig.all s value4_0.res.st.obl := by
    simp only [value4_0.res]
    t3n [h8,h17]
    omega
  refine ⟨_,symRun_sound (value4_run hb) hc s hp ho,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [Result.toState_pc,E.eval]
  · simp only [Result.toState_getMem,value4_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value4_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value4_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value4_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn
    simp only [Result.toState_getMem,value4_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
def value5Code : List (BitVec 32) := bv_list% 32 [0x508b303,0x588b383,0x16643823,0x16743c23,0x2e643823,0x2e743c23]
sym_block value5_0 := symRun { noAlias := true } value5Code (pcOf 45294) 20
sym_block value5_1 := symRun { noAlias := true } value5Code (pcOf 45428) 20
sym_block value5_2 := symRun { noAlias := true } value5Code (pcOf 45571) 20
sym_block value5_3 := symRun { noAlias := true } value5Code (pcOf 45705) 20
sym_block value5_4 := symRun { noAlias := true } value5Code (pcOf 45848) 20
sym_block value5_5 := symRun { noAlias := true } value5Code (pcOf 45982) 20
sym_block value5_6 := symRun { noAlias := true } value5Code (pcOf 46125) 20
sym_block value5_7 := symRun { noAlias := true } value5Code (pcOf 46259) 20
sym_block value5_8 := symRun { noAlias := true } value5Code (pcOf 46404) 20
theorem value5_run {b : Nat} (hb : b=45294 ∨ b=45428 ∨ b=45571 ∨ b=45705 ∨ b=45848 ∨ b=45982 ∨ b=46125 ∨ b=46259 ∨ b=46404) :
    symRun { noAlias := true } value5Code (pcOf b) 20 =
      some ⟨value5_0.res.st,.c (pcOf (b+6)),value5_0.res.stop,value5_0.res.steps,value5_0.res.cycles⟩ := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact value5_0.trans (congrArg some (by kernel_rfl))
  · exact value5_1.trans (congrArg some (by kernel_rfl))
  · exact value5_2.trans (congrArg some (by kernel_rfl))
  · exact value5_3.trans (congrArg some (by kernel_rfl))
  · exact value5_4.trans (congrArg some (by kernel_rfl))
  · exact value5_5.trans (congrArg some (by kernel_rfl))
  · exact value5_6.trans (congrArg some (by kernel_rfl))
  · exact value5_7.trans (congrArg some (by kernel_rfl))
  · exact value5_8.trans (congrArg some (by kernel_rfl))
theorem value5_steps {im : Image} {b : Nat} (hb : b=45294 ∨ b=45428 ∨ b=45571 ∨ b=45705 ∨ b=45848 ∨ b=45982 ∨ b=46125 ∨ b=46259 ∨ b=46404)
    (hc : CodeAt im (pcOf b) value5Code) (s : MachineState) (hp : s.pc=pcOf b)
    (region source : Nat) (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h17 : s.getReg .x17=BitVec.ofNat 64 source) :
    ∃ t, Steps im s 6 6 t ∧ t.pc=pcOf (b+6) ∧
      t.getMem (BitVec.ofNat 64 (region+368))=s.getMem (BitVec.ofNat 64 (source+80)) ∧
      t.getMem (BitVec.ofNat 64 (region+376))=s.getMem (BitVec.ofNat 64 (source+88)) ∧
      t.getMem (BitVec.ofNat 64 (region+752))=s.getMem (BitVec.ofNat 64 (source+80)) ∧
      t.getMem (BitVec.ofNat 64 (region+760))=s.getMem (BitVec.ofNat 64 (source+88)) ∧
      RegsExcept s t [.x6,.x7] ∧ Frame s t (fun A => A=region+368 ∨ A=region+376 ∨ A=region+752 ∨ A=region+760) := by
  have ho : Oblig.all s value5_0.res.st.obl := by
    simp only [value5_0.res]
    t3n [h8,h17]
    omega
  refine ⟨_,symRun_sound (value5_run hb) hc s hp ho,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [Result.toState_pc,E.eval]
  · simp only [Result.toState_getMem,value5_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value5_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value5_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value5_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn
    simp only [Result.toState_getMem,value5_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

theorem rotate_raw (raw : Nat) (hr : raw<128) :
    (BitVec.ofNat 64 raw >>> 1) + ((BitVec.ofNat 64 raw &&& 1#64) <<< 6) =
      BitVec.ofNat 64 (raw/2+64*(raw%2)) := by
  have hm : BitVec.ofNat 64 raw &&& 1#64=BitVec.ofNat 64 (raw%2) := by
    simpa using SigGolfCandidate.T3M.Sign.ofNat_and_mask raw 1 (by decide)
  rw [ofNat_shr raw 1 (by omega),hm,ofNat_shl,ofNat_add_ofNat]
  congr 1
  simp only [pow_one]
  omega
def entry0Code : List (BitVec 32) := bv_list% 32 [0x208b7,0x16088893,0x8b803,0x85813,0x7f87813,0x2437,0x62840413,0x78b7,0x1088893]
sym_block entry0 := symRun { noAlias := true } entry0Code (pcOf 45257) 32
theorem entry0_steps {im : Image} (hc : CodeAt im (pcOf 45257) entry0Code)
    (s : MachineState) (hp : s.pc=pcOf 45257) (raw : Nat) (hr : raw<128)
    (hraw : s.getMem (BitVec.ofNat 64 131424) >>> 0 &&& 127#64=BitVec.ofNat 64 raw) :
    ∃ t, Steps im s 9 9 t ∧ t.pc=pcOf 45266 ∧
      t.getReg .x16=BitVec.ofNat 64 raw ∧
      t.getReg .x8=BitVec.ofNat 64 9768 ∧
      t.getReg .x17=BitVec.ofNat 64 28688 ∧
      RegsExcept s t [.x6,.x8,.x16,.x17] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound entry0 hc s hp (by simp [entry0.res,rv_simp]),?_,?_,?_,?_,?_,?_⟩
  · simp [entry0.res,E.eval]
  · simp only [Result.toState_getReg,entry0.res]
    t3n []
    simpa using hraw
  · simp [entry0.res,rv_simp]
  · simp [entry0.res,rv_simp]
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn; simp [entry0.res,rv_simp]
def entry1Code : List (BitVec 32) := bv_list% 32 [0x208b7,0x16088893,0x8b803,0x685813,0x7f87813,0x187313,0x631313,0x185813,0x680833,0x2437,0x2d840413,0x78b7,0xe088893]
sym_block entry1 := symRun { noAlias := true } entry1Code (pcOf 45387) 32
theorem entry1_steps {im : Image} (hc : CodeAt im (pcOf 45387) entry1Code)
    (s : MachineState) (hp : s.pc=pcOf 45387) (raw : Nat) (hr : raw<128)
    (hraw : s.getMem (BitVec.ofNat 64 131424) >>> 6 &&& 127#64=BitVec.ofNat 64 raw) :
    ∃ t, Steps im s 13 13 t ∧ t.pc=pcOf 45400 ∧
      t.getReg .x16=BitVec.ofNat 64 (raw/2+64*(raw%2)) ∧
      t.getReg .x8=BitVec.ofNat 64 8920 ∧
      t.getReg .x17=BitVec.ofNat 64 28896 ∧
      RegsExcept s t [.x6,.x8,.x16,.x17] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound entry1 hc s hp (by simp [entry1.res,rv_simp]),?_,?_,?_,?_,?_,?_⟩
  · simp [entry1.res,E.eval]
  · simp only [Result.toState_getReg,entry1.res]
    t3n []
    have hraw' : s.getMem 131424#64 >>> 6 &&& 127#64=BitVec.ofNat 64 raw := hraw
    rw [hraw']
    exact rotate_raw raw hr
  · simp [entry1.res,rv_simp]
  · simp [entry1.res,rv_simp]
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn; simp [entry1.res,rv_simp]
def entry2Code : List (BitVec 32) := bv_list% 32 [0x208b7,0x16088893,0x88b803,0x85813,0x7f87813,0x2437,0xf8840413,0x78b7,0x1b088893]
sym_block entry2 := symRun { noAlias := true } entry2Code (pcOf 45534) 32
theorem entry2_steps {im : Image} (hc : CodeAt im (pcOf 45534) entry2Code)
    (s : MachineState) (hp : s.pc=pcOf 45534) (raw : Nat) (hr : raw<128)
    (hraw : s.getMem (BitVec.ofNat 64 131432) >>> 0 &&& 127#64=BitVec.ofNat 64 raw) :
    ∃ t, Steps im s 9 9 t ∧ t.pc=pcOf 45543 ∧
      t.getReg .x16=BitVec.ofNat 64 raw ∧
      t.getReg .x8=BitVec.ofNat 64 8072 ∧
      t.getReg .x17=BitVec.ofNat 64 29104 ∧
      RegsExcept s t [.x6,.x8,.x16,.x17] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound entry2 hc s hp (by simp [entry2.res,rv_simp]),?_,?_,?_,?_,?_,?_⟩
  · simp [entry2.res,E.eval]
  · simp only [Result.toState_getReg,entry2.res]
    t3n []
    simpa using hraw
  · simp [entry2.res,rv_simp]
  · simp [entry2.res,rv_simp]
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn; simp [entry2.res,rv_simp]
def entry3Code : List (BitVec 32) := bv_list% 32 [0x208b7,0x16088893,0x88b803,0x685813,0x7f87813,0x187313,0x631313,0x185813,0x680833,0x2437,0xc3840413,0x78b7,0x28088893]
sym_block entry3 := symRun { noAlias := true } entry3Code (pcOf 45664) 32
theorem entry3_steps {im : Image} (hc : CodeAt im (pcOf 45664) entry3Code)
    (s : MachineState) (hp : s.pc=pcOf 45664) (raw : Nat) (hr : raw<128)
    (hraw : s.getMem (BitVec.ofNat 64 131432) >>> 6 &&& 127#64=BitVec.ofNat 64 raw) :
    ∃ t, Steps im s 13 13 t ∧ t.pc=pcOf 45677 ∧
      t.getReg .x16=BitVec.ofNat 64 (raw/2+64*(raw%2)) ∧
      t.getReg .x8=BitVec.ofNat 64 7224 ∧
      t.getReg .x17=BitVec.ofNat 64 29312 ∧
      RegsExcept s t [.x6,.x8,.x16,.x17] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound entry3 hc s hp (by simp [entry3.res,rv_simp]),?_,?_,?_,?_,?_,?_⟩
  · simp [entry3.res,E.eval]
  · simp only [Result.toState_getReg,entry3.res]
    t3n []
    have hraw' : s.getMem 131432#64 >>> 6 &&& 127#64=BitVec.ofNat 64 raw := hraw
    rw [hraw']
    exact rotate_raw raw hr
  · simp [entry3.res,rv_simp]
  · simp [entry3.res,rv_simp]
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn; simp [entry3.res,rv_simp]
def entry4Code : List (BitVec 32) := bv_list% 32 [0x208b7,0x16088893,0x108b803,0x85813,0x7f87813,0x2437,0x8e840413,0x78b7,0x35088893]
sym_block entry4 := symRun { noAlias := true } entry4Code (pcOf 45811) 32
theorem entry4_steps {im : Image} (hc : CodeAt im (pcOf 45811) entry4Code)
    (s : MachineState) (hp : s.pc=pcOf 45811) (raw : Nat) (hr : raw<128)
    (hraw : s.getMem (BitVec.ofNat 64 131440) >>> 0 &&& 127#64=BitVec.ofNat 64 raw) :
    ∃ t, Steps im s 9 9 t ∧ t.pc=pcOf 45820 ∧
      t.getReg .x16=BitVec.ofNat 64 raw ∧
      t.getReg .x8=BitVec.ofNat 64 6376 ∧
      t.getReg .x17=BitVec.ofNat 64 29520 ∧
      RegsExcept s t [.x6,.x8,.x16,.x17] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound entry4 hc s hp (by simp [entry4.res,rv_simp]),?_,?_,?_,?_,?_,?_⟩
  · simp [entry4.res,E.eval]
  · simp only [Result.toState_getReg,entry4.res]
    t3n []
    simpa using hraw
  · simp [entry4.res,rv_simp]
  · simp [entry4.res,rv_simp]
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn; simp [entry4.res,rv_simp]
def entry5Code : List (BitVec 32) := bv_list% 32 [0x208b7,0x16088893,0x108b803,0x685813,0x7f87813,0x187313,0x631313,0x185813,0x680833,0x1437,0x59840413,0x78b7,0x42088893]
sym_block entry5 := symRun { noAlias := true } entry5Code (pcOf 45941) 32
theorem entry5_steps {im : Image} (hc : CodeAt im (pcOf 45941) entry5Code)
    (s : MachineState) (hp : s.pc=pcOf 45941) (raw : Nat) (hr : raw<128)
    (hraw : s.getMem (BitVec.ofNat 64 131440) >>> 6 &&& 127#64=BitVec.ofNat 64 raw) :
    ∃ t, Steps im s 13 13 t ∧ t.pc=pcOf 45954 ∧
      t.getReg .x16=BitVec.ofNat 64 (raw/2+64*(raw%2)) ∧
      t.getReg .x8=BitVec.ofNat 64 5528 ∧
      t.getReg .x17=BitVec.ofNat 64 29728 ∧
      RegsExcept s t [.x6,.x8,.x16,.x17] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound entry5 hc s hp (by simp [entry5.res,rv_simp]),?_,?_,?_,?_,?_,?_⟩
  · simp [entry5.res,E.eval]
  · simp only [Result.toState_getReg,entry5.res]
    t3n []
    have hraw' : s.getMem 131440#64 >>> 6 &&& 127#64=BitVec.ofNat 64 raw := hraw
    rw [hraw']
    exact rotate_raw raw hr
  · simp [entry5.res,rv_simp]
  · simp [entry5.res,rv_simp]
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn; simp [entry5.res,rv_simp]
def entry6Code : List (BitVec 32) := bv_list% 32 [0x208b7,0x16088893,0x188b803,0x85813,0x7f87813,0x1437,0x24840413,0x78b7,0x4f088893]
sym_block entry6 := symRun { noAlias := true } entry6Code (pcOf 46088) 32
theorem entry6_steps {im : Image} (hc : CodeAt im (pcOf 46088) entry6Code)
    (s : MachineState) (hp : s.pc=pcOf 46088) (raw : Nat) (hr : raw<128)
    (hraw : s.getMem (BitVec.ofNat 64 131448) >>> 0 &&& 127#64=BitVec.ofNat 64 raw) :
    ∃ t, Steps im s 9 9 t ∧ t.pc=pcOf 46097 ∧
      t.getReg .x16=BitVec.ofNat 64 raw ∧
      t.getReg .x8=BitVec.ofNat 64 4680 ∧
      t.getReg .x17=BitVec.ofNat 64 29936 ∧
      RegsExcept s t [.x6,.x8,.x16,.x17] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound entry6 hc s hp (by simp [entry6.res,rv_simp]),?_,?_,?_,?_,?_,?_⟩
  · simp [entry6.res,E.eval]
  · simp only [Result.toState_getReg,entry6.res]
    t3n []
    simpa using hraw
  · simp [entry6.res,rv_simp]
  · simp [entry6.res,rv_simp]
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn; simp [entry6.res,rv_simp]
def entry7Code : List (BitVec 32) := bv_list% 32 [0x208b7,0x16088893,0x188b803,0x685813,0x7f87813,0x187313,0x631313,0x185813,0x680833,0x1437,0xef840413,0x78b7,0x5c088893]
sym_block entry7 := symRun { noAlias := true } entry7Code (pcOf 46218) 32
theorem entry7_steps {im : Image} (hc : CodeAt im (pcOf 46218) entry7Code)
    (s : MachineState) (hp : s.pc=pcOf 46218) (raw : Nat) (hr : raw<128)
    (hraw : s.getMem (BitVec.ofNat 64 131448) >>> 6 &&& 127#64=BitVec.ofNat 64 raw) :
    ∃ t, Steps im s 13 13 t ∧ t.pc=pcOf 46231 ∧
      t.getReg .x16=BitVec.ofNat 64 (raw/2+64*(raw%2)) ∧
      t.getReg .x8=BitVec.ofNat 64 3832 ∧
      t.getReg .x17=BitVec.ofNat 64 30144 ∧
      RegsExcept s t [.x6,.x8,.x16,.x17] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound entry7 hc s hp (by simp [entry7.res,rv_simp]),?_,?_,?_,?_,?_,?_⟩
  · simp [entry7.res,E.eval]
  · simp only [Result.toState_getReg,entry7.res]
    t3n []
    have hraw' : s.getMem 131448#64 >>> 6 &&& 127#64=BitVec.ofNat 64 raw := hraw
    rw [hraw']
    exact rotate_raw raw hr
  · simp [entry7.res,rv_simp]
  · simp [entry7.res,rv_simp]
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn; simp [entry7.res,rv_simp]
def entry8Code : List (BitVec 32) := bv_list% 32 [0x208b7,0x16088893,0x188b803,0x2585813,0x7f87813,0x187313,0x631313,0x185813,0x680833,0xcb040413,0x78b7,0x69088893]
sym_block entry8 := symRun { noAlias := true } entry8Code (pcOf 46364) 32
theorem entry8_steps {im : Image} (hc : CodeAt im (pcOf 46364) entry8Code)
    (s : MachineState) (hp : s.pc=pcOf 46364) (raw : Nat) (hr : raw<128)
    (hraw : s.getMem (BitVec.ofNat 64 131448) >>> 37 &&& 127#64=BitVec.ofNat 64 raw)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 3832) :
    ∃ t, Steps im s 12 12 t ∧ t.pc=pcOf 46376 ∧
      t.getReg .x16=BitVec.ofNat 64 (raw/2+64*(raw%2)) ∧
      t.getReg .x8=BitVec.ofNat 64 2984 ∧
      t.getReg .x17=BitVec.ofNat 64 30352 ∧
      RegsExcept s t [.x6,.x8,.x16,.x17] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound entry8 hc s hp (by simp [entry8.res,rv_simp]),?_,?_,?_,?_,?_,?_⟩
  · simp [entry8.res,E.eval]
  · simp only [Result.toState_getReg,entry8.res]
    t3n []
    have hraw' : s.getMem 131448#64 >>> 37 &&& 127#64=BitVec.ofNat 64 raw := hraw
    rw [hraw']
    exact rotate_raw raw hr
  · simp only [Result.toState_getReg,entry8.res]
    t3n [h8]
  · simp [entry8.res,rv_simp]
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn; simp [entry8.res,rv_simp]
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
def planCode : List (BitVec 32) := bv_list% 32 [0x1f87913,0x291313,0x690933,0xff9337,0xf9030313,0x690933]
sym_block plan0 := symRun { noAlias := true } planCode (pcOf 45300) 20
sym_block plan1 := symRun { noAlias := true } planCode (pcOf 45434) 20
sym_block plan2 := symRun { noAlias := true } planCode (pcOf 45577) 20
sym_block plan3 := symRun { noAlias := true } planCode (pcOf 45711) 20
sym_block plan4 := symRun { noAlias := true } planCode (pcOf 45854) 20
sym_block plan5 := symRun { noAlias := true } planCode (pcOf 45988) 20
sym_block plan6 := symRun { noAlias := true } planCode (pcOf 46131) 20
sym_block plan7 := symRun { noAlias := true } planCode (pcOf 46265) 20
sym_block plan8 := symRun { noAlias := true } planCode (pcOf 46410) 20
theorem plan_run {b : Nat} (hb : b=45300 ∨ b=45434 ∨ b=45577 ∨ b=45711 ∨ b=45854 ∨ b=45988 ∨ b=46131 ∨ b=46265 ∨ b=46410) :
    symRun { noAlias := true } planCode (pcOf b) 20 = some
      ⟨plan0.res.st,.c (pcOf (b+6)),plan0.res.stop,plan0.res.steps,plan0.res.cycles⟩ := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact plan0.trans (congrArg some (by kernel_rfl))
  · exact plan1.trans (congrArg some (by kernel_rfl))
  · exact plan2.trans (congrArg some (by kernel_rfl))
  · exact plan3.trans (congrArg some (by kernel_rfl))
  · exact plan4.trans (congrArg some (by kernel_rfl))
  · exact plan5.trans (congrArg some (by kernel_rfl))
  · exact plan6.trans (congrArg some (by kernel_rfl))
  · exact plan7.trans (congrArg some (by kernel_rfl))
  · exact plan8.trans (congrArg some (by kernel_rfl))
theorem plan_steps {im : Image} {b : Nat} (hb : b=45300 ∨ b=45434 ∨ b=45577 ∨ b=45711 ∨ b=45854 ∨ b=45988 ∨ b=46131 ∨ b=46265 ∨ b=46410)
    (hc : CodeAt im (pcOf b) planCode) (s : MachineState) (hp : s.pc=pcOf b)
    (child : Nat) (hchild : child<128) (h16 : s.getReg .x16=BitVec.ofNat 64 child) :
    ∃ t, Steps im s 6 6 t ∧ t.pc=pcOf (b+6) ∧
      t.getReg .x18=BitVec.ofNat 64 (16748432+5*(child%32)) ∧
      RegsExcept s t [.x6,.x18] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (plan_run hb) hc s hp (by simp [plan0.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [Result.toState_pc,E.eval]
  · simp only [Result.toState_getReg,plan0.res]
    t3n [h16]
    have hm : BitVec.ofNat 64 child &&& 31#64 = BitVec.ofNat 64 (child%32) := by
      simpa using SigGolfCandidate.T3M.Sign.ofNat_and_mask child 5 (by decide)
    rw [hm,ofNat_shl]
    simp only [ofNat_add_ofNat]
    congr 1
    norm_num
    omega
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn; simp [plan0.res,rv_simp]
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
structure ValuesCode (im : Image) (b : Nat) : Prop where
  value0 : CodeAt im (pcOf (b+0)) value0Code
  value1 : CodeAt im (pcOf (b+4)) value1Code
  value2 : CodeAt im (pcOf (b+10)) value2Code
  value3 : CodeAt im (pcOf (b+16)) value3Code
  value4 : CodeAt im (pcOf (b+22)) value4Code
  value5 : CodeAt im (pcOf (b+28)) value5Code
def ValuesW (region A : Nat) : Prop :=
  ∃ i<6, A=region+(640+40*(i-(i-1))+72*(i/5)-52*i-124*(i%2)) ∨ A=region+(640+40*(i-(i-1))+72*(i/5)-52*i-124*(i%2)+8) ∨
    (0 < i ∧ (A=region+672+16*i ∨ A=region+680+16*i))
theorem values_steps {im : Image} {b : Nat} (hb : b=45266 ∨ b=45400 ∨ b=45543 ∨ b=45677 ∨ b=45820 ∨ b=45954 ∨ b=46097 ∨ b=46231 ∨ b=46376) (hc : ValuesCode im b)
    (s : MachineState) (hp : s.pc=pcOf b) (region source : Nat)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h17 : s.getReg .x17=BitVec.ofNat 64 source) :
    ∃ t, Steps im s 34 34 t ∧ t.pc=pcOf (b+34) ∧
      (∀ i<6,∀ half<2,t.getMem (BitVec.ofNat 64 (region+(640+40*(i-(i-1))+72*(i/5)-52*i-124*(i%2))+8*half))=
        s.getMem (BitVec.ofNat 64 (source+16*i+8*half))) ∧
      (∀ i<6,0 < i → ∀ half<2,t.getMem (BitVec.ofNat 64 (region+672+16*i+8*half))=
        s.getMem (BitVec.ofNat 64 (source+16*i+8*half))) ∧
      RegsExcept s t [.x6,.x7] ∧ Frame s t (ValuesW region) := by
  obtain ⟨t0,st0,p0,v0lo,v0hi,r0,f0⟩ := value0_steps (b:=b+0) (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp) hc.value0 s (by simpa using hp) region source hr0 hr1 hra hs0 hs1 hsa h8 h17
  have fw0 : Frame s t0 (ValuesW region) := f0.mono (by
    intro A hA h
    refine ⟨0,by decide,?_⟩
    omega)
  have r00 := r0
  have f00 := fw0
  obtain ⟨t1,st1,p1,v1lo,v1hi,l1lo,l1hi,r1,f1⟩ := value1_steps (b:=b+4) (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp) hc.value1 t0 (by simpa using p0) region source hr0 hr1 hra hs0 hs1 hsa (by rw [r00.get (by simp),h8]) (by rw [r00.get (by simp),h17])
  have fw1 : Frame t0 t1 (ValuesW region) := f1.mono (by
    intro A hA h
    refine ⟨1,by decide,?_⟩
    omega)
  have r01 : RegsExcept s t1 [.x6,.x7] := (r00.trans r1).mono (by simp)
  have f01 : Frame s t1 (ValuesW region) := (f00.trans fw1).mono (by intro A hA h; exact h.elim id id)
  rw [f00.get (A:=source+16) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at v1lo
  rw [f00.get (A:=source+24) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at v1hi
  rw [f00.get (A:=source+16) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at l1lo
  rw [f00.get (A:=source+24) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at l1hi
  obtain ⟨t2,st2,p2,v2lo,v2hi,l2lo,l2hi,r2,f2⟩ := value2_steps (b:=b+10) (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp) hc.value2 t1 (by simpa using p1) region source hr0 hr1 hra hs0 hs1 hsa (by rw [r01.get (by simp),h8]) (by rw [r01.get (by simp),h17])
  have fw2 : Frame t1 t2 (ValuesW region) := f2.mono (by
    intro A hA h
    refine ⟨2,by decide,?_⟩
    omega)
  have r02 : RegsExcept s t2 [.x6,.x7] := (r01.trans r2).mono (by simp)
  have f02 : Frame s t2 (ValuesW region) := (f01.trans fw2).mono (by intro A hA h; exact h.elim id id)
  rw [f01.get (A:=source+32) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at v2lo
  rw [f01.get (A:=source+40) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at v2hi
  rw [f01.get (A:=source+32) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at l2lo
  rw [f01.get (A:=source+40) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at l2hi
  obtain ⟨t3,st3,p3,v3lo,v3hi,l3lo,l3hi,r3,f3⟩ := value3_steps (b:=b+16) (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp) hc.value3 t2 (by simpa using p2) region source hr0 hr1 hra hs0 hs1 hsa (by rw [r02.get (by simp),h8]) (by rw [r02.get (by simp),h17])
  have fw3 : Frame t2 t3 (ValuesW region) := f3.mono (by
    intro A hA h
    refine ⟨3,by decide,?_⟩
    omega)
  have r03 : RegsExcept s t3 [.x6,.x7] := (r02.trans r3).mono (by simp)
  have f03 : Frame s t3 (ValuesW region) := (f02.trans fw3).mono (by intro A hA h; exact h.elim id id)
  rw [f02.get (A:=source+48) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at v3lo
  rw [f02.get (A:=source+56) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at v3hi
  rw [f02.get (A:=source+48) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at l3lo
  rw [f02.get (A:=source+56) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at l3hi
  obtain ⟨t4,st4,p4,v4lo,v4hi,l4lo,l4hi,r4,f4⟩ := value4_steps (b:=b+22) (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp) hc.value4 t3 (by simpa using p3) region source hr0 hr1 hra hs0 hs1 hsa (by rw [r03.get (by simp),h8]) (by rw [r03.get (by simp),h17])
  have fw4 : Frame t3 t4 (ValuesW region) := f4.mono (by
    intro A hA h
    refine ⟨4,by decide,?_⟩
    omega)
  have r04 : RegsExcept s t4 [.x6,.x7] := (r03.trans r4).mono (by simp)
  have f04 : Frame s t4 (ValuesW region) := (f03.trans fw4).mono (by intro A hA h; exact h.elim id id)
  rw [f03.get (A:=source+64) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at v4lo
  rw [f03.get (A:=source+72) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at v4hi
  rw [f03.get (A:=source+64) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at l4lo
  rw [f03.get (A:=source+72) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at l4hi
  obtain ⟨t5,st5,p5,v5lo,v5hi,l5lo,l5hi,r5,f5⟩ := value5_steps (b:=b+28) (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp) hc.value5 t4 (by simpa using p4) region source hr0 hr1 hra hs0 hs1 hsa (by rw [r04.get (by simp),h8]) (by rw [r04.get (by simp),h17])
  have fw5 : Frame t4 t5 (ValuesW region) := f5.mono (by
    intro A hA h
    refine ⟨5,by decide,?_⟩
    omega)
  have r05 : RegsExcept s t5 [.x6,.x7] := (r04.trans r5).mono (by simp)
  have f05 : Frame s t5 (ValuesW region) := (f04.trans fw5).mono (by intro A hA h; exact h.elim id id)
  rw [f04.get (A:=source+80) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at v5lo
  rw [f04.get (A:=source+88) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at v5hi
  rw [f04.get (A:=source+80) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at l5lo
  rw [f04.get (A:=source+88) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at l5hi
  have tail4 : Frame t4 t5 (ValuesW region) := fw5
  have exactTail4 := f5
  have tail3 : Frame t3 t5 (ValuesW region) := (fw4.trans tail4).mono (by intro A hA h; exact h.elim id id)
  have exactTail3 := (f4.trans f5)
  have tail2 : Frame t2 t5 (ValuesW region) := (fw3.trans tail3).mono (by intro A hA h; exact h.elim id id)
  have exactTail2 := ((f3.trans f4).trans f5)
  have tail1 : Frame t1 t5 (ValuesW region) := (fw2.trans tail2).mono (by intro A hA h; exact h.elim id id)
  have exactTail1 := (((f2.trans f3).trans f4).trans f5)
  have tail0 : Frame t0 t5 (ValuesW region) := (fw1.trans tail1).mono (by intro A hA h; exact h.elim id id)
  have exactTail0 := ((((f1.trans f2).trans f3).trans f4).trans f5)
  refine ⟨t5,(((((st0.trans st1).trans st2).trans st3).trans st4).trans st5),by simpa using p5,?_,?_,r05,f05⟩
  · intro i hi half hh
    interval_cases i <;> interval_cases half
    · rw [exactTail0.get (by omega) (by omega)]
      simpa using v0lo
    · rw [exactTail0.get (by omega) (by omega)]
      simpa using v0hi
    · rw [exactTail1.get (by omega) (by omega)]
      simpa using v1lo
    · rw [exactTail1.get (by omega) (by omega)]
      simpa using v1hi
    · rw [exactTail2.get (by omega) (by omega)]
      simpa using v2lo
    · rw [exactTail2.get (by omega) (by omega)]
      simpa using v2hi
    · rw [exactTail3.get (by omega) (by omega)]
      simpa using v3lo
    · rw [exactTail3.get (by omega) (by omega)]
      simpa using v3hi
    · rw [exactTail4.get (by omega) (by omega)]
      simpa using v4lo
    · rw [exactTail4.get (by omega) (by omega)]
      simpa using v4hi
    · simpa using v5lo
    · simpa using v5hi
  · intro i hi hz half hh
    have hp : 1 ≤ i := by omega
    interval_cases i <;> interval_cases half
    · rw [exactTail1.get (by omega) (by omega)]
      simpa using l1lo
    · rw [exactTail1.get (by omega) (by omega)]
      simpa using l1hi
    · rw [exactTail2.get (by omega) (by omega)]
      simpa using l2lo
    · rw [exactTail2.get (by omega) (by omega)]
      simpa using l2hi
    · rw [exactTail3.get (by omega) (by omega)]
      simpa using l3lo
    · rw [exactTail3.get (by omega) (by omega)]
      simpa using l3hi
    · rw [exactTail4.get (by omega) (by omega)]
      simpa using l4lo
    · rw [exactTail4.get (by omega) (by omega)]
      simpa using l4hi
    · simpa using l5lo
    · simpa using l5hi
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
def PathsW (dst : Nat → Nat) (n A : Nat) : Prop := ∃ i < n, A=dst i ∨ A=dst i+8
structure PathsInv (s : MachineState) (b source : Nat) (dst : Nat → Nat) (n : Nat) (t : MachineState) : Prop where
  pc : t.pc=pcOf (b+14*n)
  regs : RegsExcept s t [.x6,.x7,.x28]
  frame : Frame s t (PathsW dst n)
  reads : ∀ i<n,∀ half<2,t.getMem (BitVec.ofNat 64 (dst i+8*half))=
    s.getMem (BitVec.ofNat 64 (source+96+16*i+8*half))
theorem paths_join {im : Image} (s : MachineState) (b source : Nat) (dst : Nat → Nat)
    (hp : s.pc=pcOf b) (hd : ∀ j<5,dst j+16<2^64)
    (hdis : ∀ i<5,∀ j<5,i≠j → dst i+16≤dst j ∨ dst j+16≤dst i)
    (hstep : ∀ j<5,∀ u,PathsInv s b source dst j u →
      ∃ t,Steps im u 14 17 t ∧ t.pc=pcOf (b+14*(j+1)) ∧
        (∀ half<2,t.getMem (BitVec.ofNat 64 (dst j+8*half))=
          s.getMem (BitVec.ofNat 64 (source+96+16*j+8*half))) ∧
        RegsExcept u t [.x6,.x7,.x28] ∧ Frame u t (fun A=>A=dst j ∨ A=dst j+8)) :
    ∃ t,Steps im s 70 85 t ∧ PathsInv s b source dst 5 t := by
  have run : ∀ n,n≤5 → ∃ t,Steps im s (14*n) (17*n) t ∧ PathsInv s b source dst n t := by
    intro n
    induction n with
    | zero =>
      intro hn
      refine ⟨s,Steps.refl _,?_,RegsExcept.refl _ _,Frame.refl _ _,?_⟩
      · simpa using hp
      · intro i hi; omega
    | succ n ih =>
      intro hn
      obtain ⟨u,su,hu⟩:=ih (by omega)
      obtain ⟨t,st,tp,tr,rr,ff⟩:=hstep n (by omega) u hu
      refine ⟨t,(su.trans st).of_eq (by omega) (by omega),tp,?_,?_,?_⟩
      · exact (hu.regs.trans rr).mono (by simp)
      · exact (hu.frame.trans ff).mono (by
          intro A hA h
          rcases h with h | h
          · obtain ⟨i,hi,h⟩:=h;exact ⟨i,by omega,h⟩
          · exact ⟨n,by omega,h⟩)
      · intro i hi half hh
        by_cases he:i=n
        · subst i;exact tr half hh
        · have hin:i<n:=by omega
          have hsep:=hdis i (by omega) n (by omega) he
          have hbound:=hd i (by omega)
          rw [ff.get (by omega) (by omega)]
          exact hu.reads i hin half hh
  exact run 5 (by omega)
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
theorem path_cell0 {im : Image} {b : Nat} (hb : b=45306 ∨ b=45440 ∨ b=45583 ∨ b=45717 ∨ b=45860 ∨ b=45994 ∨ b=46137 ∨ b=46271 ∨ b=46416)
    (hlc : CodeAt im (pcOf b) [609795]) (hpc : CodeAt im (pcOf (b+1)) pathCode0)
    (s : MachineState) (hp : s.pc=pcOf b) (region source child table slot : Nat)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (hj : child<128) (hbnd : slot<53) (ht : table+5<2^24)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h16 : s.getReg .x16=BitVec.ofNat 64 child)
    (h17 : s.getReg .x17=BitVec.ofNat 64 source) (h18 : s.getReg .x18=BitVec.ofNat 64 table)
    (hbyte : s.getByte (BitVec.ofNat 64 (table+0))=BitVec.ofNat 8 slot) :
    ∃ t, Steps im s 14 17 t ∧ t.pc=pcOf (b+14) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child/1))) =
        s.getMem (BitVec.ofNat 64 (source+96)) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child/1)+8)) =
        s.getMem (BitVec.ofNat 64 (source+104)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A=destination region slot (child/1) ∨ A=destination region slot (child/1)+8) := by
  obtain ⟨u,su,upc,u28,ur,uf⟩ := load_plan_step (pcOf b) hlc ⟨0,by decide⟩ (by kernel_rfl)
    s hp table slot ht hbnd h18 hbyte
  have upc' : u.pc=pcOf (b+1) := by rw [upc]; simp [pcOf,Nat.mul_add,ofNat_add_ofNat,Nat.add_assoc]
  obtain ⟨t,st,tpc,tlo,thi,tr,tf⟩ := path0_steps_rebased (b:=b+1)
    (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp) hpc u upc'
    region source child slot hr0 hr1 hra hs0 hs1 hsa hj hbnd
    (by rw [ur.get (by decide),h8]) (by rw [ur.get (by decide),h16])
    (by rw [ur.get (by decide),h17]) u28
  refine ⟨t,su.trans st,by simpa [Nat.add_assoc] using tpc,?_,?_,?_,?_⟩
  · rw [uf.get (by omega) (fun h => h)] at tlo
    simpa using tlo
  · rw [uf.get (by omega) (fun h => h)] at thi
    simpa using thi
  · exact (ur.trans tr).mono (by simp)
  · exact (uf.trans tf).mono (fun A _ h => by simpa using h)
theorem path_cell1 {im : Image} {b : Nat} (hb : b=45320 ∨ b=45454 ∨ b=45597 ∨ b=45731 ∨ b=45874 ∨ b=46008 ∨ b=46151 ∨ b=46285 ∨ b=46430)
    (hlc : CodeAt im (pcOf b) [1658371]) (hpc : CodeAt im (pcOf (b+1)) pathCode1)
    (s : MachineState) (hp : s.pc=pcOf b) (region source child table slot : Nat)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (hj : child<128) (hbnd : slot<53) (ht : table+5<2^24)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h16 : s.getReg .x16=BitVec.ofNat 64 child)
    (h17 : s.getReg .x17=BitVec.ofNat 64 source) (h18 : s.getReg .x18=BitVec.ofNat 64 table)
    (hbyte : s.getByte (BitVec.ofNat 64 (table+1))=BitVec.ofNat 8 slot) :
    ∃ t, Steps im s 14 17 t ∧ t.pc=pcOf (b+14) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child/2))) =
        s.getMem (BitVec.ofNat 64 (source+112)) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child/2)+8)) =
        s.getMem (BitVec.ofNat 64 (source+120)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A=destination region slot (child/2) ∨ A=destination region slot (child/2)+8) := by
  obtain ⟨u,su,upc,u28,ur,uf⟩ := load_plan_step (pcOf b) hlc ⟨1,by decide⟩ (by kernel_rfl)
    s hp table slot ht hbnd h18 hbyte
  have upc' : u.pc=pcOf (b+1) := by rw [upc]; simp [pcOf,Nat.mul_add,ofNat_add_ofNat,Nat.add_assoc]
  obtain ⟨t,st,tpc,tlo,thi,tr,tf⟩ := path1_steps_rebased (b:=b+1)
    (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp) hpc u upc'
    region source child slot hr0 hr1 hra hs0 hs1 hsa hj hbnd
    (by rw [ur.get (by decide),h8]) (by rw [ur.get (by decide),h16])
    (by rw [ur.get (by decide),h17]) u28
  refine ⟨t,su.trans st,by simpa [Nat.add_assoc] using tpc,?_,?_,?_,?_⟩
  · rw [uf.get (by omega) (fun h => h)] at tlo
    simpa using tlo
  · rw [uf.get (by omega) (fun h => h)] at thi
    simpa using thi
  · exact (ur.trans tr).mono (by simp)
  · exact (uf.trans tf).mono (fun A _ h => by simpa using h)
theorem path_cell2 {im : Image} {b : Nat} (hb : b=45334 ∨ b=45468 ∨ b=45611 ∨ b=45745 ∨ b=45888 ∨ b=46022 ∨ b=46165 ∨ b=46299 ∨ b=46444)
    (hlc : CodeAt im (pcOf b) [2706947]) (hpc : CodeAt im (pcOf (b+1)) pathCode2)
    (s : MachineState) (hp : s.pc=pcOf b) (region source child table slot : Nat)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (hj : child<128) (hbnd : slot<53) (ht : table+5<2^24)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h16 : s.getReg .x16=BitVec.ofNat 64 child)
    (h17 : s.getReg .x17=BitVec.ofNat 64 source) (h18 : s.getReg .x18=BitVec.ofNat 64 table)
    (hbyte : s.getByte (BitVec.ofNat 64 (table+2))=BitVec.ofNat 8 slot) :
    ∃ t, Steps im s 14 17 t ∧ t.pc=pcOf (b+14) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child/4))) =
        s.getMem (BitVec.ofNat 64 (source+128)) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child/4)+8)) =
        s.getMem (BitVec.ofNat 64 (source+136)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A=destination region slot (child/4) ∨ A=destination region slot (child/4)+8) := by
  obtain ⟨u,su,upc,u28,ur,uf⟩ := load_plan_step (pcOf b) hlc ⟨2,by decide⟩ (by kernel_rfl)
    s hp table slot ht hbnd h18 hbyte
  have upc' : u.pc=pcOf (b+1) := by rw [upc]; simp [pcOf,Nat.mul_add,ofNat_add_ofNat,Nat.add_assoc]
  obtain ⟨t,st,tpc,tlo,thi,tr,tf⟩ := path2_steps_rebased (b:=b+1)
    (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp) hpc u upc'
    region source child slot hr0 hr1 hra hs0 hs1 hsa hj hbnd
    (by rw [ur.get (by decide),h8]) (by rw [ur.get (by decide),h16])
    (by rw [ur.get (by decide),h17]) u28
  refine ⟨t,su.trans st,by simpa [Nat.add_assoc] using tpc,?_,?_,?_,?_⟩
  · rw [uf.get (by omega) (fun h => h)] at tlo
    simpa using tlo
  · rw [uf.get (by omega) (fun h => h)] at thi
    simpa using thi
  · exact (ur.trans tr).mono (by simp)
  · exact (uf.trans tf).mono (fun A _ h => by simpa using h)
theorem path_cell3 {im : Image} {b : Nat} (hb : b=45348 ∨ b=45482 ∨ b=45625 ∨ b=45759 ∨ b=45902 ∨ b=46036 ∨ b=46179 ∨ b=46313 ∨ b=46458)
    (hlc : CodeAt im (pcOf b) [3755523]) (hpc : CodeAt im (pcOf (b+1)) pathCode3)
    (s : MachineState) (hp : s.pc=pcOf b) (region source child table slot : Nat)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (hj : child<128) (hbnd : slot<53) (ht : table+5<2^24)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h16 : s.getReg .x16=BitVec.ofNat 64 child)
    (h17 : s.getReg .x17=BitVec.ofNat 64 source) (h18 : s.getReg .x18=BitVec.ofNat 64 table)
    (hbyte : s.getByte (BitVec.ofNat 64 (table+3))=BitVec.ofNat 8 slot) :
    ∃ t, Steps im s 14 17 t ∧ t.pc=pcOf (b+14) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child/8))) =
        s.getMem (BitVec.ofNat 64 (source+144)) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child/8)+8)) =
        s.getMem (BitVec.ofNat 64 (source+152)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A=destination region slot (child/8) ∨ A=destination region slot (child/8)+8) := by
  obtain ⟨u,su,upc,u28,ur,uf⟩ := load_plan_step (pcOf b) hlc ⟨3,by decide⟩ (by kernel_rfl)
    s hp table slot ht hbnd h18 hbyte
  have upc' : u.pc=pcOf (b+1) := by rw [upc]; simp [pcOf,Nat.mul_add,ofNat_add_ofNat,Nat.add_assoc]
  obtain ⟨t,st,tpc,tlo,thi,tr,tf⟩ := path3_steps_rebased (b:=b+1)
    (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp) hpc u upc'
    region source child slot hr0 hr1 hra hs0 hs1 hsa hj hbnd
    (by rw [ur.get (by decide),h8]) (by rw [ur.get (by decide),h16])
    (by rw [ur.get (by decide),h17]) u28
  refine ⟨t,su.trans st,by simpa [Nat.add_assoc] using tpc,?_,?_,?_,?_⟩
  · rw [uf.get (by omega) (fun h => h)] at tlo
    simpa using tlo
  · rw [uf.get (by omega) (fun h => h)] at thi
    simpa using thi
  · exact (ur.trans tr).mono (by simp)
  · exact (uf.trans tf).mono (fun A _ h => by simpa using h)
theorem path_cell4 {im : Image} {b : Nat} (hb : b=45362 ∨ b=45496 ∨ b=45639 ∨ b=45773 ∨ b=45916 ∨ b=46050 ∨ b=46193 ∨ b=46327 ∨ b=46472)
    (hlc : CodeAt im (pcOf b) [4804099]) (hpc : CodeAt im (pcOf (b+1)) pathCode4)
    (s : MachineState) (hp : s.pc=pcOf b) (region source child table slot : Nat)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (hj : child<128) (hbnd : slot<53) (ht : table+5<2^24)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h16 : s.getReg .x16=BitVec.ofNat 64 child)
    (h17 : s.getReg .x17=BitVec.ofNat 64 source) (h18 : s.getReg .x18=BitVec.ofNat 64 table)
    (hbyte : s.getByte (BitVec.ofNat 64 (table+4))=BitVec.ofNat 8 slot) :
    ∃ t, Steps im s 14 17 t ∧ t.pc=pcOf (b+14) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child/16))) =
        s.getMem (BitVec.ofNat 64 (source+160)) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child/16)+8)) =
        s.getMem (BitVec.ofNat 64 (source+168)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A=destination region slot (child/16) ∨ A=destination region slot (child/16)+8) := by
  obtain ⟨u,su,upc,u28,ur,uf⟩ := load_plan_step (pcOf b) hlc ⟨4,by decide⟩ (by kernel_rfl)
    s hp table slot ht hbnd h18 hbyte
  have upc' : u.pc=pcOf (b+1) := by rw [upc]; simp [pcOf,Nat.mul_add,ofNat_add_ofNat,Nat.add_assoc]
  obtain ⟨t,st,tpc,tlo,thi,tr,tf⟩ := path4_steps_rebased (b:=b+1)
    (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp) hpc u upc'
    region source child slot hr0 hr1 hra hs0 hs1 hsa hj hbnd
    (by rw [ur.get (by decide),h8]) (by rw [ur.get (by decide),h16])
    (by rw [ur.get (by decide),h17]) u28
  refine ⟨t,su.trans st,by simpa [Nat.add_assoc] using tpc,?_,?_,?_,?_⟩
  · rw [uf.get (by omega) (fun h => h)] at tlo
    simpa using tlo
  · rw [uf.get (by omega) (fun h => h)] at thi
    simpa using thi
  · exact (ur.trans tr).mono (by simp)
  · exact (uf.trans tf).mono (fun A _ h => by simpa using h)
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter.Packing
open SigGolfCandidate.Research.SharedPathPacking
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- The copied siblings occupy separate aligned digest slots and leave both carried pads intact
(C1, stage 1: the carried R pad of the pinned level-four window `X = 128` is at `+160`). -/
def ScatterSafe (child : Nat) : Prop :=
  (∀ l : Fin 5, block child l.val % 16 = 0 ∧ block child l.val / 16 < 53 ∧
    sibling child l.val + 16 ≤ 320 ∧ sibling child l.val ≠ 160) ∧
  (∀ i l : Fin 5, i ≠ l → sibling child i.val + 16 ≤ sibling child l.val ∨
    sibling child l.val + 16 ≤ sibling child i.val)
theorem scatterSafe : ∀ child : Fin 128, ScatterSafe child.val := by
  intro child
  fin_cases child <;> unfold ScatterSafe <;> decide +kernel

theorem slots_bound (child : Fin 128) (l : Fin 5) : block child.val l.val / 16 < 53 :=
  ((scatterSafe child).1 l).2.1

theorem block_reassemble (child : Fin 128) (l : Fin 5) :
    16 * (block child.val l.val / 16) = block child.val l.val := by
  have h:=((scatterSafe child).1 l).1
  omega

end ClaudeWCT.W9.Machine.Expand.SharedScatter.Packing

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter.Packing
open SigGolfCandidate.Research.SharedPathPacking
set_option maxRecDepth 100000
set_option maxHeartbeats 0
end ClaudeWCT.W9.Machine.Expand.SharedScatter.Packing

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
def pathWords (j : Fin 5) : List (BitVec 32) :=
  match j.val with | 0=>pathCode0 | 1=>pathCode1 | 2=>pathCode2 | 3=>pathCode3 | _=>pathCode4
structure PathsCode (im : Image) (b : Nat) : Prop where
  load : ∀ j : Fin 5,CodeAt im (pcOf (b+14*j.val)) [BitVec.ofNat 32 (609795+1048576*j.val)]
  path : ∀ j : Fin 5,CodeAt im (pcOf (b+14*j.val+1)) (pathWords j)
theorem path_cell {im : Image} {b : Nat} (hb : b=45306 ∨ b=45440 ∨ b=45583 ∨ b=45717 ∨ b=45860 ∨ b=45994 ∨ b=46137 ∨ b=46271 ∨ b=46416)
    (hc : PathsCode im b) (j : Fin 5)
    (s : MachineState) (hp : s.pc=pcOf (b+14*j.val)) (region source child table slot : Nat)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (hj : child<128) (hbnd : slot<53) (ht : table+5<2^24)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h16 : s.getReg .x16=BitVec.ofNat 64 child)
    (h17 : s.getReg .x17=BitVec.ofNat 64 source) (h18 : s.getReg .x18=BitVec.ofNat 64 table)
    (hbyte : s.getByte (BitVec.ofNat 64 (table+j.val))=BitVec.ofNat 8 slot) :
    ∃ t,Steps im s 14 17 t ∧ t.pc=pcOf (b+14*(j.val+1)) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child/2^j.val)))=
        s.getMem (BitVec.ofNat 64 (source+96+16*j.val)) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child/2^j.val)+8))=
        s.getMem (BitVec.ofNat 64 (source+96+16*j.val+8)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A=>A=destination region slot (child/2^j.val) ∨ A=destination region slot (child/2^j.val)+8) := by
  fin_cases j
  · simpa [Nat.mul_add,Nat.mul_one,Nat.add_assoc] using
      path_cell0 (b:=b+14*0) (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
        (hc.load ⟨0,by decide⟩) (by simpa [pathWords] using hc.path ⟨0,by decide⟩) s hp region source child table slot
        hr0 hr1 hra hs0 hs1 hsa hj hbnd ht h8 h16 h17 h18 hbyte
  · simpa [Nat.mul_add,Nat.mul_one,Nat.add_assoc] using
      path_cell1 (b:=b+14*1) (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
        (hc.load ⟨1,by decide⟩) (by simpa [pathWords] using hc.path ⟨1,by decide⟩) s hp region source child table slot
        hr0 hr1 hra hs0 hs1 hsa hj hbnd ht h8 h16 h17 h18 hbyte
  · simpa [Nat.mul_add,Nat.mul_one,Nat.add_assoc] using
      path_cell2 (b:=b+14*2) (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
        (hc.load ⟨2,by decide⟩) (by simpa [pathWords] using hc.path ⟨2,by decide⟩) s hp region source child table slot
        hr0 hr1 hra hs0 hs1 hsa hj hbnd ht h8 h16 h17 h18 hbyte
  · simpa [Nat.mul_add,Nat.mul_one,Nat.add_assoc] using
      path_cell3 (b:=b+14*3) (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
        (hc.load ⟨3,by decide⟩) (by simpa [pathWords] using hc.path ⟨3,by decide⟩) s hp region source child table slot
        hr0 hr1 hra hs0 hs1 hsa hj hbnd ht h8 h16 h17 h18 hbyte
  · simpa [Nat.mul_add,Nat.mul_one,Nat.add_assoc] using
      path_cell4 (b:=b+14*4) (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
        (hc.load ⟨4,by decide⟩) (by simpa [pathWords] using hc.path ⟨4,by decide⟩) s hp region source child table slot
        hr0 hr1 hra hs0 hs1 hsa hj hbnd ht h8 h16 h17 h18 hbyte

end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
def pathDestination (region child : Nat) (slots : Nat → Nat) (j : Nat) : Nat :=
  destination region (slots j) (child/2^j)
theorem five_paths {im : Image} {b : Nat}
    (hb : b=45306 ∨ b=45440 ∨ b=45583 ∨ b=45717 ∨ b=45860 ∨ b=45994 ∨ b=46137 ∨ b=46271 ∨ b=46416)
    (hc : PathsCode im b) (s : MachineState) (hp : s.pc=pcOf b)
    (region source child table : Nat) (slots : Nat → Nat)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (hchild : child<128) (ht0 : 11048 ≤ table) (ht1 : table+5<2^24)
    (hslots : ∀j<5,slots j<53)
    (hdis : ∀i<5,∀j<5,i ≠ j → pathDestination region child slots i+16 ≤ pathDestination region child slots j ∨
      pathDestination region child slots j+16 ≤ pathDestination region child slots i)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h16 : s.getReg .x16=BitVec.ofNat 64 child)
    (h17 : s.getReg .x17=BitVec.ofNat 64 source) (h18 : s.getReg .x18=BitVec.ofNat 64 table)
    (hbytes : ∀j<5,s.getByte (BitVec.ofNat 64 (table+j))=BitVec.ofNat 8 (slots j)) :
    ∃ t,Steps im s 70 85 t ∧ PathsInv s b source (pathDestination region child slots) 5 t := by
  have hdst : ∀j<5,pathDestination region child slots j+16 ≤ 11048 := by
    intro j hj
    have hs:=hslots j hj
    unfold pathDestination destination
    omega
  apply paths_join s b source (pathDestination region child slots) hp
    (fun j hj=>by have:=hdst j hj;omega) hdis
  intro j hj u hu
  have ub : u.getByte (BitVec.ofNat 64 (table+j))=BitVec.ofNat 8 (slots j) := by
    rw [hu.frame.getByte (by omega) (by
      rintro ⟨i,hi,h⟩
      have hd:=hdst i (by omega)
      omega)]
    exact hbytes j hj
  obtain ⟨t,st,tp,tlo,thi,tr,tf⟩:=path_cell hb hc ⟨j,hj⟩ u hu.pc region source child table (slots j)
    hr0 hr1 hra hs0 hs1 hsa hchild (hslots j hj) ht1
    (by rw [hu.regs.get (by decide),h8]) (by rw [hu.regs.get (by decide),h16])
    (by rw [hu.regs.get (by decide),h17]) (by rw [hu.regs.get (by decide),h18]) ub
  have oldlo : u.getMem (BitVec.ofNat 64 (source+96+16*j))=s.getMem (BitVec.ofNat 64 (source+96+16*j)) :=
    hu.frame.get (by omega) (by
      rintro ⟨i,hi,h⟩;have hd:=hdst i (by omega);omega)
  have oldhi : u.getMem (BitVec.ofNat 64 (source+96+16*j+8))=s.getMem (BitVec.ofNat 64 (source+96+16*j+8)) :=
    hu.frame.get (by omega) (by
      rintro ⟨i,hi,h⟩;have hd:=hdst i (by omega);omega)
  rw [oldlo] at tlo
  rw [oldhi] at thi
  refine ⟨t,st,tp,?_,tr,tf⟩
  intro half hh
  interval_cases half
  · simpa [pathDestination] using tlo
  · simpa [pathDestination] using thi
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter.Packing
open SigGolfCandidate.Research.SharedPathPacking
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
theorem path_slot (region : Nat) (child : Fin 128) (level : Fin 5) :
    destination region (block child.val level.val / 16) (child.val / 2^level.val) =
      region + sibling child.val level.val := by
  unfold destination sibling bitAt
  rw [block_reassemble child level]
  omega

theorem path_slots_disjoint (region : Nat) (child : Fin 128) (i j : Fin 5) (hne : i ≠ j) :
    destination region (block child.val i.val / 16) (child.val / 2^i.val)+16 ≤
      destination region (block child.val j.val / 16) (child.val / 2^j.val) ∨
    destination region (block child.val j.val / 16) (child.val / 2^j.val)+16 ≤
      destination region (block child.val i.val / 16) (child.val / 2^i.val) := by
  rw [path_slot, path_slot]
  have h:=(scatterSafe child).2 i j hne
  omega

theorem path_slot_bound (region : Nat) (child : Fin 128) (level : Fin 5) :
    region ≤ destination region (block child.val level.val / 16) (child.val / 2^level.val) ∧
    destination region (block child.val level.val / 16) (child.val / 2^level.val)+16 ≤ region+320 := by
  rw [path_slot]
  have h:=((scatterSafe child).1 level).2.2.1
  omega

end ClaudeWCT.W9.Machine.Expand.SharedScatter.Packing

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
def entryStart (k : Nat) : Nat := [45257, 45387, 45534, 45664, 45811, 45941, 46088, 46218, 46364].getD k 0
def valueStart (k : Nat) : Nat := [45266, 45400, 45543, 45677, 45820, 45954, 46097, 46231, 46376].getD k 0
def planStart (k : Nat) : Nat := [45300, 45434, 45577, 45711, 45854, 45988, 46131, 46265, 46410].getD k 0
def pathStart (k : Nat) : Nat := [45306, 45440, 45583, 45717, 45860, 45994, 46137, 46271, 46416].getD k 0
def topStart (k : Nat) : Nat := [45376, 45523, 45653, 45800, 45930, 46077, 46207, 46354, 46499].getD k 0
def sixthStart (k : Nat) : Nat := [45510, 45787, 46064, 46341, 46486].getD k 0
def entryWords (k : Nat) : List (BitVec 32) := [entry0Code, entry1Code, entry2Code, entry3Code, entry4Code, entry5Code, entry6Code, entry7Code, entry8Code].getD k []
def topWords (k : Nat) : List (BitVec 32) := [topCode0, topCode1, topCode2, topCode3, topCode4, topCode5, topCode6, topCode7, topCode8].getD k []
theorem valuesCode_of_driver {im : Image} (hc : CodeAt im (pcOf 45056) Images.expandSharedDriver) (k : Fin 9) : ValuesCode im (valueStart k.val) := by
  fin_cases k
  · constructor
    · exact SharedCounterHooks.code_slice (off:=210) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=214) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=220) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=226) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=232) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=238) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · exact SharedCounterHooks.code_slice (off:=344) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=348) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=354) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=360) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=366) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=372) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · exact SharedCounterHooks.code_slice (off:=487) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=491) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=497) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=503) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=509) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=515) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · exact SharedCounterHooks.code_slice (off:=621) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=625) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=631) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=637) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=643) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=649) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · exact SharedCounterHooks.code_slice (off:=764) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=768) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=774) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=780) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=786) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=792) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · exact SharedCounterHooks.code_slice (off:=898) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=902) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=908) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=914) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=920) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=926) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · exact SharedCounterHooks.code_slice (off:=1041) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1045) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1051) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1057) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1063) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1069) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · exact SharedCounterHooks.code_slice (off:=1175) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1179) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1185) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1191) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1197) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1203) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · exact SharedCounterHooks.code_slice (off:=1320) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1324) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1330) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1336) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1342) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1348) hc (by decide +kernel) (by decide +kernel)
theorem pathsCode_of_driver {im : Image} (hc : CodeAt im (pcOf 45056) Images.expandSharedDriver) (k : Fin 9) : PathsCode im (pathStart k.val) := by
  fin_cases k
  · constructor
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=250) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=264) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=278) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=292) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=306) hc (by decide +kernel) (by decide +kernel)
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=251) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=265) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=279) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=293) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=307) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=384) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=398) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=412) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=426) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=440) hc (by decide +kernel) (by decide +kernel)
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=385) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=399) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=413) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=427) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=441) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=527) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=541) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=555) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=569) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=583) hc (by decide +kernel) (by decide +kernel)
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=528) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=542) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=556) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=570) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=584) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=661) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=675) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=689) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=703) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=717) hc (by decide +kernel) (by decide +kernel)
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=662) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=676) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=690) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=704) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=718) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=804) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=818) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=832) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=846) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=860) hc (by decide +kernel) (by decide +kernel)
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=805) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=819) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=833) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=847) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=861) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=938) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=952) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=966) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=980) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=994) hc (by decide +kernel) (by decide +kernel)
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=939) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=953) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=967) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=981) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=995) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=1081) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1095) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1109) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1123) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1137) hc (by decide +kernel) (by decide +kernel)
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=1082) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1096) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1110) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1124) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1138) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=1215) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1229) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1243) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1257) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1271) hc (by decide +kernel) (by decide +kernel)
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=1216) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1230) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1244) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1258) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1272) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=1360) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1374) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1388) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1402) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1416) hc (by decide +kernel) (by decide +kernel)
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=1361) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1375) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1389) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1403) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1417) hc (by decide +kernel) (by decide +kernel)
theorem planCode_of_driver {im : Image} (hc : CodeAt im (pcOf 45056) Images.expandSharedDriver) (k : Fin 9) : CodeAt im (pcOf (planStart k.val)) planCode := by
  fin_cases k
  · exact SharedCounterHooks.code_slice (off:=244) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=378) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=521) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=655) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=798) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=932) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1075) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1209) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1354) hc (by decide +kernel) (by decide +kernel)
theorem entryCode_of_driver {im : Image} (hc : CodeAt im (pcOf 45056) Images.expandSharedDriver) (k : Fin 9) : CodeAt im (pcOf (entryStart k.val)) (entryWords k.val) := by
  fin_cases k
  · exact SharedCounterHooks.code_slice (off:=201) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=331) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=478) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=608) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=755) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=885) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1032) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1162) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1308) hc (by decide +kernel) (by decide +kernel)
theorem topCode_of_driver {im : Image} (hc : CodeAt im (pcOf 45056) Images.expandSharedDriver) (k : Fin 9) : CodeAt im (pcOf (topStart k.val)) (topWords k.val) := by
  fin_cases k
  · exact SharedCounterHooks.code_slice (off:=320) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=467) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=597) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=744) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=874) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1021) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1151) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1298) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1443) hc (by decide +kernel) (by decide +kernel)
theorem sixthCode_of_driver {im : Image} (hc : CodeAt im (pcOf 45056) Images.expandSharedDriver) (k : Fin 5) : CodeAt im (pcOf (sixthStart k.val)) sixthCode := by
  fin_cases k
  · exact SharedCounterHooks.code_slice (off:=454) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=731) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1008) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1285) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1430) hc (by decide +kernel) (by decide +kernel)
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter.Packing
open SigGolfCandidate.Research.SharedPathPacking
end ClaudeWCT.W9.Machine.Expand.SharedScatter.Packing

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
def coordRegion (k : Nat) : Nat := 9768-848*k
def coordSource (k : Nat) : Nat := 28688+208*k
def coordPhysical (k raw : Nat) : Nat := if k<8 ∧ k%2=0 then raw else raw/2+64*(raw%2)
def rawAddress (k : Nat) : Nat := [131424,131424,131432,131432,131440,131440,131448,131448,131448].getD k 0
def rawShift (k : Nat) : Nat := [0,6,0,6,0,6,0,6,37].getD k 0
def entryCycles (k : Nat) : Nat := [9,13,9,13,9,13,9,13,12].getD k 0
theorem coordPhysical_lt (k : Nat) (raw : Fin 128) : coordPhysical k raw.val<128 := by
  unfold coordPhysical
  split_ifs
  · exact raw.isLt
  · have:=Nat.mod_lt raw.val (by decide : 0<2);omega

theorem entry_setup {im : Image} (k : Fin 9)
    (hc : CodeAt im (pcOf (entryStart k.val)) (entryWords k.val))
    (s : MachineState) (hp : s.pc=pcOf (entryStart k.val)) (raw : Fin 128)
    (hraw : s.getMem (BitVec.ofNat 64 (rawAddress k.val)) >>> rawShift k.val &&& 127#64=BitVec.ofNat 64 raw.val)
    (h8in : k.val=8 → s.getReg .x8=BitVec.ofNat 64 3832) :
    ∃ t, Steps im s (entryCycles k.val) (entryCycles k.val) t ∧ t.pc=pcOf (valueStart k.val) ∧
      t.getReg .x16=BitVec.ofNat 64 (coordPhysical k.val raw.val) ∧
      t.getReg .x8=BitVec.ofNat 64 (coordRegion k.val) ∧
      t.getReg .x17=BitVec.ofNat 64 (coordSource k.val) ∧
      RegsExcept s t [.x6,.x8,.x16,.x17] ∧ Frame s t (fun _=>False) := by
  fin_cases k
  · simpa [entryCycles,valueStart,coordPhysical,coordRegion,coordSource] using entry0_steps (by simpa [entryStart,entryWords] using hc) s hp raw.val raw.isLt hraw
  · simpa [entryCycles,valueStart,coordPhysical,coordRegion,coordSource] using entry1_steps (by simpa [entryStart,entryWords] using hc) s hp raw.val raw.isLt hraw
  · simpa [entryCycles,valueStart,coordPhysical,coordRegion,coordSource] using entry2_steps (by simpa [entryStart,entryWords] using hc) s hp raw.val raw.isLt hraw
  · simpa [entryCycles,valueStart,coordPhysical,coordRegion,coordSource] using entry3_steps (by simpa [entryStart,entryWords] using hc) s hp raw.val raw.isLt hraw
  · simpa [entryCycles,valueStart,coordPhysical,coordRegion,coordSource] using entry4_steps (by simpa [entryStart,entryWords] using hc) s hp raw.val raw.isLt hraw
  · simpa [entryCycles,valueStart,coordPhysical,coordRegion,coordSource] using entry5_steps (by simpa [entryStart,entryWords] using hc) s hp raw.val raw.isLt hraw
  · simpa [entryCycles,valueStart,coordPhysical,coordRegion,coordSource] using entry6_steps (by simpa [entryStart,entryWords] using hc) s hp raw.val raw.isLt hraw
  · simpa [entryCycles,valueStart,coordPhysical,coordRegion,coordSource] using entry7_steps (by simpa [entryStart,entryWords] using hc) s hp raw.val raw.isLt hraw
  · simpa [entryCycles,valueStart,coordPhysical,coordRegion,coordSource] using entry8_steps (by simpa [entryStart,entryWords] using hc) s hp raw.val raw.isLt hraw (h8in rfl)
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
def topDest (k child : Nat) : Nat := [topDest0 child,topDest1 child,topDest2 child,topDest3 child,topDest4 child,topDest5 child,topDest6 child,topDest7 child,topDest8 child].getD k 0
def topInput (k : Nat) : Nat := if k<8 ∧ k%2=0 then 176 else 192
def nextEntry (k : Nat) : Nat := [45387,45534,45664,45811,45941,46088,46218,46364,46509].getD k 0
def topSteps (k : Nat) : Nat := if k<7 then 11 else 10
theorem top_copy {im : Image} (k : Fin 9)
    (hc : CodeAt im (pcOf (topStart k.val)) (topWords k.val))
    (s : MachineState) (hp : s.pc=pcOf (topStart k.val)) (source : Nat) (child : Fin 128)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (h16 : s.getReg .x16=BitVec.ofNat 64 child.val) (h17 : s.getReg .x17=BitVec.ofNat 64 source)
    (h8 : s.getReg .x8=BitVec.ofNat 64 (coordRegion k.val)) :
    ∃ t,Steps im s (topSteps k.val) (topSteps k.val+3) t ∧ t.pc=pcOf (nextEntry k.val) ∧
      (∀half<2,t.getMem (BitVec.ofNat 64 (topDest k.val child.val+8*half))=
        s.getMem (BitVec.ofNat 64 (source+topInput k.val+8*half))) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧ Frame s t (fun A=>A=topDest k.val child.val ∨ A=topDest k.val child.val+8) := by
  fin_cases k
  · obtain ⟨t,st,tp,lo,hi,tr,tf⟩:=top0_steps (by simpa [topStart,topWords] using hc) s hp source child.val hs0 hs1 hsa child.isLt h16 h17
    refine ⟨t,st,tp,?_,tr,tf⟩
    intro half hh
    interval_cases half
    · simpa [topDest,topInput] using lo
    · simpa [topDest,topInput] using hi
  · obtain ⟨t,st,tp,lo,hi,tr,tf⟩:=top1_steps (by simpa [topStart,topWords] using hc) s hp source child.val hs0 hs1 hsa child.isLt h16 h17
    refine ⟨t,st,tp,?_,tr,tf⟩
    intro half hh
    interval_cases half
    · simpa [topDest,topInput] using lo
    · simpa [topDest,topInput] using hi
  · obtain ⟨t,st,tp,lo,hi,tr,tf⟩:=top2_steps (by simpa [topStart,topWords] using hc) s hp source child.val hs0 hs1 hsa child.isLt h16 h17
    refine ⟨t,st,tp,?_,tr,tf⟩
    intro half hh
    interval_cases half
    · simpa [topDest,topInput] using lo
    · simpa [topDest,topInput] using hi
  · obtain ⟨t,st,tp,lo,hi,tr,tf⟩:=top3_steps (by simpa [topStart,topWords] using hc) s hp source child.val hs0 hs1 hsa child.isLt h16 h17
    refine ⟨t,st,tp,?_,tr,tf⟩
    intro half hh
    interval_cases half
    · simpa [topDest,topInput] using lo
    · simpa [topDest,topInput] using hi
  · obtain ⟨t,st,tp,lo,hi,tr,tf⟩:=top4_steps (by simpa [topStart,topWords] using hc) s hp source child.val hs0 hs1 hsa child.isLt h16 h17
    refine ⟨t,st,tp,?_,tr,tf⟩
    intro half hh
    interval_cases half
    · simpa [topDest,topInput] using lo
    · simpa [topDest,topInput] using hi
  · obtain ⟨t,st,tp,lo,hi,tr,tf⟩:=top5_steps (by simpa [topStart,topWords] using hc) s hp source child.val hs0 hs1 hsa child.isLt h16 h17
    refine ⟨t,st,tp,?_,tr,tf⟩
    intro half hh
    interval_cases half
    · simpa [topDest,topInput] using lo
    · simpa [topDest,topInput] using hi
  · obtain ⟨t,st,tp,lo,hi,tr,tf⟩:=top6_steps (by simpa [topStart,topWords] using hc) s hp source child.val hs0 hs1 hsa child.isLt h16 h17
    refine ⟨t,st,tp,?_,tr,tf⟩
    intro half hh
    interval_cases half
    · simpa [topDest,topInput] using lo
    · simpa [topDest,topInput] using hi
  · obtain ⟨t,st,tp,lo,hi,tr,tf⟩:=top7_steps (by simpa [topStart,topWords] using hc) s hp source child.val hs0 hs1 hsa child.isLt h16 h17 (by simpa [coordRegion] using h8)
    refine ⟨t,st,tp,?_,tr,tf⟩
    intro half hh
    interval_cases half
    · simpa [topDest,topInput] using lo
    · simpa [topDest,topInput] using hi
  · obtain ⟨t,st,tp,lo,hi,tr,tf⟩:=top8_steps (by simpa [topStart,topWords] using hc) s hp source child.val hs0 hs1 hsa child.isLt h16 h17 (by simpa [coordRegion] using h8)
    refine ⟨t,st,tp,?_,tr,tf⟩
    intro half hh
    interval_cases half
    · simpa [topDest,topInput] using lo
    · simpa [topDest,topInput] using hi
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
def PayloadW (region child : Nat) (slots : Nat → Nat) (A : Nat) : Prop :=
  ValuesW region A ∨ PathsW (pathDestination region child slots) 5 A
structure PayloadPost (s : MachineState) (b region source child : Nat) (slots : Nat → Nat)
    (t : MachineState) : Prop where
  pc : t.pc=pcOf (b+110)
  values : ∀ i<6,∀ half<2,t.getMem (BitVec.ofNat 64 (region+(640+40*(i-(i-1))+72*(i/5)-52*i-124*(i%2))+8*half))=
    s.getMem (BitVec.ofNat 64 (source+16*i+8*half))
  ends : ∀ i<6,0 < i → ∀ half<2,t.getMem (BitVec.ofNat 64 (region+672+16*i+8*half))=
    s.getMem (BitVec.ofNat 64 (source+16*i+8*half))
  paths : ∀ i<5,∀ half<2,t.getMem (BitVec.ofNat 64 (pathDestination region child slots i+8*half))=
    s.getMem (BitVec.ofNat 64 (source+96+16*i+8*half))
  regs : RegsExcept s t [.x6,.x7,.x18,.x28]
  frame : Frame s t (PayloadW region child slots)
theorem payload_steps {im : Image} {b : Nat}
    (hb : b=45266 ∨ b=45400 ∨ b=45543 ∨ b=45677 ∨ b=45820 ∨ b=45954 ∨ b=46097 ∨ b=46231 ∨ b=46376)
    (hv : ValuesCode im b) (hp : CodeAt im (pcOf (b+34)) planCode) (hd : PathsCode im (b+40))
    (s : MachineState) (hpc : s.pc=pcOf b) (region source child : Nat) (slots : Nat → Nat)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (hchild : child<128) (hslots : ∀j<5,slots j<53)
    (hdst : ∀j<5,pathDestination region child slots j+16 ≤ region+320)
    (hdis : ∀i<5,∀j<5,i ≠ j → pathDestination region child slots i+16 ≤ pathDestination region child slots j ∨
      pathDestination region child slots j+16 ≤ pathDestination region child slots i)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h16 : s.getReg .x16=BitVec.ofNat 64 child)
    (h17 : s.getReg .x17=BitVec.ofNat 64 source)
    (hbytes : ∀j<5,s.getByte (BitVec.ofNat 64 (16748432+5*(child%32)+j))=BitVec.ofNat 8 (slots j)) :
    ∃ t,Steps im s 110 125 t ∧ PayloadPost s b region source child slots t := by
  obtain ⟨u,su,up,uv,ue,ur,uf⟩:=values_steps hb hv s hpc region source hr0 hr1 hra hs0 hs1 hsa h8 h17
  obtain ⟨v,uvs,vp,vt,vr,vf⟩:=plan_steps (b:=b+34) (by omega) hp u up child hchild
    (by rw [ur.get (by decide),h16])
  have sf : Frame s v (ValuesW region) := (uf.trans vf).mono (by intro A hA h;exact h.elim id False.elim)
  have sr : RegsExcept s v [.x6,.x7,.x18] := (ur.trans vr).mono (by simp)
  have vb : ∀j<5,v.getByte (BitVec.ofNat 64 (16748432+5*(child%32)+j))=BitVec.ofNat 8 (slots j) := by
    intro j hj
    rw [sf.getByte (by have:=Nat.mod_lt child (by decide : 0<32);omega) (by
      rintro ⟨i,hi,h⟩;omega)]
    exact hbytes j hj
  obtain ⟨t,st,ht⟩:=five_paths (b:=b+40) (by omega) hd v (by simpa [Nat.add_assoc] using vp)
    region source child (16748432+5*(child%32)) slots hr0 hr1 hra hs0 hs1 hsa hchild
    (by omega) (by have:=Nat.mod_lt child (by decide : 0<32);omega) hslots hdis
    (by rw [sr.get (by decide),h8]) (by rw [sr.get (by decide),h16])
    (by rw [sr.get (by decide),h17]) vt vb
  refine ⟨t,((su.trans uvs).trans st).of_eq (by omega) (by omega),?_,?_,?_,?_,?_,?_⟩
  · simpa [Nat.add_assoc] using ht.pc
  · intro i hi half hh
    have key := uv i hi half hh
    obtain ⟨ilow, ihigh⟩ : 368 ≤ (640+40*(i-(i-1))+72*(i/5)-52*i-124*(i%2)) ∧
        (640+40*(i-(i-1))+72*(i/5)-52*i-124*(i%2)) ≤ 680 := by
      rcases (show i=0∨i=1∨i=2∨i=3∨i=4∨i=5 by omega) with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    generalize (640+40*(i-(i-1))+72*(i/5)-52*i-124*(i%2)) = ve at key ilow ihigh ⊢
    rw [ht.frame.get (by omega) (by rintro ⟨j,hj,h⟩;have:=hdst j hj;omega)]
    rw [vf.get (by omega) (by simp)]
    exact key
  · intro i hi hip half hh
    rw [ht.frame.get (by omega) (by rintro ⟨j,hj,h⟩;have:=hdst j hj;omega)]
    rw [vf.get (by omega) (by simp)]
    exact ue i hi hip half hh
  · intro i hi half hh
    rw [ht.reads i hi half hh]
    exact sf.get (by omega) (by rintro ⟨j,hj,h⟩;omega)
  · exact (sr.trans ht.regs).mono (by simp)
  · exact (sf.trans ht.frame).mono (by intro A hA h;exact h)
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open SigGolfCandidate.Rv SigGolfCandidate.T3M
theorem installed_values (k : Fin 9) : ValuesCode Images.expandImage (valueStart k.val) :=
  valuesCode_of_driver codeAt_expand_shared_driver k
theorem installed_paths (k : Fin 9) : PathsCode Images.expandImage (pathStart k.val) :=
  pathsCode_of_driver codeAt_expand_shared_driver k
theorem installed_plan (k : Fin 9) : CodeAt Images.expandImage (pcOf (planStart k.val)) planCode :=
  planCode_of_driver codeAt_expand_shared_driver k
theorem installed_entry (k : Fin 9) : CodeAt Images.expandImage (pcOf (entryStart k.val)) (entryWords k.val) :=
  entryCode_of_driver codeAt_expand_shared_driver k
theorem installed_top (k : Fin 9) : CodeAt Images.expandImage (pcOf (topStart k.val)) (topWords k.val) :=
  topCode_of_driver codeAt_expand_shared_driver k
theorem installed_sixth (k : Fin 5) : CodeAt Images.expandImage (pcOf (sixthStart k.val)) sixthCode :=
  sixthCode_of_driver codeAt_expand_shared_driver k
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
def SixthW (region child A : Nat) : Prop := A=destination region 49 (child/32) ∨ A=destination region 49 (child/32)+8
structure ExtendedPost (s : MachineState) (region source child : Nat) (slots : Nat → Nat) (t : MachineState) : Prop where
  values : ∀i<6,∀half<2,t.getMem (BitVec.ofNat 64 (region+(640+40*(i-(i-1))+72*(i/5)-52*i-124*(i%2))+8*half))=s.getMem (BitVec.ofNat 64 (source+16*i+8*half))
  ends : ∀ i < 6, 0 < i → ∀half<2,t.getMem (BitVec.ofNat 64 (region+672+16*i+8*half))=s.getMem (BitVec.ofNat 64 (source+16*i+8*half))
  paths : ∀i<5,∀half<2,t.getMem (BitVec.ofNat 64 (pathDestination region child slots i+8*half))=s.getMem (BitVec.ofNat 64 (source+96+16*i+8*half))
  sixth : ∀half<2,t.getMem (BitVec.ofNat 64 (destination region 49 (child/32)+8*half))=s.getMem (BitVec.ofNat 64 (source+176+8*half))
  regs : RegsExcept s t [.x6,.x7,.x18,.x28]
  frame : Frame s t (fun A=>PayloadW region child slots A ∨ SixthW region child A)
theorem payload_sixth {im : Image} {b : Nat}
    (hb : b+110=45510 ∨ b+110=45787 ∨ b+110=46064 ∨ b+110=46341 ∨ b+110=46486)
    (hc : CodeAt im (pcOf (b+110)) sixthCode) {s u : MachineState}
    (region source child : Nat) (slots : Nat → Nat)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0) (hchild : child<128)
    (hdst : ∀j<5,pathDestination region child slots j+16 ≤ region+320)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h16 : s.getReg .x16=BitVec.ofNat 64 child)
    (h17 : s.getReg .x17=BitVec.ofNat 64 source)
    (hu : PayloadPost s b region source child slots u) :
    ∃t,Steps im u 13 16 t ∧ t.pc=pcOf (b+123) ∧ ExtendedPost s region source child slots t := by
  obtain ⟨t,st,tp,lo,hi,tr,tf⟩:=sixth_steps_rebased hb hc u hu.pc region source child
    hr0 hr1 hra hs0 hs1 hsa hchild
    (by rw [hu.regs.get (by decide),h8]) (by rw [hu.regs.get (by decide),h16])
    (by rw [hu.regs.get (by decide),h17])
  have hd : region+784 ≤ destination region 49 (child/32) ∧ destination region 49 (child/32)+16 ≤ region+848 := by
    unfold destination
    have:=Nat.mod_lt (child/32) (by decide : 0<2)
    omega
  refine ⟨t,st,by simpa [Nat.add_assoc] using tp,?_,?_,?_,?_,?_,?_⟩
  · intro i hi half hh
    rw [tf.get (by omega) (by omega)]
    exact hu.values i hi half hh
  · intro i hi hip half hh
    rw [tf.get (by omega) (by omega)]
    exact hu.ends i hi hip half hh
  · intro i hi half hh
    have hdi:=hdst i hi
    rw [tf.get (by omega) (by omega)]
    exact hu.paths i hi half hh
  · intro half hh
    have hsfr : ∀off,176 ≤ off → off ≤184 → u.getMem (BitVec.ofNat 64 (source+off))=s.getMem (BitVec.ofNat 64 (source+off)) := by
      intro off hlo hhi
      apply hu.frame.get (by omega)
      rintro (h|h)
      · obtain ⟨j,hj,h⟩:=h;omega
      · obtain ⟨j,hj,h⟩:=h;have:=hdst j hj;omega
    interval_cases half
    · simpa only [Nat.mul_zero,Nat.add_zero,hsfr 176 (by omega) (by omega)] using lo
    · simpa only [Nat.mul_one,show source+176+8=source+184 by omega,hsfr 184 (by omega) (by omega)] using hi
  · exact (hu.regs.trans tr).mono (by simp)
  · exact (hu.frame.trans tf).mono (by intro A hA h;exact h)
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.Research.SharedPathPacking
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
def packedSlots (child j : Nat) : Nat := block child j / 16

theorem payload_packed {im : Image} {b : Nat}
    (hb : b=45266 ∨ b=45400 ∨ b=45543 ∨ b=45677 ∨ b=45820 ∨ b=45954 ∨ b=46097 ∨ b=46231 ∨ b=46376)
    (hv : ValuesCode im b) (hp : CodeAt im (pcOf (b+34)) planCode) (hd : PathsCode im (b+40))
    (s : MachineState) (hpc : s.pc=pcOf b) (region source : Nat) (child : Fin 128)
    (hr0 : 2968 ≤ region) (hr1 : region ≤ 10152) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h16 : s.getReg .x16=BitVec.ofNat 64 child.val)
    (h17 : s.getReg .x17=BitVec.ofNat 64 source)
    (hbytes : ∀j<5,s.getByte (BitVec.ofNat 64 (16748432+5*(child.val%32)+j))=
      BitVec.ofNat 8 (packedSlots child.val j)) :
    ∃t,Steps im s 110 125 t ∧ PayloadPost s b region source child.val (packedSlots child.val) t := by
  apply payload_steps hb hv hp hd s hpc region source child.val (packedSlots child.val)
    hr0 hr1 hra hs0 hs1 hsa child.isLt
    (fun j hj=>Packing.slots_bound child ⟨j,hj⟩) ?_ ?_ h8 h16 h17 hbytes
  · intro j hj
    exact (Packing.path_slot_bound region child ⟨j,hj⟩).2
  · intro i hi j hj hne
    exact Packing.path_slots_disjoint region child ⟨i,hi⟩ ⟨j,hj⟩ (by intro h;exact hne (congrArg Fin.val h))

end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.Research.SharedPathPacking
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
def firstCoord (k : Nat) : Prop := k<8 ∧ k%2=0
instance (k : Nat) : Decidable (firstCoord k) := inferInstanceAs (Decidable (k<8 ∧ k%2=0))
def bodyInstructions (k : Nat) : Nat := if firstCoord k then 110 else 123
def bodyCycles (k : Nat) : Nat := if firstCoord k then 125 else 141
def LocalW (region child A : Nat) : Prop := PayloadW region child (packedSlots child) A ∨ SixthW region child A
structure BodyPost (s : MachineState) (k child : Nat) (t : MachineState) : Prop where
  pc : t.pc=pcOf (topStart k)
  values : ∀i<6,∀half<2,t.getMem (BitVec.ofNat 64 (coordRegion k+(640+40*(i-(i-1))+72*(i/5)-52*i-124*(i%2))+8*half))=s.getMem (BitVec.ofNat 64 (coordSource k+16*i+8*half))
  ends : ∀ i<6,0 < i → ∀half<2,t.getMem (BitVec.ofNat 64 (coordRegion k+672+16*i+8*half))=s.getMem (BitVec.ofNat 64 (coordSource k+16*i+8*half))
  paths : ∀i<5,∀half<2,t.getMem (BitVec.ofNat 64 (pathDestination (coordRegion k) child (packedSlots child) i+8*half))=s.getMem (BitVec.ofNat 64 (coordSource k+96+16*i+8*half))
  sixth : ¬firstCoord k → ∀half<2,t.getMem (BitVec.ofNat 64 (destination (coordRegion k) 49 (child/32)+8*half))=s.getMem (BitVec.ofNat 64 (coordSource k+176+8*half))
  regs : RegsExcept s t [.x6,.x7,.x18,.x28]
  frame : Frame s t (LocalW (coordRegion k) child)
theorem body_steps {im : Image} (k : Fin 9)
    (hv : ValuesCode im (valueStart k.val))
    (hp : CodeAt im (pcOf (planStart k.val)) planCode)
    (hd : PathsCode im (pathStart k.val))
    (hx : ¬firstCoord k.val → CodeAt im (pcOf (valueStart k.val+110)) sixthCode)
    (s : MachineState) (hpc : s.pc=pcOf (valueStart k.val)) (child : Fin 128)
    (h8 : s.getReg .x8=BitVec.ofNat 64 (coordRegion k.val)) (h16 : s.getReg .x16=BitVec.ofNat 64 child.val)
    (h17 : s.getReg .x17=BitVec.ofNat 64 (coordSource k.val))
    (hbytes : ∀j<5,s.getByte (BitVec.ofNat 64 (16748432+5*(child.val%32)+j))=
      BitVec.ofNat 8 (packedSlots child.val j)) :
    ∃t,Steps im s (bodyInstructions k.val) (bodyCycles k.val) t ∧ BodyPost s k.val child.val t := by
  have hb : valueStart k.val=45266 ∨ valueStart k.val=45400 ∨ valueStart k.val=45543 ∨ valueStart k.val=45677 ∨ valueStart k.val=45820 ∨ valueStart k.val=45954 ∨ valueStart k.val=46097 ∨ valueStart k.val=46231 ∨ valueStart k.val=46376 := by fin_cases k <;> decide
  have hpl : valueStart k.val+34=planStart k.val := by fin_cases k <;> decide
  have hpa : valueStart k.val+40=pathStart k.val := by fin_cases k <;> decide
  have r0 : 2968 ≤ coordRegion k.val := by fin_cases k <;> decide
  have r1 : coordRegion k.val ≤ 10152 := by fin_cases k <;> decide
  have ra : coordRegion k.val%8=0 := by fin_cases k <;> decide
  have s0 : 28672 ≤ coordSource k.val := by fin_cases k <;> decide
  have s1 : coordSource k.val ≤ 31000 := by fin_cases k <;> decide
  have sa : coordSource k.val%8=0 := by fin_cases k <;> decide
  obtain ⟨u,su,hu⟩:=payload_packed hb hv (by rw [hpl];exact hp) (by rw [hpa];exact hd)
    s hpc (coordRegion k.val) (coordSource k.val) child r0 r1 ra s0 s1 sa h8 h16 h17 hbytes
  by_cases hf:firstCoord k.val
  · have pc : valueStart k.val+110=topStart k.val := by fin_cases k <;> simp_all [firstCoord,valueStart,topStart]
    refine ⟨u,by simpa [bodyInstructions,bodyCycles,hf] using su,?_,hu.values,hu.ends,hu.paths,?_,hu.regs,?_⟩
    · simpa [pc] using hu.pc
    · intro hn;exact (hn hf).elim
    · exact hu.frame.mono (by intro A hA h;exact Or.inl h)
  · have h6 : valueStart k.val+110=45510 ∨ valueStart k.val+110=45787 ∨ valueStart k.val+110=46064 ∨ valueStart k.val+110=46341 ∨ valueStart k.val+110=46486 := by
      fin_cases k <;> simp_all [firstCoord,valueStart]
    have pc : valueStart k.val+123=topStart k.val := by fin_cases k <;> simp_all [firstCoord,valueStart,topStart]
    obtain ⟨t,ut,tp,ht⟩:=payload_sixth h6 (hx hf) (coordRegion k.val) (coordSource k.val) child.val (packedSlots child.val)
      r0 r1 ra s0 s1 sa child.isLt (fun j hj=>(Packing.path_slot_bound (coordRegion k.val) child ⟨j,hj⟩).2) h8 h16 h17 hu
    refine ⟨t,?_,?_,ht.values,ht.ends,ht.paths,fun _=>ht.sixth,ht.regs,ht.frame⟩
    · simpa [bodyInstructions,bodyCycles,hf] using su.trans ut
    · simpa [pc] using tp
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.Research.SharedPathPacking
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
theorem localW_bounds (region : Nat) (child : Fin 128) (A : Nat)
    (h : LocalW region child.val A) : region ≤ A ∧ A+8 ≤ region+848 := by
  rcases h with (h|h)|h
  · obtain ⟨i,hi,h⟩:=h
    omega
  · obtain ⟨i,hi,h⟩:=h
    have hb:=Packing.path_slot_bound region child ⟨i,hi⟩
    change region ≤ pathDestination region child.val (packedSlots child.val) i ∧
      pathDestination region child.val (packedSlots child.val) i+16 ≤ region+320 at hb
    omega
  · unfold SixthW destination at h
    have:=Nat.mod_lt (child.val/32) (by decide : 0<2)
    omega

theorem topDest_bound (k : Fin 9) (child : Fin 128) : topDest k.val child.val+16 ≤ coordRegion k.val := by
  have h32:=Nat.mod_lt (child.val/32) (by decide : 0<2)
  have h64:=Nat.mod_lt (child.val/64) (by decide : 0<2)
  fin_cases k <;> norm_num [topDest,topDest0,topDest1,topDest2,topDest3,topDest4,topDest5,topDest6,topDest7,topDest8,coordRegion] <;> omega

theorem coordRegion_bounds (k : Fin 9) : 2968 ≤ coordRegion k.val ∧ coordRegion k.val ≤ 10152 ∧ coordRegion k.val%8=0 := by
  fin_cases k <;> decide

theorem coordSource_bounds (k : Fin 9) : 28672 ≤ coordSource k.val ∧ coordSource k.val ≤ 31000 ∧ coordSource k.val%8=0 := by
  fin_cases k <;> decide

def coordinateInstructions (k : Nat) : Nat := entryCycles k+bodyInstructions k+topSteps k
def coordinateCycles (k : Nat) : Nat := entryCycles k+bodyCycles k+topSteps k+3

theorem coordinateTotals : ((List.range 9).map coordinateInstructions).sum=1252 ∧
    ((List.range 9).map coordinateCycles).sum=1429 := by decide
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.Research.SharedPathPacking
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
structure CoordinateCode (im : Image) (k : Nat) : Prop where
  entry : CodeAt im (pcOf (entryStart k)) (entryWords k)
  values : ValuesCode im (valueStart k)
  plan : CodeAt im (pcOf (planStart k)) planCode
  paths : PathsCode im (pathStart k)
  sixth : ¬firstCoord k → CodeAt im (pcOf (valueStart k+110)) sixthCode
  top : CodeAt im (pcOf (topStart k)) (topWords k)
def CoordinateW (k child A : Nat) : Prop := LocalW (coordRegion k) child A ∨ A=topDest k child ∨ A=topDest k child+8
structure CoordinatePost (s : MachineState) (k child : Nat) (t : MachineState) : Prop where
  pc : t.pc=pcOf (nextEntry k)
  values : ∀i<6,∀half<2,t.getMem (BitVec.ofNat 64 (coordRegion k+(640+40*(i-(i-1))+72*(i/5)-52*i-124*(i%2))+8*half))=s.getMem (BitVec.ofNat 64 (coordSource k+16*i+8*half))
  ends : ∀i<6,0 < i → ∀half<2,t.getMem (BitVec.ofNat 64 (coordRegion k+672+16*i+8*half))=s.getMem (BitVec.ofNat 64 (coordSource k+16*i+8*half))
  paths : ∀i<5,∀half<2,t.getMem (BitVec.ofNat 64 (pathDestination (coordRegion k) child (packedSlots child) i+8*half))=s.getMem (BitVec.ofNat 64 (coordSource k+96+16*i+8*half))
  sixth : ¬firstCoord k → ∀half<2,t.getMem (BitVec.ofNat 64 (destination (coordRegion k) 49 (child/32)+8*half))=s.getMem (BitVec.ofNat 64 (coordSource k+176+8*half))
  top : ∀half<2,t.getMem (BitVec.ofNat 64 (topDest k child+8*half))=s.getMem (BitVec.ofNat 64 (coordSource k+topInput k+8*half))
  regs : RegsExcept s t [.x6,.x7,.x8,.x16,.x17,.x18,.x28]
  frame : Frame s t (CoordinateW k child)
  x8 : t.getReg .x8=BitVec.ofNat 64 (coordRegion k)
theorem coordinate_steps {im : Image} (k : Fin 9) (hc : CoordinateCode im k.val)
    (s : MachineState) (hp : s.pc=pcOf (entryStart k.val)) (raw : Fin 128)
    (hraw : s.getMem (BitVec.ofNat 64 (rawAddress k.val)) >>> rawShift k.val &&& 127#64=BitVec.ofNat 64 raw.val)
    (hbytes : ∀j<5,s.getByte (BitVec.ofNat 64 (16748432+5*(coordPhysical k.val raw.val%32)+j))=
      BitVec.ofNat 8 (packedSlots (coordPhysical k.val raw.val) j))
    (h8in : k.val=8 → s.getReg .x8=BitVec.ofNat 64 3832) :
    ∃t,Steps im s (coordinateInstructions k.val) (coordinateCycles k.val) t ∧
      CoordinatePost s k.val (coordPhysical k.val raw.val) t := by
  let child : Fin 128 := ⟨coordPhysical k.val raw.val,coordPhysical_lt k.val raw⟩
  change ∃t,Steps im s (coordinateInstructions k.val) (coordinateCycles k.val) t ∧ CoordinatePost s k.val child.val t
  have rb:=coordRegion_bounds k
  have sb:=coordSource_bounds k
  obtain ⟨u,su,up,u16,u8,u17,ur,uf⟩:=entry_setup k hc.entry s hp raw hraw h8in
  obtain ⟨v,uv,hv⟩:=body_steps k hc.values hc.plan hc.paths hc.sixth u up child u8 u16 u17 (by
    intro j hj
    rw [uf.getByte (by have:=Nat.mod_lt child.val (by decide : 0<32);omega) (by simp)]
    exact hbytes j hj)
  obtain ⟨t,vt,tp,tt,tr,tf⟩:=top_copy k hc.top v hv.pc (coordSource k.val) child sb.1 sb.2.1 sb.2.2
    (by rw [hv.regs.get (by decide),u16]) (by rw [hv.regs.get (by decide),u17]) (by rw [hv.regs.get (by decide),u8])
  have td:=topDest_bound k child
  have local_eq : ∀A,coordRegion k.val ≤ A → A<2^64 → t.getMem (BitVec.ofNat 64 A)=v.getMem (BitVec.ofNat 64 A) := by
    intro A hA hi
    exact tf.get hi (by omega)
  have bf : Frame s v (LocalW (coordRegion k.val) child.val) :=
    (uf.trans hv.frame).mono (by intro A hA h;exact h.elim False.elim id)
  refine ⟨t,((su.trans uv).trans vt).of_eq (by rfl) (by unfold coordinateCycles;omega),tp,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i hi half hh
    rw [local_eq _ (by omega) (by omega),hv.values i hi half hh]
    exact uf.get (by omega) (by simp)
  · intro i hi hip half hh
    rw [local_eq _ (by omega) (by omega),hv.ends i hi hip half hh]
    exact uf.get (by omega) (by simp)
  · intro i hi half hh
    have pd:=Packing.path_slot_bound (coordRegion k.val) child ⟨i,hi⟩
    change coordRegion k.val ≤ pathDestination (coordRegion k.val) child.val (packedSlots child.val) i ∧
      pathDestination (coordRegion k.val) child.val (packedSlots child.val) i+16 ≤ coordRegion k.val+320 at pd
    rw [local_eq _ (by omega) (by omega),hv.paths i hi half hh]
    exact uf.get (by omega) (by simp)
  · intro hn half hh
    have ph:=Nat.mod_lt (child.val/32) (by decide : 0<2)
    rw [local_eq _ (by unfold destination;omega) (by unfold destination;omega),hv.sixth hn half hh]
    exact uf.get (by omega) (by simp)
  · intro half hh
    rw [tt half hh]
    have hb : topInput k.val ≤192 := by unfold topInput;split_ifs <;> omega
    apply bf.get (by omega)
    intro hw
    have h:=localW_bounds (coordRegion k.val) child _ hw
    omega
  · exact ((ur.trans hv.regs).trans tr).mono (by simp)
  · exact (bf.trans tf).mono (by intro A hA h;exact h)
  · rw [tr.get (by decide),hv.regs.get (by decide),u8]
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.Research.SharedPathPacking
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem localW_pad (region : Nat) (child : Fin 128) (half : Fin 2) (right : Bool) :
    ¬LocalW region child.val (region+(if right then 160 else 672)+8*half.val) := by
  intro h
  rcases h with (h|h)|h
  · obtain ⟨i,hi,h⟩:=h
    cases right <;> simp only [Bool.false_eq_true,ite_false,ite_true] at h <;> omega
  · obtain ⟨i,hi,h⟩:=h
    have hs:=((Packing.scatterSafe child).1 ⟨i,hi⟩)
    dsimp only at hs
    have hmod : sibling child.val i %16=0 := by
      simp only [sibling,Nat.add_mod,Nat.mul_mod,show 48%16=0 from rfl,zero_mul,Nat.zero_mod,Nat.add_zero,hs.1]
    change (region+(if right then 160 else 672)+8*half.val=destination region (block child.val i/16) (child.val/2^i) ∨ region+(if right then 160 else 672)+8*half.val=destination region (block child.val i/16) (child.val/2^i)+8) at h
    rw [Packing.path_slot region child ⟨i,hi⟩] at h
    cases right <;> simp only [Bool.false_eq_true,ite_false,ite_true] at h <;> omega
  · unfold SixthW destination at h
    have:=Nat.mod_lt (child.val/32) (by decide : 0<2)
    cases right <;> simp only [Bool.false_eq_true,ite_false,ite_true] at h <;> omega

theorem localW_pads (region : Nat) (child : Fin 128) (A : Nat)
    (ha:A=region+160 ∨ A=region+168 ∨ A=region+672 ∨ A=region+680) : ¬LocalW region child.val A := by
  rcases ha with rfl|rfl|rfl|rfl
  · exact localW_pad region child 0 true
  · simpa [Nat.add_assoc] using localW_pad region child 1 true
  · exact localW_pad region child 0 false
  · simpa [Nat.add_assoc] using localW_pad region child 1 false

theorem topDest_prev (k : Fin 8) (child : Fin 128) :
    topDest k.val child.val=coordRegion (k.val+1)+160 ∨
    topDest k.val child.val=coordRegion (k.val+1)+672 := by
  have h32:=Nat.mod_lt (child.val/32) (by decide : 0<2)
  have h64:=Nat.mod_lt (child.val/64) (by decide : 0<2)
  fin_cases k <;> norm_num [topDest,topDest0,topDest1,topDest2,topDest3,topDest4,topDest5,topDest6,topDest7,topDest8,coordRegion] <;> omega

theorem coordRegion_gap (j k : Fin 9) (hjk:j.val<k.val) :
    coordRegion k.val+848 ≤ coordRegion j.val := by
  unfold coordRegion
  omega

theorem coordinateW_bounds (k : Fin 9) (child : Fin 128) (A : Nat) (h:CoordinateW k.val child.val A) :
    1200 ≤ A ∧ A+8 ≤ coordRegion k.val+848 := by
  rcases h with h|h|h
  · have hb:=localW_bounds (coordRegion k.val) child A h
    have hr:=coordRegion_bounds k
    omega
  · have hb:=topDest_bound k child
    have hlo : 1216 ≤ topDest k.val child.val := by
      have h32:=Nat.mod_lt (child.val/32) (by decide : 0<2)
      have h64:=Nat.mod_lt (child.val/64) (by decide : 0<2)
      fin_cases k <;> norm_num [topDest,topDest0,topDest1,topDest2,topDest3,topDest4,topDest5,topDest6,topDest7,topDest8] <;> omega
    omega
  · have hb:=topDest_bound k child
    have hlo : 1216 ≤ topDest k.val child.val := by
      have h32:=Nat.mod_lt (child.val/32) (by decide : 0<2)
      have h64:=Nat.mod_lt (child.val/64) (by decide : 0<2)
      fin_cases k <;> norm_num [topDest,topDest0,topDest1,topDest2,topDest3,topDest4,topDest5,topDest6,topDest7,topDest8] <;> omega
    omega

def ReadArea (k child A : Nat) : Prop :=
  (coordRegion k≤A ∧ A+8≤coordRegion k+848) ∨ A=topDest k child ∨ A=topDest k child+8

theorem readArea_disjoint (j k : Fin 9) (hj:j.val<k.val) (cj ck : Fin 128) (A : Nat)
    (ha:ReadArea j.val cj.val A) : ¬CoordinateW k.val ck.val A := by
  intro hw
  have wb:=coordinateW_bounds k ck A hw
  have gap:=coordRegion_gap j k hj
  rcases ha with ha|ha|ha
  · omega
  all_goals
    have j8:j.val<8 := by omega
    have jp : topDest j.val cj.val=coordRegion (j.val+1)+160 ∨ topDest j.val cj.val=coordRegion (j.val+1)+672 := topDest_prev ⟨j.val,j8⟩ cj
    have kd:=topDest_bound k ck
    by_cases hk:k.val=j.val+1
    · have rg : coordRegion k.val=coordRegion (j.val+1) := congrArg coordRegion hk
      rcases hw with hw|hw|hw
      · exact localW_pads (coordRegion k.val) ck A (by rcases jp with jp|jp <;> omega) hw
      · omega
      · omega
    · have g2:coordRegion k.val+848≤coordRegion (j.val+1) := by
        unfold coordRegion
        omega
      omega
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.Research.SharedPathPacking
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
structure CoordinateReadout (s : MachineState) (k child : Nat) (t : MachineState) : Prop where
  values : ∀i<6,∀half<2,t.getMem (BitVec.ofNat 64 (coordRegion k+(640+40*(i-(i-1))+72*(i/5)-52*i-124*(i%2))+8*half))=s.getMem (BitVec.ofNat 64 (coordSource k+16*i+8*half))
  ends : ∀i<6,0 < i → ∀half<2,t.getMem (BitVec.ofNat 64 (coordRegion k+672+16*i+8*half))=s.getMem (BitVec.ofNat 64 (coordSource k+16*i+8*half))
  paths : ∀i<5,∀half<2,t.getMem (BitVec.ofNat 64 (pathDestination (coordRegion k) child (packedSlots child) i+8*half))=s.getMem (BitVec.ofNat 64 (coordSource k+96+16*i+8*half))
  sixth : ¬firstCoord k → ∀half<2,t.getMem (BitVec.ofNat 64 (destination (coordRegion k) 49 (child/32)+8*half))=s.getMem (BitVec.ofNat 64 (coordSource k+176+8*half))
  top : ∀half<2,t.getMem (BitVec.ofNat 64 (topDest k child+8*half))=s.getMem (BitVec.ofNat 64 (coordSource k+topInput k+8*half))

theorem CoordinatePost.readout {s t : MachineState} {k child : Nat} (h:CoordinatePost s k child t) :
    CoordinateReadout s k child t := ⟨h.values,h.ends,h.paths,h.sixth,h.top⟩

theorem CoordinateReadout.congr {s u v : MachineState} (k : Fin 9) (child : Fin 128)
    (h:CoordinateReadout s k.val child.val u)
    (he:∀A,ReadArea k.val child.val A → v.getMem (BitVec.ofNat 64 A)=u.getMem (BitVec.ofNat 64 A)) :
    CoordinateReadout s k.val child.val v := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i hi half hh
    rw [he _ (Or.inl ⟨by omega,by omega⟩)]
    exact h.values i hi half hh
  · intro i hi hip half hh
    rw [he _ (Or.inl ⟨by omega,by omega⟩)]
    exact h.ends i hi hip half hh
  · intro i hi half hh
    have hb:=Packing.path_slot_bound (coordRegion k.val) child ⟨i,hi⟩
    change coordRegion k.val≤pathDestination (coordRegion k.val) child.val (packedSlots child.val) i ∧ pathDestination (coordRegion k.val) child.val (packedSlots child.val) i+16≤coordRegion k.val+320 at hb
    rw [he _ (Or.inl ⟨by omega,by omega⟩)]
    exact h.paths i hi half hh
  · intro hn half hh
    have hm:=Nat.mod_lt (child.val/32) (by decide:0<2)
    rw [he _ (Or.inl ⟨by unfold destination;omega,by unfold destination;omega⟩)]
    exact h.sixth hn half hh
  · intro half hh
    rw [he _ (Or.inr (by omega))]
    exact h.top half hh

theorem CoordinateReadout.source {s u t : MachineState} (k : Fin 9) (child : Fin 128)
    (h:CoordinateReadout u k.val child.val t)
    (he:∀A,coordSource k.val≤A → A<coordSource k.val+208 → u.getMem (BitVec.ofNat 64 A)=s.getMem (BitVec.ofNat 64 A)) :
    CoordinateReadout s k.val child.val t := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i hi half hh
    rw [h.values i hi half hh,he _ (by omega) (by omega)]
  · intro i hi hip half hh
    rw [h.ends i hi hip half hh,he _ (by omega) (by omega)]
  · intro i hi half hh
    rw [h.paths i hi half hh,he _ (by omega) (by omega)]
  · intro hn half hh
    rw [h.sixth hn half hh,he _ (by omega) (by omega)]
  · intro half hh
    have hb:topInput k.val≤192:=by unfold topInput;split_ifs <;>omega
    rw [h.top half hh,he _ (by omega) (by omega)]
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.Research.SharedPathPacking
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem steps_same {im:Image} {s t u:MachineState} {n c d:Nat}
    (h:Steps im s n c t) (h':Steps im s n d u) : t=u := by
  induction h generalizing d u with
  | refl => cases h';rfl
  | @step s v t ins n c hf hs tail ih =>
    cases h' with
    | @step s' v' u' ins' n' d' hf' hs' tail' =>
      have he:ins'=ins:=Option.some.inj (hf'.symm.trans hf)
      subst ins'
      have hv:v'=v:=Option.some.inj (hs'.symm.trans hs)
      subst v'
      exact ih tail'

def PreciseBodyW (k child A:Nat) : Prop :=
  PayloadW (coordRegion k) child (packedSlots child) A ∨ (¬firstCoord k ∧ SixthW (coordRegion k) child A)

def PreciseCoordinateW (k child A:Nat) : Prop := PreciseBodyW k child A ∨ A=topDest k child ∨ A=topDest k child+8

theorem body_frame_exact {im:Image} (k:Fin 9) (hv:ValuesCode im (valueStart k.val))
    (hp:CodeAt im (pcOf (planStart k.val)) planCode) (hd:PathsCode im (pathStart k.val))
    (hx:¬firstCoord k.val → CodeAt im (pcOf (valueStart k.val+110)) sixthCode)
    (s t:MachineState) (hpc:s.pc=pcOf (valueStart k.val)) (child:Fin 128)
    (h8:s.getReg .x8=BitVec.ofNat 64 (coordRegion k.val)) (h16:s.getReg .x16=BitVec.ofNat 64 child.val)
    (h17:s.getReg .x17=BitVec.ofNat 64 (coordSource k.val))
    (hbytes:∀j<5,s.getByte (BitVec.ofNat 64 (16748432+5*(child.val%32)+j))=BitVec.ofNat 8 (packedSlots child.val j))
    (hst:Steps im s (bodyInstructions k.val) (bodyCycles k.val) t) : Frame s t (PreciseBodyW k.val child.val) := by
  by_cases ha:firstCoord k.val
  · have hb : valueStart k.val=45266 ∨ valueStart k.val=45400 ∨ valueStart k.val=45543 ∨ valueStart k.val=45677 ∨ valueStart k.val=45820 ∨ valueStart k.val=45954 ∨ valueStart k.val=46097 ∨ valueStart k.val=46231 ∨ valueStart k.val=46376 := by fin_cases k <;> decide
    have hpl:valueStart k.val+34=planStart k.val:=by fin_cases k <;>decide
    have hpa:valueStart k.val+40=pathStart k.val:=by fin_cases k <;>decide
    have rb:=coordRegion_bounds k
    have sb:=coordSource_bounds k
    obtain ⟨u,su,hu⟩:=payload_packed hb hv (by rw [hpl];exact hp) (by rw [hpa];exact hd)
      s hpc (coordRegion k.val) (coordSource k.val) child rb.1 rb.2.1 rb.2.2 sb.1 sb.2.1 sb.2.2 h8 h16 h17 hbytes
    have ht:u=t:=steps_same su (by simpa [bodyInstructions,bodyCycles,ha] using hst)
    subst t
    exact hu.frame.mono (by intro A hA h;exact Or.inl h)
  · obtain ⟨u,su,hu⟩:=body_steps k hv hp hd hx s hpc child h8 h16 h17 hbytes
    have ht:u=t:=steps_same su hst
    subst t
    exact hu.frame.mono (by intro A hA h;rcases h with h|h;exact Or.inl h;exact Or.inr ⟨ha,h⟩)

theorem coordinate_frame_exact {im:Image} (k:Fin 9) (hc:CoordinateCode im k.val)
    (s t:MachineState) (hp:s.pc=pcOf (entryStart k.val)) (raw:Fin 128)
    (hraw:s.getMem (BitVec.ofNat 64 (rawAddress k.val)) >>> rawShift k.val &&& 127#64=BitVec.ofNat 64 raw.val)
    (hbytes:∀j<5,s.getByte (BitVec.ofNat 64 (16748432+5*(coordPhysical k.val raw.val%32)+j))=BitVec.ofNat 8 (packedSlots (coordPhysical k.val raw.val) j))
    (hst:Steps im s (coordinateInstructions k.val) (coordinateCycles k.val) t)
    (h8in : k.val=8 → s.getReg .x8=BitVec.ofNat 64 3832) :
    Frame s t (PreciseCoordinateW k.val (coordPhysical k.val raw.val)) := by
  let child:Fin 128:=⟨coordPhysical k.val raw.val,coordPhysical_lt k.val raw⟩
  obtain ⟨u,su,up,u16,u8,u17,ur,uf⟩:=entry_setup k hc.entry s hp raw hraw h8in
  have hbytesu:∀j<5,u.getByte (BitVec.ofNat 64 (16748432+5*(child.val%32)+j))=BitVec.ofNat 8 (packedSlots child.val j) := by
    intro j hj
    rw [uf.getByte (by have:=Nat.mod_lt child.val (by decide:0<32);omega) (by simp)]
    exact hbytes j hj
  obtain ⟨v,uv,hv⟩:=body_steps k hc.values hc.plan hc.paths hc.sixth u up child u8 u16 u17 hbytesu
  have hf:=body_frame_exact k hc.values hc.plan hc.paths hc.sixth u v up child u8 u16 u17 hbytesu uv
  have sb:=coordSource_bounds k
  obtain ⟨z,vz,zp,zt,zr,zf⟩:=top_copy k hc.top v hv.pc (coordSource k.val) child sb.1 sb.2.1 sb.2.2
    (by rw [hv.regs.get (by decide),u16]) (by rw [hv.regs.get (by decide),u17]) (by rw [hv.regs.get (by decide),u8])
  have hsz:Steps im s (coordinateInstructions k.val) (coordinateCycles k.val) z:=((su.trans uv).trans vz).of_eq (by rfl) (by unfold coordinateCycles;omega)
  have hz:z=t:=steps_same hsz hst
  subst t
  exact ((uf.trans hf).trans zf).mono (by intro A hA h;rcases h with (h|h)|h;exact h.elim;exact Or.inl h;exact Or.inr h)
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.Research.SharedPathPacking
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

def scatterPC (n:Nat) : Nat := if n<9 then entryStart n else 46509
/-- Pairing stage 1: the scatter writes stay below `11000 = WIT + 8096` (the compactor's layer area). -/
def ScatterW (A:Nat) : Prop := 1152≤A ∧ A<11000

theorem preciseCoordinateW_bounds (k : Fin 9) (child : Fin 128) (A : Nat)
    (h : PreciseCoordinateW k.val child.val A) : 1200 ≤ A ∧ A+8 ≤ 11000 := by
  have hr:=coordRegion_bounds k
  have hcw : CoordinateW k.val child.val A := by
    rcases h with (h|⟨_,h⟩)|h|h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hb:=coordinateW_bounds k child A hcw
  refine ⟨hb.1,?_⟩
  rcases h with (h|⟨hf,h⟩)|h|h
  · rcases h with h|h
    · obtain ⟨i,hi,h⟩:=h
      have : coordRegion k.val ≤ 10152 := hr.2.1
      omega
    · obtain ⟨i,hi,h⟩:=h
      have hb:=Packing.path_slot_bound (coordRegion k.val) child ⟨i,hi⟩
      change coordRegion k.val ≤ pathDestination (coordRegion k.val) child.val (packedSlots child.val) i ∧
        pathDestination (coordRegion k.val) child.val (packedSlots child.val) i+16 ≤ coordRegion k.val+320 at hb
      omega
  · have hk : k.val ≠ 0 := by intro h0; apply hf; unfold firstCoord; omega
    have : coordRegion k.val ≤ 9256 := by unfold coordRegion; omega
    omega
  · have hb:=topDest_bound k child; omega
  · have hb:=topDest_bound k child; omega
structure ScatterInv (s : MachineState) (raw:Fin 9 → Fin 128) (n:Nat) (t:MachineState) : Prop where
  pc:t.pc=pcOf (scatterPC n)
  readout:∀k:Fin 9,k.val<n → CoordinateReadout s k.val (coordPhysical k.val (raw k).val) t
  regs:RegsExcept s t [.x6,.x7,.x8,.x16,.x17,.x18,.x28]
  frame:Frame s t ScatterW
  exactFrame:Frame s t (fun A=>∃k:Fin 9,k.val<n ∧ PreciseCoordinateW k.val (coordPhysical k.val (raw k).val) A)
  x8:0<n → t.getReg .x8=BitVec.ofNat 64 (coordRegion (n-1))

def RawAt (s:MachineState) (raw:Fin 9 → Fin 128) : Prop := ∀k:Fin 9,
  s.getMem (BitVec.ofNat 64 (rawAddress k.val)) >>> rawShift k.val &&& 127#64=BitVec.ofNat 64 (raw k).val

def PlanAt (s:MachineState) : Prop := ∀child:Fin 128,∀j<5,
  s.getByte (BitVec.ofNat 64 (16748432+5*(child.val%32)+j))=BitVec.ofNat 8 (packedSlots child.val j)

theorem ScatterInv.next {im:Image} {s t:MachineState} {raw:Fin 9 → Fin 128} (k:Fin 9)
    (hc:CoordinateCode im k.val) (hr:RawAt s raw) (hp:PlanAt s) (hi:ScatterInv s raw k.val t) :
    ∃u,Steps im t (coordinateInstructions k.val) (coordinateCycles k.val) u ∧ ScatterInv s raw (k.val+1) u := by
  have hrawaddr : 11064≤rawAddress k.val ∧ rawAddress k.val<2^64 := by fin_cases k <;> decide
  have hraw : t.getMem (BitVec.ofNat 64 (rawAddress k.val)) >>> rawShift k.val &&& 127#64=BitVec.ofNat 64 (raw k).val := by
    rw [hi.frame.get hrawaddr.2 (by unfold ScatterW;omega)]
    exact hr k
  have hpc:t.pc=pcOf (entryStart k.val):=by simpa [scatterPC,k.isLt] using hi.pc
  have hbytes:∀j<5,t.getByte (BitVec.ofNat 64 (16748432+5*(coordPhysical k.val (raw k).val%32)+j))=BitVec.ofNat 8 (packedSlots (coordPhysical k.val (raw k).val) j) := by
    intro j hj
    rw [hi.frame.getByte (by have:=Nat.mod_lt (coordPhysical k.val (raw k).val) (by decide:0<32);omega) (by unfold ScatterW;omega)]
    exact hp ⟨coordPhysical k.val (raw k).val,coordPhysical_lt k.val (raw k)⟩ j hj
  have h8in : k.val=8 → t.getReg .x8=BitVec.ofNat 64 3832 := by
    intro hk8
    rw [hi.x8 (by omega),hk8]
    rfl
  obtain ⟨u,tu,hu⟩:=coordinate_steps k hc t hpc (raw k) hraw hbytes h8in
  have hprecise:=coordinate_frame_exact k hc t u hpc (raw k) hraw hbytes tu h8in
  have hw : ∀A,A<2^64 → PreciseCoordinateW k.val (coordPhysical k.val (raw k).val) A → ScatterW A := by
    intro A hA hw
    have hb:=preciseCoordinateW_bounds k ⟨coordPhysical k.val (raw k).val,coordPhysical_lt k.val (raw k)⟩ A hw
    unfold ScatterW
    omega
  refine ⟨u,tu,?_,?_,(hi.regs.trans hu.regs).mono (by simp),(hi.frame.trans (hprecise.mono hw)).mono (by intro A hA h;exact h.elim id id),?_,fun _=>by simpa using hu.x8⟩
  · have he:nextEntry k.val=scatterPC (k.val+1) := by fin_cases k <;> decide
    simpa [he] using hu.pc
  · intro j hj
    by_cases he:j.val=k.val
    · have je:j=k:=Fin.ext he
      subst j
      apply CoordinateReadout.source k ⟨coordPhysical k.val (raw k).val,coordPhysical_lt k.val (raw k)⟩ hu.readout
      intro A ha hb
      have sb:=coordSource_bounds k
      exact hi.frame.get (by omega) (by unfold ScatterW;omega)
    · have hjk:j.val<k.val:=by omega
      apply (hi.readout j hjk).congr j ⟨coordPhysical j.val (raw j).val,coordPhysical_lt j.val (raw j)⟩
      intro A ha
      have hA:A<2^64 := by
        rcases ha with ha|ha|ha
        · have rb:=coordRegion_bounds j;omega
        · have td:=topDest_bound j ⟨coordPhysical j.val (raw j).val,coordPhysical_lt j.val (raw j)⟩;have rb:=coordRegion_bounds j;omega
        · have td:=topDest_bound j ⟨coordPhysical j.val (raw j).val,coordPhysical_lt j.val (raw j)⟩;have rb:=coordRegion_bounds j;omega
      exact hu.frame.get hA (readArea_disjoint j k hjk ⟨_,coordPhysical_lt j.val (raw j)⟩ ⟨_,coordPhysical_lt k.val (raw k)⟩ A ha)
  · exact (hi.exactFrame.trans hprecise).mono (by
      intro A hA h
      rcases h with ⟨j,hj,h⟩|h
      · exact ⟨j,by omega,h⟩
      · exact ⟨k,by omega,h⟩)

def scatterInstructions (n:Nat) : Nat := ((List.range n).map coordinateInstructions).sum
def scatterCycles (n:Nat) : Nat := ((List.range n).map coordinateCycles).sum

theorem scatter_steps {im:Image} (hc:∀k:Fin 9,CoordinateCode im k.val) (s:MachineState)
    (raw:Fin 9 → Fin 128) (hr:RawAt s raw) (hp:PlanAt s) (hpc:s.pc=pcOf 45257) :
    ∃t,Steps im s 1252 1429 t ∧ ScatterInv s raw 9 t := by
  have hn : ∀n,n≤9 → ∃t,Steps im s (scatterInstructions n) (scatterCycles n) t ∧ ScatterInv s raw n t := by
    intro n
    induction n with
    | zero =>
      intro hn
      exact ⟨s,Steps.refl s,hpc,fun k hk=>by omega,RegsExcept.refl _ _,Frame.refl _ _,Frame.refl _ _,fun h=>absurd h (Nat.lt_irrefl 0)⟩
    | succ n ih =>
      intro hn
      obtain ⟨t,st,ht⟩:=ih (by omega)
      obtain ⟨u,tu,hu⟩:=ht.next ⟨n,by omega⟩ (hc ⟨n,by omega⟩) hr hp
      refine ⟨u,?_,hu⟩
      simpa [scatterInstructions,scatterCycles,List.range_succ] using st.trans tu
  simpa [scatterInstructions,scatterCycles,coordinateTotals.1,coordinateTotals.2] using hn 9 (by decide)
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
set_option maxHeartbeats 1000000
theorem coordinateCodes {im:Image}
    (he:∀k:Fin 9,CodeAt im (pcOf (entryStart k.val)) (entryWords k.val))
    (hv:∀k:Fin 9,ValuesCode im (valueStart k.val))
    (hp:∀k:Fin 9,CodeAt im (pcOf (planStart k.val)) planCode)
    (hd:∀k:Fin 9,PathsCode im (pathStart k.val))
    (hx:∀k:Fin 5,CodeAt im (pcOf (sixthStart k.val)) sixthCode)
    (ht:∀k:Fin 9,CodeAt im (pcOf (topStart k.val)) (topWords k.val)) :
    ∀k:Fin 9,CoordinateCode im k.val := by
  intro k
  refine ⟨he k,hv k,hp k,hd k,?_,ht k⟩
  intro hn
  fin_cases k <;> simp only [firstCoord] at hn
  · exact (hn (by decide)).elim
  · exact hx 0
  · exact (hn (by decide)).elim
  · exact hx 1
  · exact (hn (by decide)).elim
  · exact hx 2
  · exact (hn (by decide)).elim
  · exact hx 3
  · exact hx 4
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv

theorem installed_coordinates : ∀k:Fin 9,CoordinateCode Images.expandImage k.val :=
  coordinateCodes installed_entry installed_values installed_plan installed_paths installed_sixth installed_top
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 1000000

end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedCompact
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

-- T51 (KEYCODEC's kernel-cheap proofs: no per-case `rfl` through `inflatedRead` / `digC`).
theorem inflated_coordinate_value (b : SharedCodec.CBytes) (k : Fin 9) (i : Fin 6) :
    SharedCodec.inflatedRead (0 : Digest) (SharedCodec.digC b) (1+13*k.val+i.val)=
      Paired.coordinateValues (SharedCodec.sigDecC b).forest k i := by
  have hk := k.isLt
  have hi := i.isLt
  unfold Paired.coordinateValues
  split
  · rename_i h8
    split
    · rename_i h2
      rw [show 1 + 13 * k.val + i.val = SharedCodec.internalFullIndex (1 + 25 * (k.val / 2) + i.val) by
        unfold SharedCodec.internalFullIndex; split_ifs <;> omega, SharedCodec.inflatedRead_internal]
      rfl
    · rename_i h2
      rw [show 1 + 13 * k.val + i.val = SharedCodec.internalFullIndex (1 + 25 * (k.val / 2) + 12 + i.val) by
        unfold SharedCodec.internalFullIndex; split_ifs <;> omega, SharedCodec.inflatedRead_internal]
      rfl
  · rename_i h8
    rw [show 1 + 13 * k.val + i.val = SharedCodec.internalFullIndex (101 + i.val) by
      unfold SharedCodec.internalFullIndex; split_ifs <;> omega, SharedCodec.inflatedRead_internal]
    rfl

theorem inflated_coordinate_path (b : SharedCodec.CBytes) (k : Fin 9) (level : Nat)
    (hl : level < if k.val<8 ∧ k.val%2=0 then 6 else 7) :
    SharedCodec.inflatedRead (0 : Digest) (SharedCodec.digC b) (1+13*k.val+6+level)=
      Paired.coordinatePath (SharedCodec.sigDecC b).forest k level := by
  have hk := k.isLt
  unfold Paired.coordinatePath
  split
  · rename_i h8
    split
    · rename_i h2
      rw [if_pos ⟨h8, h2⟩] at hl
      rw [show 1 + 13 * k.val + 6 + level = SharedCodec.internalFullIndex (1 + 25 * (k.val / 2) + 6 + level % 6) by
        rw [Nat.mod_eq_of_lt hl]; unfold SharedCodec.internalFullIndex; split_ifs <;> omega,
        SharedCodec.inflatedRead_internal]
      rfl
    · rename_i h2
      rw [if_neg (fun h => h2 h.2)] at hl
      rw [show 1 + 13 * k.val + 6 + level = SharedCodec.internalFullIndex (1 + 25 * (k.val / 2) + 18 + level % 7) by
        rw [Nat.mod_eq_of_lt hl]; unfold SharedCodec.internalFullIndex; split_ifs <;> omega,
        SharedCodec.inflatedRead_internal]
      rfl
  · rename_i h8
    rw [if_neg (fun h => h8 h.1)] at hl
    rw [show 1 + 13 * k.val + 6 + level = SharedCodec.internalFullIndex (107 + level % 7) by
      rw [Nat.mod_eq_of_lt hl]; unfold SharedCodec.internalFullIndex; split_ifs <;> omega,
      SharedCodec.inflatedRead_internal]
    rfl
end ClaudeWCT.W9.Machine.Expand.SharedCompact
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_CanonV6Validate ====
section

/-! # img-v6 expand final policy check (canon-v6 porter)

Machine proof of the expand policy check at 46929..46979 for the img-v6 image: credit pool 69, policy hints in
the mixed radix `484·f1 + 22·f2 + f3`, L1 floors by residual `< 56`, L2 `< 41`, L3 floor = residual `< 22`.
Adapted from `SharedValidate` in `Expand/H2Front.lean` (e7b: pool 72, radix 20); new namespace
`SharedValidateV6`, result `validate_source_steps` against `SharedForest.policyHintsValid` (bound 7744). -/

namespace ClaudeWCT.W9.Machine.Expand.SharedValidateV6
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
def first0Code : List (BitVec 32) := [0x66e37,0xe0e13,0x40e3303,0x1536663]
sym_block first0Run := symRun {noAlias:=true} first0Code (pcOf 46933) 20
def zero0Code : List (BitVec 32) := [0xa93,0x80006f]
sym_block zero0Run := symRun {noAlias:=true} zero0Code (pcOf 46937) 20
def sub0Code : List (BitVec 32) := [0x406a8ab3]
sym_block sub0Run := symRun {noAlias:=true} sub0Code (pcOf 46939) 20
theorem first0_steps {im : Image} (hc : CodeAt im (pcOf 46933) first0Code)
    (s : MachineState) (hp : s.pc=pcOf 46933) (R C : Nat) (hR : R≤69) (hC : C<2^64)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (hm : s.getMem 417856=BitVec.ofNat 64 C) :
    ∃t,Steps im s 4 4 t ∧ t.pc=(if C<R then pcOf 46939 else pcOf 46937) ∧
      t.getReg .x6=BitVec.ofNat 64 C ∧ RegsExcept s t [.x6,.x28] ∧ Frame s t (fun _=>False) := by
  change s.getMem (417856#64)=BitVec.ofNat 64 C at hm
  refine ⟨_,symRun_sound first0Run hc s hp (by simp [first0Run.res,rv_simp]),?_,?_,?_,?_⟩
  · simp only [Result.toState_pc,first0Run.res]
    t3n [h21,hm]
    simp only [BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hC,Nat.mod_eq_of_lt (show R<2^64 by omega)]
    simp only [decide_eq_true_eq]
    all_goals split_ifs <;> rfl
  · simp [first0Run.res,rv_simp,hm]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

theorem zero0_steps {im : Image} (hc : CodeAt im (pcOf 46937) zero0Code)
    (s : MachineState) (hp : s.pc=pcOf 46937) :
    ∃t,Steps im s 2 2 t ∧ t.pc=pcOf 46940 ∧ t.getReg .x21=0 ∧
      RegsExcept s t [.x21] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound zero0Run hc s hp (by simp [zero0Run.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · rfl
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

theorem sub0_steps {im : Image} (hc : CodeAt im (pcOf 46939) sub0Code)
    (s : MachineState) (hp : s.pc=pcOf 46939) (R C : Nat) (hR : R≤69) (hC : C<R)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (h6 : s.getReg .x6=BitVec.ofNat 64 C) :
    ∃t,Steps im s 1 1 t ∧ t.pc=pcOf 46940 ∧ t.getReg .x21=BitVec.ofNat 64 (R-C) ∧
      RegsExcept s t [.x21] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound sub0Run hc s hp (by simp [sub0Run.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · simp only [Result.toState_getReg,sub0Run.res]
    t3n [h21,h6]
    exact BitVec.ofNat_sub_ofNat_of_le R C (by omega) (by omega)
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

class Residual0Code (im : Image) : Prop where
  first : CodeAt im (pcOf 46933) first0Code
  zero : CodeAt im (pcOf 46937) zero0Code
  sub : CodeAt im (pcOf 46939) sub0Code

theorem residual0_steps {im : Image} [hc : Residual0Code im]
    (s : MachineState) (hp : s.pc=pcOf 46933) (R C : Nat) (hR : R≤69) (hC : C<2^64)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (hm : s.getMem 417856=BitVec.ofNat 64 C) :
    ∃t n,n≤6 ∧ Steps im s n n t ∧ t.pc=pcOf 46940 ∧ t.getReg .x21=BitVec.ofNat 64 (R-C) ∧
      RegsExcept s t [.x6,.x21,.x28] ∧ Frame s t (fun _=>False) := by
  obtain ⟨u,su,pu,u6,ru,fu⟩:=first0_steps hc.first s hp R C hR hC h21 hm
  by_cases h : C<R
  · rw [if_pos h] at pu
    obtain ⟨t,st,pt,ht,rr,ff⟩:=sub0_steps hc.sub u pu R C hR h (by rw [ru.get (by decide)];exact h21) u6
    exact ⟨t,5,by omega,su.trans st,pt,ht,(ru.trans rr).mono (by decide),(fu.trans ff).mono (by simp)⟩
  · rw [if_neg h] at pu
    obtain ⟨t,st,pt,ht,rr,ff⟩:=zero0_steps hc.zero u pu
    exact ⟨t,6,by omega,su.trans st,pt,by simpa [show R-C=0 by omega] using ht,
      (ru.trans rr).mono (by decide),(fu.trans ff).mono (by simp)⟩
def first1Code : List (BitVec 32) := [0x66e37,0xe0e13,0x48e3303,0x1536663]
sym_block first1Run := symRun {noAlias:=true} first1Code (pcOf 46949) 20
def zero1Code : List (BitVec 32) := [0xa93,0x80006f]
sym_block zero1Run := symRun {noAlias:=true} zero1Code (pcOf 46953) 20
def sub1Code : List (BitVec 32) := [0x406a8ab3]
sym_block sub1Run := symRun {noAlias:=true} sub1Code (pcOf 46955) 20
theorem first1_steps {im : Image} (hc : CodeAt im (pcOf 46949) first1Code)
    (s : MachineState) (hp : s.pc=pcOf 46949) (R C : Nat) (hR : R≤69) (hC : C<2^64)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (hm : s.getMem 417864=BitVec.ofNat 64 C) :
    ∃t,Steps im s 4 4 t ∧ t.pc=(if C<R then pcOf 46955 else pcOf 46953) ∧
      t.getReg .x6=BitVec.ofNat 64 C ∧ RegsExcept s t [.x6,.x28] ∧ Frame s t (fun _=>False) := by
  change s.getMem (417864#64)=BitVec.ofNat 64 C at hm
  refine ⟨_,symRun_sound first1Run hc s hp (by simp [first1Run.res,rv_simp]),?_,?_,?_,?_⟩
  · simp only [Result.toState_pc,first1Run.res]
    t3n [h21,hm]
    simp only [BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hC,Nat.mod_eq_of_lt (show R<2^64 by omega)]
    simp only [decide_eq_true_eq]
    all_goals split_ifs <;> rfl
  · simp [first1Run.res,rv_simp,hm]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

theorem zero1_steps {im : Image} (hc : CodeAt im (pcOf 46953) zero1Code)
    (s : MachineState) (hp : s.pc=pcOf 46953) :
    ∃t,Steps im s 2 2 t ∧ t.pc=pcOf 46956 ∧ t.getReg .x21=0 ∧
      RegsExcept s t [.x21] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound zero1Run hc s hp (by simp [zero1Run.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · rfl
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

theorem sub1_steps {im : Image} (hc : CodeAt im (pcOf 46955) sub1Code)
    (s : MachineState) (hp : s.pc=pcOf 46955) (R C : Nat) (hR : R≤69) (hC : C<R)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (h6 : s.getReg .x6=BitVec.ofNat 64 C) :
    ∃t,Steps im s 1 1 t ∧ t.pc=pcOf 46956 ∧ t.getReg .x21=BitVec.ofNat 64 (R-C) ∧
      RegsExcept s t [.x21] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound sub1Run hc s hp (by simp [sub1Run.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · simp only [Result.toState_getReg,sub1Run.res]
    t3n [h21,h6]
    exact BitVec.ofNat_sub_ofNat_of_le R C (by omega) (by omega)
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

class Residual1Code (im : Image) : Prop where
  first : CodeAt im (pcOf 46949) first1Code
  zero : CodeAt im (pcOf 46953) zero1Code
  sub : CodeAt im (pcOf 46955) sub1Code

theorem residual1_steps {im : Image} [hc : Residual1Code im]
    (s : MachineState) (hp : s.pc=pcOf 46949) (R C : Nat) (hR : R≤69) (hC : C<2^64)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (hm : s.getMem 417864=BitVec.ofNat 64 C) :
    ∃t n,n≤6 ∧ Steps im s n n t ∧ t.pc=pcOf 46956 ∧ t.getReg .x21=BitVec.ofNat 64 (R-C) ∧
      RegsExcept s t [.x6,.x21,.x28] ∧ Frame s t (fun _=>False) := by
  obtain ⟨u,su,pu,u6,ru,fu⟩:=first1_steps hc.first s hp R C hR hC h21 hm
  by_cases h : C<R
  · rw [if_pos h] at pu
    obtain ⟨t,st,pt,ht,rr,ff⟩:=sub1_steps hc.sub u pu R C hR h (by rw [ru.get (by decide)];exact h21) u6
    exact ⟨t,5,by omega,su.trans st,pt,ht,(ru.trans rr).mono (by decide),(fu.trans ff).mono (by simp)⟩
  · rw [if_neg h] at pu
    obtain ⟨t,st,pt,ht,rr,ff⟩:=zero1_steps hc.zero u pu
    exact ⟨t,6,by omega,su.trans st,pt,by simpa [show R-C=0 by omega] using ht,
      (ru.trans rr).mono (by decide),(fu.trans ff).mono (by simp)⟩
def first2Code : List (BitVec 32) := [0x66e37,0xe0e13,0x50e3303,0x1536663]
sym_block first2Run := symRun {noAlias:=true} first2Code (pcOf 46966) 20
def zero2Code : List (BitVec 32) := [0xa93,0x80006f]
sym_block zero2Run := symRun {noAlias:=true} zero2Code (pcOf 46970) 20
def sub2Code : List (BitVec 32) := [0x406a8ab3]
sym_block sub2Run := symRun {noAlias:=true} sub2Code (pcOf 46972) 20
theorem first2_steps {im : Image} (hc : CodeAt im (pcOf 46966) first2Code)
    (s : MachineState) (hp : s.pc=pcOf 46966) (R C : Nat) (hR : R≤69) (hC : C<2^64)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (hm : s.getMem 417872=BitVec.ofNat 64 C) :
    ∃t,Steps im s 4 4 t ∧ t.pc=(if C<R then pcOf 46972 else pcOf 46970) ∧
      t.getReg .x6=BitVec.ofNat 64 C ∧ RegsExcept s t [.x6,.x28] ∧ Frame s t (fun _=>False) := by
  change s.getMem (417872#64)=BitVec.ofNat 64 C at hm
  refine ⟨_,symRun_sound first2Run hc s hp (by simp [first2Run.res,rv_simp]),?_,?_,?_,?_⟩
  · simp only [Result.toState_pc,first2Run.res]
    t3n [h21,hm]
    simp only [BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hC,Nat.mod_eq_of_lt (show R<2^64 by omega)]
    simp only [decide_eq_true_eq]
    all_goals split_ifs <;> rfl
  · simp [first2Run.res,rv_simp,hm]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

theorem zero2_steps {im : Image} (hc : CodeAt im (pcOf 46970) zero2Code)
    (s : MachineState) (hp : s.pc=pcOf 46970) :
    ∃t,Steps im s 2 2 t ∧ t.pc=pcOf 46973 ∧ t.getReg .x21=0 ∧
      RegsExcept s t [.x21] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound zero2Run hc s hp (by simp [zero2Run.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · rfl
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

theorem sub2_steps {im : Image} (hc : CodeAt im (pcOf 46972) sub2Code)
    (s : MachineState) (hp : s.pc=pcOf 46972) (R C : Nat) (hR : R≤69) (hC : C<R)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (h6 : s.getReg .x6=BitVec.ofNat 64 C) :
    ∃t,Steps im s 1 1 t ∧ t.pc=pcOf 46973 ∧ t.getReg .x21=BitVec.ofNat 64 (R-C) ∧
      RegsExcept s t [.x21] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound sub2Run hc s hp (by simp [sub2Run.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · simp only [Result.toState_getReg,sub2Run.res]
    t3n [h21,h6]
    exact BitVec.ofNat_sub_ofNat_of_le R C (by omega) (by omega)
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

class Residual2Code (im : Image) : Prop where
  first : CodeAt im (pcOf 46966) first2Code
  zero : CodeAt im (pcOf 46970) zero2Code
  sub : CodeAt im (pcOf 46972) sub2Code

theorem residual2_steps {im : Image} [hc : Residual2Code im]
    (s : MachineState) (hp : s.pc=pcOf 46966) (R C : Nat) (hR : R≤69) (hC : C<2^64)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (hm : s.getMem 417872=BitVec.ofNat 64 C) :
    ∃t n,n≤6 ∧ Steps im s n n t ∧ t.pc=pcOf 46973 ∧ t.getReg .x21=BitVec.ofNat 64 (R-C) ∧
      RegsExcept s t [.x6,.x21,.x28] ∧ Frame s t (fun _=>False) := by
  obtain ⟨u,su,pu,u6,ru,fu⟩:=first2_steps hc.first s hp R C hR hC h21 hm
  by_cases h : C<R
  · rw [if_pos h] at pu
    obtain ⟨t,st,pt,ht,rr,ff⟩:=sub2_steps hc.sub u pu R C hR h (by rw [ru.get (by decide)];exact h21) u6
    exact ⟨t,5,by omega,su.trans st,pt,ht,(ru.trans rr).mono (by decide),(fu.trans ff).mono (by simp)⟩
  · rw [if_neg h] at pu
    obtain ⟨t,st,pt,ht,rr,ff⟩:=zero2_steps hc.zero u pu
    exact ⟨t,6,by omega,su.trans st,pt,by simpa [show R-C=0 by omega] using ht,
      (ru.trans rr).mono (by decide),(fu.trans ff).mono (by simp)⟩
end ClaudeWCT.W9.Machine.Expand.SharedValidateV6

namespace ClaudeWCT.W9.Machine.Expand.SharedValidateV6
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
def initCode : List (BitVec 32) := [0x66e37,0xe0e13,0xe3a03,0x4500a93]
sym_block initRun := symRun {noAlias:=true} initCode (pcOf 46929) 100
def range1Code : List (BitVec 32) := [0x3800393,0x87afc63]
sym_block range1Run := symRun {noAlias:=true} range1Code (pcOf 46940) 100
def range2Code : List (BitVec 32) := [0x2900393,0x47afc63]
sym_block range2Run := symRun {noAlias:=true} range2Code (pcOf 46956) 100
def range3Code : List (BitVec 32) := [0x1600393,0x7afa63]
sym_block range3Run := symRun {noAlias:=true} range3Code (pcOf 46973) 100
def lastCode : List (BitVec 32) := [0x1600393,0x27a7eb3,0x1da9463]
sym_block lastRun := symRun {noAlias:=true} lastCode (pcOf 46975) 100
def goodCode : List (BitVec 32) := [0xea5fb06f]
sym_block goodRun := symRun {noAlias:=true} goodCode (pcOf 46978) 100
def badCode : List (BitVec 32) := [0xf7cd206f]
sym_block badRun := symRun {noAlias:=true} badCode (pcOf 46979) 100
theorem range1_steps {im : Image} (hc : CodeAt im (pcOf 46940) range1Code)
    (s : MachineState) (hp : s.pc=pcOf 46940) (R : Nat) (hR : R≤69)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) :
    ∃t,Steps im s 2 2 t ∧ t.pc=(if R<56 then pcOf 46942 else pcOf 46979) ∧
      RegsExcept s t [.x7] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound range1Run hc s hp (by simp [range1Run.res,rv_simp]),?_,?_,?_⟩
  · simp only [Result.toState_pc,range1Run.res]
    t3n [h21]
    simp only [BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show R<2^64 by omega),decide_eq_true_eq]
    by_cases h : R<56 <;> simp [h]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl
theorem range2_steps {im : Image} (hc : CodeAt im (pcOf 46956) range2Code)
    (s : MachineState) (hp : s.pc=pcOf 46956) (R : Nat) (hR : R≤69)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) :
    ∃t,Steps im s 2 2 t ∧ t.pc=(if R<41 then pcOf 46958 else pcOf 46979) ∧
      RegsExcept s t [.x7] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound range2Run hc s hp (by simp [range2Run.res,rv_simp]),?_,?_,?_⟩
  · simp only [Result.toState_pc,range2Run.res]
    t3n [h21]
    simp only [BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show R<2^64 by omega),decide_eq_true_eq]
    by_cases h : R<41 <;> simp [h]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl
theorem range3_steps {im : Image} (hc : CodeAt im (pcOf 46973) range3Code)
    (s : MachineState) (hp : s.pc=pcOf 46973) (R : Nat) (hR : R≤69)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) :
    ∃t,Steps im s 2 2 t ∧ t.pc=(if R<22 then pcOf 46975 else pcOf 46979) ∧
      RegsExcept s t [.x7] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound range3Run hc s hp (by simp [range3Run.res,rv_simp]),?_,?_,?_⟩
  · simp only [Result.toState_pc,range3Run.res]
    t3n [h21]
    simp only [BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show R<2^64 by omega),decide_eq_true_eq]
    by_cases h : R<22 <;> simp [h]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl
theorem init_steps {im : Image} (hc : CodeAt im (pcOf 46929) initCode)
    (s : MachineState) (hp : s.pc=pcOf 46929) (hints : Nat)
    (hm : s.getMem (0x66000#64)=BitVec.ofNat 64 hints) :
    ∃t,Steps im s 4 4 t ∧ t.pc=pcOf 46933 ∧ t.getReg .x20=BitVec.ofNat 64 hints ∧
      t.getReg .x21=69 ∧ RegsExcept s t [.x20,.x21,.x28] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound initRun hc s hp (by simp [initRun.res,rv_simp]),rfl,?_,rfl,?_,?_⟩
  · simp [initRun.res,rv_simp,hm]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl
end ClaudeWCT.W9.Machine.Expand.SharedValidateV6

namespace ClaudeWCT.W9.Machine.Expand.SharedValidateV6
open RiscvZkvm.Rv64
theorem rem22 (n : Nat) (hn : n<2^64) : rv64_remu (BitVec.ofNat 64 n) 22#64=BitVec.ofNat 64 (n%22) := by
  apply BitVec.eq_of_toNat_eq
  simp [rv64_remu,BitVec.toNat_umod,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (show n%22<2^64 by omega)]
  omega
theorem div22 (n : Nat) (hn : n<2^64) : rv64_divu (BitVec.ofNat 64 n) 22#64=BitVec.ofNat 64 (n/22) := by
  apply BitVec.eq_of_toNat_eq
  simp [rv64_divu,BitVec.toNat_udiv,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (show n/22<2^64 by omega)]
  omega
theorem div484 (n : Nat) (hn : n<2^64) : rv64_divu (BitVec.ofNat 64 n) 484#64=BitVec.ofNat 64 (n/484) := by
  apply BitVec.eq_of_toNat_eq
  simp [rv64_divu,BitVec.toNat_udiv,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (show n/484<2^64 by omega)]
  omega
end ClaudeWCT.W9.Machine.Expand.SharedValidateV6

namespace ClaudeWCT.W9.Machine.Expand.SharedValidateV6
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
def lookup1PreCode : List (BitVec 32) := [0xff9e37,0x390e0e13,0x15e0e33]
sym_block lookup1PreRun := symRun {noAlias:=true} lookup1PreCode (pcOf 46942) 100
def lookup1LoadCode : List (BitVec 32) := [0xe4303]
def lookup1PostCode : List (BitVec 32) := [0x1e400393,0x27a5eb3,0x7d31e63]
sym_block lookup1PostRun := symRun {noAlias:=true} lookup1PostCode (pcOf 46946) 100
theorem lookup1_pre {im : Image} (hc : CodeAt im (pcOf 46942) lookup1PreCode)
    (s : MachineState) (hp : s.pc=pcOf 46942) (R : Nat) (h21 : s.getReg .x21=BitVec.ofNat 64 R) :
    ∃t,Steps im s 3 3 t ∧ t.pc=pcOf 46945 ∧ t.getReg .x28=BitVec.ofNat 64 (16749456+R) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound lookup1PreRun hc s hp (by simp [lookup1PreRun.res,rv_simp]),rfl,?_,?_,?_⟩
  · simp [lookup1PreRun.res,rv_simp,h21,BitVec.ofNat_add,add_comm]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

theorem lookup1_load {im : Image} (hc : CodeAt im (pcOf 46945) lookup1LoadCode)
    (s : MachineState) (hp : s.pc=pcOf 46945) (a F : Nat) (ha : a+1≤2^24) (hF : F<256)
    (h28 : s.getReg .x28=BitVec.ofNat 64 a) (hm : s.getByte (BitVec.ofNat 64 a)=BitVec.ofNat 8 F) :
    ∃t,Steps im s 1 1 t ∧ t.pc=pcOf 46946 ∧ t.getReg .x6=BitVec.ofNat 64 F ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _=>False) := by
  have hoff : s.getReg .x28+signExtend12 (0:BitVec 12)=BitVec.ofNat 64 a := by
    rw [h28];apply BitVec.eq_of_toNat_eq;simp [signExtend12]
  have st:=steps_lbu (rd:=.x6) (rs:=.x28) (off:=0) hc hp rfl
    (by rw [hoff,accessValid_iff,toNat_ofNat_lt (by omega)];simp [MEMORY_BYTES];omega)
  refine ⟨_,st,?_,?_,?_,?_⟩
  · show s.pc+4=pcOf 46946;rw [hp];rfl
  · rw [MachineState.getReg_setPC,MachineState.getReg_setReg_eq (by decide),hoff,hm]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.truncate_eq_setWidth,BitVec.toNat_setWidth,BitVec.toNat_ofNat]
    omega
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rw [MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr)]
  · intro A hA hn;simp

theorem lookup1_post {im : Image} (hc : CodeAt im (pcOf 46946) lookup1PostCode)
    (s : MachineState) (hp : s.pc=pcOf 46946) (H F : Nat) (hH : H<8000) (hF : F<22)
    (h6 : s.getReg .x6=BitVec.ofNat 64 F) (h20 : s.getReg .x20=BitVec.ofNat 64 H) :
    ∃t,Steps im s 3 6 t ∧ t.pc=(if F=H/484 then pcOf 46949 else pcOf 46979) ∧
      RegsExcept s t [.x7,.x29] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound lookup1PostRun hc s hp (by simp [lookup1PostRun.res,rv_simp]),?_,?_,?_⟩
  · simp only [Result.toState_pc,lookup1PostRun.res]
    t3n [h6,h20]
    simp only [div484 H (by omega)]
    have he : (BitVec.ofNat 64 F=BitVec.ofNat 64 (H/484)) ↔ F=H/484 := by
      constructor
      · intro h;have:=congrArg BitVec.toNat h;simp only [BitVec.toNat_ofNat] at this;omega
      · intro h;rw [h]
    simp only [he]
    by_cases h : F=H/484 <;> simp [h]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl
def lookup2PreCode : List (BitVec 32) := [0xff9e37,0x3d0e0e13,0x15e0e33]
sym_block lookup2PreRun := symRun {noAlias:=true} lookup2PreCode (pcOf 46958) 100
def lookup2LoadCode : List (BitVec 32) := [0xe4303]
def lookup2PostCode : List (BitVec 32) := [0x1600393,0x27a5eb3,0x27efeb3,0x3d31c63]
sym_block lookup2PostRun := symRun {noAlias:=true} lookup2PostCode (pcOf 46962) 100
theorem lookup2_pre {im : Image} (hc : CodeAt im (pcOf 46958) lookup2PreCode)
    (s : MachineState) (hp : s.pc=pcOf 46958) (R : Nat) (h21 : s.getReg .x21=BitVec.ofNat 64 R) :
    ∃t,Steps im s 3 3 t ∧ t.pc=pcOf 46961 ∧ t.getReg .x28=BitVec.ofNat 64 (16749520+R) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound lookup2PreRun hc s hp (by simp [lookup2PreRun.res,rv_simp]),rfl,?_,?_,?_⟩
  · simp [lookup2PreRun.res,rv_simp,h21,BitVec.ofNat_add,add_comm]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

theorem lookup2_load {im : Image} (hc : CodeAt im (pcOf 46961) lookup2LoadCode)
    (s : MachineState) (hp : s.pc=pcOf 46961) (a F : Nat) (ha : a+1≤2^24) (hF : F<256)
    (h28 : s.getReg .x28=BitVec.ofNat 64 a) (hm : s.getByte (BitVec.ofNat 64 a)=BitVec.ofNat 8 F) :
    ∃t,Steps im s 1 1 t ∧ t.pc=pcOf 46962 ∧ t.getReg .x6=BitVec.ofNat 64 F ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _=>False) := by
  have hoff : s.getReg .x28+signExtend12 (0:BitVec 12)=BitVec.ofNat 64 a := by
    rw [h28];apply BitVec.eq_of_toNat_eq;simp [signExtend12]
  have st:=steps_lbu (rd:=.x6) (rs:=.x28) (off:=0) hc hp rfl
    (by rw [hoff,accessValid_iff,toNat_ofNat_lt (by omega)];simp [MEMORY_BYTES];omega)
  refine ⟨_,st,?_,?_,?_,?_⟩
  · show s.pc+4=pcOf 46962;rw [hp];rfl
  · rw [MachineState.getReg_setPC,MachineState.getReg_setReg_eq (by decide),hoff,hm]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.truncate_eq_setWidth,BitVec.toNat_setWidth,BitVec.toNat_ofNat]
    omega
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rw [MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr)]
  · intro A hA hn;simp

theorem lookup2_post {im : Image} (hc : CodeAt im (pcOf 46962) lookup2PostCode)
    (s : MachineState) (hp : s.pc=pcOf 46962) (H F : Nat) (hH : H<8000) (hF : F<22)
    (h6 : s.getReg .x6=BitVec.ofNat 64 F) (h20 : s.getReg .x20=BitVec.ofNat 64 H) :
    ∃t,Steps im s 4 10 t ∧ t.pc=(if F=H/22%22 then pcOf 46966 else pcOf 46979) ∧
      RegsExcept s t [.x7,.x29] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound lookup2PostRun hc s hp (by simp [lookup2PostRun.res,rv_simp]),?_,?_,?_⟩
  · simp only [Result.toState_pc,lookup2PostRun.res]
    t3n [h6,h20]
    simp only [div22 H (by omega),rem22 (H/22) (by omega)]
    have he : (BitVec.ofNat 64 F=BitVec.ofNat 64 (H/22%22)) ↔ F=H/22%22 := by
      constructor
      · intro h;have:=congrArg BitVec.toNat h;simp only [BitVec.toNat_ofNat] at this;omega
      · intro h;rw [h]
    simp only [he]
    by_cases h : F=H/22%22 <;> simp [h]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl
end ClaudeWCT.W9.Machine.Expand.SharedValidateV6

namespace ClaudeWCT.W9.Machine.Expand.SharedValidateV6
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
theorem lookup1_steps {im : Image}
    (hpre : CodeAt im (pcOf 46942) lookup1PreCode)
    (hload : CodeAt im (pcOf 46945) lookup1LoadCode)
    (hpost : CodeAt im (pcOf 46946) lookup1PostCode)
    (s : MachineState) (hp : s.pc=pcOf 46942) (R H F : Nat) (hR : R<56) (hH : H<8000) (hF : F<22)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (h20 : s.getReg .x20=BitVec.ofNat 64 H)
    (hm : s.getByte (BitVec.ofNat 64 (16749456+R))=BitVec.ofNat 8 F) :
    ∃t,Steps im s 7 10 t ∧ t.pc=(if F=H/484 then pcOf 46949 else pcOf 46979) ∧
      RegsExcept s t [.x6,.x7,.x28,.x29] ∧ Frame s t (fun _=>False) := by
  obtain ⟨u,su,pu,u28,ru,fu⟩:=lookup1_pre hpre s hp R h21
  obtain ⟨v,sv,pv,v6,rv,fv⟩:=lookup1_load hload u pu (16749456+R) F (by omega) (by omega) u28
    (by rw [fu.getByte (by omega) (by simp)];exact hm)
  obtain ⟨t,st,pt,rt,ft⟩:=lookup1_post hpost v pv H F hH hF v6
    (by rw [rv.get (by decide),ru.get (by decide)];exact h20)
  exact ⟨t,(su.trans sv).trans st,pt,((ru.trans rv).trans rt).mono (by decide),
    ((fu.trans fv).trans ft).mono (by simp)⟩
theorem lookup2_steps {im : Image}
    (hpre : CodeAt im (pcOf 46958) lookup2PreCode)
    (hload : CodeAt im (pcOf 46961) lookup2LoadCode)
    (hpost : CodeAt im (pcOf 46962) lookup2PostCode)
    (s : MachineState) (hp : s.pc=pcOf 46958) (R H F : Nat) (hR : R<41) (hH : H<8000) (hF : F<22)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (h20 : s.getReg .x20=BitVec.ofNat 64 H)
    (hm : s.getByte (BitVec.ofNat 64 (16749520+R))=BitVec.ofNat 8 F) :
    ∃t,Steps im s 8 14 t ∧ t.pc=(if F=H/22%22 then pcOf 46966 else pcOf 46979) ∧
      RegsExcept s t [.x6,.x7,.x28,.x29] ∧ Frame s t (fun _=>False) := by
  obtain ⟨u,su,pu,u28,ru,fu⟩:=lookup2_pre hpre s hp R h21
  obtain ⟨v,sv,pv,v6,rv,fv⟩:=lookup2_load hload u pu (16749520+R) F (by omega) (by omega) u28
    (by rw [fu.getByte (by omega) (by simp)];exact hm)
  obtain ⟨t,st,pt,rt,ft⟩:=lookup2_post hpost v pv H F hH hF v6
    (by rw [rv.get (by decide),ru.get (by decide)];exact h20)
  exact ⟨t,(su.trans sv).trans st,pt,((ru.trans rv).trans rt).mono (by decide),
    ((fu.trans fv).trans ft).mono (by simp)⟩
theorem last_steps {im : Image} (hc : CodeAt im (pcOf 46975) lastCode)
    (s : MachineState) (hp : s.pc=pcOf 46975) (R H : Nat) (hR : R≤69) (hH : H<8000)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (h20 : s.getReg .x20=BitVec.ofNat 64 H) :
    ∃t,Steps im s 3 6 t ∧ t.pc=(if H%22=R then pcOf 46978 else pcOf 46979) ∧
      RegsExcept s t [.x7,.x29] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound lastRun hc s hp (by simp [lastRun.res,rv_simp]),?_,?_,?_⟩
  · simp only [Result.toState_pc,lastRun.res]
    t3n [h21,h20]
    rw [rem22 H (by omega)]
    have he : (BitVec.ofNat 64 R=BitVec.ofNat 64 (H%22)) ↔ H%22=R := by
      constructor
      · intro h;have:=congrArg BitVec.toNat h;simp only [BitVec.toNat_ofNat] at this;omega
      · intro h;rw [h]
    simp only [he]
    by_cases h : H%22=R <;> simp [h]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

theorem good_steps {im : Image} (hc : CodeAt im (pcOf 46978) goodCode) (s : MachineState) (hp : s.pc=pcOf 46978) :
    ∃t,Steps im s 1 1 t ∧ t.pc=pcOf 42795 ∧ RegsExcept s t [] ∧ Frame s t (fun _=>False) := by
  exact ⟨_,symRun_sound goodRun hc s hp (by simp [goodRun.res,rv_simp]),rfl,fun r _=>by cases r <;> rfl,fun A _ _=>rfl⟩
theorem bad_steps {im : Image} (hc : CodeAt im (pcOf 46979) badCode) (s : MachineState) (hp : s.pc=pcOf 46979) :
    ∃t,Steps im s 1 1 t ∧ t.pc=pcOf 354 ∧ RegsExcept s t [] ∧ Frame s t (fun _=>False) := by
  exact ⟨_,symRun_sound badRun hc s hp (by simp [badRun.res,rv_simp]),rfl,fun r _=>by cases r <;> rfl,fun A _ _=>rfl⟩
end ClaudeWCT.W9.Machine.Expand.SharedValidateV6

namespace ClaudeWCT.W9.Machine.Expand.SharedValidateV6
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
structure Code (im : Image) : Prop where
  init : CodeAt im (pcOf 46929) initCode
  r0 : Residual0Code im
  r1 : Residual1Code im
  r2 : Residual2Code im
  range1 : CodeAt im (pcOf 46940) range1Code
  range2 : CodeAt im (pcOf 46956) range2Code
  range3 : CodeAt im (pcOf 46973) range3Code
  lookup1Pre : CodeAt im (pcOf 46942) lookup1PreCode
  lookup1Load : CodeAt im (pcOf 46945) lookup1LoadCode
  lookup1Post : CodeAt im (pcOf 46946) lookup1PostCode
  lookup2Pre : CodeAt im (pcOf 46958) lookup2PreCode
  lookup2Load : CodeAt im (pcOf 46961) lookup2LoadCode
  lookup2Post : CodeAt im (pcOf 46962) lookup2PostCode
  last : CodeAt im (pcOf 46975) lastCode
  good : CodeAt im (pcOf 46978) goodCode
  bad : CodeAt im (pcOf 46979) badCode

def regs : List Reg := [.x6,.x7,.x21,.x28,.x29]
theorem phase1_steps {im : Image} (hc : Code im)
    (s : MachineState) (hp : s.pc=pcOf 46933) (R C H : Nat) (hR : R≤69) (hC : C<2^64) (hH : H<8000)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (h20 : s.getReg .x20=BitVec.ofNat 64 H)
    (hm : s.getMem (417856#64)=BitVec.ofNat 64 C)
    (T : Nat→Nat) (hT : ∀ r,r<56 → T r<22)
    (hbytes : ∀ r,r<56 → s.getByte (BitVec.ofNat 64 (16749456+r))=BitVec.ofNat 8 (T r)) :
    ∃t n c,n≤15 ∧ c≤18 ∧ Steps im s n c t ∧
      t.pc=(if R-C<56 ∧ H/484=T (R-C) then pcOf 46949 else pcOf 46979) ∧
      t.getReg .x21=BitVec.ofNat 64 (R-C) ∧ RegsExcept s t regs ∧ Frame s t (fun _=>False) := by
  letI:=hc.r0
  obtain ⟨u,n,hn,su,pu,u21,ru,fu⟩:=residual0_steps (im:=im) s hp R C hR hC h21 hm
  obtain ⟨v,sv,pv,rv,fv⟩:=range1_steps hc.range1 u pu (R-C) (by omega) u21
  by_cases hlt : R-C<56
  · rw [if_pos hlt] at pv
    obtain ⟨t,st,pt,rt,ft⟩:=lookup1_steps hc.lookup1Pre hc.lookup1Load hc.lookup1Post v pv
      (R-C) H (T (R-C)) hlt hH (hT _ hlt)
      (by rw [rv.get (by decide)];exact u21)
      (by rw [rv.get (by decide),ru.get (by decide)];exact h20)
      (by rw [fv.getByte (by omega) (by simp),fu.getByte (by omega) (by simp)];exact hbytes _ hlt)
    refine ⟨t,n+2+7,n+2+10,by omega,by omega,(su.trans sv).trans st,?_,?_,?_,?_⟩
    · simpa [hlt,eq_comm] using pt
    · rw [rt.get (by decide),rv.get (by decide)];exact u21
    · exact ((ru.trans rv).trans rt).mono (by decide)
    · exact ((fu.trans fv).trans ft).mono (by simp)
  · rw [if_neg hlt] at pv
    refine ⟨v,n+2,n+2,by omega,by omega,su.trans sv,?_,?_,?_,?_⟩
    · simpa [hlt] using pv
    · rw [rv.get (by decide)];exact u21
    · exact (ru.trans rv).mono (by decide)
    · exact (fu.trans fv).mono (by simp)
theorem phase2_steps {im : Image} (hc : Code im)
    (s : MachineState) (hp : s.pc=pcOf 46949) (R C H : Nat) (hR : R≤69) (hC : C<2^64) (hH : H<8000)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (h20 : s.getReg .x20=BitVec.ofNat 64 H)
    (hm : s.getMem (417864#64)=BitVec.ofNat 64 C)
    (T : Nat→Nat) (hT : ∀ r,r<41 → T r<22)
    (hbytes : ∀ r,r<41 → s.getByte (BitVec.ofNat 64 (16749520+r))=BitVec.ofNat 8 (T r)) :
    ∃t n c,n≤16 ∧ c≤22 ∧ Steps im s n c t ∧
      t.pc=(if R-C<41 ∧ H/22%22=T (R-C) then pcOf 46966 else pcOf 46979) ∧
      t.getReg .x21=BitVec.ofNat 64 (R-C) ∧ RegsExcept s t regs ∧ Frame s t (fun _=>False) := by
  letI:=hc.r1
  obtain ⟨u,n,hn,su,pu,u21,ru,fu⟩:=residual1_steps (im:=im) s hp R C hR hC h21 hm
  obtain ⟨v,sv,pv,rv,fv⟩:=range2_steps hc.range2 u pu (R-C) (by omega) u21
  by_cases hlt : R-C<41
  · rw [if_pos hlt] at pv
    obtain ⟨t,st,pt,rt,ft⟩:=lookup2_steps hc.lookup2Pre hc.lookup2Load hc.lookup2Post v pv
      (R-C) H (T (R-C)) hlt hH (hT _ hlt)
      (by rw [rv.get (by decide)];exact u21)
      (by rw [rv.get (by decide),ru.get (by decide)];exact h20)
      (by rw [fv.getByte (by omega) (by simp),fu.getByte (by omega) (by simp)];exact hbytes _ hlt)
    refine ⟨t,n+2+8,n+2+14,by omega,by omega,(su.trans sv).trans st,?_,?_,?_,?_⟩
    · simpa [hlt,eq_comm] using pt
    · rw [rt.get (by decide),rv.get (by decide)];exact u21
    · exact ((ru.trans rv).trans rt).mono (by decide)
    · exact ((fu.trans fv).trans ft).mono (by simp)
  · rw [if_neg hlt] at pv
    refine ⟨v,n+2,n+2,by omega,by omega,su.trans sv,?_,?_,?_,?_⟩
    · simpa [hlt] using pv
    · rw [rv.get (by decide)];exact u21
    · exact (ru.trans rv).mono (by decide)
    · exact (fu.trans fv).mono (by simp)
theorem phase3_steps {im : Image} (hc : Code im)
    (s : MachineState) (hp : s.pc=pcOf 46966) (R C H : Nat) (hR : R≤69) (hC : C<2^64) (hH : H<8000)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (h20 : s.getReg .x20=BitVec.ofNat 64 H)
    (hm : s.getMem (417872#64)=BitVec.ofNat 64 C) :
    ∃t n c,n≤11 ∧ c≤14 ∧ Steps im s n c t ∧
      t.pc=(if R-C<22 ∧ H%22=R-C then pcOf 46978 else pcOf 46979) ∧
      t.getReg .x21=BitVec.ofNat 64 (R-C) ∧ RegsExcept s t regs ∧ Frame s t (fun _=>False) := by
  letI:=hc.r2
  obtain ⟨u,n,hn,su,pu,u21,ru,fu⟩:=residual2_steps (im:=im) s hp R C hR hC h21 hm
  obtain ⟨v,sv,pv,rv,fv⟩:=range3_steps hc.range3 u pu (R-C) (by omega) u21
  by_cases hlt : R-C<22
  · rw [if_pos hlt] at pv
    obtain ⟨t,st,pt,rt,ft⟩:=last_steps hc.last v pv (R-C) H (by omega) hH
      (by rw [rv.get (by decide)];exact u21)
      (by rw [rv.get (by decide),ru.get (by decide)];exact h20)
    refine ⟨t,n+2+3,n+2+6,by omega,by omega,(su.trans sv).trans st,?_,?_,?_,?_⟩
    · simpa [hlt] using pt
    · rw [rt.get (by decide),rv.get (by decide)];exact u21
    · exact ((ru.trans rv).trans rt).mono (by decide)
    · exact ((fu.trans fv).trans ft).mono (by simp)
  · rw [if_neg hlt] at pv
    refine ⟨v,n+2,n+2,by omega,by omega,su.trans sv,?_,?_,?_,?_⟩
    · simpa [hlt] using pv
    · rw [rv.get (by decide)];exact u21
    · exact (ru.trans rv).mono (by decide)
    · exact (fu.trans fv).mono (by simp)
end ClaudeWCT.W9.Machine.Expand.SharedValidateV6

namespace ClaudeWCT.W9.Machine.Expand.SharedValidateV6
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 20000

abbrev Condition (H C0 C1 C2 : Nat) (T1 T2 : Nat→Nat) : Prop :=
  let R1:=69-C0
  let R2:=R1-C1
  let R3:=R2-C2
  R1<56 ∧ R2<41 ∧ R3<22 ∧ H/484=T1 R1 ∧ H/22%22=T2 R2 ∧ H%22=R3

theorem validate_steps {im : Image} (hc : Code im)
    (s : MachineState) (hp : s.pc=pcOf 46929) (H C0 C1 C2 : Nat)
    (hH : H<8000) (hC0 : C0<2^64) (hC1 : C1<2^64) (hC2 : C2<2^64)
    (hm : s.getMem (0x66000#64)=BitVec.ofNat 64 H)
    (hm0 : s.getMem (417856#64)=BitVec.ofNat 64 C0)
    (hm1 : s.getMem (417864#64)=BitVec.ofNat 64 C1)
    (hm2 : s.getMem (417872#64)=BitVec.ofNat 64 C2)
    (T1 T2 : Nat→Nat) (ht1 : ∀r,r<56→T1 r<22) (ht2 : ∀r,r<41→T2 r<22)
    (hb1 : ∀r,r<56→s.getByte (BitVec.ofNat 64 (16749456+r))=BitVec.ofNat 8 (T1 r))
    (hb2 : ∀r,r<41→s.getByte (BitVec.ofNat 64 (16749520+r))=BitVec.ofNat 8 (T2 r)) :
    ∃t n c,n≤47 ∧ c≤59 ∧ Steps im s n c t ∧
      t.pc=(if Condition H C0 C1 C2 T1 T2 then pcOf 42795 else pcOf 354) ∧
      RegsExcept s t [.x6,.x7,.x20,.x21,.x28,.x29] ∧ Frame s t (fun _=>False) := by
  obtain ⟨u,su,pu,u20,u21,ru,fu⟩:=init_steps hc.init s hp H hm
  obtain ⟨v,n1,c1,hn1,hc1,sv,pv,v21,rv,fv⟩:=phase1_steps hc u pu 69 C0 H (by omega) hC0 hH u21 u20
    (by rw [fu.get (by decide) (by simp)];exact hm0) T1 ht1
    (fun r hr=>by rw [fu.getByte (by omega) (by simp)];exact hb1 r hr)
  by_cases h1 : 69-C0<56 ∧ H/484=T1 (69-C0)
  · rw [if_pos h1] at pv
    obtain ⟨w,n2,c2,hn2,hc2,sw,pw,w21,rw_,fw⟩:=phase2_steps hc v pv (69-C0) C1 H (by omega) hC1 hH v21
      (by rw [rv.get (by decide)];exact u20)
      (by rw [fv.get (by decide) (by simp),fu.get (by decide) (by simp)];exact hm1) T2 ht2
      (fun r hr=>by rw [fv.getByte (by omega) (by simp),fu.getByte (by omega) (by simp)];exact hb2 r hr)
    by_cases h2 : 69-C0-C1<41 ∧ H/22%22=T2 (69-C0-C1)
    · rw [if_pos h2] at pw
      obtain ⟨x,n3,c3,hn3,hc3,sx,px,x21,rx,fx⟩:=phase3_steps hc w pw (69-C0-C1) C2 H (by omega) hC2 hH w21
        (by rw [rw_.get (by decide),rv.get (by decide)];exact u20)
        (by rw [fw.get (by decide) (by simp),fv.get (by decide) (by simp),fu.get (by decide) (by simp)];exact hm2)
      by_cases h3 : 69-C0-C1-C2<22 ∧ H%22=69-C0-C1-C2
      · rw [if_pos h3] at px
        obtain ⟨t,st,pt,rt,ft⟩:=good_steps hc.good x px
        refine ⟨t,4+n1+n2+n3+1,4+c1+c2+c3+1,by omega,by omega,(((su.trans sv).trans sw).trans sx).trans st,?_,?_,?_⟩
        · have hcond : Condition H C0 C1 C2 T1 T2 := by exact ⟨h1.1,h2.1,h3.1,h1.2,h2.2,h3.2⟩
          simpa only [if_pos hcond] using pt
        · exact ((((ru.trans rv).trans rw_).trans rx).trans rt).mono (by decide)
        · exact ((((fu.trans fv).trans fw).trans fx).trans ft).mono (by simp)
      · rw [if_neg h3] at px
        obtain ⟨t,st,pt,rt,ft⟩:=bad_steps hc.bad x px
        refine ⟨t,4+n1+n2+n3+1,4+c1+c2+c3+1,by omega,by omega,(((su.trans sv).trans sw).trans sx).trans st,?_,?_,?_⟩
        · have hcond : ¬Condition H C0 C1 C2 T1 T2 := by intro h;exact h3 ⟨h.2.2.1,h.2.2.2.2.2⟩
          simpa [hcond] using pt
        · exact ((((ru.trans rv).trans rw_).trans rx).trans rt).mono (by decide)
        · exact ((((fu.trans fv).trans fw).trans fx).trans ft).mono (by simp)
    · rw [if_neg h2] at pw
      obtain ⟨t,st,pt,rt,ft⟩:=bad_steps hc.bad w pw
      refine ⟨t,4+n1+n2+1,4+c1+c2+1,by omega,by omega,((su.trans sv).trans sw).trans st,?_,?_,?_⟩
      · have hcond : ¬Condition H C0 C1 C2 T1 T2 := by intro h;exact h2 ⟨h.2.1,h.2.2.2.2.1⟩
        simpa [hcond] using pt
      · exact (((ru.trans rv).trans rw_).trans rt).mono (by decide)
      · exact (((fu.trans fv).trans fw).trans ft).mono (by simp)
  · rw [if_neg h1] at pv
    obtain ⟨t,st,pt,rt,ft⟩:=bad_steps hc.bad v pv
    refine ⟨t,4+n1+1,4+c1+1,by omega,by omega,(su.trans sv).trans st,?_,?_,?_⟩
    · have hcond : ¬Condition H C0 C1 C2 T1 T2 := by intro h;exact h1 ⟨h.1,h.2.2.2.1⟩
      simpa [hcond] using pt
    · exact ((ru.trans rv).trans rt).mono (by decide)
    · exact ((fu.trans fv).trans ft).mono (by simp)
end ClaudeWCT.W9.Machine.Expand.SharedValidateV6

namespace ClaudeWCT.W9.Machine.Expand.SharedValidateV6
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem code_of_driver {im : Image}
    (hc : CodeAt im (pcOf 45056) Images.expandSharedDriver) : Code im := by
  constructor
  · exact SharedCounterHooks.code_slice (off:=1873) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · exact SharedCounterHooks.code_slice (off:=1877) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1881) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1883) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · exact SharedCounterHooks.code_slice (off:=1893) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1897) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1899) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · exact SharedCounterHooks.code_slice (off:=1910) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1914) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1916) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1884) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1900) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1917) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1886) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1889) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1890) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1902) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1905) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1906) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1919) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1922) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1923) hc (by decide +kernel) (by decide +kernel)
theorem installed_code : Code Images.expandImage := code_of_driver codeAt_expand_shared_driver
end ClaudeWCT.W9.Machine.Expand.SharedValidateV6

namespace ClaudeWCT.W9.Machine.Expand.SharedValidateV6
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.WCT9 SigGolfCandidate.Research
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

theorem credit_lt (lay : SigGolfCandidate.T3.Layer) (low : Bool) (digits : List Nat) :
    CanonicalPolicy.credit lay low digits<2^64 := by
  have hw : wordCredit lay digits≤SigGolfCandidate.T3.chainCount lay := by
    unfold wordCredit
    exact (List.length_filter_le _ _).trans_eq (List.length_range)
  have hs : savedCopies lay digits≤SigGolfCandidate.T3.chainCount lay := by
    unfold savedCopies
    exact (List.length_filter_le _ _).trans_eq (List.length_range)
  have hc : SigGolfCandidate.T3.chainCount lay≤54 := by fin_cases lay <;> decide +kernel
  have hb := CanonicalPolicy.pathBonus_le lay low
  unfold CanonicalPolicy.credit CanonicalPolicy.pathReward CanonicalPolicy.reward
  omega

theorem validate_source_steps {im : Image} (hc : Code im)
    (s : MachineState) (hp : s.pc=pcOf 46929) (hints : BitVec 16) (digits : List (List Nat)) (lows : List Bool)
    (hH : hints.toNat<8000) (hlen : digits.length=4)
    (hfloor : ∀lay:SigGolfCandidate.T3.Layer, SharedForest.hintFloor hints lay≤
      CanonicalPolicy.credit lay (lows.getD lay.val true) (digits.getD lay.val []))
    (hm : s.getMem (0x66000#64)=BitVec.ofNat 64 hints.toNat)
    (hcredits : ∀lay:SigGolfCandidate.T3.Layer,s.getMem (BitVec.ofNat 64 (417856+8*lay.val))=
      BitVec.ofNat 64 (CanonicalPolicy.credit lay (lows.getD lay.val true) (digits.getD lay.val [])))
    (ht1 : ∀r,r<56→CanonicalPolicy.threshold 1 r<22)
    (ht2 : ∀r,r<41→CanonicalPolicy.threshold 2 r<22)
    (hb1 : ∀r,r<56→s.getByte (BitVec.ofNat 64 (16749456+r))=BitVec.ofNat 8 (CanonicalPolicy.threshold 1 r))
    (hb2 : ∀r,r<41→s.getByte (BitVec.ofNat 64 (16749520+r))=BitVec.ofNat 8 (CanonicalPolicy.threshold 2 r)) :
    ∃t n c,n≤47 ∧ c≤59 ∧ Steps im s n c t ∧
      t.pc=(if SharedForest.policyHintsValid hints digits lows then pcOf 42795 else pcOf 354) ∧
      RegsExcept s t [.x6,.x7,.x20,.x21,.x28,.x29] ∧ Frame s t (fun _=>False) := by
  obtain ⟨t,n,c,hn,hc',st,pt,rt,ft⟩:=validate_steps hc s hp hints.toNat
    (CanonicalPolicy.credit 0 (lows.getD 0 true) (digits.getD 0 []))
    (CanonicalPolicy.credit 1 (lows.getD 1 true) (digits.getD 1 []))
    (CanonicalPolicy.credit 2 (lows.getD 2 true) (digits.getD 2 [])) hH (credit_lt _ _ _) (credit_lt _ _ _)
    (credit_lt _ _ _) hm
    (hcredits 0) (hcredits 1) (hcredits 2)
    (CanonicalPolicy.threshold 1) (CanonicalPolicy.threshold 2) ht1 ht2 hb1 hb2
  refine ⟨t,n,c,hn,hc',st,?_,rt,ft⟩
  have hh:=SharedValidate.policyCondition_iff hints digits lows hH hlen (by simpa [SharedForest.hintFloor,CanonicalPolicy.topFloor] using hfloor 0)
    (hfloor 1) (hfloor 2)
  change (Condition hints.toNat (CanonicalPolicy.credit 0 (lows.getD 0 true) (digits.getD 0 []))
    (CanonicalPolicy.credit 1 (lows.getD 1 true) (digits.getD 1 []))
    (CanonicalPolicy.credit 2 (lows.getD 2 true) (digits.getD 2 []))
    (CanonicalPolicy.threshold 1) (CanonicalPolicy.threshold 2) ↔ SharedForest.policyHintsValid hints digits lows=true) at hh
  simpa only [hh] using pt
end ClaudeWCT.W9.Machine.Expand.SharedValidateV6
end
