import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Sign_FtsRuns
import SigGolfCandidate.W9Drv_FtsCore
import SigGolfCandidate.W9Machine_WctChainCertified
import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Expand_CompactCode
import SigGolfCandidate.T3M_Expand_Layers
import SigGolfCandidate.T3M_Search_BCCounterSearch
import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Expand_Canon
import SigGolfCandidate.W9Machine_WctNestView
import SigGolfCandidate.W9Drv_ChildPrefix
import SigGolfCandidate.W9Machine_WctN600Assembly
import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Expand_Base
import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Expand_DrvBits
import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Merkle_ChildDefs
import SigGolfCandidate.W9Machine_WctImageIdentity

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

#print axioms core_tbsim
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
#print axioms checked0
theorem checked1 : rOK (symRun {} (words 1) (pcOf (start 1)) (length 1)) (result 1)=true := by decide +kernel
#print axioms checked1
theorem checked2 : rOK (symRun {} (words 2) (pcOf (start 2)) (length 2)) (result 2)=true := by decide +kernel
#print axioms checked2
theorem checked3 : rOK (symRun {} (words 3) (pcOf (start 3)) (length 3)) (result 3)=true := by decide +kernel
#print axioms checked3
theorem checked4 : rOK (symRun {} (words 4) (pcOf (start 4)) (length 4)) (result 4)=true := by decide +kernel
#print axioms checked4
theorem checked5 : rOK (symRun {} (words 5) (pcOf (start 5)) (length 5)) (result 5)=true := by decide +kernel
#print axioms checked5
theorem checked6 : rOK (symRun {} (words 6) (pcOf (start 6)) (length 6)) (result 6)=true := by decide +kernel
#print axioms checked6
theorem checked7 : rOK (symRun {} (words 7) (pcOf (start 7)) (length 7)) (result 7)=true := by decide +kernel
#print axioms checked7
theorem checked8 : rOK (symRun {} (words 8) (pcOf (start 8)) (length 8)) (result 8)=true := by decide +kernel
#print axioms checked8
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

#print axioms checked
#print axioms result_pc
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
#print axioms steps

theorem result_child_raw (k : Fin 9) (u : MachineState) : ((result k.val).toState u).getReg .x23=
      (rawRead k.val u <<< (if k.val<8 ∧ k.val%2=0 then 7 else 8))+
        BitVec.ofNat 64 (4096+4*(if k.val<8 ∧ k.val%2=0 then 231616 else if k.val=8 then 235776 else 246464)) := by
  fin_cases k <;> rfl

#print axioms result_child_raw

theorem result_child (k : Fin 9) (u : MachineState) (raw : Fin 128)
    (hraw : rawRead k.val u=BitVec.ofNat 64 raw.val) :
    ((result k.val).toState u).getReg .x23=pcOf ((SharedLayout.layout k).childWord raw) := by
  change _=pcOf (SharedLayout.childWord k.val raw.val)
  rw [result_child_raw,hraw]
  unfold SharedLayout.childWord
  split_ifs <;> rw [BitVec.shiftLeft_eq_mul_twoPow]
  all_goals change BitVec.ofNat 64 raw.val * BitVec.ofNat 64 _ + BitVec.ofNat 64 _ = BitVec.ofNat 64 _
  all_goals rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add]; congr 1 <;> norm_num [Nat.shiftLeft_eq] <;> omega

#print axioms result_child
theorem result_node_value (k : Fin 9) (u : MachineState) (index : Nat)
  (hi : index<2^31) (hindex : u.getMem 0x66010=BitVec.ofNat 64 index) : ((result k.val).toState u).getReg .x15=BitVec.ofNat 64 (V3.nodeLow k.val index) := by
  rw [result_node,hindex]
  apply BitVec.eq_of_toNat_eq
  simp only [V3.nodeLow,ClaudeWCT.WCT9.ftsLeafLow,Nat.mod_eq_of_lt hi,
    Nat.mod_eq_of_lt (show k.val<16 by have := k.isLt; omega)]
  simp [BitVec.toNat_add,BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,Nat.shiftLeft_eq]
  omega

#print axioms result_node_value
theorem result_hashMode (k : Fin 9) (u : MachineState) : ((result k.val).toState u).getReg .x5=0 := by fin_cases k <;> rfl
theorem result_stepOne (k : Fin 9) (u : MachineState) : ((result k.val).toState u).getReg .x7=1 := by fin_cases k <;> rfl
theorem result_stepTwo (k : Fin 9) (u : MachineState) : ((result k.val).toState u).getReg .x13=2 := by fin_cases k <;> rfl
theorem result_hashLen (k : Fin 9) (u : MachineState) : ((result k.val).toState u).getReg .x11=64 := by fin_cases k <;> rfl
theorem result_heaps (k : Fin 9) (u : MachineState) (h : Nat) (h2 : 2≤h) (h7 : h≤7) :
    ((result k.val).toState u).getReg (Child.heapReg h)=BitVec.ofNat 64 h := by
  interval_cases h <;> fin_cases k <;> rfl
#print axioms result_heaps

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
#print axioms result_pc_value

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

#print axioms result_leaf_value

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
#print axioms chain_pre
#print axioms steps
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

#print axioms witness_view
#print axioms fields_frame
#print axioms core_frame_dispatch
#print axioms next_other
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
#print axioms next
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
#print axioms installed_code
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

#print axioms step_tbsim

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

#print axioms forest_tbsim
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
#print axioms forest_tbsim_of_bank
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

def stage (sig : WCT9.Signature) (hints : BitVec 16) (index n : Nat) (value : WCT9.LayerMsg) :
    SigGolfCandidate.T3.M (Option (BitVec 32 × List Nat × Bool × WCT9.LayerMsg × Digest × List Nat)) := do
  let lay : Layer := Fin.ofNat 4 n
  let some (c,ds,low) ← WCT9.CanonicalPolicy.layerCounterSearchAt lay (hintFloor hints lay)
    (route index lay).2 (route index lay).1 value 0 (WCT9.searchLimit lay) | pure none
  let mv ← BC.recoverMsg sig index lay ds
  pure (some (c,ds,low,mv.1,mv.2.1,mv.2.2))
def stageCost (lay : Layer) : Nat := lK lay+csCost lay+10+rlCost lay

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
  [SharedRecover.BCBlocks.Code im] [SharedRecover.PackedBlocks.Code im] {sk : BitVec 256}
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
  obtain ⟨t1, s1, p1, x1, x8, x15, x26, x27, x17, x18, x9, r1, f1⟩ :=
    SharedRecover.lentry_spec (im := im) lay s (by rw [hI.pc]; rfl) index hI.hidx hI.idx
  have g1 : ∀ A, A < 2 ^ 64 → t1.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) :=
    fun A hA => f1.get hA (fun h => h)
  obtain ⟨x, hx, hx32⟩ := hI.c32
  have htable1 : Search.TableOK t1 := hI.table.frame f1 (by intro i hi h; exact h)
  have hcs : CsPre 354 ⟨lay, tree, leaf, value, lR1 lay, hintFloor hints lay, hints⟩ t1 :=
    ⟨p1, x1, by rw [r1.get (by decide)]; exact hI.x5, x8, x9, x18, (by convert x17 using 2; clear_value lay; fin_cases lay <;> rfl), x26, x27, htree, hleaf32,
      route_routed index lay hI.hidx, Or.inr x15, by rw [g1 _ (by decide)]; exact hI.enc.1, by rw [g1 _ (by decide)]; exact hI.enc.2,
      ⟨x, hx, by rw [g1 _ (by decide)]; exact hx32⟩, by rw [g1 _ (by decide)]; exact hI.z.e40,
      by rw [g1 _ (by decide)]; exact (hI.right (by omega)).1, by rw [g1 _ (by decide)]; exact (hI.right (by omega)).2, htable1,
      hI.cf.frame f1 (by intro i hi hi' h; exact h),
      hI.reward.frame f1 (by intro i hi hi' h; exact h), hI.zt.frame f1 (by intro r hr h; exact h),
      hintFloor_lt hints lay, (fun he => by change lay=0 at he; change hintFloor hints lay=19;rw [he];rfl), hI.hintsLt, rfl, by rw [g1 _ (by decide)]; exact hI.hintsMem⟩
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
    have g3 : ∀ r, r ∉ [Reg.x1, .x6, .x7, .x8, .x9, .x15, .x17, .x18, .x26, .x27, .x28] → r ∉ csRegs →
        r ∉ [Reg.x1, .x16, .x23, .x24, .x28] → t3.getReg r = s.getReg r :=
      fun r h1 h2 h3 => by rw [r3.get h3, r2.get h2, r1.get h1]
    have g3' : ∀ r, r ∉ csRegs → r ∉ [Reg.x1, .x16, .x23, .x24, .x28] → t3.getReg r = t1.getReg r :=
      fun r h2 h3 => by rw [r3.get h3, r2.get h2]
    have m3 : ∀ A, A < 2 ^ 64 → ¬ CsW lay A → A ≠ lD lay → t3.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) :=
      fun A hA h1 h2 => by rw [f3.get hA h2, f2.get hA h1, g1 A hA]
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
    have hfar4 : ∀ A, A < 2 ^ 64 → ¬ CsW lay A → A ≠ lD lay → (A < 0x2c48 ∨ 0x7000 ≤ A) → ¬ BC.RlScratch A →
        t4.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
      intro A hA h1 h2 h3 h4
      have hw : ¬ (BC.RlScratch A ∨ RlWit lay (route index lay).1 (lWC lay) (lWM lay) A) := by
        rintro (h | h)
        · exact h4 h
        · have := rlWit_range h; have := ltable_lo lay; omega
      rw [f4.get hA hw, m3 A hA h1 h2]
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
        · exact h
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
        · exact h
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
        · exact h
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
        · exact h.elim
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
    refine TBSim.pure ⟨⟨hI4base,hI.hintsLt,hint4,zt4⟩,cv4,pv4,frame4,?_,credit4,hlen,⟨v,hdec⟩,blk4,?_,creditFloor2,flag4,non4⟩
    · exact (((r1.trans r2).trans r3).trans r4).mono (by decide)
    · have hw : ¬ (BC.RlScratch (lD lay) ∨ RlWit lay (route index lay).1 (lWC lay) (lWM lay) (lD lay)) := by
        rintro (h|h)
        · unfold BC.RlScratch Expand.RlScratch at h; simp only [CHAIN,NODE,NOUT,LEAFPK,ENC] at h;omega
        · exact counter_ne_wit lay lay _ h
      rw [f4.get (by omega) hw,hD,f2.get (by omega) (ncs _ (by omega)),g1 _ (by omega)]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp

#print axioms stage_good
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
#print axioms stage_half
#print axioms old_wit_preserved
#print axioms old_credit_preserved
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
  [SharedRecover.BCBlocks.Code im] [SharedRecover.PackedBlocks.Code im] {sk : BitVec 256}
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
#print axioms run_good
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
#print axioms run_eq_recover
#print axioms cost_four
end SigGolfCandidate.T3M.Expand.SharedLayers

namespace ClaudeWCT.W9.Machine.Expand.SharedValidate
open SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.Research
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- img-v6 machine policy check: pool 74, hints `484·f1 + 22·f2 + f3`; L1 residual < 56, L2 < 41, L3 < 22. -/
def policyCondition (hints : BitVec 16) (digits : List (List Nat)) (lows : List Bool) : Prop :=
  let r1:=74-CanonicalPolicy.credit 0 (lows.getD 0 true) (digits.getD 0 [])
  let r2:=r1-CanonicalPolicy.credit 1 (lows.getD 1 true) (digits.getD 1 [])
  let r3:=r2-CanonicalPolicy.credit 2 (lows.getD 2 true) (digits.getD 2 [])
  r1<56 ∧ r2<41 ∧ r3<22 ∧
    hints.toNat/484=CanonicalPolicy.threshold 1 r1 ∧
    hints.toNat/22%22=CanonicalPolicy.threshold 2 r2 ∧ hints.toNat%22=r3

theorem policyCondition_iff (hints : BitVec 16) (digits : List (List Nat)) (lows : List Bool)
    (hh : hints.toNat<8000) (hlen : digits.length=4)
    (hc0 : 19≤CanonicalPolicy.credit 0 (lows.getD 0 true) (digits.getD 0 []))
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
    have hr1 : 74-CanonicalPolicy.credit 0 (lows.getD 0 true) (digits.getD 0 [])<56 := by omega
    have ht1 := (CanonicalPolicy.lower_one_progress ⟨_,hr1⟩).2
    simp only [Fin.val_mk] at ht1
    have hr2 : 74-CanonicalPolicy.credit 0 (lows.getD 0 true) (digits.getD 0 [])-
        CanonicalPolicy.credit 1 (lows.getD 1 true) (digits.getD 1 [])<41 := by
      rw [←he1] at ht1
      omega
    have ht2 := (CanonicalPolicy.lower_two_progress ⟨_,hr2⟩).2
    simp only [Fin.val_mk] at ht2
    have hr3 : 74-CanonicalPolicy.credit 0 (lows.getD 0 true) (digits.getD 0 [])-
        CanonicalPolicy.credit 1 (lows.getD 1 true) (digits.getD 1 [])-
        CanonicalPolicy.credit 2 (lows.getD 2 true) (digits.getD 2 [])<22 := by
      rw [←he2] at ht2
      omega
    refine ⟨hr1,hr2,hr3,by omega,he2,?_⟩
    rw [CanonicalPolicy.lower_three_progress _ hr3] at he3
    exact he3
#print axioms policyCondition_iff
end ClaudeWCT.W9.Machine.Expand.SharedValidate

namespace SigGolfCandidate.T3M.Expand.SharedLayers
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest)
open SigGolfCandidate.T3M.Search.CanonicalExpand (CsArgs CsPre CsPost csCost)
open SigGolfCandidate.Research
open ClaudeWCT
variable {im : Image} [SharedRecover.EntryCode im] [SharedRecover.Code im]
  [SharedRecover.BCBlocks.Code im] [SharedRecover.PackedBlocks.Code im] {sk : BitVec 256}
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
#print axioms recover_good
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
#print axioms data1
#print axioms data2
#print axioms Tables.first
#print axioms Tables.second
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
/-- Pairing stage 1: the pair copy block 48000 .. 48017 in the installed image (beyond the reference chunks). -/
theorem installed_pairCopy : PairCopy.Code Images.expandImage := by
  constructor <;> apply SigGolfCandidate.T3M.codeAt_expand_last <;> decide +kernel
/-- Pairing stage 1: the layout block 48100 .. 49225 in the installed image. -/
theorem installed_layout_chunks : ∀ k < 183, 44032 ≤ Layout.pcK k ∧
    0x1000 + 4 * Layout.pcK k + 4 * (Layout.lbCodes.getD k []).length < 2 ^ 64 ∧
    (Images.expandCode_172.drop (Layout.pcK k - 44032)).take (Layout.lbCodes.getD k []).length =
      Layout.lbCodes.getD k [] := by decide +kernel
theorem installed_layout_heads : ∀ g < 4, 44032 ≤ Layout.lbHeadPc.getD g 0 ∧
    0x1000 + 4 * Layout.lbHeadPc.getD g 0 + 4 * (Layout.lbHeadCodes.getD g []).length < 2 ^ 64 ∧
    (Images.expandCode_172.drop (Layout.lbHeadPc.getD g 0 - 44032)).take (Layout.lbHeadCodes.getD g []).length =
      Layout.lbHeadCodes.getD g [] := by decide +kernel
theorem installed_layout : Layout.Code Images.expandImage := by
  refine ⟨?_, ?_, ?_, fun g hg => ?_, fun k hk => ?_, ?_⟩
  · apply SigGolfCandidate.T3M.codeAt_expand_last <;> decide +kernel
  · apply SigGolfCandidate.T3M.codeAt_expand_last <;> decide +kernel
  · apply SigGolfCandidate.T3M.codeAt_expand_last <;> decide +kernel
  · obtain ⟨h1, h2, h3⟩ := installed_layout_heads g hg
    exact SigGolfCandidate.T3M.codeAt_expand_last h1 h2 h3
  · obtain ⟨h1, h2, h3⟩ := installed_layout_chunks k hk
    exact SigGolfCandidate.T3M.codeAt_expand_last h1 h2 h3
  · apply SigGolfCandidate.T3M.codeAt_expand_last <;> decide +kernel
theorem installed_compact : CompactCodeAt Images.expandImage :=
  compactCode_of_chunks installed_compact_chunks installed_pairCopy installed_layout
#print axioms installed_compact
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
#print axioms initial_of_original
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
#print axioms raw_output
#print axioms rank_output
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
#print axioms fields_of_output
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
#print axioms installed_forest_good
end ClaudeWCT.W9.Machine.Expand.SharedForestRun
