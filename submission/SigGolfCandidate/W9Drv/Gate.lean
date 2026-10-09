import SigGolfCandidate.Research.V7Composed198Gate
import SigGolfCandidate.W9Machine.WctFetch
import SigGolfCandidate.W9Drv.CoordDefs

section
namespace W9Drv
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
open W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def gJumpWords : List (BitVec 32) := [41943151]
def gCheckWords : List (BitVec 32) := [35150611,0x1803883,0x328d193,0x46b1b393,0xa039263]
def gSetupWords : List (BitVec 32) :=
  [29038483,0x60178793,66359,2098835,3148179,4196883,5245587,6294803,7343891,486618115,385957507,394345475,50398355,0xffd90113]
def gRejectWords : List (BitVec 32) := [1049235,1049875,115]
def gateE : E := .bin .sltu
  (.bin .srl (.ld (.c (BitVec.ofNat 64 24)))
    (.c (BitVec.ofNat 64 50))) (.c (BitVec.ofNat 64 1131))
def gJump : Result := ⟨SymState.init, .c (pcOf 32792), .jump, 1, 1⟩
def gCheck : Result :=
  ⟨⟨(((RegFile.init.set .x3
    (.bin .srl (.ld (.c (BitVec.ofNat 64 24))) (.c 50))).set .x7 gateE).set
    .x17 (.ld (.c (BitVec.ofNat 64 24)))).set
    .x22 (.bin .srl (.reg .x16) (.c (BitVec.ofNat 64 33))), [], []⟩,
    .ite .ne gateE (.c 0) (.c (pcOf 32822)) (.c (pcOf 32782)), .branch, 5, 5⟩
def gSetup : Result :=
  ⟨⟨((((((((((((RegFile.init.set .x2 (.bin .add (.reg .x18) (.c (BitVec.ofNat 64 (2 ^ 64 - 3))))).set .x6 (.c 65536)).set
      .x8 (.ld (addC (.reg .x2) 464))).set .x9 (addC (.reg .x2) 48)).set .x13 (.c 2)).set
      .x15 (.bin .add (.bin .sll (.reg .x22) (.c 27)) (.c 1537))).set .x19 (.c 3)).set .x20 (.c 4)).set
      .x21 (.c 5)).set .x24 (.ld (addC (.reg .x2) 376))).set .x26 (.c 6)).set
      .x29 (.ld (addC (.reg .x2) 368))).set .x30 (.c 7), [],
    [.valid ⟨some (.reg .x2), 376⟩ 8, .valid ⟨some (.reg .x2), 368⟩ 8, .valid ⟨some (.reg .x2), 464⟩ 8]⟩,
    .c (pcOf 32836), .fuel, 14, 14⟩
def gReject : Result :=
  ⟨⟨(RegFile.init.set .x5 (.c 1)).set .x10 (.c 1), [], []⟩, .c (pcOf 32794), .ecall, 2, 2⟩
theorem gJump_checked : rOK (symRun {} gJumpWords (pcOf 32782) 1) gJump = true := by decide +kernel
theorem gJump_linked : sliceChecked 32782 gJumpWords = true := by decide +kernel
theorem gCheck_checked : rOK (symRun {} gCheckWords (pcOf 32777) 5) gCheck = true := by decide +kernel
theorem gCheck_linked : sliceChecked 32777 gCheckWords = true := by decide +kernel
theorem gSetup_checked : rOK (symRun {} gSetupWords (pcOf 32822) 14) gSetup = true := by decide +kernel
theorem gSetup_linked : sliceChecked 32822 gSetupWords = true := by decide +kernel
theorem gReject_checked : rOK (symRun {} gRejectWords (pcOf 32792) 3) gReject = true := by decide +kernel
theorem gReject_linked : sliceChecked 32792 gRejectWords = true := by decide +kernel
end W9Drv
end
section
namespace W9Drv
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput M)
open W9Machine
theorem block_steps {words : List (BitVec 32)} {p n : Nat} {r : Result}
    (hc : rOK (symRun {} words (pcOf p) n) r = true) (hl : sliceChecked p words = true)
    (hob : r.st.obl = []) (s : MachineState) (hpc : s.pc = pcOf p) :
    Steps Frozen.image s r.steps r.cycles (r.toState s) :=
  symRun_sound (rOK_eq hc) (slice_at p words hl) s hpc (by simp [Result.obligs, hob, Oblig.all])
theorem block_ecall {words : List (BitVec 32)} {p n : Nat} {r : Result}
    (hc : rOK (symRun {} words (pcOf p) n) r = true) (hl : sliceChecked p words = true)
    (hob : r.st.obl = []) (s : MachineState) (hstop : r.stop = .ecall) :
    fetch Frozen.image (r.toState s) = some (.base .ECALL) :=
  symRun_ecall (rOK_eq hc) (slice_at p words hl) s (by simp [Result.obligs, hob, Oblig.all]) hstop
theorem toState_mem_nil (r : Result) (s : MachineState) (h : r.st.mem = []) :
    (r.toState s).mem = s.mem := by
  show memEval s r.st.mem = s.mem
  rw [h]; rfl
theorem init_getReg (s : MachineState) (x : Reg) : (RegFile.init.get x).eval s = s.getReg x := by
  cases x <;> rfl
theorem glob_congr {w : ClaudeWCT.W9.T3M.WBytes} {pk : Digest} {s t : MachineState} (h : Glob baseK w pk s)
    (hm : t.mem = s.mem) (h5 : t.getReg .x5 = 0) (h18 : t.getReg .x18 = 0xFFF) :
    Glob baseK w pk t := by
  obtain ⟨-, h0, h2, h3, h4, h5'⟩ := h
  have e : ∀ A, t.getMem A = s.getMem A := fun A => congrFun hm A
  refine ⟨?_, fun j hj4 hj => (e _).trans (h0 j hj4 hj), ⟨(e _).trans h2.1, (e _).trans h2.2⟩,
    fun a ha => (e _).trans (h3 a ha), ?_, h5'.congr (fun A _ _ => e _)⟩
  · intro p hp
    simp only [baseK, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact h5
    · exact h18
  · show (t.getMem _).toNat / 2 ^ 32 = 0
    rw [e]; exact h4
theorem idx_val (x : Word) :
    x >>> 33 = BitVec.ofNat 64 (x.toNat / 2 ^ 33) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  have := x.isLt
  omega
theorem heap_val (i h : Nat) (hi : i < 2 ^ 31) :
    BitVec.ofNat 64 (2 ^ 32 * h) ||| BitVec.ofNat 64 i = BitVec.ofNat 64 (i + 2 ^ 32 * h) := by
  rw [ofNat_or_disjoint i (2 ^ 32 * h) 32 (by omega) (by simp), Nat.add_comm]
theorem gateE_eval (s : MachineState) (a : BitVec 256)
    (hw : s.getMem (BitVec.ofNat 64 24) = a.extractLsb' 192 64) :
    gateE.eval s = if decide (a.toNat / 2 ^ 242 % 2 ^ 14 < 1131) then 1 else 0 := by
  change (if BitVec.ult (s.getMem (BitVec.ofNat 64 24) >>> 50)
    (BitVec.ofNat 64 1131) then (1 : BitVec 64) else 0) = _
  rw [hw, SigGolfCandidate.Research.V7Composed198Gate.gate_ult_shift50]

theorem word0_toNat (a : HashOutput) : (a.extractLsb' 0 64).toNat = a.toNat % 2 ^ 64 := by
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
theorem index_eq (a : HashOutput) : (a.extractLsb' 0 64).toNat / 2 ^ 33 = idxOf a := by
  rw [word0_toNat]; unfold idxOf ClaudeWCT.WCT9.digestIndex; omega
theorem setup_load (s : MachineState) (hsp : s.getReg .x2 = BitVec.ofNat 64 dataBase7) (k : Nat) :
    s.getMem ((addC (.reg .x2) (BitVec.ofNat 64 k)).eval s) = s.getMem (BitVec.ofNat 64 (dataBase7 + k)) := by
  rw [addC_eval]
  change s.getMem (s.getReg .x2 + BitVec.ofNat 64 k) = _
  rw [hsp, ofNat_add_ofNat]
theorem gate_good (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput)
    (u : MachineState) (N C A : Nat) (Q : Prop)
    (K : Bool → OracleComp HashSpec Obs)
    (hu : GatePre pk w a u) (hnone : K false = pure (false, 0))
    (hnext : ∀ t, CoordPre pk w a 0 [] t →
      GoodQFor Frozen.image t N C Q A (K true)) :
    GoodQFor Frozen.image u (N + 19) (C + 19) Q (A + 19) (K (ClaudeWCT.W9.T3M.gateOk a)) := by
  let s1 := u
  have m1 : s1.mem = u.mem := rfl
  have r1 : ∀ x, s1.getReg x = u.getReg x := fun _ => rfl
  have pc1 : s1.pc = pcOf 32777 := hu.pc
  have st2 := block_steps gCheck_checked gCheck_linked rfl s1 pc1
  set s2 := gCheck.toState s1 with hs2
  have m2 : s2.mem = u.mem := (toState_mem_nil _ _ rfl).trans m1
  have hw3 : s1.getMem (BitVec.ofNat 64 24) = a.extractLsb' 192 64 := by
    have := hu.digest 3 (by decide +kernel)
    simpa [MachineState.getMem, m1] using this
  have pc2 : s2.pc = if gateE.eval s1 != 0 then pcOf 32822 else pcOf 32782 := by
    show (E.ite .ne gateE (.c 0) (.c (pcOf 32822)) (.c (pcOf 32782))).eval s1 = _
    rfl
  have hg : gateE.eval s1 = if ClaudeWCT.W9.T3M.gateOk a then 1 else 0 :=
    gateE_eval s1 a hw3
  have st2' : Steps Frozen.image s1 5 5 s2 := st2
  by_cases hok : ClaudeWCT.W9.T3M.gateOk a = true
  ·
    rw [hok]
    have hz : gateE.eval s1 = 1 := by simpa [hok] using hg
    have pc2' : s2.pc = pcOf 32822 := by rw [pc2, hz]; rfl
    have hsp2 : s2.getReg .x2 = BitVec.ofNat 64 dataBase7 := by
      rw [hs2, Result.toState_getReg]
      show s1.getReg .x2 = _
      rw [r1]; exact hu.sp
    have hob : gSetup.obligs s2 := by
      apply (Oblig.all_iff s2 _).mpr
      intro o ho
      simp only [gSetup, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl
      all_goals
        change accessValid (s2.getReg .x2 + _) 8 = true
        rw [hsp2]
        decide +kernel
    have st3 := symRun_sound (rOK_eq gSetup_checked) (slice_at _ _ gSetup_linked) s2 pc2' hob
    set s3 := gSetup.toState s2 with hs3
    have st3' : Steps Frozen.image s2 14 14 s3 := st3
    have m2' : ∀ A, s2.getMem A = u.getMem A := fun A => congrFun m2 A
    have hchild : s3.getReg .x29 = BitVec.ofNat 64 0xce800 := by
      rw [hs3, Result.toState_getReg]
      change s2.getMem ((addC (.reg .x2) (BitVec.ofNat 64 368)).eval s2) = _
      rw [setup_load s2 hsp2, m2']
      exact hu.setupMask.child
    have hjt : s3.getReg .x24 = BitVec.ofNat 64 0xd6800 := by
      rw [hs3, Result.toState_getReg]
      change s2.getMem ((addC (.reg .x2) (BitVec.ofNat 64 376)).eval s2) = _
      rw [setup_load s2 hsp2, m2']
      exact hu.setupMask.jt
    have hbase : s3.getReg .x8 = BitVec.ofNat 64 8640 := by
      rw [hs3, Result.toState_getReg]
      change s2.getMem ((addC (.reg .x2) (BitVec.ofNat 64 464)).eval s2) = _
      rw [setup_load s2 hsp2, m2']
      exact hu.setupMask.coord
    have m3 : s3.mem = u.mem := (toState_mem_nil _ _ rfl).trans m2
    have e3 : ∀ A, s3.getMem A = u.getMem A := fun A => congrFun m3 A
    have r22 : s2.getReg .x22 = a.extractLsb' 0 64 >>> 33 := by
      rw [hs2, Result.toState_getReg]
      show s1.getReg .x16 >>> 33 = _
      rw [r1, hu.cached0]
    have hidx : s2.getReg .x22 = BitVec.ofNat 64 (idxOf a) := by
      rw [r22, idx_val, index_eq]
    have hia : idxOf a < 2 ^ 31 := ClaudeWCT.WCT9.digestIndex_lt a
    have h5 : s3.getReg .x5 = 0 := by
      rw [hs3, Result.toState_getReg]
      show s2.getReg .x5 = 0
      rw [hs2, Result.toState_getReg]
      show s1.getReg .x5 = 0
      rw [r1]; exact hu.glob.1 (.x5, 0) (by simp [baseK])
    have h18 : s3.getReg .x18 = 0xFFF := by
      rw [hs3, Result.toState_getReg]
      show s2.getReg .x18 = 0xFFF
      rw [hs2, Result.toState_getReg]
      show s1.getReg .x18 = 0xFFF
      rw [r1]; exact hu.glob.1 (.x18, 0xFFF) (by simp [baseK])
    have hpre : CoordPre pk w a 0 [] s3 := by
      refine {
        le := (by decide +kernel), length := rfl, pc := rfl,
        glob := glob_congr hu.glob m3 h5 h18,
        digest := ?_, bank := ?_, forest := ?_, index := ?_, heaps := ?_,
        stepOne := ?_, stepTwo := rfl, hashLen := ?_, coordStep := rfl,
        nodeReg := ?_, cached3 := ?_, cached := ?_,
        mask := ?_, jt := hjt, childBlock := hchild, baseReg := hbase, pairPtr := ?_,
        pairs := fun i hi => absurd hi (Nat.not_lt_zero _), coords := ?_, layer := ?_ }
      · intro k hk; rw [e3]; exact hu.digest k hk
      · exact ⟨fun k hk => (e3 _).trans (hu.bank.top k hk), (e3 _).trans hu.bank.top8⟩
      · exact ⟨(e3 _).trans hu.forest.zero0, (e3 _).trans hu.forest.zero1, (e3 _).trans hu.forest.header⟩
      · rw [hs3, Result.toState_getReg]; show s2.getReg .x22 = _; exact hidx
      · intro h h2 h7
        interval_cases h <;> rfl
      · rw [hs3, Result.toState_getReg]
        show s2.getReg .x7 = 1
        rw [hs2, Result.toState_getReg]
        exact hz
      · rw [hs3, Result.toState_getReg]
        show s2.getReg .x11 = 64
        rw [hs2, Result.toState_getReg]
        show s1.getReg .x11 = 64
        rw [r1]; exact hu.len64
      · change (s2.getReg .x22 <<< 27) + 1537 = _
        rw [hidx]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
        have h1 : idxOf a * 2 ^ 27 < 2 ^ 58 := by omega
        rw [Nat.mod_eq_of_lt (by omega : idxOf a < 2^64), Nat.mod_eq_of_lt (by omega : idxOf a * 2 ^ 27 < 2 ^ 64),
          show BitVec.toNat (1537 : Word) = 1537 from rfl, show (0 : Nat) - 1 = 0 from rfl, Nat.mul_zero, Nat.add_zero]
      · rw [hs3, Result.toState_getReg]
        show s2.getReg .x17 = _
        rw [hs2, Result.toState_getReg]
        exact hw3
      · rw [hs3, Result.toState_getReg]
        show s2.getReg .x16 = _
        rw [hs2, Result.toState_getReg]
        show s1.getReg .x16 = _
        rw [r1]; exact hu.cached0
      · rw [hs3, Result.toState_getReg]
        change s2.getReg .x18 + BitVec.ofNat 64 (2 ^ 64 - 3) = _
        have h18s2 : s2.getReg .x18 = 0xFFF := by
          rw [hs2, Result.toState_getReg]
          show s1.getReg .x18 = 0xFFF
          rw [r1]; exact hu.glob.1 (.x18, 0xFFF) (by simp [baseK])
        rw [h18s2]
        decide
      · rw [hs3, Result.toState_getReg]
        change s2.getReg .x2 + BitVec.ofNat 64 48 = _
        rw [hsp2, ofNat_add_ofNat]; rfl
      · intro k _ off hoff h8
        unfold W9Machine.OrigW
        rw [e3]
        have hw := hu.wit ((64 + 816 * (8 - k.val) + off) / 8) (by unfold WX; have := k.isLt; omega)
          (by have := k.isLt; omega)
        rw [show WIT + 8 * ((64 + 816 * (8 - k.val) + off) / 8) = coordinateBase k + off by
          unfold WIT coordinateBase; omega] at hw
        have e : 8 * (coordinateBase k + off - 0x800) = 64 * ((64 + 816 * (8 - k.val) + off) / 8) := by
          unfold coordinateBase; omega
        rw [hw, wword, e]
      · exact (hu.wit.mono (fun o ho => by omega)).frame (fun j _ _ => e3 _)
    have := (((hnext s3 hpre).steps st3').steps st2')
    exact this.mono (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
  ·
    have hok' : ClaudeWCT.W9.T3M.gateOk a = false := by simpa using hok
    rw [hok', hnone]
    have hz : gateE.eval s1 = 0 := by simpa [hok'] using hg
    have pc2' : s2.pc = pcOf 32782 := by
      rw [pc2, hz]; rfl
    have sj := block_steps gJump_checked gJump_linked rfl s2 pc2'
    let sr := gJump.toState s2
    have sj' : Steps Frozen.image s2 1 1 sr := sj
    have st3 := block_steps gReject_checked gReject_linked rfl sr rfl
    have st3' : Steps Frozen.image sr 2 2 (gReject.toState sr) := st3
    have hf := block_ecall gReject_checked gReject_linked rfl sr rfl
    have hr : GoodQFor Frozen.image (gReject.toState sr) 1 1 Q A (pure (false, 0)) :=
      GoodQFor.reject hf (by rw [Result.toState_getReg]; rfl) (by rw [Result.toState_getReg]; rfl)
    have := ((hr.steps st3').steps sj').steps st2'
    exact this.mono (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
end W9Drv
end
