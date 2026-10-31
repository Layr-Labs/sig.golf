import SigGolf
import VCVio.EvalDist.Expectation
import SigGolfCandidate.Merge001
import SigGolfCandidate.Merge005
import SigGolfCandidate.Merge017
import SigGolfCandidate.Merge033
import SigGolfCandidate.Merge043
import SigGolfCandidate.Merge051
import SigGolfCandidate.Merge053
import SigGolfCandidate.Merge054
import SigGolfCandidate.Merge057
import SigGolfCandidate.Merge058
import SigGolfCandidate.Merge074
import SigGolfCandidate.Merge075
import SigGolfCandidate.Merge093
import SigGolfCandidate.Merge094
import SigGolfCandidate.Merge097

-- ==== merged from ClaudeWCT_W9_T3M_Final_Main ====
section

open OracleComp OracleSpec

namespace ClaudeWCT.W9.T3M.Final.Paired
open OracleComp OracleSpec SigGolfCandidate.Legacy
open SigGolfCandidate.T3M (mrealize)
open SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.T3M (Images)
set_option allowUnsafeReducibility true in
attribute [local reducible] ClaudeWCT.W9.T3M.Paired.submission SigGolfCandidate.Legacy.Output SigGolfCandidate.Legacy.Input
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
variable {I : Images}

theorem submission_terminates (P : Pending I) : (submission I).Terminates := by
  intro hash phase input
  cases phase with
  | keygen =>
    exact ⟨(P.keygen_runWith hash input).2.1, (P.keygen_runWith hash input).2.2.1⟩
  | sign => obtain ⟨sk,cache,m⟩:=input;exact P.sign_terminates hash sk cache m
  | expand => obtain ⟨m,pk,s⟩:=input;exact P.expand_terminates hash m pk s
  | verify => obtain ⟨m,pk,w⟩:=input;exact P.verify_terminates hash m pk w

theorem witnessCycles_eq : witnessCycles (submission I).sizes.witness=86 := by
  change witnessCycles 22012=86
  decide

theorem claimedC_eq : claimedC=verifyCycleBound+witnessCycles (submission I).sizes.witness := by
  rw [witnessCycles_eq];decide

theorem submission_verificationBound (E : EncodingFacts) (F : SourceQueries) (P : Pending I) :
    (submission I).VerificationBound 7006 := by
  intro hash sk m
  dsimp only
  intro h
  obtain ⟨pk,s,w,he,hacc,hcyc⟩:=Credit.honest_success_verify_cf (submission I) hash sk m h
  obtain ⟨sig,output,wt,hx,rfl⟩:=Credit.Paired.expand_witness E F P hash m pk s w he
  obtain ⟨floors,hfloors,hagree⟩:=Credit.Paired.agree_verifyP hash m pk sig output wt hx
  have heq:=Credit.Paired.verify_run_agree E F P hash (okHashBy floors wt.topHigh hash) m pk _ hagree
  rw [hcyc,witnessCycles_eq,heq]
  rw [heq] at hacc
  have hok : HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh (ClaudeWCT.W9.T3M.Paired.witEncN output wt))
      (okHashBy floors wt.topHigh hash) := by
    rw [ClaudeWCT.W9.T3M.Paired.wtopHigh_witEncN]; exact hashOkBy_okHashBy floors wt.topHigh hash
  have hc:=P.verify_accept_cycles floors hfloors (okHashBy floors wt.topHigh hash) m pk _
    hok (Credit.Paired.digestCap_okHashBy floors wt.topHigh hash m pk sig output wt hx) hacc
  unfold verifyCycleBound at hc
  omega
end ClaudeWCT.W9.T3M.Final.Paired

namespace ClaudeWCT.W9.T3M.Final.Paired
open SigGolfCandidate.Legacy
open ClaudeWCT.W9.T3M (Images)
variable {I : Images}

theorem certificate_of (E : EncodingFacts) (F : SourceQueries) (P : Pending I) (S : SourceFacts) :
    Certificate (submission I) 7006 where
  admissible := P.admissible
  termination := submission_terminates P
  completeness := submission_complete E F P S
  compressionBounds := submission_compressionBounds E F P S
  security := submission_secure E F P S.securityP
  verificationBound := submission_verificationBound E F P
end ClaudeWCT.W9.T3M.Final.Paired
end
-- ==== merged from Transfer_Basic ====
section

namespace SigGolfCandidate.Transfer
open OracleComp OracleSpec RiscvZkvm.Rv64
def phaseOf : SigGolf.Program → Legacy.Phase
  | .keygen => .keygen
  | .sign => .sign
  | .expand => .expand
  | .verify => .verify
def programOf : Legacy.Phase → SigGolf.Program
  | .keygen => .keygen
  | .sign => .sign
  | .expand => .expand
  | .verify => .verify
@[simp] theorem phaseOf_programOf (phase : Legacy.Phase) : phaseOf (programOf phase) = phase := by
  cases phase <;> rfl
@[simp] theorem programOf_phaseOf (program : SigGolf.Program) :
    programOf (phaseOf program) = program := by
  cases program <;> rfl
def sizesOf (sizes : SigGolf.Sizes) : Legacy.Sizes := ⟨sizes.signature, sizes.witness, sizes.cache⟩
def layoutOf (layout : SigGolf.Layout) : Legacy.Layout :=
  ⟨layout.message, layout.secretKey, layout.publicKey, layout.cache, layout.signature,
    layout.witness⟩
def imageOf (image : SigGolf.Riscv.Image) : Legacy.Riscv.Image := ⟨image.code, image.data⟩
@[reducible] def legacyOf (submission : SigGolf.Submission) : Legacy.Submission where
  sizes := sizesOf submission.sizes
  layout := layoutOf submission.layout
  image phase := imageOf (submission.image (programOf phase))
def currentOf (submission : Legacy.Submission) : SigGolf.Submission where
  sizes := ⟨submission.sizes.signature, submission.sizes.witness, submission.sizes.cache⟩
  layout := ⟨submission.layout.message, submission.layout.secretKey, submission.layout.publicKey,
    submission.layout.cache, submission.layout.signature, submission.layout.witness⟩
  image program :=
    ⟨(submission.image (phaseOf program)).code, (submission.image (phaseOf program)).data⟩
theorem legacyOf_currentOf (submission : Legacy.Submission) :
    legacyOf (currentOf submission) = submission := by
  obtain ⟨⟨s, w, k⟩, ⟨m, sk, pk, c, sg, wt⟩, image⟩ := submission
  simp only [legacyOf, currentOf, sizesOf, layoutOf, imageOf, phaseOf_programOf]
@[simp] theorem legacyOf_sizes (submission : SigGolf.Submission) :
    (legacyOf submission).sizes = sizesOf submission.sizes := rfl
def inputOf {sizes : SigGolf.Sizes} :
    (program : SigGolf.Program) → SigGolf.Input sizes program →
      Legacy.Input (sizesOf sizes) (phaseOf program)
  | .keygen, input => input
  | .sign, input => input
  | .expand, input => input
  | .verify, input => input
def outputOf {sizes : SigGolf.Sizes} :
    (program : SigGolf.Program) → Legacy.Output (sizesOf sizes) (phaseOf program) →
      SigGolf.Output sizes program
  | .keygen, output => output
  | .sign, output => output
  | .expand, output => output
  | .verify, output => output
def resultOf {sizes : SigGolf.Sizes} (program : SigGolf.Program)
    (result : Legacy.RunResult (Legacy.Output (sizesOf sizes) (phaseOf program))) :
    SigGolf.RunResult (SigGolf.Output sizes program) :=
  ⟨result.value.map (outputOf program), result.cycles, result.hashCompressions⟩
namespace Riscv
def wordOpOf : Legacy.Riscv.WordOp → SigGolf.Riscv.WordOp
  | .add => .add | .sub => .sub | .sll => .sll | .srl => .srl | .sra => .sra
  | .mul => .mul | .div => .div | .divu => .divu | .rem => .rem | .remu => .remu
def instructionOf : Legacy.Riscv.Instruction → SigGolf.Riscv.Instruction
  | .base instruction => .base instruction
  | .word op rd rs1 rs2 => .word (wordOpOf op) rd rs1 rs2
  | .sraiw rd rs1 shift => .sraiw rd rs1 shift
def exitOf : Legacy.Riscv.Exit → SigGolf.Riscv.Exit
  | .success => .success
  | .failure => .failure
  | .unfinished => .unfinished
def executionOf (execution : Legacy.Riscv.Execution) : SigGolf.Riscv.Execution :=
  ⟨exitOf execution.exit, execution.state, execution.cycles, execution.hashCompressions⟩
theorem decodeInstruction_eq (word : BitVec 32) :
    SigGolf.Riscv.decodeInstruction word =
      (Legacy.Riscv.decodeInstruction word).map instructionOf := by
  unfold SigGolf.Riscv.decodeInstruction Legacy.Riscv.decodeInstruction
  simp only
  split_ifs <;> simp only [Option.map_some, Option.map_none, instructionOf, Option.pure_def,
    Option.bind_eq_bind]
  · generalize (BitVec.extractLsb' 25 7 word).toNat = a
    generalize (BitVec.extractLsb' 12 3 word).toNat = b
    split
    any_goals rfl
    split
    any_goals rfl
    all_goals (exfalso; simp at *)
  · cases RiscvZkvm.Interpreter.decode word <;> rfl
theorem fetch_eq (image : SigGolf.Riscv.Image) (state : MachineState) :
    SigGolf.Riscv.fetch image state =
      (Legacy.Riscv.fetch (imageOf image) state).map instructionOf := by
  unfold SigGolf.Riscv.fetch Legacy.Riscv.fetch
  by_cases h : 0x1000 ≤ state.pc.toNat ∧ state.pc.toNat % 4 = 0
  · have h' : (decide (state.pc.toNat < 0x1000) || state.pc.toNat % 4 != 0) = false := by
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Nat.not_lt, bne_eq_false_iff_eq]
      exact h
    rw [if_pos h]
    simp only [h', Bool.false_eq_true, ↓reduceIte, imageOf, Option.bind_eq_bind]
    cases image.code[(state.pc.toNat - 0x1000) / 4]? with
    | none => rfl
    | some word => simpa using decodeInstruction_eq word
  · have h' : (decide (state.pc.toNat < 0x1000) || state.pc.toNat % 4 != 0) = true := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
      omega
    rw [if_neg h]
    simp [h']
theorem memoryArgumentsValid_eq (state : MachineState) (instruction : Instr) :
    SigGolf.Riscv.memoryArgumentsValid state instruction =
      Legacy.Riscv.memoryArgumentsValid state instruction := by
  cases instruction <;> rfl
theorem ordinaryStep_eq (state : MachineState) (instruction : Legacy.Riscv.Instruction) :
    SigGolf.Riscv.ordinaryStep state (instructionOf instruction) =
      Legacy.Riscv.ordinaryStep state instruction := by
  cases instruction with
  | base instruction =>
      cases instruction <;>
        simp only [instructionOf, SigGolf.Riscv.ordinaryStep, Legacy.Riscv.ordinaryStep,
          memoryArgumentsValid_eq]
  | word op rd rs1 rs2 => cases op <;> rfl
  | sraiw rd rs1 shift => rfl
theorem instructionCycles_eq (instruction : Legacy.Riscv.Instruction) :
    SigGolf.Riscv.instructionCycles (instructionOf instruction) =
      Legacy.Riscv.instructionCycles instruction := by
  cases instruction with
  | base instruction => cases instruction <;> rfl
  | word op rd rs1 rs2 => cases op <;> rfl
  | sraiw rd rs1 shift => rfl
theorem hashArgumentsValid_eq (state : MachineState) :
    SigGolf.Riscv.hashArgumentsValid state = Legacy.Riscv.hashArgumentsValid state := by
  unfold SigGolf.Riscv.hashArgumentsValid Legacy.Riscv.hashArgumentsValid
    Legacy.Riscv.accessValid
  simp only [SigGolf.Riscv.rangeValid, Legacy.Riscv.rangeValid, SigGolf.MEMORY_BYTES,
    Legacy.MEMORY_BYTES]
  generalize (state.getReg .x12).toNat = d
  by_cases h : d + 32 ≤ 2 ^ 24
  · have h8 : d + 8 ≤ 2 ^ 24 := by omega
    simp only [h, h8, decide_true, Bool.true_and, Bool.and_true]
    rfl
  · simp only [h, decide_false, Bool.and_false]
theorem foldl_range_eq_sum (f : Nat → Nat) (n : Nat) :
    (List.range n).foldl (fun acc i => acc + f i) 0 = ∑ i ∈ Finset.range n, f i := by
  suffices h : ∀ a, (List.range n).foldl (fun acc i => acc + f i) a =
      a + ∑ i ∈ Finset.range n, f i by simpa using h 0
  induction n with
  | zero => intro a; simp
  | succ n ih =>
      intro a
      rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]
      simp [Nat.add_assoc]
theorem ofNat_toNat_add (address : BitVec 64) (i : Nat) :
    BitVec.ofNat 64 (address.toNat + i) = address + BitVec.ofNat 64 i := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add]
theorem hashInput_eq (state : MachineState) :
    SigGolf.Riscv.hashInput state = Legacy.Riscv.hashInput state := by
  unfold SigGolf.Riscv.hashInput Legacy.Riscv.hashInput SigGolf.Riscv.readBuffer
  simp only [foldl_range_eq_sum, ofNat_toNat_add]
theorem readBuffer_eq (state : MachineState) (address n : Nat) :
    SigGolf.Riscv.readBuffer state address n = Legacy.readBuffer state address n := by
  unfold SigGolf.Riscv.readBuffer Legacy.readBuffer
  rw [foldl_range_eq_sum]
theorem execute_eq (image : SigGolf.Riscv.Image) (steps : Nat) (state : MachineState) :
    SigGolf.Riscv.execute image steps state =
      executionOf <$> Legacy.Riscv.execute steps (imageOf image) state := by
  induction steps generalizing state with
  | zero => simp [SigGolf.Riscv.execute, Legacy.Riscv.execute, executionOf, exitOf]
  | succ steps ih =>
      rw [SigGolf.Riscv.execute, Legacy.Riscv.execute, fetch_eq]
      rcases Legacy.Riscv.fetch (imageOf image) state with _ | instruction
      · simp [executionOf, exitOf]
      · simp only [Option.map_some]
        rcases em (instruction = .base .ECALL) with hE | hE
        · subst hE
          simp only [instructionOf, hashArgumentsValid_eq, hashInput_eq]
          split_ifs
          · rw [hashInput_eq]
            simp only [map_bind, map_pure, ih, bind_map_left]
            rfl
          all_goals simp [executionOf, exitOf]
        · have hE' : instructionOf instruction ≠ .base .ECALL := by
            cases instruction <;> simp_all [instructionOf]
          split
          · rename_i heq; cases heq
          · rename_i heq; exact absurd (Option.some.inj heq) hE'
          · rename_i instruction' _ heq
            obtain rfl := Option.some.inj heq
            rw [ordinaryStep_eq, instructionCycles_eq]
            cases hstep : Legacy.Riscv.ordinaryStep state instruction with
            | none =>
                dsimp only
                split
                · rename_i heq'; cases heq'
                · rename_i heq'; exact absurd (Option.some.inj heq') hE
                · rename_i instruction'' _ heq'
                  obtain rfl := Option.some.inj heq'
                  simp [hstep, executionOf, exitOf]
            | some next =>
                dsimp only
                split
                · rename_i heq'; cases heq'
                · rename_i heq'; exact absurd (Option.some.inj heq') hE
                · rename_i instruction'' _ heq'
                  obtain rfl := Option.some.inj heq'
                  simp only [hstep, ih, Functor.map_map, bind_pure_comp]
                  rfl
end Riscv
open Riscv in
theorem initialState_eq (submission : SigGolf.Submission) (program : SigGolf.Program)
    (input : SigGolf.Input submission.sizes program)
    (hvalid : ((legacyOf submission).image (phaseOf program)).Valid (legacyOf submission).sizes
      (legacyOf submission).layout) :
    Legacy.initialState (legacyOf submission) (phaseOf program) (inputOf program input) =
      some (SigGolf.initialState submission program input) := by
  unfold Legacy.initialState
  rw [if_pos hvalid]
  cases program <;> rfl
theorem readOutput_eq (sizes : SigGolf.Sizes) (layout : SigGolf.Layout)
    (program : SigGolf.Program) (state : MachineState) :
    SigGolf.readOutput sizes layout program state =
      outputOf program (Legacy.readOutput (sizesOf sizes) (layoutOf layout) (phaseOf program) state) := by
  cases program <;>
    simp only [SigGolf.readOutput, Legacy.readOutput, Riscv.readBuffer_eq, outputOf, phaseOf,
      sizesOf, layoutOf] <;> rfl
def ImagesValid (submission : SigGolf.Submission) : Prop :=
  ∀ phase, ((legacyOf submission).image phase).Valid (legacyOf submission).sizes
    (legacyOf submission).layout
def RunAgrees (submission : SigGolf.Submission) : Prop :=
  ∀ (program : SigGolf.Program) (input : SigGolf.Input submission.sizes program),
    submission.run program input =
      resultOf program <$> (legacyOf submission).run (phaseOf program) (inputOf program input)
theorem runAgrees_of_imagesValid (submission : SigGolf.Submission)
    (hvalid : ImagesValid submission) : RunAgrees submission := by
  intro program input
  unfold SigGolf.Submission.run Legacy.Submission.run
  rw [initialState_eq submission program input (hvalid _)]
  have hprog : (legacyOf submission).image (phaseOf program) =
      imageOf (submission.image program) := by
    cases program <;> rfl
  have hlimit : Legacy.CYCLE_LIMIT = SigGolf.CYCLE_LIMIT := rfl
  rw [hprog, hlimit, Riscv.execute_eq]
  dsimp only
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  congr 1
  funext execution
  congr 1
  obtain ⟨exit, state, cycles, calls, compressions⟩ := execution
  cases exit <;> simp only [resultOf, Riscv.executionOf, Riscv.exitOf, readOutput_eq] <;> rfl
theorem imagesValid_of_admissible (submission : SigGolf.Submission)
    (hadmissible : (legacyOf submission).Admissible) : ImagesValid submission :=
  hadmissible.2
theorem runAgrees_of_admissible (submission : SigGolf.Submission)
    (hadmissible : (legacyOf submission).Admissible) : RunAgrees submission :=
  runAgrees_of_imagesValid submission (imagesValid_of_admissible submission hadmissible)
theorem evalWithAnswerFn_run (submission : SigGolf.Submission) (hrun : RunAgrees submission)
    (hash : SigGolf.Hash) (program : SigGolf.Program)
    (input : SigGolf.Input submission.sizes program) :
    evalWithAnswerFn hash (submission.run program input) =
      resultOf program ((legacyOf submission).runWith hash (phaseOf program)
        (inputOf program input)) := by
  rw [hrun, evalWithAnswerFn_map]
  rfl
end SigGolfCandidate.Transfer
end
-- ==== merged from Transfer_Statements ====
section

namespace SigGolfCandidate.Transfer
open OracleComp OracleSpec OracleComp.EvalDist
def honestOf (result : Legacy.HonestResult) : SigGolf.HonestResult :=
  ⟨result.success, fun program => result.costs (phaseOf program), result.verificationCycles⟩
theorem honest_eq (submission : SigGolf.Submission) (hrun : RunAgrees submission)
    (secretKey : SigGolf.SecretKey) (message : SigGolf.Message) :
    submission.honest secretKey message =
      honestOf <$> (legacyOf submission).honest secretKey message := by
  unfold SigGolf.Submission.honest Legacy.Submission.honest
  dsimp only
  rw [hrun SigGolf.Program.keygen secretKey, bind_map_left, map_bind]
  congr 1; funext keygen
  rcases keygen with ⟨_ | ⟨pk, cache⟩, _, _, _, _⟩
  · simp only [resultOf, Option.map_none, map_pure]
    congr 1
    simp only [honestOf, SigGolf.HonestResult.mk.injEq, true_and, and_true]
    funext program; cases program <;> rfl
  dsimp only [resultOf, Option.map, outputOf]
  rw [hrun SigGolf.Program.sign (secretKey, cache, message), bind_map_left, map_bind]
  congr 1; funext sign
  rcases sign with ⟨_ | signature, _, _, _, _⟩
  · simp only [resultOf, Option.map_none, map_pure]
    congr 1
    simp only [honestOf, SigGolf.HonestResult.mk.injEq, true_and, and_true]
    funext program; cases program <;> rfl
  dsimp only [resultOf, Option.map, outputOf]
  rw [hrun SigGolf.Program.expand (message, pk, signature), bind_map_left, map_bind]
  congr 1; funext expand
  rcases expand with ⟨_ | witness, _, _, _, _⟩
  · simp only [resultOf, Option.map_none, map_pure]
    congr 1
    simp only [honestOf, SigGolf.HonestResult.mk.injEq, true_and, and_true]
    funext program; cases program <;> rfl
  dsimp only [resultOf, Option.map, outputOf]
  rw [hrun SigGolf.Program.verify (message, pk, witness), bind_map_left, map_bind]
  congr 1; funext verify
  simp only [resultOf, map_pure, Option.isSome_map]
  congr 1
  simp only [honestOf, SigGolf.HonestResult.mk.injEq]
  refine ⟨rfl, ?_, rfl⟩
  funext program; cases program <;> rfl
theorem evalWithAnswerFn_honest (submission : SigGolf.Submission) (hrun : RunAgrees submission)
    (hash : SigGolf.Hash) (secretKey : SigGolf.SecretKey) (message : SigGolf.Message) :
    evalWithAnswerFn hash (submission.honest secretKey message) =
      honestOf (evalWithAnswerFn hash ((legacyOf submission).honest secretKey message)) := by
  rw [honest_eq submission hrun, evalWithAnswerFn_map]
theorem withRandomOracle_map {α β : Type} (f : α → β) (program : OracleComp SigGolf.HashSpec α) :
    SigGolf.withRandomOracle (f <$> program) = f <$> SigGolf.withRandomOracle program := by
  simp [SigGolf.withRandomOracle, simulateQ_map]
theorem withRandomOracle_eq {α : Type} (program : OracleComp SigGolf.HashSpec α) :
    SigGolf.withRandomOracle program = Legacy.withRandomOracle program := rfl
theorem verificationCycles_of_legacy (submission : SigGolf.Submission)
    (hrun : RunAgrees submission) (C : Nat) (hbound : (legacyOf submission).VerificationBound C) :
    submission.VerificationCycles C := by
  intro hash secretKey message
  dsimp only
  rw [evalWithAnswerFn_honest submission hrun]
  exact hbound hash secretKey message
theorem termination_of_legacy (submission : SigGolf.Submission) (hrun : RunAgrees submission)
    (hterm : (legacyOf submission).Terminates) : submission.Termination := by
  intro hash program input
  rw [evalWithAnswerFn_run submission hrun]
  exact (hterm hash (phaseOf program) (inputOf program input)).2
theorem two_rpow_eq (x : ℝ) : (2 : ENNReal) ^ x = ENNReal.ofReal (Real.rpow 2 x) := by
  rw [Real.rpow_eq_pow, ← ENNReal.ofReal_rpow_of_pos (by norm_num)]
  simp
theorem compressionBudgets_of_legacy (submission : SigGolf.Submission)
    (hrun : RunAgrees submission) (hbounds : (legacyOf submission).CompressionBounds) :
    submission.CompressionBudgets := by
  intro secretKey program budget hbudget
  have hphase : phaseOf program ∈ Legacy.Phase.budgeted ∧
      (phaseOf program).budget = budget := by
    cases program <;> simp_all [SigGolf.Program.budget, Legacy.Phase.budget, Legacy.Phase.budgeted,
      phaseOf, SigGolf.BUDGET_KEYGEN, SigGolf.BUDGET_SIGN, SigGolf.BUDGET_EXPAND,
      Legacy.BUDGET_KEYGEN, Legacy.BUDGET_SIGN, Legacy.BUDGET_EXPAND]
  have hlegacy := hbounds secretKey (phaseOf program) hphase.1
  have hworkload : (do
        let message ← ($ᵗ SigGolf.Message : ProbComp SigGolf.Message)
        SigGolf.withRandomOracle (submission.honest secretKey message)) =
      honestOf <$> (legacyOf submission).honestWorkload secretKey := by
    unfold Legacy.Submission.honestWorkload
    simp only [honest_eq submission hrun, withRandomOracle_map, map_bind]
    rfl
  rw [hworkload, expectedValue_map]
  refine le_of_eq_of_le ?_ hlegacy
  congr 1
  funext result
  simp only [honestOf, two_rpow_eq, hphase.2]
theorem forIn_eq_foldlM (submission : SigGolf.Submission) (hrun : RunAgrees submission)
    (secretKey : SigGolf.SecretKey) (messages : List SigGolf.Message) (summary : Legacy.HonestSummary) :
    forIn messages summary.allSucceed (fun message (allSucceeded : Bool) => do
        let result ← submission.honest secretKey message
        pure (ForInStep.yield (allSucceeded && result.success))) =
      (fun summary => summary.allSucceed) <$>
        messages.foldlM (fun summary message => do
          let result ← (legacyOf submission).honest secretKey message
          return (⟨summary.allSucceed && result.success,
            fun phase => max (summary.maxCosts phase) (result.costs phase)⟩ :
              Legacy.HonestSummary)) summary := by
  induction messages generalizing summary with
  | nil => simp
  | cons message messages ih =>
      simp only [List.forIn_cons, List.foldlM_cons, honest_eq submission hrun, bind_assoc,
        map_bind, bind_map_left, pure_bind]
      congr 1
      funext result
      have ih' := ih ⟨summary.allSucceed && result.success,
        fun phase => max (summary.maxCosts phase) (result.costs phase)⟩
      simp only [honest_eq submission hrun, bind_map_left] at ih'
      exact ih'
theorem everyMessageSucceeds_eq (submission : SigGolf.Submission) (hrun : RunAgrees submission)
    (secretKey : SigGolf.SecretKey) :
    submission.everyMessageSucceeds secretKey =
      (fun summary => summary.allSucceed) <$> (legacyOf submission).allMessages secretKey := by
  unfold SigGolf.Submission.everyMessageSucceeds Legacy.Submission.allMessages
  have := forIn_eq_foldlM submission hrun secretKey (Finset.univ : Finset SigGolf.Message).toList {}
  simp only at this ⊢
  rw [← this]
  simp
theorem completeness_of_legacy (submission : SigGolf.Submission) (hrun : RunAgrees submission)
    (hcomplete : (legacyOf submission).Complete) : submission.Completeness := by
  intro secretKey
  rw [everyMessageSucceeds_eq submission hrun, withRandomOracle_map,
    ← probEvent_eq_eq_probOutput, probEvent_map]
  exact hcomplete secretKey
theorem buffersDisjoint_iff (buffers : List (Nat × Nat)) :
    Legacy.Riscv.buffersDisjoint buffers = true ↔ buffers.Pairwise SigGolf.Riscv.DisjointBuffers := by
  induction buffers with
  | nil => simp [Legacy.Riscv.buffersDisjoint]
  | cons first rest ih =>
      simp only [Legacy.Riscv.buffersDisjoint, Bool.and_eq_true, List.all_eq_true,
        decide_eq_true_eq, List.pairwise_cons, ih]
      rfl
theorem admission_of_legacy (submission : SigGolf.Submission)
    (hadmissible : (legacyOf submission).Admissible) : submission.Admission := by
  obtain ⟨⟨_, hS, hW, hK⟩, himages⟩ := hadmissible
  refine ⟨⟨hS, hW, hK⟩, fun program => ?_⟩
  have h := himages (phaseOf program)
  simp only [programOf_phaseOf] at h
  obtain ⟨hsize, hall, hdisjoint⟩ := h
  refine ⟨hsize, ?_, (buffersDisjoint_iff _).1 hdisjoint⟩
  intro buffer hbuffer
  exact of_decide_eq_true (List.all_eq_true.1 hall buffer hbuffer)
end SigGolfCandidate.Transfer
end
-- ==== merged from Transfer_Security ====
section

namespace SigGolfCandidate.Transfer.Sec
open OracleComp OracleSpec SigGolf
def countImpl : QueryImpl World (AddWriterT ℕ (OracleComp World)) :=
  (QueryImpl.ofLift World (OracleComp World)).withAddCost hashCost
def countQ {α : Type} (x : OracleComp World α) : OracleComp World (α × ℕ) :=
  (fun z => (z.1, Multiplicative.toAdd z.2)) <$> (simulateQ countImpl x).run
variable {α β : Type}
@[simp] theorem countQ_pure (a : α) : countQ (pure a : OracleComp World α) = pure (a, 0) := by
  simp [countQ]
theorem countQ_bind (x : OracleComp World α) (f : α → OracleComp World β) :
    countQ (x >>= f) = countQ x >>= fun z => (fun w => (w.1, z.2 + w.2)) <$> countQ (f z.1) := by
  simp [countQ, WriterT.run_bind]
theorem countQ_map (x : OracleComp World α) (f : α → β) :
    countQ (f <$> x) = (fun z => (f z.1, z.2)) <$> countQ x := by
  simp [countQ]
abbrev hashQ (t : Query) : OracleComp World (BitVec 256) := liftM (World.query (Sum.inr t))
theorem countQ_hashQ (t : Query) : countQ (hashQ t) = (fun u => (u, 1)) <$> hashQ t := by
  simp [countQ, countImpl, hashCost]
theorem countQ_legacyHash (t : Legacy.Query) :
    countQ (liftM (liftM (Legacy.HashSpec.query t) : OracleComp Legacy.HashSpec _) :
      OracleComp World (BitVec 256)) =
    (fun u => (u, 1)) <$> (liftM (liftM (Legacy.HashSpec.query t) : OracleComp Legacy.HashSpec _) :
      OracleComp World (BitVec 256)) :=
  countQ_hashQ t
theorem countQ_execute (fuel : ℕ) (image : Legacy.Riscv.Image) (state : RiscvZkvm.Rv64.MachineState) :
    countQ (liftM (Legacy.Riscv.execute fuel image state) : OracleComp World _) =
      (fun e => (e, e.hashCalls)) <$> liftM (Legacy.Riscv.execute fuel image state) := by
  induction fuel generalizing state with
  | zero => simp [Legacy.Riscv.execute]
  | succ fuel ih =>
    rw [Legacy.Riscv.execute]
    split
    · simp
    · split_ifs
      · simp only [liftM_bind]
        rw [countQ_bind, countQ_legacyHash]
        simp [countQ_map, ih, Legacy.Riscv.Execution.charge, Nat.add_comm]
      all_goals simp
    · split
      · simp
      · simp [countQ_map, ih, Legacy.Riscv.Execution.charge]
theorem countQ_legacyRun (old : Legacy.Submission) (phase : Legacy.Phase)
    (input : Legacy.Input old.sizes phase) :
    countQ (liftM (old.run phase input) : OracleComp World _) =
      (fun r => (r, r.hashCalls)) <$> liftM (old.run phase input) := by
  unfold Legacy.Submission.run
  split
  · simp
  · simp only [liftM_bind, liftM_pure, countQ_bind, countQ_execute]
    simp
abbrev coinQ (n : ℕ) : OracleComp World (Fin (n + 1)) := liftM (World.query (Sum.inl n))
theorem countQ_coinQ (n : ℕ) : countQ (coinQ n) = (fun u => (u, 0)) <$> coinQ n := by
  simp [countQ, countImpl, hashCost]
theorem countQ_unifQ (n : ℕ) :
    countQ (liftM (liftM (unifSpec.query n) : ProbComp _) : OracleComp World (Fin (n + 1))) =
      (fun u => (u, 0)) <$> (liftM (liftM (unifSpec.query n) : ProbComp _) :
        OracleComp World (Fin (n + 1))) :=
  countQ_coinQ n
theorem countQ_liftProb (x : ProbComp α) :
    countQ (liftM x : OracleComp World α) = (fun a => (a, 0)) <$> liftM x := by
  induction x using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    simp only [liftM_bind, countQ_bind, ih, countQ_unifQ]
    simp
abbrev so : QueryImpl World (StateT (QueryCache HashSpec) ProbComp) :=
  unifFwdImpl HashSpec + HashSpec.randomOracle
theorem simulate_countImpl (G : OracleComp World α) :
    simulateQ so ((simulateQ countImpl G).run) = (simulateQ (so.withAddCost hashCost) G).run := by
  induction G using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    simp [countImpl] at ih ⊢
    simp [ih]
def Dom {α β : Type} (p : α → Prop) (q : β → Prop) (A : OracleComp World α)
    (B : OracleComp World β) : Prop :=
  ∀ σ, Pr[p | (simulateQ so A).run' σ] ≤ Pr[q | (simulateQ so B).run' σ]
namespace Dom
variable {γ α' β' : Type} {p p' : α → Prop} {q q' : β → Prop}
  {A : OracleComp World α} {B : OracleComp World β}
theorem bind (x : OracleComp World γ) {f : γ → OracleComp World α} {g : γ → OracleComp World β}
    (h : ∀ c, Dom p q (f c) (g c)) : Dom p q (x >>= f) (x >>= g) := by
  intro σ
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun z => mul_le_mul_right ?_ _
  have := h z.1 z.2
  simpa only [StateT.run'_eq] using this
theorem map_left {f : α' → α} {A : OracleComp World α'} (h : Dom (p ∘ f) q A B) :
    Dom p q (f <$> A) B := by
  intro σ
  simpa [simulateQ_map, StateT.run'_eq, probEvent_map, Function.comp_def] using h σ
theorem map_right {f : β' → β} {B : OracleComp World β'} (h : Dom p (q ∘ f) A B) :
    Dom p q A (f <$> B) := by
  intro σ
  simpa [simulateQ_map, StateT.run'_eq, probEvent_map, Function.comp_def] using h σ
theorem mono_left (hp : ∀ z, p' z → p z) (h : Dom p q A B) : Dom p' q A B :=
  fun σ => le_trans (probEvent_mono fun z _ => hp z) (h σ)
theorem mono_right (hq : ∀ z, q z → q' z) (h : Dom p q A B) : Dom p q' A B :=
  fun σ => le_trans (h σ) (probEvent_mono fun z _ => hq z)
theorem of_false (hp : ∀ z, ¬ p z) : Dom p q A B := by
  intro σ
  have : Pr[p | (simulateQ so A).run' σ] = 0 := by
    rw [probEvent_eq_zero_iff]; intro z _; exact hp z
  rw [this]; exact zero_le
theorem pure_pure {a : α} {b : β} (h : p a → q b) :
    Dom p q (pure a) (pure b) := by
  intro σ
  classical
  simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure, probEvent_pure]
  by_cases ha : p a
  · simp [ha, h ha]
  · simp [ha]
end Dom
noncomputable def depth {ι : Type} {spec : OracleSpec ι} [spec.Fintype] {α : Type} :
    OracleComp spec α → ℕ
  | .pure _ => 0
  | .queryBind _ k => (Finset.univ.sup fun u => depth (k u)) + 1
theorem depth_lt {ι : Type} {spec : OracleSpec ι} [spec.Fintype] {α : Type} {t : spec.Domain}
    (k : spec.Range t → OracleComp spec α) (u : spec.Range t) :
    depth (k u) < depth (OracleComp.queryBind t k) := by
  show depth (k u) < (Finset.univ.sup fun u => depth (k u)) + 1
  exact Nat.lt_succ_of_le (Finset.le_sup (f := fun u => depth (k u)) (Finset.mem_univ u))
abbrev NewComp (S : Sizes) := OracleComp (World + SigningSpec S) (Option (Forgery S))
def forgeryOf {S : Sizes} : Forgery S → Legacy.Forgery (sizesOf S)
  | .witness m w => .witness m w
  | .signature m s => .signature m s
def requestOf {S : Sizes} (r : SigningRequest S) : Legacy.SigningRequest (sizesOf S) :=
  ⟨r.message, r.cache⟩
def stepOf {S : Sizes} : NewComp S → Legacy.Action (sizesOf S) (Option (NewComp S))
  | .pure (some f) => .submit (forgeryOf f)
  | .pure none => .step none
  | .queryBind (.inl (.inl n)) k => .sample n (fun u => some (k u))
  | .queryBind (.inl (.inr x)) k => .hash x (fun h => some (k h))
  | .queryBind (.inr r) k => .sign (requestOf r) (fun o => some (k o))
def advOf {S : Sizes} (adv : Adversary S) : Legacy.Adversary (sizesOf S) where
  State := Option (NewComp S)
  initial pk cache := some (adv pk cache)
  step
    | none => .step none
    | some c => stepOf c
example {S : Sizes} (n : ℕ) (k : Fin (n+1) → NewComp S) :
    stepOf (OracleComp.queryBind (Sum.inl (Sum.inl n)) k) = .sample n (fun u => some (k u)) := rfl
section New
variable (sub : Submission)
abbrev implN (sk : SecretKey) :
    QueryImpl (World + SigningSpec sub.sizes) (WriterT (SigningLog sub.sizes) (OracleComp World)) :=
  QueryImpl.ofLift World (WriterT (SigningLog sub.sizes) (OracleComp World)) +
    sub.signingOracle sk
def tailN (pk : PublicKey) (log : SigningLog sub.sizes) :
    Option (Forgery sub.sizes) → OracleComp World Bool
  | none => pure false
  | some forgery => do
      let forged ← liftM (sub.checkForgery pk log forgery)
      pure (decide log.WithinLifetime && forged)
def contN (sk : SecretKey) (pk : PublicKey) (c : NewComp sub.sizes) (L : SigningLog sub.sizes) :
    OracleComp World Bool :=
  (simulateQ (implN sub sk) c).run >>= fun z => tailN sub pk (L ++ z.2) z.1
theorem game_eq (adv : Adversary sub.sizes) :
    sub.game adv = (do
      let sk ← liftM ($ᵗ SecretKey : ProbComp SecretKey)
      let keygen ← liftM (sub.run .keygen sk)
      match keygen.output with
      | none => pure false
      | some (pk, cache) => contN sub sk pk (adv pk cache) []) := by
  unfold Submission.game
  congr 1; funext sk; congr 1; funext keygen
  rcases keygen.output with _ | ⟨pk, cache⟩
  · rfl
  · simp only [contN, Submission.interact]
    congr 1; funext z
    rcases z with ⟨_ | f, log⟩ <;> simp [tailN]
variable {sub}
theorem contN_pure (sk : SecretKey) (pk : PublicKey) (x : Option (Forgery sub.sizes))
    (L : SigningLog sub.sizes) : contN sub sk pk (pure x) L = tailN sub pk L x := by
  simp [contN]
theorem contN_queryBind (sk : SecretKey) (pk : PublicKey) (t : (World + SigningSpec sub.sizes).Domain)
    (k : (World + SigningSpec sub.sizes).Range t → NewComp sub.sizes) (L : SigningLog sub.sizes) :
    contN sub sk pk (OracleComp.queryBind t k) L =
      (implN sub sk t).run >>= fun z => contN sub sk pk (k z.1) (L ++ z.2) := by
  rw [show OracleComp.queryBind t k = (liftM ((World + SigningSpec sub.sizes).query t) >>= k) from rfl]
  simp only [contN, simulateQ_bind, simulateQ_spec_query, WriterT.run_bind', bind_assoc]
  congr 1; funext z
  simp [List.append_assoc]
theorem implN_coin (sk : SecretKey) (n : ℕ) :
    (implN sub sk (Sum.inl (Sum.inl n))).run = (fun u => (u, [])) <$> coinQ n := rfl
theorem implN_hash (sk : SecretKey) (x : Query) :
    (implN sub sk (Sum.inl (Sum.inr x))).run = (fun u => (u, [])) <$> hashQ x := rfl
theorem withLogging_run {S : Sizes} (so : QueryImpl (SigningSpec S) (OracleComp World))
    (r : SigningRequest S) :
    (so.withLogging r).run = (fun u => (u, [⟨r, u⟩])) <$> so r := by
  rw [QueryImpl.withLogging_apply]
  simp
theorem implN_sign (sk : SecretKey) (r : SigningRequest sub.sizes) :
    (implN sub sk (Sum.inr r)).run = (fun run => (run.output, [⟨r, run.output⟩])) <$>
      (liftM (sub.run .sign (sk, r.cache, r.message)) : OracleComp World _) := by
  simp only [implN]
  rw [QueryImpl.add_apply_inr, Submission.signingOracle]
  refine (withLogging_run _ r).trans ?_
  generalize (liftM (sub.run .sign (sk, r.cache, r.message)) : OracleComp World _) = x
  simp only [bind_pure_comp]
  exact Functor.map_map _ _ _
end New
section Rel
variable {S : Sizes}
structure Rel (L : SigningLog S) (T : Legacy.Transcript (sizesOf S)) : Prop where
  count : T.signingRequests = L.length
  lifetime : L.length ≤ LIFETIME
  signed : ∀ m s, (m, s) ∈ T.signed ↔ L.Contains m s
theorem Rel.nil (n : ℕ) : Rel ([] : SigningLog S) ({ hashCalls := n } : Legacy.Transcript _) :=
  ⟨rfl, Nat.zero_le _, by simp [SigningLog.Contains]⟩
theorem Rel.freshMessage {L : SigningLog S} {T} (h : Rel L T) (m : Message) :
    T.freshMessage m = !decide (L.Signed m) := by
  unfold Legacy.Transcript.freshMessage
  congr 1
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true, beq_iff_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨m', s⟩, hmem, rfl⟩
    obtain ⟨e, he, hm, hs⟩ := (h.signed _ _).1 hmem
    refine ⟨e, he, hm, ?_⟩
    rw [hs]; rfl
  · rintro ⟨e, he, hm, hs⟩
    obtain ⟨s, hs'⟩ := Option.isSome_iff_exists.1 hs
    exact ⟨(m, s), (h.signed _ _).2 ⟨e, he, hm, hs'⟩, rfl⟩
theorem Rel.freshSignature {L : SigningLog S} {T} (h : Rel L T) (m : Message) (s) :
    T.freshSignature m s = !decide (L.Contains m s) := by
  unfold Legacy.Transcript.freshSignature
  congr 1
  rw [Bool.eq_iff_iff]
  simp only [List.contains_iff_mem, decide_eq_true_eq]
  exact h.signed m s
theorem Rel.record {L : SigningLog S} {T} (h : Rel L T)
    (hlt : T.signingRequests < Legacy.LIFETIME) (r : SigningRequest S)
    (result : Legacy.RunResult (Legacy.Bytes (sizesOf S).signature)) :
    Rel (L ++ [⟨r, result.value⟩]) (T.record r.message result) := by
  constructor
  · simp [Legacy.Transcript.record, h.count]
  · have := h.count ▸ hlt
    simp only [List.length_append, List.length_singleton]
    exact this
  · intro m s
    have hc : (L ++ [⟨r, result.value⟩] : SigningLog S).Contains m s ↔
        L.Contains m s ∨ (r.message = m ∧ result.value = some s) := by
      simp only [SigningLog.Contains, List.mem_append, List.mem_singleton]
      constructor
      · rintro ⟨e, he | rfl, hm, hs⟩
        · exact Or.inl ⟨e, he, hm, hs⟩
        · exact Or.inr ⟨hm, hs⟩
      · rintro (⟨e, he, hm, hs⟩ | ⟨hm, hs⟩)
        · exact ⟨e, Or.inl he, hm, hs⟩
        · exact ⟨_, Or.inr rfl, hm, hs⟩
    rw [hc, ← h.signed]
    unfold Legacy.Transcript.record
    rcases hv : result.value with _ | sig
    · simp
    · simp only [List.mem_cons, Prod.mk.injEq, Option.some.injEq]
      constructor
      · rintro (⟨rfl, rfl⟩ | h') <;> simp_all
      · rintro (h' | ⟨rfl, rfl⟩) <;> simp_all
end Rel
section Old
variable (sub : Submission) (adv : Adversary sub.sizes) (sk : SecretKey) (pk : PublicKey)
theorem old_none (T : Legacy.Transcript (sizesOf sub.sizes)) (rounds : ℕ) :
    (legacyOf sub).interact (advOf adv) sk pk rounds none T = pure ⟨false, T.hashCalls⟩ := by
  induction rounds with
  | zero => rfl
  | succ r ih => exact ih
theorem old_pure_none (T : Legacy.Transcript (sizesOf sub.sizes)) (r : ℕ) :
    (legacyOf sub).interact (advOf adv) sk pk (r + 1) (some (pure none)) T = pure ⟨false, T.hashCalls⟩ := by
  exact old_none sub adv sk pk T r
theorem old_pure_some (T : Legacy.Transcript (sizesOf sub.sizes)) (r : ℕ) (f : Forgery sub.sizes) :
    (legacyOf sub).interact (advOf adv) sk pk (r + 1) (some (pure (some f))) T =
      liftM ((legacyOf sub).checkForgery pk T (forgeryOf f)) := by
  rfl
theorem old_coin (T : Legacy.Transcript (sizesOf sub.sizes)) (r : ℕ) (n : ℕ)
    (k : Fin (n + 1) → NewComp sub.sizes) :
    (legacyOf sub).interact (advOf adv) sk pk (r + 1)
      (some (OracleComp.queryBind (Sum.inl (Sum.inl n)) k)) T =
      coinQ n >>= fun u => (legacyOf sub).interact (advOf adv) sk pk r (some (k u)) T := by
  rfl
theorem old_hash (T : Legacy.Transcript (sizesOf sub.sizes)) (r : ℕ) (x : Query)
    (k : BitVec 256 → NewComp sub.sizes) :
    (legacyOf sub).interact (advOf adv) sk pk (r + 1)
      (some (OracleComp.queryBind (Sum.inl (Sum.inr x)) k)) T =
      hashQ x >>= fun u => (legacyOf sub).interact (advOf adv) sk pk r (some (k u))
        { T with hashCalls := T.hashCalls + 1 } := by
  rfl
theorem old_sign (T : Legacy.Transcript (sizesOf sub.sizes)) (r : ℕ) (req : SigningRequest sub.sizes)
    (k : Option (Bytes sub.sizes.signature) → NewComp sub.sizes) :
    (legacyOf sub).interact (advOf adv) sk pk (r + 1)
      (some (OracleComp.queryBind (Sum.inr req) k)) T =
      if T.signingRequests < Legacy.LIFETIME then
        (liftM ((legacyOf sub).run .sign (sk, req.cache, req.message)) : OracleComp World _) >>=
          fun result => (legacyOf sub).interact (advOf adv) sk pk r (some (k result.value))
            (T.record req.message result)
      else pure ⟨false, T.hashCalls⟩ := by
  rfl
end Old
theorem map_map_eq_bind {γ δ ε : Type} (x : OracleComp World γ) (g : γ → δ) (f : δ → ε) :
    f <$> (g <$> x) = x >>= fun r => pure (f (g r)) := by
  simp [map_eq_bind_pure_comp]
section Main
variable {sub : Submission} (hrun : RunAgrees sub)
include hrun
omit hrun in
@[simp] theorem resultOf_isSome {S : Sizes} (p : Program)
    (r : Legacy.RunResult (Legacy.Output (sizesOf S) (phaseOf p))) :
    (resultOf p r).output.isSome = r.value.isSome := by
  simp [resultOf]
theorem countQ_run (p : Program) (input : Input sub.sizes p) :
    countQ (liftM (sub.run p input) : OracleComp World _) =
      (liftM ((legacyOf sub).run (phaseOf p) (inputOf p input)) : OracleComp World _) >>=
        fun r => pure (resultOf p r, r.hashCalls) := by
  have h : (liftM (sub.run p input) : OracleComp World _) = resultOf p <$>
      (liftM ((legacyOf sub).run (phaseOf p) (inputOf p input) : OracleComp HashSpec _) :
        OracleComp World _) := by
    rw [hrun p input]; exact liftM_map _ _
  rw [h]
  erw [countQ_map]
  erw [countQ_legacyRun]
  exact map_map_eq_bind _ _ _
omit hrun in
theorem Dom.pure_left {α β : Type} {p : α → Prop} {q : β → Prop} {a : α} {B : OracleComp World β}
    (h : ¬ p a) : Dom p q (pure a) B := by
  intro σ
  classical
  simp [probEvent_pure, h]
theorem check_dom (pk : PublicKey) (Q : ℕ) (L : SigningLog sub.sizes)
    (T : Legacy.Transcript (sizesOf sub.sizes)) (hrel : Rel L T) (f : Forgery sub.sizes) :
    Dom (fun z : Bool × ℕ => z.1 = true ∧ T.hashCalls + z.2 ≤ Q)
      (fun r : Legacy.AttackResult => r.won = true ∧ r.hashCalls ≤ Q)
      (countQ (tailN sub pk L (some f)))
      (liftM ((legacyOf sub).checkForgery pk T (forgeryOf f))) := by
  have hlt : decide L.WithinLifetime = true := by simpa using hrel.lifetime
  cases f with
  | witness m w =>
    simp only [tailN, forgeryOf, Submission.checkForgery, Legacy.Submission.checkForgery, hlt,
      Bool.true_and, liftM_bind, liftM_pure, countQ_bind]
    erw [countQ_run hrun]
    simp only [countQ_pure, bind_assoc, pure_bind, map_pure]
    refine Dom.bind _ fun r => Dom.pure_pure ?_
    erw [resultOf_isSome, hrel.freshMessage]
    intro h; simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      decide_eq_false_iff_not] at h ⊢
    exact h
  | signature m s =>
    simp only [tailN, forgeryOf, Submission.checkForgery, Legacy.Submission.checkForgery, hlt,
      Bool.true_and, liftM_bind, countQ_bind]
    erw [countQ_run hrun]
    simp only [countQ_pure, bind_assoc, pure_bind, map_pure]
    refine Dom.bind _ fun r => ?_
    rcases hv : r.value with _ | wit
    · have ho : (resultOf Program.expand r).output = none := by
        simp only [resultOf, hv]; rfl
      erw [ho]
      simp only [liftM_pure, countQ_pure, map_pure, pure_bind]
      exact Dom.pure_left (by simp)
    · have ho : (resultOf Program.expand r).output = some wit := by
        simp only [resultOf, hv]; rfl
      erw [ho]
      simp only [liftM_bind, liftM_pure, countQ_bind]
      erw [countQ_run hrun]
      simp only [countQ_pure, bind_assoc, pure_bind, map_pure, map_bind]
      refine Dom.bind _ fun r' => Dom.pure_pure ?_
      erw [resultOf_isSome, hrel.freshSignature]
      intro h
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
        decide_eq_false_iff_not, Nat.add_zero] at h ⊢
      exact ⟨h.1, by omega⟩
omit hrun in
theorem alwaysFalse_bind {γ : Type} (x : OracleComp World γ) {f : γ → OracleComp World Bool}
    (h : ∀ c, (fun _ => false) <$> f c = f c) :
    (fun _ => false) <$> (x >>= f) = x >>= f := by
  rw [map_bind]; congr 1; funext c; exact h c
omit hrun in
theorem tailN_alwaysFalse (pk : PublicKey) (L : SigningLog sub.sizes) (hL : LIFETIME < L.length)
    (f : Option (Forgery sub.sizes)) :
    (fun _ => false) <$> tailN sub pk L f = tailN sub pk L f := by
  have : decide L.WithinLifetime = false := by simp; omega
  rcases f with _ | f
  · simp [tailN]
  · simp only [tailN, this, Bool.false_and, map_bind, map_pure]
omit hrun in
theorem contN_alwaysFalse (sk : SecretKey) (pk : PublicKey) (c : NewComp sub.sizes)
    (L : SigningLog sub.sizes) (hL : LIFETIME < L.length) :
    (fun _ => false) <$> contN sub sk pk c L = contN sub sk pk c L :=
  alwaysFalse_bind _ fun z => tailN_alwaysFalse pk _ (by simp; omega) _
omit hrun in
theorem Dom.of_alwaysFalse {β : Type} {P : ℕ → Prop} {q : β → Prop} {A : OracleComp World Bool}
    {B : OracleComp World β} (h : (fun _ => false) <$> A = A) :
    Dom (fun z : Bool × ℕ => z.1 = true ∧ P z.2) q (countQ A) B := by
  rw [← h, countQ_map]
  exact Dom.map_left (Dom.of_false (by simp))
theorem main_dom (adv : Adversary sub.sizes) (sk : SecretKey) (pk : PublicKey) (Q : ℕ)
    (c : NewComp sub.sizes) :
    ∀ (L : SigningLog sub.sizes) (T : Legacy.Transcript (sizesOf sub.sizes)) (rounds : ℕ),
      depth c < rounds → Rel L T →
      Dom (fun z : Bool × ℕ => z.1 = true ∧ T.hashCalls + z.2 ≤ Q)
        (fun r : Legacy.AttackResult => r.won = true ∧ r.hashCalls ≤ Q)
        (countQ (contN sub sk pk c L))
        ((legacyOf sub).interact (advOf adv) sk pk rounds (some c) T) := by
  induction c using OracleComp.recOn with
  | pure x =>
    intro L T rounds hd hrel
    obtain ⟨r, rfl⟩ : ∃ r, rounds = r + 1 := ⟨rounds - 1, by omega⟩
    erw [contN_pure]
    rcases x with _ | f
    · simp only [tailN, countQ_pure]
      exact Dom.pure_left (by simp)
    · erw [old_pure_some]
      exact check_dom hrun pk Q L T hrel f
  | queryBind t k ih =>
    intro L T rounds hd hrel
    obtain ⟨r, rfl⟩ : ∃ r, rounds = r + 1 := ⟨rounds - 1, by omega⟩
    have hk : ∀ u, depth (k u) < r := fun u => by have := depth_lt k u; omega
    rw [contN_queryBind]
    rcases t with (n | x) | req
    · erw [implN_coin, old_coin]
      rw [bind_map_left, countQ_bind, countQ_coinQ, bind_map_left]
      refine Dom.bind _ fun u => Dom.map_left ?_
      simp only [List.append_nil]
      refine Dom.mono_left ?_ (ih u L T r (hk u) hrel)
      intro z hz; simpa using hz
    · erw [implN_hash, old_hash]
      rw [bind_map_left, countQ_bind, countQ_hashQ, bind_map_left]
      refine Dom.bind _ fun u => Dom.map_left ?_
      simp only [List.append_nil]
      have hrel' : Rel L { T with hashCalls := T.hashCalls + 1 } :=
        ⟨hrel.count, hrel.lifetime, hrel.signed⟩
      refine Dom.mono_left ?_ (ih u L { T with hashCalls := T.hashCalls + 1 } r (hk u) hrel')
      intro z hz
      simp only [Function.comp] at hz ⊢
      exact ⟨hz.1, by omega⟩
    · erw [implN_sign, old_sign]
      split_ifs with hlt
      · erw [bind_map_left]
        erw [countQ_bind, countQ_run hrun]
        simp only [bind_assoc, pure_bind]
        refine Dom.bind _ fun res => Dom.map_left ?_
        have ho : (resultOf Program.sign res).output = res.value := by
          simp only [resultOf]; cases res.value <;> rfl
        erw [ho]
        refine Dom.mono_left ?_ (ih res.value _ _ r (hk _) (hrel.record hlt req res))
        intro z hz
        simp only [Function.comp, Legacy.Transcript.record] at hz ⊢
        exact ⟨hz.1, by omega⟩
      · have hL : LIFETIME ≤ L.length := by
          have := hrel.count; simp only [Legacy.LIFETIME] at hlt; simp only [LIFETIME]; omega
        refine Dom.of_alwaysFalse (P := fun n => T.hashCalls + n ≤ Q) ?_
        erw [bind_map_left]
        exact alwaysFalse_bind _ fun run =>
          contN_alwaysFalse sk pk _ _ (by simp; omega)
theorem game_dom (adv : Adversary sub.sizes) (Q rounds : ℕ)
    (hrounds : ∀ pk cache, depth (adv pk cache) < rounds) :
    Dom (fun z : Bool × ℕ => z.1 = true ∧ z.2 ≤ Q)
      (fun r : Legacy.AttackResult => r.won = true ∧ r.hashCalls ≤ Q)
      (countQ (sub.game adv))
      (do
        let secretKey ← liftM Legacy.sampleSecretKey
        let keygen ← liftM ((legacyOf sub).run .keygen secretKey)
        let some (pk, cache) := keygen.value | return ⟨false, keygen.hashCalls⟩
        (legacyOf sub).interact (advOf adv) secretKey pk rounds ((advOf adv).initial pk cache)
          { hashCalls := keygen.hashCalls }) := by
  rw [game_eq, countQ_bind, countQ_liftProb, bind_map_left]
  refine Dom.bind _ fun sk => Dom.map_left ?_
  erw [countQ_bind, countQ_run hrun]
  simp only [bind_assoc, pure_bind]
  refine Dom.bind _ fun res => Dom.map_left ?_
  rcases hv : res.value with _ | ⟨pk, cache⟩
  · have ho : (resultOf Program.keygen res).output = none := by
      simp only [resultOf, hv]; rfl
    erw [ho]
    exact Dom.pure_left (by simp)
  · have ho : (resultOf Program.keygen res).output = some (pk, cache) := by
      simp only [resultOf, hv]; rfl
    erw [ho]
    refine Dom.mono_left ?_ (main_dom hrun adv sk pk Q (adv pk cache) [] { hashCalls := res.hashCalls }
      rounds (hrounds pk cache) (Rel.nil _))
    intro z hz
    simp only [Function.comp] at hz ⊢
    exact ⟨hz.1, by omega⟩
end Main
theorem experiment_eq (sub : Submission) (adv : Adversary sub.sizes) :
    sub.securityExperiment adv = (simulateQ so (countQ (sub.game adv))).run' ∅ := by
  unfold Submission.securityExperiment countQ
  rw [simulateQ_map, simulate_countImpl]
  simp only [StateT.run'_eq, StateT.run_map, Functor.map_map]
  rfl
theorem security_of_legacy (sub : Submission) (hrun : RunAgrees sub)
    (hsec : (legacyOf sub).Secure) : sub.Security := by
  intro adv Q hQ
  let rounds := (Finset.univ.sup fun pc : PublicKey × Bytes sub.sizes.cache =>
    depth (adv pc.1 pc.2)) + 1
  have hrounds : ∀ pk cache, depth (adv pk cache) < rounds := fun pk cache =>
    Nat.lt_succ_of_le (Finset.le_sup (f := fun pc : PublicKey × Bytes sub.sizes.cache =>
      depth (adv pc.1 pc.2)) (Finset.mem_univ (pk, cache)))
  have hold := hsec (advOf adv) rounds Q hQ
  have hnew := game_dom hrun adv Q rounds hrounds ∅
  rw [experiment_eq]
  refine le_trans (le_of_eq ?_) (le_trans hnew (le_of_eq_of_le ?_ hold))
  · rfl
  · unfold Legacy.Submission.securityExperiment Legacy.withRandomness
    congr 3
    congr 1
    funext sk
    congr 1
    funext keygen
    obtain ⟨_ | ⟨pk, cache⟩, _, _, _, _⟩ := keygen
    · rfl
    · rfl
end SigGolfCandidate.Transfer.Sec
namespace SigGolfCandidate.Transfer
theorem security_of_legacy (sub : SigGolf.Submission) (hrun : RunAgrees sub)
    (hsec : (legacyOf sub).Secure) : sub.Security :=
  Sec.security_of_legacy sub hrun hsec
end SigGolfCandidate.Transfer
end
-- ==== merged from ClaudeWCT_W9_T3M_Final_Transfer ====
section


namespace ClaudeWCT.W9.T3M.Final.Paired
open SigGolfCandidate.Transfer
open ClaudeWCT.W9.T3M (Images)
def submissionNew (I : Images) : SigGolf.Submission := currentOf (submission I)
theorem legacyOf_submissionNew (I : Images) : legacyOf (submissionNew I) = submission I :=
  legacyOf_currentOf (submission I)
theorem certificateNew_of {I : Images} (E : EncodingFacts) (F : SourceQueries) (P : Pending I) (S : SourceFacts) :
    SigGolf.Certificate (submissionNew I) 7006 := by
  have hL : SigGolfCandidate.Legacy.Certificate (legacyOf (submissionNew I)) 7006 := by
    rw [legacyOf_submissionNew]
    exact certificate_of E F P S
  have hrun : RunAgrees (submissionNew I) := runAgrees_of_admissible (submissionNew I) hL.admissible
  exact
    { admission := admission_of_legacy (submissionNew I) hL.admissible
      completeness := completeness_of_legacy (submissionNew I) hrun hL.completeness
      compressionBudgets := compressionBudgets_of_legacy (submissionNew I) hrun hL.compressionBounds
      verificationCycles := verificationCycles_of_legacy (submissionNew I) hrun _ hL.verificationBound
      security := security_of_legacy (submissionNew I) hrun hL.security
      termination := termination_of_legacy (submissionNew I) hrun hL.termination }
end ClaudeWCT.W9.T3M.Final.Paired
end
-- ==== merged from T3M_Keygen_TopLeaf ====
section

/-!
# Keygen top leaf with family seeds (campaign T8D, TOP2 NF17)

The keygen image's top-leaf routine (entry 144) first runs KTOP (img-v6, 612 -> 1149..1168 + the pair loop 618..640:
at a family start `leaf % 4 = 0` the family's private pairs `privatePair 0 0 0 (31 f / 2 + j) 0`, `j ∈ [f % 2, 16)`,
copied to the coefficient buffer at `KCOEF`, an odd family first copying the carry slot 31 to slot 0; otherwise
nothing: `topFamilyCoefs`), then for every chain `i < 51` (campaign T51) runs
HORN (642 -> KHORN 1169..1176, loop 647..682: `familyEval coefs (topPoint leaf i)`, 31 coefficients, into `CHAIN + 48`), the per-chain cap table CAP (684..688: `maxDigit 0 i`),
the shared chain routine (117) and stores the chain end; finally the leaf hash. This file proves the blocks, the two
new loops and `buildLeafTop_tsim` (refinement of `T3.buildLeafTop leaf []` with exact step/cycle/hash counts).
-/

namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest chainCount maxDigit chain leafHash privatePair header privateInput
  topCoefsK topPairsFrom topFamilyCoefs topCoefCount topSeedPair topSeed topPoint buildLeafTopC pad64)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.Machine.Sign.Gf ClaudeWCT.Arith

local instance (image : Image) (pc : Word) (code : List (BitVec 32)) :
    Decidable (CodeAt image pc code) := by
  unfold CodeAt
  infer_instance

/-! ## Blocks -/
def kg27 : List (BitVec 32) := sub27K
def kg159 : List (BitVec 32) := sub42K
def kg161 : List (BitVec 32) := sub44K.take 1
def kg188 : List (BitVec 32) := [20647475]
def kg192 : List (BitVec 32) := sub75K
def kg612 : List (BitVec 32) := coefgenCode.take 1
def kgCG1 : List (BitVec 32) := (coefgenCode.drop 6).take 5
def kgCG2 : List (BitVec 32) := (coefgenCode.drop 12).take 15
def kgCG3 : List (BitVec 32) := (coefgenCode.drop 27).take 2
def kgH0 : List (BitVec 32) := hornCode.take 1
def kgHK : List (BitVec 32) := (hornCode.drop 5).take 6
def kgHB1 : List (BitVec 32) := (hornCode.drop 11).take 2
def kgHB2 : List (BitVec 32) := (hornCode.drop 13).take 3
def kgHB3 : List (BitVec 32) := (hornCode.drop 16).take 9
def kgHF : List (BitVec 32) := (hornCode.drop 25).take 12
def kgHE : List (BitVec 32) := (hornCode.drop 37).take 4
def kgC1 : List (BitVec 32) := capCode.take 3
def kgC2 : List (BitVec 32) := capCode.drop 3
/-- Campaign T51: the CAP continuation at 770 (`i < 48`, `i < 50`, chain 50). -/
def kgC3 : List (BitVec 32) := capCont.take 2
def kgC4 : List (BitVec 32) := (capCont.drop 2).take 3
def kgC5 : List (BitVec 32) := capCont.drop 5
def kfA : List (BitVec 32) := ktopCode.take 2
def kfB : List (BitVec 32) := (ktopCode.drop 2).take 10
def kfD : List (BitVec 32) := (ktopCode.drop 12).take 5
def kfE : List (BitVec 32) := (ktopCode.drop 17).take 1
def kfF : List (BitVec 32) := (ktopCode.drop 18).take 2
def khA : List (BitVec 32) := (ktopCode.drop 20).take 8

theorem codeAt_kg27 : CodeAt image (pcOf 144) kg27 := by decide +kernel
theorem codeAt_kg159 : CodeAt image (pcOf 159) kg159 := by decide +kernel
theorem codeAt_kg161 : CodeAt image (pcOf 161) kg161 := by decide +kernel
theorem codeAt_kg188 : CodeAt image (pcOf 188) kg188 := by decide +kernel
theorem codeAt_kg192 : CodeAt image (pcOf 192) kg192 := by decide +kernel
theorem codeAt_kg612 : CodeAt image (pcOf 612) kg612 := by decide +kernel
theorem codeAt_kgCG1 : CodeAt image (pcOf 618) kgCG1 := by decide +kernel
theorem codeAt_kg623 : CodeAt image (pcOf 623) [115] := by decide +kernel
theorem codeAt_kgCG2 : CodeAt image (pcOf 624) kgCG2 := by decide +kernel
theorem codeAt_kgCG3 : CodeAt image (pcOf 639) kgCG3 := by decide +kernel
theorem codeAt_kgH0 : CodeAt image (pcOf 642) kgH0 := by decide +kernel
theorem codeAt_kgHK : CodeAt image (pcOf 647) kgHK := by decide +kernel
theorem codeAt_kgHB1 : CodeAt image (pcOf 653) kgHB1 := by decide +kernel
theorem codeAt_kgHB2 : CodeAt image (pcOf 655) kgHB2 := by decide +kernel
theorem codeAt_kgHB3 : CodeAt image (pcOf 658) kgHB3 := by decide +kernel
theorem codeAt_kgHF : CodeAt image (pcOf 667) kgHF := by decide +kernel
theorem codeAt_kgHE : CodeAt image (pcOf 679) kgHE := by decide +kernel
theorem codeAt_kgC1 : CodeAt image (pcOf 684) kgC1 := by decide +kernel
theorem codeAt_kgC2 : CodeAt image (pcOf 687) kgC2 := by decide +kernel
theorem codeAt_kgC3 : CodeAt image (pcOf 770) kgC3 := by decide +kernel
theorem codeAt_kgC4 : CodeAt image (pcOf 772) kgC4 := by decide +kernel
theorem codeAt_kgC5 : CodeAt image (pcOf 775) kgC5 := by decide +kernel
theorem codeAt_kfA : CodeAt image (pcOf 1149) kfA := by decide +kernel
theorem codeAt_kfB : CodeAt image (pcOf 1151) kfB := by decide +kernel
theorem codeAt_kfD : CodeAt image (pcOf 1161) kfD := by decide +kernel
theorem codeAt_kfE : CodeAt image (pcOf 1166) kfE := by decide +kernel
theorem codeAt_kfF : CodeAt image (pcOf 1167) kfF := by decide +kernel
theorem codeAt_khA : CodeAt image (pcOf 1169) khA := by decide +kernel

sym_block bk27 := symRun { noAlias := true } kg27 (pcOf 144) 100
sym_block bk159 := symRun { noAlias := true } kg159 (pcOf 159) 100
sym_block bk161 := symRun { noAlias := true } kg161 (pcOf 161) 100
sym_block bk188 := symRun { noAlias := true } kg188 (pcOf 188) 100
sym_block bk192 := symRun { noAlias := true } kg192 (pcOf 192) 100
sym_block bk612 := symRun { noAlias := true } kg612 (pcOf 612) 100
sym_block bkCG1 := symRun { noAlias := true } kgCG1 (pcOf 618) 100
sym_block bkCG2 := symRun { noAlias := true } kgCG2 (pcOf 624) 100
sym_block bkCG3 := symRun { noAlias := true } kgCG3 (pcOf 639) 100
sym_block bkH0 := symRun { noAlias := true } kgH0 (pcOf 642) 100
sym_block bkHK := symRun { noAlias := true } kgHK (pcOf 647) 100
sym_block bkHB1 := symRun { noAlias := true } kgHB1 (pcOf 653) 100
sym_block bkHB2 := symRun { noAlias := true } kgHB2 (pcOf 655) 100
sym_block bkHB3 := symRun { noAlias := true } kgHB3 (pcOf 658) 100
sym_block bkHF := symRun { noAlias := true } kgHF (pcOf 667) 100
sym_block bkHE := symRun { noAlias := true } kgHE (pcOf 679) 100
sym_block bkC1 := symRun { noAlias := true } kgC1 (pcOf 684) 100
sym_block bkC2 := symRun { noAlias := true } kgC2 (pcOf 687) 100
sym_block bkC3 := symRun { noAlias := true } kgC3 (pcOf 770) 100
sym_block bkC4 := symRun { noAlias := true } kgC4 (pcOf 772) 100
sym_block bkC5 := symRun { noAlias := true } kgC5 (pcOf 775) 100
sym_block bkfA := symRun { noAlias := true } kfA (pcOf 1149) 100
sym_block bkfB := symRun { noAlias := true } kfB (pcOf 1151) 100
sym_block bkfD := symRun { noAlias := true } kfD (pcOf 1161) 100
sym_block bkfE := symRun { noAlias := true } kfE (pcOf 1166) 100
sym_block bkfF := symRun { noAlias := true } kfF (pcOf 1167) 100
sym_block bkhA := symRun { noAlias := true } khA (pcOf 1169) 100

theorem kshl (x : Word) (k : Nat) (hk : k < 64) : BinOp.eval .sll x (BitVec.ofNat 64 k) = x <<< k := by
  simp only [BinOp.eval, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt hk]
theorem kshr (x : Word) (k : Nat) (hk : k < 64) : BinOp.eval .srl x (BitVec.ofNat 64 k) = x >>> k := by
  simp only [BinOp.eval, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt hk]

/-- Leaf entry (144..157): leaf header words, `gp = ra`, then `jal ra, COEFGEN`. -/
theorem kg27_spec (s : MachineState) (hpc : s.pc = pcOf 144) (lay leaf : Nat) (hlay : lay < 256)
    (hleaf : leaf < 2 ^ 32) (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) :
    ∃ t, Steps image s 14 14 t ∧ t.pc = pcOf 612 ∧ t.getReg .x1 = pcOf 158 ∧ t.getReg .x3 = s.getReg .x1 ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + 16)) = T3.hyperWord lay leaf ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + 24)) = 0 ∧
      RegsExcept s t [.x1, .x3, .x6, .x28, .x30] ∧
      Frame s t (fun A => A = LEAFPK + 16 ∨ A = LEAFPK + 24) := by
  refine ⟨_, symRun_sound bk27 codeAt_kg27 s hpc
    (by simp [bk27.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [bk27.res, Result.toState_pc, E.eval]
  · simp [bk27.res, rv_simp]
  · simp [bk27.res, rv_simp]
  · simp only [Result.toState_getMem, bk27.res, LEAFPK]
    t3n [h8, h18]
    rw [show (513#64) = BitVec.ofNat 64 513 from rfl,
      ofNat_or_disjoint 513 (leaf * 65536) 16 (by decide) (by omega),
      ofNat_or_disjoint' _ (lay * 281474976710656) 48 (by omega) (by omega),
      show (13907115649320091648#64) = BitVec.ofNat 64 (193 * 2 ^ 56) from rfl,
      ofNat_or_disjoint' _ (193 * 2 ^ 56) 56 (by omega) (by omega)]
    unfold T3.hyperWord
    congr 1
    rw [Nat.mod_eq_of_lt hleaf, Nat.mod_eq_of_lt hlay]
    omega
  · simp only [Result.toState_getMem, bk27.res, LEAFPK]
    t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [bk27.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [LEAFPK] at hn
    simp only [Result.toState_getMem, bk27.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega)]

/-- 159..160: `addi a3, s3, 1; jal ra, HORN`. -/
theorem kg159_spec (s : MachineState) (hpc : s.pc = pcOf 159) (i : Nat)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf 642 ∧ t.getReg .x1 = pcOf 161 ∧
      t.getReg .x13 = BitVec.ofNat 64 (i + 1) ∧ RegsExcept s t [.x1, .x13] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bk159 codeAt_kg159 s hpc (by simp [bk159.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [bk159.res, Result.toState_pc, E.eval]
  · simp [bk159.res, rv_simp]
  · t3n [bk159.res, h19]
  · intro r hr; simp at hr; cases r <;> simp_all [bk159.res, rv_simp] <;> rfl
  · intro A _ _; simp [bk159.res, rv_simp]

/-- 161: `j 188`. -/
theorem kg161_spec (s : MachineState) (hpc : s.pc = pcOf 161) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 188 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bk161 codeAt_kg161 s hpc (by simp [bk161.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [bk161.res, Result.toState_pc, E.eval]
  · intro r hr; cases r <;> simp_all [bk161.res, rv_simp] <;> rfl
  · intro A _ _; simp [bk161.res, rv_simp]

/-- 188: `add t3, s6, s3` (digit address). -/
theorem kg188_spec (s : MachineState) (hpc : s.pc = pcOf 188) (i digp : Nat)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) (h22 : s.getReg .x22 = BitVec.ofNat 64 digp) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 189 ∧ t.getReg .x28 = BitVec.ofNat 64 (digp + i) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bk188 codeAt_kg188 s hpc (by simp [bk188.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [bk188.res, Result.toState_pc, E.eval]
  · t3n [bk188.res, h19, h22]
  · intro r hr; simp at hr; cases r <;> simp_all [bk188.res, rv_simp] <;> rfl
  · intro A _ _; simp [bk188.res, rv_simp]

/-- 192: `j CAP`. -/
theorem kg192_spec (s : MachineState) (hpc : s.pc = pcOf 192) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 684 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bk192 codeAt_kg192 s hpc (by simp [bk192.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [bk192.res, Result.toState_pc, E.eval]
  · intro r hr; cases r <;> simp_all [bk192.res, rv_simp] <;> rfl
  · intro A _ _; simp [bk192.res, rv_simp]

/-- Steps of CAP (campaign T51): 3 (`i < 27`), 7 (`i < 48`), 10 (`i < 50`), 12 (chain 50). -/
def capK (i : Nat) : Nat := if i < 27 then 3 else if i < 48 then 7 else if i < 50 then 10 else 12
/-- CAP (684..688, 770..776): `s5 = maxDigit 0 i`, then 193. -/
theorem kgCap_spec (s : MachineState) (hpc : s.pc = pcOf 684) (i : Nat) (hi : i < 2 ^ 63)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s (capK i) (capK i) t ∧ t.pc = pcOf 193 ∧
      t.getReg .x21 = BitVec.ofNat 64 (maxDigit 0 i) ∧ RegsExcept s t [.x21, .x30] ∧
      Frame s t (fun _ => False) := by
  obtain ⟨t1, st1, t1pc, t1x21, t1r, t1f⟩ : ∃ t, Steps image s 3 3 t ∧
      t.pc = (if i < 27 then pcOf 193 else pcOf 687) ∧ t.getReg .x21 = BitVec.ofNat 64 5 ∧
      RegsExcept s t [.x21, .x30] ∧ Frame s t (fun _ => False) := by
    refine ⟨_, symRun_sound bkC1 codeAt_kgC1 s hpc (by simp [bkC1.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, bkC1.res, E.eval, CmpOp.eval, h19,
        ofNat_slt i 27 hi (by norm_num)]
      by_cases h : i < 27 <;> simp [h]
    · simp [bkC1.res, rv_simp]
    · intro r hr; simp at hr; cases r <;> simp_all [bkC1.res, rv_simp] <;> rfl
    · intro A _ _; simp [bkC1.res, rv_simp]
  by_cases h27 : i < 27
  · rw [if_pos h27] at t1pc
    refine ⟨t1, by simpa [capK, h27] using st1, t1pc, ?_, t1r, t1f⟩
    rw [t1x21]; simp [maxDigit, h27]
  rw [if_neg h27] at t1pc
  obtain ⟨t2, st2, t2pc, t2x21, t2r, t2f⟩ : ∃ t, Steps image t1 2 2 t ∧ t.pc = pcOf 770 ∧
      t.getReg .x21 = BitVec.ofNat 64 4 ∧ RegsExcept t1 t [.x21] ∧ Frame t1 t (fun _ => False) := by
    refine ⟨_, symRun_sound bkC2 codeAt_kgC2 t1 t1pc (by simp [bkC2.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [bkC2.res, Result.toState_pc, E.eval]
    · simp [bkC2.res, rv_simp]
    · intro r hr; simp at hr; cases r <;> simp_all [bkC2.res, rv_simp] <;> rfl
    · intro A _ _; simp [bkC2.res, rv_simp]
  have r19 : t2.getReg .x19 = BitVec.ofNat 64 i := by rw [t2r.get (by simp), t1r.get (by simp)]; exact h19
  obtain ⟨t3, st3, t3pc, t3r, t3f⟩ : ∃ t, Steps image t2 2 2 t ∧
      t.pc = (if i < 48 then pcOf 193 else pcOf 772) ∧ RegsExcept t2 t [.x30] ∧ Frame t2 t (fun _ => False) := by
    refine ⟨_, symRun_sound bkC3 codeAt_kgC3 t2 t2pc (by simp [bkC3.res, rv_simp]), ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, bkC3.res, E.eval, CmpOp.eval, r19,
        ofNat_slt i 48 hi (by norm_num)]
      by_cases h : i < 48 <;> simp [h]
    · intro r hr; simp at hr; cases r <;> simp_all [bkC3.res, rv_simp] <;> rfl
    · intro A _ _; simp [bkC3.res, rv_simp]
  have r12 : RegsExcept s t3 ([.x21, .x30] ++ [.x21] ++ [.x30]) := (t1r.trans t2r).trans t3r
  have f12 : Frame s t3 (fun _ => False) := ((t1f.trans t2f).trans t3f).mono (fun _ _ h => by simp_all)
  by_cases h48 : i < 48
  · rw [if_pos h48] at t3pc
    refine ⟨t3, by simpa [capK, h27, h48] using (st1.trans st2).trans st3, t3pc, ?_, r12.mono (by simp), f12⟩
    rw [t3r.get (by simp), t2x21]; simp [maxDigit, h27, h48]
  rw [if_neg h48] at t3pc
  have r19' : t3.getReg .x19 = BitVec.ofNat 64 i := by rw [t3r.get (by simp)]; exact r19
  obtain ⟨t4, st4, t4pc, t4x21, t4r, t4f⟩ : ∃ t, Steps image t3 3 3 t ∧
      t.pc = (if i < 50 then pcOf 193 else pcOf 775) ∧ t.getReg .x21 = BitVec.ofNat 64 6 ∧
      RegsExcept t3 t [.x21, .x30] ∧ Frame t3 t (fun _ => False) := by
    refine ⟨_, symRun_sound bkC4 codeAt_kgC4 t3 t3pc (by simp [bkC4.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, bkC4.res, E.eval, CmpOp.eval, r19',
        ofNat_slt i 50 hi (by norm_num)]
      by_cases h : i < 50 <;> simp [h]
    · simp [bkC4.res, rv_simp]
    · intro r hr; simp at hr; cases r <;> simp_all [bkC4.res, rv_simp] <;> rfl
    · intro A _ _; simp [bkC4.res, rv_simp]
  have r14 : RegsExcept s t4 ([.x21, .x30] ++ [.x21] ++ [.x30] ++ [.x21, .x30]) := r12.trans t4r
  have f14 : Frame s t4 (fun _ => False) := (f12.trans t4f).mono (fun _ _ h => by simp_all)
  by_cases h50 : i < 50
  · rw [if_pos h50] at t4pc
    refine ⟨t4, by simpa [capK, h27, h48, h50] using ((st1.trans st2).trans st3).trans st4, t4pc, ?_,
      r14.mono (by simp), f14⟩
    rw [t4x21]; simp [maxDigit, h27, h48, h50]
  rw [if_neg h50] at t4pc
  obtain ⟨t5, st5, t5pc, t5x21, t5r, t5f⟩ : ∃ t, Steps image t4 2 2 t ∧ t.pc = pcOf 193 ∧
      t.getReg .x21 = BitVec.ofNat 64 5 ∧ RegsExcept t4 t [.x21] ∧ Frame t4 t (fun _ => False) := by
    refine ⟨_, symRun_sound bkC5 codeAt_kgC5 t4 t4pc (by simp [bkC5.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [bkC5.res, Result.toState_pc, E.eval]
    · simp [bkC5.res, rv_simp]
    · intro r hr; simp at hr; cases r <;> simp_all [bkC5.res, rv_simp] <;> rfl
    · intro A _ _; simp [bkC5.res, rv_simp]
  refine ⟨t5, by simpa [capK, h27, h48, h50] using (((st1.trans st2).trans st3).trans st4).trans st5, t5pc, ?_,
    (r14.trans t5r).mono (by simp), (f14.trans t5f).mono (fun _ _ h => by simp_all)⟩
  rw [t5x21]; simp [maxDigit, h27, h48, h50]

/-! ## COEFGEN blocks -/
/-! ## img-v6 KTOP / KHORN blocks (1149..1176) -/
/-- 612 (img-v6): `jal 1149` (KTOP). -/
theorem kg612_spec (s : MachineState) (hpc : s.pc = pcOf 612) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 1149 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bk612 codeAt_kg612 s hpc (by simp [bk612.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [bk612.res, Result.toState_pc, E.eval]
  · intro r hr; cases r <;> simp_all [bk612.res, rv_simp] <;> rfl
  · intro A _ _; simp [bk612.res, rv_simp]

theorem kand3 (q : Nat) : BitVec.ofNat 64 q &&& 3#64 = BitVec.ofNat 64 (q % 4) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show 3 % 2 ^ 64 = 2 ^ 2 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- 1149..1150: `t5 = s2 & 3; bne t5, zero, 1167`. -/
theorem kfA_spec (s : MachineState) (hpc : s.pc = pcOf 1149) (leaf : Nat)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if leaf % 4 = 0 then pcOf 1151 else pcOf 1167) ∧
      RegsExcept s t [.x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bkfA codeAt_kfA s hpc (by simp [bkfA.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, bkfA.res, E.eval, CmpOp.eval, RegFile.get, h18, BinOp.eval, kand3]
    by_cases h : leaf % 4 = 0
    · simp [h]
    · have : BitVec.ofNat 64 (leaf % 4) ≠ 0#64 := by
        rw [Ne, show (0#64) = BitVec.ofNat 64 0 from rfl, ofNat_inj (by omega) (by norm_num)]; exact h
      simp [h, this]
  · intro r hr; simp at hr; cases r <;> simp_all [bkfA.res, rv_simp] <;> rfl
  · intro A _ _; simp [bkfA.res, rv_simp]

theorem kshr2 (q : Nat) (hq : q < 2 ^ 64) :
    BitVec.ofNat 64 q >>> (2 : Nat) &&& 1#64 = BitVec.ofNat 64 (q / 4 % 2) := by
  rw [ofNat_shr q 2 hq, ofNat_and1]; rfl
theorem kfB_x14 (leaf : Nat) (hleaf : leaf < 2 ^ 32) :
    (BitVec.ofNat 64 leaf >>> (2 : Nat) * 31#64 + BitVec.ofNat 64 (leaf / 4 % 2)) >>> (1 : Nat) <<< (32 : Nat) |||
      1#64 = BitVec.ofNat 64 (1 + 2 ^ 32 * (31 * (leaf / 4) / 2 + leaf / 4 % 2)) := by
  have e1 : BitVec.ofNat 64 leaf >>> (2 : Nat) = BitVec.ofNat 64 (leaf / 4) := by
    rw [ofNat_shr leaf 2 (by omega)]; rfl
  have e2 : BitVec.ofNat 64 (leaf / 4) * 31#64 = BitVec.ofNat 64 (leaf / 4 * 31) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul]
  rw [e1, e2, ofNat_add_ofNat, ofNat_shr _ 1 (by omega), ofNat_shl, show (1#64) = BitVec.ofNat 64 1 from rfl,
    ofNat_or_disjoint 1 ((leaf / 4 * 31 + leaf / 4 % 2) / 2 ^ 1 * 2 ^ 32) 32 (by norm_num) (by omega)]
  congr 1; omega
/-- 1151..1160: `s8 = KCOEF`, `f = s2 >> 2`, `t4 = f & 1`, `a4 = ((31 f + t4) >> 1) << 32 | 1`, `beq t4, zero, 1166`
(the `mul` costs 4 cycles). -/
theorem kfB_spec (s : MachineState) (hpc : s.pc = pcOf 1151) (leaf : Nat) (hleaf : leaf < 2 ^ 32)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) :
    ∃ t, Steps image s 10 13 t ∧ t.pc = (if leaf / 4 % 2 = 0 then pcOf 1166 else pcOf 1161) ∧
      t.getReg .x14 = BitVec.ofNat 64 (1 + 2 ^ 32 * (31 * (leaf / 4) / 2 + leaf / 4 % 2)) ∧
      t.getReg .x24 = BitVec.ofNat 64 KCOEF ∧ t.getReg .x29 = BitVec.ofNat 64 (leaf / 4 % 2) ∧
      RegsExcept s t [.x14, .x24, .x29, .x30] ∧ Frame s t (fun _ => False) := by
  have h2 : (2#64).toNat % 64 = 2 := by decide
  have h1 : (1#64).toNat % 64 = 1 := by decide
  have h32 : (32#64).toNat % 64 = 32 := by decide
  refine ⟨_, symRun_sound bkfB codeAt_kfB s hpc (by simp [bkfB.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, bkfB.res, E.eval, CmpOp.eval, RegFile.get, h18, BinOp.eval, h2,
      kshr2 leaf (by omega)]
    by_cases h : leaf / 4 % 2 = 0
    · simp [h]
    · have : BitVec.ofNat 64 (leaf / 4 % 2) ≠ 0#64 := by
        rw [Ne, show (0#64) = BitVec.ofNat 64 0 from rfl, ofNat_inj (by omega) (by norm_num)]; exact h
      simp [h, this]
  · simp only [Result.toState_getReg, bkfB.res, RegFile.get, E.eval, h18, BinOp.eval, h2, h1, h32,
      kshr2 leaf (by omega)]
    exact kfB_x14 leaf hleaf
  · simp [bkfB.res, rv_simp]
  · simp only [Result.toState_getReg, bkfB.res, RegFile.get, E.eval, h18, BinOp.eval, h2,
      kshr2 leaf (by omega)]
  · intro r hr; simp at hr; cases r <;> simp_all [bkfB.res, rv_simp] <;> rfl
  · intro A _ _; simp [bkfB.res, rv_simp]

/-- 1161..1165 (odd family): copy the carry slot 31 to slot 0, `s8 += 16`. -/
theorem kfD_spec (s : MachineState) (hpc : s.pc = pcOf 1161) (h24 : s.getReg .x24 = BitVec.ofNat 64 KCOEF) :
    ∃ t, Steps image s 5 5 t ∧ t.pc = pcOf 1166 ∧
      t.getMem (BitVec.ofNat 64 KCOEF) = s.getMem (BitVec.ofNat 64 (KCOEF + 496)) ∧
      t.getMem (BitVec.ofNat 64 (KCOEF + 8)) = s.getMem (BitVec.ofNat 64 (KCOEF + 504)) ∧
      t.getReg .x24 = BitVec.ofNat 64 (KCOEF + 16) ∧
      RegsExcept s t [.x4, .x24] ∧ Frame s t (fun A => A = KCOEF ∨ A = KCOEF + 8) := by
  have hobl : Oblig.all s bkfD.res.st.obl := by
    simp only [bkfD.res]
    t3n [h24]
    simp only [KCOEF]
    and_intros <;> first | trivial | omega
  refine ⟨_, symRun_sound bkfD codeAt_kfD s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [bkfD.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getMem, bkfD.res]
    t3n [h24]
    all_goals (try simp only [KCOEF])
    all_goals (repeat rw [if_neg (by omega)])
  · simp only [Result.toState_getMem, bkfD.res]
    t3n [h24]
    all_goals (try simp only [KCOEF])
    all_goals (repeat rw [if_neg (by omega)])
  · t3n [bkfD.res, h24]
  · intro r hr; simp at hr; cases r <;> simp_all [bkfD.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem, bkfD.res]
    t3n [h24]
    simp only [KCOEF] at hn ⊢
    rw [if_neg (by omega), if_neg (by omega)]

/-- 1166: `jal 618` (the pair loop). -/
theorem kfE_spec (s : MachineState) (hpc : s.pc = pcOf 1166) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 618 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bkfE codeAt_kfE s hpc (by simp [bkfE.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [bkfE.res, Result.toState_pc, E.eval]
  · intro r hr; cases r <;> simp_all [bkfE.res, rv_simp] <;> rfl
  · intro A _ _; simp [bkfE.res, rv_simp]

/-- 1167..1168 (not a family start): `s3 = 0; ret`. -/
theorem kfF_spec (s : MachineState) (hpc : s.pc = pcOf 1167) (ret : Nat) (h1 : s.getReg .x1 = pcOf ret) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf ret ∧ t.getReg .x19 = BitVec.ofNat 64 0 ∧
      RegsExcept s t [.x19] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bkfF codeAt_kfF s hpc (by simp [bkfF.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, bkfF.res, rv_simp, h1, pcOf_and_max]
  · simp [bkfF.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [bkfF.res, rv_simp] <;> rfl
  · intro A _ _; simp [bkfF.res, rv_simp]

/-- 1169..1176 (KHORN): point `a3 += (s2 & 3) << 6`, `a4 = a5 = 0`, `a1 = KCOEF`, `a0 = KCOEF + 16 · 31`,
`jal 647`. -/
theorem khA_spec (s : MachineState) (hpc : s.pc = pcOf 1169) (leaf d : Nat) (hd : d < 2 ^ 32)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) (h13 : s.getReg .x13 = BitVec.ofNat 64 d) :
    ∃ t, Steps image s 8 8 t ∧ t.pc = pcOf 647 ∧ t.getReg .x13 = BitVec.ofNat 64 (d + leaf % 4 * 64) ∧
      t.getReg .x10 = BitVec.ofNat 64 (KCOEF + 16 * 31) ∧ t.getReg .x11 = BitVec.ofNat 64 KCOEF ∧
      t.getReg .x14 = BitVec.ofNat 64 0 ∧ t.getReg .x15 = BitVec.ofNat 64 0 ∧
      RegsExcept s t [.x10, .x11, .x13, .x14, .x15, .x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bkhA codeAt_khA s hpc (by simp [bkhA.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · simp [bkhA.res, Result.toState_pc, E.eval]
  · have h6 : (6#64).toNat % 64 = 6 := by decide
    simp only [Result.toState_getReg, bkhA.res, RegFile.get, E.eval, h18, h13, BinOp.eval, kand3,
      ofNat_shl, ofNat_add_ofNat, h6]
    rfl
  all_goals first
    | (simp [bkhA.res, rv_simp] <;> rfl)
    | (intro r hr; simp at hr; cases r <;> simp_all [bkhA.res, rv_simp] <;> rfl)
    | (intro A _ _; simp [bkhA.res, rv_simp])

/-- 642 (img-v6): `jal 1169` (KHORN). -/
theorem kgH0_spec (s : MachineState) (hpc : s.pc = pcOf 642) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 1169 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bkH0 codeAt_kgH0 s hpc (by simp [bkH0.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [bkH0.res, Result.toState_pc, E.eval]
  · intro r hr; cases r <;> simp_all [bkH0.res, rv_simp] <;> rfl
  · intro A _ _; simp [bkH0.res, rv_simp]

/-- 618..622: private-pair header (low word `a4`, high word 0) and the hash arguments. -/
theorem kgCG1_spec (s : MachineState) (hpc : s.pc = pcOf 618) :
    ∃ t, Steps image s 5 5 t ∧ t.pc = pcOf 623 ∧ t.getReg .x10 = BitVec.ofNat 64 PRIV ∧
      t.getReg .x11 = BitVec.ofNat 64 64 ∧ t.getReg .x12 = BitVec.ofNat 64 SEEDS ∧
      t.getMem (BitVec.ofNat 64 (PRIV + 16)) = s.getReg .x14 ∧ t.getMem (BitVec.ofNat 64 (PRIV + 24)) = 0 ∧
      RegsExcept s t [.x10, .x11, .x12] ∧ Frame s t (fun A => A = PRIV + 16 ∨ A = PRIV + 24) := by
  refine ⟨_, symRun_sound bkCG1 codeAt_kgCG1 s hpc (by simp [bkCG1.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · simp [bkCG1.res, Result.toState_pc, E.eval]
  · simp [bkCG1.res, rv_simp]
  · simp [bkCG1.res, rv_simp]
  · simp [bkCG1.res, rv_simp]
  · simp only [Result.toState_getMem, bkCG1.res, PRIV]; t3n []
  · simp only [Result.toState_getMem, bkCG1.res, PRIV]; t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [bkCG1.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [PRIV] at hn
    simp only [Result.toState_getMem, bkCG1.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega)]

theorem fetch_kg623 (s : MachineState) (hpc : s.pc = pcOf 623) : fetch image s = some (.base .ECALL) :=
  (codeAt_kg623.fetch s hpc).trans rfl

/-- 624..638: copy the 32-byte answer to `KCOEF + a`, next pair, `bne t4, 16` (campaign T51: count 16). -/
theorem kgCG2_spec (s : MachineState) (hpc : s.pc = pcOf 624) (j p a : Nat) (hj : j < 16) (ha : a + 32 ≤ 640) (ha8 : a % 8 = 0)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 PRIV) (h24 : s.getReg .x24 = BitVec.ofNat 64 (KCOEF + a))
    (h29 : s.getReg .x29 = BitVec.ofNat 64 j) (h14 : s.getReg .x14 = BitVec.ofNat 64 p) :
    ∃ t, Steps image s 15 15 t ∧ t.pc = (if j + 1 < 16 then pcOf 618 else pcOf 639) ∧
      t.getReg .x14 = BitVec.ofNat 64 (p + 2 ^ 32) ∧ t.getReg .x24 = BitVec.ofNat 64 (KCOEF + a + 32) ∧
      t.getReg .x29 = BitVec.ofNat 64 (j + 1) ∧
      (∀ k < 4, t.getMem (BitVec.ofNat 64 (KCOEF + a + 8 * k)) = s.getMem (BitVec.ofNat 64 (SEEDS + 8 * k))) ∧
      RegsExcept s t [.x4, .x14, .x24, .x29, .x30] ∧
      Frame s t (fun A => KCOEF + a ≤ A ∧ A < KCOEF + a + 32) := by
  have hobl : Oblig.all s bkCG2.res.st.obl := by
    simp only [bkCG2.res]
    t3n [h10, h24]
    simp only [PRIV, KCOEF]
    and_intros <;> first | trivial | omega
  refine ⟨_, symRun_sound bkCG2 codeAt_kgCG2 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, bkCG2.res, E.eval, CmpOp.eval, h29]
    by_cases h : j + 1 < 16
    · rw [if_pos h]
      simp only [BinOp.eval, ofNat_add_ofNat, bne_iff_ne, ne_eq, ofNat_inj (show j + 1 < 2 ^ 64 by omega)
        (show 16 < 2 ^ 64 by norm_num)]
      rw [if_pos (by omega)]
    · rw [if_neg h]
      simp only [BinOp.eval, ofNat_add_ofNat, bne_iff_ne, ne_eq, ofNat_inj (show j + 1 < 2 ^ 64 by omega)
        (show 16 < 2 ^ 64 by norm_num)]
      rw [if_neg (by omega)]
  · t3n [bkCG2.res, h14]
  · t3n [bkCG2.res, h24] <;> (try simp only [KCOEF]) <;> omega
  · t3n [bkCG2.res, h29]
  · intro k hk
    simp only [Result.toState_getMem, bkCG2.res]
    t3n [h10, h24]
    interval_cases k <;> split_ifs <;> first | omega | simp only [PRIV, SEEDS]
  · intro r hr; simp at hr; cases r <;> simp_all [bkCG2.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem, bkCG2.res]
    t3n [h24]
    simp only [KCOEF] at hn ⊢
    repeat rw [if_neg (by omega)]

/-- 639..640: `s3 = 0; ret`. -/
theorem kgCG3_spec (s : MachineState) (hpc : s.pc = pcOf 639) (ret : Nat) (h1 : s.getReg .x1 = pcOf ret) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf ret ∧ t.getReg .x19 = BitVec.ofNat 64 0 ∧
      RegsExcept s t [.x19] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bkCG3 codeAt_kgCG3 s hpc (by simp [bkCG3.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, bkCG3.res, rv_simp, h1, pcOf_and_max]
  · simp [bkCG3.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [bkCG3.res, rv_simp] <;> rfl
  · intro A _ _; simp [bkCG3.res, rv_simp]

/-! ## HORN blocks -/
/-- 647..652 (HK): next coefficient address, product limbs and `tp` cleared, `t4 = a3`. -/
theorem kgHK_spec (s : MachineState) (hpc : s.pc = pcOf 647) (m : Nat) (hm : 1 ≤ m) (hm' : m ≤ 40)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 (KCOEF + 16 * m)) :
    ∃ t, Steps image s 6 6 t ∧ t.pc = pcOf 653 ∧ t.getReg .x10 = BitVec.ofNat 64 (KCOEF + 16 * (m - 1)) ∧
      t.getReg .x4 = BitVec.ofNat 64 0 ∧ t.getReg .x12 = BitVec.ofNat 64 0 ∧ t.getReg .x16 = BitVec.ofNat 64 0 ∧
      t.getReg .x24 = BitVec.ofNat 64 0 ∧ t.getReg .x29 = s.getReg .x13 ∧
      RegsExcept s t [.x4, .x10, .x12, .x16, .x24, .x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bkHK codeAt_kgHK s hpc (by simp [bkHK.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · simp [bkHK.res, Result.toState_pc, E.eval]
  · t3n [bkHK.res, h10]; simp only [KCOEF]; omega
  all_goals first
    | (simp [bkHK.res, rv_simp] <;> rfl)
    | (intro r hr; simp at hr; cases r <;> simp_all [bkHK.res, rv_simp] <;> rfl)
    | (intro A _ _; simp [bkHK.res, rv_simp])

/-- 653..654 (HB, test): `t5 = t4 & 1; beq t5, zero`. -/
theorem kgHB1_spec (s : MachineState) (hpc : s.pc = pcOf 653) :
    ∃ t, Steps image s 2 2 t ∧
      t.pc = (if (s.getReg .x29 &&& BitVec.ofNat 64 1 == BitVec.ofNat 64 0) = true then pcOf 658 else pcOf 655) ∧
      RegsExcept s t [.x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bkHB1 codeAt_kgHB1 s hpc (by simp [bkHB1.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, bkHB1.res, E.eval, CmpOp.eval, RegFile.get, BinOp.eval]; rfl
  · intro r hr; simp at hr; cases r <;> simp_all [bkHB1.res, rv_simp] <;> rfl
  · intro A _ _; simp [bkHB1.res, rv_simp]

/-- 655..657 (HB, add): `a6 ^= a4; s8 ^= a5; tp ^= a2`. -/
theorem kgHB2_spec (s : MachineState) (hpc : s.pc = pcOf 655) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf 658 ∧ t.getReg .x16 = s.getReg .x16 ^^^ s.getReg .x14 ∧
      t.getReg .x24 = s.getReg .x24 ^^^ s.getReg .x15 ∧ t.getReg .x4 = s.getReg .x4 ^^^ s.getReg .x12 ∧
      RegsExcept s t [.x4, .x16, .x24] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bkHB2 codeAt_kgHB2 s hpc (by simp [bkHB2.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [bkHB2.res, Result.toState_pc, E.eval]
  all_goals first
    | (simp only [Result.toState_getReg, bkHB2.res, RegFile.get, E.eval, BinOp.eval]; done)
    | (intro r hr; simp at hr; cases r <;> simp_all [bkHB2.res, rv_simp] <;> rfl)
    | (intro A _ _; simp [bkHB2.res, rv_simp])

/-- 658..666 (HB, shift): shift the multiplicand limbs `(a4, a5, a2)` and `t4`; loop while `t4 >> 1 ≠ 0`. -/
theorem kgHB3_spec (s : MachineState) (hpc : s.pc = pcOf 658) :
    ∃ t, Steps image s 9 9 t ∧
      t.pc = (if (s.getReg .x29 >>> 1 != BitVec.ofNat 64 0) = true then pcOf 653 else pcOf 667) ∧
      t.getReg .x14 = s.getReg .x14 <<< 1 ∧ t.getReg .x15 = (s.getReg .x15 <<< 1) ||| (s.getReg .x14 >>> 63) ∧
      t.getReg .x12 = (s.getReg .x12 <<< 1) ||| (s.getReg .x15 >>> 63) ∧ t.getReg .x29 = s.getReg .x29 >>> 1 ∧
      RegsExcept s t [.x12, .x14, .x15, .x29, .x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bkHB3 codeAt_kgHB3 s hpc (by simp [bkHB3.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, bkHB3.res, E.eval, CmpOp.eval, RegFile.get,
      kshr _ 1 (by norm_num)]
  all_goals first
    | (simp only [Result.toState_getReg, bkHB3.res, RegFile.get, E.eval, BinOp.eval.eq_4,
        kshl _ 1 (by norm_num), kshr _ 1 (by norm_num), kshr _ 63 (by norm_num)]; done)
    | (intro r hr; simp at hr; cases r <;> simp_all [bkHB3.res, rv_simp] <;> rfl)
    | (intro A _ _; simp [bkHB3.res, rv_simp])

/-- 667..678 (HF): fold `tp` into `a6` with 0x87, add the coefficient at `a0`; loop while `a0 ≠ a1`. -/
theorem kgHF_spec (s : MachineState) (hpc : s.pc = pcOf 667) {A : Nat} (h10 : s.getReg .x10 = BitVec.ofNat 64 A)
    (hA : A % 8 = 0) (hA' : A + 16 ≤ 2 ^ 24) :
    ∃ t, Steps image s 12 12 t ∧
      t.pc = (if (s.getReg .x10 != s.getReg .x11) = true then pcOf 647 else pcOf 679) ∧
      t.getReg .x14 = foldLo (s.getReg .x16) (s.getReg .x4) ^^^ s.getMem (BitVec.ofNat 64 A) ∧
      t.getReg .x15 = s.getReg .x24 ^^^ s.getMem (BitVec.ofNat 64 (A + 8)) ∧
      RegsExcept s t [.x14, .x15, .x16, .x30] ∧ Frame s t (fun _ => False) := by
  have hobl : Oblig.all s bkHF.res.st.obl := by
    simp only [bkHF.res]
    t3n [h10]
    omega
  refine ⟨_, symRun_sound bkHF codeAt_kgHF s hpc hobl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, bkHF.res, E.eval, CmpOp.eval, RegFile.get]; rfl
  · simp only [Result.toState_getReg, bkHF.res, RegFile.get, E.eval, h10, foldLo,
      kshl _ 1 (by norm_num), kshl _ 2 (by norm_num), kshl _ 7 (by norm_num)]
    rfl
  · simp only [Result.toState_getReg, bkHF.res, RegFile.get, E.eval, h10, BinOp.eval, ofNat_add_ofNat]
  · intro r hr; simp at hr; cases r <;> simp_all [bkHF.res, rv_simp] <;> rfl
  · intro A _ _; simp [bkHF.res, rv_simp]

/-- 679..682 (HE): store the seed at `CHAIN + 48`, return. -/
theorem kgHE_spec (s : MachineState) (hpc : s.pc = pcOf 679) (ret : Nat) (h1 : s.getReg .x1 = pcOf ret) :
    ∃ t, Steps image s 4 4 t ∧ t.pc = pcOf ret ∧ t.getMem (BitVec.ofNat 64 (CHAIN + 48)) = s.getReg .x14 ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 56)) = s.getReg .x15 ∧ RegsExcept s t [.x30] ∧
      Frame s t (fun A => A = CHAIN + 48 ∨ A = CHAIN + 56) := by
  refine ⟨_, symRun_sound bkHE codeAt_kgHE s hpc (by simp [bkHE.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, bkHE.res, rv_simp, h1, pcOf_and_max]
  · simp only [Result.toState_getMem, bkHE.res, CHAIN]; t3n []
  · simp only [Result.toState_getMem, bkHE.res, CHAIN]; t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [bkHE.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [CHAIN] at hn
    simp only [Result.toState_getMem, bkHE.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega)]

/-! ## HORN loops -/
/-- Registers of the bit loop. -/
def khbRegs : List Reg := [.x4, .x12, .x14, .x15, .x16, .x24, .x29, .x30]

theorem kgHB_spec (s : MachineState) (hpc : s.pc = pcOf 653) (b1 b2 : Bool)
    (h1 : (s.getReg .x29 &&& BitVec.ofNat 64 1 == BitVec.ofNat 64 0) = b1)
    (h2 : (s.getReg .x29 >>> 1 != BitVec.ofNat 64 0) = b2) :
    ∃ t, Steps image s (if b1 then 11 else 14) (if b1 then 11 else 14) t ∧
      t.pc = (if b2 then pcOf 653 else pcOf 667) ∧
      t.getReg .x14 = s.getReg .x14 <<< 1 ∧ t.getReg .x15 = (s.getReg .x15 <<< 1) ||| (s.getReg .x14 >>> 63) ∧
      t.getReg .x12 = (s.getReg .x12 <<< 1) ||| (s.getReg .x15 >>> 63) ∧
      t.getReg .x16 = (if b1 then s.getReg .x16 else s.getReg .x16 ^^^ s.getReg .x14) ∧
      t.getReg .x24 = (if b1 then s.getReg .x24 else s.getReg .x24 ^^^ s.getReg .x15) ∧
      t.getReg .x4 = (if b1 then s.getReg .x4 else s.getReg .x4 ^^^ s.getReg .x12) ∧
      t.getReg .x29 = s.getReg .x29 >>> 1 ∧ RegsExcept s t khbRegs ∧ Frame s t (fun _ => False) := by
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := kgHB1_spec s hpc
  rw [h1] at t1pc
  obtain ⟨t2, st2, t2pc, t2x16, t2x24, t2x4, t2r, t2f⟩ : ∃ t2, Steps image t1 (if b1 then 0 else 3)
      (if b1 then 0 else 3) t2 ∧ t2.pc = pcOf 658 ∧
      t2.getReg .x16 = (if b1 then s.getReg .x16 else s.getReg .x16 ^^^ s.getReg .x14) ∧
      t2.getReg .x24 = (if b1 then s.getReg .x24 else s.getReg .x24 ^^^ s.getReg .x15) ∧
      t2.getReg .x4 = (if b1 then s.getReg .x4 else s.getReg .x4 ^^^ s.getReg .x12) ∧
      RegsExcept t1 t2 [.x4, .x16, .x24] ∧ Frame t1 t2 (fun _ => False) := by
    cases b1
    · simp only [Bool.false_eq_true, if_false] at t1pc ⊢
      obtain ⟨t2, st2, t2pc, a, b, c, r, f⟩ := kgHB2_spec t1 t1pc
      refine ⟨t2, st2, t2pc, ?_, ?_, ?_, r, f⟩
      · rw [a, t1r.get (by simp), t1r.get (by simp)]
      · rw [b, t1r.get (by simp), t1r.get (by simp)]
      · rw [c, t1r.get (by simp), t1r.get (by simp)]
    · simp only [if_true] at t1pc ⊢
      exact ⟨t1, Steps.refl _, t1pc, t1r.get (by simp), t1r.get (by simp), t1r.get (by simp), RegsExcept.refl _ _,
        Frame.refl _ _⟩
  obtain ⟨t3, st3, t3pc, t3x14, t3x15, t3x12, t3x29, t3r, t3f⟩ := kgHB3_spec t2 t2pc
  have e : ∀ r, r ∉ [Reg.x30, .x4, .x16, .x24] → t2.getReg r = s.getReg r := fun r hr =>
    ((t1r.trans t2r).mono (by simp)).get hr
  refine ⟨t3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ((t1r.trans t2r).trans t3r).mono (by simp [khbRegs]),
    ((t1f.trans t2f).trans t3f).mono (fun _ _ h => by simp_all)⟩
  · exact Steps.of_eq (st1.trans (st2.trans st3)) (by cases b1 <;> rfl) (by cases b1 <;> rfl)
  · rw [t3pc, e _ (by simp), h2]
  · rw [t3x14, e _ (by simp)]
  · rw [t3x15, e _ (by simp), e _ (by simp)]
  · rw [t3x12, e _ (by simp), e _ (by simp)]
  · rw [t3r.get (by simp), t2x16]
  · rw [t3r.get (by simp), t2x24]
  · rw [t3r.get (by simp), t2x4]
  · rw [t3x29, e _ (by simp)]

/-- Steps of the bit loop over the remaining bits `q` (fuel `n`): 11 per zero bit, 14 per one bit. -/
def hbCost : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, q => (if q % 2 = 0 then 11 else 14) + (if q / 2 = 0 then 0 else hbCost n (q / 2))

structure KHbSt (t0 : MachineState) (d a k : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf 653
  sh : lim3 (t.getReg .x14) (t.getReg .x15) (t.getReg .x12) = a * 2 ^ k
  pr : lim3 (t.getReg .x16) (t.getReg .x24) (t.getReg .x4) = clmulSmall a d k
  dd : t.getReg .x29 = BitVec.ofNat 64 (d / 2 ^ k)
  regs : RegsExcept t0 t khbRegs
  frame : Frame t0 t (fun _ => False)

structure KHfSt (t0 : MachineState) (d a : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf 667
  pr : lim3 (t.getReg .x16) (t.getReg .x24) (t.getReg .x4) = clmulSmall a d 10
  regs : RegsExcept t0 t khbRegs
  frame : Frame t0 t (fun _ => False)

theorem klim3_ite (b : Bool) (a0 a1 a2 x0 x1 x2 : BitVec 64) :
    lim3 (if b then a0 else a0 ^^^ x0) (if b then a1 else a1 ^^^ x1) (if b then a2 else a2 ^^^ x2) =
      if b then lim3 a0 a1 a2 else lim3 a0 a1 a2 ^^^ lim3 x0 x1 x2 := by
  cases b
  · simp only [Bool.false_eq_true, if_false]; exact lim3_xor ..
  · rfl

theorem kb1 (q : Nat) : (BitVec.ofNat 64 q &&& BitVec.ofNat 64 1 == BitVec.ofNat 64 0) = decide (q % 2 = 0) := by
  rw [show BitVec.ofNat 64 1 = 1#64 from rfl, ofNat_and1]
  have h2 : q % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rcases Nat.mod_two_eq_zero_or_one q with h | h <;> rw [h] <;> decide

theorem kb2 (q : Nat) (hq : q < 2 ^ 64) :
    (BitVec.ofNat 64 q >>> 1 != BitVec.ofNat 64 0) = decide (q / 2 ≠ 0) := by
  rw [ofNat_shr q 1 hq, pow_one]
  have h := ofNat_inj (x := q / 2) (y := 0) (by omega) (by norm_num)
  by_cases hz : q / 2 = 0
  · rw [hz]; rfl
  · simp only [bne_iff_ne, ne_eq, h, hz, not_false_eq_true, decide_true]

theorem khb_loop {t0 : MachineState} {d a : Nat} (ha : a < 2 ^ 128) (hd : d < 2 ^ 10) :
    ∀ n k, k + n = 10 → (k = 0 ∨ 2 ^ k ≤ d) → ∀ t, KHbSt t0 d a k t →
      ∃ u, Steps image t (hbCost n (d / 2 ^ k)) (hbCost n (d / 2 ^ k)) u ∧ KHfSt t0 d a u := by
  intro n
  induction n with
  | zero =>
    intro k hk hk0 t _
    exfalso
    rcases hk0 with h | h
    · omega
    · have : k = 10 := by omega
      subst this; omega
  | succ n ih =>
    intro k hk hk0 t ht
    have hk9 : k ≤ 9 := by omega
    have hp9 : 2 ^ k ≤ 2 ^ 9 := Nat.pow_le_pow_right (by norm_num) hk9
    have hdk : d / 2 ^ k < 2 ^ 64 := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    have hq2 : d / 2 ^ k / 2 = d / 2 ^ (k + 1) := by rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]
    obtain ⟨u, su, upc, u14, u15, u12, u16, u24, u4, u29, uregs, uframe⟩ :=
      kgHB_spec t ht.pc _ _ rfl rfl
    rw [ht.dd, kb1] at su u16 u24 u4
    rw [ht.dd, kb2 _ hdk] at upc
    have hlt12 : (t.getReg .x12).toNat < 2 ^ 63 := by
      have := lim3_lt (t.getReg .x14) (t.getReg .x15) (t.getReg .x12) (n := 9) (by
        rw [ht.sh, Nat.pow_add]
        exact Nat.mul_lt_mul_of_lt_of_le ha hp9 (Nat.two_pow_pos _))
      omega
    have hbit : decide (d / 2 ^ k % 2 = 0) = !(d.testBit k) := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      rcases Nat.mod_two_eq_zero_or_one (d / 2 ^ k) with h | h <;> simp [h]
    have hsh : lim3 (u.getReg .x14) (u.getReg .x15) (u.getReg .x12) = a * 2 ^ (k + 1) := by
      rw [u14, u15, u12, lim3_shl1 _ _ _ hlt12, ht.sh, Nat.pow_succ]; ring
    have hpr : lim3 (u.getReg .x16) (u.getReg .x24) (u.getReg .x4) = clmulSmall a d (k + 1) := by
      rw [u16, u24, u4, klim3_ite, hbit, ht.pr, ht.sh]
      rw [← clmul_step a d k _ rfl (d.testBit k) rfl]
      cases d.testBit k <;> rfl
    have hdd : u.getReg .x29 = BitVec.ofNat 64 (d / 2 ^ (k + 1)) := by
      rw [u29, ht.dd, ofNat_shr _ 1 hdk, pow_one, hq2]
    have hregs : RegsExcept t0 u khbRegs := (ht.regs.trans uregs).mono (by simp [khbRegs])
    have hframe : Frame t0 u (fun _ => False) := (ht.frame.trans uframe).mono (fun _ _ h => by simpa using h)
    have hcost : ∀ (c : Nat), hbCost (n + 1) (d / 2 ^ k) =
        (if decide (d / 2 ^ k % 2 = 0) = true then 11 else 14) +
          (if d / 2 ^ (k + 1) = 0 then 0 else hbCost n (d / 2 ^ (k + 1))) := by
      intro _; simp only [hbCost, decide_eq_true_eq, hq2]
    by_cases hz : d / 2 ^ (k + 1) = 0
    · have hdlt : d < 2 ^ (k + 1) := by
        by_contra hc
        have := Nat.div_pos (Nat.le_of_not_lt hc) (Nat.two_pow_pos (k + 1))
        omega
      rw [hq2, hz] at upc
      refine ⟨u, Steps.of_eq su (by rw [hcost 0, hz]; simp) (by rw [hcost 0, hz]; simp),
        ⟨by rw [upc]; rfl, ?_, hregs, hframe⟩⟩
      rw [hpr, clmulSmall_stable a hdlt 10 (by omega)]
    · have hge : 2 ^ (k + 1) ≤ d := by
        by_contra hc
        exact hz (Nat.div_eq_of_lt (Nat.lt_of_not_le hc))
      rw [hq2] at upc
      simp only [ne_eq, hz, not_false_eq_true, decide_true, if_true] at upc
      obtain ⟨v, sv, hv⟩ := ih (k + 1) (by omega) (Or.inr hge) u ⟨upc, hsh, hpr, hdd, hregs, hframe⟩
      refine ⟨v, Steps.of_eq (su.trans sv) ?_ ?_, hv⟩ <;> rw [hcost 0, if_neg hz]

/-- Steps of one Horner step (HK, bit loop, HF). -/
def hornStepK (d : Nat) : Nat := 18 + hbCost 10 d
/-- Steps (= cycles) of HORN at the point `d`. -/
def hornK (d : Nat) : Nat := 13 + 31 * hornStepK d

/-- Registers HORN may change. -/
def khornRegs : List Reg := [.x4, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x24, .x29, .x30]

structure KHkSt (s0 : MachineState) (d : Nat) (coefs : List Digest) (m : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf 647
  x13 : t.getReg .x13 = BitVec.ofNat 64 d
  x10 : t.getReg .x10 = BitVec.ofNat 64 (KCOEF + 16 * m)
  x11 : t.getReg .x11 = BitVec.ofNat 64 KCOEF
  acc : lim2 (t.getReg .x14) (t.getReg .x15) = (familyEval (coefs.drop m) d).toNat
  regs : RegsExcept s0 t khornRegs
  frame : Frame s0 t (fun _ => False)

theorem kfamilyEval_drop (coefs : List Digest) (m : Nat) (hm : m < coefs.length) (d : Nat) :
    familyEval (coefs.drop m) d = gfMulPt (familyEval (coefs.drop (m + 1)) d) d ^^^ coefs.getD m 0 := by
  rw [List.drop_eq_getElem_cons hm, ClaudeWCT.Arith.familyEval_cons, List.getD_eq_getElem _ _ hm]

theorem kcoef_limbs {s0 u : MachineState} {coefs : List Digest} (hcoef : DigsAt s0 KCOEF coefs)
    (hf : Frame s0 u (fun _ => False)) {m : Nat} (hm : m < coefs.length) (hl : coefs.length ≤ 40) :
    lim2 (u.getMem (BitVec.ofNat 64 (KCOEF + 16 * m))) (u.getMem (BitVec.ofNat 64 (KCOEF + 16 * m + 8))) =
      (coefs.getD m 0).toNat := by
  have h := hcoef m hm
  rw [hf.get (by simp only [KCOEF]; omega) id, hf.get (by simp only [KCOEF]; omega) id, h.1, h.2, lim2_toNat]

theorem lim3_zero_hi' (a b : BitVec 64) : lim3 a b (BitVec.ofNat 64 0) = lim2 a b := by
  unfold lim3 lim2; simp

/-- One Horner step: HK, the bit loop and HF. -/
theorem khorner_step {s0 : MachineState} {d : Nat} {coefs : List Digest} (hd : d < 2 ^ 10)
    (hlen : coefs.length = 31) (hcoef : DigsAt s0 KCOEF coefs) {m : Nat} (hm : m < 31) {t : MachineState}
    (ht : KHkSt s0 d coefs (m + 1) t) :
    ∃ v, Steps image t (hornStepK d) (hornStepK d) v ∧ v.pc = (if m = 0 then pcOf 679 else pcOf 647) ∧
      v.getReg .x13 = BitVec.ofNat 64 d ∧ v.getReg .x10 = BitVec.ofNat 64 (KCOEF + 16 * m) ∧
      v.getReg .x11 = BitVec.ofNat 64 KCOEF ∧
      lim2 (v.getReg .x14) (v.getReg .x15) = (familyEval (coefs.drop m) d).toNat ∧
      RegsExcept s0 v khornRegs ∧ Frame s0 v (fun _ => False) := by
  obtain ⟨t1, st1, p1, x10, x4, x12, x16, x24, x29, r1, f1⟩ :=
    kgHK_spec t ht.pc (m + 1) (by omega) (by omega) ht.x10
  rw [Nat.add_sub_cancel] at x10
  have h0 : KHbSt t1 d (familyEval (coefs.drop (m + 1)) d).toNat 0 t1 := by
    refine ⟨p1, ?_, ?_, ?_, RegsExcept.refl _ _, Frame.refl _ _⟩
    · rw [x12, lim3_zero_hi', r1.get (by simp), r1.get (by simp), ht.acc]; simp
    · rw [x16, x24, x4]; unfold lim3; simp [clmulSmall]
    · rw [x29, ht.x13]; simp
  obtain ⟨u, su, hu⟩ := khb_loop (BitVec.isLt _) hd 10 0 (by norm_num) (Or.inl rfl) t1 h0
  have u10 : u.getReg .x10 = BitVec.ofNat 64 (KCOEF + 16 * m) := by rw [hu.regs.get (by simp [khbRegs]), x10]
  have u11 : u.getReg .x11 = BitVec.ofNat 64 KCOEF := by
    rw [hu.regs.get (by simp [khbRegs]), r1.get (by simp), ht.x11]
  obtain ⟨v, sv, vpc, v14, v15, vr, vf⟩ := kgHF_spec u hu.pc u10 (by simp only [KCOEF]; omega)
    (by simp only [KCOEF]; omega)
  have fu : Frame s0 u (fun _ => False) :=
    ((ht.frame.trans f1).trans hu.frame).mono (fun _ _ h => by simp_all)
  have hl := horner_limbs hu.pr (kcoef_limbs hcoef fu (m := m) (by omega) (by omega))
  rw [← kfamilyEval_drop coefs m (by omega)] at hl
  refine ⟨v, Steps.of_eq (st1.trans (su.trans sv)) (by simp [hornStepK]; omega) (by simp [hornStepK]; omega),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [vpc, u10, u11]
    by_cases h : m = 0
    · subst h; simp
    · rw [if_neg h]
      have : BitVec.ofNat 64 (KCOEF + 16 * m) ≠ BitVec.ofNat 64 KCOEF := by
        rw [Ne, ofNat_inj (by simp only [KCOEF]; omega) (by simp only [KCOEF]; omega)]; omega
      simp [this]
  · rw [vr.get (by simp), hu.regs.get (by simp [khbRegs]), r1.get (by simp), ht.x13]
  · rw [vr.get (by simp), u10]
  · rw [vr.get (by simp), u11]
  · rw [v14, v15]; exact hl
  · exact (((ht.regs.trans r1).trans hu.regs).trans vr).mono (by simp [khornRegs, khbRegs])
  · exact (fu.trans vf).mono (fun _ _ h => by simp_all)

theorem khorner_loop {s0 : MachineState} {d : Nat} {coefs : List Digest} (hd : d < 2 ^ 10)
    (hlen : coefs.length = 31) (hcoef : DigsAt s0 KCOEF coefs) {ret : Nat} (h1 : s0.getReg .x1 = pcOf ret) :
    ∀ m, m < 31 → ∀ t, KHkSt s0 d coefs (m + 1) t →
      ∃ u, Steps image t ((m + 1) * hornStepK d + 4) ((m + 1) * hornStepK d + 4) u ∧ u.pc = pcOf ret ∧
        DigAt u (CHAIN + 48) (familyEval coefs d) ∧ RegsExcept s0 u khornRegs ∧
        Frame s0 u (fun A => A = CHAIN + 48 ∨ A = CHAIN + 56) := by
  intro m
  induction m with
  | zero =>
    intro hm t ht
    obtain ⟨v, sv, vpc, -, -, -, vacc, vr, vf⟩ := khorner_step hd hlen hcoef hm ht
    rw [if_pos rfl] at vpc
    obtain ⟨w, sw, wpc, w48, w56, wr, wf⟩ := kgHE_spec v vpc ret (by rw [vr.get (by simp [khornRegs]), h1])
    rw [List.drop_zero] at vacc
    obtain ⟨l0, l1⟩ := limbs_of_lim2 vacc
    refine ⟨w, Steps.of_eq (sv.trans sw) (by ring) (by ring), wpc, ⟨by rw [w48, l0], by rw [w56, l1]⟩,
      (vr.trans wr).mono (by simp [khornRegs]), (vf.trans wf).mono (fun _ _ h => by simp_all)⟩
  | succ m ih =>
    intro hm t ht
    obtain ⟨v, sv, vpc, v13, v10, v11, vacc, vr, vf⟩ := khorner_step hd hlen hcoef hm ht
    rw [if_neg (by omega)] at vpc
    obtain ⟨w, sw, hw⟩ := ih (by omega) v ⟨vpc, v13, v10, v11, vacc, vr, vf⟩
    exact ⟨w, Steps.of_eq (sv.trans sw) (by ring) (by ring), hw⟩

/-- HORN from its entry 642 (img-v6: `jal 1169`, KHORN sets the point `topPoint leaf i = (leaf % 4) · 64 + i + 1`):
`topSeed coefs leaf i` (31 coefficients at KCOEF) into `CHAIN + 48`, return to `x1`. -/
theorem khorn_run (s : MachineState) (hpc : s.pc = pcOf 642) {i leaf : Nat} (hi : i < 64)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 (i + 1)) (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf)
    {coefs : List Digest} (hlen : coefs.length = 31)
    (hcoef : DigsAt s KCOEF coefs) {ret : Nat} (h1 : s.getReg .x1 = pcOf ret) :
    ∃ u, Steps image s (hornK (topPoint leaf i)) (hornK (topPoint leaf i)) u ∧ u.pc = pcOf ret ∧
      DigAt u (CHAIN + 48) (topSeed coefs leaf i) ∧
      RegsExcept s u khornRegs ∧ Frame s u (fun A => A = CHAIN + 48 ∨ A = CHAIN + 56) := by
  obtain ⟨t0, st0, t0pc, t0r, t0f⟩ := kgH0_spec s hpc
  obtain ⟨t, st, tpc, t13, t10, t11, t14, t15, tr, tf⟩ := khA_spec t0 t0pc leaf (i + 1) (by omega)
    (by rw [t0r.get (by simp)]; exact h18) (by rw [t0r.get (by simp)]; exact h13)
  have hd : topPoint leaf i < 2 ^ 10 := by unfold topPoint; omega
  have hcoef0 : DigsAt s KCOEF coefs := hcoef
  have ht : KHkSt s (topPoint leaf i) coefs (30 + 1) t := by
    refine ⟨tpc, by rw [t13]; unfold topPoint; congr 1; omega, t10, t11, ?_, (t0r.trans tr).mono
      (by simp [khornRegs]), (t0f.trans tf).mono (fun _ _ h => by simp_all)⟩
    rw [t14, t15, List.drop_eq_nil_of_le (by omega)]
    rfl
  obtain ⟨u, su, upc, ud, ur, uf⟩ := khorner_loop hd hlen hcoef0 h1 30 (by norm_num) t ht
  exact ⟨u, Steps.of_eq (st0.trans (st.trans su)) (by unfold hornK; ring) (by unfold hornK; ring), upc, ud, ur,
    uf⟩

/-! ## COEFGEN loop -/
/-- The secret-key words of the private block at 0x20000 (and `t0 = 0`), as the private-pair queries need them. -/
structure KPriv (sk : BitVec 256) (s : MachineState) : Prop where
  x5 : s.getReg .x5 = 0
  p0 : s.getMem (BitVec.ofNat 64 PRIV) = sk.extractLsb' 0 64
  p8 : s.getMem (BitVec.ofNat 64 (PRIV + 8)) = sk.extractLsb' 64 64
  p32 : s.getMem (BitVec.ofNat 64 (PRIV + 32)) = sk.extractLsb' 128 64
  p40 : s.getMem (BitVec.ofNat 64 (PRIV + 40)) = sk.extractLsb' 192 64
  p48 : s.getMem (BitVec.ofNat 64 (PRIV + 48)) = 0
  p56 : s.getMem (BitVec.ofNat 64 (PRIV + 56)) = 0

/-- Registers COEFGEN may change (besides `s3`). -/
def cgRegs : List Reg := [.x4, .x10, .x11, .x12, .x14, .x24, .x29, .x30]
/-- Memory COEFGEN may change (img-v6: the 40 coefficient slots, 640 bytes). -/
def CgW (X : Nat) : Prop :=
  X = PRIV + 16 ∨ X = PRIV + 24 ∨ (SEEDS ≤ X ∧ X < SEEDS + 32) ∨ (KCOEF ≤ X ∧ X < KCOEF + 640)

/-- img-v6 pair loop (618..638) at counter `j` (pairs `first + j`), `odd` = whether the carry occupies slot 0. -/
structure CgInv (s0 : MachineState) (first odd j : Nat) (acc : List Digest) (t : MachineState) : Prop where
  pc : t.pc = (if j < 16 then pcOf 618 else pcOf 639)
  x14 : t.getReg .x14 = BitVec.ofNat 64 (1 + 2 ^ 32 * (first + j))
  x24 : t.getReg .x24 = BitVec.ofNat 64 (KCOEF + 16 * acc.length)
  x29 : t.getReg .x29 = BitVec.ofNat 64 j
  len : acc.length + odd = 2 * j
  coefs : DigsAt t KCOEF acc
  regs : RegsExcept s0 t cgRegs
  frame : Frame s0 t CgW

theorem kcg_body (sk : BitVec 256) {s0 : MachineState} (hp : KPriv sk s0) {first odd : Nat}
    (hfirst : first + 16 < 2 ^ 32) {j : Nat} (hj : j < 16) (acc : List Digest) (t : MachineState)
    (ht : CgInv s0 first odd j acc t) :
    TSim image sk t 21 28 1 1 (do let p ← topSeedPair (first + j); pure (acc ++ [p.1, p.2]))
      (CgInv s0 first odd (j + 1)) := by
  have tpc : t.pc = pcOf 618 := by rw [ht.pc, if_pos hj]
  have hlen := ht.len
  obtain ⟨t1, st1, t1pc, t10, t11, t12, t1a, t1b, t1r, t1f⟩ := kgCG1_spec t tpc
  have hpos : first + j < 2 ^ 32 := by omega
  have t1a' : t1.getMem (BitVec.ofNat 64 (PRIV + 16)) = BitVec.ofNat 64 (hdr0 0 0 0 (first + j)) := by
    rw [t1a, ht.x14, hdr0_eq 0 0 0 _ (by norm_num) (by norm_num) (by norm_num) hpos]
  have t1b' : t1.getMem (BitVec.ofNat 64 (PRIV + 24)) = BitVec.ofNat 64 (hdr1 0 0) := by
    rw [t1b, hdr1_eq 0 0 (by norm_num) (by norm_num)]; rfl
  have fr : ∀ X, (X = PRIV ∨ X = PRIV + 8 ∨ X = PRIV + 32 ∨ X = PRIV + 40 ∨ X = PRIV + 48 ∨
      X = PRIV + 56) → t1.getMem (BitVec.ofNat 64 X) = s0.getMem (BitVec.ofNat 64 X) := by
    intro X hX
    have hX' : X < 2 ^ 64 := by rcases hX with h | h | h | h | h | h <;> (rw [h]; decide)
    rw [t1f.get hX' (by simp only [PRIV] at hX ⊢; omega),
      ht.frame.get hX' (by unfold CgW; simp only [PRIV, SEEDS, KCOEF] at hX ⊢; omega)]
  have hq : hashInput t1 = toQ (privateInput sk (.inl (header 0 0 0 (first + j) 0))) := by
    refine hashInput_toQ t1 _ 0 PRIV (privateInput_tweak_length _ _) t10 (by decide) (by decide) t11
      (by decide) ?_
    rw [wordsOf_privateInput_tweak, header_lo, header_hi, readWords_eight, fr PRIV (by simp),
      fr (PRIV + 8) (by simp), t1a', t1b', fr (PRIV + 32) (by simp), fr (PRIV + 40) (by simp),
      fr (PRIV + 48) (by simp), fr (PRIV + 56) (by simp), hp.p0, hp.p8, hp.p32, hp.p40, hp.p48, hp.p56]
    rfl
  have hv : hashArgumentsValid t1 = true :=
    hashArgs_const t1 PRIV 64 SEEDS t10 t11 t12 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h5 : t1.getReg .x5 = 0 := by rw [t1r.get (by simp), ht.regs.get (by simp [cgRegs]), hp.x5]
  refine (TSim.steps st1 (TSim.privatePair_bind (k := 15) (c := 15) (n := 0) (b := 0)
    (fetch_kg623 t1 t1pc) h5 hv hq (fun a => ?_))).of_eq rfl rfl rfl rfl rfl
  have hwf := Frame.writeHash t1 a SEEDS t12 (by decide)
  have hlo := DigAt.writeHash_lo t1 a SEEDS t12 (by decide)
  have hhi := DigAt.writeHash_hi t1 a SEEDS t12 (by decide)
  obtain ⟨u, su, upc, u14, u24, u29, umem, ur, uf⟩ := kgCG2_spec (writeHash t1 a)
    (by rw [pc_writeHash, t1pc, pcOf_add4]) j _ (16 * acc.length) hj (by omega) (by omega) (by rw [getReg_writeHash, t10])
    (by rw [getReg_writeHash, t1r.get (by simp), ht.x24]) (by rw [getReg_writeHash, t1r.get (by simp), ht.x29])
    (by rw [getReg_writeHash, t1r.get (by simp), ht.x14])
  have ftu : Frame t u (fun X => (X = PRIV + 16 ∨ X = PRIV + 24) ∨ (SEEDS ≤ X ∧ X < SEEDS + 32) ∨
      (KCOEF + 16 * acc.length ≤ X ∧ X < KCOEF + 16 * acc.length + 32)) :=
    (t1f.trans (hwf.trans uf)).mono (fun _ _ h => h)
  refine TSim.pure_steps su ⟨?_, ?_, ?_, u29, ?_, ?_, ?_, ?_⟩
  · rw [upc]
  · rw [u14, show 1 + 2 ^ 32 * (first + j) + 2 ^ 32 = 1 + 2 ^ 32 * (first + (j + 1)) by ring]
  · rw [u24]; simp only [List.length_append, List.length_cons, List.length_nil]; (try congr 1); (try ring)
  · simp; omega
  · have hold : DigsAt u KCOEF acc := ht.coefs.frame ftu (by simp only [KCOEF]; omega)
      (fun X h1 h2 h => by simp only [PRIV, SEEDS, KCOEF] at h h1 h2; omega)
    have hd1 : DigAt u (KCOEF + 16 * acc.length) (a.extractLsb' 0 128) := by
      rw [show KCOEF + 16 * acc.length = KCOEF + 16 * acc.length + 8 * 0 by ring]
      refine ⟨by rw [umem 0 (by norm_num)]; exact hlo.1, ?_⟩
      rw [show KCOEF + 16 * acc.length + 8 * 0 + 8 = KCOEF + 16 * acc.length + 8 * 1 by ring, umem 1 (by norm_num)]
      exact hlo.2
    have hd2 : DigAt u (KCOEF + 16 * (acc ++ [a.extractLsb' 0 128]).length) (a.extractLsb' 128 128) := by
      rw [List.length_append, List.length_singleton,
        show KCOEF + 16 * (acc.length + 1) = KCOEF + 16 * acc.length + 8 * 2 by ring]
      refine ⟨by rw [umem 2 (by norm_num)]; exact hhi.1, ?_⟩
      rw [show KCOEF + 16 * acc.length + 8 * 2 + 8 = KCOEF + 16 * acc.length + 8 * 3 by ring, umem 3 (by norm_num),
        show SEEDS + 8 * 3 = SEEDS + 16 + 8 by rfl]
      exact hhi.2
    have := (hold.snoc hd1).snoc hd2
    simpa using this
  · have hw0 : RegsExcept t1 (writeHash t1 a) [] := fun r _ => getReg_writeHash t1 a r
    exact (ht.regs.trans ((t1r.trans hw0).trans ur)).mono (by simp [cgRegs])
  · refine (ht.frame.trans ftu).mono (fun X _ h => ?_)
    unfold CgW at *
    rcases h with h | (h | h) | h | h
    · exact h
    · left; exact h
    · right; left; exact h
    · right; right; left; exact h
    · right; right; right; simp only [KCOEF] at h ⊢; omega

theorem DigsAt.take' {t : MachineState} {A : Nat} {ds : List Digest} (h : DigsAt t A ds) (n : Nat) :
    DigsAt t A (ds.take n) := fun i hi => by
  simp only [List.length_take] at hi
  have := h i (by omega)
  simpa [List.getD_eq_getElem?_getD, List.getElem?_take, show i < n by omega] using this

/-- img-v6: the keygen coefficient buffer before top leaf `leaf` (state `cc = (coefficients, carry)`): inside a family
the family's 31 coefficients at KCOEF; the carry at slot 31 whenever the next family start is odd. -/
def KcPre (s : MachineState) (leaf : Nat) (cc : List Digest × Digest) : Prop :=
  (leaf % 4 ≠ 0 → cc.1.length = 31 ∧ DigsAt s KCOEF cc.1) ∧
    ((leaf + 3) / 4 % 2 = 1 → DigAt s (KCOEF + 496) cc.2)
/-- img-v6: the coefficient buffer after KTOP for leaf `leaf` (and after the leaf). -/
def KcPost (s : MachineState) (leaf : Nat) (cc : List Digest × Digest) : Prop :=
  cc.1.length = 31 ∧ DigsAt s KCOEF cc.1 ∧ ((leaf + 4) / 4 % 2 = 1 → DigAt s (KCOEF + 496) cc.2)

theorem KcPre.frame {s t : MachineState} {W : Nat → Prop} {leaf : Nat} {cc : List Digest × Digest}
    (h : KcPre s leaf cc) (hf : Frame s t W) (hW : ∀ X, KCOEF ≤ X → X < KCOEF + 640 → ¬ W X) :
    KcPre t leaf cc :=
  ⟨fun h0 => ⟨(h.1 h0).1, (h.1 h0).2.frame hf (by rw [(h.1 h0).1]; simp only [KCOEF]; omega)
      (fun X h1 h2 => hW X h1 (by rw [(h.1 h0).1] at h2; omega))⟩,
    fun h1 => (h.2 h1).frame hf (by simp only [KCOEF]; omega) (hW _ (by omega) (by omega))
      (hW _ (by omega) (by omega))⟩
theorem KcPost.frame {s t : MachineState} {W : Nat → Prop} {leaf : Nat} {cc : List Digest × Digest}
    (h : KcPost s leaf cc) (hf : Frame s t W) (hW : ∀ X, KCOEF ≤ X → X < KCOEF + 640 → ¬ W X) :
    KcPost t leaf cc :=
  ⟨h.1, h.2.1.frame hf (by rw [h.1]; simp only [KCOEF]; omega) (fun X h1 h2 => hW X h1 (by rw [h.1] at h2; omega)),
    fun h1 => (h.2.2 h1).frame hf (by simp only [KCOEF]; omega) (hW _ (by omega) (by omega))
      (hW _ (by omega) (by omega))⟩

/-- Steps of KTOP at a family start (`o = f % 2`): 612, 1149..1160, [1161..1165], 1166, the pair loop, 639..640. -/
def kfK (o : Nat) : Nat := 16 + 5 * o + 21 * (16 - o)
/-- Cycles of KTOP at a family start. -/
def kfC (o : Nat) : Nat := 19 + 5 * o + 28 * (16 - o)

/-- img-v6 KTOP from 612 (called from 157 with `ra = 158`): `topFamilyCoefs leaf cc` into the coefficient buffer,
`s3 = 0`. -/
theorem kfam_tsim (sk : BitVec 256) {s : MachineState} (hpc : s.pc = pcOf 612) {leaf : Nat}
    (hleaf : leaf < 4096) (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) (hp : KPriv sk s)
    (h1 : s.getReg .x1 = pcOf 158) {cc : List Digest × Digest} (hk : KcPre s leaf cc) :
    TSim image sk s (if leaf % 4 = 0 then kfK (leaf / 4 % 2) else 5) (if leaf % 4 = 0 then kfC (leaf / 4 % 2) else 5)
      (if leaf % 4 = 0 then 16 - leaf / 4 % 2 else 0) (if leaf % 4 = 0 then 16 - leaf / 4 % 2 else 0)
      (topFamilyCoefs leaf cc)
      (fun cc' t => t.pc = pcOf 158 ∧ KcPost t leaf cc' ∧ t.getReg .x19 = BitVec.ofNat 64 0 ∧
        RegsExcept s t (cgRegs ++ [.x19]) ∧ Frame s t CgW) := by
  obtain ⟨t0, st0, t0pc, t0r, t0f⟩ := kg612_spec s hpc
  obtain ⟨tA, stA, tApc, tAr, tAf⟩ := kfA_spec t0 t0pc leaf (by rw [t0r.get (by simp)]; exact h18)
  have r0A : RegsExcept s tA ([] ++ [.x30]) := t0r.trans tAr
  have f0A : Frame s tA (fun _ => False) := (t0f.trans tAf).mono (fun _ _ h => by simp_all)
  unfold topFamilyCoefs
  by_cases h0 : leaf % 4 = 0
  · rw [if_pos h0] at tApc
    simp only [h0, ↓reduceIte]
    have o2 : leaf / 4 % 2 < 2 := Nat.mod_lt _ (by norm_num)
    obtain ⟨tB, stB, tBpc, tB14, tB24, tB29, tBr, tBf⟩ := kfB_spec tA tApc leaf (by omega)
      (by rw [r0A.get (by simp)]; exact h18)
    -- the state at 618 with the initial accumulator
    obtain ⟨tE, kE, cE, stE, hkE, hcE, ⟨tEpc, tE14, tE24, tE29, tEr, tEf, tEc⟩⟩ : ∃ tE kE cE, Steps image tB kE cE tE ∧
        kE = 1 + 5 * (leaf / 4 % 2) ∧ cE = 1 + 5 * (leaf / 4 % 2) ∧
        (tE.pc = pcOf 618 ∧ tE.getReg .x14 = tB.getReg .x14 ∧
          tE.getReg .x24 = BitVec.ofNat 64 (KCOEF + 16 * (leaf / 4 % 2)) ∧ tE.getReg .x29 = tB.getReg .x29 ∧
          RegsExcept tB tE [.x4, .x24] ∧ Frame tB tE (fun A => A = KCOEF ∨ A = KCOEF + 8) ∧
          DigsAt tE KCOEF (if leaf / 4 % 2 = 0 then [] else [cc.2])) := by
      by_cases ho : leaf / 4 % 2 = 0
      · rw [if_pos ho] at tBpc
        obtain ⟨u, su, upc, ur, uf⟩ := kfE_spec tB tBpc
        refine ⟨u, 1, 1, su, by rw [ho], by rw [ho], upc, ur.get (by simp), ?_, ur.get (by simp),
          ur.mono (by simp), uf.mono (fun _ _ h => h.elim), ?_⟩
        · rw [ur.get (by simp), tB24, ho]
        · rw [if_pos ho]; exact DigsAt.nil _ _
      · rw [if_neg ho] at tBpc
        obtain ⟨u, su, upc, um0, um8, u24, ur, uf⟩ := kfD_spec tB tBpc tB24
        obtain ⟨v, sv, vpc, vr, vf⟩ := kfE_spec u upc
        have hcar : DigAt tB (KCOEF + 496) cc.2 := by
          have := hk.2 (by omega)
          exact this.frame (f0A.trans tBf) (by simp only [KCOEF]; omega) (by simp) (by simp)
        refine ⟨v, 5 + 1, 5 + 1, su.trans sv, by omega, by omega, vpc, ?_, ?_, ?_, (ur.trans vr).mono (by simp),
          (uf.trans vf).mono (fun _ _ h => by simp_all), ?_⟩
        · rw [vr.get (by simp), ur.get (by simp)]
        · rw [vr.get (by simp), u24, show leaf / 4 % 2 = 1 by omega]
        · rw [vr.get (by simp), ur.get (by simp)]
        · rw [if_neg ho]
          intro i hi
          simp only [List.length_singleton] at hi
          have hi0 : i = 0 := by omega
          subst hi0
          refine ⟨?_, ?_⟩
          · rw [show KCOEF + 16 * 0 = KCOEF by rfl, vf.get (by decide) (by simp), um0]; exact hcar.1
          · rw [show KCOEF + 16 * 0 + 8 = KCOEF + 8 by rfl, vf.get (by decide) (by simp), um8]
            exact hcar.2
    have hfirst : 31 * (leaf / 4) / 2 + 16 < 2 ^ 32 := by omega
    have hI : CgInv s (31 * (leaf / 4) / 2) (leaf / 4 % 2) (leaf / 4 % 2 + 0)
        (if leaf / 4 % 2 = 0 then [] else [cc.2]) tE := by
      refine ⟨by rw [tEpc, if_pos (by omega)], by rw [tE14, tB14]; rfl, ?_, by rw [tE29, tB29]; rfl, ?_, tEc, ?_, ?_⟩
      · rw [tE24]; split <;> simp_all
      · split <;> simp_all <;> omega
      · exact ((r0A.trans tBr).trans tEr).mono (by simp [cgRegs])
      · refine ((f0A.trans tBf).trans tEf).mono (fun X _ h => ?_)
        unfold CgW; simp only [KCOEF] at h ⊢
        rcases h with (h | h) | h
        · exact h.elim
        · exact h.elim
        · omega
    have hloop := TSim.foldlM_range' (image := image) (sk := sk) (leaf / 4 % 2) (16 - leaf / 4 % 2)
      (fun acc j => do let p ← topSeedPair (31 * (leaf / 4) / 2 + j); pure (acc ++ [p.1, p.2]))
      (if leaf / 4 % 2 = 0 then [] else [cc.2])
      (fun j acc t => CgInv s (31 * (leaf / 4) / 2) (leaf / 4 % 2) (leaf / 4 % 2 + j) acc t)
      (fun _ => 21) (fun _ => 28) (fun _ => 1) (fun _ => 1)
      (fun j hj acc t ht => kcg_body sk hp hfirst (by omega) acc t ht) hI
    unfold topCoefsK topPairsFrom
    refine (TSim.steps (st0.trans (stA.trans (stB.trans stE))) (TSim.bind (k₂ := 2) (c₂ := 2) (n₂ := 0) (b₂ := 0)
      (f := fun acc => pure (acc.take topCoefCount, acc.getD topCoefCount 0))
      hloop (fun acc t ht => ?_))).of_eq rfl ?_ ?_ ?_ ?_
    · have hl := ht.len
      have tpc : t.pc = pcOf 639 := by rw [ht.pc, if_neg (by omega)]
      obtain ⟨u, su, upc, u19, ur, uf⟩ := kgCG3_spec t tpc 158
        (by rw [ht.regs.get (by simp [cgRegs]), h1])
      have hc : DigsAt u KCOEF acc := ht.coefs.frame uf (by simp only [KCOEF]; omega) (fun _ _ _ h => h)
      refine TSim.pure_steps su ⟨upc, ⟨?_, DigsAt.take' hc 31, fun ho => ?_⟩, u19, ht.regs.trans ur,
        (ht.frame.trans uf).mono (fun _ _ h => by simp_all)⟩
      · simp only [List.length_take, topCoefCount]; omega
      · have ho' : leaf / 4 % 2 = 0 := by omega
        have := hc 31 (by omega)
        simpa [topCoefCount] using this
    all_goals simp only [sumTo_const, kfK, kfC]; omega
  · rw [if_neg h0] at tApc
    simp only [h0, ↓reduceIte]
    obtain ⟨u, su, upc, u19, ur, uf⟩ := kfF_spec tA tApc 158 (by rw [r0A.get (by simp)]; exact h1)
    have fsu : Frame s u (fun _ => False) := (f0A.trans uf).mono (fun _ _ h => by simp_all)
    have hk' := hk.frame fsu (fun _ _ _ h => h)
    refine TSim.pure_steps (st0.trans (stA.trans su)) ⟨upc, ⟨(hk'.1 h0).1, (hk'.1 h0).2,
      fun h1 => hk'.2 (by omega)⟩, u19, (r0A.trans ur).mono (by simp [cgRegs]), fsu.mono (fun _ _ h => h.elim)⟩

/-! ## The top leaf -/
macro "tl_omega" : tactic =>
  `(tactic| ((try simp only [PRIV, SEEDS, CHAIN, NODE, NOUT, LOUT, LEAFPK, KCOEF] at *); omega))

/-- Registers the top-leaf routine may change. -/
def tRegs : List Reg := leafRegs ++ [.x4, .x13, .x14, .x15, .x16, .x24]
/-- Memory the top-leaf routine may change: the leaf writes, `end_0`'s slot (campaign T51: `LEAFPK`, below the
tweak) and the coefficient buffer. -/
def TW (A : LeafArgs) (X : Nat) : Prop := LeafW A X ∨ (LEAFPK ≤ X ∧ X < LEAFPK + 16) ∨ (KCOEF ≤ X ∧ X < KCOEF + 640)

/-- Campaign T51 ("endpad"): the slot of chain `c`'s end in the top leaf buffer: `end_0` at `LEAFPK`, the tweak at
`LEAFPK + 16`, `end_c` at `LEAFPK + 16 (c + 1)` (`c ≥ 1`). -/
def tslot (c : Nat) : Nat := if c = 0 then LEAFPK else LEAFPK + 16 * (c + 1)
theorem tslot_eq (c : Nat) : tslot c = LEAFPK + 16 * (c + (if c = 0 then 0 else 1)) := by
  unfold tslot; split_ifs <;> omega
theorem tslot_ge (c : Nat) : LEAFPK ≤ tslot c := by unfold tslot; split_ifs <;> omega
theorem tslot_lt {c n : Nat} (hc : c < n) : tslot c + 16 ≤ LEAFPK + 16 * (n + 1) := by
  unfold tslot; split_ifs <;> omega
theorem tslot_disj {c j : Nat} (h : c ≠ j) : tslot c + 16 ≤ tslot j ∨ tslot j + 16 ≤ tslot c := by
  unfold tslot; split_ifs <;> omega
theorem tslot_hdr (c : Nat) : tslot c + 16 ≤ LEAFPK + 16 ∨ LEAFPK + 32 ≤ tslot c := by
  unfold tslot; split_ifs <;> omega
theorem TW_of_tslot {A : LeafArgs} (h0 : A.lay = 0) {j X : Nat} (hj : j < A.n) (h : tslot j ≤ X ∧ X < tslot j + 16) :
    TW A X := by
  unfold TW LeafW tslot at *
  rw [if_pos h0]
  by_cases hj0 : j = 0
  · rw [if_pos hj0] at h; right; left; omega
  · rw [if_neg hj0] at h; left; right; right; right; right; right; right; left; constructor <;> omega

/-- Campaign T51: the keygen top leaf's precondition (= `LeafPre` without the zero head: `LEAFPK` now holds
`end_0` of the previous leaf). -/
structure TopPre (sk : BitVec 256) (s : MachineState) (A : LeafArgs) : Prop where
  x1 : s.getReg .x1 = pcOf A.ret
  x5 : s.getReg .x5 = 0
  x8 : s.getReg .x8 = BitVec.ofNat 64 A.lay.val
  x9 : s.getReg .x9 = BitVec.ofNat 64 A.tree
  x18 : s.getReg .x18 = BitVec.ofNat 64 A.leaf
  x22 : s.getReg .x22 = BitVec.ofNat 64 A.digp
  x23 : s.getReg .x23 = BitVec.ofNat 64 A.valp
  x25 : s.getReg .x25 = BitVec.ofNat 64 A.dest
  x26 : s.getReg .x26 = BitVec.ofNat 64 A.n
  x27 : s.getReg .x27 = BitVec.ofNat 64 (n4 A.lay)
  x31 : s.getReg .x31 = BitVec.ofNat 64 (if A.so then 1 else 0)
  htree : A.tree < 2 ^ 32
  hleaf : A.leaf < 2 ^ 32
  hroute : A.tree * 2 ^ T3.height A.lay + A.leaf < 2 ^ 31
  hleafHeight : A.leaf < 2 ^ T3.height A.lay
  hsteps : ∀ i < A.n, A.e i ≤ 8
  p0 : s.getMem (BitVec.ofNat 64 PRIV) = sk.extractLsb' 0 64
  p8 : s.getMem (BitVec.ofNat 64 (PRIV + 8)) = sk.extractLsb' 64 64
  p32 : s.getMem (BitVec.ofNat 64 (PRIV + 32)) = sk.extractLsb' 128 64
  p40 : s.getMem (BitVec.ofNat 64 (PRIV + 40)) = sk.extractLsb' 192 64
  p48 : s.getMem (BitVec.ofNat 64 (PRIV + 48)) = 0
  p56 : s.getMem (BitVec.ofNat 64 (PRIV + 56)) = 0
  z0 : s.getMem (BitVec.ofNat 64 CHAIN) = 0
  z8 : s.getMem (BitVec.ofNat 64 (CHAIN + 8)) = 0
  top0 : A.lay = 0 ∧ A.tree = 0
  hdig : ∀ i < A.n, s.getByte (BitVec.ofNat 64 (A.digp + i)) = BitVec.ofNat 8 (A.d i)
  hdigb : ∀ i < A.n, A.d i < 256 ∧ (A.so = false → A.d i ≤ maxDigit A.lay i)
  hdigp : A.digp + A.n ≤ 2 ^ 24
  hdigW : ∀ i < A.n, ¬ LeafW A ((A.digp + i) / 8 * 8)
  hv8 : A.valp % 8 = 0
  hv : A.valp + 16 * A.n ≤ 2 ^ 24
  hvs : A.valp + 16 * A.n ≤ PRIV ∨ LEAFPK + 960 ≤ A.valp
  hd8 : A.dest % 8 = 0
  hd : A.dest + 16 ≤ 2 ^ 24
  hds : A.dest + 16 ≤ PRIV ∨ LEAFPK + 960 ≤ A.dest ∨ (CHAIN + 112 ≤ A.dest ∧ A.dest + 16 ≤ LOUT)
  hdv : A.dest + 16 ≤ A.valp ∨ A.valp + 16 * A.n ≤ A.dest

/-- The keygen top-leaf arguments: signature-free, no digits, buffers clear of KCOEF. -/
structure TopArgs (A : LeafArgs) : Prop where
  so : A.so = false
  dig : A.digits = []
  cv : A.valp + 16 * A.n ≤ KCOEF ∨ KCOEF + 640 ≤ A.valp
  cd : A.dest + 16 ≤ KCOEF ∨ KCOEF + 640 ≤ A.dest
  cdig : A.digp + A.n ≤ KCOEF ∨ KCOEF + 640 ≤ A.digp
  /-- Campaign T51: the digits are clear of `end_0`'s slot. -/
  cdigL : A.digp + A.n ≤ LEAFPK ∨ LEAFPK + 16 ≤ A.digp

structure TInv (s0 : MachineState) (A : LeafArgs) (coefs extra : List Digest) (j : Nat) (st : List Digest × List Digest)
    (t : MachineState) : Prop where
  x19 : t.getReg .x19 = BitVec.ofNat 64 j
  x23 : t.getReg .x23 = BitVec.ofNat 64 (A.valp + 16 * j)
  x3 : t.getReg .x3 = pcOf A.ret
  regs : RegsExcept s0 t tRegs
  frame : Frame s0 t (TW A)
  lh16 : t.getMem (BitVec.ofNat 64 (LEAFPK + 16)) = T3.hyperWord A.lay.val (A.tree * 2 ^ T3.height A.lay + A.leaf)
  lh24 : t.getMem (BitVec.ofNat 64 (LEAFPK + 24)) = 0
  elen : st.1.length = j
  vlen : st.2.length = j
  ends : ∀ c < j, DigAt t (tslot c) (st.1.getD c 0)
  vals : DigsAt t A.valp st.2
  coef : DigsAt t KCOEF coefs
  ext : DigsAt t (KCOEF + 496) extra

/-- Registers changed between the loop head and the chain routine's return. -/
def preRegs : List Reg :=
  [.x1, .x4, .x6, .x7, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x20, .x21, .x24, .x28, .x29, .x30]

section top
variable (sk : BitVec 256) {s0 : MachineState} {A : LeafArgs} (hpre : TopPre sk s0 A) (hta : TopArgs A)
  {coefs extra : List Digest} (hcl : coefs.length = 31) (hel : extra.length ≤ 1)
include hpre hta hcl hel

theorem ktop_post {j : Nat} (hj : j < A.n) {st : List Digest × List Digest} {t u : MachineState}
    (ht : TInv s0 A coefs extra j st t) (hupc : u.pc = pcOf 196) (hur : RegsExcept t u preRegs)
    (huf : Frame t u (fun X => (X = CHAIN + 48 ∨ X = CHAIN + 56) ∨ ChainW (A.valp + 16 * j) X))
    (v last : Digest) (hv : DigAt u (A.valp + 16 * j) v) (hl : DigAt u (CHAIN + 48) last) :
    ∃ w, Steps image u 16 16 w ∧ w.pc = pcOf 158 ∧ TInv s0 A coefs extra (j + 1) (st.1 ++ [last], st.2 ++ [v]) w := by
  have hn : A.n = 51 := by show chainCount A.lay = 51; rw [hpre.top0.1]; rfl
  have h0 := hpre.top0.1
  have hvs := hpre.hvs
  have hvb := hpre.hv
  have hv8 := hpre.hv8
  have hcv := hta.cv
  have g : ∀ r, r ∉ tRegs → t.getReg r = s0.getReg r := fun r hr => ht.regs.get hr
  have r31 : u.getReg .x31 = BitVec.ofNat 64 (if A.so then 1 else 0) := by
    rw [hur.get (by simp [preRegs]), g _ (by simp [tRegs, leafRegs]), hpre.x31]
  rw [hta.so] at r31
  obtain ⟨u1, st1, u1pc, u1r, u1f⟩ := sub79_spec subAt_keygen u hupc false r31
  simp only [Bool.false_eq_true, if_false] at u1pc
  have r19 : u1.getReg .x19 = BitVec.ofNat 64 j := by
    rw [u1r.get (by simp), hur.get (by simp [preRegs])]; exact ht.x19
  obtain ⟨u3, st3, u3pc, u3x28, u3r, u3f⟩ := sub80_spec subAt_keygen u1 u1pc j (by omega) r19
  have hl1 : DigAt u1 (CHAIN + 48) last := hl.frame u1f (by decide) (by simp) (by simp)
  have hk1 : (if j = 0 then 0 else 1) ≤ 1 := by split_ifs <;> omega
  have hs := tslot_eq j
  generalize hkk : (if j = 0 then 0 else 1) = k at u3x28 hk1 hs
  obtain ⟨u4, st4, u4pc, u4x28, u4r, u4f⟩ := sub82_spec subAt_keygen u3 u3pc (j + k) (by omega) u3x28
  obtain ⟨u5, st5, u5pc, u5a, u5b, u5r, u5f⟩ := sub83_spec subAt_keygen u4 u4pc (16 * (j + k)) (by omega)
    (by sc_omega) u4x28
  have hl4 := hl1.frame (u3f.trans u4f) (by decide) (by simp) (by simp)
  have u5s : DigAt u5 (tslot j) last := ⟨by rw [hs, u5a]; exact hl4.1, by rw [hs, u5b]; exact hl4.2⟩
  have u5f' : Frame u1 u5 (fun X => tslot j ≤ X ∧ X < tslot j + 16) :=
    ((u3f.trans u4f).trans u5f).mono (fun X _ h => by rw [hs]; simp at h ⊢; omega)
  have r19' : u5.getReg .x19 = BitVec.ofNat 64 j := by
    rw [u5r.get (by simp), u4r.get (by simp), u3r.get (by simp)]; exact r19
  have r23' : u5.getReg .x23 = BitVec.ofNat 64 (A.valp + 16 * j) := by
    rw [u5r.get (by simp), u4r.get (by simp), u3r.get (by simp), u1r.get (by simp), hur.get (by simp [preRegs])]
    exact ht.x23
  obtain ⟨w, st6, wpc, wx19, wx23, wr, wf⟩ := sub92_spec subAt_keygen u5 u5pc j (A.valp + 16 * j) r19' r23'
  have hsl : LEAFPK ≤ tslot j ∧ tslot j + 16 ≤ LEAFPK + 16 * (A.n + 1) :=
    ⟨tslot_ge j, tslot_lt hj⟩
  have fuw : Frame u w (fun X => tslot j ≤ X ∧ X < tslot j + 16) :=
    ((u1f.trans u5f').trans wf).mono (fun X _ h => by
      rcases h with (h | h) | h
      · exact h.elim
      · exact h
      · exact h.elim)
  have ftw : Frame t w (fun X => ((X = CHAIN + 48 ∨ X = CHAIN + 56) ∨ ChainW (A.valp + 16 * j) X) ∨
      (tslot j ≤ X ∧ X < tslot j + 16)) := huf.trans fuw
  refine ⟨w, Steps.of_eq (st1.trans ((st3.trans (st4.trans st5)).trans st6)) (by omega) (by omega), wpc,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [wx19]
  · rw [wx23, show A.valp + 16 * j + 16 = A.valp + 16 * (j + 1) by ring]
  · rw [wr.get (by simp), u5r.get (by simp), u4r.get (by simp), u3r.get (by simp), u1r.get (by simp),
      hur.get (by simp [preRegs])]; exact ht.x3
  · refine ((ht.regs.trans hur).trans ((((u1r.trans u3r).trans u4r).trans u5r).trans wr)).mono ?_
    simp [tRegs, leafRegs, preRegs]
  · refine (ht.frame.trans ftw).mono (fun X _ h => ?_)
    rcases h with h | ((h | h) | h)
    · exact h
    · exact Or.inl (LeafW_of_c48 h)
    · exact Or.inl (LeafW_of_chainW hj h)
    · exact TW_of_tslot h0 hj h
  · have := tslot_hdr j
    rw [ftw.get (by decide) (by unfold ChainW; tl_omega), ht.lh16]
  · have := tslot_hdr j
    rw [ftw.get (by decide) (by unfold ChainW; tl_omega), ht.lh24]
  · simp [ht.elen]
  · simp [ht.vlen]
  · intro c hc
    by_cases hcj : c = j
    · subst hcj
      have hl5 : DigAt w (tslot c) last := u5s.frame wf (by tl_omega) (by simp) (by simp)
      simpa [List.getD_eq_getElem?_getD, ht.elen] using hl5
    · have hc' : c < j := by omega
      have hsc := tslot_lt (show c < A.n by omega)
      have hsc0 := tslot_ge c
      have hd := tslot_disj hcj
      have hnot : ∀ X, tslot c ≤ X → X < tslot c + 16 →
          ¬ (((X = CHAIN + 48 ∨ X = CHAIN + 56) ∨ ChainW (A.valp + 16 * j) X) ∨
            (tslot j ≤ X ∧ X < tslot j + 16)) := by
        intro X h1 h2 h
        unfold ChainW at h
        tl_omega
      have h2 : DigAt w (tslot c) (st.1.getD c 0) :=
        (ht.ends c hc').frame ftw (by tl_omega) (hnot _ le_rfl (by omega)) (hnot _ (by omega) (by omega))
      simpa [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [ht.elen]; omega : c < st.1.length)] using h2
  · have hsj0 := tslot_ge j
    have hvw : DigAt w (A.valp + 16 * j) v := hv.frame fuw (by omega) (by tl_omega) (by tl_omega)
    have hvals : DigsAt w A.valp st.2 :=
      ht.vals.frame ftw (by rw [ht.vlen]; omega) (fun X h1 h2 h => by
        rw [ht.vlen] at h2
        unfold ChainW at h
        tl_omega)
    exact hvals.snoc (by rw [ht.vlen]; exact hvw)
  · exact ht.coef.frame ftw (by rw [hcl]; tl_omega) (fun X h1 h2 h => by
      rw [hcl] at h2
      have := tslot_ge j
      unfold ChainW at h
      tl_omega)
  · exact ht.ext.frame ftw (by tl_omega) (fun X h1 h2 h => by
      have := tslot_ge j
      unfold ChainW at h
      tl_omega)
end top

/-- The chain loop body of `buildLeafTop leaf []` (chain `i`, family seed). -/
def topBody (leaf : Nat) (coefs : List Digest) (state : List Digest × List Digest) (i : Nat) :
    T3.M (List Digest × List Digest) := do
  let digit := ([] : List Nat).getD i 0
  let value ← T3.topChain leaf i 0 digit (topSeed coefs leaf i)
  if false then return (state.1, state.2 ++ [value])
  let last ← T3.topChain leaf i digit (maxDigit 0 i - digit) value
  pure (state.1 ++ [last], state.2 ++ [value])

theorem topBody_eq (leaf : Nat) (coefs : List Digest) (st : List Digest × List Digest) (i : Nat) :
    topBody leaf coefs st i =
      (do let v ← T3.topChain leaf i 0 0 (topSeed coefs leaf i)
          let last ← T3.topChain leaf i 0 (maxDigit 0 i - 0) v
          pure (v, last)) >>= fun r => pure (st.1 ++ [r.2], st.2 ++ [r.1]) := by
  simp only [topBody, List.getD_nil, bind_assoc, pure_bind, Bool.false_eq_true, if_false]

/-- Steps of one chain iteration of the top leaf. -/
def titerK (r j : Nat) : Nat := 11 + capK j + hornK (r * 64 + j + 1) + kChainK j (maxDigit 0 j) + 16
/-- Cycles of one chain iteration of the top leaf. -/
def titerC (r j : Nat) : Nat := 11 + capK j + hornK (r * 64 + j + 1) + kChainCy j (maxDigit 0 j) + 16

section top
variable (sk : BitVec 256) {s0 : MachineState} {A : LeafArgs} (hpre : TopPre sk s0 A) (hta : TopArgs A)
  {coefs extra : List Digest} (hcl : coefs.length = 31) (hel : extra.length ≤ 1)
include hpre hta hcl hel

theorem ktop_iter {j : Nat} (hj : j < 51) {st : List Digest × List Digest} {t : MachineState}
    (ht : TInv s0 A coefs extra j st t) (hpc : t.pc = pcOf 158) :
    TSim image sk t (titerK (A.leaf % 4) j) (titerC (A.leaf % 4) j) (maxDigit 0 j) (maxDigit 0 j) (topBody A.leaf coefs st j)
      (fun st' u => u.pc = pcOf 158 ∧ TInv s0 A coefs extra (j + 1) st' u) := by
  have hn : A.n = 51 := by show chainCount A.lay = 51; rw [hpre.top0.1]; rfl
  have h0 := hpre.top0
  have hvs := hpre.hvs
  have hvb := hpre.hv
  have hv8 := hpre.hv8
  have hds := hpre.hds
  have hdv := hpre.hdv
  have hcv := hta.cv
  have hcd := hta.cd
  have g : ∀ r, r ∉ tRegs → t.getReg r = s0.getReg r := fun r hr => ht.regs.get hr
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := sub41_spec subAt_keygen t hpc j 51 (by omega) (by omega) ht.x19
    (by rw [g _ (by simp [tRegs, leafRegs]), hpre.x26, hn])
  rw [if_pos hj] at t1pc
  obtain ⟨t2, st2, t2pc, t2x1, t2x13, t2r, t2f⟩ := kg159_spec t1 t1pc j (by rw [t1r.get (by simp)]; exact ht.x19)
  have hc2 : DigsAt t2 KCOEF coefs :=
    ht.coef.frame (t1f.trans t2f) (by rw [hcl]; tl_omega) (fun _ _ _ h => by simp_all)
  have r18 : t2.getReg .x18 = BitVec.ofNat 64 A.leaf := by
    rw [t2r.get (by simp), t1r.get (by simp), g _ (by simp [tRegs, leafRegs]), hpre.x18]
  obtain ⟨t3, st3, t3pc, t3seed, t3r, t3f⟩ := khorn_run t2 t2pc (i := j) (by omega) t2x13 r18 hcl hc2 t2x1
  obtain ⟨t4, st4, t4pc, t4r, t4f⟩ := kg161_spec t3 t3pc
  have e14 : RegsExcept t t4 ([] ++ [.x1, .x13] ++ khornRegs ++ []) := ((t1r.trans t2r).trans t3r).trans t4r
  have f14 : Frame t t4 (fun X => X = CHAIN + 48 ∨ X = CHAIN + 56) :=
    (((t1f.trans t2f).trans t3f).trans t4f).mono (fun X _ h => by simp_all)
  have r19 : t4.getReg .x19 = BitVec.ofNat 64 j := by rw [e14.get (by simp [khornRegs])]; exact ht.x19
  have r22 : t4.getReg .x22 = BitVec.ofNat 64 A.digp := by
    rw [e14.get (by simp [khornRegs]), g _ (by simp [tRegs, leafRegs]), hpre.x22]
  obtain ⟨t5, st5, t5pc, t5x28, t5r, t5f⟩ := kg188_spec t4 t4pc j A.digp r19 r22
  have hdj : A.d j = 0 := by show A.digits.getD j 0 = 0; rw [hta.dig]; rfl
  have hw := hpre.hdigW j (by omega)
  have hdp := hpre.hdigp
  have hcdig := hta.cdig
  have hcdigL := hta.cdigL
  have hbyte : t5.getByte (BitVec.ofNat 64 (A.digp + j)) = BitVec.ofNat 8 0 := by
    rw [t5f.getByte (by omega) (fun h => h), f14.getByte (by omega) (fun h => hw (by
        simp only [LeafW, CHAIN, PRIV, SEEDS, LEAFPK, LOUT] at h ⊢; omega)),
      ht.frame.getByte (by omega) (fun h => by
        rcases h with h | h | h
        · exact hw h
        · simp only [LEAFPK] at h hcdigL; omega
        · simp only [KCOEF] at h hcdig; omega), hpre.hdig j (by omega), hdj]
  obtain ⟨t6, st6, t6pc, t6x17, t6r, t6f⟩ := sub72_spec subAt_keygen t5 t5pc (A.digp + j) (by omega) 0
    (by norm_num) t5x28 hbyte
  have r8 : t6.getReg .x8 = BitVec.ofNat 64 0 := by
    rw [t6r.get (by simp), t5r.get (by simp), e14.get (by simp [khornRegs]), g _ (by simp [tRegs, leafRegs]),
      hpre.x8, h0.1]; rfl
  obtain ⟨t7, st7, t7pc, t7x21, t7r, t7f⟩ := sub73_spec subAt_keygen t6 t6pc 0 (by norm_num) r8
  rw [if_pos rfl] at t7pc
  obtain ⟨t8, st8, t8pc, t8r, t8f⟩ := kg192_spec t7 t7pc
  obtain ⟨t9, st9, t9pc, t9x21, t9r, t9f⟩ := kgCap_spec t8 t8pc j (by omega)
    (by rw [t8r.get (by simp), t7r.get (by simp), t6r.get (by simp), t5r.get (by simp)]; exact r19)
  have e49 : RegsExcept t4 t9 ([.x28] ++ [.x17] ++ [.x21] ++ [] ++ [.x21, .x30]) :=
    (((t5r.trans t6r).trans t7r).trans t8r).trans t9r
  have r31 : t9.getReg .x31 = BitVec.ofNat 64 (if false then 1 else 0) := by
    rw [e49.get (by simp), e14.get (by simp [khornRegs]), g _ (by simp [tRegs, leafRegs]), hpre.x31, hta.so]
  obtain ⟨t10, st10, t10pc, t10r, t10f⟩ := sub76_spec subAt_keygen t9 t9pc false r31
  simp only [Bool.false_eq_true, if_false] at t10pc
  obtain ⟨t11, st11, t11pc, t11x1, t11r, t11f⟩ := sub78_spec subAt_keygen t10 t10pc
  have e111 : RegsExcept t t11 preRegs :=
    ((e14.trans e49).trans (t10r.trans t11r)).mono (by simp [preRegs, khornRegs])
  have f111 : Frame t t11 (fun X => X = CHAIN + 48 ∨ X = CHAIN + 56) :=
    (f14.trans ((((((t5f.trans t6f).trans t7f).trans t8f).trans t9f).trans t10f).trans t11f)).mono
      (fun X _ h => by simp_all)
  have g11 : ∀ r, r ∉ preRegs → r ∉ tRegs → t11.getReg r = s0.getReg r := fun r h1 h2 =>
    (e111.get h1).trans (g r h2)
  have hL : ∀ X, (X = CHAIN ∨ X = CHAIN + 8) →
      t11.getMem (BitVec.ofNat 64 X) = s0.getMem (BitVec.ofNat 64 X) := by
    intro X hX
    have hX' : X < 2 ^ 64 := by rcases hX with h | h <;> (rw [h]; decide)
    rw [f111.get hX' (by simp only [CHAIN] at hX ⊢; omega), ht.frame.get hX' (fun h => by
      rcases h with h | h | h
      · unfold LeafW at h
        rw [if_pos h0.1] at h
        tl_omega
      · tl_omega
      · tl_omega)]
  have hcp : ChainPre t11 0 0 A.leaf j 0 (maxDigit 0 j) (A.valp + 16 * j) (117 + 79) :=
    { x5 := by rw [g11 _ (by simp [preRegs]) (by simp [tRegs, leafRegs]), hpre.x5]
      x1 := t11x1
      x8 := by
        rw [t11r.get (by simp), t10r.get (by simp), e49.get (by simp), e14.get (by simp [khornRegs]),
          g _ (by simp [tRegs, leafRegs]), hpre.x8, h0.1]
      x9 := by rw [g11 _ (by simp [preRegs]) (by simp [tRegs, leafRegs]), hpre.x9, h0.2]
      x18 := by rw [g11 _ (by simp [preRegs]) (by simp [tRegs, leafRegs]), hpre.x18]
      x17 := by rw [t11r.get (by simp), t10r.get (by simp), t9r.get (by simp), t8r.get (by simp),
        t7r.get (by simp), t6x17]
      x19 := by rw [e111.get (by simp [preRegs])]; exact ht.x19
      x21 := by rw [t11r.get (by simp), t10r.get (by simp), t9x21]
      x23 := by rw [e111.get (by simp [preRegs])]; exact ht.x23
      htree := by norm_num
      hi := by omega
      l0 := rfl
      t0 := rfl
      hroute := by have := hpre.hroute; rw [h0.1, h0.2] at this; simpa using this
      hleaf := by have := hpre.hleafHeight; rw [h0.1] at this; exact this
      hcap := Nat.zero_le _
      he := rfl
      hv8 := by omega
      hv := by omega
      hvc := by tl_omega
      z0 := by rw [hL _ (by simp), hpre.z0]
      z8 := by rw [hL _ (by simp), hpre.z8] }
  have hseed : DigAt t11 (CHAIN + 48) (topSeed coefs A.leaf j) :=
    t3seed.frame (((((((t4f.trans t5f).trans t6f).trans t7f).trans t8f).trans t9f).trans t10f).trans t11f)
      (by decide) (by simp) (by simp)
  have hch := chainRun_tsim subAt_keygen sk hcp t11pc (topSeed coefs A.leaf j) hseed
  rw [topBody_eq]
  refine (TSim.steps (((((((((st1.trans st2).trans st3).trans st4).trans st5).trans st6).trans st7).trans
    st8).trans st9).trans (st10.trans st11)) (TSim.bind (k₂ := 16) (c₂ := 16) (n₂ := 0) (b₂ := 0) hch
    (fun r u hu => ?_))).of_eq rfl ?_ ?_ (by omega) (by omega)
  · obtain ⟨hupc, hv, hl, hur, huf⟩ := hu
    obtain ⟨w, stw, wpc, hw⟩ := ktop_post sk hpre hta hcl hel (j := j) (by omega) ht hupc
      ((e111.trans hur).mono (by simp [preRegs, chainRegs])) ((f111.trans huf).mono (fun _ _ h => h))
      r.1 r.2 hv hl
    exact TSim.pure_steps stw ⟨wpc, hw⟩
  · unfold titerK topPoint; omega
  · unfold titerC topPoint; omega
end top

section top
variable (sk : BitVec 256) {s0 : MachineState} {A : LeafArgs} (hpre : TopPre sk s0 A) (hta : TopArgs A)
  {coefs extra : List Digest} (hcl : coefs.length = 31) (hel : extra.length ≤ 1)
include hpre hta hcl hel

/-- Leaf exit (158 with all 51 chains done): leaf hash of the chain ends into `dest`, return. -/
theorem ktop_exit {st : List Digest × List Digest} {t : MachineState} (ht : TInv s0 A coefs extra 51 st t)
    (hpc : t.pc = pcOf 158) :
    TSim image sk t 19 (18 + 8 * leafBlocks A.lay) 1 (leafBlocks A.lay)
      (leafHash 0 0 A.leaf st.1 >>= fun root => pure (root, st.2))
      (fun r u => u.pc = pcOf A.ret ∧ DigAt u A.dest r.1 ∧ DigsAt u A.valp r.2 ∧ RegsExcept s0 u tRegs ∧
        Frame s0 u (TW A) ∧ DigsAt u KCOEF coefs ∧ DigsAt u (KCOEF + 496) extra) := by
  have hn : A.n = 51 := by show chainCount A.lay = 51; rw [hpre.top0.1]; rfl
  have h0 := hpre.top0
  have g : ∀ r, r ∉ tRegs → t.getReg r = s0.getReg r := fun r hr => ht.regs.get hr
  have r26 : t.getReg .x26 = BitVec.ofNat 64 51 := by
    rw [g _ (by simp [tRegs, leafRegs]), hpre.x26, hn]
  have r31 : t.getReg .x31 = BitVec.ofNat 64 (if false then 1 else 0) := by
    rw [g _ (by simp [tRegs, leafRegs]), hpre.x31, hta.so]
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := sub41_spec subAt_keygen t hpc 51 51 (by omega) (by omega) ht.x19 r26
  rw [if_neg (lt_irrefl _)] at t1pc
  obtain ⟨t2, st2, t2pc, t2r, t2f⟩ := sub95_spec subAt_keygen t1 t1pc false (by rw [t1r.get (by simp)]; exact r31)
  simp only [Bool.false_eq_true, if_false] at t2pc
  have e12 : RegsExcept t t2 [] := (t1r.trans t2r).mono (by simp)
  have f12 : Frame t t2 (fun _ => False) := (t1f.trans t2f).mono (fun X _ h => by simp_all)
  have r18 : t.getReg .x18 = BitVec.ofNat 64 A.leaf := by rw [g _ (by simp [tRegs, leafRegs]), hpre.x18]
  obtain ⟨t3, st3, t3pc, t3x10, t3x11, t3x12, t3x29, t3r, t3f⟩ := sub96_spec subAt_keygen t2 t2pc 51 (Or.inl rfl)
    (by rw [e12.get (by simp)]; exact r26) A.leaf (by rw [e12.get (by simp)]; exact r18)
  have r13 : RegsExcept t t3 [.x10, .x11, .x12, .x29] := (e12.trans t3r).mono (by simp)
  have f13 : Frame t t3 (fun _ => False) := (f12.trans t3f).mono (fun X _ h => by simp_all)
  have hlen : st.1.length = A.n := by rw [ht.elen, hn]
  have hvs := hpre.hvs
  have hds := hpre.hds
  have hdv := hpre.hdv
  have hcv := hta.cv
  have hcd := hta.cd
  have hw : t3.readWords (BitVec.ofNat 64 LEAFPK) (8 * leafBlocks A.lay) =
      wordsOf (pad64 (T3.leafInput A.lay A.tree A.leaf st.1)) := by
    rw [leafInput_words A h0.1 st.1 hlen]
    have h0d : DigAt t3 LEAFPK (st.1.getD 0 0) := by
      have e0 : tslot 0 = LEAFPK := rfl
      have := (ht.ends 0 (by omega)).frame f13 (by rw [e0]; decide) (by simp) (by simp)
      rw [e0] at this
      exact this
    have hall : DigsAt t3 (LEAFPK + 32) (st.1.drop 1) := by
      intro c hc
      simp only [List.length_drop] at hc
      have e1 : tslot (c + 1) = LEAFPK + 32 + 16 * c := by unfold tslot; rw [if_neg (by omega)]; omega
      have := (ht.ends (c + 1) (by omega)).frame f13 (by rw [e1]; simp only [LEAFPK]; omega) (by simp)
        (by simp)
      rw [e1] at this
      simpa [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_comm] using this
    have hhd : t3.readWords (BitVec.ofNat 64 (LEAFPK + 16)) 2 =
        [T3.hyperWord A.lay.val (A.tree * 2 ^ T3.height A.lay + A.leaf), 0] := by
      rw [readWords_two, f13.get (by decide) (by simp), f13.get (by decide) (by simp), ht.lh16,
        show LEAFPK + 16 + 8 = LEAFPK + 24 from rfl, ht.lh24]
    have hb : 8 * leafBlocks A.lay = 2 + (2 + 2 * (st.1.drop 1).length) := by
      simp only [List.length_drop, hlen, leafBlocks, show chainCount A.lay = A.n from rfl, hn]
    rw [hb, readWords_add, readWords_add, h0d.words, hhd,
      show LEAFPK + 8 * 2 + 8 * 2 = LEAFPK + 32 from rfl, hall.words, List.append_assoc]
  have hl := leafInput_length A h0.1 st.1 hlen
  have hnb : leafBlocks A.lay = 13 := by unfold leafBlocks; rw [show chainCount A.lay = A.n from rfl, hn]
  have hq : hashInput t3 = toQ (pad64 (T3.leafInput A.lay A.tree A.leaf st.1)) := by
    refine hashInput_toQ t3 _ (leafBlocks A.lay - 1) LEAFPK (by rw [hl]; omega) t3x10 (by decide)
      (by decide) ?_ (by omega) (by rw [show 8 * (leafBlocks A.lay - 1 + 1) = 8 * leafBlocks A.lay by omega]; exact hw)
    rw [t3x11, hnb] <;> rfl
  have hblk : (toQ (pad64 (T3.leafInput A.lay A.tree A.leaf st.1))).blocks = leafBlocks A.lay := by
    rw [blocks_toQ ⟨by rw [hl]; omega, by rw [hl]; omega⟩, hl]; omega
  have hv : hashArgumentsValid t3 = true := by
    refine hashArgs_const t3 LEAFPK (64 * leafBlocks A.lay) LOUT t3x10 ?_ t3x12 (by decide) (by omega)
      (by simp only [LEAFPK]; omega) (by decide) (by decide)
    rw [t3x11, hnb] <;> rfl
  have h5 : t3.getReg .x5 = 0 := by rw [r13.get (by simp), g _ (by simp [tRegs, leafRegs]), hpre.x5]
  have hlh : leafHash 0 0 A.leaf st.1 =
      T3.projHash (T3.leafHalfHigh 0 A.leaf) (T3.leafInput A.lay A.tree A.leaf st.1) := by
    rw [h0.1, h0.2]; rfl
  rw [hlh]
  refine (TSim.steps (st1.trans (st2.trans st3)) (tsim_projHash_bind (k := 7) (c := 7) (n := 0) (b := 0)
    (f := fun root => pure (root, st.2)) (fetch_sub105 subAt_keygen t3 t3pc) h5 hv hq (fun a => ?_))).of_eq rfl
    (by omega) (by rw [hblk]; omega) (by omega) (by rw [hblk]; omega)
  have hdb := hpre.hd
  have hd8 := hpre.hd8
  have hwf := Frame.writeHash t3 a LOUT t3x12 (by decide)
  obtain ⟨u2, st5, u2pc, u2a, u2b, u2r, u2f⟩ := sub106_spec subAt_keygen (writeHash t3 a)
    (by rw [pc_writeHash, t3pc, pcOf_add4]) A.dest hd8 hdb (by tl_omega)
    (by rw [getReg_writeHash, r13.get (by simp), g _ (by simp [tRegs, leafRegs]), hpre.x25])
    (A.leaf % 2) (Nat.mod_lt _ (by decide)) (by rw [getReg_writeHash]; exact t3x29)
    (by rw [getReg_writeHash]; exact t3x12)
  have hd2 : DigAt u2 A.dest (T3.projHalf (T3.leafHalfHigh 0 A.leaf) a) := by
    rcases Nat.mod_two_eq_zero_or_one A.leaf with hp | hp
    · have hhi := DigAt.writeHash_hi t3 a LOUT t3x12 (by decide)
      have hh : T3.leafHalfHigh 0 A.leaf = true := by simp [T3.leafHalfHigh, hp]
      rw [hh, T3.projHalf_true]
      rw [hp] at u2a u2b
      exact ⟨u2a.trans hhi.1, by rw [u2b]; exact hhi.2⟩
    · have hlo := DigAt.writeHash_lo t3 a LOUT t3x12 (by decide)
      have hh : T3.leafHalfHigh 0 A.leaf = false := by simp [T3.leafHalfHigh, hp]
      rw [hh, T3.projHalf_false]
      rw [hp] at u2a u2b
      exact ⟨u2a.trans hlo.1, by rw [u2b]; exact hlo.2⟩
  obtain ⟨u3, st6, u3pc, u3r, u3f⟩ := sub112_spec subAt_keygen u2 u2pc A.ret
    (by rw [u2r.get (by simp), getReg_writeHash, r13.get (by simp)]; exact ht.x3)
  have fall : Frame t u3 (fun X => (LOUT ≤ X ∧ X < LOUT + 32) ∨ (X = A.dest ∨ X = A.dest + 8)) :=
    ((f13.trans hwf).trans (u2f.trans u3f)).mono (fun X _ h => by
      rcases h with (h | h) | (h | h)
      · exact h.elim
      · left; exact h
      · right; exact h
      · exact h.elim)
  refine TSim.pure_steps (st5.trans st6) ⟨u3pc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hd2.frame u3f (by omega) (by simp) (by simp)
  · have hvb := hpre.hv
    exact ht.vals.frame fall (by rw [ht.vlen]; omega) (fun X h1 h2 => by rw [ht.vlen] at h2; tl_omega)
  · have hw0 : RegsExcept t3 (writeHash t3 a) [] := fun r _ => getReg_writeHash t3 a r
    exact ((ht.regs.trans r13).trans ((hw0.trans u2r).trans u3r)).mono (by simp [tRegs, leafRegs])
  · refine (ht.frame.trans fall).mono (fun X _ h => ?_)
    rcases h with h | h | h
    · exact h
    · left; unfold LeafW; right; right; right; right; right; right; right; left; exact h
    · left; unfold LeafW; right; right; right; right; right; right; right; right; right
      rcases h with h | h <;> omega
  · exact ht.coef.frame fall (by rw [hcl]; tl_omega) (fun X h1 h2 h => by rw [hcl] at h2; tl_omega)
  · exact ht.ext.frame fall (by tl_omega) (fun X h1 h2 h => by tl_omega)
end top

theorem buildLeafTopC_eq' (leaf : Nat) (coefs : List Digest) : buildLeafTopC leaf coefs [] = (do
    let state ← (List.range 51).foldlM (topBody leaf coefs) ([], [])
    leafHash 0 0 leaf state.1 >>= fun root => pure (root, state.2)) := rfl

/-- Steps of a keygen top leaf (`r = leaf % 4`, `o = leaf / 4 % 2`). -/
def topLeafK (r o : Nat) : Nat := 14 + ((if r = 0 then kfK o else 5) + (sumTo (titerK r) 51 + 19))
/-- Cycles of a keygen top leaf. -/
def topLeafC (r o : Nat) : Nat := 14 + ((if r = 0 then kfC o else 5) + (sumTo (titerC r) 51 + (18 + 8 * 13)))
/-- Hash calls of a keygen top leaf. -/
def topLeafN (r o : Nat) : Nat := (if r = 0 then 16 - o else 0) + (sumTo (fun j => maxDigit 0 j) 51 + 1)
/-- Compression blocks of a keygen top leaf. -/
def topLeafB (r o : Nat) : Nat := (if r = 0 then 16 - o else 0) + (sumTo (fun j => maxDigit 0 j) 51 + 13)

section top
variable (sk : BitVec 256) {s0 : MachineState} {A : LeafArgs} (hpre : TopPre sk s0 A) (hta : TopArgs A)
include hpre hta

/-- img-v6: one keygen top leaf (entry 144, return to `A.ret`): KTOP (`topFamilyCoefs`, the family coefficients and
carry in the buffer at KCOEF) then the leaf (`buildLeafTopC`), with exact counts. -/
theorem topLeaf_tsim (hpc : s0.pc = pcOf 144) {cc : List Digest × Digest} (hk : KcPre s0 A.leaf cc) :
    TSim image sk s0 (topLeafK (A.leaf % 4) (A.leaf / 4 % 2)) (topLeafC (A.leaf % 4) (A.leaf / 4 % 2))
      (topLeafN (A.leaf % 4) (A.leaf / 4 % 2)) (topLeafB (A.leaf % 4) (A.leaf / 4 % 2))
      (topFamilyCoefs A.leaf cc >>= fun cc' => buildLeafTopC A.leaf cc'.1 [] >>= fun r => pure (r, cc'))
      (fun rc t => t.pc = pcOf A.ret ∧ DigAt t A.dest rc.1.1 ∧ DigsAt t A.valp rc.1.2 ∧ KcPost t A.leaf rc.2 ∧
        RegsExcept s0 t tRegs ∧ Frame s0 t (TW A)) := by
  have hn : A.n = 51 := by show chainCount A.lay = 51; rw [hpre.top0.1]; rfl
  have h0 := hpre.top0
  have hlay : A.lay.val < 256 := by have := A.lay.isLt; omega
  have hnb : leafBlocks A.lay = 13 := by unfold leafBlocks; rw [show chainCount A.lay = A.n from rfl, hn]
  obtain ⟨t1, st1, t1pc, t1x1, t1x3, t1l16, t1l24, t1r, t1f⟩ :=
    kg27_spec s0 hpc A.lay.val A.leaf hlay hpre.hleaf hpre.x8 hpre.x18
  have hleaf : A.leaf < 4096 := by have := hpre.hleafHeight; rw [h0.1] at this; exact this
  have fp : ∀ X, X < PRIV + 64 → t1.getMem (BitVec.ofNat 64 X) = s0.getMem (BitVec.ofNat 64 X) := fun X hX =>
    t1f.get (by simp only [PRIV] at hX; omega) (by simp only [PRIV, LEAFPK] at hX ⊢; omega)
  have hp : KPriv sk t1 :=
    { x5 := by rw [t1r.get (by simp), hpre.x5]
      p0 := by rw [fp _ (by decide), hpre.p0]
      p8 := by rw [fp _ (by decide), hpre.p8]
      p32 := by rw [fp _ (by decide), hpre.p32]
      p40 := by rw [fp _ (by decide), hpre.p40]
      p48 := by rw [fp _ (by decide), hpre.p48]
      p56 := by rw [fp _ (by decide), hpre.p56] }
  have hk1 : KcPre t1 A.leaf cc := hk.frame t1f (fun X h1 h2 h => by simp only [LEAFPK, KCOEF] at h h1 h2; omega)
  have hkf := kfam_tsim sk t1pc hleaf (by rw [t1r.get (by simp)]; exact hpre.x18) hp t1x1 hk1
  refine (TSim.steps st1 (TSim.bind (k₂ := sumTo (titerK (A.leaf % 4)) 51 + 19)
    (c₂ := sumTo (titerC (A.leaf % 4)) 51 + (18 + 8 * leafBlocks A.lay)) (n₂ := sumTo (fun j => maxDigit 0 j) 51 + 1)
    (b₂ := sumTo (fun j => maxDigit 0 j) 51 + leafBlocks A.lay) hkf (fun cc' t ht => ?_))).of_eq rfl rfl
    (by rw [hnb]; rfl) rfl (by rw [hnb]; rfl)
  obtain ⟨tpc, ⟨hcl, hcoef, hslot⟩, t19, tr, tf⟩ := ht
  obtain ⟨extra, hel, hext, hpost⟩ : ∃ extra : List Digest, extra.length ≤ 1 ∧ DigsAt t (KCOEF + 496) extra ∧
      ∀ v, DigsAt v KCOEF cc'.1 → DigsAt v (KCOEF + 496) extra → KcPost v A.leaf cc' := by
    by_cases hs : (A.leaf + 4) / 4 % 2 = 1
    · refine ⟨[cc'.2], by simp, fun i hi => ?_, fun v h1 h2 => ⟨hcl, h1, fun _ => ?_⟩⟩
      · simp only [List.length_singleton] at hi
        have : i = 0 := by omega
        subst this; simpa using hslot hs
      · simpa using h2 0 (by simp)
    · exact ⟨[], by simp, DigsAt.nil _ _, fun v h1 _ => ⟨hcl, h1, fun h => absurd h hs⟩⟩
  have hinv : TInv s0 A cc'.1 extra 0 ([], []) t := by
    refine ⟨t19, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, fun c hc => absurd hc (by omega), DigsAt.nil _ _, hcoef, hext⟩
    · rw [tr.get (by simp [cgRegs]), t1r.get (by simp), hpre.x23]; simp
    · rw [tr.get (by simp [cgRegs]), t1x3, hpre.x1]
    · exact (t1r.trans tr).mono (by simp [tRegs, leafRegs, cgRegs])
    · refine (t1f.trans tf).mono (fun X _ h => ?_)
      rcases h with h | h
      · left; unfold LeafW; rw [if_pos h0.1]; simp only [LEAFPK, CHAIN] at h ⊢; omega
      · unfold CgW at h
        rcases h with h | h | h | h
        · left; unfold LeafW; left; exact h
        · left; unfold LeafW; right; left; exact h
        · left; unfold LeafW; right; right; left; exact h
        · right; right; exact h
    · rw [tf.get (by decide) (by unfold CgW; simp only [PRIV, SEEDS, KCOEF, LEAFPK]; omega), t1l16, h0.2]; simp
    · rw [tf.get (by decide) (by unfold CgW; simp only [PRIV, SEEDS, KCOEF, LEAFPK]; omega), t1l24]
  rw [buildLeafTopC_eq', bind_assoc]
  exact TSim.bind (TSim.foldlM_range 51 (topBody A.leaf cc'.1) ([], [])
    (fun j st t => t.pc = pcOf 158 ∧ TInv s0 A cc'.1 extra j st t) (titerK (A.leaf % 4)) (titerC (A.leaf % 4))
    (fun j => maxDigit 0 j) (fun j => maxDigit 0 j)
    (fun j hj st t ht => ktop_iter sk hpre hta hcl hel hj ht.2 ht.1) ⟨tpc, hinv⟩)
    (fun st u hu => TSim.bind (k₂ := 0) (c₂ := 0) (n₂ := 0) (b₂ := 0) (ktop_exit sk hpre hta hcl hel hu.2 hu.1)
      (fun r v hv => TSim.pure ⟨hv.1, hv.2.1, hv.2.2.1, hpost v hv.2.2.2.2.2.1 hv.2.2.2.2.2.2, hv.2.2.2.1,
        hv.2.2.2.2.1⟩))
end top

/-- Cycle bound of one keygen top leaf (COMPUTED by `decide` over the 8 leaf classes; campaign T51: max 205,853 at
`leaf % 4 = 3`). -/
def topLeafW : Nat := 205853
theorem topLeaf_bound (r o : Nat) (hr : r < 4) (ho : o < 2) :
    topLeafK r o ≤ topLeafC r o ∧ topLeafC r o ≤ topLeafW := by
  interval_cases r <;> interval_cases o <;> decide

end SigGolfCandidate.T3M.Keygen
end
-- ==== merged from T3M_Keygen_SimB ====
section

/-!
# Bounded-cycle refinement helpers (top-bytes layer, keygen)

The top-bytes keygen grinds a nonce per top-tree node, so its cycle, call and compression counts are data dependent.
These are the `TBSim` (= `Sim` on `mrealize`) combinators the keygen proof needs besides those in `T3M/Sim.lean`:
program rewriting, `map`, the public-hash query, a `mapM` over `List.range` with a constant per-element bound and a
`foldlM` over `List.range'` with a per-iteration bound.
-/

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec SigGolfCandidate.Rv
open SigGolfCandidate.T3 (M publicHash HashOutput)

section sim
variable {α β : Type} {image : Image}

theorem Sim.mapM_range' {δ : Type} (f : Nat → OracleComp HashSpec δ) (W : Nat)
    (Inv : List δ → MachineState → Prop) :
    ∀ (n a : Nat) (pre : List δ) {s : MachineState}, pre.length = a →
    (∀ (pre' : List δ) t, a ≤ pre'.length → pre'.length < a + n → Inv pre' t →
      Sim image t W (f pre'.length) (fun d u => Inv (pre' ++ [d]) u)) →
    Inv pre s →
    Sim image s (n * W) ((List.range' a n).mapM f) (fun ds u => ds.length = n ∧ Inv (pre ++ ds) u)
  | 0, a, pre, s, _, _, h0 => by
    simpa using Sim.pure (image := image) (Q := fun ds u => ds.length = 0 ∧ Inv (pre ++ ds) u)
      (a := []) (by simpa using h0)
  | n + 1, a, pre, s, hlen, hb, h0 => by
    rw [List.range'_succ, List.mapM_cons]
    have h1 := hb pre s (by omega) (by omega) h0
    rw [hlen] at h1
    have key : ∀ d t, Inv (pre ++ [d]) t → Sim image t (n * W)
        (do let ds ← (List.range' (a + 1) n).mapM f; Pure.pure (d :: ds))
        (fun ds u => ds.length = n + 1 ∧ Inv (pre ++ ds) u) := by
      intro d t ht
      have h2 := Sim.mapM_range' f W Inv n (a + 1) (pre ++ [d]) (by simp [hlen])
        (fun pre' t' h1' h2' => hb pre' t' (by omega) (by omega)) ht
      have := Sim.bind (W₂ := 0) h2 (f := fun ds => Pure.pure (d :: ds))
        (fun ds u hu => Sim.pure (image := image) (Q := fun ds u => ds.length = n + 1 ∧ Inv (pre ++ ds) u)
          ⟨by simp [hu.1], by simpa using hu.2⟩)
      simpa using this
    have := Sim.bind h1 key
    refine this.mono (by rw [Nat.succ_mul]; omega) (fun _ _ h => h)

theorem Sim.foldlM_range'_var {γ : Type} (a n : Nat) (f : γ → Nat → OracleComp HashSpec γ) (init : γ)
    (Inv : Nat → γ → MachineState → Prop) (W : Nat → Nat)
    (hbody : ∀ j < n, ∀ acc t, Inv j acc t → Sim image t (W j) (f acc (a + j)) (Inv (j + 1)))
    {s : MachineState} (h0 : Inv 0 init s) :
    Sim image s (sumTo W n) ((List.range' a n).foldlM f init) (Inv n) := by
  induction n with
  | zero => simpa [sumTo] using Sim.pure (image := image) h0
  | succ n ih =>
    rw [List.range'_concat, Nat.one_mul, List.foldlM_append]
    have := Sim.bind (ih (fun j hj => hbody j (by omega))) (f := fun acc => [a + n].foldlM f acc)
      (W₂ := W n) (Q₂ := Inv (n + 1)) (fun acc t ht => by
        simpa using hbody n (by omega) acc t ht)
    simpa [sumTo] using this
end sim

section tbsim
variable {α β : Type} {image : Image} {sk : BitVec 256}

theorem TBSim.of_eq {s : MachineState} {W : Nat} {p q : M α} {Q : α → MachineState → Prop}
    (h : TBSim image sk s W p Q) (he : p = q) : TBSim image sk s W q Q := he ▸ h

theorem TBSim.pure_stepsSimB {s t : MachineState} {k c : Nat} {a : α} {Q : α → MachineState → Prop}
    (h : Steps image s k c t) (hQ : Q a t) : TBSim image sk s c (Pure.pure a) Q :=
  Sim.pure_steps h hQ

theorem TBSim.map {s : MachineState} {W : Nat} {p : M α} (f : α → β)
    {Q : β → MachineState → Prop} (h : TBSim image sk s W p (fun a t => Q (f a) t)) :
    TBSim image sk s W (f <$> p) Q := by
  rw [map_eq_bind_pure_comp]
  have := TBSim.bind (W₂ := 0) h (f := Pure.pure ∘ f) (Q₂ := Q) (fun a t ht => TBSim.pure ht)
  simpa using this

theorem TBSim.publicHash_bindSimB {s : MachineState} {input : List UInt8} {W : Nat}
    {f : HashOutput → M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (T3.pad64 input))
    (h : ∀ a, TBSim image sk (writeHash s a) W (f a) Q) :
    TBSim image sk s (8 * (toQ (T3.pad64 input)).blocks + W) (publicHash input >>= f) Q := by
  unfold TBSim; rw [mrealize_bind, mrealize_publicHash]
  exact Sim.query_bind hf ht0 hv hq h

theorem TBSim.mapM_range {δ : Type} (n : Nat) (f : Nat → M δ) (W : Nat)
    (Inv : List δ → MachineState → Prop) {s : MachineState}
    (hbody : ∀ (pre : List δ) t, pre.length < n → Inv pre t →
      TBSim image sk t W (f pre.length) (fun d u => Inv (pre ++ [d]) u))
    (h0 : Inv [] s) :
    TBSim image sk s (n * W) ((List.range n).mapM f) (fun ds u => ds.length = n ∧ Inv ds u) := by
  unfold TBSim; rw [mrealize_mapM, List.range_eq_range']
  have := Sim.mapM_range' (image := image) (fun x => mrealize sk (f x)) W Inv n 0 [] rfl
    (fun pre' t _ h2 h3 => hbody pre' t (by omega) h3) h0
  simpa using this

theorem TBSim.foldlM_range'_var {γ : Type} (a n : Nat) (f : γ → Nat → M γ) (init : γ)
    (Inv : Nat → γ → MachineState → Prop) (W : Nat → Nat)
    (hbody : ∀ j < n, ∀ acc t, Inv j acc t → TBSim image sk t (W j) (f acc (a + j)) (Inv (j + 1)))
    {s : MachineState} (h0 : Inv 0 init s) :
    TBSim image sk s (sumTo W n) ((List.range' a n).foldlM f init) (Inv n) := by
  unfold TBSim; rw [mrealize_foldlM]
  exact Sim.foldlM_range'_var a n (fun acc x => mrealize sk (f acc x)) init Inv W hbody h0
end tbsim

section run
variable {α : Type}
/-- A bounded-cycle refinement determines the whole `runWith` result: the value, termination within `W + 1` cycles,
and the hash call / compression counts of `countBoth oa` evaluated at `hash`. -/
theorem Sim.runWith_eval (submission : Submission) (phase : Phase) (input : Input submission.sizes phase)
    {s : MachineState} (hinit : initialState submission phase input = some s) {W : Nat}
    {oa : OracleComp HashSpec α} {Q : α → MachineState → Prop}
    (hsim : Sim (submission.image phase) s W oa Q) (hW : W + 1 < CYCLE_LIMIT)
    (F : α → Output submission.sizes phase)
    (hQ : ∀ a t, Q a t → fetch (submission.image phase) t = some (.base .ECALL) ∧ t.getReg .x5 = 1 ∧
      t.getReg .x10 = 0 ∧ readOutput submission.sizes submission.layout phase t = F a)
    (hash : Hash) :
    (submission.runWith hash phase input).value = some (F (evalWithAnswerFn hash oa)) ∧
    (submission.runWith hash phase input).finished = true ∧
    (submission.runWith hash phase input).cycles ≤ W + 1 ∧
    (submission.runWith hash phase input).hashCalls = (evalWithAnswerFn hash (countBoth oa)).2.1 ∧
    (submission.runWith hash phase input).hashCompressions = (evalWithAnswerFn hash (countBoth oa)).2.2 := by
  obtain ⟨oc, hp, hf⟩ := hsim
  have hc : evalWithAnswerFn hash (countBoth oa) =
      ((evalWithAnswerFn hash oc).1.val, (evalWithAnswerFn hash oc).1.calls, (evalWithAnswerFn hash oc).1.blocks) := by
    rw [← hp, evalWithAnswerFn_map]
  have hv : evalWithAnswerFn hash oa = (evalWithAnswerFn hash oc).1.val := by
    rw [← fst_countBoth oa, evalWithAnswerFn_map, hc]
  rw [hc, hv, runWith_eq submission hash phase input s hinit, hf CYCLE_LIMIT (by omega),
    evalWithAnswerFn_bind, evalWithAnswerFn_map]
  generalize evalWithAnswerFn hash oc = o
  obtain ⟨h1, h2, h3, h4⟩ := hQ _ _ o.2.2.2
  have hs : o.1.steps < CYCLE_LIMIT := by have := o.2.1; have := o.2.2.1; omega
  obtain ⟨f, hf'⟩ : ∃ f, CYCLE_LIMIT - o.1.steps = f + 1 := ⟨CYCLE_LIMIT - o.1.steps - 1, by omega⟩
  rw [hf', evalWith_halt hash f h1 h2]
  have := o.2.2.1
  simp only [toRunResult, Execution.charge, h3, if_true, h4]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl | omega
end run
end SigGolfCandidate.T3M
end
-- ==== merged from T3M_Keygen_TopTree ====
section

/-!
# Keygen top tree with node nonces (top-bytes layer, opus-topbytes A)

The keygen tree routine (subroutine at 117, offsets 113..159) is hooked at three words:
* 230 (`b + 113`) `jal 721` (KINIT: `s4 = 1`, `a3 = 1`, back to 231);
* 274 (`b + 157`) `jal 724` (KNEXT: `s4 >>= 1`, `a3 += 1`, back to 233);
* 264 (`b + 147`, right after the node hash) `jal 727` (KCHK): `a3` is the height `h` of the node level. For `h = 12`
  (the root) go straight to KOK; else `b = min (max h 2) 8`, the mask `a6` (top `b` bits of the high word, or
  `0xFF << 40` for `h = 11`) and the cap `a7 = 104 << b`; then the trial loop 746..759: test the high word of the
  selected half, on failure `pad += 1` (`NODE + 32`) and rehash unless `pad` reached the cap (then the last trial is
  kept). KOK 760..769 resets the pad and runs the original node store, then 272..273.

This file proves the blocks and the bounded refinement (`TBSim`) of `T3.buildTopLevels`.
-/

namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Digest nodeHash topZeroBits topNonceCap topZeroOk nonceBytes topNodeInput topNodeHashN
  topNonceSearch topNodeAt buildTopLevel buildTopLevels pad64 zero16)
open SphincsSecurity (bytesLE bytesLE_length)

local instance instDecidableCodeAtTopTree (image : Image) (pc : Word) (code : List (BitVec 32)) :
    Decidable (CodeAt image pc code) := by
  unfold CodeAt
  infer_instance

/-! ## Blocks -/
def kt230 : List (BitVec 32) := sub113K.take 1
def kt231 : List (BitVec 32) := sub113K.drop 1
def kt264 : List (BitVec 32) := sub147K.take 1
def kt272 : List (BitVec 32) := sub147K.drop 8
def kt274 : List (BitVec 32) := sub157K.take 1
def ktI : List (BitVec 32) := kchkCode.take 3
def ktN : List (BitVec 32) := (kchkCode.drop 3).take 3
def ktC0 : List (BitVec 32) := (kchkCode.drop 6).take 2
def ktC1 : List (BitVec 32) := (kchkCode.drop 8).take 3
def ktC2 : List (BitVec 32) := (kchkCode.drop 11).take 1
def ktC3 : List (BitVec 32) := (kchkCode.drop 12).take 2
def ktC5 : List (BitVec 32) := (kchkCode.drop 15).take 6
def ktC6 : List (BitVec 32) := (kchkCode.drop 21).take 2
def ktC7 : List (BitVec 32) := (kchkCode.drop 23).take 2
def ktL0 : List (BitVec 32) := (kchkCode.drop 25).take 4
def ktL1 : List (BitVec 32) := (kchkCode.drop 29).take 4
def ktL2 : List (BitVec 32) := (kchkCode.drop 33).take 4
def ktL3 : List (BitVec 32) := (kchkCode.drop 38).take 1
def ktOK : List (BitVec 32) := (kchkCode.drop 39).take 10

theorem codeAt_kt230 : CodeAt image (pcOf 230) kt230 := by decide +kernel
theorem codeAt_kt231 : CodeAt image (pcOf 231) kt231 := by decide +kernel
theorem codeAt_kt264 : CodeAt image (pcOf 264) kt264 := by decide +kernel
theorem codeAt_kt272 : CodeAt image (pcOf 272) kt272 := by decide +kernel
theorem codeAt_kt274 : CodeAt image (pcOf 274) kt274 := by decide +kernel
theorem codeAt_ktI : CodeAt image (pcOf 721) ktI := by decide +kernel
theorem codeAt_ktN : CodeAt image (pcOf 724) ktN := by decide +kernel
theorem codeAt_ktC0 : CodeAt image (pcOf 727) ktC0 := by decide +kernel
theorem codeAt_ktC1 : CodeAt image (pcOf 729) ktC1 := by decide +kernel
theorem codeAt_ktC2 : CodeAt image (pcOf 732) ktC2 := by decide +kernel
theorem codeAt_ktC3 : CodeAt image (pcOf 733) ktC3 := by decide +kernel
theorem codeAt_ktC5 : CodeAt image (pcOf 736) ktC5 := by decide +kernel
theorem codeAt_ktC6 : CodeAt image (pcOf 742) ktC6 := by decide +kernel
theorem codeAt_ktC7 : CodeAt image (pcOf 744) ktC7 := by decide +kernel
theorem codeAt_ktL0 : CodeAt image (pcOf 746) ktL0 := by decide +kernel
theorem codeAt_ktL1 : CodeAt image (pcOf 750) ktL1 := by decide +kernel
theorem codeAt_ktL2 : CodeAt image (pcOf 754) ktL2 := by decide +kernel
theorem codeAt_kt758 : CodeAt image (pcOf 758) [115] := by decide +kernel
theorem codeAt_ktL3 : CodeAt image (pcOf 759) ktL3 := by decide +kernel
theorem codeAt_ktOK : CodeAt image (pcOf 760) ktOK := by decide +kernel

sym_block bt230 := symRun { noAlias := true } kt230 (pcOf 230) 100
sym_block bt231 := symRun { noAlias := true } kt231 (pcOf 231) 100
sym_block bt264 := symRun { noAlias := true } kt264 (pcOf 264) 100
sym_block bt272 := symRun { noAlias := true } kt272 (pcOf 272) 100
sym_block bt274 := symRun { noAlias := true } kt274 (pcOf 274) 100
sym_block btI := symRun { noAlias := true } ktI (pcOf 721) 100
sym_block btN := symRun { noAlias := true } ktN (pcOf 724) 100
sym_block btC0 := symRun { noAlias := true } ktC0 (pcOf 727) 100
sym_block btC1 := symRun { noAlias := true } ktC1 (pcOf 729) 100
sym_block btC2 := symRun { noAlias := true } ktC2 (pcOf 732) 100
sym_block btC3 := symRun { noAlias := true } ktC3 (pcOf 733) 100
sym_block btC5 := symRun { noAlias := true } ktC5 (pcOf 736) 100
sym_block btC6 := symRun { noAlias := true } ktC6 (pcOf 742) 100
sym_block btC7 := symRun { noAlias := true } ktC7 (pcOf 744) 100
sym_block btL0 := symRun { noAlias := true } ktL0 (pcOf 746) 100
sym_block btL1 := symRun { noAlias := true } ktL1 (pcOf 750) 100
sym_block btL2 := symRun { noAlias := true } ktL2 (pcOf 754) 100
sym_block btL3 := symRun { noAlias := true } ktL3 (pcOf 759) 100
sym_block btOK := symRun { noAlias := true } ktOK (pcOf 760) 100

/-- Mask of the zero test on the high word of a top node of height `h` (`1 ≤ h ≤ 11`). Campaign T51: `h = 11` tests
node bits 104..111 (high-word mask `0xFF << 40`). -/
def maskN (h : Nat) : Nat :=
  if h = 11 then (2 ^ 8 - 1) * 2 ^ 40 else (2 ^ topZeroBits h - 1) * 2 ^ (64 - topZeroBits h)

/-! ### Jumps -/
theorem kt230_spec (s : MachineState) (hpc : s.pc = pcOf 230) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 721 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bt230 codeAt_kt230 s hpc (by simp [bt230.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [bt230.res, Result.toState_pc, E.eval]
  · intro r hr; cases r <;> simp_all [bt230.res, rv_simp] <;> rfl
  · intro A _ _; simp [bt230.res, rv_simp]
theorem kt264_spec (s : MachineState) (hpc : s.pc = pcOf 264) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 727 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bt264 codeAt_kt264 s hpc (by simp [bt264.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [bt264.res, Result.toState_pc, E.eval]
  · intro r hr; cases r <;> simp_all [bt264.res, rv_simp] <;> rfl
  · intro A _ _; simp [bt264.res, rv_simp]
theorem kt274_spec (s : MachineState) (hpc : s.pc = pcOf 274) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 724 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bt274 codeAt_kt274 s hpc (by simp [bt274.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [bt274.res, Result.toState_pc, E.eval]
  · intro r hr; cases r <;> simp_all [bt274.res, rv_simp] <;> rfl
  · intro A _ _; simp [bt274.res, rv_simp]
theorem ktL3_spec (s : MachineState) (hpc : s.pc = pcOf 759) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 746 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound btL3 codeAt_ktL3 s hpc (by simp [btL3.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [btL3.res, Result.toState_pc, E.eval]
  · intro r hr; cases r <;> simp_all [btL3.res, rv_simp] <;> rfl
  · intro A _ _; simp [btL3.res, rv_simp]
theorem fetch_kt758 (s : MachineState) (hpc : s.pc = pcOf 758) : fetch image s = some (.base .ECALL) :=
  (codeAt_kt758.fetch s hpc).trans rfl

/-! ### KINIT / KNEXT -/
theorem ktI_spec (s : MachineState) (hpc : s.pc = pcOf 721) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf 231 ∧ t.getReg .x20 = BitVec.ofNat 64 1 ∧
      t.getReg .x13 = BitVec.ofNat 64 1 ∧ RegsExcept s t [.x13, .x20] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound btI codeAt_ktI s hpc (by simp [btI.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [btI.res, Result.toState_pc, E.eval]
  · simp [btI.res, rv_simp]
  · simp [btI.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [btI.res, rv_simp] <;> rfl
  · intro A _ _; simp [btI.res, rv_simp]
theorem kt231_spec (s : MachineState) (hpc : s.pc = pcOf 231) (hh : Nat) (h1 : 1 ≤ hh) (h2 : hh ≤ 32)
    (h15 : s.getReg .x15 = BitVec.ofNat 64 hh) (h20 : s.getReg .x20 = BitVec.ofNat 64 1) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf 233 ∧ t.getReg .x20 = BitVec.ofNat 64 (2 ^ (hh - 1)) ∧
      RegsExcept s t [.x6, .x20] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bt231 codeAt_kt231 s hpc (by simp [bt231.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [bt231.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, bt231.res, rv_simp, h15, h20]
    apply BitVec.eq_of_toNat_eq
    have e : (BitVec.ofNat 64 hh - 1#64).toNat = hh - 1 := by
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
    have e' : (BitVec.ofNat 64 hh + BitVec.ofNat 64 18446744073709551615).toNat = hh - 1 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
    first
      | (rw [BitVec.toNat_shiftLeft, e', BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
          Nat.mod_eq_of_lt (show hh - 1 < 64 by omega)])
      | (rw [BitVec.toNat_shiftLeft, e, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
          Nat.mod_eq_of_lt (show hh - 1 < 64 by omega)])
    have : 2 ^ (hh - 1) < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
    simp only [Nat.one_mod, Nat.one_mul, Nat.mod_eq_of_lt this]
  · intro r hr; simp at hr; cases r <;> simp_all [bt231.res, rv_simp] <;> rfl
  · intro A _ _; simp [bt231.res, rv_simp]
theorem ktN_spec (s : MachineState) (hpc : s.pc = pcOf 724) (lo h : Nat) (hlo : lo < 2 ^ 64) (hh : h + 1 < 2 ^ 64)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 lo) (h13 : s.getReg .x13 = BitVec.ofNat 64 h) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf 233 ∧ t.getReg .x20 = BitVec.ofNat 64 (lo / 2) ∧
      t.getReg .x13 = BitVec.ofNat 64 (h + 1) ∧ RegsExcept s t [.x13, .x20] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound btN codeAt_ktN s hpc (by simp [btN.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [btN.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, btN.res, rv_simp, h20]
    rw [ofNat_shr _ _ hlo]; rfl
  · simp only [Result.toState_getReg, btN.res, rv_simp, h13]
    rw [ofNat_add_ofNat]
  · intro r hr; simp at hr; cases r <;> simp_all [btN.res, rv_simp] <;> rfl
  · intro A _ _; simp [btN.res, rv_simp]

/-! ### KCHK setup (727..745) -/
theorem kult (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = decide (a < b) := by
  simp only [BitVec.ult, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
theorem ktC0_spec (s : MachineState) (hpc : s.pc = pcOf 727) (h : Nat) (hh : h < 2 ^ 64)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 h) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if h = 12 then pcOf 760 else pcOf 729) ∧ RegsExcept s t [.x28] ∧
      Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound btC0 codeAt_ktC0 s hpc (by simp [btC0.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, btC0.res, E.eval, CmpOp.eval, RegFile.get, h13]
    by_cases hc : h = 12
    · subst hc; simp
    · have : BitVec.ofNat 64 h ≠ BitVec.ofNat 64 12 := by rw [Ne, ofNat_inj hh (by norm_num)]; exact hc
      simp [hc, this]
  · intro r hr; simp at hr; cases r <;> simp_all [btC0.res, rv_simp] <;> rfl
  · intro A _ _; simp [btC0.res, rv_simp]
/-- 729..731 (campaign T51): `a4 = h - 3`, `t3 = 3`, `blt a3, t3, 760` (heights 1, 2: no nonce search). -/
theorem ktC1_spec (s : MachineState) (hpc : s.pc = pcOf 729) (h : Nat) (hh : h < 2 ^ 63)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 h) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = (if h < 3 then pcOf 760 else pcOf 732) ∧
      (3 ≤ h → t.getReg .x14 = BitVec.ofNat 64 (h - 3)) ∧ RegsExcept s t [.x14, .x28] ∧
      Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound btC1 codeAt_ktC1 s hpc (by simp [btC1.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, btC1.res, E.eval, CmpOp.eval, RegFile.get, h13]
    rw [show (3#64 : Word) = BitVec.ofNat 64 3 from rfl, ofNat_slt h 3 hh (by norm_num)]
    by_cases hc : h < 3 <;> simp [hc]
  · intro h3
    simp only [Result.toState_getReg, btC1.res, rv_simp, h13]
    apply BitVec.eq_of_toNat_eq
    first
      | (rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega)
      | (rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega)
  · intro r hr; simp at hr; cases r <;> simp_all [btC1.res, rv_simp] <;> rfl
  · intro A _ _; simp [btC1.res, rv_simp]
/-- 732 (campaign T51): `bne a4, zero, 736` (`h = 3` falls through to 733). -/
theorem ktC2_spec (s : MachineState) (hpc : s.pc = pcOf 732) (b : Nat) (hb : b < 2 ^ 64)
    (h14 : s.getReg .x14 = BitVec.ofNat 64 b) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if b = 0 then pcOf 733 else pcOf 736) ∧ RegsExcept s t [] ∧
      Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound btC2 codeAt_ktC2 s hpc (by simp [btC2.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, btC2.res, E.eval, CmpOp.eval, RegFile.get, h14]
    by_cases hc : b = 0
    · subst hc; simp
    · have : BitVec.ofNat 64 b ≠ 0#64 := by
        rw [Ne, show (0#64) = BitVec.ofNat 64 0 from rfl, ofNat_inj hb (by norm_num)]; exact hc
      simp [hc, this]
  · intro r hr; cases r <;> simp_all [btC2.res, rv_simp] <;> rfl
  · intro A _ _; simp [btC2.res, rv_simp]
/-- 733..734 (campaign T51, `h = 3`): `a4 = 1`, `j 736`. -/
theorem ktC3_spec (s : MachineState) (hpc : s.pc = pcOf 733) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf 736 ∧ t.getReg .x14 = BitVec.ofNat 64 1 ∧ RegsExcept s t [.x14] ∧
      Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound btC3 codeAt_ktC3 s hpc (by simp [btC3.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [btC3.res, Result.toState_pc, E.eval]
  · simp [btC3.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [btC3.res, rv_simp] <;> rfl
  · intro A _ _; simp [btC3.res, rv_simp]
theorem ktC5_spec (s : MachineState) (hpc : s.pc = pcOf 736) (b h : Nat) (hb : 1 ≤ b) (hb' : b ≤ 11)
    (hh : h < 2 ^ 64) (h14 : s.getReg .x14 = BitVec.ofNat 64 b) (h13 : s.getReg .x13 = BitVec.ofNat 64 h) :
    ∃ t, Steps image s 6 6 t ∧ t.pc = (if h = 11 then pcOf 742 else pcOf 744) ∧
      t.getReg .x16 = BitVec.ofNat 64 ((2 ^ b - 1) * 2 ^ (64 - b)) ∧
      RegsExcept s t [.x16, .x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound btC5 codeAt_ktC5 s hpc (by simp [btC5.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, btC5.res, E.eval, CmpOp.eval, RegFile.get, h13]
    by_cases hc : h = 11
    · subst hc; simp
    · have : BitVec.ofNat 64 h ≠ BitVec.ofNat 64 11 := by rw [Ne, ofNat_inj hh (by norm_num)]; exact hc
      simp [hc, this]
  · simp only [Result.toState_getReg, btC5.res, rv_simp, h14]
    interval_cases b <;> decide
  · intro r hr; simp at hr; cases r <;> simp_all [btC5.res, rv_simp] <;> rfl
  · intro A _ _; simp [btC5.res, rv_simp]
theorem ktC6_spec (s : MachineState) (hpc : s.pc = pcOf 742) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf 744 ∧ t.getReg .x16 = BitVec.ofNat 64 ((2 ^ 8 - 1) * 2 ^ 40) ∧
      RegsExcept s t [.x16] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound btC6 codeAt_ktC6 s hpc (by simp [btC6.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [btC6.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, btC6.res, rv_simp]; decide
  · intro r hr; simp at hr; cases r <;> simp_all [btC6.res, rv_simp] <;> rfl
  · intro A _ _; simp [btC6.res, rv_simp]
theorem ktC7_spec (s : MachineState) (hpc : s.pc = pcOf 744) (b : Nat) (hb' : b ≤ 11)
    (h14 : s.getReg .x14 = BitVec.ofNat 64 b) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf 746 ∧ t.getReg .x17 = BitVec.ofNat 64 (104 * 2 ^ b) ∧
      RegsExcept s t [.x17] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound btC7 codeAt_ktC7 s hpc (by simp [btC7.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [btC7.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, btC7.res, rv_simp, h14]
    interval_cases b <;> decide
  · intro r hr; simp at hr; cases r <;> simp_all [btC7.res, rv_simp] <;> rfl
  · intro A _ _; simp [btC7.res, rv_simp]

/-! ### Trial loop (746..759), KOK (760..769) and 272..273 -/
theorem nout_sub (p : Nat) (hp : p < 2) :
    BitVec.ofNat 64 NOUT - BitVec.ofNat 64 (p * 2 ^ 4) = BitVec.ofNat 64 (NOUT - 16 * p) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, NOUT]
  rcases (show p = 0 ∨ p = 1 by omega) with rfl | rfl <;> norm_num
theorem ktL0_spec (s : MachineState) (hpc : s.pc = pcOf 746) (p : Nat) (hp : p < 2)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 NOUT) (h29 : s.getReg .x29 = BitVec.ofNat 64 (p * 2 ^ 4)) :
    ∃ t, Steps image s 4 4 t ∧
      t.pc = (if (s.getMem (BitVec.ofNat 64 (NOUT + 16 - 16 * p + 8)) &&& s.getReg .x16) = 0#64 then pcOf 760
        else pcOf 750) ∧
      RegsExcept s t [.x30] ∧ Frame s t (fun _ => False) := by
  have e : s.getReg .x12 - s.getReg .x29 = BitVec.ofNat 64 (NOUT - 16 * p) := by rw [h12, h29, nout_sub p hp]
  have hobl : Oblig.all s btL0.res.st.obl := by
    simp only [btL0.res]
    t3n [e]
    simp only [NOUT] at *
    omega
  refine ⟨_, symRun_sound btL0 codeAt_ktL0 s hpc hobl, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, btL0.res, E.eval, CmpOp.eval, RegFile.get]
    t3n [e]
    have ea : NOUT - 16 * p + 24 = NOUT + 16 - 16 * p + 8 := by simp only [NOUT]; omega
    rw [ea]
    split_ifs <;> simp_all
  · intro r hr; simp at hr; cases r <;> simp_all [btL0.res, rv_simp] <;> rfl
  · intro A _ _; simp [btL0.res, rv_simp]
theorem ktL1_spec (s : MachineState) (hpc : s.pc = pcOf 750) (n c : Nat) (hn : n + 1 < 2 ^ 64) (hc : c < 2 ^ 64)
    (hpad : s.getMem (BitVec.ofNat 64 (NODE + 32)) = BitVec.ofNat 64 n)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 c) :
    ∃ t, Steps image s 4 4 t ∧ t.pc = (if c ≤ n + 1 then pcOf 760 else pcOf 754) ∧
      t.getReg .x28 = BitVec.ofNat 64 0x20000 ∧ t.getReg .x30 = BitVec.ofNat 64 (n + 1) ∧
      RegsExcept s t [.x28, .x30] ∧ Frame s t (fun _ => False) := by
  have hobl : Oblig.all s btL1.res.st.obl := by
    simp only [btL1.res]
    t3n []
  have hm : memEval s btL1.res.st.mem (BitVec.ofNat 64 (NODE + 32)) = BitVec.ofNat 64 n := by
    simp only [btL1.res]; t3n [hpad]
  refine ⟨_, symRun_sound btL1 codeAt_ktL1 s hpc hobl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, btL1.res, E.eval, CmpOp.eval, RegFile.get, h17]
    t3n [hpad]
    rw [kult (n + 1) c hn hc]
    by_cases hcn : c ≤ n + 1
    · simp [hcn, show ¬ n + 1 < c by omega]
    · simp [hcn, show n + 1 < c by omega]
  · simp [btL1.res, rv_simp]
  · simp only [Result.toState_getReg, btL1.res]
    t3n [hpad]
  · intro r hr; simp at hr; cases r <;> simp_all [btL1.res, rv_simp] <;> rfl
  · intro A _ _; simp [btL1.res, rv_simp]
theorem ktL2_spec (s : MachineState) (hpc : s.pc = pcOf 754) (h28 : s.getReg .x28 = BitVec.ofNat 64 0x20000) :
    ∃ t, Steps image s 4 4 t ∧ t.pc = pcOf 758 ∧ t.getMem (BitVec.ofNat 64 (NODE + 32)) = s.getReg .x30 ∧
      t.getReg .x10 = BitVec.ofNat 64 NODE ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      RegsExcept s t [.x10, .x11] ∧ Frame s t (fun X => X = NODE + 32) := by
  have hobl : Oblig.all s btL2.res.st.obl := by
    simp only [btL2.res]
    t3n [h28]
    try decide
  refine ⟨_, symRun_sound btL2 codeAt_ktL2 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [btL2.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getMem, btL2.res, NODE]
    t3n [h28]
  · simp [btL2.res, rv_simp]
  · simp [btL2.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [btL2.res, rv_simp] <;> rfl
  · intro X hX hn
    simp only [NODE] at hn
    simp only [Result.toState_getMem, btL2.res]
    t3n [h28]
    rw [if_neg (by omega)]
theorem ktOK_spec (s : MachineState) (hpc : s.pc = pcOf 760) (arena k p : Nat) (hp : p < 2)
    (ha8 : arena % 8 = 0) (hk : arena + 16 * k + 16 ≤ 2 ^ 24)
    (hdis : NOUT + 32 ≤ arena + 16 * k ∨ arena + 16 * k + 16 ≤ NODE + 32)
    (h2 : s.getReg .x2 = BitVec.ofNat 64 arena) (h24 : s.getReg .x24 = BitVec.ofNat 64 k)
    (h29 : s.getReg .x29 = BitVec.ofNat 64 (p * 2 ^ 4)) (h12 : s.getReg .x12 = BitVec.ofNat 64 NOUT) :
    ∃ t, Steps image s 10 10 t ∧ t.pc = pcOf 272 ∧
      t.getMem (BitVec.ofNat 64 (NODE + 32)) = 0 ∧
      t.getMem (BitVec.ofNat 64 (arena + 16 * k)) = s.getMem (BitVec.ofNat 64 (NOUT + 16 - 16 * p)) ∧
      t.getMem (BitVec.ofNat 64 (arena + 16 * k + 8)) = s.getMem (BitVec.ofNat 64 (NOUT + 16 - 16 * p + 8)) ∧
      RegsExcept s t [.x6, .x7, .x28, .x29] ∧
      Frame s t (fun X => X = NODE + 32 ∨ X = arena + 16 * k ∨ X = arena + 16 * k + 8) := by
  have e : s.getReg .x12 - s.getReg .x29 = BitVec.ofNat 64 (NOUT - 16 * p) := by rw [h12, h29, nout_sub p hp]
  have hobl : Oblig.all s btOK.res.st.obl := by
    simp only [btOK.res]
    t3n [h2, h24, e]
    simp only [NOUT, NODE] at *
    omega
  refine ⟨_, symRun_sound btOK codeAt_ktOK s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [btOK.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getMem, btOK.res]
    t3n [h2, h24, e]
    simp only [NOUT, NODE] at hdis ⊢
    rw [if_neg (by omega), if_neg (by omega)]
  · simp only [Result.toState_getMem, btOK.res]
    t3n [h2, h24, e]
    simp only [NOUT, NODE] at hdis ⊢
    rw [if_neg (by omega), if_pos (by omega)]
    congr 2
    omega
  · simp only [Result.toState_getMem, btOK.res]
    t3n [h2, h24, e]
    simp only [NOUT, NODE] at hdis ⊢
    rw [if_pos (by omega)]
    congr 2
    omega
  · intro r hr; simp at hr; cases r <;> simp_all [btOK.res, rv_simp] <;> rfl
  · intro X hX hn
    simp only [Result.toState_getMem, btOK.res]
    t3n [h2, h24, e]
    simp only [NOUT, NODE] at hn ⊢
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
theorem kt272_spec (s : MachineState) (hpc : s.pc = pcOf 272) (k : Nat)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 k) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf 235 ∧ t.getReg .x24 = BitVec.ofNat 64 (k + 1) ∧
      RegsExcept s t [.x24] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bt272 codeAt_kt272 s hpc (by simp [bt272.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [bt272.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, bt272.res, rv_simp, h24]; rw [ofNat_add_ofNat]
  · intro r hr; simp at hr; cases r <;> simp_all [bt272.res, rv_simp] <;> rfl
  · intro A _ _; simp [bt272.res, rv_simp]

/-! ## The zero test, the setup and the node input -/
theorem land_mask_eq_zero (n k w : Nat) :
    n &&& ((2 ^ w - 1) * 2 ^ k) = 0 ↔ n / 2 ^ k % 2 ^ w = 0 := by
  have hM : (2 ^ w - 1) * 2 ^ k = (2 ^ w - 1) <<< k := by rw [Nat.shiftLeft_eq]
  rw [hM]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    have := congrArg (fun y => Nat.testBit y (j + k)) h
    simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, Nat.zero_testBit] at this
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.zero_testBit]
    by_cases hj : j < w
    · have e : j + k - k = j := by omega
      simp only [e, hj, decide_true, Bool.and_true, ge_iff_le, Nat.le_add_left] at this
      simp [hj, this]
    · simp [hj]
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, Nat.zero_testBit]
    by_cases hik : k ≤ i
    · by_cases hiw : i - k < w
      · have := congrArg (fun y => Nat.testBit y (i - k)) h
        simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.zero_testBit, hiw, decide_true,
          Bool.true_and] at this
        rw [show i - k + k = i by omega] at this
        simp [this]
      · simp [hiw]
    · simp [hik]
theorem hiword_toNat (v : BitVec 128) : (v.extractLsb' 64 64).toNat = v.toNat / 2 ^ 64 := by
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have := v.isLt
  apply Nat.mod_eq_of_lt
  omega
theorem zero_test_hi (v : BitVec 128) (b : Nat) (hb : b ≤ 64) :
    (v.extractLsb' 64 64 &&& BitVec.ofNat 64 ((2 ^ b - 1) * 2 ^ (64 - b)) = 0#64) ↔
      v.toNat / 2 ^ (128 - b) = 0 := by
  have hlt : (2 ^ b - 1) * 2 ^ (64 - b) < 2 ^ 64 := by
    have h1 : 2 ^ b - 1 < 2 ^ b := Nat.sub_lt (Nat.two_pow_pos _) (by norm_num)
    calc (2 ^ b - 1) * 2 ^ (64 - b) < 2 ^ b * 2 ^ (64 - b) :=
          Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos _)
      _ = 2 ^ 64 := by rw [← Nat.pow_add]; congr 1; omega
  rw [← BitVec.toNat_inj, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, hiword_toNat,
    BitVec.toNat_zero, land_mask_eq_zero, Nat.div_div_eq_div_mul, ← Nat.pow_add,
    show 64 + (64 - b) = 128 - b by omega]
  have hv : v.toNat / 2 ^ (128 - b) < 2 ^ b := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, show b + (128 - b) = 128 by omega]
    exact v.isLt
  rw [Nat.mod_eq_of_lt hv]
/-- Campaign T51: the `h = 11` zero test, high-word mask `0xFF << 40` = node bits 104..111. -/
theorem zero_test_bits104 (v : BitVec 128) :
    (v.extractLsb' 64 64 &&& BitVec.ofNat 64 ((2 ^ 8 - 1) * 2 ^ 40) = 0#64) ↔
      v.toNat / 2 ^ 104 % 2 ^ 8 = 0 := by
  rw [← BitVec.toNat_inj, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by norm_num), hiword_toNat,
    BitVec.toNat_zero, land_mask_eq_zero, Nat.div_div_eq_div_mul, ← Nat.pow_add]
/-- Campaign T51: `b_h = 0,0,1,1,2,3,4,5,6,7,8` (#938: `b_h = h`). -/
theorem topZeroBits_eq (h : Nat) (h1 : 1 ≤ h) (h11 : h ≤ 11) : topZeroBits h = SigGolfCandidate.T3.topZeroAlloc.getD h 0 := rfl
theorem topZeroBits_ge3 (h : Nat) (h3 : 3 ≤ h) (h11 : h ≤ 11) : topZeroBits h = if h = 3 then 1 else h - 3 := by
  interval_cases h <;> rfl
theorem ktopZeroBits_le (h : Nat) : topZeroBits h ≤ 8 := by
  unfold topZeroBits T3.topZeroAlloc
  rcases h with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | h <;> simp
/-- The machine's zero test (KCHK 746..749) is `topZeroOk`. -/
theorem zero_test (v : Digest) (h : Nat) (h1 : 1 ≤ h) (h11 : h ≤ 11) :
    (v.extractLsb' 64 64 &&& BitVec.ofNat 64 (maskN h) = 0#64) ↔ topZeroOk h v = true := by
  unfold maskN topZeroOk
  by_cases hc : h = 11
  · rw [if_pos hc, if_pos hc, zero_test_bits104, beq_iff_eq]
  · rw [if_neg hc, if_neg hc, zero_test_hi v _ (by have := ktopZeroBits_le h; omega), beq_iff_eq]
/-- Steps (= cycles) of the KCHK setup 727..745 at height `h ∈ 3..11` (campaign T51: `b = h - 3`, `h = 3` sets
`b = 1` at 733..734). -/
def setupK (h : Nat) : Nat :=
  14 + (if h = 3 then 2 else 0) + (if h = 11 then 2 else 0)
theorem setupK_le (h : Nat) : setupK h ≤ 18 := by unfold setupK; split_ifs <;> omega
theorem ksetup_spec (s : MachineState) (hpc : s.pc = pcOf 727) (h : Nat) (h3 : 3 ≤ h) (h11 : h ≤ 11)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 h) :
    ∃ t, Steps image s (setupK h) (setupK h) t ∧ t.pc = pcOf 746 ∧
      t.getReg .x16 = BitVec.ofNat 64 (maskN h) ∧ t.getReg .x17 = BitVec.ofNat 64 (topNonceCap h) ∧
      RegsExcept s t [.x14, .x16, .x17, .x28] ∧ Frame s t (fun _ => False) := by
  obtain ⟨t1, st1, p1, r1, f1⟩ := ktC0_spec s hpc h (by omega) h13
  rw [if_neg (by omega)] at p1
  obtain ⟨t2, st2, p2, x14_2, r2, f2⟩ := ktC1_spec t1 p1 h (by omega) (by rw [r1.get (by simp)]; exact h13)
  rw [if_neg (by omega)] at p2
  obtain ⟨t3, st3, p3, r3, f3⟩ := ktC2_spec t2 p2 (h - 3) (by omega) (x14_2 h3)
  have hb := topZeroBits_ge3 h h3 h11
  obtain ⟨t4, st4, p4, x14_4, r4, f4⟩ : ∃ t4, Steps image t3 (if h = 3 then 2 else 0) (if h = 3 then 2 else 0) t4 ∧
      t4.pc = pcOf 736 ∧ t4.getReg .x14 = BitVec.ofNat 64 (topZeroBits h) ∧ RegsExcept t3 t4 [.x14] ∧
      Frame t3 t4 (fun _ => False) := by
    by_cases hc : h = 3
    · rw [if_pos (show h - 3 = 0 by omega)] at p3
      obtain ⟨u, su, pu, xu, ru, fu⟩ := ktC3_spec t3 p3
      exact ⟨u, by rw [if_pos hc]; exact su, pu, by rw [xu, hb, if_pos hc], ru, fu⟩
    · rw [if_neg (show h - 3 ≠ 0 by omega)] at p3
      refine ⟨t3, by rw [if_neg hc]; exact Steps.refl _, p3, ?_, RegsExcept.refl _ _, Frame.refl _ _⟩
      rw [r3.get (by simp), x14_2 h3, hb, if_neg hc]
  have r14 : RegsExcept s t4 ([.x28] ++ [.x14, .x28] ++ [] ++ [.x14]) := ((r1.trans r2).trans r3).trans r4
  have hb1 : 1 ≤ topZeroBits h := by rw [hb]; split_ifs <;> omega
  have hb8 : topZeroBits h ≤ 11 := by have := ktopZeroBits_le h; omega
  obtain ⟨t6, st6, p6, x16_6, r6, f6⟩ := ktC5_spec t4 p4 (topZeroBits h) h hb1 hb8 (by omega)
    x14_4 (by rw [r14.get (by simp)]; exact h13)
  obtain ⟨t7, st7, p7, x16_7, r7, f7⟩ : ∃ t7, Steps image t6 (if h = 11 then 2 else 0) (if h = 11 then 2 else 0) t7 ∧
      t7.pc = pcOf 744 ∧ t7.getReg .x16 = BitVec.ofNat 64 (maskN h) ∧ RegsExcept t6 t7 [.x16] ∧
      Frame t6 t7 (fun _ => False) := by
    by_cases hc : h = 11
    · rw [if_pos hc] at p6
      obtain ⟨u, su, pu, xu, ru, fu⟩ := ktC6_spec t6 p6
      exact ⟨u, by rw [if_pos hc]; exact su, pu, by rw [xu]; unfold maskN; rw [if_pos hc], ru, fu⟩
    · rw [if_neg hc] at p6
      refine ⟨t6, by rw [if_neg hc]; exact Steps.refl _, p6, ?_, RegsExcept.refl _ _, Frame.refl _ _⟩
      rw [x16_6]; unfold maskN; rw [if_neg hc]
  obtain ⟨t8, st8, p8, x17_8, r8, f8⟩ := ktC7_spec t7 p7 (topZeroBits h) hb8
    (by rw [r7.get (by simp), r6.get (by simp)]; exact x14_4)
  refine ⟨t8, Steps.of_eq (st1.trans (st2.trans (st3.trans (st4.trans (st6.trans (st7.trans st8))))))
    ?_ ?_, p8, by rw [r8.get (by simp)]; exact x16_7, by rw [x17_8]; rfl, ?_, ?_⟩
  · unfold setupK; split_ifs <;> omega
  · unfold setupK; split_ifs <;> omega
  · exact (((r14.trans r6).trans r7).trans r8).mono (by simp)
  · exact ((((((f1.trans f2).trans f3).trans f4).trans f6).trans f7).trans f8).mono
      (fun _ _ h => by simp_all)

theorem nonce_words (n : Nat) (hn : n < 2 ^ 64) : wordsOf (nonceBytes n) = [BitVec.ofNat 64 n, 0] := by
  unfold nonceBytes
  rw [wordsOf_bytesLE16]
  congr 1
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
    omega
  · congr 1
    apply BitVec.eq_of_toNat_eq
    have h0 : n % 2 ^ 64 % 2 ^ 128 / 2 ^ 64 = 0 := by omega
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, h0, Nat.zero_mod]
    rfl
theorem topNodeInput_length (heap n : Nat) (l r : Digest) : (topNodeInput heap n l r).length = 64 := by
  simp [topNodeInput, nonceBytes, bytesLE_length]
theorem wordsOf_topNodeInput (heap n : Nat) (h1 : 1 ≤ heap) (h2 : heap < 4096) (hn : n < 2 ^ 64) (l r : Digest) :
    wordsOf (topNodeInput heap n l r) =
      [l.extractLsb' 0 64, l.extractLsb' 64 64, BitVec.ofNat 64 heap, 0, BitVec.ofNat 64 n, 0,
        r.extractLsb' 0 64, r.extractLsb' 64 64] := by
  unfold topNodeInput
  rw [wordsOf_append _ _ (by simp [bytesLE_length, nonceBytes]), wordsOf_append _ _ (by simp [bytesLE_length]),
    wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_bytesLE16, wordsOf_bytesLE16, nonce_words n hn,
    wordsOf_bytesLE16, nodeTweak_3_top 0 heap h1 h2, T3.append64_low]
  have hhi : (0#64 ++ BitVec.ofNat 64 (nodeLo 0 0 + heap)).extractLsb' 64 64 = 0#64 :=
    BitVec.extractLsb'_append_eq_left
  rw [hhi]
  simp [nodeLo]
theorem topNodeInput_blocks (heap n : Nat) (l r : Digest) :
    (toQ (pad64 (topNodeInput heap n l r))).blocks = 1 := by
  rw [pad64_of_aligned _ (by rw [topNodeInput_length]),
    blocks_toQ ⟨by rw [topNodeInput_length]; omega, by rw [topNodeInput_length]⟩, topNodeInput_length]
/-- The 64-byte node block at `NODE` with pad `n` is the trial-`n` input. -/
theorem hashInput_topNode (t : MachineState) (heap n : Nat) (h1 : 1 ≤ heap) (h2 : heap < 4096) (hn : n < 2 ^ 64)
    (l r : Digest) (h10 : t.getReg .x10 = BitVec.ofNat 64 NODE) (h11 : t.getReg .x11 = BitVec.ofNat 64 64)
    (w0 : t.getMem (BitVec.ofNat 64 NODE) = l.extractLsb' 0 64)
    (w8 : t.getMem (BitVec.ofNat 64 (NODE + 8)) = l.extractLsb' 64 64)
    (w16 : t.getMem (BitVec.ofNat 64 (NODE + 16)) = BitVec.ofNat 64 heap)
    (w24 : t.getMem (BitVec.ofNat 64 (NODE + 24)) = 0)
    (w32 : t.getMem (BitVec.ofNat 64 (NODE + 32)) = BitVec.ofNat 64 n)
    (w40 : t.getMem (BitVec.ofNat 64 (NODE + 40)) = 0)
    (w48 : t.getMem (BitVec.ofNat 64 (NODE + 48)) = r.extractLsb' 0 64)
    (w56 : t.getMem (BitVec.ofNat 64 (NODE + 56)) = r.extractLsb' 64 64) :
    hashInput t = toQ (pad64 (topNodeInput heap n l r)) := by
  rw [pad64_of_aligned _ (by rw [topNodeInput_length])]
  refine hashInput_toQ t _ 0 NODE (topNodeInput_length _ _ _ _) h10 (by decide) (by decide) h11 (by decide) ?_
  rw [wordsOf_topNodeInput heap n h1 h2 hn, readWords_eight, w0, w8, w16, w24, w32, w40, w48, w56]
theorem out_after_hash (t : MachineState) (a : BitVec 256) (heap : Nat)
    (h12 : t.getReg .x12 = BitVec.ofNat 64 NOUT) :
    DigAt (writeHash t a) (NOUT + 16 - 16 * (heap % 2)) (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a) := by
  rw [T3.nodeHalfHigh_top]
  rcases Nat.mod_two_eq_zero_or_one heap with hp | hp
  · have hd : decide (heap % 2 = 0) = true := by simp [hp]
    rw [hd, T3.projHalf_true, hp, show NOUT + 16 - 16 * 0 = NOUT + 16 from rfl]
    exact DigAt.writeHash_hi t a NOUT h12 (by decide)
  · have hd : decide (heap % 2 = 0) = false := by simp [hp]
    rw [hd, T3.projHalf_false, hp, show NOUT + 16 - 16 * 1 = NOUT from rfl]
    exact DigAt.writeHash_lo t a NOUT h12 (by decide)

/-! ## The trial loop -/
/-- What follows the trial-`n` hash in `topNonceSearch` (fuel = trials left). -/
def trialTail (h heap : Nat) (l r : Digest) : Nat → Nat → Digest → T3.M (Nat × Digest)
  | 0, n, v => pure (n, v)
  | fuel + 1, n, v => if topZeroOk h v then pure (n, v) else topNonceSearch h heap l r fuel (n + 1)
theorem topNonceSearch_eq (h heap : Nat) (l r : Digest) (fuel n : Nat) :
    topNonceSearch h heap l r fuel n = topNodeHashN heap n l r >>= trialTail h heap l r fuel n := by
  cases fuel <;> rfl
theorem topNodeHashN_bind {β : Type} (heap n : Nat) (l r : Digest) (g : Digest → T3.M β) :
    topNodeHashN heap n l r >>= g =
      T3.publicHash (topNodeInput heap n l r) >>= fun a => g (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a) := by
  unfold topNodeHashN T3.projHash; rw [bind_assoc]; simp only [pure_bind]
theorem topNonceCap_le (h : Nat) (h1 : 1 ≤ h) (h11 : h ≤ 11) : 1 ≤ topNonceCap h ∧ topNonceCap h ≤ 104 * 2048 := by
  interval_cases h <;> decide

/-- The state right before the first node hash (263): arguments, node words and the store slot. -/
structure T2Facts (t2 : MachineState) (arena heap : Nat) (l r : Digest) : Prop where
  x2 : t2.getReg .x2 = BitVec.ofNat 64 arena
  x5 : t2.getReg .x5 = 0
  x12 : t2.getReg .x12 = BitVec.ofNat 64 NOUT
  x24 : t2.getReg .x24 = BitVec.ofNat 64 heap
  x29 : t2.getReg .x29 = BitVec.ofNat 64 (heap % 2 * 2 ^ 4)
  w0 : t2.getMem (BitVec.ofNat 64 NODE) = l.extractLsb' 0 64
  w8 : t2.getMem (BitVec.ofNat 64 (NODE + 8)) = l.extractLsb' 64 64
  w16 : t2.getMem (BitVec.ofNat 64 (NODE + 16)) = BitVec.ofNat 64 heap
  w24 : t2.getMem (BitVec.ofNat 64 (NODE + 24)) = 0
  w40 : t2.getMem (BitVec.ofNat 64 (NODE + 40)) = 0
  w48 : t2.getMem (BitVec.ofNat 64 (NODE + 48)) = r.extractLsb' 0 64
  w56 : t2.getMem (BitVec.ofNat 64 (NODE + 56)) = r.extractLsb' 64 64
  h1 : 1 ≤ heap
  h2 : heap < 4096
  ha8 : arena % 8 = 0
  hk : arena + 16 * heap + 16 ≤ 2 ^ 24
  hdis : NOUT + 32 ≤ arena + 16 * heap ∨ arena + 16 * heap + 16 ≤ NODE + 32

def trialRegs : List Reg := [.x10, .x11, .x14, .x16, .x17, .x28, .x30]
def TrialW (X : Nat) : Prop := X = NODE + 32 ∨ (NOUT ≤ X ∧ X < NOUT + 32)

/-- At 746 after the trial-`n` hash (answer `a`). -/
structure TrialSt (t2 : MachineState) (h heap n : Nat) (a : BitVec 256) (u : MachineState) : Prop where
  pc : u.pc = pcOf 746
  regs : RegsExcept t2 u trialRegs
  x16 : u.getReg .x16 = BitVec.ofNat 64 (maskN h)
  x17 : u.getReg .x17 = BitVec.ofNat 64 (topNonceCap h)
  pad : u.getMem (BitVec.ofNat 64 (NODE + 32)) = BitVec.ofNat 64 n
  frame : Frame t2 u TrialW
  out : DigAt u (NOUT + 16 - 16 * (heap % 2)) (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a)

def kokRegs : List Reg := [.x6, .x7, .x10, .x11, .x14, .x16, .x17, .x24, .x28, .x29, .x30]
def KokW (arena heap : Nat) (X : Nat) : Prop := TrialW X ∨ X = arena + 16 * heap ∨ X = arena + 16 * heap + 8

/-- After KOK and 272..273: back at 235 with the node stored and the pad cleared. -/
structure KokPost (t2 : MachineState) (arena heap : Nat) (v : Digest) (w : MachineState) : Prop where
  pc : w.pc = pcOf 235
  x24 : w.getReg .x24 = BitVec.ofNat 64 (heap + 1)
  pad : w.getMem (BitVec.ofNat 64 (NODE + 32)) = 0
  dig : DigAt w (arena + 16 * heap) v
  regs : RegsExcept t2 w kokRegs
  frame : Frame t2 w (KokW arena heap)

theorem kok_run {t2 u : MachineState} {arena heap : Nat} {l r : Digest} (F : T2Facts t2 arena heap l r)
    (hpc : u.pc = pcOf 760) {L : List Reg} (hL : ∀ x ∈ L, x ∈ trialRegs) (hr : RegsExcept t2 u L)
    (hf : Frame t2 u TrialW) {v : Digest} (hv : DigAt u (NOUT + 16 - 16 * (heap % 2)) v) :
    ∃ w, Steps image u 12 12 w ∧ KokPost t2 arena heap v w := by
  have g : ∀ x, x ∉ trialRegs → u.getReg x = t2.getReg x := fun x hx => hr.get (fun hm => hx (hL x hm))
  obtain ⟨u1, s1, p1, m32, ma, mb, r1, f1⟩ := ktOK_spec u hpc arena heap (heap % 2) (Nat.mod_lt _ (by decide))
    F.ha8 F.hk F.hdis (by rw [g _ (by simp [trialRegs])]; exact F.x2) (by rw [g _ (by simp [trialRegs])]; exact F.x24)
    (by rw [g _ (by simp [trialRegs])]; exact F.x29) (by rw [g _ (by simp [trialRegs])]; exact F.x12)
  obtain ⟨w, s2, p2, x24w, r2, f2⟩ := kt272_spec u1 p1 heap
    (by rw [r1.get (by simp), g _ (by simp [trialRegs])]; exact F.x24)
  have hk := F.hk
  refine ⟨w, s1.trans s2, ⟨p2, x24w, ?_, ?_, ?_, ?_⟩⟩
  · rw [f2.get (by decide) (fun h => h), m32]
  · exact ⟨by rw [f2.get (by omega) (fun h => h), ma, hv.1], by rw [f2.get (by omega) (fun h => h), mb, hv.2]⟩
  · refine ((hr.trans r1).trans r2).mono (fun x hx => ?_)
    simp only [List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · exact (by decide : ∀ y ∈ trialRegs, y ∈ kokRegs) x (hL x hx)
    · exact (by decide : ∀ y ∈ [Reg.x6, .x7, .x28, .x29], y ∈ kokRegs) x hx
    · exact (by decide : ∀ y ∈ [Reg.x24], y ∈ kokRegs) x hx
  · exact ((hf.trans f1).trans f2).mono (fun X _ h => by
      unfold KokW
      rcases h with (h | h | h | h) | h
      · exact Or.inl h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact h.elim)

section loop
variable (sk : BitVec 256) {t2 : MachineState} {arena heap : Nat} {l r : Digest} (F : T2Facts t2 arena heap l r)
  (h : Nat) (h1 : 1 ≤ h) (h11 : h ≤ 11)
include F h1 h11

theorem trial_check {n : Nat} {a : BitVec 256} {u : MachineState} (hu : TrialSt t2 h heap n a u) :
    ∃ u1, Steps image u 4 4 u1 ∧
      u1.pc = (if topZeroOk h (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a) = true then pcOf 760 else pcOf 750) ∧
      RegsExcept u u1 [.x30] ∧ Frame u u1 (fun _ => False) := by
  obtain ⟨u1, s1, p1, r1, f1⟩ := ktL0_spec u hu.pc (heap % 2) (Nat.mod_lt _ (by decide))
    (by rw [hu.regs.get (by simp [trialRegs]), F.x12]) (by rw [hu.regs.get (by simp [trialRegs]), F.x29])
  refine ⟨u1, s1, ?_, r1, f1⟩
  rw [p1, hu.x16, hu.out.2]
  by_cases hz : topZeroOk h (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a) = true
  · rw [if_pos ((zero_test _ h h1 h11).mpr hz), if_pos hz]
  · rw [if_neg (fun hc => hz ((zero_test _ h h1 h11).mp hc)), if_neg hz]

theorem trial_pad {n : Nat} {a : BitVec 256} {u u1 : MachineState} (hu : TrialSt t2 h heap n a u)
    (hn : n < topNonceCap h) (r1 : RegsExcept u u1 [.x30]) (f1 : Frame u u1 (fun _ => False))
    (p1 : u1.pc = pcOf 750) :
    ∃ u2, Steps image u1 4 4 u2 ∧ u2.pc = (if topNonceCap h ≤ n + 1 then pcOf 760 else pcOf 754) ∧
      u2.getReg .x28 = BitVec.ofNat 64 0x20000 ∧ u2.getReg .x30 = BitVec.ofNat 64 (n + 1) ∧
      RegsExcept u1 u2 [.x28, .x30] ∧ Frame u1 u2 (fun _ => False) := by
  have hc := topNonceCap_le h h1 h11
  exact ktL1_spec u1 p1 n (topNonceCap h) (by omega) (by omega)
    (by rw [f1.get (by decide) (fun h => h), hu.pad]) (by rw [r1.get (by simp), hu.x17])

theorem trial_loop : ∀ fuel n (a : BitVec 256) u, TrialSt t2 h heap n a u → n + fuel + 1 = topNonceCap h →
    TBSim image sk u (21 * fuel + 20)
      (trialTail h heap l r fuel n (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a))
      (fun res w => KokPost t2 arena heap res.2 w) := by
  have hcap := topNonceCap_le h h1 h11
  intro fuel
  induction fuel with
  | zero =>
    intro n a u hu hn
    obtain ⟨u1, s1, p1, r1, f1⟩ := trial_check F h h1 h11 hu
    by_cases hz : topZeroOk h (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a) = true
    · rw [if_pos hz] at p1
      obtain ⟨w, sw, hw⟩ := kok_run F p1 (L := trialRegs ++ [.x30]) (by simp [trialRegs]) (hu.regs.trans r1)
        ((hu.frame.trans f1).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim))
        (hu.out.frame f1 (by simp only [NOUT]; omega) (fun h => h) (fun h => h))
      exact (TBSim.pure_steps (sk := sk) (Q := fun res w => KokPost t2 arena heap res.2 w)
        (a := (n, T3.projHalf (T3.nodeHalfHigh 3 0 heap) a)) (s1.trans sw) hw).mono (by omega) (fun _ _ h => h)
    · rw [if_neg hz] at p1
      obtain ⟨u2, s2, p2, -, -, r2, f2⟩ := trial_pad F h h1 h11 hu (by omega) r1 f1 p1
      rw [if_pos (by omega)] at p2
      have f12 : Frame u u2 (fun _ => False) := (f1.trans f2).mono (fun X _ h => by simp_all)
      obtain ⟨w, sw, hw⟩ := kok_run F p2 (L := trialRegs ++ [.x30] ++ [.x28, .x30]) (by simp [trialRegs])
        ((hu.regs.trans r1).trans r2)
        ((hu.frame.trans f12).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim))
        (hu.out.frame f12 (by simp only [NOUT]; omega) (fun h => h) (fun h => h))
      exact (TBSim.pure_steps (sk := sk) (Q := fun res w => KokPost t2 arena heap res.2 w)
        (a := (n, T3.projHalf (T3.nodeHalfHigh 3 0 heap) a)) (s1.trans (s2.trans sw)) hw).mono (by omega)
        (fun _ _ h => h)
  | succ fuel ih =>
    intro n a u hu hn
    obtain ⟨u1, s1, p1, r1, f1⟩ := trial_check F h h1 h11 hu
    by_cases hz : topZeroOk h (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a) = true
    · rw [if_pos hz] at p1
      obtain ⟨w, sw, hw⟩ := kok_run F p1 (L := trialRegs ++ [.x30]) (by simp [trialRegs]) (hu.regs.trans r1)
        ((hu.frame.trans f1).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim))
        (hu.out.frame f1 (by simp only [NOUT]; omega) (fun h => h) (fun h => h))
      have e : trialTail h heap l r (fuel + 1) n (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a) =
          pure (n, T3.projHalf (T3.nodeHalfHigh 3 0 heap) a) := by simp only [trialTail, hz, if_true]
      rw [e]
      exact (TBSim.pure_steps (sk := sk) (Q := fun res w => KokPost t2 arena heap res.2 w)
        (a := (n, T3.projHalf (T3.nodeHalfHigh 3 0 heap) a)) (s1.trans sw) hw).mono (by omega) (fun _ _ h => h)
    · rw [if_neg hz] at p1
      obtain ⟨u2, s2, p2, x28_2, x30_2, r2, f2⟩ := trial_pad F h h1 h11 hu (by omega) r1 f1 p1
      rw [if_neg (by omega)] at p2
      obtain ⟨u3, s3, p3, m32_3, x10_3, x11_3, r3, f3⟩ := ktL2_spec u2 p2 x28_2
      have r03 : RegsExcept t2 u3 (trialRegs ++ [.x30] ++ [.x28, .x30] ++ [.x10, .x11]) :=
        ((hu.regs.trans r1).trans r2).trans r3
      have g3 : ∀ x, x ∉ trialRegs → u3.getReg x = t2.getReg x := fun x hx => r03.get (fun hm => hx
        ((by decide : ∀ y ∈ trialRegs ++ [Reg.x30] ++ [.x28, .x30] ++ [.x10, .x11], y ∈ trialRegs) x hm))
      have f03 : Frame t2 u3 TrialW := (((hu.frame.trans f1).trans f2).trans f3).mono (fun X _ h => by
        rcases h with ((h | h) | h) | h
        · exact h
        · exact h.elim
        · exact h.elim
        · exact Or.inl h)
      have fr : ∀ X, X < 2 ^ 64 → ¬ TrialW X → u3.getMem (BitVec.ofNat 64 X) = t2.getMem (BitVec.ofNat 64 X) :=
        fun X hX hn => f03.get hX hn
      have nW : ∀ X, X < NODE + 32 ∨ (NODE + 32 < X ∧ X < NOUT) → ¬ TrialW X := by
        intro X hX hw; unfold TrialW at hw; simp only [NODE, NOUT] at hX hw; omega
      have x12_3 : u3.getReg .x12 = BitVec.ofNat 64 NOUT := by rw [g3 _ (by simp [trialRegs]), F.x12]
      have hq : hashInput u3 = toQ (pad64 (topNodeInput heap (n + 1) l r)) :=
        hashInput_topNode u3 heap (n + 1) F.h1 F.h2 (by omega) l r x10_3 x11_3
          (by rw [fr _ (by decide) (nW _ (by simp only [NODE]; omega)), F.w0])
          (by rw [fr _ (by decide) (nW _ (by simp only [NODE]; omega)), F.w8])
          (by rw [fr _ (by decide) (nW _ (by simp only [NODE]; omega)), F.w16])
          (by rw [fr _ (by decide) (nW _ (by simp only [NODE]; omega)), F.w24])
          (by rw [m32_3, x30_2])
          (by rw [fr _ (by decide) (nW _ (by simp only [NODE, NOUT]; omega)), F.w40])
          (by rw [fr _ (by decide) (nW _ (by simp only [NODE, NOUT]; omega)), F.w48])
          (by rw [fr _ (by decide) (nW _ (by simp only [NODE, NOUT]; omega)), F.w56])
      have hv : hashArgumentsValid u3 = true :=
        hashArgs_const u3 NODE 64 NOUT x10_3 x11_3 x12_3 (by decide) (by decide) (by decide) (by decide) (by decide)
      have h5 : u3.getReg .x5 = 0 := by rw [g3 _ (by simp [trialRegs]), F.x5]
      have e : trialTail h heap l r (fuel + 1) n (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a) =
          T3.publicHash (topNodeInput heap (n + 1) l r) >>= fun a' =>
            trialTail h heap l r fuel (n + 1) (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a') := by
        rw [trialTail.eq_2, if_neg hz, topNonceSearch_eq, topNodeHashN_bind]
      rw [e]
      refine (TBSim.steps (s1.trans (s2.trans s3)) (TBSim.publicHash_bind (fetch_kt758 u3 p3) h5 hv hq
        (W := 1 + (21 * fuel + 20)) (fun a' => ?_))).mono (by rw [topNodeInput_blocks]; omega) (fun _ _ h => h)
      have hwf := Frame.writeHash u3 a' NOUT x12_3 (by decide)
      obtain ⟨w, s4, p4, r4, f4⟩ := ktL3_spec (writeHash u3 a') (by rw [pc_writeHash, p3, pcOf_add4])
      refine TBSim.steps s4 (ih (n + 1) a' w ⟨p4, ?_, ?_, ?_, ?_, ?_, ?_⟩ (by omega))
      · have hw0 : RegsExcept u3 (writeHash u3 a') [] := fun r _ => getReg_writeHash u3 a' r
        exact ((r03.trans hw0).trans r4).mono (by decide)
      · rw [r4.get (by simp), getReg_writeHash, r3.get (by simp), r2.get (by simp), r1.get (by simp), hu.x16]
      · rw [r4.get (by simp), getReg_writeHash, r3.get (by simp), r2.get (by simp), r1.get (by simp), hu.x17]
      · rw [f4.get (by decide) (fun h => h), hwf.get (by decide) (by simp only [NODE, NOUT]; omega), m32_3, x30_2]
      · exact ((f03.trans hwf).trans f4).mono (fun X _ h => by
          rcases h with (h | h) | h
          · exact h
          · exact Or.inr h
          · exact h.elim)
      · exact (out_after_hash u3 a' heap x12_3).frame f4 (by simp only [NOUT]; omega) (fun h => h) (fun h => h)
end loop

/-! ## Nodes -/
/-- Registers the top-tree routine may change (the lower-tree `levRegs` plus KCHK's `a3 a4 a6 a7`). -/
def topLevRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x13, .x14, .x16, .x17, .x20, .x24, .x28, .x29, .x30]

structure TNodeInv (s0 : MachineState) (B : LevArgs) (ℓ : Nat) (levels : List (List Digest))
    (pre : List Digest) (t : MachineState) : Prop where
  x13 : t.getReg .x13 = BitVec.ofNat 64 (ℓ + 1)
  x20 : t.getReg .x20 = BitVec.ofNat 64 (2 ^ (B.h - ℓ - 1))
  x24 : t.getReg .x24 = BitVec.ofNat 64 (2 ^ (B.h - ℓ - 1) + pre.length)
  regs : RegsExcept s0 t topLevRegs
  frame : Frame s0 t (LevW B)
  heap : HeapAt t B ℓ levels
  cur : DigsAt t (B.arena + 16 * 2 ^ (B.h - ℓ - 1)) pre

structure TLevInv (s0 : MachineState) (B : LevArgs) (ℓ : Nat) (levels : List (List Digest))
    (t : MachineState) : Prop where
  x13 : t.getReg .x13 = BitVec.ofNat 64 (ℓ + 1)
  x20 : t.getReg .x20 = BitVec.ofNat 64 (2 ^ B.h / 2 ^ (ℓ + 1))
  regs : RegsExcept s0 t topLevRegs
  frame : Frame s0 t (LevW B)
  heap : HeapAt t B ℓ levels

/-- The node computation of `buildTopLevel level` at index `i`. -/
def topNodeProg (level heap : Nat) (l r : Digest) : T3.M Digest :=
  if level = 12 then nodeHash 3 0 0 heap l r else Prod.snd <$> topNodeAt level heap l r

/-- Cycle bound of one node at height `h` (`h = 12`: the root, no nonce). -/
def nodeW (h : Nat) : Nat := if h = 12 then 51 else 75 + 21 * (topNonceCap h - 1)

theorem nonceBytes_zero : nonceBytes 0 = zero16 := by decide
theorem nodeHash_top (heap : Nat) (l r : Digest) :
    nodeHash 3 0 0 heap l r = T3.publicHash (topNodeInput heap 0 l r) >>= fun a =>
      pure (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a) := by
  unfold nodeHash T3.projHash topNodeInput
  rw [nonceBytes_zero]
/-- Campaign T51: a height with `b_h = 0` (heights 1, 2) keeps its first trial (nonce 0): the node is the plain node
hash. -/
theorem topNodeAt_b0 (h heap : Nat) (l r : Digest) (hb : topZeroBits h = 0) :
    Prod.snd <$> topNodeAt h heap l r = nodeHash 3 0 0 heap l r := by
  have h11 : h ≠ 11 := by intro e; subst e; simp [topZeroBits, T3.topZeroAlloc] at hb
  have hcap : topNonceCap h - 1 = 102 + 1 := by unfold topNonceCap; simp [hb]
  unfold topNodeAt
  rw [hcap, topNonceSearch_eq, topNodeHashN_bind, nodeHash_top, map_bind]
  congr 1; funext a
  have hz : topZeroOk h (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a) = true := by
    unfold topZeroOk
    rw [if_neg h11, hb, Nat.sub_zero, Nat.div_eq_of_lt (BitVec.isLt _)]
    rfl
  simp only [trialTail, hz, if_true, map_pure]

section node
variable {image' : Image} (sk : BitVec 256) {s0 : MachineState} {B : LevArgs} {leaves : List Digest}
  (hpre : LevPre s0 B leaves) (htop : B.lay = 0 ∧ B.tree = 0) (hh12 : B.h = 12)
include hpre htop hh12

/-- From 235 to the first node hash (263): the node block is in place with a zero pad. -/
theorem node_prefix {ℓ : Nat} (hl : ℓ < 12) {levels : List (List Digest)} {pre : List Digest}
    (hi : pre.length < 2 ^ (12 - ℓ - 1)) {t : MachineState} (ht : TNodeInv s0 B ℓ levels pre t)
    (hpc : t.pc = pcOf 235) :
    ∃ t2, Steps image t 28 28 t2 ∧ t2.pc = pcOf 263 ∧
      t2.getReg .x10 = BitVec.ofNat 64 NODE ∧ t2.getReg .x11 = BitVec.ofNat 64 64 ∧
      t2.getMem (BitVec.ofNat 64 (NODE + 32)) = 0 ∧
      T2Facts t2 B.arena (2 ^ (12 - ℓ - 1) + pre.length) ((levels.getD ℓ []).getD (2 * pre.length) 0)
        ((levels.getD ℓ []).getD (2 * pre.length + 1) 0) ∧
      RegsExcept t t2 [.x6, .x6, .x7, .x28, .x29, .x30, .x10, .x11, .x12, .x29] ∧
      Frame t t2 (fun X => X = NODE ∨ X = NODE + 8 ∨ X = NODE + 16 ∨ X = NODE + 24 ∨ X = NODE + 48 ∨
        X = NODE + 56) := by
  have ha := hpre.ha
  have has := hpre.has
  have ha8 := hpre.ha8
  rw [hh12] at ha has
  set lo := 2 ^ (12 - ℓ - 1) with hlo_def
  set i := pre.length with hi_def
  have hY : 2 ^ (12 - ℓ) = 2 * lo := two_pow_split hl
  have hYZ : 2 ^ (12 - ℓ) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hlo1 : 1 ≤ lo := Nat.one_le_two_pow
  have g : ∀ r, r ∉ topLevRegs → t.getReg r = s0.getReg r := fun r hr => ht.regs.get hr
  have r2 : t.getReg .x2 = BitVec.ofNat 64 B.arena := by rw [g _ (by simp [topLevRegs]), hpre.x2]
  have r9 : t.getReg .x9 = BitVec.ofNat 64 B.tree := by rw [g _ (by simp [topLevRegs]), hpre.x9]
  have r5 : t.getReg .x5 = 0 := by rw [g _ (by simp [topLevRegs]), hpre.x5]
  have r21 : t.getReg .x21 = BitVec.ofNat 64 (nodeLo B.lay B.tree) := by
    rw [g _ (by simp [topLevRegs]), hpre.x21]
  have x20 : t.getReg .x20 = BitVec.ofNat 64 lo := by rw [ht.x20, hh12]
  have x24 : t.getReg .x24 = BitVec.ofNat 64 (lo + i) := by rw [ht.x24, hh12]
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := sub118_spec subAt_keygen t hpc lo (lo + i) (by omega) (by omega) x20 x24
  rw [if_pos (by omega)] at t1pc
  obtain ⟨t2, st2, t2pc, t2x10, t2x11, t2x12, t2x29, t2n0, t2n8, t2n16, t2n24, t2n48, t2n56, t2r, t2f⟩ :=
    sub120_full subAt_keygen t1 t1pc B.arena (lo + i) B.tree (nodeLo B.lay B.tree) ha8 (by omega) hpre.htree
      (by simp only [NODE, NOUT] at has ⊢; omega) (by rw [t1r.get (by simp)]; exact r2)
      (by rw [t1r.get (by simp)]; exact x24) (by rw [t1r.get (by simp)]; exact r9)
      (by rw [t1r.get (by simp)]; exact r21)
  obtain ⟨hlen, hlev⟩ := ht.heap
  obtain ⟨hll, hlv⟩ := hlev ℓ le_rfl
  rw [hh12] at hll hlv
  have hL : DigAt t (B.arena + 32 * (lo + i)) ((levels.getD ℓ []).getD (2 * i) 0) := by
    have := hlv.get (i := 2 * i) (by rw [hll, hY]; omega)
    rwa [hY, show B.arena + 16 * (2 * lo) + 16 * (2 * i) = B.arena + 32 * (lo + i) by ring] at this
  have hR : DigAt t (B.arena + 32 * (lo + i) + 16) ((levels.getD ℓ []).getD (2 * i + 1) 0) := by
    have := hlv.get (i := 2 * i + 1) (by rw [hll, hY]; omega)
    rwa [hY, show B.arena + 16 * (2 * lo) + 16 * (2 * i + 1) = B.arena + 32 * (lo + i) + 16 by ring] at this
  have hL1 := hL.frame t1f (by omega) (by simp) (by simp)
  have hR1 := hR.frame t1f (by omega) (by simp) (by simp)
  have fr : ∀ X, (X = NODE + 32 ∨ X = NODE + 40) → t2.getMem (BitVec.ofNat 64 X) = s0.getMem (BitVec.ofNat 64 X) := by
    intro X hX
    have hX' : X < 2 ^ 64 := by rcases hX with h | h <;> (rw [h]; decide)
    rw [t2f.get hX' (by simp only [NODE] at hX ⊢; omega), t1f.get hX' (by simp),
      ht.frame.get hX' (by unfold LevW; rw [hh12]; simp only [NODE, NOUT] at hX has ⊢; omega)]
  have e16 : t2.getMem (BitVec.ofNat 64 (NODE + 16)) = BitVec.ofNat 64 (lo + i) := by
    rw [t2n16, t1r.get (by simp), r21, htop.1, htop.2]
    simp only [nodeLo, if_true, BitVec.ofNat_eq_ofNat, BitVec.zero_shiftLeft, BitVec.or_zero]
    rw [BitVec.zero_add]
  have hfr : ∀ r, r ∉ [Reg.x6] → r ∉ [Reg.x6, .x7, .x28, .x29, .x30, .x10, .x11, .x12, .x29] →
      t2.getReg r = t.getReg r := fun r h1 h2 => by rw [t2r.get h2, t1r.get h1]
  refine ⟨t2, (st1.trans st2).of_eq (by omega) (by omega), t2pc, t2x10, t2x11, by rw [fr _ (by simp), hpre.z32],
    ⟨by rw [hfr _ (by simp) (by simp)]; exact r2, by rw [hfr _ (by simp) (by simp)]; exact r5, t2x12,
      by rw [hfr _ (by simp) (by simp)]; exact x24, t2x29,
      by rw [t2n0, hL1.1], by rw [t2n8, hL1.2], e16, t2n24, by rw [fr _ (by simp), hpre.z40],
      by rw [t2n48, hR1.1], by rw [t2n56, hR1.2], by omega, by omega, ha8, by omega, by simp only [NODE, NOUT] at has ⊢; omega⟩,
    t1r.trans t2r, (t1f.trans t2f).mono (fun X _ hX => by rcases hX with hX | hX; exact hX.elim; exact hX)⟩
theorem node_post {ℓ : Nat} (hl : ℓ < 12) {levels : List (List Digest)} {pre : List Digest}
    (hi : pre.length < 2 ^ (12 - ℓ - 1)) {t t2 w : MachineState} (ht : TNodeInv s0 B ℓ levels pre t)
    (r02 : RegsExcept t t2 [.x6, .x6, .x7, .x28, .x29, .x30, .x10, .x11, .x12, .x29])
    (f02 : Frame t t2 (fun X => X = NODE ∨ X = NODE + 8 ∨ X = NODE + 16 ∨ X = NODE + 24 ∨ X = NODE + 48 ∨
        X = NODE + 56)) {v : Digest} (hw : KokPost t2 B.arena (2 ^ (12 - ℓ - 1) + pre.length) v w) :
    w.pc = pcOf 235 ∧ TNodeInv s0 B ℓ levels (pre ++ [v]) w := by
  have ha := hpre.ha
  have has := hpre.has
  rw [hh12] at ha has
  set lo := 2 ^ (12 - ℓ - 1) with hlo_def
  set i := pre.length with hi_def
  have hY : 2 ^ (12 - ℓ) = 2 * lo := two_pow_split hl
  have hYZ : 2 ^ (12 - ℓ) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hlo1 : 1 ≤ lo := Nat.one_le_two_pow
  have fall : Frame t w (fun X => (X = NODE ∨ X = NODE + 8 ∨ X = NODE + 16 ∨ X = NODE + 24 ∨ X = NODE + 48 ∨
      X = NODE + 56) ∨ KokW B.arena (lo + i) X) := f02.trans hw.frame
  have gk : ∀ x, x ∉ kokRegs → x ∉ [Reg.x6, .x6, .x7, .x28, .x29, .x30, .x10, .x11, .x12, .x29] →
      w.getReg x = t.getReg x := fun x h1 h2 => by rw [hw.regs.get h1, r02.get h2]
  refine ⟨hw.pc, ⟨?_, ?_, ?_, ?_, ?_, ⟨ht.heap.1, fun l hl' => ?_⟩, ?_⟩⟩
  · rw [gk _ (by decide) (by decide)]; exact ht.x13
  · rw [gk _ (by decide) (by decide)]; exact ht.x20
  · rw [hw.x24, List.length_append, List.length_singleton, hh12, Nat.add_assoc]
  · exact ((ht.regs.trans r02).trans hw.regs).mono (by decide)
  · intro X hX hn
    by_cases h32 : X = NODE + 32
    · subst h32; rw [hw.pad, hpre.z32]
    · rw [fall.get hX (fun h => by
        unfold LevW at hn; unfold KokW TrialW at h; rw [hh12] at hn
        simp only [NODE, NOUT] at hn h h32 has
        omega), ht.frame.get hX hn]
  · obtain ⟨hl1, hl2⟩ := ht.heap.2 l hl'
    rw [hh12] at hl1 hl2 ⊢
    have hYl : 2 * lo ≤ 2 ^ (12 - l) := by
      rw [← hY]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hYlZ : 2 ^ (12 - l) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) (by omega)
    refine ⟨hl1, hl2.frame fall (by rw [hl1]; omega) (fun X h1 h2 h => ?_)⟩
    rw [hl1] at h2
    unfold KokW TrialW at h
    simp only [NODE, NOUT] at h has
    omega
  · have hc := ht.cur
    rw [hh12] at hc ⊢
    refine (hc.frame fall (by omega) (fun X h1 h2 h => ?_)).snoc ?_
    · unfold KokW TrialW at h
      simp only [NODE, NOUT] at h has
      omega
    · rw [show B.arena + 16 * lo + 16 * i = B.arena + 16 * (lo + i) by ring]; exact hw.dig

theorem tnode {ℓ : Nat} (hl : ℓ < 12) {levels : List (List Digest)} {pre : List Digest}
    (hi : pre.length < 2 ^ (12 - ℓ - 1)) {t : MachineState} (ht : TNodeInv s0 B ℓ levels pre t)
    (hpc : t.pc = pcOf 235) :
    TBSim image sk t (nodeW (ℓ + 1))
      (topNodeProg (ℓ + 1) (2 ^ (12 - ℓ - 1) + pre.length) ((levels.getD ℓ []).getD (2 * pre.length) 0)
        ((levels.getD ℓ []).getD (2 * pre.length + 1) 0))
      (fun v u => u.pc = pcOf 235 ∧ TNodeInv s0 B ℓ levels (pre ++ [v]) u) := by
  obtain ⟨t2, st, p2, x10, x11, z32, F, r02, f02⟩ := node_prefix hpre htop hh12 hl hi ht hpc
  have hq := hashInput_topNode t2 _ 0 F.h1 F.h2 (by norm_num) _ _ x10 x11 F.w0 F.w8 F.w16 F.w24
    (by rw [z32]; rfl) F.w40 F.w48 F.w56
  have hv : hashArgumentsValid t2 = true :=
    hashArgs_const t2 NODE 64 NOUT x10 x11 F.x12 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hf : fetch image t2 = some (.base .ECALL) := fetch_sub146 subAt_keygen t2 p2
  have x13 : t2.getReg .x13 = BitVec.ofNat 64 (ℓ + 1) := by rw [r02.get (by decide)]; exact ht.x13
  have hwf : ∀ a, Frame t2 (writeHash t2 a) TrialW := fun a =>
    (Frame.writeHash t2 a NOUT F.x12 (by decide)).mono (fun X _ h => Or.inr h)
  have hw0 : ∀ a, RegsExcept t2 (writeHash t2 a) [] := fun a r _ => getReg_writeHash t2 a r
  unfold topNodeProg
  by_cases hroot : ℓ + 1 = 12
  · rw [if_pos hroot, nodeHash_top]
    refine (TBSim.steps st (TBSim.publicHash_bind hf F.x5 hv hq (W := 15) (fun a => ?_))).mono
      (by unfold nodeW; rw [if_pos hroot, topNodeInput_blocks]) (fun _ _ h => h)
    obtain ⟨u1, s1, p1, r1, f1⟩ := kt264_spec (writeHash t2 a) (by rw [pc_writeHash, p2, pcOf_add4])
    obtain ⟨u2, s2, p2', r2, f2⟩ := ktC0_spec u1 p1 (ℓ + 1) (by omega)
      (by rw [r1.get (by simp), getReg_writeHash]; exact x13)
    rw [if_pos hroot] at p2'
    obtain ⟨w, sw, hw⟩ := kok_run F p2' (L := [] ++ [] ++ [.x28]) (by decide) (((hw0 a).trans r1).trans r2)
      ((((hwf a).trans f1).trans f2).mono (fun X _ h => by
        rcases h with (h | h) | h; exact h; exact h.elim; exact h.elim))
      ((out_after_hash t2 a _ F.x12).frame (f1.trans f2) (by simp only [NOUT]; omega)
        (fun h => by rcases h with h | h <;> exact h) (fun h => by rcases h with h | h <;> exact h))
    exact TBSim.pure_steps (s1.trans (s2.trans sw)) (node_post hpre htop hh12 hl hi ht r02 f02 hw)
  by_cases hsmall : ℓ + 1 ≤ 2
  · -- campaign T51: heights 1, 2 (`b_h = 0`): 727..731 jump to KOK with the first trial
    have hb0 : topZeroBits (ℓ + 1) = 0 := by
      have : ℓ ≤ 1 := by omega
      interval_cases ℓ <;> rfl
    rw [if_neg hroot, topNodeAt_b0 _ _ _ _ hb0, nodeHash_top]
    refine (TBSim.steps st (TBSim.publicHash_bind hf F.x5 hv hq (W := 18) (fun a => ?_))).mono
      (by unfold nodeW; rw [if_neg hroot, topNodeInput_blocks]; have : 1 ≤ topNonceCap (ℓ + 1) := by
            unfold topNonceCap; exact Nat.mul_pos (by norm_num) (Nat.two_pow_pos _)
          omega) (fun _ _ h => h)
    obtain ⟨u1, s1, p1, r1, f1⟩ := kt264_spec (writeHash t2 a) (by rw [pc_writeHash, p2, pcOf_add4])
    obtain ⟨u2, s2, p2', r2, f2⟩ := ktC0_spec u1 p1 (ℓ + 1) (by omega)
      (by rw [r1.get (by simp), getReg_writeHash]; exact x13)
    rw [if_neg hroot] at p2'
    obtain ⟨u3, s3, p3, -, r3, f3⟩ := ktC1_spec u2 p2' (ℓ + 1) (by omega)
      (by rw [r2.get (by simp), r1.get (by simp), getReg_writeHash]; exact x13)
    rw [if_pos (by omega)] at p3
    obtain ⟨w, sw, hw⟩ := kok_run F p3 (L := [] ++ [] ++ [.x28] ++ [.x14, .x28]) (by decide)
      ((((hw0 a).trans r1).trans r2).trans r3)
      (((((hwf a).trans f1).trans f2).trans f3).mono (fun X _ h => by
        rcases h with ((h | h) | h) | h; exact h; exact h.elim; exact h.elim; exact h.elim))
      ((out_after_hash t2 a _ F.x12).frame ((f1.trans f2).trans f3) (by simp only [NOUT]; omega)
        (fun h => by rcases h with (h | h) | h <;> exact h) (fun h => by rcases h with (h | h) | h <;> exact h))
    exact TBSim.pure_steps (s1.trans (s2.trans (s3.trans sw))) (node_post hpre htop hh12 hl hi ht r02 f02 hw)
  · rw [if_neg hroot]
    have h1 : 3 ≤ ℓ + 1 := by omega
    have h1' : 1 ≤ ℓ + 1 := by omega
    have h11 : ℓ + 1 ≤ 11 := by omega
    have hcap := topNonceCap_le (ℓ + 1) h1' h11
    apply TBSim.map
    unfold topNodeAt
    rw [topNonceSearch_eq, topNodeHashN_bind]
    refine (TBSim.steps st (TBSim.publicHash_bind hf F.x5 hv hq
      (W := 1 + setupK (ℓ + 1) + (21 * (topNonceCap (ℓ + 1) - 1) + 20)) (fun a => ?_))).mono
      (by unfold nodeW; rw [if_neg hroot, topNodeInput_blocks]; have := setupK_le (ℓ + 1); omega)
      (fun _ _ h => h)
    obtain ⟨u1, s1, p1, r1, f1⟩ := kt264_spec (writeHash t2 a) (by rw [pc_writeHash, p2, pcOf_add4])
    obtain ⟨u2, s2, p2', x16, x17, r2, f2⟩ := ksetup_spec u1 p1 (ℓ + 1) h1 h11
      (by rw [r1.get (by simp), getReg_writeHash]; exact x13)
    have hts : TrialSt t2 (ℓ + 1) (2 ^ (12 - ℓ - 1) + pre.length) 0 a u2 :=
      ⟨p2', (((hw0 a).trans r1).trans r2).mono (by decide), x16, x17,
        by rw [f2.get (by decide) (fun h => h), f1.get (by decide) (fun h => h),
          (Frame.writeHash t2 a NOUT F.x12 (by decide)).get (by decide) (by simp only [NODE, NOUT]; omega), z32]; rfl,
        (((hwf a).trans f1).trans f2).mono (fun X _ h => by
          rcases h with (h | h) | h; exact h; exact h.elim; exact h.elim),
        (out_after_hash t2 a _ F.x12).frame (f1.trans f2) (by simp only [NOUT]; omega)
          (fun h => by rcases h with h | h <;> exact h) (fun h => by rcases h with h | h <;> exact h)⟩
    exact (TBSim.steps (s1.trans s2) (trial_loop sk F (ℓ + 1) h1' h11 _ 0 a u2 hts (by omega))).mono
      (by omega) (fun res w hw => node_post hpre htop hh12 hl hi ht r02 f02 hw)

/-- Cycle bound of tree level `ℓ` (nodes of height `ℓ + 1`). -/
def levelW (ℓ : Nat) : Nat := 8 + 2 ^ (11 - ℓ) * nodeW (ℓ + 1)
/-- Cycle bound of the top-tree routine (230 to the return). -/
def treeW : Nat := 6 + (sumTo levelW 12 + 2)

theorem tlev_level {ℓ : Nat} (hl : ℓ < 12) {levels : List (List Digest)} {t : MachineState}
    (ht : TLevInv s0 B ℓ levels t) (hpc : t.pc = pcOf 233) :
    TBSim image sk t (levelW ℓ)
      (do let nodes ← buildTopLevel (1 + ℓ) (levels.getD (1 + ℓ - 1) [])
          pure (levels ++ [nodes]))
      (fun levels' u => u.pc = pcOf 233 ∧ TLevInv s0 B (ℓ + 1) levels' u) := by
  have ha := hpre.ha
  rw [hh12] at ha
  set lo := 2 ^ (12 - ℓ - 1) with hlo_def
  have hY : 2 ^ (12 - ℓ) = 2 * lo := two_pow_split hl
  have hlo1 : 1 ≤ lo := Nat.one_le_two_pow
  have hloZ : lo ≤ 2048 := by
    calc lo ≤ 2 ^ 11 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2048 := by norm_num
  have hx20 : 2 ^ B.h / 2 ^ (ℓ + 1) = lo := by
    rw [hh12, hlo_def, show 12 = (ℓ + 1) + (12 - ℓ - 1) by omega, Nat.pow_add, Nat.mul_div_cancel_left _
      (by positivity)]
    congr 1; omega
  have hx20' : 2 ^ B.h / 2 ^ (ℓ + 1 + 1) = lo / 2 := by
    rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, hx20]
  have hl1 : 2 ^ (11 - ℓ) = lo := by rw [hlo_def]; congr 1; omega
  have r20 : t.getReg .x20 = BitVec.ofNat 64 lo := by rw [ht.x20, hx20]
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := sub116_spec subAt_keygen t hpc lo (by omega) r20
  rw [if_neg (by omega)] at t1pc
  obtain ⟨t2, st2, t2pc, t2x24, t2r, t2f⟩ := sub117_spec subAt_keygen t1 t1pc
  have f02 : Frame t t2 (fun _ => False) := (t1f.trans t2f).mono (fun X _ h => by simp_all)
  have h0 : TNodeInv s0 B ℓ levels [] t2 := by
    refine ⟨?_, ?_, ?_, ?_, (ht.frame.trans f02).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim),
      ⟨ht.heap.1, fun l hl' => ⟨(ht.heap.2 l hl').1, (ht.heap.2 l hl').2.frame f02 (by
        rw [(ht.heap.2 l hl').1, hh12]
        have : 2 ^ (12 - l) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega) (fun X _ _ h => h.elim)⟩⟩, DigsAt.nil _ _⟩
    · rw [t2r.get (by simp), t1r.get (by simp), ht.x13]
    · rw [t2r.get (by simp), t1r.get (by simp), r20, hh12]
    · rw [t2x24, t1r.get (by simp), r20, List.length_nil, Nat.add_zero, hh12]
    · exact (ht.regs.trans (t1r.trans t2r)).mono (by decide)
  have hnodes : (levels.getD (1 + ℓ - 1) []).length / 2 = lo := by
    have := (ht.heap.2 ℓ le_rfl).1
    rw [hh12] at this
    rw [show 1 + ℓ - 1 = ℓ by omega, this, hY]; omega
  unfold buildTopLevel
  rw [hnodes, show 1 + ℓ - 1 = ℓ by omega, show 1 + ℓ = ℓ + 1 by omega, show 12 - (ℓ + 1) = 12 - ℓ - 1 by omega]
  refine (TBSim.steps (st1.trans st2) (TBSim.bind (W₂ := 6)
    (TBSim.mapM_range lo _ (nodeW (ℓ + 1))
      (fun pre w => w.pc = pcOf 235 ∧ TNodeInv s0 B ℓ levels pre w)
      (fun pre w hpre' hw => tnode sk hpre htop hh12 hl hpre' hw.2 hw.1) ⟨t2pc, h0⟩) (fun nodes w hw => ?_))).mono
    (by unfold levelW; rw [hl1]; omega) (fun _ _ h => h)
  obtain ⟨hlen, wpc, hw⟩ := hw
  have w20 : w.getReg .x20 = BitVec.ofNat 64 lo := by rw [hw.x20, hh12]
  obtain ⟨w1, st3, w1pc, w1r, w1f⟩ := sub118_spec subAt_keygen w wpc lo (lo + nodes.length) (by omega) (by omega)
    w20 (by rw [hw.x24, hh12])
  rw [if_neg (by omega)] at w1pc
  obtain ⟨w2, st4, w2pc, w2r, w2f⟩ := kt274_spec w1 w1pc
  obtain ⟨w3, st5, w3pc, w3x20, w3x13, w3r, w3f⟩ := ktN_spec w2 w2pc lo (ℓ + 1) (by omega) (by omega)
    (by rw [w2r.get (by simp), w1r.get (by simp)]; exact w20)
    (by rw [w2r.get (by simp), w1r.get (by simp)]; exact hw.x13)
  have f13 : Frame w w3 (fun _ => False) := ((w1f.trans w2f).trans w3f).mono (fun X _ h => by simp_all)
  refine TBSim.pure_steps (st3.trans (st4.trans st5)) ⟨w3pc, w3x13, ?_, ?_, ?_, ?_⟩
  · rw [w3x20, hx20']
  · exact (hw.regs.trans ((w1r.trans w2r).trans w3r)).mono (by decide)
  · exact (hw.frame.trans f13).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim)
  · obtain ⟨hlen0, hlev⟩ := hw.heap
    refine ⟨by simp [hlen0], fun l hl' => ?_⟩
    rw [hh12]
    by_cases hle : l ≤ ℓ
    · have hg : (levels ++ [nodes]).getD l [] = levels.getD l [] := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show l < levels.length by omega)]
      rw [hg]
      obtain ⟨h1, h2⟩ := hlev l hle
      rw [hh12] at h1 h2
      have : 2 ^ (12 - l) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact ⟨h1, h2.frame f13 (by rw [h1]; omega) (fun X _ _ h => h.elim)⟩
    · have hl2 : l = ℓ + 1 := by omega
      subst hl2
      have hg : (levels ++ [nodes]).getD (ℓ + 1) [] = nodes := by
        simp [List.getD_eq_getElem?_getD, hlen0]
      rw [hg, show 12 - (ℓ + 1) = 12 - ℓ - 1 by omega]
      have hc := hw.cur
      rw [hh12] at hc
      exact ⟨hlen, hc.frame f13 (by rw [hlen]; omega) (fun X _ _ h => h.elim)⟩

/-- The keygen top-tree routine (entry 230 = `117 + 113`, return to `B.ret`) refines `buildTopLevels`. -/
theorem buildTopLevels_tbsim (hpc : s0.pc = pcOf 230) :
    TBSim image sk s0 treeW (buildTopLevels leaves)
      (fun levels t => t.pc = pcOf B.ret ∧ HeapAt t B B.h levels ∧ RegsExcept s0 t topLevRegs ∧
        Frame s0 t (LevW B)) := by
  have ha := hpre.ha
  rw [hh12] at ha
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := kt230_spec s0 hpc
  obtain ⟨t2, st2, t2pc, t2x20, t2x13, t2r, t2f⟩ := ktI_spec t1 t1pc
  obtain ⟨t3, st3, t3pc, t3x20, t3r, t3f⟩ := kt231_spec t2 t2pc 12 (by norm_num) (by norm_num)
    (by rw [t2r.get (by simp), t1r.get (by simp), hpre.x15, hh12]) t2x20
  have f03 : Frame s0 t3 (fun _ => False) := ((t1f.trans t2f).trans t3f).mono (fun X _ h => by simp_all)
  have h0 : TLevInv s0 B 0 [leaves] t3 := by
    refine ⟨by rw [t3r.get (by simp)]; exact t2x13, by rw [t3x20, hh12]; rfl,
      ((t1r.trans t2r).trans t3r).mono (by decide), f03.mono (fun X _ h => h.elim), ⟨rfl, fun l hl => ?_⟩⟩
    have hl0 : l = 0 := by omega
    subst hl0
    simp only [List.getD_cons_zero, Nat.sub_zero]
    have hlv := hpre.hleaves
    rw [hh12] at hlv ⊢
    exact ⟨by rw [hpre.hlen, hh12], hlv.frame f03 (by rw [hpre.hlen, hh12]; omega) (fun X _ _ h => h.elim)⟩
  unfold buildTopLevels
  refine (TBSim.steps (st1.trans (st2.trans st3)) (TBSim.bind (W₂ := 2) (f := Pure.pure)
    (TBSim.foldlM_range'_var 1 12 _ [leaves]
      (fun j levels t => t.pc = pcOf 233 ∧ TLevInv s0 B j levels t) levelW
      (fun j hj levels t ht => tlev_level sk hpre htop hh12 hj ht.2 ht.1) ⟨t3pc, h0⟩)
    (fun levels t ht => ?_))).of_eq (bind_pure _) |>.mono (by unfold treeW; omega) (fun _ _ h => h)
  obtain ⟨tpc, hinv⟩ := ht
  have hx : 2 ^ B.h / 2 ^ (12 + 1) = 0 := by rw [hh12]; norm_num
  obtain ⟨u1, st4, u1pc, u1r, u1f⟩ := sub116_spec subAt_keygen t tpc 0 (by omega) (by rw [hinv.x20, hx])
  rw [if_pos rfl] at u1pc
  obtain ⟨u2, st5, u2pc, u2r, u2f⟩ := sub159_spec subAt_keygen u1 u1pc B.ret
    (by rw [u1r.get (by simp), hinv.regs.get (by decide), hpre.x1])
  have f12 : Frame t u2 (fun _ => False) := (u1f.trans u2f).mono (fun X _ h => by simp_all)
  refine TBSim.pure_steps (st4.trans st5) ⟨u2pc, ⟨by rw [hh12]; exact hinv.heap.1, fun l hl => ?_⟩,
    (hinv.regs.trans (u1r.trans u2r)).mono (by decide),
    (hinv.frame.trans f12).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim)⟩
  obtain ⟨h1, h2⟩ := hinv.heap.2 l (by rw [hh12] at hl; exact hl)
  rw [hh12] at h1 h2 ⊢
  have : 2 ^ (12 - l) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact ⟨h1, h2.frame f12 (by rw [h1]; omega) (fun X _ _ h => h.elim)⟩

end node

end SigGolfCandidate.T3M.Keygen
end
-- ==== merged from T3M_Keygen_Mask ====
section

section
namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest buildLeafTopC topFamilyCoefs topTreeStep buildTopTree buildTopLevels buildLevels
  height chainCount width)
def kgLeaf (j : Nat) : LeafArgs := ⟨0, 0, j, [], false, ZDIG, DUMMY, TOP + 16 * (4096 + j), 34⟩
def kgLev : LevArgs := ⟨3, 0, 0, 12, TOP, 39⟩
theorem kgLeaf_n (j : Nat) : (kgLeaf j).n = 51 := rfl
theorem kgLev_costs : kgLev.levK = 159782 ∧ kgLev.levC = 188447 ∧ kgLev.levN = 4095 := by decide
def W1 (X : Nat) : Prop :=
  X = PRIV + 16 ∨ X = PRIV + 24 ∨ (SEEDS ≤ X ∧ X < SEEDS + 32) ∨ X = CHAIN + 16 ∨ X = CHAIN + 24 ∨
    (CHAIN + 32 ≤ X ∧ X < CHAIN + 112) ∨ (LEAFPK ≤ X ∧ X < LEAFPK + 896) ∨ (LOUT ≤ X ∧ X < LOUT + 32) ∨
    (DUMMY ≤ X ∧ X < DUMMY + 864) ∨ (TOP + 65536 ≤ X ∧ X < TOP + 131072) ∨ (KCOEF ≤ X ∧ X < KCOEF + 640)
def loopRegs : List Reg := tRegs ++ [.x18, .x25]
/-- img-v6: the keygen leaf loop before leaf `j`, state `st = (roots, coefficients, carry)` of `topTreeStep`. -/
structure LoopInv (s1 : MachineState) (j : Nat) (st : List Digest × List Digest × Digest) (t : MachineState) :
    Prop where
  pc : t.pc = pcOf 26
  x18 : t.getReg .x18 = BitVec.ofNat 64 j
  regs : RegsExcept s1 t loopRegs
  frame : Frame s1 t W1
  len : st.1.length = j
  roots : DigsAt t (TOP + 65536) st.1
  kc : KcPre t j st.2
theorem extractByte_zero (k : Nat) : extractByte (0 : Word) k = 0 := by
  simp [extractByte]
section loop
variable {sk : SecretKey} {s1 : MachineState} (hs : KStart sk s1)
include hs
theorem loopInv_zero : LoopInv s1 0 ([], [], 0) s1 :=
  ⟨hs.pc, hs.x18, RegsExcept.refl _ _, Frame.refl _ _, rfl, DigsAt.nil _ _,
    ⟨fun h => absurd rfl h, fun h => absurd h (by decide)⟩⟩
theorem kgLeaf_pre {j : Nat} (hj : j < 4096) {t : MachineState} (hr : RegsExcept s1 t loopRegs)
    (hf : Frame s1 t W1) (h18 : t.getReg .x18 = BitVec.ofNat 64 j) (h1 : t.getReg .x1 = pcOf 34)
    (h23 : t.getReg .x23 = BitVec.ofNat 64 DUMMY)
    (h25 : t.getReg .x25 = BitVec.ofNat 64 (TOP + 16 * (4096 + j))) :
    TopPre sk t (kgLeaf j) := by
  have g : ∀ r, r ∉ loopRegs → t.getReg r = s1.getReg r := fun r hr' => hr.get hr'
  have m : ∀ X, X < 2 ^ 64 → ¬ W1 X → t.getMem (BitVec.ofNat 64 X) = s1.getMem (BitVec.ofNat 64 X) :=
    fun X hX hn => hf.get hX hn
  have z : ∀ X, X < 2 ^ 64 → ¬ W1 X → (X < 0x80 ∨ 0xA0 ≤ X) → (X < PRIV ∨ PRIV + 64 ≤ X) →
      t.getMem (BitVec.ofNat 64 X) = 0 := fun X hX hn h1 h2 => (m X hX hn).trans (hs.zero X hX h1 h2)
  refine
    { x1 := h1
      x5 := by rw [g _ (by decide), hs.x5]
      x8 := by rw [g _ (by decide), hs.x8]; rfl
      x9 := by rw [g _ (by decide), hs.x9]; rfl
      x18 := h18
      x22 := by rw [g _ (by decide), hs.x22]; rfl
      x23 := h23
      x25 := h25
      x26 := by rw [g _ (by decide), hs.x26]; rfl
      x27 := by rw [g _ (by decide), hs.x27]; rfl
      x31 := by rw [g _ (by decide), hs.x31]; rfl
      htree := show 0 < 2 ^ 32 by norm_num
      hleaf := by show j < 2 ^ 32; omega
      hroute := by change 0 * 2 ^ 12 + j < 2 ^ 31; omega
      hleafHeight := hj
      hsteps := fun i _ => by
        change T3.maxDigit 0 i ≤ 8
        unfold T3.maxDigit
        split_ifs <;> omega
      p0 := by rw [m _ (by decide) (by unfold W1; decide), hs.p0]
      p8 := by rw [m _ (by decide) (by unfold W1; decide), hs.p8]
      p32 := by rw [m _ (by decide) (by unfold W1; decide), hs.p32]
      p40 := by rw [m _ (by decide) (by unfold W1; decide), hs.p40]
      p48 := by rw [m _ (by decide) (by unfold W1; decide), hs.p48]
      p56 := by rw [m _ (by decide) (by unfold W1; decide), hs.p56]
      z0 := z _ (by decide) (by unfold W1; decide) (by decide) (by decide)
      z8 := z _ (by decide) (by unfold W1; decide) (by decide) (by decide)
      top0 := ⟨rfl, rfl⟩
      hdig := fun i hi => by
        rw [kgLeaf_n] at hi
        have hw : ¬ W1 ((ZDIG + i) / 8 * 8) := by unfold W1; kg_omega
        show t.getByte (BitVec.ofNat 64 (ZDIG + i)) = BitVec.ofNat 8 0
        rw [hf.getByte (by kg_omega) hw, getByte_eq_word s1 _ (by kg_omega),
          hs.zero _ (by kg_omega) (by kg_omega) (by kg_omega), extractByte_zero]
        rfl
      hdigb := fun i _ => ⟨by show [].getD i 0 < 256; simp, fun _ => by show [].getD i 0 ≤ _; simp⟩
      hdigp := by show ZDIG + 51 ≤ 2 ^ 24; decide
      hdigW := fun i hi => by
        rw [kgLeaf_n] at hi
        unfold LeafW
        rw [kgLeaf_n, if_pos (show (kgLeaf j).lay = 0 from rfl)]
        dsimp only [kgLeaf]
        kg_omega
      hv8 := show DUMMY % 8 = 0 by decide
      hv := by show DUMMY + 16 * 51 ≤ 2 ^ 24; decide
      hvs := Or.inr (by show LEAFPK + 960 ≤ DUMMY; decide)
      hd8 := by show (TOP + 16 * (4096 + j)) % 8 = 0; kg_omega
      hd := by show TOP + 16 * (4096 + j) + 16 ≤ 2 ^ 24; kg_omega
      hds := Or.inr (Or.inl (by show LEAFPK + 960 ≤ TOP + 16 * (4096 + j); kg_omega))
      hdv := Or.inr (by show DUMMY + 16 * 51 ≤ TOP + 16 * (4096 + j); kg_omega) }
omit hs in
theorem kgLeaf_top (j : Nat) : TopArgs (kgLeaf j) :=
  ⟨rfl, rfl, Or.inl (by show DUMMY + 16 * 51 ≤ KCOEF; decide),
    Or.inr (by show KCOEF + 640 ≤ TOP + 16 * (4096 + j); kg_omega), Or.inl (by show ZDIG + 51 ≤ KCOEF; decide),
    Or.inl (by show ZDIG + 51 ≤ LEAFPK; decide)⟩
/-- Cycle bound of one keygen leaf-loop iteration (26..34 and the top leaf). -/
def leafLoopW : Nat := 10 + topLeafW
theorem leafLoop_body {j : Nat} (hj : j < 4096) (acc : List Digest × List Digest × Digest) (t : MachineState)
    (ht : LoopInv s1 j acc t) :
    TBSim image sk t leafLoopW (topTreeStep acc j) (LoopInv s1 (j + 1)) := by
  have g : ∀ r, r ∉ loopRegs → t.getReg r = s1.getReg r := fun r hr => ht.regs.get hr
  obtain ⟨t1, st1, t1pc, t1x6, t1r, t1f⟩ := blk26_spec t ht.pc j (by omega) ht.x18
  rw [if_pos hj] at t1pc
  obtain ⟨t2, st2, t2pc, t2x1, t2x23, t2x25, t2r, t2f⟩ := blk28_spec t1 t1pc j
    (by rw [t1r.get (by decide)]; exact ht.x18) t1x6
    (by rw [t1r.get (by decide), g _ (by decide), hs.x2])
  have r12 : RegsExcept t t2 [.x6, .x1, .x7, .x23, .x25] := t1r.trans t2r
  have f12 : Frame t t2 (fun _ => False) := (t1f.trans t2f).mono (fun X _ h => by simp at h)
  have hpre : TopPre sk t2 (kgLeaf j) :=
    kgLeaf_pre hs hj ((ht.regs.trans r12).mono (by simp [loopRegs, tRegs, leafRegs]))
      ((ht.frame.trans f12).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim))
      (by rw [r12.get (by decide)]; exact ht.x18) t2x1 t2x23 t2x25
  have hk2 : KcPre t2 j acc.2 := ht.kc.frame f12 (fun _ _ _ h => h)
  have hleaf := topLeaf_tsim sk hpre (kgLeaf_top j) t2pc (cc := acc.2) hk2
  have hb := topLeaf_bound ((kgLeaf j).leaf % 4) ((kgLeaf j).leaf / 4 % 2) (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num))
  have hprog : topTreeStep acc j = (topFamilyCoefs (kgLeaf j).leaf acc.2 >>= fun cc' =>
      buildLeafTopC (kgLeaf j).leaf cc'.1 [] >>= fun r => pure (r, cc')) >>= fun rc => pure (acc.1 ++ [rc.1.1], rc.2) := by
    simp only [topTreeStep, bind_assoc, pure_bind]; rfl
  rw [hprog]
  refine ((TSim.steps st1 (TSim.steps st2 (TSim.bind (k₂ := 2) (c₂ := 2) (n₂ := 0) (b₂ := 0) hleaf
    (fun r u hu => ?_)))).toTBSim (by have := hb.1; omega)).mono (by unfold leafLoopW; have := hb.2; omega)
    (fun _ _ h => h)
  obtain ⟨upc, uroot, -, ukc, ur, uf⟩ := hu
  obtain ⟨⟨root, values⟩, cc'⟩ := r
  obtain ⟨t3, st3, t3pc, t3x18, t3r, t3f⟩ := blk34_spec u upc j
    (by rw [ur.get (by simp [tRegs, leafRegs]), r12.get (by decide)]; exact ht.x18)
  refine TSim.pure_steps st3 ⟨t3pc, t3x18, ?_, ?_, by simp [ht.len], ?_, ?_⟩
  · exact (((ht.regs.trans r12).trans ur).trans t3r).mono (by simp [loopRegs, tRegs, leafRegs])
  · refine (((ht.frame.trans f12).trans uf).trans t3f).mono (fun X _ h => ?_)
    rcases h with ((h | h) | h | h | h) | h
    · exact h
    · exact h.elim
    · unfold LeafW at h
      simp only [kgLeaf_n] at h
      unfold W1
      change X = PRIV + 16 ∨ X = PRIV + 24 ∨ (SEEDS ≤ X ∧ X < SEEDS + 32) ∨ X = CHAIN + 16 ∨
        X = CHAIN + 24 ∨ (CHAIN + 32 ≤ X ∧ X < CHAIN + 112) ∨ (LEAFPK + 16 ≤ X ∧ X < LEAFPK + 16 * (51 + 2)) ∨
        (LOUT ≤ X ∧ X < LOUT + 32) ∨ (DUMMY ≤ X ∧ X < DUMMY + 16 * 51) ∨
        (TOP + 16 * (4096 + j) ≤ X ∧ X < TOP + 16 * (4096 + j) + 16) at h
      kg_omega
    · unfold W1; kg_omega
    · unfold W1; kg_omega
    · exact h.elim
  · have hd : DigAt u (TOP + 65536 + 16 * acc.1.length) root := by
      rw [ht.len, show TOP + 65536 + 16 * j = TOP + 16 * (4096 + j) by kg_omega]
      exact uroot
    have hold : DigsAt u (TOP + 65536) acc.1 := by
      refine ht.roots.frame ((f12.trans uf).mono (fun X _ h => h)) (by rw [ht.len]; kg_omega) ?_
      intro B h1 h2 h
      rw [ht.len] at h2
      rcases h with h | h | h | h
      · exact h
      · unfold LeafW at h
        simp only [kgLeaf_n] at h
        change B = PRIV + 16 ∨ B = PRIV + 24 ∨ (SEEDS ≤ B ∧ B < SEEDS + 32) ∨ B = CHAIN + 16 ∨
          B = CHAIN + 24 ∨ (CHAIN + 32 ≤ B ∧ B < CHAIN + 112) ∨ (LEAFPK + 16 ≤ B ∧ B < LEAFPK + 16 * (51 + 2)) ∨
          (LOUT ≤ B ∧ B < LOUT + 32) ∨ (DUMMY ≤ B ∧ B < DUMMY + 16 * 51) ∨
          (TOP + 16 * (4096 + j) ≤ B ∧ B < TOP + 16 * (4096 + j) + 16) at h
        kg_omega
      · kg_omega
      · kg_omega
    exact (hold.snoc hd).frame t3f (by simp only [List.length_append, List.length_singleton, ht.len]; kg_omega)
      (fun _ _ _ h => h)
  · have hp := ukc.frame t3f (fun _ _ _ h => h)
    change KcPost t3 j cc' at hp
    exact ⟨fun _ => ⟨hp.1, hp.2.1⟩, fun h => hp.2.2 (by omega)⟩
def treeRegs : List Reg := loopRegs ++ [.x6] ++ [.x1, .x15, .x21] ++ topLevRegs
/-- Cycle bound of the keygen top tree: 4096 leaf-loop iterations (`leafLoopW`), the loop exit (5) and the node
levels (`treeW`, top-bytes nonces). -/
def topTreeW : Nat := 4096 * leafLoopW + (5 + treeW)
/-- The keygen top tree (campaign T8D: family-seeded top leaves; top-bytes layer: node nonces, bounded cycles). -/
theorem buildTopTree_tbsim :
    TBSim image sk s1 topTreeW buildTopTree
      (fun levels t => t.pc = pcOf 39 ∧ HeapAt t kgLev 12 levels ∧ RegsExcept s1 t treeRegs ∧
        Frame s1 t (fun X => W1 X ∨ LevW kgLev X)) := by
  unfold buildTopTree
  have hleaves := TBSim.foldlM_range'_var (image := image) (sk := sk) 0 4096 topTreeStep ([], [], 0) (LoopInv s1)
    (fun _ => leafLoopW) (fun j hj acc t ht => by simpa using leafLoop_body hs hj acc t ht) (loopInv_zero hs)
  rw [sumTo_const, ← List.range_eq_range'] at hleaves
  refine TBSim.bind (W₁ := 4096 * leafLoopW) hleaves (fun st t ht => ?_)
  obtain ⟨t1, st1, t1pc, -, t1r, t1f⟩ := blk26_spec t ht.pc 4096 (by norm_num) ht.x18
  rw [if_neg (by norm_num)] at t1pc
  obtain ⟨t2, st2, t2pc, t2x1, t2x15, t2x21, t2r, t2f⟩ := blk36_spec t1 t1pc
  have r02 : RegsExcept s1 t2 (loopRegs ++ [.x6] ++ [.x1, .x15, .x21]) := (ht.regs.trans t1r).trans t2r
  have f12 : Frame t t2 (fun _ => False) := (t1f.trans t2f).mono (fun X _ h => by simp at h)
  have f02 : Frame s1 t2 W1 := (ht.frame.trans f12).mono
    (fun X _ h => by rcases h with h | h; exact h; exact h.elim)
  have hpre : LevPre t2 kgLev st.1 :=
    { x1 := t2x1
      x2 := by rw [r02.get (by decide), hs.x2]; rfl
      x5 := by rw [r02.get (by decide), hs.x5]
      x9 := by rw [r02.get (by decide), hs.x9]; rfl
      x15 := t2x15
      x21 := by rw [t2x21]; decide
      tag3 := rfl
      hlay := show 0 < 4 by norm_num
      htree := show 0 < 2 ^ 32 by norm_num
      hh1 := show 1 ≤ 12 by norm_num
      hh := show 12 ≤ 12 by norm_num
      ha8 := show TOP % 8 = 0 by decide
      ha := show TOP + 16 * 2 ^ (12 + 1) ≤ 2 ^ 24 by decide
      has := Or.inl (show NOUT + 32 ≤ TOP by decide)
      z32 := by
        rw [f02.get (by decide) (by unfold W1; decide)]
        exact hs.zero _ (by decide) (by decide) (by decide)
      z40 := by
        rw [f02.get (by decide) (by unfold W1; decide)]
        exact hs.zero _ (by decide) (by decide) (by decide)
      hlen := ht.len
      hleaves := ht.roots.frame f12 (by rw [ht.len]; decide) (fun _ _ _ h => h) }
  have hlev := buildTopLevels_tbsim sk hpre ⟨rfl, rfl⟩ rfl t2pc
  exact (TBSim.steps st1 (TBSim.steps st2 (hlev.mono le_rfl
    (fun levels u hu => ⟨hu.1, hu.2.1, r02.trans hu.2.2.1, f02.trans hu.2.2.2⟩)))).mono (by omega)
    (fun _ _ h => h)
end loop
end SigGolfCandidate.T3M.Keygen
end
section
namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
theorem blk277_spec (s : MachineState) (hpc : s.pc = pcOf 277) :
    ∃ t, Steps image s 12 12 t ∧ t.pc = pcOf 289 ∧
      t.getReg .x2 = BitVec.ofNat 64 TOP ∧
      t.getReg .x20 = BitVec.ofNat 64 4096 ∧ t.getReg .x22 = 0 ∧
      t.getReg .x24 = BitVec.ofNat 64 REGION ∧
      t.getMem (BitVec.ofNat 64 0xA0) = s.getMem (BitVec.ofNat 64 (TOP+16)) ∧
      t.getMem (BitVec.ofNat 64 0xA8) = s.getMem (BitVec.ofNat 64 (TOP+24)) ∧
      RegsExcept s t [.x2,.x6,.x7,.x20,.x22,.x24,.x30] ∧
      Frame s t (fun A => A=0xA0 ∨ A=0xA8) := by
  refine ⟨_,symRun_sound blk_277 codeAt_277 s hpc (by simp [blk_277.res,rv_simp]),
    ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [blk_277.res,E.eval]
  · simp [blk_277.res,rv_simp,TOP]
  · simp [blk_277.res,rv_simp]
  · simp [blk_277.res,rv_simp]
  · simp [blk_277.res,rv_simp,REGION]
  · simp [blk_277.res,rv_simp,TOP]
  · simp [blk_277.res,rv_simp,TOP]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_277.res,rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,blk_277.res]
    t3n []
    rw [if_neg (by omega),if_neg (by omega)]
theorem blk289_spec (s : MachineState) (hpc : s.pc = pcOf 289) (lo : Nat)
    (hlo : lo ≤ 4096) (h20 : s.getReg .x20 = BitVec.ofNat 64 lo) :
    ∃ t, Steps image s 6 6 t ∧ t.pc = pcOf 295 ∧ t.getReg .x23 = 0 ∧
      t.getReg .x26 = BitVec.ofNat 64 (lo/2) ∧
      t.getReg .x21 = BitVec.ofNat 64 (TOP+16*lo) ∧
      t.getReg .x2 = BitVec.ofNat 64 TOP ∧
      RegsExcept s t [.x2,.x21,.x23,.x26] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound blk_289 codeAt_289 s hpc (by simp [blk_289.res,rv_simp]),
    ?_,?_,?_,?_,?_,?_,?_⟩
  · simp [blk_289.res,E.eval]
  · simp [blk_289.res,rv_simp]
  · simp only [Result.toState_getReg,blk_289.res]; t3n [h20]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  · simp only [Result.toState_getReg,blk_289.res]; t3n [h20]
    congr 1; unfold TOP; omega
  · simp [blk_289.res,rv_simp,TOP]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_289.res,rv_simp] <;> rfl
  · intro A _ _; simp [blk_289.res,rv_simp]
theorem blk295_spec (s : MachineState) (hpc : s.pc = pcOf 295) (level i : Nat)
    (hlev : level < 2^32) (hi : i < 2^32)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 level)
    (h23 : s.getReg .x23 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s 14 14 t ∧ t.pc = pcOf 309 ∧
      t.getReg .x10 = BitVec.ofNat 64 PRIV ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 MOUT ∧
      t.getMem (BitVec.ofNat 64 (PRIV+16)) = BitVec.ofNat 64 (hdr0 13 0 0 level) ∧
      t.getMem (BitVec.ofNat 64 (PRIV+24)) = BitVec.ofNat 64 (hdr1 0 i) ∧
      RegsExcept s t [.x6,.x7,.x10,.x11,.x12,.x28] ∧
      Frame s t (fun A => A=PRIV+16 ∨ A=PRIV+24) := by
  refine ⟨_,symRun_sound blk_295 codeAt_295 s hpc (by simp [blk_295.res,rv_simp]),
    ?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [blk_295.res,E.eval]
  · simp [blk_295.res,rv_simp]
  · simp [blk_295.res,rv_simp]
  · simp [blk_295.res,rv_simp,MOUT]
  · simp only [Result.toState_getMem,blk_295.res,PRIV]
    t3n [h22]
    rw [ofNat_or_disjoint' 3329 (level*4294967296) 32 (by norm_num) (by omega),
      hdr0_eq 13 0 0 level (by norm_num) (by norm_num) (by norm_num) hlev]
    congr 1; ring
  · simp only [Result.toState_getMem,blk_295.res,PRIV]
    t3n [h23]
    rw [hdr1_eq 0 i (by norm_num) hi]
    congr 1; ring
  · intro r hr; simp at hr; cases r <;> simp_all [blk_295.res,rv_simp] <;> rfl
  · intro A hA hn
    simp only [PRIV] at hn
    simp only [Result.toState_getMem,blk_295.res]
    t3n []
    rw [if_neg (by omega),if_neg (by omega)]
theorem fetch_309 (s : MachineState) (hpc : s.pc = pcOf 309) :
    fetch image s = some (.base .ECALL) := (codeAt_309.fetch s hpc).trans rfl
theorem blk330_spec (s : MachineState) (hpc : s.pc = pcOf 330) (lo level : Nat)
    (hlo : lo ≤ 4096) (hl : level < 12)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 lo)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 level) :
    ∃ t, Steps image s 4 4 t ∧ t.pc = (if level+1<12 then pcOf 289 else pcOf 334) ∧
      t.getReg .x20 = BitVec.ofNat 64 (lo/2) ∧ t.getReg .x22 = BitVec.ofNat 64 (level+1) ∧
      RegsExcept s t [.x6,.x20,.x22] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound blk_330 codeAt_330 s hpc (by simp [blk_330.res,rv_simp]),?_,?_,?_,?_,?_⟩
  · simp only [Result.toState_pc,blk_330.res,E.eval,CmpOp.eval,h22]
    have hx : (BitVec.ofNat 64 level+1#64).toNat=level+1 := by
      simp only [BitVec.toNat_add,BitVec.toNat_ofNat]; omega
    simp only [BitVec.ult,decide_eq_true_eq,BinOp.eval,hx]
    rfl
  · simp only [Result.toState_getReg,blk_330.res]; t3n [h20]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  · simp only [Result.toState_getReg,blk_330.res]; t3n [h22]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_330.res,rv_simp] <;> rfl
  · intro A _ _; simp [blk_330.res,rv_simp]
theorem blk310_spec (s : MachineState) (hpc : s.pc = pcOf 310)
    (nodep endp i cap : Nat)
    (hn0 : TOP ≤ nodep) (hn : nodep+32 ≤ 0x70000) (hn8 : nodep%8=0)
    (he0 : REGION ≤ endp) (he : endp+32 ≤ 0xA0000) (he8 : endp%8=0)
    (hi : i < 4096) (hc : cap ≤ 4096)
    (h21 : s.getReg .x21 = BitVec.ofNat 64 nodep)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 endp)
    (h23 : s.getReg .x23 = BitVec.ofNat 64 i)
    (h26 : s.getReg .x26 = BitVec.ofNat 64 cap)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 MOUT) :
    ∃ t, Steps image s 20 20 t ∧ t.pc = (if i+1<cap then pcOf 295 else pcOf 330) ∧
      (∀ j : Fin 4, t.getMem (BitVec.ofNat 64 (endp+8*j.val)) =
        s.getMem (BitVec.ofNat 64 (nodep+8*j.val)) ^^^
          s.getMem (BitVec.ofNat 64 (MOUT+8*j.val))) ∧
      t.getReg .x21 = BitVec.ofNat 64 (nodep+32) ∧
      t.getReg .x24 = BitVec.ofNat 64 (endp+32) ∧
      t.getReg .x23 = BitVec.ofNat 64 (i+1) ∧
      RegsExcept s t [.x6,.x7,.x21,.x23,.x24] ∧
      Frame s t (fun A => A=endp ∨ A=endp+8 ∨ A=endp+16 ∨ A=endp+24) := by
  have hobl : Oblig.all s blk_310.res.st.obl := by
    simp only [blk_310.res]
    t3n [h21,h24,h12]
    simp only [TOP,REGION,MOUT] at *
    simp (disch := omega) only [Nat.mod_eq_of_lt]
    norm_num [Nat.add_mod,hn8,he8] <;> omega
  refine ⟨_,symRun_sound blk_310 codeAt_310 s hpc hobl,?_,?_,?_,?_,?_,?_,?_⟩
  · simp only [Result.toState_pc,blk_310.res,E.eval,CmpOp.eval,BinOp.eval,h23,h26]
    have hx : (BitVec.ofNat 64 i+1#64).toNat=i+1 := by
      simp only [BitVec.toNat_add,BitVec.toNat_ofNat]; omega
    simp only [BitVec.ult,decide_eq_true_eq,hx,BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show cap<2^64 by omega)]
  · intro j
    fin_cases j <;> simp only [Fin.val_mk,Nat.reduceMul,Nat.add_zero,
      Result.toState_getMem,blk_310.res,MOUT] <;>
      t3n [h21,h24,h12] <;>
      (simp only [TOP,REGION,MOUT] at *; split_ifs <;> first | rfl | omega)
  · simp only [Result.toState_getReg,blk_310.res]; t3n [h21]
  · simp only [Result.toState_getReg,blk_310.res]; t3n [h24]
  · simp only [Result.toState_getReg,blk_310.res]; t3n [h23]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_310.res,rv_simp] <;> rfl
  · intro A hA hnot
    simp only [Result.toState_getMem,blk_310.res]
    t3n [h24]
    rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
end SigGolfCandidate.T3M.Keygen
end
section
namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Digest pairedMask maskedLevel header privateInput)
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
theorem TSim.post_steps {α : Type} {image : Image} {sk : BitVec 256} {s : MachineState} {k c n b k' c' : Nat}
    {p : T3.M α} {Q Q' : α → MachineState → Prop} (h : TSim image sk s k c n b p Q)
    (hs : ∀ a t, Q a t → ∃ u, Steps image t k' c' u ∧ Q' a u) :
    TSim image sk s (k + k') (c + c') n b p Q' :=
  (TSim.bind (k₂ := k') (c₂ := c') (n₂ := 0) (b₂ := 0) (f := fun a => (Pure.pure a : T3.M α)) h
    (fun a t ht => by obtain ⟨u, hu, hq⟩ := hs a t ht; exact TSim.pure_steps hu hq)).of_eq (bind_pure p)
    rfl rfl (Nat.add_zero n) (Nat.add_zero b)
def MW (X : Nat) : Prop :=
  X = PRIV + 16 ∨ X = PRIV + 24 ∨ (MOUT ≤ X ∧ X < MOUT + 32) ∨ (REGION ≤ X ∧ X < REGION + 131040)
def maskRegs : List Reg := [.x2, .x6, .x7, .x10, .x11, .x12, .x20, .x21, .x22, .x23, .x24, .x26, .x28]
structure MaskPre (sk : SecretKey) (s : MachineState) (levels : List (List Digest)) : Prop where
  pc : s.pc = pcOf 289
  x2 : s.getReg .x2 = BitVec.ofNat 64 TOP
  x5 : s.getReg .x5 = 0
  x22 : s.getReg .x22 = 0
  x20 : s.getReg .x20 = BitVec.ofNat 64 4096
  x24 : s.getReg .x24 = BitVec.ofNat 64 REGION
  p0 : s.getMem (BitVec.ofNat 64 PRIV) = sk.extractLsb' 0 64
  p8 : s.getMem (BitVec.ofNat 64 (PRIV + 8)) = sk.extractLsb' 64 64
  p32 : s.getMem (BitVec.ofNat 64 (PRIV + 32)) = sk.extractLsb' 128 64
  p40 : s.getMem (BitVec.ofNat 64 (PRIV + 40)) = sk.extractLsb' 192 64
  p48 : s.getMem (BitVec.ofNat 64 (PRIV + 48)) = 0
  p56 : s.getMem (BitVec.ofNat 64 (PRIV + 56)) = 0
  nodes : ∀ l, l ≤ 11 → (levels.getD l []).length = 2 ^ (12 - l) ∧
    DigsAt s (TOP + 16 * 2 ^ (12 - l)) (levels.getD l [])
structure LevelInv (s4 : MachineState) (pre : List (List Digest)) (t : MachineState) : Prop where
  pc : t.pc = if pre.length < 12 then pcOf 289 else pcOf 334
  x20 : t.getReg .x20 = BitVec.ofNat 64 (2 ^ (12 - pre.length))
  x22 : t.getReg .x22 = BitVec.ofNat 64 pre.length
  x24 : t.getReg .x24 = BitVec.ofNat 64 (REGION + 16 * pre.flatten.length)
  flen : pre.flatten.length + 2 ^ (13 - pre.length) = 8192
  regs : RegsExcept s4 t maskRegs
  frame : Frame s4 t MW
  out : DigsAt t REGION pre.flatten
structure MaskInv (s4 : MachineState) (pre cur : List (List Digest)) (t : MachineState) : Prop where
  pc : t.pc = if cur.length < 2 ^ (11 - pre.length) then pcOf 295 else pcOf 330
  x23 : t.getReg .x23 = BitVec.ofNat 64 cur.length
  x26 : t.getReg .x26 = BitVec.ofNat 64 (2 ^ (11 - pre.length))
  x20 : t.getReg .x20 = BitVec.ofNat 64 (2 ^ (12 - pre.length))
  x22 : t.getReg .x22 = BitVec.ofNat 64 pre.length
  x21 : t.getReg .x21 = BitVec.ofNat 64 (TOP + 16 * (2 ^ (12 - pre.length) + 2 * cur.length))
  x24 : t.getReg .x24 = BitVec.ofNat 64 (REGION + 16 * (pre.flatten.length + cur.flatten.length))
  flen : cur.flatten.length = 2 * cur.length
  regs : RegsExcept s4 t maskRegs
  frame : Frame s4 t MW
  out : DigsAt t REGION (pre.flatten ++ cur.flatten)
theorem two_pow_twelve_sub {j : Nat} (hj : j < 12) :
    2 ≤ 2 ^ (12-j) ∧ 2 ^ (12-j) ≤ 4096 ∧ 1 ≤ 2 ^ (11-j) ∧
    2 ^ (12-j) = 2 * 2 ^ (11-j) ∧
    2 ^ (13-j) = 2 * 2 ^ (12-j) ∧
    2 ^ (12-(j+1)) = 2 ^ (12-j) / 2 ∧
    2 ^ (13-(j+1)) = 2 ^ (12-j) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (12-j) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · calc 2 ^ (12-j) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 4096 := by norm_num
  · exact Nat.one_le_pow _ _ (by decide)
  · rw [show 12-j=(11-j)+1 by omega, pow_succ]; ring
  · rw [show 13-j=(12-j)+1 by omega, pow_succ]; ring
  · rw [show 12-j=(12-(j+1))+1 by omega, pow_succ]; omega
  · congr 1; omega
section masks
variable {sk : SecretKey} {s4 : MachineState} {levels : List (List Digest)} (hm : MaskPre sk s4 levels)
include hm
theorem mask_one {pre : List (List Digest)} (hpl : pre.length < 12) {cur : List (List Digest)}
    (hcl : cur.length < 2 ^ (11 - pre.length))
    (hfl : pre.flatten.length + 2 ^ (13 - pre.length) = 8192) {t : MachineState}
    (ht : MaskInv s4 pre cur t) :
    TSim image sk t 35 42 1 1
      (do
        let values ← pairedMask pre.length cur.length
        pure [(levels.getD pre.length []).getD (2*cur.length) 0 ^^^ values.1,
          (levels.getD pre.length []).getD (2*cur.length+1) 0 ^^^ values.2])
      (fun ds u => MaskInv s4 pre (cur ++ [ds]) u) := by
  obtain ⟨hl2, hl4096, hp1, hpair, h13, -, -⟩ := two_pow_twelve_sub hpl
  have g : ∀ r, r ∉ maskRegs → t.getReg r = s4.getReg r := fun r hr => ht.regs.get hr
  obtain ⟨t2, st2, t2pc, t2x10, t2x11, t2x12, t2a, t2b, t2r, t2f⟩ :=
    blk295_spec t (by simpa only [if_pos hcl] using ht.pc) pre.length cur.length
      (by omega) (by omega) ht.x22 ht.x23
  have fr : ∀ X, (X = PRIV ∨ X = PRIV+8 ∨ X = PRIV+32 ∨ X = PRIV+40 ∨ X = PRIV+48 ∨ X = PRIV+56) →
      t2.getMem (BitVec.ofNat 64 X) = s4.getMem (BitVec.ofNat 64 X) := fun X hX =>
    (t2f.get (by rcases hX with h | h | h | h | h | h <;> (rw [h]; decide)) (by kg_omega)).trans
      (ht.frame.get (by rcases hX with h | h | h | h | h | h <;> (rw [h]; decide))
        (by unfold MW; kg_omega))
  have hq : hashInput t2 = toQ (privateInput sk (.inl (header 13 0 0 pre.length cur.length))) := by
    refine hashInput_toQ t2 _ 0 PRIV (privateInput_tweak_length _ _) t2x10 (by decide) (by decide)
      t2x11 (by decide) ?_
    rw [wordsOf_privateInput_tweak, header_lo, header_hi, readWords_eight, fr PRIV (by simp),
      fr (PRIV+8) (by simp), t2a, t2b, fr (PRIV+32) (by simp), fr (PRIV+40) (by simp),
      fr (PRIV+48) (by simp), fr (PRIV+56) (by simp), hm.p0, hm.p8, hm.p32, hm.p40, hm.p48, hm.p56]
    rfl
  have hv : hashArgumentsValid t2 = true :=
    hashArgs_const t2 PRIV 64 MOUT t2x10 t2x11 t2x12 (by decide) (by decide) (by decide) (by decide)
      (by decide)
  have h5 : t2.getReg .x5 = 0 := by rw [t2r.get (by decide), g _ (by decide), hm.x5]
  unfold pairedMask
  refine (TSim.steps st2 (TSim.privatePair_bind (k := 20) (c := 20) (n := 0) (b := 0)
    (fetch_309 t2 t2pc) h5 hv hq (fun a => ?_))).of_eq rfl rfl rfl rfl rfl
  have hwf := Frame.writeHash t2 a MOUT t2x12 (by decide)
  have upc : (writeHash t2 a).pc = pcOf 310 := by rw [pc_writeHash, t2pc, pcOf_add4]
  have hmo0 := DigAt.writeHash_lo t2 a MOUT t2x12 (by decide)
  have hmo1 := DigAt.writeHash_hi t2 a MOUT t2x12 (by decide)
  have fsu := ht.frame.trans (t2f.trans hwf)
  obtain ⟨hlen, hds⟩ := hm.nodes pre.length (by omega)
  have hnode (i : Nat) (hi : i < 2 ^ (12-pre.length)) :
      DigAt (writeHash t2 a) (TOP + 16 * (2 ^ (12-pre.length)+i)) ((levels.getD pre.length []).getD i 0) := by
    have hn := hds.get (show i < _ by rw [hlen]; exact hi)
    rw [show TOP+16*2^(12-pre.length)+16*i=TOP+16*(2^(12-pre.length)+i) by ring] at hn
    exact hn.frame fsu (by kg_omega) (by unfold MW; kg_omega) (by unfold MW; kg_omega)
  have hn0 := hnode (2*cur.length) (by omega)
  have hn1 := hnode (2*cur.length+1) (by omega)
  have rw2 : RegsExcept t (writeHash t2 a) [.x6, .x7, .x10, .x11, .x12, .x28] := fun r hr => by
    rw [getReg_writeHash]; exact t2r.get hr
  have hcf := ht.flen
  obtain ⟨t3, st3, t3pc, t3mem, t3x21, t3x24, t3x23, t3r, t3f⟩ :=
    blk310_spec (writeHash t2 a) upc
      (TOP+16*(2^(12-pre.length)+2*cur.length))
      (REGION+16*(pre.flatten.length+cur.flatten.length)) cur.length (2^(11-pre.length))
      (by kg_omega) (by kg_omega) (by kg_omega)
      (by kg_omega) (by kg_omega) (by kg_omega) (by omega) (by omega)
      (by rw [rw2.get (by decide)]; exact ht.x21)
      (by rw [rw2.get (by decide)]; exact ht.x24)
      (by rw [rw2.get (by decide)]; exact ht.x23)
      (by rw [rw2.get (by decide)]; exact ht.x26) (by rw [getReg_writeHash]; exact t2x12)
  have t3a := t3mem ⟨0,by decide⟩
  have t3b := t3mem ⟨1,by decide⟩
  have t3c := t3mem ⟨2,by decide⟩
  have t3d := t3mem ⟨3,by decide⟩
  simp only [Fin.val_mk, Nat.reduceMul, Nat.add_zero] at t3a t3b t3c t3d
  have r23 := rw2.trans t3r
  refine TSim.pure_steps st3 ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [List.length_append, List.length_singleton] using t3pc
  · rw [t3x23, List.length_append, List.length_singleton]
  · rw [r23.get (by decide)]; exact ht.x26
  · rw [r23.get (by decide)]; exact ht.x20
  · rw [r23.get (by decide)]; exact ht.x22
  · rw [t3x21, List.length_append, List.length_singleton]
    congr 1
  · rw [t3x24, List.flatten_concat, List.length_append]
    simp only [List.length_cons, List.length_nil]
    congr 1
  · rw [List.flatten_concat, List.length_append, ht.flen, List.length_append, List.length_singleton]
    simp only [List.length_cons, List.length_nil]; omega
  · exact (ht.regs.trans r23).mono (by decide)
  · refine (fsu.trans t3f).mono (fun X _ h => ?_)
    unfold MW at h ⊢
    have hc := ht.flen
    kg_omega
  · rw [List.flatten_concat, ← List.append_assoc]
    have hout := ht.out.frame ((t2f.trans hwf).trans t3f)
      (by rw [List.length_append]; have hc := ht.flen; kg_omega)
      (fun B h1 h2 h => by rw [List.length_append] at h2; kg_omega)
    have hd0 : DigAt t3 (REGION+16*(pre.flatten.length+cur.flatten.length))
        ((levels.getD pre.length []).getD (2*cur.length) 0 ^^^ a.extractLsb' 0 128) := by
      constructor
      · rw [t3a, hn0.1, hmo0.1, ← BitVec.extractLsb'_xor]
      · rw [t3b, hn0.2, hmo0.2, ← BitVec.extractLsb'_xor]
    have hd1 : DigAt t3 (REGION+16*(pre.flatten.length+cur.flatten.length)+16)
        ((levels.getD pre.length []).getD (2*cur.length+1) 0 ^^^ a.extractLsb' 128 128) := by
      constructor
      · rw [t3c, show TOP+16*(2^(12-pre.length)+2*cur.length)+16=
          TOP+16*(2^(12-pre.length)+(2*cur.length+1)) by ring, hn1.1, hmo1.1, ← BitVec.extractLsb'_xor]
      · rw [t3d, show TOP+16*(2^(12-pre.length)+2*cur.length)+24=
          TOP+16*(2^(12-pre.length)+(2*cur.length+1))+8 by ring, hn1.2, hmo1.2, ← BitVec.extractLsb'_xor]
    have hs0 := DigsAt.snoc hout (by simpa only [List.length_append] using hd0)
    have hs1 := DigsAt.snoc hs0 (by
      simpa only [List.length_append, List.length_singleton, Nat.mul_add, Nat.mul_one, Nat.add_assoc] using hd1)
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using hs1
theorem levelInv_zero : LevelInv s4 [] s4 :=
  ⟨hm.pc, hm.x20, hm.x22, hm.x24, rfl, RegsExcept.refl _ _, Frame.refl _ _, DigsAt.nil _ _⟩
theorem mask_level {pre : List (List Digest)} (hpl : pre.length < 12) {t : MachineState}
    (ht : LevelInv s4 pre t) :
    TSim image sk t (10+35*2^(11-pre.length)) (10+42*2^(11-pre.length))
      (2^(11-pre.length)) (2^(11-pre.length))
      (maskedLevel (levels.getD pre.length []) pre.length)
      (fun ds u => LevelInv s4 (pre ++ [ds]) u) := by
  obtain ⟨hl2, hl4096, hp1, hpair, h13, h12', h13'⟩ := two_pow_twelve_sub hpl
  have hfl := ht.flen
  obtain ⟨t2, st2, t2pc, t2x23, t2x26, t2x21, t2x2, t2r, t2f⟩ :=
    blk289_spec t (by simpa only [if_pos hpl] using ht.pc) (2^(12-pre.length)) (by omega) ht.x20
  have h0 : MaskInv s4 pre [] t2 := by
    refine ⟨?_, t2x23, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
    · simpa only [List.length_nil, if_pos (by omega : 0<2^(11-pre.length))] using t2pc
    · rw [t2x26, hpair, Nat.mul_div_cancel_left _ (by decide)]
    · rw [t2r.get (by decide)]; exact ht.x20
    · rw [t2r.get (by decide)]; exact ht.x22
    · simpa only [List.length_nil, Nat.mul_zero, Nat.add_zero] using t2x21
    · rw [t2r.get (by decide), ht.x24]; rfl
    · exact (ht.regs.trans t2r).mono (by decide)
    · exact (ht.frame.trans t2f).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim)
    · simpa only [List.flatten_nil, List.append_nil] using ht.out.frame t2f (by kg_omega) (fun _ _ _ h => h)
  have hin := TSim.mapM_range (image := image) (sk := sk) (2^(11-pre.length))
    (fun i => do
      let values ← pairedMask pre.length i
      pure [(levels.getD pre.length []).getD (2*i) 0 ^^^ values.1,
        (levels.getD pre.length []).getD (2*i+1) 0 ^^^ values.2])
    (fun _ => 35) (fun _ => 42) (fun _ => 1) (fun _ => 1) (MaskInv s4 pre)
    (fun cur u hc hu => mask_one hm hpl hc ht.flen hu) h0
  simp only [sumTo_const] at hin
  refine (TSim.steps st2 (TSim.map List.flatten
    (TSim.post_steps (k' := 4) (c' := 4) hin (fun ds u hu => ?_)))).of_eq ?_
      (by ring) (by ring) (by simp) (by simp)
  · obtain ⟨hdl, hu⟩ := hu
    obtain ⟨u2, su2, u2pc, u2x20, u2x22, u2r, u2f⟩ :=
      blk330_spec u (by simpa only [hdl, if_neg (Nat.lt_irrefl _)] using hu.pc)
        (2^(12-pre.length)) pre.length (by omega) (by omega) hu.x20 hu.x22
    refine ⟨u2, su2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [List.length_append, List.length_singleton] using u2pc
    · rw [u2x20, List.length_append, List.length_singleton, h12']
    · rw [u2x22, List.length_append, List.length_singleton]
    · rw [u2r.get (by decide), hu.x24, List.flatten_concat, List.length_append]
    · rw [List.flatten_concat, List.length_append, hu.flen, hdl,
        List.length_append, List.length_singleton, h13', ← hpair]
      omega
    · exact (hu.regs.trans u2r).mono (by decide)
    · exact (hu.frame.trans u2f).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim)
    · rw [List.flatten_concat]
      exact hu.out.frame u2f (by rw [List.length_append, hu.flen, hdl]; kg_omega) (fun _ _ _ h => h)
  · simp only [maskedLevel, map_eq_bind_pure_comp]
    rfl
theorem masks_tsim :
    TSim image sk s4 143445 172110 4095 4095
      ((List.range' 0 12).mapM fun level => maskedLevel (levels.getD level []) level)
      (fun masked u => masked.length = 12 ∧ LevelInv s4 masked u) := by
  rw [List.range'_eq_map_range, List.mapM_map]
  simp only [Nat.zero_add]
  exact (TSim.mapM_range 12 _ (fun j => 10+35*2^(11-j)) (fun j => 10+42*2^(11-j))
    (fun j => 2^(11-j)) (fun j => 2^(11-j)) (LevelInv s4)
    (fun pre t hl ht => mask_level hm hl ht) (levelInv_zero hm)).of_eq rfl
      (by decide) (by decide) (by decide) (by decide)
end masks
end SigGolfCandidate.T3M.Keygen
end
end
-- ==== merged from T3M_Keygen_Payload ====
section

namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Digest Cache Region keygen keygenPayload buildTopTree mask privateMac privateInput
  header zero16 cacheBytes readLE)
open SphincsSecurity (bytesLE bytesLE_length)
theorem ofFn_getD_toArray (n : Nat) (l : List UInt8) (h : l.length = n) :
    List.ofFn (fun i : Fin n => l.toArray.getD i.val 0) = l := by
  subst h
  apply List.ext_getElem List.length_ofFn
  intro i h1 h2
  rw [List.getElem_ofFn]
  simp only [Array.getD, List.size_toArray, h2, dite_true]
  rfl
theorem length_flatMap16 (ds : List Digest) : (ds.flatMap (bytesLE 16)).length = 16 * ds.length := by
  induction ds with
  | nil => rfl
  | cons d ds ih => rw [List.flatMap_cons, List.length_append, bytesLE_length, ih, List.length_cons]; ring
theorem Frame.readWords {s t : MachineState} {W : Nat → Prop} (h : Frame s t W) (A : Nat) :
    ∀ m, A + 8 * m ≤ 2 ^ 64 → (∀ i < m, ¬ W (A + 8 * i)) →
      t.readWords (BitVec.ofNat 64 A) m = s.readWords (BitVec.ofNat 64 A) m
  | 0, _, _ => rfl
  | m + 1, hA, hW => by
    rw [readWords_add, readWords_add, Frame.readWords h A m (by omega) (fun i hi => hW i (by omega)),
      readWords_one, readWords_one, h.get (by omega) (hW m (by omega))]
structure PayloadPost (sk : SecretKey) (r : Digest × Region) (t : MachineState) : Prop where
  pc : t.pc = pcOf 334
  x20 : t.getReg .x20 = BitVec.ofNat 64 1
  x5 : t.getReg .x5 = 0
  pk : DigAt t 0xA0 r.1
  region : t.readWords (BitVec.ofNat 64 REGION) 16380 = wordsOf (List.ofFn r.2)
  k0 : t.getMem (BitVec.ofNat 64 0x80) = sk.extractLsb' 0 64
  k8 : t.getMem (BitVec.ofNat 64 0x88) = sk.extractLsb' 64 64
  k16 : t.getMem (BitVec.ofNat 64 0x90) = sk.extractLsb' 128 64
  k24 : t.getMem (BitVec.ofNat 64 0x98) = sk.extractLsb' 192 64
section main
variable {sk : SecretKey} {s1 : MachineState} (hs : KStart sk s1)
include hs
/-- Top-bytes layer: the payload has a cycle bound (the top-tree node nonces are data dependent). -/
theorem payload_tbsim :
    TBSim image sk s1 (topTreeW + 172123) keygenPayload (PayloadPost sk) := by
  unfold keygenPayload
  refine TBSim.bind (buildTopTree_tbsim hs) (fun levels t ht => ?_)
  refine TSim.toTBSim (k := 143458) (n := 4095) (b := 4095) ?_ (by norm_num)
  obtain ⟨tpc, theap, tregs, tframe⟩ := ht
  obtain ⟨t3, st3, t3pc, t3r, t3f⟩ := blk39_spec t tpc
  obtain ⟨t4, st4', t4pc, t4x2, t4x20, t4x22, t4x24, t4a', t4b', t4r', t4f'⟩ :=
    blk277_spec t3 t3pc
  have t4a : t4.getMem (BitVec.ofNat 64 0xA0)=t.getMem (BitVec.ofNat 64 (TOP+16)) :=
    t4a'.trans (t3f.get (by decide) (fun h => h))
  have t4b : t4.getMem (BitVec.ofNat 64 0xA8)=t.getMem (BitVec.ofNat 64 (TOP+24)) :=
    t4b'.trans (t3f.get (by decide) (fun h => h))
  have st4 := st3.trans st4'
  have t4r := t3r.trans t4r'
  have t4f : Frame t t4 (fun X => X=0xA0 ∨ X=0xA8) :=
    (t3f.trans t4f').mono (fun X _ h => by rcases h with h | h; exact h.elim; exact h)
  have fr : ∀ X, X < 2 ^ 64 → ¬ (W1 X ∨ LevW kgLev X) → X ≠ 0xA0 → X ≠ 0xA8 →
      t4.getMem (BitVec.ofNat 64 X) = s1.getMem (BitVec.ofNat 64 X) := fun X hX h1 h2 h3 =>
    (t4f.get hX (by rintro (h | h) <;> contradiction)).trans (tframe.get hX h1)
  have nW : ∀ X, (X < PRIV + 16 ∨ (PRIV + 32 ≤ X ∧ X < SEEDS) ∨ X = 0x11000 ∨ X = 0x11008 ∨ X = 0x11010 ∨
      X = 0x11018 ∨ X = NODE + 32 ∨ X = NODE + 40) → ¬ (W1 X ∨ LevW kgLev X) := by
    intro X hX h
    unfold W1 LevW kgLev at h
    kg_omega
  obtain ⟨hlev, hnodes⟩ := theap
  have hm : MaskPre sk t4 levels :=
    { pc := t4pc
      x2 := t4x2
      x5 := by rw [t4r.get (by decide), tregs.get (by decide), hs.x5]
      x22 := t4x22
      x20 := t4x20
      x24 := t4x24
      p0 := by rw [fr _ (by decide) (nW _ (by kg_omega)) (by decide) (by decide), hs.p0]
      p8 := by rw [fr _ (by decide) (nW _ (by kg_omega)) (by decide) (by decide), hs.p8]
      p32 := by rw [fr _ (by decide) (nW _ (by kg_omega)) (by decide) (by decide), hs.p32]
      p40 := by rw [fr _ (by decide) (nW _ (by kg_omega)) (by decide) (by decide), hs.p40]
      p48 := by rw [fr _ (by decide) (nW _ (by kg_omega)) (by decide) (by decide), hs.p48]
      p56 := by rw [fr _ (by decide) (nW _ (by kg_omega)) (by decide) (by decide), hs.p56]
      nodes := fun l h2 => by
        obtain ⟨hl, hd⟩ := hnodes l (by omega)
        have hp : 2 ^ (12 - l) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) (by omega)
        refine ⟨hl, hd.frame t4f ?_ ?_⟩
        · change TOP + 16 * 2 ^ (12 - l) + 16 * (levels.getD l []).length < 2 ^ 64
          rw [show (levels.getD l []).length = 2 ^ (12 - l) from hl]; kg_omega
        · intro B hB _ h; change TOP + 16 * 2 ^ (12 - l) ≤ B at hB; kg_omega }
  refine TSim.steps st4 (TSim.bind (k₂ := 0) (c₂ := 0) (n₂ := 0) (b₂ := 0) (masks_tsim hm)
    (fun masked u hu => TSim.pure ?_))
  obtain ⟨hml, hu⟩ := hu
  have hfl := hu.flen
  rw [hml] at hfl
  have hfl' : masked.flatten.length = 8190 := by rw [show 2 ^ (13 - 12) = 2 from rfl] at hfl; omega
  have g : ∀ r, r ∉ maskRegs → u.getReg r = t4.getReg r := fun r hr => hu.regs.get hr
  have fu : ∀ X, X < 2 ^ 64 → ¬ (W1 X ∨ LevW kgLev X) → X ≠ 0xA0 → X ≠ 0xA8 → ¬ MW X →
      u.getMem (BitVec.ofNat 64 X) = s1.getMem (BitVec.ofNat 64 X) := fun X hX h1 h2 h3 h4 =>
    (hu.frame.get hX h4).trans (fr X hX h1 h2 h3)
  have nM : ∀ X, X < 0xA0 → ¬ MW X := by
    intro X hX h; unfold MW at h; kg_omega
  refine ⟨by simpa only [hml, Nat.lt_irrefl, ite_false] using hu.pc, by rw [hu.x20, hml]; rfl, by rw [g _ (by decide), t4r.get (by decide), tregs.get (by decide),
    hs.x5], ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    obtain ⟨hl12, hd12⟩ := hnodes 12 le_rfl
    have h0 := hd12.get (i := 0) (by rw [hl12]; decide)
    have hpk : DigAt t4 0xA0 ((levels.getD 12 []).getD 0 0) := ⟨by rw [t4a]; exact h0.1, by rw [t4b]; exact h0.2⟩
    exact hpk.frame hu.frame (by decide) (by unfold MW; kg_omega) (by unfold MW; kg_omega)
  ·
    show u.readWords (BitVec.ofNat 64 REGION) 16380 =
      wordsOf (List.ofFn fun i : Fin 131040 => (masked.flatten.flatMap (bytesLE 16)).toArray.getD i.val 0)
    rw [ofFn_getD_toArray 131040 _ (by rw [length_flatMap16, hfl']), ← hu.out.words, hfl']
  · rw [fu 0x80 (by decide) (nW 0x80 (by kg_omega)) (by decide) (by decide) (nM 0x80 (by kg_omega)), hs.k0]
  · rw [fu 0x88 (by decide) (nW 0x88 (by kg_omega)) (by decide) (by decide) (nM 0x88 (by kg_omega)), hs.k8]
  · rw [fu 0x90 (by decide) (nW 0x90 (by kg_omega)) (by decide) (by decide) (nM 0x90 (by kg_omega)), hs.k16]
  · rw [fu 0x98 (by decide) (nW 0x98 (by kg_omega)) (by decide) (by decide) (nM 0x98 (by kg_omega)), hs.k24]
end main
end SigGolfCandidate.T3M.Keygen
end
-- ==== merged from T3M_Keygen_Halt ====
section

namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
def haltSetup : List (BitVec 32) := [1049235,1299]
theorem haltSetup_at : CodeAt image (pcOf 539) haltSetup :=
  CodeAt.of_append (pre := Images.keygenCode.take 539)
    (post := Images.keygenCode.drop 541) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
sym_block haltSetup_blk := symRun {noAlias := true} haltSetup (pcOf 539) 100
theorem haltSetup_spec (s : MachineState) (hpc : s.pc = pcOf 539) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf 541 ∧ t.getReg .x5 = 1 ∧ t.getReg .x10 = 0 ∧
      RegsExcept s t [.x5,.x10] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound haltSetup_blk haltSetup_at s hpc
    (by simp [haltSetup_blk.res,rv_simp]),?_,?_,?_,?_,?_⟩
  · simp [haltSetup_blk.res,E.eval]
  · simp [haltSetup_blk.res,rv_simp]
  · simp [haltSetup_blk.res,rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [haltSetup_blk.res,rv_simp] <;> rfl
  · intro A _ _; simp [haltSetup_blk.res,rv_simp]
theorem halt_at : CodeAt image (pcOf 541) [0x00000073] :=
  CodeAt.of_append (pre := Images.keygenCode.take 541)
    (post := Images.keygenCode.drop 542) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
theorem fetch_541 (s : MachineState) (hpc : s.pc = pcOf 541) :
    fetch image s = some (.base .ECALL) := (halt_at.fetch s hpc).trans rfl
end SigGolfCandidate.T3M.Keygen
end
-- ==== merged from T3M_Keygen_Main ====
section

namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Digest Cache Region keygen keygenPayload cacheBytes readLE)
open SphincsSecurity (bytesLE bytesLE_length)
theorem initialState_keygen (sk : SecretKey) : initialState submission .keygen sk = some (kinit sk) := by
  have hv := submission_keygen_valid
  unfold initialState
  rw [if_pos hv]
  simp only [submission_keygen, Images.keygenImage, Images.keygenData, MachineState.writeBytesAsWords_nil]
  rfl
structure KDone (r : Digest × Cache) (t : MachineState) : Prop where
  pc : t.pc = pcOf 541
  x5 : t.getReg .x5 = 1
  x10 : t.getReg .x10 = 0
  pk : t.readWords (BitVec.ofNat 64 0xA0) 2 = wordsOf (bytesLE 16 r.1)
  cache : t.readWords (BitVec.ofNat 64 0x80000) 16384 = wordsOf (cacheBytes r.2)
section main
variable {sk : SecretKey} {s1 : MachineState} (hs : KStart sk s1)
include hs
theorem keygen_from_start : TBSim image sk s1 (topTreeW + 172123 + 2489877) keygen KDone := by
  unfold keygen
  refine TBSim.bind (payload_tbsim hs) (fun r t ht => ?_)
  refine TSim.toTBSim (k := 1703623) (n := 2) (b := 2) ?_ (by norm_num)
  obtain ⟨pk,region⟩ := r
  have hsk : FullCache.SkAt t sk := by
    intro j; fin_cases j
    · exact ht.k0
    · exact ht.k8
    · exact ht.k16
    · exact ht.k24
  have hmac := FullCache.mac_tsim false sk region t ht.pc ht.x5 hsk ht.region
  refine TSim.bind (k₂ := 2) (c₂ := 2) (n₂ := 0) (b₂ := 0) hmac (fun tag u hu => ?_)
  obtain ⟨v,st,pc,h5,h10,hr,hf⟩ := haltSetup_spec u hu.pc
  refine TSim.pure_steps st ⟨pc,h5,h10,?_,?_⟩
  · have hpk : DigAt u 0xA0 pk := ht.pk.frame hu.frame (by decide)
        (by simp [FullCache.MacW,FullCache.PRIV,FullCache.KEYS,FullCache.OutW,FullCache.macOut])
        (by simp [FullCache.MacW,FullCache.PRIV,FullCache.KEYS,FullCache.OutW,FullCache.macOut])
    exact (hpk.frame hf (by decide) (fun h => h) (fun h => h)).words
  · show v.readWords (BitVec.ofNat 64 0x80000) (4+16380) = wordsOf (bytesLE 32 tag ++ List.ofFn region)
    rw [Frame.readWords hf 0x80000 (4+16380) (by decide) (fun _ _ h => h),readWords_add,
      wordsOf_append _ _ (by simp [bytesLE_length])]
    rw [show u.readWords (BitVec.ofNat 64 0x80000) 4=wordsOf (bytesLE 32 tag) from hu.words]
    rw [Frame.readWords hu.frame (0x80000+8*4) 16380 (by decide) (fun i hi h => by
      simp only [FullCache.MacW,FullCache.PRIV,FullCache.KEYS,FullCache.OutW,FullCache.macOut,Bool.false_eq_true,ite_false] at h
      omega)]
    exact congrArg _ ht.region
end main
/-- Cycle bound of a keygen run (img-v6): every hash function finishes within it.
`= 26 + 4096 · leafLoopW + 5 + treeW + 172123 + 2489877`. -/
def keygenCycleBound : Nat := 26 + (topTreeW + 172123 + 2489877)
theorem keygenCycleBound_lt : keygenCycleBound + 1 < CYCLE_LIMIT := by
  unfold keygenCycleBound topTreeW leafLoopW topLeafW CYCLE_LIMIT; decide
theorem keygen_tbsim (sk : SecretKey) : TBSim image sk (kinit sk) keygenCycleBound keygen KDone := by
  obtain ⟨s1, st1, hs⟩ := kstart sk
  exact TBSim.steps st1 (keygen_from_start hs)
theorem kdone_output {r : Digest × Cache} {t : MachineState} (h : KDone r t) :
    readOutput submission.sizes submission.layout .keygen t = ((r.1 : PublicKey), cacheB r.2) := by
  show (readBuffer t 160 16, readBuffer t 0x80000 131072) = _
  have e1 : readBuffer t 160 (8 * 2) = BitVec.ofNat _ (readLE (bytesLE 16 r.1)) :=
    readBuffer_of_words t 160 2 (bytesLE 16 r.1) (by decide) (by decide) (bytesLE_length _ _) h.pk
  have e2 : readBuffer t 0x80000 (8 * 16384) = BitVec.ofNat _ (readLE (cacheBytes r.2)) :=
    readBuffer_of_words t 0x80000 16384 (cacheBytes r.2) (by decide) (by decide) (cacheBytes_length r.2) h.cache
  rw [readLE_bytesLE] at e1
  refine Prod.ext ?_ e2
  refine e1.trans (BitVec.eq_of_toNat_eq ?_)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt r.1.isLt]
/-- Top-bytes layer: the keygen run's value and its (data-dependent) hash call / compression counts are those of
`countBoth (mrealize sk keygen)`. -/
theorem keygen_run_counts (sk : SecretKey) :
    (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> submission.run .keygen sk =
      (fun p => (some ((p.1.1 : PublicKey), cacheB p.1.2), p.2.1, p.2.2)) <$>
        countBoth (mrealize sk keygen) :=
  Sim.run_eq submission .keygen sk (initialState_keygen sk) (keygen_tbsim sk)
    (by have := keygenCycleBound_lt; omega) (fun r => some ((r.1 : PublicKey), cacheB r.2))
    (fun _ t h => ⟨fetch_541 t h.pc, h.x5, by rw [if_pos h.x10, kdone_output h]; rfl⟩)
/-- img-v6: for every hash function the keygen run returns the keys of `keygen` (evaluated at `hash`), finishes
within `keygenCycleBound + 1 < CYCLE_LIMIT` cycles, and its hash call / compression counts are those of
`countBoth (mrealize sk keygen)` evaluated at `hash` (the nonce trials make them data dependent). -/
theorem keygen_runWith (hash : Hash) (sk : SecretKey) :
    (submission.runWith hash .keygen sk).value =
        some (((evalWithAnswerFn hash (mrealize sk keygen)).1 : PublicKey),
          cacheB (evalWithAnswerFn hash (mrealize sk keygen)).2) ∧
      (submission.runWith hash .keygen sk).finished = true ∧
      (submission.runWith hash .keygen sk).cycles < CYCLE_LIMIT ∧
      (submission.runWith hash .keygen sk).hashCalls = (evalWithAnswerFn hash (countBoth (mrealize sk keygen))).2.1 ∧
      (submission.runWith hash .keygen sk).hashCompressions =
        (evalWithAnswerFn hash (countBoth (mrealize sk keygen))).2.2 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := Sim.runWith_eval submission .keygen sk (initialState_keygen sk) (keygen_tbsim sk)
    keygenCycleBound_lt (fun r => ((r.1 : PublicKey), cacheB r.2))
    (fun _ t h => ⟨fetch_541 t h.pc, h.x5, h.x10, kdone_output h⟩) hash
  exact ⟨h1, h2, lt_of_le_of_lt h3 keygenCycleBound_lt, h4, h5⟩
theorem keygen_runWith_cycles_lt (hash : Hash) (sk : SecretKey) :
    (submission.runWith hash .keygen sk).cycles < CYCLE_LIMIT := (keygen_runWith hash sk).2.2.1
end SigGolfCandidate.T3M.Keygen
end
-- ==== merged from ClaudeWCT_W9_T3M_Final_Discharge ====
section

namespace ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.Legacy OracleComp
open ClaudeWCT.W9.T3M (Images submission)
variable (I : Images)
theorem run_keygen_congr {sA wA sB wB c : Nat} {lA lB : Layout} {iA iB : Phase → Riscv.Image}
    (hk : iA .keygen = iB .keygen) (hvA : (iA .keygen).Valid ⟨sA, wA, c⟩ lA)
    (hvB : (iB .keygen).Valid ⟨sB, wB, c⟩ lB) (hsk : lA.secretKey = lB.secretKey)
    (hpk : lA.publicKey = lB.publicKey) (hc : lA.cache = lB.cache) (sk : SecretKey) :
    Submission.run ⟨⟨sA, wA, c⟩, lA, iA⟩ .keygen sk = Submission.run ⟨⟨sB, wB, c⟩, lB, iB⟩ .keygen sk := by
  obtain ⟨mA, skA, pkA, cA, sgA, wtA⟩ := lA
  obtain ⟨mB, skB, pkB, cB, sgB, wtB⟩ := lB
  dsimp only at hsk hpk hc
  subst hsk hpk hc
  have hinit : initialState ⟨⟨sA, wA, c⟩, ⟨mA, skA, pkA, cA, sgA, wtA⟩, iA⟩ .keygen sk =
      initialState ⟨⟨sB, wB, c⟩, ⟨mB, skA, pkA, cA, sgB, wtB⟩, iB⟩ .keygen sk := by
    unfold initialState
    dsimp only
    rw [if_pos hvA, if_pos hvB, hk]
    rfl
  unfold Submission.run
  rw [hinit]
  dsimp only
  rw [hk]
  rfl
theorem keygen_run_eq (hadm : (submission I).Admissible) (sk : SecretKey) :
    (submission I).run .keygen sk = SigGolfCandidate.T3M.submission.run .keygen sk := by
  have hvA : ((submission I).image .keygen).Valid ⟨5310, 22012, 131072⟩ ⟨0x6620, 0x80, 0xa0, 0x80000, 0x7000, 0x1020⟩ :=
    hadm.2 .keygen
  have hvB : (SigGolfCandidate.T3M.submission.image .keygen).Valid
      ⟨SigGolfCandidate.T3M.submission.sizes.signature, SigGolfCandidate.T3M.submission.sizes.witness, 131072⟩
      SigGolfCandidate.T3M.submission.layout := SigGolfCandidate.T3M.submission_keygen_valid
  have hk : (submission I).image .keygen = SigGolfCandidate.T3M.submission.image .keygen := by
    rw [ClaudeWCT.W9.T3M.submission_keygen, SigGolfCandidate.T3M.submission_keygen]
  exact run_keygen_congr (iA := (submission I).image) (iB := SigGolfCandidate.T3M.submission.image) hk hvA hvB
    (by rw [SigGolfCandidate.T3M.submission_layout]) (by rw [SigGolfCandidate.T3M.submission_layout])
    (by rw [SigGolfCandidate.T3M.submission_layout]) sk
theorem keygen_run_counts_holds (hadm : (submission I).Admissible) : KeygenRunCounts I := fun sk => by
  rw [keygen_run_eq I hadm sk]
  exact SigGolfCandidate.T3M.Keygen.keygen_run_counts sk
theorem keygen_runWith_holds (hadm : (submission I).Admissible) : KeygenRunWith I := fun hash sk => by
  unfold Submission.runWith
  rw [keygen_run_eq I hadm sk]
  exact SigGolfCandidate.T3M.Keygen.keygen_runWith hash sk
end ClaudeWCT.W9.T3M.Final

namespace ClaudeWCT.W9.T3M.Final.Paired
open SigGolfCandidate.Legacy OracleComp
open ClaudeWCT.W9.T3M (Images)
variable (I : Images)
theorem keygen_run_eq (hadm : (submission I).Admissible) (sk : SecretKey) :
    (submission I).run .keygen sk = SigGolfCandidate.T3M.submission.run .keygen sk := by
  have hvA : ((submission I).image .keygen).Valid ⟨5195, 22012, 131072⟩ ⟨0x6620, 0x80, 0xa0, 0x80000, 0x7000, 0x1020⟩ :=
    hadm.2 .keygen
  have hvB : (SigGolfCandidate.T3M.submission.image .keygen).Valid
      ⟨SigGolfCandidate.T3M.submission.sizes.signature, SigGolfCandidate.T3M.submission.sizes.witness, 131072⟩
      SigGolfCandidate.T3M.submission.layout := SigGolfCandidate.T3M.submission_keygen_valid
  have hk : (submission I).image .keygen = SigGolfCandidate.T3M.submission.image .keygen := by
    rw [ClaudeWCT.W9.T3M.Paired.submission_keygen, SigGolfCandidate.T3M.submission_keygen]
  exact run_keygen_congr (iA := (submission I).image) (iB := SigGolfCandidate.T3M.submission.image) hk hvA hvB
    (by rw [SigGolfCandidate.T3M.submission_layout]) (by rw [SigGolfCandidate.T3M.submission_layout])
    (by rw [SigGolfCandidate.T3M.submission_layout]) sk
theorem keygen_run_counts_holds (hadm : (submission I).Admissible) : KeygenRunCounts I := fun sk => by
  rw [keygen_run_eq I hadm sk]
  exact SigGolfCandidate.T3M.Keygen.keygen_run_counts sk
theorem keygen_runWith_holds (hadm : (submission I).Admissible) : KeygenRunWith I := fun hash sk => by
  unfold Submission.runWith
  rw [keygen_run_eq I hadm sk]
  exact SigGolfCandidate.T3M.Keygen.keygen_runWith hash sk
end ClaudeWCT.W9.T3M.Final.Paired
end
-- ==== merged from ClaudeWCT_W9_T3M_Final_SourceDischarge ====
section

namespace ClaudeWCT.W9.T3M.Final
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
end ClaudeWCT.W9.T3M.Final

namespace ClaudeWCT.W9.T3M.Final.Paired
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

theorem sourceFacts_of_securityP (expandV6 : SigGolfCandidate.Research.SharedExpansionClosure.ExpandV6Facts)
    (security : SecurityP) (keygenMoment : KeygenMoment) : SourceFacts where
  honest_keygen_exponential_budget := keygenMoment
  source_completeness := ClaudeWCT.W9.T3.Completeness.Paired.source_completeness
  honest_sign_exponential_budget :=
    SigGolfCandidate.Research.SharedSigningBudget.honest_sign_exponential_budget
      SigGolfCandidate.Research.SharedSigningBudget.schemeFixedCostV6_holds
  honest_expand_exponential_budget :=
    SigGolfCandidate.Research.SharedExpansionClosure.honest_expand_exponential_budget expandV6
  hashOnly_keygen := SigGolfCandidate.T3.SourceReplay.hashOnly_keygen
  hashOnly_sign := SigGolfCandidate.Research.SharedForest.hashOnly_sign
  hashOnly_expand := SigGolfCandidate.Research.SharedForest.hashOnly_expand
  hashOnly_verify := SigGolfCandidate.Research.SharedForest.hashOnly_verify
  securityP := security
end ClaudeWCT.W9.T3M.Final.Paired

namespace ClaudeWCT.W9.T3M.Final.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M (isPublic isHash allQ_mono)

private theorem public_is_hash (q : Spec.Domain) (h : isPublic q) : isHash q := by
  rcases q with (tag|input)|coord
  · exact h.elim
  · trivial
  · exact h.elim

theorem sourceQueries_holds : SourceQueries where
  good_sign := SigGolfCandidate.Research.SharedForest.good_sign
  good_expand := SigGolfCandidate.Research.SharedForest.good_expand
  good_verify := SigGolfCandidate.Research.SharedForest.good_verify
  good_expandN := ClaudeWCT.W9.T3M.Paired.goodQ_expandN
  good_verifyP := ClaudeWCT.W9.T3M.Paired.goodQ_verifyP
  public_expandN := ClaudeWCT.W9.T3M.Paired.publicOnly_expandN
  public_expandB := ClaudeWCT.W9.T3M.Paired.publicOnly_expandB
  public_verifyP := ClaudeWCT.W9.T3M.Paired.publicOnly_verifyP
  hashOnly_expandB := fun _ _ _=>allQ_mono (ClaudeWCT.W9.T3M.Paired.publicOnly_expandB ..) public_is_hash
  hashOnly_verifyP := fun _ _ _=>allQ_mono (ClaudeWCT.W9.T3M.Paired.publicOnly_verifyP ..) public_is_hash
end ClaudeWCT.W9.T3M.Final.Paired
end
-- ==== merged from ClaudeWCT_W9_T3M_Final_Conditional ====
section

namespace ClaudeWCT.W9.T3M.Final
open ClaudeWCT.W9.T3M (Images submission)
structure MachineFacts (I : Images) : Prop where
  admissible : (submission I).Admissible
  sign_refines : SignRefines I
  sign_terminates : SignTerminates I
  expand_refines : ExpandRefines I
  expand_terminates : ExpandTerminates I
  verify_refines : VerifyRefines I
  verify_terminates : VerifyTerminates I
  verify_accept_cycles : VerifyAcceptCycles I
theorem pending_of_machine {I : Images} (M : MachineFacts I) : Pending I where
  admissible := M.admissible
  keygen_run_counts := keygen_run_counts_holds I M.admissible
  keygen_runWith := keygen_runWith_holds I M.admissible
  sign_refines := M.sign_refines
  sign_terminates := M.sign_terminates
  expand_refines := M.expand_refines
  expand_terminates := M.expand_terminates
  verify_refines := M.verify_refines
  verify_terminates := M.verify_terminates
  verify_accept_cycles := M.verify_accept_cycles
end ClaudeWCT.W9.T3M.Final

namespace ClaudeWCT.W9.T3M.Final.Paired
open ClaudeWCT.W9.T3M (Images)
structure MachineFacts (I : Images) : Prop where
  admissible : (submission I).Admissible
  sign_refines : SignRefines I
  sign_terminates : SignTerminates I
  expand_refines : ExpandRefines I
  expand_terminates : ExpandTerminates I
  verify_refines : VerifyRefines I
  verify_terminates : VerifyTerminates I
  verify_accept_cycles : VerifyAcceptCycles I
theorem pending_of_machine {I : Images} (M : MachineFacts I) : Pending I where
  admissible := M.admissible
  keygen_run_counts := keygen_run_counts_holds I M.admissible
  keygen_runWith := keygen_runWith_holds I M.admissible
  sign_refines := M.sign_refines
  sign_terminates := M.sign_terminates
  expand_refines := M.expand_refines
  expand_terminates := M.expand_terminates
  verify_refines := M.verify_refines
  verify_terminates := M.verify_terminates
  verify_accept_cycles := M.verify_accept_cycles
theorem certificate_of_security {I : Images}
    (expandV6 : SigGolfCandidate.Research.SharedExpansionClosure.ExpandV6Facts) (security : SecurityP)
    (keygenMoment : KeygenMoment) (M : MachineFacts I) :
    SigGolf.Certificate (submissionNew I) 7006 :=
  certificateNew_of encodingFacts sourceQueries_holds (pending_of_machine M) (sourceFacts_of_securityP expandV6 security keygenMoment)
end ClaudeWCT.W9.T3M.Final.Paired
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_CapFail ====
section

/-! # Top-nonce layer: the cap-failure event is negligible (r3-lean-nonsec, subagent C)

`CapFail labels`: some top position (layer 0, children level `< 11`, nonce-0 representative) has every one of its
`trialCap = 104 · 2^b_h` nonce trials failing the zero test of height `h = level + 1` (`b_h = topZeroBits h`; campaign
T51: `b_1..b_11 = 0,0,1,1,2,3,4,5,6,7,8`, #938 had `b_h = h`). Under uniformly random labels the trials of one position
are distinct nodes, so each fails independently with probability at most `1 - 2^-b_h` (heights with `b_h = 0` never
fail); a union bound over the `2^(12-h)` positions of each height gives `Pr[CapFail] ≤ 2^-145.8 ≤ 2^-142`. -/
namespace ClaudeWCT.W9.T3.Security.CanonGraph
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable

/-- Some top position exhausts its nonce cap: every trial inside the cap fails the zero test. -/
def CapFail (labels : Labels) : Prop :=
  ∃ n : TreeNode, n.1.lay = 0 ∧ n.1.level.val < 11 ∧ n.1.nonce.val = 0 ∧
    ∀ j < trialCap n.1.lay n.1.level.val, trialFails labels n j

noncomputable local instance instSampleableTypeLabels_capFail : SampleableType Labels :=
  SampleableType.ofFintype _

namespace CapFailBound

/-! ### Uniform functions: events on a finite set of coordinates -/

theorem card_filter_forall_mem {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    (S : Finset α) (q : β → Prop) [DecidablePred q] [DecidablePred (fun f : α → β => ∀ a ∈ S, q (f a))] :
    (Finset.univ.filter (fun f : α → β => ∀ a ∈ S, q (f a))).card =
      (Finset.univ.filter q).card ^ S.card * Fintype.card β ^ (Fintype.card α - S.card) := by
  classical
  have hset : Finset.univ.filter (fun f : α → β => ∀ a ∈ S, q (f a)) =
      Fintype.piFinset (fun a => if a ∈ S then Finset.univ.filter q else Finset.univ) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h a
      split_ifs with ha
      · simpa using h a ha
      · exact Finset.mem_univ _
    · intro h a ha
      simpa [ha] using h a
  rw [hset, Fintype.card_piFinset]
  simp only [apply_ite Finset.card]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, Finset.card_univ]
  have h1 : (Finset.univ.filter (fun a => a ∈ S)) = S := by ext; simp
  have h2 : (Finset.univ.filter (fun a => a ∉ S)) = Sᶜ := by ext; simp
  rw [h1, h2, Finset.card_compl]

theorem prob_forall_mem {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [Nonempty β]
    [inst : SampleableType (α → β)] (S : Finset α) (q : β → Prop) [DecidablePred q] :
    Pr[fun f : α → β => ∀ a ∈ S, q (f a) | ($ᵗ (α → β) : ProbComp (α → β))] =
      (((Finset.univ.filter q).card : ℝ≥0∞) / Fintype.card β) ^ S.card := by
  classical
  rw [probEvent_uniformSample, card_filter_forall_mem, Fintype.card_fun]
  have hk : S.card ≤ Fintype.card α := Finset.card_le_univ S
  have hB0 : (Fintype.card β : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hBt : (Fintype.card β : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hsplit : Fintype.card β ^ Fintype.card α =
      Fintype.card β ^ S.card * Fintype.card β ^ (Fintype.card α - S.card) := by
    rw [← pow_add, Nat.add_sub_cancel' hk]
  rw [hsplit]
  push_cast
  rw [ENNReal.mul_div_mul_right _ _ (pow_ne_zero _ hB0) (ENNReal.pow_ne_top hBt),
    div_eq_mul_inv, div_eq_mul_inv, mul_pow, ENNReal.inv_pow]

/-! ### The zero test passes with probability at least `2^-h` -/

/-- Campaign T51: the top zero bits are `b_h = 0,0,1,1,2,3,4,5,6,7,8` (#938: `b_h = h`; restated). -/
theorem topZeroBits_eq {h : Nat} (hh : h ≤ 11) : topZeroBits h = topZeroAlloc.getD h 0 := rfl

theorem topZeroBits_le_eight (h : Nat) : topZeroBits h ≤ 8 := by
  unfold topZeroBits
  by_cases hh : h < 12
  · interval_cases h <;> decide
  · rw [List.getD_eq_default _ _ (by simp only [topZeroAlloc, List.length_cons, List.length_nil]; omega)]
    omega

theorem card_pass_digest {h : Nat} (h11 : h ≤ 11) :
    2 ^ (128 - topZeroBits h) ≤
      (Finset.univ.filter (fun d : BitVec 128 => topZeroOk h d = true)).card := by
  by_cases he : h = 11
  · subst he
    have hb : topZeroBits 11 = 8 := rfl
    rw [hb]
    have hc : ((Finset.range (2 ^ 16)) ×ˢ (Finset.range (2 ^ 104))).card = 2 ^ (128 - 8) := by
      rw [Finset.card_product, Finset.card_range, Finset.card_range]; norm_num
    rw [← hc]
    apply Finset.card_le_card_of_injOn (fun p : Nat × Nat => (BitVec.ofNat 128 (p.1 * 2 ^ 112 + p.2) :
      BitVec 128))
    · intro p hp
      simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio] at hp
      refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
      unfold topZeroOk
      rw [if_pos rfl]
      simp only [BitVec.toNat_ofNat, beq_iff_eq]
      obtain ⟨h1, h2⟩ := hp
      norm_num at h1 h2 ⊢
      omega
    · intro p hp p' hp' heq
      simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio] at hp hp'
      have := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_ofNat] at this
      obtain ⟨h1, h2⟩ := hp
      obtain ⟨h1', h2'⟩ := hp'
      norm_num at h1 h2 h1' h2' this
      apply Prod.ext <;> omega
  · have hb8 := topZeroBits_le_eight h
    have hlt : 2 ^ (128 - topZeroBits h) ≤ 2 ^ 128 := Nat.pow_le_pow_right (by decide) (by omega)
    have hc : (Finset.range (2 ^ (128 - topZeroBits h))).card = 2 ^ (128 - topZeroBits h) := Finset.card_range _
    rw [← hc]
    apply Finset.card_le_card_of_injOn (fun x : Nat => (BitVec.ofNat 128 x : BitVec 128))
    · intro x hx
      simp only [Finset.coe_range, Set.mem_Iio] at hx
      refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
      unfold topZeroOk
      rw [if_neg he]
      simp only [BitVec.toNat_ofNat, beq_iff_eq]
      rw [Nat.mod_eq_of_lt (by omega)]
      exact Nat.div_eq_of_lt hx
    · intro x hx y hy heq
      simp only [Finset.coe_range, Set.mem_Iio] at hx hy
      have := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_ofNat] at this
      rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this

/-- The halves map: injective pairing of two digests into an output with prescribed halves. -/
noncomputable def joinHalves (a b : BitVec 128) : BitVec 256 :=
  (SphincsSecurity.splitHashOutputEquiv 128 (by decide)).symm (a, b)

theorem joinHalves_low (a b : BitVec 128) : (joinHalves a b).extractLsb' 0 128 = a :=
  congrArg Prod.fst (Equiv.apply_symm_apply (SphincsSecurity.splitHashOutputEquiv 128 (by decide)) (a, b))

theorem joinHalves_high (a b : BitVec 128) : (joinHalves a b).extractLsb' 128 128 = b :=
  congrArg Prod.snd (Equiv.apply_symm_apply (SphincsSecurity.splitHashOutputEquiv 128 (by decide)) (a, b))

theorem card_pass_hash (p : Extract.Pos) {h : Nat} (h11 : h ≤ 11) :
    2 ^ (256 - topZeroBits h) ≤
      (Finset.univ.filter (fun v : BitVec 256 => ¬ (topZeroOk h (p.proj v) = false))).card := by
  set P := Finset.univ.filter (fun d : BitVec 128 => topZeroOk h d = true)
  have hP := card_pass_digest h11
  have hcard : (P ×ˢ (Finset.univ : Finset (BitVec 128))).card = P.card * 2 ^ 128 := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_bitVec]
  have hb8 := topZeroBits_le_eight h
  have h256 : 2 ^ (256 - topZeroBits h) ≤ P.card * 2 ^ 128 := by
    calc 2 ^ (256 - topZeroBits h) = 2 ^ (128 - topZeroBits h) * 2 ^ 128 := by
          rw [← pow_add, show 128 - topZeroBits h + 128 = 256 - topZeroBits h by omega]
      _ ≤ P.card * 2 ^ 128 := Nat.mul_le_mul_right _ hP
  refine h256.trans ?_
  rw [← hcard]
  apply Finset.card_le_card_of_injOn
    (fun x : BitVec 128 × BitVec 128 =>
      if p.high then joinHalves x.2 x.1 else joinHalves x.1 x.2)
  · intro x hx
    simp only [Finset.coe_product, Finset.coe_univ, Set.prod_univ, Set.mem_preimage, Finset.mem_coe, P,
      Finset.mem_filter, Finset.mem_univ, true_and] at hx
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
    rw [Extract.Pos.proj_eq]
    cases p.high
    · simp only [Bool.false_eq_true, ite_false, joinHalves_low, hx]; decide
    · simp only [ite_true, joinHalves_high, hx]; decide
  · intro x _ y _ heq
    by_cases hp : p.high = true
    · simp only [hp, ite_true] at heq
      have h1 := congrArg (fun v : BitVec 256 => v.extractLsb' 0 128) heq
      have h2 := congrArg (fun v : BitVec 256 => v.extractLsb' 128 128) heq
      simp only [joinHalves_low, joinHalves_high] at h1 h2
      exact Prod.ext h2 h1
    · simp only [Bool.not_eq_true] at hp
      simp only [hp, Bool.false_eq_true, ite_false] at heq
      have h1 := congrArg (fun v : BitVec 256 => v.extractLsb' 0 128) heq
      have h2 := congrArg (fun v : BitVec 256 => v.extractLsb' 128 128) heq
      simp only [joinHalves_low, joinHalves_high] at h1 h2
      exact Prod.ext h1 h2

theorem card_fail_hash (p : Extract.Pos) {h : Nat} (h11 : h ≤ 11) :
    (Finset.univ.filter (fun v : BitVec 256 => topZeroOk h (p.proj v) = false)).card +
      2 ^ (256 - topZeroBits h) ≤ 2 ^ 256 := by
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (BitVec 256))) (fun v => topZeroOk h (p.proj v) = false)
  rw [Finset.card_univ, Fintype.card_bitVec] at hsum
  have := card_pass_hash p h11
  change _ = 2 ^ 256 at hsum
  omega

theorem ratio_le {Q h : Nat} (hQ : Q + 2 ^ (256 - h) ≤ 2 ^ 256) (hh : h ≤ 256) :
    (Q : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) ≤ ENNReal.ofReal (1 - (1 / 2) ^ h) := by
  rw [← ENNReal.ofReal_natCast Q, ← ENNReal.ofReal_natCast (2 ^ 256),
    ← ENNReal.ofReal_div_of_pos (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hQ' : (Q : ℝ) + 2 ^ (256 - h) ≤ 2 ^ 256 := by exact_mod_cast hQ
  have h2 : (2 : ℝ) ^ 256 = 2 ^ (256 - h) * 2 ^ h := by rw [← pow_add, Nat.sub_add_cancel hh]
  have hpos : (0 : ℝ) < 2 ^ h := by positivity
  rw [div_le_iff₀ (by positivity), Nat.cast_pow, Nat.cast_ofNat]
  rw [h2] at hQ' ⊢
  have : (1 - (1 / 2 : ℝ) ^ h) * (2 ^ (256 - h) * 2 ^ h) = 2 ^ (256 - h) * 2 ^ h - 2 ^ (256 - h) := by
    rw [one_div_pow]; field_simp
  rw [this]; linarith

/-! ### One position -/

/-- The cap trials of the position of `n`. -/
def trialSet (n : TreeNode) : Finset Node :=
  (Finset.range (trialCap n.1.lay n.1.level.val)).image (fun j => Node.node (withNonce n j))

theorem trialSet_card (n : TreeNode) : (trialSet n).card = trialCap n.1.lay n.1.level.val := by
  unfold trialSet
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj hij
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  have hc := trialCap_le n.1.lay n.1.level.val
  have h := congrArg (fun m : TreeNode => m.1.nonce.val) (Node.node.inj hij)
  rwa [withNonce_nonce n (by omega), withNonce_nonce n (by omega)] at h

theorem allFail_iff (labels : Labels) (n : TreeNode) :
    (∀ j < trialCap n.1.lay n.1.level.val, trialFails labels n j) ↔
      ∀ a ∈ trialSet n, topZeroOk (n.1.level.val + 1) ((Node.node n).toPos.proj (labels a)) = false := by
  unfold trialSet
  constructor
  · intro h a ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
    exact h j (Finset.mem_range.mp hj)
  · intro h j hj
    exact h _ (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩)

/-- Campaign T51: the cap of height `h = level + 1` is `104 · 2^b_h` (#938: `104 · 2^h`; restated). -/
theorem trialCap_top {lay : Layer} {level : Nat} (hl : lay = 0) (hlev : level < 11) :
    trialCap lay level = 104 * 2 ^ topZeroBits (level + 1) := by
  unfold trialCap topNonceCap
  rw [if_pos ⟨hl, hlev⟩]

/-- The real cap-failure bound of one position at children level `l` (zero bits `b = topZeroBits (l + 1)`). -/
noncomputable def failR (l : Nat) : ℝ :=
  (1 - (1 / 2) ^ topZeroBits (l + 1)) ^ (104 * 2 ^ topZeroBits (l + 1))

theorem prob_allFail_le (n : TreeNode) (hl : n.1.lay = 0) (hlev : n.1.level.val < 11) :
    Pr[fun labels : Labels => ∀ j < trialCap n.1.lay n.1.level.val, trialFails labels n j |
      ($ᵗ Labels : ProbComp Labels)] ≤ ENNReal.ofReal (failR n.1.level.val) := by
  classical
  have hev : (fun labels : Labels => ∀ j < trialCap n.1.lay n.1.level.val, trialFails labels n j) =
      (fun labels : Labels => ∀ a ∈ trialSet n,
        (fun v => topZeroOk (n.1.level.val + 1) ((Node.node n).toPos.proj v) = false) (labels a)) := by
    funext labels; exact propext (allFail_iff labels n)
  rw [hev]
  refine (le_of_eq (prob_forall_mem (α := Node) (β := HashOutput) (inst := instSampleableTypeLabels_capFail)
    (trialSet n) (fun v => topZeroOk (n.1.level.val + 1) ((Node.node n).toPos.proj v) = false))).trans ?_
  rw [trialSet_card, trialCap_top hl hlev, Fintype.card_bitVec]
  unfold failR
  rw [ENNReal.ofReal_pow (by
    have : (1 / 2 : ℝ) ^ topZeroBits (n.1.level.val + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith)]
  gcongr
  have hf := card_fail_hash (Node.node n).toPos (h := n.1.level.val + 1) (by omega)
  have := ratio_le hf (by have := topZeroBits_le_eight (n.1.level.val + 1); omega)
  convert this using 2

/-! ### Union bound over the positions -/

/-- The nonce-0 representatives of the top positions. -/
def topReps : Finset TreeNode :=
  Finset.univ.filter (fun n : TreeNode => n.1.lay = 0 ∧ n.1.level.val < 11 ∧ n.1.nonce.val = 0)

theorem height_zero : height (0 : Layer) = 12 := rfl

theorem card_fiber_le (l : Nat) :
    (topReps.filter (fun n : TreeNode => n.1.level.val = l)).card ≤ 2 ^ (11 - l) := by
  rw [← Finset.card_range (2 ^ (11 - l))]
  apply Finset.card_le_card_of_injOn (fun n : TreeNode => n.1.idx.val)
  · intro n hn
    simp only [topReps, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq] at hn
    obtain ⟨⟨hlay, -, -⟩, hlev⟩ := hn
    have hv := n.2.2.1
    rw [hlay, height_zero, hlev] at hv
    simp only [Finset.coe_range, Set.mem_Iio]
    have : 12 - l - 1 = 11 - l := by omega
    rwa [this] at hv
  · intro n hn m hm heq
    simp only [topReps, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq] at hn hm
    obtain ⟨⟨hlay, -, hnon⟩, hlev⟩ := hn
    obtain ⟨⟨hlay', -, hnon'⟩, hlev'⟩ := hm
    have ht := source_tree_zero n.2.2.2.1 hlay
    have ht' := source_tree_zero m.2.2.2.1 hlay'
    obtain ⟨⟨lay, tree, level, idx, nonce⟩, hv⟩ := n
    obtain ⟨⟨lay', tree', level', idx', nonce'⟩, hv'⟩ := m
    simp only at hlay hlev hnon hlay' hlev' hnon' ht ht' heq
    subst hlay hlay'
    have e1 : tree = tree' := Fin.ext (by omega)
    have e2 : level = level' := Fin.ext (by omega)
    have e3 : idx = idx' := Fin.ext heq
    have e4 : nonce = nonce' := Fin.ext (by omega)
    subst e1 e2 e3 e4
    rfl

theorem capFail_eq :
    CapFail = fun labels : Labels =>
      ∃ n ∈ topReps, ∀ j < trialCap n.1.lay n.1.level.val, trialFails labels n j := by
  funext labels
  simp only [CapFail, topReps, Finset.mem_filter, Finset.mem_univ, true_and, and_assoc]

/-! ### Arithmetic -/

/-- Rational bounds on `(1 - 2^-b)^(2^b)`, `b = topZeroBits (l + 1)` (T51: `b = 0,0,1,1,2,3,4,5,6,7,8` for
`l = 0..10`; `b = 0` gives `0`). -/
noncomputable def capR (l : Nat) : ℝ :=
  if l ≤ 1 then 0 else if l ≤ 3 then 1 / 4 else if l = 4 then 3165 / 10000 else if l = 5 then 3437 / 10000 else
    if l = 6 then 3561 / 10000 else if l = 7 then 3622 / 10000 else 36788 / 100000

theorem base_le_exp (h : Nat) : (1 - (1 / 2 : ℝ) ^ h) ^ (2 ^ h) ≤ 36788 / 100000 := by
  have hx0 : 0 ≤ 1 - (1 / 2 : ℝ) ^ h := by
    have : (1 / 2 : ℝ) ^ h ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  have hx : 1 - (1 / 2 : ℝ) ^ h ≤ Real.exp (-(1 / 2) ^ h) := by
    linarith [Real.add_one_le_exp (-(1 / 2 : ℝ) ^ h)]
  calc (1 - (1 / 2 : ℝ) ^ h) ^ (2 ^ h) ≤ Real.exp (-(1 / 2) ^ h) ^ (2 ^ h) :=
        pow_le_pow_left₀ hx0 hx _
    _ = Real.exp (((2 ^ h : Nat) : ℝ) * (-(1 / 2) ^ h)) := (Real.exp_nat_mul _ _).symm
    _ = Real.exp (-1) := by
        congr 1; push_cast; rw [one_div_pow, mul_neg, mul_one_div_cancel (by positivity)]
    _ ≤ 36788 / 100000 := by
        rw [Real.exp_neg]
        have he := Real.exp_one_gt_d9
        rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
        linarith

theorem failR_le (l : Nat) (r : ℝ)
    (hr : (1 - (1 / 2 : ℝ) ^ topZeroBits (l + 1)) ^ (2 ^ topZeroBits (l + 1)) ≤ r) :
    failR l ≤ r ^ 104 := by
  unfold failR
  have hx0 : 0 ≤ 1 - (1 / 2 : ℝ) ^ topZeroBits (l + 1) := by
    have : (1 / 2 : ℝ) ^ topZeroBits (l + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  rw [mul_comm, pow_mul]
  exact pow_le_pow_left₀ (pow_nonneg hx0 _) hr _

theorem failR_nonneg (l : Nat) : 0 ≤ failR l := by
  unfold failR
  apply pow_nonneg
  have : (1 / 2 : ℝ) ^ topZeroBits (l + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  linarith

theorem sum_capR :
    ∑ l ∈ Finset.range 11, ((2 ^ (11 - l) : Nat) : ℝ) * capR l ^ 104 ≤ 1 / 2 ^ 142 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, capR]
  norm_num

theorem sum_failR :
    ∑ l ∈ Finset.range 11, ((2 ^ (11 - l) : Nat) : ℝ) * failR l ≤ 1 / 2 ^ 142 := by
  refine le_trans (Finset.sum_le_sum fun l hl => ?_) sum_capR
  simp only [Finset.mem_range] at hl
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply failR_le
  by_cases h8 : 8 ≤ l
  · have : capR l = 36788 / 100000 := by
      unfold capR; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega)]
    rw [this]; exact base_le_exp _
  · interval_cases l <;> norm_num [capR, topZeroBits, topZeroAlloc]

end CapFailBound

open CapFailBound in
/-- **Cap failure is negligible**: under uniformly random labels, some top position exhausts its nonce cap with
probability at most `2^-142`. -/
theorem prob_capFail_le :
    Pr[CapFail | ($ᵗ Labels : ProbComp Labels)] ≤ (2 ^ 142 : ℝ≥0∞)⁻¹ := by
  rw [capFail_eq]
  refine (probEvent_exists_finset_le_sum topReps _ _).trans ?_
  calc ∑ n ∈ topReps, Pr[fun labels : Labels =>
          ∀ j < trialCap n.1.lay n.1.level.val, trialFails labels n j | ($ᵗ Labels : ProbComp Labels)]
      ≤ ∑ n ∈ topReps, ENNReal.ofReal (failR n.1.level.val) := by
        apply Finset.sum_le_sum
        intro n hn
        simp only [topReps, Finset.mem_filter, Finset.mem_univ, true_and] at hn
        exact prob_allFail_le n hn.1 hn.2.1
    _ = ∑ l ∈ Finset.range 11, ∑ n ∈ topReps.filter (fun n : TreeNode => n.1.level.val = l),
          ENNReal.ofReal (failR n.1.level.val) := by
        rw [Finset.sum_fiberwise_of_maps_to]
        intro n hn
        simp only [topReps, Finset.mem_filter, Finset.mem_univ, true_and] at hn
        exact Finset.mem_range.mpr hn.2.1
    _ ≤ ∑ l ∈ Finset.range 11, ((2 ^ (11 - l) : Nat) : ℝ≥0∞) * ENNReal.ofReal (failR l) := by
        apply Finset.sum_le_sum
        intro l _
        have hfib := card_fiber_le l
        calc ∑ n ∈ topReps.filter (fun n : TreeNode => n.1.level.val = l), ENNReal.ofReal (failR n.1.level.val)
            = ∑ n ∈ topReps.filter (fun n : TreeNode => n.1.level.val = l), ENNReal.ofReal (failR l) :=
              Finset.sum_congr rfl (fun n hn => by simp only [Finset.mem_filter] at hn; rw [hn.2])
          _ = ((topReps.filter (fun n : TreeNode => n.1.level.val = l)).card : ℝ≥0∞) *
                ENNReal.ofReal (failR l) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ _ := by gcongr
    _ = ENNReal.ofReal (∑ l ∈ Finset.range 11, ((2 ^ (11 - l) : Nat) : ℝ) * failR l) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun l _ => mul_nonneg (by positivity) (failR_nonneg l))]
        apply Finset.sum_congr rfl
        intro l _
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (1 / 2 ^ 142) := ENNReal.ofReal_le_ofReal sum_failR
    _ = (2 ^ 142 : ℝ≥0∞)⁻¹ := by
        rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
          ENNReal.ofReal_ofNat]


end ClaudeWCT.W9.T3.Security.CanonGraph
end
-- ==== merged from T3_Secc_LargePotential ====
section

section
namespace SphincsSecurity.Concrete.PrimitiveMessagePotential
noncomputable def value (space probes remaining : ℝ) : ℝ :=
  1 - ((space - probes - remaining) / (space - probes)) ^ 2
theorem initial (space budget : ℝ) (hspace : space ≠ 0) :
    value space 0 budget = 2 * (budget / space) - (budget / space) ^ 2 := by
  unfold value
  simp only [sub_zero]
  field_simp
  ring
theorem probe_balance (space probes remaining : ℝ)
    (hspace : space - probes ≠ 0) (hnext : space - (probes + 1) ≠ 0) :
    value space probes 1 + (1 - value space probes 1) * value space (probes + 1) remaining =
      value space probes (remaining + 1) := by
  unfold value
  field_simp
  ring
theorem hazard (space probes : ℝ) (hspace : space - probes ≠ 0) :
    value space probes 1 = 1 - (1 - (space - probes)⁻¹) ^ 2 := by
  unfold value
  field_simp
theorem toReal_hazard (space probes : Nat) (hprobes : probes < space) :
    (1 - (1 - ((space - probes : Nat) : ENNReal)⁻¹) ^ 2 : ENNReal).toReal = value space probes 1 := by
  have hminimum : 1 ≤ space - probes := Nat.sub_pos_of_lt hprobes
  have hinverse : ((space - probes : Nat) : ENNReal)⁻¹ ≤ 1 := by
    apply ENNReal.inv_le_one.mpr
    exact_mod_cast hminimum
  have hsub : (1 - ((space - probes : Nat) : ENNReal)⁻¹ : ENNReal) ≤ 1 := tsub_le_self
  have hsquare : (1 - ((space - probes : Nat) : ENNReal)⁻¹) ^ 2 ≤ (1 : ENNReal) := by
    simpa only [pow_two, mul_one] using mul_le_mul' hsub hsub
  have hden : (space : ℝ) - probes ≠ 0 := ne_of_gt (sub_pos.mpr (Nat.cast_lt.mpr hprobes))
  rw [ENNReal.toReal_sub_of_le hsquare (by simp), ENNReal.toReal_one, ENNReal.toReal_pow,
    ENNReal.toReal_sub_of_le hinverse (by simp), ENNReal.toReal_one, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, Nat.cast_sub hprobes.le, hazard _ _ hden]
theorem bounds (space probes remaining : ℝ) (hremaining : 0 ≤ remaining)
    (hbudget : probes + remaining < space) :
    0 ≤ value space probes remaining ∧ value space probes remaining < 1 := by
  have hden : 0 < space - probes := by linarith
  have hnum : 0 < space - probes - remaining := by linarith
  have hratio : 0 < (space - probes - remaining) / (space - probes) := div_pos hnum hden
  have hone : (space - probes - remaining) / (space - probes) ≤ 1 := by
    apply (div_le_one₀ hden).mpr
    linarith
  unfold value
  constructor
  · nlinarith [sq_nonneg ((space - probes - remaining) / (space - probes)),
      mul_self_le_mul_self hratio.le hone]
  · nlinarith [sq_pos_of_pos hratio]
theorem message_increment (space probes remaining : ℝ) (hspace : space - probes ≠ 0) :
    value space probes (remaining + 1) - value space probes remaining =
      (2 * (space - probes - remaining) - 1) / (space - probes) ^ 2 := by
  unfold value
  field_simp
  ring
theorem message_payment (space probes remaining : ℝ) (hspace : 0 < space)
    (hprobes : 0 ≤ probes) (hremaining : 0 ≤ remaining)
    (hbudget : 2 * (probes + remaining + 1) ≤ space) :
    1 / space + value space probes remaining ≤ value space probes (remaining + 1) := by
  have hden : 0 < space - probes := by linarith
  have hnum : space ≤ 2 * (space - probes - remaining) - 1 := by linarith
  have hsq : (space - probes) ^ 2 ≤ space ^ 2 := by nlinarith
  have hpay : 1 / space ≤ (2 * (space - probes - remaining) - 1) / (space - probes) ^ 2 := by
    calc
      1 / space = space / space ^ 2 := by field_simp
      _ ≤ space / (space - probes) ^ 2 := div_le_div_of_nonneg_left hspace.le (sq_pos_of_pos hden) hsq
      _ ≤ _ := (div_le_div_iff_of_pos_right (sq_pos_of_pos hden)).mpr hnum
  rw [← message_increment space probes remaining (ne_of_gt hden)] at hpay
  linarith
theorem mono_remaining (space probes before after : ℝ) (hbefore : 0 ≤ before)
    (horder : before ≤ after) (hbudget : probes + after < space) :
    value space probes before ≤ value space probes after := by
  have hden : 0 < space - probes := by linarith
  have hsmall : 0 ≤ (space - probes - after) / (space - probes) := div_nonneg (by linarith) hden.le
  have hratio : (space - probes - after) / (space - probes) ≤ (space - probes - before) / (space - probes) :=
    (div_le_div_iff_of_pos_right hden).mpr (by linarith)
  unfold value
  nlinarith [mul_self_le_mul_self hsmall hratio]
theorem mono_probes (space before after remaining : ℝ) (hremaining : 0 ≤ remaining)
    (horder : before ≤ after) (hbudget : after + remaining < space) :
    value space before remaining ≤ value space after remaining := by
  have hafter : 0 < space - after := by linarith
  have hbefore : 0 < space - before := by linarith
  have hquot : remaining / (space - before) ≤ remaining / (space - after) :=
    div_le_div_of_nonneg_left hremaining hafter (by linarith)
  have hratio (probes : ℝ) (hden : space - probes ≠ 0) :
      (space - probes - remaining) / (space - probes) = 1 - remaining / (space - probes) := by
    field_simp
  have hnonnegative : 0 ≤ 1 - remaining / (space - after) := by
    have hle := (div_le_one₀ hafter).mpr (show remaining ≤ space - after by linarith)
    linarith
  unfold value
  rw [hratio before hbefore.ne', hratio after hafter.ne']
  nlinarith [mul_self_le_mul_self hnonnegative (show 1 - remaining / (space - after) ≤
    1 - remaining / (space - before) by linarith)]
theorem nonmessage_step (space probes after remaining probability : ℝ)
    (hremaining : 0 ≤ remaining) (hafter : after ≤ probes + 1) (hbudget : probes + remaining + 1 < space)
    (hhazard : probability ≤ value space probes 1) :
    probability + (1 - probability) * value space after remaining ≤ value space probes (remaining + 1) := by
  have hnext := bounds space (probes + 1) remaining hremaining (by linarith)
  have hfirst := bounds space probes 1 (by norm_num) (by linarith)
  have hcontinuation := mono_probes space after (probes + 1) remaining hremaining hafter (by linarith)
  have hsurvive : 0 ≤ 1 - probability := by linarith
  calc
    _ ≤ probability + (1 - probability) * value space (probes + 1) remaining :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hcontinuation hsurvive)
    _ ≤ value space probes 1 + (1 - value space probes 1) * value space (probes + 1) remaining := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hhazard) (sub_nonneg.mpr hnext.2.le)]
    _ = _ := probe_balance space probes remaining (by linarith) (by linarith)
end SphincsSecurity.Concrete.PrimitiveMessagePotential
end
section
namespace SigGolfCandidate.T3.Security.LargePotential
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
noncomputable def hazard (space probes : Nat) : ENNReal :=
  1 - (1 - ((space - probes : Nat) : ENNReal)⁻¹) ^ 2
noncomputable def continuation (space q calls probes : Nat) : ENNReal :=
  if calls ≤ q then ENNReal.ofReal (PrimitiveMessagePotential.value space probes ((q : ℝ) - calls)) else 0
theorem hazard_le_one (space probes : Nat) : hazard space probes ≤ 1 := tsub_le_self
private theorem real_facts (space q calls probes : Nat) (hspace : 0 < space) (hq : 2 * q ≤ space)
    (hprobes : probes ≤ calls) :
    (0 : ℝ) < space ∧ 2 * (q : ℝ) ≤ space ∧ (probes : ℝ) ≤ calls ∧ (q : ℝ) < space := by
  have h1 : (0 : ℝ) < space := by exact_mod_cast hspace
  have h2 : 2 * (q : ℝ) ≤ space := by exact_mod_cast hq
  have h3 : (probes : ℝ) ≤ calls := by exact_mod_cast hprobes
  refine ⟨h1, h2, h3, by linarith⟩
theorem continuation_anti (space q calls probes calls' probes' : Nat) (hspace : 0 < space)
    (hq : 2 * q ≤ space) (hprobes : probes ≤ calls) (hcalls : calls ≤ calls') (hprobes' : probes' ≤ probes) :
    continuation space q calls' probes' ≤ continuation space q calls probes := by
  unfold continuation
  by_cases h' : calls' ≤ q
  · rw [if_pos h', if_pos (le_trans hcalls h')]
    apply ENNReal.ofReal_le_ofReal
    obtain ⟨hs, hb, hp, hlt⟩ := real_facts space q calls probes hspace hq hprobes
    have hc : (calls : ℝ) ≤ calls' := by exact_mod_cast hcalls
    have hc' : (calls' : ℝ) ≤ q := by exact_mod_cast h'
    have hp' : (probes' : ℝ) ≤ probes := by exact_mod_cast hprobes'
    have hm1 := PrimitiveMessagePotential.mono_probes space probes' probes ((q : ℝ) - calls')
      (by linarith) hp' (by linarith)
    have hm2 := PrimitiveMessagePotential.mono_remaining space probes ((q : ℝ) - calls') ((q : ℝ) - calls)
      (by linarith) (by linarith) (by linarith)
    exact hm1.trans hm2
  · rw [if_neg h']
    exact zero_le
theorem continuation_pay (space q calls probes : Nat) (hspace : 0 < space) (hq : 2 * q ≤ space)
    (hprobes : probes ≤ calls) (hcall : calls + 1 ≤ q) :
    continuation space q (calls + 1) probes + (space : ENNReal)⁻¹ ≤ continuation space q calls probes := by
  obtain ⟨hs, hb, hp, hlt⟩ := real_facts space q calls probes hspace hq hprobes
  have hc : (calls : ℝ) + 1 ≤ q := by exact_mod_cast hcall
  unfold continuation
  rw [if_pos hcall, if_pos (by omega)]
  have hpay := PrimitiveMessagePotential.message_payment space probes ((q : ℝ) - ((calls + 1 : Nat) : ℝ)) hs
    (by positivity) (by push_cast; linarith) (by push_cast; linarith)
  have heq : (q : ℝ) - ((calls + 1 : Nat) : ℝ) + 1 = (q : ℝ) - calls := by push_cast; ring
  rw [heq] at hpay
  have hv := (PrimitiveMessagePotential.bounds space probes ((q : ℝ) - ((calls + 1 : Nat) : ℝ))
    (by push_cast; linarith) (by push_cast; linarith)).1
  have hfinal := ENNReal.ofReal_le_ofReal hpay
  rw [ENNReal.ofReal_add (by positivity) hv, one_div, ENNReal.ofReal_inv_of_pos hs, ENNReal.ofReal_natCast] at hfinal
  rw [add_comm]
  exact hfinal
theorem ennreal_mixture_le (probability : ENNReal) (hprobability : probability ≤ 1)
    (value bound : ℝ) (hvalue : 0 ≤ value) (hbound : 0 ≤ bound)
    (h : probability.toReal + (1 - probability.toReal) * value ≤ bound) :
    probability + (1 - probability) * ENNReal.ofReal value ≤ ENNReal.ofReal bound := by
  have hp : probability ≠ ⊤ := ne_top_of_le_ne_top (by simp) hprobability
  have hs : 1 - probability ≠ ⊤ := ne_top_of_le_ne_top (by simp) tsub_le_self
  apply (ENNReal.toReal_le_toReal (ENNReal.add_ne_top.mpr ⟨hp, ENNReal.mul_ne_top hs ENNReal.ofReal_ne_top⟩)
    ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_add hp (ENNReal.mul_ne_top hs ENNReal.ofReal_ne_top), ENNReal.toReal_mul,
    ENNReal.toReal_sub_of_le hprobability (by simp), ENNReal.toReal_one,
    ENNReal.toReal_ofReal hvalue, ENNReal.toReal_ofReal hbound]
  exact h
theorem continuation_probe (space q calls probes : Nat) (hspace : 0 < space) (hq : 2 * q ≤ space)
    (hprobes : probes ≤ calls) (hcall : calls + 1 ≤ q) (probability : ENNReal)
    (hhazard : probability ≤ hazard space probes) :
    probability + (1 - probability) * continuation space q (calls + 1) (probes + 1) ≤
      continuation space q calls probes := by
  obtain ⟨hs, hb, hp, hlt⟩ := real_facts space q calls probes hspace hq hprobes
  have hc : (calls : ℝ) + 1 ≤ q := by exact_mod_cast hcall
  have hpl : probes < space := by omega
  unfold continuation
  rw [if_pos hcall, if_pos (by omega)]
  have hone : probability ≤ 1 := hhazard.trans (hazard_le_one space probes)
  have hreal : probability.toReal ≤ PrimitiveMessagePotential.value space probes 1 := by
    have h := ENNReal.toReal_mono (ne_top_of_le_ne_top (by simp) (hazard_le_one space probes)) hhazard
    rwa [hazard, PrimitiveMessagePotential.toReal_hazard space probes hpl] at h
  have hstep := PrimitiveMessagePotential.nonmessage_step space probes ((probes + 1 : Nat) : ℝ)
    ((q : ℝ) - ((calls + 1 : Nat) : ℝ)) probability.toReal (by push_cast; linarith) (by push_cast; linarith)
    (by push_cast; linarith) hreal
  have heq : (q : ℝ) - ((calls + 1 : Nat) : ℝ) + 1 = (q : ℝ) - calls := by push_cast; ring
  rw [heq] at hstep
  have hnext := (PrimitiveMessagePotential.bounds space ((probes + 1 : Nat) : ℝ)
    ((q : ℝ) - ((calls + 1 : Nat) : ℝ)) (by push_cast; linarith) (by push_cast; linarith)).1
  have hbefore := (PrimitiveMessagePotential.bounds space probes ((q : ℝ) - calls)
    (by linarith) (by linarith)).1
  exact ennreal_mixture_le probability hone _ _ hnext hbefore hstep
theorem initial_potential (q : Nat) :
    ENNReal.ofReal (PrimitiveMessagePotential.value (2 ^ 128) 0 ((q : ℝ) - 0)) =
      ENNReal.ofReal (2 * ((q : ℝ) / 2 ^ 128) - ((q : ℝ) / 2 ^ 128) ^ 2) := by
  rw [sub_zero, PrimitiveMessagePotential.initial _ _ (by positivity)]
variable {ι : Type} {spec : OracleSpec ι} {m : Type → Type} [Monad m]
abbrev Step (m : Type → Type) (spec : OracleSpec ι) (σ : Type) :=
  (input : spec.Domain) → σ → m (Option (spec.Range input) × σ)
noncomputable def run {α σ : Type} (step : Step m spec σ) (program : OracleComp spec α) :
    σ → m (Option α × σ) :=
  OracleComp.construct
    (fun value state => pure (some value, state))
    (fun input _ next state => do
      let middle ← step input state
      match middle.1 with
      | none => pure (none, middle.2)
      | some answer => next answer middle.2) program
theorem run_pure {α σ : Type} (step : Step m spec σ) (value : α) (state : σ) :
    run step (pure value : OracleComp spec α) state = pure (some value, state) := rfl
theorem run_query_bind {α σ : Type} (step : Step m spec σ) (input : spec.Domain)
    (next : spec.Range input → OracleComp spec α) (state : σ) :
    run step (liftM (spec.query input) >>= next) state = (do
      let middle ← step input state
      match middle.1 with
      | none => pure (none, middle.2)
      | some answer => run step (next answer) middle.2) := rfl
variable [LawfulMonad m] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
  [EvalDistCompatible m]
def terminal {β σ : Type} (stopValue doneValue : σ → ENNReal) (result : Option β × σ) : ENNReal :=
  result.1.elim (stopValue result.2) (fun _ => doneValue result.2)
theorem run_expected_le {α σ : Type} (step : Step m spec σ) (inv : σ → Prop)
    (potential stopValue doneValue : σ → ENNReal)
    (hdone : ∀ state, inv state → doneValue state ≤ potential state)
    (hpreserve : ∀ input state, inv state → ∀ answer after,
      (some answer, after) ∈ support (step input state) → inv after)
    (hstep : ∀ input state, inv state →
      expectedValue (step input state) (terminal stopValue potential) ≤ potential state)
    (program : OracleComp spec α) (state : σ) (hstate : inv state) :
    expectedValue (run step program state) (terminal stopValue doneValue) ≤ potential state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value =>
      rw [run_pure, expectedValue_pure]
      exact hdone state hstate
  | query_bind input next ih =>
      rw [run_query_bind, expectedValue_bind]
      refine le_trans ?_ (hstep input state hstate)
      apply expectedValue_mono_of_support
      rintro ⟨answer, after⟩ hmiddle
      cases answer with
      | none => simp [terminal]
      | some answer => exact ih answer after (hpreserve input state hstate answer after hmiddle)
structure Charges (σ : Type) where
  calls : σ → Nat
  probes : σ → Nat
  mass : σ → Nat
noncomputable def potential {σ : Type} (ch : Charges σ) (space q : Nat) (state : σ) : ENNReal :=
  continuation space q (ch.calls state) (ch.probes state) + (ch.mass state : ENNReal) / space
noncomputable def stopValue {σ : Type} (ch : Charges σ) (space q : Nat) (state : σ) : ENNReal :=
  (if ch.calls state ≤ q then 1 else 0) + (ch.mass state : ENNReal) / space
noncomputable def doneValue {σ : Type} (ch : Charges σ) (space : Nat) (state : σ) : ENNReal :=
  (ch.mass state : ENNReal) / space
def FreeStep {σ : Type} (step : Step m spec σ) (ch : Charges σ) (input : spec.Domain) (state : σ) : Prop :=
  (∀ result ∈ support (step input state), ch.calls state ≤ ch.calls result.2 ∧
    ch.probes result.2 ≤ ch.probes state ∧ ch.mass result.2 ≤ ch.mass state) ∧
  Pr[fun result => result.1 = none | step input state] = 0
def MassStep {σ : Type} (step : Step m spec σ) (ch : Charges σ) (q : Nat) (input : spec.Domain) (state : σ) :
    Prop :=
  (∀ result ∈ support (step input state), ch.calls state + 1 ≤ ch.calls result.2 ∧
    ch.probes result.2 ≤ ch.probes state ∧
    ch.mass result.2 ≤ ch.mass state + (if ch.calls state + 1 ≤ q then 1 else 0)) ∧
  Pr[fun result => result.1 = none | step input state] = 0
def TestStep {σ : Type} (step : Step m spec σ) (ch : Charges σ) (space : Nat) (input : spec.Domain)
    (state : σ) : Prop :=
  (∀ result ∈ support (step input state), ch.calls state + 1 ≤ ch.calls result.2 ∧
    ch.probes result.2 ≤ ch.probes state ∧ ch.mass result.2 ≤ ch.mass state) ∧
  Pr[fun result => result.1 = none | step input state] ≤ (space : ENNReal)⁻¹
def ProbeStep {σ : Type} (step : Step m spec σ) (ch : Charges σ) (space : Nat) (input : spec.Domain)
    (state : σ) : Prop :=
  (∀ result ∈ support (step input state), ch.calls state + 1 ≤ ch.calls result.2 ∧
    ch.probes result.2 ≤ ch.probes state + 1 ∧ ch.mass result.2 ≤ ch.mass state) ∧
  Pr[fun result => result.1 = none | step input state] ≤ hazard space (ch.probes state)
def StepBound {σ : Type} (step : Step m spec σ) (ch : Charges σ) (space q : Nat) (input : spec.Domain)
    (state : σ) : Prop :=
  FreeStep step ch input state ∨ MassStep step ch q input state ∨ TestStep step ch space input state ∨
    ProbeStep step ch space input state
theorem StepBound.probes_le {σ : Type} {step : Step m spec σ} {ch : Charges σ} {space q : Nat}
    {input : spec.Domain} {state : σ} (h : StepBound step ch space q input state)
    (hprobes : ch.probes state ≤ ch.calls state) :
    ∀ result ∈ support (step input state), ch.probes result.2 ≤ ch.calls result.2 := by
  intro result hresult
  rcases h with h | h | h | h
  · have := h.1 result hresult; omega
  · have := h.1 result hresult; omega
  · have := h.1 result hresult; omega
  · have := h.1 result hresult; omega
theorem terminal_le_of_over {σ : Type} (ch : Charges σ) (space q : Nat) (state : σ) {β : Type}
    (result : Option β × σ) (hover : q < ch.calls state + 1)
    (hcalls : ch.calls state + 1 ≤ ch.calls result.2) (hmass : ch.mass result.2 ≤ ch.mass state) :
    terminal (stopValue ch space q) (potential ch space q) result ≤ (ch.mass state : ENNReal) / space := by
  have hnot : ¬ch.calls result.2 ≤ q := by omega
  have hm : (ch.mass result.2 : ENNReal) / space ≤ (ch.mass state : ENNReal) / space :=
    ENNReal.div_le_div_right (by exact_mod_cast hmass) _
  rcases result with ⟨_ | answer, after⟩
  · simpa [terminal, stopValue, hnot] using hm
  · simpa [terminal, potential, continuation, hnot] using hm
theorem expected_stop_le {β σ : Type} (law : m (Option β × σ)) (value rest : ENNReal) :
    expectedValue law (fun result => (if result.1 = none then 1 else value) + rest) ≤
      Pr[fun result => result.1 = none | law] +
        (1 - Pr[fun result => result.1 = none | law]) * value + rest := by
  have hcompl : Pr[fun result => ¬result.1 = none | law] ≤ 1 - Pr[fun result => result.1 = none | law] := by
    apply ENNReal.le_sub_of_add_le_left probEvent_ne_top
    rw [probEvent_compl]
    exact tsub_le_self
  rw [expectedValue_add]
  have hsplit : expectedValue law (fun result => if result.1 = none then 1 else value) =
      Pr[fun result => result.1 = none | law] + Pr[fun result => ¬result.1 = none | law] * value := by
    rw [expectedValue_def, probEvent_eq_tsum_ite, probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right,
      ← ENNReal.tsum_add]
    apply tsum_congr
    intro result
    by_cases h : result.1 = none <;> simp [h]
  rw [hsplit]
  refine add_le_add (add_le_add le_rfl (mul_le_mul' hcompl le_rfl)) ?_
  exact expectedValue_le_of_le law (fun _ => le_rfl)
section payments
variable {σ : Type} (step : Step m spec σ) (ch : Charges σ) (space q : Nat) (input : spec.Domain) (state : σ)
theorem FreeStep.payment (h : FreeStep step ch input state) (hspace : 0 < space) (hq : 2 * q ≤ space)
    (hprobes : ch.probes state ≤ ch.calls state) :
    expectedValue (step input state) (terminal (stopValue ch space q) (potential ch space q)) ≤
      potential ch space q state := by
  apply expectedValue_le_of_support
  rintro ⟨answer, after⟩ hresult
  obtain ⟨hcalls, hp, hmass⟩ := h.1 _ hresult
  have hsome : answer ≠ none := by
    have := (probEvent_eq_zero_iff.mp h.2) _ hresult
    simpa using this
  obtain ⟨answer, rfl⟩ := Option.ne_none_iff_exists'.mp hsome
  simp only [terminal, Option.elim_some, potential]
  exact add_le_add (continuation_anti space q _ _ _ _ hspace hq hprobes hcalls hp)
    (ENNReal.div_le_div_right (by exact_mod_cast hmass) _)
theorem MassStep.payment (h : MassStep step ch q input state) (hspace : 0 < space) (hq : 2 * q ≤ space)
    (hprobes : ch.probes state ≤ ch.calls state) :
    expectedValue (step input state) (terminal (stopValue ch space q) (potential ch space q)) ≤
      potential ch space q state := by
  apply expectedValue_le_of_support
  rintro ⟨answer, after⟩ hresult
  obtain ⟨hcalls, hp, hmass⟩ := h.1 _ hresult
  by_cases hc : ch.calls state + 1 ≤ q
  · rw [if_pos hc] at hmass
    have hsome : answer ≠ none := by
      have := (probEvent_eq_zero_iff.mp h.2) _ hresult
      simpa using this
    obtain ⟨answer, rfl⟩ := Option.ne_none_iff_exists'.mp hsome
    simp only [terminal, Option.elim_some, potential]
    have hcont := continuation_anti space q (ch.calls state + 1) (ch.probes state) (ch.calls after)
      (ch.probes after) hspace hq (by omega) hcalls hp
    have hpay := continuation_pay space q (ch.calls state) (ch.probes state) hspace hq hprobes hc
    have hm : (ch.mass after : ENNReal) / space ≤ (ch.mass state : ENNReal) / space + (space : ENNReal)⁻¹ := by
      rw [← one_div, ← ENNReal.add_div]
      exact ENNReal.div_le_div_right (by exact_mod_cast hmass) _
    calc
      _ ≤ continuation space q (ch.calls state + 1) (ch.probes state) +
          ((ch.mass state : ENNReal) / space + (space : ENNReal)⁻¹) := add_le_add hcont hm
      _ = (continuation space q (ch.calls state + 1) (ch.probes state) + (space : ENNReal)⁻¹) +
          (ch.mass state : ENNReal) / space := by ring
      _ ≤ _ := add_le_add hpay le_rfl
  · rw [if_neg hc, add_zero] at hmass
    exact (terminal_le_of_over ch space q state (answer, after) (by omega) hcalls hmass).trans le_add_self
theorem TestStep.payment (h : TestStep step ch space input state) (hspace : 0 < space) (hq : 2 * q ≤ space)
    (hprobes : ch.probes state ≤ ch.calls state) :
    expectedValue (step input state) (terminal (stopValue ch space q) (potential ch space q)) ≤
      potential ch space q state := by
  by_cases hc : ch.calls state + 1 ≤ q
  · have hpoint : ∀ result ∈ support (step input state),
        terminal (stopValue ch space q) (potential ch space q) result ≤
          (if result.1 = none then 1 else continuation space q (ch.calls state + 1) (ch.probes state)) +
            (ch.mass state : ENNReal) / space := by
      rintro ⟨answer, after⟩ hresult
      obtain ⟨hcalls, hp, hmass⟩ := h.1 _ hresult
      have hm : (ch.mass after : ENNReal) / space ≤ (ch.mass state : ENNReal) / space :=
        ENNReal.div_le_div_right (by exact_mod_cast hmass) _
      rcases answer with _ | answer
      · simp only [terminal, Option.elim_none, stopValue, if_true]
        exact add_le_add (by split <;> simp) hm
      · simp only [terminal, Option.elim_some, potential, reduceCtorEq, if_false]
        exact add_le_add (continuation_anti space q _ _ _ _ hspace hq (by omega) hcalls hp) hm
    calc
      _ ≤ expectedValue (step input state) (fun result =>
          (if result.1 = none then 1 else continuation space q (ch.calls state + 1) (ch.probes state)) +
            (ch.mass state : ENNReal) / space) := expectedValue_mono_of_support hpoint
      _ ≤ Pr[fun result => result.1 = none | step input state] +
          (1 - Pr[fun result => result.1 = none | step input state]) *
            continuation space q (ch.calls state + 1) (ch.probes state) + (ch.mass state : ENNReal) / space :=
        expected_stop_le _ _ _
      _ ≤ ((space : ENNReal)⁻¹ + continuation space q (ch.calls state + 1) (ch.probes state)) +
          (ch.mass state : ENNReal) / space := by
        refine add_le_add (add_le_add h.2 ?_) le_rfl
        exact mul_le_of_le_one_left' tsub_le_self
      _ ≤ _ := by
        rw [add_comm ((space : ENNReal)⁻¹)]
        exact add_le_add (continuation_pay space q _ _ hspace hq hprobes hc) le_rfl
  · apply expectedValue_le_of_support
    rintro ⟨answer, after⟩ hresult
    obtain ⟨hcalls, hp, hmass⟩ := h.1 _ hresult
    exact (terminal_le_of_over ch space q state (answer, after) (by omega) hcalls hmass).trans le_add_self
theorem ProbeStep.payment (h : ProbeStep step ch space input state) (hspace : 0 < space) (hq : 2 * q ≤ space)
    (hprobes : ch.probes state ≤ ch.calls state) :
    expectedValue (step input state) (terminal (stopValue ch space q) (potential ch space q)) ≤
      potential ch space q state := by
  by_cases hc : ch.calls state + 1 ≤ q
  · have hpoint : ∀ result ∈ support (step input state),
        terminal (stopValue ch space q) (potential ch space q) result ≤
          (if result.1 = none then 1 else continuation space q (ch.calls state + 1) (ch.probes state + 1)) +
            (ch.mass state : ENNReal) / space := by
      rintro ⟨answer, after⟩ hresult
      obtain ⟨hcalls, hp, hmass⟩ := h.1 _ hresult
      have hm : (ch.mass after : ENNReal) / space ≤ (ch.mass state : ENNReal) / space :=
        ENNReal.div_le_div_right (by exact_mod_cast hmass) _
      rcases answer with _ | answer
      · simp only [terminal, Option.elim_none, stopValue, if_true]
        exact add_le_add (by split <;> simp) hm
      · simp only [terminal, Option.elim_some, potential, reduceCtorEq, if_false]
        exact add_le_add (continuation_anti space q _ _ _ _ hspace hq (by omega) hcalls hp) hm
    calc
      _ ≤ expectedValue (step input state) (fun result =>
          (if result.1 = none then 1 else continuation space q (ch.calls state + 1) (ch.probes state + 1)) +
            (ch.mass state : ENNReal) / space) := expectedValue_mono_of_support hpoint
      _ ≤ Pr[fun result => result.1 = none | step input state] +
          (1 - Pr[fun result => result.1 = none | step input state]) *
            continuation space q (ch.calls state + 1) (ch.probes state + 1) + (ch.mass state : ENNReal) / space :=
        expected_stop_le _ _ _
      _ ≤ _ := add_le_add (continuation_probe space q _ _ hspace hq hprobes hc _ h.2) le_rfl
  · apply expectedValue_le_of_support
    rintro ⟨answer, after⟩ hresult
    obtain ⟨hcalls, hp, hmass⟩ := h.1 _ hresult
    exact (terminal_le_of_over ch space q state (answer, after) (by omega) hcalls hmass).trans le_add_self
theorem StepBound.payment (h : StepBound step ch space q input state) (hspace : 0 < space)
    (hq : 2 * q ≤ space) (hprobes : ch.probes state ≤ ch.calls state) :
    expectedValue (step input state) (terminal (stopValue ch space q) (potential ch space q)) ≤
      potential ch space q state := by
  rcases h with h | h | h | h
  · exact h.payment step ch space q input state hspace hq hprobes
  · exact h.payment step ch space q input state hspace hq hprobes
  · exact h.payment step ch space q input state hspace hq hprobes
  · exact h.payment step ch space q input state hspace hq hprobes
end payments
theorem stop_add_mass_eq {β σ : Type} (ch : Charges σ) (space q : Nat) (law : m (Option β × σ)) :
    Pr[fun result => result.1 = none ∧ ch.calls result.2 ≤ q | law] +
      (∑' result, Pr[= result | law] * (ch.mass result.2 : ENNReal)) / space =
      expectedValue law (terminal (stopValue ch space q) (doneValue ch space)) := by
  have hfun : terminal (stopValue ch space q) (doneValue ch space) = fun result : Option β × σ =>
      (if result.1 = none ∧ ch.calls result.2 ≤ q then 1 else 0) + (ch.mass result.2 : ENNReal) / space := by
    funext result
    rcases result with ⟨_ | answer, after⟩
    · simp [terminal, stopValue]
    · simp [terminal, doneValue]
  rw [hfun, expectedValue_add, expectedValue_ite_one, expectedValue_def]
  congr 1
  simp only [div_eq_mul_inv, ← mul_assoc, ENNReal.tsum_mul_right]
theorem run_potential_of_bound {α σ : Type} (step : Step m spec σ) (ch : Charges σ) (space q : Nat)
    (hspace : 0 < space) (hq : 2 * q ≤ space) (inv : σ → Prop)
    (hpreserve : ∀ input state, inv state → ch.probes state ≤ ch.calls state →
      ∀ answer after, (some answer, after) ∈ support (step input state) → inv after)
    (hbound : ∀ input state, inv state → ch.probes state ≤ ch.calls state →
      StepBound step ch space q input state)
    (program : OracleComp spec α) (state : σ) (hstate : inv state)
    (hprobes : ch.probes state ≤ ch.calls state) :
    Pr[fun result => result.1 = none ∧ ch.calls result.2 ≤ q | run step program state] +
      (∑' result, Pr[= result | run step program state] * (ch.mass result.2 : ENNReal)) / space ≤
      potential ch space q state := by
  rw [stop_add_mass_eq]
  refine run_expected_le step (fun state => inv state ∧ ch.probes state ≤ ch.calls state)
    (potential ch space q) (stopValue ch space q) (doneValue ch space) ?_ ?_ ?_ program state ⟨hstate, hprobes⟩
  · intro state _
    exact le_add_self
  · rintro input state ⟨hi, hp⟩ answer after hmem
    exact ⟨hpreserve input state hi hp answer after hmem,
      (hbound input state hi hp).probes_le hp _ hmem⟩
  · rintro input state ⟨hi, hp⟩
    exact (hbound input state hi hp).payment step ch space q input state hspace hq hp
theorem potential_initial_le {σ : Type} (ch : Charges σ) (q : Nat) (hq : q ≤ 2 ^ 127) (state : σ)
    (hprobes : ch.probes state = 0) (hmass : ch.mass state = 0) :
    potential ch (2 ^ 128) q state ≤ ENNReal.ofReal (2 * ((q : ℝ) / 2 ^ 128) - ((q : ℝ) / 2 ^ 128) ^ 2) := by
  have hmono := continuation_anti (2 ^ 128) q 0 0 (ch.calls state) (ch.probes state) (by positivity)
    (by omega) le_rfl (Nat.zero_le _) (by omega)
  unfold potential
  rw [hmass, Nat.cast_zero, ENNReal.zero_div, add_zero]
  refine hmono.trans (le_of_eq ?_)
  unfold continuation
  rw [if_pos (Nat.zero_le q), Nat.cast_zero, Nat.cast_pow, Nat.cast_ofNat]
  exact initial_potential q
theorem run_potential_initial {α σ : Type} (step : Step m spec σ) (ch : Charges σ) (q : Nat)
    (hq : q ≤ 2 ^ 127) (inv : σ → Prop)
    (hpreserve : ∀ input state, inv state → ch.probes state ≤ ch.calls state →
      ∀ answer after, (some answer, after) ∈ support (step input state) → inv after)
    (hbound : ∀ input state, inv state → ch.probes state ≤ ch.calls state →
      StepBound step ch (2 ^ 128) q input state)
    (program : OracleComp spec α) (init : σ) (hinit : inv init) (hprobes : ch.probes init = 0)
    (hmass : ch.mass init = 0) :
    Pr[fun result => result.1 = none ∧ ch.calls result.2 ≤ q | run step program init] +
      (∑' result, Pr[= result | run step program init] * (ch.mass result.2 : ENNReal)) / 2 ^ 128 ≤
      ENNReal.ofReal (2 * ((q : ℝ) / 2 ^ 128) - ((q : ℝ) / 2 ^ 128) ^ 2) := by
  have h := run_potential_of_bound step ch (2 ^ 128) q (by positivity) (by omega) inv hpreserve hbound program init
    hinit (by omega)
  rw [Nat.cast_pow, Nat.cast_ofNat] at h
  exact h.trans (potential_initial_le ch q hq init hprobes hmass)
section observe
variable {α σ : Type} (impl : QueryImpl spec (StateT σ m))
  (test : σ → (input : spec.Domain) → spec.Range input → σ → Prop)
def cut : Option σ × α × σ → Option α × σ
  | (some hit, _, _) => (none, hit)
  | (none, value, final) => (some value, final)
end observe
end SigGolfCandidate.T3.Security.LargePotential
end
end
-- ==== merged from T3_Secc_LargeResidualT3 ====
section

section
namespace SigGolfCandidate.T3.Security.LargeResidual
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete UniformTableCompletion RetainedObservation
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
abbrev Digest := SphincsSecurity.Digest
abbrev HashOutput := SphincsSecurity.HashOutput
def low (answer : HashOutput) : Digest := SphincsSecurity.truncateHash answer
inductive Hit (Coord : Type) where
  | label (parent : Coord)
  | target (value : Digest)
  | selectedTarget (target : Digest) (pickLow : HashOutput → Bool)
structure Probe (Coord : Type) where
  guess : Option (Coord × Digest)
  hit : Hit Coord
section Defs
variable {Coord : Type}
def Hit.isSelected : Hit Coord → Bool
  | .label _ => false
  | .target _ => false
  | .selectedTarget _ _ => true
def Hit.answerValue : Hit Coord → HashOutput → Digest
  | .label _, answer => low answer
  | .target _, answer => low answer
  | .selectedTarget _ pickLow, answer =>
      if pickLow answer then low answer else answer.extractLsb' 128 128
@[simp] theorem Hit.isSelected_label (parent : Coord) : (Hit.label parent).isSelected = false := rfl
@[simp] theorem Hit.isSelected_target (target : Digest) : (Hit.target (Coord := Coord) target).isSelected = false := rfl
@[simp] theorem Hit.isSelected_selectedTarget (target : Digest) (pickLow : HashOutput → Bool) :
    (Hit.selectedTarget (Coord := Coord) target pickLow).isSelected = true := rfl
@[simp] theorem Hit.answerValue_label (parent : Coord) (answer : HashOutput) :
    (Hit.label parent).answerValue answer = low answer := rfl
@[simp] theorem Hit.answerValue_target (target : Digest) (answer : HashOutput) :
    (Hit.target (Coord := Coord) target).answerValue answer = low answer := rfl
@[simp] theorem Hit.answerValue_selectedTarget (target : Digest) (pickLow : HashOutput → Bool) (answer : HashOutput) :
    (Hit.selectedTarget (Coord := Coord) target pickLow).answerValue answer =
      if pickLow answer then low answer else answer.extractLsb' 128 128 := rfl
theorem Hit.answerValue_of_not_selected (hit : Hit Coord) (h : hit.isSelected = false) (answer : HashOutput) :
    hit.answerValue answer = low answer := by
  cases hit <;> simp_all [Hit.isSelected, Hit.answerValue]
def Hit.miss : Hit Coord → (Coord → Digest) → Digest → Prop
  | .label parent, labels, value => labels parent ≠ value
  | .target t, _, value => t ≠ value
  | .selectedTarget t _, _, value => t ≠ value
def Hit.labelMiss : Hit Coord → (Coord → Digest) → Digest → Prop
  | .label parent, labels, value => labels parent ≠ value
  | .target _t, _, _ => True
  | .selectedTarget _ _, _, _ => True
def Hit.answerOk : Hit Coord → Digest → Prop
  | .label _p, _ => True
  | .target t, value => t ≠ value
  | .selectedTarget t _, value => t ≠ value
theorem Hit.miss_iff (hit : Hit Coord) (labels : Coord → Digest) (value : Digest) :
    hit.miss labels value ↔ hit.labelMiss labels value ∧ hit.answerOk value := by
  cases hit <;> simp [Hit.miss, Hit.labelMiss, Hit.answerOk]
def Probe.guessMiss (probe : Probe Coord) (labels : Coord → Digest) : Prop :=
  ∀ g ∈ probe.guess, labels g.1 ≠ g.2
def Probe.keep (probe : Probe Coord) (labels : Coord → Digest) (answer : HashOutput) : Prop :=
  probe.guessMiss labels ∧ probe.hit.miss labels (probe.hit.answerValue answer)
variable [DecidableEq Coord]
def Probe.guessRestrict (probe : Probe Coord) (allowed : Coord → Finset Digest) : Coord → Finset Digest :=
  match probe.guess with
  | none => allowed
  | some g => eraseTableValue allowed g.1 g.2
def Hit.restrict : Hit Coord → (Coord → Finset Digest) → Digest → Coord → Finset Digest
  | .label parent, allowed, value => eraseTableValue allowed parent value
  | .target _, allowed, _ => allowed
  | .selectedTarget _ _, allowed, _ => allowed
def Probe.restrict (probe : Probe Coord) (allowed : Coord → Finset Digest) (answer : HashOutput) :
    Coord → Finset Digest :=
  probe.hit.restrict (probe.guessRestrict allowed) (probe.hit.answerValue answer)
def Probe.Admissible (candidates : Coord → Finset Digest) (hit : Hit Coord) (g : Coord × Digest) : Prop :=
  2 ≤ (candidates g.1).card ∧ (∀ parent, hit = Hit.label parent → g.1 ≠ parent) ∧
    hit.isSelected = false
noncomputable def Probe.effective (candidates : Coord → Finset Digest) (probe : Probe Coord) : Probe Coord :=
  ⟨probe.guess.filter (fun g => decide (Probe.Admissible candidates probe.hit g)), probe.hit⟩
omit [DecidableEq Coord] in
@[simp] theorem Probe.effective_selectedTarget (candidates : Coord → Finset Digest)
    (guess : Option (Coord × Digest)) (target : Digest) (pickLow : HashOutput → Bool) :
    (Probe.effective candidates ⟨guess, .selectedTarget target pickLow⟩) =
      ⟨none, .selectedTarget target pickLow⟩ := by
  cases guess <;> simp [Probe.effective, Probe.Admissible]
end Defs
section Restrict
variable {Coord : Type} [DecidableEq Coord]
theorem mem_eraseTableValue (allowed : Coord → Finset Digest) (c0 : Coord) (v : Digest)
    (labels : Coord → Digest) (c : Coord) :
    labels c ∈ eraseTableValue allowed c0 v c ↔ labels c ∈ allowed c ∧ (c = c0 → labels c ≠ v) := by
  by_cases h : c = c0
  · subst h
    simp only [eraseTableValue, Function.update_self, Finset.mem_erase, true_implies]
    exact and_comm
  · simp only [eraseTableValue, Function.update_of_ne h, h, false_implies, and_true]
theorem eraseTableValue_subset (allowed : Coord → Finset Digest) (c0 : Coord) (v : Digest) (c : Coord) :
    eraseTableValue allowed c0 v c ⊆ allowed c := by
  by_cases h : c = c0
  · subst h
    simp only [eraseTableValue, Function.update_self]
    exact Finset.erase_subset _ _
  · simp only [eraseTableValue, Function.update_of_ne h, subset_refl]
theorem guessRestrict_subset (probe : Probe Coord) (allowed : Coord → Finset Digest) (c : Coord) :
    probe.guessRestrict allowed c ⊆ allowed c := by
  unfold Probe.guessRestrict
  cases probe.guess with
  | none => exact subset_refl _
  | some g => exact eraseTableValue_subset _ _ _ _
theorem Hit.restrict_subset (hit : Hit Coord) (allowed : Coord → Finset Digest) (value : Digest) (c : Coord) :
    hit.restrict allowed value c ⊆ allowed c := by
  cases hit with
  | label parent => exact eraseTableValue_subset _ _ _ _
  | target t => exact subset_refl _
  | selectedTarget t pickLow => exact subset_refl _
theorem restrict_subset (probe : Probe Coord) (allowed : Coord → Finset Digest) (answer : HashOutput) (c : Coord) :
    probe.restrict allowed answer c ⊆ allowed c :=
  (Hit.restrict_subset _ _ _ c).trans (guessRestrict_subset probe allowed c)
theorem mem_guessRestrict (probe : Probe Coord) (allowed : Coord → Finset Digest) (labels : Coord → Digest) :
    (∀ c, labels c ∈ probe.guessRestrict allowed c) ↔ (∀ c, labels c ∈ allowed c) ∧ probe.guessMiss labels := by
  unfold Probe.guessRestrict Probe.guessMiss
  cases hg : probe.guess with
  | none => simp
  | some g =>
      simp only [mem_eraseTableValue, Option.mem_def, Option.some.injEq, forall_eq']
      constructor
      · intro h
        exact ⟨fun c => (h c).1, (h g.1).2 rfl⟩
      · rintro ⟨h, hg'⟩ c
        exact ⟨h c, fun hc => hc ▸ hg'⟩
theorem mem_hitRestrict (hit : Hit Coord) (allowed : Coord → Finset Digest) (value : Digest)
    (labels : Coord → Digest) :
    (∀ c, labels c ∈ hit.restrict allowed value c) ↔ (∀ c, labels c ∈ allowed c) ∧ hit.labelMiss labels value := by
  cases hit with
  | label parent =>
      simp only [Hit.restrict, Hit.labelMiss, mem_eraseTableValue]
      constructor
      · intro h
        exact ⟨fun c => (h c).1, (h parent).2 rfl⟩
      · rintro ⟨h, hp⟩ c
        exact ⟨h c, fun hc => hc ▸ hp⟩
  | target t => simp [Hit.restrict, Hit.labelMiss]
  | selectedTarget t pickLow => simp [Hit.restrict, Hit.labelMiss]
theorem mem_restrict (probe : Probe Coord) (allowed : Coord → Finset Digest) (answer : HashOutput)
    (labels : Coord → Digest) :
    (∀ c, labels c ∈ probe.restrict allowed answer c) ↔
      (∀ c, labels c ∈ allowed c) ∧ probe.guessMiss labels ∧ probe.hit.labelMiss labels (probe.hit.answerValue answer) := by
  unfold Probe.restrict
  rw [mem_hitRestrict, mem_guessRestrict, and_assoc]
end Restrict
section Posterior
variable {Coord : Type} [Fintype Coord] [DecidableEq Coord]
noncomputable def response (labels : Coord → Digest) (probe : Probe Coord) : SPMF HashOutput := do
  let answer ← (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput)
  if probe.keep labels answer then pure answer else failure
noncomputable def lazyResponse (allowed : Coord → Finset Digest) (probe : Probe Coord) : SPMF HashOutput :=
  complete allowed >>= fun labels => response labels probe
omit [Fintype Coord] [DecidableEq Coord] in
theorem response_apply (labels : Coord → Digest) (probe : Probe Coord) (answer : HashOutput) :
    response labels probe answer =
      if probe.keep labels answer then PMF.uniformOfFintype HashOutput answer else 0 := by
  rw [response, SPMF.bind_apply_eq_tsum]
  rw [tsum_eq_single answer]
  · by_cases h : probe.keep labels answer <;> simp only [h, if_true, if_false, SPMF.liftM_apply,
      SPMF.pure_apply_self, SPMF.failure_apply, mul_one, mul_zero]
  · intro other hother
    by_cases h : probe.keep labels other <;> simp only [h, if_true, if_false, SPMF.pure_apply,
      if_neg (Ne.symm hother), SPMF.failure_apply, mul_zero]
theorem Probe.mass (probe : Probe Coord) (allowed : Coord → Finset Digest) (answer : HashOutput)
    (labels : Coord → Digest) :
    (if probe.keep labels answer then complete allowed labels else 0) =
      if probe.hit.answerOk (probe.hit.answerValue answer) then
        restrictionWeight allowed (probe.restrict allowed answer) * complete (probe.restrict allowed answer) labels
      else 0 := by
  by_cases ha : probe.hit.answerOk (probe.hit.answerValue answer)
  · rw [if_pos ha]
    have h := restrict_guard allowed (probe.restrict allowed answer) (restrict_subset probe allowed answer)
      (fun labels => probe.guessMiss labels ∧ probe.hit.labelMiss labels (probe.hit.answerValue answer))
      (fun labels => mem_restrict probe allowed answer labels) labels
    have hkeep : probe.keep labels answer ↔ probe.guessMiss labels ∧ probe.hit.labelMiss labels (probe.hit.answerValue answer) := by
      simp only [Probe.keep, Hit.miss_iff, ha, and_true]
    by_cases hc : probe.guessMiss labels ∧ probe.hit.labelMiss labels (probe.hit.answerValue answer)
    · rw [if_pos (hkeep.mpr hc)]
      rw [if_pos hc] at h
      exact h
    · rw [if_neg (fun h' => hc (hkeep.mp h'))]
      rw [if_neg hc] at h
      exact h
  · have hk : ¬probe.keep labels answer := fun h => ha ((Hit.miss_iff _ _ _).mp h.2).2
    simp only [hk, ha, if_false]
end Posterior
section Hazard
variable {Coord : Type} [Fintype Coord] [DecidableEq Coord]
noncomputable def law (allowed : Coord → Finset Digest) (ha : ∀ c, (allowed c).Nonempty) :
    PMF ((Coord → Digest) × HashOutput) :=
  (uniformTable allowed ha).bind fun labels =>
    (PMF.uniformOfFintype HashOutput).map fun answer => (labels, answer)
omit [Fintype Coord] [DecidableEq Coord] in
theorem response_failure (labels : Coord → Digest) (probe : Probe Coord) :
    (response labels probe).toPMF none =
      Pr[fun answer => ¬probe.keep labels answer | PMF.uniformOfFintype HashOutput] := by
  rw [response, toPMF_bind_lift, PMF.bind_apply, probEvent_eq_tsum_ite]
  apply tsum_congr
  intro answer
  by_cases h : probe.keep labels answer
  · simp only [h, if_true, not_true_eq_false, if_false, SPMF.toPMF_pure, PMF.pure_apply,
      reduceCtorEq, mul_zero]
  · simp only [h, if_false, not_false_eq_true, if_true, SPMF.toPMF_failure, PMF.pure_apply,
      mul_one, PMF.probOutput_eq_apply]
omit [Fintype Coord] [DecidableEq Coord] in
theorem hit_miss_prob (hit : Hit Coord) (labels : Coord → Digest) :
    Pr[fun answer => hit.miss labels (low answer) | PMF.uniformOfFintype HashOutput] =
      1 - (Fintype.card Digest : ENNReal)⁻¹ := by
  cases hit with
  | label parent =>
      have he : (fun answer => Hit.miss (.label parent) labels (low answer)) =
          (fun answer => SphincsSecurity.truncateHash answer ≠ labels parent) := by
        funext answer
        simp only [Hit.miss, low, ne_eq, eq_comm]
      rw [he]
      exact HiddenLabelProbe.prob_truncate_ne (labels parent)
  | target t =>
      have he : (fun answer => Hit.miss (.target t) labels (low answer)) =
          (fun answer => SphincsSecurity.truncateHash answer ≠ t) := by
        funext answer
        simp only [Hit.miss, low, ne_eq, eq_comm]
      rw [he]
      exact HiddenLabelProbe.prob_truncate_ne t
  | selectedTarget t pickLow =>
      have he : (fun answer => Hit.miss (.selectedTarget t pickLow) labels (low answer)) =
          (fun answer => SphincsSecurity.truncateHash answer ≠ t) := by
        funext answer
        simp only [Hit.miss, low, ne_eq, eq_comm]
      rw [he]
      exact HiddenLabelProbe.prob_truncate_ne t
/-- Independent uniform halves both miss every fixed digest with this exact count. -/
theorem card_both_halves_ne (d : Digest) :
    (Finset.univ.filter fun a : HashOutput =>
      a.extractLsb' 0 128 ≠ d ∧ a.extractLsb' 128 128 ≠ d).card =
      (2 ^ 128 - 1) ^ 2 := by
  classical
  calc
    _ = (Finset.univ.filter fun p : Digest × Digest => p.1 ≠ d ∧ p.2 ≠ d).card := by
      refine Finset.card_equiv (SphincsSecurity.splitHashOutputEquiv 128 (by decide)) fun a => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rfl
    _ = ((Finset.univ.erase d) ×ˢ (Finset.univ.erase d)).card := by
      apply congrArg Finset.card
      ext p
      simp [ne_comm]
    _ = (2 ^ 128 - 1) ^ 2 := by
      rw [Finset.card_product]
      simp only [Finset.card_erase_of_mem (Finset.mem_univ d), Finset.card_univ,
        Fintype.card_bitVec, SphincsSecurity.digestBits, pow_two]

/-- A selector constrained to return one of the two halves cannot hit unless a half hits. -/
theorem probability_selected_ne_ge (select : HashOutput → Digest)
    (hs : ∀ a, select a = a.extractLsb' 0 128 ∨ select a = a.extractLsb' 128 128)
    (d : Digest) :
    (1 - 1 / (2 : ENNReal) ^ 128) ^ 2 ≤
      Pr[fun a => select a ≠ d | ($ᵗ HashOutput : ProbComp HashOutput)] := by
  calc
    _ = Pr[fun a : HashOutput => a.extractLsb' 0 128 ≠ d ∧
          a.extractLsb' 128 128 ≠ d | ($ᵗ HashOutput : ProbComp HashOutput)] := by
      rw [probEvent_uniformSample, card_both_halves_ne, Fintype.card_bitVec]
      simp only [Nat.cast_pow, ENNReal.natCast_sub,
        Nat.cast_ofNat, Nat.cast_one, SphincsSecurity.hashOutputBits]
      have hd : (((2 : ENNReal)^128 - 1) / 2^128)^2 =
          ((2 : ENNReal)^128 - 1)^2 / (2^128)^2 := by
        simp only [div_eq_mul_inv, mul_pow, ENNReal.inv_pow]
      rw [show (2 : ENNReal)^256 = ((2 : ENNReal)^128)^2 by norm_num, ← hd]
      congr 1
      rw [ENNReal.sub_div (by intros; norm_num), ENNReal.div_self (by norm_num) (by finiteness)]
    _ ≤ _ := probEvent_mono'' fun a ha => by
      rcases hs a with h | h
      · simpa only [h] using ha.1
      · simpa only [h] using ha.2

theorem probability_pickLow_ne_ge (pickLow : HashOutput → Bool) (d : Digest) :
    (1 - 1 / (2 : ENNReal) ^ 128) ^ 2 ≤
      Pr[fun a => (if pickLow a then a.extractLsb' 0 128 else a.extractLsb' 128 128) ≠ d |
        ($ᵗ HashOutput : ProbComp HashOutput)] := by
  apply probability_selected_ne_ge
  intro a
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

end Hazard
end SigGolfCandidate.T3.Security.LargeResidual
end
section
namespace SigGolfCandidate.T3.Security.LargeResidual
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
inductive Charge where
  | none
  | call
  | mass
  deriving DecidableEq
inductive Request (Coord Cell : Type) where
  | read (row : Cell) (charge : Charge)
  | probe (row : Cell) (test : Probe Coord)
  | disclose (coord : Coord) (charge : Charge)
  | tick (charge : Charge)
abbrev ResidualSpec (Coord Cell : Type) : OracleSpec (Request Coord Cell)
  | .read _ _ => HashOutput
  | .probe _ _ => HashOutput
  | .disclose _ _ => Digest
  | .tick _ => Unit
abbrev World {AuxIndex : Type} (auxSpec : OracleSpec AuxIndex) (Coord Cell : Type) :=
  auxSpec + ResidualSpec Coord Cell
structure Counters where
  calls : Nat
  probes : Nat
  mass : Nat
def Counters.charge (q : Nat) (counters : Counters) : Charge → Counters
  | .none => counters
  | .call => ⟨counters.calls + 1, counters.probes, counters.mass⟩
  | .mass => ⟨counters.calls + 1, counters.probes, counters.mass + (if counters.calls + 1 ≤ q then 1 else 0)⟩
def Counters.probe (counters : Counters) : Counters :=
  ⟨counters.calls + 1, counters.probes + 1, counters.mass⟩
structure State (Coord Cell : Type) where
  candidates : Coord → Finset Digest
  rows : ResidualTableCompletion.Cache Cell
  counters : Counters
section World
variable {Coord Cell AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coord] [DecidableEq Coord] [Fintype Cell] [DecidableEq Cell]
def readState (q : Nat) (state : State Coord Cell) (row : Cell) (answer : HashOutput) (charge : Charge) :
    State Coord Cell :=
  ⟨state.candidates, Function.update state.rows row (some answer), state.counters.charge q charge⟩
def probeState (state : State Coord Cell) (row : Cell) (test : Probe Coord) (answer : HashOutput) :
    State Coord Cell :=
  ⟨test.restrict state.candidates answer, Function.update state.rows row (some answer), state.counters.probe⟩
def stoppedState (state : State Coord Cell) : State Coord Cell :=
  ⟨state.candidates, state.rows, state.counters.probe⟩
def disclosedState (q : Nat) (state : State Coord Cell) (coord : Coord) (value : Digest) (charge : Charge) :
    State Coord Cell :=
  ⟨discloseTableValue state.candidates coord value, state.rows, state.counters.charge q charge⟩
def tickState (q : Nat) (state : State Coord Cell) (charge : Charge) : State Coord Cell :=
  ⟨state.candidates, state.rows, state.counters.charge q charge⟩
noncomputable def observedImpl (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat)
    (labels : Coord → Digest) (table : Cell → HashOutput) :
    QueryImpl (World auxSpec Coord Cell) (OptionT (StateT (State Coord Cell) SPMF))
  | .inl input => OptionT.mk <| StateT.mk fun state =>
      (liftM (aux input) : SPMF _) >>= fun answer => pure (some answer, state)
  | .inr (.read row charge) => OptionT.mk <| StateT.mk fun state =>
      pure (some (table row), readState q state row (table row) charge)
  | .inr (.probe row test) => OptionT.mk <| StateT.mk fun state =>
      match state.rows row with
      | some answer => pure (some answer, readState q state row answer .call)
      | none => if (test.effective state.candidates).keep labels (table row) then
          pure (some (table row), probeState state row (test.effective state.candidates) (table row))
        else pure (none, stoppedState state)
  | .inr (.disclose coord charge) => OptionT.mk <| StateT.mk fun state =>
      pure (some (labels coord), disclosedState q state coord (labels coord) charge)
  | .inr (.tick charge) => OptionT.mk <| StateT.mk fun state =>
      pure (some (), tickState q state charge)
noncomputable def lazyImpl (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat) :
    QueryImpl (World auxSpec Coord Cell) (OptionT (StateT (State Coord Cell) SPMF))
  | .inl input => OptionT.mk <| StateT.mk fun state =>
      (liftM (aux input) : SPMF _) >>= fun answer => pure (some answer, state)
  | .inr (.read row charge) => OptionT.mk <| StateT.mk fun state =>
      reply state.rows row >>= fun answer => pure (some answer, readState q state row answer charge)
  | .inr (.probe row test) => OptionT.mk <| StateT.mk fun state =>
      match state.rows row with
      | some answer => pure (some answer, readState q state row answer .call)
      | none => observe (lazyResponse state.candidates (test.effective state.candidates))
          (pure (none, stoppedState state))
          (fun answer => pure (some answer, probeState state row (test.effective state.candidates) answer))
  | .inr (.disclose coord charge) => OptionT.mk <| StateT.mk fun state =>
      cell (state.candidates coord) >>= fun value => pure (some value, disclosedState q state coord value charge)
  | .inr (.tick charge) => OptionT.mk <| StateT.mk fun state =>
      pure (some (), tickState q state charge)
noncomputable def runWith {Result : Type}
    (implementation : QueryImpl (World auxSpec Coord Cell) (OptionT (StateT (State Coord Cell) SPMF)))
    (computation : OracleComp (World auxSpec Coord Cell) Result) (state : State Coord Cell) :
    SPMF (Option Result × State Coord Cell) :=
  (OptionT.run (simulateQ implementation computation)).run state
omit [Fintype Coord] [DecidableEq Coord] [Fintype Cell] [DecidableEq Cell] in
theorem runWith_pure {Result : Type}
    (implementation : QueryImpl (World auxSpec Coord Cell) (OptionT (StateT (State Coord Cell) SPMF)))
    (value : Result) (state : State Coord Cell) : runWith implementation (pure value) state = pure (some value, state) := by
  simp only [runWith, simulateQ_pure, OptionT.run_pure, StateT.run_pure]
omit [Fintype Coord] [DecidableEq Coord] [Fintype Cell] [DecidableEq Cell] in
theorem runWith_query_bind {Result : Type}
    (implementation : QueryImpl (World auxSpec Coord Cell) (OptionT (StateT (State Coord Cell) SPMF)))
    (input : (World auxSpec Coord Cell).Domain)
    (next : (World auxSpec Coord Cell).Range input → OracleComp (World auxSpec Coord Cell) Result)
    (state : State Coord Cell) :
    runWith implementation (liftM ((World auxSpec Coord Cell).query input) >>= next) state =
      ((implementation input).run.run state >>= fun result =>
        result.1.elim (pure (none, result.2)) (fun answer => runWith implementation (next answer) result.2)) := by
  simp only [runWith, simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind]
  apply congrArg (fun continuation => (implementation input).run.run state >>= continuation)
  funext result
  rcases result with ⟨answer, state⟩
  cases answer <;> rfl
noncomputable def observedRun {Result : Type} (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat)
    (labels : Coord → Digest) (table : Cell → HashOutput)
    (computation : OracleComp (World auxSpec Coord Cell) Result) (state : State Coord Cell) :=
  runWith (observedImpl aux q labels table) computation state
noncomputable def lazyRun {Result : Type} (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat)
    (computation : OracleComp (World auxSpec Coord Cell) Result) (state : State Coord Cell) :=
  runWith (lazyImpl aux q) computation state
def retain {Result : Type} (labels : Coord → Digest) (table : Cell → HashOutput)
    (result : Option Result × State Coord Cell) :
    Option ((Coord → Digest) × (Cell → HashOutput) × Result) × State Coord Cell :=
  (result.1.map (fun value => (labels, table, value)), result.2)
end World
end SigGolfCandidate.T3.Security.LargeResidual
end
section
namespace SigGolfCandidate.T3.Security.LargeResidual
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
open LargePotential (Step Charges StepBound FreeStep MassStep ProbeStep hazard)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
section Bound
variable {Coord Cell AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coord] [DecidableEq Coord] [Fintype Cell] [DecidableEq Cell]
def charges : Charges (State Coord Cell) :=
  ⟨fun state => state.counters.calls, fun state => state.counters.probes, fun state => state.counters.mass⟩
def Inv (state : State Coord Cell) : Prop :=
  ∀ c, (state.candidates c).card = 1 ∨ 2 ^ 128 - state.counters.probes ≤ (state.candidates c).card
def initial : State Coord Cell := ⟨fun _ => Finset.univ, fun _ => none, ⟨0, 0, 0⟩⟩
theorem stop_zero_of_shape {X R : Type} (p : SPMF X) (g : X → R) (f : X → State Coord Cell) :
    Pr[fun result : Option R × State Coord Cell => result.1 = none | p >>= fun a => pure (some (g a), f a)] = 0 := by
  apply probEvent_eq_zero
  intro result hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨a, _, hr⟩ := hresult
  rw [mem_support_pure_iff] at hr
  subst hr
  simp
theorem support_of_shape {X R : Type} (p : SPMF X) (g : X → R) (f : X → State Coord Cell)
    (result : Option R × State Coord Cell) (hresult : result ∈ support (p >>= fun a => pure (some (g a), f a))) :
    ∃ a, result = (some (g a), f a) := by
  rw [mem_support_bind_iff] at hresult
  obtain ⟨a, _, hr⟩ := hresult
  rw [mem_support_pure_iff] at hr
  exact ⟨a, hr⟩
theorem stepBound_of_charge (q : Nat) {X : Type} (step : Step SPMF (World auxSpec Coord Cell) (State Coord Cell))
    (input : (World auxSpec Coord Cell).Domain) (state : State Coord Cell) (charge : Charge)
    (p : SPMF X) (g : X → (World auxSpec Coord Cell).Range input) (f : X → State Coord Cell)
    (hstep : step input state = p >>= fun a => pure (some (g a), f a))
    (hcounters : ∀ a, (f a).counters = state.counters.charge q charge) :
    StepBound step charges (2 ^ 128) q input state := by
  have hstop : Pr[fun result => result.1 = none | step input state] = 0 := by
    rw [hstep]; exact stop_zero_of_shape p g f
  cases charge with
  | none =>
      left
      refine ⟨fun result hresult => ?_, hstop⟩
      rw [hstep] at hresult
      obtain ⟨a, rfl⟩ := support_of_shape p g f result hresult
      simp only [charges, hcounters a, Counters.charge, le_refl, and_self]
  | call =>
      left
      refine ⟨fun result hresult => ?_, hstop⟩
      rw [hstep] at hresult
      obtain ⟨a, rfl⟩ := support_of_shape p g f result hresult
      simp only [charges, hcounters a, Counters.charge]
      omega
  | mass =>
      right; left
      refine ⟨fun result hresult => ?_, hstop⟩
      rw [hstep] at hresult
      obtain ⟨a, rfl⟩ := support_of_shape p g f result hresult
      simp only [charges, hcounters a, Counters.charge]
      omega
theorem observe_stop {S : Type} (response : SPMF HashOutput) (stopped : S) (continued : HashOutput → S) :
    Pr[fun result : Option HashOutput × S => result.1 = none |
        observe response (pure (none, stopped)) (fun answer => pure (some answer, continued answer))] =
      response.toPMF none := by
  rw [observe, probEvent_bind_eq_tsum, tsum_option _ ENNReal.summable]
  simp
theorem observe_support {S : Type} (response : SPMF HashOutput) (stopped : S) (continued : HashOutput → S)
    (result : Option HashOutput × S)
    (hresult : result ∈ support (observe response (pure (none, stopped))
      (fun answer => pure (some answer, continued answer)))) :
    result = (none, stopped) ∨ ∃ answer, response answer ≠ 0 ∧ result = (some answer, continued answer) := by
  rw [observe, mem_support_bind_iff] at hresult
  obtain ⟨o, ho, hr⟩ := hresult
  cases o with
  | none =>
      rw [mem_support_pure_iff] at hr
      exact Or.inl hr
  | some answer =>
      rw [mem_support_pure_iff] at hr
      refine Or.inr ⟨answer, ?_, hr⟩
      rw [SPMF.apply_eq_toPMF_some response answer]
      rw [mem_support_iff] at ho
      simpa using ho
@[simp] theorem Counters.charge_probes (q : Nat) (counters : Counters) (charge : Charge) :
    (counters.charge q charge).probes = counters.probes := by
  cases charge <;> rfl
omit [Fintype Coord] in
theorem card_erase_ge (allowed : Coord → Finset Digest) (c0 : Coord) (v : Digest) (c : Coord) :
    (allowed c).card - 1 ≤ (eraseTableValue allowed c0 v c).card := by
  by_cases h : c = c0
  · subst h
    simpa only [eraseTableValue, Function.update_self] using
      (Finset.pred_card_le_card_erase (s := allowed c) (a := v))
  · simp only [eraseTableValue, Function.update_of_ne h]
    omega
omit [Fintype Coord] in
theorem card_erase_of_ne (allowed : Coord → Finset Digest) (c0 : Coord) (v : Digest) (c : Coord) (h : c ≠ c0) :
    (eraseTableValue allowed c0 v c).card = (allowed c).card := by
  simp only [eraseTableValue, Function.update_of_ne h]
omit [Fintype Coord] in
theorem card_restrict_ge (probe : Probe Coord) (allowed : Coord → Finset Digest) (answer : HashOutput)
    (hadm : ∀ g ∈ probe.guess, ∀ parent, probe.hit = Hit.label parent → g.1 ≠ parent) (c : Coord) :
    (allowed c).card - 1 ≤ (probe.restrict allowed answer c).card := by
  unfold Probe.restrict
  cases hhit : probe.hit with
  | target t =>
      simp only [Hit.restrict, Hit.answerValue]
      unfold Probe.guessRestrict
      cases hg : probe.guess with
      | none => simp
      | some g => exact card_erase_ge _ _ _ _
  | selectedTarget t pickLow =>
      simp only [Hit.restrict, Hit.answerValue]
      unfold Probe.guessRestrict
      cases hg : probe.guess with
      | none => simp
      | some g => exact card_erase_ge _ _ _ _
  | label parent =>
      simp only [Hit.restrict, Hit.answerValue]
      unfold Probe.guessRestrict
      cases hg : probe.guess with
      | none => exact card_erase_ge _ _ _ _
      | some g =>
          have hne : g.1 ≠ parent := hadm g (by rw [hg]; rfl) parent hhit
          by_cases hc : c = parent
          · subst hc
            have h1 := card_erase_ge (eraseTableValue allowed g.1 g.2) c (low answer) c
            rw [card_erase_of_ne allowed g.1 g.2 c (Ne.symm hne)] at h1
            exact h1
          · rw [card_erase_of_ne _ parent (low answer) c hc]
            exact card_erase_ge _ _ _ _
omit [Fintype Coord] in
theorem restrict_subset_card (probe : Probe Coord) (allowed : Coord → Finset Digest) (answer : HashOutput) (c : Coord) :
    (probe.restrict allowed answer c).card ≤ (allowed c).card :=
  Finset.card_le_card (restrict_subset probe allowed answer c)
end Bound
end SigGolfCandidate.T3.Security.LargeResidual
end
section
namespace SigGolfCandidate.T3.Security.LargeResidual
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open CanonGraph CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_largeResidualT3 : DecidableEq T3.Cache := Classical.decEq _
abbrev Coord := CanonGraph.Node ⊕ CanonGraph.SecretIndex
def chainChild (p : ChainGraph.Point) : Coord :=
  if p.2.val = 0 then .inr (.inl p.1) else .inl (.chain (ChainGraph.predecessor p))
def treeChild (lay : Layer) (tree : Fin (2^31)) (level c : Nat) : Option Coord :=
  if level = 0 then (if h : c < 4096 then some (.inl (.leaf ⟨lay, tree, ⟨c, h⟩⟩)) else none)
  else (treeNodeAt lay tree (level - 1) c).map fun n => .inl (.node n)
def ftsChild (index : Fin (2^31)) (coord : Fin 7) (level c : Nat) : Option Coord :=
  if level = 0 then (if h : c < 2048 then some (.inl (.ftsLeaf ⟨index, coord, ⟨c, h⟩⟩)) else none)
  else (ftsNodeAt index coord (level - 1) c).map fun n => .inl (.ftsNode n)
def endPoint (L : LeafPos) (i : Nat) : ChainGraph.Point :=
  (⟨L.lay, L.tree, L.leaf, fin58 i⟩, ⟨(maxDigit L.lay i - 1) % 7, Nat.mod_lt _ (by decide)⟩)
def listBlock (i : Nat) : Nat := if i = 0 then 0 else i + 1
def childSlots : CanonGraph.Node → List (Coord × Nat)
  | .chain p => [(chainChild p, 3)]
  | .leaf L => (List.range (chainCount L.lay)).map fun i => (.inl (.chain (endPoint L i)), listBlock i)
  | .node n => ((treeChild n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val)).map (·, 0)).toList ++
      ((treeChild n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val + 1)).map (·, 3)).toList
  | .ftsLeaf f => [(.inr (.inr f), 2)]
  | .ftsNode n => ((ftsChild n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val)).map (·, 0)).toList ++
      ((ftsChild n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val + 1)).map (·, 3)).toList
  | .forest index => (List.range 7).map fun c => (.inl (.ftsNode (ftsRootNode index (fin7 c))), listBlock c)
def slotValue (input : HashInput) (block : Nat) : Digest := readDigest ((input.drop (16 * block)).take 16)
noncomputable def honestValue (A : Answers) : Coord → Digest
  | .inl N => (A (.inl (.inr (Extract.honestInput A N.toPos)))).extractLsb' 0 128
  | .inr s => secretsOf A s
inductive Known (D : Coord → Prop) : Coord → Prop
  | base {c : Coord} : D c → Known D c
  | node {N : CanonGraph.Node} : (∀ cs ∈ childSlots N, Known D cs.1) → Known D (.inl N)
noncomputable def firstUnknown (K : Coord → Prop) (N : CanonGraph.Node) : Option (Coord × Nat) :=
  (childSlots N).find? fun cs => decide (¬K cs.1)
def keygenDisclosed : List Coord :=
  (List.range' 0 13).flatMap fun level =>
    (List.range (2 ^ (12 - level))).filterMap fun node => treeChild 0 0 level node
def chainItem (L : LeafPos) (i d : Nat) : Coord :=
  if d = 0 then .inr (.inl ⟨L.lay, L.tree, L.leaf, fin58 i⟩)
  else .inl (.chain (⟨L.lay, L.tree, L.leaf, fin58 i⟩, ⟨(d - 1) % 7, Nat.mod_lt _ (by decide)⟩))
def ftsOpened (index : Fin (2^31)) (coord : Nat) (sel : Selection) : List Coord :=
  (sel.leaves.map (fun s => sel.bucket * 128 + s)).filterMap fun leaf =>
    if h : leaf < 2048 then some (.inr (.inr ⟨index, fin7 coord, ⟨leaf, h⟩⟩)) else none
def ftsProof (index : Fin (2^31)) (coord : Nat) (sel : Selection) : List Coord :=
  ((frontier (sel.leaves.map (fun s => sel.bucket * 128 + s)) 7 sel.bucket).filterMap fun p =>
      ftsChild index (fin7 coord) p.1 p.2) ++
    ((List.range 4).filterMap fun j => ftsChild index (fin7 coord) (7 + j) (sel.bucket / 2 ^ j ^^^ 1))
def ftsItems (index : Fin (2^31)) (chosen : List Selection) : List Coord :=
  (List.range 7).flatMap fun coord =>
    ftsOpened index coord (chosen.getD coord ⟨0, []⟩) ++ ftsProof index coord (chosen.getD coord ⟨0, []⟩)
def routeAddr (index : Nat) (lay : Layer) : Wots.LeafAddr := ⟨lay, (route index lay).2, (route index lay).1⟩
def layerChains (digitsOf : Wots.LeafAddr → List Nat) (index : Fin (2^31)) (lay : Layer) : List Coord :=
  if h : (route index.val lay).2 < 2 ^ 31 ∧ (route index.val lay).1 < 4096 then
    (List.range (chainCount lay)).map fun i =>
      chainItem ⟨lay, ⟨(route index.val lay).2, h.1⟩, ⟨(route index.val lay).1, h.2⟩⟩ i
        ((digitsOf (routeAddr index.val lay)).getD i 0)
  else []
def layerPath (index : Fin (2^31)) (lay : Layer) : List Coord :=
  if h : (route index.val lay).2 < 2 ^ 31 then
    (List.range (height lay)).filterMap fun j =>
      treeChild lay ⟨(route index.val lay).2, h⟩ j ((route index.val lay).1 / 2 ^ j ^^^ 1)
  else []
def layerItems (digitsOf : Wots.LeafAddr → List Nat) (index : Fin (2^31)) : List Coord :=
  (List.finRange 4).flatMap fun lay => layerChains digitsOf index lay ++ layerPath index lay
def digestIndex (N : HashOutput) : Fin (2^31) := ⟨N.toNat % 2 ^ 31, Nat.mod_lt _ (by positivity)⟩
def signItemsWith (digitsOf : Wots.LeafAddr → List Nat) (N : HashOutput) : List Coord :=
  ftsItems (digestIndex N) (selections N) ++ layerItems digitsOf (digestIndex N)
noncomputable def signItems (A : Answers) (N : HashOutput) : List Coord :=
  signItemsWith (Wots.referenceDigits A) N
def RouteOk (A : Answers) (index : Nat) : Prop :=
  ∀ lay : Layer, lay ≠ 0 → (Wots.referenceSearch A (routeAddr index lay)).isSome
noncomputable def signDigest (A : Answers) (message : Message) : Option (BitVec 32 × HashOutput) :=
  evalWithAnswerFn A (digestSearch (evalWithAnswerFn A (privateNonce message)) message 0 attemptLimit)
noncomputable def signDisclosed (A : Answers) (published : T3.Cache) (request : SigGolfCandidate.T3.Security.Request) :
    List Coord :=
  if request.cache = published then
    match signDigest A request.message with
    | some (_, N) => if RouteOk A (N.toNat % 2 ^ 31) then signItems A N else []
    | none => []
  else []
def msgCoord (L : EncLeaf) : Coord :=
  if h : L.1.lay.val < 3 then .inl (.node (rootNode ⟨L.1.lay.val + 1, by omega⟩ (childIndex L)))
  else .inl (.forest (childIndex L))
def EncodingContact (A : Answers) (K : Coord → Prop) (input : HashInput) (answer : HashOutput) : Prop :=
  ∃ (L : EncLeaf) (m : Digest) (ctr : BitVec 32), input = Wots.encodingRow L.toWots m ctr ∧
    ((¬K (msgCoord L) ∧ m = honestValue A (msgCoord L)) ∨
      (Wots.referenceInput A L.toWots ≠ some input ∧
        decode L.1.lay (answer.extractLsb' 0 128) = some (Wots.referenceDigits A L.toWots)))
def IsDigestRow (input : HashInput) : Prop :=
  ∃ (rho : Digest) (message : Message) (counter : BitVec 32), input = pad64 (digestInput rho message counter)
end SigGolfCandidate.T3.Security.LargeResidual
end
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_LargeResidualT3 ====
section

namespace ClaudeWCT.W9.T3.Security.LargeResidual
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.LargeResidual (listBlock slotValue routeAddr IsDigestRow)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeResidualT3 : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _
def digestIndex (N : HashOutput) : Fin (2^31) := ⟨WCT9.digestIndex N, WCT9.digestIndex_lt N⟩
/-- Observable secret-side coordinates: WOTS seeds and FTS seeds (the latter are family evaluations, see
`FamResidual`; the hidden FTS coefficients are not observables). -/
abbrev SeedIndex := ChainGraph.Address ⊕ WctAddr
/-- The observable seeds of a secret table: WOTS seeds (top: secrets; lower: leaf-family values) and FTS seeds. -/
def seedView (secrets : CanonGraph.Secrets) : SeedIndex → Digest :=
  Sum.elim (seedsOf secrets) (wctSeedsOf secrets)
abbrev Coord := CanonGraph.Node ⊕ SeedIndex
def chainChild (p : ChainGraph.Point) : Coord :=
  if p.2.val = 0 then .inr (.inl p.1) else .inl (.chain (ChainGraph.predecessor p))
def treeChild (lay : Layer) (tree : Fin (2^31)) (level c : Nat) : Option Coord :=
  if level = 0 then (leafAt lay tree c).map fun L => .inl (.leaf L)
  else (treeNodeAt lay tree (level - 1) c).map fun n => .inl (.node n)
def wctItem (a : WctAddr) (p : Nat) : Coord :=
  if p = 0 then .inr (.inr a) else .inl (.wctChain (a, ⟨(p - 1) % 4, Nat.mod_lt _ (by decide)⟩))
def ftsChild (index : Fin (2^31)) (coord : Fin 9) (level c : Nat) : Option Coord :=
  if level = 0 then (if h : c < 128 then some (.inl (.wctLeaf ⟨index, coord, ⟨c, h⟩⟩)) else none)
  else (ftsNodeAt index coord (level - 1) c).map fun n => .inl (.wctNode n)
def endPoint (L : LeafPos) (i : Nat) : ChainGraph.Point :=
  (⟨L.lay, L.tree, L.leaf, fin58 i⟩, ⟨(maxDigit L.lay i - 1) % 7, Nat.mod_lt _ (by decide)⟩)
/-- Block of chain end `i` in a WOTS leaf input. Campaign T51 ("endpad"): the top leaf `end_0 | tweak | end_1 ..` has
the lower shape (#938: `pad | tweak | end_0 ..`, block `i + 2`). -/
def leafBlock (lay : Layer) (i : Nat) : Nat := if lay = 0 then listBlock i else listBlock i
/-- Block of FTS end `t` in the padded FTS leaf `end0 | hdr | pad | end1..end5` (campaign T8). -/
def ftsLeafSlot (t : Nat) : Nat := if t = 0 then 0 else t + 2
/-- Pad source of FTS coordinate `coord` (nested FTS r1-1): top node `b` of coordinate `coord - 1`; none for
coordinate 0, whose pads are the constant `ftsStart`. -/
def prevTop (index : Fin (2^31)) (coord : Fin 9) (b : Fin 2) : Option Coord :=
  if h : coord.val = 0 then none else some (.inl (.wctNode (ftsTopNode index ⟨coord.val - 1, by omega⟩ b)))
def childSlots : CanonGraph.Node → List (Coord × Nat)
  | .chain p => [(chainChild p, if WCT9.isG p.1.layer p.1.chain.val then 0 else 3)]
  | .leaf L => (List.range (chainCount L.1.lay)).map fun i => (.inl (.chain (endPoint L.1 i)), leafBlock L.1.lay i)
  | .node n => if trialCap n.1.lay n.1.level.val ≤ n.1.nonce.val then [] else
      ((treeChild n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val)).map (·, 0)).toList ++
      ((treeChild n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val + 1)).map (·, 3)).toList
  | .wctChain p => [(wctItem p.1 p.2.val, if WCT9.ftsIsG p.1.2.2.2.val then 0 else 3)]
  | .wctLeaf L => (List.ofFn fun t : Fin 6 => (wctItem (L.index, L.coord, L.child, t) 4, ftsLeafSlot t.val)) ++
      ((prevTop L.index L.coord 0).map (·, 2)).toList
  | .wctNode n => ((ftsChild n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val)).map (·, 0)).toList ++
      ((ftsChild n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val + 1)).map (·, 3)).toList ++
      (if n.1.level.val = 5 then ((prevTop n.1.index n.1.coord 1).map (·, 2)).toList else [])
  | .forest index => (List.range 9).flatMap fun c =>
      [(.inl (.wctNode (ftsTopNode index (fin9 c) 0)), 2 + 2 * c), (.inl (.wctNode (ftsTopNode index (fin9 c) 1)), 3 + 2 * c)]
/-! ### Top-nonce layer (r3-lean-nonsec, Subagent L)
Trial nodes are ordinary coordinates. The value-level trial selection mirrors `CanonGraph.selNonce` with the label
of a trial replaced by its coordinate value (the used half). -/
/-- Coordinate of trial `j` of the position of `n`. -/
def trialCoord (n : TreeNode) (j : Nat) : Coord := .inl (.node (withNonce n j))
/-- Value-level `trialFails`. -/
def trialFailsV (v : Coord → Digest) (n : TreeNode) (j : Nat) : Prop :=
  topZeroOk (n.1.level.val + 1) (v (trialCoord n j)) = false
instance (v : Coord → Digest) (n : TreeNode) (j : Nat) : Decidable (trialFailsV v n j) := by
  unfold trialFailsV; infer_instance
/-- Value-level `Active`. -/
def ActiveV (v : Coord → Digest) (n : TreeNode) : Prop :=
  n.1.nonce.val < trialCap n.1.lay n.1.level.val ∧ ∀ j < n.1.nonce.val, trialFailsV v n j
instance (v : Coord → Digest) (n : TreeNode) : Decidable (ActiveV v n) := by unfold ActiveV; infer_instance
/-- Value-level `selNonce`. -/
def selNonceV (v : Coord → Digest) (n : TreeNode) : Nat :=
  ((List.range (trialCap n.1.lay n.1.level.val)).find? fun j => !decide (trialFailsV v n j)).getD
    (trialCap n.1.lay n.1.level.val - 1)
/-- The selected trial coordinate of a tree-node coordinate (identity on other coordinates). -/
def selCoordV (v : Coord → Digest) : Coord → Coord
  | .inl (.node n) => .inl (.node (withNonce n (selNonceV v n)))
  | c => c
/-- Tree value from coordinate values: the value of the selected trial of the child position. -/
def treeVal (v : Coord → Digest) (lay : Layer) (tree : Fin (2^31)) (level c : Nat) : Digest :=
  ((treeChild lay tree level c).map fun x => v (selCoordV v x)).getD 0
/-- Coordinate values read through the selected trial (the published/honest value of a tree position). -/
def selVals (v : Coord → Digest) : Coord → Digest := fun c => v (selCoordV v c)
/-- Trials read by the cell of a tree node of this position (none for single-trial positions). -/
def trialDeps (n : TreeNode) : List Coord :=
  if trialCap n.1.lay n.1.level.val = 1 then [] else (List.range (trialCap n.1.lay n.1.level.val)).map (trialCoord n)
def childTrialDeps (lay : Layer) (tree : Fin (2^31)) (level c : Nat) : List Coord :=
  match treeChild lay tree level c with
  | some (.inl (.node m)) => trialDeps m
  | _ => []
/-- Every coordinate the cell of a node reads: its slots, and for tree nodes the trials of the own position and of
the child positions. -/
def cellDeps : CanonGraph.Node → List Coord
  | .node n => (childSlots (.node n)).map Prod.fst ++ trialDeps n ++
      childTrialDeps n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val) ++
      childTrialDeps n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val + 1)
  | N => (childSlots N).map Prod.fst
theorem selNonceV_lt (v : Coord → Digest) (n : TreeNode) : selNonceV v n < trialCap n.1.lay n.1.level.val := by
  have hc := trialCap_pos n.1.lay n.1.level.val
  unfold selNonceV
  cases hf : (List.range (trialCap n.1.lay n.1.level.val)).find? fun j => !decide (trialFailsV v n j) with
  | none => simp only [Option.getD_none]; omega
  | some j =>
      simp only [Option.getD_some]
      exact List.mem_range.mp (List.mem_of_find?_eq_some hf)
theorem selNonceV_congr {v w : Coord → Digest} {n : TreeNode}
    (h : ∀ j < trialCap n.1.lay n.1.level.val, v (trialCoord n j) = w (trialCoord n j)) :
    selNonceV v n = selNonceV w n := by
  unfold selNonceV
  congr 1
  apply find?_congr'
  intro j hj
  rw [List.mem_range] at hj
  have hiff : trialFailsV v n j ↔ trialFailsV w n j := by unfold trialFailsV; rw [h j hj]
  simp only [decide_eq_decide.mpr hiff]
theorem selNonceV_cap_one {v : Coord → Digest} {n : TreeNode} (h : trialCap n.1.lay n.1.level.val = 1) :
    selNonceV v n = 0 := by
  have := selNonceV_lt v n; omega
theorem activeV_congr {v w : Coord → Digest} {n : TreeNode}
    (h : trialCap n.1.lay n.1.level.val ≠ 1 → ∀ j < trialCap n.1.lay n.1.level.val, v (trialCoord n j) = w (trialCoord n j)) :
    ActiveV v n ↔ ActiveV w n := by
  unfold ActiveV trialFailsV
  by_cases h1 : trialCap n.1.lay n.1.level.val = 1
  · rw [h1]
    constructor <;> rintro ⟨hn, -⟩ <;> exact ⟨hn, fun j hj => by omega⟩
  · constructor <;> rintro ⟨hn, hj⟩ <;> refine ⟨hn, fun j hjn => ?_⟩
    · rw [← h h1 j (by omega)]; exact hj j hjn
    · rw [h h1 j (by omega)]; exact hj j hjn
theorem mem_trialDeps {n : TreeNode} (h : trialCap n.1.lay n.1.level.val ≠ 1) {j : Nat}
    (hj : j < trialCap n.1.lay n.1.level.val) : trialCoord n j ∈ trialDeps n := by
  unfold trialDeps
  rw [if_neg h]
  exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
/-- Selection of a coordinate only reads the trials of its position. -/
theorem selCoordV_congr {v w : Coord → Digest} (c : Coord)
    (h : ∀ n : TreeNode, c = .inl (.node n) → trialCap n.1.lay n.1.level.val ≠ 1 →
      ∀ j < trialCap n.1.lay n.1.level.val, v (trialCoord n j) = w (trialCoord n j)) :
    selCoordV v c = selCoordV w c := by
  rcases c with (_ | _ | n | _ | _ | _ | _) | s
  all_goals try rfl
  simp only [selCoordV]
  by_cases h1 : trialCap n.1.lay n.1.level.val = 1
  · rw [selNonceV_cap_one h1, selNonceV_cap_one h1]
  · rw [selNonceV_congr (h n rfl h1)]
theorem treeVal_congr {v w : Coord → Digest} (lay : Layer) (tree : Fin (2^31)) (level c : Nat)
    (h : ∀ x ∈ (treeChild lay tree level c).toList, v (selCoordV v x) = w (selCoordV v x))
    (hd : ∀ x ∈ childTrialDeps lay tree level c, v x = w x) :
    treeVal v lay tree level c = treeVal w lay tree level c := by
  unfold treeVal
  cases ht : treeChild lay tree level c with
  | none => rfl
  | some x =>
      simp only [Option.map_some, Option.getD_some]
      rw [ht] at h
      have hx := h x (by simp)
      rw [hx]
      congr 1
      apply selCoordV_congr
      intro n hn h1 j hj
      apply hd
      unfold childTrialDeps
      rw [ht, hn]
      exact mem_trialDeps h1 hj

noncomputable def honestValue (A : Answers) : Coord → Digest
  | .inl N => N.toPos.proj (A (.inl (.inr (Extract.honestInput A N.toPos))))
  | .inr s => seedView (secretsOf A) s
inductive Known (D : Coord → Prop) : Coord → Prop
  | base {c : Coord} : D c → Known D c
  | node {N : CanonGraph.Node} : (∀ cs ∈ childSlots N, Known D cs.1) → Known D (.inl N)
noncomputable def firstUnknown (K : Coord → Prop) (N : CanonGraph.Node) : Option (Coord × Nat) :=
  (childSlots N).find? fun cs => decide (¬K cs.1)
def keygenCacheDisclosed : List Coord :=
  (List.range' 0 13).flatMap fun level =>
    (List.range (2 ^ (12 - level))).filterMap fun node => treeChild 0 0 level node
def chainItem (L : LeafPos) (i d : Nat) : Coord :=
  if d = 0 then .inr (.inl ⟨L.lay, L.tree, L.leaf, fin58 i⟩)
  else .inl (.chain (⟨L.lay, L.tree, L.leaf, fin58 i⟩, ⟨(d - 1) % 7, Nat.mod_lt _ (by decide)⟩))
def wctOpened (index : Fin (2^31)) (k : Fin 9) (N : HashOutput) : List Coord :=
  List.ofFn fun t : Fin 6 => wctItem (index, k, WCT9.child N k, t) (4 - WCT9.wordDigit (WCT9.rank N k) t)
def wctPath (index : Fin (2^31)) (k : Fin 9) (N : HashOutput) : List Coord :=
  (List.range 7).filterMap fun l => ftsChild index k l ((WCT9.child N k).val / 2 ^ l ^^^ 1)
def ftsItems (index : Fin (2^31)) (N : HashOutput) : List Coord :=
  (List.finRange 9).flatMap fun k => wctOpened index k N ++ wctPath index k N
def layerChains (digitsOf : Wots.LeafAddr → List Nat) (index : Fin (2^31)) (lay : Layer) : List Coord :=
  if h : (route index.val lay).2 < 2 ^ 31 ∧ (route index.val lay).1 < 4096 then
    (List.range (chainCount lay)).map fun i =>
      chainItem ⟨lay, ⟨(route index.val lay).2, h.1⟩, ⟨(route index.val lay).1, h.2⟩⟩ i
        ((digitsOf (routeAddr index.val lay)).getD i 0)
  else []
def layerPath (index : Fin (2^31)) (lay : Layer) : List Coord :=
  if h : (route index.val lay).2 < 2 ^ 31 then
    (List.range (height lay)).filterMap fun j =>
      treeChild lay ⟨(route index.val lay).2, h⟩ j ((route index.val lay).1 / 2 ^ j ^^^ 1)
  else []
def layerItems (digitsOf : Wots.LeafAddr → List Nat) (index : Fin (2^31)) : List Coord :=
  (List.finRange 4).flatMap fun lay => layerChains digitsOf index lay ++ layerPath index lay
def signItemsWith (digitsOf : Wots.LeafAddr → List Nat) (N : HashOutput) : List Coord :=
  ftsItems (digestIndex N) N ++ layerItems digitsOf (digestIndex N)
noncomputable def signItems (A : Answers) (N : HashOutput) : List Coord :=
  signItemsWith (Wots.referenceDigits A) N
def RouteOk (A : Answers) (index : Nat) : Prop :=
  ∀ lay : Layer, lay ≠ 0 → (Wots.referenceSearch A (routeAddr index lay)).isSome
noncomputable def signDigest (A : Answers) (message : Message) : Option (BitVec 32 × HashOutput) :=
  evalWithAnswerFn A (WCT9.digestSearch (evalWithAnswerFn A (privateNonce message)) message 0
    WCT9.digestAttemptLimit)
noncomputable def signDisclosed (A : Answers) (published : SigGolfCandidate.T3.Cache) (request : SigGolfCandidate.T3.Security.Request) :
    List Coord :=
  if request.cache = published then
    match signDigest A request.message with
    | some (_, N) => if RouteOk A (WCT9.digestIndex N) then signItems A N else []
    | none => []
  else []
def msgSlots (L : EncLeaf) : List (Coord × Nat) :=
  if h : L.1.lay.val < 3 then
    [(.inl (.node (topNode ⟨L.1.lay.val + 1, by omega⟩ (childIndex L) (childIndex_treeBits L h) 0)), 0),
      (.inl (.node (topNode ⟨L.1.lay.val + 1, by omega⟩ (childIndex L) (childIndex_treeBits L h) 1)), 3)]
  else [(.inl (.wctNode (ftsTopNode (childIndex L) 8 0)), 0), (.inl (.wctNode (ftsTopNode (childIndex L) 8 1)), 3)]
/-- The large-game simulator may reveal internal message roots for free. These
coordinates contain neither WOTS chain values nor FTS chain values or seeds. -/
noncomputable def encodingDisclosed : List Coord :=
  (Finset.univ : Finset EncLeaf).toList.flatMap fun L => (msgSlots L).map Prod.fst

/-- Top-nonce layer: every keygen nonce trial of a top position is a disclosed keygen coordinate (its input is
public: children are cache values, the nonce is the trial index; no secret value). -/
noncomputable def topTrialsDisclosed : List Coord :=
  ((Finset.univ : Finset TreeNode).filter fun n =>
    n.1.lay = 0 ∧ trialCap n.1.lay n.1.level.val ≠ 1 ∧ n.1.nonce.val < trialCap n.1.lay n.1.level.val).toList.map
    fun n => .inl (.node n)

noncomputable def keygenDisclosed : List Coord :=
  keygenCacheDisclosed ++ encodingDisclosed ++ topTrialsDisclosed

attribute [local irreducible] Finset.univ

theorem msgSlot_mem_keygen {L : EncLeaf} {cs : Coord × Nat} (hc : cs ∈ msgSlots L) :
    cs.1 ∈ keygenDisclosed := by
  apply List.mem_append_left topTrialsDisclosed
  apply List.mem_append_right keygenCacheDisclosed
  exact List.mem_flatMap.mpr ⟨L, Finset.mem_toList.mpr (Finset.mem_univ _),
    List.mem_map.mpr ⟨cs, hc, rfl⟩⟩

theorem encodingDisclosed_shape {c : Coord} (hc : c ∈ encodingDisclosed) :
    (∃ n, c = .inl (.node n)) ∨ ∃ n, c = .inl (.wctNode n) := by
  unfold encodingDisclosed at hc
  obtain ⟨L, _, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨cs, hcs, rfl⟩ := List.mem_map.mp hc
  unfold msgSlots at hcs
  split_ifs at hcs
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hcs
    rcases hcs with rfl | rfl <;> exact Or.inl ⟨_, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hcs
    rcases hcs with rfl | rfl <;> exact Or.inr ⟨_, rfl⟩

theorem mem_topTrialsDisclosed {c : Coord} :
    c ∈ topTrialsDisclosed ↔ ∃ n : TreeNode, c = .inl (.node n) ∧
      n.1.lay = 0 ∧ trialCap n.1.lay n.1.level.val ≠ 1 ∧ n.1.nonce.val < trialCap n.1.lay n.1.level.val := by
  unfold topTrialsDisclosed
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨n, hn, rfl⟩; exact ⟨n, rfl, hn⟩
  · rintro ⟨n, rfl, hn⟩; exact ⟨n, hn, rfl⟩
theorem topTrialsDisclosed_shape {c : Coord} (hc : c ∈ topTrialsDisclosed) : ∃ n, c = .inl (.node n) := by
  obtain ⟨n, rfl, -⟩ := mem_topTrialsDisclosed.mp hc
  exact ⟨n, rfl⟩
theorem trialCoord_mem_topTrials {n : TreeNode} (hl : n.1.lay = 0) (hc : trialCap n.1.lay n.1.level.val ≠ 1) {j : Nat}
    (hj : j < trialCap n.1.lay n.1.level.val) : trialCoord n j ∈ topTrialsDisclosed := by
  refine mem_topTrialsDisclosed.mpr ⟨withNonce n j, rfl, hl, hc, ?_⟩
  have := trialCap_le n.1.lay n.1.level.val
  rw [withNonce_nonce n (by omega)]
  exact hj
theorem trialCoord_mem_keygen {n : TreeNode} (hl : n.1.lay = 0) (hc : trialCap n.1.lay n.1.level.val ≠ 1) {j : Nat}
    (hj : j < trialCap n.1.lay n.1.level.val) : trialCoord n j ∈ keygenDisclosed := by
  apply List.mem_append_right
  refine mem_topTrialsDisclosed.mpr ⟨withNonce n j, rfl, hl, hc, ?_⟩
  have := trialCap_le n.1.lay n.1.level.val
  rw [withNonce_nonce n (by omega)]
  exact hj
/-- Membership in the keygen disclosure by its three parts. -/
theorem mem_keygenDisclosed {c : Coord} :
    c ∈ keygenDisclosed ↔ c ∈ keygenCacheDisclosed ∨ c ∈ encodingDisclosed ∨ c ∈ topTrialsDisclosed := by
  unfold keygenDisclosed
  simp only [List.mem_append, or_assoc]

def msgVals (vals : Coord → Digest) (L : EncLeaf) : WCT9.LayerMsg :=
  if h : L.1.lay.val < 3 then
    .pair (vals (.inl (.node (topNode ⟨L.1.lay.val + 1, by omega⟩ (childIndex L) (childIndex_treeBits L h) 0))))
      (vals (.inl (.node (topNode ⟨L.1.lay.val + 1, by omega⟩ (childIndex L) (childIndex_treeBits L h) 1))))
  else .pair (vals (.inl (.wctNode (ftsTopNode (childIndex L) 8 0))))
    (vals (.inl (.wctNode (ftsTopNode (childIndex L) 8 1))))
noncomputable def firstUnknownMsg (K : Coord → Prop) (L : EncLeaf) : Option (Coord × Nat) :=
  (msgSlots L).find? fun cs => decide (¬K cs.1)
def StructuralContact (A : Answers) (K : Coord → Prop) (input : HashInput) (answer : HashOutput) : Prop :=
  ∃ N : CanonGraph.Node, Extract.posOf input = some N.toPos ∧
    ((∃ cs, firstUnknown K N = some cs ∧ slotValue input cs.2 = honestValue A cs.1) ∨
      (input ≠ Extract.honestInput A N.toPos ∧ N.toPos.proj answer = honestValue A (.inl N)))
def EncodingContact (A : Answers) (K : Coord → Prop) (input : HashInput) (answer : HashOutput) : Prop :=
  ∃ (L : EncLeaf) (m : WCT9.LayerMsg) (ctr : BitVec 32) (pad : Wots.RowPad), Extract.msgFits L.1.lay m ∧
    input = Wots.encRow L.toWots m ctr pad ∧
    ((∃ cs, firstUnknownMsg K L = some cs ∧ slotValue input cs.2 = honestValue A cs.1) ∨
      (Wots.referenceInput A L.toWots ≠ some input ∧
        decode L.1.lay (WCT9.encodingAnswer L.1.lay answer) = some (Wots.referenceDigits A L.toWots)))
def ContactTest (A : Answers) (K : Coord → Prop) (input : HashInput) (answer : HashOutput) : Prop :=
  StructuralContact A K input answer ∨ EncodingContact A K input answer
end ClaudeWCT.W9.T3.Security.LargeResidual

namespace ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
open SigGolfCandidate.T3.Security.LargeResidual (slotValue)
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- Physical tree leaves retain their raw seed-family coordinates. -/
def ftsChild (index : Fin (2^31)) (coord : Fin 9) (level physical : Nat) : Option Coord :=
 if level=0 then
   if h:CanonGraph.Paired.rawLeaf coord.val physical<128 then
     some (.inl (.wctLeaf ⟨index,coord,⟨CanonGraph.Paired.rawLeaf coord.val physical,h⟩⟩))
   else none
 else (ftsNodeAt index coord (level-1) physical).map fun n => .inl (.wctNode n)

/-- The exact branch-dependent L/R pad source. -/
def padCoord (index : Fin (2^31)) (coord : Fin 9) (branch : Nat) (side : Fin 2) : Option Coord :=
 if h:coord.val=0 then none else
   let previous : Fin 9 := ⟨coord.val-1,by have:=coord.isLt;omega⟩
   if coord.val%2=1 then ftsChild index previous 5 (2*branch+side.val)
   else ftsChild index previous 6 side.val

def childSlots : CanonGraph.Node → List (Coord×Nat)
 | .wctLeaf L => (List.ofFn fun t:Fin 6 => (wctItem (L.index,L.coord,L.child,t) 4,ftsLeafSlot t.val)) ++
   ((padCoord L.index L.coord (L.child.val%2) 0).map (·,2)).toList
 | .wctNode n => ((ftsChild n.1.index n.1.coord n.1.level.val (2*n.1.idx.val)).map (·,0)).toList ++
   ((ftsChild n.1.index n.1.coord n.1.level.val (2*n.1.idx.val+1)).map (·,3)).toList ++
   (if n.1.level.val=4 then ((padCoord n.1.index n.1.coord (n.1.idx.val/2) 1).map (·,2)).toList else [])
 | n => LargeResidual.childSlots n

noncomputable def honestValue (A : Answers) : Coord → Digest
 | .inl n => Extract.Paired.proj n.toPos (A (.inl (.inr (Extract.Paired.honestInput A n.toPos))))
 | .inr s => seedView (secretsOf A) s

inductive Known (D : Coord → Prop) : Coord → Prop
 | base {c : Coord} : D c → Known D c
 | node {n : CanonGraph.Node} : (∀cs∈childSlots n,Known D cs.1) → Known D (.inl n)

noncomputable def firstUnknown (K : Coord → Prop) (n : CanonGraph.Node) : Option (Coord×Nat) :=
 (childSlots n).find? fun cs => decide (¬K cs.1)

def StructuralContact (A : Answers) (K : Coord → Prop) (input : HashInput) (answer : HashOutput) : Prop :=
 ∃n:CanonGraph.Node, Extract.Paired.Bounded n.toPos ∧ Extract.posOf input=some n.toPos ∧
   ((∃cs,firstUnknown K n=some cs ∧ slotValue input cs.2=honestValue A cs.1) ∨
    (input≠Extract.Paired.honestInput A n.toPos ∧ Extract.Paired.proj n.toPos answer=honestValue A (.inl n)))

def EncodingContact (A : Answers) (input : HashInput) (answer : HashOutput) : Prop :=
 ∃(L:EncLeaf)(m:WCT9.LayerMsg)(ctr:BitVec 32)(pad:Wots.RowPad),Extract.msgFits L.1.lay m ∧
  input=Wots.encRow L.toWots m ctr pad ∧
  Wots.CanonicalRef.referenceSearch A (Wots.CanonicalRef.sourceMessages A) L.toWots≠none ∧
  Wots.CanonicalRef.referenceInput A (Wots.CanonicalRef.sourceMessages A) L.toWots≠some input ∧
  Wots.CanonicalRef.NotSearched A (Wots.CanonicalRef.sourceMessages A) L.toWots input ∧
  WCT9.encodingCanDecode L.1.lay answer
    (Wots.CanonicalRef.referenceDigits A (Wots.CanonicalRef.sourceMessages A) L.toWots)

def ContactTest (A : Answers) (K : Coord→Prop) (input : HashInput) (answer : HashOutput) : Prop :=
 StructuralContact A K input answer ∨ EncodingContact A input answer

theorem Known.mono {D D':Coord→Prop} (h:∀c,D c→D' c) {c:Coord} (hk:Known D c) : Known D' c := by
 induction hk with
 | base hc=>exact .base (h _ hc)
 | node _ ih=>exact .node ih

theorem firstUnknown_single (K:Coord→Prop) (n:CanonGraph.Node) (c:Coord) (b:Nat)
 (h:childSlots n=[(c,b)]) (hk:¬K c) : firstUnknown K n= some (c,b) := by
 unfold firstUnknown
 rw [h]
 simp [hk]

def Clear (A:Answers) (K:Coord→Prop) (X:HashInput) (y:HashOutput) : Prop :=
 (∀n:CanonGraph.Node,Extract.Paired.Bounded n.toPos→Extract.posOf X=some n.toPos→
   ¬(X≠Extract.Paired.honestInput A n.toPos ∧ Extract.Paired.proj n.toPos y=honestValue A (.inl n))) ∧
 (∀n:CanonGraph.Node,Extract.Paired.Bounded n.toPos→Extract.posOf X=some n.toPos→∀c b,
   childSlots n=[(c,b)]→slotValue X b=honestValue A c→K c) ∧
 ¬EncodingContact A X y

theorem clear_of_not_contact {A:Answers}{K:Coord→Prop}{X:HashInput}{y:HashOutput}
 (h:¬ContactTest A K X y) : Clear A K X y := by
 refine ⟨fun n hn hp hh=>h (Or.inl ⟨n,hn,hp,Or.inr hh⟩),?_,fun he=>h (Or.inr he)⟩
 intro n hn hp c b hc hv
 by_contra hk
 exact h (Or.inl ⟨n,hn,hp,Or.inl ⟨(c,b),firstUnknown_single K n c b hc hk,hv⟩⟩)

theorem Clear.mono {A:Answers}{K K':Coord→Prop}{X:HashInput}{y:HashOutput}
 (h:Clear A K X y) (hK:∀c,K c→K' c) : Clear A K' X y :=
 ⟨h.1,fun n hn hp c b hc hv=>hK c (h.2.1 n hn hp c b hc hv),h.2.2⟩
end ClaudeWCT.W9.T3.Security.LargeResidual.Paired

namespace ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open CanonGraph
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _

def wctOpened (index : Fin (2^31)) (k : Fin 9) (output : HashOutput) : List Coord :=
 List.ofFn fun t : Fin 6 => wctItem (index,k,rawChildFromOutput output k,t)
   (4-WCT9.wordDigit (forestRank output k.val) t)
def wctPath (index : Fin (2^31)) (k : Fin 9) (output : HashOutput) : List Coord :=
 (List.range (if firstCoord k.val then 6 else 7)).filterMap fun l =>
   ftsChild index k l ((physicalChildFromOutput output k).val/2^l ^^^ 1)
def ftsItems (index : Fin (2^31)) (output : HashOutput) : List Coord :=
 (List.finRange 9).flatMap fun k => wctOpened index k output ++ wctPath index k output
noncomputable def signItems (answers : Answers) (output : HashOutput) : List Coord :=
 ftsItems (digestIndex output) output ++ layerItems
   (Wots.CanonicalRef.referenceDigits answers (Wots.CanonicalRef.sourceMessages answers)) (digestIndex output)
def RouteOk (answers : Answers) (index : Nat) : Prop :=
 ∀lay : Layer,(Wots.CanonicalRef.referenceSearch answers (Wots.CanonicalRef.sourceMessages answers)
   (SigGolfCandidate.T3.Security.LargeResidual.routeAddr index lay)).isSome
noncomputable def signDigest (answers : Answers) (message : Message) : Option (BitVec 32×HashOutput) :=
 evalWithAnswerFn answers (sharedDigestSearch (evalWithAnswerFn answers (privateNonce message)) message 0
   WCT9.digestAttemptLimit)
noncomputable def signDisclosed (answers : Answers) (published : SigGolfCandidate.T3.Cache)
    (request : SigGolfCandidate.T3.Security.Request) : List Coord :=
 if request.cache=published then
   match signDigest answers request.message with
   | some (_,output) => if RouteOk answers (WCT9.digestIndex output) then signItems answers output else []
   | none => []
 else []
end ClaudeWCT.W9.T3.Security.LargeResidual.Paired
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_LargeCouplingTrace ====
section

namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (IsDigestRow)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
inductive TaggedStep where
  | world (event : FirstHit.QueryEvent)
  | sign (request : Security.Request) (output : Option Signature) (events : List FirstHit.QueryEvent)
def TaggedStep.events : TaggedStep → List FirstHit.QueryEvent
  | .world event => [event]
  | .sign _ _ events => events
structure Tagged (α : Type) where
  value : α × QueryLog Requests
  steps : List TaggedStep
  state : LazyPrivate.State
def Tagged.events {α : Type} (tagged : Tagged α) : List FirstHit.QueryEvent :=
  tagged.steps.flatMap TaggedStep.events
noncomputable def taggedRecord {α : Type} (published : SigGolfCandidate.T3.Cache) (program : OracleComp LazyPrivate.Interaction α) :
    LazyPrivate.State → ProbComp (Tagged α) :=
  OracleComp.construct
    (fun value state => pure ⟨(value, []), [], state⟩)
    (fun input _ next state => match input, next with
      | .inl world, next => do
          let middle ← LazyPrivate.run (liftM (SigGolfCandidate.T3.Spec.query (.inl world))) state
          (fun last => (⟨last.value, .world ⟨state, .inl world, middle.1⟩ :: last.steps, last.state⟩ : Tagged α)) <$>
            next middle.1 middle.2
      | .inr request, next => do
          let block ← FirstHit.record (FullGame.authenticatedSign published request) state
          (fun last => (⟨(last.value.1, ⟨request, block.value⟩ :: last.value.2),
              .sign request block.value block.events :: last.steps, last.state⟩ : Tagged α)) <$>
            next block.value block.state)
    program
def TaggedSplit (adversary : AdversaryP) (result : FirstHit.Recorded Bool)
    (generated : FirstHit.Recorded (Digest × SigGolfCandidate.T3.Cache)) (tagged : Tagged (Option ForgeryP))
    (checked : FirstHit.Recorded Bool) : Prop :=
  generated ∈ support (FirstHit.record keygen (∅, ∅)) ∧
  tagged ∈ support (taggedRecord generated.value.2 (adversary generated.value.1 generated.value.2) generated.state) ∧
  checked ∈ support (FirstHit.record (GameWith.verdict PaddedGame.checker generated.value.1 tagged.value)
      tagged.state) ∧
  result = ⟨checked.value, generated.events ++ (tagged.events ++ checked.events), checked.state⟩
structure Monitor where
  disclosed : List Coord
  seen : List HashInput
  calls : Nat
  digests : Nat
  contact : Bool
def Monitor.initial : Monitor := ⟨[], [], 0, 0, false⟩
def Monitor.known (monitor : Monitor) : Coord → Prop :=
  Known fun c => c ∈ keygenDisclosed ∨ c ∈ monitor.disclosed
theorem Monitor.msgSlot_known (monitor : Monitor) (L : CanonEncoding.EncLeaf) (cs : Coord × Nat)
    (hc : cs ∈ msgSlots L) : monitor.known cs.1 :=
  Known.base (Or.inl (msgSlot_mem_keygen hc))

theorem Monitor.firstUnknownMsg_none (monitor : Monitor) (L : CanonEncoding.EncLeaf) :
    firstUnknownMsg monitor.known L = none := by
  apply List.find?_eq_none.mpr
  intro cs hc
  simpa using monitor.msgSlot_known L cs hc

noncomputable def Monitor.query (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor)
    (input : HashInput) (answer : HashOutput) : Monitor :=
  if monitor.contact then monitor
  else if input ∉ monitor.seen ∧ input ∈ U ∧ monitor.calls + 1 ≤ q ∧ ContactTest A monitor.known input answer then
    ⟨monitor.disclosed, input :: monitor.seen, monitor.calls + 1, monitor.digests, true⟩
  else ⟨monitor.disclosed, input :: monitor.seen, monitor.calls + 1,
    monitor.digests + (if input ∈ U ∧ IsDigestRow input ∧ monitor.calls + 1 ≤ q then 1 else 0), false⟩
noncomputable def Monitor.event (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor)
    (event : FirstHit.QueryEvent) : Monitor :=
  match event with
  | ⟨_, .inl (.inr input), answer⟩ => monitor.query U A q input answer
  | _ => monitor
noncomputable def Monitor.sign (A : Answers) (published : SigGolfCandidate.T3.Cache) (monitor : Monitor)
    (request : Security.Request) : Monitor :=
  if monitor.contact then monitor
  else ⟨monitor.disclosed ++ signDisclosed A published request, monitor.seen, monitor.calls, monitor.digests, false⟩
noncomputable def Monitor.step (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache)
    (monitor : Monitor) : TaggedStep → Monitor
  | .world event => monitor.event U A q event
  | .sign request _ _ => monitor.sign A published request
noncomputable def monitorRun (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache)
    (steps : List TaggedStep) (verdict : List FirstHit.QueryEvent) : Monitor :=
  verdict.foldl (Monitor.event U A q) (steps.foldl (Monitor.step U A q published) Monitor.initial)
def Contact (adversary : AdversaryP) (q : Nat) (z : PaddedGame.TraceResult × Answers) : Prop :=
  ∀ generated tagged checked, TaggedSplit adversary (QueryRecorded.recordedTrace z.1) generated tagged checked →
    (monitorRun (Wots.referenceInputs adversary) z.2 q generated.value.2 tagged.steps checked.events).contact = true
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
-- ==== merged from T3_Secc_LargeCouplingTrace ====
section

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
inductive TaggedStep where
  | world (event : FirstHit.QueryEvent)
  | sign (request : Security.Request) (output : Option Signature) (events : List FirstHit.QueryEvent)
def TaggedStep.events : TaggedStep → List FirstHit.QueryEvent
  | .world event => [event]
  | .sign _ _ events => events
structure Tagged (α : Type) where
  value : α × QueryLog Requests
  steps : List TaggedStep
  state : LazyPrivate.State
def Tagged.events {α : Type} (tagged : Tagged α) : List FirstHit.QueryEvent :=
  tagged.steps.flatMap TaggedStep.events
noncomputable def taggedRecord {α : Type} (published : T3.Cache) (program : OracleComp LazyPrivate.Interaction α) :
    LazyPrivate.State → ProbComp (Tagged α) :=
  OracleComp.construct
    (fun value state => pure ⟨(value, []), [], state⟩)
    (fun input _ next state => match input, next with
      | .inl world, next => do
          let middle ← LazyPrivate.run (liftM (T3.Spec.query (.inl world))) state
          (fun last => (⟨last.value, .world ⟨state, .inl world, middle.1⟩ :: last.steps, last.state⟩ : Tagged α)) <$>
            next middle.1 middle.2
      | .inr request, next => do
          let block ← FirstHit.record (FullGame.authenticatedSign published request) state
          (fun last => (⟨(last.value.1, ⟨request, block.value⟩ :: last.value.2),
              .sign request block.value block.events :: last.steps, last.state⟩ : Tagged α)) <$>
            next block.value block.state)
    program
def TaggedSplit (adversary : AdversaryP) (result : FirstHit.Recorded Bool)
    (generated : FirstHit.Recorded (Digest × T3.Cache)) (tagged : Tagged (Option ForgeryP))
    (checked : FirstHit.Recorded Bool) : Prop :=
  generated ∈ support (FirstHit.record keygen (∅, ∅)) ∧
  tagged ∈ support (taggedRecord generated.value.2 (adversary generated.value.1 generated.value.2) generated.state) ∧
  checked ∈ support (FirstHit.record (GameWith.verdict PaddedGame.checker generated.value.1 tagged.value)
      tagged.state) ∧
  result = ⟨checked.value, generated.events ++ (tagged.events ++ checked.events), checked.state⟩
end SigGolfCandidate.T3.Security.LargeCoupling
end
-- ==== merged from T3_Secc_LargeCouplingSplit ====
section

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem queryEvent_answer_eq {state : LazyPrivate.State} {input : T3.Spec.Domain} {a b : T3.Spec.Range input}
    (h : (⟨state, input, a⟩ : FirstHit.QueryEvent) = ⟨state, input, b⟩) : a = b := by
  simp only [FirstHit.QueryEvent.mk.injEq, heq_eq_eq, true_and] at h
  exact h
theorem record_prefix_unique {α : Type} (program : M α) (state : LazyPrivate.State)
    (r1 r2 : FirstHit.Recorded α) (h1 : r1 ∈ support (FirstHit.record program state))
    (h2 : r2 ∈ support (FirstHit.record program state)) (rest1 rest2 : List FirstHit.QueryEvent)
    (heq : r1.events ++ rest1 = r2.events ++ rest2) : r1 = r2 := by
  induction program using OracleComp.inductionOn generalizing state r1 r2 rest1 rest2 with
  | pure value =>
      rw [FirstHit.record_pure, mem_support_pure_iff] at h1 h2
      rw [h1, h2]
  | query_bind input next ih =>
      rw [FirstHit.record_query_bind, mem_support_bind_iff] at h1 h2
      obtain ⟨m1, hm1, h1⟩ := h1
      obtain ⟨m2, hm2, h2⟩ := h2
      rw [support_map] at h1 h2
      obtain ⟨l1, hl1, rfl⟩ := h1
      obtain ⟨l2, hl2, rfl⟩ := h2
      simp only [List.cons_append, List.cons.injEq] at heq
      have ha : m1.1 = m2.1 := queryEvent_answer_eq heq.1
      have hs1 := FirstHit.query_advance state input m1 hm1
      have hs2 := FirstHit.query_advance state input m2 hm2
      have hm : m1 = m2 := Prod.ext ha (by rw [hs1, hs2, ha])
      subst hm
      have hl := ih m1.1 m1.2 l1 l2 hl1 hl2 rest1 rest2 heq.2
      rw [hl]
end SigGolfCandidate.T3.Security.LargeCoupling
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_LargeCouplingSplit ====
section

namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeCoupling (record_prefix_unique queryEvent_answer_eq)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem taggedRecord_pure {α : Type} (published : SigGolfCandidate.T3.Cache) (value : α) (state : LazyPrivate.State) :
    taggedRecord published (pure value : OracleComp LazyPrivate.Interaction α) state =
      pure ⟨(value, []), [], state⟩ := rfl
theorem taggedRecord_world {α : Type} (published : SigGolfCandidate.T3.Cache) (input : SphincsSecurity.OracleWorld.Domain)
    (next : SphincsSecurity.OracleWorld.Range input → OracleComp LazyPrivate.Interaction α)
    (state : LazyPrivate.State) :
    taggedRecord published (liftM (LazyPrivate.Interaction.query (.inl input)) >>= next) state = (do
      let middle ← LazyPrivate.run (liftM (SigGolfCandidate.T3.Spec.query (.inl input))) state
      (fun last => (⟨last.value, .world ⟨state, .inl input, middle.1⟩ :: last.steps, last.state⟩ : Tagged α)) <$>
        taggedRecord published (next middle.1) middle.2) := rfl
theorem taggedRecord_request {α : Type} (published : SigGolfCandidate.T3.Cache) (request : Security.Request)
    (next : Option Signature → OracleComp LazyPrivate.Interaction α) (state : LazyPrivate.State) :
    taggedRecord published (liftM (LazyPrivate.Interaction.query (.inr request)) >>= next) state = (do
      let block ← FirstHit.record (FullGame.authenticatedSign published request) state
      (fun last => (⟨(last.value.1, ⟨request, block.value⟩ :: last.value.2),
          .sign request block.value block.events :: last.steps, last.state⟩ : Tagged α)) <$>
        taggedRecord published (next block.value) block.state) := rfl
def Tagged.untag {α : Type} (tagged : Tagged α) : FirstHit.Recorded (α × QueryLog Requests) :=
  ⟨tagged.value, tagged.events, tagged.state⟩
theorem taggedRecord_untag {α : Type} (published : SigGolfCandidate.T3.Cache) (program : OracleComp LazyPrivate.Interaction α)
    (state : LazyPrivate.State) (tagged : Tagged α) (h : tagged ∈ support (taggedRecord published program state)) :
    tagged.untag ∈ support (FirstHit.record (FullGame.loggedWith (FullGame.authenticatedSign published) program)
      state) := by
  induction program using OracleComp.inductionOn generalizing state tagged with
  | pure value =>
      rw [taggedRecord_pure, mem_support_pure_iff] at h
      subst h
      rw [FullGame.loggedWith_pure, FirstHit.record_pure, mem_support_pure_iff]
      rfl
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [taggedRecord_world, mem_support_bind_iff] at h
          obtain ⟨middle, hm, h⟩ := h
          rw [support_map] at h
          obtain ⟨last, hl, rfl⟩ := h
          have hu := ih middle.1 middle.2 last hl
          rw [FullGame.loggedWith_world]
          change _ ∈ support (FirstHit.record (liftM (SigGolfCandidate.T3.Spec.query (.inl input)) >>= fun answer =>
            FullGame.loggedWith (FullGame.authenticatedSign published) (next answer)) state)
          rw [FirstHit.record_query_bind, mem_support_bind_iff]
          refine ⟨middle, hm, ?_⟩
          rw [support_map]
          exact ⟨last.untag, hu, rfl⟩
      | inr request =>
          rw [taggedRecord_request, mem_support_bind_iff] at h
          obtain ⟨block, hb, h⟩ := h
          rw [support_map] at h
          obtain ⟨last, hl, rfl⟩ := h
          have hu := ih block.value block.state last hl
          rw [FullGame.loggedWith_request, FirstHit.record_bind, mem_support_bind_iff]
          refine ⟨block, hb, ?_⟩
          rw [mem_support_bind_iff]
          rw [FirstHit.record_map, support_map] at *
          refine ⟨⟨(last.value.1, ⟨request, block.value⟩ :: last.value.2), last.events, last.state⟩,
            ⟨last.untag, hu, rfl⟩, ?_⟩
          rw [mem_support_pure_iff]
          simp only [Tagged.untag, Tagged.events, List.flatMap_cons, TaggedStep.events]
theorem TaggedSplit.untag {adversary : AdversaryP} {result : FirstHit.Recorded Bool}
    {generated : FirstHit.Recorded (Digest × SigGolfCandidate.T3.Cache)} {tagged : Tagged (Option ForgeryP)}
    {checked : FirstHit.Recorded Bool} (h : TaggedSplit adversary result generated tagged checked) :
    generated ∈ support (FirstHit.record keygen (∅, ∅)) ∧
    tagged.untag ∈ support (FirstHit.record (FullGame.loggedWith (FullGame.authenticatedSign generated.value.2)
      (adversary generated.value.1 generated.value.2)) generated.state) ∧
    checked ∈ support (FirstHit.record (GameWith.verdict PaddedGame.checker generated.value.1 tagged.untag.value)
      tagged.untag.state) ∧
    result = ⟨checked.value, generated.events ++ (tagged.untag.events ++ checked.events), checked.state⟩ := by
  obtain ⟨hg, ht, hc, hr⟩ := h
  exact ⟨hg, taggedRecord_untag _ _ _ _ ht, hc, hr⟩
theorem taggedRecord_prefix_unique {α : Type} (published : SigGolfCandidate.T3.Cache) (program : OracleComp LazyPrivate.Interaction α)
    (state : LazyPrivate.State) (t1 t2 : Tagged α) (h1 : t1 ∈ support (taggedRecord published program state))
    (h2 : t2 ∈ support (taggedRecord published program state)) (rest1 rest2 : List FirstHit.QueryEvent)
    (heq : t1.events ++ rest1 = t2.events ++ rest2) : t1 = t2 := by
  induction program using OracleComp.inductionOn generalizing state t1 t2 rest1 rest2 with
  | pure value =>
      rw [taggedRecord_pure, mem_support_pure_iff] at h1 h2
      rw [h1, h2]
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [taggedRecord_world, mem_support_bind_iff] at h1 h2
          obtain ⟨m1, hm1, h1⟩ := h1
          obtain ⟨m2, hm2, h2⟩ := h2
          rw [support_map] at h1 h2
          obtain ⟨l1, hl1, rfl⟩ := h1
          obtain ⟨l2, hl2, rfl⟩ := h2
          simp only [Tagged.events, List.flatMap_cons, TaggedStep.events,
            List.cons_append, List.cons.injEq] at heq
          have ha : m1.1 = m2.1 := queryEvent_answer_eq heq.1
          have hs1 := FirstHit.query_advance state (.inl input) m1 hm1
          have hs2 := FirstHit.query_advance state (.inl input) m2 hm2
          have hm : m1 = m2 := Prod.ext ha (by rw [hs1, hs2, ha])
          subst hm
          have hl := ih m1.1 m1.2 l1 l2 hl1 hl2 rest1 rest2 heq.2
          rw [hl]
      | inr request =>
          rw [taggedRecord_request, mem_support_bind_iff] at h1 h2
          obtain ⟨b1, hb1, h1⟩ := h1
          obtain ⟨b2, hb2, h2⟩ := h2
          rw [support_map] at h1 h2
          obtain ⟨l1, hl1, rfl⟩ := h1
          obtain ⟨l2, hl2, rfl⟩ := h2
          simp only [Tagged.events, List.flatMap_cons, TaggedStep.events, List.append_assoc] at heq
          have hb := record_prefix_unique _ state b1 b2 hb1 hb2 _ _ heq
          subst hb
          have heq' := List.append_cancel_left heq
          have hl := ih b1.value b1.state l1 l2 hl1 hl2 rest1 rest2 heq'
          rw [hl]
theorem taggedSplit_unique {adversary : AdversaryP} {result : FirstHit.Recorded Bool}
    {g1 g2 : FirstHit.Recorded (Digest × SigGolfCandidate.T3.Cache)} {t1 t2 : Tagged (Option ForgeryP)}
    {c1 c2 : FirstHit.Recorded Bool}
    (h1 : TaggedSplit adversary result g1 t1 c1) (h2 : TaggedSplit adversary result g2 t2 c2) :
    g1 = g2 ∧ t1 = t2 ∧ c1 = c2 := by
  obtain ⟨hg1, ht1, hc1, hr1⟩ := h1
  obtain ⟨hg2, ht2, hc2, hr2⟩ := h2
  have hevents : g1.events ++ (t1.events ++ c1.events) = g2.events ++ (t2.events ++ c2.events) := by
    have := congrArg FirstHit.Recorded.events (hr1.symm.trans hr2)
    simpa using this
  have hg := record_prefix_unique keygen (∅, ∅) g1 g2 hg1 hg2 _ _ hevents
  subst hg
  have hevents' := List.append_cancel_left hevents
  have ht := taggedRecord_prefix_unique _ _ _ t1 t2 ht1 ht2 _ _ hevents'
  subst ht
  have hevents'' := List.append_cancel_left hevents'
  have hc := record_prefix_unique _ _ c1 c2 hc1 hc2 [] [] (by simpa using hevents'')
  exact ⟨rfl, rfl, hc⟩
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
-- ==== merged from T3_Secc_LargeContactMonitor ====
section

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem Known.mono {D D' : Coord → Prop} (h : ∀ c, D c → D' c) {c : Coord} (hk : Known D c) : Known D' c := by
  induction hk with
  | base hc => exact .base (h _ hc)
  | node _ ih => exact .node ih
def EventsAgree (A : Answers) (events : List FirstHit.QueryEvent) : Prop :=
  ∀ event ∈ events, SourceReplay.IsHash event.input → A event.input = event.answer
def chargeOf (events : List FirstHit.QueryEvent) : Nat := (events.map fun event => FullGame.queryCharge event.input).sum
end SigGolfCandidate.T3.Security.LargeCoupling
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_LargeContactMonitor ====
section

namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (slotValue IsDigestRow)
open SigGolfCandidate.T3.Security.LargeCoupling (chargeOf EventsAgree)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem Known.mono {D D' : Coord → Prop} (h : ∀ c, D c → D' c) {c : Coord} (hk : Known D c) : Known D' c := by
  induction hk with
  | base hc => exact .base (h _ hc)
  | node _ ih => exact .node ih
def Clear (A : Answers) (K : Coord → Prop) (X : HashInput) (y : HashOutput) : Prop :=
  (∀ N : CanonGraph.Node, Extract.posOf X = some N.toPos →
      ¬(X ≠ Extract.honestInput A N.toPos ∧ N.toPos.proj y = honestValue A (.inl N))) ∧
  (∀ N : CanonGraph.Node, Extract.posOf X = some N.toPos → ∀ c b, childSlots N = [(c, b)] →
      slotValue X b = honestValue A c → K c) ∧
  (∀ (L : CanonEncoding.EncLeaf) (m : WCT9.LayerMsg) (ctr : BitVec 32) (pad : Wots.RowPad),
      Extract.msgFits L.1.lay m → X = Wots.encRow L.toWots m ctr pad →
      ¬(Wots.referenceInput A L.toWots ≠ some X ∧
        decode L.1.lay (WCT9.encodingAnswer L.1.lay y) = some (Wots.referenceDigits A L.toWots)))
theorem firstUnknown_single (K : Coord → Prop) (N : CanonGraph.Node) (c : Coord) (b : Nat)
    (h : childSlots N = [(c, b)]) (hk : ¬K c) : firstUnknown K N = some (c, b) := by
  unfold firstUnknown
  rw [h]
  simp [hk]
theorem clear_of_not_contact {A : Answers} {K : Coord → Prop} {X : HashInput} {y : HashOutput}
    (h : ¬ContactTest A K X y) : Clear A K X y := by
  refine ⟨fun N hpos hhit => h (Or.inl ⟨N, hpos, Or.inr hhit⟩), fun N hpos c b hs hv => ?_,
    fun L m ctr pad hfit hX hhit => h (Or.inr ⟨L, m, ctr, pad, hfit, hX, Or.inr hhit⟩)⟩
  by_contra hk
  exact h (Or.inl ⟨N, hpos, Or.inl ⟨(c, b), firstUnknown_single K N c b hs hk, hv⟩⟩)
theorem Clear.mono {A : Answers} {K K' : Coord → Prop} {X : HashInput} {y : HashOutput}
    (h : Clear A K X y) (hK : ∀ c, K c → K' c) : Clear A K' X y :=
  ⟨h.1, fun N hpos c b hs hv => hK c (h.2.1 N hpos c b hs hv), h.2.2⟩
def MonitorOK (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) : Prop :=
  monitor.contact = false → monitor.calls ≤ q → ∀ X ∈ monitor.seen, X ∈ U →
    Clear A monitor.known X (A (.inl (.inr X)))
theorem monitorOK_initial (U : Finset HashInput) (A : Answers) (q : Nat) : MonitorOK U A q Monitor.initial := by
  intro _ _ X hX
  simp [Monitor.initial] at hX
theorem monitorOK_query (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (X : HashInput)
    (h : MonitorOK U A q monitor) : MonitorOK U A q (monitor.query U A q X (A (.inl (.inr X)))) := by
  unfold Monitor.query
  by_cases hc : monitor.contact = true
  · rw [if_pos hc]; exact h
  rw [if_neg hc]
  by_cases ht : X ∉ monitor.seen ∧ X ∈ U ∧ monitor.calls + 1 ≤ q ∧ ContactTest A monitor.known X (A (.inl (.inr X)))
  · rw [if_pos ht]
    intro hfalse
    simp at hfalse
  · rw [if_neg ht]
    intro _ hq Y hY hYU
    change monitor.calls + 1 ≤ q at hq
    have hcf : monitor.contact = false := by simpa using hc
    have hq' : monitor.calls ≤ q := by omega
    simp only [List.mem_cons] at hY
    change Clear A monitor.known Y (A (.inl (.inr Y)))
    rcases hY with rfl | hY
    · by_cases hs : Y ∈ monitor.seen
      · exact h hcf hq' Y hs hYU
      · exact clear_of_not_contact (fun hct => ht ⟨hs, hYU, hq, hct⟩)
    · exact h hcf hq' Y hY hYU
theorem monitorOK_sign (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache) (monitor : Monitor) (request : Security.Request)
    (h : MonitorOK U A q monitor) : MonitorOK U A q (monitor.sign A published request) := by
  unfold Monitor.sign
  by_cases hc : monitor.contact = true
  · rw [if_pos hc]; exact h
  rw [if_neg hc]
  intro _ hq Y hY hYU
  have hcf : monitor.contact = false := by simpa using hc
  refine (h hcf hq Y hY hYU).mono fun c hk => Known.mono (fun d hd => ?_) hk
  rcases hd with hd | hd
  · exact Or.inl hd
  · exact Or.inr (List.mem_append_left _ hd)
theorem monitorOK_event (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (event : FirstHit.QueryEvent)
    (hagree : SourceReplay.IsHash event.input → A event.input = event.answer) (h : MonitorOK U A q monitor) :
    MonitorOK U A q (monitor.event U A q event) := by
  rcases event with ⟨before, (n | X) | c, answer⟩
  · exact h
  · have hagree' : A (.inl (.inr X)) = answer := hagree trivial
    subst hagree'
    exact monitorOK_query U A q monitor X h
  · exact h
theorem monitorOK_events (U : Finset HashInput) (A : Answers) (q : Nat) (events : List FirstHit.QueryEvent) (hagree : EventsAgree A events)
    (monitor : Monitor) (h : MonitorOK U A q monitor) : MonitorOK U A q (events.foldl (Monitor.event U A q) monitor) := by
  induction events generalizing monitor with
  | nil => exact h
  | cons event rest ih =>
      rw [List.foldl_cons]
      exact ih (fun e he => hagree e (List.mem_cons_of_mem _ he)) _
        (monitorOK_event U A q monitor event (hagree event List.mem_cons_self) h)
def StepsAgree (A : Answers) (steps : List TaggedStep) : Prop :=
  ∀ step ∈ steps, ∀ event, step = .world event → SourceReplay.IsHash event.input → A event.input = event.answer
theorem monitorOK_steps (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep)
    (hagree : StepsAgree A steps) (monitor : Monitor) (h : MonitorOK U A q monitor) :
    MonitorOK U A q (steps.foldl (Monitor.step U A q published) monitor) := by
  induction steps generalizing monitor with
  | nil => exact h
  | cons step rest ih =>
      rw [List.foldl_cons]
      apply ih (fun s hs e he => hagree s (List.mem_cons_of_mem _ hs) e he)
      cases step with
      | world event => exact monitorOK_event U A q monitor event (hagree _ List.mem_cons_self event rfl) h
      | sign request output events => exact monitorOK_sign U A q published monitor request h
theorem monitorRun_clear (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep)
    (verdict : List FirstHit.QueryEvent) (hsteps : StepsAgree A steps) (hverdict : EventsAgree A verdict)
    (hno : (monitorRun U A q published steps verdict).contact = false)
    (hcalls : (monitorRun U A q published steps verdict).calls ≤ q) :
    ∀ X ∈ (monitorRun U A q published steps verdict).seen, X ∈ U →
      Clear A (monitorRun U A q published steps verdict).known X (A (.inl (.inr X))) :=
  monitorOK_events U A q verdict hverdict _
    (monitorOK_steps U A q published steps hsteps _ (monitorOK_initial U A q)) hno hcalls
theorem contact_query_mono (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (X : HashInput) (y : HashOutput)
    (h : monitor.contact = true) : (monitor.query U A q X y).contact = true := by
  unfold Monitor.query; rw [if_pos h]; exact h
theorem contact_event_mono (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (event : FirstHit.QueryEvent)
    (h : monitor.contact = true) : (monitor.event U A q event).contact = true := by
  rcases event with ⟨before, (n | X) | c, answer⟩
  · exact h
  · exact contact_query_mono U A q monitor X answer h
  · exact h
theorem contact_events_mono (U : Finset HashInput) (A : Answers) (q : Nat) (events : List FirstHit.QueryEvent) (monitor : Monitor)
    (h : monitor.contact = true) : (events.foldl (Monitor.event U A q) monitor).contact = true := by
  induction events generalizing monitor with
  | nil => exact h
  | cons event rest ih => exact ih _ (contact_event_mono U A q monitor event h)
theorem seen_query_mono (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (X Y : HashInput) (y : HashOutput)
    (h : Y ∈ monitor.seen) : Y ∈ (monitor.query U A q X y).seen := by
  unfold Monitor.query
  split_ifs <;> simp [h]
theorem seen_event_mono (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (event : FirstHit.QueryEvent) (Y : HashInput)
    (h : Y ∈ monitor.seen) : Y ∈ (monitor.event U A q event).seen := by
  rcases event with ⟨before, (n | X) | c, answer⟩
  · exact h
  · exact seen_query_mono U A q monitor X Y answer h
  · exact h
theorem seen_events_mono (U : Finset HashInput) (A : Answers) (q : Nat) (events : List FirstHit.QueryEvent) (monitor : Monitor)
    (Y : HashInput) (h : Y ∈ monitor.seen) : Y ∈ (events.foldl (Monitor.event U A q) monitor).seen := by
  induction events generalizing monitor with
  | nil => exact h
  | cons event rest ih => exact ih _ (seen_event_mono U A q monitor event Y h)
theorem events_seen (U : Finset HashInput) (A : Answers) (q : Nat) (events : List FirstHit.QueryEvent) (monitor : Monitor)
    (hno : (events.foldl (Monitor.event U A q) monitor).contact = false) :
    ∀ event ∈ events, ∀ X, event.input = .inl (.inr X) → X ∈ (events.foldl (Monitor.event U A q) monitor).seen := by
  induction events generalizing monitor with
  | nil => intro event he; cases he
  | cons event rest ih =>
      intro e he X hX
      rw [List.foldl_cons] at hno ⊢
      rcases List.mem_cons.mp he with rfl | he
      · apply seen_events_mono
        rcases e with ⟨before, (n | Y) | c, answer⟩
        · cases hX
        · simp only [Sum.inl.injEq, Sum.inr.injEq] at hX
          subst hX
          change Y ∈ (monitor.query U A q Y answer).seen
          by_cases hc : monitor.contact = true
          · exfalso
            have := contact_events_mono U A q rest _ (contact_event_mono U A q monitor ⟨before, .inl (.inr Y), answer⟩ hc)
            rw [hno] at this
            exact Bool.false_ne_true this
          · unfold Monitor.query
            rw [if_neg hc]
            split_ifs <;> exact List.mem_cons_self
        · cases hX
      · exact ih _ hno e he X hX
theorem disclosed_query (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (X : HashInput) (y : HashOutput) :
    (monitor.query U A q X y).disclosed = monitor.disclosed := by
  unfold Monitor.query
  split_ifs <;> rfl
theorem disclosed_event (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (event : FirstHit.QueryEvent) :
    (monitor.event U A q event).disclosed = monitor.disclosed := by
  rcases event with ⟨before, (n | X) | c, answer⟩
  · rfl
  · exact disclosed_query U A q monitor X answer
  · rfl
theorem disclosed_events (U : Finset HashInput) (A : Answers) (q : Nat) (events : List FirstHit.QueryEvent) (monitor : Monitor) :
    (events.foldl (Monitor.event U A q) monitor).disclosed = monitor.disclosed := by
  induction events generalizing monitor with
  | nil => rfl
  | cons event rest ih => rw [List.foldl_cons, ih, disclosed_event]
theorem disclosed_steps (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep)
    (monitor : Monitor) (c : Coord) (hc : c ∈ (steps.foldl (Monitor.step U A q published) monitor).disclosed) :
    c ∈ monitor.disclosed ∨ ∃ request, c ∈ signDisclosed A published request := by
  induction steps generalizing monitor with
  | nil => exact Or.inl hc
  | cons step rest ih =>
      rw [List.foldl_cons] at hc
      rcases ih _ hc with h | h
      · cases step with
        | world event =>
            change c ∈ (monitor.event U A q event).disclosed at h
            rw [disclosed_event] at h
            exact Or.inl h
        | sign request output events =>
            change c ∈ (monitor.sign A published request).disclosed at h
            unfold Monitor.sign at h
            split_ifs at h
            · exact Or.inl h
            · rcases List.mem_append.mp h with h | h
              · exact Or.inl h
              · exact Or.inr ⟨request, h⟩
      · exact Or.inr h
theorem monitorRun_known (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep)
    (verdict : List FirstHit.QueryEvent) (c : Coord) (hk : (monitorRun U A q published steps verdict).known c) :
    Known (fun d => d ∈ keygenDisclosed ∨ ∃ request, d ∈ signDisclosed A published request) c := by
  refine Known.mono (fun d hd => ?_) hk
  rcases hd with hd | hd
  · exact Or.inl hd
  · unfold monitorRun at hd
    rw [disclosed_events] at hd
    rcases disclosed_steps U A q published steps Monitor.initial d hd with h | h
    · simp [Monitor.initial] at h
    · exact Or.inr h
theorem calls_query_le (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (X : HashInput) (y : HashOutput) :
    (monitor.query U A q X y).calls ≤ monitor.calls + 1 := by
  unfold Monitor.query
  split_ifs <;> simp
theorem calls_event_le (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (event : FirstHit.QueryEvent) :
    (monitor.event U A q event).calls ≤ monitor.calls + FullGame.queryCharge event.input := by
  rcases event with ⟨before, (n | X) | c, answer⟩
  · exact Nat.le_add_right _ _
  · have h1 : FullGame.queryCharge (.inl (.inr X)) = 1 := by
      simp [FullGame.queryCharge, Derivation.charged]
    rw [h1]
    exact calls_query_le U A q monitor X answer
  · exact Nat.le_add_right _ _
theorem calls_events_le (U : Finset HashInput) (A : Answers) (q : Nat) (events : List FirstHit.QueryEvent) (monitor : Monitor) :
    (events.foldl (Monitor.event U A q) monitor).calls ≤ monitor.calls + chargeOf events := by
  induction events generalizing monitor with
  | nil => simp [chargeOf]
  | cons event rest ih =>
      rw [List.foldl_cons]
      have h1 := ih (monitor.event U A q event)
      have h2 := calls_event_le U A q monitor event
      simp only [chargeOf, List.map_cons, List.sum_cons] at h1 ⊢
      omega
theorem calls_steps_le (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep) (monitor : Monitor) :
    (steps.foldl (Monitor.step U A q published) monitor).calls ≤ monitor.calls + chargeOf (steps.flatMap TaggedStep.events) := by
  induction steps generalizing monitor with
  | nil => simp [chargeOf]
  | cons step rest ih =>
      rw [List.foldl_cons]
      have h1 := ih (monitor.step U A q published step)
      have h2 : (monitor.step U A q published step).calls ≤ monitor.calls + chargeOf step.events := by
        cases step with
        | world event =>
            have := calls_event_le U A q monitor event
            simp only [Monitor.step, TaggedStep.events, chargeOf, List.map_cons, List.map_nil, List.sum_cons,
              List.sum_nil] at this ⊢
            omega
        | sign request output events =>
            simp only [Monitor.step, Monitor.sign]
            split_ifs <;> simp
      simp only [chargeOf, List.flatMap_cons, List.map_append, List.sum_append] at h1 h2 ⊢
      omega
theorem monitorRun_calls_le (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep)
    (verdict : List FirstHit.QueryEvent) :
    (monitorRun U A q published steps verdict).calls ≤ chargeOf (steps.flatMap TaggedStep.events ++ verdict) := by
  unfold monitorRun
  have h1 := calls_events_le U A q verdict (steps.foldl (Monitor.step U A q published) Monitor.initial)
  have h2 := calls_steps_le U A q published steps Monitor.initial
  have h0 : Monitor.initial.calls = 0 := rfl
  simp only [chargeOf, List.map_append, List.sum_append] at h1 h2 ⊢
  omega
end ClaudeWCT.W9.T3.Security.LargeCoupling

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open SigGolfCandidate.T3.Security.LargeResidual (IsDigestRow)
open SigGolfCandidate.T3.Security.LargeCoupling (chargeOf EventsAgree)
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
inductive TaggedStep where
 | world (event : FirstHit.QueryEvent)
 | sign (request : Security.Request) (output : Option SigGolfCandidate.Research.SharedForest.Signature)
     (events : List FirstHit.QueryEvent)
def TaggedStep.events : TaggedStep → List FirstHit.QueryEvent
 | .world event => [event]
 | .sign _ _ events => events
structure Monitor where
  disclosed : List Coord
  seen : List HashInput
  calls : Nat
  digests : Nat
  contact : Bool
def Monitor.initial : Monitor := ⟨[], [], 0, 0, false⟩
def Monitor.known (monitor : Monitor) : Coord → Prop :=
  LargeResidual.Paired.Known fun c => c ∈ keygenDisclosed ∨ c ∈ monitor.disclosed
noncomputable def Monitor.query (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor)
    (input : HashInput) (answer : HashOutput) : Monitor :=
  if monitor.contact then monitor
  else if input ∉ monitor.seen ∧ input ∈ U ∧ monitor.calls + 1 ≤ q ∧ LargeResidual.Paired.ContactTest A monitor.known input answer then
    ⟨monitor.disclosed, input :: monitor.seen, monitor.calls + 1, monitor.digests, true⟩
  else ⟨monitor.disclosed, input :: monitor.seen, monitor.calls + 1,
    monitor.digests + (if input ∈ U ∧ IsDigestRow input ∧ monitor.calls + 1 ≤ q then 1 else 0), false⟩
noncomputable def Monitor.event (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor)
    (event : FirstHit.QueryEvent) : Monitor :=
  match event with
  | ⟨_, .inl (.inr input), answer⟩ => monitor.query U A q input answer
  | _ => monitor
noncomputable def Monitor.sign (A : Answers) (published : SigGolfCandidate.T3.Cache) (monitor : Monitor)
    (request : Security.Request) : Monitor :=
  if monitor.contact then monitor
  else ⟨monitor.disclosed ++ LargeResidual.Paired.signDisclosed A published request, monitor.seen, monitor.calls, monitor.digests, false⟩
noncomputable def Monitor.step (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache)
    (monitor : Monitor) : TaggedStep → Monitor
  | .world event => monitor.event U A q event
  | .sign request _ _ => monitor.sign A published request
noncomputable def monitorRun (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache)
    (steps : List TaggedStep) (verdict : List FirstHit.QueryEvent) : Monitor :=
  verdict.foldl (Monitor.event U A q) (steps.foldl (Monitor.step U A q published) Monitor.initial)

def MonitorOK (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) : Prop :=
  monitor.contact = false → monitor.calls ≤ q → ∀ X ∈ monitor.seen, X ∈ U →
    LargeResidual.Paired.Clear A monitor.known X (A (.inl (.inr X)))
theorem monitorOK_initial (U : Finset HashInput) (A : Answers) (q : Nat) : MonitorOK U A q Monitor.initial := by
  intro _ _ X hX
  simp [Monitor.initial] at hX
theorem monitorOK_query (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (X : HashInput)
    (h : MonitorOK U A q monitor) : MonitorOK U A q (monitor.query U A q X (A (.inl (.inr X)))) := by
  unfold Monitor.query
  by_cases hc : monitor.contact = true
  · rw [if_pos hc]; exact h
  rw [if_neg hc]
  by_cases ht : X ∉ monitor.seen ∧ X ∈ U ∧ monitor.calls + 1 ≤ q ∧ LargeResidual.Paired.ContactTest A monitor.known X (A (.inl (.inr X)))
  · rw [if_pos ht]
    intro hfalse
    simp at hfalse
  · rw [if_neg ht]
    intro _ hq Y hY hYU
    change monitor.calls + 1 ≤ q at hq
    have hcf : monitor.contact = false := by simpa using hc
    have hq' : monitor.calls ≤ q := by omega
    simp only [List.mem_cons] at hY
    change LargeResidual.Paired.Clear A monitor.known Y (A (.inl (.inr Y)))
    rcases hY with rfl | hY
    · by_cases hs : Y ∈ monitor.seen
      · exact h hcf hq' Y hs hYU
      · exact LargeResidual.Paired.clear_of_not_contact (fun hct => ht ⟨hs, hYU, hq, hct⟩)
    · exact h hcf hq' Y hY hYU
theorem monitorOK_sign (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache) (monitor : Monitor) (request : Security.Request)
    (h : MonitorOK U A q monitor) : MonitorOK U A q (monitor.sign A published request) := by
  unfold Monitor.sign
  by_cases hc : monitor.contact = true
  · rw [if_pos hc]; exact h
  rw [if_neg hc]
  intro _ hq Y hY hYU
  have hcf : monitor.contact = false := by simpa using hc
  refine (h hcf hq Y hY hYU).mono fun c hk => LargeResidual.Paired.Known.mono (fun d hd => ?_) hk
  rcases hd with hd | hd
  · exact Or.inl hd
  · exact Or.inr (List.mem_append_left _ hd)
theorem monitorOK_event (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (event : FirstHit.QueryEvent)
    (hagree : SourceReplay.IsHash event.input → A event.input = event.answer) (h : MonitorOK U A q monitor) :
    MonitorOK U A q (monitor.event U A q event) := by
  rcases event with ⟨before, (n | X) | c, answer⟩
  · exact h
  · have hagree' : A (.inl (.inr X)) = answer := hagree trivial
    subst hagree'
    exact monitorOK_query U A q monitor X h
  · exact h
theorem monitorOK_events (U : Finset HashInput) (A : Answers) (q : Nat) (events : List FirstHit.QueryEvent) (hagree : EventsAgree A events)
    (monitor : Monitor) (h : MonitorOK U A q monitor) : MonitorOK U A q (events.foldl (Monitor.event U A q) monitor) := by
  induction events generalizing monitor with
  | nil => exact h
  | cons event rest ih =>
      rw [List.foldl_cons]
      exact ih (fun e he => hagree e (List.mem_cons_of_mem _ he)) _
        (monitorOK_event U A q monitor event (hagree event List.mem_cons_self) h)
def StepsAgree (A : Answers) (steps : List TaggedStep) : Prop :=
  ∀ step ∈ steps, ∀ event, step = .world event → SourceReplay.IsHash event.input → A event.input = event.answer
theorem monitorOK_steps (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep)
    (hagree : StepsAgree A steps) (monitor : Monitor) (h : MonitorOK U A q monitor) :
    MonitorOK U A q (steps.foldl (Monitor.step U A q published) monitor) := by
  induction steps generalizing monitor with
  | nil => exact h
  | cons step rest ih =>
      rw [List.foldl_cons]
      apply ih (fun s hs e he => hagree s (List.mem_cons_of_mem _ hs) e he)
      cases step with
      | world event => exact monitorOK_event U A q monitor event (hagree _ List.mem_cons_self event rfl) h
      | sign request output events => exact monitorOK_sign U A q published monitor request h
theorem monitorRun_clear (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep)
    (verdict : List FirstHit.QueryEvent) (hsteps : StepsAgree A steps) (hverdict : EventsAgree A verdict)
    (hno : (monitorRun U A q published steps verdict).contact = false)
    (hcalls : (monitorRun U A q published steps verdict).calls ≤ q) :
    ∀ X ∈ (monitorRun U A q published steps verdict).seen, X ∈ U →
      LargeResidual.Paired.Clear A (monitorRun U A q published steps verdict).known X (A (.inl (.inr X))) :=
  monitorOK_events U A q verdict hverdict _
    (monitorOK_steps U A q published steps hsteps _ (monitorOK_initial U A q)) hno hcalls
theorem contact_query_mono (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (X : HashInput) (y : HashOutput)
    (h : monitor.contact = true) : (monitor.query U A q X y).contact = true := by
  unfold Monitor.query; rw [if_pos h]; exact h
theorem contact_event_mono (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (event : FirstHit.QueryEvent)
    (h : monitor.contact = true) : (monitor.event U A q event).contact = true := by
  rcases event with ⟨before, (n | X) | c, answer⟩
  · exact h
  · exact contact_query_mono U A q monitor X answer h
  · exact h
theorem contact_events_mono (U : Finset HashInput) (A : Answers) (q : Nat) (events : List FirstHit.QueryEvent) (monitor : Monitor)
    (h : monitor.contact = true) : (events.foldl (Monitor.event U A q) monitor).contact = true := by
  induction events generalizing monitor with
  | nil => exact h
  | cons event rest ih => exact ih _ (contact_event_mono U A q monitor event h)
theorem seen_query_mono (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (X Y : HashInput) (y : HashOutput)
    (h : Y ∈ monitor.seen) : Y ∈ (monitor.query U A q X y).seen := by
  unfold Monitor.query
  split_ifs <;> simp [h]
theorem seen_event_mono (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (event : FirstHit.QueryEvent) (Y : HashInput)
    (h : Y ∈ monitor.seen) : Y ∈ (monitor.event U A q event).seen := by
  rcases event with ⟨before, (n | X) | c, answer⟩
  · exact h
  · exact seen_query_mono U A q monitor X Y answer h
  · exact h
theorem seen_events_mono (U : Finset HashInput) (A : Answers) (q : Nat) (events : List FirstHit.QueryEvent) (monitor : Monitor)
    (Y : HashInput) (h : Y ∈ monitor.seen) : Y ∈ (events.foldl (Monitor.event U A q) monitor).seen := by
  induction events generalizing monitor with
  | nil => exact h
  | cons event rest ih => exact ih _ (seen_event_mono U A q monitor event Y h)
theorem events_seen (U : Finset HashInput) (A : Answers) (q : Nat) (events : List FirstHit.QueryEvent) (monitor : Monitor)
    (hno : (events.foldl (Monitor.event U A q) monitor).contact = false) :
    ∀ event ∈ events, ∀ X, event.input = .inl (.inr X) → X ∈ (events.foldl (Monitor.event U A q) monitor).seen := by
  induction events generalizing monitor with
  | nil => intro event he; cases he
  | cons event rest ih =>
      intro e he X hX
      rw [List.foldl_cons] at hno ⊢
      rcases List.mem_cons.mp he with rfl | he
      · apply seen_events_mono
        rcases e with ⟨before, (n | Y) | c, answer⟩
        · cases hX
        · simp only [Sum.inl.injEq, Sum.inr.injEq] at hX
          subst hX
          change Y ∈ (monitor.query U A q Y answer).seen
          by_cases hc : monitor.contact = true
          · exfalso
            have := contact_events_mono U A q rest _ (contact_event_mono U A q monitor ⟨before, .inl (.inr Y), answer⟩ hc)
            rw [hno] at this
            exact Bool.false_ne_true this
          · unfold Monitor.query
            rw [if_neg hc]
            split_ifs <;> exact List.mem_cons_self
        · cases hX
      · exact ih _ hno e he X hX
theorem disclosed_query (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (X : HashInput) (y : HashOutput) :
    (monitor.query U A q X y).disclosed = monitor.disclosed := by
  unfold Monitor.query
  split_ifs <;> rfl
theorem disclosed_event (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (event : FirstHit.QueryEvent) :
    (monitor.event U A q event).disclosed = monitor.disclosed := by
  rcases event with ⟨before, (n | X) | c, answer⟩
  · rfl
  · exact disclosed_query U A q monitor X answer
  · rfl
theorem disclosed_events (U : Finset HashInput) (A : Answers) (q : Nat) (events : List FirstHit.QueryEvent) (monitor : Monitor) :
    (events.foldl (Monitor.event U A q) monitor).disclosed = monitor.disclosed := by
  induction events generalizing monitor with
  | nil => rfl
  | cons event rest ih => rw [List.foldl_cons, ih, disclosed_event]
theorem disclosed_steps (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep)
    (monitor : Monitor) (c : Coord) (hc : c ∈ (steps.foldl (Monitor.step U A q published) monitor).disclosed) :
    c ∈ monitor.disclosed ∨ ∃ request, c ∈ LargeResidual.Paired.signDisclosed A published request := by
  induction steps generalizing monitor with
  | nil => exact Or.inl hc
  | cons step rest ih =>
      rw [List.foldl_cons] at hc
      rcases ih _ hc with h | h
      · cases step with
        | world event =>
            change c ∈ (monitor.event U A q event).disclosed at h
            rw [disclosed_event] at h
            exact Or.inl h
        | sign request output events =>
            change c ∈ (monitor.sign A published request).disclosed at h
            unfold Monitor.sign at h
            split_ifs at h
            · exact Or.inl h
            · rcases List.mem_append.mp h with h | h
              · exact Or.inl h
              · exact Or.inr ⟨request, h⟩
      · exact Or.inr h
theorem monitorRun_known (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep)
    (verdict : List FirstHit.QueryEvent) (c : Coord) (hk : (monitorRun U A q published steps verdict).known c) :
    LargeResidual.Paired.Known (fun d => d ∈ keygenDisclosed ∨ ∃ request, d ∈ LargeResidual.Paired.signDisclosed A published request) c := by
  refine LargeResidual.Paired.Known.mono (fun d hd => ?_) hk
  rcases hd with hd | hd
  · exact Or.inl hd
  · unfold monitorRun at hd
    rw [disclosed_events] at hd
    rcases disclosed_steps U A q published steps Monitor.initial d hd with h | h
    · simp [Monitor.initial] at h
    · exact Or.inr h
theorem calls_query_le (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (X : HashInput) (y : HashOutput) :
    (monitor.query U A q X y).calls ≤ monitor.calls + 1 := by
  unfold Monitor.query
  split_ifs <;> simp
theorem calls_event_le (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (event : FirstHit.QueryEvent) :
    (monitor.event U A q event).calls ≤ monitor.calls + FullGame.queryCharge event.input := by
  rcases event with ⟨before, (n | X) | c, answer⟩
  · exact Nat.le_add_right _ _
  · have h1 : FullGame.queryCharge (.inl (.inr X)) = 1 := by
      simp [FullGame.queryCharge, Derivation.charged]
    rw [h1]
    exact calls_query_le U A q monitor X answer
  · exact Nat.le_add_right _ _
theorem calls_events_le (U : Finset HashInput) (A : Answers) (q : Nat) (events : List FirstHit.QueryEvent) (monitor : Monitor) :
    (events.foldl (Monitor.event U A q) monitor).calls ≤ monitor.calls + chargeOf events := by
  induction events generalizing monitor with
  | nil => simp [chargeOf]
  | cons event rest ih =>
      rw [List.foldl_cons]
      have h1 := ih (monitor.event U A q event)
      have h2 := calls_event_le U A q monitor event
      simp only [chargeOf, List.map_cons, List.sum_cons] at h1 ⊢
      omega
theorem calls_steps_le (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep) (monitor : Monitor) :
    (steps.foldl (Monitor.step U A q published) monitor).calls ≤ monitor.calls + chargeOf (steps.flatMap TaggedStep.events) := by
  induction steps generalizing monitor with
  | nil => simp [chargeOf]
  | cons step rest ih =>
      rw [List.foldl_cons]
      have h1 := ih (monitor.step U A q published step)
      have h2 : (monitor.step U A q published step).calls ≤ monitor.calls + chargeOf step.events := by
        cases step with
        | world event =>
            have := calls_event_le U A q monitor event
            simp only [Monitor.step, TaggedStep.events, chargeOf, List.map_cons, List.map_nil, List.sum_cons,
              List.sum_nil] at this ⊢
            omega
        | sign request output events =>
            simp only [Monitor.step, Monitor.sign]
            split_ifs <;> simp
      simp only [chargeOf, List.flatMap_cons, List.map_append, List.sum_append] at h1 h2 ⊢
      omega
theorem monitorRun_calls_le (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep)
    (verdict : List FirstHit.QueryEvent) :
    (monitorRun U A q published steps verdict).calls ≤ chargeOf (steps.flatMap TaggedStep.events ++ verdict) := by
  unfold monitorRun
  have h1 := calls_events_le U A q verdict (steps.foldl (Monitor.step U A q published) Monitor.initial)
  have h2 := calls_steps_le U A q published steps Monitor.initial
  have h0 : Monitor.initial.calls = 0 := rfl
  simp only [chargeOf, List.map_append, List.sum_append] at h1 h2 ⊢
  omega

end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.LargeCoupling (record_prefix_unique queryEvent_answer_eq)
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
structure Tagged (α : Type) where
  value : α × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests
  steps : List TaggedStep
  state : LazyPrivate.State
def Tagged.events {α : Type} (tagged : Tagged α) : List FirstHit.QueryEvent :=
  tagged.steps.flatMap TaggedStep.events
noncomputable def taggedRecord {α : Type} (published : SigGolfCandidate.T3.Cache) (program : OracleComp PairedOuter.LazyPrivate.Interaction α) :
    LazyPrivate.State → ProbComp (Tagged α) :=
  OracleComp.construct
    (fun value state => pure ⟨(value, []), [], state⟩)
    (fun input _ next state => match input, next with
      | .inl world, next => do
          let middle ← LazyPrivate.run (liftM (SigGolfCandidate.T3.Spec.query (.inl world))) state
          (fun last => (⟨last.value, .world ⟨state, .inl world, middle.1⟩ :: last.steps, last.state⟩ : Tagged α)) <$>
            next middle.1 middle.2
      | .inr request, next => do
          let block ← FirstHit.record (PairedOuter.FullGame.authenticatedSign published request) state
          (fun last => (⟨(last.value.1, ⟨request, block.value⟩ :: last.value.2),
              .sign request block.value block.events :: last.steps, last.state⟩ : Tagged α)) <$>
            next block.value block.state)
    program
def TaggedSplit (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (result : FirstHit.Recorded Bool)
    (generated : FirstHit.Recorded (Digest × SigGolfCandidate.T3.Cache)) (tagged : Tagged (Option ClaudeWCT.W9.T3M.Final.Paired.ForgeryP))
    (checked : FirstHit.Recorded Bool) : Prop :=
  generated ∈ support (FirstHit.record keygen (∅, ∅)) ∧
  tagged ∈ support (taggedRecord generated.value.2 (adversary generated.value.1 generated.value.2) generated.state) ∧
  checked ∈ support (FirstHit.record (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker generated.value.1 tagged.value)
      tagged.state) ∧
  result = ⟨checked.value, generated.events ++ (tagged.events ++ checked.events), checked.state⟩
theorem taggedRecord_pure {α : Type} (published : SigGolfCandidate.T3.Cache) (value : α) (state : LazyPrivate.State) :
    taggedRecord published (pure value : OracleComp PairedOuter.LazyPrivate.Interaction α) state =
      pure ⟨(value, []), [], state⟩ := rfl
theorem taggedRecord_world {α : Type} (published : SigGolfCandidate.T3.Cache) (input : SphincsSecurity.OracleWorld.Domain)
    (next : SphincsSecurity.OracleWorld.Range input → OracleComp PairedOuter.LazyPrivate.Interaction α)
    (state : LazyPrivate.State) :
    taggedRecord published (liftM (PairedOuter.LazyPrivate.Interaction.query (.inl input)) >>= next) state = (do
      let middle ← LazyPrivate.run (liftM (SigGolfCandidate.T3.Spec.query (.inl input))) state
      (fun last => (⟨last.value, .world ⟨state, .inl input, middle.1⟩ :: last.steps, last.state⟩ : Tagged α)) <$>
        taggedRecord published (next middle.1) middle.2) := rfl
theorem taggedRecord_request {α : Type} (published : SigGolfCandidate.T3.Cache) (request : Security.Request)
    (next : Option SigGolfCandidate.Research.SharedForest.Signature → OracleComp PairedOuter.LazyPrivate.Interaction α) (state : LazyPrivate.State) :
    taggedRecord published (liftM (PairedOuter.LazyPrivate.Interaction.query (.inr request)) >>= next) state = (do
      let block ← FirstHit.record (PairedOuter.FullGame.authenticatedSign published request) state
      (fun last => (⟨(last.value.1, ⟨request, block.value⟩ :: last.value.2),
          .sign request block.value block.events :: last.steps, last.state⟩ : Tagged α)) <$>
        taggedRecord published (next block.value) block.state) := rfl
def Tagged.untag {α : Type} (tagged : Tagged α) : FirstHit.Recorded (α × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) :=
  ⟨tagged.value, tagged.events, tagged.state⟩
theorem taggedRecord_untag {α : Type} (published : SigGolfCandidate.T3.Cache) (program : OracleComp PairedOuter.LazyPrivate.Interaction α)
    (state : LazyPrivate.State) (tagged : Tagged α) (h : tagged ∈ support (taggedRecord published program state)) :
    tagged.untag ∈ support (FirstHit.record (PairedOuter.FullGame.loggedWith (PairedOuter.FullGame.authenticatedSign published) program)
      state) := by
  induction program using OracleComp.inductionOn generalizing state tagged with
  | pure value =>
      rw [taggedRecord_pure, mem_support_pure_iff] at h
      subst h
      rw [PairedOuter.FullGame.loggedWith_pure, FirstHit.record_pure, mem_support_pure_iff]
      rfl
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [taggedRecord_world, mem_support_bind_iff] at h
          obtain ⟨middle, hm, h⟩ := h
          rw [support_map] at h
          obtain ⟨last, hl, rfl⟩ := h
          have hu := ih middle.1 middle.2 last hl
          rw [PairedOuter.FullGame.loggedWith_world]
          change _ ∈ support (FirstHit.record (liftM (SigGolfCandidate.T3.Spec.query (.inl input)) >>= fun answer =>
            PairedOuter.FullGame.loggedWith (PairedOuter.FullGame.authenticatedSign published) (next answer)) state)
          rw [FirstHit.record_query_bind, mem_support_bind_iff]
          refine ⟨middle, hm, ?_⟩
          rw [support_map]
          exact ⟨last.untag, hu, rfl⟩
      | inr request =>
          rw [taggedRecord_request, mem_support_bind_iff] at h
          obtain ⟨block, hb, h⟩ := h
          rw [support_map] at h
          obtain ⟨last, hl, rfl⟩ := h
          have hu := ih block.value block.state last hl
          rw [PairedOuter.FullGame.loggedWith_request, FirstHit.record_bind, mem_support_bind_iff]
          refine ⟨block, hb, ?_⟩
          rw [mem_support_bind_iff]
          rw [FirstHit.record_map, support_map] at *
          refine ⟨⟨(last.value.1, ⟨request, block.value⟩ :: last.value.2), last.events, last.state⟩,
            ⟨last.untag, hu, rfl⟩, ?_⟩
          rw [mem_support_pure_iff]
          simp only [Tagged.untag, Tagged.events, List.flatMap_cons, TaggedStep.events]
theorem TaggedSplit.untag {adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP} {result : FirstHit.Recorded Bool}
    {generated : FirstHit.Recorded (Digest × SigGolfCandidate.T3.Cache)} {tagged : Tagged (Option ClaudeWCT.W9.T3M.Final.Paired.ForgeryP)}
    {checked : FirstHit.Recorded Bool} (h : TaggedSplit adversary result generated tagged checked) :
    generated ∈ support (FirstHit.record keygen (∅, ∅)) ∧
    tagged.untag ∈ support (FirstHit.record (PairedOuter.FullGame.loggedWith (PairedOuter.FullGame.authenticatedSign generated.value.2)
      (adversary generated.value.1 generated.value.2)) generated.state) ∧
    checked ∈ support (FirstHit.record (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker generated.value.1 tagged.untag.value)
      tagged.untag.state) ∧
    result = ⟨checked.value, generated.events ++ (tagged.untag.events ++ checked.events), checked.state⟩ := by
  obtain ⟨hg, ht, hc, hr⟩ := h
  exact ⟨hg, taggedRecord_untag _ _ _ _ ht, hc, hr⟩
theorem taggedRecord_prefix_unique {α : Type} (published : SigGolfCandidate.T3.Cache) (program : OracleComp PairedOuter.LazyPrivate.Interaction α)
    (state : LazyPrivate.State) (t1 t2 : Tagged α) (h1 : t1 ∈ support (taggedRecord published program state))
    (h2 : t2 ∈ support (taggedRecord published program state)) (rest1 rest2 : List FirstHit.QueryEvent)
    (heq : t1.events ++ rest1 = t2.events ++ rest2) : t1 = t2 := by
  induction program using OracleComp.inductionOn generalizing state t1 t2 rest1 rest2 with
  | pure value =>
      rw [taggedRecord_pure, mem_support_pure_iff] at h1 h2
      rw [h1, h2]
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [taggedRecord_world, mem_support_bind_iff] at h1 h2
          obtain ⟨m1, hm1, h1⟩ := h1
          obtain ⟨m2, hm2, h2⟩ := h2
          rw [support_map] at h1 h2
          obtain ⟨l1, hl1, rfl⟩ := h1
          obtain ⟨l2, hl2, rfl⟩ := h2
          simp only [Tagged.events, List.flatMap_cons, TaggedStep.events,
            List.cons_append, List.cons.injEq] at heq
          have ha : m1.1 = m2.1 := queryEvent_answer_eq heq.1
          have hs1 := FirstHit.query_advance state (.inl input) m1 hm1
          have hs2 := FirstHit.query_advance state (.inl input) m2 hm2
          have hm : m1 = m2 := Prod.ext ha (by rw [hs1, hs2, ha])
          subst hm
          have hl := ih m1.1 m1.2 l1 l2 hl1 hl2 rest1 rest2 heq.2
          rw [hl]
      | inr request =>
          rw [taggedRecord_request, mem_support_bind_iff] at h1 h2
          obtain ⟨b1, hb1, h1⟩ := h1
          obtain ⟨b2, hb2, h2⟩ := h2
          rw [support_map] at h1 h2
          obtain ⟨l1, hl1, rfl⟩ := h1
          obtain ⟨l2, hl2, rfl⟩ := h2
          simp only [Tagged.events, List.flatMap_cons, TaggedStep.events, List.append_assoc] at heq
          have hb := record_prefix_unique _ state b1 b2 hb1 hb2 _ _ heq
          subst hb
          have heq' := List.append_cancel_left heq
          have hl := ih b1.value b1.state l1 l2 hl1 hl2 rest1 rest2 heq'
          rw [hl]
theorem taggedSplit_unique {adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP} {result : FirstHit.Recorded Bool}
    {g1 g2 : FirstHit.Recorded (Digest × SigGolfCandidate.T3.Cache)} {t1 t2 : Tagged (Option ClaudeWCT.W9.T3M.Final.Paired.ForgeryP)}
    {c1 c2 : FirstHit.Recorded Bool}
    (h1 : TaggedSplit adversary result g1 t1 c1) (h2 : TaggedSplit adversary result g2 t2 c2) :
    g1 = g2 ∧ t1 = t2 ∧ c1 = c2 := by
  obtain ⟨hg1, ht1, hc1, hr1⟩ := h1
  obtain ⟨hg2, ht2, hc2, hr2⟩ := h2
  have hevents : g1.events ++ (t1.events ++ c1.events) = g2.events ++ (t2.events ++ c2.events) := by
    have := congrArg FirstHit.Recorded.events (hr1.symm.trans hr2)
    simpa using this
  have hg := record_prefix_unique keygen (∅, ∅) g1 g2 hg1 hg2 _ _ hevents
  subst hg
  have hevents' := List.append_cancel_left hevents
  have ht := taggedRecord_prefix_unique _ _ _ t1 t2 ht1 ht2 _ _ hevents'
  subst ht
  have hevents'' := List.append_cancel_left hevents'
  have hc := record_prefix_unique _ _ c1 c2 hc1 hc2 [] [] (by simpa using hevents'')
  exact ⟨rfl, rfl, hc⟩

end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.LargeCoupling (record_prefix_unique queryEvent_answer_eq)
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable def taggedFixed {α : Type} (F : Answers) (published : SigGolfCandidate.T3.Cache)
    (program : OracleComp PairedOuter.LazyPrivate.Interaction α) : LazyPrivate.State → ProbComp (Tagged α) :=
  OracleComp.construct
    (fun value state => pure ⟨(value, []), [], state⟩)
    (fun input _ next state => match input, next with
      | .inl world, next => do
          let answer ← Wots.Ref.fixedWorld F (.inl world)
          (fun last => (⟨last.value, .world ⟨state, .inl world, answer⟩ :: last.steps, last.state⟩ : Tagged α)) <$>
            next answer (FirstHit.advance state (.inl world) answer)
      | .inr request, next => do
          let block ← Wots.Ref.fixedRecord F (PairedOuter.FullGame.authenticatedSign published request) state
          (fun last => (⟨(last.value.1, ⟨request, block.value⟩ :: last.value.2),
              .sign request block.value block.events :: last.steps, last.state⟩ : Tagged α)) <$>
            next block.value block.state)
    program
section Fixed
variable {α : Type} (F : Answers) (published : SigGolfCandidate.T3.Cache)
theorem taggedFixed_pure (value : α) (state : LazyPrivate.State) :
    taggedFixed F published (pure value : OracleComp PairedOuter.LazyPrivate.Interaction α) state =
      pure ⟨(value, []), [], state⟩ := rfl
theorem taggedFixed_world (input : SphincsSecurity.OracleWorld.Domain)
    (next : SphincsSecurity.OracleWorld.Range input → OracleComp PairedOuter.LazyPrivate.Interaction α)
    (state : LazyPrivate.State) :
    taggedFixed F published (liftM (PairedOuter.LazyPrivate.Interaction.query (.inl input)) >>= next) state = (do
      let answer ← Wots.Ref.fixedWorld F (.inl input)
      (fun last => (⟨last.value, .world ⟨state, .inl input, answer⟩ :: last.steps, last.state⟩ : Tagged α)) <$>
        taggedFixed F published (next answer) (FirstHit.advance state (.inl input) answer)) := rfl
theorem taggedFixed_request (request : Security.Request)
    (next : Option SigGolfCandidate.Research.SharedForest.Signature → OracleComp PairedOuter.LazyPrivate.Interaction α) (state : LazyPrivate.State) :
    taggedFixed F published (liftM (PairedOuter.LazyPrivate.Interaction.query (.inr request)) >>= next) state = (do
      let block ← Wots.Ref.fixedRecord F (PairedOuter.FullGame.authenticatedSign published request) state
      (fun last => (⟨(last.value.1, ⟨request, block.value⟩ :: last.value.2),
          .sign request block.value block.events :: last.steps, last.state⟩ : Tagged α)) <$>
        taggedFixed F published (next block.value) block.state) := rfl
theorem taggedFixed_support (program : OracleComp PairedOuter.LazyPrivate.Interaction α) (state : LazyPrivate.State)
    (hF : Wots.Ref.Agrees F state) (tagged : Tagged α) (h : tagged ∈ support (taggedFixed F published program state)) :
    tagged ∈ support (taggedRecord published program state) ∧ Wots.Ref.Agrees F tagged.state := by
  induction program using OracleComp.inductionOn generalizing state tagged with
  | pure value =>
      rw [taggedFixed_pure, mem_support_pure_iff] at h
      subst h
      exact ⟨by rw [taggedRecord_pure, mem_support_pure_iff], hF⟩
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [taggedFixed_world, mem_support_bind_iff] at h
          obtain ⟨answer, ha, h⟩ := h
          rw [support_map] at h
          obtain ⟨last, hl, rfl⟩ := h
          have hcons : ∀ cached, SourceReplay.known state (.inl input) = some cached → cached = answer := by
            intro cached hc
            rcases input with n | x
            · cases hc
            · have h1 := hF _ _ hc
              rw [Wots.Ref.fixedWorld_public, mem_support_pure_iff] at ha
              rw [ha, ← h1]
          have hadv : Wots.Ref.Agrees F (FirstHit.advance state (.inl input) answer) := by
            rcases input with n | x
            · exact hF
            · rw [Wots.Ref.fixedWorld_public, mem_support_pure_iff] at ha
              subst ha
              exact Wots.Ref.agrees_advance hF _
          obtain ⟨h1, h2⟩ := ih answer _ hadv last hl
          refine ⟨?_, h2⟩
          rw [taggedRecord_world, mem_support_bind_iff]
          refine ⟨(answer, FirstHit.advance state (.inl input) answer),
            Wots.Ref.lazy_query_mem state (.inl input) answer hcons, ?_⟩
          rw [support_map]
          exact ⟨last, h1, rfl⟩
      | inr request =>
          rw [taggedFixed_request, mem_support_bind_iff] at h
          obtain ⟨block, hb, h⟩ := h
          rw [support_map] at h
          obtain ⟨last, hl, rfl⟩ := h
          obtain ⟨hb1, hb2⟩ := Wots.Ref.fixedRecord_mem_record F _ state hF block hb
          obtain ⟨h1, h2⟩ := ih block.value block.state hb2 last hl
          refine ⟨?_, h2⟩
          rw [taggedRecord_request, mem_support_bind_iff]
          exact ⟨block, hb1, by rw [support_map]; exact ⟨last, h1, rfl⟩⟩
theorem taggedFixed_untag (program : OracleComp PairedOuter.LazyPrivate.Interaction α) (state : LazyPrivate.State) :
    Tagged.untag <$> taggedFixed F published program state =
      Wots.Ref.fixedRecord F (PairedOuter.FullGame.loggedWith (PairedOuter.FullGame.authenticatedSign published) program) state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value =>
      rw [taggedFixed_pure, map_pure, PairedOuter.FullGame.loggedWith_pure, Wots.Ref.fixedRecord_pure]
      rfl
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [taggedFixed_world, PairedOuter.FullGame.loggedWith_world]
          change _ = Wots.Ref.fixedRecord F (liftM (SigGolfCandidate.T3.Spec.query (.inl input)) >>= fun answer =>
            PairedOuter.FullGame.loggedWith (PairedOuter.FullGame.authenticatedSign published) (next answer)) state
          rw [Wots.Ref.fixedRecord_query_bind, map_bind]
          apply bind_congr
          intro answer
          rw [Functor.map_map, ← ih answer]
          simp only [Functor.map_map]
          rfl
      | inr request =>
          rw [taggedFixed_request, PairedOuter.FullGame.loggedWith_request, Wots.Ref.fixedRecord_bind, map_bind]
          apply bind_congr
          intro block
          rw [Wots.Ref.fixedRecord_map, ← ih block.value, Functor.map_map, Functor.map_map,
            map_eq_bind_pure_comp]
          simp only [Function.comp_def, bind_pure_comp, Functor.map_map]
          rfl
end Fixed
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
def Contact (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat)
    (z : PairedOuter.PaddedGame.TraceResult × Answers) : Prop :=
  ∀ generated tagged checked, TaggedSplit adversary (QueryRecorded.recordedTrace z.1) generated tagged checked →
    (monitorRun (Wots.PairedReference.referenceInputs adversary) z.2 q generated.value.2 tagged.steps checked.events).contact = true
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
end
-- ==== merged from T3_Secc_LargeResidualRouter ====
section

namespace SigGolfCandidate.T3.Security.LargeResidual
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open CanonGraph CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_largeResidualRouter : DecidableEq T3.Cache := Classical.decEq _
inductive AuxQuery where
  | coin (n : Nat)
  | init
structure AuxData where
  high : CanonGraph.Node → Digest
  rows : EncLeaf → Fin (2 ^ 22) → HashOutput
  priv : FullGame.FullTable
noncomputable def AuxData.sel (a : AuxData) : Selections := fun L =>
  SphincsSecurity.Concrete.FirstSuccessTable.select (decodeAt L) (a.rows L)
abbrev AuxSpec : OracleSpec AuxQuery
  | .coin n => Fin (n + 1)
  | .init => AuxData
abbrev Cell (U : Finset HashInput) := {x // x ∈ U}
abbrev WCoord := Coord ⊕ Message
abbrev RWorld (U : Finset HashInput) := World AuxSpec WCoord (Cell U)
section Requests
variable (U : Finset HashInput)
def discloseReq (c : WCoord) (charge : Charge) : OracleComp (RWorld U) Digest :=
  liftM ((RWorld U).query (.inr (.disclose c charge)))
end Requests
def lookupVal (pairs : List (Coord × Digest)) (c : Coord) : Digest :=
  ((pairs.find? fun p => decide (p.1 = c)).map Prod.snd).getD 0
structure RouterState where
  disclosed : List Coord
  seen : List HashInput
  calls : Nat
  trials : List HashInput
  births : List (HashInput × HashOutput)
  exposures : List HashOutput
  reused : Bool
  memo : List (Message × Option (BitVec 32 × HashOutput))
def RouterState.initial : RouterState := ⟨[], [], 0, [], [], [], false, []⟩
def RouterState.after (st : RouterState) (X : HashInput) : RouterState :=
  { st with seen := X :: st.seen, calls := st.calls + 1 }
def RouterState.Fresh (st : RouterState) (X : HashInput) : Prop := X ∉ st.seen ∧ X ∉ st.trials
noncomputable def RouterState.next (U : Finset HashInput) (st : RouterState) (X : HashInput) (y : HashOutput) :
    RouterState :=
  if X ∈ U ∧ IsDigestRow X ∧ st.Fresh X then { st.after X with births := (X, y) :: st.births } else st.after X
def RouterState.known (st : RouterState) : Coord → Prop :=
  Known fun c => c ∈ keygenDisclosed ∨ c ∈ st.disclosed
noncomputable def dummyDigest (lay : Layer) : Digest := Classical.choose (Wots.dummyDigits_valid lay)
noncomputable def refDigest (a : AuxData) (L : EncLeaf) : Digest :=
  match a.sel L with
  | some r => r.2
  | none => dummyDigest L.1.lay
def PrefixRow (a : AuxData) (L : EncLeaf) (ctr : BitVec 32) : Prop :=
  ctr.toNat < 2 ^ 22 ∧ ∀ r, a.sel L = some r → ctr.toNat ≤ r.1.val
def prefixValue (a : AuxData) (L : EncLeaf) (ctr : BitVec 32) : HashOutput :=
  if h : ctr.toNat < 2 ^ 22 then a.rows L ⟨ctr.toNat, h⟩ else 0
def maskOf (a : AuxData) (level node : Nat) : Digest :=
  let answer := a.priv (.inl (header 13 0 0 level (node/2)))
  if node%2=0 then answer.extractLsb' 0 128 else answer.extractLsb' 128 128
def macOf (a : AuxData) (region : Region) : HashOutput :=
  SiggolfT3Mac4.encodeTag (SiggolfT3Mac4.macTag
    (fun i => a.priv (.inl (header 14 0 0 0 i.val))) (List.ofFn region))
def topValue (v : Coord → Digest) (level node : Nat) : Digest :=
  ((treeChild 0 0 level node).map v).getD 0
section Route
variable (U : Finset HashInput)
def RouterState.cache (st : RouterState) : Sampling.RCache := fun X => st.births.lookup X
end Route
end SigGolfCandidate.T3.Security.LargeResidual
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_FamResidual ====
section

/-!
# The residual lazy engine with FTS seed families (campaign X1, stream A5)

The T3 engine `SigGolfCandidate.T3.Security.LargeResidual` keeps a product posterior `candidates : Coord → Finset Digest`
and samples hidden labels uniformly from the product box. On the switched W9 spec some observables are FTS seeds:
the seed at `(family, point)` is `familyEval K point` for a hidden coefficient vector `K : Fin 102 → Digest`.

This module keeps the T3 `State` (the `candidates` record every disclosure and every failed guess, seeds included) and
changes the law: the hidden object is `x : Hid Coord = (Plain → Digest) × (∀ f, Coefs (deg f))` (uniform prior), observed
labels are `view x`, and the posterior given `candidates` is uniform on `supp candidates`, the hidden objects whose
labels lie in the candidate sets. Disclosures sample the posterior marginal (`discLaw`, uniform on the candidates for
plain coordinates); a probe's guess on a seed is kept only while its family is undetermined (`Adm`: at most `deg`
disclosed seeds in the family, and the hit is not a seed), and the seed hazard then comes from
`ClaudeWCT.Arith.fam_hazard_prob`. `run_posterior` (exact Bayes) and `residual_potential` keep the T3 statements.
-/

section
namespace ClaudeWCT.W9.T3.Security.FamResidual
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
open SigGolfCandidate.T3.Security.LargeResidual (Digest HashOutput low Hit Probe response response_apply)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

/-- Coefficient vectors of a degree-`n` family. -/
abbrev Coefs (n : ℕ) := Fin (n + 1) → Digest

/-- The seed of a family at a point. -/
def ev {n : ℕ} (K : Fin n → Digest) (p : ℕ) : Digest := ClaudeWCT.Arith.familyEval (List.ofFn K) p

/-- Observable coordinates split into plain coordinates (independent uniform labels) and FTS seeds (a family and
an evaluation point below 1024; distinct seeds have distinct `(family, point)`). -/
class Seeds (Coord : Type) where
  Plain : Type
  Fam : Type
  [plainFin : Fintype Plain]
  [plainDec : DecidableEq Plain]
  [famFin : Fintype Fam]
  [famDec : DecidableEq Fam]
  deg : Fam → ℕ
  split : Coord → Plain ⊕ (Fam × ℕ)
  embed : Plain → Coord
  split_embed : ∀ p, split (embed p) = .inl p
  embed_of_split : ∀ c p, split c = .inl p → embed p = c
  point_lt : ∀ c f pt, split c = .inr (f, pt) → pt < 1024
  seed_inj : ∀ c c' fp, split c = .inr fp → split c' = .inr fp → c = c'

instance instSeedsPlainFin {Coord : Type} [h : Seeds Coord] : Fintype (Seeds.Plain Coord) := h.plainFin
instance instSeedsPlainDec {Coord : Type} [h : Seeds Coord] : DecidableEq (Seeds.Plain Coord) := h.plainDec
instance instSeedsFamFin {Coord : Type} [h : Seeds Coord] : Fintype (Seeds.Fam Coord) := h.famFin
instance instSeedsFamDec {Coord : Type} [h : Seeds Coord] : DecidableEq (Seeds.Fam Coord) := h.famDec

/-- Hidden objects: plain labels and family coefficients. -/
abbrev Hid (Coord : Type) [Seeds Coord] :=
  (Seeds.Plain Coord → Digest) × ((f : Seeds.Fam Coord) → Coefs (Seeds.deg f))

section Bayes
variable {Coord : Type} [Seeds Coord]

/-- Observed labels of a hidden object. -/
def view (x : Hid Coord) (c : Coord) : Digest :=
  match Seeds.split c with
  | .inl p => x.1 p
  | .inr fp => ev (x.2 fp.1) fp.2

/-- Hidden objects consistent with the candidate sets. -/
noncomputable def supp (cand : Coord → Finset Digest) : Finset (Hid Coord) :=
  Finset.univ.filter fun x => ∀ c, view x c ∈ cand c

theorem mem_supp (cand : Coord → Finset Digest) (x : Hid Coord) : x ∈ supp cand ↔ ∀ c, view x c ∈ cand c := by
  simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and]

end Bayes

section Cell
variable {X : Type} [DecidableEq X]

/-- The guard identity for the uniform law on a finset. -/
theorem cell_guard (S : Finset X) (P : X → Prop) (x : X) :
    (if P x then cell S x else 0) = ((S.filter P).card / S.card : ℝ≥0∞) * cell (S.filter P) x := by
  rw [cell_apply, cell_apply]
  by_cases hx : x ∈ S.filter P
  · have hxS : x ∈ S := (Finset.mem_filter.mp hx).1
    have hP : P x := (Finset.mem_filter.mp hx).2
    rw [if_pos hP, if_pos hxS, if_pos hx]
    have hpos : ((S.filter P).card : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.mpr ⟨x, hx⟩).ne'
    rw [div_eq_mul_inv, mul_comm ((S.filter P).card : ℝ≥0∞), mul_assoc,
      ENNReal.mul_inv_cancel hpos (ENNReal.natCast_ne_top _), mul_one]
  · rw [if_neg hx, mul_zero]
    by_cases hP : P x
    · rw [if_pos hP, if_neg (fun hxS => hx (Finset.mem_filter.mpr ⟨hxS, hP⟩))]
    · rw [if_neg hP]

theorem tsum_cell_mul (S : Finset X) (x : X) : (∑' y, cell S y) * cell S x = cell S x := by
  by_cases hS : S.Nonempty
  · rw [cell, dif_pos hS]
    simp only [SPMF.liftM_apply, PMF.tsum_coe, one_mul]
  · rw [cell_apply, if_neg (fun hx => hS ⟨x, hx⟩), mul_zero]

/-- The marginal law of `f` under the uniform law on `S`. -/
noncomputable def margOf (S : Finset X) {V : Type} (f : X → V) : SPMF V := cell S >>= fun x => pure (f x)

/-- The elements of `S` on which `f` takes the value `v`. -/
noncomputable def margFilter (S : Finset X) {V : Type} (f : X → V) (v : V) : Finset X := S.filter fun x => f x = v

theorem mem_margFilter (S : Finset X) {V : Type} (f : X → V) (v : V) (x : X) :
    x ∈ margFilter S f v ↔ x ∈ S ∧ f x = v := by
  rw [margFilter, Finset.mem_filter]

theorem margOf_apply (S : Finset X) {V : Type} (f : X → V) (v : V) :
    margOf S f v = ((margFilter S f v).card / S.card : ℝ≥0∞) * ∑' y, cell (margFilter S f v) y := by
  rw [margOf, SPMF.bind_apply_eq_tsum, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro y
  rw [margFilter, ← cell_guard S (fun x => f x = v) y, SPMF.pure_apply]
  by_cases h : f y = v
  · rw [if_pos h.symm, if_pos h, mul_one]
  · rw [if_neg (Ne.symm h), if_neg h, mul_zero]

theorem margOf_mass (S : Finset X) {V : Type} (f : X → V) (v : V) (x : X) :
    margOf S f v * cell (margFilter S f v) x = if f x = v then cell S x else 0 := by
  rw [margOf_apply, mul_assoc, tsum_cell_mul, cell_guard S (fun x => f x = v) x, margFilter]

/-- Conditioning identity: observe `f x`, then sample from the filtered uniform law. -/
theorem bind_margOf {V Result : Type} (S : Finset X) (f : X → V) (next : V → X → SPMF Result) :
    (cell S >>= fun x => next (f x) x) =
      (margOf S f >>= fun v => cell (margFilter S f v) >>= next v) := by
  apply SPMF.ext
  intro result
  simp only [SPMF.bind_apply_eq_tsum, ← ENNReal.tsum_mul_left, ← mul_assoc, margOf_mass, ite_mul, zero_mul]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro x
  rw [tsum_eq_single (f x)]
  · simp only [if_true]
  · intro v hv
    rw [if_neg (Ne.symm hv)]

theorem margOf_nonempty (S : Finset X) {V : Type} (f : X → V) (v : V) (h : margOf S f v ≠ 0) :
    (margFilter S f v).Nonempty := by
  by_contra hn
  rw [margOf_apply, Finset.not_nonempty_iff_eq_empty.mp hn, Finset.card_empty, Nat.cast_zero,
    ENNReal.zero_div, zero_mul] at h
  exact h rfl

/-- Bayes for an observation whose likelihood is an indicator times a common weight. -/
theorem bind_cell_observe {Answer Result : Type} (S : Finset X) (hS : S.Nonempty) (resp : X → SPMF Answer)
    (keepP : Answer → X → Prop) (u : Answer → ℝ≥0∞) (hresp : ∀ x a, resp x a = if keepP a x then u a else 0)
    (stopped : SPMF Result) (next : Answer → X → SPMF Result) :
    (cell S >>= fun x => observe (resp x) stopped (fun a => next a x)) =
      observe (cell S >>= resp) stopped (fun a => cell (S.filter (keepP a)) >>= next a) := by
  have hcell : cell S = (liftM (PMF.uniformOfFinset S hS) : SPMF X) := by rw [cell, dif_pos hS]
  have h := posterior_observe (PMF.uniformOfFinset S hS) resp (cell S >>= resp) (fun a => cell (S.filter (keepP a)))
    (by rw [hcell])
    (fun a x => by
      rw [← SPMF.liftM_apply, ← hcell, hresp, SPMF.bind_apply_eq_tsum]
      have hsum : (∑' y, cell S y * resp y a) = u a * ((S.filter (keepP a)).card / S.card : ℝ≥0∞) *
          ∑' y, cell (S.filter (keepP a)) y := by
        rw [mul_assoc, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
        apply tsum_congr
        intro y
        rw [hresp, ← cell_guard S (keepP a) y]
        split_ifs <;> simp only [mul_comm, mul_zero, zero_mul]
      rw [hsum, mul_assoc, mul_assoc, tsum_cell_mul, ← cell_guard S (keepP a) x]
      split_ifs <;> simp only [mul_comm, mul_zero, zero_mul])
    stopped next
  rw [← hcell] at h
  exact h

end Cell
end ClaudeWCT.W9.T3.Security.FamResidual
end

section
namespace ClaudeWCT.W9.T3.Security.FamResidual
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
open SigGolfCandidate.T3.Security.LargeResidual (Digest HashOutput low Hit Probe response response_apply Charge
  Request ResidualSpec World Counters State readState probeState stoppedState disclosedState tickState runWith
  runWith_pure runWith_query_bind retain mem_restrict)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

section Effective
variable {Coord : Type} [Seeds Coord] [Fintype Coord]

/-- The seed coordinates of family `f`. -/
@[irreducible] noncomputable def famSeeds (f : Seeds.Fam Coord) : Finset Coord :=
  Finset.univ.filter fun c => ∃ pt, Seeds.split c = .inr (f, pt)

/-- The seeds of family `f` with a singleton candidate set (disclosed). -/
noncomputable def famKnown (cand : Coord → Finset Digest) (f : Seeds.Fam Coord) : Finset Coord :=
  (famSeeds f).filter fun c => (cand c).card = 1

theorem mem_famSeeds (f : Seeds.Fam Coord) (c : Coord) : c ∈ famSeeds f ↔ ∃ pt, Seeds.split c = .inr (f, pt) := by
  unfold famSeeds
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_famKnown (cand : Coord → Finset Digest) (f : Seeds.Fam Coord) (c : Coord) :
    c ∈ famKnown cand f ↔ (∃ pt, Seeds.split c = .inr (f, pt)) ∧ (cand c).card = 1 := by
  rw [famKnown, Finset.mem_filter, mem_famSeeds]

/-- A guess `g` is kept by a probe with hit `hit` when its coordinate is still uncertain, differs from the hit's
parent, and, for a seed, its family is undetermined (at most `deg` disclosed seeds) and the hit is not a seed. -/
def Adm (cand : Coord → Finset Digest) (hit : Hit Coord) (g : Coord × Digest) : Prop :=
  2 ≤ (cand g.1).card ∧ (∀ parent, hit = Hit.label parent → g.1 ≠ parent) ∧
    ∀ fp, Seeds.split g.1 = .inr fp → (famKnown cand fp.1).card ≤ Seeds.deg fp.1 ∧
      ∀ parent, hit = Hit.label parent → ∀ fp', Seeds.split parent ≠ .inr fp'

end Effective

/-- The effective probe of the family engine: the guess is dropped unless `Adm`. -/
noncomputable def _root_.SigGolfCandidate.T3.Security.LargeResidual.Probe.effF {Coord : Type} [Seeds Coord]
    [Fintype Coord] (cand : Coord → Finset Digest) (probe : Probe Coord) : Probe Coord :=
  ⟨if probe.hit.isSelected then none else probe.guess.filter (fun g => decide (Adm cand probe.hit g)), probe.hit⟩

section Laws
variable {Coord : Type} [Seeds Coord] [Fintype Coord] [DecidableEq Coord]

/-- The predictive law of a probe answer. -/
noncomputable def lazyResp (cand : Coord → Finset Digest) (probe : Probe Coord) : SPMF HashOutput :=
  cell (supp cand) >>= fun x => response (view x) probe

/-- The posterior marginal of coordinate `c`. -/
noncomputable def discLaw (cand : Coord → Finset Digest) (c : Coord) : SPMF Digest :=
  margOf (supp cand) fun x => view x c

theorem supp_disclose (cand : Coord → Finset Digest) (c : Coord) (v : Digest) (hv : v ∈ cand c) :
    supp (discloseTableValue cand c v) = margFilter (supp cand) (fun x => view x c) v := by
  ext x
  simp only [mem_supp, mem_margFilter]
  constructor
  · intro h
    have hc := h c
    simp only [discloseTableValue, Function.update_self, Finset.mem_singleton] at hc
    refine ⟨fun c' => ?_, hc⟩
    by_cases hc' : c' = c
    · subst hc'; rw [hc]; exact hv
    · simpa only [discloseTableValue, Function.update_of_ne hc'] using h c'
  · rintro ⟨h, hc⟩ c'
    by_cases hc' : c' = c
    · subst hc'; simp only [discloseTableValue, Function.update_self, Finset.mem_singleton]; exact hc
    · simpa only [discloseTableValue, Function.update_of_ne hc'] using h c'

theorem discLaw_mem (cand : Coord → Finset Digest) (c : Coord) (v : Digest) (h : discLaw cand c v ≠ 0) :
    v ∈ cand c ∧ (supp (discloseTableValue cand c v)).Nonempty := by
  obtain ⟨x, hx⟩ := margOf_nonempty _ _ v h
  have hx' := (mem_margFilter _ _ _ _).mp hx
  have hv : v ∈ cand c := by rw [← hx'.2]; exact (mem_supp cand x).mp hx'.1 c
  exact ⟨hv, by rw [supp_disclose cand c v hv]; exact ⟨x, hx⟩⟩

theorem supp_probeRestrict (cand : Coord → Finset Digest) (probe : Probe Coord) (answer : HashOutput) :
    supp (probe.restrict cand answer) =
      (supp cand).filter fun x => probe.guessMiss (view x) ∧ probe.hit.labelMiss (view x) (probe.hit.answerValue answer) := by
  ext x
  simp only [mem_supp, Finset.mem_filter]
  exact mem_restrict probe cand answer (view x)

theorem lazyResp_nonempty (cand : Coord → Finset Digest) (probe : Probe Coord) (answer : HashOutput)
    (h : lazyResp cand probe answer ≠ 0) :
    probe.hit.answerOk (probe.hit.answerValue answer) ∧ (supp (probe.restrict cand answer)).Nonempty := by
  rw [lazyResp, SPMF.bind_apply_eq_tsum] at h
  obtain ⟨x, hx⟩ : ∃ x, cell (supp cand) x * response (view x) probe answer ≠ 0 := by
    by_contra hn
    push Not at hn
    exact h (ENNReal.tsum_eq_zero.mpr hn)
  have h1 : cell (supp cand) x ≠ 0 := left_ne_zero_of_mul hx
  have h2 : response (view x) probe answer ≠ 0 := right_ne_zero_of_mul hx
  rw [cell_apply] at h1
  have hxs : x ∈ supp cand := by by_contra hn; exact h1 (if_neg hn)
  rw [response_apply] at h2
  have hk : probe.keep (view x) answer := by by_contra hn; exact h2 (if_neg hn)
  have hm := (Hit.miss_iff _ _ _).mp hk.2
  refine ⟨hm.2, x, ?_⟩
  rw [supp_probeRestrict, Finset.mem_filter]
  exact ⟨hxs, hk.1, hm.1⟩

end Laws

section World
variable {Coord Cell AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Seeds Coord] [Fintype Coord] [DecidableEq Coord] [Fintype Cell] [DecidableEq Cell]

/-- Observed run of the family engine: labels and table fixed, probes stop when the effective probe hits. -/
noncomputable def observedImpl (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat)
    (labels : Coord → Digest) (table : Cell → HashOutput) :
    QueryImpl (World auxSpec Coord Cell) (OptionT (StateT (State Coord Cell) SPMF))
  | .inl input => OptionT.mk <| StateT.mk fun state =>
      (liftM (aux input) : SPMF _) >>= fun answer => pure (some answer, state)
  | .inr (.read row charge) => OptionT.mk <| StateT.mk fun state =>
      pure (some (table row), readState q state row (table row) charge)
  | .inr (.probe row test) => OptionT.mk <| StateT.mk fun state =>
      match state.rows row with
      | some answer => pure (some answer, readState q state row answer .call)
      | none => if (test.effF state.candidates).keep labels (table row) then
          pure (some (table row), probeState state row (test.effF state.candidates) (table row))
        else pure (none, stoppedState state)
  | .inr (.disclose coord charge) => OptionT.mk <| StateT.mk fun state =>
      pure (some (labels coord), disclosedState q state coord (labels coord) charge)
  | .inr (.tick charge) => OptionT.mk <| StateT.mk fun state =>
      pure (some (), tickState q state charge)

/-- Lazy run of the family engine: posterior predictive answers and marginals. -/
noncomputable def lazyImpl (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat) :
    QueryImpl (World auxSpec Coord Cell) (OptionT (StateT (State Coord Cell) SPMF))
  | .inl input => OptionT.mk <| StateT.mk fun state =>
      (liftM (aux input) : SPMF _) >>= fun answer => pure (some answer, state)
  | .inr (.read row charge) => OptionT.mk <| StateT.mk fun state =>
      reply state.rows row >>= fun answer => pure (some answer, readState q state row answer charge)
  | .inr (.probe row test) => OptionT.mk <| StateT.mk fun state =>
      match state.rows row with
      | some answer => pure (some answer, readState q state row answer .call)
      | none => observe (lazyResp state.candidates (test.effF state.candidates))
          (pure (none, stoppedState state))
          (fun answer => pure (some answer, probeState state row (test.effF state.candidates) answer))
  | .inr (.disclose coord charge) => OptionT.mk <| StateT.mk fun state =>
      discLaw state.candidates coord >>= fun value => pure (some value, disclosedState q state coord value charge)
  | .inr (.tick charge) => OptionT.mk <| StateT.mk fun state =>
      pure (some (), tickState q state charge)

noncomputable def observedRun {Result : Type} (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat)
    (labels : Coord → Digest) (table : Cell → HashOutput)
    (computation : OracleComp (World auxSpec Coord Cell) Result) (state : State Coord Cell) :=
  runWith (observedImpl aux q labels table) computation state

noncomputable def lazyRun {Result : Type} (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat)
    (computation : OracleComp (World auxSpec Coord Cell) Result) (state : State Coord Cell) :=
  runWith (lazyImpl aux q) computation state

/-- Completion of a finished lazy run: hidden object from the posterior, then the residual rows. -/
noncomputable def finish {Result : Type} (result : Option Result × State Coord Cell) :
    SPMF (Option ((Coord → Digest) × (Cell → HashOutput) × Result) × State Coord Cell) :=
  match result.1 with
  | none => pure (none, result.2)
  | some value => cell (supp result.2.candidates) >>= fun x =>
      completeRows result.2.rows >>= fun table => pure (some (view x, table, value), result.2)

private theorem bind_if {A B : Type} (p : Prop) [Decidable p] (left right : SPMF A) (next : A → SPMF B) :
    ((if p then left else right) >>= next) = if p then left >>= next else right >>= next := by
  split <;> rfl
private theorem map_if {A B : Type} (p : Prop) [Decidable p] (left right : SPMF A) (f : A → B) :
    f <$> (if p then left else right) = if p then f <$> left else f <$> right := by
  split <;> rfl
omit [Seeds Coord] [Fintype Coord] [DecidableEq Coord] in
private theorem observe_response_eq (labels : Coord → Digest) (probe : Probe Coord) {Result : Type}
    (stopped : SPMF Result) (next : HashOutput → SPMF Result) :
    observe (response labels probe) stopped next =
      ((liftM (PMF.uniformOfFintype HashOutput) : SPMF _) >>= fun answer =>
        if probe.keep labels answer then next answer else stopped) := by
  rw [observe, response, toPMF_bind_lift]
  simp only [← PMF.monad_bind_eq_bind, evalSPMF_bind, bind_assoc]
  apply congrArg ((liftM (PMF.uniformOfFintype HashOutput) : SPMF _) >>= ·)
  funext answer
  by_cases h : probe.keep labels answer
  · simp only [h, if_true, SPMF.toPMF_pure, SPMF.lift_pure, pure_bind]
  · simp only [h, if_false, SPMF.toPMF_failure, SPMF.lift_pure, pure_bind]
omit [Seeds Coord] [Fintype Coord] [DecidableEq Coord] in
private theorem fixedLabels_fresh (labels : Coord → Digest) (cache : ResidualTableCompletion.Cache Cell) (input : Cell)
    (hfresh : cache input = none) (probe : Probe Coord) {Result : Type} (stopped : SPMF Result)
    (next : HashOutput → (Cell → HashOutput) → SPMF Result) :
    (completeRows cache >>= fun table =>
      if probe.keep labels (table input) then next (table input) table else stopped) =
        observe (response labels probe) stopped
          (fun answer => completeRows (Function.update cache input (some answer)) >>= next answer) := by
  rw [bind_fresh cache input hfresh (fun answer table => if probe.keep labels answer then next answer table else stopped),
    observe_response_eq]
  apply congrArg ((liftM (PMF.uniformOfFintype HashOutput) : SPMF _) >>= ·)
  funext answer
  by_cases h : probe.keep labels answer
  · simp only [h, if_true]
  · simp only [h, if_false, completeRows_bind_const]

private theorem bind_fresh_probe (cand : Coord → Finset Digest) (hS : (supp cand).Nonempty)
    (cache : ResidualTableCompletion.Cache Cell) (input : Cell)
    (hfresh : cache input = none) (probe : Probe Coord) {Result : Type} (stopped : SPMF Result)
    (next : HashOutput → Hid Coord → (Cell → HashOutput) → SPMF Result) :
    (cell (supp cand) >>= fun x => completeRows cache >>= fun table =>
      if probe.keep (view x) (table input) then next (table input) x table else stopped) =
        observe (lazyResp cand probe) stopped (fun answer =>
          cell (supp (probe.restrict cand answer)) >>= fun x =>
            completeRows (Function.update cache input (some answer)) >>= next answer x) := by
  have hfixed (x : Hid Coord) := fixedLabels_fresh (view x) cache input hfresh probe stopped
    (fun answer table => next answer x table)
  simp_rw [hfixed]
  rw [bind_cell_observe (supp cand) hS (fun x => response (view x) probe) (fun a x => probe.keep (view x) a)
    (fun a => PMF.uniformOfFintype HashOutput a) (fun x a => response_apply (view x) probe a) stopped
    (fun answer x => completeRows (Function.update cache input (some answer)) >>= next answer x)]
  apply observe_congr
  intro answer hanswer
  obtain ⟨hok, -⟩ := lazyResp_nonempty cand probe answer hanswer
  rw [supp_probeRestrict]
  congr 2
  ext x
  simp only [Probe.keep, Hit.miss_iff, hok, and_true]

theorem run_posterior {Result : Type} (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat)
    (computation : OracleComp (World auxSpec Coord Cell) Result) (state : State Coord Cell)
    (ha : (supp state.candidates).Nonempty) :
    (cell (supp state.candidates) >>= fun x => completeRows state.rows >>= fun table =>
      retain (view x) table <$> observedRun aux q (view x) table computation state) =
        (lazyRun aux q computation state >>= finish) := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure result =>
      simp only [observedRun, lazyRun, runWith_pure, map_pure, pure_bind, retain, Option.map_some, finish]
  | query_bind input next ih =>
      cases input with
      | inl input =>
          simp only [observedRun, lazyRun, runWith_query_bind, observedImpl, lazyImpl, OptionT.run_mk,
            StateT.run_mk, bind_assoc, pure_bind, map_bind, Option.elim_some]
          conv_lhs => enter [2, labels]; rw [RetainedObservation.bind_comm]
          rw [RetainedObservation.bind_comm]
          apply congrArg ((liftM (aux input) : SPMF _) >>= ·)
          funext answer
          exact ih answer state ha
      | inr input =>
          cases input with
          | read row charge =>
              simp only [observedRun, lazyRun, runWith_query_bind, observedImpl, lazyImpl, OptionT.run_mk,
                StateT.run_mk, bind_assoc, pure_bind, Option.elim_some]
              have hread (x : Hid Coord) := bind_read state.rows row
                (fun answer table => retain (view x) table <$>
                  runWith (observedImpl aux q (view x) table) (next answer) (readState q state row answer charge))
              simp_rw [hread]
              rw [RetainedObservation.bind_comm]
              apply congrArg (reply state.rows row >>= ·)
              funext answer
              exact ih answer (readState q state row answer charge) ha
          | probe row test =>
              cases hcache : state.rows row with
              | some answer =>
                  simp only [observedRun, lazyRun, runWith_query_bind, observedImpl, lazyImpl, OptionT.run_mk,
                    StateT.run_mk, hcache, pure_bind, Option.elim_some]
                  have hrows : Function.update state.rows row (some answer) = state.rows := by
                    rw [← hcache, Function.update_eq_self]
                  have h := ih answer (readState q state row answer .call) ha
                  simp only [readState, hrows] at h ⊢
                  exact h
              | none =>
                  change HashOutput → OracleComp (World auxSpec Coord Cell) Result at next
                  dsimp only [OracleSpec.Range, World, ResidualSpec] at ih ⊢
                  simp only [observedRun, lazyRun, runWith_query_bind, observedImpl, lazyImpl, OptionT.run_mk,
                    StateT.run_mk, hcache, observe_bind, pure_bind, Option.elim_none, Option.elim_some, finish]
                  dsimp only [OracleSpec.Range, World, OracleSpec.add_apply_inr, ResidualSpec]
                  simp only [bind_if, pure_bind, Option.elim_none, Option.elim_some, map_if, map_pure, retain,
                    Option.map_none]
                  rw [bind_fresh_probe state.candidates ha state.rows row hcache (test.effF state.candidates)
                    (pure (none, stoppedState state))
                    (fun answer x table => retain (view x) table <$>
                      runWith (observedImpl aux q (view x) table) (next answer)
                        (probeState state row (test.effF state.candidates) answer))]
                  apply observe_congr
                  intro answer hanswer
                  exact ih answer (probeState state row (test.effF state.candidates) answer)
                    (lazyResp_nonempty state.candidates _ answer hanswer).2
          | disclose coord charge =>
              simp only [observedRun, lazyRun, runWith_query_bind, observedImpl, lazyImpl, OptionT.run_mk,
                StateT.run_mk, bind_assoc, pure_bind, Option.elim_some]
              rw [bind_margOf (supp state.candidates) (fun x => view x coord) (fun value x =>
                completeRows state.rows >>= fun table => retain (view x) table <$>
                  runWith (observedImpl aux q (view x) table) (next value)
                    (disclosedState q state coord value charge))]
              apply RetainedObservation.bind_congr
              intro value hvalue
              obtain ⟨hv, hne⟩ := discLaw_mem state.candidates coord value hvalue
              have h := ih value (disclosedState q state coord value charge) hne
              simp only [disclosedState] at h ⊢
              rw [← supp_disclose state.candidates coord value hv]
              exact h
          | tick charge =>
              simp only [observedRun, lazyRun, runWith_query_bind, observedImpl, lazyImpl, OptionT.run_mk,
                StateT.run_mk, pure_bind, Option.elim_some]
              exact ih () (tickState q state charge) ha

end World
end ClaudeWCT.W9.T3.Security.FamResidual
end

section
namespace ClaudeWCT.W9.T3.Security.FamResidual
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete UniformTableCompletion
open SigGolfCandidate.T3.Security.LargeResidual (Digest HashOutput low Hit Probe)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

section Ratio

/-- Updating one factor of a product finset scales its card by the factor's ratio. -/
theorem piFinset_update_card {I : Type} [Fintype I] [DecidableEq I] {α : I → Type} [∀ i, DecidableEq (α i)]
    (B : ∀ i, Finset (α i)) (i₀ : I) (B' : Finset (α i₀)) :
    (Fintype.piFinset (Function.update B i₀ B')).card * (B i₀).card = (Fintype.piFinset B).card * B'.card := by
  rw [Fintype.card_piFinset, Fintype.card_piFinset,
    Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i₀) (fun i => (Function.update B i₀ B' i).card),
    Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i₀) (fun i => (B i).card)]
  have hrest : (∏ i ∈ Finset.univ \ {i₀}, (Function.update B i₀ B' i).card) = ∏ i ∈ Finset.univ \ {i₀}, (B i).card := by
    apply Finset.prod_congr rfl
    intro i hi
    have hne : i ≠ i₀ := by simpa using hi
    rw [Function.update_of_ne hne]
  rw [hrest, Function.update_self]
  ring

theorem natCast_div_eq_of_mul_eq {a b c d : ℕ} (h : a * d = b * c) (hb : b ≠ 0) (hd : d ≠ 0) :
    (a : ℝ≥0∞) / b = c / d := by
  rw [ENNReal.div_eq_div_iff (by exact_mod_cast hd) (ENNReal.natCast_ne_top _) (by exact_mod_cast hb)
    (ENNReal.natCast_ne_top _)]
  exact_mod_cast (by rw [mul_comm, h, mul_comm] : d * a = b * c)

variable {X : Type} [DecidableEq X]

theorem probEvent_uniformOfFinset_le (S : Finset X) (hS : S.Nonempty) (P : X → Prop) :
    Pr[P | PMF.uniformOfFinset S hS] ≤ ((S.filter P).card : ℝ≥0∞) / S.card := by
  have hcell : ∀ x, PMF.uniformOfFinset S hS x = cell S x := by
    intro x
    rw [cell, dif_pos hS, SPMF.liftM_apply]
  rw [probEvent_eq_tsum_ite]
  simp only [PMF.probOutput_eq_apply, hcell]
  calc
    _ = ∑' x, ((S.filter P).card / S.card : ℝ≥0∞) * cell (S.filter P) x := by
      apply tsum_congr
      intro x
      exact cell_guard S P x
    _ = ((S.filter P).card / S.card : ℝ≥0∞) * ∑' x, cell (S.filter P) x := ENNReal.tsum_mul_left
    _ ≤ ((S.filter P).card / S.card : ℝ≥0∞) * 1 := by
      gcongr
      by_cases hn : (S.filter P).Nonempty
      · rw [cell, dif_pos hn]
        simp only [SPMF.liftM_apply, PMF.tsum_coe, le_refl]
      · rw [cell, dif_neg hn]
        simp only [SPMF.failure_apply, tsum_zero, zero_le]
    _ = _ := mul_one _

end Ratio

section Product
variable {Coord : Type} [Seeds Coord] [Fintype Coord] [DecidableEq Coord]

/-- The plain part of the candidate box. -/
def plainBox (cand : Coord → Finset Digest) : Seeds.Plain Coord → Finset Digest := fun p => cand (Seeds.embed p)

/-- The family posteriors: coefficient vectors whose seeds lie in the candidate sets. -/
@[irreducible] noncomputable def famSet (cand : Coord → Finset Digest) :
    (f : Seeds.Fam Coord) → Finset (Coefs (Seeds.deg f)) := fun f =>
  Finset.univ.filter fun K => ∀ c pt, Seeds.split c = .inr (f, pt) → ev K pt ∈ cand c

theorem mem_famSet (cand : Coord → Finset Digest) (f : Seeds.Fam Coord) (K : Coefs (Seeds.deg f)) :
    K ∈ famSet cand f ↔ ∀ c pt, Seeds.split c = .inr (f, pt) → ev K pt ∈ cand c := by
  unfold famSet
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem view_embed (x : Hid Coord) (p : Seeds.Plain Coord) : view x (Seeds.embed p) = x.1 p := by
  unfold view
  rw [Seeds.split_embed]

theorem view_seed (x : Hid Coord) {c : Coord} {f : Seeds.Fam Coord} {pt : ℕ} (h : Seeds.split c = .inr (f, pt)) :
    view x c = ev (x.2 f) pt := by
  unfold view
  rw [h]

theorem mem_supp_iff_prod (cand : Coord → Finset Digest) (x : Hid Coord) :
    x ∈ supp cand ↔ (∀ p, x.1 p ∈ plainBox cand p) ∧ ∀ f, x.2 f ∈ famSet cand f := by
  rw [mem_supp]
  constructor
  · intro h
    refine ⟨fun p => ?_, fun f => (mem_famSet cand f (x.2 f)).mpr fun c pt hc => ?_⟩
    · have := h (Seeds.embed p)
      rwa [view_embed] at this
    · have := h c
      rwa [view_seed x hc] at this
  · rintro ⟨h1, h2⟩ c
    cases hc : Seeds.split c with
    | inl p =>
        have := h1 p
        rw [plainBox, Seeds.embed_of_split c p hc] at this
        unfold view
        rw [hc]
        exact this
    | inr fp =>
        rw [view_seed x (show Seeds.split c = .inr (fp.1, fp.2) from hc)]
        exact (mem_famSet cand fp.1 (x.2 fp.1)).mp (h2 fp.1) c fp.2 hc

theorem supp_eq_prod (cand : Coord → Finset Digest) :
    supp cand = Fintype.piFinset (plainBox cand) ×ˢ Fintype.piFinset (famSet cand) := by
  ext x
  rw [mem_supp_iff_prod, Finset.mem_product, Fintype.mem_piFinset, Fintype.mem_piFinset]

/-- Ratio of a seed observation: the family posterior ratio. -/
theorem seed_ratio (cand : Coord → Finset Digest) (hS : (supp cand).Nonempty) {c : Coord} {f : Seeds.Fam Coord}
    {pt : ℕ} (hc : Seeds.split c = .inr (f, pt)) (v : Digest) :
    ((margFilter (supp cand) (fun x => view x c) v).card : ℝ≥0∞) / (supp cand).card =
      (((famSet cand f).filter fun K => ev K pt = v).card : ℝ≥0∞) / (famSet cand f).card := by
  have hfil : margFilter (supp cand) (fun x => view x c) v = Fintype.piFinset (plainBox cand) ×ˢ
      Fintype.piFinset (Function.update (famSet cand) f ((famSet cand f).filter fun K => ev K pt = v)) := by
    ext x
    rw [mem_margFilter, mem_supp_iff_prod, Finset.mem_product, Fintype.mem_piFinset, Fintype.mem_piFinset,
      view_seed x hc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, fun f' => ?_⟩
      by_cases hf : f' = f
      · subst hf; rw [Function.update_self, Finset.mem_filter]; exact ⟨h2 f', h3⟩
      · rw [Function.update_of_ne hf]; exact h2 f'
    · rintro ⟨h1, h2⟩
      have hf := h2 f
      rw [Function.update_self, Finset.mem_filter] at hf
      refine ⟨⟨h1, fun f' => ?_⟩, hf.2⟩
      by_cases hf' : f' = f
      · subst hf'; exact hf.1
      · have := h2 f'; rwa [Function.update_of_ne hf'] at this
  have hS' := hS
  rw [supp_eq_prod] at hS'
  have hcard : (supp cand).card ≠ 0 := Finset.card_ne_zero.mpr hS
  have hB : (famSet cand f).card ≠ 0 := by
    obtain ⟨x, hx⟩ := hS
    exact Finset.card_ne_zero.mpr ⟨x.2 f, ((mem_supp_iff_prod cand x).mp hx).2 f⟩
  apply natCast_div_eq_of_mul_eq _ hcard hB
  rw [hfil, supp_eq_prod, Finset.card_product, Finset.card_product, mul_assoc, piFinset_update_card, mul_assoc]

/-- Ratio of a plain observation. -/
theorem plain_ratio (cand : Coord → Finset Digest) (hS : (supp cand).Nonempty) (p : Seeds.Plain Coord) (v : Digest) :
    ((margFilter (supp cand) (fun x => view x (Seeds.embed p)) v).card : ℝ≥0∞) / (supp cand).card ≤
      ((cand (Seeds.embed p)).card : ℝ≥0∞)⁻¹ := by
  have hfil : margFilter (supp cand) (fun x => view x (Seeds.embed p)) v = Fintype.piFinset
      (Function.update (plainBox cand) p ((plainBox cand p).filter fun w => w = v)) ×ˢ
      Fintype.piFinset (famSet cand) := by
    ext x
    rw [mem_margFilter, mem_supp_iff_prod, Finset.mem_product, Fintype.mem_piFinset, Fintype.mem_piFinset,
      view_embed]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨fun p' => ?_, h2⟩
      by_cases hp : p' = p
      · subst hp; rw [Function.update_self, Finset.mem_filter]; exact ⟨h1 p', h3⟩
      · rw [Function.update_of_ne hp]; exact h1 p'
    · rintro ⟨h1, h2⟩
      have hp := h1 p
      rw [Function.update_self, Finset.mem_filter] at hp
      refine ⟨⟨fun p' => ?_, h2⟩, hp.2⟩
      by_cases hp' : p' = p
      · subst hp'; exact hp.1
      · have := h1 p'; rwa [Function.update_of_ne hp'] at this
  have hcard : (supp cand).card ≠ 0 := Finset.card_ne_zero.mpr hS
  have hA : (plainBox cand p).card ≠ 0 := by
    obtain ⟨x, hx⟩ := hS
    exact Finset.card_ne_zero.mpr ⟨x.1 p, ((mem_supp_iff_prod cand x).mp hx).1 p⟩
  have heq : ((margFilter (supp cand) (fun x => view x (Seeds.embed p)) v).card : ℝ≥0∞) / (supp cand).card =
      (((plainBox cand p).filter fun w => w = v).card : ℝ≥0∞) / (plainBox cand p).card := by
    apply natCast_div_eq_of_mul_eq _ hcard hA
    rw [hfil, supp_eq_prod, Finset.card_product, Finset.card_product, mul_comm (Fintype.piFinset _).card,
      mul_assoc, piFinset_update_card]
    ring
  rw [heq, div_eq_mul_inv]
  have h1 : (((plainBox cand p).filter fun w => w = v).card : ℝ≥0∞) ≤ 1 := by
    have : ((plainBox cand p).filter fun w => w = v).card ≤ 1 :=
      Finset.card_le_one.mpr fun a ha b hb => by
        rw [Finset.mem_filter] at ha hb; rw [ha.2, hb.2]
    exact_mod_cast this
  calc _ ≤ 1 * ((plainBox cand p).card : ℝ≥0∞)⁻¹ := by gcongr
    _ = _ := one_mul _

end Product
end ClaudeWCT.W9.T3.Security.FamResidual
end

section
namespace ClaudeWCT.W9.T3.Security.FamResidual
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete UniformTableCompletion
open SigGolfCandidate.T3.Security.LargeResidual (Digest HashOutput low Hit Probe response hit_miss_prob)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

section Posterior
variable {Coord : Type} [Seeds Coord] [Fintype Coord] [DecidableEq Coord]

/-- The evaluation point of a seed coordinate. -/
def ptOf (c : Coord) : ℕ :=
  match Seeds.split c with
  | .inr fp => fp.2
  | .inl _ => 0

theorem ptOf_seed {c : Coord} {f : Seeds.Fam Coord} {pt : ℕ} (h : Seeds.split c = .inr (f, pt)) : ptOf c = pt := by
  unfold ptOf; rw [h]


/-- Disclosed `(point, value)` pairs of family `f`. -/
noncomputable def famKnownPairs (cand : Coord → Finset Digest) (f : Seeds.Fam Coord) : Finset (ℕ × Digest) :=
  (famKnown cand f).biUnion fun c => (cand c).image fun v => (ptOf c, v)

/-- Excluded `(point, value)` pairs of the undisclosed seeds of family `f`. -/
noncomputable def famMissPairs (cand : Coord → Finset Digest) (f : Seeds.Fam Coord) : Finset (ℕ × Digest) :=
  ((famSeeds f).filter fun c => (cand c).card ≠ 1).biUnion fun c => (Finset.univ \ cand c).image fun v => (ptOf c, v)

/-- Values excluded from the undisclosed seeds of family `f` (the failed guesses charged to the family). -/
noncomputable def famDebt (cand : Coord → Finset Digest) (f : Seeds.Fam Coord) : ℕ :=
  ∑ c ∈ (famSeeds f).filter (fun c => (cand c).card ≠ 1), (2 ^ 128 - (cand c).card)

theorem famSet_eq_famPost (cand : Coord → Finset Digest) (f : Seeds.Fam Coord) :
    famSet cand f = ClaudeWCT.Arith.famPost (m := Seeds.deg f) (famKnownPairs cand f) (famMissPairs cand f) := by
  ext K
  rw [mem_famSet]
  unfold ClaudeWCT.Arith.famPost ClaudeWCT.Arith.famAffine
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    refine ⟨fun p hp => ?_, fun p hp => ?_⟩
    · obtain ⟨c, hc, hp⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨hcs, hc1⟩ := Finset.mem_filter.mp hc
      obtain ⟨pt, hpt⟩ := (mem_famSeeds f c).mp hcs
      obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hc1
      have h1 := h c pt hpt
      rw [hw, Finset.mem_singleton] at h1
      rw [hw, Finset.mem_singleton] at hv
      simp only [ptOf_seed hpt]
      rw [hv]
      exact h1
    · obtain ⟨c, hc, hp⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨hcs, -⟩ := Finset.mem_filter.mp hc
      obtain ⟨pt, hpt⟩ := (mem_famSeeds f c).mp hcs
      have h1 := h c pt hpt
      simp only [ptOf_seed hpt]
      intro heq
      apply (Finset.mem_sdiff.mp hv).2
      change ev K pt = v at heq
      rw [← heq]
      exact h1
  · rintro ⟨hk, hm⟩ c pt hc
    have hcs : c ∈ famSeeds f := (mem_famSeeds f c).mpr ⟨pt, hc⟩
    by_cases h1 : (cand c).card = 1
    · obtain ⟨w, hw⟩ := Finset.card_eq_one.mp h1
      have hmem : (pt, w) ∈ famKnownPairs cand f := by
        apply Finset.mem_biUnion.mpr
        refine ⟨c, Finset.mem_filter.mpr ⟨hcs, h1⟩, Finset.mem_image.mpr ⟨w, by rw [hw]; exact Finset.mem_singleton_self w, ?_⟩⟩
        rw [ptOf_seed hc]
      have := hk _ hmem
      rw [hw, Finset.mem_singleton]
      exact this
    · by_contra hn
      have hmem : (pt, ev K pt) ∈ famMissPairs cand f := by
        apply Finset.mem_biUnion.mpr
        refine ⟨c, Finset.mem_filter.mpr ⟨hcs, h1⟩, Finset.mem_image.mpr ⟨ev K pt, ?_, ?_⟩⟩
        · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hn⟩
        · rw [ptOf_seed hc]
      exact hm _ hmem rfl

theorem famKnownPairs_card (cand : Coord → Finset Digest) (f : Seeds.Fam Coord) :
    (famKnownPairs cand f).card ≤ (famKnown cand f).card := by
  refine Finset.card_biUnion_le.trans ?_
  calc _ ≤ ∑ c ∈ famKnown cand f, 1 := by
        apply Finset.sum_le_sum
        intro c hc
        exact Finset.card_image_le.trans (Finset.mem_filter.mp hc).2.le
    _ = _ := by simp

theorem card_digest_univ : (Finset.univ : Finset Digest).card = 2 ^ 128 := by
  rw [Finset.card_univ]
  simp [SphincsSecurity.digestBits]

theorem famMissPairs_card (cand : Coord → Finset Digest) (f : Seeds.Fam Coord) :
    (famMissPairs cand f).card ≤ famDebt cand f := by
  refine Finset.card_biUnion_le.trans ?_
  apply Finset.sum_le_sum
  intro c _
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), card_digest_univ]

theorem famKnownPairs_pt (cand : Coord → Finset Digest) (f : Seeds.Fam Coord) :
    ∀ p ∈ famKnownPairs cand f, ∃ c, (cand c).card = 1 ∧ Seeds.split c = .inr (f, p.1) := by
  intro p hp
  obtain ⟨c, hc, hp⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨hcs, hc1⟩ := Finset.mem_filter.mp hc
  obtain ⟨pt, hpt⟩ := (mem_famSeeds f c).mp hcs
  exact ⟨c, hc1, by rw [ptOf_seed hpt]; exact hpt⟩

theorem famMissPairs_pt (cand : Coord → Finset Digest) (f : Seeds.Fam Coord) :
    ∀ p ∈ famMissPairs cand f, ∃ c, Seeds.split c = .inr (f, p.1) := by
  intro p hp
  obtain ⟨c, hc, hp⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨pt, hpt⟩ := (mem_famSeeds f c).mp (Finset.mem_filter.mp hc).1
  exact ⟨c, by rw [ptOf_seed hpt]; exact hpt⟩

/-- The hazard of an admissible guess: a uniform plain label or an undetermined family seed. -/
theorem guess_ratio_le (cand : Coord → Finset Digest) (hS : (supp cand).Nonempty) (probes : ℕ)
    (hinv : ∀ c, (cand c).card = 1 ∨ 2 ^ 128 - probes ≤ (cand c).card) (hdebt : ∀ f, famDebt cand f ≤ probes)
    (hit : Hit Coord) (g : Coord × Digest) (hadm : Adm cand hit g) :
    ((margFilter (supp cand) (fun x => view x g.1) g.2).card : ℝ≥0∞) / (supp cand).card ≤
      ((2 ^ 128 - probes : ℕ) : ℝ≥0∞)⁻¹ := by
  obtain ⟨h2, -, hseed⟩ := hadm
  have hcard : 2 ^ 128 - probes ≤ (cand g.1).card := by
    rcases hinv g.1 with h | h
    · omega
    · exact h
  cases hsplit : Seeds.split g.1 with
  | inl p =>
      have he : Seeds.embed p = g.1 := Seeds.embed_of_split g.1 p hsplit
      have h := plain_ratio cand hS p g.2
      rw [he] at h
      exact h.trans (ENNReal.inv_le_inv.mpr (by exact_mod_cast hcard))
  | inr fp =>
      obtain ⟨f, pt⟩ := fp
      obtain ⟨hk, -⟩ := hseed (f, pt) hsplit
      rw [seed_ratio cand hS hsplit g.2, famSet_eq_famPost]
      apply ClaudeWCT.Arith.fam_hazard_prob ((famKnownPairs_card cand f).trans hk)
      · intro p hp
        obtain ⟨c, -, hc⟩ := famKnownPairs_pt cand f p hp
        exact Seeds.point_lt c f p.1 hc
      · intro p hp
        obtain ⟨c, hc⟩ := famMissPairs_pt cand f p hp
        exact Seeds.point_lt c f p.1 hc
      · exact Seeds.point_lt g.1 f pt hsplit
      · intro hmem
        obtain ⟨p, hp, hp1⟩ := Finset.mem_image.mp hmem
        obtain ⟨c, hc1, hc⟩ := famKnownPairs_pt cand f p hp
        rw [hp1] at hc
        have := Seeds.seed_inj c g.1 (f, pt) hc hsplit
        rw [this] at hc1
        omega
      · exact (famMissPairs_card cand f).trans (hdebt f)

end Posterior
end ClaudeWCT.W9.T3.Security.FamResidual
end

section
namespace ClaudeWCT.W9.T3.Security.FamResidual
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete UniformTableCompletion RetainedObservation
open SigGolfCandidate.T3.Security.LargeResidual (Digest HashOutput low Hit Probe response hit_miss_prob response_failure)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

section Hazard
variable {Coord : Type} [Seeds Coord] [Fintype Coord] [DecidableEq Coord]

/-- Joint law of the hidden object and a uniform answer. -/
noncomputable def lawF (S : Finset (Hid Coord)) (hS : S.Nonempty) : PMF (Hid Coord × HashOutput) :=
  (PMF.uniformOfFinset S hS).bind fun x => (PMF.uniformOfFintype HashOutput).map fun answer => (x, answer)

theorem lazyResp_failure (cand : Coord → Finset Digest) (hS : (supp cand).Nonempty) (probe : Probe Coord) :
    (lazyResp cand probe).toPMF none = Pr[fun z => ¬probe.keep (view z.1) z.2 | lawF (supp cand) hS] := by
  rw [lazyResp, cell, dif_pos hS, toPMF_bind_lift, PMF.bind_apply]
  change _ = Pr[fun z => ¬probe.keep (view z.1) z.2 |
    (PMF.uniformOfFinset (supp cand) hS) >>= fun x => (fun answer => (x, answer)) <$> PMF.uniformOfFintype HashOutput]
  rw [probEvent_bind_eq_tsum]
  simp only [PMF.probOutput_eq_apply, probEvent_map]
  apply tsum_congr
  intro x
  rw [response_failure]
  rfl

theorem keep_probF (S : Finset (Hid Coord)) (hS : S.Nonempty) (probe : Probe Coord)
    (hsel : probe.hit.isSelected = false) :
    Pr[fun z => probe.keep (view z.1) z.2 | lawF S hS] =
      Pr[fun x => probe.guessMiss (view x) | PMF.uniformOfFinset S hS] * (1 - (Fintype.card Digest : ENNReal)⁻¹) := by
  change Pr[fun z => probe.keep (view z.1) z.2 |
    (PMF.uniformOfFinset S hS) >>= fun x => (fun answer => (x, answer)) <$> PMF.uniformOfFintype HashOutput] = _
  rw [probEvent_bind_eq_tsum]
  have hinner (x : Hid Coord) :
      Pr[(fun z : Hid Coord × HashOutput => probe.keep (view z.1) z.2) ∘ (fun answer => (x, answer)) |
        PMF.uniformOfFintype HashOutput] =
      if probe.guessMiss (view x) then 1 - (Fintype.card Digest : ENNReal)⁻¹ else 0 := by
    by_cases hg : probe.guessMiss (view x)
    · rw [if_pos hg, ← hit_miss_prob probe.hit (view x)]
      have he : ((fun z : Hid Coord × HashOutput => probe.keep (view z.1) z.2) ∘ (fun answer => (x, answer))) =
          (fun answer => probe.hit.miss (view x) (low answer)) := by
        funext answer
        simp only [Function.comp_def, Probe.keep, hg, true_and, Hit.answerValue_of_not_selected _ hsel]
      rw [he]
    · rw [if_neg hg]
      have he : ((fun z : Hid Coord × HashOutput => probe.keep (view z.1) z.2) ∘ (fun answer => (x, answer))) =
          (fun _ => False) := by
        funext answer
        simp only [Function.comp_def, Probe.keep, hg, false_and]
      rw [he, probEvent_eq_tsum_ite]
      simp
  simp only [probEvent_map, hinner, PMF.probOutput_eq_apply, mul_ite, mul_zero]
  rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
  simp only [PMF.probOutput_eq_apply, ite_mul, zero_mul]

/-- A target selected from either half misses whenever both halves miss. -/
theorem keep_selected_prob_geF (S : Finset (Hid Coord)) (hS : S.Nonempty) (probe : Probe Coord)
    (hsel : probe.hit.isSelected = true) (hguess : probe.guess = none) :
    (1 - (Fintype.card Digest : ENNReal)⁻¹) ^ 2 ≤
      Pr[fun z => probe.keep (view z.1) z.2 | lawF S hS] := by
  obtain ⟨guess, hit⟩ := probe
  change guess = none at hguess
  subst guess
  cases hit with
  | label parent => simp [Hit.isSelected] at hsel
  | target target => simp [Hit.isSelected] at hsel
  | selectedTarget target pickLow =>
      have hinner (x : Hid Coord) :
          Pr[(fun z : Hid Coord × HashOutput =>
              (⟨none, .selectedTarget target pickLow⟩ : Probe Coord).keep (view z.1) z.2) ∘
                (fun answer => (x, answer)) | PMF.uniformOfFintype HashOutput] =
            Pr[fun answer => (if pickLow answer then low answer else answer.extractLsb' 128 128) ≠ target |
              PMF.uniformOfFintype HashOutput] := by
        congr 1
        funext answer
        simp [Probe.keep, Probe.guessMiss, Hit.miss, Hit.answerValue, ne_comm]
      change _ ≤ Pr[fun z => (⟨none, .selectedTarget target pickLow⟩ : Probe Coord).keep (view z.1) z.2 |
        (PMF.uniformOfFinset S hS) >>= fun x => (fun answer => (x, answer)) <$> PMF.uniformOfFintype HashOutput]
      rw [probEvent_bind_eq_tsum]
      simp only [probEvent_map, hinner, PMF.probOutput_eq_apply]
      rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
      have hc : (Fintype.card Digest : ENNReal) = (2 : ENNReal) ^ 128 := by
        rw [show Fintype.card Digest = (2 : Nat) ^ 128 from Fintype.card_bitVec 128,
          Nat.cast_pow, Nat.cast_ofNat]
      rw [hc]
      have h := SigGolfCandidate.T3.Security.LargeResidual.probability_pickLow_ne_ge pickLow target
      rw [probEvent_def, evalSPMF_uniformSample] at h
      change (1 - 1 / (2 : ENNReal) ^ 128) ^ 2 ≤
        Pr[fun answer => (if pickLow answer then low answer else answer.extractLsb' 128 128) ≠ target |
          PMF.uniformOfFintype HashOutput] at h
      simpa only [one_div] using h

theorem guessMiss_prob_geF (S : Finset (Hid Coord)) (hS : S.Nonempty) (probe : Probe Coord) (minimum : ENNReal)
    (hmin : ∀ g ∈ probe.guess, Pr[fun x => view x g.1 = g.2 | PMF.uniformOfFinset S hS] ≤ minimum) :
    1 - minimum ≤ Pr[fun x => probe.guessMiss (view x) | PMF.uniformOfFinset S hS] := by
  cases hg : probe.guess with
  | none =>
      have he : (fun x => probe.guessMiss (view x)) = (fun _ => True) := by
        funext x
        simp only [Probe.guessMiss, hg, Option.mem_def, reduceCtorEq, false_implies, implies_true]
      rw [he, probEvent_eq_tsum_ite]
      simp only [if_true, PMF.probOutput_eq_apply, PMF.tsum_coe]
      exact tsub_le_self
  | some g =>
      have hhit := hmin g (by rw [hg]; rfl)
      have hcompl := probEvent_compl (PMF.uniformOfFinset S hS) (fun x => view x g.1 = g.2)
      rw [probFailure_of_liftM_PMF, tsub_zero] at hcompl
      have hmiss : (fun x => probe.guessMiss (view x)) = (fun x => ¬view x g.1 = g.2) := by
        funext x
        simp only [Probe.guessMiss, hg, Option.mem_def, Option.some.injEq, forall_eq', ne_eq]
      rw [hmiss]
      have heq : Pr[fun x => ¬view x g.1 = g.2 | PMF.uniformOfFinset S hS] =
          1 - Pr[fun x => view x g.1 = g.2 | PMF.uniformOfFinset S hS] :=
        ENNReal.eq_sub_of_add_eq' (by simp) (by rw [add_comm]; exact hcompl)
      rw [heq]
      exact tsub_le_tsub_left hhit 1

theorem lazyResp_failure_le_hazard (cand : Coord → Finset Digest) (hS : (supp cand).Nonempty) (probe : Probe Coord)
    (probes : Nat)
    (hmin : ∀ g ∈ probe.guess, Pr[fun x => view x g.1 = g.2 | PMF.uniformOfFinset (supp cand) hS] ≤
      ((2 ^ 128 - probes : Nat) : ENNReal)⁻¹)
    (hselected : probe.hit.isSelected = true → probe.guess = none) :
    (lazyResp cand probe).toPMF none ≤ SigGolfCandidate.T3.Security.LargePotential.hazard (2 ^ 128) probes := by
  rw [lazyResp_failure cand hS probe]
  have hcompl := probEvent_compl (lawF (supp cand) hS) (fun z => probe.keep (view z.1) z.2)
  rw [probFailure_of_liftM_PMF, tsub_zero] at hcompl
  have heq : Pr[fun z => ¬probe.keep (view z.1) z.2 | lawF (supp cand) hS] =
      1 - Pr[fun z => probe.keep (view z.1) z.2 | lawF (supp cand) hS] :=
    ENNReal.eq_sub_of_add_eq' (by simp) (by rw [add_comm]; exact hcompl)
  rw [heq, SigGolfCandidate.T3.Security.LargePotential.hazard]
  apply tsub_le_tsub_left _ 1
  have hcard : (Fintype.card Digest : ENNReal) = ((2 ^ 128 : Nat) : ENNReal) := by
    simp [SphincsSecurity.digestBits]
  have hmiss : 1 - ((2 ^ 128 - probes : Nat) : ENNReal)⁻¹ ≤
      1 - (Fintype.card Digest : ENNReal)⁻¹ := by
    apply tsub_le_tsub_left
    rw [hcard]
    exact ENNReal.inv_le_inv.mpr (by exact_mod_cast Nat.sub_le _ _)
  by_cases hs : probe.hit.isSelected = true
  · exact (pow_le_pow_left' hmiss 2).trans (keep_selected_prob_geF (supp cand) hS probe hs (hselected hs))
  · have hn : probe.hit.isSelected = false := by cases hh : probe.hit.isSelected <;> simp_all
    rw [keep_probF (supp cand) hS probe hn, pow_two]
    exact mul_le_mul' (guessMiss_prob_geF (supp cand) hS probe _ hmin) hmiss

/-- The hazard of an admissible guess as a probability. -/
theorem guess_prob_le (cand : Coord → Finset Digest) (hS : (supp cand).Nonempty) (probes : ℕ)
    (hinv : ∀ c, (cand c).card = 1 ∨ 2 ^ 128 - probes ≤ (cand c).card) (hdebt : ∀ f, famDebt cand f ≤ probes)
    (hit : Hit Coord) (g : Coord × Digest) (hadm : Adm cand hit g) :
    Pr[fun x => view x g.1 = g.2 | PMF.uniformOfFinset (supp cand) hS] ≤ ((2 ^ 128 - probes : Nat) : ENNReal)⁻¹ :=
  (probEvent_uniformOfFinset_le _ hS _).trans (guess_ratio_le cand hS probes hinv hdebt hit g hadm)

end Hazard
end ClaudeWCT.W9.T3.Security.FamResidual
end

section
namespace ClaudeWCT.W9.T3.Security.FamResidual
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
open SigGolfCandidate.T3.Security.LargePotential (Step Charges StepBound FreeStep MassStep ProbeStep hazard)
open SigGolfCandidate.T3.Security.LargeResidual (Digest HashOutput low Hit Probe Charge Request ResidualSpec World
  Counters State readState probeState stoppedState disclosedState tickState runWith runWith_pure runWith_query_bind
  charges initial stop_zero_of_shape support_of_shape stepBound_of_charge observe_stop observe_support
  card_restrict_ge restrict_subset_card restrict_subset)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

section Debt
variable {Coord : Type} [Seeds Coord] [Fintype Coord] [DecidableEq Coord]

theorem famDebt_le_of (cand cand' : Coord → Finset Digest) (f : Seeds.Fam Coord)
    (hsub : ∀ c, cand' c ⊆ cand c) (hne : ∀ c, (cand' c).Nonempty)
    (hdrop : ∀ c, (cand c).card ≤ (cand' c).card + 1)
    (hone : ∀ c ∈ famSeeds f, ∀ c' ∈ famSeeds f, cand' c ≠ cand c → cand' c' ≠ cand c' → c = c') :
    famDebt cand' f ≤ famDebt cand f + 1 := by
  unfold famDebt
  set T := (famSeeds f).filter fun c => (cand c).card ≠ 1
  set T' := (famSeeds f).filter fun c => (cand' c).card ≠ 1
  have hTT : T' ⊆ T := by
    intro c hc
    obtain ⟨hcs, hc1⟩ := Finset.mem_filter.mp hc
    refine Finset.mem_filter.mpr ⟨hcs, fun h1 => hc1 ?_⟩
    have hle := Finset.card_le_card (hsub c)
    have hpos := (hne c).card_pos
    omega
  have hterm : ∀ c ∈ T', 2 ^ 128 - (cand' c).card ≤ (2 ^ 128 - (cand c).card) + (if cand' c = cand c then 0 else 1) := by
    intro c _
    by_cases heq : cand' c = cand c
    · rw [if_pos heq, heq, add_zero]
    · rw [if_neg heq]
      have := hdrop c
      omega
  calc
    _ ≤ ∑ c ∈ T', ((2 ^ 128 - (cand c).card) + (if cand' c = cand c then 0 else 1)) := Finset.sum_le_sum hterm
    _ = ∑ c ∈ T', (2 ^ 128 - (cand c).card) + ∑ c ∈ T', (if cand' c = cand c then 0 else 1) :=
        Finset.sum_add_distrib
    _ ≤ ∑ c ∈ T, (2 ^ 128 - (cand c).card) + 1 := by
        apply add_le_add (Finset.sum_le_sum_of_subset hTT)
        rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul, mul_one]
        apply Finset.card_le_one.mpr
        intro a ha b hb
        obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
        obtain ⟨hb1, hb2⟩ := Finset.mem_filter.mp hb
        exact hone a (Finset.mem_filter.mp ha1).1 b (Finset.mem_filter.mp hb1).1 ha2 hb2

theorem famDebt_disclose_le (cand : Coord → Finset Digest) (c0 : Coord) (v : Digest) (f : Seeds.Fam Coord) :
    famDebt (discloseTableValue cand c0 v) f ≤ famDebt cand f := by
  unfold famDebt
  have hsame : ∀ c ∈ (famSeeds f).filter (fun c => (discloseTableValue cand c0 v c).card ≠ 1),
      discloseTableValue cand c0 v c = cand c := by
    intro c hc
    have hc1 := (Finset.mem_filter.mp hc).2
    have hne : c ≠ c0 := by
      rintro rfl
      simp [discloseTableValue] at hc1
    simp only [discloseTableValue, Function.update_of_ne hne]
  rw [Finset.sum_congr rfl (fun c hc => by rw [hsame c hc])]
  apply Finset.sum_le_sum_of_subset
  intro c hc
  obtain ⟨hcs, hc1⟩ := Finset.mem_filter.mp hc
  refine Finset.mem_filter.mpr ⟨hcs, ?_⟩
  rw [← hsame c hc]
  exact hc1

theorem restrict_eq_of_ne (probe : Probe Coord) (cand : Coord → Finset Digest) (answer : HashOutput) (c : Coord)
    (hg : ∀ g ∈ probe.guess, c ≠ g.1) (hp : ∀ parent, probe.hit = Hit.label parent → c ≠ parent) :
    probe.restrict cand answer c = cand c := by
  have hguess : probe.guessRestrict cand c = cand c := by
    unfold Probe.guessRestrict
    cases hgs : probe.guess with
    | none => rfl
    | some g =>
        simp only [eraseTableValue]
        rw [Function.update_of_ne (hg g (by rw [hgs]; rfl))]
  unfold Probe.restrict
  cases hh : probe.hit with
  | target t => simp only [Hit.restrict]; exact hguess
  | selectedTarget t pick => simp only [Hit.restrict]; exact hguess
  | label parent =>
      simp only [Hit.restrict, eraseTableValue]
      rw [Function.update_of_ne (hp parent hh)]
      exact hguess

theorem famDebt_probe_le (cand : Coord → Finset Digest) (test : Probe Coord) (answer : HashOutput)
    (hne : ∀ c, ((test.effF cand).restrict cand answer c).Nonempty) (f : Seeds.Fam Coord) :
    famDebt ((test.effF cand).restrict cand answer) f ≤ famDebt cand f + 1 := by
  have hadm : ∀ g ∈ (test.effF cand).guess, Adm cand (test.effF cand).hit g := by
    intro g hg
    by_cases hs : test.hit.isSelected = true
    · simp [Probe.effF, hs] at hg
    · simp only [Probe.effF, hs, Bool.false_eq_true, if_false, Option.mem_def,
        Option.filter_eq_some_iff, decide_eq_true_eq] at hg
      exact hg.2
  apply famDebt_le_of cand _ f (restrict_subset _ cand answer) hne
  · intro c
    have := card_restrict_ge (test.effF cand) cand answer (fun g hg => (hadm g hg).2.1) c
    omega
  · have hchanged : ∀ c, (test.effF cand).restrict cand answer c ≠ cand c →
        (∃ g ∈ (test.effF cand).guess, c = g.1) ∨ ∃ parent, (test.effF cand).hit = Hit.label parent ∧ c = parent := by
      intro c hc
      by_contra hn
      push Not at hn
      exact hc (restrict_eq_of_ne _ cand answer c hn.1 hn.2)
    intro c hc c' hc' hch hch'
    obtain ⟨pt, hpt⟩ := (mem_famSeeds f c).mp hc
    obtain ⟨pt', hpt'⟩ := (mem_famSeeds f c').mp hc'
    rcases hchanged c hch with ⟨g, hg, rfl⟩ | ⟨p, hp, rfl⟩ <;>
      rcases hchanged c' hch' with ⟨g', hg', rfl⟩ | ⟨p', hp', rfl⟩
    · rw [Option.mem_def] at hg hg'; rw [hg] at hg'; cases hg'; rfl
    · exact absurd hpt' (((hadm g hg).2.2 _ hpt).2 _ hp' _)
    · exact absurd hpt (((hadm g' hg').2.2 _ hpt').2 _ hp _)
    · rw [hp] at hp'; cases hp'; rfl

end Debt

section Bound
variable {Coord Cell AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Seeds Coord] [Fintype Coord] [DecidableEq Coord] [Fintype Cell] [DecidableEq Cell]

noncomputable def residualStep (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat) :
    Step SPMF (World auxSpec Coord Cell) (State Coord Cell) :=
  fun request state => ((lazyImpl aux q request).run).run state

/-- Invariant of the family engine: a consistent posterior, the T3 per-coordinate bound, and family debts within
the probe count. -/
def Inv (state : State Coord Cell) : Prop :=
  (supp state.candidates).Nonempty ∧
    (∀ c, (state.candidates c).card = 1 ∨ 2 ^ 128 - state.counters.probes ≤ (state.candidates c).card) ∧
    ∀ f, famDebt state.candidates f ≤ state.counters.probes

theorem supp_univ : (supp (fun _ : Coord => (Finset.univ : Finset Digest))) = Finset.univ := by
  ext x
  simp only [mem_supp, Finset.mem_univ, implies_true]

theorem initial_inv : Inv (initial : State Coord Cell) := by
  refine ⟨?_, fun c => Or.inr ?_, fun f => ?_⟩
  · change (supp (fun _ : Coord => (Finset.univ : Finset Digest))).Nonempty
    rw [supp_univ]
    exact Finset.univ_nonempty
  · change 2 ^ 128 - 0 ≤ (Finset.univ : Finset Digest).card
    rw [card_digest_univ]
    omega
  · change famDebt (fun _ : Coord => (Finset.univ : Finset Digest)) f ≤ 0
    unfold famDebt
    simp only [card_digest_univ, Nat.sub_self, Finset.sum_const_zero, le_refl]

theorem run_residual {Result : Type} (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat)
    (program : OracleComp (World auxSpec Coord Cell) Result) (state : State Coord Cell) :
    SigGolfCandidate.T3.Security.LargePotential.run (residualStep aux q) program state = lazyRun aux q program state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => rw [SigGolfCandidate.T3.Security.LargePotential.run_pure, lazyRun, runWith_pure]
  | query_bind input next ih =>
      rw [SigGolfCandidate.T3.Security.LargePotential.run_query_bind, lazyRun, runWith_query_bind]
      apply _root_.bind_congr
      intro middle
      rcases middle with ⟨answer, after⟩
      cases answer with
      | none => rfl
      | some answer => exact ih answer after

theorem effF_adm (cand : Coord → Finset Digest) (test : Probe Coord) :
    ∀ g ∈ (test.effF cand).guess, Adm cand (test.effF cand).hit g := by
  intro g hg
  by_cases hs : test.hit.isSelected = true
  · simp [Probe.effF, hs] at hg
  · simp only [Probe.effF, hs, Bool.false_eq_true, if_false, Option.mem_def,
      Option.filter_eq_some_iff, decide_eq_true_eq] at hg
    exact hg.2

theorem residual_step_bound (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat)
    (input : (World auxSpec Coord Cell).Domain) (state : State Coord Cell) (hinv : Inv state) :
    StepBound (residualStep aux q) charges (2 ^ 128) q input state := by
  cases input with
  | inl input =>
      apply stepBound_of_charge q (residualStep aux q) (.inl input) state .none (liftM (aux input) : SPMF _)
        id (fun _ => state)
      · rfl
      · intro a; rfl
  | inr request =>
      cases request with
      | read row charge =>
          apply stepBound_of_charge q (residualStep aux q) (.inr (.read row charge)) state charge
            (reply state.rows row) id (fun a => readState q state row a charge)
          · rfl
          · intro a; rfl
      | disclose coord charge =>
          apply stepBound_of_charge q (residualStep aux q) (.inr (.disclose coord charge)) state charge
            (discLaw state.candidates coord) id (fun v => disclosedState q state coord v charge)
          · rfl
          · intro a; rfl
      | tick charge =>
          apply stepBound_of_charge q (residualStep aux q) (.inr (.tick charge)) state charge
            (pure ()) id (fun _ => tickState q state charge)
          · change pure (some (), tickState q state charge) = _
            rw [pure_bind]
          · intro a; rfl
      | probe row test =>
          cases hcache : state.rows row with
          | some answer =>
              apply stepBound_of_charge q (residualStep aux q) (.inr (.probe row test)) state .call
                (pure answer) id (fun a => readState q state row a .call)
              · change (match state.rows row with
                  | some answer => pure (some answer, readState q state row answer .call)
                  | none => _) = _
                rw [hcache, pure_bind]
                rfl
              · intro a; rfl
          | none =>
              right; right; right
              have hstep : residualStep aux q (.inr (.probe row test)) state =
                  observe (lazyResp state.candidates (test.effF state.candidates))
                    (pure (none, stoppedState state))
                    (fun answer => pure (some answer, probeState state row (test.effF state.candidates) answer)) := by
                change (match state.rows row with
                  | some answer => pure (some answer, readState q state row answer .call)
                  | none => _) = _
                rw [hcache]
              refine ⟨fun result hresult => ?_, ?_⟩
              · rw [hstep] at hresult
                rcases observe_support _ _ _ result hresult with rfl | ⟨answer, _, rfl⟩
                · simp only [charges, stoppedState, Counters.probe]; omega
                · simp only [charges, probeState, Counters.probe]; omega
              · rw [hstep]
                erw [observe_stop]
                by_cases hp : state.counters.probes < 2 ^ 128
                · exact lazyResp_failure_le_hazard state.candidates hinv.1 _ state.counters.probes
                    (fun g hg => guess_prob_le state.candidates hinv.1 state.counters.probes hinv.2.1 hinv.2.2
                      _ g (effF_adm state.candidates test g hg))
                    (fun hs => by
                      change test.hit.isSelected = true at hs
                      simp [Probe.effF, hs])
                · have hzero : (((2 ^ 128 - state.counters.probes : Nat) : ENNReal))⁻¹ = ⊤ := by
                    rw [show 2 ^ 128 - state.counters.probes = 0 by omega, Nat.cast_zero, ENNReal.inv_zero]
                  have hh : hazard (2 ^ 128) state.counters.probes = 1 := by
                    simp only [SigGolfCandidate.T3.Security.LargePotential.hazard, hzero]
                    simp
                  change _ ≤ hazard (2 ^ 128) state.counters.probes
                  rw [hh]
                  exact PMF.coe_le_one _ _

theorem support_of_shape' {X R : Type} (p : SPMF X) (g : X → R) (f : X → State Coord Cell)
    (result : Option R × State Coord Cell) (hresult : result ∈ support (p >>= fun a => pure (some (g a), f a))) :
    ∃ a, p a ≠ 0 ∧ result = (some (g a), f a) := by
  rw [mem_support_bind_iff] at hresult
  obtain ⟨a, ha, hr⟩ := hresult
  rw [mem_support_pure_iff] at hr
  refine ⟨a, ?_, hr⟩
  rw [mem_support_iff, SPMF.probOutput_eq_apply] at ha
  exact ha

theorem residual_preserve (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat)
    (input : (World auxSpec Coord Cell).Domain) (state : State Coord Cell) (hinv : Inv state)
    (answer : (World auxSpec Coord Cell).Range input) (after : State Coord Cell)
    (hafter : (some answer, after) ∈ support (residualStep aux q input state)) : Inv after := by
  have hsame : ∀ after : State Coord Cell, after.candidates = state.candidates →
      after.counters.probes = state.counters.probes → Inv after := by
    intro after hc hp
    unfold Inv
    rw [hc, hp]
    exact hinv
  cases input with
  | inl input =>
      obtain ⟨a, ha⟩ := support_of_shape (liftM (aux input) : SPMF _) id (fun _ => state) _ hafter
      simp only [Prod.mk.injEq] at ha
      rw [ha.2]; exact hinv
  | inr request =>
      cases request with
      | read row charge =>
          obtain ⟨a, ha⟩ := support_of_shape (reply state.rows row) id (fun a => readState q state row a charge) _ hafter
          simp only [Prod.mk.injEq] at ha
          rw [ha.2]
          exact hsame _ rfl (SigGolfCandidate.T3.Security.LargeResidual.Counters.charge_probes _ _ _)
      | tick charge =>
          change (some answer, after) ∈ support (pure (some (), tickState q state charge) : SPMF _) at hafter
          rw [mem_support_pure_iff, Prod.mk.injEq] at hafter
          rw [hafter.2]
          exact hsame _ rfl (SigGolfCandidate.T3.Security.LargeResidual.Counters.charge_probes _ _ _)
      | disclose coord charge =>
          obtain ⟨v, hv0, hv⟩ := support_of_shape' (discLaw state.candidates coord) id
            (fun v => disclosedState q state coord v charge) _ hafter
          simp only [Prod.mk.injEq] at hv
          rw [hv.2]
          obtain ⟨-, hne⟩ := discLaw_mem state.candidates coord v hv0
          refine ⟨hne, fun c => ?_, fun f => ?_⟩
          · by_cases hc : c = coord
            · subst hc
              left
              simp only [disclosedState, discloseTableValue, Function.update_self, Finset.card_singleton]
            · simp only [disclosedState, discloseTableValue, Function.update_of_ne hc,
                SigGolfCandidate.T3.Security.LargeResidual.Counters.charge_probes]
              exact hinv.2.1 c
          · simp only [disclosedState, SigGolfCandidate.T3.Security.LargeResidual.Counters.charge_probes]
            exact (famDebt_disclose_le _ _ _ f).trans (hinv.2.2 f)
      | probe row test =>
          cases hcache : state.rows row with
          | some cached =>
              change (some answer, after) ∈ support (match state.rows row with
                | some answer => (pure (some answer, readState q state row answer .call) : SPMF _)
                | none => _) at hafter
              rw [hcache, mem_support_pure_iff, Prod.mk.injEq] at hafter
              rw [hafter.2]
              exact hsame _ rfl (SigGolfCandidate.T3.Security.LargeResidual.Counters.charge_probes _ _ _)
          | none =>
              have hstep : residualStep aux q (.inr (.probe row test)) state =
                  observe (lazyResp state.candidates (test.effF state.candidates))
                    (pure (none, stoppedState state))
                    (fun answer => pure (some answer, probeState state row (test.effF state.candidates) answer)) := by
                change (match state.rows row with
                  | some answer => pure (some answer, readState q state row answer .call)
                  | none => _) = _
                rw [hcache]
              rw [hstep] at hafter
              rcases observe_support _ _ _ _ hafter with h | ⟨a, ha, h⟩
              · simp at h
              · simp only [Prod.mk.injEq] at h
                rw [h.2]
                obtain ⟨-, hS'⟩ := lazyResp_nonempty state.candidates _ a ha
                have hne : ∀ c, ((test.effF state.candidates).restrict state.candidates a c).Nonempty := by
                  obtain ⟨x, hx⟩ := hS'
                  exact fun c => ⟨view x c, (mem_supp _ x).mp hx c⟩
                refine ⟨hS', fun c => ?_, fun f => ?_⟩
                · have hge := card_restrict_ge (test.effF state.candidates) state.candidates a
                    (fun g hg => (effF_adm state.candidates test g hg).2.1) c
                  have hle := restrict_subset_card (test.effF state.candidates) state.candidates a c
                  have hpos := (hne c).card_pos
                  simp only [probeState, Counters.probe]
                  rcases hinv.2.1 c with h1 | h2
                  · left; omega
                  · right; omega
                · simp only [probeState, Counters.probe]
                  exact (famDebt_probe_le state.candidates test a hne f).trans (by have := hinv.2.2 f; omega)

theorem residual_potential {Result : Type} (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat)
    (hq : q ≤ 2 ^ 127) (program : OracleComp (World auxSpec Coord Cell) Result) :
    Pr[fun result => result.1 = none ∧ result.2.counters.calls ≤ q | lazyRun aux q program initial] +
      (∑' result, Pr[= result | lazyRun aux q program initial] * (result.2.counters.mass : ENNReal)) / 2 ^ 128 ≤
      ENNReal.ofReal (2 * ((q : ℝ) / 2 ^ 128) - ((q : ℝ) / 2 ^ 128) ^ 2) := by
  have h := SigGolfCandidate.T3.Security.LargePotential.run_potential_initial (residualStep aux q) charges q hq Inv
    (fun input state hinv _ answer after hafter => residual_preserve aux q input state hinv answer after hafter)
    (fun input state hinv _ => residual_step_bound aux q input state hinv) program initial initial_inv rfl rfl
  rw [run_residual] at h
  exact h

end Bound
end ClaudeWCT.W9.T3.Security.FamResidual
end

section
namespace ClaudeWCT.W9.T3.Security.FamResidual
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
open SigGolfCandidate.T3.Security.LargeResidual (Digest HashOutput low Hit Probe Charge Request ResidualSpec World
  Counters State readState probeState stoppedState disclosedState tickState runWith runWith_pure runWith_query_bind)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

section Steps
variable {Coord Cell AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Seeds Coord] [Fintype Coord] [DecidableEq Coord] [Fintype Cell] [DecidableEq Cell]
variable (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat)

section Observed
variable (labels : Coord → Digest) (table : Cell → HashOutput)
theorem observed_pure {β : Type} (v : β) (s : State Coord Cell) :
    observedRun aux q labels table (pure v) s = pure (some v, s) :=
  runWith_pure _ v s
theorem observed_aux {β : Type} (i : AuxIndex) (k : auxSpec.Range i → OracleComp (World auxSpec Coord Cell) β)
    (s : State Coord Cell) :
    observedRun aux q labels table (liftM ((World auxSpec Coord Cell).query (.inl i)) >>= k) s =
      ((liftM (aux i) : SPMF _) >>= fun v => observedRun aux q labels table (k v) s) := by
  rw [observedRun, runWith_query_bind]
  simp only [observedImpl, OptionT.run_mk, StateT.run_mk, bind_assoc, pure_bind, Option.elim_some]
  rfl
theorem observed_read {β : Type} (row : Cell) (ch : Charge) (k : HashOutput → OracleComp (World auxSpec Coord Cell) β)
    (s : State Coord Cell) :
    observedRun aux q labels table (liftM ((World auxSpec Coord Cell).query (.inr (.read row ch))) >>= k) s =
      observedRun aux q labels table (k (table row)) (readState q s row (table row) ch) := by
  rw [observedRun, runWith_query_bind]
  simp only [observedImpl, OptionT.run_mk, StateT.run_mk, pure_bind, Option.elim_some]
  rfl
theorem observed_probe_cached {β : Type} (row : Cell) (test : Probe Coord)
    (k : HashOutput → OracleComp (World auxSpec Coord Cell) β) (s : State Coord Cell) (v : HashOutput)
    (h : s.rows row = some v) :
    observedRun aux q labels table (liftM ((World auxSpec Coord Cell).query (.inr (.probe row test))) >>= k) s =
      observedRun aux q labels table (k v) (readState q s row v .call) := by
  rw [observedRun, runWith_query_bind]
  simp only [observedImpl, OptionT.run_mk, StateT.run_mk, h, pure_bind, Option.elim_some]
  rfl
theorem observed_probe_fresh {β : Type} (row : Cell) (test : Probe Coord)
    (k : HashOutput → OracleComp (World auxSpec Coord Cell) β) (s : State Coord Cell) (h : s.rows row = none) :
    observedRun aux q labels table (liftM ((World auxSpec Coord Cell).query (.inr (.probe row test))) >>= k) s =
      if (test.effF s.candidates).keep labels (table row) then
        observedRun aux q labels table (k (table row)) (probeState s row (test.effF s.candidates) (table row))
      else pure (none, stoppedState s) := by
  rw [observedRun, runWith_query_bind]
  simp only [observedImpl, OptionT.run_mk, StateT.run_mk, h]
  split_ifs <;> simp only [pure_bind, Option.elim_some, Option.elim_none, observedRun]
theorem observed_disclose {β : Type} (c : Coord) (ch : Charge) (k : Digest → OracleComp (World auxSpec Coord Cell) β)
    (s : State Coord Cell) :
    observedRun aux q labels table (liftM ((World auxSpec Coord Cell).query (.inr (.disclose c ch))) >>= k) s =
      observedRun aux q labels table (k (labels c)) (disclosedState q s c (labels c) ch) := by
  rw [observedRun, runWith_query_bind]
  simp only [observedImpl, OptionT.run_mk, StateT.run_mk, pure_bind, Option.elim_some]
  rfl
theorem observed_tick {β : Type} (ch : Charge) (k : Unit → OracleComp (World auxSpec Coord Cell) β)
    (s : State Coord Cell) :
    observedRun aux q labels table (liftM ((World auxSpec Coord Cell).query (.inr (.tick ch))) >>= k) s =
      observedRun aux q labels table (k ()) (tickState q s ch) := by
  rw [observedRun, runWith_query_bind]
  simp only [observedImpl, OptionT.run_mk, StateT.run_mk, pure_bind, Option.elim_some]
  rfl
end Observed

section Lazy
theorem lazy_pure {β : Type} (v : β) (s : State Coord Cell) :
    lazyRun aux q (pure v) s = pure (some v, s) :=
  runWith_pure _ v s
theorem lazy_aux' {β : Type} (i : AuxIndex) (k : auxSpec.Range i → OracleComp (World auxSpec Coord Cell) β)
    (s : State Coord Cell) :
    lazyRun aux q (liftM ((World auxSpec Coord Cell).query (.inl i)) >>= k) s =
      ((liftM (aux i) : SPMF _) >>= fun v => lazyRun aux q (k v) s) := by
  rw [lazyRun, runWith_query_bind]
  simp only [lazyImpl, OptionT.run_mk, StateT.run_mk, bind_assoc, pure_bind, Option.elim_some]
  rfl
theorem lazy_read {β : Type} (row : Cell) (ch : Charge) (k : HashOutput → OracleComp (World auxSpec Coord Cell) β)
    (s : State Coord Cell) :
    lazyRun aux q (liftM ((World auxSpec Coord Cell).query (.inr (.read row ch))) >>= k) s =
      (reply s.rows row >>= fun y => lazyRun aux q (k y) (readState q s row y ch)) := by
  rw [lazyRun, runWith_query_bind]
  simp only [lazyImpl, OptionT.run_mk, StateT.run_mk, bind_assoc, pure_bind, Option.elim_some]
  rfl
theorem lazy_probe_cached {β : Type} (row : Cell) (test : Probe Coord)
    (k : HashOutput → OracleComp (World auxSpec Coord Cell) β) (s : State Coord Cell) (v : HashOutput)
    (h : s.rows row = some v) :
    lazyRun aux q (liftM ((World auxSpec Coord Cell).query (.inr (.probe row test))) >>= k) s =
      lazyRun aux q (k v) (readState q s row v .call) := by
  rw [lazyRun, runWith_query_bind]
  simp only [lazyImpl, OptionT.run_mk, StateT.run_mk, h, pure_bind, Option.elim_some]
  rfl
theorem lazy_probe_fresh {β : Type} (row : Cell) (test : Probe Coord)
    (k : HashOutput → OracleComp (World auxSpec Coord Cell) β) (s : State Coord Cell) (h : s.rows row = none) :
    lazyRun aux q (liftM ((World auxSpec Coord Cell).query (.inr (.probe row test))) >>= k) s =
      observe (lazyResp s.candidates (test.effF s.candidates)) (pure (none, stoppedState s))
        (fun y => lazyRun aux q (k y) (probeState s row (test.effF s.candidates) y)) := by
  rw [lazyRun, runWith_query_bind]
  simp only [lazyImpl, OptionT.run_mk, StateT.run_mk, h, observe_bind, pure_bind, Option.elim_none,
    Option.elim_some]
  rfl
theorem lazy_disclose {β : Type} (c : Coord) (ch : Charge) (k : Digest → OracleComp (World auxSpec Coord Cell) β)
    (s : State Coord Cell) :
    lazyRun aux q (liftM ((World auxSpec Coord Cell).query (.inr (.disclose c ch))) >>= k) s =
      (discLaw s.candidates c >>= fun v => lazyRun aux q (k v) (disclosedState q s c v ch)) := by
  rw [lazyRun, runWith_query_bind]
  simp only [lazyImpl, OptionT.run_mk, StateT.run_mk, bind_assoc, pure_bind, Option.elim_some]
  rfl
theorem lazy_tick {β : Type} (ch : Charge) (k : Unit → OracleComp (World auxSpec Coord Cell) β)
    (s : State Coord Cell) :
    lazyRun aux q (liftM ((World auxSpec Coord Cell).query (.inr (.tick ch))) >>= k) s =
      lazyRun aux q (k ()) (tickState q s ch) := by
  rw [lazyRun, runWith_query_bind]
  simp only [lazyImpl, OptionT.run_mk, StateT.run_mk, pure_bind, Option.elim_some]
  rfl
end Lazy
end Steps

section Plain
variable {Coord : Type} [Seeds Coord] [Fintype Coord] [DecidableEq Coord]

/-- The marginal of a plain coordinate is dominated by the uniform law on its candidates. -/
theorem discLaw_le_cell (cand : Coord → Finset Digest) {c : Coord} {p : Seeds.Plain Coord}
    (hc : Seeds.split c = .inl p) (v : Digest) : discLaw cand c v ≤ cell (cand c) v := by
  have he : Seeds.embed p = c := Seeds.embed_of_split c p hc
  rw [discLaw, margOf_apply]
  by_cases hv : v ∈ cand c
  · rw [cell_apply, if_pos hv]
    by_cases hS : (supp cand).Nonempty
    · have h := plain_ratio cand hS p v
      rw [he] at h
      calc _ ≤ ((margFilter (supp cand) (fun x => view x c) v).card / (supp cand).card : ℝ≥0∞) * 1 := by
            gcongr
            by_cases hn : (margFilter (supp cand) (fun x => view x c) v).Nonempty
            · rw [cell, dif_pos hn]; simp only [SPMF.liftM_apply, PMF.tsum_coe, le_refl]
            · rw [cell, dif_neg hn]; simp only [SPMF.failure_apply, tsum_zero, zero_le]
        _ ≤ _ := by rw [mul_one]; exact h
    · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
      simp [margFilter]
  · have hempty : margFilter (supp cand) (fun x => view x c) v = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro x hx
      obtain ⟨hxs, hxv⟩ := (mem_margFilter _ _ _ _).mp hx
      exact hv (hxv ▸ (mem_supp cand x).mp hxs c)
    rw [hempty]
    simp

theorem expectedValue_discLaw_le (cand : Coord → Finset Digest) {c : Coord} {p : Seeds.Plain Coord}
    (hc : Seeds.split c = .inl p) (g : Digest → ENNReal) :
    expectedValue (discLaw cand c) g ≤ expectedValue (cell (cand c)) g := by
  simp only [expectedValue_def]
  apply ENNReal.tsum_le_tsum
  intro v
  rw [SPMF.probOutput_eq_apply, SPMF.probOutput_eq_apply]
  gcongr
  exact discLaw_le_cell cand hc v

end Plain
end ClaudeWCT.W9.T3.Security.FamResidual
end

section
namespace ClaudeWCT.W9.T3.Security.FamResidual
open SigGolfCandidate.T3.Security.LargeResidual (Digest Hit Probe)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {Coord : Type} [Seeds Coord] [Fintype Coord]

theorem effF_self (cand : Coord → Finset Digest) (test : Probe Coord)
    (h : ∀ g ∈ test.guess, Adm cand test.hit g)
    (hsel : test.hit.isSelected = false ∨ test.guess = none := by
      first | exact Or.inl rfl | exact Or.inr rfl) : test.effF cand = test := by
  obtain ⟨guess, hit⟩ := test
  cases guess with
  | none => simp [Probe.effF]
  | some g =>
      have hs : hit.isSelected = false := hsel.resolve_right (by simp)
      have hg' := h g rfl
      simp only [Probe.effF, hs, Bool.false_eq_true, if_false, Option.filter_some,
        decide_eq_true_eq]
      rw [if_pos hg']

/-- `Adm` for a plain guess: the T3 admissibility. -/
theorem adm_of_plain (cand : Coord → Finset Digest) (hit : Hit Coord) (g : Coord × Digest)
    {p : Seeds.Plain Coord} (hp : Seeds.split g.1 = .inl p) (h2 : 2 ≤ (cand g.1).card)
    (hpar : ∀ parent, hit = Hit.label parent → g.1 ≠ parent) : Adm cand hit g :=
  ⟨h2, hpar, fun fp h => by rw [hp] at h; cases h⟩

end ClaudeWCT.W9.T3.Security.FamResidual
end

section
namespace ClaudeWCT.W9.T3.Security.FamResidual
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
open SigGolfCandidate.T3.Security.LargeResidual (Digest HashOutput World State runWith runWith_pure runWith_query_bind
  initial)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

section NoFail
variable {Coord Cell AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Seeds Coord] [Fintype Coord] [DecidableEq Coord] [Fintype Cell] [DecidableEq Cell]
  (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat)

theorem observed_noFail (labels : Coord → Digest) (table : Cell → HashOutput) {R : Type}
    (P : OracleComp (World auxSpec Coord Cell) R) :
    ∀ s, Pr[⊥ | observedRun aux q labels table P s] = 0 := by
  induction P using OracleComp.inductionOn with
  | pure v =>
      intro s
      rw [observedRun, runWith_pure]
      simp
  | query_bind input next ih =>
      intro s
      rw [observedRun, runWith_query_bind, probFailure_bind_eq_add_tsum]
      have h1 : Pr[⊥ | (observedImpl aux q labels table input).run.run s] = 0 := by
        rcases input with i | req
        · simp [observedImpl]
        · cases req with
          | read row ch => simp [observedImpl]
          | probe row test =>
              simp only [observedImpl, OptionT.run_mk, StateT.run_mk]
              split
              · simp
              · split <;> simp
          | disclose c ch => simp [observedImpl]
          | tick ch => simp [observedImpl]
      rw [h1, zero_add]
      apply ENNReal.tsum_eq_zero.mpr
      intro r
      rcases r with ⟨o, s'⟩
      cases o with
      | none => simp
      | some v =>
          simp only [Option.elim_some]
          exact mul_eq_zero_of_right _ (ih v s')

theorem supp_initial_nonempty : (supp (initial : State Coord Cell).candidates).Nonempty := by
  change (supp (fun _ : Coord => (Finset.univ : Finset Digest))).Nonempty
  rw [supp_univ]
  exact Finset.univ_nonempty

theorem lazy_noFail {R : Type} (P : OracleComp (World auxSpec Coord Cell) R) :
    Pr[⊥ | lazyRun aux q P (initial : State Coord Cell)] = 0 := by
  have hS := supp_initial_nonempty (Coord := Coord) (Cell := Cell)
  have hpost := run_posterior aux q P (initial : State Coord Cell) hS
  have h1 : Pr[⊥ | lazyRun aux q P (initial : State Coord Cell) >>= finish] = 0 := by
    rw [← hpost]
    have hc : cell (supp (initial : State Coord Cell).candidates) =
        liftM (PMF.uniformOfFinset (supp (initial : State Coord Cell).candidates) hS) := by
      rw [cell, dif_pos hS]
    have hr : completeRows (initial : State Coord Cell).rows =
        liftM (PMF.uniformOfFintype (Cell → HashOutput)) := completeRows_empty
    rw [hc, hr, probFailure_bind_eq_add_tsum, SPMF.probFailure_liftM, probFailure_eq_zero, zero_add]
    apply ENNReal.tsum_eq_zero.mpr
    intro x
    rw [probFailure_bind_eq_add_tsum, SPMF.probFailure_liftM, probFailure_eq_zero, zero_add]
    rw [ENNReal.tsum_eq_zero.mpr, mul_zero]
    intro table
    rw [probFailure_map, observed_noFail, mul_zero]
  have h2 := probFailure_bind_eq_add_tsum (lazyRun aux q P (initial : State Coord Cell)) finish
  rw [h1] at h2
  exact (add_eq_zero.mp h2.symm).1

end NoFail
end ClaudeWCT.W9.T3.Security.FamResidual
end
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_LargeResidualRouter ====
section

namespace ClaudeWCT.W9.T3.Security.LargeResidual
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.LargeResidual (listBlock slotValue routeAddr IsDigestRow AuxQuery
  Cell dummyDigest World Probe Hit Charge)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeResidualRouter : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
structure AuxData where
  high : CanonGraph.Node → Digest
  rows : EncLeaf → Fin (2 ^ 22) → HashOutput
  priv : FullGame.FullTable
noncomputable def AuxData.sel (a : AuxData) : Selections := fun L =>
  capSel L (SphincsSecurity.Concrete.FirstSuccessTable.select (decodeAt L) (a.rows L))
abbrev AuxSpec : OracleSpec AuxQuery
  | .coin n => Fin (n + 1)
  | .init => AuxData
noncomputable def auxLaw (initLaw : PMF AuxData) : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)
  | .coin n => PMF.uniformOfFintype (Fin (n + 1))
  | .init => initLaw
abbrev WCoord := Coord ⊕ Message
/-- Top-layer WOTS seed addresses as plain secrets: none since campaign T8D (top seeds are leaf-family evaluations);
the empty type keeps the shape of the plain coordinates. -/
abbrev WTopAddr := {_a : ChainGraph.Address // False}
/-- WOTS seed families `(layer, tree, f)` (`f = famOf layer leaf`, `famSize layer f` coefficients; today one family per
leaf). The name is kept from stage B. -/
abbrev LowerLeaf := {_L : Layer × Fin (2 ^ 31) × Fin 4096 // True}
/-- Secret cells that are not coefficients (address `(lay, tree, f, j)` with `j ≥ famSize lay f`): unused, not
observable. -/
abbrev WJunk := {a : ChainGraph.Address // WCT9.famSize a.layer a.leaf.val ≤ a.chain.val}
/-- Plain (independently uniform) world coordinates: nodes, (no) top WOTS seeds, nonces. -/
abbrev WPlain := (CanonGraph.Node ⊕ WTopAddr) ⊕ Message
/-- Seed families: WOTS leaves (`famCount` coefficients) and FTS coordinates `(index, coord)` (54 coefficients). -/
abbrev WFam := LowerLeaf ⊕ (Fin (2 ^ 31) × Fin 9)
/-- Split of the world coordinates: WOTS seeds are their family `(layer, tree, famOf leaf)` at `famPoint layer leaf chain`
(family slot `CanonGraph.famSlot`), FTS seeds are
evaluations of their family `(index, coord)` at `ftsPoint`. -/
def wsplit : WCoord → WPlain ⊕ (WFam × ℕ)
  | .inl (.inl N) => .inl (.inl (.inl N))
  | .inl (.inr (.inl a)) =>
      .inr (.inl ⟨(a.layer, a.tree, CanonGraph.famSlot a.layer a.leaf), trivial⟩, WCT9.famPoint a.layer a.leaf.val a.chain.val)
  | .inl (.inr (.inr w)) => .inr (.inr (w.1, w.2.1), WCT9.ftsPoint w.2.2.1.val w.2.2.2.val)
  | .inr m => .inl (.inr m)
/-- Embedding of the plain coordinates. -/
def wembed : WPlain → WCoord
  | .inl (.inl N) => .inl (.inl N)
  | .inl (.inr a) => .inl (.inr (.inl a.1))
  | .inr m => .inr m
theorem wsplit_addr (a : ChainGraph.Address) :
    wsplit (.inl (.inr (.inl a))) =
      .inr (.inl ⟨(a.layer, a.tree, CanonGraph.famSlot a.layer a.leaf), trivial⟩,
        WCT9.famPoint a.layer a.leaf.val a.chain.val) :=
  rfl
theorem wsplit_lower_eq {a a' : ChainGraph.Address}
    (he : (⟨(a.layer, a.tree, CanonGraph.famSlot a.layer a.leaf), trivial⟩ : LowerLeaf) =
      ⟨(a'.layer, a'.tree, CanonGraph.famSlot a'.layer a'.leaf), trivial⟩)
    (hp : WCT9.famPoint a.layer a.leaf.val a.chain.val = WCT9.famPoint a'.layer a'.leaf.val a'.chain.val) :
    a = a' := by
  have h1 := congrArg Subtype.val he
  simp only [Prod.mk.injEq] at h1
  obtain ⟨hl, ht, hf⟩ := h1
  rw [hl] at hp hf
  have hf' : WCT9.famOf a'.layer a.leaf.val = WCT9.famOf a'.layer a'.leaf.val := congrArg Fin.val hf
  obtain ⟨e1, e2⟩ := WCT9.famPoint_inj a.chain.isLt a'.chain.isLt hf' hp
  exact ChainGraph.Address.ext hl ht (Fin.ext e1) (Fin.ext e2)
theorem wsplit_inr {c : WCoord} {fp : WFam × ℕ} (h : wsplit c = .inr fp) :
    (∃ (a : ChainGraph.Address) (_ha : True), c = .inl (.inr (.inl a)) ∧
      fp = (.inl ⟨(a.layer, a.tree, CanonGraph.famSlot a.layer a.leaf), trivial⟩,
        WCT9.famPoint a.layer a.leaf.val a.chain.val)) ∨
    (∃ w : WctAddr, c = .inl (.inr (.inr w)) ∧
      fp = (.inr (w.1, w.2.1), WCT9.ftsPoint w.2.2.1.val w.2.2.2.val)) := by
  rcases c with (N | a | w) | m
  · simp only [wsplit, reduceCtorEq] at h
  · rw [wsplit_addr, Sum.inr.injEq] at h
    exact Or.inl ⟨a, trivial, rfl, h.symm⟩
  · simp only [wsplit, Sum.inr.injEq] at h
    exact Or.inr ⟨w, rfl, h.symm⟩
  · simp only [wsplit, reduceCtorEq] at h
noncomputable instance instSeedsWCoord : ClaudeWCT.W9.T3.Security.FamResidual.Seeds WCoord where
  Plain := WPlain
  Fam := WFam
  plainDec := Classical.decEq _
  famDec := Classical.decEq _
  deg := Sum.elim (fun L => WCT9.famSize L.1.1 L.1.2.2.val - 1) (fun _ => 53)
  split := wsplit
  embed := wembed
  split_embed p := by
    rcases p with (N | ⟨a, ha⟩) | m
    · rfl
    · exact ha.elim
    · rfl
  embed_of_split c p h := by
    rcases c with (N | a | w) | m
    · simp only [wsplit, Sum.inl.injEq] at h; subst h; rfl
    · rw [wsplit_addr] at h; cases h
    · simp only [wsplit, reduceCtorEq] at h
    · simp only [wsplit, Sum.inl.injEq] at h; subst h; rfl
  point_lt c f pt h := by
    rcases c with (N | a | w) | m
    · simp only [wsplit, reduceCtorEq] at h
    · rw [wsplit_addr, Sum.inr.injEq, Prod.mk.injEq] at h
      rw [← h.2]
      exact WCT9.famPoint_lt _ _ _ a.chain.isLt
    · simp only [wsplit, Sum.inr.injEq, Prod.mk.injEq] at h
      rw [← h.2]
      have := w.2.2.1.isLt; have := w.2.2.2.isLt
      unfold WCT9.ftsPoint WCT9.ftsOrdinal
      omega
    · simp only [wsplit, reduceCtorEq] at h
  seed_inj c c' fp h h' := by
    rcases wsplit_inr h with ⟨a, ha, rfl, rfl⟩ | ⟨w, rfl, rfl⟩ <;>
      rcases wsplit_inr h' with ⟨a', ha', rfl, he⟩ | ⟨w', rfl, he⟩
    · simp only [Prod.mk.injEq, Sum.inl.injEq] at he
      rw [wsplit_lower_eq he.1 he.2]
    · simp only [Prod.mk.injEq, reduceCtorEq, false_and] at he
    · simp only [Prod.mk.injEq, reduceCtorEq, false_and] at he
    · simp only [Prod.mk.injEq, Sum.inr.injEq] at he
      obtain ⟨⟨h1, h2⟩, h3⟩ := he
      unfold WCT9.ftsPoint WCT9.ftsOrdinal at h3
      have := w.2.2.2.isLt; have := w'.2.2.2.isLt
      have h4 : w.2.2.1 = w'.2.2.1 := Fin.ext (by omega)
      have h5 : w.2.2.2 = w'.2.2.2 := Fin.ext (by omega)
      have : w = w' := Prod.ext h1 (Prod.ext h2 (Prod.ext h4 h5))
      rw [this]
/-- Configuration (1)+(2): the target probe covers every permitted opening of the answer (both top halves unless
LOW is forced), so it detects any witness hint (`WCT9.encodingTarget`, 7/4 point mass). -/
noncomputable def encodingHit (lay : Layer) (target : Digest) : Hit WCoord :=
  .selectedTarget target (fun answer => decide (if lay = 0 then answer.extractLsb' 0 128 = target ∨
    TopChoice.blocked (answer.extractLsb' 0 128) else lowerSpare (answer.extractLsb' 0 128)))

theorem encodingHit_answerValue (lay : Layer) (target : Digest) (answer : HashOutput) :
    (encodingHit lay target).answerValue answer = WCT9.encodingTarget lay target answer := by
  have hlow : SigGolfCandidate.T3.Security.LargeResidual.low answer = answer.extractLsb' 0 128 := rfl
  by_cases hl : lay = 0
  · simp [hlow, encodingHit, Hit.answerValue, WCT9.encodingTarget, hl]
  · simp [hlow, encodingHit, Hit.answerValue, WCT9.encodingTarget, WCT9.encodingAnswer, hl, DualHalf.select,
      DualHalf.selectPair]

/-- Legacy (non-Paired) route: the probe compares the producer's selected half. -/
noncomputable def encodingHitSel (lay : Layer) (target : Digest) : Hit WCoord :=
  .selectedTarget target (fun answer => decide (if lay = 0 then WCT9.topGood (answer.extractLsb' 0 128) ∨
    TopChoice.blocked (answer.extractLsb' 0 128) else lowerSpare (answer.extractLsb' 0 128)))

theorem encodingHitSel_answerValue (lay : Layer) (target : Digest) (answer : HashOutput) :
    (encodingHitSel lay target).answerValue answer = WCT9.encodingAnswer lay answer := by
  have hlow : SigGolfCandidate.T3.Security.LargeResidual.low answer = answer.extractLsb' 0 128 := rfl
  by_cases hl : lay = 0
  · subst hl
    rw [WCT9.encodingAnswer_top_eq]
    simp [hlow, encodingHitSel, Hit.answerValue, WCT9.topChooseLow]
  · simp [hlow, encodingHitSel, Hit.answerValue, WCT9.encodingAnswer, hl, DualHalf.select, DualHalf.selectPair]

theorem keep_encodingHitSel (labels : WCoord → Digest) (lay : Layer) (target : Digest) (answer : HashOutput) :
    (⟨none, encodingHitSel lay target⟩ : Probe WCoord).keep labels answer ↔
      target ≠ WCT9.encodingAnswer lay answer := by
  unfold Probe.keep
  rw [encodingHitSel_answerValue]
  simp [Probe.guessMiss, encodingHitSel, Hit.miss]

theorem keep_encodingHit (labels : WCoord → Digest) (lay : Layer) (target : Digest) (answer : HashOutput) :
    (⟨none, encodingHit lay target⟩ : Probe WCoord).keep labels answer ↔
      target ≠ WCT9.encodingTarget lay target answer := by
  unfold Probe.keep
  rw [encodingHit_answerValue]
  simp [Probe.guessMiss, encodingHit, Hit.miss]

abbrev RWorld (U : Finset HashInput) := World AuxSpec WCoord (Cell U)
section Requests
variable (U : Finset HashInput)
def coinReq (n : Nat) : OracleComp (RWorld U) (Fin (n + 1)) := liftM ((RWorld U).query (.inl (.coin n)))
def initReq : OracleComp (RWorld U) AuxData := liftM ((RWorld U).query (.inl .init))
def readReq (row : Cell U) (charge : Charge) : OracleComp (RWorld U) HashOutput :=
  liftM ((RWorld U).query (.inr (.read row charge)))
def probeReq (row : Cell U) (test : Probe WCoord) : OracleComp (RWorld U) HashOutput :=
  liftM ((RWorld U).query (.inr (.probe row test)))
def discloseReq (c : WCoord) (charge : Charge) : OracleComp (RWorld U) Digest :=
  liftM ((RWorld U).query (.inr (.disclose c charge)))
def tickReq (charge : Charge) : OracleComp (RWorld U) Unit := liftM ((RWorld U).query (.inr (.tick charge)))
def discloseAll : List Coord → OracleComp (RWorld U) (List (Coord × Digest))
  | [] => pure []
  | c :: rest => do
      let v ← discloseReq U (.inl c) .none
      let tail ← discloseAll rest
      pure ((c, v) :: tail)
end Requests
def lookupVal (pairs : List (Coord × Digest)) (c : Coord) : Digest :=
  ((pairs.find? fun p => decide (p.1 = c)).map Prod.snd).getD 0
structure RouterState where
  disclosed : List Coord
  seen : List HashInput
  calls : Nat
  trials : List HashInput
  births : List (HashInput × HashOutput)
  exposures : List HashOutput
  reused : Bool
  memo : List (Message × Option (BitVec 32 × HashOutput))
def RouterState.initial : RouterState := ⟨[], [], 0, [], [], [], false, []⟩
def RouterState.after (st : RouterState) (X : HashInput) : RouterState :=
  { st with seen := X :: st.seen, calls := st.calls + 1 }
def RouterState.Fresh (st : RouterState) (X : HashInput) : Prop := X ∉ st.seen ∧ X ∉ st.trials
noncomputable def RouterState.next (U : Finset HashInput) (st : RouterState) (X : HashInput) (y : HashOutput) :
    RouterState :=
  if X ∈ U ∧ IsDigestRow X ∧ st.Fresh X then { st.after X with births := (X, y) :: st.births } else st.after X
def RouterState.known (st : RouterState) : Coord → Prop :=
  Known fun c => c ∈ keygenDisclosed ∨ c ∈ st.disclosed
theorem RouterState.msgSlot_known (st : RouterState) (L : EncLeaf) (cs : Coord × Nat)
    (hc : cs ∈ msgSlots L) : st.known cs.1 :=
  Known.base (Or.inl (msgSlot_mem_keygen hc))

theorem RouterState.firstUnknownMsg_none (st : RouterState) (L : EncLeaf) :
    firstUnknownMsg st.known L = none := by
  apply List.find?_eq_none.mpr
  intro cs hc
  simpa using st.msgSlot_known L cs hc

/-- Pads of FTS coordinate `coord` read from coordinate values (nested FTS r1-1): the previous coordinate's top
values, `(0, 0)` for coordinate 0. -/
def prevVals (v : Coord → Digest) (index : Fin (2^31)) (coord : Fin 9) : Digest × Digest :=
  (((prevTop index coord 0).map v).getD 0, ((prevTop index coord 1).map v).getD 0)
noncomputable def cellValues : CanonGraph.Node → (Coord → Digest) → HashInput
  | .chain p, v => CanonGraph.rowW p (v (chainChild p))
  | .leaf L, v => pad64 (Extract.leafInput L.1.lay L.1.tree.val L.1.leaf.val
      ((List.range (chainCount L.1.lay)).map fun i => v (.inl (.chain (endPoint L.1 i)))))
  | .node n, v => if ActiveV v n then pad64 (WCT9.merkleNodeInputN n.1.lay.val n.1.tree.val
      (2 ^ (height n.1.lay - n.1.level.val - 1) + n.1.idx.val) n.1.nonce.val
      (treeVal v n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val))
      (treeVal v n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val + 1))) else phantom n
  | .wctChain p, v => WCT9.ftsChainInputW p.1.1.val p.1.2.1.val p.1.2.2.1.val p.1.2.2.2.val p.2.val
      (v (wctItem p.1 p.2.val))
  | .wctLeaf L, v => pad64 (Extract.wctLeafInputP L.index.val L.coord.val L.child.val (prevVals v L.index L.coord).1
      (List.ofFn fun t : Fin 6 => v (wctItem (L.index, L.coord, L.child, t) 4)))
  | .wctNode n, v => pad64 (nodeInputP 3 (WCT9.nodeLayer n.1.coord.val) n.1.index.val
      (2 ^ (7 - n.1.level.val - 1) + n.1.idx.val)
      (((ftsChild n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val)).map v).getD 0)
      (if n.1.level.val = 5 then (prevVals v n.1.index n.1.coord).2 else 0)
      (((ftsChild n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val + 1)).map v).getD 0))
  | .forest index, v => pad64 (Extract.forestInput index.val
      ((List.range 9).map fun c => (v (.inl (.wctNode (ftsTopNode index (fin9 c) 0))),
        v (.inl (.wctNode (ftsTopNode index (fin9 c) 1))))))
/-- The canonical input of node `N` from coordinate values (`cell` with the seeds read from the values). -/
noncomputable def cellFrom (N : CanonGraph.Node) (v : Coord → Digest) : HashInput := cellValues N v
noncomputable def refDigest (a : AuxData) (L : EncLeaf) : Digest :=
  match a.sel L with
  | some r => r.2
  | none => dummyDigest L.1.lay
def PrefixRow (a : AuxData) (L : EncLeaf) (ctr : BitVec 32) : Prop :=
  ctr.toNat < WCT9.searchLimit L.1.lay ∧ ∀ r, a.sel L = some r → ctr.toNat ≤ r.1.val
def prefixValue (a : AuxData) (L : EncLeaf) (ctr : BitVec 32) : HashOutput :=
  if h : ctr.toNat < 2 ^ 22 then a.rows L ⟨ctr.toNat, h⟩ else 0
noncomputable def routerDigits (a : AuxData) (L : Wots.LeafAddr) : List Nat :=
  if h : ∃ L' : EncLeaf, L'.toWots = L then
    ((a.sel (Classical.choose h)).bind fun r => decode L.lay r.2).getD (Wots.dummyDigits L.lay)
  else Wots.dummyDigits L.lay
def RouteOkR (a : AuxData) (index : Nat) : Prop :=
  ∀ lay : Layer, lay ≠ 0 → ∃ (L : EncLeaf) (r : Fin (2 ^ 22) × Digest),
    L.toWots = routeAddr index lay ∧ a.sel L = some r ∧ (decode lay r.2).isSome
def maskOf (a : AuxData) (level node : Nat) : Digest :=
  let answer := a.priv (.inl (header 13 0 0 level (node/2)))
  if node%2=0 then answer.extractLsb' 0 128 else answer.extractLsb' 128 128
def macOf (a : AuxData) (region : Region) : HashOutput :=
  SiggolfT3Mac4.encodeTag (SiggolfT3Mac4.macTag
    (fun i => a.priv (.inl (header 14 0 0 0 i.val))) (List.ofFn region))
/-- Published top-tree value: the value of the selected trial (top-nonce layer). -/
def topValue (v : Coord → Digest) (level node : Nat) : Digest := treeVal v 0 0 level node
def EncRow (X : HashInput) : Prop :=
  ∃ (L : EncLeaf) (m : WCT9.LayerMsg) (ctr : BitVec 32) (pad : Wots.RowPad), Extract.msgFits L.1.lay m ∧
    X = Wots.encRow L.toWots m ctr pad
def Parsed (X : HashInput) : Prop := ∃ N : CanonGraph.Node, Extract.posOf X = some N.toPos
/-- How the router presents a sampled answer for row `X` (nested FTS r1-1): with the halves swapped when `X` parses
as a top FTS node, so that the sampled low half lands in the half the node's parents read. -/
noncomputable def rowPresent (X : HashInput) : HashOutput ≃ HashOutput :=
  if hp : Parsed X then CanonGraph.presentEquiv (Classical.choose hp) else Equiv.refl _
section Route
variable (U : Finset HashInput)
def testReq (first : Bool) (row : Cell U) (test : Probe WCoord) : OracleComp (RWorld U) HashOutput :=
  if first then probeReq U row test else readReq U row .call
noncomputable def routeQuery (a : AuxData) (st : RouterState) (X : HashInput) :
    OracleComp (RWorld U) (HashOutput × RouterState) :=
  let st' : RouterState := st.after X
  let first : Bool := decide (X ∉ st.seen)
  if h : X ∈ U then
    if hp : Parsed X then
      let N := Classical.choose hp
      match firstUnknown st.known N with
      | some cs => (fun y => (rowPresent X y, st')) <$>
          testReq U first ⟨X, h⟩ ⟨some (.inl cs.1, slotValue X cs.2), .label (.inl (.inl N))⟩
      | none => do
          let pairs ← discloseAll U ((childSlots N).map Prod.fst)
          if X = cellFrom N (lookupVal pairs) then do
            let v ← discloseReq U (.inl (.inl N)) .call
            pure (CanonGraph.presentEquiv N (ChainGraph.joinOutput v (a.high N)), st')
          else (fun y => (rowPresent X y, st')) <$> testReq U first ⟨X, h⟩ ⟨none, .label (.inl (.inl N))⟩
    else if he : EncRow X then
      let L := Classical.choose he
      let ctr := Classical.choose (Classical.choose_spec (Classical.choose_spec he))
      match firstUnknownMsg st.known L with
      | some cs => (fun y => (y, st')) <$>
          testReq U first ⟨X, h⟩ ⟨some (.inl cs.1, slotValue X cs.2), .target (refDigest a L)⟩
      | none => do
          let pairs ← discloseAll U ((msgSlots L).map Prod.fst)
          if X = Wots.encRow L.toWots (msgVals (lookupVal pairs) L) ctr 0 ∧ PrefixRow a L ctr then do
            tickReq U .call
            pure (prefixValue a L ctr, st')
          else (fun y => (y, st')) <$> testReq U first ⟨X, h⟩ ⟨none, encodingHitSel L.1.lay (refDigest a L)⟩
    else if IsDigestRow X then
      (fun y => (y, if st.Fresh X then { st' with births := (X, y) :: st.births } else st')) <$> readReq U ⟨X, h⟩ .mass
    else (fun y => (y, st')) <$> readReq U ⟨X, h⟩ .call
  else do
    tickReq U .call
    pure (0, st')
noncomputable def readImpl (a : AuxData) : QueryImpl SigGolfCandidate.T3.Spec (OracleComp (RWorld U))
  | .inl (.inl n) => coinReq U n
  | .inl (.inr X) => if h : X ∈ U then readReq U ⟨X, h⟩ .none else pure (0 : HashOutput)
  | .inr c => pure (a.priv c)
def assembleSig (rho : Digest) (N : HashOutput) (v : Coord → Digest) (digitsOf : Wots.LeafAddr → List Nat) :
    Signature :=
  let index := digestIndex N
  ⟨rho,
    fun k => ⟨fun t => v (wctItem (index, k, WCT9.child N k, t) (4 - WCT9.wordDigit (WCT9.rank N k) t)),
      fun l => ((wctPath index k N).map v).getD l.val 0⟩,
    fun lay => piecesSignature lay ((layerChains digitsOf index lay).map v, (layerPath index lay).map v)⟩
def trialRows (rho : Digest) (m : Message) (found : Option (BitVec 32 × HashOutput)) : List HashInput :=
  (List.range (match found with | some (c, _) => c.toNat + 1 | none => WCT9.digestAttemptLimit)).map fun c =>
    pad64 (digestInput rho m (BitVec.ofNat 32 c))
def RouterState.cache (st : RouterState) : Sampling.RCache := fun X => st.births.lookup X
noncomputable def RouterState.signed (st : RouterState) (rho : Digest) (m : Message) (found : Option (BitVec 32 × HashOutput)) :
    RouterState :=
  if CaseC.bankSpec.Reuse st.cache rho m then
    { st with
      trials := st.trials ++ trialRows rho m found
      memo := (m, found) :: st.memo
      reused := true }
  else
    { st with
      trials := st.trials ++ trialRows rho m found
      memo := (m, found) :: st.memo
      exposures := st.exposures ++ (found.map Prod.snd).toList }
theorem RouterState.signed_fields (st : RouterState) (rho : Digest) (m : Message)
    (found : Option (BitVec 32 × HashOutput)) :
    (st.signed rho m found).disclosed = st.disclosed ∧ (st.signed rho m found).seen = st.seen ∧
      (st.signed rho m found).calls = st.calls ∧ (st.signed rho m found).births = st.births ∧
      (st.signed rho m found).trials = st.trials ++ trialRows rho m found ∧
      (st.signed rho m found).memo = (m, found) :: st.memo := by
  unfold RouterState.signed
  split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
noncomputable def signFinish (a : AuxData) (st : RouterState) (rho : Digest)
    (found : Option (BitVec 32 × HashOutput)) : OracleComp (RWorld U) (Option Signature × RouterState) :=
  match found with
  | none => pure (none, st)
  | some (_, N) =>
      if RouteOkR a (WCT9.digestIndex N) then do
        let items := signItemsWith (routerDigits a) N
        let pairs ← discloseAll U items
        pure (some (assembleSig rho N (lookupVal pairs) (routerDigits a)),
          { st with disclosed := st.disclosed ++ items })
      else pure (none, st)
noncomputable def routeSign (a : AuxData) (published : SigGolfCandidate.T3.Cache) (st : RouterState)
    (request : SigGolfCandidate.T3.Security.Request) : OracleComp (RWorld U) (Option Signature × RouterState) :=
  if request.cache = published then do
    let rho ← discloseReq U (.inr request.message) .none
    match st.memo.lookup request.message with
    | some found => signFinish U a st rho found
    | none => do
        let found ← simulateQ (readImpl U a) (WCT9.digestSearch rho request.message 0 WCT9.digestAttemptLimit)
        signFinish U a (st.signed rho request.message found) rho found
  else pure (none, st)
noncomputable def routeInteraction (a : AuxData) (published : SigGolfCandidate.T3.Cache) (q : Nat) {α : Type}
    (program : OracleComp LazyPrivate.Interaction α) :
    RouterState → OracleComp (RWorld U) (Option ((α × QueryLog Requests) × RouterState)) :=
  OracleComp.construct
    (fun value st => pure (some ((value, []), st)))
    (fun input _ next st => match input, next with
      | .inl (.inl n), next => do
          let c ← coinReq U n
          next c st
      | .inl (.inr X), next =>
          if q ≤ st.calls then pure none else do
            let r ← routeQuery U a st X
            next r.1 r.2
      | .inr request, next => do
          let s ← routeSign U a published st request
          let rest ← next s.1 s.2
          pure (rest.map fun res => ((res.1.1, ⟨request, s.1⟩ :: res.1.2), res.2)))
    program
noncomputable def routeVerdict (a : AuxData) (q : Nat) {β : Type} (program : M β) :
    RouterState → OracleComp (RWorld U) (Option (β × RouterState)) :=
  OracleComp.construct
    (fun value st => pure (some (value, st)))
    (fun input _ next st => match input, next with
      | .inl (.inl n), next => do
          let c ← coinReq U n
          next c st
      | .inl (.inr X), next =>
          if q ≤ st.calls then pure none else do
            let r ← routeQuery U a st X
            next r.1 r.2
      | .inr c, next => next (a.priv c) st)
    program
noncomputable def routerWith (adversary : Final.AdversaryP) (q : Nat) (a : AuxData) :
    OracleComp (RWorld U) (Option (Bool × RouterState)) := do
  let pairs ← discloseAll U keygenDisclosed
  let v := lookupVal pairs
  let pk := v (.inl (.node rootNode))
  let region := Correctness.cacheRegion fun level node => topValue v level node ^^^ maskOf a level node
  let published : SigGolfCandidate.T3.Cache := ⟨macOf a region, region⟩
  let r ← routeInteraction U a published q (adversary pk published) RouterState.initial
  match r with
  | none => pure none
  | some (result, st) => routeVerdict U a q (GameWith.verdict PaddedGame.checker pk result) st
noncomputable def router (adversary : Final.AdversaryP) (q : Nat) : OracleComp (RWorld U) (Option (Bool × RouterState)) :=
  initReq U >>= routerWith U adversary q
end Route
end ClaudeWCT.W9.T3.Security.LargeResidual

/-!
# Paired-family residual engine prototype

The installed WCoord instance above is unchanged. A distinct wrapper type
below gets a fully proved Seeds instance grouping lower leaves by leaf/2,
with 14 coefficients and stride-58 points. This makes the existing generic
residual posterior engine applicable to this address model. It does NOT
establish that the sign image or old large-coupling proof implements it.
-/
namespace ClaudeWCT.W9.T3.Security.LargeResidual.AdjacentLeafResearch
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3.Security.CanonGraph
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-- Distinct type: never silently replace the installed WCoord instance. -/
structure PairedCoord where
  value : WCoord
  deriving DecidableEq, Fintype

/-- The top family keeps its original identity; lower families share
identity between adjacent leaves. -/
def groupedLeaf (a : ChainGraph.Address) : LowerLeaf :=
  ⟨(a.layer,a.tree,
    if a.layer=0 then a.leaf else ⟨a.leaf.val/2, by have := a.leaf.isLt; omega⟩),trivial⟩

def groupedPoint (a : ChainGraph.Address) : Nat :=
  if a.layer=0 then a.chain.val+1 else 58*(a.leaf.val%2)+a.chain.val+1

/-- Inversion includes all reserved Fin58 addresses, not just 43 real chains. -/
theorem grouped_address_injective {a a' : ChainGraph.Address}
    (hf : groupedLeaf a = groupedLeaf a') (hp : groupedPoint a = groupedPoint a') : a=a' := by
  have hv := congrArg Subtype.val hf
  have hl : a.layer=a'.layer := congrArg Prod.fst hv
  have ht : a.tree=a'.tree := congrArg (fun p => p.2.1) hv
  have hc := a.chain.isLt
  have hc' := a'.chain.isLt
  have hm := Nat.mod_lt a.leaf.val (by decide : 0<2)
  have hm' := Nat.mod_lt a'.leaf.val (by decide : 0<2)
  have hleaf := congrArg (fun p => p.2.2.val) hv
  by_cases h0 : a.layer=0
  · have h0' : a'.layer=0 := hl ▸ h0
    simp only [groupedLeaf,groupedPoint,if_pos h0,if_pos h0'] at hleaf hp
    exact ChainGraph.Address.ext hl ht (Fin.ext hleaf) (Fin.ext (by omega))
  · have h0' : a'.layer≠0 := hl ▸ h0
    simp only [groupedLeaf,groupedPoint,if_neg h0,if_neg h0'] at hleaf hp
    exact ChainGraph.Address.ext hl ht (Fin.ext (by omega)) (Fin.ext (by omega))

theorem groupedPoint_small (a : ChainGraph.Address) : groupedPoint a < 1024 := by
  have hc := a.chain.isLt
  have hm := Nat.mod_lt a.leaf.val (by decide : 0<2)
  unfold groupedPoint
  split <;> omega

def pairedSplit : PairedCoord → WPlain ⊕ (WFam × Nat)
  | ⟨.inl (.inl N)⟩ => .inl (.inl (.inl N))
  | ⟨.inl (.inr (.inl a))⟩ => .inr (.inl (groupedLeaf a),groupedPoint a)
  | ⟨.inl (.inr (.inr w))⟩ => .inr (.inr (w.1,w.2.1),WCT9.ftsPoint w.2.2.1.val w.2.2.2.val)
  | ⟨.inr m⟩ => .inl (.inr m)

def pairedEmbed (p : WPlain) : PairedCoord := ⟨wembed p⟩

/-- Top degree23, lower-pair degree13, FTS degree53. -/
def pairedDegree : WFam → Nat
  | .inl L => if L.1.1=0 then 23 else 13
  | .inr _ => 53

noncomputable instance instPairedSeeds : FamResidual.Seeds PairedCoord where
  Plain := WPlain
  Fam := WFam
  plainDec := Classical.decEq _
  famDec := Classical.decEq _
  deg := pairedDegree
  split := pairedSplit
  embed := pairedEmbed
  split_embed p := by
    rcases p with (N | ⟨a,ha⟩) | m
    · rfl
    · exact ha.elim
    · rfl
  embed_of_split c p h := by
    rcases c with ⟨(N | a | w) | m⟩
    · simp only [pairedSplit,Sum.inl.injEq] at h; subst h; rfl
    · simp only [pairedSplit,reduceCtorEq] at h
    · simp only [pairedSplit,reduceCtorEq] at h
    · simp only [pairedSplit,Sum.inl.injEq] at h; subst h; rfl
  point_lt c f pt h := by
    rcases c with ⟨(N | a | w) | m⟩
    · simp only [pairedSplit,reduceCtorEq] at h
    · simp only [pairedSplit,Sum.inr.injEq,Prod.mk.injEq] at h
      rw [← h.2]
      exact groupedPoint_small a
    · simp only [pairedSplit,Sum.inr.injEq,Prod.mk.injEq] at h
      rw [← h.2]
      have := w.2.2.1.isLt; have := w.2.2.2.isLt
      unfold WCT9.ftsPoint WCT9.ftsOrdinal
      omega
    · simp only [pairedSplit,reduceCtorEq] at h
  seed_inj c c' fp h h' := by
    have he : pairedSplit c = pairedSplit c' := h.trans h'.symm
    rcases c with ⟨(N | a | w) | m⟩ <;> rcases c' with ⟨(N' | a' | w') | m'⟩ <;>
      simp only [pairedSplit,Sum.inl.injEq,Sum.inr.injEq,Prod.mk.injEq,reduceCtorEq,false_and] at he h
    · have haa := grouped_address_injective he.1 he.2
      subst a'
      rfl
    · obtain ⟨⟨h1,h2⟩,h3⟩ := he
      unfold WCT9.ftsPoint WCT9.ftsOrdinal at h3
      have := w.2.2.2.isLt; have := w'.2.2.2.isLt
      have h4 : w.2.2.1=w'.2.2.1 := Fin.ext (by omega)
      have h5 : w.2.2.2=w'.2.2.2 := Fin.ext (by omega)
      have hw : w=w' := Prod.ext h1 (Prod.ext h2 (Prod.ext h4 h5))
      subst w'
      rfl

/-- The generic residual engine now sees the proposed shared seed family. -/
theorem paired_view_seed (x : FamResidual.Hid PairedCoord) (a : ChainGraph.Address) :
    FamResidual.view x ⟨.inl (.inr (.inl a))⟩ =
      ClaudeWCT.Arith.familyEval (List.ofFn (x.2 (.inl (groupedLeaf a)))) (groupedPoint a) := rfl

end ClaudeWCT.W9.T3.Security.LargeResidual.AdjacentLeafResearch

namespace ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.LargeResidual (slotValue routeAddr IsDigestRow AuxQuery Cell dummyDigest World Probe Hit Charge)
open ClaudeWCT.W9.T3.Security.CanonGraph ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _

structure AuxData where
  high : CanonGraph.Node → Digest
  rows : CanonEncoding.EncLeaf → Fin (2^22) → HashOutput
  sel : CanonEncoding.Selections
  priv : FullGame.FullTable
abbrev AuxSpec : OracleSpec AuxQuery
  | .coin n => Fin (n+1)
  | .init => AuxData
noncomputable def auxLaw (initLaw : PMF AuxData) : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)
  | .coin n => PMF.uniformOfFintype (Fin (n+1))
  | .init => initLaw
abbrev RWorld (U : Finset HashInput) := World AuxSpec WCoord (Cell U)

section Requests
variable (U : Finset HashInput)
def coinReq (n : Nat) : OracleComp (RWorld U) (Fin (n+1)) := liftM ((RWorld U).query (.inl (.coin n)))
def initReq : OracleComp (RWorld U) AuxData := liftM ((RWorld U).query (.inl .init))
def readReq (row : Cell U) (charge : Charge) : OracleComp (RWorld U) HashOutput :=
  liftM ((RWorld U).query (.inr (.read row charge)))
def probeReq (row : Cell U) (test : Probe WCoord) : OracleComp (RWorld U) HashOutput :=
  liftM ((RWorld U).query (.inr (.probe row test)))
def discloseReq (c : WCoord) (charge : Charge) : OracleComp (RWorld U) Digest :=
  liftM ((RWorld U).query (.inr (.disclose c charge)))
def tickReq (charge : Charge) : OracleComp (RWorld U) Unit := liftM ((RWorld U).query (.inr (.tick charge)))
def discloseAll : List Coord → OracleComp (RWorld U) (List (Coord × Digest))
  | [] => pure []
  | c::rest => do
      let v ← discloseReq U (.inl c) .none
      let tail ← discloseAll rest
      pure ((c,v)::tail)
end Requests

abbrev RouterState := LargeResidual.RouterState
def RouterState.known (st : RouterState) : Coord → Prop :=
  Known fun c => c∈keygenDisclosed ∨ c∈st.disclosed

def padVals (v : Coord → Digest) (index : Fin (2^31)) (coord : Fin 9) (branch : Nat) : Digest×Digest :=
  (((padCoord index coord branch 0).map v).getD 0,((padCoord index coord branch 1).map v).getD 0)

noncomputable def cellValues : CanonGraph.Node → (Coord → Digest) → HashInput
  | .wctLeaf L,v => pad64 (Extract.wctLeafInputP L.index.val L.coord.val L.child.val
      (padVals v L.index L.coord (L.child.val%2)).1
      (List.ofFn fun t : Fin 6 => v (wctItem (L.index,L.coord,L.child,t) 4)))
  | .wctNode n,v => pad64 (nodeInputP 3 (WCT9.nodeLayer n.1.coord.val) n.1.index.val
      (2^(7-n.1.level.val-1)+n.1.idx.val)
      (((ftsChild n.1.index n.1.coord n.1.level.val (2*n.1.idx.val)).map v).getD 0)
      (if n.1.level.val=4 then (padVals v n.1.index n.1.coord (n.1.idx.val/2)).2 else 0)
      (((ftsChild n.1.index n.1.coord n.1.level.val (2*n.1.idx.val+1)).map v).getD 0))
  | n,v => LargeResidual.cellValues n v
noncomputable def cellFrom (N : CanonGraph.Node) (v : Coord → Digest) : HashInput := cellValues N v
/-- Top-nonce layer: the node of the queried position whose cell is `X` (unique by `cell_separated`), else `N`. -/
noncomputable def cellNode (N : CanonGraph.Node) (v : Coord → Digest) (X : HashInput) : CanonGraph.Node :=
  @dite _ (∃ M : CanonGraph.Node, CanonGraph.Paired.Filtered.Used M ∧ M.toPos = N.toPos ∧ X = cellFrom M v)
    (Classical.propDecidable _) (fun h => Classical.choose h) (fun _ => N)
/-- Every coordinate a cell reads (slots plus, on the top tree, the trials of the own and child positions). -/
def cellDepsP : CanonGraph.Node → List Coord
  | .node n => LargeResidual.cellDeps (.node n)
  | N => (childSlots N).map Prod.fst
noncomputable def refDigest (a : AuxData) (L : CanonEncoding.EncLeaf) : Digest :=
  match a.sel L with
  | some r => r.2
  | none => dummyDigest L.1.lay

def PrefixRow (a : AuxData) (L : CanonEncoding.EncLeaf) (ctr : BitVec 32) : Prop :=
  (CanonEncoding.Paired.rowsContext a.rows L.toWots).isSome ∧
  ctr.toNat<WCT9.searchLimit L.1.lay ∧ ∀r,a.sel L=some r → ctr.toNat≤r.1.val

def prefixValue (a : AuxData) (L : CanonEncoding.EncLeaf) (ctr : BitVec 32) : HashOutput :=
  if h : ctr.toNat<2^22 then a.rows L ⟨ctr.toNat,h⟩ else 0

noncomputable def routerDigits (a : AuxData) (L : Wots.LeafAddr) : List Nat :=
  if h : ∃L' : CanonEncoding.EncLeaf,L'.toWots=L then
    ((a.sel (Classical.choose h)).bind fun r => WCT9.CanonicalPolicy.decode L.lay r.2).getD (Wots.dummyDigits (WCT9.CanonicalPolicy.normalLayer L.lay))
  else Wots.dummyDigits L.lay

/-- The selected half of the router's canonical selection (`true` = LOW). -/
noncomputable def routerLows (a : AuxData) (L : Wots.LeafAddr) : Bool :=
  if h : ∃L' : CanonEncoding.EncLeaf,L'.toWots=L then
    ((a.sel (Classical.choose h)).map fun r => WCT9.lowSelected L.lay (a.rows (Classical.choose h) r.1)).getD true
  else true

def RouteOkR (a : AuxData) (index : Nat) : Prop :=
  ∀lay : Layer,∃(L : CanonEncoding.EncLeaf)(r : Fin (2^22)×Digest),
    L.toWots=routeAddr index lay ∧ a.sel L=some r ∧ (WCT9.CanonicalPolicy.decode lay r.2).isSome

def maskOf (a : AuxData) (level node : Nat) : Digest :=
  let answer := a.priv (.inl (header 13 0 0 level (node/2)))
  if node%2=0 then answer.extractLsb' 0 128 else answer.extractLsb' 128 128

def macOf (a : AuxData) (region : Region) : HashOutput :=
  SiggolfT3Mac4.encodeTag (SiggolfT3Mac4.macTag
    (fun i => a.priv (.inl (header 14 0 0 0 i.val))) (List.ofFn region))

def Parsed (X : HashInput) : Prop :=
  ∃N : CanonGraph.Node,CanonGraph.Paired.Filtered.Used N ∧ Extract.posOf X=some N.toPos

noncomputable def rowPresent (X : HashInput) : HashOutput ≃ HashOutput :=
  if hp : Parsed X then CanonGraph.Paired.presentEquiv (Classical.choose hp) else Equiv.refl _

section Route
variable (U : Finset HashInput)
def testReq (first : Bool) (row : Cell U) (test : Probe WCoord) : OracleComp (RWorld U) HashOutput :=
  if first then probeReq U row test else readReq U row .call

noncomputable def routeQuery (a : AuxData) (st : RouterState) (X : HashInput) :
    OracleComp (RWorld U) (HashOutput×RouterState) :=
  let st' := st.after X
  let first : Bool := decide (X∉st.seen)
  if h : X∈U then
    if hp : Parsed X then
      let N := (Classical.choose hp).base
      match firstUnknown (RouterState.known st) N with
      | some cs => (fun y => (rowPresent X y,st')) <$>
          testReq U first ⟨X,h⟩ ⟨some (.inl cs.1,slotValue X cs.2),.label (.inl (.inl N))⟩
      | none => do
          let pairs ← discloseAll U (cellDepsP N)
          let M := cellNode N (lookupVal pairs) X
          if X=cellFrom M (lookupVal pairs) then do
            let v ← discloseReq U (.inl (.inl M)) .call
            pure (CanonGraph.Paired.presentEquiv M (ChainGraph.joinOutput v (a.high M)),st')
          else (fun y => (rowPresent X y,st')) <$>
            testReq U first ⟨X,h⟩ ⟨none,.label (.inl (selCoordV (lookupVal pairs) (.inl N)))⟩
    else if hph : ∃ n : TreeNode, X = phantom n then
      let n := Classical.choose hph
      do
        let pairs ← discloseAll U (trialDeps n)
        if ActiveV (lookupVal pairs) n then (fun y => (y,st')) <$> readReq U ⟨X,h⟩ .call
        else do
          let v ← discloseReq U (.inl (.inl (.node n))) .call
          pure (CanonGraph.Paired.presentEquiv (.node n) (ChainGraph.joinOutput v (a.high (.node n))),st')
    else if he : EncRow X then
      let L := Classical.choose he
      let ctr := Classical.choose (Classical.choose_spec (Classical.choose_spec he))
      do
        let pairs ← discloseAll U ((msgSlots L).map Prod.fst)
        if X=Wots.encRow L.toWots (msgVals (lookupVal pairs) L) ctr 0 ∧ PrefixRow a L ctr then do
          tickReq U .call
          pure (prefixValue a L ctr,st')
        else (fun y => (y,st')) <$> testReq U first ⟨X,h⟩ ⟨none,encodingHit L.1.lay (refDigest a L)⟩
    else if IsDigestRow X then
      (fun y => (y,if st.Fresh X then {st' with births:=(X,y)::st.births} else st')) <$> readReq U ⟨X,h⟩ .mass
    else (fun y => (y,st')) <$> readReq U ⟨X,h⟩ .call
  else do
    tickReq U .call
    pure (0,st')

noncomputable def readImpl (a : AuxData) : QueryImpl SigGolfCandidate.T3.Spec (OracleComp (RWorld U))
  | .inl (.inl n) => coinReq U n
  | .inl (.inr X) => if h : X∈U then readReq U ⟨X,h⟩ .none else pure (0 : HashOutput)
  | .inr c => pure (a.priv c)

end Route
end ClaudeWCT.W9.T3.Security.LargeResidual.Paired

namespace ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.LargeResidual (Cell)
open ClaudeWCT.W9.T3.Security.CanonGraph ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

open SigGolfCandidate.T3.Security.LargeResidual (IsDigestRow slotValue)
variable (U : Finset HashInput)
noncomputable def routeQuerySelected (a : AuxData) (st : RouterState) (X : HashInput) :
    OracleComp (RWorld U) (HashOutput×RouterState) :=
  let st' := st.after X
  let first : Bool := decide (X∉st.seen)
  if h : X∈U then
    if hp : Parsed X then
      let N := (Classical.choose hp).base
      match firstUnknown (RouterState.known st) N with
      | some cs => (fun y => (rowPresent X y,st')) <$>
          testReq U first ⟨X,h⟩ ⟨some (.inl cs.1,slotValue X cs.2),.label (.inl (.inl N))⟩
      | none => do
          let pairs ← discloseAll U (cellDepsP N)
          let M := cellNode N (lookupVal pairs) X
          if X=cellFrom M (lookupVal pairs) then do
            let v ← discloseReq U (.inl (.inl M)) .call
            pure (CanonGraph.Paired.presentEquiv M (ChainGraph.joinOutput v (a.high M)),st')
          else (fun y => (rowPresent X y,st')) <$>
            testReq U first ⟨X,h⟩ ⟨none,.label (.inl (selCoordV (lookupVal pairs) (.inl N)))⟩
    else if hph : ∃ n : TreeNode, X = phantom n then
      let n := Classical.choose hph
      do
        let pairs ← discloseAll U (trialDeps n)
        if ActiveV (lookupVal pairs) n then (fun y => (y,st')) <$> readReq U ⟨X,h⟩ .call
        else do
          let v ← discloseReq U (.inl (.inl (.node n))) .call
          pure (CanonGraph.Paired.presentEquiv (.node n) (ChainGraph.joinOutput v (a.high (.node n))),st')
    else if he : EncRow X then
      let L := Classical.choose he
      let ctr := Classical.choose (Classical.choose_spec (Classical.choose_spec he))
      do
        let pairs ← discloseAll U ((msgSlots L).map Prod.fst)
        if X=Wots.encRow L.toWots (msgVals (lookupVal pairs) L) ctr 0 ∧ PrefixRow a L ctr then do
          tickReq U .call
          pure (prefixValue a L ctr,st')
        else if (a.sel L).isSome then
          (fun y => (y,st')) <$> testReq U first ⟨X,h⟩ ⟨none,encodingHit L.1.lay (refDigest a L)⟩
        else (fun y => (y,st')) <$> readReq U ⟨X,h⟩ .call
    else if IsDigestRow X then
      (fun y => (y,if st.Fresh X then {st' with births:=(X,y)::st.births} else st')) <$> readReq U ⟨X,h⟩ .mass
    else (fun y => (y,st')) <$> readReq U ⟨X,h⟩ .call
  else do
    tickReq U .call
    pure (0,st')

end ClaudeWCT.W9.T3.Security.LargeResidual.Paired
end
-- ==== merged from T3_Secc_LargeCouplingObserved ====
section

namespace SigGolfCandidate.T3.Security.LargeResidual
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
section Generic
variable {Coord Cell AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coord] [DecidableEq Coord] [Fintype Cell] [DecidableEq Cell]
theorem runWith_bind {α β : Type}
    (impl : QueryImpl (World auxSpec Coord Cell) (OptionT (StateT (State Coord Cell) SPMF)))
    (comp : OracleComp (World auxSpec Coord Cell) α) (k : α → OracleComp (World auxSpec Coord Cell) β)
    (s : State Coord Cell) :
    runWith impl (comp >>= k) s =
      (runWith impl comp s >>= fun r => r.1.elim (pure (none, r.2)) (fun v => runWith impl (k v) r.2)) := by
  simp only [runWith, simulateQ_bind, OptionT.run_bind, Option.elimM, StateT.run_bind]
  apply congrArg (fun continuation => (simulateQ impl comp).run.run s >>= continuation)
  funext r
  rcases r with ⟨v, s'⟩
  cases v <;> rfl
theorem runWith_map {α β : Type}
    (impl : QueryImpl (World auxSpec Coord Cell) (OptionT (StateT (State Coord Cell) SPMF)))
    (f : α → β) (comp : OracleComp (World auxSpec Coord Cell) α) (s : State Coord Cell) :
    runWith impl (f <$> comp) s = (fun r => (r.1.map f, r.2)) <$> runWith impl comp s := by
  rw [map_eq_bind_pure_comp, runWith_bind, map_eq_bind_pure_comp]
  apply congrArg (fun continuation => runWith impl comp s >>= continuation)
  funext r
  rcases r with ⟨v, s'⟩
  cases v with
  | none => rfl
  | some v => simp only [Option.elim_some, Function.comp_def, runWith_pure, Option.map_some]
variable (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat)
  (labels : Coord → Digest) (table : Cell → HashOutput)
end Generic
end SigGolfCandidate.T3.Security.LargeResidual
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_LargeCouplingObserved ====
section

namespace ClaudeWCT.W9.T3.Security.LargeResidual
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.LargeResidual (State Charge Probe Cell readState probeState stoppedState
  disclosedState tickState)
open ClaudeWCT.W9.T3.Security.FamResidual (observedRun observed_aux observed_read observed_probe_cached
  observed_probe_fresh observed_disclose observed_tick)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
section Router
variable (U : Finset HashInput) (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
  (labels : WCoord → Digest) (table : Cell U → HashOutput)
theorem observed_coinReq {β : Type} (n : Nat) (k : Fin (n + 1) → OracleComp (RWorld U) β) (s : State WCoord (Cell U)) :
    observedRun aux q labels table (coinReq U n >>= k) s =
      ((liftM (aux (.coin n)) : SPMF _) >>= fun v => observedRun aux q labels table (k v) s) :=
  observed_aux aux q labels table (.coin n) k s
theorem observed_readReq {β : Type} (row : Cell U) (ch : Charge) (k : HashOutput → OracleComp (RWorld U) β)
    (s : State WCoord (Cell U)) :
    observedRun aux q labels table (readReq U row ch >>= k) s =
      observedRun aux q labels table (k (table row)) (readState q s row (table row) ch) :=
  observed_read aux q labels table row ch k s
theorem observed_probeReq_fresh {β : Type} (row : Cell U) (test : Probe WCoord)
    (k : HashOutput → OracleComp (RWorld U) β) (s : State WCoord (Cell U)) (h : s.rows row = none) :
    observedRun aux q labels table (probeReq U row test >>= k) s =
      if (test.effF s.candidates).keep labels (table row) then
        observedRun aux q labels table (k (table row)) (probeState s row (test.effF s.candidates) (table row))
      else pure (none, stoppedState s) :=
  observed_probe_fresh aux q labels table row test k s h
theorem observed_discloseReq {β : Type} (c : WCoord) (ch : Charge) (k : Digest → OracleComp (RWorld U) β)
    (s : State WCoord (Cell U)) :
    observedRun aux q labels table (discloseReq U c ch >>= k) s =
      observedRun aux q labels table (k (labels c)) (disclosedState q s c (labels c) ch) :=
  observed_disclose aux q labels table c ch k s
theorem observed_tickReq {β : Type} (ch : Charge) (k : Unit → OracleComp (RWorld U) β) (s : State WCoord (Cell U)) :
    observedRun aux q labels table (tickReq U ch >>= k) s =
      observedRun aux q labels table (k ()) (tickState q s ch) :=
  observed_tick aux q labels table ch k s
def discloseStates (q : Nat) (labels : WCoord → Digest) (s : State WCoord (Cell U)) (cs : List Coord) :
    State WCoord (Cell U) :=
  cs.foldl (fun s c => disclosedState q s (.inl c) (labels (.inl c)) .none) s
theorem observed_discloseAll {β : Type} (cs : List Coord) (k : List (Coord × Digest) → OracleComp (RWorld U) β)
    (s : State WCoord (Cell U)) :
    observedRun aux q labels table (discloseAll U cs >>= k) s =
      observedRun aux q labels table (k (cs.map fun c => (c, labels (.inl c)))) (discloseStates U q labels s cs) := by
  induction cs generalizing s k with
  | nil => simp only [discloseAll, pure_bind, List.map_nil, discloseStates, List.foldl_nil]
  | cons c rest ih =>
      simp only [discloseAll, bind_assoc]
      rw [observed_discloseReq]
      simp only [pure_bind]
      rw [ih]
      rfl
end Router
end ClaudeWCT.W9.T3.Security.LargeResidual

namespace ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.LargeResidual (State Charge Probe Cell readState probeState stoppedState
  disclosedState tickState)
open ClaudeWCT.W9.T3.Security.FamResidual (observedRun observed_aux observed_read observed_probe_cached
  observed_probe_fresh observed_disclose observed_tick)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
section Router
variable (U : Finset HashInput) (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
  (labels : WCoord → Digest) (table : Cell U → HashOutput)
theorem observed_coinReq {β : Type} (n : Nat) (k : Fin (n + 1) → OracleComp (RWorld U) β) (s : State WCoord (Cell U)) :
    observedRun aux q labels table (coinReq U n >>= k) s =
      ((liftM (aux (.coin n)) : SPMF _) >>= fun v => observedRun aux q labels table (k v) s) :=
  observed_aux aux q labels table (.coin n) k s
theorem observed_readReq {β : Type} (row : Cell U) (ch : Charge) (k : HashOutput → OracleComp (RWorld U) β)
    (s : State WCoord (Cell U)) :
    observedRun aux q labels table (readReq U row ch >>= k) s =
      observedRun aux q labels table (k (table row)) (readState q s row (table row) ch) :=
  observed_read aux q labels table row ch k s
theorem observed_probeReq_fresh {β : Type} (row : Cell U) (test : Probe WCoord)
    (k : HashOutput → OracleComp (RWorld U) β) (s : State WCoord (Cell U)) (h : s.rows row = none) :
    observedRun aux q labels table (probeReq U row test >>= k) s =
      if (test.effF s.candidates).keep labels (table row) then
        observedRun aux q labels table (k (table row)) (probeState s row (test.effF s.candidates) (table row))
      else pure (none, stoppedState s) :=
  observed_probe_fresh aux q labels table row test k s h
theorem observed_discloseReq {β : Type} (c : WCoord) (ch : Charge) (k : Digest → OracleComp (RWorld U) β)
    (s : State WCoord (Cell U)) :
    observedRun aux q labels table (discloseReq U c ch >>= k) s =
      observedRun aux q labels table (k (labels c)) (disclosedState q s c (labels c) ch) :=
  observed_disclose aux q labels table c ch k s
theorem observed_tickReq {β : Type} (ch : Charge) (k : Unit → OracleComp (RWorld U) β) (s : State WCoord (Cell U)) :
    observedRun aux q labels table (tickReq U ch >>= k) s =
      observedRun aux q labels table (k ()) (tickState q s ch) :=
  observed_tick aux q labels table ch k s
def discloseStates (q : Nat) (labels : WCoord → Digest) (s : State WCoord (Cell U)) (cs : List Coord) :
    State WCoord (Cell U) :=
  cs.foldl (fun s c => disclosedState q s (.inl c) (labels (.inl c)) .none) s
theorem observed_discloseAll {β : Type} (cs : List Coord) (k : List (Coord × Digest) → OracleComp (RWorld U) β)
    (s : State WCoord (Cell U)) :
    observedRun aux q labels table (discloseAll U cs >>= k) s =
      observedRun aux q labels table (k (cs.map fun c => (c, labels (.inl c)))) (discloseStates U q labels s cs) := by
  induction cs generalizing s k with
  | nil => simp only [discloseAll, pure_bind, List.map_nil, discloseStates, List.foldl_nil]
  | cons c rest ih =>
      simp only [discloseAll, bind_assoc]
      rw [observed_discloseReq]
      simp only [pure_bind]
      rw [ih]
      rfl
end Router
end ClaudeWCT.W9.T3.Security.LargeResidual.Paired
end
-- ==== merged from T3_Secc_LargeCouplingCell ====
section

namespace SigGolfCandidate.T3.Security.LargeResidual
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (bytesLE bytesLE_length)
open CanonGraph CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def coordVal (s : Secrets) (L : Labels) : Coord → Digest
  | .inl M => (L M).extractLsb' 0 128
  | .inr x => s x
def cellValues : CanonGraph.Node → (Coord → Digest) → HashInput
  | .chain p, v => ChainGraph.row p (v (chainChild p))
  | .leaf L, v => pad64 (Extract.leafInput L.lay L.tree.val L.leaf.val
      ((List.range (chainCount L.lay)).map fun i => v (.inl (.chain (endPoint L i)))))
  | .node n, v => pad64 (nodeInputP 3 n.1.lay.val n.1.tree.val
      (2 ^ (height n.1.lay - n.1.level.val - 1) + n.1.idx.val)
      (((treeChild n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val)).map v).getD 0) 0
      (((treeChild n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val + 1)).map v).getD 0))
  | .ftsLeaf f, v => pad64 (ftsLeafInputP f.index.val f.coord.val f.leaf.val 0 (v (.inr (.inr f))) 0)
  | .ftsNode n, v => pad64 (nodeInputP 10 n.1.coord.val n.1.index.val
      (2 ^ (11 - n.1.level.val - 1) + n.1.idx.val)
      (((ftsChild n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val)).map v).getD 0) 0
      (((ftsChild n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val + 1)).map v).getD 0))
  | .forest index, v => pad64 (Extract.forestInput index.val
      ((List.range 7).map fun c => v (.inl (.ftsNode (ftsRootNode index (fin7 c))))))
theorem treeLabel_eq (s : Secrets) (L : Labels) (lay : Layer) (tree : Fin (2^31)) (level c : Nat) :
    treeLabel L lay tree level c = ((treeChild lay tree level c).map (coordVal s L)).getD 0 := by
  unfold treeLabel treeChild
  by_cases h0 : level = 0
  · rw [if_pos h0, if_pos h0]
    by_cases hc : c < 4096
    · rw [dif_pos hc, dif_pos hc]; rfl
    · rw [dif_neg hc, dif_neg hc]; rfl
  · rw [if_neg h0, if_neg h0]
    cases treeNodeAt lay tree (level - 1) c <;> rfl
theorem ftsLabel_eq (s : Secrets) (L : Labels) (index : Fin (2^31)) (coord : Fin 7) (level c : Nat) :
    ftsLabel L index coord level c = ((ftsChild index coord level c).map (coordVal s L)).getD 0 := by
  unfold ftsLabel ftsChild
  by_cases h0 : level = 0
  · rw [if_pos h0, if_pos h0]
    by_cases hc : c < 2048
    · rw [dif_pos hc, dif_pos hc]; rfl
    · rw [dif_neg hc, dif_neg hc]; rfl
  · rw [if_neg h0, if_neg h0]
    cases ftsNodeAt index coord (level - 1) c <;> rfl
theorem width_ge (lay : Layer) (i : Nat) : 2 ≤ width lay i := by
  unfold width; norm_num
theorem cell_eq_cellValues (s : Secrets) (L : Labels) (N : CanonGraph.Node) :
    cell s N L = cellValues N (coordVal s L) := by
  cases N with
  | chain p =>
      change ChainGraph.row p (ChainGraph.prior (seedsOf s) p (chainLabels L)) = ChainGraph.row p _
      congr 1
      unfold ChainGraph.prior chainChild
      by_cases h0 : p.2.val = 0
      · rw [if_pos h0, if_pos h0]; rfl
      · rw [if_neg h0, if_neg h0]; rfl
  | leaf Lf =>
      change pad64 (Extract.leafInput _ _ _ ((List.range (chainCount Lf.lay)).map (endLabel s L Lf))) = _
      congr 3
      funext i
      unfold endLabel ChainGraph.value
      have hw := width_ge Lf.lay i
      have h1 : 1 ≤ maxDigit Lf.lay i := by
        unfold maxDigit
        split_ifs <;> decide
      rw [if_neg (by omega)]
      simp only [coordVal, endPoint, chainLabels, Nat.sub_sub]
  | node n =>
      change pad64 (nodeInputP 3 _ _ _ (treeLabel L _ _ _ _) 0 (treeLabel L _ _ _ _)) = _
      rw [treeLabel_eq s, treeLabel_eq s]
      rfl
  | ftsLeaf f => rfl
  | ftsNode n =>
      change pad64 (nodeInputP 10 _ _ _ (ftsLabel L _ _ _ _) 0 (ftsLabel L _ _ _ _)) = _
      rw [ftsLabel_eq s, ftsLabel_eq s]
      rfl
  | forest index =>
      change pad64 (Extract.forestInput _ ((List.range 7).map fun c => ftsLabel L index (fin7 c) 11 0)) = _
      congr 3
theorem slotValue_append_left (X Y : HashInput) (k : Nat) (hk : 16 * (k + 1) ≤ X.length) :
    slotValue (X ++ Y) k = slotValue X k := by
  unfold slotValue
  congr 1
  rw [List.drop_append_of_le_length (by omega)]
  rw [List.take_append_of_le_length (by simp; omega)]
theorem slotValue_pad64 (X : HashInput) (k : Nat) (hk : 16 * (k + 1) ≤ X.length) :
    slotValue (pad64 X) k = slotValue X k := slotValue_append_left _ _ k hk
theorem slotValue_bytes_cons (x : Digest) (rest : HashInput) : slotValue (bytesLE 16 x ++ rest) 0 = x := by
  unfold slotValue
  simp only [Nat.mul_zero, List.drop_zero]
  rw [List.take_append_of_le_length (by rw [bytesLE_length])]
  rw [List.take_of_length_le (by rw [bytesLE_length])]
  exact Correctness.readDigest_bytesLE x
theorem slotValue_shift (X Y : HashInput) (k : Nat) (hX : X.length = 16) :
    slotValue (X ++ Y) (k + 1) = slotValue Y k := by
  unfold slotValue
  congr 1
  rw [show 16 * (k + 1) = X.length + 16 * k by omega, List.drop_append,
    List.drop_eq_nil_of_le (by omega), List.nil_append]
  simp
theorem slotValue_flatMap (values : List Digest) (rest : HashInput) (j : Nat) (hj : j < values.length) :
    slotValue (values.flatMap (bytesLE 16) ++ rest) j = values.getD j 0 := by
  induction values generalizing j with
  | nil => simp at hj
  | cons x xs ih =>
      rw [List.flatMap_cons, List.append_assoc]
      cases j with
      | zero => exact slotValue_bytes_cons x _
      | succ j =>
          rw [slotValue_shift _ _ j (bytesLE_length _ _)]
          simp only [List.getD_cons_succ]
          exact ih j (by simpa using hj)
theorem slotValue_block4 (a b c d : Digest) :
    slotValue (block4 a b c d) 0 = a ∧ slotValue (block4 a b c d) 2 = c ∧ slotValue (block4 a b c d) 3 = d := by
  have hl : ∀ x : Digest, (bytesLE 16 x).length = 16 := fun x => bytesLE_length 16 x
  unfold block4
  refine ⟨?_, ?_, ?_⟩
  · rw [List.append_assoc, List.append_assoc]; exact slotValue_bytes_cons a _
  · rw [List.append_assoc, List.append_assoc, slotValue_shift _ _ 1 (hl a), slotValue_shift _ _ 0 (hl b)]
    exact slotValue_bytes_cons c _
  · rw [List.append_assoc, List.append_assoc, slotValue_shift _ _ 2 (hl a), slotValue_shift _ _ 1 (hl b),
      slotValue_shift _ _ 0 (hl c)]
    have := slotValue_bytes_cons d []
    simpa using this
theorem slotValue_listInput (first : Digest) (hdr : BitVec 128) (rest : List Digest) (i : Nat)
    (hi : i ≤ rest.length) : slotValue (pad64 (Extract.listInput first hdr rest)) (listBlock i) =
      (first :: rest).getD i 0 := by
  have hlen := Extract.listInput_length first hdr rest
  unfold listBlock
  by_cases h0 : i = 0
  · subst h0
    rw [if_pos rfl, slotValue_pad64 _ 0 (by omega)]
    unfold Extract.listInput
    rw [List.append_assoc]
    exact slotValue_bytes_cons first _
  · rw [if_neg h0, slotValue_pad64 _ _ (by omega)]
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    unfold Extract.listInput
    rw [List.append_assoc, show j + 1 + 1 = (j + 1) + 1 from rfl,
      slotValue_shift _ _ (j + 1) (bytesLE_length _ _), slotValue_shift _ _ j (bytesLE_length _ _)]
    simp only [List.getD_cons_succ]
    have := slotValue_flatMap rest [] j (by omega)
    simpa using this
theorem chainRow_block4 (p : ChainGraph.Point) (x : Digest) :
    ChainGraph.row p x = block4 0 (chainHeader p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val p.2.val) 0 x := by
  simp only [ChainGraph.row, chainInput, block4, show zero16 = bytesLE 16 (0 : Digest) by decide]
theorem chainCount_pos (lay : Layer) : 0 < chainCount lay := by fin_cases lay <;> decide
end SigGolfCandidate.T3.Security.LargeResidual
end
-- ==== merged from T3_Secc_LargeCouplingSign ====
section

namespace SigGolfCandidate.T3.Security.LargeResidual
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafValue honestPieces forestOpenPrefix
  forestProofPrefix forestRoots forestOpened forestInner forestOuter)
open CanonGraph CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] buildFts buildTree keygen
noncomputable local instance instDecidableEqCache_largeCouplingSign : DecidableEq T3.Cache := Classical.decEq _
section Honest
variable {T : Answers} {labels : Labels}
theorem filterMap_map_getD {α β γ : Type} (l : List α) (f : α → Option β) (v : β → γ) (d : γ)
    (h : ∀ a ∈ l, (f a).isSome) : (l.filterMap f).map v = l.map fun a => ((f a).map v).getD d := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
      have ha := h a List.mem_cons_self
      cases hf : f a with
      | none => rw [hf] at ha; cases ha
      | some b =>
          rw [List.filterMap_cons, hf]
          simp only [List.map_cons]
          rw [ih fun x hx => h x (List.mem_cons_of_mem _ hx), hf]
          rfl
end Honest
end SigGolfCandidate.T3.Security.LargeResidual
end
