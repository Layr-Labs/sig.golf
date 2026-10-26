import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.EvalDist.BitVec
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import RiscvZkvm.Rv64.Execution
import RiscvZkvm.Interpreter.Decode
import Mathlib.Data.List.Sort
import VCVio.EvalDist.Expectation

-- ==== merged from Legacy_Security ====
section

section
namespace SigGolfCandidate.Legacy
def BUDGET_KEYGEN : Nat := 2 ^ 20
def BUDGET_SIGN : Nat := 2 ^ 17
def BUDGET_EXPAND : Nat := 2 ^ 20
def LIFETIME : Nat := 2 ^ 32
def SECURITY_BITS : Nat := 127
def CYCLE_LIMIT : Nat := 2 ^ 32
def MEMORY_BYTES : Nat := 2 ^ 24
def MAX_IMAGE_BYTES : Nat := 2 ^ 20
def MAX_CACHE_BYTES : Nat := 2 ^ 17
def MAX_SIGNATURE_BYTES : Nat := 2 ^ 14
def MAX_WITNESS_BYTES : Nat := 2 ^ 17
noncomputable def FAILURE : ENNReal := 1 / 2 ^ 128
abbrev Byte := BitVec 8
abbrev Bytes (n : Nat) := BitVec (8 * n)
abbrev SecretKey := Bytes 32
abbrev Message := Bytes 32
abbrev PublicKey := Bytes 16
inductive Phase where
  | keygen | sign | expand | verify
  deriving DecidableEq, Repr
def Phase.budget : Phase → Nat
  | .keygen => BUDGET_KEYGEN
  | .sign => BUDGET_SIGN
  | .expand => BUDGET_EXPAND
  | .verify => 0
def Phase.budgeted : List Phase := [.keygen, .sign, .expand]
structure Sizes where
  signature : Nat
  witness : Nat
  cache : Nat
  deriving DecidableEq, Repr
structure Layout where
  message : Nat
  secretKey : Nat
  publicKey : Nat
  cache : Nat
  signature : Nat
  witness : Nat
  deriving DecidableEq, Repr
def Sizes.Valid (sizes : Sizes) : Prop :=
  1 ≤ sizes.signature ∧ sizes.signature ≤ MAX_SIGNATURE_BYTES ∧ sizes.witness ≤ MAX_WITNESS_BYTES ∧
    sizes.cache ≤ MAX_CACHE_BYTES
def witnessCycles (bytes : Nat) : Nat := (bytes + 255) / 256
end SigGolfCandidate.Legacy
end
section
namespace SigGolfCandidate.Legacy
open OracleSpec OracleComp
abbrev Query := (n : Nat) × Bytes (64 * (n + 1))
def Query.blocks (query : Query) : Nat := query.1 + 1
abbrev HashSpec : OracleSpec Query := Query →ₒ BitVec 256
abbrev Hash := QueryImpl HashSpec Id
abbrev World := unifSpec + HashSpec
noncomputable def withRandomOracle {α : Type} (program : OracleComp HashSpec α) : ProbComp α :=
  (simulateQ (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)) program).run' ∅
noncomputable def withRandomness {α : Type} (program : OracleComp World α) : ProbComp α :=
  (simulateQ (unifFwdImpl HashSpec +
    (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))) program).run' ∅
noncomputable def sampleSecretKey : ProbComp SecretKey := $ᵗ SecretKey
end SigGolfCandidate.Legacy
end
section
namespace SigGolfCandidate.Legacy.Riscv
open RiscvZkvm.Rv64 RiscvZkvm.Interpreter OracleComp OracleSpec
structure Image where
  code : List (BitVec 32)
  data : List Byte
  deriving Repr
def Image.byteSize (image : Image) : Nat := 4 * image.code.length + image.data.length
def dataBase (image : Image) : Nat := 16 * ((MEMORY_BYTES - image.data.length) / 16)
def signatureBase (sizes : Sizes) : Nat := 0x60 + 8 * ((sizes.cache + 7) / 8)
def witnessBase (sizes : Sizes) : Nat := signatureBase sizes + 8 * ((sizes.signature + 7) / 8)
def standardLayout (sizes : Sizes) : Layout :=
  ⟨0, 0x20, 0x40, 0x60, signatureBase sizes, witnessBase sizes⟩
def layoutBuffers (layout : Layout) (sizes : Sizes) : List (Nat × Nat) :=
  [(layout.message, 32), (layout.secretKey, 32), (layout.publicKey, 16),
   (layout.cache, sizes.cache), (layout.signature, sizes.signature),
   (layout.witness, sizes.witness)]
def disjointBuffers (left right : Nat × Nat) : Prop :=
  left.2 = 0 ∨ right.2 = 0 ∨ left.1 + left.2 ≤ right.1 ∨ right.1 + right.2 ≤ left.1
instance (left right : Nat × Nat) : Decidable (disjointBuffers left right) := by
  unfold disjointBuffers
  infer_instance
def buffersDisjoint : List (Nat × Nat) → Bool
  | [] => true
  | first :: rest =>
      rest.all (fun second => decide (disjointBuffers first second)) && buffersDisjoint rest
def layoutValid (layout : Layout) (sizes : Sizes) (image : Image) : Prop :=
  (layoutBuffers layout sizes).all (fun buffer =>
    decide (buffer.1 % 8 = 0 ∧ buffer.1 + buffer.2 ≤ dataBase image)) = true ∧
  buffersDisjoint (layoutBuffers layout sizes) = true
instance (layout : Layout) (sizes : Sizes) (image : Image) :
    Decidable (layoutValid layout sizes image) := by
  unfold layoutValid
  infer_instance
def Image.Valid (image : Image) (sizes : Sizes) (layout : Layout) : Prop :=
  image.byteSize < MAX_IMAGE_BYTES ∧ layoutValid layout sizes image
instance (image : Image) (sizes : Sizes) (layout : Layout) : Decidable (image.Valid sizes layout) :=
  inferInstanceAs (Decidable (image.byteSize < MAX_IMAGE_BYTES ∧ layoutValid layout sizes image))
def rangeValid (address : BitVec 64) (bytes : Nat) : Bool :=
  decide (address.toNat + bytes ≤ MEMORY_BYTES)
def accessValid (address : BitVec 64) (bytes : Nat) : Bool :=
  rangeValid address bytes && decide (address.toNat % bytes = 0)
inductive WordOp where
  | add | sub | sll | srl | sra | mul | div | divu | rem | remu
  deriving DecidableEq, Repr
inductive Instruction where
  | base (instruction : Instr)
  | word (op : WordOp) (rd rs1 rs2 : Reg)
  | sraiw (rd rs1 : Reg) (shift : BitVec 5)
  deriving Repr
def decodeInstruction (word : BitVec 32) : Option Instruction := do
  let opcode := (word.extractLsb' 0 7).toNat
  let rd := regOfBits (word.extractLsb' 7 5)
  let rs1 := regOfBits (word.extractLsb' 15 5)
  let rs2 := regOfBits (word.extractLsb' 20 5)
  let f3 := (word.extractLsb' 12 3).toNat
  let f7 := (word.extractLsb' 25 7).toNat
  if opcode = 0x73 then
    if word = 0x00000073 then return .base .ECALL
    else if word = 0x00100073 then return .base .EBREAK
    else none
  else if opcode = 0x3b then
    let op ← match f7, f3 with
      | 0, 0 => some WordOp.add
      | 0x20, 0 => some .sub
      | 0, 1 => some .sll
      | 0, 5 => some .srl
      | 0x20, 5 => some .sra
      | 1, 0 => some .mul
      | 1, 4 => some .div
      | 1, 5 => some .divu
      | 1, 6 => some .rem
      | 1, 7 => some .remu
      | _, _ => none
    return .word op rd rs1 rs2
  else if opcode = 0x1b && f3 = 5 && f7 = 0x20 then
    return .sraiw rd rs1 (word.extractLsb' 20 5)
  else
    return .base (← RiscvZkvm.Interpreter.decode word)
def wordResult (op : WordOp) (a b : BitVec 32) : BitVec 32 :=
  match op with
  | .add => a + b
  | .sub => a - b
  | .sll => a <<< (b.toNat % 32)
  | .srl => a >>> (b.toNat % 32)
  | .sra => a.sshiftRight (b.toNat % 32)
  | .mul => a * b
  | .div => if b = 0 then BitVec.allOnes 32 else a.sdiv b
  | .divu => if b = 0 then BitVec.allOnes 32 else a / b
  | .rem => if b = 0 then a else a.srem b
  | .remu => if b = 0 then a else a % b
def memoryArgumentsValid (state : MachineState) : Instr → Bool
  | .LB _ rs off | .LBU _ rs off | .SB rs _ off =>
      accessValid (state.getReg rs + signExtend12 off) 1
  | .LH _ rs off | .LHU _ rs off | .SH rs _ off =>
      accessValid (state.getReg rs + signExtend12 off) 2
  | .LW _ rs off | .LWU _ rs off | .SW rs _ off =>
      accessValid (state.getReg rs + signExtend12 off) 4
  | .LD _ rs off | .SD rs _ off =>
      accessValid (state.getReg rs + signExtend12 off) 8
  | _ => true
def ordinaryStep (state : MachineState) : Instruction → Option MachineState
  | .base (.ECALL) | .base (.EBREAK) | .base (.CSRS _ _) => none
  | .base (.LI _ _) | .base (.MV _ _) | .base (.NOP) => none
  | .base instruction =>
      if memoryArgumentsValid state instruction then some (execInstrBr state instruction) else none
  | .word op rd rs1 rs2 =>
      let value := wordResult op ((state.getReg rs1).truncate 32) ((state.getReg rs2).truncate 32)
      some ((state.setReg rd (value.signExtend 64)).setPC (state.pc + 4))
  | .sraiw rd rs shift =>
      let value := ((state.getReg rs).truncate 32).sshiftRight shift.toNat
      some ((state.setReg rd (value.signExtend 64)).setPC (state.pc + 4))
def instructionCycles : Instruction → Nat
  | .base (.MUL ..) | .base (.MULH ..) | .base (.MULHSU ..) | .base (.MULHU ..)
  | .base (.DIV ..) | .base (.DIVU ..) | .base (.REM ..) | .base (.REMU ..) => 4
  | .word .mul .. | .word .div .. | .word .divu .. | .word .rem .. | .word .remu .. => 4
  | _ => 1
def fetch (image : Image) (state : MachineState) : Option Instruction := do
  if state.pc.toNat < 0x1000 || state.pc.toNat % 4 != 0 then none else
    let word ← image.code[(state.pc.toNat - 0x1000) / 4]?
    decodeInstruction word
def hashArgumentsValid (state : MachineState) : Bool :=
  let source := state.getReg .x10
  let bytes := (state.getReg .x11).toNat
  let destination := state.getReg .x12
  decide (source.toNat % 8 = 0) && decide (0 < bytes ∧ bytes % 64 = 0) && rangeValid source bytes &&
    accessValid destination 8 && rangeValid destination 32
def hashInput (state : MachineState) : Query :=
  let n := (state.getReg .x11).toNat / 64 - 1
  ⟨n, BitVec.ofNat (8 * (64 * (n + 1))) ((List.range (64 * (n + 1))).foldl (fun acc i =>
    acc + (state.getByte (state.getReg .x10 + BitVec.ofNat 64 i)).toNat * 2 ^ (8 * i)) 0)⟩
def writeHash (state : MachineState) (answer : BitVec 256) : MachineState :=
  (state.writeWords (state.getReg .x12)
    [answer.extractLsb' 0 64, answer.extractLsb' 64 64,
      answer.extractLsb' 128 64, answer.extractLsb' 192 64]).setPC (state.pc + 4)
inductive Exit where
  | success | failure | unfinished
  deriving DecidableEq, Repr
structure Execution where
  exit : Exit
  state : MachineState
  cycles : Nat := 0
  hashCalls : Nat := 0
  hashCompressions : Nat := 0
def Execution.charge (result : Execution) (cycles hashes blocks : Nat) : Execution :=
  { result with
    cycles := cycles + result.cycles
    hashCalls := hashes + result.hashCalls
    hashCompressions := blocks + result.hashCompressions }
def execute : Nat → Image → MachineState → OracleComp HashSpec Execution
  | 0, _, state => pure ⟨.unfinished, state, 0, 0, 0⟩
  | fuel + 1, image, state =>
    match fetch image state with
    | none => pure ⟨.failure, state, 0, 0, 0⟩
    | some (.base .ECALL) =>
      if state.getReg .x5 = 0 && hashArgumentsValid state then do
        let input := hashInput state
        let answer ← HashSpec.query input
        let result ← execute fuel image (writeHash state answer)
        return result.charge (8 * input.blocks) 1 input.blocks
      else if state.getReg .x5 = 1 then
        pure ⟨if state.getReg .x10 = 0 then .success else .failure, state, 1, 0, 0⟩
      else pure ⟨.failure, state, 1, 0, 0⟩
    | some instruction =>
      match ordinaryStep state instruction with
      | none => pure ⟨.failure, state, 1, 0, 0⟩
      | some next => (fun result => result.charge (instructionCycles instruction) 0 0) <$>
          execute fuel image next
end SigGolfCandidate.Legacy.Riscv
end
section
namespace SigGolfCandidate.Legacy
open OracleComp OracleSpec RiscvZkvm.Rv64
structure Submission where
  sizes : Sizes
  layout : Layout
  image : Phase → Riscv.Image
def Submission.score (submission : Submission) (cycles : Nat) : Nat :=
  submission.sizes.signature * cycles
def Input (sizes : Sizes) : Phase → Type
  | .keygen => SecretKey
  | .sign => SecretKey × Bytes sizes.cache × Message
  | .expand => Message × PublicKey × Bytes sizes.signature
  | .verify => Message × PublicKey × Bytes sizes.witness
def Output (sizes : Sizes) : Phase → Type
  | .keygen => PublicKey × Bytes sizes.cache
  | .sign => Bytes sizes.signature
  | .expand => Bytes sizes.witness
  | .verify => Unit
def bytes {n : Nat} (value : Bytes n) : List Byte :=
  (List.range n).map fun i => value.extractLsb' (8 * i) 8
def readBuffer (state : MachineState) (address n : Nat) : Bytes n :=
  BitVec.ofNat (8 * n) ((List.range n).foldl
    (fun acc i => acc + (state.getByte (BitVec.ofNat 64 (address + i))).toNat * 2 ^ (8 * i)) 0)
def inputBuffers (sizes : Sizes) (layout : Layout) :
    (phase : Phase) → Input sizes phase → List (Nat × List Byte)
  | .keygen, secretKey => [(layout.secretKey, bytes secretKey)]
  | .sign, (secretKey, cache, message) =>
      [(layout.secretKey, bytes secretKey), (layout.cache, bytes cache),
        (layout.message, bytes message)]
  | .expand, (message, pk, signature) =>
      [(layout.message, bytes message), (layout.publicKey, bytes pk),
        (layout.signature, bytes signature)]
  | .verify, (message, pk, witness) =>
      [(layout.message, bytes message), (layout.publicKey, bytes pk),
        (layout.witness, bytes witness)]
def initialState (submission : Submission) (phase : Phase) (input : Input submission.sizes phase) :
    Option MachineState :=
  let image := submission.image phase
  if image.Valid submission.sizes submission.layout then
    let blank : MachineState :=
      { regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 }
    let withData := blank.writeBytesAsWords (BitVec.ofNat 64 (Riscv.dataBase image)) image.data
    let loaded := (inputBuffers submission.sizes submission.layout phase input).foldl
      (fun state buffer => state.writeBytesAsWords (BitVec.ofNat 64 buffer.1) buffer.2) withData
    some (loaded.setReg .x2 (BitVec.ofNat 64 (Riscv.dataBase image)))
  else none
def readOutput (sizes : Sizes) (layout : Layout) :
    (phase : Phase) → MachineState → Output sizes phase
  | .keygen, state =>
      (readBuffer state layout.publicKey 16, readBuffer state layout.cache sizes.cache)
  | .sign, state => readBuffer state layout.signature sizes.signature
  | .expand, state => readBuffer state layout.witness sizes.witness
  | .verify, _ => ()
structure RunResult (α : Type) where
  value : Option α
  finished : Bool
  cycles : Nat
  hashCalls : Nat
  hashCompressions : Nat
def Submission.run (submission : Submission) (phase : Phase) (input : Input submission.sizes phase) :
    OracleComp HashSpec (RunResult (Output submission.sizes phase)) := do
  match initialState submission phase input with
  | none => return ⟨none, true, 0, 0, 0⟩
  | some state =>
    let execution ← Riscv.execute CYCLE_LIMIT (submission.image phase) state
    return ⟨if execution.exit = .success then some (readOutput submission.sizes submission.layout phase execution.state)
      else none, execution.exit != .unfinished, execution.cycles, execution.hashCalls,
      execution.hashCompressions⟩
def Submission.runWith (submission : Submission) (hash : Hash) (phase : Phase)
    (input : Input submission.sizes phase) : RunResult (Output submission.sizes phase) :=
  evalWithAnswerFn hash (submission.run phase input)
structure HonestResult where
  success : Bool
  costs : Phase → Nat
  verificationCycles : Nat
def recordCost (costs : Phase → Nat) (phase : Phase) (cost : Nat) : Phase → Nat :=
  fun other => if other = phase then cost else costs other
def Submission.honest (submission : Submission) (secretKey : SecretKey) (message : Message) :
    OracleComp HashSpec HonestResult := do
  let mut costs : Phase → Nat := fun _ => 0
  let keygen ← submission.run .keygen secretKey
  costs := recordCost costs .keygen keygen.hashCompressions
  let some (pk, cache) := keygen.value | return ⟨false, costs, 0⟩
  let sign ← submission.run .sign (secretKey, cache, message)
  costs := recordCost costs .sign sign.hashCompressions
  let some signature := sign.value | return ⟨false, costs, 0⟩
  let expand ← submission.run .expand (message, pk, signature)
  costs := recordCost costs .expand expand.hashCompressions
  let some witness := expand.value | return ⟨false, costs, 0⟩
  let verify ← submission.run .verify (message, pk, witness)
  costs := recordCost costs .verify verify.hashCompressions
  return ⟨verify.value.isSome, costs, verify.cycles + witnessCycles submission.sizes.witness⟩
noncomputable def Submission.honestWorkload (submission : Submission) (secretKey : SecretKey) :
    ProbComp HonestResult := do
  let message ← ($ᵗ Message : ProbComp Message)
  withRandomOracle (submission.honest secretKey message)
structure HonestSummary where
  allSucceed : Bool := true
  maxCosts : Phase → Nat := fun _ => 0
noncomputable def Submission.allMessages (submission : Submission) (secretKey : SecretKey) :
    OracleComp HashSpec HonestSummary :=
  (Finset.univ : Finset Message).toList.foldlM (fun summary message => do
    let result ← submission.honest secretKey message
    return ⟨summary.allSucceed && result.success,
      fun phase => max (summary.maxCosts phase) (result.costs phase)⟩) {}
end SigGolfCandidate.Legacy
end
section
namespace SigGolfCandidate.Legacy
open OracleComp OracleSpec
structure SigningRequest (sizes : Sizes) where
  message : Message
  cache : Bytes sizes.cache
def Submission.signingOracle (submission : Submission) (secretKey : SecretKey)
    (request : SigningRequest submission.sizes) : OracleComp HashSpec (RunResult (Bytes submission.sizes.signature)) :=
  submission.run .sign (secretKey, request.cache, request.message)
inductive Forgery (sizes : Sizes) where
  | witness (message : Message) (witness : Bytes sizes.witness)
  | signature (message : Message) (signature : Bytes sizes.signature)
inductive Action (sizes : Sizes) (state : Type) where
  | submit (candidate : Forgery sizes)
  | hash (input : Query) (resume : BitVec 256 → state)
  | sign (request : SigningRequest sizes) (resume : Option (Bytes sizes.signature) → state)
  | sample (n : Nat) (resume : Fin (n + 1) → state)
  | step (next : state)
structure Adversary (sizes : Sizes) where
  State : Type
  initial : PublicKey → Bytes sizes.cache → State
  step : State → Action sizes State
structure Transcript (sizes : Sizes) where
  signed : List (Message × Bytes sizes.signature) := []
  signingRequests : Nat := 0
  hashCalls : Nat := 0
def Transcript.record {sizes : Sizes} (transcript : Transcript sizes) (message : Message)
    (result : RunResult (Bytes sizes.signature)) : Transcript sizes :=
  { signed := match result.value with
      | none => transcript.signed
      | some signature => (message, signature) :: transcript.signed
    signingRequests := transcript.signingRequests + 1
    hashCalls := transcript.hashCalls + result.hashCalls }
structure AttackResult where
  won : Bool
  hashCalls : Nat
  deriving DecidableEq, Repr
def Transcript.freshMessage {sizes : Sizes} (transcript : Transcript sizes) (message : Message) : Bool :=
  !transcript.signed.any (fun entry => entry.1 == message)
def Transcript.freshSignature {sizes : Sizes} (transcript : Transcript sizes)
    (message : Message) (signature : Bytes sizes.signature) : Bool :=
  !transcript.signed.contains (message, signature)
def Submission.checkForgery (submission : Submission) (pk : PublicKey)
    (transcript : Transcript submission.sizes) : Forgery submission.sizes → OracleComp HashSpec AttackResult
  | .witness message witness => do
      let verify ← submission.run .verify (message, pk, witness)
      return ⟨verify.value.isSome && transcript.freshMessage message,
        transcript.hashCalls + verify.hashCalls⟩
  | .signature message signature => do
      let expand ← submission.run .expand (message, pk, signature)
      let calls := transcript.hashCalls + expand.hashCalls
      let some witness := expand.value | return ⟨false, calls⟩
      let verify ← submission.run .verify (message, pk, witness)
      return ⟨verify.value.isSome && transcript.freshSignature message signature,
        calls + verify.hashCalls⟩
def Submission.interact (submission : Submission) (adversary : Adversary submission.sizes)
    (secretKey : SecretKey) (pk : PublicKey) : Nat → adversary.State → Transcript submission.sizes →
      OracleComp World AttackResult
  | 0, _, transcript => pure ⟨false, transcript.hashCalls⟩
  | rounds + 1, state, transcript =>
      match adversary.step state with
      | .submit candidate => liftM (submission.checkForgery pk transcript candidate)
      | .hash input resume => do
          let answer ← liftM (HashSpec.query input)
          submission.interact adversary secretKey pk rounds (resume answer)
            { transcript with hashCalls := transcript.hashCalls + 1 }
      | .sign request resume => do
          if transcript.signingRequests < LIFETIME then
            let result ← liftM (submission.signingOracle secretKey request)
            submission.interact adversary secretKey pk rounds (resume result.value)
              (transcript.record request.message result)
          else return ⟨false, transcript.hashCalls⟩
      | .sample n resume => do
          let answer ← liftM (unifSpec.query n)
          submission.interact adversary secretKey pk rounds (resume answer) transcript
      | .step next => submission.interact adversary secretKey pk rounds next transcript
noncomputable def Submission.securityExperiment (submission : Submission)
    (adversary : Adversary submission.sizes) (rounds : Nat) : ProbComp AttackResult :=
  withRandomness do
    let secretKey ← liftM sampleSecretKey
    let keygen ← liftM (submission.run .keygen secretKey)
    let some (pk, cache) := keygen.value | return ⟨false, keygen.hashCalls⟩
    submission.interact adversary secretKey pk rounds (adversary.initial pk cache)
      { hashCalls := keygen.hashCalls }
def Submission.Secure (submission : Submission) : Prop :=
  ∀ (adversary : Adversary submission.sizes) (rounds Q : Nat), 1 ≤ Q →
    Pr[fun result => result.won = true ∧ result.hashCalls ≤ Q |
      submission.securityExperiment adversary rounds] ≤ (Q : ENNReal) / 2 ^ SECURITY_BITS
end SigGolfCandidate.Legacy
end
end
-- ==== merged from Legacy ====
section

section
namespace SigGolfCandidate.Legacy
open OracleComp
def Submission.Admissible (submission : Submission) : Prop :=
  submission.sizes.Valid ∧ ∀ phase, (submission.image phase).Valid submission.sizes submission.layout
def Submission.Terminates (submission : Submission) : Prop :=
  ∀ (hash : Hash) (phase : Phase) (input : Input submission.sizes phase),
    let result := submission.runWith hash phase input
    result.finished = true ∧ result.cycles < CYCLE_LIMIT
def Submission.Complete (submission : Submission) : Prop :=
  ∀ secretKey, 1 - FAILURE ≤ Pr[fun summary => summary.allSucceed = true |
    withRandomOracle (submission.allMessages secretKey)]
def Submission.CompressionBounds (submission : Submission) : Prop :=
  ∀ secretKey phase, phase ∈ Phase.budgeted →
    OracleComp.EvalDist.expectedValue (submission.honestWorkload secretKey)
      (fun result => ENNReal.ofReal (Real.rpow 2
        ((result.costs phase : ℝ) / (phase.budget : ℝ)))) ≤ 2
def Submission.VerificationBound (submission : Submission) (C : Nat) : Prop :=
  ∀ (hash : Hash) secretKey message,
    let result := evalWithAnswerFn hash (submission.honest secretKey message)
    result.success = true → result.verificationCycles ≤ C
structure Certificate (submission : Submission) (C : Nat) : Prop where
  admissible : submission.Admissible
  termination : submission.Terminates
  completeness : submission.Complete
  compressionBounds : submission.CompressionBounds
  security : submission.Secure
  verificationBound : submission.VerificationBound C
end SigGolfCandidate.Legacy
end
section
end
end
-- ==== merged from Budget_Bytes ====
section

section


section
namespace SigGolfCandidate
def CACHE_BYTES : Nat := 2 ^ 17
abbrev BudgetCache := SigGolfCandidate.Legacy.Bytes CACHE_BYTES
end SigGolfCandidate
end
section
namespace SigGolfCandidate.Ref
open SigGolfCandidate.Legacy OracleComp OracleSpec
abbrev Val := List Byte
def byte (n : Nat) : Byte := BitVec.ofNat 8 n
def leBytes (k v : Nat) : List Byte := (List.range k).map fun i => byte (v / 256 ^ i)
def le32 (v : Nat) : List Byte := leBytes 4 v
def leNat : List Byte → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leNat bs
def zeros (k : Nat) : List Byte := List.replicate k 0
def toList {n : Nat} (x : Bytes n) : List Byte := SigGolfCandidate.Legacy.bytes x
def ofList (n : Nat) (l : List Byte) : Bytes n := BitVec.ofNat (8 * n) (leNat l)
def answerBytes (k : Nat) (a : BitVec 256) : List Byte :=
  (List.range k).map fun i => a.extractLsb' (8 * i) 8
def slice (l : List Byte) (off len : Nat) : List Byte := (l.drop off).take len
def nChains : Nat := 42
def targetSum : Nat := 181
abbrev target : Nat := targetSum
def nLayers : Nat := 5
def heights : List Nat := [11,6,6,6,5]
def totalH : Nat := 34
def porsH : Nat := 14
def porsK : Nat := 15
def porsT : Nat := 2 ^ porsH
def porsM : Nat := 118
def porsSegs : Nat := 2 * porsK - 1
def aMax : Nat := 2 ^ 20
def cMax : Nat := 2 ^ 22
def sigBytes : Nat := 6048
def witBytes : Nat := 6348
def height (lay : Nat) : Nat := heights.getD lay 0
def shiftBelow (lay : Nat) : Nat := ((List.range nLayers).filter (lay < ·)).foldr (height · + ·) 0
def route (idx lay : Nat) : Nat × Nat :=
  (idx / 2 ^ shiftBelow lay % 2 ^ height lay, idx / 2 ^ (shiftBelow lay + height lay))
abbrev topH : Nat := height 0
def topN (l : Nat) : Nat := ((List.range l).map fun k => 2 ^ (topH - k)).sum
def regionBytes : Nat := 16 * topN topH
def cacheBytes : Nat := CACHE_BYTES
def cacheNodeOff (l j : Nat) : Nat := 32 + 16 * (topN l + j)
def cacheNode (cache : List Byte) (l j : Nat) : Val := slice cache (cacheNodeOff l j) 16
def cacheTag (cache : List Byte) : List Byte := slice cache 0 32
def cacheRegion (cache : List Byte) : List Byte := slice cache 32 regionBytes
def xorBytes (a b : List Byte) : List Byte := List.zipWith (· ^^^ ·) a b
def tweak (t lay tau p j : Nat) : List Byte :=
  [byte 1, byte t, byte lay, byte (tau / 2 ^ 32)] ++ le32 p ++ le32 (tau % 2 ^ 32) ++ le32 j
def P : List Byte := zeros 16
def thInput (tw payload : List Byte) : List Byte := tw ++ P ++ payload
def padBlocks (len : Nat) : Nat := (len + 63) / 64 - 1
def padTo64 (x : List Byte) : List Byte :=
  x ++ zeros (64 * (padBlocks x.length + 1) - x.length)
def pad64 (x : List Byte) : Query := ⟨padBlocks x.length, ofList _ (padTo64 x)⟩
def IsChainFmt (x : List Byte) : Prop := x.length = 48 ∧ x.getD 1 0 = byte 1
instance (x : List Byte) : Decidable (IsChainFmt x) :=
  inferInstanceAs (Decidable (x.length = 48 ∧ x.getD 1 0 = byte 1))
def IsNodeFmt (x : List Byte) : Prop := x.length = 64 ∧ x.getD 1 0 = byte 3
instance (x : List Byte) : Decidable (IsNodeFmt x) :=
  inferInstanceAs (Decidable (x.length = 64 ∧ x.getD 1 0 = byte 3))
def IsDigestFmt (x : List Byte) : Prop := x.length = 96 ∧ x.getD 1 0 = byte 12
instance (x : List Byte) : Decidable (IsDigestFmt x) :=
  inferInstanceAs (Decidable (x.length = 96 ∧ x.getD 1 0 = byte 12))
def splitP (p : Nat) : Nat := p % 8 + 256 * (p / 8)
def heapIndex (h lam j : Nat) : Nat := 2 ^ (h - lam) + j
def nodeHeight (x : List Byte) : Nat := height (x.getD 2 0).toNat
def chainBlock (x : List Byte) : List Byte :=
  x.take 4 ++ le32 (splitP (leNat (slice x 4 4))) ++ slice x 8 8 ++ zeros 32 ++ x.drop 32
def nodeBlock (x : List Byte) : List Byte :=
  x.take 4 ++ le32 0 ++ slice x 8 4 ++
    le32 (heapIndex (nodeHeight x) (leNat (slice x 4 4)) (leNat (slice x 12 4))) ++ x.drop 16
def digestBlock (x : List Byte) : List Byte := x.take 16 ++ slice x 32 16 ++ x.drop 64
def fmt (x : List Byte) : Query :=
  if IsChainFmt x then ⟨0, ofList _ (chainBlock x)⟩
  else if IsNodeFmt x then ⟨0, ofList _ (nodeBlock x)⟩
  else if IsDigestFmt x then ⟨0, ofList _ (digestBlock x)⟩
  else pad64 x
def fmtList (x : List Byte) : List Byte :=
  if IsChainFmt x then chainBlock x
  else if IsNodeFmt x then nodeBlock x
  else if IsDigestFmt x then digestBlock x
  else padTo64 x
def H (x : List Byte) : OracleComp HashSpec (BitVec 256) := HashSpec.query (fmt x)
def prf2 (x : List Byte) : OracleComp HashSpec (Val × Val) := do
  let a ← H x
  pure ((answerBytes 32 a).take 16, (answerBytes 32 a).drop 16)
def hash16 (x : List Byte) : OracleComp HashSpec Val := do
  let a ← H x
  pure (answerBytes 16 a)
def th (tw payload : List Byte) : OracleComp HashSpec Val := hash16 (thInput tw payload)
def prfInput (S : List Byte) (lay tau e i : Nat) : List Byte := thInput (tweak 0 lay tau i e) S
def chainInput (lay tau e i mu : Nat) (v : Val) : List Byte :=
  thInput (tweak 1 lay tau (8 * i + mu - 1) e) v
def leafInput (lay tau e : Nat) (ends : List Val) : List Byte :=
  thInput (tweak 2 lay tau 0 e) ends.flatten
def nodeInput (lay tau lam j : Nat) (l r : Val) : List Byte :=
  thInput (tweak 3 lay tau lam j) (l ++ r)
def encInput (lay tau e : Nat) (M : Val) (c : Nat) : List Byte :=
  thInput (tweak 4 lay tau 0 e) (M ++ le32 c)
def rndInput (S m : List Byte) (a : Nat) : List Byte :=
  [byte 1, byte 7] ++ S.take 26 ++ m ++ le32 a
def porsPrfInput (S : List Byte) (idx q : Nat) : List Byte := thInput (tweak 8 0 idx 0 q) S
def porsLeafInput (idx j : Nat) (s : Val) : List Byte := thInput (tweak 9 0 idx 0 j) s
def porsNodeInput (idx H : Nat) (l r : Val) : List Byte := thInput (tweak 10 0 idx 0 H) (l ++ r)
def digestInput (rho m : List Byte) : List Byte := thInput (tweak 12 0 0 0 0) (rho ++ zeros 16 ++ m)
def maskInput (S : List Byte) (l j : Nat) : List Byte := thInput (tweak 13 0 0 l j) S
def macInput (S region : List Byte) : List Byte := thInput (tweak 14 0 0 0 0) (S ++ region)
def digest (rho m : List Byte) : OracleComp HashSpec Nat := do
  let a ← H (digestInput rho m)
  pure a.toNat
def idxOf (N : Nat) : Nat := N % 2 ^ totalH
def leafOf (N r : Nat) : Nat := N / 2 ^ (totalH + porsH * r) % 2 ^ porsH
def leavesOf (N : Nat) : List Nat := (List.range porsK).map (leafOf N)
def bitLen (x : Nat) : Nat := if x = 0 then 0 else Nat.log2 x + 1
def octopusSize (vs : List Nat) : Nat :=
  porsH + 2 + (List.zipWith (fun a b => bitLen (a ^^^ b)) vs vs.tail).sum - 2 * vs.length
def sortLeaves (v : List Nat) : List Nat := v.insertionSort (· ≤ ·)
def admissible (N : Nat) : Bool :=
  decide (leavesOf N).Nodup && decide (octopusSize (sortLeaves (leavesOf N)) ≤ porsM)
structure SchedState where
  segs : List Nat
  reads : List (Nat × Nat)
  stack : List Nat
deriving DecidableEq, Repr
def schedStep (x : SchedState × Nat × Nat × Nat) (h : Nat) : SchedState × Nat × Nat × Nat :=
  let (st, E, cnt, t) := x
  match st.stack with
  | Q :: rest =>
    if Q = E then ({ st with segs := st.segs ++ [cnt ||| 16 ||| 32 * t], stack := rest },
      E / 2, 0, E / 2 % 2)
    else ({ st with reads := st.reads ++ [(h, (E ^^^ 1) - porsT / 2 ^ h)] }, E / 2, cnt + 1, t)
  | [] => ({ st with reads := st.reads ++ [(h, (E ^^^ 1) - porsT / 2 ^ h)] }, E / 2, cnt + 1, t)
def schedLeaf (vs : List Nat) (st : SchedState) (s : Nat) : SchedState :=
  let k := vs.length
  let E := porsT ||| vs.getD s 0
  let top := if s + 1 < k then bitLen (vs.getD s 0 ^^^ vs.getD (s + 1) 0) - 1 else porsH
  let (st, E, cnt, t) := (List.range top).foldl schedStep (st, E, 0, E % 2)
  let st := { st with segs := st.segs ++ [cnt ||| 32 * t] }
  if s + 1 < k then { st with stack := (E ^^^ 1) :: st.stack } else st
def schedule (vs : List Nat) : List Nat × List (Nat × Nat) :=
  let st := (List.range vs.length).foldl (schedLeaf vs) ⟨[], [], []⟩
  (st.segs, st.reads)
def digitsOfWord (d : Nat) : List Nat := (List.range 21).map fun r => d / 8 ^ r % 8
def decodeDigits (v : Val) : Option (List Nat) :=
  let d0 := leNat (slice v 0 8)
  let d1 := leNat (slice v 8 8)
  if d0 < 2 ^ 63 ∧ d1 < 2 ^ 63 then
    let x := digitsOfWord d0 ++ digitsOfWord d1
    if x.sum = targetSum then some x else none
  else none
end SigGolfCandidate.Ref
end
end

section


section
namespace SigGolfCandidate.Ref
open SigGolfCandidate.Legacy OracleComp OracleSpec
abbrev NodeFmt := Nat → Nat → Val → Val → List Byte
def buildLevel (node : NodeFmt) (lam : Nat) (level : List Val) :
    OracleComp HashSpec (List Val) :=
  (List.range (level.length / 2)).foldlM (fun acc j => do
    let v ← hash16 (node lam j (level.getD (2 * j) []) (level.getD (2 * j + 1) []))
    pure (acc ++ [v])) []
def levelStep (node : NodeFmt) (cap : Nat) (st : List Val × List Val) (lam : Nat) :
    OracleComp HashSpec (List Val × List Val) := do
  let path := st.2 ++ [st.1.getD ((cap / 2 ^ (lam - 1)) ^^^ 1) []]
  let level ← buildLevel node lam st.1
  pure (level, path)
def buildLevels (node : NodeFmt) (cap h : Nat) (leaves : List Val) :
    OracleComp HashSpec (Val × List Val) := do
  let st ← (List.range' 1 h).foldlM (levelStep node cap) (leaves, [])
  pure (st.1.getD 0 [], st.2)
def chainSteps (lay tau e i x : Nat) (v : Val) : OracleComp HashSpec (Val × Val) :=
  (List.range' 1 7).foldlM (fun (st : Val × Val) mu => do
    let v ← hash16 (chainInput lay tau e i mu st.1)
    pure (v, if mu = x then v else st.2)) (v, v)
def buildLeaf (S : List Byte) (lay tau e : Nat) (x : List Nat) :
    OracleComp HashSpec (Val × List Val) := do
  let st ← (List.range (nChains / 2)).foldlM (fun (st : List Val × List Val) k => do
    let (s0, s1) ← prf2 (prfInput S lay tau e k)
    let (v0, c0) ← chainSteps lay tau e (2 * k) (x.getD (2 * k) 0) s0
    let (v1, c1) ← chainSteps lay tau e (2 * k + 1) (x.getD (2 * k + 1) 0) s1
    pure (st.1 ++ [v0, v1], st.2 ++ [c0, c1])) ([], [])
  let leaf ← hash16 (leafInput lay tau e st.1)
  pure (leaf, st.2)
def buildLeaves (S : List Byte) (lay tau h cap : Nat) (x : List Nat) :
    OracleComp HashSpec (List Val × List Val) :=
  (List.range (2 ^ h)).foldlM (fun (st : List Val × List Val) e => do
    let (leaf, c) ← buildLeaf S lay tau e x
    pure (st.1 ++ [leaf], if e = cap then c else st.2)) ([], [])
def buildTree (S : List Byte) (lay tau h cap : Nat) (x : List Nat) :
    OracleComp HashSpec (Val × List Val × List Val) := do
  let (leaves, vals) ← buildLeaves S lay tau h cap x
  let (root, path) ← buildLevels (nodeInput lay tau) cap h leaves
  pure (root, vals, path)
def buildAllLevels (node : NodeFmt) (h : Nat) (leaves : List Val) :
    OracleComp HashSpec (List (List Val)) :=
  (List.range' 1 h).foldlM (fun (levels : List (List Val)) lam => do
    let level ← buildLevel node lam (levels.getD (lam - 1) [])
    pure (levels ++ [level])) [leaves]
def maskLevel (S : List Byte) (l : Nat) (level : List Val) : OracleComp HashSpec (List Val) :=
  (List.range level.length).foldlM (fun acc j => do
    let mk ← hash16 (maskInput S l j)
    pure (acc ++ [xorBytes (level.getD j []) mk])) []
def keygenList (S : List Byte) : OracleComp HashSpec (Val × List Byte) := do
  let (leaves, _) ← buildLeaves S 0 0 topH 0 []
  let levels ← buildAllLevels (nodeInput 0 0) topH leaves
  let masked ← (List.range topH).foldlM (fun (acc : List Val) l => do
    let ml ← maskLevel S l (levels.getD l [])
    pure (acc ++ ml)) []
  let region := masked.flatten
  let tag ← H (macInput S region)
  pure ((levels.getD topH []).getD 0 [],
    toList (n := 32) tag ++ region ++ zeros (cacheBytes - 32 - regionBytes))
def keygenRef (sk : Bytes 32) : OracleComp HashSpec (Bytes 16 × BudgetCache) := do
  let (root, cache) ← keygenList (toList sk)
  pure (ofList 16 root, ofList CACHE_BYTES cache)
def searchDigest (S m : List Byte) (a : Nat) : Nat → OracleComp HashSpec (Option (Val × Nat))
  | 0 => pure none
  | fuel + 1 => do
    let rho ← hash16 (rndInput S m a)
    let N ← digest rho m
    if admissible N then pure (some (rho, N)) else searchDigest S m (a + 1) fuel
def buildPorsLeaves (S : List Byte) (idx : Nat) : OracleComp HashSpec (List Val × List Val) :=
  (List.range (porsT / 2)).foldlM (fun (st : List Val × List Val) q => do
    let (s0, s1) ← prf2 (porsPrfInput S idx q)
    let l0 ← hash16 (porsLeafInput idx (2 * q) s0)
    let l1 ← hash16 (porsLeafInput idx (2 * q + 1) s1)
    pure (st.1 ++ [l0, l1], st.2 ++ [s0, s1])) ([], [])
def porsNodeFmt (idx : Nat) : NodeFmt := fun lam j l r => porsNodeInput idx (heapIndex porsH lam j) l r
def buildPorsTree (S : List Byte) (idx : Nat) :
    OracleComp HashSpec (List (List Val) × List Val) := do
  let (leaves, secrets) ← buildPorsLeaves S idx
  let levels ← buildAllLevels (porsNodeFmt idx) porsH leaves
  pure (levels, secrets)
def porsOpening (vs : List Nat) (levels : List (List Val)) (secrets : List Val) : List Val :=
  let fts := vs.map (fun x => secrets.getD x []) ++
    (schedule vs).2.map (fun hj => (levels.getD hj.1 []).getD hj.2 [])
  fts ++ List.replicate (porsK + porsM - fts.length) (zeros 16)
def searchCounter (lay tau e : Nat) (M : Val) (c : Nat) :
    Nat → OracleComp HashSpec (Option (Nat × List Nat))
  | 0 => pure none
  | fuel + 1 => do
    let d ← hash16 (encInput lay tau e M c)
    match decodeDigits d with
    | some x => pure (some (c, x))
    | none => searchCounter lay tau e M (c + 1) fuel
abbrev LayerSig := Nat × List Val × List Val
def chainTo (lay tau e i x : Nat) (v : Val) : OracleComp HashSpec Val :=
  (List.range' 1 x).foldlM (fun v mu => hash16 (chainInput lay tau e i mu v)) v
def topPath (S cache : List Byte) (e : Nat) : OracleComp HashSpec (List Val) :=
  (List.range topH).foldlM (fun acc l => do
    let s := (e / 2 ^ l) ^^^ 1
    let mk ← hash16 (maskInput S l s)
    pure (acc ++ [xorBytes (cacheNode cache l s) mk])) []
def signTop (S cache : List Byte) (idx : Nat) (M : Val) :
    OracleComp HashSpec (Option (List LayerSig)) := do
  let (e, tau) := route idx 0
  match ← searchCounter 0 tau e M 0 cMax with
  | none => pure none
  | some (c, x) =>
    let vals ← (List.range (nChains / 2)).foldlM (fun acc k => do
      let (s0, s1) ← prf2 (prfInput S 0 tau e k)
      let v0 ← chainTo 0 tau e (2 * k) (x.getD (2 * k) 0) s0
      let v1 ← chainTo 0 tau e (2 * k + 1) (x.getD (2 * k + 1) 0) s1
      pure (acc ++ [v0, v1])) []
    let path ← topPath S cache e
    pure (some [(c, vals, path)])
def signLayers (S cache : List Byte) (idx : Nat) :
    Nat → Val → OracleComp HashSpec (Option (List LayerSig))
  | 0, M => signTop S cache idx M
  | lay + 1, M => do
    let (e, tau) := route idx (lay + 1)
    match ← searchCounter (lay + 1) tau e M 0 cMax with
    | none => pure none
    | some (c, x) =>
      let (root, vals, path) ← buildTree S (lay + 1) tau (height (lay + 1)) e x
      match ← signLayers S cache idx lay root with
      | none => pure none
      | some rest => pure (some (rest ++ [(c, vals, path)]))
def serialize (rho : Val) (fts : List Val) (lays : List LayerSig) : List Byte :=
  rho ++ fts.flatten ++
    (lays.map fun l => l.2.1.flatten ++ l.2.2.flatten).flatten
def signList (S cache m : List Byte) : OracleComp HashSpec (Option (List Byte)) := do
  let tag ← H (macInput S (cacheRegion cache))
  if toList (n := 32) tag = cacheTag cache then
    match ← searchDigest S m 0 aMax with
    | none => pure none
    | some (rho, N) =>
      let (levels, secrets) ← buildPorsTree S (idxOf N)
      let M := (levels.getD porsH []).getD 0 []
      let fts := porsOpening (sortLeaves (leavesOf N)) levels secrets
      match ← signLayers S cache (idxOf N) (nLayers - 1) M with
      | none => pure none
      | some lays => pure (some (serialize rho fts lays))
  else pure none
def signRef (sk : Bytes 32) (cache : BudgetCache) (m : Bytes 32) :
    OracleComp HashSpec (Option (Bytes 6048)) := do
  let r ← signList (toList sk) (toList cache) (toList m)
  pure (r.map (ofList 6048))
def sigLayerBytes (lay : Nat) : Nat := 4 + 16 * nChains + 16 * height lay
def bodyBytes (lay : Nat) : Nat := 16 * nChains + 16 * height lay
def headBytes : Nat := 16 + 16 * (porsK + porsM)
def sigLayerOff (lay : Nat) : Nat := headBytes + ((List.range lay).map bodyBytes).sum
def sigRho (sig : List Byte) : Val := slice sig 0 16
def sigItem (sig : List Byte) (i : Nat) : Val := slice sig (16 + 16 * i) 16
def sigAuth (sig : List Byte) (i : Nat) : Val := sigItem sig (porsK + i)
def sigLayerBody (sig : List Byte) (lay : Nat) : List Byte := slice sig (sigLayerOff lay) (bodyBytes lay)
def wPi : Nat := 16
def wSec : Nat := 32
def wStream : Nat := wSec + 16 * porsK
def streamBytes : Nat := 8 * porsSegs + 16 * 120
def wLayers : Nat := wStream + streamBytes
def witLayerOff (lay : Nat) : Nat := wLayers + ((List.range lay).map fun l => sigLayerBytes l - 4).sum
def witCounters : Nat := witLayerOff nLayers
def streamStep (sig : List Byte) (st : List Byte × Nat) (b : Nat) : List Byte × Nat :=
  (st.1 ++ [byte b] ++ zeros 7 ++ ((List.range (b % 16)).map fun i => sigAuth sig (st.2 + i)).flatten,
    st.2 + b % 16)
def segStream (sig : List Byte) (segs : List Nat) : List Byte := (segs.foldl (streamStep sig) ([], 0)).1
def witnessBody (sig : List Byte) (v vs segs : List Nat) : List Byte :=
  sigRho sig ++ vs.map (fun x => byte (8 * v.idxOf x)) ++ zeros (wSec - wPi - porsK) ++
    ((List.range porsK).map (sigItem sig)).flatten ++
    (segStream sig segs ++ zeros streamBytes).take streamBytes ++
    ((List.range nLayers).map (sigLayerBody sig)).flatten
def witnessList (sig : List Byte) (v vs segs : List Nat) : List Byte :=
  witnessBody sig v vs segs ++ zeros (4 * nLayers)
def expandOf (sig : List Byte) (N : Nat) : Option (List Byte) :=
  let v := leavesOf N
  if !decide v.Nodup then none
  else
    let vs := sortLeaves v
    if octopusSize vs > porsM then none
    else
      let (segs, reads) := schedule vs
      let n := reads.length
      if !(List.range' n (porsM - n)).all (fun i => sigAuth sig i == zeros 16) then none
      else some (witnessList sig v vs segs)
def witRho (w : List Byte) : Val := slice w 0 16
def witPi (w : List Byte) (s : Nat) : Nat := (w.getD (wPi + s) 0).toNat
def witSecret (w : List Byte) (s : Nat) : Val := slice w (wSec + 16 * s) 16
def wbyte (w : List Byte) (off : Nat) : Nat := (w.getD off 0).toNat
def wbytes (w : List Byte) (off n : Nat) : Val := (List.range n).map fun i => w.getD (off + i) 0
def witChain (w : List Byte) (lay i : Nat) : Val := slice w (witLayerOff lay + 16 * i) 16
def witSib (w : List Byte) (lay l : Nat) : Val := slice w (witLayerOff lay + 672 + 16 * l) 16
def witPath (w : List Byte) (lay : Nat) : List Val := (List.range (height lay)).map (witSib w lay)
def witCounter (w : List Byte) (lay : Nat) : Nat := leNat (slice w (witCounters + 4 * lay) 4)
def countersOk (w : List Byte) : Bool := (List.range nLayers).all fun lay => witCounter w lay < cMax
def foldPath (node : NodeFmt) (leaf : Nat) (v : Val) (path : List Val) : OracleComp HashSpec Val :=
  (List.range path.length).foldlM (fun v lam =>
    let sib := path.getD lam []
    let j := leaf / 2 ^ (lam + 1)
    if leaf / 2 ^ lam % 2 = 1 then hash16 (node (lam + 1) j sib v)
    else hash16 (node (lam + 1) j v sib)) v
inductive Pending where
  | leaf (x : Nat) (s : Val)
  | merge (H : Nat) (l : Val)
def pendingHash (idx : Nat) (node : Val) : Pending → OracleComp HashSpec Val
  | .leaf x s => hash16 (porsLeafInput idx x s)
  | .merge H l => hash16 (porsNodeInput idx H l node)
def segFolds (idx : Nat) (w : List Byte) (ptr a : Nat) (node : Val) (E : Nat) :
    OracleComp HashSpec (Val × Nat) :=
  (List.range a).foldlM (fun (st : Val × Nat) i =>
    let sib := wbytes w (ptr + 8 + 16 * i) 16
    if st.2 % 2 = 1 then do
      let v ← hash16 (porsNodeInput idx (st.2 / 2) sib st.1)
      pure (v, st.2 / 2)
    else do
      let v ← hash16 (porsNodeInput idx (st.2 / 2) st.1 sib)
      pure (v, st.2 / 2)) (node, E)
def segment (idx : Nat) (w : List Byte) (ptr E folds : Nat) (pending : Pending) (node : Val) :
    OracleComp HashSpec (Option (Nat × Nat × Nat × Val × Bool)) := do
  let b := wbyte w ptr
  let a := b % 16
  let merge := b / 16 % 2
  let t := b / 32 % 2
  if a > porsH then pure none
  else if 0 < a ∧ t ≠ E % 2 then pure none
  else
    let node ← pendingHash idx node pending
    let (node, E) ← segFolds idx w ptr a node E
    pure (some (ptr + 8 + 16 * a, E, folds + a, node, merge = 1))
def segLoop (idx : Nat) (w : List Byte) :
    Nat → Nat → Nat → Pending → Val → List (Val × Nat) →
      OracleComp HashSpec (Option (Nat × Nat × Nat × Val × List (Val × Nat)))
  | ptr, E, folds, pending, node, [] => do
    match ← segment idx w ptr E folds pending node with
    | none => pure none
    | some (ptr, E, folds, node, merge) =>
      if merge then pure none else pure (some (ptr, E, folds, node, []))
  | ptr, E, folds, pending, node, (pnode, Q) :: rest => do
    match ← segment idx w ptr E folds pending node with
    | none => pure none
    | some (ptr, E, folds, node, merge) =>
      if !merge then pure (some (ptr, E, folds, node, (pnode, Q) :: rest))
      else if Q ≠ E then pure none
      else segLoop idx w ptr (E / 2) folds (.merge (E / 2) pnode) node rest
structure PorsState where
  ptr : Nat
  prev : Nat
  E : Nat
  folds : Nat
  node : Val
  stack : List (Val × Nat)
def porsLeaves (idx : Nat) (v : List Nat) (w : List Byte) :
    List Nat → PorsState → OracleComp HashSpec (Option PorsState)
  | [], st => pure (some st)
  | s :: rest, st => do
    let x := (v ++ [porsT]).getD (witPi w s / 8 % 16) 0
    if s ≠ 0 ∧ ¬ st.prev < x then pure none
    else if s = porsK - 1 ∧ ¬ x < porsT then pure none
    else
      match ← segLoop idx w st.ptr (porsT ||| x) st.folds (.leaf x (witSecret w s)) st.node
          st.stack with
      | none => pure none
      | some (ptr, E, folds, node, stack) =>
        let stack := if s < porsK - 1 then (node, E ^^^ 1) :: stack else stack
        porsLeaves idx v w rest ⟨ptr, x, E, folds, node, stack⟩
def porsRoot (idx : Nat) (v : List Nat) (w : List Byte) : OracleComp HashSpec (Option Val) := do
  match ← porsLeaves idx v w (List.range porsK) ⟨wStream, 0, 0, 0, [], []⟩ with
  | none => pure none
  | some st =>
    if st.folds > porsM ∨ st.E ≠ 1 ∨ st.stack ≠ [] then pure none else pure (some st.node)
def chainFrom (lay tau e i x : Nat) (v : Val) : OracleComp HashSpec Val :=
  (List.range' (x + 1) (7 - x)).foldlM (fun v mu => hash16 (chainInput lay tau e i mu v)) v
def verifyLeaf (w : List Byte) (lay tau e : Nat) (x : List Nat) : OracleComp HashSpec Val := do
  let ends ← (List.range nChains).foldlM (fun ends i => do
    let v ← chainFrom lay tau e i (x.getD i 0) (witChain w lay i)
    pure (ends ++ [v])) []
  hash16 (leafInput lay tau e ends)
def verifyLayers (w : List Byte) (idx : Nat) : Nat → Val → OracleComp HashSpec (Option Val)
  | 0, M => pure (some M)
  | lay + 1, M => do
    let (e, tau) := route idx lay
    let d ← hash16 (encInput lay tau e M (witCounter w lay))
    match decodeDigits d with
    | none => pure none
    | some x =>
      let leaf ← verifyLeaf w lay tau e x
      let root ← foldPath (nodeInput lay tau) e leaf (witPath w lay)
      verifyLayers w idx lay root
def verifyList (m pk w : List Byte) : OracleComp HashSpec Bool := do
  if !countersOk w then return false
  let N ← digest (witRho w) m
  match ← porsRoot (idxOf N) (leavesOf N) w with
  | none => pure false
  | some M =>
    match ← verifyLayers w (idxOf N) nLayers M with
    | none => pure false
    | some root => pure (root == pk)
def verifyRef (m : Bytes 32) (pk : Bytes 16) (w : Bytes 6348) : OracleComp HashSpec Bool :=
  verifyList (toList m) (toList pk) (toList w)
def expandLayers (w : List Byte) (idx : Nat) : Nat → Val → OracleComp HashSpec (Option (List Nat))
  | 0, _ => pure (some [])
  | 1, M => do
    let (e, tau) := route idx 0
    match ← searchCounter 0 tau e M 0 cMax with
    | none => pure none
    | some (c, _) => pure (some [c])
  | lay + 2, M => do
    let (e, tau) := route idx (lay + 1)
    match ← searchCounter (lay + 1) tau e M 0 cMax with
    | none => pure none
    | some (c, x) =>
      let leaf ← verifyLeaf w (lay + 1) tau e x
      let root ← foldPath (nodeInput (lay + 1) tau) e leaf (witPath w (lay + 1))
      match ← expandLayers w idx (lay + 1) root with
      | none => pure none
      | some cs => pure (some (cs ++ [c]))
def withCounters (w0 : List Byte) (cs : List Nat) : List Byte := w0.take witCounters ++ (cs.map le32).flatten
def expandList (m sig : List Byte) : OracleComp HashSpec (Option (List Byte)) := do
  let N ← digest (sigRho sig) m
  match expandOf sig N with
  | none => pure none
  | some w0 =>
    match ← porsRoot (idxOf N) (leavesOf N) w0 with
    | none => pure none
    | some M =>
      match ← expandLayers w0 (idxOf N) nLayers M with
      | none => pure none
      | some cs => pure (some (withCounters w0 cs))
def expandRef (m : Bytes 32) (_pk : Bytes 16) (sig : Bytes 6048) :
    OracleComp HashSpec (Option (Bytes 6348)) := do
  let r ← expandList (toList m) (toList sig)
  pure (r.map (ofList 6348))
def verifySigRef (m : Bytes 32) (pk : Bytes 16) (sig : Bytes 6048) : OracleComp HashSpec Bool := do
  match ← expandRef m pk sig with
  | none => pure false
  | some w => verifyRef m pk w
end SigGolfCandidate.Ref
end
section
namespace SigGolfCandidate.Ref
open SigGolfCandidate.Legacy OracleComp OracleSpec
universe u
def countImpl (wt : Query → Nat) : QueryImpl HashSpec (StateT Nat (OracleComp HashSpec)) :=
  fun q => do
    modify (· + wt q)
    liftM (HashSpec.query q)
def countWith (wt : Query → Nat) {α : Type} (oa : OracleComp HashSpec α) :
    OracleComp HashSpec (α × Nat) :=
  (simulateQ (countImpl wt) oa).run 0
def countCalls {α : Type} (oa : OracleComp HashSpec α) : OracleComp HashSpec (α × Nat) :=
  countWith (fun _ => 1) oa
def countBlocks {α : Type} (oa : OracleComp HashSpec α) : OracleComp HashSpec (α × Nat) :=
  countWith Query.blocks oa
section
variable (wt : Query → Nat) {α β : Type}
theorem countImpl_run (oa : OracleComp HashSpec α) (n : Nat) :
    (simulateQ (countImpl wt) oa).run n = (fun p => (p.1, n + p.2)) <$> countWith wt oa := by
  unfold countWith
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => simp
  | query_bind q oa ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, countImpl]
    simp only [StateT.run_modify, pure_bind, map_bind]
    have hl : ∀ s, (liftM (OracleSpec.query q) : StateT Nat (OracleComp HashSpec) _).run s =
        (fun a => (a, s)) <$> (liftM (OracleSpec.query q) : OracleComp HashSpec _) := fun s => rfl
    simp only [hl, bind_map_left, ih _ (n + wt q), ih _ (0 + wt q), Functor.map_map]
    congr 1; funext a; congr 1; funext p; simp only [Prod.mk.injEq, true_and]; omega
@[simp] theorem countWith_pure (a : α) : countWith wt (pure a : OracleComp HashSpec α) = pure (a, 0) :=
  rfl
theorem countWith_bind (oa : OracleComp HashSpec α) (f : α → OracleComp HashSpec β) :
    countWith wt (oa >>= f) =
      countWith wt oa >>= fun p => (fun r => (r.1, p.2 + r.2)) <$> countWith wt (f p.1) := by
  conv_lhs => unfold countWith
  rw [simulateQ_bind, StateT.run_bind]
  exact congrArg _ (funext fun p => countImpl_run wt (f p.1) p.2)
@[simp] theorem countWith_query (q : Query) :
    countWith wt (liftM (HashSpec.query q) : OracleComp HashSpec _) =
      (fun a => (a, wt q)) <$> (liftM (HashSpec.query q) : OracleComp HashSpec _) := by
  unfold countWith
  rw [simulateQ_spec_query]
  simp only [countImpl, StateT.run_bind, StateT.run_modify, pure_bind, Nat.zero_add]
  rfl
@[simp] theorem fst_countWith (oa : OracleComp HashSpec α) : Prod.fst <$> countWith wt oa = oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q oa ih =>
    rw [countWith_bind, countWith_query]
    simp only [map_bind, bind_map_left, Functor.map_map]
    congr 1; funext a
    exact ih a
@[simp] theorem countWith_H (x : List Byte) :
    countWith wt (H x) = (fun a => (a, wt (fmt x))) <$> H x :=
  countWith_query wt (fmt x)
end
theorem countCalls_bind {α β : Type} (oa : OracleComp HashSpec α) (f : α → OracleComp HashSpec β) :
    countCalls (oa >>= f) =
      countCalls oa >>= fun p => (fun r => (r.1, p.2 + r.2)) <$> countCalls (f p.1) :=
  countWith_bind _ oa f
@[simp] theorem countCalls_pure {α : Type} (a : α) :
    countCalls (pure a : OracleComp HashSpec α) = pure (a, 0) := rfl
@[simp] theorem countCalls_query (q : Query) :
    countCalls (liftM (HashSpec.query q) : OracleComp HashSpec _) =
      (fun a => (a, 1)) <$> (liftM (HashSpec.query q) : OracleComp HashSpec _) :=
  countWith_query _ q
@[simp] theorem countCalls_H (x : List Byte) : countCalls (H x) = (fun a => (a, 1)) <$> H x :=
  countWith_H _ x
@[simp] theorem fst_countCalls {α : Type} (oa : OracleComp HashSpec α) :
    Prod.fst <$> countCalls oa = oa := fst_countWith _ oa
theorem evalWith_countCalls_fst {α : Type} (hash : Hash) (oa : OracleComp HashSpec α) :
    (evalWithAnswerFn hash (countCalls oa)).1 = evalWithAnswerFn hash oa := by
  conv_rhs => rw [← fst_countCalls oa]
  simp only [evalWithAnswerFn, simulateQ_map]
  rfl
end SigGolfCandidate.Ref
end
section
namespace SigGolfCandidate.Ref
open SigGolfCandidate.Legacy
theorem byte_toNat (v : Nat) : (byte v).toNat = v % 256 := by simp [byte]
theorem leNat_lt (l : List Byte) : leNat l < 256 ^ l.length := by
  induction l with
  | nil => simp [leNat]
  | cons b bs ih =>
    simp only [leNat, List.length_cons, Nat.pow_succ]
    have := b.isLt
    simp only [Nat.reducePow] at this
    nlinarith
theorem leNat_map_range (n v : Nat) :
    leNat ((List.range n).map fun i => byte (v / 256 ^ i)) = v % 256 ^ n := by
  induction n generalizing v with
  | zero => simp [leNat, Nat.mod_one]
  | succ n ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [leNat, Nat.pow_zero, Nat.div_one, byte_toNat]
    have h : (fun i => byte (v / 256 ^ i)) ∘ Nat.succ = fun i => byte (v / 256 / 256 ^ i) := by
      funext i; simp [Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]
    rw [h, ih, Nat.pow_succ, Nat.mul_comm (256 ^ n) 256, Nat.mod_mul]
theorem leNat_div_mod (l : List Byte) (i : Nat) :
    leNat l / 256 ^ i % 256 = (l.getD i 0).toNat := by
  induction l generalizing i with
  | nil => simp [leNat]
  | cons b bs ih =>
    have hb := b.isLt
    cases i with
    | zero => simp only [leNat, Nat.pow_zero, Nat.div_one, List.getD_cons_zero]; simp at hb ⊢; omega
    | succ i =>
      simp only [leNat, List.getD_cons_succ, Nat.pow_succ]
      rw [Nat.mul_comm (256 ^ i) 256, ← Nat.div_div_eq_div_mul]
      rw [show (b.toNat + 256 * leNat bs) / 256 = leNat bs by simp at hb; omega]
      exact ih i
theorem extractByte_ofNat (w v i : Nat) (h : 8 * i + 8 ≤ w) :
    (BitVec.ofNat w v).extractLsb' (8 * i) 8 = byte (v / 256 ^ i) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, byte_toNat, Nat.shiftRight_eq_div_pow]
  rw [show (256 : Nat) ^ i = 2 ^ (8 * i) by rw [Nat.pow_mul]]
  rw [show w = 8 * i + (w - 8 * i) by omega, Nat.pow_add, Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]
theorem toList_ofList (n : Nat) (l : List Byte) (h : l.length = n) : toList (ofList n l) = l := by
  subst h
  apply List.ext_getElem (by simp [toList, SigGolfCandidate.Legacy.bytes])
  intro i h1 h2
  simp only [toList, SigGolfCandidate.Legacy.bytes, ofList, List.getElem_map, List.getElem_range]
  rw [extractByte_ofNat _ _ _ (by simp [toList, SigGolfCandidate.Legacy.bytes] at h1; omega)]
  apply BitVec.eq_of_toNat_eq
  rw [byte_toNat, leNat_div_mod, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]; rfl
theorem toList_eq_map {n : Nat} (x : Bytes n) :
    toList x = (List.range n).map fun i => byte (x.toNat / 256 ^ i) := by
  simp only [toList, SigGolfCandidate.Legacy.bytes]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  have := extractByte_ofNat (8 * n) x.toNat i (by omega)
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
theorem leNat_toList {n : Nat} (x : Bytes n) : leNat (toList x) = x.toNat := by
  rw [toList_eq_map, leNat_map_range, Nat.mod_eq_of_lt]
  have := x.isLt
  rwa [Nat.pow_mul] at this
theorem ofList_toList {n : Nat} (x : Bytes n) : ofList n (toList x) = x := by
  apply BitVec.eq_of_toNat_eq
  simp [ofList, leNat_toList]
theorem length_toList {n : Nat} (x : Bytes n) : (toList x).length = n := by
  simp [toList, SigGolfCandidate.Legacy.bytes]
@[simp] theorem length_leBytes (k v : Nat) : (leBytes k v).length = k := by simp [leBytes]
@[simp] theorem length_le32 (v : Nat) : (le32 v).length = 4 := by simp [le32]
@[simp] theorem length_zeros (k : Nat) : (zeros k).length = k := by simp [zeros]
@[simp] theorem length_P : P.length = 16 := rfl
@[simp] theorem length_tweak (t lay tau p j : Nat) : (tweak t lay tau p j).length = 16 := by
  simp [tweak]
@[simp] theorem length_answerBytes (k : Nat) (a : BitVec 256) : (answerBytes k a).length = k := by
  simp [answerBytes]
@[simp] theorem length_thInput (tw payload : List Byte) :
    (thInput tw payload).length = tw.length + 16 + payload.length := by
  simp [thInput]; omega
theorem padBlocks_eq (len n : Nat) (h1 : len ≤ 64 * (n + 1)) (h2 : 64 * n < len) :
    padBlocks len = n := by
  unfold padBlocks; omega
theorem pad64_eq (x : List Byte) (n : Nat) (h1 : x.length ≤ 64 * (n + 1)) (h2 : 64 * n < x.length) :
    pad64 x = ⟨n, ofList _ (x ++ zeros (64 * (n + 1) - x.length))⟩ := by
  unfold pad64 padTo64
  rw [padBlocks_eq _ _ h1 h2]
theorem leNat_le32 (v : Nat) : leNat (le32 v) = v % 2 ^ 32 := by
  unfold le32 leBytes; rw [leNat_map_range]; norm_num
theorem fmt_of_chain (x : List Byte) (h : IsChainFmt x) : fmt x = ⟨0, ofList _ (chainBlock x)⟩ := by
  unfold fmt; rw [if_pos h]
theorem fmt_of_node (x : List Byte) (h : IsNodeFmt x) : fmt x = ⟨0, ofList _ (nodeBlock x)⟩ := by
  unfold fmt; rw [if_neg (fun hc => by have := hc.1.symm.trans h.1; omega), if_pos h]
theorem fmt_of_digest (x : List Byte) (h : IsDigestFmt x) : fmt x = ⟨0, ofList _ (digestBlock x)⟩ := by
  unfold fmt
  rw [if_neg (fun hc => by have := hc.1.symm.trans h.1; omega),
    if_neg (fun hc => by have := hc.1.symm.trans h.1; omega), if_pos h]
theorem fmt_of_plain (x : List Byte) (h1 : ¬ IsChainFmt x) (h2 : ¬ IsNodeFmt x)
    (h3 : ¬ IsDigestFmt x) : fmt x = pad64 x := by
  unfold fmt; rw [if_neg h1, if_neg h2, if_neg h3]
theorem fmt_of_tag (x : List Byte) (h : x.getD 1 0 ∉ [byte 1, byte 3, byte 12]) :
    fmt x = pad64 x := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  exact fmt_of_plain x (fun hc => h.1 hc.2) (fun hc => h.2.1 hc.2) (fun hc => h.2.2 hc.2)
theorem fmt_of_length (x : List Byte) (h : x.length ≠ 48 ∧ x.length ≠ 64 ∧ x.length ≠ 96) :
    fmt x = pad64 x :=
  fmt_of_plain x (fun hc => h.1 hc.1) (fun hc => h.2.1 hc.1) (fun hc => h.2.2 hc.1)
theorem getD_one_thInput (t lay tau p j : Nat) (payload : List Byte) :
    (thInput (tweak t lay tau p j) payload).getD 1 0 = byte t := by
  simp [thInput, tweak]
theorem fmt_thInput (t lay tau p j : Nat) (payload : List Byte)
    (ht : byte t ∉ [byte 1, byte 3, byte 12]) :
    fmt (thInput (tweak t lay tau p j) payload) = pad64 (thInput (tweak t lay tau p j) payload) :=
  fmt_of_tag _ (by rw [getD_one_thInput]; exact ht)
private theorem thInput_split (t lay tau p j : Nat) (pl : List Byte) :
    thInput (tweak t lay tau p j) pl =
      [byte 1, byte t, byte lay, byte (tau / 2 ^ 32)] ++ (le32 p ++ (le32 (tau % 2 ^ 32) ++
        (le32 j ++ (P ++ pl)))) := by
  simp [thInput, tweak]
private theorem take_app {l₁ : List Byte} (l₂ : List Byte) {n : Nat} (h : l₁.length = n) :
    (l₁ ++ l₂).take n = l₁ := by subst h; simp
private theorem drop_app {l₁ : List Byte} (l₂ : List Byte) {n : Nat} (h : l₁.length = n) :
    (l₁ ++ l₂).drop n = l₂ := by subst h; simp
theorem fmt_thInput_chain (lay tau p j : Nat) (v : Val) (hv : v.length = 16) (hp : p < 2 ^ 32) :
    fmt (thInput (tweak 1 lay tau p j) v) =
      ⟨0, ofList _ (tweak 1 lay tau (splitP p) j ++ zeros 32 ++ v)⟩ := by
  have hc : IsChainFmt (thInput (tweak 1 lay tau p j) v) :=
    ⟨by simp [hv], getD_one_thInput _ _ _ _ _ _⟩
  rw [fmt_of_chain _ hc]
  congr 2
  unfold chainBlock slice
  rw [thInput_split]
  have e4 : ∀ (l : List Byte) (a b c d : Byte), ([a, b, c, d] ++ l).take 4 = [a, b, c, d] :=
    fun l a b c d => rfl
  have d4 : ∀ (l : List Byte) (a b c d : Byte), ([a, b, c, d] ++ l).drop 4 = l :=
    fun l a b c d => rfl
  rw [e4, d4, take_app _ (length_le32 p), leNat_le32, Nat.mod_eq_of_lt hp]
  rw [show (8 : Nat) = 4 + 4 from rfl, ← List.drop_drop, d4, drop_app _ (length_le32 p),
    show 32 = 4 + 28 from rfl, ← List.drop_drop, d4, show 28 = 4 + 24 from rfl, ← List.drop_drop,
    drop_app _ (length_le32 p), show 24 = 4 + 20 from rfl, ← List.drop_drop,
    drop_app _ (length_le32 _), show 20 = 4 + 16 from rfl, ← List.drop_drop,
    drop_app _ (length_le32 _), drop_app _ length_P]
  have : (le32 (tau % 2 ^ 32) ++ (le32 j ++ (P ++ v))).take (4 + 4) = le32 (tau % 2 ^ 32) ++ le32 j := by
    rw [List.take_add, take_app _ (length_le32 _), drop_app _ (length_le32 _), take_app _ (length_le32 _)]
  rw [this]
  simp [tweak, zeros]
theorem fmt_chainInput (lay tau e i mu : Nat) (v : Val) (hv : v.length = 16) (hmu : 1 ≤ mu)
    (hmu' : mu ≤ 8) (hi : i < 2 ^ 24) :
    fmt (chainInput lay tau e i mu v) =
      ⟨0, ofList _ (tweak 1 lay tau (mu - 1 + 256 * i) e ++ zeros 32 ++ v)⟩ := by
  unfold chainInput
  rw [fmt_thInput_chain _ _ _ _ _ hv (by omega)]
  have : splitP (8 * i + mu - 1) = mu - 1 + 256 * i := by unfold splitP; omega
  rw [this]
theorem fmt_thInput_node (lay tau lam j : Nat) (pl : List Byte)
    (hpl : pl.length = 32) (hlam : lam < 2 ^ 32) (hj : j < 2 ^ 32) :
    fmt (thInput (tweak 3 lay tau lam j) pl) =
      ⟨0, ofList _ (thInput (tweak 3 lay tau 0 (heapIndex (height (lay % 256)) lam j)) pl)⟩ := by
  have hn : IsNodeFmt (thInput (tweak 3 lay tau lam j) pl) :=
    ⟨by simp [hpl], getD_one_thInput _ _ _ _ _ _⟩
  rw [fmt_of_node _ hn]
  congr 2
  have hh : nodeHeight (thInput (tweak 3 lay tau lam j) pl) = height (lay % 256) := by
    simp [nodeHeight, thInput, tweak, byte_toNat]
  unfold nodeBlock slice
  rw [hh, thInput_split]
  have e4 : ∀ (l : List Byte) (a b c d : Byte), ([a, b, c, d] ++ l).take 4 = [a, b, c, d] :=
    fun l a b c d => rfl
  have d4 : ∀ (l : List Byte) (a b c d : Byte), ([a, b, c, d] ++ l).drop 4 = l :=
    fun l a b c d => rfl
  rw [e4, d4, take_app _ (length_le32 lam), leNat_le32, Nat.mod_eq_of_lt hlam]
  rw [show (8 : Nat) = 4 + 4 from rfl, ← List.drop_drop, d4, drop_app _ (length_le32 lam),
    take_app _ (length_le32 _), show 12 = 4 + 8 from rfl, ← List.drop_drop, d4,
    show 8 = 4 + 4 from rfl, ← List.drop_drop, drop_app _ (length_le32 lam),
    drop_app _ (length_le32 _), take_app _ (length_le32 j), leNat_le32, Nat.mod_eq_of_lt hj,
    show 16 = 4 + 12 from rfl, ← List.drop_drop, d4, show 12 = 4 + 8 from rfl, ← List.drop_drop,
    drop_app _ (length_le32 lam), show 8 = 4 + 4 from rfl, ← List.drop_drop,
    drop_app _ (length_le32 _), drop_app _ (length_le32 j)]
  simp [thInput, tweak]
theorem fmt_nodeInput (lay tau lam j : Nat) (l r : Val) (hl : l.length = 16) (hr : r.length = 16)
    (hlay : lay < 256) (hlam : lam < 2 ^ 32) (hj : j < 2 ^ 32) :
    fmt (nodeInput lay tau lam j l r) =
      ⟨0, ofList _ (thInput (tweak 3 lay tau 0 (heapIndex (height lay) lam j)) (l ++ r))⟩ := by
  unfold nodeInput
  rw [fmt_thInput_node _ _ _ _ _ (by simp [hl, hr]) hlam hj, Nat.mod_eq_of_lt hlay]
theorem fmt_porsNodeInput (idx H : Nat) (l r : Val) (hl : l.length = 16) (hr : r.length = 16) :
    fmt (porsNodeInput idx H l r) = ⟨0, ofList _ (porsNodeInput idx H l r)⟩ := by
  unfold porsNodeInput
  rw [fmt_thInput _ _ _ _ _ _ (by decide),
    pad64_eq _ 0 (by simp [hl, hr]) (by simp [hl, hr])]
  simp [hl, hr, zeros]
theorem fmt_porsLeafInput (idx j : Nat) (s : Val) (hs : s.length = 16) :
    fmt (porsLeafInput idx j s) = ⟨0, ofList _ (porsLeafInput idx j s ++ zeros 16)⟩ := by
  unfold porsLeafInput
  rw [fmt_thInput _ _ _ _ _ _ (by decide), pad64_eq _ 0 (by simp [hs]) (by simp [hs])]
  simp [hs]
theorem fmt_porsPrfInput (S : List Byte) (idx q : Nat) :
    fmt (porsPrfInput S idx q) = pad64 (porsPrfInput S idx q) :=
  fmt_thInput _ _ _ _ _ _ (by decide)
theorem fmt_digestInput (rho m : List Byte) (hr : rho.length = 16) (hm : m.length = 32) :
    fmt (digestInput rho m) = ⟨0, ofList _ (tweak 12 0 0 0 0 ++ rho ++ m)⟩ := by
  have hd : IsDigestFmt (digestInput rho m) :=
    ⟨by simp [digestInput, hr, hm], getD_one_thInput _ _ _ _ _ _⟩
  rw [fmt_of_digest _ hd]
  congr 2
  unfold digestBlock slice digestInput thInput
  have h16 := length_tweak 12 0 0 0 0
  simp only [List.append_assoc]
  rw [take_app _ h16, show 32 = 16 + 16 from rfl, ← List.drop_drop, drop_app _ h16,
    drop_app _ length_P, take_app _ hr, show 64 = 16 + 48 from rfl, ← List.drop_drop, drop_app _ h16,
    show 48 = 16 + 32 from rfl, ← List.drop_drop, drop_app _ length_P,
    show 32 = 16 + 16 from rfl, ← List.drop_drop, drop_app _ hr, drop_app _ (length_zeros 16)]
theorem length_chainBlock (x : List Byte) (h : x.length = 48) : (chainBlock x).length = 64 := by
  simp [chainBlock, slice, h]
theorem length_nodeBlock (x : List Byte) (h : x.length = 64) : (nodeBlock x).length = 64 := by
  simp [nodeBlock, slice, h]
theorem length_digestBlock (x : List Byte) (h : x.length = 96) : (digestBlock x).length = 64 := by
  simp [digestBlock, slice, h]
theorem length_padTo64 (x : List Byte) : (padTo64 x).length = 64 * (padBlocks x.length + 1) := by
  simp only [padTo64, List.length_append, length_zeros, padBlocks]; omega
set_option exponentiation.threshold 600 in
theorem toList_fmt (x : List Byte) : toList (fmt x).2 = fmtList x := by
  have key : ∀ (l : List Byte) (hl : l.length = 64), toList (⟨0, ofList _ l⟩ : Query).2 = l :=
    fun l hl => toList_ofList _ _ hl
  by_cases h1 : IsChainFmt x
  · have e := congrArg (fun q : Query => toList q.2) (fmt_of_chain x h1)
    refine e.trans ((key _ (length_chainBlock x h1.1)).trans ?_)
    unfold fmtList; rw [if_pos h1]
  by_cases h2 : IsNodeFmt x
  · have e := congrArg (fun q : Query => toList q.2) (fmt_of_node x h2)
    refine e.trans ((key _ (length_nodeBlock x h2.1)).trans ?_)
    unfold fmtList; rw [if_neg h1, if_pos h2]
  by_cases h3 : IsDigestFmt x
  · have e := congrArg (fun q : Query => toList q.2) (fmt_of_digest x h3)
    refine e.trans ((key _ (length_digestBlock x h3.1)).trans ?_)
    unfold fmtList; rw [if_neg h1, if_neg h2, if_pos h3]
  · have e := congrArg (fun q : Query => toList q.2) (fmt_of_plain x h1 h2 h3)
    refine e.trans ((toList_ofList _ _ (length_padTo64 x)).trans ?_)
    unfold fmtList; rw [if_neg h1, if_neg h2, if_neg h3]
theorem getD_fmtList (x : List Byte) (i : Nat) (hi : i < 4 ∨ (8 ≤ i ∧ i < 12)) :
    (fmtList x).getD i 0 = x.getD i 0 := by
  unfold fmtList
  split_ifs with h1 h2 h3
  · unfold chainBlock slice
    simp only [List.getD_eq_getElem?_getD, List.append_assoc]
    rcases hi with hi | hi
    · rw [List.getElem?_append_left (by simp [h1.1]; omega), List.getElem?_take_of_lt hi]
    · rw [List.getElem?_append_right (by simp [h1.1]; omega),
        List.getElem?_append_right (by simp; omega), List.getElem?_append_left (by simp [h1.1]; omega),
        List.getElem?_take_of_lt (by simp [h1.1]; omega), List.getElem?_drop]
      simp only [List.length_take, length_le32, h1.1]
      congr 2; omega
  · unfold nodeBlock slice
    simp only [List.getD_eq_getElem?_getD, List.append_assoc]
    rcases hi with hi | hi
    · rw [List.getElem?_append_left (by simp [h2.1]; omega), List.getElem?_take_of_lt hi]
    · rw [List.getElem?_append_right (by simp [h2.1]; omega),
        List.getElem?_append_right (by simp; omega), List.getElem?_append_left (by simp [h2.1]; omega),
        List.getElem?_take_of_lt (by simp [h2.1]; omega), List.getElem?_drop]
      simp only [List.length_take, length_le32, h2.1]
      congr 2; omega
  · unfold digestBlock
    simp only [List.getD_eq_getElem?_getD, List.append_assoc]
    rw [List.getElem?_append_left (by simp [h3.1]; omega), List.getElem?_take_of_lt (by omega)]
  · unfold padTo64
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append, zeros]
    split
    · rfl
    · rename_i h
      simp
      first
        | (rw [List.getElem?_eq_none (l := x) (by omega), List.getElem?_replicate]
           split <;> rfl)
        | (rw [List.getElem?_eq_none (l := x) (by omega)]; simp)
        | rfl
theorem getD_toList_fmt (x : List Byte) (i : Nat) (hi : i < 4 ∨ (8 ≤ i ∧ i < 12)) :
    (toList (fmt x).2).getD i 0 = x.getD i 0 := by
  rw [toList_fmt, getD_fmtList x i hi]
theorem blocks_fmt (x : List Byte) (h : ¬ IsDigestFmt x) : (fmt x).blocks = (pad64 x).blocks := by
  by_cases h1 : IsChainFmt x
  · rw [fmt_of_chain x h1]; show 0 + 1 = padBlocks x.length + 1; rw [h1.1]; rfl
  by_cases h2 : IsNodeFmt x
  · rw [fmt_of_node x h2]; show 0 + 1 = padBlocks x.length + 1; rw [h2.1]; rfl
  rw [fmt_of_plain x h1 h2 h]
theorem blocks_fmt_digest (x : List Byte) (h : IsDigestFmt x) : (fmt x).blocks = 1 := by
  rw [fmt_of_digest x h]; rfl
theorem blocks_fmt_le (x : List Byte) : (fmt x).blocks ≤ (pad64 x).blocks := by
  by_cases h : IsDigestFmt x
  · rw [blocks_fmt_digest x h]; show 1 ≤ padBlocks x.length + 1; omega
  · rw [blocks_fmt x h]
theorem height_values : (List.range nLayers).map height = [11, 6, 6, 6, 5] := by decide
theorem shiftBelow_values :
    (List.range nLayers).map shiftBelow = [23, 17, 11, 5, 0] := by decide
theorem topH_eq : topH = 11 := rfl
theorem topN_values : (List.range (topH + 1)).map topN =
    [0, 2048, 3072, 3584, 3840, 3968, 4032, 4064, 4080, 4088, 4092, 4094] := by decide
theorem regionBytes_eq : regionBytes = 65504 := by decide
theorem porsT_eq : porsT = 16384 := rfl
theorem porsSegs_eq : porsSegs = 29 := rfl
theorem headBytes_eq : headBytes = 2144 := rfl
theorem sigLayerOff_values :
    (List.range (nLayers + 1)).map sigLayerOff = [2144, 2992, 3760, 4528, 5296, 6048] := by
  decide
theorem bodyBytes_eq (lay : Nat) : bodyBytes lay = sigLayerBytes lay - 4 := by
  simp only [bodyBytes, sigLayerBytes]; omega
theorem witLayerOff_eq_sig (lay : Nat) (h : lay ≤ nLayers) : witLayerOff lay = sigLayerOff lay + 280 := by
  simp only [nLayers] at h
  interval_cases lay <;> decide
theorem sigBytes_eq_sigLayerOff : sigBytes = sigLayerOff nLayers := by decide
theorem wStream_eq : wStream = 272 := rfl
theorem streamBytes_eq : streamBytes = 2152 := rfl
theorem wLayers_eq : wLayers = 2424 := rfl
theorem witLayerOff_values :
    (List.range (nLayers + 1)).map witLayerOff = [2424, 3272, 4040, 4808, 5576, 6328] := by
  decide
theorem witCounters_eq : witCounters = 6328 := by decide
theorem witBytes_eq : witBytes = witCounters + 4 * nLayers := by decide
private theorem length_slice (l : List Byte) (off len : Nat) (h : off + len ≤ l.length) :
    (slice l off len).length = len := by
  simp [slice]; omega
private theorem length_flatten_map_range (n k : Nat) (f : Nat → List Byte)
    (hf : ∀ i, i < n → (f i).length = k) : ((List.range n).map f).flatten.length = n * k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.flatten_append, List.length_append,
      ih (fun i hi => hf i (by omega))]
    simp [hf n (by omega)]; ring
private theorem length_flatten_map_range' (n : Nat) (f : Nat → List Byte) (g : Nat → Nat)
    (hf : ∀ i, i < n → (f i).length = g i) :
    ((List.range n).map f).flatten.length = ((List.range n).map g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.flatten_append, List.length_append,
      ih (fun i hi => hf i (by omega))]
    simp [hf n (by omega)]
theorem length_witnessList (sig : List Byte) (hsig : sig.length = sigBytes) (v vs segs : List Nat)
    (hvs : vs.length = porsK) : (witnessList sig v vs segs).length = witBytes := by
  have hs : sig.length = 6048 := hsig
  have hoff : ∀ lay, lay < nLayers → sigLayerOff lay + bodyBytes lay ≤ 6048 := by decide
  have hitem : ∀ i, i < porsK → (sigItem sig i).length = 16 := fun i hi =>
    length_slice _ _ _ (by rw [hs]; unfold porsK at hi; omega)
  have hbody : ∀ lay, lay < nLayers → (sigLayerBody sig lay).length = bodyBytes lay :=
    fun lay hl => length_slice _ _ _ (by have := hoff lay hl; rw [hs]; omega)
  unfold witnessList witnessBody
  simp only [List.length_append, List.length_map, List.length_take, length_zeros, hvs,
    length_flatten_map_range _ _ _ hitem, length_flatten_map_range' _ _ _ hbody]
  rw [show (sigRho sig).length = 16 from length_slice _ _ _ (by rw [hs]; decide)]
  have : ((List.range nLayers).map bodyBytes).sum = 3904 := by decide
  rw [this]
  have : min streamBytes ((segStream sig segs).length + streamBytes) = streamBytes := by omega
  rw [this]
  decide
theorem length_of_expandOf (sig : List Byte) (hsig : sig.length = sigBytes) (N : Nat)
    (w : List Byte) (h : expandOf sig N = some w) : w.length = witBytes := by
  unfold expandOf at h
  dsimp only at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  cases h
  exact length_witnessList _ hsig _ _ _ (by simp [sortLeaves, leavesOf, porsK])
end SigGolfCandidate.Ref
end
section
end
section
namespace SigGolfCandidate.Budget
open SigGolfCandidate.Legacy OracleComp OracleSpec ENNReal OracleComp.EvalDist
open SigGolfCandidate.Ref
abbrev RCache := QueryCache HashSpec
abbrev qry (q : Query) : OracleComp HashSpec (BitVec 256) :=
  liftM (OracleSpec.query (spec := HashSpec) q)
noncomputable def roRun {α : Type} (oa : OracleComp HashSpec α) (c : RCache) :
    ProbComp (α × RCache) :=
  (simulateQ randomOracle oa).run c
theorem roRun_bind {α β : Type} (oa : OracleComp HashSpec α) (f : α → OracleComp HashSpec β)
    (c : RCache) : roRun (oa >>= f) c = roRun oa c >>= fun x => roRun (f x.1) x.2 := by
  simp only [roRun, simulateQ_bind, StateT.run_bind]
theorem roRun_map {α β : Type} (g : α → β) (oa : OracleComp HashSpec α) (c : RCache) :
    roRun (g <$> oa) c = (fun x => (g x.1, x.2)) <$> roRun oa c := by
  simp only [roRun, simulateQ_map, StateT.run_map]
@[simp] theorem roRun_pure {α : Type} (a : α) (c : RCache) :
    roRun (pure a : OracleComp HashSpec α) c = pure (a, c) := by
  simp [roRun]
theorem roRun_qry (q : Query) (c : RCache) :
    roRun (qry q) c = (randomOracle q).run c := by
  simp [roRun, qry]
theorem mem_support_roRun_of_count {α : Type} (wt : Query → Nat) (oa : OracleComp HashSpec α)
    (c : RCache) (x : (α × Nat) × RCache) (hx : x ∈ support (roRun (countWith wt oa) c)) :
    (x.1.1, x.2) ∈ support (roRun oa c) := by
  have h : roRun oa c = (fun x => (x.1.1, x.2)) <$> roRun (countWith wt oa) c := by
    conv_lhs => rw [← fst_countWith wt oa]
    rw [roRun_map]
  rw [h, support_map]
  exact ⟨x, hx, rfl⟩
theorem ev_const_mul {γ : Type} (mx : ProbComp γ) (g : γ → ℝ≥0∞) (a : ℝ≥0∞) :
    expectedValue mx (fun x => a * g x) = a * expectedValue mx g := by
  simp only [mul_comm a]
  exact expectedValue_mul_const mx g a
noncomputable def V (z : ℝ≥0∞) {α : Type} (oa : OracleComp HashSpec α) (c : RCache) : ℝ≥0∞ :=
  expectedValue (roRun (countBlocks oa) c) (fun x => z ^ x.1.2)
@[simp] theorem V_pure (z : ℝ≥0∞) {α : Type} (a : α) (c : RCache) :
    V z (pure a : OracleComp HashSpec α) c = 1 := by
  simp [V, countBlocks]
theorem V_bind_eq (z : ℝ≥0∞) {α β : Type} (oa : OracleComp HashSpec α)
    (f : α → OracleComp HashSpec β) (c : RCache) :
    V z (oa >>= f) c = expectedValue (roRun (countBlocks oa) c)
      (fun x => z ^ x.1.2 * V z (f x.1.1) x.2) := by
  unfold V countBlocks
  rw [countWith_bind, roRun_bind, expectedValue_bind]
  congr 1; funext x
  rw [roRun_map, expectedValue_map]
  simp only [pow_add]
  exact ev_const_mul _ _ _
theorem V_bind_le (z : ℝ≥0∞) {α β : Type} (oa : OracleComp HashSpec α)
    (f : α → OracleComp HashSpec β) (c : RCache) (b : ℝ≥0∞)
    (h : ∀ x ∈ support (roRun oa c), V z (f x.1) x.2 ≤ b) :
    V z (oa >>= f) c ≤ V z oa c * b := by
  rw [V_bind_eq]
  unfold V
  rw [← expectedValue_mul_const]
  refine expectedValue_mono_of_support fun x hx => ?_
  have := h (x.1.1, x.2) (mem_support_roRun_of_count _ oa c x hx)
  exact mul_le_mul' le_rfl this
theorem V_map (z : ℝ≥0∞) {α β : Type} (g : α → β) (oa : OracleComp HashSpec α) (c : RCache) :
    V z (g <$> oa) c = V z oa c := by
  rw [map_eq_bind_pure_comp, V_bind_eq, V]
  simp
theorem V_map_le (z : ℝ≥0∞) {α β : Type} (g : α → β) (oa : OracleComp HashSpec α) (c : RCache)
    (b : ℝ≥0∞) (h : V z oa c ≤ b) : V z (g <$> oa) c ≤ b := by
  rwa [V_map]
theorem V_query (z : ℝ≥0∞) {α : Type} (q : Query) (f : BitVec 256 → OracleComp HashSpec α)
    (c : RCache) :
    V z (qry q >>= f) c =
      z ^ q.blocks * expectedValue ((randomOracle q).run c) (fun y => V z (f y.1) y.2) := by
  rw [V_bind_eq]
  unfold countBlocks
  rw [countWith_query, roRun_map, expectedValue_map, roRun_qry]
  exact ev_const_mul ((randomOracle q).run c) (fun y => V z (f y.1) y.2) (z ^ q.blocks)
theorem expectedValue_ro_fresh (q : Query) (c : RCache) (hq : c q = none)
    (g : BitVec 256 × RCache → ℝ≥0∞) :
    expectedValue ((randomOracle q).run c) g =
      expectedValue ($ᵗ BitVec 256 : ProbComp (BitVec 256)) (fun u => g (u, c.cacheQuery q u)) := by
  rw [randomOracle.run_eq, hq]
  simp only
  rw [expectedValue_bind]
  simp
theorem expectedValue_ro_cached (q : Query) (c : RCache) (u : BitVec 256) (hq : c q = some u)
    (g : BitVec 256 × RCache → ℝ≥0∞) :
    expectedValue ((randomOracle q).run c) g = g (u, c) := by
  rw [randomOracle.run_eq, hq]
  simp
theorem mem_support_ro (q : Query) (c : RCache) (y : BitVec 256 × RCache)
    (hy : y ∈ support ((randomOracle q).run c)) :
    (c q = some y.1 ∧ y.2 = c) ∨ (c q = none ∧ y.2 = c.cacheQuery q y.1) := by
  rw [randomOracle.run_eq] at hy
  cases hq : c q with
  | some u =>
    rw [hq] at hy
    simp only [support_pure, Set.mem_singleton_iff] at hy
    subst hy
    left; exact ⟨rfl, rfl⟩
  | none =>
    rw [hq] at hy
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
      exists_prop] at hy
    obtain ⟨u, _, rfl⟩ := hy
    right; exact ⟨rfl, rfl⟩
inductive Spec (P : Query → Prop) {α : Type} (Post : α → Prop) :
    Nat → OracleComp HashSpec α → Prop
  | pure (a : α) (k : Nat) : Post a → Spec P Post k (pure a)
  | query (q : Query) (f : BitVec 256 → OracleComp HashSpec α) (k : Nat) :
      P q → (∀ u, Spec P Post k (f u)) → Spec P Post (q.blocks + k) (qry q >>= f)
namespace Spec
variable {P : Query → Prop} {α β : Type}
theorem mono_k {Post : α → Prop} {k k' : Nat} {oa : OracleComp HashSpec α}
    (h : Spec P Post k oa) (hk : k ≤ k') : Spec P Post k' oa := by
  induction h generalizing k' with
  | pure a k hp => exact .pure a k' hp
  | query q f k hq _ ih =>
    have : k' = q.blocks + (k' - q.blocks) := by omega
    rw [this]
    exact .query q f _ hq fun u => ih u (by omega)
theorem mono {P' : Query → Prop} {Post Post' : α → Prop} {k : Nat} {oa : OracleComp HashSpec α}
    (h : Spec P Post k oa) (hP : ∀ q, P q → P' q) (hQ : ∀ a, Post a → Post' a) :
    Spec P' Post' k oa := by
  induction h with
  | pure a k hp => exact .pure a k (hQ a hp)
  | query q f k hq _ ih => exact .query q f k (hP q hq) ih
theorem bind {Q : α → Prop} {R : β → Prop} {k l : Nat} {oa : OracleComp HashSpec α}
    {f : α → OracleComp HashSpec β} (h : Spec P Q k oa) (hf : ∀ a, Q a → Spec P R l (f a)) :
    Spec P R (k + l) (oa >>= f) := by
  induction h with
  | pure a k hp => rw [pure_bind]; exact (hf a hp).mono_k (by omega)
  | query q g k hq _ ih =>
    rw [bind_assoc, Nat.add_assoc]
    exact .query q _ _ hq ih
theorem bind' {Q : α → Prop} {R : β → Prop} {k l n : Nat} {oa : OracleComp HashSpec α}
    {f : α → OracleComp HashSpec β} (h : Spec P Q k oa) (hf : ∀ a, Q a → Spec P R l (f a))
    (hn : k + l ≤ n) : Spec P R n (oa >>= f) :=
  (h.bind hf).mono_k hn
theorem map {Q : α → Prop} {R : β → Prop} {k : Nat} {oa : OracleComp HashSpec α} (g : α → β)
    (h : Spec P Q k oa) (hg : ∀ a, Q a → R (g a)) : Spec P R k (g <$> oa) := by
  rw [map_eq_bind_pure_comp]
  exact (h.bind (l := 0) fun a ha => .pure _ 0 (hg a ha))
theorem qry_bind {R : β → Prop} {q : Query} {f : BitVec 256 → OracleComp HashSpec β} {k n : Nat}
    (hq : P q) (hf : ∀ u, Spec P R k (f u)) (hn : q.blocks + k ≤ n) :
    Spec P R n (qry q >>= f) :=
  (Spec.query q f k hq hf).mono_k hn
theorem V_le {Post : α → Prop} {k : Nat} {oa : OracleComp HashSpec α} (h : Spec P Post k oa)
    {z : ℝ≥0∞} (hz : 1 ≤ z) (c : RCache) : V z oa c ≤ z ^ k := by
  induction h generalizing c with
  | pure a k _ => rw [V_pure]; exact one_le_pow₀ hz
  | query q f k _ _ ih =>
    rw [V_query, pow_add]
    exact mul_le_mul' le_rfl (expectedValue_le_of_le _ fun y => ih y.1 y.2)
def _root_.SigGolfCandidate.Budget.CacheInv (I : Query → Prop) (c : RCache) : Prop :=
  ∀ q u, c q = some u → I q
theorem support {Post : α → Prop} {k : Nat} {oa : OracleComp HashSpec α} (h : Spec P Post k oa)
    {I : Query → Prop} (hPI : ∀ q, P q → I q) (c : RCache) (hc : CacheInv I c)
    (x : α × RCache) (hx : x ∈ support (roRun oa c)) : Post x.1 ∧ CacheInv I x.2 := by
  induction h generalizing c with
  | pure a k hp =>
    rw [roRun_pure, support_pure, Set.mem_singleton_iff] at hx
    subst hx; exact ⟨hp, hc⟩
  | query q f k hq _ ih =>
    rw [roRun_bind, support_bind] at hx
    simp only [Set.mem_iUnion, exists_prop] at hx
    obtain ⟨y, hy, hx⟩ := hx
    rw [roRun_qry] at hy
    refine ih y.1 y.2 ?_ hx
    rcases mem_support_ro q c y hy with ⟨_, h2⟩ | ⟨_, h2⟩
    · rw [h2]; exact hc
    · rw [h2]
      intro q' u hq'
      by_cases hqq : q' = q
      · subst hqq; exact hPI _ hq
      · rw [QueryCache.cacheQuery_of_ne _ _ hqq] at hq'
        exact hc q' u hq'
end Spec
theorem CacheInv.mono {I I' : Query → Prop} {c : RCache} (h : CacheInv I c)
    (hI : ∀ q, I q → I' q) : CacheInv I' c := fun q u hq => hI q (h q u hq)
end SigGolfCandidate.Budget
end
section
namespace SigGolfCandidate.Budget
open SigGolfCandidate.Legacy SigGolfCandidate.Ref
def qbyte (q : Query) (i : Nat) : Nat := q.2.toNat / 256 ^ i % 256
theorem length_padTo64 (x : List Byte) : (padTo64 x).length = 64 * (padBlocks x.length + 1) := by
  unfold padTo64 padBlocks
  simp only [List.length_append, length_zeros]
  omega
theorem getD_padTo64 (x : List Byte) (i : Nat) : (padTo64 x).getD i 0 = x.getD i 0 := by
  unfold padTo64 zeros
  simp only [List.getD_eq_getElem?_getD]
  by_cases hi : i < x.length
  · rw [List.getElem?_append_left hi]
  · rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (l := x) (by omega),
      List.getElem?_replicate]
    split <;> rfl
theorem qbyte_pad64 (x : List Byte) (i : Nat) : qbyte (pad64 x) i = (x.getD i 0).toNat := by
  unfold qbyte pad64 ofList
  simp only [BitVec.toNat_ofNat]
  have hlt := leNat_lt (padTo64 x)
  rw [length_padTo64] at hlt
  have h2 : (2 : Nat) ^ (8 * (64 * (padBlocks x.length + 1))) = 256 ^ (64 * (padBlocks x.length + 1)) := by
    rw [Nat.pow_mul]
  rw [h2, Nat.mod_eq_of_lt hlt, leNat_div_mod, getD_padTo64]
theorem getD_eq_of_pad64_eq {x y : List Byte} (e : pad64 x = pad64 y) (i : Nat) :
    x.getD i 0 = y.getD i 0 := by
  have h := congrArg (fun q => qbyte q i) e
  simp only [qbyte_pad64] at h
  exact BitVec.eq_of_toNat_eq h
theorem pad64_inj {x y : List Byte} (h : x.length = y.length) (e : pad64 x = pad64 y) : x = y := by
  apply List.ext_getElem h
  intro i h1 h2
  have := getD_eq_of_pad64_eq e i
  simpa [List.getD_eq_getElem?_getD, h1, h2] using this
theorem blocks_pad64 (x : List Byte) : (pad64 x).blocks = padBlocks x.length + 1 := rfl
theorem blocks_pad64_le (x : List Byte) (k : Nat) (h : x.length ≤ 64 * k) (hk : 1 ≤ k) :
    (pad64 x).blocks ≤ k := by
  rw [blocks_pad64]; unfold padBlocks; omega
theorem blocksFmt_le (x : List Byte) (k : Nat) (h : x.length ≤ 64 * k) (hk : 1 ≤ k) :
    (fmt x).blocks ≤ k :=
  (Ref.blocks_fmt_le x).trans (blocks_pad64_le x k h hk)
theorem qbyte_fmt (x : List Byte) (i : Nat) (hi : i < 4) : qbyte (fmt x) i = (x.getD i 0).toNat := by
  unfold qbyte
  rw [← leNat_toList, leNat_div_mod, getD_toList_fmt x i (Or.inl hi)]
theorem fmt_eq_pad64 (t lay tau p j : Nat) (pl : List Byte)
    (ht : t % 256 ≠ 1 ∧ t % 256 ≠ 3 ∧ t % 256 ≠ 12) :
    fmt (thInput (tweak t lay tau p j) pl) = pad64 (thInput (tweak t lay tau p j) pl) := by
  refine fmt_thInput _ _ _ _ _ _ ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;> have := congrArg BitVec.toNat h <;>
    simp [byte_toNat] at this <;> omega
theorem qbyte_tag (t lay tau p j : Nat) (pl : List Byte) :
    qbyte (fmt (thInput (tweak t lay tau p j) pl)) 1 = t % 256 := by
  rw [qbyte_fmt _ _ (by omega)]; simp [thInput, tweak, byte_toNat]
theorem qbyte_lay (t lay tau p j : Nat) (pl : List Byte) :
    qbyte (fmt (thInput (tweak t lay tau p j) pl)) 2 = lay % 256 := by
  rw [qbyte_fmt _ _ (by omega)]; simp [thInput, tweak, byte_toNat]
theorem leNat_leBytes (k v : Nat) : leNat (leBytes k v) = v % 256 ^ k := leNat_map_range k v
theorem le32_inj {c c' : Nat} (hc : c < 2 ^ 32) (hc' : c' < 2 ^ 32) (h : le32 c = le32 c') :
    c = c' := by
  have := congrArg leNat h
  simp only [le32, leNat_leBytes] at this
  rw [Nat.mod_eq_of_lt (by simpa using hc), Nat.mod_eq_of_lt (by simpa using hc')] at this
  exact this
theorem tweak_p_inj {t lay tau p j t' lay' tau' p' j' : Nat} (hp : p < 2 ^ 32) (hp' : p' < 2 ^ 32)
    (h : tweak t lay tau p j = tweak t' lay' tau' p' j') : p = p' := by
  unfold tweak at h
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
  obtain ⟨-, -, -, -, h⟩ := h
  have h2 := List.append_inj_left' (List.append_inj_left' h (by simp)) (by simp)
  exact le32_inj hp hp' (List.append_inj_left' h2 (by simp))
theorem getD_len_le {l : List (List Byte)} {n : Nat} (h : ∀ v ∈ l, v.length ≤ n) (i : Nat) :
    (l.getD i []).length ≤ n := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : l[i]? with
  | none => simp
  | some v => exact h v (List.mem_of_getElem? hi)
theorem length_flatten_le {l : List (List Byte)} {n : Nat} (h : ∀ v ∈ l, v.length ≤ n) :
    l.flatten.length ≤ n * l.length := by
  induction l with
  | nil => simp
  | cons v l ih =>
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    have h1 := h v (by simp)
    have h2 := ih (fun w hw => h w (by simp [hw]))
    rw [Nat.mul_succ]; omega
end SigGolfCandidate.Budget
end
end
end
-- ==== merged from Budget_Loops ====
section

namespace SigGolfCandidate.Budget
open SigGolfCandidate.Legacy SigGolfCandidate.Ref OracleComp OracleSpec Finset
theorem Spec.foldlM_list {P : Query → Prop} {γ β : Type} (l : List β)
    (f : γ → β → OracleComp HashSpec γ) (Inv : Nat → γ → Prop) (cost : Nat → Nat) (init : γ)
    (h0 : Inv 0 init)
    (hs : ∀ i (hi : i < l.length) acc, Inv i acc → Spec P (Inv (i + 1)) (cost i) (f acc l[i])) :
    Spec P (Inv l.length) (∑ i ∈ range l.length, cost i) (l.foldlM f init) := by
  induction l generalizing Inv cost init with
  | nil => exact Spec.pure _ _ h0
  | cons x l ih =>
    rw [List.foldlM_cons, List.length_cons]
    have h0' := hs 0 (by simp) init h0
    simp only [List.getElem_cons_zero] at h0'
    refine Spec.bind' h0' (fun a ha => ih (fun i => Inv (i + 1)) (fun i => cost (i + 1)) a ha
      (fun i hi acc hacc => hs (i + 1) (by simp; omega) acc hacc)) ?_
    rw [Finset.sum_range_succ' _ l.length]; omega
theorem Spec.foldlM_range {P : Query → Prop} {γ : Type} (n : Nat)
    (f : γ → Nat → OracleComp HashSpec γ) (Inv : Nat → γ → Prop) (cost : Nat → Nat) (init : γ)
    (h0 : Inv 0 init)
    (hs : ∀ i, i < n → ∀ acc, Inv i acc → Spec P (Inv (i + 1)) (cost i) (f acc i)) :
    Spec P (Inv n) (∑ i ∈ range n, cost i) ((List.range n).foldlM f init) := by
  have h := Spec.foldlM_list (P := P) (List.range n) f Inv cost init h0
    (fun i hi acc hacc => by
      simp only [List.getElem_range]; exact hs i (by simpa using hi) acc hacc)
  simpa using h
theorem Spec.foldlM_range' {P : Query → Prop} {γ : Type} (a n : Nat)
    (f : γ → Nat → OracleComp HashSpec γ) (Inv : Nat → γ → Prop) (cost : Nat → Nat) (init : γ)
    (h0 : Inv 0 init)
    (hs : ∀ i, i < n → ∀ acc, Inv i acc → Spec P (Inv (i + 1)) (cost i) (f acc (a + i))) :
    Spec P (Inv n) (∑ i ∈ range n, cost i) ((List.range' a n).foldlM f init) := by
  have h := Spec.foldlM_list (P := P) (List.range' a n) f Inv cost init h0
    (fun i hi acc hacc => by
      simp only [List.getElem_range', Nat.one_mul]; exact hs i (by simpa using hi) acc hacc)
  simpa using h
theorem Spec.foldlM_range_le {P : Query → Prop} {γ : Type} (n : Nat)
    (f : γ → Nat → OracleComp HashSpec γ) (Inv : Nat → γ → Prop) (cost : Nat → Nat) (init : γ)
    {Post : γ → Prop} {k : Nat} (h0 : Inv 0 init)
    (hs : ∀ i, i < n → ∀ acc, Inv i acc → Spec P (Inv (i + 1)) (cost i) (f acc i))
    (hpost : ∀ acc, Inv n acc → Post acc) (hk : ∑ i ∈ range n, cost i ≤ k) :
    Spec P Post k ((List.range n).foldlM f init) :=
  ((Spec.foldlM_range n f Inv cost init h0 hs).mono (fun _ h => h) hpost).mono_k hk
theorem Spec.foldlM_range'_le {P : Query → Prop} {γ : Type} (a n : Nat)
    (f : γ → Nat → OracleComp HashSpec γ) (Inv : Nat → γ → Prop) (cost : Nat → Nat) (init : γ)
    {Post : γ → Prop} {k : Nat} (h0 : Inv 0 init)
    (hs : ∀ i, i < n → ∀ acc, Inv i acc → Spec P (Inv (i + 1)) (cost i) (f acc (a + i)))
    (hpost : ∀ acc, Inv n acc → Post acc) (hk : ∑ i ∈ range n, cost i ≤ k) :
    Spec P Post k ((List.range' a n).foldlM f init) :=
  ((Spec.foldlM_range' a n f Inv cost init h0 hs).mono (fun _ h => h) hpost).mono_k hk
theorem sum_const_range (n c : Nat) : ∑ _i ∈ range n, c = n * c := by simp
theorem sum_levels (h : Nat) : ∑ i ∈ range h, 2 ^ (h - i) / 2 = 2 ^ h - 1 := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [Finset.sum_range_succ']
    have : ∀ i ∈ range h, 2 ^ (h + 1 - (i + 1)) / 2 = 2 ^ (h - i) / 2 := by
      intro i _; rw [Nat.add_sub_add_right]
    rw [Finset.sum_congr rfl this, ih]
    simp only [Nat.sub_zero, Nat.pow_succ, Nat.mul_div_cancel _ (by norm_num : 0 < 2)]
    have : 1 ≤ 2 ^ h := Nat.one_le_two_pow
    omega
def AllShort (l : List Val) : Prop := ∀ v ∈ l, v.length ≤ 16
theorem AllShort.nil : AllShort [] := by simp [AllShort]
theorem AllShort.append {l : List Val} {v : Val} (hl : AllShort l) (hv : v.length ≤ 16) :
    AllShort (l ++ [v]) := by
  intro w hw
  simp only [List.mem_append, List.mem_singleton] at hw
  rcases hw with hw | rfl
  · exact hl w hw
  · exact hv
theorem spec_hash16 {P : Query → Prop} (x : List Byte) (k : Nat) (hP : P (fmt x))
    (hk : (fmt x).blocks ≤ k) : Spec P (fun v : Val => v.length = 16) k (hash16 x) := by
  show Spec P _ k (qry (fmt x) >>= fun a => Pure.pure (answerBytes 16 a))
  exact Spec.qry_bind hP (fun u => Spec.pure _ 0 (by simp)) (by omega)
theorem spec_hash16_bind {P : Query → Prop} {β : Type} {R : β → Prop} (x : List Byte)
    {f : Val → OracleComp HashSpec β} {kx l n : Nat} (hP : P (fmt x))
    (hk : (fmt x).blocks ≤ kx) (hf : ∀ v : Val, v.length = 16 → Spec P R l (f v))
    (hn : kx + l ≤ n) : Spec P R n (Ref.hash16 x >>= f) :=
  (spec_hash16 x kx hP hk).bind' hf hn
def PT (q : Query) : Prop := qbyte q 1 ≤ 3
def PP (q : Query) : Prop := 8 ≤ qbyte q 1 ∧ qbyte q 1 ≤ 10
def NodeOK (P : Query → Prop) (node : NodeFmt) : Prop :=
  ∀ lam j l r, l.length ≤ 16 → r.length ≤ 16 →
    P (fmt (node lam j l r)) ∧ (node lam j l r).length ≤ 64
theorem nodeOK_nodeInput (lay tau : Nat) : NodeOK PT (nodeInput lay tau) := by
  intro lam j l r hl hr
  refine ⟨?_, ?_⟩
  · unfold PT nodeInput; rw [qbyte_tag]
  · simp [nodeInput]; omega
theorem nodeOK_porsNodeFmt (idx : Nat) : NodeOK PP (porsNodeFmt idx) := by
  intro lam j l r hl hr
  refine ⟨?_, ?_⟩
  · unfold PP porsNodeFmt porsNodeInput; rw [qbyte_tag]; omega
  · simp [porsNodeFmt, porsNodeInput]; omega
theorem spec_buildLevel {P : Query → Prop} {node : NodeFmt} (hn : NodeOK P node) (lam : Nat)
    (level : List Val) (hl : AllShort level) :
    Spec P (fun r => r.length = level.length / 2 ∧ AllShort r) (level.length / 2)
      (buildLevel node lam level) := by
  unfold buildLevel
  refine Spec.foldlM_range_le (P := P) (level.length / 2) _
    (fun i (acc : List Val) => acc.length = i ∧ AllShort acc) (fun _ => 1) [] ⟨rfl, AllShort.nil⟩
    (fun i _ acc hacc => ?_) (fun acc h => h) (by simp)
  obtain ⟨hn1, hn2⟩ := hn lam i (level.getD (2 * i) []) (level.getD (2 * i + 1) [])
    (getD_len_le hl _) (getD_len_le hl _)
  exact spec_hash16_bind (node lam i (level.getD (2 * i) []) (level.getD (2 * i + 1) []))
    hn1 (blocksFmt_le _ 1 (by omega) le_rfl)
    (fun v hv => Spec.pure _ 0 ⟨by simp [hacc.1], hacc.2.append (by omega)⟩) le_rfl
theorem spec_levelStep {P : Query → Prop} {node : NodeFmt} (hn : NodeOK P node) (cap : Nat)
    (st : List Val × List Val) (lam : Nat) (hl : AllShort st.1) :
    Spec P (fun r => r.1.length = st.1.length / 2 ∧ AllShort r.1) (st.1.length / 2)
      (levelStep node cap st lam) := by
  unfold levelStep
  exact (spec_buildLevel hn lam st.1 hl).bind' (l := 0)
    (fun r hr => Spec.pure _ 0 hr) (by omega)
theorem spec_buildLevels {P : Query → Prop} {node : NodeFmt} (hn : NodeOK P node) (cap h : Nat)
    (leaves : List Val) (hlen : leaves.length = 2 ^ h) (hl : AllShort leaves) :
    Spec P (fun r => r.1.length ≤ 16) (2 ^ h - 1) (buildLevels node cap h leaves) := by
  unfold buildLevels
  rw [← sum_levels h]
  refine Spec.bind' (l := 0) (Spec.foldlM_range' (P := P) 1 h (levelStep node cap)
    (fun i (st : List Val × List Val) => st.1.length = 2 ^ (h - i) ∧ AllShort st.1)
    (fun i => 2 ^ (h - i) / 2) (leaves, []) ⟨by simpa using hlen, hl⟩
    (fun i hi st hst => ?_)) (fun st hst => Spec.pure _ 0 (getD_len_le hst.2 0)) (by omega)
  refine ((spec_levelStep hn cap st (1 + i) hst.2).mono_k (by rw [hst.1])).mono
    (fun _ h => h) (fun r hr => ⟨?_, hr.2⟩)
  rw [hr.1, hst.1]
  have : h - i = (h - (i + 1)) + 1 := by omega
  rw [this, Nat.pow_succ, Nat.mul_div_cancel _ (by norm_num)]
theorem prf_ok (S : List Byte) (hS : S.length = 32) (lay tau e i : Nat) :
    PT (fmt (prfInput S lay tau e i)) ∧ (fmt (prfInput S lay tau e i)).blocks ≤ 1 := by
  refine ⟨?_, blocksFmt_le _ 1 (by simp [prfInput, hS]) le_rfl⟩
  unfold PT prfInput; rw [qbyte_tag]; omega
theorem spec_prf2 {P : Query → Prop} {β : Type} {R : β → Prop} (x : List Byte)
    {f : Val × Val → OracleComp HashSpec β} {kx l n : Nat} (hP : P (fmt x))
    (hk : (fmt x).blocks ≤ kx) (hf : ∀ v : Val × Val, v.1.length ≤ 16 → v.2.length ≤ 16 →
      Spec P R l (f v)) (hn : kx + l ≤ n) : Spec P R n (prf2 x >>= f) := by
  show Spec P R n ((qry (fmt x) >>= fun a => Pure.pure ((answerBytes 32 a).take 16,
    (answerBytes 32 a).drop 16)) >>= f)
  rw [bind_assoc]
  refine Spec.qry_bind hP (k := l) (fun u => ?_) (by omega)
  rw [pure_bind]
  exact hf _ (by simp) (by simp)
theorem spec_chainSteps (lay tau e i x : Nat) (v : Val) (hv : v.length ≤ 16) :
    Spec PT (fun r : Val × Val => r.1.length ≤ 16) 7 (chainSteps lay tau e i x v) := by
  unfold chainSteps
  refine Spec.foldlM_range'_le (P := PT) 1 7 _ (fun _ (st : Val × Val) => st.1.length ≤ 16)
    (fun _ => 1) (v, v) hv (fun i' _ st hst => ?_) (fun _ h => h) (by simp)
  refine spec_hash16_bind (chainInput lay tau e i (1 + i') st.1) ?_
    (blocksFmt_le _ 1 (by simp [chainInput]; omega) le_rfl)
    (fun w hw => Spec.pure _ 0 (by simp [hw])) le_rfl
  unfold PT chainInput; rw [qbyte_tag]; omega
theorem spec_buildLeaf (S : List Byte) (hS : S.length = 32) (lay tau e : Nat) (x : List Nat) :
    Spec PT (fun r : Val × List Val => r.1.length ≤ 16) 326 (buildLeaf S lay tau e x) := by
  unfold buildLeaf
  refine Spec.bind' (Spec.foldlM_range (P := PT) (nChains / 2) _
    (fun i (st : List Val × List Val) => st.1.length = 2 * i ∧ AllShort st.1) (fun _ => 15)
    ([], []) ⟨rfl, AllShort.nil⟩ (fun k _ st hst => ?_)) (fun st hst => ?_)
    (show (∑ _i ∈ range (nChains / 2), 15) + 11 ≤ 326 by decide)
  · obtain ⟨h1, h2⟩ := prf_ok S hS lay tau e k
    refine spec_prf2 _ h1 h2 (l := 14) (fun s hs0 hs1 => ?_) (by omega)
    obtain ⟨s0, s1⟩ := s
    refine (spec_chainSteps lay tau e (2 * k) _ s0 hs0).bind' (l := 7) (fun r0 hr0 => ?_) le_rfl
    obtain ⟨v0, c0⟩ := r0
    refine (spec_chainSteps lay tau e (2 * k + 1) _ s1 hs1).bind' (l := 0)
      (fun r1 hr1 => ?_) (by omega)
    obtain ⟨v1, c1⟩ := r1
    refine Spec.pure _ 0 ⟨by simp [hst.1]; omega, fun w hw => ?_⟩
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with hw | rfl | rfl
    · exact hst.2 w hw
    · exact hr0
    · exact hr1
  refine spec_hash16_bind (leafInput lay tau e st.1) ?_ (blocksFmt_le _ 11 ?_ (by omega))
    (fun v hv => Spec.pure _ 0 (by simp [hv])) (show 11 + 0 ≤ 11 by omega)
  · unfold PT leafInput; rw [qbyte_tag]; omega
  · have := length_flatten_le hst.2
    simp only [leafInput, length_thInput, length_tweak, hst.1] at this ⊢
    simp only [nChains] at this; omega
theorem spec_buildLeaves (S : List Byte) (hS : S.length = 32) (lay tau h cap : Nat)
    (x : List Nat) :
    Spec PT (fun r : List Val × List Val => r.1.length = 2 ^ h ∧ AllShort r.1) (2 ^ h * 326)
      (buildLeaves S lay tau h cap x) := by
  unfold buildLeaves
  refine Spec.foldlM_range_le (P := PT) (2 ^ h) _
    (fun i (st : List Val × List Val) => st.1.length = i ∧ AllShort st.1) (fun _ => 326) ([], [])
    ⟨rfl, AllShort.nil⟩ (fun i _ st hst => ?_) (fun _ h => h) (by simp)
  refine (spec_buildLeaf S hS lay tau i x).bind' (l := 0) (fun r hr => ?_) (by omega)
  obtain ⟨v, c⟩ := r
  exact Spec.pure _ 0 ⟨by simp [hst.1], hst.2.append hr⟩
def treeCost (h : Nat) : Nat := 2 ^ h * 326 + (2 ^ h - 1)
theorem spec_buildTree (S : List Byte) (hS : S.length = 32) (lay tau h cap : Nat)
    (x : List Nat) :
    Spec PT (fun r : Val × List Val × List Val => r.1.length ≤ 16) (treeCost h)
      (buildTree S lay tau h cap x) := by
  unfold buildTree treeCost
  refine (spec_buildLeaves S hS lay tau h cap x).bind (fun r hr => ?_)
  obtain ⟨leaves, vals⟩ := r
  refine (spec_buildLevels (nodeOK_nodeInput lay tau) cap h leaves hr.1 hr.2).bind' (l := 0)
    (fun r' hr' => ?_) (by omega)
  obtain ⟨root, path⟩ := r'
  exact Spec.pure _ 0 hr'
theorem treeCost_6 : treeCost 6 = 20927 := by decide
theorem treeCost_5 : treeCost 5 = 10463 := by decide
def PK (q : Query) : Prop := qbyte q 1 ≤ 3 ∨ qbyte q 1 = 13 ∨ qbyte q 1 = 14
theorem getD_append_left' {α : Type} (l l' : List α) (d : α) (n : Nat) (h : n < l.length) :
    (l ++ l').getD n d = l.getD n d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
theorem getD_append_single {α : Type} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]
theorem spec_buildAllLevels {P : Query → Prop} {node : NodeFmt} (hn : NodeOK P node) (h : Nat)
    (leaves : List Val) (hlen : leaves.length = 2 ^ h) (hl : AllShort leaves) :
    Spec P (fun levels : List (List Val) => ∀ k, k ≤ h →
        (levels.getD k []).length = 2 ^ (h - k) ∧ AllShort (levels.getD k []))
      (2 ^ h - 1) (buildAllLevels node h leaves) := by
  unfold buildAllLevels
  rw [← sum_levels h]
  refine Spec.foldlM_range'_le (P := P) 1 h _
    (fun i (levels : List (List Val)) => levels.length = i + 1 ∧ ∀ k, k ≤ i →
      (levels.getD k []).length = 2 ^ (h - k) ∧ AllShort (levels.getD k []))
    (fun i => 2 ^ (h - i) / 2) [leaves] ⟨rfl, fun k hk => ?_⟩ (fun i hi levels hlv => ?_)
    (fun levels hlv k hk => hlv.2 k hk) le_rfl
  · have : k = 0 := by omega
    subst this; simp [hlen, hl]
  · have hi' : 1 + i - 1 = i := by omega
    rw [hi']
    obtain ⟨hA, hB⟩ := hlv.2 i le_rfl
    refine ((spec_buildLevel hn (1 + i) (levels.getD i []) hB).mono_k (by rw [hA])).bind'
      (l := 0) (fun level hlevel => Spec.pure _ 0 ⟨by simp [hlv.1], fun k hk => ?_⟩) (by omega)
    rcases Nat.lt_or_ge k (i + 1) with hk' | hk'
    · rw [getD_append_left' _ _ _ _ (by rw [hlv.1]; exact hk')]
      exact hlv.2 k (by omega)
    · have : k = levels.length := by rw [hlv.1]; omega
      rw [this, getD_append_single]
      refine ⟨?_, hlevel.2⟩
      rw [hlevel.1, hA, ← this, hlv.1] at *
      have e : h - i = (h - (i + 1)) + 1 := by omega
      rw [show k = i + 1 by omega, e, Nat.pow_succ, Nat.mul_div_cancel _ (by norm_num)]
theorem length_xorBytes_le (a b : List Byte) (hb : b.length = 16) : (xorBytes a b).length ≤ 16 := by
  unfold xorBytes; rw [List.length_zipWith]; omega
theorem mask_ok (S : List Byte) (hS : S.length = 32) (l j : Nat) :
    (13 = qbyte (fmt (maskInput S l j)) 1) ∧ (fmt (maskInput S l j)).blocks ≤ 1 := by
  refine ⟨?_, blocksFmt_le _ 1 (by simp [maskInput, hS]) le_rfl⟩
  unfold maskInput; rw [qbyte_tag]
theorem spec_maskLevel {P : Query → Prop} (hP : ∀ q, qbyte q 1 = 13 → P q) (S : List Byte)
    (hS : S.length = 32) (l : Nat) (level : List Val) :
    Spec P (fun r : List Val => r.length = level.length ∧ AllShort r) level.length
      (maskLevel S l level) := by
  unfold maskLevel
  refine Spec.foldlM_range_le (P := P) level.length _
    (fun i (acc : List Val) => acc.length = i ∧ AllShort acc) (fun _ => 1) [] ⟨rfl, AllShort.nil⟩
    (fun j _ acc hacc => ?_) (fun _ h => h) (by simp)
  obtain ⟨h1, h2⟩ := mask_ok S hS l j
  exact spec_hash16_bind (maskInput S l j) (hP _ h1.symm) h2
    (fun mk hmk => Spec.pure _ 0 ⟨by simp [hacc.1], hacc.2.append (length_xorBytes_le _ _ hmk)⟩)
    le_rfl
theorem topN_succ (l : Nat) : topN (l + 1) = topN l + 2 ^ (topH - l) := by
  simp [topN, List.range_succ]
def keygenCost : Nat := 2 ^ 11 * 326 + (2 ^ 11 - 1) + ∑ l ∈ range 11, 2 ^ (11 - l) + 1025
theorem keygenCost_eq : keygenCost = 674814 := by decide
theorem spec_keygenRef (sk : Bytes 32) :
    Spec PK (fun _ => True) keygenCost (keygenRef sk) := by
  have hS := length_toList sk
  have hPT : ∀ q, PT q → PK q := fun q h => Or.inl h
  unfold keygenRef keygenList keygenCost
  refine Spec.bind' (Q := fun _ => True) (l := 0) ?_ (fun _ _ => Spec.pure _ 0 trivial) le_rfl
  rw [topH_eq]
  refine Spec.bind' (((spec_buildLeaves (toList sk) hS 0 0 11 0 []).mono hPT fun _ h => h))
    (fun r hr => ?_) (show 2 ^ 11 * 326 + ((2 ^ 11 - 1) + ∑ l ∈ range 11, 2 ^ (11 - l) + 1025) ≤ _
      by omega)
  obtain ⟨leaves, _⟩ := r
  refine Spec.bind' ((spec_buildAllLevels (nodeOK_nodeInput 0 0) 11 leaves hr.1 hr.2).mono hPT
    fun _ h => h) (fun levels hlev => ?_) (show (2 ^ 11 - 1) + (∑ l ∈ range 11, 2 ^ (11 - l) + 1025)
      ≤ _ by omega)
  refine Spec.bind' (Spec.foldlM_range (P := PK) 11 _
    (fun l (acc : List Val) => acc.length = topN l ∧ AllShort acc) (fun l => 2 ^ (11 - l)) []
    ⟨rfl, AllShort.nil⟩ (fun l hl acc hacc => ?_)) (fun masked hm => ?_) le_rfl
  · obtain ⟨hL, hA⟩ := hlev l (by omega)
    refine ((spec_maskLevel (fun q h => Or.inr (Or.inl h)) (toList sk) hS l _ ).mono_k
      (k' := 2 ^ (11 - l)) (by rw [hL])).bind' (l := 0)
      (fun ml hml => Spec.pure _ 0 ⟨?_, fun w hw => ?_⟩) (by omega)
    · rw [List.length_append, hacc.1, hml.1, hL, topN_succ, topH_eq]
    · rw [List.mem_append] at hw
      rcases hw with hw | hw
      · exact hacc.2 w hw
      · exact hml.2 w hw
  · have hreg : masked.flatten.length ≤ 16 * 4094 := by
      have := length_flatten_le hm.2
      rw [hm.1, show topN 11 = 4094 by decide] at this
      omega
    show Spec PK _ _ (qry (fmt (macInput (toList sk) masked.flatten)) >>= fun tag => Pure.pure _)
    refine Spec.qry_bind (Or.inr (Or.inr ?_)) (fun u => Spec.pure _ 0 trivial)
      (blocksFmt_le _ 1025 ?_ (by omega) |> fun h => by omega)
    · unfold macInput; rw [qbyte_tag]
    · simp only [macInput, length_thInput, length_tweak, List.length_append, hS]; omega
theorem spec_buildPorsLeaves (S : List Byte) (hS : S.length = 32) (idx : Nat) :
    Spec PP (fun r : List Val × List Val => r.1.length = porsT ∧ AllShort r.1)
      (porsT / 2 * 3) (buildPorsLeaves S idx) := by
  unfold buildPorsLeaves
  refine Spec.foldlM_range_le (P := PP) (porsT / 2) _
    (fun i (st : List Val × List Val) => st.1.length = 2 * i ∧ AllShort st.1) (fun _ => 3) ([], [])
    ⟨rfl, AllShort.nil⟩ (fun q _ st hst => ?_)
    (fun _ h => ⟨by rw [h.1]; decide, h.2⟩) (by simp)
  refine spec_prf2 (porsPrfInput S idx q) ?_
    (blocksFmt_le _ 1 (by simp [porsPrfInput, thInput, hS]) le_rfl) (l := 2)
    (fun s hs0 hs1 => ?_) (show 1 + 2 ≤ 3 by omega)
  · unfold PP porsPrfInput; rw [qbyte_tag]; omega
  obtain ⟨s0, s1⟩ := s
  dsimp only at hs0 hs1 ⊢
  refine spec_hash16_bind (porsLeafInput idx (2 * q) s0) ?_
    (blocksFmt_le _ 1 (by simp [porsLeafInput, thInput]; omega) le_rfl) (l := 1)
    (fun l0 hl0 => ?_) le_rfl
  · unfold PP porsLeafInput; rw [qbyte_tag]; omega
  refine spec_hash16_bind (porsLeafInput idx (2 * q + 1) s1) ?_
    (blocksFmt_le _ 1 (by simp [porsLeafInput, thInput]; omega) le_rfl)
    (fun l1 hl1 => Spec.pure _ 0 ⟨by simp [hst.1]; omega, fun w hw => ?_⟩) le_rfl
  · unfold PP porsLeafInput; rw [qbyte_tag]; omega
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with hw | rfl | rfl
  · exact hst.2 w hw
  · omega
  · omega
def porsCost : Nat := porsT / 2 * 3 + (2 ^ porsH - 1)
theorem porsCost_eq : porsCost = 40959 := by decide
theorem spec_buildPorsTree (S : List Byte) (hS : S.length = 32) (idx : Nat) :
    Spec PP (fun r : List (List Val) × List Val => ((r.1.getD porsH []).getD 0 []).length ≤ 16)
      porsCost (buildPorsTree S idx) := by
  unfold buildPorsTree porsCost
  refine (spec_buildPorsLeaves S hS idx).bind (fun r hr => ?_)
  obtain ⟨leaves, secrets⟩ := r
  refine (spec_buildAllLevels (nodeOK_porsNodeFmt idx) porsH leaves hr.1 hr.2).bind' (l := 0)
    (fun levels hl => Spec.pure _ 0 (getD_len_le (hl porsH le_rfl).2 0)) (by omega)
def PC (lay : Nat) (q : Query) : Prop := qbyte q 1 = 4 ∧ qbyte q 2 = lay
def PD (q : Query) : Prop := qbyte q 1 = 7 ∨ qbyte q 1 = 12
theorem enc_ok (lay tau e : Nat) (M : Val) (hM : M.length ≤ 16) (c : Nat) (hlay : lay < 256) :
    PC lay (fmt (encInput lay tau e M c)) ∧ (fmt (encInput lay tau e M c)).blocks ≤ 1 := by
  refine ⟨⟨?_, ?_⟩, blocksFmt_le _ 1 (by simp [encInput]; omega) le_rfl⟩
  · unfold encInput; rw [qbyte_tag]
  · unfold encInput; rw [qbyte_lay]; omega
theorem decodeDigits_some {v : Val} {x : List Nat} (h : decodeDigits v = some x) :
    x.length = 42 ∧ x.sum = targetSum := by
  unfold decodeDigits at h
  simp only at h
  split_ifs at h with h1 h2
  cases h
  exact ⟨by simp [digitsOfWord], h2⟩
def DigOK (o : Option (Nat × List Nat)) : Prop :=
  ∀ c x, o = some (c, x) → x.length = 42 ∧ x.sum = targetSum
theorem spec_searchCounter (lay tau e : Nat) (M : Val) (hM : M.length ≤ 16) (hlay : lay < 256) :
    ∀ fuel c, Spec (PC lay) DigOK fuel (searchCounter lay tau e M c fuel) := by
  intro fuel
  induction fuel with
  | zero => intro c; exact Spec.pure _ _ (by simp [DigOK])
  | succ n ih =>
    intro c
    unfold searchCounter
    obtain ⟨h1, h2⟩ := enc_ok lay tau e M hM c hlay
    refine spec_hash16_bind _ h1 h2 (l := n) (fun d _ => ?_) (by omega)
    split
    · next x hx =>
      exact Spec.pure _ _ (by
        intro c' x' h; cases h; exact decodeDigits_some hx)
    · exact ih (c + 1)
theorem rnd_ok (S m : List Byte) (hS : S.length = 32) (hm : m.length = 32) (a : Nat) :
    PD (fmt (rndInput S m a)) ∧ (fmt (rndInput S m a)).blocks ≤ 1 := by
  refine ⟨Or.inl ?_, blocksFmt_le _ 1 (by simp [rndInput, hS, hm]) (by omega)⟩
  rw [qbyte_fmt _ _ (by decide)]
  simp [rndInput, byte_toNat]
theorem dig_ok (rho m : List Byte) (hr : rho.length = 16) (hm : m.length = 32) :
    PD (fmt (digestInput rho m)) ∧ (fmt (digestInput rho m)).blocks ≤ 1 := by
  refine ⟨Or.inr ?_, by rw [Ref.fmt_digestInput rho m hr hm]; exact le_rfl⟩
  unfold digestInput; rw [qbyte_tag]
theorem spec_searchDigest (S m : List Byte) (hS : S.length = 32) (hm : m.length = 32) :
    ∀ fuel a, Spec PD (fun _ => True) (2 * fuel) (searchDigest S m a fuel) := by
  intro fuel
  induction fuel with
  | zero => intro a; exact Spec.pure _ _ trivial
  | succ n ih =>
    intro a
    unfold searchDigest
    obtain ⟨h1, h2⟩ := rnd_ok S m hS hm a
    refine spec_hash16_bind _ h1 h2 (l := 1 + 2 * n) (fun rho hrho => ?_) (by omega)
    obtain ⟨h3, h4⟩ := dig_ok rho m hrho hm
    show Spec PD _ _ (qry (fmt (digestInput rho m)) >>= fun b => Pure.pure b.toNat
      >>= fun N => if admissible N = true then Pure.pure (some (rho, N))
        else searchDigest S m (a + 1) n)
    refine Spec.qry_bind h3 (k := 2 * n) (fun u => ?_) (by omega)
    rw [pure_bind]
    split
    · exact Spec.pure _ _ trivial
    · exact ih (a + 1)
end SigGolfCandidate.Budget
end
