import SigGolfCandidate.Choice.ProducerArithmetic
import SigGolfCandidate.Choice.Encoding
import SigGolfCandidate.T3M.Search.Basic

/-! Refinement of the assembly producer's canonical half selector.
The common 156-word body precedes the image-specific return jump. -/
namespace SigGolfCandidate.Choice.ProducerSelector
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Search SigGolfCandidate.T3M.Search.Reward
open SigGolfCandidate.T3 (Digest)
open ClaudeWCT.WCT9
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

def words : List (BitVec 32) := [0x3e3de13,0x240e0463,0xfff34313,0xfff00e13,0x9e5e13,0x1c3c3b3,0x10005b7,0x80058593,0xc93,0xa13,0x35513,0x7f57e13,0x1c58e33,0x800e4e83,0x1dc8cb3,0xe4e83,0x1da0a33,0x735513,0x7f57e13,0x1c58e33,0x800e4e83,0x1dc8cb3,0x80e4e83,0x1da0a33,0xe35513,0x7f57e13,0x1c58e33,0x800e4e83,0x1dc8cb3,0x80e4e83,0x1da0a33,0x1535513,0x7f57e13,0x1c58e33,0x800e4e83,0x1dc8cb3,0x80e4e83,0x1da0a33,0x1c35513,0x7f57e13,0x1c58e33,0x800e4e83,0x1dc8cb3,0x80e4e83,0x1da0a33,0x2335513,0x7f57e13,0x1c58e33,0x800e4e83,0x1dc8cb3,0x80e4e83,0x1da0a33,0x2a35513,0x7f57e13,0x1c58e33,0x800e4e83,0x1dc8cb3,0x80e4e83,0x1da0a33,0x3135513,0x7f57e13,0x1c58e33,0x800e4e83,0x1dc8cb3,0x80e4e83,0x1da0a33,0x3835513,0x7f57e13,0x1c58e33,0x800e4e83,0x1dc8cb3,0x80e4e83,0x1da0a33,0x3f35513,0x139e13,0x1c56533,0x7f57e13,0x1c58e33,0x800e4e83,0x1dc8cb3,0x100e4e83,0x1da0a33,0x63d513,0x7f57e13,0x1c58e33,0x800e4e83,0x1dc8cb3,0x80e4e83,0x1da0a33,0xd3d513,0x7f57e13,0x1c58e33,0x800e4e83,0x1dc8cb3,0x80e4e83,0x1da0a33,0x143d513,0x7f57e13,0x1c58e33,0x800e4e83,0x1dc8cb3,0x80e4e83,0x1da0a33,0x1b3d513,0x7f57e13,0x1c58e33,0x800e4e83,0x1dc8cb3,0x100e4e83,0x1da0a33,0x223d513,0x7f57e13,0x1c58e33,0x800e4e83,0x1dc8cb3,0x100e4e83,0x1da0a33,0x293d513,0x7f57e13,0x1c58e33,0x800e4e83,0x1dc8cb3,0x100e4e83,0x1da0a33,0x303d513,0x7f57e13,0x1c58e33,0x800e4e83,0x1dc8cb3,0x100e4e83,0x1da0a33,0x373d513,0x1ff57e13,0x1c58e33,0x180e4e83,0x1da0a33,0x757e13,0x1cc8cb3,0x355513,0x757e13,0x1cc8cb3,0x355513,0xac8cb3,0x9200e13,0x1cc9e63,0x2200e13,0x1ca6a63,0x63303,0x863383,0xe93,0x100006f,0x1063303,0x1863383,0x1000e93,0x20e37,0x45de3c23]

theorem words_length : words.length=156 := rfl
attribute [local irreducible] words

def Allowed (b : Nat) : Prop := b=21942 ∨ b=44046
def At (image : Image) (b : Nat) : Prop := CodeAt image (pcOf b) words

theorem slice {image : Image} {b : Nat} (hc : At image b) (k n : Nat) (hk : k ≤ 156) :
    CodeAt image (pcOf (b+k)) ((words.drop k).take n) := by
  have he : words = words.take k ++ (words.drop k).take n ++ (words.drop k).drop n := by
    simp only [List.append_assoc,List.take_append_drop]
  change CodeAt image (pcOf b) words at hc
  rw [he] at hc
  have hx := CodeAt.drop_prefix hc
  convert hx using 1
  simp only [List.length_take,words_length,Nat.min_eq_left hk,
    pcOf,ofNat_add_ofNat]
  congr 1
  omega

def start (q : Nat) : Nat := 10+7*q+(if q≤9 then 0 else 2)
def plen (q : Nat) : Nat := if q=9 then 5 else 3
def prefixCode (q : Nat) : List (BitVec 32) := (words.drop (start q)).take (plen q)
def windowE (q : Nat) : E :=
  if q<9 then mkBin .srl (.reg .x6) (.c (BitVec.ofNat 64 (7*q)))
  else if q=9 then mkBin .or (mkBin .srl (.reg .x6) (.c 63)) (mkBin .sll (.reg .x7) (.c 1))
  else mkBin .srl (.reg .x7) (.c (BitVec.ofNat 64 (7*q-64)))
def indexE (q : Nat) : E := mkBin .and (windowE q) (.c 127)
def prefixState (q : Nat) : SymState :=
  ⟨{RegFile.init with r10:=windowE q, r28:=mkAdd (.reg .x11) (indexE q)},[],[]⟩
def prefixResult (b q : Nat) : Result :=
  ⟨prefixState q,.c (pcOf (b+start q+plen q)),.endOfCode,plen q,plen q⟩
theorem prefix_run (b q : Nat) (hb : Allowed b) (hq : q<17) :
    symRun {noAlias:=true} (prefixCode q) (pcOf (b+start q)) 10 = some (prefixResult b q) := by
  rcases hb with rfl|rfl <;> interval_cases q <;> sym_eval

theorem index_eval (s : MachineState) (v : Digest) (q : Nat) (hq : q<17)
    (h6 : s.getReg .x6=v.extractLsb' 0 64) (h7 : s.getReg .x7=v.extractLsb' 64 64) :
    (indexE q).eval s = BitVec.ofNat 64 (topRank v q) := by
  by_cases h9 : q=9
  · subst q
    simp [indexE,windowE,mkBin_eval,E.eval,BinOp.eval,h6,h7]
    rw [BitVec.or_comm,topWindow_cross]
    simpa [topRank] using ext_shr_mask v 63 0 7 (by decide)
  · by_cases hl : q<9
    · simp only [indexE,windowE,if_pos hl,mkBin_eval,E.eval,BinOp.eval,h6]
      rw [show (BitVec.ofNat 64 (7*q)).toNat % 64 = 7*q by simp [Nat.mod_eq_of_lt (by omega : 7*q<64)]]
      simpa [topRank] using ext_shr_mask v 0 (7*q) 7 (by omega)
    · simp only [indexE,windowE,if_neg hl,if_neg h9,mkBin_eval,E.eval,BinOp.eval,h7]
      rw [show (BitVec.ofNat 64 (7*q-64)).toNat % 64 = 7*q-64 by simp [Nat.mod_eq_of_lt (by omega : 7*q-64<64)]]
      have he := ext_shr_mask v 64 (7*q-64) 7 (by omega)
      simpa [topRank,show 64+(7*q-64)=7*q by omega] using he

theorem prefix_spec {image : Image} {b : Nat} (hb : Allowed b) (hc : At image b)
    (s : MachineState) (v : Digest) (q : Nat) (hq : q<17)
    (hpc : s.pc=pcOf (b+start q))
    (h6 : s.getReg .x6=v.extractLsb' 0 64) (h7 : s.getReg .x7=v.extractLsb' 64 64)
    (h11 : s.getReg .x11=BitVec.ofNat 64 (TOP_DATA+2048)) :
    ∃ t, Steps image s (plen q) (plen q) t ∧ t.pc=pcOf (b+start q+plen q) ∧
      t.getReg .x28=BitVec.ofNat 64 (TOP_DATA+2048+topRank v q) ∧
      RegsExcept s t [.x10,.x28] ∧ Frame s t (fun _=>False) := by
  have hcode := slice hc (start q) (plen q) (by unfold start; split_ifs <;> omega)
  refine ⟨_,symRun_sound (prefix_run b q hb hq) hcode s hpc
    (by simp [prefixResult,prefixState,rv_simp]),rfl,?_,?_,?_⟩
  · change (mkAdd (.reg .x11) (indexE q)).eval s = _
    rw [mkAdd_eval,E.eval,index_eval s v q hq h6 h7,h11,ofNat_add_ofNat]
  · intro r hr; cases r <;> simp_all [prefixResult,prefixState,RegFile.init,rv_simp] <;> rfl
  · intro A _ _; rfl

def loadOffset (isReward : Bool) (q : Nat) : BitVec 12 :=
  if isReward then BitVec.ofNat 12 (128*topKind q) else 2048
def loadIndex (q : Nat) (isReward : Bool) : Nat := start q+plen q+(if isReward then 2 else 0)
def lookupValue (v : Digest) (q : Nat) (isReward : Bool) : Nat :=
  if isReward then topLookup (topKind q) (topRank v q) else rankLookup (topRank v q)
def loadWord (q : Nat) (isReward : Bool) : BitVec 32 := words.getD (loadIndex q isReward) 0
theorem kind_lt (q : Nat) : topKind q<3 := by unfold topKind; split_ifs <;> omega
theorem lookupValue_le (v : Digest) (q : Nat) (r : Bool) : lookupValue v q r≤255 := by
  cases r
  · exact rankLookup_le _
  · exact (topLookup_le _ _).trans (by decide)
theorem load_decode (q : Nat) (hq : q<17) (r : Bool) :
    decodeInstruction (loadWord q r) = some (.base (.LBU .x29 .x28 (loadOffset r q))) := by
  cases r <;> interval_cases q <;> kernel_rfl
def loadAddr (v : Digest) (q : Nat) (r : Bool) : Nat :=
  TOP_DATA+(if r then 2048+128*topKind q else 0)+topRank v q

theorem load_address (v : Digest) (q : Nat) (hq : q<17) (r : Bool) :
    BitVec.ofNat 64 (TOP_DATA+2048+topRank v q)+signExtend12 (loadOffset r q)=
      BitVec.ofNat 64 (loadAddr v q r) := by
  cases r
  · change BitVec.ofNat 64 (TOP_DATA+2048+topRank v q)+(-(BitVec.ofNat 64 2048)) =
      BitVec.ofNat 64 (TOP_DATA+topRank v q)
    rw [show TOP_DATA+2048+topRank v q=TOP_DATA+topRank v q+2048 by omega,
      ← ofNat_add_ofNat,BitVec.add_neg_eq_sub,BitVec.add_sub_cancel]
  · have ho : signExtend12 (loadOffset true q)=BitVec.ofNat 64 (128*topKind q) := by
      interval_cases q <;> decide +kernel
    rw [ho,ofNat_add_ofNat]
    congr 1
    simp only [loadAddr,if_true]
    omega

theorem load_access (v : Digest) (q : Nat) (r : Bool) :
    accessValid (BitVec.ofNat 64 (loadAddr v q r)) 1=true := by
  have hab : loadAddr v q r<16777216 := by
    have hr := topRank_lt v q
    have hk := kind_lt q
    dsimp [loadAddr,TOP_DATA]
    cases r <;> simp only [Bool.false_eq_true,if_false,if_true] <;> omega
  rw [accessValid_iff,toNat_ofNat_lt (by omega)]
  simp only [MEMORY_BYTES,Nat.mod_one,and_true,true_and]
  omega

theorem table_lookup (s : MachineState) (v : Digest) (q : Nat) (r : Bool)
    (hsum : SumTableOK s) (hrew : RewardTablesOK s) :
    (s.getByte (BitVec.ofNat 64 (loadAddr v q r))).zeroExtend 64=
      BitVec.ofNat 64 (lookupValue v q r) := by
  have hvb : s.getByte (BitVec.ofNat 64 (loadAddr v q r))=BitVec.ofNat 8 (lookupValue v q r) := by
    cases r
    · simpa [loadAddr,lookupValue] using hsum _ (topRank_lt v q)
    · simpa [loadAddr,lookupValue,Nat.add_assoc] using table_top s hrew (topKind q) (topRank v q)
        (kind_lt q) (topRank_lt v q)
  rw [hvb]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat]
  have := lookupValue_le v q r
  omega

theorem load_code (q : Nat) (hq : q<17) (r : Bool) :
    (words.drop (loadIndex q r)).take 1=[loadWord q r] := by
  cases r <;> interval_cases q <;> kernel_rfl

theorem lbu_post {image : Image} (s : MachineState) (pc : Word) (word : BitVec 32)
    (off : BitVec 12) (value : Word)
    (hc : CodeAt image pc [word]) (hpc : s.pc=pc)
    (hd : decodeInstruction word=some (.base (.LBU .x29 .x28 off)))
    (hv : accessValid (s.getReg .x28+signExtend12 off) 1=true)
    (he : (s.getByte (s.getReg .x28+signExtend12 off)).zeroExtend 64=value) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=s.pc+4 ∧ t.getReg .x29=value ∧
      RegsExcept s t [.x29] ∧ Frame s t (fun _=>False) := by
  have hs := steps_lbu hc hpc hd hv
  rw [he] at hs
  refine ⟨_,hs,rfl,?_,?_,?_⟩
  · change (s.setReg .x29 value).getReg .x29 = value
    exact MachineState.getReg_setReg_eq (by decide)
  · intro r hr
    cases r <;> first | exact False.elim (hr (by decide)) | rfl
  · intro A _ _; rfl

theorem load_spec {image : Image} {b : Nat} (hb : Allowed b) (hc : At image b)
    (s : MachineState) (v : Digest) (q : Nat) (hq : q<17) (r : Bool)
    (hsum : SumTableOK s) (hrew : RewardTablesOK s)
    (hpc : s.pc=pcOf (b+loadIndex q r))
    (h28 : s.getReg .x28=BitVec.ofNat 64 (TOP_DATA+2048+topRank v q)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf (b+loadIndex q r+1) ∧
      t.getReg .x29=BitVec.ofNat 64 (lookupValue v q r) ∧
      RegsExcept s t [.x29] ∧ Frame s t (fun _=>False) := by
  have ha : s.getReg .x28+signExtend12 (loadOffset r q)=BitVec.ofNat 64 (loadAddr v q r) := by
    rw [h28]; exact load_address v q hq r
  have hv : accessValid (s.getReg .x28+signExtend12 (loadOffset r q)) 1=true := by
    rw [ha]; exact load_access v q r
  have hcode : CodeAt image (pcOf (b+loadIndex q r)) [loadWord q r] := by
    have h := slice hc (loadIndex q r) 1 (by unfold loadIndex start plen; split_ifs <;> omega)
    rwa [load_code q hq r] at h
  obtain ⟨t,ht,pt,gt,rt,ft⟩ := lbu_post s _ (loadWord q r) (loadOffset r q)
    (BitVec.ofNat 64 (lookupValue v q r)) hcode hpc (load_decode q hq r) hv
    (by rw [ha]; exact table_lookup s v q r hsum hrew)
  refine ⟨t,ht,?_,gt,rt,ft⟩
  simpa only [hpc,pcOf_add4] using pt

end SigGolfCandidate.Choice.ProducerSelector
#print axioms SigGolfCandidate.Choice.ProducerSelector.prefix_spec
#print axioms SigGolfCandidate.Choice.ProducerSelector.load_spec
