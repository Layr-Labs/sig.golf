import SigGolfCandidate.T3M.Mem
import SigGolfCandidate.T3M.Verify.Exec
import SigGolfCandidate.ClaudeWCT.WCT9.Forest
import SigGolfCandidate.ClaudeWCT.W9.T3M.SigCodecC
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.Data

section





namespace ClaudeWCT.W9.Machine.Sign
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M Pieces Layer chainCount height privateMac privateNonce)
abbrev SK : Nat := 0x80
abbrev SIG : Nat := 0x7000
abbrev DIG : Nat := 0x20120
abbrev NBUF : Nat := 0x20160
abbrev FOUT : Nat := 0x203A0
abbrev IDXV : Nat := 0x20550
abbrev TBL : Nat := 0xfef000
abbrev COST : Nat := 0xfeb000
abbrev PRIVW : Nat := 0x50000
abbrev PAIRW : Nat := 0x50040
abbrev CHAINW : Nat := 0x50100
abbrev LEAFW : Nat := 0x50200
abbrev NODEW : Nat := 0x50300
abbrev FORW : Nat := 0x50600
abbrev NOUTW : Nat := 0x50500
abbrev HEAPW : Nat := 0x51000
abbrev SCREND : Nat := 0x52010
def hook153 : BitVec 32 := 0x1890a06f
def hook540 : BitVec 32 := 0x3791306f
def NewCodeAt (im : Image) : Prop := signNew <+: im.code.drop 11003
/-- [h2 lane] the sign prepass appended at word 20813 (entered from the record's copy at 20730): move digest 192 (the top
sibling, scratch 0x7ca0) to the last scratch slot and digests 193..340 down one slot, then return to 20731. -/
def h2SignTail : List (BitVec 32) := [0x8e37, 0xca0e0e13, 0xe3703, 0x8e3783, 0xe0e93, 0x10e0e13, 0x8f37, 0x5f0f0f13,
  0xe3303, 0x8e3383, 0x6eb023, 0x7eb423, 0x10e0e13, 0x10e8e93, 0xffee64e3, 0xeeb023, 0xfeb423, 0x8e37, 0xe71ff06f]
def HooksAt (im : Image) : Prop :=
  im.code[153]? = some hook153 ∧ im.code[540]? = some hook540 ∧ im.code[545]? = some 0x00000073 ∧
    h2SignTail <+: im.code.drop 20813
def SignCodeAt (im : Image) : Prop := NewCodeAt im ∧ HooksAt im
def TableAt (t : MachineState) : Prop :=
  ∀ k < 8192, t.getMem (BitVec.ofNat 64 (TBL + 8 * k)) = bytesToWordLE ((tblBytes.drop (8 * k)).take 8)
def CostAt (t : MachineState) : Prop :=
  ∀ k < 2048, t.getMem (BitVec.ofNat 64 (COST + 8 * k)) = bytesToWordLE ((costBytes.drop (8 * k)).take 8)
def OutAt (t : MachineState) (A : Nat) (N : BitVec 256) : Prop :=
  ∀ k < 4, t.getMem (BitVec.ofNat 64 (A + 8 * k)) = N.extractLsb' (64 * k) 64
structure SearchPre (rho : Digest) (m : Message) (s : MachineState) : Prop where
  pc : s.pc = pcOf 153
  x5 : s.getReg .x5 = 0
  x19 : s.getReg .x19 = BitVec.ofNat 64 0
  rho : DigAt s DIG rho
  msg : ∀ k < 4, s.getMem (BitVec.ofNat 64 (DIG + 32 + 8 * k)) = m.extractLsb' (64 * k) 64
  cost : CostAt s
structure FailedS (t : MachineState) : Prop where
  pc : t.pc = pcOf 11174
  x5 : t.getReg .x5 = 1
  x10 : t.getReg .x10 = 1
def searchRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x19, .x20, .x21, .x22, .x24, .x25, .x28]
def SearchW (A : Nat) : Prop := A = DIG + 16 ∨ A = DIG + 24 ∨ (NBUF ≤ A ∧ A < NBUF + 32) ∨ A = IDXV
def SearchPost (s : MachineState) : Option (BitVec 32 × HashOutput) → MachineState → Prop
  | none, t => FailedS t
  | some (c, N), t => t.pc = pcOf 11175 ∧ t.getReg .x5 = 0 ∧ WCT9.producerAdmissible N = true ∧ OutAt t NBUF N ∧
      t.getReg .x22 = BitVec.ofNat 64 (WCT9.digestIndex N) ∧
      t.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 (WCT9.digestIndex N) ∧
      c.toNat < WCT9.digestAttemptLimit ∧ RegsExcept s t searchRegs ∧ Frame s t SearchW
def trialC : Nat := 200
def searchC : Nat := WCT9.digestAttemptLimit * trialC + 200
def SearchGood (im : Image) : Prop :=
  NewCodeAt im → HooksAt im → ∀ (sk : BitVec 256) (rho : Digest) (m : Message) (s : MachineState),
    SearchPre rho m s →
      TBSim im sk s searchC (WCT9.digestSearch rho m 0 WCT9.digestAttemptLimit) (SearchPost s)
def ScrZero (A : Nat) : Prop :=
  A = PRIVW + 48 ∨ A = PRIVW + 56 ∨ A = CHAINW ∨ A = CHAINW + 8 ∨ A = CHAINW + 32 ∨ A = CHAINW + 40 ∨
    A = NODEW + 32 ∨ A = NODEW + 40
structure FtsPre (sk : BitVec 256) (N : HashOutput) (s : MachineState) : Prop where
  pc : s.pc = pcOf 11175
  x5 : s.getReg .x5 = 0
  x22 : s.getReg .x22 = BitVec.ofNat 64 (WCT9.digestIndex N)
  adm : WCT9.admissible N = true
  nbuf : OutAt s NBUF N
  sk : ∀ k < 4, s.getMem (BitVec.ofNat 64 (SK + 8 * k)) = sk.extractLsb' (64 * k) 64
  zero : ∀ A, ScrZero A → s.getMem (BitVec.ofNat 64 A) = 0
  table : TableAt s
def ftsRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x18, .x24, .x25, .x26, .x28, .x29]
def FtsW (A : Nat) : Prop := (PRIVW ≤ A ∧ A < SCREND) ∨ (SIG + 16 ≤ A ∧ A < SIG + 2032) ∨ (FOUT ≤ A ∧ A < FOUT + 32)
def OpeningAt (t : MachineState) (k : Nat) (op : WCT9.Opening) : Prop :=
  (∀ i : Fin 7, DigAt t (SIG + 16 + 224 * k + 16 * i.val) (op.values i)) ∧
    ∀ l : Fin 7, DigAt t (SIG + 128 + 224 * k + 16 * l.val) (op.path l)
def FtsPost (s : MachineState) : List WCT9.Opening × Digest → MachineState → Prop
  | (ops, root), t => t.pc = pcOf 370 ∧ t.getReg .x5 = 0 ∧ DigAt t FOUT root ∧ ops.length = 9 ∧
      (∀ k < 9, OpeningAt t k (ops.getD k ⟨fun _ => 0, fun _ => 0⟩)) ∧ RegsExcept s t ftsRegs ∧ Frame s t FtsW
def ftsC : Nat := 2000000
def FtsGood (im : Image) : Prop :=
  NewCodeAt im → ∀ (sk : BitVec 256) (N : HashOutput) (s : MachineState), FtsPre sk N s →
    TBSim im sk s ftsC (WCT9.signForest (WCT9.digestIndex N) N) (FtsPost s)
/-- H2: scratch slot (relative to digest 127) read for compact output slot `p`: digest 192 (the top sibling,
slot 65) goes last, digests 193..340 move down one slot. -/
def cpIdx (p : Nat) : Nat := if p < 65 then p else if p < 213 then p + 1 else 65
def CompactPost (s t : MachineState) : Prop :=
  t.pc = pcOf 20745 ∧ t.getReg .x5 = 1 ∧ t.getReg .x10 = 0 ∧
    (∀ k < 428, t.getMem (BitVec.ofNat 64 (SIG + 2032 + 8 * k)) =
      s.getMem (BitVec.ofNat 64 (SIG + 2192 + 16 * cpIdx (k / 2) + 8 * (k % 2)))) ∧
    Frame s t (fun A => SIG + 2032 ≤ A ∧ A < SIG + 5616)
def compactK : Nat := 1 + 9 + 148 * 7 + 4 + 5 + 214 * 7 + 2
def CompactGood (im : Image) : Prop :=
  NewCodeAt im → HooksAt im → ∀ s : MachineState, s.pc = pcOf 540 →
    ∃ t, Steps im s compactK compactK t ∧ CompactPost s t
structure FailedT (t : MachineState) : Prop where
  pc : t.pc = pcOf 545
  x5 : t.getReg .x5 = 1
  x10 : t.getReg .x10 = 1
structure HookPre (sk : BitVec 256) (m : Message) (rho : Digest) (t : MachineState) : Prop where
  search : SearchPre rho m t
  sigRho : DigAt t SIG rho
  sk : ∀ k < 4, t.getMem (BitVec.ofNat 64 (SK + 8 * k)) = sk.extractLsb' (64 * k) 64
  zero : ∀ A, ScrZero A → t.getMem (BitVec.ofNat 64 A) = 0
  table : TableAt t
def frontC : Nat := 2490014
def FrontSpec (im : Image) (sk : BitVec 256) (cache : Bytes 131072) (m : Message) (s0 : MachineState)
    (Inv : MachineState → Prop) : Prop :=
  ∀ {α : Type} (W : Nat) (Q : Option α → MachineState → Prop) (K : Digest → M (Option α)),
    (∀ t, FailedT t → Q none t) →
    (∀ rho t, HookPre sk m rho t → Inv t → TBSim im sk t W (K rho) Q) →
    TBSim im sk s0 (frontC + W) (do
      let tag ← privateMac (cacheDec cache).region
      if tag ≠ (cacheDec cache).tag then pure none else privateNonce m >>= K) Q
structure LayPre (index : Nat) (root : Digest) (t : MachineState) : Prop where
  pc : t.pc = pcOf 370
  x5 : t.getReg .x5 = 0
  hidx : index < 2 ^ 31
  idx : t.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 index
  root : DigAt t FOUT root
def t3LayIdx (lay : Layer) : Nat := (![137, 203, 253, 302] : Layer → Nat) lay
def PieceAt (u : MachineState) (lay : Layer) (p : Pieces) : Prop :=
  (∀ i < chainCount lay, DigAt u (SIG + 16 * (t3LayIdx lay + i)) (p.1.getD i 0)) ∧
    ∀ j < height lay, DigAt u (SIG + 16 * (t3LayIdx lay + chainCount lay + j)) (p.2.getD j 0)
def LayPost (t : MachineState) : Option (List Pieces) → MachineState → Prop
  | none, u => FailedT u
  | some ps, u => u.pc = pcOf 540 ∧ ps.length = 4 ∧ (∀ lay : Layer, PieceAt u lay (ps.getD lay.val ([], []))) ∧
      Frame t u (fun A => ¬ (SIG ≤ A ∧ A < SIG + 2192))
def layC : Nat := 26 + 3014005327
def LayersSpec (im : Image) (sk : BitVec 256) (cache : Bytes 131072) (Inv : MachineState → Prop) : Prop :=
  ∀ (index : Nat) (root : Digest) (t : MachineState), LayPre index root t → Inv t →
    TBSim im sk t layC (WCT9.signLayersBC (cacheDec cache) index 4 (.forest root)) (LayPost t)
def newRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x18, .x19, .x20, .x21, .x22, .x24, .x25, .x26, .x28, .x29]
def NewW (A : Nat) : Prop := SearchW A ∨ FtsW A
def InvStable (Inv : MachineState → Prop) : Prop :=
  ∀ t u, Inv t → Frame t u NewW → RegsExcept t u newRegs → Inv u
def wsub (imgs : Phase → Image) : Submission :=
  ⟨⟨5454, 21484, 131072⟩, ⟨0x5BF0, 0x80, 0xA0, 0x80000, 0x7000, 0x800⟩, imgs⟩
structure Unchanged (imgs : Phase → Image) (Inv : BitVec 256 → Bytes 131072 → Message → MachineState → Prop) :
    Prop where
  front : ∀ sk cache m, ∃ s0, initialState (wsub imgs) .sign (sk, cache, m) = some s0 ∧
    FrontSpec (imgs .sign) sk cache m s0 (Inv sk cache m)
  stable : ∀ sk cache m, InvStable (Inv sk cache m)
  layers : ∀ sk cache m, LayersSpec (imgs .sign) sk cache (Inv sk cache m)
def SignRefinesW (imgs : Phase → Image) : Prop :=
  ∀ (sk : SecretKey) (cache : Bytes 131072) (m : Message),
    (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> (wsub imgs).run .sign (sk, cache, m) =
      (fun p => (p.1.map W9.T3M.sigBC, p.2.1, p.2.2)) <$> countBoth (mrealize sk (WCT9.Rev3.sign (cacheDec cache) m))
def SignTerminatesW (imgs : Phase → Image) : Prop :=
  ∀ (hash : Hash) (sk : SecretKey) (cache : Bytes 131072) (m : Message),
    ((wsub imgs).runWith hash .sign (sk, cache, m)).finished = true ∧
      ((wsub imgs).runWith hash .sign (sk, cache, m)).cycles < CYCLE_LIMIT
def SignMain : Prop :=
  ∀ (imgs : Phase → Image) (Inv : BitVec 256 → Bytes 131072 → Message → MachineState → Prop),
    SignCodeAt (imgs .sign) → Unchanged imgs Inv → SignRefinesW imgs ∧ SignTerminatesW imgs
end ClaudeWCT.W9.Machine.Sign
end

section

section
namespace ClaudeWCT.W9.Machine.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
def scfg : Config := {}
def cbase (c : Nat) : Nat := fieldIdx.getD c 0
def headLook (n : Nat) : Option (BitVec 32) := if 11003 ≤ n then headCode[n - 11003]? else none
def coordLook (c n : Nat) : Option (BitVec 32) :=
  if cbase c ≤ n then (coordCodes.getD c [])[n - cbase c]? else none
def tailLook (n : Nat) : Option (BitVec 32) := if 20715 ≤ n then tailCode[n - 20715]? else none
def hookLook (n : Nat) : Option (BitVec 32) :=
  if n = 153 then some hook153 else if n = 540 then some hook540 else if n = 545 then some 0x00000073 else none
def run (look : Nat → Option (BitVec 32)) (stops : List Nat) (n : Nat) (dirs : List Dir) : Option PRes :=
  pathAux scfg look (stops.map pcOf) 200 (pcOf n) dirs (σK []) []
theorem headCode_length : headCode.length = 183 := by decide +kernel
theorem coordCode0_length : coordCode0.length = 1052 := by decide +kernel
theorem coordCode1_length : coordCode1.length = 1059 := by decide +kernel
theorem coordCode2_length : coordCode2.length = 1060 := by decide +kernel
theorem coordCode3_length : coordCode3.length = 1060 := by decide +kernel
theorem coordCode4_length : coordCode4.length = 1059 := by decide +kernel
theorem coordCode5_length : coordCode5.length = 1060 := by decide +kernel
theorem coordCode6_length : coordCode6.length = 1060 := by decide +kernel
theorem coordCode7_length : coordCode7.length = 1059 := by decide +kernel
theorem coordCode8_length : coordCode8.length = 1060 := by decide +kernel
theorem tailCode_length : tailCode.length = 56 := by decide +kernel
theorem getElem?_append_off {α : Type} {a l : List α} {n k : Nat} {w : α} (ha : a.length = n)
    (h : l[k]? = some w) : (a ++ l)[n + k]? = some w := by
  rw [List.getElem?_append_right (by omega), ha, Nat.add_sub_cancel_left]; exact h
theorem getElem?_append_pre {α : Type} {a l : List α} {k : Nat} {w : α}
    (h : a[k]? = some w) : (a ++ l)[k]? = some w := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]; exact h
theorem signNew_head {k : Nat} {w : BitVec 32} (h : headCode[k]? = some w) : signNew[k]? = some w := by
  unfold signNew; exact getElem?_append_pre h
theorem signNew_tail {k : Nat} {w : BitVec 32} (h : tailCode[k]? = some w) : signNew[9712 + k]? = some w := by
  unfold signNew
  rw [show 9712 + k = 183 + (1052 + (1059 + (1060 + (1060 + (1059 + (1060 + (1060 + (1059 + (1060 + (k)))))))))) by omega]
  exact getElem?_append_off headCode_length (getElem?_append_off coordCode0_length (getElem?_append_off coordCode1_length (getElem?_append_off coordCode2_length (getElem?_append_off coordCode3_length (getElem?_append_off coordCode4_length (getElem?_append_off coordCode5_length (getElem?_append_off coordCode6_length (getElem?_append_off coordCode7_length (getElem?_append_off coordCode8_length (h))))))))))
theorem signNew_coord {c k : Nat} (hc : c < 9) {w : BitVec 32} (h : (coordCodes.getD c [])[k]? = some w) :
    signNew[cbase c - 11003 + k]? = some w := by
  unfold signNew
  interval_cases c
  · rw [show cbase 0 - 11003 + k = 183 + (k) by simp [cbase, fieldIdx] <;> omega]
    exact getElem?_append_off headCode_length (getElem?_append_pre h)
  · rw [show cbase 1 - 11003 + k = 183 + (1052 + (k)) by simp [cbase, fieldIdx] <;> omega]
    exact getElem?_append_off headCode_length (getElem?_append_off coordCode0_length (getElem?_append_pre h))
  · rw [show cbase 2 - 11003 + k = 183 + (1052 + (1059 + (k))) by simp [cbase, fieldIdx] <;> omega]
    exact getElem?_append_off headCode_length (getElem?_append_off coordCode0_length (getElem?_append_off coordCode1_length (getElem?_append_pre h)))
  · rw [show cbase 3 - 11003 + k = 183 + (1052 + (1059 + (1060 + (k)))) by simp [cbase, fieldIdx] <;> omega]
    exact getElem?_append_off headCode_length (getElem?_append_off coordCode0_length (getElem?_append_off coordCode1_length (getElem?_append_off coordCode2_length (getElem?_append_pre h))))
  · rw [show cbase 4 - 11003 + k = 183 + (1052 + (1059 + (1060 + (1060 + (k))))) by simp [cbase, fieldIdx] <;> omega]
    exact getElem?_append_off headCode_length (getElem?_append_off coordCode0_length (getElem?_append_off coordCode1_length (getElem?_append_off coordCode2_length (getElem?_append_off coordCode3_length (getElem?_append_pre h)))))
  · rw [show cbase 5 - 11003 + k = 183 + (1052 + (1059 + (1060 + (1060 + (1059 + (k)))))) by simp [cbase, fieldIdx] <;> omega]
    exact getElem?_append_off headCode_length (getElem?_append_off coordCode0_length (getElem?_append_off coordCode1_length (getElem?_append_off coordCode2_length (getElem?_append_off coordCode3_length (getElem?_append_off coordCode4_length (getElem?_append_pre h))))))
  · rw [show cbase 6 - 11003 + k = 183 + (1052 + (1059 + (1060 + (1060 + (1059 + (1060 + (k))))))) by simp [cbase, fieldIdx] <;> omega]
    exact getElem?_append_off headCode_length (getElem?_append_off coordCode0_length (getElem?_append_off coordCode1_length (getElem?_append_off coordCode2_length (getElem?_append_off coordCode3_length (getElem?_append_off coordCode4_length (getElem?_append_off coordCode5_length (getElem?_append_pre h)))))))
  · rw [show cbase 7 - 11003 + k = 183 + (1052 + (1059 + (1060 + (1060 + (1059 + (1060 + (1060 + (k)))))))) by simp [cbase, fieldIdx] <;> omega]
    exact getElem?_append_off headCode_length (getElem?_append_off coordCode0_length (getElem?_append_off coordCode1_length (getElem?_append_off coordCode2_length (getElem?_append_off coordCode3_length (getElem?_append_off coordCode4_length (getElem?_append_off coordCode5_length (getElem?_append_off coordCode6_length (getElem?_append_pre h))))))))
  · rw [show cbase 8 - 11003 + k = 183 + (1052 + (1059 + (1060 + (1060 + (1059 + (1060 + (1060 + (1059 + (k))))))))) by simp [cbase, fieldIdx] <;> omega]
    exact getElem?_append_off headCode_length (getElem?_append_off coordCode0_length (getElem?_append_off coordCode1_length (getElem?_append_off coordCode2_length (getElem?_append_off coordCode3_length (getElem?_append_off coordCode4_length (getElem?_append_off coordCode5_length (getElem?_append_off coordCode6_length (getElem?_append_off coordCode7_length (getElem?_append_pre h)))))))))
theorem newCode_word {im : Image} (h : NewCodeAt im) {k : Nat} {w : BitVec 32} (hk : signNew[k]? = some w) :
    im.code[11003 + k]? = some w := by
  obtain ⟨rest, hrest⟩ := h
  have hlen : k < signNew.length := (List.getElem?_eq_some_iff.mp hk).1
  have h2 : (im.code.drop 11003)[k]? = some w := by
    rw [← hrest, List.getElem?_append_left hlen]; exact hk
  rwa [List.getElem?_drop] at h2
theorem headLook_ok {im : Image} (h : NewCodeAt im) : LookOK im headLook := by
  intro n w hw
  unfold headLook at hw
  split at hw
  · rename_i hle
    have := newCode_word h (signNew_head hw)
    rwa [Nat.add_sub_cancel' hle] at this
  · cases hw
theorem cbase_ge (c : Nat) (hc : c < 9) : 11003 ≤ cbase c := by
  interval_cases c <;> decide +kernel
theorem coordLook_ok {im : Image} (h : NewCodeAt im) {c : Nat} (hc : c < 9) : LookOK im (coordLook c) := by
  intro n w hw
  unfold coordLook at hw
  split at hw
  · rename_i hle
    have := newCode_word h (signNew_coord hc hw)
    have hb := cbase_ge c hc
    rwa [show 11003 + (cbase c - 11003 + (n - cbase c)) = n by omega] at this
  · cases hw
theorem tailLook_ok {im : Image} (h : NewCodeAt im) : LookOK im tailLook := by
  intro n w hw
  unfold tailLook at hw
  split at hw
  · rename_i hle
    have := newCode_word h (signNew_tail hw)
    rwa [show 11003 + (9712 + (n - 20715)) = n by omega] at this
  · cases hw
theorem hookLook_ok {im : Image} (h : HooksAt im) : LookOK im hookLook := by
  intro n w hw
  obtain ⟨h1, h2, h3, -⟩ := h
  unfold hookLook at hw
  split_ifs at hw with e1 e2 e3
  · subst e1; cases hw; exact h1
  · subst e2; cases hw; exact h2
  · subst e3; cases hw; exact h3
def h2Look (n : Nat) : Option (BitVec 32) := if 20813 ≤ n then h2SignTail[n - 20813]? else none
/-- The record's tail window, then the H2 prepass: the path from the copy hook at 20730 runs through both. -/
def cLook (n : Nat) : Option (BitVec 32) := match tailLook n with | some w => some w | none => h2Look n
theorem h2Look_ok {im : Image} (h : HooksAt im) : LookOK im h2Look := by
  intro n w hw
  obtain ⟨-, -, -, ⟨rest, hrest⟩⟩ := h
  unfold h2Look at hw
  split at hw
  · rename_i hle
    have hlen : n - 20813 < h2SignTail.length := (List.getElem?_eq_some_iff.mp hw).1
    have h2 : (im.code.drop 20813)[n - 20813]? = some w := by
      rw [← hrest, List.getElem?_append_left hlen]; exact hw
    rwa [List.getElem?_drop, Nat.add_sub_cancel' hle] at h2
  · cases hw
theorem cLook_ok {im : Image} (h1 : NewCodeAt im) (h2 : HooksAt im) : LookOK im cLook := by
  intro n w hw
  unfold cLook at hw
  split at hw
  · rename_i w' hw'
    cases hw
    exact tailLook_ok h1 n _ hw'
  · exact h2Look_ok h2 n w hw
theorem run_sound {im : Image} {look : Nat → Option (BitVec 32)} (hl : LookOK im look) {stops : List Nat}
    {n : Nat} {dirs : List Dir} {r : PRes} (h : run look stops n dirs = some r) (s : MachineState)
    (hpc : s.pc = pcOf n) (hobl : ∀ o ∈ r.st.obl, o.holds s) (hbr : ∀ b ∈ r.brs, b.holds s) :
    Steps im s r.steps r.cycles (r.toState s) ∧
      (r.ecall = true → fetch im (r.toState s) = some (.base .ECALL)) :=
  pathRun_sound (known := []) h hl s hpc (by intro p hp; cases hp) hobl hbr
theorem PRes.toState_getReg' (r : PRes) (s : MachineState) (x : Reg) :
    (r.toState s).getReg x = (r.st.regs.get x).eval s := SymState.toState_getReg _ _ _ _
theorem PRes.toState_getMem' (r : PRes) (s : MachineState) (a : Word) :
    (r.toState s).getMem a = memEval s r.st.mem a := rfl
theorem PRes.toState_pc' (r : PRes) (s : MachineState) (h : r.spc = none) : (r.toState s).pc = r.pc := by
  simp [PRes.toState, PRes.finalPc, h]
end ClaudeWCT.W9.Machine.Sign
end
section
namespace ClaudeWCT.W9.Machine.Sign
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Spec publicHash shortHash privateHash privatePair privateInput header pad64 Coordinate
  HashOutput Digest)
section tb
variable {α β : Type} {im : Image} {sk : BitVec 256}
theorem TBSim.pure_steps' {s t : MachineState} {k c : Nat} {a : α} {Q : α → MachineState → Prop}
    (h : Steps im s k c t) (hQ : Q a t) : TBSim im sk s c (Pure.pure a) Q :=
  Sim.pure_steps h hQ
theorem TBSim.of_eq' {s : MachineState} {W W' : Nat} {p q : M α} {Q : α → MachineState → Prop}
    (h : TBSim im sk s W p Q) (he : p = q) (hW : W = W') : TBSim im sk s W' q Q := by
  subst he hW; exact h
theorem TBSim.publicHash_bind' {s : MachineState} {input : List UInt8} {W : Nat}
    {f : HashOutput → M β} {Q : β → MachineState → Prop}
    (hf : fetch im s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (pad64 input))
    (h : ∀ a, TBSim im sk (writeHash s a) W (f a) Q) :
    TBSim im sk s (8 * (toQ (pad64 input)).blocks + W) (publicHash input >>= f) Q := by
  unfold TBSim; rw [mrealize_bind, mrealize_publicHash]
  exact Sim.query_bind hf ht0 hv hq h
theorem TBSim.shortHash_bind' {s : MachineState} {input : List UInt8} {W : Nat}
    {f : Digest → M β} {Q : β → MachineState → Prop}
    (hf : fetch im s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (pad64 input))
    (h : ∀ a : BitVec 256, TBSim im sk (writeHash s a) W (f (a.extractLsb' 0 128)) Q) :
    TBSim im sk s (8 * (toQ (pad64 input)).blocks + W) (shortHash input >>= f) Q := by
  unfold TBSim; rw [mrealize_bind, mrealize_shortHash, map_eq_bind_pure_comp, bind_assoc]
  refine Sim.query_bind hf ht0 hv hq (fun a => ?_)
  have := h a
  unfold TBSim at this
  simpa only [Function.comp, pure_bind] using this
theorem TBSim.privateHash_bind' {s : MachineState} {co : Coordinate} {W : Nat}
    {f : HashOutput → M β} {Q : β → MachineState → Prop}
    (hf : fetch im s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (privateInput sk co))
    (h : ∀ a, TBSim im sk (writeHash s a) W (f a) Q) :
    TBSim im sk s (8 * (toQ (privateInput sk co)).blocks + W) (privateHash co >>= f) Q := by
  unfold TBSim; rw [mrealize_bind, mrealize_privateHash]
  exact Sim.query_bind hf ht0 hv hq h
theorem TBSim.privatePair_bind' {s : MachineState} {tag lay tree position index : Nat} {W : Nat}
    {f : Digest × Digest → M β} {Q : β → MachineState → Prop}
    (hf : fetch im s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true)
    (hq : hashInput s = toQ (privateInput sk (.inl (header tag lay tree position index))))
    (h : ∀ a : BitVec 256, TBSim im sk (writeHash s a) W
      (f (a.extractLsb' 0 128, a.extractLsb' 128 128)) Q) :
    TBSim im sk s (8 + W) (privatePair tag lay tree position index >>= f) Q := by
  have hb : (toQ (privateInput sk (.inl (header tag lay tree position index)))).blocks = 1 := by
    rw [blocks_toQ (privateInput_aligned _ _), privateInput_tweak_length]
  have : privatePair tag lay tree position index >>= f =
      privateHash (.inl (header tag lay tree position index)) >>= fun a =>
        f (a.extractLsb' 0 128, a.extractLsb' 128 128) := by
    unfold privatePair; rw [bind_assoc]; simp only [pure_bind]
  rw [this]
  exact TBSim.of_eq' (TBSim.privateHash_bind' hf ht0 hv hq h) rfl (by rw [hb])
end tb
theorem memEval_frame_ofNat (s : MachineState) (ws : SymMem) (A : Nat) (hA : A < 2 ^ 64)
    (h : ∀ p ∈ ws, p.1.base = none ∧ p.1.off.toNat ≠ A) :
    memEval s ws (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
  apply memEval_frame
  intro p hp heq
  obtain ⟨h1, h2⟩ := h p hp
  obtain ⟨⟨b, off⟩, v⟩ := p
  simp only at h1; subst h1
  simp only [Addr.eval] at heq
  apply h2; rw [← heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hA]
theorem memEval_cons_ofNat (s : MachineState) (k A : Nat) (v : E) (ws : SymMem) (hA : A < 2 ^ 64)
    (hk : k < 2 ^ 64) :
    memEval s ((⟨none, BitVec.ofNat 64 k⟩, v) :: ws) (BitVec.ofNat 64 A) =
      if A = k then v.eval s else memEval s ws (BitVec.ofNat 64 A) := by
  rw [memEval_cons]
  have e : Addr.eval s ⟨none, BitVec.ofNat 64 k⟩ = BitVec.ofNat 64 k := rfl
  by_cases h : A = k
  · subst h; rw [if_pos e.symm, if_pos rfl]
  · have hne : BitVec.ofNat 64 A ≠ Addr.eval s ⟨none, BitVec.ofNat 64 k⟩ := by
      rw [e]; intro he; exact h ((ofNat_inj hA hk).mp he)
    rw [if_neg hne, if_neg h]
@[simp] theorem E_eval_c' (s : MachineState) (v : Word) : (E.c v).eval s = v := rfl
@[simp] theorem E_eval_reg' (s : MachineState) (r : Reg) : (E.reg r).eval s = s.getReg r := rfl
end ClaudeWCT.W9.Machine.Sign
end
end
