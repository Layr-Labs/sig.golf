import SigGolfCandidate.T3M.Search.CounterSearch
import SigGolfCandidate.T3M.Search.CreditBlock
import SigGolfCandidate.T3M.Search.CapScan
import SigGolfCandidate.ClaudeWCT.WCT9.TopDecode
import SigGolfCandidate.T3.Nonbinary.CreditFilter

section
namespace SigGolfCandidate.T3M.Search.BC
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT
def left : WCT9.LayerMsg → Digest
  | .forest root => root
  | .pair l _ => l
def right : WCT9.LayerMsg → Digest
  | .forest _ => 0
  | .pair _ r => r
theorem counterWords (c : BitVec 32) :
    wordsOf (bytesLE 4 c ++ bytesLE 12 (0 : BitVec 96)) = [BitVec.ofNat 64 c.toNat, 0] := by
  have hc : T3.readLE (bytesLE 4 c ++ List.replicate 4 0) = c.toNat := by
    rw [readLE_append, readLE_bytesLE, readLE_replicate_zero]
    simp
  rw [show bytesLE 12 (0 : BitVec 96) = List.replicate 4 0 ++ List.replicate 8 0 by decide,
    ← List.append_assoc, wordsOf_append8 _ _ (by simp [bytesLE_length]), hc]
  rfl
theorem wordsOf_encodingInput (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (c : BitVec 32) :
    wordsOf (T3.pad64 (WCT9.layerEncodingInput lay tree leaf msg c)) =
      [(left msg).extractLsb' 0 64, (left msg).extractLsb' 64 64,
        BitVec.ofNat 64 (hdr0 4 lay.val tree 0), BitVec.ofNat 64 (hdr1 tree leaf),
        BitVec.ofNat 64 c.toNat, 0, (right msg).extractLsb' 0 64, (right msg).extractLsb' 64 64] := by
  cases msg with
  | forest root => simpa [WCT9.layerEncodingInput, left, right] using Search.wordsOf_encodingInput lay tree leaf root c
  | pair l r =>
    change wordsOf (T3.pad64 (WCT9.pairEncodingInputP lay tree leaf l r c 0)) = _
    rw [pad64_of_aligned _ (by simp [WCT9.pairEncodingInputP, bytesLE_length])]
    have he : WCT9.pairEncodingInputP lay tree leaf l r c 0 =
        (bytesLE 16 l ++ bytesLE 16 (T3.header 4 lay.val tree 0 leaf)) ++
          (bytesLE 4 c ++ bytesLE 12 (0 : BitVec 96)) ++ bytesLE 16 r := by
      simp only [WCT9.pairEncodingInputP, List.append_assoc]
    rw [he, wordsOf_append _ _ (by simp [bytesLE_length]),
      wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_append _ _ (by simp [bytesLE_length]),
      wordsOf_bytesLE16, wordsOf_header, counterWords, wordsOf_bytesLE16]
    rfl
theorem encodingInput_length (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (c : BitVec 32) :
    (T3.pad64 (WCT9.layerEncodingInput lay tree leaf msg c)).length = 64 := by
  cases msg with
  | forest root => exact Search.encodingInput_length lay tree leaf root c
  | pair l r =>
    change (T3.pad64 (WCT9.pairEncodingInputP lay tree leaf l r c 0)).length = 64
    rw [pad64_of_aligned _ (by simp [WCT9.pairEncodingInputP, bytesLE_length])]
    simp [WCT9.pairEncodingInputP, bytesLE_length]
theorem blocks_encodingInput (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (c : BitVec 32) :
    (toQ (T3.pad64 (WCT9.layerEncodingInput lay tree leaf msg c))).blocks = 1 := by
  have hl := encodingInput_length lay tree leaf msg c
  rw [blocks_toQ (by rw [Aligned, hl]; omega), hl]
end SigGolfCandidate.T3M.Search.BC
end
section
namespace SigGolfCandidate.T3M.Search.BC
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer)
open ClaudeWCT
set_option linter.unusedSimpArgs false
structure CsArgs where
  lay : Layer
  tree : Nat
  leaf : Nat
  msg : WCT9.LayerMsg
  ret : Nat
def csT (lay : Layer) : Nat := if lay = 0 then 412 else 200
def csOk (lay : Layer) : Nat := if lay = 0 then 1520 else 971
theorem capLimit_le (n : Nat) : capLimit n ≤ 2 ^ 22 := by unfold capLimit; split_ifs <;> omega
theorem capLimit_eq (lay : Layer) : capLimit lay.val = WCT9.searchLimit lay := by
  fin_cases lay <;> rfl
theorem length_filter_range (n : Nat) (p : Nat → Prop) [DecidablePred p] :
    ((List.range n).filter fun i => decide (p i)).length = ∑ i ∈ Finset.range n, if p i then 1 else 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih, Finset.sum_range_succ]
    by_cases h : p n <;> simp [h]
theorem producerDecode_top (v : Digest) :
    WCT9.producerDecode 0 v = if T3.topCredit v < 8 then none else T3.decode 0 v := by
  unfold WCT9.producerDecode
  cases hd : T3.decode 0 v with
  | none => simp
  | some ds =>
    simp only
    rw [WCT9.wordCredit_top hd, show WCT9.producerFloor 0 = 8 from rfl]
    by_cases h : T3.topCredit v < 8
    · rw [if_neg (by omega), if_pos h]
    · rw [if_pos (by omega), if_neg h]
theorem producerDecode_lower {lay : Layer} (hlz : lay ≠ 0) (v : Digest) (c : Nat) {ds : List Nat}
    (hdec : T3.decode lay v = some ds) (hds : ds = lowDigits v ++ [c]) :
    WCT9.producerDecode lay v = if scanFloor lay.val ≤ scanCredit v c then some ds else none := by
  unfold WCT9.producerDecode
  rw [hdec]
  simp only
  have hfl : WCT9.producerFloor lay = scanFloor lay.val := by
    fin_cases lay
    · exact absurd rfl hlz
    all_goals rfl
  have hcr : WCT9.wordCredit lay ds = scanCredit v c := by
    unfold WCT9.wordCredit scanCredit
    have hc : T3.chainCount lay = 43 := by
      fin_cases lay
      · exact absurd rfl hlz
      all_goals rfl
    have hm : ∀ i, T3.maxDigit lay i = 7 := by
      intro i; unfold T3.maxDigit; rw [if_neg hlz]
    simp only [hc, hm, hds]
    rw [show (fun i => decide ((lowDigits v ++ [c]).getD i 0 + 1 = 7)) =
        (fun i => decide ((lowDigits v ++ [c]).getD i 0 = 6)) from by
      funext i; congr 1; apply propext; omega]
    exact length_filter_range 43 _
  rw [hfl, hcr]
def cfFlag (b : Nat) : Nat := if b = 543 then 1 else 0
abbrev csRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x19, .x20, .x21, .x25, .x28, .x29, .x30]
def CsW (A : Nat) : Prop :=
  A = ENC + 16 ∨ A = ENC + 24 ∨ A = ENC + 32 ∨ (EOUT ≤ A ∧ A < EOUT + 32) ∨ DigW A
structure CsPre (b : Nat) (A : CsArgs) (s : MachineState) : Prop where
  pc : s.pc = pcOf (b + 103)
  x1 : s.getReg .x1 = pcOf A.ret
  x5 : s.getReg .x5 = 0
  x8 : s.getReg .x8 = BitVec.ofNat 64 A.lay.val
  x9 : s.getReg .x9 = BitVec.ofNat 64 A.tree
  x18 : s.getReg .x18 = BitVec.ofNat 64 A.leaf
  x17 : s.getReg .x17 = BitVec.ofNat 64 (T3.target A.lay)
  x26 : s.getReg .x26 = BitVec.ofNat 64 (T3.chainCount A.lay)
  x27 : s.getReg .x27 = BitVec.ofNat 64 (csN4 A.lay)
  htree : A.tree < 2 ^ 32
  hleaf : A.leaf < 2 ^ 32
  m0 : s.getMem (BitVec.ofNat 64 ENC) = (left A.msg).extractLsb' 0 64
  m8 : s.getMem (BitVec.ofNat 64 (ENC + 8)) = (left A.msg).extractLsb' 64 64
  c32 : ∃ x < 2 ^ 32, s.getMem (BitVec.ofNat 64 (ENC + 32)) = BitVec.ofNat 64 x
  z40 : s.getMem (BitVec.ofNat 64 (ENC + 40)) = 0
  r48 : s.getMem (BitVec.ofNat 64 (ENC + 48)) = (right A.msg).extractLsb' 0 64
  r56 : s.getMem (BitVec.ofNat 64 (ENC + 56)) = (right A.msg).extractLsb' 64 64
  table : TableOK s
  cf : CfTableOK (cfFlag b) s
structure CsInv (b : Nat) (A : CsArgs) (s0 : MachineState) (i : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf (capBase b)
  hi : i ≤ capLimit A.lay.val
  x19 : t.getReg .x19 = BitVec.ofNat 64 i
  h16 : t.getMem (BitVec.ofNat 64 (ENC + 16)) = BitVec.ofNat 64 (hdr0 4 A.lay.val A.tree 0)
  h24 : t.getMem (BitVec.ofNat 64 (ENC + 24)) = BitVec.ofNat 64 (hdr1 A.tree A.leaf)
  c32 : ∃ x < 2 ^ 32, t.getMem (BitVec.ofNat 64 (ENC + 32)) = BitVec.ofNat 64 x
  regs : RegsExcept s0 t csRegs
  frame : Frame s0 t CsW
def DummyOut (A : CsArgs) (s0 t : MachineState) : Prop :=
  t.pc = pcOf A.ret ∧
    (∀ j < 54, t.getByte (BitVec.ofNat 64 (DIGITS + j)) = BitVec.ofNat 8 (T3.dummyTop.getD j 0)) ∧
    (t.getMem (BitVec.ofNat 64 (ENC + 32))).toNat < 2 ^ 32 ∧ RegsExcept s0 t csRegs ∧ Frame s0 t CsW ∧
    (t.getReg .x25).toNat ≤ 129
def CsPost (image : Image) (b : Nat) (A : CsArgs) (s0 : MachineState) : Option (BitVec 32 × List Nat) → MachineState → Prop
  | none, t => if A.lay = 0 ∧ b = 543 then DummyOut A s0 t else
      t.pc = pcOf (b + 2) ∧ t.getReg .x5 = BitVec.ofNat 64 1 ∧ t.getReg .x10 = BitVec.ofNat 64 1 ∧
      fetch image t = some (.base .ECALL)
  | some (c, ds), t => t.pc = pcOf A.ret ∧ c.toNat < 2 ^ 22 ∧ t.getReg .x19 = BitVec.ofNat 64 c.toNat ∧
      t.getMem (BitVec.ofNat 64 (ENC + 32)) = BitVec.ofNat 64 c.toNat ∧
      (∃ v, T3.decode A.lay v = some ds) ∧ ds.length = T3.chainCount A.lay ∧
      (∀ j < T3.chainCount A.lay, t.getByte (BitVec.ofNat 64 (DIGITS + j)) = BitVec.ofNat 8 (ds.getD j 0)) ∧
      RegsExcept s0 t csRegs ∧ Frame s0 t CsW ∧ (t.getReg .x25).toNat ≤ T3.target A.lay
structure TrialSt (b : Nat) (A : CsArgs) (s0 : MachineState) (i : Nat) (u : MachineState) : Prop where
  x19 : u.getReg .x19 = BitVec.ofNat 64 i
  h16 : u.getMem (BitVec.ofNat 64 (ENC + 16)) = BitVec.ofNat 64 (hdr0 4 A.lay.val A.tree 0)
  h24 : u.getMem (BitVec.ofNat 64 (ENC + 24)) = BitVec.ofNat 64 (hdr1 A.tree A.leaf)
  c32 : u.getMem (BitVec.ofNat 64 (ENC + 32)) = BitVec.ofNat 64 i
  regs : RegsExcept s0 u csRegs
  frame : Frame s0 u CsW
theorem TrialSt.step {b : Nat} {A : CsArgs} {s0 u u' : MachineState} {i : Nat} (h : TrialSt b A s0 i u)
    {L : List Reg} (hr : RegsExcept u u' L)
    (hL : L.all (fun r => decide (r ∈ csRegs ∧ r ≠ .x19)) = true) (hf : Frame u u' (fun _ => False)) :
    TrialSt b A s0 i u' := by
  have hL' : ∀ r ∈ L, r ∈ csRegs ∧ r ≠ .x19 := fun r hr => by simpa using List.all_eq_true.1 hL r hr
  have hnot : ∀ r, r ∉ csRegs → r ∉ L := fun r h1 h2 => h1 (hL' r h2).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr.get (fun h' => (hL' _ h').2 rfl), h.x19]
  · rw [hf.get (by simp only [ENC]; omega) (by simp), h.h16]
  · rw [hf.get (by simp only [ENC]; omega) (by simp), h.h24]
  · rw [hf.get (by simp only [ENC]; omega) (by simp), h.c32]
  · exact (h.regs.trans hr).mono (fun r hr' => by
      rcases List.mem_append.1 hr' with h1 | h1
      · exact h1
      · exact (hL' r h1).1)
  · exact (h.frame.trans hf).mono (fun A _ h' => by simp only [or_false] at h'; exact h')
theorem TrialSt.reg {b : Nat} {A : CsArgs} {s0 u : MachineState} {i : Nat} (h : TrialSt b A s0 i u)
    {r : Reg} (hr : r ∉ csRegs) : u.getReg r = s0.getReg r := h.regs.get hr
section trial
variable {image : Image} {b : Nat} {sk : BitVec 256}
theorem cs_next {A : CsArgs} {s0 u : MachineState} {i F W : Nat} {Q : Option (BitVec 32 × List Nat) → MachineState → Prop}
    (hK : KernAt image b) (hu : TrialSt b A s0 i u) (hpc : u.pc = pcOf (b + 468)) (hi : i < capLimit A.lay.val)
    (ih : ∀ t, CsInv b A s0 (i + 1) t → TBSim image sk t W (WCT9.layerCounterSearch A.lay A.tree A.leaf A.msg (i + 1) F) Q) :
    TBSim image sk u (2 + W) (WCT9.layerCounterSearch A.lay A.tree A.leaf A.msg (i + 1) F) Q := by
  obtain ⟨t1, s1, p1, h19, r1, f1⟩ := cs468_spec hK u hpc i hu.x19
  have hcap := capLimit_le A.lay.val
  refine TBSim.steps s1 (ih t1 ⟨p1, by omega, h19, ?_, ?_, ⟨i, by omega, ?_⟩, ?_, ?_⟩)
  · rw [f1.get (by simp only [ENC]; omega) (by simp), hu.h16]
  · rw [f1.get (by simp only [ENC]; omega) (by simp), hu.h24]
  · rw [f1.get (by simp only [ENC]; omega) (by simp), hu.c32]
  · exact (hu.regs.trans r1).mono (by decide)
  · exact (hu.frame.trans f1).mono (fun A _ h' => by simp only [or_false] at h'; exact h')
theorem chainCount_eq (lay : Layer) : T3.chainCount lay = if lay = 0 then 54 else 43 := by
  fin_cases lay <;> rfl
theorem target_lt (lay : Layer) : T3.target lay < 2 ^ 63 := by
  fin_cases lay <;> decide
theorem getD_map_range {f : Nat → Nat} {n j : Nat} (hj : j < n) : ((List.range n).map f).getD j 0 = f j := by
  simp [List.getD_eq_getElem?_getD, hj]
theorem cs_success {A : CsArgs} {s0 u : MachineState} {i : Nat} (hK : KernAt image b) (hpre : CsPre b A s0)
    (hu : TrialSt b A s0 i u) (hpc : u.pc = pcOf (b + 438)) (hi : i < 2 ^ 22) (hlz : A.lay ≠ 0)
    (v : Digest) (S : Nat) (ds : List Nat) (hdec : T3.decode A.lay v = some ds)
    (hds : ds = lowDigits v ++ [T3.target A.lay - S]) (hS : S ≤ T3.target A.lay)
    (h6 : u.getReg .x6 = v.extractLsb' 0 64) (h7 : u.getReg .x7 = v.extractLsb' 64 64)
    (h25 : u.getReg .x25 = BitVec.ofNat 64 S) :
    TBSim image sk u 810 (pure (some (BitVec.ofNat 32 i, ds))) (CsPost image b A s0) := by
  have hl0 : A.lay.val ≠ 0 := fun h => hlz (Fin.ext h)
  obtain ⟨k, t, st, kle, tpc, tdig, tchk, tr, tf⟩ := cs_tail hK u hpc v A.lay.val
    (T3.target A.lay) S A.ret A.lay.isLt (target_lt _) (fun _ => hS)
    (by rw [hu.reg (by decide), hpre.x1]) (by rw [hu.reg (by decide), hpre.x8])
    (by rw [hu.reg (by decide), hpre.x17]) h25
    (by rw [hu.reg (by decide), hpre.x26, chainCount_eq]; simp [hlz, hl0])
    (by rw [hu.reg (by decide), hpre.x27, csN4]; simp [hlz, hl0]) h6 h7
  rw [if_neg hl0] at kle tdig
  have hc : (BitVec.ofNat 32 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
  refine (TBSim.steps st (TBSim.pure ?_)).mono kle (fun _ _ h => h)
  refine ⟨tpc, by rw [hc]; exact hi, by rw [hc, tr.get (by decide), hu.x19], ?_, ⟨v, hdec⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hc, tf.get (by simp only [ENC]; omega) (by simp only [DigW, DIGITS, ENC]; omega), hu.c32]
  · rw [hds, chainCount_eq, if_neg hlz]
    simp [lowDigits_length]
  · intro j hj
    rw [chainCount_eq, if_neg hlz] at hj
    rw [hds]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · rw [List.getD_append _ _ _ _ (by rw [lowDigits_length]; exact hj), lowDigits_eq, getD_map_range hj]
      simpa only [if_neg hl0] using tdig j hj
    · rw [List.getD_append_right _ _ _ _ (by rw [lowDigits_length]), lowDigits_length]
      simpa using tchk hl0
  · exact (hu.regs.trans tr).mono (by decide)
  · exact (hu.frame.trans tf).mono (fun A _ h => by
      rcases h with h | h
      · exact h
      · exact Or.inr (Or.inr (Or.inr (Or.inr h))))
  · rw [tr.get (by decide), h25, BitVec.toNat_ofNat]
    have := target_lt A.lay
    omega
theorem TrialSt.table {A : CsArgs} {s0 u : MachineState} {i : Nat}
    (hu : TrialSt b A s0 i u) (ht : TableOK s0) : TableOK u :=
  ht.frame hu.frame (by intro j hj; unfold CsW DigW TOP_DATA ENC EOUT DIGITS; omega)
theorem TrialSt.cf {A : CsArgs} {s0 u : MachineState} {i : Nat} {flag : Nat}
    (hu : TrialSt b A s0 i u) (ht : CfTableOK flag s0) : CfTableOK flag u :=
  ht.frame hu.frame (by intro j hj hj'; unfold CsW DigW TOP_DATA ENC EOUT DIGITS; omega)
theorem cs_top_success {A : CsArgs} {s0 u : MachineState} {i : Nat} (hK : KernAt image b)
    (hpre : CsPre b A s0) (hu : TrialSt b A s0 i u) (hpc : u.pc = pcOf (b + 363))
    (hi : i < 2 ^ 22) (hlz : A.lay = 0) (v : Digest) (hv : v.toNat < 2 ^ 125)
    (hvalid : T3.topRanksValid v = true) (hdec : T3.decode A.lay v = some (topDigits v))
    (h6 : u.getReg .x6 = v.extractLsb' 0 64) (h7 : u.getReg .x7 = v.extractLsb' 64 64)
    (h30 : u.getReg .x30 = BitVec.ofNat 64 TOP_DATA) (h25 : u.getReg .x25 = 129#64) (h20 : u.getReg .x20 = 0) :
    TBSim image sk u 301 (pure (some (BitVec.ofNat 32 i, topDigits v))) (CsPost image b A s0) := by
  obtain ⟨t, st, tpc, tdig, tr, tf⟩ := topUnpack_spec hK u v hv hvalid (hu.table hpre.table) hpc h6 h7 h30 h20
  have hc : (BitVec.ofNat 32 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
  refine TBSim.steps st (TBSim.pure ?_)
  refine ⟨?_, by rw [hc]; exact hi, ?_, ?_, ⟨v, hdec⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [tpc, hu.reg (by decide), hpre.x1, pcOf_and_not1]
  · rw [hc, tr.get (by decide), hu.x19]
  · rw [hc, tf.get (by unfold ENC; omega) (by unfold TopUnpack.Writes DIGITS ENC; omega), hu.c32]
  · rw [hlz, topDigits_length]; rfl
  · intro j hj
    rw [hlz] at hj
    change j < 54 at hj
    rw [tdig j hj]
    simp only [topDigits, getD_map_range hj]
  · exact (hu.regs.trans tr).mono (by decide)
  · exact (hu.frame.trans tf).mono (fun A _ h => by
      rcases h with h | h
      · exact h
      · exact Or.inr (Or.inr (Or.inr (Or.inr h))))
  · rw [tr.get (by decide), h25, hlz]; decide
theorem cs_answer {A : CsArgs} {s0 t : MachineState} {i : Nat} (hK : KernAt image b) (hpre : CsPre b A s0)
    (hI : CsInv b A s0 i t) (hi : i < capLimit A.lay.val) :
    ∃ k t2, Steps image t k k t2 ∧ k ≤ (if A.lay = 0 then 14 else 12) ∧ t2.pc = pcOf (b + 123) ∧
      fetch image t2 = some (.base .ECALL) ∧
      t2.getReg .x5 = 0 ∧ hashArgumentsValid t2 = true ∧
      hashInput t2 = toQ (T3.pad64 (WCT9.layerEncodingInput A.lay A.tree A.leaf A.msg (BitVec.ofNat 32 i))) ∧
      t2.getReg .x12 = BitVec.ofNat 64 EOUT ∧ TrialSt b A s0 i t2 := by
  have hcap := capLimit_le A.lay.val
  obtain ⟨k1, t1, s1, k1le, p1, r1, f1⟩ := cap_spec hK t hI.pc A.lay.val i A.lay.isLt hI.hi
    (by rw [hI.regs.get (by decide), hpre.x8]) hI.x19
  rw [if_neg (by omega)] at p1
  obtain ⟨x, hx, hx32⟩ := hI.c32
  obtain ⟨t2, s2, p2, c32, h10, h11, h12, r2, f2⟩ := cs115_spec hK t1 p1 i x (by omega) hx
    (by rw [r1.get (by decide), hI.x19]) (by rw [f1.get (by simp only [ENC]; omega) (by simp), hx32])
  have fr : Frame s0 t2 CsW := ((hI.frame.trans f1).trans f2).mono (fun A _ h => by
    simp only [or_false] at h; rcases h with h | h
    · exact h
    · exact Or.inr (Or.inr (Or.inl h)))
  have mem : ∀ A, A < 2 ^ 64 → ¬ CsW A → t2.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A) :=
    fun A hA hn => fr.get hA hn
  have hT : TrialSt b A s0 i t2 := by
    refine ⟨?_, ?_, ?_, c32, ((hI.regs.trans r1).trans r2).mono (by decide), fr⟩
    · rw [r2.get (by decide), r1.get (by decide), hI.x19]
    · rw [f2.get (by simp only [ENC]; omega) (by simp only [ENC]; omega), f1.get (by simp only [ENC]; omega) (by simp),
        hI.h16]
    · rw [f2.get (by simp only [ENC]; omega) (by simp only [ENC]; omega), f1.get (by simp only [ENC]; omega) (by simp),
        hI.h24]
  have hk : k1 + 8 ≤ (if A.lay = 0 then 14 else 12) := by
    have hl0 : (A.lay.val = 0) ↔ A.lay = 0 := ⟨fun h => Fin.ext h, fun h => by rw [h]; rfl⟩
    by_cases h : A.lay = 0
    · rw [if_pos (hl0.2 h)] at k1le; rw [if_pos h]; omega
    · rw [if_neg (fun h' => h (hl0.1 h'))] at k1le; rw [if_neg h]; omega
  refine ⟨_, t2, s1.trans s2, hk, p2, (codeAt_k_123 hK).fetch _ p2, by rw [hT.reg (by decide), hpre.x5],
    hashArgs_const t2 ENC 64 EOUT h10 h11 h12 (by decide) (by decide) (by decide) (by decide) (by decide),
    ?_, h12, hT⟩
  have hc : (BitVec.ofNat 32 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
  refine hashInput_toQ t2 _ 0 ENC (encodingInput_length _ _ _ _ _) h10 (by decide) (by decide) h11 (by decide) ?_
  rw [readWords_eight, wordsOf_encodingInput, hc]
  have nw : ∀ A, A = ENC ∨ A = ENC + 8 ∨ A = ENC + 40 ∨ A = ENC + 48 ∨ A = ENC + 56 → ¬ CsW A := by
    intro A hA; simp only [CsW, DigW, ENC, EOUT, DIGITS] at hA ⊢; omega
  rw [mem _ (by simp only [ENC]; omega) (nw _ (by omega)), mem _ (by simp only [ENC]; omega) (nw _ (by omega)),
    hT.h16, hT.h24, c32, mem _ (by simp only [ENC]; omega) (nw _ (by omega)),
    mem _ (by simp only [ENC]; omega) (nw _ (by omega)), mem _ (by simp only [ENC]; omega) (nw _ (by omega)),
    hpre.m0, hpre.m8, hpre.z40, hpre.r48, hpre.r56]
theorem TrialSt.hash {A : CsArgs} {s0 t2 : MachineState} {i : Nat} (hT : TrialSt b A s0 i t2)
    (h12 : t2.getReg .x12 = BitVec.ofNat 64 EOUT) (a : BitVec 256) : TrialSt b A s0 i (writeHash t2 a) := by
  have fw := Frame.writeHash t2 a EOUT h12 (by decide)
  refine ⟨by rw [getReg_writeHash, hT.x19], ?_, ?_, ?_, ?_, ?_⟩
  · rw [fw.get (by simp only [ENC]; omega) (by simp only [ENC, EOUT]; omega), hT.h16]
  · rw [fw.get (by simp only [ENC]; omega) (by simp only [ENC, EOUT]; omega), hT.h24]
  · rw [fw.get (by simp only [ENC]; omega) (by simp only [ENC, EOUT]; omega), hT.c32]
  · intro r hr; rw [getReg_writeHash]; exact hT.regs r hr
  · exact (hT.frame.trans fw).mono (fun A _ h => by
      rcases h with h | h
      · exact h
      · exact Or.inr (Or.inr (Or.inr (Or.inl h))))
theorem cfFlag_lt (b : Nat) : cfFlag b < 256 := by unfold cfFlag; split <;> omega
theorem cs_exhaust {A : CsArgs} {s0 t : MachineState} {i : Nat} (hK : KernAt image b) (hpre : CsPre b A s0)
    (hI : CsInv b A s0 i t) (hi : i = capLimit A.lay.val) :
    TBSim image sk t (0 * csT A.lay + csOk A.lay) (WCT9.layerCounterSearch A.lay A.tree A.leaf A.msg i 0)
      (CsPost image b A s0) := by
  obtain ⟨k1, t1, s1, k1le, p1, r1, f1⟩ := cap_spec hK t hI.pc A.lay.val i A.lay.isLt hI.hi
    (by rw [hI.regs.get (by decide), hpre.x8]) hI.x19
  rw [if_pos hi] at p1
  have hk1 : k1 ≤ 6 := by split_ifs at k1le <;> omega
  have h8 : t1.getReg .x8 = BitVec.ofNat 64 A.lay.val := by
    rw [r1.get (by decide), hI.regs.get (by decide), hpre.x8]
  have fr1 : Frame s0 t1 CsW := (hI.frame.trans f1).mono (fun A _ h => by simp only [or_false] at h; exact h)
  have hcf1 : CfTableOK (cfFlag b) t1 :=
    hpre.cf.frame fr1 (by intro j hj hj'; unfold CsW DigW TOP_DATA ENC EOUT DIGITS; omega)
  have prog : WCT9.layerCounterSearch A.lay A.tree A.leaf A.msg i 0 = pure none := rfl
  rw [prog]
  by_cases hd : A.lay = 0 ∧ b = 543
  · have hfl : cfFlag b ≠ 0 := by unfold cfFlag; rw [if_pos hd.2]; omega
    obtain ⟨t2, s2, p2, g6, g7, g20, g25, g30, r2, f2⟩ := Credit.exhaust_dummy hK t1 p1
      (by rw [h8, hd.1]; rfl) (cfFlag b) (cfFlag_lt b) hcf1 hfl
    have ht2 : TableOK t2 := hpre.table.frame (fr1.trans f2 |>.mono (fun A _ h => by
      simp only [or_false] at h; exact h)) (by intro j hj; unfold CsW DigW TOP_DATA ENC EOUT DIGITS; omega)
    obtain ⟨t3, s3, p3, dig3, r3, f3⟩ := topUnpack_spec hK t2 Credit.dummyDigest Credit.dummy_lt
      Credit.dummy_valid ht2 p2 g6 g7 g30 g20
    refine (TBSim.steps (s1.trans (s2.trans s3)) (TBSim.pure ?_)).mono ?_ (fun _ _ h => h)
    · change (if A.lay = 0 ∧ b = 543 then DummyOut A s0 t3 else _)
      rw [if_pos hd]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [p3, r2.get (by decide), r1.get (by decide), hI.regs.get (by decide), hpre.x1, pcOf_and_not1]
      · intro j hj
        rw [dig3 j hj, ← Credit.dummy_digits]
        simp only [topDigits, getD_map_range hj]
      · obtain ⟨x, hx, hx32⟩ := hI.c32
        rw [f3.get (by unfold ENC; omega) (by unfold TopUnpack.Writes DIGITS ENC; omega),
          f2.get (by unfold ENC; omega) (by simp), f1.get (by unfold ENC; omega) (by simp), hx32,
          BitVec.toNat_ofNat]
        omega
      · exact (((hI.regs.trans r1).trans r2).trans r3).mono (by decide)
      · exact ((fr1.trans f2).trans f3).mono (fun A _ h => by
          rcases h with (h | h) | h
          · exact h
          · exact absurd h id
          · exact Or.inr (Or.inr (Or.inr (Or.inr h))))
      · rw [r3.get (by decide), g25]; decide
    · unfold csOk; rw [if_pos hd.1]; omega
  · have hfl : A.lay.val ≠ 0 ∨ cfFlag b = 0 := by
      by_cases hz : A.lay = 0
      · right; unfold cfFlag; rw [if_neg (fun h => hd ⟨hz, h⟩)]
      · left; exact fun h => hz (Fin.ext h)
    obtain ⟨n, t2, hn, s2, p2, r2, f2⟩ := Credit.exhaust_fail hK t1 p1 A.lay.val A.lay.isLt h8 (cfFlag b)
      (cfFlag_lt b) hcf1 hfl
    obtain ⟨t3, s3, p3, h5, h10, hf⟩ := cs0_spec hK t2 p2
    refine (TBSim.steps (s1.trans (s2.trans s3)) (TBSim.pure ?_)).mono ?_ (fun _ _ h => h)
    · change (if A.lay = 0 ∧ b = 543 then DummyOut A s0 t3 else _)
      rw [if_neg hd]
      exact ⟨p3, h5, h10, hf⟩
    · unfold csOk; split_ifs <;> omega
theorem cs_loop {A : CsArgs} {s0 : MachineState} (hK : KernAt image b) (hpre : CsPre b A s0) :
    ∀ F i t, i + F = capLimit A.lay.val → CsInv b A s0 i t →
      TBSim image sk t (F * csT A.lay + csOk A.lay) (WCT9.layerCounterSearch A.lay A.tree A.leaf A.msg i F)
        (CsPost image b A s0) := by
  have hl0 : (A.lay.val = 0) ↔ A.lay = 0 := by
    constructor
    · intro h; exact Fin.ext h
    · intro h; rw [h]; rfl
  have hcap := capLimit_le A.lay.val
  intro F
  induction F with
  | zero =>
    intro i t h hI
    exact cs_exhaust hK hpre hI (by omega)
  | succ F ih =>
    intro i t h hI
    have hi : i < capLimit A.lay.val := by omega
    have hi22 : i < 2 ^ 22 := by omega
    obtain ⟨k2, t2, s2, k2le, p2, hf, h5, hv, hq, h12, hT⟩ := cs_answer hK hpre hI hi
    have prog : WCT9.layerCounterSearch A.lay A.tree A.leaf A.msg i (F + 1) =
        (T3.shortHash (WCT9.layerEncodingInput A.lay A.tree A.leaf A.msg (BitVec.ofNat 32 i)) >>= fun answer =>
          match WCT9.producerDecode A.lay answer with
          | none => WCT9.layerCounterSearch A.lay A.tree A.leaf A.msg (i + 1) F
          | some digits => pure (some (BitVec.ofNat 32 i, digits))) := rfl
    have ih' : ∀ t, CsInv b A s0 (i + 1) t → TBSim image sk t (F * csT A.lay + csOk A.lay)
        (WCT9.layerCounterSearch A.lay A.tree A.leaf A.msg (i + 1) F) (CsPost image b A s0) :=
      fun t ht => ih (i + 1) t (by omega) ht
    rw [prog]
    refine (TBSim.steps s2 (TBSim.shortHash_bind hf h5 hv hq
      (W := F * csT A.lay + csOk A.lay + (csT A.lay - (if A.lay = 0 then 22 else 20))) (fun a => ?_))).mono ?_
      (fun _ _ h => h)
    swap
    · rw [blocks_encodingInput, Nat.succ_mul]; unfold csT at *; split_ifs at k2le ⊢ <;> omega
    set v := a.extractLsb' 0 128 with hvdef
    have hT3 := hT.hash h12 a
    have p3 : (writeHash t2 a).pc = pcOf (b + 124) := by rw [pc_writeHash, p2, pcOf_add4]
    have hd := DigAt.writeHash_lo t2 a EOUT h12 (by decide)
    obtain ⟨t4, s4, p4, h6, h7, h25, r4, f4⟩ := cs124_spec hK (writeHash t2 a) p3 A.lay.val A.lay.isLt
      (by rw [hT3.reg (by decide), hpre.x8])
    rw [hd.1] at h6
    rw [hd.2] at h7
    have hT4 := hT3.step r4 (by decide) f4
    by_cases hlz : A.lay = 0
    · rw [if_pos (hl0.2 hlz)] at p4
      have hdec := decode_top_lookup v
      rw [← hlz] at hdec
      have hsd : WCT9.producerDecode A.lay v = if T3.topCredit v < 8 then none else T3.decode A.lay v := by
        rw [hlz]; exact producerDecode_top v
      rw [hsd]
      obtain ⟨t5, s5, p5, r5, f5⟩ := cs263_spec hK t4 p4 v h7
      have hT5 := hT4.step r5 (by decide) f5
      by_cases hr : v.toNat < 2 ^ 125
      · rw [if_pos hr] at p5
        obtain ⟨t6, s6, p6, h25', h30', r6, f6⟩ := topCheck_spec hK t5 v hr p5
          (by rw [r5.get (by decide), h6]) (by rw [r5.get (by decide), h7])
          (by rw [hT5.reg (by decide), hpre.x17, hlz]; rfl) (hT5.table hpre.table).sum
        have hT6 := hT5.step r6 (by decide) f6
        by_cases hs : topLookupSum v = 129
        · rw [if_pos hs] at p6
          have hd' : T3.decode A.lay v = some (topDigits v) := by rw [hdec, if_pos ⟨hr, hs⟩]
          have hvalid := ((topLookupSum_eq_iff v).mp hs).1
          obtain ⟨t7, s7, p7, r7, f7⟩ := TopUnpack.jump_spec hK t6 p6
          have hT7 := hT6.step r7 (by decide) f7
          obtain ⟨t8, s8, p8, g20, r8, f8⟩ := Credit.credit_spec hK t7 p7 v hr hvalid (hT7.table hpre.table)
            (by rw [r7.get (by decide), r6.get (by decide), r5.get (by decide), h6])
            (by rw [r7.get (by decide), r6.get (by decide), r5.get (by decide), h7])
            (by rw [r7.get (by decide), h30'])
          have hT8 := hT7.step r8 (by decide) f8
          by_cases hc : T3.topCredit v < 8
          · rw [if_pos hc] at p8 s8
            rw [if_pos hc]
            refine (TBSim.steps ((((s4.trans s5).trans s6).trans s7).trans s8) (cs_next hK hT8 p8 hi ih')).mono ?_
              (fun _ _ h => h)
            simp only [csT, csOk, if_pos hlz]; omega
          · rw [if_neg hc] at p8 s8
            rw [if_neg hc, hd']
            refine (TBSim.steps ((((s4.trans s5).trans s6).trans s7).trans s8) (cs_top_success hK hpre hT8 p8 hi22 hlz v hr
              hvalid hd'
              (by rw [r8.get (by decide), r7.get (by decide), r6.get (by decide), r5.get (by decide), h6])
              (by rw [r8.get (by decide), r7.get (by decide), r6.get (by decide), r5.get (by decide), h7])
              (by rw [r8.get (by decide), r7.get (by decide), h30'])
              (by rw [r8.get (by decide), r7.get (by decide)]; simpa only [hs] using h25') (g20 hc))).mono ?_
              (fun _ _ h => h)
            simp only [csT, csOk, if_pos hlz]; omega
        · rw [if_neg hs] at p6
          have hd' : T3.decode A.lay v = none := by rw [hdec, if_neg (fun h => hs h.2)]
          rw [hd', ite_self]
          refine (TBSim.steps ((s4.trans s5).trans s6) (cs_next hK hT6 p6 hi ih')).mono ?_ (fun _ _ h => h)
          simp only [csT, csOk, if_pos hlz]; omega
      · rw [if_neg hr] at p5
        have hd' : T3.decode A.lay v = none := by rw [hdec, if_neg (fun h => hr h.1)]
        rw [hd', ite_self]
        refine (TBSim.steps (s4.trans s5) (cs_next hK hT5 p5 hi ih')).mono ?_ (fun _ _ h => h)
        simp only [csT, csOk, if_pos hlz]; omega
    · rw [if_neg (fun h => hlz (hl0.1 h))] at p4
      have hdec := decode_low A.lay hlz v
      obtain ⟨t5, s5, p5, r5, f5⟩ := cs130_spec hK t4 p4 v h7
      have hT5 := hT4.step r5 (by decide) f5
      by_cases hr : v.toNat < 2 ^ 126
      · rw [if_pos hr] at p5
        obtain ⟨t6, s6, p6, h25', h28', r6, f6⟩ := cs132_spec hK t5 p5 v (T3.target A.lay) (target_lt _)
          (by rw [r5.get (by decide), h6]) (by rw [r5.get (by decide), h7]) (by rw [r5.get (by decide), h25])
          (by rw [hT5.reg (by decide), hpre.x17])
        have hT6 := hT5.step r6 (by decide) f6
        by_cases hs : (lowDigits v).sum ≤ T3.target A.lay ∧ T3.target A.lay - (lowDigits v).sum < 8
        · rw [if_pos hs] at p6
          obtain ⟨t7, s7, p7, r7, f7⟩ := cs262_spec hK t6 p6
          have hT7 := hT6.step r7 (by decide) f7
          have hd' : T3.decode A.lay v = some (lowDigits v ++ [T3.target A.lay - (lowDigits v).sum]) := by
            rw [hdec, if_pos ⟨hr, hs⟩]
          have hpd := producerDecode_lower hlz v (T3.target A.lay - (lowDigits v).sum) hd' rfl
          rw [hpd]
          have hcs : T3.target A.lay - (lowDigits v).sum < 8 := hs.2
          have hx28 : t7.getReg .x28 = BitVec.ofNat 64 (T3.target A.lay - (lowDigits v).sum) := by
            rw [r7.get (by decide), h28']
            apply BitVec.eq_of_toNat_eq
            have hT := target_lt A.lay
            simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
            rw [Nat.mod_eq_of_lt (show T3.target A.lay < 2 ^ 64 by omega),
              Nat.mod_eq_of_lt (show (lowDigits v).sum < 2 ^ 64 by omega),
              show 2 ^ 64 - (lowDigits v).sum + T3.target A.lay = 2 ^ 64 + (T3.target A.lay - (lowDigits v).sum)
                by omega, Nat.add_mod_left]
          obtain ⟨k8, n8, t8, s8, n8le, p8, r8, f8⟩ := scan_spec hK t7 p7 A.lay.val A.lay.isLt
            (by rw [hT7.reg (by decide), hpre.x8]) v hr _ hcs hx28
            (by rw [r7.get (by decide), r6.get (by decide), r5.get (by decide), h6])
            (by rw [r7.get (by decide), r6.get (by decide), r5.get (by decide), h7])
          have hT8 := hT7.step r8 (by decide) f8
          by_cases hok : scanFloor A.lay.val ≤ scanCredit v (T3.target A.lay - (lowDigits v).sum)
          · rw [if_pos hok] at p8 ⊢
            refine (TBSim.steps ((((s4.trans s5).trans s6).trans s7).trans s8) (cs_success hK hpre hT8 p8 hi22 hlz v _ _
              hd' rfl hs.1
              (by rw [r8.get (by decide), r7.get (by decide), r6.get (by decide), r5.get (by decide), h6])
              (by rw [r8.get (by decide), r7.get (by decide), r6.get (by decide), r5.get (by decide), h7])
              (by rw [r8.get (by decide), r7.get (by decide), h25']))).mono ?_ (fun _ _ h => h)
            simp only [csT, csOk, if_neg hlz]; omega
          · rw [if_neg hok] at p8 ⊢
            refine (TBSim.steps ((((s4.trans s5).trans s6).trans s7).trans s8) (cs_next hK hT8 p8 hi ih')).mono ?_
              (fun _ _ h => h)
            simp only [csT, csOk, if_neg hlz]; omega
        · rw [if_neg hs] at p6
          have hd' : T3.decode A.lay v = none := by rw [hdec, if_neg (fun h => hs h.2)]
          have hpd : WCT9.producerDecode A.lay v = none := by unfold WCT9.producerDecode; rw [hd']
          rw [hpd]
          refine (TBSim.steps ((s4.trans s5).trans s6) (cs_next hK hT6 p6 hi ih')).mono ?_ (fun _ _ h => h)
          simp only [csT, csOk, if_neg hlz]; omega
      · rw [if_neg hr] at p5
        have hd' : T3.decode A.lay v = none := by rw [hdec, if_neg (fun h => hr h.1)]
        have hpd : WCT9.producerDecode A.lay v = none := by unfold WCT9.producerDecode; rw [hd']
        rw [hpd]
        refine (TBSim.steps (s4.trans s5) (cs_next hK hT5 p5 hi ih')).mono ?_ (fun _ _ h => h)
        simp only [csT, csOk, if_neg hlz]; omega
theorem counterSearch_tbsim {A : CsArgs} {s0 : MachineState} (hK : KernAt image b) (hpre : CsPre b A s0) :
    TBSim image sk s0 (11 + capLimit A.lay.val * csT A.lay + csOk A.lay)
      (WCT9.layerCounterSearch A.lay A.tree A.leaf A.msg 0 (WCT9.searchLimit A.lay)) (CsPost image b A s0) := by
  obtain ⟨t, st, pt, h16, h24, h19, rt, ft⟩ := cs103_spec hK s0 hpre.pc A.lay.val A.tree A.leaf A.lay.isLt
    hpre.htree hpre.hleaf hpre.x8 hpre.x9 hpre.x18
  obtain ⟨t', st', pt', rt', ft'⟩ := cs113_spec hK t pt
  have hI : CsInv b A s0 0 t' := by
    refine ⟨pt', Nat.zero_le _, by rw [rt'.get (by decide), h19], by rw [ft'.get (by simp only [ENC]; omega) (by simp), h16],
      by rw [ft'.get (by simp only [ENC]; omega) (by simp), h24], ?_,
      (rt.trans rt').mono (by decide), (ft.trans ft').mono (fun A _ h => by
        rcases h with h | h
        · rcases h with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        · exact absurd h id)⟩
    obtain ⟨x, hx, hx32⟩ := hpre.c32
    exact ⟨x, hx, by rw [ft'.get (by simp only [ENC]; omega) (by simp), ft.get (by simp only [ENC]; omega)
      (by simp only [ENC]; omega), hx32]⟩
  rw [← capLimit_eq]
  have := TBSim.steps st (TBSim.steps st' (cs_loop (sk := sk) hK hpre (capLimit A.lay.val) 0 t' (by omega) hI))
  exact this.mono (le_of_eq (by ring)) (fun _ _ h => h)
end trial
structure FailedAt (b : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf (b + 2)
  x5 : t.getReg .x5 = 1
  x10 : t.getReg .x10 = 1
structure CsPreS (b : Nat) (s : MachineState) (lay : Layer) (tree leaf : Nat) (message : WCT9.LayerMsg) (ret : Nat) :
    Prop where
  pc : s.pc = pcOf (b + 103)
  x1 : s.getReg .x1 = pcOf ret
  x5 : s.getReg .x5 = 0
  x8 : s.getReg .x8 = BitVec.ofNat 64 lay.val
  x9 : s.getReg .x9 = BitVec.ofNat 64 tree
  x18 : s.getReg .x18 = BitVec.ofNat 64 leaf
  x17 : s.getReg .x17 = BitVec.ofNat 64 (T3.target lay)
  x26 : s.getReg .x26 = BitVec.ofNat 64 (T3.chainCount lay)
  x27 : s.getReg .x27 = BitVec.ofNat 64 (csN4 lay)
  htree : tree < 2 ^ 32
  hleaf : leaf < 2 ^ 32
  msg : DigAt s ENC (left message)
  c32 : (s.getMem (BitVec.ofNat 64 (ENC + 32))).toNat < 2 ^ 32
  z40 : s.getMem (BitVec.ofNat 64 (ENC + 40)) = 0
  r48 : s.getMem (BitVec.ofNat 64 (ENC + 48)) = (right message).extractLsb' 0 64
  r56 : s.getMem (BitVec.ofNat 64 (ENC + 56)) = (right message).extractLsb' 64 64
  table : TableOK s
  cf : CfTableOK (cfFlag b) s
def DummyOutS (s : MachineState) (ret : Nat) (t : MachineState) : Prop :=
  t.pc = pcOf ret ∧ t.getReg .x5 = 0 ∧
    (∀ j < 54, t.getByte (BitVec.ofNat 64 (DIGITS + j)) = BitVec.ofNat 8 (T3.dummyTop.getD j 0)) ∧
    (t.getMem (BitVec.ofNat 64 (ENC + 32))).toNat < 2 ^ 32 ∧ RegsExcept s t csRegs ∧ Frame s t CsW ∧
    (t.getReg .x25).toNat ≤ 129
def CsPostS (b : Nat) (s : MachineState) (lay : Layer) (ret : Nat) :
    Option (BitVec 32 × List Nat) → MachineState → Prop
  | none, t => if lay = 0 ∧ b = 543 then DummyOutS s ret t else FailedAt b t
  | some (_, ds), t => t.pc = pcOf ret ∧ t.getReg .x5 = 0 ∧ (∃ v, T3.decode lay v = some ds) ∧
      (∀ i < T3.chainCount lay, t.getByte (BitVec.ofNat 64 (DIGITS + i)) = BitVec.ofNat 8 (ds.getD i 0)) ∧
      (t.getMem (BitVec.ofNat 64 (ENC + 32))).toNat < 2 ^ 32 ∧ RegsExcept s t csRegs ∧ Frame s t CsW ∧
      (t.getReg .x25).toNat ≤ T3.target lay
def csCostS (lay : Layer) : Nat := (if lay = 0 then T3.counterLimit * 416 else WCT9.lowerSearchLimit * 200) + 2000
theorem CsPreS.toCsPre {b : Nat} {s : MachineState} {lay : Layer} {tree leaf : Nat} {msg : WCT9.LayerMsg} {ret : Nat}
    (h : CsPreS b s lay tree leaf msg ret) : CsPre b ⟨lay, tree, leaf, msg, ret⟩ s :=
  ⟨h.pc, h.x1, h.x5, h.x8, h.x9, h.x18, h.x17, h.x26, h.x27, h.htree, h.hleaf, h.msg.1, h.msg.2,
    ⟨_, h.c32, (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _)|>.symm⟩, h.z40, h.r48, h.r56, h.table, h.cf⟩
theorem counterSearch_spec {image : Image} {b : Nat} {sk : BitVec 256} (hK : KernAt image b)
    (s : MachineState) (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (ret : Nat)
    (h : CsPreS b s lay tree leaf msg ret) :
    TBSim image sk s (csCostS lay) (WCT9.layerCounterSearch lay tree leaf msg 0 (WCT9.searchLimit lay))
      (CsPostS b s lay ret) := by
  refine (counterSearch_tbsim (sk := sk) hK h.toCsPre).mono ?_ (fun r t ht => ?_)
  · show 11 + capLimit lay.val * csT lay + csOk lay ≤
      (if lay = 0 then T3.counterLimit * 416 else WCT9.lowerSearchLimit * 200) + 2000
    have hl0 : (lay.val = 0) ↔ lay = 0 := ⟨fun h => Fin.ext h, fun h => by rw [h]; rfl⟩
    unfold capLimit csT csOk T3.counterLimit WCT9.lowerSearchLimit
    by_cases h : lay = 0
    · rw [if_pos (hl0.2 h), if_pos h, if_pos h, if_pos h]; norm_num
    · rw [if_neg (fun h' => h (hl0.1 h')), if_neg h, if_neg h, if_neg h]; norm_num
  · rcases r with _ | ⟨c, ds⟩
    · change (if lay = 0 ∧ b = 543 then DummyOut _ s t else _) at ht
      show (if lay = 0 ∧ b = 543 then DummyOutS s ret t else FailedAt b t)
      split_ifs at ht ⊢ with hd
      · obtain ⟨tpc, dig, c32, hr, hf, h25⟩ := ht
        exact ⟨tpc, by rw [hr.get (by decide), h.x5], dig, c32, hr, hf, h25⟩
      · exact ⟨ht.1, ht.2.1, ht.2.2.1⟩
    · obtain ⟨tpc, hc, _, h32, hdec, _, hdig, hr, hf, h25⟩ := ht
      refine ⟨tpc, ?_, hdec, hdig, ?_, hr, hf, h25⟩
      · rw [hr.get (by decide), h.x5]
      · rw [h32, BitVec.toNat_ofNat]
        omega
end SigGolfCandidate.T3M.Search.BC
end
