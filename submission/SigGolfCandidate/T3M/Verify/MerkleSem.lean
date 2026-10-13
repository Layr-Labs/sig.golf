import SigGolfCandidate.T3M.Verify.MerklePlan
import SigGolfCandidate.T3M.Verify.LayerLower
import SigGolfCandidate.T3M.Verify.Arith

/-! Campaign S1 Merkle path semantics.

The node computed by fold `k - 1` (the leaf hash for `k = 0`) is the input of window `k`; a left node (bit `k` of the
leaf is 0) is the HIGH half of its answer, written 16 bytes below its slot (`mkWa`), a right node the low half,
written at its slot. Labels are one word (`t3 + heap - 1` / `heap`), bytes 24..48 of every window stay witness
(`wmerkleHigh`, `wmerklePad`). The window plans are bit dependent (top: two lines, lower: plan slots); the per-plan
facts (bounds, garbage halves never hit a sibling/pad still needed) are checked by `decide`. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

section
set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount pad64 shortHash leafHash header projHash
  projHalf nodeHigh leafHigh)
theorem mkSpec_run {allow : List Nat} {rel : List Reg} {gk known post : List (Reg × Word)}
    {stops : List Nat} {n : Nat} {dirs : List Dir} {sp : Spec} {obl : List Oblig} {keep : List Reg}
    (h : mkSpecB allow rel gk known stops n dirs sp obl post keep = true)
    (s : MachineState) (hpc : s.pc = pcOf n) (hk : KnownOK known s)
    (hbr : ∀ b ∈ sp.brs, b.holds s) (hob : ∀ o ∈ obl, o.holds s) :
    ∃ t, SpecRes allow rel gk sp post keep s t := by
  obtain ⟨t, ht⟩ := spec_run h s hpc hk hbr hob
  refine ⟨t, { ht with known := ?_, keep := ?_ }⟩
  · intro p hp
    exact ht.known p (List.mem_append_left _ hp)
  · intro r hr
    by_cases he : ∃ p ∈ known, p.1 = r
    · obtain ⟨p, hp, er⟩ := he
      have hpk : p ∈ mkKnownKeep known keep := by simp [mkKnownKeep, hp, er, hr]
      have ht' := ht.known p (List.mem_append_right _ hpk)
      rw [← er]
      exact ht'.trans (hk p hp).symm
    · have hany : known.any (fun p => p.1 == r) = false := by
        apply Bool.eq_false_iff.mpr
        intro h
        obtain ⟨p, hp, hpr⟩ := List.any_eq_true.mp h
        exact he ⟨p, hp, by simpa using hpr⟩
      exact ht.keep r (by simp [mkUnknownKeep, hr, hany])
/-- One S1 fold of the padded verifier's Merkle path (`layerPairP` / `topFinishP`). -/
def mkStep (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (value : Digest) (j : Nat) : T3.M Digest :=
  let other := ClaudeWCT.W9.T3M.wpath w lay (route index lay).1 j
  let pair := if (route index lay).1 / 2 ^ j % 2 = 0 then (value, other) else (other, value)
  ClaudeWCT.W9.T3M.nodeHashPH lay.val (route index lay).2 (2 ^ (height lay - j - 1) + (route index lay).1 / 2 ^ (j + 1))
    pair.1 (ClaudeWCT.W9.T3M.wmerkleHigh w lay (route index lay).1 j) (ClaudeWCT.W9.T3M.wmerklePad w lay (route index lay).1 j)
    pair.2
theorem mkFinRange_map_val (n : Nat) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp
theorem merkleP_eq (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (value : Digest) :
    merkleP w index lay value = (List.range (height lay)).foldlM (mkStep w index lay) value := by
  rw [← mkFinRange_map_val, List.foldlM_map]
  rfl
def mkIn (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (value : Digest) (j : Nat) : List UInt8 :=
  let other := ClaudeWCT.W9.T3M.wpath w lay (route index lay).1 j
  let pair := if (route index lay).1 / 2 ^ j % 2 = 0 then (value, other) else (other, value)
  SecurityInputs.nodeInputPH 3 lay.val (route index lay).2 (2 ^ (height lay - j - 1) + (route index lay).1 / 2 ^ (j + 1))
    pair.1 (ClaudeWCT.W9.T3M.wmerkleHigh w lay (route index lay).1 j) (ClaudeWCT.W9.T3M.wmerklePad w lay (route index lay).1 j)
    pair.2
theorem mkStep_eq (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (value : Digest) (j : Nat) :
    mkStep w index lay value j =
      projHash (nodeHigh 3 lay.val (2 ^ (height lay - j - 1) + (route index lay).1 / 2 ^ (j + 1)))
        (mkIn w index lay value j) := rfl
theorem mkIn_blk4 (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (value : Digest) (j : Nat) :
    mkIn w index lay value j =
      let other := ClaudeWCT.W9.T3M.wpath w lay (route index lay).1 j
      let pair := if (route index lay).1 / 2 ^ j % 2 = 0 then (value, other) else (other, value)
      blk4 pair.1 (SecurityInputs.withHigh (T3.nodeTweak 3 lay.val (route index lay).2
        (2 ^ (height lay - j - 1) + (route index lay).1 / 2 ^ (j + 1))) (ClaudeWCT.W9.T3M.wmerkleHigh w lay (route index lay).1 j))
        (ClaudeWCT.W9.T3M.wmerklePad w lay (route index lay).1 j) pair.2 := rfl
theorem mkIn_length (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (value : Digest) (j : Nat) :
    (mkIn w index lay value j).length = 64 := by rw [mkIn_blk4]; exact blk4_length _ _ _ _
theorem mkIn_blocks (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (value : Digest) (j : Nat) :
    (toQ (pad64 (mkIn w index lay value j))).blocks = 1 := by rw [mkIn_blk4]; exact blocks_blk4 _ _ _ _
/-- The pc of the ecall that ends the block before level `k` (the entry ecall for `k = 0`, the stub/second-half entry
for top level 6). -/
def mkEc (lay leaf k : Nat) : Nat :=
  BC.mkShp lay (mkCi lay k) (mkSh lay (mkCi lay k) leaf) +
    mkOff lay (mkCi lay k) (mkSh lay (mkCi lay k) leaf) (k - mkLo lay (mkCi lay k)) + 1
/-- The pc of the top path's last fold ecall (level 11); the compare tail follows. -/
def mkFin (lay leaf : Nat) : Nat :=
  BC.mkShp lay (mkNch lay - 1) (mkSh lay (mkNch lay - 1) leaf) +
    mkOff lay (mkNch lay - 1) (mkSh lay (mkNch lay - 1) leaf) (mkBits lay (mkNch lay - 1)) + 1
/-- Steps from the start of level `k`'s block to its fold ecall (dispatch level 5 of the top: + stub `j` + entry). -/
def mkLvlSt (lay leaf k : Nat) : Nat :=
  if lay = 0 ∧ k = 5 then mkWords 0 0 (mkSh 0 0 leaf) 5 + 2
  else mkBody lay (mkCi lay k) (mkSh lay (mkCi lay k) leaf) (k - mkLo lay (mkCi lay k))
theorem mk_facts (lay k : Nat) (hlay : lay < 4) (hk : k < hL lay) :
    mkCi lay k < mkNch lay ∧ mkLo lay (mkCi lay k) ≤ k ∧ k - mkLo lay (mkCi lay k) < mkBits lay (mkCi lay k) ∧
    mkIsDisp lay (mkCi lay k) (k - mkLo lay (mkCi lay k)) = decide (lay = 0 ∧ k = 5) ∧
    (k + 1 < hL lay → ¬ (lay = 0 ∧ k = 5) → mkCi lay (k + 1) = mkCi lay k ∧
      k + 1 - mkLo lay (mkCi lay k) = k - mkLo lay (mkCi lay k) + 1 ∧
      k - mkLo lay (mkCi lay k) + 1 < mkBits lay (mkCi lay k)) ∧
    (k + 1 = hL lay → mkCi lay k = mkNch lay - 1 ∧ ¬ (k - mkLo lay (mkCi lay k) + 1 < mkBits lay (mkCi lay k)) ∧
      k - mkLo lay (mkCi lay k) + 1 = mkBits lay (mkCi lay k)) := by
  interval_cases lay
  · change k < 12 at hk; interval_cases k <;> decide +kernel
  · change k < 7 at hk; interval_cases k <;> decide +kernel
  · change k < 6 at hk; interval_cases k <;> decide +kernel
  · change k < 6 at hk; interval_cases k <;> decide +kernel
theorem mk_disp_facts : mkCi 0 5 = 0 ∧ mkLo 0 0 = 0 ∧ mkCi 0 6 = 1 ∧ mkLo 0 1 = 6 ∧ mkBits 0 0 = 6 ∧ mkBits 0 1 = 6 ∧
    mkNch 0 = 2 := by decide +kernel
theorem mkBase_eq (lay : Layer) : mkBase lay.val = ClaudeWCT.W9.T3M.layerBase lay := by fin_cases lay <;> rfl
theorem mkPS_eq (lay : Layer) : mkPS lay.val = ClaudeWCT.W9.T3M.pathSlots lay := by fin_cases lay <;> rfl
theorem mkBo_eq (lay : Layer) (leaf k : Nat) (hleaf : leaf < 2 ^ hL lay.val) :
    mkBo lay.val leaf k = ClaudeWCT.W9.T3M.merkleBlock lay leaf k := by
  unfold ClaudeWCT.W9.T3M.merkleBlock ClaudeWCT.W9.T3M.pathOff
  rw [← mkBase_eq]
  by_cases h0 : lay.val = 0
  · rw [if_pos h0, h0, mkBo_top]; simp only [mkBase, List.getD_cons_zero]
  · rw [if_neg h0, mkBo_low _ _ _ h0]
    congr 2
    unfold plan ClaudeWCT.W9.T3M.lowerPlan
    fin_cases lay
    · exact absurd rfl h0
    · simp only [hL, List.getD_cons_succ, List.getD_cons_zero] at hleaf
      simp [Nat.mod_eq_of_lt (show leaf < 128 by simpa using hleaf), planL1, ClaudeWCT.W9.T3M.lowerPlanL1]
    · simp only [hL, List.getD_cons_succ, List.getD_cons_zero] at hleaf
      simp [Nat.mod_eq_of_lt (show leaf < 64 by simpa using hleaf), planL32, ClaudeWCT.W9.T3M.lowerPlanL32]
    · simp only [hL, List.getD_cons_succ, List.getD_cons_zero] at hleaf
      simp [Nat.mod_eq_of_lt (show leaf < 64 by simpa using hleaf), planL32, ClaudeWCT.W9.T3M.lowerPlanL32]
theorem mkCi_ok (lay k : Nat) : lay = 0 ∨ mkCi lay k = 0 := by
  by_cases h : lay = 0
  · exact Or.inl h
  · exact Or.inr (by simp [mkCi, h])
theorem mkSh_low (lay leaf : Nat) (h0 : lay ≠ 0) (hleaf : leaf < 2 ^ hL lay) : mkSh lay 0 leaf = leaf := by
  simp only [mkSh, mkLo, mkBits, h0, false_and, if_false, Nat.pow_zero, Nat.div_one]
  exact Nat.mod_eq_of_lt hleaf
/-- The block of level `k` is checked for the chunk's representative leaf: same window, same bit. -/
theorem mk_lift (lay leaf k : Nat) (hlay : lay < 4) (hleaf : leaf < 2 ^ hL lay) (hk : k < hL lay) :
    mkBo lay (mkLeafOf lay (mkCi lay k) (mkSh lay (mkCi lay k) leaf)) k = mkBo lay leaf k ∧
      mkBit (mkLeafOf lay (mkCi lay k) (mkSh lay (mkCi lay k) leaf)) k = mkBit leaf k := by
  obtain ⟨hci, hlo, hkk, -⟩ := mk_facts lay k hlay hk
  exact ⟨mkLeafOf_bo _ _ _ _ hlay hleaf hci hlo hkk, mkLeafOf_bit _ _ _ _ hlo hkk⟩
theorem mkBlk_lift (lay leaf k : Nat) (hlay : lay < 4) (hleaf : leaf < 2 ^ hL lay) (hk : k < hL lay) :
    mkBlk lay (mkLeafOf lay (mkCi lay k) (mkSh lay (mkCi lay k) leaf)) k = mkBlk lay leaf k := by
  unfold mkBlk; rw [(mk_lift lay leaf k hlay hleaf hk).1]
theorem mkWa_lift (lay leaf k : Nat) (hlay : lay < 4) (hleaf : leaf < 2 ^ hL lay) (hk : k < hL lay) :
    mkWa lay (mkLeafOf lay (mkCi lay k) (mkSh lay (mkCi lay k) leaf)) k = mkWa lay leaf k := by
  unfold mkWa mkBlk; rw [(mk_lift lay leaf k hlay hleaf hk).1, (mk_lift lay leaf k hlay hleaf hk).2]
theorem mkBo_facts (lay leaf k : Nat) (hlay : lay < 4) (hleaf : leaf < 2 ^ hL lay) (hk : k < hL lay) :
    mkBo lay leaf k % 16 = 0 ∧ 8256 ≤ mkBo lay leaf k ∧ mkBo lay leaf k + 80 ≤ 19100 ∧ mkBase lay ≤ mkBo lay leaf k ∧
      mkBo lay leaf k + 64 ≤ mkBase lay + 16 * mkPS lay := by
  obtain ⟨hR1, -, -, -⟩ := route_facts lay leaf hlay hleaf
  obtain ⟨p16, p64⟩ := hR1 k hk
  have hb := mkBase_ge lay hlay
  have ht : mkBase lay + 16 * mkPS lay ≤ 19008 := by interval_cases lay <;> decide +kernel
  unfold mkBo
  omega
theorem mkWa_wo (lay leaf l : Nat) (h : 16 ≤ mkBo lay leaf l) : mkWa lay leaf l = WIT + mkWo lay leaf l := by
  unfold mkWa mkWo mkBlk WIT; omega
/-! ### Witness words still needed -/
/-- Witness offsets still original before the fold of window `k`: everything below the layer (later layers) and the
words of the windows `≥ k` (`mkNeedW`). -/
def mkP (lay leaf k o : Nat) : Prop :=
  (8256 ≤ o ∧ o < mkBase lay) ∨ ∃ j, k ≤ j ∧ j < hL lay ∧ o ∈ mkNeedW lay leaf j
theorem mkP_need {lay leaf k j o : Nat} (hkj : k ≤ j) (hj : j < hL lay) (ho : o ∈ mkNeedW lay leaf j) :
    mkP lay leaf k o := Or.inr ⟨j, hkj, hj, ho⟩
theorem mkP_rd (lay leaf k : Nat) (hk : k < hL lay) :
    mkP lay leaf k (mkSibO lay leaf k) ∧ mkP lay leaf k (mkSibO lay leaf k + 8) ∧ mkP lay leaf k (mkBo lay leaf k + 24) ∧
      mkP lay leaf k (mkBo lay leaf k + 32) ∧ mkP lay leaf k (mkBo lay leaf k + 40) :=
  ⟨mkP_need le_rfl hk (by simp [mkNeedW]), mkP_need le_rfl hk (by simp [mkNeedW]),
    mkP_need le_rfl hk (by simp [mkNeedW]), mkP_need le_rfl hk (by simp [mkNeedW]),
    mkP_need le_rfl hk (by simp [mkNeedW])⟩
theorem mkBase_zero_out (o : Nat) (h : 8256 ≤ o ∧ o < mkBase 0) : False := by
  have : mkBase 0 = 8256 := rfl
  omega
theorem mkP_step (lay leaf k : Nat) (hlay : lay < 4) (hleaf : leaf < 2 ^ hL lay) (hk1 : k + 1 < hL lay) (o : Nat)
    (h8 : o % 8 = 0) (ho : mkP lay leaf (k + 1) o) :
    (mkP lay leaf k o ∧ o ≠ mkBo lay leaf k + 16) ∧
      (WIT + o + 8 ≤ mkWa lay leaf (k + 1) ∨ mkWa lay leaf (k + 1) + 32 ≤ WIT + o) := by
  obtain ⟨-, hR2, -, hR4⟩ := route_facts lay leaf hlay hleaf
  obtain ⟨-, hBlo, -, hBase, -⟩ := mkBo_facts lay leaf (k + 1) hlay hleaf hk1
  obtain ⟨-, -, -, hBase0, -⟩ := mkBo_facts lay leaf k hlay hleaf (by omega)
  have hg := mkBase_ge lay hlay
  rw [mkWa_wo _ _ _ (by omega)]
  rcases ho with ho | ⟨j, hj1, hj2, hoj⟩
  · have h0 : lay ≠ 0 := by rintro rfl; exact mkBase_zero_out o ho
    have := hR2 h0 (k + 1) hk1
    exact ⟨⟨Or.inl ho, by omega⟩, Or.inl (by unfold WIT; omega)⟩
  · obtain ⟨hn, hd⟩ := hR4 k j (by omega) hj2 o hoj
    simp only [mkDis, decide_eq_true_eq] at hd
    exact ⟨⟨mkP_need (by omega) hj2 hoj, hn⟩, by unfold WIT; omega⟩
theorem mkNeedW_range (lay leaf j o : Nat) (ho : o ∈ mkNeedW lay leaf j) :
    mkBo lay leaf j + 16 < o ∧ o + 8 ≤ mkBo lay leaf j + 64 ∨
      mkBo lay leaf j ≤ o ∧ o + 8 ≤ mkBo lay leaf j + 16 ∧ mkBit leaf j = 1 := by
  have hb := mkBit_lt' leaf j
  simp only [mkNeedW, mkSibO, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with h | h | h | h | h <;> subst h <;> omega
theorem mkP_leaf (lay leaf : Nat) (hlay : lay < 4) (hleaf : leaf < 2 ^ hL lay) (o : Nat) (h8 : o % 8 = 0)
    (ho : mkP lay leaf 0 o) :
    (8256 ≤ o ∧ o < mkBase lay + 16 * mkPS lay) ∧
      (WIT + o + 8 ≤ mkWa lay leaf 0 ∨ mkWa lay leaf 0 + 32 ≤ WIT + o) := by
  have hhL : 0 < hL lay := by interval_cases lay <;> decide +kernel
  obtain ⟨-, hR2, hR3, -⟩ := route_facts lay leaf hlay hleaf
  obtain ⟨-, hBlo, -, hBase, -⟩ := mkBo_facts lay leaf 0 hlay hleaf hhL
  have hg := mkBase_ge lay hlay
  have hps : 4 ≤ mkPS lay := by interval_cases lay <;> decide +kernel
  rw [mkWa_wo _ _ _ (by omega)]
  rcases ho with ho | ⟨j, -, hj2, hoj⟩
  · have h0 : lay ≠ 0 := by rintro rfl; exact mkBase_zero_out o ho
    have := hR2 h0 0 hhL
    exact ⟨⟨ho.1, by omega⟩, Or.inl (by unfold WIT; omega)⟩
  · have hd := hR3 j hj2 o hoj
    simp only [mkDis, decide_eq_true_eq] at hd
    obtain ⟨-, hBloj, -, hBasej, hTopj⟩ := mkBo_facts lay leaf j hlay hleaf hj2
    have hr := mkNeedW_range lay leaf j o hoj
    exact ⟨⟨by omega, by omega⟩, by unfold WIT; omega⟩
theorem Verify.Orig.mono8 {w : ClaudeWCT.W9.T3M.WBytes} {s : MachineState} {P P' : Nat → Prop} (h : Orig w P s)
    (hP : ∀ o, o % 8 = 0 → P' o → P o) : Orig w P' s :=
  fun j h1 h2 => h j h1 (hP _ (Nat.mul_mod_right 8 j) h2)
/-! ### Machine states between the folds -/
def mkStop (lay : Nat) : Nat := hL lay - (if lay = 0 then 0 else 1)
/-- Heap of the node computed by the fold of window `k`. -/
def mkHeapN (lay leaf k : Nat) : Nat := 2 ^ (hL lay - k - 1) + leaf / 2 ^ (k + 1)
structure MAfter (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (lay leaf : Nat) (u : MachineState) (k : Nat) (v : Digest)
    (s : MachineState) : Prop where
  pc : s.pc = pcOf (mkEc lay leaf k + 1)
  glob : Glob baseK w pk s
  known : KnownOK (mkLvlK lay k) s
  keep : ∀ r ∈ mkKeep, s.getReg r = u.getReg r
  node : DigAt s (mkCur lay leaf k) v
  orig : Orig w (mkP lay leaf k) s
  dstReg : s.getReg .x12 = BitVec.ofNat 64 (mkWa lay leaf k)
  x28 : k ≠ 0 → lay ≠ 0 → s.getReg .x28 = T3.hyperWord (lay - 1) (u.getReg .x31).toNat
  x8 : lay = 1 → mkS0 lay leaf < k → s.getReg .x8 = BitVec.ofNat 64 s3v
  bufferOrig : lay ≠ 0 → Orig w (fun o => BC.bufferStart (lay-1) ≤ o ∧ o < 24880) s
structure MkEnd (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (lay leaf : Nat) (u : MachineState) (root : Digest)
    (t : MachineState) : Prop where
  pc : t.pc = pcOf (mkFin lay leaf + 1)
  glob : Glob baseK w pk t
  known : KnownOK (mkKc lay ++ [(.x11, 64)]) t
  keep : ∀ r ∈ mkKeep, t.getReg r = u.getReg r
  root : DigAt t (mkDst lay leaf) root
  orig : Orig w (fun o => 8256 ≤ o ∧ o < mkBase lay) t
  dstReg : t.getReg .x12 = BitVec.ofNat 64 (mkDst lay leaf)
  x10 : t.getReg .x10 = BitVec.ofNat 64 (mkBlk lay leaf (hL lay - 1))
def mkHashInputOf (a b : Word) (f : Word → BitVec 8) : Query :=
  ⟨b.toNat / 64 - 1, BitVec.ofNat (8 * (64 * (b.toNat / 64 - 1 + 1))) ((List.range (64 * (b.toNat / 64 - 1 + 1))).foldl
    (fun acc i => acc + (f (a + BitVec.ofNat 64 i)).toNat * 2 ^ (8 * i)) 0)⟩
theorem mkHashInput_eq_of (s : MachineState) : hashInput s = mkHashInputOf (s.getReg .x10) (s.getReg .x11) s.getByte := rfl
theorem mkHashInput_congr {s t : MachineState} (h10 : t.getReg .x10 = s.getReg .x10)
    (h11 : t.getReg .x11 = s.getReg .x11) (hm : ∀ A, t.getMem A = s.getMem A) : hashInput t = hashInput s := by
  have hb : t.getByte = s.getByte := funext fun a => by simp only [MachineState.getByte, hm]
  rw [mkHashInput_eq_of, mkHashInput_eq_of, h10, h11, hb]
theorem mkKeep_sub (l : List Reg) : ∀ r ∈ mkKeep, r ∈ mkKeep ++ l := fun r hr => List.mem_append_left _ hr
theorem mkKc_mkK (lay : Nat) : ∀ p ∈ mkKc lay, p ∈ mkK lay := by
  intro p hp; unfold mkK; unfold mkKc at hp; exact List.mem_append_left _ hp
theorem mkK_cases (lay : Nat) (p : Reg × Word) (hp : p ∈ mkK lay) :
    p ∈ mkKc lay ∨ p = (.x9, BitVec.ofNat 64 TOPB9) := by
  unfold mkK at hp; unfold mkKc
  rcases List.mem_append.mp hp with h | h
  · exact Or.inl h
  · right; split_ifs at h with h0 <;> simp_all
theorem lvlMem_read (lay ci sh l : Nat) (s : MachineState) (A : Nat) (hA : A < 2 ^ 64)
    (hB : mkBlk lay (mkLeafOf lay ci sh) l + 16 < 2 ^ 64) :
    memEval s (mkLvlMem lay ci sh l) (BitVec.ofNat 64 A) =
      if A = mkBlk lay (mkLeafOf lay ci sh) l + 16 then (mkLabelE lay ci sh l).eval s
      else s.getMem (BitVec.ofNat 64 A) := by
  unfold mkLvlMem
  rw [memEval_cons_ofNat _ _ _ _ _ hA hB, memEval_nil]
theorem mk_buffer_ge (lay o : Nat) (hlay : lay < 4)
    (ho : BC.bufferStart (lay-1) ≤ o ∧ o < 24880) : 21712 ≤ o := by
  interval_cases lay <;> simp [BC.bufferStart] at ho <;> omega
theorem mk_buffer_writeHash {w : ClaudeWCT.W9.T3M.WBytes} {s : MachineState}
    (lay : Nat) (hlay : lay < 4)
    (hO : Orig w (fun o => BC.bufferStart (lay-1) ≤ o ∧ o < 24880) s)
    (a : BitVec 256) (d : Nat) (h12 : s.getReg .x12 = BitVec.ofNat 64 d)
    (hd : d + 32 ≤ WIT + 21712) :
    Orig w (fun o => BC.bufferStart (lay-1) ≤ o ∧ o < 24880) (writeHash s a) := by
  apply (Orig_writeHash hO a d h12 (by unfold WIT at hd; omega)).mono
  intro o ho
  exact ⟨ho, Or.inr (by have := mk_buffer_ge lay o hlay ho; omega)⟩
theorem lvl_bufferOrig {w : ClaudeWCT.W9.T3M.WBytes} (lay : Nat) (hlay : lay < 4) (leaf k : Nat)
    (hleaf : leaf < 2 ^ hL lay) (hk : k < hL lay) (s t : MachineState)
    (hO : lay ≠ 0 → Orig w (fun o => BC.bufferStart (lay-1) ≤ o ∧ o < 24880) s)
    (hmem : ∀ A, t.getMem A = memEval s (mkLvlMem lay (mkCi lay k) (mkSh lay (mkCi lay k) leaf) k) A) :
    lay ≠ 0 → Orig w (fun o => BC.bufferStart (lay-1) ≤ o ∧ o < 24880) t := by
  intro h0
  apply (hO h0).frame
  intro j hj ho
  have hmin := mk_buffer_ge lay (8 * j) hlay ho
  obtain ⟨_, _, hhi, _, _⟩ := mkBo_facts lay leaf k hlay hleaf hk
  have he := mkBlk_lift lay leaf k hlay hleaf hk
  rw [hmem, lvlMem_read _ _ _ _ s (WIT + 8 * j) (by unfold WIT WX at *; omega) (by rw [he]; unfold mkBlk; omega), he]
  rw [if_neg (by unfold WIT mkBlk; omega)]
theorem t3E_eval (l' tree : Nat) (hl : l' < 4) (htr : tree < 2 ^ 32) (s : MachineState)
    (h31 : s.getReg .x31 = BitVec.ofNat 64 tree) (hD : DataOK s) :
    (t3E l').eval s = T3.hyperWord l' tree := by
  simp only [t3E, E.eval, BinOp.eval, kw, h31]
  rw [hdrA_eq l' hl, hD.header l' hl, ofNat_shl', show (16 : Nat) % 2 ^ 64 % 64 = 16 by norm_num, BitVec.or_comm]
  exact hyper_or l' tree hl htr
theorem mkHdrE_eval (lay l tree : Nat) (hlay : lay < 4) (h0 : lay ≠ 0) (htr : tree < 2 ^ 32) (s : MachineState)
    (h31 : l = 0 → s.getReg .x31 = BitVec.ofNat 64 tree) (hD : DataOK s)
    (h28 : l ≠ 0 → s.getReg .x28 = T3.hyperWord (lay - 1) tree) :
    (mkHdrE lay l).eval s = T3.hyperWord (lay - 1) tree := by
  unfold mkHdrE
  rw [if_neg h0]
  by_cases hl : l = 0
  · rw [if_pos hl]; exact t3E_eval _ _ (by omega) htr s (h31 hl) hD
  · rw [if_neg hl]; exact h28 hl
/-! ### Labels and projections -/
/-- The one-word label of a fold (the low word of `nodeTweak`). -/
def mkTw (lay tree heap : Nat) : Word :=
  if lay = 0 then BitVec.ofNat 64 (T3.topNodeWord heap) else T3.lowerNodeWord (lay - 1) tree heap
theorem nodeTweak_tw (lay tree heap : Nat) (hlay : lay < 4) :
    T3.nodeTweak 3 lay tree heap = 0#64 ++ mkTw lay tree heap := by
  unfold T3.nodeTweak mkTw; rw [if_pos ⟨rfl, hlay⟩]
theorem withHigh_tw (lay tree heap : Nat) (hlay : lay < 4) (hp : BitVec 64) :
    SecurityInputs.withHigh (T3.nodeTweak 3 lay tree heap) hp = hp ++ mkTw lay tree heap := by
  rw [nodeTweak_tw _ _ _ hlay]
  unfold SecurityInputs.withHigh
  rw [if_pos (by rw [BitVec.extractLsb'_append_eq_left]; rfl), BitVec.extractLsb'_append_eq_right]
theorem mkHeapN_lt (lay leaf k : Nat) (hleaf : leaf < 2 ^ hL lay) (hk : k < hL lay) :
    1 ≤ mkHeapN lay leaf k ∧ mkHeapN lay leaf k < 2 ^ (hL lay - k) := by
  unfold mkHeapN
  have e : 2 ^ hL lay = 2 ^ (k + 1) * 2 ^ (hL lay - k - 1) := by rw [← Nat.pow_add]; congr 1; omega
  have h1 : leaf / 2 ^ (k + 1) < 2 ^ (hL lay - k - 1) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), Nat.mul_comm, ← e]; exact hleaf
  have e2 : 2 ^ (hL lay - k) = 2 * 2 ^ (hL lay - k - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  have := Nat.two_pow_pos (hL lay - k - 1)
  rw [e2]
  generalize 2 ^ (hL lay - k - 1) = X at *
  generalize leaf / 2 ^ (k + 1) = Y at *
  omega
theorem mkHigh_eq (lay leaf k : Nat) (hlay : lay < 4) (hk : k + 1 < hL lay) :
    nodeHigh 3 lay (mkHeapN lay leaf k) = decide (mkBit leaf (k + 1) = 0) := by
  have h2 : 2 ≤ 2 ^ (hL lay - k - 1) := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
  have he : 2 ^ (hL lay - k - 1) % 2 = 0 := by
    rw [show hL lay - k - 1 = (hL lay - k - 2) + 1 by omega, Nat.pow_succ]; simp
  unfold T3.nodeHigh T3.leftHigh mkHeapN mkBit
  rw [if_neg (by omega : ¬ 4 ≤ lay)]
  have hm : (2 ^ (hL lay - k - 1) + leaf / 2 ^ (k + 1)) % 2 = leaf / 2 ^ (k + 1) % 2 := by
    generalize 2 ^ (hL lay - k - 1) = X at *
    generalize leaf / 2 ^ (k + 1) = Y at *
    omega
  have hge : decide (2 ≤ 2 ^ (hL lay - k - 1) + leaf / 2 ^ (k + 1)) = true :=
    decide_eq_true (Nat.le_add_right_of_le h2)
  rw [hm, hge]
  rcases Nat.mod_two_eq_zero_or_one (leaf / 2 ^ (k + 1)) with h | h <;> simp [h]
theorem mkHigh_root (leaf : Nat) (hleaf : leaf < 4096) : nodeHigh 3 0 (mkHeapN 0 leaf 11) = false := by
  have : mkHeapN 0 leaf 11 = 1 := by
    unfold mkHeapN; simp only [hL, List.getD_cons_zero]
    rw [Nat.div_eq_of_lt (by norm_num; omega)]
    try norm_num
  rw [this]; rfl
theorem mkPow_add_div (h k x : Nat) (hk : k < h) :
    (2 ^ h + x) / 2 ^ (k + 1) = 2 ^ (h - k - 1) + x / 2 ^ (k + 1) := by
  have : 2 ^ h = 2 ^ (k + 1) * 2 ^ (h - k - 1) := by rw [← Nat.pow_add]; congr 1; omega
  rw [this, Nat.mul_add_div (Nat.two_pow_pos _)]
theorem mkDiv64_mul_div (leaf k : Nat) (hk : 6 ≤ k) : leaf / 64 * 64 / 2 ^ (k + 1) = leaf / 2 ^ (k + 1) := by
  have e : 2 ^ (k + 1) = 64 * 2 ^ (k - 5) := by
    rw [show (64 : Nat) = 2 ^ 6 by rfl, ← Nat.pow_add]; congr 1; omega
  rw [e, Nat.mul_comm 64 (2 ^ (k - 5)), Nat.mul_div_mul_right _ _ (by decide +kernel : 0 < 64), Nat.div_div_eq_div_mul,
    Nat.mul_comm 64]
theorem mkHeap_eq (lay leaf k : Nat) (hlay : lay < 4) (hleaf : leaf < 2 ^ hL lay) (hk : k < hL lay)
    (hci : ¬ (lay = 0 ∧ mkCi lay k = 0)) :
    mkHeap lay (mkCi lay k) (mkSh lay (mkCi lay k) leaf) k = mkHeapN lay leaf k := by
  unfold mkHeap mkHeapN
  by_cases h0 : lay = 0
  · subst h0
    have hk6 : 6 ≤ k := by
      by_contra hk6; exact hci ⟨rfl, by simp [mkCi]; omega⟩
    have hci1 : mkCi 0 k = 1 := by simp [mkCi]; omega
    rw [hci1]
    have hl : leaf < 4096 := by simpa [hL] using hleaf
    have hsh : mkSh 0 1 leaf = leaf / 64 := by
      simp only [mkSh, mkLo, mkBits]; norm_num; omega
    rw [hsh, show mkLo 0 1 = 6 by rfl, show hL 0 = 12 by rfl, show (2 : Nat) ^ 6 = 64 by rfl,
      mkPow_add_div 12 k _ (by simpa [hL] using hk), mkDiv64_mul_div leaf k hk6]
  · have hci0 : mkCi lay k = 0 := by simp [mkCi, h0]
    rw [hci0, mkSh_low lay leaf h0 hleaf, show mkLo lay 0 = 0 by simp [mkLo], Nat.pow_zero, Nat.mul_one,
      mkPow_add_div _ k _ hk]
theorem mkLabel_eval (lay leaf tree k : Nat) (hlay : lay < 4) (hleaf : leaf < 2 ^ hL lay) (hk : k < hL lay)
    (s : MachineState) (h23 : lay = 0 → s.getReg .x23 = BitVec.ofNat 64 (dispatchHeap 0 leaf))
    (hhdr : lay ≠ 0 → (mkHdrE lay k).eval s = T3.hyperWord (lay - 1) tree) :
    (mkLabelE lay (mkCi lay k) (mkSh lay (mkCi lay k) leaf) k).eval s = mkTw lay tree (mkHeapN lay leaf k) := by
  obtain ⟨hh1, hh2⟩ := mkHeapN_lt lay leaf k hleaf hk
  unfold mkLabelE mkTw
  by_cases h0 : lay = 0
  · subst h0
    have hl : leaf < 4096 := hleaf
    have hk12 : k < 12 := hk
    have hlt : mkHeapN 0 leaf k < 4096 := by
      have h2 : 2 ^ (hL 0 - k) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) (by change 12 - k ≤ 12; omega)
      exact lt_of_lt_of_le hh2 h2
    rw [if_pos rfl, if_pos rfl, T3.topNodeWord_eq hh1 hlt]
    by_cases hc : mkCi 0 k = 0
    · rw [if_pos hc]
      have hk6 : k < 6 := by by_contra h; simp [mkCi] at hc; omega
      apply BitVec.eq_of_toNat_eq
      have hd : dispatchHeap 0 leaf = 16 * (2 ^ hL 0 + leaf) := by simp [dispatchHeap, s7Bias, hL]
      simp only [E.eval, BinOp.eval, kw, h23 rfl, hd]
      have hdiv : 16 * (2 ^ hL 0 + leaf) / 2 ^ (k + 5) = (2 ^ hL 0 + leaf) / 2 ^ (k + 1) := by
        rw [show (k + 5 : Nat) = 4 + (k + 1) by omega, Nat.pow_add, show (2 : Nat) ^ 4 = 16 by rfl,
          ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel_left _ (by decide : 0 < 16)]
      have hb : 16 * (2 ^ hL 0 + leaf) < 2 ^ 64 := by simp only [hL, List.getD_cons_zero]; omega
      rw [toNat_srl _ _ (by omega), BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb, hdiv,
        mkPow_add_div _ k _ hk]
      unfold mkHeapN
      exact (Nat.mod_eq_of_lt (by unfold mkHeapN at hlt; omega)).symm
    · rw [if_neg hc]
      simp only [E.eval, kw]
      rw [mkHeap_eq 0 leaf k (by decide) hleaf hk (by simp [hc])]
  · rw [if_neg h0, if_neg h0, addC_eval, hhdr h0, mkHeap_eq lay leaf k hlay hleaf hk (by simp [h0])]
    have h128 : mkHeapN lay leaf k < 128 :=
      lt_of_lt_of_le hh2 (by
        rw [show (128 : Nat) = 2 ^ 7 by rfl]
        exact Nat.pow_le_pow_right (by norm_num) (by interval_cases lay <;> simp [hL] <;> omega))
    rw [T3.lowerNodeWord_eq_add _ _ hh1 h128]
theorem mkTw_lo (lay tree heap : Nat) (hp : BitVec 64) : dlo (hp ++ mkTw lay tree heap) = mkTw lay tree heap :=
  BitVec.extractLsb'_append_eq_right
theorem mkTw_hi (lay tree heap : Nat) (hp : BitVec 64) : dhi (hp ++ mkTw lay tree heap) = hp :=
  BitVec.extractLsb'_append_eq_left
theorem wpath_eq (w : ClaudeWCT.W9.T3M.WBytes) (lay : Layer) (leaf j : Nat) (hleaf : leaf < 2 ^ hL lay.val) :
    ClaudeWCT.W9.T3M.wpath w lay leaf j = ClaudeWCT.W9.T3M.wdig w (mkSibO lay.val leaf j) := by
  unfold ClaudeWCT.W9.T3M.wpath mkSibO
  rw [← mkBo_eq lay leaf j hleaf]
  have hb := mkBit_lt leaf j
  unfold sibOff mkBit
  split <;> rename_i h <;> congr 1 <;> omega
theorem wpad_eq (w : ClaudeWCT.W9.T3M.WBytes) (lay : Layer) (leaf j : Nat) (hleaf : leaf < 2 ^ hL lay.val) :
    ClaudeWCT.W9.T3M.wmerklePad w lay leaf j = ClaudeWCT.W9.T3M.wdig w (mkBo lay.val leaf j + 32) := by
  unfold ClaudeWCT.W9.T3M.wmerklePad; rw [mkBo_eq lay leaf j hleaf]
theorem whigh_eq (w : ClaudeWCT.W9.T3M.WBytes) (lay : Layer) (leaf j : Nat) (hleaf : leaf < 2 ^ hL lay.val)
    (h8 : mkBo lay.val leaf j % 8 = 0) :
    ClaudeWCT.W9.T3M.wmerkleHigh w lay leaf j = wword w ((mkBo lay.val leaf j + 24) / 8) := by
  unfold ClaudeWCT.W9.T3M.wmerkleHigh wword
  rw [← mkBo_eq lay leaf j hleaf, wdig_hi]
  congr 1; omega
theorem mkNode_write (lay leaf l : Nat) (t : MachineState) (a : BitVec 256)
    (hB : 16 ≤ mkBo lay leaf l) (hB2 : mkBo lay leaf l + 80 ≤ 19100)
    (h12 : t.getReg .x12 = BitVec.ofNat 64 (mkWa lay leaf l)) :
    DigAt (writeHash t a) (mkCur lay leaf l) (projHalf (decide (mkBit leaf l = 0)) a) := by
  have hb := mkBit_lt' leaf l
  rcases (show mkBit leaf l = 0 ∨ mkBit leaf l = 1 by omega) with h | h
  · have e : mkCur lay leaf l = mkWa lay leaf l + 16 := by unfold mkCur mkWa mkBlk; rw [h]; omega
    rw [e, show decide (mkBit leaf l = 0) = true by simp [h], T3.projHalf_true]
    exact DigAt.writeHash_hi t a _ h12 (by unfold mkWa mkBlk; omega)
  · have e : mkCur lay leaf l = mkWa lay leaf l := by unfold mkCur mkWa mkBlk; rw [h]; omega
    rw [e, show decide (mkBit leaf l = 0) = false by simp [h], T3.projHalf_false]
    exact DigAt.writeHash_lo t a _ h12 (by unfold mkWa mkBlk; omega)
theorem mkWa_bounds (lay leaf l : Nat) (hlay : lay < 4) (hleaf : leaf < 2 ^ hL lay) (hl : l < hL lay) :
    mkWa lay leaf l % 8 = 0 ∧ mkWa lay leaf l + 32 ≤ 2 ^ 23 ∧ WLO ≤ mkWa lay leaf l := by
  obtain ⟨hB16, hBlo, hBhi, -, -⟩ := mkBo_facts lay leaf l hlay hleaf hl
  have hb := mkBit_lt' leaf l
  unfold mkWa mkBlk WLO WIT
  omega
theorem lvl_input (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer) (u : MachineState)
    (hidx : index < 2 ^ 31)
    (hs7 : lay.val = 0 → u.getReg .x23 = BitVec.ofNat 64 (dispatchHeap 0 (route index lay).1))
    (ht5 : lay.val ≠ 0 → u.getReg .x31 = BitVec.ofNat 64 (route index lay).2)
    (k : Nat) (hk : k < hL lay.val) (v : Digest) (s t : MachineState)
    (hs : MAfter w pk lay.val (route index lay).1 u k v s)
    (hmem : ∀ A, t.getMem A =
      memEval s (mkLvlMem lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1) k) A)
    (h10 : t.getReg .x10 = BitVec.ofNat 64 (mkBlk lay.val (route index lay).1 k))
    (h11 : t.getReg .x11 = BitVec.ofNat 64 64) :
    hashInput t = toQ (pad64 (mkIn w index lay v k)) ∧
      Orig w (fun o => mkP lay.val (route index lay).1 k o ∧ o ≠ mkBo lay.val (route index lay).1 k + 16) t := by
  have hlay := lay.isLt
  have hleaf : (route index lay).1 < 2 ^ hL lay.val := leaf_lt index lay
  have htree : (route index lay).2 < 2 ^ 32 := tree_lt index lay hidx
  obtain ⟨hB16, hBlo, hBhi, hBase, -⟩ := mkBo_facts lay.val (route index lay).1 k hlay hleaf hk
  have hb := mkBit_lt' (route index lay).1 k
  have hlift := mkBlk_lift lay.val (route index lay).1 k hlay hleaf hk
  have h23 : lay.val = 0 → s.getReg .x23 = BitVec.ofNat 64 (dispatchHeap 0 (route index lay).1) :=
    fun h => (hs.keep .x23 (by simp [mkKeep])).trans (hs7 h)
  have hlbl : (mkLabelE lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1) k).eval s =
      mkTw lay.val (route index lay).2 (mkHeapN lay.val (route index lay).1 k) := by
    apply mkLabel_eval _ _ _ k hlay hleaf hk s h23
    intro h0
    apply mkHdrE_eval _ _ _ hlay h0 htree s
    · intro _; exact (hs.keep .x31 (by simp [mkKeep])).trans (ht5 h0)
    · exact hs.glob.2.2.2.2.2
    · intro hk0
      rw [hs.x28 hk0 h0, ht5 h0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hrd : ∀ A, A < 2 ^ 64 → t.getMem (BitVec.ofNat 64 A) =
      if A = mkBlk lay.val (route index lay).1 k + 16 then
        mkTw lay.val (route index lay).2 (mkHeapN lay.val (route index lay).1 k)
      else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [hmem, lvlMem_read _ _ _ _ s A hA (by rw [hlift]; unfold mkBlk; omega), hlift, hlbl]
  have hfr : ∀ A, A < 2 ^ 64 → A ≠ mkBlk lay.val (route index lay).1 k + 16 →
      t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1; rw [hrd A hA, if_neg h1]
  have hO := hs.orig
  have hlen := mkIn_length w index lay v k
  obtain ⟨rs0, rs1, rh, rp0, rp1⟩ := mkP_rd lay.val (route index lay).1 k hk
  refine ⟨?_, ?_⟩
  · rw [pad64_of_aligned _ (by rw [hlen])]
    apply hashInput_words8 t _ (mkBlk lay.val (route index lay).1 k) hlen h10 (by unfold mkBlk; omega)
      (by unfold mkBlk; omega) h11
    have hpad := hO.dig (mkBo lay.val (route index lay).1 k + 32) (by omega) (by unfold WX; omega) rp0 rp1
    rw [show WIT + (mkBo lay.val (route index lay).1 k + 32) = mkBlk lay.val (route index lay).1 k + 32 by
        unfold WIT mkBlk; omega,
      show mkBlk lay.val (route index lay).1 k + 32 + 8 = mkBlk lay.val (route index lay).1 k + 40 by omega] at hpad
    have hhw := hO.word (mkBo lay.val (route index lay).1 k + 24) (by omega) (by unfold WX; omega) rh
    rw [show WIT + (mkBo lay.val (route index lay).1 k + 24) = mkBlk lay.val (route index lay).1 k + 24 by
      unfold WIT mkBlk; omega] at hhw
    have f24 := hfr (mkBlk lay.val (route index lay).1 k + 24) (by unfold mkBlk; omega) (by omega)
    have f32 := hfr (mkBlk lay.val (route index lay).1 k + 32) (by unfold mkBlk; omega) (by omega)
    have f40 := hfr (mkBlk lay.val (route index lay).1 k + 40) (by unfold mkBlk; omega) (by omega)
    have f0 := hfr (mkBlk lay.val (route index lay).1 k) (by unfold mkBlk; omega) (by omega)
    have f8 := hfr (mkBlk lay.val (route index lay).1 k + 8) (by unfold mkBlk; omega) (by omega)
    have f48 := hfr (mkBlk lay.val (route index lay).1 k + 48) (by unfold mkBlk; omega) (by omega)
    have f56 := hfr (mkBlk lay.val (route index lay).1 k + 56) (by unfold mkBlk; omega) (by omega)
    have hT0 : t.getMem (BitVec.ofNat 64 (mkBlk lay.val (route index lay).1 k + 16)) =
        mkTw lay.val (route index lay).2 (mkHeapN lay.val (route index lay).1 k) := by
      rw [hrd _ (by unfold mkBlk; omega), if_pos rfl]
    have hnode := hs.node
    have hheap : 2 ^ (height lay - k - 1) + (route index lay).1 / 2 ^ (k + 1) = mkHeapN lay.val (route index lay).1 k := by
      rw [← hL_eq]; rfl
    rw [mkIn_blk4]
    dsimp only
    rw [wpath_eq w lay _ _ hleaf, wpad_eq w lay _ _ hleaf, whigh_eq w lay _ _ hleaf (by omega), hheap,
      withHigh_tw _ _ _ hlay, wordsOf_blk4, mkTw_lo, mkTw_hi, f0, f8, hT0, f24, f32, f40, f48, f56, hhw, hpad.1, hpad.2]
    rcases (show mkBit (route index lay).1 k = 0 ∨ mkBit (route index lay).1 k = 1 by omega) with hb0 | hb0
    · have hsel : (route index lay).1 / 2 ^ k % 2 = 0 := hb0
      simp only [hsel, if_true]
      have hsib := hO.dig (mkSibO lay.val (route index lay).1 k) (by unfold mkSibO; omega)
        (by unfold mkSibO WX; omega) rs0 rs1
      rw [show WIT + mkSibO lay.val (route index lay).1 k = mkBlk lay.val (route index lay).1 k + 48 by
          unfold mkSibO WIT mkBlk; rw [hb0]; omega,
        show mkBlk lay.val (route index lay).1 k + 48 + 8 = mkBlk lay.val (route index lay).1 k + 56 by omega] at hsib
      have hn0 : s.getMem (BitVec.ofNat 64 (mkBlk lay.val (route index lay).1 k)) = dlo v := by
        have := hnode.1; unfold mkCur at this; rw [hb0, Nat.mul_zero, Nat.add_zero] at this; exact this
      have hn8 : s.getMem (BitVec.ofNat 64 (mkBlk lay.val (route index lay).1 k + 8)) = dhi v := by
        have := hnode.2; unfold mkCur at this; rw [hb0, Nat.mul_zero, Nat.add_zero] at this; exact this
      rw [hn0, hn8, hsib.1, hsib.2]
    · have hsel : ¬ (route index lay).1 / 2 ^ k % 2 = 0 := by
        intro h; have : mkBit (route index lay).1 k = 0 := h; omega
      simp only [hsel, if_false]
      have hsib := hO.dig (mkSibO lay.val (route index lay).1 k) (by unfold mkSibO; omega)
        (by unfold mkSibO WX; omega) rs0 rs1
      rw [show WIT + mkSibO lay.val (route index lay).1 k = mkBlk lay.val (route index lay).1 k by
          unfold mkSibO WIT mkBlk; rw [hb0]; omega] at hsib
      have hn0 : s.getMem (BitVec.ofNat 64 (mkBlk lay.val (route index lay).1 k + 48)) = dlo v := by
        have := hnode.1; unfold mkCur at this; rw [hb0, Nat.mul_one] at this; exact this
      have hn8 : s.getMem (BitVec.ofNat 64 (mkBlk lay.val (route index lay).1 k + 56)) = dhi v := by
        have := hnode.2; unfold mkCur at this; rw [hb0, Nat.mul_one, Nat.add_assoc] at this; exact this
      rw [hn0, hn8, hsib.1, hsib.2]
  · intro j hj ⟨h1, h2⟩
    rw [hfr _ (by unfold WIT WX at *; omega) (by unfold WIT mkBlk; omega)]
    exact hO j hj h1
/-- The top root (level-11 node, line B) is written at a place that depends only on bits 6..11 (the second-half
chunk): the compare tail reads it at `cmpDst`. -/
theorem mkDst_chunk (leaf : Nat) (hleaf : leaf < 4096) : cmpDst (mkSh 0 1 leaf) = mkDst 0 leaf := by
  have h := mkWa_lift 0 leaf 11 (by decide) hleaf (by decide)
  have hc : mkCi 0 11 = 1 := rfl
  rw [hc] at h
  unfold cmpDst mkDst
  rw [if_pos rfl, ← h]
  unfold mkLeafOf
  rw [show mkLo 0 1 = 6 from rfl, show (2 : Nat) ^ 6 = 64 from rfl, Nat.mul_comm]
theorem lvl_after (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (lay leaf : Nat) (u : MachineState) (hlay : lay < 4)
    (hleaf : leaf < 2 ^ hL lay) (k : Nat) (hk : k < hL lay) (t : MachineState)
    (hglob : Glob baseK w pk t) (hknown : KnownOK (mkKc lay ++ [(.x11, 64)]) t)
    (hkeep : ∀ r ∈ mkKeep, t.getReg r = u.getReg r)
    (h28 : lay ≠ 0 → t.getReg .x28 = T3.hyperWord (lay - 1) (u.getReg .x31).toNat)
    (h8 : lay = 1 → mkS0 lay leaf < k + 1 → t.getReg .x8 = BitVec.ofNat 64 s3v)
    (horig : Orig w (fun o => mkP lay leaf k o ∧ o ≠ mkBo lay leaf k + 16) t)
    (hbuffer : lay ≠ 0 → Orig w (fun o => BC.bufferStart (lay-1) ≤ o ∧ o < 24880) t)
    (h10 : t.getReg .x10 = BitVec.ofNat 64 (mkBlk lay leaf k)) (a : BitVec 256) :
    (k + 1 < hL lay → t.pc = pcOf (mkEc lay leaf (k + 1)) →
      t.getReg .x12 = BitVec.ofNat 64 (mkWa lay leaf (k + 1)) →
      MAfter w pk lay leaf u (k + 1) (projHalf (nodeHigh 3 lay (mkHeapN lay leaf k)) a) (writeHash t a)) ∧
    (lay = 0 → k + 1 = hL lay → t.pc = pcOf (mkFin lay leaf) → t.getReg .x12 = BitVec.ofNat 64 (mkDst lay leaf) →
      MkEnd w pk lay leaf u (projHalf (nodeHigh 3 lay (mkHeapN lay leaf k)) a) (writeHash t a)) := by
  refine ⟨fun hk1 hpc h12 => ?_, fun hl0 hk1 hpc h12 => ?_⟩
  · obtain ⟨hB16', hBlo', hBhi', -, -⟩ := mkBo_facts lay leaf (k + 1) hlay hleaf hk1
    obtain ⟨hw8, hw23, hwlo⟩ := mkWa_bounds lay leaf (k + 1) hlay hleaf hk1
    have hd : mkWa lay leaf (k + 1) + 32 < 2 ^ 64 := by omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [writeHash_pc, hpc, pcOf_add4]
    · exact Glob_writeHash hglob a _ h12 (safeDest_hi _ hwlo hw8 hw23)
    · intro p hp
      rw [writeHash_getReg]
      exact hknown p (by simpa [mkLvlK] using hp)
    · intro r hr; rw [writeHash_getReg]; exact hkeep r hr
    · rw [mkHigh_eq lay leaf k hlay hk1]
      exact mkNode_write lay leaf (k + 1) t a (by omega) hBhi' h12
    · have hw2 := Orig_writeHash horig a _ h12 hd
      exact hw2.mono8 (fun o h8 ho => mkP_step lay leaf k hlay hleaf hk1 o h8 ho)
    · rw [writeHash_getReg]; exact h12
    · intro _ h0; rw [writeHash_getReg]; exact h28 h0
    · intro h1 hs; rw [writeHash_getReg]; exact h8 h1 hs
    · intro h0
      exact mk_buffer_writeHash lay hlay (hbuffer h0) a _ h12 (by
        have := (mkBo_facts lay leaf (k + 1) hlay hleaf hk1).2.2.1
        have := mkBit_lt' leaf (k + 1)
        unfold mkWa mkBlk WIT; omega)
  · subst hl0
    have hl : leaf < 4096 := hleaf
    have hk11 : k = 11 := by change k + 1 = 12 at hk1; omega
    subst hk11
    obtain ⟨hw8, hw23, hwlo⟩ := mkWa_bounds 0 leaf 11 hlay hleaf hk
    have hdst : mkDst 0 leaf = mkWa 0 leaf 11 := rfl
    rw [hdst] at h12
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [writeHash_pc, hpc, pcOf_add4]
    · exact Glob_writeHash hglob a _ h12 (safeDest_hi _ hwlo hw8 hw23)
    · intro p hp; rw [writeHash_getReg]; exact hknown p hp
    · intro r hr; rw [writeHash_getReg]; exact hkeep r hr
    · rw [mkHigh_root leaf hl, T3.projHalf_false, hdst]
      exact DigAt.writeHash_lo t a _ h12 (by omega)
    · intro j _ hj
      exact (mkBase_zero_out _ hj).elim
    · rw [writeHash_getReg, hdst]; exact h12
    · rw [writeHash_getReg, h10]; rfl
theorem dispTgt_eval (leaf : Nat) (hleaf : leaf < 4096) (s : MachineState)
    (h23 : s.getReg .x23 = BitVec.ofNat 64 (16 * (2 ^ hL 0 + leaf))) :
    (mkDispTgt (mkSh 0 0 leaf)).eval s = pcOf (mkTabW 0 1 (mkSh 0 1 leaf)) := by
  have hsh0 : mkSh 0 0 leaf = leaf % 64 := by simp only [mkSh, mkLo, mkBits]; norm_num
  have hsh1 : mkSh 0 1 leaf = leaf / 64 := by simp only [mkSh, mkLo, mkBits]; norm_num; omega
  rw [hsh0, hsh1]
  unfold mkDispTgt
  simp only [E.eval, BinOp.eval, addC_eval, h23, show hL 0 = 12 from rfl, mkTabW, Nat.reduceEqDiff, and_self, if_true, pcOf]
  have hm : BitVec.ofNat 64 (16 * (2 ^ 12 + leaf)) + (BitVec.ofNat 64 1432 - BitVec.ofNat 64 (16 * (leaf % 64))) =
      BitVec.ofNat 64 (0x1000 + 4 * (15718 + 256 * (leaf / 64))) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  rw [hm, even_andNot1' _ (by omega)]
theorem lminTab_lt : (List.range 128).all (fun l => decide (mkS0 1 l < 6)) = true := by decide +kernel
theorem mkS0_lt (leaf : Nat) (hleaf : leaf < 128) : mkS0 1 leaf < 6 :=
  of_decide_eq_true (List.all_eq_true.mp lminTab_lt leaf (List.mem_range.mpr hleaf))
theorem mkWa_top5 (leaf : Nat) (hleaf : leaf < 4096) : mkWa 0 leaf 5 = mkP5 := by
  have h := mkWo_top5 leaf hleaf
  have hb := (mkBo_facts 0 leaf 5 (by decide) hleaf (by decide)).2.1
  rw [mkWa_wo _ _ _ (by omega), h]; rfl
theorem lfK_mkK (lay : Nat) : ∀ p ∈ mkK lay, p ∈ lfK lay := by
  intro p hp
  by_cases h0 : lay = 0
  · subst h0
    simp only [mkK, if_pos, baseK, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    repeat' first | subst p | rcases hp with hp | hp
    all_goals simp [lfK, postLf, leafK, lfKeepK, baseK]
  · simp only [mkK, h0, if_false, baseK, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    repeat' first | subst p | rcases hp with hp | hp
    all_goals simp [lfK, postLf, leafK, lfKeepK, h0, baseK]
theorem lvl_step (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer) (u : MachineState)
    (hidx : index < 2 ^ 31)
    (hs7 : lay.val = 0 → u.getReg .x23 = BitVec.ofNat 64 (dispatchHeap 0 (route index lay).1))
    (ht5 : lay.val ≠ 0 → u.getReg .x31 = BitVec.ofNat 64 (route index lay).2)
    (k : Nat) (hk : k < hL lay.val) (hlive : k < mkStop lay.val) (v : Digest) (s : MachineState)
    (hs : MAfter w pk lay.val (route index lay).1 u k v s) :
    ∃ t, Steps image s (mkLvlSt lay.val (route index lay).1 k) (mkLvlSt lay.val (route index lay).1 k) t ∧
      fetch image t = some (.base .ECALL) ∧
      t.getReg .x5 = 0 ∧ hashArgumentsValid t = true ∧ hashInput t = toQ (pad64 (mkIn w index lay v k)) ∧
      ∀ a : BitVec 256,
        (k + 1 < hL lay.val → MAfter w pk lay.val (route index lay).1 u (k + 1)
          (projHalf (nodeHigh 3 lay.val (mkHeapN lay.val (route index lay).1 k)) a) (writeHash t a)) ∧
        (k + 1 = hL lay.val → MkEnd w pk lay.val (route index lay).1 u
          (projHalf (nodeHigh 3 lay.val (mkHeapN lay.val (route index lay).1 k)) a) (writeHash t a)) := by
  have hlay := lay.isLt
  have hleaf : (route index lay).1 < 2 ^ hL lay.val := leaf_lt index lay
  obtain ⟨hci, hlo, hkk, hdisp, hnext, hlast⟩ := mk_facts lay.val k hlay hk
  obtain ⟨hB8, hBlo, hBhi, hBase, -⟩ := mkBo_facts lay.val (route index lay).1 k hlay hleaf hk
  have hlk : mkLo lay.val (mkCi lay.val k) + (k - mkLo lay.val (mkCi lay.val k)) = k := by omega
  have hblk := BC.mkBlockCheck_at lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1) hlay hci
    (mkSh_lt _ _ _)
  have hliveChunk : k - mkLo lay.val (mkCi lay.val k) <
      mkBits lay.val (mkCi lay.val k) - (if lay.val = 0 then 0 else 1) := by
    by_cases h0 : lay.val = 0
    · simpa [h0] using hkk
    · have : mkStop lay.val = hL lay.val - 1 := by simp [mkStop, h0]
      simp only [mkCi, mkLo, mkBits, h0, false_and, if_false, Nat.sub_zero]; omega
  have hlvl := BC.mkLvl_of hblk _ hliveChunk
  have hpc0 : s.pc = pcOf (mkShp lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1) +
      mkOff lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1)
        (k - mkLo lay.val (mkCi lay.val k)) + 2) := by rw [hs.pc]; rfl
  have hkn0 : KnownOK (mkLvlK lay.val (mkLo lay.val (mkCi lay.val k) + (k - mkLo lay.val (mkCi lay.val k)))) s := by
    rw [hlk]; exact hs.known
  have hknAddr : KnownOK (mkLvlKN lay.val (mkCi lay.val k)
      (mkSh lay.val (mkCi lay.val k) (route index lay).1) (k - mkLo lay.val (mkCi lay.val k))) s := by
    intro p hp
    simp only [mkLvlKN, List.mem_append] at hp
    rcases hp with (hp | hp) | hp
    · exact hkn0 p hp
    · split_ifs at hp with h0
      · simp only [List.mem_singleton] at hp
        subst p
        dsimp only
        rw [hlk, mkWa_lift _ _ _ hlay hleaf hk]
        exact hs.dstReg
      · simp at hp
    · split_ifs at hp with h0
      · simp only [List.mem_singleton] at hp
        subst p
        obtain ⟨h0a, h0b, h0c⟩ := h0
        have hk5 : k = 5 := by rw [h0b] at h0c; simpa [mkLo] using h0c
        have hl0 : (route index lay).1 < 4096 := by rw [h0a] at hleaf; simpa [hL] using hleaf
        dsimp only
        have hd := hs.dstReg
        rw [hk5, h0a, mkWa_top5 _ hl0] at hd
        exact hd
      · simp at hp
  have h23 : lay.val = 0 → s.getReg .x23 = BitVec.ofNat 64 (dispatchHeap 0 (route index lay).1) :=
    fun h => (hs.keep .x23 (by simp [mkKeep])).trans (hs7 h)
  by_cases hd : lay.val = 0 ∧ k = 5
  · obtain ⟨hl0, hk5⟩ := hd
    have hdt : mkIsDisp lay.val (mkCi lay.val k) (k - mkLo lay.val (mkCi lay.val k)) = true := by
      rw [hdisp]; simp [hl0, hk5]
    have hD : mkLvlCheckD lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1)
        (k - mkLo lay.val (mkCi lay.val k)) = true := by
      simp only [BC.mkLvlCheck, mkLvlCheck, hdt, if_true] at hlvl; exact hlvl
    obtain ⟨t1, ht1⟩ := mkSpec_run hD s hpc0 hknAddr (by simp [mkLvlSpecD]) (by simp)
    have hleaf0 : (route index lay).1 < 4096 := by rw [hl0] at hleaf; simpa [hL] using hleaf
    have hpc1 : t1.pc = pcOf (mkTabW 0 1 (mkSh 0 1 (route index lay).1)) := by
      rw [ht1.spc (mkDispTgt (mkSh lay.val (mkCi lay.val k) (route index lay).1)) (by simp [mkLvlSpecD])]
      rw [hl0, hk5, show mkCi 0 5 = 0 from rfl]
      exact dispTgt_eval _ hleaf0 s (by simpa [dispatchHeap, s7Bias, hL, hl0] using h23 hl0)
    have hkt1 : KnownOK (mkLvlPostD lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1)
      (k - mkLo lay.val (mkCi lay.val k))) t1 := ht1.known
    have hkn1 : KnownOK (mkEntK 0 1) t1 := by
      intro p hp
      simp only [mkEntK, Nat.reduceEqDiff, and_self, if_true, List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · exact hkt1 p (List.mem_append_left _ (by rw [hl0]; exact hp))
      · exact hkt1 (.x12, BitVec.ofNat 64 mkP5) (by simp [mkLvlPostD])
    have hent := BC.mkEnt_of (BC.mkBlockCheck_at 0 1 (mkSh 0 1 (route index lay).1) (by decide +kernel)
      (by decide +kernel) (mkSh_lt _ _ _))
    obtain ⟨t, ht⟩ := mkSpec_run hent t1 hpc1 hkn1 (by simp [BC.mkEntSpec]) (by simp)
    have hst : Steps image s (mkLvlSt lay.val (route index lay).1 k) (mkLvlSt lay.val (route index lay).1 k) t := by
      have := ht1.steps.trans ht.steps
      simp only [mkLvlSpecD, BC.mkEntSpec, Nat.reduceEqDiff, and_self, if_true] at this
      have e : mkLvlSt lay.val (route index lay).1 k =
          mkWords lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1)
            (k - mkLo lay.val (mkCi lay.val k)) + 2 := by
        simp only [mkLvlSt, hl0, hk5, and_self, if_true]; rfl
      rw [e]; exact this
    have hmem : ∀ A, t.getMem A =
        memEval s (mkLvlMem lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1) k) A := by
      intro A
      rw [ht.mem]
      show memEval t1 [] A = _
      rw [memEval_nil, ht1.mem]
      show memEval s (mkLvlMem _ _ _ (mkLo lay.val (mkCi lay.val k) + (k - mkLo lay.val (mkCi lay.val k)))) A = _
      rw [hlk]
    have h10 : t.getReg .x10 = BitVec.ofNat 64 (mkBlk lay.val (route index lay).1 k) := by
      rw [ht.keep .x10 (by simp [mkEntKeep])]
      have := hkt1 (.x10, BitVec.ofNat 64 (mkBlk lay.val (mkLeafOf lay.val (mkCi lay.val k)
        (mkSh lay.val (mkCi lay.val k) (route index lay).1)) (mkLo lay.val (mkCi lay.val k) +
          (k - mkLo lay.val (mkCi lay.val k))))) (by simp [mkLvlPostD])
      rw [this, hlk, mkBlk_lift _ _ _ hlay hleaf hk]
    have h11 : t.getReg .x11 = BitVec.ofNat 64 64 := by
      rw [ht.keep .x11 (by simp [mkEntKeep])]
      exact hkt1 (.x11, 64) (by simp [mkLvlPostD])
    have hkt : KnownOK (mkEntPost 0 1 (mkSh 0 1 (route index lay).1)) t := ht.known
    have hk6 : k + 1 < hL lay.val := by rw [hl0, hk5]; decide +kernel
    have h12 : t.getReg .x12 = BitVec.ofNat 64 (mkWa lay.val (route index lay).1 (k + 1)) := by
      rw [hkt (.x12, BitVec.ofNat 64 (mkWa 0 (mkLeafOf 0 1 (mkSh 0 1 (route index lay).1)) (mkLo 0 1)))
        (by simp [mkEntPost])]
      have hl := mkWa_lift lay.val (route index lay).1 (k + 1) hlay hleaf hk6
      rw [hl0, hk5] at hl ⊢
      exact congrArg (BitVec.ofNat 64) hl
    obtain ⟨hinp, horig⟩ := lvl_input w pk index lay u hidx hs7 ht5 k hk v s t hs hmem h10 h11
    have hglob : Glob baseK w pk t := ht.glob _ _ _ (ht1.glob _ _ _ hs.glob (RelOK.nil s)) (RelOK.nil t1)
    have hknown : KnownOK (mkKc lay.val ++ [(.x11, 64)]) t := by
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hkt p (by rw [← hl0]; simp [mkEntPost, hp])
      · simp only [List.mem_singleton] at hp; subst hp; exact h11
    have hkeep : ∀ r ∈ mkKeep, t.getReg r = u.getReg r := by
      intro r hr
      rw [ht.keep r (mkKeep_sub _ r hr), ht1.keep r (List.mem_append_left _ (mkKeep_sub _ r hr))]
      exact hs.keep r hr
    obtain ⟨hw8, hw23, -⟩ := mkWa_bounds lay.val (route index lay).1 (k + 1) hlay hleaf hk6
    refine ⟨t, hst, ht.ecall rfl, hknown (.x5, 0) (by simp [mkKc, baseK]),
      hashArgs_of t _ 64 _ h10 h11 h12 (by unfold mkBlk; omega) (by decide +kernel) (by unfold mkBlk; omega)
        hw8 (by omega), hinp, fun a => ?_⟩
    obtain ⟨hA1, -⟩ := lvl_after w pk lay.val (route index lay).1 u hlay hleaf k hk t hglob hknown hkeep
      (fun h => absurd hl0 h) (fun h => by rw [hl0] at h; exact absurd h (by decide)) horig
      (lvl_bufferOrig lay.val hlay _ k hleaf hk s t hs.bufferOrig hmem) h10 a
    refine ⟨fun _ => hA1 hk6 ?_ h12, fun h => absurd h (by omega)⟩
    rw [ht.pc rfl]
    simp only [BC.mkEntSpec, mkEc, hl0, hk5, show mkCi 0 6 = 1 from rfl, show mkLo 0 1 = 6 from rfl]
    rfl
  · have hdf : mkIsDisp lay.val (mkCi lay.val k) (k - mkLo lay.val (mkCi lay.val k)) = false := by
      rw [hdisp]; exact decide_eq_false hd
    have hN : mkLvlCheckN lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1)
        (k - mkLo lay.val (mkCi lay.val k)) = true := by
      simp only [BC.mkLvlCheck, mkLvlCheck, hdf, Bool.false_eq_true, if_false] at hlvl; exact hlvl
    obtain ⟨t, ht⟩ := mkSpec_run hN s hpc0 hknAddr (by simp [mkLvlSpecN]) (by simp)
    have hst : Steps image s (mkLvlSt lay.val (route index lay).1 k) (mkLvlSt lay.val (route index lay).1 k) t := by
      have := ht.steps
      have e : mkLvlSt lay.val (route index lay).1 k =
          mkBody lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1)
            (k - mkLo lay.val (mkCi lay.val k)) := by simp only [mkLvlSt, if_neg hd]
      rw [e]; exact this
    have hmem : ∀ A, t.getMem A =
        memEval s (mkLvlMem lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1) k) A := by
      intro A; rw [ht.mem]; simp only [mkLvlSpecN, hlk]
    have hkt : KnownOK (mkLvlPostN lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1)
        (k - mkLo lay.val (mkCi lay.val k))) t := ht.known
    have h10 : t.getReg .x10 = BitVec.ofNat 64 (mkBlk lay.val (route index lay).1 k) := by
      have := hkt (.x10, BitVec.ofNat 64 (mkBlk lay.val (mkLeafOf lay.val (mkCi lay.val k)
        (mkSh lay.val (mkCi lay.val k) (route index lay).1)) (mkLo lay.val (mkCi lay.val k) +
          (k - mkLo lay.val (mkCi lay.val k))))) (by simp [mkLvlPostN])
      rw [this, hlk, mkBlk_lift _ _ _ hlay hleaf hk]
    have h11 : t.getReg .x11 = BitVec.ofNat 64 64 := hkt (.x11, 64) (by simp [mkLvlPostN])
    have h12 : t.getReg .x12 = BitVec.ofNat 64 (mkNextA2 lay.val (mkCi lay.val k)
        (mkSh lay.val (mkCi lay.val k) (route index lay).1) (k - mkLo lay.val (mkCi lay.val k))) :=
      hkt (.x12, BitVec.ofNat 64 (mkNextA2 lay.val (mkCi lay.val k)
        (mkSh lay.val (mkCi lay.val k) (route index lay).1) (k - mkLo lay.val (mkCi lay.val k))))
        (List.mem_append_left _ (List.mem_append_right _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))))
    obtain ⟨hinp, horig⟩ := lvl_input w pk index lay u hidx hs7 ht5 k hk v s t hs hmem h10 h11
    have hglob : Glob baseK w pk t := ht.glob _ _ _ hs.glob (RelOK.nil s)
    have hknown : KnownOK (mkKc lay.val ++ [(.x11, 64)]) t := by
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hkt p (by simp [mkLvlPostN, hp])
      · simp only [List.mem_singleton] at hp; subst hp; exact h11
    have hkeep : ∀ r ∈ mkKeep, t.getReg r = u.getReg r := by
      intro r hr; rw [ht.keep r (List.mem_append_left _ (mkKeep_sub _ r hr))]; exact hs.keep r hr
    have h28 : lay.val ≠ 0 → t.getReg .x28 = T3.hyperWord (lay.val - 1) (u.getReg .x31).toNat := by
      intro hl0
      by_cases hk0 : k = 0
      · have hreg : mkLvlRegs lay.val (mkLo lay.val (mkCi lay.val k) + (k - mkLo lay.val (mkCi lay.val k))) =
            [(.x28, t3E (lay.val - 1))] := by
          rw [hlk, hk0]; simp [mkLvlRegs, hl0]
        have hr : t.getReg .x28 = (t3E (lay.val - 1)).eval s :=
          ht.regs (.x28, t3E (lay.val - 1)) (by simp only [mkLvlSpecN]; rw [hreg]; exact List.mem_singleton.mpr rfl)
        have htr := tree_lt index lay hidx
        rw [hr, ht5 hl0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        exact t3E_eval _ _ (by omega) htr s ((hs.keep .x31 (by simp [mkKeep])).trans (ht5 hl0)) hs.glob.2.2.2.2.2
      · have hkp : Reg.x28 ∈ mkLvlKeep lay.val (mkLo lay.val (mkCi lay.val k) + (k - mkLo lay.val (mkCi lay.val k))) := by
          rw [hlk]; simp [mkLvlKeep, hk0]
        rw [ht.keep .x28 (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ hkp)))]
        exact hs.x28 hk0 hl0
    have h8 : lay.val = 1 → mkS0 lay.val (route index lay).1 < k + 1 → t.getReg .x8 = BitVec.ofNat 64 s3v := by
      intro h1 hs0
      have hsh : mkSh lay.val (mkCi lay.val k) (route index lay).1 = (route index lay).1 := by
        rw [show mkCi lay.val k = 0 by simp [mkCi, h1]]; exact mkSh_low _ _ (by omega) hleaf
      have hkk0 : k - mkLo lay.val (mkCi lay.val k) = k := by simp [mkCi, mkLo, h1]
      by_cases he : k = mkS0 lay.val (route index lay).1
      · apply hkt (.x8, BitVec.ofNat 64 s3v)
        simp only [mkLvlPostN, List.mem_append]
        right
        rw [hsh, hkk0]
        have he' : k = mkS0 1 (route index lay).1 := by rw [← h1]; exact he
        simp [mkS0Post, h1, he']
      · rw [ht.keep .x8 (List.mem_append_right _ (by
            rw [hsh, hkk0]
            have he' : ¬ k = mkS0 1 (route index lay).1 := by rw [← h1]; exact he
            simp [mkS0Keep, h1, he']))]
        exact hs.x8 h1 (by omega)
    have hpcT : t.pc = pcOf (mkShp lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1) +
        mkOff lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1)
          (k - mkLo lay.val (mkCi lay.val k) + 1) + 1) := by
      have h := ht.pc rfl
      simpa only [mkLvlSpecN] using h
    have hdst : ∃ d, t.getReg .x12 = BitVec.ofNat 64 d ∧ d % 8 = 0 ∧ d + 32 ≤ 2 ^ 24 := by
      by_cases hk1 : k + 1 < hL lay.val
      · obtain ⟨hn1, hn2, hn3⟩ := hnext hk1 hd
        refine ⟨_, h12, ?_⟩
        simp only [mkNextA2, if_pos hn3]
        have hl := mkWa_lift lay.val (route index lay).1 (k + 1) hlay hleaf hk1
        rw [hn1] at hl
        rw [show mkLo lay.val (mkCi lay.val k) + (k - mkLo lay.val (mkCi lay.val k)) + 1 = k + 1 by omega, hl]
        have := mkWa_bounds lay.val (route index lay).1 (k + 1) hlay hleaf hk1
        omega
      · have hk1' : k + 1 = hL lay.val := by omega
        obtain ⟨-, hn2, -⟩ := hlast hk1'
        refine ⟨_, h12, ?_⟩
        simp only [mkNextA2, if_neg hn2]
        rw [hlk, mkWa_lift _ _ _ hlay hleaf hk]
        have := mkWa_bounds lay.val (route index lay).1 k hlay hleaf hk
        omega
    obtain ⟨d, hd12, hd8, hd32⟩ := hdst
    refine ⟨t, hst, ht.ecall rfl, hknown (.x5, 0) (by simp [mkKc, baseK]),
      hashArgs_of t _ 64 _ h10 h11 hd12 (by unfold mkBlk; omega) (by decide +kernel) (by unfold mkBlk; omega) hd8 hd32,
      hinp, fun a => ?_⟩
    obtain ⟨hA1, hA2⟩ := lvl_after w pk lay.val (route index lay).1 u hlay hleaf k hk t hglob hknown hkeep h28 h8 horig
      (lvl_bufferOrig lay.val hlay _ k hleaf hk s t hs.bufferOrig hmem) h10 a
    refine ⟨fun hk1 => hA1 hk1 ?_ ?_, fun hk1 => hA2 ?_ hk1 ?_ ?_⟩
    · obtain ⟨hn1, hn2, hn3⟩ := hnext hk1 hd
      rw [hpcT]; unfold mkEc; rw [hn1, hn2]
      rfl
    · obtain ⟨hn1, hn2, hn3⟩ := hnext hk1 hd
      rw [h12]; simp only [mkNextA2, if_pos hn3]
      have hl := mkWa_lift lay.val (route index lay).1 (k + 1) hlay hleaf hk1
      rw [hn1] at hl
      rw [show mkLo lay.val (mkCi lay.val k) + (k - mkLo lay.val (mkCi lay.val k)) + 1 = k + 1 by omega, hl]
    · by_contra h0
      have : mkStop lay.val = hL lay.val - 1 := by simp [mkStop, h0]
      omega
    · obtain ⟨hl1, hl2, hl3⟩ := hlast hk1
      rw [hpcT]; unfold mkFin; rw [← hl1, hl3]
      rfl
    · obtain ⟨hl1, hl2, hl3⟩ := hlast hk1
      have h0 : lay.val = 0 := by
        by_contra h0
        have : mkStop lay.val = hL lay.val - 1 := by simp [mkStop, h0]
        omega
      rw [h12]; simp only [mkNextA2, if_neg hl2]
      rw [hlk, mkWa_lift _ _ _ hlay hleaf hk]
      have hk11 : k = 11 := by rw [h0] at hk1; simp [hL] at hk1; omega
      rw [h0, hk11]; rfl
def MkStop (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (lay leaf : Nat) (u : MachineState)
    (v : Digest) (s : MachineState) : Prop :=
  if lay = 0 then MkEnd w pk lay leaf u v s else MAfter w pk lay leaf u (mkStop lay) v s
def mkCycR (lay leaf : Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | k, n + 1 => mkLvlSt lay leaf k + 8 + mkCycR lay leaf (k + 1) n
def mkFuelR (lay leaf : Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | k, n + 1 => mkLvlSt lay leaf k + 1 + mkFuelR lay leaf (k + 1) n
theorem mkHeapN_height (lay : Layer) (leaf j : Nat) :
    2 ^ (height lay - j - 1) + leaf / 2 ^ (j + 1) = mkHeapN lay.val leaf j := by
  unfold mkHeapN; rw [hL_eq]
theorem merkle_rest (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer) (u : MachineState)
    (hidx : index < 2 ^ 31)
    (hs7 : lay.val = 0 → u.getReg .x23 = BitVec.ofNat 64 (dispatchHeap 0 (route index lay).1))
    (ht5 : lay.val ≠ 0 → u.getReg .x31 = BitVec.ofNat 64 (route index lay).2)
    (K : Digest → OracleComp HashSpec Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ root t, MkStop w pk lay.val (route index lay).1 u root t → GoodQ t N C Q A (K root)) :
    ∀ n k v s, k + n = mkStop lay.val → k < hL lay.val → MAfter w pk lay.val (route index lay).1 u k v s →
      GoodQ s (N + mkFuelR lay.val (route index lay).1 k n) (C + mkCycR lay.val (route index lay).1 k n) Q
        (A + mkCycR lay.val (route index lay).1 k n)
        (ccM ((List.range' k n).foldlM (mkStep w index lay) v) K) := by
  intro n
  induction n with
  | zero =>
    intro k v s hkn hk hs
    have h0 : lay.val ≠ 0 := by intro h; simp [mkStop, h] at hkn; rw [h] at hk; omega
    simp only [List.range'_zero, List.foldlM_nil, ccM_pure, mkFuelR, mkCycR, Nat.add_zero]
    apply hK v s
    simpa [MkStop, h0, ← hkn] using hs
  | succ m ih =>
    intro k v s hkn hk hs
    have hlive : k < mkStop lay.val := by omega
    obtain ⟨t, hst, hf, h5, hv, hin, hpost⟩ := lvl_step w pk index lay u hidx hs7 ht5 k hk hlive v s hs
    rw [List.range'_succ, List.foldlM_cons, mkStep_eq, mkHeapN_height]
    have H : ∀ a : BitVec 256, GoodQ (writeHash t a) (N + mkFuelR lay.val (route index lay).1 (k + 1) m)
        (C + mkCycR lay.val (route index lay).1 (k + 1) m) Q (A + mkCycR lay.val (route index lay).1 (k + 1) m)
        (ccM ((fun v' => (List.range' (k + 1) m).foldlM (mkStep w index lay) v')
          (projHalf (nodeHigh 3 lay.val (mkHeapN lay.val (route index lay).1 k)) a)) K) := by
      intro a
      by_cases he : k + 1 = hL lay.val
      · have hm : m = 0 := by unfold mkStop at hkn; split_ifs at hkn <;> omega
        subst m
        have h0 : lay.val = 0 := by unfold mkStop at hkn; split_ifs at hkn <;> omega
        simp only [List.range'_zero, List.foldlM_nil, ccM_pure, mkFuelR, mkCycR, Nat.add_zero]
        apply hK
        simpa [MkStop, h0] using (hpost a).2 he
      · exact ih (k + 1) _ _ (by omega) (by omega) ((hpost a).1 (by omega))
    have hg := GoodQ.projHash_bind (f := fun v' => (List.range' (k + 1) m).foldlM (mkStep w index lay) v')
      (nodeHigh 3 lay.val (mkHeapN lay.val (route index lay).1 k)) hf h5 hv hin H
    rw [mkIn_blocks] at hg
    simp only [mkFuelR, mkCycR]
    exact GoodQ.steps' hst hg (by omega) (by omega) (fun q => ⟨q, by omega⟩)
def merklePrefix (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (value : Digest) : T3.M Digest :=
  (List.range (mkStop lay.val)).foldlM (mkStep w index lay) value
def mkFuel (lay : Nat) : Nat := 2 + mkFuelR lay 0 0 (mkStop lay)
def mkCyc (lay : Nat) : Nat := 1 + 8 * lfBlocks lay + mkCycR lay 0 0 (mkStop lay)
/-- The path cost does not depend on the leaf (L1: the `addi s0` sits in exactly one level for every leaf). -/
def mkCostOk (lay : Nat) : Bool :=
  (List.range (2 ^ hL lay)).all fun leaf =>
    mkCycR lay leaf 0 (mkStop lay) == mkCycR lay 0 0 (mkStop lay) &&
      mkFuelR lay leaf 0 (mkStop lay) == mkFuelR lay 0 0 (mkStop lay)
theorem mkCostOk_all : mkCostOk 0 = true ∧ mkCostOk 1 = true ∧ mkCostOk 2 = true ∧ mkCostOk 3 = true := by
  decide +kernel
theorem mkCost_leaf (lay leaf : Nat) (hlay : lay < 4) (hleaf : leaf < 2 ^ hL lay) :
    mkCycR lay leaf 0 (mkStop lay) = mkCycR lay 0 0 (mkStop lay) ∧
      mkFuelR lay leaf 0 (mkStop lay) = mkFuelR lay 0 0 (mkStop lay) := by
  have h : mkCostOk lay = true := by
    interval_cases lay
    · exact mkCostOk_all.1
    · exact mkCostOk_all.2.1
    · exact mkCostOk_all.2.2.1
    · exact mkCostOk_all.2.2.2
  have := List.all_eq_true.mp h leaf (List.mem_range.mpr hleaf)
  simpa only [Bool.and_eq_true, beq_iff_eq] using this
theorem mkCyc_vals : mkCyc 0 = 256 ∧ mkCyc 1 = 166 ∧ mkCyc 2 = 153 ∧ mkCyc 3 = 153 := by decide +kernel
theorem mkFuel_vals : mkFuel 0 = 61 ∧ mkFuel 1 = 37 ∧ mkFuel 2 = 31 ∧ mkFuel 3 = 31 := by decide +kernel
theorem mkBits_stabBits (lay : Nat) (hlay : lay < 4) : mkBits lay 0 = stabBits lay := by
  interval_cases lay <;> decide +kernel
theorem leafHigh_bit (leaf : Nat) : T3.leafHigh leaf = decide (mkBit leaf 0 = 0) := by
  unfold T3.leafHigh mkBit
  simp only [pow_zero, Nat.div_one]
  rcases Nat.mod_two_eq_zero_or_one leaf with h | h <;> simp [h]
theorem merkle_good (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer) (ends : List Digest) (u : MachineState)
    (hidx : index < 2 ^ 31) (hu : LeafOut w pk index lay ends u)
    (K : Digest → OracleComp HashSpec Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ root t, MkStop w pk lay.val (route index lay).1 u root t → GoodQ t N C Q A (K root)) :
    GoodQ u (N + mkFuel lay.val) (C + mkCyc lay.val) Q (A + mkCyc lay.val)
      (ccM (leafHashS w lay (route index lay).2 (route index lay).1 ends >>= merklePrefix w index lay) K) := by
  have hlay := lay.isLt
  have hleaf : (route index lay).1 < 2 ^ hL lay.val := leaf_lt index lay
  have hkU : KnownOK (lfK lay.val) u := hu.glob.1
  have hknown : KnownOK (mkKc lay.val) u := fun p hp => hkU p (lfK_mkK _ p (mkKc_mkK _ p hp))
  have hhL : 0 < hL lay.val := by interval_cases lay.val <;> decide +kernel
  have hent := BC.mkEnt_of (BC.mkBlockCheck_at lay.val 0 (mkSh lay.val 0 (route index lay).1) hlay
    (by unfold mkNch; split <;> omega) (mkSh_lt _ _ _))
  have hpc : u.pc = pcOf (mkTabW lay.val 0 (mkSh lay.val 0 (route index lay).1)) := by
    rw [hu.pc]
    have e2 : mkSh lay.val 0 (route index lay).1 = (route index lay).1 % 2 ^ stabBits lay.val := by
      simp only [mkSh, show mkLo lay.val 0 = 0 by simp [mkLo], Nat.pow_zero, Nat.div_one, mkBits_stabBits _ hlay]
    rw [e2]; simp [mkTabW]
  have hEntKnown : KnownOK (mkEntK lay.val 0) u := by
    simpa [mkEntK] using hknown
  obtain ⟨t, ht⟩ := mkSpec_run hent u hpc hEntKnown (by simp [BC.mkEntSpec]) (by simp)
  have hmem : ∀ A, t.getMem A = u.getMem A := fun A => by rw [ht.mem]; rfl
  have h10u : u.getReg .x10 = BitVec.ofNat 64 (lfBase lay.val) :=
    hkU (.x10, BitVec.ofNat 64 (lfBase lay.val)) (by simp [lfK, postLf, lfBase])
  have h11u : u.getReg .x11 = BitVec.ofNat 64 (lfBytes lay.val) :=
    hkU (.x11, BitVec.ofNat 64 (if lay.val = 0 then 896 else 704)) (by simp [lfK, postLf])
  have h10 : t.getReg .x10 = u.getReg .x10 := ht.keep .x10 (by simp [mkEntKeep])
  have h11 : t.getReg .x11 = u.getReg .x11 := ht.keep .x11 (by simp [mkEntKeep])
  have hkt : KnownOK (mkEntPost lay.val 0 (mkSh lay.val 0 (route index lay).1)) t := ht.known
  have hc0 : mkCi lay.val 0 = 0 := by simp [mkCi]
  have h12 : t.getReg .x12 = BitVec.ofNat 64 (mkWa lay.val (route index lay).1 0) := by
    have hl := mkWa_lift lay.val (route index lay).1 0 hlay hleaf hhL
    rw [hc0] at hl
    rw [hkt (.x12, BitVec.ofNat 64 (mkWa lay.val (mkLeafOf lay.val 0 (mkSh lay.val 0 (route index lay).1))
      (mkLo lay.val 0))) (by simp [mkEntPost]), show mkLo lay.val 0 = 0 by simp [mkLo], hl]
  obtain ⟨hw8, hw23, hwlo⟩ := mkWa_bounds lay.val (route index lay).1 0 hlay hleaf hhL
  obtain ⟨hB8, hBlo, hBhi, hBase, hBtop⟩ := mkBo_facts lay.val (route index lay).1 0 hlay hleaf hhL
  have hin : hashInput t = toQ (pad64 (leafInS w lay (route index lay).2 (route index lay).1 ends)) := by
    rw [mkHashInput_congr h10 h11 hmem]; exact hu.hashInput.1
  have hv : hashArgumentsValid t = true := by
    refine hashArgs_of t (lfBase lay.val) (lfBytes lay.val) _ (h10.trans h10u) (h11.trans h11u) h12
      (by fin_cases lay <;> decide +kernel) (by fin_cases lay <;> decide +kernel) (by fin_cases lay <;> decide +kernel)
      hw8 (by omega)
  have hG : Glob baseK w pk t := ht.glob _ _ _ hu.glob (RelOK.nil u)
  have hcost := mkCost_leaf lay.val (route index lay).1 hlay hleaf
  have H : ∀ a : BitVec 256, GoodQ (writeHash t a) (N + mkFuelR lay.val (route index lay).1 0 (mkStop lay.val))
      (C + mkCycR lay.val (route index lay).1 0 (mkStop lay.val)) Q
      (A + mkCycR lay.val (route index lay).1 0 (mkStop lay.val))
      (ccM (merklePrefix w index lay (T3.projHalf (T3.leafHigh (route index lay).1) a)) K) := by
    intro a
    have hA : MAfter w pk lay.val (route index lay).1 u 0 (T3.projHalf (T3.leafHigh (route index lay).1) a)
        (writeHash t a) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun h => absurd rfl h, fun _ h => absurd h (Nat.not_lt_zero _), ?_⟩
      · rw [writeHash_pc, ht.pc rfl, pcOf_add4]
        simp only [BC.mkEntSpec, mkEc, hc0, show mkLo lay.val 0 = 0 by simp [mkLo]]
        rfl
      · exact Glob_writeHash hG a _ h12 (safeDest_hi _ hwlo hw8 hw23)
      · intro p hp
        rw [writeHash_getReg]
        have hp' : p ∈ mkK lay.val := by simpa [mkLvlK] using hp
        rcases mkK_cases _ p hp' with hp'' | hp''
        · exact hkt p (List.mem_append_left _ hp'')
        · rw [ht.keep p.1 (by rw [hp'']; simp [mkEntKeep, mkKeep])]
          exact hkU p (lfK_mkK _ p hp')
      · intro r hr; rw [writeHash_getReg]; exact ht.keep r (mkKeep_sub _ r hr)
      · rw [leafHigh_bit]
        exact mkNode_write lay.val (route index lay).1 0 t a (by omega) hBhi h12
      · have hO : Orig w (fun o => 8256 ≤ o ∧
            o < ClaudeWCT.W9.T3M.layerBase lay + 16 * ClaudeWCT.W9.T3M.pathSlots lay) t :=
          hu.orig.frame (fun j _ _ => hmem _)
        have hw2 := Orig_writeHash hO a _ h12 (by omega)
        refine hw2.mono8 (fun o h8 ho => ?_)
        obtain ⟨⟨h1, h2⟩, h3⟩ := mkP_leaf lay.val (route index lay).1 hlay hleaf o h8 ho
        exact ⟨⟨h1, by rw [← mkBase_eq, ← mkPS_eq]; exact h2⟩, by unfold WIT at *; omega⟩
      · rw [writeHash_getReg]; exact h12
      · intro h0
        have h0' : lay ≠ 0 := by intro he; apply h0; rw [he]; rfl
        have hbuf := (hu.bufferOrig h0').frame (fun j _ _ => hmem _)
        have hb0 := mkBit_lt' (route index lay).1 0
        exact mk_buffer_writeHash lay.val hlay hbuf a _ h12 (by unfold mkWa mkBlk WIT; omega)
    rw [merklePrefix, List.range_eq_range']
    have hs7 : lay.val = 0 → u.getReg .x23 = BitVec.ofNat 64 (dispatchHeap 0 (route index lay).1) := by
      intro h
      rw [hu.s7 (Fin.ext h)]
    exact merkle_rest w pk index lay u hidx hs7 hu.t5 K N C A Q hK (mkStop lay.val) 0 _ _ (by omega) hhL hA
  have h5 : t.getReg .x5 = 0 := hkt (.x5, 0) (by simp [mkEntPost, mkKc, baseK])
  have hg := GoodQ.projHash_bind (f := merklePrefix w index lay) (K := K) (T3.leafHigh (route index lay).1)
    (ht.ecall rfl) h5 hv hin H
  rw [hu.hashInput.2] at hg
  have hst := ht.steps
  simp only [BC.mkEntSpec, Nat.reduceEqDiff, and_false, if_false] at hst
  unfold leafHashS
  rw [hcost.1, hcost.2] at hg
  exact GoodQ.steps' hst hg (by unfold mkFuel; omega) (by unfold mkCyc; omega) (fun q => ⟨q, by unfold mkCyc; omega⟩)
open ClaudeWCT.WCT9 (LayerMsg)
def mkMessage (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (v : Digest) : LayerMsg :=
  if lay.val = 0 then .forest v else
  let other := ClaudeWCT.W9.T3M.wpath w lay (route index lay).1 (height lay - 1)
  if (route index lay).1 / 2 ^ (height lay - 1) % 2 = 0 then .pair v other else .pair other v
def merkleMsg (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (v : Digest) : T3.M LayerMsg :=
  merklePrefix w index lay v >>= fun root => pure (mkMessage w index lay root)
theorem layerPairP_eq (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (h0 : lay.val ≠ 0) (digits : List Nat) :
    (ClaudeWCT.W9.T3M.layerPairP w index lay digits >>= fun p => pure (LayerMsg.pair p.1 p.2)) =
      (chainsP w lay (route index lay).2 (route index lay).1 digits >>= fun ends =>
        leafHashS w lay (route index lay).2 (route index lay).1 ends >>= merkleMsg w index lay) := by
  have hl0 : lay ≠ 0 := fun h => h0 (by rw [h]; rfl)
  simp only [leafHashS_low w lay hl0]
  unfold ClaudeWCT.W9.T3M.layerPairP chainsP merkleMsg merklePrefix
  rw [mkStop, if_neg h0, hL_eq, ← mkFinRange_map_val]
  simp only [List.foldlM_map]
  unfold mkStep mkMessage
  generalize route index lay = pair
  rcases pair with ⟨leaf, tree⟩
  simp only [bind_assoc, pure_bind]
  congr 1
  funext ends
  congr 1
  funext v
  congr 1
  funext root
  simp only [h0, if_false]
  split_ifs <;> rfl
theorem merkleMsg_top (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) :
    merkleMsg w index 0 v = merkleP w index 0 v >>= fun root => pure (LayerMsg.forest root) := by
  rw [merkleP_eq]
  rfl
theorem layerLoop_succ (w : ClaudeWCT.W9.T3M.WBytes) (index n : Nat) (hn : n < 4) (hn0 : n ≠ 0) (msg : LayerMsg) :
    BC.layerLoop w index (n + 1) msg =
      layerHead w index (Fin.ofNat 4 n) msg (fun ends =>
        leafHashS w (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 ends >>=
          fun v => merkleMsg w index (Fin.ofNat 4 n) v >>= BC.layerLoop w index n) := by
  change ClaudeWCT.W9.T3M.layersBC w index (n + 1) msg = _
  rw [ClaudeWCT.W9.T3M.layersBC, layerHead]
  dsimp only
  simp only [hn0, ↓reduceIte]
  split_ifs with hc
  · rfl
  · congr 1
    funext answer
    cases T3.decode (Fin.ofNat 4 n) answer with
    | none => rfl
    | some digits =>
      unfold guardedChainsP ClaudeWCT.W9.T3M.layerGuardedPairP ClaudeWCT.WCT9.lowerGuardedRun
      by_cases hgood : ClaudeWCT.WCT9.lowerRankGood answer
      · simp only [if_pos hgood, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
        have hv : (Fin.ofNat 4 n : Layer).val ≠ 0 := by simpa [Fin.val_ofNat, Nat.mod_eq_of_lt hn] using hn0
        have h := congrArg (fun p => p >>= BC.layerLoop w index n) (layerPairP_eq w index (Fin.ofNat 4 n) hv digits)
        cases n with
        | zero => contradiction
        | succ m => simpa only [bind_assoc, pure_bind, BC.layerLoop] using h
      · simp only [if_neg hgood, bind_assoc, pure_bind]
theorem layerLoop_one (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (msg : LayerMsg) :
    BC.layerLoop w index 1 msg =
      if (ClaudeWCT.W9.T3M.wbcCtr w index 0).toNat ≥ ClaudeWCT.WCT9.verifyWindow then pure none else
      shortHash (ClaudeWCT.W9.T3M.layerEncodingInputP 0 (route index 0).2 (route index 0).1 msg
        (ClaudeWCT.W9.T3M.wbcCtr w index 0) (ClaudeWCT.W9.T3M.wbcHigh w index 0) (ClaudeWCT.W9.T3M.wbcPad w index 0) (ClaudeWCT.W9.T3M.wbcRight w)) >>=
        ClaudeWCT.W9.T3M.topLayerP w index := by
  change ClaudeWCT.W9.T3M.layersBC w index 1 msg = _
  rw [ClaudeWCT.W9.T3M.layersBC]
  rfl
set_option maxRecDepth 10000
theorem mAfter_pair (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer) (u : MachineState)
    (k : Nat) (hk : k < hL lay.val) (v : Digest) (s : MachineState)
    (hs : MAfter w pk lay.val (route index lay).1 u k v s) :
    let other := ClaudeWCT.W9.T3M.wpath w lay (route index lay).1 k
    let pair := if (route index lay).1 / 2 ^ k % 2 = 0 then (v, other) else (other, v)
    DigAt s (mkBlk lay.val (route index lay).1 k) pair.1 ∧ DigAt s (mkBlk lay.val (route index lay).1 k + 48) pair.2 := by
  dsimp only
  have hleaf : (route index lay).1 < 2 ^ hL lay.val := leaf_lt index lay
  obtain ⟨hB16, hBlo, hBhi, -, -⟩ := mkBo_facts lay.val (route index lay).1 k lay.isLt hleaf hk
  obtain ⟨rs0, rs1, -, -, -⟩ := mkP_rd lay.val (route index lay).1 k hk
  have hO := hs.orig
  have hnode := hs.node
  unfold mkCur mkBit at hnode
  unfold mkSibO mkBit at rs0 rs1
  rw [wpath_eq w lay _ _ hleaf]
  unfold mkSibO mkBit
  rcases (show (route index lay).1 / 2 ^ k % 2 = 0 ∨ (route index lay).1 / 2 ^ k % 2 = 1 by omega) with hb | hb
  · rw [hb] at hnode rs0 rs1
    simp only [hb, if_true, sibOff, show (0 : Nat) ≠ 1 by decide +kernel, if_false]
    have hsib := hO.dig (mkBo lay.val (route index lay).1 k + 48) (by omega) (by unfold WX; omega)
      (by simpa using rs0) (by simpa using rs1)
    exact ⟨by simpa using hnode, by simpa [DigAt, dlo, dhi, WIT, mkBlk, Nat.add_assoc] using hsib⟩
  · rw [hb] at hnode rs0 rs1
    simp only [hb, show (1 : Nat) ≠ 0 by decide +kernel, if_false, sibOff, if_true, Nat.add_zero]
    have hsib := hO.dig (mkBo lay.val (route index lay).1 k) (by omega) (by unfold WX; omega)
      (by simpa using rs0) (by simpa using rs1)
    exact ⟨by simpa [DigAt, dlo, dhi, WIT, mkBlk] using hsib, by simpa using hnode⟩
theorem mAfter_pad (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer) (u : MachineState)
    (k : Nat) (hk : k < hL lay.val) (v : Digest) (s : MachineState)
    (hs : MAfter w pk lay.val (route index lay).1 u k v s) (j : Nat) (hj : j = 3 ∨ j = 4 ∨ j = 5) :
    s.getMem (BitVec.ofNat 64 (mkBlk lay.val (route index lay).1 k + 8 * j)) =
      wword w ((mkBlk lay.val (route index lay).1 k - WIT) / 8 + j) := by
  have hleaf : (route index lay).1 < 2 ^ hL lay.val := leaf_lt index lay
  obtain ⟨hB16, hBlo, hBhi, -, -⟩ := mkBo_facts lay.val (route index lay).1 k lay.isLt hleaf hk
  obtain ⟨-, -, rp3, rp4, rp5⟩ := mkP_rd lay.val (route index lay).1 k hk
  have hm : 8 * (mkBo lay.val (route index lay).1 k / 8 + j) = mkBo lay.val (route index lay).1 k + 8 * j := by omega
  have h := hs.orig (mkBo lay.val (route index lay).1 k / 8 + j) (by unfold WX; omega) (by
    rw [hm]
    rcases hj with rfl | rfl | rfl
    · simpa using rp3
    · simpa using rp4
    · simpa using rp5)
  simpa only [mkBlk, WIT, Nat.add_sub_cancel_left, hm, Nat.add_assoc] using h
theorem rowA_mk (index : Nat) (lay : Layer) (h0 : lay.val ≠ 0) :
    rowA (lay.val - 1) (BC.cpIdx index (lay.val - 1)) = mkBlk lay.val (route index lay).1 (mkStop lay.val) := by
  have hcp : BC.cpIdx index (lay.val - 1) = (route index lay).1 := by
    rw [route_fst]; unfold BC.cpIdx; rw [if_neg (by have := lay.isLt; omega), show lay.val - 1 + 1 = lay.val by omega]
    rfl
  rw [hcp]; unfold rowA mkBlk
  rw [mkBo_low _ _ _ h0, show lay.val - 1 + 1 = lay.val by omega, mkStop, if_neg h0]
  omega
theorem mkStop_msg (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer) (h0 : lay.val ≠ 0)
    (u : MachineState) (v : Digest) (s : MachineState)
    (hs : MkStop w pk lay.val (route index lay).1 u v s) :
    BC.MsgAt w index (lay.val - 1) (mkMessage w index lay v) s := by
  have hS : mkStop lay.val = height lay - 1 := by rw [mkStop, if_neg h0, hL_eq]
  have hk : mkStop lay.val < hL lay.val := by fin_cases lay <;> first | contradiction | decide
  have ha : MAfter w pk lay.val (route index lay).1 u (mkStop lay.val) v s := by
    simpa [MkStop, h0] using hs
  have hp := mAfter_pair w pk index lay u _ hk v s ha
  have hpad := mAfter_pad w pk index lay u _ hk v s ha
  rw [← rowA_mk index lay h0] at hp hpad
  rw [hS] at hp
  have hlt : lay.val - 1 < 3 := by omega
  unfold mkMessage
  rw [if_neg h0]
  have h3 : lay.val - 1 ≠ 3 := by omega
  split_ifs with hb
  · simp only [hb, if_true] at hp
    simp only [BC.MsgAt, if_neg h3]
    exact ⟨hlt, hp.1, hp.2, hpad⟩
  · simp only [hb, if_false] at hp
    simp only [BC.MsgAt, if_neg h3]
    exact ⟨hlt, hp.1, hp.2, hpad⟩
theorem mkStop_known_next (n : Nat) (hn : n < 4) (hn0 : n ≠ 0) (u t : MachineState)
    (hu : KnownOK (lfK n) u) (ht : KnownOK (mkLvlK n (mkStop n)) t)
    (keep : ∀ r ∈ mkKeep, t.getReg r = u.getReg r) (h8 : n = 1 → t.getReg .x8 = BitVec.ofNat 64 s3v) :
    KnownOK (BC.preK (n - 1)) t := by
  intro p hp
  interval_cases n
  · contradiction
  all_goals
    simp only [BC.preK, preK, baseK] at hp
    dsimp at hp
    simp only [List.mem_append, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with ⟨hp, hf⟩ | hp
    all_goals
      repeat' first | subst p | rcases hp with hp | hp
      all_goals first
      | exact ht _ (by decide +kernel)
      | (rw [keep _ (by decide +kernel)]; exact hu _ (by decide +kernel))
      | exact h8 rfl
      | contradiction
theorem mkStop_pc (n leaf : Nat) (hn : n < 4) (h0 : n ≠ 0) (hleaf : leaf < 2 ^ hL n) :
    mkEc n leaf (mkStop n) + 1 = trPc (n - 1) leaf := by
  have hbits : mkBits n 0 = hL n := by simp [mkBits, h0]
  have hc := BC.mkBlockCheck_at n 0 leaf hn (by simp [mkNch, h0]) (by rwa [hbits])
  simp only [BC.mkBlockCheck, Bool.and_eq_true] at hc
  have hr : BC.childReturn n leaf = trPc (n - 1) leaf := by simpa [h0] using hc.2
  rw [← hr]
  simp only [mkEc, mkCi, h0, false_and, if_false, mkSh, mkLo, Nat.pow_zero, Nat.div_one,
    hbits, Nat.mod_eq_of_lt hleaf, mkStop, BC.childReturn, Nat.sub_zero]
theorem mkStop_next_lower (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (hidx : index < 2 ^ 31)
    (lay : Layer) (h0 : lay.val ≠ 0) (ends : List Digest) (u : MachineState)
    (hu : LeafOut w pk index lay ends u) (v : Digest) (t : MachineState)
    (ht : MkStop w pk lay.val (route index lay).1 u v t) :
    LayerIn w pk index (lay.val - 1) (mkMessage w index lay v) t := by
  have ha : MAfter w pk lay.val (route index lay).1 u (mkStop lay.val) v t := by
    simpa [MkStop, h0] using ht
  have hleaf := leaf_lt index lay
  have hL0 : lay ≠ 0 := by intro h; apply h0; rw [h]; rfl
  have hk0 : mkStop lay.val ≠ 0 := by fin_cases lay <;> first | contradiction | decide
  have hcp : BC.cpIdx index (lay.val - 1) = (route index lay).1 := by
    rw [route_fst]; unfold BC.cpIdx; rw [if_neg (by have := lay.isLt; omega), show lay.val - 1 + 1 = lay.val by omega]
    rfl
  have he : BC.below (lay.val - 1) = below (lay.val - 1) := by
    fin_cases lay <;> rfl
  have h8 : lay.val = 1 → t.getReg .x8 = BitVec.ofNat 64 s3v := by
    intro h1
    have hl1 : (route index lay).1 < 128 := by rw [h1] at hleaf; simpa [hL] using hleaf
    have hs0 := mkS0_lt _ hl1
    exact ha.x8 h1 (by rw [h1]; show mkS0 1 _ < 6; omega)
  refine ⟨by omega, hidx, ?_, ⟨mkStop_known_next _ lay.isLt h0 u t hu.glob.1 ha.known ha.keep h8, ha.glob.2⟩, ?_, ?_,
    mkStop_msg w pk index lay h0 u v t ht, ?_, fun h => absurd h (by have := lay.isLt; omega), ?_, ha.bufferOrig h0,
    fun h => absurd h (by have := lay.isLt; omega), fun h => absurd h (by have := lay.isLt; omega),
    fun h => absurd h (by have := lay.isLt; omega)⟩
  · rw [ha.pc, mkStop_pc _ _ lay.isLt h0 hleaf, hcp]
    simp only [setupPc, if_neg (show lay.val - 1 ≠ 3 by have := lay.isLt; omega)]
  · rw [show rReg (lay.val - 1) = .x31 by simp [rReg]; omega,
      ha.keep .x31 (by simp [mkKeep]), hu.t5 h0, tree_next index lay hL0, he]
  · intro _
    have htr := tree_lt index lay hidx
    rw [ha.x28 hk0 h0, hu.t5 h0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), tree_next index lay hL0, he]
  · have hle : BC.layerEnd (lay.val - 1) = mkBase lay.val := by
      fin_cases lay <;> first | contradiction | rfl
    refine ha.orig.mono (fun o ho => ?_)
    exact Or.inl ⟨ho.1, by rw [← hle]; exact ho.2⟩
  · intro _
    rw [ha.dstReg]
    congr 1
    have e1 := rowA_mk index lay h0
    have e2 : hL (lay.val - 1 + 1) - 1 = mkStop lay.val := by
      rw [show lay.val - 1 + 1 = lay.val by omega, mkStop, if_neg h0]
    unfold rowWa
    rw [e1, hcp, e2]
    rfl
end SigGolfCandidate.T3M
end
