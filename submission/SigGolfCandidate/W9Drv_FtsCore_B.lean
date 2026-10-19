import SigGolfCandidate.W9Drv_FtsCore_A

set_option Elab.async false


/-! Nested FTS (r1-1): the machine-level FTS phase `W9Drv.ftsN` is track A's padded verifier FTS phase
`ClaudeWCT.W9.T3M.wctP`. The chain part reuses the frontier bridge; the tree part matches `V3.childN` (explicit
nested pads, high-half top node) against `wctCoordP`. -/

section
set_option autoImplicit false
namespace W9Machine
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open OracleComp SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest M)
open ClaudeWCT
theorem chainLow_canonical (index coord child chain step : Nat)
    (hi : index < 2 ^ 31) (hk : coord < 9) (hj : child < 128) (ht : chain < 6) (hs : step < 4) :
    V3.chainLow index coord child chain step = WCT9.ftsChainLow index coord child chain step := by
  rw [chainLow_add _ _ _ _ _ ht hs, chainPrefix_value _ _ _ hk hj]
  unfold WCT9.ftsChainLow
  rw [Nat.mod_eq_of_lt (by omega : chain < 8), Nat.mod_eq_of_lt (by omega : step < 4),
    Nat.mod_eq_of_lt (by omega : coord + 1 < 16), Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hi]
  omega
/-- Witness stack: the V3 step input is the padded verifier's input in either chain format. -/
theorem chainInput_canonical (index coord child chain step : Nat) (a c value : Digest)
    (b : V3.HeaderPad) (hi : index < 2 ^ 31) (hk : coord < 9) (hj : child < 128)
    (ht : chain < 6) (hs : step < 4) :
    V3.chainInput index coord child chain step a b c value =
      ClaudeWCT.W9.T3M.wctChainInputPW index coord child chain step a b c value := by
  unfold ClaudeWCT.W9.T3M.wctChainInputPW
  by_cases hG : WCT9.ftsIsG chain = true
  · rw [if_pos hG]
    change _ = blk4 value (WCT9.ftsChainHeaderP index coord child chain step b) a c
    rw [← wordBytes_wordsOf (V3.chainInput _ _ _ _ _ _ _ _ _) 8
        (chainInput_length _ _ _ _ _ _ _ _ _),
      ← wordBytes_wordsOf (blk4 _ _ _ _) 8 (blk4_length _ _ _ _),
      wordsOf_chainInput, if_pos hG, wordsOf_blk4]
    simp only [dlo, dhi, WCT9.ftsChainHeaderP_low, WCT9.ftsChainHeaderP_high,
      chainLow_canonical _ _ _ _ _ hi hk hj ht hs]
  · rw [if_neg hG]
    change _ = blk4 a (WCT9.ftsChainHeaderP index coord child chain step b) c value
    rw [← wordBytes_wordsOf (V3.chainInput _ _ _ _ _ _ _ _ _) 8
        (chainInput_length _ _ _ _ _ _ _ _ _),
      ← wordBytes_wordsOf (blk4 _ _ _ _) 8 (blk4_length _ _ _ _),
      wordsOf_chainInput, if_neg hG, wordsOf_blk4]
    simp only [dlo, dhi, WCT9.ftsChainHeaderP_low, WCT9.ftsChainHeaderP_high,
      chainLow_canonical _ _ _ _ _ hi hk hj ht hs]
theorem chainP_canonical (index coord child chain start count : Nat) (a c value : Digest)
    (b : V3.HeaderPad) (hi : index < 2 ^ 31) (hk : coord < 9) (hj : child < 128)
    (ht : chain < 6) (hbound : start + count ≤ 4) :
    V3.chainP index coord child chain start count a b c value =
      ClaudeWCT.W9.T3M.wctChainP index coord child chain start count a b c value := by
  induction count generalizing start value with
  | zero => rfl
  | succ count ih =>
    simp only [V3.chainP, ClaudeWCT.W9.T3M.wctChainP, List.range'_succ, List.foldlM_cons]
    rw [chainInput_canonical _ _ _ _ _ _ _ _ _ hi hk hj ht (by omega)]
    congr 1
    funext v
    exact ih (start + 1) v (by omega)
def canonicalChains (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (k : Fin 9) (j : Fin 128) (rank : Fin 666) :
    M (List Digest) :=
  (List.finRange 6).mapM fun t =>
    let d := WCT9.digit rank t
    ClaudeWCT.W9.T3M.wctChainP index k.val j.val t.val (4 - d) d
      (ClaudeWCT.W9.T3M.wcpads w k.val t.val).1
      (ClaudeWCT.W9.T3M.wcHeaderPad w k.val t.val)
      (ClaudeWCT.W9.T3M.wcpads w k.val t.val).2
      (ClaudeWCT.W9.T3M.wreveal w k.val t.val d)
theorem chainProgram_canonical (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (k : Fin 9) (j : Fin 128)
    (rank : Fin 666) (hi : index < 2 ^ 31) :
    V3.chainProgram w index k j rank = canonicalChains w index k j rank := by
  unfold V3.chainProgram canonicalChains
  congr 1
  funext t
  have hd := WCT9.digit_le_four rank t
  rw [chainP_canonical _ _ _ _ _ _ _ _ _ _ hi k.isLt j.isLt t.isLt (by omega)]
  have hb : V3.chainPadB w k.val t.val = ClaudeWCT.W9.T3M.wcHeaderPad w k.val t.val := by
    simp only [V3.chainPadB, ClaudeWCT.W9.T3M.wcHeaderPad,
      V3.chainOffset, V3.regionOffset, ClaudeWCT.W9.T3M.wctChainBlock,
      ClaudeWCT.W9.T3M.regionBase, Nat.add_assoc]
    rw [show ClaudeWCT.W9.T3M.wdig w = W9Machine.wdig w from rfl, W9Machine.wdig_hi]
    congr 2 <;> omega
  rw [hb]
  rfl
end W9Machine
end
section
set_option autoImplicit false
namespace W9Drv
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open W9Machine SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open OracleComp
open SigGolfCandidate.T3 (Digest HashOutput M shortHash header)
open SphincsSecurity (bytesLE bytesLE_length)
theorem nodeHdr_canonical (k : Fin 9) (index heap : Nat) (hp : BitVec 64) :
    V3.nodeHdr k.val index heap hp =
      SigGolfCandidate.T3M.SecurityInputs.withHigh
        (SigGolfCandidate.T3.nodeTweak 3 (ClaudeWCT.WCT9.nodeLayer k.val) index heap) hp := by
  have hk := k.isLt
  have hlow : V3.nodeLow k.val index = 1537 + 65536 * (k.val + 1) + 2 ^ 27 * (index % 2 ^ 31) := by
    unfold V3.nodeLow ClaudeWCT.WCT9.ftsLeafLow
    rw [Nat.mod_eq_of_lt (show k.val + 1 < 16 by omega)]
    simp only [Nat.zero_mod, Nat.zero_mul, Nat.add_zero]
    ring
  rw [show ClaudeWCT.WCT9.nodeLayer k.val = 4 + k.val from rfl]
  unfold V3.nodeHdr SigGolfCandidate.T3M.SecurityInputs.withHigh
  by_cases hn : SigGolfCandidate.T3.FtsNew heap
  · have hm := SigGolfCandidate.T3.ftsNodeWordH_marker hn (4 + k.val - 4) index
    rw [if_pos (show 8 ≤ heap ∧ heap < 128 from hn), SigGolfCandidate.T3.nodeTweak_ftsN (by omega) (by omega) _ hn,
      if_pos (by rw [SigGolfCandidate.T3.append64_toNat]
                 obtain ⟨h8, h128⟩ := hn
                 have h0 : (0#64).toNat = 0 := rfl
                 omega),
      SigGolfCandidate.T3.append64_low]
    congr 1
    unfold SigGolfCandidate.T3.ftsNodeWordH
    rw [hlow, show 4 + k.val - 4 = k.val by omega, Nat.mod_eq_of_lt (show k.val + 1 < 16 by omega)]
    obtain ⟨h8, h128⟩ := hn
    congr 1
    omega
  · rw [if_neg (show ¬ (8 ≤ heap ∧ heap < 128) from hn), SigGolfCandidate.T3.nodeTweak_fts (by omega) (by omega) _ hn,
      if_neg (by rw [SigGolfCandidate.T3.append64_toNat, SigGolfCandidate.T3.ftsNodeWord_toNat]; omega),
      show 4 + k.val - 4 = k.val by omega]
    have hw : BitVec.ofNat 64 (V3.nodeLow k.val index) = SigGolfCandidate.T3.ftsNodeWord k.val index := by
      apply BitVec.eq_of_toNat_eq
      rw [SigGolfCandidate.T3.ftsNodeWord_toNat, BitVec.toNat_ofNat, hlow, Nat.mod_eq_of_lt (show k.val + 1 < 16 by omega)]
      have := Nat.mod_lt index (show 0 < 2 ^ 31 by decide)
      omega
    rw [hw]
theorem nodeInput_canonical (k : Fin 9) (index heap : Nat) (left : Digest) (hp : BitVec 64) (pad right : Digest) :
    shortHash (V3.nodeInput k.val index heap left hp pad right) =
      ClaudeWCT.W9.T3M.wctNodeHashP k.val index heap left hp pad right := by
  unfold V3.nodeInput ClaudeWCT.W9.T3M.wctNodeHashP SigGolfCandidate.T3M.SecurityInputs.nodeInputPH
    SigGolfCandidate.T3M.SecurityInputs.block4
  rw [nodeHdr_canonical]
theorem leafInput_canonical (k index j : Nat) (pad : Digest) (ends : List Digest) (h : ends.length = 6) :
    shortHash (V3.leafInput k index j pad ends) = ClaudeWCT.WCT9.leafHashP index k j pad ends := by
  match ends, h with
  | [e0, e1, e2, e3, e4, e5], _ =>
    simp only [V3.leafInput, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl,
      List.flatMap_cons, List.flatMap_nil, V3.leafFields, ClaudeWCT.WCT9.leafHashP, ClaudeWCT.WCT9.leafInputP,
      List.drop_succ_cons, List.drop_zero, List.append_nil, List.append_assoc]
    rfl
theorem heap_eq (j l : Nat) (hj : j < 128) (hl : l < 6) :
    (128 + j) / 2 ^ (l + 1) = 2 ^ (6 - l) + j / 2 ^ (l + 1) := by
  interval_cases l <;> norm_num [Nat.add_div] <;> omega
theorem finRange_map_val (n : Nat) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp
theorem topInput_canonical (k : Fin 9) (index j : Nat) (left pad right : Digest) :
    V3.nodeInput k.val index ((128 + j) / 2 ^ 6) left 0 pad right =
      ClaudeWCT.WCT9.wctTopInput k.val index (2 + j / 2 ^ 6) left pad right := by
  have hh : (128 + j) / 2 ^ 6 = 2 + j / 2 ^ 6 := by omega
  unfold V3.nodeInput ClaudeWCT.WCT9.wctTopInput ClaudeWCT.WCT9.wctNodeHeader
  rw [hh, nodeHdr_canonical, SigGolfCandidate.T3M.SecurityInputs.withHigh_nodeTweak_zero]
theorem hashHi_top (k : Fin 9) (index j : Nat) (left pad right : Digest) :
    V3.hashHi (V3.nodeInput k.val index ((128 + j) / 2 ^ 6) left 0 pad right) =
      ClaudeWCT.WCT9.wctTopHash k.val index (2 + j / 2 ^ 6) left pad right := by
  rw [topInput_canonical]
  rfl
/-- Pairing stage 1: the legacy padded verifier reads coordinate 0's level-5 sibling and pad from `legacySib0` /
`legacyPad0` (that window left the witness), so the legacy machine-view identities exclude `k = 0, l = 5`. -/
theorem sibling_eq (w : ClaudeWCT.W9.T3M.WBytes) (k j l : Nat) (hl : l < 6) (h05 : k ≠ 0 ∨ l ≠ 5) :
    V3.sibling w k j l = ClaudeWCT.W9.T3M.wsib w k j l := by
  unfold V3.sibling ClaudeWCT.W9.T3M.wsib ClaudeWCT.W9.T3M.authSibOff V3.sibOff V3.blkOff
  rw [if_pos hl, if_pos hl, if_neg (show ¬ (k = 0 ∧ l = 5) by omega)]
  have hb : j / 2 ^ l % 2 = 0 ∨ j / 2 ^ l % 2 = 1 := by omega
  by_cases h5 : l < 5
  · rw [if_pos h5]
    rcases hb with hb | hb <;>
      simp only [hb, SigGolfCandidate.T3M.sibOff, V3.regionOffset, ClaudeWCT.W9.T3M.regionBase] <;> rfl
  · rw [if_neg h5, show l = 5 by omega, ClaudeWCT.W9.T3M.authBase_five]
    rw [show l = 5 by omega] at hb
    rcases hb with hb | hb <;>
      simp only [hb, SigGolfCandidate.T3M.sibOff, V3.regionOffset, ClaudeWCT.W9.T3M.regionBase] <;> rfl
theorem nodePad_eq (w : ClaudeWCT.W9.T3M.WBytes) (k j l : Nat) (hl : l < 6) (h05 : k ≠ 0 ∨ l ≠ 5) :
    V3.nodePad w k j l = ClaudeWCT.W9.T3M.wmpad w k j l := by
  unfold V3.nodePad ClaudeWCT.W9.T3M.wmpad ClaudeWCT.W9.T3M.authPadOff V3.padOff V3.blkOff
  rw [if_neg (show ¬ (k = 0 ∧ l = 5) by omega)]
  by_cases h5 : l < 5
  · rw [if_pos h5]; rfl
  · rw [if_neg h5, show l = 5 by omega, ClaudeWCT.W9.T3M.authBase_five]; rfl
theorem nodeHPad_eq (w : ClaudeWCT.W9.T3M.WBytes) (k j l : Nat) (hl : l < 5) :
    V3.nodeHPad w k j l = ClaudeWCT.W9.T3M.wmhpad w k j l := by
  unfold V3.nodeHPad ClaudeWCT.W9.T3M.wmhpad V3.nodeTw V3.blkOff
  rw [if_pos hl]
  rfl
theorem topOther_eq (w : ClaudeWCT.W9.T3M.WBytes) (k j : Nat) :
    V3.topOther w k j = ClaudeWCT.W9.T3M.wsib w k j 6 := by
  unfold V3.topOther V3.topOtherOff ClaudeWCT.W9.T3M.wsib ClaudeWCT.W9.T3M.topSlot
  rw [if_neg (show ¬ (6 < 6) by decide), show (2 : Nat) ^ 6 = 64 by rfl]
  split_ifs <;> rfl
/-- Monadic congruence after a `mapM`: the continuations need only agree on lists of the right length. -/
theorem mapM_bind_len {α γ β : Type} (f : γ → M α) :
    ∀ (xs : List γ) (g h : List α → M β), (∀ l : List α, l.length = xs.length → g l = h l) →
      (xs.mapM f >>= g) = (xs.mapM f >>= h)
  | [], g, h, H => by simp only [List.mapM_nil, pure_bind]; exact H [] rfl
  | x :: xs, g, h, H => by
    simp only [List.mapM_cons, bind_assoc, pure_bind]
    congr 1
    funext a
    exact mapM_bind_len f xs (fun l => g (a :: l)) (fun l => h (a :: l))
      (fun l hl => H (a :: l) (by simp [hl]))
theorem fold5_canonical (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (k : Fin 9) (j : Fin 128) (leaf : Digest) :
    (List.range 5).foldlM (fun value level =>
        shortHash (V3.nodeInput k.val index ((128 + j.val) / 2 ^ (level + 1))
          (if j.val / 2 ^ level % 2 = 0 then value else V3.sibling w k.val j.val level)
          (V3.nodeHPad w k.val j.val level) (V3.nodePad w k.val j.val level)
          (if j.val / 2 ^ level % 2 = 0 then V3.sibling w k.val j.val level else value))) leaf =
      (List.finRange 5).foldlM (fun value level => do
        let other := ClaudeWCT.W9.T3M.wsib w k.val j.val level.val
        let pair := if j.val / 2 ^ level.val % 2 = 0 then (value, other) else (other, value)
        ClaudeWCT.W9.T3M.wctNodeHashP k.val index (2 ^ (6 - level.val) + j.val / 2 ^ (level.val + 1))
          pair.1 (ClaudeWCT.W9.T3M.wmhpad w k.val j.val level.val) (ClaudeWCT.W9.T3M.wmpad w k.val j.val level.val)
          pair.2) leaf := by
  rw [← finRange_map_val (n := 5), List.foldlM_map]
  congr 1
  funext value level
  have hl := level.isLt
  rw [heap_eq j.val level.val j.isLt (by omega), nodeInput_canonical k index _ _ _ _ _,
    sibling_eq w k.val j.val level.val (by omega) (Or.inr (by omega)), nodeHPad_eq w k.val j.val level.val hl,
    nodePad_eq w k.val j.val level.val (by omega) (Or.inr (by omega))]
  by_cases hb : j.val / 2 ^ level.val % 2 = 0 <;> simp [hb]
theorem coordN_canonical (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (k : Fin 9) (j : Fin 128)
    (rank : Fin 563) (prev : Digest × Digest) (hi : index < 2 ^ 31) (hk0 : k.val ≠ 0) :
    coordN w index k j rank prev = ClaudeWCT.W9.T3M.wctCoordP w index k j rank prev := by
  unfold coordN ClaudeWCT.W9.T3M.wctCoordP N600.program
  rw [chainProgram_canonical w index k j (N600.embed rank) hi,
    (show N600.embed = ClaudeWCT.WCT9.embed from N600.embed_eq_c1)]
  unfold canonicalChains
  apply mapM_bind_len
  intro ends hends
  simp only [List.length_finRange] at hends
  unfold V3.childN
  rw [leafInput_canonical _ _ _ _ _ hends]
  simp only [bind_assoc, pure_bind]
  congr 1
  funext leaf
  rw [fold5_canonical]
  congr 1
  funext value
  rw [hashHi_top, sibling_eq w k.val j.val 5 (by decide) (Or.inl hk0), topOther_eq]
  have hb5 : j.val / 32 % 2 = 0 ∨ j.val / 32 % 2 = 1 := by omega
  have hb6 : j.val / 64 % 2 = 0 ∨ j.val / 64 % 2 = 1 := by omega
  rcases hb5 with hb5 | hb5 <;> rcases hb6 with hb6 | hb6 <;>
    simp [hb5, hb6, show (2 : Nat) ^ 5 = 32 by rfl, show (2 : Nat) ^ 6 = 64 by rfl]
/- Pairing stage 1: `ftsStartW_eq` / `prevOf_eq` / `stepN_eq` / `ftsN_eq` (legacy Frozen-layout machine FTS = legacy
padded verifier FTS) were removed: the legacy machine reads coordinate 0's level-5 window at `regionAddr 0 + 832`,
which the paired witness no longer carries (legacy `wsib`/`wmpad` read `legacySib0`/`legacyPad0` instead). They had
no users; the live route is `SharedCoord`/`SharedCanonical` below. -/
end W9Drv
end

/-! Shared-forest dispatch prototype; not yet installed in Frozen.image. -/
namespace W9Drv.SharedDispatch
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
def words (k : Nat) : List (BitVec 32) :=
  [[0x7f87213,0x1421f93,0xffefb3,0x721b93,0x1cb8bb3,0x585713,0x277733,0x700e7],
    [0xe81213,0x1b27233,0x803803,0x1886833,0x6787b3,0xf26fb3,0xc25b93,0x1db8bb3,0xcb040413,0x585713,0x277733,0x700e7],
    [0x7f87213,0x6787b3,0x1421f93,0xffefb3,0x721b93,0x1cb8bb3,0xcb040413,0x1185713,0x277733,0x700e7],
    [0xe81213,0x1b27233,0x6787b3,0xf26fb3,0xc25b93,0x1db8bb3,0xcb040413,0x1d85713,0x277733,0x700e7],
    [0x1003803,0x1886833,0x7f87213,0x6787b3,0x1421f93,0xffefb3,0x721b93,0x1cb8bb3,0xcb040413,0x585713,0x277733,0x700e7],
    [0xe81213,0x1b27233,0x6787b3,0xf26fb3,0xc25b93,0x1db8bb3,0xcb040413,0x1185713,0x277733,0x700e7],
    [0x1d85713,0x277733,0x7f8f213,0x6787b3,0x1421f93,0xffefb3,0x721b93,0x1cb8bb3,0xcb040413,0x700e7],
    [0x188e8b3,0xe89213,0x1b27233,0x6787b3,0xf26fb3,0xc25b93,0x1db8bb3,0xcb040413,0x58d713,0x277733,0x118d213,0x700e7],
    [0x227733,0x1b27233,0x6787b3,0xf26fb3,0xf104bc83,0xc25b93,0x19b8bb3,0xcb040413,0x700e7]].getD k []
def start (k : Nat) : Nat := [89,171,257,341,425,511,595,679,765].getD k 849
def length (k : Nat) : Nat := [8,12,10,10,12,10,10,12,9].getD k 0
def first (k : Nat) : Bool := decide (k < 8 ∧ k % 2 = 0)
def rankPosition (k : Nat) : Nat := [13,13,25,37,13,25,37,13,25].getD k 13
def result (k : Nat) : Result :=
  let fresh : E := if k = 1 then .ld (.c 8) else .ld (.c 16)
  let padded := mkBin .or fresh (.reg .x24)
  let lastPadded := mkBin .or (.reg .x17) (.reg .x24)
  let childDig : E := if k = 4 then padded else if k = 7 then lastPadded
    else if k ≥ 6 then .reg .x17 else .reg .x16
  let rankDig : E := if k = 1 ∨ k = 4 then padded else if k = 7 then lastPadded
    else if k ≥ 7 then .reg .x17 else .reg .x16
  -- Coordinate 8 (dispatch hoist): `tp` already holds `a7 >>> 17` (coordinate 7's word 689), so the child and rank
  -- fields are masked directly out of `tp`.
  let child := if first k then mkBin .and childDig (.c 127)
    else mkBin .and (if k = 8 then .reg .x4
      else mkBin .sll childDig (.c 14)) (.reg .x27)
  let node := if k = 0 then .reg .x15 else mkAdd (.reg .x15) (.reg .x6)
  let header := mkBin .or (if first k then mkBin .sll child (.c 20) else child) node
  let singletonBase := .ld (addC (.reg .x9) (BitVec.ofNat 64 (2^64 - 240)))
  let childPC := mkAdd (if first k then mkBin .sll child (.c 7)
    else mkBin .srl child (.c 12)) (if first k then .reg .x28
      else if k = 8 then singletonBase else .reg .x29)
  let field := mkBin .and (if k = 8 then .reg .x4
    else mkBin .srl rankDig (.c (BitVec.ofNat 64 (rankPosition k - 8)))) (.reg .x2)
  let regs := if k = 1 ∨ k = 4 then RegFile.init.set .x16 padded else RegFile.init
  let regs := if k = 7 then regs.set .x17 lastPadded else regs
  let regs := if k = 8 then regs.set .x25 singletonBase else regs
  -- Coordinate 7 ends with `srli tp,a7,17` (word 689): its `tp` is the hoisted shift, not the child.
  let regs := (regs.set .x4 (if k = 7 then mkBin .srl lastPadded (.c 17) else child)).set .x31 header
  let regs := if k = 0 then regs else (regs.set .x15 node).set .x8
    (addC (.reg .x8) (BitVec.ofNat 64 (2^64 - 848)))
  let regs := ((regs.set .x23 childPC).set .x14 field).set .x1 (.c (pcOf (start k + length k)))
  ⟨⟨regs, [], if k = 8 then [.valid ⟨some (.reg .x9), BitVec.ofNat 64 (2^64 - 240)⟩ 8] else []⟩,
    mkBin .and field (.c (~~~1#64)), .jump, length k, length k⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : ∀ k : Fin 9,
    rOK (symRun {} (words k.val) (pcOf (start k.val)) (length k.val)) (result k.val) = true := by
  intro k; fin_cases k <;> decide +kernel
theorem total_dispatch_words : ((List.range 9).map length).sum = 93 := by decide
theorem linked (k : Fin 9) : sliceChecked (start k.val) (words k.val) = true := by
  fin_cases k <;> decide +kernel

end W9Drv.SharedDispatch

namespace W9Drv.SharedDispatch
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.Research
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def childWord (k : Nat) : Nat := [0,0,1,1,2,2,3,3,3].getD k 0
def childPos (k : Nat) : Nat := [0,6,0,6,0,6,0,6,37].getD k 0
def childOfWord (k : Fin 9) (x : Word) : Word := (x >>> childPos k.val) &&& 127#64

def childDig (k : Nat) : E :=
  let fresh : E := if k = 1 then .ld (.c 8) else .ld (.c 16)
  let padded := mkBin .or fresh (.reg .x24)
  let lastPadded := mkBin .or (.reg .x17) (.reg .x24)
  if k = 4 then padded else if k = 7 then lastPadded
    else if k ≥ 6 then .reg .x17 else .reg .x16

def rankDig (k : Nat) : E :=
  let fresh : E := if k = 1 then .ld (.c 8) else .ld (.c 16)
  let padded := mkBin .or fresh (.reg .x24)
  let lastPadded := mkBin .or (.reg .x17) (.reg .x24)
  if k = 1 ∨ k = 4 then padded else if k = 7 then lastPadded
    else if k ≥ 7 then .reg .x17 else .reg .x16

theorem child_field (a : HashOutput) (k : Fin 9) :
    childOfWord k (a.extractLsb' (64 * childWord k.val) 64) =
      BitVec.ofNat 64 (SharedForest.rawChildFromOutput a k).val := by
  apply BitVec.eq_of_toNat_eq
  fin_cases k <;> simp [childOfWord, childPos, childWord, SharedForest.rawChildFromOutput,
    SharedForest.rawChildBase, BitVec.toNat_and, BitVec.toNat_ushiftRight,
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, W9Drv.nat_and127,
    BitVec.toNat_ofNat] <;> omega

theorem child_pad (k : Fin 9) (x : Word) :
    childOfWord k (x ||| SharedCoord.rankPad) = childOfWord k x := by
  fin_cases k <;> simp only [childOfWord, childPos, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some] <;>
    apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;> interval_cases i <;> simp [SharedCoord.rankPad]

theorem childDig_eval (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput)
    (k : Fin 9) (pairs : List (Digest × Digest)) (u : MachineState)
    (hu : SharedCoord.Pre pk w a k.val pairs u) :
    (childDig k.val).eval u = a.extractLsb' (64 * childWord k.val) 64 |||
      (if k.val = 6 then 0 else SharedCoord.rankPad) := by
  have hd := hu.digest (childWord k.val) (by fin_cases k <;> decide)
  have hc := hu.cached
  have h3 := hu.cached3
  have hp := hu.jt
  fin_cases k <;> simp_all [childDig, childWord, cachedWord, mkBin_eval, E.eval, BinOp.eval]

theorem rankDig_eval (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput)
    (k : Fin 9) (pairs : List (Digest × Digest)) (u : MachineState)
    (hu : SharedCoord.Pre pk w a k.val pairs u) :
    (rankDig k.val).eval u = a.extractLsb' (64 * W9Drv.digWord k.val) 64 ||| SharedCoord.rankPad := by
  have hd := hu.digest (W9Drv.digWord k.val) (by fin_cases k <;> decide)
  have hc := hu.cached
  have h3 := hu.cached3
  have hp := hu.jt
  fin_cases k <;> simp_all [rankDig, W9Drv.digWord, cachedWord, mkBin_eval, E.eval, BinOp.eval]

theorem raw_eval (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput)
    (k : Fin 9) (pairs : List (Digest × Digest)) (u : MachineState)
    (hu : SharedCoord.Pre pk w a k.val pairs u) :
    childOfWord k ((childDig k.val).eval u) = BitVec.ofNat 64 (SharedForest.rawChildFromOutput a k).val := by
  rw [childDig_eval pk w a k pairs u hu]
  by_cases h : k.val = 6
  · rw [if_pos h]
    simpa using (child_field a k)
  · rw [if_neg h, child_pad, child_field]

theorem packed_pair (x : Word) :
    (x <<< 14) &&& 0x7f00000#64 = ((x >>> 6) &&& 127#64) <<< 20 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp

theorem packed_singleton (x : Word) :
    (x >>> 17) &&& 0x7f00000#64 = ((x >>> 37) &&& 127#64) <<< 20 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp

theorem packed_shr (x : Word) :
    (((x &&& 127#64) <<< 20) >>> 12) = (x &&& 127#64) <<< 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp

theorem mem (k : Fin 9) (u : MachineState) (addr : Word) :
    ((result k.val).toState u).getMem addr = u.getMem addr := by
  fin_cases k <;> rfl

theorem keep (k : Fin 9) (u : MachineState) (r : Reg)
    (hr : r ∉ [.x1,.x4,.x8,.x14,.x15,.x16,.x17,.x23,.x25,.x31]) :
    ((result k.val).toState u).getReg r = u.getReg r := by
  rw [Result.toState_getReg]
  fin_cases k <;> cases r <;> first | exact False.elim (hr (by decide)) | rfl

/-- Dispatch hoist: coordinate 7's dispatcher ends with `srli tp,a7,17` (word 689) after `or a7,a7,s8`, so it leaves
coordinate 8's shared shift in `tp`. -/
theorem hoist_seven (u : MachineState) :
    ((result 7).toState u).getReg .x4 = ((result 7).toState u).getReg .x17 >>> 17 := by
  rw [Result.toState_getReg, Result.toState_getReg]
  rfl

theorem node (k : Fin 9) (u : MachineState) :
    ((result k.val).toState u).getReg .x15 =
      (if k.val = 0 then u.getReg .x15 else u.getReg .x15 + u.getReg .x6) := by
  fin_cases k <;> rfl

theorem nodeWord (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (k : Fin 9)
    (pairs : List (Digest × Digest)) (u : MachineState) (hu : SharedCoord.Pre pk w a k.val pairs u) :
    ((result k.val).toState u).getReg .x15 = BitVec.ofNat 64 (V3.nodeLow k.val (idxOf a)) := by
  have hi : idxOf a < 2 ^ 31 := ClaudeWCT.WCT9.digestIndex_lt a
  rw [node, nodeLow_value _ _ k.isLt hi]
  by_cases hk0 : k.val = 0
  · rw [if_pos hk0, hu.nodeReg]
    apply congrArg (BitVec.ofNat 64)
    omega
  · rw [if_neg hk0, hu.nodeReg, hu.coordStep, show (65536 : BitVec 64) = BitVec.ofNat 64 65536 from rfl,
      ofNat_add_ofNat]
    apply congrArg (BitVec.ofNat 64)
    generalize idxOf a = x
    have := k.isLt
    omega

end W9Drv.SharedDispatch

namespace W9Drv.SharedDispatch
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.Research
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The packed child expression of dispatcher `k` (the `child` of `result k`): `childDig & 127` (A), or the raw child
moved to bits 20..26 (B, C). Coordinate 8 masks the hoisted `tp = a7 >>> 17`. -/
def childE (k : Nat) : E :=
  if first k then mkBin .and (childDig k) (.c 127)
  else mkBin .and (if k = 8 then .reg .x4 else mkBin .sll (childDig k) (.c 14)) (.reg .x27)

theorem packed_result (k : Fin 9) (u : MachineState)
    (hm : u.getReg .x27 = BitVec.ofNat 64 0x7f00000)
    (hx4 : k.val = 8 → u.getReg .x4 = u.getReg .x17 >>> 17) :
    (childE k.val).eval u =
      if first k.val then childOfWord k ((childDig k.val).eval u)
      else childOfWord k ((childDig k.val).eval u) <<< 20 := by
  fin_cases k
  · change ((childDig 0).eval u) &&& 127#64 = (((childDig 0).eval u) >>> 0) &&& 127#64
    simp
  · change (((childDig 1).eval u) <<< 14) &&& u.getReg .x27 = ((((childDig 1).eval u) >>> 6) &&& 127#64) <<< 20
    rw [hm]
    exact packed_pair _
  · change ((childDig 2).eval u) &&& 127#64 = (((childDig 2).eval u) >>> 0) &&& 127#64
    simp
  · change (((childDig 3).eval u) <<< 14) &&& u.getReg .x27 = ((((childDig 3).eval u) >>> 6) &&& 127#64) <<< 20
    rw [hm]
    exact packed_pair _
  · change ((childDig 4).eval u) &&& 127#64 = (((childDig 4).eval u) >>> 0) &&& 127#64
    simp
  · change (((childDig 5).eval u) <<< 14) &&& u.getReg .x27 = ((((childDig 5).eval u) >>> 6) &&& 127#64) <<< 20
    rw [hm]
    exact packed_pair _
  · change ((childDig 6).eval u) &&& 127#64 = (((childDig 6).eval u) >>> 0) &&& 127#64
    simp
  · change (((childDig 7).eval u) <<< 14) &&& u.getReg .x27 = ((((childDig 7).eval u) >>> 6) &&& 127#64) <<< 20
    rw [hm]
    exact packed_pair _
  · change u.getReg .x4 &&& u.getReg .x27 = ((u.getReg .x17 >>> 37) &&& 127#64) <<< 20
    rw [hm, hx4 rfl]
    exact packed_singleton _

theorem leaf (k : Fin 9) (u : MachineState)
    (hm : u.getReg .x27 = BitVec.ofNat 64 0x7f00000)
    (hx4 : k.val = 8 → u.getReg .x4 = u.getReg .x17 >>> 17) :
    ((result k.val).toState u).getReg .x31 =
      (childOfWord k ((childDig k.val).eval u) <<< 20) |||
        ((result k.val).toState u).getReg .x15 := by
  have he : ((result k.val).toState u).getReg .x31 =
      (if first k.val then (childE k.val).eval u <<< 20
       else (childE k.val).eval u) |||
        ((result k.val).toState u).getReg .x15 := by
    fin_cases k <;> rfl
  rw [he, packed_result k u hm hx4]
  cases first k.val <;> rfl

theorem child_pc (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (k : Fin 9)
    (pairs : List (Digest × Digest)) (u : MachineState) (hu : SharedCoord.Pre pk w a k.val pairs u) :
    ((result k.val).toState u).getReg .x23 =
      pcOf ((SharedLayout.layout k).childWord (SharedForest.rawChildFromOutput a k)) := by
  have hraw := raw_eval pk w a k pairs u hu
  have hm := hu.childMask
  have hA := hu.aTable
  have hB := hu.childBlock
  have hC := hu.singletonTable
  have h9 := hu.pairPtr
  have hj := (SharedForest.rawChildFromOutput a k).isLt
  have hpc : ((result k.val).toState u).getReg .x23 =
      (childOfWord k ((childDig k.val).eval u) <<< (if first k.val then 7 else 8)) +
      (if first k.val then u.getReg .x28 else if k.val = 8 then
        u.getMem (BitVec.ofNat 64 (TOPB9 - 240)) else u.getReg .x29) := by
    have he : ((result k.val).toState u).getReg .x23 =
        (if first k.val then (childE k.val).eval u <<< 7
         else (childE k.val).eval u >>> 12) +
        (if first k.val then u.getReg .x28 else if k.val = 8 then
          u.getMem (u.getReg .x9 + BitVec.ofNat 64 (2^64 - 240)) else u.getReg .x29) := by
      fin_cases k <;> rfl
    rw [he, packed_result k u hm hu.hoist, h9]
    have ha : BitVec.ofNat 64 TOPB9 + BitVec.ofNat 64 (2^64 - 240) =
        BitVec.ofNat 64 (TOPB9 - 240) := by decide +kernel
    rw [ha]
    cases first k.val
    · simp only [Bool.false_eq_true, ↓reduceIte, childOfWord, packed_shr]
    · rfl
  rw [hpc, hraw, hA, hB, hC]
  generalize SharedForest.rawChildFromOutput a k = j
  have hbound := j.isLt
  apply BitVec.eq_of_toNat_eq
  fin_cases k <;>
    norm_num [SharedLayout.layout, SharedLayout.childWord, first, BitVec.toNat_add,
      BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, pcOf] <;> omega

end W9Drv.SharedDispatch

namespace W9Drv.SharedDispatch
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.Research
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def chainEntryState (k : Fin 9) (rank : Fin 563) (u : MachineState) : MachineState :=
  { (result k.val).toState u with
    pc := pcOf ((SharedLayout.layout k).chainWord (N600.embed rank)) }

theorem chain_pre (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (k : Fin 9)
    (rank : Fin 563) (pairs : List (Digest × Digest)) (u : MachineState)
    (hu : SharedCoord.Pre pk w a k.val pairs u) :
    N600.Pre (SharedLayout.layout k) (SharedV3.viewW w k.val u) (idxOf a) k
      (SharedForest.rawChildFromOutput a k) rank (chainEntryState k rank u) := by
  have hm (addr : Word) : (chainEntryState k rank u).getMem addr = u.getMem addr := rfl
  have hr (r : Reg) (h : r ∉ [.x1,.x4,.x8,.x14,.x15,.x16,.x17,.x23,.x25,.x31]) :
      (chainEntryState k rank u).getReg r = u.getReg r := keep k u r h
  have hc := raw_eval pk w a k pairs u hu
  have hi : idxOf a < 2^31 := ClaudeWCT.WCT9.digestIndex_lt a
  have hj := (SharedForest.rawChildFromOutput a k).isLt
  have hnode := nodeWord pk w a k pairs u hu
  refine {
    indexBound := hi
    pc := rfl
    baseReg := ?_
    leafWord := ?_
    nodeWord := hnode
    hashMode := (hr .x5 (by decide)).trans (hu.glob.1 (.x5, 0) (by simp [baseK]))
    stepOne := (hr .x7 (by decide)).trans hu.stepOne
    stepTwo := (hr .x13 (by decide)).trans hu.stepTwo
    hashLen := (hr .x11 (by decide)).trans hu.hashLen
    childPC := child_pc pk w a k pairs u hu
    returnPC := ?_
    heaps := ?_
    witness := by
      intro off ho h8
      rw [hm]
      have hk := k.isLt
      have hr8 := V3.regionOffset_mod k.val
      have hrl := V3.regionOffset_le k.val
      rw [SharedV3.view_word w k.val u _ (by omega) (by unfold V3.regionOffset; omega)]
      by_cases hh : SharedV3.isHand off
      · rw [if_pos ⟨by omega, by rw [Nat.add_sub_cancel_left]; exact hh⟩]
        congr 2
        base0; unfold coordinateBase V3.regionOffset
        omega
      · rw [if_neg (fun h => hh (by rw [Nat.add_sub_cancel_left] at h; exact h.2))]
        have hw := hu.coords k.val (Nat.le_refl _) (by omega) off ho h8 (by omega)
          (fun _ => by simpa only [SharedCoord.isHand, if_neg (by omega : k.val ≠ 9)] using hh)
        have he : regionAddr k.val + off - 0x1020 = V3.regionOffset k.val + off := by
          unfold regionAddr V3.regionOffset; omega
        have hb : Chain.base (SharedLayout.layout k) k + off = regionAddr k.val + off := by
          base0; unfold coordinateBase regionAddr; omega
        rw [hb]
        simpa only [W9Machine.OrigW, he] using hw }
  · change ((result k.val).toState u).getReg .x8 = _
    have hb := hu.baseReg
    fin_cases k <;> simp [result, Result.toState_getReg, RegFile.get, RegFile.set, RegFile.init,
      addC_eval, E.eval, hb, W9Machine.Frozen.base_eq, W9Machine.SharedLayout.base_eq, coordinateBase]
  · change ((result k.val).toState u).getReg .x31 = _
    rw [leaf k u hu.childMask hu.hoist, hc, hnode]
    exact W9Drv.leafLow_or _ _ _ k.isLt hj hi
  · change ((result k.val).toState u).getReg .x1 = _
    fin_cases k <;> rfl
  · intro h h2 h7
    exact (hr (Child.heapReg h) (by interval_cases h <;> decide)).trans (hu.heaps h h2 h7)

end W9Drv.SharedDispatch


/-! Canonical injection conditions for the shared-path arbitrary-witness source.
The serializer/expander must establish these concrete memory readouts. -/


namespace W9Drv.SharedDispatch
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.Research
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rankOfWord (k : Fin 9) (x : Word) : Word := (x >>> rankPosition k.val) &&& 1023#64

theorem rank_field (a : HashOutput) (k : Fin 9) :
    rankOfWord k (a.extractLsb' (64 * W9Drv.digWord k.val) 64) =
      BitVec.ofNat 64 (SharedForest.rawForestRank a k.val) := by
  apply BitVec.eq_of_toNat_eq
  fin_cases k <;> simp [rankOfWord, rankPosition, W9Drv.digWord, SharedForest.rawForestRank,
    SharedForest.rankBase, BitVec.toNat_and, BitVec.toNat_ushiftRight,
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, W9Drv.nat_and1023,
    BitVec.toNat_ofNat] <;> omega

theorem padded_field (p : Nat) (hp : p = 13 ∨ p = 25 ∨ p = 37) (x : Word) :
    ((x ||| SharedCoord.rankPad) >>> (p - 8)) &&& 0xfff00#64 =
      (((x >>> p) &&& 1023#64) <<< 8) ||| 0xc0000#64 := by
  rcases hp with rfl | rfl | rfl <;>
    apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;> interval_cases i <;>
    simp [SharedCoord.rankPad]

theorem padded_low (x : Word) :
    (x &&& 0xfff00#64) &&& ~~~1#64 = x &&& 0xfff00#64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp

/-- The dispatch target (rank field) of coordinate `k`; coordinate 8 masks the hoisted `tp = a7 >>> 17`. -/
theorem pc_shift (k : Fin 9) (u : MachineState)
    (hx4 : k.val = 8 → u.getReg .x4 = u.getReg .x17 >>> 17) :
    (result k.val).pc.eval u =
      (((rankDig k.val).eval u >>> (rankPosition k.val - 8)) &&& u.getReg .x2) &&& ~~~1#64 := by
  fin_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · change (u.getReg .x4 &&& u.getReg .x2) &&& ~~~1#64 =
      ((u.getReg .x17 >>> 17) &&& u.getReg .x2) &&& ~~~1#64
    rw [hx4 rfl]

theorem pc_eval (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (k : Fin 9)
    (pairs : List (Digest × Digest)) (u : MachineState) (hu : SharedCoord.Pre pk w a k.val pairs u) :
    (result k.val).pc.eval u = pcOf (slotStart + 64 * SharedForest.rawForestRank a k.val) := by
  rw [pc_shift k u hu.hoist, hu.mask, show BitVec.ofNat 64 0xfff00 = 0xfff00#64 from rfl, padded_low,
    rankDig_eval pk w a k pairs u hu,
    padded_field _ (by fin_cases k <;> decide)]
  change (rankOfWord k (a.extractLsb' (64 * W9Drv.digWord k.val) 64) <<< 8) ||| 0xc0000#64 = _
  rw [rank_field]
  have hr : SharedForest.rawForestRank a k.val < 1024 := Nat.mod_lt _ (by decide)
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    pcOf, slotStart]
  have hlow : SharedForest.rawForestRank a k.val * 2 ^ 8 < 2 ^ 18 := by omega
  rw [Nat.mod_eq_of_lt (by omega : SharedForest.rawForestRank a k.val < 2^64),
    Nat.mod_eq_of_lt (by omega : SharedForest.rawForestRank a k.val * 2^8 < 2^64)]
  have hor : (SharedForest.rawForestRank a k.val * 2^8) ||| 786432 =
      786432 + SharedForest.rawForestRank a k.val * 2^8 := by
    rw [Nat.or_comm, show 786432 = 3 <<< 18 from rfl,
      ← Nat.shiftLeft_add_eq_or_of_lt hlow]
  rw [hor, Nat.mod_eq_of_lt (by omega)]
  omega

end W9Drv.SharedDispatch
namespace W9Drv.SharedCoord
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest HashOutput M)
open SigGolfCandidate.Research
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem core_good (chains : ∀ k : Fin 9, N600.AllGood (P := P) (SharedLayout.layout k))
    (childs : ∀ (k : Fin 9) (raw : Fin 128), SharedChild.Good (P := P) (SharedLayout.layout k) k raw)
    (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (k : Fin 9) (raw : Fin 128) (rank : Fin 563)
    (v u : MachineState) (padL padR : Digest) (N C A : Nat) (Q : Prop)
    (K : Digest → OracleComp HashSpec Obs)
    (hu : N600.Pre (SharedLayout.layout k) (SharedV3.viewW w k.val v) index k raw rank u)
    (hL : DigAt v (0x1020 + V3.regionOffset k.val + 672) padL)
    (hR : DigAt v (0x1020 + V3.regionOffset k.val + 160) padR)
    (hnext : ∀ ends entry, Chain.Post (SharedLayout.layout k) (SharedV3.viewW w k.val v)
        index k raw u ends entry →
      ∀ computed t, SharedChild.Post (SharedLayout.layout k) k raw entry computed t →
        GoodQFor (P := P) Frozen.image t N C Q A (K computed)) :
    GoodQFor (P := P) Frozen.image u (N + 128) (C + 185) Q
      (A + (N600.rankCost rank + SharedChild.cost k raw))
      (ccM (N600.program w index k raw rank >>= fun ends =>
        SharedV3.childN w index k raw ends padL padR) K) := by
  have hspec : (N600.program w index k raw rank >>= fun ends =>
      SharedV3.childN w index k raw ends padL padR) =
      (N600.program (SharedV3.viewW w k.val v) index k raw rank >>= fun ends =>
        SharedV3.childProgram (SharedV3.viewW w k.val v) index k raw ends) := by
    unfold N600.program
    rw [SharedV3.chainProgram_view]
    simp only [fun ends => SharedV3.childProgram_view w index k v raw ends padL padR hL hR]
  rw [hspec, ccM_bind]
  have hc := chains k rank (SharedV3.viewW w k.val v) index k raw u (N+39) (C+96)
    (A+SharedChild.cost k raw) Q
    (fun ends => ccM (SharedV3.childProgram (SharedV3.viewW w k.val v) index k raw ends) K) hu
    (fun ends entry hp => childs k raw (SharedV3.viewW w k.val v) index ends entry N C A Q K
      (hp.sharedChild hu) (hnext ends entry hp))
  convert hc using 1 <;> first | rfl | omega

def coordN (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (k : Fin 9) (raw : Fin 128)
    (rank : Fin 563) (prev : Digest × Digest) : M (Digest × Digest) :=
  SharedV3.coordinate w index k raw (N600.embed rank) prev

def stepN (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput)
    (state : Option (List (Digest × Digest))) (k : Fin 9) : M (Option (List (Digest × Digest))) := do
  let some pairs := state | pure none
  if ¬ SharedForest.rawForestRank a k.val < 563 then return none
  let pair ← coordN w (idxOf a) k (SharedForest.rawChildFromOutput a k)
    (SharedForest.forestRank a k.val) (prevOf w pairs)
  pure (some (pairs ++ [pair]))

def ftsN (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) : M (Option (Digest × Digest)) := do
  let some pairs ← (List.finRange 9).foldlM (stepN w a) (some []) | pure none
  pure (some (prevOf w pairs))

theorem prevOf_snoc (w : ClaudeWCT.W9.T3M.WBytes) (pairs : List (Digest × Digest))
    (p : Digest × Digest) : prevOf w (pairs ++ [p]) = p := by
  unfold prevOf; simp

/-- All chain writes lie within the child routine's local frame. -/
theorem chainWrites_childWrites (k : Fin 9) (raw : Fin 128) (addr : Nat)
    (h : Chain.writes (SharedLayout.layout k) k addr) : SharedChild.writes (SharedLayout.layout k) k raw addr := by
  left
  unfold Chain.writes at h; simp only [W9Machine.SharedLayout.base_eq] at h ⊢
  split <;> omega

theorem core_frame (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (k : Fin 9) (raw : Fin 128)
    (v u entry t : MachineState) (ends : List Digest) (computed : Digest)
    (hp : Chain.Post (SharedLayout.layout k) (SharedV3.viewW w k.val v) index k raw u ends entry)
    (ht : SharedChild.Post (SharedLayout.layout k) k raw entry computed t) :
    Frame u t (SharedChild.writes (SharedLayout.layout k) k raw) := by
  intro addr ha hn
  rw [ht.frame addr ha hn]
  exact hp.frame addr ha (fun h => hn (chainWrites_childWrites k raw addr h))

end W9Drv.SharedCoord

namespace W9Drv.SharedCoord
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest HashOutput M)
open SigGolfCandidate.Research
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem writes_bounds (k : Fin 9) (raw : Fin 128) (addr : Nat)
    (h : SharedChild.writes (SharedLayout.layout k) k raw addr) : 1200 ≤ addr ∧ addr < 11792 := by
  have hk := k.isLt
  unfold SharedChild.writes SharedChild.outputAddr SharedChild.handAddr at h; simp only [W9Machine.Frozen.base_eq, W9Machine.SharedLayout.base_eq] at h; unfold coordinateBase at h
  split_ifs at h <;> omega

theorem hand_address (k : Fin 9) (raw : Fin 128) :
    SharedChild.handAddr (SharedLayout.layout k) k raw = regionAddr (k.val + 1) +
      (if SharedV3.direction k.val (SharedV3.physical k.val raw.val) = 0 then SharedV3.handL (k.val + 1)
       else SharedV3.handR (k.val + 1)) := by
  have hk := k.isLt
  unfold SharedChild.handAddr; base0; unfold coordinateBase regionAddr SharedV3.handR SharedV3.handL
  split_ifs <;> omega

theorem frame_after_dispatch (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (k : Fin 9)
    (rank : Fin 563) (u entry t : MachineState) (ends : List Digest) (computed : Digest)
    (hp : Chain.Post (SharedLayout.layout k) (SharedV3.viewW w k.val u) (idxOf a) k
      (SharedForest.rawChildFromOutput a k) (SharedDispatch.chainEntryState k rank u) ends entry)
    (ht : SharedChild.Post (SharedLayout.layout k) k (SharedForest.rawChildFromOutput a k)
      entry computed t) : Frame u t (SharedChild.writes (SharedLayout.layout k) k (SharedForest.rawChildFromOutput a k)) := by
  have hf := core_frame w (idxOf a) k (SharedForest.rawChildFromOutput a k) u
    (SharedDispatch.chainEntryState k rank u) entry t ends computed hp ht
  intro addr ha hn
  exact (hf addr ha hn).trans (SharedDispatch.mem k u _)

/-- The unused hand-off slot remains the exact authentication digest supplied
by the witness, including the direct LOW singleton output layout. -/
theorem next_other (w : ClaudeWCT.W9.T3M.WBytes) (k : Fin 9) (raw : Fin 128)
    (u t : MachineState) (hf : Frame u t (SharedChild.writes (SharedLayout.layout k) k raw)) (off : Nat)
    (hoff : off = SharedV3.handL (k.val + 1) ∨ off = SharedV3.handR (k.val + 1))
    (hsel : if SharedV3.direction k.val (SharedV3.physical k.val raw.val) = 0
      then off = SharedV3.handR (k.val + 1) else off = SharedV3.handL (k.val + 1))
    (h0 : W9Machine.OrigW w u (regionAddr (k.val + 1) + off))
    (h1 : W9Machine.OrigW w u (regionAddr (k.val + 1) + (off + 8))) :
    DigAt t (regionAddr (k.val + 1) + off)
      (SharedV3.topOther w k.val (SharedV3.physical k.val raw.val)) := by
  have hk := k.isLt
  have h1' : W9Machine.OrigW w u (regionAddr (k.val + 1) + off + 8) := by
    rw [Nat.add_assoc]; exact h1
  have hlo : 0x1020 ≤ regionAddr (k.val + 1) + off := by
    unfold SharedV3.handR SharedV3.handL at hoff
    unfold regionAddr
    split_ifs at hoff <;> omega
  have hd := W9Machine.DigAt_origW h0 h1' hlo
  have he : regionAddr (k.val + 1) + off - 0x1020 =
      SharedV3.topOtherOff k.val (SharedV3.physical k.val raw.val) := by
    unfold SharedV3.topOtherOff V3.regionOffset regionAddr
    unfold SharedV3.handR SharedV3.handL at hsel ⊢
    split_ifs at hsel ⊢ <;> omega
  rw [he] at hd
  refine hd.frame hf (by
    unfold SharedV3.handR SharedV3.handL at hoff
    unfold regionAddr
    split_ifs at hoff <;> omega) ?_ ?_
  all_goals
    intro hw
    unfold SharedChild.writes SharedChild.outputAddr SharedChild.handAddr at hw; simp only [W9Machine.Frozen.base_eq, W9Machine.SharedLayout.base_eq] at hw; unfold coordinateBase at hw
    unfold SharedV3.handR SharedV3.handL at hoff hsel
    unfold regionAddr at hw
    split_ifs at hsel hw <;> omega

end W9Drv.SharedCoord

namespace W9Drv.SharedCoord
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest HashOutput M)
open SigGolfCandidate.Research
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem next (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (k : Fin 9)
    (rank : Fin 563) (pairs : List (Digest × Digest)) (u entry t : MachineState) (ends : List Digest) (computed : Digest)
    (hu : Pre pk w a k.val pairs u)
    (hp : Chain.Post (SharedLayout.layout k) (SharedV3.viewW w k.val u) (idxOf a) k (SharedForest.rawChildFromOutput a k)
      (SharedDispatch.chainEntryState k rank u) ends entry)
    (ht : SharedChild.Post (SharedLayout.layout k) k (SharedForest.rawChildFromOutput a k) entry computed t) :
    Pre pk w a (k.val+1) (pairs ++ [if SharedV3.direction k.val (SharedV3.physical k.val (SharedForest.rawChildFromOutput a k).val) = 0
      then (computed, SharedV3.topOther w k.val (SharedV3.physical k.val (SharedForest.rawChildFromOutput a k).val))
      else (SharedV3.topOther w k.val (SharedV3.physical k.val (SharedForest.rawChildFromOutput a k).val), computed)]) t := by
  have hk := k.isLt
  have hc := SharedDispatch.chain_pre pk w a k rank pairs u hu
  have hf := frame_after_dispatch w a k rank u entry t ends computed hp ht
  have hm (A : Nat) (hA : A < 2^64) (hs : A < 1200 ∨ 11792 ≤ A) :
      t.getMem (BitVec.ofNat 64 A) = u.getMem (BitVec.ofNat 64 A) := by
    apply hf A hA
    intro hw
    have := writes_bounds k (SharedForest.rawChildFromOutput a k) A hw
    omega
  have hr (r : Reg) (h : r ∉ [.x3,.x10,.x11,.x12,.x14,.x25]) :
      t.getReg r = (SharedDispatch.chainEntryState k rank u).getReg r := by
    rw [ht.keep r (by
      simp only [Child.clobbers, List.mem_cons, List.not_mem_nil, or_false] at *
      tauto)]
    exact hp.keep r h
  have hd (r : Reg) (h : r ∉ [.x1,.x4,.x8,.x14,.x15,.x16,.x17,.x23,.x25,.x31]) :
      (SharedDispatch.chainEntryState k rank u).getReg r = u.getReg r := SharedDispatch.keep k u r h
  have hdr : ∀ i, 4 ≤ i → i < 6 → ¬ SharedChild.writes (SharedLayout.layout k) k (SharedForest.rawChildFromOutput a k) (WIT + 8 * i) := by
    intro i h4 h6 hw
    unfold SharedChild.writes SharedChild.outputAddr SharedChild.handAddr at hw; simp only [W9Machine.Frozen.base_eq, W9Machine.SharedLayout.base_eq] at hw; unfold coordinateBase WIT at hw
    split_ifs at hw <;> omega
  have hg : Glob [(.x5, 0)] w pk t := by
    obtain ⟨hreg, hh, hpk, hz, hhalf, hdata⟩ := hu.glob
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      exact (hr .x5 (by decide)).trans ((hd .x5 (by decide)).trans (hreg (.x5, 0) (by simp)))
    · intro j hj4 hj
      rw [hf _ (by unfold WIT; omega) (hdr j hj4 hj)]
      exact hh j hj4 hj
    · exact ⟨(hm 160 (by decide) (Or.inl (by omega))).trans hpk.1,
        (hm 168 (by decide) (Or.inl (by omega))).trans hpk.2⟩
    · intro A hA
      have hb : A < 1200 := by simp [pSlots] at hA; omega
      exact (hm A (by omega) (Or.inl hb)).trans (hz A hA)
    · change (t.getMem (BitVec.ofNat 64 CTRW)).toNat / 2 ^ 32 = 0
      rw [hm CTRW (by decide) (Or.inl (by decide))]
      exact hhalf
    · refine ⟨?_, fun lay hl => ?_, ?_⟩
      · rw [hm (TOPBASE-8) (by unfold TOPBASE; omega) (Or.inr (by unfold TOPBASE; omega))]
        exact hdata.mask
      · have hb := hdrAddr_bounds lay
        rw [hm (hdrAddr lay) (by unfold TOPBASE at *; omega) (Or.inr (by unfold TOPBASE at *; omega))]
        exact hdata.header lay hl
      · rw [hm (TOPB9+56) (by unfold TOPB9; omega) (Or.inr (by unfold TOPB9; omega))]
        exact hdata.buffer3
  have hb6 : SharedV3.direction k.val (SharedV3.physical k.val (SharedForest.rawChildFromOutput a k).val) = 0 ∨ SharedV3.direction k.val (SharedV3.physical k.val (SharedForest.rawChildFromOutput a k).val) = 1 := by unfold SharedV3.direction; omega
  have hra := regionAddr_succ k.val hk
  have hbase : coordinateBase k = regionAddr k.val := by base0; unfold coordinateBase regionAddr; omega
  have hR9 : regionAddr (k.val + 1) ≥ 496 := by unfold regionAddr; omega
  -- the other top sibling, from the witness (region k+1 is untouched outside one hand-off slot)
  have hother : ∀ off, (off = SharedV3.handL (k.val + 1) ∨ off = SharedV3.handR (k.val + 1)) →
      (if SharedV3.direction k.val (SharedV3.physical k.val (SharedForest.rawChildFromOutput a k).val) = 0 then off = SharedV3.handR (k.val + 1) else off = SharedV3.handL (k.val + 1)) →
      DigAt t (regionAddr (k.val + 1) + off) (SharedV3.topOther w k.val (SharedV3.physical k.val (SharedForest.rawChildFromOutput a k).val)) := by
    intro off hoff hsel
    have ho : off ≤ 816 ∧ off % 8 = 0 ∧ (k.val + 1 = 9 → 768 ≤ off) := by
      unfold SharedV3.handR SharedV3.handL at hoff
      split_ifs at hoff <;> omega
    exact next_other w k _ u t hf off hoff hsel
      (hu.coords (k.val + 1) (by omega) (by omega) off (by omega) (by omega) ho.2.2
        (fun h => by omega))
      (hu.coords (k.val + 1) (by omega) (by omega) (off + 8) (by omega) (by omega) (fun h => by have := ho.2.2 h; omega)
        (fun h => by omega))
  have htop : DigAt t (SharedChild.handAddr (SharedLayout.layout k) k (SharedForest.rawChildFromOutput a k)) computed := ht.top
  refine {
    le := by omega
    length := by simp [hu.length]
    pc := ?_
    glob := hg
    digest := fun i hi => (hm _ (by omega) (Or.inl (by omega))).trans (hu.digest i hi)
    bank := ?_
    forest := ?_
    index := (hr .x22 (by decide)).trans ((hd .x22 (by decide)).trans hu.index)
    heaps := ?_
    stepOne := (hr .x7 (by decide)).trans hc.stepOne
    stepTwo := (hr .x13 (by decide)).trans hc.stepTwo
    hashLen := ht.hashLen
    coordStep := (hr .x6 (by decide)).trans ((hd .x6 (by decide)).trans hu.coordStep)
    d0 := (hm _ (by unfold dataBase7; omega) (Or.inr (by unfold dataBase7; omega))).trans hu.d0
    nodeReg := ?_
    cached3 := ?_
    cached := ?_
    mask := (hr .x2 (by decide)).trans ((hd .x2 (by decide)).trans hu.mask)
    childMask := (hr .x27 (by decide)).trans ((hd .x27 (by decide)).trans hu.childMask)
    aTable := (hr .x28 (by decide)).trans ((hd .x28 (by decide)).trans hu.aTable)
    singletonTable := (hm _ (by unfold TOPB9; omega) (Or.inr (by unfold TOPB9; omega))).trans hu.singletonTable
    jt := (hr .x24 (by decide)).trans ((hd .x24 (by decide)).trans hu.jt)
    childBlock := (hr .x29 (by decide)).trans ((hd .x29 (by decide)).trans hu.childBlock)
    baseReg := ?_
    pairPtr := ?_
    prevL := ?_
    prevR := ?_
    a2 := ?_
    coords := ?_
    layer := ?_
    hoist := ?_ }
  · rw [ht.pc]
    fin_cases k <;> rfl
  · refine ⟨?_, ?_⟩
    · intro i hi
      exact (hm _ (by unfold TOPLOAD; omega) (Or.inr (by unfold TOPLOAD; omega))).trans (hu.bank.top i hi)
    · exact (hm _ (by unfold TOPLOAD; omega) (Or.inr (by unfold TOPLOAD; omega))).trans hu.bank.top8
  · refine ⟨?_, ?_, ?_⟩
    · exact (hm _ (by unfold dataBase7; omega) (Or.inr (by unfold dataBase7; omega))).trans hu.forest.zero0
    · exact (hm _ (by unfold dataBase7; omega) (Or.inr (by unfold dataBase7; omega))).trans hu.forest.zero1
    · exact (hm _ (by unfold dataBase7; omega) (Or.inr (by unfold dataBase7; omega))).trans hu.forest.header
  · intro h h2 h7
    exact (hr (Child.heapReg h) (by interval_cases h <;> decide)).trans (hc.heaps h h2 h7)
  · rw [hr .x15 (by decide), show k.val + 1 - 1 = k.val by omega]
    change ((SharedDispatch.result k.val).toState u).getReg .x15 = _
    rw [SharedDispatch.nodeWord pk w a k pairs u hu,
      nodeLow_value _ _ k.isLt (ClaudeWCT.WCT9.digestIndex_lt a)]
    apply congrArg (BitVec.ofNat 64)
    change ClaudeWCT.WCT9.digestIndex a * 2 ^ 27 + 1537 + 65536 * (k.val + 1) =
      ClaudeWCT.WCT9.digestIndex a * 2 ^ 27 + 67073 + 65536 * k.val
    omega
  · rw [hr .x17 (by decide)]
    have h3 := hu.cached3
    have hj := hu.jt
    fin_cases k <;> first | exact h3 | exact congrArg₂ (fun x y : Word => x ||| y) h3 hj
  · rw [hr .x16 (by decide)]
    have hd1 := hu.digest 1 (by decide)
    have hd2 := hu.digest 2 (by decide)
    have hcache := hu.cached
    have hj := hu.jt
    fin_cases k <;> first | exact hcache | exact congrArg₂ (fun x y : Word => x ||| y) hd1 hj | exact congrArg₂ (fun x y : Word => x ||| y) hd2 hj
  · rw [hr .x8 (by decide), show k.val + 1 - 1 = k.val by omega]
    have hb := hc.baseReg
    simp only [W9Machine.Frozen.base_eq, W9Machine.SharedLayout.base_eq, coordinateBase] at hb
    rw [hb]
    congr 1
    try omega
  · rw [hr .x9 (by decide)]
    exact (SharedDispatch.keep k u .x9 (by decide)).trans hu.pairPtr
  · rw [prevOf_snoc]
    rcases hb6 with h0 | h1
    · simp only [h0, if_true]
      have e : SharedChild.handAddr (SharedLayout.layout k) k (SharedForest.rawChildFromOutput a k) = regionAddr (k.val + 1) + SharedV3.handL (k.val + 1) := by
        rw [hand_address, if_pos h0]
      rw [← e]; exact htop
    · simp only [h1, show (1 : Nat) ≠ 0 by decide, if_false]
      exact hother (SharedV3.handL (k.val + 1)) (Or.inl rfl) (by rw [if_neg (by omega)])
  · rw [prevOf_snoc]
    rcases hb6 with h0 | h1
    · simp only [h0, if_true]
      exact hother (SharedV3.handR (k.val + 1)) (Or.inr rfl) (by rw [if_pos h0])
    · simp only [h1, show (1 : Nat) ≠ 0 by decide, if_false]
      have e : SharedChild.handAddr (SharedLayout.layout k) k (SharedForest.rawChildFromOutput a k) = regionAddr (k.val + 1) + SharedV3.handR (k.val + 1) := by
        rw [hand_address, if_neg (by omega)]
      rw [← e]; exact htop
  · intro _
    have h12 := ht.a2
    unfold SharedChild.outputAddr SharedChild.handAddr at h12
    split_ifs at h12
    all_goals first
      | (left; rw [h12]; congr 1; base0; unfold coordinateBase regionAddr; split_ifs <;> omega)
      | (right; rw [h12]; congr 1; base0; unfold coordinateBase regionAddr; split_ifs <;> omega)
  · intro m hm1 hm9 off hoff h8 hv hh
    have h0 := hu.coords m (by omega) hm9 off hoff h8 hv (fun h => by omega)
    unfold W9Machine.OrigW at h0 ⊢
    rw [← h0]
    apply hf _ (by unfold regionAddr; omega)
    intro hw
    unfold SharedChild.writes SharedChild.outputAddr SharedChild.handAddr at hw; simp only [W9Machine.Frozen.base_eq, W9Machine.SharedLayout.base_eq] at hw; unfold coordinateBase at hw
    have hmk : regionAddr m + 848 ≤ regionAddr k.val := by unfold regionAddr; omega
    rcases Nat.lt_or_ge (k.val + 1) m with hgt | hle
    · have : regionAddr m + 848 ≤ regionAddr (k.val + 1) := by unfold regionAddr; omega
      try simp only [W9Machine.Frozen.base_eq, W9Machine.SharedLayout.base_eq] at *
      unfold coordinateBase regionAddr at *
      split_ifs at hw <;> omega
    · have hm' : m = k.val + 1 := by omega
      subst hm'
      have hn := hh rfl
      unfold isHand SharedV3.isHand at hn
      try simp only [W9Machine.Frozen.base_eq, W9Machine.SharedLayout.base_eq] at *
      unfold coordinateBase regionAddr at *
      split_ifs at hn <;> split_ifs at hw <;> omega
  · exact hu.layer.frame (fun j hj h => hf _ (by unfold WIT WX at *; omega)
      (by intro hw; unfold SharedChild.writes SharedChild.outputAddr SharedChild.handAddr at *; simp only [W9Machine.Frozen.base_eq, W9Machine.SharedLayout.base_eq] at hw ⊢; unfold coordinateBase regionAddr WIT at *; split_ifs at hw <;> omega))
  · -- dispatch hoist: `tp = a7 >>> 17` from coordinate 7's dispatcher; the chain (`Chain.clobbers`) and B′ child
    -- (`Child.clobbers`) routines keep both `tp` and `a7`.
    intro h8
    have hk7 : k = ⟨7, by decide⟩ := Fin.ext (show k.val = 7 by omega)
    subst hk7
    rw [hr .x4 (by decide), hr .x17 (by decide)]
    change ((SharedDispatch.result 7).toState u).getReg .x4 =
      ((SharedDispatch.result 7).toState u).getReg .x17 >>> 17
    exact SharedDispatch.hoist_seven u

end W9Drv.SharedCoord
