import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.HdrBlocks

namespace ClaudeWCT.W9.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SigGolfCandidate.T3M.Extract (canonicalHeader_high_zero canonicalHeader_marker_ne)
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
def treeBits (lay : Layer) : Nat := ![0, 12, 19, 25] lay
theorem route_tree_treeBits (index : Nat) (hindex : index < 2 ^ 31) (lay : Layer) :
    (route index lay).2 < 2 ^ treeBits lay := by
  fin_cases lay <;> simp [route, treeBits, height] <;> omega
theorem routed_lt_of_treeBits {lay : Layer} {tree leaf : Nat} (ht : tree < 2 ^ treeBits lay)
    (hl : leaf < 2 ^ height lay) : tree * 2 ^ height lay + leaf < 2 ^ 31 := by
  fin_cases lay <;> simp [treeBits, height] at ht hl ⊢ <;> omega
theorem routed_treeBits_succ {lay : Layer} (h3 : lay.val < 3) {tree leaf : Nat} (ht : tree < 2 ^ treeBits lay)
    (hl : leaf < 2 ^ height lay) : tree * 2 ^ height lay + leaf < 2 ^ treeBits ⟨lay.val + 1, by omega⟩ := by
  obtain ⟨l, hlt⟩ := lay
  change l < 3 at h3
  interval_cases l <;> simp [treeBits, height] at ht hl ⊢ <;> omega
theorem treeBits_le (lay : Layer) : treeBits lay ≤ 25 := by fin_cases lay <;> decide
theorem tree_lt_of_treeBits {lay : Layer} {tree : Nat} (ht : tree < 2 ^ treeBits lay) : tree < 2 ^ 31 :=
  lt_of_lt_of_le ht (le_trans (Nat.pow_le_pow_right (by decide) (treeBits_le lay)) (by norm_num))
theorem tree_zero_of_treeBits {lay : Layer} {tree : Nat} (ht : tree < 2 ^ treeBits lay) : lay = 0 → tree = 0 := by
  rintro rfl; simpa [treeBits] using ht
theorem leaf_bounded_of_treeBits {lay : Layer} {tree leaf : Nat} (ht : tree < 2 ^ treeBits lay)
    (hl : leaf < 2 ^ height lay) : (Pos.leaf lay tree leaf).Bounded :=
  ⟨hl, lt_trans (routed_lt_of_treeBits ht hl) (by norm_num)⟩
def hdrClass (h : BitVec 128) : Nat :=
  if 128 ≤ tweakMarker h then 0
  else if tweakMarker h = 64 then 1
  else if tweakTag h = 2 then (if tweakHigh h = 0 then 2 else 3)
  else if tweakTag h = 6 then (if tweakHigh h = 0 then 4 else 5)
  else 6
def Pos.cls : Pos → Nat
  | .chain .. => 0
  | .wctChain .. => 0
  | .node lay .. => if lay = 0 then 1 else 3
  | .leaf .. => 2
  | .wctLeaf .. => 4
  | .wctNode .. => 5
  | .forest .. => 6
theorem heap_lt {e x : Nat} (hx : x < 2 ^ e) (he : e ≤ 12) : 2 ^ e + x < 2 ^ 32 := by
  have : 2 ^ e ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) he
  have : (2 : Nat) ^ 12 = 4096 := by norm_num
  have : (2 : Nat) ^ 32 = 4294967296 := by norm_num
  omega
theorem heap_inj {e f x y : Nat} (hx : x < 2 ^ e) (hy : y < 2 ^ f) (h : 2 ^ e + x = 2 ^ f + y) : e = f ∧ x = y := by
  have key : ∀ {e f x y : Nat}, x < 2 ^ e → e < f → 2 ^ e + x < 2 ^ f + y := by
    intro e f x y hx hef
    have : 2 ^ (e + 1) ≤ 2 ^ f := Nat.pow_le_pow_right (by decide) hef
    rw [pow_succ] at this
    omega
  rcases Nat.lt_trichotomy e f with hlt | heq | hgt
  · exact absurd h (ne_of_lt (key hx hlt))
  · subst heq; exact ⟨rfl, by omega⟩
  · exact absurd h.symm (ne_of_lt (key hy hgt))
private theorem height_le12 (lay : Layer) : height lay ≤ 12 := by fin_cases lay <;> decide
theorem heap_lt64 {e x : Nat} (hx : x < 2 ^ e) (he : e ≤ 12) : 2 ^ e + x < 2 ^ 64 :=
  lt_trans (heap_lt hx he) (by norm_num)
private theorem node_heap_lt {lay : Layer} {level nd : Nat} (hnd : nd < 2 ^ (height lay - level - 1)) :
    2 ^ (height lay - level - 1) + nd < 2 ^ 64 :=
  heap_lt64 hnd (le_trans (Nat.sub_le _ _) (le_trans (Nat.sub_le _ _) (height_le12 lay)))
private theorem hdrClass_packed {x : BitVec 128} (h : 128 ≤ tweakMarker x) : hdrClass x = 0 := by
  unfold hdrClass; rw [if_pos h]
private theorem hdrClass_top {x : BitVec 128} (h : tweakMarker x = 64) : hdrClass x = 1 := by
  unfold hdrClass; rw [if_neg (by omega), if_pos h]
private theorem hdrClass_one {x : BitVec 128} (h : tweakMarker x = 1) :
    hdrClass x = if tweakTag x = 2 then (if tweakHigh x = 0 then 2 else 3)
      else if tweakTag x = 6 then (if tweakHigh x = 0 then 4 else 5) else 6 := by
  unfold hdrClass; rw [if_neg (by omega), if_neg (by omega)]
private theorem ftsLeafHeader_tweakHigh (index coord selected : Nat) :
    tweakHigh (WCT9.ftsLeafHeader index coord selected) = 0 := by
  unfold tweakHigh
  rw [WCT9.ftsLeafHeader_toNat]
  exact Nat.div_eq_of_lt (lt_trans (WCT9.ftsLeafLow_lt _ _ _) (by norm_num))
private theorem wctNodeHeader_tweakHigh {coord : Nat} (hk : coord < 9) (index heap : Nat) :
    tweakHigh (WCT9.wctNodeHeader coord index heap) = heap % 2 ^ 64 := by
  unfold tweakHigh
  rw [WCT9.wctNodeHeader_toNat hk]
  have := lt_trans (WCT9.ftsLeafLow_lt index coord 0) (show 2 ^ 58 < 2 ^ 64 by norm_num)
  omega
theorem Pos.hdrClass_eq {p : Pos} (hb : p.Bounded) : hdrClass p.hdr = p.cls := by
  cases p with
  | chain lay tree lf i step => exact hdrClass_packed (chainHeader_firstByte lay tree lf i step)
  | wctChain index coord child t step =>
      have h := WCT9.ftsChainHeaderP_firstByte index coord child t step 0
      exact hdrClass_packed (show 128 ≤ tweakMarker (WCT9.ftsChainHeaderP index coord child t step 0) by
        unfold tweakMarker; omega)
  | leaf lay tree lf =>
      simp only [Pos.hdr, Pos.cls]
      rw [hdrClass_one (leafTweak_marker _ _ _), leafTweak_tag, leafTweak_high]; rfl
  | node lay tree level nd =>
      obtain ⟨-, hlev, -, -, hnd⟩ := hb
      simp only [Pos.hdr, Pos.cls]
      by_cases h0 : lay = 0
      · subst h0
        rw [if_pos rfl]
        exact hdrClass_top (nodeTweak_top_marker _ _)
      · have hv : lay.val ≠ 0 := fun h => h0 (Fin.ext h)
        have h4 : lay.val < 4 := lay.isLt
        have : 0 < 2 ^ (height lay - level - 1) := pow_pos (by decide) _
        rw [if_neg h0, hdrClass_one (nodeTweak_lower_marker hv h4 _ _), nodeTweak_lower_tag hv h4,
          nodeTweak_hyper_high h4, Nat.mod_eq_of_lt (node_heap_lt hnd), if_pos rfl, if_neg (by omega)]
  | wctLeaf index coord child =>
      simp only [Pos.hdr, Pos.cls]
      rw [hdrClass_one (WCT9.ftsLeafHeader_tweakMarker _ _ _), WCT9.ftsLeafHeader_tweakTag,
        ftsLeafHeader_tweakHigh]; rfl
  | wctNode index coord level nd =>
      obtain ⟨-, hk, hlev, hnd⟩ := hb
      have hheap := heap_lt64 hnd (show 7 - level - 1 ≤ 12 by omega)
      have : 0 < 2 ^ (7 - level - 1) := pow_pos (by decide) _
      simp only [Pos.hdr, Pos.cls]
      rw [hdrClass_one (WCT9.wctNodeHeader_tweakMarker _ _ _), WCT9.wctNodeHeader_tweakTag hk,
        wctNodeHeader_tweakHigh hk, Nat.mod_eq_of_lt hheap, if_neg (by decide), if_pos rfl, if_neg (by omega)]
  | forest index =>
      simp only [Pos.hdr, Pos.cls]
      rw [hdrClass_one (header_marker _ _ _ _ _), header_tag]; rfl
private theorem node_level_inj {lay : Layer} {level nd level' nd' : Nat} (hlev : level < height lay)
    (hlev' : level' < height lay) (hnd : nd < 2 ^ (height lay - level - 1))
    (hnd' : nd' < 2 ^ (height lay - level' - 1))
    (h : 2 ^ (height lay - level - 1) + nd = 2 ^ (height lay - level' - 1) + nd') : level = level' ∧ nd = nd' := by
  obtain ⟨e, x⟩ := heap_inj hnd hnd' h
  exact ⟨by omega, x⟩
theorem Pos.hdr_injective {p p' : Pos} (hb : p.Bounded) (hb' : p'.Bounded)
    (h : p.hdr = p'.hdr) : p = p' := by
  have hc : p.cls = p'.cls := by rw [← Pos.hdrClass_eq hb, ← Pos.hdrClass_eq hb', h]
  cases p
  case chain lay tree lf i step =>
    obtain ⟨ht, hf, hi, hs⟩ := hb
    cases p'
    case chain lay' tree' lf' i' step' =>
      obtain ⟨ht', hf', hi', hs'⟩ := hb'
      obtain ⟨hl, ht, hf, hi, hs⟩ := chainHeader_low_injective ht hf hi hs ht' hf' hi' hs'
        (congrArg (BitVec.extractLsb' 0 64) h)
      subst_vars; rfl
    case wctChain index coord child t step' =>
      exact False.elim (WCT9.ftsChainHeaderP_low_ne_chainHeader _ _ _ _ _ _ _ _ _ _ _
        (congrArg (BitVec.extractLsb' 0 64) h.symm))
    all_goals (simp only [Pos.cls] at hc; (try split_ifs at hc) <;> omega)
  case wctChain index coord child t step =>
    obtain ⟨hi, hc9, hj, ht, hs⟩ := hb
    cases p'
    case chain lay tree lf i step' =>
      exact False.elim (WCT9.ftsChainHeaderP_low_ne_chainHeader _ _ _ _ _ _ _ _ _ _ _
        (congrArg (BitVec.extractLsb' 0 64) h))
    case wctChain index' coord' child' t' step' =>
      obtain ⟨hi', hc9', hj', ht', hs'⟩ := hb'
      obtain ⟨e1, e2, e3, e4, e5, -⟩ := WCT9.ftsChainHeaderP_injective hi (by omega) hj (by omega)
        (by omega) hi' (by omega) hj' (by omega) (by omega) h
      subst_vars; rfl
    all_goals (simp only [Pos.cls] at hc; (try split_ifs at hc) <;> omega)
  case leaf lay tree lf =>
    cases p'
    case leaf lay' tree' lf' =>
      obtain ⟨hl, hr⟩ := hb
      obtain ⟨hl', hr'⟩ := hb'
      obtain ⟨rfl, rfl, rfl⟩ := leafTweak_injective hl hr hl' hr' h
      rfl
    all_goals (simp only [Pos.cls] at hc; (try split_ifs at hc) <;> omega)
  case node lay tree level nd =>
    obtain ⟨ht, hlev, -, h0, hnd⟩ := hb
    cases p'
    case node lay' tree' level' nd' =>
      obtain ⟨ht', hlev', -, h0', hnd'⟩ := hb'
      have h0v : lay.val = 0 → tree = 0 := fun e => h0 (Fin.ext e)
      have h0v' : lay'.val = 0 → tree' = 0 := fun e => h0' (Fin.ext e)
      obtain ⟨hl, htr, hh⟩ := nodeTweak_hyper_injective lay.isLt lay'.isLt ht ht' h0v h0v'
        (node_heap_lt hnd) (node_heap_lt hnd') h
      have hlay : lay = lay' := Fin.ext hl
      subst hlay htr
      obtain ⟨rfl, rfl⟩ := node_level_inj hlev hlev' hnd hnd' hh
      rfl
    all_goals (simp only [Pos.cls] at hc; (try split_ifs at hc) <;> omega)
  case forest index =>
    cases p'
    case forest index' =>
      have hb1 : index < 2 ^ 40 := hb
      have hb2 : index' < 2 ^ 40 := hb'
      obtain ⟨-, -, hi, -, -⟩ := header_injective (by decide) (by decide) hb1 (by decide) (by decide)
        (by decide) (by decide) hb2 (by decide) (by decide) h
      rw [hi]
    all_goals (simp only [Pos.cls] at hc; (try split_ifs at hc) <;> omega)
  case wctLeaf index coord child =>
    cases p'
    case wctLeaf index' coord' child' =>
      obtain ⟨hi, hc9, hj⟩ := hb
      obtain ⟨hi', hc9', hj'⟩ := hb'
      obtain ⟨rfl, rfl, rfl⟩ := WCT9.ftsLeafHeader_injective hi (by omega) hj hi' (by omega) hj' h
      rfl
    all_goals (simp only [Pos.cls] at hc; (try split_ifs at hc) <;> omega)
  case wctNode index coord level nd =>
    cases p'
    case wctNode index' coord' level' nd' =>
      obtain ⟨hi, hc9, hlev, hnd⟩ := hb
      obtain ⟨hi', hc9', hlev', hnd'⟩ := hb'
      obtain ⟨rfl, rfl, hh⟩ := WCT9.wctNodeHeader_injective hc9 hi
        (heap_lt64 hnd (show 7 - level - 1 ≤ 12 by omega)) hc9' hi'
        (heap_lt64 hnd' (show 7 - level' - 1 ≤ 12 by omega)) h
      obtain ⟨e, x⟩ := heap_inj hnd hnd' hh
      have : level = level' := by omega
      subst this x
      rfl
    all_goals (simp only [Pos.cls] at hc; (try split_ifs at hc) <;> omega)
theorem rowTweak_ne_hdr (lay : Layer) (tree leaf : Nat) {p : Pos} (hb : p.Bounded) : rowTweak lay tree leaf ≠ p.hdr := by
  intro h
  have hc := Pos.hdrClass_eq hb
  rw [← h, hdrClass_one (rowTweak_marker _ _ _), rowTweak_tag, rowTweak_high] at hc
  cases p with
  | node lay' tree' level nd =>
      obtain ⟨-, hlev, hroot, -, hnd⟩ := hb
      simp only [Pos.cls] at hc
      by_cases h0 : lay' = 0
      · rw [if_pos h0] at hc; simp at hc
      · have hH := congrArg tweakHigh h
        rw [rowTweak_high] at hH
        simp only [Pos.hdr] at hH
        rw [nodeTweak_hyper_high lay'.isLt, Nat.mod_eq_of_lt (node_heap_lt hnd)] at hH
        rcases hroot with h0' | hlt
        · exact h0 h0'
        · have : 2 ^ 1 ≤ 2 ^ (height lay' - level - 1) := Nat.pow_le_pow_right (by decide) (by omega)
          omega
  | _ => simp [Pos.cls] at hc
theorem Pos.hdr_firstByte_chain (lay : Layer) (tree leaf i step : Nat) :
    128 ≤ (Pos.chain lay tree leaf i step).hdr.toNat % 256 :=
  chainHeader_firstByte lay tree leaf i step
theorem Pos.hdr_firstByte_wctChain (index coord child t step : Nat) :
    (Pos.wctChain index coord child t step).hdr.toNat % 256 = 128 + 4 * (t % 8) :=
  WCT9.ftsChainHeaderP_firstByte index coord child t step 0
theorem Pos.hdr_marker_lt {p : Pos} (hb : p.Bounded) (hn : p.cls ≠ 0) : p.hdr.toNat % 256 < 128 := by
  have hc := Pos.hdrClass_eq hb
  unfold hdrClass at hc
  unfold tweakMarker at hc
  split_ifs at hc <;> omega
theorem Pos.canonicalHeader_eq {p : Pos} (hb : p.Bounded) :
    canonicalHeader (bytesLE 16 p.hdr) = bytesLE 16 p.hdr := by
  cases p with
  | chain lay tree leaf i step =>
      exact canonicalHeader_high_zero _
        (SigGolfCandidate.T3M.chainHeader_high_zero lay tree leaf i step hb.1 hb.2.1 hb.2.2.1 hb.2.2.2)
  | wctChain index coord child t step =>
      exact canonicalHeader_high_zero _ (WCT9.ftsChainHeaderP_high index coord child t step 0)
  | leaf => exact canonicalHeader_marker_ne _ (Pos.hdr_marker_lt hb (by simp [Pos.cls]))
  | node lay => exact canonicalHeader_marker_ne _ (Pos.hdr_marker_lt hb (by simp only [Pos.cls]; split <;> omega))
  | forest => exact canonicalHeader_marker_ne _ (Pos.hdr_marker_lt hb (by simp [Pos.cls]))
  | wctLeaf => exact canonicalHeader_marker_ne _ (Pos.hdr_marker_lt hb (by simp [Pos.cls]))
  | wctNode => exact canonicalHeader_marker_ne _ (Pos.hdr_marker_lt hb (by simp [Pos.cls]))
noncomputable def posOf (input : HashInput) : Option Pos := by
  classical
  exact if h : ∃ p : Pos, p.Bounded ∧ canonicalHeader (hdrBlock input) = bytesLE 16 p.hdr
    then some (Classical.choose h) else none
theorem posOf_key_eq {input : HashInput} {p : Pos} (hb : p.Bounded)
    (h : canonicalHeader (hdrBlock input) = bytesLE 16 p.hdr) :
    posOf input = some p := by
  classical
  have hex : ∃ p : Pos, p.Bounded ∧ canonicalHeader (hdrBlock input) = bytesLE 16 p.hdr := ⟨p, hb, h⟩
  unfold posOf
  rw [dif_pos hex]
  have hs := Classical.choose_spec hex
  exact congrArg some (Pos.hdr_injective hs.1 hb (bytesLE_injective (hs.2.symm.trans h)))
theorem posOf_eq {input : HashInput} {p : Pos} (hb : p.Bounded)
    (h : hdrBlock input = bytesLE 16 p.hdr) : posOf input = some p := by
  apply posOf_key_eq hb
  rw [h, Pos.canonicalHeader_eq hb]
theorem hitIn_posOf {answers : Answers} {qs : List Spec.Domain} (h : HitIn answers qs) :
    ∃ pos actual, pos.Bounded ∧ .inl (.inr actual) ∈ qs ∧ posOf actual = some pos ∧
      HashHit answers (honestInput answers pos) actual := by
  obtain ⟨pos, actual, hb, hq, hh, hs⟩ := h
  refine ⟨pos, actual, hb, hq, posOf_key_eq hb ?_, hh⟩
  rw [hs, hdrBlock_honestInput, Pos.canonicalHeader_eq hb]
end ClaudeWCT.W9.T3M.Extract
