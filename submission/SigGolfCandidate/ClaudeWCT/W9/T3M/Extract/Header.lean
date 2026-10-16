import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.HdrBlocks

namespace ClaudeWCT.W9.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SigGolfCandidate.T3M.Extract (canonicalHeader_high_zero canonicalHeader_marker_ne)
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
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
  | .node lay .. => if lay = 0 then 1 else 0
  | .leaf .. => 2
  | .wctLeaf .. => 4
  | .wctNode _ _ level _ => if level < 4 then 0 else 5
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
private theorem height_le7 {lay : Layer} (h0 : lay ≠ 0) : height lay ≤ 7 := by
  fin_cases lay <;> simp_all [height]
/-- A lower-tree heap (any node position of a tree of height `≤ 7`) is below 128. -/
theorem node_heap_lt128 {lay : Layer} {level nd : Nat} (hnd : nd < 2 ^ (height lay - level - 1))
    (h7 : height lay ≤ 7) : 2 ^ (height lay - level - 1) + nd < 128 := by
  have : 2 ^ (height lay - level - 1) ≤ 2 ^ 6 := Nat.pow_le_pow_right (by decide) (by omega)
  have h64 : (2 : Nat) ^ 6 = 64 := by norm_num
  have : nd < 64 := lt_of_lt_of_le hnd (by omega)
  omega
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
private theorem wctNodeHeader_tweakHigh {coord : Nat} (hk : coord < 9) (index : Nat) {heap : Nat}
    (hn : ¬ FtsNew heap) : tweakHigh (WCT9.wctNodeHeader coord index heap) = heap % 2 ^ 64 := by
  unfold tweakHigh
  rw [WCT9.wctNodeHeader_toNat hk, if_neg hn]
  have := lt_trans (WCT9.ftsLeafLow_lt index coord 0) (show 2 ^ 58 < 2 ^ 64 by norm_num)
  omega
theorem ftsNew_wctNode {level nd : Nat} (hl : level < 6) (hnd : nd < 2 ^ (7 - level - 1)) :
    FtsNew (2 ^ (7 - level - 1) + nd) ↔ level < 4 := by
  unfold FtsNew
  interval_cases level <;> simp at hnd ⊢ <;> omega
private theorem merkleTweak_layer_top {lay : Layer} (h : lay = 0) (tree heap : Nat) :
    WCT9.merkleTweak lay.val tree heap = nodeTweak 3 lay.val tree heap := by
  subst h; unfold WCT9.merkleTweak; exact if_pos rfl
theorem merkleTweak_layer_lower {lay : Layer} (h : lay ≠ 0) (tree heap : Nat) :
    WCT9.merkleTweak lay.val tree heap = WCT9.lowerTweak lay.val tree heap :=
  WCT9.merkleTweak_lower (fun e => h (Fin.ext e)) tree heap
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
      · rw [if_pos h0, merkleTweak_layer_top h0]
        subst h0
        exact hdrClass_top (nodeTweak_top_marker _ _)
      · rw [if_neg h0, merkleTweak_layer_lower h0]
        apply hdrClass_packed
        have hm := WCT9.lowerTweak_marker (node_heap_lt128 hnd (height_le7 h0)) lay.val tree
        omega
  | wctLeaf index coord child =>
      simp only [Pos.hdr, Pos.cls]
      rw [hdrClass_one (WCT9.ftsLeafHeader_tweakMarker _ _ _), WCT9.ftsLeafHeader_tweakTag,
        ftsLeafHeader_tweakHigh]; rfl
  | wctNode index coord level nd =>
      obtain ⟨-, hk, hlev, hnd⟩ := hb
      have hheap := heap_lt64 hnd (show 7 - level - 1 ≤ 12 by omega)
      have : 0 < 2 ^ (7 - level - 1) := pow_pos (by decide) _
      have hiff := ftsNew_wctNode hlev hnd
      simp only [Pos.hdr, Pos.cls]
      by_cases hl4 : level < 4
      · have hn := hiff.mpr hl4
        rw [if_pos hl4]
        apply hdrClass_packed
        rw [WCT9.wctNodeHeader_tweakMarker, if_pos ⟨hk, hn⟩]
        obtain ⟨h8, h128⟩ := hn; omega
      · have hn : ¬ FtsNew (2 ^ (7 - level - 1) + nd) := fun h => hl4 (hiff.mp h)
        rw [if_neg hl4, hdrClass_one (by rw [WCT9.wctNodeHeader_tweakMarker, if_neg (fun h => hn h.2)]),
          WCT9.wctNodeHeader_tweakTag hk, if_neg hn, wctNodeHeader_tweakHigh hk _ hn, Nat.mod_eq_of_lt hheap,
          if_neg (by decide), if_pos rfl, if_neg (by omega)]
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
      obtain ⟨hl, ht, hf, hi, hs⟩ := chainHeader_low_injective ht hf hi (by omega) ht' hf' hi' (by omega)
        (congrArg (BitVec.extractLsb' 0 64) h)
      subst_vars; rfl
    case wctChain index coord child t step' =>
      exact False.elim (WCT9.ftsChainHeaderP_low_ne_chainHeader _ _ _ _ _ _ _ _ _ _ _
        (congrArg (BitVec.extractLsb' 0 64) h.symm))
    case wctNode index coord level nd =>
      exact False.elim (WCT9.wctNodeHeader_ne_chainHeader _ _ _ _ _ _ _ _ h.symm)
    case node lay' tree' level' nd' =>
      obtain ⟨-, -, -, -, hnd'⟩ := hb'
      by_cases hz' : lay' = 0
      · simp [Pos.cls, hz'] at hc
      · simp only [Pos.hdr] at h
        rw [merkleTweak_layer_lower hz'] at h
        exact False.elim (WCT9.lowerTweak_ne_chainHeader (node_heap_lt128 hnd' (height_le7 hz')) _ _ _ _ _ _ _
          (by omega) h.symm)
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
    case wctNode index' coord' level' nd' =>
      exact False.elim (WCT9.wctNodeHeader_ne_ftsChainHeaderP _ _ _ _ _ _ _ _ 0 h.symm)
    case node lay' tree' level' nd' =>
      obtain ⟨-, -, -, -, hnd'⟩ := hb'
      by_cases hz' : lay' = 0
      · simp [Pos.cls, hz'] at hc
      · simp only [Pos.hdr] at h
        rw [merkleTweak_layer_lower hz'] at h
        exact False.elim (WCT9.lowerTweak_ne_ftsChainHeaderP (node_heap_lt128 hnd' (height_le7 hz')) _ _ _ _ _ _ _
          0 h.symm)
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
      simp only [Pos.hdr] at h
      by_cases hz : lay = 0
      · by_cases hz' : lay' = 0
        · have h0v : lay.val = 0 → tree = 0 := fun e => h0 (Fin.ext e)
          have h0v' : lay'.val = 0 → tree' = 0 := fun e => h0' (Fin.ext e)
          rw [merkleTweak_layer_top hz, merkleTweak_layer_top hz'] at h
          obtain ⟨hl, htr, hh⟩ := nodeTweak_hyper_injective lay.isLt lay'.isLt ht ht' h0v h0v'
            (node_heap_lt hnd) (node_heap_lt hnd') h
          have hlay : lay = lay' := Fin.ext hl
          subst hlay htr
          obtain ⟨rfl, rfl⟩ := node_level_inj hlev hlev' hnd hnd' hh
          rfl
        · simp [Pos.cls, hz, hz'] at hc
      · by_cases hz' : lay' = 0
        · simp [Pos.cls, hz, hz'] at hc
        · rw [merkleTweak_layer_lower hz, merkleTweak_layer_lower hz'] at h
          obtain ⟨hl, htr, hh⟩ := WCT9.lowerTweak_injective (Nat.pos_of_ne_zero (fun e => hz (Fin.ext e)))
            lay.isLt (Nat.pos_of_ne_zero (fun e => hz' (Fin.ext e))) lay'.isLt ht ht'
            (node_heap_lt128 hnd (height_le7 hz)) (node_heap_lt128 hnd' (height_le7 hz')) h
          have hlay : lay = lay' := Fin.ext hl
          subst hlay htr
          obtain ⟨rfl, rfl⟩ := node_level_inj hlev hlev' hnd hnd' hh
          rfl
    case chain lay' tree' lf' i' step' =>
      obtain ⟨-, -, -, hs'⟩ := hb'
      by_cases hz : lay = 0
      · simp [Pos.cls, hz] at hc
      · simp only [Pos.hdr] at h
        rw [merkleTweak_layer_lower hz] at h
        exact False.elim (WCT9.lowerTweak_ne_chainHeader (node_heap_lt128 hnd (height_le7 hz)) _ _ _ _ _ _ _
          (by omega) h)
    case wctChain index' coord' child' t' step' =>
      by_cases hz : lay = 0
      · simp [Pos.cls, hz] at hc
      · simp only [Pos.hdr] at h
        rw [merkleTweak_layer_lower hz] at h
        exact False.elim (WCT9.lowerTweak_ne_ftsChainHeaderP (node_heap_lt128 hnd (height_le7 hz)) _ _ _ _ _ _ _
          0 h)
    case wctNode index' coord' level' nd' =>
      obtain ⟨-, hc9', -, -⟩ := hb'
      by_cases hz : lay = 0
      · simp only [Pos.cls, if_pos hz] at hc; split_ifs at hc <;> omega
      · simp only [Pos.hdr] at h
        rw [merkleTweak_layer_lower hz] at h
        exact False.elim (WCT9.lowerTweak_ne_wctNodeHeader (node_heap_lt128 hnd (height_le7 hz)) _ _ hc9' _ _ h)
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
    case chain lay tree lf i step =>
      exact False.elim (WCT9.wctNodeHeader_ne_chainHeader _ _ _ _ _ _ _ _ h)
    case wctChain index' coord' child t step =>
      exact False.elim (WCT9.wctNodeHeader_ne_ftsChainHeaderP _ _ _ _ _ _ _ _ 0 h)
    case node lay' tree' level' nd' =>
      obtain ⟨-, hc9, -, -⟩ := hb
      obtain ⟨-, -, -, -, hnd'⟩ := hb'
      by_cases hz' : lay' = 0
      · simp only [Pos.cls, if_pos hz'] at hc; split_ifs at hc <;> omega
      · simp only [Pos.hdr] at h
        rw [merkleTweak_layer_lower hz'] at h
        exact False.elim (WCT9.lowerTweak_ne_wctNodeHeader (node_heap_lt128 hnd' (height_le7 hz')) _ _ hc9 _ _ h.symm)
    all_goals (simp only [Pos.cls] at hc; (try split_ifs at hc) <;> omega)
theorem rowTweak_ne_hdr (lay : Layer) (tree leaf : Nat) {p : Pos} (hb : p.Bounded) : rowTweak lay tree leaf ≠ p.hdr := by
  intro h
  have hc := Pos.hdrClass_eq hb
  rw [← h, hdrClass_one (rowTweak_marker _ _ _), rowTweak_tag, rowTweak_high] at hc
  cases p with
  | node lay' tree' level nd => simp only [Pos.cls] at hc; split_ifs at hc <;> simp at hc
  | wctNode _ _ level _ => simp only [Pos.cls] at hc; split_ifs at hc <;> omega
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
        (SigGolfCandidate.T3M.chainHeader_high_zero lay tree leaf i step hb.1 hb.2.1 hb.2.2.1 (by have := hb.2.2.2; omega))
  | wctChain index coord child t step =>
      exact canonicalHeader_high_zero _ (WCT9.ftsChainHeaderP_high index coord child t step 0)
  | leaf => exact canonicalHeader_marker_ne _ (Pos.hdr_marker_lt hb (by simp [Pos.cls]))
  | node lay tree level nd =>
      by_cases hz : lay = 0
      · exact canonicalHeader_marker_ne _ (Pos.hdr_marker_lt hb (by simp [Pos.cls, hz]))
      · apply canonicalHeader_high_zero
        simp only [Pos.hdr]
        rw [merkleTweak_layer_lower hz]
        exact WCT9.lowerTweak_high _ _ _
  | forest => exact canonicalHeader_marker_ne _ (Pos.hdr_marker_lt hb (by simp [Pos.cls]))
  | wctLeaf => exact canonicalHeader_marker_ne _ (Pos.hdr_marker_lt hb (by simp [Pos.cls]))
  | wctNode index coord level nd =>
      by_cases hl4 : level < 4
      · apply canonicalHeader_high_zero
        obtain ⟨-, hk, hlev, hnd⟩ := hb
        simp only [Pos.hdr]
        rw [WCT9.wctNodeHeader_high hk, if_pos ((ftsNew_wctNode hlev hnd).mpr hl4)]
        rfl
      · exact canonicalHeader_marker_ne _ (Pos.hdr_marker_lt hb (by simp [Pos.cls, hl4]))
/-! ### Length-aware position decoding (C3 FULL, S2-2)
The leaf tweak's high word and the encoding row tweak's high word are witness pads. An encoding with high word 0 has
the 16-byte header of a leaf tweak, so a position is decoded from the input length (`Pos.len`) and the decoding key
`hdrKey` (leaf-length inputs: the low tweak word only; every other input: its canonical header). -/
@[simp] theorem Pos.len_leaf (lay : Layer) (tree leaf : Nat) :
    (Pos.leaf lay tree leaf).len = if lay = 0 then 896 else 704 := rfl
theorem Pos.len_leafLen {p : Pos} : (p.len = 704 ∨ p.len = 896) ↔ ∃ lay tree leaf, p = .leaf lay tree leaf := by
  constructor
  · intro h
    cases p with
    | leaf lay tree leaf => exact ⟨lay, tree, leaf, rfl⟩
    | _ => simp [Pos.len] at h
  · rintro ⟨lay, tree, leaf, rfl⟩
    simp only [Pos.len_leaf]; split <;> simp
theorem Pos.len_of_ne_leaf {p : Pos} (h : ∀ lay tree leaf, p ≠ .leaf lay tree leaf) : ¬ (p.len = 704 ∨ p.len = 896) :=
  fun hl => by obtain ⟨lay, tree, leaf, e⟩ := Pos.len_leafLen.mp hl; exact h lay tree leaf e
theorem hdrKey_of_leafLen {x : HashInput} (h : x.length = 704 ∨ x.length = 896) :
    hdrKey x = (hdrBlock x).take 8 ++ List.replicate 8 0 := by
  unfold hdrKey; rw [if_pos h]
theorem hdrKey_of_not_leafLen {x : HashInput} (h : ¬ (x.length = 704 ∨ x.length = 896)) :
    hdrKey x = canonicalHeader (hdrBlock x) := by
  unfold hdrKey; rw [if_neg h]
/-- The low-word key of a header block whose high word is zero is the block itself. -/
theorem bytesLE_high_zero_key (hi lo : BitVec 64) (hz : hi = 0) :
    (bytesLE 16 (hi ++ lo)).take 8 ++ List.replicate 8 0 = bytesLE 16 (hi ++ lo) := by
  subst hz
  rw [SigGolfCandidate.T3M.Extract.bytesLE_header_words, List.take_left' (bytesLE_length 8 lo)]
  congr 1
theorem leafKey_hdr (lay : Layer) (tree leaf : Nat) :
    (bytesLE 16 (Pos.leaf lay tree leaf).hdr).take 8 ++ List.replicate 8 0 = bytesLE 16 (Pos.leaf lay tree leaf).hdr :=
  bytesLE_high_zero_key _ _ rfl
/-- For a bounded position, the key of an input whose header block is the position's header is that header. -/
theorem hdrKey_of_hdrBlock {x : HashInput} {p : Pos} (hb : p.Bounded) (hlen : x.length = p.len)
    (h : hdrBlock x = bytesLE 16 p.hdr) : hdrKey x = bytesLE 16 p.hdr := by
  by_cases hl : x.length = 704 ∨ x.length = 896
  · rw [hdrKey_of_leafLen hl, h]
    rw [hlen] at hl
    obtain ⟨lay, tree, leaf, rfl⟩ := Pos.len_leafLen.mp hl
    exact leafKey_hdr lay tree leaf
  · rw [hdrKey_of_not_leafLen hl, h, Pos.canonicalHeader_eq hb]
theorem hdrKey_honestInput (answers : Answers) {p : Pos} (hb : p.Bounded) :
    hdrKey (honestInput answers p) = bytesLE 16 p.hdr :=
  hdrKey_of_hdrBlock hb (honestInput_length answers p) (hdrBlock_honestInput answers p)
noncomputable def posOf (input : HashInput) : Option Pos := by
  classical
  exact if h : ∃ p : Pos, p.Bounded ∧ input.length = p.len ∧ hdrKey input = bytesLE 16 p.hdr
    then some (Classical.choose h) else none
theorem posOf_key_eq {input : HashInput} {p : Pos} (hb : p.Bounded) (hlen : input.length = p.len)
    (h : hdrKey input = bytesLE 16 p.hdr) :
    posOf input = some p := by
  classical
  have hex : ∃ p : Pos, p.Bounded ∧ input.length = p.len ∧ hdrKey input = bytesLE 16 p.hdr := ⟨p, hb, hlen, h⟩
  unfold posOf
  rw [dif_pos hex]
  have hs := Classical.choose_spec hex
  exact congrArg some (Pos.hdr_injective hs.1 hb (bytesLE_injective (hs.2.2.symm.trans h)))
theorem posOf_eq {input : HashInput} {p : Pos} (hb : p.Bounded) (hlen : input.length = p.len)
    (h : hdrBlock input = bytesLE 16 p.hdr) : posOf input = some p :=
  posOf_key_eq hb hlen (hdrKey_of_hdrBlock hb hlen h)
theorem posOf_eq_none {input : HashInput}
    (h : ∀ p : Pos, p.Bounded → input.length = p.len → hdrKey input ≠ bytesLE 16 p.hdr) : posOf input = none := by
  classical
  unfold posOf
  rw [dif_neg]
  rintro ⟨p, hb, hlen, hk⟩
  exact h p hb hlen hk
theorem posOf_spec {input : HashInput} {p : Pos} (h : posOf input = some p) :
    p.Bounded ∧ input.length = p.len ∧ hdrKey input = bytesLE 16 p.hdr := by
  classical
  unfold posOf at h
  split at h
  · rename_i hex
    cases h
    exact Classical.choose_spec hex
  · cases h
theorem hitIn_posOf {answers : Answers} {qs : List Spec.Domain} (h : HitIn answers qs) :
    ∃ pos actual, pos.Bounded ∧ .inl (.inr actual) ∈ qs ∧ posOf actual = some pos ∧
      HashHitAt answers pos (honestInput answers pos) actual := by
  obtain ⟨pos, actual, hb, hq, hh, hs⟩ := h
  refine ⟨pos, actual, hb, hq, posOf_key_eq hb ?_ ?_, hh⟩
  · rw [hs.1, honestInput_length]
  · rw [hs.2, hdrKey_honestInput answers hb]
theorem low_tweakMarker (x : BitVec 128) : (x.extractLsb' 0 64).toNat % 256 = tweakMarker x := by
  unfold tweakMarker
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  exact Nat.mod_mod_of_dvd _ (by norm_num)
theorem low_tweakTag (x : BitVec 128) : (x.extractLsb' 0 64).toNat / 256 % 256 = tweakTag x := by
  unfold tweakTag
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, show (2 : Nat) ^ 64 = 256 * 2 ^ 56 by norm_num,
    Nat.mod_mul_right_div_self]
  exact Nat.mod_mod_of_dvd _ (by norm_num)
/-- C3 (FULL): the encoding's low row-tweak word differs from the low header word of every 64-byte position. -/
theorem rowTweak_low_ne_hdr (lay : Layer) (tree leaf : Nat) {p : Pos} (hb : p.Bounded) (h64 : p.len = 64) :
    (rowTweak lay tree leaf).extractLsb' 0 64 ≠ p.hdr.extractLsb' 0 64 := by
  intro h
  have hm : tweakMarker p.hdr = 1 := by rw [← low_tweakMarker, ← h, low_tweakMarker, rowTweak_marker]
  have ht : tweakTag p.hdr = 2 := by rw [← low_tweakTag, ← h, low_tweakTag, rowTweak_tag]
  have hc2 : p.cls = 2 ∨ p.cls = 3 := by
    have hc := Pos.hdrClass_eq hb
    unfold hdrClass at hc
    rw [hm, ht] at hc
    split_ifs at hc <;> omega
  cases p with
  | chain => simp [Pos.cls] at hc2
  | wctChain => simp [Pos.cls] at hc2
  | leaf => simp only [Pos.len] at h64; split_ifs at h64 <;> omega
  | wctLeaf => simp [Pos.len] at h64
  | forest => simp [Pos.len] at h64
  | node lay' => simp only [Pos.cls] at hc2; by_cases h : lay' = 0 <;> simp [h] at hc2
  | wctNode _ _ level => simp only [Pos.cls] at hc2; by_cases h : level < 4 <;> simp [h] at hc2
end ClaudeWCT.W9.T3M.Extract
