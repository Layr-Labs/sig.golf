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
/-- C4 key class of a position from its input length and header (adapted from b3cc11b's `keyClass`): leaves by
length (704/896), FTS leaf (128), forest (320); 64-byte inputs by the low word `W`: top folds `1 ≤ W < 2 ^ 16`,
marked words (WOTS and FTS chains, packed lower and FTS folds) byte0 `≥ 128`, FTS two-word folds otherwise. -/
def keyClass (len : Nat) (h : BitVec 128) : Nat :=
  if len = 896 ∨ len = 704 then 2
  else if len = 128 then 4
  else if len = 320 then 6
  else if 1 ≤ tweakLow h ∧ tweakLow h < 2 ^ 16 then 1
  else if 128 ≤ tweakMarker h then 0
  else 5
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
/-- The heap of a bounded node is in `[1, 2 ^ height)`. -/
theorem node_heap_bounds {lay : Layer} {level nd : Nat} (hlev : level < height lay)
    (hnd : nd < 2 ^ (height lay - level - 1)) :
    1 ≤ 2 ^ (height lay - level - 1) + nd ∧ 2 ^ (height lay - level - 1) + nd < 2 ^ height lay := by
  have h1 : 1 ≤ 2 ^ (height lay - level - 1) := Nat.one_le_two_pow
  have h2 : 2 ^ (height lay - level - 1) * 2 ≤ 2 ^ height lay := by
    rw [← pow_succ]; exact Nat.pow_le_pow_right (by decide) (by omega)
  omega
theorem top_heap_bounds {level nd : Nat} (hlev : level < height (0 : Layer))
    (hnd : nd < 2 ^ (height (0 : Layer) - level - 1)) :
    1 ≤ 2 ^ (height (0 : Layer) - level - 1) + nd ∧ 2 ^ (height (0 : Layer) - level - 1) + nd < 4096 := by
  have := node_heap_bounds hlev hnd
  exact ⟨this.1, by simpa [height] using this.2⟩
theorem Pos.keyClass_eq {p : Pos} (hb : p.Bounded) : keyClass p.len p.hdr = p.cls := by
  cases p with
  | chain lay tree lf i step =>
      have hL : 193 * 2 ^ 56 ≤ tweakLow (chainHeader lay tree lf i step) := by
        rw [tweakLow_eq_low, chainHeader_low, chainHeaderFlaggedLow_toNat]
        have := chainHeaderLow_band lay tree lf i step
        omega
      have hm := chainHeader_firstByte lay tree lf i step
      simp only [keyClass, Pos.len, Pos.hdr, Pos.cls, tweakMarker]
      split_ifs <;> omega
  | wctChain index coord child t step =>
      obtain ⟨-, hk, -, -, -⟩ := hb
      have hm := WCT9.ftsChainHeaderP_firstByte index coord child t step 0
      have hL : 2 ^ 16 ≤ tweakLow (WCT9.ftsChainHeader index coord child t step) := by
        unfold WCT9.ftsChainHeader
        rw [tweakLow_eq_low, WCT9.ftsChainHeaderP_low, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (lt_trans (WCT9.ftsChainLow_lt _ _ _ _ _) (by norm_num))]
        exact WCT9.ftsChainLow_ge (by omega) _ _ _ _
      simp only [keyClass, Pos.len, Pos.hdr, Pos.cls, WCT9.ftsChainHeader, tweakMarker] at hm hL ⊢
      split_ifs <;> omega
  | leaf lay tree lf =>
      simp only [keyClass, Pos.len, Pos.cls]
      split_ifs <;> simp_all
  | node lay tree level nd =>
      obtain ⟨-, hlev, -, -, hnd⟩ := hb
      by_cases h0 : lay = 0
      · subst h0
        have hl : tweakLow (WCT9.merkleTweak 0 tree (2 ^ (height (0 : Layer) - level - 1) + nd)) =
            topNodeWord (2 ^ (height (0 : Layer) - level - 1) + nd) := by
          rw [tweakLow_eq_low, WCT9.merkleTweak_top_low, topNodeWord_toNat64]
        have h1 := topNodeWord_pos (2 ^ (height (0 : Layer) - level - 1) + nd)
        have h2 := topNodeWord_lt (2 ^ (height (0 : Layer) - level - 1) + nd)
        show keyClass 64 (WCT9.merkleTweak 0 tree (2 ^ (height (0 : Layer) - level - 1) + nd)) = 1
        unfold keyClass
        rw [hl, if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos ⟨h1, by omega⟩]
      · have hh := node_heap_lt128 hnd (height_le7 h0)
        have hm := WCT9.lowerTweak_marker hh lay.val tree
        have hL := WCT9.lowerTweak_low_ge hh lay.val tree
        show keyClass 64 (WCT9.merkleTweak lay.val tree (2 ^ (height lay - level - 1) + nd)) = (if lay = 0 then 1 else 0)
        rw [if_neg h0, merkleTweak_layer_lower h0]
        unfold keyClass
        rw [if_neg (by decide), if_neg (by decide), if_neg (by decide)]
        unfold tweakLow
        rw [if_neg (by omega), if_pos (by omega)]
  | wctLeaf index coord child =>
      simp [keyClass, Pos.len, Pos.cls]
  | wctNode index coord level nd =>
      obtain ⟨-, hk, hlev, hnd⟩ := hb
      have hiff := ftsNew_wctNode hlev hnd
      have hlow := WCT9.wctNodeHeader_toNat hk index (2 ^ (7 - level - 1) + nd)
      have hm := WCT9.wctNodeHeader_tweakMarker coord index (2 ^ (7 - level - 1) + nd)
      have hge := WCT9.ftsLeafLow_ge (show coord < 15 by omega) index 0
      have hlt := WCT9.ftsLeafLow_lt index coord 0
      have hgeN : 2 ^ 16 ≤ WCT9.ftsNodeLowN index coord (2 ^ (7 - level - 1) + nd) := by
        rw [WCT9.ftsNodeLowN_eq, Nat.mod_eq_of_lt (show coord + 1 < 16 by omega)]; omega
      have hltN := WCT9.ftsNodeLowN_lt index coord (2 ^ (7 - level - 1) + nd)
      simp only [keyClass, Pos.len, Pos.hdr, Pos.cls]
      unfold tweakLow
      by_cases hl4 : level < 4
      · have hn := hiff.mpr hl4
        rw [if_pos hn] at hlow
        rw [if_pos ⟨hk, hn⟩] at hm
        obtain ⟨h8, h128⟩ := hn
        simp only [if_pos hl4]
        split_ifs <;> omega
      · have hn : ¬ FtsNew (2 ^ (7 - level - 1) + nd) := fun h => hl4 (hiff.mp h)
        rw [if_neg hn] at hlow
        rw [if_neg (fun h => hn h.2)] at hm
        simp only [if_neg hl4]
        split_ifs <;> omega
  | forest index =>
      simp [keyClass, Pos.len, Pos.cls]
/-- The class of a key depends on its header only through the low word. -/
theorem keyClass_of_low_eq (len : Nat) {h h' : BitVec 128} (he : h.extractLsb' 0 64 = h'.extractLsb' 0 64) :
    keyClass len h = keyClass len h' := by
  have hv := congrArg BitVec.toNat he
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero] at hv
  have hl : tweakLow h = tweakLow h' := hv
  have hm : tweakMarker h = tweakMarker h' := by
    unfold tweakMarker
    rw [← Nat.mod_mod_of_dvd h.toNat (show 256 ∣ 2 ^ 64 by norm_num),
      ← Nat.mod_mod_of_dvd h'.toNat (show 256 ∣ 2 ^ 64 by norm_num)]
    exact congrArg (· % 256) hv
  unfold keyClass
  rw [hl, hm]
private theorem node_level_inj {lay : Layer} {level nd level' nd' : Nat} (hlev : level < height lay)
    (hlev' : level' < height lay) (hnd : nd < 2 ^ (height lay - level - 1))
    (hnd' : nd' < 2 ^ (height lay - level' - 1))
    (h : 2 ^ (height lay - level - 1) + nd = 2 ^ (height lay - level' - 1) + nd') : level = level' ∧ nd = nd' := by
  obtain ⟨e, x⟩ := heap_inj hnd hnd' h
  exact ⟨by omega, x⟩
/-- C4: bounded positions are determined by their key (length and header); the length separates the forest header
`header 15 0 index 0 0` (low word 3841 for `index < 2 ^ 32`) from the top label of heap 3841. -/
theorem Pos.hdr_injective {p p' : Pos} (hb : p.Bounded) (hb' : p'.Bounded) (hlen : p.len = p'.len)
    (h : p.hdr = p'.hdr) : p = p' := by
  have hc : p.cls = p'.cls := by rw [← Pos.keyClass_eq hb, ← Pos.keyClass_eq hb', hlen, h]
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
          have hb1 : 1 ≤ 2 ^ (height lay - level - 1) + nd ∧ 2 ^ (height lay - level - 1) + nd < 4096 := by
            subst hz; exact top_heap_bounds hlev hnd
          have hb2 : 1 ≤ 2 ^ (height lay' - level' - 1) + nd' ∧ 2 ^ (height lay' - level' - 1) + nd' < 4096 := by
            subst hz'; exact top_heap_bounds hlev' hnd'
          obtain ⟨hl, htr, hh⟩ := nodeTweak_hyper_injective lay.isLt lay'.isLt ht ht' h0v h0v'
            (node_heap_lt hnd) (node_heap_lt hnd') (fun _ => hb1) (fun _ => hb2) h
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
/-- The encoding row tweak (honest high word 1) is no position header. C4: by marker, tag or high word. -/
theorem rowTweak_ne_hdr (lay : Layer) (tree leaf : Nat) {p : Pos} (hb : p.Bounded) : rowTweak lay tree leaf ≠ p.hdr := by
  intro h
  have hH : tweakHigh p.hdr = 1 := by rw [← h, rowTweak_high]
  have hM : tweakMarker p.hdr = 1 := by rw [← h, rowTweak_marker]
  have hT : tweakTag p.hdr = 2 := by rw [← h, rowTweak_tag]
  cases p with
  | chain lay' tree' lf i step =>
      have := chainHeader_firstByte lay' tree' lf i step
      simp only [Pos.hdr, tweakMarker] at hM; omega
  | wctChain index coord child t step =>
      have := WCT9.ftsChainHeaderP_firstByte index coord child t step 0
      simp only [Pos.hdr, WCT9.ftsChainHeader, tweakMarker] at hM; omega
  | leaf lay' tree' lf => simp only [Pos.hdr] at hH; rw [leafTweak_high] at hH; omega
  | node lay' tree' level nd =>
      simp only [Pos.hdr] at hH
      have hz : (WCT9.merkleTweak lay'.val tree' (2 ^ (height lay' - level - 1) + nd)).extractLsb' 64 64 = 0 := by
        by_cases h0 : lay' = 0
        · subst h0; exact WCT9.merkleTweak_top_high _ _
        · rw [merkleTweak_layer_lower h0]; exact WCT9.lowerTweak_high _ _ _
      have hx := (BitVec.extractLsb'_append_extractLsb' (w := 64) (len := 64)
        (x := WCT9.merkleTweak lay'.val tree' (2 ^ (height lay' - level - 1) + nd))).symm
      rw [hx, append64_high, hz] at hH
      simp at hH
  | wctLeaf index coord child =>
      simp only [Pos.hdr, tweakHigh] at hH
      rw [WCT9.ftsLeafHeader_toNat] at hH
      have := WCT9.ftsLeafLow_lt index coord child
      rw [Nat.div_eq_of_lt (lt_trans this (by norm_num))] at hH; omega
  | wctNode index coord level nd =>
      obtain ⟨-, hk, -, -⟩ := hb
      have := WCT9.wctNodeHeader_tweakTag hk index (2 ^ (7 - level - 1) + nd)
      simp only [Pos.hdr] at hT
      rw [this] at hT; split_ifs at hT <;> omega
  | forest index => simp only [Pos.hdr] at hT; rw [header_tag] at hT; omega
theorem Pos.hdr_firstByte_chain (lay : Layer) (tree leaf i step : Nat) :
    128 ≤ (Pos.chain lay tree leaf i step).hdr.toNat % 256 :=
  chainHeader_firstByte lay tree leaf i step
theorem Pos.hdr_firstByte_wctChain (index coord child t step : Nat) :
    (Pos.wctChain index coord child t step).hdr.toNat % 256 = 128 + 4 * (t % 8) :=
  WCT9.ftsChainHeaderP_firstByte index coord child t step 0
/-- C4: the marker byte of a position of class neither 0 (marked) nor 1 (top fold, whose marker byte is the heap's
low byte) is below 128. -/
theorem Pos.hdr_marker_lt {p : Pos} (hb : p.Bounded) (hn : p.cls ≠ 0) (h1 : p.cls ≠ 1) : p.hdr.toNat % 256 < 128 := by
  cases p with
  | chain => simp [Pos.cls] at hn
  | wctChain => simp [Pos.cls] at hn
  | leaf lay tree lf =>
      have := leafTweak_marker lay tree lf; unfold tweakMarker at this; simp only [Pos.hdr]; omega
  | node lay tree level nd => simp only [Pos.cls] at hn h1; split_ifs at hn h1 <;> omega
  | wctLeaf index coord child => simp only [Pos.hdr]; rw [WCT9.ftsLeafHeader_firstByte]; decide
  | wctNode index coord level nd =>
      obtain ⟨-, hk, hlev, hnd⟩ := hb
      have hl4 : ¬ level < 4 := by intro h; simp [Pos.cls, h] at hn
      have hn' : ¬ FtsNew (2 ^ (7 - level - 1) + nd) := fun h => hl4 ((ftsNew_wctNode hlev hnd).mp h)
      simp only [Pos.hdr]; rw [WCT9.wctNodeHeader_firstByte_lt _ _ _ hn']; decide
  | forest index =>
      have := header_marker 15 0 index 0 0; unfold tweakMarker at this; simp only [Pos.hdr]; omega
/-- C4: a position of class 1 is a top fold; its header's high word is 0. -/
theorem Pos.hdr_high_of_cls1 {p : Pos} (hc : p.cls = 1) : p.hdr.extractLsb' 64 64 = 0 := by
  cases p with
  | node lay tree level nd =>
      simp only [Pos.cls] at hc
      by_cases hz : lay = 0
      · subst hz; exact WCT9.merkleTweak_top_high _ _
      · simp [hz] at hc
  | wctNode _ _ level _ => simp only [Pos.cls] at hc; split_ifs at hc <;> omega
  | _ => simp [Pos.cls] at hc
theorem Pos.canonicalHeader_eq {p : Pos} (hb : p.Bounded) :
    canonicalHeader (bytesLE 16 p.hdr) = bytesLE 16 p.hdr := by
  cases p with
  | chain lay tree leaf i step =>
      exact canonicalHeader_high_zero _
        (SigGolfCandidate.T3M.chainHeader_high_zero lay tree leaf i step hb.1 hb.2.1 hb.2.2.1 (by have := hb.2.2.2; omega))
  | wctChain index coord child t step =>
      exact canonicalHeader_high_zero _ (WCT9.ftsChainHeaderP_high index coord child t step 0)
  | leaf => exact canonicalHeader_marker_ne _ (Pos.hdr_marker_lt hb (by simp [Pos.cls]) (by simp [Pos.cls]))
  | node lay tree level nd =>
      apply canonicalHeader_high_zero
      simp only [Pos.hdr]
      by_cases hz : lay = 0
      · subst hz; exact WCT9.merkleTweak_top_high _ _
      · rw [merkleTweak_layer_lower hz]
        exact WCT9.lowerTweak_high _ _ _
  | forest => exact canonicalHeader_marker_ne _ (Pos.hdr_marker_lt hb (by simp [Pos.cls]) (by simp [Pos.cls]))
  | wctLeaf => exact canonicalHeader_marker_ne _ (Pos.hdr_marker_lt hb (by simp [Pos.cls]) (by simp [Pos.cls]))
  | wctNode index coord level nd =>
      by_cases hl4 : level < 4
      · apply canonicalHeader_high_zero
        obtain ⟨-, hk, hlev, hnd⟩ := hb
        simp only [Pos.hdr]
        rw [WCT9.wctNodeHeader_high hk, if_pos ((ftsNew_wctNode hlev hnd).mpr hl4)]
        rfl
      · exact canonicalHeader_marker_ne _ (Pos.hdr_marker_lt hb (by simp [Pos.cls, hl4]) (by simp [Pos.cls, hl4]))
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
theorem hdrKey_of_not_leafLen {x : HashInput} (h : ¬ (x.length = 704 ∨ x.length = 896))
    (ht : ¬ (x.length = 64 ∧ TopLow (hdrBlock x))) :
    hdrKey x = canonicalHeader (hdrBlock x) := by
  unfold hdrKey; rw [if_neg h, if_neg ht]
/-- The low-word key of a header block whose high word is zero is the block itself. -/
theorem bytesLE_high_zero_key (hi lo : BitVec 64) (hz : hi = 0) :
    (bytesLE 16 (hi ++ lo)).take 8 ++ List.replicate 8 0 = bytesLE 16 (hi ++ lo) := by
  subst hz
  rw [SigGolfCandidate.T3M.Extract.bytesLE_header_words, List.take_left' (bytesLE_length 8 lo)]
  congr 1
/-- The low-word key of a header whose high word is zero is the header itself. -/
theorem bytesLE_high_zero_key' (hdr : BitVec 128) (hz : hdr.extractLsb' 64 64 = 0) :
    (bytesLE 16 hdr).take 8 ++ List.replicate 8 0 = bytesLE 16 hdr := by
  have he : hdr = hdr.extractLsb' 64 64 ++ hdr.extractLsb' 0 64 :=
    (BitVec.extractLsb'_append_extractLsb' (w := 64) (len := 64) (x := hdr)).symm
  rw [he]
  exact bytesLE_high_zero_key _ _ hz
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
  · by_cases ht : x.length = 64 ∧ TopLow (hdrBlock x)
    · rw [hdrKey_of_top ht.1 ht.2, h]
      have hT := ht.2
      rw [h, topLow_bytesLE_iff] at hT
      have hk := Pos.keyClass_eq hb
      rw [← hlen, ht.1] at hk
      unfold keyClass at hk
      rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos hT] at hk
      exact bytesLE_high_zero_key' _ (Pos.hdr_high_of_cls1 hk.symm)
    · rw [hdrKey_of_not_leafLen hl ht, h, Pos.canonicalHeader_eq hb]
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
  exact congrArg some (Pos.hdr_injective hs.1 hb (hs.2.1.symm.trans hlen) (bytesLE_injective (hs.2.2.symm.trans h)))
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
  have hL : tweakLow p.hdr = (hyperWord lay.val (tree * 2 ^ height lay + leaf)).toNat := by
    rw [tweakLow_eq_low, ← h, rowTweak, append64_low]
  have hy := hyperWord_toNat lay.val (tree * 2 ^ height lay + leaf)
  have hm : tweakMarker p.hdr = 1 := by rw [← low_tweakMarker, ← h, low_tweakMarker, rowTweak_marker]
  have hk := Pos.keyClass_eq hb
  rw [h64] at hk
  unfold keyClass at hk
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by rw [hL, hy]; omega),
    if_neg (by rw [hm]; omega)] at hk
  cases p with
  | wctNode index coord level nd =>
      obtain ⟨-, hk9, -, -⟩ := hb
      have hw := WCT9.wctNodeHeader_toNat hk9 index (2 ^ (7 - level - 1) + nd)
      have := WCT9.ftsLeafLow_lt index coord 0
      have := WCT9.ftsNodeLowN_lt index coord (2 ^ (7 - level - 1) + nd)
      simp only [Pos.hdr] at hL
      unfold tweakLow at hL
      rw [hw] at hL
      split_ifs at hL <;> omega
  | node lay' => simp only [Pos.cls] at hk; split_ifs at hk <;> omega
  | _ => simp [Pos.cls] at hk
end ClaudeWCT.W9.T3M.Extract
