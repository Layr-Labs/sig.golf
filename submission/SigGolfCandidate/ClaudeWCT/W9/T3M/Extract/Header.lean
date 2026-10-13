import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.HdrBlocks

namespace ClaudeWCT.W9.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SigGolfCandidate.T3M.Extract (canonicalHeaderL_high_zero canonicalHeaderL_keep_hdr canonicalHeaderL_words)
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
/-- Campaign S1 key class of a position from its input length and (canonical) header: leaves by length (704/896),
FTS leaf (128), forest (320); 64-byte inputs by the low word `W`: top folds `W < 2 ^ 16`, marked words (chains, FTS
chains, packed FTS folds) byte0 `≥ 128`, lower folds type byte 193, FTS two-word folds otherwise. -/
def keyClass (len : Nat) (h : BitVec 128) : Nat :=
  if len = 896 ∨ len = 704 then 2
  else if len = 128 then 4
  else if len = 320 then 6
  else if tweakLow h < 2 ^ 16 then 1
  else if 128 ≤ tweakMarker h then 0
  else if tweakLow h / 2 ^ 56 = 193 then 3
  else 5
def Pos.cls : Pos → Nat
  | .chain .. => 0
  | .wctChain .. => 0
  | .node lay .. => if lay = 0 then 1 else 3
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
/-- Heap bounds of a bounded tree node: top heaps `< 4096`, lower heaps in `[2, 128)`. -/
private theorem node_heap_bounds {lay : Layer} {level nd : Nat} (hlev : level < height lay)
    (hroot : lay = 0 ∨ level + 1 < height lay) (hnd : nd < 2 ^ (height lay - level - 1)) :
    1 ≤ 2 ^ (height lay - level - 1) + nd ∧ 2 ^ (height lay - level - 1) + nd < 4096 ∧
      (lay ≠ 0 → 2 ≤ 2 ^ (height lay - level - 1) + nd ∧ 2 ^ (height lay - level - 1) + nd < 128) := by
  have hp : 1 ≤ 2 ^ (height lay - level - 1) := Nat.one_le_two_pow
  have h12 : 2 ^ (height lay - level - 1) ≤ 2 ^ 11 := Nat.pow_le_pow_right (by decide) (by
    have := height_le12 lay; omega)
  refine ⟨by omega, by norm_num at h12; omega, fun h0 => ?_⟩
  have hroot' : level + 1 < height lay := hroot.resolve_left h0
  have h2 : 2 ≤ 2 ^ (height lay - level - 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (height lay - level - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hh7 : height lay ≤ 7 := by
    obtain ⟨l, hl⟩ := lay
    interval_cases l <;> simp_all [height]
  have h6 : 2 ^ (height lay - level - 1) ≤ 2 ^ 6 := Nat.pow_le_pow_right (by decide) (by omega)
  norm_num at h6
  omega
private theorem ftsChainLow_ge {coord : Nat} (hk : coord < 15) (index selected chain step : Nat) :
    2 ^ 16 ≤ WCT9.ftsChainLow index coord selected chain step := by
  unfold WCT9.ftsChainLow; omega
private theorem ftsLeafLow_ge {coord : Nat} (hk : coord < 15) (index selected : Nat) :
    2 ^ 16 ≤ WCT9.ftsLeafLow index coord selected := by
  unfold WCT9.ftsLeafLow; omega
theorem ftsNew_wctNode {level nd : Nat} (hl : level < 6) (hnd : nd < 2 ^ (7 - level - 1)) :
    FtsNew (2 ^ (7 - level - 1) + nd) ↔ level < 4 := by
  unfold FtsNew
  interval_cases level <;> simp at hnd ⊢ <;> omega
private theorem tweakLow_chainHeader (lay : Layer) (tree leaf i step : Nat) :
    tweakLow (chainHeader lay tree leaf i step) = (chainHeaderFlaggedLow lay tree leaf i step).toNat := by
  have h := chainHeader_low lay tree leaf i step
  have hn := congrArg BitVec.toNat h
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero] at hn
  exact hn
private theorem chainHeader_low_band (lay : Layer) (tree leaf i step : Nat) :
    193 * 2 ^ 56 ≤ tweakLow (chainHeader lay tree leaf i step) := by
  rw [tweakLow_chainHeader, chainHeaderFlaggedLow_toNat]
  have := chainHeaderLow_band lay tree leaf i step
  split_ifs <;> omega
private theorem tweakLow_ftsChainHeaderP (index coord child t step : Nat) (hp : BitVec 64) :
    tweakLow (WCT9.ftsChainHeaderP index coord child t step hp) = WCT9.ftsChainLow index coord child t step := by
  unfold tweakLow
  rw [WCT9.ftsChainHeaderP_toNat]
  have := WCT9.ftsChainLow_lt index coord child t step
  omega
private theorem tweakLow_ftsLeafHeader (index coord child : Nat) :
    tweakLow (WCT9.ftsLeafHeader index coord child) = WCT9.ftsLeafLow index coord child := by
  unfold tweakLow
  rw [WCT9.ftsLeafHeader_toNat]
  exact Nat.mod_eq_of_lt (lt_trans (WCT9.ftsLeafLow_lt _ _ _) (by norm_num))
private theorem tweakLow_wctNodeHeader {coord : Nat} (hk : coord < 9) (index heap : Nat) :
    tweakLow (WCT9.wctNodeHeader coord index heap) =
      if FtsNew heap then WCT9.ftsNodeLowN index coord heap else WCT9.ftsLeafLow index coord 0 := by
  unfold tweakLow
  rw [WCT9.wctNodeHeader_toNat hk]
  have h1 := WCT9.ftsNodeLowN_lt index coord heap
  have h2 := WCT9.ftsLeafLow_lt index coord 0
  split_ifs <;> omega
theorem Pos.keyClass_eq {p : Pos} (hb : p.Bounded) : keyClass p.len p.hdr = p.cls := by
  cases p with
  | chain lay tree lf i step =>
      have hb := chainHeader_low_band lay tree lf i step
      have hm := chainHeader_firstByte lay tree lf i step
      simp only [keyClass, Pos.len, Pos.hdr, Pos.cls, tweakMarker]
      split_ifs <;> omega
  | wctChain index coord child t step =>
      obtain ⟨-, hk, -, -, -⟩ := hb
      have h := WCT9.ftsChainHeaderP_firstByte index coord child t step 0
      have hge := ftsChainLow_ge (show coord < 15 by omega) index child t step
      have hlow := tweakLow_ftsChainHeaderP index coord child t step 0
      simp only [keyClass, Pos.len, Pos.hdr, Pos.cls, WCT9.ftsChainHeader, tweakMarker]
      split_ifs <;> omega
  | leaf lay tree lf =>
      simp only [keyClass, Pos.len, Pos.cls]
      split_ifs <;> simp_all
  | node lay tree level nd =>
      obtain ⟨-, hlev, hroot, -, hnd⟩ := hb
      obtain ⟨h1, h4096, hlow⟩ := node_heap_bounds hlev hroot hnd
      by_cases h0 : lay = 0
      · subst h0
        have hl := nodeTweak_top_low tree (2 ^ (height (0 : Layer) - level - 1) + nd)
        have := topNodeWord_lt (2 ^ (height (0 : Layer) - level - 1) + nd)
        simp only [keyClass, Pos.len, Pos.hdr, Pos.cls, Fin.val_zero, if_true]
        split_ifs <;> omega
      · have hv : lay.val ≠ 0 := fun h => h0 (Fin.ext h)
        have h4 : lay.val < 4 := lay.isLt
        obtain ⟨h2, h128⟩ := hlow h0
        have hl := nodeTweak_lower_low hv h4 tree (2 ^ (height lay - level - 1) + nd)
        have hm := nodeTweak_lower_marker hv h4 tree (2 ^ (height lay - level - 1) + nd)
        have hw := lowerNodeWord_toNat (lay.val - 1) tree (2 ^ (height lay - level - 1) + nd)
        have := Nat.mod_lt tree (show 0 < 2 ^ 32 by decide)
        simp only [keyClass, Pos.len, Pos.hdr, Pos.cls, if_neg h0]
        split_ifs <;> omega
  | wctLeaf index coord child =>
      simp [keyClass, Pos.len, Pos.cls]
  | wctNode index coord level nd =>
      obtain ⟨-, hk, hlev, hnd⟩ := hb
      have hiff := ftsNew_wctNode hlev hnd
      have hlow := tweakLow_wctNodeHeader hk index (2 ^ (7 - level - 1) + nd)
      have hm := WCT9.wctNodeHeader_tweakMarker coord index (2 ^ (7 - level - 1) + nd)
      have hge := ftsLeafLow_ge (show coord < 15 by omega) index 0
      have hlt := WCT9.ftsLeafLow_lt index coord 0
      have hgeN : 2 ^ 16 ≤ WCT9.ftsNodeLowN index coord (2 ^ (7 - level - 1) + nd) := by
        rw [WCT9.ftsNodeLowN_eq]; omega
      have hltN := WCT9.ftsNodeLowN_lt index coord (2 ^ (7 - level - 1) + nd)
      simp only [keyClass, Pos.len, Pos.hdr, Pos.cls]
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
theorem keyClass_chainHeader (lay : Layer) (tree leaf i step : Nat) :
    keyClass 64 (chainHeader lay tree leaf i step) = 0 := by
  have hb := chainHeader_low_band lay tree leaf i step
  have hm := chainHeader_firstByte lay tree leaf i step
  simp only [keyClass, tweakMarker]
  split_ifs <;> omega
/-- The low 8 bytes of a canonical header are the low label word (padded or kept). -/
theorem canonicalHeaderL_take8 (len : Nat) (hdr : BitVec 128) :
    (canonicalHeaderL len (bytesLE 16 hdr)).take 8 = bytesLE 8 (hdr.extractLsb' 0 64) := by
  have he : hdr = hdr.extractLsb' 64 64 ++ hdr.extractLsb' 0 64 :=
    (BitVec.extractLsb'_append_extractLsb' (w := 64) (len := 64) (x := hdr)).symm
  conv_lhs => rw [he, SigGolfCandidate.T3M.Extract.bytesLE_header_words]
  unfold canonicalHeaderL
  split_ifs <;> simp [List.take_append, bytesLE_length]
theorem bytesLE16_take8 (hdr : BitVec 128) : (bytesLE 16 hdr).take 8 = bytesLE 8 (hdr.extractLsb' 0 64) := by
  have he : hdr = hdr.extractLsb' 64 64 ++ hdr.extractLsb' 0 64 :=
    (BitVec.extractLsb'_append_extractLsb' (w := 64) (len := 64) (x := hdr)).symm
  conv_lhs => rw [he, SigGolfCandidate.T3M.Extract.bytesLE_header_words]
  simp [List.take_append, bytesLE_length]
private theorem node_level_inj {lay : Layer} {level nd level' nd' : Nat} (hlev : level < height lay)
    (hlev' : level' < height lay) (hnd : nd < 2 ^ (height lay - level - 1))
    (hnd' : nd' < 2 ^ (height lay - level' - 1))
    (h : 2 ^ (height lay - level - 1) + nd = 2 ^ (height lay - level' - 1) + nd') : level = level' ∧ nd = nd' := by
  obtain ⟨e, x⟩ := heap_inj hnd hnd' h
  exact ⟨by omega, x⟩
/-- Campaign S1: bounded positions are determined by their key (length and header). -/
theorem Pos.hdr_injective {p p' : Pos} (hb : p.Bounded) (hb' : p'.Bounded) (hlen : p.len = p'.len)
    (h : p.hdr = p'.hdr) : p = p' := by
  have hc : p.cls = p'.cls := by rw [← Pos.keyClass_eq hb, ← Pos.keyClass_eq hb', hlen, h]
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
    case wctNode index coord level nd =>
      exact False.elim (WCT9.wctNodeHeader_ne_chainHeader _ _ _ _ _ _ _ _ h.symm)
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
    obtain ⟨ht, hlev, hroot, h0, hnd⟩ := hb
    cases p'
    case node lay' tree' level' nd' =>
      obtain ⟨ht', hlev', hroot', h0', hnd'⟩ := hb'
      have h0v : lay.val = 0 → tree = 0 := fun e => h0 (Fin.ext e)
      have h0v' : lay'.val = 0 → tree' = 0 := fun e => h0' (Fin.ext e)
      obtain ⟨b1, b2, b3⟩ := node_heap_bounds hlev hroot hnd
      obtain ⟨b1', b2', b3'⟩ := node_heap_bounds hlev' hroot' hnd'
      obtain ⟨hl, htr, hh⟩ := nodeTweak_hyper_injective lay.isLt lay'.isLt ht ht' h0v h0v'
        ⟨b1, b2, fun hz => (b3 (fun e => hz (congrArg Fin.val e))).2⟩
        ⟨b1', b2', fun hz => (b3' (fun e => hz (congrArg Fin.val e))).2⟩ h
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
    case chain lay tree lf i step =>
      exact False.elim (WCT9.wctNodeHeader_ne_chainHeader _ _ _ _ _ _ _ _ h)
    case wctChain index' coord' child t step =>
      exact False.elim (WCT9.wctNodeHeader_ne_ftsChainHeaderP _ _ _ _ _ _ _ _ 0 h)
    all_goals (simp only [Pos.cls] at hc; (try split_ifs at hc) <;> omega)
theorem Pos.hdr_firstByte_chain (lay : Layer) (tree leaf i step : Nat) :
    128 ≤ (Pos.chain lay tree leaf i step).hdr.toNat % 256 :=
  chainHeader_firstByte lay tree leaf i step
theorem Pos.hdr_firstByte_wctChain (index coord child t step : Nat) :
    (Pos.wctChain index coord child t step).hdr.toNat % 256 = 128 + 4 * (t % 8) :=
  WCT9.ftsChainHeaderP_firstByte index coord child t step 0
/-- Honest header high words: zero except for the FTS two-word labels (levels 4/5) and the forest header. -/
theorem Pos.canonicalHeader_eq {p : Pos} (hb : p.Bounded) :
    canonicalHeaderL p.len (bytesLE 16 p.hdr) = bytesLE 16 p.hdr := by
  cases p with
  | chain lay tree leaf i step =>
      exact canonicalHeaderL_high_zero _ _
        (SigGolfCandidate.T3M.chainHeader_high_zero lay tree leaf i step hb.1 hb.2.1 hb.2.2.1 hb.2.2.2)
  | wctChain index coord child t step =>
      exact canonicalHeaderL_high_zero _ _ (WCT9.ftsChainHeaderP_high index coord child t step 0)
  | leaf lay tree lf =>
      exact canonicalHeaderL_high_zero _ _ BitVec.extractLsb'_append_eq_left
  | node lay tree level nd =>
      apply canonicalHeaderL_high_zero
      simp only [Pos.hdr]
      by_cases h0 : lay.val = 0
      · rw [show lay = 0 from Fin.ext h0, show ((0 : Layer).val) = 0 from rfl, nodeTweak_top]
        exact BitVec.extractLsb'_append_eq_left
      · rw [nodeTweak_lower h0 lay.isLt]
        exact BitVec.extractLsb'_append_eq_left
  | forest index =>
      apply canonicalHeaderL_keep_hdr
      have hb' : index < 2 ^ 40 := hb
      simp only [Pos.len, Pos.hdr]
      rw [header_toNat']
      have : ¬ packedNodeTag 15 := by decide
      rw [if_neg this]
      have hc := Nat.mod_lt (index / 2 ^ 32) (show 0 < 256 by decide)
      have hi := Nat.mod_lt index (show 0 < 2 ^ 32 by decide)
      generalize index / 2 ^ 32 % 256 = c at hc ⊢
      generalize index % 2 ^ 32 = i at hi ⊢
      have hx : (1 + 15 % 256 * 2 ^ 8 + 0 % 256 * 2 ^ 16 + c * 2 ^ 24 +
          (0 % 2 ^ 32 * 2 ^ 32 + i * 2 ^ 64 + 0 % 2 ^ 32 * 2 ^ 96)) % 2 ^ 64 = 3841 + c * 2 ^ 24 := by
        omega
      rw [hx]
      unfold padLabel
      omega
  | wctLeaf index coord child =>
      apply canonicalHeaderL_high_zero
      simp only [Pos.hdr, WCT9.ftsLeafHeader]
      exact BitVec.extractLsb'_append_eq_left
  | wctNode index coord level nd =>
      obtain ⟨-, hk, hlev, hnd⟩ := hb
      by_cases hl4 : level < 4
      · apply canonicalHeaderL_high_zero
        simp only [Pos.hdr]
        rw [WCT9.wctNodeHeader_high hk, if_pos ((ftsNew_wctNode hlev hnd).mpr hl4)]
        rfl
      · apply canonicalHeaderL_keep_hdr
        have hn : ¬ FtsNew (2 ^ (7 - level - 1) + nd) := fun h => hl4 ((ftsNew_wctNode hlev hnd).mp h)
        simp only [Pos.len, Pos.hdr]
        have hlow := tweakLow_wctNodeHeader hk index (2 ^ (7 - level - 1) + nd)
        rw [if_neg hn] at hlow
        unfold tweakLow at hlow
        rw [hlow]
        have hge := ftsLeafLow_ge (show coord < 15 by omega) index 0
        have hlt := WCT9.ftsLeafLow_lt index coord 0
        have hb0 := WCT9.ftsLeafLow_byte0 index coord 0
        unfold padLabel
        omega
theorem keyOf_honestInput (answers : Answers) {p : Pos} (hb : p.Bounded) :
    keyOf (honestInput answers p) = p.key := by
  unfold keyOf Pos.key
  rw [length_honestInput, hdrBlock_honestInput, Pos.canonicalHeader_eq hb]
noncomputable def posOf (input : HashInput) : Option Pos := by
  classical
  exact if h : ∃ p : Pos, p.Bounded ∧ keyOf input = p.key then some (Classical.choose h) else none
theorem posOf_key_eq {input : HashInput} {p : Pos} (hb : p.Bounded) (h : keyOf input = p.key) :
    posOf input = some p := by
  classical
  have hex : ∃ p : Pos, p.Bounded ∧ keyOf input = p.key := ⟨p, hb, h⟩
  unfold posOf
  rw [dif_pos hex]
  have hs := Classical.choose_spec hex
  have hk : (Classical.choose hex).key = p.key := hs.2.symm.trans h
  unfold Pos.key at hk
  exact congrArg some (Pos.hdr_injective hs.1 hb (congrArg Prod.fst hk) (bytesLE_injective (congrArg Prod.snd hk)))
theorem keyOf_eq {input : HashInput} {p : Pos} (hb : p.Bounded) (hl : input.length = p.len)
    (h : hdrBlock input = bytesLE 16 p.hdr) : keyOf input = p.key := by
  unfold keyOf Pos.key
  rw [hl, h, Pos.canonicalHeader_eq hb]
theorem posOf_eq {input : HashInput} {p : Pos} (hb : p.Bounded) (hl : input.length = p.len)
    (h : hdrBlock input = bytesLE 16 p.hdr) : posOf input = some p :=
  posOf_key_eq hb (keyOf_eq hb hl h)
theorem posOf_honestInput (answers : Answers) {p : Pos} (hb : p.Bounded) :
    posOf (honestInput answers p) = some p :=
  posOf_key_eq hb (keyOf_honestInput answers hb)
theorem posOf_of_same {answers : Answers} {actual : HashInput} {p : Pos} (hb : p.Bounded)
    (h : SameHeader actual (honestInput answers p)) : posOf actual = some p :=
  posOf_key_eq hb (h.trans (keyOf_honestInput answers hb))
theorem hitIn_posOf {answers : Answers} {qs : List Spec.Domain} (h : HitIn answers qs) :
    ∃ pos actual, pos.Bounded ∧ .inl (.inr actual) ∈ qs ∧ posOf actual = some pos ∧
      HashHitAt answers pos (honestInput answers pos) actual := by
  obtain ⟨pos, actual, hb, hq, hh, hs⟩ := h
  exact ⟨pos, actual, hb, hq, posOf_of_same hb hs, hh⟩
/-- Campaign S1: a 64-byte block whose tweak is a one-word hyper label (`hp ++ hyperWord up routed`: byte0 1, type
byte 193, any witness high word) is not the input of any position (lower fold words have byte0 = heap ≥ 2; leaves
and the forest have other lengths). This covers every encoding block. -/
theorem key_row_ne {x : HashInput} {up routed : Nat} {hp : BitVec 64} (hlen64 : x.length = 64)
    (hblk : hdrBlock x = bytesLE 16 (hp ++ hyperWord up routed)) {p : Pos} (hb : p.Bounded) :
    keyOf x ≠ p.key := by
  intro hk
  unfold keyOf Pos.key at hk
  rw [hlen64] at hk
  have hl := congrArg Prod.fst hk
  have hh := congrArg Prod.snd hk
  simp only at hl hh
  rw [hblk, canonicalHeaderL_words _ _ _ (by unfold padLabel; rw [hyperWord_toNat]; omega)] at hh
  have hz : bytesLE 8 (hyperWord up routed) ++ List.replicate 8 0 = bytesLE 16 (0#64 ++ hyperWord up routed) := by
    rw [SigGolfCandidate.T3M.Extract.bytesLE_header_words]
    congr 1
  rw [hz] at hh
  have hhdr := bytesLE_injective hh
  have hc := Pos.keyClass_eq hb
  rw [← hl, ← hhdr] at hc
  have hw := hyperWord_toNat up routed
  have hl64 : tweakLow (0#64 ++ hyperWord up routed) = (hyperWord up routed).toNat := append64_lowNat _ _
  have hm : tweakMarker (0#64 ++ hyperWord up routed) = 1 := by
    rw [append64_marker, hyperWord_marker]
  unfold keyClass at hc
  rw [hl64, hm, hw] at hc
  have := Nat.mod_lt routed (show 0 < 2 ^ 32 by decide)
  have := Nat.mod_lt up (show 0 < 256 by decide)
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega)] at hc
  cases p with
  | node lay tree' level nd =>
      obtain ⟨-, hlev, hroot, -, hnd⟩ := hb
      simp only [Pos.cls] at hc
      by_cases h0 : lay = 0
      · rw [if_pos h0] at hc; omega
      · have hv : lay.val ≠ 0 := fun h => h0 (Fin.ext h)
        obtain ⟨h2, h128⟩ := (node_heap_bounds hlev hroot hnd).2.2 h0
        have hm' := congrArg tweakMarker hhdr
        simp only [Pos.hdr] at hm'
        rw [append64_marker, hyperWord_marker, nodeTweak_lower_marker hv lay.isLt] at hm'
        omega
  | wctNode _ _ level _ => simp only [Pos.cls] at hc; split_ifs at hc <;> omega
  | _ => simp [Pos.cls] at hc
theorem posOf_row_none {x : HashInput} {up routed : Nat} {hp : BitVec 64} (hlen64 : x.length = 64)
    (hblk : hdrBlock x = bytesLE 16 (hp ++ hyperWord up routed)) : posOf x = none := by
  classical
  unfold posOf
  rw [dif_neg]
  rintro ⟨p, hb, hk⟩
  exact key_row_ne hlen64 hblk hb hk
theorem key_pairEncoding_ne (up : Layer) (tree leaf : Nat) (left right : Digest) (counter : BitVec 32)
    (hp : BitVec 64) (pad : BitVec 96) {p : Pos} (hb : p.Bounded) :
    keyOf (pad64 (WCT9.pairEncodingInputPH up tree leaf left right counter hp pad)) ≠ p.key := by
  have hlen64 : (WCT9.pairEncodingInputPH up tree leaf left right counter hp pad).length = 64 := by
    simp [WCT9.pairEncodingInputPH, bytesLE_length]
  have hpad : pad64 (WCT9.pairEncodingInputPH up tree leaf left right counter hp pad) =
      WCT9.pairEncodingInputPH up tree leaf left right counter hp pad := by
    unfold pad64; rw [hlen64]; simp
  rw [hpad]
  refine key_row_ne (up := up.val) (routed := tree * 2 ^ height up + leaf) (hp := hp) hlen64 ?_ hb
  unfold WCT9.pairEncodingInputPH
  simp only [List.append_assoc]
  exact hdrBlock_prefix' _ _ _
theorem posOf_pairEncoding_none (up : Layer) (tree leaf : Nat) (left right : Digest) (counter : BitVec 32)
    (hp : BitVec 64) (pad : BitVec 96) :
    posOf (pad64 (WCT9.pairEncodingInputPH up tree leaf left right counter hp pad)) = none := by
  classical
  unfold posOf
  rw [dif_neg]
  rintro ⟨p, hb, hk⟩
  exact key_pairEncoding_ne up tree leaf left right counter hp pad hb hk
end ClaudeWCT.W9.T3M.Extract
