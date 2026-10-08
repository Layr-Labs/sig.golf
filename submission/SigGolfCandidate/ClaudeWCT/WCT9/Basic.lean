import SigGolfCandidate.ClaudeWCT.WCT9.Core
import SigGolfCandidate.T3.Proofs

namespace ClaudeWCT.WCT9
open OracleComp OracleSpec SigGolfCandidate.T3
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
theorem wctHeader_eq_header (tag lay tree position index : Nat) (h : ¬ packedNodeTag tag) :
    wctHeader tag lay tree position index = header tag lay tree position index := by
  unfold wctHeader header
  rw [if_neg h]
  simp only [Nat.add_assoc]
theorem forest_header_plain (index : Nat) :
    header 15 0 index 0 0 = wctHeader 15 0 index 0 0 :=
  (wctHeader_eq_header 15 0 index 0 0 (by decide)).symm
theorem wct_tags_plain : ¬ packedNodeTag 6 ∧ ¬ packedNodeTag 15 ∧ packedNodeTag 3 := by decide
theorem ftsChainLow_lt (index coord selected chain step : Nat) :
    ftsChainLow index coord selected chain step < 2 ^ 58 := by
  unfold ftsChainLow
  have := Nat.mod_lt chain (show 0 < 8 by decide)
  have := Nat.mod_lt step (show 0 < 4 by decide)
  have := Nat.mod_lt coord (show 0 < 16 by decide)
  have := Nat.mod_lt selected (show 0 < 128 by decide)
  have := Nat.mod_lt index (show 0 < 2 ^ 31 by decide)
  norm_num only at *
  omega
theorem ftsChainLow_byte0 (index coord selected chain step : Nat) :
    ftsChainLow index coord selected chain step % 256 = 128 + 4 * (chain % 8) := by
  unfold ftsChainLow
  have := Nat.mod_lt chain (show 0 < 8 by decide)
  omega
theorem ftsChainLow_injective {i k j t s i' k' j' t' s' : Nat}
    (hi : i < 2 ^ 31) (hk : k < 16) (hj : j < 128) (ht : t < 8) (hs : s < 4)
    (hi' : i' < 2 ^ 31) (hk' : k' < 16) (hj' : j' < 128) (ht' : t' < 8) (hs' : s' < 4)
    (h : ftsChainLow i k j t s = ftsChainLow i' k' j' t' s') :
    i = i' ∧ k = k' ∧ j = j' ∧ t = t' ∧ s = s' := by
  unfold ftsChainLow at h
  rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt ht,
    Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt hk', Nat.mod_eq_of_lt hj',
    Nat.mod_eq_of_lt ht', Nat.mod_eq_of_lt hs'] at h
  norm_num only at h hi hi'
  omega
theorem ftsChainHeaderP_toNat (index coord selected chain step : Nat) (high : BitVec 64) :
    (ftsChainHeaderP index coord selected chain step high).toNat =
      high.toNat * 2 ^ 64 + ftsChainLow index coord selected chain step := by
  have hq := ftsChainLow_lt index coord selected chain step
  unfold ftsChainHeaderP
  rw [BitVec.toNat_append, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hlt : ftsChainLow index coord selected chain step < 2 ^ 64 := by omega
  rw [← Nat.shiftLeft_add_eq_or_of_lt hlt, Nat.shiftLeft_eq]
theorem ftsChainHeader_toNat (index coord selected chain step : Nat) :
    (ftsChainHeader index coord selected chain step).toNat = ftsChainLow index coord selected chain step := by
  unfold ftsChainHeader
  rw [ftsChainHeaderP_toNat]
  simp
theorem ftsChainHeaderP_low (index coord selected chain step : Nat) (high : BitVec 64) :
    (ftsChainHeaderP index coord selected chain step high).extractLsb' 0 64 =
      BitVec.ofNat 64 (ftsChainLow index coord selected chain step) :=
  BitVec.extractLsb'_append_eq_right
theorem ftsChainHeaderP_high (index coord selected chain step : Nat) (high : BitVec 64) :
    (ftsChainHeaderP index coord selected chain step high).extractLsb' 64 64 = high :=
  BitVec.extractLsb'_append_eq_left
theorem ftsChainHeaderP_injective {i k j t s i' k' j' t' s' : Nat} {high high' : BitVec 64}
    (hi : i < 2 ^ 31) (hk : k < 16) (hj : j < 128) (ht : t < 8) (hs : s < 4)
    (hi' : i' < 2 ^ 31) (hk' : k' < 16) (hj' : j' < 128) (ht' : t' < 8) (hs' : s' < 4)
    (h : ftsChainHeaderP i k j t s high = ftsChainHeaderP i' k' j' t' s' high') :
    i = i' ∧ k = k' ∧ j = j' ∧ t = t' ∧ s = s' ∧ high = high' := by
  have hlo := congrArg (fun x : BitVec 128 => x.extractLsb' 0 64) h
  have hhi := congrArg (fun x : BitVec 128 => x.extractLsb' 64 64) h
  simp only [ftsChainHeaderP_low, ftsChainHeaderP_high] at hlo hhi
  have hq := congrArg BitVec.toNat hlo
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_trans (ftsChainLow_lt ..) (by decide)),
    Nat.mod_eq_of_lt (lt_trans (ftsChainLow_lt ..) (by decide))] at hq
  obtain ⟨e1, e2, e3, e4, e5⟩ := ftsChainLow_injective hi hk hj ht hs hi' hk' hj' ht' hs' hq
  exact ⟨e1, e2, e3, e4, e5, hhi⟩
theorem chainInput_eq (index coord selected chain step : Nat) (value : Digest) :
    chainInput index coord selected chain step value =
      zero16 ++ bytesLE 16 (ftsChainHeader index coord selected chain step) ++
        zero16 ++ bytesLE 16 value := rfl
theorem ftsLeafLow_lt (index coord selected : Nat) : ftsLeafLow index coord selected < 2 ^ 58 := by
  unfold ftsLeafLow
  have := Nat.mod_lt coord (show 0 < 16 by decide)
  have := Nat.mod_lt selected (show 0 < 128 by decide)
  have := Nat.mod_lt index (show 0 < 2 ^ 31 by decide)
  norm_num only at *
  omega
theorem ftsLeafLow_byte0 (index coord selected : Nat) : ftsLeafLow index coord selected % 256 = 1 := by
  unfold ftsLeafLow
  omega
theorem ftsLeafLow_byte1 (index coord selected : Nat) : ftsLeafLow index coord selected / 2 ^ 8 % 256 = 6 := by
  unfold ftsLeafLow
  omega
theorem ftsLeafLow_injective {i k j i' k' j' : Nat}
    (hi : i < 2 ^ 31) (hk : k < 16) (hj : j < 128) (hi' : i' < 2 ^ 31) (hk' : k' < 16) (hj' : j' < 128)
    (h : ftsLeafLow i k j = ftsLeafLow i' k' j') : i = i' ∧ k = k' ∧ j = j' := by
  unfold ftsLeafLow at h
  rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hi',
    Nat.mod_eq_of_lt hk', Nat.mod_eq_of_lt hj'] at h
  norm_num only at h hi hi'
  omega
theorem ftsLeafHeader_toNat (index coord selected : Nat) :
    (ftsLeafHeader index coord selected).toNat = ftsLeafLow index coord selected := by
  have hq := ftsLeafLow_lt index coord selected
  unfold ftsLeafHeader
  rw [BitVec.toNat_append, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_trans hq (by decide))]
  simp
theorem ftsLeafHeader_low (index coord selected : Nat) :
    (ftsLeafHeader index coord selected).extractLsb' 0 64 = BitVec.ofNat 64 (ftsLeafLow index coord selected) :=
  BitVec.extractLsb'_append_eq_right
theorem ftsLeafHeader_high (index coord selected : Nat) :
    (ftsLeafHeader index coord selected).extractLsb' 64 64 = 0 :=
  BitVec.extractLsb'_append_eq_left
theorem ftsLeafHeader_firstByte (index coord selected : Nat) :
    (ftsLeafHeader index coord selected).toNat % 256 = 1 := by
  rw [ftsLeafHeader_toNat, ftsLeafLow_byte0]
theorem ftsLeafHeader_byte1 (index coord selected : Nat) :
    (ftsLeafHeader index coord selected).toNat / 2 ^ 8 % 256 = 6 := by
  rw [ftsLeafHeader_toNat, ftsLeafLow_byte1]
theorem ftsLeafHeader_injective {i k j i' k' j' : Nat}
    (hi : i < 2 ^ 31) (hk : k < 16) (hj : j < 128) (hi' : i' < 2 ^ 31) (hk' : k' < 16) (hj' : j' < 128)
    (h : ftsLeafHeader i k j = ftsLeafHeader i' k' j') : i = i' ∧ k = k' ∧ j = j' := by
  have hq := congrArg BitVec.toNat h
  rw [ftsLeafHeader_toNat, ftsLeafHeader_toNat] at hq
  exact ftsLeafLow_injective hi hk hj hi' hk' hj' hq
theorem wctNodeHeader_eq {coord : Nat} (hk : coord < 9) (index heap : Nat) :
    wctNodeHeader coord index heap = BitVec.ofNat 64 heap ++ BitVec.ofNat 64 (ftsLeafLow index coord 0) := by
  unfold wctNodeHeader nodeLayer
  rw [nodeTweak_fts (by omega) (by omega), show 4 + coord - 4 = coord by omega]
  rfl
theorem wctNodeHeader_toNat {coord : Nat} (hk : coord < 9) (index heap : Nat) :
    (wctNodeHeader coord index heap).toNat = heap % 2 ^ 64 * 2 ^ 64 + ftsLeafLow index coord 0 := by
  rw [wctNodeHeader_eq hk, append64_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (lt_trans (ftsLeafLow_lt _ _ _) (by decide))]
theorem wctNodeHeader_low {coord : Nat} (hk : coord < 9) (index heap : Nat) :
    (wctNodeHeader coord index heap).extractLsb' 0 64 = BitVec.ofNat 64 (ftsLeafLow index coord 0) := by
  rw [wctNodeHeader_eq hk]; exact BitVec.extractLsb'_append_eq_right
theorem wctNodeHeader_high {coord : Nat} (hk : coord < 9) (index heap : Nat) :
    (wctNodeHeader coord index heap).extractLsb' 64 64 = BitVec.ofNat 64 heap := by
  rw [wctNodeHeader_eq hk]; exact BitVec.extractLsb'_append_eq_left
theorem wctNodeHeader_firstByte (coord index heap : Nat) : (wctNodeHeader coord index heap).toNat % 256 = 1 := by
  have h := nodeTweak_marker 3 (nodeLayer coord) index heap
  unfold tweakMarker at h
  unfold wctNodeHeader
  rw [h, if_neg (by unfold nodeLayer; omega)]
theorem wctNodeHeader_byte1 {coord : Nat} (hk : coord < 9) (index heap : Nat) :
    (wctNodeHeader coord index heap).toNat / 2 ^ 8 % 256 = 6 := by
  rw [wctNodeHeader_toNat hk]
  have := ftsLeafLow_byte1 index coord 0
  omega
theorem wctNodeHeader_injective {k i h k' i' h' : Nat}
    (hk : k < 9) (hi : i < 2 ^ 31) (hh : h < 2 ^ 64) (hk' : k' < 9) (hi' : i' < 2 ^ 31) (hh' : h' < 2 ^ 64)
    (he : wctNodeHeader k i h = wctNodeHeader k' i' h') : k = k' ∧ i = i' ∧ h = h' := by
  unfold wctNodeHeader nodeLayer at he
  obtain ⟨e1, e2, e3⟩ := nodeTweak_fts_injective (by omega) (by omega) (by omega) (by omega) hi hi' hh hh' he
  exact ⟨by omega, e2, e3⟩
theorem ftsLeafHeader_ne_wctNodeHeader (index coord selected : Nat) {coord' : Nat} (hk : coord' < 9)
    (index' heap : Nat) (hh : heap % 2 ^ 64 ≠ 0) :
    ftsLeafHeader index coord selected ≠ wctNodeHeader coord' index' heap := by
  intro h
  have hhi := congrArg BitVec.toNat (congrArg (fun x : BitVec 128 => x.extractLsb' 64 64) h)
  simp only [ftsLeafHeader_high, wctNodeHeader_high hk, BitVec.toNat_ofNat] at hhi
  exact hh hhi.symm
theorem radix_inj {B a a' m m' : Nat} (h : a + B * m = a' + B * m') (ha : a < B) (ha' : a' < B) :
    a = a' ∧ m = m' := by
  have hB : 0 < B := by omega
  have h1 := congrArg (· % B) h
  have h2 := congrArg (· / B) h
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha'] at h1
  simp only [Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt ha, Nat.div_eq_of_lt ha',
    Nat.zero_add] at h2
  exact ⟨h1, h2⟩
def headerValue (tag lay tree position index : Nat) : Nat :=
  1 + tag % 256 * 2 ^ 8 + lay % 256 * 2 ^ 16 + (tree / 2 ^ 32 % 256) * 2 ^ 24 +
    position % 2 ^ 32 * 2 ^ 32 + tree % 2 ^ 32 * 2 ^ 64 + index % 2 ^ 32 * 2 ^ 96
theorem headerValue_nested (tag lay tree position index : Nat) :
    headerValue tag lay tree position index =
      1 + 256 * (tag % 256 + 256 * (lay % 256 + 256 * (tree / 2 ^ 32 % 256 +
        256 * (position % 2 ^ 32 + 2 ^ 32 * (tree % 2 ^ 32 + 2 ^ 32 * (index % 2 ^ 32)))))) := by
  unfold headerValue
  ring
theorem headerValue_lt (tag lay tree position index : Nat) :
    headerValue tag lay tree position index < 2 ^ 128 := by
  rw [headerValue_nested]
  have h1 := Nat.mod_lt tag (show 0 < 256 by decide)
  have h2 := Nat.mod_lt lay (show 0 < 256 by decide)
  have h3 := Nat.mod_lt (tree / 2 ^ 32) (show 0 < 256 by decide)
  have h4 := Nat.mod_lt position (show 0 < 2 ^ 32 by decide)
  have h5 := Nat.mod_lt tree (show 0 < 2 ^ 32 by decide)
  have h6 := Nat.mod_lt index (show 0 < 2 ^ 32 by decide)
  generalize tag % 256 = a1 at *
  generalize lay % 256 = a2 at *
  generalize tree / 2 ^ 32 % 256 = a3 at *
  generalize position % 2 ^ 32 = a4 at *
  generalize tree % 2 ^ 32 = a5 at *
  generalize index % 2 ^ 32 = a6 at *
  norm_num only at h1 h2 h3 h4 h5 h6 ⊢
  omega
theorem wctHeader_toNat (tag lay tree position index : Nat) :
    (wctHeader tag lay tree position index).toNat = headerValue tag lay tree position index := by
  unfold wctHeader
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (headerValue_lt _ _ _ _ _)
theorem headerValue_inj {tag lay tree position index tag' lay' tree' position' index' : Nat}
    (h : headerValue tag lay tree position index = headerValue tag' lay' tree' position' index') :
    tag % 256 = tag' % 256 ∧ lay % 256 = lay' % 256 ∧ tree / 2 ^ 32 % 256 = tree' / 2 ^ 32 % 256 ∧
      position % 2 ^ 32 = position' % 2 ^ 32 ∧ tree % 2 ^ 32 = tree' % 2 ^ 32 ∧
      index % 2 ^ 32 = index' % 2 ^ 32 := by
  rw [headerValue_nested, headerValue_nested] at h
  have h0 := Nat.add_left_cancel h
  obtain ⟨e1, h1⟩ := radix_inj (Nat.eq_of_mul_eq_mul_left (by decide) h0)
    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
  obtain ⟨e2, h2⟩ := radix_inj h1 (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
  obtain ⟨e3, h3⟩ := radix_inj h2 (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
  obtain ⟨e4, h4⟩ := radix_inj h3 (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
  obtain ⟨e5, h5⟩ := radix_inj h4 (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
  exact ⟨e1, e2, e3, e4, e5, h5⟩
theorem tree_of_split {tree tree' : Nat} (ht : tree < 2 ^ 40) (ht' : tree' < 2 ^ 40)
    (hhi : tree / 2 ^ 32 % 256 = tree' / 2 ^ 32 % 256) (hlo : tree % 2 ^ 32 = tree' % 2 ^ 32) :
    tree = tree' := by
  have hq : tree / 2 ^ 32 < 256 := Nat.div_lt_of_lt_mul (by norm_num at ht ⊢; omega)
  have hq' : tree' / 2 ^ 32 < 256 := Nat.div_lt_of_lt_mul (by norm_num at ht' ⊢; omega)
  rw [Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt hq'] at hhi
  rw [← Nat.div_add_mod tree (2 ^ 32), ← Nat.div_add_mod tree' (2 ^ 32), hhi, hlo]
theorem wctHeader_inj {tag lay tree position index tag' lay' tree' position' index' : Nat}
    (ht : tag < 256) (hl : lay < 256) (htr : tree < 2 ^ 40) (hp : position < 2 ^ 32)
    (hi : index < 2 ^ 32) (ht' : tag' < 256) (hl' : lay' < 256) (htr' : tree' < 2 ^ 40)
    (hp' : position' < 2 ^ 32) (hi' : index' < 2 ^ 32)
    (h : wctHeader tag lay tree position index = wctHeader tag' lay' tree' position' index') :
    tag = tag' ∧ lay = lay' ∧ tree = tree' ∧ position = position' ∧ index = index' := by
  have hn := congrArg BitVec.toNat h
  rw [wctHeader_toNat, wctHeader_toNat] at hn
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := headerValue_inj hn
  rw [Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt ht'] at e1
  rw [Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hl'] at e2
  rw [Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hp'] at e4
  rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hi'] at e6
  exact ⟨e1, e2, tree_of_split htr htr' e3 e5, e4, e6⟩
theorem serializeOpening_length (opened : Opening) : (serializeOpening opened).length = 208 := by
  simp only [serializeOpening, List.length_append, digest_list_bytes_length, List.length_ofFn]
theorem serialize_length (sig : Signature) : (serialize sig).length = 5312 := by
  simp only [serialize, List.length_append, bytesLE_length, List.length_flatMap,
    List.map_ofFn, Function.comp_def, List.length_flatten]
  simp_rw [serializeOpening_length, serializeLayer_length]
  decide
theorem serializeOpening_injective : Function.Injective serializeOpening := by
  rintro ⟨lv, lp⟩ ⟨rv, rp⟩ h
  simp only [serializeOpening] at h
  obtain ⟨hv, hp⟩ := List.append_inj h (by simp only [digest_list_bytes_length, List.length_ofFn])
  have hv := SphincsSecurity.flatMap_bytesLE_ofFn_injective hv
  have hp := SphincsSecurity.flatMap_bytesLE_ofFn_injective hp
  subst rv rp
  rfl
theorem serialize_injective : Function.Injective serialize := by
  rintro ⟨lr, lo, ll⟩ ⟨rr, ro, rl⟩ h
  simp only [serialize] at h
  have hopen (o : Coord → Opening) :
      ((List.ofFn o).flatMap serializeOpening).length = 1872 := by
    simp only [List.length_flatMap, List.map_ofFn, Function.comp_def, serializeOpening_length]
    decide
  obtain ⟨hhead, hlayers⟩ := List.append_inj h (by
    simp only [List.length_append, bytesLE_length, hopen])
  obtain ⟨hrho, hopenings⟩ := List.append_inj hhead (by simp only [bytesLE_length])
  have hrho := bytesLE_injective hrho
  rw [List.flatMap_def, List.flatMap_def, List.map_ofFn, List.map_ofFn] at hopenings
  have ho := SphincsSecurity.length_flatten_ofFn_eq _ _
    (fun coord => by
      simp only [Function.comp_apply, serializeOpening_length]) hopenings
  have ho' : lo = ro := funext fun coord => serializeOpening_injective (congrFun ho coord)
  have hl := SphincsSecurity.length_flatten_ofFn_eq _ _
    (fun lay => by rw [serializeLayer_length, serializeLayer_length]) hlayers
  have hl' : ll = rl := funext fun lay => serializeLayer_injective lay (congrFun hl lay)
  subst rr ro rl
  rfl
theorem child_val (output : HashOutput) (coord : Coord) :
    (child output coord).val = output.toNat / 2 ^ childBase coord.val % 128 := rfl
theorem field_val (output : HashOutput) (coord : Coord) :
    field output coord = output.toNat / 2 ^ fieldBase coord.val % 2 ^ 10 := rfl
theorem digestIndex_val (output : HashOutput) : digestIndex output = output.toNat / 2 ^ 33 % 2 ^ 31 := rfl
theorem field_lt (output : HashOutput) (coord : Coord) : field output coord < 2 ^ 10 :=
  Nat.mod_lt _ (by decide)
theorem rank_val (output : HashOutput) (coord : Coord) :
    (rank output coord).val = field output coord % 563 := rfl
theorem admissible_iff (output : HashOutput) :
    admissible output = true ↔
      output.toNat / 2 ^ 242 % 2 ^ 14 < 1131 ∧ ∀ coord : Coord, field output coord < 563 := by
  unfold admissible field
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  constructor
  · rintro ⟨hg, hf⟩
    exact ⟨hg, fun coord => hf coord.val coord.isLt⟩
  · rintro ⟨hg, hf⟩
    exact ⟨hg, fun coord hc => hf ⟨coord, hc⟩⟩
theorem admissible_field_split (output : HashOutput) (h : admissible output = true)
    (coord : Coord) :
    field output coord = (rank output coord).val + 563 * (field output coord / 563) ∧
      field output coord / 563 < 1 := by
  have hf := ((admissible_iff output).1 h).2 coord
  rw [rank_val]
  omega
theorem rank_fiber_card (r : Rank) :
    ((Finset.range 563).filter (fun f => f % 563 = r.val)).card = 1 := by
  have he : (Finset.range 563).filter (fun f => f % 563 = r.val) =
      (Finset.range 1).image (fun q => r.val + 563 * q) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    have hr := r.isLt
    constructor
    · rintro ⟨hf, hm⟩
      exact ⟨f / 563, by omega, by omega⟩
    · rintro ⟨q, hq, rfl⟩
      constructor <;> omega
  rw [he, Finset.card_image_of_injective _
    (fun a b hab => Nat.eq_of_mul_eq_mul_left (by decide) (Nat.add_left_cancel hab))]
  simp
def acceptedFieldEquiv : Fin 563 ≃ Rank × Fin 1 where
  toFun f := (⟨f.val % 563, Nat.mod_lt _ (by decide)⟩, ⟨f.val / 563, by omega⟩)
  invFun p := ⟨p.1.val + 563 * p.2.val, by omega⟩
  left_inv f := by apply Fin.ext; simp only; omega
  right_inv p := by
    apply Prod.ext <;> apply Fin.ext <;> simp only <;> omega
theorem acceptedFieldEquiv_rank (f : Fin 563) :
    (acceptedFieldEquiv f).1.val = f.val % 563 := rfl
def digestLayout : List (Nat × Nat) :=
  [(0, 7), (7, 10), (17, 16), (33, 31),
   (64, 7), (71, 10), (81, 4), (85, 7), (92, 10), (102, 5), (107, 10), (117, 4), (121, 7),
   (128, 7), (135, 10), (145, 4), (149, 7), (156, 10), (166, 5), (171, 10), (181, 4), (185, 7),
   (192, 7), (199, 10), (209, 4), (213, 7), (220, 10), (230, 12), (242, 14)]
theorem childBase_values :
    List.ofFn (fun k : Coord => childBase k.val) = [0, 64, 85, 121, 128, 149, 185, 192, 213] := by
  decide
theorem fieldBase_values :
    List.ofFn (fun k : Coord => fieldBase k.val) = [7, 71, 92, 107, 135, 156, 171, 199, 220] := by
  decide
theorem digestLayout_tiles :
    digestLayout.map Prod.fst = ((digestLayout.map Prod.snd).scanl (· + ·) 0).dropLast ∧
      (digestLayout.map Prod.snd).sum = 256 ∧ ∀ p ∈ digestLayout, 0 < p.2 := by
  decide
theorem digestLayout_index : (indexShift, 31) ∈ digestLayout := by decide
theorem digestLayout_child (k : Coord) : (childBase k.val, 7) ∈ digestLayout := by
  revert k; decide
theorem digestLayout_field (k : Coord) : (fieldBase k.val, 10) ∈ digestLayout := by
  revert k; decide
theorem digestLayout_disjoint :
    digestLayout.Pairwise (fun p q => p.1 + p.2 ≤ q.1) ∧
      ∀ p ∈ digestLayout, p.1 + p.2 ≤ 256 := by
  decide
theorem childBase_word_aligned (k : Coord) :
    childBase k.val / 64 = (childBase k.val + 6) / 64 ∧ childBase k.val + 7 ≤ 234 := by
  revert k; decide
theorem fieldBase_word_aligned (k : Coord) :
    fieldBase k.val / 64 = (fieldBase k.val + 9) / 64 ∧ fieldBase k.val + 10 ≤ 234 := by
  revert k; decide
theorem childBase_disjoint (k l : Coord) (h : k ≠ l) :
    childBase k.val + 7 ≤ childBase l.val ∨ childBase l.val + 7 ≤ childBase k.val := by
  revert k l; decide
theorem fieldBase_disjoint (k l : Coord) (h : k ≠ l) :
    fieldBase k.val + 10 ≤ fieldBase l.val ∨ fieldBase l.val + 10 ≤ fieldBase k.val := by
  revert k l; decide
theorem childBase_fieldBase_disjoint (k l : Coord) :
    childBase k.val + 7 ≤ fieldBase l.val ∨ fieldBase l.val + 10 ≤ childBase k.val := by
  revert k l; decide
theorem index_disjoint (k : Coord) :
    (childBase k.val + 7 ≤ 33 ∨ 64 ≤ childBase k.val) ∧ (fieldBase k.val + 10 ≤ 33 ∨ 64 ≤ fieldBase k.val) := by
  revert k; decide
theorem coordinate_verify_steps (output : HashOutput) (coord : Coord) :
    (∑ t : Fin 6, (List.range' (4 - wordDigit (rank output coord) t)
      (wordDigit (rank output coord) t)).length) = 7 := by
  simp only [List.length_range']
  exact wordStep_count _
theorem verify_walk_positions (word : Rank) (t : Fin 6) :
    (∀ s ∈ List.range' (4 - wordDigit word t) (wordDigit word t), s < 4) ∧
      4 - wordDigit word t + wordDigit word t = 4 := by
  have hd := wordDigit_le_four word t
  refine ⟨fun s hs => ?_, by omega⟩
  rw [List.mem_range'] at hs
  omega
theorem verify_steps_total (output : HashOutput) :
    (∑ coord : Coord, ∑ t : Fin 6, wordDigit (rank output coord) t) = 63 := by
  simp only [wordStep_count, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
theorem gate_value (output : HashOutput) : output.toNat / 2 ^ 242 % 2 ^ 14 = output.toNat / 2 ^ 242 := by
  have h := output.isLt
  apply Nat.mod_eq_of_lt
  rw [Nat.div_lt_iff_lt_mul (by positivity)]
  norm_num at h ⊢
  omega
theorem admissible_iff' (output : HashOutput) :
    admissible output = true ↔
      output.toNat / 2 ^ 242 < gateLimit ∧ ∀ coord : Coord, field output coord < fieldLimit := by
  rw [admissible_iff, gate_value]; rfl
theorem jointCost_eq_sum (output : HashOutput) :
    jointCost output = ∑ coord : Coord, (routineCost (rank output coord) + childExtra (child output coord)) := by
  unfold jointCost
  rw [← List.sum_ofFn]
  congr 1
theorem childExtra_le (c : Child) : childExtra c ≤ 3 := by
  unfold childExtra maxChildSave; omega
theorem jointCost_bounds (output : HashOutput) : 675 ≤ jointCost output ∧ jointCost output ≤ 828 := by
  rw [jointCost_eq_sum]
  have hb := fun coord => routineCost_bounds (rank output coord)
  have he := fun coord => childExtra_le (child output coord)
  constructor
  · calc 675 = ∑ _coord : Coord, 75 := by simp
      _ ≤ _ := Finset.sum_le_sum fun coord _ => le_trans (hb coord).1 (Nat.le_add_right _ _)
  · calc _ ≤ ∑ _coord : Coord, 92 := Finset.sum_le_sum fun coord _ => by
          have := (hb coord).2; have := he coord; omega
      _ = 828 := by simp
theorem capOk_iff (output : HashOutput) : capOk output = true ↔ jointCost output ≤ jointCap := by
  simp [capOk]
theorem producerAdmissible_iff (output : HashOutput) :
    producerAdmissible output = true ↔ admissible output = true ∧ jointCost output ≤ jointCap := by
  simp [producerAdmissible, capOk_iff]
theorem admissible_of_producer {output : HashOutput} (h : producerAdmissible output = true) :
    admissible output = true := ((producerAdmissible_iff output).1 h).1
/-- Coefficient `j < 102` of the FTS seed family of `(index, coord)` (campaign X1, stage A): half `j % 2` of the
private pair `ftsSeedPair index coord (j / 2)`. -/
def ftsCoef (answers : SigGolfCandidate.T3.Correctness.Answers) (index coord : Nat) (j : Fin 102) : Digest :=
  seedHalf (evalWithAnswerFn answers (ftsSeedPair index coord (j.val / 2))) j.val
end ClaudeWCT.WCT9
