import SigGolfCandidate.ClaudeWCT.WCT9.Basic
import SigGolfCandidate.T3.PackedChain

namespace ClaudeWCT.WCT9
open OracleComp OracleSpec SigGolfCandidate.T3
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
theorem header_byte1 (tag lay tree position index : Nat) :
    (header tag lay tree position index).toNat / 2 ^ 8 % 256 = tag % 256 := by
  rw [header_toNat]
  have := Nat.mod_lt tag (show 0 < 256 by decide)
  have := Nat.mod_lt lay (show 0 < 256 by decide)
  split <;> omega
theorem header_byte2 (tag lay tree position index : Nat) :
    (header tag lay tree position index).toNat / 2 ^ 16 % 256 = lay % 256 := by
  rw [header_toNat]
  have := Nat.mod_lt tag (show 0 < 256 by decide)
  have := Nat.mod_lt lay (show 0 < 256 by decide)
  split <;> omega
theorem ftsChainHeaderP_firstByte (index coord selected chain step : Nat) (high : BitVec 64) :
    (ftsChainHeaderP index coord selected chain step high).toNat % 256 = 128 + 4 * (chain % 8) := by
  rw [ftsChainHeaderP_toNat, ← ftsChainLow_byte0 index coord selected chain step]
  omega
theorem ftsChainHeaderP_ne_header (index coord selected chain step : Nat) (high : BitVec 64)
    (tag lay tree position idx : Nat) :
    ftsChainHeaderP index coord selected chain step high ≠ header tag lay tree position idx := by
  intro h
  have hc := ftsChainHeaderP_firstByte index coord selected chain step high
  rw [h, header_firstByte] at hc
  omega
theorem chainHeader_low_band (lay : Layer) (tree leaf i step : Nat) :
    193 * 2 ^ 56 ≤ ((chainHeader lay tree leaf i step).extractLsb' 0 64).toNat ∧
      ((chainHeader lay tree leaf i step).extractLsb' 0 64).toNat < 194 * 2 ^ 56 := by
  rw [chainHeader_low, chainHeaderFlaggedLow_toNat]
  have hb := chainHeaderLow_band lay tree leaf i step
  split_ifs <;> omega
theorem ftsChainHeaderP_low_ne_chainHeader (index coord selected chain step : Nat) (high : BitVec 64)
    (lay : Layer) (tree leaf i st : Nat) :
    (ftsChainHeaderP index coord selected chain step high).extractLsb' 0 64 ≠
      (chainHeader lay tree leaf i st).extractLsb' 0 64 := by
  intro h
  have hw := chainHeader_low_band lay tree leaf i st
  rw [← h, ftsChainHeaderP_low, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (lt_trans (ftsChainLow_lt ..) (by decide))] at hw
  have := ftsChainLow_lt index coord selected chain step
  omega
theorem ftsChainHeaderP_ne_chainHeader (index coord selected chain step : Nat) (high : BitVec 64)
    (lay : Layer) (tree leaf i st : Nat) :
    ftsChainHeaderP index coord selected chain step high ≠ chainHeader lay tree leaf i st := fun h =>
  ftsChainHeaderP_low_ne_chainHeader index coord selected chain step high lay tree leaf i st
    (congrArg (fun x : BitVec 128 => x.extractLsb' 0 64) h)
theorem ftsLeafHeader_ne_header (index coord selected tag lay tree position idx : Nat) (ht : tag % 256 ≠ 6) :
    ftsLeafHeader index coord selected ≠ header tag lay tree position idx := by
  intro h
  have h1 := ftsLeafHeader_byte1 index coord selected
  rw [h, header_byte1] at h1
  exact ht h1
theorem ftsLeafHeader_ne_chainHeader (index coord selected : Nat) (lay : Layer) (tree leaf i st : Nat) :
    ftsLeafHeader index coord selected ≠ chainHeader lay tree leaf i st := by
  intro h
  have hc := chainHeader_firstByte lay tree leaf i st
  rw [← h, ftsLeafHeader_firstByte] at hc
  omega
theorem ftsLeafHeader_ne_ftsChainHeaderP (index coord selected : Nat) (i k j t s : Nat) (high : BitVec 64) :
    ftsLeafHeader index coord selected ≠ ftsChainHeaderP i k j t s high := by
  intro h
  have hc := ftsChainHeaderP_firstByte i k j t s high
  rw [← h, ftsLeafHeader_firstByte] at hc
  omega
theorem wctNodeHeader_ne_chainHeader (coord index heap : Nat) (lay : Layer) (tree leaf i st : Nat) :
    wctNodeHeader coord index heap ≠ chainHeader lay tree leaf i st := by
  intro h
  have hc := chainHeader_firstByte lay tree leaf i st
  rw [← h, wctNodeHeader_firstByte] at hc
  omega
theorem wctNodeHeader_ne_header {coord : Nat} (hk : coord < 9) (index heap tag lay tree position idx : Nat)
    (ht : tag % 256 ≠ 6) : wctNodeHeader coord index heap ≠ header tag lay tree position idx := by
  intro h
  have h1 := wctNodeHeader_byte1 hk index heap
  rw [h, header_byte1] at h1
  exact ht h1
theorem wctNodeHeader_ne_ftsChainHeaderP (coord index heap : Nat) (i k j t s : Nat) (high : BitVec 64) :
    wctNodeHeader coord index heap ≠ ftsChainHeaderP i k j t s high := by
  intro h
  have hc := ftsChainHeaderP_firstByte i k j t s high
  rw [← h, wctNodeHeader_firstByte] at hc
  omega
theorem ftsLeafHeader_tweakMarker (index coord selected : Nat) : tweakMarker (ftsLeafHeader index coord selected) = 1 :=
  ftsLeafHeader_firstByte index coord selected
theorem ftsLeafHeader_tweakTag (index coord selected : Nat) : tweakTag (ftsLeafHeader index coord selected) = 6 := by
  unfold tweakTag; have := ftsLeafHeader_byte1 index coord selected; norm_num at this ⊢; omega
theorem wctNodeHeader_tweakMarker (coord index heap : Nat) : tweakMarker (wctNodeHeader coord index heap) = 1 :=
  wctNodeHeader_firstByte coord index heap
theorem wctNodeHeader_tweakTag {coord : Nat} (hk : coord < 9) (index heap : Nat) :
    tweakTag (wctNodeHeader coord index heap) = 6 := by
  unfold tweakTag; have := wctNodeHeader_byte1 hk index heap; norm_num at this ⊢; omega
theorem ftsChainHeaderP_tweakMarker (index coord selected chain step : Nat) (high : BitVec 64) :
    128 ≤ tweakMarker (ftsChainHeaderP index coord selected chain step high) := by
  unfold tweakMarker; rw [ftsChainHeaderP_firstByte]; omega
theorem ftsLeafHeader_ne_rowTweak (index coord selected : Nat) (lay : Layer) (tree leaf : Nat) :
    ftsLeafHeader index coord selected ≠ rowTweak lay tree leaf :=
  ne_of_tweakTag (by rw [ftsLeafHeader_tweakTag, rowTweak_tag]; decide)
theorem ftsLeafHeader_ne_leafTweak (index coord selected : Nat) (lay : Layer) (tree leaf : Nat) :
    ftsLeafHeader index coord selected ≠ leafTweak lay tree leaf :=
  ne_of_tweakTag (by rw [ftsLeafHeader_tweakTag, leafTweak_tag]; decide)
theorem ftsLeafHeader_ne_digestHeader (index coord selected : Nat) (counter : BitVec 32) :
    ftsLeafHeader index coord selected ≠ digestHeader counter :=
  ne_of_tweakMarker (by rw [ftsLeafHeader_tweakMarker, digestHeader_marker]; decide)
theorem wctNodeHeader_ne_rowTweak {coord : Nat} (hk : coord < 9) (index heap : Nat) (lay : Layer) (tree leaf : Nat) :
    wctNodeHeader coord index heap ≠ rowTweak lay tree leaf :=
  ne_of_tweakTag (by rw [wctNodeHeader_tweakTag hk, rowTweak_tag]; decide)
theorem wctNodeHeader_ne_leafTweak {coord : Nat} (hk : coord < 9) (index heap : Nat) (lay : Layer) (tree leaf : Nat) :
    wctNodeHeader coord index heap ≠ leafTweak lay tree leaf :=
  ne_of_tweakTag (by rw [wctNodeHeader_tweakTag hk, leafTweak_tag]; decide)
theorem wctNodeHeader_ne_digestHeader (coord index heap : Nat) (counter : BitVec 32) :
    wctNodeHeader coord index heap ≠ digestHeader counter :=
  ne_of_tweakMarker (by rw [wctNodeHeader_tweakMarker, digestHeader_marker]; decide)
theorem ftsChainHeaderP_ne_rowTweak (index coord selected chain step : Nat) (high : BitVec 64) (lay : Layer)
    (tree leaf : Nat) : ftsChainHeaderP index coord selected chain step high ≠ rowTweak lay tree leaf := by
  apply ne_of_tweakMarker
  have := ftsChainHeaderP_tweakMarker index coord selected chain step high
  rw [rowTweak_marker]; omega
theorem ftsChainHeaderP_ne_leafTweak (index coord selected chain step : Nat) (high : BitVec 64) (lay : Layer)
    (tree leaf : Nat) : ftsChainHeaderP index coord selected chain step high ≠ leafTweak lay tree leaf := by
  apply ne_of_tweakMarker
  have := ftsChainHeaderP_tweakMarker index coord selected chain step high
  rw [leafTweak_marker]; omega
theorem ftsChainHeaderP_ne_digestHeader (index coord selected chain step : Nat) (high : BitVec 64)
    (counter : BitVec 32) : ftsChainHeaderP index coord selected chain step high ≠ digestHeader counter := by
  apply ne_of_tweakMarker
  have := ftsChainHeaderP_tweakMarker index coord selected chain step high
  rw [digestHeader_marker]; omega
theorem pairs_bytes_length (pairs : List (Digest × Digest)) :
    (pairs.flatMap (fun p => bytesLE 16 p.1 ++ bytesLE 16 p.2)).length = 32 * pairs.length := by
  induction pairs with
  | nil => rfl
  | cons p ps ih => simp only [List.flatMap_cons, List.length_append, bytesLE_length, ih, List.length_cons]; ring
theorem pairs_bytes_injective : ∀ {ps qs : List (Digest × Digest)}, ps.length = qs.length →
    ps.flatMap (fun p => bytesLE 16 p.1 ++ bytesLE 16 p.2) = qs.flatMap (fun p => bytesLE 16 p.1 ++ bytesLE 16 p.2) →
      ps = qs
  | [], [], _, _ => rfl
  | p :: ps, q :: qs, hl, h => by
      simp only [List.flatMap_cons] at h
      obtain ⟨hpq, hrest⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
      obtain ⟨h1, h2⟩ := List.append_inj hpq (by simp only [bytesLE_length])
      rw [show p = q from Prod.ext (bytesLE_injective h1) (bytesLE_injective h2),
        pairs_bytes_injective (by simpa using hl) hrest]
theorem forestInput_length (index : Nat) (pairs : List (Digest × Digest)) (h : pairs.length = 9) :
    (forestInput index pairs).length = 320 := by
  simp only [forestInput, zero16, List.length_append, List.length_replicate, bytesLE_length, pairs_bytes_length, h]
theorem forestInput_injective {index index' : Nat} {pairs pairs' : List (Digest × Digest)}
    (hi : index < 2 ^ 40) (hi' : index' < 2 ^ 40) (hl : pairs.length = pairs'.length)
    (h : forestInput index pairs = forestInput index' pairs') : index = index' ∧ pairs = pairs' := by
  unfold forestInput at h
  obtain ⟨hh, hp⟩ := List.append_inj h (by simp only [zero16, List.length_append, List.length_replicate,
    bytesLE_length])
  obtain ⟨-, hh⟩ := List.append_inj hh (by simp only [zero16, List.length_replicate])
  obtain ⟨-, -, e, -, -⟩ := header_injective (by decide) (by decide) hi (by norm_num) (by norm_num)
    (by decide) (by decide) hi' (by norm_num) (by norm_num) (bytesLE_injective hh)
  exact ⟨e, pairs_bytes_injective hl hp⟩
theorem pairEncodingInputP_length (up : Layer) (tree leaf : Nat) (left right : Digest) (counter : BitVec 32)
    (pad : BitVec 96) : (pairEncodingInputP up tree leaf left right counter pad).length = 64 := by
  simp only [pairEncodingInputP, List.length_append, bytesLE_length]
theorem pairEncodingInputP_injective {up up' : Layer} {tree leaf tree' leaf' : Nat} {l r l' r' : Digest}
    {c c' : BitVec 32} {pad pad' : BitVec 96}
    (hl : leaf < 2 ^ height up) (hr : tree * 2 ^ height up + leaf < 2 ^ 32)
    (hl' : leaf' < 2 ^ height up') (hr' : tree' * 2 ^ height up' + leaf' < 2 ^ 32)
    (h : pairEncodingInputP up tree leaf l r c pad = pairEncodingInputP up' tree' leaf' l' r' c' pad') :
    up = up' ∧ tree = tree' ∧ leaf = leaf' ∧ l = l' ∧ r = r' ∧ c = c' ∧ pad = pad' := by
  unfold pairEncodingInputP at h
  obtain ⟨h, hR⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨h, hp⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨h, hc⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨hL, hh⟩ := List.append_inj h (by simp only [bytesLE_length])
  obtain ⟨e1, e2, e3⟩ := rowTweak_injective hl hr hl' hr' (bytesLE_injective hh)
  exact ⟨e1, e2, e3, bytesLE_injective hL, bytesLE_injective hR, bytesLE_injective hc, bytesLE_injective hp⟩
theorem pairEncoding_separation (up : Layer) (tree leaf : Nat) :
    (∀ (lay : Layer) (tree' leaf' i st : Nat), rowTweak up tree leaf ≠ chainHeader lay tree' leaf' i st) ∧
    (∀ (i k j t s : Nat) (high : BitVec 64), rowTweak up tree leaf ≠ ftsChainHeaderP i k j t s high) ∧
    (∀ (tag lay tree' position idx : Nat), tag % 256 ≠ 2 →
      rowTweak up tree leaf ≠ header tag lay tree' position idx) ∧
    (up.val < 3 → ∀ tree' leaf' : Nat, rowTweak up tree leaf ≠ rowTweak 3 tree' leaf') := by
  refine ⟨fun lay tree' leaf' i st h => ?_, fun i k j t s high h => ?_,
    fun tag lay tree' position idx ht => rowTweak_ne_header up tree leaf ht lay tree' position idx,
    fun hup tree' leaf' h => ?_⟩
  · have hc := chainHeader_firstByte lay tree' leaf' i st
    have hm := rowTweak_marker up tree leaf
    unfold tweakMarker at hm
    rw [← h, hm] at hc
    omega
  · have hc := ftsChainHeaderP_firstByte i k j t s high
    have hm := rowTweak_marker up tree leaf
    unfold tweakMarker at hm
    rw [← h, hm] at hc
    omega
  · obtain ⟨-, hw⟩ := append64_inj h
    have hb := congrArg (fun x : BitVec 64 => x.toNat / 2 ^ 48 % 256) hw
    simp only [hyperWord_toNat] at hb
    have := up.isLt
    omega
theorem ordinal_slot_injective {q q' : Nat} (h1 : q / 2 = q' / 2) (h2 : q % 2 = q' % 2) : q = q' := by
  omega
theorem ftsOrdinal_injective {child chain child' chain' : Nat} (hc : chain < 7) (hc' : chain' < 7)
    (h : ftsOrdinal child chain = ftsOrdinal child' chain') : child = child' ∧ chain = chain' := by
  unfold ftsOrdinal at h
  omega
theorem ftsSlot_injective {child chain child' chain' : Nat} (hc : chain < 7) (hc' : chain' < 7)
    (h1 : ftsOrdinal child chain / 2 = ftsOrdinal child' chain' / 2)
    (h2 : ftsOrdinal child chain % 2 = ftsOrdinal child' chain' % 2) : child = child' ∧ chain = chain' :=
  ftsOrdinal_injective hc hc' (ordinal_slot_injective h1 h2)
theorem ftsOrdinal_pair_lt {child chain : Nat} (hs : child < 128) (hc : chain < 7) :
    ftsOrdinal child chain / 2 < 448 := by
  unfold ftsOrdinal; omega
theorem lowerOrdinal_injective (lay : Layer) {leaf chain leaf' chain' : Nat} (hc : chain < chainCount lay)
    (hc' : chain' < chainCount lay) (h : lowerOrdinal lay leaf chain = lowerOrdinal lay leaf' chain') :
    leaf = leaf' ∧ chain = chain' := by
  unfold lowerOrdinal at h
  have hpos : 0 < chainCount lay := by fin_cases lay <;> decide
  rcases Nat.lt_trichotomy leaf leaf' with hl | hl | hl
  · have : chainCount lay * leaf + chainCount lay ≤ chainCount lay * leaf' := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hl
    omega
  · subst hl; omega
  · have : chainCount lay * leaf' + chainCount lay ≤ chainCount lay * leaf := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hl
    omega
theorem lowerSlot_injective (lay : Layer) {leaf chain leaf' chain' : Nat} (hc : chain < chainCount lay)
    (hc' : chain' < chainCount lay) (h1 : lowerOrdinal lay leaf chain / 2 = lowerOrdinal lay leaf' chain' / 2)
    (h2 : lowerOrdinal lay leaf chain % 2 = lowerOrdinal lay leaf' chain' % 2) : leaf = leaf' ∧ chain = chain' :=
  lowerOrdinal_injective lay hc hc' (ordinal_slot_injective h1 h2)
theorem lowerOrdinal_pair_lt (lay : Layer) {leaf chain : Nat} (hl : leaf < 2 ^ height lay)
    (hc : chain < chainCount lay) : lowerOrdinal lay leaf chain / 2 < chainCount lay * 2 ^ height lay / 2 + 1 := by
  unfold lowerOrdinal
  have : chainCount lay * leaf + chainCount lay ≤ chainCount lay * 2 ^ height lay := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hl
  omega
theorem lowerOrdinal_pair_lt_pow (lay : Layer) {leaf chain : Nat} (hl : leaf < 2 ^ height lay)
    (hc : chain < chainCount lay) : lowerOrdinal lay leaf chain / 2 < 2 ^ 32 := by
  have h := lowerOrdinal_pair_lt lay hl hc
  have hb : chainCount lay * 2 ^ height lay / 2 + 1 ≤ 2 ^ 32 := by
    fin_cases lay <;> decide
  omega
theorem ftsSeedHeader_injective {coord index pair coord' index' pair' : Nat}
    (hk : coord < 256) (hi : index < 2 ^ 40) (hp : pair < 2 ^ 32)
    (hk' : coord' < 256) (hi' : index' < 2 ^ 40) (hp' : pair' < 2 ^ 32)
    (h : ftsSeedHeader coord index pair = ftsSeedHeader coord' index' pair') :
    coord = coord' ∧ index = index' ∧ pair = pair' := by
  obtain ⟨-, e1, e2, -, e3⟩ := header_injective (by decide) hk hi (by norm_num) hp
    (by decide) hk' hi' (by norm_num) hp' h
  exact ⟨e1, e2, e3⟩
theorem lowerSeedHeader_injective {lay lay' : Layer} {tree pair tree' pair' : Nat}
    (ht : tree < 2 ^ 40) (hp : pair < 2 ^ 32) (ht' : tree' < 2 ^ 40) (hp' : pair' < 2 ^ 32)
    (h : lowerSeedHeader lay tree pair = lowerSeedHeader lay' tree' pair') :
    lay = lay' ∧ tree = tree' ∧ pair = pair' := by
  have hl := lay.isLt
  have hl' := lay'.isLt
  obtain ⟨-, e1, e2, e3, -⟩ := header_injective (by decide) (by omega) ht hp (by norm_num)
    (by decide) (by omega) ht' hp' (by norm_num) h
  exact ⟨Fin.ext e1, e2, e3⟩
theorem ftsSeedHeader_ne_tag (coord index pair tag lay tree position idx : Nat) (ht : tag % 256 ≠ 8) :
    ftsSeedHeader coord index pair ≠ header tag lay tree position idx := by
  intro h
  have h1 := header_byte1 8 coord index 0 pair
  unfold ftsSeedHeader at h
  rw [h, header_byte1] at h1
  omega
theorem lowerSeedHeader_ne_tag (lay : Layer) (tree pair tag lay' tree' position idx : Nat) (ht : tag % 256 ≠ 0) :
    lowerSeedHeader lay tree pair ≠ header tag lay' tree' position idx := by
  intro h
  have h1 := header_byte1 0 lay.val tree pair 0
  unfold lowerSeedHeader at h
  rw [h, header_byte1] at h1
  omega
theorem lowerSeedHeader_ne_top (lay : Layer) (hlay : lay ≠ 0) (tree pair tree' position idx : Nat) :
    lowerSeedHeader lay tree pair ≠ header 0 0 tree' position idx := by
  intro h
  have h2 := header_byte2 0 lay.val tree pair 0
  unfold lowerSeedHeader at h
  rw [h, header_byte2] at h2
  have := lay.isLt
  have : lay.val ≠ 0 := fun h0 => hlay (Fin.ext h0)
  omega
theorem ftsSeedHeader_ne_lowerSeedHeader (coord index pair : Nat) (lay : Layer) (tree pair' : Nat) :
    ftsSeedHeader coord index pair ≠ lowerSeedHeader lay tree pair' :=
  ftsSeedHeader_ne_tag coord index pair 0 lay.val tree pair' 0 (by decide)
end ClaudeWCT.WCT9
