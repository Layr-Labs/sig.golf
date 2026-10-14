import SigGolfCandidate.T3.Core

namespace SigGolfCandidate.T3
set_option maxHeartbeats 1000000
def tweakMarker (h : BitVec 128) : Nat := h.toNat % 256
def tweakTag (h : BitVec 128) : Nat := h.toNat / 256 % 256
def tweakHigh (h : BitVec 128) : Nat := h.toNat / 2 ^ 64
/-- The low (verifier-written) label word of a tweak, bytes 16..24 of a 64-byte input. -/
def tweakLow (h : BitVec 128) : Nat := h.toNat % 2 ^ 64
theorem hyperWord_toNat (lay routed : Nat) :
    (hyperWord lay routed).toNat =
      1 + 2 * 2 ^ 8 + routed % 2 ^ 32 * 2 ^ 16 + lay % 256 * 2 ^ 48 + 193 * 2 ^ 56 := by
  unfold hyperWord
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have := Nat.mod_lt routed (show 0 < 2 ^ 32 by decide)
  have := Nat.mod_lt lay (show 0 < 256 by decide)
  omega
theorem hyperWord_injective {lay routed lay' routed' : Nat} (hl : lay < 256) (hl' : lay' < 256)
    (hr : routed < 2 ^ 32) (hr' : routed' < 2 ^ 32) (h : hyperWord lay routed = hyperWord lay' routed') :
    lay = lay' ∧ routed = routed' := by
  have hh := congrArg BitVec.toNat h
  rw [hyperWord_toNat, hyperWord_toNat, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hr', Nat.mod_eq_of_lt hl,
    Nat.mod_eq_of_lt hl'] at hh
  omega
theorem append64_toNat (hi lo : BitVec 64) : (hi ++ lo).toNat = hi.toNat * 2 ^ 64 + lo.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt lo.isLt, Nat.shiftLeft_eq]
theorem append64_marker (hi lo : BitVec 64) : tweakMarker (hi ++ lo) = lo.toNat % 256 := by
  unfold tweakMarker
  rw [append64_toNat]
  omega
theorem append64_tag (hi lo : BitVec 64) : tweakTag (hi ++ lo) = lo.toNat / 256 % 256 := by
  unfold tweakTag
  rw [append64_toNat]
  have := lo.isLt
  omega
theorem append64_high (hi lo : BitVec 64) : tweakHigh (hi ++ lo) = hi.toNat := by
  unfold tweakHigh
  rw [append64_toNat]
  have := lo.isLt
  omega
theorem append64_low (hi lo : BitVec 64) : (hi ++ lo).extractLsb' 0 64 = lo :=
  BitVec.extractLsb'_append_eq_right
theorem append64_lowNat (hi lo : BitVec 64) : tweakLow (hi ++ lo) = lo.toNat := by
  unfold tweakLow
  rw [append64_toNat]
  have := lo.isLt
  omega
theorem append64_inj {hi lo hi' lo' : BitVec 64} (h : hi ++ lo = hi' ++ lo') : hi = hi' ∧ lo = lo' := by
  have h1 := congrArg (fun x : BitVec 128 => x.extractLsb' 64 64) h
  have h2 := congrArg (fun x : BitVec 128 => x.extractLsb' 0 64) h
  simp only [BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right] at h1 h2
  exact ⟨h1, h2⟩
theorem hyperWord_marker (lay routed : Nat) : (hyperWord lay routed).toNat % 256 = 1 := by
  rw [hyperWord_toNat]; omega
theorem hyperWord_tag (lay routed : Nat) : (hyperWord lay routed).toNat / 256 % 256 = 2 := by
  rw [hyperWord_toNat]; omega
theorem lowerNodeWord_toNat (lay routed heap : Nat) :
    (lowerNodeWord lay routed heap).toNat =
      heap % 128 + 2 * 2 ^ 8 + routed % 2 ^ 32 * 2 ^ 16 + lay % 256 * 2 ^ 48 + 193 * 2 ^ 56 := by
  unfold lowerNodeWord
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have := Nat.mod_lt heap (show 0 < 128 by decide)
  have := Nat.mod_lt routed (show 0 < 2 ^ 32 by decide)
  have := Nat.mod_lt lay (show 0 < 256 by decide)
  omega
theorem lowerNodeWord_one (lay routed : Nat) : lowerNodeWord lay routed 1 = hyperWord lay routed := by
  apply BitVec.eq_of_toNat_eq
  rw [lowerNodeWord_toNat, hyperWord_toNat]
/-- The machine form of a lower fold word: `t3 + (heap - 1)` with `t3 = hyperWord lay routed` (the root word). -/
theorem lowerNodeWord_eq_add (lay routed : Nat) {heap : Nat} (h1 : 1 ≤ heap) (h128 : heap < 128) :
    lowerNodeWord lay routed heap = hyperWord lay routed + BitVec.ofNat 64 (heap - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [lowerNodeWord_toNat, BitVec.toNat_add, hyperWord_toNat, BitVec.toNat_ofNat]
  have := Nat.mod_lt routed (show 0 < 2 ^ 32 by decide)
  have := Nat.mod_lt lay (show 0 < 256 by decide)
  rw [Nat.mod_eq_of_lt (show heap - 1 < 2 ^ 64 by omega), Nat.mod_eq_of_lt h128]
  omega
theorem lowerNodeWord_marker (lay routed heap : Nat) : (lowerNodeWord lay routed heap).toNat % 256 = heap % 128 := by
  rw [lowerNodeWord_toNat]; omega
theorem lowerNodeWord_tag (lay routed heap : Nat) : (lowerNodeWord lay routed heap).toNat / 256 % 256 = 2 := by
  rw [lowerNodeWord_toNat]
  have := Nat.mod_lt heap (show 0 < 128 by decide)
  omega
theorem lowerNodeWord_type (lay routed heap : Nat) : (lowerNodeWord lay routed heap).toNat / 2 ^ 56 = 193 := by
  rw [lowerNodeWord_toNat]
  have := Nat.mod_lt heap (show 0 < 128 by decide)
  have := Nat.mod_lt routed (show 0 < 2 ^ 32 by decide)
  have := Nat.mod_lt lay (show 0 < 256 by decide)
  omega
theorem hyperWord_type (lay routed : Nat) : (hyperWord lay routed).toNat / 2 ^ 56 = 193 := by
  rw [← lowerNodeWord_one]; exact lowerNodeWord_type lay routed 1
theorem lowerNodeWord_injective {lay routed heap lay' routed' heap' : Nat} (hl : lay < 256) (hl' : lay' < 256)
    (hr : routed < 2 ^ 32) (hr' : routed' < 2 ^ 32) (hh : heap < 128) (hh' : heap' < 128)
    (h : lowerNodeWord lay routed heap = lowerNodeWord lay' routed' heap') :
    lay = lay' ∧ routed = routed' ∧ heap = heap' := by
  have hq := congrArg BitVec.toNat h
  rw [lowerNodeWord_toNat, lowerNodeWord_toNat, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hr', Nat.mod_eq_of_lt hl,
    Nat.mod_eq_of_lt hl', Nat.mod_eq_of_lt hh, Nat.mod_eq_of_lt hh'] at hq
  omega
theorem leafTweak_marker (lay : Layer) (tree leaf : Nat) : tweakMarker (leafTweak lay tree leaf) = 1 := by
  rw [leafTweak, append64_marker, hyperWord_marker]
theorem leafTweak_tag (lay : Layer) (tree leaf : Nat) : tweakTag (leafTweak lay tree leaf) = 2 := by
  rw [leafTweak, append64_tag, hyperWord_tag]
theorem leafTweak_high (lay : Layer) (tree leaf : Nat) : tweakHigh (leafTweak lay tree leaf) = 0 := by
  rw [leafTweak, append64_high]; rfl
/-- Campaign S1: the encoding tweak and the leaf tweak are the same value (one word `t3`); the two inputs differ in
length. -/
theorem rowTweak_eq_leafTweak (lay : Layer) (tree leaf : Nat) : rowTweak lay tree leaf = leafTweak lay tree leaf := rfl
theorem rowTweak_marker (lay : Layer) (tree leaf : Nat) : tweakMarker (rowTweak lay tree leaf) = 1 := by
  rw [rowTweak, append64_marker, hyperWord_marker]
theorem rowTweak_tag (lay : Layer) (tree leaf : Nat) : tweakTag (rowTweak lay tree leaf) = 2 := by
  rw [rowTweak, append64_tag, hyperWord_tag]
theorem rowTweak_high (lay : Layer) (tree leaf : Nat) : tweakHigh (rowTweak lay tree leaf) = 0 := by
  rw [rowTweak, append64_high]; rfl
theorem topNodeWord_pos (heap : Nat) : 1 ≤ topNodeWord heap := by unfold topNodeWord; omega
theorem topNodeWord_lt (heap : Nat) : topNodeWord heap < 4096 := by unfold topNodeWord; omega
theorem topNodeWord_eq {heap : Nat} (h1 : 1 ≤ heap) (h : heap < 4096) : topNodeWord heap = heap := by
  unfold topNodeWord; omega
theorem topNodeWord_inj {heap heap' : Nat} (h1 : 1 ≤ heap) (h : heap < 4096) (h1' : 1 ≤ heap') (h' : heap' < 4096)
    (he : topNodeWord heap = topNodeWord heap') : heap = heap' := by
  rw [topNodeWord_eq h1 h, topNodeWord_eq h1' h'] at he; exact he
theorem nodeTweak_top (tree heap : Nat) : nodeTweak 3 0 tree heap = 0#64 ++ BitVec.ofNat 64 (topNodeWord heap) := by
  simp [nodeTweak]
theorem nodeTweak_lower {lay : Nat} (h0 : lay ≠ 0) (h4 : lay < 4) (tree heap : Nat) :
    nodeTweak 3 lay tree heap = 0#64 ++ lowerNodeWord (lay - 1) tree heap := by
  simp [nodeTweak, h0, h4]
def FtsNew (heap : Nat) : Prop := 8 ≤ heap ∧ heap < 128
instance (heap : Nat) : Decidable (FtsNew heap) := inferInstanceAs (Decidable (8 ≤ heap ∧ heap < 128))
theorem nodeTweak_fts {lay : Nat} (h4 : 4 ≤ lay) (h13 : lay < 13) (tree : Nat) {heap : Nat} (hn : ¬ FtsNew heap) :
    nodeTweak 3 lay tree heap = BitVec.ofNat 64 heap ++ ftsNodeWord (lay - 4) tree := by
  unfold nodeTweak
  rw [if_neg (show ¬ (3 = 3 ∧ lay < 4) by omega), if_pos (show (3 = 3 ∧ lay < 13) by omega), if_neg (show ¬ (8 ≤ heap ∧ heap < 128) from hn)]
theorem nodeTweak_ftsN {lay : Nat} (h4 : 4 ≤ lay) (h13 : lay < 13) (tree : Nat) {heap : Nat} (hn : FtsNew heap) :
    nodeTweak 3 lay tree heap = 0#64 ++ ftsNodeWordH (lay - 4) tree heap := by
  unfold nodeTweak
  rw [if_neg (show ¬ (3 = 3 ∧ lay < 4) by omega), if_pos (show (3 = 3 ∧ lay < 13) by omega), if_pos (show (8 ≤ heap ∧ heap < 128) from hn)]
theorem ftsNodeWordH_toNat (coord index heap : Nat) :
    (ftsNodeWordH coord index heap).toNat = 1537 - heap + (coord + 1) % 16 * 2 ^ 16 + index % 2 ^ 31 * 2 ^ 27 := by
  unfold ftsNodeWordH
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have := Nat.mod_lt (coord + 1) (show 0 < 16 by decide)
  have := Nat.mod_lt index (show 0 < 2 ^ 31 by decide)
  omega
theorem ftsNodeWordH_lt (coord index heap : Nat) : (ftsNodeWordH coord index heap).toNat < 2 ^ 58 := by
  rw [ftsNodeWordH_toNat]
  have := Nat.mod_lt (coord + 1) (show 0 < 16 by decide)
  have := Nat.mod_lt index (show 0 < 2 ^ 31 by decide)
  omega
/-- Campaign S1: every FTS word is `≥ 2 ^ 16` for coordinates `< 15`. -/
theorem ftsNodeWordH_ge {coord : Nat} (hc : coord < 15) (index heap : Nat) :
    2 ^ 16 ≤ (ftsNodeWordH coord index heap).toNat := by
  rw [ftsNodeWordH_toNat]; omega
theorem ftsNodeWordH_marker {heap : Nat} (hn : FtsNew heap) (coord index : Nat) :
    (ftsNodeWordH coord index heap).toNat % 256 = 257 - heap := by
  obtain ⟨h8, h128⟩ := hn
  rw [ftsNodeWordH_toNat]; omega
theorem ftsNodeWordH_tag {heap : Nat} (hn : FtsNew heap) (coord index : Nat) :
    (ftsNodeWordH coord index heap).toNat / 256 % 256 = 5 := by
  obtain ⟨h8, h128⟩ := hn
  rw [ftsNodeWordH_toNat]; omega
theorem ftsNodeWordH_injective {coord index heap coord' index' heap' : Nat} (hc : coord < 16) (hi : index < 2 ^ 31)
    (hn : FtsNew heap) (hc' : coord' < 16) (hi' : index' < 2 ^ 31) (hn' : FtsNew heap')
    (h : ftsNodeWordH coord index heap = ftsNodeWordH coord' index' heap') :
    coord = coord' ∧ index = index' ∧ heap = heap' := by
  obtain ⟨h8, h128⟩ := hn
  obtain ⟨h8', h128'⟩ := hn'
  have hh := congrArg BitVec.toNat h
  rw [ftsNodeWordH_toNat, ftsNodeWordH_toNat, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hi'] at hh
  omega
theorem nodeTweak_other {tag lay : Nat} (h : ¬ (tag = 3 ∧ lay < 13)) (tree heap : Nat) :
    nodeTweak tag lay tree heap = header tag lay tree 0 heap := by
  unfold nodeTweak
  rw [if_neg (show ¬ (tag = 3 ∧ lay < 4) by omega), if_neg h]
theorem ftsNodeWord_toNat (coord index : Nat) :
    (ftsNodeWord coord index).toNat = 1 + 6 * 2 ^ 8 + (coord + 1) % 16 * 2 ^ 16 + index % 2 ^ 31 * 2 ^ 27 := by
  unfold ftsNodeWord
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have := Nat.mod_lt (coord + 1) (show 0 < 16 by decide)
  have := Nat.mod_lt index (show 0 < 2 ^ 31 by decide)
  omega
theorem ftsNodeWord_ge {coord : Nat} (hc : coord < 15) (index : Nat) : 2 ^ 16 ≤ (ftsNodeWord coord index).toNat := by
  rw [ftsNodeWord_toNat]; omega
theorem ftsNodeWord_lt (coord index : Nat) : (ftsNodeWord coord index).toNat < 2 ^ 58 := by
  rw [ftsNodeWord_toNat]
  have := Nat.mod_lt (coord + 1) (show 0 < 16 by decide)
  have := Nat.mod_lt index (show 0 < 2 ^ 31 by decide)
  omega
theorem ftsNodeWord_marker (coord index : Nat) : (ftsNodeWord coord index).toNat % 256 = 1 := by
  rw [ftsNodeWord_toNat]; omega
theorem ftsNodeWord_tag (coord index : Nat) : (ftsNodeWord coord index).toNat / 256 % 256 = 6 := by
  rw [ftsNodeWord_toNat]; omega
theorem ftsNodeWord_injective {coord index coord' index' : Nat} (hc : coord < 16) (hi : index < 2 ^ 31)
    (hc' : coord' < 16) (hi' : index' < 2 ^ 31) (h : ftsNodeWord coord index = ftsNodeWord coord' index') :
    coord = coord' ∧ index = index' := by
  have hh := congrArg BitVec.toNat h
  rw [ftsNodeWord_toNat, ftsNodeWord_toNat, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hi'] at hh
  omega
theorem nodeTweak_fts_marker {lay : Nat} (h4 : 4 ≤ lay) (h13 : lay < 13) (tree heap : Nat) :
    tweakMarker (nodeTweak 3 lay tree heap) = if FtsNew heap then 257 - heap else 1 := by
  by_cases hn : FtsNew heap
  · rw [if_pos hn, nodeTweak_ftsN h4 h13 tree hn, append64_marker, ftsNodeWordH_marker hn]
  · rw [if_neg hn, nodeTweak_fts h4 h13 tree hn, append64_marker, ftsNodeWord_marker]
theorem nodeTweak_fts_tag {lay : Nat} (h4 : 4 ≤ lay) (h13 : lay < 13) (tree heap : Nat) :
    tweakTag (nodeTweak 3 lay tree heap) = if FtsNew heap then 5 else 6 := by
  by_cases hn : FtsNew heap
  · rw [if_pos hn, nodeTweak_ftsN h4 h13 tree hn, append64_tag, ftsNodeWordH_tag hn]
  · rw [if_neg hn, nodeTweak_fts h4 h13 tree hn, append64_tag, ftsNodeWord_tag]
theorem nodeTweak_fts_tag_ne {lay : Nat} (h4 : 4 ≤ lay) (h13 : lay < 13) (tree heap : Nat) {t : Nat}
    (h5 : t ≠ 5) (h6 : t ≠ 6) : tweakTag (nodeTweak 3 lay tree heap) ≠ t := by
  rw [nodeTweak_fts_tag h4 h13]; by_cases hn : FtsNew heap
  · rw [if_pos hn]; omega
  · rw [if_neg hn]; omega
theorem nodeTweak_fts_marker_ne {lay : Nat} (h4 : 4 ≤ lay) (h13 : lay < 13) (tree heap : Nat) {t : Nat}
    (h1 : t ≠ 1) (h128 : t < 128) : tweakMarker (nodeTweak 3 lay tree heap) ≠ t := by
  rw [nodeTweak_fts_marker h4 h13]; by_cases hn : FtsNew heap
  · rw [if_pos hn]; obtain ⟨h8, h128'⟩ := hn; omega
  · rw [if_neg hn]; omega
theorem nodeTweak_fts_high {lay : Nat} (h4 : 4 ≤ lay) (h13 : lay < 13) (tree heap : Nat) :
    tweakHigh (nodeTweak 3 lay tree heap) = if FtsNew heap then 0 else heap % 2 ^ 64 := by
  by_cases hn : FtsNew heap
  · rw [if_pos hn, nodeTweak_ftsN h4 h13 tree hn, append64_high]; rfl
  · rw [if_neg hn, nodeTweak_fts h4 h13 tree hn, append64_high, BitVec.toNat_ofNat]
theorem nodeTweak_fts_injective {lay lay' tree tree' heap heap' : Nat} (h4 : 4 ≤ lay) (h13 : lay < 13)
    (h4' : 4 ≤ lay') (h13' : lay' < 13) (ht : tree < 2 ^ 31) (ht' : tree' < 2 ^ 31)
    (hh : heap < 2 ^ 64) (hh' : heap' < 2 ^ 64)
    (h : nodeTweak 3 lay tree heap = nodeTweak 3 lay' tree' heap') : lay = lay' ∧ tree = tree' ∧ heap = heap' := by
  have hm := congrArg tweakMarker h
  rw [nodeTweak_fts_marker h4 h13, nodeTweak_fts_marker h4' h13'] at hm
  by_cases hn : FtsNew heap <;> by_cases hn' : FtsNew heap'
  · rw [nodeTweak_ftsN h4 h13 tree hn, nodeTweak_ftsN h4' h13' tree' hn'] at h
    obtain ⟨-, hw⟩ := append64_inj h
    obtain ⟨hc, hi, he⟩ := ftsNodeWordH_injective (by omega) ht hn (by omega) ht' hn' hw
    exact ⟨by omega, hi, he⟩
  · rw [if_pos hn, if_neg hn'] at hm; obtain ⟨-, h128⟩ := hn; omega
  · rw [if_neg hn, if_pos hn'] at hm; obtain ⟨-, h128⟩ := hn'; omega
  · have hH := congrArg tweakHigh h
    rw [nodeTweak_fts_high h4 h13, nodeTweak_fts_high h4' h13', if_neg hn, if_neg hn', Nat.mod_eq_of_lt hh,
      Nat.mod_eq_of_lt hh'] at hH
    rw [nodeTweak_fts h4 h13 tree hn, nodeTweak_fts h4' h13' tree' hn'] at h
    obtain ⟨-, hw⟩ := append64_inj h
    obtain ⟨hc, hi⟩ := ftsNodeWord_injective (by omega) ht (by omega) ht' hw
    exact ⟨by omega, hi, hH⟩
/-- Campaign S1: the top fold word is the heap itself. -/
theorem nodeTweak_top_low (tree heap : Nat) : tweakLow (nodeTweak 3 0 tree heap) = topNodeWord heap := by
  rw [nodeTweak_top, append64_lowNat, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (lt_trans (topNodeWord_lt heap) (by norm_num))
theorem nodeTweak_top_marker (tree heap : Nat) : tweakMarker (nodeTweak 3 0 tree heap) = topNodeWord heap % 256 := by
  have := topNodeWord_lt heap
  rw [nodeTweak_top, append64_marker, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show topNodeWord heap < 2 ^ 64 by omega)]
theorem nodeTweak_top_tag (tree heap : Nat) : tweakTag (nodeTweak 3 0 tree heap) = topNodeWord heap / 256 := by
  have := topNodeWord_lt heap
  rw [nodeTweak_top, append64_tag, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show topNodeWord heap < 2 ^ 64 by omega)]; omega
theorem nodeTweak_lower_low {lay : Nat} (h0 : lay ≠ 0) (h4 : lay < 4) (tree heap : Nat) :
    tweakLow (nodeTweak 3 lay tree heap) = (lowerNodeWord (lay - 1) tree heap).toNat := by
  rw [nodeTweak_lower h0 h4, append64_lowNat]
theorem nodeTweak_lower_marker {lay : Nat} (h0 : lay ≠ 0) (h4 : lay < 4) (tree heap : Nat) :
    tweakMarker (nodeTweak 3 lay tree heap) = heap % 128 := by
  rw [nodeTweak_lower h0 h4, append64_marker, lowerNodeWord_marker]
theorem nodeTweak_lower_tag {lay : Nat} (h0 : lay ≠ 0) (h4 : lay < 4) (tree heap : Nat) :
    tweakTag (nodeTweak 3 lay tree heap) = 2 := by
  rw [nodeTweak_lower h0 h4, append64_tag, lowerNodeWord_tag]
/-- Campaign S1: top and lower node tweaks are one word (honest high word 0). -/
theorem nodeTweak_hyper_high {lay : Nat} (h4 : lay < 4) (tree heap : Nat) :
    tweakHigh (nodeTweak 3 lay tree heap) = 0 := by
  by_cases h0 : lay = 0
  · subst h0; rw [nodeTweak_top, append64_high]; rfl
  · rw [nodeTweak_lower h0 h4, append64_high]; rfl
theorem header_toNat' (tag lay tree position index : Nat) :
    (header tag lay tree position index).toNat =
      (1 + tag % 256 * 2^8 + lay % 256 * 2^16 + (tree / 2^32 % 256) * 2^24 +
        if packedNodeTag tag then tree % 2^32 * 2^32 + nodeWord tag position index * 2^64
        else position % 2^32 * 2^32 + tree % 2^32 * 2^64 + index % 2^32 * 2^96) := by
  unfold header
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have := Nat.mod_lt tag (show 0 < 256 by decide)
  have := Nat.mod_lt lay (show 0 < 256 by decide)
  have := Nat.mod_lt (tree / 2 ^ 32) (show 0 < 256 by decide)
  have := Nat.mod_lt position (show 0 < 2 ^ 32 by decide)
  have := Nat.mod_lt tree (show 0 < 2 ^ 32 by decide)
  have := Nat.mod_lt index (show 0 < 2 ^ 32 by decide)
  have := nodeWord_lt tag position index
  split_ifs <;> omega
theorem header_marker (tag lay tree position index : Nat) :
    tweakMarker (header tag lay tree position index) = 1 := by
  unfold tweakMarker
  rw [header_toNat']
  split_ifs <;> omega
theorem header_tag (tag lay tree position index : Nat) :
    tweakTag (header tag lay tree position index) = tag % 256 := by
  unfold tweakTag
  rw [header_toNat']
  have := Nat.mod_lt tag (show 0 < 256 by decide)
  have := Nat.mod_lt lay (show 0 < 256 by decide)
  have := Nat.mod_lt (tree / 2 ^ 32) (show 0 < 256 by decide)
  have := Nat.mod_lt position (show 0 < 2 ^ 32 by decide)
  have := Nat.mod_lt tree (show 0 < 2 ^ 32 by decide)
  have := Nat.mod_lt index (show 0 < 2 ^ 32 by decide)
  have := nodeWord_lt tag position index
  generalize nodeWord tag position index = g at *
  generalize tag % 256 = a at *
  generalize lay % 256 = b at *
  generalize tree / 2 ^ 32 % 256 = c at *
  generalize position % 2 ^ 32 = d at *
  generalize tree % 2 ^ 32 = e at *
  generalize index % 2 ^ 32 = f at *
  split_ifs <;> omega
theorem digestHeader_toNat (counter : BitVec 32) : (digestHeader counter).toNat = counter.toNat * 2 ^ 64 := by
  simp only [digestHeader, BitVec.toNat_append, BitVec.toNat_zero, Nat.or_zero, Nat.shiftLeft_eq,
    Nat.zero_mul, Nat.zero_or]
theorem digestHeader_firstByte (counter : BitVec 32) : (digestHeader counter).toNat % 256 = 0 := by
  rw [digestHeader_toNat]; omega
theorem digestHeader_marker (counter : BitVec 32) : tweakMarker (digestHeader counter) = 0 :=
  digestHeader_firstByte counter
theorem digestHeader_tag (counter : BitVec 32) : tweakTag (digestHeader counter) = 0 := by
  unfold tweakTag; rw [digestHeader_toNat]; omega
theorem digestHeader_low (counter : BitVec 32) : (digestHeader counter).extractLsb' 0 64 = 0 :=
  BitVec.extractLsb'_append_eq_right
theorem digestHeader_high (counter : BitVec 32) :
    (digestHeader counter).extractLsb' 64 64 = BitVec.ofNat 64 counter.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, digestHeader_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have := counter.isLt
  omega
theorem digestHeader_injective : Function.Injective digestHeader := by
  intro counter counter' h
  have hh := congrArg BitVec.toNat h
  rw [digestHeader_toNat, digestHeader_toNat] at hh
  exact BitVec.eq_of_toNat_eq (by omega)
theorem leafTweak_injective {lay lay' : Layer} {tree leaf tree' leaf' : Nat}
    (hl : leaf < 2 ^ height lay) (hr : tree * 2 ^ height lay + leaf < 2 ^ 32)
    (hl' : leaf' < 2 ^ height lay') (hr' : tree' * 2 ^ height lay' + leaf' < 2 ^ 32)
    (h : leafTweak lay tree leaf = leafTweak lay' tree' leaf') : lay = lay' ∧ tree = tree' ∧ leaf = leaf' := by
  obtain ⟨-, hw⟩ := append64_inj h
  obtain ⟨hlay, hroute⟩ := hyperWord_injective (by have := lay.isLt; omega) (by have := lay'.isLt; omega) hr hr' hw
  have hla : lay = lay' := Fin.ext hlay
  subst hla
  have hp : 0 < 2 ^ height lay := by positivity
  have h1 := congrArg (· / 2 ^ height lay) hroute
  have h2 := congrArg (· % 2 ^ height lay) hroute
  simp only [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hl, Nat.div_eq_of_lt hl', Nat.mul_comm tree,
    Nat.mul_comm tree', Nat.mul_add_div hp] at h1
  simp only [Nat.mul_comm tree, Nat.mul_comm tree', Nat.mul_add_mod, Nat.mod_eq_of_lt hl,
    Nat.mod_eq_of_lt hl'] at h2
  exact ⟨rfl, by simpa using h1, h2⟩
theorem rowTweak_injective {lay lay' : Layer} {tree leaf tree' leaf' : Nat}
    (hl : leaf < 2 ^ height lay) (hr : tree * 2 ^ height lay + leaf < 2 ^ 32)
    (hl' : leaf' < 2 ^ height lay') (hr' : tree' * 2 ^ height lay' + leaf' < 2 ^ 32)
    (h : rowTweak lay tree leaf = rowTweak lay' tree' leaf') : lay = lay' ∧ tree = tree' ∧ leaf = leaf' := by
  obtain ⟨-, hw⟩ := append64_inj h
  exact leafTweak_injective hl hr hl' hr' (by rw [leafTweak, leafTweak, hw])
/-- Campaign S1: top/lower node tweaks are injective (top words `heap < 2 ^ 56`, lower words carry type byte 193
and the heap in byte0). -/
theorem nodeTweak_hyper_injective {lay lay' tree tree' heap heap' : Nat} (hl : lay < 4) (hl' : lay' < 4)
    (ht : tree < 2 ^ 32) (ht' : tree' < 2 ^ 32) (h0 : lay = 0 → tree = 0) (h0' : lay' = 0 → tree' = 0)
    (hh : 1 ≤ heap ∧ heap < 4096 ∧ (lay ≠ 0 → heap < 128))
    (hh' : 1 ≤ heap' ∧ heap' < 4096 ∧ (lay' ≠ 0 → heap' < 128))
    (h : nodeTweak 3 lay tree heap = nodeTweak 3 lay' tree' heap') : lay = lay' ∧ tree = tree' ∧ heap = heap' := by
  have hL := congrArg tweakLow h
  by_cases hz : lay = 0
  · subst hz
    rw [nodeTweak_top_low] at hL
    have := topNodeWord_lt heap
    by_cases hz' : lay' = 0
    · subst hz'
      rw [nodeTweak_top_low] at hL
      exact ⟨rfl, by rw [h0 rfl, h0' rfl], topNodeWord_inj hh.1 hh.2.1 hh'.1 hh'.2.1 hL⟩
    · rw [nodeTweak_lower_low hz' hl', lowerNodeWord_toNat] at hL; omega
  · rw [nodeTweak_lower_low hz hl, lowerNodeWord_toNat] at hL
    by_cases hz' : lay' = 0
    · subst hz'; rw [nodeTweak_top_low] at hL; have := topNodeWord_lt heap'; omega
    · rw [nodeTweak_lower hz hl, nodeTweak_lower hz' hl'] at h
      obtain ⟨-, hw⟩ := append64_inj h
      obtain ⟨hlay, htree, hheap⟩ := lowerNodeWord_injective (by omega) (by omega) ht ht' (hh.2.2 hz) (hh'.2.2 hz') hw
      exact ⟨by omega, htree, hheap⟩
theorem ne_of_tweakMarker {a b : BitVec 128} (h : tweakMarker a ≠ tweakMarker b) : a ≠ b :=
  fun e => h (congrArg tweakMarker e)
theorem ne_of_tweakTag {a b : BitVec 128} (h : tweakTag a ≠ tweakTag b) : a ≠ b :=
  fun e => h (congrArg tweakTag e)
theorem ne_of_tweakHigh {a b : BitVec 128} (h : tweakHigh a ≠ tweakHigh b) : a ≠ b :=
  fun e => h (congrArg tweakHigh e)
theorem leafTweak_low (lay : Layer) (tree leaf : Nat) :
    tweakLow (leafTweak lay tree leaf) = (hyperWord lay.val (tree * 2 ^ height lay + leaf)).toNat := by
  rw [leafTweak, append64_lowNat]
/-- A leaf/encoding tweak is not a non-root top/lower fold tweak (S1: separated by the low word). -/
theorem leafTweak_ne_nodeTweak (lay : Layer) (tree leaf : Nat) {lay' : Nat} (h4 : lay' < 4)
    (tree' heap : Nat) (hh : lay' = 0 ∨ heap % 128 ≠ 1) :
    leafTweak lay tree leaf ≠ nodeTweak 3 lay' tree' heap := by
  intro he
  have hL := congrArg tweakLow he
  rw [leafTweak_low, hyperWord_toNat] at hL
  by_cases h0 : lay' = 0
  · subst h0; rw [nodeTweak_top_low] at hL; have := topNodeWord_lt heap; omega
  · rw [nodeTweak_lower_low h0 h4, lowerNodeWord_toNat] at hL
    have := hh.resolve_left h0
    omega
theorem rowTweak_ne_nodeTweak (lay : Layer) (tree leaf : Nat) {lay' : Nat} (h4 : lay' < 4)
    (tree' heap : Nat) (hh : lay' = 0 ∨ heap % 128 ≠ 1) :
    rowTweak lay tree leaf ≠ nodeTweak 3 lay' tree' heap :=
  leafTweak_ne_nodeTweak lay tree leaf h4 tree' heap hh
theorem leafTweak_ne_header (lay : Layer) (tree leaf : Nat) {tag : Nat} (ht : tag % 256 ≠ 2)
    (lay' tree' position index : Nat) : leafTweak lay tree leaf ≠ header tag lay' tree' position index :=
  ne_of_tweakTag (by rw [leafTweak_tag, header_tag]; omega)
theorem rowTweak_ne_header (lay : Layer) (tree leaf : Nat) {tag : Nat} (ht : tag % 256 ≠ 2)
    (lay' tree' position index : Nat) : rowTweak lay tree leaf ≠ header tag lay' tree' position index :=
  ne_of_tweakTag (by rw [rowTweak_tag, header_tag]; omega)
theorem nodeTweak_lower_ne_header {lay : Nat} (h0 : lay ≠ 0) (h4 : lay < 4) (tree heap : Nat) {tag : Nat}
    (ht : tag % 256 ≠ 2) (lay' tree' position index : Nat) :
    nodeTweak 3 lay tree heap ≠ header tag lay' tree' position index :=
  ne_of_tweakTag (by rw [nodeTweak_lower_tag h0 h4, header_tag]; omega)
theorem nodeTweak_top_ne_header (tree : Nat) {heap : Nat} (hh : topNodeWord heap % 256 ≠ 1)
    (tag lay' tree' position index : Nat) :
    nodeTweak 3 0 tree heap ≠ header tag lay' tree' position index :=
  ne_of_tweakMarker (by rw [nodeTweak_top_marker, header_marker]; exact hh)
theorem digestHeader_ne_header (counter : BitVec 32) (tag lay tree position index : Nat) :
    digestHeader counter ≠ header tag lay tree position index :=
  ne_of_tweakMarker (by rw [digestHeader_marker, header_marker]; decide)
theorem digestHeader_ne_leafTweak (counter : BitVec 32) (lay : Layer) (tree leaf : Nat) :
    digestHeader counter ≠ leafTweak lay tree leaf :=
  ne_of_tweakMarker (by rw [digestHeader_marker, leafTweak_marker]; decide)
theorem digestHeader_ne_rowTweak (counter : BitVec 32) (lay : Layer) (tree leaf : Nat) :
    digestHeader counter ≠ rowTweak lay tree leaf :=
  ne_of_tweakMarker (by rw [digestHeader_marker, rowTweak_marker]; decide)
theorem nodeTweak_marker (tag lay tree heap : Nat) :
    tweakMarker (nodeTweak tag lay tree heap) = (if tag = 3 ∧ lay = 0 then topNodeWord heap % 256
      else if tag = 3 ∧ lay < 4 then heap % 128
      else if tag = 3 ∧ 4 ≤ lay ∧ lay < 13 ∧ FtsNew heap then 257 - heap else 1) := by
  by_cases h : tag = 3 ∧ lay < 4
  · obtain ⟨rfl, h4⟩ := h
    by_cases h0 : lay = 0
    · subst h0; rw [nodeTweak_top_marker, if_pos ⟨rfl, rfl⟩]
    · rw [nodeTweak_lower_marker h0 h4, if_neg (fun h' => h0 h'.2), if_pos ⟨rfl, h4⟩]
  · rw [if_neg (fun h' => h ⟨h'.1, by omega⟩), if_neg h]
    by_cases hf : tag = 3 ∧ lay < 13
    · obtain ⟨rfl, h13⟩ := hf
      rw [nodeTweak_fts_marker (by omega) h13]
      by_cases hn : FtsNew heap
      · rw [if_pos hn, if_pos ⟨rfl, by omega, h13, hn⟩]
      · rw [if_neg hn, if_neg (fun h' => hn h'.2.2.2)]
    · rw [nodeTweak_other hf, header_marker]
      have h2 : ¬ (tag = 3 ∧ 4 ≤ lay ∧ lay < 13 ∧ FtsNew heap) := fun h' => hf ⟨h'.1, h'.2.2.1⟩
      rw [if_neg h2]
/-- The low word of a node tweak. Top: the heap; lower: `lowerNodeWord`; FTS: the packed/two-word FTS word; other
tags: the header low word (byte0 1). -/
theorem nodeTweak_low_ne_zero (tag lay tree heap : Nat) : tweakLow (nodeTweak tag lay tree heap) ≠ 0 := by
  by_cases h : tag = 3 ∧ lay < 4
  · obtain ⟨rfl, h4⟩ := h
    by_cases h0 : lay = 0
    · subst h0; rw [nodeTweak_top_low]; have := topNodeWord_pos heap; omega
    · rw [nodeTweak_lower_low h0 h4, lowerNodeWord_toNat]; omega
  · have hm := nodeTweak_marker tag lay tree heap
    rw [if_neg (fun h' => h ⟨h'.1, by omega⟩), if_neg h] at hm
    unfold tweakMarker at hm
    unfold tweakLow
    intro h0
    have : (nodeTweak tag lay tree heap).toNat % 256 = 0 := by omega
    rw [this] at hm
    split_ifs at hm with hf
    obtain ⟨-, -, -, h8, h128⟩ := hf; omega
theorem digestHeader_lowNat (counter : BitVec 32) : tweakLow (digestHeader counter) = 0 := by
  unfold tweakLow; rw [digestHeader_toNat]; omega
/-- S1: the digest is separated from every node by its zero low word (top heaps may have byte0 = 0). -/
theorem digestHeader_ne_nodeTweak (counter : BitVec 32) (tag lay tree heap : Nat) :
    digestHeader counter ≠ nodeTweak tag lay tree heap := by
  intro he
  have := congrArg tweakLow he
  rw [digestHeader_lowNat] at this
  exact nodeTweak_low_ne_zero tag lay tree heap this.symm
theorem nodeTweak_fts_low {lay : Nat} (h4 : 4 ≤ lay) (h13 : lay < 13) (tree heap : Nat) :
    tweakLow (nodeTweak 3 lay tree heap) =
      if FtsNew heap then (ftsNodeWordH (lay - 4) tree heap).toNat else (ftsNodeWord (lay - 4) tree).toNat := by
  by_cases hn : FtsNew heap
  · rw [if_pos hn, nodeTweak_ftsN h4 h13 tree hn, append64_lowNat]
  · rw [if_neg hn, nodeTweak_fts h4 h13 tree hn, append64_lowNat]
/-- Campaign S1: FTS node words are `≥ 2 ^ 16` (coordinate nibble `coord + 1`), top words are `heap < 2 ^ 16`,
lower words carry type byte 193. -/
theorem nodeTweak_fts_ne_hyper {lay lay' : Nat} (h4 : 4 ≤ lay) (h13 : lay < 13) (hl' : lay' < 4)
    (tree heap tree' heap' : Nat) : nodeTweak 3 lay tree heap ≠ nodeTweak 3 lay' tree' heap' := by
  intro he
  have hL := congrArg tweakLow he
  rw [nodeTweak_fts_low h4 h13] at hL
  have hge : 2 ^ 16 ≤ (if FtsNew heap then (ftsNodeWordH (lay - 4) tree heap).toNat
      else (ftsNodeWord (lay - 4) tree).toNat) := by
    split_ifs
    · exact ftsNodeWordH_ge (by omega) _ _
    · exact ftsNodeWord_ge (by omega) _
  have hlt : (if FtsNew heap then (ftsNodeWordH (lay - 4) tree heap).toNat
      else (ftsNodeWord (lay - 4) tree).toNat) < 2 ^ 58 := by
    split_ifs
    · exact ftsNodeWordH_lt _ _ _
    · exact ftsNodeWord_lt _ _
  by_cases h0 : lay' = 0
  · subst h0; rw [nodeTweak_top_low] at hL; have := topNodeWord_lt heap'; omega
  · rw [nodeTweak_lower_low h0 hl', lowerNodeWord_toNat] at hL; omega
theorem nodeTweak_fts_ne_leafTweak {lay : Nat} (h4 : 4 ≤ lay) (h13 : lay < 13) (tree heap : Nat)
    (lay' : Layer) (tree' leaf' : Nat) : nodeTweak 3 lay tree heap ≠ leafTweak lay' tree' leaf' :=
  ne_of_tweakTag (by rw [leafTweak_tag]; exact nodeTweak_fts_tag_ne h4 h13 _ _ (by decide) (by decide))
theorem nodeTweak_fts_ne_rowTweak {lay : Nat} (h4 : 4 ≤ lay) (h13 : lay < 13) (tree heap : Nat)
    (lay' : Layer) (tree' leaf' : Nat) : nodeTweak 3 lay tree heap ≠ rowTweak lay' tree' leaf' :=
  ne_of_tweakTag (by rw [rowTweak_tag]; exact nodeTweak_fts_tag_ne h4 h13 _ _ (by decide) (by decide))
theorem nodeTweak_fts_ne_header {lay : Nat} (h4 : 4 ≤ lay) (h13 : lay < 13) (tree heap : Nat) {tag : Nat}
    (ht : tag % 256 ≠ 6) (lay' tree' position index : Nat) :
    nodeTweak 3 lay tree heap ≠ header tag lay' tree' position index := by
  by_cases hn : FtsNew heap
  · exact ne_of_tweakMarker (by rw [header_marker, nodeTweak_fts_marker h4 h13, if_pos hn]; obtain ⟨-, h⟩ := hn; omega)
  · exact ne_of_tweakTag (by rw [nodeTweak_fts_tag h4 h13, if_neg hn, header_tag]; omega)
theorem leafInput_length (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    (leafInput lay tree leaf ends).length =
      if lay = 0 then 32 + 16 * ends.length else 32 + 16 * (ends.length - 1) := by
  unfold leafInput
  split_ifs
  · simp [zero16, SphincsSecurity.bytesLE_length, List.length_flatMap, List.map_const', List.sum_replicate]
    omega
  · simp [SphincsSecurity.bytesLE_length, List.length_flatMap, List.map_const', List.sum_replicate]
    omega
theorem hyperWord_chainHeaderLow (lay : Layer) (tree leaf : Nat) (hf : leaf < 2 ^ height lay)
    (hr : tree * 2 ^ height lay + leaf < 2 ^ 31) :
    hyperWord lay.val (tree * 2 ^ height lay + leaf) = chainHeaderLow lay tree leaf 0 0 + 0x181#64 := by
  have htr : tree < 2 ^ 31 := by fin_cases lay <;> simp [height] at hr ⊢ <;> omega
  have hlf : leaf < 4096 := by fin_cases lay <;> simp [height] at hf ⊢ <;> omega
  have he1 : tree / 2 ^ (32 - height lay) = 0 := by
    apply Nat.div_eq_of_lt; fin_cases lay <;> simp [height] at hr ⊢ <;> omega
  have he2 : leaf / 2 ^ height lay = 0 := Nat.div_eq_of_lt hf
  have hR : tree * 2 ^ height lay + leaf < 2 ^ 32 := by omega
  have hl := lay.isLt
  apply BitVec.eq_of_toNat_eq
  rw [hyperWord_toNat, BitVec.toNat_add]
  unfold chainHeaderLow
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htr, Nat.mod_eq_of_lt hlf, he1, he2, Nat.zero_mod,
    Nat.zero_mul, Nat.add_zero, Nat.zero_div, Nat.zero_add, Nat.mod_eq_of_lt hR,
    Nat.mod_eq_of_lt (show lay.val < 256 by omega)]
  omega
end SigGolfCandidate.T3
