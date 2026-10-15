import SigGolfCandidate.T3.Core

namespace SigGolfCandidate.T3
set_option maxHeartbeats 1000000
def tweakMarker (h : BitVec 128) : Nat := h.toNat % 256
def tweakTag (h : BitVec 128) : Nat := h.toNat / 256 % 256
def tweakHigh (h : BitVec 128) : Nat := h.toNat / 2 ^ 64
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
theorem append64_inj {hi lo hi' lo' : BitVec 64} (h : hi ++ lo = hi' ++ lo') : hi = hi' ∧ lo = lo' := by
  have h1 := congrArg (fun x : BitVec 128 => x.extractLsb' 64 64) h
  have h2 := congrArg (fun x : BitVec 128 => x.extractLsb' 0 64) h
  simp only [BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right] at h1 h2
  exact ⟨h1, h2⟩
theorem hyperWord_marker (lay routed : Nat) : (hyperWord lay routed).toNat % 256 = 1 := by
  rw [hyperWord_toNat]; omega
theorem hyperWord_tag (lay routed : Nat) : (hyperWord lay routed).toNat / 256 % 256 = 2 := by
  rw [hyperWord_toNat]; omega
theorem leafTweak_marker (lay : Layer) (tree leaf : Nat) : tweakMarker (leafTweak lay tree leaf) = 1 := by
  rw [leafTweak, append64_marker, hyperWord_marker]
theorem leafTweak_tag (lay : Layer) (tree leaf : Nat) : tweakTag (leafTweak lay tree leaf) = 2 := by
  rw [leafTweak, append64_tag, hyperWord_tag]
theorem leafTweak_high (lay : Layer) (tree leaf : Nat) : tweakHigh (leafTweak lay tree leaf) = 0 := by
  rw [leafTweak, append64_high]; rfl
theorem rowTweak_marker (lay : Layer) (tree leaf : Nat) : tweakMarker (rowTweak lay tree leaf) = 1 := by
  rw [rowTweak, append64_marker, hyperWord_marker]
theorem rowTweak_tag (lay : Layer) (tree leaf : Nat) : tweakTag (rowTweak lay tree leaf) = 2 := by
  rw [rowTweak, append64_tag, hyperWord_tag]
theorem rowTweak_high (lay : Layer) (tree leaf : Nat) : tweakHigh (rowTweak lay tree leaf) = 1 := by
  rw [rowTweak, append64_high]; rfl
theorem nodeTweak_top (tree heap : Nat) : nodeTweak 3 0 tree heap = BitVec.ofNat 64 heap ++ 64#64 := by
  simp [nodeTweak]
theorem nodeTweak_lower {lay : Nat} (h0 : lay ≠ 0) (h4 : lay < 4) (tree heap : Nat) :
    nodeTweak 3 lay tree heap = BitVec.ofNat 64 heap ++ hyperWord (lay - 1) tree := by
  simp [nodeTweak, h0, h4]
theorem nodeTweak_fts {lay : Nat} (h4 : 4 ≤ lay) (h13 : lay < 13) (tree heap : Nat) :
    nodeTweak 3 lay tree heap = BitVec.ofNat 64 heap ++ ftsNodeWord (lay - 4) tree := by
  unfold nodeTweak
  rw [if_neg (show ¬ (3 = 3 ∧ lay < 4) by omega), if_pos (show (3 = 3 ∧ lay < 13) by omega)]
theorem nodeTweak_other {tag lay : Nat} (h : ¬ (tag = 3 ∧ lay < 13)) (tree heap : Nat) :
    nodeTweak tag lay tree heap = header tag lay tree 0 heap := by
  unfold nodeTweak
  rw [if_neg (show ¬ (tag = 3 ∧ lay < 4) by omega), if_neg h]
theorem ftsNodeWord_toNat (coord index : Nat) :
    (ftsNodeWord coord index).toNat = 1 + 6 * 2 ^ 8 + coord % 16 * 2 ^ 16 + index % 2 ^ 31 * 2 ^ 27 := by
  unfold ftsNodeWord
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have := Nat.mod_lt coord (show 0 < 16 by decide)
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
  rw [ftsNodeWord_toNat, ftsNodeWord_toNat, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hc',
    Nat.mod_eq_of_lt hi'] at hh
  omega
theorem nodeTweak_fts_marker {lay : Nat} (h4 : 4 ≤ lay) (h13 : lay < 13) (tree heap : Nat) :
    tweakMarker (nodeTweak 3 lay tree heap) = 1 := by
  rw [nodeTweak_fts h4 h13, append64_marker, ftsNodeWord_marker]
theorem nodeTweak_fts_tag {lay : Nat} (h4 : 4 ≤ lay) (h13 : lay < 13) (tree heap : Nat) :
    tweakTag (nodeTweak 3 lay tree heap) = 6 := by
  rw [nodeTweak_fts h4 h13, append64_tag, ftsNodeWord_tag]
theorem nodeTweak_fts_high {lay : Nat} (h4 : 4 ≤ lay) (h13 : lay < 13) (tree heap : Nat) :
    tweakHigh (nodeTweak 3 lay tree heap) = heap % 2 ^ 64 := by
  rw [nodeTweak_fts h4 h13, append64_high, BitVec.toNat_ofNat]
theorem nodeTweak_fts_injective {lay lay' tree tree' heap heap' : Nat} (h4 : 4 ≤ lay) (h13 : lay < 13)
    (h4' : 4 ≤ lay') (h13' : lay' < 13) (ht : tree < 2 ^ 31) (ht' : tree' < 2 ^ 31)
    (hh : heap < 2 ^ 64) (hh' : heap' < 2 ^ 64)
    (h : nodeTweak 3 lay tree heap = nodeTweak 3 lay' tree' heap') : lay = lay' ∧ tree = tree' ∧ heap = heap' := by
  have hH := congrArg tweakHigh h
  rw [nodeTweak_fts_high h4 h13, nodeTweak_fts_high h4' h13', Nat.mod_eq_of_lt hh, Nat.mod_eq_of_lt hh'] at hH
  rw [nodeTweak_fts h4 h13, nodeTweak_fts h4' h13'] at h
  obtain ⟨-, hw⟩ := append64_inj h
  obtain ⟨hc, hi⟩ := ftsNodeWord_injective (by omega) ht (by omega) ht' hw
  exact ⟨by omega, hi, hH⟩
theorem nodeTweak_top_marker (tree heap : Nat) : tweakMarker (nodeTweak 3 0 tree heap) = 64 := by
  rw [nodeTweak_top, append64_marker]; rfl
theorem nodeTweak_top_tag (tree heap : Nat) : tweakTag (nodeTweak 3 0 tree heap) = 0 := by
  rw [nodeTweak_top, append64_tag]; rfl
theorem nodeTweak_lower_marker {lay : Nat} (h0 : lay ≠ 0) (h4 : lay < 4) (tree heap : Nat) :
    tweakMarker (nodeTweak 3 lay tree heap) = 1 := by
  rw [nodeTweak_lower h0 h4, append64_marker, hyperWord_marker]
theorem nodeTweak_lower_tag {lay : Nat} (h0 : lay ≠ 0) (h4 : lay < 4) (tree heap : Nat) :
    tweakTag (nodeTweak 3 lay tree heap) = 2 := by
  rw [nodeTweak_lower h0 h4, append64_tag, hyperWord_tag]
theorem nodeTweak_hyper_high' {lay : Nat} (h4 : lay < 4) (tree heap : Nat) :
    tweakHigh (nodeTweak 3 lay tree heap) = heap % 2 ^ 64 := by
  by_cases h0 : lay = 0
  · subst h0; rw [nodeTweak_top, append64_high, BitVec.toNat_ofNat]
  · rw [nodeTweak_lower h0 h4, append64_high, BitVec.toNat_ofNat]
theorem nodeTweak_hyper_high {lay : Nat} (h4 : lay < 4) (tree heap : Nat) :
    tweakHigh (nodeTweak 3 lay tree heap) = heap % 2 ^ 64 := nodeTweak_hyper_high' h4 tree heap
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
theorem nodeTweak_hyper_injective {lay lay' tree tree' heap heap' : Nat} (hl : lay < 4) (hl' : lay' < 4)
    (ht : tree < 2 ^ 32) (ht' : tree' < 2 ^ 32) (h0 : lay = 0 → tree = 0) (h0' : lay' = 0 → tree' = 0)
    (hh : heap < 2 ^ 64) (hh' : heap' < 2 ^ 64)
    (h : nodeTweak 3 lay tree heap = nodeTweak 3 lay' tree' heap') : lay = lay' ∧ tree = tree' ∧ heap = heap' := by
  have hm := congrArg tweakMarker h
  have hH := congrArg tweakHigh h
  rw [nodeTweak_hyper_high hl, nodeTweak_hyper_high hl', Nat.mod_eq_of_lt hh, Nat.mod_eq_of_lt hh'] at hH
  by_cases hz : lay = 0
  · subst hz
    by_cases hz' : lay' = 0
    · subst hz'; exact ⟨rfl, by rw [h0 rfl, h0' rfl], hH⟩
    · rw [nodeTweak_top_marker, nodeTweak_lower_marker hz' hl'] at hm; omega
  · by_cases hz' : lay' = 0
    · subst hz'; rw [nodeTweak_top_marker, nodeTweak_lower_marker hz hl] at hm; omega
    · rw [nodeTweak_lower hz hl, nodeTweak_lower hz' hl'] at h
      obtain ⟨-, hw⟩ := append64_inj h
      obtain ⟨hlay, htree⟩ := hyperWord_injective (by omega) (by omega) ht ht' hw
      exact ⟨by omega, htree, hH⟩
theorem ne_of_tweakMarker {a b : BitVec 128} (h : tweakMarker a ≠ tweakMarker b) : a ≠ b :=
  fun e => h (congrArg tweakMarker e)
theorem ne_of_tweakTag {a b : BitVec 128} (h : tweakTag a ≠ tweakTag b) : a ≠ b :=
  fun e => h (congrArg tweakTag e)
theorem ne_of_tweakHigh {a b : BitVec 128} (h : tweakHigh a ≠ tweakHigh b) : a ≠ b :=
  fun e => h (congrArg tweakHigh e)
theorem leafTweak_ne_rowTweak (lay lay' : Layer) (tree leaf tree' leaf' : Nat) :
    leafTweak lay tree leaf ≠ rowTweak lay' tree' leaf' :=
  ne_of_tweakHigh (by rw [leafTweak_high, rowTweak_high]; decide)
theorem leafTweak_ne_nodeTweak (lay : Layer) (tree leaf : Nat) {lay' : Nat} (h4 : lay' < 4)
    (tree' heap : Nat) (hh : heap % 2 ^ 64 ≠ 0) : leafTweak lay tree leaf ≠ nodeTweak 3 lay' tree' heap :=
  ne_of_tweakHigh (by rw [leafTweak_high, nodeTweak_hyper_high h4]; omega)
theorem rowTweak_ne_nodeTweak (lay : Layer) (tree leaf : Nat) {lay' : Nat} (h4 : lay' < 4)
    (tree' heap : Nat) (hh : heap % 2 ^ 64 ≠ 1) : rowTweak lay tree leaf ≠ nodeTweak 3 lay' tree' heap :=
  ne_of_tweakHigh (by rw [rowTweak_high, nodeTweak_hyper_high h4]; omega)
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
theorem nodeTweak_top_ne_header (tree heap tag lay' tree' position index : Nat) :
    nodeTweak 3 0 tree heap ≠ header tag lay' tree' position index :=
  ne_of_tweakMarker (by rw [nodeTweak_top_marker, header_marker]; decide)
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
    tweakMarker (nodeTweak tag lay tree heap) = (if tag = 3 ∧ lay = 0 then 64 else 1) := by
  by_cases h : tag = 3 ∧ lay < 4
  · obtain ⟨rfl, h4⟩ := h
    by_cases h0 : lay = 0
    · subst h0; rw [nodeTweak_top_marker]; simp
    · rw [nodeTweak_lower_marker h0 h4]; simp [h0]
  · by_cases hf : tag = 3 ∧ lay < 13
    · obtain ⟨rfl, h13⟩ := hf
      rw [nodeTweak_fts_marker (by omega) h13]; simp; omega
    · rw [nodeTweak_other hf, header_marker]
      have : ¬ (tag = 3 ∧ lay = 0) := fun h' => h ⟨h'.1, by omega⟩
      simp [this]
theorem nodeTweak_marker_ne_zero (tag lay tree heap : Nat) : tweakMarker (nodeTweak tag lay tree heap) ≠ 0 := by
  rw [nodeTweak_marker]; split_ifs <;> decide
theorem digestHeader_ne_nodeTweak (counter : BitVec 32) (tag lay tree heap : Nat) :
    digestHeader counter ≠ nodeTweak tag lay tree heap :=
  ne_of_tweakMarker (by rw [digestHeader_marker]; exact (nodeTweak_marker_ne_zero tag lay tree heap).symm)
theorem nodeTweak_fts_ne_hyper {lay lay' : Nat} (h4 : 4 ≤ lay) (h13 : lay < 13) (hl' : lay' < 4)
    (tree heap tree' heap' : Nat) : nodeTweak 3 lay tree heap ≠ nodeTweak 3 lay' tree' heap' := by
  by_cases h0 : lay' = 0
  · subst h0
    exact ne_of_tweakMarker (by rw [nodeTweak_fts_marker h4 h13, nodeTweak_top_marker]; decide)
  · exact ne_of_tweakTag (by rw [nodeTweak_fts_tag h4 h13, nodeTweak_lower_tag h0 hl']; decide)
theorem nodeTweak_fts_ne_leafTweak {lay : Nat} (h4 : 4 ≤ lay) (h13 : lay < 13) (tree heap : Nat)
    (lay' : Layer) (tree' leaf' : Nat) : nodeTweak 3 lay tree heap ≠ leafTweak lay' tree' leaf' :=
  ne_of_tweakTag (by rw [nodeTweak_fts_tag h4 h13, leafTweak_tag]; decide)
theorem nodeTweak_fts_ne_rowTweak {lay : Nat} (h4 : 4 ≤ lay) (h13 : lay < 13) (tree heap : Nat)
    (lay' : Layer) (tree' leaf' : Nat) : nodeTweak 3 lay tree heap ≠ rowTweak lay' tree' leaf' :=
  ne_of_tweakTag (by rw [nodeTweak_fts_tag h4 h13, rowTweak_tag]; decide)
theorem nodeTweak_fts_ne_header {lay : Nat} (h4 : 4 ≤ lay) (h13 : lay < 13) (tree heap : Nat) {tag : Nat}
    (ht : tag % 256 ≠ 6) (lay' tree' position index : Nat) :
    nodeTweak 3 lay tree heap ≠ header tag lay' tree' position index :=
  ne_of_tweakTag (by rw [nodeTweak_fts_tag h4 h13, header_tag]; omega)
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
