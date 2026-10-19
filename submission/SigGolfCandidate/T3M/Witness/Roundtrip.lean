import SigGolfCandidate.T3M.Witness.Shaped

namespace SigGolfCandidate.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
open SphincsSecurity (bytesLE bytesLE_length)
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
theorem readLE_cons (b : UInt8) (L : List UInt8) : readLE (b :: L) = b.toNat + 256 * readLE L := rfl
theorem readLE_append (A B : List UInt8) : readLE (A ++ B) = readLE A + 256 ^ A.length * readLE B := by
  induction A with
  | nil => simp [readLE]
  | cons a A ih => rw [List.cons_append, readLE_cons, readLE_cons, ih, List.length_cons, pow_succ]; ring
theorem readLE_lt (L : List UInt8) : readLE L < 256 ^ L.length := by
  induction L with
  | nil => simp [readLE]
  | cons a L ih =>
      rw [readLE_cons, List.length_cons, pow_succ]
      have := a.toNat_lt
      omega
theorem readLE_drop : ∀ (L : List UInt8) (k : Nat), readLE L / 256 ^ k = readLE (L.drop k) := by
  intro L k
  induction k generalizing L with
  | zero => simp
  | succ k ih =>
      cases L with
      | nil => simp [readLE]
      | cons a L =>
          rw [List.drop_succ_cons, ← ih L, readLE_cons, pow_succ', ← Nat.div_div_eq_div_mul]
          congr 1
          have := a.toNat_lt
          omega
theorem readLE_take : ∀ (L : List UInt8) (k : Nat), readLE L % 256 ^ k = readLE (L.take k) := by
  intro L k
  induction k generalizing L with
  | zero => simp [readLE, Nat.mod_one]
  | succ k ih =>
      cases L with
      | nil => simp [readLE]
      | cons a L =>
          rw [List.take_succ_cons, readLE_cons, readLE_cons, ← ih L, pow_succ', Nat.mod_mul]
          have := a.toNat_lt
          have h1 : (a.toNat + 256 * readLE L) % 256 = a.toNat := by omega
          have h2 : (a.toNat + 256 * readLE L) / 256 = readLE L := by omega
          rw [h1, h2]
theorem extract_readLE (L : List UInt8) (n : Nat) (hL : L.length ≤ n) (off k : Nat) :
    (BitVec.ofNat (8 * n) (readLE L)).extractLsb' (8 * off) (8 * k) =
      BitVec.ofNat (8 * k) (readLE ((L.drop off).take k)) := by
  have hlt : readLE L < 2 ^ (8 * n) := by
    have := readLE_lt L
    calc readLE L < 256 ^ L.length := this
      _ ≤ 256 ^ n := Nat.pow_le_pow_right (by norm_num) hL
      _ = 2 ^ (8 * n) := by rw [pow_mul]; norm_num
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt,
    Nat.shiftRight_eq_div_pow, show 2 ^ (8 * off) = 256 ^ off by rw [pow_mul]; norm_num, readLE_drop,
    show 2 ^ (8 * k) = 256 ^ k by rw [pow_mul]; norm_num, readLE_take]
  rw [Nat.mod_eq_of_lt]
  have := readLE_lt ((L.drop off).take k)
  calc readLE ((L.drop off).take k) < 256 ^ ((L.drop off).take k).length := this
    _ ≤ 256 ^ k := Nat.pow_le_pow_right (by norm_num) (by simp)
theorem headerBytes_length (w : Witness) : (headerBytes w).length = 64 := by
  simp [headerBytes, zeros, bytesLE_length, List.length_flatMap, List.sum_replicate]
theorem leafBytes_length (sig : Signature) : (leafBytes sig).length = 1024 := by
  simp [leafBytes, zeros, bytesLE_length, List.length_flatMap, List.sum_replicate]
theorem streamBytes_length (chosen : List Selection) (proof : Fin 115 → Digest) :
    (streamBytes chosen proof).length = 8200 := by
  simp only [streamBytes, zeros, List.length_take, List.length_append, List.length_replicate]
  omega
theorem layerBytes_length (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) :
    (layerBytes lay leaf ls).length = 64 * (height lay + chainCount lay) := by
  unfold layerBytes
  rw [List.length_append, List.length_flatMap, List.length_flatMap]
  have h1 : ∀ j : Fin (height lay), (if leaf / 2 ^ j.val % 2 = 1 then bytesLE 16 (ls.path j) ++ zeros 48
      else zeros 48 ++ bytesLE 16 (ls.path j)).length = 64 := by
    intro j; split <;> simp [zeros, bytesLE_length]
  simp only [h1]
  simp only [List.length_append, zeros, List.length_replicate, bytesLE_length, List.map_const',
    List.length_reverse, List.length_finRange, List.sum_replicate, smul_eq_mul]
  ring
theorem layerStorage_length (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) :
    (layerStorage lay leaf ls).length = 64 * (height lay + chainCount lay) := by
  simp only [layerStorage, layerBytes_length]

theorem take_one_drop (L : List UInt8) : ∀ i, readLE ((L.drop i).take 1) = (L.getD i 0).toNat := by
  induction L with
  | nil => intro i; simp [readLE]
  | cons a L ih =>
      intro i
      cases i with
      | zero => simp [readLE]
      | succ i => rw [List.drop_succ_cons, ih i]; simp
def window (L : List UInt8) (off n : Nat) : List UInt8 := (L.drop off).take n
theorem window_append_left (A B : List UInt8) (off n : Nat) (h : off + n ≤ A.length) :
    window (A ++ B) off n = window A off n := by
  unfold window
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
theorem window_append_right (A B : List UInt8) (off n : Nat) (h : A.length ≤ off) :
    window (A ++ B) off n = window B (off - A.length) n := by
  unfold window
  rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append]
theorem window_flatMap {β : Type} (l : List β) (f : β → List UInt8) :
    ∀ (i : Nat) (hi : i < l.length) (j n : Nat), j + n ≤ (f l[i]).length →
      window (l.flatMap f) (((l.take i).map fun b => (f b).length).sum + j) n = window (f l[i]) j n := by
  induction l with
  | nil => intro i hi; simp at hi
  | cons b l ih =>
      intro i hi j n hjn
      cases i with
      | zero =>
          simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add, List.flatMap_cons,
            List.getElem_cons_zero] at hjn ⊢
          exact window_append_left _ _ _ _ hjn
      | succ i =>
          simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.flatMap_cons,
            List.getElem_cons_succ] at hjn ⊢
          rw [window_append_right _ _ _ _ (by omega), show (f b).length + ((l.take i).map fun b => (f b).length).sum + j
            - (f b).length = ((l.take i).map fun b => (f b).length).sum + j by omega]
          exact ih i (by simpa using hi) j n hjn
theorem window_flatMap_const {β : Type} (l : List β) (f : β → List UInt8) (k : Nat) (hk : ∀ b, (f b).length = k)
    (i : Nat) (hi : i < l.length) (j n : Nat) (hjn : j + n ≤ k) :
    window (l.flatMap f) (k * i + j) n = window (f l[i]) j n := by
  have := window_flatMap l f i hi j n (by rw [hk]; exact hjn)
  rwa [show ((l.take i).map fun b => (f b).length).sum = k * i by
    rw [List.map_congr_left (fun b _ => hk b), List.map_const', List.sum_replicate, List.length_take,
      Nat.min_eq_left hi.le, smul_eq_mul, Nat.mul_comm]] at this
theorem window_full (L : List UInt8) (n : Nat) (h : L.length = n) : window L 0 n = L := by
  unfold window; rw [List.drop_zero, List.take_of_length_le (by omega)]
theorem window_zeros (m off n : Nat) (h : off + n ≤ m) : window (zeros m) off n = zeros n := by
  unfold window zeros; rw [List.drop_replicate, List.take_replicate, Nat.min_eq_left (by omega)]
theorem readDigest_zeros : readDigest (zeros 16) = 0 := by
  rw [show zeros 16 = bytesLE 16 0 from bytesLE_zero16.symm, Correctness.readDigest_bytesLE]
theorem readLE_bytesLE_32 (v : BitVec 32) : BitVec.ofNat 32 (readLE (bytesLE 4 v)) = v := by
  rw [Correctness.readLE_bytesLE]; exact BitVec.ofNat_toNat 32 v
theorem window_take (L : List UInt8) (m off n : Nat) (h : off + n ≤ m) : window (L.take m) off n = window L off n := by
  unfold window; rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega)]
theorem getD_of_window (L : List UInt8) (i : Nat) (x : UInt8) (h : window L i 1 = [x]) : L.getD i 0 = x := by
  unfold window at h
  rcases hl : L.drop i with _ | ⟨y, rest⟩
  · rw [hl] at h; simp at h
  · rw [hl] at h
    simp only [List.take_succ_cons, List.take_zero, List.cons.injEq, and_true] at h
    have hi : i < L.length := by
      by_contra hc; rw [List.drop_eq_nil_of_le (by omega)] at hl; simp at hl
    rw [List.getD_eq_getElem _ _ hi]
    have e := congrArg (fun l => l[0]?) hl
    simp only [List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero, List.getElem?_eq_getElem hi] at e
    rw [Option.some.inj e, h]
section regions
variable (N : HashOutput) (w : Witness)
theorem win_header (off n : Nat) (h : off + n ≤ 64) :
    window (witList N w) off n = window (headerBytes w) off n := by
  unfold witList
  rw [window_append_left _ _ _ _ (by simp [headerBytes_length, leafBytes_length, streamBytes_length]; omega),
    window_append_left _ _ _ _ (by simp [headerBytes_length, leafBytes_length]; omega),
    window_append_left _ _ _ _ (by simp [headerBytes_length]; omega)]
theorem win_leaf (off n : Nat) (h1 : 64 ≤ off) (h : off + n ≤ 1088) :
    window (witList N w) off n = window (leafBytes w.signature) (off - 64) n := by
  unfold witList
  rw [window_append_left _ _ _ _ (by simp [headerBytes_length, leafBytes_length, streamBytes_length]; omega),
    window_append_left _ _ _ _ (by simp [headerBytes_length, leafBytes_length]; omega),
    window_append_right _ _ _ _ (by simp [headerBytes_length]; omega), headerBytes_length]
theorem win_stream (off n : Nat) (h1 : 1088 ≤ off) (h : off + n ≤ 9288) :
    window (witList N w) off n = window (streamBytes (selections N) w.signature.proof) (off - 1088) n := by
  unfold witList
  rw [window_append_left _ _ _ _ (by simp [headerBytes_length, leafBytes_length, streamBytes_length]; omega),
    window_append_right _ _ _ _ (by simp [headerBytes_length, leafBytes_length]; omega)]
  simp [headerBytes_length, leafBytes_length]
theorem win_layers (off n : Nat) (h1 : 9288 ≤ off) :
    window (witList N w) off n = window ((List.finRange 4).flatMap fun lay =>
      layerStorage lay (route (N.toNat % 2 ^ 31) lay).1 (w.signature.layers lay)) (off - 9288) n := by
  unfold witList
  rw [window_append_right _ _ _ _ (by simp [headerBytes_length, leafBytes_length, streamBytes_length]; omega)]
  simp [headerBytes_length, leafBytes_length, streamBytes_length]
end regions
theorem foldBytes_length (E : Nat) (sib : Digest) : (foldBytes E sib).length = 64 := by
  unfold foldBytes; split <;> simp [zeros, bytesLE_length]
theorem segBytes_length (chosen : List Selection) (proof : Fin 115 → Digest) (seg : Segment) :
    (segBytes chosen proof seg).length = 8 + 64 * seg.a := by
  unfold segBytes
  simp only [List.length_append, List.length_singleton, zeros, List.length_replicate, List.length_flatMap,
    foldBytes_length, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
  omega
theorem stream_flat_length (chosen : List Selection) (proof : Fin 115 → Digest) :
    ((schedule chosen).flatMap (segBytes chosen proof)).length = ((schedule chosen).map fun s => 8 + 64 * s.a).sum := by
  rw [List.length_flatMap]; congr 1; exact List.map_congr_left (fun s _ => segBytes_length _ _ _)
theorem segPtr_le_end (chosen : List Selection) (_hc : ChosenOk chosen) {n : Nat} (_hn : n ≤ 35) :
    segPtr (schedule chosen) n ≤ segPtr (schedule chosen) 35 := by
  unfold segPtr
  have := List.sum_take_add_sum_drop ((schedule chosen).map fun s => 8 + 64 * s.a) n
  rw [← List.map_take] at this
  rw [show (schedule chosen).take 35 = schedule chosen from List.take_of_length_le (by rw [schedule_length])]
  omega
theorem win_seg (N : HashOutput) (w : Witness) (hc : ChosenOk (selections N)) (hle : slotBase (selections N) 7 ≤ 115)
    {n : Nat} (hn : n < 35) (j m : Nat) (hjm : j + m ≤ 8 + 64 * ((schedule (selections N)).getD n default).a) :
    window (witList N w) (segPtr (schedule (selections N)) n + j) m =
      window (segBytes (selections N) w.signature.proof ((schedule (selections N)).getD n default)) j m := by
  have hend := segPtr_end (selections N) hc
  have hsucc := segPtr_succ (schedule (selections N)) (m := n) (by rw [schedule_length]; exact hn)
  have hmono := segPtr_le_end (selections N) hc (show n + 1 ≤ 35 by omega)
  unfold segNext at hsucc
  have hb : 1088 ≤ segPtr (schedule (selections N)) n := by unfold segPtr streamBase; omega
  have hflat := stream_flat_length (selections N) w.signature.proof
  have hsum : segPtr (schedule (selections N)) 35 = 1088 + ((schedule (selections N)).map fun s => 8 + 64 * s.a).sum := by
    unfold segPtr streamBase; rw [List.take_of_length_le (by rw [schedule_length])]
  rw [win_stream _ _ _ _ (by omega) (by unfold streamBase at hend; omega)]
  unfold streamBytes
  rw [window_take _ _ _ _ (by unfold streamBase at hend; omega),
    window_append_left _ _ _ _ (by rw [hflat]; omega)]
  have hpre : segPtr (schedule (selections N)) n + j - 1088 =
      (((schedule (selections N)).take n).map fun s => (segBytes (selections N) w.signature.proof s).length).sum + j := by
    unfold segPtr streamBase
    rw [List.map_congr_left (fun s _ => segBytes_length _ _ s)]
    omega
  rw [hpre, window_flatMap _ _ n (by rw [schedule_length]; exact hn) j m
    (by rw [segBytes_length, ← List.getD_eq_getElem _ default (by rw [schedule_length]; exact hn)]; exact hjm)]
  rw [List.getD_eq_getElem _ default (by rw [schedule_length]; exact hn)]
theorem segBytes_header (chosen : List Selection) (proof : Fin 115 → Digest) (seg : Segment) :
    window (segBytes chosen proof seg) 0 1 = [UInt8.ofNat seg.byte0] := by
  unfold segBytes window; simp
theorem segBytes_fold (chosen : List Selection) (proof : Fin 115 → Digest) (seg : Segment) {r : Nat}
    (hr : r < seg.a) (j : Nat) (hj : j + 16 ≤ 64) :
    window (segBytes chosen proof seg) (8 + 64 * r + j) 16 =
      window (foldBytes (seg.heap r) (proof ⟨foldSlot chosen seg r % 115, Nat.mod_lt _ (by decide)⟩)) j 16 := by
  unfold segBytes
  have hl : ([UInt8.ofNat seg.byte0] ++ zeros 7).length = 8 := by simp [zeros]
  rw [window_append_right _ _ _ _ (by rw [hl]; omega), hl, show 8 + 64 * r + j - 8 = 64 * r + j by omega]
  rw [window_flatMap_const _ _ 64 (fun _ => foldBytes_length _ _) r (by simpa using hr) j 16 hj]
  simp only [List.getElem_range]
theorem foldBytes_sib (E : Nat) (sib : Digest) : window (foldBytes E sib) (sibOff (E % 2)) 16 = bytesLE 16 sib := by
  unfold foldBytes sibOff
  rcases Nat.mod_two_eq_zero_or_one E with h | h
  · simp only [h, show (0 : Nat) ≠ 1 by decide, if_false]
    rw [window_append_right _ _ _ _ (by simp [zeros]),
      show 48 - (zeros 48).length = 0 by simp [zeros], window_full _ _ (bytesLE_length _ _)]
  · simp only [h, if_true]
    rw [window_append_left _ _ _ _ (by simp [bytesLE_length]), window_full _ _ (bytesLE_length _ _)]
theorem foldBytes_pad (E : Nat) (sib : Digest) : window (foldBytes E sib) 32 16 = zeros 16 := by
  unfold foldBytes
  split
  · rw [window_append_right _ _ _ _ (by simp [bytesLE_length]), window_zeros _ _ _ (by simp [bytesLE_length])]
  · rw [window_append_left _ _ _ _ (by simp [zeros]), window_zeros _ _ _ (by omega)]

theorem layerBytes_merkle (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) (j : Fin (height lay)) (o : Nat)
    (ho : o + 16 ≤ 64) :
    window (layerBytes lay leaf ls) (64 * (height lay - 1 - j.val) + o) 16 =
      window (if leaf / 2 ^ j.val % 2 = 1 then bytesLE 16 (ls.path j) ++ zeros 48
        else zeros 48 ++ bytesLE 16 (ls.path j)) o 16 := by
  unfold layerBytes
  rw [window_append_left _ _ _ _ (by
    rw [List.length_flatMap]
    have : ∀ j : Fin (height lay), (if leaf / 2 ^ j.val % 2 = 1 then bytesLE 16 (ls.path j) ++ zeros 48
        else zeros 48 ++ bytesLE 16 (ls.path j)).length = 64 := by intro j; split <;> simp [zeros, bytesLE_length]
    simp only [this, List.map_const', List.length_reverse, List.length_finRange, List.sum_replicate, smul_eq_mul]
    have := j.isLt; omega)]
  rw [window_flatMap_const _ _ 64 (fun j => by split <;> simp [zeros, bytesLE_length]) (height lay - 1 - j.val)
    (by simp; omega) o 16 ho]
  have hj : ((List.finRange (height lay)).reverse[height lay - 1 - j.val]'(by simp; omega)) = j := by
    rw [List.getElem_reverse]; ext; simp; omega
  rw [hj]
theorem layerBytes_chain (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) (i : Fin (chainCount lay)) (o : Nat)
    (ho : o + 16 ≤ 64) :
    window (layerBytes lay leaf ls) (64 * height lay + 64 * (chainCount lay - 1 - i.val) + o) 16 =
      window (zeros 48 ++ bytesLE 16 (ls.values i)) o 16 := by
  unfold layerBytes
  have hM : ((List.finRange (height lay)).reverse.flatMap fun j =>
      if leaf / 2 ^ j.val % 2 = 1 then bytesLE 16 (ls.path j) ++ zeros 48
      else zeros 48 ++ bytesLE 16 (ls.path j)).length = 64 * height lay := by
    rw [List.length_flatMap]
    have : ∀ j : Fin (height lay), (if leaf / 2 ^ j.val % 2 = 1 then bytesLE 16 (ls.path j) ++ zeros 48
        else zeros 48 ++ bytesLE 16 (ls.path j)).length = 64 := by intro j; split <;> simp [zeros, bytesLE_length]
    simp only [this, List.map_const', List.length_reverse, List.length_finRange, List.sum_replicate, smul_eq_mul]
    ring
  rw [window_append_right _ _ _ _ (by rw [hM]; omega), hM,
    show 64 * height lay + 64 * (chainCount lay - 1 - i.val) + o - 64 * height lay =
      64 * (chainCount lay - 1 - i.val) + o by omega]
  rw [window_flatMap_const _ _ 64 (fun j => by simp [zeros, bytesLE_length]) (chainCount lay - 1 - i.val)
    (by simp; omega) o 16 ho]
  have hi : ((List.finRange (chainCount lay)).reverse[chainCount lay - 1 - i.val]'(by simp; omega)) = i := by
    rw [List.getElem_reverse]; ext; simp; omega
  rw [hi]
theorem schedule_a_le (chosen : List Selection) (hc : ChosenOk chosen) {n : Nat} (hn : n < 35) :
    ((schedule chosen).getD n default).lo + ((schedule chosen).getD n default).a ≤ 11 := by
  rw [schedule_getD chosen hn]; exact (foldFacts _ _ (hc _ (by omega))).top _ (by omega)
theorem byte0_lt (seg : Segment) (h : seg.a ≤ 11) : seg.byte0 < 64 := by
  unfold Segment.byte0 Segment.t
  have := Nat.mod_lt (seg.heap 0) (show 0 < 2 by decide)
  split <;> omega
theorem Segment.matches_byte0 (seg : Segment) (h : seg.a ≤ 11) : seg.Matches seg.byte0 := by
  unfold Segment.Matches Segment.byte0
  have ht : seg.t < 2 := Nat.mod_lt _ (by decide)
  refine ⟨?_, ?_, ?_⟩
  · split <;> omega
  · cases seg.merge <;> simp <;> omega
  · intro _; split <;> omega
theorem foldPositions_nodup (segs : List Segment) : (foldPositions segs).Nodup := by
  unfold foldPositions
  refine List.nodup_flatMap.mpr ⟨fun n _ => (List.nodup_range).map (fun a b h => by simpa using h), ?_⟩
  refine (List.nodup_range).pairwise_of_forall_ne (fun a _ b _ hab => ?_)
  simp only [Function.onFun, List.disjoint_left, List.mem_map, List.mem_range, not_exists, not_and]
  rintro p ⟨r, _, rfl⟩ r' _ h
  simp only [Prod.mk.injEq] at h
  exact hab h.1.symm
theorem foldPositions_length (segs : List Segment) : (foldPositions segs).length = (segs.map Segment.a).sum := by
  unfold foldPositions
  rw [List.length_flatMap]
  simp only [List.length_map, List.length_range]
  rw [← sum_range_getD segs default Segment.a]
theorem foldSlot_surj (chosen : List Selection) (hc : ChosenOk chosen) {k : Nat} (hk : k < slotBase chosen 7) :
    ∃ p ∈ foldPositions (schedule chosen), foldSlot chosen ((schedule chosen).getD p.1 default) p.2 = k := by
  classical
  have key := Finset.surj_on_of_inj_on_of_card_le (s := (foldPositions (schedule chosen)).toFinset)
    (t := Finset.range (slotBase chosen 7))
    (fun p _ => foldSlot chosen ((schedule chosen).getD p.1 default) p.2)
    (fun p hp => by
      have hm := mem_foldPositions.mp (List.mem_toFinset.mp hp)
      rw [schedule_length] at hm
      obtain ⟨e, l⟩ := foldSlot_split chosen hc hm.1 hm.2
      have hb1 := slotBase_mono chosen (show p.1 / 5 + 1 ≤ 7 by omega)
      rw [slotBase_succ] at hb1
      rw [Finset.mem_range, e]; omega)
    (fun p q hp hq h => by
      have hm := mem_foldPositions.mp (List.mem_toFinset.mp hp)
      have hm' := mem_foldPositions.mp (List.mem_toFinset.mp hq)
      rw [schedule_length] at hm hm'
      obtain ⟨h1, h2⟩ := foldSlot_inj chosen hc hm.1 hm'.1 hm.2 hm'.2 h
      exact Prod.ext h1 h2)
    (by
      rw [Finset.card_range, List.toFinset_card_of_nodup (foldPositions_nodup _), foldPositions_length,
        schedule_folds chosen hc])
  obtain ⟨p, hp, he⟩ := key k (Finset.mem_range.mpr hk)
  exact ⟨p, List.mem_toFinset.mp hp, he.symm⟩
theorem LayerSignature.ext' {lay : Layer} {x y : LayerSignature lay} (hv : x.values = y.values)
    (hp : x.path = y.path) : x = y := by
  cases x; cases y; simp_all
end SigGolfCandidate.T3M
