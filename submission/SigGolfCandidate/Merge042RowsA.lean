import SigGolfCandidate.Merge042Head
set_option linter.all false

section
set_option Elab.async false
set_option maxRecDepth 100000
open Finset Polynomial
open Finset

namespace ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedPathPacked

certify_pair_chunk 5 0 1 Pair_5_0 pair_5_0_checked
certify_pair_chunk 5 1 1 Pair_5_1 pair_5_1_checked
certify_pair_chunk 5 2 1 Pair_5_2 pair_5_2_checked
noncomputable def Pair_5_3 : Nat := pair_copy% 5 2
theorem pair_5_3_checked : pairChunkWith cachedCoordinate 5 3 1 = Pair_5_3 :=
  (pairChunkWith_mirror cachedCoordinate 5 3 2 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_5_2_checked
noncomputable def Pair_5_4 : Nat := pair_copy% 5 1
theorem pair_5_4_checked : pairChunkWith cachedCoordinate 5 4 1 = Pair_5_4 :=
  (pairChunkWith_mirror cachedCoordinate 5 4 1 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_5_1_checked
certify_pair_chunk 5 5 1 Pair_5_5 pair_5_5_checked

noncomputable def Pair_5 : Nat := pair_sum_numeral% 5

noncomputable def chunks_5 (t : Nat) : Nat :=
  match t with
  | 0 => Pair_5_0
  | 1 => Pair_5_1
  | 2 => Pair_5_2
  | 3 => Pair_5_3
  | 4 => Pair_5_4
  | 5 => Pair_5_5
  | _ => 0

theorem chunks_5_checked (t : Nat) (ht : t ≤ 5) :
    pairChunkWith cachedCoordinate 5 t 1 = chunks_5 t := by
  interval_cases t
  · exact pair_5_0_checked
  · exact pair_5_1_checked
  · exact pair_5_2_checked
  · exact pair_5_3_checked
  · exact pair_5_4_checked
  · exact pair_5_5_checked

theorem pair_5_checked : pairFirst 5 = Pair_5 := by
  have h := pairFirst_eq_cached_sum cachedCoordinate chunks_5 5
    (fun t ht => cachedCoordinate_correct t (by omega)) chunks_5_checked
  exact h.trans (by decide +kernel)

certify_pair_chunk 6 0 1 Pair_6_0 pair_6_0_checked
certify_pair_chunk 6 1 1 Pair_6_1 pair_6_1_checked
certify_pair_chunk 6 2 1 Pair_6_2 pair_6_2_checked
certify_pair_chunk 6 3 1 Pair_6_3 pair_6_3_checked
noncomputable def Pair_6_4 : Nat := pair_copy% 6 2
theorem pair_6_4_checked : pairChunkWith cachedCoordinate 6 4 1 = Pair_6_4 :=
  (pairChunkWith_mirror cachedCoordinate 6 4 2 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_6_2_checked
noncomputable def Pair_6_5 : Nat := pair_copy% 6 1
theorem pair_6_5_checked : pairChunkWith cachedCoordinate 6 5 1 = Pair_6_5 :=
  (pairChunkWith_mirror cachedCoordinate 6 5 1 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_6_1_checked
certify_pair_chunk 6 6 1 Pair_6_6 pair_6_6_checked

noncomputable def Pair_6 : Nat := pair_sum_numeral% 6

noncomputable def chunks_6 (t : Nat) : Nat :=
  match t with
  | 0 => Pair_6_0
  | 1 => Pair_6_1
  | 2 => Pair_6_2
  | 3 => Pair_6_3
  | 4 => Pair_6_4
  | 5 => Pair_6_5
  | 6 => Pair_6_6
  | _ => 0

theorem chunks_6_checked (t : Nat) (ht : t ≤ 6) :
    pairChunkWith cachedCoordinate 6 t 1 = chunks_6 t := by
  interval_cases t
  · exact pair_6_0_checked
  · exact pair_6_1_checked
  · exact pair_6_2_checked
  · exact pair_6_3_checked
  · exact pair_6_4_checked
  · exact pair_6_5_checked
  · exact pair_6_6_checked

theorem pair_6_checked : pairFirst 6 = Pair_6 := by
  have h := pairFirst_eq_cached_sum cachedCoordinate chunks_6 6
    (fun t ht => cachedCoordinate_correct t (by omega)) chunks_6_checked
  exact h.trans (by decide +kernel)

certify_pair_chunk 7 0 1 Pair_7_0 pair_7_0_checked
certify_pair_chunk 7 1 1 Pair_7_1 pair_7_1_checked
certify_pair_chunk 7 2 1 Pair_7_2 pair_7_2_checked
certify_pair_chunk 7 3 1 Pair_7_3 pair_7_3_checked
noncomputable def Pair_7_4 : Nat := pair_copy% 7 3
theorem pair_7_4_checked : pairChunkWith cachedCoordinate 7 4 1 = Pair_7_4 :=
  (pairChunkWith_mirror cachedCoordinate 7 4 3 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_7_3_checked
noncomputable def Pair_7_5 : Nat := pair_copy% 7 2
theorem pair_7_5_checked : pairChunkWith cachedCoordinate 7 5 1 = Pair_7_5 :=
  (pairChunkWith_mirror cachedCoordinate 7 5 2 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_7_2_checked
noncomputable def Pair_7_6 : Nat := pair_copy% 7 1
theorem pair_7_6_checked : pairChunkWith cachedCoordinate 7 6 1 = Pair_7_6 :=
  (pairChunkWith_mirror cachedCoordinate 7 6 1 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_7_1_checked
certify_pair_chunk 7 7 1 Pair_7_7 pair_7_7_checked

noncomputable def Pair_7 : Nat := pair_sum_numeral% 7

noncomputable def chunks_7 (t : Nat) : Nat :=
  match t with
  | 0 => Pair_7_0
  | 1 => Pair_7_1
  | 2 => Pair_7_2
  | 3 => Pair_7_3
  | 4 => Pair_7_4
  | 5 => Pair_7_5
  | 6 => Pair_7_6
  | 7 => Pair_7_7
  | _ => 0

theorem chunks_7_checked (t : Nat) (ht : t ≤ 7) :
    pairChunkWith cachedCoordinate 7 t 1 = chunks_7 t := by
  interval_cases t
  · exact pair_7_0_checked
  · exact pair_7_1_checked
  · exact pair_7_2_checked
  · exact pair_7_3_checked
  · exact pair_7_4_checked
  · exact pair_7_5_checked
  · exact pair_7_6_checked
  · exact pair_7_7_checked

theorem pair_7_checked : pairFirst 7 = Pair_7 := by
  have h := pairFirst_eq_cached_sum cachedCoordinate chunks_7 7
    (fun t ht => cachedCoordinate_correct t (by omega)) chunks_7_checked
  exact h.trans (by decide +kernel)

certify_pair_chunk 8 0 1 Pair_8_0 pair_8_0_checked
certify_pair_chunk 8 1 1 Pair_8_1 pair_8_1_checked
certify_pair_chunk 8 2 1 Pair_8_2 pair_8_2_checked
certify_pair_chunk 8 3 1 Pair_8_3 pair_8_3_checked
certify_pair_chunk 8 4 1 Pair_8_4 pair_8_4_checked
noncomputable def Pair_8_5 : Nat := pair_copy% 8 3
theorem pair_8_5_checked : pairChunkWith cachedCoordinate 8 5 1 = Pair_8_5 :=
  (pairChunkWith_mirror cachedCoordinate 8 5 3 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_8_3_checked
noncomputable def Pair_8_6 : Nat := pair_copy% 8 2
theorem pair_8_6_checked : pairChunkWith cachedCoordinate 8 6 1 = Pair_8_6 :=
  (pairChunkWith_mirror cachedCoordinate 8 6 2 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_8_2_checked
noncomputable def Pair_8_7 : Nat := pair_copy% 8 1
theorem pair_8_7_checked : pairChunkWith cachedCoordinate 8 7 1 = Pair_8_7 :=
  (pairChunkWith_mirror cachedCoordinate 8 7 1 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_8_1_checked
certify_pair_chunk 8 8 1 Pair_8_8 pair_8_8_checked

noncomputable def Pair_8 : Nat := pair_sum_numeral% 8

noncomputable def chunks_8 (t : Nat) : Nat :=
  match t with
  | 0 => Pair_8_0
  | 1 => Pair_8_1
  | 2 => Pair_8_2
  | 3 => Pair_8_3
  | 4 => Pair_8_4
  | 5 => Pair_8_5
  | 6 => Pair_8_6
  | 7 => Pair_8_7
  | 8 => Pair_8_8
  | _ => 0

theorem chunks_8_checked (t : Nat) (ht : t ≤ 8) :
    pairChunkWith cachedCoordinate 8 t 1 = chunks_8 t := by
  interval_cases t
  · exact pair_8_0_checked
  · exact pair_8_1_checked
  · exact pair_8_2_checked
  · exact pair_8_3_checked
  · exact pair_8_4_checked
  · exact pair_8_5_checked
  · exact pair_8_6_checked
  · exact pair_8_7_checked
  · exact pair_8_8_checked

theorem pair_8_checked : pairFirst 8 = Pair_8 := by
  have h := pairFirst_eq_cached_sum cachedCoordinate chunks_8 8
    (fun t ht => cachedCoordinate_correct t (by omega)) chunks_8_checked
  exact h.trans (by decide +kernel)

certify_pair_chunk 9 0 1 Pair_9_0 pair_9_0_checked
certify_pair_chunk 9 1 1 Pair_9_1 pair_9_1_checked
certify_pair_chunk 9 2 1 Pair_9_2 pair_9_2_checked
certify_pair_chunk 9 3 1 Pair_9_3 pair_9_3_checked
certify_pair_chunk 9 4 1 Pair_9_4 pair_9_4_checked
noncomputable def Pair_9_5 : Nat := pair_copy% 9 4
theorem pair_9_5_checked : pairChunkWith cachedCoordinate 9 5 1 = Pair_9_5 :=
  (pairChunkWith_mirror cachedCoordinate 9 5 4 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_9_4_checked
noncomputable def Pair_9_6 : Nat := pair_copy% 9 3
theorem pair_9_6_checked : pairChunkWith cachedCoordinate 9 6 1 = Pair_9_6 :=
  (pairChunkWith_mirror cachedCoordinate 9 6 3 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_9_3_checked
noncomputable def Pair_9_7 : Nat := pair_copy% 9 2
theorem pair_9_7_checked : pairChunkWith cachedCoordinate 9 7 1 = Pair_9_7 :=
  (pairChunkWith_mirror cachedCoordinate 9 7 2 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_9_2_checked
noncomputable def Pair_9_8 : Nat := pair_copy% 9 1
theorem pair_9_8_checked : pairChunkWith cachedCoordinate 9 8 1 = Pair_9_8 :=
  (pairChunkWith_mirror cachedCoordinate 9 8 1 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_9_1_checked
certify_pair_chunk 9 9 1 Pair_9_9 pair_9_9_checked

noncomputable def Pair_9 : Nat := pair_sum_numeral% 9

noncomputable def chunks_9 (t : Nat) : Nat :=
  match t with
  | 0 => Pair_9_0
  | 1 => Pair_9_1
  | 2 => Pair_9_2
  | 3 => Pair_9_3
  | 4 => Pair_9_4
  | 5 => Pair_9_5
  | 6 => Pair_9_6
  | 7 => Pair_9_7
  | 8 => Pair_9_8
  | 9 => Pair_9_9
  | _ => 0

theorem chunks_9_checked (t : Nat) (ht : t ≤ 9) :
    pairChunkWith cachedCoordinate 9 t 1 = chunks_9 t := by
  interval_cases t
  · exact pair_9_0_checked
  · exact pair_9_1_checked
  · exact pair_9_2_checked
  · exact pair_9_3_checked
  · exact pair_9_4_checked
  · exact pair_9_5_checked
  · exact pair_9_6_checked
  · exact pair_9_7_checked
  · exact pair_9_8_checked
  · exact pair_9_9_checked

theorem pair_9_checked : pairFirst 9 = Pair_9 := by
  have h := pairFirst_eq_cached_sum cachedCoordinate chunks_9 9
    (fun t ht => cachedCoordinate_correct t (by omega)) chunks_9_checked
  exact h.trans (by decide +kernel)

certify_pair_chunk 10 0 1 Pair_10_0 pair_10_0_checked
certify_pair_chunk 10 1 1 Pair_10_1 pair_10_1_checked
certify_pair_chunk 10 2 1 Pair_10_2 pair_10_2_checked
certify_pair_chunk 10 3 1 Pair_10_3 pair_10_3_checked
certify_pair_chunk 10 4 1 Pair_10_4 pair_10_4_checked
certify_pair_chunk 10 5 1 Pair_10_5 pair_10_5_checked
noncomputable def Pair_10_6 : Nat := pair_copy% 10 4
theorem pair_10_6_checked : pairChunkWith cachedCoordinate 10 6 1 = Pair_10_6 :=
  (pairChunkWith_mirror cachedCoordinate 10 6 4 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_10_4_checked
noncomputable def Pair_10_7 : Nat := pair_copy% 10 3
theorem pair_10_7_checked : pairChunkWith cachedCoordinate 10 7 1 = Pair_10_7 :=
  (pairChunkWith_mirror cachedCoordinate 10 7 3 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_10_3_checked
noncomputable def Pair_10_8 : Nat := pair_copy% 10 2
theorem pair_10_8_checked : pairChunkWith cachedCoordinate 10 8 1 = Pair_10_8 :=
  (pairChunkWith_mirror cachedCoordinate 10 8 2 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_10_2_checked
noncomputable def Pair_10_9 : Nat := pair_copy% 10 1
theorem pair_10_9_checked : pairChunkWith cachedCoordinate 10 9 1 = Pair_10_9 :=
  (pairChunkWith_mirror cachedCoordinate 10 9 1 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_10_1_checked
certify_pair_chunk 10 10 1 Pair_10_10 pair_10_10_checked

noncomputable def Pair_10 : Nat := pair_sum_numeral% 10

noncomputable def chunks_10 (t : Nat) : Nat :=
  match t with
  | 0 => Pair_10_0
  | 1 => Pair_10_1
  | 2 => Pair_10_2
  | 3 => Pair_10_3
  | 4 => Pair_10_4
  | 5 => Pair_10_5
  | 6 => Pair_10_6
  | 7 => Pair_10_7
  | 8 => Pair_10_8
  | 9 => Pair_10_9
  | 10 => Pair_10_10
  | _ => 0

theorem chunks_10_checked (t : Nat) (ht : t ≤ 10) :
    pairChunkWith cachedCoordinate 10 t 1 = chunks_10 t := by
  interval_cases t
  · exact pair_10_0_checked
  · exact pair_10_1_checked
  · exact pair_10_2_checked
  · exact pair_10_3_checked
  · exact pair_10_4_checked
  · exact pair_10_5_checked
  · exact pair_10_6_checked
  · exact pair_10_7_checked
  · exact pair_10_8_checked
  · exact pair_10_9_checked
  · exact pair_10_10_checked

theorem pair_10_checked : pairFirst 10 = Pair_10 := by
  have h := pairFirst_eq_cached_sum cachedCoordinate chunks_10 10
    (fun t ht => cachedCoordinate_correct t (by omega)) chunks_10_checked
  exact h.trans (by decide +kernel)

certify_pair_chunk 11 0 1 Pair_11_0 pair_11_0_checked
certify_pair_chunk 11 1 1 Pair_11_1 pair_11_1_checked
certify_pair_chunk 11 2 1 Pair_11_2 pair_11_2_checked
certify_pair_chunk 11 3 1 Pair_11_3 pair_11_3_checked
certify_pair_chunk 11 4 1 Pair_11_4 pair_11_4_checked
certify_pair_chunk 11 5 1 Pair_11_5 pair_11_5_checked
noncomputable def Pair_11_6 : Nat := pair_copy% 11 5
theorem pair_11_6_checked : pairChunkWith cachedCoordinate 11 6 1 = Pair_11_6 :=
  (pairChunkWith_mirror cachedCoordinate 11 6 5 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_11_5_checked
noncomputable def Pair_11_7 : Nat := pair_copy% 11 4
theorem pair_11_7_checked : pairChunkWith cachedCoordinate 11 7 1 = Pair_11_7 :=
  (pairChunkWith_mirror cachedCoordinate 11 7 4 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_11_4_checked
noncomputable def Pair_11_8 : Nat := pair_copy% 11 3
theorem pair_11_8_checked : pairChunkWith cachedCoordinate 11 8 1 = Pair_11_8 :=
  (pairChunkWith_mirror cachedCoordinate 11 8 3 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_11_3_checked
noncomputable def Pair_11_9 : Nat := pair_copy% 11 2
theorem pair_11_9_checked : pairChunkWith cachedCoordinate 11 9 1 = Pair_11_9 :=
  (pairChunkWith_mirror cachedCoordinate 11 9 2 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_11_2_checked
noncomputable def Pair_11_10 : Nat := pair_copy% 11 1
theorem pair_11_10_checked : pairChunkWith cachedCoordinate 11 10 1 = Pair_11_10 :=
  (pairChunkWith_mirror cachedCoordinate 11 10 1 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_11_1_checked
certify_pair_chunk 11 11 1 Pair_11_11 pair_11_11_checked

noncomputable def Pair_11 : Nat := pair_sum_numeral% 11

noncomputable def chunks_11 (t : Nat) : Nat :=
  match t with
  | 0 => Pair_11_0
  | 1 => Pair_11_1
  | 2 => Pair_11_2
  | 3 => Pair_11_3
  | 4 => Pair_11_4
  | 5 => Pair_11_5
  | 6 => Pair_11_6
  | 7 => Pair_11_7
  | 8 => Pair_11_8
  | 9 => Pair_11_9
  | 10 => Pair_11_10
  | 11 => Pair_11_11
  | _ => 0

theorem chunks_11_checked (t : Nat) (ht : t ≤ 11) :
    pairChunkWith cachedCoordinate 11 t 1 = chunks_11 t := by
  interval_cases t
  · exact pair_11_0_checked
  · exact pair_11_1_checked
  · exact pair_11_2_checked
  · exact pair_11_3_checked
  · exact pair_11_4_checked
  · exact pair_11_5_checked
  · exact pair_11_6_checked
  · exact pair_11_7_checked
  · exact pair_11_8_checked
  · exact pair_11_9_checked
  · exact pair_11_10_checked
  · exact pair_11_11_checked

theorem pair_11_checked : pairFirst 11 = Pair_11 := by
  have h := pairFirst_eq_cached_sum cachedCoordinate chunks_11 11
    (fun t ht => cachedCoordinate_correct t (by omega)) chunks_11_checked
  exact h.trans (by decide +kernel)

end ClaudeWCT.Numerics.SharedGeneratedPair

namespace ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedPathPacked
certify_pair_chunk 12 0 1 Pair_12_0 pair_12_0_checked
certify_pair_chunk 12 1 1 Pair_12_1 pair_12_1_checked
certify_pair_chunk 12 2 1 Pair_12_2 pair_12_2_checked
certify_pair_chunk 12 3 1 Pair_12_3 pair_12_3_checked
certify_pair_chunk 12 4 1 Pair_12_4 pair_12_4_checked
certify_pair_chunk 12 5 1 Pair_12_5 pair_12_5_checked
certify_pair_chunk 12 6 1 Pair_12_6 pair_12_6_checked
noncomputable def Pair_12_7 : Nat := pair_copy% 12 5
theorem pair_12_7_checked : pairChunkWith cachedCoordinate 12 7 1 = Pair_12_7 :=
  (pairChunkWith_mirror cachedCoordinate 12 7 5 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_12_5_checked
noncomputable def Pair_12_8 : Nat := pair_copy% 12 4
theorem pair_12_8_checked : pairChunkWith cachedCoordinate 12 8 1 = Pair_12_8 :=
  (pairChunkWith_mirror cachedCoordinate 12 8 4 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_12_4_checked
noncomputable def Pair_12_9 : Nat := pair_copy% 12 3
theorem pair_12_9_checked : pairChunkWith cachedCoordinate 12 9 1 = Pair_12_9 :=
  (pairChunkWith_mirror cachedCoordinate 12 9 3 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_12_3_checked
noncomputable def Pair_12_10 : Nat := pair_copy% 12 2
theorem pair_12_10_checked : pairChunkWith cachedCoordinate 12 10 1 = Pair_12_10 :=
  (pairChunkWith_mirror cachedCoordinate 12 10 2 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_12_2_checked
noncomputable def Pair_12_11 : Nat := pair_copy% 12 1
theorem pair_12_11_checked : pairChunkWith cachedCoordinate 12 11 1 = Pair_12_11 :=
  (pairChunkWith_mirror cachedCoordinate 12 11 1 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_12_1_checked
certify_pair_chunk 12 12 1 Pair_12_12 pair_12_12_checked

noncomputable def Pair_12 : Nat := pair_sum_numeral% 12

noncomputable def chunks_12 (t : Nat) : Nat :=
  match t with
  | 0 => Pair_12_0
  | 1 => Pair_12_1
  | 2 => Pair_12_2
  | 3 => Pair_12_3
  | 4 => Pair_12_4
  | 5 => Pair_12_5
  | 6 => Pair_12_6
  | 7 => Pair_12_7
  | 8 => Pair_12_8
  | 9 => Pair_12_9
  | 10 => Pair_12_10
  | 11 => Pair_12_11
  | 12 => Pair_12_12
  | _ => 0

theorem chunks_12_checked (t : Nat) (ht : t ≤ 12) :
    pairChunkWith cachedCoordinate 12 t 1 = chunks_12 t := by
  interval_cases t
  · exact pair_12_0_checked
  · exact pair_12_1_checked
  · exact pair_12_2_checked
  · exact pair_12_3_checked
  · exact pair_12_4_checked
  · exact pair_12_5_checked
  · exact pair_12_6_checked
  · exact pair_12_7_checked
  · exact pair_12_8_checked
  · exact pair_12_9_checked
  · exact pair_12_10_checked
  · exact pair_12_11_checked
  · exact pair_12_12_checked

theorem pair_12_checked : pairFirst 12 = Pair_12 := by
  have h := pairFirst_eq_cached_sum cachedCoordinate chunks_12 12
    (fun t ht => cachedCoordinate_correct t (by omega)) chunks_12_checked
  exact h.trans (by decide +kernel)


end ClaudeWCT.Numerics.SharedGeneratedPair

namespace ClaudeWCT.Numerics.SharedGeneratedForest
open Lean Elab Command
open ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedGeneratedCoordinate
open ClaudeWCT.Numerics.SharedGeneratedFeeVector
open ClaudeWCT.Numerics.SharedFees
set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000
set_option Elab.async false

noncomputable def Forest_5 : Nat := forest_numeral% 5

theorem forest_5_checked : forest 5=Forest_5 := by
  exact (forest_eq_of_inputs 5 Pair_5 Coordinate_128_5
    pair_5_checked coordinate_128_5_checked).trans (by rw [spread_eq_fast]; decide +kernel)



end ClaudeWCT.Numerics.SharedGeneratedForest

namespace ClaudeWCT.Numerics.SharedGeneratedForest
open Lean Elab Command
open ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedGeneratedCoordinate
open ClaudeWCT.Numerics.SharedGeneratedFeeVector
open ClaudeWCT.Numerics.SharedFees
set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000
set_option Elab.async false

noncomputable def Forest_6 : Nat := forest_numeral% 6

theorem forest_6_checked : forest 6=Forest_6 := by
  exact (forest_eq_of_inputs 6 Pair_6 Coordinate_128_6
    pair_6_checked coordinate_128_6_checked).trans (by rw [spread_eq_fast]; decide +kernel)


end ClaudeWCT.Numerics.SharedGeneratedForest

namespace ClaudeWCT.Numerics.SharedGeneratedForest
open Lean Elab Command
open ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedGeneratedCoordinate
open ClaudeWCT.Numerics.SharedGeneratedFeeVector
open ClaudeWCT.Numerics.SharedFees
set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000
set_option Elab.async false

noncomputable def Forest_7 : Nat := forest_numeral% 7

theorem forest_7_checked : forest 7=Forest_7 := by
  exact (forest_eq_of_inputs 7 Pair_7 Coordinate_128_7
    pair_7_checked coordinate_128_7_checked).trans (by rw [spread_eq_fast]; decide +kernel)


end ClaudeWCT.Numerics.SharedGeneratedForest

namespace ClaudeWCT.Numerics.SharedGeneratedForest
open Lean Elab Command
open ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedGeneratedCoordinate
open ClaudeWCT.Numerics.SharedGeneratedFeeVector
open ClaudeWCT.Numerics.SharedFees
set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000
set_option Elab.async false

noncomputable def Forest_8 : Nat := forest_numeral% 8

theorem forest_8_checked : forest 8=Forest_8 := by
  exact (forest_eq_of_inputs 8 Pair_8 Coordinate_128_8
    pair_8_checked coordinate_128_8_checked).trans (by rw [spread_eq_fast]; decide +kernel)


end ClaudeWCT.Numerics.SharedGeneratedForest

namespace ClaudeWCT.Numerics.SharedGeneratedForest
open Lean Elab Command
open ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedGeneratedCoordinate
open ClaudeWCT.Numerics.SharedGeneratedFeeVector
open ClaudeWCT.Numerics.SharedFees
set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000
set_option Elab.async false

noncomputable def Forest_9 : Nat := forest_numeral% 9

theorem forest_9_checked : forest 9=Forest_9 := by
  exact (forest_eq_of_inputs 9 Pair_9 Coordinate_128_9
    pair_9_checked coordinate_128_9_checked).trans (by rw [spread_eq_fast]; decide +kernel)



end ClaudeWCT.Numerics.SharedGeneratedForest

namespace ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedPathPacked
certify_pair_chunk 13 0 1 Pair_13_0 pair_13_0_checked
certify_pair_chunk 13 1 1 Pair_13_1 pair_13_1_checked
certify_pair_chunk 13 2 1 Pair_13_2 pair_13_2_checked
certify_pair_chunk 13 3 1 Pair_13_3 pair_13_3_checked
certify_pair_chunk 13 4 1 Pair_13_4 pair_13_4_checked
certify_pair_chunk 13 5 1 Pair_13_5 pair_13_5_checked
certify_pair_chunk 13 6 1 Pair_13_6 pair_13_6_checked
noncomputable def Pair_13_7 : Nat := pair_copy% 13 6
theorem pair_13_7_checked : pairChunkWith cachedCoordinate 13 7 1 = Pair_13_7 :=
  (pairChunkWith_mirror cachedCoordinate 13 7 6 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_13_6_checked
noncomputable def Pair_13_8 : Nat := pair_copy% 13 5
theorem pair_13_8_checked : pairChunkWith cachedCoordinate 13 8 1 = Pair_13_8 :=
  (pairChunkWith_mirror cachedCoordinate 13 8 5 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_13_5_checked
noncomputable def Pair_13_9 : Nat := pair_copy% 13 4
theorem pair_13_9_checked : pairChunkWith cachedCoordinate 13 9 1 = Pair_13_9 :=
  (pairChunkWith_mirror cachedCoordinate 13 9 4 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_13_4_checked
noncomputable def Pair_13_10 : Nat := pair_copy% 13 3
theorem pair_13_10_checked : pairChunkWith cachedCoordinate 13 10 1 = Pair_13_10 :=
  (pairChunkWith_mirror cachedCoordinate 13 10 3 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_13_3_checked
noncomputable def Pair_13_11 : Nat := pair_copy% 13 2
theorem pair_13_11_checked : pairChunkWith cachedCoordinate 13 11 1 = Pair_13_11 :=
  (pairChunkWith_mirror cachedCoordinate 13 11 2 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_13_2_checked
noncomputable def Pair_13_12 : Nat := pair_copy% 13 1
theorem pair_13_12_checked : pairChunkWith cachedCoordinate 13 12 1 = Pair_13_12 :=
  (pairChunkWith_mirror cachedCoordinate 13 12 1 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_13_1_checked
certify_pair_chunk 13 13 1 Pair_13_13 pair_13_13_checked

noncomputable def Pair_13 : Nat := pair_sum_numeral% 13

noncomputable def chunks_13 (t : Nat) : Nat :=
  match t with
  | 0 => Pair_13_0
  | 1 => Pair_13_1
  | 2 => Pair_13_2
  | 3 => Pair_13_3
  | 4 => Pair_13_4
  | 5 => Pair_13_5
  | 6 => Pair_13_6
  | 7 => Pair_13_7
  | 8 => Pair_13_8
  | 9 => Pair_13_9
  | 10 => Pair_13_10
  | 11 => Pair_13_11
  | 12 => Pair_13_12
  | 13 => Pair_13_13
  | _ => 0

theorem chunks_13_checked (t : Nat) (ht : t ≤ 13) :
    pairChunkWith cachedCoordinate 13 t 1 = chunks_13 t := by
  interval_cases t
  · exact pair_13_0_checked
  · exact pair_13_1_checked
  · exact pair_13_2_checked
  · exact pair_13_3_checked
  · exact pair_13_4_checked
  · exact pair_13_5_checked
  · exact pair_13_6_checked
  · exact pair_13_7_checked
  · exact pair_13_8_checked
  · exact pair_13_9_checked
  · exact pair_13_10_checked
  · exact pair_13_11_checked
  · exact pair_13_12_checked
  · exact pair_13_13_checked

theorem pair_13_checked : pairFirst 13 = Pair_13 := by
  have h := pairFirst_eq_cached_sum cachedCoordinate chunks_13 13
    (fun t ht => cachedCoordinate_correct t (by omega)) chunks_13_checked
  exact h.trans (by decide +kernel)


end ClaudeWCT.Numerics.SharedGeneratedPair

namespace ClaudeWCT.Numerics.SharedGeneratedForest
open Lean Elab Command
open ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedGeneratedCoordinate
open ClaudeWCT.Numerics.SharedGeneratedFeeVector
open ClaudeWCT.Numerics.SharedFees
set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000
set_option Elab.async false

noncomputable def Forest_10 : Nat := forest_numeral% 10

theorem forest_10_checked : forest 10=Forest_10 := by
  exact (forest_eq_of_inputs 10 Pair_10 Coordinate_128_10
    pair_10_checked coordinate_128_10_checked).trans (by rw [spread_eq_fast]; decide +kernel)



end ClaudeWCT.Numerics.SharedGeneratedForest

namespace ClaudeWCT.Numerics.SharedGeneratedForest
open Lean Elab Command
open ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedGeneratedCoordinate
open ClaudeWCT.Numerics.SharedGeneratedFeeVector
open ClaudeWCT.Numerics.SharedFees
set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000
set_option Elab.async false

noncomputable def Forest_11 : Nat := forest_numeral% 11

theorem forest_11_checked : forest 11=Forest_11 := by
  exact (forest_eq_of_inputs 11 Pair_11 Coordinate_128_11
    pair_11_checked coordinate_128_11_checked).trans (by rw [spread_eq_fast]; decide +kernel)



end ClaudeWCT.Numerics.SharedGeneratedForest

namespace ClaudeWCT.Numerics.SharedGeneratedForest
open Lean Elab Command
open ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedGeneratedCoordinate
open ClaudeWCT.Numerics.SharedGeneratedFeeVector
open ClaudeWCT.Numerics.SharedFees
set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000
set_option Elab.async false

noncomputable def Forest_12 : Nat := forest_numeral% 12

theorem forest_12_checked : forest 12=Forest_12 := by
  exact (forest_eq_of_inputs 12 Pair_12 Coordinate_128_12
    pair_12_checked coordinate_128_12_checked).trans (by rw [spread_eq_fast]; decide +kernel)



end ClaudeWCT.Numerics.SharedGeneratedForest

namespace ClaudeWCT.Numerics.SharedGeneratedForest
open Lean Elab Command
open ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedGeneratedCoordinate
open ClaudeWCT.Numerics.SharedGeneratedFeeVector
open ClaudeWCT.Numerics.SharedFees
set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000
set_option Elab.async false

noncomputable def Forest_13 : Nat := forest_numeral% 13

theorem forest_13_checked : forest 13=Forest_13 := by
  exact (forest_eq_of_inputs 13 Pair_13 Coordinate_128_13
    pair_13_checked coordinate_128_13_checked).trans (by rw [spread_eq_fast]; decide +kernel)



end ClaudeWCT.Numerics.SharedGeneratedForest

namespace ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedPathPacked
certify_pair_chunk 14 0 1 Pair_14_0 pair_14_0_checked
certify_pair_chunk 14 1 1 Pair_14_1 pair_14_1_checked
certify_pair_chunk 14 2 1 Pair_14_2 pair_14_2_checked
certify_pair_chunk 14 3 1 Pair_14_3 pair_14_3_checked
certify_pair_chunk 14 4 1 Pair_14_4 pair_14_4_checked
certify_pair_chunk 14 5 1 Pair_14_5 pair_14_5_checked
certify_pair_chunk 14 6 1 Pair_14_6 pair_14_6_checked
certify_pair_chunk 14 7 1 Pair_14_7 pair_14_7_checked
noncomputable def Pair_14_8 : Nat := pair_copy% 14 6
theorem pair_14_8_checked : pairChunkWith cachedCoordinate 14 8 1 = Pair_14_8 :=
  (pairChunkWith_mirror cachedCoordinate 14 8 6 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_14_6_checked
noncomputable def Pair_14_9 : Nat := pair_copy% 14 5
theorem pair_14_9_checked : pairChunkWith cachedCoordinate 14 9 1 = Pair_14_9 :=
  (pairChunkWith_mirror cachedCoordinate 14 9 5 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_14_5_checked
noncomputable def Pair_14_10 : Nat := pair_copy% 14 4
theorem pair_14_10_checked : pairChunkWith cachedCoordinate 14 10 1 = Pair_14_10 :=
  (pairChunkWith_mirror cachedCoordinate 14 10 4 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_14_4_checked
noncomputable def Pair_14_11 : Nat := pair_copy% 14 3
theorem pair_14_11_checked : pairChunkWith cachedCoordinate 14 11 1 = Pair_14_11 :=
  (pairChunkWith_mirror cachedCoordinate 14 11 3 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_14_3_checked
noncomputable def Pair_14_12 : Nat := pair_copy% 14 2
theorem pair_14_12_checked : pairChunkWith cachedCoordinate 14 12 1 = Pair_14_12 :=
  (pairChunkWith_mirror cachedCoordinate 14 12 2 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_14_2_checked
noncomputable def Pair_14_13 : Nat := pair_copy% 14 1
theorem pair_14_13_checked : pairChunkWith cachedCoordinate 14 13 1 = Pair_14_13 :=
  (pairChunkWith_mirror cachedCoordinate 14 13 1 rfl (by decide) (by decide)
    (addFirst_swap _ _ (by decide +kernel))).trans pair_14_1_checked
certify_pair_chunk 14 14 1 Pair_14_14 pair_14_14_checked

noncomputable def Pair_14 : Nat := pair_sum_numeral% 14

noncomputable def chunks_14 (t : Nat) : Nat :=
  match t with
  | 0 => Pair_14_0
  | 1 => Pair_14_1
  | 2 => Pair_14_2
  | 3 => Pair_14_3
  | 4 => Pair_14_4
  | 5 => Pair_14_5
  | 6 => Pair_14_6
  | 7 => Pair_14_7
  | 8 => Pair_14_8
  | 9 => Pair_14_9
  | 10 => Pair_14_10
  | 11 => Pair_14_11
  | 12 => Pair_14_12
  | 13 => Pair_14_13
  | 14 => Pair_14_14
  | _ => 0

theorem chunks_14_checked (t : Nat) (ht : t ≤ 14) :
    pairChunkWith cachedCoordinate 14 t 1 = chunks_14 t := by
  interval_cases t
  · exact pair_14_0_checked
  · exact pair_14_1_checked
  · exact pair_14_2_checked
  · exact pair_14_3_checked
  · exact pair_14_4_checked
  · exact pair_14_5_checked
  · exact pair_14_6_checked
  · exact pair_14_7_checked
  · exact pair_14_8_checked
  · exact pair_14_9_checked
  · exact pair_14_10_checked
  · exact pair_14_11_checked
  · exact pair_14_12_checked
  · exact pair_14_13_checked
  · exact pair_14_14_checked

theorem pair_14_checked : pairFirst 14 = Pair_14 := by
  have h := pairFirst_eq_cached_sum cachedCoordinate chunks_14 14
    (fun t ht => cachedCoordinate_correct t (by omega)) chunks_14_checked
  exact h.trans (by decide +kernel)


end ClaudeWCT.Numerics.SharedGeneratedPair

namespace ClaudeWCT.Numerics.SharedGeneratedForest
open Lean Elab Command
open ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedGeneratedCoordinate
open ClaudeWCT.Numerics.SharedGeneratedFeeVector
open ClaudeWCT.Numerics.SharedFees
set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000
set_option Elab.async false

noncomputable def Forest_14 : Nat := forest_numeral% 14

theorem forest_14_checked : forest 14=Forest_14 := by
  exact (forest_eq_of_inputs 14 Pair_14 Coordinate_128_14
    pair_14_checked coordinate_128_14_checked).trans (by rw [spread_eq_fast]; decide +kernel)



end ClaudeWCT.Numerics.SharedGeneratedForest

end
