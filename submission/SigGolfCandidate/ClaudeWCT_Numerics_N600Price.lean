import SigGolfCandidate.ClaudeWCT_Numerics_N600Price_C

set_option Elab.async false
set_option maxRecDepth 100000
open Finset Polynomial


namespace ClaudeWCT.Numerics.SharedFees
open Finset Polynomial ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem histogram_moment_bound {α : Type} [Fintype α]
    (n total G : Nat) (good : α → Prop) [DecidablePred good] (bin weight : α → Nat)
    (P : Nat[X]) (hP : CoeffLE P (weightedHistogram good bin weight))
    (htotal : (∑ a, weight a)=total)
    (cost : α → ℝ) (fee : Nat → Nat) (κ : ℝ)
    (hκ : 0≤κ) (hfee : ∀ j, j<n → fee j≤G)
    (hglobal : ∀ a, cost a≤κ*(weight a : ℝ)*G)
    (hlocal : ∀ a, good a → bin a<n → cost a≤κ*(weight a : ℝ)*(fee (bin a) : ℝ)) :
    (∑ a, cost a)≤κ*((((∑ j ∈ range n, P.coeff j*fee j) +
      G*(total-(∑ j ∈ range n, P.coeff j)) : Nat) : ℝ)) := by
  classical
  have hm : (∑ j ∈ range n, P.coeff j)≤∑ a, weight a := by
    calc _ ≤ P.eval 1 := sum_coeff_le_eval_one P (range n)
         _ ≤ (weightedHistogram good bin weight).eval 1 := polynomial_mass_mono hP
         _ = ∑ a, if good a then weight a else 0 := weightedHistogram_eval_one good bin weight
         _ ≤ ∑ a, weight a := Finset.sum_le_sum (fun a _ => by split_ifs <;> omega)
  have h := histogram_paid_bound n good bin weight cost P.coeff fee κ G hκ hfee
    (fun j _ => by simpa only [weightedHistogram_coeff] using hP j) hm hglobal hlocal
  simpa only [htotal] using h

theorem sum_fin_list_getD {α : Type} (fs : List α) (fallback : α) (f : Nat → α → Nat) :
    (∑ i : Fin fs.length, f i.val fs[i]) =
      ∑ j ∈ range fs.length, f j (fs[j]?.getD fallback) := by
  calc _ = ∑ i : Fin fs.length, f i.val (fs[i.val]?.getD fallback) := by
         apply Finset.sum_congr rfl
         intro i _
         simp only [List.getElem?_eq_getElem i.isLt, Option.getD_some, Fin.getElem_fin]
       _ = _ := Fin.sum_univ_eq_sum_range (fun j => f j (fs[j]?.getD fallback)) fs.length

theorem paidTree_polynomial_range (fuel : Nat) (fs : List (Nat × Nat)) (P : Nat[X])
    (hc : ∀ j, P.coeff j<2^4096) :
    paidTree fuel fs (P.eval (2^4096)) =
      (∑ j ∈ range fs.length, P.coeff j,
       ∑ j ∈ range fs.length, P.coeff j*(fs[j]?.getD (0,0)).1,
       ∑ j ∈ range fs.length, P.coeff j*(fs[j]?.getD (0,0)).2) := by
  rw [paidTree_polynomial fuel fs P hc, Fin.sum_univ_eq_sum_range,
    sum_fin_list_getD fs (0,0) (fun j e => P.coeff j*e.1),
    sum_fin_list_getD fs (0,0) (fun j e => P.coeff j*e.2)]

#print axioms histogram_moment_bound
#print axioms paidTree_polynomial_range
end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.CanonicalCompression
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem acceptedMass_antitone (hist : List (Nat × Nat)) {floor lower : Nat} (hle : lower ≤ floor) :
    acceptedMass hist floor ≤ acceptedMass hist lower := by
  induction hist with
  | nil => simp [acceptedMass_sum]
  | cons e hist ih =>
      simp only [acceptedMass_sum, List.map_cons, List.sum_cons] at ih ⊢
      by_cases hf : floor ≤ e.1
      · have hl := hle.trans hf
        simp only [if_pos hf, if_pos hl]
        omega
      · by_cases hl : lower ≤ e.1
        · simp only [if_neg hf, if_pos hl]
          omega
        · simp only [if_neg hf, if_neg hl]
          simpa only [Nat.zero_add] using ih

#print axioms acceptedMass_antitone
end ClaudeWCT.Numerics.CanonicalCompression

namespace ClaudeWCT.Numerics.SharedPathPacked
open Finset Polynomial ClaudeWCT.Numerics.N600
open ClaudeWCT.Numerics.SharedDigitBlock ClaudeWCT.Numerics.SharedCoverage
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem prefix_coeff_lt_of_mass (P : Nat[X]) (n B : Nat) (h : P.eval 1*n<B)
    (j : Nat) : (P*geomPoly n).coeff j<B := by
  apply (polynomial_coeff_le_mass _ j).trans_lt
  simpa [Polynomial.eval_mul, geomPoly_eval] using h

theorem directed_polynomial_histogram_lower {α β : Type} [Fintype α] [Fintype β]
    (ga : α → Prop) [DecidablePred ga] (gb : β → Prop) [DecidablePred gb]
    (ba wa : α → Nat) (bb wb : β → Nat)
    (aP aF bP bF : Nat[X]) (lo hi shift Ma Mb : Nat)
    (haP : aP.eval (2^1024)<(2^1024)^2048)
    (haF : aF.eval (2^1024)<(2^1024)^2048)
    (haPc : ∀ j, aP.coeff j<2^1024) (haFc : ∀ j, aF.coeff j<2^1024)
    (hbPm : bP.eval 1*2048<2^1024) (hbFm : bF.eval 1*2048<2^1024)
    (hap : CoeffLE aP (weightedHistogram ga ba (fun _ => 1)))
    (haf : CoeffLE aF (weightedHistogram ga ba wa))
    (hbp : CoeffLE bP (weightedHistogram gb bb (fun _ => 1)))
    (hbf : CoeffLE bF (weightedHistogram gb bb wb))
    (hlo : lo≤hi) (hwa : ∀ a, wa a≤Ma) (hwb : ∀ b, wb b≤Mb)
    (hsize : Fintype.card α*Fintype.card β*(Ma+Mb)<2^1024)
    (k : Nat) (hk : k<2048) :
    digit (2^1024)
      (directedFirst (aP.eval (2^1024),aF.eval (2^1024))
        (prefixes (bP.eval (2^1024)),prefixes (bF.eval (2^1024))) lo hi shift) k ≤
      (weightedHistogram
        (fun p : α×β => ga p.1 ∧ gb p.2 ∧ bb p.2≤ba p.1 ∧
          lo≤ba p.1-bb p.2 ∧ ba p.1-bb p.2≤hi)
        (fun p => ba p.1+shift) (fun p => wa p.1+wb p.2)).coeff k := by
  have da (j : Nat) : digit (2^1024) (aP.eval (2^1024)) j=aP.coeff j :=
    ClaudeWCT.Numerics.eval_div_pow_mod (by positivity) j aP haPc
  have df (j : Nat) : digit (2^1024) (aF.eval (2^1024)) j=aF.coeff j :=
    ClaudeWCT.Numerics.eval_div_pow_mod (by positivity) j aF haFc
  have hbp' (j : Nat) : bP.coeff j≤∑ b, if gb b ∧ bb b=j then 1 else 0 := by
    simpa only [weightedHistogram_coeff] using hbp j
  have hbf' (j : Nat) : bF.coeff j≤∑ b, if gb b ∧ bb b=j then wb b else 0 := by
    simpa only [weightedHistogram_coeff] using hbf j
  have hap' (j : Nat) : digit (2^1024) (aP.eval (2^1024)) j≤
      ∑ a, if ga a ∧ ba a=j then 1 else 0 := by
    rw [da]; simpa only [weightedHistogram_coeff] using hap j
  have haf' (j : Nat) : digit (2^1024) (aF.eval (2^1024)) j≤
      ∑ a, if ga a ∧ ba a=j then wa a else 0 := by
    rw [df]; simpa only [weightedHistogram_coeff] using haf j
  have wp := window_prefix_interval bP (prefix_coeff_lt_of_mass bP 2048 _ hbPm) lo hi
  have wf := window_prefix_interval bF (prefix_coeff_lt_of_mass bF 2048 _ hbFm) lo hi
  apply directed_histogram_lower ga gb ba wa bb wb _ _ bP.coeff bF.coeff lo hi shift
    haP haF ?_ (fun j hj => wp j hlo hj) (fun j hj => wf j hlo hj)
    hap' haf' hbp' hbf' k hk
  intro j hj
  dsimp only
  rw [wp j hlo hj, wf j hlo hj]
  by_cases hl : lo≤j
  · simp only [if_pos hl]
    exact directed_cross_small ga gb ba wa bb wb _ _ bP.coeff bF.coeff
      hap' haf' hbp' hbf' Ma Mb _ hwa hwb hsize j (Ico (j-hi) (j-lo+1))
  · simp only [if_neg hl, Nat.mul_zero, Nat.zero_add]
    positivity

#print axioms prefix_coeff_lt_of_mass
#print axioms directed_polynomial_histogram_lower
end ClaudeWCT.Numerics.SharedPathPacked

namespace ClaudeWCT.Numerics.SharedPathCoordinate
open Finset Polynomial
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open ClaudeWCT.Numerics.SharedPathReflection ClaudeWCT.Numerics.SharedPathList
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

abbrev binList : List Nat := 0 :: binPairs.map Prod.snd

theorem binList_length : binList.length = 11261 := by
  have h := congrArg List.length bin_indices_checked
  simp only [List.length_map, List.length_range'] at h
  simp only [binList, List.length_cons, List.length_map, h]

theorem binList_bound_checked : binList.all (fun b => decide (b<1024)) = true := by decide +kernel

theorem binList_bound (i : Fin binList.length) : binList[i]<1024 := by
  have h := List.all_eq_true.mp binList_bound_checked _ (List.getElem_mem i.isLt)
  exact of_decide_eq_true h

private theorem child_bounds (K : Nat) (hK : K ∈ [64,128]) : 1 ≤ K ∧ K ≤ 128 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hK
  rcases hK with hK | hK <;> subst K <;> decide

theorem history_mass_small {β : Type} [Fintype β] (hβ : Fintype.card β=563)
    (K : Nat) (hK : K ∈ [64,128]) (r : Fin 21) :
    Fintype.card (Fin r.val → Fin K×β)<2^384 ∧
      Fintype.card (Fin r.val → Fin K×β)*(K*563)<2^384 := by
  rw [coordinate_history_card hβ K r.val]
  have hmass := coordinate_mass_small K r.val (child_bounds K hK).2 (by omega)
  refine ⟨?_,hmass⟩
  calc
    (K*563)^r.val = (K*563)^r.val*1 := (Nat.mul_one _).symm
    _ ≤ (K*563)^r.val*(K*563) := Nat.mul_le_mul_left _ (by have := (child_bounds K hK).1; omega)
    _ < 2^384 := hmass

/-- The concrete packed coordinate stores the two retained histograms exactly;
no arithmetic carry can cross the1024-bit bins. -/
theorem coordinate_polynomial {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (K : Nat) (hK : K ∈ [64,128]) (r : Fin 21)
    (hp : ∀ j, (coordinatePoly K r.val).coeff j ≤
      (univ.filter fun E : Fin r.val → Fin K×β => coordinateCoverage val E=j).card) :
    coordinate K r.val =
      ((binnedPoly binList (coordinatePoly K r.val).coeff).eval (2^1024),
       (binnedPoly binList (fun j => j*(coordinatePoly K r.val).coeff j)).eval (2^1024)) := by
  have hm := history_mass_small hβ K hK r
  have h := bucket_no_carry binList (coordinateCoverage val) (coordinatePoly K r.val) hp (K*563)
    (coordinate_coverage_le val hβ) (hm.1.trans_le (by decide +kernel))
    (hm.2.trans_le (by decide +kernel))
  simpa only [coordinate, coordinatePacked_eval, binList] using h.1

theorem coordinate_histogram {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (K : Nat) (hK : K ∈ [64,128]) (r : Fin 21)
    (hp : ∀ j, (coordinatePoly K r.val).coeff j ≤
      (univ.filter fun E : Fin r.val → Fin K×β => coordinateCoverage val E=j).card) :
    CoeffLE (binnedPoly binList (coordinatePoly K r.val).coeff)
      (weightedHistogram (fun E : Fin r.val → Fin K×β => coordinateCoverage val E<binList.length)
        (fun E => binList[coordinateCoverage val E]?.getD 0) (fun _ => 1)) ∧
    CoeffLE (binnedPoly binList (fun j => j*(coordinatePoly K r.val).coeff j))
      (weightedHistogram (fun E : Fin r.val → Fin K×β => coordinateCoverage val E<binList.length)
        (fun E => binList[coordinateCoverage val E]?.getD 0) (coordinateCoverage val)) :=
  coordinate_histograms_lower binList (coordinateCoverage val) (coordinatePoly K r.val) hp

theorem coordinate_mass {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (K : Nat) (hK : K ∈ [64,128]) (r : Fin 21)
    (hp : ∀ j, (coordinatePoly K r.val).coeff j ≤
      (univ.filter fun E : Fin r.val → Fin K×β => coordinateCoverage val E=j).card) :
    (binnedPoly binList (coordinatePoly K r.val).coeff).eval 1<2^384 ∧
    (binnedPoly binList (fun j => j*(coordinatePoly K r.val).coeff j)).eval 1<2^384 := by
  have h := coordinate_histograms_mass binList (coordinateCoverage val) (coordinatePoly K r.val) hp
    (K*563) (coordinate_coverage_le val hβ)
  have hm := history_mass_small hβ K hK r
  exact ⟨h.1.trans_lt hm.1,h.2.trans_lt hm.2⟩

theorem coordinate_size {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (K : Nat) (hK : K ∈ [64,128]) (r : Fin 21)
    (hp : ∀ j, (coordinatePoly K r.val).coeff j ≤
      (univ.filter fun E : Fin r.val → Fin K×β => coordinateCoverage val E=j).card) :
    (coordinate K r.val).1<(2^1024)^1024 ∧ (coordinate K r.val).2<(2^1024)^1024 := by
  have hm := history_mass_small hβ K hK r
  have h := bucket_histogram_bounds binList (coordinateCoverage val) (coordinatePoly K r.val) hp
    (K*563) 1024 (coordinate_coverage_le val hβ) (hm.1.trans_le (by decide +kernel))
      (hm.2.trans_le (by decide +kernel)) binList_bound
  simpa only [coordinate, coordinatePacked_eval, binList] using h

#print axioms coordinate_polynomial
#print axioms coordinate_histogram
#print axioms coordinate_mass
#print axioms coordinate_size
end ClaudeWCT.Numerics.SharedPathCoordinate


namespace ClaudeWCT.Numerics.SharedPathPacked
open Finset Polynomial ClaudeWCT.Numerics.N600
open ClaudeWCT.Numerics.SharedDigitBlock ClaudeWCT.Numerics.SharedCoverage
open ClaudeWCT.Numerics.SharedPathList
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

def pieceValueWith
    (F : Cell → Cell → Nat → Nat → Nat → Nat) (P : Nat → Nat)
    (runs : List (Nat × Nat × Nat)) (a b : Cell) (e : Fin runs.length × Bool) : Nat :=
  if e.2 then
    if runs[e.1].2.1=0 then 0 else
      F b (P a.1,P a.2) (max 1 runs[e.1].1) runs[e.1].2.1 runs[e.1].2.2
  else F a (P b.1,P b.2) runs[e.1].1 runs[e.1].2.1 runs[e.1].2.2

theorem pieceValueWith_reverse
    (F : Cell → Cell → Nat → Nat → Nat → Nat) (P : Nat → Nat)
    (runs : List (Nat × Nat × Nat)) (a b : Cell) (e : Fin runs.length)
    (hz : runs[e].2.1≠0) :
    pieceValueWith F P runs a b (e,true) =
      F b (P a.1,P a.2) (max 1 runs[e].1) runs[e].2.1 runs[e].2.2 := by
  simp only [pieceValueWith, if_true, if_neg hz]

theorem pieceValueWith_forward
    (F : Cell → Cell → Nat → Nat → Nat → Nat) (P : Nat → Nat)
    (runs : List (Nat × Nat × Nat)) (a b : Cell) (e : Fin runs.length) :
    pieceValueWith F P runs a b (e,false) =
      F a (P b.1,P b.2) runs[e].1 runs[e].2.1 runs[e].2.2 := rfl

theorem addPieceValue_model (a b : Cell) (e : AddPiece) :
    addPieceValue a b e=pieceValueWith directedFirst prefixes addRuns a b e := rfl

theorem addPieceValue_forward (a b : Cell) (e : Fin addRuns.length) :
    addPieceValue a b (e,false) =
      directedFirst a (prefixes b.1,prefixes b.2)
        addRuns[e].1 addRuns[e].2.1 addRuns[e].2.2 :=
  (addPieceValue_model a b (e,false)).trans
    (pieceValueWith_forward directedFirst prefixes addRuns a b e)

theorem addPieceValue_reverse (a b : Cell) (e : Fin addRuns.length)
    (hz : addRuns[e].2.1≠0) :
    addPieceValue a b (e,true) =
      directedFirst b (prefixes a.1,prefixes a.2)
        (max 1 addRuns[e].1) addRuns[e].2.1 addRuns[e].2.2 :=
  (addPieceValue_model a b (e,true)).trans
    (pieceValueWith_reverse directedFirst prefixes addRuns a b e hz)

theorem histogram_reverse {α β : Type} [Fintype α] [Fintype β]
    (ga : α → Prop) (gb : β → Prop)
    (ba wa : α → Nat) (bb wb : β → Nat) (lo hi shift : Nat) :
    weightedHistogram
      (fun p : β×α => gb p.1 ∧ ga p.2 ∧ ba p.2≤bb p.1 ∧
        max 1 lo≤bb p.1-ba p.2 ∧ bb p.1-ba p.2≤hi)
      (fun p => bb p.1+shift) (fun p => wb p.1+wa p.2) =
    weightedHistogram
      (fun p : α×β => ga p.1 ∧ gb p.2 ∧ ba p.1<bb p.2 ∧
        lo≤bb p.2-ba p.1 ∧ bb p.2-ba p.1≤hi)
      (fun p => bb p.2+shift) (fun p => wa p.1+wb p.2) := by
  classical
  have he := weightedHistogram_equiv (Equiv.prodComm α β)
    (fun p : β×α => gb p.1 ∧ ga p.2 ∧ ba p.2≤bb p.1 ∧
      max 1 lo≤bb p.1-ba p.2 ∧ bb p.1-ba p.2≤hi)
    (fun p => bb p.1+shift) (fun p => wb p.1+wa p.2)
  have hg : (fun p : α×β => gb p.2 ∧ ga p.1 ∧ ba p.1≤bb p.2 ∧
      max 1 lo≤bb p.2-ba p.1 ∧ bb p.2-ba p.1≤hi) =
      (fun p : α×β => ga p.1 ∧ gb p.2 ∧ ba p.1<bb p.2 ∧
        lo≤bb p.2-ba p.1 ∧ bb p.2-ba p.1≤hi) := by
    funext p
    apply propext
    constructor
    · rintro ⟨hb,ha,hle,hlo,hhi⟩
      exact ⟨ha,hb,by omega,by omega,hhi⟩
    · rintro ⟨ha,hb,hlt,hlo,hhi⟩
      exact ⟨hb,ha,by omega,by omega,hhi⟩
  calc _ = _ := he.symm
       _ = _ := by
        change weightedHistogram
          (fun p : α×β => gb p.2 ∧ ga p.1 ∧ ba p.1≤bb p.2 ∧
            max 1 lo≤bb p.2-ba p.1 ∧ bb p.2-ba p.1≤hi)
          (fun p => bb p.2+shift) (fun p => wb p.2+wa p.1) = _
        rw [hg]
        congr 1
        funext p
        exact Nat.add_comm _ _

theorem addFirst_polynomial_histogram_lower {α β : Type} [Fintype α] [Fintype β]
    (ga : α → Prop) [DecidablePred ga] (gb : β → Prop) [DecidablePred gb]
    (ba wa : α → Nat) (bb wb : β → Nat)
    (aP aF bP bF : Nat[X]) (Ma Mb : Nat)
    (haP : aP.eval (2^1024)<(2^1024)^2048)
    (haF : aF.eval (2^1024)<(2^1024)^2048)
    (hbP : bP.eval (2^1024)<(2^1024)^2048)
    (hbF : bF.eval (2^1024)<(2^1024)^2048)
    (haPm : aP.eval 1*2048<2^1024) (haFm : aF.eval 1*2048<2^1024)
    (hbPm : bP.eval 1*2048<2^1024) (hbFm : bF.eval 1*2048<2^1024)
    (hap : CoeffLE aP (weightedHistogram ga ba (fun _ => 1)))
    (haf : CoeffLE aF (weightedHistogram ga ba wa))
    (hbp : CoeffLE bP (weightedHistogram gb bb (fun _ => 1)))
    (hbf : CoeffLE bF (weightedHistogram gb bb wb))
    (hwa : ∀ a, wa a≤Ma) (hwb : ∀ b, wb b≤Mb)
    (hsize : Fintype.card α*Fintype.card β*(Ma+Mb)<2^1024) :
    addFirst (aP.eval (2^1024),aF.eval (2^1024))
        (bP.eval (2^1024),bF.eval (2^1024))<(2^1024)^2048 ∧
      ∀ j, j<2048 → digit (2^1024)
        (addFirst (aP.eval (2^1024),aF.eval (2^1024))
          (bP.eval (2^1024),bF.eval (2^1024))) j≤
        (weightedHistogram (fun p : α×β => ga p.1 ∧ gb p.2)
          (fun p => mergeBin (ba p.1) (bb p.2)) (fun p => wa p.1+wb p.2)).coeff j := by
  classical
  have coeff (P : Nat[X]) (h : P.eval 1*2048<2^1024) (j : Nat) : P.coeff j<2^1024 := by
    have hc := polynomial_coeff_le_mass P j
    omega
  apply addFirst_histogram_lower ga gb ba wa bb wb _ _ Ma Mb hwa hwb hsize
  intro e k hk
  rcases e with ⟨e,b⟩
  cases b
  · apply (congrArg (fun x => digit (2^1024) x k)
      (addPieceValue_forward (aP.eval (2^1024),aF.eval (2^1024))
        (bP.eval (2^1024),bF.eval (2^1024)) e)).le.trans
    exact directed_polynomial_histogram_lower ga gb ba wa bb wb aP aF bP bF
      addRuns[e].1 addRuns[e].2.1 addRuns[e].2.2 Ma Mb
      haP haF (coeff aP haPm) (coeff aF haFm) hbPm hbFm hap haf hbp hbf
      (add_run_bounds e).1 hwa hwb hsize k hk
  · by_cases hz : addRuns[e].2.1=0
    · simp only [addPieceValue, if_true, hz, digit, Nat.zero_div, Nat.zero_mod]
      exact Nat.zero_le _
    · have hlo : max 1 addRuns[e].1≤addRuns[e].2.1 := by
        have h := (add_run_bounds e).1
        omega
      have hs : Fintype.card β*Fintype.card α*(Mb+Ma)<2^1024 := by
        simpa only [Nat.mul_comm, Nat.add_comm] using hsize
      have h := directed_polynomial_histogram_lower gb ga bb wb ba wa bP bF aP aF
        (max 1 addRuns[e].1) addRuns[e].2.1 addRuns[e].2.2 Mb Ma
        hbP hbF (coeff bP hbPm) (coeff bF hbFm) haPm haFm hbp hbf hap haf
        hlo hwb hwa hs k hk
      have he' := histogram_reverse ga gb ba wa bb wb
        addRuns[e].1 addRuns[e].2.1 addRuns[e].2.2
      have hh := h.trans_eq (congrArg (fun P : Nat[X] => P.coeff k) he')
      exact (congrArg (fun x => digit (2^1024) x k)
        (addPieceValue_reverse (aP.eval (2^1024),aF.eval (2^1024))
          (bP.eval (2^1024),bF.eval (2^1024)) e hz)).le.trans hh

#print axioms addPieceValue_reverse
#print axioms addFirst_polynomial_histogram_lower
end ClaudeWCT.Numerics.SharedPathPacked

namespace ClaudeWCT.Numerics.SharedPathCoordinate
open Finset Polynomial
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open ClaudeWCT.Numerics.SharedPathReflection ClaudeWCT.Numerics.SharedPathList
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

noncomputable abbrev probPoly (K r : Nat) : Nat[X] := binnedPoly binList (coordinatePoly K r).coeff
noncomputable abbrev firstPoly (K r : Nat) : Nat[X] :=
  binnedPoly binList (fun j => j*(coordinatePoly K r).coeff j)

attribute [local irreducible] binnedPoly coordinatePoly

noncomputable def coordinateGood {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    {K r : Nat} (h : Fin r → Fin K×β) : Prop := coordinateCoverage val h<binList.length
noncomputable def coordinateBin {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    {K r : Nat} (h : Fin r → Fin K×β) : Nat := binList[coordinateCoverage val h]?.getD 0

abbrev BranchHistory (β : Type) (K r : Nat) :=
  (Fin r → Fin K×β) × (Fin r → Fin K×β)
noncomputable def branchGood {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    {K r : Nat} (h : BranchHistory β K r) : Prop :=
  coordinateGood val h.1 ∧ coordinateGood val h.2
noncomputable def branchBin {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    {K r : Nat} (h : BranchHistory β K r) : Nat := coordinateBin val h.1+coordinateBin val h.2
noncomputable def branchCoverage {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    {K r : Nat} (h : BranchHistory β K r) : Nat :=
  coordinateCoverage val h.1*coordinateCoverage val h.2

theorem branch_bin_bound {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) {K r : Nat} (h : BranchHistory β K r)
    (hg : branchGood val h) : branchBin val h<2047 := by
  have hb (a : Fin r → Fin K×β) (ha : coordinateGood val a) : coordinateBin val a<1024 := by
    unfold coordinateGood at ha
    unfold coordinateBin
    rw [List.getElem?_eq_getElem ha]
    exact binList_bound ⟨coordinateCoverage val a,ha⟩
  have h1 := hb h.1 hg.1
  have h2 := hb h.2 hg.2
  unfold branchBin
  omega

theorem branch_histogram {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (K : Nat) (hK : K ∈ [64,128]) (r : Fin 21)
    (hp : ∀ j, (coordinatePoly K r.val).coeff j ≤
      (univ.filter fun E : Fin r.val → Fin K×β => coordinateCoverage val E=j).card) :
    CoeffLE ((probPoly K r.val)^2) (weightedHistogram (branchGood val)
      (branchBin val) (fun _ : BranchHistory β K r.val => 1)) ∧
    CoeffLE ((firstPoly K r.val)^2) (weightedHistogram (branchGood val)
      (branchBin val) (branchCoverage (K:=K) (r:=r.val) val)) := by
  have h := coordinate_histogram val hβ K hK r hp
  unfold probPoly firstPoly branchGood branchBin branchCoverage coordinateGood coordinateBin
  constructor
  · simpa only [pow_two, probPoly, branchGood, coordinateGood, branchBin, coordinateBin,
      Nat.one_mul] using weightedHistogram_product_lower
        (fun E : Fin r.val → Fin K×β => coordinateCoverage val E<binList.length)
        (fun E : Fin r.val → Fin K×β => coordinateCoverage val E<binList.length)
        (fun E => binList[coordinateCoverage val E]?.getD 0) (fun _ => 1)
        (fun E => binList[coordinateCoverage val E]?.getD 0) (fun _ => 1)
        _ _ h.1 h.1
  · simpa only [pow_two, firstPoly, branchGood, coordinateGood, branchBin, coordinateBin,
      branchCoverage] using weightedHistogram_product_lower
        (fun E : Fin r.val → Fin K×β => coordinateCoverage val E<binList.length)
        (fun E : Fin r.val → Fin K×β => coordinateCoverage val E<binList.length)
        (fun E => binList[coordinateCoverage val E]?.getD 0) (coordinateCoverage val)
        (fun E => binList[coordinateCoverage val E]?.getD 0) (coordinateCoverage val)
        _ _ h.2 h.2

theorem product_polynomial {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (K : Nat) (hK : K ∈ [64,128]) (r : Fin 21)
    (hp : ∀ j, (coordinatePoly K r.val).coeff j ≤
      (univ.filter fun E : Fin r.val → Fin K×β => coordinateCoverage val E=j).card) :
    SharedPathPacked.product (coordinate K r.val) =
      (((probPoly K r.val)^2).eval (2^1024), ((firstPoly K r.val)^2).eval (2^1024)) := by
  rw [coordinate_polynomial val hβ K hK r hp]
  simp only [SharedPathPacked.product, Polynomial.eval_pow, probPoly, firstPoly]

theorem square_mass (a : Nat) (ha : a<2^384) : a^2*2048<2^1024 := by
  have h : a^2≤(2^384)^2 := Nat.pow_le_pow_left ha.le 2
  exact lt_of_le_of_lt (Nat.mul_le_mul_right 2048 h) (by decide +kernel)

theorem product_mass {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (K : Nat) (hK : K ∈ [64,128]) (r : Fin 21)
    (hp : ∀ j, (coordinatePoly K r.val).coeff j ≤
      (univ.filter fun E : Fin r.val → Fin K×β => coordinateCoverage val E=j).card) :
    ((probPoly K r.val)^2).eval 1*2048<2^1024 ∧
      ((firstPoly K r.val)^2).eval 1*2048<2^1024 := by
  have hm := coordinate_mass val hβ K hK r hp
  simpa only [Polynomial.eval_pow, probPoly, firstPoly] using
    And.intro (square_mass _ hm.1) (square_mass _ hm.2)

theorem product_size {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (K : Nat) (hK : K ∈ [64,128]) (r : Fin 21)
    (hp : ∀ j, (coordinatePoly K r.val).coeff j ≤
      (univ.filter fun E : Fin r.val → Fin K×β => coordinateCoverage val E=j).card) :
    (SharedPathPacked.product (coordinate K r.val)).1<(2^1024)^2048 ∧
      (SharedPathPacked.product (coordinate K r.val)).2<(2^1024)^2048 := by
  have hm := coordinate_size val hβ K hK r hp
  have hs (a : Nat) (ha : a<(2^1024)^1024) : a^2<(2^1024)^2048 := by
    have h := Nat.pow_lt_pow_left ha (by decide : 2≠0)
    simpa only [← pow_mul] using h
  exact ⟨hs _ hm.1,hs _ hm.2⟩

theorem split_product_size {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (r t : Nat) (hr : r≤20) (ht : t≤r)
    (hp : ∀ u, u≤r → ∀ j, (coordinatePoly 64 u).coeff j ≤
      (univ.filter fun E : Fin u → Fin 64×β => coordinateCoverage val E=j).card) :
    (SharedPathPacked.product (coordinate 64 t)).1<(2^1024)^2048 ∧
    (SharedPathPacked.product (coordinate 64 t)).2<(2^1024)^2048 ∧
    (SharedPathPacked.product (coordinate 64 (r-t))).1<(2^1024)^2048 ∧
    (SharedPathPacked.product (coordinate 64 (r-t))).2<(2^1024)^2048 := by
  have h1 := product_size val hβ 64 (by simp) (⟨t,by omega⟩ : Fin 21) (hp t ht)
  have h2 := product_size val hβ 64 (by simp) (⟨r-t,by omega⟩ : Fin 21) (hp (r-t) (Nat.sub_le ..))
  exact ⟨h1.1,h1.2,h2.1,h2.2⟩

#print axioms branch_histogram
#print axioms product_polynomial
#print axioms product_mass
#print axioms product_size
#print axioms split_product_size
open Finset Polynomial
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem branch_coverage_le {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    {K r : Nat} (h : BranchHistory β K r) : branchCoverage val h≤(K*563)^2 := by
  exact (Nat.mul_le_mul (coordinate_coverage_le val hβ h.1)
    (coordinate_coverage_le val hβ h.2)).trans_eq (pow_two _).symm

theorem split_branch_mass {β : Type} [Fintype β]
    (hβ : Fintype.card β=563) (r t : Nat) (hr : r≤20) (ht : t≤r) :
    Fintype.card (BranchHistory β 64 t)*Fintype.card (BranchHistory β 64 (r-t))*
      ((64*563)^2+(64*563)^2)<2^1024 := by
  simp only [BranchHistory, Fintype.card_prod, coordinate_history_card hβ]
  have he : (64*563)^t*(64*563)^t*((64*563)^(r-t)*(64*563)^(r-t)) =
      ((64*563)^r)^2 := by
    calc
      _ = ((64*563)^t*(64*563)^(r-t))^2 := by ring
      _ = _ := by rw [← pow_add, Nat.add_sub_of_le ht]
  rw [he]
  have hs : ((64*563)^r)^2*((64*563)^2+(64*563)^2) =
      ((64*563)^r*(64*563))^2*2 := by ring
  rw [hs]
  have hmass := coordinate_mass_small 64 r (by decide) hr
  have h := square_mass _ hmass
  exact lt_of_le_of_lt (Nat.mul_le_mul_left _ (by decide : 2≤2048)) h

#print axioms split_branch_mass
end ClaudeWCT.Numerics.SharedPathCoordinate


namespace ClaudeWCT.Numerics.SharedPathList
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false

def runsCoverCheck : List (Nat × Nat × Nat) → Nat → Nat → Bool
  | [], start, finish => decide (start=finish)
  | e::es, start, finish => decide (e.1=start ∧ start≤e.2.1) &&
      runsCoverCheck es (e.2.1+1) finish

theorem runsCoverCheck_sound (runs : List (Nat × Nat × Nat)) (start finish d : Nat)
    (h : runsCoverCheck runs start finish=true) (hd : start≤d ∧ d<finish) :
    ∃ e ∈ runs, e.1≤d ∧ d≤e.2.1 := by
  induction runs generalizing start with
  | nil => simp only [runsCoverCheck, decide_eq_true_eq] at h; omega
  | cons e es ih =>
    simp only [runsCoverCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    by_cases he : d≤e.2.1
    · exact ⟨e,List.mem_cons_self,by omega,he⟩
    · obtain ⟨v,hv,hvd⟩ := ih (e.2.1+1) h.2 (by omega)
      exact ⟨v,List.mem_cons_of_mem _ hv,hvd⟩

theorem add_runs_contiguous : runsCoverCheck addRuns 0 2047=true := by decide +kernel

theorem add_runs_cover_checked (d : Fin 2047) : ∃ e : Fin addRuns.length,
    addRuns[e].1 ≤ d.val ∧ d.val ≤ addRuns[e].2.1 := by
  obtain ⟨v,hv,hd⟩ := runsCoverCheck_sound addRuns 0 2047 d.val
    add_runs_contiguous ⟨Nat.zero_le _,d.isLt⟩
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hv
  refine ⟨i,?_⟩
  simpa only [←hi, List.get_eq_getElem, Fin.getElem_fin] using hd

theorem mergeBin_interval_of_lt (i j : Nat) (hi : i<2047) (hj : j<2047) :
    (101/100 : ℝ)^(mergeBin i j)*(100/101) ≤ (101/100 : ℝ)^i+(101/100 : ℝ)^j ∧
      (101/100 : ℝ)^i+(101/100 : ℝ)^j ≤ (101/100 : ℝ)^(mergeBin i j) := by
  rcases le_total j i with hji|hij
  · obtain ⟨e,hlo,hhi⟩ := add_runs_cover_checked ⟨i-j,by omega⟩
    exact mergeBin_interval e i j hji hlo hhi
  · obtain ⟨e,hlo,hhi⟩ := add_runs_cover_checked ⟨j-i,by omega⟩
    have h := mergeBin_interval e j i hij hlo hhi
    simpa only [mergeBin_comm j i, add_comm] using h

theorem RoundedInterval.merge {a i j : Nat} {x y : ℝ}
    (hx : RoundedInterval a i x) (hy : RoundedInterval a j y)
    (hi : i<2047) (hj : j<2047) :
    RoundedInterval (a+1) (mergeBin i j) (x+y) := by
  have h := mergeBin_interval_of_lt i j hi hj
  exact hx.add hy h.1 h.2

#print axioms add_runs_cover_checked
#print axioms RoundedInterval.merge
end ClaudeWCT.Numerics.SharedPathList


namespace ClaudeWCT.Numerics.SharedFees
open Finset Polynomial
open scoped BigOperators Polynomial
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false

noncomputable def reverseFeePoly (n : Nat) (f : Nat → Nat) : Nat[X] :=
  ∑ i ∈ range n, C (f i)*X^(n-1-i)

theorem reverseFeePoly_eval_one (n : Nat) (f : Nat → Nat) :
    (reverseFeePoly n f).eval 1=∑ i ∈ range n, f i := by
  simp only [reverseFeePoly, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, one_pow, mul_one]

theorem reverseFeePoly_dot (P : Nat[X]) (n : Nat) (f : Nat → Nat) :
    (P*reverseFeePoly n f).coeff (n-1)=∑ i ∈ range n, P.coeff i*f i := by
  simp only [reverseFeePoly, Finset.mul_sum, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  rw [←mul_assoc, Polynomial.coeff_mul_X_pow', if_pos (by omega),
    show n-1-(n-1-i)=i by omega, Polynomial.coeff_mul_C]

theorem packed_convolution_dot (P : Nat[X]) (B n : Nat) (f : Nat → Nat)
    (hB : 0<B) (hmass : P.eval 1*(∑ i ∈ range n, f i)<B) :
    (P.eval B*(reverseFeePoly n f).eval B/B^(n-1))%B =
      ∑ i ∈ range n, P.coeff i*f i := by
  have hc (i : Nat) : (P*reverseFeePoly n f).coeff i<B := by
    have h := ClaudeWCT.Numerics.N600.sum_coeff_le_eval_one (P*reverseFeePoly n f) {i}
    simp only [Finset.sum_singleton, Polynomial.eval_mul, reverseFeePoly_eval_one] at h
    exact h.trans_lt hmass
  rw [←Polynomial.eval_mul]
  exact (ClaudeWCT.Numerics.eval_div_pow_mod hB (n-1) (P*reverseFeePoly n f) hc).trans
    (reverseFeePoly_dot P n f)

#print axioms packed_convolution_dot
end ClaudeWCT.Numerics.SharedFees


namespace ClaudeWCT.Numerics.SharedPathPair
open Finset Polynomial
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open ClaudeWCT.Numerics.SharedPathList ClaudeWCT.Numerics.SharedPathCoordinate
open ClaudeWCT.Numerics.SharedPathPacked ClaudeWCT.Numerics.SharedDigitBlock
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
attribute [local irreducible] binnedPoly coordinatePoly coordinate SharedPathPacked.product SharedPathPacked.addFirst

noncomputable def splitGood {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    (t u : Nat) (h : BranchHistory β 64 t × BranchHistory β 64 u) : Prop :=
  if t=0 then branchGood val h.2 else if u=0 then branchGood val h.1 else
    branchGood val h.1 ∧ branchGood val h.2
noncomputable def splitBin {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    (t u : Nat) (h : BranchHistory β 64 t × BranchHistory β 64 u) : Nat :=
  if t=0 then branchBin val h.2 else if u=0 then branchBin val h.1 else
    mergeBin (branchBin val h.1) (branchBin val h.2)
noncomputable def splitWeight {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    (t u : Nat) (h : BranchHistory β 64 t × BranchHistory β 64 u) : Nat :=
  branchCoverage val h.1+branchCoverage val h.2

def splitRow (r t : Nat) : Nat :=
  let a := SharedPathPacked.product (coordinate 64 t)
  let b := SharedPathPacked.product (coordinate 64 (r-t))
  if t=0 then b.2 else if r-t=0 then a.2 else addFirst a b

end ClaudeWCT.Numerics.SharedPathPair

namespace ClaudeWCT.Numerics.SharedPathPair
open Finset Polynomial
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open ClaudeWCT.Numerics.SharedPathReflection ClaudeWCT.Numerics.SharedPathList
open ClaudeWCT.Numerics.SharedPathCoordinate ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedDigitBlock
open scoped BigOperators Polynomial
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
attribute [local irreducible] binnedPoly coordinatePoly coordinate SharedPathPacked.product SharedPathPacked.addFirst

noncomputable def pairGood {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    {r : Nat} (h : PairHistory β r) : Prop :=
  splitGood val (occ h.1 0) (occ h.1 1)
    ((splitRanks h.1 h.2.1 0,splitRanks h.1 h.2.2 0),
     (splitRanks h.1 h.2.1 1,splitRanks h.1 h.2.2 1))
noncomputable def pairBin {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    {r : Nat} (h : PairHistory β r) : Nat :=
  splitBin val (occ h.1 0) (occ h.1 1)
    ((splitRanks h.1 h.2.1 0,splitRanks h.1 h.2.2 0),
     (splitRanks h.1 h.2.1 1,splitRanks h.1 h.2.2 1))

end ClaudeWCT.Numerics.SharedPathPair

namespace ClaudeWCT.Numerics.SharedPathPair
open Finset Polynomial
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open ClaudeWCT.Numerics.SharedPathReflection ClaudeWCT.Numerics.SharedPathList
open ClaudeWCT.Numerics.SharedPathCoordinate
open scoped BigOperators Polynomial
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
attribute [local irreducible] binnedPoly coordinatePoly coordinate SharedPathPacked.product SharedPathPacked.addFirst

theorem coordinate_empty {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    (K : Nat) (h : Fin 0 → Fin K×β) : coordinateCoverage val h=0 := by
  classical
  unfold coordinateCoverage
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  obtain ⟨i,hi⟩ := (Finset.mem_filter.mp ha).2 (0 : Fin 6)
  exact Fin.elim0 i

theorem branch_empty {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    (K : Nat) (h : BranchHistory β K 0) : branchCoverage val h=0 := by
  simp only [branchCoverage, coordinate_empty, Nat.zero_mul]

theorem coordinate_interval {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    {K r : Nat} (hr : 0<r) (h : Fin r → Fin K×β) (hg : coordinateGood val h) :
    RoundedInterval 1 (coordinateBin val h) (coordinateCoverage val h : ℝ) := by
  have hpos := coordinate_coverage_pos val hr h
  have hlen : coordinateCoverage val h≤11260 := by
    unfold coordinateGood at hg
    rw [binList_length] at hg
    omega
  have hb := bin_lookup_bounds bin_runs_checked bin_indices_checked
    (coordinateCoverage val h) (by omega) hlen
  have he : bins[coordinateCoverage val h]?.getD 0=coordinateBin val h := by
    simp only [bins, coordinateBin, binList, List.getElem?_toArray]
  rw [he] at hb
  have hi := geometric_bin_interval _ _ hb.1 hb.2
  exact ⟨by positivity,by simpa only [pow_one,mul_comm] using hi.1,hi.2⟩

theorem branch_interval {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    {K r : Nat} (hr : 0<r) (h : BranchHistory β K r) (hg : branchGood val h) :
    RoundedInterval 2 (branchBin val h) (branchCoverage val h : ℝ) := by
  have h1 := coordinate_interval val hr h.1 hg.1
  have h2 := coordinate_interval val hr h.2 hg.2
  simpa only [branchBin, branchCoverage, Nat.cast_mul] using h1.mul h2

theorem interval_weaken {a b i : Nat} {x : ℝ}
    (h : RoundedInterval a i x) (hab : a≤b) : RoundedInterval b i x := by
  refine ⟨h.nonneg,?_,h.upper⟩
  apply le_trans ?_ h.lower
  apply mul_le_mul_of_nonneg_right ?_ (by positivity)
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hab

theorem split_interval {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    (t u : Nat) (hpos : 0<t+u) (h : BranchHistory β 64 t × BranchHistory β 64 u)
    (hg : splitGood val t u h) :
    RoundedInterval 3 (splitBin val t u h) (splitWeight val t u h : ℝ) := by
  by_cases ht : t=0
  · subst t
    have hu : 0<u := by omega
    have hI := interval_weaken (branch_interval val hu h.2 (by simpa only [splitGood,ite_true] using hg)) (by decide : 2≤3)
    simpa only [splitBin,splitWeight,ite_true,branch_empty,Nat.zero_add] using hI
  · by_cases hu : u=0
    · subst u
      have ht' : 0<t := by omega
      have hI := interval_weaken (branch_interval val ht' h.1 (by simpa only [splitGood,if_neg ht,ite_true] using hg)) (by decide : 2≤3)
      simpa only [splitBin,splitWeight,if_neg ht,ite_true,branch_empty,Nat.add_zero] using hI
    · have hg' : branchGood val h.1 ∧ branchGood val h.2 := by
        simpa only [splitGood,if_neg ht,if_neg hu] using hg
      have h1 := branch_interval val (by omega : 0<t) h.1 hg'.1
      have h2 := branch_interval val (by omega : 0<u) h.2 hg'.2
      have hI := h1.merge h2 (branch_bin_bound val h.1 hg'.1) (branch_bin_bound val h.2 hg'.2)
      simpa only [splitBin,splitWeight,if_neg ht,if_neg hu,Nat.cast_add] using hI

theorem pair_interval {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    {r : Nat} (hr : 0<r) (h : PairHistory β r) (hg : pairGood val h) :
    RoundedInterval 3 (pairBin val h) (pairCoverage val h : ℝ) := by
  have hs : occ h.1 0+occ h.1 1=r := by
    simpa only [Fin.sum_univ_two] using occ_sum h.1
  exact split_interval val _ _ (by omega)
    ((splitRanks h.1 h.2.1 0,splitRanks h.1 h.2.2 0),
     (splitRanks h.1 h.2.1 1,splitRanks h.1 h.2.2 1)) hg

#print axioms pair_interval
end ClaudeWCT.Numerics.SharedPathPair


namespace ClaudeWCT.Numerics.SharedPathPair
open Finset Polynomial
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open ClaudeWCT.Numerics.SharedPathList ClaudeWCT.Numerics.SharedPathCoordinate
open ClaudeWCT.Numerics.SharedPathPacked ClaudeWCT.Numerics.SharedDigitBlock
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
attribute [local irreducible] binnedPoly coordinatePoly coordinate SharedPathPacked.product SharedPathPacked.addFirst

private theorem histogram_left_unique_lower {α β : Type} [Fintype α] [Unique α] [Fintype β]
    (g : β → Prop) (b w : β → Nat) (v : α → Nat) :
    CoeffLE (weightedHistogram g b w)
      (weightedHistogram (fun p : α×β => g p.2) (fun p => b p.2) (fun p => v p.1+w p.2)) := by
  classical
  intro j
  rw [weightedHistogram_coeff, weightedHistogram_coeff, Fintype.sum_prod_type]
  simp only [Fintype.sum_unique]
  apply Finset.sum_le_sum
  intro a _
  split_ifs <;> omega

private theorem histogram_right_unique_lower {α β : Type} [Fintype α] [Fintype β] [Unique β]
    (g : α → Prop) (b w : α → Nat) (v : β → Nat) :
    CoeffLE (weightedHistogram g b w)
      (weightedHistogram (fun p : α×β => g p.1) (fun p => b p.1) (fun p => w p.1+v p.2)) := by
  classical
  intro j
  rw [weightedHistogram_coeff, weightedHistogram_coeff, Fintype.sum_prod_type]
  simp only [Fintype.sum_unique]
  apply Finset.sum_le_sum
  intro a _
  split_ifs <;> omega

theorem product_first_digit {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (K : Nat) (hK : K∈[64,128]) (r : Fin 21)
    (hp : ∀ j, (coordinatePoly K r.val).coeff j ≤
      (univ.filter fun E : Fin r.val → Fin K×β => coordinateCoverage val E=j).card) (j : Nat) :
    digit (2^1024) (SharedPathPacked.product (coordinate K r.val)).2 j =
      ((firstPoly K r.val)^2).coeff j := by
  rw [product_polynomial val hβ K hK r hp]
  exact ClaudeWCT.Numerics.eval_div_pow_mod (by positivity) j _ (fun i => by
    have h1 := (product_mass val hβ K hK r hp).2
    have h2 := polynomial_coeff_le_mass ((firstPoly K r.val)^2) i
    omega)

theorem split_row_histogram {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (r t : Nat) (hr : r≤20) (ht : t≤r)
    (hp : ∀ u, u≤r → ∀ j, (coordinatePoly 64 u).coeff j ≤
      (univ.filter fun E : Fin u → Fin 64×β => coordinateCoverage val E=j).card) :
    splitRow r t<(2^1024)^2048 ∧
      ∀ j, j<2048 → digit (2^1024) (splitRow r t) j ≤
        (weightedHistogram (splitGood val t (r-t)) (splitBin val t (r-t))
          (splitWeight val t (r-t))).coeff j := by
  classical
  have hsize := split_product_size val hβ r t hr ht hp
  have ht' : t<21 := by omega
  have hu' : r-t<21 := by omega
  have hPt := branch_histogram val hβ 64 (by simp) (⟨t,ht'⟩ : Fin 21) (hp t ht)
  have hPu := branch_histogram val hβ 64 (by simp) (⟨r-t,hu'⟩ : Fin 21) (hp _ (Nat.sub_le ..))
  letI : Unique (BranchHistory β 64 0) := {
    default := (Fin.elim0, Fin.elim0)
    uniq := by intro x; apply Prod.ext <;> funext i <;> exact Fin.elim0 i }
  unfold splitGood splitBin splitWeight
  by_cases h0 : t=0
  · subst t
    simp only [splitRow, if_pos rfl, Nat.sub_zero, ite_true]
    refine ⟨hsize.2.2.2,?_⟩
    intro j hj
    rw [product_first_digit val hβ 64 (by simp) (⟨r,by omega⟩ : Fin 21) (hp r le_rfl)]
    apply (hPu.2 j).trans
    simpa only [splitGood, splitBin, splitWeight, if_pos rfl, Nat.sub_zero, ite_true] using
      histogram_left_unique_lower (α:=BranchHistory β 64 0)
        (branchGood (K:=64) (r:=r) val) (branchBin val) (branchCoverage val)
        (branchCoverage val) j
  · by_cases h1 : r-t=0
    · have htr : t=r := by omega
      subst t
      letI : Unique (BranchHistory β 64 (r-r)) := by
        simpa only [Nat.sub_self] using (inferInstance : Unique (BranchHistory β 64 0))
      simp only [splitRow, if_neg h0, Nat.sub_self, if_pos rfl, ite_true]
      refine ⟨hsize.2.1,?_⟩
      intro j hj
      rw [product_first_digit val hβ 64 (by simp) (⟨r,by omega⟩ : Fin 21) (hp r le_rfl)]
      apply (hPt.2 j).trans
      simpa only [splitGood, splitBin, splitWeight, if_neg h0, Nat.sub_self, if_pos rfl, ite_true] using
        histogram_right_unique_lower (β:=BranchHistory β 64 (r-r))
          (branchGood (K:=64) (r:=r) val) (branchBin val) (branchCoverage val)
          (branchCoverage val) j
    · have hmt := product_mass val hβ 64 (by simp) (⟨t,ht'⟩ : Fin 21) (hp t ht)
      have hmu := product_mass val hβ 64 (by simp) (⟨r-t,hu'⟩ : Fin 21) (hp _ (Nat.sub_le ..))
      have hEt := product_polynomial val hβ 64 (by simp) (⟨t,ht'⟩ : Fin 21) (hp t ht)
      have hEu := product_polynomial val hβ 64 (by simp) (⟨r-t,hu'⟩ : Fin 21) (hp _ (Nat.sub_le ..))
      rw [hEt,hEu] at hsize
      have h := addFirst_polynomial_histogram_lower
        (branchGood (K:=64) (r:=t) val) (branchGood (K:=64) (r:=r-t) val)
        (branchBin val) (branchCoverage val) (branchBin val) (branchCoverage val)
        ((probPoly 64 t)^2) ((firstPoly 64 t)^2) ((probPoly 64 (r-t))^2) ((firstPoly 64 (r-t))^2)
        ((64*563)^2) ((64*563)^2)
        hsize.1 hsize.2.1 hsize.2.2.1 hsize.2.2.2 hmt.1 hmt.2 hmu.1 hmu.2
        hPt.1 hPt.2 hPu.1 hPu.2
        (branch_coverage_le val hβ) (branch_coverage_le val hβ) (split_branch_mass hβ r t hr ht)
      simpa only [splitRow, if_neg h0, if_neg h1, hEt, hEu, splitGood, splitBin, splitWeight, ite_true] using h

#print axioms product_first_digit
#print axioms split_row_histogram
end ClaudeWCT.Numerics.SharedPathPair


namespace ClaudeWCT.Numerics.SharedPathPair
open Finset Polynomial
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open ClaudeWCT.Numerics.SharedPathReflection ClaudeWCT.Numerics.SharedPathList
open ClaudeWCT.Numerics.SharedPathCoordinate ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedDigitBlock
open scoped BigOperators Polynomial
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
attribute [local irreducible] binnedPoly coordinatePoly coordinate SharedPathPacked.product SharedPathPacked.addFirst

theorem pair_histogram_split {β : Type} [Fintype β] (val : β → Fin 6 → Nat) (r : Nat) :
    weightedHistogram (pairGood (r:=r) val) (pairBin val) (pairCoverage val) =
      ∑ t ∈ range (r+1), r.choose t • weightedHistogram (splitGood val t (r-t))
        (splitBin val t (r-t)) (splitWeight val t (r-t)) := by
  exact weightedHistogram_selector_split r
    (fun t u A B C D => splitGood val t u ((A,B),(C,D)))
    (fun t u A B C D => splitBin val t u ((A,B),(C,D)))
    (fun t u A B C D => splitWeight val t u ((A,B),(C,D)))

private theorem range_map_sum (n : Nat) (f : Nat → Nat) :
    ((List.range n).map f).sum = ∑ t ∈ range n, f t := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.range_succ, List.map_append, List.sum_append,
      List.map_singleton, List.sum_singleton, ih, Finset.sum_range_succ]

theorem pairFirst_sum (r : Nat) :
    pairFirst r = ∑ t ∈ range (r+1), r.choose t * splitRow r t := by
  classical
  unfold pairFirst
  rw [foldl_weighted_sum, Nat.zero_add, range_map_sum]
  apply Finset.sum_congr rfl
  intro t ht
  have htr : t≤r := by have h := Finset.mem_range.mp ht; omega
  have ht' : t<r+1 := by omega
  have hu' : r-t<r+1 := by omega
  have get (u : Nat) (hu : u<r+1) :
      ((List.range (r+1)).map fun t => SharedPathPacked.product (coordinate 64 t)).getD u (0,0) =
        SharedPathPacked.product (coordinate 64 u) := by
    rw [List.getD_eq_getElem _ _ (by simpa using hu)]
    simp only [List.getElem_map, List.getElem_range]
  rw [get t ht', get (r-t) hu']
  rw [PoissonReflect.fact_eq, PoissonReflect.fact_eq, PoissonReflect.fact_eq, ← Nat.choose_eq_factorial_div_factorial htr]
  rfl

private theorem eval_nsmul_nat (P : Nat[X]) (n B : Nat) :
    (n • P).eval B=n*P.eval B := by
  induction n with
  | zero => simp only [zero_nsmul,Polynomial.eval_zero,Nat.zero_mul]
  | succ n ih => rw [succ_nsmul,Polynomial.eval_add,ih,Nat.succ_mul]

private theorem coeff_nsmul_nat (P : Nat[X]) (n j : Nat) :
    (n • P).coeff j=n*P.coeff j := by
  induction n with
  | zero => simp only [zero_nsmul,Polynomial.coeff_zero,Nat.zero_mul]
  | succ n ih => rw [succ_nsmul,Polynomial.coeff_add,ih,Nat.succ_mul]

noncomputable def pairPoly (r : Nat) : Nat[X] :=
  ∑ t ∈ range (r+1), r.choose t • packedPoly (2^1024) 2048 (splitRow r t)

theorem pair_polynomial {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (r : Nat) (hr : r≤20)
    (hp : ∀ u, u≤r → ∀ j, (coordinatePoly 64 u).coeff j ≤
      (univ.filter fun E : Fin u → Fin 64×β => coordinateCoverage val E=j).card) :
    (pairPoly r).eval (2^1024)=pairFirst r ∧
      CoeffLE (pairPoly r) (weightedHistogram (pairGood val) (pairBin val) (pairCoverage (r:=r) val)) := by
  classical
  constructor
  · rw [pairFirst_sum]
    unfold pairPoly
    rw [Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro t ht
    rw [eval_nsmul_nat,
      packedPoly_eval _ _ _ (split_row_histogram val hβ r t hr (Nat.le_of_lt_succ (Finset.mem_range.mp ht)) hp).1]
  · rw [pair_histogram_split]
    intro j
    simp only [pairPoly, Polynomial.finsetSum_coeff, coeff_nsmul_nat]
    apply Finset.sum_le_sum
    intro t ht
    exact Nat.mul_le_mul_left _
      (packedPoly_below _ _ _ _ (split_row_histogram val hβ r t hr (Nat.le_of_lt_succ (Finset.mem_range.mp ht)) hp).2 j)

theorem pairFirst_histogram {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (r : Nat) (hr : r≤20)
    (hp : ∀ u, u≤r → ∀ j, (coordinatePoly 64 u).coeff j ≤
      (univ.filter fun E : Fin u → Fin 64×β => coordinateCoverage val E=j).card) :
    pairFirst r<(2^1024)^2048 ∧
      ∀ j, j<2048 → digit (2^1024) (pairFirst r) j ≤
        (weightedHistogram (pairGood val) (pairBin val) (pairCoverage (r:=r) val)).coeff j := by
  classical
  have h := pair_polynomial val hβ r hr hp
  have hc (j : Nat) : (pairPoly r).coeff j<2^1024 := by
    apply histogram_lower_coeff_lt _ _ _ _ h.2 (2*(64*563)^2) _
    · intro a _
      exact pair_coverage_le val hβ a
    · rw [pair_history_card hβ]
      exact pair_mass_small r hr
  have hz (j : Nat) (hj : 2048≤j) : (pairPoly r).coeff j=0 := by
    simp only [pairPoly, Polynomial.finsetSum_coeff, coeff_nsmul_nat, packedPoly,
      polyOf_coeff, if_neg (by omega : ¬j<2048), Nat.mul_zero, Finset.sum_const_zero]
  rw [←h.1]
  refine ⟨polynomial_eval_lt _ _ _ (by positivity) (fun j _ => hc j) hz,?_⟩
  intro j hj
  rw [digit_polynomial_eval _ _ _ (by positivity) (fun i _ => hc i) hz j hj]
  exact h.2 j

#print axioms pair_histogram_split
#print axioms pairFirst_sum
#print axioms pairFirst_histogram
end ClaudeWCT.Numerics.SharedPathPair

namespace ClaudeWCT.Numerics.SharedFees
open Finset Polynomial ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
attribute [local irreducible] feeRuns feeEntries fees scale maxFee

theorem fees_bound_of_chunks (hsize : feeRuns.size = 1578)
    (hchunks : ∀ block : Nat, block < 25 → feeChunk block = true)
    (hidx : feeEntries.map Prod.fst = List.range 7210) (i : Nat) (hi : i < 7210) :
    (fees[i]?.getD (0,0)).1 ≤ maxFee ∧ (fees[i]?.getD (0,0)).2 ≤ scale :=  by
  have hv :=  fee_run_values hsize hchunks
  obtain ⟨e,he,_,_,hfee⟩ :=  fee_lookup_run (fun e he  => (hv e he).1) hidx i hi
  rw [hfee]
  exact (hv e he).2.2

theorem histogram_winsor_pair {α : Type} [Fintype α]
    (good : α → Prop) [DecidablePred good] (bin weight : α → Nat)
    (P : Nat[X]) (total : Nat) (κ : ℝ) (hκ : 0 ≤ κ)
    (hP : CoeffLE P (weightedHistogram good bin weight))
    (htotal : (∑ a, weight a) = total)
    (hsize : feeRuns.size = 1578)
    (hchunks : ∀ block : Nat, block < 25 → feeChunk block = true)
    (hidx : feeEntries.map Prod.fst = List.range 7210)
    (hinterval : ∀ a, good a →
      lowerValue (bin a) ≤ κ*(weight a : ℝ) ∧ κ*(weight a : ℝ) ≤ upperValue (bin a)) :
    (∑ a, (Real.exp (6*min (κ*(weight a : ℝ)) (6/5))-1))  ≤ 
      κ/(scale : ℝ)*(((∑ j ∈ range 7210, P.coeff j*(fees[j]?.getD (0,0)).1)+
        maxFee*(total-∑ j ∈ range 7210, P.coeff j) : Nat) : ℝ) ∧
    (∑ a, max 0 (κ*(weight a : ℝ)-6/5))  ≤ 
      κ/(scale : ℝ)*(((∑ j ∈ range 7210, P.coeff j*(fees[j]?.getD (0,0)).2)+
        scale*(total-∑ j ∈ range 7210, P.coeff j) : Nat) : ℝ) :=  by
  have hS : (0 : ℝ) < scale :=  by exact_mod_cast scale_pos
  have hnon (a : α) : 0 ≤ κ*(weight a : ℝ) :=  mul_nonneg hκ (Nat.cast_nonneg _)
  have hfee :=  fees_bound_of_chunks hsize hchunks hidx
  have hlocal (a : α) (ha : good a) (hb : bin a < 7210) := 
    fee_lookup_sound hsize hchunks hidx (bin a) hb (κ*(weight a : ℝ))
      (hnon a) (hinterval a ha).1 (hinterval a ha).2
  constructor
  · apply histogram_moment_bound 7210 total maxFee good bin weight P hP htotal
      (fun a  => Real.exp (6*min (κ*(weight a : ℝ)) (6/5))-1)
      (fun j  => (fees[j]?.getD (0,0)).1) (κ/scale) (div_nonneg hκ hS.le)
      (fun j hj  => (hfee j hj).1)
    · intro a
      convert global_fee_sound (κ*(weight a : ℝ)) (hnon a) using 1  <;> ring
    · intro a ha hb
      convert (hlocal a ha hb).1 using 1  <;> ring
  · apply histogram_moment_bound 7210 total scale good bin weight P hP htotal
      (fun a  => max 0 (κ*(weight a : ℝ)-6/5))
      (fun j  => (fees[j]?.getD (0,0)).2) (κ/scale) (div_nonneg hκ hS.le)
      (fun j hj  => (hfee j hj).2)
    · intro a
      have h : max 0 (κ*(weight a : ℝ)-6/5) ≤ κ*(weight a : ℝ) := 
        max_le (hnon a) (by linarith)
      convert h using 1
      field_simp
    · intro a ha hb
      convert (hlocal a ha hb).2 using 1  <;> ring

#print axioms histogram_winsor_pair
end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.SharedPathForest
open Finset Polynomial ClaudeWCT.Numerics.N600
open ClaudeWCT.Numerics.SharedCoverage ClaudeWCT.Numerics.SharedMoments
open ClaudeWCT.Numerics.SharedDigitBlock ClaudeWCT.Numerics.SharedPathList
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false

noncomputable def encodedForestPoly (p q : Nat) : Nat[X] :=
  (packedPoly (2^1024) 2048 p)^4 * packedPoly (2^1024) 1024 q

theorem encodedForest_encoding (p q : Nat)
    (hp : p < (2^1024)^2048) (hq : q < (2^1024)^1024) :
    (SharedPathPacked.spread 11 p)^4*SharedPathPacked.spread 10 q =
      (encodedForestPoly p q).eval (2^4096) :=
  SharedPathPacked.forest_packed_polynomial p q hp hq

theorem encodedForest_histogram {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (r p q : Nat)
    (gp : PairHistory β r → Prop) [DecidablePred gp] (bp : PairHistory β r → Nat)
    (gq : (Fin r → Fin 128×β) → Prop) [DecidablePred gq]
    (bq : (Fin r → Fin 128×β) → Nat)
    (hp : ∀ j, j < 2048 → digit (2^1024) p j ≤
      (weightedHistogram gp bp (pairCoverage val)).coeff j)
    (hq : ∀ j, j < 1024 → digit (2^1024) q j ≤
      (weightedHistogram gq bq (coordinateCoverage val)).coeff j) :
    CoeffLE (encodedForestPoly p q)
      (weightedHistogram (fun h : ForestHistory β r => (∀ i, gp (h.1 i)) ∧ gq h.2)
        (fun h => (∑ i, bp (h.1 i))+bq h.2) (forestCoverage val)) := by
  exact forest_histogram_lower val r gp bp gq bq _ _
    (packedPoly_below _ _ _ _ hp) (packedPoly_below _ _ _ _ hq)

theorem encodedForest_coeff_small {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β = 563) (r p q : Nat) (hr : r ≤ 20)
    (gp : PairHistory β r → Prop) [DecidablePred gp] (bp : PairHistory β r → Nat)
    (gq : (Fin r → Fin 128×β) → Prop) [DecidablePred gq]
    (bq : (Fin r → Fin 128×β) → Nat)
    (hp : ∀ j, j < 2048 → digit (2^1024) p j ≤
      (weightedHistogram gp bp (pairCoverage val)).coeff j)
    (hq : ∀ j, j < 1024 → digit (2^1024) q j ≤
      (weightedHistogram gq bq (coordinateCoverage val)).coeff j)
    (j : Nat) : (encodedForestPoly p q).coeff j < 2^4096 := by
  have h := encodedForest_histogram val r p q gp bp gq bq hp hq
  refine histogram_lower_coeff_lt _ _ _ _ h alphabetSize (2^4096)
    (fun h _ => forest_coverage_le val hβ h) ?_ j
  rw [forest_history_card hβ r]
  exact forest_mass_small r hr

theorem forest_interval {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (r : Nat)
    (gp : PairHistory β r → Prop) (bp : PairHistory β r → Nat)
    (gq : (Fin r → Fin 128×β) → Prop) (bq : (Fin r → Fin 128×β) → Nat)
    (hp : ∀ h, gp h → RoundedInterval 3 (bp h) (pairCoverage val h : ℝ))
    (hq : ∀ h, gq h → RoundedInterval 1 (bq h) (coordinateCoverage val h : ℝ))
    (h : ForestHistory β r) (hg : (∀ i, gp (h.1 i)) ∧ gq h.2) :
    RoundedInterval 13 ((∑ i, bp (h.1 i))+bq h.2) (forestCoverage val h : ℝ) := by
  have hf := RoundedInterval.forest (fun i => bp (h.1 i))
    (fun i => (pairCoverage val (h.1 i) : ℝ)) (bq h.2) (coordinateCoverage val h.2 : ℝ)
    (fun i => hp _ (hg.1 i)) (hq _ hg.2)
  simpa only [forestCoverage, Nat.cast_mul, Nat.cast_prod] using hf

#print axioms encodedForest_histogram
#print axioms encodedForest_coeff_small
#print axioms forest_interval
end ClaudeWCT.Numerics.SharedPathForest

namespace ClaudeWCT.Numerics.SharedFees
open Finset Polynomial ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open scoped BigOperators Polynomial ENNReal
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
attribute [local irreducible] feeRuns feeEntries fees scale maxFee

theorem ofReal_sum_nat_bound {α : Type} [Fintype α]
    (f : α → ℝ) (κ : ℝ) (A B : Nat) (hκ : 0 ≤ κ) (hB : 0 < B)
    (hf : ∀ a, 0 ≤ f a) (h : (∑ a, f a) ≤ κ/(B : ℝ)*(A : ℝ)) :
    (∑ a, ENNReal.ofReal (f a)) ≤ ENNReal.ofReal κ/(B : ENNReal)*(A : ENNReal) := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hf a)]
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  calc
    _ ≤ ENNReal.ofReal (κ/(B : ℝ)*(A : ℝ)) := ENNReal.ofReal_le_ofReal h
    _ = _ := by
      rw [ENNReal.ofReal_mul (div_nonneg hκ hBR.le), ENNReal.ofReal_div_of_pos hBR,
        ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]

theorem histogram_winsor_pair_ennreal {α : Type} [Fintype α]
    (good : α → Prop) [DecidablePred good] (bin weight : α → Nat)
    (P : Nat[X]) (total : Nat) (κ : ℝ) (hκ : 0 ≤ κ)
    (hP : CoeffLE P (weightedHistogram good bin weight))
    (htotal : (∑ a, weight a) = total)
    (hsize : feeRuns.size = 1578)
    (hchunks : ∀ block : Nat, block < 25 → feeChunk block = true)
    (hidx : feeEntries.map Prod.fst = List.range 7210)
    (hinterval : ∀ a, good a →
      lowerValue (bin a) ≤ κ*(weight a : ℝ) ∧ κ*(weight a : ℝ) ≤ upperValue (bin a)) :
    (∑ a, ENNReal.ofReal (Real.exp (6*min (κ*(weight a : ℝ)) (6/5))-1)) ≤
      ENNReal.ofReal κ/(scale : ENNReal)*
        (((∑ j ∈ range 7210, P.coeff j*(fees[j]?.getD (0,0)).1)+
          maxFee*(total-∑ j ∈ range 7210, P.coeff j) : Nat) : ENNReal) ∧
    (∑ a, ENNReal.ofReal (max 0 (κ*(weight a : ℝ)-6/5))) ≤
      ENNReal.ofReal κ/(scale : ENNReal)*
        (((∑ j ∈ range 7210, P.coeff j*(fees[j]?.getD (0,0)).2)+
          scale*(total-∑ j ∈ range 7210, P.coeff j) : Nat) : ENNReal) := by
  have h := histogram_winsor_pair good bin weight P total κ hκ hP htotal hsize hchunks hidx hinterval
  constructor
  · apply ofReal_sum_nat_bound _ κ _ scale hκ scale_pos _ h.1
    intro a
    apply sub_nonneg.mpr
    exact Real.one_le_exp (mul_nonneg (by norm_num)
      (le_min (mul_nonneg hκ (Nat.cast_nonneg _)) (by norm_num)))
  · exact ofReal_sum_nat_bound _ κ _ scale hκ scale_pos (fun _ => le_max_left _ _) h.2

theorem capped_payoff_of_coverage_bound (x κ D : ℝ)
    (hx : 0 ≤ x) (hbound : x ≤ κ*D) :
    Real.exp (6*min x (6/5))-1 ≤ (maxFee : ℝ)*κ*D/scale ∧
    max 0 (x-6/5) ≤ κ*D := by
  have hS : (0 : ℝ) < scale := by exact_mod_cast scale_pos
  constructor
  · calc
      _ ≤ x*((maxFee : ℝ)/scale) := global_fee_sound x hx
      _ ≤ κ*D*((maxFee : ℝ)/scale) := mul_le_mul_of_nonneg_right hbound
        (div_nonneg (Nat.cast_nonneg _) hS.le)
      _ = _ := by ring
  · exact (max_le hx (by linarith)).trans hbound

#print axioms histogram_winsor_pair_ennreal
#print axioms capped_payoff_of_coverage_bound
end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.SharedPathForest
open Finset Polynomial ClaudeWCT.Numerics.N600
open ClaudeWCT.Numerics.SharedCoverage ClaudeWCT.Numerics.SharedMoments
open ClaudeWCT.Numerics.SharedDigitBlock ClaudeWCT.Numerics.SharedPathList
open ClaudeWCT.Numerics.SharedPathCoordinate ClaudeWCT.Numerics.SharedPathPair
open scoped BigOperators Polynomial
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
attribute [local irreducible] binnedPoly coordinatePoly coordinate SharedPathPacked.product SharedPathPacked.addFirst

noncomputable def actualGood {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    {r : Nat} (h : ForestHistory β r) : Prop :=
  (∀ i, pairGood val (h.1 i)) ∧ coordinateGood val h.2
noncomputable def actualBin {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    {r : Nat} (h : ForestHistory β r) : Nat :=
  (∑ i, pairBin val (h.1 i))+coordinateBin val h.2
noncomputable def actualPoly (r : Nat) : Nat[X] :=
  encodedForestPoly (SharedPathPacked.pairFirst r) (coordinate 128 r).2

theorem coordinate_first_digit {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (K : Nat) (hK : K∈[64,128]) (r : Fin 21)
    (hp : ∀ j, (coordinatePoly K r.val).coeff j ≤
      (univ.filter fun E : Fin r.val → Fin K×β => coordinateCoverage val E=j).card) (j : Nat) :
    digit (2^1024) (coordinate K r.val).2 j = (firstPoly K r.val).coeff j := by
  rw [coordinate_polynomial val hβ K hK r hp]
  exact ClaudeWCT.Numerics.eval_div_pow_mod (by positivity) j _ (fun i => by
    have h1 := (coordinate_mass val hβ K hK r hp).2
    have h2 := polynomial_coeff_le_mass (firstPoly K r.val) i
    have h3 : 2^384<2^1024 := by decide +kernel
    exact h2.trans_lt (h1.trans h3))

theorem coordinate_first_histogram {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (K : Nat) (hK : K∈[64,128]) (r : Fin 21)
    (hp : ∀ j, (coordinatePoly K r.val).coeff j ≤
      (univ.filter fun E : Fin r.val → Fin K×β => coordinateCoverage val E=j).card) :
    ∀ j, digit (2^1024) (coordinate K r.val).2 j ≤
      (weightedHistogram (coordinateGood val) (coordinateBin val) (coordinateCoverage (C:=Fin K) (r:=r.val) val)).coeff j := by
  intro j
  rw [coordinate_first_digit val hβ K hK r hp]
  exact (coordinate_histogram val hβ K hK r hp).2 j

theorem actual_encoding {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (r : Nat) (hr : r≤20)
    (hp : ∀ K, K∈[64,128] → ∀ u, u≤r → ∀ j, (coordinatePoly K u).coeff j ≤
      (univ.filter fun E : Fin u → Fin K×β => coordinateCoverage val E=j).card) :
    SharedPathPacked.forest r=(actualPoly r).eval (2^4096) := by
  exact encodedForest_encoding _ _ (pairFirst_histogram val hβ r hr (hp 64 (by simp))).1
    (coordinate_size val hβ 128 (by simp) ⟨r,by omega⟩ (hp 128 (by simp) r le_rfl)).2

theorem actual_histogram {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (r : Nat) (hr : r≤20)
    (hp : ∀ K, K∈[64,128] → ∀ u, u≤r → ∀ j, (coordinatePoly K u).coeff j ≤
      (univ.filter fun E : Fin u → Fin K×β => coordinateCoverage val E=j).card) :
    CoeffLE (actualPoly r) (weightedHistogram (actualGood val) (actualBin val) (forestCoverage (r:=r) val)) := by
  classical
  exact encodedForest_histogram val r _ _ (pairGood val) (pairBin val)
    (coordinateGood val) (coordinateBin val)
    (pairFirst_histogram val hβ r hr (hp 64 (by simp))).2
    (fun j _ => coordinate_first_histogram val hβ 128 (by simp) ⟨r,by omega⟩
      (hp 128 (by simp) r le_rfl) j)

theorem actual_coeff_small {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (r : Nat) (hr : r≤20)
    (hp : ∀ K, K∈[64,128] → ∀ u, u≤r → ∀ j, (coordinatePoly K u).coeff j ≤
      (univ.filter fun E : Fin u → Fin K×β => coordinateCoverage val E=j).card) (j : Nat) :
    (actualPoly r).coeff j<2^4096 := by
  classical
  exact encodedForest_coeff_small val hβ r _ _ hr (pairGood val) (pairBin val)
    (coordinateGood val) (coordinateBin val)
    (pairFirst_histogram val hβ r hr (hp 64 (by simp))).2
    (fun j _ => coordinate_first_histogram val hβ 128 (by simp) ⟨r,by omega⟩
      (hp 128 (by simp) r le_rfl) j) j

theorem actual_interval {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    {r : Nat} (hr : 0<r) (h : ForestHistory β r) (hg : actualGood val h) :
    RoundedInterval 13 (actualBin val h) (forestCoverage val h : ℝ) := by
  exact forest_interval val r (pairGood val) (pairBin val) (coordinateGood val) (coordinateBin val)
    (fun h hh => pair_interval val hr h hh) (fun h hh => coordinate_interval val hr h hh) h hg

#print axioms actual_encoding
#print axioms actual_histogram
#print axioms actual_coeff_small
#print axioms actual_interval
end ClaudeWCT.Numerics.SharedPathForest


namespace ClaudeWCT.Numerics.SharedFees
open Finset Polynomial ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open ClaudeWCT.Numerics.SharedMoments
open scoped BigOperators Polynomial ENNReal
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
attribute [local irreducible] fees scale maxFee

theorem rowDots_polynomial (r : Nat) (hr : r ≤ 20) (P : Nat[X])
    (henc : SharedPathPacked.forest r = P.eval (2^4096))
    (hc : ∀ j, P.coeff j < 2^4096) :
    rowDots r =
      ((∑ j ∈ range 7210, P.coeff j*(fees[j]?.getD (0,0)).1)+
        maxFee*(forestMoment r-∑ j ∈ range 7210, P.coeff j),
       (∑ j ∈ range 7210, P.coeff j*(fees[j]?.getD (0,0)).2)+
        scale*(forestMoment r-∑ j ∈ range 7210, P.coeff j)) := by
  rw [rowDots, if_pos hr, henc, paidTree_polynomial_range 10 fees.toList P hc]
  simp only [Array.length_toList, fee_count, Array.getElem?_toList]

theorem rowDots_winsor_pair_ennreal {α : Type} [Fintype α]
    (good : α → Prop) [DecidablePred good] (bin weight : α → Nat)
    (r : Nat) (hr : r ≤ 20) (P : Nat[X]) (κ : ℝ) (hκ : 0 ≤ κ)
    (henc : SharedPathPacked.forest r = P.eval (2^4096))
    (hc : ∀ j, P.coeff j < 2^4096)
    (hP : CoeffLE P (weightedHistogram good bin weight))
    (htotal : (∑ a, weight a) = forestMoment r)
    (hsize : feeRuns.size = 1578)
    (hchunks : ∀ block : Nat, block < 25 → feeChunk block = true)
    (hinterval : ∀ a, good a →
      lowerValue (bin a) ≤ κ*(weight a : ℝ) ∧ κ*(weight a : ℝ) ≤ upperValue (bin a)) :
    (∑ a, ENNReal.ofReal (Real.exp (6*min (κ*(weight a : ℝ)) (6/5))-1)) ≤
      ENNReal.ofReal κ/(scale : ENNReal)*((rowDots r).1 : ENNReal) ∧
    (∑ a, ENNReal.ofReal (max 0 (κ*(weight a : ℝ)-6/5))) ≤
      ENNReal.ofReal κ/(scale : ENNReal)*((rowDots r).2 : ENNReal) := by
  rw [rowDots_polynomial r hr P henc hc]
  exact histogram_winsor_pair_ennreal good bin weight P (forestMoment r) κ hκ
    hP htotal hsize hchunks fee_indices hinterval

#print axioms rowDots_polynomial
#print axioms rowDots_winsor_pair_ennreal
end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.SharedFees
open Finset
open scoped BigOperators ENNReal
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
attribute [local irreducible] scale maxFee

theorem finite_payoff_global {α : Type} [Fintype α]
    (weight : α → Nat) (total : Nat) (κ : ℝ) (hκ : 0 ≤ κ)
    (htotal : (∑ a, weight a) = total) :
    (∑ a, ENNReal.ofReal (Real.exp (6*min (κ*(weight a : ℝ)) (6/5))-1)) ≤
      ENNReal.ofReal κ/(scale : ENNReal)*((maxFee*total : Nat) : ENNReal) ∧
    (∑ a, ENNReal.ofReal (max 0 (κ*(weight a : ℝ)-6/5))) ≤
      ENNReal.ofReal κ/(scale : ENNReal)*((scale*total : Nat) : ENNReal) := by
  have hS : (0 : ℝ) < scale := by exact_mod_cast scale_pos
  have htotalR : (∑ a, (weight a : ℝ)) = (total : ℝ) := by exact_mod_cast htotal
  have hx (a : α) : 0 ≤ κ*(weight a : ℝ) := mul_nonneg hκ (Nat.cast_nonneg _)
  constructor
  · apply ofReal_sum_nat_bound _ κ _ scale hκ scale_pos
      (fun a => sub_nonneg.mpr (Real.one_le_exp
        (mul_nonneg (by norm_num) (le_min (hx a) (by norm_num)))))
    calc
      _ ≤ ∑ a, κ*(weight a : ℝ)*((maxFee : ℝ)/scale) :=
        Finset.sum_le_sum (fun a _ => global_fee_sound _ (hx a))
      _ = κ/(scale : ℝ)*((maxFee*total : Nat) : ℝ) := by
        rw [← Finset.sum_mul, ← Finset.mul_sum, htotalR, Nat.cast_mul]
        ring
  · apply ofReal_sum_nat_bound _ κ _ scale hκ scale_pos (fun _ => le_max_left _ _)
    calc
      _ ≤ ∑ a, κ*(weight a : ℝ) := Finset.sum_le_sum
        (fun a _ => max_le (hx a) (by linarith))
      _ = κ/(scale : ℝ)*((scale*total : Nat) : ℝ) := by
        rw [← Finset.mul_sum, htotalR, Nat.cast_mul]
        field_simp

#print axioms finite_payoff_global
end ClaudeWCT.Numerics.SharedFees


namespace ClaudeWCT.Numerics.SharedFees
open ClaudeWCT.Numerics.N600
open Finset Polynomial ClaudeWCT.Numerics.SharedCoverage ClaudeWCT.Numerics.SharedMoments
open ClaudeWCT.Numerics.SharedPathForest ClaudeWCT.Numerics.SharedPathList
open scoped BigOperators Polynomial ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false

theorem actual_forest_fee_row {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (r : Nat) (hr0 : 0<r) (hr : r≤20)
    (hp : ∀ K, K∈[64,128] → ∀ u, u≤r → ∀ j, (coordinatePoly K u).coeff j ≤
      (univ.filter fun E : Fin u → Fin K×β => coordinateCoverage val E=j).card)
    (htotal : (∑ h : ForestHistory β r, forestCoverage val h) = forestMoment r) :
    (∑ h : ForestHistory β r, ENNReal.ofReal
      (Real.exp (6*min ((734:ℝ)/2^66*(forestCoverage val h : ℝ)) (6/5))-1)) ≤
      ENNReal.ofReal ((734:ℝ)/2^66)/(scale:ENNReal)*((rowDots r).1:ENNReal) ∧
    (∑ h : ForestHistory β r, ENNReal.ofReal
      (max 0 ((734:ℝ)/2^66*(forestCoverage val h : ℝ)-6/5))) ≤
      ENNReal.ofReal ((734:ℝ)/2^66)/(scale:ENNReal)*((rowDots r).2:ENNReal) := by
  classical
  exact rowDots_winsor_pair_ennreal (actualGood val) (actualBin val) (forestCoverage val)
    r hr (actualPoly r) ((734:ℝ)/2^66) (by positivity)
    (actual_encoding val hβ r hr hp) (actual_coeff_small val hβ r hr hp)
    (actual_histogram val hβ r hr hp) htotal fee_runs_count all_chunks
    (fun h hh => SharedPathList.RoundedInterval.fee_bounds (actual_interval val hr0 h hh))

theorem actual_forest_fee_global {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (r : Nat)
    (htotal : (∑ h : ForestHistory β r, forestCoverage val h) = forestMoment r) :
    (∑ h : ForestHistory β r, ENNReal.ofReal
      (Real.exp (6*min ((734:ℝ)/2^66*(forestCoverage val h : ℝ)) (6/5))-1)) ≤
      ENNReal.ofReal ((734:ℝ)/2^66)/(scale:ENNReal)*((maxFee*forestMoment r:Nat):ENNReal) ∧
    (∑ h : ForestHistory β r, ENNReal.ofReal
      (max 0 ((734:ℝ)/2^66*(forestCoverage val h : ℝ)-6/5))) ≤
      ENNReal.ofReal ((734:ℝ)/2^66)/(scale:ENNReal)*((scale*forestMoment r:Nat):ENNReal) := by
  exact finite_payoff_global (forestCoverage val) (forestMoment r) ((734:ℝ)/2^66) (by positivity) htotal

#print axioms actual_forest_fee_row
#print axioms actual_forest_fee_global
end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedPathList (Cell coordinate)
open ClaudeWCT.Numerics.SharedCoverage (foldl_weighted_sum)
open ClaudeWCT.Numerics.Kernel (fact)
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false

def pairChunkWith (coord : Nat → Nat → Cell) (r start size : Nat) : Nat :=
  let branches := (List.range (r+1)).map fun t => product (coord 64 t)
  (List.range' start size).foldl (fun acc t =>
    let a := branches.getD t (0,0)
    let b := branches.getD (r-t) (0,0)
    let row := if t=0 then b.2 else if r-t=0 then a.2 else addFirst a b
    acc + fact r / (fact t * fact (r-t)) * row) 0

/-- `pairChunkWith` evaluated through `addFirstFast` (theorem `pairChunkWith_eq_fast`). -/
def pairChunkWithFast (coord : Nat → Nat → Cell) (r start size : Nat) : Nat :=
  let branches := (List.range (r+1)).map fun t => product (coord 64 t)
  (List.range' start size).foldl (fun acc t =>
    let a := branches.getD t (0,0)
    let b := branches.getD (r-t) (0,0)
    let row := if t=0 then b.2 else if r-t=0 then a.2 else addFirstFast a b
    acc + fact r / (fact t * fact (r-t)) * row) 0

theorem pairChunkWith_eq_fast : pairChunkWith = pairChunkWithFast := by
  funext coord r start size
  unfold pairChunkWith pairChunkWithFast
  rw [addFirst_eq_fast]

theorem pairChunkWith_append (coord : Nat → Nat → Cell) (r start a b : Nat) :
    pairChunkWith coord r start (a+b) =
      pairChunkWith coord r start a + pairChunkWith coord r (start+a) b := by
  unfold pairChunkWith
  rw [← List.range'_append_1]
  simp only [foldl_weighted_sum, List.map_append, List.sum_append, Nat.zero_add]

theorem pairFirst_eq_chunk (r : Nat) :
    pairFirst r = pairChunkWith coordinate r 0 (r+1) := by
  unfold pairFirst pairChunkWith
  rw [List.range_eq_range']

theorem pairFirst_eq_two_chunks (r m : Nat) (hm : m ≤ r+1) :
    pairFirst r = pairChunkWith coordinate r 0 m +
      pairChunkWith coordinate r m (r+1-m) := by
  rw [pairFirst_eq_chunk, ← Nat.add_sub_of_le hm, pairChunkWith_append]
  simp only [Nat.zero_add, Nat.add_sub_cancel_left]

theorem pairChunkWith_congr (coord other : Nat → Nat → Cell) (r start size : Nat)
    (h : ∀ t, t ≤ r → coord 64 t = other 64 t) :
    pairChunkWith coord r start size = pairChunkWith other r start size := by
  have he : (List.range (r+1)).map (fun t => product (coord 64 t)) =
      (List.range (r+1)).map (fun t => product (other 64 t)) := by
    apply List.map_congr_left
    intro t ht
    rw [h t (by have := List.mem_range.mp ht; omega)]
  unfold pairChunkWith
  rw [he]

#print axioms pairFirst_eq_two_chunks
#print axioms pairChunkWith_congr
end ClaudeWCT.Numerics.SharedPathPacked

namespace ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedPathList (Cell coordinate)
open ClaudeWCT.Numerics.SharedCoverage (foldl_weighted_sum)
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false

theorem pairChunkWith_eq_singletons (coord : Nat → Nat → Cell) (r start size : Nat) :
    pairChunkWith coord r start size =
      ((List.range' start size).map (fun t => pairChunkWith coord r t 1)).sum := by
  unfold pairChunkWith
  simp only [foldl_weighted_sum, Nat.zero_add, List.range'_succ, List.range'_zero,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]

theorem pairFirst_eq_singletons (coord : Nat → Nat → Cell) (r : Nat)
    (h : ∀ t, t ≤ r → coordinate 64 t = coord 64 t) :
    pairFirst r = ((List.range (r+1)).map (fun t => pairChunkWith coord r t 1)).sum := by
  rw [pairFirst_eq_chunk, pairChunkWith_congr coordinate coord r 0 (r+1) h,
    pairChunkWith_eq_singletons, ← List.range_eq_range']

#print axioms pairChunkWith_eq_singletons
#print axioms pairFirst_eq_singletons
end ClaudeWCT.Numerics.SharedPathPacked

namespace ClaudeWCT.Numerics.SharedFees
open Finset Polynomial
open scoped BigOperators Polynomial
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false

def packTree (bits : Nat) : Nat → Nat → (Nat → Nat) → Nat
  | 0, start, f => f start
  | h+1, start, f =>
    packTree bits h start f + (packTree bits h (start+2^h) f <<< (bits*2^h))

theorem packTree_sum (bits h start : Nat) (f : Nat → Nat) :
    packTree bits h start f =
      ∑ i ∈ range (2^h), f (start+i)*(2^bits)^i := by
  induction h generalizing start with
  | zero => simp [packTree]
  | succ h ih =>
    rw [packTree, ih, ih, Nat.shiftLeft_eq, pow_mul]
    rw [show 2^(h+1)=2^h+2^h by omega]
    rw [Finset.sum_range_add]
    congr 1
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [pow_add]
    rw [Nat.add_assoc]
    ring

theorem packTree_reversed (bits h n : Nat) (f : Nat → Nat) (hn : n≤2^h) :
    packTree bits h 0 (fun i => if i<n then f (n-1-i) else 0) =
      (reverseFeePoly n f).eval (2^bits) := by
  rw [packTree_sum]
  simp only [Nat.zero_add, ite_mul, zero_mul]
  rw [← Finset.sum_range_add_sum_Ico _ hn]
  have hz : (∑ i ∈ Ico n (2^h), if i<n then f (n-1-i)*(2^bits)^i else 0)=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [if_neg (by have := (Finset.mem_Ico.mp hi).1; omega)]
  rw [hz, Nat.add_zero]
  have hs : (∑ i ∈ range n, if i<n then f (n-1-i)*(2^bits)^i else 0)=
      ∑ i ∈ range n, f (n-1-i)*(2^bits)^i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [if_pos (Finset.mem_range.mp hi)]
  rw [hs, ← Finset.sum_range_reflect]
  simp only [reverseFeePoly, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  apply Finset.sum_congr rfl
  intro i hi
  have hi := Finset.mem_range.mp hi
  congr 2
  omega

#print axioms packTree_sum
#print axioms packTree_reversed
end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.SharedPathForest
open Finset Polynomial SharedCoverage SharedMoments Thinning N600 SharedPathList
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem actual_mass_le {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (r : Nat) (hr : r≤20)
    (hp : ∀ K, K∈[64,128] → ∀ u, u≤r → ∀ j, (coordinatePoly K u).coeff j ≤
      (univ.filter fun E : Fin u → Fin K×β => coordinateCoverage val E=j).card) :
    (actualPoly r).eval 1≤alphabetSize^r*alphabetSize := by
  classical
  have hm := histogram_lower_mass_le (actualGood val) (actualBin val)
    (forestCoverage (r:=r) val) (actualPoly r) (actual_histogram val hβ r hr hp)
    alphabetSize (fun h _ => forest_coverage_le val hβ h)
  rwa [forest_history_card hβ r] at hm

#print axioms actual_mass_le
end ClaudeWCT.Numerics.SharedPathForest

namespace ClaudeWCT.Numerics.SharedFees
open Finset Polynomial
open ClaudeWCT.Numerics.SharedMoments
open scoped BigOperators Polynomial
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false
attribute [local irreducible] fees maxFee scale

def feeValue (which i : Nat) : Nat :=
  if which=0 then 1 else if which=1 then (fees[i]?.getD (0,0)).1 else (fees[i]?.getD (0,0)).2

def packedFee (which : Nat) : Nat :=
  packTree 4096 13 0 (fun i => if i < 7210 then feeValue which (7209-i) else 0)

def packedDot (p q : Nat) : Nat := ((p*q) >>> (4096*7209)) % 2^4096

def convolutionDots (r p : Nat) : Nat × Nat :=
  let mass := packedDot p (packedFee 0)
  let lost := forestMoment r-mass
  (packedDot p (packedFee 1)+maxFee*lost, packedDot p (packedFee 2)+scale*lost)

theorem packedFee_model (which : Nat) :
    packedFee which = (reverseFeePoly 7210 (feeValue which)).eval (2^4096) := by
  exact packTree_reversed 4096 13 7210 (feeValue which) (by decide)

theorem convolution_shift (P : Nat[X]) (bits n : Nat) (f : Nat → Nat)
    (hmass : P.eval 1*(∑ i ∈ range n, f i) < 2^bits) :
    ((P.eval (2^bits)*(reverseFeePoly n f).eval (2^bits)) >>> (bits*(n-1))) % 2^bits =
      ∑ i ∈ range n, P.coeff i*f i := by
  rw [Nat.shiftRight_eq_div_pow, pow_mul]
  exact packed_convolution_dot P (2^bits) n f (by positivity) hmass

theorem packedDot_fee (P : Nat[X]) (p which : Nat)
    (hp : p=P.eval (2^4096))
    (hmass : P.eval 1*(∑ i ∈ range 7210, feeValue which i) < 2^4096) :
    packedDot p (packedFee which) = ∑ i ∈ range 7210, P.coeff i*feeValue which i := by
  unfold packedDot
  rw [packedFee_model, hp]
  exact convolution_shift P 4096 7210 (feeValue which) hmass

theorem convolutionDots_model (P : Nat[X]) (r p : Nat)
    (hp : p=P.eval (2^4096))
    (hmass : ∀ which, which ≤ 2 → P.eval 1*(∑ i ∈ range 7210, feeValue which i) < 2^4096) :
    convolutionDots r p =
      ((∑ i ∈ range 7210, P.coeff i*(fees[i]?.getD (0,0)).1)+
        maxFee*(forestMoment r-∑ i ∈ range 7210, P.coeff i),
       (∑ i ∈ range 7210, P.coeff i*(fees[i]?.getD (0,0)).2)+
        scale*(forestMoment r-∑ i ∈ range 7210, P.coeff i)) := by
  rw [convolutionDots, packedDot_fee P p 0 hp (hmass 0 (by decide)),
    packedDot_fee P p 1 hp (hmass 1 (by decide)),
    packedDot_fee P p 2 hp (hmass 2 (by decide))]
  simp only [feeValue, show ¬(1:Nat)=0 by decide, show ¬(2:Nat)=0 by decide,
    show ¬(2:Nat)=1 by decide, if_true, if_false, mul_one]

theorem feeValue_sum_small
    (hfee : ∀ i, i < 7210 → (fees[i]?.getD (0,0)).1 ≤ maxFee ∧ (fees[i]?.getD (0,0)).2 ≤ scale)
    (hmax : maxFee ≤ 2^140) (hscale : scale ≤ 2^140) (which : Nat) :
    (∑ i ∈ range 7210, feeValue which i) < 2^160 := by
  have hb (i : Nat) (hi : i∈range 7210) : feeValue which i ≤ 2^140 := by
    unfold feeValue
    split_ifs
    · exact Nat.one_le_pow _ _ (by decide)
    · exact (hfee i (Finset.mem_range.mp hi)).1.trans hmax
    · exact (hfee i (Finset.mem_range.mp hi)).2.trans hscale
  calc
    _  ≤  ∑ _i ∈ range 7210, (2:Nat)^140 := Finset.sum_le_sum hb
    _ = 7210*2^140 := by simp
    _  <  2^160 := by decide +kernel

theorem convolution_mass_small (P : Nat[X])
    (hmass : P.eval 1 ≤ 2^3072)
    (hfee : ∀ i, i < 7210 → (fees[i]?.getD (0,0)).1 ≤ maxFee ∧ (fees[i]?.getD (0,0)).2 ≤ scale)
    (hmax : maxFee ≤ 2^140) (hscale : scale ≤ 2^140) (which : Nat) :
    P.eval 1*(∑ i ∈ range 7210, feeValue which i) < 2^4096 := by
  have hf := feeValue_sum_small hfee hmax hscale which
  exact (Nat.mul_le_mul hmass hf.le).trans_lt (by decide +kernel)

#print axioms convolutionDots_model
#print axioms convolution_mass_small
end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.SharedFees
open Finset Polynomial
open ClaudeWCT.Numerics.SharedMoments
open scoped BigOperators Polynomial
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false

theorem maxFee_small : maxFee ≤ 2^140 := by decide +kernel
theorem scale_small : scale ≤ 2^140 := by decide +kernel

theorem forest_mass_3072 (r : Nat) (hr : r ≤ 20) :
    alphabetSize^r*alphabetSize ≤ 2^3072 := by
  have hp := Nat.pow_le_pow_right (n:=alphabetSize) (by decide : 0 < alphabetSize) hr
  exact (Nat.mul_le_mul_right _ hp).trans (by decide +kernel)

theorem rowDots_convolution (r : Nat) (hr : r ≤ 20) (P : Nat[X])
    (henc : SharedPathPacked.forest r = P.eval (2^4096))
    (hc : ∀ j, P.coeff j < 2^4096)
    (hmass : P.eval 1 ≤ 2^3072) :
    rowDots r = convolutionDots r (SharedPathPacked.forest r) := by
  have hfee := fees_bound_of_chunks fee_runs_count all_chunks fee_indices
  exact (rowDots_polynomial r hr P henc hc).trans
    (convolutionDots_model P r _ henc (fun w _ =>
      convolution_mass_small P hmass hfee maxFee_small scale_small w)).symm

#print axioms rowDots_convolution
end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.SharedFees
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false

theorem packTree_congr (bits h a b : Nat) (f g : Nat → Nat)
    (hfg : ∀ i, i < 2^h → f (a+i)=g (b+i)) :
    packTree bits h a f=packTree bits h b g := by
  induction h generalizing a b with
  | zero => simpa [packTree] using hfg 0 (by decide)
  | succ h ih =>
    have hp : 2^(h+1)=2^h+2^h := by omega
    simp only [packTree]
    apply congrArg₂ Nat.add
    · apply ih
      intro i hi
      exact hfg i (by rw [hp]; omega)
    · apply congrArg (fun n => n <<< (bits*2^h))
      apply ih
      intro i hi
      simpa only [Nat.add_assoc] using hfg (2^h+i) (by rw [hp]; omega)

def packList (bits : Nat) : Nat → List Nat → Nat
  | 0, xs => xs.headD 0
  | h+1, xs =>
    packList bits h (xs.take (2^h)) + (packList bits h (xs.drop (2^h)) <<< (bits*2^h))

theorem packList_eq_tree (bits h : Nat) (xs : List Nat) :
    packList bits h xs=packTree bits h 0 (fun i => xs[i]?.getD 0) := by
  induction h generalizing xs with
  | zero => cases xs <;> rfl
  | succ h ih =>
    rw [packList, ih, ih]
    conv_rhs => rw [packTree]
    apply congrArg₂ Nat.add
    · apply packTree_congr
      intro i hi
      simp only [Nat.zero_add, List.getElem?_take_of_lt hi]
    · apply congrArg (fun n => n <<< (bits*2^h))
      apply packTree_congr
      intro i hi
      simp only [Nat.zero_add, List.getElem?_drop]

#print axioms packTree_congr
#print axioms packList_eq_tree
end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.SharedFees
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false

def feeVector (which : Nat) : List Nat :=
  feeEntries.map (fun e => if which=0 then 1 else if which=1 then e.2.1 else e.2.2)

def packedFeeVector (which : Nat) : Nat :=
  packList 4096 13 (feeVector which).reverse

theorem feeVector_length (which : Nat) (hl : feeEntries.length=7210) :
    (feeVector which).length=7210 := by simpa [feeVector] using hl

theorem feeVector_get (which i : Nat) (hl : feeEntries.length=7210) (hi : i < 7210) :
    (feeVector which)[i]?.getD 0=feeValue which i := by
  have h : i < feeEntries.length := by omega
  simp only [feeVector, feeValue, fees, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_eq_getElem h, Option.map_some, Option.getD_some]

theorem packedFeeVector_eq (which : Nat) (hl : feeEntries.length=7210) :
    packedFeeVector which=packedFee which := by
  rw [packedFeeVector, packList_eq_tree, packedFee]
  apply packTree_congr
  intro i hi
  simp only [Nat.zero_add]
  by_cases h : i < 7210
  · rw [List.getElem?_reverse (by rw [feeVector_length which hl]; exact h),
      feeVector_length which hl, if_pos h]
    exact feeVector_get which (7209-i) hl (by omega)
  · have hh : (feeVector which).reverse.length ≤ i := by
      rw [List.length_reverse, feeVector_length which hl]
      omega
    rw [List.getElem?_eq_none hh, if_neg h]
    rfl


#print axioms packedFeeVector_eq
end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.SharedGeneratedFeeVector
open Lean Elab Command
open ClaudeWCT.Numerics.SharedFees
set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000
set_option Elab.async false

elab "fee_vector_numeral% " which:num : term =>
  return ClaudeWCT.Numerics.SharedGeneratedCoordinate.limbExpr (packedFeeVector which.getNat)

elab "certify_fee_vector " which:num cached:ident proof:ident : command => do
  elabCommand (← `(noncomputable def $cached : Nat := fee_vector_numeral% $which))
  elabCommand (← `(theorem $proof : packedFeeVector $which = $cached := by decide +kernel))

certify_fee_vector 0 MassFee mass_fee_checked
#print axioms mass_fee_checked
certify_fee_vector 1 MgfFee mgf_fee_checked
#print axioms mgf_fee_checked
certify_fee_vector 2 ResFee res_fee_checked
#print axioms res_fee_checked
end ClaudeWCT.Numerics.SharedGeneratedFeeVector

namespace ClaudeWCT.Numerics.SharedGeneratedFeeVector
open ClaudeWCT.Numerics.SharedFees
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false

theorem feeEntries_length : feeEntries.length=7210 := by
  have h := congrArg List.length fee_indices
  simpa only [List.length_map, List.length_range] using h

theorem packedFee_0_checked : packedFee 0=MassFee :=
  (packedFeeVector_eq 0 feeEntries_length).symm.trans mass_fee_checked
theorem packedFee_1_checked : packedFee 1=MgfFee :=
  (packedFeeVector_eq 1 feeEntries_length).symm.trans mgf_fee_checked
theorem packedFee_2_checked : packedFee 2=ResFee :=
  (packedFeeVector_eq 2 feeEntries_length).symm.trans res_fee_checked

#print axioms packedFee_0_checked
#print axioms packedFee_1_checked
#print axioms packedFee_2_checked
end ClaudeWCT.Numerics.SharedGeneratedFeeVector

namespace ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedPathList (Cell)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false

theorem pairFirst_eq_cached_sum (coord : Nat → Nat → Cell) (chunks : Nat → Nat)
    (r : Nat)
    (hc : ∀ t, t ≤ r → ClaudeWCT.Numerics.SharedPathList.coordinate 64 t = coord 64 t)
    (hp : ∀ t, t ≤ r → pairChunkWith coord r t 1 = chunks t) :
    pairFirst r = ((List.range (r+1)).map chunks).sum := by
  calc
    pairFirst r = ((List.range (r+1)).map (fun t => pairChunkWith coord r t 1)).sum :=
      pairFirst_eq_singletons coord r hc
    _ = _ := congrArg List.sum (List.map_congr_left (fun t ht => hp t (by
      have := List.mem_range.mp ht
      omega)))

#print axioms pairFirst_eq_cached_sum
end ClaudeWCT.Numerics.SharedPathPacked

namespace ClaudeWCT.Numerics.SharedGeneratedPair
open Lean Elab Command
open ClaudeWCT.Numerics.SharedGeneratedCoordinate
open ClaudeWCT.Numerics.SharedPathList (Cell coordinate)
open ClaudeWCT.Numerics.SharedPathPacked
set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000
set_option Elab.async false

noncomputable def cachedCoordinate (_ r : Nat) : Cell :=
  match r with
  | 0 => Coordinate_64_0
  | 1 => Coordinate_64_1
  | 2 => Coordinate_64_2
  | 3 => Coordinate_64_3
  | 4 => Coordinate_64_4
  | 5 => Coordinate_64_5
  | 6 => Coordinate_64_6
  | 7 => Coordinate_64_7
  | 8 => Coordinate_64_8
  | 9 => Coordinate_64_9
  | 10 => Coordinate_64_10
  | 11 => Coordinate_64_11
  | 12 => Coordinate_64_12
  | 13 => Coordinate_64_13
  | 14 => Coordinate_64_14
  | 15 => Coordinate_64_15
  | 16 => Coordinate_64_16
  | 17 => Coordinate_64_17
  | 18 => Coordinate_64_18
  | _ => (0,0)

theorem cachedCoordinate_correct (r : Nat) (hr : r ≤ 18) :
    ClaudeWCT.Numerics.SharedPathList.coordinate 64 r = cachedCoordinate 64 r := by
  interval_cases r
  · exact coordinate_64_0_checked
  · exact coordinate_64_1_checked
  · exact coordinate_64_2_checked
  · exact coordinate_64_3_checked
  · exact coordinate_64_4_checked
  · exact coordinate_64_5_checked
  · exact coordinate_64_6_checked
  · exact coordinate_64_7_checked
  · exact coordinate_64_8_checked
  · exact coordinate_64_9_checked
  · exact coordinate_64_10_checked
  · exact coordinate_64_11_checked
  · exact coordinate_64_12_checked
  · exact coordinate_64_13_checked
  · exact coordinate_64_14_checked
  · exact coordinate_64_15_checked
  · exact coordinate_64_16_checked
  · exact coordinate_64_17_checked
  · exact coordinate_64_18_checked

/- The elaborator only proposes a numeral. The following theorem checks the
entire arithmetic expression in the kernel, independently of that proposal. -/
elab "pair_chunk_numeral% " r:num start:num size:num : term => do
  let mut coordinates : Array Cell := #[]
  for i in [:19] do
    let info ← getConstInfo ((s!"ClaudeWCT.Numerics.SharedGeneratedCoordinate.Coordinate_64_{i}").toName)
    let args := info.value!.getAppArgs
    match limbValue? args[2]!, limbValue? args[3]! with
    | some x, some y => coordinates := coordinates.push (x,y)
    | _, _ => throwError "coordinate cache {i} is not a pair of Nat literals"
  let value := pairChunkWithFast (fun _ n => coordinates[n]?.getD (0,0))
    r.getNat start.getNat size.getNat
  return limbExpr value

elab "certify_pair_chunk " r:num start:num size:num cached:ident proof:ident : command => do
  elabCommand (← `(noncomputable def $cached : Nat := pair_chunk_numeral% $r $start $size))
  elabCommand (← `(theorem $proof :
    pairChunkWith cachedCoordinate $r $start $size = $cached := by
      rw [pairChunkWith_eq_fast]; decide +kernel))

elab "pair_sum_numeral% " r:num : term => do
  let mut total := 0
  for i in [:r.getNat+1] do
    let info ← getConstInfo ((← getCurrNamespace) ++ Name.mkSimple s!"Pair_{r.getNat}_{i}")
    match limbValue? info.value! with
    | some n => total := total+n
    | none => throwError "pair chunk {i} is not a Nat literal"
  return limbExpr total

end ClaudeWCT.Numerics.SharedGeneratedPair

namespace ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedPathPacked

certify_pair_chunk 5 0 1 Pair_5_0 pair_5_0_checked
#print axioms pair_5_0_checked
certify_pair_chunk 5 1 1 Pair_5_1 pair_5_1_checked
#print axioms pair_5_1_checked
certify_pair_chunk 5 2 1 Pair_5_2 pair_5_2_checked
#print axioms pair_5_2_checked
certify_pair_chunk 5 3 1 Pair_5_3 pair_5_3_checked
#print axioms pair_5_3_checked
certify_pair_chunk 5 4 1 Pair_5_4 pair_5_4_checked
#print axioms pair_5_4_checked
certify_pair_chunk 5 5 1 Pair_5_5 pair_5_5_checked
#print axioms pair_5_5_checked

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
#print axioms pair_5_checked

certify_pair_chunk 6 0 1 Pair_6_0 pair_6_0_checked
#print axioms pair_6_0_checked
certify_pair_chunk 6 1 1 Pair_6_1 pair_6_1_checked
#print axioms pair_6_1_checked
certify_pair_chunk 6 2 1 Pair_6_2 pair_6_2_checked
#print axioms pair_6_2_checked
certify_pair_chunk 6 3 1 Pair_6_3 pair_6_3_checked
#print axioms pair_6_3_checked
certify_pair_chunk 6 4 1 Pair_6_4 pair_6_4_checked
#print axioms pair_6_4_checked
certify_pair_chunk 6 5 1 Pair_6_5 pair_6_5_checked
#print axioms pair_6_5_checked
certify_pair_chunk 6 6 1 Pair_6_6 pair_6_6_checked
#print axioms pair_6_6_checked

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
#print axioms pair_6_checked

certify_pair_chunk 7 0 1 Pair_7_0 pair_7_0_checked
#print axioms pair_7_0_checked
certify_pair_chunk 7 1 1 Pair_7_1 pair_7_1_checked
#print axioms pair_7_1_checked
certify_pair_chunk 7 2 1 Pair_7_2 pair_7_2_checked
#print axioms pair_7_2_checked
certify_pair_chunk 7 3 1 Pair_7_3 pair_7_3_checked
#print axioms pair_7_3_checked
certify_pair_chunk 7 4 1 Pair_7_4 pair_7_4_checked
#print axioms pair_7_4_checked
certify_pair_chunk 7 5 1 Pair_7_5 pair_7_5_checked
#print axioms pair_7_5_checked
certify_pair_chunk 7 6 1 Pair_7_6 pair_7_6_checked
#print axioms pair_7_6_checked
certify_pair_chunk 7 7 1 Pair_7_7 pair_7_7_checked
#print axioms pair_7_7_checked

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
#print axioms pair_7_checked

certify_pair_chunk 8 0 1 Pair_8_0 pair_8_0_checked
#print axioms pair_8_0_checked
certify_pair_chunk 8 1 1 Pair_8_1 pair_8_1_checked
#print axioms pair_8_1_checked
certify_pair_chunk 8 2 1 Pair_8_2 pair_8_2_checked
#print axioms pair_8_2_checked
certify_pair_chunk 8 3 1 Pair_8_3 pair_8_3_checked
#print axioms pair_8_3_checked
certify_pair_chunk 8 4 1 Pair_8_4 pair_8_4_checked
#print axioms pair_8_4_checked
certify_pair_chunk 8 5 1 Pair_8_5 pair_8_5_checked
#print axioms pair_8_5_checked
certify_pair_chunk 8 6 1 Pair_8_6 pair_8_6_checked
#print axioms pair_8_6_checked
certify_pair_chunk 8 7 1 Pair_8_7 pair_8_7_checked
#print axioms pair_8_7_checked
certify_pair_chunk 8 8 1 Pair_8_8 pair_8_8_checked
#print axioms pair_8_8_checked

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
#print axioms pair_8_checked

certify_pair_chunk 9 0 1 Pair_9_0 pair_9_0_checked
#print axioms pair_9_0_checked
certify_pair_chunk 9 1 1 Pair_9_1 pair_9_1_checked
#print axioms pair_9_1_checked
certify_pair_chunk 9 2 1 Pair_9_2 pair_9_2_checked
#print axioms pair_9_2_checked
certify_pair_chunk 9 3 1 Pair_9_3 pair_9_3_checked
#print axioms pair_9_3_checked
certify_pair_chunk 9 4 1 Pair_9_4 pair_9_4_checked
#print axioms pair_9_4_checked
certify_pair_chunk 9 5 1 Pair_9_5 pair_9_5_checked
#print axioms pair_9_5_checked
certify_pair_chunk 9 6 1 Pair_9_6 pair_9_6_checked
#print axioms pair_9_6_checked
certify_pair_chunk 9 7 1 Pair_9_7 pair_9_7_checked
#print axioms pair_9_7_checked
certify_pair_chunk 9 8 1 Pair_9_8 pair_9_8_checked
#print axioms pair_9_8_checked
certify_pair_chunk 9 9 1 Pair_9_9 pair_9_9_checked
#print axioms pair_9_9_checked

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
#print axioms pair_9_checked

certify_pair_chunk 10 0 1 Pair_10_0 pair_10_0_checked
#print axioms pair_10_0_checked
certify_pair_chunk 10 1 1 Pair_10_1 pair_10_1_checked
#print axioms pair_10_1_checked
certify_pair_chunk 10 2 1 Pair_10_2 pair_10_2_checked
#print axioms pair_10_2_checked
certify_pair_chunk 10 3 1 Pair_10_3 pair_10_3_checked
#print axioms pair_10_3_checked
certify_pair_chunk 10 4 1 Pair_10_4 pair_10_4_checked
#print axioms pair_10_4_checked
certify_pair_chunk 10 5 1 Pair_10_5 pair_10_5_checked
#print axioms pair_10_5_checked
certify_pair_chunk 10 6 1 Pair_10_6 pair_10_6_checked
#print axioms pair_10_6_checked
certify_pair_chunk 10 7 1 Pair_10_7 pair_10_7_checked
#print axioms pair_10_7_checked
certify_pair_chunk 10 8 1 Pair_10_8 pair_10_8_checked
#print axioms pair_10_8_checked
certify_pair_chunk 10 9 1 Pair_10_9 pair_10_9_checked
#print axioms pair_10_9_checked
certify_pair_chunk 10 10 1 Pair_10_10 pair_10_10_checked
#print axioms pair_10_10_checked

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
#print axioms pair_10_checked

certify_pair_chunk 11 0 1 Pair_11_0 pair_11_0_checked
#print axioms pair_11_0_checked
certify_pair_chunk 11 1 1 Pair_11_1 pair_11_1_checked
#print axioms pair_11_1_checked
certify_pair_chunk 11 2 1 Pair_11_2 pair_11_2_checked
#print axioms pair_11_2_checked
certify_pair_chunk 11 3 1 Pair_11_3 pair_11_3_checked
#print axioms pair_11_3_checked
certify_pair_chunk 11 4 1 Pair_11_4 pair_11_4_checked
#print axioms pair_11_4_checked
certify_pair_chunk 11 5 1 Pair_11_5 pair_11_5_checked
#print axioms pair_11_5_checked
certify_pair_chunk 11 6 1 Pair_11_6 pair_11_6_checked
#print axioms pair_11_6_checked
certify_pair_chunk 11 7 1 Pair_11_7 pair_11_7_checked
#print axioms pair_11_7_checked
certify_pair_chunk 11 8 1 Pair_11_8 pair_11_8_checked
#print axioms pair_11_8_checked
certify_pair_chunk 11 9 1 Pair_11_9 pair_11_9_checked
#print axioms pair_11_9_checked
certify_pair_chunk 11 10 1 Pair_11_10 pair_11_10_checked
#print axioms pair_11_10_checked
certify_pair_chunk 11 11 1 Pair_11_11 pair_11_11_checked
#print axioms pair_11_11_checked

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
#print axioms pair_11_checked

end ClaudeWCT.Numerics.SharedGeneratedPair

namespace ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedPathPacked
certify_pair_chunk 12 0 1 Pair_12_0 pair_12_0_checked
#print axioms pair_12_0_checked
certify_pair_chunk 12 1 1 Pair_12_1 pair_12_1_checked
#print axioms pair_12_1_checked
certify_pair_chunk 12 2 1 Pair_12_2 pair_12_2_checked
#print axioms pair_12_2_checked
certify_pair_chunk 12 3 1 Pair_12_3 pair_12_3_checked
#print axioms pair_12_3_checked
certify_pair_chunk 12 4 1 Pair_12_4 pair_12_4_checked
#print axioms pair_12_4_checked
certify_pair_chunk 12 5 1 Pair_12_5 pair_12_5_checked
#print axioms pair_12_5_checked
certify_pair_chunk 12 6 1 Pair_12_6 pair_12_6_checked
#print axioms pair_12_6_checked
certify_pair_chunk 12 7 1 Pair_12_7 pair_12_7_checked
#print axioms pair_12_7_checked
certify_pair_chunk 12 8 1 Pair_12_8 pair_12_8_checked
#print axioms pair_12_8_checked
certify_pair_chunk 12 9 1 Pair_12_9 pair_12_9_checked
#print axioms pair_12_9_checked
certify_pair_chunk 12 10 1 Pair_12_10 pair_12_10_checked
#print axioms pair_12_10_checked
certify_pair_chunk 12 11 1 Pair_12_11 pair_12_11_checked
#print axioms pair_12_11_checked
certify_pair_chunk 12 12 1 Pair_12_12 pair_12_12_checked
#print axioms pair_12_12_checked

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
#print axioms pair_12_checked


end ClaudeWCT.Numerics.SharedGeneratedPair

namespace ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedPathList (Cell)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false

theorem forest_eq_of_inputs (r p : Nat) (q : Cell)
    (hp : pairFirst r=p) (hq : ClaudeWCT.Numerics.SharedPathList.coordinate 128 r=q) :
    forest r=(spread 11 p)^4*spread 10 q.2 :=
  congrArg₂ (fun (x : Nat) (y : Cell) => (spread 11 x)^4*spread 10 y.2) hp hq

#print axioms forest_eq_of_inputs
end ClaudeWCT.Numerics.SharedPathPacked

namespace ClaudeWCT.Numerics.SharedFees
open ClaudeWCT.Numerics.SharedMoments
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false

theorem convolutionDots_eq_of_fees (r p mass mgf res : Nat)
    (h0 : packedFee 0=mass) (h1 : packedFee 1=mgf) (h2 : packedFee 2=res) :
    convolutionDots r p =
      (packedDot p mgf + maxFee*(forestMoment r-packedDot p mass),
       packedDot p res + scale*(forestMoment r-packedDot p mass)) := by
  subst mass
  subst mgf
  subst res
  rfl

#print axioms convolutionDots_eq_of_fees
end ClaudeWCT.Numerics.SharedFees

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

elab "forest_numeral% " r:num : term => do
  let pInfo ← getConstInfo ((s!"ClaudeWCT.Numerics.SharedGeneratedPair.Pair_{r.getNat}").toName)
  let qInfo ← getConstInfo ((s!"ClaudeWCT.Numerics.SharedGeneratedCoordinate.Coordinate_128_{r.getNat}").toName)
  match limbValue? pInfo.value!, limbValue? qInfo.value!.getAppArgs[3]! with
  | some p, some q => return limbExpr ((spread 11 p)^4 * spread 10 q)
  | _, _ => throwError "forest inputs are not Nat literals"

noncomputable def Forest_5 : Nat := forest_numeral% 5

theorem forest_5_checked : forest 5=Forest_5 := by
  exact (forest_eq_of_inputs 5 Pair_5 Coordinate_128_5
    pair_5_checked coordinate_128_5_checked).trans (by rw [spread_eq_fast]; decide +kernel)
#print axioms forest_5_checked

theorem convolution_5_checked : convolutionDots 5 (forest 5)=certifiedPayoff 5 := by
  have hf := congrArg (convolutionDots 5) forest_5_checked
  exact hf.trans ((convolutionDots_eq_of_fees 5 Forest_5 MassFee MgfFee ResFee
    packedFee_0_checked packedFee_1_checked packedFee_2_checked).trans (by decide +kernel))
#print axioms convolution_5_checked


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
#print axioms forest_6_checked

theorem convolution_6_checked : convolutionDots 6 (forest 6)=certifiedPayoff 6 := by
  have hf := congrArg (convolutionDots 6) forest_6_checked
  exact hf.trans ((convolutionDots_eq_of_fees 6 Forest_6 MassFee MgfFee ResFee
    packedFee_0_checked packedFee_1_checked packedFee_2_checked).trans (by decide +kernel))
#print axioms convolution_6_checked

noncomputable def Forest_7 : Nat := forest_numeral% 7

theorem forest_7_checked : forest 7=Forest_7 := by
  exact (forest_eq_of_inputs 7 Pair_7 Coordinate_128_7
    pair_7_checked coordinate_128_7_checked).trans (by rw [spread_eq_fast]; decide +kernel)
#print axioms forest_7_checked

theorem convolution_7_checked : convolutionDots 7 (forest 7)=certifiedPayoff 7 := by
  have hf := congrArg (convolutionDots 7) forest_7_checked
  exact hf.trans ((convolutionDots_eq_of_fees 7 Forest_7 MassFee MgfFee ResFee
    packedFee_0_checked packedFee_1_checked packedFee_2_checked).trans (by decide +kernel))
#print axioms convolution_7_checked

noncomputable def Forest_8 : Nat := forest_numeral% 8

theorem forest_8_checked : forest 8=Forest_8 := by
  exact (forest_eq_of_inputs 8 Pair_8 Coordinate_128_8
    pair_8_checked coordinate_128_8_checked).trans (by rw [spread_eq_fast]; decide +kernel)
#print axioms forest_8_checked

theorem convolution_8_checked : convolutionDots 8 (forest 8)=certifiedPayoff 8 := by
  have hf := congrArg (convolutionDots 8) forest_8_checked
  exact hf.trans ((convolutionDots_eq_of_fees 8 Forest_8 MassFee MgfFee ResFee
    packedFee_0_checked packedFee_1_checked packedFee_2_checked).trans (by decide +kernel))
#print axioms convolution_8_checked

noncomputable def Forest_9 : Nat := forest_numeral% 9

theorem forest_9_checked : forest 9=Forest_9 := by
  exact (forest_eq_of_inputs 9 Pair_9 Coordinate_128_9
    pair_9_checked coordinate_128_9_checked).trans (by rw [spread_eq_fast]; decide +kernel)
#print axioms forest_9_checked

theorem convolution_9_checked : convolutionDots 9 (forest 9)=certifiedPayoff 9 := by
  have hf := congrArg (convolutionDots 9) forest_9_checked
  exact hf.trans ((convolutionDots_eq_of_fees 9 Forest_9 MassFee MgfFee ResFee
    packedFee_0_checked packedFee_1_checked packedFee_2_checked).trans (by decide +kernel))
#print axioms convolution_9_checked


end ClaudeWCT.Numerics.SharedGeneratedForest

namespace ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedPathPacked
certify_pair_chunk 13 0 1 Pair_13_0 pair_13_0_checked
#print axioms pair_13_0_checked
certify_pair_chunk 13 1 1 Pair_13_1 pair_13_1_checked
#print axioms pair_13_1_checked
certify_pair_chunk 13 2 1 Pair_13_2 pair_13_2_checked
#print axioms pair_13_2_checked
certify_pair_chunk 13 3 1 Pair_13_3 pair_13_3_checked
#print axioms pair_13_3_checked
certify_pair_chunk 13 4 1 Pair_13_4 pair_13_4_checked
#print axioms pair_13_4_checked
certify_pair_chunk 13 5 1 Pair_13_5 pair_13_5_checked
#print axioms pair_13_5_checked
certify_pair_chunk 13 6 1 Pair_13_6 pair_13_6_checked
#print axioms pair_13_6_checked
certify_pair_chunk 13 7 1 Pair_13_7 pair_13_7_checked
#print axioms pair_13_7_checked
certify_pair_chunk 13 8 1 Pair_13_8 pair_13_8_checked
#print axioms pair_13_8_checked
certify_pair_chunk 13 9 1 Pair_13_9 pair_13_9_checked
#print axioms pair_13_9_checked
certify_pair_chunk 13 10 1 Pair_13_10 pair_13_10_checked
#print axioms pair_13_10_checked
certify_pair_chunk 13 11 1 Pair_13_11 pair_13_11_checked
#print axioms pair_13_11_checked
certify_pair_chunk 13 12 1 Pair_13_12 pair_13_12_checked
#print axioms pair_13_12_checked
certify_pair_chunk 13 13 1 Pair_13_13 pair_13_13_checked
#print axioms pair_13_13_checked

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
#print axioms pair_13_checked


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
#print axioms forest_10_checked

theorem convolution_10_checked : convolutionDots 10 (forest 10)=certifiedPayoff 10 := by
  have hf := congrArg (convolutionDots 10) forest_10_checked
  exact hf.trans ((convolutionDots_eq_of_fees 10 Forest_10 MassFee MgfFee ResFee
    packedFee_0_checked packedFee_1_checked packedFee_2_checked).trans (by decide +kernel))
#print axioms convolution_10_checked


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
#print axioms forest_11_checked

theorem convolution_11_checked : convolutionDots 11 (forest 11)=certifiedPayoff 11 := by
  have hf := congrArg (convolutionDots 11) forest_11_checked
  exact hf.trans ((convolutionDots_eq_of_fees 11 Forest_11 MassFee MgfFee ResFee
    packedFee_0_checked packedFee_1_checked packedFee_2_checked).trans (by decide +kernel))
#print axioms convolution_11_checked


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
#print axioms forest_12_checked

theorem convolution_12_checked : convolutionDots 12 (forest 12)=certifiedPayoff 12 := by
  have hf := congrArg (convolutionDots 12) forest_12_checked
  exact hf.trans ((convolutionDots_eq_of_fees 12 Forest_12 MassFee MgfFee ResFee
    packedFee_0_checked packedFee_1_checked packedFee_2_checked).trans (by decide +kernel))
#print axioms convolution_12_checked


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
#print axioms forest_13_checked

theorem convolution_13_checked : convolutionDots 13 (forest 13)=certifiedPayoff 13 := by
  have hf := congrArg (convolutionDots 13) forest_13_checked
  exact hf.trans ((convolutionDots_eq_of_fees 13 Forest_13 MassFee MgfFee ResFee
    packedFee_0_checked packedFee_1_checked packedFee_2_checked).trans (by decide +kernel))
#print axioms convolution_13_checked


end ClaudeWCT.Numerics.SharedGeneratedForest

namespace ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedPathPacked
certify_pair_chunk 14 0 1 Pair_14_0 pair_14_0_checked
#print axioms pair_14_0_checked
certify_pair_chunk 14 1 1 Pair_14_1 pair_14_1_checked
#print axioms pair_14_1_checked
certify_pair_chunk 14 2 1 Pair_14_2 pair_14_2_checked
#print axioms pair_14_2_checked
certify_pair_chunk 14 3 1 Pair_14_3 pair_14_3_checked
#print axioms pair_14_3_checked
certify_pair_chunk 14 4 1 Pair_14_4 pair_14_4_checked
#print axioms pair_14_4_checked
certify_pair_chunk 14 5 1 Pair_14_5 pair_14_5_checked
#print axioms pair_14_5_checked
certify_pair_chunk 14 6 1 Pair_14_6 pair_14_6_checked
#print axioms pair_14_6_checked
certify_pair_chunk 14 7 1 Pair_14_7 pair_14_7_checked
#print axioms pair_14_7_checked
certify_pair_chunk 14 8 1 Pair_14_8 pair_14_8_checked
#print axioms pair_14_8_checked
certify_pair_chunk 14 9 1 Pair_14_9 pair_14_9_checked
#print axioms pair_14_9_checked
certify_pair_chunk 14 10 1 Pair_14_10 pair_14_10_checked
#print axioms pair_14_10_checked
certify_pair_chunk 14 11 1 Pair_14_11 pair_14_11_checked
#print axioms pair_14_11_checked
certify_pair_chunk 14 12 1 Pair_14_12 pair_14_12_checked
#print axioms pair_14_12_checked
certify_pair_chunk 14 13 1 Pair_14_13 pair_14_13_checked
#print axioms pair_14_13_checked
certify_pair_chunk 14 14 1 Pair_14_14 pair_14_14_checked
#print axioms pair_14_14_checked

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
#print axioms pair_14_checked


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
#print axioms forest_14_checked

theorem convolution_14_checked : convolutionDots 14 (forest 14)=certifiedPayoff 14 := by
  have hf := congrArg (convolutionDots 14) forest_14_checked
  exact hf.trans ((convolutionDots_eq_of_fees 14 Forest_14 MassFee MgfFee ResFee
    packedFee_0_checked packedFee_1_checked packedFee_2_checked).trans (by decide +kernel))
#print axioms convolution_14_checked


end ClaudeWCT.Numerics.SharedGeneratedForest

namespace ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedPathPacked
certify_pair_chunk 15 0 1 Pair_15_0 pair_15_0_checked
#print axioms pair_15_0_checked
certify_pair_chunk 15 1 1 Pair_15_1 pair_15_1_checked
#print axioms pair_15_1_checked
certify_pair_chunk 15 2 1 Pair_15_2 pair_15_2_checked
#print axioms pair_15_2_checked
certify_pair_chunk 15 3 1 Pair_15_3 pair_15_3_checked
#print axioms pair_15_3_checked
certify_pair_chunk 15 4 1 Pair_15_4 pair_15_4_checked
#print axioms pair_15_4_checked
certify_pair_chunk 15 5 1 Pair_15_5 pair_15_5_checked
#print axioms pair_15_5_checked
certify_pair_chunk 15 6 1 Pair_15_6 pair_15_6_checked
#print axioms pair_15_6_checked
certify_pair_chunk 15 7 1 Pair_15_7 pair_15_7_checked
#print axioms pair_15_7_checked
certify_pair_chunk 15 8 1 Pair_15_8 pair_15_8_checked
#print axioms pair_15_8_checked
certify_pair_chunk 15 9 1 Pair_15_9 pair_15_9_checked
#print axioms pair_15_9_checked
certify_pair_chunk 15 10 1 Pair_15_10 pair_15_10_checked
#print axioms pair_15_10_checked
certify_pair_chunk 15 11 1 Pair_15_11 pair_15_11_checked
#print axioms pair_15_11_checked
certify_pair_chunk 15 12 1 Pair_15_12 pair_15_12_checked
#print axioms pair_15_12_checked
certify_pair_chunk 15 13 1 Pair_15_13 pair_15_13_checked
#print axioms pair_15_13_checked
certify_pair_chunk 15 14 1 Pair_15_14 pair_15_14_checked
#print axioms pair_15_14_checked
certify_pair_chunk 15 15 1 Pair_15_15 pair_15_15_checked
#print axioms pair_15_15_checked

noncomputable def Pair_15 : Nat := pair_sum_numeral% 15

noncomputable def chunks_15 (t : Nat) : Nat :=
  match t with
  | 0 => Pair_15_0
  | 1 => Pair_15_1
  | 2 => Pair_15_2
  | 3 => Pair_15_3
  | 4 => Pair_15_4
  | 5 => Pair_15_5
  | 6 => Pair_15_6
  | 7 => Pair_15_7
  | 8 => Pair_15_8
  | 9 => Pair_15_9
  | 10 => Pair_15_10
  | 11 => Pair_15_11
  | 12 => Pair_15_12
  | 13 => Pair_15_13
  | 14 => Pair_15_14
  | 15 => Pair_15_15
  | _ => 0

theorem chunks_15_checked (t : Nat) (ht : t ≤ 15) :
    pairChunkWith cachedCoordinate 15 t 1 = chunks_15 t := by
  interval_cases t
  · exact pair_15_0_checked
  · exact pair_15_1_checked
  · exact pair_15_2_checked
  · exact pair_15_3_checked
  · exact pair_15_4_checked
  · exact pair_15_5_checked
  · exact pair_15_6_checked
  · exact pair_15_7_checked
  · exact pair_15_8_checked
  · exact pair_15_9_checked
  · exact pair_15_10_checked
  · exact pair_15_11_checked
  · exact pair_15_12_checked
  · exact pair_15_13_checked
  · exact pair_15_14_checked
  · exact pair_15_15_checked

theorem pair_15_checked : pairFirst 15 = Pair_15 := by
  have h := pairFirst_eq_cached_sum cachedCoordinate chunks_15 15
    (fun t ht => cachedCoordinate_correct t (by omega)) chunks_15_checked
  exact h.trans (by decide +kernel)
#print axioms pair_15_checked


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

noncomputable def Forest_15 : Nat := forest_numeral% 15

theorem forest_15_checked : forest 15=Forest_15 := by
  exact (forest_eq_of_inputs 15 Pair_15 Coordinate_128_15
    pair_15_checked coordinate_128_15_checked).trans (by rw [spread_eq_fast]; decide +kernel)
#print axioms forest_15_checked

theorem convolution_15_checked : convolutionDots 15 (forest 15)=certifiedPayoff 15 := by
  have hf := congrArg (convolutionDots 15) forest_15_checked
  exact hf.trans ((convolutionDots_eq_of_fees 15 Forest_15 MassFee MgfFee ResFee
    packedFee_0_checked packedFee_1_checked packedFee_2_checked).trans (by decide +kernel))
#print axioms convolution_15_checked


end ClaudeWCT.Numerics.SharedGeneratedForest

namespace ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedPathPacked
certify_pair_chunk 16 0 1 Pair_16_0 pair_16_0_checked
#print axioms pair_16_0_checked
certify_pair_chunk 16 1 1 Pair_16_1 pair_16_1_checked
#print axioms pair_16_1_checked
certify_pair_chunk 16 2 1 Pair_16_2 pair_16_2_checked
#print axioms pair_16_2_checked
certify_pair_chunk 16 3 1 Pair_16_3 pair_16_3_checked
#print axioms pair_16_3_checked
certify_pair_chunk 16 4 1 Pair_16_4 pair_16_4_checked
#print axioms pair_16_4_checked
certify_pair_chunk 16 5 1 Pair_16_5 pair_16_5_checked
#print axioms pair_16_5_checked
certify_pair_chunk 16 6 1 Pair_16_6 pair_16_6_checked
#print axioms pair_16_6_checked
certify_pair_chunk 16 7 1 Pair_16_7 pair_16_7_checked
#print axioms pair_16_7_checked
certify_pair_chunk 16 8 1 Pair_16_8 pair_16_8_checked
#print axioms pair_16_8_checked
certify_pair_chunk 16 9 1 Pair_16_9 pair_16_9_checked
#print axioms pair_16_9_checked
certify_pair_chunk 16 10 1 Pair_16_10 pair_16_10_checked
#print axioms pair_16_10_checked
certify_pair_chunk 16 11 1 Pair_16_11 pair_16_11_checked
#print axioms pair_16_11_checked
certify_pair_chunk 16 12 1 Pair_16_12 pair_16_12_checked
#print axioms pair_16_12_checked
certify_pair_chunk 16 13 1 Pair_16_13 pair_16_13_checked
#print axioms pair_16_13_checked
certify_pair_chunk 16 14 1 Pair_16_14 pair_16_14_checked
#print axioms pair_16_14_checked
certify_pair_chunk 16 15 1 Pair_16_15 pair_16_15_checked
#print axioms pair_16_15_checked
certify_pair_chunk 16 16 1 Pair_16_16 pair_16_16_checked
#print axioms pair_16_16_checked

noncomputable def Pair_16 : Nat := pair_sum_numeral% 16

noncomputable def chunks_16 (t : Nat) : Nat :=
  match t with
  | 0 => Pair_16_0
  | 1 => Pair_16_1
  | 2 => Pair_16_2
  | 3 => Pair_16_3
  | 4 => Pair_16_4
  | 5 => Pair_16_5
  | 6 => Pair_16_6
  | 7 => Pair_16_7
  | 8 => Pair_16_8
  | 9 => Pair_16_9
  | 10 => Pair_16_10
  | 11 => Pair_16_11
  | 12 => Pair_16_12
  | 13 => Pair_16_13
  | 14 => Pair_16_14
  | 15 => Pair_16_15
  | 16 => Pair_16_16
  | _ => 0

theorem chunks_16_checked (t : Nat) (ht : t ≤ 16) :
    pairChunkWith cachedCoordinate 16 t 1 = chunks_16 t := by
  interval_cases t
  · exact pair_16_0_checked
  · exact pair_16_1_checked
  · exact pair_16_2_checked
  · exact pair_16_3_checked
  · exact pair_16_4_checked
  · exact pair_16_5_checked
  · exact pair_16_6_checked
  · exact pair_16_7_checked
  · exact pair_16_8_checked
  · exact pair_16_9_checked
  · exact pair_16_10_checked
  · exact pair_16_11_checked
  · exact pair_16_12_checked
  · exact pair_16_13_checked
  · exact pair_16_14_checked
  · exact pair_16_15_checked
  · exact pair_16_16_checked

theorem pair_16_checked : pairFirst 16 = Pair_16 := by
  have h := pairFirst_eq_cached_sum cachedCoordinate chunks_16 16
    (fun t ht => cachedCoordinate_correct t (by omega)) chunks_16_checked
  exact h.trans (by decide +kernel)
#print axioms pair_16_checked


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

noncomputable def Forest_16 : Nat := forest_numeral% 16

theorem forest_16_checked : forest 16=Forest_16 := by
  exact (forest_eq_of_inputs 16 Pair_16 Coordinate_128_16
    pair_16_checked coordinate_128_16_checked).trans (by rw [spread_eq_fast]; decide +kernel)
#print axioms forest_16_checked

theorem convolution_16_checked : convolutionDots 16 (forest 16)=certifiedPayoff 16 := by
  have hf := congrArg (convolutionDots 16) forest_16_checked
  exact hf.trans ((convolutionDots_eq_of_fees 16 Forest_16 MassFee MgfFee ResFee
    packedFee_0_checked packedFee_1_checked packedFee_2_checked).trans (by decide +kernel))
#print axioms convolution_16_checked


end ClaudeWCT.Numerics.SharedGeneratedForest

namespace ClaudeWCT.Numerics.SharedGeneratedPair
open ClaudeWCT.Numerics.SharedPathPacked
certify_pair_chunk 17 0 1 Pair_17_0 pair_17_0_checked
#print axioms pair_17_0_checked
certify_pair_chunk 17 1 1 Pair_17_1 pair_17_1_checked
#print axioms pair_17_1_checked
certify_pair_chunk 17 2 1 Pair_17_2 pair_17_2_checked
#print axioms pair_17_2_checked
certify_pair_chunk 17 3 1 Pair_17_3 pair_17_3_checked
#print axioms pair_17_3_checked
certify_pair_chunk 17 4 1 Pair_17_4 pair_17_4_checked
#print axioms pair_17_4_checked
certify_pair_chunk 17 5 1 Pair_17_5 pair_17_5_checked
#print axioms pair_17_5_checked
certify_pair_chunk 17 6 1 Pair_17_6 pair_17_6_checked
#print axioms pair_17_6_checked
certify_pair_chunk 17 7 1 Pair_17_7 pair_17_7_checked
#print axioms pair_17_7_checked
certify_pair_chunk 17 8 1 Pair_17_8 pair_17_8_checked
#print axioms pair_17_8_checked
certify_pair_chunk 17 9 1 Pair_17_9 pair_17_9_checked
#print axioms pair_17_9_checked
certify_pair_chunk 17 10 1 Pair_17_10 pair_17_10_checked
#print axioms pair_17_10_checked
certify_pair_chunk 17 11 1 Pair_17_11 pair_17_11_checked
#print axioms pair_17_11_checked
certify_pair_chunk 17 12 1 Pair_17_12 pair_17_12_checked
#print axioms pair_17_12_checked
certify_pair_chunk 17 13 1 Pair_17_13 pair_17_13_checked
#print axioms pair_17_13_checked
certify_pair_chunk 17 14 1 Pair_17_14 pair_17_14_checked
#print axioms pair_17_14_checked
certify_pair_chunk 17 15 1 Pair_17_15 pair_17_15_checked
#print axioms pair_17_15_checked
certify_pair_chunk 17 16 1 Pair_17_16 pair_17_16_checked
#print axioms pair_17_16_checked
certify_pair_chunk 17 17 1 Pair_17_17 pair_17_17_checked
#print axioms pair_17_17_checked

noncomputable def Pair_17 : Nat := pair_sum_numeral% 17

noncomputable def chunks_17 (t : Nat) : Nat :=
  match t with
  | 0 => Pair_17_0
  | 1 => Pair_17_1
  | 2 => Pair_17_2
  | 3 => Pair_17_3
  | 4 => Pair_17_4
  | 5 => Pair_17_5
  | 6 => Pair_17_6
  | 7 => Pair_17_7
  | 8 => Pair_17_8
  | 9 => Pair_17_9
  | 10 => Pair_17_10
  | 11 => Pair_17_11
  | 12 => Pair_17_12
  | 13 => Pair_17_13
  | 14 => Pair_17_14
  | 15 => Pair_17_15
  | 16 => Pair_17_16
  | 17 => Pair_17_17
  | _ => 0

theorem chunks_17_checked (t : Nat) (ht : t ≤ 17) :
    pairChunkWith cachedCoordinate 17 t 1 = chunks_17 t := by
  interval_cases t
  · exact pair_17_0_checked
  · exact pair_17_1_checked
  · exact pair_17_2_checked
  · exact pair_17_3_checked
  · exact pair_17_4_checked
  · exact pair_17_5_checked
  · exact pair_17_6_checked
  · exact pair_17_7_checked
  · exact pair_17_8_checked
  · exact pair_17_9_checked
  · exact pair_17_10_checked
  · exact pair_17_11_checked
  · exact pair_17_12_checked
  · exact pair_17_13_checked
  · exact pair_17_14_checked
  · exact pair_17_15_checked
  · exact pair_17_16_checked
  · exact pair_17_17_checked

theorem pair_17_checked : pairFirst 17 = Pair_17 := by
  have h := pairFirst_eq_cached_sum cachedCoordinate chunks_17 17
    (fun t ht => cachedCoordinate_correct t (by omega)) chunks_17_checked
  exact h.trans (by decide +kernel)
#print axioms pair_17_checked


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

noncomputable def Forest_17 : Nat := forest_numeral% 17

theorem forest_17_checked : forest 17=Forest_17 := by
  exact (forest_eq_of_inputs 17 Pair_17 Coordinate_128_17
    pair_17_checked coordinate_128_17_checked).trans (by rw [spread_eq_fast]; decide +kernel)
#print axioms forest_17_checked

theorem convolution_17_checked : convolutionDots 17 (forest 17)=certifiedPayoff 17 := by
  have hf := congrArg (convolutionDots 17) forest_17_checked
  exact hf.trans ((convolutionDots_eq_of_fees 17 Forest_17 MassFee MgfFee ResFee
    packedFee_0_checked packedFee_1_checked packedFee_2_checked).trans (by decide +kernel))
#print axioms convolution_17_checked


end ClaudeWCT.Numerics.SharedGeneratedForest

namespace ClaudeWCT.Numerics.SharedGeneratedPair
open Lean Elab Command
open ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedGeneratedCoordinate
set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000
set_option Elab.async false
certify_pair_chunk 18 0 1 Pair_18_0 pair_18_0_checked
#print axioms pair_18_0_checked
certify_pair_chunk 18 1 1 Pair_18_1 pair_18_1_checked
#print axioms pair_18_1_checked
certify_pair_chunk 18 2 1 Pair_18_2 pair_18_2_checked
#print axioms pair_18_2_checked
certify_pair_chunk 18 3 1 Pair_18_3 pair_18_3_checked
#print axioms pair_18_3_checked
certify_pair_chunk 18 4 1 Pair_18_4 pair_18_4_checked
#print axioms pair_18_4_checked
certify_pair_chunk 18 5 1 Pair_18_5 pair_18_5_checked
#print axioms pair_18_5_checked
certify_pair_chunk 18 6 1 Pair_18_6 pair_18_6_checked
#print axioms pair_18_6_checked
certify_pair_chunk 18 7 1 Pair_18_7 pair_18_7_checked
#print axioms pair_18_7_checked
certify_pair_chunk 18 8 1 Pair_18_8 pair_18_8_checked
#print axioms pair_18_8_checked
certify_pair_chunk 18 9 1 Pair_18_9 pair_18_9_checked
#print axioms pair_18_9_checked
certify_pair_chunk 18 10 1 Pair_18_10 pair_18_10_checked
#print axioms pair_18_10_checked
certify_pair_chunk 18 11 1 Pair_18_11 pair_18_11_checked
#print axioms pair_18_11_checked
certify_pair_chunk 18 12 1 Pair_18_12 pair_18_12_checked
#print axioms pair_18_12_checked
certify_pair_chunk 18 13 1 Pair_18_13 pair_18_13_checked
#print axioms pair_18_13_checked
certify_pair_chunk 18 14 1 Pair_18_14 pair_18_14_checked
#print axioms pair_18_14_checked
certify_pair_chunk 18 15 1 Pair_18_15 pair_18_15_checked
#print axioms pair_18_15_checked
certify_pair_chunk 18 16 1 Pair_18_16 pair_18_16_checked
#print axioms pair_18_16_checked
certify_pair_chunk 18 17 1 Pair_18_17 pair_18_17_checked
#print axioms pair_18_17_checked
certify_pair_chunk 18 18 1 Pair_18_18 pair_18_18_checked
#print axioms pair_18_18_checked

noncomputable def Pair_18 : Nat := pair_sum_numeral% 18

noncomputable def chunks_18 (t : Nat) : Nat :=
  match t with
  | 0 => Pair_18_0
  | 1 => Pair_18_1
  | 2 => Pair_18_2
  | 3 => Pair_18_3
  | 4 => Pair_18_4
  | 5 => Pair_18_5
  | 6 => Pair_18_6
  | 7 => Pair_18_7
  | 8 => Pair_18_8
  | 9 => Pair_18_9
  | 10 => Pair_18_10
  | 11 => Pair_18_11
  | 12 => Pair_18_12
  | 13 => Pair_18_13
  | 14 => Pair_18_14
  | 15 => Pair_18_15
  | 16 => Pair_18_16
  | 17 => Pair_18_17
  | 18 => Pair_18_18
  | _ => 0

theorem chunks_18_checked (t : Nat) (ht : t ≤ 18) :
    pairChunkWith cachedCoordinate 18 t 1 = chunks_18 t := by
  interval_cases t
  · exact pair_18_0_checked
  · exact pair_18_1_checked
  · exact pair_18_2_checked
  · exact pair_18_3_checked
  · exact pair_18_4_checked
  · exact pair_18_5_checked
  · exact pair_18_6_checked
  · exact pair_18_7_checked
  · exact pair_18_8_checked
  · exact pair_18_9_checked
  · exact pair_18_10_checked
  · exact pair_18_11_checked
  · exact pair_18_12_checked
  · exact pair_18_13_checked
  · exact pair_18_14_checked
  · exact pair_18_15_checked
  · exact pair_18_16_checked
  · exact pair_18_17_checked
  · exact pair_18_18_checked

theorem pair_18_checked : pairFirst 18 = Pair_18 := by
  have h := pairFirst_eq_cached_sum cachedCoordinate chunks_18 18
    (fun t ht => cachedCoordinate_correct t (by omega)) chunks_18_checked
  exact h.trans (by decide +kernel)
#print axioms pair_18_checked


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

noncomputable def Forest_18 : Nat := forest_numeral% 18

theorem forest_18_checked : forest 18=Forest_18 := by
  exact (forest_eq_of_inputs 18 Pair_18 Coordinate_128_18
    pair_18_checked coordinate_128_18_checked).trans (by rw [spread_eq_fast]; decide +kernel)
#print axioms forest_18_checked

theorem convolution_18_checked : convolutionDots 18 (forest 18)=certifiedPayoff 18 := by
  have hf := congrArg (convolutionDots 18) forest_18_checked
  exact hf.trans ((convolutionDots_eq_of_fees 18 Forest_18 MassFee MgfFee ResFee
    packedFee_0_checked packedFee_1_checked packedFee_2_checked).trans (by decide +kernel))
#print axioms convolution_18_checked

theorem convolution_rows_checked (r : Nat) (hlo : 5 ≤ r) (hhi : r ≤ 18) :
    convolutionDots r (forest r)=certifiedPayoff r := by
  interval_cases r
  · exact convolution_5_checked
  · exact convolution_6_checked
  · exact convolution_7_checked
  · exact convolution_8_checked
  · exact convolution_9_checked
  · exact convolution_10_checked
  · exact convolution_11_checked
  · exact convolution_12_checked
  · exact convolution_13_checked
  · exact convolution_14_checked
  · exact convolution_15_checked
  · exact convolution_16_checked
  · exact convolution_17_checked
  · exact convolution_18_checked

#print axioms convolution_rows_checked
end ClaudeWCT.Numerics.SharedGeneratedForest
