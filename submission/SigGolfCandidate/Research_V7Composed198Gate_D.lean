import SigGolfCandidate.Research_V7Composed198Gate_C

set_option autoImplicit false
set_option Elab.async false


/-! Exact relevant-bit product law for the shared forest producer. -/
namespace SigGolfCandidate.Research.SharedDigestFields

def fromBits (n : Nat) (f : Fin n → Bool) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn

theorem fromBits_get (n : Nat) (f : Fin n → Bool) (i : Fin n) :
    (fromBits n f).getLsbD i.val = f i := by
  simp only [fromBits, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]

def bitsEquiv (n : Nat) : BitVec n ≃ (Fin n → Bool) where
  toFun v i := v.getLsbD i.val
  invFun := fromBits n
  left_inv v := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    exact fromBits_get n (fun j => v.getLsbD j.val) ⟨i, hi⟩
  right_inv f := by
    funext i
    exact fromBits_get n f i


set_option maxRecDepth 10000
set_option maxHeartbeats 0
def costBase (k : Nat) : Nat := [0, 7, 64, 71, 128, 135, 192, 199, 230].getD k 0
def rankBase (k : Nat) : Nat := [13, 77, 89, 101, 141, 153, 165, 205, 217].getD k 0
def spareBase (k : Nat) : Nat := [5, 6, 12, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 69, 70, 76, 87, 88, 99, 100, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 133, 134, 140, 151, 152, 163, 164, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 197, 198, 204, 215, 216, 227, 228, 229, 235, 236, 237, 238, 239, 240, 241].getD k 0
def position (i : Nat) : Nat :=
  if i < 45 then costBase (i / 5) + i % 5
  else if i < 135 then rankBase ((i-45)/10) + (i-45)%10
  else if i < 166 then 33 + (i-135)
  else if i < 180 then 242 + (i-166)
  else spareBase (i-180)
def inversePosition (i : Nat) : Nat := [0, 1, 2, 3, 4, 180, 181, 5, 6, 7, 8, 9, 182, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 10, 11, 12, 13, 14, 193, 194, 15, 16, 17, 18, 19, 195, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 196, 197, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 198, 199, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 20, 21, 22, 23, 24, 217, 218, 25, 26, 27, 28, 29, 219, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 220, 221, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 222, 223, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 30, 31, 32, 33, 34, 241, 242, 35, 36, 37, 38, 39, 243, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 244, 245, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 246, 247, 248, 40, 41, 42, 43, 44, 249, 250, 251, 252, 253, 254, 255, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179].getD i 0
theorem inversePosition_bound : ∀ i : Fin 256, inversePosition i.val < 256 := by decide +kernel
theorem inversePosition_correct : ∀ i : Fin 256, position (inversePosition i.val) = i.val := by decide +kernel
abbrev Fields := (Fin 9 → BitVec 5) × (Fin 9 → BitVec 10) × BitVec 31 × BitVec 14
def fields (a : BitVec 256) : Fields :=
  (fun k => a.extractLsb' (costBase k.val) 5,
   fun k => a.extractLsb' (rankBase k.val) 10,
   a.extractLsb' 33 31, a.extractLsb' 242 14)
def decompose (a : BitVec 256) : Fields × BitVec 76 :=
  (fields a, fromBits 76 (fun i => a.getLsbD (spareBase i.val)))
theorem decompose_injective : Function.Injective decompose := by
  intro a b h
  have hb : ∀ i : Fin 256, a.getLsbD (position i.val) = b.getLsbD (position i.val) := by
    intro i
    unfold position
    split_ifs with h0 h1 h2 h3
    · have hk : i.val / 5 < 9 := by omega
      have e := congrArg (fun v : Fields × BitVec 76 => (v.1.1 ⟨i.val / 5,hk⟩).getLsbD (i.val % 5)) h
      simpa only [decompose, fields, BitVec.getLsbD_extractLsb',
        Nat.mod_lt _ (by decide : 0 < 5), decide_true, Bool.true_and] using e
    · have hk : (i.val-45)/10 < 9 := by omega
      have e := congrArg (fun v : Fields × BitVec 76 => (v.1.2.1 ⟨(i.val-45)/10,hk⟩).getLsbD ((i.val-45)%10)) h
      simpa only [decompose, fields, BitVec.getLsbD_extractLsb',
        Nat.mod_lt _ (by decide : 0 < 10), decide_true, Bool.true_and] using e
    · have hk : i.val-135 < 31 := by omega
      have e := congrArg (fun v : Fields × BitVec 76 => v.1.2.2.1.getLsbD (i.val-135)) h
      simpa only [decompose, fields, BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and] using e
    · have hk : i.val-166 < 14 := by omega
      have e := congrArg (fun v : Fields × BitVec 76 => v.1.2.2.2.getLsbD (i.val-166)) h
      simpa only [decompose, fields, BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and] using e
    · have hk : i.val-180 < 76 := by omega
      have e := congrArg (fun v : Fields × BitVec 76 => v.2.getLsbD (i.val-180)) h
      simpa only [decompose, fromBits_get 76 _ ⟨i.val-180,hk⟩] using e
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have e := hb ⟨inversePosition k, inversePosition_bound ⟨k,hk⟩⟩
  simpa only [inversePosition_correct ⟨k,hk⟩] using e

theorem decompose_bijective : Function.Bijective decompose := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨decompose_injective, ?_⟩
  simp only [Fields, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_bitVec]
  norm_num
noncomputable def decomposeEquiv : BitVec 256 ≃ Fields × BitVec 76 :=
  Equiv.ofBijective decompose decompose_bijective
end SigGolfCandidate.Research.SharedDigestFields
namespace SigGolfCandidate.Research.SharedDigestFields
noncomputable def fiberEquiv (f : Fields) : {a : BitVec 256 // fields a = f} ≃ BitVec 76 where
  toFun a := (decompose a.val).2
  invFun spare := ⟨decomposeEquiv.symm (f, spare),
    congrArg Prod.fst (decomposeEquiv.apply_symm_apply (f,spare))⟩
  left_inv a := by
    apply Subtype.ext
    apply decomposeEquiv.injective
    change decomposeEquiv (decomposeEquiv.symm (f, (decompose a.val).2)) = decompose a.val
    rw [decomposeEquiv.apply_symm_apply]
    exact Prod.ext a.property.symm rfl
  right_inv spare := congrArg Prod.snd (decomposeEquiv.apply_symm_apply (f,spare))
theorem fiber_card (f : Fields) : Fintype.card {a : BitVec 256 // fields a = f} = 2^76 :=
  (Fintype.card_congr (fiberEquiv f)).trans (Fintype.card_bitVec 76)
end SigGolfCandidate.Research.SharedDigestFields
namespace SigGolfCandidate.Research.SharedDigestFields
open OracleComp OracleSpec ENNReal
 theorem fields_uniform :
    𝒮[fields <$> ($ᵗ BitVec 256 : ProbComp (BitVec 256))] =
      𝒮[($ᵗ Fields : ProbComp Fields)] := by
  have hm : fields <$> ($ᵗ BitVec 256 : ProbComp (BitVec 256)) =
      Prod.fst <$> (decompose <$> ($ᵗ BitVec 256 : ProbComp (BitVec 256))) := by
    simp only [Functor.map_map]
    rfl
  have hd : 𝒮[decompose <$> ($ᵗ BitVec 256 : ProbComp (BitVec 256))] =
      𝒮[($ᵗ (Fields × BitVec 76) : ProbComp (Fields × BitVec 76))] :=
    evalSPMF_map_bijective_uniform_cross (α := BitVec 256) (β := Fields × BitVec 76) decompose decompose_bijective
  rw [hm, evalSPMF_map, hd, ← evalSPMF_map]
  exact evalSPMF_map_fst_uniformSample_prod
end SigGolfCandidate.Research.SharedDigestFields
namespace SigGolfCandidate.Research.SharedDigestFields
open SigGolfCandidate.T3

theorem costBase_source (k : Fin 9) : costBase k.val = SharedForest.costFieldBase k.val := by
  fin_cases k <;> rfl

theorem rankBase_source (k : Nat) : rankBase k = SharedForest.rankBase k := rfl

theorem fields_cost (a : HashOutput) (k : Fin 9) :
    ((fields a).1 k).toNat = (SharedForest.costField a k).val := by
  simp only [fields, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, costBase_source]
  rfl

theorem fields_rank (a : HashOutput) (k : Fin 9) :
    ((fields a).2.1 k).toNat = SharedForest.rawForestRank a k.val := by
  simp only [fields, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, rankBase_source]
  rfl

theorem fields_index (a : HashOutput) : (fields a).2.2.1.toNat = ClaudeWCT.WCT9.digestIndex a := by
  simp only [fields, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rfl

theorem fields_gate (a : HashOutput) : (fields a).2.2.2.toNat = a.toNat / 2^242 % 16384 := by
  simp only [fields, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
end SigGolfCandidate.Research.SharedDigestFields

namespace SigGolfCandidate.Research.SharedDigestFields
open SigGolfCandidate.T3 ClaudeWCT.WCT9 OracleComp OracleSpec

def decodedRank (f : Fields) (k : Fin 9) : Fin 563 :=
  ⟨(f.2.1 k).toNat % 563, Nat.mod_lt _ (by decide)⟩
def coordinateCost (f : Fields) (k : Fin 9) : Nat :=
  routineCost (decodedRank f k) +
    (if SharedForest.firstCoord k.val then SharedForest.aCorrection (f.1 k).toNat
     else SharedForest.bCorrection (f.1 k).toNat)
def cost (f : Fields) : Nat := ((List.finRange 9).map (coordinateCost f)).sum
def accepted (f : Fields) : Bool :=
  decide (f.2.2.2.toNat < 734) &&
    (List.finRange 9).all (fun k => decide ((f.2.1 k).toNat < 563)) && decide (cost f ≤ 777)

theorem decodedRank_fields (a : HashOutput) (k : Fin 9) :
    decodedRank (fields a) k = SharedForest.forestRank a k.val := by
  apply Fin.ext
  simp only [decodedRank, fields_rank]
  rfl

theorem coordinateCost_fields (a : HashOutput) (k : Fin 9) :
    coordinateCost (fields a) k = SharedForest.coordinateAccountingCost a k := by
  simp only [coordinateCost, decodedRank_fields, fields_cost,
    SharedForest.coordinateAccountingCost, SharedForest.accountingCorrection_field]

theorem cost_fields (a : HashOutput) : cost (fields a) = SharedForest.jointAccountingCost a := by
  have hc : coordinateCost (fields a) = SharedForest.coordinateAccountingCost a :=
    funext (coordinateCost_fields a)
  simp only [cost, SharedForest.jointAccountingCost, hc]

theorem accepted_fields (a : HashOutput) : accepted (fields a) = SharedForest.digestAccepted a := by
  simp only [accepted, SharedForest.digestAccepted, SharedForest.ranksAccepted,
    fields_gate, fields_rank, cost_fields]

theorem accepted_uniform :
    𝒮[SharedForest.digestAccepted <$> ($ᵗ HashOutput : ProbComp HashOutput)] =
      𝒮[accepted <$> ($ᵗ Fields : ProbComp Fields)] := by
  have h : SharedForest.digestAccepted = accepted ∘ fields := by
    funext a
    exact (accepted_fields a).symm
  have hm : SharedForest.digestAccepted <$> ($ᵗ HashOutput : ProbComp HashOutput) =
      accepted <$> (fields <$> ($ᵗ HashOutput : ProbComp HashOutput)) := by
    rw [Functor.map_map]
    exact congrArg (fun f => f <$> ($ᵗ HashOutput : ProbComp HashOutput)) h
  rw [hm, evalSPMF_map, fields_uniform, ← evalSPMF_map]

noncomputable def predicateEquiv (p : Fields → Prop) :
    {a : HashOutput // p (fields a)} ≃ {f : Fields // p f} × BitVec 76 where
  toFun a := (⟨fields a.val, a.property⟩, (decompose a.val).2)
  invFun v := ⟨decomposeEquiv.symm (v.1.val, v.2), by
    have h := congrArg Prod.fst (decomposeEquiv.apply_symm_apply (v.1.val,v.2))
    change fields (decomposeEquiv.symm (v.1.val,v.2)) = v.1.val at h
    rw [h]
    exact v.1.property⟩
  left_inv a := by
    apply Subtype.ext
    exact decomposeEquiv.symm_apply_apply a.val
  right_inv v := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst (decomposeEquiv.apply_symm_apply (v.1.val,v.2))
    · change (decompose (decomposeEquiv.symm (v.1.val,v.2))).2 = v.2
      exact congrArg Prod.snd (decomposeEquiv.apply_symm_apply (v.1.val,v.2))

theorem predicate_card (p : Fields → Prop) [DecidablePred p] :
    Fintype.card {a : HashOutput // p (fields a)} = Fintype.card {f : Fields // p f} * 2^76 := by
  rw [Fintype.card_congr (predicateEquiv p), Fintype.card_prod, Fintype.card_bitVec]
end SigGolfCandidate.Research.SharedDigestFields

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem recoverHintedLayers_credit (answers : Answers) (sig : Signature) (index : Nat) (other : Digest) :
    ∀ n, n ≤ 4 → ∀ msg result,
      evalWithAnswerFn answers (recoverHintedLayers sig index other n msg) = some result →
      result.digits.length = n ∧ result.lows.length = n ∧ ∀ lay : Layer, lay.val < n →
        hintFloor sig.policyHints lay ≤
          CanonicalPolicy.credit lay (result.lows.getD lay.val true) (result.digits.getD lay.val []) := by
  intro n
  induction n with
  | zero =>
      intro _ msg result he
      simp [recoverHintedLayers] at he
  | succ n ih =>
      intro hn msg result he
      simp only [recoverHintedLayers, evalWithAnswerFn_bind] at he
      cases hs : evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt (Fin.ofNat 4 n)
        (hintFloor sig.policyHints (Fin.ofNat 4 n)) (route index (Fin.ofNat 4 n)).2
        (route index (Fin.ofNat 4 n)).1 msg 0 (searchLimit (Fin.ofNat 4 n))) with
      | none => simp only [hs, evalWithAnswerFn_pure, reduceCtorEq] at he
      | some found =>
          obtain ⟨counter, digits, low⟩ := found
          have hlim := searchLimit_le (Fin.ofNat 4 n)
          have hd := (canonical_search_valid_credit answers (Fin.ofNat 4 n)
            (hintFloor sig.policyHints (Fin.ofNat 4 n)) (route index (Fin.ofNat 4 n)).2
            (route index (Fin.ofNat 4 n)).1 msg (searchLimit (Fin.ofNat 4 n)) 0 counter digits low
            (by unfold counterLimit at hlim; omega) hs).2
          have hlay := ofNat_layer_val n (by omega)
          simp only [hs] at he
          by_cases hn0 : n = 0
          · subst n
            simp only [if_true, evalWithAnswerFn_bind, evalWithAnswerFn_pure, Option.some.injEq] at he
            subst result
            refine ⟨rfl, rfl, fun lay hsmall => ?_⟩
            have heq : lay = 0 := Fin.ext (by omega)
            subst lay
            exact hd
          · simp only [hn0, if_false, evalWithAnswerFn_bind] at he
            cases hr : evalWithAnswerFn answers (recoverHintedLayers sig index other n
              (.pair (evalWithAnswerFn answers (recoverLayerPair (mainSignature sig) index (Fin.ofNat 4 n) digits)).1
                (evalWithAnswerFn answers (recoverLayerPair (mainSignature sig) index (Fin.ofNat 4 n) digits)).2)) with
            | none => simp only [hr, evalWithAnswerFn_pure, reduceCtorEq] at he
            | some previous =>
                simp only [hr, evalWithAnswerFn_pure, Option.some.injEq] at he
                subst result
                obtain ⟨hlen, hllen, hprevious⟩ := ih (by omega) _ _ hr
                refine ⟨by simp [hlen], by simp [hllen], fun lay hsmall => ?_⟩
                by_cases htop : lay.val = n
                · have heq : lay = Fin.ofNat 4 n := Fin.ext (htop.trans hlay.symm)
                  subst lay
                  simp only [hlay, List.getD_append_right previous.digits [digits] [] n (by omega), hlen,
                    List.getD_append_right previous.lows [low] true n (by omega), hllen,
                    Nat.sub_self, List.getD_cons_zero]
                  exact hd
                · rw [List.getD_append previous.digits [digits] [] lay.val (by omega),
                    List.getD_append previous.lows [low] true lay.val (by omega)]
                  exact hprevious lay (by omega)

theorem policyHints_credit_sum (hints : BitVec 16) (digits : List (List Nat)) (lows : List Bool)
    (hh : policyHintsValid hints digits lows = true)
    (hc : ∀ lay : Layer, hintFloor hints lay ≤
      CanonicalPolicy.credit lay (lows.getD lay.val true) (digits.getD lay.val [])) :
    74 ≤ ((List.finRange 4).map fun lay =>
      CanonicalPolicy.credit lay (lows.getD lay.val true) (digits.getD lay.val [])).sum := by
  simp only [policyHintsValid, decide_eq_true_eq] at hh
  have h0 : 19 ≤ CanonicalPolicy.credit 0 (lows.getD 0 true) (digits.getD 0 []) := by
    simpa [hintFloor, CanonicalPolicy.topFloor] using hc 0
  have h1 := hc 1
  have h2 := hc 2
  have h3 := hc 3
  rw [hh.2.2.1] at h1
  rw [hh.2.2.2.1] at h2
  rw [hh.2.2.2.2] at h3
  have hz := canonical_four_residual (digits.getD 0 []) (digits.getD 1 []) (digits.getD 2 [])
    (digits.getD 3 []) (lows.getD 0 true) (lows.getD 1 true) (lows.getD 2 true) (lows.getD 3 true) h0 h1 h2 h3
  simp only [CanonicalPolicy.nextResidual] at hz
  change 74 ≤ CanonicalPolicy.credit 0 (lows.getD 0 true) (digits.getD 0 []) +
    (CanonicalPolicy.credit 1 (lows.getD 1 true) (digits.getD 1 []) +
      (CanonicalPolicy.credit 2 (lows.getD 2 true) (digits.getD 2 []) +
      (CanonicalPolicy.credit 3 (lows.getD 3 true) (digits.getD 3 []) + 0)))
  omega
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.Cost
open ClaudeWCT.WCT9.Cost
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem maxDigit_le_seven (lay : Layer) (i : Nat) : maxDigit lay i ≤ 7 := by
  unfold maxDigit
  split
  · split <;> omega
  · omega

/-- Coarse unconditional main-tree recovery bound; no old local credit floor
or old layer-two/three target is used. -/
theorem bound_recoverLayerPair_coarse (sig : ClaudeWCT.WCT9.Signature) (index : Nat)
    (lay : Layer) (digits : List Nat) :
    CBound (fun _ => True) 404 (recoverLayerPair sig index lay digits) := by
  unfold recoverLayerPair
  dsimp only
  refine (Bound.mapM_list (P := GoodQuery) (List.finRange (chainCount lay)) _
    (fun _ => 7) (fun i _ => (bound_chainW _ _ _ _ _ _ _).mono_k
      (Nat.sub_le _ _ |>.trans (maxDigit_le_seven lay i.val)))).bind'
    (l := leafHashCost lay + (height lay - 1)) (fun ends hends => ?_) ?_
  · refine (bound_lowerLeafHash lay _ _ ends (by simpa using hends)).bind (fun root _ => ?_)
    refine ((Bound.foldlM_list (P := GoodQuery) (List.finRange (height lay - 1)) _
      (fun _ _ => True) (fun _ => 1) root trivial (fun i hi value _ => ?_)).bind' (l := 0)
      (fun _ _ => .pure _ 0 trivial) (by simp))
    exact bound_lowerNodeHash _ _ _ _ _
  · fin_cases lay <;> decide

theorem bound_topFold_coarse (sig : ClaudeWCT.WCT9.Signature) (index : Nat) (digits : List Nat) :
    CBound (fun _ => True) 403 (topFold sig index digits) := by
  unfold topFold topEnds
  refine (Bound.mapM_list (P := GoodQuery) (List.finRange (chainCount 0)) _
    (fun _ => 7) (fun i _ => (bound_layChain _ _ _ _ _ _ _).mono_k
      (Nat.sub_le _ _ |>.trans (maxDigit_le_seven 0 i.val)))).bind'
    (l := leafHashCost 0 + 11) (fun ends hends => ?_) ?_
  · refine (bound_leafHash 0 _ _ ends (by simpa using hends)).bind (fun root _ => ?_)
    refine (Bound.foldlM_list (P := GoodQuery) ((List.finRange (height 0)).take 11) _
      (fun _ _ => True) (fun _ => 1) root trivial (fun i hi value _ => ?_)).mono_k
        (by rw [take_top_length]; simp)
    unfold topStep
    exact bound_nodeHash _ _ _ _ _ _
  · decide

/-- Top-bytes layer: the expander's nonce re-derivation costs at most `topNonceCap h = 104·2^h` per path node of
height `h = 1..11` (Σ = 425,776), on top of the 392 chain/leaf compressions. -/
def topFoldNCost : Nat := 392 + 425776
theorem bound_topFoldN_coarse (sig : ClaudeWCT.WCT9.Signature) (index : Nat) (digits : List Nat) :
    CBound (fun _ => True) topFoldNCost (topFoldN sig index digits) := by
  unfold topFoldN topEnds topFoldNCost
  refine (Bound.mapM_list (P := GoodQuery) (List.finRange (chainCount 0)) _
    (fun _ => 7) (fun i _ => (bound_layChain _ _ _ _ _ _ _).mono_k
      (Nat.sub_le _ _ |>.trans (maxDigit_le_seven 0 i.val)))).bind'
    (l := leafHashCost 0 + 425776) (fun ends hends => ?_) ?_
  · refine (bound_leafHash 0 _ _ ends (by simpa using hends)).bind (fun root _ => ?_)
    refine (Bound.foldlM_list (P := GoodQuery) ((List.finRange (height 0)).take 11) _
      (fun _ _ => True) (fun i => topNonceCap (i + 1)) (root, []) trivial (fun i hi st _ => ?_)).mono_k
        (by decide +kernel)
    have hjv : (((List.finRange (height 0)).take 11)[i]'hi).val = i := by simp [List.getElem_take]
    unfold topStepN
    exact (Cost.bound_topNodeAt _ _ _ _).bind' (l := 0) (fun _ _ => .pure _ 0 trivial) (by rw [hjv]; simp)
  · decide

theorem bound_recoverSharedInner (first : Bool) (index coord : Nat) (hc : coord<9)
    (selected : Child) (word : Rank) (values : Fin 6 → Digest) (path : Nat → Digest) (prev : PairRoot) :
    CBound (fun _ => True) 31 (recoverSharedInner first index coord selected word values path prev) := by
  unfold recoverSharedInner
  have hj := rawChild_lt first selected.val selected.isLt
  refine (Bound.mapM_list (P := GoodQuery) (List.finRange 6) _ (fun _ => 4)
    (fun i _ => (cbound_of_ftsBound (ftsBound_chain index coord (rawChild first selected.val)
      i.val (4-wordDigit word i) (wordDigit word i) (values i) hc hj i.isLt
      (by have h := wordDigit_le_four word i; omega))).mono_k (wordDigit_le_four word i))).bind'
      (l := 7) (fun ends hends => ?_) (by decide)
  refine (cbound_of_ftsBound (ftsBound_leafHashH index (128 + selected.val) coord (rawChild first selected.val)
    prev.1 ends hc hj (by simpa using hends))).bind'
      (l := 5) (fun leaf _ => ?_) (by decide)
  exact (Bound.foldlM_list (P := GoodQuery) (List.range 5) _ (fun _ _ => True) (fun _ => 1)
    leaf trivial (fun i hi value _ => bound_sharedNode ..)).mono_k (by simp)

theorem bound_recoverPair (index pair : Nat) (hp : pair<4) (selected : Selection)
    (aWord bWord : Rank) (opened : PairOpening) (prev : PairRoot) :
    CBound (fun _ => True) 63 (recoverPair index pair selected aWord bWord opened prev) := by
  unfold recoverPair
  refine (bound_recoverSharedInner true index (2*pair) (by omega) _ _ _ _ _).bind'
    (l := 32) (fun a _ => ?_) (by decide)
  refine (bound_recoverSharedInner false index (2*pair+1) (by omega) _ _ _ _ _).bind'
    (l := 1) (fun b _ => ?_) (by decide)
  exact (bound_sharedOuterHash ..).bind' (l := 0) (fun outer _ => .pure _ 0 trivial) (by decide)

theorem bound_recoverSingleton (index : Nat) (selected : Child) (word : Rank)
    (opened : SingletonOpening) (prev : PairRoot) :
    CBound (fun _ => True) 32 (recoverSingleton index selected word opened prev) := by
  unfold recoverSingleton
  refine (bound_recoverSharedInner false index 8 (by decide) _ _ _ _ _).bind'
    (l := 1) (fun inner _ => ?_) (by decide)
  exact (bound_sharedOuterHash ..).bind' (l := 0) (fun outer _ => .pure _ 0 trivial) (by decide)

theorem bound_recoverForest (index : Nat) (selected : ForestSelection) (words : ForestWords)
    (opened : ForestOpening) :
    CBound (fun _ => True) 284 (recoverForest index selected words opened) := by
  unfold recoverForest
  refine (Bound.foldlM_list (P := GoodQuery) (List.finRange 4) _ (fun _ _ => True) (fun _ => 63)
    ftsStart trivial (fun i hi prev _ => bound_recoverPair index ((List.finRange 4)[i]).val ((List.finRange 4)[i]).isLt _ _ _ _ _)).bind'
      (l := 32) (fun prev _ => bound_recoverSingleton ..) (by decide)

#print axioms bound_recoverForest
#print axioms bound_recoverLayerPair_coarse
end SigGolfCandidate.Research.SharedForest
