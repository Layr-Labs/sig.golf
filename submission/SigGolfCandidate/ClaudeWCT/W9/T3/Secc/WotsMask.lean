import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMaskChain

namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace Mask
open SigGolfCandidate.T3.Security.Wots.Mask
variable (answers : Answers) (a : ChainAddr)
theorem eval_mask_maskAt (level index : Nat) :
    evalWithAnswerFn (maskAt answers a) (mask level index) = evalWithAnswerFn answers (mask level index) :=
  eval_maskAt_of_respects answers a (respectsP_mask a level index)
/-- The keygen payload after the top tree (campaign T8D: masks over the given levels). -/
def keygenRest (levels : List (List Digest)) : M (Digest × Region) := Correctness.cachePayloadProgram (pure levels)
/-- Campaign T8D: the keygen payload is computed from the honest top tree with family seeds. -/
theorem eval_cachePayload_pure (T : Answers) (builder : M (List (List Digest))) :
    evalWithAnswerFn T (Correctness.cachePayloadProgram builder) =
      evalWithAnswerFn T (Correctness.cachePayloadProgram (pure (evalWithAnswerFn T builder))) := by
  unfold Correctness.cachePayloadProgram
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
theorem eval_keygenPayload_wots (T : Answers) :
    evalWithAnswerFn T keygenPayload = evalWithAnswerFn T (keygenRest (WCT9.wotsTree T 0 0)) := by
  have hb : evalWithAnswerFn T buildTopTree = WCT9.wotsTree T 0 0 :=
    (Correctness.eval_buildTopTree T).trans (WCT9.wotsTree_top T).symm
  have h := eval_cachePayload_pure T buildTopTree
  rw [hb] at h
  rw [Correctness.keygenPayload_eq]
  exact h
theorem respects_keygenRest (c : ChainAddr) (levels : List (List Digest)) :
    Respects (Untouched c) (keygenRest levels) := by
  unfold keygenRest Correctness.cachePayloadProgram
  refine Respects.bind (Respects.pure' _) fun levels => ?_
  refine Respects.bind (Respects.mapM _ _ fun level _ => ?_) fun _ => Respects.pure' _
  unfold maskedLevel pairedMask
  exact Respects.bind (Respects.mapM _ _ fun pair _ => Respects.bind
    (Respects.privatePair _ _ _ _ _ (untouched_privatePair c (by decide) _ _ _ _)) fun _ => Respects.pure' _)
    fun _ => Respects.pure' _
theorem eval_buildLeafTop_sig (T : Answers) (leaf : Nat) (digits : List Nat) (hvalid : Cost.ValidDigits 0 digits) :
    evalWithAnswerFn T (buildLeafTop leaf digits true) =
      (0, (List.range (chainCount 0)).map (WCT9.wotsValue T 0 0 leaf digits)) := by
  have h2 := Correctness.eval_buildLeafTop_values T leaf digits hvalid true
  rw [← WCT9.wotsValue_top] at h2
  have h1 : (evalWithAnswerFn T (buildLeafTop leaf digits true)).1 = 0 := by
    rw [Correctness.buildLeafTop_eq]
    simp only [evalWithAnswerFn_bind, ↓reduceIte, evalWithAnswerFn_pure]
  exact Prod.ext h1 h2
/-- Campaign T8D: the top signature values are the family-seeded honest values. -/
theorem eval_signTop_wots (T : Answers) (cache : Cache) (leaf : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits 0 digits) :
    evalWithAnswerFn T (signTop cache leaf digits) =
      ((List.range (chainCount 0)).map (WCT9.wotsValue T 0 0 leaf digits), evalWithAnswerFn T (topPath cache leaf)) := by
  simp only [signTop, evalWithAnswerFn_bind, eval_buildLeafTop_sig T leaf digits hvalid, evalWithAnswerFn_pure]
theorem eval_keygenPayload_maskAt :
    evalWithAnswerFn (maskAt answers a) keygenPayload = evalWithAnswerFn answers keygenPayload := by
  rw [eval_keygenPayload_wots, eval_keygenPayload_wots, wotsTree_maskAt answers a 0 0 (Or.inl rfl)]
  exact eval_maskAt_of_respects answers a (Respects.untouchedP (fun c => respects_keygenRest c _) a)
end Mask
theorem eval_maskAt_keygen (answers : Answers) (a : ChainAddr) :
    evalWithAnswerFn (maskAt answers a) keygen = evalWithAnswerFn answers keygen := by
  unfold keygen
  refine Mask.eval_bind_of (Mask.eval_keygenPayload_maskAt answers a) ?_
  generalize evalWithAnswerFn answers keygenPayload = payload
  rcases payload with ⟨publicKey, region⟩
  exact Mask.eval_maskAt_of_respects answers a (Mask.Respects.bind (Mask.respectsP_privateMac a region) fun _ => Mask.Respects.pure' _)
namespace Mask
open SigGolfCandidate.T3.Security.Wots.Mask
variable (answers : Answers) (a : ChainAddr)
theorem wotsValues_maskAt (lay : Layer) (tree leaf : Nat) (digits : List Nat) (hvalid : Cost.ValidDigits lay digits)
    (hb : SlotOK a lay leaf)
    (halias : LeafAlias lay tree leaf a.key → a.chain < chainCount lay → depth answers a ≤ digits.getD a.chain 0) :
    (List.range (chainCount lay)).map (WCT9.wotsValue (maskAt answers a) lay tree leaf digits) =
      (List.range (chainCount lay)).map (WCT9.wotsValue answers lay tree leaf digits) := by
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  apply wotsValue_maskAt answers a lay tree leaf digits i hi'
  · have := hvalid i hi'
    have := width_le lay i
    omega
  · exact hb
  · intro hal hia
    subst hia
    exact halias hal hi'
theorem eval_topPath_maskAt (cache : Cache) (leaf : Nat) :
    evalWithAnswerFn (maskAt answers a) (topPath cache leaf) = evalWithAnswerFn answers (topPath cache leaf) := by
  apply eval_maskAt_of_respects
  unfold topPath
  exact Respects.mapM _ _ fun level _ => Respects.bind (respectsP_mask a _ _) fun _ => Respects.pure' _
theorem eval_signTop_maskAt (cache : Cache) (leaf : Nat) (digits : List Nat) (hvalid : Cost.ValidDigits 0 digits)
    (halias : LeafAlias 0 0 leaf a.key → a.chain < chainCount 0 → depth answers a ≤ digits.getD a.chain 0) :
    evalWithAnswerFn (maskAt answers a) (signTop cache leaf digits) =
      evalWithAnswerFn answers (signTop cache leaf digits) := by
  have hv := wotsValues_maskAt answers a 0 0 leaf digits hvalid (Or.inl rfl) halias
  rw [eval_signTop_wots _ cache leaf digits hvalid, eval_signTop_wots _ cache leaf digits hvalid, hv,
    eval_topPath_maskAt answers a]
theorem eval_buildTreeP_maskAt (lay : Layer) (hlay : lay ≠ 0) (tree selected : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) (hsel : selected < 2 ^ height lay) (hm : MaskOK a)
    (halias : LeafAlias lay tree selected a.key → a.chain < chainCount lay → depth answers a ≤ digits.getD a.chain 0) :
    evalWithAnswerFn (maskAt answers a) (WCT9.buildTreeP lay tree selected digits) =
      evalWithAnswerFn answers (WCT9.buildTreeP lay tree selected digits) := by
  rw [WCT9.eval_buildTreeP_result _ hlay tree selected digits hvalid hsel,
    WCT9.eval_buildTreeP_result _ hlay tree selected digits hvalid hsel, wotsTree_maskAt answers a lay tree (Or.inr hm),
    wotsValues_maskAt answers a lay tree selected digits hvalid
      (slotOK_of (Or.inr hm) (by have := height_pow_le lay; omega)) halias]
theorem signedMsg_succ (T : Answers) (index m : Nat) (hm : m < 3) :
    WCT9.LayerMsg.pair
      (WCT9.topPair (Fin.ofNat 4 (m + 1)) (WCT9.wotsTree T (Fin.ofNat 4 (m + 1)) (route index (Fin.ofNat 4 (m + 1))).2)).1
      (WCT9.topPair (Fin.ofNat 4 (m + 1)) (WCT9.wotsTree T (Fin.ofNat 4 (m + 1)) (route index (Fin.ofNat 4 (m + 1))).2)).2 =
      leafMsg T (routeLeaf index (Fin.ofNat 4 m)) := by
  have hl : (Fin.ofNat 4 m : Layer).val < 3 := by
    change m % 4 < 3
    omega
  have hlay : (⟨(Fin.ofNat 4 m : Layer).val + 1, by omega⟩ : Layer) = Fin.ofNat 4 (m + 1) := by
    apply Fin.ext
    change m % 4 + 1 = (m + 1) % 4
    omega
  unfold leafMsg routeLeaf
  simp only [dif_pos hl]
  rw [hlay, ← route_tree_succ index m hm]
  rfl
theorem signedMsg_top (T : Answers) (index : Nat) (hindex : index < 2 ^ 31) :
    WCT9.LayerMsg.forest (Extract.honestForest T index) = leafMsg T (routeLeaf index 3) := by
  unfold leafMsg routeLeaf
  simp only [show ¬((3 : Layer).val < 3) by decide, dite_false]
  rw [route_top_index, Nat.mod_eq_of_lt hindex]
theorem routeLeaf_alias {index : Nat} (hindex : index < 2 ^ 31) {lay : Layer} {T : Answers} {counter : BitVec 32}
    {digits : List Nat} (hsearch : referenceSearch T (routeLeaf index lay) = some (counter, digits))
    (htree : a.key.tree < 2 ^ 40) (hleaf : a.key.leaf < 2 ^ 24)
    (hal : LeafAlias lay (route index lay).2 (route index lay).1 a.key) :
    depth T a ≤ digits.getD a.chain 0 := by
  have hk : routeLeaf index lay = a.key :=
    hal.eq_of_lt (route_tree_lt index hindex lay) (route_leaf_lt index lay) htree (by omega)
  unfold depth
  rw [← hk, referenceDigits_of_search hsearch]
theorem routeLeaf_alias_ref {index : Nat} (hindex : index < 2 ^ 31) {lay : Layer} {T : Answers}
    (htree : a.key.tree < 2 ^ 40) (hleaf : a.key.leaf < 2 ^ 24)
    (hal : LeafAlias lay (route index lay).2 (route index lay).1 a.key) :
    depth T a ≤ (referenceDigits T (routeLeaf index lay)).getD a.chain 0 := by
  have hk : routeLeaf index lay = a.key :=
    hal.eq_of_lt (route_tree_lt index hindex lay) (route_leaf_lt index lay) htree (by omega)
  unfold depth
  rw [← hk]
theorem eval_signLayers_maskAt (htree : a.key.tree < 2 ^ 40) (hleaf : a.key.leaf < 2 ^ 24) (cache : Cache)
    (index : Nat) (hindex : index < 2 ^ 31) :
    ∀ n, n ≤ 4 → ∀ msg, (∀ m, n = m + 1 → msg = leafMsg answers (routeLeaf index (Fin.ofNat 4 m))) →
      evalWithAnswerFn (maskAt answers a) (WCT9.signLayersBC cache index n msg) =
        evalWithAnswerFn answers (WCT9.signLayersBC cache index n msg) := by
  intro n
  induction n with
  | zero => intro _ _ _; rfl
  | succ n ih =>
      intro hn msg hmsg
      simp only [WCT9.signLayersBC, evalWithAnswerFn_bind]
      rw [eval_maskAt_of_respects answers a (respectsP_layerCounterSearch a _ _ _ _ _ _)]
      by_cases hn0 : n = 0
      · subst hn0
        have hD : ((evalWithAnswerFn answers (WCT9.layerCounterSearch (Fin.ofNat 4 0) (route index (Fin.ofNat 4 0)).2
            (route index (Fin.ofNat 4 0)).1 msg 0 (WCT9.searchLimit (Fin.ofNat 4 0)))).map Prod.snd).getD dummyTop =
            referenceDigits answers (routeLeaf index (Fin.ofNat 4 0)) := by
          rw [hmsg 0 rfl]
          exact topSigned_reference answers (routeLeaf index (Fin.ofNat 4 0)) rfl
        simp only [ite_true, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
        rw [hD, eval_signTop_maskAt answers a cache _ _ (referenceDigits_spec answers (routeLeaf index (Fin.ofNat 4 0))).2]
        intro hal _
        apply routeLeaf_alias_ref a hindex htree (by omega)
        have ht : (route index (Fin.ofNat 4 0)).2 = 0 := route_top_tree index hindex
        rw [ht]
        exact hal
      cases hs : evalWithAnswerFn answers (WCT9.layerCounterSearch (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2
        (route index (Fin.ofNat 4 n)).1 msg 0 (WCT9.searchLimit (Fin.ofNat 4 n))) with
      | none => simp only [hn0, ite_false]; rfl
      | some found =>
          obtain ⟨counter, digits⟩ := found
          have hd := (WCT9.layerCounterSearch_some answers _ _ _ msg (WCT9.searchLimit (Fin.ofNat 4 n)) 0 counter digits
            (ClaudeWCT.W9.T3.Security.Wots.searchLimit_fits _) hs).2.2
          have hvalid := Cost.validDigits_decode hd
          have hsearch : referenceSearch answers (routeLeaf index (Fin.ofNat 4 n)) = some (counter, digits) := by
            unfold referenceSearch
            rw [← hmsg n rfl]
            exact hs
          simp only [hn0, ite_false]
          · simp only [evalWithAnswerFn_bind]
            have hl0 : (Fin.ofNat 4 n : Layer) ≠ 0 := by
              intro h
              have hv : (Fin.ofNat 4 n : Layer).val = n := Nat.mod_eq_of_lt (by omega)
              rw [h] at hv
              exact hn0 hv.symm
            rw [eval_buildTreeP_maskAt answers a _ hl0 _ _ digits hvalid (route_leaf_bound index _) (maskOK_of_lt hleaf)
                (fun hal _ => routeLeaf_alias a hindex hsearch htree (by omega) hal),
              WCT9.eval_buildTreeP_result answers hl0 _ _ digits hvalid (route_leaf_bound index _)]
            dsimp only
            rw [WCT9.topPair_take]
            obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
            rw [ih (by omega) _ (fun m' hm' => by
              obtain rfl : m = m' := by omega
              exact signedMsg_succ answers index m (by omega))]
            cases evalWithAnswerFn answers (WCT9.signLayersBC cache index (m + 1) _) <;> rfl
end Mask
theorem eval_maskAt_signPayload (answers : Answers) (a : ChainAddr) (htree : a.key.tree < 2 ^ 40)
    (hleaf : a.key.leaf < 2 ^ 24) (cache : Cache) (message : Message) :
    evalWithAnswerFn (maskAt answers a) (signPayload cache message) =
      evalWithAnswerFn answers (signPayload cache message) := by
  rw [show signPayload cache message = ClaudeWCT.WCT9.Rev3.signPayload cache message from rfl,
    ClaudeWCT.WCT9.Rev3.signPayload_eq]
  refine Mask.eval_bind_of (Mask.eval_maskAt_of_respects answers a (Mask.respectsP_privateNonce a message)) ?_
  generalize evalWithAnswerFn answers (privateNonce message) = rho
  refine Mask.eval_bind_of (Mask.eval_maskAt_of_respects answers a (Mask.respectsP_digestSearch a _ _ _ _)) ?_
  generalize evalWithAnswerFn answers (ClaudeWCT.WCT9.digestSearch rho message 0
    ClaudeWCT.WCT9.digestAttemptLimit) = found
  rcases found with _ | ⟨counter, output⟩
  · rfl
  · dsimp only
    refine Mask.eval_bind_of (Mask.eval_maskAt_of_respects answers a (Mask.respectsP_signForest a _ _)) ?_
    rw [ClaudeWCT.WCT9.eval_signForest]
    dsimp only
    refine Mask.eval_bind_of (Mask.eval_signLayers_maskAt answers a htree hleaf cache _ (WCT9.digestIndex_lt _) 4
      le_rfl _ (fun m hm => ?_)) ?_
    · obtain rfl : m = 3 := by omega
      rw [← Extract.honestForest_eq_wct9]
      exact Mask.signedMsg_top answers _ (WCT9.digestIndex_lt _)
    · generalize evalWithAnswerFn answers (WCT9.signLayersBC cache (WCT9.digestIndex output) 4 _) = pieces
      rcases pieces with _ | pieces <;> rfl
theorem eval_maskAt_sign (answers : Answers) (a : ChainAddr) (htree : a.key.tree < 2 ^ 40)
    (hleaf : a.key.leaf < 2 ^ 24) (published : SigGolfCandidate.T3.Cache) (request : Request) :
    evalWithAnswerFn (maskAt answers a) (FullGame.authenticatedSign published request) =
      evalWithAnswerFn answers (FullGame.authenticatedSign published request) := by
  unfold FullGame.authenticatedSign
  refine Mask.eval_bind_of (Mask.eval_maskAt_of_respects answers a (Mask.respectsP_privateMac a _)) ?_
  split
  · exact eval_maskAt_signPayload answers a htree hleaf _ _
  · rfl
theorem maskAt_congr (answers answers' : Answers) (a : ChainAddr)
    (hrows : ∀ input, prefixStep answers a input = none →
      answers (.inl (.inr input)) = answers' (.inl (.inr input)))
    (hcoins : ∀ coin, answers (.inl (.inl coin)) = answers' (.inl (.inl coin)))
    (hprivate : ∀ coordinate, answers (.inr coordinate) = answers' (.inr coordinate))
    (hdepth : depth answers a = depth answers' a)
    (hfrontier : frontierValue answers a = frontierValue answers' a) :
    maskAt answers a = maskAt answers' a := by
  have hstep : prefixStep answers a = prefixStep answers' a := by
    funext input
    unfold prefixStep
    simp only [hdepth]
  funext q
  rcases q with (coin | input) | c
  · exact hcoins coin
  · rw [Mask.maskAt_public, Mask.maskAt_public, ← hstep, hdepth, hfrontier]
    cases hp : prefixStep answers a input with
    | none => exact hrows input hp
    | some step => rfl
  · exact hprivate c
end ClaudeWCT.W9.T3.Security.Wots
