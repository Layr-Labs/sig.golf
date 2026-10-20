import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsMask

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
theorem count_maskAt_of_respects {α : Type} {program : M α} (h : Respects (UntouchedP a) program) :
    (SourceReplay.queried (maskAt answers a) program).length = (SourceReplay.queried answers program).length := by
  rw [queried_maskAt_of_respects answers a h]
def leafCountP (lay : Layer) (leaf : Nat) (digits : List Nat) : Nat :=
  (if leaf % WCT9.famGrp lay = 0 then WCT9.famPairs lay (WCT9.famOf lay leaf) else 0) +
    ((List.range (chainCount lay)).map fun i => digits.getD i 0 + (maxDigit lay i - digits.getD i 0)).sum + 1
theorem queried_length_packedSecret (T : Answers) (lay : Layer) (tree q : Nat) (carry : Digest) :
    (SourceReplay.queried T (WCT9.packedSecret (WCT9.lowerSeedPair lay tree) q carry)).length =
      if q % 2 = 0 then 1 else 0 := by
  unfold WCT9.packedSecret
  split_ifs
  · rw [queried_length_bind, queried_length_pure]
    rfl
  · rfl
theorem queried_length_lowerCoefs (T : Answers) (lay : Layer) (tree leaf : Nat) (carry : List Digest) :
    (SourceReplay.queried T (WCT9.lowerCoefs lay tree leaf carry)).length =
      if leaf % WCT9.famGrp lay = 0 then WCT9.famPairs lay (WCT9.famOf lay leaf) else 0 := by
  unfold WCT9.lowerCoefs WCT9.lowerFamCoefs
  split_ifs
  · rw [queried_length_bind, queried_length_bind, queried_length_foldlM T _ _ (fun _ => 1)
      (fun j _ s => by rw [queried_length_bind, queried_length_pure]; rfl), sum_map_one, List.length_range]
    simp only [queried_length_pure, Nat.add_zero]
  · rfl
theorem queried_length_halfHash (T : Answers) (high : Bool) (input : HashInput) :
    (SourceReplay.queried T (WCT9.halfHash high input)).length = 1 := by
  cases high
  · exact queried_length_shortHash _ _
  · rfl
/-- C3: a chain of the current scheme makes one query per step. -/
theorem queried_length_chainW (T : Answers) (lay : Layer) (tree leaf i start count : Nat) (v : Digest) :
    (SourceReplay.queried T (WCT9.chainW lay tree leaf i start count v)).length = count := by
  unfold WCT9.chainW
  rw [queried_length_foldlM T _ _ (fun _ => 1) (fun _ _ _ => queried_length_halfHash _ _ _), sum_map_one,
    List.length_range']
theorem queried_length_leafStepF (T : Answers) (lay : Layer) (tree leaf : Nat) (digits : List Nat)
    (coefs : List Digest) (s : List Digest × List Digest) (i : Nat) :
    (SourceReplay.queried T (WCT9.leafStepF lay tree leaf digits coefs s i)).length =
      digits.getD i 0 + (maxDigit lay i - digits.getD i 0) := by
  unfold WCT9.leafStepF
  rw [queried_length_bind, queried_length_chainW, queried_length_bind, queried_length_chainW, queried_length_pure,
    Nat.add_zero]
theorem queried_length_buildLeafPF (T : Answers) (lay : Layer) (tree leaf : Nat) (digits : List Nat) (carry : List Digest) :
    (SourceReplay.queried T (WCT9.buildLeafPF lay tree leaf digits carry)).length = leafCountP lay leaf digits := by
  rw [WCT9.buildLeafPF_factor, queried_length_bind, queried_length_lowerCoefs, queried_length_bind]
  unfold WCT9.leafRowsF leafCountP
  rw [queried_length_foldlM T _ _ _ (fun i _ s => queried_length_leafStepF T lay tree leaf digits _ s i),
    queried_length_bind, queried_length_pure]
  have hl : ∀ ends, (SourceReplay.queried T (WCT9.lowerLeafHash lay tree leaf ends)).length = 1 := fun ends => by
    unfold WCT9.lowerLeafHash WCT9.leafHashW WCT9.lowerHash; exact queried_length_halfHash _ _ _
  rw [hl]
  omega
def treeCountP (lay : Layer) (selected : Nat) (digits : List Nat) : Nat :=
  ((List.range (2 ^ height lay)).map fun leaf => leafCountP lay leaf (if leaf = selected then digits else [])).sum
theorem queried_length_treeRowsP (T : Answers) (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    (SourceReplay.queried T (WCT9.treeRowsP lay tree selected digits)).length = treeCountP lay selected digits := by
  unfold WCT9.treeRowsP
  refine queried_length_foldlM T _ _ _ (fun leaf _ rows => ?_) _
  rw [queried_length_bind, queried_length_buildLeafPF]
  generalize evalWithAnswerFn T (WCT9.buildLeafPF lay tree leaf (if leaf = selected then digits else []) rows.2.2) = r
  rcases r with ⟨⟨root, values⟩, c⟩
  dsimp only
  rw [queried_length_pure, Nat.add_zero]
theorem count_buildTreeP_maskAt (lay : Layer) (hlay : lay ≠ 0) (tree selected : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) (hm : MaskOK a) :
    (SourceReplay.queried (maskAt answers a) (WCT9.buildTreeP lay tree selected digits)).length =
      (SourceReplay.queried answers (WCT9.buildTreeP lay tree selected digits)).length := by
  have hroots : ∀ T, (evalWithAnswerFn T (WCT9.treeRowsP lay tree selected digits)).1 =
      (List.range (2 ^ height lay)).map (WCT9.wotsRoot T lay tree) := fun T => by
    obtain ⟨hlen, hroot, -, -⟩ := WCT9.eval_treeRowsP T hlay tree selected digits hvalid
    exact Correctness.list_eq_range_map _ _ _ hlen hroot
  have hm' : (List.range (2 ^ height lay)).map (WCT9.wotsRoot (maskAt answers a) lay tree) =
      (List.range (2 ^ height lay)).map (WCT9.wotsRoot answers lay tree) :=
    List.map_congr_left (fun leaf hleaf => wotsRoot_maskAt answers a lay tree leaf
      (slotOK_of hm (by have := List.mem_range.mp hleaf; have := height_pow_le lay; omega)))
  rw [WCT9.buildTreeP_factor]
  simp only [queried_length_bind, queried_length_pure, queried_length_treeRowsP]
  rw [hroots, hroots, hm', count_maskAt_of_respects answers a (respectsP_buildLevelsBelow a 3 _ _ _
    (by fin_cases lay <;> decide) _ (by simp only [List.length_map, List.length_range]; exact le_rfl))]
theorem count_keygenPayload_maskAt (hm : MaskOK a) :
    (SourceReplay.queried (maskAt answers a) keygenPayload).length =
      (SourceReplay.queried answers keygenPayload).length :=
  queried_length_keygenPayload_congr (S := UntouchedP a) (fun leaves => respectsP_buildTopLevels a leaves) _ _
    (fun _ hq => maskAt_untouched answers a hq)
    (by rw [Correctness.eval_buildTopTree, Correctness.eval_buildTopTree]; exact builtTree_maskAt_top answers a hm)
end Mask
theorem queried_length_maskAt_keygen (answers : Answers) (a : ChainAddr) (hm : Mask.MaskOK a) :
    (SourceReplay.queried (maskAt answers a) keygen).length = (SourceReplay.queried answers keygen).length := by
  unfold keygen
  refine Mask.count_bind_of (Mask.eval_keygenPayload_maskAt answers a hm) (Mask.count_keygenPayload_maskAt answers a hm) ?_
  generalize evalWithAnswerFn answers keygenPayload = payload
  rcases payload with ⟨publicKey, region⟩
  exact Mask.count_maskAt_of_respects answers a (Mask.Respects.bind (Mask.respectsP_privateMac a region) fun _ => Mask.Respects.pure' _)
namespace Mask
open SigGolfCandidate.T3.Security.Wots.Mask
variable (answers : Answers) (a : ChainAddr)
theorem count_signLayers_maskAt (htree : a.key.tree < 2 ^ 40) (hleaf : a.key.leaf < 2 ^ 24) (cache : Cache)
    (index : Nat) (hindex : index < 2 ^ 31) :
    ∀ n, n ≤ 4 → ∀ msg, (∀ m, n = m + 1 → msg = leafMsg answers (routeLeaf index (Fin.ofNat 4 m))) →
      (SourceReplay.queried (maskAt answers a) (WCT9.signLayersBC cache index n msg)).length =
        (SourceReplay.queried answers (WCT9.signLayersBC cache index n msg)).length := by
  intro n
  induction n with
  | zero => intro _ _ _; rfl
  | succ n ih =>
      intro hn msg hmsg
      simp only [WCT9.signLayersBC]
      have cbo : ∀ {α β : Type} {p : M α} {f : α → M β},
          evalWithAnswerFn (maskAt answers a) p = evalWithAnswerFn answers p →
          (SourceReplay.queried (maskAt answers a) p).length = (SourceReplay.queried answers p).length →
          (∀ x, evalWithAnswerFn answers p = x →
            (SourceReplay.queried (maskAt answers a) (f x)).length = (SourceReplay.queried answers (f x)).length) →
          (SourceReplay.queried (maskAt answers a) (p >>= f)).length =
            (SourceReplay.queried answers (p >>= f)).length :=
        fun hp hc hf => count_bind_of hp hc (hf _ rfl)
      refine cbo (eval_maskAt_of_respects answers a (respectsP_layerCounterSearch a _ _ _ _ _ _))
        (count_maskAt_of_respects answers a (respectsP_layerCounterSearch a _ _ _ _ _ _)) ?_
      intro found hs
      by_cases hn0 : n = 0
      · rw [if_pos hn0]
        rw [queried_length_bind, queried_length_bind, queried_length_signTop, queried_length_signTop]
        rfl
      rw [if_neg hn0]
      rcases found with _ | ⟨counter, digits⟩
      · rfl
      ·
          have hd := (WCT9.layerCounterSearch_some answers _ _ _ msg _ 0 counter digits
            (ClaudeWCT.W9.T3.Security.Wots.searchLimit_fits _) hs).2.2
          have hvalid := Cost.validDigits_decode hd
          have hsearch : referenceSearch answers (routeLeaf index (Fin.ofNat 4 n)) = some (counter, digits) := by
            unfold referenceSearch
            rw [← hmsg n rfl]
            exact hs
          have hl0' : (Fin.ofNat 4 n : Layer) ≠ 0 := by
            intro h
            have hv : (Fin.ofNat 4 n : Layer).val = n := Nat.mod_eq_of_lt (by omega)
            rw [h] at hv
            exact hn0 hv.symm
          generalize hL : (Fin.ofNat 4 n : Layer) = L at hs hd hvalid hsearch ⊢
          · have hl0 : L ≠ 0 := hL ▸ hl0'
            refine count_bind_of (eval_buildTreeP_maskAt answers a _ hl0 _ _ digits hvalid (route_leaf_bound index _)
                (maskOK_of_lt hleaf) (fun hal _ => routeLeaf_alias a hindex hsearch htree (by omega) hal))
              (count_buildTreeP_maskAt answers a _ hl0 _ _ digits hvalid (maskOK_of_lt hleaf)) ?_
            rw [WCT9.eval_buildTreeP_result answers hl0 _ _ digits hvalid (route_leaf_bound index _)]
            dsimp only
            rw [WCT9.topPair_take]
            obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
            have hmsg' : ∀ m', m + 1 = m' + 1 → WCT9.LayerMsg.pair
                (WCT9.topPair L (WCT9.wotsTree answers L (route index L).2)).1
                (WCT9.topPair L (WCT9.wotsTree answers L (route index L).2)).2 =
                leafMsg answers (routeLeaf index (Fin.ofNat 4 m')) := fun m' hm' => by
              subst hL
              rw [show m' = m by omega]
              exact signedMsg_succ answers index m (by omega)
            refine count_bind_of (eval_signLayers_maskAt answers a htree hleaf cache index hindex (m + 1) (by omega)
              _ hmsg') (ih (by omega) _ hmsg') ?_
            cases evalWithAnswerFn answers (WCT9.signLayersBC cache index (m + 1) _) <;> rfl
end Mask
theorem queried_length_maskAt_signPayload (answers : Answers) (a : ChainAddr) (htree : a.key.tree < 2 ^ 40)
    (hleaf : a.key.leaf < 2 ^ 24) (cache : Cache) (message : Message) :
    (SourceReplay.queried (maskAt answers a) (signPayload cache message)).length =
      (SourceReplay.queried answers (signPayload cache message)).length := by
  rw [show signPayload cache message = ClaudeWCT.WCT9.Rev3.signPayload cache message from rfl,
    ClaudeWCT.WCT9.Rev3.signPayload_eq]
  refine Mask.count_bind_of (Mask.eval_maskAt_of_respects answers a (Mask.respectsP_privateNonce a message))
    (Mask.count_maskAt_of_respects answers a (Mask.respectsP_privateNonce a message)) ?_
  generalize evalWithAnswerFn answers (privateNonce message) = rho
  refine Mask.count_bind_of (Mask.eval_maskAt_of_respects answers a (Mask.respectsP_digestSearch a _ _ _ _))
    (Mask.count_maskAt_of_respects answers a (Mask.respectsP_digestSearch a _ _ _ _)) ?_
  generalize evalWithAnswerFn answers (ClaudeWCT.WCT9.digestSearch rho message 0
    ClaudeWCT.WCT9.digestAttemptLimit) = found
  rcases found with _ | ⟨counter, output⟩
  · rfl
  · dsimp only
    refine Mask.count_bind_of (Mask.eval_maskAt_of_respects answers a (Mask.respectsP_signForest a _ _))
      (Mask.count_maskAt_of_respects answers a (Mask.respectsP_signForest a _ _)) ?_
    rw [ClaudeWCT.WCT9.eval_signForest]
    dsimp only
    have hmsg : ∀ m, 4 = m + 1 → WCT9.LayerMsg.pair (ClaudeWCT.WCT9.honestTop answers (WCT9.digestIndex output)).1 (ClaudeWCT.WCT9.honestTop answers (WCT9.digestIndex output)).2 =
        leafMsg answers (Mask.routeLeaf (WCT9.digestIndex output) (Fin.ofNat 4 m)) := fun m hm => by
      obtain rfl : m = 3 := by omega
      rw [← Extract.honestTop_eq_wct9]
      exact Mask.signedMsg_top answers _ (WCT9.digestIndex_lt _)
    refine Mask.count_bind_of (Mask.eval_signLayers_maskAt answers a htree hleaf cache _ (WCT9.digestIndex_lt _)
      4 le_rfl _ hmsg) (Mask.count_signLayers_maskAt answers a htree hleaf cache _ (WCT9.digestIndex_lt _) 4
      le_rfl _ hmsg) ?_
    generalize evalWithAnswerFn answers (WCT9.signLayersBC cache (WCT9.digestIndex output) 4 _) = pieces
    rcases pieces with _ | pieces <;> rfl
theorem queried_length_maskAt_sign (answers : Answers) (a : ChainAddr) (htree : a.key.tree < 2 ^ 40)
    (hleaf : a.key.leaf < 2 ^ 24) (published : SigGolfCandidate.T3.Cache) (request : Request) :
    (SourceReplay.queried (maskAt answers a) (FullGame.authenticatedSign published request)).length =
      (SourceReplay.queried answers (FullGame.authenticatedSign published request)).length := by
  unfold FullGame.authenticatedSign
  refine Mask.count_bind_of (Mask.eval_maskAt_of_respects answers a (Mask.respectsP_privateMac a _))
    (Mask.count_maskAt_of_respects answers a (Mask.respectsP_privateMac a _)) ?_
  split
  · exact queried_length_maskAt_signPayload answers a htree hleaf _ _
  · rfl
end ClaudeWCT.W9.T3.Security.Wots
