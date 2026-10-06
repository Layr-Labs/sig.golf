import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMask

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
theorem count_buildTree_maskAt_top (tree selected : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits 0 digits) :
    (SourceReplay.queried (maskAt answers a) (buildTree 0 tree selected digits)).length =
      (SourceReplay.queried answers (buildTree 0 tree selected digits)).length := by
  rw [Correctness.buildTree_eq, queried_length_bind (maskAt answers a), queried_length_bind answers,
    queried_length_treeRows, queried_length_treeRows, Correctness.eval_treeRows _ 0 tree selected digits hvalid,
    Correctness.eval_treeRows _ 0 tree selected digits hvalid]
  have hr : Correctness.leafRoot (maskAt answers a) 0 tree = Correctness.leafRoot answers 0 tree :=
    funext (leafRoot_maskAt_top answers a tree)
  rw [hr]
  dsimp only
  rw [queried_length_bind, queried_length_bind, queried_length_pure, queried_length_pure,
    count_maskAt_of_respects answers a (respectsP_buildLevels a 3 _ _ _ _ (by decide))]
def leafCountP (lay : Layer) (leaf : Nat) (digits : List Nat) : Nat :=
  ((List.range (chainCount lay)).map fun i =>
    (if WCT9.lowerOrdinal lay leaf i % 2 = 0 then 1 else 0) +
      (digits.getD i 0 + (maxDigit lay i - digits.getD i 0))).sum + 1
theorem queried_length_packedSecret (T : Answers) (lay : Layer) (tree q : Nat) (carry : Digest) :
    (SourceReplay.queried T (WCT9.packedSecret (WCT9.lowerSeedPair lay tree) q carry)).length =
      if q % 2 = 0 then 1 else 0 := by
  unfold WCT9.packedSecret
  split_ifs
  · rw [queried_length_bind, queried_length_pure]
    rfl
  · rfl
theorem queried_length_leafStepP (T : Answers) (lay : Layer) (tree leaf : Nat) (digits : List Nat)
    (s : List Digest × List Digest × Digest) (i : Nat) :
    (SourceReplay.queried T (WCT9.leafStepP lay tree leaf digits s i)).length =
      (if WCT9.lowerOrdinal lay leaf i % 2 = 0 then 1 else 0) +
        (digits.getD i 0 + (maxDigit lay i - digits.getD i 0)) := by
  unfold WCT9.leafStepP
  rw [queried_length_bind, queried_length_packedSecret]
  generalize evalWithAnswerFn T (WCT9.packedSecret (WCT9.lowerSeedPair lay tree) (WCT9.lowerOrdinal lay leaf i) s.2.2) = sc
  rcases sc with ⟨seed, c⟩
  dsimp only
  rw [queried_length_bind, queried_length_chain, queried_length_bind, queried_length_chain, queried_length_pure,
    Nat.add_zero]
theorem queried_length_buildLeafP (T : Answers) (lay : Layer) (tree leaf : Nat) (digits : List Nat) (carry : Digest) :
    (SourceReplay.queried T (WCT9.buildLeafP lay tree leaf digits carry)).length = leafCountP lay leaf digits := by
  rw [WCT9.buildLeafP_factor, queried_length_bind]
  unfold WCT9.leafRowsP leafCountP
  rw [queried_length_foldlM T _ _ _ (fun i _ s => queried_length_leafStepP T lay tree leaf digits s i),
    queried_length_bind, queried_length_pure]
  rfl
def treeCountP (lay : Layer) (selected : Nat) (digits : List Nat) : Nat :=
  ((List.range (2 ^ height lay)).map fun leaf => leafCountP lay leaf (if leaf = selected then digits else [])).sum
theorem queried_length_treeRowsP (T : Answers) (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    (SourceReplay.queried T (WCT9.treeRowsP lay tree selected digits)).length = treeCountP lay selected digits := by
  unfold WCT9.treeRowsP
  refine queried_length_foldlM T _ _ _ (fun leaf _ rows => ?_) _
  rw [queried_length_bind, queried_length_buildLeafP]
  generalize evalWithAnswerFn T (WCT9.buildLeafP lay tree leaf (if leaf = selected then digits else []) rows.2.2) = r
  rcases r with ⟨⟨root, values⟩, c⟩
  rfl
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
      (slotOK_of (Or.inr hm) (by have := List.mem_range.mp hleaf; have := height_pow_le lay; omega)))
  rw [WCT9.buildTreeP_factor]
  simp only [queried_length_bind, queried_length_pure, queried_length_treeRowsP]
  rw [hroots, hroots, hm', count_maskAt_of_respects answers a (respectsP_buildLevels a 3 _ _ _ _ (by decide))]
theorem count_keygenPayload_maskAt :
    (SourceReplay.queried (maskAt answers a) keygenPayload).length =
      (SourceReplay.queried answers keygenPayload).length := by
  rw [Correctness.keygenPayload_eq, queried_length_cachePayload, queried_length_cachePayload,
    count_buildTree_maskAt_top answers a 0 0 [] (Cost.validDigits_nil 0)]
end Mask
theorem queried_length_maskAt_keygen (answers : Answers) (a : ChainAddr) :
    (SourceReplay.queried (maskAt answers a) keygen).length = (SourceReplay.queried answers keygen).length := by
  unfold keygen
  refine Mask.count_bind_of (Mask.eval_keygenPayload_maskAt answers a) (Mask.count_keygenPayload_maskAt answers a) ?_
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
      refine count_bind_of (eval_maskAt_of_respects answers a (respectsP_layerCounterSearch a _ _ _ _ _ _))
        (count_maskAt_of_respects answers a (respectsP_layerCounterSearch a _ _ _ _ _ _)) ?_
      by_cases hn0 : n = 0
      · simp only [hn0, ite_true]
        generalize ((evalWithAnswerFn answers (WCT9.layerCounterSearch (Fin.ofNat 4 0) (route index (Fin.ofNat 4 0)).2
          (route index (Fin.ofNat 4 0)).1 msg 0 (WCT9.searchLimit (Fin.ofNat 4 0)))).map Prod.snd).getD dummyTop = dg
        rw [queried_length_bind, queried_length_bind, queried_length_signTop, queried_length_signTop]
        rfl
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
          · have hl0 : (Fin.ofNat 4 n : Layer) ≠ 0 := by
              intro h
              have hv : (Fin.ofNat 4 n : Layer).val = n := Nat.mod_eq_of_lt (by omega)
              rw [h] at hv
              exact hn0 hv.symm
            refine count_bind_of (eval_buildTreeP_maskAt answers a _ hl0 _ _ digits hvalid (route_leaf_bound index _)
                (maskOK_of_lt hleaf) (fun hal _ => routeLeaf_alias a hindex hsearch htree (by omega) hal))
              (count_buildTreeP_maskAt answers a _ hl0 _ _ digits hvalid (maskOK_of_lt hleaf)) ?_
            rw [WCT9.eval_buildTreeP_result answers hl0 _ _ digits hvalid (route_leaf_bound index _)]
            dsimp only
            obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
            have hmsg' : ∀ m', m + 1 = m' + 1 → WCT9.LayerMsg.pair
                (WCT9.topPair (Fin.ofNat 4 (m + 1)) (WCT9.wotsTree answers (Fin.ofNat 4 (m + 1))
                  (route index (Fin.ofNat 4 (m + 1))).2)).1
                (WCT9.topPair (Fin.ofNat 4 (m + 1)) (WCT9.wotsTree answers (Fin.ofNat 4 (m + 1))
                  (route index (Fin.ofNat 4 (m + 1))).2)).2 =
                leafMsg answers (routeLeaf index (Fin.ofNat 4 m')) := fun m' hm' => by
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
    have hmsg : ∀ m, 4 = m + 1 → WCT9.LayerMsg.forest (ClaudeWCT.WCT9.honestForest answers (WCT9.digestIndex output)) =
        leafMsg answers (Mask.routeLeaf (WCT9.digestIndex output) (Fin.ofNat 4 m)) := fun m hm => by
      obtain rfl : m = 3 := by omega
      rw [← Extract.honestForest_eq_wct9]
      exact Mask.signedMsg_top answers _ (WCT9.digestIndex_lt _)
    refine Mask.count_bind_of (Mask.eval_signLayers_maskAt answers a htree hleaf cache _ (WCT9.digestIndex_lt _)
      4 le_rfl _ hmsg) (Mask.count_signLayers_maskAt answers a htree hleaf cache _ (WCT9.digestIndex_lt _) 4
      le_rfl _ hmsg) ?_
    generalize evalWithAnswerFn answers (WCT9.signLayersBC cache (WCT9.digestIndex output) 4 _) = pieces
    rcases pieces with _ | pieces <;> rfl
theorem queried_length_maskAt_coreSign (answers : Answers) (a : ChainAddr) (htree : a.key.tree < 2 ^ 40)
    (hleaf : a.key.leaf < 2 ^ 24) (cache : Cache) (message : Message) :
    (SourceReplay.queried (maskAt answers a) (sign cache message)).length =
      (SourceReplay.queried answers (sign cache message)).length := by
  rw [ClaudeWCT.W9.T3.Security.sign_eq]
  refine Mask.count_bind_of (Mask.eval_maskAt_of_respects answers a (Mask.respectsP_privateMac a _))
    (Mask.count_maskAt_of_respects answers a (Mask.respectsP_privateMac a _)) ?_
  split
  · rfl
  · exact queried_length_maskAt_signPayload answers a htree hleaf cache message
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
