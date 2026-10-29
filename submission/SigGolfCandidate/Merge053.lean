import SigGolfCandidate.Merge005
import SigGolfCandidate.Merge014
import SigGolfCandidate.Merge015
import SigGolfCandidate.Merge026
import SigGolfCandidate.Merge028
import SigGolfCandidate.Merge029
import SigGolfCandidate.Merge030
import SigGolfCandidate.Merge033
import SigGolfCandidate.Merge039
import SigGolfCandidate.Merge043
import SigGolfCandidate.Merge045
import SigGolfCandidate.Merge052

-- ==== merged from ClaudeWCT_W9_T3M_Witness_Queries ====
section

namespace ClaudeWCT.W9.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M (PubGood isHash isPublic allQ_pure allQ_bind allQ_map allQ_ite allQ_foldlM allQ_mapM
  allQ_mono pubGood_shortHash pubGood_publicHash pubGood_nodeHashP pubGood_nodeHash pubGood_digest
  pubGood_chainP pubGood_layerP pubGood_recoverLayer)
open SphincsSecurity (bytesLE bytesLE_length)
set_option linter.unusedSimpArgs false
set_option maxRecDepth 10000
theorem pubGood_wctChainP (index coord child t start count : Nat) (pa : Digest) (pb : BitVec 64) (pc v : Digest) :
    AllQueriesSatisfy (wctChainP index coord child t start count pa pb pc v) PubGood :=
  allQ_foldlM _ _ (fun _ _ => SigGolfCandidate.T3M.pubGood_projHash _ _ (by
    unfold wctChainInputPW wctChainInputP; split <;> simp [bytesLE_length])) _
theorem pubGood_chain (index coord child t start count : Nat) (v : Digest) :
    AllQueriesSatisfy (WCT9.chain index coord child t start count v) PubGood :=
  allQ_foldlM _ _ (fun _ _ => SigGolfCandidate.T3M.pubGood_projHash _ _ (by
    rw [WCT9.ftsChainInputW_length]; omega)) _
theorem pubGood_leafHash (index coord child : Nat) (ends : List Digest) :
    AllQueriesSatisfy (WCT9.leafHash index coord child ends) PubGood :=
  pubGood_shortHash _ (by simp [bytesLE_length])
theorem pubGood_leafHashP (index coord child : Nat) (pad : Digest) (ends : List Digest) :
    AllQueriesSatisfy (WCT9.leafHashP index coord child pad ends) PubGood :=
  pubGood_shortHash _ (by simp [WCT9.leafInputP, bytesLE_length])
theorem pubGood_forestPk (index : Nat) (pairs : List (Digest × Digest)) :
    AllQueriesSatisfy (WCT9.forestPk index pairs) PubGood :=
  pubGood_shortHash _ (by simp [WCT9.forestInput, bytesLE_length, zero16])
theorem pubGood_wctNodeHashP (coord index heap : Nat) (l : Digest) (hp : BitVec 64) (p r : Digest) :
    AllQueriesSatisfy (wctNodeHashP coord index heap l hp p r) PubGood :=
  pubGood_shortHash _ (by simp [SigGolfCandidate.T3M.SecurityInputs.nodeInputPH])
theorem pubGood_wctTopHash (coord index heap : Nat) (l p r : Digest) :
    AllQueriesSatisfy (WCT9.wctTopHash coord index heap l p r) PubGood :=
  WCT9.allQ_highHash_of_shortHash _ (pubGood_shortHash _ (by simp [WCT9.wctTopInput, bytesLE_length]))
theorem pubGood_wctNodeHash (coord index heap : Nat) (l r : Digest) :
    AllQueriesSatisfy (WCT9.wctNodeHash coord index heap l r) PubGood := pubGood_nodeHash _ _ _ _ _ _
/-- C1: the paired leaf of heap `heap` (either half) makes one public, well-formed query. -/
theorem pubGood_leafHashH (heap index coord child : Nat) (pad : Digest) (ends : List Digest) :
    AllQueriesSatisfy (WCT9.leafHashH heap index coord child pad ends) PubGood :=
  WCT9.allQ_ftsHash_of_shortHash _ _ (pubGood_shortHash _ (by simp [WCT9.leafInputP, bytesLE_length]))
/-- C1: a paired packed node (either half) makes one public, well-formed query. -/
theorem pubGood_wctNodeHashH (coord index heap : Nat) (l r : Digest) :
    AllQueriesSatisfy (WCT9.wctNodeHashH coord index heap l r) PubGood :=
  WCT9.allQ_ftsHash_of_shortHash _ _ (pubGood_shortHash _ (by simp [bytesLE_length, zero16]))
theorem pubGood_layerEncodingInputP (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (c : BitVec 32)
    (pad : BitVec 96) (padR : Digest) (hi : BitVec 64) :
    AllQueriesSatisfy (ClaudeWCT.WCT9.encodingHash lay (layerEncodingInputP lay tree leaf msg c pad padR hi)) PubGood := by
  apply (WCT9.allQueries_encodingHash_iff _ _ _).mpr
  apply pubGood_shortHash
  cases msg <;> simp [layerEncodingInputP, WCT9.pairEncodingInputH, bytesLE_length]
theorem pubGood_layerEncodingInput (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (c : BitVec 32) :
    AllQueriesSatisfy (ClaudeWCT.WCT9.encodingHash lay (WCT9.layerEncodingInput lay tree leaf msg c)) PubGood := by
  apply (WCT9.allQueries_encodingHash_iff _ _ _).mpr
  apply pubGood_shortHash
  cases msg <;> simp [WCT9.layerEncodingInput, encodingInput, WCT9.pairEncodingInputP, bytesLE_length]
theorem pubGood_chainW (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (WCT9.chainW lay tree leaf i start count value) PubGood := by
  unfold WCT9.chainW
  exact allQ_foldlM _ _ (fun _ _ => pubGood_halfHash _ _ (by rw [WCT9.chainInputW_length]; omega)) _
theorem pubGood_layerPairP (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) :
    AllQueriesSatisfy (layerPairP w index lay digits) PubGood := by
  unfold layerPairP
  exact allQ_bind (allQ_mapM _ _ fun _ => pubGood_chainPW _ _ _ _ _ _ _ _ _ _) fun _ =>
    allQ_bind (pubGood_leafHashW _ _ _ _ _ _) fun _ =>
      allQ_bind (allQ_foldlM _ _ (fun _ _ => pubGood_lowerNodeHashP _ _ _ _ _ _ _) _) fun _ => allQ_pure _
theorem pubGood_layerGuardedPairP (w : WBytes) (index : Nat) (lay : Layer)
    (answer : Digest) (digits : List Nat) :
    AllQueriesSatisfy (layerGuardedPairP w index lay answer digits) PubGood := by
  unfold layerGuardedPairP
  exact allQ_lowerGuardedRun _ _ _ (fun _ => pubGood_chainPW _ _ _ _ _ _ _ _ _ _)
    (pubGood_layerPairP _ _ _ _)
theorem allQ_topDecodeRun {P : Spec.Domain → Prop} (run : Fin (chainCount 0) → Nat → M Digest)
    (finish : List Digest → M Digest) (answer : Digest) (hrun : ∀ i digit, AllQueriesSatisfy (run i digit) P)
    (hfinish : ∀ ends, AllQueriesSatisfy (finish ends) P) :
    AllQueriesSatisfy (WCT9.topDecodeRun run finish answer) P := by
  cases hd : decode 0 answer with
  | some digits =>
      rw [WCT9.topDecodeRun_of_decode hd]
      exact allQ_map _ (allQ_bind (allQ_mapM _ _ fun _ => hrun _ _) fun _ => hfinish _)
  | none =>
      rw [WCT9.topDecodeRun_of_decode_none hd]
      unfold WCT9.topRejectChains
      exact allQ_map _ (allQ_mapM _ _ fun _ => hrun _ _)
theorem pubGood_verifyTop (sig : WCT9.Signature) (index : Nat) (answer : Digest) :
    AllQueriesSatisfy (WCT9.verifyTop sig index answer) PubGood := by
  unfold WCT9.verifyTop
  exact allQ_topDecodeRun _ _ _ (fun _ _ => SigGolfCandidate.T3M.pubGood_layChain _ _ _ _ _ _ _) fun _ =>
    allQ_bind (SigGolfCandidate.T3M.pubGood_leafHash _ _ _ _) fun _ =>
      allQ_foldlM _ _ (fun _ _ => pubGood_nodeHash _ _ _ _ _ _) _
theorem pubGood_verifyTopP (sig : WCT9.Signature) (pads : Pads) (index : Nat) (answer : Digest) :
    AllQueriesSatisfy (verifyTopP sig pads index answer) PubGood := by
  unfold verifyTopP
  exact allQ_topDecodeRun _ _ _ (fun _ _ => pubGood_chainPW _ _ _ _ _ _ _ _ _ _) fun _ =>
    allQ_bind (pubGood_leafHashW _ _ _ _ _ _) fun _ =>
      allQ_foldlM _ _ (fun _ _ => pubGood_lowerNodeHashP _ _ _ _ _ _ _) _
theorem pubGood_topLayerP (w : WBytes) (index : Nat) (answer : Digest) :
    AllQueriesSatisfy (topLayerP w index answer) PubGood := by
  cases hd : decode 0 answer with
  | some digits =>
      rw [topLayerP_of_decode w index hd]
      exact allQ_map _ (pubGood_layerP _ _ _ _)
  | none =>
      rw [topLayerP_of_decode_none w index hd]
      unfold WCT9.topRejectChains topChainP
      exact allQ_map _ (allQ_mapM _ _ fun _ => pubGood_chainPW _ _ _ _ _ _ _ _ _ _)
theorem pubGood_layersBC (w : WBytes) (index : Nat) : ∀ n msg,
    AllQueriesSatisfy (layersBC w index n msg) PubGood := by
  intro n
  induction n with
  | zero => intro msg; exact allQ_pure _
  | succ n ih =>
      intro msg
      unfold layersBC
      refine allQ_ite _ (allQ_pure _) (allQ_bind (pubGood_layerEncodingInputP _ _ _ _ _ _ _ _) fun ans => ?_)
      refine allQ_ite _ (pubGood_topLayerP _ _ _) ?_
      rcases decode (Fin.ofNat 4 n) ans with _ | digits
      · exact allQ_pure _
      · refine allQ_bind (pubGood_layerGuardedPairP _ _ _ _ _) fun pair => ?_
        cases pair with
        | none => exact allQ_pure _
        | some pair => exact ih _
theorem pubGood_layersBCPrepass (w : WBytes) (index : Nat) : ∀ n msg,
    AllQueriesSatisfy (layersBCPrepass w index n msg) PubGood := by
  intro n
  induction n with
  | zero => intro msg; exact allQ_pure _
  | succ n ih =>
      intro msg
      unfold layersBCPrepass
      refine allQ_ite _ (allQ_pure _) (allQ_bind (pubGood_layerEncodingInputP _ _ _ _ _ _ _ _) fun ans => ?_)
      rcases decode (Fin.ofNat 4 n) ans with _ | digits
      · exact allQ_pure _
      · exact allQ_ite _ (allQ_map _ (pubGood_layerP _ _ _ _))
          (allQ_bind (pubGood_layerPairP _ _ _ _) fun _ => ih _)
theorem pubGood_wctCoordP (w : WBytes) (index : Nat) (coord : WCT9.Coord) (child : WCT9.Child)
    (word : WCT9.Rank) (prev : Digest × Digest) : AllQueriesSatisfy (wctCoordP w index coord child word prev) PubGood := by
  unfold wctCoordP
  exact allQ_bind (allQ_mapM _ _ fun _ => pubGood_wctChainP _ _ _ _ _ _ _ _ _ _) fun _ =>
    allQ_bind (pubGood_leafHashP _ _ _ _ _) fun _ =>
      allQ_bind (allQ_foldlM _ _ (fun _ _ => pubGood_wctNodeHashP _ _ _ _ _ _ _) _) fun _ =>
        allQ_bind (pubGood_wctTopHash _ _ _ _ _ _) fun _ => allQ_pure _
theorem pubGood_wctStep (w : WBytes) (N : HashOutput) (st : Option (List (Digest × Digest))) (coord : WCT9.Coord) :
    AllQueriesSatisfy (wctStep w N st coord) PubGood := by
  unfold wctStep
  rcases st with _ | roots
  · exact allQ_pure _
  · exact allQ_ite _ (allQ_pure _) (allQ_bind (pubGood_wctCoordP _ _ _ _ _ _) fun _ => allQ_pure _)
theorem pubGood_wctP (w : WBytes) (N : HashOutput) : AllQueriesSatisfy (wctP w N) PubGood := by
  unfold wctP
  refine allQ_bind (allQ_foldlM _ _ (pubGood_wctStep w N) _) fun r => ?_
  rcases r with _ | roots
  · exact allQ_pure _
  · exact allQ_pure _
theorem pubGood_verifyP (m : Message) (pk : Digest) (w : WBytes) : AllQueriesSatisfy (verifyP m pk w) PubGood := by
  rw [verifyP_eq_tail]
  refine allQ_bind ?_ fun r => ?_
  · unfold digestP; exact allQ_ite _ (allQ_pure _) (allQ_map _ (pubGood_digest _ _ _))
  · rcases r with _ | N
    · exact allQ_pure _
    unfold verifyTailP
    refine allQ_ite _ (allQ_pure _) (allQ_bind (pubGood_wctP _ _) fun r => ?_)
    rcases r with _ | root
    · exact allQ_pure _
    refine allQ_bind (pubGood_layersBC _ _ _ _) fun r => ?_
    rcases r with _ | root <;> exact allQ_pure _
theorem pubGood_verifyPPrepass (m : Message) (pk : Digest) (w : WBytes) :
    AllQueriesSatisfy (verifyPPrepass m pk w) PubGood := by
  unfold verifyPPrepass
  refine allQ_bind ?_ fun r => ?_
  · unfold digestP; exact allQ_ite _ (allQ_pure _) (allQ_map _ (pubGood_digest _ _ _))
  · rcases r with _ | N
    · exact allQ_pure _
    refine allQ_ite _ (allQ_pure _) (allQ_bind (pubGood_wctP _ _) fun r => ?_)
    rcases r with _ | root
    · exact allQ_pure _
    refine allQ_bind (pubGood_layersBCPrepass _ _ _ _) fun r => ?_
    rcases r with _ | root <;> exact allQ_pure _
theorem pubGood_digestSearch (rho : Digest) (m : Message) : ∀ fuel counter,
    AllQueriesSatisfy (WCT9.digestSearch rho m counter fuel) PubGood := by
  intro fuel
  induction fuel with
  | zero => intro counter; exact allQ_pure _
  | succ fuel ih =>
      intro counter
      unfold WCT9.digestSearch
      exact allQ_bind (pubGood_digest _ _ _) fun _ => allQ_ite _ (allQ_pure _) (ih _)
theorem pubGood_recoverCoordinate (sig : WCT9.Signature) (index : Nat) (output : HashOutput) (coord : WCT9.Coord)
    (prev : Digest × Digest) :
    AllQueriesSatisfy (WCT9.recoverCoordinate sig index output coord prev) PubGood := by
  unfold WCT9.recoverCoordinate
  exact allQ_bind (allQ_mapM _ _ fun _ => pubGood_chain _ _ _ _ _ _ _) fun _ =>
    allQ_bind (pubGood_leafHashP _ _ _ _ _) fun _ =>
      allQ_bind (allQ_foldlM _ _ (fun _ _ => pubGood_wctNodeHash _ _ _ _ _) _) fun _ =>
        allQ_bind (pubGood_wctTopHash _ _ _ _ _ _) fun _ => allQ_pure _
theorem pubGood_recoverFts (sig : WCT9.Signature) (index : Nat) (output : HashOutput) :
    AllQueriesSatisfy (WCT9.recoverFts sig index output) PubGood := by
  unfold WCT9.recoverFts WCT9.recoverFtsFrom
  exact allQ_bind (allQ_foldlM _ _ (fun _ _ => allQ_bind (pubGood_recoverCoordinate _ _ _ _ _) fun _ => allQ_pure _) _)
    fun _ => allQ_pure _
theorem pubGood_recoverCoordinateP (sig : WCT9.Signature) (pads : Pads) (index : Nat) (output : HashOutput)
    (coord : WCT9.Coord) (prev : Digest × Digest) :
    AllQueriesSatisfy (recoverCoordinateP sig pads index output coord prev) PubGood := by
  unfold recoverCoordinateP
  exact allQ_bind (allQ_mapM _ _ fun _ => pubGood_wctChainP _ _ _ _ _ _ _ _ _ _) fun _ =>
    allQ_bind (pubGood_leafHashP _ _ _ _ _) fun _ =>
      allQ_bind (allQ_foldlM _ _ (fun _ _ => pubGood_wctNodeHashP _ _ _ _ _ _ _) _) fun _ =>
        allQ_bind (pubGood_wctTopHash _ _ _ _ _ _) fun _ => allQ_pure _
theorem pubGood_layerCounterSearch (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) : ∀ fuel counter,
    AllQueriesSatisfy (WCT9.layerCounterSearch lay tree leaf msg counter fuel) PubGood := by
  intro fuel
  induction fuel with
  | zero => intro counter; exact allQ_pure _
  | succ fuel ih =>
      intro counter
      unfold WCT9.layerCounterSearch
      refine allQ_bind (pubGood_layerEncodingInput _ _ _ _ _) fun ans => ?_
      rcases WCT9.producerDecode lay ans with _ | digits
      · exact ih _
      · exact allQ_pure _
theorem pubGood_recoverLayerPair (sig : WCT9.Signature) (index : Nat) (lay : Layer) (digits : List Nat) :
    AllQueriesSatisfy (WCT9.recoverLayerPair sig index lay digits) PubGood := by
  unfold WCT9.recoverLayerPair
  exact allQ_bind (allQ_mapM _ _ fun _ => pubGood_chainW _ _ _ _ _ _ _) fun _ =>
    allQ_bind (pubGood_lowerLeafHash _ _ _ _) fun _ =>
      allQ_bind (allQ_foldlM _ _ (fun _ _ => pubGood_lowerNodeHash _ _ _ _ _) _) fun _ => allQ_pure _
theorem pubGood_recoverLayerPairGuard (sig : WCT9.Signature) (index : Nat) (lay : Layer)
    (answer : Digest) (digits : List Nat) :
    AllQueriesSatisfy (WCT9.recoverLayerPairGuard sig index lay answer digits) PubGood := by
  unfold WCT9.recoverLayerPairGuard
  exact allQ_lowerGuardedRun _ _ _ (fun _ => pubGood_chainW _ _ _ _ _ _ _)
    (pubGood_recoverLayerPair _ _ _ _)
theorem pubGood_verifyLayersBC (w : WCT9.Witness) (index : Nat) : ∀ n msg,
    AllQueriesSatisfy (WCT9.verifyLayersBC w index n msg) PubGood := by
  intro n
  induction n with
  | zero => intro msg; exact allQ_pure _
  | succ n ih =>
      intro msg
      unfold WCT9.verifyLayersBC
      refine allQ_ite _ (allQ_pure _) (allQ_bind (pubGood_layerEncodingInput _ _ _ _ _) fun ans => ?_)
      refine allQ_ite _ (pubGood_verifyTop _ _ _) ?_
      rcases decode (Fin.ofNat 4 n) ans with _ | digits
      · exact allQ_pure _
      · refine allQ_bind (pubGood_recoverLayerPairGuard _ _ _ _ _) fun pair => ?_
        cases pair with
        | none => exact allQ_pure _
        | some pair => exact ih _
theorem pubGood_expandLayersBC (sig : WCT9.Signature) (index : Nat) : ∀ n msg,
    AllQueriesSatisfy (WCT9.expandLayersBC sig index n msg) PubGood := by
  intro n
  induction n with
  | zero => intro msg; exact allQ_pure _
  | succ n ih =>
      intro msg
      unfold WCT9.expandLayersBC
      refine allQ_bind (pubGood_layerCounterSearch _ _ _ _ _ _) fun r => ?_
      rcases r with _ | ⟨counter, digits⟩
      · exact allQ_pure _
      · exact allQ_ite _ (allQ_bind (pubGood_recoverLayer _ _ _ _) fun _ => allQ_pure _)
          (allQ_bind (pubGood_recoverLayerPair _ _ _ _) fun _ => allQ_bind (ih _) fun r => by
            rcases r with _ | ⟨root, cs⟩ <;> exact allQ_pure _)
theorem pubGood_recoverFtsP (sig : WCT9.Signature) (pads : Pads) (index : Nat) (output : HashOutput) :
    AllQueriesSatisfy (recoverFtsP sig pads index output) PubGood := by
  unfold recoverFtsP
  exact allQ_bind (allQ_foldlM _ _ (fun _ _ => allQ_bind (pubGood_recoverCoordinateP _ _ _ _ _ _) fun _ => allQ_pure _) _)
    fun _ => allQ_pure _
theorem pubGood_expandN0 (m : Message) (pk : Digest) (σ : WCT9.Signature) :
    AllQueriesSatisfy (expandN0 m pk σ) PubGood := by
  unfold expandN0
  refine allQ_bind (pubGood_digestSearch _ _ _ _) fun r => ?_
  rcases r with _ | ⟨c, N⟩
  · exact allQ_pure _
  refine allQ_bind (pubGood_recoverFts _ _ _) fun root => ?_
  refine allQ_bind (pubGood_expandLayersBC _ _ _ _) fun r => ?_
  rcases r with _ | ⟨root', cs⟩
  · exact allQ_pure _
  exact allQ_ite _ (allQ_pure _) (allQ_pure _)
theorem pubGood_topFold (sig : WCT9.Signature) (index : Nat) (digits : List Nat) :
    AllQueriesSatisfy (WCT9.topFold sig index digits) PubGood := by
  unfold WCT9.topFold WCT9.topEnds
  exact allQ_bind (allQ_mapM _ _ fun _ => SigGolfCandidate.T3M.pubGood_layChain _ _ _ _ _ _ _) fun _ =>
    allQ_bind (SigGolfCandidate.T3M.pubGood_leafHash _ _ _ _) fun _ =>
      allQ_foldlM _ _ (fun _ _ => pubGood_nodeHash _ _ _ _ _ _) _
theorem pubGood_topNode (index : Nat) (v o : Digest) : AllQueriesSatisfy (WCT9.topNode index v o) PubGood := by
  unfold WCT9.topNode
  exact pubGood_nodeHash _ _ _ _ _ _
/-- Top-bytes layer: top node nonce trials are public, well-formed hashes. -/
theorem pubGood_topNodeHashN (heap n : Nat) (l r : Digest) :
    AllQueriesSatisfy (SigGolfCandidate.T3.topNodeHashN heap n l r) PubGood := by
  unfold SigGolfCandidate.T3.topNodeHashN
  exact SigGolfCandidate.T3M.pubGood_projHash _ _
    (by simp [SigGolfCandidate.T3.topNodeInput, SigGolfCandidate.T3.nonceBytes, SphincsSecurity.bytesLE_length])
theorem pubGood_topNonceSearch (h heap : Nat) (l r : Digest) :
    ∀ fuel n, AllQueriesSatisfy (SigGolfCandidate.T3.topNonceSearch h heap l r fuel n) PubGood
  | 0, n => by
      unfold SigGolfCandidate.T3.topNonceSearch
      exact allQ_bind (pubGood_topNodeHashN _ _ _ _) fun _ => allQ_pure _
  | fuel + 1, n => by
      unfold SigGolfCandidate.T3.topNonceSearch
      refine allQ_bind (pubGood_topNodeHashN _ _ _ _) fun _ => ?_
      split
      · exact allQ_pure _
      · exact pubGood_topNonceSearch h heap l r fuel (n + 1)
theorem pubGood_topFoldN (sig : WCT9.Signature) (index : Nat) (digits : List Nat) :
    AllQueriesSatisfy (WCT9.topFoldN sig index digits) PubGood := by
  unfold WCT9.topFoldN WCT9.topEnds
  exact allQ_bind (allQ_mapM _ _ fun _ => SigGolfCandidate.T3M.pubGood_layChain _ _ _ _ _ _ _) fun _ =>
    allQ_bind (SigGolfCandidate.T3M.pubGood_leafHash _ _ _ _) fun _ =>
      allQ_foldlM _ _ (fun _ _ => by
        unfold WCT9.topStepN SigGolfCandidate.T3.topNodeAt
        exact allQ_bind (pubGood_topNonceSearch _ _ _ _ _ _) fun _ => allQ_pure _) _
theorem pubGood_verifyTopN (sig : WCT9.Signature) (nonces : List Nat) (index : Nat) (answer : Digest) :
    AllQueriesSatisfy (WCT9.verifyTopN sig nonces index answer) PubGood := by
  unfold WCT9.verifyTopN
  exact allQ_topDecodeRun _ _ _ (fun _ _ => SigGolfCandidate.T3M.pubGood_layChain _ _ _ _ _ _ _) fun _ =>
    allQ_bind (SigGolfCandidate.T3M.pubGood_leafHash _ _ _ _) fun _ =>
      allQ_foldlM _ _ (fun _ j => by
        dsimp only
        split
        · exact pubGood_topNodeHashN _ _ _ _
        · exact pubGood_nodeHash _ _ _ _ _ _) _
theorem pubGood_expandLayersT (sig : WCT9.Signature) (index : Nat) (o : Digest) : ∀ n msg,
    AllQueriesSatisfy (WCT9.expandLayersT sig index o n msg) PubGood := by
  intro n
  induction n with
  | zero => intro msg; exact allQ_pure _
  | succ n ih =>
      intro msg
      unfold WCT9.expandLayersT
      refine allQ_bind (pubGood_layerCounterSearch _ _ _ _ _ _) fun r => ?_
      rcases r with _ | ⟨counter, digits⟩
      · exact allQ_pure _
      · exact allQ_ite _ (allQ_bind (pubGood_topFold _ _ _) fun _ =>
            allQ_bind (pubGood_topNode _ _ _) fun _ => allQ_pure _)
          (allQ_bind (pubGood_recoverLayerPair _ _ _ _) fun _ => allQ_bind (ih _) fun r => by
            rcases r with _ | ⟨v, root, cs⟩ <;> exact allQ_pure _)
theorem pubGood_searchTop (index : Nat) (v sib pk : Digest) : ∀ fuel c,
    AllQueriesSatisfy (WCT9.searchTop index v sib pk fuel c) PubGood := by
  intro fuel
  induction fuel with
  | zero => intro c; exact allQ_pure _
  | succ fuel ih =>
      intro c
      unfold WCT9.searchTop
      exact allQ_bind (pubGood_topNode _ _ _) fun _ => allQ_ite _ (allQ_pure _) (ih _)
theorem pubGood_expandN (m : Message) (pk : Digest) (σ : WCT9.Signature) :
    AllQueriesSatisfy (expandN m pk σ) PubGood := by
  unfold expandN WCT9.expandS
  refine allQ_bind (pubGood_digestSearch _ _ _ _) fun r => ?_
  rcases r with _ | ⟨c, N⟩
  · exact allQ_pure _
  refine allQ_bind (pubGood_recoverFts _ _ _) fun root => ?_
  refine allQ_bind (pubGood_expandLayersT _ _ _ _ _) fun r => ?_
  rcases r with _ | ⟨v, root', cs⟩
  · exact allQ_pure _
  refine allQ_ite _ (allQ_pure _) (allQ_bind (pubGood_searchTop _ _ _ _ _ _) fun r => ?_)
  rcases r with _ | c <;> exact allQ_pure _
theorem pubGood_expandB (m : Message) (pk : Digest) (σ : WCT9.Signature) :
    AllQueriesSatisfy (expandB m pk σ) PubGood := allQ_map _ (pubGood_expandN m pk σ)
theorem hashOnly_verifyP (m : Message) (pk : Digest) (w : WBytes) : AllQueriesSatisfy (verifyP m pk w) isHash :=
  allQ_mono (pubGood_verifyP m pk w) fun _ h => h.hashGood.1
theorem hashOnly_expandN (m : Message) (pk : Digest) (σ : WCT9.Signature) :
    AllQueriesSatisfy (expandN m pk σ) isHash :=
  allQ_mono (pubGood_expandN m pk σ) fun _ h => h.hashGood.1
theorem hashOnly_expandB (m : Message) (pk : Digest) (σ : WCT9.Signature) :
    AllQueriesSatisfy (expandB m pk σ) isHash :=
  allQ_mono (pubGood_expandB m pk σ) fun _ h => h.hashGood.1
theorem publicOnly_verifyP (m : Message) (pk : Digest) (w : WBytes) : AllQueriesSatisfy (verifyP m pk w) isPublic :=
  allQ_mono (pubGood_verifyP m pk w) fun _ h => h.1
theorem publicOnly_expandN (m : Message) (pk : Digest) (σ : WCT9.Signature) :
    AllQueriesSatisfy (expandN m pk σ) isPublic := allQ_mono (pubGood_expandN m pk σ) fun _ h => h.1
theorem publicOnly_expandB (m : Message) (pk : Digest) (σ : WCT9.Signature) :
    AllQueriesSatisfy (expandB m pk σ) isPublic := allQ_mono (pubGood_expandB m pk σ) fun _ h => h.1
theorem goodQ_verifyP (m : Message) (pk : Digest) (w : WBytes) :
    AllQueriesSatisfy (verifyP m pk w) Cost.GoodQuery := allQ_mono (pubGood_verifyP m pk w) fun _ h => h.2
theorem goodQ_expandN (m : Message) (pk : Digest) (σ : WCT9.Signature) :
    AllQueriesSatisfy (expandN m pk σ) Cost.GoodQuery := allQ_mono (pubGood_expandN m pk σ) fun _ h => h.2
theorem goodQ_expandB (m : Message) (pk : Digest) (σ : WCT9.Signature) :
    AllQueriesSatisfy (expandB m pk σ) Cost.GoodQuery := allQ_mono (pubGood_expandB m pk σ) fun _ h => h.2
theorem hashOnly_honestProgramB (hk : AllQueriesSatisfy WCT9.Rev3.keygen isHash)
    (hs : ∀ c m, AllQueriesSatisfy (WCT9.Rev3.sign c m) isHash) (m : Message) :
    AllQueriesSatisfy (honestProgramB m) isHash := by
  unfold honestProgramB
  apply allQ_bind hk
  intro keys
  apply allQ_bind (hs _ _)
  intro sig
  rcases sig with _ | sig
  · exact allQ_pure _
  apply allQ_bind (hashOnly_expandB _ _ _)
  intro wb
  rcases wb with _ | wb
  · exact allQ_pure _
  exact hashOnly_verifyP _ _ _
end ClaudeWCT.W9.T3M

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security ClaudeWCT.WCT9
open SigGolfCandidate.T3M (isPublic allQ_bind allQ_pure allQ_map allQ_mapM allQ_foldlM allQ_ite allQ_mono)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
abbrev Only {α : Type} (p : M α) := AllQueriesSatisfy p isPublic

theorem public_pure {α : Type} (a : α) : Only (pure a) := allQ_pure _
theorem public_bind {α β : Type} {p : M α} {f : α→M β} (hp : Only p) (hf : ∀a,Only (f a)) : Only (p >>= f) := allQ_bind hp hf
theorem public_map {α β : Type} (f : α→β) {p : M α} (hp : Only p) : Only (f <$> p) := allQ_map _ hp
theorem public_mapM {α β : Type} (f : α→M β) (xs : List α) (h : ∀a,Only (f a)) : Only (xs.mapM f) := allQ_mapM _ _ h
theorem public_foldlM {α β : Type} (f : α→β→M α) (xs : List β) (h : ∀a b,Only (f a b)) (a : α) : Only (xs.foldlM f a) := allQ_foldlM _ _ h _
theorem public_publicHash (input : HashInput) : Only (publicHash input) := SourceQueries.publicHash_allowed _ (fun _=>trivial) _
theorem public_shortHash (input : HashInput) : Only (shortHash input) := SourceQueries.shortHash_allowed _ (fun _=>trivial) _
theorem public_projHash (high : Bool) (input : HashInput) : Only (projHash high input) :=
  SourceQueries.projHash_allowed _ (fun _=>trivial) _ _
theorem public_chain (index coord child t start count : Nat) (v : Digest) : Only (ClaudeWCT.WCT9.chain index coord child t start count v) :=
  allQ_mono (ClaudeWCT.W9.T3M.pubGood_chain ..) fun _ h=>h.1
theorem public_leafHashP (index coord child : Nat) (pad : Digest) (ends : List Digest) : Only (ClaudeWCT.WCT9.leafHashP index coord child pad ends) :=
  allQ_mono (ClaudeWCT.W9.T3M.pubGood_leafHashP ..) fun _ h=>h.1
theorem public_wctNodeHash (coord index heap : Nat) (left right : Digest) : Only (wctNodeHash coord index heap left right) :=
  allQ_mono (ClaudeWCT.W9.T3M.pubGood_wctNodeHash ..) fun _ h=>h.1
theorem public_leafHashH (heap index coord child : Nat) (pad : Digest) (ends : List Digest) :
    Only (ClaudeWCT.WCT9.leafHashH heap index coord child pad ends) :=
  allQ_mono (ClaudeWCT.W9.T3M.pubGood_leafHashH ..) fun _ h=>h.1
theorem public_wctNodeHashH (coord index heap : Nat) (left right : Digest) :
    Only (wctNodeHashH coord index heap left right) :=
  allQ_mono (ClaudeWCT.W9.T3M.pubGood_wctNodeHashH ..) fun _ h=>h.1
theorem public_encodingHash (lay : Layer) (input : HashInput) : Only (encodingHash lay input) :=
  (allQueries_encodingHash_iff _ _ _).mpr (public_shortHash _)
theorem public_topFold (sig : ClaudeWCT.WCT9.Signature) (index : Nat) (digits : List Nat) : Only (topFold sig index digits) :=
  allQ_mono (ClaudeWCT.W9.T3M.pubGood_topFold ..) fun _ h=>h.1
theorem public_topFoldN (sig : ClaudeWCT.WCT9.Signature) (index : Nat) (digits : List Nat) : Only (topFoldN sig index digits) :=
  allQ_mono (ClaudeWCT.W9.T3M.pubGood_topFoldN ..) fun _ h=>h.1
theorem public_topNode (index : Nat) (value other : Digest) : Only (topNode index value other) :=
  allQ_mono (ClaudeWCT.W9.T3M.pubGood_topNode ..) fun _ h=>h.1
theorem public_recoverLayerPair (sig : ClaudeWCT.WCT9.Signature) (index : Nat) (lay : Layer) (digits : List Nat) : Only (recoverLayerPair sig index lay digits) :=
  allQ_mono (ClaudeWCT.W9.T3M.pubGood_recoverLayerPair ..) fun _ h=>h.1
theorem public_digest (rho : Digest) (message : Message) (counter : BitVec 32) : Only (digest rho message counter) := public_publicHash _
theorem public_searchTop (index : Nat) (value sibling pk : Digest) (fuel counter : Nat) : Only (searchTop index value sibling pk fuel counter) :=
  allQ_mono (ClaudeWCT.W9.T3M.pubGood_searchTop ..) fun _ h=>h.1
theorem public_sharedOuterHash (coord index heap : Nat) (left right : Digest) :
    Only (sharedOuterHash coord index heap left right) := by
  unfold sharedOuterHash
  split
  · exact public_shortHash _
  · unfold highHash
    exact public_bind (public_publicHash _) fun _ => public_pure _
theorem public_sharedNode (first : Bool) (coord index heap : Nat)
    (pads : Nat → PairRoot) (left right : Digest) :
    Only (sharedNode first coord index heap pads left right) := by
  unfold sharedNode
  split
  · exact public_sharedOuterHash _ _ _ _ _
  · split
    · split
      · unfold highHash
        exact public_bind (public_publicHash _) fun _ => public_pure _
      · exact public_shortHash _
    · exact public_wctNodeHashH _ _ _ _ _
theorem public_recoverSharedInner (first : Bool) (index coord : Nat) (selected : Child)
    (word : Rank) (values : Fin 6 → Digest) (path : Nat → Digest) (prev : PairRoot) :
    Only (recoverSharedInner first index coord selected word values path prev) := by
  unfold recoverSharedInner
  refine public_bind (public_mapM _ _ (fun _ => public_chain _ _ _ _ _ _ _)) fun _ => ?_
  refine public_bind (public_leafHashH _ _ _ _ _ _) fun _ => ?_
  exact public_foldlM _ _ (fun _ _ => public_sharedNode _ _ _ _ _ _ _) _
theorem public_recoverPair (index pair : Nat) (s : Selection) (aWord bWord : Rank)
    (opened : PairOpening) (prev : PairRoot) : Only (recoverPair index pair s aWord bWord opened prev) := by
  unfold recoverPair
  refine public_bind (public_recoverSharedInner _ _ _ _ _ _ _ _) fun _ => ?_
  refine public_bind (public_recoverSharedInner _ _ _ _ _ _ _ _) fun _ => ?_
  exact public_bind (public_sharedOuterHash _ _ _ _ _) fun _ => public_pure _
theorem public_recoverSingleton (index : Nat) (selected : Child) (word : Rank)
    (opened : SingletonOpening) (prev : PairRoot) : Only (recoverSingleton index selected word opened prev) := by
  unfold recoverSingleton
  refine public_bind (public_recoverSharedInner _ _ _ _ _ _ _ _) fun _ => ?_
  exact public_bind (public_sharedOuterHash _ _ _ _ _) fun _ => public_pure _
theorem public_recoverForest (index : Nat) (selected : ForestSelection) (words : ForestWords)
    (opened : ForestOpening) : Only (recoverForest index selected words opened) := by
  unfold recoverForest
  exact public_bind (public_foldlM _ _ (fun _ _ => public_recoverPair _ _ _ _ _ _ _) _) fun _ =>
    public_recoverSingleton _ _ _ _ _
theorem public_layerCounterSearchAt (lay : Layer) (floor tree leaf : Nat)
    (msg : LayerMsg) (counter fuel : Nat) :
    Only (CanonicalPolicy.layerCounterSearchAt lay floor tree leaf msg counter fuel) := by
  induction fuel generalizing counter with
  | zero => unfold CanonicalPolicy.layerCounterSearchAt; exact public_pure _
  | succ fuel ih =>
    unfold CanonicalPolicy.layerCounterSearchAt
    refine public_bind (public_publicHash _) fun result => ?_
    split
    · exact ih _
    · exact public_pure _
theorem public_recoverHintedLayers (sig : Signature) (index : Nat) (other : Digest)
    (n : Nat) (msg : LayerMsg) : Only (recoverHintedLayers sig index other n msg) := by
  induction n generalizing msg with
  | zero => unfold recoverHintedLayers; exact public_pure _
  | succ n ih =>
    unfold recoverHintedLayers
    refine public_bind (public_layerCounterSearchAt _ _ _ _ _ _ _) fun result => ?_
    rcases result with _ | ⟨counter,digits,low⟩
    · exact public_pure _
    · dsimp only
      split
      · exact public_bind (public_topFoldN _ _ _) fun p => by
          rcases p with ⟨_, _⟩
          exact public_bind (public_topNode _ _ _) fun _ => public_pure _
      · refine public_bind (public_recoverLayerPair _ _ _ _) fun pair => ?_
        refine public_bind (ih _) fun previous => ?_
        cases previous <;> exact public_pure _
theorem public_sharedDigestSearch (rho : Digest) (message : Message) (counter fuel : Nat) :
    Only (sharedDigestSearch rho message counter fuel) := by
  induction fuel generalizing counter with
  | zero => unfold sharedDigestSearch; exact public_pure _
  | succ fuel ih =>
    unfold sharedDigestSearch
    refine public_bind (public_digest _ _ _) fun output => ?_
    split
    · exact public_pure _
    · exact ih _

end SigGolfCandidate.Research.SharedForest
namespace ClaudeWCT.W9.T3M.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M (isPublic allQ_bind allQ_pure allQ_map allQ_mapM allQ_foldlM allQ_ite allQ_mono)
open SigGolfCandidate.Research.SharedForest
open W9Machine
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem publicOnly_expandN (message : Message) (pk : Digest) (sig : SigGolfCandidate.Research.SharedForest.Signature) : Only (expandN message pk sig) := by
  unfold expandN
  split
  · exact allQ_pure _
  · refine allQ_bind (public_sharedDigestSearch _ _ _ _) fun found=>?_
    rcases found with _|⟨counter,output⟩
    · exact allQ_pure _
    · refine allQ_bind (public_recoverForest _ _ _ _) fun forest=>?_
      refine allQ_bind (public_recoverHintedLayers _ _ _ _ _) fun layers=>?_
      cases layers
      · exact allQ_pure _
      · dsimp only
        split
        · exact allQ_pure _
        · split
          · exact allQ_pure _
          · refine allQ_bind (public_searchTop _ _ _ _ _ _) fun found=>?_
            cases found <;> exact allQ_pure _

theorem publicOnly_expandB (message : Message) (pk : Digest) (sig : SigGolfCandidate.Research.SharedForest.Signature) : Only (expandB message pk sig) :=
  allQ_map _ (publicOnly_expandN ..)

theorem publicOnly_coordinate (w : WBytes) (index : Nat) (k : Fin 9) (raw : Fin 128) (rank : Fin 666) (prev : Digest×Digest) :
    Only (SharedV3.coordinate w index k raw rank prev) := by
  unfold SharedV3.coordinate
  refine allQ_bind ?_ fun ends=>?_
  · unfold V3.chainProgram
    exact allQ_mapM _ _ fun _=>allQ_foldlM _ _ (fun _ _=>public_projHash _ _) _
  · refine allQ_bind ?_ fun _=>allQ_pure _
    unfold SharedV3.childN
    have hsel : ∀ hi input, Only (SharedV3.hashSel hi input) := by
      intro hi input
      unfold SharedV3.hashSel
      split
      · unfold V3.hashHi
        exact allQ_bind (public_publicHash _) fun _=>allQ_pure _
      · exact public_shortHash _
    refine allQ_bind (hsel _ _) fun _=>?_
    refine allQ_bind (allQ_foldlM _ _ (fun _ _=>hsel _ _) _) fun _=>?_
    split
    · exact hsel _ _
    · unfold V3.hashHi
      exact allQ_bind (public_publicHash _) fun _=>allQ_pure _

theorem publicOnly_ftsStep (w : WBytes) (output : HashOutput) (state : Option (List (Digest×Digest))) (coord : Fin 9) :
    Only (ftsStep w output state coord) := by
  unfold ftsStep
  cases state
  · exact allQ_pure _
  · exact allQ_ite _ (allQ_pure _) (allQ_bind (publicOnly_coordinate ..) fun _=>allQ_pure _)

theorem publicOnly_ftsP (w : WBytes) (output : HashOutput) : Only (ftsP w output) := by
  unfold ftsP
  split
  · exact allQ_pure _
  · refine allQ_bind (allQ_foldlM _ _ (fun state coord=>publicOnly_ftsStep w output state coord) _) fun found=>?_
    cases found <;> exact allQ_pure _

theorem publicOnly_layersCanonicalBC (w : WBytes) (index : Nat) : ∀n msg,Only (layersCanonicalBC w index n msg) := by
  intro n
  induction n with
  | zero=>intro msg;exact allQ_pure _
  | succ n ih=>
    intro msg
    unfold layersCanonicalBC
    refine allQ_ite _ (allQ_pure _) (allQ_bind (allQ_mono (pubGood_layerEncodingInputP ..) (fun _ h=>h.1)) fun answer=>?_)
    refine allQ_ite _ (allQ_mono (pubGood_topLayerP ..) (fun _ h=>h.1)) ?_
    rcases ClaudeWCT.WCT9.CanonicalPolicy.decode (Fin.ofNat 4 n) answer with _|digits
    · exact allQ_pure _
    · refine allQ_bind (allQ_mono (pubGood_layerGuardedPairP ..) (fun _ h=>h.1)) fun pair=>?_
      cases pair
      · exact allQ_pure _
      · exact ih _

theorem publicOnly_verifyP (message : Message) (pk : Digest) (w : WBytes) : Only (verifyP message pk w) := by
  unfold verifyP
  refine allQ_bind ?_ fun output=>?_
  · unfold digestP
    exact allQ_ite _ (allQ_pure _) (allQ_map _ (public_digest ..))
  · cases output
    · exact allQ_pure _
    · refine allQ_bind (publicOnly_ftsP ..) fun top=>?_
      cases top
      · exact allQ_pure _
      · refine allQ_bind (publicOnly_layersCanonicalBC ..) fun root=>?_
        cases root <;> exact allQ_pure _
end ClaudeWCT.W9.T3M.Paired

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security ClaudeWCT.WCT9
open SigGolfCandidate.T3M (isPublic allQ_bind allQ_pure allQ_map allQ_mapM allQ_foldlM allQ_ite allQ_mono)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
abbrev Good {α : Type} (p : M α) := AllQueriesSatisfy p Cost.GoodQuery

theorem good_pure {α : Type} (a : α) : Good (pure a) := allQ_pure _
theorem good_bind {α β : Type} {p : M α} {f : α→M β} (hp : Good p) (hf : ∀a,Good (f a)) : Good (p >>= f) := allQ_bind hp hf
theorem good_map {α β : Type} (f : α→β) {p : M α} (hp : Good p) : Good (f <$> p) := allQ_map _ hp
theorem good_mapM {α β : Type} (f : α→M β) (xs : List α) (h : ∀a,Good (f a)) : Good (xs.mapM f) := allQ_mapM _ _ h
theorem good_foldlM {α β : Type} (f : α→β→M α) (xs : List β) (h : ∀a b,Good (f a b)) (a : α) : Good (xs.foldlM f a) := allQ_foldlM _ _ h _
theorem good_publicHash (input : HashInput) (h : 0 < input.length) : Good (publicHash input) :=
  allQ_mono (SigGolfCandidate.T3M.pubGood_publicHash input h) fun _ h=>h.2
theorem good_shortHash (input : HashInput) (h : 0 < input.length) : Good (shortHash input) :=
  allQ_mono (SigGolfCandidate.T3M.pubGood_shortHash input h) fun _ h=>h.2
theorem good_projHash (high : Bool) (input : HashInput) (h : 0 < input.length) : Good (projHash high input) :=
  allQ_mono (SigGolfCandidate.T3M.pubGood_projHash high input h) fun _ h=>h.2
theorem good_chain (index coord child t start count : Nat) (v : Digest) : Good (ClaudeWCT.WCT9.chain index coord child t start count v) :=
  allQ_mono (ClaudeWCT.W9.T3M.pubGood_chain ..) fun _ h=>h.2
theorem good_leafHashP (index coord child : Nat) (pad : Digest) (ends : List Digest) : Good (ClaudeWCT.WCT9.leafHashP index coord child pad ends) :=
  allQ_mono (ClaudeWCT.W9.T3M.pubGood_leafHashP ..) fun _ h=>h.2
theorem good_wctNodeHash (coord index heap : Nat) (left right : Digest) : Good (wctNodeHash coord index heap left right) :=
  allQ_mono (ClaudeWCT.W9.T3M.pubGood_wctNodeHash ..) fun _ h=>h.2
theorem good_leafHashH (heap index coord child : Nat) (pad : Digest) (ends : List Digest) :
    Good (ClaudeWCT.WCT9.leafHashH heap index coord child pad ends) :=
  allQ_mono (ClaudeWCT.W9.T3M.pubGood_leafHashH ..) fun _ h=>h.2
theorem good_wctNodeHashH (coord index heap : Nat) (left right : Digest) :
    Good (wctNodeHashH coord index heap left right) :=
  allQ_mono (ClaudeWCT.W9.T3M.pubGood_wctNodeHashH ..) fun _ h=>h.2
theorem good_layerEncodingHash (lay : Layer) (tree leaf : Nat) (msg : LayerMsg) (counter : BitVec 32) :
    Good (encodingHash lay (layerEncodingInput lay tree leaf msg counter)) :=
  allQ_mono (ClaudeWCT.W9.T3M.pubGood_layerEncodingInput ..) fun _ h=>h.2
theorem good_topFold (sig : ClaudeWCT.WCT9.Signature) (index : Nat) (digits : List Nat) : Good (topFold sig index digits) :=
  allQ_mono (ClaudeWCT.W9.T3M.pubGood_topFold ..) fun _ h=>h.2
theorem good_topFoldN (sig : ClaudeWCT.WCT9.Signature) (index : Nat) (digits : List Nat) : Good (topFoldN sig index digits) :=
  allQ_mono (ClaudeWCT.W9.T3M.pubGood_topFoldN ..) fun _ h=>h.2
theorem good_topNode (index : Nat) (value other : Digest) : Good (topNode index value other) :=
  allQ_mono (ClaudeWCT.W9.T3M.pubGood_topNode ..) fun _ h=>h.2
theorem good_recoverLayerPair (sig : ClaudeWCT.WCT9.Signature) (index : Nat) (lay : Layer) (digits : List Nat) : Good (recoverLayerPair sig index lay digits) :=
  allQ_mono (ClaudeWCT.W9.T3M.pubGood_recoverLayerPair ..) fun _ h=>h.2
theorem good_digest (rho : Digest) (message : Message) (counter : BitVec 32) : Good (digest rho message counter) := allQ_mono (SigGolfCandidate.T3M.pubGood_digest ..) fun _ h=>h.2
theorem good_searchTop (index : Nat) (value sibling pk : Digest) (fuel counter : Nat) : Good (searchTop index value sibling pk fuel counter) :=
  allQ_mono (ClaudeWCT.W9.T3M.pubGood_searchTop ..) fun _ h=>h.2
theorem good_sharedOuterHash (coord index heap : Nat) (left right : Digest) :
    Good (sharedOuterHash coord index heap left right) := by
  unfold sharedOuterHash
  split
  · exact good_shortHash _ (by simp [wctTopInput_length])
  · unfold highHash
    exact good_bind (good_publicHash _ (by simp [wctTopInput_length])) fun _ => good_pure _
theorem good_sharedNode (first : Bool) (coord index heap : Nat)
    (pads : Nat → PairRoot) (left right : Digest) :
    Good (sharedNode first coord index heap pads left right) := by
  unfold sharedNode
  split
  · exact good_sharedOuterHash _ _ _ _ _
  · split
    · split
      · unfold highHash
        exact good_bind (good_publicHash _ (by simp [wctTopInput_length])) fun _ => good_pure _
      · exact good_shortHash _ (by simp [wctTopInput_length])
    · exact good_wctNodeHashH _ _ _ _ _
theorem good_recoverSharedInner (first : Bool) (index coord : Nat) (selected : Child)
    (word : Rank) (values : Fin 6 → Digest) (path : Nat → Digest) (prev : PairRoot) :
    Good (recoverSharedInner first index coord selected word values path prev) := by
  unfold recoverSharedInner
  refine good_bind (good_mapM _ _ (fun _ => good_chain _ _ _ _ _ _ _)) fun _ => ?_
  refine good_bind (good_leafHashH _ _ _ _ _ _) fun _ => ?_
  exact good_foldlM _ _ (fun _ _ => good_sharedNode _ _ _ _ _ _ _) _
theorem good_recoverPair (index pair : Nat) (s : Selection) (aWord bWord : Rank)
    (opened : PairOpening) (prev : PairRoot) : Good (recoverPair index pair s aWord bWord opened prev) := by
  unfold recoverPair
  refine good_bind (good_recoverSharedInner _ _ _ _ _ _ _ _) fun _ => ?_
  refine good_bind (good_recoverSharedInner _ _ _ _ _ _ _ _) fun _ => ?_
  exact good_bind (good_sharedOuterHash _ _ _ _ _) fun _ => good_pure _
theorem good_recoverSingleton (index : Nat) (selected : Child) (word : Rank)
    (opened : SingletonOpening) (prev : PairRoot) : Good (recoverSingleton index selected word opened prev) := by
  unfold recoverSingleton
  refine good_bind (good_recoverSharedInner _ _ _ _ _ _ _ _) fun _ => ?_
  exact good_bind (good_sharedOuterHash _ _ _ _ _) fun _ => good_pure _
theorem good_recoverForest (index : Nat) (selected : ForestSelection) (words : ForestWords)
    (opened : ForestOpening) : Good (recoverForest index selected words opened) := by
  unfold recoverForest
  exact good_bind (good_foldlM _ _ (fun _ _ => good_recoverPair _ _ _ _ _ _ _) _) fun _ =>
    good_recoverSingleton _ _ _ _ _
theorem good_layerCounterSearchAt (lay : Layer) (floor tree leaf : Nat)
    (msg : LayerMsg) (counter fuel : Nat) :
    Good (CanonicalPolicy.layerCounterSearchAt lay floor tree leaf msg counter fuel) := by
  induction fuel generalizing counter with
  | zero => unfold CanonicalPolicy.layerCounterSearchAt; exact good_pure _
  | succ fuel ih =>
    unfold CanonicalPolicy.layerCounterSearchAt
    refine good_bind (good_layerEncodingHash _ _ _ _ _) fun result => ?_
    split
    · exact ih _
    · exact good_pure _
theorem good_recoverHintedLayers (sig : Signature) (index : Nat) (other : Digest)
    (n : Nat) (msg : LayerMsg) : Good (recoverHintedLayers sig index other n msg) := by
  induction n generalizing msg with
  | zero => unfold recoverHintedLayers; exact good_pure _
  | succ n ih =>
    unfold recoverHintedLayers
    refine good_bind (good_layerCounterSearchAt _ _ _ _ _ _ _) fun result => ?_
    rcases result with _ | ⟨counter,digits⟩
    · exact good_pure _
    · dsimp only
      split
      · exact good_bind (good_topFoldN _ _ _) fun p => by
          rcases p with ⟨_, _⟩
          exact good_bind (good_topNode _ _ _) fun _ => good_pure _
      · refine good_bind (good_recoverLayerPair _ _ _ _) fun pair => ?_
        refine good_bind (ih _) fun previous => ?_
        cases previous <;> exact good_pure _
theorem good_sharedDigestSearch (rho : Digest) (message : Message) (counter fuel : Nat) :
    Good (sharedDigestSearch rho message counter fuel) := by
  induction fuel generalizing counter with
  | zero => unfold sharedDigestSearch; exact good_pure _
  | succ fuel ih =>
    unfold sharedDigestSearch
    refine good_bind (good_digest _ _ _) fun output => ?_
    split
    · exact good_pure _
    · exact ih _

end SigGolfCandidate.Research.SharedForest

namespace ClaudeWCT.W9.T3M.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M (isPublic allQ_bind allQ_pure allQ_map allQ_mapM allQ_foldlM allQ_ite allQ_mono)
open SigGolfCandidate.Research.SharedForest
open W9Machine
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem goodQ_expandN (message : Message) (pk : Digest) (sig : SigGolfCandidate.Research.SharedForest.Signature) : Good (expandN message pk sig) := by
  unfold expandN
  split
  · exact allQ_pure _
  · refine allQ_bind (good_sharedDigestSearch _ _ _ _) fun found=>?_
    rcases found with _|⟨counter,output⟩
    · exact allQ_pure _
    · refine allQ_bind (good_recoverForest _ _ _ _) fun forest=>?_
      refine allQ_bind (good_recoverHintedLayers _ _ _ _ _) fun layers=>?_
      cases layers
      · exact allQ_pure _
      · dsimp only
        split
        · exact allQ_pure _
        · split
          · exact allQ_pure _
          · refine allQ_bind (good_searchTop _ _ _ _ _ _) fun found=>?_
            cases found <;> exact allQ_pure _

theorem goodQ_expandB (message : Message) (pk : Digest) (sig : SigGolfCandidate.Research.SharedForest.Signature) : Good (expandB message pk sig) :=
  allQ_map _ (goodQ_expandN ..)

theorem goodQ_coordinate (w : WBytes) (index : Nat) (k : Fin 9) (raw : Fin 128) (rank : Fin 666) (prev : Digest×Digest) :
    Good (SharedV3.coordinate w index k raw rank prev) := by
  unfold SharedV3.coordinate
  refine allQ_bind ?_ fun ends=>?_
  · unfold V3.chainProgram
    exact allQ_mapM _ _ fun _=>allQ_foldlM _ _ (fun _ _=>good_projHash _ _ (by
      unfold V3.chainInput; split <;> simp [SphincsSecurity.bytesLE_length])) _
  · refine allQ_bind ?_ fun _=>allQ_pure _
    unfold SharedV3.childN
    have hsel : ∀ hi input, 0 < input.length → Good (SharedV3.hashSel hi input) := by
      intro hi input hpos
      unfold SharedV3.hashSel
      split
      · unfold V3.hashHi
        exact allQ_bind (good_publicHash _ hpos) fun _=>allQ_pure _
      · exact good_shortHash _ hpos
    refine allQ_bind (hsel _ _ (by simp [V3.chainInput,V3.leafInput,SharedV3.childInput,V3.nodeInput,SphincsSecurity.bytesLE_length])) fun _=>?_
    refine allQ_bind (allQ_foldlM _ _ (fun _ _=>hsel _ _ (by simp [V3.chainInput,V3.leafInput,SharedV3.childInput,V3.nodeInput,SphincsSecurity.bytesLE_length])) _) fun _=>?_
    split
    · exact hsel _ _ (by simp [SharedV3.childInput,V3.nodeInput,SphincsSecurity.bytesLE_length])
    · unfold V3.hashHi
      exact allQ_bind (good_publicHash _ (by simp [V3.chainInput,V3.leafInput,SharedV3.childInput,V3.nodeInput,SphincsSecurity.bytesLE_length])) fun _=>allQ_pure _

theorem goodQ_ftsStep (w : WBytes) (output : HashOutput) (state : Option (List (Digest×Digest))) (coord : Fin 9) :
    Good (ftsStep w output state coord) := by
  unfold ftsStep
  cases state
  · exact allQ_pure _
  · exact allQ_ite _ (allQ_pure _) (allQ_bind (goodQ_coordinate ..) fun _=>allQ_pure _)

theorem goodQ_ftsP (w : WBytes) (output : HashOutput) : Good (ftsP w output) := by
  unfold ftsP
  split
  · exact allQ_pure _
  · refine allQ_bind (allQ_foldlM _ _ (fun state coord=>goodQ_ftsStep w output state coord) _) fun found=>?_
    cases found <;> exact allQ_pure _

theorem goodQ_layersCanonicalBC (w : WBytes) (index : Nat) : ∀n msg,Good (layersCanonicalBC w index n msg) := by
  intro n
  induction n with
  | zero=>intro msg;exact allQ_pure _
  | succ n ih=>
    intro msg
    unfold layersCanonicalBC
    refine allQ_ite _ (allQ_pure _) (allQ_bind (allQ_mono (pubGood_layerEncodingInputP ..) (fun _ h=>h.2)) fun answer=>?_)
    refine allQ_ite _ (allQ_mono (pubGood_topLayerP ..) (fun _ h=>h.2)) ?_
    rcases ClaudeWCT.WCT9.CanonicalPolicy.decode (Fin.ofNat 4 n) answer with _|digits
    · exact allQ_pure _
    · refine allQ_bind (allQ_mono (pubGood_layerGuardedPairP ..) (fun _ h=>h.2)) fun pair=>?_
      cases pair
      · exact allQ_pure _
      · exact ih _

theorem goodQ_verifyP (message : Message) (pk : Digest) (w : WBytes) : Good (verifyP message pk w) := by
  unfold verifyP
  refine allQ_bind ?_ fun output=>?_
  · unfold digestP
    exact allQ_ite _ (allQ_pure _) (allQ_map _ (good_digest ..))
  · cases output
    · exact allQ_pure _
    · refine allQ_bind (goodQ_ftsP ..) fun top=>?_
      cases top
      · exact allQ_pure _
      · refine allQ_bind (goodQ_layersCanonicalBC ..) fun root=>?_
        cases root <;> exact allQ_pure _
end ClaudeWCT.W9.T3M.Paired

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3M (allQ_mono allQ_ite)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem good_privateHash (coord : Coordinate) : Good (privateHash coord) :=
  (allQueriesSatisfy_query_iff _ _).mpr trivial

theorem good_privatePair (tag lay tree position index : Nat) : Good (privatePair tag lay tree position index) :=
  good_bind (good_privateHash _) fun _=>good_pure _

theorem good_topCoefs (leaf : Nat) : Good (topCoefs leaf) := by
  unfold topCoefs topPairsFrom topSeedPair
  exact good_bind (good_foldlM _ _ (fun _ _=>good_bind (good_privatePair ..) fun _=>good_pure _) _) fun _=>good_pure _

theorem good_buildLeafTop (leaf : Nat) (digits : List Nat) : Good (buildLeafTop leaf digits true) := by
  unfold buildLeafTop buildLeafTopC
  simp only [↓reduceIte]
  refine good_bind (good_topCoefs _) fun _=>?_
  refine good_bind (good_foldlM _ _ (fun _ _=>good_bind
    (allQ_mono (SigGolfCandidate.T3M.pubGood_topChain ..) fun _ h=>h.2) fun _=>good_pure _) _) fun _=>good_pure _

theorem good_topPath (cache : SigGolfCandidate.T3.Cache) (leaf : Nat) : Good (topPath cache leaf) := by
  unfold topPath mask pairedMask
  exact good_mapM _ _ fun _=>good_bind (good_bind (good_privatePair ..) fun _=>good_pure _) fun _=>good_pure _

theorem good_signTop (cache : SigGolfCandidate.T3.Cache) (leaf : Nat) (digits : List Nat) : Good (signTop cache leaf digits) :=
  good_bind (good_buildLeafTop ..) fun _=>good_bind (good_topPath ..) fun _=>good_pure _

theorem good_searchPreparedLayers (cache : SigGolfCandidate.T3.Cache) (index : Nat) (prepared : PreparedRoots) (forest : PairRoot) :
    Good (searchPreparedLayers cache index prepared forest) := by
  unfold searchPreparedLayers
  refine good_bind (good_layerCounterSearchAt ..) fun found=>?_
  rcases found with _|⟨counter0,digits0⟩
  · exact good_pure _
  · dsimp only
    refine allQ_ite _ (good_pure _) ?_
    refine good_bind (good_layerCounterSearchAt ..) fun found=>?_
    rcases found with _|⟨counter1,digits1⟩
    · exact good_pure _
    · dsimp only
      refine allQ_ite _ (good_pure _) ?_
      refine good_bind (good_layerCounterSearchAt ..) fun found=>?_
      rcases found with _|⟨counter2,digits2⟩
      · exact good_pure _
      · dsimp only
        refine allQ_ite _ (good_pure _) ?_
        refine good_bind (good_layerCounterSearchAt ..) fun found=>?_
        rcases found with _|⟨counter3,digits3⟩
        · exact good_pure _
        · exact good_bind (good_signTop ..) fun _=>good_pure _

theorem good_signFromOutput (cache : SigGolfCandidate.T3.Cache) (rho : Digest) (counter : BitVec 32) (output : HashOutput) :
    Good (signFromOutput cache rho counter output) := by
  unfold signFromOutput
  refine good_bind (allQueriesSatisfy_of_bound (bound_buildForest ..)) fun _=>?_
  refine good_bind (allQueriesSatisfy_of_bound (bound_prepareRoots ..)) fun _=>?_
  refine good_bind (good_searchPreparedLayers ..) fun found=>?_
  cases found <;> exact good_pure _

theorem good_signPayload (cache : SigGolfCandidate.T3.Cache) (message : Message) : Good (signPayload cache message) := by
  unfold signPayload privateNonce
  refine good_bind (good_bind (good_privateHash _) fun _=>good_pure _) fun _=>?_
  refine good_bind (good_sharedDigestSearch ..) fun found=>?_
  rcases found with _|⟨counter,output⟩
  · exact good_pure _
  · refine good_bind (good_signFromOutput ..) fun found=>?_
    cases found <;> exact good_pure _

theorem good_sign (cache : SigGolfCandidate.T3.Cache) (message : Message) : Good (sign cache message) := by
  unfold sign
  have hmac : Good (privateMac cache.region) := by
    unfold privateMac privateMacKey
    exact good_bind (good_bind (good_privateHash _) fun _=>good_bind (good_privateHash _) fun _=>good_pure _) fun _=>good_pure _
  refine good_bind hmac fun _=>?_
  exact allQ_ite _ (good_pure _) (good_signPayload ..)

theorem good_verifyLayers (w : SigGolfCandidate.Research.SharedForest.Witness) (index : Nat) :
    ∀n msg,Good (verifyLayers w index n msg) := by
  intro n
  induction n with
  | zero => intro msg;exact good_pure _
  | succ n ih =>
    intro msg
    unfold verifyLayers
    refine allQ_ite _ (good_pure _) (good_bind (good_layerEncodingHash ..) fun answer=>?_)
    refine allQ_ite _ (allQ_mono (ClaudeWCT.W9.T3M.pubGood_verifyTopN ..) fun _ h=>h.2) ?_
    rcases CanonicalPolicy.decode (Fin.ofNat 4 n) answer with _|digits
    · exact good_pure _
    · refine good_bind (allQ_mono (ClaudeWCT.W9.T3M.pubGood_recoverLayerPairGuard ..) fun _ h=>h.2) fun pair=>?_
      cases pair
      · exact good_pure _
      · exact ih _

theorem good_verify (message : Message) (pk : Digest) (w : SigGolfCandidate.Research.SharedForest.Witness) :
    Good (verify message pk w) := by
  unfold verify
  refine allQ_ite _ (good_pure _) (good_bind (good_digest ..) fun output=>?_)
  refine allQ_ite _ (good_pure _) (good_bind (good_recoverForest ..) fun forest=>?_)
  refine good_bind (good_verifyLayers ..) fun found=>?_
  cases found <;> exact good_pure _
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3

theorem good_expand (message : Message) (pk : Digest) (sig : SigGolfCandidate.Research.SharedForest.Signature) :
    Good (expand message pk sig) := by
  show Good (expandFill message pk (normTop sig))
  rw [←ClaudeWCT.W9.T3M.Paired.expandN_snd]
  exact good_map _ (ClaudeWCT.W9.T3M.Paired.goodQ_expandN ..)
end SigGolfCandidate.Research.SharedForest
end
-- ==== merged from ClaudeWCT_W9_T3M_Final_SecurityP ====
section

namespace ClaudeWCT.W9.T3M.Final
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 (M Spec Message Digest Cache keygen privateInput)
open SigGolfCandidate.T3.Security (Request forwardWorld)
open ClaudeWCT.W9.T3.Security (Signature Requests signingOracle)
open SphincsSecurity (OracleWorld romImpl sampleMasterSeed)
noncomputable local instance instDecidableEqSignature_securityP : DecidableEq Signature := Classical.decEq _
inductive ForgeryP where
  | witness (message : Message) (witness : WBytes)
  | signature (message : Message) (signature : Signature)
abbrev AdversaryP := Digest → Cache → OracleComp (OracleWorld + Requests) (Option ForgeryP)
noncomputable def checkForgeryP (publicKey : Digest) (log : QueryLog Requests) : ForgeryP → M Bool := by
  classical
  exact fun forgery => do
    match forgery with
    | .witness message wb =>
        let verified ← verifyP message publicKey wb
        pure (decide (¬∃ entry ∈ log, entry.1.message = message ∧ entry.2.isSome = true) && verified)
    | .signature message signature =>
        let wb ← expandB message publicKey signature
        let some wb := wb | return false
        let verified ← verifyP message publicKey wb
        pure (decide (¬∃ entry ∈ log, entry.1.message = message ∧
          entry.2.map ClaudeWCT.WCT9.proj = some (ClaudeWCT.WCT9.proj signature)) && verified)
noncomputable def gameP (adversary : AdversaryP) : M Bool := do
    let (publicKey, cache) ← keygen
    let (forgery, log) ← (simulateQ
      ((fun input => liftM (forwardWorld input) : QueryImpl OracleWorld (WriterT (QueryLog Requests) M)) +
        signingOracle) (adversary publicKey cache)).run
    let some forgery := forgery | return false
    let verified ← checkForgeryP publicKey log forgery
    pure (decide (log.length ≤ 2^32) && verified)
noncomputable def realExperimentP (adversary : AdversaryP) : ProbComp (Bool × Nat) :=
  sampleMasterSeed >>= fun secret =>
    (simulateQ romImpl (SphincsSecurity.countHashQueries
      (SigGolfCandidate.T3.Derivation.realize (privateInput secret) (gameP adversary)))).run' ∅
def SecurityP : Prop := ∀ (adversary : AdversaryP) (q : Nat), 1 ≤ q →
  Pr[fun result => result.1 = true ∧ result.2 ≤ q | realExperimentP adversary] ≤ (q : ℝ≥0∞) / 2 ^ 127
end ClaudeWCT.W9.T3M.Final

namespace ClaudeWCT.W9.T3M.Final.Paired
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 (M Spec Message Digest Cache keygen privateInput)
open SigGolfCandidate.T3.Security (Request forwardWorld)
open SigGolfCandidate.Research.SharedForest (Signature)
open SphincsSecurity (OracleWorld romImpl sampleMasterSeed)

abbrev Requests := Request →ₒ Option Signature

def signingOracle : QueryImpl Requests (WriterT (QueryLog Requests) M) :=
  QueryImpl.withLogging fun request => liftM
    (SigGolfCandidate.Research.SharedForest.sign request.cache request.message)

inductive ForgeryP where
  | witness (message : Message) (witness : WBytes)
  | signature (message : Message) (signature : Signature)

abbrev AdversaryP := Digest → Cache → OracleComp (OracleWorld + Requests) (Option ForgeryP)

/-- Strong novelty compares the complete5239-byte wire signature, including
its canonical policy hints and the112-bit serialized top sibling. -/
noncomputable def checkForgeryP (publicKey : Digest) (log : QueryLog Requests) : ForgeryP → M Bool := by
  classical
  exact fun forgery => do
    match forgery with
    | .witness message wb =>
        let verified ← ClaudeWCT.W9.T3M.Paired.verifyP message publicKey wb
        pure (decide (¬∃ entry ∈ log, entry.1.message = message ∧ entry.2.isSome = true) && verified)
    | .signature message signature =>
        let wb ← ClaudeWCT.W9.T3M.Paired.expandB message publicKey signature
        let some wb := wb | return false
        let verified ← ClaudeWCT.W9.T3M.Paired.verifyP message publicKey wb
        pure (decide (¬∃ entry ∈ log, entry.1.message = message ∧
          entry.2.map SharedCodec.sigBC = some (SharedCodec.sigBC signature)) && verified)

noncomputable def gameP (adversary : AdversaryP) : M Bool := do
  let (publicKey, cache) ← keygen
  let (forgery, log) ← (simulateQ
    ((fun input => liftM (forwardWorld input) : QueryImpl OracleWorld (WriterT (QueryLog Requests) M)) +
      signingOracle) (adversary publicKey cache)).run
  let some forgery := forgery | return false
  let verified ← checkForgeryP publicKey log forgery
  pure (decide (log.length ≤ 2^32) && verified)

noncomputable def realExperimentP (adversary : AdversaryP) : ProbComp (Bool × Nat) :=
  sampleMasterSeed >>= fun secret =>
    (simulateQ romImpl (SphincsSecurity.countHashQueries
      (SigGolfCandidate.T3.Derivation.realize (privateInput secret) (gameP adversary)))).run' ∅

def SecurityP : Prop := ∀ (adversary : AdversaryP) (q : Nat), 1 ≤ q →
  Pr[fun result => result.1 = true ∧ result.2 ≤ q | realExperimentP adversary] ≤ (q : ENNReal) / 2 ^ 127

end ClaudeWCT.W9.T3M.Final.Paired

namespace ClaudeWCT.W9.T3M.Final.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def Fresh (log : QueryLog Requests) : ForgeryP → Prop
  | .witness message _ => ¬∃ entry ∈ log, entry.1.message = message ∧ entry.2.isSome = true
  | .signature message sig => ¬∃ entry ∈ log, entry.1.message = message ∧
      entry.2.map SharedCodec.sigBC = some (SharedCodec.sigBC sig)

def WitnessOf (answers : Answers) (pk : Digest) : ForgeryP → Message → WBytes → Prop
  | .witness sourceMessage sourceWitness, message, witness =>
      sourceMessage = message ∧ sourceWitness = witness
  | .signature sourceMessage sig, message, witness =>
      sourceMessage = message ∧
        evalWithAnswerFn answers (ClaudeWCT.W9.T3M.Paired.expandB message pk sig) = some witness

theorem check_accepting (answers : Answers) (pk : Digest) (log : QueryLog Requests)
    (forgery : ForgeryP) (h : evalWithAnswerFn answers (checkForgeryP pk log forgery) = true) :
    Fresh log forgery ∧ ∃ message witness,
      WitnessOf answers pk forgery message witness ∧
      evalWithAnswerFn answers (ClaudeWCT.W9.T3M.Paired.verifyP message pk witness) = true ∧
      ∀ q ∈ queried answers (ClaudeWCT.W9.T3M.Paired.verifyP message pk witness),
        q ∈ queried answers (checkForgeryP pk log forgery) := by
  cases forgery with
  | witness message witness =>
      simp only [checkForgeryP, evalWithAnswerFn_bind, evalWithAnswerFn_pure, Bool.and_eq_true,
        decide_eq_true_eq] at h
      refine ⟨h.1, message, witness, ⟨rfl,rfl⟩, h.2, ?_⟩
      intro q hq
      simpa only [checkForgeryP, queried_bind, queried_pure, List.append_nil] using hq
  | signature message sig =>
      cases he : evalWithAnswerFn answers (ClaudeWCT.W9.T3M.Paired.expandB message pk sig) with
      | none => simp [checkForgeryP, evalWithAnswerFn_bind, he, evalWithAnswerFn_pure] at h
      | some witness =>
          simp only [checkForgeryP, evalWithAnswerFn_bind, he, evalWithAnswerFn_pure, Bool.and_eq_true,
            decide_eq_true_eq] at h
          refine ⟨h.1, message, witness, ⟨rfl, he⟩, h.2, ?_⟩
          intro q hq
          simp only [checkForgeryP, queried_bind, he, queried_pure, List.append_nil]
          exact List.mem_append_right _ hq
end ClaudeWCT.W9.T3M.Final.Paired
end
-- ==== merged from ClaudeWCT_W9_T3_BPORS ====
section

set_option linter.unusedSimpArgs false
section
namespace ClaudeWCT.W9.T3.Security.CountedPrivate
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _
theorem authenticatedSign_avoids (protectedMessage : Message) (published : SigGolfCandidate.T3.Cache)
    (request : Request) (hrequest : request.cache≠published ∨ request.message≠protectedMessage) :
    NonceFreshness.Avoids protectedMessage (FullGame.authenticatedSign published request) := by
  unfold FullGame.authenticatedSign
  apply NonceFreshness.avoids_bind protectedMessage
    (NonceFreshness.avoids_privateMac protectedMessage request.cache.region)
  intro tag
  split_ifs with hc
  · exact Signer.signPayload_avoids protectedMessage request.cache request.message
      (hrequest.resolve_left (not_not.mpr hc))
  · exact NonceFreshness.avoids_pure protectedMessage none
theorem authenticatedSign_hashOnly (published : SigGolfCandidate.T3.Cache) (request : Request) :
    SigGolfCandidate.T3.Security.SourceReplay.HashOnly (FullGame.authenticatedSign published request) := by
  unfold FullGame.authenticatedSign
  apply SourceQueries.bind_allowed SigGolfCandidate.T3.Security.SourceReplay.IsHash
    (SourceQueries.privateMac_allowed SigGolfCandidate.T3.Security.SourceReplay.IsHash (fun _ => trivial)
      request.cache.region)
  intro tag
  split_ifs
  · exact Signer.signPayload_hashOnly request.cache request.message
  · exact SourceQueries.pure_allowed _ _
end ClaudeWCT.W9.T3.Security.CountedPrivate
end
section
namespace ClaudeWCT.W9.T3.Security.MonitoredPrivate
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
abbrev Interaction := LazyPrivate.Interaction
noncomputable def interactionSource (published : SigGolfCandidate.T3.Cache) : QueryImpl Interaction M
  | .inl input => forwardWorld input
  | .inr request => FullGame.authenticatedSign published request
def Outcome (input : Interaction.Domain) : Type :=
  Interaction.Range input × SigGolfCandidate.T3.Security.MonitoredPrivate.State
noncomputable def interactionRecord (published : SigGolfCandidate.T3.Cache) (input : Interaction.Domain)
    (state : SigGolfCandidate.T3.Security.MonitoredPrivate.State) : PMF (Outcome input) :=
  liftM (MonitoredPrivate.run (interactionSource published input) state)
def response (input : Interaction.Domain) (result : Outcome input) : Interaction.Range input := result.1
def advance (input : Interaction.Domain) (_ : SigGolfCandidate.T3.Security.MonitoredPrivate.State)
    (result : Outcome input) : SigGolfCandidate.T3.Security.MonitoredPrivate.State := result.2
def label (input : Interaction.Domain) (_ : Outcome input) : DigestSampling.IndexBuckets := default
def active : Interaction.Domain → SigGolfCandidate.T3.Security.MonitoredPrivate.State → Bool
  | .inl _, _ => false
  | .inr _, _ => true
noncomputable def proposalModel (published : SigGolfCandidate.T3.Cache) (budget : Nat)
    (_hbudget : budget ≤ 2^127) :
    BPORS.Adaptive.ProposalModel Interaction SigGolfCandidate.T3.Security.MonitoredPrivate.State
      DigestSampling.IndexBuckets where
  Outcome := Outcome
  record := interactionRecord published
  response := response
  advance := advance
  label := label
  active := active
  base := PMF.pure default
  accept := 1024/1025
  positive := by norm_num
  lt_one := by
    apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_div]
  cap := by
    intro input state _ point
    have hconst : (interactionRecord published input state).map (label input) = PMF.pure default :=
      PMF.map_const _ _
    rw [hconst]
    exact mul_le_of_le_one_left (by simp) ProposalOverflow.acceptance_le_one
theorem proposal_query_erasure (published : SigGolfCandidate.T3.Cache) (budget : Nat)
    (hbudget : budget ≤ 2^127) (input : Interaction.Domain)
    (state : SigGolfCandidate.T3.Security.MonitoredPrivate.State) :
    (((proposalModel published budget hbudget).original input).run state)=
      (liftM (MonitoredPrivate.run (interactionSource published input) state) :
        PMF (Interaction.Range input × SigGolfCandidate.T3.Security.MonitoredPrivate.State)) := by
  change id <$> (liftM (MonitoredPrivate.run (interactionSource published input) state) : PMF _)=_
  rw [id_map]
theorem proposal_execution_erasure {α : Type} (published : SigGolfCandidate.T3.Cache) (budget : Nat)
    (hbudget : budget ≤ 2^127) (program : OracleComp Interaction α)
    (state : SigGolfCandidate.T3.Security.MonitoredPrivate.State) :
    (simulateQ (proposalModel published budget hbudget).original program).run state=
      (liftM (MonitoredPrivate.run (simulateQ (interactionSource published) program) state) :
        PMF (α × SigGolfCandidate.T3.Security.MonitoredPrivate.State)) := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp [MonitoredPrivate.run_pure]
  | query_bind input next ih =>
      rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,proposal_query_erasure]
      rw [simulateQ_bind,simulateQ_spec_query,MonitoredPrivate.run_bind,liftM_bind]
      apply bind_congr
      intro result
      exact ih result.1 result.2
theorem proposal_trace_erasure {α : Type} (published : SigGolfCandidate.T3.Cache) (budget : Nat)
    (hbudget : budget ≤ 2^127) (program : OracleComp Interaction α)
    (history : List DigestSampling.IndexBuckets) (state : SigGolfCandidate.T3.Security.MonitoredPrivate.State) :
    Prod.map id Prod.snd <$>
      (simulateQ (proposalModel published budget hbudget).traced program).run (history,state)=
      (liftM (MonitoredPrivate.run (simulateQ (interactionSource published) program) state) :
        PMF (α × SigGolfCandidate.T3.Security.MonitoredPrivate.State)) := by
  rw [(proposalModel published budget hbudget).traced_erasure,proposal_execution_erasure]
theorem logged_source {α : Type} (published : SigGolfCandidate.T3.Cache) (program : OracleComp Interaction α) :
    simulateQ (interactionSource published) (ProposalOverflow.logged program)=
      FullGame.loggedWith (FullGame.authenticatedSign published) program := by
  rw [ProposalOverflow.logged,QueryImpl.simulateQ_writerTMapBase_run]
  unfold FullGame.loggedWith
  congr 2
  funext input
  cases input <;>
    simp [QueryImpl.writerTMapBase,ProposalOverflow.logging,QueryImpl.withTraceAppend_apply,
      ProposalOverflow.logFragment,interactionSource]
  · rfl
  · apply WriterT.ext
    simp
end ClaudeWCT.W9.T3.Security.MonitoredPrivate
end
section
namespace ClaudeWCT.W9.T3.Security.MonitoredPrivate
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem signing_trace_overflow {Result : Type} (published : SigGolfCandidate.T3.Cache)
    (budget : Nat) (hbudget : budget ≤ 2^127)
    (program : OracleComp Interaction Result) (state : SigGolfCandidate.T3.Security.MonitoredPrivate.State) :
    Pr[fun result => result.2.2.1 ≤ 2^32 ∧ BPORS.Numeric.proposalLength < result.2.1.length |
      (simulateQ (ProposalOverflow.counted (proposalModel published budget hbudget)).traced program).run
        ([],0,state)] ≤ (2 : ENNReal)⁻¹ ^ 700 :=
  ProposalOverflow.full_trace_overflow_bound (proposalModel published budget hbudget) rfl program state
theorem signing_count_le_fragment (published : SigGolfCandidate.T3.Cache) (budget : Nat)
    (hbudget : budget ≤ 2^127) (input : LazyPrivate.Interaction.Domain)
    (state : List DigestSampling.IndexBuckets × (Nat × SigGolfCandidate.T3.Security.MonitoredPrivate.State))
    (result : LazyPrivate.Interaction.Range input ×
      (List DigestSampling.IndexBuckets × (Nat × SigGolfCandidate.T3.Security.MonitoredPrivate.State)))
    (hr : result ∈ (((ProposalOverflow.counted (proposalModel published budget hbudget)).traced input).run
      state).support) :
    result.2.2.1 ≤ state.2.1 + (ProposalOverflow.logFragment input result.1).length := by
  rw [ProposalOverflow.counted_query_count _ input state result hr]
  cases input with
  | inl input => simp [proposalModel, active, ProposalOverflow.logFragment]
  | inr request => simp only [ProposalOverflow.logFragment, List.length_singleton]; split <;> omega
theorem signing_count_le_log {Result : Type} (published : SigGolfCandidate.T3.Cache) (budget : Nat)
    (hbudget : budget ≤ 2^127) (program : OracleComp LazyPrivate.Interaction Result)
    (state : List DigestSampling.IndexBuckets × (Nat × SigGolfCandidate.T3.Security.MonitoredPrivate.State))
    (result : (Result × QueryLog Requests) ×
      (List DigestSampling.IndexBuckets × (Nat × SigGolfCandidate.T3.Security.MonitoredPrivate.State)))
    (hr : result ∈ ((simulateQ (ProposalOverflow.counted (proposalModel published budget hbudget)).traced
      (ProposalOverflow.logged program)).run state).support) :
    result.2.2.1 ≤ state.2.1 + result.1.2.length := by
  induction program using OracleComp.inductionOn generalizing state result with
  | pure value =>
      rw [ProposalOverflow.logged_pure, simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure,
        PMF.mem_support_pure_iff] at hr
      subst result
      simp
  | query_bind input next ih =>
      rw [ProposalOverflow.logged_query_bind, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
      obtain ⟨middle, hm, hr⟩ := hr
      have hstep := signing_count_le_fragment published budget hbudget input state middle hm
      rw [simulateQ_bind, StateT.run_bind, PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
      obtain ⟨last, hl, hr⟩ := hr
      have hrest := ih middle.1 middle.2 last hl
      rw [simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hr
      subst result
      simp only [List.length_append]
      omega
theorem signing_log_overflow {Result : Type} (published : SigGolfCandidate.T3.Cache) (budget : Nat)
    (hbudget : budget ≤ 2^127) (program : OracleComp LazyPrivate.Interaction Result)
    (state : SigGolfCandidate.T3.Security.MonitoredPrivate.State) :
    Pr[fun result => result.1.2.length ≤ 2^32 ∧ BPORS.Numeric.proposalLength < result.2.1.length |
      (simulateQ (ProposalOverflow.counted (proposalModel published budget hbudget)).traced
        (ProposalOverflow.logged program)).run ([],0,state)] ≤ (2 : ENNReal)⁻¹ ^ 700 := by
  apply le_trans ?_ (signing_trace_overflow published budget hbudget (ProposalOverflow.logged program) state)
  classical
  rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ ((simulateQ (ProposalOverflow.counted (proposalModel published budget hbudget)).traced
      (ProposalOverflow.logged program)).run ([],0,state)).support
  · by_cases hb : result.1.2.length ≤ 2^32 ∧ BPORS.Numeric.proposalLength < result.2.1.length
    · have hcount := signing_count_le_log published budget hbudget program ([],0,state) result hr
      have hc : result.2.2.1 ≤ result.1.2.length := by simpa using hcount
      simp only [hb, if_true, show result.2.2.1 ≤ 2^32 ∧
        BPORS.Numeric.proposalLength < result.2.1.length from ⟨hc.trans hb.1,hb.2⟩, le_refl]
    · simp only [hb, if_false, zero_le]
  · have hz : ((simulateQ (ProposalOverflow.counted (proposalModel published budget hbudget)).traced
        (ProposalOverflow.logged program)).run ([],0,state)) result = 0 := by
      simpa only [PMF.mem_support_iff, not_not] using hr
    simp only [PMF.probOutput_eq_apply, hz, ite_self, le_refl]
theorem source_proposal_overflow {Result : Type} (published : SigGolfCandidate.T3.Cache) (budget : Nat)
    (hbudget : budget ≤ 2^127) (program : OracleComp LazyPrivate.Interaction Result)
    (state : SigGolfCandidate.T3.Security.MonitoredPrivate.State) :
    Pr[fun result => result.1.2.length ≤ 2^32 ∧ BPORS.Numeric.proposalLength < result.2.1.length |
      (simulateQ (proposalModel published budget hbudget).traced (ProposalOverflow.logged program)).run
        ([],state)] ≤ (2 : ENNReal)⁻¹ ^ 700 := by
  rw [← ProposalOverflow.counted_trace_erasure (proposalModel published budget hbudget)
    (ProposalOverflow.logged program) ([],0,state), probEvent_map]
  exact signing_log_overflow published budget hbudget program state
theorem traced_source_support {α : Type} (published : SigGolfCandidate.T3.Cache) (budget : Nat)
    (hbudget : budget≤2^127) (program : OracleComp Interaction α)
    (before : SigGolfCandidate.T3.Security.MonitoredPrivate.History × SigGolfCandidate.T3.Security.MonitoredPrivate.State)
    (result : α × (SigGolfCandidate.T3.Security.MonitoredPrivate.History ×
      SigGolfCandidate.T3.Security.MonitoredPrivate.State))
    (hr : result ∈ ((simulateQ (proposalModel published budget hbudget).traced program).run before).support) :
    (result.1,result.2.2) ∈
      support (MonitoredPrivate.run (simulateQ (interactionSource published) program) before.2) := by
  rw [← MonitoredPrivate.pmf_support,← proposal_trace_erasure published budget hbudget program before.1 before.2]
  rw [PMF.monad_map_eq_map,PMF.mem_support_map_iff]
  exact ⟨result,hr,rfl⟩
theorem traced_query_source_support (published : SigGolfCandidate.T3.Cache) (budget : Nat)
    (hbudget : budget≤2^127) (input : Interaction.Domain)
    (before : SigGolfCandidate.T3.Security.MonitoredPrivate.History × SigGolfCandidate.T3.Security.MonitoredPrivate.State)
    (result : Interaction.Range input × (SigGolfCandidate.T3.Security.MonitoredPrivate.History ×
      SigGolfCandidate.T3.Security.MonitoredPrivate.State))
    (hr : result ∈ (((proposalModel published budget hbudget).traced input).run before).support) :
    (result.1,result.2.2) ∈ support (MonitoredPrivate.run (interactionSource published input) before.2) := by
  simpa only [simulateQ_spec_query] using
    traced_source_support published budget hbudget (liftM (Interaction.query input)) before result
      (by simpa only [simulateQ_spec_query] using hr)
end ClaudeWCT.W9.T3.Security.MonitoredPrivate
end
section
namespace ClaudeWCT.W9.T3.Security.QueryRecorded
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def Outcome (input : LazyPrivate.Interaction.Domain) : Type :=
  LazyPrivate.Interaction.Range input × SigGolfCandidate.T3.Security.QueryRecorded.State
def outcome (input : LazyPrivate.Interaction.Domain) (result : Outcome input) :
    MonitoredPrivate.Outcome input := (result.1, result.2.base)
noncomputable def interactionRecord (published : SigGolfCandidate.T3.Cache)
    (input : LazyPrivate.Interaction.Domain) (state : SigGolfCandidate.T3.Security.QueryRecorded.State) :
    PMF (Outcome input) :=
  liftM (QueryRecorded.run (MonitoredPrivate.interactionSource published input) state)
def advance (input : LazyPrivate.Interaction.Domain) (_ : SigGolfCandidate.T3.Security.QueryRecorded.State)
    (result : Outcome input) : SigGolfCandidate.T3.Security.QueryRecorded.State := result.2
theorem interactionRecord_project (published : SigGolfCandidate.T3.Cache)
    (input : LazyPrivate.Interaction.Domain) (state : SigGolfCandidate.T3.Security.QueryRecorded.State) :
    (interactionRecord published input state).map (outcome input)=
      MonitoredPrivate.interactionRecord published input state.base := by
  rw [← PMF.monad_map_eq_map,interactionRecord,← liftM_map]
  change (liftM (Prod.map id SigGolfCandidate.T3.Security.QueryRecorded.State.base <$>
    QueryRecorded.run (MonitoredPrivate.interactionSource published input) state) : PMF _)=_
  rw [QueryRecorded.run_erasure]
  rfl
noncomputable def refinement (published : SigGolfCandidate.T3.Cache) (budget : Nat) (hbudget : budget ≤ 2^127) :
    BPORS.Adaptive.ProposalModel.Refinement (MonitoredPrivate.proposalModel published budget hbudget)
      SigGolfCandidate.T3.Security.QueryRecorded.State where
  project := SigGolfCandidate.T3.Security.QueryRecorded.State.base
  Outcome := Outcome
  outcome := outcome
  record := interactionRecord published
  advance := advance
  record_project := interactionRecord_project published
  advance_project := by intro input state result; rfl
noncomputable def proposalModel (published : SigGolfCandidate.T3.Cache) (budget : Nat) (hbudget : budget ≤ 2^127) :=
  (refinement published budget hbudget).model'
theorem proposal_trace_project {α : Type} (published : SigGolfCandidate.T3.Cache) (budget : Nat)
    (hbudget : budget ≤ 2^127) (program : OracleComp LazyPrivate.Interaction α)
    (history : List DigestSampling.IndexBuckets) (state : SigGolfCandidate.T3.Security.QueryRecorded.State) :
    Prod.map id (Prod.map id SigGolfCandidate.T3.Security.QueryRecorded.State.base) <$>
      (simulateQ (proposalModel published budget hbudget).traced program).run (history,state)=
        (simulateQ (MonitoredPrivate.proposalModel published budget hbudget).traced program).run
          (history,state.base) :=
  (refinement published budget hbudget).traced_project program (history,state)
theorem proposal_query_erasure (published : SigGolfCandidate.T3.Cache) (budget : Nat) (hbudget : budget ≤ 2^127)
    (input : LazyPrivate.Interaction.Domain) (state : SigGolfCandidate.T3.Security.QueryRecorded.State) :
    (((proposalModel published budget hbudget).original input).run state)=
      (liftM (QueryRecorded.run (MonitoredPrivate.interactionSource published input) state) :
        PMF (LazyPrivate.Interaction.Range input × SigGolfCandidate.T3.Security.QueryRecorded.State)) := by
  change id <$> (liftM (QueryRecorded.run (MonitoredPrivate.interactionSource published input) state) : PMF _)=_
  rw [id_map]
theorem proposal_execution_erasure {α : Type} (published : SigGolfCandidate.T3.Cache) (budget : Nat)
    (hbudget : budget ≤ 2^127) (program : OracleComp LazyPrivate.Interaction α)
    (state : SigGolfCandidate.T3.Security.QueryRecorded.State) :
    (simulateQ (proposalModel published budget hbudget).original program).run state=
      (liftM (QueryRecorded.run (simulateQ (MonitoredPrivate.interactionSource published) program) state) :
        PMF (α × SigGolfCandidate.T3.Security.QueryRecorded.State)) := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp [QueryRecorded.run_pure]
  | query_bind input next ih =>
      rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,proposal_query_erasure]
      rw [simulateQ_bind,simulateQ_spec_query,QueryRecorded.run_bind,liftM_bind]
      apply bind_congr
      intro result
      exact ih result.1 result.2
theorem proposal_trace_erasure {α : Type} (published : SigGolfCandidate.T3.Cache) (budget : Nat)
    (hbudget : budget ≤ 2^127) (program : OracleComp LazyPrivate.Interaction α)
    (history : List DigestSampling.IndexBuckets) (state : SigGolfCandidate.T3.Security.QueryRecorded.State) :
    Prod.map id Prod.snd <$>
      (simulateQ (proposalModel published budget hbudget).traced program).run (history,state)=
      (liftM (QueryRecorded.run (simulateQ (MonitoredPrivate.interactionSource published) program) state) :
        PMF (α × SigGolfCandidate.T3.Security.QueryRecorded.State)) := by
  rw [(proposalModel published budget hbudget).traced_erasure,proposal_execution_erasure]
end ClaudeWCT.W9.T3.Security.QueryRecorded
end
section
namespace ClaudeWCT.W9.T3.Security.GameWith
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity (OracleWorld romImpl sampleMasterSeed)
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.FullGame
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _
noncomputable local instance : DecidableEq SiggolfT3Mac4.Cache := Classical.decEq _
noncomputable local instance : DecidableEq Region := Classical.decEq _
noncomputable local instance : Fintype Coordinate := coordinateFintype
noncomputable local instance : Fintype OtherCoordinate := otherFintype
noncomputable local instance : Fintype Region := CacheAuthentication.regionFintype
noncomputable local instance : SampleableType FullTable := Derivation.outputSampler Coordinate
noncomputable local instance : SampleableType OtherTable := otherSampler
noncomputable local instance : SampleableType MacTable := CacheAuthentication.macTableSampler
structure Checker (Forgery : Type) where
  check : Digest → QueryLog Requests → Forgery → M Bool
  nonMac : ∀ pk log forgery, NonMac (check pk log forgery)
variable {Forgery : Type}
abbrev AdversaryFor (Forgery : Type) :=
  Digest → SigGolfCandidate.T3.Cache → OracleComp LazyPrivate.Interaction (Option Forgery)
noncomputable def verdict (checker : Checker Forgery) (publicKey : Digest)
    (result : Option Forgery × QueryLog Requests) : M Bool := do
  let some forgery := result.1 | return false
  let verified ← checker.check publicKey result.2 forgery
  pure (decide (result.2.length ≤ 2^32) && verified)
theorem verdict_nonMac (checker : Checker Forgery) (publicKey : Digest)
    (result : Option Forgery × QueryLog Requests) : NonMac (verdict checker publicKey result) := by
  unfold verdict
  cases result.1 with
  | none => exact SourceQueries.pure_allowed _ _
  | some forgery =>
      exact SourceQueries.bind_allowed _ (checker.nonMac publicKey result.2 forgery)
        (fun _ => SourceQueries.pure_allowed _ _)
noncomputable def game (checker : Checker Forgery) (adversary : AdversaryFor Forgery) : M Bool := do
  let generated ← keygen
  let result ← FullGame.loggedWith (fun request => sign request.cache request.message)
    (adversary generated.1 generated.2)
  verdict checker generated.1 result
noncomputable def realExperiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery) :
    ProbComp (Bool × Nat) :=
  sampleMasterSeed >>= fun secret =>
    (simulateQ romImpl (SphincsSecurity.countHashQueries
      (Derivation.realize (privateInput secret) (game checker adversary)))).run' ∅
noncomputable def tableExperiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery)
    (q : Nat) : ProbComp (Option (Bool × Nat)) :=
  ($ᵗ FullTable : ProbComp _) >>= fun outputs =>
    (simulateQ romImpl (Derivation.tableRun outputs (Derivation.cap (game checker adversary) q))).run' ∅
theorem private_derivation_event_bound (checker : Checker Forgery)
    (adversary : AdversaryFor Forgery) (q : Nat) (hq : q < 2^256) :
    Pr[fun result => result.1=true ∧ result.2 ≤ q | realExperiment checker adversary] ≤
      Pr[fun outcome => ∃ result, outcome=some result ∧ result.1=true |
        tableExperiment checker adversary q] + q / ((2^256 : Nat) : ENNReal) :=
  Derivation.event_game_hop privateInput privateInput_injective
    privateInput_hit (game checker adversary) q hq (· = true)
noncomputable def countedTableExperiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery) : ProbComp (Bool × CountState) := do
  let table ← ($ᵗ FullTable : ProbComp _)
  run table (game checker adversary) (0,∅)
theorem counted_table_event (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) :
    Pr[fun result => result.1=true ∧ result.2.1≤q | countedTableExperiment checker adversary]=
      Pr[fun outcome => ∃ result,outcome=some result ∧ result.1=true | tableExperiment checker adversary q] := by
  unfold countedTableExperiment tableExperiment
  simp only [probEvent_bind_eq_tsum]
  apply tsum_congr
  intro table
  apply congrArg
  exact table_cap_event table (game checker adversary) ∅ q (·=true)
theorem real_to_counted_table (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) (hq : q < 2^256) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment checker adversary] ≤
      Pr[fun result => result.1=true ∧ result.2.1≤q | countedTableExperiment checker adversary]+
        q/((2^256 : Nat) : ENNReal) := by
  rw [counted_table_event]
  exact private_derivation_event_bound checker adversary q hq
noncomputable def splitTableExperiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery) : ProbComp (Bool × CountState) := do
  let other ← ($ᵗ OtherTable : ProbComp _)
  let mac ← ($ᵗ MacTable : ProbComp _)
  run (joinTable other mac) (game checker adversary) (0,∅)
theorem table_experiment_split (checker : Checker Forgery) (adversary : AdversaryFor Forgery) :
    𝒮[countedTableExperiment checker adversary]=𝒮[splitTableExperiment checker adversary] :=
  uniform_table_split_bind (fun table => run table (game checker adversary) (0,∅))
noncomputable def checkContinuation (checker : Checker Forgery) (other : OtherTable) (publicKey : Digest)
    (result : (Option Forgery × QueryLog Requests) × CountState) : ProbComp (Bool × CountState) :=
  (simulateQ (baseHandler other) (verdict checker publicKey result.1)).run result.2
noncomputable def realRest (checker : Checker Forgery) (other : OtherTable) (mac : MacTable) (adversary : AdversaryFor Forgery)
    (publicKey : Digest) (published : SigGolfCandidate.T3.Cache) (state : CountState) : ProbComp (Bool × CountState) :=
  RequestHop.run (worldHandler other) (MacGame.realSigner (baseHandler other) mac)
    (adversary publicKey published) state >>= checkContinuation checker other publicKey
noncomputable def idealRest (checker : Checker Forgery) (other : OtherTable) (adversary : AdversaryFor Forgery)
    (publicKey : Digest) (published : SigGolfCandidate.T3.Cache) (state : CountState) : ProbComp (Bool × CountState) :=
  RequestHop.run (worldHandler other) (MacGame.idealSigner (baseHandler other) published)
    (adversary publicKey published) state >>= checkContinuation checker other publicKey
theorem logged_source_run (other : OtherTable) (mac : MacTable)
    (program : OracleComp LazyPrivate.Interaction (Option Forgery)) (state : CountState) :
    (simulateQ (MacGame.sourceHandler (baseHandler other) mac) (FullGame.loggedWith (fun request => sign request.cache request.message) program)).run state=
      RequestHop.run (worldHandler other) (MacGame.realSigner (baseHandler other) mac) program state := by
  rw [FullGame.loggedWith_interpretation]
  change RequestHop.run (worldHandler other)
    (fun request => simulateQ (MacGame.sourceHandler (baseHandler other) mac)
      (sign request.cache request.message)) program state=_
  exact congrArg (fun signer => RequestHop.run (worldHandler other) signer program state)
    (funext fun request => MacGame.source_signer_eq (baseHandler other) mac request)
theorem source_rest_run (checker : Checker Forgery) (other : OtherTable) (mac : MacTable) (adversary : AdversaryFor Forgery)
    (publicKey : Digest) (published : SigGolfCandidate.T3.Cache) (state : CountState) :
    (simulateQ (MacGame.sourceHandler (baseHandler other) mac) (do
      let result ← FullGame.loggedWith (fun request => sign request.cache request.message) (adversary publicKey published)
      verdict checker publicKey result)).run state=
      realRest checker other mac adversary publicKey published state := by
  rw [simulateQ_bind,StateT.run_bind,logged_source_run]
  unfold realRest
  apply bind_congr
  intro result
  rw [MacGame.simulate_no_mac _ _ _ (verdict_nonMac checker publicKey result.1)]
  rfl
theorem fixed_game_expansion (checker : Checker Forgery) (other : OtherTable) (mac : MacTable) (adversary : AdversaryFor Forgery) :
    run (joinTable other mac) (game checker adversary) (0,∅)=
      (do
        let generated ← (simulateQ (baseHandler other) keygenPayload).run (0,∅)
        realRest checker other mac adversary generated.1.1 ⟨MacGame.tagAt mac generated.1.2,generated.1.2⟩
          (generated.2.1+2,generated.2.2)) := by
  rw [run,tableHandler_split,game]
  simp only [keygen,bind_assoc,pure_bind,simulateQ_bind,StateT.run_bind]
  rw [MacGame.simulate_no_mac _ _ _ keygenPayload_nonMac]
  apply bind_congr
  intro generated
  rw [source_mac_run,pure_bind]
  simpa only [simulateQ_bind,StateT.run_bind] using
    source_rest_run checker other mac adversary generated.1.1
      ⟨MacGame.tagAt mac generated.1.2,generated.1.2⟩ (generated.2.1+2,generated.2.2)
theorem refresh_published_mac (checker : Checker Forgery) (other : OtherTable) (adversary : AdversaryFor Forgery)
    (generated : (Digest × Region) × CountState) :
    𝒮[do
      let mac ← ($ᵗ MacTable : ProbComp _)
      realRest checker other mac adversary generated.1.1 ⟨MacGame.tagAt mac generated.1.2,generated.1.2⟩
        (generated.2.1+2,generated.2.2)]=
    𝒮[do
      let tag ← ($ᵗ HashOutput : ProbComp _)
      let mac ← ($ᵗ MacTable : ProbComp _)
      realRest checker other (MacGame.retag mac ⟨tag,generated.1.2⟩) adversary
        generated.1.1 ⟨tag,generated.1.2⟩ (generated.2.1+2,generated.2.2)] := by
  exact MacGame.refresh_published generated.1.2 (fun tag mac =>
    realRest checker other mac adversary generated.1.1 ⟨tag,generated.1.2⟩
      (generated.2.1+2,generated.2.2))
noncomputable def preparedExperiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery) : ProbComp (Bool × CountState) := do
  let prepared ← setup
  let mac ← ($ᵗ MacTable : ProbComp _)
  realRest checker prepared.other (MacGame.retag mac prepared.published)
    adversary prepared.publicKey prepared.published prepared.state
noncomputable def authenticatedExperiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery) : ProbComp (Bool × CountState) := do
  let prepared ← setup
  idealRest checker prepared.other adversary prepared.publicKey prepared.published prepared.state
theorem split_experiment_prepared (checker : Checker Forgery) (adversary : AdversaryFor Forgery) :
    𝒮[splitTableExperiment checker adversary]=𝒮[preparedExperiment checker adversary] := by
  unfold splitTableExperiment preparedExperiment setup
  simp only [bind_assoc,pure_bind]
  apply evalSPMF_bind_congr'
  intro other
  simp_rw [fixed_game_expansion]
  rw [evalSPMF_bind_bind_swap]
  apply evalSPMF_bind_congr'
  intro generated
  exact refresh_published_mac checker other adversary generated
theorem checkContinuation_long (checker : Checker Forgery) (other : OtherTable) (publicKey : Digest)
    (result : (Option Forgery × QueryLog Requests) × CountState)
    (hlong : 2^32 < result.1.2.length) (q : Nat) :
    Pr[fun outcome => outcome.1=true ∧ outcome.2.1≤q | checkContinuation checker other publicKey result]=0 := by
  have hn : ¬result.1.2.length≤2^32 := Nat.not_le.mpr hlong
  unfold checkContinuation verdict
  cases result.1.1 with
  | none => simp [StateT.run_pure]
  | some forgery =>
      simp
      intro count cache _ hshort
      exact False.elim (hn hshort)
theorem rest_authentication_bound (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (prepared : Setup) (q : Nat) :
    Pr[fun result => result.1=true ∧ result.2.1≤q | do
      let mac ← ($ᵗ MacTable : ProbComp _)
      realRest checker prepared.other (MacGame.retag mac prepared.published)
        adversary prepared.publicKey prepared.published prepared.state] ≤
    Pr[fun result => result.1=true ∧ result.2.1≤q |
      idealRest checker prepared.other adversary prepared.publicKey prepared.published prepared.state]+
      ((2 : ENNReal)^152)⁻¹ := by
  have h := MacGame.authentication_hop (worldHandler prepared.other) (baseHandler prepared.other)
    prepared.published (adversary prepared.publicKey prepared.published) (2^32) prepared.state
    (checkContinuation checker prepared.other prepared.publicKey) (fun result => result.1=true ∧ result.2.1≤q)
    (fun result hlong => checkContinuation_long checker prepared.other prepared.publicKey result hlong q)
  refine h.trans (add_le_add le_rfl ?_)
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_pow]
theorem prepared_authentication_bound (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) :
    Pr[fun result => result.1=true ∧ result.2.1≤q | preparedExperiment checker adversary] ≤
      Pr[fun result => result.1=true ∧ result.2.1≤q | authenticatedExperiment checker adversary]+
        ((2 : ENNReal)^152)⁻¹ :=
  probEvent_bind_le_add setup _ _ _ _ (fun prepared => rest_authentication_bound checker adversary prepared q)
theorem real_to_authenticated (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) (hq : q < 2^256) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment checker adversary] ≤
      Pr[fun result => result.1=true ∧ result.2.1≤q | authenticatedExperiment checker adversary]+
        ((2 : ENNReal)^152)⁻¹+q/((2^256 : Nat) : ENNReal) := by
  have h := real_to_counted_table checker adversary q hq
  have he := (table_experiment_split checker adversary).trans (split_experiment_prepared checker adversary)
  have hp : Pr[fun result => result.1=true ∧ result.2.1≤q | countedTableExperiment checker adversary]=
      Pr[fun result => result.1=true ∧ result.2.1≤q | preparedExperiment checker adversary] :=
    probEvent_congr' (fun _ _ => Iff.rfl) he
  rw [hp] at h
  exact h.trans (add_le_add (prepared_authentication_bound checker adversary q) le_rfl)
noncomputable def idealGame (checker : Checker Forgery) (adversary : AdversaryFor Forgery) : M Bool := do
  let generated ← keygen
  let result ← FullGame.loggedWith (FullGame.authenticatedSign generated.2) (adversary generated.1 generated.2)
  verdict checker generated.1 result
theorem ideal_rest_run (checker : Checker Forgery) (other : OtherTable) (mac : MacTable) (adversary : AdversaryFor Forgery)
    (publicKey : Digest) (published : SigGolfCandidate.T3.Cache) (state : CountState) :
    (simulateQ (MacGame.sourceHandler (baseHandler other) mac) (do
      let result ← FullGame.loggedWith (FullGame.authenticatedSign published) (adversary publicKey published)
      verdict checker publicKey result)).run state=idealRest checker other adversary publicKey published state := by
  rw [simulateQ_bind,StateT.run_bind,FullGame.loggedWith_interpretation]
  have hs : (fun request => simulateQ (MacGame.sourceHandler (baseHandler other) mac)
      (FullGame.authenticatedSign published request))=MacGame.idealSigner (baseHandler other) published :=
    funext fun request => FullGame.authenticatedSign_interpretation other mac published request
  rw [hs]
  change RequestHop.run (worldHandler other) (MacGame.idealSigner (baseHandler other) published)
    (adversary publicKey published) state >>= _ = _
  unfold idealRest
  apply bind_congr
  intro result
  rw [MacGame.simulate_no_mac _ _ _ (verdict_nonMac checker publicKey result.1)]
  rfl
theorem fixed_ideal_expansion (checker : Checker Forgery) (other : OtherTable) (mac : MacTable) (adversary : AdversaryFor Forgery) :
    run (joinTable other mac) (idealGame checker adversary) (0,∅)=
      (do
        let generated ← (simulateQ (baseHandler other) keygenPayload).run (0,∅)
        idealRest checker other adversary generated.1.1 ⟨MacGame.tagAt mac generated.1.2,generated.1.2⟩
          (generated.2.1+2,generated.2.2)) := by
  rw [run,tableHandler_split,idealGame]
  simp only [keygen,bind_assoc,pure_bind,simulateQ_bind,StateT.run_bind]
  rw [MacGame.simulate_no_mac _ _ _ keygenPayload_nonMac]
  apply bind_congr
  intro generated
  rw [source_mac_run,pure_bind]
  simpa only [simulateQ_bind,StateT.run_bind] using
    ideal_rest_run checker other mac adversary generated.1.1
      ⟨MacGame.tagAt mac generated.1.2,generated.1.2⟩ (generated.2.1+2,generated.2.2)
noncomputable def idealTableExperiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery) : ProbComp (Bool × CountState) := do
  let table ← ($ᵗ FullTable : ProbComp _)
  run table (idealGame checker adversary) (0,∅)
theorem ideal_table_authenticated (checker : Checker Forgery) (adversary : AdversaryFor Forgery) :
    𝒮[idealTableExperiment checker adversary]=𝒮[authenticatedExperiment checker adversary] := by
  unfold idealTableExperiment
  rw [uniform_table_split_bind]
  unfold authenticatedExperiment setup
  simp only [bind_assoc,pure_bind]
  apply evalSPMF_bind_congr'
  intro other
  simp_rw [fixed_ideal_expansion]
  rw [evalSPMF_bind_bind_swap]
  apply evalSPMF_bind_congr'
  intro generated
  exact sample_mac_at_bind generated.1.2 (fun tag =>
    idealRest checker other adversary generated.1.1 ⟨tag,generated.1.2⟩ (generated.2.1+2,generated.2.2))
noncomputable def idealLazyExperiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery) :
    ProbComp ((Bool × Nat) × LazyPrivate.State) :=
  LazyPrivate.run (SphincsSecurity.QueryCap.counted Derivation.charged (idealGame checker adversary)) (∅,∅)
theorem ideal_lazy_event (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) :
    Pr[fun result => result.1.1=true ∧ result.1.2≤q | idealLazyExperiment checker adversary]=
      Pr[fun result => result.1=true ∧ result.2.1≤q | authenticatedExperiment checker adversary] := by
  have h := LazyPrivate.run_eq_table
    (SphincsSecurity.QueryCap.counted Derivation.charged (idealGame checker adversary)) ∅
  have hp : Pr[fun result => result.1.1=true ∧ result.1.2≤q |
      Prod.map id Prod.snd <$> idealLazyExperiment checker adversary]=
      Pr[fun result => result.1.1=true ∧ result.1.2≤q | do
        let table ← ($ᵗ FullTable : ProbComp _)
        (simulateQ romImpl (Derivation.tableRun table
          (SphincsSecurity.QueryCap.counted Derivation.charged (idealGame checker adversary)))).run ∅] :=
    probEvent_congr' (fun _ _ => Iff.rfl) h
  simp only [probEvent_map,Prod.map,id_eq,Function.comp_def] at hp
  rw [hp]
  have he : Pr[fun result => result.1=true ∧ result.2.1≤q | idealTableExperiment checker adversary]=
      Pr[fun result => result.1=true ∧ result.2.1≤q | authenticatedExperiment checker adversary] :=
    probEvent_congr' (fun _ _ => Iff.rfl) (ideal_table_authenticated checker adversary)
  rw [← he]
  unfold idealTableExperiment
  simp only [probEvent_bind_eq_tsum]
  apply tsum_congr
  intro table
  apply congrArg
  rw [run,tableHandler,countHandler_run,probEvent_map]
  simp only [plain_run,Function.comp_def,Nat.zero_add]
theorem real_to_ideal_lazy (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) (hq : q < 2^256) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment checker adversary] ≤
      Pr[fun result => result.1.1=true ∧ result.1.2≤q | idealLazyExperiment checker adversary]+
        ((2 : ENNReal)^152)⁻¹+q/((2^256 : Nat) : ENNReal) := by
  rw [ideal_lazy_event]
  exact real_to_authenticated checker adversary q hq
end ClaudeWCT.W9.T3.Security.GameWith
end
section
namespace ClaudeWCT.W9.T3.Security.GameWith
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {Forgery : Type}
namespace Counted
open SigGolfCandidate.T3.Security.CountedPrivate
noncomputable def experiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery) : ProbComp (Bool × State) :=
  run (GameWith.idealGame checker adversary) (0,∅,∅)
theorem experiment_event (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) :
    Pr[fun result => result.1=true ∧ result.2.1≤q | experiment checker adversary]=
      Pr[fun result => result.1.1=true ∧ result.1.2≤q | GameWith.idealLazyExperiment checker adversary] := by
  simp only [experiment,run,GameWith.idealLazyExperiment,probEvent_map,Function.comp_def,Nat.zero_add]
theorem real_to_counted_ideal (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) (hq : q < 2^256) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment checker adversary] ≤
      Pr[fun result => result.1=true ∧ result.2.1≤q | experiment checker adversary]+
        ((2 : ENNReal)^152)⁻¹+q/((2^256 : Nat) : ENNReal) := by
  rw [experiment_event]
  exact GameWith.real_to_ideal_lazy checker adversary q hq
end Counted
namespace Monitored
open SigGolfCandidate.T3.Security.MonitoredPrivate
noncomputable def experiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery) : ProbComp (Bool × State) :=
  run (GameWith.idealGame checker adversary) ⟨(0,∅,∅),false⟩
theorem experiment_erasure (checker : Checker Forgery) (adversary : AdversaryFor Forgery) :
    Prod.map id State.source <$> experiment checker adversary=Counted.experiment checker adversary :=
  run_erasure (GameWith.idealGame checker adversary) ⟨(0,∅,∅),false⟩
theorem experiment_event (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) :
    Pr[fun result => result.1=true ∧ result.2.source.1≤q | experiment checker adversary]=
      Pr[fun result => result.1=true ∧ result.2.1≤q | Counted.experiment checker adversary] := by
  rw [← experiment_erasure checker adversary,probEvent_map]
  rfl
theorem real_to_monitored_ideal (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) (hq : q < 2^256) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment checker adversary] ≤
      Pr[fun result => result.1=true ∧ result.2.source.1≤q | experiment checker adversary]+
        ((2 : ENNReal)^152)⁻¹+q/((2^256 : Nat) : ENNReal) := by
  rw [experiment_event]
  exact Counted.real_to_counted_ideal checker adversary q hq
abbrev History := List DigestSampling.IndexBuckets
noncomputable def tracedExperiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (budget : Nat)
    (hbudget : budget ≤ 2^127) : PMF (Bool × (History × State)) := do
  let generated ← (liftM (run keygen ⟨(0,∅,∅),false⟩) : PMF _)
  let interaction ← (simulateQ (MonitoredPrivate.proposalModel generated.1.2 budget hbudget).traced
    (ProposalOverflow.logged (adversary generated.1.1 generated.1.2))).run ([],generated.2)
  let checked ← (liftM (run (GameWith.verdict checker generated.1.1 interaction.1) interaction.2.2) : PMF _)
  pure (checked.1,interaction.2.1,checked.2)
theorem tracedExperiment_erasure (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (budget : Nat)
    (hbudget : budget ≤ 2^127) :
    Prod.map id Prod.snd <$> tracedExperiment checker adversary budget hbudget=
      (liftM (experiment checker adversary) : PMF (Bool × State)) := by
  unfold tracedExperiment experiment GameWith.idealGame
  simp only [run_bind,liftM_bind,map_bind,map_pure,Prod.map,id_eq,Prod.mk.eta]
  apply bind_congr
  intro generated
  have h := MonitoredPrivate.proposal_trace_erasure generated.1.2 budget hbudget
    (ProposalOverflow.logged (adversary generated.1.1 generated.1.2)) [] generated.2
  rw [MonitoredPrivate.logged_source] at h
  rw [← h,bind_map_left]
  simp only [bind_pure,Prod.map,id_eq]
theorem tracedExperiment_event (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.1=true ∧ result.2.2.source.1≤q | tracedExperiment checker adversary q hq]=
      Pr[fun result => result.1=true ∧ result.2.source.1≤q | experiment checker adversary] := by
  have h := congrArg (fun law : PMF (Bool × State) =>
    Pr[fun result => result.1=true ∧ result.2.source.1≤q | law]) (tracedExperiment_erasure checker adversary q hq)
  simp only [probEvent_map,Function.comp_def,Prod.map,id_eq] at h
  calc
    _ = Pr[fun result => result.1=true ∧ result.2.source.1≤q | (liftM (experiment checker adversary) : PMF _)] := h
    _ = _ := by
      simp only [probEvent_eq_tsum_ite]
      rfl
theorem real_to_traced (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment checker adversary] ≤
      Pr[fun result => result.1=true ∧ result.2.2.source.1≤q | tracedExperiment checker adversary q hq]+
        ((2 : ENNReal)^152)⁻¹+q/((2^256 : Nat) : ENNReal) := by
  rw [tracedExperiment_event]
  exact real_to_monitored_ideal checker adversary q (hq.trans_lt (by norm_num))
theorem verdict_success_log (checker : Checker Forgery) (publicKey : Digest) (interaction : Option Forgery × QueryLog Requests)
    (state : State) (result : Bool × State)
    (hr : result ∈ support (run (GameWith.verdict checker publicKey interaction) state))
    (hwin : result.1=true) : interaction.2.length≤2^32 := by
  unfold GameWith.verdict at hr
  cases ho : interaction.1 with
  | none =>
      simp only [ho,run_pure,support_pure,Set.mem_singleton_iff] at hr
      subst result
      contradiction
  | some forgery =>
      simp only [ho,run_bind,mem_support_bind_iff,run_pure,support_pure,Set.mem_singleton_iff] at hr
      obtain ⟨middle,_,rfl⟩ := hr
      simp only [Bool.and_eq_true,decide_eq_true_eq] at hwin
      exact hwin.1
theorem winning_trace_overflow (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (budget : Nat)
    (hbudget : budget ≤ 2^127) :
    Pr[fun result => result.1=true ∧ BPORS.Numeric.proposalLength < result.2.1.length |
      tracedExperiment checker adversary budget hbudget] ≤ (2 : ENNReal)⁻¹^700 := by
  rw [← expectedValue_ite_one]
  simp only [tracedExperiment,expectedValue_bind,expectedValue_pure]
  change expectedValue (run keygen ⟨(0,∅,∅),false⟩) _ ≤ _
  apply expectedValue_le_of_support
  intro generated _
  apply le_trans ?_ (MonitoredPrivate.source_proposal_overflow generated.1.2 budget hbudget
    (adversary generated.1.1 generated.1.2) generated.2)
  rw [← expectedValue_ite_one]
  apply expectedValue_mono
  intro interaction
  change expectedValue (run (GameWith.verdict checker generated.1.1 interaction.1) interaction.2.2)
    (fun checked => if checked.1=true ∧ BPORS.Numeric.proposalLength < interaction.2.1.length then 1 else 0) ≤ _
  apply expectedValue_le_of_support
  intro checked hchecked
  by_cases h : checked.1=true ∧ BPORS.Numeric.proposalLength < interaction.2.1.length
  · have hl := verdict_success_log checker generated.1.1 interaction.1 interaction.2.2 checked hchecked h.1
    simp only [h,if_true,show interaction.1.2.length≤2^32 ∧
      BPORS.Numeric.proposalLength < interaction.2.1.length from ⟨hl,h.2⟩,le_refl]
  · simp only [h,if_false,zero_le]
theorem split_winning_trace (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.1=true ∧ result.2.2.source.1≤q | tracedExperiment checker adversary q hq] ≤
      Pr[fun result => result.1=true ∧ result.2.2.source.1≤q ∧
        result.2.1.length≤BPORS.Numeric.proposalLength | tracedExperiment checker adversary q hq]+
      Pr[fun result => result.1=true ∧ BPORS.Numeric.proposalLength < result.2.1.length |
        tracedExperiment checker adversary q hq] := by
  simp only [probEvent_eq_tsum_ite]
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hw : result.1=true ∧ result.2.2.source.1≤q
  · by_cases hn : result.2.1.length≤BPORS.Numeric.proposalLength
    · simp [hw,hw.1,hw.2,hn,Nat.not_lt.mpr hn]
    · simp [hw,hw.1,hw.2,hn,Nat.lt_of_not_ge hn]
  · simp only [hw,if_false,zero_le]
theorem real_to_bounded_trace (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment checker adversary] ≤
      Pr[fun result => result.1=true ∧ result.2.2.source.1≤q ∧
        result.2.1.length≤BPORS.Numeric.proposalLength | tracedExperiment checker adversary q hq]+
        (2 : ENNReal)⁻¹^700+((2 : ENNReal)^152)⁻¹+q/((2^256 : Nat) : ENNReal) := by
  apply (real_to_traced checker adversary q hq).trans
  apply add_le_add_left
  apply add_le_add_left
  exact (split_winning_trace checker adversary q hq).trans
    (add_le_add le_rfl (winning_trace_overflow checker adversary q hq))
theorem experiment_exception_bound (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.2.source.1≤q ∧ result.2.exceptional=true | experiment checker adversary] ≤
      q/(2 : ENNReal)^146 := by
  exact gate6_run_empty_linear_charge (GameWith.idealGame checker adversary) q 146 hq (by decide)
theorem traced_exception_bound (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.2.2.source.1≤q ∧ result.2.2.exceptional=true |
      tracedExperiment checker adversary q hq] ≤ q/(2 : ENNReal)^146 := by
  have h := congrArg (fun law : PMF (Bool × State) =>
    Pr[fun result => result.2.source.1≤q ∧ result.2.exceptional=true | law])
    (tracedExperiment_erasure checker adversary q hq)
  simp only [probEvent_map,Function.comp_def,Prod.map,id_eq,event_lift] at h
  rw [h]
  exact experiment_exception_bound checker adversary q hq
theorem split_bounded_trace (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.1=true ∧ result.2.2.source.1≤q ∧
      result.2.1.length≤BPORS.Numeric.proposalLength | tracedExperiment checker adversary q hq] ≤
      Pr[fun result => result.1=true ∧ result.2.2.source.1≤q ∧
        result.2.1.length≤BPORS.Numeric.proposalLength ∧ result.2.2.exceptional=false |
          tracedExperiment checker adversary q hq]+
      Pr[fun result => result.2.2.source.1≤q ∧ result.2.2.exceptional=true |
        tracedExperiment checker adversary q hq] := by
  simp only [probEvent_eq_tsum_ite]
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hw : result.1=true ∧ result.2.2.source.1≤q ∧ result.2.1.length≤BPORS.Numeric.proposalLength
  · cases hb : result.2.2.exceptional <;> simp [hw,hw.2.1,hb]
  · simp only [hw,if_false,zero_le]
theorem real_to_clean_bounded_trace (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment checker adversary] ≤
      Pr[fun result => result.1=true ∧ result.2.2.source.1≤q ∧
        result.2.1.length≤BPORS.Numeric.proposalLength ∧ result.2.2.exceptional=false |
          tracedExperiment checker adversary q hq]+
        q/(2 : ENNReal)^146+(2 : ENNReal)⁻¹^700+
        ((2 : ENNReal)^152)⁻¹+q/((2^256 : Nat) : ENNReal) := by
  apply (real_to_bounded_trace checker adversary q hq).trans
  apply add_le_add_left
  apply add_le_add_left
  apply add_le_add_left
  exact (split_bounded_trace checker adversary q hq).trans
    (add_le_add le_rfl (traced_exception_bound checker adversary q hq))
end Monitored
end ClaudeWCT.W9.T3.Security.GameWith
end
section
namespace ClaudeWCT.W9.T3.Security.GameWith.Recorded
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.QueryRecorded
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen GameWith.idealGame
variable {Forgery : Type}
noncomputable def tracedExperiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (budget : Nat)
    (hbudget : budget ≤ 2^127) : PMF (Bool × (MonitoredPrivate.History × State)) := do
  let generated ← (liftM (run keygen initial) : PMF _)
  let interaction ← (simulateQ (QueryRecorded.proposalModel generated.1.2 budget hbudget).traced
    (ProposalOverflow.logged (adversary generated.1.1 generated.1.2))).run ([],generated.2)
  let checked ← (liftM (run (GameWith.verdict checker generated.1.1 interaction.1) interaction.2.2) : PMF _)
  pure (checked.1,interaction.2.1,checked.2)
theorem traced_base_erasure (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (budget : Nat) (hbudget : budget ≤ 2^127) :
    Prod.map id (Prod.map id State.base) <$> tracedExperiment checker adversary budget hbudget=
      Monitored.tracedExperiment checker adversary budget hbudget := by
  unfold tracedExperiment Monitored.tracedExperiment
  simp only [map_bind,map_pure,Prod.map,id_eq]
  have hk := lift_run_erasure keygen initial
  change Prod.map id State.base <$> (liftM (run keygen initial) : PMF _)=
    (liftM (MonitoredPrivate.run keygen ⟨(0,∅,∅),false⟩) : PMF _) at hk
  rw [← hk,bind_map_left]
  apply bind_congr
  intro generated
  simp only [Prod.map,id_eq]
  rw [← QueryRecorded.proposal_trace_project generated.1.2 budget hbudget _ [] generated.2,bind_map_left]
  apply bind_congr
  intro interaction
  simp only [Prod.map,id_eq]
  rw [← lift_run_erasure (GameWith.verdict checker generated.1.1 interaction.1) interaction.2.2,bind_map_left]
  rfl
theorem traced_source_erasure (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (budget : Nat) (hbudget : budget ≤ 2^127) :
    Prod.map id Prod.snd <$> tracedExperiment checker adversary budget hbudget=
      (liftM (run (GameWith.idealGame checker adversary) initial) : PMF _) := by
  unfold tracedExperiment GameWith.idealGame
  simp only [run_bind,liftM_bind,map_bind,map_pure,Prod.map,id_eq,Prod.mk.eta]
  apply bind_congr
  intro generated
  have h := QueryRecorded.proposal_trace_erasure generated.1.2 budget hbudget
    (ProposalOverflow.logged (adversary generated.1.1 generated.1.2)) [] generated.2
  rw [MonitoredPrivate.logged_source] at h
  rw [← h,bind_map_left]
  simp only [bind_pure,Prod.map,id_eq]
theorem traced_record_erasure (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (budget : Nat) (hbudget : budget ≤ 2^127) :
    recordedTrace <$> tracedExperiment checker adversary budget hbudget=
      (liftM (FirstHit.record (GameWith.idealGame checker adversary) (∅,∅)) : PMF _) := by
  have hr : recorded <$> run (GameWith.idealGame checker adversary) initial=
      FirstHit.record (GameWith.idealGame checker adversary) (∅,∅) := by
    rw [run_recorded]
    have hp : prepend ([] : List FirstHit.QueryEvent)=(id : FirstHit.Recorded Bool → FirstHit.Recorded Bool) := by
      funext result
      rfl
    change prepend [] <$> FirstHit.record (GameWith.idealGame checker adversary) (∅,∅)=_
    rw [hp,id_map]
  calc
    _ = recorded <$> (Prod.map id Prod.snd <$> tracedExperiment checker adversary budget hbudget) := by
      rw [Functor.map_map]
      rfl
    _ = recorded <$> (liftM (run (GameWith.idealGame checker adversary) initial) : PMF _) := by
      rw [traced_source_erasure]
    _ = (liftM (recorded <$> run (GameWith.idealGame checker adversary) initial) : PMF _) := (liftM_map _ _).symm
    _ = _ := by rw [hr]
theorem traced_cost_coherent (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (budget : Nat) (hbudget : budget ≤ 2^127)
    (result : Bool × (MonitoredPrivate.History × State))
    (hr : result ∈ (tracedExperiment checker adversary budget hbudget).support) : CostCoherent result.2.2 := by
  have hp : (result.1,result.2.2) ∈
      (Prod.map id Prod.snd <$> tracedExperiment checker adversary budget hbudget).support := by
    rw [PMF.monad_map_eq_map,PMF.support_map]
    exact ⟨result,hr,rfl⟩
  rw [traced_source_erasure] at hp
  rw [MonitoredPrivate.pmf_support] at hp
  exact run_cost_coherent (GameWith.idealGame checker adversary) initial initial_cost
    (result.1,result.2.2) hp
theorem known_public_hit_bound (checker : Checker Forgery) (reference : FirstHit.Reference) (adversary : AdversaryFor Forgery)
    (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.2.2.base.source.1≤q ∧ FirstHit.KnownPublicHit reference (recordedTrace result) |
      tracedExperiment checker adversary q hq] ≤ q/(2 : ENNReal)^128 := by
  have h := FirstHit.recorded_known_public_hit_bound reference (GameWith.idealGame checker adversary) (∅,∅) q
  have he := congrArg (fun law => Pr[fun result : FirstHit.Recorded Bool =>
      (result.events.map (fun event => FullGame.queryCharge event.input)).sum≤q ∧
      FirstHit.KnownPublicHit reference result | law]) (traced_record_erasure checker adversary q hq)
  rw [probEvent_map,MonitoredPrivate.event_lift] at he
  apply le_trans _ (he.le.trans h)
  simp only [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ (tracedExperiment checker adversary q hq).support
  · have hc := traced_cost_coherent checker adversary q hq result hr
    simp only [Function.comp_def,recordedTrace,recorded]
    rw [show result.2.2.base.source.1=
      (result.2.2.events.map (fun event => FullGame.queryCharge event.input)).sum from hc]
  · have hz : (tracedExperiment checker adversary q hq) result=0 := by
      by_contra hn
      exact hr (by simpa only [PMF.mem_support_iff] using hn)
    simp only [PMF.probOutput_eq_apply,hz,ite_self,le_refl]
theorem real_to_clean_trace (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment checker adversary] ≤
      Pr[fun result => result.1=true ∧ result.2.2.base.source.1≤q ∧
        result.2.1.length≤BPORS.Numeric.proposalLength ∧ result.2.2.base.exceptional=false |
          tracedExperiment checker adversary q hq]+
      q/(2 : ENNReal)^146+(2 : ENNReal)⁻¹^700+((2 : ENNReal)^152)⁻¹+q/((2^256 : Nat) : ENNReal) := by
  have h := Monitored.real_to_clean_bounded_trace checker adversary q hq
  rw [← traced_base_erasure checker adversary q hq,probEvent_map] at h
  exact h
theorem split_known_hit (checker : Checker Forgery) (reference : FirstHit.Reference) (adversary : AdversaryFor Forgery)
    (q : Nat) (hq : q ≤ 2^127) :
    Pr[CleanWin q | tracedExperiment checker adversary q hq] ≤
      Pr[fun result => CleanWin q result ∧ ¬FirstHit.KnownPublicHit reference (recordedTrace result) |
        tracedExperiment checker adversary q hq]+
      Pr[fun result => result.2.2.base.source.1≤q ∧ FirstHit.KnownPublicHit reference (recordedTrace result) |
        tracedExperiment checker adversary q hq] := by
  simp only [probEvent_eq_tsum_ite]
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hw : CleanWin q result
  · have hcount := hw.2.1
    by_cases hh : FirstHit.KnownPublicHit reference (recordedTrace result)
    · simp [hw,hcount,hh]
    · simp [hw,hcount,hh]
  · simp only [hw,if_false,zero_le]
theorem real_to_clean_without_known (checker : Checker Forgery) (reference : FirstHit.Reference) (adversary : AdversaryFor Forgery)
    (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment checker adversary] ≤
      Pr[fun result => CleanWin q result ∧ ¬FirstHit.KnownPublicHit reference (recordedTrace result) |
        tracedExperiment checker adversary q hq]+
      q/(2 : ENNReal)^128+q/(2 : ENNReal)^146+(2 : ENNReal)⁻¹^700+
      ((2 : ENNReal)^152)⁻¹+q/((2^256 : Nat) : ENNReal) := by
  apply (real_to_clean_trace checker adversary q hq).trans
  apply add_le_add _ le_rfl
  apply add_le_add _ le_rfl
  apply add_le_add _ le_rfl
  apply add_le_add _ le_rfl
  exact (split_known_hit checker reference adversary q hq).trans
    (add_le_add le_rfl (known_public_hit_bound checker reference adversary q hq))
theorem large_budget (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) (hq : 2^127 ≤ q) :
    Pr[fun result => result.1=true ∧ result.2 ≤ q | realExperiment checker adversary] ≤
      (q : ENNReal)/2^127 := by
  apply probEvent_le_one.trans
  have hcast : (2 : ENNReal)^127 ≤ (q : ENNReal) := by exact_mod_cast hq
  calc
    (1 : ENNReal) = (2 : ENNReal)^127/(2 : ENNReal)^127 := (ENNReal.div_self (by positivity) (by finiteness)).symm
    _ ≤ _ := ENNReal.div_le_div_right hcast _
theorem security_of_clean_bound (checker : Checker Forgery)
    (hclean : ∀ (adversary : AdversaryFor Forgery) (q : Nat), 1 ≤ q → ∀ hq : q ≤ 2^127,
      Pr[CleanWin q | tracedExperiment checker adversary q hq]+
        q/(2 : ENNReal)^146+(2 : ENNReal)⁻¹^700+((2 : ENNReal)^152)⁻¹+
        q/((2^256 : Nat) : ENNReal) ≤ (q : ENNReal)/2^127)
    (adversary : AdversaryFor Forgery) (q : Nat) (hpositive : 1 ≤ q) :
    Pr[fun result => result.1=true ∧ result.2 ≤ q | realExperiment checker adversary] ≤
      (q : ENNReal)/2^127 := by
  by_cases hq : 2^127 ≤ q
  · exact large_budget checker adversary q hq
  · have hsmall : q ≤ 2^127 := Nat.le_of_lt (Nat.lt_of_not_ge hq)
    refine (real_to_clean_trace checker adversary q hsmall).trans ?_
    exact hclean adversary q hpositive hsmall
end ClaudeWCT.W9.T3.Security.GameWith.Recorded
end
section
namespace ClaudeWCT.W9.T3.Security.PaddedGame
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M (allQ_bind allQ_pure)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen checkForgeryP
theorem check_public (publicKey : Digest) (log : QueryLog Requests) (forgery : ForgeryP) :
    PublicVerdict.Only (checkForgeryP publicKey log forgery) := by
  have hv (message : Message) (witness : WBytes) : PublicVerdict.Only (verifyP message publicKey witness) :=
    publicOnly_verifyP message publicKey witness
  have he (message : Message) (signature : Signature) : PublicVerdict.Only (expandB message publicKey signature) :=
    publicOnly_expandB message publicKey signature
  cases forgery with
  | witness message witness =>
      unfold checkForgeryP
      exact allQ_bind (hv message witness) fun _ => allQ_pure _
  | signature message signature =>
      unfold checkForgeryP
      apply allQ_bind (he message signature)
      intro witness
      cases witness with
      | none => exact allQ_pure _
      | some witness => exact allQ_bind (hv message witness) fun _ => allQ_pure _
theorem check_nonMac (publicKey : Digest) (log : QueryLog Requests) (forgery : ForgeryP) :
    FullGame.NonMac (checkForgeryP publicKey log forgery) := by
  apply SigGolfCandidate.T3M.allQ_mono (check_public publicKey log forgery)
  intro input h
  rcases input with (sample | input) | coordinate
  · exact h.elim
  · trivial
  · exact h.elim
noncomputable def checker : GameWith.Checker ForgeryP := ⟨checkForgeryP,check_nonMac⟩
theorem game_eq (adversary : AdversaryP) : GameWith.game checker adversary=gameP adversary := by
  unfold GameWith.game gameP
  apply bind_congr
  rintro ⟨publicKey,cache⟩
  unfold FullGame.loggedWith signingOracle
  simp only [monadLift_self]
  apply bind_congr
  rintro ⟨forgery,log⟩
  cases forgery <;> rfl
theorem realExperiment_eq (adversary : AdversaryP) :
    GameWith.realExperiment checker adversary=realExperimentP adversary := by
  unfold GameWith.realExperiment realExperimentP
  rw [game_eq]
theorem verdict_public (publicKey : Digest) (result : Option ForgeryP × QueryLog Requests) :
    PublicVerdict.Only (GameWith.verdict checker publicKey result) := by
  unfold GameWith.verdict
  cases result.1 with
  | none => exact allQ_pure _
  | some forgery => exact allQ_bind (check_public publicKey result.2 forgery) fun _ => allQ_pure _
abbrev TraceResult := Bool × (MonitoredPrivate.History × QueryRecorded.State)
noncomputable def tracedExperiment (adversary : AdversaryP) (budget : Nat) (hbudget : budget ≤ 2^127) :
    PMF TraceResult := GameWith.Recorded.tracedExperiment checker adversary budget hbudget
theorem real_to_clean_trace (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.1=true ∧ result.2 ≤ q | realExperimentP adversary] ≤
      Pr[QueryRecorded.CleanWin q | tracedExperiment adversary q hq]+
      q/(2 : ENNReal)^146+(2 : ENNReal)⁻¹^700+((2 : ENNReal)^152)⁻¹+
      q/((2^256 : Nat) : ENNReal) := by
  rw [show (QueryRecorded.CleanWin q : TraceResult → Prop)=(fun result =>
    result.1=true ∧ result.2.2.base.source.1 ≤ q ∧
      result.2.1.length ≤ BPORS.Numeric.proposalLength ∧ result.2.2.base.exceptional=false) from rfl]
  simpa only [realExperiment_eq,tracedExperiment] using
    GameWith.Recorded.real_to_clean_trace checker adversary q hq
theorem real_to_clean_without_known (reference : FirstHit.Reference) (adversary : AdversaryP)
    (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.1=true ∧ result.2 ≤ q | realExperimentP adversary] ≤
      Pr[fun result => QueryRecorded.CleanWin q result ∧
        ¬FirstHit.KnownPublicHit reference (QueryRecorded.recordedTrace result) |
        tracedExperiment adversary q hq]+
      q/(2 : ENNReal)^128+q/(2 : ENNReal)^146+(2 : ENNReal)⁻¹^700+
      ((2 : ENNReal)^152)⁻¹+q/((2^256 : Nat) : ENNReal) := by
  simpa only [realExperiment_eq,tracedExperiment,QueryRecorded.CleanWin] using
    GameWith.Recorded.real_to_clean_without_known checker reference adversary q hq
theorem traced_record_erasure (adversary : AdversaryP) (budget : Nat) (hbudget : budget ≤ 2^127) :
    QueryRecorded.recordedTrace <$> tracedExperiment adversary budget hbudget=
      (liftM (FirstHit.record (GameWith.idealGame checker adversary) (∅,∅)) : PMF _) :=
  GameWith.Recorded.traced_record_erasure checker adversary budget hbudget
theorem traced_cost_coherent (adversary : AdversaryP) (budget : Nat) (hbudget : budget ≤ 2^127)
    (result : TraceResult) (hr : result ∈ (tracedExperiment adversary budget hbudget).support) :
    QueryRecorded.CostCoherent result.2.2 :=
  GameWith.Recorded.traced_cost_coherent checker adversary budget hbudget result hr
end ClaudeWCT.W9.T3.Security.PaddedGame
end
section
namespace ClaudeWCT.W9.T3.Security.PaddedGame
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M.Final
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem large_budget (adversary : AdversaryP) (q : Nat) (hq : 2^127 ≤ q) :
    Pr[fun result => result.1=true ∧ result.2 ≤ q | realExperimentP adversary] ≤
      (q : ENNReal)/2^127 := by
  apply probEvent_le_one.trans
  have hcast : (2 : ENNReal)^127 ≤ (q : ENNReal) := by exact_mod_cast hq
  calc
    (1 : ENNReal) = (2 : ENNReal)^127/(2 : ENNReal)^127 := (ENNReal.div_self (by positivity) (by finiteness)).symm
    _ ≤ _ := ENNReal.div_le_div_right hcast _
theorem securityP_of_clean_bound
    (hclean : ∀ (adversary : AdversaryP) (q : Nat), 1 ≤ q → ∀ hq : q ≤ 2^127,
      Pr[QueryRecorded.CleanWin q | tracedExperiment adversary q hq]+
        q/(2 : ENNReal)^146+(2 : ENNReal)⁻¹^700+((2 : ENNReal)^152)⁻¹+
        q/((2^256 : Nat) : ENNReal) ≤ (q : ENNReal)/2^127) : SecurityP := by
  intro adversary q hpositive
  by_cases hq : 2^127 ≤ q
  · exact large_budget adversary q hq
  · have hsmall : q ≤ 2^127 := Nat.le_of_lt (Nat.lt_of_not_ge hq)
    exact (real_to_clean_trace adversary q hsmall).trans (hclean adversary q hpositive hsmall)
end ClaudeWCT.W9.T3.Security.PaddedGame
end
section
namespace ClaudeWCT.W9.T3.Security.CreationGame
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.BPORS.Adaptive
open SigGolfCandidate.T3.Security.CreationGame (publicClass prefixCount CountInvariant recorded_count_monotone
  recorded_world_hash_count prefixCount_le prefixCount_prefix_mono prefixCount_append_singleton prefixCount_disjoint)
open ClaudeWCT.W9.T3M.Final
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen
def publicHandler : QueryImpl SigGolfCandidate.T3.Spec (OracleComp LazyPrivate.Interaction)
  | .inl input => LazyPrivate.Interaction.query (.inl input)
  | .inr _ => pure (0 : HashOutput)
def publicProgram {α : Type} (program : M α) : OracleComp LazyPrivate.Interaction α :=
  simulateQ publicHandler program
theorem publicProgram_pure {α : Type} (value : α) :
    publicProgram (pure value : M α) = pure value := by
  simp [publicProgram]
theorem publicProgram_bind {α β : Type} (program : M α) (next : α → M β) :
    publicProgram (program >>= next) =
      (publicProgram program >>= fun value => publicProgram (next value)) := by
  simp only [publicProgram, simulateQ_bind]
theorem traced_world (published : SigGolfCandidate.T3.Cache) (budget : Nat) (hbudget : budget ≤ 2^127)
    (input : SphincsSecurity.OracleWorld.Domain)
    (state : MonitoredPrivate.History × QueryRecorded.State) :
    ((QueryRecorded.proposalModel published budget hbudget).traced (.inl input)).run state =
      (fun result => (result.1, (state.1, result.2))) <$>
        (liftM (QueryRecorded.run (forwardWorld input) state.2) : PMF _) := by
  rw [ProposalModel.traced_query_inactive _ _ _ (by rfl), QueryRecorded.proposal_query_erasure]
  rfl
theorem publicProgram_trace {α : Type} (published : SigGolfCandidate.T3.Cache) (budget : Nat)
    (hbudget : budget ≤ 2^127) (program : M α) (hp : PublicVerdict.Only program)
    (state : MonitoredPrivate.History × QueryRecorded.State) :
    (simulateQ (QueryRecorded.proposalModel published budget hbudget).traced
      (publicProgram program)).run state =
      (fun result => (result.1, (state.1, result.2))) <$>
        (liftM (QueryRecorded.run program state.2) : PMF _) := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [publicProgram_pure, simulateQ_pure, StateT.run_pure, QueryRecorded.run_pure,
        liftM_pure, PMF.monad_pure_eq_pure, PMF.monad_map_eq_map, PMF.pure_map]
  | query_bind input next ih =>
      change AllQueriesSatisfy _ PublicVerdict.IsPublicHash at hp
      rw [allQueriesSatisfy_query_bind_iff] at hp
      rcases input with (sample | input) | coordinate
      · exact False.elim hp.1
      · rw [publicProgram_bind]
        simp only [publicProgram, simulateQ_spec_query, publicHandler, simulateQ_bind,
          StateT.run_bind]
        rw [traced_world, bind_map_left, QueryRecorded.run_bind, liftM_bind, map_bind]
        apply bind_congr
        intro middle
        exact ih middle.1 (hp.2 middle.1) (state.1, middle.2)
      · exact False.elim hp.1
noncomputable def rest (adversary : AdversaryP) (publicKey : Digest) (published : SigGolfCandidate.T3.Cache) :
    OracleComp LazyPrivate.Interaction Bool := do
  let result ← ProposalOverflow.logged (adversary publicKey published)
  publicProgram (GameWith.verdict PaddedGame.checker publicKey result)
theorem rest_trace (adversary : AdversaryP) (published : SigGolfCandidate.T3.Cache) (publicKey : Digest)
    (budget : Nat) (hbudget : budget ≤ 2^127) (state : QueryRecorded.State) :
    (simulateQ (QueryRecorded.proposalModel published budget hbudget).traced
      (rest adversary publicKey published)).run ([], state) =
      (do
        let interaction ← (simulateQ (QueryRecorded.proposalModel published budget hbudget).traced
          (ProposalOverflow.logged (adversary publicKey published))).run ([], state)
        let checked ← (liftM (QueryRecorded.run
          (GameWith.verdict PaddedGame.checker publicKey interaction.1) interaction.2.2) : PMF _)
        pure (checked.1, interaction.2.1, checked.2)) := by
  rw [rest, simulateQ_bind, StateT.run_bind]
  apply bind_congr
  intro interaction
  rw [publicProgram_trace published budget hbudget _ (PaddedGame.verdict_public _ _)]
  rfl
theorem padded_trace_eq (adversary : AdversaryP) (budget : Nat) (hbudget : budget ≤ 2^127) :
    PaddedGame.tracedExperiment adversary budget hbudget =
      (do
        let generated ← (liftM (QueryRecorded.run keygen QueryRecorded.initial) : PMF _)
        (simulateQ (QueryRecorded.proposalModel generated.1.2 budget hbudget).traced
          (rest adversary generated.1.1 generated.1.2)).run ([], generated.2)) := by
  unfold PaddedGame.tracedExperiment GameWith.Recorded.tracedExperiment
  apply bind_congr
  intro generated
  exact (rest_trace adversary generated.1.2 generated.1.1 budget hbudget generated.2).symm
abbrev Weight := SigGolfCandidate.T3.Cache → LazyPrivate.Interaction.Domain →
  (MonitoredPrivate.History × QueryRecorded.State) → Nat
noncomputable def experiment (weight : Weight) (cap : Nat)
    (adversary : AdversaryP) (budget : Nat) (hbudget : budget ≤ 2^127) :
    PMF (Bool × (Nat × (MonitoredPrivate.History × QueryRecorded.State))) := do
  let generated ← (liftM (QueryRecorded.run keygen QueryRecorded.initial) : PMF _)
  (simulateQ ((QueryRecorded.proposalModel generated.1.2 budget hbudget).creationImpl
    (weight generated.1.2) cap) (rest adversary generated.1.1 generated.1.2)).run
      (0, [], generated.2)
theorem experiment_project (weight : Weight) (cap : Nat)
    (adversary : AdversaryP) (budget : Nat) (hbudget : budget ≤ 2^127) :
    Prod.map id Prod.snd <$> experiment weight cap adversary budget hbudget =
      PaddedGame.tracedExperiment adversary budget hbudget := by
  rw [experiment, map_bind, padded_trace_eq]
  apply bind_congr
  intro generated
  exact (QueryRecorded.proposalModel generated.1.2 budget hbudget).creation_program_project
    (weight generated.1.2) cap _ (0, [], generated.2)
theorem experiment_mass_le (weight : Weight) (cap : Nat)
    (adversary : AdversaryP) (budget : Nat) (hbudget : budget ≤ 2^127)
    (result : Bool × (Nat × (MonitoredPrivate.History × QueryRecorded.State)))
    (hr : result ∈ (experiment weight cap adversary budget hbudget).support) :
    result.2.1 ≤ cap := by
  rw [experiment, PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
  obtain ⟨generated, _, hr⟩ := hr
  exact (QueryRecorded.proposalModel generated.1.2 budget hbudget).creation_program_mass_le
    (weight generated.1.2) cap _ (0, [], generated.2) (Nat.zero_le _) result hr
end ClaudeWCT.W9.T3.Security.CreationGame
namespace ClaudeWCT.W9.T3.Security.CreationGame
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.BPORS.Adaptive
open SigGolfCandidate.T3.Security.CreationGame (publicClass prefixCount CountInvariant recorded_count_monotone
  recorded_world_hash_count prefixCount_le prefixCount_prefix_mono prefixCount_append_singleton prefixCount_disjoint)
open ClaudeWCT.W9.T3M.Final (AdversaryP)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable def classWeight (cls : HashInput → Prop) (budget : Nat) :
    LazyPrivate.Interaction.Domain → (MonitoredPrivate.History × QueryRecorded.State) → Nat
  | .inl (.inr input), state =>
      if state.2.base.source.1 < budget ∧ cls input ∧ state.2.base.source.2.2 input = none
        then 1 else 0
  | _, _ => 0
theorem classWeight_le_one (cls : HashInput → Prop) (budget : Nat)
    (input : LazyPrivate.Interaction.Domain) (state : MonitoredPrivate.History × QueryRecorded.State) :
    classWeight cls budget input state ≤ 1 := by
  rcases input with (sample | input) | request
  · exact Nat.zero_le _
  · change (if state.2.base.source.1 < budget ∧ cls input ∧
      state.2.base.source.2.2 input = none then 1 else 0) ≤ 1
    split_ifs <;> omega
  · exact Nat.zero_le _
theorem class_creationStep_eq (cls : HashInput → Prop) (budget : Nat)
    (input : LazyPrivate.Interaction.Domain)
    (state : Nat × (MonitoredPrivate.History × QueryRecorded.State))
    (hcost : state.1 ≤ state.2.2.base.source.1) :
    ProposalModel.creationStep (classWeight cls budget) budget input state =
      classWeight cls budget input state.2 := by
  unfold ProposalModel.creationStep
  apply Nat.min_eq_left
  rcases input with (sample | input) | request
  · exact Nat.zero_le _
  · change (if state.2.2.base.source.1 < budget ∧ cls input ∧
      state.2.2.base.source.2.2 input = none then 1 else 0) ≤ budget - state.1
    split_ifs with h
    · omega
    · exact Nat.zero_le _
  · exact Nat.zero_le _
theorem traced_query_source_support (published : SigGolfCandidate.T3.Cache) (budget : Nat)
    (hbudget : budget ≤ 2^127) (input : LazyPrivate.Interaction.Domain)
    (before : MonitoredPrivate.History × QueryRecorded.State)
    (result : LazyPrivate.Interaction.Range input × (MonitoredPrivate.History × QueryRecorded.State))
    (hr : result ∈ (((QueryRecorded.proposalModel published budget hbudget).traced input).run before).support) :
    (result.1, result.2.2) ∈ support
      (QueryRecorded.run (MonitoredPrivate.interactionSource published input) before.2) := by
  rw [← MonitoredPrivate.pmf_support,
    ← QueryRecorded.proposal_query_erasure published budget hbudget input before.2,
    ← (QueryRecorded.proposalModel published budget hbudget).traced_query_erasure input before,
    PMF.monad_map_eq_map, PMF.mem_support_map_iff]
  exact ⟨result, hr, rfl⟩
theorem class_creation_query_cost (published : SigGolfCandidate.T3.Cache) (budget : Nat)
    (hbudget : budget ≤ 2^127) (cls : HashInput → Prop)
    (input : LazyPrivate.Interaction.Domain)
    (before : Nat × (MonitoredPrivate.History × QueryRecorded.State))
    (hcost : before.1 ≤ before.2.2.base.source.1)
    (result : LazyPrivate.Interaction.Range input ×
      (Nat × (MonitoredPrivate.History × QueryRecorded.State)))
    (hr : result ∈ (((QueryRecorded.proposalModel published budget hbudget).creationImpl
      (classWeight cls budget) budget input).run before).support) :
    result.2.1 ≤ result.2.2.2.base.source.1 := by
  rw [ProposalModel.creationImpl, StateT.run_mk, PMF.monad_map_eq_map,
    PMF.mem_support_map_iff] at hr
  obtain ⟨middle, hm, rfl⟩ := hr
  have hs := traced_query_source_support published budget hbudget input before.2 middle hm
  have hmon := recorded_count_monotone _ before.2.2 (middle.1, middle.2.2) hs
  change before.1 + ProposalModel.creationStep (classWeight cls budget) budget input before ≤ _
  rw [class_creationStep_eq cls budget input before hcost]
  rcases input with (sample | input) | request
  · simpa only [classWeight, Nat.add_zero] using hcost.trans hmon
  · have hc := recorded_world_hash_count input before.2.2 (middle.1, middle.2.2) hs
    rw [hc]
    exact Nat.add_le_add hcost (classWeight_le_one cls budget (.inl (.inr input)) before.2)
  · simpa only [classWeight, Nat.add_zero] using hcost.trans hmon
theorem class_creation_program_cost {α : Type} (published : SigGolfCandidate.T3.Cache) (budget : Nat)
    (hbudget : budget ≤ 2^127) (cls : HashInput → Prop)
    (program : OracleComp LazyPrivate.Interaction α)
    (before : Nat × (MonitoredPrivate.History × QueryRecorded.State))
    (hcost : before.1 ≤ before.2.2.base.source.1)
    (result : α × (Nat × (MonitoredPrivate.History × QueryRecorded.State)))
    (hr : result ∈ ((simulateQ ((QueryRecorded.proposalModel published budget hbudget).creationImpl
      (classWeight cls budget) budget) program).run before).support) :
    result.2.1 ≤ result.2.2.2.base.source.1 := by
  induction program using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure,
        PMF.mem_support_pure_iff] at hr
      subst result
      exact hcost
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
      obtain ⟨middle, hm, hr⟩ := hr
      exact ih middle.1 middle.2
        (class_creation_query_cost published budget hbudget cls input before hcost middle hm) hr
theorem class_experiment_cost (cls : HashInput → Prop)
    (adversary : AdversaryP)
    (budget : Nat) (hbudget : budget ≤ 2^127)
    (result : Bool × (Nat × (MonitoredPrivate.History × QueryRecorded.State)))
    (hr : result ∈ (experiment (fun _ => classWeight cls budget) budget adversary budget hbudget).support) :
    result.2.1 ≤ result.2.2.2.base.source.1 := by
  rw [experiment, PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
  obtain ⟨generated, _, hr⟩ := hr
  exact class_creation_program_cost generated.1.2 budget hbudget cls _
    (0, [], generated.2) (Nat.zero_le _) result hr
theorem class_program_mass_eq {α : Type} (published : SigGolfCandidate.T3.Cache) (budget : Nat)
    (hbudget : budget ≤ 2^127) (cls : HashInput → Prop)
    (program : OracleComp LazyPrivate.Interaction α)
    (before : MonitoredPrivate.History × QueryRecorded.State) :
    expectedValue ((simulateQ ((QueryRecorded.proposalModel published budget hbudget).creationImpl
      (classWeight cls budget) budget) program).run (0, before))
      (fun result => (result.2.1 : ENNReal)) =
      Creation.expectedCharges (QueryRecorded.proposalModel published budget hbudget).traced
        (fun input state => (classWeight cls budget input state : ENNReal)) program before := by
  let model := QueryRecorded.proposalModel published budget hbudget
  apply le_antisymm
  · exact model.creation_mass_le_source_charges (classWeight cls budget) budget program before
  · have hp := Creation.expectedCharges_project (model.creationImpl (classWeight cls budget) budget)
      model.traced Prod.snd (model.creation_query_project (classWeight cls budget) budget)
      (fun input state => (classWeight cls budget input state : ENNReal)) program (0, before)
    calc
      _ = Creation.expectedCharges (model.creationImpl (classWeight cls budget) budget)
          (fun input state => (classWeight cls budget input state.2 : ENNReal))
          program (0, before) := hp.symm
      _ ≤ Creation.expectedCharges (model.creationImpl (classWeight cls budget) budget)
          (fun input state => (ProposalModel.creationStep (classWeight cls budget) budget input state : ENNReal))
          program (0, before) := by
        apply Creation.expectedCharges_mono _ _ _
          (fun state => state.1 ≤ state.2.2.base.source.1)
          (class_creation_query_cost published budget hbudget cls) _ _ _ (Nat.zero_le _)
        intro input state hcost
        exact le_of_eq (congrArg (fun value : Nat => (value : ENNReal))
          (class_creationStep_eq cls budget input state hcost)).symm
      _ = _ := (model.creation_program_mass (classWeight cls budget) budget program before).symm
noncomputable def expectedBirths (cls : HashInput → Prop)
    (adversary : AdversaryP)
    (budget : Nat) (hbudget : budget ≤ 2^127) : ENNReal :=
  expectedValue (liftM (QueryRecorded.run keygen QueryRecorded.initial) : PMF _)
    (fun generated =>
      Creation.expectedCharges (QueryRecorded.proposalModel generated.1.2 budget hbudget).traced
        (fun input state => (classWeight cls budget input state : ENNReal))
        (rest adversary generated.1.1 generated.1.2) ([], generated.2))
theorem expectedBirths_eq_mass (cls : HashInput → Prop)
    (adversary : AdversaryP)
    (budget : Nat) (hbudget : budget ≤ 2^127) :
    expectedBirths cls adversary budget hbudget =
      expectedValue (experiment (fun _ => classWeight cls budget) budget adversary budget hbudget)
        (fun result => (result.2.1 : ENNReal)) := by
  rw [expectedBirths, experiment, expectedValue_bind]
  congr 1
  funext generated
  exact (class_program_mass_eq generated.1.2 budget hbudget cls _ ([], generated.2)).symm
end ClaudeWCT.W9.T3.Security.CreationGame
namespace ClaudeWCT.W9.T3.Security.CreationGame
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.BPORS.Adaptive
open SigGolfCandidate.T3.Security.CreationGame (publicClass prefixCount CountInvariant recorded_count_monotone
  recorded_world_hash_count prefixCount_le prefixCount_prefix_mono prefixCount_append_singleton prefixCount_disjoint)
open ClaudeWCT.W9.T3M.Final (AdversaryP)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem class_source_count_step (published : SigGolfCandidate.T3.Cache) (budget : Nat)
    (cls : HashInput → Prop) (input : LazyPrivate.Interaction.Domain)
    (before : MonitoredPrivate.History × QueryRecorded.State)
    (hcoherent : QueryRecorded.CostCoherent before.2)
    (result : LazyPrivate.Interaction.Range input × QueryRecorded.State)
    (hr : result ∈ support
      (QueryRecorded.run (MonitoredPrivate.interactionSource published input) before.2)) :
    prefixCount (publicClass cls) budget before.2.events + classWeight cls budget input before ≤
      prefixCount (publicClass cls) budget result.2.events := by
  have hmono := prefixCount_prefix_mono (publicClass cls) budget
    (QueryRecorded.run_events_extend _ before.2 result hr)
  rcases input with (sample | input) | request
  · simpa only [classWeight, Nat.add_zero] using hmono
  · by_cases hb : before.2.base.source.1 < budget ∧ cls input ∧
        before.2.base.source.2.2 input = none
    · have hweight : classWeight cls budget (.inl (.inr input)) before = 1 := by
        change (if _ then 1 else 0) = 1
        exact if_pos hb
      rw [hweight]
      change result ∈ support
        (QueryRecorded.run (liftM (SigGolfCandidate.T3.Spec.query (.inl (.inr input)))) before.2) at hr
      rw [QueryRecorded.run_query_explicit, support_map] at hr
      obtain ⟨middle, _, rfl⟩ := hr
      change _ ≤ prefixCount (publicClass cls) budget
        (before.2.events ++ [⟨before.2.base.source.2, .inl (.inr input), middle.1⟩])
      rw [prefixCount_append_singleton]
      · simp only [publicClass, hb.2.1, if_true]
        rfl
      · change (before.2.events.map (fun event => FullGame.queryCharge event.input)).sum + 1 ≤ budget
        rw [← hcoherent]
        omega
    · have hweight : classWeight cls budget (.inl (.inr input)) before = 0 := by
        change (if _ then 1 else 0) = 0
        exact if_neg hb
      simpa only [hweight, Nat.add_zero] using hmono
  · simpa only [classWeight, Nat.add_zero] using hmono
theorem class_creation_query_count (published : SigGolfCandidate.T3.Cache) (budget : Nat)
    (hbudget : budget ≤ 2^127) (cls : HashInput → Prop)
    (input : LazyPrivate.Interaction.Domain)
    (before : Nat × (MonitoredPrivate.History × QueryRecorded.State))
    (hinv : CountInvariant cls budget before)
    (result : LazyPrivate.Interaction.Range input ×
      (Nat × (MonitoredPrivate.History × QueryRecorded.State)))
    (hr : result ∈ (((QueryRecorded.proposalModel published budget hbudget).creationImpl
      (classWeight cls budget) budget input).run before).support) :
    CountInvariant cls budget result.2 := by
  rw [ProposalModel.creationImpl, StateT.run_mk, PMF.monad_map_eq_map,
    PMF.mem_support_map_iff] at hr
  obtain ⟨middle, hm, rfl⟩ := hr
  have hs := traced_query_source_support published budget hbudget input before.2 middle hm
  refine ⟨QueryRecorded.run_cost_coherent _ before.2.2 hinv.1 (middle.1, middle.2.2) hs, ?_⟩
  exact (Nat.add_le_add hinv.2 (Nat.min_le_left _ _)).trans
    (class_source_count_step published budget cls input before.2 hinv.1 (middle.1, middle.2.2) hs)
theorem class_creation_program_count {α : Type} (published : SigGolfCandidate.T3.Cache) (budget : Nat)
    (hbudget : budget ≤ 2^127) (cls : HashInput → Prop)
    (program : OracleComp LazyPrivate.Interaction α)
    (before : Nat × (MonitoredPrivate.History × QueryRecorded.State))
    (hinv : CountInvariant cls budget before)
    (result : α × (Nat × (MonitoredPrivate.History × QueryRecorded.State)))
    (hr : result ∈ ((simulateQ ((QueryRecorded.proposalModel published budget hbudget).creationImpl
      (classWeight cls budget) budget) program).run before).support) :
    CountInvariant cls budget result.2 := by
  induction program using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure,
        PMF.mem_support_pure_iff] at hr
      subst result
      exact hinv
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
      obtain ⟨middle, hm, hr⟩ := hr
      exact ih middle.1 middle.2
        (class_creation_query_count published budget hbudget cls input before hinv middle hm) hr
theorem class_experiment_count (cls : HashInput → Prop)
    (adversary : AdversaryP)
    (budget : Nat) (hbudget : budget ≤ 2^127)
    (result : Bool × (Nat × (MonitoredPrivate.History × QueryRecorded.State)))
    (hr : result ∈ (experiment (fun _ => classWeight cls budget) budget adversary budget hbudget).support) :
    result.2.1 ≤ prefixCount (publicClass cls) budget result.2.2.2.events := by
  rw [experiment, PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
  obtain ⟨generated, hg, hr⟩ := hr
  rw [MonitoredPrivate.pmf_support] at hg
  have hc := QueryRecorded.run_cost_coherent keygen QueryRecorded.initial
    QueryRecorded.initial_cost generated hg
  exact (class_creation_program_count generated.1.2 budget hbudget cls _
    (0, [], generated.2) ⟨hc, Nat.zero_le _⟩ result hr).2
noncomputable def expectedClassCount (cls : SigGolfCandidate.T3.Spec.Domain → Prop)
    (adversary : AdversaryP)
    (budget : Nat) (hbudget : budget ≤ 2^127) : ENNReal :=
  expectedValue (PaddedGame.tracedExperiment adversary budget hbudget)
    (fun result => (prefixCount cls budget result.2.2.events : ENNReal))
theorem expectedBirths_le_classCount (cls : HashInput → Prop)
    (adversary : AdversaryP)
    (budget : Nat) (hbudget : budget ≤ 2^127) :
    expectedBirths cls adversary budget hbudget ≤
      expectedClassCount (publicClass cls) adversary budget hbudget := by
  rw [expectedBirths_eq_mass, expectedClassCount,
    ← experiment_project (fun _ => classWeight cls budget) budget adversary budget hbudget,
    expectedValue_map]
  unfold expectedValue
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ (experiment (fun _ => classWeight cls budget) budget adversary budget hbudget).support
  · apply mul_le_mul' le_rfl
    change (result.2.1 : ENNReal) ≤
      (prefixCount (publicClass cls) budget result.2.2.2.events : ENNReal)
    exact_mod_cast class_experiment_count cls adversary budget hbudget result hr
  · have hp : Pr[= result | experiment (fun _ => classWeight cls budget) budget adversary budget hbudget] = 0 := by
      rw [PMF.probOutput_eq_apply, PMF.apply_eq_zero_iff]
      exact hr
    rw [hp, zero_mul, zero_mul]
theorem expectedClassCount_le (cls : SigGolfCandidate.T3.Spec.Domain → Prop)
    (adversary : AdversaryP)
    (budget : Nat) (hbudget : budget ≤ 2^127) :
    expectedClassCount cls adversary budget hbudget ≤ (budget : ENNReal) := by
  unfold expectedClassCount
  calc
    _ ≤ expectedValue (PaddedGame.tracedExperiment adversary budget hbudget)
        (fun _ => (budget : ENNReal)) := by
      apply expectedValue_mono
      intro result
      exact_mod_cast prefixCount_le cls budget result.2.2.events
    _ = _ := expectedValue_const (by simp) _
theorem expectedClassCount_disjoint (first second : SigGolfCandidate.T3.Spec.Domain → Prop)
    (hdisjoint : ∀ input, ¬ (first input ∧ second input))
    (adversary : AdversaryP)
    (budget : Nat) (hbudget : budget ≤ 2^127) :
    expectedClassCount (fun input => first input ∨ second input) adversary budget hbudget =
      expectedClassCount first adversary budget hbudget +
        expectedClassCount second adversary budget hbudget := by
  unfold expectedClassCount
  simp_rw [prefixCount_disjoint first second hdisjoint, Nat.cast_add]
  exact expectedValue_add _ _ _
end ClaudeWCT.W9.T3.Security.CreationGame
end

section
namespace ClaudeWCT.W9.T3.Security.PairedOuter.GameWith
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity (OracleWorld romImpl sampleMasterSeed)
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.FullGame
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _
noncomputable local instance : DecidableEq SiggolfT3Mac4.Cache := Classical.decEq _
noncomputable local instance : DecidableEq Region := Classical.decEq _
noncomputable local instance : Fintype Coordinate := coordinateFintype
noncomputable local instance : Fintype OtherCoordinate := otherFintype
noncomputable local instance : Fintype Region := CacheAuthentication.regionFintype
noncomputable local instance : SampleableType FullTable := Derivation.outputSampler Coordinate
noncomputable local instance : SampleableType OtherTable := otherSampler
noncomputable local instance : SampleableType MacTable := CacheAuthentication.macTableSampler
structure Checker (Forgery : Type) where
  check : Digest → QueryLog Requests → Forgery → M Bool
  nonMac : ∀ pk log forgery, NonMac (check pk log forgery)
variable {Forgery : Type}
abbrev AdversaryFor (Forgery : Type) :=
  Digest → SigGolfCandidate.T3.Cache → OracleComp LazyPrivate.Interaction (Option Forgery)
noncomputable def verdict (checker : Checker Forgery) (publicKey : Digest)
    (result : Option Forgery × QueryLog Requests) : M Bool := do
  let some forgery := result.1 | return false
  let verified ← checker.check publicKey result.2 forgery
  pure (decide (result.2.length ≤ 2^32) && verified)
theorem verdict_nonMac (checker : Checker Forgery) (publicKey : Digest)
    (result : Option Forgery × QueryLog Requests) : NonMac (verdict checker publicKey result) := by
  unfold verdict
  cases result.1 with
  | none => exact SourceQueries.pure_allowed _ _
  | some forgery =>
      exact SourceQueries.bind_allowed _ (checker.nonMac publicKey result.2 forgery)
        (fun _ => SourceQueries.pure_allowed _ _)
noncomputable def game (checker : Checker Forgery) (adversary : AdversaryFor Forgery) : M Bool := do
  let generated ← keygen
  let result ← FullGame.loggedWith (fun request => sign request.cache request.message)
    (adversary generated.1 generated.2)
  verdict checker generated.1 result
noncomputable def realExperiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery) :
    ProbComp (Bool × Nat) :=
  sampleMasterSeed >>= fun secret =>
    (simulateQ romImpl (SphincsSecurity.countHashQueries
      (Derivation.realize (privateInput secret) (game checker adversary)))).run' ∅
noncomputable def tableExperiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery)
    (q : Nat) : ProbComp (Option (Bool × Nat)) :=
  ($ᵗ FullTable : ProbComp _) >>= fun outputs =>
    (simulateQ romImpl (Derivation.tableRun outputs (Derivation.cap (game checker adversary) q))).run' ∅
theorem private_derivation_event_bound (checker : Checker Forgery)
    (adversary : AdversaryFor Forgery) (q : Nat) (hq : q < 2^256) :
    Pr[fun result => result.1=true ∧ result.2 ≤ q | realExperiment checker adversary] ≤
      Pr[fun outcome => ∃ result, outcome=some result ∧ result.1=true |
        tableExperiment checker adversary q] + q / ((2^256 : Nat) : ENNReal) :=
  Derivation.event_game_hop privateInput privateInput_injective
    privateInput_hit (game checker adversary) q hq (· = true)
noncomputable def countedTableExperiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery) : ProbComp (Bool × CountState) := do
  let table ← ($ᵗ FullTable : ProbComp _)
  run table (game checker adversary) (0,∅)
theorem counted_table_event (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) :
    Pr[fun result => result.1=true ∧ result.2.1≤q | countedTableExperiment checker adversary]=
      Pr[fun outcome => ∃ result,outcome=some result ∧ result.1=true | tableExperiment checker adversary q] := by
  unfold countedTableExperiment tableExperiment
  simp only [probEvent_bind_eq_tsum]
  apply tsum_congr
  intro table
  apply congrArg
  exact table_cap_event table (game checker adversary) ∅ q (·=true)
theorem real_to_counted_table (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) (hq : q < 2^256) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment checker adversary] ≤
      Pr[fun result => result.1=true ∧ result.2.1≤q | countedTableExperiment checker adversary]+
        q/((2^256 : Nat) : ENNReal) := by
  rw [counted_table_event]
  exact private_derivation_event_bound checker adversary q hq
noncomputable def splitTableExperiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery) : ProbComp (Bool × CountState) := do
  let other ← ($ᵗ OtherTable : ProbComp _)
  let mac ← ($ᵗ MacTable : ProbComp _)
  run (joinTable other mac) (game checker adversary) (0,∅)
theorem table_experiment_split (checker : Checker Forgery) (adversary : AdversaryFor Forgery) :
    𝒮[countedTableExperiment checker adversary]=𝒮[splitTableExperiment checker adversary] :=
  uniform_table_split_bind (fun table => run table (game checker adversary) (0,∅))
noncomputable def checkContinuation (checker : Checker Forgery) (other : OtherTable) (publicKey : Digest)
    (result : (Option Forgery × QueryLog Requests) × CountState) : ProbComp (Bool × CountState) :=
  (simulateQ (baseHandler other) (verdict checker publicKey result.1)).run result.2
noncomputable def realRest (checker : Checker Forgery) (other : OtherTable) (mac : MacTable) (adversary : AdversaryFor Forgery)
    (publicKey : Digest) (published : SigGolfCandidate.T3.Cache) (state : CountState) : ProbComp (Bool × CountState) :=
  RequestHop.run (worldHandler other) (MacGame.realSigner (baseHandler other) mac)
    (adversary publicKey published) state >>= checkContinuation checker other publicKey
noncomputable def idealRest (checker : Checker Forgery) (other : OtherTable) (adversary : AdversaryFor Forgery)
    (publicKey : Digest) (published : SigGolfCandidate.T3.Cache) (state : CountState) : ProbComp (Bool × CountState) :=
  RequestHop.run (worldHandler other) (MacGame.idealSigner (baseHandler other) published)
    (adversary publicKey published) state >>= checkContinuation checker other publicKey
theorem logged_source_run (other : OtherTable) (mac : MacTable)
    (program : OracleComp LazyPrivate.Interaction (Option Forgery)) (state : CountState) :
    (simulateQ (MacGame.sourceHandler (baseHandler other) mac) (FullGame.loggedWith (fun request => sign request.cache request.message) program)).run state=
      RequestHop.run (worldHandler other) (MacGame.realSigner (baseHandler other) mac) program state := by
  rw [FullGame.loggedWith_interpretation]
  change RequestHop.run (worldHandler other)
    (fun request => simulateQ (MacGame.sourceHandler (baseHandler other) mac)
      (sign request.cache request.message)) program state=_
  exact congrArg (fun signer => RequestHop.run (worldHandler other) signer program state)
    (funext fun request => MacGame.source_signer_eq (baseHandler other) mac request)
theorem source_rest_run (checker : Checker Forgery) (other : OtherTable) (mac : MacTable) (adversary : AdversaryFor Forgery)
    (publicKey : Digest) (published : SigGolfCandidate.T3.Cache) (state : CountState) :
    (simulateQ (MacGame.sourceHandler (baseHandler other) mac) (do
      let result ← FullGame.loggedWith (fun request => sign request.cache request.message) (adversary publicKey published)
      verdict checker publicKey result)).run state=
      realRest checker other mac adversary publicKey published state := by
  rw [simulateQ_bind,StateT.run_bind,logged_source_run]
  unfold realRest
  apply bind_congr
  intro result
  rw [MacGame.simulate_no_mac _ _ _ (verdict_nonMac checker publicKey result.1)]
  rfl
theorem fixed_game_expansion (checker : Checker Forgery) (other : OtherTable) (mac : MacTable) (adversary : AdversaryFor Forgery) :
    run (joinTable other mac) (game checker adversary) (0,∅)=
      (do
        let generated ← (simulateQ (baseHandler other) keygenPayload).run (0,∅)
        realRest checker other mac adversary generated.1.1 ⟨MacGame.tagAt mac generated.1.2,generated.1.2⟩
          (generated.2.1+2,generated.2.2)) := by
  rw [run,tableHandler_split,game]
  simp only [keygen,bind_assoc,pure_bind,simulateQ_bind,StateT.run_bind]
  rw [MacGame.simulate_no_mac _ _ _ keygenPayload_nonMac]
  apply bind_congr
  intro generated
  rw [source_mac_run,pure_bind]
  simpa only [simulateQ_bind,StateT.run_bind] using
    source_rest_run checker other mac adversary generated.1.1
      ⟨MacGame.tagAt mac generated.1.2,generated.1.2⟩ (generated.2.1+2,generated.2.2)
theorem refresh_published_mac (checker : Checker Forgery) (other : OtherTable) (adversary : AdversaryFor Forgery)
    (generated : (Digest × Region) × CountState) :
    𝒮[do
      let mac ← ($ᵗ MacTable : ProbComp _)
      realRest checker other mac adversary generated.1.1 ⟨MacGame.tagAt mac generated.1.2,generated.1.2⟩
        (generated.2.1+2,generated.2.2)]=
    𝒮[do
      let tag ← ($ᵗ HashOutput : ProbComp _)
      let mac ← ($ᵗ MacTable : ProbComp _)
      realRest checker other (MacGame.retag mac ⟨tag,generated.1.2⟩) adversary
        generated.1.1 ⟨tag,generated.1.2⟩ (generated.2.1+2,generated.2.2)] := by
  exact MacGame.refresh_published generated.1.2 (fun tag mac =>
    realRest checker other mac adversary generated.1.1 ⟨tag,generated.1.2⟩
      (generated.2.1+2,generated.2.2))
noncomputable def preparedExperiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery) : ProbComp (Bool × CountState) := do
  let prepared ← setup
  let mac ← ($ᵗ MacTable : ProbComp _)
  realRest checker prepared.other (MacGame.retag mac prepared.published)
    adversary prepared.publicKey prepared.published prepared.state
noncomputable def authenticatedExperiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery) : ProbComp (Bool × CountState) := do
  let prepared ← setup
  idealRest checker prepared.other adversary prepared.publicKey prepared.published prepared.state
theorem split_experiment_prepared (checker : Checker Forgery) (adversary : AdversaryFor Forgery) :
    𝒮[splitTableExperiment checker adversary]=𝒮[preparedExperiment checker adversary] := by
  unfold splitTableExperiment preparedExperiment setup
  simp only [bind_assoc,pure_bind]
  apply evalSPMF_bind_congr'
  intro other
  simp_rw [fixed_game_expansion]
  rw [evalSPMF_bind_bind_swap]
  apply evalSPMF_bind_congr'
  intro generated
  exact refresh_published_mac checker other adversary generated
theorem checkContinuation_long (checker : Checker Forgery) (other : OtherTable) (publicKey : Digest)
    (result : (Option Forgery × QueryLog Requests) × CountState)
    (hlong : 2^32 < result.1.2.length) (q : Nat) :
    Pr[fun outcome => outcome.1=true ∧ outcome.2.1≤q | checkContinuation checker other publicKey result]=0 := by
  have hn : ¬result.1.2.length≤2^32 := Nat.not_le.mpr hlong
  unfold checkContinuation verdict
  cases result.1.1 with
  | none => simp [StateT.run_pure]
  | some forgery =>
      simp
      intro count cache _ hshort
      exact False.elim (hn hshort)
theorem rest_authentication_bound (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (prepared : Setup) (q : Nat) :
    Pr[fun result => result.1=true ∧ result.2.1≤q | do
      let mac ← ($ᵗ MacTable : ProbComp _)
      realRest checker prepared.other (MacGame.retag mac prepared.published)
        adversary prepared.publicKey prepared.published prepared.state] ≤
    Pr[fun result => result.1=true ∧ result.2.1≤q |
      idealRest checker prepared.other adversary prepared.publicKey prepared.published prepared.state]+
      ((2 : ENNReal)^152)⁻¹ := by
  have h := MacGame.authentication_hop (worldHandler prepared.other) (baseHandler prepared.other)
    prepared.published (adversary prepared.publicKey prepared.published) (2^32) prepared.state
    (checkContinuation checker prepared.other prepared.publicKey) (fun result => result.1=true ∧ result.2.1≤q)
    (fun result hlong => checkContinuation_long checker prepared.other prepared.publicKey result hlong q)
  refine h.trans (add_le_add le_rfl ?_)
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_pow]
theorem prepared_authentication_bound (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) :
    Pr[fun result => result.1=true ∧ result.2.1≤q | preparedExperiment checker adversary] ≤
      Pr[fun result => result.1=true ∧ result.2.1≤q | authenticatedExperiment checker adversary]+
        ((2 : ENNReal)^152)⁻¹ :=
  probEvent_bind_le_add setup _ _ _ _ (fun prepared => rest_authentication_bound checker adversary prepared q)
theorem real_to_authenticated (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) (hq : q < 2^256) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment checker adversary] ≤
      Pr[fun result => result.1=true ∧ result.2.1≤q | authenticatedExperiment checker adversary]+
        ((2 : ENNReal)^152)⁻¹+q/((2^256 : Nat) : ENNReal) := by
  have h := real_to_counted_table checker adversary q hq
  have he := (table_experiment_split checker adversary).trans (split_experiment_prepared checker adversary)
  have hp : Pr[fun result => result.1=true ∧ result.2.1≤q | countedTableExperiment checker adversary]=
      Pr[fun result => result.1=true ∧ result.2.1≤q | preparedExperiment checker adversary] :=
    probEvent_congr' (fun _ _ => Iff.rfl) he
  rw [hp] at h
  exact h.trans (add_le_add (prepared_authentication_bound checker adversary q) le_rfl)
noncomputable def idealGame (checker : Checker Forgery) (adversary : AdversaryFor Forgery) : M Bool := do
  let generated ← keygen
  let result ← FullGame.loggedWith (FullGame.authenticatedSign generated.2) (adversary generated.1 generated.2)
  verdict checker generated.1 result
theorem ideal_rest_run (checker : Checker Forgery) (other : OtherTable) (mac : MacTable) (adversary : AdversaryFor Forgery)
    (publicKey : Digest) (published : SigGolfCandidate.T3.Cache) (state : CountState) :
    (simulateQ (MacGame.sourceHandler (baseHandler other) mac) (do
      let result ← FullGame.loggedWith (FullGame.authenticatedSign published) (adversary publicKey published)
      verdict checker publicKey result)).run state=idealRest checker other adversary publicKey published state := by
  rw [simulateQ_bind,StateT.run_bind,FullGame.loggedWith_interpretation]
  have hs : (fun request => simulateQ (MacGame.sourceHandler (baseHandler other) mac)
      (FullGame.authenticatedSign published request))=MacGame.idealSigner (baseHandler other) published :=
    funext fun request => FullGame.authenticatedSign_interpretation other mac published request
  rw [hs]
  change RequestHop.run (worldHandler other) (MacGame.idealSigner (baseHandler other) published)
    (adversary publicKey published) state >>= _ = _
  unfold idealRest
  apply bind_congr
  intro result
  rw [MacGame.simulate_no_mac _ _ _ (verdict_nonMac checker publicKey result.1)]
  rfl
theorem fixed_ideal_expansion (checker : Checker Forgery) (other : OtherTable) (mac : MacTable) (adversary : AdversaryFor Forgery) :
    run (joinTable other mac) (idealGame checker adversary) (0,∅)=
      (do
        let generated ← (simulateQ (baseHandler other) keygenPayload).run (0,∅)
        idealRest checker other adversary generated.1.1 ⟨MacGame.tagAt mac generated.1.2,generated.1.2⟩
          (generated.2.1+2,generated.2.2)) := by
  rw [run,tableHandler_split,idealGame]
  simp only [keygen,bind_assoc,pure_bind,simulateQ_bind,StateT.run_bind]
  rw [MacGame.simulate_no_mac _ _ _ keygenPayload_nonMac]
  apply bind_congr
  intro generated
  rw [source_mac_run,pure_bind]
  simpa only [simulateQ_bind,StateT.run_bind] using
    ideal_rest_run checker other mac adversary generated.1.1
      ⟨MacGame.tagAt mac generated.1.2,generated.1.2⟩ (generated.2.1+2,generated.2.2)
noncomputable def idealTableExperiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery) : ProbComp (Bool × CountState) := do
  let table ← ($ᵗ FullTable : ProbComp _)
  run table (idealGame checker adversary) (0,∅)
theorem ideal_table_authenticated (checker : Checker Forgery) (adversary : AdversaryFor Forgery) :
    𝒮[idealTableExperiment checker adversary]=𝒮[authenticatedExperiment checker adversary] := by
  unfold idealTableExperiment
  rw [uniform_table_split_bind]
  unfold authenticatedExperiment setup
  simp only [bind_assoc,pure_bind]
  apply evalSPMF_bind_congr'
  intro other
  simp_rw [fixed_ideal_expansion]
  rw [evalSPMF_bind_bind_swap]
  apply evalSPMF_bind_congr'
  intro generated
  exact sample_mac_at_bind generated.1.2 (fun tag =>
    idealRest checker other adversary generated.1.1 ⟨tag,generated.1.2⟩ (generated.2.1+2,generated.2.2))
noncomputable def idealLazyExperiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery) :
    ProbComp ((Bool × Nat) × LazyPrivate.State) :=
  LazyPrivate.run (SphincsSecurity.QueryCap.counted Derivation.charged (idealGame checker adversary)) (∅,∅)
theorem ideal_lazy_event (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) :
    Pr[fun result => result.1.1=true ∧ result.1.2≤q | idealLazyExperiment checker adversary]=
      Pr[fun result => result.1=true ∧ result.2.1≤q | authenticatedExperiment checker adversary] := by
  have h := LazyPrivate.run_eq_table
    (SphincsSecurity.QueryCap.counted Derivation.charged (idealGame checker adversary)) ∅
  have hp : Pr[fun result => result.1.1=true ∧ result.1.2≤q |
      Prod.map id Prod.snd <$> idealLazyExperiment checker adversary]=
      Pr[fun result => result.1.1=true ∧ result.1.2≤q | do
        let table ← ($ᵗ FullTable : ProbComp _)
        (simulateQ romImpl (Derivation.tableRun table
          (SphincsSecurity.QueryCap.counted Derivation.charged (idealGame checker adversary)))).run ∅] :=
    probEvent_congr' (fun _ _ => Iff.rfl) h
  simp only [probEvent_map,Prod.map,id_eq,Function.comp_def] at hp
  rw [hp]
  have he : Pr[fun result => result.1=true ∧ result.2.1≤q | idealTableExperiment checker adversary]=
      Pr[fun result => result.1=true ∧ result.2.1≤q | authenticatedExperiment checker adversary] :=
    probEvent_congr' (fun _ _ => Iff.rfl) (ideal_table_authenticated checker adversary)
  rw [← he]
  unfold idealTableExperiment
  simp only [probEvent_bind_eq_tsum]
  apply tsum_congr
  intro table
  apply congrArg
  rw [run,tableHandler,countHandler_run,probEvent_map]
  simp only [plain_run,Function.comp_def,Nat.zero_add]
theorem real_to_ideal_lazy (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) (hq : q < 2^256) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment checker adversary] ≤
      Pr[fun result => result.1.1=true ∧ result.1.2≤q | idealLazyExperiment checker adversary]+
        ((2 : ENNReal)^152)⁻¹+q/((2^256 : Nat) : ENNReal) := by
  rw [ideal_lazy_event]
  exact real_to_authenticated checker adversary q hq
end ClaudeWCT.W9.T3.Security.PairedOuter.GameWith
end

namespace ClaudeWCT.W9.T3.Security.PairedOuter.GameWith
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {Forgery : Type}
namespace Counted
open SigGolfCandidate.T3.Security.CountedPrivate
noncomputable def experiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery) : ProbComp (Bool × State) :=
  run (GameWith.idealGame checker adversary) (0,∅,∅)
theorem experiment_event (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) :
    Pr[fun result => result.1=true ∧ result.2.1≤q | experiment checker adversary]=
      Pr[fun result => result.1.1=true ∧ result.1.2≤q | GameWith.idealLazyExperiment checker adversary] := by
  simp only [experiment,run,GameWith.idealLazyExperiment,probEvent_map,Function.comp_def,Nat.zero_add]
theorem real_to_counted_ideal (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) (hq : q < 2^256) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment checker adversary] ≤
      Pr[fun result => result.1=true ∧ result.2.1≤q | experiment checker adversary]+
        ((2 : ENNReal)^152)⁻¹+q/((2^256 : Nat) : ENNReal) := by
  rw [experiment_event]
  exact GameWith.real_to_ideal_lazy checker adversary q hq
end Counted
namespace Monitored
open SigGolfCandidate.T3.Security.MonitoredPrivate
noncomputable def experiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery) : ProbComp (Bool × State) :=
  run (GameWith.idealGame checker adversary) ⟨(0,∅,∅),false⟩
theorem experiment_erasure (checker : Checker Forgery) (adversary : AdversaryFor Forgery) :
    Prod.map id State.source <$> experiment checker adversary=Counted.experiment checker adversary :=
  run_erasure (GameWith.idealGame checker adversary) ⟨(0,∅,∅),false⟩
theorem experiment_event (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) :
    Pr[fun result => result.1=true ∧ result.2.source.1≤q | experiment checker adversary]=
      Pr[fun result => result.1=true ∧ result.2.1≤q | Counted.experiment checker adversary] := by
  rw [← experiment_erasure checker adversary,probEvent_map]
  rfl
theorem real_to_monitored_ideal (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) (hq : q < 2^256) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment checker adversary] ≤
      Pr[fun result => result.1=true ∧ result.2.source.1≤q | experiment checker adversary]+
        ((2 : ENNReal)^152)⁻¹+q/((2^256 : Nat) : ENNReal) := by
  rw [experiment_event]
  exact Counted.real_to_counted_ideal checker adversary q hq
end Monitored
namespace Recorded
open SigGolfCandidate.T3.Security.QueryRecorded
abbrev TraceResult := Bool × (SigGolfCandidate.T3.Security.MonitoredPrivate.History × State)
/-- The paired source is recorded directly. Its bank exposes accepted outputs,
so no auxiliary proposal trace is needed by this game. -/
noncomputable def tracedExperiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery)
    (_budget : Nat) (_hbudget : _budget≤2^127) : PMF TraceResult :=
  (fun r=> (r.1,[],r.2)) <$> (liftM (run (GameWith.idealGame checker adversary) initial) : PMF _)

theorem traced_source_erasure (checker : Checker Forgery) (adversary : AdversaryFor Forgery)
    (q : Nat) (hq : q≤2^127) :
    Prod.map id Prod.snd <$> tracedExperiment checker adversary q hq =
      (liftM (run (GameWith.idealGame checker adversary) initial) : PMF _) := by
  unfold tracedExperiment
  simp only [Functor.map_map,Prod.map,id_eq]
  exact id_map _

theorem traced_base_erasure (checker : Checker Forgery) (adversary : AdversaryFor Forgery)
    (q : Nat) (hq : q≤2^127) :
    (fun r : TraceResult=>(r.1,r.2.2.base)) <$> tracedExperiment checker adversary q hq =
      (liftM (Monitored.experiment checker adversary) : PMF _) := by
  unfold tracedExperiment
  simp only [Functor.map_map]
  exact lift_run_erasure (GameWith.idealGame checker adversary) initial

theorem traced_event (checker : Checker Forgery) (adversary : AdversaryFor Forgery)
    (q : Nat) (hq : q≤2^127) :
    Pr[fun r=>r.1=true ∧ r.2.2.base.source.1≤q|tracedExperiment checker adversary q hq]=
    Pr[fun r=>r.1=true ∧ r.2.source.1≤q|Monitored.experiment checker adversary] := by
  have h:=congrArg (fun law : PMF (Bool×SigGolfCandidate.T3.Security.MonitoredPrivate.State)=>
    Pr[fun r=>r.1=true ∧ r.2.source.1≤q|law]) (traced_base_erasure checker adversary q hq)
  simpa only [probEvent_map,Function.comp_def,MonitoredPrivate.event_lift] using h

theorem traced_exception_bound (checker : Checker Forgery) (adversary : AdversaryFor Forgery)
    (q : Nat) (hq : q≤2^127) :
    Pr[fun r=>r.2.2.base.source.1≤q ∧ r.2.2.base.exceptional=true|
      tracedExperiment checker adversary q hq] ≤ q/(2:ENNReal)^146 := by
  have he:=congrArg (fun law : PMF (Bool×SigGolfCandidate.T3.Security.MonitoredPrivate.State)=>
    Pr[fun r=>r.2.source.1≤q ∧ r.2.exceptional=true|law]) (traced_base_erasure checker adversary q hq)
  simp only [probEvent_map,Function.comp_def,MonitoredPrivate.event_lift] at he
  rw [he]
  exact MonitoredPrivate.gate6_run_empty_linear_charge (GameWith.idealGame checker adversary) q 146 hq (by decide)

theorem split_clean (checker : Checker Forgery) (adversary : AdversaryFor Forgery)
    (q : Nat) (hq : q≤2^127) :
    Pr[fun r=>r.1=true ∧ r.2.2.base.source.1≤q|tracedExperiment checker adversary q hq]≤
      Pr[CleanWin q|tracedExperiment checker adversary q hq]+
      Pr[fun r=>r.2.2.base.source.1≤q ∧ r.2.2.base.exceptional=true|
        tracedExperiment checker adversary q hq] := by
  simp only [probEvent_eq_tsum_ite]
  rw [←ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro r
  by_cases hr:r∈(tracedExperiment checker adversary q hq).support
  · have hh:r.2.1=[] := by
      unfold tracedExperiment at hr
      rw [PMF.monad_map_eq_map,PMF.support_map] at hr
      obtain ⟨v,hv,he⟩:=hr
      exact congrArg (fun x:TraceResult=>x.2.1) he.symm
    by_cases hw:r.1=true ∧ r.2.2.base.source.1≤q
    · cases hb:r.2.2.base.exceptional <;> simp [CleanWin,hw,hw.1,hw.2,hb,hh]
    · simp only [hw,if_false,zero_le]
  · have hz:(tracedExperiment checker adversary q hq) r=0 := by
      simpa only [PMF.mem_support_iff,not_not] using hr
    simp only [PMF.probOutput_eq_apply,hz,ite_self,add_zero,le_refl]

theorem real_to_clean_trace (checker : Checker Forgery) (adversary : AdversaryFor Forgery)
    (q : Nat) (hq : q≤2^127) :
    Pr[fun r=>r.1=true ∧ r.2≤q|realExperiment checker adversary]≤
      Pr[CleanWin q|tracedExperiment checker adversary q hq]+
      q/(2:ENNReal)^146+((2:ENNReal)^152)⁻¹+q/((2^256:Nat):ENNReal) := by
  have h:=Monitored.real_to_monitored_ideal checker adversary q (lt_of_le_of_lt hq (by decide))
  rw [←traced_event checker adversary q hq] at h
  exact h.trans (add_le_add (add_le_add
    ((split_clean checker adversary q hq).trans
      (add_le_add le_rfl (traced_exception_bound checker adversary q hq))) le_rfl) le_rfl)

theorem traced_record_erasure (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (budget : Nat) (hbudget : budget ≤ 2^127) :
    recordedTrace <$> tracedExperiment checker adversary budget hbudget=
      (liftM (FirstHit.record (GameWith.idealGame checker adversary) (∅,∅)) : PMF _) := by
  have hr : recorded <$> run (GameWith.idealGame checker adversary) initial=
      FirstHit.record (GameWith.idealGame checker adversary) (∅,∅) := by
    rw [run_recorded]
    have hp : prepend ([] : List FirstHit.QueryEvent)=(id : FirstHit.Recorded Bool → FirstHit.Recorded Bool) := by
      funext result
      rfl
    change prepend [] <$> FirstHit.record (GameWith.idealGame checker adversary) (∅,∅)=_
    rw [hp,id_map]
  calc
    _ = recorded <$> (Prod.map id Prod.snd <$> tracedExperiment checker adversary budget hbudget) := by
      rw [Functor.map_map]
      rfl
    _ = recorded <$> (liftM (run (GameWith.idealGame checker adversary) initial) : PMF _) := by
      rw [traced_source_erasure]
    _ = (liftM (recorded <$> run (GameWith.idealGame checker adversary) initial) : PMF _) := (liftM_map _ _).symm
    _ = _ := by rw [hr]
theorem traced_cost_coherent (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (budget : Nat) (hbudget : budget ≤ 2^127)
    (result : Bool × (MonitoredPrivate.History × State))
    (hr : result ∈ (tracedExperiment checker adversary budget hbudget).support) : CostCoherent result.2.2 := by
  have hp : (result.1,result.2.2) ∈
      (Prod.map id Prod.snd <$> tracedExperiment checker adversary budget hbudget).support := by
    rw [PMF.monad_map_eq_map,PMF.support_map]
    exact ⟨result,hr,rfl⟩
  rw [traced_source_erasure] at hp
  rw [MonitoredPrivate.pmf_support] at hp
  exact run_cost_coherent (GameWith.idealGame checker adversary) initial initial_cost
    (result.1,result.2.2) hp
theorem known_public_hit_bound (checker : Checker Forgery) (reference : FirstHit.Reference) (adversary : AdversaryFor Forgery)
    (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.2.2.base.source.1≤q ∧ FirstHit.KnownPublicHit reference (recordedTrace result) |
      tracedExperiment checker adversary q hq] ≤ q/(2 : ENNReal)^128 := by
  have h := FirstHit.recorded_known_public_hit_bound reference (GameWith.idealGame checker adversary) (∅,∅) q
  have he := congrArg (fun law => Pr[fun result : FirstHit.Recorded Bool =>
      (result.events.map (fun event => FullGame.queryCharge event.input)).sum≤q ∧
      FirstHit.KnownPublicHit reference result | law]) (traced_record_erasure checker adversary q hq)
  rw [probEvent_map,Function.comp_def,MonitoredPrivate.event_lift] at he
  apply le_trans _ (he.le.trans h)
  simp only [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ (tracedExperiment checker adversary q hq).support
  · have hc := traced_cost_coherent checker adversary q hq result hr
    simp only [Function.comp_def,recordedTrace,recorded]
    rw [show result.2.2.base.source.1=
      (result.2.2.events.map (fun event => FullGame.queryCharge event.input)).sum from hc]
  · have hz : (tracedExperiment checker adversary q hq) result=0 := by
      by_contra hn
      exact hr (by simpa only [PMF.mem_support_iff] using hn)
    simp only [PMF.probOutput_eq_apply,hz,ite_self,le_refl]

end Recorded
end ClaudeWCT.W9.T3.Security.PairedOuter.GameWith

section
namespace ClaudeWCT.W9.T3.Security.PairedOuter.PaddedGame
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final.Paired
open ClaudeWCT.W9.T3M.Paired
open SigGolfCandidate.T3M (allQ_bind allQ_pure)
open SigGolfCandidate.Research.SharedForest (Signature)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen ClaudeWCT.W9.T3M.Final.Paired.checkForgeryP
theorem check_public (publicKey : Digest) (log : QueryLog Requests) (forgery : ClaudeWCT.W9.T3M.Final.Paired.ForgeryP) :
    PublicVerdict.Only (ClaudeWCT.W9.T3M.Final.Paired.checkForgeryP publicKey log forgery) := by
  have hv (message : Message) (witness : WBytes) : PublicVerdict.Only (ClaudeWCT.W9.T3M.Paired.verifyP message publicKey witness) :=
    ClaudeWCT.W9.T3M.Paired.publicOnly_verifyP message publicKey witness
  have he (message : Message) (signature : Signature) : PublicVerdict.Only (ClaudeWCT.W9.T3M.Paired.expandB message publicKey signature) :=
    ClaudeWCT.W9.T3M.Paired.publicOnly_expandB message publicKey signature
  cases forgery with
  | witness message witness =>
      unfold ClaudeWCT.W9.T3M.Final.Paired.checkForgeryP
      exact allQ_bind (hv message witness) fun _ => allQ_pure _
  | signature message signature =>
      unfold ClaudeWCT.W9.T3M.Final.Paired.checkForgeryP
      apply allQ_bind (he message signature)
      intro witness
      cases witness with
      | none => exact allQ_pure _
      | some witness => exact allQ_bind (hv message witness) fun _ => allQ_pure _
theorem check_nonMac (publicKey : Digest) (log : QueryLog Requests) (forgery : ClaudeWCT.W9.T3M.Final.Paired.ForgeryP) :
    FullGame.NonMac (ClaudeWCT.W9.T3M.Final.Paired.checkForgeryP publicKey log forgery) := by
  apply SigGolfCandidate.T3M.allQ_mono (check_public publicKey log forgery)
  intro input h
  rcases input with (sample | input) | coordinate
  · exact h.elim
  · trivial
  · exact h.elim
noncomputable def checker : GameWith.Checker ClaudeWCT.W9.T3M.Final.Paired.ForgeryP := ⟨ClaudeWCT.W9.T3M.Final.Paired.checkForgeryP,check_nonMac⟩
theorem game_eq (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) : GameWith.game checker adversary=ClaudeWCT.W9.T3M.Final.Paired.gameP adversary := by
  unfold GameWith.game ClaudeWCT.W9.T3M.Final.Paired.gameP
  apply bind_congr
  rintro ⟨publicKey,cache⟩
  unfold FullGame.loggedWith ClaudeWCT.W9.T3M.Final.Paired.signingOracle
  simp only [monadLift_self]
  apply bind_congr
  rintro ⟨forgery,log⟩
  cases forgery <;> rfl
theorem realExperiment_eq (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) :
    GameWith.realExperiment checker adversary=ClaudeWCT.W9.T3M.Final.Paired.realExperimentP adversary := by
  unfold GameWith.realExperiment ClaudeWCT.W9.T3M.Final.Paired.realExperimentP
  rw [game_eq]
theorem verdict_public (publicKey : Digest) (result : Option ClaudeWCT.W9.T3M.Final.Paired.ForgeryP × QueryLog Requests) :
    PublicVerdict.Only (GameWith.verdict checker publicKey result) := by
  unfold GameWith.verdict
  cases result.1 with
  | none => exact allQ_pure _
  | some forgery => exact allQ_bind (check_public publicKey result.2 forgery) fun _ => allQ_pure _
abbrev TraceResult := Bool × (MonitoredPrivate.History × QueryRecorded.State)
noncomputable def tracedExperiment (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (budget : Nat) (hbudget : budget ≤ 2^127) :
    PMF TraceResult := GameWith.Recorded.tracedExperiment checker adversary budget hbudget
theorem real_to_clean_trace (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.1=true ∧ result.2 ≤ q | ClaudeWCT.W9.T3M.Final.Paired.realExperimentP adversary] ≤
      Pr[QueryRecorded.CleanWin q | tracedExperiment adversary q hq]+
      q/(2 : ENNReal)^146+((2 : ENNReal)^152)⁻¹+
      q/((2^256 : Nat) : ENNReal) := by
  simpa only [realExperiment_eq,tracedExperiment] using
    GameWith.Recorded.real_to_clean_trace checker adversary q hq
theorem traced_record_erasure (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (budget : Nat) (hbudget : budget ≤ 2^127) :
    QueryRecorded.recordedTrace <$> tracedExperiment adversary budget hbudget=
      (liftM (FirstHit.record (GameWith.idealGame checker adversary) (∅,∅)) : PMF _) :=
  GameWith.Recorded.traced_record_erasure checker adversary budget hbudget
theorem traced_cost_coherent (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (budget : Nat) (hbudget : budget ≤ 2^127)
    (result : TraceResult) (hr : result ∈ (tracedExperiment adversary budget hbudget).support) :
    QueryRecorded.CostCoherent result.2.2 :=
  GameWith.Recorded.traced_cost_coherent checker adversary budget hbudget result hr
end ClaudeWCT.W9.T3.Security.PairedOuter.PaddedGame
end
namespace ClaudeWCT.W9.T3.Security.PairedOuter.PaddedGame
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M.Final.Paired
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
attribute [local instance] Classical.propDecidable

theorem large_budget (adversary : AdversaryP) (q : Nat) (hq : 2^127≤q) :
    Pr[fun r=>r.1=true ∧ r.2≤q|realExperimentP adversary]≤(q:ENNReal)/2^127 := by
  apply probEvent_le_one.trans
  have hcast : (2:ENNReal)^127≤(q:ENNReal) := by exact_mod_cast hq
  calc
    (1:ENNReal)=(2:ENNReal)^127/(2:ENNReal)^127 := (ENNReal.div_self (by positivity) (by finiteness)).symm
    _≤_ := ENNReal.div_le_div_right hcast _

theorem securityP_of_clean_bound
    (hclean : ∀ (adversary : AdversaryP) (q : Nat),1≤q→∀hq:q≤2^127,
      Pr[QueryRecorded.CleanWin q|tracedExperiment adversary q hq]+
      q/(2:ENNReal)^146+(2:ENNReal)⁻¹^700+((2:ENNReal)^152)⁻¹+
      q/((2^256:Nat):ENNReal)≤(q:ENNReal)/2^127) : SecurityP := by
  intro adversary q hpositive
  by_cases hq:2^127≤q
  · exact large_budget adversary q hq
  · have hs:q≤2^127:=by omega
    apply (real_to_clean_trace adversary q hs).trans
    apply le_trans ?_ (hclean adversary q hpositive hs)
    have ha : Pr[QueryRecorded.CleanWin q|tracedExperiment adversary q hs]+q/(2:ENNReal)^146 ≤
        Pr[QueryRecorded.CleanWin q|tracedExperiment adversary q hs]+q/(2:ENNReal)^146+(2:ENNReal)⁻¹^700 :=
      le_add_of_nonneg_right (by positivity)
    exact add_le_add (add_le_add ha le_rfl) le_rfl
end ClaudeWCT.W9.T3.Security.PairedOuter.PaddedGame
end
-- ==== merged from ClaudeWCT_W9_New_G3a_PaddedWitness ====
section

namespace ClaudeWCT.W9.T3.Security.PaddedExtraction
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open Correctness (Answers)
def Fresh (log : QueryLog Requests) : ForgeryP → Prop
  | .witness message _ => ¬∃ entry ∈ log, entry.1.message = message ∧ entry.2.isSome = true
  | .signature message signature => ¬∃ entry ∈ log, entry.1.message = message ∧
      entry.2.map ClaudeWCT.WCT9.proj = some (ClaudeWCT.WCT9.proj signature)
def WitnessOf (answers : Answers) (publicKey : Digest) : ForgeryP → Message → WBytes → Prop
  | .witness message witness, m, w => m = message ∧ w = witness
  | .signature message signature, m, w =>
      m = message ∧ evalWithAnswerFn answers (expandB message publicKey signature) = some w
end ClaudeWCT.W9.T3.Security.PaddedExtraction
end
-- ==== merged from T3_Secc_WotsMaskBase ====
section

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
def seedTweak (a : ChainAddr) : BitVec 128 := header 0 a.key.lay.val a.key.tree (a.chain / 2) a.key.leaf
def siblingHalf (a : ChainAddr) (output : HashOutput) : Digest :=
  if a.chain % 2 = 0 then output.extractLsb' 128 128 else output.extractLsb' 0 128
noncomputable def prefixStep (answers : Answers) (a : ChainAddr) (input : HashInput) : Option Nat :=
  if h : ∃ step value, step < depth answers a ∧ input = chainRow a step value then some (Classical.choose h) else none
noncomputable def maskAt (answers : Answers) (a : ChainAddr) : Answers
  | .inl (.inr input) =>
      match prefixStep answers a input with
      | some step => if step + 1 = depth answers a then ChainGraph.joinOutput (frontierValue answers a) 0
          else (0 : HashOutput)
      | none => answers (.inl (.inr input))
  | .inl (.inl coin) => answers (.inl (.inl coin))
  | .inr (.inl tweak) =>
      if tweak = seedTweak a ∧ 1 ≤ depth answers a then
        (let output := answers (.inr (.inl tweak))
         if a.chain % 2 = 0 then ChainGraph.joinOutput 0 (output.extractLsb' 128 128)
         else ChainGraph.joinOutput (output.extractLsb' 0 128) 0)
      else answers (.inr (.inl tweak))
  | .inr (.inr other) => answers (.inr (.inr other))
namespace Mask
def Respects (S : Spec.Domain → Prop) {α : Type} (program : M α) : Prop :=
  ∀ T T' : Answers, (∀ q, S q → T q = T' q) →
    evalWithAnswerFn T program = evalWithAnswerFn T' program ∧
      SourceReplay.queried T program = SourceReplay.queried T' program
section Respects
variable {S : Spec.Domain → Prop}
theorem Respects.eval_eq {α : Type} {program : M α} (h : Respects S program) {T T' : Answers}
    (hT : ∀ q, S q → T q = T' q) : evalWithAnswerFn T program = evalWithAnswerFn T' program := (h T T' hT).1
theorem Respects.queried_eq {α : Type} {program : M α} (h : Respects S program) {T T' : Answers}
    (hT : ∀ q, S q → T q = T' q) : SourceReplay.queried T program = SourceReplay.queried T' program := (h T T' hT).2
theorem Respects.pure' {α : Type} (x : α) : Respects S (pure x : M α) := fun _ _ _ => ⟨rfl, rfl⟩
theorem Respects.bind {α β : Type} {p : M α} {f : α → M β} (hp : Respects S p) (hf : ∀ x, Respects S (f x)) :
    Respects S (p >>= f) := by
  intro T T' hT
  obtain ⟨he, hq⟩ := hp T T' hT
  obtain ⟨he', hq'⟩ := hf (evalWithAnswerFn T' p) T T' hT
  refine ⟨?_, ?_⟩
  · rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, he]
    exact he'
  · rw [SourceReplay.queried_bind, SourceReplay.queried_bind, hq, he, hq']
theorem Respects.map {α β : Type} {p : M α} (f : α → β) (hp : Respects S p) : Respects S (f <$> p) := by
  rw [map_eq_bind_pure_comp]
  exact Respects.bind hp fun _ => Respects.pure' _
theorem Respects.publicHash (input : HashInput) (h : S (.inl (.inr (pad64 input)))) :
    Respects S (T3.publicHash input) := fun _ _ hT => ⟨hT _ h, rfl⟩
theorem Respects.shortHash (input : HashInput) (h : S (.inl (.inr (pad64 input)))) :
    Respects S (T3.shortHash input) := by
  unfold T3.shortHash
  exact Respects.bind (Respects.publicHash input h) fun _ => Respects.pure' _
/-- C4: a hash keeping either half (`T3.projHash`) issues the same single query as `shortHash`. -/
theorem Respects.projHash (high : Bool) (input : HashInput) (h : S (.inl (.inr (pad64 input)))) :
    Respects S (T3.projHash high input) := by
  unfold T3.projHash
  exact Respects.bind (Respects.publicHash input h) fun _ => Respects.pure' _
theorem Respects.privateHash (c : Coordinate) (h : S (.inr c)) : Respects S (T3.privateHash c) :=
  fun _ _ hT => ⟨hT _ h, rfl⟩
theorem Respects.privatePair (tag lay tree position index : Nat)
    (h : S (.inr (.inl (header tag lay tree position index)))) :
    Respects S (T3.privatePair tag lay tree position index) := by
  unfold T3.privatePair
  exact Respects.bind (Respects.privateHash _ h) fun _ => Respects.pure' _
theorem Respects.foldlM {β γ : Type} (l : List β) (f : γ → β → M γ) (hf : ∀ x ∈ l, ∀ s, Respects S (f s x)) :
    ∀ init, Respects S (l.foldlM f init) := by
  induction l with
  | nil => intro init; exact Respects.pure' init
  | cons x xs ih =>
      intro init
      rw [List.foldlM_cons]
      exact Respects.bind (hf x List.mem_cons_self init)
        fun s => ih (fun y hy s => hf y (List.mem_cons_of_mem x hy) s) s
theorem Respects.mapM {α β : Type} (l : List α) (f : α → M β) (hf : ∀ x ∈ l, Respects S (f x)) :
    Respects S (l.mapM f) := by
  induction l with
  | nil => exact Respects.pure' _
  | cons x xs ih =>
      rw [List.mapM_cons]
      exact Respects.bind (hf x List.mem_cons_self) fun _ =>
        Respects.bind (ih fun y hy => hf y (List.mem_cons_of_mem x hy)) fun _ => Respects.pure' _
end Respects
theorem eval_bind_of {T T' : Answers} {α β : Type} {p : M α} {f : α → M β}
    (hp : evalWithAnswerFn T' p = evalWithAnswerFn T p)
    (hf : evalWithAnswerFn T' (f (evalWithAnswerFn T p)) = evalWithAnswerFn T (f (evalWithAnswerFn T p))) :
    evalWithAnswerFn T' (p >>= f) = evalWithAnswerFn T (p >>= f) := by
  rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, hp, hf]
theorem header_normal (t l tr p ix : Nat) :
    header t l tr p ix = header (t % 256) (l % 256) (tr % 2 ^ 40) (p % 2 ^ 32) (ix % 2 ^ 32) := by
  have htag : packedNodeTag (t % 256) ↔ packedNodeTag t := by simp only [packedNodeTag, Nat.mod_mod]
  have htlo : tr % 1099511627776 % 4294967296 = tr % 4294967296 := by omega
  have hthi : tr % 1099511627776 / 4294967296 % 256 = tr / 4294967296 % 256 := by omega
  by_cases h : packedNodeTag t
  · have h' := htag.mpr h
    simp only [header, if_pos h, if_pos h', Nat.mod_mod, Nat.reducePow, htlo, hthi, nodeWord_normal, nodeWord_normal']
  · have h' : ¬packedNodeTag (t % 256) := fun e => h (htag.mp e)
    simp only [header, if_neg h, if_neg h', Nat.mod_mod, Nat.reducePow, htlo, hthi]
theorem header_fields {t l tr p ix t' l' tr' p' ix' : Nat}
    (h : header t l tr p ix = header t' l' tr' p' ix') :
    t % 256 = t' % 256 ∧ l % 256 = l' % 256 ∧ tr % 2 ^ 40 = tr' % 2 ^ 40 ∧ p % 2 ^ 32 = p' % 2 ^ 32 ∧
      ix % 2 ^ 32 = ix' % 2 ^ 32 := by
  rw [header_normal t l tr p ix, header_normal t' l' tr' p' ix'] at h
  exact header_injective (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) h
theorem header_congr {t l tr p ix l' tr' ix' : Nat} (hl : l % 256 = l' % 256) (htr : tr % 2 ^ 40 = tr' % 2 ^ 40)
    (hix : ix % 2 ^ 32 = ix' % 2 ^ 32) : header t l tr p ix = header t l' tr' p ix' := by
  rw [header_normal t l tr p ix, header_normal t l' tr' p ix', hl, htr, hix]
theorem header_ne_of_tag {t l tr p ix t' l' tr' p' ix' : Nat} (h : t % 256 ≠ t' % 256) :
    header t l tr p ix ≠ header t' l' tr' p' ix' := fun he => h (header_fields he).1
def LeafAlias (lay : Layer) (tree leaf : Nat) (L : LeafAddr) : Prop :=
  lay = L.lay ∧ tree % 2 ^ 40 = L.tree % 2 ^ 40 ∧ leaf % 2 ^ 32 = L.leaf % 2 ^ 32
theorem LeafAlias.refl (L : LeafAddr) : LeafAlias L.lay L.tree L.leaf L := ⟨rfl, rfl, rfl⟩
theorem LeafAlias.header_eq {lay : Layer} {tree leaf : Nat} {L : LeafAddr} (h : LeafAlias lay tree leaf L)
    (t p : Nat) : header t lay.val tree p leaf = header t L.lay.val L.tree p L.leaf := by
  obtain ⟨hl, ht, hi⟩ := h
  subst hl
  exact header_congr rfl ht hi
theorem LeafAlias.eq_of_lt {lay : Layer} {tree leaf : Nat} {L : LeafAddr} (h : LeafAlias lay tree leaf L)
    (ht : tree < 2 ^ 40) (hl : leaf < 2 ^ 32) (ht' : L.tree < 2 ^ 40) (hl' : L.leaf < 2 ^ 32) :
    (⟨lay, tree, leaf⟩ : LeafAddr) = L := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt ht'] at h2
  rw [Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hl'] at h3
  cases L
  simp only at h1 h2 h3
  subst h1 h2 h3
  rfl
theorem chainInput_alias {lay : Layer} {tree leaf : Nat} {L : LeafAddr} (h : LeafAlias lay tree leaf L) (i : Nat) :
    chainInput lay tree leaf i = chainInput L.lay L.tree L.leaf i := by
  funext step value
  unfold chainInput
  rw [chainHeader_congr_old h.1 h.2.1 h.2.2 rfl rfl]
theorem chain_alias {lay : Layer} {tree leaf : Nat} {L : LeafAddr} (h : LeafAlias lay tree leaf L) (i : Nat) :
    chain lay tree leaf i = chain L.lay L.tree L.leaf i := by
  funext start count value
  unfold chain
  rw [chainInput_alias h i]
/-- Lower (legacy T3) seeds are private half-cells; top seeds are leaf-family values since campaign T8D
(`Correctness.leafSeed_top`). -/
theorem leafSeed_eq (T : Answers) {lay : Layer} (hlay : lay ≠ 0) (tree leaf i : Nat) : leafSeed T lay tree leaf i =
    if i % 2 = 0 then (T (.inr (.inl (header 0 lay.val tree (i / 2) leaf)))).extractLsb' 0 128
    else (T (.inr (.inl (header 0 lay.val tree (i / 2) leaf)))).extractLsb' 128 128 := by
  unfold leafSeed; rw [if_neg hlay]; rfl
theorem pad64_chainInput (lay : Layer) (tree leaf i step : Nat) (value : Digest) :
    pad64 (chainInput lay tree leaf i step value) = chainInput lay tree leaf i step value := by
  simp [chainInput, pad64, bytesLE_length, zero16]
theorem chainRow_eq (a : ChainAddr) (step : Nat) (value : Digest) :
    chainRow a step value = chainInput a.key.lay a.key.tree a.key.leaf a.chain step value := rfl
theorem chainRow_inj {a : ChainAddr} {s s' : Nat} {v v' : Digest} (hs : s < 256) (hs' : s' < 256)
    (h : chainRow a s v = chainRow a s' v') : s = s' ∧ v = v' := by
  obtain ⟨hh, hv⟩ := chainInput_fields h
  have hp := (chainHeader_fields hh).2.2.2.2
  exact ⟨by omega, hv⟩
theorem chainInput_eq_chainRow {lay : Layer} {tree leaf i s s' : Nat} {v v' : Digest} {a : ChainAddr}
    (hi : i < 2 ^ 24) (hc : a.chain < 2 ^ 24) (hs : s < 256) (hs' : s' < 256)
    (h : chainInput lay tree leaf i s v = chainRow a s' v') :
    LeafAlias lay tree leaf a.key ∧ i = a.chain ∧ s = s' ∧ v = v' := by
  obtain ⟨hh, hv⟩ := chainInput_fields h
  obtain ⟨hl, ht, hf, hi', hs''⟩ := chainHeader_fields hh
  exact ⟨⟨hl, ht, hf⟩, by omega, by omega, hv⟩
theorem seedTweak_alias {lay : Layer} {tree leaf i : Nat} {a : ChainAddr} (hi : i < 2 ^ 24) (hc : a.chain < 2 ^ 24)
    (h : header 0 lay.val tree (i / 2) leaf = seedTweak a) : LeafAlias lay tree leaf a.key ∧ i / 2 = a.chain / 2 := by
  unfold seedTweak at h
  obtain ⟨-, hl, ht, hp, hx⟩ := header_fields h
  have hl' : lay = a.key.lay := by
    apply Fin.ext
    rw [Nat.mod_eq_of_lt (lt_trans lay.isLt (by decide)),
      Nat.mod_eq_of_lt (lt_trans a.key.lay.isLt (by decide))] at hl
    exact hl
  simp only [Nat.reducePow] at hp hi hc
  have hp1 : i / 2 < 4294967296 := by omega
  have hp2 : a.chain / 2 < 4294967296 := by omega
  rw [Nat.mod_eq_of_lt hp1, Nat.mod_eq_of_lt hp2] at hp
  exact ⟨⟨hl', ht, hx⟩, hp⟩
theorem dummyDigits_spec (lay : Layer) :
    (dummyDigits lay).length = chainCount lay ∧ Cost.ValidDigits lay (dummyDigits lay) := by
  fin_cases lay <;> exact ⟨by decide, by unfold Cost.ValidDigits; decide⟩
theorem referenceDigits_spec (answers : Answers) (L : LeafAddr) :
    (referenceDigits answers L).length = chainCount L.lay ∧ Cost.ValidDigits L.lay (referenceDigits answers L) := by
  unfold referenceDigits
  cases h : referenceSearch answers L with
  | none => exact dummyDigits_spec L.lay
  | some found =>
      obtain ⟨counter, digits⟩ := found
      have hd := (Correctness.counterSearch_some answers L.lay L.tree L.leaf (leafMsg answers L)
        counterLimit 0 counter digits (by decide) h).2.2
      exact ⟨(decode_length_sum hd).1, Cost.validDigits_decode hd⟩
theorem depth_le_width (answers : Answers) (a : ChainAddr) (hc : a.chain < chainCount a.key.lay) :
    depth answers a ≤ maxDigit a.key.lay a.chain :=
  (referenceDigits_spec answers a.key).2 a.chain hc
theorem width_le (lay : Layer) (i : Nat) : maxDigit lay i ≤ 7 := by
  unfold maxDigit
  split_ifs <;> decide
theorem chain_lt_of_depth (answers : Answers) (a : ChainAddr) (hd : 1 ≤ depth answers a) :
    a.chain < chainCount a.key.lay := by
  by_contra hc
  have hlen := (referenceDigits_spec answers a.key).1
  have h0 : depth answers a = 0 := List.getD_eq_default _ _ (by omega)
  omega
theorem depth_le_seven (answers : Answers) (a : ChainAddr) : depth answers a ≤ 7 := by
  by_cases hd : 1 ≤ depth answers a
  · exact (depth_le_width answers a (chain_lt_of_depth answers a hd)).trans (width_le _ _)
  · omega
theorem chainCount_le (lay : Layer) : chainCount lay ≤ 58 := chainCount_bound lay
/-- Pairing stage 1 (W9): the G-format row `value | header | 0 | 0` of chain `a` at `step` (the current scheme's
step input of a G chain, `WCT9.chainInputW`). -/
def chainRowG (a : ChainAddr) (step : Nat) (value : Digest) : HashInput :=
  bytesLE 16 value ++ bytesLE 16 (chainHeader a.key.lay a.key.tree a.key.leaf a.chain step) ++ zero16 ++ zero16
theorem chainRowG_header (a : ChainAddr) (step : Nat) (value : Digest) :
    Extract.hdrBlock (chainRowG a step value) =
      bytesLE 16 (chainHeader a.key.lay a.key.tree a.key.leaf a.chain step) := by
  simp [chainRowG, Extract.hdrBlock, zero16, List.append_assoc, bytesLE_length]
/-- Queries that are no row of chain `a` (F format `chainRow`, nor, pairing stage 1, G format `chainRowG`) and do
not read `a`'s seed cell. -/
def Untouched (a : ChainAddr) : Spec.Domain → Prop
  | .inl (.inr input) => ∀ step value, step < 256 → input ≠ chainRow a step value ∧ input ≠ chainRowG a step value
  | .inr (.inl tweak) => tweak ≠ seedTweak a
  | _ => True
theorem prefixStep_spec {answers : Answers} {a : ChainAddr} {input : HashInput} {step : Nat}
    (h : prefixStep answers a input = some step) :
    step < depth answers a ∧ ∃ value, input = chainRow a step value := by
  unfold prefixStep at h
  split at h
  · rename_i hex
    have he := Option.some.inj h
    subst he
    obtain ⟨value, hlt, heq⟩ := Classical.choose_spec hex
    exact ⟨hlt, value, heq⟩
  · cases h
theorem prefixStep_untouched {answers : Answers} {a : ChainAddr} {input : HashInput}
    (h : Untouched a (.inl (.inr input))) : prefixStep answers a input = none := by
  cases hp : prefixStep answers a input with
  | none => rfl
  | some step =>
      obtain ⟨hlt, w, heq⟩ := prefixStep_spec hp
      exact absurd heq (h step w (by have := depth_le_seven answers a; omega)).1
theorem maskAt_public (answers : Answers) (a : ChainAddr) (input : HashInput) :
    maskAt answers a (.inl (.inr input)) = match prefixStep answers a input with
      | some step => if step + 1 = depth answers a then ChainGraph.joinOutput (frontierValue answers a) 0
          else (0 : HashOutput)
      | none => answers (.inl (.inr input)) := rfl
theorem maskAt_tweak (answers : Answers) (a : ChainAddr) (tweak : BitVec 128) :
    maskAt answers a (.inr (.inl tweak)) =
      if tweak = seedTweak a ∧ 1 ≤ depth answers a then
        (if a.chain % 2 = 0 then ChainGraph.joinOutput 0 ((answers (.inr (.inl tweak))).extractLsb' 128 128)
         else ChainGraph.joinOutput ((answers (.inr (.inl tweak))).extractLsb' 0 128) 0)
      else answers (.inr (.inl tweak)) := rfl
theorem maskAt_untouched (answers : Answers) (a : ChainAddr) {q : Spec.Domain} (h : Untouched a q) :
    maskAt answers a q = answers q := by
  rcases q with (coin | input) | (tweak | other)
  · rfl
  · rw [maskAt_public, prefixStep_untouched h]
  · rw [maskAt_tweak, if_neg (fun h' => h h'.1)]
  · rfl
theorem untouched_of_hdr (a : ChainAddr) (input : HashInput) (h : BitVec 128)
    (hblock : Extract.hdrBlock input = bytesLE 16 h)
    (htag : ∀ (l : Layer) tr leaf i step, h ≠ chainHeader l tr leaf i step) :
    Untouched a (.inl (.inr input)) := by
  intro step value _
  have hb : Extract.hdrBlock (chainRow a step value) =
      bytesLE 16 (chainHeader a.key.lay a.key.tree a.key.leaf a.chain step) :=
    chainInput_header _ _ _ _ _ _
  constructor
  · intro heq
    rw [heq, hb] at hblock
    exact htag _ _ _ _ _ (bytesLE_injective hblock).symm
  · intro heq
    rw [heq, chainRowG_header] at hblock
    exact htag _ _ _ _ _ (bytesLE_injective hblock).symm
theorem untouched_prefixed (a : ChainAddr) (x : Digest) (rest : HashInput) {t : Nat} (ht : t % 256 ≠ 1)
    (l tr p ix : Nat) :
    Untouched a (.inl (.inr (pad64 (bytesLE 16 x ++ bytesLE 16 (header t l tr p ix) ++ rest)))) := by
  apply untouched_of_hdr a _ (header t l tr p ix) _
    (fun _ _ _ _ _ => Ne.symm (chainHeader_ne_header _ _ _ _ _ _ _ _ _ _))
  rw [Extract.hdrBlock_pad64 _ (by simp only [List.length_append, bytesLE_length]; omega), Extract.hdrBlock_prefix]
theorem untouched_privatePair (a : ChainAddr) {t : Nat} (ht : t % 256 ≠ 0) (l tr p ix : Nat) :
    Untouched a (.inr (.inl (header t l tr p ix))) := by
  change header t l tr p ix ≠ seedTweak a
  exact header_ne_of_tag (by simpa using ht)
section Programs
variable (a : ChainAddr)
theorem respects_nodeHash (tag lay tree heap : Nat) (left right : Digest) (ht : tag % 256 ≠ 1) :
    Respects (Untouched a) (nodeHash tag lay tree heap left right) := by
  rw [nodeHash_eq_projHash]
  apply Respects.projHash
  rw [pad64_nodeInputP]
  exact untouched_of_hdr a _ (nodeTweak tag lay tree heap) (Extract.hdrBlock_block4 left _ 0 right)
    (fun _ _ _ _ _ => Ne.symm (chainHeader_ne_nodeTweak _ _ _ _ _ _ _ _ _))
theorem respects_buildLevel (tag lay tree h level : Nat) (nodes : List Digest) (ht : tag % 256 ≠ 1) :
    Respects (Untouched a) (buildLevel tag lay tree h level nodes) :=
  Respects.mapM _ _ fun _ _ => respects_nodeHash a _ _ _ _ _ _ ht
theorem respects_buildLevels (tag lay tree h : Nat) (leaves : List Digest) (ht : tag % 256 ≠ 1) :
    Respects (Untouched a) (buildLevels tag lay tree h leaves) := by
  unfold buildLevels
  exact Respects.foldlM _ _ (fun level _ levels =>
    Respects.bind (respects_buildLevel a tag lay tree h level _ ht) fun _ => Respects.pure' _) _
theorem respects_leafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    Respects (Untouched a) (leafHash lay tree leaf ends) := by
  unfold leafHash
  exact Respects.projHash _ _ (untouched_of_hdr a _ (leafTweak lay tree leaf) (Extract.hdrBlock_leafInput _ _ _ _)
    (fun _ _ _ _ _ => Ne.symm (chainHeader_ne_leafTweak _ _ _ _ _ _ _ _)))
theorem respects_mask (level index : Nat) : Respects (Untouched a) (mask level index) := by
  unfold mask pairedMask
  exact Respects.bind (Respects.privatePair _ _ _ _ _ (untouched_privatePair a (by decide) _ _ _ _))
    fun _ => Respects.pure' _
theorem respects_privateMac (region : Region) : Respects (Untouched a) (privateMac region) := by
  unfold privateMac privateMacKey
  exact Respects.bind (Respects.bind
    (Respects.privateHash _ (untouched_privatePair a (by decide) 0 0 0 0)) fun _ =>
    Respects.bind (Respects.privateHash _ (untouched_privatePair a (by decide) 0 0 0 1)) fun _ =>
      Respects.pure' _) fun _ => Respects.pure' _
theorem respects_privateNonce (message : Message) : Respects (Untouched a) (privateNonce message) := by
  unfold privateNonce
  exact Respects.bind (Respects.privateHash _ trivial) fun _ => Respects.pure' _
theorem respects_digest (rho : Digest) (message : Message) (counter : BitVec 32) :
    Respects (Untouched a) (digest rho message counter) := by
  unfold digest
  apply Respects.publicHash
  apply untouched_of_hdr a _ (digestHeader counter) _
    (fun _ _ _ _ _ => (chainHeader_ne_digestHeader _ _ _ _ _ counter).symm)
  unfold digestInput
  rw [Extract.hdrBlock_pad64 _ (by simp only [List.length_append, bytesLE_length]; omega),
    Extract.hdrBlock_prefix]
end Programs
end Mask
end SigGolfCandidate.T3.Security.Wots
end
-- ==== merged from ClaudeWCT_WCT9_TopHonest ====
section

/-! # Top-nonce layer (img-v6): honest node inputs with nonces (r3-lean-nonsec)

The honest input of a tree node `(lay, tree, level, c)` (children at `level`, heap `2^(height lay - level - 1) + c`)
is `left | merkleTweak | nonce | right`. The nonce slot is the keygen nonce search's result on the top tree (levels
0..10, `honestNonce`) and 0 elsewhere (the root and every lower tree). `wotsTree_node_nonce` states the honest node
equation for the top tree with this nonce. -/
namespace ClaudeWCT.WCT9
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
open SphincsSecurity (bytesLE)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- The 16-byte nonce slot of a top node input (`T3.nonceBytes n`) as a digest. -/
def nonceDigest (n : Nat) : Digest := BitVec.ofNat 128 (n % 2 ^ 64)
theorem bytesLE_nonceDigest (n : Nat) : bytesLE 16 (nonceDigest n) = nonceBytes n := rfl
theorem nonceDigest_zero : nonceDigest 0 = 0 := rfl
theorem nonceDigest_inj {n m : Nat} (hn : n < 2 ^ 64) (hm : m < 2 ^ 64) (h : nonceDigest n = nonceDigest m) :
    n = m := by
  unfold nonceDigest at h
  rw [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hm] at h
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  exact this

/-- Node input with nonce slot `n` (all layers; `n = 0` is `merkleNodeInput`). -/
def merkleNodeInputN (lay tree heap n : Nat) (left right : Digest) : HashInput :=
  bytesLE 16 left ++ bytesLE 16 (merkleTweak lay tree heap) ++ bytesLE 16 (nonceDigest n) ++ bytesLE 16 right

theorem merkleNodeInputN_zero (lay tree heap : Nat) (left right : Digest) :
    merkleNodeInputN lay tree heap 0 left right = merkleNodeInput lay tree heap left right := by
  unfold merkleNodeInputN merkleNodeInput
  rw [nonceDigest_zero, bytesLE_zero16]

theorem merkleNodeInputN_length (lay tree heap n : Nat) (left right : Digest) :
    (merkleNodeInputN lay tree heap n left right).length = 64 := by
  simp [merkleNodeInputN, SphincsSecurity.bytesLE_length]

theorem pad64_merkleNodeInputN (lay tree heap n : Nat) (left right : Digest) :
    pad64 (merkleNodeInputN lay tree heap n left right) = merkleNodeInputN lay tree heap n left right := by
  unfold pad64; rw [merkleNodeInputN_length]; simp

theorem merkleNodeInputN_eq_lowerNodeInputP (lay tree heap n : Nat) (left right : Digest) :
    merkleNodeInputN lay tree heap n left right = lowerNodeInputP lay tree heap left 0 (nonceDigest n) right := by
  unfold merkleNodeInputN lowerNodeInputP
  rw [merkleTweak_eq_word]
  rfl

theorem merkleTweak_top0 (tree heap : Nat) : merkleTweak 0 tree heap = nodeTweak 3 0 0 heap := by
  rw [merkleTweak_top]
  unfold nodeTweak
  simp

theorem merkleNodeInputN_top (tree heap n : Nat) (left right : Digest) :
    merkleNodeInputN 0 tree heap n left right = topNodeInput heap n left right := by
  unfold merkleNodeInputN topNodeInput
  rw [merkleTweak_top0, bytesLE_nonceDigest]

/-- The honest nonce of node `(lay, tree, level, c)` (children at `level`): the keygen nonce search on the top tree
(`level < 11`), 0 on the root and on every lower tree. -/
noncomputable def honestNonce (answers : Answers) (lay : Layer) (tree level c : Nat) : Nat :=
  if lay = 0 ∧ level < 11 then
    (evalWithAnswerFn answers (topNodeAt (level + 1) (2 ^ (height lay - level - 1) + c)
      (treeValue (wotsTree answers lay tree) level (2 * c))
      (treeValue (wotsTree answers lay tree) level (2 * c + 1)))).1
  else 0

theorem honestNonce_lower (answers : Answers) {lay : Layer} (h : lay ≠ 0) (tree level c : Nat) :
    honestNonce answers lay tree level c = 0 := by
  unfold honestNonce; rw [if_neg (fun h' => h h'.1)]

theorem honestNonce_root (answers : Answers) (lay : Layer) (tree c : Nat) :
    honestNonce answers lay tree 11 c = 0 := by
  unfold honestNonce; rw [if_neg (fun h' => by omega)]

theorem honestInputN_lower (answers : Answers) {lay : Layer} (h : lay ≠ 0) (tree heap level c : Nat)
    (left right : Digest) :
    merkleNodeInputN lay.val tree heap (honestNonce answers lay tree level c) left right =
      merkleNodeInput lay.val tree heap left right := by
  rw [honestNonce_lower answers h, merkleNodeInputN_zero]

/-- The honest top-tree node equation with nonces: node `c` of level `level + 1` is the used half of the hash of its
honest nonce input. -/
theorem wotsTree_node_nonce (answers : Answers) (tree level c : Nat) (hl : level < 12)
    (hc : c < 2 ^ (11 - level)) :
    treeValue (wotsTree answers 0 tree) (level + 1) c =
      evalWithAnswerFn answers (projHash (lowerHigh 0 (2 ^ (11 - level) + c))
        (merkleNodeInputN 0 tree (2 ^ (11 - level) + c) (honestNonce answers 0 tree level c)
          (treeValue (wotsTree answers 0 tree) level (2 * c))
          (treeValue (wotsTree answers 0 tree) level (2 * c + 1)))) := by
  have hw : wotsTree answers 0 tree =
      evalWithAnswerFn answers (buildTopLevels ((List.range (2 ^ height 0)).map (wotsRoot answers 0 tree))) := by
    unfold wotsTree; rw [if_pos rfl]
  have htree := eval_buildTopLevels_correct answers ((List.range (2 ^ height 0)).map (wotsRoot answers 0 tree))
    (by simp [height])
  rw [← hw] at htree
  have hnode := htree.2.2 level hl c (by simpa [show 12 - (level + 1) = 11 - level by omega] using hc)
  have hheap : 2 ^ (12 - (level + 1)) + c = 2 ^ (11 - level) + c := by
    rw [show 12 - (level + 1) = 11 - level by omega]
  rw [hheap] at hnode
  unfold treeValue
  rw [hnode, merkleNodeInputN_top, lowerHigh_top_eq_nodeHalfHigh]
  unfold topLevelNode
  by_cases h12 : level + 1 = 12
  · rw [if_pos h12]
    have h11 : level = 11 := by omega
    subst h11
    rw [honestNonce_root]
    unfold nodeHash topNodeInput
    rw [show nonceBytes 0 = zero16 from (bytesLE_nonceDigest 0).symm.trans
      (by rw [nonceDigest_zero, bytesLE_zero16])]
  · rw [if_neg h12]
    have hn : honestNonce answers 0 tree level c =
        (evalWithAnswerFn answers (topNodeAt (level + 1) (2 ^ (11 - level) + c)
          ((wotsTree answers 0 tree).getD level [] |>.getD (2 * c) 0)
          ((wotsTree answers 0 tree).getD level [] |>.getD (2 * c + 1) 0))).1 := by
      unfold honestNonce
      rw [if_pos ⟨rfl, by omega⟩]
      rw [show height (0 : Layer) - level - 1 = 11 - level by simp [height]; omega]
      rfl
    rw [hn]
    exact (eval_topNodeAt_hash answers (level + 1) (2 ^ (11 - level) + c) _ _).symm

/-- The honest node equation of every layer, with the honest nonce. -/
theorem wotsTree_node_any (answers : Answers) (lay : Layer) (tree level c : Nat) (hl : level < height lay)
    (hc : c < 2 ^ (height lay - level - 1)) :
    treeValue (wotsTree answers lay tree) (level + 1) c =
      evalWithAnswerFn answers (halfHash (lowerHigh lay.val (2 ^ (height lay - level - 1) + c))
        (merkleNodeInputN lay.val tree (2 ^ (height lay - level - 1) + c)
          (honestNonce answers lay tree level c)
          (treeValue (wotsTree answers lay tree) level (2 * c))
          (treeValue (wotsTree answers lay tree) level (2 * c + 1)))) := by
  by_cases h0 : lay = 0
  · subst h0
    have hh : height (0 : Layer) - level - 1 = 11 - level := by simp [height]; omega
    rw [hh] at hc ⊢
    rw [halfHash_eq_projHash]
    exact wotsTree_node_nonce answers tree level c (by simp [height] at hl; omega) hc
  · obtain ⟨-, -, hnodes⟩ := wotsTree_correct answers h0 tree
    have hsub : height lay - (level + 1) = height lay - level - 1 := by omega
    have hrec := hnodes level hl c (by rw [hsub]; exact hc)
    rw [hsub] at hrec
    unfold treeValue
    rw [hrec, honestInputN_lower answers h0]
    rfl

end ClaudeWCT.WCT9
end
-- ==== merged from ClaudeWCT_W9_T3M_Extract_Basic ====
section

namespace ClaudeWCT.W9.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers treeValue)
open ClaudeWCT.WCT9 (wotsTree wotsSeed wotsEnd)
open SphincsSecurity (bytesLE)
export SigGolfCandidate.T3M.Extract (canonicalHeader)
noncomputable def honestRoot (answers : Answers) (lay : Layer) (tree : Nat) : Digest :=
  treeValue (wotsTree answers lay tree) (height lay) 0
noncomputable def honestPair (answers : Answers) (lay : Layer) (tree : Nat) : Digest × Digest :=
  (treeValue (wotsTree answers lay tree) (height lay - 1) 0, treeValue (wotsTree answers lay tree) (height lay - 1) 1)
/-- FTS seed of `(index, coord, child, chain)`: the stage-A seed family of `(index, coord)` at `ftsPoint child chain`
(agrees with `WCT9.seed` by `rfl`). -/
def wctSeed (answers : Answers) (index coord child chain : Nat) : Digest :=
  ClaudeWCT.Arith.familyEval (List.ofFn (WCT9.ftsCoef answers index coord)) (WCT9.ftsPoint child chain)
def wctValue (answers : Answers) (index coord child chain step : Nat) : Digest :=
  evalWithAnswerFn answers (WCT9.chain index coord child chain 0 step (wctSeed answers index coord child chain))
def wctEnds (answers : Answers) (index coord child : Nat) : List Digest :=
  List.ofFn fun t : Fin 6 => wctValue answers index coord child t.val 4
/-- Honest pads of coordinate `coord` (nested FTS r1-1): the honest top pair of `coord - 1`, `(0, 0)` for 0. -/
abbrev ftsPrev (answers : Answers) (index coord : Nat) : Digest × Digest := WCT9.ftsPrev answers index coord
def ftsLeaves (answers : Answers) (index coord : Nat) : List Digest :=
  List.ofFn fun j : Fin 128 => evalWithAnswerFn answers
    (WCT9.leafHashP index coord j.val (ftsPrev answers index coord).1 (wctEnds answers index coord j.val))
def ftsNodes (answers : Answers) (index coord : Nat) : Array Digest :=
  evalWithAnswerFn answers (WCT9.heapBuild index coord (ftsPrev answers index coord).2 (ftsLeaves answers index coord))
def ftsLevels (answers : Answers) (index coord : Nat) : List (List Digest) :=
  WCT9.heapLevels (ftsNodes answers index coord)
def ftsPair (answers : Answers) (index coord : Nat) : Digest × Digest :=
  (treeValue (ftsLevels answers index coord) 6 0, treeValue (ftsLevels answers index coord) 6 1)
def ftsPairsHonest (answers : Answers) (index : Nat) : List (Digest × Digest) :=
  (List.range 9).map (ftsPair answers index)
def listInput (first : Digest) (hdr : BitVec 128) (rest : List Digest) : HashInput :=
  bytesLE 16 first ++ bytesLE 16 hdr ++ rest.flatMap (bytesLE 16)
def leafInput (lay : Layer) (tree leaf : Nat) (ends : List Digest) : HashInput :=
  SigGolfCandidate.T3.leafInput lay tree leaf ends
/-- Honest FTS leaf input (campaign T8): `end0 | header | zero pad | end1..end5`, i.e. the pad slot is the first
digest of the list part. -/
def wctLeafInput (index coord child : Nat) (ends : List Digest) : HashInput :=
  listInput (ends.getD 0 0) (WCT9.ftsLeafHeader index coord child) (0 :: ends.drop 1)
/-- Padded FTS leaf input (campaign T8): the leaf pad `pad` in the slot after the header. -/
def wctLeafInputP (index coord child : Nat) (pad : Digest) (ends : List Digest) : HashInput :=
  listInput (ends.getD 0 0) (WCT9.ftsLeafHeader index coord child) (pad :: ends.drop 1)
theorem wctLeafInputP_zero (index coord child : Nat) (ends : List Digest) :
    wctLeafInputP index coord child 0 ends = wctLeafInput index coord child ends := rfl
abbrev forestInput (index : Nat) (pairs : List (Digest × Digest)) : HashInput := WCT9.forestInput index pairs
def honestForest (answers : Answers) (index : Nat) : Digest :=
  evalWithAnswerFn answers (WCT9.forestPk index (ftsPairsHonest answers index))
/-- Honest L3 message (nested FTS r1-1): the top pair of coordinate 8. -/
def honestTop (answers : Answers) (index : Nat) : Digest × Digest := ftsPair answers index 8
noncomputable def honestMsg (answers : Answers) (index : Nat) (lay : Layer) : WCT9.LayerMsg :=
  if h : lay.val < 3 then
    .pair (honestPair answers ⟨lay.val + 1, by omega⟩ (route index ⟨lay.val + 1, by omega⟩).2).1
      (honestPair answers ⟨lay.val + 1, by omega⟩ (route index ⟨lay.val + 1, by omega⟩).2).2
  else .pair (honestTop answers index).1 (honestTop answers index).2
/-- Tree index bits per layer (the routed tree of an index below `2 ^ 31`). -/
def treeBits (lay : Layer) : Nat := ![0, 12, 19, 25] lay
theorem treeBits_le (lay : Layer) : treeBits lay ≤ 25 := by fin_cases lay <;> decide
theorem tree_lt_of_treeBits {lay : Layer} {tree : Nat} (ht : tree < 2 ^ treeBits lay) : tree < 2 ^ 31 :=
  lt_of_lt_of_le ht (le_trans (Nat.pow_le_pow_right (by decide) (treeBits_le lay)) (by norm_num))
theorem leaf_lt_4096 {lay : Layer} {leaf : Nat} (hl : leaf < 2 ^ height lay) : leaf < 4096 := by
  fin_cases lay <;> simp [height] at hl ⊢ <;> omega
/-- The honest chain value of the current scheme after `step` steps (`WCT9.chainW`; pairing stage 1: the G chains'
interior steps keep the high half). -/
def honestChainValueW (answers : Answers) (lay : Layer) (tree leaf i : Nat) (seed : Digest) (step : Nat) : Digest :=
  evalWithAnswerFn answers (WCT9.chainW lay tree leaf i 0 step seed)
inductive Pos where
  | chain (lay : Layer) (tree leaf i step : Nat)
  | leaf (lay : Layer) (tree leaf : Nat)
  | node (lay : Layer) (tree level node : Nat)
  | forest (index : Nat)
  | wctChain (index coord child chain step : Nat)
  | wctLeaf (index coord child : Nat)
  | wctNode (index coord level node : Nat)
noncomputable def honestInput (answers : Answers) : Pos → HashInput
  | .chain lay tree leaf i step => pad64 (WCT9.chainInputW lay tree leaf i step
      (honestChainValueW answers lay tree leaf i (wotsSeed answers lay tree leaf i) step))
  | .leaf lay tree leaf => pad64 (leafInput lay tree leaf
      ((List.range (chainCount lay)).map (wotsEnd answers lay tree leaf)))
  | .node lay tree level node => pad64 (WCT9.merkleNodeInputN lay.val tree (2 ^ (height lay - level - 1) + node)
      (WCT9.honestNonce answers lay tree level node)
      (treeValue (wotsTree answers lay tree) level (2 * node))
      (treeValue (wotsTree answers lay tree) level (2 * node + 1)))
  | .forest index => pad64 (forestInput index (ftsPairsHonest answers index))
  | .wctChain index coord child chain step => pad64 (WCT9.ftsChainInputW index coord child chain step
      (wctValue answers index coord child chain step))
  | .wctLeaf index coord child => pad64 (wctLeafInputP index coord child (ftsPrev answers index coord).1
      (wctEnds answers index coord child))
  | .wctNode index coord level node => pad64 (nodeInputP 3 (WCT9.nodeLayer coord) index (2 ^ (7 - level - 1) + node)
      (treeValue (ftsLevels answers index coord) level (2 * node))
      (if level = 5 then (ftsPrev answers index coord).2 else 0)
      (treeValue (ftsLevels answers index coord) level (2 * node + 1)))
def Pos.hdr : Pos → BitVec 128
  | .chain lay tree lf i step => chainHeader lay tree lf i step
  | .leaf lay tree lf => leafTweak lay tree lf
  | .node lay tree level nd => WCT9.merkleTweak lay.val tree (2 ^ (height lay - level - 1) + nd)
  | .forest index => header 15 0 index 0 0
  | .wctChain index coord child t step => WCT9.ftsChainHeader index coord child t step
  | .wctLeaf index coord child => WCT9.ftsLeafHeader index coord child
  | .wctNode index coord level nd => WCT9.wctNodeHeader coord index (2 ^ (7 - level - 1) + nd)
def Pos.Bounded : Pos → Prop
  | .chain _ tree lf i step => tree < 2 ^ 31 ∧ lf < 4096 ∧ i < 64 ∧ step < 7
  | .leaf lay tree lf => lf < 2 ^ height lay ∧ tree * 2 ^ height lay + lf < 2 ^ 32
  | .node lay tree level nd => tree < 2 ^ 32 ∧ level < height lay ∧ (lay = 0 ∨ level + 1 < height lay) ∧
      (lay = 0 → tree = 0) ∧ nd < 2 ^ (height lay - level - 1)
  | .forest index => index < 2 ^ 40
  | .wctChain index coord child t step => index < 2 ^ 31 ∧ coord < 9 ∧ child < 128 ∧ t < 6 ∧ step < 4
  | .wctLeaf index coord child => index < 2 ^ 31 ∧ coord < 9 ∧ child < 128
  | .wctNode index coord level nd => index < 2 ^ 31 ∧ coord < 9 ∧ level < 6 ∧ nd < 2 ^ (7 - level - 1)
/-- Whether a position's honest value is the HIGH half of its hash output (C2/C3 on the paired tree). The legacy
unpaired FTS positions keep the paired tree's legacy rule (the top FTS nodes, `wctNode` level 5, nested FTS r1-1; the
paired forest's halves live in `Extract.Paired`). The lower trees follow #866: the left children (C2: lower leaves and
nodes of even heap, `WCT9.lowerHigh`) and the last step of lower chain 0 (C3, `WCT9.chainHigh`). -/
def Pos.high : Pos → Bool
  | .wctNode _ _ level _ => decide (level = 5)
  | .leaf lay _ lf => WCT9.lowerHigh lay.val lf
  | .node lay _ level nd => WCT9.lowerHigh lay.val (2 ^ (height lay - level - 1) + nd)
  | .chain lay _ _ i step => WCT9.chainHigh lay i step
  | .wctChain _ _ _ t step => WCT9.ftsChainHigh t step
  | _ => false
/-- The 128-bit half of an output that a position's honest value uses. -/
def Pos.proj (p : Pos) : HashOutput → Digest := WCT9.halfOf p.high
theorem Pos.proj_eq (p : Pos) :
    p.proj = fun a => if p.high then a.extractLsb' 128 128 else a.extractLsb' 0 128 := rfl
theorem Pos.proj_of_low {p : Pos} (h : p.high = false) : p.proj = fun a => a.extractLsb' 0 128 := by
  unfold Pos.proj; rw [h]; rfl
theorem Pos.proj_of_high {p : Pos} (h : p.high = true) : p.proj = fun a => a.extractLsb' 128 128 := by
  unfold Pos.proj; rw [h]; rfl
/-- The (padded) length of a position's honest input (S2-2). -/
def Pos.len : Pos → Nat
  | .leaf lay _ _ => if lay = 0 then 832 else 704
  | .wctLeaf .. => 128
  | .forest .. => 320
  | _ => 64
/-- A hit at a position: a different input whose output agrees with the honest one on the used half. -/
def HashHitAt (answers : Answers) (pos : Pos) (honest actual : HashInput) : Prop :=
  actual ≠ honest ∧ pos.proj (answers (.inl (.inr actual))) = pos.proj (answers (.inl (.inr honest)))
theorem hashHitAt_of_low {answers : Answers} {pos : Pos} {honest actual : HashInput}
    (hp : pos.proj = fun a => a.extractLsb' 0 128) (h : HashHit answers honest actual) :
    HashHitAt answers pos honest actual := by
  unfold HashHitAt; rw [hp]; exact h
def hdrBlock (input : HashInput) : HashInput := (input.drop 16).take 16
/-- C4: a header block whose low word `W` (its first 8 bytes) satisfies `1 ≤ W < 2 ^ 16`. Among 64-byte positions
only the top folds have such a label (`T3.topNodeWord`, in `[1, 4096)`): the digest has `W = 0`, every FTS word is
`≥ 2 ^ 16` (coordinate nibble `coord + 1`), WOTS chain and lower fold words carry type byte 193. -/
def TopLow (b : HashInput) : Prop := 1 ≤ readLE (b.take 8) ∧ readLE (b.take 8) < 2 ^ 16
instance (b : HashInput) : Decidable (TopLow b) :=
  inferInstanceAs (Decidable (1 ≤ readLE (b.take 8) ∧ readLE (b.take 8) < 2 ^ 16))
/-- C3 (FULL, S2-2) + C4: the decoding key of an input's header block. Leaf-length inputs (704 or 832 bytes) and
64-byte inputs with a top label (`TopLow`) are keyed by the low tweak word only (their high word is a witness pad);
every other input by its canonical header. -/
def hdrKey (x : HashInput) : HashInput :=
  if x.length = 704 ∨ x.length = 832 then (hdrBlock x).take 8 ++ List.replicate 8 0
  else if x.length = 64 ∧ TopLow (hdrBlock x) then (hdrBlock x).take 8 ++ List.replicate 8 0
  else canonicalHeader (hdrBlock x)
/-- Same length and same decoding key (C3 FULL; S2-2). -/
def SameHeader (actual honest : HashInput) : Prop :=
  actual.length = honest.length ∧ hdrKey actual = hdrKey honest
/-- C4: a 64-byte input without a top label is keyed by its canonical header. -/
theorem hdrKey_of_len64 {x : HashInput} (h : x.length = 64) (ht : ¬ TopLow (hdrBlock x)) :
    hdrKey x = canonicalHeader (hdrBlock x) := by
  unfold hdrKey; rw [if_neg (by omega), if_neg (fun h' => ht h'.2)]
/-- C4: a 64-byte input with a top label is keyed by its low word. -/
theorem hdrKey_of_top {x : HashInput} (h : x.length = 64) (ht : TopLow (hdrBlock x)) :
    hdrKey x = (hdrBlock x).take 8 ++ List.replicate 8 0 := by
  unfold hdrKey; rw [if_neg (by omega), if_pos ⟨h, ht⟩]
theorem hdrBlock_length_of_64 {x : HashInput} (h : x.length = 64) : (hdrBlock x).length = 16 := by
  unfold hdrBlock; simp [h]
theorem canonicalHeader_take8 {h : HashInput} (hl : 8 ≤ h.length) : (canonicalHeader h).take 8 = h.take 8 := by
  unfold canonicalHeader
  split
  · rw [List.take_append_of_le_length (by simp; omega)]; simp
  · rfl
theorem hdrKey_congr {a b : HashInput} (hl : a.length = b.length) (hb : hdrBlock a = hdrBlock b) :
    hdrKey a = hdrKey b := by
  unfold hdrKey; rw [hl, hb]
theorem SameHeader.of_hdrBlock {a b : HashInput} (hl : a.length = b.length) (hb : hdrBlock a = hdrBlock b) :
    SameHeader a b := ⟨hl, hdrKey_congr hl hb⟩
theorem SameHeader.of_canonical {a b : HashInput} (hl : a.length = b.length)
    (hn : ¬ (b.length = 704 ∨ b.length = 832))
    (hc : canonicalHeader (hdrBlock a) = canonicalHeader (hdrBlock b)) : SameHeader a b := by
  refine ⟨hl, ?_⟩
  unfold hdrKey
  rw [if_neg (by rw [hl]; exact hn), if_neg hn]
  by_cases h64 : b.length = 64
  · have ha := hdrBlock_length_of_64 (hl.trans h64)
    have hb := hdrBlock_length_of_64 h64
    have ht : (hdrBlock a).take 8 = (hdrBlock b).take 8 := by
      rw [← canonicalHeader_take8 (by omega : 8 ≤ (hdrBlock a).length), hc,
        canonicalHeader_take8 (by omega : 8 ≤ (hdrBlock b).length)]
    have hT : TopLow (hdrBlock a) ↔ TopLow (hdrBlock b) := by unfold TopLow; rw [ht]
    by_cases hT' : TopLow (hdrBlock b)
    · rw [if_pos ⟨hl.trans h64, hT.mpr hT'⟩, if_pos ⟨h64, hT'⟩, ht]
    · rw [if_neg (fun h => hT' (hT.mp h.2)), if_neg (fun h => hT' h.2), hc]
  · rw [if_neg (fun h => h64 (by rw [← hl]; exact h.1)), if_neg (fun h => h64 h.1), hc]
theorem pad64_length_congr {a b : HashInput} (h : a.length = b.length) : (pad64 a).length = (pad64 b).length := by
  simp only [pad64, List.length_append, List.length_replicate, h]
def HitIn (answers : Answers) (qs : List Spec.Domain) : Prop :=
  ∃ pos actual, pos.Bounded ∧ .inl (.inr actual) ∈ qs ∧ HashHitAt answers pos (honestInput answers pos) actual ∧
    SameHeader actual (honestInput answers pos)
theorem HitIn.mono {answers : Answers} {qs qs' : List Spec.Domain} (h : HitIn answers qs)
    (hsub : ∀ q ∈ qs, q ∈ qs') : HitIn answers qs' := by
  obtain ⟨pos, actual, hb, hq, hh, hs⟩ := h
  exact ⟨pos, actual, hb, hsub _ hq, hh, hs⟩
theorem HitIn.append_left {answers : Answers} {qs : List Spec.Domain} (qs' : List Spec.Domain)
    (h : HitIn answers qs) : HitIn answers (qs ++ qs') :=
  h.mono fun _ hq => List.mem_append_left _ hq
theorem HitIn.append_right {answers : Answers} {qs' : List Spec.Domain} (qs : List Spec.Domain)
    (h : HitIn answers qs') : HitIn answers (qs ++ qs') :=
  h.mono fun _ hq => List.mem_append_right _ hq
theorem ftsPairsHonest_length (answers : Answers) (index : Nat) : (ftsPairsHonest answers index).length = 9 := by
  simp [ftsPairsHonest]
theorem wctEnds_length (answers : Answers) (index coord child : Nat) :
    (wctEnds answers index coord child).length = 6 := by
  simp [wctEnds]
end ClaudeWCT.W9.T3M.Extract


namespace ClaudeWCT.W9.T3M.Extract.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.Research
open SphincsSecurity (bytesLE)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- The four canonical paired commitments preceding the final singleton. -/
def pairPrev (answers : Answers) (index : Nat) : Nat → SharedForest.PairRoot
  | 0 => ClaudeWCT.WCT9.ftsStart
  | n+1 => SharedForest.expectedPairRoot answers index n (pairPrev answers index n)

def first (coord : Nat) : Bool := decide (coord < 8 ∧ coord % 2 = 0)

def physical (coord raw : Nat) : Nat := SharedForest.physicalChild (first coord) raw

def pads (answers : Answers) (index coord branch : Nat) : SharedForest.PairRoot :=
  if coord = 8 then pairPrev answers index 4
  else if first coord then pairPrev answers index (coord/2)
  else SharedForest.nodesPair
    (SharedForest.firstNodes answers index (coord/2) (pairPrev answers index (coord/2))) branch

def nodes (answers : Answers) (index coord : Nat) : Array Digest :=
  if coord = 8 then SharedForest.sharedNodes answers false index 8 (fun _ => pairPrev answers index 4)
  else if first coord then SharedForest.firstNodes answers index (coord/2) (pairPrev answers index (coord/2))
  else SharedForest.secondNodes answers index (coord/2) (pairPrev answers index (coord/2))

/-- Every used node chooses one fixed balanced128-bit output projection. -/
def highPosition (coord level : Nat) : Prop :=
  coord < 8 ∧ ((coord % 2 = 0 ∧ level = 4) ∨ (coord % 2 = 1 ∧ level = 5))
instance (coord level : Nat) : Decidable (highPosition coord level) := by
  unfold highPosition
  infer_instance

/-- Stage 2 (merged singleton "Cm"): the final singleton's left top node (coordinate 8, level 5, node 0 = heap 2)
keeps the HIGH half of its output (its value lands on `WIT + 0`, the junk low half below the witness, so the C3 row
pad at `WIT + 24` stays witness memory); its right top node (heap 3) keeps the low half. -/
def singletonHigh (coord level node : Nat) : Prop := coord = 8 ∧ level = 5 ∧ node = 0
instance (coord level node : Nat) : Decidable (singletonHigh coord level node) := by
  unfold singletonHigh
  infer_instance

/-- C1 (FTS Merkle half-swap): node `node` of level `level` (heap `2^(6-level) + node`) uses the high half on the
top folds of `highPosition`, on the singleton's left top node (stage 2, `singletonHigh`) and on every even heap
`16..127` (the even nodes of levels `0..2`). -/
def highNodeAt (coord level node : Nat) : Prop :=
  (highPosition coord level ∨ singletonHigh coord level node) ∨ (level ≤ 2 ∧ node % 2 = 0)
instance (coord level node : Nat) : Decidable (highNodeAt coord level node) := by
  unfold highNodeAt
  infer_instance

/-- Stage 2: the top folds (level 5) of the final singleton: heap 2 (node 0) high, heap 3 (node 1) low. -/
theorem highNodeAt_singleton (node : Nat) : highNodeAt 8 5 node ↔ node = 0 := by
  unfold highNodeAt highPosition singletonHigh
  omega

/-- No packed node (`level ≤ 4`) and no A/B top fold is a singleton top node. -/
theorem not_singletonHigh_of_level {coord level node : Nat} (h : level ≠ 5) : ¬singletonHigh coord level node := by
  unfold singletonHigh
  omega

/-- C1: the leaf of raw child `child` (heap `128 + physical`) uses the high half on even physical children. -/
def highLeafAt (coord child : Nat) : Prop := physical coord child % 2 = 0
instance (coord child : Nat) : Decidable (highLeafAt coord child) := by
  unfold highLeafAt
  infer_instance

/-- The used half of a position's output on the paired tree. FTS leaves and nodes follow `highLeafAt` /
`highNodeAt`; the lower-tree positions follow #866's C2/C3 rule (`Extract.Pos.high`: the left children of the lower
trees and the last step of lower chain 0 are high; `proj_lower` states that this is `Pos.proj`); everything else uses
the low half. The lower cases are written as `if`s so that `simp only [proj, ite_apply]` unfolds every case alike. -/
def proj : Pos → HashOutput → Digest
  | .wctNode _ coord level node => if highNodeAt coord level node then
      fun answer => answer.extractLsb' 128 128 else fun answer => answer.extractLsb' 0 128
  | .wctLeaf _ coord child => if highLeafAt coord child then
      fun answer => answer.extractLsb' 128 128 else fun answer => answer.extractLsb' 0 128
  | .chain lay _ _ i step => if ClaudeWCT.WCT9.chainHigh lay i step then
      fun answer => answer.extractLsb' 128 128 else fun answer => answer.extractLsb' 0 128
  | .wctChain _ _ _ t step => if ClaudeWCT.WCT9.ftsChainHigh t step then
      fun answer => answer.extractLsb' 128 128 else fun answer => answer.extractLsb' 0 128
  | .leaf lay _ leaf => if ClaudeWCT.WCT9.lowerHigh lay.val leaf then
      fun answer => answer.extractLsb' 128 128 else fun answer => answer.extractLsb' 0 128
  | .node lay _ level node => if ClaudeWCT.WCT9.lowerHigh lay.val (2 ^ (height lay - level - 1) + node) then
      fun answer => answer.extractLsb' 128 128 else fun answer => answer.extractLsb' 0 128
  | _ => fun answer => answer.extractLsb' 0 128

/-- C2/C3: on every non-FTS position the paired projection is the legacy (#866) `Pos.proj`. -/
theorem proj_lower (position : Pos) (hn : ∀ index coord level node, position ≠ .wctNode index coord level node)
    (hl : ∀ index coord child, position ≠ .wctLeaf index coord child) : proj position = position.proj := by
  funext answer
  rw [Pos.proj_eq]
  cases position with
  | wctNode index coord level node => exact (hn index coord level node rfl).elim
  | wctLeaf index coord child => exact (hl index coord child rfl).elim
  | chain lay tree leaf i step => simp only [proj, Pos.high, ite_apply] <;> rfl
  | leaf lay tree leaf => simp only [proj, Pos.high, ite_apply] <;> rfl
  | node lay tree level node => simp only [proj, Pos.high, ite_apply] <;> rfl
  | forest index => simp only [proj, Pos.high, Bool.false_eq_true, ↓reduceIte]
  | wctChain index coord child t step => simp only [proj, Pos.high, ite_apply] <;> rfl
/-- The main (lower-tree) positions: the paired projection is `Pos.proj` (unconditional forms of `proj_lower`). -/
theorem proj_chain (lay : Layer) (tree leaf i step : Nat) :
    proj (.chain lay tree leaf i step) = (Pos.chain lay tree leaf i step).proj :=
  proj_lower _ (fun _ _ _ _ h => Pos.noConfusion h) (fun _ _ _ h => Pos.noConfusion h)
theorem proj_leaf (lay : Layer) (tree leaf : Nat) : proj (.leaf lay tree leaf) = (Pos.leaf lay tree leaf).proj :=
  proj_lower _ (fun _ _ _ _ h => Pos.noConfusion h) (fun _ _ _ h => Pos.noConfusion h)
theorem proj_node (lay : Layer) (tree level node : Nat) :
    proj (.node lay tree level node) = (Pos.node lay tree level node).proj :=
  proj_lower _ (fun _ _ _ _ h => Pos.noConfusion h) (fun _ _ _ h => Pos.noConfusion h)

/-- C1: a leaf position projects onto the half of its heap `128 + physical`. -/
theorem proj_wctLeaf (index coord child : Nat) :
    proj (.wctLeaf index coord child) = ClaudeWCT.WCT9.ftsHalf (128 + physical coord child) := by
  funext answer
  have hiff := ClaudeWCT.WCT9.ftsHighHeap_iff (show 4 ≤ 128 + physical coord child by omega)
  by_cases h : physical coord child % 2 = 0
  · have ht : ClaudeWCT.WCT9.ftsHighHeap (128 + physical coord child) = true := hiff.mpr ⟨by omega, by omega⟩
    simp [proj, highLeafAt, h, ClaudeWCT.WCT9.ftsHalf, ht]
  · have hf : ClaudeWCT.WCT9.ftsHighHeap (128 + physical coord child) = false :=
      Bool.eq_false_iff.mpr (fun ht => h (by have := (hiff.mp ht).2; omega))
    simp [proj, highLeafAt, h, ClaudeWCT.WCT9.ftsHalf, hf]

/-- C1: below the top folds (`level ≤ 3`, heaps `8..127`) the high nodes are exactly the `ftsHighHeap` heaps. -/
theorem highNodeAt_packed (coord level node : Nat) (hl : level ≤ 3) (hn : node < 2 ^ (6 - level)) :
    ClaudeWCT.WCT9.ftsHighHeap (2 ^ (6 - level) + node) = decide (highNodeAt coord level node) := by
  have hp : ¬(highPosition coord level ∨ singletonHigh coord level node) := by
    unfold highPosition singletonHigh; omega
  have h4 : 4 ≤ 2 ^ (6 - level) + node := by interval_cases level <;> norm_num <;> omega
  have hiff := ClaudeWCT.WCT9.ftsHighHeap_iff h4
  have he : (16 ≤ 2 ^ (6 - level) + node ∧ (2 ^ (6 - level) + node) % 2 = 0) ↔ (level ≤ 2 ∧ node % 2 = 0) := by
    interval_cases level <;> norm_num at hn ⊢ <;> omega
  have hh : highNodeAt coord level node ↔ (level ≤ 2 ∧ node % 2 = 0) := by
    unfold highNodeAt
    exact ⟨fun h => h.resolve_left hp, Or.inr⟩
  by_cases hc : level ≤ 2 ∧ node % 2 = 0
  · rw [decide_eq_true (hh.mpr hc)]
    exact hiff.mpr (he.mpr hc)
  · rw [decide_eq_false (fun h => hc (hh.mp h))]
    exact Bool.eq_false_iff.mpr (fun ht => hc (he.mp (hiff.mp ht)))

/-- C1: below the top folds (`level ≤ 3`, heaps `8..127`) a node position projects onto the half of its heap. -/
theorem proj_wctNode_packed (index coord level node : Nat) (hl : level ≤ 3) (hn : node < 2 ^ (6 - level)) :
    proj (.wctNode index coord level node) = ClaudeWCT.WCT9.ftsHalf (2 ^ (6 - level) + node) := by
  funext answer
  have hh := highNodeAt_packed coord level node hl hn
  by_cases hc : highNodeAt coord level node
  · rw [decide_eq_true hc] at hh
    simp [proj, hc, ClaudeWCT.WCT9.ftsHalf, hh]
  · rw [decide_eq_false hc] at hh
    simp [proj, hc, ClaudeWCT.WCT9.ftsHalf, hh]

/-- C1: a node of level `level` hashes into the half of `highNodeAt coord level node`. -/
def nodeProgram (coord level node : Nat) (input : HashInput) : M Digest :=
  if highNodeAt coord level node then ClaudeWCT.WCT9.highHash input else shortHash input

set_option backward.isDefEq.respectTransparency false in
theorem eval_nodeProgram (answers : Answers) (index coord level node : Nat) (input : HashInput) :
    evalWithAnswerFn answers (nodeProgram coord level node input) =
      proj (.wctNode index coord level node) (answers (.inl (.inr (pad64 input)))) := by
  by_cases hp : highNodeAt coord level node
  · simp only [nodeProgram, proj, if_pos hp]
    rfl
  · simp only [nodeProgram, proj, if_neg hp]
    rfl

/-- Stage 2: an outer node other than the singleton's right top node (heap 3) keeps the high half. -/
theorem sharedOuterHash_of_high {coord heap : Nat} (h : ¬(coord = 8 ∧ heap = 3)) (index : Nat) (left right : Digest) :
    SharedForest.sharedOuterHash coord index heap left right =
      ClaudeWCT.WCT9.highHash (ClaudeWCT.WCT9.wctTopInput coord index heap left 0 right) := by
  unfold SharedForest.sharedOuterHash
  simp only [if_neg h]

/-- Stage 2: the singleton's right top node (heap 3) keeps the low half. -/
theorem sharedOuterHash_of_low {coord heap : Nat} (h : coord = 8 ∧ heap = 3) (index : Nat) (left right : Digest) :
    SharedForest.sharedOuterHash coord index heap left right =
      shortHash (ClaudeWCT.WCT9.wctTopInput coord index heap left 0 right) := by
  unfold SharedForest.sharedOuterHash
  simp only [if_pos h]

set_option backward.isDefEq.respectTransparency false in
/-- C1: the paired node at heap `2^(6-level)+node`, for any branch pads `ps`, is the fixed-projection hash of its
`wctTopInput`. -/
theorem sharedNode_eq_nodeProgramP (index coord level node : Nat) (hc : coord < 9) (hl : level < 6)
    (hn : node < 2^(6-level)) (hu : first coord = true → level < 5) (ps : Nat → SharedForest.PairRoot)
    (left right : Digest) :
    SharedForest.sharedNode (first coord) coord index (2^(6-level)+node) ps left right =
    nodeProgram coord level node (ClaudeWCT.WCT9.wctTopInput coord index (2^(6-level)+node) left
      (if level=4 then (ps ((2^(6-level)+node)/2-2)).2 else 0) right) := by
  have h4 : (2^(6-level)+node<4) ↔ level=5 := by
    interval_cases level <;> norm_num at hn ⊢ <;> omega
  have h8 : (2^(6-level)+node<8) ↔ 4≤level := by
    interval_cases level <;> norm_num at hn ⊢ <;> omega
  simp only [SharedForest.sharedNode, h4, h8]
  by_cases h5 : level=5
  · subst level
    have hnode2 : node < 2 := by
      have h := hn
      norm_num at h
      omega
    have hf : first coord = false := Bool.eq_false_iff.mpr (by intro h; have := hu h; omega)
    have hn : ¬(coord<8 ∧ coord%2=0) := by
      simpa only [first, decide_eq_false_iff_not] using hf
    by_cases hco : coord=8
    · subst coord
      -- Stage 2 (Cm): heap 2 (node 0) keeps the high half, heap 3 (node 1) the low half.
      rcases (show node = 0 ∨ node = 1 by omega) with rfl | rfl
      · have hp : highNodeAt 8 5 0 := (highNodeAt_singleton 0).mpr rfl
        rw [sharedOuterHash_of_high (by decide : ¬((8:Nat) = 8 ∧ 2^(6-5)+0 = 3))]
        simp only [nodeProgram, if_pos hp, ↓reduceIte]
        rfl
      · have hp : ¬highNodeAt 8 5 1 := fun h => absurd ((highNodeAt_singleton 1).mp h) (by decide)
        rw [sharedOuterHash_of_low (by decide : (8:Nat) = 8 ∧ 2^(6-5)+1 = 3)]
        simp only [nodeProgram, if_neg hp, ↓reduceIte]
        rfl
    · have hp : highNodeAt coord 5 node := Or.inl (Or.inl (by unfold highPosition; omega))
      rw [sharedOuterHash_of_high (fun h => hco h.1)]
      simp only [if_pos rfl, nodeProgram, if_pos hp, ↓reduceIte]
      rfl
  · simp only [if_neg h5]
    by_cases hlev : level=4
    · subst level
      simp only [show 4≤4 by decide, if_true, if_pos rfl]
      by_cases hf : first coord=true
      · have hp : highNodeAt coord 4 node := by
          have hc := of_decide_eq_true hf
          exact Or.inl (Or.inl ⟨hc.1,Or.inl ⟨hc.2,rfl⟩⟩)
        simp only [hf, if_true, nodeProgram, if_pos hp, ↓reduceIte]
      · have hp : ¬highNodeAt coord 4 node := by
          intro hp
          rcases hp with (hp|hp)|hp
          · apply hf
            simp only [first, decide_eq_true_eq]
            exact ⟨hp.1, by rcases hp.2 with hp|hp <;> omega⟩
          · exact not_singletonHigh_of_level (by decide) hp
          · omega
        simp only [hf, if_false, nodeProgram, if_neg hp, ↓reduceIte]
        rfl
    · have hlt : level<4 := by omega
      simp only [if_neg (show ¬4≤level by omega), if_neg hlev, ↓reduceIte]
      have hnode : ClaudeWCT.WCT9.wctNodeHashH coord index (2^(6-level)+node) left right =
          ClaudeWCT.WCT9.ftsHash (2^(6-level)+node) (ClaudeWCT.WCT9.wctTopInput coord index (2^(6-level)+node) left 0 right) := by
        unfold ClaudeWCT.WCT9.wctNodeHashH ClaudeWCT.WCT9.wctTopInput
        rw [ClaudeWCT.WCT9.bytesLE_zero16]
      rw [hnode]
      have hpk := highNodeAt_packed coord level node (by omega) hn
      by_cases hh : highNodeAt coord level node
      · rw [decide_eq_true hh] at hpk
        rw [ClaudeWCT.WCT9.ftsHash_of_high hpk]
        simp only [nodeProgram, if_pos hh]
      · rw [decide_eq_false hh] at hpk
        rw [ClaudeWCT.WCT9.ftsHash_of_low hpk]
        simp only [nodeProgram, if_neg hh]


noncomputable def honestInput (answers : Answers) : Pos → HashInput
  | .wctLeaf index coord child => pad64 (wctLeafInputP index coord child
      (pads answers index coord (physical coord child/64)).1 (wctEnds answers index coord child))
  | .wctNode index coord level node =>
      let heap := 2^(6-level)+node
      pad64 (ClaudeWCT.WCT9.wctTopInput coord index heap
        ((nodes answers index coord).getD (2*heap) 0)
        (if level = 4 then (pads answers index coord (heap/2-2)).2 else 0)
        ((nodes answers index coord).getD (2*heap+1) 0))
  | position => Extract.honestInput answers position

/-- Only positions actually constructed by the paired source are charged. -/
def Bounded (position : Pos) : Prop :=
  match position with
  | .forest _ => False
  | .wctNode _ coord level _ => position.Bounded ∧ (first coord = true → level < 5)
  | _ => position.Bounded

theorem Bounded.legacy {position : Pos} (h : Bounded position) : position.Bounded := by
  cases position <;> simp only [Bounded] at h <;> first | exact h | exact h.1

def HashHitAt (answers : Answers) (position : Pos) (honest actual : HashInput) : Prop :=
  actual ≠ honest ∧ proj position (answers (.inl (.inr actual))) =
    proj position (answers (.inl (.inr honest)))

def HitIn (answers : Answers) (queries : List Spec.Domain) : Prop :=
  ∃ position actual, Bounded position ∧ .inl (.inr actual) ∈ queries ∧
    HashHitAt answers position (honestInput answers position) actual ∧
    SameHeader actual (honestInput answers position)

theorem HitIn.mono {answers : Answers} {queries queries' : List Spec.Domain}
    (hit : HitIn answers queries) (hsub : ∀ query ∈ queries, query ∈ queries') :
    HitIn answers queries' := by
  obtain ⟨position, actual, hb, hq, hh, hs⟩ := hit
  exact ⟨position, actual, hb, hsub _ hq, hh, hs⟩

theorem input_eq_of_no_hit {answers : Answers} {queries : List Spec.Domain}
    (hn : ¬HitIn answers queries) (position : Pos) (actual : HashInput)
    (hb : Bounded position) (hq : .inl (.inr actual) ∈ queries)
    (hs : SameHeader actual (honestInput answers position))
    (hout : proj position (answers (.inl (.inr actual))) =
      proj position (answers (.inl (.inr (honestInput answers position))))) :
    actual = honestInput answers position := by
  by_contra he
  exact hn ⟨position, actual, hb, hq, ⟨he,hout⟩, hs⟩

theorem first_even (pair : Nat) (hp : pair < 4) : first (2*pair) = true := by
  simp only [first, decide_eq_true_eq]
  omega

theorem first_odd (pair : Nat) : first (2*pair+1) = false := by
  simp only [first, decide_eq_false_iff_not]
  omega

theorem pads_even (answers : Answers) (index pair branch : Nat) (hp : pair < 4) :
    pads answers index (2*pair) branch = pairPrev answers index pair := by
  simp only [pads, if_neg (show 2*pair ≠ 8 by omega), first_even pair hp, if_true,
    Nat.mul_div_cancel_left pair (by decide : 0<2)]

theorem pads_odd (answers : Answers) (index pair branch : Nat) :
    pads answers index (2*pair+1) branch = SharedForest.nodesPair
      (SharedForest.firstNodes answers index pair (pairPrev answers index pair)) branch := by
  simp only [pads, if_neg (show 2*pair+1 ≠ 8 by omega), first_odd pair, Bool.false_eq_true, if_false]
  rw [show (2*pair+1)/2 = pair by omega]

theorem nodes_even (answers : Answers) (index pair : Nat) (hp : pair < 4) :
    nodes answers index (2*pair) = SharedForest.firstNodes answers index pair (pairPrev answers index pair) := by
  simp only [nodes, if_neg (show 2*pair ≠ 8 by omega), first_even pair hp, if_true,
    Nat.mul_div_cancel_left pair (by decide : 0<2)]

theorem nodes_odd (answers : Answers) (index pair : Nat) :
    nodes answers index (2*pair+1) = SharedForest.secondNodes answers index pair (pairPrev answers index pair) := by
  simp only [nodes, if_neg (show 2*pair+1 ≠ 8 by omega), first_odd pair, Bool.false_eq_true, if_false]
  rw [show (2*pair+1)/2 = pair by omega]

theorem singleton_top (answers : Answers) (index : Nat) :
    ((nodes answers index 8).getD 2 0, (nodes answers index 8).getD 3 0) =
      SharedForest.forestCommitment answers index := by
  rfl

end ClaudeWCT.W9.T3M.Extract.Paired
end
-- ==== merged from ClaudeWCT_W9_T3M_Extract_HdrBlocks ====
section

namespace ClaudeWCT.W9.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SigGolfCandidate.T3M.Extract (canonicalHeader_high_zero canonicalHeader_marker_ne)
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
theorem hdrBlock_prefix' (a h : Digest) (rest : HashInput) :
    hdrBlock (bytesLE 16 a ++ bytesLE 16 h ++ rest) = bytesLE 16 h := by
  unfold hdrBlock
  rw [List.append_assoc, List.drop_left' (bytesLE_length 16 a), List.take_left' (bytesLE_length 16 h)]
theorem hdrBlock_pad64' (input : HashInput) (h : 32 ≤ input.length) :
    hdrBlock (pad64 input) = hdrBlock input := by
  unfold hdrBlock pad64
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
theorem hdrBlock_block4' (a b c d : Digest) : hdrBlock (block4 a b c d) = bytesLE 16 b := by
  unfold block4
  rw [List.append_assoc]
  exact hdrBlock_prefix' a b _
theorem hdrBlock_listInput' (first : Digest) (hdr : BitVec 128) (rest : List Digest) :
    hdrBlock (pad64 (listInput first hdr rest)) = bytesLE 16 hdr := by
  have hl : 32 ≤ (listInput first hdr rest).length := by
    simp only [listInput, List.length_append, bytesLE_length]; omega
  rw [hdrBlock_pad64' _ hl]
  exact hdrBlock_prefix' first hdr _
theorem bytesLE_zero' : bytesLE 16 (0 : Digest) = zero16 := by decide
theorem wctChainInput_block4 (index coord child t step : Nat) (value : Digest) :
    WCT9.chainInput index coord child t step value =
      block4 0 (WCT9.ftsChainHeader index coord child t step) 0 value := by
  simp only [WCT9.chainInput, block4, bytesLE_zero']
theorem pad64_wctChainInput (index coord child t step : Nat) (value : Digest) :
    pad64 (WCT9.chainInput index coord child t step value) = WCT9.chainInput index coord child t step value := by
  rw [wctChainInput_block4, pad64_block4]
theorem hdrBlock_wctChainInput (index coord child t step : Nat) (value : Digest) :
    hdrBlock (WCT9.chainInput index coord child t step value) =
      bytesLE 16 (WCT9.ftsChainHeader index coord child t step) := by
  rw [wctChainInput_block4, hdrBlock_block4']
/-- Witness stack: the FTS step input in either format (G chains 1, 3: `value | header | 0 | 0`). -/
theorem ftsChainInputW_block4 (index coord child t step : Nat) (value : Digest) :
    WCT9.ftsChainInputW index coord child t step value =
      if WCT9.ftsIsG t then block4 value (WCT9.ftsChainHeader index coord child t step) 0 0
      else block4 0 (WCT9.ftsChainHeader index coord child t step) 0 value := by
  unfold WCT9.ftsChainInputW
  split
  · simp only [block4, bytesLE_zero']
  · exact wctChainInput_block4 index coord child t step value
theorem hdrBlock_ftsChainInputW (index coord child t step : Nat) (value : Digest) :
    hdrBlock (WCT9.ftsChainInputW index coord child t step value) =
      bytesLE 16 (WCT9.ftsChainHeader index coord child t step) := by
  rw [ftsChainInputW_block4]
  split <;> exact hdrBlock_block4' _ _ _ _
theorem hdrBlock_wctLeafInput (index coord child : Nat) (ends : List Digest) :
    hdrBlock (pad64 (wctLeafInput index coord child ends)) = bytesLE 16 (WCT9.ftsLeafHeader index coord child) :=
  hdrBlock_listInput' _ _ _
theorem hdrBlock_wctLeafInputP (index coord child : Nat) (pad : Digest) (ends : List Digest) :
    hdrBlock (pad64 (wctLeafInputP index coord child pad ends)) = bytesLE 16 (WCT9.ftsLeafHeader index coord child) :=
  hdrBlock_listInput' _ _ _
theorem hdrBlock_forestInput (index : Nat) (pairs : List (Digest × Digest)) :
    hdrBlock (pad64 (forestInput index pairs)) = bytesLE 16 (header 15 0 index 0 0) := by
  have hl : 32 ≤ (forestInput index pairs).length := by
    simp only [forestInput, WCT9.forestInput, zero16, List.length_append, List.length_replicate, bytesLE_length]
    omega
  rw [hdrBlock_pad64' _ hl]
  unfold forestInput WCT9.forestInput
  rw [← bytesLE_zero']
  exact hdrBlock_prefix' 0 _ _
theorem hdrBlock_nodeInputP (tag lay tree heap : Nat) (left pad right : Digest) :
    hdrBlock (pad64 (nodeInputP tag lay tree heap left pad right)) = bytesLE 16 (nodeTweak tag lay tree heap) := by
  rw [pad64_nodeInputP, nodeInputP, hdrBlock_block4']
theorem hdrBlock_merkleNodeInput (lay tree heap : Nat) (left right : Digest) :
    hdrBlock (pad64 (WCT9.merkleNodeInput lay tree heap left right)) = bytesLE 16 (WCT9.merkleTweak lay tree heap) := by
  unfold WCT9.merkleNodeInput
  rw [hdrBlock_pad64' _ (by simp [bytesLE_length, zero16]), List.append_assoc]
  exact hdrBlock_prefix' _ _ _
/-- Top-nonce layer: the nonce slot is the third block, so the header block is the tweak. -/
theorem hdrBlock_merkleNodeInputN (lay tree heap n : Nat) (left right : Digest) :
    hdrBlock (pad64 (WCT9.merkleNodeInputN lay tree heap n left right)) =
      bytesLE 16 (WCT9.merkleTweak lay tree heap) := by
  unfold WCT9.merkleNodeInputN
  rw [hdrBlock_pad64' _ (by simp [bytesLE_length]), List.append_assoc]
  exact hdrBlock_prefix' _ _ _
theorem hdrBlock_wotsChainInput (lay : Layer) (tree leaf i step : Nat) (value : Digest) :
    hdrBlock (chainInput lay tree leaf i step value) = bytesLE 16 (chainHeader lay tree leaf i step) :=
  chainInput_header lay tree leaf i step value
theorem hdrBlock_leafInput (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    hdrBlock (pad64 (leafInput lay tree leaf ends)) = bytesLE 16 (leafTweak lay tree leaf) := by
  unfold leafInput SigGolfCandidate.T3.leafInput
  split <;>
  · rw [hdrBlock_pad64' _ (by simp [bytesLE_length]; omega), List.append_assoc]
    exact hdrBlock_prefix' _ _ _

theorem listInput_length' (first : Digest) (hdr : BitVec 128) (rest : List Digest) :
    (listInput first hdr rest).length = 32 + 16 * rest.length := by
  simp only [listInput, List.length_append, bytesLE_length, digest_list_bytes_length]
theorem hdrBlock_honestInput (answers : Answers) (p : Pos) :
    hdrBlock (honestInput answers p) = bytesLE 16 p.hdr := by
  cases p with
  | chain lay tree lf i step =>
      simp only [honestInput, Pos.hdr, WCT9.chainInputW_padded, hdrBlock, WCT9.chainInputW_header]
  | leaf lay tree lf => simp only [honestInput, Pos.hdr]; rw [hdrBlock_leafInput]
  | node lay tree level nd =>
      simp only [honestInput, Pos.hdr]; rw [hdrBlock_merkleNodeInputN]
  | forest index => simp only [honestInput, Pos.hdr]; rw [hdrBlock_forestInput]
  | wctChain index coord child t step =>
      simp only [honestInput, Pos.hdr]; rw [WCT9.ftsChainInputW_padded, hdrBlock_ftsChainInputW]
  | wctLeaf index coord child =>
      simp only [honestInput, Pos.hdr]; rw [hdrBlock_wctLeafInputP]
  | wctNode index coord level nd =>
      simp only [honestInput, Pos.hdr]; rw [hdrBlock_nodeInputP]; rfl
theorem pad64_length_of_mod {x : HashInput} (h : x.length % 64 = 0) : (pad64 x).length = x.length := by
  unfold pad64; simp [h]
theorem honestInput_length (answers : Answers) (p : Pos) : (honestInput answers p).length = p.len := by
  cases p with
  | chain lay tree leaf i step =>
      simp only [honestInput, Pos.len]
      rw [pad64_length_of_mod] <;> simp [WCT9.chainInputW_length]
  | leaf lay tree leaf =>
      simp only [honestInput, Pos.len, leafInput, SigGolfCandidate.T3.leafInput]
      split
      · rename_i h0
        have hc' : chainCount lay = 51 := by subst h0; rfl
        rw [pad64_length_of_mod] <;>
          simp only [List.length_append, bytesLE_length, digest_list_bytes_length, List.length_drop,
            List.length_map, List.length_range, hc'] <;> decide
      · rename_i h0
        have hc' : chainCount lay = 43 := by fin_cases lay <;> simp_all <;> decide
        rw [pad64_length_of_mod] <;>
          simp only [List.length_append, bytesLE_length, digest_list_bytes_length, List.length_drop,
            List.length_map, List.length_range, hc'] <;> decide
  | node lay tree level nd =>
      simp only [honestInput, Pos.len]
      rw [WCT9.pad64_merkleNodeInputN, WCT9.merkleNodeInputN_length]
  | forest index =>
      simp only [honestInput, Pos.len]
      have hl : (forestInput index (ftsPairsHonest answers index)).length = 320 := by
        simp only [forestInput, WCT9.forestInput, List.length_append, zero16, List.length_replicate, bytesLE_length,
          List.length_flatMap, ftsPairsHonest, List.map_map]
        simp [Function.comp_def]
      rw [pad64_length_of_mod] <;> rw [hl]
  | wctChain index coord child t step =>
      simp only [honestInput, Pos.len]
      rw [WCT9.ftsChainInputW_padded, WCT9.ftsChainInputW_length]
  | wctLeaf index coord child =>
      simp only [honestInput, Pos.len]
      rw [pad64_length_of_mod] <;> simp [wctLeafInputP, listInput, bytesLE_length, wctEnds]
  | wctNode index coord level nd =>
      simp only [honestInput, Pos.len]
      rw [pad64_length_of_mod] <;> simp [nodeInputP]

theorem tweakLow_eq_low (h : BitVec 128) : tweakLow h = (h.extractLsb' 0 64).toNat := by
  unfold tweakLow; rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
/-- C4: the low word of a 16-byte header is read from its first 8 bytes. -/
theorem readLE_take8 (h : BitVec 128) : readLE ((bytesLE 16 h).take 8) = tweakLow h := by
  have he : h = h.extractLsb' 64 64 ++ h.extractLsb' 0 64 :=
    (BitVec.extractLsb'_append_extractLsb' (w := 64) (len := 64) (x := h)).symm
  conv_lhs => rw [he, SigGolfCandidate.T3M.Extract.bytesLE_header_words, List.take_left' (bytesLE_length 8 _)]
  rw [SigGolfCandidate.T3M.readLE_bytesLE, tweakLow_eq_low]
theorem topLow_bytesLE_iff (h : BitVec 128) : TopLow (bytesLE 16 h) ↔ 1 ≤ tweakLow h ∧ tweakLow h < 2 ^ 16 := by
  unfold TopLow; rw [readLE_take8]
end ClaudeWCT.W9.T3M.Extract
end
-- ==== merged from ClaudeWCT_W9_T3M_Extract_Leaf ====
section

namespace ClaudeWCT.W9.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3M
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers treeValue)
open ClaudeWCT.WCT9 (wotsTree wotsSeed wotsEnd wotsValue wotsRoot)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem flatMap_bytes_injective : ∀ {xs ys : List Digest}, xs.length = ys.length →
    xs.flatMap (bytesLE 16) = ys.flatMap (bytesLE 16) → xs = ys
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, hlen, h => by
      simp only [List.flatMap_cons] at h
      obtain ⟨hxy, hrest⟩ := List.append_inj h (by simp only [bytesLE_length])
      rw [bytesLE_injective hxy, flatMap_bytes_injective (by simpa using hlen) hrest]
theorem listInput_length (first : Digest) (hdr : BitVec 128) (rest : List Digest) :
    (listInput first hdr rest).length = 32 + 16 * rest.length := by
  simp only [listInput, List.length_append, bytesLE_length, digest_list_bytes_length]
theorem listInput_injective {first first' : Digest} {hdr hdr' : BitVec 128} {rest rest' : List Digest}
    (hlen : rest.length = rest'.length) (h : listInput first hdr rest = listInput first' hdr' rest') :
    first = first' ∧ hdr = hdr' ∧ rest = rest' := by
  unfold listInput at h
  obtain ⟨h, hr⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨hf, hh⟩ := List.append_inj h (by simp only [bytesLE_length])
  exact ⟨bytesLE_injective hf, bytesLE_injective hh, flatMap_bytes_injective hlen hr⟩
theorem list_head_drop : ∀ (xs : List Digest), 0 < xs.length → xs.getD 0 0 :: xs.drop 1 = xs
  | _ :: _, _ => rfl
theorem listInput_lists {xs ys : List Digest} {hdr hdr' : BitVec 128} (hlen : xs.length = ys.length)
    (hpos : 0 < ys.length)
    (h : pad64 (listInput (xs.getD 0 0) hdr (xs.drop 1)) = pad64 (listInput (ys.getD 0 0) hdr' (ys.drop 1))) :
    xs = ys ∧ hdr = hdr' := by
  have hl : (listInput (xs.getD 0 0) hdr (xs.drop 1)).length = (listInput (ys.getD 0 0) hdr' (ys.drop 1)).length := by
    rw [listInput_length, listInput_length, List.length_drop, List.length_drop, hlen]
  obtain ⟨hf, hh, hr⟩ := listInput_injective (by rw [List.length_drop, List.length_drop, hlen])
    (Sampling.pad64_inj_of_length hl h)
  refine ⟨?_, hh⟩
  rw [← list_head_drop xs (by omega), ← list_head_drop ys hpos, hf, hr]
theorem hdrBlock_prefix (a h : Digest) (rest : HashInput) :
    hdrBlock (bytesLE 16 a ++ bytesLE 16 h ++ rest) = bytesLE 16 h := by
  unfold hdrBlock
  rw [List.append_assoc, List.drop_left' (bytesLE_length 16 a), List.take_left' (bytesLE_length 16 h)]
theorem hdrBlock_pad64 (input : HashInput) (h : 32 ≤ input.length) : hdrBlock (pad64 input) = hdrBlock input := by
  unfold hdrBlock pad64
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
theorem hdrBlock_block4 (a b c d : Digest) : hdrBlock (block4 a b c d) = bytesLE 16 b := by
  unfold block4
  rw [List.append_assoc]
  exact hdrBlock_prefix a b _
theorem hdrBlock_listInput (first : Digest) (hdr : BitVec 128) (rest : List Digest) :
    hdrBlock (pad64 (listInput first hdr rest)) = bytesLE 16 hdr := by
  rw [hdrBlock_pad64 _ (by rw [listInput_length]; omega)]
  exact hdrBlock_prefix first hdr _
private theorem hdrBlock_forestInput_leaf (index : Nat) (pairs : List (Digest × Digest)) :
    hdrBlock (pad64 (forestInput index pairs)) = bytesLE 16 (header 15 0 index 0 0) := by
  rw [hdrBlock_pad64 _ (by simp only [forestInput, WCT9.forestInput, zero16, List.length_append,
    List.length_replicate, bytesLE_length]; omega)]
  unfold forestInput WCT9.forestInput
  rw [show zero16 = bytesLE 16 (0 : Digest) by decide]
  exact hdrBlock_prefix 0 _ _
/-- C4: a legacy leaf hash keeps the half `leafHalfHigh lay leaf` (high for even top leaves). -/
theorem leafHash_eq_projHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    leafHash lay tree leaf ends = projHash (leafHalfHigh lay leaf) (leafInput lay tree leaf ends) := rfl
theorem leafHash_eq_shortHash {lay : Layer} (h : lay ≠ 0) (tree leaf : Nat) (ends : List Digest) :
    leafHash lay tree leaf ends = shortHash (leafInput lay tree leaf ends) := leafHash_lower h tree leaf ends
theorem forestPk_eq_shortHash (index : Nat) (pairs : List (Digest × Digest)) :
    WCT9.forestPk index pairs = shortHash (forestInput index pairs) := rfl
theorem forestInput_pairs_injective {index : Nat} {ps qs : List (Digest × Digest)} (hl : ps.length = qs.length)
    (h : pad64 (forestInput index ps) = pad64 (forestInput index qs)) : ps = qs := by
  have hlen : (forestInput index ps).length = (forestInput index qs).length := by
    simp only [forestInput, WCT9.forestInput, zero16, List.length_append, List.length_replicate, bytesLE_length,
      WCT9.pairs_bytes_length, hl]
  have h := Sampling.pad64_inj_of_length hlen h
  unfold forestInput WCT9.forestInput at h
  obtain ⟨-, hp⟩ := List.append_inj h (by simp only [zero16, List.length_append, List.length_replicate,
    bytesLE_length])
  exact WCT9.pairs_bytes_injective hl hp
theorem listHash_extract (answers : Answers) (hdr : BitVec 128) (xs ys : List Digest)
    (hlen : xs.length = ys.length) (hpos : 0 < ys.length)
    (reaches : evalWithAnswerFn answers (shortHash (listInput (xs.getD 0 0) hdr (xs.drop 1))) =
      evalWithAnswerFn answers (shortHash (listInput (ys.getD 0 0) hdr (ys.drop 1)))) :
    xs = ys ∨
      (HashHit answers (pad64 (listInput (ys.getD 0 0) hdr (ys.drop 1)))
          (pad64 (listInput (xs.getD 0 0) hdr (xs.drop 1))) ∧
        SameHeader (pad64 (listInput (xs.getD 0 0) hdr (xs.drop 1)))
          (pad64 (listInput (ys.getD 0 0) hdr (ys.drop 1))) ∧
        .inl (.inr (pad64 (listInput (xs.getD 0 0) hdr (xs.drop 1)))) ∈
          queried answers (shortHash (listInput (xs.getD 0 0) hdr (xs.drop 1)))) := by
  by_cases heq : pad64 (listInput (xs.getD 0 0) hdr (xs.drop 1)) = pad64 (listInput (ys.getD 0 0) hdr (ys.drop 1))
  · exact Or.inl (listInput_lists hlen hpos heq).1
  · refine Or.inr ⟨⟨heq, ?_⟩, ?_, ?_⟩
    · rw [eval_shortHash, eval_shortHash] at reaches
      exact reaches
    · refine SameHeader.of_hdrBlock (pad64_length_congr ?_) (by rw [hdrBlock_listInput, hdrBlock_listInput])
      simp only [listInput, List.length_append, bytesLE_length, digest_list_bytes_length, List.length_drop, hlen]
    · rw [queried_shortHash]
      exact List.mem_singleton_self _
theorem leafInput_lists {lay : Layer} {tree leaf : Nat} {xs ys : List Digest} (hlen : xs.length = ys.length)
    (hpos : 0 < ys.length)
    (h : pad64 (leafInput lay tree leaf xs) = pad64 (leafInput lay tree leaf ys)) : xs = ys := by
  unfold leafInput SigGolfCandidate.T3.leafInput at h
  rw [ite_self, ite_self] at h
  exact (listInput_lists (hdr := leafTweak lay tree leaf) (hdr' := leafTweak lay tree leaf) hlen hpos h).1

theorem forestPk_extract (answers : Answers) (index : Nat) (pairs honest : List (Digest × Digest))
    (hlen : pairs.length = honest.length)
    (reaches : evalWithAnswerFn answers (WCT9.forestPk index pairs) =
      evalWithAnswerFn answers (WCT9.forestPk index honest)) :
    pairs = honest ∨
      (HashHit answers (pad64 (forestInput index honest)) (pad64 (forestInput index pairs)) ∧
        SameHeader (pad64 (forestInput index pairs)) (pad64 (forestInput index honest)) ∧
        .inl (.inr (pad64 (forestInput index pairs))) ∈ queried answers (WCT9.forestPk index pairs)) := by
  by_cases heq : pad64 (forestInput index pairs) = pad64 (forestInput index honest)
  · exact Or.inl (forestInput_pairs_injective hlen heq)
  · refine Or.inr ⟨⟨heq, ?_⟩, ?_, ?_⟩
    · rw [forestPk_eq_shortHash, forestPk_eq_shortHash, eval_shortHash, eval_shortHash] at reaches
      exact reaches
    · refine SameHeader.of_hdrBlock (pad64_length_congr ?_)
        (by rw [hdrBlock_forestInput_leaf, hdrBlock_forestInput_leaf])
      simp only [forestInput, WCT9.forestInput, List.length_append, zero16, List.length_replicate, bytesLE_length,
        List.length_flatMap]
      simp [Function.comp_def, bytesLE_length, hlen]
    · rw [forestPk_eq_shortHash, queried_shortHash]
      exact List.mem_singleton_self _
theorem forestPk_honest_extract (answers : Answers) (index : Nat) (hidx : index < 2 ^ 40)
    (pairs : List (Digest × Digest)) (hlen : pairs.length = 9)
    (reaches : evalWithAnswerFn answers (WCT9.forestPk index pairs) = honestForest answers index) :
    pairs = ftsPairsHonest answers index ∨ HitIn answers (queried answers (WCT9.forestPk index pairs)) := by
  rcases forestPk_extract answers index pairs (ftsPairsHonest answers index)
      (by rw [hlen, ftsPairsHonest_length]) reaches with h | ⟨hh, hs, hq⟩
  · exact Or.inl h
  · exact Or.inr ⟨.forest index, _, hidx, hq, hh, hs⟩
theorem queried_mapM_mem {α β : Type} (answers : Answers) (f : α → M β) :
    ∀ (l : List α), ∀ a ∈ l, ∀ q ∈ queried answers (f a), q ∈ queried answers (l.mapM f)
  | [], _, ha, _, _ => absurd ha (List.not_mem_nil)
  | x :: xs, a, ha, q, hq => by
      rw [List.mapM_cons, queried_bind, queried_bind]
      rcases List.mem_cons.mp ha with rfl | ha
      · exact List.mem_append_left _ hq
      · exact List.mem_append_right _ (List.mem_append_left _ (queried_mapM_mem answers f xs a ha q hq))
/-! ### C2/C3 (FULL): half-aware hash paths and pads (shared with the Secc consumers, S2-6)
`hashPathW high input` is `hashPath input` with step `s` keeping the half `high s` (`WCT9.halfHash`). A hit on the
half `high` is `HashHitH answers high`; for a position `pos` it is `HashHitAt` (`hashHitAt_iff`, `pos.high`). -/
section halfPath
open ClaudeWCT.WCT9 (halfHash halfOf)
def hashPathW (high : Nat → Bool) (input : Nat → Digest → HashInput) (count : Nat) (initial : Digest) : M Digest :=
  (List.range count).foldlM (fun value step => halfHash (high step) (input step value)) initial
def pathValueW (answers : Answers) (high : Nat → Bool) (input : Nat → Digest → HashInput) (initial : Digest)
    (count : Nat) : Digest :=
  evalWithAnswerFn answers (hashPathW high input count initial)
def pathInputW (answers : Answers) (high : Nat → Bool) (input : Nat → Digest → HashInput) (initial : Digest)
    (step : Nat) : HashInput := input step (pathValueW answers high input initial step)
theorem eval_halfHash (answers : Answers) (high : Bool) (input : HashInput) :
    evalWithAnswerFn answers (halfHash high input) = halfOf high (answers (.inl (.inr (pad64 input)))) := by
  cases high <;> rfl
@[simp] theorem queried_halfHash (answers : Answers) (high : Bool) (input : HashInput) :
    queried answers (halfHash high input) = [.inl (.inr (pad64 input))] := by
  cases high <;> rfl
theorem hashPathW_succ (high : Nat → Bool) (input : Nat → Digest → HashInput) (count : Nat) (initial : Digest) :
    hashPathW high input (count + 1) initial =
      (hashPathW high input count initial >>= fun value => halfHash (high count) (input count value)) := by
  simp [hashPathW, List.range_succ, List.foldlM_append]
@[simp] theorem pathValueW_zero (answers : Answers) (high : Nat → Bool) (input : Nat → Digest → HashInput)
    (initial : Digest) : pathValueW answers high input initial 0 = initial := rfl
theorem pathValueW_succ (answers : Answers) (high : Nat → Bool) (input : Nat → Digest → HashInput)
    (initial : Digest) (step : Nat) :
    pathValueW answers high input initial (step + 1) =
      evalWithAnswerFn answers (halfHash (high step) (pathInputW answers high input initial step)) := by
  simp only [pathValueW, hashPathW_succ, evalWithAnswerFn_bind, pathInputW]
theorem pathInputW_queried (answers : Answers) (high : Nat → Bool) (input : Nat → Digest → HashInput)
    (initial : Digest) (count step : Nat) (hstep : step < count) :
    .inl (.inr (pad64 (pathInputW answers high input initial step))) ∈
      queried answers (hashPathW high input count initial) := by
  induction count with
  | zero => omega
  | succ count ih =>
      rw [hashPathW_succ, queried_bind]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hstep with hlt | rfl
      · exact List.mem_append_left _ (ih hlt)
      · apply List.mem_append_right
        simp only [queried_halfHash, List.mem_singleton]
        rfl
theorem hashPathW_false (input : Nat → Digest → HashInput) (count : Nat) (initial : Digest) :
    hashPathW (fun _ => false) input count initial = hashPath input count initial := rfl
/-- A hit on the half `high`: a different input whose output agrees with the honest one on that half. -/
def HashHitH (answers : Answers) (high : Bool) (honest actual : HashInput) : Prop :=
  actual ≠ honest ∧ halfOf high (answers (.inl (.inr actual))) = halfOf high (answers (.inl (.inr honest)))
theorem hashHitAt_iff (answers : Answers) (pos : Pos) (honest actual : HashInput) :
    HashHitAt answers pos honest actual ↔ HashHitH answers pos.high honest actual := Iff.rfl
theorem hashHitH_false {answers : Answers} {honest actual : HashInput} :
    HashHitH answers false honest actual ↔ HashHit answers honest actual := Iff.rfl
theorem hashPathW_extract (answers : Answers) (high : Nat → Bool) (input : Nat → Digest → HashInput)
    (honestInput : Nat → HashInput) (target : Nat → Digest) (Good : Nat → Prop)
    (initial : Digest) (count : Nat)
    (reference : ∀ step, step < count →
      evalWithAnswerFn answers (halfHash (high step) (honestInput step)) = target (step + 1))
    (parse : ∀ step, step < count → ∀ value,
      pad64 (input step value) = pad64 (honestInput step) → value = target step ∧ Good step)
    (reaches : pathValueW answers high input initial count = target count) :
    (initial = target 0 ∧ ∀ step, step < count → Good step) ∨
      ∃ step, step < count ∧
        .inl (.inr (pad64 (pathInputW answers high input initial step))) ∈
          queried answers (hashPathW high input count initial) ∧
        HashHitH answers (high step) (pad64 (honestInput step)) (pad64 (pathInputW answers high input initial step)) := by
  induction count with
  | zero => exact Or.inl ⟨reaches, fun step hstep => by omega⟩
  | succ count ih =>
      by_cases heq : pad64 (pathInputW answers high input initial count) = pad64 (honestInput count)
      · obtain ⟨hprev, hgood⟩ := parse count (by omega) _ heq
        rcases ih (fun step hstep => reference step (by omega))
          (fun step hstep => parse step (by omega)) hprev with ⟨hinit, hall⟩ | ⟨step, hstep, _, hhit⟩
        · left
          refine ⟨hinit, fun step hstep => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hstep with hlt | rfl
          · exact hall step hlt
          · exact hgood
        · exact Or.inr ⟨step, by omega, pathInputW_queried answers high input initial _ _ (by omega), hhit⟩
      · right
        refine ⟨count, by omega, pathInputW_queried answers high input initial _ _ (by omega), heq, ?_⟩
        have hr := reference count (by omega)
        rw [pathValueW_succ, eval_halfHash] at reaches
        rw [eval_halfHash] at hr
        exact reaches.trans hr.symm
/-! #### Chains (C3: lower chain 0's step 6 keeps the high half) -/
theorem honestChainValueW_succ (answers : Answers) (lay : Layer) (tree leaf i : Nat) (seed : Digest) (step : Nat) :
    evalWithAnswerFn answers (halfHash (WCT9.chainHigh lay i step) (WCT9.chainInputW lay tree leaf i step
      (honestChainValueW answers lay tree leaf i seed step))) =
        honestChainValueW answers lay tree leaf i seed (step + 1) := by
  unfold honestChainValueW
  rw [WCT9.eval_chainW_add]
  simp [WCT9.chainW]
/-- Before step 6 an F chain of the current scheme is the legacy chain. -/
theorem honestChainValueW_eq (answers : Answers) (lay : Layer) (tree leaf i : Nat) (seed : Digest) {step : Nat}
    (hG : WCT9.isG lay i = false) (hs : step ≤ 6) :
    honestChainValueW answers lay tree leaf i seed step = honestChainValue answers lay tree leaf i seed step := by
  unfold honestChainValueW honestChainValue
  rw [WCT9.chainW_of_low hG (fun s _ hs' => WCT9.chainHigh_eq_false_F hG (Or.inr (by omega)))]
/-- Pairing stage 1: the verifier's sub-chain input in either format. -/
def chainPathInputW (lay : Layer) (tree leaf i start : Nat) (pad0 pad1 : Digest) (headerPad : BitVec 64) :
    Nat → Digest → HashInput := fun step value =>
  chainInputPW lay tree leaf i (start + step) pad0 pad1 headerPad value
theorem wotsValue_eqW (answers : Answers) (lay : Layer) (tree leaf : Nat) (digits : List Nat) (i : Nat) :
    wotsValue answers lay tree leaf digits i =
      honestChainValueW answers lay tree leaf i (wotsSeed answers lay tree leaf i) (digits.getD i 0) := rfl
theorem wotsEnd_eqW (answers : Answers) (lay : Layer) (tree leaf i : Nat) :
    wotsEnd answers lay tree leaf i =
      honestChainValueW answers lay tree leaf i (wotsSeed answers lay tree leaf i) (maxDigit lay i) := rfl
theorem chainPW_eq_hashPathW (lay : Layer) (tree leaf i start count : Nat) (pad0 pad1 : Digest)
    (headerPad : BitVec 64) (initial : Digest) :
    chainPW lay tree leaf i start count pad0 pad1 headerPad initial =
      hashPathW (fun s => WCT9.chainHigh lay i (start + s)) (chainPathInputW lay tree leaf i start pad0 pad1 headerPad)
        count initial := by
  unfold chainPW hashPathW chainPathInputW
  rw [List.range'_eq_map_range, List.foldlM_map]
theorem chainPathW_extract (answers : Answers) (lay : Layer) (tree leaf i start count : Nat)
    (pad0 pad1 : Digest) (headerPad : BitVec 64) (value seed : Digest)
    (ht : tree < 2 ^ 31) (hl : leaf < 4096) (hi : i < 64)
    (hsteps : count = 0 ∨ start + count ≤ 8)
    (reaches : pathValueW answers (fun s => WCT9.chainHigh lay i (start + s))
        (chainPathInputW lay tree leaf i start pad0 pad1 headerPad) value count =
      honestChainValueW answers lay tree leaf i seed (start + count)) :
    (value = honestChainValueW answers lay tree leaf i seed start ∧
      (0 < count → pad0 = 0 ∧ pad1 = 0 ∧ headerPad = 0)) ∨
      ∃ step, step < count ∧
        .inl (.inr (pad64 (pathInputW answers (fun s => WCT9.chainHigh lay i (start + s))
          (chainPathInputW lay tree leaf i start pad0 pad1 headerPad) value step))) ∈
          queried answers (hashPathW (fun s => WCT9.chainHigh lay i (start + s))
            (chainPathInputW lay tree leaf i start pad0 pad1 headerPad) count value) ∧
        HashHitH answers (WCT9.chainHigh lay i (start + step))
          (pad64 (WCT9.chainInputW lay tree leaf i (start + step)
            (honestChainValueW answers lay tree leaf i seed (start + step))))
          (pad64 (pathInputW answers (fun s => WCT9.chainHigh lay i (start + s))
            (chainPathInputW lay tree leaf i start pad0 pad1 headerPad) value step)) := by
  have h := hashPathW_extract answers (fun s => WCT9.chainHigh lay i (start + s))
    (chainPathInputW lay tree leaf i start pad0 pad1 headerPad)
    (fun step => WCT9.chainInputW lay tree leaf i (start + step)
      (honestChainValueW answers lay tree leaf i seed (start + step)))
    (fun step => honestChainValueW answers lay tree leaf i seed (start + step))
    (fun _ => pad0 = 0 ∧ pad1 = 0 ∧ headerPad = 0) value count
    (fun step _ => by simpa only [Nat.add_assoc] using
      honestChainValueW_succ answers lay tree leaf i seed (start + step))
    (fun step hstep current heq => by
      have hs : start + step < 8 := by rcases hsteps with hz | hb <;> omega
      simp only [chainPathInputW, chainInputW_eq_zero _ _ _ _ _ _ ht hl hi hs, pad64_chainInputPW] at heq
      obtain ⟨hp0, hhp, hp1, hv⟩ := chainInputPW_fields heq
      exact ⟨hv, hp0, hp1, hhp⟩) reaches
  rcases h with ⟨hvalue, hpads⟩ | hhit
  · exact Or.inl ⟨by simpa using hvalue, fun hcount => hpads 0 hcount⟩
  · exact Or.inr hhit
/-! #### Lower Merkle folds (C2: packed node word with a witness high word, half by heap parity) -/
/-- Fold input `step` of a lower path (`layerPairP`). -/
def merkleInputW (lay tree height leaf : Nat) (path : Nat → Digest) (hpads : Nat → BitVec 64) (pads : Nat → Digest)
    (step : Nat) (value : Digest) : HashInput :=
  let pair := if leaf / 2 ^ step % 2 = 0 then (value, path step) else (path step, value)
  WCT9.lowerNodeInputP lay tree (2 ^ (height - step - 1) + leaf / 2 ^ (step + 1)) pair.1 (hpads step) (pads step) pair.2
/-- The half kept by fold `step` of a lower path. -/
def merkleHighW (lay height leaf step : Nat) : Bool := WCT9.lowerHigh lay (2 ^ (height - step - 1) + leaf / 2 ^ (step + 1))
theorem lowerNodeInputP_length (lay tree heap : Nat) (l : Digest) (hp : BitVec 64) (p r : Digest) :
    (WCT9.lowerNodeInputP lay tree heap l hp p r).length = 64 := by
  simp [WCT9.lowerNodeInputP, bytesLE_length]
@[simp] theorem pad64_lowerNodeInputP (lay tree heap : Nat) (l : Digest) (hp : BitVec 64) (p r : Digest) :
    pad64 (WCT9.lowerNodeInputP lay tree heap l hp p r) = WCT9.lowerNodeInputP lay tree heap l hp p r := by
  simp [pad64, lowerNodeInputP_length]
theorem lowerNodeInputP_fields {lay tree heap : Nat} {l l' p p' r r' : Digest} {hp hp' : BitVec 64}
    (h : WCT9.lowerNodeInputP lay tree heap l hp p r = WCT9.lowerNodeInputP lay tree heap l' hp' p' r') :
    l = l' ∧ hp = hp' ∧ p = p' ∧ r = r' := by
  unfold WCT9.lowerNodeInputP at h
  obtain ⟨h, hr⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨h, hpd⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨hl, ht⟩ := List.append_inj h (by simp only [bytesLE_length])
  exact ⟨bytesLE_injective hl, (append64_inj (bytesLE_injective ht)).1, bytesLE_injective hpd, bytesLE_injective hr⟩
theorem merkleInputW_parse (lay tree height leaf step : Nat) (path honestPath : Nat → Digest)
    (hpads : Nat → BitVec 64) (pads honestPads : Nat → Digest) (current target : Digest)
    (heq : pad64 (merkleInputW lay tree height leaf path hpads pads step current) =
      pad64 (merkleInputW lay tree height leaf honestPath (fun _ => 0) honestPads step target)) :
    current = target ∧ path step = honestPath step ∧ hpads step = 0 ∧ pads step = honestPads step := by
  unfold merkleInputW at heq
  split at heq <;> simp only [pad64_lowerNodeInputP] at heq
  · obtain ⟨hc, hh, hp, hs⟩ := lowerNodeInputP_fields heq
    exact ⟨hc, hs, hh, hp⟩
  · obtain ⟨hs, hh, hp, hc⟩ := lowerNodeInputP_fields heq
    exact ⟨hc, hs, hh, hp⟩
theorem merklePathW_extract (answers : Answers) (lay tree height leaf count : Nat)
    (path honestPath target : Nat → Digest) (hpads : Nat → BitVec 64) (pads honestPads : Nat → Digest)
    (value : Digest)
    (reference : ∀ step, step < count →
      evalWithAnswerFn answers (halfHash (merkleHighW lay height leaf step)
        (merkleInputW lay tree height leaf honestPath (fun _ => 0) honestPads step (target step))) =
          target (step + 1))
    (reaches : pathValueW answers (merkleHighW lay height leaf) (merkleInputW lay tree height leaf path hpads pads)
      value count = target count) :
    (value = target 0 ∧ ∀ step, step < count → path step = honestPath step ∧ hpads step = 0 ∧
        pads step = honestPads step) ∨
      ∃ step, step < count ∧
        .inl (.inr (pad64 (pathInputW answers (merkleHighW lay height leaf)
          (merkleInputW lay tree height leaf path hpads pads) value step))) ∈
          queried answers (hashPathW (merkleHighW lay height leaf) (merkleInputW lay tree height leaf path hpads pads)
            count value) ∧
        HashHitH answers (merkleHighW lay height leaf step)
          (pad64 (merkleInputW lay tree height leaf honestPath (fun _ => 0) honestPads step (target step)))
          (pad64 (pathInputW answers (merkleHighW lay height leaf) (merkleInputW lay tree height leaf path hpads pads)
            value step)) :=
  hashPathW_extract answers _ _ _ target _ value count reference
    (fun step _ current => merkleInputW_parse lay tree height leaf step path honestPath hpads pads honestPads current
      (target step)) reaches
/-- Top-nonce layer: the honest node pads of the path of `leaf` (the keygen nonce digests on the top tree, 0 on
every lower tree and on the root). -/
noncomputable def honestPads (answers : Answers) (lay : Layer) (tree leaf : Nat) : Nat → Digest :=
  fun j => WCT9.nonceDigest (WCT9.honestNonce answers lay tree j (leaf / 2 ^ (j + 1)))
theorem honestPads_lower (answers : Answers) {lay : Layer} (h : lay ≠ 0) (tree leaf : Nat) :
    honestPads answers lay tree leaf = fun _ => 0 := by
  funext j
  unfold honestPads
  rw [WCT9.honestNonce_lower answers h, WCT9.nonceDigest_zero]
/-- The honest fold reference of every layer with the honest pads (top tree: nonce digests). -/
theorem merkleInputW_wotsTree_reference (answers : Answers) (lay : Layer) (tree leaf : Nat)
    (hleaf : leaf < 2 ^ height lay) (step : Nat) (hstep : step < height lay) :
    evalWithAnswerFn answers (halfHash (merkleHighW lay.val (height lay) leaf step)
      (merkleInputW lay.val tree (height lay) leaf (fun j => treeValue (WCT9.wotsTree answers lay tree) j (leaf / 2 ^ j ^^^ 1))
        (fun _ => 0) (honestPads answers lay tree leaf) step
        (treeValue (WCT9.wotsTree answers lay tree) step (leaf / 2 ^ step)))) =
      treeValue (WCT9.wotsTree answers lay tree) (step + 1) (leaf / 2 ^ (step + 1)) := by
  have hparent : leaf / 2 ^ (step + 1) < 2 ^ (height lay - step - 1) := by
    have := Correctness.div_pow_bound (start := 0) (level := step + 1)
      (node := leaf) (height := height lay) (by omega) (by simpa using hleaf)
    simpa [Nat.sub_sub] using this
  rw [WCT9.wotsTree_node_any answers lay tree step (leaf / 2 ^ (step + 1)) hstep hparent]
  unfold merkleInputW merkleHighW honestPads
  dsimp only
  rw [Correctness.sibling_pair, Correctness.div_pow_succ, ← WCT9.merkleNodeInputN_eq_lowerNodeInputP]
/-- C4: the honest fold reference on every layer (the top included). -/
theorem merkleInputW_tree_reference' (answers : Answers) (lay tree height leaf : Nat)
    (levels : List (List Digest)) (leaves : List Digest)
    (htree : WCT9.TreeLevelsL answers lay tree height leaves height levels)
    (hleaf : leaf < 2 ^ height) (step : Nat) (hstep : step < height) :
    evalWithAnswerFn answers (halfHash (merkleHighW lay height leaf step)
      (merkleInputW lay tree height leaf (fun j => treeValue levels j (leaf / 2 ^ j ^^^ 1)) (fun _ => 0) (fun _ => 0)
        step (treeValue levels step (leaf / 2 ^ step)))) =
      treeValue levels (step + 1) (leaf / 2 ^ (step + 1)) := by
  unfold merkleInputW merkleHighW
  dsimp only
  rw [Correctness.sibling_pair, Correctness.div_pow_succ, WCT9.lowerNodeInputP_zero']
  have hparent : leaf / 2 ^ (step + 1) < 2 ^ (height - (step + 1)) := by
    simpa using Correctness.div_pow_bound (start := 0) (level := step + 1)
      (node := leaf) (height := height) (by omega) (by simpa using hleaf)
  have hp := htree.2.2 step hstep (leaf / 2 ^ (step + 1)) hparent
  simpa only [treeValue, Nat.sub_sub, WCT9.lowerNodeHash, WCT9.lowerHash] using hp.symm
theorem merkleInputW_tree_reference (answers : Answers) (lay tree height leaf : Nat) (_hlay : lay ≠ 0)
    (levels : List (List Digest)) (leaves : List Digest)
    (htree : WCT9.TreeLevelsL answers lay tree height leaves height levels)
    (hleaf : leaf < 2 ^ height) (step : Nat) (hstep : step < height) :
    evalWithAnswerFn answers (halfHash (merkleHighW lay height leaf step)
      (merkleInputW lay tree height leaf (fun j => treeValue levels j (leaf / 2 ^ j ^^^ 1)) (fun _ => 0) (fun _ => 0)
        step (treeValue levels step (leaf / 2 ^ step)))) =
      treeValue levels (step + 1) (leaf / 2 ^ (step + 1)) :=
  merkleInputW_tree_reference' answers lay tree height leaf levels leaves htree hleaf step hstep
/-! #### Leaves (C3: witness pads in the leaf header block) -/
theorem leafInput_padded_length (lay : Layer) (tree leaf : Nat) (ends : List Digest)
    (hc : ends.length = chainCount lay) :
    (pad64 (leafInput lay tree leaf ends)).length = if lay = 0 then 832 else 704 := by
  unfold leafInput
  rw [pad64_length_of_mod] <;> rw [SigGolfCandidate.T3.leafInput_length, hc] <;> fin_cases lay <;> decide

theorem hdrBlock_leafInputW (lay : Layer) (tree leaf : Nat) (pad : Digest) (hi : BitVec 64) (ends : List Digest) :
    hdrBlock (pad64 (WCT9.leafInputW lay tree leaf pad hi ends)) = bytesLE 16 (WCT9.leafTweakW lay tree leaf hi) := by
  unfold WCT9.leafInputW
  split
  · rw [hdrBlock_pad64 _ (by simp only [List.length_append, bytesLE_length]; omega), List.append_assoc]
    exact hdrBlock_prefix _ _ _
  · rw [hdrBlock_pad64 _ (by simp only [List.length_append, bytesLE_length]; omega), List.append_assoc]
    exact hdrBlock_prefix _ _ _
theorem leafInputW_parse {lay : Layer} {tree leaf : Nat} {pad : Digest} {hi : BitVec 64} {ends honest : List Digest}
    (hlen : ends.length = honest.length) (hpos : 0 < honest.length)
    (h : pad64 (WCT9.leafInputW lay tree leaf pad hi ends) = pad64 (leafInput lay tree leaf honest)) :
    ends = honest ∧ hi = 0 := by
  -- T51 ("endpad"): every leaf, the top included, is `end_0 | tweak | end_1 ..`; `pad` is never read.
  rw [leafInput, ← WCT9.leafInputW_zero] at h
  unfold WCT9.leafInputW at h
  rw [ite_self, ite_self] at h
  obtain ⟨he, hh⟩ := listInput_lists (hdr := WCT9.leafTweakW lay tree leaf hi)
    (hdr' := WCT9.leafTweakW lay tree leaf 0) hlen hpos h
  exact ⟨he, (append64_inj hh).1⟩

theorem leafHashW_extract (answers : Answers) (lay : Layer) (tree leaf : Nat) (pad : Digest) (hi : BitVec 64)
    (ends honest : List Digest) (hlen : ends.length = honest.length) (hc : honest.length = chainCount lay)
    (reaches : evalWithAnswerFn answers (WCT9.leafHashW lay tree leaf pad hi ends) =
      evalWithAnswerFn answers (WCT9.lowerLeafHash lay tree leaf honest)) :
    (ends = honest ∧ hi = 0) ∨
      (HashHitH answers (WCT9.lowerHigh lay.val leaf) (pad64 (leafInput lay tree leaf honest))
          (pad64 (WCT9.leafInputW lay tree leaf pad hi ends)) ∧
        SameHeader (pad64 (WCT9.leafInputW lay tree leaf pad hi ends)) (pad64 (leafInput lay tree leaf honest)) ∧
        .inl (.inr (pad64 (WCT9.leafInputW lay tree leaf pad hi ends))) ∈
          queried answers (WCT9.leafHashW lay tree leaf pad hi ends)) := by
  have hpos : 0 < honest.length := by rw [hc]; fin_cases lay <;> decide
  by_cases heq : pad64 (WCT9.leafInputW lay tree leaf pad hi ends) = pad64 (leafInput lay tree leaf honest)
  · exact Or.inl (leafInputW_parse hlen hpos heq)
  · right
    refine ⟨⟨heq, ?_⟩, ?_, ?_⟩
    · rw [WCT9.lowerLeafHash_eq] at reaches
      unfold WCT9.leafHashW WCT9.lowerHash at reaches
      rw [eval_halfHash, eval_halfHash] at reaches
      exact reaches
    · have hl : (pad64 (WCT9.leafInputW lay tree leaf pad hi ends)).length =
          (pad64 (leafInput lay tree leaf honest)).length :=
        pad64_length_congr (by
          rw [leafInputW_length]; unfold leafInput
          rw [SigGolfCandidate.T3.leafInput_length, SigGolfCandidate.T3.leafInput_length, hlen])
      have hll : (pad64 (leafInput lay tree leaf honest)).length = 704 ∨
          (pad64 (leafInput lay tree leaf honest)).length = 832 := by
        rw [leafInput_padded_length lay tree leaf honest hc]; split <;> simp
      refine ⟨hl, ?_⟩
      unfold hdrKey
      rw [if_pos (by rw [hl]; exact hll), if_pos hll, hdrBlock_leafInputW, hdrBlock_leafInput]
      unfold WCT9.leafTweakW leafTweak
      rw [SigGolfCandidate.T3M.Extract.bytesLE_header_words, SigGolfCandidate.T3M.Extract.bytesLE_header_words,
        List.take_left' (bytesLE_length 8 _), List.take_left' (bytesLE_length 8 _)]
    · unfold WCT9.leafHashW WCT9.lowerHash
      rw [queried_halfHash]
      exact List.mem_singleton_self _
end halfPath
end ClaudeWCT.W9.T3M.Extract
end
-- ==== merged from ClaudeWCT_W9_T3M_Extract_Header ====
section

namespace ClaudeWCT.W9.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SigGolfCandidate.T3M.Extract (canonicalHeader_high_zero canonicalHeader_marker_ne)
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
theorem route_tree_treeBits (index : Nat) (hindex : index < 2 ^ 31) (lay : Layer) :
    (route index lay).2 < 2 ^ treeBits lay := by
  fin_cases lay <;> simp [route, treeBits, height] <;> omega
theorem routed_lt_of_treeBits {lay : Layer} {tree leaf : Nat} (ht : tree < 2 ^ treeBits lay)
    (hl : leaf < 2 ^ height lay) : tree * 2 ^ height lay + leaf < 2 ^ 31 := by
  fin_cases lay <;> simp [treeBits, height] at ht hl ⊢ <;> omega
theorem routed_treeBits_succ {lay : Layer} (h3 : lay.val < 3) {tree leaf : Nat} (ht : tree < 2 ^ treeBits lay)
    (hl : leaf < 2 ^ height lay) : tree * 2 ^ height lay + leaf < 2 ^ treeBits ⟨lay.val + 1, by omega⟩ := by
  obtain ⟨l, hlt⟩ := lay
  change l < 3 at h3
  interval_cases l <;> simp [treeBits, height] at ht hl ⊢ <;> omega
theorem tree_zero_of_treeBits {lay : Layer} {tree : Nat} (ht : tree < 2 ^ treeBits lay) : lay = 0 → tree = 0 := by
  rintro rfl; simpa [treeBits] using ht
theorem leaf_bounded_of_treeBits {lay : Layer} {tree leaf : Nat} (ht : tree < 2 ^ treeBits lay)
    (hl : leaf < 2 ^ height lay) : (Pos.leaf lay tree leaf).Bounded :=
  ⟨hl, lt_trans (routed_lt_of_treeBits ht hl) (by norm_num)⟩
/-- C4 key class of a position from its input length and header (adapted from b3cc11b's `keyClass`): leaves by
length (704/832), FTS leaf (128), forest (320); 64-byte inputs by the low word `W`: top folds `1 ≤ W < 2 ^ 16`,
marked words (WOTS and FTS chains, packed lower and FTS folds) byte0 `≥ 128`, FTS two-word folds otherwise. -/
def keyClass (len : Nat) (h : BitVec 128) : Nat :=
  if len = 832 ∨ len = 704 then 2
  else if len = 128 then 4
  else if len = 320 then 6
  else if 1 ≤ tweakLow h ∧ tweakLow h < 2 ^ 16 then 1
  else if 128 ≤ tweakMarker h then 0
  else 5
def Pos.cls : Pos → Nat
  | .chain .. => 0
  | .wctChain .. => 0
  | .node lay .. => if lay = 0 then 1 else 0
  | .leaf .. => 2
  | .wctLeaf .. => 4
  | .wctNode _ _ level _ => if level < 4 then 0 else 5
  | .forest .. => 6
theorem heap_lt {e x : Nat} (hx : x < 2 ^ e) (he : e ≤ 12) : 2 ^ e + x < 2 ^ 32 := by
  have : 2 ^ e ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) he
  have : (2 : Nat) ^ 12 = 4096 := by norm_num
  have : (2 : Nat) ^ 32 = 4294967296 := by norm_num
  omega
theorem heap_inj {e f x y : Nat} (hx : x < 2 ^ e) (hy : y < 2 ^ f) (h : 2 ^ e + x = 2 ^ f + y) : e = f ∧ x = y := by
  have key : ∀ {e f x y : Nat}, x < 2 ^ e → e < f → 2 ^ e + x < 2 ^ f + y := by
    intro e f x y hx hef
    have : 2 ^ (e + 1) ≤ 2 ^ f := Nat.pow_le_pow_right (by decide) hef
    rw [pow_succ] at this
    omega
  rcases Nat.lt_trichotomy e f with hlt | heq | hgt
  · exact absurd h (ne_of_lt (key hx hlt))
  · subst heq; exact ⟨rfl, by omega⟩
  · exact absurd h.symm (ne_of_lt (key hy hgt))
private theorem height_le12 (lay : Layer) : height lay ≤ 12 := by fin_cases lay <;> decide
theorem heap_lt64 {e x : Nat} (hx : x < 2 ^ e) (he : e ≤ 12) : 2 ^ e + x < 2 ^ 64 :=
  lt_trans (heap_lt hx he) (by norm_num)
private theorem node_heap_lt {lay : Layer} {level nd : Nat} (hnd : nd < 2 ^ (height lay - level - 1)) :
    2 ^ (height lay - level - 1) + nd < 2 ^ 64 :=
  heap_lt64 hnd (le_trans (Nat.sub_le _ _) (le_trans (Nat.sub_le _ _) (height_le12 lay)))
private theorem height_le7 {lay : Layer} (h0 : lay ≠ 0) : height lay ≤ 7 := by
  fin_cases lay <;> simp_all [height]
/-- A lower-tree heap (any node position of a tree of height `≤ 7`) is below 128. -/
theorem node_heap_lt128 {lay : Layer} {level nd : Nat} (hnd : nd < 2 ^ (height lay - level - 1))
    (h7 : height lay ≤ 7) : 2 ^ (height lay - level - 1) + nd < 128 := by
  have : 2 ^ (height lay - level - 1) ≤ 2 ^ 6 := Nat.pow_le_pow_right (by decide) (by omega)
  have h64 : (2 : Nat) ^ 6 = 64 := by norm_num
  have : nd < 64 := lt_of_lt_of_le hnd (by omega)
  omega
private theorem ftsLeafHeader_tweakHigh (index coord selected : Nat) :
    tweakHigh (WCT9.ftsLeafHeader index coord selected) = 0 := by
  unfold tweakHigh
  rw [WCT9.ftsLeafHeader_toNat]
  exact Nat.div_eq_of_lt (lt_trans (WCT9.ftsLeafLow_lt _ _ _) (by norm_num))
private theorem wctNodeHeader_tweakHigh {coord : Nat} (hk : coord < 9) (index : Nat) {heap : Nat}
    (hn : ¬ FtsNew heap) : tweakHigh (WCT9.wctNodeHeader coord index heap) = heap % 2 ^ 64 := by
  unfold tweakHigh
  rw [WCT9.wctNodeHeader_toNat hk, if_neg hn]
  have := lt_trans (WCT9.ftsLeafLow_lt index coord 0) (show 2 ^ 58 < 2 ^ 64 by norm_num)
  omega
theorem ftsNew_wctNode {level nd : Nat} (hl : level < 6) (hnd : nd < 2 ^ (7 - level - 1)) :
    FtsNew (2 ^ (7 - level - 1) + nd) ↔ level < 4 := by
  unfold FtsNew
  interval_cases level <;> simp at hnd ⊢ <;> omega
private theorem merkleTweak_layer_top {lay : Layer} (h : lay = 0) (tree heap : Nat) :
    WCT9.merkleTweak lay.val tree heap = nodeTweak 3 lay.val tree heap := by
  subst h; unfold WCT9.merkleTweak; exact if_pos rfl
theorem merkleTweak_layer_lower {lay : Layer} (h : lay ≠ 0) (tree heap : Nat) :
    WCT9.merkleTweak lay.val tree heap = WCT9.lowerTweak lay.val tree heap :=
  WCT9.merkleTweak_lower (fun e => h (Fin.ext e)) tree heap
/-- The heap of a bounded node is in `[1, 2 ^ height)`. -/
theorem node_heap_bounds {lay : Layer} {level nd : Nat} (hlev : level < height lay)
    (hnd : nd < 2 ^ (height lay - level - 1)) :
    1 ≤ 2 ^ (height lay - level - 1) + nd ∧ 2 ^ (height lay - level - 1) + nd < 2 ^ height lay := by
  have h1 : 1 ≤ 2 ^ (height lay - level - 1) := Nat.one_le_two_pow
  have h2 : 2 ^ (height lay - level - 1) * 2 ≤ 2 ^ height lay := by
    rw [← pow_succ]; exact Nat.pow_le_pow_right (by decide) (by omega)
  omega
theorem top_heap_bounds {level nd : Nat} (hlev : level < height (0 : Layer))
    (hnd : nd < 2 ^ (height (0 : Layer) - level - 1)) :
    1 ≤ 2 ^ (height (0 : Layer) - level - 1) + nd ∧ 2 ^ (height (0 : Layer) - level - 1) + nd < 4096 := by
  have := node_heap_bounds hlev hnd
  exact ⟨this.1, by simpa [height] using this.2⟩
theorem Pos.keyClass_eq {p : Pos} (hb : p.Bounded) : keyClass p.len p.hdr = p.cls := by
  cases p with
  | chain lay tree lf i step =>
      have hL : 193 * 2 ^ 56 ≤ tweakLow (chainHeader lay tree lf i step) := by
        rw [tweakLow_eq_low, chainHeader_low, chainHeaderFlaggedLow_toNat]
        have := chainHeaderLow_band lay tree lf i step
        omega
      have hm := chainHeader_firstByte lay tree lf i step
      simp only [keyClass, Pos.len, Pos.hdr, Pos.cls, tweakMarker]
      split_ifs <;> omega
  | wctChain index coord child t step =>
      obtain ⟨-, hk, -, -, -⟩ := hb
      have hm := WCT9.ftsChainHeaderP_firstByte index coord child t step 0
      have hL : 2 ^ 16 ≤ tweakLow (WCT9.ftsChainHeader index coord child t step) := by
        unfold WCT9.ftsChainHeader
        rw [tweakLow_eq_low, WCT9.ftsChainHeaderP_low, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (lt_trans (WCT9.ftsChainLow_lt _ _ _ _ _) (by norm_num))]
        exact WCT9.ftsChainLow_ge (by omega) _ _ _ _
      simp only [keyClass, Pos.len, Pos.hdr, Pos.cls, WCT9.ftsChainHeader, tweakMarker] at hm hL ⊢
      split_ifs <;> omega
  | leaf lay tree lf =>
      simp only [keyClass, Pos.len, Pos.cls]
      split_ifs <;> simp_all
  | node lay tree level nd =>
      obtain ⟨-, hlev, -, -, hnd⟩ := hb
      by_cases h0 : lay = 0
      · subst h0
        have hl : tweakLow (WCT9.merkleTweak 0 tree (2 ^ (height (0 : Layer) - level - 1) + nd)) =
            topNodeWord (2 ^ (height (0 : Layer) - level - 1) + nd) := by
          rw [tweakLow_eq_low, WCT9.merkleTweak_top_low, topNodeWord_toNat64]
        have h1 := topNodeWord_pos (2 ^ (height (0 : Layer) - level - 1) + nd)
        have h2 := topNodeWord_lt (2 ^ (height (0 : Layer) - level - 1) + nd)
        show keyClass 64 (WCT9.merkleTweak 0 tree (2 ^ (height (0 : Layer) - level - 1) + nd)) = 1
        unfold keyClass
        rw [hl, if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos ⟨h1, by omega⟩]
      · have hh := node_heap_lt128 hnd (height_le7 h0)
        have hm := WCT9.lowerTweak_marker hh lay.val tree
        have hL := WCT9.lowerTweak_low_ge hh lay.val tree
        show keyClass 64 (WCT9.merkleTweak lay.val tree (2 ^ (height lay - level - 1) + nd)) = (if lay = 0 then 1 else 0)
        rw [if_neg h0, merkleTweak_layer_lower h0]
        unfold keyClass
        rw [if_neg (by decide), if_neg (by decide), if_neg (by decide)]
        unfold tweakLow
        rw [if_neg (by omega), if_pos (by omega)]
  | wctLeaf index coord child =>
      simp [keyClass, Pos.len, Pos.cls]
  | wctNode index coord level nd =>
      obtain ⟨-, hk, hlev, hnd⟩ := hb
      have hiff := ftsNew_wctNode hlev hnd
      have hlow := WCT9.wctNodeHeader_toNat hk index (2 ^ (7 - level - 1) + nd)
      have hm := WCT9.wctNodeHeader_tweakMarker coord index (2 ^ (7 - level - 1) + nd)
      have hge := WCT9.ftsLeafLow_ge (show coord < 15 by omega) index 0
      have hlt := WCT9.ftsLeafLow_lt index coord 0
      have hgeN : 2 ^ 16 ≤ WCT9.ftsNodeLowN index coord (2 ^ (7 - level - 1) + nd) := by
        rw [WCT9.ftsNodeLowN_eq, Nat.mod_eq_of_lt (show coord + 1 < 16 by omega)]; omega
      have hltN := WCT9.ftsNodeLowN_lt index coord (2 ^ (7 - level - 1) + nd)
      simp only [keyClass, Pos.len, Pos.hdr, Pos.cls]
      unfold tweakLow
      by_cases hl4 : level < 4
      · have hn := hiff.mpr hl4
        rw [if_pos hn] at hlow
        rw [if_pos ⟨hk, hn⟩] at hm
        obtain ⟨h8, h128⟩ := hn
        simp only [if_pos hl4]
        split_ifs <;> omega
      · have hn : ¬ FtsNew (2 ^ (7 - level - 1) + nd) := fun h => hl4 (hiff.mp h)
        rw [if_neg hn] at hlow
        rw [if_neg (fun h => hn h.2)] at hm
        simp only [if_neg hl4]
        split_ifs <;> omega
  | forest index =>
      simp [keyClass, Pos.len, Pos.cls]
/-- The class of a key depends on its header only through the low word. -/
theorem keyClass_of_low_eq (len : Nat) {h h' : BitVec 128} (he : h.extractLsb' 0 64 = h'.extractLsb' 0 64) :
    keyClass len h = keyClass len h' := by
  have hv := congrArg BitVec.toNat he
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero] at hv
  have hl : tweakLow h = tweakLow h' := hv
  have hm : tweakMarker h = tweakMarker h' := by
    unfold tweakMarker
    rw [← Nat.mod_mod_of_dvd h.toNat (show 256 ∣ 2 ^ 64 by norm_num),
      ← Nat.mod_mod_of_dvd h'.toNat (show 256 ∣ 2 ^ 64 by norm_num)]
    exact congrArg (· % 256) hv
  unfold keyClass
  rw [hl, hm]
private theorem node_level_inj {lay : Layer} {level nd level' nd' : Nat} (hlev : level < height lay)
    (hlev' : level' < height lay) (hnd : nd < 2 ^ (height lay - level - 1))
    (hnd' : nd' < 2 ^ (height lay - level' - 1))
    (h : 2 ^ (height lay - level - 1) + nd = 2 ^ (height lay - level' - 1) + nd') : level = level' ∧ nd = nd' := by
  obtain ⟨e, x⟩ := heap_inj hnd hnd' h
  exact ⟨by omega, x⟩
/-- C4: bounded positions are determined by their key (length and header); the length separates the forest header
`header 15 0 index 0 0` (low word 3841 for `index < 2 ^ 32`) from the top label of heap 3841. -/
theorem Pos.hdr_injective {p p' : Pos} (hb : p.Bounded) (hb' : p'.Bounded) (hlen : p.len = p'.len)
    (h : p.hdr = p'.hdr) : p = p' := by
  have hc : p.cls = p'.cls := by rw [← Pos.keyClass_eq hb, ← Pos.keyClass_eq hb', hlen, h]
  cases p
  case chain lay tree lf i step =>
    obtain ⟨ht, hf, hi, hs⟩ := hb
    cases p'
    case chain lay' tree' lf' i' step' =>
      obtain ⟨ht', hf', hi', hs'⟩ := hb'
      obtain ⟨hl, ht, hf, hi, hs⟩ := chainHeader_low_injective ht hf hi (by omega) ht' hf' hi' (by omega)
        (congrArg (BitVec.extractLsb' 0 64) h)
      subst_vars; rfl
    case wctChain index coord child t step' =>
      exact False.elim (WCT9.ftsChainHeaderP_low_ne_chainHeader _ _ _ _ _ _ _ _ _ _ _
        (congrArg (BitVec.extractLsb' 0 64) h.symm))
    case wctNode index coord level nd =>
      exact False.elim (WCT9.wctNodeHeader_ne_chainHeader _ _ _ _ _ _ _ _ h.symm)
    case node lay' tree' level' nd' =>
      obtain ⟨-, -, -, -, hnd'⟩ := hb'
      by_cases hz' : lay' = 0
      · simp [Pos.cls, hz'] at hc
      · simp only [Pos.hdr] at h
        rw [merkleTweak_layer_lower hz'] at h
        exact False.elim (WCT9.lowerTweak_ne_chainHeader (node_heap_lt128 hnd' (height_le7 hz')) _ _ _ _ _ _ _
          (by omega) h.symm)
    all_goals (simp only [Pos.cls] at hc; (try split_ifs at hc) <;> omega)
  case wctChain index coord child t step =>
    obtain ⟨hi, hc9, hj, ht, hs⟩ := hb
    cases p'
    case chain lay tree lf i step' =>
      exact False.elim (WCT9.ftsChainHeaderP_low_ne_chainHeader _ _ _ _ _ _ _ _ _ _ _
        (congrArg (BitVec.extractLsb' 0 64) h))
    case wctChain index' coord' child' t' step' =>
      obtain ⟨hi', hc9', hj', ht', hs'⟩ := hb'
      obtain ⟨e1, e2, e3, e4, e5, -⟩ := WCT9.ftsChainHeaderP_injective hi (by omega) hj (by omega)
        (by omega) hi' (by omega) hj' (by omega) (by omega) h
      subst_vars; rfl
    case wctNode index' coord' level' nd' =>
      exact False.elim (WCT9.wctNodeHeader_ne_ftsChainHeaderP _ _ _ _ _ _ _ _ 0 h.symm)
    case node lay' tree' level' nd' =>
      obtain ⟨-, -, -, -, hnd'⟩ := hb'
      by_cases hz' : lay' = 0
      · simp [Pos.cls, hz'] at hc
      · simp only [Pos.hdr] at h
        rw [merkleTweak_layer_lower hz'] at h
        exact False.elim (WCT9.lowerTweak_ne_ftsChainHeaderP (node_heap_lt128 hnd' (height_le7 hz')) _ _ _ _ _ _ _
          0 h.symm)
    all_goals (simp only [Pos.cls] at hc; (try split_ifs at hc) <;> omega)
  case leaf lay tree lf =>
    cases p'
    case leaf lay' tree' lf' =>
      obtain ⟨hl, hr⟩ := hb
      obtain ⟨hl', hr'⟩ := hb'
      obtain ⟨rfl, rfl, rfl⟩ := leafTweak_injective hl hr hl' hr' h
      rfl
    all_goals (simp only [Pos.cls] at hc; (try split_ifs at hc) <;> omega)
  case node lay tree level nd =>
    obtain ⟨ht, hlev, -, h0, hnd⟩ := hb
    cases p'
    case node lay' tree' level' nd' =>
      obtain ⟨ht', hlev', -, h0', hnd'⟩ := hb'
      simp only [Pos.hdr] at h
      by_cases hz : lay = 0
      · by_cases hz' : lay' = 0
        · have h0v : lay.val = 0 → tree = 0 := fun e => h0 (Fin.ext e)
          have h0v' : lay'.val = 0 → tree' = 0 := fun e => h0' (Fin.ext e)
          rw [merkleTweak_layer_top hz, merkleTweak_layer_top hz'] at h
          have hb1 : 1 ≤ 2 ^ (height lay - level - 1) + nd ∧ 2 ^ (height lay - level - 1) + nd < 4096 := by
            subst hz; exact top_heap_bounds hlev hnd
          have hb2 : 1 ≤ 2 ^ (height lay' - level' - 1) + nd' ∧ 2 ^ (height lay' - level' - 1) + nd' < 4096 := by
            subst hz'; exact top_heap_bounds hlev' hnd'
          obtain ⟨hl, htr, hh⟩ := nodeTweak_hyper_injective lay.isLt lay'.isLt ht ht' h0v h0v'
            (node_heap_lt hnd) (node_heap_lt hnd') (fun _ => hb1) (fun _ => hb2) h
          have hlay : lay = lay' := Fin.ext hl
          subst hlay htr
          obtain ⟨rfl, rfl⟩ := node_level_inj hlev hlev' hnd hnd' hh
          rfl
        · simp [Pos.cls, hz, hz'] at hc
      · by_cases hz' : lay' = 0
        · simp [Pos.cls, hz, hz'] at hc
        · rw [merkleTweak_layer_lower hz, merkleTweak_layer_lower hz'] at h
          obtain ⟨hl, htr, hh⟩ := WCT9.lowerTweak_injective (Nat.pos_of_ne_zero (fun e => hz (Fin.ext e)))
            lay.isLt (Nat.pos_of_ne_zero (fun e => hz' (Fin.ext e))) lay'.isLt ht ht'
            (node_heap_lt128 hnd (height_le7 hz)) (node_heap_lt128 hnd' (height_le7 hz')) h
          have hlay : lay = lay' := Fin.ext hl
          subst hlay htr
          obtain ⟨rfl, rfl⟩ := node_level_inj hlev hlev' hnd hnd' hh
          rfl
    case chain lay' tree' lf' i' step' =>
      obtain ⟨-, -, -, hs'⟩ := hb'
      by_cases hz : lay = 0
      · simp [Pos.cls, hz] at hc
      · simp only [Pos.hdr] at h
        rw [merkleTweak_layer_lower hz] at h
        exact False.elim (WCT9.lowerTweak_ne_chainHeader (node_heap_lt128 hnd (height_le7 hz)) _ _ _ _ _ _ _
          (by omega) h)
    case wctChain index' coord' child' t' step' =>
      by_cases hz : lay = 0
      · simp [Pos.cls, hz] at hc
      · simp only [Pos.hdr] at h
        rw [merkleTweak_layer_lower hz] at h
        exact False.elim (WCT9.lowerTweak_ne_ftsChainHeaderP (node_heap_lt128 hnd (height_le7 hz)) _ _ _ _ _ _ _
          0 h)
    case wctNode index' coord' level' nd' =>
      obtain ⟨-, hc9', -, -⟩ := hb'
      by_cases hz : lay = 0
      · simp only [Pos.cls, if_pos hz] at hc; split_ifs at hc <;> omega
      · simp only [Pos.hdr] at h
        rw [merkleTweak_layer_lower hz] at h
        exact False.elim (WCT9.lowerTweak_ne_wctNodeHeader (node_heap_lt128 hnd (height_le7 hz)) _ _ hc9' _ _ h)
    all_goals (simp only [Pos.cls] at hc; (try split_ifs at hc) <;> omega)
  case forest index =>
    cases p'
    case forest index' =>
      have hb1 : index < 2 ^ 40 := hb
      have hb2 : index' < 2 ^ 40 := hb'
      obtain ⟨-, -, hi, -, -⟩ := header_injective (by decide) (by decide) hb1 (by decide) (by decide)
        (by decide) (by decide) hb2 (by decide) (by decide) h
      rw [hi]
    all_goals (simp only [Pos.cls] at hc; (try split_ifs at hc) <;> omega)
  case wctLeaf index coord child =>
    cases p'
    case wctLeaf index' coord' child' =>
      obtain ⟨hi, hc9, hj⟩ := hb
      obtain ⟨hi', hc9', hj'⟩ := hb'
      obtain ⟨rfl, rfl, rfl⟩ := WCT9.ftsLeafHeader_injective hi (by omega) hj hi' (by omega) hj' h
      rfl
    all_goals (simp only [Pos.cls] at hc; (try split_ifs at hc) <;> omega)
  case wctNode index coord level nd =>
    cases p'
    case wctNode index' coord' level' nd' =>
      obtain ⟨hi, hc9, hlev, hnd⟩ := hb
      obtain ⟨hi', hc9', hlev', hnd'⟩ := hb'
      obtain ⟨rfl, rfl, hh⟩ := WCT9.wctNodeHeader_injective hc9 hi
        (heap_lt64 hnd (show 7 - level - 1 ≤ 12 by omega)) hc9' hi'
        (heap_lt64 hnd' (show 7 - level' - 1 ≤ 12 by omega)) h
      obtain ⟨e, x⟩ := heap_inj hnd hnd' hh
      have : level = level' := by omega
      subst this x
      rfl
    case chain lay tree lf i step =>
      exact False.elim (WCT9.wctNodeHeader_ne_chainHeader _ _ _ _ _ _ _ _ h)
    case wctChain index' coord' child t step =>
      exact False.elim (WCT9.wctNodeHeader_ne_ftsChainHeaderP _ _ _ _ _ _ _ _ 0 h)
    case node lay' tree' level' nd' =>
      obtain ⟨-, hc9, -, -⟩ := hb
      obtain ⟨-, -, -, -, hnd'⟩ := hb'
      by_cases hz' : lay' = 0
      · simp only [Pos.cls, if_pos hz'] at hc; split_ifs at hc <;> omega
      · simp only [Pos.hdr] at h
        rw [merkleTweak_layer_lower hz'] at h
        exact False.elim (WCT9.lowerTweak_ne_wctNodeHeader (node_heap_lt128 hnd' (height_le7 hz')) _ _ hc9 _ _ h.symm)
    all_goals (simp only [Pos.cls] at hc; (try split_ifs at hc) <;> omega)
/-- The encoding row tweak (honest high word 1) is no position header. C4: by marker, tag or high word. -/
theorem rowTweak_ne_hdr (lay : Layer) (tree leaf : Nat) {p : Pos} (hb : p.Bounded) : rowTweak lay tree leaf ≠ p.hdr := by
  intro h
  have hH : tweakHigh p.hdr = 1 := by rw [← h, rowTweak_high]
  have hM : tweakMarker p.hdr = 1 := by rw [← h, rowTweak_marker]
  have hT : tweakTag p.hdr = 2 := by rw [← h, rowTweak_tag]
  cases p with
  | chain lay' tree' lf i step =>
      have := chainHeader_firstByte lay' tree' lf i step
      simp only [Pos.hdr, tweakMarker] at hM; omega
  | wctChain index coord child t step =>
      have := WCT9.ftsChainHeaderP_firstByte index coord child t step 0
      simp only [Pos.hdr, WCT9.ftsChainHeader, tweakMarker] at hM; omega
  | leaf lay' tree' lf => simp only [Pos.hdr] at hH; rw [leafTweak_high] at hH; omega
  | node lay' tree' level nd =>
      simp only [Pos.hdr] at hH
      have hz : (WCT9.merkleTweak lay'.val tree' (2 ^ (height lay' - level - 1) + nd)).extractLsb' 64 64 = 0 := by
        by_cases h0 : lay' = 0
        · subst h0; exact WCT9.merkleTweak_top_high _ _
        · rw [merkleTweak_layer_lower h0]; exact WCT9.lowerTweak_high _ _ _
      have hx := (BitVec.extractLsb'_append_extractLsb' (w := 64) (len := 64)
        (x := WCT9.merkleTweak lay'.val tree' (2 ^ (height lay' - level - 1) + nd))).symm
      rw [hx, append64_high, hz] at hH
      simp at hH
  | wctLeaf index coord child =>
      simp only [Pos.hdr, tweakHigh] at hH
      rw [WCT9.ftsLeafHeader_toNat] at hH
      have := WCT9.ftsLeafLow_lt index coord child
      rw [Nat.div_eq_of_lt (lt_trans this (by norm_num))] at hH; omega
  | wctNode index coord level nd =>
      obtain ⟨-, hk, -, -⟩ := hb
      have := WCT9.wctNodeHeader_tweakTag hk index (2 ^ (7 - level - 1) + nd)
      simp only [Pos.hdr] at hT
      rw [this] at hT; split_ifs at hT <;> omega
  | forest index => simp only [Pos.hdr] at hT; rw [header_tag] at hT; omega
theorem Pos.hdr_firstByte_chain (lay : Layer) (tree leaf i step : Nat) :
    128 ≤ (Pos.chain lay tree leaf i step).hdr.toNat % 256 :=
  chainHeader_firstByte lay tree leaf i step
theorem Pos.hdr_firstByte_wctChain (index coord child t step : Nat) :
    (Pos.wctChain index coord child t step).hdr.toNat % 256 = 128 + 4 * (t % 8) :=
  WCT9.ftsChainHeaderP_firstByte index coord child t step 0
/-- C4: the marker byte of a position of class neither 0 (marked) nor 1 (top fold, whose marker byte is the heap's
low byte) is below 128. -/
theorem Pos.hdr_marker_lt {p : Pos} (hb : p.Bounded) (hn : p.cls ≠ 0) (h1 : p.cls ≠ 1) : p.hdr.toNat % 256 < 128 := by
  cases p with
  | chain => simp [Pos.cls] at hn
  | wctChain => simp [Pos.cls] at hn
  | leaf lay tree lf =>
      have := leafTweak_marker lay tree lf; unfold tweakMarker at this; simp only [Pos.hdr]; omega
  | node lay tree level nd => simp only [Pos.cls] at hn h1; split_ifs at hn h1 <;> omega
  | wctLeaf index coord child => simp only [Pos.hdr]; rw [WCT9.ftsLeafHeader_firstByte]; decide
  | wctNode index coord level nd =>
      obtain ⟨-, hk, hlev, hnd⟩ := hb
      have hl4 : ¬ level < 4 := by intro h; simp [Pos.cls, h] at hn
      have hn' : ¬ FtsNew (2 ^ (7 - level - 1) + nd) := fun h => hl4 ((ftsNew_wctNode hlev hnd).mp h)
      simp only [Pos.hdr]; rw [WCT9.wctNodeHeader_firstByte_lt _ _ _ hn']; decide
  | forest index =>
      have := header_marker 15 0 index 0 0; unfold tweakMarker at this; simp only [Pos.hdr]; omega
/-- C4: a position of class 1 is a top fold; its header's high word is 0. -/
theorem Pos.hdr_high_of_cls1 {p : Pos} (hc : p.cls = 1) : p.hdr.extractLsb' 64 64 = 0 := by
  cases p with
  | node lay tree level nd =>
      simp only [Pos.cls] at hc
      by_cases hz : lay = 0
      · subst hz; exact WCT9.merkleTweak_top_high _ _
      · simp [hz] at hc
  | wctNode _ _ level _ => simp only [Pos.cls] at hc; split_ifs at hc <;> omega
  | _ => simp [Pos.cls] at hc
theorem Pos.canonicalHeader_eq {p : Pos} (hb : p.Bounded) :
    canonicalHeader (bytesLE 16 p.hdr) = bytesLE 16 p.hdr := by
  cases p with
  | chain lay tree leaf i step =>
      exact canonicalHeader_high_zero _
        (SigGolfCandidate.T3M.chainHeader_high_zero lay tree leaf i step hb.1 hb.2.1 hb.2.2.1 (by have := hb.2.2.2; omega))
  | wctChain index coord child t step =>
      exact canonicalHeader_high_zero _ (WCT9.ftsChainHeaderP_high index coord child t step 0)
  | leaf => exact canonicalHeader_marker_ne _ (Pos.hdr_marker_lt hb (by simp [Pos.cls]) (by simp [Pos.cls]))
  | node lay tree level nd =>
      apply canonicalHeader_high_zero
      simp only [Pos.hdr]
      by_cases hz : lay = 0
      · subst hz; exact WCT9.merkleTweak_top_high _ _
      · rw [merkleTweak_layer_lower hz]
        exact WCT9.lowerTweak_high _ _ _
  | forest => exact canonicalHeader_marker_ne _ (Pos.hdr_marker_lt hb (by simp [Pos.cls]) (by simp [Pos.cls]))
  | wctLeaf => exact canonicalHeader_marker_ne _ (Pos.hdr_marker_lt hb (by simp [Pos.cls]) (by simp [Pos.cls]))
  | wctNode index coord level nd =>
      by_cases hl4 : level < 4
      · apply canonicalHeader_high_zero
        obtain ⟨-, hk, hlev, hnd⟩ := hb
        simp only [Pos.hdr]
        rw [WCT9.wctNodeHeader_high hk, if_pos ((ftsNew_wctNode hlev hnd).mpr hl4)]
        rfl
      · exact canonicalHeader_marker_ne _ (Pos.hdr_marker_lt hb (by simp [Pos.cls, hl4]) (by simp [Pos.cls, hl4]))
/-! ### Length-aware position decoding (C3 FULL, S2-2)
The leaf tweak's high word and the encoding row tweak's high word are witness pads. An encoding with high word 0 has
the 16-byte header of a leaf tweak, so a position is decoded from the input length (`Pos.len`) and the decoding key
`hdrKey` (leaf-length inputs: the low tweak word only; every other input: its canonical header). -/
@[simp] theorem Pos.len_leaf (lay : Layer) (tree leaf : Nat) :
    (Pos.leaf lay tree leaf).len = if lay = 0 then 832 else 704 := rfl
theorem Pos.len_leafLen {p : Pos} : (p.len = 704 ∨ p.len = 832) ↔ ∃ lay tree leaf, p = .leaf lay tree leaf := by
  constructor
  · intro h
    cases p with
    | leaf lay tree leaf => exact ⟨lay, tree, leaf, rfl⟩
    | _ => simp [Pos.len] at h
  · rintro ⟨lay, tree, leaf, rfl⟩
    simp only [Pos.len_leaf]; split <;> simp
theorem Pos.len_of_ne_leaf {p : Pos} (h : ∀ lay tree leaf, p ≠ .leaf lay tree leaf) : ¬ (p.len = 704 ∨ p.len = 832) :=
  fun hl => by obtain ⟨lay, tree, leaf, e⟩ := Pos.len_leafLen.mp hl; exact h lay tree leaf e
theorem hdrKey_of_leafLen {x : HashInput} (h : x.length = 704 ∨ x.length = 832) :
    hdrKey x = (hdrBlock x).take 8 ++ List.replicate 8 0 := by
  unfold hdrKey; rw [if_pos h]
theorem hdrKey_of_not_leafLen {x : HashInput} (h : ¬ (x.length = 704 ∨ x.length = 832))
    (ht : ¬ (x.length = 64 ∧ TopLow (hdrBlock x))) :
    hdrKey x = canonicalHeader (hdrBlock x) := by
  unfold hdrKey; rw [if_neg h, if_neg ht]
/-- The low-word key of a header block whose high word is zero is the block itself. -/
theorem bytesLE_high_zero_key (hi lo : BitVec 64) (hz : hi = 0) :
    (bytesLE 16 (hi ++ lo)).take 8 ++ List.replicate 8 0 = bytesLE 16 (hi ++ lo) := by
  subst hz
  rw [SigGolfCandidate.T3M.Extract.bytesLE_header_words, List.take_left' (bytesLE_length 8 lo)]
  congr 1
/-- The low-word key of a header whose high word is zero is the header itself. -/
theorem bytesLE_high_zero_key' (hdr : BitVec 128) (hz : hdr.extractLsb' 64 64 = 0) :
    (bytesLE 16 hdr).take 8 ++ List.replicate 8 0 = bytesLE 16 hdr := by
  have he : hdr = hdr.extractLsb' 64 64 ++ hdr.extractLsb' 0 64 :=
    (BitVec.extractLsb'_append_extractLsb' (w := 64) (len := 64) (x := hdr)).symm
  rw [he]
  exact bytesLE_high_zero_key _ _ hz
theorem leafKey_hdr (lay : Layer) (tree leaf : Nat) :
    (bytesLE 16 (Pos.leaf lay tree leaf).hdr).take 8 ++ List.replicate 8 0 = bytesLE 16 (Pos.leaf lay tree leaf).hdr :=
  bytesLE_high_zero_key _ _ rfl
/-- For a bounded position, the key of an input whose header block is the position's header is that header. -/
theorem hdrKey_of_hdrBlock {x : HashInput} {p : Pos} (hb : p.Bounded) (hlen : x.length = p.len)
    (h : hdrBlock x = bytesLE 16 p.hdr) : hdrKey x = bytesLE 16 p.hdr := by
  by_cases hl : x.length = 704 ∨ x.length = 832
  · rw [hdrKey_of_leafLen hl, h]
    rw [hlen] at hl
    obtain ⟨lay, tree, leaf, rfl⟩ := Pos.len_leafLen.mp hl
    exact leafKey_hdr lay tree leaf
  · by_cases ht : x.length = 64 ∧ TopLow (hdrBlock x)
    · rw [hdrKey_of_top ht.1 ht.2, h]
      have hT := ht.2
      rw [h, topLow_bytesLE_iff] at hT
      have hk := Pos.keyClass_eq hb
      rw [← hlen, ht.1] at hk
      unfold keyClass at hk
      rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos hT] at hk
      exact bytesLE_high_zero_key' _ (Pos.hdr_high_of_cls1 hk.symm)
    · rw [hdrKey_of_not_leafLen hl ht, h, Pos.canonicalHeader_eq hb]
theorem hdrKey_honestInput (answers : Answers) {p : Pos} (hb : p.Bounded) :
    hdrKey (honestInput answers p) = bytesLE 16 p.hdr :=
  hdrKey_of_hdrBlock hb (honestInput_length answers p) (hdrBlock_honestInput answers p)
noncomputable def posOf (input : HashInput) : Option Pos := by
  classical
  exact if h : ∃ p : Pos, p.Bounded ∧ input.length = p.len ∧ hdrKey input = bytesLE 16 p.hdr
    then some (Classical.choose h) else none
theorem posOf_key_eq {input : HashInput} {p : Pos} (hb : p.Bounded) (hlen : input.length = p.len)
    (h : hdrKey input = bytesLE 16 p.hdr) :
    posOf input = some p := by
  classical
  have hex : ∃ p : Pos, p.Bounded ∧ input.length = p.len ∧ hdrKey input = bytesLE 16 p.hdr := ⟨p, hb, hlen, h⟩
  unfold posOf
  rw [dif_pos hex]
  have hs := Classical.choose_spec hex
  exact congrArg some (Pos.hdr_injective hs.1 hb (hs.2.1.symm.trans hlen) (bytesLE_injective (hs.2.2.symm.trans h)))
theorem posOf_eq {input : HashInput} {p : Pos} (hb : p.Bounded) (hlen : input.length = p.len)
    (h : hdrBlock input = bytesLE 16 p.hdr) : posOf input = some p :=
  posOf_key_eq hb hlen (hdrKey_of_hdrBlock hb hlen h)
theorem posOf_eq_none {input : HashInput}
    (h : ∀ p : Pos, p.Bounded → input.length = p.len → hdrKey input ≠ bytesLE 16 p.hdr) : posOf input = none := by
  classical
  unfold posOf
  rw [dif_neg]
  rintro ⟨p, hb, hlen, hk⟩
  exact h p hb hlen hk
theorem posOf_spec {input : HashInput} {p : Pos} (h : posOf input = some p) :
    p.Bounded ∧ input.length = p.len ∧ hdrKey input = bytesLE 16 p.hdr := by
  classical
  unfold posOf at h
  split at h
  · rename_i hex
    cases h
    exact Classical.choose_spec hex
  · cases h
theorem hitIn_posOf {answers : Answers} {qs : List Spec.Domain} (h : HitIn answers qs) :
    ∃ pos actual, pos.Bounded ∧ .inl (.inr actual) ∈ qs ∧ posOf actual = some pos ∧
      HashHitAt answers pos (honestInput answers pos) actual := by
  obtain ⟨pos, actual, hb, hq, hh, hs⟩ := h
  refine ⟨pos, actual, hb, hq, posOf_key_eq hb ?_ ?_, hh⟩
  · rw [hs.1, honestInput_length]
  · rw [hs.2, hdrKey_honestInput answers hb]
theorem low_tweakMarker (x : BitVec 128) : (x.extractLsb' 0 64).toNat % 256 = tweakMarker x := by
  unfold tweakMarker
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  exact Nat.mod_mod_of_dvd _ (by norm_num)
theorem low_tweakTag (x : BitVec 128) : (x.extractLsb' 0 64).toNat / 256 % 256 = tweakTag x := by
  unfold tweakTag
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, show (2 : Nat) ^ 64 = 256 * 2 ^ 56 by norm_num,
    Nat.mod_mul_right_div_self]
  exact Nat.mod_mod_of_dvd _ (by norm_num)
/-- C3 (FULL): the encoding's low row-tweak word differs from the low header word of every 64-byte position. -/
theorem rowTweak_low_ne_hdr (lay : Layer) (tree leaf : Nat) {p : Pos} (hb : p.Bounded) (h64 : p.len = 64) :
    (rowTweak lay tree leaf).extractLsb' 0 64 ≠ p.hdr.extractLsb' 0 64 := by
  intro h
  have hL : tweakLow p.hdr = (hyperWord lay.val (tree * 2 ^ height lay + leaf)).toNat := by
    rw [tweakLow_eq_low, ← h, rowTweak, append64_low]
  have hy := hyperWord_toNat lay.val (tree * 2 ^ height lay + leaf)
  have hm : tweakMarker p.hdr = 1 := by rw [← low_tweakMarker, ← h, low_tweakMarker, rowTweak_marker]
  have hk := Pos.keyClass_eq hb
  rw [h64] at hk
  unfold keyClass at hk
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by rw [hL, hy]; omega),
    if_neg (by rw [hm]; omega)] at hk
  cases p with
  | wctNode index coord level nd =>
      obtain ⟨-, hk9, -, -⟩ := hb
      have hw := WCT9.wctNodeHeader_toNat hk9 index (2 ^ (7 - level - 1) + nd)
      have := WCT9.ftsLeafLow_lt index coord 0
      have := WCT9.ftsNodeLowN_lt index coord (2 ^ (7 - level - 1) + nd)
      simp only [Pos.hdr] at hL
      unfold tweakLow at hL
      rw [hw] at hL
      split_ifs at hL <;> omega
  | node lay' => simp only [Pos.cls] at hk; split_ifs at hk <;> omega
  | _ => simp [Pos.cls] at hk
end ClaudeWCT.W9.T3M.Extract
end
-- ==== merged from ClaudeWCT_W9_T3M_Extract_Defs ====
section

namespace ClaudeWCT.W9.T3M.WctExtract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers treeValue)
def HonestQ (answers : Answers) (N : HashOutput) (c : WCT9.Coord) (q : Spec.Domain) : Prop :=
  (∃ t : Fin 6, ∃ s, 4 - WCT9.wordDigit (WCT9.rank N c) t ≤ s ∧ s < 4 ∧
      q = .inl (.inr (Extract.honestInput answers
        (.wctChain (WCT9.digestIndex N) c.val (WCT9.child N c).val t.val s)))) ∨
    q = .inl (.inr (Extract.honestInput answers (.wctLeaf (WCT9.digestIndex N) c.val (WCT9.child N c).val))) ∨
    ∃ l, l < 6 ∧ q = .inl (.inr (Extract.honestInput answers
      (.wctNode (WCT9.digestIndex N) c.val l ((WCT9.child N c).val / 2 ^ (l + 1)))))
/-- Honest coordinate (nested FTS r1-1): revealed values, chain pads, the Merkle siblings (including the supplied
top sibling) and the pads of the five low fold levels are honest. The leaf pad and the top fold's pad are not
witness data for coordinates 1..8: they are the previous coordinate's top pair (`WctHonest` pins coordinate 0's). -/
def CoordHonest (answers : Answers) (N : HashOutput) (w : WBytes) (c : WCT9.Coord) : Prop :=
  (∀ t : Fin 6, wreveal w c.val t.val (WCT9.wordDigit (WCT9.rank N c) t) =
      Extract.wctValue answers (WCT9.digestIndex N) c.val (WCT9.child N c).val t.val
        (4 - WCT9.wordDigit (WCT9.rank N c) t) ∧
    (0 < WCT9.wordDigit (WCT9.rank N c) t →
      wcpads w c.val t.val = (0, 0) ∧ wcHeaderPad w c.val t.val = 0)) ∧
  (∀ l, l < 7 → wsib w c.val (WCT9.child N c).val l =
      treeValue (Extract.ftsLevels answers (WCT9.digestIndex N) c.val) l ((WCT9.child N c).val / 2 ^ l ^^^ 1) ∧
    (l < 5 → wmpad w c.val (WCT9.child N c).val l = 0))
def WctHonest (answers : Answers) (N : HashOutput) (w : WBytes) : Prop :=
  (∀ q ∈ queried answers (recoverFtsP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) N),
      ∃ c : WCT9.Coord, HonestQ answers N c q) ∧
    (∀ c : WCT9.Coord, CoordHonest answers N w c) ∧ wctStart w = (0, 0)
end ClaudeWCT.W9.T3M.WctExtract
namespace ClaudeWCT.W9.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3M
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers treeValue)
open ClaudeWCT.WCT9 (wotsTree wotsValue)
def msgFits (lay : Layer) : WCT9.LayerMsg → Prop
  | .forest _ => False
  | .pair _ _ => True
def LayerShaped (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) : Prop :=
  (∀ j, j < height lay →
    wpath w lay (route index lay).1 j =
        treeValue (wotsTree answers lay (route index lay).2) j ((route index lay).1 / 2 ^ j ^^^ 1) ∧
      (j + 1 < height lay ∨ lay.val = 0 → wmerklePad w lay (route index lay).1 j =
        WCT9.nonceDigest (WCT9.honestNonce answers lay (route index lay).2 j ((route index lay).1 / 2 ^ (j + 1)))) ∧
      (j + 1 < height lay ∨ lay.val = 0 → wmerkleHigh w lay (route index lay).1 j = 0)) ∧
  (∀ i, i < chainCount lay →
    wvalueFor w lay digits i = wotsValue answers lay (route index lay).2 (route index lay).1 digits i ∧
      (digits.getD i 0 < maxDigit lay i →
        wchainPads w lay i = (0, 0) ∧ wchainHeaderPad w lay i = 0)) ∧
  wleafHigh w lay = 0
def Frame (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (msg : WCT9.LayerMsg) (digits : List Nat) :
    Prop :=
  (wbcCtr w index lay).toNat < WCT9.verifyWindow ∧
    decode lay (evalWithAnswerFn answers (ClaudeWCT.WCT9.encodingHash lay (layerEncodingInputP lay (route index lay).2 (route index lay).1
      msg (wbcCtr w index lay) (wbcPad w index lay) (wbcRight w) (wbcHigh w index lay)))) = some digits
def encodingQuery (w : WBytes) (index : Nat) (lay : Layer) (msg : WCT9.LayerMsg) : Spec.Domain :=
  .inl (.inr (pad64 (layerEncodingInputP lay (route index lay).2 (route index lay).1 msg (wbcCtr w index lay)
    (wbcPad w index lay) (wbcRight w) (wbcHigh w index lay))))
def Good (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) : Prop :=
  ∃ digits, Frame answers w index lay (honestMsg answers index lay) digits ∧ LayerShaped answers w index lay digits
def Diverge (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (qs : List Spec.Domain) : Prop :=
  ∃ msg digits, msgFits lay msg ∧ msg ≠ honestMsg answers index lay ∧ Frame answers w index lay msg digits ∧
    LayerShaped answers w index lay digits ∧ encodingQuery w index lay msg ∈ qs
end ClaudeWCT.W9.T3M.Extract
end
-- ==== merged from ClaudeWCT_W9_New_BC_Rows ====
section

namespace ClaudeWCT.W9.T3M.BC
open OracleComp OracleSpec SigGolfCandidate.T3
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
theorem layerEncodingInputP_forest (lay : Layer) (tree leaf : Nat) (root : Digest) (counter : BitVec 32)
    (pad : BitVec 96) (padR : Digest) (hi : BitVec 64) :
    layerEncodingInputP lay tree leaf (.forest root) counter pad padR hi =
      WCT9.pairEncodingInputH lay tree leaf root padR counter pad hi := rfl
theorem layerEncodingInputP_pair (lay : Layer) (tree leaf : Nat) (l r : Digest) (counter : BitVec 32)
    (pad : BitVec 96) (padR : Digest) (hi : BitVec 64) :
    layerEncodingInputP lay tree leaf (.pair l r) counter pad padR hi =
      WCT9.pairEncodingInputH lay tree leaf l r counter pad hi :=
  rfl
def rowLeft : WCT9.LayerMsg → Digest
  | .forest root => root
  | .pair l _ => l
def rowRight (padR : Digest) : WCT9.LayerMsg → Digest
  | .forest _ => padR
  | .pair _ r => r
theorem layerEncodingInputP_eq (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32)
    (pad : BitVec 96) (padR : Digest) (hi : BitVec 64) :
    layerEncodingInputP lay tree leaf msg counter pad padR hi =
      WCT9.pairEncodingInputH lay tree leaf (rowLeft msg) (rowRight padR msg) counter pad hi := by
  cases msg <;> rfl
theorem layerEncodingInputP_length (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32)
    (pad : BitVec 96) (padR : Digest) (hi : BitVec 64) :
    (layerEncodingInputP lay tree leaf msg counter pad padR hi).length = 64 := by
  rw [layerEncodingInputP_eq]; exact WCT9.pairEncodingInputH_length _ _ _ _ _ _ _ _
theorem pad64_pairEncodingInputP (lay : Layer) (tree leaf : Nat) (l r : Digest) (counter : BitVec 32)
    (pad : BitVec 96) :
    pad64 (WCT9.pairEncodingInputP lay tree leaf l r counter pad) = WCT9.pairEncodingInputP lay tree leaf l r counter pad := by
  simp [pad64, WCT9.pairEncodingInputP, bytesLE_length]
theorem pad64_pairEncodingInputH (lay : Layer) (tree leaf : Nat) (l r : Digest) (counter : BitVec 32)
    (pad : BitVec 96) (hi : BitVec 64) :
    pad64 (WCT9.pairEncodingInputH lay tree leaf l r counter pad hi) =
      WCT9.pairEncodingInputH lay tree leaf l r counter pad hi := by
  simp [pad64, WCT9.pairEncodingInputH, bytesLE_length]
theorem pad64_layerEncodingInputP (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32)
    (pad : BitVec 96) (padR : Digest) (hi : BitVec 64) :
    pad64 (layerEncodingInputP lay tree leaf msg counter pad padR hi) =
      layerEncodingInputP lay tree leaf msg counter pad padR hi := by
  rw [layerEncodingInputP_eq, pad64_pairEncodingInputH]
theorem layerEncodingRow_length (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32)
    (pad : BitVec 96) (padR : Digest) (hi : BitVec 64) :
    (pad64 (layerEncodingInputP lay tree leaf msg counter pad padR hi)).length = 64 := by
  rw [pad64_layerEncodingInputP, layerEncodingInputP_length]
/-- The honest encoding (zero pads, row tweak high word 1). -/
theorem pad64_layerEncodingInputP_zero (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32) :
    pad64 (layerEncodingInputP lay tree leaf msg counter 0 0 1) =
      pad64 (WCT9.layerEncodingInput lay tree leaf msg counter) := by
  cases msg with
  | forest root =>
      rw [layerEncodingInputP_forest, WCT9.pairEncodingInputH_one, pad64_pairEncodingInputP]
      exact (pad64_encodingInput lay tree leaf root counter).symm
  | pair l r => rfl
theorem layerEncodingInputP_split (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32)
    (pad : BitVec 96) (padR : Digest) (hi : BitVec 64) :
    ∃ first rest : HashInput, first.length = 16 ∧
      layerEncodingInputP lay tree leaf msg counter pad padR hi =
        first ++ bytesLE 16 (WCT9.rowTweakW lay tree leaf hi) ++ (bytesLE 4 counter ++ rest) := by
  refine ⟨bytesLE 16 (rowLeft msg), bytesLE 12 pad ++ bytesLE 16 (rowRight padR msg), bytesLE_length _ _, ?_⟩
  rw [layerEncodingInputP_eq, WCT9.pairEncodingInputH_eq]
  simp only [List.append_assoc]
/-- C2/C3 (FULL): the header block of an encoding carries the row tweak with the witness high word `hi`. -/
theorem hdrBlock_layerEncodingInputP (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32)
    (pad : BitVec 96) (padR : Digest) (hi : BitVec 64) :
    Extract.hdrBlock (pad64 (layerEncodingInputP lay tree leaf msg counter pad padR hi)) =
      bytesLE 16 (WCT9.rowTweakW lay tree leaf hi) := by
  obtain ⟨first, rest, hf, he⟩ := layerEncodingInputP_split lay tree leaf msg counter pad padR hi
  rw [pad64_layerEncodingInputP, he]
  unfold Extract.hdrBlock
  rw [List.append_assoc, List.drop_left' hf, List.take_left' (bytesLE_length _ _)]
theorem hdrBlock_layerEncodingInput (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32) :
    Extract.hdrBlock (pad64 (WCT9.layerEncodingInput lay tree leaf msg counter)) =
      bytesLE 16 (rowTweak lay tree leaf) := by
  rw [← pad64_layerEncodingInputP_zero]
  exact hdrBlock_layerEncodingInputP lay tree leaf msg counter 0 0 1
def ctrBlock (input : HashInput) : HashInput := (input.drop 32).take 4
theorem ctrBlock_layerEncodingInputP (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32)
    (pad : BitVec 96) (padR : Digest) (hi : BitVec 64) :
    ctrBlock (pad64 (layerEncodingInputP lay tree leaf msg counter pad padR hi)) = bytesLE 4 counter := by
  obtain ⟨first, rest, hf, he⟩ := layerEncodingInputP_split lay tree leaf msg counter pad padR hi
  rw [pad64_layerEncodingInputP, he]
  unfold ctrBlock
  have h32 : (first ++ bytesLE 16 (WCT9.rowTweakW lay tree leaf hi)).length = 32 := by
    simp [hf, bytesLE_length]
  rw [List.drop_left' h32, List.take_left' (bytesLE_length _ _)]
theorem layerEncodingRow_coords {lay lay' : Layer} {tree leaf tree' leaf' : Nat} {msg msg' : WCT9.LayerMsg}
    {c c' : BitVec 32} {pad pad' : BitVec 96} {padR padR' : Digest} {hi hi' : BitVec 64}
    (hl : leaf < 2 ^ height lay) (hr : tree * 2 ^ height lay + leaf < 2 ^ 32)
    (hl' : leaf' < 2 ^ height lay') (hr' : tree' * 2 ^ height lay' + leaf' < 2 ^ 32)
    (h : pad64 (layerEncodingInputP lay tree leaf msg c pad padR hi) =
      pad64 (layerEncodingInputP lay' tree' leaf' msg' c' pad' padR' hi')) :
    lay = lay' ∧ tree = tree' ∧ leaf = leaf' ∧ c = c' := by
  rw [pad64_layerEncodingInputP, pad64_layerEncodingInputP, layerEncodingInputP_eq, layerEncodingInputP_eq] at h
  obtain ⟨e1, e2, e3, -, -, e4, -⟩ := WCT9.pairEncodingInputH_injective hl hr hl' hr' h
  exact ⟨e1, e2, e3, e4⟩
theorem layerEncodingRow_injective {lay lay' : Layer} {tree leaf tree' leaf' : Nat} {msg msg' : WCT9.LayerMsg}
    {c c' : BitVec 32} {pad pad' : BitVec 96} {padR padR' : Digest} {hi hi' : BitVec 64}
    (hl : leaf < 2 ^ height lay) (hr : tree * 2 ^ height lay + leaf < 2 ^ 32)
    (hl' : leaf' < 2 ^ height lay') (hr' : tree' * 2 ^ height lay' + leaf' < 2 ^ 32)
    (hf : Extract.msgFits lay msg) (hf' : Extract.msgFits lay' msg')
    (h : pad64 (layerEncodingInputP lay tree leaf msg c pad padR hi) =
      pad64 (layerEncodingInputP lay' tree' leaf' msg' c' pad' padR' hi')) :
    lay = lay' ∧ tree = tree' ∧ leaf = leaf' ∧ msg = msg' ∧ c = c' ∧ pad = pad' ∧
      (∀ root, msg = .forest root → padR = padR') ∧ hi = hi' := by
  rw [pad64_layerEncodingInputP, pad64_layerEncodingInputP, layerEncodingInputP_eq, layerEncodingInputP_eq] at h
  obtain ⟨rfl, rfl, rfl, hL, hR, rfl, rfl, rfl⟩ := WCT9.pairEncodingInputH_injective hl hr hl' hr' h
  refine ⟨rfl, rfl, rfl, ?_, rfl, rfl, ?_, rfl⟩
  · cases msg with
    | forest root => exact hf.elim
    | pair l r =>
        cases msg' with
        | forest root' => exact hf'.elim
        | pair l' r' => simp only [rowLeft, rowRight] at hL hR; rw [hL, hR]
  · rintro root rfl
    exact hf.elim
theorem layerEncodingRow_injective_leaf {lay : Layer} {tree leaf : Nat} {msg msg' : WCT9.LayerMsg}
    {c c' : BitVec 32} {pad pad' : BitVec 96} {padR padR' : Digest} {hi hi' : BitVec 64}
    (hf : Extract.msgFits lay msg) (hf' : Extract.msgFits lay msg')
    (h : pad64 (layerEncodingInputP lay tree leaf msg c pad padR hi) =
      pad64 (layerEncodingInputP lay tree leaf msg' c' pad' padR' hi')) :
    msg = msg' ∧ c = c' ∧ pad = pad' ∧ (∀ root, msg = .forest root → padR = padR') := by
  rw [pad64_layerEncodingInputP, pad64_layerEncodingInputP, layerEncodingInputP_eq, layerEncodingInputP_eq] at h
  unfold WCT9.pairEncodingInputH at h
  obtain ⟨h, hr⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨h, hp⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨h, hc⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨hL, -⟩ := List.append_inj h (by simp only [bytesLE_length])
  have hL := bytesLE_injective hL
  have hR := bytesLE_injective hr
  refine ⟨?_, bytesLE_injective hc, bytesLE_injective hp, ?_⟩
  · cases msg with
    | forest root => exact hf.elim
    | pair l r =>
        cases msg' with
        | forest root' => exact hf'.elim
        | pair l' r' => simp only [rowLeft, rowRight] at hL hR; rw [hL, hR]
  · rintro root rfl
    exact hf.elim
/-- The row tweak's high word of two equal encoding rows agrees (C2/C3 FULL: the high word is a witness pad). -/
theorem layerEncodingRow_hi_eq {lay : Layer} {tree leaf : Nat} {msg msg' : WCT9.LayerMsg}
    {c c' : BitVec 32} {pad pad' : BitVec 96} {padR padR' : Digest} {hi hi' : BitVec 64}
    (h : pad64 (layerEncodingInputP lay tree leaf msg c pad padR hi) =
      pad64 (layerEncodingInputP lay tree leaf msg' c' pad' padR' hi')) : hi = hi' := by
  rw [pad64_layerEncodingInputP, pad64_layerEncodingInputP, layerEncodingInputP_eq, layerEncodingInputP_eq] at h
  unfold WCT9.pairEncodingInputH at h
  obtain ⟨h, -⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨h, -⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨h, -⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨-, ht⟩ := List.append_inj h (by simp only [bytesLE_length])
  exact (append64_inj (bytesLE_injective ht)).1
/-- Honest layer frame with a zero 12-byte row pad and the honest row high word 1 (C2/C3 FULL). (Nested FTS r1-1:
the L3 row is a pair row, so the old `wbcRight` slot is no longer read and carries no condition.) -/
def GoodZ (answers : SigGolfCandidate.T3.Correctness.Answers) (w : WBytes) (index : Nat) (lay : Layer) : Prop :=
  Extract.Good answers w index lay ∧ wbcPad w index lay = 0 ∧ wbcHigh w index lay = 1
theorem GoodZ.good {answers : SigGolfCandidate.T3.Correctness.Answers} {w : WBytes} {index : Nat} {lay : Layer}
    (h : GoodZ answers w index lay) : Extract.Good answers w index lay := h.1
end ClaudeWCT.W9.T3M.BC
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsEvents ====
section

namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue)
noncomputable def leafMsg (answers : Answers) (L : LeafAddr) : WCT9.LayerMsg :=
  if h : L.lay.val < 3 then
    .pair (Extract.honestPair answers ⟨L.lay.val + 1, by omega⟩ (L.tree * 2 ^ height L.lay + L.leaf)).1
      (Extract.honestPair answers ⟨L.lay.val + 1, by omega⟩ (L.tree * 2 ^ height L.lay + L.leaf)).2
  else .pair (Extract.honestTop answers ((L.tree * 2 ^ height L.lay + L.leaf) % 2 ^ 31)).1
    (Extract.honestTop answers ((L.tree * 2 ^ height L.lay + L.leaf) % 2 ^ 31)).2
theorem msgFits_leafMsg (answers : Answers) (L : LeafAddr) : Extract.msgFits L.lay (leafMsg answers L) := by
  unfold leafMsg
  split_ifs <;> trivial
/-- Encoding-row witness pads: bytes 36..48, the (unused since nested FTS) forest right slot, and (C2/C3 FULL) the
row tweak's high word as an XOR mask on its honest value 1, so the zero pad is the honest row. -/
abbrev RowPad := BitVec 96 × Digest × BitVec 64
def encRow (L : LeafAddr) (msg : WCT9.LayerMsg) (counter : BitVec 32) (pad : RowPad) : HashInput :=
  pad64 (layerEncodingInputP L.lay L.tree L.leaf msg counter pad.1 pad.2.1 (pad.2.2 ^^^ 1))
theorem encRow_zero (L : LeafAddr) (msg : WCT9.LayerMsg) (counter : BitVec 32) :
    encRow L msg counter 0 = pad64 (WCT9.layerEncodingInput L.lay L.tree L.leaf msg counter) := by
  show pad64 (layerEncodingInputP L.lay L.tree L.leaf msg counter 0 0 ((0 : BitVec 64) ^^^ 1)) = _
  rw [show ((0 : BitVec 64) ^^^ 1 : BitVec 64) = 1 by decide]
  exact BC.pad64_layerEncodingInputP_zero _ _ _ _ _
theorem searchLimit_fits (lay : Layer) : 0 + WCT9.searchLimit lay ≤ 2 ^ 32 := by
  have := WCT9.searchLimit_le lay
  unfold counterLimit at this
  omega
noncomputable def referenceSearch (answers : Answers) (L : LeafAddr) : Option (BitVec 32 × List Nat) :=
  evalWithAnswerFn answers (WCT9.layerCounterSearch L.lay L.tree L.leaf (leafMsg answers L) 0 (WCT9.searchLimit L.lay))
noncomputable def referenceDigits (answers : Answers) (L : LeafAddr) : List Nat :=
  ((referenceSearch answers L).map Prod.snd).getD (dummyDigits L.lay)
noncomputable def depth (answers : Answers) (a : ChainAddr) : Nat :=
  (referenceDigits answers a.key).getD a.chain 0
/-! ### C3 (FULL): the honest chain of the current scheme (`WCT9.chainW`, chain 0 of a lower layer keeps the HIGH
half of its last step) and chain rows read through the half their step uses. -/
/-- Pairing stage 1: a chain row of the current scheme, `WCT9.chainInputW` (F rows `0 | hdr | 0 | v`, G rows
`v | hdr | 0 | 0`). The header determines the chain and hence the format. -/
def chainRowW (a : ChainAddr) (step : Nat) (value : Digest) : HashInput :=
  WCT9.chainInputW a.key.lay a.key.tree a.key.leaf a.chain step value
theorem chainRowW_eq (a : ChainAddr) (step : Nat) (value : Digest) :
    chainRowW a step value = WCT9.chainInputW a.key.lay a.key.tree a.key.leaf a.chain step value := rfl
theorem chainRowW_length (a : ChainAddr) (step : Nat) (value : Digest) : (chainRowW a step value).length = 64 :=
  WCT9.chainInputW_length _ _ _ _ _ _
theorem pad64_chainInputW (lay : Layer) (tree leaf i step : Nat) (value : Digest) :
    pad64 (WCT9.chainInputW lay tree leaf i step value) = WCT9.chainInputW lay tree leaf i step value :=
  WCT9.chainInputW_padded _ _ _ _ _ _
theorem pad64_chainRowW (a : ChainAddr) (step : Nat) (value : Digest) :
    pad64 (chainRowW a step value) = chainRowW a step value := WCT9.chainInputW_padded _ _ _ _ _ _
theorem chainInputW_hdr_eq {lay lay' : Layer} {tree leaf i step tree' leaf' i' step' : Nat} {value value' : Digest}
    (h : WCT9.chainInputW lay tree leaf i step value = WCT9.chainInputW lay' tree' leaf' i' step' value') :
    chainHeader lay tree leaf i step = chainHeader lay' tree' leaf' i' step' := by
  have := congrArg (fun l : List UInt8 => (l.drop 16).take 16) h
  simp only [WCT9.chainInputW_header] at this
  exact SphincsSecurity.bytesLE_injective this
/-- Field recovery for the format-aware chain input: equal inputs have equal headers and values. -/
theorem chainInputW_fields {lay lay' : Layer} {tree leaf i step tree' leaf' i' step' : Nat} {value value' : Digest}
    (h : WCT9.chainInputW lay tree leaf i step value = WCT9.chainInputW lay' tree' leaf' i' step' value') :
    chainHeader lay tree leaf i step = chainHeader lay' tree' leaf' i' step' ∧ value = value' := by
  have hh := chainInputW_hdr_eq h
  refine ⟨hh, ?_⟩
  -- Witness stack: the header no longer fixes the format on the top (`topIsG` needs `i ≤ 52`, the header only
  -- `i % 2^24`); a G input equal to an F input has both values 0 (bytes 0..16 resp. 48..64 are zero).
  have hz : ∀ v : Digest, SphincsSecurity.bytesLE 16 v = zero16 → v = 0 := fun v hv =>
    SphincsSecurity.bytesLE_injective (hv.trans WCT9.bytesLE_zero16.symm)
  have hb : ∀ v : Digest, (SphincsSecurity.bytesLE 16 v).length = 16 := fun v => SphincsSecurity.bytesLE_length 16 v
  have hz16 : zero16.length = 16 := rfl
  cases hG : WCT9.isG lay i <;> cases hG' : WCT9.isG lay' i'
  · rw [WCT9.chainInputW_F hG, WCT9.chainInputW_F hG'] at h
    exact (chainInput_fields h).2
  · rw [WCT9.chainInputW_F hG, WCT9.chainInputW_G hG'] at h
    unfold SigGolfCandidate.T3.chainInput at h
    simp only [List.append_assoc] at h
    obtain ⟨h1, h'⟩ := List.append_inj h (by simp only [hb, hz16])
    obtain ⟨-, h'⟩ := List.append_inj h' (by simp only [hb])
    obtain ⟨-, h2⟩ := List.append_inj h' rfl
    rw [hz _ h1.symm, hz _ h2]
  · rw [WCT9.chainInputW_G hG, WCT9.chainInputW_F hG'] at h
    unfold SigGolfCandidate.T3.chainInput at h
    simp only [List.append_assoc] at h
    obtain ⟨h1, h'⟩ := List.append_inj h (by simp only [hb, hz16])
    obtain ⟨-, h'⟩ := List.append_inj h' (by simp only [hb])
    obtain ⟨-, h2⟩ := List.append_inj h' rfl
    rw [hz _ h1, hz _ h2.symm]
  · rw [WCT9.chainInputW_G hG, WCT9.chainInputW_G hG'] at h
    have := congrArg (List.take 16) h
    simp only [List.append_assoc] at this
    rw [List.take_left' (SphincsSecurity.bytesLE_length 16 _),
      List.take_left' (SphincsSecurity.bytesLE_length 16 _)] at this
    exact SphincsSecurity.bytesLE_injective this
theorem chainRowW_inj {a : ChainAddr} {s s' : Nat} {v v' : Digest} (hs : s < 256) (hs' : s' < 256)
    (h : chainRowW a s v = chainRowW a s' v') : s = s' ∧ v = v' := by
  obtain ⟨hh, hv⟩ := chainInputW_fields h
  have hp := (chainHeader_fields hh).2.2.2.2
  exact ⟨by omega, hv⟩
theorem chainInputW_eq_chainRowW {lay : Layer} {tree leaf i s s' : Nat} {v v' : Digest} {a : ChainAddr}
    (hi : i < 2 ^ 24) (hc : a.chain < 2 ^ 24) (hs : s < 256) (hs' : s' < 256)
    (h : WCT9.chainInputW lay tree leaf i s v = chainRowW a s' v') :
    SigGolfCandidate.T3.Security.Wots.Mask.LeafAlias lay tree leaf a.key ∧ i = a.chain ∧ s = s' ∧ v = v' := by
  obtain ⟨hh, hv⟩ := chainInputW_fields h
  obtain ⟨hl, ht, hf, hi', hs''⟩ := chainHeader_fields hh
  exact ⟨⟨hl, ht, hf⟩, by omega, by omega, hv⟩
/-- The half of a chain row's output that chain `a` reads after `step`. -/
def rowHalf (a : ChainAddr) (step : Nat) (output : HashOutput) : Digest :=
  WCT9.halfOf (WCT9.chainHigh a.key.lay a.chain step) output
/-- A trace row of chain `a` at `step` with input value `value` whose used half is `out`. -/
def SeenRowW (trace : List Entry) (a : ChainAddr) (step : Nat) (value out : Digest) : Prop :=
  ∃ answer, (chainRowW a step value, answer) ∈ trace ∧ rowHalf a step answer = out
theorem seenRowW_mono {trace trace' : List Entry} {a : ChainAddr} {step : Nat} {value out : Digest}
    (h : SeenRowW trace a step value out) (hsub : ∀ e ∈ trace, e ∈ trace') : SeenRowW trace' a step value out := by
  obtain ⟨answer, hm, hl⟩ := h
  exact ⟨answer, hsub _ hm, hl⟩
/-- The honest value of chain `(lay, tree, leaf, i)` after `step` steps from `seed` (current scheme). -/
noncomputable def honestChainValueW (answers : Answers) (lay : Layer) (tree leaf i : Nat) (seed : Digest)
    (step : Nat) : Digest :=
  evalWithAnswerFn answers (WCT9.chainW lay tree leaf i 0 step seed)
theorem chainW_add' (lay : Layer) (tree leaf i start m n : Nat) (value : Digest) :
    WCT9.chainW lay tree leaf i start (m + n) value =
      (WCT9.chainW lay tree leaf i start m value >>= WCT9.chainW lay tree leaf i (start + m) n) := by
  unfold WCT9.chainW
  rw [← List.range'_append_1, List.foldlM_append]
theorem eval_chainW_add' (answers : Answers) (lay : Layer) (tree leaf i start m n : Nat) (value : Digest) :
    evalWithAnswerFn answers (WCT9.chainW lay tree leaf i start (m + n) value) =
      evalWithAnswerFn answers (WCT9.chainW lay tree leaf i (start + m) n
        (evalWithAnswerFn answers (WCT9.chainW lay tree leaf i start m value))) := by
  rw [chainW_add', evalWithAnswerFn_bind]
theorem eval_halfHash' (answers : Answers) (high : Bool) (input : HashInput) :
    evalWithAnswerFn answers (WCT9.halfHash high input) = WCT9.halfOf high (answers (.inl (.inr (pad64 input)))) := by
  cases high <;> rfl
theorem queried_halfHash' (answers : Answers) (high : Bool) (input : HashInput) :
    queried answers (WCT9.halfHash high input) = [.inl (.inr (pad64 input))] := by
  cases high <;> rfl
@[simp] theorem chainW_zero' (lay : Layer) (tree leaf i start : Nat) (value : Digest) :
    WCT9.chainW lay tree leaf i start 0 value = pure value := rfl
theorem chainW_one' (lay : Layer) (tree leaf i start : Nat) (value : Digest) :
    WCT9.chainW lay tree leaf i start 1 value =
      WCT9.halfHash (WCT9.chainHigh lay i start) (WCT9.chainInputW lay tree leaf i start value) := by
  unfold WCT9.chainW
  simp only [List.range'_one, List.foldlM_cons, List.foldlM_nil, bind_pure]
theorem eval_chainW_one' (answers : Answers) (lay : Layer) (tree leaf i s : Nat) (v : Digest) :
    evalWithAnswerFn answers (WCT9.chainW lay tree leaf i s 1 v) =
      WCT9.halfOf (WCT9.chainHigh lay i s) (answers (.inl (.inr (pad64 (WCT9.chainInputW lay tree leaf i s v))))) := by
  rw [chainW_one', eval_halfHash']
theorem honestChainValueW_zero (answers : Answers) (lay : Layer) (tree leaf i : Nat) (seed : Digest) :
    honestChainValueW answers lay tree leaf i seed 0 = seed := rfl
theorem honestChainValueW_succ (answers : Answers) (lay : Layer) (tree leaf i : Nat) (seed : Digest) (step : Nat) :
    WCT9.halfOf (WCT9.chainHigh lay i step) (answers (.inl (.inr (pad64 (WCT9.chainInputW lay tree leaf i step
      (honestChainValueW answers lay tree leaf i seed step)))))) =
        honestChainValueW answers lay tree leaf i seed (step + 1) := by
  unfold honestChainValueW
  rw [eval_chainW_add', Nat.zero_add, eval_chainW_one']
/-- On an F chain (`isG = false`), below the last step of a chain or off chain 0 of a lower layer, the current
chain is the legacy chain. -/
theorem honestChainValueW_eq {answers : Answers} {lay : Layer} {tree leaf i : Nat} {seed : Digest} {step : Nat}
    (hG : WCT9.isG lay i = false) (h : lay = 0 ∨ i ≠ 0 ∨ step ≤ 6) :
    honestChainValueW answers lay tree leaf i seed step = honestChainValue answers lay tree leaf i seed step := by
  unfold honestChainValueW honestChainValue
  have hl : ∀ s, 0 ≤ s → s < 0 + step → WCT9.chainHigh lay i s = false := by
    intro s _ hs
    rcases h with h | h | h
    · subst h
      rw [WCT9.chainHigh_top_eq]
      exact WCT9.topChainHigh_of_F (by rw [← WCT9.isG_top_eq]; exact hG)
    · exact WCT9.chainHigh_eq_false_F hG (Or.inl h)
    · exact WCT9.chainHigh_eq_false_F hG (Or.inr (by omega))
  rw [WCT9.chainW_of_low hG hl tree leaf seed]
theorem rowHalf_of_low {a : ChainAddr} {step : Nat} (h : WCT9.chainHigh a.key.lay a.chain step = false)
    (output : HashOutput) : rowHalf a step output = low output := by
  unfold rowHalf; rw [h]; rfl
/-- An output whose `high`-selected half is `v` and whose other half is `o`. -/
noncomputable def joinHalf (high : Bool) (v o : Digest) : HashOutput :=
  if high then SigGolfCandidate.T3.Security.ChainGraph.joinOutput o v else SigGolfCandidate.T3.Security.ChainGraph.joinOutput v o
theorem halfOf_joinHalf (high : Bool) (v o : Digest) : WCT9.halfOf high (joinHalf high v o) = v := by
  cases high
  · exact SigGolfCandidate.T3.Security.ChainGraph.joinOutput_low _ _
  · exact SigGolfCandidate.T3.Security.ChainGraph.joinOutput_high _ _
theorem halfOf_not_joinHalf (high : Bool) (v o : Digest) : WCT9.halfOf (!high) (joinHalf high v o) = o := by
  cases high
  · exact SigGolfCandidate.T3.Security.ChainGraph.joinOutput_high _ _
  · exact SigGolfCandidate.T3.Security.ChainGraph.joinOutput_low _ _
theorem joinHalf_halfOf (high : Bool) (y : HashOutput) :
    joinHalf high (WCT9.halfOf high y) (WCT9.halfOf (!high) y) = y := by
  cases high <;> exact SigGolfCandidate.T3.Security.ChainGraph.joinOutput_parts _
@[simp] theorem halfOf_zero (high : Bool) : WCT9.halfOf high (0 : HashOutput) = 0 := by
  cases high <;> rfl
noncomputable def frontierValue (answers : Answers) (a : ChainAddr) : Digest :=
  honestChainValueW answers a.key.lay a.key.tree a.key.leaf a.chain
    (WCT9.wotsSeed answers a.key.lay a.key.tree a.key.leaf a.chain) (depth answers a)
def ContactAt (answers : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  1 ≤ depth answers a ∧ ∃ value, SeenRowW trace a (depth answers a - 1) value (frontierValue answers a)
def TwoEdgeAt (answers : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  2 ≤ depth answers a ∧ ∃ start middle, SeenRowW trace a (depth answers a - 2) start middle ∧
    SeenRowW trace a (depth answers a - 1) middle (frontierValue answers a)
noncomputable def referenceInput (answers : Answers) (L : LeafAddr) : Option HashInput :=
  (referenceSearch answers L).map fun selected => encRow L (leafMsg answers L) selected.1 0
def EncodingMatchAt (answers : Answers) (trace : List Entry) (L : LeafAddr) : Prop :=
  ∃ message counter pad answer, Extract.msgFits L.lay message ∧ (encRow L message counter pad, answer) ∈ trace ∧
    referenceInput answers L ≠ some (encRow L message counter pad) ∧
    decode L.lay (WCT9.encodingAnswer L.lay answer) = some (referenceDigits answers L)
def MarkerAt (answers : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  ∃ message counter pad answer digits, Extract.msgFits a.key.lay message ∧
    (encRow a.key message counter pad, answer) ∈ trace ∧
    referenceInput answers a.key ≠ some (encRow a.key message counter pad) ∧
    decode a.key.lay (WCT9.encodingAnswer a.key.lay answer) = some digits ∧
    digits.getD a.chain 0 + 1 = (referenceDigits answers a.key).getD a.chain 0 ∧
    ∀ i, i ≠ a.chain → (referenceDigits answers a.key).getD i 0 ≤ digits.getD i 0
def OtherChainRow (answers : Answers) (input : HashInput) : Prop :=
  ∃ (a : ChainAddr) (step : Nat), Extract.posOf input =
      some (.chain a.key.lay a.key.tree a.key.leaf a.chain step) ∧
    ((∀ value, input ≠ chainRowW a step value) ∨ depth answers a ≤ step)
def StructuralClass (answers : Answers) (input : HashInput) (position : Extract.Pos) : Prop :=
  match position with
  | .chain _ _ _ _ _ => OtherChainRow answers input
  | _ => True
def StructuralHit (answers : Answers) (trace : List Entry) : Prop :=
  ∃ position input answer, (input, answer) ∈ trace ∧ Extract.posOf input = some position ∧
    position.Bounded ∧ StructuralClass answers input position ∧
    HashHit answers (Extract.honestInput answers position) input
def WotsPrimitive (answers : Answers) (trace : List Entry) : Prop :=
  (∃ L, EncodingMatchAt answers trace L) ∨ StructuralHit answers trace ∨
    (∃ a, TwoEdgeAt answers trace a) ∨
    (∃ a b, a ≠ b ∧ ContactAt answers trace a ∧ ContactAt answers trace b) ∨
    (∃ a, MarkerAt answers trace a ∧ ContactAt answers trace a)
end ClaudeWCT.W9.T3.Security.Wots

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open SigGolfCandidate.T3
open SigGolfCandidate.T3.Security.Wots

/-- The unique WOTS leaf authenticating the tree containing `L`. The value at
    layer zero is unused; recursive calls are made only for positive layers. -/
def parent (L : LeafAddr) : LeafAddr :=
  let lay : Layer := ⟨L.lay.val - 1, by have := L.lay.isLt; omega⟩
  ⟨lay, L.tree / 2 ^ height lay, L.tree % 2 ^ height lay⟩

theorem parent_layer_lt (L : LeafAddr) (h : L.lay.val ≠ 0) : (parent L).lay.val < L.lay.val := by
  simp only [parent]
  omega

/-- A canonical search result: the counter, the digits and the selected half (`true` = LOW). -/
abbrev Search := LeafAddr → Nat → Option (BitVec 32 × List Nat × Bool)
/-- Path-aware credit: layer, selected half (`true` = LOW), digits. -/
abbrev Credit := Layer → Bool → List Nat → Nat

/-- Remaining credit after the canonical search at a leaf. The recursion goes
    from a leaf to its ancestors and never depends on a descendant or an FTS
    digest. Failure of an ancestor propagates to the descendant. -/
def after (search : Search) (credit : Credit) (L : LeafAddr) : Option Nat :=
  (if L.lay.val = 0 then some WCT9.CanonicalPolicy.totalCredit else after search credit (parent L)).bind fun remaining =>
    (search L remaining).map fun found => remaining - credit L.lay found.2.2 found.2.1
termination_by L.lay.val
decreasing_by exact parent_layer_lt L (by assumption)

def context (search : Search) (credit : Credit) (L : LeafAddr) : Option Nat :=
  if L.lay.val = 0 then some WCT9.CanonicalPolicy.totalCredit else after search credit (parent L)

def selected (search : Search) (credit : Credit) (L : LeafAddr) : Option (BitVec 32 × List Nat × Bool) :=
  (context search credit L).bind (search L)

theorem after_eq (search : Search) (credit : Credit) (L : LeafAddr) :
    after search credit L = (context search credit L).bind fun remaining =>
      (search L remaining).map fun found => remaining - credit L.lay found.2.2 found.2.1 := by
  rw [after]
  rfl

theorem context_top (search : Search) (credit : Credit) (L : LeafAddr) (h : L.lay.val = 0) :
    context search credit L = some WCT9.CanonicalPolicy.totalCredit := by simp only [context, if_pos h]

theorem context_parent (search : Search) (credit : Credit) (L : LeafAddr) (h : L.lay.val ≠ 0) :
    context search credit L = after search credit (parent L) := by simp only [context, if_neg h]

/-- Preserving each canonical successful search (and each canonical failure)
    preserves every descendant's threshold context. Equality is needed only at
    the original canonical context, rather than at every possible threshold. -/
theorem after_congr {search search' : Search} (credit : Credit)
    (hsearch : ∀ L remaining, context search credit L = some remaining →
      search' L remaining = search L remaining) (L : LeafAddr) :
    after search' credit L = after search credit L := by
  have hall : ∀ n, ∀ L : LeafAddr, L.lay.val = n → after search' credit L = after search credit L := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro L hL
        have hc : context search' credit L = context search credit L := by
          unfold context
          by_cases hzero : L.lay.val = 0
          · rw [if_pos hzero, if_pos hzero]
          · rw [if_neg hzero, if_neg hzero]
            exact ih (parent L).lay.val (hL ▸ parent_layer_lt L hzero) (parent L) rfl
        rw [after_eq, after_eq, hc]
        cases he : context search credit L with
        | none => rfl
        | some remaining =>
            simp only [Option.bind_some]
            rw [hsearch L remaining he]
  exact hall L.lay.val L rfl

theorem context_congr {search search' : Search} (credit : Credit)
    (hsearch : ∀ L remaining, context search credit L = some remaining →
      search' L remaining = search L remaining) (L : LeafAddr) :
    context search' credit L = context search credit L := by
  unfold context
  split
  · rfl
  · exact after_congr credit hsearch (parent L)

theorem selected_congr {search search' : Search} (credit : Credit)
    (hsearch : ∀ L remaining, context search credit L = some remaining →
      search' L remaining = search L remaining) (L : LeafAddr) :
    selected search' credit L = selected search credit L := by
  unfold selected
  rw [context_congr credit hsearch L]
  cases he : context search credit L with
  | none => rfl
  | some remaining => exact hsearch L remaining he

/-- A finite source universe suffices when it is closed under parent leaves. -/
theorem after_congr_on {search search' : Search} (credit : Credit)
    (allowed : LeafAddr → Prop)
    (hparent : ∀ L, allowed L → L.lay.val ≠ 0 → allowed (parent L))
    (hsearch : ∀ L, allowed L → ∀ remaining, context search credit L = some remaining →
      search' L remaining = search L remaining) {L : LeafAddr} (hL : allowed L) :
    after search' credit L = after search credit L := by
  have hall : ∀ n, ∀ L : LeafAddr, L.lay.val = n → allowed L →
      after search' credit L = after search credit L := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro L hn hL
        have hc : context search' credit L = context search credit L := by
          unfold context
          by_cases hzero : L.lay.val = 0
          · rw [if_pos hzero, if_pos hzero]
          · rw [if_neg hzero, if_neg hzero]
            exact ih (parent L).lay.val (hn ▸ parent_layer_lt L hzero) (parent L) rfl
              (hparent L hL hzero)
        rw [after_eq, after_eq, hc]
        cases he : context search credit L with
        | none => rfl
        | some remaining =>
            simp only [Option.bind_some]
            rw [hsearch L hL remaining he]
  exact hall L.lay.val L rfl hL

theorem context_congr_on {search search' : Search} (credit : Credit)
    (allowed : LeafAddr → Prop)
    (hparent : ∀ L, allowed L → L.lay.val ≠ 0 → allowed (parent L))
    (hsearch : ∀ L, allowed L → ∀ remaining, context search credit L = some remaining →
      search' L remaining = search L remaining) {L : LeafAddr} (hL : allowed L) :
    context search' credit L = context search credit L := by
  unfold context
  split_ifs with hzero
  · rfl
  · exact after_congr_on credit allowed hparent hsearch (hparent L hL hzero)

/-- The message family is explicit so the same canonical search applies to the
    paired forest and to the original forest during the transition. -/
noncomputable def searchOf (answers : SigGolfCandidate.T3.Correctness.Answers)
    (messages : LeafAddr → WCT9.LayerMsg) : Search := fun L remaining =>
  evalWithAnswerFn answers (WCT9.CanonicalPolicy.layerCounterSearchAt L.lay
    (WCT9.CanonicalPolicy.threshold L.lay.val remaining) L.tree L.leaf
    (messages L) 0 (WCT9.searchLimit L.lay))

noncomputable def referenceContext (answers : SigGolfCandidate.T3.Correctness.Answers)
    (messages : LeafAddr → WCT9.LayerMsg) : LeafAddr → Option Nat :=
  context (searchOf answers messages) WCT9.CanonicalPolicy.credit

noncomputable def referenceSearch (answers : SigGolfCandidate.T3.Correctness.Answers)
    (messages : LeafAddr → WCT9.LayerMsg) : LeafAddr → Option (BitVec 32 × List Nat × Bool) :=
  selected (searchOf answers messages) WCT9.CanonicalPolicy.credit

theorem referenceSearch_congr
    {answers answers' : SigGolfCandidate.T3.Correctness.Answers}
    {messages messages' : LeafAddr → WCT9.LayerMsg}
    (hsearch : ∀ L remaining, referenceContext answers messages L = some remaining →
      searchOf answers' messages' L remaining = searchOf answers messages L remaining) (L : LeafAddr) :
    referenceSearch answers' messages' L = referenceSearch answers messages L :=
  selected_congr WCT9.CanonicalPolicy.credit hsearch L

theorem referenceContext_congr
    {answers answers' : SigGolfCandidate.T3.Correctness.Answers}
    {messages messages' : LeafAddr → WCT9.LayerMsg}
    (hsearch : ∀ L remaining, referenceContext answers messages L = some remaining →
      searchOf answers' messages' L remaining = searchOf answers messages L remaining) :
    referenceContext answers' messages' = referenceContext answers messages := by
  funext L
  exact context_congr WCT9.CanonicalPolicy.credit hsearch L

noncomputable def decodeRow (answers : SigGolfCandidate.T3.Correctness.Answers)
    (L : LeafAddr) (floor : Nat) (message : WCT9.LayerMsg) (counter : Nat) : Option (List Nat × Bool) :=
  WCT9.CanonicalPolicy.producerDecodeOut L.lay floor
    (evalWithAnswerFn answers (publicHash
      (WCT9.layerEncodingInput L.lay L.tree L.leaf message (BitVec.ofNat 32 counter))))

/-- It suffices to preserve decisions on the original reached prefix. In
    particular, replacing a rejected answer by another rejected answer leaves
    the canonical counter and digit word unchanged. -/
theorem search_congr (answers answers' : SigGolfCandidate.T3.Correctness.Answers)
    (L : LeafAddr) (floor : Nat) (message : WCT9.LayerMsg) : ∀ fuel start,
    (∀ c < fuel, (∀ c' < c, decodeRow answers L floor message (start + c') = none) →
      decodeRow answers' L floor message (start + c) = decodeRow answers L floor message (start + c)) →
    evalWithAnswerFn answers' (WCT9.CanonicalPolicy.layerCounterSearchAt L.lay floor L.tree L.leaf message start fuel) =
      evalWithAnswerFn answers (WCT9.CanonicalPolicy.layerCounterSearchAt L.lay floor L.tree L.leaf message start fuel) := by
  intro fuel
  induction fuel with
  | zero => intro start _; rfl
  | succ fuel ih =>
      intro start h
      have hzero : decodeRow answers' L floor message start = decodeRow answers L floor message start := by
        have h0 := h 0 (Nat.zero_lt_succ _) (fun c hc => absurd hc (Nat.not_lt_zero _))
        simpa only [Nat.add_zero] using h0
      have hrest (hnone : decodeRow answers L floor message start = none) :
          evalWithAnswerFn answers' (WCT9.CanonicalPolicy.layerCounterSearchAt L.lay floor L.tree L.leaf message (start + 1) fuel) =
            evalWithAnswerFn answers (WCT9.CanonicalPolicy.layerCounterSearchAt L.lay floor L.tree L.leaf message (start + 1) fuel) := by
        apply ih (start + 1)
        intro c hc hprev
        have hnext := h (c + 1) (by omega) (fun c' hc' => by
          cases c' with
          | zero => simpa only [Nat.add_zero] using hnone
          | succ c' =>
              have hp := hprev c' (by omega)
              simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hp)
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hnext
      rw [WCT9.CanonicalPolicy.layerCounterSearchAt]
      conv_lhs => rw [evalWithAnswerFn_bind]
      conv_rhs => rw [evalWithAnswerFn_bind]
      change evalWithAnswerFn answers' (match decodeRow answers' L floor message start with
        | none => WCT9.CanonicalPolicy.layerCounterSearchAt L.lay floor L.tree L.leaf message (start + 1) fuel
        | some found => pure (some (BitVec.ofNat 32 start, found))) =
        evalWithAnswerFn answers (match decodeRow answers L floor message start with
        | none => WCT9.CanonicalPolicy.layerCounterSearchAt L.lay floor L.tree L.leaf message (start + 1) fuel
        | some found => pure (some (BitVec.ofNat 32 start, found)))
      rw [hzero]
      cases hd : decodeRow answers L floor message start with
      | none => exact hrest hd
      | some digits => rfl

theorem reference_congr_of_decisions
    (answers answers' : SigGolfCandidate.T3.Correctness.Answers)
    (messages messages' : LeafAddr → WCT9.LayerMsg)
    (allowed : LeafAddr → Prop)
    (hparent : ∀ L, allowed L → L.lay.val ≠ 0 → allowed (parent L))
    (hmessages : ∀ L, allowed L → messages' L = messages L)
    (hdecisions : ∀ L, allowed L → ∀ remaining, referenceContext answers messages L = some remaining →
      ∀ c < WCT9.searchLimit L.lay,
        (∀ c' < c, decodeRow answers L (WCT9.CanonicalPolicy.threshold L.lay.val remaining) (messages L) c' = none) →
        decodeRow answers' L (WCT9.CanonicalPolicy.threshold L.lay.val remaining) (messages L) c =
          decodeRow answers L (WCT9.CanonicalPolicy.threshold L.lay.val remaining) (messages L) c)
    {L : LeafAddr} (hL : allowed L) :
    referenceContext answers' messages' L = referenceContext answers messages L ∧
      referenceSearch answers' messages' L = referenceSearch answers messages L := by
  have hs : ∀ L, allowed L → ∀ remaining, referenceContext answers messages L = some remaining →
      searchOf answers' messages' L remaining = searchOf answers messages L remaining := by
    intro L hL remaining hc
    unfold searchOf
    rw [hmessages L hL]
    apply search_congr answers answers' L _ _ _ 0
    simpa only [Nat.zero_add] using hdecisions L hL remaining hc
  have hc := context_congr_on WCT9.CanonicalPolicy.credit allowed hparent hs hL
  refine ⟨hc, ?_⟩
  exact (congrArg (fun o : Option Nat => o.bind (searchOf answers' messages' L)) hc).trans
    (Option.bind_congr (fun remaining he => hs L hL remaining he))

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
namespace ClaudeWCT.W9.T3.Security.WotsExtract
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security.Wots
def SourceLeaf7 (L : LeafAddr) : Prop := L.tree < 2 ^ ClaudeWCT.W9.T3M.Extract.treeBits L.lay ∧ L.leaf < 2 ^ height L.lay
def SourceChain7 (a : ChainAddr) : Prop := SourceLeaf7 a.key ∧ a.chain < chainCount a.key.lay
theorem SourceLeaf7.tree_lt {L : LeafAddr} (h : SourceLeaf7 L) : L.tree < 2 ^ 31 :=
  lt_of_lt_of_le h.1 (Nat.pow_le_pow_right (by decide)
    (le_trans (ClaudeWCT.W9.T3M.Extract.treeBits_le _) (by decide)))
end ClaudeWCT.W9.T3.Security.WotsExtract

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

noncomputable def referenceDigits (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (L : LeafAddr) : List Nat :=
  ((referenceSearch answers messages L).map fun found => found.2.1).getD
    (dummyDigits (WCT9.CanonicalPolicy.normalLayer L.lay))

/-- The half the canonical search selected (`true` = LOW; `true` when the search fails). -/
noncomputable def referenceLow (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (L : LeafAddr) : Bool :=
  ((referenceSearch answers messages L).map fun found => found.2.2).getD true

noncomputable def depth (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (a : ChainAddr) : Nat := (referenceDigits answers messages a.key).getD a.chain 0

/-- C3 (#866): the frontier is the honest chain of the current scheme (`honestChainValueW`: lower chain 0's last
step keeps the HIGH half). -/
noncomputable def frontierValue (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (a : ChainAddr) : Digest :=
  ClaudeWCT.W9.T3.Security.Wots.honestChainValueW answers a.key.lay a.key.tree a.key.leaf a.chain
    (WCT9.wotsSeed answers a.key.lay a.key.tree a.key.leaf a.chain) (depth answers messages a)

noncomputable def referenceInput (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (L : LeafAddr) : Option HashInput :=
  (referenceSearch answers messages L).map fun selected => encRow L (messages L) selected.1 0


end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M

/-- C3 (#866): chain rows are read through the half their step keeps (`SeenRowW`). -/
def ContactAt (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (trace : List Entry) (a : ChainAddr) : Prop :=
  1 ≤ depth answers messages a ∧ ∃ value,
    ClaudeWCT.W9.T3.Security.Wots.SeenRowW trace a (depth answers messages a - 1) value
      (frontierValue answers messages a)

def TwoEdgeAt (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (trace : List Entry) (a : ChainAddr) : Prop :=
  2 ≤ depth answers messages a ∧ ∃ start middle,
    ClaudeWCT.W9.T3.Security.Wots.SeenRowW trace a (depth answers messages a - 2) start middle ∧
    ClaudeWCT.W9.T3.Security.Wots.SeenRowW trace a (depth answers messages a - 1) middle
      (frontierValue answers messages a)

/-- Configuration (1)+(2): `input` is none of the canonical search's own honest rows (honest message, zero pads)
up to the selected counter. With path-aware floors a rejected honest row can still decode, through its other
half, to the reference word; a forgery through such a row has honest message and pads and is covered by `Good`
(any counter), so the encoding-match event excludes these rows. -/
def NotSearched (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg) (L : LeafAddr) (input : HashInput) :
    Prop :=
  ∀ found, referenceSearch answers messages L = some found →
    ∀ c : Nat, c ≤ found.1.toNat → input ≠ encRow L (messages L) (BitVec.ofNat 32 c) 0

def EncodingMatchAt (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (trace : List Entry) (L : LeafAddr) : Prop :=
  ∃ message counter pad answer, Extract.msgFits L.lay message ∧ (encRow L message counter pad, answer) ∈ trace ∧
    referenceInput answers messages L ≠ some (encRow L message counter pad) ∧
    NotSearched answers messages L (encRow L message counter pad) ∧
    WCT9.encodingCanDecode L.lay answer (referenceDigits answers messages L)

def MarkerAt (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (trace : List Entry) (a : ChainAddr) : Prop :=
  ∃ message counter pad answer digits, Extract.msgFits a.key.lay message ∧
    (encRow a.key message counter pad, answer) ∈ trace ∧
    referenceInput answers messages a.key ≠ some (encRow a.key message counter pad) ∧
    WCT9.encodingCanDecode a.key.lay answer digits ∧
    digits.getD a.chain 0 + 1 = (referenceDigits answers messages a.key).getD a.chain 0 ∧
    ∀ i, i ≠ a.chain → (referenceDigits answers messages a.key).getD i 0 ≤ digits.getD i 0

def OtherChainRow (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg) (input : HashInput) : Prop :=
  ∃ (a : ChainAddr) (step : Nat), Extract.posOf input =
      some (.chain a.key.lay a.key.tree a.key.leaf a.chain step) ∧
    ((∀ value, input ≠ chainRowW a step value) ∨ depth answers messages a ≤ step)

def StructuralClass (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (input : HashInput) (position : Extract.Pos) : Prop :=
  match position with
  | .chain _ _ _ _ _ => OtherChainRow answers messages input
  | _ => True
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
end
-- ==== merged from T3_Secc_WotsMaskChain ====
section

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open Mask
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace Mask
theorem eval_chain_one (T : Answers) (lay : Layer) (tree leaf i s : Nat) (v : Digest) :
    evalWithAnswerFn T (chain lay tree leaf i s 1 v) =
      (T (.inl (.inr (chainInput lay tree leaf i s v)))).extractLsb' 0 128 := by
  rw [← pad64_chainInput]
  rfl
variable (answers : Answers) (a : ChainAddr)
end Mask
namespace Mask
variable (answers : Answers) (a : ChainAddr)
end Mask
end SigGolfCandidate.T3.Security.Wots
end
-- ==== merged from T3_Secc_WotsMask ====
section

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open Mask
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace Mask
variable (answers : Answers) (a : ChainAddr)
end Mask
namespace Mask
variable (answers : Answers) (a : ChainAddr)
theorem eval_buildLeaf_sig (T : Answers) {lay : Layer} (hlay : lay ≠ 0) (tree leaf : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) :
    evalWithAnswerFn T (buildLeaf lay tree leaf digits true) =
      (0, (List.range (chainCount lay)).map (leafValue T lay tree leaf digits)) := by
  have h2 := Correctness.eval_buildLeaf_values T hlay tree leaf digits hvalid true
  have h1 : (evalWithAnswerFn T (buildLeaf lay tree leaf digits true)).1 = 0 := by
    rw [Correctness.buildLeaf_eq]
    simp only [evalWithAnswerFn_bind, ↓reduceIte, evalWithAnswerFn_pure]
  exact Prod.ext h1 h2
def routeLeaf (index : Nat) (lay : Layer) : LeafAddr := ⟨lay, (route index lay).2, (route index lay).1⟩
theorem route_tree_succ (index m : Nat) (hm : m < 3) :
    (route index (Fin.ofNat 4 (m + 1))).2 =
      (route index (Fin.ofNat 4 m)).2 * 2 ^ height (Fin.ofNat 4 m) + (route index (Fin.ofNat 4 m)).1 := by
  interval_cases m
  · change index / 2 ^ (12 + 7) = index / 2 ^ (19 + 12) * 2 ^ 12 + index / 2 ^ 19 % 2 ^ 12
    simp only [Nat.reducePow, Nat.reduceAdd]; omega
  · change index / 2 ^ (6 + 6) = index / 2 ^ (12 + 7) * 2 ^ 7 + index / 2 ^ 12 % 2 ^ 7
    simp only [Nat.reducePow, Nat.reduceAdd]; omega
  · change index / 2 ^ (0 + 6) = index / 2 ^ (6 + 6) * 2 ^ 6 + index / 2 ^ 6 % 2 ^ 6
    simp only [Nat.reducePow, Nat.reduceAdd]; omega
theorem route_top_index (index : Nat) : (route index 3).2 * 2 ^ height 3 + (route index 3).1 = index := by
  change index / 2 ^ (0 + 6) * 2 ^ 6 + index / 2 ^ 0 % 2 ^ 6 = index
  simp only [Nat.reducePow, Nat.reduceAdd]; omega
theorem route_tree_lt (index : Nat) (hindex : index < 2 ^ 31) (lay : Layer) : (route index lay).2 < 2 ^ 40 := by
  have : (route index lay).2 ≤ index := Nat.div_le_self _ _
  have : (2 : Nat) ^ 31 < 2 ^ 40 := by decide
  omega
theorem route_leaf_lt (index : Nat) (lay : Layer) : (route index lay).1 < 2 ^ 32 := by
  have h := route_leaf_bound index lay
  have : 2 ^ height lay ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by fin_cases lay <;> decide)
  omega
end Mask
end SigGolfCandidate.T3.Security.Wots
end
-- ==== merged from T3_Secc_WotsMaskCharge ====
section

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open Mask
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace Mask
theorem queried_length_bind (T : Answers) {α β : Type} (p : M α) (f : α → M β) :
    (SourceReplay.queried T (p >>= f)).length =
      (SourceReplay.queried T p).length + (SourceReplay.queried T (f (evalWithAnswerFn T p))).length := by
  rw [SourceReplay.queried_bind, List.length_append]
theorem queried_length_pure (T : Answers) {α : Type} (x : α) :
    (SourceReplay.queried T (pure x : M α)).length = 0 := rfl
theorem queried_length_shortHash (T : Answers) (input : HashInput) :
    (SourceReplay.queried T (shortHash input)).length = 1 := rfl
theorem queried_length_projHash (T : Answers) (high : Bool) (input : HashInput) :
    (SourceReplay.queried T (projHash high input)).length = 1 := rfl
theorem queried_length_privatePair (T : Answers) (tag lay tree position index : Nat) :
    (SourceReplay.queried T (privatePair tag lay tree position index)).length = 1 := rfl
theorem queried_length_foldlM (T : Answers) {β γ : Type} (l : List β) (f : γ → β → M γ) (c : β → Nat)
    (hf : ∀ x ∈ l, ∀ s, (SourceReplay.queried T (f s x)).length = c x) :
    ∀ init, (SourceReplay.queried T (l.foldlM f init)).length = (l.map c).sum := by
  induction l with
  | nil => intro init; rfl
  | cons x xs ih =>
      intro init
      rw [List.foldlM_cons, queried_length_bind, hf x List.mem_cons_self,
        ih (fun y hy s => hf y (List.mem_cons_of_mem x hy) s), List.map_cons, List.sum_cons]
theorem queried_length_mapM (T : Answers) {α β : Type} (l : List α) (f : α → M β) (c : α → Nat)
    (hf : ∀ x ∈ l, (SourceReplay.queried T (f x)).length = c x) :
    (SourceReplay.queried T (l.mapM f)).length = (l.map c).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      rw [List.mapM_cons, queried_length_bind, queried_length_bind, queried_length_pure,
        hf x List.mem_cons_self, ih (fun y hy => hf y (List.mem_cons_of_mem x hy)), List.map_cons, List.sum_cons,
        Nat.add_zero]
theorem sum_map_one {β : Type} (l : List β) : (l.map fun _ => 1).sum = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih => rw [List.map_cons, List.sum_cons, ih, List.length_cons]; omega
theorem queried_length_chain (T : Answers) (lay : Layer) (tree leaf i start count : Nat) (v : Digest) :
    (SourceReplay.queried T (chain lay tree leaf i start count v)).length = count := by
  unfold chain
  rw [queried_length_foldlM T _ _ (fun _ => 1) (fun _ _ _ => queried_length_shortHash _ _), sum_map_one,
    List.length_range']
theorem queried_length_topChain (T : Answers) (leaf i start count : Nat) (v : Digest) :
    (SourceReplay.queried T (topChain leaf i start count v)).length = count := by
  unfold topChain
  rw [queried_length_foldlM T _ _ (fun _ => 1) (fun _ _ _ => queried_length_projHash _ _ _), sum_map_one,
    List.length_range']
def halfCount (lay : Layer) (digits : List Nat) (signatureOnly : Bool) (i : Nat) : Nat :=
  if chainCount lay ≤ i then 0
  else digits.getD i 0 + (if signatureOnly then 0 else maxDigit lay i - digits.getD i 0)
def leafCount (lay : Layer) (digits : List Nat) (signatureOnly : Bool) : Nat :=
  ((List.range ((chainCount lay + 1) / 2)).map fun pair =>
      1 + ((List.range 2).map fun half => halfCount lay digits signatureOnly (2 * pair + half)).sum).sum +
    (if signatureOnly then 0 else 1)
theorem queried_length_leafHalf (T : Answers) (lay : Layer) (tree leaf : Nat) (digits : List Nat)
    (signatureOnly : Bool) (pair : Nat) (seeds : Digest × Digest) (rows : List Digest × List Digest) (half : Nat) :
    (SourceReplay.queried T (Correctness.leafHalf lay tree leaf digits signatureOnly pair seeds rows half)).length =
      halfCount lay digits signatureOnly (2 * pair + half) := by
  unfold Correctness.leafHalf halfCount
  by_cases hi : chainCount lay ≤ 2 * pair + half
  · simp only [hi, ↓reduceIte]
    rfl
  · simp only [hi, ↓reduceIte]
    rw [queried_length_bind, queried_length_chain]
    cases signatureOnly
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [queried_length_bind, queried_length_chain, queried_length_pure, Nat.add_zero]
    · simp only [↓reduceIte]
      rw [queried_length_pure]
theorem queried_length_leafRows (T : Answers) (lay : Layer) (tree leaf : Nat) (digits : List Nat)
    (signatureOnly : Bool) :
    (SourceReplay.queried T (Correctness.leafRows lay tree leaf digits signatureOnly)).length =
      ((List.range ((chainCount lay + 1) / 2)).map fun pair =>
        1 + ((List.range 2).map fun half => halfCount lay digits signatureOnly (2 * pair + half)).sum).sum := by
  unfold Correctness.leafRows
  refine queried_length_foldlM T _ _ _ (fun pair _ rows => ?_) _
  rw [queried_length_bind, queried_length_privatePair,
    queried_length_foldlM T _ _ _ (fun half _ s => queried_length_leafHalf T lay tree leaf digits signatureOnly
      pair _ s half)]
theorem queried_length_buildLeaf (T : Answers) (lay : Layer) (tree leaf : Nat) (digits : List Nat)
    (signatureOnly : Bool) :
    (SourceReplay.queried T (buildLeaf lay tree leaf digits signatureOnly)).length =
      leafCount lay digits signatureOnly := by
  rw [Correctness.buildLeaf_eq, queried_length_bind, queried_length_leafRows]
  unfold leafCount
  cases signatureOnly
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [queried_length_bind, queried_length_pure]
    rfl
  · simp only [↓reduceIte]
    rfl
def treeRowsCount (lay : Layer) (selected : Nat) (digits : List Nat) : Nat :=
  ((List.range (2 ^ height lay)).map fun leaf => leafCount lay (if leaf = selected then digits else []) false).sum
theorem queried_length_treeRows (T : Answers) (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    (SourceReplay.queried T (Correctness.treeRows lay tree selected digits)).length =
      treeRowsCount lay selected digits := by
  unfold Correctness.treeRows
  refine queried_length_foldlM T _ _ _ (fun leaf _ rows => ?_) _
  rw [queried_length_bind, queried_length_buildLeaf]
  rfl
def topPathCount : Nat := ((List.range 12).map fun _ => 1).sum
theorem queried_length_topPath (T : Answers) (cache : Cache) (leaf : Nat) :
    (SourceReplay.queried T (topPath cache leaf)).length = topPathCount := by
  unfold topPath topPathCount
  exact queried_length_mapM T _ _ (fun _ => 1) (fun level _ => by
    unfold mask pairedMask
    simp only [queried_length_bind, queried_length_privatePair, queried_length_pure])
/-! ### Top leaves (campaign T8D: family seeds, `buildLeafTop`) -/
def topChainCount (digits : List Nat) (signatureOnly : Bool) (i : Nat) : Nat :=
  digits.getD i 0 + (if signatureOnly then 0 else maxDigit 0 i - digits.getD i 0)
def topLeafCountC (digits : List Nat) (signatureOnly : Bool) : Nat :=
  ((List.range (chainCount 0)).map (topChainCount digits signatureOnly)).sum + (if signatureOnly then 0 else 1)
def topLeafCount (digits : List Nat) (signatureOnly : Bool) : Nat :=
  topCoefPairs + topLeafCountC digits signatureOnly
theorem queried_length_topPairsFrom (T : Answers) (first start : Nat) (init : List Digest) :
    (SourceReplay.queried T (topPairsFrom first start init)).length = topCoefPairs - start := by
  unfold topPairsFrom
  rw [queried_length_foldlM T _ _ (fun _ => 1) (fun j _ acc => by
    unfold topSeedPair
    rw [queried_length_bind, queried_length_privatePair, queried_length_pure]), sum_map_one, List.length_range']
theorem queried_length_topCoefs (T : Answers) (leaf : Nat) :
    (SourceReplay.queried T (topCoefs leaf)).length = topCoefPairs := by
  unfold topCoefs
  rw [queried_length_bind, queried_length_topPairsFrom, queried_length_pure]
  rfl
theorem queried_length_topLeafStep (T : Answers) (leaf : Nat) (digits : List Nat) (signatureOnly : Bool)
    (coefs : List Digest) (state : List Digest × List Digest) (i : Nat) :
    (SourceReplay.queried T (Correctness.topLeafStep leaf digits signatureOnly coefs state i)).length =
      topChainCount digits signatureOnly i := by
  unfold Correctness.topLeafStep topChainCount
  rw [queried_length_bind, queried_length_topChain]
  cases signatureOnly
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [queried_length_bind, queried_length_topChain, queried_length_pure, Nat.add_zero]
  · simp only [↓reduceIte]
    rw [queried_length_pure]
theorem queried_length_buildLeafTopC (T : Answers) (leaf : Nat) (coefs : List Digest) (digits : List Nat)
    (signatureOnly : Bool) :
    (SourceReplay.queried T (buildLeafTopC leaf coefs digits signatureOnly)).length =
      topLeafCountC digits signatureOnly := by
  rw [Correctness.buildLeafTopC_eq, queried_length_bind,
    queried_length_foldlM T _ _ (topChainCount digits signatureOnly)
      (fun i _ s => queried_length_topLeafStep T leaf digits signatureOnly _ s i)]
  unfold topLeafCountC
  cases signatureOnly
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [queried_length_bind, queried_length_pure, leafHash, queried_length_projHash]
  · simp only [↓reduceIte]
    rw [queried_length_pure]
theorem queried_length_buildLeafTop (T : Answers) (leaf : Nat) (digits : List Nat) (signatureOnly : Bool) :
    (SourceReplay.queried T (buildLeafTop leaf digits signatureOnly)).length = topLeafCount digits signatureOnly := by
  unfold buildLeafTop
  rw [queried_length_bind, queried_length_topCoefs, queried_length_buildLeafTopC]
  rfl
theorem queried_length_signTop (T : Answers) (cache : Cache) (leaf : Nat) (digits : List Nat) :
    (SourceReplay.queried T (signTop cache leaf digits)).length = topLeafCount digits true + topPathCount := by
  unfold signTop
  simp only [queried_length_bind, queried_length_buildLeafTop, queried_length_topPath, queried_length_pure,
    Nat.add_zero]
theorem queried_length_buildLevel (T : Answers) (tag lay tree h level : Nat) (nodes : List Digest) :
    (SourceReplay.queried T (buildLevel tag lay tree h level nodes)).length = nodes.length / 2 := by
  unfold buildLevel
  rw [queried_length_mapM T _ _ (fun _ => 1) (fun i _ => by unfold nodeHash; exact queried_length_projHash _ _ _),
    sum_map_one, List.length_range]
theorem getD_length_of_map {xs ys : List (List Digest)} (h : xs.map List.length = ys.map List.length) (i : Nat) :
    (xs.getD i []).length = (ys.getD i []).length := by
  have := congrArg (fun l : List Nat => l.getD i 0) h
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map] at this ⊢
  cases hx : xs[i]? <;> cases hy : ys[i]? <;> simp_all
/-- The query count of `buildLevels` only depends on the length of its leaves. -/
theorem queried_length_buildLevels_congr (T T' : Answers) (tag lay tree h : Nat) (leaves leaves' : List Digest)
    (hlen : leaves.length = leaves'.length) :
    (SourceReplay.queried T (buildLevels tag lay tree h leaves)).length =
      (SourceReplay.queried T' (buildLevels tag lay tree h leaves')).length := by
  unfold buildLevels
  suffices H : ∀ (ls : List Nat) (s s' : List (List Digest)), s.map List.length = s'.map List.length →
      (SourceReplay.queried T (ls.foldlM (fun levels level => do
        let nodes ← buildLevel tag lay tree h level (levels.getD (level - 1) [])
        pure (levels ++ [nodes])) s)).length =
      (SourceReplay.queried T' (ls.foldlM (fun levels level => do
        let nodes ← buildLevel tag lay tree h level (levels.getD (level - 1) [])
        pure (levels ++ [nodes])) s')).length from H _ _ _ (by simp [hlen])
  intro ls
  induction ls with
  | nil => intro s s' _; rfl
  | cons level ls ih =>
      intro s s' hs
      simp only [List.foldlM_cons, queried_length_bind, queried_length_buildLevel, queried_length_pure,
        Nat.add_zero, getD_length_of_map hs]
      congr 1
      apply ih
      simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, List.map_append, List.map_cons, List.map_nil,
        Correctness.eval_buildLevel_length, hs, getD_length_of_map hs]
/-- img-v6 keygen top leaves: the family coefficients (`topCoefsK` at the first leaf of each family) and the leaf. -/
def topStepCount (leaf : Nat) : Nat :=
  (if leaf % 4 = 0 then topCoefPairs - leaf / 4 % 2 else 0) + topLeafCountC [] false
theorem queried_length_topTreeStep (T : Answers) (st : List Digest × List Digest × Digest) (leaf : Nat) :
    (SourceReplay.queried T (topTreeStep st leaf)).length = topStepCount leaf := by
  unfold topTreeStep topFamilyCoefs topStepCount
  rw [queried_length_bind, queried_length_bind, queried_length_buildLeafTopC, queried_length_pure, Nat.add_zero]
  split
  · unfold topCoefsK
    rw [queried_length_bind, queried_length_topPairsFrom, queried_length_pure, Nat.add_zero]
  · rw [queried_length_pure]
theorem queried_length_topLeaves (T : Answers) :
    (SourceReplay.queried T ((List.range (2 ^ height 0)).foldlM topTreeStep ([], [], 0))).length =
      ((List.range (2 ^ height 0)).map topStepCount).sum :=
  queried_length_foldlM T _ _ topStepCount (fun leaf _ st => queried_length_topTreeStep T st leaf) _
/-- Top node (nonce trial) queries carry the node tweak in bytes `16..32`: they are no chain row. -/
theorem respects_topNodeHashN (a : ChainAddr) (heap n : Nat) (left right : Digest) :
    Respects (Untouched a) (topNodeHashN heap n left right) := by
  unfold topNodeHashN
  apply Respects.projHash
  refine untouched_of_hdr a _ (nodeTweak 3 0 0 heap) ?_
    (fun _ _ _ _ _ => Ne.symm (chainHeader_ne_nodeTweak _ _ _ _ _ _ _ _ _))
  rw [Extract.hdrBlock_pad64 _ (by simp [topNodeInput, nonceBytes, bytesLE_length])]
  unfold topNodeInput
  rw [List.append_assoc]
  exact Extract.hdrBlock_prefix _ _ _
theorem respects_topNonceSearch (a : ChainAddr) (h heap : Nat) (left right : Digest) :
    ∀ fuel n, Respects (Untouched a) (topNonceSearch h heap left right fuel n)
  | 0, n => by
      unfold topNonceSearch
      exact Respects.bind (respects_topNodeHashN a _ _ _ _) fun _ => Respects.pure' _
  | fuel + 1, n => by
      unfold topNonceSearch
      refine Respects.bind (respects_topNodeHashN a _ _ _ _) fun _ => ?_
      split
      · exact Respects.pure' _
      · exact respects_topNonceSearch a h heap left right fuel (n + 1)
theorem respects_buildTopLevels (a : ChainAddr) (leaves : List Digest) :
    Respects (Untouched a) (buildTopLevels leaves) := by
  unfold buildTopLevels
  refine Respects.foldlM _ _ (fun level _ levels => Respects.bind ?_ fun _ => Respects.pure' _) _
  unfold buildTopLevel
  refine Respects.mapM _ _ fun i _ => ?_
  split
  · exact respects_nodeHash a _ _ _ _ _ _ (by decide)
  · unfold topNodeAt
    exact Respects.map _ (respects_topNonceSearch a _ _ _ _ _ _)
/-- The leaves of the top tree are the first level of `buildTopLevels`. -/
theorem eval_buildTopLevels_head (T : Answers) (leaves : List Digest) :
    (evalWithAnswerFn T (buildTopLevels leaves)).getD 0 [] = leaves := by
  unfold buildTopLevels
  suffices H : ∀ (ls : List Nat) (s : List (List Digest)), s ≠ [] → s.getD 0 [] = leaves →
      (evalWithAnswerFn T (ls.foldlM (fun levels level => do
        let nodes ← buildTopLevel level (levels.getD (level - 1) [])
        pure (levels ++ [nodes])) s)).getD 0 [] = leaves from H _ _ (List.cons_ne_nil _ _) rfl
  intro ls
  induction ls with
  | nil => intro s _ hs; exact hs
  | cons level ls ih =>
      intro s hne hs
      rw [List.foldlM_cons, evalWithAnswerFn_bind]
      simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
      cases s with
      | nil => exact absurd rfl hne
      | cons x xs => exact ih _ (by simp) (by simpa using hs)
/-- img-v6: the keygen top tree's query count depends on the tables only through its nonce trials, i.e. through
the answers at top node queries. Two tables that agree on every query some `S` contains (with `S` respected by
the node levels) and produce the same top tree issue the same number of queries. -/
theorem queried_length_buildTopTree_of {S : Spec.Domain → Prop} (hS : ∀ leaves, Respects S (buildTopLevels leaves))
    (T T' : Answers) (hT : ∀ q, S q → T q = T' q)
    (hb : evalWithAnswerFn T buildTopTree = evalWithAnswerFn T' buildTopTree) :
    (SourceReplay.queried T buildTopTree).length = (SourceReplay.queried T' buildTopTree).length := by
  have hroots : (evalWithAnswerFn T ((List.range (2 ^ height 0)).foldlM topTreeStep ([], [], 0))).1 =
      (evalWithAnswerFn T' ((List.range (2 ^ height 0)).foldlM topTreeStep ([], [], 0))).1 := by
    have h := congrArg (fun l : List (List Digest) => l.getD 0 []) hb
    simp only [buildTopTree, evalWithAnswerFn_bind, eval_buildTopLevels_head] at h
    exact h
  unfold buildTopTree
  rw [queried_length_bind, queried_length_bind, queried_length_topLeaves, queried_length_topLeaves, hroots,
    (hS _).queried_eq hT]
variable (answers : Answers) (a : ChainAddr)
theorem count_bind_of {T T' : Answers} {α β : Type} {p : M α} {f : α → M β}
    (hp : evalWithAnswerFn T' p = evalWithAnswerFn T p)
    (hcp : (SourceReplay.queried T' p).length = (SourceReplay.queried T p).length)
    (hf : (SourceReplay.queried T' (f (evalWithAnswerFn T p))).length =
      (SourceReplay.queried T (f (evalWithAnswerFn T p))).length) :
    (SourceReplay.queried T' (p >>= f)).length = (SourceReplay.queried T (p >>= f)).length := by
  rw [queried_length_bind, queried_length_bind, hp, hcp, hf]
def maskCount : Nat := ((List.range' 0 12).map fun level => ((List.range (2 ^ (11 - level))).map fun _ => 1).sum).sum
theorem queried_length_maskedLevel (T : Answers) (nodes : List Digest) (level : Nat) :
    (SourceReplay.queried T (maskedLevel nodes level)).length =
      ((List.range (2 ^ (11-level))).map fun _ => 1).sum := by
  unfold maskedLevel pairedMask
  rw [queried_length_bind, queried_length_pure, Nat.add_zero]
  exact queried_length_mapM T _ _ (fun _ => 1) (fun pair _ => by
    simp only [queried_length_bind, queried_length_privatePair, queried_length_pure])
theorem queried_length_cachePayload (T : Answers) (builder : M (List (List Digest))) :
    (SourceReplay.queried T (Correctness.cachePayloadProgram builder)).length =
      (SourceReplay.queried T builder).length + maskCount := by
  unfold Correctness.cachePayloadProgram
  rw [queried_length_bind]
  generalize evalWithAnswerFn T builder = levels
  rw [queried_length_bind, queried_length_pure, Nat.add_zero,
    queried_length_mapM _ _ _ (fun level => ((List.range (2 ^ (11 - level))).map fun _ => 1).sum)
      (fun level _ => queried_length_maskedLevel _ _ _)]
  rfl
/-- Keygen's payload: same query count for two tables that agree on `S` and build the same top tree (img-v6:
nonce trials). -/
theorem queried_length_keygenPayload_congr {S : Spec.Domain → Prop} (hS : ∀ leaves, Respects S (buildTopLevels leaves))
    (T T' : Answers) (hT : ∀ q, S q → T q = T' q)
    (hb : evalWithAnswerFn T buildTopTree = evalWithAnswerFn T' buildTopTree) :
    (SourceReplay.queried T keygenPayload).length = (SourceReplay.queried T' keygenPayload).length := by
  rw [Correctness.keygenPayload_eq, queried_length_cachePayload, queried_length_cachePayload,
    queried_length_buildTopTree_of hS T T' hT hb]
end Mask
namespace Mask
variable (answers : Answers) (a : ChainAddr)
end Mask
end SigGolfCandidate.T3.Security.Wots
end
-- ==== merged from T3_Secc_WotsMaskRef ====
section

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3M
open SigGolfCandidate.T3.Correctness (Answers)
end SigGolfCandidate.T3.Security.Wots
end
-- ==== merged from T3_Secc_CanonGraphHonest ====
section

namespace SigGolfCandidate.T3.Security.CanonGraph
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers treeValue builtTree leafSeed leafEnd leafRoot leafValue)
open ChainGraph (Address Point Seeds)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] SigGolfCandidate.T3.buildFts SigGolfCandidate.T3.buildTree SigGolfCandidate.T3.buildLeaf
  SigGolfCandidate.T3.buildLevels Correctness.builtTree Correctness.ftsRows
def ftsSecretNat (answers : Answers) (index coord leaf : Nat) : Digest :=
  let pair := evalWithAnswerFn answers (privatePair 8 coord index 0 (leaf / 2))
  if leaf % 2 = 0 then pair.1 else pair.2
theorem eval_ftsRows_secrets (answers : Answers) (index coord : Nat) :
    (evalWithAnswerFn answers (Correctness.ftsRows index coord)).2.length = 2048 ∧
      ∀ leaf, leaf < 2048 →
        (evalWithAnswerFn answers (Correctness.ftsRows index coord)).2.getD leaf 0 =
          ftsSecretNat answers index coord leaf := by
  unfold Correctness.ftsRows
  refine Correctness.eval_foldlM_range_inv answers 1024 _
    (fun pairs (rows : List Digest × List Digest) => rows.2.length = 2 * pairs ∧
      ∀ leaf, leaf < 2 * pairs → rows.2.getD leaf 0 = ftsSecretNat answers index coord leaf)
    ([], []) ⟨rfl, fun leaf h => by omega⟩ (fun pair _ rows hrows => ?_)
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  obtain ⟨hlen, hget⟩ := hrows
  refine ⟨by simp [hlen]; omega, ?_⟩
  intro leaf hleaf
  by_cases hold : leaf < 2 * pair
  · rw [List.getD_append _ _ _ _ (by rw [hlen]; exact hold)]
    exact hget leaf hold
  · rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen]
    have he : leaf = 2 * pair ∨ leaf = 2 * pair + 1 := by omega
    rcases he with rfl | rfl
    · simp only [Nat.sub_self, List.getD_cons_zero, ftsSecretNat]
      rw [show 2 * pair / 2 = pair by omega, if_pos (by omega)]
    · simp only [show 2 * pair + 1 - 2 * pair = 1 by omega, ftsSecretNat]
      rw [show (2 * pair + 1) / 2 = pair by omega, if_neg (by omega)]
      rfl
theorem ftsSecret_nat (answers : Answers) (index coord leaf : Nat) (hleaf : leaf < 2048) :
    Extract.ftsSecret answers index coord leaf = ftsSecretNat answers index coord leaf := by
  unfold Extract.ftsSecret
  rw [Correctness.buildFts_eq]
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  exact (eval_ftsRows_secrets answers index coord).2 leaf hleaf
theorem ftsSecret_eq (answers : Answers) (f : FtsLeafPos) :
    Extract.ftsSecret answers f.index.val f.coord.val f.leaf.val = ftsOf (secretsOf answers) f :=
  ftsSecret_nat answers _ _ _ f.leaf.isLt
section Honest
variable {answers : Answers} {labels : Labels}
theorem chainValue_eq (h : Agrees answers labels) (a : Address) (step : Nat) (hstep : step ≤ 7) :
    honestChainValue answers a.layer a.tree.val a.leaf.val a.chain.val
      (leafSeed answers a.layer a.tree.val a.leaf.val a.chain.val) step =
      ChainGraph.value (seedsOf (secretsOf answers)) (chainLabels labels) a step :=
  ChainGraph.source_prefix answers (chainLabels labels) (agrees_chain h) a step hstep
/-- Witness stack: lower layers only (dead legacy route, not in the constant cone of `certificate_ready`; the top
endpoint is now `topChain`, which this F-chain graph does not model). -/
theorem leafEnd_eq (h : Agrees answers labels) (L : LeafPos) (hl : L.lay ≠ 0) (i : Nat) (hi : i < 58) :
    leafEnd answers L.lay L.tree.val L.leaf.val i = endLabel (secretsOf answers) labels L i := by
  have hval : (fin58 i).val = i := Nat.mod_eq_of_lt hi
  have hx := ChainGraph.source_endpoint answers (chainLabels labels) (agrees_chain h) ⟨L.lay, L.tree, L.leaf, fin58 i⟩ hl
  simp only [hval] at hx
  exact hx
theorem leafEnds_eq (h : Agrees answers labels) (L : LeafPos) (hl : L.lay ≠ 0) :
    (List.range (chainCount L.lay)).map (leafEnd answers L.lay L.tree.val L.leaf.val) =
      (List.range (chainCount L.lay)).map (endLabel (secretsOf answers) labels L) := by
  apply List.map_congr_left
  intro i hi
  exact leafEnd_eq h L hl i (lt_of_lt_of_le (List.mem_range.mp hi) (chainCount_bound L.lay))
theorem treeNodeAt_some (lay : Layer) (tree : Fin (2^31)) (level c : Nat) (hlevel : level < height lay)
    (hc : c < 2 ^ (height lay - level - 1)) :
    ∃ n : TreeNode, treeNodeAt lay tree level c = some n ∧ n.1.lay = lay ∧ n.1.tree = tree ∧
      n.1.level.val = level ∧ n.1.idx.val = c := by
  unfold treeNodeAt
  rw [dif_pos ⟨hlevel, hc⟩]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
theorem ftsNodeAt_some (index : Fin (2^31)) (coord : Fin 7) (level c : Nat) (hlevel : level < 11)
    (hc : c < 2 ^ (11 - level - 1)) :
    ∃ n : FtsNodePos, ftsNodeAt index coord level c = some n ∧ n.1.index = index ∧ n.1.coord = coord ∧
      n.1.level.val = level ∧ n.1.idx.val = c := by
  unfold ftsNodeAt
  rw [dif_pos ⟨hlevel, hc⟩]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
end Honest
end SigGolfCandidate.T3.Security.CanonGraph
end
-- ==== merged from SphincsSecurity_Proof_Base_FirstSuccessTable ====
section

namespace SphincsSecurity.Concrete.FirstSuccessTable
open _root_.OracleComp ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {Answer Value : Type}
def select (decode : Answer → Option Value) : {n : Nat} → (Fin n → Answer) → Option (Fin n × Value)
  | 0, _ => none
  | n + 1, table =>
      match decode (table 0) with
      | some value => some (0, value)
      | none => (select decode (fun i : Fin n => table i.succ)).map (fun result => (result.1.succ, result.2))
theorem select_none_iff (decode : Answer → Option Value) {n : Nat} (table : Fin n → Answer) :
    select decode table = none ↔ ∀ i, decode (table i) = none := by
  induction n with
  | zero => simp [select]
  | succ n ih =>
      rw [select, Fin.forall_fin_succ]
      cases hzero : decode (table 0) <;> simp [ih]
theorem select_some_iff (decode : Answer → Option Value) {n : Nat} (table : Fin n → Answer)
    (index : Fin n) (value : Value) :
    select decode table = some (index, value) ↔
      decode (table index) = some value ∧ ∀ i, i < index → decode (table i) = none := by
  induction n with
  | zero => exact Fin.elim0 index
  | succ n ih =>
      refine Fin.cases ?_ (fun index => ?_) index
      · rw [select]
        cases hzero : decode (table 0) with
        | none =>
            simp only [Option.map_eq_some_iff, Prod.mk.injEq]
            constructor
            · rintro ⟨⟨i, result⟩, _, hi, _⟩
              exact (Fin.succ_ne_zero i hi).elim
            · simp
        | some result => simp
      · rw [select]
        cases hzero : decode (table 0) with
        | none =>
            simp only [Option.map_eq_some_iff, Prod.mk.injEq, Fin.succ_inj]
            constructor
            · rintro ⟨⟨i, result⟩, hselected, hi, hv⟩
              dsimp only at hi hv
              subst i
              subst result
              obtain ⟨hvalue, hbefore⟩ := (ih _ _).mp hselected
              refine ⟨hvalue, ?_⟩
              intro i
              refine Fin.cases (fun _ => hzero) (fun i hi => hbefore i (by simpa using hi)) i
            · rintro ⟨hvalue, hbefore⟩
              refine ⟨(index, value), (ih _ _).mpr ⟨hvalue, ?_⟩, rfl, rfl⟩
              intro i hi
              exact hbefore i.succ (by simpa using hi)
        | some result =>
            constructor
            · intro h
              have hindex := congrArg (fun result => result.map (fun pair => pair.1.val)) h
              simp at hindex
            · rintro ⟨_, hbefore⟩
              have h := hbefore 0 (by simp)
              simp [hzero] at h
variable [Fintype Answer] [DecidableEq Answer]
noncomputable def invalid (decode : Answer → Option Value) : Finset Answer :=
  Finset.univ.filter (fun answer => decode answer = none)
noncomputable def fiber (decode : Answer → Option Value) (value : Value) : Finset Answer :=
  Finset.univ.filter (fun answer => decode answer = some value)
omit [DecidableEq Answer] in
@[simp] theorem mem_invalid (decode : Answer → Option Value) (answer : Answer) :
    answer ∈ invalid decode ↔ decode answer = none := by simp [invalid]
omit [DecidableEq Answer] in
@[simp] theorem mem_fiber (decode : Answer → Option Value) (value : Value) (answer : Answer) :
    answer ∈ fiber decode value ↔ decode answer = some value := by simp [fiber]
noncomputable def allowed (decode : Answer → Option Value) {n : Nat} (index : Fin n) (value : Value)
    (coordinate : Fin n) : Finset Answer :=
  if coordinate < index then invalid decode else if coordinate = index then fiber decode value else Finset.univ
omit [DecidableEq Answer] in
theorem select_some_iff_allowed (decode : Answer → Option Value) {n : Nat} (table : Fin n → Answer)
    (index : Fin n) (value : Value) :
    select decode table = some (index, value) ↔
      ∀ coordinate, table coordinate ∈ allowed decode index value coordinate := by
  rw [select_some_iff]
  constructor
  · rintro ⟨hvalue, hbefore⟩ coordinate
    unfold allowed
    split_ifs with hlt heq
    · exact (mem_invalid _ _).mpr (hbefore coordinate hlt)
    · subst coordinate
      exact (mem_fiber _ _ _).mpr hvalue
    · exact Finset.mem_univ _
  · intro h
    refine ⟨?_, ?_⟩
    · simpa [allowed] using h index
    · intro coordinate hlt
      simpa [allowed, hlt] using h coordinate
noncomputable def full (n : Nat) [Nonempty Answer] : PMF (Fin n → Answer) :=
  uniformTable (fun _ => Finset.univ) (fun _ => Finset.univ_nonempty)
omit [DecidableEq Answer] in
theorem full_eq_uniform (n : Nat) [Nonempty Answer] :
    full (Answer := Answer) n = PMF.uniformOfFintype (Fin n → Answer) := by
  unfold full uniformTable PMF.uniformOfFintype
  congr 1
noncomputable def constrained [Nonempty Answer] {n : Nat} (rows : Fin n → Finset Answer) : PMF (Fin n → Answer) :=
  if hrows : ∀ coordinate, (rows coordinate).Nonempty then uniformTable rows hrows else full n
theorem full_restrict_mass [Nonempty Answer] {n : Nat} (rows : Fin n → Finset Answer) (table : Fin n → Answer) :
    (if ∀ coordinate, table coordinate ∈ rows coordinate then full n table else 0) =
      ((∏ coordinate, (rows coordinate).card : Nat) : ENNReal) /
        ((∏ _coordinate : Fin n, Fintype.card Answer : Nat) : ENNReal) * constrained rows table := by
  by_cases hrows : ∀ coordinate, (rows coordinate).Nonempty
  · have h := uniformTable_restrict (fun _ : Fin n => Finset.univ) rows
      (fun _ => Finset.univ_nonempty) hrows (fun _ => Finset.subset_univ _) table
    by_cases ht : ∀ coordinate, table coordinate ∈ rows coordinate <;>
      simpa only [full, constrained, dif_pos hrows, Finset.card_univ, ht, if_true, if_false] using h
  · push Not at hrows
    obtain ⟨coordinate, hempty⟩ := hrows
    have hzero : (∏ coordinate, (rows coordinate).card : Nat) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ coordinate) (by rw [hempty, Finset.card_empty])
    have ht : ¬∀ coordinate, table coordinate ∈ rows coordinate := fun h => by
      simpa only [hempty, Finset.notMem_empty] using h coordinate
    simp only [ht, if_false, hzero, Nat.cast_zero, ENNReal.zero_div, zero_mul]
noncomputable def successMass (decode : Answer → Option Value) {n : Nat} (index : Fin n) (value : Value) : ENNReal :=
  ((∏ coordinate, (allowed decode index value coordinate).card : Nat) : ENNReal) /
    ((∏ _coordinate : Fin n, Fintype.card Answer : Nat) : ENNReal)
theorem full_success_mass [Nonempty Answer] (decode : Answer → Option Value) {n : Nat}
    (index : Fin n) (value : Value) (table : Fin n → Answer) :
    (if select decode table = some (index, value) then full n table else 0) =
      successMass decode index value * constrained (allowed decode index value) table := by
  simp only [select_some_iff_allowed]
  exact full_restrict_mass _ table
theorem probEvent_full_success [Nonempty Answer] (decode : Answer → Option Value) {n : Nat}
    (index : Fin n) (value : Value) :
    Pr[fun table => select decode table = some (index, value) | full (Answer := Answer) n] =
      successMass decode index value := by
  simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply,
    full_success_mass decode index value, ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
theorem full_exhaustion_mass [Nonempty Answer] (decode : Answer → Option Value) (n : Nat)
    (table : Fin n → Answer) :
    (if select decode table = none then full n table else 0) =
      ((invalid decode).card / (Fintype.card Answer : ENNReal)) ^ n *
        constrained (fun _ : Fin n => invalid decode) table := by
  have h := full_restrict_mass (fun _ : Fin n => invalid decode) table
  have hmass :
      (((∏ _coordinate : Fin n, (invalid decode).card : Nat) : ENNReal) /
        ((∏ _coordinate : Fin n, Fintype.card Answer : Nat) : ENNReal)) =
          ((invalid decode).card / (Fintype.card Answer : ENNReal)) ^ n := by
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.cast_pow,
      div_eq_mul_inv, ENNReal.inv_pow, mul_pow]
  rw [hmass] at h
  simp only [mem_invalid] at h
  simpa only [select_none_iff] using h
theorem probEvent_full_exhaustion [Nonempty Answer] (decode : Answer → Option Value) (n : Nat) :
    Pr[fun table => select decode table = none | full (Answer := Answer) n] =
      ((invalid decode).card / (Fintype.card Answer : ENNReal)) ^ n := by
  simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply,
    full_exhaustion_mass decode n, ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
noncomputable def selected [Nonempty Answer] (decode : Answer → Option Value) (n : Nat) :
    PMF (Option (Fin n × Value)) := (full n).map (select decode)
noncomputable def afterSelect [Nonempty Answer] (decode : Answer → Option Value) (n : Nat) :
    Option (Fin n × Value) → PMF (Fin n → Answer)
  | none => constrained (fun _ => invalid decode)
  | some (index, value) => constrained (allowed decode index value)
omit [DecidableEq Answer] in
theorem selected_apply [Nonempty Answer] (decode : Answer → Option Value) (n : Nat)
    (result : Option (Fin n × Value)) :
    selected decode n result = Pr[fun table => select decode table = result | full (Answer := Answer) n] := by
  simp only [selected, PMF.map_apply, probEvent_eq_tsum_ite, PMF.probOutput_eq_apply]
  apply tsum_congr
  intro table
  by_cases h : select decode table = result
  · subst result
    simp
  · simp only [h, Ne.symm h, if_false]
theorem selected_mul_afterSelect [Nonempty Answer] (decode : Answer → Option Value) (n : Nat)
    (result : Option (Fin n × Value)) (table : Fin n → Answer) :
    selected decode n result * afterSelect decode n result table =
      if select decode table = result then full n table else 0 := by
  cases result with
  | none =>
      rw [selected_apply, probEvent_full_exhaustion decode n, afterSelect]
      exact (full_exhaustion_mass decode n table).symm
  | some result =>
      obtain ⟨index, value⟩ := result
      rw [selected_apply, probEvent_full_success decode index value, afterSelect]
      exact (full_success_mass decode index value table).symm
end SphincsSecurity.Concrete.FirstSuccessTable
end
-- ==== merged from SphincsSecurity_Proof_Base_FirstSuccessFamily ====
section

namespace SphincsSecurity.Concrete
open _root_.OracleComp ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
namespace FinitePmfProduct
variable {Index Value : Type} [Fintype Index] [DecidableEq Index] [Fintype Value]
noncomputable def law (family : Index → PMF Value) : PMF (Index → Value) :=
  PMF.ofFintype (fun values => ∏ index, family index (values index)) (by
    rw [← Fintype.prod_sum]
    apply Finset.prod_eq_one
    intro index _
    simpa only [tsum_fintype] using PMF.tsum_coe (family index))
theorem apply (family : Index → PMF Value) (values : Index → Value) :
    law family values = ∏ index, family index (values index) := rfl
theorem uniform [Nonempty Value] :
    law (fun _ : Index => PMF.uniformOfFintype Value) = PMF.uniformOfFintype (Index → Value) := by
  apply PMF.ext
  intro values
  simp only [apply, PMF.uniformOfFintype_apply, Finset.prod_const, Finset.card_univ,
    Fintype.card_fun, Nat.cast_pow, ENNReal.inv_pow]
end FinitePmfProduct
namespace FirstSuccessFamily
variable {Index Answer Value : Type} [Fintype Index] [DecidableEq Index]
  [Fintype Answer] [DecidableEq Answer] [Nonempty Answer] [Fintype Value]
def select (decode : Answer → Option Value) (n : Nat) (tables : Index → Fin n → Answer) :
    Index → Option (Fin n × Value) := fun index => FirstSuccessTable.select decode (tables index)
noncomputable def selected (decode : Answer → Option Value) (n : Nat) :
    PMF (Index → Option (Fin n × Value)) :=
  FinitePmfProduct.law (fun _ => FirstSuccessTable.selected decode n)
noncomputable def afterSelect (decode : Answer → Option Value) (n : Nat) (results : Index → Option (Fin n × Value)) :
    PMF (Index → Fin n → Answer) :=
  FinitePmfProduct.law (fun index => FirstSuccessTable.afterSelect decode n (results index))
theorem selected_mul_afterSelect (decode : Answer → Option Value) (n : Nat) (results : Index → Option (Fin n × Value))
    (tables : Index → Fin n → Answer) :
    selected decode n results * afterSelect decode n results tables =
      if select decode n tables = results then PMF.uniformOfFintype (Index → Fin n → Answer) tables else 0 := by
  rw [selected, afterSelect, FinitePmfProduct.apply, FinitePmfProduct.apply, ← Finset.prod_mul_distrib]
  simp only [FirstSuccessTable.selected_mul_afterSelect]
  by_cases h : select decode n tables = results
  · rw [if_pos h]
    have hcoordinate (index : Index) : FirstSuccessTable.select decode (tables index) = results index := congrFun h index
    simp only [hcoordinate, if_true, FirstSuccessTable.full_eq_uniform]
    exact congrFun (congrArg DFunLike.coe (FinitePmfProduct.uniform (Index := Index) (Value := Fin n → Answer))) tables
  · rw [if_neg h]
    have hex : ∃ index, FirstSuccessTable.select decode (tables index) ≠ results index := by
      by_contra! hall
      exact h (funext hall)
    obtain ⟨index, hindex⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ index) (if_neg hindex)
theorem uniform_bind_eq_selected {Result : Type} (decode : Answer → Option Value) (n : Nat)
    (next : (Index → Option (Fin n × Value)) → (Index → Fin n → Answer) → PMF Result) :
    (PMF.uniformOfFintype (Index → Fin n → Answer)).bind (fun tables => next (select decode n tables) tables) =
      (selected decode n).bind (fun results => (afterSelect decode n results).bind (next results)) := by
  apply PMF.ext
  intro output
  simp only [PMF.bind_apply, ← ENNReal.tsum_mul_left, ← mul_assoc, selected_mul_afterSelect,
    ite_mul, zero_mul]
  rw [ENNReal.tsum_comm]
  simp
end FirstSuccessFamily
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Base_UniformTableSplit ====
section

namespace SphincsSecurity.Concrete.UniformTableSplit
open _root_.OracleComp ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {Index Cell Answer : Type}
abbrev Outside (embed : Index → Cell) := {cell : Cell // cell ∉ Set.range embed}
theorem inclusion_not_range {α : Type} {small large : Set α} (hsubset : small ⊆ large)
    (cell : large) (houtside : cell.val ∉ small) : cell ∉ Set.range (Set.inclusion hsubset) := by
  rintro ⟨input, heq⟩
  exact houtside ((congrArg Subtype.val heq) ▸ input.property)
noncomputable def split (embed : Index → Cell) (hinj : Function.Injective embed) :
    (Cell → Answer) ≃ (Index → Answer) × (Outside embed → Answer) :=
  (Equiv.arrowCongr ((Equiv.Set.sumCompl (Set.range embed)).symm.trans
    ((Equiv.ofInjective embed hinj).symm.sumCongr (Equiv.refl (Outside embed)))) (Equiv.refl Answer)).trans
      (Equiv.sumArrowEquivProdArrow _ _ _)
theorem split_fst (embed : Index → Cell) (hinj : Function.Injective embed) (table : Cell → Answer) :
    (split embed hinj table).1 = table ∘ embed := by
  funext index
  simp [split, Equiv.sumArrowEquivProdArrow, Equiv.ofInjective]
theorem split_snd (embed : Index → Cell) (hinj : Function.Injective embed) (table : Cell → Answer) :
    (split embed hinj table).2 = fun cell => table cell.val := by
  funext cell
  simp [split, Equiv.sumArrowEquivProdArrow, Equiv.ofInjective]
  rfl
noncomputable def join (embed : Index → Cell) (hinj : Function.Injective embed)
    (rows : Index → Answer) (outside : Outside embed → Answer) : Cell → Answer :=
  (split embed hinj).symm (rows, outside)
@[simp] theorem join_embed (embed : Index → Cell) (hinj : Function.Injective embed)
    (rows : Index → Answer) (outside : Outside embed → Answer) (index : Index) :
    join embed hinj rows outside (embed index) = rows index := by
  have h := congrArg Prod.fst ((split embed hinj).apply_symm_apply (rows, outside))
  rw [split_fst] at h
  exact congrFun h index
@[simp] theorem join_outside (embed : Index → Cell) (hinj : Function.Injective embed)
    (rows : Index → Answer) (outside : Outside embed → Answer) (cell : Outside embed) :
    join embed hinj rows outside cell.val = outside cell := by
  have h := congrArg Prod.snd ((split embed hinj).apply_symm_apply (rows, outside))
  rw [split_snd] at h
  exact congrFun h cell
@[simp] theorem join_split (embed : Index → Cell) (hinj : Function.Injective embed) (table : Cell → Answer) :
    join embed hinj (table ∘ embed) (fun cell => table cell.val) = table := by
  rw [← split_fst embed hinj table, ← split_snd embed hinj table]
  exact (split embed hinj).symm_apply_apply table
theorem uniform_product {Left Right : Type} [Fintype Left] [Fintype Right] [Nonempty Left] [Nonempty Right] :
    PMF.uniformOfFintype (Left × Right) =
      (PMF.uniformOfFintype Left).bind (fun left => (PMF.uniformOfFintype Right).map (fun right => (left, right))) := by
  classical
  letI : DecidableEq Left := Classical.decEq Left
  letI : DecidableEq Right := Classical.decEq Right
  apply PMF.ext
  rintro ⟨left, right⟩
  have hmap : ∀ a : Left,
      (PMF.uniformOfFintype Right).map (fun b => (a, b)) (left, right) =
        if a = left then PMF.uniformOfFintype Right right else 0 := by
    intro a
    rw [PMF.map_apply]
    by_cases ha : a = left
    · subst a
      rw [if_pos rfl, tsum_eq_single right]
      · rw [if_pos rfl]
      · intro b hb
        exact if_neg (fun h => hb (congrArg Prod.snd h).symm)
    · rw [if_neg ha]
      apply ENNReal.tsum_eq_zero.mpr
      intro b
      exact if_neg (fun h => ha (congrArg Prod.fst h).symm)
  rw [PMF.bind_apply]
  simp only [hmap, mul_ite, mul_zero]
  rw [tsum_eq_single left]
  · simp only [if_true, PMF.uniformOfFintype_apply]
    rw [Fintype.card_prod, Nat.cast_mul, ENNReal.mul_inv (by simp) (by simp)]
  · intro a ha
    exact if_neg ha
variable [Fintype Index] [Fintype Cell] [Fintype Answer] [Nonempty Answer]
  [DecidableEq Index] [DecidableEq Cell]
theorem uniform_join (embed : Index → Cell) (hinj : Function.Injective embed) :
    PMF.uniformOfFintype (Cell → Answer) =
      (PMF.uniformOfFintype (Index → Answer)).bind (fun rows =>
        (PMF.uniformOfFintype (Outside embed → Answer)).map (join embed hinj rows)) := by
  unfold join
  have h := PMF.uniformOfFintype_map_of_bijective (split (Answer := Answer) embed hinj).symm
    (split embed hinj).symm.bijective
  rw [uniform_product, PMF.map_bind] at h
  simpa only [PMF.map_comp, Function.comp_def] using h.symm
theorem uniform_bind_split {Result : Type} (embed : Index → Cell) (hinj : Function.Injective embed)
    (next : (Cell → Answer) → PMF Result) :
    (PMF.uniformOfFintype (Cell → Answer)).bind next =
      (PMF.uniformOfFintype (Index → Answer)).bind (fun rows =>
        (PMF.uniformOfFintype (Outside embed → Answer)).bind (fun outside => next (join embed hinj rows outside))) := by
  conv_lhs => rw [uniform_join embed hinj]
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
end SphincsSecurity.Concrete.UniformTableSplit
end
-- ==== merged from SphincsSecurity_Proof_Base_UniformTableOverwrite ====
section

namespace SphincsSecurity.Concrete.UniformTableSplit
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {Index Cell Answer : Type}
noncomputable def overwrite (embed : Index → Cell) (hinj : Function.Injective embed)
    (rows : Index → Answer) (table : Cell → Answer) : Cell → Answer :=
  join embed hinj rows (fun cell => table cell.val)
theorem overwrite_embed (embed : Index → Cell) (hinj : Function.Injective embed)
    (rows : Index → Answer) (table : Cell → Answer) (index : Index) :
    overwrite embed hinj rows table (embed index) = rows index :=
  join_embed embed hinj rows _ index
theorem overwrite_outside (embed : Index → Cell) (hinj : Function.Injective embed)
    (rows : Index → Answer) (table : Cell → Answer) (cell : Cell) (hcell : cell ∉ Set.range embed) :
    overwrite embed hinj rows table cell = table cell :=
  join_outside embed hinj rows _ ⟨cell, hcell⟩
theorem overwrite_join (embed : Index → Cell) (hinj : Function.Injective embed)
    (rows previous : Index → Answer) (outside : Outside embed → Answer) :
    overwrite embed hinj rows (join embed hinj previous outside) = join embed hinj rows outside := by
  unfold overwrite
  congr 1
  funext cell
  exact join_outside embed hinj previous outside cell
variable [Fintype Index] [Fintype Cell] [Fintype Answer] [Nonempty Answer]
  [DecidableEq Index] [DecidableEq Cell]
theorem uniform_overwrite (embed : Index → Cell) (hinj : Function.Injective embed) (rows : Index → Answer) :
    (PMF.uniformOfFintype (Cell → Answer)).map (overwrite embed hinj rows) =
      (PMF.uniformOfFintype (Outside embed → Answer)).map (join embed hinj rows) := by
  rw [uniform_join embed hinj]
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, overwrite_join, PMF.bind_const]
end SphincsSecurity.Concrete.UniformTableSplit
end
-- ==== merged from T3_Secc_CanonEncoding ====
section

namespace SigGolfCandidate.T3.Security.CanonEncoding
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SphincsSecurity.Concrete
open SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers)
open CanonGraph
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
abbrev EncLeaf := {L : LeafPos // L.Source}
def EncLeaf.toWots (L : EncLeaf) : Wots.LeafAddr := ⟨L.1.lay, L.1.tree.val, L.1.leaf.val⟩
theorem route_tree_lt (index : Nat) (hindex : index < 2 ^ 31) (lay : Layer) :
    (route index lay).2 < 2 ^ treeBits lay := by
  fin_cases lay <;> simp [route, treeBits, height] <;> omega
theorem childIndex_lt (L : EncLeaf) : L.1.tree.val * 2 ^ height L.1.lay + L.1.leaf.val < 2 ^ 31 := by
  obtain ⟨⟨lay, tree, leaf⟩, ht, hl⟩ := L
  change tree.val < 2 ^ treeBits lay at ht
  change leaf.val < 2 ^ height lay at hl
  change tree.val * 2 ^ height lay + leaf.val < 2 ^ 31
  fin_cases lay <;> simp [treeBits, height] at ht hl ⊢ <;> omega
def childIndex (L : EncLeaf) : Fin (2^31) :=
  ⟨L.1.tree.val * 2 ^ height L.1.lay + L.1.leaf.val, childIndex_lt L⟩
def msgLabel (labels : Labels) (L : EncLeaf) : Digest :=
  if h : L.1.lay.val < 3 then
    treeLabel labels ⟨L.1.lay.val + 1, by omega⟩ (childIndex L) (height ⟨L.1.lay.val + 1, by omega⟩) 0
  else (labels (.forest (childIndex L))).extractLsb' 0 128
def decodeAt (L : EncLeaf) (answer : HashOutput) : Option Digest :=
  if (searchDecode L.1.lay (answer.extractLsb' 0 128)).isSome then some (answer.extractLsb' 0 128) else none
abbrev Selection := Option (Fin (2^22) × Digest)
abbrev Selections := EncLeaf → Selection
noncomputable def rowsLaw (selections : Selections) : PMF (EncLeaf → Fin (2^22) → HashOutput) :=
  FinitePmfProduct.law (fun L => FirstSuccessTable.afterSelect (decodeAt L) (2^22) (selections L))
end SigGolfCandidate.T3.Security.CanonEncoding
end
-- ==== merged from T3_Secc_WotsEncodingCongr ====
section

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue leafRoot)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open Mask
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace Enc
/-- C2/C3 (FULL): an encoding block is a 64-byte input whose tweak is a hyper word with ANY high word (the verifier
reads the encoding row tweak's high word from the witness, honest value 1). A leaf block carries the same 16-byte
header (high word 0) but is 704 or 832 bytes long (T51 top leaf: 832), so the length keeps them apart. -/
def EncHeader (input : HashInput) : Prop :=
  input.length = 64 ∧ ∃ (lay : Layer) (tree leaf : Nat) (hp : BitVec 64),
    Extract.hdrBlock input = bytesLE 16 (hp ++ hyperWord lay.val (tree * 2 ^ height lay + leaf))
def NonEnc : Spec.Domain → Prop
  | .inl (.inr input) => ¬ EncHeader input
  | _ => True
/-- `h` is no hyper tweak, whatever its high word. -/
def NotHyper (h : BitVec 128) : Prop :=
  ∀ (lay : Layer) (tree leaf : Nat) (hp : BitVec 64), h ≠ hp ++ hyperWord lay.val (tree * 2 ^ height lay + leaf)
theorem notHyper_of_marker {h : BitVec 128} (hm : tweakMarker h ≠ 1) : NotHyper h := by
  intro lay tree leaf hp he
  apply hm
  rw [he, append64_marker, hyperWord_marker]
theorem notHyper_of_tag {h : BitVec 128} (ht : tweakTag h ≠ 2) : NotHyper h := by
  intro lay tree leaf hp he
  apply ht
  rw [he, append64_tag, hyperWord_tag]
theorem notHyper_of_ne_rowTweak_low {h : BitVec 128}
    (hl : ∀ lay routed : Nat, h.extractLsb' 0 64 ≠ hyperWord lay routed) : NotHyper h := by
  intro lay tree leaf hp he
  apply hl lay.val (tree * 2 ^ height lay + leaf)
  rw [he, append64_low]
theorem rowTweak_eq_hyper (lay : Layer) (tree leaf : Nat) :
    rowTweak lay tree leaf = 1#64 ++ hyperWord lay.val (tree * 2 ^ height lay + leaf) := rfl
theorem encHeader_of_rowTweak {input : HashInput} (hlen : input.length = 64) {lay : Layer} {tree leaf : Nat}
    (h : Extract.hdrBlock input = bytesLE 16 (rowTweak lay tree leaf)) : EncHeader input :=
  ⟨hlen, lay, tree, leaf, 1#64, h⟩
theorem nonEnc_of_hdr (input : HashInput) (h : BitVec 128) (hblock : Extract.hdrBlock input = bytesLE 16 h)
    (htag : NotHyper h) : NonEnc (.inl (.inr input)) := by
  rintro ⟨-, l, tr, lf, hp, he⟩
  rw [hblock] at he
  exact htag l tr lf hp (bytesLE_injective he)
theorem nonEnc_of_length (input : HashInput) (hl : input.length ≠ 64) : NonEnc (.inl (.inr input)) :=
  fun he => hl he.1
theorem nonEnc_pad64_long (input : HashInput) (hl : 64 < input.length) : NonEnc (.inl (.inr (pad64 input))) := by
  apply nonEnc_of_length
  have : input.length ≤ (pad64 input).length := by
    simp only [pad64, List.length_append, List.length_replicate]; omega
  omega
theorem tag_ne_four {t : Nat} (ht : t % 256 ≠ 2) (l tr p ix : Nat) : NotHyper (header t l tr p ix) :=
  notHyper_of_tag (by rw [header_tag]; exact ht)
/-- Legacy node tweaks other than the lower Merkle tweaks (whose low word is a hyper word) are no hyper tweak. -/
theorem nodeTweak_ne_row (tag lay tree heap : Nat) (ht : tag % 256 ≠ 2)
    (hlow : tag = 3 → lay < 4 → lay = 0) : NotHyper (nodeTweak tag lay tree heap) := by
  by_cases h : tag = 3 ∧ lay < 4
  · obtain ⟨rfl, h4⟩ := h
    obtain rfl := hlow rfl h4
    -- C4: the top label's low word is `topNodeWord heap < 4096`; a hyper word has byte7 = 193.
    apply notHyper_of_ne_rowTweak_low
    intro l r he
    have hv := congrArg BitVec.toNat he
    have hl := nodeTweak_top_low tree heap
    have hlt := topNodeWord_lt heap
    unfold tweakLow at hl
    rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, hyperWord_toNat] at hv
    omega
  · by_cases hf : tag = 3 ∧ lay < 13
    · obtain ⟨rfl, h13⟩ := hf
      exact notHyper_of_tag (nodeTweak_fts_tag_ne (by omega) h13 _ _ (by decide) (by decide))
    · rw [nodeTweak_other hf]; exact tag_ne_four ht _ _ _ _
theorem rowTweak_layer {lay lay' : Layer} {tree leaf tree' leaf' : Nat}
    (h : rowTweak lay tree leaf = rowTweak lay' tree' leaf') : lay = lay' := by
  have hw := (append64_inj h).2
  have hl := congrArg (fun w : BitVec 64 => w.toNat / 2 ^ 48 % 256) hw
  simp only [hyperWord_toNat] at hl
  have h1 := lay.isLt
  have h2 := lay'.isLt
  have := Nat.mod_lt (tree * 2 ^ height lay + leaf) (show 0 < 2 ^ 32 by decide)
  have := Nat.mod_lt (tree' * 2 ^ height lay' + leaf') (show 0 < 2 ^ 32 by decide)
  exact Fin.ext (by omega)
/-- The layer of a hyper tweak, whatever the high words. -/
theorem hyperH_layer {lay lay' : Layer} {r r' : Nat} {hp hp' : BitVec 64}
    (h : hp ++ hyperWord lay.val r = hp' ++ hyperWord lay'.val r') : lay = lay' := by
  have hw := (append64_inj h).2
  have hl := congrArg (fun w : BitVec 64 => w.toNat / 2 ^ 48 % 256) hw
  simp only [hyperWord_toNat] at hl
  have h1 := lay.isLt
  have h2 := lay'.isLt
  have := Nat.mod_lt r (show 0 < 2 ^ 32 by decide)
  have := Nat.mod_lt r' (show 0 < 2 ^ 32 by decide)
  exact Fin.ext (by omega)
theorem nonEnc_prefixed (x : Digest) (rest : HashInput) {t : Nat} (ht : t % 256 ≠ 2) (l tr p ix : Nat) :
    NonEnc (.inl (.inr (pad64 (bytesLE 16 x ++ bytesLE 16 (header t l tr p ix) ++ rest)))) := by
  apply nonEnc_of_hdr _ _ _ (tag_ne_four ht l tr p ix)
  rw [Extract.hdrBlock_pad64 _ (by simp only [List.length_append, bytesLE_length]; omega), Extract.hdrBlock_prefix]
theorem nonEnc_chainInput (lay : Layer) (tree leaf i s : Nat) (v : Digest) :
    NonEnc (.inl (.inr (pad64 (chainInput lay tree leaf i s v)))) := by
  apply nonEnc_of_hdr _ (chainHeader lay tree leaf i s) _
    (notHyper_of_marker (by unfold tweakMarker; have := chainHeader_firstByte lay tree leaf i s; omega))
  rw [chainInput_padded]
  change ((chainInput lay tree leaf i s v).drop 16).take 16 = _
  rw [chainInput_header]
section Programs
theorem respects_nodeHash (tag lay tree heap : Nat) (left right : Digest) (ht : tag % 256 ≠ 2)
    (hlow : tag = 3 → lay < 4 → lay = 0) :
    Respects NonEnc (nodeHash tag lay tree heap left right) := by
  rw [nodeHash_eq_projHash]
  apply Respects.projHash
  rw [pad64_nodeInputP]
  exact nonEnc_of_hdr _ _ (Extract.hdrBlock_block4 left _ 0 right) (nodeTweak_ne_row tag lay tree heap ht hlow)
theorem respects_buildLevel (tag lay tree h level : Nat) (nodes : List Digest) (ht : tag % 256 ≠ 2)
    (hlow : tag = 3 → lay = 0 ∨ 4 ≤ lay) :
    Respects NonEnc (buildLevel tag lay tree h level nodes) :=
  Respects.mapM _ _ fun _ _ => respects_nodeHash _ _ _ _ _ _ ht
    (fun h3 h4 => by rcases hlow h3 with h | h <;> omega)
theorem respects_buildLevels (tag lay tree h : Nat) (leaves : List Digest) (ht : tag % 256 ≠ 2)
    (hlow : tag = 3 → lay = 0 ∨ 4 ≤ lay) :
    Respects NonEnc (buildLevels tag lay tree h leaves) := by
  unfold buildLevels
  exact Respects.foldlM _ _ (fun level _ levels =>
    Respects.bind (respects_buildLevel tag lay tree h level _ ht hlow) fun _ => Respects.pure' _) _
theorem leafInput_long (lay : Layer) (tree leaf : Nat) (ends : List Digest) (hlen : 4 ≤ ends.length) :
    64 < (leafInput lay tree leaf ends).length := by
  rw [leafInput_length]
  split_ifs <;> omega
/-- C3 (FULL): a leaf block carries its leaf's hyper label; it is no encoding block because it hashes at least 4
chain ends (every leaf hashes `chainCount lay ≥ 43`), so it is longer than 64 bytes. -/
theorem respects_leafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) (hlen : 4 ≤ ends.length) :
    Respects NonEnc (leafHash lay tree leaf ends) := by
  unfold leafHash
  exact Respects.projHash _ _ (nonEnc_pad64_long _ (leafInput_long lay tree leaf ends hlen))
theorem chainCount_ge4 (lay : Layer) : 4 ≤ chainCount lay := by fin_cases lay <;> decide
theorem respects_privatePair (tag lay tree position index : Nat) :
    Respects NonEnc (privatePair tag lay tree position index) :=
  Respects.privatePair _ _ _ _ _ trivial
theorem respects_mask (level index : Nat) : Respects NonEnc (mask level index) := by
  unfold mask pairedMask
  exact Respects.bind (respects_privatePair _ _ _ _ _) fun _ => Respects.pure' _
theorem respects_privateMac (region : Region) : Respects NonEnc (privateMac region) := by
  unfold privateMac privateMacKey
  exact Respects.bind (Respects.bind (Respects.privateHash _ trivial) fun _ =>
    Respects.bind (Respects.privateHash _ trivial) fun _ => Respects.pure' _) fun _ => Respects.pure' _
theorem respects_maskedLevel (nodes : List Digest) (level : Nat) : Respects NonEnc (maskedLevel nodes level) := by
  unfold maskedLevel pairedMask
  exact Respects.bind (Respects.mapM _ _ fun _ _ =>
    Respects.bind (respects_privatePair _ _ _ _ _) fun _ => Respects.pure' _) fun _ => Respects.pure' _
theorem respects_privateNonce (message : Message) : Respects NonEnc (privateNonce message) := by
  unfold privateNonce
  exact Respects.bind (Respects.privateHash _ trivial) fun _ => Respects.pure' _
theorem respects_digest (rho : Digest) (message : Message) (counter : BitVec 32) :
    Respects NonEnc (digest rho message counter) := by
  unfold digest
  apply Respects.publicHash
  apply nonEnc_of_hdr _ (digestHeader counter) _ (notHyper_of_marker (by rw [digestHeader_marker]; decide))
  unfold digestInput
  rw [Extract.hdrBlock_pad64 _ (by simp only [List.length_append, bytesLE_length]; omega),
    Extract.hdrBlock_prefix]
theorem respects_chain (lay : Layer) (tree leaf i start count : Nat) (v : Digest) :
    Respects NonEnc (chain lay tree leaf i start count v) := by
  unfold chain
  exact Respects.foldlM _ _ (fun step _ value => Respects.shortHash _ (nonEnc_chainInput _ _ _ _ _ _)) v
/-- Witness stack: top chain steps (G or F input) carry the chain header in bytes `16..32`. -/
theorem nonEnc_topChainInput (leaf i s : Nat) (v : Digest) :
    NonEnc (.inl (.inr (pad64 (topChainInput leaf i s v)))) := by
  apply nonEnc_of_hdr _ (chainHeader 0 0 leaf i s) _
    (notHyper_of_marker (by unfold tweakMarker; have := chainHeader_firstByte 0 0 leaf i s; omega))
  have hpad : pad64 (topChainInput leaf i s v) = topChainInput leaf i s v := by
    unfold topChainInput; split
    · simp [pad64, SphincsSecurity.bytesLE_length, zero16]
    · exact chainInput_padded _ _ _ _ _ _
  rw [hpad]
  change ((topChainInput leaf i s v).drop 16).take 16 = _
  unfold topChainInput; split
  · simp [zero16, List.append_assoc, SphincsSecurity.bytesLE_length]
  · exact chainInput_header _ _ _ _ _ _
theorem respects_topChain (leaf i start count : Nat) (v : Digest) :
    Respects NonEnc (topChain leaf i start count v) := by
  unfold topChain
  exact Respects.foldlM _ _ (fun step _ value => Respects.projHash _ _ (nonEnc_topChainInput _ _ _ _)) v
theorem respects_layChain (lay : Layer) (tree leaf i start count : Nat) (v : Digest) :
    Respects NonEnc (layChain lay tree leaf i start count v) := by
  unfold layChain; split
  · exact respects_topChain _ _ _ _ _
  · exact respects_chain _ _ _ _ _ _ _
theorem respects_topPairsFrom (first start : Nat) (init : List Digest) :
    Respects NonEnc (topPairsFrom first start init) := by
  unfold topPairsFrom topSeedPair
  exact Respects.foldlM _ _ (fun _ _ _ =>
    Respects.bind (respects_privatePair _ _ _ _ _) fun _ => Respects.pure' _) _
theorem respects_topCoefs (leaf : Nat) : Respects NonEnc (topCoefs leaf) := by
  unfold topCoefs
  exact Respects.bind (respects_topPairsFrom _ _ _) fun _ => Respects.pure' _
/-- `Respects.bind` whose continuation only needs to respect `S` on values satisfying an invariant of `p`. -/
theorem respects_bind_invT {S : Spec.Domain → Prop} {α β : Type} {p : M α} {f : α → M β} (P : α → Prop)
    (hp : Respects S p) (hP : ∀ T, P (evalWithAnswerFn T p)) (hf : ∀ x, P x → Respects S (f x)) :
    Respects S (p >>= f) := by
  intro T T' hT
  obtain ⟨he, hq⟩ := hp T T' hT
  obtain ⟨he', hq'⟩ := hf (evalWithAnswerFn T' p) (hP T') T T' hT
  refine ⟨?_, ?_⟩
  · rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, he]
    exact he'
  · rw [SourceReplay.queried_bind, SourceReplay.queried_bind, hq, he, hq']
/-- C3 (FULL): the top leaf hashes all `chainCount 0 ≥ 4` chain ends, so its block is longer than an encoding
block. -/
theorem respects_buildLeafTopC (leaf : Nat) (coefs : List Digest) (digits : List Nat) (signatureOnly : Bool) :
    Respects NonEnc (buildLeafTopC leaf coefs digits signatureOnly) := by
  rw [Correctness.buildLeafTopC_eq]
  refine respects_bind_invT
    (fun rows : List Digest × List Digest => signatureOnly = false → rows.1.length = chainCount 0)
    (Respects.foldlM _ _ (fun i _ state => ?_) _) (fun T => ?_) fun rows hrows => ?_
  · unfold Correctness.topLeafStep
    refine Respects.bind (respects_topChain _ _ _ _ _) fun value => ?_
    split
    · exact Respects.pure' _
    · exact Respects.bind (respects_topChain _ _ _ _ _) fun _ => Respects.pure' _
  · intro hso
    subst hso
    exact Correctness.eval_foldlM_range_inv T (chainCount 0) _
      (fun done (state : List Digest × List Digest) => state.1.length = done) ([], []) rfl
      (fun i _ state hs => by
        unfold Correctness.topLeafStep
        simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, Bool.false_eq_true, ↓reduceIte,
          List.length_append, List.length_singleton, hs])
  · split
    · exact Respects.pure' _
    · rename_i hso
      exact Respects.bind (respects_leafHash _ _ _ _ (by rw [hrows (by simpa using hso)]; exact chainCount_ge4 0))
        fun _ => Respects.pure' _
theorem respects_buildLeafTop (leaf : Nat) (digits : List Nat) (signatureOnly : Bool) :
    Respects NonEnc (buildLeafTop leaf digits signatureOnly) := by
  unfold buildLeafTop
  exact Respects.bind (respects_topCoefs _) fun _ => respects_buildLeafTopC _ _ _ _
theorem respects_topTreeStep (st : List Digest × List Digest × Digest) (leaf : Nat) :
    Respects NonEnc (topTreeStep st leaf) := by
  unfold topTreeStep topFamilyCoefs
  refine Respects.bind ?_ fun _ => Respects.bind (respects_buildLeafTopC _ _ _ _) fun _ => Respects.pure' _
  split
  · unfold topCoefsK
    exact Respects.bind (respects_topPairsFrom _ _ _) fun _ => Respects.pure' _
  · exact Respects.pure' _
/-- Top-bytes layer: nonce trials carry the top node tweak in bytes `16..32`. -/
theorem respects_topNodeHashN (heap n : Nat) (l r : Digest) : Respects NonEnc (topNodeHashN heap n l r) := by
  unfold topNodeHashN
  apply Respects.projHash
  refine nonEnc_of_hdr _ (nodeTweak 3 0 0 heap) ?_ (nodeTweak_ne_row 3 0 0 heap (by decide) (fun _ _ => rfl))
  rw [Extract.hdrBlock_pad64 _ (by simp [topNodeInput, nonceBytes, bytesLE_length])]
  unfold topNodeInput
  rw [List.append_assoc]
  exact Extract.hdrBlock_prefix _ _ _
theorem respects_topNonceSearch (h heap : Nat) (l r : Digest) :
    ∀ fuel n, Respects NonEnc (topNonceSearch h heap l r fuel n)
  | 0, n => by
      unfold topNonceSearch
      exact Respects.bind (respects_topNodeHashN _ _ _ _) fun _ => Respects.pure' _
  | fuel + 1, n => by
      unfold topNonceSearch
      refine Respects.bind (respects_topNodeHashN _ _ _ _) fun _ => ?_
      split
      · exact Respects.pure' _
      · exact respects_topNonceSearch h heap l r fuel (n + 1)
theorem respects_buildTopLevels (leaves : List Digest) : Respects NonEnc (buildTopLevels leaves) := by
  unfold buildTopLevels
  refine Respects.foldlM _ _ (fun level _ levels => Respects.bind ?_ fun _ => Respects.pure' _) _
  unfold buildTopLevel
  refine Respects.mapM _ _ fun i _ => ?_
  split
  · exact respects_nodeHash 3 0 0 _ _ _ (by decide) (fun _ _ => rfl)
  · unfold topNodeAt
    exact Respects.map _ (respects_topNonceSearch _ _ _ _ _ _)
theorem respects_buildTopTree : Respects NonEnc buildTopTree := by
  unfold buildTopTree
  exact Respects.bind (Respects.foldlM _ _ (fun _ _ _ => respects_topTreeStep _ _) _) fun _ =>
    respects_buildTopLevels _
theorem respects_keygen : Respects NonEnc keygen := by
  unfold keygen
  rw [Correctness.keygenPayload_eq]
  unfold Correctness.cachePayloadProgram
  refine Respects.bind (Respects.bind respects_buildTopTree fun levels => ?_) fun payload => ?_
  · exact Respects.bind (Respects.mapM _ _ fun level _ => respects_maskedLevel _ _) fun _ => Respects.pure' _
  · rcases payload with ⟨publicKey, region⟩
    exact Respects.bind (respects_privateMac region) fun _ => Respects.pure' _
theorem respects_topPath (cache : Cache) (leaf : Nat) : Respects NonEnc (topPath cache leaf) := by
  unfold topPath
  exact Respects.mapM _ _ fun level _ =>
    Respects.bind (respects_mask _ _) fun _ => Respects.pure' _
theorem respects_signTop (cache : Cache) (leaf : Nat) (digits : List Nat) :
    Respects NonEnc (signTop cache leaf digits) := by
  unfold signTop
  refine Respects.bind (respects_buildLeafTop _ _ _) ?_
  rintro ⟨_, values⟩
  exact Respects.bind (respects_topPath _ _) fun _ => Respects.pure' _
end Programs
def leafOf (L : CanonGraph.LeafPos) : LeafAddr := ⟨L.lay, L.tree.val, L.leaf.val⟩
abbrev EncIndex := CanonGraph.LeafPos × Digest × BitVec 32
def encInput (e : EncIndex) : HashInput := encodingRow (leafOf e.1) e.2.1 e.2.2
theorem encInput_length (e : EncIndex) : (encInput e).length = 64 := by
  simp [encInput, encodingRow, encodingInput, pad64, bytesLE_length]
def RejPair (T T' : Answers) (q : Spec.Domain) : Prop :=
  ∃ (input : HashInput) (lay : Layer) (tr lf : Nat), q = .inl (.inr input) ∧
    Extract.hdrBlock input = bytesLE 16 (rowTweak lay tr lf) ∧
    searchDecode lay (low (T (.inl (.inr input)))) = none ∧ searchDecode lay (low (T' (.inl (.inr input)))) = none
theorem RejPair.layer {T T' : Answers} {input : HashInput} {lay : Layer} {tr lf : Nat}
    (h : RejPair T T' (.inl (.inr input))) (hh : Extract.hdrBlock input = bytesLE 16 (rowTweak lay tr lf)) :
    searchDecode lay (low (T (.inl (.inr input)))) = none ∧
      searchDecode lay (low (T' (.inl (.inr input)))) = none := by
  obtain ⟨input', lay', tr', lf', hq, hh', h1, h2⟩ := h
  have hi : input' = input := (Sum.inr.inj (Sum.inl.inj hq)).symm
  subst hi
  rw [hh] at hh'
  have hl : lay' = lay := (rowTweak_layer (bytesLE_injective hh')).symm
  subst hl
  exact ⟨h1, h2⟩
theorem RejPair.mk {T T' : Answers} {input : HashInput} {lay : Layer} {tr lf : Nat}
    (hh : Extract.hdrBlock input = bytesLE 16 (rowTweak lay tr lf))
    (h1 : searchDecode lay (low (T (.inl (.inr input)))) = none)
    (h2 : searchDecode lay (low (T' (.inl (.inr input)))) = none) : RejPair T T' (.inl (.inr input)) :=
  ⟨input, lay, tr, lf, rfl, hh, h1, h2⟩
def AgreeOn (S : Spec.Domain → Prop) (T T' : Answers) : Prop :=
  ∀ q, S q → T' q = T q ∨ RejPair T T' q
def RespAt (T : Answers) (S : Spec.Domain → Prop) {α : Type} (p : M α) : Prop :=
  ∀ T' : Answers, AgreeOn S T T' →
    evalWithAnswerFn T' p = evalWithAnswerFn T p ∧ SourceReplay.queried T' p = SourceReplay.queried T p
section RespAt
variable {T : Answers} {S : Spec.Domain → Prop}
theorem RespAt.pure' {α : Type} (x : α) : RespAt T S (pure x : M α) := fun _ _ => ⟨rfl, rfl⟩
theorem RespAt.bind {α β : Type} {p : M α} {f : α → M β} (hp : RespAt T S p)
    (hf : RespAt T S (f (evalWithAnswerFn T p))) : RespAt T S (p >>= f) := by
  intro T' hT'
  obtain ⟨he, hq⟩ := hp T' hT'
  obtain ⟨he', hq'⟩ := hf T' hT'
  refine ⟨?_, ?_⟩
  · rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, he]
    exact he'
  · rw [SourceReplay.queried_bind, SourceReplay.queried_bind, hq, he, hq']
theorem RespAt.eval_eq {α : Type} {p : M α} (h : RespAt T S p) {T' : Answers} (hT' : AgreeOn S T T') :
    evalWithAnswerFn T' p = evalWithAnswerFn T p := (h T' hT').1
theorem RespAt.queried_eq {α : Type} {p : M α} (h : RespAt T S p) {T' : Answers} (hT' : AgreeOn S T T') :
    SourceReplay.queried T' p = SourceReplay.queried T p := (h T' hT').2
end RespAt
end Enc
open Enc
theorem leafSeed_congr_nonEnc {T T' : Answers} (h : ∀ q, NonEnc q → T' q = T q) (lay : Layer) (tree leaf i : Nat) :
    leafSeed T' lay tree leaf i = leafSeed T lay tree leaf i := by
  unfold leafSeed
  split_ifs
  · unfold Correctness.topLeafSeed Correctness.topCoefList
    congr 2
    funext j
    unfold Correctness.topCoef Correctness.topCoefN topSeedPair
    rw [(Enc.respects_privatePair 0 0 0 _ 0).eval_eq h]
  all_goals rw [(Enc.respects_privatePair 0 lay.val tree (i / 2) leaf).eval_eq h]
theorem leafEnd_congr_nonEnc {T T' : Answers} (h : ∀ q, NonEnc q → T' q = T q) (lay : Layer) (tree leaf i : Nat) :
    leafEnd T' lay tree leaf i = leafEnd T lay tree leaf i := by
  unfold leafEnd
  rw [leafSeed_congr_nonEnc h]
  exact (Enc.respects_layChain _ _ _ _ _ _ _).eval_eq h
theorem leafRoot_congr_nonEnc {T T' : Answers} (h : ∀ q, NonEnc q → T' q = T q) (lay : Layer) (tree leaf : Nat) :
    leafRoot T' lay tree leaf = leafRoot T lay tree leaf := by
  unfold leafRoot
  have he : (List.range (chainCount lay)).map (leafEnd T' lay tree leaf) =
      (List.range (chainCount lay)).map (leafEnd T lay tree leaf) :=
    List.map_congr_left fun i _ => leafEnd_congr_nonEnc h lay tree leaf i
  rw [he]
  exact (Enc.respects_leafHash _ _ _ _
    (by simp only [List.length_map, List.length_range]; exact Enc.chainCount_ge4 lay)).eval_eq h
theorem builtTree_congr_nonEnc {T T' : Answers} (h : ∀ q, NonEnc q → T' q = T q) (lay : Layer) (tree : Nat)
    (hlay : lay = 0) : builtTree T' lay tree = builtTree T lay tree := by
  unfold builtTree
  have hr : Correctness.leafRoot T' lay tree = Correctness.leafRoot T lay tree :=
    funext (leafRoot_congr_nonEnc h lay tree)
  rw [hr, if_pos hlay, if_pos hlay]
  exact (Enc.respects_buildTopLevels _).eval_eq h
end SigGolfCandidate.T3.Security.Wots
end
-- ==== merged from T3_Secc_WotsStructuralHonest ====
section

namespace SigGolfCandidate.T3.Security.Wots.Structural
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue leafRoot)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] SigGolfCandidate.T3.buildFts SigGolfCandidate.T3.buildTree SigGolfCandidate.T3.buildLeaf
def QueriesSat (T : Answers) (Q : T3.Spec.Domain → Prop) {α : Type} (program : M α) : Prop :=
  ∀ q ∈ SourceReplay.queried T program, Q q
section QueriesSat
variable {T : Answers} {Q : T3.Spec.Domain → Prop}
theorem QueriesSat.pure' {α : Type} (x : α) : QueriesSat T Q (pure x : M α) := by
  intro q hq
  simp at hq
theorem QueriesSat.bind {α β : Type} {p : M α} {f : α → M β} (hp : QueriesSat T Q p)
    (hf : QueriesSat T Q (f (evalWithAnswerFn T p))) : QueriesSat T Q (p >>= f) := by
  intro q hq
  rw [SourceReplay.queried_bind, List.mem_append] at hq
  rcases hq with hq | hq
  · exact hp q hq
  · exact hf q hq
theorem QueriesSat.map {α β : Type} {p : M α} (f : α → β) (hp : QueriesSat T Q p) : QueriesSat T Q (f <$> p) := by
  rw [map_eq_bind_pure_comp]
  exact QueriesSat.bind hp (QueriesSat.pure' _)
theorem QueriesSat.query {q : T3.Spec.Domain} (h : Q q) : QueriesSat T Q (liftM (T3.Spec.query q)) := by
  intro q' hq'
  have he : SourceReplay.queried T (liftM (T3.Spec.query q) : M _) = [q] := by
    have := SourceReplay.queried_query_bind T q (fun x => (pure x : M _))
    simpa only [bind_pure, SourceReplay.queried_pure] using this
  rw [he, List.mem_singleton] at hq'
  rw [hq']
  exact h
theorem QueriesSat.foldlM_list {β γ : Type} (items : List β) (f : γ → β → M γ) (Inv : Nat → γ → Prop)
    (initial : γ) (h0 : Inv 0 initial)
    (hs : ∀ i (hi : i < items.length) state, Inv i state →
      QueriesSat T Q (f state items[i]) ∧ Inv (i + 1) (evalWithAnswerFn T (f state items[i]))) :
    QueriesSat T Q (items.foldlM f initial) := by
  induction items generalizing Inv initial with
  | nil => exact QueriesSat.pure' _
  | cons x xs ih =>
      rw [List.foldlM_cons]
      obtain ⟨hq, hi⟩ := hs 0 (by simp) initial h0
      refine QueriesSat.bind hq ?_
      exact ih (fun i => Inv (i + 1)) _ hi (fun i hi state hstate => hs (i + 1) (by simp; omega) state hstate)
theorem QueriesSat.foldlM_range {γ : Type} (n : Nat) (f : γ → Nat → M γ) (Inv : Nat → γ → Prop) (initial : γ)
    (h0 : Inv 0 initial)
    (hs : ∀ i, i < n → ∀ state, Inv i state →
      QueriesSat T Q (f state i) ∧ Inv (i + 1) (evalWithAnswerFn T (f state i))) :
    QueriesSat T Q ((List.range n).foldlM f initial) :=
  QueriesSat.foldlM_list (List.range n) f Inv initial h0 (fun i hi state hstate => by
    simp only [List.getElem_range]
    exact hs i (by simpa using hi) state hstate)
theorem QueriesSat.foldlM_range' {γ : Type} (start n : Nat) (f : γ → Nat → M γ) (Inv : Nat → γ → Prop)
    (initial : γ) (h0 : Inv 0 initial)
    (hs : ∀ i, i < n → ∀ state, Inv i state →
      QueriesSat T Q (f state (start + i)) ∧ Inv (i + 1) (evalWithAnswerFn T (f state (start + i)))) :
    QueriesSat T Q ((List.range' start n).foldlM f initial) :=
  QueriesSat.foldlM_list (List.range' start n) f Inv initial h0 (fun i hi state hstate => by
    simp only [List.getElem_range', Nat.one_mul]
    exact hs i (by simpa using hi) state hstate)
theorem QueriesSat.mapM {α β : Type} (items : List α) (f : α → M β) (hf : ∀ x ∈ items, QueriesSat T Q (f x)) :
    QueriesSat T Q (items.mapM f) := by
  induction items with
  | nil => exact QueriesSat.pure' _
  | cons x xs ih =>
      rw [List.mapM_cons]
      exact QueriesSat.bind (hf x List.mem_cons_self) (QueriesSat.bind
        (ih fun y hy => hf y (List.mem_cons_of_mem x hy)) (QueriesSat.pure' _))
theorem QueriesSat.mono {α : Type} {Q' : T3.Spec.Domain → Prop} {p : M α} (hp : QueriesSat T Q p)
    (h : ∀ q, Q q → Q' q) : QueriesSat T Q' p := fun q hq => h q (hp q hq)
end QueriesSat
theorem queried_shortHash' (T : Answers) (input : HashInput) :
    SourceReplay.queried T (shortHash input) = [.inl (.inr (pad64 input))] := rfl
theorem sat_shortHash {T : Answers} {Q : T3.Spec.Domain → Prop} (input : HashInput)
    (h : Q (.inl (.inr (pad64 input)))) : QueriesSat T Q (shortHash input) := by
  intro q hq
  rw [queried_shortHash', List.mem_singleton] at hq
  rw [hq]
  exact h
theorem queried_projHash' (T : Answers) (high : Bool) (input : HashInput) :
    SourceReplay.queried T (projHash high input) = [.inl (.inr (pad64 input))] := rfl
/-- C4: `sat_shortHash` for a hash keeping either half. -/
theorem sat_projHash {T : Answers} {Q : T3.Spec.Domain → Prop} (high : Bool) (input : HashInput)
    (h : Q (.inl (.inr (pad64 input)))) : QueriesSat T Q (projHash high input) := by
  intro q hq
  rw [queried_projHash', List.mem_singleton] at hq
  rw [hq]
  exact h
theorem sat_publicHash {T : Answers} {Q : T3.Spec.Domain → Prop} (input : HashInput)
    (h : Q (.inl (.inr (pad64 input)))) : QueriesSat T Q (publicHash input) :=
  QueriesSat.query h
theorem chain_zero (lay : Layer) (tree leaf i start : Nat) (v : Digest) :
    chain lay tree leaf i start 0 v = pure v := rfl
theorem queried_chain_one (T : Answers) (lay : Layer) (tree leaf i s : Nat) (v : Digest) :
    SourceReplay.queried T (chain lay tree leaf i s 1 v) = [.inl (.inr (pad64 (chainInput lay tree leaf i s v)))] := rfl
theorem eval_honestChain (T : Answers) (lay : Layer) (tree leaf i : Nat) (seed : Digest) (start count : Nat) :
    evalWithAnswerFn T (chain lay tree leaf i start count (honestChainValue T lay tree leaf i seed start)) =
      honestChainValue T lay tree leaf i seed (start + count) := by
  unfold honestChainValue
  rw [Correctness.eval_chain_add]
  simp only [Nat.zero_add]
theorem honestChainValue_zero (T : Answers) (lay : Layer) (tree leaf i : Nat) (seed : Digest) :
    honestChainValue T lay tree leaf i seed 0 = seed := rfl
def nodeQuery (tag lay tree heap : Nat) (left right : Digest) : T3.Spec.Domain :=
  .inl (.inr (pad64 (nodeInputP tag lay tree heap left 0 right)))
theorem sat_nodeHash {T : Answers} {Q : T3.Spec.Domain → Prop} (tag lay tree heap : Nat) (left right : Digest)
    (h : Q (nodeQuery tag lay tree heap left right)) : QueriesSat T Q (T3.nodeHash tag lay tree heap left right) := by
  rw [nodeHash_eq_projHash]
  exact sat_projHash _ _ h
theorem sat_buildLevel {T : Answers} {Q : T3.Spec.Domain → Prop} (tag lay tree h level : Nat)
    (nodes : List Digest)
    (hq : ∀ i, i < nodes.length / 2 →
      Q (nodeQuery tag lay tree (2 ^ (h - level) + i) (nodes.getD (2 * i) 0) (nodes.getD (2 * i + 1) 0))) :
    QueriesSat T Q (T3.buildLevel tag lay tree h level nodes) := by
  unfold T3.buildLevel
  exact QueriesSat.mapM _ _ (fun i hi => sat_nodeHash _ _ _ _ _ _ (hq i (List.mem_range.mp hi)))
def levelsStep (tag lay tree h : Nat) (levels : List (List Digest)) (level : Nat) : M (List (List Digest)) := do
  let nodes ← T3.buildLevel tag lay tree h level (levels.getD (level - 1) [])
  pure (levels ++ [nodes])
def levelsFold (tag lay tree h : Nat) (leaves : List Digest) (n : Nat) : M (List (List Digest)) :=
  (List.range' 1 n).foldlM (levelsStep tag lay tree h) [leaves]
theorem buildLevels_eq_fold (tag lay tree h : Nat) (leaves : List Digest) :
    T3.buildLevels tag lay tree h leaves = levelsFold tag lay tree h leaves h := rfl
theorem eval_levelsStep (T : Answers) (tag lay tree h : Nat) (levels : List (List Digest)) (level : Nat) :
    evalWithAnswerFn T (levelsStep tag lay tree h levels level) =
      levels ++ [evalWithAnswerFn T (T3.buildLevel tag lay tree h level (levels.getD (level - 1) []))] := by
  simp only [levelsStep, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
theorem eval_levelsSteps_append (T : Answers) (tag lay tree h : Nat) (levels : List Nat) :
    ∀ state : List (List Digest), ∃ extra,
      evalWithAnswerFn T (levels.foldlM (levelsStep tag lay tree h) state) = state ++ extra := by
  induction levels with
  | nil => intro state; exact ⟨[], by simp⟩
  | cons x xs ih =>
      intro state
      rw [List.foldlM_cons, evalWithAnswerFn_bind, eval_levelsStep]
      obtain ⟨extra, he⟩ := ih (state ++ [evalWithAnswerFn T (T3.buildLevel tag lay tree h x (state.getD (x - 1) []))])
      exact ⟨[evalWithAnswerFn T (T3.buildLevel tag lay tree h x (state.getD (x - 1) []))] ++ extra,
        by rw [he, List.append_assoc]⟩
theorem levelsFold_succ (tag lay tree h : Nat) (leaves : List Digest) (n : Nat) :
    levelsFold tag lay tree h leaves (n + 1) =
      (levelsFold tag lay tree h leaves n >>= fun state => levelsStep tag lay tree h state (1 + n)) := by
  unfold levelsFold
  rw [List.range'_concat, List.foldlM_append]
  simp only [Nat.one_mul, List.foldlM_cons, List.foldlM_nil, bind_pure]
theorem levelsFold_length (T : Answers) (tag lay tree h : Nat) (leaves : List Digest) (n : Nat) :
    (evalWithAnswerFn T (levelsFold tag lay tree h leaves n)).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [levelsFold_succ, evalWithAnswerFn_bind, eval_levelsStep, List.length_append, ih]
      simp
theorem levelsFold_prefix (T : Answers) (tag lay tree h : Nat) (leaves : List Digest) (n m : Nat) (hnm : n ≤ m) :
    ∃ extra, evalWithAnswerFn T (levelsFold tag lay tree h leaves m) =
      evalWithAnswerFn T (levelsFold tag lay tree h leaves n) ++ extra := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  unfold levelsFold
  rw [← List.range'_append_1, List.foldlM_append, evalWithAnswerFn_bind]
  exact eval_levelsSteps_append T tag lay tree h _ _
theorem sat_buildLevels {T : Answers} {Q : T3.Spec.Domain → Prop} (tag lay tree h : Nat)
    (leaves : List Digest)
    (hq : ∀ level, level < h → ∀ node,
      node < ((evalWithAnswerFn T (T3.buildLevels tag lay tree h leaves)).getD level []).length / 2 →
      Q (nodeQuery tag lay tree (2 ^ (h - (level + 1)) + node)
        (treeValue (evalWithAnswerFn T (T3.buildLevels tag lay tree h leaves)) level (2 * node))
        (treeValue (evalWithAnswerFn T (T3.buildLevels tag lay tree h leaves)) level (2 * node + 1)))) :
    QueriesSat T Q (T3.buildLevels tag lay tree h leaves) := by
  rw [buildLevels_eq_fold] at hq ⊢
  unfold levelsFold
  refine QueriesSat.foldlM_range' 1 h _
    (fun i state => state = evalWithAnswerFn T (levelsFold tag lay tree h leaves i)) _ rfl ?_
  intro i hi state hstate
  subst hstate
  refine ⟨?_, ?_⟩
  · unfold levelsStep
    refine QueriesSat.bind (sat_buildLevel _ _ _ _ _ _ ?_) (QueriesSat.pure' _)
    intro node hnode
    have hlen := levelsFold_length T tag lay tree h leaves i
    obtain ⟨extra, hext⟩ := levelsFold_prefix T tag lay tree h leaves i h (by omega)
    have hget : (evalWithAnswerFn T (levelsFold tag lay tree h leaves h)).getD i [] =
        (evalWithAnswerFn T (levelsFold tag lay tree h leaves i)).getD i [] := by
      rw [hext, List.getD_append _ _ _ _ (by omega)]
    have h1 : 1 + i - 1 = i := by omega
    have h2 : h - (1 + i) = h - (i + 1) := by omega
    rw [h1] at hnode ⊢
    rw [h2]
    have := hq i hi node (by rw [hget]; exact hnode)
    simpa only [treeValue, hget] using this
  · rw [levelsFold_succ, evalWithAnswerFn_bind]
end SigGolfCandidate.T3.Security.Wots.Structural
end
-- ==== merged from ClaudeWCT_WCT9_QueriesWots ====
section

namespace ClaudeWCT.WCT9.Wots
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness SigGolfCandidate.T3.Cost
open SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem queried_query (A : Answers) (q : Query) :
    SourceReplay.queried A (liftM (SigGolfCandidate.T3.Spec.query q) : M (SigGolfCandidate.T3.Spec.Range q)) = [q] := by
  have := SourceReplay.queried_query_bind A q (fun x => (pure x : M _))
  simpa only [bind_pure, SourceReplay.queried_pure] using this
theorem respects_query {S : Query → Prop} {q : Query} (hq : S q) :
    Mask.Respects S (liftM (SigGolfCandidate.T3.Spec.query q) : M (SigGolfCandidate.T3.Spec.Range q)) := by
  intro T T' hT
  refine ⟨?_, by rw [queried_query, queried_query]⟩
  rw [show evalWithAnswerFn T (liftM (SigGolfCandidate.T3.Spec.query q)) = T q from simulateQ_spec_query T q,
    show evalWithAnswerFn T' (liftM (SigGolfCandidate.T3.Spec.query q)) = T' q from simulateQ_spec_query T' q]
  exact hT q hq
theorem respects_of_allQueriesSatisfy {S : Query → Prop} {α : Type} {p : M α}
    (h : AllQueriesSatisfy p S) : Mask.Respects S p := by
  induction p using OracleComp.inductionOn with
  | pure a => exact Mask.Respects.pure' a
  | query_bind q f ih =>
      obtain ⟨hq, hf⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp h
      exact Mask.Respects.bind (respects_query hq) fun u => ih u (hf u)
theorem shortRespects_of_allQueriesSatisfy {α : Type} {p : M α}
    (h : AllQueriesSatisfy p Ref.ShortQuery) : Ref.ShortRespects p := fun A T hAT =>
  (respects_of_allQueriesSatisfy h A T hAT).1
theorem queriesSat_of_allQueriesSatisfy {Q : Query → Prop} {α : Type} {p : M α}
    (h : AllQueriesSatisfy p Q) (T : Answers) : Structural.QueriesSat T Q p := by
  induction p using OracleComp.inductionOn with
  | pure a => exact Structural.QueriesSat.pure' a
  | query_bind q f ih =>
      obtain ⟨hq, hf⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp h
      exact Structural.QueriesSat.bind (Structural.QueriesSat.query hq) (ih _ (hf _))
theorem allQueriesSatisfy_mono {P Q : Query → Prop} {α : Type} {p : M α}
    (h : AllQueriesSatisfy p P) (hPQ : ∀ q, P q → Q q) : AllQueriesSatisfy p Q := by
  induction p using OracleComp.inductionOn with
  | pure a => exact allQueriesSatisfy_pure _ _
  | query_bind q f ih =>
      obtain ⟨hq, hf⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp h
      exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨hPQ _ hq, fun u => ih u (hf u)⟩
theorem tag_mod {tag : Nat} (h : tag = 3 ∨ tag = 6 ∨ tag = 15) :
    tag % 256 ≠ 0 ∧ tag % 256 ≠ 1 ∧ tag % 256 ≠ 4 ∧ tag % 256 ≠ 12 := by
  rcases h with rfl | rfl | rfl <;> decide
theorem tag_mod' {tag lay : Nat} (h : (tag = 3 ∧ 4 ≤ lay ∧ lay < 13) ∨ tag = 6 ∨ tag = 15) :
    tag % 256 ≠ 0 ∧ tag % 256 ≠ 1 ∧ tag % 256 ≠ 4 ∧ tag % 256 ≠ 12 :=
  tag_mod (by rcases h with ⟨rfl, -⟩ | h | h <;> simp_all)
theorem ftsChainHeader_ne_wots (index coord selected t step : Nat) :
    ∀ (l : Layer) tr leaf i st, ftsChainHeader index coord selected t step ≠ chainHeader l tr leaf i st :=
  fun l tr leaf i st => ftsChainHeaderP_ne_chainHeader _ _ _ _ _ 0 l tr leaf i st
theorem ftsChainHeader_ne_header' (index coord selected t step : Nat) :
    ∀ l tr p ix, ftsChainHeader index coord selected t step ≠ header 4 l tr p ix :=
  fun l tr p ix => ftsChainHeaderP_ne_header _ _ _ _ _ 0 4 l tr p ix
theorem hdrTag_ftsChain {input : HashInput} {index coord selected t step : Nat}
    (h : SigGolfCandidate.T3M.Extract.hdrBlock input = bytesLE 16 (ftsChainHeader index coord selected t step)) :
    Security.BPB.hdrTag input = 1 := by
  unfold Security.BPB.hdrTag
  rw [h, bytesLE16_first_toNat, show (ftsChainHeader index coord selected t step).toNat % 256 = 128 + 4 * (t % 8)
    from ftsChainHeaderP_firstByte _ _ _ _ _ 0, if_pos (by omega)]
theorem hdrTag_ftsLeaf {input : HashInput} {index coord selected : Nat}
    (h : SigGolfCandidate.T3M.Extract.hdrBlock input = bytesLE 16 (ftsLeafHeader index coord selected)) :
    Security.BPB.hdrTag input = 6 := by
  unfold Security.BPB.hdrTag
  rw [h, bytesLE16_first_toNat, ftsLeafHeader_firstByte, if_neg (by decide)]
  have hb : ((bytesLE 16 (ftsLeafHeader index coord selected)).getD 1 0).toNat =
      (ftsLeafHeader index coord selected).toNat / 2 ^ 8 % 256 := by
    show ((ftsLeafHeader index coord selected).extractLsb' 8 8).toNat = _
    rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [hb, ftsLeafHeader_byte1]
theorem ftsQuery_untouched {index : Nat} (a : ChainAddr) {q : Query} (h : FtsQuery index q) :
    Mask.Untouched a q := by
  rcases q with (coin | input) | (tweak | other)
  · exact h.elim
  · rcases FtsInput.hdrBlock (show FtsInput index input from h) with
      ⟨coord, selected, t, step, hblock⟩ | ⟨coord, selected, -, -, hblock⟩ | ⟨coord, heap, -, -, -, hblock⟩ | hblock
    · exact Mask.untouched_of_hdr a input _ hblock (ftsChainHeader_ne_wots _ _ _ _ _)
    · exact Mask.untouched_of_hdr a input _ hblock (fun _ _ _ _ _ => ftsLeafHeader_ne_chainHeader _ _ _ _ _ _ _ _)
    · exact Mask.untouched_of_hdr a input _ hblock (fun _ _ _ _ _ => wctNodeHeader_ne_chainHeader _ _ _ _ _ _ _ _)
    · exact Mask.untouched_of_hdr a input _ hblock
        (fun _ _ _ _ _ => Ne.symm (chainHeader_ne_header _ _ _ _ _ _ _ _ _ _))
  · obtain ⟨coord, selected, pair, -, -, -, rfl⟩ := (show FtsSeed index tweak from h)
    exact Mask.untouched_privatePair a (by decide) _ _ _ _
  · exact h.elim
theorem ftsQuery_nonEnc {index : Nat} {q : Query} (h : FtsQuery index q) : Enc.NonEnc q := by
  rcases q with (coin | input) | (tweak | other)
  · exact h.elim
  · rcases FtsInput.hdrBlock (show FtsInput index input from h) with
      ⟨coord, selected, t, step, hblock⟩ | ⟨coord, selected, -, -, hblock⟩ | ⟨coord, heap, hk, -, -, hblock⟩ | hblock
    · exact Enc.nonEnc_of_hdr input _ hblock (Enc.notHyper_of_marker
        (ne_of_gt (lt_of_lt_of_le (by decide) (ftsChainHeaderP_tweakMarker index coord selected t step 0))))
    · exact Enc.nonEnc_of_hdr input _ hblock (Enc.notHyper_of_tag (by rw [ftsLeafHeader_tweakTag]; decide))
    · exact Enc.nonEnc_of_hdr input _ hblock (Enc.notHyper_of_tag (by
        rw [wctNodeHeader_tweakTag hk]; split <;> decide))
    · exact Enc.nonEnc_of_hdr input _ hblock (Enc.tag_ne_four (by decide) _ _ _ _)
  · trivial
  · trivial
theorem ftsQuery_short {index : Nat} {q : Query} (h : FtsQuery index q) : Ref.ShortQuery q := by
  rcases q with (coin | input) | (tweak | other)
  · trivial
  · have := FtsInput.length_le (show FtsInput index input from h)
    show input.length ≤ SeccLaw.maxInputLength
    unfold SeccLaw.maxInputLength
    omega
  · trivial
  · trivial
theorem ftsQuery_notDigest {index : Nat} {q : Query} (h : FtsQuery index q) : BPB.NotDigestQ q := by
  rcases q with (coin | input) | (tweak | other)
  · trivial
  · show BPB.hdrMarker input ≠ 0
    rcases FtsInput.hdrBlock (show FtsInput index input from h) with
      ⟨coord, selected, t, step, hblock⟩ | ⟨coord, selected, -, -, hblock⟩ | ⟨coord, heap, -, -, -, hblock⟩ | hblock
    · refine BPB.hdrMarker_ne_zero hblock ?_
      unfold tweakMarker
      rw [show ftsChainHeader index coord selected t step = ftsChainHeaderP index coord selected t step 0 from rfl,
        ftsChainHeaderP_firstByte]
      omega
    · refine BPB.hdrMarker_ne_zero hblock ?_; unfold tweakMarker; rw [ftsLeafHeader_firstByte]; decide
    · exact BPB.hdrMarker_ne_zero hblock (wctNodeHeader_tweakMarker_ne_zero _ _ _)
    · exact BPB.hdrMarker_ne_zero hblock (by rw [header_marker]; decide)
  · trivial
  · trivial
namespace Mask
variable (a : ChainAddr) (index : Nat)
theorem respects_chain (coord selected t start count : Nat) (value : Digest) :
    Wots.Mask.Respects (Wots.Mask.Untouched a) (WCT9.chain index coord selected t start count value) := by
  unfold WCT9.chain
  refine Wots.Mask.Respects.foldlM _ _ (fun step _ v => Wots.Mask.Respects.projHash _ _ ?_) _
  unfold ftsChainInputW; split
  · rw [List.append_assoc (bytesLE 16 v ++ _)]
    exact Wots.Mask.untouched_of_hdr a _ _ (hdrBlock_pad64_prefix _ _ _ (bytesLE_length _ _))
      (ftsChainHeader_ne_wots _ _ _ _ _)
  · unfold chainInput
    rw [List.append_assoc (zero16 ++ _)]
    exact Wots.Mask.untouched_of_hdr a _ _ (hdrBlock_pad64_prefix _ _ _ (by simp [zero16]))
      (ftsChainHeader_ne_wots _ _ _ _ _)
theorem respects_leafHash (coord selected : Nat) (ends : List Digest) :
    Wots.Mask.Respects (Wots.Mask.Untouched a) (WCT9.leafHash index coord selected ends) := by
  unfold WCT9.leafHash
  exact Wots.Mask.Respects.shortHash _ (Wots.Mask.untouched_of_hdr a _ _
    (hdrBlock_pad64_prefix _ _ _ (bytesLE_length _ _))
    (fun _ _ _ _ _ => ftsLeafHeader_ne_chainHeader _ _ _ _ _ _ _ _))
theorem respects_forestPk (pairs : List (Digest × Digest)) :
    Wots.Mask.Respects (Wots.Mask.Untouched a) (WCT9.forestPk index pairs) := by
  unfold WCT9.forestPk forestInput
  rw [show zero16 = bytesLE 16 (0 : Digest) by decide]
  exact Wots.Mask.Respects.shortHash _ (Wots.Mask.untouched_prefixed a _ _ (by decide) _ _ _ _)
theorem respects_wctNodeHash (coord heap : Nat) (left right : Digest) :
    Wots.Mask.Respects (Wots.Mask.Untouched a) (WCT9.wctNodeHash coord index heap left right) := by
  unfold WCT9.wctNodeHash
  exact Wots.Mask.respects_nodeHash a 3 _ _ _ _ _ (by decide)
theorem respects_buildChildF (coord selected : Nat) (word : Rank) (coefs : List Digest) (pad : Digest) (hcoord : coord < 9)
    (hsel : selected < 128) :
    Wots.Mask.Respects (Wots.Mask.Untouched a) (buildChildF index coord selected word coefs pad) :=
  respects_of_allQueriesSatisfy (allQueriesSatisfy_mono (buildChildF_queries index coord selected word coefs pad hcoord hsel)
    fun _ => ftsQuery_untouched a)
theorem respects_buildChildH (heap coord selected : Nat) (word : Rank) (coefs : List Digest) (pad : Digest)
    (hcoord : coord < 9) (hsel : selected < 128) :
    Wots.Mask.Respects (Wots.Mask.Untouched a) (buildChildH heap index coord selected word coefs pad) :=
  respects_of_allQueriesSatisfy (allQueriesSatisfy_mono
    (buildChildH_queries index heap coord selected word coefs pad hcoord hsel) fun _ => ftsQuery_untouched a)
theorem respects_buildCoordinateF (coord : Coord) (selected : Child) (word : Rank) (prev : Digest × Digest) :
    Wots.Mask.Respects (Wots.Mask.Untouched a) (buildCoordinateF index coord selected word prev) :=
  respects_of_allQueriesSatisfy (allQueriesSatisfy_mono (buildCoordinateF_queries index coord selected word prev)
    fun _ => ftsQuery_untouched a)
theorem respects_forestRows (output : HashOutput) :
    Wots.Mask.Respects (Wots.Mask.Untouched a) (forestRows index output) :=
  respects_of_allQueriesSatisfy (allQueriesSatisfy_mono (forestRows_queries index output)
    fun _ => ftsQuery_untouched a)
theorem respects_signForest (output : HashOutput) :
    Wots.Mask.Respects (Wots.Mask.Untouched a) (signForest index output) :=
  respects_of_allQueriesSatisfy (allQueriesSatisfy_mono (signForest_queries index output)
    fun _ => ftsQuery_untouched a)
theorem respects_recoverCoordinate (sig : Signature) (output : HashOutput) (coord : Coord) (prev : Digest × Digest) :
    Wots.Mask.Respects (Wots.Mask.Untouched a) (recoverCoordinate sig index output coord prev) :=
  respects_of_allQueriesSatisfy (allQueriesSatisfy_mono (recoverCoordinate_queries index sig output coord prev)
    fun _ => ftsQuery_untouched a)
theorem respects_recoverFts (sig : Signature) (output : HashOutput) :
    Wots.Mask.Respects (Wots.Mask.Untouched a) (recoverFts sig index output) :=
  respects_of_allQueriesSatisfy (allQueriesSatisfy_mono (recoverFts_queries index sig output)
    fun _ => ftsQuery_untouched a)
end Mask
section Programs
variable (index : Nat)
namespace Enc
theorem respects_chain (coord selected t start count : Nat) (value : Digest) :
    Wots.Mask.Respects Wots.Enc.NonEnc (WCT9.chain index coord selected t start count value) := by
  unfold WCT9.chain
  refine Wots.Mask.Respects.foldlM _ _ (fun step _ v => Wots.Mask.Respects.projHash _ _ ?_) _
  unfold ftsChainInputW; split
  · rw [List.append_assoc (bytesLE 16 v ++ _)]
    exact Wots.Enc.nonEnc_of_hdr _ _ (hdrBlock_pad64_prefix _ _ _ (bytesLE_length _ _))
      (Wots.Enc.notHyper_of_marker
        (ne_of_gt (lt_of_lt_of_le (by decide) (ftsChainHeaderP_tweakMarker index coord selected t step 0))))
  · unfold chainInput
    rw [List.append_assoc (zero16 ++ _)]
    exact Wots.Enc.nonEnc_of_hdr _ _ (hdrBlock_pad64_prefix _ _ _ (by simp [zero16]))
      (Wots.Enc.notHyper_of_marker
        (ne_of_gt (lt_of_lt_of_le (by decide) (ftsChainHeaderP_tweakMarker index coord selected t step 0))))
theorem respects_leafHash (coord selected : Nat) (ends : List Digest) :
    Wots.Mask.Respects Wots.Enc.NonEnc (WCT9.leafHash index coord selected ends) := by
  unfold WCT9.leafHash
  exact Wots.Mask.Respects.shortHash _ (Wots.Enc.nonEnc_of_hdr _ _
    (hdrBlock_pad64_prefix _ _ _ (bytesLE_length _ _))
    (Wots.Enc.notHyper_of_tag (by rw [ftsLeafHeader_tweakTag]; decide)))
theorem respects_forestPk (pairs : List (Digest × Digest)) :
    Wots.Mask.Respects Wots.Enc.NonEnc (WCT9.forestPk index pairs) := by
  unfold WCT9.forestPk forestInput
  rw [show zero16 = bytesLE 16 (0 : Digest) by decide]
  exact Wots.Mask.Respects.shortHash _ (Wots.Enc.nonEnc_prefixed _ _ (by decide) _ _ _ _)
theorem respects_buildChildF (coord selected : Nat) (word : Rank) (coefs : List Digest) (pad : Digest) (hcoord : coord < 9)
    (hsel : selected < 128) :
    Wots.Mask.Respects Wots.Enc.NonEnc (buildChildF index coord selected word coefs pad) :=
  respects_of_allQueriesSatisfy (allQueriesSatisfy_mono (buildChildF_queries index coord selected word coefs pad hcoord hsel)
    fun _ => ftsQuery_nonEnc)
theorem respects_buildChildH (heap coord selected : Nat) (word : Rank) (coefs : List Digest) (pad : Digest)
    (hcoord : coord < 9) (hsel : selected < 128) :
    Wots.Mask.Respects Wots.Enc.NonEnc (buildChildH heap index coord selected word coefs pad) :=
  respects_of_allQueriesSatisfy (allQueriesSatisfy_mono
    (buildChildH_queries index heap coord selected word coefs pad hcoord hsel) fun _ => ftsQuery_nonEnc)
theorem respects_buildCoordinateF (coord : Coord) (selected : Child) (word : Rank) (prev : Digest × Digest) :
    Wots.Mask.Respects Wots.Enc.NonEnc (buildCoordinateF index coord selected word prev) :=
  respects_of_allQueriesSatisfy (allQueriesSatisfy_mono (buildCoordinateF_queries index coord selected word prev)
    fun _ => ftsQuery_nonEnc)
theorem respects_forestRows (output : HashOutput) :
    Wots.Mask.Respects Wots.Enc.NonEnc (forestRows index output) :=
  respects_of_allQueriesSatisfy (allQueriesSatisfy_mono (forestRows_queries index output) fun _ => ftsQuery_nonEnc)
theorem respects_signForest (output : HashOutput) :
    Wots.Mask.Respects Wots.Enc.NonEnc (signForest index output) :=
  respects_of_allQueriesSatisfy (allQueriesSatisfy_mono (signForest_queries index output) fun _ => ftsQuery_nonEnc)
theorem respects_recoverFts (sig : Signature) (output : HashOutput) :
    Wots.Mask.Respects Wots.Enc.NonEnc (recoverFts sig index output) :=
  respects_of_allQueriesSatisfy (allQueriesSatisfy_mono (recoverFts_queries index sig output)
    fun _ => ftsQuery_nonEnc)
end Enc
namespace Ref
theorem chain_respects (coord selected t start count : Nat) (value : Digest) :
    Wots.Ref.ShortRespects (WCT9.chain index coord selected t start count value) := by
  unfold WCT9.chain
  exact Wots.Ref.ShortRespects.foldlM _ _ (fun step _ v => Wots.Ref.ShortRespects.projHash _ _
    (Wots.Ref.short_of_le _ (by rw [ftsChainInputW_length]; omega))) value
theorem leafHash_respects (coord selected : Nat) (ends : List Digest) (hlen : ends.length ≤ 200) :
    Wots.Ref.ShortRespects (WCT9.leafHash index coord selected ends) := by
  unfold WCT9.leafHash
  apply Wots.Ref.ShortRespects.shortHash
  apply Wots.Ref.short_of_le
  simp only [zero16, List.length_append, bytesLE_length, digest_list_bytes_length, List.length_drop,
    List.length_replicate]
  omega
theorem forestPk_respects (pairs : List (Digest × Digest)) (hlen : pairs.length ≤ 100) :
    Wots.Ref.ShortRespects (WCT9.forestPk index pairs) := by
  unfold WCT9.forestPk
  apply Wots.Ref.ShortRespects.shortHash
  apply Wots.Ref.short_of_le
  simp only [forestInput, zero16, List.length_append, List.length_replicate, bytesLE_length, pairs_bytes_length]
  omega
theorem buildChildF_respects (coord selected : Nat) (word : Rank) (coefs : List Digest) (pad : Digest) (hcoord : coord < 9)
    (hsel : selected < 128) :
    Wots.Ref.ShortRespects (buildChildF index coord selected word coefs pad) :=
  shortRespects_of_allQueriesSatisfy (allQueriesSatisfy_mono
    (buildChildF_queries index coord selected word coefs pad hcoord hsel) fun _ => ftsQuery_short)
theorem buildCoordinateF_respects (coord : Coord) (selected : Child) (word : Rank) (prev : Digest × Digest) :
    Wots.Ref.ShortRespects (buildCoordinateF index coord selected word prev) :=
  shortRespects_of_allQueriesSatisfy (allQueriesSatisfy_mono
    (buildCoordinateF_queries index coord selected word prev) fun _ => ftsQuery_short)
theorem forestRows_respects (output : HashOutput) : Wots.Ref.ShortRespects (forestRows index output) :=
  shortRespects_of_allQueriesSatisfy (allQueriesSatisfy_mono (forestRows_queries index output)
    fun _ => ftsQuery_short)
theorem signForest_respects (output : HashOutput) : Wots.Ref.ShortRespects (signForest index output) :=
  shortRespects_of_allQueriesSatisfy (allQueriesSatisfy_mono (signForest_queries index output)
    fun _ => ftsQuery_short)
theorem recoverFts_respects (sig : Signature) (output : HashOutput) :
    Wots.Ref.ShortRespects (recoverFts sig index output) :=
  shortRespects_of_allQueriesSatisfy (allQueriesSatisfy_mono (recoverFts_queries index sig output)
    fun _ => ftsQuery_short)
theorem honestTop_short {A T : Answers} (hAT : Wots.Ref.ShortAgree A T) (output : HashOutput) :
    honestTop A index = honestTop T index := by
  rw [← signForest_root A index output, ← signForest_root T index output,
    signForest_respects index output A T hAT]
end Ref
namespace BPB
theorem forestRows_ok (output : HashOutput) : AllQueriesSatisfy (forestRows index output) Security.BPB.NotDigestQ :=
  allQueriesSatisfy_mono (forestRows_queries index output) fun _ => ftsQuery_notDigest
theorem signForest_ok (output : HashOutput) : AllQueriesSatisfy (signForest index output) Security.BPB.NotDigestQ :=
  allQueriesSatisfy_mono (signForest_queries index output) fun _ => ftsQuery_notDigest
theorem recoverFts_ok (sig : Signature) (output : HashOutput) :
    AllQueriesSatisfy (recoverFts sig index output) Security.BPB.NotDigestQ :=
  allQueriesSatisfy_mono (recoverFts_queries index sig output) fun _ => ftsQuery_notDigest
end BPB
namespace Structural
theorem sat_signForest_shape (T : Answers) (output : HashOutput) :
    Wots.Structural.QueriesSat T (FtsQuery index) (signForest index output) :=
  queriesSat_of_allQueriesSatisfy (signForest_queries index output) T
theorem sat_recoverFts_shape (T : Answers) (sig : Signature) (output : HashOutput) :
    Wots.Structural.QueriesSat T (FtsQuery index) (recoverFts sig index output) :=
  queriesSat_of_allQueriesSatisfy (recoverFts_queries index sig output) T
end Structural
end Programs
end ClaudeWCT.WCT9.Wots
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsMaskBase ====
section

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
def seedSlot (a : ChainAddr) : Nat :=
  if a.key.lay = 0 then a.chain else WCT9.lowerOrdinal a.key.lay a.key.leaf a.chain
def seedTweakP (a : ChainAddr) : BitVec 128 :=
  if a.key.lay = 0 then seedTweak a else WCT9.lowerSeedHeader a.key.lay a.key.tree (seedSlot a / 2)
def slotAddr (a : ChainAddr) : ChainAddr :=
  if a.key.lay = 0 then a else ⟨⟨a.key.lay, a.key.tree, 0⟩, 2 * (seedSlot a / 2)⟩
theorem seedTweak_slotAddr (a : ChainAddr) : seedTweak (slotAddr a) = seedTweakP a := by
  unfold slotAddr seedTweakP
  split_ifs with h
  · rfl
  · unfold seedTweak WCT9.lowerSeedHeader
    simp only
    rw [show 2 * (seedSlot a / 2) / 2 = seedSlot a / 2 by omega]
def parAddr (a : ChainAddr) : ChainAddr := ⟨a.key, seedSlot a % 2⟩
theorem parAddr_chain_mod (a : ChainAddr) : (parAddr a).chain % 2 = seedSlot a % 2 := Nat.mod_mod _ _
def siblingHalfP (a : ChainAddr) (output : HashOutput) : Digest := siblingHalf (parAddr a) output
/-- Queries that neither are a row of chain `a` at a chain step (`< 7`; C2: a lower Merkle node input can equal a
row at step 7, which no chain reaches) nor read `a`'s seed cell. -/
def UntouchedP (a : ChainAddr) : Spec.Domain → Prop
  | .inl (.inr input) => ∀ step value, step < 7 → input ≠ chainRowW a step value
  | .inr (.inl tweak) => tweak ≠ seedTweakP a
  | _ => True
noncomputable def prefixStep (answers : Answers) (a : ChainAddr) (input : HashInput) : Option Nat :=
  if h : ∃ step value, step < depth answers a ∧ input = chainRowW a step value then some (Classical.choose h) else none
/-- Mask of chain `a`: its rows below `depth` answer `0` (the last one answers the frontier, in the half its step
reads, C3). Seeds are evaluations
of their leaf family at every layer (campaign X1 stage B, top leaves since campaign T8D), so no private cell is
blanked. -/
noncomputable def maskAt (answers : Answers) (a : ChainAddr) : Answers
  | .inl (.inr input) =>
      match prefixStep answers a input with
      | some step => if step + 1 = depth answers a then
            joinHalf (WCT9.chainHigh a.key.lay a.chain step) (frontierValue answers a) 0
          else (0 : HashOutput)
      | none => answers (.inl (.inr input))
  | .inl (.inl coin) => answers (.inl (.inl coin))
  | .inr c => answers (.inr c)
namespace Mask
open SigGolfCandidate.T3.Security.Wots.Mask in
theorem Respects.inter {S₁ S₂ : Spec.Domain → Prop} {α : Type} {p : M α} (h₁ : Respects S₁ p) (h₂ : Respects S₂ p) :
    Respects (fun q => S₁ q ∧ S₂ q) p := by
  intro T T' hT
  let T'' : Answers := fun q => if S₁ q then T q else T' q
  have e1 := h₁ T T'' (fun q hq => by simp only [T'', if_pos hq])
  have e2 := h₂ T'' T' (fun q hq => by
    simp only [T'']
    split_ifs with h
    · exact hT q ⟨h, hq⟩
    · rfl)
  exact ⟨e1.1.trans e2.1, e1.2.trans e2.2⟩
open SigGolfCandidate.T3.Security.Wots.Mask in
theorem Respects.mono' {S S' : Spec.Domain → Prop} {α : Type} {p : M α} (h : Respects S p) (hS : ∀ q, S q → S' q) :
    Respects S' p := fun T T' hT => h T T' fun q hq => hT q (hS q hq)
theorem untouchedP_of_untouched (a : ChainAddr) {q : Spec.Domain}
    (h : SigGolfCandidate.T3.Security.Wots.Mask.Untouched a q ∧
      SigGolfCandidate.T3.Security.Wots.Mask.Untouched (slotAddr a) q) : UntouchedP a q := by
  rcases q with (coin | input) | (tweak | other)
  · trivial
  · intro step value hs heq
    have hu := h.1 step value (by omega)
    unfold chainRowW WCT9.chainInputW at heq
    split at heq
    · exact hu.2 heq
    · exact hu.1 heq
  · show tweak ≠ seedTweakP a
    rw [← seedTweak_slotAddr]
    exact h.2
  · trivial
open SigGolfCandidate.T3.Security.Wots.Mask in
theorem Respects.untouchedP {α : Type} {p : M α} (h : ∀ c, Respects (Untouched c) p) (a : ChainAddr) :
    Respects (UntouchedP a) p :=
  Respects.mono' (Respects.inter (h a) (h (slotAddr a))) fun _ hq => untouchedP_of_untouched a hq
open SigGolfCandidate.T3.Security.Wots.Mask
theorem referenceDigits_spec (answers : Answers) (L : LeafAddr) :
    (referenceDigits answers L).length = chainCount L.lay ∧ Cost.ValidDigits L.lay (referenceDigits answers L) := by
  unfold referenceDigits
  cases h : referenceSearch answers L with
  | none => exact dummyDigits_spec L.lay
  | some found =>
      obtain ⟨counter, digits⟩ := found
      have hd := (WCT9.layerCounterSearch_some answers L.lay L.tree L.leaf (leafMsg answers L)
        (WCT9.searchLimit L.lay) 0 counter digits (ClaudeWCT.W9.T3.Security.Wots.searchLimit_fits L.lay) h).2.2
      exact ⟨(decode_length_sum hd).1, Cost.validDigits_decode hd⟩
theorem referenceDigits_of_search {answers : Answers} {L : LeafAddr} {counter : BitVec 32} {digits : List Nat}
    (h : referenceSearch answers L = some (counter, digits)) : referenceDigits answers L = digits := by
  unfold referenceDigits
  rw [h]
  rfl
theorem topSigned_reference (answers : Answers) (L : LeafAddr) (hl : L.lay = 0) :
    ((referenceSearch answers L).map Prod.snd).getD dummyTop = referenceDigits answers L := by
  unfold referenceDigits
  rw [hl]
  rfl
theorem depth_le_width (answers : Answers) (a : ChainAddr) (hc : a.chain < chainCount a.key.lay) :
    depth answers a ≤ maxDigit a.key.lay a.chain :=
  (referenceDigits_spec answers a.key).2 a.chain hc
theorem chain_lt_of_depth (answers : Answers) (a : ChainAddr) (hd : 1 ≤ depth answers a) :
    a.chain < chainCount a.key.lay := by
  by_contra hc
  have hlen := (referenceDigits_spec answers a.key).1
  have h0 : depth answers a = 0 := List.getD_eq_default _ _ (by omega)
  omega
theorem depth_le_seven (answers : Answers) (a : ChainAddr) : depth answers a ≤ 7 := by
  by_cases hd : 1 ≤ depth answers a
  · exact (depth_le_width answers a (chain_lt_of_depth answers a hd)).trans (width_le _ _)
  · omega
theorem prefixStep_spec {answers : Answers} {a : ChainAddr} {input : HashInput} {step : Nat}
    (h : prefixStep answers a input = some step) :
    step < depth answers a ∧ ∃ value, input = chainRowW a step value := by
  unfold prefixStep at h
  split at h
  · rename_i hex
    have he := Option.some.inj h
    subst he
    obtain ⟨value, hlt, heq⟩ := Classical.choose_spec hex
    exact ⟨hlt, value, heq⟩
  · cases h
theorem prefixStep_chainRow (answers : Answers) (a : ChainAddr) {s : Nat} (v : Digest) (hs : s < 256) :
    prefixStep answers a (chainRowW a s v) = if s < depth answers a then some s else none := by
  have h7 := depth_le_seven answers a
  split
  · rename_i hlt
    unfold prefixStep
    rw [dif_pos ⟨s, v, hlt, rfl⟩]
    obtain ⟨w, hw, heq⟩ := Classical.choose_spec (⟨s, v, hlt, rfl⟩ :
      ∃ step value, step < depth answers a ∧ chainRowW a s v = chainRowW a step value)
    exact congrArg some (chainRowW_inj hs (by omega) heq).1.symm
  · rename_i hge
    cases hp : prefixStep answers a (chainRowW a s v) with
    | none => rfl
    | some step =>
        obtain ⟨hlt, w, heq⟩ := prefixStep_spec hp
        have := (chainRowW_inj hs (by omega) heq).1
        omega
theorem prefixStep_untouched {answers : Answers} {a : ChainAddr} {input : HashInput}
    (h : UntouchedP a (.inl (.inr input))) : prefixStep answers a input = none := by
  cases hp : prefixStep answers a input with
  | none => rfl
  | some step =>
      obtain ⟨hlt, w, heq⟩ := prefixStep_spec hp
      exact absurd heq (h step w (by have := depth_le_seven answers a; omega))
theorem maskAt_public (answers : Answers) (a : ChainAddr) (input : HashInput) :
    maskAt answers a (.inl (.inr input)) = match prefixStep answers a input with
      | some step => if step + 1 = depth answers a then
            joinHalf (WCT9.chainHigh a.key.lay a.chain step) (frontierValue answers a) 0
          else (0 : HashOutput)
      | none => answers (.inl (.inr input)) := rfl
theorem maskAt_private (answers : Answers) (a : ChainAddr) (c : Coordinate) :
    maskAt answers a (.inr c) = answers (.inr c) := rfl
theorem maskAt_tweak (answers : Answers) (a : ChainAddr) (tweak : BitVec 128) :
    maskAt answers a (.inr (.inl tweak)) = answers (.inr (.inl tweak)) := rfl
theorem maskAt_untouched (answers : Answers) (a : ChainAddr) {q : Spec.Domain} (h : UntouchedP a q) :
    maskAt answers a q = answers q := by
  rcases q with (coin | input) | (tweak | other)
  · rfl
  · rw [maskAt_public, prefixStep_untouched h]
  · rfl
  · rfl
theorem maskAt_prefix (answers : Answers) (a : ChainAddr) {s : Nat} (v : Digest) (hs : s < depth answers a) :
    maskAt answers a (.inl (.inr (chainRowW a s v))) =
      if s + 1 = depth answers a then joinHalf (WCT9.chainHigh a.key.lay a.chain s) (frontierValue answers a) 0
        else 0 := by
  have h7 := depth_le_seven answers a
  rw [maskAt_public, prefixStep_chainRow answers a v (by omega), if_pos hs]
  rfl
theorem maskAt_row_ge (answers : Answers) (a : ChainAddr) {s : Nat} (v : Digest) (hs : depth answers a ≤ s)
    (hs' : s < 256) : maskAt answers a (.inl (.inr (chainRowW a s v))) = answers (.inl (.inr (chainRowW a s v))) := by
  rw [maskAt_public, prefixStep_chainRow answers a v hs', if_neg (by omega)]
theorem maskAt_of_depth_zero (answers : Answers) (a : ChainAddr) (hd : depth answers a = 0) :
    maskAt answers a = answers := by
  funext q
  rcases q with (coin | input) | (tweak | other)
  · rfl
  · rw [maskAt_public]
    cases hp : prefixStep answers a input with
    | none => rfl
    | some step => have := (prefixStep_spec hp).1; omega
  · rfl
  · rfl
theorem eval_maskAt_of_respects (answers : Answers) (a : ChainAddr) {α : Type} {program : M α}
    (h : Respects (UntouchedP a) program) :
    evalWithAnswerFn (maskAt answers a) program = evalWithAnswerFn answers program :=
  (h _ _ fun _ hq => maskAt_untouched answers a hq).1
theorem queried_maskAt_of_respects (answers : Answers) (a : ChainAddr) {α : Type} {program : M α}
    (h : Respects (UntouchedP a) program) :
    SourceReplay.queried (maskAt answers a) program = SourceReplay.queried answers program :=
  (h _ _ fun _ hq => maskAt_untouched answers a hq).2
section Programs
variable (a : ChainAddr)
theorem respectsP_signForest (index : Nat) (output : HashOutput) :
    Respects (UntouchedP a) (ClaudeWCT.WCT9.signForest index output) :=
  Respects.untouchedP (fun c => ClaudeWCT.WCT9.Wots.Mask.respects_signForest c index output) a
theorem respectsP_digest (rho : Digest) (message : Message) (counter : BitVec 32) :
    Respects (UntouchedP a) (digest rho message counter) :=
  Respects.untouchedP (fun c => respects_digest c rho message counter) a
theorem respectsP_digestSearch (rho : Digest) (message : Message) :
    ∀ fuel counter, Respects (UntouchedP a) (ClaudeWCT.WCT9.digestSearch rho message counter fuel) := by
  intro fuel
  induction fuel with
  | zero => intro counter; exact Respects.pure' _
  | succ fuel ih =>
      intro counter
      simp only [ClaudeWCT.WCT9.digestSearch]
      refine Respects.bind (respectsP_digest a _ _ _) fun output => ?_
      split
      · exact Respects.pure' _
      · exact ih _
theorem respectsP_privateMac (region : Region) : Respects (UntouchedP a) (privateMac region) :=
  Respects.untouchedP (fun c => respects_privateMac c region) a
theorem respectsP_privateNonce (message : Message) : Respects (UntouchedP a) (privateNonce message) :=
  Respects.untouchedP (fun c => respects_privateNonce c message) a
theorem respectsP_mask (level index : Nat) : Respects (UntouchedP a) (mask level index) :=
  Respects.untouchedP (fun c => respects_mask c level index) a
theorem respectsP_buildLevels (tag lay tree h : Nat) (leaves : List Digest) (ht : tag % 256 ≠ 1) :
    Respects (UntouchedP a) (buildLevels tag lay tree h leaves) :=
  Respects.untouchedP (fun c => respects_buildLevels c tag lay tree h leaves ht) a
theorem respectsP_leafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    Respects (UntouchedP a) (leafHash lay tree leaf ends) :=
  Respects.untouchedP (fun c => respects_leafHash c lay tree leaf ends) a
end Programs
/-! ### C2/C3 (FULL) programs: halves, the packed lower node tweak, the chain-0 high half -/
theorem respects_halfHash' {S : Spec.Domain → Prop} (high : Bool) (input : HashInput)
    (h : S (.inl (.inr (pad64 input)))) : Respects S (WCT9.halfHash high input) := by
  cases high
  · unfold WCT9.halfHash; simp only [Bool.false_eq_true, ↓reduceIte]; exact Respects.shortHash input h
  · unfold WCT9.halfHash WCT9.highHash; simp only [↓reduceIte]
    exact Respects.bind (Respects.publicHash input h) fun _ => Respects.pure' _
theorem respects_chainW' {S : Spec.Domain → Prop} (lay : Layer) (tree leaf i start count : Nat) (v : Digest)
    (h : ∀ step value, start ≤ step → step < start + count →
      S (.inl (.inr (pad64 (WCT9.chainInputW lay tree leaf i step value))))) :
    Respects S (WCT9.chainW lay tree leaf i start count v) := by
  unfold WCT9.chainW
  exact Respects.foldlM _ _ (fun step hs value => respects_halfHash' _ _ (h step value
    (List.mem_range'_1.mp hs).1 (List.mem_range'_1.mp hs).2)) v
theorem merkleNodeInput_eq_block4 (lay tree heap : Nat) (left right : Digest) :
    WCT9.merkleNodeInput lay tree heap left right = block4 left (WCT9.merkleTweak lay tree heap) 0 right := by
  unfold WCT9.merkleNodeInput block4
  rw [show zero16 = bytesLE 16 (0 : Digest) by decide]
theorem respects_lowerNodeHash' {S : Spec.Domain → Prop} (lay tree heap : Nat) (left right : Digest)
    (h : S (.inl (.inr (block4 left (WCT9.merkleTweak lay tree heap) 0 right)))) :
    Respects S (WCT9.lowerNodeHash lay tree heap left right) := by
  unfold WCT9.lowerNodeHash WCT9.lowerHash
  refine respects_halfHash' _ _ ?_
  rw [merkleNodeInput_eq_block4, pad64_block4]
  exact h
theorem respects_lowerLevel' {S : Spec.Domain → Prop} (lay tree h level : Nat) (nodes : List Digest)
    (hS : ∀ i left right, i < nodes.length / 2 →
      S (.inl (.inr (block4 left (WCT9.merkleTweak lay tree (2 ^ (h - level) + i)) 0 right)))) :
    Respects S (WCT9.lowerLevel lay tree h level nodes) := by
  unfold WCT9.lowerLevel
  exact Respects.mapM _ _ fun i hi => respects_lowerNodeHash' _ _ _ _ _ (hS i _ _ (List.mem_range.mp hi))
theorem respects_lowerLeafHash' {S : Spec.Domain → Prop} (lay : Layer) (tree leaf : Nat) (ends : List Digest)
    (h : S (.inl (.inr (pad64 (leafInput lay tree leaf ends))))) :
    Respects S (WCT9.lowerLeafHash lay tree leaf ends) := by
  rw [WCT9.lowerLeafHash_eq]
  unfold WCT9.lowerHash
  exact respects_halfHash' _ _ h
theorem respects_bind_inv' {S : Spec.Domain → Prop} {α β : Type} {p : M α} {f : α → M β} (P : α → Prop)
    (hp : Respects S p) (hP : ∀ T, P (evalWithAnswerFn T p)) (hf : ∀ x, P x → Respects S (f x)) :
    Respects S (p >>= f) := by
  intro T T' hT
  obtain ⟨he, hq⟩ := hp T T' hT
  obtain ⟨he', hq'⟩ := hf (evalWithAnswerFn T' p) (hP T') T T' hT
  refine ⟨?_, ?_⟩
  · rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, he]
    exact he'
  · rw [SourceReplay.queried_bind, SourceReplay.queried_bind, hq, he, hq']
theorem respects_foldlM_inv' {S : Spec.Domain → Prop} {β γ : Type} (I : γ → Prop) (l : List β) (f : γ → β → M γ)
    (hpres : ∀ x ∈ l, ∀ s, I s → ∀ T, I (evalWithAnswerFn T (f s x)))
    (hf : ∀ x ∈ l, ∀ s, I s → Respects S (f s x)) : ∀ init, I init → Respects S (l.foldlM f init) := by
  induction l with
  | nil => intro init _; exact Respects.pure' init
  | cons x xs ih =>
      intro init hinit
      rw [List.foldlM_cons]
      exact respects_bind_inv' I (hf x List.mem_cons_self init hinit) (hpres x List.mem_cons_self init hinit)
        fun s hs => ih (fun y hy => hpres y (List.mem_cons_of_mem _ hy))
          (fun y hy => hf y (List.mem_cons_of_mem _ hy)) s hs
theorem getD_append_length_le' {levels : List (List Digest)} {nodes : List Digest} {B : Nat}
    (h1 : ∀ j, (levels.getD j []).length ≤ B) (h2 : nodes.length ≤ B) (j : Nat) :
    ((levels ++ [nodes]).getD j []).length ≤ B := by
  rcases Nat.lt_or_ge j levels.length with hj | hj
  · rw [List.getD_append _ _ _ _ hj]; exact h1 j
  · rw [List.getD_append_right _ _ _ _ hj]
    rcases Nat.eq_or_lt_of_le hj with he | hlt
    · rw [← he, Nat.sub_self]; simpa using h2
    · rw [List.getD_eq_default _ _ (by simp; omega)]; simp
theorem lowerLevel_length' (answers : Answers) (lay tree h level : Nat) (nodes : List Digest) :
    (evalWithAnswerFn answers (WCT9.lowerLevel lay tree h level nodes)).length = nodes.length / 2 := by
  unfold WCT9.lowerLevel
  rw [Correctness.eval_mapM, List.length_map, List.length_range]
/-- The fold queries of a lower tree (`lowerLevels`, `buildLevelsBelow`): heaps `2 ^ (h - level) + i` with
`level ≥ 1` and `i < 2 ^ h / 2`. -/
def FoldOK (S : Spec.Domain → Prop) (lay tree h : Nat) : Prop :=
  ∀ level i left right, 1 ≤ level → i < 2 ^ h / 2 →
    S (.inl (.inr (block4 left (WCT9.merkleTweak lay tree (2 ^ (h - level) + i)) 0 right)))
theorem respects_lowerFold' {S : Spec.Domain → Prop} {lay tree h : Nat} (hS : FoldOK S lay tree h) (l : List Nat)
    (hl : ∀ x ∈ l, 1 ≤ x) (leaves : List Digest) (hlen : leaves.length ≤ 2 ^ h) :
    Respects S (l.foldlM (fun levels level => do
      let nodes ← WCT9.lowerLevel lay tree h level (levels.getD (level - 1) [])
      pure (levels ++ [nodes])) [leaves]) := by
  refine respects_foldlM_inv' (fun levels : List (List Digest) => ∀ j, (levels.getD j []).length ≤ 2 ^ h) _ _
    ?_ ?_ [leaves] ?_
  · intro level _ levels hI T
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
    refine getD_append_length_le' hI ?_
    rw [lowerLevel_length']
    exact le_trans (Nat.div_le_self _ _) (hI _)
  · intro level hlv levels hI
    refine Respects.bind (respects_lowerLevel' _ _ _ _ _ fun i left right hi => hS level i left right (hl level hlv)
      ?_) fun _ => Respects.pure' _
    have := hI (level - 1)
    exact lt_of_lt_of_le hi (Nat.div_le_div_right this)
  · intro j
    cases j with
    | zero => simpa using hlen
    | succ j => simp
theorem respects_lowerLevels' {S : Spec.Domain → Prop} {lay tree h : Nat} (hS : FoldOK S lay tree h)
    (leaves : List Digest) (hlen : leaves.length ≤ 2 ^ h) : Respects S (WCT9.lowerLevels lay tree h leaves) := by
  unfold WCT9.lowerLevels
  exact respects_lowerFold' hS _ (fun x hx => (List.mem_range'_1.mp hx).1) leaves hlen
theorem respects_buildLevelsBelow' {S : Spec.Domain → Prop} {lay tree h : Nat} (hS : FoldOK S lay tree h)
    (tag : Nat) (leaves : List Digest) (hlen : leaves.length ≤ 2 ^ h) :
    Respects S (WCT9.buildLevelsBelow tag lay tree h leaves) := by
  unfold WCT9.buildLevelsBelow
  exact respects_lowerFold' hS _ (fun x hx => (List.mem_range'_1.mp hx).1) leaves hlen
theorem lowerHeap_lt' {h level i : Nat} (hlev : 1 ≤ level) (h7 : h ≤ 7) (hi : i < 2 ^ h / 2) :
    2 ^ (h - level) + i < 128 := by
  have hA : 2 ^ (h - level) ≤ 2 ^ (h - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hr : 2 ^ h ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) h7
  have h128 : (2 : Nat) ^ 7 = 128 := by norm_num
  rcases Nat.eq_zero_or_pos h with hz | hpos
  · subst hz; simp at hi
  · have hB : 2 ^ h = 2 * 2 ^ (h - 1) := by rw [← pow_succ']; congr 1; omega
    omega
theorem untouchedP_of_hdr (a : ChainAddr) (input : HashInput) (h : BitVec 128)
    (hblock : SigGolfCandidate.T3M.Extract.hdrBlock input = bytesLE 16 h)
    (htag : ∀ (l : Layer) tr leaf i step, step < 7 → h ≠ chainHeader l tr leaf i step) :
    UntouchedP a (.inl (.inr input)) := by
  intro step value hs heq
  have hb : SigGolfCandidate.T3M.Extract.hdrBlock (chainRowW a step value) =
      bytesLE 16 (chainHeader a.key.lay a.key.tree a.key.leaf a.chain step) :=
    WCT9.chainInputW_header _ _ _ _ _ _
  rw [heq, hb] at hblock
  exact htag _ _ _ _ _ hs (bytesLE_injective hblock).symm
theorem untouchedP_of_length (a : ChainAddr) (input : HashInput) (hl : input.length ≠ 64) :
    UntouchedP a (.inl (.inr input)) := by
  intro step value _ heq
  apply hl
  rw [heq, chainRowW_length]
theorem pad64_long_length {input : HashInput} (hl : 64 < input.length) : (pad64 input).length ≠ 64 := by
  have : input.length ≤ (pad64 input).length := by
    simp only [pad64, List.length_append, List.length_replicate]; omega
  omega
/-- A Merkle node tweak of the current scheme is no chain header at a chain step (`< 7`): the C4 top label's low word
is `topNodeWord heap < 4096` while a chain header's low word has byte7 193; a lower node word has byte1 `7` while a
chain header at step `< 7` has byte1 `≡ step (mod 8)`. -/
theorem merkleTweak_ne_chainHeader {lay tree heap : Nat} (hh : lay = 0 ∨ heap < 128) (l : Layer)
    (tr leaf i step : Nat) (hs : step < 7) : WCT9.merkleTweak lay tree heap ≠ chainHeader l tr leaf i step := by
  unfold WCT9.merkleTweak
  split_ifs with h0
  · intro he
    have hl := congrArg (fun x : BitVec 128 => (x.extractLsb' 0 64).toNat) he
    have hb := (WCT9.chainHeader_low_band l tr leaf i step).1
    have ht := nodeTweak_top_low tree heap
    have := topNodeWord_lt heap
    unfold tweakLow at ht
    have hn : ((nodeTweak 3 0 tree heap).extractLsb' 0 64).toNat = topNodeWord heap := by
      rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]; exact ht
    rw [hn] at hl
    omega
  · exact WCT9.lowerTweak_ne_chainHeader (hh.resolve_left h0) _ _ _ _ _ _ _ (by omega)
section ProgramsW
variable (a : ChainAddr)
theorem respectsP_lowerNodeHash (lay tree heap : Nat) (left right : Digest) (hh : lay = 0 ∨ heap < 128) :
    Respects (UntouchedP a) (WCT9.lowerNodeHash lay tree heap left right) :=
  respects_lowerNodeHash' _ _ _ _ _ (untouchedP_of_hdr a _ _ (SigGolfCandidate.T3M.Extract.hdrBlock_block4 left _ 0 right)
    fun l tr leaf i step hs => merkleTweak_ne_chainHeader hh l tr leaf i step hs)
theorem foldOK_untouchedP (lay tree h : Nat) (h7 : lay ≠ 0 → h ≤ 7) : FoldOK (UntouchedP a) lay tree h := by
  intro level i left right hlev hi
  refine untouchedP_of_hdr a _ _ (SigGolfCandidate.T3M.Extract.hdrBlock_block4 left _ 0 right)
    fun l tr leaf c step hs => merkleTweak_ne_chainHeader ?_ l tr leaf c step hs
  by_cases h0 : lay = 0
  · exact Or.inl h0
  · exact Or.inr (lowerHeap_lt' hlev (h7 h0) hi)
theorem respectsP_lowerLevels (lay tree h : Nat) (h7 : lay ≠ 0 → h ≤ 7) (leaves : List Digest)
    (hlen : leaves.length ≤ 2 ^ h) : Respects (UntouchedP a) (WCT9.lowerLevels lay tree h leaves) :=
  respects_lowerLevels' (foldOK_untouchedP a lay tree h h7) leaves hlen
theorem respectsP_buildLevelsBelow (tag lay tree h : Nat) (h7 : lay ≠ 0 → h ≤ 7) (leaves : List Digest)
    (hlen : leaves.length ≤ 2 ^ h) : Respects (UntouchedP a) (WCT9.buildLevelsBelow tag lay tree h leaves) :=
  respects_buildLevelsBelow' (foldOK_untouchedP a lay tree h h7) tag leaves hlen
theorem respectsP_lowerLeafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) (hlen : 4 ≤ ends.length) :
    Respects (UntouchedP a) (WCT9.lowerLeafHash lay tree leaf ends) :=
  respects_lowerLeafHash' _ _ _ _ (untouchedP_of_length a _ (pad64_long_length
    (SigGolfCandidate.T3.Security.Wots.Enc.leafInput_long lay tree leaf ends hlen)))
end ProgramsW
end Mask
end ClaudeWCT.W9.T3.Security.Wots
end
-- ==== merged from ClaudeWCT_W9_New_BC_Respects ====
section

namespace ClaudeWCT.W9.T3.Security.Wots.Mask
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Mask
set_option maxHeartbeats 1000000
theorem untouched_layerEncoding (a : ChainAddr) (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg)
    (counter : BitVec 32) :
    Untouched a (.inl (.inr (pad64 (WCT9.layerEncodingInput lay tree leaf msg counter)))) :=
  untouched_of_hdr a _ (rowTweak lay tree leaf)
    (ClaudeWCT.W9.T3M.BC.hdrBlock_layerEncodingInput lay tree leaf msg counter)
    (fun _ _ _ _ _ => Ne.symm (chainHeader_ne_rowTweak _ _ _ _ _ _ _ _))
/-- C2/C3 (FULL): a chain header (marker at least 128) is no encoding row tweak, whatever its witness high word. -/
theorem chainHeader_ne_rowTweakW (lay : Layer) (tree leaf i step : Nat) (up : Layer) (tree' leaf' : Nat)
    (hi : BitVec 64) : chainHeader lay tree leaf i step ≠ WCT9.rowTweakW up tree' leaf' hi := by
  intro h
  have hc := chainHeader_tweakMarker lay tree leaf i step
  rw [h] at hc
  unfold WCT9.rowTweakW at hc
  rw [append64_marker, hyperWord_toNat] at hc
  omega
theorem untouched_layerEncodingP (a : ChainAddr) (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg)
    (counter : BitVec 32) (pad : BitVec 96) (padR : Digest) (hi : BitVec 64) :
    Untouched a (.inl (.inr (pad64 (ClaudeWCT.W9.T3M.layerEncodingInputP lay tree leaf msg counter pad padR hi)))) :=
  untouched_of_hdr a _ (WCT9.rowTweakW lay tree leaf hi)
    (ClaudeWCT.W9.T3M.BC.hdrBlock_layerEncodingInputP lay tree leaf msg counter pad padR hi)
    (fun _ _ _ _ _ => Ne.symm (chainHeader_ne_rowTweakW _ _ _ _ _ _ _ _ _))
theorem respects_layerEncoding (a : ChainAddr) (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg)
    (counter : BitVec 32) :
    Respects (Untouched a) (ClaudeWCT.WCT9.encodingHash lay (WCT9.layerEncodingInput lay tree leaf msg counter)) :=
  Respects.map (WCT9.encodingAnswer lay) (Respects.publicHash _ (untouched_layerEncoding a lay tree leaf msg counter))
theorem respects_layerCounterSearch (a : ChainAddr) (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) :
    ∀ fuel counter, Respects (Untouched a) (WCT9.layerCounterSearch lay tree leaf msg counter fuel) := by
  intro fuel
  induction fuel with
  | zero => intro counter; exact Respects.pure' _
  | succ fuel ih =>
      intro counter
      simp only [WCT9.layerCounterSearch]
      refine Respects.bind (respects_layerEncoding a _ _ _ _ _) fun answer => ?_
      split
      · exact ih _
      · exact Respects.pure' _
theorem respectsP_layerCounterSearch (a : ChainAddr) (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg)
    (fuel counter : Nat) :
    Respects (UntouchedP a) (WCT9.layerCounterSearch lay tree leaf msg counter fuel) :=
  Respects.untouchedP (fun c => respects_layerCounterSearch c lay tree leaf msg fuel counter) a
end ClaudeWCT.W9.T3.Security.Wots.Mask
namespace ClaudeWCT.W9.T3.Security.Wots.Ref
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Ref
theorem shortRespects_encodingHash (lay : Layer) (input : HashInput)
    (h : (pad64 input).length ≤ SeccLaw.maxInputLength) : ShortRespects (WCT9.encodingHash lay input) := by
  intro A T hAT
  rw [WCT9.eval_encodingHash, WCT9.eval_encodingHash, hAT.public _ h]
theorem layerCounterSearch_respects (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter fuel : Nat) :
    ShortRespects (WCT9.layerCounterSearch lay tree leaf msg counter fuel) := by
  induction fuel generalizing counter with
  | zero => exact ShortRespects.pure' _
  | succ fuel ih =>
      unfold WCT9.layerCounterSearch
      refine ShortRespects.bind (shortRespects_encodingHash lay _ ?_) fun answer => ?_
      · rw [← ClaudeWCT.W9.T3M.BC.pad64_layerEncodingInputP_zero, ClaudeWCT.W9.T3M.BC.layerEncodingRow_length]
        unfold SeccLaw.maxInputLength
        omega
      · split
        · exact ih _
        · exact ShortRespects.pure' _
end ClaudeWCT.W9.T3.Security.Wots.Ref
end
-- ==== merged from ClaudeWCT_W9_T3_FullCache_NativeBudgetB1_PairRows ====
section

namespace ClaudeWCT.W9.T3.PairRows
open OracleComp OracleSpec ENNReal
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SigGolfCandidate.T3 hiding digestSearch admissible
open SigGolfCandidate.T3.Sampling (RCache roRun V publicProgram digestTrial V_publicSearch public_randomOracle)
open ClaudeWCT.W9.T3.ProducerV5 (producerEncodingDecode)
open SigGolfCandidate.T3.Freshness (Avoids RowQ SearchQ RowQ.searchQ searchQ_digest avoids_pure avoids_bind preserves
  avoids_shortHash_of_ne)
open ClaudeWCT.WCT9 (LayerMsg layerEncodingInput pairEncodingInputP layerCounterSearch)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
def pairTrial (lay : Layer) (tree leaf : Nat) (left right : Digest) (counter : Nat) : HashInput :=
  pairEncodingInputP lay tree leaf left right (BitVec.ofNat 32 counter) 0
def layerTrial (lay : Layer) (tree leaf : Nat) (msg : LayerMsg) (counter : Nat) : HashInput :=
  pad64 (layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 counter))
def msgLeft : LayerMsg → Digest
  | .forest root => root
  | .pair left _ => left
def msgRight : LayerMsg → Digest
  | .forest _ => 0
  | .pair _ right => right
theorem pairTrial_length (lay : Layer) (tree leaf : Nat) (left right : Digest) (counter : Nat) :
    (pairTrial lay tree leaf left right counter).length = 64 := by
  simp [pairTrial, pairEncodingInputP, bytesLE_length]
theorem pad64_pairTrial (lay : Layer) (tree leaf : Nat) (left right : Digest) (counter : Nat) :
    pad64 (pairTrial lay tree leaf left right counter) = pairTrial lay tree leaf left right counter := by
  simp [pad64, pairTrial_length]
theorem layerTrial_eq (lay : Layer) (tree leaf : Nat) (msg : LayerMsg) (counter : Nat) :
    layerTrial lay tree leaf msg counter = pairTrial lay tree leaf (msgLeft msg) (msgRight msg) counter := by
  cases msg with
  | forest root =>
      have h12 : bytesLE 12 (0 : BitVec 96) = List.replicate 12 0 := by decide
      have h16 : bytesLE 16 (0 : Digest) = List.replicate 16 0 := by decide
      simp only [layerTrial, pairTrial, layerEncodingInput, encodingInput, pairEncodingInputP, msgLeft,
        msgRight, pad64, List.length_append, bytesLE_length, h12, h16, List.append_assoc,
        List.replicate_append_replicate]
  | pair left right =>
      exact pad64_pairTrial lay tree leaf left right counter
theorem layerTrial_length (lay : Layer) (tree leaf : Nat) (msg : LayerMsg) (counter : Nat) :
    (layerTrial lay tree leaf msg counter).length = 64 := by
  rw [layerTrial_eq, pairTrial_length]
theorem pairTrial_coordinates {lay lay' : Layer} {tree tree' leaf leaf' : Nat} {left left' right right' : Digest}
    {counter counter' : Nat} (hl : leaf < 2 ^ height lay) (hr : tree * 2 ^ height lay + leaf < 2 ^ 32)
    (hl' : leaf' < 2 ^ height lay') (hr' : tree' * 2 ^ height lay' + leaf' < 2 ^ 32)
    (hc : counter < 2 ^ 32) (hc' : counter' < 2 ^ 32)
    (he : pairTrial lay tree leaf left right counter = pairTrial lay' tree' leaf' left' right' counter') :
    lay = lay' ∧ tree = tree' ∧ leaf = leaf' ∧ left = left' ∧ right = right' ∧ counter = counter' := by
  unfold pairTrial pairEncodingInputP at he
  obtain ⟨he, hR⟩ := List.append_inj he (by simp [bytesLE_length])
  obtain ⟨he, -⟩ := List.append_inj he (by simp [bytesLE_length])
  obtain ⟨he, hC⟩ := List.append_inj he (by simp [bytesLE_length])
  obtain ⟨hL, hH⟩ := List.append_inj he (by simp [bytesLE_length])
  obtain ⟨hlay, htree, hleaf⟩ := rowTweak_injective hl hr hl' hr' (bytesLE_injective hH)
  have hC := congrArg BitVec.toNat (bytesLE_injective hC)
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hc'] at hC
  exact ⟨hlay, htree, hleaf, bytesLE_injective hL, bytesLE_injective hR, hC⟩
theorem pairTrial_injective (lay : Layer) (tree leaf : Nat) (left right : Digest) {c c' : Nat}
    (hc : c < 2 ^ 32) (hc' : c' < 2 ^ 32)
    (he : pairTrial lay tree leaf left right c = pairTrial lay tree leaf left right c') : c = c' := by
  unfold pairTrial pairEncodingInputP at he
  obtain ⟨he, -⟩ := List.append_inj he (by simp [bytesLE_length])
  obtain ⟨he, -⟩ := List.append_inj he (by simp [bytesLE_length])
  obtain ⟨-, hC⟩ := List.append_inj he (by simp [bytesLE_length])
  have hC := congrArg BitVec.toNat (bytesLE_injective hC)
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hc'] using hC
theorem layerTrial_injective (lay : Layer) (tree leaf : Nat) (msg : LayerMsg) {c c' : Nat}
    (hc : c < 2 ^ 32) (hc' : c' < 2 ^ 32)
    (he : layerTrial lay tree leaf msg c = layerTrial lay tree leaf msg c') : c = c' := by
  rw [layerTrial_eq, layerTrial_eq] at he
  exact pairTrial_injective lay tree leaf _ _ hc hc' he
@[simp] theorem queryHeader_pairTrial (lay : Layer) (tree leaf : Nat) (left right : Digest) (counter : Nat) :
    SigGolfCandidate.T3.QuerySpace.queryHeader (pairTrial lay tree leaf left right counter) =
      bytesLE 16 (rowTweak lay tree leaf) := by
  simp [SigGolfCandidate.T3.QuerySpace.queryHeader, pairTrial, pairEncodingInputP, List.append_assoc,
    bytesLE_length]
theorem rowQ_pairTrial (lay : Layer) (tree leaf : Nat) (left right : Digest) (counter : Nat) :
    RowQ (pairTrial lay tree leaf left right counter) :=
  ⟨rowTweak lay tree leaf, queryHeader_pairTrial .., rowTweak_marker .., rowTweak_tag .., rowTweak_high ..⟩
theorem pairTrial_ne_of_layer {lay other : Layer} (hne : lay ≠ other) (tree leaf : Nat) (left right : Digest)
    (counter : Nat) (tree' leaf' : Nat) (left' right' : Digest) (counter' : Nat) :
    pairTrial lay tree leaf left right counter ≠ pairTrial other tree' leaf' left' right' counter' := by
  intro he
  have hh := congrArg SigGolfCandidate.T3.QuerySpace.queryHeader he
  simp only [queryHeader_pairTrial] at hh
  have hw := (append64_inj (bytesLE_injective hh)).2
  have hl := congrArg (fun w : BitVec 64 => w.toNat / 2 ^ 48 % 256) hw
  simp only [hyperWord_toNat] at hl
  have h1 := lay.isLt
  have h2 := other.isLt
  have := Nat.mod_lt (tree * 2 ^ height lay + leaf) (show 0 < 2 ^ 32 by decide)
  have := Nat.mod_lt (tree' * 2 ^ height other + leaf') (show 0 < 2 ^ 32 by decide)
  exact hne (Fin.ext (by omega))
theorem pairTrial_ne_digestTrial (lay : Layer) (tree leaf : Nat) (left right : Digest) (counter : Nat)
    (rho : Digest) (message : Message) (ctr : Nat) :
    pairTrial lay tree leaf left right counter ≠ digestTrial rho message ctr := by
  intro he
  have hh := congrArg SigGolfCandidate.T3.QuerySpace.queryHeader he
  rw [queryHeader_pairTrial, SigGolfCandidate.T3.QuerySpace.queryHeader_digest] at hh
  exact digestHeader_ne_rowTweak _ lay tree leaf (bytesLE_injective hh).symm
theorem layerCounterSearch_public (lay : Layer) (tree leaf : Nat) (msg : LayerMsg) :
    ∀ fuel counter, layerCounterSearch lay tree leaf msg counter fuel =
      publicProgram (SphincsSecurity.Completeness.searchLoop
        (layerTrial lay tree leaf msg) (producerEncodingDecode lay)
        (fun c digits => pure (BitVec.ofNat 32 c, digits)) fuel counter) := by
  intro fuel
  induction fuel with
  | zero => intro counter; rfl
  | succ fuel ih =>
      intro counter
      rw [ClaudeWCT.WCT9.layerCounterSearch, SphincsSecurity.Completeness.searchLoop]
      simp only [publicProgram, simulateQ_bind, simulateQ_spec_query,
        SphincsSecurity.Concrete.oracleHash, HasQuery.query, SigGolfCandidate.T3.Sampling.publicHandler,
        ClaudeWCT.WCT9.encodingHash, shortHash, publicHash, map_eq_bind_pure_comp, Function.comp_apply,
        bind_assoc, pure_bind, layerTrial, producerEncodingDecode]
      apply bind_congr
      intro answer
      cases hd : ClaudeWCT.WCT9.producerDecode lay (ClaudeWCT.WCT9.encodingAnswer lay answer) <;>
        simp only [simulateQ_map, simulateQ_pure, map_pure, ih, publicProgram]
theorem V_layerCounterSearch (secret : BitVec 256) (z b : ENNReal) (hb : 1 ≤ b)
    (lay : Layer) (tree leaf : Nat) (msg : LayerMsg)
    (hstep : z * (SphincsSecurity.Completeness.failMass (producerEncodingDecode lay) * b +
      (1 - SphincsSecurity.Completeness.failMass (producerEncodingDecode lay))) ≤ b)
    (fuel counter : Nat) (hlimit : counter + fuel ≤ 2 ^ 32) (cache : RCache)
    (hfresh : ∀ c, counter ≤ c → c < 2 ^ 32 → cache (layerTrial lay tree leaf msg c) = none) :
    V secret z (layerCounterSearch lay tree leaf msg counter fuel) cache ≤ b := by
  rw [layerCounterSearch_public]
  exact V_publicSearch secret z b hb _ _ _ (2 ^ 32)
    (fun c _ => layerTrial_length lay tree leaf msg c)
    (fun _ _ hl hr he => layerTrial_injective lay tree leaf msg hl hr he)
    hstep fuel counter hlimit cache hfresh
theorem layerCounterSearch_failure (secret : BitVec 256) (lay : Layer) (tree leaf : Nat) (msg : LayerMsg)
    (fuel counter : Nat) (hlimit : counter + fuel ≤ 2 ^ 32)
    (cache : QueryCache SphincsSecurity.HashSpec)
    (hfresh : ∀ c, counter ≤ c → c < 2 ^ 32 → cache (layerTrial lay tree leaf msg c) = none) :
    Pr[fun result => result.1 = none |
      (simulateQ SphincsSecurity.romImpl
        (realize secret (layerCounterSearch lay tree leaf msg counter fuel))).run cache] ≤
      SphincsSecurity.Completeness.failMass (producerEncodingDecode lay) ^ fuel := by
  rw [layerCounterSearch_public, public_randomOracle]
  exact SphincsSecurity.Completeness.probEvent_searchLoop _ _ _ (2 ^ 32)
    (fun _ _ hl hr he => layerTrial_injective lay tree leaf msg hl hr he)
    fuel counter hlimit cache hfresh
theorem bound_layerCounterSearch (lay : Layer) (tree leaf : Nat) (msg : LayerMsg) :
    ∀ fuel counter, Cost.CBound (Cost.CounterResult lay) fuel (layerCounterSearch lay tree leaf msg counter fuel) := by
  intro fuel
  induction fuel with
  | zero =>
      intro counter
      exact .pure none 0 (by simp [Cost.CounterResult])
  | succ fuel ih =>
      intro counter
      unfold ClaudeWCT.WCT9.layerCounterSearch
      refine (ClaudeWCT.WCT9.Cost.bound_encodingHash lay (layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 counter)) 1
        (by cases msg <;> simp [layerEncodingInput, encodingInput, pairEncodingInputP, bytesLE_length])
        (by rw [show pad64 (layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 counter)) =
              layerTrial lay tree leaf msg counter from rfl, layerTrial_length])).bind'
        (l := fuel) (fun answer _ => ?_) (by omega)
      cases hs : ClaudeWCT.WCT9.producerDecode lay answer with
      | none => exact ih (counter + 1)
      | some digits =>
          have hd := ClaudeWCT.WCT9.producerDecode_decode hs
          refine .pure (some (BitVec.ofNat 32 counter, digits)) fuel ?_
          intro other values hv
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hv)
          exact ⟨(decode_length_sum hd).1, (decode_length_sum hd).2, Cost.validDigits_decode hd⟩
theorem layerCounterSearch_none_iff (answers : Correctness.Answers) (lay : Layer) (tree leaf : Nat)
    (msg : LayerMsg) :
    ∀ fuel counter,
      evalWithAnswerFn answers (layerCounterSearch lay tree leaf msg counter fuel) = none ↔
      ∀ offset, offset < fuel → ClaudeWCT.WCT9.producerDecode lay (evalWithAnswerFn answers
        (ClaudeWCT.WCT9.encodingHash lay (layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 (counter + offset))))) = none := by
  intro fuel
  induction fuel with
  | zero => intro counter; simp [ClaudeWCT.WCT9.layerCounterSearch]
  | succ fuel ih =>
      intro counter
      simp only [ClaudeWCT.WCT9.layerCounterSearch, evalWithAnswerFn_bind]
      cases hd : ClaudeWCT.WCT9.producerDecode lay (evalWithAnswerFn answers
        (ClaudeWCT.WCT9.encodingHash lay (layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 counter)))) with
      | none =>
          simp only [hd, ih]
          constructor
          · intro hall offset hoff
            cases offset with
            | zero => simpa using hd
            | succ offset =>
                simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hall offset (by omega)
          · intro hall offset hoff
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hall (offset + 1) (by omega)
      | some digits =>
          simp only [hd, evalWithAnswerFn_pure, reduceCtorEq, false_iff]
          intro hall
          have := hall 0 (by omega)
          simp only [Nat.add_zero, hd, reduceCtorEq] at this
theorem eval_shortHash_layer (answers : Correctness.Answers) (lay : Layer) (tree leaf : Nat) (msg : LayerMsg)
    (counter : Nat) :
    evalWithAnswerFn answers (ClaudeWCT.WCT9.encodingHash lay (layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 counter))) =
      ClaudeWCT.WCT9.encodingAnswer lay
        (answers (.inl (.inr (pairTrial lay tree leaf (msgLeft msg) (msgRight msg) counter)))) := by
  rw [ClaudeWCT.WCT9.eval_encodingHash, ← layerTrial_eq]
  rfl
theorem eval_publicHash_layer (answers : Correctness.Answers) (lay : Layer) (tree leaf : Nat) (msg : LayerMsg)
    (counter : Nat) :
    evalWithAnswerFn answers (publicHash (layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 counter))) =
      answers (.inl (.inr (pairTrial lay tree leaf (msgLeft msg) (msgRight msg) counter))) := by
  rw [← layerTrial_eq]
  rfl
theorem layerCounterSearch_forest_eval (answers : Correctness.Answers) (lay : Layer) (tree leaf : Nat)
    (root : Digest) : ∀ fuel counter,
      evalWithAnswerFn answers (layerCounterSearch lay tree leaf (.forest root) counter fuel) =
        evalWithAnswerFn answers (layerCounterSearch lay tree leaf (.pair root 0) counter fuel) := by
  intro fuel
  induction fuel with
  | zero => intro counter; rfl
  | succ fuel ih =>
      intro counter
      have hs : evalWithAnswerFn answers (ClaudeWCT.WCT9.encodingHash lay (layerEncodingInput lay tree leaf (.forest root)
            (BitVec.ofNat 32 counter))) =
          evalWithAnswerFn answers (ClaudeWCT.WCT9.encodingHash lay (layerEncodingInput lay tree leaf (.pair root 0)
            (BitVec.ofNat 32 counter))) := by
        rw [eval_shortHash_layer, eval_shortHash_layer]
        rfl
      simp only [ClaudeWCT.WCT9.layerCounterSearch, evalWithAnswerFn_bind, hs]
      cases hd : ClaudeWCT.WCT9.producerDecode lay (evalWithAnswerFn answers (ClaudeWCT.WCT9.encodingHash lay (layerEncodingInput lay tree leaf
        (.pair root 0) (BitVec.ofNat 32 counter)))) <;> simp only [hd, ih]
def PairFreshBelow (n : Nat) (cache : RCache) : Prop :=
  ∀ lay : Layer, lay.val < n → ∀ tree leaf left right c, c < 2 ^ 32 →
    cache (pairTrial lay tree leaf left right c) = none
def AllSearchesFreshBC (cache : RCache) : Prop :=
  (∀ rho message c, c < 2 ^ 32 → cache (digestTrial rho message c) = none) ∧ PairFreshBelow 4 cache
@[simp] theorem allSearchesFreshBC_empty : AllSearchesFreshBC ∅ := by
  constructor
  · intro rho message c hc; rfl
  · intro lay hl tree leaf left right c hc; rfl
theorem PairFreshBelow.layerTrial {n : Nat} {cache : RCache} (h : PairFreshBelow n cache) (lay : Layer)
    (hl : lay.val < n) (tree leaf : Nat) (msg : LayerMsg) (c : Nat) (hc : c < 2 ^ 32) :
    cache (layerTrial lay tree leaf msg c) = none := by
  rw [layerTrial_eq]
  exact h lay hl tree leaf _ _ c hc
theorem PairFreshBelow.mono {n m : Nat} {cache : RCache} (h : PairFreshBelow n cache) (hm : m ≤ n) :
    PairFreshBelow m cache :=
  fun lay hl => h lay (by omega)
theorem avoids_layerCounterSearch (secret : BitVec 256) {lay other : Layer} (hne : lay ≠ other)
    (tree leaf : Nat) (msg : LayerMsg) (counter fuel : Nat)
    (tree' leaf' : Nat) (left' right' : Digest) (counter' : Nat) :
    Avoids secret (pairTrial other tree' leaf' left' right' counter')
      (layerCounterSearch lay tree leaf msg counter fuel) := by
  induction fuel generalizing counter with
  | zero => exact avoids_pure _ _ _
  | succ fuel ih =>
      unfold ClaudeWCT.WCT9.layerCounterSearch
      apply avoids_bind
      · apply avoids_shortHash_of_ne
        rw [show pad64 (layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 counter)) =
          layerTrial lay tree leaf msg counter from rfl, layerTrial_eq]
        exact pairTrial_ne_of_layer hne tree leaf _ _ counter tree' leaf' left' right' counter'
      · intro answer
        split
        · exact ih _
        · exact avoids_pure _ _ _
theorem preserves_pairBelow {α : Type} (secret : BitVec 256) (program : M α)
    (h : ∀ target, RowQ target → Avoids secret target program)
    (n : Nat) (cache : RCache) (hc : PairFreshBelow n cache) (result : α × RCache)
    (hr : result ∈ support (roRun secret program cache)) : PairFreshBelow n result.2 := by
  intro lay hl tree leaf left right c hlt
  rw [preserves secret _ program (h _ (rowQ_pairTrial ..)) cache result hr]
  exact hc lay hl tree leaf left right c hlt
theorem preserves_allSearchesBC {α : Type} (secret : BitVec 256) (program : M α)
    (h : ∀ target, SearchQ target → Avoids secret target program)
    (cache : RCache) (hc : AllSearchesFreshBC cache) (result : α × RCache)
    (hr : result ∈ support (roRun secret program cache)) : AllSearchesFreshBC result.2 := by
  constructor
  · intro rho message c hlt
    rw [preserves secret _ program (h _ (searchQ_digest ..)) cache result hr]
    exact hc.1 rho message c hlt
  · exact preserves_pairBelow secret program (fun target ht => h target ht.searchQ) 4 cache hc.2 result hr
theorem avoids_digestSearch_encoding (secret : BitVec 256) (target : HashInput) (ht : RowQ target)
    (rho : Digest) (message : Message) (counter fuel : Nat) :
    Avoids secret target (ClaudeWCT.WCT9.digestSearch rho message counter fuel) := by
  induction fuel generalizing counter with
  | zero => unfold ClaudeWCT.WCT9.digestSearch; exact avoids_pure _ _ _
  | succ fuel ih =>
      unfold ClaudeWCT.WCT9.digestSearch
      refine avoids_bind (SigGolfCandidate.T3.Freshness.avoids_digest_encoding secret target ht rho message _) ?_
      intro output
      split
      · exact avoids_pure _ _ _
      · exact ih _
theorem digestSearch_preserves_pairBelow (secret : BitVec 256) (rho : Digest) (message : Message)
    (counter fuel : Nat) (cache : RCache) (hc : AllSearchesFreshBC cache) (result : _ × RCache)
    (hr : result ∈ support (roRun secret (ClaudeWCT.WCT9.digestSearch rho message counter fuel) cache)) :
    PairFreshBelow 4 result.2 :=
  preserves_pairBelow secret _ (fun target ht => avoids_digestSearch_encoding secret target ht rho message _ _)
    4 cache hc.2 result hr
theorem privateMac_preserves_fresh (secret : BitVec 256) (region : Region) (cache : RCache)
    (hc : AllSearchesFreshBC cache) (result : _ × RCache)
    (hr : result ∈ support (roRun secret (privateMac region) cache)) : AllSearchesFreshBC result.2 :=
  preserves_allSearchesBC secret _
    (fun target ht => SigGolfCandidate.T3.Freshness.avoids_privateMac secret target ht region) cache hc result hr
theorem privateNonce_preserves_fresh (secret : BitVec 256) (message : Message) (cache : RCache)
    (hc : AllSearchesFreshBC cache) (result : _ × RCache)
    (hr : result ∈ support (roRun secret (privateNonce message) cache)) : AllSearchesFreshBC result.2 :=
  preserves_allSearchesBC secret _
    (fun target ht => SigGolfCandidate.T3.Freshness.avoids_privateNonce secret target ht message) cache hc result hr
theorem keygen_fresh_from_empty_bc (secret : BitVec 256) (result : (Digest × Cache) × RCache)
    (hr : result ∈ support (roRun secret keygen ∅)) : AllSearchesFreshBC result.2 :=
  preserves_allSearchesBC secret keygen
    (fun target ht => SigGolfCandidate.T3.Freshness.avoids_keygen secret target ht) ∅
    allSearchesFreshBC_empty result hr
end ClaudeWCT.W9.T3.PairRows

namespace ClaudeWCT.W9.T3.CanonicalSearch
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3
open SigGolfCandidate.T3.Sampling
open SphincsSecurity.Completeness
open ClaudeWCT.WCT9
open ClaudeWCT.W9.T3.PairRows
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The selected 256-bit oracle answer, with the canonical per-leaf floor: the producer's digits and the
selected half (`true` = LOW; configuration (1)+(2)). -/
def decoder (lay : Layer) (floor : Nat) (answer : HashOutput) : Option (List Nat × Bool) :=
  CanonicalPolicy.producerDecodeOut lay floor answer

theorem search_public (lay : Layer) (floor tree leaf : Nat) (msg : LayerMsg) :
    ∀ fuel counter, CanonicalPolicy.layerCounterSearchAt lay floor tree leaf msg counter fuel =
      publicProgram (searchLoop (layerTrial lay tree leaf msg) (decoder lay floor)
        (fun c found => pure (BitVec.ofNat 32 c, found)) fuel counter) := by
  intro fuel
  induction fuel with
  | zero => intro counter; rfl
  | succ fuel ih =>
      intro counter
      rw [CanonicalPolicy.layerCounterSearchAt, searchLoop]
      simp only [publicProgram, simulateQ_bind, simulateQ_spec_query,
        SphincsSecurity.Concrete.oracleHash, HasQuery.query,
        SigGolfCandidate.T3.Sampling.publicHandler,
        publicHash, map_eq_bind_pure_comp, Function.comp_apply,
        bind_assoc, pure_bind, layerTrial, decoder]
      apply bind_congr
      intro answer
      cases hd : CanonicalPolicy.producerDecodeOut lay floor answer <;>
        simp only [simulateQ_map, simulateQ_pure, map_pure, ih, publicProgram]

theorem search_failure (secret : BitVec 256) (lay : Layer) (floor tree leaf : Nat)
    (msg : LayerMsg) (fuel counter : Nat) (hlimit : counter + fuel ≤ 2 ^ 32)
    (cache : QueryCache SphincsSecurity.HashSpec)
    (hfresh : ∀ c, counter ≤ c → c < 2 ^ 32 →
      cache (layerTrial lay tree leaf msg c) = none) :
    Pr[fun result => result.1 = none |
      (simulateQ SphincsSecurity.romImpl (realize secret
        (CanonicalPolicy.layerCounterSearchAt lay floor tree leaf msg counter fuel))).run cache] ≤
      failMass (decoder lay floor) ^ fuel := by
  rw [search_public, public_randomOracle]
  exact probEvent_searchLoop _ _ _ (2 ^ 32)
    (fun _ _ hl hr he => layerTrial_injective lay tree leaf msg hl hr he)
    fuel counter hlimit cache hfresh

/-- A rejection search with a value-dependent continuation. The invariant tracks
fresh rows of later canonical ancestors/descendants independently of the floor. -/
theorem V_search_bind {β γ δ : Type} (secret : BitVec 256) (z b : ENNReal)
    (inputs : Nat → HashInput) (dec : HashOutput → Option β)
    (result : Nat → β → γ) (next : Option γ → M δ) (weight : β → ENNReal)
    (G : RCache → Prop) (bound : Nat)
    (hinput : ∀ counter, counter < bound → (inputs counter).length = 64)
    (hinj : ∀ left right, left < bound → right < bound →
      inputs left = inputs right → left = right)
    (hG : ∀ cache, G cache → ∀ counter, counter < bound → ∀ answer,
      G (cache.cacheQuery (inputs counter) answer))
    (hnone : ∀ cache, G cache → V secret z (next none) cache ≤ b)
    (hsome : ∀ cache, G cache → ∀ counter, counter < bound → ∀ answer value,
      dec answer = some value →
      V secret z (next (some (result counter value)))
        (cache.cacheQuery (inputs counter) answer) ≤ weight value)
    (hstep : z * (acceptedWeight dec weight + failMass dec * b) ≤ b) :
    ∀ fuel counter, counter + fuel ≤ bound → ∀ cache, G cache →
      (∀ c, counter ≤ c → c < bound → cache (inputs c) = none) →
      V secret z ((publicProgram (searchLoop inputs dec
        (fun c value => pure (result c value)) fuel counter)) >>= next) cache ≤ b := by
  intro fuel
  induction fuel with
  | zero =>
      intro counter _ cache hg _
      simpa only [searchLoop, publicProgram, simulateQ_pure, pure_bind] using hnone cache hg
  | succ fuel ih =>
      intro counter hlimit cache hg hfresh
      rw [publicSearch_succ, bind_assoc, V_publicQuery, hinput counter (by omega)]
      simp only [show (64 : Nat) / 64 = 1 by decide, pow_one]
      rw [expectedValue_fresh _ _ (hfresh counter le_rfl (by omega))]
      calc
        _ ≤ z * expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
            (fun answer => (dec answer).elim b weight) := by
          apply mul_le_mul' le_rfl
          apply expectedValue_mono
          intro answer
          cases hd : dec answer with
          | some value =>
              simp only [pure_bind, Option.elim_some]
              exact hsome cache hg counter (by omega) answer value hd
          | none =>
              simp only [Option.elim_none]
              apply ih (counter + 1) (by omega) _ (hG cache hg counter (by omega) answer)
              intro c hstart hc
              rw [QueryCache.cacheQuery_of_ne]
              · exact hfresh c (by omega) hc
              · intro he
                have := hinj c counter hc (by omega) he
                omega
        _ = z * (acceptedWeight dec weight + failMass dec * b) := by
          rw [uniform_decoder_weight]
        _ ≤ b := hstep

end ClaudeWCT.W9.T3.CanonicalSearch

namespace ClaudeWCT.W9.T3.CanonicalSearch
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
open SphincsSecurity.Completeness
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem acceptedWeight_mul {β : Type} (dec : HashOutput → Option β)
    (weight : β → ENNReal) (factor : ENNReal) :
    acceptedWeight dec (fun value => factor * weight value) =
      factor * acceptedWeight dec weight := by
  unfold acceptedWeight
  have he (answer : HashOutput) :
      (dec answer).elim 0 (fun value => factor * weight value) =
        factor * (dec answer).elim 0 weight := by
    cases dec answer <;> simp
  simp_rw [he]
  exact ev_const_mul _ _ _

theorem scaled_step {β : Type} (z b factor : ENNReal) (dec : HashOutput → Option β)
    (weight : β → ENNReal)
    (hstep : z * (acceptedWeight dec weight + failMass dec * b) ≤ b) :
    z * (acceptedWeight dec (fun value => factor * weight value) +
      failMass dec * (factor * b)) ≤ factor * b := by
  rw [acceptedWeight_mul]
  have he : z * (factor * acceptedWeight dec weight + failMass dec * (factor * b)) =
      factor * (z * (acceptedWeight dec weight + failMass dec * b)) := by ring
  rw [he]
  exact mul_le_mul' le_rfl hstep

end ClaudeWCT.W9.T3.CanonicalSearch

namespace ClaudeWCT.W9.T3.CanonicalSearch
open OracleComp OracleSpec OracleComp.EvalDist ENNReal Finset
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
open SphincsSecurity.Completeness
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

private theorem expected_finite_sum {α ι : Type} [DecidableEq ι] (law : ProbComp α)
    (s : Finset ι) (f : ι → α → ENNReal) :
    expectedValue law (fun a => ∑ i ∈ s, f i a) =
      ∑ i ∈ s, expectedValue law (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [expectedValue_def]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [expectedValue_add, ih]

/-- Group success-weighted continuation costs by a finite credit label. -/
theorem acceptedWeight_labels {β ι : Type} [Fintype ι] [DecidableEq ι]
    (dec : HashOutput → Option β) (label : β → ι) (weight : ι → ENNReal) :
    acceptedWeight dec (fun value => weight (label value)) =
      ∑ i : ι, Pr[fun answer => ∃ value, dec answer = some value ∧ label value = i |
        ($ᵗ HashOutput : ProbComp HashOutput)] * weight i := by
  classical
  have he (answer : HashOutput) :
      (dec answer).elim 0 (fun value => weight (label value)) =
        ∑ i : ι, (if ∃ value, dec answer = some value ∧ label value = i
          then 1 else 0) * weight i := by
    cases hd : dec answer with
    | none => simp
    | some value =>
        simp only [Option.elim_some]
        rw [Finset.sum_eq_single (label value)]
        · rw [if_pos (show ∃ other, some value = some other ∧ label other = label value
            from ⟨value, rfl, rfl⟩), one_mul]
        · intro i _ hi
          have hn : ¬ ∃ other, some value = some other ∧ label other = i := by
            rintro ⟨other, heq, hlabel⟩
            cases heq
            exact hi hlabel.symm
          rw [if_neg hn, zero_mul]
        · simp
  unfold acceptedWeight
  simp_rw [he]
  rw [expected_finite_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [expectedValue_mul_const, expectedValue_ite_one]

/-- The failure mass is the complement of the total finite labelled mass. -/
theorem failMass_labels {β ι : Type} [Fintype ι] [DecidableEq ι]
    (dec : HashOutput → Option β) (label : β → ι) :
    failMass dec = 1 - ∑ i : ι, Pr[fun answer =>
      ∃ value, dec answer = some value ∧ label value = i |
      ($ᵗ HashOutput : ProbComp HashOutput)] := by
  classical
  have hm : acceptedWeight dec (fun _ => (1 : ENNReal)) + failMass dec = 1 := by
    have h := uniform_decoder_weight dec (fun _ => (1 : ENNReal)) 1
    have he (answer : HashOutput) : (dec answer).elim (1 : ENNReal) (fun _ => 1) = 1 := by
      cases dec answer <;> rfl
    simp_rw [he] at h
    rw [expectedValue_const (by simp)] at h
    simpa only [mul_one] using h.symm
  have hs := acceptedWeight_labels dec label (fun _ => (1 : ENNReal))
  simp only [mul_one] at hs
  rw [hs] at hm
  have hle : (∑ x, Pr[fun answer => ∃ value, dec answer = some value ∧ label value = x |
      ($ᵗ HashOutput : ProbComp HashOutput)]) ≤ 1 := by
    calc
      _ ≤ _ + failMass dec := le_add_right le_rfl
      _ = 1 := hm
  exact ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top (by simp) hle)
    ((add_comm _ _).trans hm)

end ClaudeWCT.W9.T3.CanonicalSearch

namespace ClaudeWCT.W9.T3.CanonicalSearch
open OracleComp OracleSpec OracleComp.EvalDist ENNReal Finset
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
open SphincsSecurity.Completeness
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem acceptedWeight_nat_labels {β : Type} (n : Nat) [NeZero n]
    (dec : HashOutput → Option β) (credit : β → Nat) (weight : Nat → ENNReal)
    (hbound : ∀ answer value, dec answer = some value → credit value < n) :
    acceptedWeight dec (fun value => weight (credit value)) =
      ∑ i : Fin n, Pr[fun answer => ∃ value,
        dec answer = some value ∧ credit value = i.val |
        ($ᵗ HashOutput : ProbComp HashOutput)] * weight i.val := by
  classical
  let label : β → Fin n := fun value => Fin.ofNat n (credit value)
  have he : acceptedWeight dec (fun value => weight (credit value)) =
      acceptedWeight dec (fun value => weight (label value).val) := by
    unfold acceptedWeight
    congr 1
    funext answer
    cases hd : dec answer with
    | none => rfl
    | some value =>
        simp only [Option.elim_some, label, Fin.val_ofNat]
        rw [Nat.mod_eq_of_lt (hbound answer value hd)]
  rw [he, acceptedWeight_labels dec label (fun i => weight i.val)]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply probEvent_congr'
  · intro answer _
    constructor
    · rintro ⟨value, hd, hi⟩
      refine ⟨value, hd, ?_⟩
      have hv := congrArg Fin.val hi
      simpa only [label, Fin.val_ofNat, Nat.mod_eq_of_lt (hbound answer value hd)] using hv
    · rintro ⟨value, hd, hi⟩
      exact ⟨value, hd, Fin.ext (by
        simp only [label, Fin.val_ofNat, Nat.mod_eq_of_lt (hbound answer value hd), hi, Nat.mod_eq_of_lt i.isLt])⟩
  · rfl

end ClaudeWCT.W9.T3.CanonicalSearch

namespace ClaudeWCT.W9.T3.CanonicalSearch
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
open SphincsSecurity.Completeness
open ClaudeWCT.WCT9 ClaudeWCT.W9.T3.PairRows
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def RowsFreshFrom (stage : Nat) (cache : RCache) : Prop :=
  ∀ lay : Layer, stage ≤ lay.val → ∀ tree leaf left right counter,
    counter < 2 ^ 32 → cache (pairTrial lay tree leaf left right counter) = none

theorem RowsFreshFrom.mono {stage next : Nat} {cache : RCache}
    (h : RowsFreshFrom stage cache) (hle : stage ≤ next) : RowsFreshFrom next cache :=
  fun lay hl => h lay (hle.trans hl)

theorem RowsFreshFrom.layer {stage : Nat} {cache : RCache}
    (h : RowsFreshFrom stage cache) (lay : Layer) (hle : stage ≤ lay.val)
    (tree leaf : Nat) (msg : LayerMsg) (counter : Nat) (hc : counter < 2 ^ 32) :
    cache (layerTrial lay tree leaf msg counter) = none := by
  rw [layerTrial_eq]
  exact h lay hle tree leaf _ _ counter hc

theorem RowsFreshFrom.cacheQuery {stage : Nat} {cache : RCache}
    (h : RowsFreshFrom stage cache) (lay : Layer) (hl : lay.val < stage)
    (tree leaf : Nat) (msg : LayerMsg) (counter : Nat) (answer : HashOutput) :
    RowsFreshFrom stage (cache.cacheQuery (layerTrial lay tree leaf msg counter) answer) := by
  intro other ho tree' leaf' left right counter' hc
  rw [QueryCache.cacheQuery_of_ne]
  · exact h other ho tree' leaf' left right counter' hc
  · rw [layerTrial_eq]
    exact pairTrial_ne_of_layer (by intro he; subst other; omega)
      tree' leaf' left right counter' tree leaf _ _ counter

theorem RowsFreshFrom.cacheDigest {stage : Nat} {cache : RCache}
    (h : RowsFreshFrom stage cache) (rho : Digest) (message : Message)
    (c : Nat) (answer : HashOutput) :
    RowsFreshFrom stage (cache.cacheQuery (digestTrial rho message c) answer) := by
  intro lay hl tree leaf left right counter hc
  rw [QueryCache.cacheQuery_of_ne]
  · exact h lay hl tree leaf left right counter hc
  · exact pairTrial_ne_digestTrial lay tree leaf left right counter rho message c

/-- A canonical stage can spend credit on its continuation while preserving all
later layers' fresh rows. No independence of the chosen floor is assumed here. -/
theorem V_layerSearch_bind {α : Type} (secret : BitVec 256) (z b : ENNReal)
    (lay : Layer) (floor tree leaf : Nat) (msg : LayerMsg)
    (next : Option (BitVec 32 × List Nat × Bool) → M α) (weight : List Nat × Bool → ENNReal)
    (hnone : ∀ cache, RowsFreshFrom (lay.val + 1) cache → V secret z (next none) cache ≤ b)
    (hsome : ∀ cache, RowsFreshFrom (lay.val + 1) cache →
      ∀ counter, counter < 2 ^ 32 → ∀ answer found,
      decoder lay floor answer = some found →
      V secret z (next (some (BitVec.ofNat 32 counter, found))) cache ≤ weight found)
    (hstep : z * (acceptedWeight (decoder lay floor) weight +
      failMass (decoder lay floor) * b) ≤ b)
    (fuel counter : Nat) (hlimit : counter + fuel ≤ 2 ^ 32)
    (cache : RCache) (hfresh : RowsFreshFrom lay.val cache) :
    V secret z (CanonicalPolicy.layerCounterSearchAt lay floor tree leaf msg counter fuel >>= next)
      cache ≤ b := by
  rw [search_public]
  apply V_search_bind secret z b _ _ _ next weight (RowsFreshFrom (lay.val + 1)) (2 ^ 32)
    (fun c _ => layerTrial_length lay tree leaf msg c)
    (fun _ _ hl hr he => layerTrial_injective lay tree leaf msg hl hr he)
    (fun cache hg counter _ answer => hg.cacheQuery lay (by omega) tree leaf msg counter answer)
    hnone
    (fun cache hg counter hc answer digits hd => hsome _
      (hg.cacheQuery lay (by omega) tree leaf msg counter answer) counter hc answer digits hd)
    hstep fuel counter hlimit cache (hfresh.mono (by omega))
  intro c _ hc
  exact hfresh.layer lay le_rfl tree leaf msg c hc

end ClaudeWCT.W9.T3.CanonicalSearch

namespace ClaudeWCT.W9.T3.CanonicalSearch
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
open SigGolfCandidate.T3.Freshness
open ClaudeWCT.WCT9 ClaudeWCT.W9.T3.PairRows
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem avoids_search (secret : BitVec 256) {lay other : Layer} (hne : lay ≠ other)
    (floor tree leaf : Nat) (msg : LayerMsg) (counter fuel : Nat)
    (tree' leaf' : Nat) (left' right' : Digest) (counter' : Nat) :
    Avoids secret (pairTrial other tree' leaf' left' right' counter')
      (CanonicalPolicy.layerCounterSearchAt lay floor tree leaf msg counter fuel) := by
  induction fuel generalizing counter with
  | zero => exact avoids_pure _ _ _
  | succ fuel ih =>
      unfold CanonicalPolicy.layerCounterSearchAt
      apply avoids_bind
      · apply (allQueriesSatisfy_query_iff _ _).mpr
        change pad64 (layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 counter)) ≠ _
        rw [show pad64 (layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 counter)) =
          layerTrial lay tree leaf msg counter from rfl, layerTrial_eq]
        exact pairTrial_ne_of_layer hne tree leaf _ _ counter tree' leaf' left' right' counter'
      · intro answer
        split
        · exact ih _
        · exact avoids_pure _ _ _

theorem search_preserves_rows (secret : BitVec 256) (lay : Layer)
    (floor tree leaf : Nat) (msg : LayerMsg) (counter fuel : Nat)
    (cache : RCache) (hfresh : RowsFreshFrom (lay.val + 1) cache)
    (result : Option (BitVec 32 × List Nat × Bool) × RCache)
    (hr : result ∈ support (roRun secret
      (CanonicalPolicy.layerCounterSearchAt lay floor tree leaf msg counter fuel) cache)) :
    RowsFreshFrom (lay.val + 1) result.2 := by
  intro other ho tree' leaf' left right counter' hc
  rw [preserves secret _ _ (avoids_search secret (by intro he; subst other; omega)
    floor tree leaf msg counter fuel tree' leaf' left right counter') cache result hr]
  exact hfresh other ho tree' leaf' left right counter' hc

end ClaudeWCT.W9.T3.CanonicalSearch
end
-- ==== merged from ClaudeWCT_W9_T3_FullCache_NativeBudgetB1_QuerySpace ====
section

section
namespace ClaudeWCT.W9.T3.Sampling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 hiding digestSearch admissible
open SigGolfCandidate.T3.Sampling (RCache roRun V publicProgram digestTrial digestTrial_injective
  digestTrial_length V_publicSearch public_randomOracle)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
def digestDecode (answer : HashOutput) : Option HashOutput :=
  if ClaudeWCT.WCT9.producerAdmissible answer then some answer else none
theorem digestDecode_eq_none_iff (value : HashOutput) :
    digestDecode value = none ↔ ClaudeWCT.WCT9.producerAdmissible value = false := by
  simp [digestDecode]
theorem digestSearch_public (rho : Digest) (message : Message) :
    ∀ fuel counter, ClaudeWCT.WCT9.digestSearch rho message counter fuel =
      publicProgram (SphincsSecurity.Completeness.searchLoop
        (digestTrial rho message) digestDecode
        (fun c output => pure (BitVec.ofNat 32 c, output)) fuel counter) := by
  intro fuel
  induction fuel with
  | zero => intro counter; rfl
  | succ fuel ih =>
      intro counter
      rw [ClaudeWCT.WCT9.digestSearch, SphincsSecurity.Completeness.searchLoop]
      simp only [publicProgram, simulateQ_bind, simulateQ_spec_query,
        SphincsSecurity.Concrete.oracleHash, HasQuery.query, SigGolfCandidate.T3.Sampling.publicHandler,
        digest, publicHash, bind_assoc, pure_bind, digestTrial, digestDecode]
      apply bind_congr
      intro answer
      split <;> simp only [simulateQ_map, simulateQ_pure, map_pure, ih, publicProgram]
theorem digestSearch_failure (secret : BitVec 256) (rho : Digest) (message : Message)
    (fuel counter : Nat) (hlimit : counter + fuel ≤ 2 ^ 32)
    (cache : QueryCache SphincsSecurity.HashSpec)
    (hfresh : ∀ c, counter ≤ c → c < 2 ^ 32 → cache (digestTrial rho message c) = none) :
    Pr[fun result => result.1 = none |
      (simulateQ SphincsSecurity.romImpl
        (realize secret (ClaudeWCT.WCT9.digestSearch rho message counter fuel))).run cache] ≤
      SphincsSecurity.Completeness.failMass digestDecode ^ fuel := by
  rw [digestSearch_public, public_randomOracle]
  exact SphincsSecurity.Completeness.probEvent_searchLoop _ _ _ (2 ^ 32)
    (fun _ _ hl hr he => digestTrial_injective rho message hl hr he)
    fuel counter hlimit cache hfresh
theorem V_digestSearch (secret : BitVec 256) (z b : ENNReal) (hb : 1 ≤ b)
    (rho : Digest) (message : Message)
    (hstep : z * (SphincsSecurity.Completeness.failMass digestDecode * b +
      (1 - SphincsSecurity.Completeness.failMass digestDecode)) ≤ b)
    (fuel counter : Nat) (hlimit : counter + fuel ≤ 2 ^ 32) (cache : RCache)
    (hfresh : ∀ c, counter ≤ c → c < 2 ^ 32 → cache (digestTrial rho message c) = none) :
    V secret z (ClaudeWCT.WCT9.digestSearch rho message counter fuel) cache ≤ b := by
  rw [digestSearch_public]
  exact V_publicSearch secret z b hb _ _ _ (2 ^ 32)
    (fun c _ => digestTrial_length rho message c)
    (fun _ _ hl hr he => digestTrial_injective rho message hl hr he)
    hstep fuel counter hlimit cache hfresh
end ClaudeWCT.W9.T3.Sampling
end
section
namespace ClaudeWCT.W9.T3.QuerySpace
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SigGolfCandidate.T3
open SigGolfCandidate.T3.Sampling (digestTrial)
open SigGolfCandidate.T3.QuerySpace (DigestFamily digestTrial_coordinates)
open ClaudeWCT.W9.T3.PairRows (pairTrial pairTrial_coordinates pairTrial_ne_digestTrial pairTrial_length)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
abbrev EncodingFamilyBC := Layer × Fin (2 ^ 32) × Digest × Digest
theorem encodingFamilyBC_card : Fintype.card EncodingFamilyBC = 2 ^ 290 := by
  set_option exponentiation.threshold 512 in
  norm_num [EncodingFamilyBC, Layer, Fintype.card_prod, Fintype.card_bitVec]
theorem encodingFamilyBC_card_le : (Fintype.card EncodingFamilyBC : ENNReal) ≤ 2 ^ 301 := by
  rw [encodingFamilyBC_card]
  exact_mod_cast Nat.pow_le_pow_right (by norm_num) (by norm_num)
def routedTree (lay : Layer) (r : Nat) : Nat := r / 2 ^ height lay
def routedLeaf (lay : Layer) (r : Nat) : Nat := r % 2 ^ height lay
theorem routedLeaf_lt (lay : Layer) (r : Nat) : routedLeaf lay r < 2 ^ height lay :=
  Nat.mod_lt _ (Nat.two_pow_pos _)
theorem routed_eq (lay : Layer) (r : Nat) : routedTree lay r * 2 ^ height lay + routedLeaf lay r = r := by
  unfold routedTree routedLeaf
  rw [Nat.mul_comm]
  exact Nat.div_add_mod r _
theorem routedTree_of (lay : Layer) {tree leaf : Nat} (hl : leaf < 2 ^ height lay) :
    routedTree lay (tree * 2 ^ height lay + leaf) = tree := by
  unfold routedTree
  rw [Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt hl, Nat.add_zero]
theorem routedLeaf_of (lay : Layer) {tree leaf : Nat} (hl : leaf < 2 ^ height lay) :
    routedLeaf lay (tree * 2 ^ height lay + leaf) = leaf := by
  unfold routedLeaf
  rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hl]
abbrev EncodingKeyBC := EncodingFamilyBC × Fin (2 ^ 22)
abbrev DigestKey := DigestFamily × Fin (2 ^ 21)
abbrev SearchKey := EncodingKeyBC ⊕ DigestKey
def encodingQueryBC (key : EncodingKeyBC) : HashInput :=
  pairTrial key.1.1 (routedTree key.1.1 key.1.2.1) (routedLeaf key.1.1 key.1.2.1) key.1.2.2.1 key.1.2.2.2 key.2
def digestQuery (key : DigestKey) : HashInput := digestTrial key.1.1 key.1.2 key.2
def searchQuery : SearchKey → HashInput := Sum.elim encodingQueryBC digestQuery
theorem encodingQueryBC_injective : Function.Injective encodingQueryBC := by
  rintro ⟨⟨lay, r, left, right⟩, counter⟩ ⟨⟨lay', r', left', right'⟩, counter'⟩ he
  obtain ⟨a, b, c, d, e, f⟩ := pairTrial_coordinates (routedLeaf_lt lay r)
    (by rw [routed_eq]; exact r.isLt) (routedLeaf_lt lay' r') (by rw [routed_eq]; exact r'.isLt)
    (by have := counter.isLt; omega) (by have := counter'.isLt; omega) he
  cases a
  have hr : r = r' := Fin.ext (by rw [← routed_eq lay r.val, ← routed_eq lay r'.val, b, c])
  have f := Fin.ext f
  cases hr; cases d; cases e; cases f; rfl
theorem digestQuery_injective : Function.Injective digestQuery := by
  rintro ⟨⟨rho, msg⟩, counter⟩ ⟨⟨rho', msg'⟩, counter'⟩ he
  obtain ⟨a, b, c⟩ := digestTrial_coordinates
    (by have := counter.isLt; omega) (by have := counter'.isLt; omega) he
  have c := Fin.ext c
  cases a; cases b; cases c; rfl
theorem searchQuery_injective : Function.Injective searchQuery := by
  intro left right he
  cases left with
  | inl l =>
    cases right with
    | inl r => exact congrArg Sum.inl (encodingQueryBC_injective he)
    | inr r => exact False.elim (pairTrial_ne_digestTrial _ _ _ _ _ _ _ _ _ he)
  | inr l =>
    cases right with
    | inl r => exact False.elim (pairTrial_ne_digestTrial _ _ _ _ _ _ _ _ _ he.symm)
    | inr r => exact congrArg Sum.inr (digestQuery_injective he)
theorem searchQuery_length (key : SearchKey) : (searchQuery key).length = 64 := by
  cases key with
  | inl key => exact pairTrial_length _ _ _ _ _ _
  | inr key => exact SigGolfCandidate.T3.Sampling.digestTrial_length _ _ _
end ClaudeWCT.W9.T3.QuerySpace
end
end
-- ==== merged from ClaudeWCT_W9_T3_FullCache_NativeBudgetB1_Presampling ====
section

namespace ClaudeWCT.W9.T3.Presampling
open OracleComp OracleSpec ENNReal
open SphincsSecurity.Seeded
open SigGolfCandidate.T3 hiding digestSearch admissible
open ClaudeWCT.W9.T3.QuerySpace
open SigGolfCandidate.T3.QuerySpace (DigestFamily)
open ClaudeWCT.W9.T3.PairRows (msgLeft msgRight layerCounterSearch_none_iff eval_shortHash_layer)
open SigGolfCandidate.T3.Presampling (eval_shortHash eval_digest uniform_table_forall)
open ClaudeWCT.WCT9 (digestAttemptLimit searchLimit)
open ClaudeWCT.W9.T3.ProducerV5 (producerEncodingDecode)
abbrev HashInput := SphincsSecurity.HashInput
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[irreducible] noncomputable def tableSampler : SampleableType (SearchKey → HashOutput) :=
  Derivation.outputSampler SearchKey
noncomputable local instance : SampleableType (SearchKey → HashOutput) := tableSampler
noncomputable def preparedCache (outputs : SearchKey → HashOutput) : QueryCache SphincsSecurity.HashSpec :=
  cacheTable ∅ searchQuery outputs
theorem preparedCache_apply (outputs : SearchKey → HashOutput) (key : SearchKey) :
    preparedCache outputs (searchQuery key) = some (outputs key) :=
  cacheTable_apply ∅ searchQuery searchQuery_injective outputs key
theorem presample_source {α : Type} (secret : BitVec 256) (program : M α) :
    𝒮[(simulateQ SphincsSecurity.romImpl (realize secret program)).run' ∅] =
    𝒮[do
      let outputs ← ($ᵗ (SearchKey → HashOutput) : ProbComp _)
      (simulateQ SphincsSecurity.romImpl (realize secret program)).run' (preparedCache outputs)] := by
  let : SampleableType (SearchKey → SphincsSecurity.HashOutput) := tableSampler
  let preparation : OracleComp SphincsSecurity.OracleWorld (SearchKey → HashOutput) :=
    liftM (queryTable (R := SphincsSecurity.HashOutput) searchQuery)
  have hprep : (simulateQ SphincsSecurity.romImpl preparation).run ∅ =
      (simulateQ randomOracle (queryTable (R := SphincsSecurity.HashOutput) searchQuery)).run ∅ := by
    exact congrArg (fun run => run.run (∅ : QueryCache SphincsSecurity.HashSpec))
      (QueryImpl.simulateQ_add_liftM_right (unifFwdImpl SphincsSecurity.HashSpec)
        (randomOracle (spec := SphincsSecurity.HashSpec)) (queryTable (R := SphincsSecurity.HashOutput) searchQuery))
  rw [evalDist_presample_computation (realize secret program) preparation ∅, hprep,
    evalSPMF_bind, evalDist_queryTable_fresh (R := SphincsSecurity.HashOutput) searchQuery searchQuery_injective
      ∅ (fun _ => rfl)]
  simp only [evalSPMF_map, bind_map_left]
  rw [evalSPMF_bind]
  congr 1
noncomputable def tableAnswers (outputs : SearchKey → HashOutput)
    (fallback : Correctness.Answers) : Correctness.Answers
  | .inl (.inr input) => (preparedCache outputs input).getD (fallback (.inl (.inr input)))
  | .inl (.inl input) => fallback (.inl (.inl input))
  | .inr input => fallback (.inr input)
theorem tableAnswers_apply (outputs : SearchKey → HashOutput) (fallback : Correctness.Answers)
    (key : SearchKey) : tableAnswers outputs fallback (.inl (.inr (searchQuery key))) = outputs key := by
  simp only [tableAnswers, preparedCache_apply, Option.getD_some]
theorem uniform_table_restriction_failure {J : Type} [Fintype J]
    [DecidableEq J] [SampleableType (J → HashOutput)] (e : J → SearchKey) (he : Function.Injective e)
    (p : HashOutput → Prop) :
    Pr[fun outputs : SearchKey → HashOutput => ∀ j, p (outputs (e j)) |
      ($ᵗ (SearchKey → HashOutput) : ProbComp _)] =
      Pr[p | ($ᵗ HashOutput : ProbComp _)] ^ Fintype.card J := by
  have h := evalSPMF_uniformSample_map_comp_injective (R := HashOutput) he
  have hp := congrArg (fun law => probEvent law (fun outputs : J → HashOutput => ∀ j, p (outputs j))) h
  simpa only [probEvent_evalSPMF, bind_pure_comp, probEvent_map, Function.comp_def,
    uniform_table_forall] using hp
theorem digestSearch_none_table (outputs : SearchKey → HashOutput)
    (fallback : Correctness.Answers) (family : DigestFamily) :
    evalWithAnswerFn (tableAnswers outputs fallback)
      (ClaudeWCT.WCT9.digestSearch family.1 family.2 0 digestAttemptLimit) = none ↔
    ∀ c : Fin (2 ^ 21), ClaudeWCT.W9.T3.Sampling.digestDecode (outputs (.inr (family, c))) = none := by
  rw [ClaudeWCT.WCT9.digestSearch_none_iff]
  have hv (c : Nat) (hc : c < digestAttemptLimit) :
      evalWithAnswerFn (tableAnswers outputs fallback)
        (digest family.1 family.2 (BitVec.ofNat 32 (0 + c))) = outputs (.inr (family, ⟨c, hc⟩)) := by
    rw [eval_digest]
    have hinput : pad64 (digestInput family.1 family.2 (BitVec.ofNat 32 (0 + c))) =
        searchQuery (.inr (family, ⟨c, hc⟩)) := by
      simp only [searchQuery, Sum.elim_inr, digestQuery, SigGolfCandidate.T3.Sampling.digestTrial,
        Nat.zero_add]
    rw [hinput, tableAnswers_apply]
  constructor
  · intro h c
    rw [ClaudeWCT.W9.T3.Sampling.digestDecode_eq_none_iff]
    have h := h c c.isLt
    rwa [hv c c.isLt] at h
  · intro h c hc
    rw [hv c hc]
    exact (ClaudeWCT.W9.T3.Sampling.digestDecode_eq_none_iff _).mp (h ⟨c, hc⟩)
theorem digestSearch_table_failure (fallback : Correctness.Answers) (family : DigestFamily) :
    Pr[fun outputs => evalWithAnswerFn (tableAnswers outputs fallback)
      (ClaudeWCT.WCT9.digestSearch family.1 family.2 0 digestAttemptLimit) = none |
      ($ᵗ (SearchKey → HashOutput) : ProbComp _)] =
    SphincsSecurity.Completeness.failMass ClaudeWCT.W9.T3.Sampling.digestDecode ^ digestAttemptLimit := by
  simp_rw [digestSearch_none_table]
  have h := uniform_table_restriction_failure (fun c : Fin (2 ^ 21) => .inr (family, c))
    (fun _ _ h => congrArg Prod.snd (Sum.inr.inj h))
    (fun x => ClaudeWCT.W9.T3.Sampling.digestDecode x = none)
  simpa only [SphincsSecurity.Completeness.failMass_eq_probEvent, Fintype.card_fin,
    ClaudeWCT.WCT9.digestAttemptLimit, HashOutput, SphincsSecurity.HashOutput,
    SphincsSecurity.hashOutputBits] using h
theorem layerCounterSearch_none_table_le (L : ℕ) (hL : L ≤ 2 ^ 22) (outputs : SearchKey → HashOutput)
    (fallback : Correctness.Answers) (lay : Layer) (r : Fin (2 ^ 32))
    (msg : ClaudeWCT.WCT9.LayerMsg) :
    evalWithAnswerFn (tableAnswers outputs fallback)
      (ClaudeWCT.WCT9.layerCounterSearch lay (routedTree lay r) (routedLeaf lay r) msg 0 L) = none ↔
    ∀ c : Fin L, producerEncodingDecode lay
      (outputs (.inl ((lay, r, msgLeft msg, msgRight msg), Fin.castLE hL c))) = none := by
  rw [layerCounterSearch_none_iff]
  have hv (c : Nat) (hc : c < L) :
      evalWithAnswerFn (tableAnswers outputs fallback)
        (ClaudeWCT.WCT9.encodingHash lay (ClaudeWCT.WCT9.layerEncodingInput lay (routedTree lay r) (routedLeaf lay r) msg
          (BitVec.ofNat 32 (0 + c)))) =
        ClaudeWCT.WCT9.encodingAnswer lay (outputs (.inl ((lay, r, msgLeft msg, msgRight msg), Fin.castLE hL ⟨c, hc⟩))) := by
    rw [Nat.zero_add, eval_shortHash_layer]
    have hinput : PairRows.pairTrial lay (routedTree lay r) (routedLeaf lay r) (msgLeft msg) (msgRight msg) c =
        searchQuery (.inl ((lay, r, msgLeft msg, msgRight msg), Fin.castLE hL ⟨c, hc⟩)) := rfl
    rw [hinput, tableAnswers_apply]
  constructor
  · intro h c
    have h := h c c.isLt
    rw [hv c c.isLt] at h
    exact h
  · intro h c hc
    rw [hv c hc]
    exact h ⟨c, hc⟩
theorem layerCounterSearch_table_failure_le (L : ℕ) (hL : L ≤ 2 ^ 22) (fallback : Correctness.Answers)
    (lay : Layer) (r : Fin (2 ^ 32)) (left right : Digest) :
    Pr[fun outputs => evalWithAnswerFn (tableAnswers outputs fallback)
      (ClaudeWCT.WCT9.layerCounterSearch lay (routedTree lay r) (routedLeaf lay r) (.pair left right) 0 L) = none |
      ($ᵗ (SearchKey → HashOutput) : ProbComp _)] =
    SphincsSecurity.Completeness.failMass (producerEncodingDecode lay) ^ L := by
  simp_rw [layerCounterSearch_none_table_le L hL, msgLeft, msgRight]
  have h := uniform_table_restriction_failure
    (fun c : Fin L => .inl ((lay, r, left, right), Fin.castLE hL c))
    (fun _ _ h => Fin.castLE_injective hL (congrArg Prod.snd (Sum.inl.inj h)))
    (fun x => producerEncodingDecode lay x = none)
  simpa only [SphincsSecurity.Completeness.failMass_eq_probEvent, Fintype.card_fin,
    HashOutput, SphincsSecurity.HashOutput, SphincsSecurity.hashOutputBits] using h
theorem searchLimit_le_rows (lay : Layer) : searchLimit lay ≤ 2 ^ 22 := ClaudeWCT.WCT9.searchLimit_le lay
theorem layerCounterSearch_none_table (outputs : SearchKey → HashOutput)
    (fallback : Correctness.Answers) (lay : Layer) (r : Fin (2 ^ 32))
    (msg : ClaudeWCT.WCT9.LayerMsg) :
    evalWithAnswerFn (tableAnswers outputs fallback)
      (ClaudeWCT.WCT9.layerCounterSearch lay (routedTree lay r) (routedLeaf lay r) msg 0 (searchLimit lay)) = none ↔
    ∀ c : Fin (searchLimit lay), producerEncodingDecode lay
      (outputs (.inl ((lay, r, msgLeft msg, msgRight msg), Fin.castLE (searchLimit_le_rows lay) c))) = none :=
  layerCounterSearch_none_table_le _ (searchLimit_le_rows lay) outputs fallback lay r msg
theorem layerCounterSearch_table_failure (fallback : Correctness.Answers) (lay : Layer) (r : Fin (2 ^ 32))
    (left right : Digest) :
    Pr[fun outputs => evalWithAnswerFn (tableAnswers outputs fallback)
      (ClaudeWCT.WCT9.layerCounterSearch lay (routedTree lay r) (routedLeaf lay r) (.pair left right) 0
        (searchLimit lay)) = none |
      ($ᵗ (SearchKey → HashOutput) : ProbComp _)] =
    SphincsSecurity.Completeness.failMass (producerEncodingDecode lay) ^ searchLimit lay :=
  layerCounterSearch_table_failure_le _ (searchLimit_le_rows lay) fallback lay r left right
end ClaudeWCT.W9.T3.Presampling

namespace ClaudeWCT.W9.T3.CanonicalSearch
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3
open ClaudeWCT.WCT9
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem search_none_iff (answers : Correctness.Answers) (lay : Layer) (floor tree leaf : Nat)
    (msg : LayerMsg) :
    ∀ fuel counter,
      evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt lay floor tree leaf msg counter fuel) = none ↔
      ∀ offset, offset < fuel → CanonicalPolicy.producerDecodeOut lay floor (evalWithAnswerFn answers
        (publicHash (layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 (counter + offset))))) = none := by
  intro fuel
  induction fuel with
  | zero => intro counter; simp [CanonicalPolicy.layerCounterSearchAt]
  | succ fuel ih =>
      intro counter
      simp only [CanonicalPolicy.layerCounterSearchAt, evalWithAnswerFn_bind]
      cases hd : CanonicalPolicy.producerDecodeOut lay floor (evalWithAnswerFn answers
        (publicHash (layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 counter)))) with
      | none =>
          simp only [hd, ih]
          constructor
          · intro hall offset hoff
            cases offset with
            | zero => simpa using hd
            | succ offset => simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hall offset (by omega)
          · intro hall offset hoff
            simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hall (offset+1) (by omega)
      | some digits =>
          simp only [hd,evalWithAnswerFn_pure,reduceCtorEq,false_iff]
          intro hall
          have := hall 0 (by omega)
          simp only [Nat.add_zero,hd,reduceCtorEq] at this
end ClaudeWCT.W9.T3.CanonicalSearch

namespace ClaudeWCT.W9.T3.Presampling.Canonical
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3
open ClaudeWCT.WCT9 ClaudeWCT.W9.T3.QuerySpace ClaudeWCT.W9.T3.CanonicalSearch
open ClaudeWCT.W9.T3.PairRows (msgLeft msgRight eval_shortHash_layer)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable local instance : SampleableType (SearchKey → HashOutput) := tableSampler

theorem search_none_table (L : Nat) (hL : L≤2^22) (outputs : SearchKey → HashOutput)
    (fallback : Correctness.Answers) (lay : Layer) (floor : Nat) (r : Fin (2^32)) (msg : LayerMsg) :
    evalWithAnswerFn (tableAnswers outputs fallback)
      (CanonicalPolicy.layerCounterSearchAt lay floor (routedTree lay r) (routedLeaf lay r) msg 0 L)=none ↔
    ∀ c : Fin L, decoder lay floor
      (outputs (.inl ((lay,r,msgLeft msg,msgRight msg),Fin.castLE hL c)))=none := by
  rw [search_none_iff]
  have hv (c : Nat) (hc : c<L) :
      evalWithAnswerFn (tableAnswers outputs fallback)
        (publicHash (layerEncodingInput lay (routedTree lay r) (routedLeaf lay r) msg
          (BitVec.ofNat 32 (0+c)))) =
        (outputs (.inl ((lay,r,msgLeft msg,msgRight msg),Fin.castLE hL ⟨c,hc⟩))) := by
    rw [Nat.zero_add,PairRows.eval_publicHash_layer]
    have hinput : PairRows.pairTrial lay (routedTree lay r) (routedLeaf lay r) (msgLeft msg) (msgRight msg) c =
        searchQuery (.inl ((lay,r,msgLeft msg,msgRight msg),Fin.castLE hL ⟨c,hc⟩)) := rfl
    rw [hinput,tableAnswers_apply]
  constructor
  · intro h c
    have h := h c c.isLt
    rw [hv c c.isLt] at h
    exact h
  · intro h c hc
    rw [hv c hc]
    exact h ⟨c,hc⟩

theorem search_table_failure (L : Nat) (hL : L≤2^22) (fallback : Correctness.Answers)
    (lay : Layer) (floor : Nat) (r : Fin (2^32)) (left right : Digest) :
    Pr[fun outputs => evalWithAnswerFn (tableAnswers outputs fallback)
      (CanonicalPolicy.layerCounterSearchAt lay floor (routedTree lay r) (routedLeaf lay r)
        (.pair left right) 0 L)=none | ($ᵗ (SearchKey → HashOutput) : ProbComp _)] =
      SphincsSecurity.Completeness.failMass (decoder lay floor)^L := by
  simp_rw [search_none_table L hL,msgLeft,msgRight]
  have h := uniform_table_restriction_failure
    (fun c : Fin L => .inl ((lay,r,left,right),Fin.castLE hL c))
    (fun _ _ h => Fin.castLE_injective hL (congrArg Prod.snd (Sum.inl.inj h)))
    (fun x => decoder lay floor x=none)
  simpa only [SphincsSecurity.Completeness.failMass_eq_probEvent,Fintype.card_fin,
    HashOutput,SphincsSecurity.HashOutput,SphincsSecurity.hashOutputBits] using h

end ClaudeWCT.W9.T3.Presampling.Canonical


namespace ClaudeWCT.W9.T3.Presampling.Canonical
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3
open ClaudeWCT.WCT9 ClaudeWCT.W9.T3.QuerySpace ClaudeWCT.W9.T3.CanonicalSearch
open ClaudeWCT.W9.T3.PairRows (msgLeft msgRight eval_shortHash_layer)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable local instance : SampleableType (SearchKey → HashOutput) := tableSampler

theorem search_none_agreement (L : Nat) (hL : L≤2^22) (outputs : SearchKey → HashOutput)
    (answers : Correctness.Answers)
    (hagree : ∀ key, answers (.inl (.inr (searchQuery key)))=outputs key) (lay : Layer) (floor : Nat) (r : Fin (2^32)) (msg : LayerMsg) :
    evalWithAnswerFn answers
      (CanonicalPolicy.layerCounterSearchAt lay floor (routedTree lay r) (routedLeaf lay r) msg 0 L)=none ↔
    ∀ c : Fin L, decoder lay floor
      (outputs (.inl ((lay,r,msgLeft msg,msgRight msg),Fin.castLE hL c)))=none := by
  rw [search_none_iff]
  have hv (c : Nat) (hc : c<L) :
      evalWithAnswerFn answers
        (publicHash (layerEncodingInput lay (routedTree lay r) (routedLeaf lay r) msg
          (BitVec.ofNat 32 (0+c)))) =
        (outputs (.inl ((lay,r,msgLeft msg,msgRight msg),Fin.castLE hL ⟨c,hc⟩))) := by
    rw [Nat.zero_add,PairRows.eval_publicHash_layer]
    have hinput : PairRows.pairTrial lay (routedTree lay r) (routedLeaf lay r) (msgLeft msg) (msgRight msg) c =
        searchQuery (.inl ((lay,r,msgLeft msg,msgRight msg),Fin.castLE hL ⟨c,hc⟩)) := rfl
    rw [hinput,hagree]
  constructor
  · intro h c
    have h := h c c.isLt
    rw [hv c c.isLt] at h
    exact h
  · intro h c hc
    rw [hv c hc]
    exact h ⟨c,hc⟩


end ClaudeWCT.W9.T3.Presampling.Canonical
end
-- ==== merged from ClaudeWCT_W9_T3_FullCache_NativeBudgetB1_Budgets ====
section

section



namespace ClaudeWCT.W9.T3.Budgets
open OracleComp OracleSpec OracleComp.EvalDist ENNReal Finset
open SigGolfCandidate.T3 (HashOutput)
open ClaudeWCT.Bank.WCT (WProposal proposal)
open ClaudeWCT.WCT9 (Coord Child Rank)
def capP (p : WProposal) : Prop :=
  ClaudeWCT.Numerics.N600Cap.pairCost p.2 ≤ ClaudeWCT.WCT9.jointCap
instance : DecidablePred capP := fun _ => Nat.decLe _ _
theorem producerAdmissible_iff_capP (x : HashOutput) :
    ClaudeWCT.WCT9.producerAdmissible x = true ↔ ClaudeWCT.WCT9.admissible x = true ∧ capP (proposal x) := by
  rw [ClaudeWCT.WCT9.producerAdmissible_iff, ClaudeWCT.WCT9.jointCost_eq_sum]
  rfl
theorem card_capP : #{p : WProposal | capP p} = 2 ^ 31 * ClaudeWCT.Numerics.N600Cap.J := by
  have h : (univ.filter capP : Finset WProposal) =
      (univ ×ˢ ClaudeWCT.Numerics.N600Cap.capSet : Finset (Fin (2 ^ 31) × (Coord → Child × Rank))) :=
    Finset.ext fun p => by
      rw [mem_filter, mem_product, ClaudeWCT.Numerics.N600Cap.mem_capSet]
      simp only [mem_univ, true_and]
      exact Iff.rfl
  rw [h, card_product, ClaudeWCT.Numerics.N600Cap.card_capSet, card_univ, Fintype.card_fin]
theorem acceptanceV5 :
    Pr[fun x : HashOutput => ClaudeWCT.WCT9.producerAdmissible x = true | ($ᵗ HashOutput : ProbComp HashOutput)] =
      (1353 * ClaudeWCT.Numerics.N600Cap.J : ENNReal) / 2 ^ 167 := by
  rw [← expectedValue_ite_one, SigGolfCandidate.T3.BPORS.expected_uniform_eq_finiteAverage]
  unfold SigGolfResearch.Gate6.Moments.finiteAverage
  have hsum : (∑ x : HashOutput, if ClaudeWCT.WCT9.producerAdmissible x = true then (1 : ENNReal) else 0) =
      ∑ x : HashOutput, if ClaudeWCT.WCT9.admissible x = true then
        (if capP (proposal x) then (1 : ENNReal) else 0) else 0 := by
    refine sum_congr rfl fun x _ => ?_
    by_cases ha : ClaudeWCT.WCT9.admissible x = true
    · simp only [ha, if_true]
      exact if_congr ((producerAdmissible_iff_capP x).trans (and_iff_right ha)) rfl rfl
    · rw [if_neg ha, if_neg (fun h => ha ((producerAdmissible_iff_capP x).mp h).1)]
  rw [hsum, ClaudeWCT.Bank.WCT.sum_admissible (fun p : WProposal => if capP p then (1 : ENNReal) else 0),
    sum_boole, card_capP, Fintype.card_bitVec]
  unfold ClaudeWCT.WCT9.gateLimit
  generalize hJ : ClaudeWCT.Numerics.N600Cap.J = J
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp
theorem acceptanceV5_eq_p0 :
    Pr[fun x : HashOutput => ClaudeWCT.WCT9.producerAdmissible x = true | ($ᵗ HashOutput : ProbComp HashOutput)] =
      ENNReal.ofReal (BaseAudit.V5.p0 : ℝ) := by
  rw [acceptanceV5]
  have hq : ((BaseAudit.V5.p0 : ℚ) : ℝ) = (1353 : ℝ) * (ClaudeWCT.Numerics.N600Cap.J : ℝ) / 2 ^ 167 := by
    simp only [BaseAudit.V5.p0, BaseAudit.V5.J, ClaudeWCT.Numerics.N600Cap.J]
    push_cast
    ring
  rw [hq, ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_pow (by norm_num)]
  simp
end ClaudeWCT.W9.T3.Budgets
end

section







section
namespace ClaudeWCT.W9.T3.Correctness
open OracleComp OracleSpec
open ClaudeWCT.WCT9 (Signature Witness digestAttemptLimit honestTop eval_signForest)
open ClaudeWCT.WCT9.Rev3 (sign expand verify signPayload)
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.Correctness (Answers DigestFamily KeygenCorrect)
open ClaudeWCT.W9.T3.QuerySpace (EncodingFamilyBC routedTree routedLeaf routedTree_of routedLeaf_of)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
def DigestSearchesSucceed (answers : Answers) : Prop :=
  ∀ family : DigestFamily, ∃ found,
    evalWithAnswerFn answers (ClaudeWCT.WCT9.digestSearch family.1 family.2 0 digestAttemptLimit) = some found
def EncodingSearchesSucceedBC (answers : Answers) : Prop :=
  ∀ family : EncodingFamilyBC, ∃ found,
    evalWithAnswerFn answers (ClaudeWCT.WCT9.layerCounterSearch family.1 (routedTree family.1 family.2.1)
      (routedLeaf family.1 family.2.1) (.pair family.2.2.1 family.2.2.2) 0 (ClaudeWCT.WCT9.searchLimit family.1)) =
      some found
theorem encodingSearchesSucceedBC_msg (answers : Answers) (hgood : EncodingSearchesSucceedBC answers)
    (lay : Layer) (tree leaf : Nat) (hleaf : leaf < 2 ^ height lay) (hr : tree * 2 ^ height lay + leaf < 2 ^ 32)
    (msg : ClaudeWCT.WCT9.LayerMsg) : ∃ found,
    evalWithAnswerFn answers (ClaudeWCT.WCT9.layerCounterSearch lay tree leaf msg 0 (ClaudeWCT.WCT9.searchLimit lay)) =
      some found := by
  have ht := routedTree_of lay (tree := tree) hleaf
  have hl := routedLeaf_of lay (tree := tree) hleaf
  cases msg with
  | forest root =>
      rw [ClaudeWCT.W9.T3.PairRows.layerCounterSearch_forest_eval]
      have h := hgood (lay, ⟨_, hr⟩, root, 0)
      simp only [ht, hl] at h
      exact h
  | pair left right =>
      have h := hgood (lay, ⟨_, hr⟩, left, right)
      simp only [ht, hl] at h
      exact h
theorem route_routed_lt (index : Nat) (hindex : index < 2 ^ 31) (lay : Layer) :
    (route index lay).2 * 2 ^ height lay + (route index lay).1 < 2 ^ 32 := by
  fin_cases lay <;> simp [route, height] <;> omega
theorem encodingSearchesSucceedBC_at_route (answers : Answers) (hgood : EncodingSearchesSucceedBC answers)
    (index : Nat) (hindex : index < 2 ^ 31) (lay : Layer) (msg : ClaudeWCT.WCT9.LayerMsg) : ∃ found,
    evalWithAnswerFn answers (ClaudeWCT.WCT9.layerCounterSearch lay (route index lay).2
      (route index lay).1 msg 0 (ClaudeWCT.WCT9.searchLimit lay)) = some found :=
  encodingSearchesSucceedBC_msg answers hgood lay _ _ (route_leaf_bound index lay)
    (route_routed_lt index hindex lay) msg
theorem topSearchesSucceedBC_of (answers : Answers) (hgood : EncodingSearchesSucceedBC answers) :
    ClaudeWCT.WCT9.TopSearchesSucceedBC answers :=
  fun index hindex msg => encodingSearchesSucceedBC_at_route answers hgood index hindex (Fin.ofNat 4 0) msg
theorem signLayersBC_succeeds (answers : Answers) (cache : Cache) (index : Nat)
    (hindex : index < 2 ^ 31) (hgood : EncodingSearchesSucceedBC answers) :
    ∀ n msg, ∃ pieces,
      evalWithAnswerFn answers (ClaudeWCT.WCT9.signLayersBC cache index n msg) = some pieces := by
  intro n
  induction n with
  | zero => intro msg; exact ⟨[], rfl⟩
  | succ n ih =>
      intro msg
      simp only [ClaudeWCT.WCT9.signLayersBC, evalWithAnswerFn_bind]
      by_cases hn : n = 0
      · simp only [hn, if_true, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
        exact ⟨_, rfl⟩
      · simp only [hn, if_false, evalWithAnswerFn_bind]
        split
        · simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
          split
          · exact ⟨_, rfl⟩
          · rename_i hp
            refine (hp ?p ?hp).elim
            case hp => exact (ih _).choose_spec
        · rename_i hs
          refine (hs ?a ?b ?h).elim
          case h => exact (encodingSearchesSucceedBC_at_route answers hgood index hindex _ _).choose_spec
def SearchesSucceed (answers : Answers) : Prop :=
  DigestSearchesSucceed answers ∧ EncodingSearchesSucceedBC answers
theorem signPayload_succeeds (answers : Answers) (cache : Cache) (message : Message)
    (hgood : SearchesSucceed answers) :
    ∃ sig, evalWithAnswerFn answers (signPayload cache message) = some sig := by
  obtain ⟨⟨counter, output⟩, hd⟩ := hgood.1 (evalWithAnswerFn answers (privateNonce message), message)
  rw [ClaudeWCT.WCT9.Rev3.signPayload_eq]
  simp only [evalWithAnswerFn_bind, hd, eval_signForest]
  obtain ⟨pieces, hp⟩ := signLayersBC_succeeds answers cache (ClaudeWCT.WCT9.digestIndex output)
    (ClaudeWCT.WCT9.digestIndex_lt output) hgood.2 4 (.pair (honestTop answers (ClaudeWCT.WCT9.digestIndex output)).1
      (honestTop answers (ClaudeWCT.WCT9.digestIndex output)).2)
  simp only [hp, evalWithAnswerFn_pure]
  exact ⟨_, rfl⟩
def SigningComplete (answers : Answers) (keys : Digest × Cache) : Prop :=
  ∀ message : Message, ∃ sig : Signature, ∃ w : Witness,
    evalWithAnswerFn answers (sign keys.2 message) = some sig ∧
    evalWithAnswerFn answers (expand message keys.1 sig) = some w ∧
    evalWithAnswerFn answers (verify message keys.1 w) = true
def RealizedSigningComplete (answers : QueryImpl SphincsSecurity.OracleWorld Id)
    (secret : BitVec 256) (keys : Digest × Cache) : Prop :=
  ∀ message : Message, ∃ sig : Signature, ∃ w : Witness,
    evalWithAnswerFn answers (realize secret (sign keys.2 message)) = some sig ∧
    evalWithAnswerFn answers (realize secret (expand message keys.1 sig)) = some w ∧
    evalWithAnswerFn answers (realize secret (verify message keys.1 w)) = true
def SearchesSucceedFor (answers : Answers) (message : Message) : Prop :=
  (∀ rho : Digest, ∃ found,
    evalWithAnswerFn answers (ClaudeWCT.WCT9.digestSearch rho message 0 digestAttemptLimit) = some found) ∧
  EncodingSearchesSucceedBC answers
theorem signPayload_succeedsFor (answers : Answers) (cache : Cache) (message : Message)
    (hgood : SearchesSucceedFor answers message) :
    ∃ sig, evalWithAnswerFn answers (signPayload cache message) = some sig := by
  obtain ⟨⟨counter, output⟩, hd⟩ := hgood.1 (evalWithAnswerFn answers (privateNonce message))
  rw [ClaudeWCT.WCT9.Rev3.signPayload_eq]
  simp only [evalWithAnswerFn_bind, hd, eval_signForest]
  obtain ⟨pieces, hp⟩ := signLayersBC_succeeds answers cache (ClaudeWCT.WCT9.digestIndex output)
    (ClaudeWCT.WCT9.digestIndex_lt output) hgood.2 4 (.pair (honestTop answers (ClaudeWCT.WCT9.digestIndex output)).1
      (honestTop answers (ClaudeWCT.WCT9.digestIndex output)).2)
  simp only [hp, evalWithAnswerFn_pure]
  exact ⟨_, rfl⟩
def SearchesSucceedSelected (answers : Answers) : Prop :=
  (∀ message : Message, ∃ found,
    evalWithAnswerFn answers (ClaudeWCT.WCT9.digestSearch
      (evalWithAnswerFn answers (privateNonce message)) message 0 digestAttemptLimit) = some found) ∧
  EncodingSearchesSucceedBC answers
theorem signPayload_succeedsSelected (answers : Answers) (cache : Cache) (message : Message)
    (hgood : SearchesSucceedSelected answers) :
    ∃ sig, evalWithAnswerFn answers (signPayload cache message) = some sig := by
  obtain ⟨⟨counter, output⟩, hd⟩ := hgood.1 message
  rw [ClaudeWCT.WCT9.Rev3.signPayload_eq]
  simp only [evalWithAnswerFn_bind, hd, eval_signForest]
  obtain ⟨pieces, hp⟩ := signLayersBC_succeeds answers cache (ClaudeWCT.WCT9.digestIndex output)
    (ClaudeWCT.WCT9.digestIndex_lt output) hgood.2 4 (.pair (honestTop answers (ClaudeWCT.WCT9.digestIndex output)).1
      (honestTop answers (ClaudeWCT.WCT9.digestIndex output)).2)
  simp only [hp, evalWithAnswerFn_pure]
  exact ⟨_, rfl⟩
end ClaudeWCT.W9.T3.Correctness
end
section
namespace ClaudeWCT.W9.T3.Budgets
open OracleComp OracleSpec ENNReal
open SphincsSecurity.Completeness (failMass failMass_eq_probEvent)
open ClaudeWCT.WCT9 (Signature Witness digestAttemptLimit)
open ClaudeWCT.WCT9.Rev3 (sign expand verify signPayload)
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.Correctness (Answers DigestFamily digestFamily_card KeygenCorrect)
open SigGolfCandidate.T3.Budgets (zeroAnswers failMass_eq_one_sub_accept
  rejection_power_le ofReal_inv_two_pow finite_family_failure_le)
open ClaudeWCT.W9.T3.Correctness (SearchesSucceed DigestSearchesSucceed EncodingSearchesSucceedBC SigningComplete
  SearchesSucceedFor SearchesSucceedSelected)
open ClaudeWCT.W9.T3.QuerySpace (SearchKey searchQuery EncodingFamilyBC encodingFamilyBC_card_le routedTree routedLeaf)
open ClaudeWCT.W9.T3.PairRows (pairTrial msgLeft msgRight layerCounterSearch_none_iff eval_shortHash_layer)
open ClaudeWCT.W9.T3.Sampling (digestDecode)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
theorem digest_probability_eq_p0 :
    Pr[fun answer => (digestDecode answer).isSome |
      ($ᵗ HashOutput : ProbComp HashOutput)] = ENNReal.ofReal (BaseAudit.V5.p0 : ℝ) := by
  have h : (fun answer : HashOutput => (digestDecode answer).isSome = true) =
      fun x => ClaudeWCT.WCT9.producerAdmissible x = true := by
    funext x
    simp only [digestDecode]
    split <;> simp_all
  rw [h, acceptanceV5_eq_p0]
theorem digest_failure_power_of_acceptance (p : ℝ) (hp : 1 / 5026 ≤ p) (hp1 : p ≤ 1)
    (haccept : Pr[fun answer => (digestDecode answer).isSome |
      ($ᵗ HashOutput : ProbComp HashOutput)] = ENNReal.ofReal p) :
    failMass digestDecode ^ digestAttemptLimit ≤ 1 / (2 : ENNReal) ^ 450 := by
  have hm : failMass digestDecode = ENNReal.ofReal (1 - p) := by
    rw [failMass_eq_one_sub_accept, haccept, ENNReal.ofReal_sub 1 (by linarith)]
    simp
  rw [hm, ← ENNReal.ofReal_pow (by linarith)]
  have hreal := rejection_power_le p hp1 digestAttemptLimit 450
    (by have hl := Real.log_two_lt_d9
        change (450 : ℝ) * Real.log 2 ≤ 2097152 * p
        nlinarith)
  have hcast := ENNReal.ofReal_le_ofReal hreal
  simpa only [ofReal_inv_two_pow] using hcast
theorem digest_failure_power :
    failMass digestDecode ^ digestAttemptLimit ≤ 1 / (2 : ENNReal) ^ 450 :=
  digest_failure_power_of_acceptance (BaseAudit.V5.p0 : ℝ)
    (by norm_num [BaseAudit.V5.p0, BaseAudit.V5.J]) (by norm_num [BaseAudit.V5.p0, BaseAudit.V5.J]) digest_probability_eq_p0
theorem digest_failMass_eq :
    failMass digestDecode = 1 - (1353 * ClaudeWCT.Numerics.N600Cap.J : ENNReal) / 2 ^ 167 := by
  have h : (fun answer : HashOutput => (digestDecode answer).isSome = true) =
      fun x => ClaudeWCT.WCT9.producerAdmissible x = true := by
    funext x
    simp only [digestDecode]
    split <;> simp_all
  rw [failMass_eq_one_sub_accept, h, acceptanceV5]
theorem digest_failure_explicit :
    (1 - (1353 * ClaudeWCT.Numerics.N600Cap.J : ENNReal) / 2 ^ 167) ^ (2 ^ 21) ≤
      1 / (2 : ENNReal) ^ 450 := by
  rw [← digest_failMass_eq]
  exact digest_failure_power
theorem digest_failure_power_900 :
    failMass digestDecode ^ digestAttemptLimit ≤ 1 / (2 : ENNReal) ^ 900 :=
  V5.digest_failure_power_900_of digestDecode digest_probability_eq_p0
theorem digest_failure_power_752 :
    failMass digestDecode ^ digestAttemptLimit ≤ 1 / (2 : ENNReal) ^ 752 := by
  refine digest_failure_power_900.trans ?_
  gcongr
  · norm_num
  · norm_num
theorem digest_failure_power_602 :
    failMass digestDecode ^ digestAttemptLimit ≤ 1 / (2 : ENNReal) ^ 602 := by
  refine digest_failure_power_752.trans ?_
  gcongr
  · norm_num
  · norm_num
def DigestFailed (family : DigestFamily) (answers : Answers) : Prop :=
  evalWithAnswerFn answers (ClaudeWCT.WCT9.digestSearch family.1 family.2 0 digestAttemptLimit) = none
def EncodingFailedBC (family : EncodingFamilyBC) (answers : Answers) : Prop :=
  evalWithAnswerFn answers (ClaudeWCT.WCT9.layerCounterSearch family.1 (routedTree family.1 family.2.1)
    (routedLeaf family.1 family.2.1) (.pair family.2.2.1 family.2.2.2) 0 (ClaudeWCT.WCT9.searchLimit family.1)) = none
theorem not_searchesSucceed_iff (answers : Answers) :
    ¬ SearchesSucceed answers ↔
      (∃ family, DigestFailed family answers) ∨ (∃ family, EncodingFailedBC family answers) := by
  classical
  simp only [SearchesSucceed, DigestSearchesSucceed, EncodingSearchesSucceedBC,
    ← Option.ne_none_iff_exists', not_and_or, not_forall, not_not, DigestFailed, EncodingFailedBC]
theorem union_real_65 : (2 : ℝ) ^ 384 * (1 / 2 ^ 450) + 2 ^ 301 * (1 / 2 ^ 600) ≤ 1 / 2 ^ 65 := by
  set_option exponentiation.threshold 2048 in norm_num
theorem union_real_298 : (2 : ℝ) ^ 128 * (1 / 2 ^ 450) + 2 ^ 301 * (1 / 2 ^ 600) ≤ 1 / 2 ^ 298 := by
  set_option exponentiation.threshold 2048 in norm_num
theorem union_ennreal (a c : ℕ)
    (hreal : (2 : ℝ) ^ a * (1 / 2 ^ 450) + 2 ^ 301 * (1 / 2 ^ 600) ≤ 1 / 2 ^ c) :
    (2 : ENNReal) ^ a * (1 / 2 ^ 450) + (2 : ENNReal) ^ 301 * (1 / 2 ^ 600) ≤ 1 / 2 ^ c := by
  have hcast := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_add (show 0 ≤ (2 : ℝ) ^ a * (1 / 2 ^ 450) by positivity)
    (show 0 ≤ (2 : ℝ) ^ 301 * (1 / 2 ^ 600) by positivity),
    ENNReal.ofReal_mul (show 0 ≤ (2 : ℝ) ^ a by positivity),
    ENNReal.ofReal_mul (show 0 ≤ (2 : ℝ) ^ 301 by positivity)] at hcast
  simpa only [ENNReal.ofReal_pow (show 0 ≤ (2 : ℝ) by norm_num),
    ENNReal.ofReal_ofNat, ofReal_inv_two_pow] using hcast
noncomputable local instance : SampleableType (SearchKey → HashOutput) := Presampling.tableSampler
def SearchAgreement (outputs : SearchKey → HashOutput) (answers : Answers) : Prop :=
  ∀ key, answers (.inl (.inr (searchQuery key))) = outputs key
def tableGood (outputs : SearchKey → HashOutput) : Prop :=
  SearchesSucceed (Presampling.tableAnswers outputs zeroAnswers)
theorem layerCounterSearch_none_agreement (outputs : SearchKey → HashOutput)
    (answers : Answers) (hagree : SearchAgreement outputs answers) (lay : Layer) (r : Fin (2 ^ 32))
    (msg : ClaudeWCT.WCT9.LayerMsg) :
    evalWithAnswerFn answers
      (ClaudeWCT.WCT9.layerCounterSearch lay (routedTree lay r) (routedLeaf lay r) msg 0
        (ClaudeWCT.WCT9.searchLimit lay)) = none ↔
    ∀ c : Fin (ClaudeWCT.WCT9.searchLimit lay), ClaudeWCT.W9.T3.ProducerV5.producerEncodingDecode lay
      (outputs (.inl ((lay, r, msgLeft msg, msgRight msg),
        Fin.castLE (Presampling.searchLimit_le_rows lay) c))) = none := by
  rw [layerCounterSearch_none_iff]
  have hv (c : Nat) (hc : c < ClaudeWCT.WCT9.searchLimit lay) :
      evalWithAnswerFn answers
        (ClaudeWCT.WCT9.encodingHash lay (ClaudeWCT.WCT9.layerEncodingInput lay (routedTree lay r) (routedLeaf lay r) msg
          (BitVec.ofNat 32 (0 + c)))) =
        ClaudeWCT.WCT9.encodingAnswer lay (outputs (.inl ((lay, r, msgLeft msg, msgRight msg),
          Fin.castLE (Presampling.searchLimit_le_rows lay) ⟨c, hc⟩))) := by
    rw [Nat.zero_add, eval_shortHash_layer]
    have hinput : pairTrial lay (routedTree lay r) (routedLeaf lay r) (msgLeft msg) (msgRight msg) c =
        searchQuery (.inl ((lay, r, msgLeft msg, msgRight msg),
          Fin.castLE (Presampling.searchLimit_le_rows lay) ⟨c, hc⟩)) := rfl
    rw [hinput, hagree]
  constructor
  · intro h c
    have h := h c c.isLt
    rw [hv c c.isLt] at h
    exact h
  · intro h c hc
    rw [hv c hc]
    exact h ⟨c, hc⟩
theorem encodingFamily_none_iff (outputs : SearchKey → HashOutput) (answers : Answers)
    (hagree : SearchAgreement outputs answers) (family : EncodingFamilyBC) :
    EncodingFailedBC family answers ↔ EncodingFailedBC family (Presampling.tableAnswers outputs zeroAnswers) :=
  (layerCounterSearch_none_agreement outputs answers hagree family.1 family.2.1
    (.pair family.2.2.1 family.2.2.2)).trans
    (Presampling.layerCounterSearch_none_table outputs zeroAnswers family.1 family.2.1
      (.pair family.2.2.1 family.2.2.2)).symm
theorem digestSearch_none_agreement (outputs : SearchKey → HashOutput)
    (answers : Answers) (hagree : SearchAgreement outputs answers) (family : DigestFamily) :
    evalWithAnswerFn answers
      (ClaudeWCT.WCT9.digestSearch family.1 family.2 0 digestAttemptLimit) = none ↔
    ∀ c : Fin (2 ^ 21), digestDecode (outputs (.inr (family, c))) = none := by
  rw [ClaudeWCT.WCT9.digestSearch_none_iff]
  have hv (c : Nat) (hc : c < digestAttemptLimit) :
      evalWithAnswerFn answers (digest family.1 family.2 (BitVec.ofNat 32 (0 + c))) =
        outputs (.inr (family, ⟨c, hc⟩)) := by
    rw [SigGolfCandidate.T3.Presampling.eval_digest]
    have hinput : pad64 (digestInput family.1 family.2 (BitVec.ofNat 32 (0 + c))) =
        searchQuery (.inr (family, ⟨c, hc⟩)) := by
      simp only [searchQuery, Sum.elim_inr, ClaudeWCT.W9.T3.QuerySpace.digestQuery,
        SigGolfCandidate.T3.Sampling.digestTrial, Nat.zero_add]
    rw [hinput, hagree]
  constructor
  · intro h c
    rw [ClaudeWCT.W9.T3.Sampling.digestDecode_eq_none_iff]
    have h := h c c.isLt
    rwa [hv c c.isLt] at h
  · intro h c hc
    rw [hv c hc]
    exact (ClaudeWCT.W9.T3.Sampling.digestDecode_eq_none_iff _).mp (h ⟨c, hc⟩)
theorem digestFamily_none_iff (outputs : SearchKey → HashOutput) (answers : Answers)
    (hagree : SearchAgreement outputs answers) (family : DigestFamily) :
    DigestFailed family answers ↔ DigestFailed family (Presampling.tableAnswers outputs zeroAnswers) :=
  (digestSearch_none_agreement outputs answers hagree family).trans
    (Presampling.digestSearch_none_table outputs zeroAnswers family).symm
theorem tableGood_iff_searchesSucceed (outputs : SearchKey → HashOutput)
    (answers : Answers) (hagree : SearchAgreement outputs answers) :
    tableGood outputs ↔ SearchesSucceed answers := by
  unfold tableGood
  rw [← not_iff_not, not_searchesSucceed_iff, not_searchesSucceed_iff]
  exact or_congr (exists_congr fun family => (digestFamily_none_iff outputs answers hagree family).symm)
    (exists_congr fun family => (encodingFamily_none_iff outputs answers hagree family).symm)
theorem tableGood_searchesSucceed (outputs : SearchKey → HashOutput)
    (answers : Answers) (hgood : tableGood outputs) (hagree : SearchAgreement outputs answers) :
    SearchesSucceed answers := (tableGood_iff_searchesSucceed outputs answers hagree).mp hgood
theorem tableGood_fallback_iff (outputs : SearchKey → HashOutput) (fallback : Answers) :
    tableGood outputs ↔ SearchesSucceed (Presampling.tableAnswers outputs fallback) :=
  tableGood_iff_searchesSucceed outputs _ (Presampling.tableAnswers_apply outputs fallback)
theorem encodingFamily_table_failure (encodingFail : ENNReal)
    (he : ∀ lay, failMass (ClaudeWCT.W9.T3.ProducerV5.producerEncodingDecode lay) ^ ClaudeWCT.WCT9.searchLimit lay ≤
      encodingFail)
    (family : EncodingFamilyBC) :
    Pr[fun outputs => EncodingFailedBC family (Presampling.tableAnswers outputs zeroAnswers) |
      ($ᵗ (SearchKey → HashOutput) : ProbComp _)] ≤ encodingFail :=
  (Presampling.layerCounterSearch_table_failure zeroAnswers family.1 family.2.1
    family.2.2.1 family.2.2.2).le.trans (he family.1)
theorem tableGood_failure_le (digestFail encodingFail : ENNReal)
    (hd : failMass digestDecode ^ digestAttemptLimit ≤ digestFail)
    (he : ∀ lay, failMass (ClaudeWCT.W9.T3.ProducerV5.producerEncodingDecode lay) ^ ClaudeWCT.WCT9.searchLimit lay ≤
      encodingFail) :
    Pr[fun outputs => ¬tableGood outputs |
      ($ᵗ (SearchKey → HashOutput) : ProbComp _)] ≤
      (2 : ENNReal) ^ 384 * digestFail + (2 : ENNReal) ^ 301 * encodingFail := by
  let law := ($ᵗ (SearchKey → HashOutput) : ProbComp _)
  have hd' := finite_family_failure_le law
    (fun family outputs => DigestFailed family (Presampling.tableAnswers outputs zeroAnswers)) digestFail
    (fun family => (Presampling.digestSearch_table_failure zeroAnswers family).le.trans hd)
  have he' := finite_family_failure_le law
    (fun family outputs => EncodingFailedBC family (Presampling.tableAnswers outputs zeroAnswers)) encodingFail
    (encodingFamily_table_failure encodingFail he)
  rw [digestFamily_card, Nat.cast_pow, Nat.cast_ofNat] at hd'
  replace he' := he'.trans (mul_le_mul' encodingFamilyBC_card_le le_rfl)
  simp only [tableGood, not_searchesSucceed_iff]
  exact (probEvent_or_le law _ _).trans (add_le_add hd' he')
def tableGoodFor (message : Message) (outputs : SearchKey → HashOutput) : Prop :=
  SearchesSucceedFor (Presampling.tableAnswers outputs zeroAnswers) message
theorem not_searchesSucceedFor_iff (answers : Answers) (message : Message) :
    ¬ SearchesSucceedFor answers message ↔
      (∃ rho : Digest, DigestFailed (rho, message) answers) ∨ (∃ family, EncodingFailedBC family answers) := by
  classical
  simp only [SearchesSucceedFor, EncodingSearchesSucceedBC,
    ← Option.ne_none_iff_exists', not_and_or, not_forall, not_not, DigestFailed, EncodingFailedBC]
theorem tableGoodFor_iff_searchesSucceedFor (message : Message) (outputs : SearchKey → HashOutput)
    (answers : Answers) (hagree : SearchAgreement outputs answers) :
    tableGoodFor message outputs ↔ SearchesSucceedFor answers message := by
  unfold tableGoodFor
  rw [← not_iff_not, not_searchesSucceedFor_iff, not_searchesSucceedFor_iff]
  exact or_congr (exists_congr fun rho => (digestFamily_none_iff outputs answers hagree (rho, message)).symm)
    (exists_congr fun family => (encodingFamily_none_iff outputs answers hagree family).symm)
theorem tableGoodFor_searchesSucceedFor (message : Message) (outputs : SearchKey → HashOutput)
    (answers : Answers) (hgood : tableGoodFor message outputs) (hagree : SearchAgreement outputs answers) :
    SearchesSucceedFor answers message :=
  (tableGoodFor_iff_searchesSucceedFor message outputs answers hagree).mp hgood
theorem tableGoodFor_failure_le (message : Message) (digestFail encodingFail : ENNReal)
    (hd : failMass digestDecode ^ digestAttemptLimit ≤ digestFail)
    (he : ∀ lay, failMass (ClaudeWCT.W9.T3.ProducerV5.producerEncodingDecode lay) ^ ClaudeWCT.WCT9.searchLimit lay ≤
      encodingFail) :
    Pr[fun outputs => ¬tableGoodFor message outputs |
      ($ᵗ (SearchKey → HashOutput) : ProbComp _)] ≤
      (2 : ENNReal) ^ 128 * digestFail + (2 : ENNReal) ^ 301 * encodingFail := by
  let law := ($ᵗ (SearchKey → HashOutput) : ProbComp _)
  have hd' := finite_family_failure_le law
    (fun (rho : Digest) outputs => DigestFailed (rho, message) (Presampling.tableAnswers outputs zeroAnswers))
    digestFail
    (fun rho => (Presampling.digestSearch_table_failure zeroAnswers (rho, message)).le.trans hd)
  have he' := finite_family_failure_le law
    (fun family outputs => EncodingFailedBC family (Presampling.tableAnswers outputs zeroAnswers)) encodingFail
    (encodingFamily_table_failure encodingFail he)
  rw [Fintype.card_bitVec, Nat.cast_pow, Nat.cast_ofNat] at hd'
  replace he' := he'.trans (mul_le_mul' encodingFamilyBC_card_le le_rfl)
  simp only [tableGoodFor, not_searchesSucceedFor_iff]
  exact (probEvent_or_le law _ _).trans (add_le_add hd' he')
def tableGoodForNonces (nonces : Message → HashOutput) (outputs : SearchKey → HashOutput) : Prop :=
  (∀ message : Message, ∃ found,
    evalWithAnswerFn (Presampling.tableAnswers outputs zeroAnswers)
      (ClaudeWCT.WCT9.digestSearch ((nonces message).extractLsb' 0 128) message 0 digestAttemptLimit) =
        some found) ∧
  EncodingSearchesSucceedBC (Presampling.tableAnswers outputs zeroAnswers)
def NonceAgreement (nonces : Message → HashOutput) (answers : Answers) : Prop :=
  ∀ message, evalWithAnswerFn answers (privateNonce message) = (nonces message).extractLsb' 0 128
theorem tableGoodForNonces_searchesSucceedSelected (nonces : Message → HashOutput)
    (outputs : SearchKey → HashOutput) (answers : Answers)
    (hgood : tableGoodForNonces nonces outputs) (hagree : SearchAgreement outputs answers)
    (hnonce : NonceAgreement nonces answers) : SearchesSucceedSelected answers := by
  constructor
  · intro message
    rw [hnonce]
    apply Option.ne_none_iff_exists'.mp
    intro hnone
    have hnone' := (digestFamily_none_iff outputs answers hagree
      ((nonces message).extractLsb' 0 128, message)).mp hnone
    obtain ⟨found, hfound⟩ := hgood.1 message
    simp only [DigestFailed] at hnone'
    rw [hfound] at hnone'
    cases hnone'
  · intro family
    apply Option.ne_none_iff_exists'.mp
    intro hnone
    have hnone' := (encodingFamily_none_iff outputs answers hagree family).mp hnone
    obtain ⟨found, hfound⟩ := hgood.2 family
    simp only [EncodingFailedBC] at hnone'
    rw [hfound] at hnone'
    cases hnone'
theorem not_tableGoodForNonces_iff (nonces : Message → HashOutput)
    (outputs : SearchKey → HashOutput) :
    ¬tableGoodForNonces nonces outputs ↔
    (∃ message : Message, DigestFailed ((nonces message).extractLsb' 0 128, message)
      (Presampling.tableAnswers outputs zeroAnswers)) ∨
    (∃ family, EncodingFailedBC family (Presampling.tableAnswers outputs zeroAnswers)) := by
  classical
  simp only [tableGoodForNonces, EncodingSearchesSucceedBC,
    ← Option.ne_none_iff_exists', not_and_or, not_forall, not_not, DigestFailed, EncodingFailedBC]
theorem union_failure_small_bc {α ι κ : Type} [Fintype ι] [Fintype κ] (law : ProbComp α)
    (digestFailed : ι → α → Prop) (encodingFailed : κ → α → Prop)
    (hι : Fintype.card ι ≤ 2 ^ 256) (hκ : Fintype.card κ ≤ 2 ^ 301)
    (hd : ∀ i, Pr[digestFailed i | law] ≤ 1 / (2 : ENNReal) ^ 450)
    (he : ∀ k, Pr[encodingFailed k | law] ≤ 1 / (2 : ENNReal) ^ 600) :
    Pr[fun value => (∃ i, digestFailed i value) ∨ (∃ k, encodingFailed k value) | law] ≤
      1 / (2 : ENNReal) ^ 193 := by
  have hd' := finite_family_failure_le law digestFailed _ hd
  have he' := finite_family_failure_le law encodingFailed _ he
  have hι' : (Fintype.card ι : ENNReal) ≤ 2 ^ 256 := by exact_mod_cast hι
  have hκ' : (Fintype.card κ : ENNReal) ≤ 2 ^ 301 := by exact_mod_cast hκ
  refine ((probEvent_or_le law _ _).trans (add_le_add hd' he')).trans ?_
  refine (add_le_add (mul_le_mul' hι' le_rfl) (mul_le_mul' hκ' le_rfl)).trans ?_
  exact union_ennreal 256 193 BaseAudit.V5.completeness_union
end ClaudeWCT.W9.T3.Budgets
end
end
end
-- ==== merged from ClaudeWCT_W9_T3_FullCache_NativeBudgetB1_Moment ====
section

section
namespace ClaudeWCT.W9.T3.LayerBudget
open OracleComp OracleSpec ENNReal
open SphincsSecurity.Completeness (failMass)
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling SigGolfCandidate.T3.Cost SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.Budgets (signingZ signing_z_le EncodingFreshBelow SourceFreshness V_bind_bounded
  post_of_roRun)
open ClaudeWCT.W9.T3.ProducerV5 (producerEncodingDecode)
open ClaudeWCT.W9.T3.PairRows (PairFreshBelow layerTrial V_layerCounterSearch bound_layerCounterSearch
  avoids_layerCounterSearch preserves_pairBelow)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace Envelopes
section AvoidsSupport
open SigGolfCandidate.T3.Freshness (Avoids avoids_pure avoids_bind)
theorem avoids_bind_support {α β : Type} {secret : BitVec 256} {target : HashInput} {program : M α}
    {next : α → M β} (hp : Avoids secret target program)
    (hn : ∀ a ∈ support program, Avoids secret target (next a)) : Avoids secret target (program >>= next) := by
  induction program using OracleComp.inductionOn with
  | pure a =>
    rw [pure_bind]
    exact hn a (by simp)
  | query_bind t mx ih =>
    rw [bind_assoc]
    change AllQueriesSatisfy _ _ at hp ⊢
    rw [allQueriesSatisfy_query_bind_iff] at hp ⊢
    refine ⟨hp.1, fun u => ih u (hp.2 u) fun a ha => hn a ?_⟩
    rw [mem_support_bind_iff]
    exact ⟨u, by simp, ha⟩
theorem avoids_mapM_mem {α β : Type} {secret : BitVec 256} {target : HashInput} (f : α → M β) :
    ∀ items : List α, (∀ a ∈ items, Avoids secret target (f a)) → Avoids secret target (items.mapM f)
  | [], _ => by rw [List.mapM_nil]; exact avoids_pure secret target _
  | a :: items, h => by
    rw [List.mapM_cons]
    exact avoids_bind (h a List.mem_cons_self) fun _ =>
      avoids_bind (avoids_mapM_mem f items fun b hb => h b (List.mem_cons_of_mem a hb)) fun _ =>
        avoids_pure secret target _
theorem length_of_mem_support_mapM {α β : Type} (f : α → M β) :
    ∀ (xs : List α) (ys : List β), ys ∈ support (xs.mapM f) → ys.length = xs.length
  | [], ys, h => by simpa using h
  | x :: xs, ys, h => by
    rw [List.mapM_cons, mem_support_bind_iff] at h
    obtain ⟨y, -, h⟩ := h
    rw [mem_support_bind_iff] at h
    obtain ⟨zs, hzs, h⟩ := h
    simp only [support_pure, Set.mem_singleton_iff] at h
    subst h
    simp [length_of_mem_support_mapM f xs zs hzs]
theorem mem_support_foldlM_inv {α β : Type} (f : α → β → M α) (Inv : Nat → α → Prop)
    (hstep : ∀ k a b, Inv k a → ∀ a' ∈ support (f a b), Inv (k + 1) a') :
    ∀ (xs : List β) (k : Nat) (init : α), Inv k init → ∀ s ∈ support (xs.foldlM f init), Inv (k + xs.length) s
  | [], k, init, hinit, s, hs => by
    rw [List.foldlM_nil] at hs
    simp only [support_pure, Set.mem_singleton_iff] at hs
    subst hs
    simpa using hinit
  | x :: xs, k, init, hinit, s, hs => by
    rw [List.foldlM_cons, mem_support_bind_iff] at hs
    obtain ⟨a, ha, hs⟩ := hs
    have := mem_support_foldlM_inv f Inv hstep xs (k + 1) a (hstep k init x hinit a ha) s hs
    simpa [Nat.add_assoc, Nat.add_comm 1] using this
theorem avoids_foldlM_range'_inv {α : Type} {secret : BitVec 256} {target : HashInput} (f : α → Nat → M α)
    (Inv : Nat → α → Prop) :
    ∀ n s, (∀ k a, s ≤ k → k < s + n → Inv k a →
        Avoids secret target (f a k) ∧ ∀ b ∈ support (f a k), Inv (k + 1) b) →
      ∀ init, Inv s init → Avoids secret target ((List.range' s n).foldlM f init)
  | 0, s, _, init, _ => by rw [List.range'_zero, List.foldlM_nil]; exact avoids_pure secret target init
  | n + 1, s, hstep, init, hinit => by
    rw [List.range'_succ, List.foldlM_cons]
    have h0 := hstep s init le_rfl (by omega) hinit
    exact avoids_bind_support h0.1 fun b hb =>
      avoids_foldlM_range'_inv f Inv n (s + 1)
        (fun k a hk hk' ha => hstep k a (by omega) (by omega) ha) b (h0.2 b hb)
end AvoidsSupport
section Avoid
open SigGolfCandidate.T3.Freshness
variable (secret : BitVec 256) (target : HashInput) (ht : SearchQ target)
include ht
theorem avoids_packedLowerSecret (lay : Layer) (tree q : Nat) (carry : Digest) :
    Avoids secret target (ClaudeWCT.WCT9.packedSecret (ClaudeWCT.WCT9.lowerSeedPair lay tree) q carry) := by
  unfold ClaudeWCT.WCT9.packedSecret ClaudeWCT.WCT9.lowerSeedPair
  split
  · exact avoids_bind (avoids_privatePair secret target ht 0 _ _ _ _ (by decide))
      fun _ => avoids_pure _ _ _
  · exact avoids_pure _ _ _
/-- C2/C3: a half-selecting hash makes the same single query as `shortHash`. -/
theorem avoids_halfHash_of_ne (high : Bool) (input : HashInput) (hne : pad64 input ≠ target) :
    Avoids secret target (ClaudeWCT.WCT9.halfHash high input) := by
  rw [ClaudeWCT.WCT9.halfHash_eq]
  apply avoids_bind
  · exact (allQueriesSatisfy_query_iff _ _).mpr hne
  · intro _; exact avoids_pure _ _ _
theorem avoids_chainW (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    Avoids secret target (ClaudeWCT.WCT9.chainW lay tree leaf i start count value) := by
  unfold ClaudeWCT.WCT9.chainW
  apply avoids_foldlM
  intro value step
  apply avoids_halfHash_of_ne secret target ht
  have hh : SigGolfCandidate.T3.QuerySpace.queryHeader (pad64 (ClaudeWCT.WCT9.chainInputW lay tree leaf i step value)) =
      SphincsSecurity.bytesLE 16 (chainHeader lay tree leaf i step) := by
    unfold ClaudeWCT.WCT9.chainInputW
    split
    · simpa only [List.append_assoc] using
        SigGolfCandidate.T3.QuerySpace.queryHeader_padded (SphincsSecurity.bytesLE 16 value) (zero16 ++ zero16)
          (by simp [SphincsSecurity.bytesLE_length]) (chainHeader lay tree leaf i step)
    · simpa only [SigGolfCandidate.T3.chainInput, List.append_assoc] using
        SigGolfCandidate.T3.QuerySpace.queryHeader_padded zero16 (zero16 ++ SphincsSecurity.bytesLE 16 value)
          (by simp [zero16]) (chainHeader lay tree leaf i step)
  exact searchQ_ne hh (chainHeader_not_search lay tree leaf i step) ht
theorem avoids_lowerLeafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    Avoids secret target (ClaudeWCT.WCT9.lowerLeafHash lay tree leaf ends) := by
  rw [ClaudeWCT.WCT9.lowerLeafHash_eq]
  unfold ClaudeWCT.WCT9.lowerHash
  apply avoids_halfHash_of_ne secret target ht
  exact searchQ_ne (SigGolfCandidate.T3.QuerySpace.queryHeader_leafInput ..) (leafTweak_not_search lay tree leaf) ht
omit ht in
/-- C2: the packed lower node word has marker `128 + heap` (heap < 128), so it is no search header. -/
theorem lowerTweak_not_search (lay tree heap : Nat) (hh : heap < 128) :
    ¬ SearchHdr (ClaudeWCT.WCT9.lowerTweak lay tree heap) := by
  have hm : tweakMarker (ClaudeWCT.WCT9.lowerTweak lay tree heap) = 128 + heap := by
    unfold ClaudeWCT.WCT9.lowerTweak ClaudeWCT.WCT9.lowerNodeWord ClaudeWCT.WCT9.lowerK
    rw [append64_marker, BitVec.toNat_add, BitVec.toNat_ofNat, hyperWord_toNat]
    omega
  unfold SearchHdr RowHdr; omega
theorem avoids_lowerNodeHash (lay tree heap : Nat) (left right : Digest) (hh : lay ≠ 0 → heap < 128) :
    Avoids secret target (ClaudeWCT.WCT9.lowerNodeHash lay tree heap left right) := by
  unfold ClaudeWCT.WCT9.lowerNodeHash ClaudeWCT.WCT9.lowerHash
  apply avoids_halfHash_of_ne secret target ht
  have hq : SigGolfCandidate.T3.QuerySpace.queryHeader
      (pad64 (ClaudeWCT.WCT9.merkleNodeInput lay tree heap left right)) =
      SphincsSecurity.bytesLE 16 (ClaudeWCT.WCT9.merkleTweak lay tree heap) := by
    simpa only [ClaudeWCT.WCT9.merkleNodeInput, List.append_assoc] using
      (SigGolfCandidate.T3.QuerySpace.queryHeader_padded (SphincsSecurity.bytesLE 16 left)
        (zero16 ++ SphincsSecurity.bytesLE 16 right) (SphincsSecurity.bytesLE_length ..)
        (ClaudeWCT.WCT9.merkleTweak lay tree heap))
  refine searchQ_ne hq ?_ ht
  by_cases h0 : lay = 0
  · subst h0
    rw [ClaudeWCT.WCT9.merkleTweak_top]
    exact nodeTweak_not_search 3 0 tree heap (by decide) (fun _ h _ => by omega)
  · rw [ClaudeWCT.WCT9.merkleTweak_lower h0]
    exact lowerTweak_not_search lay tree heap (hh h0)
theorem avoids_lowerCoefs (lay : Layer) (tree leaf : Nat) (carry : List Digest) :
    Avoids secret target (ClaudeWCT.WCT9.lowerCoefs lay tree leaf carry) := by
  unfold ClaudeWCT.WCT9.lowerCoefs ClaudeWCT.WCT9.lowerFamCoefs ClaudeWCT.WCT9.lowerSeedPair
  split
  · exact avoids_bind (avoids_bind (avoids_foldlM _ _ _ _ (fun state j =>
      avoids_bind (avoids_privatePair secret target ht 0 _ _ _ _ (by decide)) fun _ => avoids_pure _ _ _) _)
      fun _ => avoids_pure _ _ _) fun _ => avoids_pure _ _ _
  · exact avoids_pure _ _ _
theorem avoids_buildLeafPF (lay : Layer) (tree leaf : Nat) (digits : List Nat) (carry : List Digest) :
    Avoids secret target (ClaudeWCT.WCT9.buildLeafPF lay tree leaf digits carry) := by
  unfold ClaudeWCT.WCT9.buildLeafPF
  refine avoids_bind ?_ fun cc => ?_
  · exact avoids_lowerCoefs secret target ht _ _ _ _
  rcases cc with ⟨coefs, carry'⟩
  refine avoids_bind (avoids_foldlM _ _ _ _ (fun state i => ?_) _)
    (fun state => avoids_bind (avoids_lowerLeafHash secret target ht _ _ _ _) fun _ => avoids_pure _ _ _)
  exact avoids_bind (avoids_chainW secret target ht _ _ _ _ _ _ _) fun value =>
    avoids_bind (avoids_chainW secret target ht _ _ _ _ _ _ _) fun _ => avoids_pure _ _ _
/-- C2: the lower levels use `lowerLevel` (packed node word, heap < 128 below the root of a height-7 tree). -/
theorem avoids_buildLevel_below (lay tree h level : Nat) (nodes : List Digest) (hlev : level < h) (h1 : 1 ≤ level)
    (h7 : lay ≠ 0 → h ≤ 7) (hlen : nodes.length / 2 ≤ 2 ^ (h - level)) :
    Avoids secret target (ClaudeWCT.WCT9.lowerLevel lay tree h level nodes) := by
  unfold ClaudeWCT.WCT9.lowerLevel
  refine avoids_mapM_mem _ _ fun i hi => avoids_lowerNodeHash secret target ht _ _ _ _ _ fun hl => ?_
  have hi : i < nodes.length / 2 := List.mem_range.mp hi
  have hp : 2 ^ (h - level) ≤ 2 ^ 6 := Nat.pow_le_pow_right (by decide) (by have := h7 hl; omega)
  have : (2 : Nat) ^ 6 = 64 := by norm_num
  omega
theorem avoids_buildLevelsBelow (lay tree h : Nat) (hh : lay ≠ 0 → h ≤ 7) (leaves : List Digest)
    (hlen : leaves.length ≤ 2 ^ h) :
    Avoids secret target (ClaudeWCT.WCT9.buildLevelsBelow 3 lay tree h leaves) := by
  unfold ClaudeWCT.WCT9.buildLevelsBelow
  refine avoids_foldlM_range'_inv _ (fun k (levels : List (List Digest)) => levels.length = k ∧
      ∀ j < k, (levels.getD j []).length ≤ 2 ^ (h - j)) (h - 1) 1 ?_ [leaves]
    ⟨rfl, fun j hj => by rw [show j = 0 by omega]; simpa using hlen⟩
  intro k levels hk hk' ⟨hlk, hshape⟩
  have hnodes := hshape (k - 1) (by omega)
  rw [show h - (k - 1) = h - k + 1 by omega, Nat.pow_succ] at hnodes
  refine ⟨avoids_bind (avoids_buildLevel_below secret target ht lay tree h k _ (by omega) (by omega) hh (by omega))
    fun _ => avoids_pure _ _ _, fun b hb => ?_⟩
  rw [mem_support_bind_iff] at hb
  obtain ⟨nodes, hn, hb⟩ := hb
  simp only [support_pure, Set.mem_singleton_iff] at hb
  subst hb
  have hlenN : nodes.length = (levels.getD (k - 1) []).length / 2 := by
    unfold ClaudeWCT.WCT9.lowerLevel at hn
    rw [length_of_mem_support_mapM _ _ _ hn, List.length_range]
  refine ⟨by simp [hlk], fun j hj => ?_⟩
  by_cases hjk : j < k
  · rw [List.getD_append _ _ _ _ (by omega)]
    exact hshape j hjk
  · rw [show j = k by omega, List.getD_append_right _ _ _ _ (by omega), hlk, Nat.sub_self, List.getD_cons_zero,
      hlenN]
    omega
end Avoid
end Envelopes
end ClaudeWCT.W9.T3.LayerBudget
end
section
namespace ClaudeWCT.W9.T3.Budgets
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Completeness (failMass)
open ClaudeWCT.WCT9 (Signature Witness digestAttemptLimit)
open ClaudeWCT.WCT9.Rev3 (sign expand verify signPayload)
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.Sampling (RCache roRun V V_pure V_of_bound)
open SigGolfCandidate.T3.Budgets (signingZ signing_z_le V_bind_bounded post_of_roRun signingZ_pow)
open ClaudeWCT.W9.T3.PairRows (PairFreshBelow AllSearchesFreshBC digestSearch_preserves_pairBelow
  privateMac_preserves_fresh privateNonce_preserves_fresh)
open SigGolfCandidate.T3.BaseAudit (zU)
open SigGolfCandidate.T3.Cost (bound_privateNonce bound_privateMac)
open ClaudeWCT.W9.T3.Sampling (digestDecode)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
end ClaudeWCT.W9.T3.Budgets
end

namespace SigGolfCandidate.Research.SharedSigningBudget
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling SigGolfCandidate.T3.Cost
open SigGolfCandidate.T3.Budgets (V_bind_bounded)
open ClaudeWCT.WCT9
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- The forest and retained lower roots consume a fixed budget before the
canonical search. The bound on that search is required only at reached states. -/
theorem V_signFromOutput_fixed (secret : BitVec 256) (z L : ENNReal) (hz : 1 ≤ z)
    (cache : SigGolfCandidate.T3.Cache) (rho : Digest) (counter : BitVec 32)
    (output : HashOutput) (rcache : RCache)
    (hsearch : ∀ forest ∈ support (roRun secret
        (SigGolfCandidate.Research.SharedForest.buildForest (digestIndex output) (SigGolfCandidate.Research.SharedForest.forestSelectionFromOutput output)
          (SigGolfCandidate.Research.SharedForest.forestWordsFromOutput output)) rcache),
      ∀ prepared ∈ support (roRun secret (SigGolfCandidate.Research.SharedForest.prepareRoots (digestIndex output)) forest.2),
      V secret z (SigGolfCandidate.Research.SharedForest.searchPreparedLayers cache (digestIndex output) prepared.1 forest.1.2
        (SigGolfCandidate.Research.SharedForest.conditionalCredit output)
        (SigGolfCandidate.Research.SharedForest.conditionalTopFloor output))
        prepared.2 ≤ L) :
    V secret z (SigGolfCandidate.Research.SharedForest.signFromOutput cache rho counter output) rcache ≤ z ^ 112142 * L := by
  unfold SigGolfCandidate.Research.SharedForest.signFromOutput
  refine (V_bind_bounded secret z _ _ rcache (z ^ 31321) (z ^ 80821 * L)
    (V_of_bound (SigGolfCandidate.Research.SharedForest.bound_buildForest ..) secret z hz rcache) ?_).trans_eq ?_
  · intro forest hforest
    have hp := SigGolfCandidate.Research.SharedForest.bound_prepareRoots (digestIndex output)
    rw [SigGolfCandidate.Research.SharedForest.prepared_roots_cost] at hp
    refine V_bind_bounded secret z _ _ forest.2 (z ^ 80821) L
      (V_of_bound hp secret z hz forest.2) ?_
    intro prepared hprepared
    refine (V_bind_bounded secret z _ _ prepared.2 L 1
      (hsearch forest hforest prepared hprepared) ?_).trans_eq (mul_one L)
    intro layers _
    cases layers.1 <;> simp only [V_pure, le_refl]
  · rw [← mul_assoc, ← pow_add]

/-- The payload adds the private nonce's two compressions. -/
theorem V_signPayload_fixed (secret : BitVec 256) (z D P : ENNReal) (hz : 1 ≤ z)
    (hP : 1 ≤ P) (cache : SigGolfCandidate.T3.Cache) (message : Message) (rcache : RCache)
    (hdigest : ∀ nonce ∈ support (roRun secret (privateNonce message) rcache),
      V secret z (SigGolfCandidate.Research.SharedForest.sharedDigestSearch nonce.1 message 0 digestAttemptLimit) nonce.2 ≤ D)
    (hnext : ∀ nonce ∈ support (roRun secret (privateNonce message) rcache),
      ∀ found ∈ support (roRun secret
        (SigGolfCandidate.Research.SharedForest.sharedDigestSearch nonce.1 message 0 digestAttemptLimit) nonce.2),
      ∀ counter output, found.1 = some (counter, output) →
        V secret z (SigGolfCandidate.Research.SharedForest.signFromOutput cache nonce.1 counter output) found.2 ≤ P) :
    V secret z (SigGolfCandidate.Research.SharedForest.signPayload cache message) rcache ≤ z ^ 2 * (D * P) := by
  unfold SigGolfCandidate.Research.SharedForest.signPayload
  refine V_bind_bounded secret z _ _ rcache (z ^ 2) (D * P)
    (V_of_bound (bound_privateNonce message) secret z hz rcache) ?_
  intro nonce hnonce
  refine V_bind_bounded secret z _ _ nonce.2 D P (hdigest nonce hnonce) ?_
  intro found hfound
  cases he : found.1 with
  | none => simpa only [V_pure] using hP
  | some pair =>
      obtain ⟨counter, output⟩ := pair
      refine (V_bind_bounded secret z _ _ found.2 P 1
        (hnext nonce hnonce found hfound counter output he) ?_).trans_eq (mul_one P)
      intro result _
      cases result.1 <;> simp only [V_pure, le_refl]

/-- Cache authentication adds two compressions, including the rejecting branch. -/
theorem V_sign_fixed (secret : BitVec 256) (z P : ENNReal) (hz : 1 ≤ z) (hP : 1 ≤ P)
    (cache : SigGolfCandidate.T3.Cache) (message : Message) (rcache : RCache)
    (hpayload : ∀ checked ∈ support (roRun secret (privateMac cache.region) rcache),
      checked.1 = cache.tag → V secret z (SigGolfCandidate.Research.SharedForest.signPayload cache message) checked.2 ≤ P) :
    V secret z (SigGolfCandidate.Research.SharedForest.sign cache message) rcache ≤ z ^ 2 * P := by
  unfold SigGolfCandidate.Research.SharedForest.sign
  refine V_bind_bounded secret z _ _ rcache (z ^ 2) P
    (V_of_bound (bound_privateMac cache.region) secret z hz rcache) ?_
  intro checked hchecked
  split
  · simpa only [V_pure] using hP
  · rename_i h
    exact hpayload checked hchecked (by simpa only [ne_eq, not_not] using h)

/-- The top-signing cost remains inside the search continuation; this identity
matches the numerical certificate's complete fixed-cost exponent. -/
theorem fixed_budget_factor (z D L : ENNReal) :
    z ^ 2 * (z ^ 2 * (D * (z ^ 112142 * (z ^ 180 * L)))) =
      z ^ 112326 * (D * L) := by
  rw [show 112326 = 2 + 2 + 112142 + 180 by decide, pow_add, pow_add, pow_add]
  ac_rfl

end SigGolfCandidate.Research.SharedSigningBudget

namespace ClaudeWCT.W9.T3.CanonicalSearch
open OracleComp OracleSpec OracleComp.EvalDist ENNReal Finset
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
open SphincsSecurity.Completeness ClaudeWCT.WCT9
open ClaudeWCT.Numerics.CanonicalCompression ClaudeWCT.Numerics.CanonicalHistogram
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- Finite histogram laws allow arbitrary continuation weights. The floor is
an external canonical context and need not be statistically independent of ancestors. -/
theorem acceptedWeight_histogram {β : Type} (n : Nat) [NeZero n]
    (dec : HashOutput → Option β) (credit : β → Nat)
    (hist : List (Nat × Nat)) (floor den : Nat) (weight : Nat → ENNReal)
    (hbound : ∀ answer value, dec answer = some value → credit value < n)
    (hlaw : ∀ i : Fin n,
      Pr[fun answer => ∃ value, dec answer = some value ∧ credit value = i.val |
        ($ᵗ HashOutput : ProbComp HashOutput)] =
      if floor ≤ i.val then (histogramWeight hist i.val : ENNReal) / den else 0) :
    acceptedWeight dec (fun value => weight (credit value)) =
      ∑ i : Fin n, if floor ≤ i.val then
        (histogramWeight hist i.val : ENNReal) / den * weight i.val else 0 := by
  rw [acceptedWeight_nat_labels n dec credit weight hbound]
  apply Finset.sum_congr rfl
  intro i _
  rw [hlaw i]
  split_ifs <;> simp

/-- The weighted next row is exactly the integer dot product certified by the
arithmetic packet, divided by the common probability and fixed-point denominators. -/
theorem acceptedWeight_nextMass {β : Type} (n : Nat) [NeZero n]
    (dec : HashOutput → Option β) (credit : β → Nat)
    (hist : List (Nat × Nat)) (floor residual den unit : Nat) (next : Array Nat)
    (hbound : ∀ answer value, dec answer = some value → credit value < n)
    (hhist : ∀ e ∈ hist, e.1 < n)
    (hlaw : ∀ i : Fin n,
      Pr[fun answer => ∃ value, dec answer = some value ∧ credit value = i.val |
        ($ᵗ HashOutput : ProbComp HashOutput)] =
      if floor ≤ i.val then (histogramWeight hist i.val : ENNReal) / den else 0) :
    acceptedWeight dec (fun value => (next[residual-credit value]?.getD 0 : ENNReal) / unit) =
      (nextMass hist floor residual next : ENNReal) / (den * unit) := by
  rw [acceptedWeight_histogram n dec credit hist floor den
      (fun c => (next[residual-c]?.getD 0 : ENNReal) / unit) hbound hlaw,
    nextMass_finite hist n floor residual next hhist]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Nat.cast_mul]
  simp only [div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inr (show (unit : ENNReal) ≠ ∞ by simp))
    (Or.inl (show (den : ENNReal) ≠ ∞ by simp)), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp [mul_assoc, mul_left_comm, mul_comm]

end ClaudeWCT.W9.T3.CanonicalSearch

namespace ClaudeWCT.W9.T3.CanonicalSearch
open OracleComp OracleSpec OracleComp.EvalDist ENNReal Finset
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
open SphincsSecurity.Completeness
open ClaudeWCT.Numerics.CanonicalCompression ClaudeWCT.Numerics.CanonicalHistogram
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem acceptedWeight_acceptedMass {β : Type} (n : Nat) [NeZero n]
    (dec : HashOutput → Option β) (credit : β → Nat)
    (hist : List (Nat × Nat)) (floor den : Nat)
    (hbound : ∀ answer value, dec answer = some value → credit value < n)
    (hhist : ∀ e ∈ hist, e.1 < n)
    (hlaw : ∀ i : Fin n,
      Pr[fun answer => ∃ value, dec answer = some value ∧ credit value = i.val |
        ($ᵗ HashOutput : ProbComp HashOutput)] =
      if floor ≤ i.val then (histogramWeight hist i.val : ENNReal) / den else 0) :
    acceptedWeight dec (fun _ => 1) = (acceptedMass hist floor : ENNReal) / den := by
  rw [acceptedWeight_histogram n dec credit hist floor den (fun _ => 1) hbound hlaw,
    acceptedMass_finite hist n floor hhist]
  simp only [mul_one, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
  simp only [div_eq_mul_inv]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

/-- Integer rejection counts exactly complement the selected mass. -/
theorem failMass_of_acceptedMass {β : Type} (dec : HashOutput → Option β) (mass den : Nat)
    (hden : 0 < den) (hmass : mass ≤ den)
    (ha : acceptedWeight dec (fun _ => 1) = (mass : ENNReal) / den) :
    failMass dec = ((den-mass : Nat) : ENNReal) / den := by
  have hm : acceptedWeight dec (fun _ => (1 : ENNReal)) + failMass dec = 1 := by
    have h := uniform_decoder_weight dec (fun _ => (1 : ENNReal)) 1
    have he (answer : HashOutput) : (dec answer).elim (1 : ENNReal) (fun _ => 1) = 1 := by
      cases dec answer <;> rfl
    simp_rw [he] at h
    rw [expectedValue_const (by simp)] at h
    simpa only [mul_one] using h.symm
  rw [ha] at hm
  have hn : (mass : ENNReal)/den + ((den-mass : Nat) : ENNReal)/den = 1 := by
    rw [← ENNReal.add_div, ← Nat.cast_add, Nat.add_sub_of_le hmass]
    exact ENNReal.div_self (by exact_mod_cast hden.ne') (by simp)
  have hfinite : (mass : ENNReal)/den ≠ ∞ := by
    exact ENNReal.div_ne_top (by simp) (by exact_mod_cast hden.ne')
  have hf := ENNReal.eq_sub_of_add_eq hfinite ((add_comm _ _).trans hm)
  have hn' := ENNReal.eq_sub_of_add_eq hfinite ((add_comm _ _).trans hn)
  exact hf.trans hn'.symm

end ClaudeWCT.W9.T3.CanonicalSearch

namespace ClaudeWCT.W9.T3.CanonicalSearch
open OracleComp OracleSpec OracleComp.EvalDist ENNReal Finset
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
open SphincsSecurity.Completeness
open ClaudeWCT.Numerics.CanonicalCompression ClaudeWCT.Numerics.CanonicalHistogram
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem decoder_recurrence {β : Type} (n : Nat) [NeZero n]
    (dec : HashOutput → Option β) (credit : β → Nat)
    (hist : List (Nat × Nat)) (floor residual den : Nat) (next : Array Nat) (value : Nat)
    (hden : 0 < den)
    (hbound : ∀ answer digits, dec answer = some digits → credit digits < n)
    (hhist : ∀ e ∈ hist, e.1 < n)
    (hlaw : ∀ i : Fin n,
      Pr[fun answer => ∃ digits, dec answer = some digits ∧ credit digits = i.val |
        ($ᵗ HashOutput : ProbComp HashOutput)] =
      if floor ≤ i.val then (histogramWeight hist i.val : ENNReal) / den else 0)
    (hcheck : recurrenceCheck den hist floor residual next value = true) :
    1 ≤ (value : ENNReal) / scale ∧
      ((zNum : ENNReal) / zDen) *
        (acceptedWeight dec (fun digits => (next[residual-credit digits]?.getD 0 : ENNReal) / scale) +
         failMass dec * ((value : ENNReal) / scale)) ≤ (value : ENNReal) / scale := by
  have hs := recurrenceCheck_sound den hist floor residual next value hden hcheck
  have hm : acceptedMass hist floor ≤ den := by
    simp only [recurrenceCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    exact hcheck.1.1.1.2
  rw [acceptedWeight_nextMass n dec credit hist floor residual den scale next hbound hhist hlaw,
    failMass_of_acceptedMass dec (acceptedMass hist floor) den hden hm
      (acceptedWeight_acceptedMass n dec credit hist floor den hbound hhist hlaw)]
  exact hs

end ClaudeWCT.W9.T3.CanonicalSearch

namespace ClaudeWCT.W9.T3.CanonicalSearch
open OracleComp OracleSpec OracleComp.EvalDist ENNReal Finset
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
open SphincsSecurity.Completeness ClaudeWCT.WCT9
open ClaudeWCT.W9.T3.ProducerV5.Canonical
open ClaudeWCT.Numerics ClaudeWCT.Numerics.CanonicalCompression
open ClaudeWCT.Numerics.CanonicalHistogram
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- The path-aware credit of a decoded answer (digits, selected half). -/
def dcredit (lay : Layer) (dl : List Nat × Bool) : Nat := CanonicalPolicy.credit lay dl.2 dl.1

theorem decoder_credit {lay : Layer} {floor : Nat} {answer : HashOutput} {dl : List Nat × Bool}
    (h : decoder lay floor answer = some dl) : floor ≤ dcredit lay dl := by
  obtain ⟨ds, l⟩ := dl
  exact CanonicalPolicy.producerDecodeOut_credit h

private theorem selected_probability_below (lay : Layer) (floor c : Nat) (hc : c < floor) :
    Pr[fun answer => ∃ dl, decoder lay floor answer = some dl ∧ dcredit lay dl = c |
      ($ᵗ HashOutput : ProbComp HashOutput)] = 0 := by
  have he : (fun answer => ∃ dl, decoder lay floor answer = some dl ∧ dcredit lay dl = c) =
      (fun _ : HashOutput => False) := by
    funext answer
    apply propext
    constructor
    · rintro ⟨dl, hd, hr⟩
      have hf := decoder_credit hd
      omega
    · exact False.elim
  rw [he]
  simp

theorem top_decoder_credit_lt {floor : Nat} (hf : 3 ≤ floor) {answer : HashOutput} {dl : List Nat × Bool}
    (h : decoder 0 floor answer = some dl) : dcredit 0 dl < 220 := by
  obtain ⟨ds, l⟩ := dl
  exact producerDecodeAt_top_credit_lt hf (CanonicalPolicy.producerDecodeOut_spec h).2

theorem lower_decoder_credit_lt (lay : Layer) (hl : lay ≠ 0) {floor : Nat} {answer : HashOutput}
    {dl : List Nat × Bool} (h : decoder lay floor answer = some dl) : dcredit lay dl < 128 := by
  obtain ⟨ds, l⟩ := dl
  exact producerDecodeAt_lower_credit_lt lay hl (CanonicalPolicy.producerDecodeOut_spec h).2

/-- The selected-credit law is unchanged when the top floor rises: the floor
only filters which of the same histogram entries are accepted. -/
theorem selected_top_probability_at (floor : Nat) (hf : 14 ≤ floor) (c : Fin 220) :
    Pr[fun answer => ∃ dl, decoder 0 floor answer = some dl ∧ dcredit 0 dl = c.val |
      ($ᵗ HashOutput : ProbComp HashOutput)] =
      if floor ≤ c.val then (histogramWeight ClaudeWCT.Numerics.TopZero.topAcceptedHistogram c.val : ENNReal) / topDen else 0 := by
  by_cases hc : floor ≤ c.val
  · rw [if_pos hc]
    classical
    rw [probEvent_uniformSample]
    have hcard := selected_top_path_card floor c.val hf hc
    rw [hcard, ClaudeWCT.Numerics.TopZero.topAcceptedHistogram,
      histogramWeight_split, if_pos (by omega : 2 ≤ c.val),
      topWordCount_eq_hist (c.val - 2) (by omega),
      topWordCount_eq_hist c.val (by omega), topHighWeight_eq]
    simp only [Fintype.card_bitVec, topDen, Nat.cast_pow, Nat.cast_ofNat]
    push_cast
    ring
  · rw [if_neg hc]
    exact selected_probability_below 0 floor c.val (by omega)

/-- The exact selected-credit law at the original top floor. -/
theorem selected_top_probability (c : Fin 220) :
    Pr[fun answer => ∃ dl, decoder 0 14 answer = some dl ∧ dcredit 0 dl = c.val |
      ($ᵗ HashOutput : ProbComp HashOutput)] =
      if 14 ≤ c.val then (histogramWeight ClaudeWCT.Numerics.TopZero.topAcceptedHistogram c.val : ENNReal) / topDen else 0 :=
  selected_top_probability_at 14 (by omega) c

/-- The exact selected-credit law of a canonical lower search (path-aware). -/
theorem selected_lower_probability (lay : Layer) (hl : lay ≠ 0) (floor : Nat) (c : Fin 128) :
    Pr[fun answer => ∃ dl, decoder lay floor answer = some dl ∧ dcredit lay dl = c.val |
      ($ᵗ HashOutput : ProbComp HashOutput)] =
      if floor ≤ c.val then (histogramWeight lowerHistogram c.val : ENNReal) / lowerDen else 0 := by
  by_cases hc : floor ≤ c.val
  · rw [if_pos hc]
    have hd (z : Fin 6) (i : Nat) (hi : i<128) :
        SharedDigitBlock.digit (2^132) SigGolfResearch.LowerEffectiveCounting.packed
          (65536*z.val+128*201+i) =
        (univ.filter fun w : SigGolfResearch.LowerEffectiveCounting.«Word» =>
          SigGolfResearch.LowerEffectiveCounting.zeros w = z.val ∧
          SigGolfResearch.LowerEffectiveCounting.weight w = 201 ∧
          SigGolfResearch.LowerEffectiveCounting.score w = i).card := by
      rw [← bits_digit_eq]
      exact CanonicalCounting.lower_digit z.val i hi
    exact selected_lower_histogram_probability hd lower_histogram_checked lay hl floor c.val hc c.isLt
  · rw [if_neg hc]
    exact selected_probability_below lay floor c.val (by omega)

end ClaudeWCT.W9.T3.CanonicalSearch

namespace ClaudeWCT.W9.T3.CanonicalSearch
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem acceptedWeight_one_probability {β : Type} (dec : HashOutput → Option β) :
    acceptedWeight dec (fun _ => 1) =
      Pr[fun answer => (dec answer).isSome | ($ᵗ HashOutput : ProbComp HashOutput)] := by
  classical
  unfold acceptedWeight
  have he (answer : HashOutput) : (dec answer).elim (0 : ENNReal) (fun _ => 1) =
      if (dec answer).isSome then 1 else 0 := by
    cases dec answer <;> simp
  simp_rw [he]
  exact expectedValue_ite_one _ _

end ClaudeWCT.W9.T3.CanonicalSearch


namespace ClaudeWCT.W9.T3.CanonicalSearch
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling SigGolfCandidate.T3.Freshness
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9 ClaudeWCT.W9.T3.LayerBudget.Envelopes ClaudeWCT.W9.T3.PairRows
open SigGolfCandidate.T3.QuerySpace
open SphincsSecurity (bytesLE bytesLE_length)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

section Avoid
variable (secret : BitVec 256) (target : HashInput) (ht : SearchQ target)
include ht

theorem avoids_chainPrefixes (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    Avoids secret target (chainPrefixes lay tree leaf i start count value) := by
  induction count generalizing start value with
  | zero => exact avoids_pure _ _ _
  | succ count ih =>
      unfold chainPrefixes
      apply avoids_bind
      · -- C3 (#866): a prefix step keeps the half `chainHigh lay i start` (same query input).
        apply avoids_halfHash_of_ne secret target ht
        have hh : queryHeader (pad64 (ClaudeWCT.WCT9.chainInputW lay tree leaf i start value)) =
            bytesLE 16 (chainHeader lay tree leaf i start) := by
          unfold ClaudeWCT.WCT9.chainInputW
          split
          · simpa only [List.append_assoc] using
              queryHeader_padded (bytesLE 16 value) (zero16 ++ zero16) (by simp [bytesLE_length])
                (chainHeader lay tree leaf i start)
          · simpa only [SigGolfCandidate.T3.chainInput, List.append_assoc] using
              queryHeader_padded zero16 (zero16 ++ bytesLE 16 value) (by simp [zero16])
                (chainHeader lay tree leaf i start)
        exact searchQ_ne hh (chainHeader_not_search lay tree leaf i start) ht
      · intro next
        exact avoids_bind (ih _ _) fun _ => avoids_pure _ _ _

theorem avoids_buildLeafPrefixes (lay : Layer) (tree leaf : Nat) (carry : List Digest) :
    Avoids secret target (buildLeafPrefixes lay tree leaf carry) := by
  unfold buildLeafPrefixes
  refine avoids_bind ?_ fun cc => ?_
  · exact avoids_lowerCoefs secret target ht _ _ _ _
  · rcases cc with ⟨coefs, carry'⟩
    exact avoids_bind (avoids_mapM _ _ _ _
      (fun i => avoids_chainPrefixes secret target ht _ _ _ _ _ _ _)) fun prefixes =>
      avoids_bind (avoids_lowerLeafHash secret target ht _ _ _ _) fun _ => avoids_pure _ _ _

theorem avoids_buildTreePrefixes (lay : Layer) (tree selected : Nat) :
    Avoids secret target (buildTreePrefixes lay tree selected) := by
  unfold buildTreePrefixes
  refine avoids_bind_support (avoids_foldlM _ _ _ _ (fun state leaf => ?_) _) fun state hs => ?_
  · dsimp only
    split
    · refine avoids_bind (avoids_buildLeafPrefixes secret target ht _ _ _ _) fun r => ?_
      rcases r with ⟨⟨root, prefixes⟩, carry⟩
      exact avoids_pure _ _ _
    · refine avoids_bind (avoids_buildLeafPF secret target ht _ _ _ _ _) fun r => ?_
      rcases r with ⟨⟨root, prefixes⟩, carry⟩
      simp only [pure_bind]
      exact avoids_pure _ _ _
  · have hlen := mem_support_foldlM_inv _
        (fun k (s : List Digest × List (List Digest) × List Digest) => s.1.length = k)
        (fun k a leaf ha a' ha' => by
          dsimp only at ha'
          split_ifs at ha' with hleaf
          all_goals
            rw [mem_support_bind_iff] at ha'
            obtain ⟨⟨⟨root, prefixes⟩, carry⟩, -, ha'⟩ := ha'
            simp only [pure_bind, support_pure, Set.mem_singleton_iff] at ha'
            subst ha'
            simp [ha]) _ 0 _ rfl state hs
    have hh : lay.val ≠ 0 → height lay ≤ 7 := by fin_cases lay <;> decide
    refine avoids_bind (avoids_buildLevelsBelow secret target ht _ _ _ hh _ ?_) fun _ => avoids_pure _ _ _
    simp only [List.length_range, Nat.zero_add] at hlen
    omega

theorem avoids_prepareRoots (index : Nat) : Avoids secret target (prepareRoots index) := by
  unfold prepareRoots
  exact avoids_bind (avoids_buildTreePrefixes secret target ht _ _ _) fun _ =>
    avoids_bind (avoids_buildTreePrefixes secret target ht _ _ _) fun _ =>
      avoids_bind (avoids_buildTreePrefixes secret target ht _ _ _) fun _ => avoids_pure _ _ _
end Avoid

theorem prepareRoots_preserves_rows (secret : BitVec 256) (index stage : Nat)
    (cache : RCache) (hfresh : RowsFreshFrom stage cache) (result : PreparedRoots × RCache)
    (hr : result ∈ support (roRun secret (prepareRoots index) cache)) :
    RowsFreshFrom stage result.2 := by
  intro lay hl tree leaf left right counter hc
  rw [preserves secret _ _ (avoids_prepareRoots secret _ (rowQ_pairTrial ..).searchQ index)
    cache result hr]
  exact hfresh lay hl tree leaf left right counter hc

end ClaudeWCT.W9.T3.CanonicalSearch

namespace ClaudeWCT.W9.T3.CanonicalSearch
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling SigGolfCandidate.T3.Cost
open SigGolfCandidate.T3.Budgets (V_bind_bounded)
open ClaudeWCT.WCT9
open CanonicalPolicy
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

structure SearchEnvelopeAt (z : ENNReal) (topFloor credit : Nat) where
  initial : ENNReal
  one : Nat → ENNReal
  two : Nat → ENNReal
  three : Nat → ENNReal
  initial_ge : 1 ≤ initial
  one_ge : ∀ r, r < 56 → 1 ≤ one r
  two_ge : ∀ r, r < 41 → 1 ≤ two r
  three_ge : ∀ r, r < 22 → 1 ≤ three r
  initial_step : z * (acceptedWeight (decoder 0 topFloor) (fun dl => one (nextResidual credit 0 dl.2 dl.1)) +
    SphincsSecurity.Completeness.failMass (decoder 0 topFloor) * initial) ≤ initial
  one_step : ∀ r, r < 56 → z *
    (acceptedWeight (decoder 1 (threshold 1 r)) (fun dl => two (nextResidual r 1 dl.2 dl.1)) +
     SphincsSecurity.Completeness.failMass (decoder 1 (threshold 1 r)) * one r) ≤ one r
  two_step : ∀ r, r < 41 → z *
    (acceptedWeight (decoder 2 (threshold 2 r)) (fun dl => three (nextResidual r 2 dl.2 dl.1)) +
     SphincsSecurity.Completeness.failMass (decoder 2 (threshold 2 r)) * two r) ≤ two r
  three_step : ∀ r, r < 22 → z *
    (acceptedWeight (decoder 3 (threshold 3 r)) (fun _ => 1) +
     SphincsSecurity.Completeness.failMass (decoder 3 (threshold 3 r)) * three r) ≤ three r

abbrev SearchEnvelope (z : ENNReal) := SearchEnvelopeAt z 14 69

theorem decoder_spec {lay : Layer} {floor : Nat} {answer : HashOutput} {ds : List Nat} {low : Bool}
    (h : decoder lay floor answer = some (ds, low)) :
    producerDecodeAt lay floor low (encodingAnswer lay answer) = some ds :=
  (producerDecodeOut_spec h).2

/-- The actual four searches follow canonical ancestors. Their continuation
weights depend on the remaining path-aware credit, and the retained lower reveals cost no HASH calls. -/
theorem V_searchPreparedLayers_at (secret : BitVec 256) (z : ENNReal) (hz : 1 ≤ z)
    (topFloor credit : Nat) (hgap : credit = topFloor + 55)
    (E : SearchEnvelopeAt z topFloor credit) (cache : SigGolfCandidate.T3.Cache) (index : Nat)
    (prepared : PreparedRoots) (forest : PairRoot) (rcache : RCache)
    (hfresh : RowsFreshFrom 0 rcache) :
    V secret z (searchPreparedLayers cache index prepared forest credit topFloor) rcache ≤ z^180 * E.initial := by
  have hfactor : 1 ≤ z^180 := one_le_pow₀ hz
  unfold searchPreparedLayers
  simp only [threshold_top]
  apply V_layerSearch_bind (secret := secret) (z := z) (lay := 0)
    (weight := fun dl => z^180 * E.one (nextResidual credit 0 dl.2 dl.1))
  · intro rc _
    simpa only [V_pure] using one_le_mul hfactor E.initial_ge
  · intro rc hr counter hc answer dl0 hd0
    obtain ⟨ds0, l0⟩ := dl0
    have hd0' := decoder_spec hd0
    have hres1 : nextResidual credit 0 l0 ds0 < 56 := by
      have hc := CanonicalPolicy.producerDecodeAt_credit hd0'
      unfold nextResidual
      omega
    have hp1 : threshold 1 (nextResidual credit 0 l0 ds0) < 16 :=
      lower_one_floor_lt ⟨nextResidual credit 0 l0 ds0, hres1⟩
    simp only [show ¬ (threshold 1 (nextResidual credit 0 l0 ds0) ≥ 16) by omega, ↓reduceIte]
    apply V_layerSearch_bind (secret := secret) (z := z) (lay := 1)
      (weight := fun dl => z^180 * E.two (nextResidual (nextResidual credit 0 l0 ds0) 1 dl.2 dl.1))
    · intro rc _
      simpa only [V_pure] using one_le_mul hfactor (E.one_ge _ hres1)
    · intro rc hr counter1 hc1 answer1 dl1 hd1
      obtain ⟨ds1, l1⟩ := dl1
      have hd1' := decoder_spec hd1
      have hres2 : nextResidual (nextResidual credit 0 l0 ds0) 1 l1 ds1 < 41 :=
        accepted_one_residual ⟨nextResidual credit 0 l0 ds0, hres1⟩ hd1'
      have hp2 : threshold 2 (nextResidual (nextResidual credit 0 l0 ds0) 1 l1 ds1) ≤ 19 :=
        (lower_two_progress ⟨nextResidual (nextResidual credit 0 l0 ds0) 1 l1 ds1, hres2⟩).1
      simp only [show ¬ (threshold 2 (nextResidual (nextResidual credit 0 l0 ds0) 1 l1 ds1) ≥ 22) by omega,
        ↓reduceIte]
      apply V_layerSearch_bind (secret := secret) (z := z) (lay := 2)
        (weight := fun dl => z^180 * E.three
          (nextResidual (nextResidual (nextResidual credit 0 l0 ds0) 1 l1 ds1) 2 dl.2 dl.1))
      · intro rc _
        simpa only [V_pure] using one_le_mul hfactor (E.two_ge _ hres2)
      · intro rc hr counter2 hc2 answer2 dl2 hd2
        obtain ⟨ds2, l2⟩ := dl2
        have hd2' := decoder_spec hd2
        have hres3 : nextResidual (nextResidual (nextResidual credit 0 l0 ds0) 1 l1 ds1) 2 l2 ds2 < 22 :=
          accepted_two_residual ⟨nextResidual (nextResidual credit 0 l0 ds0) 1 l1 ds1, hres2⟩ hd2'
        have hp3 := lower_three_progress _ hres3
        simp only [show ¬ (threshold 3
            (nextResidual (nextResidual (nextResidual credit 0 l0 ds0) 1 l1 ds1) 2 l2 ds2) ≥ 22) by omega,
          ↓reduceIte]
        apply V_layerSearch_bind (secret := secret) (z := z) (lay := 3) (weight := fun _ => z^180)
        · intro rc _
          simpa only [V_pure] using one_le_mul hfactor (E.three_ge _ hres3)
        · intro rc hr counter3 hc3 answer3 dl3 hd3
          obtain ⟨ds3, l3⟩ := dl3
          have hd : SigGolfCandidate.T3.decode 0 (encodingAnswer 0 answer) = some ds0 :=
            (producerDecodeAt_spec hd0').1
          have hds := SigGolfCandidate.T3.decode_length_sum hd
          have hbound := bound_signTop cache (route index 0).1 ds0
            (by exact hds.1)
            (by exact hds.2.le)
          refine (V_bind_bounded secret z _ _ rc (z^180) 1
            (V_of_bound hbound secret z hz rc) ?_).trans_eq (mul_one _)
          intro top _
          simp only [V_pure]
          exact le_rfl
        · simpa only [mul_one] using scaled_step z
            (E.three (nextResidual (nextResidual (nextResidual credit 0 l0 ds0) 1 l1 ds1) 2 l2 ds2))
            (z^180) _ (fun _ => 1) (E.three_step _ hres3)
        · decide
        · exact hr
      · exact scaled_step z _ (z^180) _ _ (E.two_step _ hres2)
      · decide
      · exact hr
    · exact scaled_step z _ (z^180) _ _ (E.one_step _ hres1)
    · decide
    · exact hr
  · exact scaled_step z _ (z^180) _ _ E.initial_step
  · decide
  · exact hfresh

theorem V_searchPreparedLayers (secret : BitVec 256) (z : ENNReal) (hz : 1 ≤ z)
    (E : SearchEnvelope z) (cache : SigGolfCandidate.T3.Cache) (index : Nat)
    (prepared : PreparedRoots) (forest : PairRoot) (rcache : RCache)
    (hfresh : RowsFreshFrom 0 rcache) :
    V secret z (searchPreparedLayers cache index prepared forest) rcache ≤ z^180 * E.initial := by
  simpa using V_searchPreparedLayers_at secret z hz 14 69 (by decide)
    E cache index prepared forest rcache hfresh

end ClaudeWCT.W9.T3.CanonicalSearch

namespace ClaudeWCT.W9.T3.CanonicalSearch
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
open SphincsSecurity.Completeness ClaudeWCT.WCT9 CanonicalPolicy
open ClaudeWCT.Numerics.CanonicalCompression ClaudeWCT.Numerics.CanonicalHistogram
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem acceptedWeight_congr_on {α : Type} (dec : HashOutput → Option α)
    (w v : α → ENNReal) (h : ∀ answer value, dec answer = some value → w value = v value) :
    acceptedWeight dec w = acceptedWeight dec v := by
  unfold acceptedWeight
  congr 1
  funext answer
  cases hd : dec answer with
  | none => rfl
  | some value => exact h answer value hd

/-- Integer continuation rows give the envelope for the actual canonical
source decoder, through its exact selected-credit law (path-aware credits). -/
noncomputable def envelope_of_rows_at
    (topFloor credit : Nat) (topHist lowerHist : List (Nat × Nat)) (topDen lowerDen : Nat)
    (one two three : Array Nat) (initial : Nat)
    (htopDen : 0 < topDen) (hlowerDen : 0 < lowerDen)
    (htopHist : ∀ e ∈ topHist, e.1 < 220)
    (hlowerHist : ∀ e ∈ lowerHist, e.1 < 128)
    (htopBound : ∀ answer dl, decoder 0 topFloor answer = some dl → dcredit 0 dl < 220)
    (hlowerBound : ∀ (lay : Layer), lay ≠ 0 → ∀ floor answer dl,
      decoder lay floor answer = some dl → dcredit lay dl < 128)
    (htopLaw : ∀ i : Fin 220,
      Pr[fun answer => ∃ dl, decoder 0 topFloor answer = some dl ∧ dcredit 0 dl = i.val |
        ($ᵗ HashOutput : ProbComp HashOutput)] =
        if topFloor ≤ i.val then (histogramWeight topHist i.val : ENNReal)/topDen else 0)
    (hlowerLaw : ∀ (lay : Layer), lay ≠ 0 → ∀ floor (i : Fin 128),
      Pr[fun answer => ∃ dl, decoder lay floor answer = some dl ∧ dcredit lay dl = i.val |
        ($ᵗ HashOutput : ProbComp HashOutput)] =
        if floor ≤ i.val then (histogramWeight lowerHist i.val : ENNReal)/lowerDen else 0)
    (hinitial : recurrenceCheck topDen topHist topFloor credit one initial = true)
    (hone : ∀ r, r < 56 → recurrenceCheck lowerDen lowerHist (threshold 1 r) r two
      (one[r]?.getD 0) = true)
    (htwo : ∀ r, r < 41 → recurrenceCheck lowerDen lowerHist (threshold 2 r) r three
      (two[r]?.getD 0) = true)
    (hthree : ∀ r, r < 22 → recurrenceCheck lowerDen lowerHist (threshold 3 r) r #[scale]
      (three[r]?.getD 0) = true) : SearchEnvelopeAt ((zNum : ENNReal)/zDen) topFloor credit := by
  have h0 := decoder_recurrence 220 (decoder 0 topFloor) (dcredit 0) topHist topFloor credit topDen one initial
    htopDen htopBound htopHist htopLaw hinitial
  have h1 (r : Nat) (hr : r < 56) := decoder_recurrence 128 (decoder 1 (threshold 1 r))
    (dcredit 1) lowerHist (threshold 1 r) r lowerDen two (one[r]?.getD 0) hlowerDen
    (hlowerBound 1 (by decide) _) hlowerHist (hlowerLaw 1 (by decide) _) (hone r hr)
  have h2 (r : Nat) (hr : r < 41) := decoder_recurrence 128 (decoder 2 (threshold 2 r))
    (dcredit 2) lowerHist (threshold 2 r) r lowerDen three (two[r]?.getD 0) hlowerDen
    (hlowerBound 2 (by decide) _) hlowerHist (hlowerLaw 2 (by decide) _) (htwo r hr)
  have h3 (r : Nat) (hr : r < 22) := decoder_recurrence 128 (decoder 3 (threshold 3 r))
    (dcredit 3) lowerHist (threshold 3 r) r lowerDen #[scale] (three[r]?.getD 0) hlowerDen
    (hlowerBound 3 (by decide) _) hlowerHist (hlowerLaw 3 (by decide) _) (hthree r hr)
  refine ⟨(initial : ENNReal)/scale,
    (fun r => (one[r]?.getD 0 : ENNReal)/scale),
    (fun r => (two[r]?.getD 0 : ENNReal)/scale),
    (fun r => (three[r]?.getD 0 : ENNReal)/scale),
    h0.1, (fun r hr => (h1 r hr).1), (fun r hr => (h2 r hr).1),
    (fun r hr => (h3 r hr).1), h0.2, (fun r hr => (h1 r hr).2),
    (fun r hr => (h2 r hr).2), ?_⟩
  intro r hr
  have hweight : acceptedWeight (decoder 3 (threshold 3 r))
      (fun dl => (#[scale][r-dcredit 3 dl]?.getD 0 : ENNReal)/scale) =
      acceptedWeight (decoder 3 (threshold 3 r)) (fun _ => 1) := by
    apply acceptedWeight_congr_on
    intro answer dl hd
    have hf := decoder_credit hd
    rw [lower_three_progress r hr] at hf
    rw [Nat.sub_eq_zero_of_le hf]
    change (scale : ENNReal)/scale = 1
    exact ENNReal.div_self (by norm_num [scale]) (by finiteness)
  have h := (h3 r hr).2
  rw [hweight] at h
  exact h

noncomputable def envelope_of_rows
    (topHist lowerHist : List (Nat × Nat)) (topDen lowerDen : Nat)
    (one two three : Array Nat) (initial : Nat)
    (htopDen : 0 < topDen) (hlowerDen : 0 < lowerDen)
    (htopHist : ∀ e ∈ topHist, e.1 < 220)
    (hlowerHist : ∀ e ∈ lowerHist, e.1 < 128)
    (htopBound : ∀ answer dl, decoder 0 14 answer = some dl → dcredit 0 dl < 220)
    (hlowerBound : ∀ (lay : Layer), lay ≠ 0 → ∀ floor answer dl,
      decoder lay floor answer = some dl → dcredit lay dl < 128)
    (htopLaw : ∀ i : Fin 220,
      Pr[fun answer => ∃ dl, decoder 0 14 answer = some dl ∧ dcredit 0 dl = i.val |
        ($ᵗ HashOutput : ProbComp HashOutput)] =
        if 14 ≤ i.val then (histogramWeight topHist i.val : ENNReal)/topDen else 0)
    (hlowerLaw : ∀ (lay : Layer), lay ≠ 0 → ∀ floor (i : Fin 128),
      Pr[fun answer => ∃ dl, decoder lay floor answer = some dl ∧ dcredit lay dl = i.val |
        ($ᵗ HashOutput : ProbComp HashOutput)] =
        if floor ≤ i.val then (histogramWeight lowerHist i.val : ENNReal)/lowerDen else 0)
    (hinitial : recurrenceCheck topDen topHist 14 69 one initial = true)
    (hone : ∀ r, r < 56 → recurrenceCheck lowerDen lowerHist (threshold 1 r) r two
      (one[r]?.getD 0) = true)
    (htwo : ∀ r, r < 41 → recurrenceCheck lowerDen lowerHist (threshold 2 r) r three
      (two[r]?.getD 0) = true)
    (hthree : ∀ r, r < 22 → recurrenceCheck lowerDen lowerHist (threshold 3 r) r #[scale]
      (three[r]?.getD 0) = true) : SearchEnvelope ((zNum : ENNReal)/zDen) :=
  envelope_of_rows_at 14 69 topHist lowerHist topDen lowerDen one two three initial
    htopDen hlowerDen htopHist hlowerHist htopBound hlowerBound htopLaw hlowerLaw
    hinitial hone htwo hthree

end ClaudeWCT.W9.T3.CanonicalSearch

namespace ClaudeWCT.W9.T3.CanonicalSearch
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
open ClaudeWCT.Numerics.CanonicalCompression
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

noncomputable def SearchEnvelopeAt.mono_z {z z' : ENNReal} {topFloor credit : Nat}
    (E : SearchEnvelopeAt z topFloor credit) (hz : z' ≤ z) :
    SearchEnvelopeAt z' topFloor credit where
  initial := E.initial
  one := E.one
  two := E.two
  three := E.three
  initial_ge := E.initial_ge
  one_ge := E.one_ge
  two_ge := E.two_ge
  three_ge := E.three_ge
  initial_step := (mul_le_mul' hz le_rfl).trans E.initial_step
  one_step r hr := (mul_le_mul' hz le_rfl).trans (E.one_step r hr)
  two_step r hr := (mul_le_mul' hz le_rfl).trans (E.two_step r hr)
  three_step r hr := (mul_le_mul' hz le_rfl).trans (E.three_step r hr)

noncomputable def SearchEnvelope.mono_z {z z' : ENNReal}
    (E : SearchEnvelope z) (hz : z' ≤ z) : SearchEnvelope z' :=
  SearchEnvelopeAt.mono_z E hz

theorem signing_z_ratio : SigGolfCandidate.T3.Budgets.signingZ ≤ (zNum : ENNReal)/zDen := by
  refine SigGolfCandidate.T3.Budgets.signing_z_le.trans ?_
  apply (ENNReal.toReal_le_toReal (by finiteness) (by unfold zDen; finiteness)).mp
  rw [ENNReal.toReal_ofReal (by norm_num [SigGolfCandidate.T3.BaseAudit.zU]),
    ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  norm_num [SigGolfCandidate.T3.BaseAudit.zU, zNum, zDen]

end ClaudeWCT.W9.T3.CanonicalSearch

namespace ClaudeWCT.W9.T3.CanonicalSearch
open OracleComp OracleSpec OracleComp.EvalDist ENNReal Finset
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
open SphincsSecurity.Completeness ClaudeWCT.WCT9
open ClaudeWCT.W9.T3.ProducerV5.Canonical
open ClaudeWCT.Numerics ClaudeWCT.Numerics.CanonicalCompression
open ClaudeWCT.Numerics.CanonicalHistogram
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem checkRows_at (stage : Nat) (row next : Array Nat) (h : checkRows stage row next = true)
    (r : Nat) (hr : r < row.size) :
    recurrenceCheck lowerDen lowerHistogram (CanonicalPolicy.threshold stage r) r next
      (row[r]?.getD 0) = true := by
  simp only [checkRows, List.all_eq_true] at h
  have he := h r (List.mem_range.mpr hr)
  simpa only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, show (default : Nat) = 0 from rfl] using he

noncomputable def certifiedEnvelope : SearchEnvelope ((zNum : ENNReal)/zDen) :=
  envelope_of_rows ClaudeWCT.Numerics.TopZero.topAcceptedHistogram lowerHistogram topDen lowerDen rowOne rowTwo rowThree ClaudeWCT.Numerics.TopZero.initialBound
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (fun a dl hd => top_decoder_credit_lt (by norm_num) hd)
    (fun lay hl floor a dl hd => lower_decoder_credit_lt lay hl hd)
    selected_top_probability selected_lower_probability
    ClaudeWCT.Numerics.TopZero.initial_checked
    (fun r hr => checkRows_at 1 rowOne rowTwo row_one_checked r (by exact hr))
    (fun r hr => checkRows_at 2 rowTwo rowThree row_two_checked r (by exact hr))
    (fun r hr => checkRows_at 3 rowThree #[scale] row_three_checked r (by exact hr))

theorem certifiedEnvelope_initial : certifiedEnvelope.initial = (ClaudeWCT.Numerics.TopZero.initialBound : ENNReal)/scale := rfl

theorem V_searchPreparedLayers_certified (secret : BitVec 256) (cache : SigGolfCandidate.T3.Cache)
    (index : Nat) (prepared : SigGolfCandidate.Research.SharedForest.PreparedRoots)
    (forest : SigGolfCandidate.Research.SharedForest.PairRoot) (rcache : RCache)
    (hfresh : RowsFreshFrom 0 rcache) :
    V secret SigGolfCandidate.T3.Budgets.signingZ
      (SigGolfCandidate.Research.SharedForest.searchPreparedLayers cache index prepared forest) rcache ≤
      SigGolfCandidate.T3.Budgets.signingZ^180 * ((ClaudeWCT.Numerics.TopZero.initialBound : ENNReal)/scale) := by
  have h := V_searchPreparedLayers secret SigGolfCandidate.T3.Budgets.signingZ
    (SigGolfCandidate.Budget.one_le_zOf _)
    (certifiedEnvelope.mono_z signing_z_ratio)
    cache index prepared forest rcache hfresh
  exact h

/-- A certified envelope for each of the five digest-cost tiers. -/
noncomputable def certifiedTierEnvelope (extra : Nat) (he : extra ≤ 4) :
    SearchEnvelopeAt ((zNum : ENNReal)/zDen) (14 + extra) (69 + extra) :=
  envelope_of_rows_at (14 + extra) (69 + extra)
    ClaudeWCT.Numerics.TopZero.topAcceptedHistogram lowerHistogram topDen lowerDen
    rowOne rowTwo rowThree (ClaudeWCT.Numerics.TopZero.tierInitialBound extra)
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (fun a dl hd => top_decoder_credit_lt (by omega) hd)
    (fun lay hl floor a dl hd => lower_decoder_credit_lt lay hl hd)
    (selected_top_probability_at (14 + extra) (by omega)) selected_lower_probability
    (ClaudeWCT.Numerics.TopZero.tier_initial_checked extra he)
    (fun r hr => checkRows_at 1 rowOne rowTwo row_one_checked r (by exact hr))
    (fun r hr => checkRows_at 2 rowTwo rowThree row_two_checked r (by exact hr))
    (fun r hr => checkRows_at 3 rowThree #[scale] row_three_checked r (by exact hr))

theorem certifiedTierEnvelope_initial (extra : Nat) (he : extra ≤ 4) :
    (certifiedTierEnvelope extra he).initial =
      (ClaudeWCT.Numerics.TopZero.tierInitialBound extra : ENNReal)/scale := rfl

theorem V_searchPreparedLayers_certified_tier (secret : BitVec 256)
    (cache : SigGolfCandidate.T3.Cache) (index extra : Nat) (he : extra ≤ 4)
    (prepared : SigGolfCandidate.Research.SharedForest.PreparedRoots)
    (forest : SigGolfCandidate.Research.SharedForest.PairRoot) (rcache : RCache)
    (hfresh : RowsFreshFrom 0 rcache) :
    V secret SigGolfCandidate.T3.Budgets.signingZ
      (SigGolfCandidate.Research.SharedForest.searchPreparedLayers cache index prepared forest
        (69 + extra) (14 + extra)) rcache ≤
      SigGolfCandidate.T3.Budgets.signingZ^180 *
        ((ClaudeWCT.Numerics.TopZero.tierInitialBound extra : ENNReal)/scale) := by
  have h := V_searchPreparedLayers_at secret SigGolfCandidate.T3.Budgets.signingZ
    (SigGolfCandidate.Budget.one_le_zOf _) (14 + extra) (69 + extra) (by omega)
    ((certifiedTierEnvelope extra he).mono_z signing_z_ratio)
    cache index prepared forest rcache hfresh
  simpa only [certifiedTierEnvelope_initial] using h

/-- Uniform digest outputs are partitioned by their field-word cost prefix.
The field-count theorem supplies the polynomial cardinality, while the
numeric packet checks its five values. -/
def digestPrefixSet (extra : Nat) : Finset HashOutput :=
  Finset.univ.filter (fun a =>
    SigGolfCandidate.Research.SharedFtsModel.validUpTo (98 + extra)
      (SigGolfCandidate.Research.SharedDigestFields.fields a))

theorem mem_digestPrefixSet (extra : Nat) (a : HashOutput) :
    a ∈ digestPrefixSet extra ↔
      (SigGolfCandidate.Research.SharedDigestFields.fields a).2.2.2.toNat < 791 ∧
      (∀ k, ((SigGolfCandidate.Research.SharedDigestFields.fields a).2.1 k).toNat < 563) ∧
      SigGolfCandidate.Research.SharedForest.jointAccountingCost a ≤ 773 + extra := by
  simp only [digestPrefixSet, Finset.mem_filter, Finset.mem_univ, true_and,
    SigGolfCandidate.Research.SharedFtsModel.validUpTo,
    SigGolfCandidate.Research.SharedDigestFields.cost_fields]
  have he : 675 + (98 + extra) = 773 + extra := by omega
  rw [he]

theorem digestAccepted_iff_cost (a : HashOutput) :
    SigGolfCandidate.Research.SharedForest.digestAccepted a = true ↔
      (SigGolfCandidate.Research.SharedDigestFields.fields a).2.2.2.toNat < 791 ∧
      (∀ k, ((SigGolfCandidate.Research.SharedDigestFields.fields a).2.1 k).toNat < 563) ∧
      SigGolfCandidate.Research.SharedForest.jointAccountingCost a ≤ 777 := by
  rw [← SigGolfCandidate.Research.SharedDigestFields.accepted_fields a]
  simpa only [SigGolfCandidate.Research.SharedDigestFields.cost_fields] using
    SigGolfCandidate.Research.SharedFtsModel.accepted_iff
      (SigGolfCandidate.Research.SharedDigestFields.fields a)

theorem digestPrefixSet_mono {i j : Nat} (hij : i ≤ j) :
    digestPrefixSet i ⊆ digestPrefixSet j := by
  intro a ha
  simp only [digestPrefixSet, Finset.mem_filter, Finset.mem_univ, true_and,
    SigGolfCandidate.Research.SharedFtsModel.validUpTo] at ha ⊢
  rcases ha with ⟨hg, hr, hc⟩
  exact ⟨hg, hr, by omega⟩

theorem digestPrefixSet_card (extra : Nat) (he : extra ≤ 4) :
    (digestPrefixSet extra).card =
      ClaudeWCT.Numerics.TopZero.tierFieldPrefix extra * 2^31 * 791 * 2^76 := by
  classical
  have hcap : SigGolfCandidate.Research.SharedFtsModel.fieldCappedCount (98 + extra) =
      ClaudeWCT.Numerics.TopZero.tierFieldPrefix extra := by
    unfold SigGolfCandidate.Research.SharedFtsModel.fieldCappedCount
    have hindex : 98 + extra + 1 = 99 + extra := by omega
    rw [hindex]
    exact ClaudeWCT.Numerics.TopZero.tier_field_prefix_checked extra he
  unfold digestPrefixSet
  rw [← Fintype.card_subtype]
  rw [SigGolfCandidate.Research.SharedDigestFields.predicate_card]
  rw [SigGolfCandidate.Research.SharedFtsModel.tier_fields_card]
  rw [hcap]

def digestTierSet (extra : Nat) : Finset HashOutput :=
  if extra = 0 then digestPrefixSet 0
  else digestPrefixSet extra \ digestPrefixSet (extra - 1)

theorem digestTierSet_card (extra : Nat) (he : extra ≤ 4) :
    (digestTierSet extra).card =
      ClaudeWCT.Numerics.TopZero.tierFieldCount extra * 2^31 * 791 * 2^76 := by
  classical
  by_cases hzero : extra = 0
  · subst extra
    simp only [digestTierSet, ↓reduceIte, digestPrefixSet_card 0 (by decide)]
    rfl
  · have hsub : digestPrefixSet (extra - 1) ⊆ digestPrefixSet extra :=
      digestPrefixSet_mono (by omega)
    have hpos : 1 ≤ extra := by omega
    rw [digestTierSet, if_neg hzero, Finset.card_sdiff_of_subset hsub,
      digestPrefixSet_card extra he,
      digestPrefixSet_card (extra - 1) (by omega)]
    interval_cases extra <;> decide

theorem mem_digestTierSet (extra : Nat) (he : extra ≤ 4) (a : HashOutput) :
    a ∈ digestTierSet extra ↔
      SigGolfCandidate.Research.SharedForest.digestAccepted a = true ∧
      SigGolfCandidate.Research.SharedForest.conditionalExtra a = extra := by
  have hacc := digestAccepted_iff_cost a
  have hp (k : Nat) := mem_digestPrefixSet k a
  by_cases hzero : extra = 0
  · subst extra
    rw [digestTierSet, if_pos rfl, hp 0, hacc]
    simp only [SigGolfCandidate.Research.SharedForest.conditionalExtra]
    constructor
    · rintro ⟨hg, hr, hc⟩
      exact ⟨⟨hg, hr, by omega⟩, by omega⟩
    · rintro ⟨⟨hg, hr, _⟩, hc⟩
      exact ⟨hg, hr, by omega⟩
  · rw [digestTierSet, if_neg hzero, Finset.mem_sdiff, hp extra, hp (extra - 1), hacc]
    simp only [SigGolfCandidate.Research.SharedForest.conditionalExtra]
    constructor
    · rintro ⟨⟨hg, hr, hc⟩, hn⟩
      have hlow : 773 + (extra - 1) <
          SigGolfCandidate.Research.SharedForest.jointAccountingCost a := by
        by_contra hnot
        exact hn ⟨hg, hr, by omega⟩
      exact ⟨⟨hg, hr, by omega⟩, by omega⟩
    · rintro ⟨⟨hg, hr, _⟩, hc⟩
      refine ⟨⟨hg, hr, by omega⟩, ?_⟩
      rintro ⟨_, _, hprev⟩
      omega

theorem digestTierSet_probability (extra : Nat) (he : extra ≤ 4) :
    Pr[fun a : HashOutput => a ∈ digestTierSet extra |
      ($ᵗ HashOutput : ProbComp HashOutput)] =
      ((ClaudeWCT.Numerics.TopZero.tierFieldCount extra * 2^31 * 791 * 2^76 : Nat) : ENNReal) /
        (2^256 : Nat) := by
  classical
  rw [probEvent_uniformSample]
  have hs : (Finset.univ.filter fun a : HashOutput => a ∈ digestTierSet extra) =
      digestTierSet extra := by ext a; simp
  rw [hs, digestTierSet_card extra he]
  simp only [Fintype.card_bitVec]

def digestTierLabel (a : HashOutput) : Fin 5 :=
  ⟨min (SigGolfCandidate.Research.SharedForest.conditionalExtra a) 4, by omega⟩

theorem digest_label_event (i : Fin 5) (a : HashOutput) :
    (∃ value, DigestGeneric.decoder SigGolfCandidate.Research.SharedForest.digestAccepted a = some value ∧
      digestTierLabel value = i) ↔ a ∈ digestTierSet i.val := by
  rw [mem_digestTierSet i.val (by omega) a]
  constructor
  · rintro ⟨value, hd, hl⟩
    by_cases ha : SigGolfCandidate.Research.SharedForest.digestAccepted a = true
    · simp [DigestGeneric.decoder, ha] at hd
      subst value
      have he := (SigGolfCandidate.Research.SharedForest.conditional_bounds_of_accepted a ha).1
      exact ⟨ha, by have hi := Fin.ext_iff.mp hl; dsimp [digestTierLabel] at hi; omega⟩
    · simp [DigestGeneric.decoder, ha] at hd
  · rintro ⟨ha, he⟩
    refine ⟨a, by simp [DigestGeneric.decoder, ha], ?_⟩
    apply Fin.ext
    dsimp [digestTierLabel]
    omega

/-- The accepted digest trial has exactly five cost-dependent continuation
weights. -/
theorem digest_acceptedWeight_tiers :
    acceptedWeight
      (DigestGeneric.decoder SigGolfCandidate.Research.SharedForest.digestAccepted)
      (fun a => (ClaudeWCT.Numerics.TopZero.tierInitialBound
        (SigGolfCandidate.Research.SharedForest.conditionalExtra a) : ENNReal) / scale) =
      ∑ i : Fin 5,
        (((ClaudeWCT.Numerics.TopZero.tierFieldCount i.val * 2^31 * 791 * 2^76 : Nat) : ENNReal) /
          (2^256 : Nat)) *
        ((ClaudeWCT.Numerics.TopZero.tierInitialBound i.val : ENNReal) / scale) := by
  let dec := DigestGeneric.decoder SigGolfCandidate.Research.SharedForest.digestAccepted
  let wt : Fin 5 → ENNReal := fun i =>
    (ClaudeWCT.Numerics.TopZero.tierInitialBound i.val : ENNReal) / scale
  have hcongr : acceptedWeight dec (fun a =>
      (ClaudeWCT.Numerics.TopZero.tierInitialBound
        (SigGolfCandidate.Research.SharedForest.conditionalExtra a) : ENNReal) / scale) =
      acceptedWeight dec (fun a => wt (digestTierLabel a)) := by
    apply acceptedWeight_congr_on
    intro answer value hd
    have ha : SigGolfCandidate.Research.SharedForest.digestAccepted answer = true := by
      by_cases h : SigGolfCandidate.Research.SharedForest.digestAccepted answer = true
      · exact h
      · simp [dec, DigestGeneric.decoder, h] at hd
    simp [dec, DigestGeneric.decoder, ha] at hd
    subst value
    have he := (SigGolfCandidate.Research.SharedForest.conditional_bounds_of_accepted answer ha).1
    congr 1
    dsimp [wt, digestTierLabel]
    congr 1
    omega
  rw [hcongr, acceptedWeight_labels dec digestTierLabel wt]
  apply Finset.sum_congr rfl
  intro i _
  have he : (fun a : HashOutput => ∃ value, dec a = some value ∧ digestTierLabel value = i) =
      (fun a : HashOutput => a ∈ digestTierSet i.val) := by
    funext a
    apply propext
    exact digest_label_event i a
  rw [he, digestTierSet_probability i.val (by omega)]
  rfl

theorem digest_acceptedWeight_le_mixed :
    acceptedWeight
      (DigestGeneric.decoder SigGolfCandidate.Research.SharedForest.digestAccepted)
      (fun a => (ClaudeWCT.Numerics.TopZero.tierInitialBound
        (SigGolfCandidate.Research.SharedForest.conditionalExtra a) : ENNReal) / scale) ≤
      ((ftsNum : ENNReal) / ftsDen) *
        ((ClaudeWCT.Numerics.TopZero.mixedInitialBound : ENNReal) / scale) := by
  rw [digest_acceptedWeight_tiers]
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [Fin.sum_univ_succ, ClaudeWCT.Numerics.TopZero.tierFieldCount,
    ClaudeWCT.Numerics.TopZero.tierInitialBound,
    ClaudeWCT.Numerics.TopZero.mixedInitialBound, ftsNum, ftsDen, scale,
    ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div]

noncomputable def tierDigestMoment : ENNReal :=
  ((ftsBound : ENNReal) / scale) *
    ((ClaudeWCT.Numerics.TopZero.mixedInitialBound : ENNReal) / scale)

theorem tierDigestMoment_ge_one : 1 ≤ tierDigestMoment := by
  apply one_le_mul
  · apply (ENNReal.toReal_le_toReal (by simp) (by finiteness)).mp
    norm_num [ftsBound, scale, ENNReal.toReal_div]
  · apply (ENNReal.toReal_le_toReal (by simp) (by finiteness)).mp
    norm_num [ClaudeWCT.Numerics.TopZero.mixedInitialBound, scale, ENNReal.toReal_div]

/-- The weighted digest continuation satisfies the same geometric-search
recurrence as the old uniform bound. -/
theorem tier_digest_moment_step :
    SigGolfCandidate.T3.Budgets.signingZ *
      (acceptedWeight
        (DigestGeneric.decoder SigGolfCandidate.Research.SharedForest.digestAccepted)
        (fun a => (ClaudeWCT.Numerics.TopZero.tierInitialBound
          (SigGolfCandidate.Research.SharedForest.conditionalExtra a) : ENNReal) / scale) +
        SphincsSecurity.Completeness.failMass
          (DigestGeneric.decoder SigGolfCandidate.Research.SharedForest.digestAccepted) *
          tierDigestMoment) ≤ tierDigestMoment := by
  let p : ENNReal := (ftsNum : ENNReal) / ftsDen
  let d : ENNReal := (ftsBound : ENNReal) / scale
  let m : ENNReal := (ClaudeWCT.Numerics.TopZero.mixedInitialBound : ENNReal) / scale
  have hp : p ≤ 1 := by
    apply (ENNReal.div_le_iff (by norm_num [ftsDen]) (by finiteness)).mpr
    norm_num [p, ftsNum, ftsDen]
  have hdouble : 1 - (1 - p) = p := ENNReal.sub_sub_cancel (by simp) hp
  have hfail : SphincsSecurity.Completeness.failMass
      (DigestGeneric.decoder SigGolfCandidate.Research.SharedForest.digestAccepted) = 1 - p := by
    rw [SigGolfCandidate.T3.Budgets.failMass_eq_one_sub_accept,
      DigestGeneric.decoder_acceptance,
      ClaudeWCT.Bank.Paired.digestAccepted_acceptance_exact]
    rfl
  rw [hfail]
  change SigGolfCandidate.T3.Budgets.signingZ *
    (acceptedWeight
      (DigestGeneric.decoder SigGolfCandidate.Research.SharedForest.digestAccepted)
      (fun a => (ClaudeWCT.Numerics.TopZero.tierInitialBound
        (SigGolfCandidate.Research.SharedForest.conditionalExtra a) : ENNReal) / scale) +
      (1 - p) * (d * m)) ≤ d * m
  calc
    _ ≤ ((zNum : ENNReal) / zDen) * (p * m + (1 - p) * (d * m)) :=
      mul_le_mul' signing_z_ratio (add_le_add digest_acceptedWeight_le_mixed le_rfl)
    _ = m * (((zNum : ENNReal) / zDen) * ((1 - p) * d + (1 - (1 - p)))) := by
      rw [hdouble]
      ring
    _ ≤ m * d := mul_le_mul' le_rfl fts_ratio_step
    _ = d * m := mul_comm _ _

theorem V_digestRun_bind_tier {δ : Type} (secret : BitVec 256)
    (rho : Digest) (message : Message)
    (next : Option (BitVec 32 × HashOutput) → M δ)
    (hnone : ∀ rc, RowsFreshFrom 0 rc →
      V secret SigGolfCandidate.T3.Budgets.signingZ (next none) rc ≤ tierDigestMoment)
    (hsome : ∀ rc, RowsFreshFrom 0 rc → ∀ c, c < 2^32 → ∀ answer,
      SigGolfCandidate.Research.SharedForest.digestAccepted answer = true →
      V secret SigGolfCandidate.T3.Budgets.signingZ
        (next (some (BitVec.ofNat 32 c, answer)))
        (rc.cacheQuery (digestTrial rho message c) answer) ≤
        ((ClaudeWCT.Numerics.TopZero.tierInitialBound
          (SigGolfCandidate.Research.SharedForest.conditionalExtra answer) : ENNReal) / scale))
    (fuel counter : Nat) (hlimit : counter + fuel ≤ 2^32) (cache : RCache)
    (hrows : RowsFreshFrom 0 cache)
    (hfresh : ∀ c, counter ≤ c → c < 2^32 → cache (digestTrial rho message c) = none) :
    V secret SigGolfCandidate.T3.Budgets.signingZ
      (DigestGeneric.run SigGolfCandidate.Research.SharedForest.digestAccepted
        rho message counter fuel >>= next) cache ≤ tierDigestMoment := by
  exact DigestGeneric.V_run_bind SigGolfCandidate.Research.SharedForest.digestAccepted
    secret SigGolfCandidate.T3.Budgets.signingZ tierDigestMoment rho message next
    (fun answer => (ClaudeWCT.Numerics.TopZero.tierInitialBound
      (SigGolfCandidate.Research.SharedForest.conditionalExtra answer) : ENNReal) / scale)
    hnone hsome tier_digest_moment_step fuel counter hlimit cache hrows hfresh

end ClaudeWCT.W9.T3.CanonicalSearch

namespace ClaudeWCT.W9.T3.CanonicalSearch
open OracleComp OracleSpec OracleComp.EvalDist ENNReal Finset
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
open SphincsSecurity.Completeness ClaudeWCT.WCT9
open ClaudeWCT.W9.T3.ProducerV5.Canonical
open ClaudeWCT.Numerics ClaudeWCT.Numerics.CanonicalCompression
open ClaudeWCT.Numerics.CanonicalHistogram
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

theorem top_acceptance_at (floor : Nat) (hf : 14 ≤ floor) :
    Pr[fun a => (decoder 0 floor a).isSome | ($ᵗ HashOutput : ProbComp HashOutput)] =
      (acceptedMass ClaudeWCT.Numerics.TopZero.topAcceptedHistogram floor : ENNReal)/topDen := by
  rw [← acceptedWeight_one_probability]
  exact acceptedWeight_acceptedMass 220 (decoder 0 floor) (dcredit 0)
    ClaudeWCT.Numerics.TopZero.topAcceptedHistogram floor topDen
    (fun a dl hd => top_decoder_credit_lt (by norm_num) hd) (by decide +kernel)
    (selected_top_probability_at floor hf)

theorem top_acceptance :
    Pr[fun a => (decoder 0 14 a).isSome | ($ᵗ HashOutput : ProbComp HashOutput)] =
      (acceptedMass ClaudeWCT.Numerics.TopZero.topAcceptedHistogram 14 : ENNReal)/topDen :=
  top_acceptance_at 14 (by norm_num)

theorem lower_acceptance (lay : Layer) (hl : lay≠0) (floor : Nat) :
    Pr[fun a => (decoder lay floor a).isSome | ($ᵗ HashOutput : ProbComp HashOutput)] =
      (acceptedMass lowerHistogram floor : ENNReal)/lowerDen := by
  rw [← acceptedWeight_one_probability]
  exact acceptedWeight_acceptedMass 128 (decoder lay floor) (dcredit lay)
    lowerHistogram floor lowerDen
    (fun a dl hd => lower_decoder_credit_lt lay hl hd) (by decide +kernel)
    (selected_lower_probability lay hl floor)

theorem ofReal_nat_ratio (n d : Nat) (hd : 0<d) :
    ENNReal.ofReal (((n : ℚ)/d : ℚ) : ℝ) = (n : ENNReal)/d := by
  push_cast
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hd), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]

def topFailureRate : ℚ := (acceptedMass ClaudeWCT.Numerics.TopZero.topAcceptedHistogram 14 : ℚ)/topDen
def topFailureRate18 : ℚ := (acceptedMass ClaudeWCT.Numerics.TopZero.topAcceptedHistogram 18 : ℚ)/topDen
def lowerFailureRate : ℚ := (acceptedMass lowerHistogram 19 : ℚ)/lowerDen
/-- L3 (img-v6 floors up to 21, window `3·2^20`). -/
def lowerThreeFailureRate : ℚ := (acceptedMass lowerHistogram 21 : ℚ)/lowerDen

/-- The top counter window is the single parameter `topSearchLimit` (0x10c000). -/
theorem top_failure_rate_440_checked : 0≤topFailureRate ∧ topFailureRate≤1 ∧
    (440 : ℚ)*0.6931471808≤(topSearchLimit : ℚ)*topFailureRate := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  simp only [topSearchLimit, Nat.cast_pow, Nat.cast_ofNat]
  decide +kernel

theorem top_failure_rate_435_checked : 0≤topFailureRate18 ∧ topFailureRate18≤1 ∧
    (435 : ℚ)*0.6931471808≤(topSearchLimit : ℚ)*topFailureRate18 := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  simp only [topSearchLimit, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  decide +kernel

theorem lower_failure_rate_440_checked : 0≤lowerFailureRate ∧ lowerFailureRate≤1 ∧
    (440 : ℚ)*0.6931471808≤2^21*lowerFailureRate := by decide +kernel

theorem lower_three_failure_rate_440_checked : 0≤lowerThreeFailureRate ∧ lowerThreeFailureRate≤1 ∧
    (440 : ℚ)*0.6931471808≤(3*2^20)*lowerThreeFailureRate := by decide +kernel

/-- The floor-14 tail under the current top search window. -/
theorem top_failure_power_440 : failMass (decoder 0 14)^topSearchLimit≤1/(2:ENNReal)^440 := by
  apply ClaudeWCT.W9.T3.Budgets.V5.failure_power_of_rate _ topFailureRate
    topSearchLimit 440 top_failure_rate_440_checked.1 top_failure_rate_440_checked.2.1 _ top_failure_rate_440_checked.2.2
  rw [top_acceptance, topFailureRate, ofReal_nat_ratio _ _ (by decide)]

theorem top_failure_power_435_at (floor : Nat) (hlo : 14 ≤ floor) (hhi : floor ≤ 18) :
    failMass (decoder 0 floor)^topSearchLimit≤1/(2:ENNReal)^435 := by
  apply ClaudeWCT.W9.T3.Budgets.V5.failure_power_of_rate _ topFailureRate18
    topSearchLimit 435 top_failure_rate_435_checked.1 top_failure_rate_435_checked.2.1 _
    top_failure_rate_435_checked.2.2
  rw [top_acceptance_at floor hlo, topFailureRate18, ofReal_nat_ratio _ _ (by decide)]
  gcongr
  exact_mod_cast acceptedMass_antitone ClaudeWCT.Numerics.TopZero.topAcceptedHistogram hhi

theorem lower_failure_power_440 (lay : Layer) (hl : lay≠0) (floor : Nat) (hf : floor≤19) :
    failMass (decoder lay floor)^(2^21)≤1/(2:ENNReal)^440 := by
  apply ClaudeWCT.W9.T3.Budgets.V5.failure_power_of_rate _ lowerFailureRate
    (2^21) 440 lower_failure_rate_440_checked.1 lower_failure_rate_440_checked.2.1 _ lower_failure_rate_440_checked.2.2
  rw [lower_acceptance lay hl floor, lowerFailureRate, ofReal_nat_ratio _ _ (by decide)]
  gcongr
  exact_mod_cast acceptedMass_antitone lowerHistogram hf

/-- L3: floors up to 21 within the `3·2^20` window. -/
theorem lower_three_failure_power_440 (floor : Nat) (hf : floor≤21) :
    failMass (decoder 3 floor)^(3*2^20)≤1/(2:ENNReal)^440 := by
  apply ClaudeWCT.W9.T3.Budgets.V5.failure_power_of_rate _ lowerThreeFailureRate
    (3*2^20) 440 lower_three_failure_rate_440_checked.1 lower_three_failure_rate_440_checked.2.1 _
    (by exact_mod_cast lower_three_failure_rate_440_checked.2.2)
  rw [lower_acceptance 3 (by decide) floor, lowerThreeFailureRate, ofReal_nat_ratio _ _ (by decide)]
  gcongr
  exact_mod_cast acceptedMass_antitone lowerHistogram hf

end ClaudeWCT.W9.T3.CanonicalSearch

namespace ClaudeWCT.W9.T3.CanonicalSearch
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.WCT9
open ClaudeWCT.W9.T3.QuerySpace
open SigGolfCandidate.T3.Budgets (zeroAnswers finite_family_failure_le ofReal_inv_two_pow)
open SphincsSecurity.Completeness
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable local instance : SampleableType (SearchKey → HashOutput) := Presampling.tableSampler

/-- A canonical encoding context: the routed family and the floor (top floors 14 through 18; L1/L2
floors are below 20 (clipped at 19), L3 floors below 22). -/
abbrev EncodingContext := EncodingFamilyBC × Fin 22

def contextFloor (context : EncodingContext) : Nat :=
  if context.1.1=0 then 14 + min context.2.val 4
  else if context.1.1=3 then context.2.val else min context.2.val 19

def ContextFailed (context : EncodingContext) (answers : Correctness.Answers) : Prop :=
  evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt context.1.1 (contextFloor context)
    (routedTree context.1.1 context.1.2.1) (routedLeaf context.1.1 context.1.2.1)
    (.pair context.1.2.2.1 context.1.2.2.2) 0 (searchLimit context.1.1))=none

theorem encodingContext_card_le : Fintype.card EncodingContext ≤ 2^301 := by
  change Fintype.card (EncodingFamilyBC × Fin 22) ≤ 2^301
  rw [Fintype.card_prod,encodingFamilyBC_card,Fintype.card_fin]
  exact (Nat.mul_le_mul_left _ (show 22≤2^11 by norm_num)).trans_eq (by rw [←pow_add])

theorem encodingContext_card_le_295 : Fintype.card EncodingContext ≤ 2^295 := by
  change Fintype.card (EncodingFamilyBC × Fin 22) ≤ 2^295
  rw [Fintype.card_prod,encodingFamilyBC_card,Fintype.card_fin]
  exact (Nat.mul_le_mul_left _ (show 22≤2^5 by norm_num)).trans_eq (by rw [←pow_add])

theorem context_table_failure (context : EncodingContext) :
    Pr[fun outputs => ContextFailed context (Presampling.tableAnswers outputs zeroAnswers) |
      ($ᵗ (SearchKey → HashOutput) : ProbComp _)] ≤ 1/(2:ENNReal)^435 := by
  unfold ContextFailed
  rw [Presampling.Canonical.search_table_failure _ (Presampling.searchLimit_le_rows _) ]
  by_cases hl : context.1.1=0
  · simpa only [contextFloor,hl,if_pos,searchLimit_top] using
      (top_failure_power_435_at (14 + min context.2.val 4) (by omega) (by omega))
  · by_cases h3 : context.1.1=3
    · have hf : context.2.val≤21 := by omega
      have hlow := lower_three_failure_power_440 context.2.val hf
      simp only [contextFloor,hl,h3,if_false,if_true]
      have hs : searchLimit (3 : Layer) = 3*2^20 := searchLimit_values.2.2.2
      rw [hs]
      exact hlow.trans (by norm_num)
    · have hf : min context.2.val 19≤19 := Nat.min_le_right _ _
      have hlow := lower_failure_power_440 context.1.1 hl (min context.2.val 19) hf
      simp only [contextFloor,hl,h3,if_false]
      refine le_trans ?_ (hlow.trans (by norm_num))
      have hone : failMass (decoder context.1.1 (min context.2.val 19))≤1 := by
        rw [failMass_eq_probEvent]
        exact probEvent_le_one
      exact pow_le_pow_right_of_le_one' hone
        (by simpa only [lowerSearchLimit] using searchLimit_lower hl)
theorem context_family_failure :
    Pr[fun outputs => ∃ context, ContextFailed context (Presampling.tableAnswers outputs zeroAnswers) |
      ($ᵗ (SearchKey → HashOutput) : ProbComp _)] ≤ (2:ENNReal)^295*(1/(2:ENNReal)^435) := by
  have h := finite_family_failure_le ($ᵗ (SearchKey → HashOutput) : ProbComp _)
    (fun context outputs => ContextFailed context (Presampling.tableAnswers outputs zeroAnswers))
    (1/(2:ENNReal)^435) context_table_failure
  exact h.trans (mul_le_mul' (by exact_mod_cast encodingContext_card_le_295) le_rfl)

theorem completeness_union_arithmetic :
    (2:ENNReal)^256*(1/(2:ENNReal)^400)+(2:ENNReal)^295*(1/(2:ENNReal)^435)
      ≤ 1/(2:ENNReal)^138 := by
  have hr : (2:ℝ)^256*(1/(2:ℝ)^400)+(2:ℝ)^295*(1/(2:ℝ)^435)≤1/(2:ℝ)^138 := by
    set_option exponentiation.threshold 1024 in norm_num
  have h := ENNReal.ofReal_le_ofReal hr
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul (by positivity)] at h
  simpa only [ENNReal.ofReal_pow (show 0≤(2:ℝ) by norm_num),ENNReal.ofReal_ofNat,
    ofReal_inv_two_pow] using h

theorem all_search_failure_small {α ι : Type} [Fintype ι] (law : ProbComp α)
    (digestFailed : ι → α → Prop) (encodingFailed : EncodingContext → α → Prop)
    (hι : Fintype.card ι≤2^256)
    (hd : ∀ i, Pr[digestFailed i | law]≤1/(2:ENNReal)^400)
    (he : ∀ context, Pr[encodingFailed context | law]≤1/(2:ENNReal)^435) :
    Pr[fun value => (∃ i, digestFailed i value) ∨ (∃ context, encodingFailed context value) | law]
      ≤1/(2:ENNReal)^138 := by
  have hd' := finite_family_failure_le law digestFailed _ hd
  have he' := finite_family_failure_le law encodingFailed _ he
  have hι' : (Fintype.card ι:ENNReal)≤2^256 := by exact_mod_cast hι
  have hc' : (Fintype.card EncodingContext:ENNReal)≤2^295 := by exact_mod_cast encodingContext_card_le_295
  exact ((probEvent_or_le law _ _).trans (add_le_add hd' he')).trans
    ((add_le_add (mul_le_mul' hι' le_rfl) (mul_le_mul' hc' le_rfl)).trans completeness_union_arithmetic)

end ClaudeWCT.W9.T3.CanonicalSearch


namespace ClaudeWCT.W9.T3.CanonicalSearch
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open ClaudeWCT.W9.T3.QuerySpace
open SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def ContextGood (answers : Answers) : Prop := ∀ context, ¬ContextFailed context answers

theorem context_good_at_route (answers : Answers) (hgood : ContextGood answers)
    (index : Nat) (hi : index<2^31) (lay : Layer) (floor : Nat)
    (hf : if lay=0 then 14 ≤ floor ∧ floor ≤ 18 else if lay=3 then floor<22 else floor<20)
    (left right : Digest) :
    ∃ found, evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt lay floor
      (route index lay).2 (route index lay).1 (.pair left right) 0 (searchLimit lay))=some found := by
  let routed : Fin (2^32) := ⟨(route index lay).2*2^height lay+(route index lay).1,
    ClaudeWCT.W9.T3.Correctness.route_routed_lt index hi lay⟩
  let context : EncodingContext := ((lay,routed,left,right),⟨if lay=0 then floor-14 else floor,by
    by_cases hl : lay=0
    · have hf' : 14 ≤ floor ∧ floor ≤ 18 := by simpa only [hl, if_true] using hf
      simp only [hl, if_true]
      omega
    · by_cases h3 : lay=3
      · rw [if_neg hl]; rw [if_neg hl, if_pos h3] at hf; exact hf
      · rw [if_neg hl]; rw [if_neg hl, if_neg h3] at hf; omega⟩)
  have hh := hgood context
  have hfloor : contextFloor context=floor := by
    by_cases hl : lay=0
    · have hf' : 14 ≤ floor ∧ floor ≤ 18 := by simpa only [hl,if_true] using hf
      have hmin : min (floor - 14) 4 = floor - 14 := Nat.min_eq_left (by omega)
      dsimp only [contextFloor,context]
      simp only [hl,if_true,hmin]
      omega
    · by_cases h3 : lay=3
      · dsimp only [contextFloor,context]; rw [if_neg hl, if_pos h3, if_neg hl]
      · have : floor<20 := by rw [if_neg hl, if_neg h3] at hf; exact hf
        dsimp only [contextFloor,context]; rw [if_neg hl, if_neg h3, if_neg hl]
        omega
  have ht := routedTree_of lay (tree:=(route index lay).2) (route_leaf_bound index lay)
  have hl := routedLeaf_of lay (tree:=(route index lay).2) (route_leaf_bound index lay)
  unfold ContextFailed at hh
  rw [hfloor] at hh
  simp only [context,routed,ht,hl] at hh
  exact Option.ne_none_iff_exists'.mp hh
end ClaudeWCT.W9.T3.CanonicalSearch

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness ClaudeWCT.W9.T3.CanonicalSearch
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem searchPreparedLayers_complete_at (answers : Answers) (hgood : ContextGood answers)
    (cache : SigGolfCandidate.T3.Cache) (index : Nat) (hi : index<2^31)
    (prepared : PreparedRoots) (forest : PairRoot) (credit topFloor : Nat)
    (hfloor : 14 ≤ topFloor ∧ topFloor ≤ 18) (hcredit : credit = topFloor + 55) :
    ∃ result, evalWithAnswerFn answers
      (searchPreparedLayers cache index prepared forest credit topFloor)=some result := by
  obtain ⟨⟨c0,d0,l0⟩,hs0⟩ := context_good_at_route answers hgood index hi 0 topFloor
    (by simpa only [show (0:Layer)=0 by rfl, if_true] using hfloor)
    (topPair 1 prepared.one.levels).1 (topPair 1 prepared.one.levels).2
  have hd0 := (canonical_search_some' answers 0 topFloor (route index 0).2 (route index 0).1
    (.pair (topPair 1 prepared.one.levels).1 (topPair 1 prepared.one.levels).2)
    (searchLimit 0) 0 c0 d0 l0 (by decide) hs0).2.2.2
  let r1 := CanonicalPolicy.nextResidual credit 0 l0 d0
  have hr1 : r1<56 := by
    have hc := CanonicalPolicy.producerDecodeAt_credit hd0
    dsimp only [r1, CanonicalPolicy.nextResidual]
    omega
  have hf1' : CanonicalPolicy.threshold 1 r1<16 := CanonicalPolicy.lower_one_floor_lt ⟨r1,hr1⟩
  have hf1 : CanonicalPolicy.threshold 1 r1<20 := by omega
  obtain ⟨⟨c1,d1,l1⟩,hs1⟩ := context_good_at_route answers hgood index hi 1
    (CanonicalPolicy.threshold 1 r1) (by simpa only [show (1:Layer)≠0 by decide, show (1:Layer)≠3 by decide, if_false] using hf1)
    (topPair 2 prepared.two.levels).1 (topPair 2 prepared.two.levels).2
  have hd1 := (canonical_search_some' answers 1 (CanonicalPolicy.threshold 1 r1)
    (route index 1).2 (route index 1).1
    (.pair (topPair 2 prepared.two.levels).1 (topPair 2 prepared.two.levels).2)
    (searchLimit 1) 0 c1 d1 l1 (by decide) hs1).2.2.2
  let r2 := CanonicalPolicy.nextResidual r1 1 l1 d1
  have hr2 : r2<41 := CanonicalPolicy.accepted_one_residual ⟨r1,hr1⟩ hd1
  have hf2 : CanonicalPolicy.threshold 2 r2<20 := by
    have h := (CanonicalPolicy.lower_two_progress ⟨r2,hr2⟩).1
    change CanonicalPolicy.threshold 2 r2≤19 at h
    omega
  obtain ⟨⟨c2,d2,l2⟩,hs2⟩ := context_good_at_route answers hgood index hi 2
    (CanonicalPolicy.threshold 2 r2) (by simpa only [show (2:Layer)≠0 by decide, show (2:Layer)≠3 by decide, if_false] using hf2)
    (topPair 3 prepared.three.levels).1 (topPair 3 prepared.three.levels).2
  have hd2 := (canonical_search_some' answers 2 (CanonicalPolicy.threshold 2 r2)
    (route index 2).2 (route index 2).1
    (.pair (topPair 3 prepared.three.levels).1 (topPair 3 prepared.three.levels).2)
    (searchLimit 2) 0 c2 d2 l2 (by decide) hs2).2.2.2
  let r3 := CanonicalPolicy.nextResidual r2 2 l2 d2
  have hr3 : r3<22 := CanonicalPolicy.accepted_two_residual ⟨r2,hr2⟩ hd2
  have hf3 : CanonicalPolicy.threshold 3 r3<22 := by
    rwa [CanonicalPolicy.lower_three_progress r3 hr3]
  obtain ⟨⟨c3,d3,l3⟩,hs3⟩ := context_good_at_route answers hgood index hi 3
    (CanonicalPolicy.threshold 3 r3) (by simpa only [show (3:Layer)≠0 by decide, if_false, if_true] using hf3) forest.1 forest.2
  have hn1 : ¬CanonicalPolicy.threshold 1 r1≥16 := by omega
  have hn2 : ¬CanonicalPolicy.threshold 2 r2≥22 := by omega
  have hn3 : ¬CanonicalPolicy.threshold 3 r3≥22 := by omega
  dsimp only [r1,r2,r3] at hs1 hs2 hs3 hn1 hn2 hn3
  simp only [searchPreparedLayers,CanonicalPolicy.threshold_top,CanonicalPolicy.totalCredit,
    evalWithAnswerFn_bind,hs0,hn1,if_false,hs1,hn2,hs2,hn3,hs3,evalWithAnswerFn_pure]
  exact ⟨_,rfl⟩

theorem searchPreparedLayers_complete (answers : Answers) (hgood : ContextGood answers)
    (cache : SigGolfCandidate.T3.Cache) (index : Nat) (hi : index<2^31)
    (prepared : PreparedRoots) (forest : PairRoot) :
    ∃ result, evalWithAnswerFn answers (searchPreparedLayers cache index prepared forest)=some result := by
  simpa only [CanonicalPolicy.totalCredit, CanonicalPolicy.topFloor] using
    searchPreparedLayers_complete_at answers hgood cache index hi prepared forest 69 14
      (by norm_num) (by norm_num)

end SigGolfCandidate.Research.SharedForest


namespace ClaudeWCT.W9.T3.CanonicalSearch.DigestGeneric
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9 ENNReal
open SigGolfCandidate.T3.Correctness
open ClaudeWCT.W9.T3.QuerySpace
open SphincsSecurity.Completeness
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable local instance : SampleableType (SearchKey → HashOutput) := Presampling.tableSampler

def run (accept : HashOutput → Bool) (rho : Digest) (message : Message) (counter : Nat) :
    Nat → M (Option (BitVec 32 × HashOutput))
  | 0 => pure none
  | fuel+1 => do
      let output ← digest rho message (BitVec.ofNat 32 counter)
      if accept output then return some (BitVec.ofNat 32 counter,output)
      run accept rho message (counter+1) fuel

def decoder (accept : HashOutput → Bool) (output : HashOutput) : Option HashOutput :=
  if accept output then some output else none

theorem run_none_iff (accept : HashOutput → Bool) (answers : Answers) (rho : Digest) (message : Message) :
    ∀ fuel counter, evalWithAnswerFn answers (run accept rho message counter fuel)=none ↔
      ∀ offset, offset<fuel → accept (evalWithAnswerFn answers
        (digest rho message (BitVec.ofNat 32 (counter+offset))))=false := by
  intro fuel
  induction fuel with
  | zero => intro counter; simp [run]
  | succ fuel ih =>
      intro counter
      simp only [run,evalWithAnswerFn_bind]
      by_cases ha : accept (evalWithAnswerFn answers (digest rho message (BitVec.ofNat 32 counter)))=true
      · simp only [ha,if_true,evalWithAnswerFn_pure,reduceCtorEq,false_iff]
        intro hall
        have h := hall 0 (by omega)
        simp only [Nat.add_zero,ha,Bool.true_eq_false] at h
      · have haf : accept (evalWithAnswerFn answers (digest rho message (BitVec.ofNat 32 counter)))=false :=
          Bool.eq_false_iff.mpr ha
        simp only [haf,Bool.false_eq_true,if_false,ih]
        constructor
        · intro hall offset hoff
          cases offset with
          | zero => simpa only [Nat.add_zero] using haf
          | succ offset =>
              rw [show counter+Nat.succ offset=counter+1+offset by omega]
              exact hall offset (by omega)
        · intro hall offset hoff
          have h := hall (offset+1) (by omega)
          rwa [show counter+(offset+1)=counter+1+offset by omega] at h

theorem run_none_table (accept : HashOutput → Bool) (L : Nat) (hL : L≤2^21)
    (outputs : SearchKey → HashOutput) (fallback : Answers) (rho : Digest) (message : Message) :
    evalWithAnswerFn (Presampling.tableAnswers outputs fallback) (run accept rho message 0 L)=none ↔
      ∀ c : Fin L, decoder accept (outputs (.inr ((rho,message),Fin.castLE hL c)))=none := by
  rw [run_none_iff]
  have hv (c : Nat) (hc : c<L) : evalWithAnswerFn (Presampling.tableAnswers outputs fallback)
      (digest rho message (BitVec.ofNat 32 (0+c)))=outputs (.inr ((rho,message),Fin.castLE hL ⟨c,hc⟩)) := by
    rw [SigGolfCandidate.T3.Presampling.eval_digest]
    have hinput : pad64 (digestInput rho message (BitVec.ofNat 32 (0+c)))=
        searchQuery (.inr ((rho,message),Fin.castLE hL ⟨c,hc⟩)) := by
      simp only [searchQuery,Sum.elim_inr,ClaudeWCT.W9.T3.QuerySpace.digestQuery,
        SigGolfCandidate.T3.Sampling.digestTrial,Nat.zero_add]
      rfl
    rw [hinput,Presampling.tableAnswers_apply]
  have hd (x : HashOutput) : decoder accept x=none ↔ accept x=false := by simp [decoder]
  constructor
  · intro h c
    rw [hd,←hv c c.isLt]
    exact h c c.isLt
  · intro h c hc
    rw [hv c hc]
    exact (hd _).mp (h ⟨c,hc⟩)

theorem run_table_failure (accept : HashOutput → Bool) (L : Nat) (hL : L≤2^21)
    (fallback : Answers) (rho : Digest) (message : Message) :
    Pr[fun outputs => evalWithAnswerFn (Presampling.tableAnswers outputs fallback)
      (run accept rho message 0 L)=none | ($ᵗ (SearchKey → HashOutput) : ProbComp _)] =
      SphincsSecurity.Completeness.failMass (decoder accept)^L := by
  simp_rw [run_none_table accept L hL]
  rw [SphincsSecurity.Completeness.failMass_eq_probEvent]
  have h := Presampling.uniform_table_restriction_failure
    (fun c : Fin L => .inr ((rho,message),Fin.castLE hL c))
    (fun _ _ h => Fin.castLE_injective hL (congrArg Prod.snd (Sum.inr.inj h)))
    (fun x => decoder accept x=none)
  simpa only [failMass_eq_probEvent,Fintype.card_fin,HashOutput,
    SphincsSecurity.HashOutput,SphincsSecurity.hashOutputBits] using h

end ClaudeWCT.W9.T3.CanonicalSearch.DigestGeneric


namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness ClaudeWCT.W9.T3.CanonicalSearch
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem signFromOutput_complete (answers : Answers) (hgood : ContextGood answers)
    (cache : SigGolfCandidate.T3.Cache) (rho : Digest) (counter : BitVec 32) (output : HashOutput)
    (haccepted : digestAccepted output = true) :
    ∃ witness, evalWithAnswerFn answers (signFromOutput cache rho counter output)=some witness := by
  let forest := evalWithAnswerFn answers
    (buildForest (digestIndex output) (forestSelectionFromOutput output) (forestWordsFromOutput output))
  let prepared := evalWithAnswerFn answers (prepareRoots (digestIndex output))
  have hfloor : 14 ≤ conditionalTopFloor output ∧ conditionalTopFloor output ≤ 18 := by
    have h := conditional_bounds_of_accepted output haccepted
    constructor
    · unfold conditionalTopFloor CanonicalPolicy.topFloor
      omega
    · exact h.2.2
  obtain ⟨layers,hl⟩ := searchPreparedLayers_complete_at answers hgood cache
    (digestIndex output) (digestIndex_lt output) prepared forest.2
    (conditionalCredit output) (conditionalTopFloor output) hfloor
    (conditional_credit_floor output)
  dsimp only [forest,prepared] at hl
  simp only [signFromOutput,evalWithAnswerFn_bind,hl,evalWithAnswerFn_pure]
  exact ⟨_,rfl⟩

theorem signPayload_complete (answers : Answers) (hgood : ContextGood answers)
    (cache : SigGolfCandidate.T3.Cache) (message : Message)
    (hd : evalWithAnswerFn answers (sharedDigestSearch (evalWithAnswerFn answers (privateNonce message))
      message 0 digestAttemptLimit)≠none) :
    ∃ signature, evalWithAnswerFn answers (signPayload cache message)=some signature := by
  obtain ⟨⟨counter,output⟩,hs⟩ := Option.ne_none_iff_exists'.mp hd
  have haccepted : digestAccepted output = true :=
    (sharedDigestSearch_some answers (evalWithAnswerFn answers (privateNonce message)) message
      digestAttemptLimit 0 counter output (by decide) hs).2.2.1
  obtain ⟨witness,hw⟩ := signFromOutput_complete answers hgood cache
    (evalWithAnswerFn answers (privateNonce message)) counter output haccepted
  simp only [signPayload,evalWithAnswerFn_bind,hs,hw,evalWithAnswerFn_pure]
  exact ⟨_,rfl⟩

theorem sign_complete (answers : Answers) (hgood : ContextGood answers)
    (cache : SigGolfCandidate.T3.Cache) (message : Message)
    (hmac : evalWithAnswerFn answers (privateMac cache.region)=cache.tag)
    (hd : evalWithAnswerFn answers (sharedDigestSearch (evalWithAnswerFn answers (privateNonce message))
      message 0 digestAttemptLimit)≠none) :
    ∃ signature, evalWithAnswerFn answers (sign cache message)=some signature := by
  simpa only [sign,evalWithAnswerFn_bind,hmac,ne_eq,not_true_eq_false,if_false] using
    signPayload_complete answers hgood cache message hd

def SigningComplete (answers : Answers) (cache : SigGolfCandidate.T3.Cache) : Prop :=
  ∀ message, ∃ signature, evalWithAnswerFn answers (sign cache message)=some signature

def DigestFailed (answers : Answers) (message : Message) : Prop :=
  evalWithAnswerFn answers (sharedDigestSearch (evalWithAnswerFn answers (privateNonce message))
    message 0 digestAttemptLimit)=none

theorem signing_failed_implies_search (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hmac : evalWithAnswerFn answers (privateMac cache.region)=cache.tag)
    (hfail : ¬SigningComplete answers cache) :
    (∃ message, DigestFailed answers message) ∨ (∃ context, ContextFailed context answers) := by
  classical
  by_contra h
  rcases not_or.mp h with ⟨hd,hc⟩
  apply hfail
  intro message
  exact sign_complete answers (not_exists.mp hc) cache message hmac (not_exists.mp hd message)

end SigGolfCandidate.Research.SharedForest


namespace ClaudeWCT.W9.T3.CanonicalSearch
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness ClaudeWCT.W9.T3.QuerySpace
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem context_none_agreement (outputs : SearchKey → HashOutput) (answers fallback : Answers)
    (hagree : Budgets.SearchAgreement outputs answers) (context : EncodingContext) :
    ContextFailed context answers ↔ ContextFailed context (Presampling.tableAnswers outputs fallback) := by
  exact (Presampling.Canonical.search_none_agreement (searchLimit context.1.1)
    (Presampling.searchLimit_le_rows _) outputs answers hagree context.1.1 (contextFloor context)
    context.1.2.1 (.pair context.1.2.2.1 context.1.2.2.2)).trans
    (Presampling.Canonical.search_none_table (searchLimit context.1.1)
      (Presampling.searchLimit_le_rows _) outputs fallback context.1.1 (contextFloor context)
      context.1.2.1 (.pair context.1.2.2.1 context.1.2.2.2)).symm

theorem contextGood_agreement (outputs : SearchKey → HashOutput) (answers fallback : Answers)
    (hagree : Budgets.SearchAgreement outputs answers) :
    ContextGood answers ↔ ContextGood (Presampling.tableAnswers outputs fallback) := by
  constructor
  · intro h context hh
    exact h context ((context_none_agreement outputs answers fallback hagree context).mpr hh)
  · intro h context hh
    exact h context ((context_none_agreement outputs answers fallback hagree context).mp hh)

end ClaudeWCT.W9.T3.CanonicalSearch


namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9 ENNReal
open SigGolfCandidate.T3.Correctness ClaudeWCT.W9.T3.CanonicalSearch
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem signing_failed_keygen (answers : Answers)
    (hfail : ¬SigningComplete answers (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2) :
    (∃ message, DigestFailed answers message) ∨ (∃ context, ContextFailed context answers) := by
  have hc := (SigGolfCandidate.T3.Correctness.keygen_correct answers).2.2
  have hm : (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2.tag=
      evalWithAnswerFn answers (privateMac (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2.region) := hc
  exact signing_failed_implies_search answers _ hm.symm hfail

theorem signing_failure_probability (law : ProbComp Answers)
    (hd : ∀ message, Pr[fun answers => DigestFailed answers message | law]≤1/(2:ENNReal)^400)
    (he : ∀ context, Pr[ContextFailed context | law]≤1/(2:ENNReal)^435) :
    Pr[fun answers => ¬SigningComplete answers (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2 | law]
      ≤1/(2:ENNReal)^138 := by
  have hm := probEvent_mono (mx:=law) (fun answers _ => signing_failed_keygen answers)
  exact hm.trans (all_search_failure_small law (fun message answers => DigestFailed answers message)
    ContextFailed (by simp [Message,Fintype.card_bitVec]) hd he)

end SigGolfCandidate.Research.SharedForest


namespace ClaudeWCT.W9.T3.CanonicalSearch.DigestGeneric
open OracleComp OracleSpec SigGolfCandidate.T3 ENNReal
open SphincsSecurity.Completeness
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem decoder_acceptance (accept : HashOutput → Bool) :
    Pr[fun output => (decoder accept output).isSome | ($ᵗ HashOutput : ProbComp HashOutput)] =
      Pr[fun output => accept output=true | ($ᵗ HashOutput : ProbComp HashOutput)] := by
  apply congrArg (probEvent ($ᵗ HashOutput : ProbComp HashOutput))
  funext output
  apply propext
  simp [decoder]

theorem failure_power_400 (accept : HashOutput → Bool)
    (hacc : (1:ENNReal)/5000≤Pr[fun output => accept output=true | ($ᵗ HashOutput : ProbComp HashOutput)]) :
    failMass (decoder accept)^(2^21)≤1/(2:ENNReal)^400 := by
  apply Budgets.V5.failure_power_of_rate _ (1/5000) (2^21) 400 (by norm_num) (by norm_num) _ (by norm_num)
  rw [decoder_acceptance]
  have he : ENNReal.ofReal (((1/5000 : ℚ) : ℚ) : ℝ)=(1:ENNReal)/5000 := by
    push_cast
    rw [ENNReal.ofReal_div_of_pos (by norm_num),ENNReal.ofReal_one,ENNReal.ofReal_ofNat]
  rw [he]
  exact hacc

end ClaudeWCT.W9.T3.CanonicalSearch.DigestGeneric


namespace ClaudeWCT.W9.T3.CanonicalSearch.DigestGeneric
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9 ENNReal
open SigGolfCandidate.T3.Correctness
open ClaudeWCT.W9.T3.QuerySpace
open SphincsSecurity.Completeness
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable local instance : SampleableType (SearchKey → HashOutput) := Presampling.tableSampler

theorem run_none_agreement (accept : HashOutput → Bool) (L : Nat) (hL : L≤2^21)
    (outputs : SearchKey → HashOutput) (answers : Answers)
    (hagree : ∀ key, answers (.inl (.inr (searchQuery key)))=outputs key) (rho : Digest) (message : Message) :
    evalWithAnswerFn answers (run accept rho message 0 L)=none ↔
      ∀ c : Fin L, decoder accept (outputs (.inr ((rho,message),Fin.castLE hL c)))=none := by
  rw [run_none_iff]
  have hv (c : Nat) (hc : c<L) : evalWithAnswerFn answers
      (digest rho message (BitVec.ofNat 32 (0+c)))=outputs (.inr ((rho,message),Fin.castLE hL ⟨c,hc⟩)) := by
    rw [SigGolfCandidate.T3.Presampling.eval_digest]
    have hinput : pad64 (digestInput rho message (BitVec.ofNat 32 (0+c)))=
        searchQuery (.inr ((rho,message),Fin.castLE hL ⟨c,hc⟩)) := by
      simp only [searchQuery,Sum.elim_inr,ClaudeWCT.W9.T3.QuerySpace.digestQuery,
        SigGolfCandidate.T3.Sampling.digestTrial,Nat.zero_add]
      rfl
    rw [hinput,hagree]
  have hd (x : HashOutput) : decoder accept x=none ↔ accept x=false := by simp [decoder]
  constructor
  · intro h c
    rw [hd,←hv c c.isLt]
    exact h c c.isLt
  · intro h c hc
    rw [hv c hc]
    exact (hd _).mp (h ⟨c,hc⟩)


end ClaudeWCT.W9.T3.CanonicalSearch.DigestGeneric


namespace ClaudeWCT.W9.T3.CanonicalSearch.DigestGeneric
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3
open SigGolfCandidate.T3.Sampling (RCache roRun V publicProgram digestTrial digestTrial_injective
  digestTrial_length V_publicSearch public_randomOracle)
open SphincsSecurity.Completeness
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem run_public (accept : HashOutput → Bool) (rho : Digest) (message : Message) :
    ∀ fuel counter, run accept rho message counter fuel =
      publicProgram (searchLoop (digestTrial rho message) (decoder accept)
        (fun c output => pure (BitVec.ofNat 32 c,output)) fuel counter) := by
  intro fuel
  induction fuel with
  | zero => intro counter; rfl
  | succ fuel ih =>
    intro counter
    rw [run,searchLoop]
    simp only [publicProgram,simulateQ_bind,simulateQ_spec_query,
      SphincsSecurity.Concrete.oracleHash,HasQuery.query,SigGolfCandidate.T3.Sampling.publicHandler,
      digest,publicHash,bind_assoc,pure_bind,digestTrial,decoder]
    apply bind_congr
    intro answer
    split <;> simp only [simulateQ_map,simulateQ_pure,map_pure,ih,publicProgram]

theorem V_run (accept : HashOutput → Bool) (secret : BitVec 256) (z b : ENNReal)
    (hb : 1≤b) (rho : Digest) (message : Message)
    (hstep : z*(failMass (decoder accept)*b+(1-failMass (decoder accept)))≤b)
    (fuel counter : Nat) (hlimit : counter+fuel≤2^32) (cache : RCache)
    (hfresh : ∀ c, counter≤c → c<2^32 → cache (digestTrial rho message c)=none) :
    V secret z (run accept rho message counter fuel) cache≤b := by
  rw [run_public]
  exact V_publicSearch secret z b hb _ _ _ (2^32)
    (fun c _ => digestTrial_length rho message c)
    (fun _ _ hl hr he => digestTrial_injective rho message hl hr he)
    hstep fuel counter hlimit cache hfresh

/-- A digest search with an answer-dependent signing continuation.  The row
freshness invariant survives every digest query. -/
theorem V_run_bind {δ : Type} (accept : HashOutput → Bool) (secret : BitVec 256)
    (z b : ENNReal) (rho : Digest) (message : Message)
    (next : Option (BitVec 32 × HashOutput) → M δ)
    (weight : HashOutput → ENNReal)
    (hnone : ∀ rc, RowsFreshFrom 0 rc → V secret z (next none) rc ≤ b)
    (hsome : ∀ rc, RowsFreshFrom 0 rc → ∀ c, c < 2^32 → ∀ answer,
      accept answer = true →
      V secret z (next (some (BitVec.ofNat 32 c, answer)))
        (rc.cacheQuery (digestTrial rho message c) answer) ≤ weight answer)
    (hstep : z * (acceptedWeight (decoder accept) weight + failMass (decoder accept) * b) ≤ b)
    (fuel counter : Nat) (hlimit : counter + fuel ≤ 2^32) (cache : RCache)
    (hrows : RowsFreshFrom 0 cache)
    (hfresh : ∀ c, counter ≤ c → c < 2^32 → cache (digestTrial rho message c) = none) :
    V secret z (run accept rho message counter fuel >>= next) cache ≤ b := by
  rw [run_public]
  apply V_search_bind secret z b (digestTrial rho message) (decoder accept)
    (fun c output => (BitVec.ofNat 32 c, output)) next weight (RowsFreshFrom 0) (2^32)
    (fun c _ => digestTrial_length rho message c)
    (fun _ _ hl hr he => digestTrial_injective rho message hl hr he)
    (fun rc hr c _ answer => hr.cacheDigest rho message c answer)
    hnone
    (fun rc hr c hc answer value hd => by
      cases hacc : accept answer with
      | false => simp [decoder, hacc] at hd
      | true =>
          simp [decoder, hacc] at hd
          subst value
          exact hsome rc hr c hc answer hacc)
    hstep fuel counter hlimit cache hrows hfresh
end ClaudeWCT.W9.T3.CanonicalSearch.DigestGeneric


namespace ClaudeWCT.W9.T3.CanonicalSearch.DigestGeneric
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
open SigGolfCandidate.T3.Freshness ClaudeWCT.W9.T3.PairRows
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem avoids_run_encoding (accept : HashOutput → Bool) (secret : BitVec 256)
    (target : HashInput) (ht : RowQ target) (rho : Digest) (message : Message) (counter fuel : Nat) :
    Avoids secret target (run accept rho message counter fuel) := by
  induction fuel generalizing counter with
  | zero => unfold run; exact avoids_pure _ _ _
  | succ fuel ih =>
    unfold run
    refine avoids_bind (SigGolfCandidate.T3.Freshness.avoids_digest_encoding secret target ht rho message _) ?_
    intro output
    split
    · exact avoids_pure _ _ _
    · exact ih _

theorem run_preserves_rows (accept : HashOutput → Bool) (secret : BitVec 256)
    (stage : Nat) (rho : Digest) (message : Message) (counter fuel : Nat) (cache : RCache)
    (hc : RowsFreshFrom stage cache) (result : Option (BitVec 32 × HashOutput) × RCache)
    (hr : result∈support (roRun secret (run accept rho message counter fuel) cache)) :
    RowsFreshFrom stage result.2 := by
  intro lay hl tree leaf left right c hlt
  rw [preserves secret _ _ (avoids_run_encoding accept secret _ (rowQ_pairTrial ..)
    rho message counter fuel) cache result hr]
  exact hc lay hl tree leaf left right c hlt
end ClaudeWCT.W9.T3.CanonicalSearch.DigestGeneric
end
-- ==== merged from ClaudeWCT_W9_T3_FullCache_NativeBudgetB1_ExpansionBudget ====
section

section
namespace ClaudeWCT.W9.T3.FullCacheExpansionCost
open OracleComp OracleSpec
open ClaudeWCT.WCT9 (Signature Witness digestAttemptLimit)
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.SearchCost (cost cost_bind cost_pure cost_query)
open SigGolfCandidate.T3.FullCacheExpansionCost (foldlM_cost_ge privatePair_cost)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem shortHash_cost (answers : SigGolfCandidate.T3.Correctness.Answers) (x : HashInput) :
    cost answers (shortHash x) = (pad64 x).length / 64 := by
  unfold shortHash
  rw [cost_bind, cost_pure, Nat.add_zero]
  unfold publicHash
  rw [cost_query]
  rfl
theorem projHash_cost (answers : SigGolfCandidate.T3.Correctness.Answers) (high : Bool) (x : HashInput) :
    cost answers (projHash high x) = (pad64 x).length / 64 := by
  unfold projHash
  rw [cost_bind, cost_pure, Nat.add_zero]
  unfold publicHash
  rw [cost_query]
  rfl
theorem pad64_length_ge (x : HashInput) (hx : 0 < x.length) : 64 ≤ (pad64 x).length := by
  simp only [pad64, List.length_append, List.length_replicate]
  omega
theorem leafHash_cost_ge (answers : SigGolfCandidate.T3.Correctness.Answers) (index coord selected : Nat)
    (ends : List Digest) : 1 ≤ cost answers (ClaudeWCT.WCT9.leafHash index coord selected ends) := by
  unfold ClaudeWCT.WCT9.leafHash
  rw [shortHash_cost]
  refine le_trans (by norm_num) (Nat.div_le_div_right (c := 64) (pad64_length_ge _ ?_))
  simp only [List.length_append, SphincsSecurity.bytesLE_length]
  omega
theorem leafHashP_cost_ge (answers : SigGolfCandidate.T3.Correctness.Answers) (index coord selected : Nat)
    (pad : Digest) (ends : List Digest) : 1 ≤ cost answers (ClaudeWCT.WCT9.leafHashP index coord selected pad ends) := by
  unfold ClaudeWCT.WCT9.leafHashP ClaudeWCT.WCT9.leafInputP
  rw [shortHash_cost]
  refine le_trans (by norm_num) (Nat.div_le_div_right (c := 64) (pad64_length_ge _ ?_))
  simp only [List.length_append, SphincsSecurity.bytesLE_length]
  omega
/-- C1: an FTS hash (either half) costs one compression per 64-byte block, like `shortHash`. -/
theorem ftsHash_cost (answers : SigGolfCandidate.T3.Correctness.Answers) (heap : Nat) (x : HashInput) :
    cost answers (ClaudeWCT.WCT9.ftsHash heap x) = (pad64 x).length / 64 := by
  rw [ClaudeWCT.WCT9.ftsHash_eq]
  split
  · unfold ClaudeWCT.WCT9.highHash
    rw [cost_bind, cost_pure, Nat.add_zero]
    unfold publicHash
    rw [cost_query]
    rfl
  · exact shortHash_cost answers x
/-- C1: the paired leaf of heap `heap` (either half) costs at least one compression. -/
theorem leafHashH_cost_ge (answers : SigGolfCandidate.T3.Correctness.Answers) (heap index coord selected : Nat)
    (pad : Digest) (ends : List Digest) :
    1 ≤ cost answers (ClaudeWCT.WCT9.leafHashH heap index coord selected pad ends) := by
  unfold ClaudeWCT.WCT9.leafHashH ClaudeWCT.WCT9.leafInputP
  rw [ftsHash_cost]
  refine le_trans (by norm_num) (Nat.div_le_div_right (c := 64) (pad64_length_ge _ ?_))
  simp only [List.length_append, SphincsSecurity.bytesLE_length]
  omega
theorem chain_cost_ge (answers : SigGolfCandidate.T3.Correctness.Answers) (index coord selected i start count : Nat)
    (value : Digest) : count ≤ cost answers (ClaudeWCT.WCT9.chain index coord selected i start count value) := by
  unfold ClaudeWCT.WCT9.chain
  refine le_trans (by simp) (foldlM_cost_ge answers _ 1 (fun state step => ?_) (List.range' start count) value)
  have h := projHash_cost answers (ClaudeWCT.WCT9.ftsChainHigh i step)
    (ClaudeWCT.WCT9.ftsChainInputW index coord selected i step state)
  rw [ClaudeWCT.WCT9.ftsChainInputW_padded, ClaudeWCT.WCT9.ftsChainInputW_length] at h
  omega
theorem buildChildF_cost_ge (answers : SigGolfCandidate.T3.Correctness.Answers) (index coord selected : Nat)
    (word : ClaudeWCT.WCT9.Rank) (coefs : List Digest) (padL : Digest) :
    25 ≤ cost answers (ClaudeWCT.WCT9.buildChildF index coord selected word coefs padL) := by
  unfold ClaudeWCT.WCT9.buildChildF
  rw [cost_bind, cost_bind, cost_pure, Nat.add_zero]
  refine le_trans (by norm_num) (Nat.add_le_add (foldlM_cost_ge answers _ 4 (fun state i => ?_) (List.finRange 6) _)
    (leafHashP_cost_ge answers index coord selected padL _))
  simp only [cost_bind, cost_pure, Nat.add_zero]
  exact le_trans (by omega) (Nat.add_le_add (chain_cost_ge answers _ _ _ _ _ _ _) (chain_cost_ge answers _ _ _ _ _ _ _))
theorem buildChildH_cost_ge (answers : SigGolfCandidate.T3.Correctness.Answers) (heap index coord selected : Nat)
    (word : ClaudeWCT.WCT9.Rank) (coefs : List Digest) (padL : Digest) :
    25 ≤ cost answers (ClaudeWCT.WCT9.buildChildH heap index coord selected word coefs padL) := by
  unfold ClaudeWCT.WCT9.buildChildH
  rw [cost_bind, cost_bind, cost_pure, Nat.add_zero]
  refine le_trans (by norm_num) (Nat.add_le_add (foldlM_cost_ge answers _ 4 (fun state i => ?_) (List.finRange 6) _)
    (leafHashH_cost_ge answers heap index coord selected padL _))
  simp only [cost_bind, cost_pure, Nat.add_zero]
  exact le_trans (by omega) (Nat.add_le_add (chain_cost_ge answers _ _ _ _ _ _ _) (chain_cost_ge answers _ _ _ _ _ _ _))
theorem buildCoordinateF_cost_ge (answers : SigGolfCandidate.T3.Correctness.Answers) (index : Nat)
    (coord : ClaudeWCT.WCT9.Coord) (selected : ClaudeWCT.WCT9.Child) (word : ClaudeWCT.WCT9.Rank)
    (prev : Digest × Digest) :
    3200 ≤ cost answers (ClaudeWCT.WCT9.buildCoordinateF index coord selected word prev) := by
  unfold ClaudeWCT.WCT9.buildCoordinateF
  rw [cost_bind, cost_bind]
  refine le_trans ?_ (Nat.le_add_left _ _)
  refine le_trans ?_ (Nat.le_add_right _ _)
  refine le_trans (by simp) (foldlM_cost_ge answers _ 25 (fun state j => ?_) (List.range 128) _)
  rw [cost_bind]
  exact le_trans (buildChildF_cost_ge answers index coord.val j word _ _) (Nat.le_add_right _ _)
theorem forestRows_cost_ge (answers : SigGolfCandidate.T3.Correctness.Answers) (index : Nat)
    (output : HashOutput) :
    28800 ≤ cost answers (ClaudeWCT.WCT9.forestRows index output) := by
  unfold ClaudeWCT.WCT9.forestRows
  apply (show 28800 = (List.finRange 9).length * 3200 by decide).le.trans
  apply foldlM_cost_ge
  intro state coord
  unfold ClaudeWCT.WCT9.openingStep
  simp only [cost_bind, cost_pure, Nat.add_zero]
  exact buildCoordinateF_cost_ge answers index coord _ _ _
theorem signForest_cost_ge (answers : SigGolfCandidate.T3.Correctness.Answers) (index : Nat)
    (output : HashOutput) :
    28800 ≤ cost answers (ClaudeWCT.WCT9.signForest index output) := by
  unfold ClaudeWCT.WCT9.signForest
  rw [cost_bind]
  exact (forestRows_cost_ge answers index output).trans (Nat.le_add_right _ _)
theorem signPayload_cost_ge (answers : SigGolfCandidate.T3.Correctness.Answers) (cache : Cache)
    (message : Message) (sig : Signature)
    (hs : evalWithAnswerFn answers (ClaudeWCT.WCT9.Rev3.signPayload cache message) = some sig) :
    28800 ≤ cost answers (ClaudeWCT.WCT9.Rev3.signPayload cache message) := by
  rw [ClaudeWCT.WCT9.Rev3.signPayload_eq] at hs ⊢
  simp only [evalWithAnswerFn_bind] at hs
  rw [cost_bind]
  cases hd : evalWithAnswerFn answers
      (ClaudeWCT.WCT9.digestSearch (evalWithAnswerFn answers (privateNonce message)) message 0
        digestAttemptLimit) with
  | none => simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at hs
  | some found =>
      obtain ⟨counter, output⟩ := found
      simp only [cost_bind, hd]
      have h := signForest_cost_ge answers (ClaudeWCT.WCT9.digestIndex output) output
      omega
end ClaudeWCT.W9.T3.FullCacheExpansionCost
end
section
namespace ClaudeWCT.W9.T3.ExpansionBudget
open OracleComp OracleSpec
open ClaudeWCT.WCT9 (Signature Witness digestAttemptLimit assembledSignature honestTop
  signForest_root assembled_forest_recovery toT3Signature)
open ClaudeWCT.WCT9.Rev3 (sign expand verify signPayload)
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.SearchCost (cost cost_bind cost_pure cost_query cost_bound)
open SigGolfCandidate.T3.Correctness (Answers cacheRegion maskedTop PiecesAgree CacheTagCorrect
  keygen_correct keygen_cache_tag privateMac_count)
open SigGolfCandidate.T3.Cost (CBound GoodQuery Bound ValidDigits recoverLayerCost recoveryLayersCost
  leafHashCost bound_chain bound_leafHash bound_nodeHash bound_recoverLayer sum_finRange remaining_steps)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem bound_recoverLayerPair (sig : Signature) (index : Nat) (lay : Layer) (digits : List Nat)
    (hd : ValidDigits lay digits) (hlen : digits.length = chainCount lay) (hsum : digits.sum = target lay) :
    CBound (fun _ => True) (recoverLayerCost lay) (ClaudeWCT.WCT9.recoverLayerPair sig index lay digits) := by
  unfold ClaudeWCT.WCT9.recoverLayerPair
  dsimp only
  refine (Bound.mapM_list (P := GoodQuery) (List.finRange (chainCount lay)) _
    (fun i => maxDigit lay i.val - digits.getD i.val 0) (fun i _ => ClaudeWCT.WCT9.Cost.bound_chainW _ _ _ _ _ _ _)).bind'
    (l := leafHashCost lay + height lay) (fun ends hends => ?_) ?_
  · refine (ClaudeWCT.WCT9.Cost.bound_lowerLeafHash lay _ _ ends (by simpa using hends)).bind (fun root _ => ?_)
    refine ((Bound.foldlM_list (P := GoodQuery) (List.finRange (height lay - 1)) _
      (fun _ _ => True) (fun _ => 1) root trivial (fun i hi value _ => ?_)).bind
        (fun top _ => .pure _ 0 trivial)).mono_k (by simp)
    exact ClaudeWCT.WCT9.Cost.bound_lowerNodeHash _ _ _ _ _
  · rw [sum_finRange (chainCount lay) (fun i => maxDigit lay i - digits.getD i 0),
      remaining_steps lay digits hd hlen hsum]
    simp only [recoverLayerCost]
    omega
theorem expand_cost_step (answers : Answers) (message : Message) (pk : Digest) (sig : Signature)
    (counter : BitVec 32) (output : HashOutput)
    (hd : evalWithAnswerFn answers
      (ClaudeWCT.WCT9.digestSearch sig.rho message 0 digestAttemptLimit) = some (counter, output)) :
    cost answers (ClaudeWCT.WCT9.expandWith digestAttemptLimit message pk sig) =
      cost answers (ClaudeWCT.WCT9.digestSearch sig.rho message 0 digestAttemptLimit) +
      cost answers (ClaudeWCT.WCT9.recoverFts sig (ClaudeWCT.WCT9.digestIndex output) output) +
      cost answers (ClaudeWCT.WCT9.expandLayersBC sig (ClaudeWCT.WCT9.digestIndex output) 4
        (.pair (evalWithAnswerFn answers (ClaudeWCT.WCT9.recoverFts sig (ClaudeWCT.WCT9.digestIndex output) output)).1 (evalWithAnswerFn answers (ClaudeWCT.WCT9.recoverFts sig (ClaudeWCT.WCT9.digestIndex output) output)).2)) := by
  simp only [ClaudeWCT.WCT9.expandWith, cost_bind, hd]
  split
  · split <;> simp only [cost_pure, Nat.add_zero, Nat.add_assoc]
  · simp only [cost_pure, Nat.add_zero, Nat.add_assoc]
theorem signPayload_cost_step (answers : Answers) (cache : Cache) (message : Message)
    (counter : BitVec 32) (output : HashOutput)
    (hd : evalWithAnswerFn answers
      (ClaudeWCT.WCT9.digestSearch (evalWithAnswerFn answers (privateNonce message)) message 0
        digestAttemptLimit) = some (counter, output)) :
    cost answers (signPayload cache message) =
      cost answers (privateNonce message) +
      cost answers (ClaudeWCT.WCT9.digestSearch (evalWithAnswerFn answers (privateNonce message)) message 0
        digestAttemptLimit) +
      cost answers (ClaudeWCT.WCT9.signForest (ClaudeWCT.WCT9.digestIndex output) output) +
      cost answers (ClaudeWCT.WCT9.signLayersBC cache (ClaudeWCT.WCT9.digestIndex output) 4
        (.pair (evalWithAnswerFn answers (ClaudeWCT.WCT9.signForest (ClaudeWCT.WCT9.digestIndex output) output)).2.1 (evalWithAnswerFn answers (ClaudeWCT.WCT9.signForest (ClaudeWCT.WCT9.digestIndex output) output)).2.2)) := by
  rw [ClaudeWCT.WCT9.Rev3.signPayload_eq]
  simp only [cost_bind, hd]
  split <;> simp only [cost_pure, Nat.add_zero, Nat.add_assoc]
theorem cost_map' {α β : Type} (answers : Answers) (f : α → β) (x : M α) :
    cost answers (f <$> x) = cost answers x := by
  rw [map_eq_bind_pure_comp, cost_bind]
  simp
theorem cost_topNode (answers : Answers) (index : Nat) (v o : Digest) :
    cost answers (ClaudeWCT.WCT9.topNode index v o) = 1 := by
  apply le_antisymm (cost_bound answers (ClaudeWCT.WCT9.Cost.bound_topNode index v o))
  unfold ClaudeWCT.WCT9.topNode nodeHash
  rw [ClaudeWCT.W9.T3.FullCacheExpansionCost.projHash_cost]
  refine le_trans (by norm_num) (Nat.div_le_div_right (c := 64)
    (ClaudeWCT.W9.T3.FullCacheExpansionCost.pad64_length_ge _ ?_))
  simp only [List.length_append, SphincsSecurity.bytesLE_length, zero16, List.length_replicate]
  omega
theorem cost_expandLayersT_other (answers : Answers) (s : Signature) (index : Nat) (o o' : Digest) :
    ∀ n msg, cost answers (ClaudeWCT.WCT9.expandLayersT s index o n msg) =
      cost answers (ClaudeWCT.WCT9.expandLayersT s index o' n msg) := by
  intro n
  induction n with
  | zero => intro msg; rfl
  | succ n ih =>
    intro msg
    simp only [ClaudeWCT.WCT9.expandLayersT, cost_bind]
    congr 1
    split
    · rename_i counter digits _
      by_cases hn : n = 0
      · subst hn
        simp only [if_true, cost_bind, cost_topNode, cost_pure]
      · simp only [hn, if_false, cost_bind]
        rw [ih]
        congr 1
        congr 1
        split <;> split <;> simp
    · rfl
theorem cost_bind_le {α β : Type} (answers : Answers) (x : M α) (f : α → M β) (k : Nat)
    (h : cost answers (f (evalWithAnswerFn answers x)) ≤ k) : cost answers (x >>= f) ≤ cost answers x + k := by
  rw [cost_bind]; omega
theorem expandS_cost_le (answers : Answers) (message : Message) (pk : Digest) (sig : Signature) :
    cost answers (ClaudeWCT.WCT9.expandS digestAttemptLimit message pk sig) ≤
      cost answers (ClaudeWCT.WCT9.expandWith digestAttemptLimit message pk sig) + ClaudeWCT.WCT9.searchFuel := by
  have hrho : (ClaudeWCT.WCT9.proj sig).rho = sig.rho := rfl
  have hfts : ClaudeWCT.WCT9.recoverFts (ClaudeWCT.WCT9.proj sig) = ClaudeWCT.WCT9.recoverFts sig := rfl
  cases hd : evalWithAnswerFn answers (ClaudeWCT.WCT9.digestSearch sig.rho message 0 digestAttemptLimit) with
  | none =>
    unfold ClaudeWCT.WCT9.expandS ClaudeWCT.WCT9.expandWith
    simp only [cost_bind, hrho, hd, cost_pure]
    omega
  | some found =>
    obtain ⟨counter, output⟩ := found
    rw [expand_cost_step answers message pk sig counter output hd]
    have hC : cost answers (ClaudeWCT.WCT9.expandLayersBC sig (ClaudeWCT.WCT9.digestIndex output) 4
        (.pair (evalWithAnswerFn answers (ClaudeWCT.WCT9.recoverFts sig (ClaudeWCT.WCT9.digestIndex output) output)).1 (evalWithAnswerFn answers (ClaudeWCT.WCT9.recoverFts sig (ClaudeWCT.WCT9.digestIndex output) output)).2)) =
        cost answers (ClaudeWCT.WCT9.expandLayersT (ClaudeWCT.WCT9.proj sig) (ClaudeWCT.WCT9.digestIndex output)
          (ClaudeWCT.WCT9.topSib (ClaudeWCT.WCT9.proj sig)) 4
          (.pair (evalWithAnswerFn answers (ClaudeWCT.WCT9.recoverFts sig (ClaudeWCT.WCT9.digestIndex output) output)).1 (evalWithAnswerFn answers (ClaudeWCT.WCT9.recoverFts sig (ClaudeWCT.WCT9.digestIndex output) output)).2)) := by
      rw [ClaudeWCT.WCT9.expandLayersBC_eq_T sig _ 4 le_rfl, cost_map',
        cost_expandLayersT_other answers _ _ (ClaudeWCT.WCT9.topSib sig) (ClaudeWCT.WCT9.topSib (ClaudeWCT.WCT9.proj sig))]
    unfold ClaudeWCT.WCT9.expandS
    simp only [hrho]
    refine le_trans (cost_bind_le answers _ _ (cost answers (ClaudeWCT.WCT9.recoverFts sig (ClaudeWCT.WCT9.digestIndex output) output) +
      cost answers (ClaudeWCT.WCT9.expandLayersT (ClaudeWCT.WCT9.proj sig) (ClaudeWCT.WCT9.digestIndex output)
          (ClaudeWCT.WCT9.topSib (ClaudeWCT.WCT9.proj sig)) 4
          (.pair (evalWithAnswerFn answers (ClaudeWCT.WCT9.recoverFts sig (ClaudeWCT.WCT9.digestIndex output) output)).1 (evalWithAnswerFn answers (ClaudeWCT.WCT9.recoverFts sig (ClaudeWCT.WCT9.digestIndex output) output)).2)) +
      ClaudeWCT.WCT9.searchFuel) ?_) (by omega)
    simp only [hd, hfts]
    refine le_trans (cost_bind_le answers _ _ (
      cost answers (ClaudeWCT.WCT9.expandLayersT (ClaudeWCT.WCT9.proj sig) (ClaudeWCT.WCT9.digestIndex output)
          (ClaudeWCT.WCT9.topSib (ClaudeWCT.WCT9.proj sig)) 4
          (.pair (evalWithAnswerFn answers (ClaudeWCT.WCT9.recoverFts sig (ClaudeWCT.WCT9.digestIndex output) output)).1 (evalWithAnswerFn answers (ClaudeWCT.WCT9.recoverFts sig (ClaudeWCT.WCT9.digestIndex output) output)).2)) +
      ClaudeWCT.WCT9.searchFuel) ?_) (by omega)
    refine le_trans (cost_bind_le answers _ _ ClaudeWCT.WCT9.searchFuel ?_) (by omega)
    try dsimp only
    split
    · split
      · simp
      · refine le_trans (cost_bind_le answers _ _ 0 ?_) ?_
        · try dsimp only
          split <;> simp
        · rw [Nat.add_zero]
          exact cost_bound answers (ClaudeWCT.WCT9.Cost.bound_searchTop _ _ _ _ _ _)
    · simp
theorem expand_cost_le_expandWith (answers : Answers) (message : Message) (pk : Digest) (sig : Signature) :
    cost answers (expand message pk sig) ≤
      cost answers (ClaudeWCT.WCT9.expandWith digestAttemptLimit message pk sig) + ClaudeWCT.WCT9.searchFuel := by
  unfold ClaudeWCT.WCT9.Rev3.expand
  rw [cost_map']
  exact expandS_cost_le answers message pk sig
theorem sign_cost_ge_mac (answers : Answers) (cache : Cache) (message : Message) :
    2 ≤ cost answers (sign cache message) := by
  have hmac : cost answers (privateMac cache.region) = 2 := by
    simp only [SigGolfCandidate.T3.SearchCost.cost, privateMac_count, evalWithAnswerFn_map]
  simp only [ClaudeWCT.WCT9.Rev3.sign, ClaudeWCT.WCT9.signWith, cost_bind, hmac]
  omega
theorem sign_cost_honest (answers : Answers) (message : Message) :
    cost answers (sign (evalWithAnswerFn answers keygen).2 message) =
      2 + cost answers (signPayload (evalWithAnswerFn answers keygen).2 message) := by
  have hvalid := keygen_cache_tag answers
  have hmac : cost answers (privateMac (evalWithAnswerFn answers keygen).2.region) = 2 := by
    simp only [SigGolfCandidate.T3.SearchCost.cost, privateMac_count, evalWithAnswerFn_map]
  simp only [CacheTagCorrect] at hvalid
  simp only [ClaudeWCT.WCT9.Rev3.sign, ClaudeWCT.WCT9.signWith, cost_bind, hmac, ← hvalid, ne_eq,
    not_true_eq_false, ite_false]
  rfl
theorem recoverFts_budget : 140 + recoveryLayersCost 4 ≤ 622 := by
  have h := SigGolfCandidate.T3.Cost.recoveryLayersCost_four
  omega
end ClaudeWCT.W9.T3.ExpansionBudget
end

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.SearchCost (cost cost_bind cost_pure cost_bound)
open SigGolfCandidate.T3.FullCacheExpansionCost (foldlM_cost_ge)
open ClaudeWCT.W9.T3.FullCacheExpansionCost (buildChildF_cost_ge buildChildH_cost_ge)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem buildSharedCoordinate_cost_ge (answers : Answers) (first : Bool) (index coord : Nat)
    (selected : Child) (word : Rank) (pads : Nat → PairRoot) :
    3200 ≤ cost answers (buildSharedCoordinate first index coord selected word pads) := by
  unfold buildSharedCoordinate
  rw [cost_bind, cost_bind]
  refine le_trans ?_ (Nat.le_add_left _ _)
  refine le_trans ?_ (Nat.le_add_right _ _)
  refine le_trans (by simp) (foldlM_cost_ge answers _ 25 (fun state j => ?_) (List.range 128) _)
  rw [cost_bind]
  exact le_trans (buildChildH_cost_ge answers (128 + j) index coord (rawChild first j) word _ _) (Nat.le_add_right _ _)

theorem buildPair_cost_ge (answers : Answers) (index pair : Nat) (selected : Selection)
    (aWord bWord : Rank) (prev : PairRoot) :
    6400 ≤ cost answers (buildPair index pair selected aWord bWord prev) := by
  unfold buildPair
  simp only [cost_bind, cost_pure, Nat.add_zero]
  have h0 := buildSharedCoordinate_cost_ge answers true index (2*pair) (firstChild selected) aWord (fun _ => prev)
  have h1 := buildSharedCoordinate_cost_ge answers false index (2*pair+1) (secondChild selected) bWord
    (nodesPair (evalWithAnswerFn answers
      (buildSharedCoordinate true index (2*pair) (firstChild selected) aWord (fun _ => prev))).1)
  omega

theorem buildSingleton_cost_ge (answers : Answers) (index : Nat) (selected : Child)
    (word : Rank) (prev : PairRoot) :
    3200 ≤ cost answers (buildSingleton index selected word prev) := by
  unfold buildSingleton
  simp only [cost_bind, cost_pure, Nat.add_zero]
  exact buildSharedCoordinate_cost_ge answers false index 8 selected word (fun _ => prev)

theorem buildForest_cost_ge (answers : Answers) (index : Nat) (selected : ForestSelection) (words : ForestWords) :
    28800 ≤ cost answers (buildForest index selected words) := by
  unfold buildForest
  rw [cost_bind]
  have h0 := foldlM_cost_ge answers
    (fun (state : List PairOpening × PairRoot) (pair : Fin 4) => do
      let built ← buildPair index pair.val (selected.pairs pair)
        (words.first pair) (words.second pair) state.2
      pure (state.1 ++ [built.1], built.2))
    6400 (fun state pair => ?_) (List.finRange 4) ([], ftsStart)
  have h1 := buildSingleton_cost_ge answers index selected.singleton words.singleton
    (evalWithAnswerFn answers ((List.finRange 4).foldlM
      (fun (state : List PairOpening × PairRoot) pair => do
        let built ← buildPair index pair.val (selected.pairs pair)
          (words.first pair) (words.second pair) state.2
        pure (state.1 ++ [built.1], built.2)) ([], ftsStart))).2
  · simp only [List.length_finRange] at h0
    simp only [cost_bind, cost_pure, Nat.add_zero]
    omega
  · simp only [cost_bind, cost_pure, Nat.add_zero]
    exact buildPair_cost_ge answers index pair.val (selected.pairs pair) (words.first pair) (words.second pair) state.2

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.SearchCost (cost cost_bind cost_pure cost_bound)
open ClaudeWCT.W9.T3.ExpansionBudget (cost_bind_le cost_topNode)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem cost_recoverHintedLayers_other (answers : Answers) (sig : Signature)
    (index : Nat) (other other' : Digest) :
    ∀ n msg, cost answers (recoverHintedLayers sig index other n msg) =
      cost answers (recoverHintedLayers sig index other' n msg) := by
  intro n
  induction n with
  | zero => intro msg; rfl
  | succ n ih =>
    intro msg
    simp only [recoverHintedLayers, cost_bind]
    congr 1
    split
    · rename_i counter digits low _
      by_cases hn : n = 0
      · subst hn
        simp only [if_true, cost_bind, cost_topNode, cost_pure]
      · simp only [hn, if_false, cost_bind]
        rw [ih]
        congr 1
        congr 1
        split <;> split <;> simp
    · rfl

theorem expand_cost_le_recovery (answers : Answers) (message : Message) (pk : Digest) (sig : Signature)
    (counter : BitVec 32) (output : HashOutput)
    (hd : evalWithAnswerFn answers (sharedDigestSearch sig.rho message 0 digestAttemptLimit) =
      some (counter, output)) :
    cost answers (expandFill message pk sig) ≤
      cost answers (sharedDigestSearch sig.rho message 0 digestAttemptLimit) +
      cost answers (recoverForest (digestIndex output) (forestSelectionFromOutput output)
        (forestWordsFromOutput output) sig.forest) +
      cost answers (recoverHintedLayers sig (digestIndex output) ((sig.layers 0).path topJ) 4
        (.pair (evalWithAnswerFn answers (recoverForest (digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).1
          (evalWithAnswerFn answers (recoverForest (digestIndex output)
            (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).2)) + searchFuel := by
  unfold expandFill
  split
  · simp only [cost_pure]; omega
  · simp only [cost_bind, nonce_retained, hd,
      show (fillTopSignature sig 0).forest = sig.forest from rfl]
    rw [recoverHintedLayers_fill _ _ _ _ _ le_rfl,
      cost_recoverHintedLayers_other answers sig (digestIndex output)
        (((fillTopSignature sig 0).layers 0).path topJ) ((sig.layers 0).path topJ)]
    simp only [Nat.add_assoc]
    apply Nat.add_le_add_left
    apply Nat.add_le_add_left
    apply Nat.add_le_add_left
    split
    · split
      · simp only [cost_pure]; exact Nat.zero_le _
      · split
        · simp only [cost_pure]; exact Nat.zero_le _
        · refine le_trans (cost_bind_le answers _ _ 0 ?_) ?_
          · split <;> simp only [cost_pure, le_refl]
          · rw [Nat.add_zero]
            exact cost_bound answers (ClaudeWCT.WCT9.Cost.bound_searchTop ..)
    · simp only [cost_pure]; exact Nat.zero_le _

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.SearchCost (cost cost_bind cost_pure cost_bound)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem signFromOutput_cost (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (rho : Digest) (counter : BitVec 32) (output : HashOutput) :
    cost answers (signFromOutput cache rho counter output) =
      cost answers (buildForest (digestIndex output) (forestSelectionFromOutput output) (forestWordsFromOutput output)) +
      cost answers (prepareRoots (digestIndex output)) +
      cost answers (searchPreparedLayers cache (digestIndex output)
        (evalWithAnswerFn answers (prepareRoots (digestIndex output)))
        (evalWithAnswerFn answers (buildForest (digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output))).2) := by
  simp only [signFromOutput, cost_bind]
  split <;> simp only [cost_pure, Nat.add_zero, Nat.add_assoc]

theorem signFromOutput_cost_ge (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (rho : Digest) (counter : BitVec 32) (output : HashOutput) :
    28800 ≤ cost answers (signFromOutput cache rho counter output) := by
  rw [signFromOutput_cost]
  have h := buildForest_cost_ge answers (digestIndex output) (forestSelectionFromOutput output) (forestWordsFromOutput output)
  omega

theorem signFromOutput_recovery_cost_le (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (rho : Digest)
    (counter : BitVec 32) (output : HashOutput) (w : Witness)
    (he : evalWithAnswerFn answers (signFromOutput cache rho counter output) = some w) :
    cost answers (recoverHintedLayers w.signature (digestIndex output) ((w.signature.layers 0).path topJ) 4
      (.pair (evalWithAnswerFn answers (recoverForest (digestIndex output)
        (forestSelectionFromOutput output) (forestWordsFromOutput output) w.signature.forest)).1
        (evalWithAnswerFn answers (recoverForest (digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) w.signature.forest)).2)) ≤
      cost answers (signFromOutput cache rho counter output) + (1616 + 425765) := by
  let index := digestIndex output
  let built := evalWithAnswerFn answers (buildForest index (forestSelectionFromOutput output) (forestWordsFromOutput output))
  let prepared := evalWithAnswerFn answers (prepareRoots index)
  unfold signFromOutput at he
  simp only [evalWithAnswerFn_bind] at he
  cases hs : evalWithAnswerFn answers (searchPreparedLayers cache index prepared built.2) with
  | none =>
    dsimp only [index, prepared, built] at hs
    simp only [hs, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some layers =>
    have hf := searchPreparedLayers_some answers cache index prepared built.2 layers hs
    dsimp only [index, prepared, built] at hs
    simp only [hs, evalWithAnswerFn_pure, Option.some.injEq] at he
    subst w
    let sig : Signature := ⟨rho, layers.policyHints, built.1,
      fun lay => piecesSignature lay (layers.pieces.getD lay.val ([], []))⟩
    have hp : ∀ lay, lay ≠ 0 → evalWithAnswerFn answers
        (recoverLayerPair (mainSignature sig) index lay (layers.digits.getD lay.val [])) =
        builtPair answers lay (route index lay).2 := by
      intro lay hl
      apply recoverLayerPair_wotsPieces answers sig index lay hl _ (hf.validDigits lay)
      change piecesSignature lay (layers.pieces.getD lay.val ([], [])) = _
      rw [hf.honest_pieces hcache (digestIndex_lt output)]
    have hm0 : topPair 1 prepared.one.levels = builtPair answers 1 (route index 1).2 := by
      dsimp only [prepared]; rw [prepareRoots_result]; exact fixedPrepared_pair answers index 1
    have hm1 : topPair 2 prepared.two.levels = builtPair answers 2 (route index 2).2 := by
      dsimp only [prepared]; rw [prepareRoots_result]; exact fixedPrepared_pair answers index 2
    have hm2 : topPair 3 prepared.three.levels = builtPair answers 3 (route index 3).2 := by
      dsimp only [prepared]; rw [prepareRoots_result]; exact fixedPrepared_pair answers index 3
    have hc := hf.recovery_cost_le sig ((sig.layers 0).path topJ) rfl hm0 hm1 hm2 hp
    have hforest : evalWithAnswerFn answers (recoverForest index (forestSelectionFromOutput output)
      (forestWordsFromOutput output) built.1) = built.2 := recoverForest_honest answers index _ _
    change cost answers (recoverHintedLayers sig index ((sig.layers 0).path topJ) 4
      (.pair (evalWithAnswerFn answers (recoverForest index (forestSelectionFromOutput output)
        (forestWordsFromOutput output) built.1)).1
        (evalWithAnswerFn answers (recoverForest index (forestSelectionFromOutput output)
          (forestWordsFromOutput output) built.1)).2)) ≤ _
    rw [hforest, signFromOutput_cost]
    dsimp only [index, prepared, built] at hc ⊢
    omega

/-- The recovery replay bound also holds for the img-v6 normal form of the signer's output (the top path enters
only through `topFoldN`, whose cost is bounded coarsely; the 13-bit hint and the lower layers are unchanged). -/
theorem signFromOutput_recovery_cost_le_norm (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (rho : Digest)
    (counter : BitVec 32) (output : HashOutput) (w : Witness)
    (he : evalWithAnswerFn answers (signFromOutput cache rho counter output) = some w) :
    cost answers (recoverHintedLayers (normTop w.signature) (digestIndex output)
      (((normTop w.signature).layers 0).path topJ) 4
      (.pair (evalWithAnswerFn answers (recoverForest (digestIndex output)
        (forestSelectionFromOutput output) (forestWordsFromOutput output) w.signature.forest)).1
        (evalWithAnswerFn answers (recoverForest (digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) w.signature.forest)).2)) ≤
      cost answers (signFromOutput cache rho counter output) + (1616 + 425765) := by
  let index := digestIndex output
  let built := evalWithAnswerFn answers (buildForest index (forestSelectionFromOutput output) (forestWordsFromOutput output))
  let prepared := evalWithAnswerFn answers (prepareRoots index)
  unfold signFromOutput at he
  simp only [evalWithAnswerFn_bind] at he
  cases hs : evalWithAnswerFn answers (searchPreparedLayers cache index prepared built.2) with
  | none =>
    dsimp only [index, prepared, built] at hs
    simp only [hs, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some layers =>
    have hf := searchPreparedLayers_some answers cache index prepared built.2 layers hs
    dsimp only [index, prepared, built] at hs
    simp only [hs, evalWithAnswerFn_pure, Option.some.injEq] at he
    subst w
    let sig : Signature := ⟨rho, layers.policyHints, built.1,
      fun lay => piecesSignature lay (layers.pieces.getD lay.val ([], []))⟩
    let sig' := normTop sig
    have hh' : sig'.policyHints = layers.policyHints := by
      apply normTop_hints
      have := hf.hints_spec.1
      show layers.policyHints.toNat < 2 ^ 13
      omega
    have hp : ∀ lay, lay ≠ 0 → evalWithAnswerFn answers
        (recoverLayerPair (mainSignature sig') index lay (layers.digits.getD lay.val [])) =
        builtPair answers lay (route index lay).2 := by
      intro lay hl
      apply recoverLayerPair_wotsPieces answers sig' index lay hl _ (hf.validDigits lay)
      rw [normTop_layers_ne sig lay hl]
      change piecesSignature lay (layers.pieces.getD lay.val ([], [])) = _
      rw [hf.honest_pieces hcache (digestIndex_lt output)]
    have hm0 : topPair 1 prepared.one.levels = builtPair answers 1 (route index 1).2 := by
      dsimp only [prepared]; rw [prepareRoots_result]; exact fixedPrepared_pair answers index 1
    have hm1 : topPair 2 prepared.two.levels = builtPair answers 2 (route index 2).2 := by
      dsimp only [prepared]; rw [prepareRoots_result]; exact fixedPrepared_pair answers index 2
    have hm2 : topPair 3 prepared.three.levels = builtPair answers 3 (route index 3).2 := by
      dsimp only [prepared]; rw [prepareRoots_result]; exact fixedPrepared_pair answers index 3
    have hc := hf.recovery_cost_le sig' ((sig'.layers 0).path topJ) hh' hm0 hm1 hm2 hp
    have hforest : evalWithAnswerFn answers (recoverForest index (forestSelectionFromOutput output)
      (forestWordsFromOutput output) built.1) = built.2 := recoverForest_honest answers index _ _
    change cost answers (recoverHintedLayers sig' index ((sig'.layers 0).path topJ) 4
      (.pair (evalWithAnswerFn answers (recoverForest index (forestSelectionFromOutput output)
        (forestWordsFromOutput output) built.1)).1
        (evalWithAnswerFn answers (recoverForest index (forestSelectionFromOutput output)
          (forestWordsFromOutput output) built.1)).2)) ≤ _
    rw [hforest, signFromOutput_cost]
    dsimp only [index, prepared, built] at hc ⊢
    omega

theorem signPayload_cost_step (answers : Answers) (cache : SigGolfCandidate.T3.Cache) (message : Message)
    (counter : BitVec 32) (output : HashOutput)
    (hd : evalWithAnswerFn answers (sharedDigestSearch (evalWithAnswerFn answers (privateNonce message))
      message 0 digestAttemptLimit) = some (counter, output)) :
    cost answers (signPayload cache message) = cost answers (privateNonce message) +
      cost answers (sharedDigestSearch (evalWithAnswerFn answers (privateNonce message)) message 0 digestAttemptLimit) +
      cost answers (signFromOutput cache (evalWithAnswerFn answers (privateNonce message)) counter output) := by
  simp only [signPayload, cost_bind, hd]
  split <;> simp only [cost_pure, Nat.add_zero, Nat.add_assoc]

/-- Expand's pointwise excess over the signer (img-v6): replay 1,616 + 284 = 1,900 plus the worst-case re-derivation of the
11 ancestor top-node nonces `Σ_h (104·2^h − 1) = 425,765`. -/
def expandReplayExtra : Nat := 1900 + 425765

theorem expand_cost_le_payload_add (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (message : Message) (sig : Signature)
    (he : evalWithAnswerFn answers (signPayload cache message) = some sig) (pk : Digest) :
    cost answers (expand message pk sig) ≤ cost answers (signPayload cache message) + expandReplayExtra + searchFuel := by
  unfold expandReplayExtra
  unfold signPayload at he
  simp only [evalWithAnswerFn_bind] at he
  let rho := evalWithAnswerFn answers (privateNonce message)
  cases hd : evalWithAnswerFn answers (sharedDigestSearch rho message 0 digestAttemptLimit) with
  | none =>
    dsimp only [rho] at hd
    simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some found =>
    obtain ⟨counter, output⟩ := found
    dsimp only [rho] at hd
    simp only [hd, evalWithAnswerFn_bind] at he
    cases hs : evalWithAnswerFn answers (signFromOutput cache rho counter output) with
    | none =>
      dsimp only [rho] at hs
      simp only [hs, evalWithAnswerFn_pure, reduceCtorEq] at he
    | some original =>
      have hr := signFromOutput_recovery_cost_le_norm answers cache hcache rho counter output original hs
      have hh := signFromOutput_recovery answers cache hcache rho counter output original hs
      dsimp only [rho] at hs
      simp only [hs, evalWithAnswerFn_pure, Option.some.injEq] at he
      subst sig
      have hd' : evalWithAnswerFn answers (sharedDigestSearch (normTop original.signature).rho message 0
          digestAttemptLimit) = some (counter, output) := by rw [normTop_rho, hh.1]; exact hd
      have hx := expand_cost_le_recovery answers message pk (normTop original.signature) counter output hd'
      have hf := cost_bound answers (bound_recoverForest (digestIndex output)
        (forestSelectionFromOutput output) (forestWordsFromOutput output) original.signature.forest)
      simp only [normTop_rho, normTop_forest] at hx
      rw [hh.1] at hx
      change cost answers (expandFill message pk (normTop original.signature)) ≤ _
      rw [signPayload_cost_step answers cache message counter output hd]
      dsimp only [rho] at hx hr
      omega

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.SearchCost (cost cost_bind cost_pure cost_bound)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem signPayload_cost_ge (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (message : Message) (sig : Signature)
    (hs : evalWithAnswerFn answers (signPayload cache message) = some sig) :
    28800 ≤ cost answers (signPayload cache message) := by
  unfold signPayload at hs
  simp only [evalWithAnswerFn_bind] at hs
  cases hd : evalWithAnswerFn answers (sharedDigestSearch
    (evalWithAnswerFn answers (privateNonce message)) message 0 digestAttemptLimit) with
  | none => simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at hs
  | some found =>
    obtain ⟨counter, output⟩ := found
    rw [signPayload_cost_step answers cache message counter output hd]
    have h := signFromOutput_cost_ge answers cache
      (evalWithAnswerFn answers (privateNonce message)) counter output
    omega

theorem sign_cost_honest (answers : Answers) (message : Message) :
    cost answers (sign (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2 message) =
      2 + cost answers (signPayload (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2 message) := by
  have hvalid := keygen_cache_tag answers
  have hmac : cost answers (privateMac (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2.region) = 2 := by
    simp only [SigGolfCandidate.T3.SearchCost.cost, privateMac_count, evalWithAnswerFn_map]
  simp only [CacheTagCorrect] at hvalid
  simp only [sign, cost_bind, hmac, ← hvalid, ne_eq, not_true_eq_false, ite_false]

/-- img-v6: the pointwise route `expand ≤ 8·sign` is FALSE (PORT v6 §E). What holds pointwise is
`expand ≤ sign + expandReplayExtra + searchFuel` (replay 1,900 + worst ancestor nonce re-derivation 425,765, brute force);
the expand moment is closed by Hölder (`ClaudeWCT.Arith.ExpectHolder.expand_moment_of_holder`). -/
theorem expand_cost_le_sign_add (answers : Answers) (message : Message) (sig : Signature)
    (hs : evalWithAnswerFn answers (sign (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2 message) = some sig) :
    cost answers (expand message (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).1 sig) ≤
      cost answers (sign (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2 message) +
        expandReplayExtra + searchFuel := by
  have hvalid := keygen_cache_tag answers
  have hs' : evalWithAnswerFn answers (signPayload (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2 message) = some sig := by
    simp only [CacheTagCorrect] at hvalid
    simpa only [sign, evalWithAnswerFn_bind, ← hvalid, ne_eq, not_true_eq_false, ite_false] using hs
  have hk := SigGolfCandidate.T3.Correctness.keygen_correct answers
  have h := expand_cost_le_payload_add answers (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2 hk.2.1
    message sig hs' (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).1
  have hmin := signPayload_cost_ge answers (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2 message sig hs'
  rw [sign_cost_honest]
  omega

end SigGolfCandidate.Research.SharedForest
end
-- ==== merged from ClaudeWCT_W9_T3_FullCache_NativeBudgetB1_TopMoment ====
section

/-! # Top-node nonce searches under the lazy random oracle (r3-lean-topbytes, img-v6)

The probabilistic core shared by the v6 KEYGEN moment (every top node is a nonce search with a geometric number of
trials) and the v6 EXPAND excess moment (the brute-forced top-sibling field is uniform):

* `Ev secret program cache F` — the expectation of `F` over the lazy-RO run (`roRun`); `Ev_bind`, `Ev_pure`,
  `Ev_publicQuery_fresh`.
* `topTrial`, `topVal`: the oracle input of trial `n` of the node at `heap` and the node value read from an answer;
  `topNodeHashN_eq`, `topNonceSearch_zero_bind`, `topNonceSearch_succ_bind`, `topTrial_injective`.
* `Ev_topNonceSearch_bind` (value-weighted bound, any `F`) and `V_topNonceSearch_bind` (cost moment), for fresh trial
  inputs and a cache invariant `G` preserved by the search's own queries.
-/

namespace ClaudeWCT.W9.T3.TopMoment
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- Expectation of `F` over the lazy-RO run of `program` from `cache`. -/
noncomputable def Ev {α : Type} (secret : BitVec 256) (program : M α) (cache : RCache)
    (F : α × RCache → ℝ≥0∞) : ℝ≥0∞ :=
  expectedValue (roRun secret program cache) F

theorem Ev_bind {α β : Type} (secret : BitVec 256) (program : M α) (next : α → M β) (cache : RCache)
    (F : β × RCache → ℝ≥0∞) :
    Ev secret (program >>= next) cache F = Ev secret program cache (fun r => Ev secret (next r.1) r.2 F) := by
  unfold Ev; rw [roRun_bind, expectedValue_bind]

theorem Ev_pure {α : Type} (secret : BitVec 256) (value : α) (cache : RCache) (F : α × RCache → ℝ≥0∞) :
    Ev secret (pure value : M α) cache F = F (value, cache) := by
  unfold Ev; rw [roRun_pure, expectedValue_pure]

theorem Ev_mono {α : Type} (secret : BitVec 256) (program : M α) (cache : RCache) {F F' : α × RCache → ℝ≥0∞}
    (h : ∀ r, F r ≤ F' r) : Ev secret program cache F ≤ Ev secret program cache F' :=
  expectedValue_mono _ h

theorem Ev_le_of_support {α : Type} (secret : BitVec 256) (program : M α) (cache : RCache)
    {F : α × RCache → ℝ≥0∞} {c : ℝ≥0∞} (h : ∀ r ∈ support (roRun secret program cache), F r ≤ c) :
    Ev secret program cache F ≤ c :=
  expectedValue_le_of_support h

theorem Ev_publicQuery_fresh {β : Type} (secret : BitVec 256) (input : HashInput) (cache : RCache)
    (hfresh : cache input = none) (next : HashOutput → M β) (F : β × RCache → ℝ≥0∞) :
    Ev secret (publicQuery input >>= next) cache F =
      expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
        (fun answer => Ev secret (next answer) (cache.cacheQuery input answer) F) := by
  rw [Ev_bind]
  unfold Ev
  rw [roRun_publicQuery]
  exact expectedValue_fresh input cache hfresh (fun r => expectedValue (roRun secret (next r.1) r.2) F)

/-- Oracle input of trial `n` of the top node at `heap`. -/
def topTrial (heap n : Nat) (left right : Digest) : HashInput := pad64 (topNodeInput heap n left right)
/-- The node value read from an answer (the half kept at `heap`). -/
def topVal (heap : Nat) (answer : HashOutput) : Digest := projHalf (nodeHalfHigh 3 0 heap) answer

theorem topNodeHashN_eq (heap n : Nat) (left right : Digest) :
    topNodeHashN heap n left right =
      (publicQuery (topTrial heap n left right) >>= fun answer => pure (topVal heap answer)) := rfl

theorem topNonceSearch_zero_bind {β : Type} (h heap : Nat) (left right : Digest) (n : Nat)
    (next : Nat × Digest → M β) :
    (topNonceSearch h heap left right 0 n >>= next) =
      (publicQuery (topTrial heap n left right) >>= fun answer => next (n, topVal heap answer)) := by
  simp only [topNonceSearch, topNodeHashN_eq, bind_assoc, pure_bind]

theorem topNonceSearch_succ_bind {β : Type} (h heap : Nat) (left right : Digest) (fuel n : Nat)
    (next : Nat × Digest → M β) :
    (topNonceSearch h heap left right (fuel + 1) n >>= next) =
      (publicQuery (topTrial heap n left right) >>= fun answer =>
        if topZeroOk h (topVal heap answer) then next (n, topVal heap answer)
        else (topNonceSearch h heap left right fuel (n + 1) >>= next)) := by
  simp only [topNonceSearch, topNodeHashN_eq, bind_assoc, pure_bind]
  congr 1
  funext answer
  split <;> simp only [pure_bind]

theorem topNodeInput_length (heap n : Nat) (left right : Digest) : (topNodeInput heap n left right).length = 64 := by
  simp [topNodeInput, nonceBytes, SphincsSecurity.bytesLE_length]

theorem topTrial_length (heap n : Nat) (left right : Digest) : (topTrial heap n left right).length = 64 := by
  simp [topTrial, pad64, topNodeInput_length]

theorem topTrial_injective (heap : Nat) (left right : Digest) {k n : Nat} (hk : k < 2 ^ 64) (hn : n < 2 ^ 64)
    (he : topTrial heap k left right = topTrial heap n left right) : k = n := by
  unfold topTrial at he
  have he' : topNodeInput heap k left right = topNodeInput heap n left right := by
    unfold pad64 at he
    rw [topNodeInput_length, topNodeInput_length] at he
    exact List.append_cancel_right he
  unfold topNodeInput at he'
  simp only [List.append_assoc] at he'
  have h1 := List.append_inj he' (by simp [SphincsSecurity.bytesLE_length])
  have h2 := List.append_inj h1.2 (by simp [SphincsSecurity.bytesLE_length])
  have h3 := List.append_inj h2.2 (by simp [nonceBytes, SphincsSecurity.bytesLE_length])
  have h4 := SphincsSecurity.bytesLE_injective h3.1
  have h5 := congrArg BitVec.toNat h4
  simp only [BitVec.toNat_ofNat] at h5
  rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num)),
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num)),
    Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hn] at h5
  exact h5

/-- **Value-weighted bound for a top-node nonce search** (any functional `F`). If every continuation after an
accepted trial with value `v` is bounded by `w v`, then a fresh search is bounded by any `b` with
`E_a[ok ? w(val a) : b] ≤ b` and `E_a[w (val a)] ≤ b` (the last trial is kept). -/
theorem Ev_topNonceSearch_bind {β : Type} (secret : BitVec 256) (h heap : Nat) (left right : Digest)
    (next : Nat × Digest → M β) (F : β × RCache → ℝ≥0∞) (G : RCache → Prop) (w : Digest → ℝ≥0∞) (b : ℝ≥0∞)
    (hG : ∀ cache, G cache → ∀ k answer, G (cache.cacheQuery (topTrial heap k left right) answer))
    (hnext : ∀ cache, G cache → ∀ k answer,
      Ev secret (next (k, topVal heap answer)) (cache.cacheQuery (topTrial heap k left right) answer) F ≤
        w (topVal heap answer))
    (hstep : expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun answer => if topZeroOk h (topVal heap answer) then w (topVal heap answer) else b) ≤ b)
    (htail : expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun answer => w (topVal heap answer)) ≤ b) :
    ∀ fuel n, n + fuel < 2 ^ 64 → ∀ cache, G cache →
      (∀ k, n ≤ k → k ≤ n + fuel → cache (topTrial heap k left right) = none) →
      Ev secret (topNonceSearch h heap left right fuel n >>= next) cache F ≤ b := by
  intro fuel
  induction fuel with
  | zero =>
      intro n hn cache hg hfresh
      rw [topNonceSearch_zero_bind, Ev_publicQuery_fresh _ _ _ (hfresh n le_rfl (by omega))]
      exact (expectedValue_mono _ fun answer => hnext cache hg n answer).trans htail
  | succ fuel ih =>
      intro n hn cache hg hfresh
      rw [topNonceSearch_succ_bind, Ev_publicQuery_fresh _ _ _ (hfresh n le_rfl (by omega))]
      refine le_trans (expectedValue_mono _ fun answer => ?_) hstep
      split
      · exact hnext cache hg n answer
      · apply ih (n + 1) (by omega) _ (hG cache hg n answer)
        intro k hk1 hk2
        have hne : topTrial heap k left right ≠ topTrial heap n left right := by
          intro he
          have := topTrial_injective heap left right (by omega) (by omega) he
          omega
        exact (QueryCache.cacheQuery_of_ne (cache := cache) answer hne).trans (hfresh k (by omega) (by omega))

/-- **Cost moment of a top-node nonce search**: every trial is one compression (`z` per trial). -/
theorem V_topNonceSearch_bind {β : Type} (secret : BitVec 256) (z : ℝ≥0∞) (h heap : Nat) (left right : Digest)
    (next : Nat × Digest → M β) (G : RCache → Prop) (B b : ℝ≥0∞)
    (hG : ∀ cache, G cache → ∀ k answer, G (cache.cacheQuery (topTrial heap k left right) answer))
    (hnext : ∀ cache, G cache → ∀ k answer,
      V secret z (next (k, topVal heap answer)) (cache.cacheQuery (topTrial heap k left right) answer) ≤ B)
    (hstep : z * expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun answer => if topZeroOk h (topVal heap answer) then B else b) ≤ b)
    (htail : z * B ≤ b) :
    ∀ fuel n, n + fuel < 2 ^ 64 → ∀ cache, G cache →
      (∀ k, n ≤ k → k ≤ n + fuel → cache (topTrial heap k left right) = none) →
      V secret z (topNonceSearch h heap left right fuel n >>= next) cache ≤ b := by
  intro fuel
  induction fuel with
  | zero =>
      intro n hn cache hg hfresh
      rw [topNonceSearch_zero_bind, V_publicQuery, topTrial_length]
      have hf := expectedValue_fresh (topTrial heap n left right) cache (hfresh n le_rfl (by omega))
        (fun r => V secret z (next (n, topVal heap r.1)) r.2)
      refine le_trans (le_of_eq (congrArg (fun t => z ^ (64 / 64) * t) hf)) ?_
      simp only [show (64 : Nat) / 64 = 1 by decide, pow_one]
      refine le_trans (mul_le_mul' le_rfl ?_) htail
      refine (expectedValue_mono _ fun answer => hnext cache hg n answer).trans ?_
      rw [expectedValue_const (by simp)]
  | succ fuel ih =>
      intro n hn cache hg hfresh
      rw [topNonceSearch_succ_bind, V_publicQuery, topTrial_length]
      have hf := expectedValue_fresh (topTrial heap n left right) cache (hfresh n le_rfl (by omega))
        (fun r => V secret z (if topZeroOk h (topVal heap r.1) then next (n, topVal heap r.1)
          else (topNonceSearch h heap left right fuel (n + 1) >>= next)) r.2)
      refine le_trans (le_of_eq (congrArg (fun t => z ^ (64 / 64) * t) hf)) ?_
      simp only [show (64 : Nat) / 64 = 1 by decide, pow_one]
      refine le_trans (mul_le_mul' le_rfl (expectedValue_mono _ fun answer => ?_)) hstep
      split
      · exact hnext cache hg n answer
      · apply ih (n + 1) (by omega) _ (hG cache hg n answer)
        intro k hk1 hk2
        have hne : topTrial heap k left right ≠ topTrial heap n left right := by
          intro he
          have := topTrial_injective heap left right (by omega) (by omega) he
          omega
        exact (QueryCache.cacheQuery_of_ne (cache := cache) answer hne).trans (hfresh k (by omega) (by omega))

section Prob
open Finset
attribute [local instance] Classical.propDecidable

/-- Bit-window count: exactly `2^(n-k)` words of `n` bits have the `k`-bit window at `s` equal to `j`. -/
theorem window_card (n s k j : Nat) (hsk : s + k ≤ n) (hj : j < 2 ^ k) :
    (univ.filter fun x : BitVec n => x.toNat / 2 ^ s % 2 ^ k = j).card = 2 ^ (n - k) := by
  have e1 : ∀ x : BitVec n, (x.toNat / 2 ^ s % 2 ^ k = j) ↔
      (fun y : BitVec (n - s) => (y.extractLsb' 0 k).toNat = j) (x.extractLsb' s (n - s)) := by
    intro x
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one]
    rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]
  rw [Finset.filter_congr (fun x _ => e1 x)]
  rw [SphincsSecurity.Completeness.card_filter_high (n := n) (w := s) (by omega)
    (fun y : BitVec (n - s) => (y.extractLsb' 0 k).toNat = j)]
  have e2 := SphincsSecurity.Completeness.card_filter_low (n := n - s) (w := k) (by omega)
    (fun u : BitVec k => u.toNat = j)
  rw [e2]
  have h1 : (univ.filter fun u : BitVec k => u.toNat = j).card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨BitVec.ofNat k j, ?_⟩
    ext u
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro hu
      apply BitVec.eq_of_toNat_eq
      rw [hu, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj]
    · rintro rfl
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj]
  rw [h1, one_mul, ← pow_add]
  congr 1
  omega

theorem two_pow_div_two_pow (n k : Nat) (hk : k ≤ n) :
    ((2 : ℝ≥0∞) ^ (n - k)) / 2 ^ n = ((2 : ℝ≥0∞) ^ k)⁻¹ := by
  have hn : (2 : ℝ≥0∞) ^ n = 2 ^ (n - k) * 2 ^ k := by rw [← pow_add]; congr 1; omega
  rw [hn, ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp)),
    mul_comm ((2 : ℝ≥0∞) ^ (n - k))⁻¹, mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), mul_one]

/-- A `k`-bit window of a uniform answer takes each value with probability `2^-k`. -/
theorem prob_window (s k j : Nat) (hsk : s + k ≤ 256) (hj : j < 2 ^ k) :
    Pr[fun a : HashOutput => a.toNat / 2 ^ s % 2 ^ k = j | ($ᵗ HashOutput : ProbComp HashOutput)] =
      ((2 : ℝ≥0∞) ^ k)⁻¹ := by
  rw [probEvent_uniformSample, window_card 256 s k j hsk hj, Fintype.card_bitVec]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  exact two_pow_div_two_pow 256 k (by omega)

/-- Offset of the kept half of a top node answer. -/
def topOff (heap : Nat) : Nat := if nodeHalfHigh 3 0 heap then 128 else 0

theorem topVal_toNat (heap : Nat) (a : HashOutput) :
    (topVal heap a).toNat = a.toNat / 2 ^ topOff heap % 2 ^ 128 := by
  unfold topVal topOff projHalf
  cases nodeHalfHigh 3 0 heap <;> simp [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

/-- Start of the zero window of a height-`h` node value (img-v6, `b_h = h`). -/
def zeroStart (h : Nat) : Nat := if h = 11 then 104 else 128 - topZeroBits h

/-- Campaign T51: the top zero bits are `b_h = 0,0,1,1,2,3,4,5,6,7,8` (#938: `b_h = h`; restated, its users are sorried). -/
theorem topZeroBits_eq {h : Nat} (h1 : 1 ≤ h) (h11 : h ≤ 11) : topZeroBits h = topZeroAlloc.getD h 0 := rfl

theorem window_of_half (x s k : Nat) (hsk : s + k ≤ 128) :
    x % 2 ^ 128 / 2 ^ s % 2 ^ k = x / 2 ^ s % 2 ^ k := by
  have h128 : (2 : Nat) ^ 128 = 2 ^ s * 2 ^ (128 - s) := by rw [← pow_add]; congr 1; omega
  rw [h128, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]

theorem topZeroBits_le (h : Nat) (h11 : h ≤ 11) : topZeroBits h ≤ 8 := by interval_cases h <;> decide

/-- Campaign T51: the zero test of a height-`h` node is the `b_h`-bit window at `zeroStart h` (bits 104..111 at h = 11). -/
theorem topZeroOk_iff {h : Nat} (h1 : 1 ≤ h) (h11 : h ≤ 11) (v : Digest) :
    topZeroOk h v = true ↔ v.toNat / 2 ^ zeroStart h % 2 ^ topZeroBits h = 0 := by
  unfold topZeroOk zeroStart
  by_cases he : h = 11
  · subst he; simp [show topZeroBits 11 = 8 from rfl]
  · rw [if_neg he, if_neg he]
    have hb := topZeroBits_le h h11
    have hv := v.isLt
    have hlt : v.toNat / 2 ^ (128 - topZeroBits h) < 2 ^ topZeroBits h := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
      exact lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.mod_eq_of_lt hlt]
    simp

/-- The accepted trials of a height-`h` node are a bit window of the answer. -/
theorem topZeroOk_topVal_iff {h : Nat} (h1 : 1 ≤ h) (h11 : h ≤ 11) (heap : Nat) (a : HashOutput) :
    topZeroOk h (topVal heap a) = true ↔ a.toNat / 2 ^ (topOff heap + zeroStart h) % 2 ^ topZeroBits h = 0 := by
  have hb := topZeroBits_le h h11
  rw [topZeroOk_iff h1 h11, topVal_toNat, window_of_half _ _ _ (by unfold zeroStart; split <;> omega),
    Nat.div_div_eq_div_mul, ← pow_add]

theorem topOff_add_le (heap : Nat) : topOff heap + 128 ≤ 256 := by
  unfold topOff; split <;> omega

/-- **Acceptance probability** of a top-node trial at height `h`: exactly `2^-b_h` (T51 `b_h = topZeroBits h`). -/
theorem prob_topAccept {h : Nat} (h1 : 1 ≤ h) (h11 : h ≤ 11) (heap : Nat) :
    Pr[fun a : HashOutput => topZeroOk h (topVal heap a) = true | ($ᵗ HashOutput : ProbComp HashOutput)] =
      ((2 : ℝ≥0∞) ^ topZeroBits h)⁻¹ := by
  have hb := topZeroBits_le h h11
  simp only [topZeroOk_topVal_iff h1 h11]
  exact prob_window _ _ _ (by have := topOff_add_le heap; unfold zeroStart; split <;> omega)
    (by positivity)

/-- Expectation of a two-valued function of a uniform answer. -/
theorem expectedValue_uniform_ite (P : HashOutput → Prop) (B b : ℝ≥0∞) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun a => if P a then B else b) =
      Pr[P | ($ᵗ HashOutput : ProbComp HashOutput)] * B +
        (1 - Pr[P | ($ᵗ HashOutput : ProbComp HashOutput)]) * b := by
  have hc := probEvent_compl ($ᵗ HashOutput : ProbComp HashOutput) P
  rw [probFailure_uniformSample, tsub_zero] at hc
  have hn : Pr[fun a => ¬P a | ($ᵗ HashOutput : ProbComp HashOutput)] =
      1 - Pr[P | ($ᵗ HashOutput : ProbComp HashOutput)] :=
    ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top ENNReal.one_ne_top (hc ▸ le_add_right le_rfl)) (by
      rw [add_comm]; exact hc)
  have he : (fun a => if P a then B else b) =
      fun a => (if P a then 1 else 0) * B + (if ¬P a then 1 else 0) * b := by
    funext a; by_cases hp : P a <;> simp [hp]
  rw [he, expectedValue_add, expectedValue_mul_const, expectedValue_mul_const, expectedValue_ite_one,
    expectedValue_ite_one, hn]

end Prob

end ClaudeWCT.W9.T3.TopMoment
end
-- ==== merged from ClaudeWCT_W9_T3_FullCache_NativeBudgetB1_TopFresh ====
section

/-! # Freshness of the top-node trial inputs (r3-lean-topbytes, img-v6)

`TopQ heap x`: the oracle input `x` carries the top-node tweak of `heap` (`queryHeader x = nodeTweak 3 0 0 heap`);
every trial `topTrial heap n l r` does. Markers separate the root children (heaps 2, 3: marker byte 2, 3) from the
private pairs / MAC / nonce (`header`, marker 1), the chains (marker ≥ 128) and the leaf hashes (`leafTweak`, marker 1);
other top nodes differ in the low tweak word (`topNodeWord`, injective on heaps 1..4095).

`Bound.allQueries` / `Bound.and_of_allQueries` combine query predicates with the shape-carrying `Bound` (needed because
the node heaps of a level are only below 4096 thanks to the level lengths). -/

namespace SigGolfCandidate.T3.Cost.Bound
open OracleComp OracleSpec

theorem allQueries {P : Query → Prop} {α : Type} {Post : α → Prop} {k : Nat} {oa : M α}
    (h : Bound P Post k oa) : AllQueriesSatisfy oa P := by
  induction h with
  | pure a k hp => exact allQueriesSatisfy_pure _ _
  | query q f k hq _ ih => exact (allQueriesSatisfy_query_bind_iff q f P).mpr ⟨hq, ih⟩

theorem and_of_allQueries {P P' : Query → Prop} {α : Type} {Post : α → Prop} {k : Nat} {oa : M α}
    (hA : AllQueriesSatisfy oa P) (h : Bound P' Post k oa) : Bound (fun q => P' q ∧ P q) Post k oa := by
  induction h with
  | pure a k hp => exact .pure a k hp
  | query q f k hq _ ih =>
      have hq' := (allQueriesSatisfy_query_bind_iff q f P).mp hA
      exact .query q f k ⟨hq, hq'.1⟩ (fun u => ih u (hq'.2 u))

end SigGolfCandidate.T3.Cost.Bound

namespace ClaudeWCT.W9.T3.TopMoment
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling SigGolfCandidate.T3.Cost
open SigGolfCandidate.T3.Freshness (Avoids avoidsQuery avoids_pure avoids_bind avoids_map avoids_foldlM
  avoids_shortHash_of_ne avoids_privateHash_of_ne HasTag hasTag_privatePair)
open SigGolfCandidate.T3.QuerySpace (queryHeader queryHeader_padded queryHeader_leafInput)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- The input carries the top-node tweak of `heap`. -/
def TopQ (heap : Nat) (x : HashInput) : Prop := queryHeader x = bytesLE 16 (nodeTweak 3 0 0 heap)

theorem topQ_topTrial (heap n : Nat) (left right : Digest) : TopQ heap (topTrial heap n left right) := by
  unfold TopQ topTrial topNodeInput
  simpa only [List.append_assoc] using
    queryHeader_padded (bytesLE 16 left) (nonceBytes n ++ bytesLE 16 right) (bytesLE_length ..) (nodeTweak 3 0 0 heap)

theorem topQ_ne {input target : HashInput} {hdr : BitVec 128} {heap : Nat}
    (h : queryHeader input = bytesLE 16 hdr) (hn : hdr ≠ nodeTweak 3 0 0 heap) (ht : TopQ heap target) :
    input ≠ target := by
  rintro rfl
  exact hn (bytesLE_injective (h.symm.trans ht))

theorem topNodeWord_eq {heap : Nat} (h1 : 1 ≤ heap) (h2 : heap < 4096) : topNodeWord heap = heap := by
  unfold topNodeWord; omega

theorem tweakMarker_top {heap : Nat} (h1 : 1 ≤ heap) (h2 : heap < 4096) :
    tweakMarker (nodeTweak 3 0 0 heap) = heap % 256 := by
  have hl := nodeTweak_top_low 0 heap
  unfold tweakLow at hl
  unfold tweakMarker
  rw [← Nat.mod_mod_of_dvd _ (by norm_num : 256 ∣ 2 ^ 64), hl, topNodeWord_eq h1 h2]

theorem ne_top_of_marker {hdr : BitVec 128} {heap : Nat} (h1 : 1 ≤ heap) (h2 : heap < 4096)
    (hm : tweakMarker hdr ≠ heap % 256) : hdr ≠ nodeTweak 3 0 0 heap := by
  rintro rfl
  exact hm (tweakMarker_top h1 h2)

theorem top_tweak_ne {a b : Nat} (ha1 : 1 ≤ a) (ha2 : a < 4096) (hb1 : 1 ≤ b) (hb2 : b < 4096) (hne : a ≠ b) :
    nodeTweak 3 0 0 a ≠ nodeTweak 3 0 0 b := by
  intro he
  have := congrArg tweakLow he
  rw [nodeTweak_top_low, nodeTweak_top_low, topNodeWord_eq ha1 ha2, topNodeWord_eq hb1 hb2] at this
  exact hne this

section RootChildren
variable (secret : BitVec 256) (target : HashInput) (heap : Nat) (ht : TopQ heap target) (h23 : heap = 2 ∨ heap = 3)
include ht h23

theorem tav_privatePair (tag lay tree position index : Nat) :
    Avoids secret target (privatePair tag lay tree position index) := by
  unfold privatePair
  apply avoids_bind
  · apply avoids_privateHash_of_ne
    obtain ⟨l, t, p, i, hq⟩ := hasTag_privatePair secret tag lay tree position index
    refine topQ_ne hq (ne_top_of_marker (by omega) (by omega) ?_) ht
    rw [header_marker]; omega
  · intro _; exact avoids_pure _ _ _

theorem tav_chain (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    Avoids secret target (chain lay tree leaf i start count value) := by
  unfold chain
  apply avoids_foldlM
  intro value step
  apply avoids_shortHash_of_ne
  have hh : queryHeader (pad64 (chainInput lay tree leaf i step value)) =
      bytesLE 16 (chainHeader lay tree leaf i step) := by
    simpa only [chainInput, List.append_assoc] using
      queryHeader_padded zero16 (zero16 ++ bytesLE 16 value) (by simp [zero16])
        (chainHeader lay tree leaf i step)
  refine topQ_ne hh (ne_top_of_marker (by omega) (by omega) ?_) ht
  have := chainHeader_tweakMarker lay tree leaf i step
  omega

/-- Witness stack: top chains (G `value | header | 0 | 0`, F `chainInput`) carry the chain header in bytes `16..32`. -/
theorem tav_topChain (leaf i start count : Nat) (value : Digest) :
    Avoids secret target (topChain leaf i start count value) := by
  unfold topChain
  apply avoids_foldlM
  intro value step
  apply avoids_shortHash_of_ne
  have hh : queryHeader (pad64 (topChainInput leaf i step value)) = bytesLE 16 (chainHeader 0 0 leaf i step) := by
    unfold topChainInput
    split
    · simpa only [List.append_assoc] using
        queryHeader_padded (bytesLE 16 value) (zero16 ++ zero16) (bytesLE_length ..) (chainHeader 0 0 leaf i step)
    · simpa only [chainInput, List.append_assoc] using
        queryHeader_padded zero16 (zero16 ++ bytesLE 16 value) (by simp [zero16]) (chainHeader 0 0 leaf i step)
  refine topQ_ne hh (ne_top_of_marker (by omega) (by omega) ?_) ht
  have := chainHeader_tweakMarker 0 0 leaf i step
  omega

theorem tav_leafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    Avoids secret target (leafHash lay tree leaf ends) := by
  unfold leafHash
  apply avoids_shortHash_of_ne
  refine topQ_ne (queryHeader_leafInput ..) (ne_top_of_marker (by omega) (by omega) ?_) ht
  rw [leafTweak_marker]; omega

theorem tav_topNodeHashN (heap' n : Nat) (left right : Digest) (h1 : 1 ≤ heap') (h2 : heap' < 4096)
    (hne : heap' ≠ heap) : Avoids secret target (topNodeHashN heap' n left right) := by
  unfold topNodeHashN
  apply avoids_shortHash_of_ne
  have hq := topQ_topTrial heap' n left right
  unfold TopQ topTrial at hq
  exact topQ_ne hq (top_tweak_ne h1 h2 (by omega) (by omega) hne) ht

theorem tav_topNonceSearch (h heap' : Nat) (left right : Digest) (h1 : 1 ≤ heap') (h2 : heap' < 4096)
    (hne : heap' ≠ heap) : ∀ fuel n, Avoids secret target (topNonceSearch h heap' left right fuel n) := by
  intro fuel
  induction fuel with
  | zero =>
      intro n; unfold topNonceSearch
      exact avoids_bind (tav_topNodeHashN secret target heap ht h23 heap' n left right h1 h2 hne)
        fun _ => avoids_pure _ _ _
  | succ fuel ih =>
      intro n; unfold topNonceSearch
      refine avoids_bind (tav_topNodeHashN secret target heap ht h23 heap' n left right h1 h2 hne) fun v => ?_
      split
      · exact avoids_pure _ _ _
      · exact ih (n + 1)

theorem tav_topNodeAt (h heap' : Nat) (left right : Digest) (h1 : 1 ≤ heap') (h2 : heap' < 4096)
    (hne : heap' ≠ heap) : Avoids secret target (topNodeAt h heap' left right) := by
  unfold topNodeAt
  exact tav_topNonceSearch secret target heap ht h23 h heap' left right h1 h2 hne _ 0

theorem tav_nodeHash_root (left right : Digest) : Avoids secret target (nodeHash 3 0 0 1 left right) := by
  unfold nodeHash
  apply avoids_shortHash_of_ne
  have hq : queryHeader (pad64 (bytesLE 16 left ++ bytesLE 16 (nodeTweak 3 0 0 1) ++ zero16 ++ bytesLE 16 right)) =
      bytesLE 16 (nodeTweak 3 0 0 1) := by
    simpa only [List.append_assoc] using
      queryHeader_padded (bytesLE 16 left) (zero16 ++ bytesLE 16 right) (bytesLE_length ..) (nodeTweak 3 0 0 1)
  exact topQ_ne hq (top_tweak_ne (by omega) (by omega) (by omega) (by omega) (by omega)) ht

end RootChildren

end ClaudeWCT.W9.T3.TopMoment
end
-- ==== merged from ClaudeWCT_W9_T3_FullCache_NativeBudgetB1_TopSibling ====
section

/-! # The brute-forced top-sibling field is uniform (r3-lean-topbytes, img-v6 expand excess moment)

Campaign T51: `topFieldV v = v.toNat / 2^112` (bits 112..127 of a level-11 node, the 16 bits expand brute-forces; the
signature omits bits 104..127 and bits 104..111 are the zero bits). For a fresh trial answer `a` of a height-11 node,
the zero test (bits 104..111) and the field (bits 112..127) are disjoint windows of `a`, so (`expected_ok_field`)
`E_a[ok ? φ(field) : b] = 2^-8·avgF φ + (1 − 2^-8)·b` and (`expected_field`) `E_a[φ(field)] = avgF φ`, with
`avgF φ = Σ_{c<2^16} 2^-16 φ c`. -/

namespace ClaudeWCT.W9.T3.TopMoment
open OracleComp OracleSpec OracleComp.EvalDist ENNReal Finset
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-- The 16-bit brute-forced field of a level-11 node value (T51: bits 112..127). -/
def topFieldV (v : Digest) : Nat := v.toNat / 2 ^ 112

theorem topFieldV_lt (v : Digest) : topFieldV v < 2 ^ 16 := by
  have hv := v.isLt
  unfold topFieldV
  rw [Nat.div_lt_iff_lt_mul (by positivity)]
  norm_num at hv ⊢
  omega

/-- Uniform average of `φ` over the 2^16 field values. -/
noncomputable def avgF (φ : Nat → ℝ≥0∞) : ℝ≥0∞ := ∑ c ∈ range (2 ^ 16), ((2 : ℝ≥0∞) ^ 16)⁻¹ * φ c

theorem topFieldV_topVal (heap : Nat) (a : HashOutput) :
    topFieldV (topVal heap a) = a.toNat / 2 ^ (topOff heap + 112) % 2 ^ 16 := by
  unfold topFieldV
  rw [topVal_toNat, show (2 : Nat) ^ 128 = 2 ^ 112 * 2 ^ 16 by norm_num, Nat.mod_mul_right_div_self,
    Nat.div_div_eq_div_mul, ← pow_add]

theorem window_split (y s c : Nat) :
    (y / 2 ^ s % 2 ^ 8 = 0 ∧ y / 2 ^ (s + 8) % 2 ^ 16 = c) ↔ y / 2 ^ s % 2 ^ 24 = c * 2 ^ 8 := by
  rw [pow_add, ← Nat.div_div_eq_div_mul]
  generalize y / 2 ^ s = x
  have hm : x % 2 ^ 24 = x % 2 ^ 8 + 2 ^ 8 * (x / 2 ^ 8 % 2 ^ 16) := by
    rw [show (2 : Nat) ^ 24 = 2 ^ 8 * 2 ^ 16 by norm_num, Nat.mod_mul]
  have h1 := Nat.mod_lt x (show 0 < 2 ^ 8 by norm_num)
  have h2 := Nat.mod_lt (x / 2 ^ 8) (show 0 < 2 ^ 16 by norm_num)
  omega

theorem ok_field_iff (heap : Nat) (a : HashOutput) (c : Nat) :
    (topZeroOk 11 (topVal heap a) = true ∧ topFieldV (topVal heap a) = c) ↔
      a.toNat / 2 ^ (topOff heap + 104) % 2 ^ 24 = c * 2 ^ 8 := by
  rw [topZeroOk_topVal_iff (by norm_num) (by norm_num), topFieldV_topVal, show zeroStart 11 = 104 from rfl,
    show topZeroBits 11 = 8 from rfl, show topOff heap + 112 = topOff heap + 104 + 8 by omega]
  exact window_split a.toNat (topOff heap + 104) c

theorem expected_finite_sum {α ι : Type} [DecidableEq ι] (law : ProbComp α) (s : Finset ι) (f : ι → α → ℝ≥0∞) :
    expectedValue law (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, expectedValue law (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [expectedValue_def]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [expectedValue_add, ih]

theorem prob_not (P : HashOutput → Prop) :
    Pr[fun a => ¬P a | ($ᵗ HashOutput : ProbComp HashOutput)] =
      1 - Pr[P | ($ᵗ HashOutput : ProbComp HashOutput)] := by
  have hc := probEvent_compl ($ᵗ HashOutput : ProbComp HashOutput) P
  rw [probFailure_uniformSample, tsub_zero] at hc
  exact ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top ENNReal.one_ne_top (hc ▸ le_add_right le_rfl))
    (by rw [add_comm]; exact hc)

/-- **Accepted trial, weighted by the omitted field.** -/
theorem expected_ok_field (heap : Nat) (φ : Nat → ℝ≥0∞) (b : ℝ≥0∞) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun a => if topZeroOk 11 (topVal heap a) = true then φ (topFieldV (topVal heap a)) else b) =
      ((2 : ℝ≥0∞) ^ 8)⁻¹ * avgF φ + (1 - ((2 : ℝ≥0∞) ^ 8)⁻¹) * b := by
  have hpt : (fun a : HashOutput => if topZeroOk 11 (topVal heap a) = true then φ (topFieldV (topVal heap a)) else b) =
      fun a => (∑ c ∈ range (2 ^ 16), (if topZeroOk 11 (topVal heap a) = true ∧ topFieldV (topVal heap a) = c
          then 1 else 0) * φ c) + (if ¬ topZeroOk 11 (topVal heap a) = true then 1 else 0) * b := by
    funext a
    by_cases hok : topZeroOk 11 (topVal heap a) = true
    · rw [if_pos hok, if_neg (not_not.mpr hok), zero_mul, add_zero,
        Finset.sum_eq_single (topFieldV (topVal heap a))]
      · rw [if_pos ⟨hok, rfl⟩, one_mul]
      · intro c _ hc
        rw [if_neg (fun h => hc h.2.symm), zero_mul]
      · intro hn; exact absurd (mem_range.mpr (topFieldV_lt _)) hn
    · rw [if_neg hok, if_pos hok, one_mul]
      rw [Finset.sum_eq_zero (fun c _ => by rw [if_neg (fun h => hok h.1), zero_mul]), zero_add]
  have hsum : ∑ c ∈ range (2 ^ 16), expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun a => (if topZeroOk 11 (topVal heap a) = true ∧ topFieldV (topVal heap a) = c then 1 else 0) * φ c) =
      ((2 : ℝ≥0∞) ^ 8)⁻¹ * avgF φ := by
    unfold avgF
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun c hc => ?_)
    rw [expectedValue_mul_const, expectedValue_ite_one]
    have hcl : c < 2 ^ 16 := mem_range.mp hc
    have hp : Pr[fun a : HashOutput => topZeroOk 11 (topVal heap a) = true ∧ topFieldV (topVal heap a) = c |
        ($ᵗ HashOutput : ProbComp HashOutput)] = ((2 : ℝ≥0∞) ^ 24)⁻¹ := by
      simp only [ok_field_iff heap _ c]
      exact prob_window _ _ _ (by have := topOff_add_le heap; omega) (by omega)
    rw [hp, ← mul_assoc, ← ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp)), ← pow_add]
  have hnot : expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun a => (if ¬ topZeroOk 11 (topVal heap a) = true then 1 else 0) * b) =
      (1 - ((2 : ℝ≥0∞) ^ 8)⁻¹) * b := by
    rw [expectedValue_mul_const, expectedValue_ite_one, prob_not, prob_topAccept (by norm_num) (by norm_num)]
    rfl
  rw [hpt, expectedValue_add, expected_finite_sum, hsum, hnot]

/-- **Kept trial** (fuel exhausted): the field is uniform. -/
theorem expected_field (heap : Nat) (φ : Nat → ℝ≥0∞) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun a => φ (topFieldV (topVal heap a))) = avgF φ := by
  have hpt : (fun a : HashOutput => φ (topFieldV (topVal heap a))) =
      fun a => ∑ c ∈ range (2 ^ 16), (if topFieldV (topVal heap a) = c then 1 else 0) * φ c := by
    funext a
    rw [Finset.sum_eq_single (topFieldV (topVal heap a))]
    · rw [if_pos rfl, one_mul]
    · intro c _ hc; rw [if_neg (fun h => hc h.symm), zero_mul]
    · intro hn; exact absurd (mem_range.mpr (topFieldV_lt _)) hn
  rw [hpt, expected_finite_sum]
  unfold avgF
  refine Finset.sum_congr rfl (fun c hc => ?_)
  rw [expectedValue_mul_const, expectedValue_ite_one]
  have hp : Pr[fun a : HashOutput => topFieldV (topVal heap a) = c | ($ᵗ HashOutput : ProbComp HashOutput)] =
      ((2 : ℝ≥0∞) ^ 16)⁻¹ := by
    simp only [topFieldV_topVal]
    exact prob_window _ _ _ (by have := topOff_add_le heap; omega) (mem_range.mp hc)
  rw [hp, mul_comm]

/-- `avgF φ` is a fixed point of the accepted-trial step. -/
theorem avgF_step (heap : Nat) (φ : Nat → ℝ≥0∞) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun a => if topZeroOk 11 (topVal heap a) = true then φ (topFieldV (topVal heap a)) else avgF φ) ≤ avgF φ := by
  rw [expected_ok_field, ← add_mul, add_tsub_cancel_of_le (ENNReal.inv_le_one.mpr (by norm_num)), one_mul]

end ClaudeWCT.W9.T3.TopMoment

namespace SigGolfCandidate.T3.Cost.Bound
open OracleComp OracleSpec

theorem post_of_support {P : Query → Prop} {α : Type} {Post : α → Prop} {k : Nat} {oa : M α}
    (h : Bound P Post k oa) : ∀ x ∈ support oa, Post x := by
  intro x hx
  rw [← fst_countWith weight oa, support_map] at hx
  obtain ⟨r, hr, rfl⟩ := hx
  exact (h.count_support r hr).1

theorem post_of_roRun {P : Query → Prop} {α : Type} {Post : α → Prop} {k : Nat} {oa : M α}
    (h : Bound P Post k oa) (secret : BitVec 256) (cache : SigGolfCandidate.T3.Sampling.RCache)
    (r : α × SigGolfCandidate.T3.Sampling.RCache)
    (hr : r ∈ support (SigGolfCandidate.T3.Sampling.roRun secret oa cache)) : Post r.1 := by
  apply h.post_of_support
  apply SigGolfCandidate.T3.Cost.realize_support_subset secret
  apply support_simulateQ_run'_subset SphincsSecurity.romImpl _ cache
  rw [StateT.run'_eq, support_map]
  exact ⟨r, hr, rfl⟩

end SigGolfCandidate.T3.Cost.Bound

namespace ClaudeWCT.W9.T3.TopMoment
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling SigGolfCandidate.T3.Cost
open SigGolfCandidate.T3.Freshness (Avoids avoidsQuery avoids_map preserves)
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- Query predicate of the freshness bounds: well-formed and avoiding `target`. -/
abbrev PAv (secret : BitVec 256) (target : HashInput) : Query → Prop :=
  fun q => GoodQuery q ∧ avoidsQuery secret target q

theorem avoids_of_bound {α : Type} {secret : BitVec 256} {target : HashInput} {Post : α → Prop} {k : Nat}
    {oa : M α} (h : Bound (PAv secret target) Post k oa) : Avoids secret target oa :=
  (h.mono (fun _ hq => hq.2) (fun _ hp => hp)).allQueries

theorem level_pow (level : Nat) (h1 : 1 ≤ level) (h10 : level ≤ 10) :
    2 ^ (13 - level) / 2 = 2 ^ (12 - level) ∧ 4 ≤ 2 ^ (12 - level) ∧ 2 ^ (12 - level) + 2 ^ (12 - level) ≤ 4096 := by
  interval_cases level <;> norm_num

section RootChildren2
variable (secret : BitVec 256) (target : HashInput) (heap : Nat) (ht : TopQ heap target) (h23 : heap = 2 ∨ heap = 3)
include ht h23

theorem tbound_topLevel (level : Nat) (h1 : 1 ≤ level) (h10 : level ≤ 10) (nodes : List Digest)
    (hlen : nodes.length = 2 ^ (13 - level)) :
    Bound (PAv secret target) (fun result => result.length = nodes.length / 2) (nodes.length / 2 * topLevelCost level)
      (buildTopLevel level nodes) := by
  obtain ⟨hp1, hp2, hp3⟩ := level_pow level h1 h10
  unfold buildTopLevel
  have hc := Bound.mapM_list (P := PAv secret target) (List.range (nodes.length / 2))
    (fun i => if level = 12 then nodeHash 3 0 0 (2 ^ (12 - level) + i) (nodes.getD (2 * i) 0) (nodes.getD (2 * i + 1) 0)
      else Prod.snd <$> topNodeAt level (2 ^ (12 - level) + i) (nodes.getD (2 * i) 0) (nodes.getD (2 * i + 1) 0))
    (fun _ => topLevelCost level) (fun i hi => by
      have hl : level ≠ 12 := by omega
      simp only [hl, if_false]
      rw [List.mem_range, hlen, hp1] at hi
      exact Bound.and_of_allQueries
        (avoids_map _ (tav_topNodeAt secret target heap ht h23 level _ _ _ (by omega) (by omega) (by omega)))
        (Bound.map _ ((bound_topNodeAt _ _ _ _).mono_k (by simp [topLevelCost, hl])) (fun _ _ => trivial)))
  simpa [List.map_const', List.sum_replicate, Nat.mul_comm] using hc

/-- Levels 1..10 of the top tree avoid the trials of the root's children. -/
theorem tbound_levels10 (leaves : List Digest) (hlen : leaves.length = 2 ^ 12) :
    Bound (PAv secret target) (LevelShape 12 10) (∑ i ∈ Finset.range 10, 2 ^ (12 - i) / 2 * topLevelCost (1 + i))
      ((List.range' 1 10).foldlM (fun levels level => do
        let nodes ← buildTopLevel level (levels.getD (level - 1) [])
        pure (levels ++ [nodes])) [leaves]) := by
  refine Bound.foldlM_range'_le 1 10 _ (LevelShape 12) (fun i => 2 ^ (12 - i) / 2 * topLevelCost (1 + i)) [leaves]
    ⟨rfl, fun j hj => by
      have he : j = 0 := by omega
      subst j
      simpa using hlen⟩
    (fun i hi levels hlevels => ?_) (fun _ h => h) le_rfl
  have hprevious : (levels.getD (1 + i - 1) []).length = 2 ^ (12 - i) := by
    simpa using hlevels.2 i (by omega)
  refine (tbound_topLevel secret target heap ht h23 (1 + i) (by omega) (by omega) (levels.getD (1 + i - 1) [])
    (by rw [hprevious]; congr 1; omega)).bind' (l := 0) (fun nodes hnodes => ?_) (by rw [hprevious, Nat.add_zero])
  have hnext : nodes.length = 2 ^ (12 - (i + 1)) := by
    rw [hprevious, show 12 - i = 12 - (i + 1) + 1 by omega, pow_succ, Nat.mul_div_cancel _ (by decide : 0 < 2)] at hnodes
    exact hnodes
  refine .pure (levels ++ [nodes]) 0 ⟨by simp [hlevels.1], ?_⟩
  intro j hj
  by_cases hold : j ≤ i
  · rw [List.getD_append levels [nodes] [] j (by have := hlevels.1; omega)]
    exact hlevels.2 j hold
  · have he : j = i + 1 := by omega
    subst j
    rw [List.getD_append_right levels [nodes] [] (i + 1) (by have := hlevels.1; omega)]
    simp only [hlevels.1, Nat.sub_self, List.getD_cons_zero]
    exact hnext

end RootChildren2

/-- One level step of `buildTopLevels`. -/
def topStepL (levels : List (List Digest)) (level : Nat) : M (List (List Digest)) := do
  let nodes ← buildTopLevel level (levels.getD (level - 1) [])
  pure (levels ++ [nodes])

theorem buildTopLevels_split (leaves : List Digest) :
    buildTopLevels leaves = ((List.range' 1 10).foldlM topStepL [leaves] >>= fun levels =>
      topStepL levels 11 >>= fun levels' => topStepL levels' 12) := by
  unfold buildTopLevels
  rw [show List.range' 1 12 = List.range' 1 10 ++ [11, 12] by decide, List.foldlM_append]
  simp only [List.foldlM_cons, List.foldlM_nil, bind_pure]
  rfl

theorem Ev_const_le {α : Type} (secret : BitVec 256) (program : M α) (cache : RCache) (c : ℝ≥0∞) :
    Ev secret program cache (fun _ => c) ≤ c :=
  Ev_le_of_support secret program cache (fun _ _ => le_rfl)

theorem topTrial_ne_23 (n m : Nat) (l r l' r' : Digest) : topTrial 2 n l r ≠ topTrial 3 m l' r' := by
  intro he
  have h2 := topQ_topTrial 2 n l r
  have h3 := topQ_topTrial 3 m l' r'
  unfold TopQ at h2 h3
  rw [he] at h2
  exact top_tweak_ne (a := 2) (b := 3) (by omega) (by omega) (by omega) (by omega) (by omega)
    (SphincsSecurity.bytesLE_injective (h2.symm.trans h3))

theorem topNonceCap_11 : topNonceCap 11 = 104 * 2 ^ 8 := rfl

/-- The level-11 step on a shape-10 level list: the two root children (heaps 2, 3), as explicit binds. -/
theorem topStepL_11 (levels : List (List Digest)) (hlen10 : (levels.getD 10 []).length = 4) :
    topStepL levels 11 = ((Prod.snd <$> topNodeAt 11 2 ((levels.getD 10 []).getD 0 0) ((levels.getD 10 []).getD 1 0))
      >>= fun a => (Prod.snd <$> topNodeAt 11 3 ((levels.getD 10 []).getD 2 0) ((levels.getD 10 []).getD 3 0))
      >>= fun b => pure (levels ++ [[a, b]])) := by
  unfold topStepL buildTopLevel
  rw [hlen10]
  simp only [show (4 : Nat) / 2 = 2 from rfl, show List.range 2 = [0, 1] from rfl, List.mapM_cons, List.mapM_nil,
    show (11 : Nat) - 1 = 10 from rfl, show ¬ ((11 : Nat) = 12) from by decide, if_false,
    show (2 : Nat) ^ (12 - 11) = 2 from rfl, bind_assoc, pure_bind]

/-- **The root children's omitted fields are independent and uniform** (from the cache after levels 1..10). -/
theorem Ev_rootChildren_tail (secret : BitVec 256) (g : Nat → ℝ≥0∞) (levels : List (List Digest))
    (hshape : LevelShape 12 10 levels) (cache : RCache)
    (hfresh : ∀ heap, heap = 2 ∨ heap = 3 → ∀ n l r, cache (topTrial heap n l r) = none) :
    Ev secret (topStepL levels 11 >>= fun levels' => topStepL levels' 12) cache
      (fun res => g (max (topFieldV ((res.1.getD 11 []).getD 0 0)) (topFieldV ((res.1.getD 11 []).getD 1 0)))) ≤
      avgF (fun c2 => avgF (fun c3 => g (max c2 c3))) := by
  have hlen10 : (levels.getD 10 []).length = 4 := by simpa using hshape.2 10 le_rfl
  have hlen : levels.length = 11 := hshape.1
  rw [topStepL_11 levels hlen10]
  simp only [bind_assoc, bind_map_left, pure_bind]
  unfold topNodeAt
  set L2 := (levels.getD 10 []).getD 0 0
  set R2 := (levels.getD 10 []).getD 1 0
  set L3 := (levels.getD 10 []).getD 2 0
  set R3 := (levels.getD 10 []).getD 3 0
  set F := (fun res : List (List Digest) × RCache =>
    g (max (topFieldV ((res.1.getD 11 []).getD 0 0)) (topFieldV ((res.1.getD 11 []).getD 1 0))))
  -- the root step keeps the children
  have hroot : ∀ (a b : Digest) (σ : RCache),
      Ev secret (topStepL (levels ++ [[a, b]]) 12) σ F ≤ g (max (topFieldV a) (topFieldV b)) := by
    intro a b σ
    unfold topStepL
    rw [Ev_bind]
    refine Ev_le_of_support _ _ _ (fun r _ => ?_)
    rw [Ev_pure]
    simp only [F]
    rw [List.getD_append _ _ _ 11 (by simp [hlen]), List.getD_append_right _ _ _ 11 (by simp [hlen])]
    simp [hlen]
  have hcap : topNonceCap 11 - 1 < 2 ^ 64 := by rw [topNonceCap_11]; norm_num
  refine Ev_topNonceSearch_bind secret 11 2 L2 R2 _ F (fun σ => ∀ n, σ (topTrial 3 n L3 R3) = none)
    (fun v => avgF (fun c3 => g (max (topFieldV v) c3))) _ ?_ ?_ ?_ ?_ (topNonceCap 11 - 1) 0 (by omega) cache
    (fun n => hfresh 3 (Or.inr rfl) n L3 R3) (fun k _ _ => hfresh 2 (Or.inl rfl) k L2 R2)
  · intro σ hσ k ans n
    exact (QueryCache.cacheQuery_of_ne (cache := σ) ans (fun he => topTrial_ne_23 k n L2 R2 L3 R3 he.symm)).trans (hσ n)
  · intro σ hσ k ans
    refine Ev_topNonceSearch_bind secret 11 3 L3 R3 _ F (fun _ => True)
      (fun v => g (max (topFieldV (topVal 2 ans)) (topFieldV v))) _ (fun _ _ _ _ => trivial) ?_ ?_ ?_
      (topNonceCap 11 - 1) 0 (by omega) _ trivial ?_
    · intro σ' _ k' ans'
      exact hroot _ _ _
    · exact avgF_step 3 (fun c => g (max (topFieldV (topVal 2 ans)) c))
    · exact le_of_eq (expected_field 3 (fun c => g (max (topFieldV (topVal 2 ans)) c)))
    · intro n _ _
      exact (QueryCache.cacheQuery_of_ne (cache := σ) ans (fun he => topTrial_ne_23 k n L2 R2 L3 R3 he.symm)).trans (hσ n)
  · exact avgF_step 2 (fun c2 => avgF (fun c3 => g (max c2 c3)))
  · exact le_of_eq (expected_field 2 (fun c2 => avgF (fun c3 => g (max c2 c3))))

/-- **Expand excess, RO part**: over the top-tree build (any prefix producing the 4096 leaves while avoiding the
root children's trials), `E[g(max(field v₂, field v₃))] ≤ avg_{c₂,c₃} g(max c₂ c₃)`. -/
theorem Ev_buildTop_rootChildren (secret : BitVec 256) {γ : Type} (pre : M γ) (sel : γ → List Digest) (k : Nat)
    (hpre : ∀ heap target, TopQ heap target → (heap = 2 ∨ heap = 3) →
      Bound (PAv secret target) (fun s => (sel s).length = 2 ^ 12) k pre) (g : Nat → ℝ≥0∞) :
    Ev secret (pre >>= fun s => buildTopLevels (sel s)) ∅
      (fun res => g (max (topFieldV ((res.1.getD 11 []).getD 0 0)) (topFieldV ((res.1.getD 11 []).getD 1 0)))) ≤
      avgF (fun c2 => avgF (fun c3 => g (max c2 c3))) := by
  rw [Ev_bind]
  refine Ev_le_of_support _ _ _ (fun r1 hr1 => ?_)
  have hlen : (sel r1.1).length = 2 ^ 12 :=
    (hpre 2 _ (topQ_topTrial 2 0 0 0) (Or.inl rfl)).post_of_roRun secret ∅ r1 hr1
  have hf1 : ∀ heap, heap = 2 ∨ heap = 3 → ∀ n l r, r1.2 (topTrial heap n l r) = none := by
    intro heap h23 n l r
    rw [preserves secret _ pre (avoids_of_bound (hpre heap _ (topQ_topTrial heap n l r) h23)) ∅ r1 hr1]
    rfl
  rw [buildTopLevels_split, Ev_bind]
  refine Ev_le_of_support _ _ _ (fun r2 hr2 => ?_)
  have hshape : LevelShape 12 10 r2.1 :=
    (tbound_levels10 secret _ 2 (topQ_topTrial 2 0 0 0) (Or.inl rfl) _ hlen).post_of_roRun secret _ r2 hr2
  have hf2 : ∀ heap, heap = 2 ∨ heap = 3 → ∀ n l r, r2.2 (topTrial heap n l r) = none := by
    intro heap h23 n l r
    rw [preserves secret _ _ (avoids_of_bound (tbound_levels10 secret _ heap (topQ_topTrial heap n l r) h23 _ hlen))
      r1.2 r2 hr2]
    exact hf1 heap h23 n l r
  exact Ev_rootChildren_tail secret g r2.1 hshape r2.2 hf2

end ClaudeWCT.W9.T3.TopMoment
end
-- ==== merged from ClaudeWCT_W9_T3_FullCache_NativeBudgetB1_ExpandExcess ====
section

/-! # img-v6 expand excess, pointwise part (r3-lean-topbytes)

`expand_cost_le_sign_field`: on the honest run, expand ≤ sign + `expandReplayExtra` + the omitted 19-bit field of the
signer's top sibling, and that sibling is one of the two level-11 nodes of the keygen top tree, so the excess is at
most `expandReplayExtra + max (field v₂) (field v₃)` (`v₂, v₃ = treeValue (builtTree answers 0 0) 11 0/1`). -/

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.SearchCost (cost cost_bind cost_pure cost_bound)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
open ClaudeWCT.W9.T3.ExpansionBudget (cost_bind_le cost_topNode)

/-- img-v6: the brute force stops at the first hit; with a hit at `c` it costs at most `c + 1 - c0` node hashes. -/
theorem cost_searchTop_le_hit (answers : Answers) (index : Nat) (v sib pk : Digest) :
    ∀ fuel c0 c, c0 ≤ c → c < c0 + fuel → evalWithAnswerFn answers (topNode index v (setTop sib c)) = pk →
      cost answers (searchTop index v sib pk fuel c0) ≤ c + 1 - c0 := by
  intro fuel
  induction fuel with
  | zero => intro c0 c h1 h2; omega
  | succ fuel ih =>
    intro c0 c h1 h2 h3
    simp only [searchTop, cost_bind, cost_topNode]
    split
    · simp only [cost_pure]; omega
    · rename_i hne
      have hc : c ≠ c0 := by rintro rfl; exact hne h3
      have := ih (c0 + 1) c (by omega) (by omega) h3
      omega

/-- The brute-forced field of a top sibling (T51): bits 112..127 (16 bits; `setTop_self`, `top_lt`). -/
def topField (d : Digest) : Nat := d.toNat / 2 ^ 112

/-- **img-v6 refined expand cost**: on a signature whose full (unfilled) top path recovers to the key, the brute
force costs at most the omitted field of the true top sibling (`topField`), instead of `searchFuel`. -/
theorem expand_cost_le_recovery_field (answers : Answers) (message : Message) (pk : Digest) (sig : Signature)
    (counter : BitVec 32) (output : HashOutput) (result : RecoveredLayers)
    (hd : evalWithAnswerFn answers (sharedDigestSearch sig.rho message 0 digestAttemptLimit) =
      some (counter, output))
    (hr : evalWithAnswerFn answers (recoverHintedLayers sig (digestIndex output) ((sig.layers 0).path topJ) 4
      (.pair (evalWithAnswerFn answers (recoverForest (digestIndex output)
        (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).1
        (evalWithAnswerFn answers (recoverForest (digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).2)) = some result)
    (hpk : result.root = pk) :
    cost answers (expandFill message pk sig) ≤
      cost answers (sharedDigestSearch sig.rho message 0 digestAttemptLimit) +
      cost answers (recoverForest (digestIndex output) (forestSelectionFromOutput output)
        (forestWordsFromOutput output) sig.forest) +
      cost answers (recoverHintedLayers sig (digestIndex output) ((sig.layers 0).path topJ) 4
        (.pair (evalWithAnswerFn answers (recoverForest (digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).1
          (evalWithAnswerFn answers (recoverForest (digestIndex output)
            (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).2)) +
      topField ((sig.layers 0).path topJ) := by
  let index := digestIndex output
  let forest := evalWithAnswerFn answers (recoverForest index (forestSelectionFromOutput output)
    (forestWordsFromOutput output) sig.forest)
  let sig0 := fillTopSignature sig 0
  have hroot : evalWithAnswerFn answers (topNode index result.foldedTop ((sig.layers 0).path topJ)) = pk := by
    have he := eval_recoverHintedLayers_other answers sig index ((sig.layers 0).path topJ)
      ((sig.layers 0).path topJ) 4 (.pair forest.1 forest.2)
    rw [hr] at he
    simp only [Option.map_some, Option.some.injEq] at he
    exact (congrArg RecoveredLayers.root he).symm.trans hpk
  have hr0 : evalWithAnswerFn answers (recoverHintedLayers sig index ((sig0.layers 0).path topJ) 4
      (.pair forest.1 forest.2)) = some {result with
        root := evalWithAnswerFn answers (topNode index result.foldedTop ((sig0.layers 0).path topJ))} := by
    rw [eval_recoverHintedLayers_other answers sig index ((sig.layers 0).path topJ)]
    rw [hr]
    rfl
  unfold expandFill
  split
  · simp only [cost_pure]; omega
  · simp only [cost_bind, nonce_retained, hd,
      show (fillTopSignature sig 0).forest = sig.forest from rfl]
    rw [recoverHintedLayers_fill _ _ _ _ _ le_rfl,
      cost_recoverHintedLayers_other answers sig (digestIndex output)
        (((fillTopSignature sig 0).layers 0).path topJ) ((sig.layers 0).path topJ)]
    simp only [Nat.add_assoc]
    apply Nat.add_le_add_left
    apply Nat.add_le_add_left
    apply Nat.add_le_add_left
    dsimp only [sig0, index, forest] at hr0
    rw [hr0]
    simp only
    split
    · simp only [cost_pure]; exact Nat.zero_le _
    · split
      · simp only [cost_pure]; exact Nat.zero_le _
      · rename_i hz
        refine le_trans (cost_bind_le answers _ _ 0 ?_) ?_
        · split <;> simp only [cost_pure, le_refl]
        · rw [Nat.add_zero]
          have hcompletion : evalWithAnswerFn answers (topNode (digestIndex output) result.foldedTop
              (setTop (((fillTopSignature sig 0).layers 0).path topJ) (topField ((sig.layers 0).path topJ)))) = pk := by
            rw [topPath_fill_signature, setTop_setTop]
            unfold topField
            rw [setTop_self]
            exact hroot
          have hn : topField ((sig.layers 0).path topJ) ≠ 0 := by
            intro he
            rw [he, topPath_fill_signature, setTop_setTop] at hcompletion
            exact hz hcompletion
          have ht := top_lt ((sig.layers 0).path topJ)
          have := cost_searchTop_le_hit answers (digestIndex output) result.foldedTop
            (((fillTopSignature sig 0).layers 0).path topJ) pk searchFuel 1 (topField ((sig.layers 0).path topJ))
            (by omega) (by unfold searchFuel topField at *; omega) hcompletion
          omega



theorem route_top_tree (index : Nat) (h : index < 2 ^ 31) : (route index 0).2 = 0 := by
  simp only [route]
  apply Nat.div_eq_of_lt
  simpa [height] using h

theorem route_top_leaf_lt (index : Nat) : (route index 0).1 < 2 ^ 12 := by
  simp only [route]
  exact Nat.mod_lt _ (by simp [height])

/-- The signer's top sibling (path node at height 11) is the keygen's level-11 node next to the signed leaf. -/
theorem signFromOutput_topSib (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (rho : Digest)
    (counter : BitVec 32) (output : HashOutput) (w : Witness)
    (he : evalWithAnswerFn answers (signFromOutput cache rho counter output) = some w) :
    (w.signature.layers 0).path topJ =
      treeValue (builtTree answers 0 0) 11 ((route (digestIndex output) 0).1 / 2 ^ 11 ^^^ 1) := by
  let index := digestIndex output
  let built := evalWithAnswerFn answers (buildForest index (forestSelectionFromOutput output)
    (forestWordsFromOutput output))
  let prepared := evalWithAnswerFn answers (prepareRoots index)
  unfold signFromOutput at he
  simp only [evalWithAnswerFn_bind] at he
  cases hs : evalWithAnswerFn answers (searchPreparedLayers cache index prepared built.2) with
  | none =>
    dsimp only [index, prepared, built] at hs
    simp only [hs, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some layers =>
    have hf := searchPreparedLayers_some answers cache index prepared built.2 layers hs
    dsimp only [index, prepared, built] at hs
    simp only [hs, evalWithAnswerFn_pure, Option.some.injEq] at he
    subst w
    have hp := hf.honest_pieces hcache (digestIndex_lt output) 0
    change (piecesSignature 0 (layers.pieces.getD (0 : Layer).val ([], []))).path topJ = _
    rw [hp, route_top_tree _ (digestIndex_lt output)]
    simp [piecesSignature, wotsPieces, topJ, wotsTree_top, height, index]

theorem topField_sib_le (answers : Answers) (index : Nat) :
    topField (treeValue (builtTree answers 0 0) 11 ((route index 0).1 / 2 ^ 11 ^^^ 1)) ≤
      max (topField (treeValue (builtTree answers 0 0) 11 0)) (topField (treeValue (builtTree answers 0 0) 11 1)) := by
  have hl := route_top_leaf_lt index
  have h2 : (route index 0).1 / 2 ^ 11 < 2 := by omega
  generalize (route index 0).1 / 2 ^ 11 = b at h2
  interval_cases b
  · exact le_max_right _ _
  · exact le_max_left _ _

/-- Pointwise expand excess over the signer's payload (honest cache, key = top root). -/
theorem expand_cost_le_payload_field (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hreg : cache.region = cacheRegion (maskedTop answers)) (message : Message) (sig : Signature)
    (hs' : evalWithAnswerFn answers (signPayload cache message) = some sig) (pk : Digest)
    (hpk : pk = treeValue (builtTree answers 0 0) 12 0) (htree : TopTreeOK answers) :
    cost answers (expand message pk sig) ≤ cost answers (signPayload cache message) + expandReplayExtra +
        max (topField (treeValue (builtTree answers 0 0) 11 0)) (topField (treeValue (builtTree answers 0 0) 11 1)) := by
  unfold signPayload at hs'
  simp only [evalWithAnswerFn_bind] at hs'
  let rho := evalWithAnswerFn answers (privateNonce message)
  cases hd : evalWithAnswerFn answers (sharedDigestSearch rho message 0 digestAttemptLimit) with
  | none =>
    dsimp only [rho] at hd
    simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at hs'
  | some found =>
    obtain ⟨counter, output⟩ := found
    dsimp only [rho] at hd
    simp only [hd, evalWithAnswerFn_bind] at hs'
    cases hso : evalWithAnswerFn answers (signFromOutput cache rho counter output) with
    | none =>
      dsimp only [rho] at hso
      simp only [hso, evalWithAnswerFn_pure, reduceCtorEq] at hs'
    | some original =>
      have hr := signFromOutput_recovery_cost_le answers cache hreg rho counter output original hso
      have hh := signFromOutput_recovery answers cache hreg rho counter output original hso
      have hsib := signFromOutput_topSib answers cache hreg rho counter output original hso
      have htop := signFromOutput_topPathOK answers cache hreg htree rho counter output original hso
      dsimp only [rho] at hso
      simp only [hso, evalWithAnswerFn_pure, Option.some.injEq] at hs'
      subst sig
      obtain ⟨hrho, result, hres, hroot, hval, _⟩ := hh
      have hhb : original.signature.policyHints.toNat < 2 ^ 13 := by
        have hv := hval
        simp only [policyHintsValid, decide_eq_true_eq] at hv
        have := hv.1
        omega
      rw [expand_eq_expandFill message pk original.signature hhb htop]
      have hd' : evalWithAnswerFn answers (sharedDigestSearch original.signature.rho message 0 digestAttemptLimit) =
          some (counter, output) := by rw [hrho]; exact hd
      have hx := expand_cost_le_recovery_field answers message pk original.signature counter output result hd'
        hres (hroot.trans hpk.symm)
      have hf := cost_bound answers (bound_recoverForest (digestIndex output)
        (forestSelectionFromOutput output) (forestWordsFromOutput output) original.signature.forest)
      have hle := topField_sib_le answers (digestIndex output)
      rw [← hsib] at hle
      rw [hrho] at hx
      dsimp only [rho] at hx hr
      rw [signPayload_cost_step answers cache message counter output hd]
      unfold expandReplayExtra
      omega

/-- The brute-force part of the excess: the larger root-child field if every top node passed its zero test,
the whole search otherwise (cap exhaustion, probability ≤ 2^-143). -/
noncomputable def excessField (answers : Answers) : Nat :=
  open Classical in
  if TopTreeOK answers then
    max (topField (treeValue (builtTree answers 0 0) 11 0)) (topField (treeValue (builtTree answers 0 0) 11 1))
  else searchFuel

/-- **img-v6 pointwise expand excess** (replaces `expand ≤ 8·sign`). -/
theorem expand_cost_le_sign_field (answers : Answers) (message : Message) (sig : Signature)
    (hs : evalWithAnswerFn answers (sign (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2 message) = some sig) :
    cost answers (expand message (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).1 sig) ≤
      cost answers (sign (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2 message) + expandReplayExtra +
        excessField answers := by
  unfold excessField
  by_cases htree : TopTreeOK answers
  swap
  · simp only [htree, if_false]
    exact expand_cost_le_sign_add answers message sig hs
  simp only [htree, if_true]
  have hvalid := keygen_cache_tag answers
  have hk := SigGolfCandidate.T3.Correctness.keygen_correct answers
  have hs' : evalWithAnswerFn answers (signPayload (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2 message) =
      some sig := by
    simp only [CacheTagCorrect] at hvalid
    simpa only [sign, evalWithAnswerFn_bind, ← hvalid, ne_eq, not_true_eq_false, ite_false] using hs
  have h := expand_cost_le_payload_field answers _ hk.2.1 message sig hs' _ hk.1 htree
  rw [sign_cost_honest]
  omega

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedExpansionV6
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.Sampling SigGolfCandidate.T3.Cost
open SigGolfCandidate.T3.Correctness (Answers builtTree treeValue)
open SigGolfCandidate.T3.SourceReplay (fixedAnswers)
open SigGolfCandidate.T3.SearchCost (cost counted_fst)
open SigGolfCandidate.T3.ExpansionClosure (jointCounts)
open SigGolfCandidate.T3.SourceReplay (HashOnly hashOnly_pure hashOnly_bind hashOnly_map hashOnly_buildTopTree)
open SigGolfCandidate.T3.CountedReplay (hashOnly_countBlocks support_replay)
open SigGolfCandidate.Research.SharedForest (Signature Witness sign expand expandReplayExtra topField
  expand_cost_le_sign_field)
open ClaudeWCT.W9.T3.TopMoment
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- The keygen payload after the top tree (masking). -/
def payloadTail (levels : List (List Digest)) : M (Digest × Region) := do
  let masked ← (List.range' 0 12).mapM fun level => maskedLevel (levels.getD level []) level
  let raw := (masked.flatten.flatMap (SphincsSecurity.bytesLE 16)).toArray
  pure ((levels.getD 12 []).getD 0 0, fun i => raw.getD i.val 0)

/-- The keygen after the top tree (masking, MAC). -/
def keygenRest (levels : List (List Digest)) : M (Digest × SigGolfCandidate.T3.Cache) := do
  let (publicKey, region) ← payloadTail levels
  let tag ← privateMac region
  pure (publicKey, ⟨tag, region⟩)

theorem keygen_split : keygen = (buildTopTree >>= keygenRest) := by
  unfold keygen keygenPayload keygenRest payloadTail
  simp only [bind_assoc]

/-- The joint run after the keys (`jointCounts` from fixed keys). -/
def afterKeys (message : Message) (keys : Digest × SigGolfCandidate.T3.Cache) : M (Nat × Nat) :=
  jointCounts (pure keys) (fun keys => sign keys.2 message) (fun keys sig => expand message keys.1 sig)

theorem jointCounts_bind {κ σ ω : Type} (initial : M κ) (signer : κ → M (Option σ)) (expander : κ → σ → M ω) :
    jointCounts initial signer expander = (initial >>= fun k => jointCounts (pure k) signer expander) := by
  unfold jointCounts
  simp only [pure_bind]

/-- The joint run, also returning the keygen's level-11 nodes. -/
def jointI (message : Message) : M ((Nat × Nat) × List Digest) :=
  buildTopTree >>= fun levels => (fun c => (c, levels.getD 11 [])) <$> (keygenRest levels >>= afterKeys message)

theorem jointCounts_eq (message : Message) :
    jointCounts keygen (fun keys => sign keys.2 message) (fun keys sig => expand message keys.1 sig) =
      Prod.fst <$> jointI message := by
  rw [jointCounts_bind, keygen_split]
  unfold jointI afterKeys
  simp only [bind_assoc, map_bind, Functor.map_map, id_map']

/-- Additive version of `eval_joint_cost_le`. -/
theorem eval_joint_cost_le_add {κ σ ω : Type} (answers : Answers)
    (initial : M κ) (signer : κ → M (Option σ)) (expander : κ → σ → M ω) (B : Nat)
    (hbound : ∀ sig, evalWithAnswerFn answers (signer (evalWithAnswerFn answers initial)) = some sig →
      cost answers (expander (evalWithAnswerFn answers initial) sig) ≤
        cost answers (signer (evalWithAnswerFn answers initial)) + B) :
    (evalWithAnswerFn answers (jointCounts initial signer expander)).2 ≤
      (evalWithAnswerFn answers (jointCounts initial signer expander)).1 + B := by
  unfold jointCounts
  have hfst := counted_fst answers (signer (evalWithAnswerFn answers initial))
  generalize hk : evalWithAnswerFn answers initial = keys at hfst hbound ⊢
  simp only [evalWithAnswerFn_bind, hk]
  generalize hc : evalWithAnswerFn answers (countBlocks (signer keys)) = signed at hfst ⊢
  rcases signed with ⟨sig, n⟩
  cases sig with
  | none => simp only [evalWithAnswerFn_pure]; omega
  | some sig =>
      simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
      have hh := hbound sig hfst.symm
      simpa only [SigGolfCandidate.T3.SearchCost.cost, hc] using hh

/-- The leaf part of the top-tree build avoids the root children's trials and yields 4096 leaves (scheme-dependent;
discharged per keygen spec). -/
def TopPrefixOK (secret : BitVec 256) : Prop :=
  ∃ (γ : Type) (pre : M γ) (sel : γ → List Digest) (k : Nat),
    buildTopTree = (pre >>= fun s => buildTopLevels (sel s)) ∧
    ∀ heap target, TopQ heap target → (heap = 2 ∨ heap = 3) →
      Bound (PAv secret target) (fun s => (sel s).length = 2 ^ 12) k pre

/-- The excess weight `2^((8/7)(K + c)/2^20)`. -/
noncomputable def excessWeight (c : Nat) : ℝ≥0∞ :=
  (2 : ℝ≥0∞) ^ ((8 / 7 : ℝ) * ((expandReplayExtra + c : ℕ) : ℝ) / 1048576)

/-- **Numeric obligation (N2b, r3k numerics porter)**: `E_{c₂,c₃ uniform}[2^((8/7)(K + max c₂ c₃)/2^20)] ≤ 2`
(value ≈ 1.806). -/
def ExpandExcessNumeric : Prop := avgF (fun c2 => avgF (fun c3 => excessWeight (max c2 c3))) ≤ 2

theorem excessWeight_mono {a b : Nat} (h : a ≤ b) : excessWeight a ≤ excessWeight b := by
  unfold excessWeight
  apply ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
  have : ((expandReplayExtra + a : ℕ) : ℝ) ≤ ((expandReplayExtra + b : ℕ) : ℝ) := by exact_mod_cast (by omega)
  have h87 : (0 : ℝ) ≤ 8 / 7 := by norm_num
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left this h87) (by norm_num)

/- `expand_excess_moment` moved to `ExpandMomentV6.lean` (needs the cap-exhaustion bound `TopCapBad`). -/
end SigGolfCandidate.Research.SharedExpansionV6
end
-- ==== merged from ClaudeWCT_W9_T3_FullCache_NativeBudgetB1_TopPrefixV6 ====
section

/-! # `TopPrefixOK` for the img-v6 keygen spec (4-leaf top families, carry; r3-lean-topbytes)

The top-tree leaf loop (`topTreeStep`: family coefficients `topCoefsK`, then `buildLeafTopC`) makes only private pair,
chain and leaf-hash queries, so it avoids the root children's trials; its 4096 roots come from
`bound_topTreeStep` (keygen sub-porter, T3/Proofs). -/

namespace ClaudeWCT.W9.T3.TopMoment
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Cost
open SigGolfCandidate.T3.Freshness (Avoids avoids_pure avoids_bind avoids_foldlM)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

section V6Leaves
variable (secret : BitVec 256) (target : HashInput) (heap : Nat) (ht : TopQ heap target) (h23 : heap = 2 ∨ heap = 3)
include ht h23

theorem tav_topPairsFrom (first start : Nat) (init : List Digest) :
    Avoids secret target (topPairsFrom first start init) := by
  unfold topPairsFrom topSeedPair
  exact avoids_foldlM _ _ _ _ (fun acc j => avoids_bind (tav_privatePair secret target heap ht h23 0 0 0 _ 0)
    (fun _ => avoids_pure _ _ _)) _

theorem tav_topCoefsK (f : Nat) (carry : Digest) : Avoids secret target (topCoefsK f carry) := by
  unfold topCoefsK
  exact avoids_bind (tav_topPairsFrom secret target heap ht h23 _ _ _) (fun _ => avoids_pure _ _ _)

theorem tav_buildLeafTopC (leaf : Nat) (coefs : List Digest) (digits : List Nat) (signatureOnly : Bool) :
    Avoids secret target (buildLeafTopC leaf coefs digits signatureOnly) := by
  unfold buildLeafTopC
  apply avoids_bind
  · apply avoids_foldlM
    intro state i
    refine avoids_bind (tav_topChain secret target heap ht h23 _ _ _ _ _) (fun value => ?_)
    split
    · exact avoids_pure _ _ _
    · exact avoids_bind (tav_topChain secret target heap ht h23 _ _ _ _ _) (fun _ => avoids_pure _ _ _)
  · intro state
    split
    · exact avoids_pure _ _ _
    · exact avoids_bind (tav_leafHash secret target heap ht h23 _ _ _ _) (fun _ => avoids_pure _ _ _)

theorem tav_topTreeStep (st : List Digest × List Digest × Digest) (leaf : Nat) :
    Avoids secret target (topTreeStep st leaf) := by
  unfold topTreeStep topFamilyCoefs
  refine avoids_bind ?_ (fun cc => avoids_bind (tav_buildLeafTopC secret target heap ht h23 _ _ _ _)
    (fun _ => avoids_pure _ _ _))
  split
  · exact tav_topCoefsK secret target heap ht h23 _ _
  · exact avoids_pure _ _ _

end V6Leaves

theorem topPrefixOK (secret : BitVec 256) : SigGolfCandidate.Research.SharedExpansionV6.TopPrefixOK secret := by
  refine ⟨_, (List.range (2 ^ height 0)).foldlM topTreeStep ([], [], 0), Prod.fst, topLeavesCost, rfl, ?_⟩
  intro heap target ht h23
  refine Bound.and_of_allQueries
    (avoids_foldlM _ _ _ _ (fun st leaf => tav_topTreeStep secret target heap ht h23 st leaf) _) ?_
  refine ((Bound.foldlM_range 4096 _ (fun i (st : List Digest × List Digest × Digest) => st.1.length = i)
    topLeafCost ([], [], 0) rfl (fun leaf _ st hst => bound_topTreeStep st leaf hst)).mono
      (fun _ h => h) (fun st h => by simpa using h)).mono_k ?_
  rw [topLeaves_sum]

end ClaudeWCT.W9.T3.TopMoment
end
-- ==== merged from ClaudeWCT_W9_T3_FullCache_NativeBudgetB1_ExpandNumericV6 ====
section

/-! # N2b wired (certificate by the r3k numerics porter, `ClaudeWCT.Numerics.V6Budgets.expand_excess_numeric`). -/

namespace ClaudeWCT.Numerics.V6Budgets
open CanonicalCompression Finset
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! N2b with slack (r3-lean-topbytes copy of r3k's certificate proof, final constant 19/10; the kernel check
`expand_block_checked` gives < 1.81213). The slack absorbs the cap-exhaustion term of the expand excess. -/
theorem expand_excess_moment19 (w : ℝ) (hw1 : 1 ≤ w) (hw : w ≤ (expandWNum:ℝ)/expandWDen) :
    w^427665 * ((1:ℝ)/2^38 * ∑ a ∈ range (2^19), ∑ b ∈ range (2^19), w^(max a b)) ≤ 19 / 10 := by
  have hwf := hw.trans expandW_fix
  have hw0 : 0 ≤ w := by linarith
  set v : ℝ := w^8192 with hv
  -- blocks: w^max a b ≤ v^(max (a/L) (b/L) + 1)
  have hpt : ∀ a b : ℕ, w^(max a b) ≤ v^(max (a/8192) (b/8192) + 1) := by
    intro a b
    rw [hv, ← pow_mul]
    exact pow_le_pow_right₀ hw1 (max_block_le a b 8192 (by norm_num))
  have hR : (2:ℕ)^19 = 64 * 8192 := by norm_num
  have hsum : ∑ a ∈ range (2^19), ∑ b ∈ range (2^19), w^(max a b) ≤
      (8192:ℝ) * (8192 * ∑ i ∈ range 64, ∑ j ∈ range 64, v^(max i j + 1)) := by
    calc ∑ a ∈ range (2^19), ∑ b ∈ range (2^19), w^(max a b)
        ≤ ∑ a ∈ range (64*8192), ∑ b ∈ range (64*8192), v^(max (a/8192) (b/8192) + 1) := by
          rw [hR]; exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hpt a b
      _ = (8192:ℝ) * ∑ i ∈ range 64, ∑ b ∈ range (64*8192), v^(max i (b/8192) + 1) :=
          sum_range_mul_div (fun i => ∑ b ∈ range (64*8192), v^(max i (b/8192) + 1)) 64 8192 (by norm_num)
      _ = (8192:ℝ) * (8192 * ∑ i ∈ range 64, ∑ j ∈ range 64, v^(max i j + 1)) := by
          congr 1
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ =>
            sum_range_mul_div (fun j => v^(max i j + 1)) 64 8192 (by norm_num)
  -- fixed point: v ≤ blockV/scale, v^k ≤ pw k/scale
  have hvb : v ≤ (blockV:ℝ)/scale := by
    rw [hv]
    rw [blockV_eq]
    exact (pow_le_pow_left₀ hw0 hwf 8192).trans (powerUp_ratio_ge _ _)
  have hv0 : 0 ≤ v := by positivity
  have hterm : ∀ i j : ℕ, v^(max i j + 1) ≤ (pw (max i j + 1):ℝ)/scale := fun i j =>
    (pow_le_pow_left₀ hv0 hvb _).trans (pw_ratio_ge _)
  have hblock : ∑ i ∈ range 64, ∑ j ∈ range 64, v^(max i j + 1) ≤ (blockSum:ℝ)/scale := by
    calc ∑ i ∈ range 64, ∑ j ∈ range 64, v^(max i j + 1)
        ≤ ∑ i ∈ range 64, ∑ j ∈ range 64, (pw (max i j + 1):ℝ)/scale :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
      _ = (blockSum:ℝ)/scale := by
          simp only [blockSum, Nat.cast_sum, Finset.sum_div]
  have hK : w^427665 ≤ (powerUp expandWFix 427665:ℝ)/scale :=
    (pow_le_pow_left₀ hw0 hwf _).trans (powerUp_ratio_ge _ _)
  have hcheck : (mulUp (powerUp expandWFix 427665) blockSum:ℝ) * 100000 <
      181213 * (scale:ℝ) * 4096 := by exact_mod_cast expand_block_checked
  have hmul := mulUp_ratio_ge (powerUp expandWFix 427665) blockSum
  have hs : (0:ℝ) < scale := by norm_num [scale]
  have hS : (1:ℝ)/2^38 * ∑ a ∈ range (2^19), ∑ b ∈ range (2^19), w^(max a b) ≤
      ((blockSum:ℝ)/scale) / 4096 := by
    have h2 : (1:ℝ)/2^38 * ((8192:ℝ) * (8192 * ((blockSum:ℝ)/scale))) = ((blockSum:ℝ)/scale) / 4096 := by
      generalize ((blockSum:ℝ)/scale) = B
      norm_num; ring
    rw [← h2]
    have h3 : (8192:ℝ) * (8192 * ∑ i ∈ range 64, ∑ j ∈ range 64, v^(max i j + 1)) ≤
        (8192:ℝ) * (8192 * ((blockSum:ℝ)/scale)) := by
      gcongr
    have h4 := hsum.trans h3
    have h5 : (0:ℝ) ≤ 1/2^38 := by positivity
    exact mul_le_mul_of_nonneg_left h4 h5
  have hB : w^427665 * ((1:ℝ)/2^38 * ∑ a ∈ range (2^19), ∑ b ∈ range (2^19), w^(max a b)) ≤
      ((powerUp expandWFix 427665:ℝ)/scale) * (((blockSum:ℝ)/scale) / 4096) :=
    mul_le_mul hK hS
      (mul_nonneg (by norm_num) (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => pow_nonneg hw0 _))
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hC : ((powerUp expandWFix 427665:ℝ)/scale) * (((blockSum:ℝ)/scale) / 4096) ≤
      ((mulUp (powerUp expandWFix 427665) blockSum:ℝ)/scale) / 4096 := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right hmul (by norm_num)
  have hD : ((mulUp (powerUp expandWFix 427665) blockSum:ℝ)/scale) / 4096 ≤ 19 / 10 := by
    have hs0 : (0:ℝ) < scale := by norm_num [scale]
    generalize (mulUp (powerUp expandWFix 427665) blockSum:ℝ) = P at hcheck ⊢
    generalize (scale:ℝ) = S at hcheck hs0 ⊢
    rw [div_div, div_le_iff₀ (by positivity)]
    nlinarith
  linarith


theorem expand_excess_numeric19 :
    avgF19 (fun c2 => avgF19 (fun c3 => excessWeightV6 (max c2 c3))) ≤ ENNReal.ofReal (19 / 10) := by
  set w : ℝ := (2:ℝ)^(1/((917504:ℕ):ℝ)) with hw
  have hw1 : 1 ≤ w := Real.one_le_rpow (by norm_num) (by positivity)
  have hw0 : 0 ≤ w := by linarith
  have hin : ∀ c2, avgF19 (fun c3 => excessWeightV6 (max c2 c3)) =
      ENNReal.ofReal (∑ c3 ∈ range (2^19), (1/2^19) * w^(427665 + max c2 c3)) := by
    intro c2
    simp_rw [excessWeightV6_eq]
    exact avgF19_ofReal (fun c3 => w^(427665 + max c2 c3)) (fun _ => pow_nonneg hw0 _)
  simp_rw [hin]
  rw [avgF19_ofReal _ (fun _ => Finset.sum_nonneg fun _ _ => mul_nonneg (by positivity) (pow_nonneg hw0 _))]
  have hreal : ∑ c2 ∈ range (2^19), (1/2^19) * ∑ c3 ∈ range (2^19), (1/2^19) * w^(427665 + max c2 c3) =
      w^427665 * ((1:ℝ)/2^38 * ∑ a ∈ range (2^19), ∑ b ∈ range (2^19), w^(max a b)) := by
    simp only [pow_add, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [hreal]
  have h := expand_excess_moment19 w hw1 (by rw [hw]; exact expand_w_le)
  exact ENNReal.ofReal_le_ofReal h

end ClaudeWCT.Numerics.V6Budgets

namespace SigGolfCandidate.Research.SharedExpansionV6
open ClaudeWCT.W9.T3.TopMoment
open Finset

/-! Campaign T51: the brute-forced sibling field has 16 bits (`TopMoment.avgF` over `2^16`), so the expand excess
numeric is a monotone bound: every field value is at most `2^16 - 1`, and
`2^((8/7)(427665 + 65535)/2^20) ≤ 1.9` (kernel power check). -/
theorem avgF_le_of (φ : Nat → ENNReal) (B : ENNReal) (h : ∀ c, c < 2 ^ 16 → φ c ≤ B) : avgF φ ≤ B := by
  unfold avgF
  calc ∑ c ∈ range (2 ^ 16), ((2 : ENNReal) ^ 16)⁻¹ * φ c ≤ ∑ _c ∈ range (2 ^ 16), ((2 : ENNReal) ^ 16)⁻¹ * B :=
        Finset.sum_le_sum fun c hc => mul_le_mul' le_rfl (h c (mem_range.mp hc))
    _ = B := by
        rw [Finset.sum_const, card_range, nsmul_eq_mul, ← mul_assoc, Nat.cast_pow, Nat.cast_ofNat,
          ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]

theorem expand_field_power_checked :
    ClaudeWCT.Numerics.CanonicalCompression.powerUp ClaudeWCT.Numerics.V6Budgets.expandWFix (427665 + 65535) * 10 ≤
      19 * ClaudeWCT.Numerics.CanonicalCompression.scale := by
  decide +kernel

theorem excessWeight_field_max : excessWeight 65535 ≤ ENNReal.ofReal (19 / 10) := by
  have he : excessWeight 65535 = ClaudeWCT.Numerics.V6Budgets.excessWeightV6 65535 := by
    unfold excessWeight ClaudeWCT.Numerics.V6Budgets.excessWeightV6 SigGolfCandidate.Research.SharedForest.expandReplayExtra
    norm_num
  rw [he, ClaudeWCT.Numerics.V6Budgets.excessWeightV6_eq]
  apply ENNReal.ofReal_le_ofReal
  have hw := ClaudeWCT.Numerics.V6Budgets.expand_w_le.trans ClaudeWCT.Numerics.V6Budgets.expandW_fix
  have hw0 : (0 : ℝ) ≤ (2:ℝ)^(1/((917504:ℕ):ℝ)) := by positivity
  have hp := ClaudeWCT.Numerics.CanonicalCompression.powerUp_ratio_ge ClaudeWCT.Numerics.V6Budgets.expandWFix
    (427665 + 65535)
  have hc := expand_field_power_checked
  have hs0 : (0 : ℝ) < ClaudeWCT.Numerics.CanonicalCompression.scale := by
    norm_num [ClaudeWCT.Numerics.CanonicalCompression.scale]
  have hc' : (ClaudeWCT.Numerics.CanonicalCompression.powerUp ClaudeWCT.Numerics.V6Budgets.expandWFix
      (427665 + 65535) : ℝ) * 10 ≤ 19 * (ClaudeWCT.Numerics.CanonicalCompression.scale : ℝ) := by exact_mod_cast hc
  calc ((2:ℝ)^(1/((917504:ℕ):ℝ)))^(427665 + 65535)
      ≤ ((ClaudeWCT.Numerics.V6Budgets.expandWFix : ℝ) / ClaudeWCT.Numerics.CanonicalCompression.scale) ^
          (427665 + 65535) := pow_le_pow_left₀ hw0 hw _
    _ ≤ (ClaudeWCT.Numerics.CanonicalCompression.powerUp ClaudeWCT.Numerics.V6Budgets.expandWFix
          (427665 + 65535) : ℝ) / ClaudeWCT.Numerics.CanonicalCompression.scale := hp
    _ ≤ 19 / 10 := by
        rw [div_le_iff₀ hs0]; linarith

/-- N2b with slack: `E_{c₂,c₃}[2^((8/7)(K + max c₂ c₃)/2^20)] ≤ 1.9`. -/
def ExpandExcessNumeric19 : Prop :=
  avgF (fun c2 => avgF (fun c3 => excessWeight (max c2 c3))) ≤ ENNReal.ofReal (19 / 10)

theorem expandExcessNumeric19_holds : ExpandExcessNumeric19 := by
  unfold ExpandExcessNumeric19
  apply avgF_le_of; intro c2 hc2
  apply avgF_le_of; intro c3 hc3
  exact (excessWeight_mono (by omega : max c2 c3 ≤ 65535)).trans excessWeight_field_max

theorem expandExcessNumeric_holds : ExpandExcessNumeric :=
  expandExcessNumeric19_holds.trans (by
    rw [show (2 : ENNReal) = ENNReal.ofReal 2 by norm_num]
    exact ENNReal.ofReal_le_ofReal (by norm_num))

end SigGolfCandidate.Research.SharedExpansionV6
end
