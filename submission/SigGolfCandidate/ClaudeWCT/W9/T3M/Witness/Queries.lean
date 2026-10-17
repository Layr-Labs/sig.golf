import SigGolfCandidate.T3.FullCache.SourcePrelude
import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.Honest
import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.VerifyP

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
  allQ_foldlM _ _ (fun _ _ => pubGood_shortHash _ (by simp [wctChainInputP, bytesLE_length])) _
theorem pubGood_chain (index coord child t start count : Nat) (v : Digest) :
    AllQueriesSatisfy (WCT9.chain index coord child t start count v) PubGood :=
  allQ_foldlM _ _ (fun _ _ => pubGood_shortHash _ (by simp [WCT9.chainInput, bytesLE_length, zero16])) _
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
  exact allQ_topDecodeRun _ _ _ (fun _ _ => SigGolfCandidate.T3M.pubGood_chain _ _ _ _ _ _ _) fun _ =>
    allQ_bind (SigGolfCandidate.T3M.pubGood_leafHash _ _ _ _) fun _ =>
      allQ_foldlM _ _ (fun _ _ => pubGood_nodeHash _ _ _ _ _ _) _
theorem pubGood_verifyTopP (sig : WCT9.Signature) (pads : Pads) (index : Nat) (answer : Digest) :
    AllQueriesSatisfy (verifyTopP sig pads index answer) PubGood := by
  unfold verifyTopP
  exact allQ_topDecodeRun _ _ _ (fun _ _ => pubGood_chainP _ _ _ _ _ _ _ _ _ _) fun _ =>
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
      exact allQ_map _ (allQ_mapM _ _ fun _ => pubGood_chainP _ _ _ _ _ _ _ _ _ _)
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
  exact allQ_bind (allQ_mapM _ _ fun _ => SigGolfCandidate.T3M.pubGood_chain _ _ _ _ _ _ _) fun _ =>
    allQ_bind (SigGolfCandidate.T3M.pubGood_leafHash _ _ _ _) fun _ =>
      allQ_foldlM _ _ (fun _ _ => pubGood_nodeHash _ _ _ _ _ _) _
theorem pubGood_topNode (index : Nat) (v o : Digest) : AllQueriesSatisfy (WCT9.topNode index v o) PubGood := by
  unfold WCT9.topNode
  exact pubGood_nodeHash _ _ _ _ _ _
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
    refine public_bind (public_encodingHash _ _) fun result => ?_
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
    rcases result with _ | ⟨counter,digits⟩
    · exact public_pure _
    · dsimp only
      split
      · exact public_bind (public_topFold _ _ _) fun _ =>
          public_bind (public_topNode _ _ _) fun _ => public_pure _
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
    exact allQ_mapM _ _ fun _=>allQ_foldlM _ _ (fun _ _=>public_shortHash _) _
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
#print axioms publicOnly_verifyP
#print axioms publicOnly_expandB
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
      · exact good_bind (good_topFold _ _ _) fun _ =>
          good_bind (good_topNode _ _ _) fun _ => good_pure _
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
    exact allQ_mapM _ _ fun _=>allQ_foldlM _ _ (fun _ _=>good_shortHash _ (by simp [V3.chainInput,V3.leafInput,SharedV3.childInput,V3.nodeInput,SphincsSecurity.bytesLE_length])) _
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
#print axioms goodQ_verifyP
#print axioms goodQ_expandB
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

theorem good_topCoefs (leaf : Nat) : Good (topCoefs leaf) :=
  good_foldlM _ _ (fun _ _=>good_bind (good_privatePair ..) fun _=>good_pure _) _

theorem good_buildLeafTop (leaf : Nat) (digits : List Nat) : Good (buildLeafTop leaf digits true) := by
  unfold buildLeafTop
  simp only [↓reduceIte]
  refine good_bind (good_topCoefs _) fun _=>?_
  refine good_bind (good_foldlM _ _ (fun _ _=>good_bind
    (allQ_mono (SigGolfCandidate.T3M.pubGood_chain ..) fun _ h=>h.2) fun _=>good_pure _) _) fun _=>good_pure _

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
    refine allQ_ite _ (allQ_mono (ClaudeWCT.W9.T3M.pubGood_verifyTop ..) fun _ h=>h.2) ?_
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
  rw [←ClaudeWCT.W9.T3M.Paired.expandN_snd]
  exact good_map _ (ClaudeWCT.W9.T3M.Paired.goodQ_expandN ..)
end SigGolfCandidate.Research.SharedForest

