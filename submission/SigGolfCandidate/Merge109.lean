import SigGolfCandidate.Merge010
import SigGolfCandidate.Merge033
import SigGolfCandidate.Merge045
import SigGolfCandidate.Merge053
import SigGolfCandidate.Merge057
import SigGolfCandidate.Merge058
import SigGolfCandidate.Merge105
import SigGolfCandidate.Merge107
import SigGolfCandidate.Merge108

-- ==== merged from T3_Secc_LargeCouplingKeygen ====
section

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
  SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree)
open LargeResidual CanonGraph CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] buildFts buildTree keygen
noncomputable local instance instDecidableEqCache_largeCouplingKeygen : DecidableEq T3.Cache := Classical.decEq _
noncomputable def keyValues (vals : Coord → Digest) : Coord → Digest :=
  lookupVal (keygenDisclosed.map fun c => (c, vals c))
theorem treeChild_top_some (level node : Nat) (hl : 0 ≤ level) (hl' : level ≤ 12) (hn : node < 2 ^ (12 - level)) :
    ∃ c, treeChild 0 0 level node = some c := by
  by_cases hz : level=0
  · subst level
    have hn' : node < 4096 := by simpa using hn
    simp only [treeChild,ite_true,dif_pos hn']
    exact ⟨_,rfl⟩
  unfold treeChild treeNodeAt
  rw [if_neg hz]
  have h1 : level - 1 < height 0 := by simp [height]; omega
  have h2 : node < 2 ^ (height 0 - (level - 1) - 1) := by
    have : height 0 - (level - 1) - 1 = 12 - level := by simp [height]; omega
    rw [this]; exact hn
  rw [dif_pos ⟨h1, h2⟩]
  exact ⟨_, rfl⟩
theorem treeChild_mem_keygen (level node : Nat) (hl : 0 ≤ level) (hl' : level ≤ 12) (hn : node < 2 ^ (12 - level))
    (c : Coord) (hc : treeChild 0 0 level node = some c) : c ∈ keygenDisclosed := by
  unfold keygenDisclosed
  simp only [List.mem_flatMap, List.mem_range'_1, List.mem_filterMap, List.mem_range]
  exact ⟨level, ⟨by omega, by omega⟩, node, hn, hc⟩
theorem cacheRegion_congr (f g : Nat → Nat → Digest)
    (h : ∀ level node, 0 ≤ level → level < 12 → node < 2 ^ (12 - level) → f level node = g level node) :
    Correctness.cacheRegion f = Correctness.cacheRegion g := by
  have hw : Correctness.cacheWordList f = Correctness.cacheWordList g := by
    unfold Correctness.cacheWordList
    apply List.flatMap_congr
    intro level hlevel
    rw [List.mem_range'_1] at hlevel
    apply List.map_congr_left
    intro node hnode
    exact h level node (by omega) (by omega) (List.mem_range.mp hnode)
  unfold Correctness.cacheRegion
  rw [hw]
section Keygen
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData}
theorem Coherent.private_header (hcoh : Coherent U T vals nv τ a)
    (tag level node : Nat) (h0 : tag%256 ≠ 0) (h8 : tag%256 ≠ 8) :
    T (.inr (.inl (header tag 0 0 level node))) = a.priv (.inl (header tag 0 0 level node)) := by
  apply hcoh.priv
  · intro i hi
    obtain ⟨s, hs⟩ := hi
    have hp := congrArg Prod.fst hs
    cases s with
    | inl x =>
        change Sum.inl (header 0 _ _ _ _) = (Sum.inl (header tag 0 0 level node) : Coordinate) at hp
        exact QuerySpace.header_ne_of_tag (Ne.symm h0) (Sum.inl.inj hp)
    | inr f =>
        change Sum.inl (header 8 _ _ _ _) = (Sum.inl (header tag 0 0 level node) : Coordinate) at hp
        exact QuerySpace.header_ne_of_tag (Ne.symm h8) (Sum.inl.inj hp)
  · intro m h
    cases h
theorem Coherent.mask_eq (hcoh : Coherent U T vals nv τ a) (level node : Nat) :
    maskOf a level node = evalWithAnswerFn T (T3.mask level node) := by
  have hp := hcoh.private_header 13 level (node/2) (by decide) (by decide)
  unfold maskOf T3.mask pairedMask privatePair privateHash
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rw [← hp]
  rfl
theorem Coherent.mac_eq (hcoh : Coherent U T vals nv τ a) (region : Region) :
    macOf a region = evalWithAnswerFn T (T3.privateMac region) := by
  have hk : (fun i : Fin 2 => a.priv (.inl (header 14 0 0 0 i.val))) =
      (fun i : Fin 2 => if i=0 then T (.inr (.inl (header 14 0 0 0 0)))
        else T (.inr (.inl (header 14 0 0 0 1)))) := by
    funext i
    fin_cases i <;> simp [hcoh.private_header 14 0 0 (by decide) (by decide),
      hcoh.private_header 14 0 1 (by decide) (by decide)]
  unfold macOf T3.privateMac T3.privateMacKey privateHash
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rw [hk]
  rfl
end Keygen
end SigGolfCandidate.T3.Security.LargeCoupling
end
-- ==== merged from T3_Secc_LargeCouplingShort ====
section

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
  SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual CanonGraph CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_largeCouplingShort : DecidableEq T3.Cache := Classical.decEq _
section Short
variable {A T : Answers} (hAT : Wots.Ref.ShortAgree A T)
include hAT
theorem publicHash_respects (input : HashInput) (h : (pad64 input).length ≤ SeccLaw.maxInputLength) :
    Wots.Ref.ShortRespects (publicHash input) := by
  intro A' T' hAT'
  unfold publicHash
  change A' (.inl (.inr (pad64 input))) = T' (.inl (.inr (pad64 input)))
  exact hAT'.public _ h
end Short
end SigGolfCandidate.T3.Security.LargeCoupling
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_LargeCouplingShort ====
section

section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (State Cell runWith_bind)
open ClaudeWCT.W9.T3.Security.FamResidual (observedRun)
open SigGolfCandidate.T3.Security.LargeCoupling (cacheRegion_congr)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
attribute [local irreducible] buildFts buildTree keygen
noncomputable local instance instDecidableEqCache_w9largeCouplingKeygen : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
noncomputable def keyValues (vals : Coord → Digest) : Coord → Digest :=
  lookupVal (keygenDisclosed.map fun c => (c, vals c))
theorem treeChild_top_some (level node : Nat) (hl : 0 ≤ level) (hl' : level ≤ 12) (hn : node < 2 ^ (12 - level)) :
    ∃ c, treeChild 0 0 level node = some c := by
  by_cases hz : level=0
  · subst level
    have hn' : node < 2 ^ height 0 := by simpa [height] using hn
    simp only [treeChild, ite_true]
    unfold leafAt
    rw [dif_pos ⟨hn', by decide⟩]
    exact ⟨_, rfl⟩
  unfold treeChild treeNodeAt
  rw [if_neg hz]
  have h1 : level - 1 < height 0 := by simp [height]; omega
  have h2 : node < 2 ^ (height 0 - (level - 1) - 1) := by
    have : height 0 - (level - 1) - 1 = 12 - level := by simp [height]; omega
    rw [this]; exact hn
  rw [dif_pos ⟨h1, h2, by decide, Or.inl rfl⟩]
  exact ⟨_, rfl⟩
theorem treeChild_mem_keygen (level node : Nat) (hl : 0 ≤ level) (hl' : level ≤ 12) (hn : node < 2 ^ (12 - level))
    (c : Coord) (hc : treeChild 0 0 level node = some c) : c ∈ keygenDisclosed := by
  apply List.mem_append_left
  apply List.mem_append_left
  unfold keygenCacheDisclosed
  simp only [List.mem_flatMap, List.mem_range'_1, List.mem_filterMap, List.mem_range]
  exact ⟨level, ⟨by omega, by omega⟩, node, hn, hc⟩
section Keygen
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData}
theorem rootNode_coord : treeChild 0 0 12 0 = some (.inl (.node rootNode)) := by
  unfold treeChild treeNodeAt
  rw [if_neg (by decide), dif_pos (by simp [height])]
  rfl
end Keygen
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeCoupling (publicHash_respects)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeCouplingShort : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
section Short
variable {A T : Answers} (hAT : Wots.Ref.ShortAgree A T)
include hAT
end Short
end ClaudeWCT.W9.T3.Security.LargeCoupling
end

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open CanonGraph
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9pairedShort : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _

theorem honestInput_short_all {A T : Answers} (hAT : Wots.Ref.ShortAgree A T)
    (position : Extract.Pos) (hb : position.Bounded) :
    Extract.Paired.honestInput A position = Extract.Paired.honestInput T position := by
  cases position with
  | chain | leaf | node | wctChain | forest => exact Wots.Ref.honestInput_short hAT _ hb
  | wctLeaf index coord child =>
      obtain ⟨hi,hc,hch⟩ := hb
      simp only [Extract.Paired.honestInput]
      rw [Wots.PairedReference.pads_short hAT index coord _ hc,Wots.Ref.wctEnds_short hAT index coord child hc hch]
  | wctNode index coord level node =>
      have hc := hb.2.1
      simp only [Extract.Paired.honestInput]
      rw [Wots.PairedReference.nodes_short hAT index coord hc,Wots.PairedReference.pads_short hAT index coord _ hc]
section Short
variable {A T : Answers} (hAT : Wots.Ref.ShortAgree A T)
include hAT
theorem secretsOf_short : CanonGraph.secretsOf A = CanonGraph.secretsOf T := by
  funext s
  change CanonGraph.halfAnswer A (CanonGraph.secretCoordinate s) = CanonGraph.halfAnswer T (CanonGraph.secretCoordinate s)
  unfold CanonGraph.halfAnswer
  rw [hAT.priv]
theorem honestValue_short : LargeResidual.Paired.honestValue A = LargeResidual.Paired.honestValue T := by
  funext c
  cases c with
  | inl N =>
      change Extract.Paired.proj N.toPos (A (.inl (.inr (Extract.Paired.honestInput A N.toPos)))) =
        Extract.Paired.proj N.toPos (T (.inl (.inr (Extract.Paired.honestInput T N.toPos))))
      rw [honestInput_short_all hAT _ (toPos_bounded N),
        hAT.public _ (Wots.PairedReference.honestInput_length T N.toPos)]
  | inr s =>
      change seedView (CanonGraph.secretsOf A) s = seedView (CanonGraph.secretsOf T) s
      rw [secretsOf_short hAT]
theorem contactTest_short (K : Coord → Prop) (X : HashInput) (y : HashOutput) :
    LargeResidual.Paired.ContactTest A K X y ↔ LargeResidual.Paired.ContactTest T K X y := by
  have hin : ∀ N : CanonGraph.Node, Extract.Paired.honestInput A N.toPos = Extract.Paired.honestInput T N.toPos :=
    fun N => honestInput_short_all hAT _ (toPos_bounded N)
  have hns : Wots.CanonicalRef.NotSearched A (Wots.CanonicalRef.sourceMessages A) =
      Wots.CanonicalRef.NotSearched T (Wots.CanonicalRef.sourceMessages T) := by
    funext L' x
    unfold Wots.CanonicalRef.NotSearched
    rw [Wots.CanonicalRef.referenceSearch_short hAT, Wots.CanonicalRef.sourceMessages_short hAT]
  unfold LargeResidual.Paired.ContactTest LargeResidual.Paired.StructuralContact LargeResidual.Paired.EncodingContact
  simp only [honestValue_short hAT, hin, Wots.CanonicalRef.referenceSearch_short hAT, Wots.CanonicalRef.referenceInput_short hAT, Wots.CanonicalRef.referenceDigits_short hAT, hns]
theorem digestSearch_short (rho : Digest) (m : Message) :
    ∀ fuel c, evalWithAnswerFn A (SigGolfCandidate.Research.SharedForest.sharedDigestSearch rho m c fuel) = evalWithAnswerFn T (SigGolfCandidate.Research.SharedForest.sharedDigestSearch rho m c fuel) := by
  intro fuel
  induction fuel with
  | zero => intro c; rfl
  | succ fuel ih =>
      intro c
      simp only [SigGolfCandidate.Research.SharedForest.sharedDigestSearch, digest, evalWithAnswerFn_bind]
      have hlen : (pad64 (digestInput rho m (BitVec.ofNat 32 c))).length ≤ SeccLaw.maxInputLength := by
        rw [BPB.pad64_digestInput, BPB.digestInput_length]
        unfold SeccLaw.maxInputLength
        omega
      have hh : evalWithAnswerFn A (publicHash (digestInput rho m (BitVec.ofNat 32 c))) =
          evalWithAnswerFn T (publicHash (digestInput rho m (BitVec.ofNat 32 c))) := hAT.public _ hlen
      rw [hh]
      split_ifs
      · rfl
      · exact ih (c + 1)
theorem signDigest_short (m : Message) : LargeResidual.Paired.signDigest A m = LargeResidual.Paired.signDigest T m := by
  unfold LargeResidual.Paired.signDigest
  have hn : evalWithAnswerFn A (SigGolfCandidate.T3.privateNonce m) = evalWithAnswerFn T (SigGolfCandidate.T3.privateNonce m) := by
    simp only [SigGolfCandidate.T3.privateNonce, privateHash, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
    change (A (.inr (.inr (.inl m)))).extractLsb' 0 128 = (T (.inr (.inr (.inl m)))).extractLsb' 0 128
    rw [hAT.priv]
  rw [hn]
  exact digestSearch_short hAT _ _ _ _
theorem signDisclosed_short (published : SigGolfCandidate.T3.Cache) (request : Security.Request) :
    LargeResidual.Paired.signDisclosed A published request = LargeResidual.Paired.signDisclosed T published request := by
  have hd : Wots.CanonicalRef.referenceDigits A (Wots.CanonicalRef.sourceMessages A) = Wots.CanonicalRef.referenceDigits T (Wots.CanonicalRef.sourceMessages T) := funext (Wots.CanonicalRef.referenceDigits_short hAT)
  have hok : ∀ index, LargeResidual.Paired.RouteOk A index ↔ LargeResidual.Paired.RouteOk T index := by
    intro index
    unfold LargeResidual.Paired.RouteOk
    simp only [Wots.CanonicalRef.referenceSearch_short hAT]
  unfold LargeResidual.Paired.signDisclosed LargeResidual.Paired.signItems
  rw [signDigest_short hAT, hd]
  split_ifs
  · rcases LargeResidual.Paired.signDigest T request.message with _ | ⟨c, N⟩
    · rfl
    · simp only [hok]
  · rfl
theorem query_short (U : Finset HashInput) (q : Nat) (mon : Monitor) (X : HashInput) (y : HashOutput) :
    mon.query U A q X y = mon.query U T q X y := by
  unfold Monitor.query
  simp only [contactTest_short hAT]
theorem event_short (U : Finset HashInput) (q : Nat) (mon : Monitor) (e : FirstHit.QueryEvent) :
    mon.event U A q e = mon.event U T q e := by
  rcases e with ⟨before, (n | X) | c, answer⟩
  · rfl
  · exact query_short hAT U q mon X answer
  · rfl
theorem events_short (U : Finset HashInput) (q : Nat) (events : List FirstHit.QueryEvent) (mon : Monitor) :
    events.foldl (Monitor.event U A q) mon = events.foldl (Monitor.event U T q) mon := by
  induction events generalizing mon with
  | nil => rfl
  | cons e rest ih => rw [List.foldl_cons, List.foldl_cons, event_short hAT, ih]
theorem steps_short (U : Finset HashInput) (q : Nat) (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep) (mon : Monitor) :
    steps.foldl (Monitor.step U A q published) mon = steps.foldl (Monitor.step U T q published) mon := by
  induction steps generalizing mon with
  | nil => rfl
  | cons s rest ih =>
      rw [List.foldl_cons, List.foldl_cons]
      have h1 : Monitor.step U A q published mon s = Monitor.step U T q published mon s := by
        cases s with
        | world e => exact event_short hAT U q mon e
        | sign request out events =>
            simp only [Monitor.step, Monitor.sign, signDisclosed_short hAT]
      rw [h1, ih]
theorem monitorRun_short (U : Finset HashInput) (q : Nat) (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep)
    (verdict : List FirstHit.QueryEvent) :
    monitorRun U A q published steps verdict = monitorRun U T q published steps verdict := by
  unfold monitorRun
  rw [steps_short hAT, events_short hAT]
end Short
def ContactR (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (result : FirstHit.Recorded Bool) (A : Answers) : Prop :=
  ∀ generated tagged checked, TaggedSplit adversary result generated tagged checked →
    (monitorRun (Wots.PairedReference.referenceInputs adversary) A q generated.value.2 tagged.steps checked.events).contact = true
theorem contactR_short {A T : Answers} (hAT : Wots.Ref.ShortAgree A T) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat)
    (result : FirstHit.Recorded Bool) : ContactR adversary q result A ↔ ContactR adversary q result T := by
  unfold ContactR
  simp only [monitorRun_short hAT]
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree)
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord treeChild topValue keygenDisclosed keygenCacheDisclosed encodingDisclosed lookupVal)
open ClaudeWCT.W9.T3.Security.LargeCoupling (keyValues treeChild_top_some treeChild_mem_keygen rootNode_coord)
open SigGolfCandidate.T3.Security.LargeResidual (State Cell runWith_bind)
open ClaudeWCT.W9.T3.Security.FamResidual (observedRun)
open SigGolfCandidate.T3.Security.LargeCoupling (cacheRegion_congr)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
attribute [local irreducible] buildFts buildTree keygen
noncomputable local instance instDecidableEqCache_w9largeCouplingKeygen : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
section Keygen
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData}
theorem _root_.ClaudeWCT.W9.T3.Security.LargeResidual.Paired.Coherent.topValue_eq (hcoh : LargeResidual.Paired.Coherent U T vals nv τ a) (level node : Nat) (hl : 0 ≤ level) (hl' : level < 12)
    (hn : node < 2 ^ (12 - level)) : topValue (keyValues vals) level node = treeValue (builtTree T 0 0) level node := by
  obtain ⟨c, hc⟩ := treeChild_top_some level node (by omega) (by omega) hn
  have hmem := treeChild_mem_keygen level node hl (by omega) hn c hc
  have hb := CanonGraph.Paired.builtTree_eq (CanonGraph.Paired.Filtered.completeLabels_agrees hcoh.agrees) 0 ⟨0, by decide⟩ level node (by simp [height]; omega)
    (by simpa [height] using hn) (by decide) (Or.inl rfl)
  change _ = treeValue (builtTree T 0 (⟨0, by decide⟩ : Fin (2 ^ 31)).val) level node
  rw [← WCT9.wotsTree_top, hb, CanonGraph.Paired.Filtered.treeLabel_complete, LargeResidual.Paired.treeLabel_eq (secretsOf T), hcoh.coordVal]
  have hk : ∀ y ∈ keygenDisclosed, keyValues vals y = vals y := fun y hy => lookupVal_map vals keygenDisclosed y hy
  unfold LargeResidual.topValue
  apply ClaudeWCT.W9.T3.Security.LargeResidual.treeVal_congr
  · intro x hx
    have hx' : treeChild 0 0 level node = some x := by simpa using hx
    exact ClaudeWCT.W9.T3.Security.LargeResidual.treeChild_sel_agree hx'
      (hk x (treeChild_mem_keygen level node hl (by omega) hn x hx'))
      (fun y hy => hk y (ClaudeWCT.W9.T3.Security.LargeResidual.Paired.childTrialDeps_keygen hy))
  · intro y hy
    exact hk y (ClaudeWCT.W9.T3.Security.LargeResidual.Paired.childTrialDeps_keygen hy)
theorem _root_.ClaudeWCT.W9.T3.Security.LargeResidual.Paired.Coherent.private_header (hcoh : LargeResidual.Paired.Coherent U T vals nv τ a)
    (tag level node : Nat) (h0 : tag%256 ≠ 0) (h8 : tag%256 ≠ 8) :
    T (.inr (.inl (header tag 0 0 level node))) = a.priv (.inl (header tag 0 0 level node)) := by
  apply hcoh.priv
  · intro i hi
    obtain ⟨s, hs⟩ := hi
    have hp := congrArg Prod.fst hs
    cases s with
    | inl x =>
        simp only [CanonGraph.secretCoordinate, Sum.elim_inl, CanonGraph.seedCoordinateP] at hp
        split_ifs at hp
        · change Sum.inl (header 0 _ _ _ _) = (Sum.inl (header tag 0 0 level node) : Coordinate) at hp
          exact QuerySpace.header_ne_of_tag (Ne.symm h0) (Sum.inl.inj hp)
        · change Sum.inl (header 0 _ _ _ _) = (Sum.inl (header tag 0 0 level node) : Coordinate) at hp
          exact QuerySpace.header_ne_of_tag (Ne.symm h0) (Sum.inl.inj hp)
    | inr f =>
        change Sum.inl (header 8 _ _ _ _) = (Sum.inl (header tag 0 0 level node) : Coordinate) at hp
        exact QuerySpace.header_ne_of_tag (Ne.symm h8) (Sum.inl.inj hp)
  · intro m h
    cases h
theorem _root_.ClaudeWCT.W9.T3.Security.LargeResidual.Paired.Coherent.mask_eq (hcoh : LargeResidual.Paired.Coherent U T vals nv τ a) (level node : Nat) :
    maskOf a level node = evalWithAnswerFn T (SigGolfCandidate.T3.mask level node) := by
  have hp := hcoh.private_header 13 level (node/2) (by decide) (by decide)
  unfold maskOf SigGolfCandidate.T3.mask pairedMask privatePair privateHash
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rw [← hp]
  rfl
theorem _root_.ClaudeWCT.W9.T3.Security.LargeResidual.Paired.Coherent.mac_eq (hcoh : LargeResidual.Paired.Coherent U T vals nv τ a) (region : Region) :
    macOf a region = evalWithAnswerFn T (SigGolfCandidate.T3.privateMac region) := by
  have hk : (fun i : Fin 2 => a.priv (.inl (header 14 0 0 0 i.val))) =
      (fun i : Fin 2 => if i=0 then T (.inr (.inl (header 14 0 0 0 0)))
        else T (.inr (.inl (header 14 0 0 0 1)))) := by
    funext i
    fin_cases i <;> simp [hcoh.private_header 14 0 0 (by decide) (by decide),
      hcoh.private_header 14 0 1 (by decide) (by decide)]
  unfold macOf SigGolfCandidate.T3.privateMac SigGolfCandidate.T3.privateMacKey privateHash
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rw [hk]
  rfl
theorem _root_.ClaudeWCT.W9.T3.Security.LargeResidual.Paired.Coherent.region (hcoh : LargeResidual.Paired.Coherent U T vals nv τ a) :
    Correctness.cacheRegion (fun level node => topValue (keyValues vals) level node ^^^ maskOf a level node) =
      Correctness.cacheRegion (Correctness.maskedTop T) := by
  apply cacheRegion_congr
  intro level node hl hl' hn
  rw [hcoh.topValue_eq level node hl hl' hn, hcoh.mask_eq]
  rfl
theorem _root_.ClaudeWCT.W9.T3.Security.LargeResidual.Paired.Coherent.pk (hcoh : LargeResidual.Paired.Coherent U T vals nv τ a) :
    keyValues vals (.inl (.node rootNode)) = (evalWithAnswerFn T keygen).1 := by
  rw [show (evalWithAnswerFn T keygen).1 = Extract.honestRoot T 0 0 from Extract.keygen_pk T,
    CanonGraph.Paired.honestRoot_label (CanonGraph.Paired.Filtered.completeLabels_agrees hcoh.agrees)]
  have hmem := treeChild_mem_keygen 12 0 (by decide) le_rfl (by decide) _ rootNode_coord
  unfold keyValues
  rw [lookupVal_map vals keygenDisclosed _ hmem]
  rw [CanonGraph.Paired.Filtered.completeLabels_used T _ (.node rootNode) (by trivial)]
  exact (CanonGraph.Paired.joinLabels_low (low := fun N => vals (.inl N)) (high := a.high) rfl).symm
theorem _root_.ClaudeWCT.W9.T3.Security.LargeResidual.Paired.Coherent.published (hcoh : LargeResidual.Paired.Coherent U T vals nv τ a) :
    (⟨macOf a (Correctness.cacheRegion fun level node =>
        topValue (keyValues vals) level node ^^^ maskOf a level node),
      Correctness.cacheRegion fun level node => topValue (keyValues vals) level node ^^^ maskOf a level node⟩ :
        SigGolfCandidate.T3.Cache) = (evalWithAnswerFn T keygen).2 := by
  obtain ⟨-, hreg, htag⟩ := Correctness.keygen_correct T
  rw [hcoh.region, hcoh.mac_eq]
  unfold Correctness.CacheTagCorrect at htag
  cases hk : (evalWithAnswerFn T keygen).2 with
  | mk tag region =>
      rw [hk] at hreg htag
      simp only at hreg htag
      subst hreg
      rw [htag]
end Keygen
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
end
end
-- ==== merged from T3_Secc_LargeCouplingTable ====
section

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
  SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual CanonGraph CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen
noncomputable local instance instDecidableEqCache_largeCouplingTable : DecidableEq T3.Cache := Classical.decEq _
section Table
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData} {q : Nat}
theorem keygen_record (T : Answers) :
    Wots.Ref.pureRecord T keygen (∅, ∅) ∈ support (FirstHit.record keygen (∅, ∅)) ∧
      Wots.Ref.Agrees T (Wots.Ref.pureRecord T keygen (∅, ∅)).state := by
  apply Wots.Ref.fixedRecord_mem_record T keygen (∅, ∅) (Wots.Ref.agrees_empty T)
  rw [Wots.Ref.fixedRecord_hashOnly T keygen SourceReplay.keygen_hashOnly, mem_support_pure_iff]
end Table
end SigGolfCandidate.T3.Security.LargeCoupling
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_LargeFamZeros ====
section

/-! # Large route, family level: zero sets of a family (r3-lean-seedfam, family port P7, additive)

The large route bounds, per seed family, the seeds the router can have disclosed (`FamOK`: at most `deg = size − 1`).
Today (one family per leaf) this is `LargeCouplingTable.lowerZeros_card`. For grouped families (v6 flip) the revealed
seeds of a family are the union of the revealed seeds of its REAL member leaves (`leaf < 2 ^ height`), so the bound is
`zcap · members + 3 ≤ famSize` with `members = min famGrp (2 ^ height − famGrp · f)` (short last family included).

`famZeros_card_le`: the counting step, for any per-address predicate `Z` with a per-leaf cap. -/

namespace ClaudeWCT.W9.T3.Security.CanonGraph
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false

/-- Real member leaves of family `f` of layer `lay` (the last family of a tree may be short). -/
def famMembersL (lay : Layer) (f : Nat) : Nat := min (WCT9.famGrp lay) (2 ^ height lay - WCT9.famGrp lay * f)

/-- A real leaf of family `f` is `famGrp · f + r` with `r < famMembersL lay f`. -/
theorem leaf_decomp {lay : Layer} {leaf : Nat} (hreal : leaf < 2 ^ height lay) :
    leaf = WCT9.famGrp lay * WCT9.famOf lay leaf + leaf % WCT9.famGrp lay ∧
      leaf % WCT9.famGrp lay < famMembersL lay (WCT9.famOf lay leaf) := by
  have hg := WCT9.famGrp_pos lay
  have e := Nat.div_add_mod leaf (WCT9.famGrp lay)
  have hm : leaf % WCT9.famGrp lay < WCT9.famGrp lay := Nat.mod_lt _ hg
  refine ⟨by unfold WCT9.famOf; omega, ?_⟩
  unfold famMembersL
  refine lt_min hm ?_
  unfold WCT9.famOf
  omega

/-- **Family zero count.** If every set of addresses of one real leaf satisfying `Z` has at most `zcap lay` elements,
every set of addresses of family `f` (real leaves) satisfying `Z` has at most `zcap lay · famMembersL lay f`. -/
theorem famZeros_card_le (Z : ChainGraph.Address → Prop) (zcap : Layer → Nat)
    (hleaf : ∀ (lay : Layer) (tree : Fin (2 ^ 31)) (n : Nat), n < 2 ^ height lay → ∀ S : Finset ChainGraph.Address,
      (∀ a ∈ S, a.layer = lay ∧ a.tree = tree ∧ a.leaf.val = n ∧ Z a) → S.card ≤ zcap lay)
    (lay : Layer) (tree : Fin (2 ^ 31)) (f : Fin 4096) (S : Finset ChainGraph.Address)
    (hS : ∀ a ∈ S, (a.layer, a.tree, famSlot a.layer a.leaf) = (lay, tree, f) ∧ a.leaf.val < 2 ^ height a.layer ∧ Z a) :
    S.card ≤ zcap lay * famMembersL lay f.val := by
  classical
  set m := famMembersL lay f.val
  have hsub : S ⊆ (Finset.range m).biUnion fun r => S.filter fun a => a.leaf.val = WCT9.famGrp lay * f.val + r := by
    intro a ha
    obtain ⟨hlf, hreal, -⟩ := hS a ha
    simp only [Prod.mk.injEq] at hlf
    obtain ⟨hl, -, hf⟩ := hlf
    have hf' : WCT9.famOf a.layer a.leaf.val = f.val := congrArg Fin.val hf
    obtain ⟨e, hr⟩ := leaf_decomp hreal
    rw [hf', hl] at hr
    rw [hf', hl] at e
    rw [Finset.mem_biUnion]
    exact ⟨a.leaf.val % WCT9.famGrp lay, Finset.mem_range.mpr hr, Finset.mem_filter.mpr ⟨ha, e⟩⟩
  refine (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans ?_)
  calc ∑ r ∈ Finset.range m, (S.filter fun a => a.leaf.val = WCT9.famGrp lay * f.val + r).card
      ≤ ∑ _r ∈ Finset.range m, zcap lay := by
        refine Finset.sum_le_sum fun r hr => hleaf lay tree (WCT9.famGrp lay * f.val + r) ?_ _ fun a ha => ?_
        · have hr' : r < m := Finset.mem_range.mp hr
          have : r < 2 ^ height lay - WCT9.famGrp lay * f.val := lt_of_lt_of_le hr' (min_le_right _ _)
          omega
        · obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
          obtain ⟨hlf, -, hz⟩ := hS a ha1
          simp only [Prod.mk.injEq] at hlf
          exact ⟨hlf.1, hlf.2.1, ha2, hz⟩
    _ = zcap lay * m := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_comm]

/-- Today: every family has exactly one real member when its leaf is real. -/
theorem famMembersL_le_grp (lay : Layer) (f : Nat) : famMembersL lay f ≤ WCT9.famGrp lay := min_le_left _ _

end ClaudeWCT.W9.T3.Security.CanonGraph
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_LargeCouplingTable ====
section

namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (State Cell runWith_bind)
open ClaudeWCT.W9.T3.Security.FamResidual (observedRun)
open SigGolfCandidate.T3.Security.LargeCoupling (keygen_record)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen
noncomputable local instance instDecidableEqCache_w9largeCouplingTable : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
section Table
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData} {q : Nat}
end Table
section Overflow
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData}
theorem idx_zero_card (l : List ℕ) :
    ((Finset.range l.length).filter fun i => l.getD i 0 = 0).card = (l.filter (· = 0)).length := by
  induction l with
  | nil => simp
  | cons x t ih =>
      rw [Finset.card_filter, List.length_cons, Finset.sum_range_succ']
      rw [Finset.card_filter] at ih
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      rw [ih]
      by_cases hx : x = 0
      · simp [List.filter_cons, hx]
      · simp [List.filter_cons, hx]
end Overflow
end ClaudeWCT.W9.T3.Security.LargeCoupling


namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord WCoord keygenDisclosed keygenCacheDisclosed lookupVal digestIndex LowerLeaf chainItem layerItems layerPath layerChains treeChild wctItem)
open ClaudeWCT.W9.T3.Security.LargeCoupling (keyValues idx_zero_card)
open SigGolfCandidate.T3.Security.LargeResidual (State Cell runWith_bind)
open ClaudeWCT.W9.T3.Security.FamResidual (observedRun)
open SigGolfCandidate.T3.Security.LargeCoupling (keygen_record)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen
noncomputable local instance instDecidableEqCache_w9largeCouplingTable_initial : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
section Table
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData} {q : Nat}
noncomputable def keyState (U : Finset HashInput) (q : Nat) (vals : Coord → Digest) (nv : Message → Digest) :
    LargeResidual.State WCoord (Cell U) :=
  discloseStates U q (Sum.elim vals nv) LargeResidual.initial keygenDisclosed
theorem rel_initial :
    Rel U T vals nv τ a q Monitor.initial LargeResidual.RouterState.initial (keyState U q vals nv) := by
  have hc := discloseStates_counters (U := U) (q := q) (vals := vals) (nv := nv) keygenDisclosed
    (LargeResidual.initial : LargeResidual.State WCoord (Cell U))
  have hr := discloseStates_rows (U := U) (q := q) (vals := vals) (nv := nv) keygenDisclosed
    (LargeResidual.initial : LargeResidual.State WCoord (Cell U))
  unfold keyState
  refine ⟨rfl, rfl, rfl, by rw [hc]; rfl, by rw [hc]; rfl, rfl, by rw [hc]; exact le_rfl, Nat.zero_le _, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro c
    rw [discloseStates_candidates]
    split_ifs
    · exact Finset.mem_singleton_self _
    · exact Finset.mem_univ _
  · intro c hck
    rw [discloseStates_candidates, if_neg, hc]
    · simp only [LargeResidual.initial, Finset.card_univ, Nat.sub_zero]
      simp [SphincsSecurity.digestBits]
    · intro hm
      obtain ⟨d, hd, hdc⟩ := List.mem_map.mp hm
      rw [Sum.inl.inj hdc] at hd
      exact hck (LargeResidual.Paired.Known.base (Or.inl hd))
  · intro row v hv
    rw [hr] at hv
    cases hv
  · intro row v hv
    rw [hr] at hv
    cases hv
  · intro X hX
    cases hX
  · intro X hX
    cases hX
theorem canonical_split (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (T : Answers)
    (t : Tagged (Option ClaudeWCT.W9.T3M.Final.Paired.ForgeryP))
    (ht : t ∈ support (taggedFixed T (evalWithAnswerFn T keygen).2
      (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2)
      (Wots.Ref.pureRecord T keygen (∅, ∅)).state)) :
    TaggedSplit adversary (Wots.PairedReference.Ref.combine T t.untag) (Wots.Ref.pureRecord T keygen (∅, ∅)) t
      (Wots.PairedReference.Ref.verdictRecord T t.untag) := by
  obtain ⟨hk, hka⟩ := keygen_record T
  have hval : (Wots.Ref.pureRecord T keygen (∅, ∅)).value = evalWithAnswerFn T keygen :=
    Wots.Ref.pureRecord_value T keygen (∅, ∅)
  obtain ⟨ht1, ht2⟩ := taggedFixed_support T _ _ _ hka t ht
  refine ⟨hk, by rw [hval]; exact ht1, ?_, rfl⟩
  have hv := Wots.Ref.fixedRecord_mem_record T
    (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker (evalWithAnswerFn T keygen).1 t.value) t.state ht2
    (Wots.PairedReference.Ref.verdictRecord T t.untag)
    (by rw [Wots.Ref.fixedRecord_hashOnly T _ (Wots.PairedReference.Ref.verdict_hashOnly _ _), mem_support_pure_iff]; rfl)
  rw [hval]
  exact hv.1
noncomputable def verdictContact (U : Finset HashInput) (T : Answers) (q : Nat) (pk : Digest) (mon : Monitor)
    (value : Option ClaudeWCT.W9.T3M.Final.Paired.ForgeryP × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) (state : LazyPrivate.State) : Prop :=
  ((Wots.Ref.pureRecord T (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker pk value) state).events.foldl
    (Monitor.event U T q) mon).contact = true
noncomputable def verdictCont (U : Finset HashInput) (a : AuxData) (q : Nat) (pk : Digest)
    (r : Option ((Option ClaudeWCT.W9.T3M.Final.Paired.ForgeryP × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) × RouterState)) :
    OracleComp (RWorld U) (Option (Bool × RouterState)) :=
  match r with
  | none => pure none
  | some (result, st) => routeVerdict U a q (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker pk result) st
theorem _root_.ClaudeWCT.W9.T3.Security.LargeResidual.Paired.Coherent.routerWith (hcoh : LargeResidual.Paired.Coherent U T vals nv τ a) (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input))
    (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) :
    observedRun aux q (Sum.elim vals nv) τ (routerWith U adversary q a) LargeResidual.initial =
      observedRun aux q (Sum.elim vals nv) τ
        (routeInteraction U a (evalWithAnswerFn T keygen).2 q
          (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2) LargeResidual.RouterState.initial >>=
            verdictCont U a q (evalWithAnswerFn T keygen).1) (keyState U q vals nv) := by
  unfold LargeResidual.Paired.routerWith
  rw [observed_discloseAll]
  have hkv : lookupVal (List.map (fun c => (c, Sum.elim vals nv (Sum.inl c))) keygenDisclosed) = keyValues vals :=
    rfl
  simp only [hkv]
  rw [hcoh.published, hcoh.pk]
  rfl
end Table

end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord WCoord keygenDisclosed keygenCacheDisclosed lookupVal digestIndex LowerLeaf chainItem layerItems layerPath layerChains treeChild wctItem)
open ClaudeWCT.W9.T3.Security.LargeCoupling (keyValues idx_zero_card)
open SigGolfCandidate.T3.Security.LargeResidual (State Cell runWith_bind)
open ClaudeWCT.W9.T3.Security.FamResidual (observedRun)
open SigGolfCandidate.T3.Security.LargeCoupling (keygen_record)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen
noncomputable local instance instDecidableEqCache_w9largeCouplingTable_families : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
def LogNoOverflow (T : Answers) (log : QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) : Prop :=
  ∀j : Fin (2^31),((WPair.Paired.loggedOutputs T log).toFinset.filter fun out => ClaudeWCT.Bank.WCT.outIdx out=j).card≤50
section Overflow
/-- FTS seeds of family `f` opened by the signatures of a log (digit 4 words open the seed; T8: at most one per word). -/
@[irreducible] noncomputable def logSeeds (T : Answers) (log : QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) (f : Fin (2 ^ 31) × Fin 9) :
    Finset CanonGraph.WctAddr :=
  Finset.univ.filter fun w => (w.1, w.2.1) = f ∧ ∃ N ∈ WPair.Paired.loggedOutputs T log, digestIndex N = w.1 ∧
    SigGolfCandidate.Research.SharedForest.rawChildFromOutput N w.2.1 = w.2.2.1 ∧ WCT9.wordDigit (SigGolfCandidate.Research.SharedForest.forestRank N w.2.1.val) w.2.2.2 = 4
theorem mem_logSeeds (T : Answers) (log : QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) (f : Fin (2 ^ 31) × Fin 9) (w : CanonGraph.WctAddr) :
    w ∈ logSeeds T log f ↔ (w.1, w.2.1) = f ∧ ∃ N ∈ WPair.Paired.loggedOutputs T log, digestIndex N = w.1 ∧
      SigGolfCandidate.Research.SharedForest.rawChildFromOutput N w.2.1 = w.2.2.1 ∧ WCT9.wordDigit (SigGolfCandidate.Research.SharedForest.forestRank N w.2.1.val) w.2.2.2 = 4 := by
  unfold logSeeds
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
theorem digitThree_card (r : WCT9.Rank) : (Finset.univ.filter fun t : Fin 6 => WCT9.wordDigit r t = 4).card ≤ 1 :=
  WCT9.f8_seedDisclosures_card_le _
theorem logSeeds_card (T : Answers) (log : QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) (hno : LogNoOverflow T log)
    (f : Fin (2 ^ 31) × Fin 9) : (logSeeds T log f).card ≤ 50 := by
  set S := (WPair.Paired.loggedOutputs T log).toFinset.filter fun out => ClaudeWCT.Bank.WCT.outIdx out = f.1
  have hsub : logSeeds T log f ⊆ S.biUnion fun N =>
      (Finset.univ.filter fun t : Fin 6 => WCT9.wordDigit (SigGolfCandidate.Research.SharedForest.forestRank N f.2.val) t = 4).image
        fun t => ((f.1, f.2, SigGolfCandidate.Research.SharedForest.rawChildFromOutput N f.2, t) : CanonGraph.WctAddr) := by
    intro w hw
    obtain ⟨hf, N, hN, hidx, hch, hdig⟩ := (mem_logSeeds T log f w).mp hw
    have h1 : w.1 = f.1 := congrArg Prod.fst hf
    have h2 : w.2.1 = f.2 := congrArg Prod.snd hf
    refine Finset.mem_biUnion.mpr ⟨N, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hN, ?_⟩, ?_⟩
    · rw [← h1, ← hidx]; rfl
    · refine Finset.mem_image.mpr ⟨w.2.2.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [← h2]; exact hdig⟩, ?_⟩
      rw [← h2, hch, ← h1]
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  calc _ ≤ ∑ N ∈ S, 1 := Finset.sum_le_sum fun N _ => Finset.card_image_le.trans (digitThree_card _)
    _ = 1 * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ 1 * 50 := Nat.mul_le_mul_left _ (hno f.1)
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData}
/-- The seeds a sign step discloses are opened by the logged signature of that step. -/
theorem signDisclosed_logSeeds (hcoh : LargeResidual.Paired.Coherent U T vals nv τ a) (published : SigGolfCandidate.T3.Cache)
    (hsource : ∀request : Security.Request,request.cache=published →
      evalWithAnswerFn T (PairedOuter.FullGame.authenticatedSign published request)=
        finishOut T vals (nv request.message) (LargeResidual.Paired.signDigest T request.message)) (request : Security.Request)
    (w : CanonGraph.WctAddr) (hw : (.inr (.inr w) : Coord) ∈ signDisclosed T published request) :
    w ∈ logSeeds T [⟨request, evalWithAnswerFn T (PairedOuter.FullGame.authenticatedSign published request)⟩] (w.1, w.2.1) := by
  unfold signDisclosed at hw
  split_ifs at hw with hc
  swap
  · cases hw
  cases hsd : LargeResidual.Paired.signDigest T request.message with
  | none => rw [hsd] at hw; cases hw
  | some cn =>
      obtain ⟨c, N⟩ := cn
      rw [hsd] at hw
      simp only at hw
      split_ifs at hw with hok
      swap
      · cases hw
      obtain ⟨h1, h2, h3⟩ := wctItem_mem_signItems T N w 0 (Nat.zero_le _) (by rw [wctItem_zero]; exact hw)
      have hdig : WCT9.wordDigit (SigGolfCandidate.Research.SharedForest.forestRank N w.2.1.val) w.2.2.2 = 4 := by
        have := WCT9.wordDigit_le_four (SigGolfCandidate.Research.SharedForest.forestRank N w.2.1.val) w.2.2.2
        omega
      refine (mem_logSeeds T _ _ w).mpr ⟨rfl, N, ?_, h1.symm, h2.symm, hdig⟩
      rw [WPair.Paired.mem_loggedOutputs]
      refine ⟨_, List.mem_singleton_self _, assembleSig (nv request.message) N (ClaudeWCT.W9.T3.Security.LargeResidual.selVals vals) (Wots.CanonicalRef.referenceDigits T (Wots.CanonicalRef.sourceMessages T)) (Wots.CanonicalRef.referenceLow T (Wots.CanonicalRef.sourceMessages T)), ?_, ?_⟩
      · change evalWithAnswerFn T (PairedOuter.FullGame.authenticatedSign published request) = _
        rw [hsource request hc, hsd]
        unfold finishOut
        dsimp only
        rw [if_pos hok]
      · unfold WPair.Paired.signedOutput
        have hrho : (assembleSig (nv request.message) N (ClaudeWCT.W9.T3.Security.LargeResidual.selVals vals) (Wots.CanonicalRef.referenceDigits T (Wots.CanonicalRef.sourceMessages T)) (Wots.CanonicalRef.referenceLow T (Wots.CanonicalRef.sourceMessages T))).rho = nv request.message := rfl
        rw [hrho, ← hcoh.privateNonce]
        unfold LargeResidual.Paired.signDigest at hsd
        rw [hsd]
        rfl
/-- Router disclosures over a tagged run are covered by the seeds opened in its log. -/
theorem discSeeds_steps (hcoh : LargeResidual.Paired.Coherent U T vals nv τ a) (published : SigGolfCandidate.T3.Cache)
    (hsource : ∀request : Security.Request,request.cache=published →
      evalWithAnswerFn T (PairedOuter.FullGame.authenticatedSign published request)=
        finishOut T vals (nv request.message) (LargeResidual.Paired.signDigest T request.message)) {α : Type}
    (program : OracleComp PairedOuter.LazyPrivate.Interaction α) :
    ∀ (state : LazyPrivate.State) (t : Tagged α), t ∈ support (taggedFixed T published program state) →
      ∀ (st : RouterState) (f : Fin (2 ^ 31) × Fin 9),
        DiscSeeds (t.steps.foldl (routerStep U T nv published) st) f ⊆ DiscSeeds st f ∪ logSeeds T t.value.2 f := by
  induction program using OracleComp.inductionOn with
  | pure v =>
      intro state t ht st f
      rw [taggedFixed_pure, mem_support_pure_iff] at ht
      subst ht
      exact Finset.subset_union_left
  | query_bind input next ih =>
      intro state t ht st f
      rcases input with world | request
      · rw [taggedFixed_world, mem_support_bind_iff] at ht
        obtain ⟨answer, -, ht⟩ := ht
        rw [support_map] at ht
        obtain ⟨last, hl, rfl⟩ := ht
        simp only [List.foldl_cons]
        have hst : DiscSeeds (routerStep U T nv published st (.world ⟨state, .inl world, answer⟩)) f =
            DiscSeeds st f := by
          have hd : (routerStep U T nv published st (.world ⟨state, .inl world, answer⟩)).disclosed = st.disclosed := by
            rcases world with n | X
            · rfl
            · exact LargeResidual.RouterState.next_disclosed U st X answer
          unfold DiscSeeds
          rw [hd]
        have := ih answer _ last hl (routerStep U T nv published st (.world ⟨state, .inl world, answer⟩)) f
        rw [hst] at this
        exact this
      · rw [taggedFixed_request, mem_support_bind_iff] at ht
        obtain ⟨block, hb, ht⟩ := ht
        rw [support_map] at ht
        obtain ⟨last, hl, rfl⟩ := ht
        rw [Wots.Ref.fixedRecord_hashOnly T _ (Wots.PairedReference.Ref.authenticatedSign_hashOnly _ _), mem_support_pure_iff] at hb
        simp only [List.foldl_cons]
        have hih := ih block.value _ last hl (routerStep U T nv published st (.sign request block.value block.events)) f
        intro w hw
        rcases Finset.mem_union.mp (hih hw) with h | h
        · have hd : (routerStep U T nv published st (.sign request block.value block.events)).disclosed =
              st.disclosed ++ signDisclosed T published request := signedState_disclosed T nv published st request
          rw [mem_DiscSeeds, hd, List.mem_append] at h
          rcases h.2 with h2 | h2
          · exact Finset.mem_union_left _ ((mem_DiscSeeds st f w).mpr ⟨h.1, h2⟩)
          · apply Finset.mem_union_right
            have hls := signDisclosed_logSeeds hcoh published hsource request w h2
            have hv : block.value = evalWithAnswerFn T (PairedOuter.FullGame.authenticatedSign published request) := by
              rw [hb]; exact Wots.Ref.pureRecord_value _ _ _
            rw [← h.1]
            obtain ⟨hf', N, hN, hrest⟩ := (mem_logSeeds T _ _ w).mp hls
            refine (mem_logSeeds T _ _ w).mpr ⟨hf', N, ?_, hrest⟩
            rw [WPair.Paired.mem_loggedOutputs] at hN ⊢
            obtain ⟨entry, he, hrest'⟩ := hN
            rw [List.mem_singleton] at he
            refine ⟨entry, ?_, hrest'⟩
            rw [he, hv]
            exact List.mem_cons_self
        · apply Finset.mem_union_right
          obtain ⟨hf', N, hN, hrest⟩ := (mem_logSeeds T _ _ w).mp h
          refine (mem_logSeeds T _ _ w).mpr ⟨hf', N, ?_, hrest⟩
          rw [WPair.Paired.mem_loggedOutputs] at hN ⊢
          obtain ⟨entry, he, hrest'⟩ := hN
          exact ⟨entry, List.mem_cons_of_mem _ he, hrest'⟩
theorem discSeeds_initial (f : Fin (2 ^ 31) × Fin 9) : DiscSeeds LargeResidual.RouterState.initial f = ∅ := by
  ext w
  rw [mem_DiscSeeds]
  simp [LargeResidual.RouterState.initial]
/-- WOTS seeds of leaf `L` revealed by its reference digits (digit `0`). -/
@[irreducible] noncomputable def lowerZeros (T : Answers) (L : LowerLeaf) : Finset ChainGraph.Address :=
  Finset.univ.filter fun a => (a.layer, a.tree, CanonGraph.famSlot a.layer a.leaf) = L.1 ∧
    a.leaf.val < 2 ^ height a.layer ∧ a.chain.val < chainCount a.layer ∧
    Wots.CanonicalRef.depth T (Wots.CanonicalRef.sourceMessages T) (SigGolfCandidate.T3.Security.LargeCoupling.wotsAddr a) = 0
theorem mem_lowerZeros (T : Answers) (L : LowerLeaf) (a : ChainGraph.Address) :
    a ∈ lowerZeros T L ↔ (a.layer, a.tree, CanonGraph.famSlot a.layer a.leaf) = L.1 ∧
      a.leaf.val < 2 ^ height a.layer ∧ a.chain.val < chainCount a.layer ∧
      Wots.CanonicalRef.depth T (Wots.CanonicalRef.sourceMessages T) (SigGolfCandidate.T3.Security.LargeCoupling.wotsAddr a) = 0 := by
  unfold lowerZeros
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
/-- Per-leaf zero cap of the canonical reference digits (any answers, real leaves; v6: lower 5, top 9). -/
def LeafZeroCapRef (zcap : Layer → Nat) : Prop :=
  ∀ (T : Answers) (K : Wots.LeafAddr), K.leaf < 2 ^ height K.lay →
    (Finset.univ.filter fun c : Fin (chainCount K.lay) =>
      Wots.CanonicalRef.depth T (Wots.CanonicalRef.sourceMessages T) ⟨K, c.val⟩ = 0).card ≤ zcap K.lay
set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
/-- **Per-family disclosure bound (layout-generic).** With a per-leaf zero cap and the family budget
`zcap · members + 3 ≤ famSize`, a family has at most `famSize − 3` revealed seeds. At the v6 flip this replaces the
today-only proof of `lowerZeros_card`. -/
theorem lowerZeros_card_of_caps {zcap : Layer → Nat} (hz : LeafZeroCapRef zcap)
    (hsize : ∀ lay f, zcap lay * CanonGraph.famMembersL lay f + 3 ≤ WCT9.famSize lay f) (T : Answers)
    (L : LowerLeaf) : (lowerZeros T L).card + 3 ≤ WCT9.famSize L.1.1 L.1.2.2.val := by
  obtain ⟨⟨lay, tree, f⟩, hL⟩ := L
  let Z : ChainGraph.Address → Prop := fun a => a.chain.val < chainCount a.layer ∧
    Wots.CanonicalRef.depth T (Wots.CanonicalRef.sourceMessages T) (SigGolfCandidate.T3.Security.LargeCoupling.wotsAddr a) = 0
  have hleaf : ∀ (lay' : Layer) (tree' : Fin (2 ^ 31)) (n : Nat), n < 2 ^ height lay' →
      ∀ S : Finset ChainGraph.Address, (∀ a ∈ S, a.layer = lay' ∧ a.tree = tree' ∧ a.leaf.val = n ∧ Z a) →
        S.card ≤ zcap lay' := by
    intro lay' tree' n hn S hS
    have hpos : 0 < chainCount lay' := by fin_cases lay' <;> decide
    refine le_trans (Finset.card_le_card_of_injOn (t := Finset.univ.filter fun c : Fin (chainCount lay') =>
        Wots.CanonicalRef.depth T (Wots.CanonicalRef.sourceMessages T) ⟨⟨lay', tree'.val, n⟩, c.val⟩ = 0)
      (fun a => (⟨a.chain.val % chainCount lay', Nat.mod_lt _ hpos⟩ : Fin (chainCount lay'))) ?_ ?_)
      (hz T ⟨lay', tree'.val, n⟩ hn)
    · intro a ha
      obtain ⟨hl, ht, hn', hc, hd⟩ := hS a (Finset.mem_coe.mp ha)
      refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
      obtain ⟨al, atr, alf, ach⟩ := a
      simp only at hl ht hn' hc hd ⊢
      subst hl ht hn'
      rw [Nat.mod_eq_of_lt hc]
      exact hd
    · intro a ha b hb hab
      obtain ⟨hla, hta, hna, hca, -⟩ := hS a (Finset.mem_coe.mp ha)
      obtain ⟨hlb, htb, hnb, hcb, -⟩ := hS b (Finset.mem_coe.mp hb)
      rw [hla] at hca
      rw [hlb] at hcb
      have hv := congrArg Fin.val hab
      simp only at hv
      rw [Nat.mod_eq_of_lt hca, Nat.mod_eq_of_lt hcb] at hv
      exact ChainGraph.Address.ext (hla.trans hlb.symm) (hta.trans htb.symm)
        (Fin.ext (hna.trans hnb.symm)) (Fin.ext hv)
  exact le_trans (Nat.add_le_add_right (CanonGraph.famZeros_card_le Z zcap hleaf lay tree f _
    fun a ha => (mem_lowerZeros T ⟨(lay, tree, f), hL⟩ a).mp ha) 3) (hsize lay f.val)
/-- Canonical producer zero caps per leaf (`WCT9.producerZeroCap`): top 7 of 51 (T51; img-v6: 9 of 54), lower 5 of 43. -/
def leafZeroCap (lay : Layer) : Nat := if lay = 0 then 7 else 5
theorem leafZeroCapRef : LeafZeroCapRef leafZeroCap := by
  intro T K _
  set ds := Wots.CanonicalRef.referenceDigits T (Wots.CanonicalRef.sourceMessages T) K with hds
  have hlen : ds.length = chainCount K.lay := Wots.CanonicalRef.referenceDigits_length T (Wots.CanonicalRef.sourceMessages T) K
  have hzero : (ds.filter (· = 0)).length ≤ leafZeroCap K.lay := by
    dsimp only [ds]
    cases hs : Wots.CanonicalRef.referenceSearch T (Wots.CanonicalRef.sourceMessages T) K with
    | none =>
      simp only [Wots.CanonicalRef.referenceDigits,hs,Option.map_none,Option.getD_none,Wots.Leaf.dummyDigits_zero]
      exact Nat.zero_le _
    | some found =>
      obtain ⟨counter,digits,low⟩ := found
      have hd : ∃floor value,WCT9.CanonicalPolicy.producerDecodeAt K.lay floor low value=some digits := by
        obtain ⟨remaining, _, hs0⟩ := Option.bind_eq_some_iff.mp hs
        exact ⟨_,Wots.CanonicalRef.counterSearch_accepted T _ _ _ _ _ _ _ counter digits low hs0⟩
      simp only [Wots.CanonicalRef.referenceDigits,hs,Option.map_some,Option.getD_some]
      obtain ⟨floor,value,hd⟩ := hd
      have hp := WCT9.CanonicalPolicy.producerDecodeAt_spec hd
      by_cases hz : K.lay=0
      · have hb := hp.2.2.1
        simp only [WCT9.canonicalZeroBound, WCT9.producerZeroCap, hz, if_true] at hb
        unfold leafZeroCap; rw [if_pos hz]; omega
      · have hb := hp.2.2.1
        simp only [WCT9.canonicalZeroBound, WCT9.producerZeroCap, hz, if_false] at hb
        unfold leafZeroCap; rw [if_neg hz]; omega
  refine le_trans (Finset.card_le_card_of_injOn
    (t := (Finset.range ds.length).filter fun i => ds.getD i 0 = 0) (fun c => c.val) ?_ ?_) ?_
  · intro c hc
    have hc' := Finset.mem_filter.mp (Finset.mem_coe.mp hc)
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by rw [hlen]; exact c.isLt), ?_⟩)
    have : Wots.CanonicalRef.depth T (Wots.CanonicalRef.sourceMessages T) ⟨K, c.val⟩ = ds.getD c.val 0 := by
      unfold Wots.CanonicalRef.depth; rfl
    rw [← this]; exact hc'.2
  · intro a _ b _ hab; exact Fin.ext hab
  · rw [idx_zero_card]; exact hzero
theorem leafZeroCap_size (lay : Layer) (f : Nat) :
    leafZeroCap lay * CanonGraph.famMembersL lay f + 3 ≤ WCT9.famSize lay f := by
  unfold leafZeroCap CanonGraph.famMembersL WCT9.famSize WCT9.famGrp
  split_ifs with h
  · have := min_le_left 4 (2 ^ height lay - 4 * f)
    simp only [SigGolfCandidate.T3.topCoefCount]; omega
  · exact le_rfl

/-- At most `famSize − 3` revealed seeds per family (v6 lower: `5 r + 3` coefficients for `r` real members). -/
theorem lowerZeros_card (T : Answers) (L : LowerLeaf) : (lowerZeros T L).card + 3 ≤ WCT9.famSize L.1.1 L.1.2.2.val :=
  lowerZeros_card_of_caps leafZeroCapRef leafZeroCap_size T L
theorem layerItems_seed_lt (digitsOf : Wots.LeafAddr → List Nat) (index : Fin (2 ^ 31)) (a : ChainGraph.Address)
    (h : (.inr (.inl a) : Coord) ∈ layerItems digitsOf index) :
    a.chain.val < chainCount a.layer ∧ a.leaf.val < 2 ^ height a.layer := by
  unfold layerItems at h
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_append] at h
  obtain ⟨lay, hc | hc⟩ := h
  · unfold layerChains at hc
    split_ifs at hc with hb
    · simp only [List.mem_map, List.mem_range] at hc
      obtain ⟨i, hi, hi'⟩ := hc
      obtain ⟨h1, -⟩ := chainItem_seed hi'
      subst h1
      have hi58 : i < 58 := lt_of_lt_of_le hi (by fin_cases lay <;> decide)
      refine ⟨?_, ?_⟩
      · change (CanonGraph.fin58 i).val < chainCount lay
        rw [show (CanonGraph.fin58 i).val = i from Nat.mod_eq_of_lt hi58]
        exact hi
      · change (route index.val lay).1 < 2 ^ height lay
        simp only [route]
        exact Nat.mod_lt _ (by positivity)
    · cases hc
  · unfold layerPath at hc
    split_ifs at hc with hb
    · simp only [List.mem_filterMap, List.mem_range] at hc
      obtain ⟨j, _, hj⟩ := hc
      exact absurd rfl ((treeChild_not_chain hj).2 a)
    · cases hc
theorem signDisclosed_lowerZeros (A : Answers) (published : SigGolfCandidate.T3.Cache) (request : Security.Request)
    (L : LowerLeaf) (a : ChainGraph.Address) (hL : (a.layer, a.tree, CanonGraph.famSlot a.layer a.leaf) = L.1)
    (h : (.inr (.inl a) : Coord) ∈ signDisclosed A published request) : a ∈ lowerZeros A L := by
  have hd := (signDisclosed_chain A published request _ h).2 a rfl
  have hlt : a.chain.val < chainCount a.layer ∧ a.leaf.val < 2 ^ height a.layer := by
    unfold signDisclosed at h
    split_ifs at h with hcache
    · split at h
      · split_ifs at h with hok
        · unfold LargeResidual.Paired.signItems at h
          rcases List.mem_append.mp h with h | h
          · exact absurd rfl ((ftsItems_not_chain _ _ _ h).2 a)
          · exact layerItems_seed_lt _ _ a h
        · cases h
      · cases h
    · cases h
  exact (mem_lowerZeros A L a).mpr ⟨hL, hlt.2, hlt.1, hd⟩
theorem discLower_initial (L : LowerLeaf) : DiscLower LargeResidual.RouterState.initial L = ∅ := by
  ext w
  rw [mem_DiscLower]
  simp [LargeResidual.RouterState.initial]
theorem discLower_steps (U : Finset HashInput) (T : Answers) (nv : Message → Digest)
    (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep) :
    ∀ (st : RouterState) (L : LowerLeaf),
      DiscLower (steps.foldl (routerStep U T nv published) st) L ⊆ DiscLower st L ∪ lowerZeros T L := by
  induction steps with
  | nil => intro st L; exact Finset.subset_union_left
  | cons s rest ih =>
      intro st L w hw
      rw [List.foldl_cons] at hw
      rcases Finset.mem_union.mp (ih _ L hw) with h | h
      · obtain ⟨hL, hd⟩ := (mem_DiscLower _ L w).mp h
        cases s with
        | world e =>
            have he : (routerStep U T nv published st (.world e)).disclosed = st.disclosed := by
              change (routerEvent U st e).disclosed = st.disclosed
              rcases e with ⟨before, (n | X) | c, y⟩
              · rfl
              · exact LargeResidual.RouterState.next_disclosed U st X y
              · rfl
            rw [he] at hd
            exact Finset.mem_union_left _ ((mem_DiscLower st L w).mpr ⟨hL, hd⟩)
        | sign request out events =>
            change (.inr (.inl w) : Coord) ∈ (signedState T nv published st request).disclosed at hd
            rw [signedState_disclosed, List.mem_append] at hd
            rcases hd with hd | hd
            · exact Finset.mem_union_left _ ((mem_DiscLower st L w).mpr ⟨hL, hd⟩)
            · exact Finset.mem_union_right _ (signDisclosed_lowerZeros T published request L w hL hd)
      · exact Finset.mem_union_right _ h
end Overflow

end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord WCoord keygenDisclosed keygenCacheDisclosed lookupVal digestIndex LowerLeaf chainItem layerItems layerPath layerChains treeChild wctItem)
open ClaudeWCT.W9.T3.Security.LargeCoupling (keyValues idx_zero_card)
open SigGolfCandidate.T3.Security.LargeResidual (State Cell runWith_bind)
open ClaudeWCT.W9.T3.Security.FamResidual (observedRun)
open SigGolfCandidate.T3.Security.LargeCoupling (keygen_record)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen
noncomputable local instance instDecidableEqCache_w9largeCouplingTable_contact : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
/-- No index carries more than 50 distinct signed outputs in the log of any game split. -/
def NoOvR (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (rec : FirstHit.Recorded Bool) (A : Answers) : Prop :=
  ∀ g i c, Wots.PairedReference.GameSplit adversary rec g i c → LogNoOverflow A i.value.2
theorem table_contact_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) (initLaw : PMF AuxData)
    {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
    {τ : Cell (Wots.PairedReference.referenceInputs adversary) → HashOutput} {a : AuxData}
    (hcoh : LargeResidual.Paired.Coherent (Wots.PairedReference.referenceInputs adversary) T vals nv τ a)
    (hsource : ∀request : Security.Request,request.cache=(evalWithAnswerFn T keygen).2 →
      evalWithAnswerFn T (PairedOuter.FullGame.authenticatedSign (evalWithAnswerFn T keygen).2 request)=
        finishOut T vals (nv request.message) (LargeResidual.Paired.signDigest T request.message)) :
    Pr[fun rec => ContactR adversary q rec T ∧ NoOvR adversary rec T |
        Wots.Ref.fixedRecord T (PairedOuter.GameWith.idealGame PairedOuter.PaddedGame.checker adversary) (∅, ∅)] ≤
      Pr[fun r => r.1 = none ∧ r.2.counters.calls ≤ q |
        observedRun (auxLaw initLaw) q (Sum.elim vals nv) τ (routerWith (Wots.PairedReference.referenceInputs adversary) adversary q a)
          LargeResidual.initial] := by
  have hUpub : SeccLaw.publicUniverse ⊆ Wots.PairedReference.referenceInputs adversary := Wots.PairedReference.Ref.referenceInputs_universe adversary
  obtain ⟨-, hpub, -⟩ := Correctness.keygen_correct T
  rw [hcoh.routerWith, Wots.PairedReference.Ref.fixed_game_eq, probEvent_map]
  unfold Wots.PairedReference.Ref.fixedInteraction
  rw [← taggedFixed_untag, probEvent_map]
  refine (probEvent_mono ?_).trans (interaction_le initLaw hcoh hq hUpub (evalWithAnswerFn T keygen).2 hsource
    (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2)
    (fun mon st value state => verdictContact (Wots.PairedReference.referenceInputs adversary) T q (evalWithAnswerFn T keygen).1 mon
      value state ∧ FamOK st)
    (verdictCont (Wots.PairedReference.referenceInputs adversary) a q (evalWithAnswerFn T keygen).1) (fun r => r.1 = none ∧ r.2.counters.calls ≤ q)
    ?_ ?_ ?_ (fun _ _ _ _ h => h.2) Monitor.initial LargeResidual.RouterState.initial (keyState (Wots.PairedReference.referenceInputs adversary) q vals nv) _
      rel_initial (fun _ _ h => by cases h))
  · intro t ht hc
    have hsplit := canonical_split adversary T t ht
    have h := hc.1 _ _ _ hsplit
    rw [Wots.Ref.pureRecord_value] at h
    refine ⟨h, fun f => ?_, fun L => ?_⟩
    · have hno : LogNoOverflow T t.value.2 := hc.2 _ _ _ hsplit.untag
      have hsub := discSeeds_steps hcoh (evalWithAnswerFn T keygen).2 hsource _ _ t ht LargeResidual.RouterState.initial f
      rw [discSeeds_initial, Finset.empty_union] at hsub
      exact (Finset.card_le_card hsub).trans ((logSeeds_card T _ hno f).trans (by norm_num))
    · have hsub := discLower_steps (Wots.PairedReference.referenceInputs adversary) T nv (evalWithAnswerFn T keygen).2 t.steps
        LargeResidual.RouterState.initial L
      rw [discLower_initial, Finset.empty_union] at hsub
      have := lowerZeros_card T L
      exact (Finset.card_le_card hsub).trans (by omega)
  · intro mon st ws state v log hrel _ hf
    obtain ⟨out, ws', hrun, hph⟩ := routeVerdict_observed (auxLaw initLaw) hcoh hq
      (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker (evalWithAnswerFn T keygen).1 (v, log))
      (PairedOuter.PaddedGame.verdict_public _ _) mon st ws state hrel hf.2
    change 1 ≤ Pr[_ | observedRun (auxLaw initLaw) q (Sum.elim vals nv) τ
      (routeVerdict (Wots.PairedReference.referenceInputs adversary) a q (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker (evalWithAnswerFn T keygen).1 (v, log)) st) ws]
    rw [hrun, probEvent_pure]
    replace hf := hf.1
    unfold verdictContact at hf
    rcases hph with ⟨h1, -, h3⟩ | ⟨-, h2, -⟩ | ⟨-, h2⟩
    · rw [if_pos ⟨h1, h3⟩]
    · rw [hf] at h2; cases h2
    · have h4 := h2.contact
      rw [hf] at h4
      cases h4
  · intro m s v σ hf
    replace hf := hf.1
    by_contra hcon
    simp only [not_or, not_le] at hcon
    have hc : m.contact = false := by simpa using hcon.1
    have h := events_over (Wots.PairedReference.referenceInputs adversary) T q m hc (by omega) (Wots.Ref.pureRecord T
      (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker (evalWithAnswerFn T keygen).1 v) σ).events
    unfold verdictContact at hf
    rw [h.1] at hf
    cases hf
  · intro ws' hws
    exact ⟨rfl, hws⟩

end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
end
-- ==== merged from T3_Secc_LargeCouplingSwap ====
section

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
section Swap
variable {ι A : Type} [Fintype ι] [Fintype A] [Nonempty A]
noncomputable def mix (P : (ι → A) → ι → Prop) (f g : ι → A) : ι → A := fun i => if P f i then f i else g i
def PrefixDetermined (P : (ι → A) → ι → Prop) : Prop :=
  ∀ f g : ι → A, (∀ i, P f i → f i = g i) → ∀ i, P g i ↔ P f i
noncomputable def swapPair (P : (ι → A) → ι → Prop) (p : (ι → A) × (ι → A)) : (ι → A) × (ι → A) :=
  (mix P p.1 p.2, fun i => if P p.1 i then p.2 i else p.1 i)
theorem prefix_mix (P : (ι → A) → ι → Prop) (hP : PrefixDetermined P) (f g : ι → A) (i : ι) :
    P (mix P f g) i ↔ P f i :=
  hP f (mix P f g) (fun j hj => by unfold mix; rw [if_pos hj]) i
theorem swapPair_involutive (P : (ι → A) → ι → Prop) (hP : PrefixDetermined P) :
    Function.Involutive (swapPair P) := by
  intro p
  rcases p with ⟨f, g⟩
  have hpre : ∀ i, P (mix P f g) i ↔ P f i := prefix_mix P hP f g
  simp only [swapPair]
  ext i
  · simp only [mix]
    by_cases h : P f i
    · rw [if_pos ((hpre i).mpr h), if_pos h]
    · rw [if_neg (fun h' => h ((hpre i).mp h')), if_neg h]
  · simp only [mix]
    by_cases h : P f i
    · rw [if_pos ((hpre i).mpr h), if_pos h]
    · rw [if_neg (fun h' => h ((hpre i).mp h')), if_neg h]
theorem uniform_mix [SampleableType (ι → A)] {Result : Type} (P : (ι → A) → ι → Prop) (hP : PrefixDetermined P)
    (next : (ι → A) → ProbComp Result) :
    𝒮[do let f ← ($ᵗ (ι → A) : ProbComp _); let g ← ($ᵗ (ι → A) : ProbComp _); next (mix P f g)] =
      𝒮[do let h ← ($ᵗ (ι → A) : ProbComp _); next h] := by
  let _ : SampleableType ((ι → A) × (ι → A)) := SampleableType.ofFintype _
  have hprod := FullGame.uniform_product (A := ι → A) (B := ι → A)
  have h1 : 𝒮[do let f ← ($ᵗ (ι → A) : ProbComp _); let g ← ($ᵗ (ι → A) : ProbComp _); next (mix P f g)] =
      𝒮[($ᵗ ((ι → A) × (ι → A)) : ProbComp _) >>= fun p => next (swapPair P p).1] := by
    have h := congrArg (fun law : SPMF ((ι → A) × (ι → A)) => law >>= fun p => 𝒮[next (swapPair P p).1]) hprod
    simpa only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind, swapPair] using h
  have h2 : 𝒮[($ᵗ ((ι → A) × (ι → A)) : ProbComp _) >>= fun p => next (swapPair P p).1] =
      𝒮[($ᵗ ((ι → A) × (ι → A)) : ProbComp _) >>= fun p => next p.1] := by
    have hb := evalSPMF_map_bijective_uniform_cross (α := (ι → A) × (ι → A)) (β := (ι → A) × (ι → A))
      (swapPair P) (swapPair_involutive P hP).bijective
    have h := congrArg (fun law : SPMF ((ι → A) × (ι → A)) => law >>= fun p => 𝒮[next p.1]) hb
    simpa only [evalSPMF_bind, evalSPMF_map, bind_map_left] using h
  have h3 : 𝒮[($ᵗ ((ι → A) × (ι → A)) : ProbComp _) >>= fun p => next p.1] =
      𝒮[do let h ← ($ᵗ (ι → A) : ProbComp _); next h] := by
    have h := congrArg (fun law : SPMF ((ι → A) × (ι → A)) => law >>= fun p => 𝒮[next p.1]) hprod.symm
    simp only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind] at h
    rw [evalSPMF_bind, h, evalSPMF_bind]
    congr 1
    funext f
    rw [evalSPMF_uniformSample]
    exact SphincsSecurity.Concrete.RetainedObservation.lift_bind_const _ _
  rw [h1, h2, h3]
end Swap
end SigGolfCandidate.T3.Security.LargeCoupling
end
-- ==== merged from T3_Secc_LargeCouplingSamplers ====
section

section
namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
  SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual CanonGraph CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem nonce_not_secret (m : Message) :
    (((.inr (.inl m) : Coordinate), (0 : Fin 2)) : ChainGraph.HalfCoordinate) ∉ Set.range secretCoordinate := by
  rintro ⟨s, hs⟩
  have hp := congrArg Prod.fst hs
  cases s <;> cases hp
def nonceHalf (m : Message) : OtherHalf := ⟨((.inr (.inl m) : Coordinate), 0), nonce_not_secret m⟩
end SigGolfCandidate.T3.Security.LargeCoupling
end
section
namespace SigGolfCandidate.T3.Security.LargeCoupling.Samplers
open OracleComp
open SigGolfCandidate.T3 SigGolfCandidate.T3M
open LargeResidual CanonGraph CanonEncoding
attribute [local instance] Classical.propDecidable
noncomputable scoped instance (priority := high) fintypeCoordinate : Fintype Coordinate := coordinateFintype
noncomputable scoped instance (priority := high) samplerFull : SampleableType FullGame.FullTable :=
  Derivation.outputSampler Coordinate
noncomputable scoped instance (priority := high) samplerLabels : SampleableType Labels := SampleableType.ofFintype _
noncomputable scoped instance (priority := high) samplerSecrets : SampleableType Secrets := SampleableType.ofFintype _
noncomputable scoped instance (priority := high) samplerOthers : SampleableType OtherHalves :=
  SampleableType.ofFintype _
noncomputable scoped instance (priority := high) samplerPublic (U : Finset HashInput) :
    SampleableType (U → HashOutput) := SampleableType.ofFintype _
noncomputable scoped instance (priority := high) samplerCell (U : Finset HashInput) :
    SampleableType (Cell U → LargeResidual.HashOutput) := SampleableType.ofFintype _
noncomputable scoped instance (priority := high) samplerLow : SampleableType LowLabels := SampleableType.ofFintype _
noncomputable scoped instance (priority := high) samplerNonces : SampleableType (Message → Digest) :=
  SampleableType.ofFintype _
noncomputable scoped instance (priority := high) samplerVals : SampleableType (Coord → Digest) :=
  SampleableType.ofFintype _
noncomputable scoped instance (priority := high) samplerWorld : SampleableType (WCoord → LargeResidual.Digest) :=
  SampleableType.ofFintype _
noncomputable scoped instance (priority := high) samplerRows :
    SampleableType (EncLeaf → Fin (2 ^ 22) → HashOutput) := SampleableType.ofFintype _
noncomputable scoped instance (priority := high) samplerRowsFlat :
    SampleableType (EncLeaf × Fin (2 ^ 22) → HashOutput) := SampleableType.ofFintype _
noncomputable scoped instance (priority := high) decEqNonceOutside :
    DecidableEq (SphincsSecurity.Concrete.UniformTableSplit.Outside nonceHalf) := Classical.decEq _
noncomputable scoped instance (priority := high) fintypeNonceOutside :
    Fintype (SphincsSecurity.Concrete.UniformTableSplit.Outside nonceHalf) := Subtype.fintype _
noncomputable scoped instance (priority := high) samplerNonceOutside :
    SampleableType (SphincsSecurity.Concrete.UniformTableSplit.Outside nonceHalf → Digest) := SampleableType.ofFintype _
end SigGolfCandidate.T3.Security.LargeCoupling.Samplers
end
end
-- ==== merged from T3_Secc_LargeCouplingLaw ====
section

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual CanonGraph CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
section Generic
theorem evalSPMF_bind_comm {α β γ : Type} (mx : ProbComp α) (my : ProbComp β) (k : α → β → ProbComp γ) :
    𝒮[mx >>= fun x => my >>= fun y => k x y] = 𝒮[my >>= fun y => mx >>= fun x => k x y] := by
  simp only [evalSPMF_bind]
  exact SphincsSecurity.Concrete.RetainedObservation.bind_comm _ _ _
theorem evalSPMF_unused (α : Type) [SampleableType α] [Fintype α] [Nonempty α] {β : Type} (k : ProbComp β) :
    𝒮[($ᵗ α : ProbComp α) >>= fun _ => k] = 𝒮[k] := by
  rw [evalSPMF_bind, evalSPMF_uniformSample]
  exact SphincsSecurity.Concrete.RetainedObservation.lift_bind_const _ _
theorem uniform_equiv_bind {α β γ : Type} [SampleableType α] [SampleableType β] [Finite α] (e : α ≃ β)
    (next : β → ProbComp γ) :
    𝒮[($ᵗ β : ProbComp β) >>= next] = 𝒮[($ᵗ α : ProbComp α) >>= fun x => next (e x)] := by
  have hb := evalSPMF_map_bijective_uniform_cross (α := α) (β := β) e e.bijective
  have h := congrArg (fun law : SPMF β => law >>= fun y => 𝒮[next y]) hb
  simp only [evalSPMF_map, bind_map_left] at h
  rw [evalSPMF_bind, evalSPMF_bind, ← h]
theorem uniform_prod_bind {α β γ : Type} [Finite α] [Finite β] [SampleableType α] [SampleableType β]
    [SampleableType (α × β)] (next : α × β → ProbComp γ) :
    𝒮[($ᵗ (α × β) : ProbComp _) >>= next] =
      𝒮[($ᵗ α : ProbComp α) >>= fun x => ($ᵗ β : ProbComp β) >>= fun y => next (x, y)] := by
  have hprod := FullGame.uniform_product (A := α) (B := β)
  have h := congrArg (fun law : SPMF (α × β) => law >>= fun p => 𝒮[next p]) hprod
  simp only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind] at h
  rw [evalSPMF_bind, ← h, evalSPMF_bind]
  simp only [evalSPMF_bind]
end Generic
section Tables
open SphincsSecurity.Concrete.UniformTableSplit in
theorem uniform_join_bind {ι C A R : Type} [Fintype ι] [Fintype C] [Fintype A] [Nonempty A] [DecidableEq ι]
    [DecidableEq C] (embed : ι → C) (hinj : Function.Injective embed) [SampleableType (C → A)]
    [SampleableType (ι → A)] [SampleableType (Outside embed → A)] (next : (C → A) → ProbComp R) :
    𝒮[($ᵗ (C → A) : ProbComp _) >>= next] =
      𝒮[($ᵗ (ι → A) : ProbComp _) >>= fun r => ($ᵗ (Outside embed → A) : ProbComp _) >>= fun o =>
        next (join embed hinj r o)] := by
  let _ : SampleableType ((ι → A) × (Outside embed → A)) := SampleableType.ofFintype _
  rw [uniform_equiv_bind (split embed hinj).symm next, uniform_prod_bind]
  rfl
open SphincsSecurity.Concrete.UniformTableSplit in
theorem overwrite_bind {ι C A R : Type} [Fintype ι] [Fintype C] [Fintype A] [Nonempty A] [DecidableEq ι]
    [DecidableEq C] (embed : ι → C) (hinj : Function.Injective embed) [SampleableType (C → A)]
    [SampleableType (ι → A)] [SampleableType (Outside embed → A)] (next : (C → A) → ProbComp R) :
    𝒮[($ᵗ (C → A) : ProbComp _) >>= fun t => ($ᵗ (ι → A) : ProbComp _) >>= fun r =>
        next (overwrite embed hinj r t)] =
      𝒮[($ᵗ (C → A) : ProbComp _) >>= next] := by
  rw [uniform_join_bind embed hinj, uniform_join_bind embed hinj next]
  simp only [overwrite_join]
  rw [evalSPMF_unused (ι → A)]
  exact evalSPMF_bind_comm _ _ _
end Tables
end SigGolfCandidate.T3.Security.LargeCoupling
end
-- ==== merged from T3_Secc_LargeCouplingChain ====
section

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual CanonGraph CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
section Chain
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3.Security.LargeCoupling.Samplers
noncomputable def initComp : ProbComp AuxData :=
  ($ᵗ LowLabels : ProbComp _) >>= fun high =>
    ($ᵗ (EncLeaf → Fin (2 ^ 22) → HashOutput) : ProbComp _) >>= fun rows =>
      ($ᵗ FullGame.FullTable : ProbComp _) >>= fun priv => pure ⟨high, rows, priv⟩
noncomputable def initLaw : PMF AuxData := liftM initComp
theorem completeRows_none_apply (U : Finset HashInput) (table : Cell U → LargeResidual.HashOutput) :
    SphincsSecurity.Concrete.ResidualTableCompletion.completeRows (Cell := Cell U) (fun _ => none) table =
      Pr[= table | ($ᵗ (Cell U → LargeResidual.HashOutput) : ProbComp _)] := by
  unfold SphincsSecurity.Concrete.ResidualTableCompletion.completeRows
  rw [SphincsSecurity.Concrete.UniformTableCompletion.complete_apply, if_pos (fun _ => by
      simp [SphincsSecurity.Concrete.ResidualTableCompletion.allowed]),
    probOutput_uniformSample, Fintype.card_fun]
  simp only [SphincsSecurity.Concrete.ResidualTableCompletion.allowed, Finset.prod_const, Finset.card_univ]
theorem completeRows_none (U : Finset HashInput) :
    SphincsSecurity.Concrete.ResidualTableCompletion.completeRows (Cell := Cell U) (fun _ => none) =
      𝒮[($ᵗ (Cell U → LargeResidual.HashOutput) : ProbComp _)] := by
  apply SPMF.ext
  intro table
  rw [completeRows_none_apply]
  rfl
section Lazy
variable {U : Finset HashInput}
theorem probEvent_bind_congr_eq {α β γ : Type} (m : SPMF α) (f : α → SPMF β) (g : α → SPMF γ) (E : β → Prop)
    (E' : γ → Prop) (h : ∀ x, Pr[E | f x] = Pr[E' | g x]) : Pr[E | m >>= f] = Pr[E' | m >>= g] := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  exact tsum_congr fun x => by rw [h x]
end Lazy
end Chain
end SigGolfCandidate.T3.Security.LargeCoupling
end
-- ==== merged from T3_Secc_LargeCouplingContact ====
section

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual CanonGraph CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
section Contact
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3.Security.LargeCoupling.Samplers
theorem probEvent_bind_le_of {α β γ : Type} (mx : ProbComp α) (my : SPMF α) (f : α → ProbComp β) (g : α → SPMF γ)
    (E : β → Prop) (F : γ → Prop) (hw : ∀ x, Pr[= x | mx] = Pr[= x | my]) (h : ∀ x, Pr[E | f x] ≤ Pr[F | g x]) :
    Pr[E | mx >>= f] ≤ Pr[F | my >>= g] := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  exact ENNReal.tsum_le_tsum fun x => by rw [hw x]; gcongr; exact h x
theorem uniform_weight {α : Type} [Fintype α] [Nonempty α] (s1 s2 : SampleableType α) (x : α) :
    Pr[= x | (@uniformSample α s1 : ProbComp α)] = Pr[= x | 𝒮[(@uniformSample α s2 : ProbComp α)]] := by
  rw [show Pr[= x | 𝒮[(@uniformSample α s2 : ProbComp α)]] = Pr[= x | (@uniformSample α s2 : ProbComp α)] from rfl,
    probOutput_uniformSample, probOutput_uniformSample]
theorem evalSPMF_uniform_inst {α : Type} [Fintype α] [Nonempty α] (s1 s2 : SampleableType α) :
    𝒮[(@uniformSample α s1 : ProbComp α)] = 𝒮[(@uniformSample α s2 : ProbComp α)] := by
  apply evalSPMF_ext
  intro x
  rw [probOutput_uniformSample, probOutput_uniformSample]
theorem weight_self {α : Type} (mx : ProbComp α) (x : α) : Pr[= x | mx] = Pr[= x | 𝒮[mx]] := rfl
end Contact
end SigGolfCandidate.T3.Security.LargeCoupling
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_LargeCouplingContact ====
section

section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeCoupling (mix PrefixDetermined)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
theorem nonce_not_secret (m : Message) :
    (((.inr (.inl m) : Coordinate), (0 : Fin 2)) : ChainGraph.HalfCoordinate) ∉ Set.range secretCoordinate := by
  rintro ⟨s, hs⟩
  have hp := congrArg Prod.fst hs
  cases s with
  | inl a =>
      simp only [secretCoordinate, Sum.elim_inl, seedCoordinateP] at hp
      split_ifs at hp <;> cases hp
  | inr f => cases hp
def nonceHalf (m : Message) : OtherHalf := ⟨((.inr (.inl m) : Coordinate), 0), nonce_not_secret m⟩
theorem nonceHalf_injective : Function.Injective nonceHalf := by
  intro m m' h
  have h1 := congrArg (fun x : OtherHalf => x.val.1) h
  simp only [nonceHalf] at h1
  exact Sum.inl.inj (Sum.inr.inj h1)
noncomputable def nonceOver (o : OtherHalves) (nvv : Message → Digest) : OtherHalves :=
  SphincsSecurity.Concrete.UniformTableSplit.overwrite nonceHalf nonceHalf_injective nvv o
noncomputable def privPsi (s : Secrets) (nvv : Message → Digest) (priv : FullGame.FullTable) : FullGame.FullTable :=
  privateEquiv.symm (s, nonceOver (privateEquiv priv).2 nvv)
theorem privateEquiv_snd (t : FullGame.FullTable) (h : OtherHalf) : (privateEquiv t).2 h = ChainGraph.halves t h.val := by
  change (splitEquiv (ChainGraph.halves t)).2 h = _
  simp [splitEquiv, Equiv.sumArrowEquivProdArrow]
  rfl
theorem halves_privPsi (s : Secrets) (nvv : Message → Digest) (priv : FullGame.FullTable)
    (h : ChainGraph.HalfCoordinate) (hs : h ∉ Set.range secretCoordinate) :
    ChainGraph.halves (privPsi s nvv priv) h =
      if hn : ∃ m, h = ((.inr (.inl m) : Coordinate), 0) then nvv (Classical.choose hn)
      else ChainGraph.halves priv h := by
  have h1 := privateEquiv_snd (privPsi s nvv priv) ⟨h, hs⟩
  unfold privPsi at h1
  rw [Equiv.apply_symm_apply] at h1
  change (nonceOver (privateEquiv priv).2 nvv) ⟨h, hs⟩ = _ at h1
  change ChainGraph.halves (privateEquiv.symm (s, nonceOver (privateEquiv priv).2 nvv)) (⟨h, hs⟩ : OtherHalf).val = _
  rw [← h1]
  split_ifs with hn
  · have hm := Classical.choose_spec hn
    have heq : (⟨h, hs⟩ : OtherHalf) = nonceHalf (Classical.choose hn) := Subtype.ext hm
    rw [heq]
    exact SphincsSecurity.Concrete.UniformTableSplit.overwrite_embed _ _ _ _ _
  · rw [nonceOver, SphincsSecurity.Concrete.UniformTableSplit.overwrite_outside _ _ _ _ _ (by
      rintro ⟨m, hm⟩
      exact hn ⟨m, (congrArg Subtype.val hm).symm⟩), privateEquiv_snd]
theorem privPsi_other (s : Secrets) (nvv : Message → Digest) (priv : FullGame.FullTable) (c : Coordinate)
    (hc : ∀ i : Fin 2, (c, i) ∉ Set.range secretCoordinate) (hn : ∀ m : Message, c ≠ .inr (.inl m)) :
    privPsi s nvv priv c = priv c := by
  have hh : ∀ i : Fin 2, ChainGraph.halves (privPsi s nvv priv) (c, i) = ChainGraph.halves priv (c, i) := by
    intro i
    rw [halves_privPsi s nvv priv (c, i) (hc i), dif_neg]
    rintro ⟨m, hm⟩
    exact hn m (congrArg Prod.fst hm)
  have h0 := hh 0
  have h1 := hh 1
  simp only [ChainGraph.halves] at h0 h1
  simp only [Fin.isValue, Fin.val_zero, if_true, Fin.val_one, one_ne_zero, if_false] at h0 h1
  rw [← ChainGraph.joinOutput_parts (privPsi s nvv priv c), ← ChainGraph.joinOutput_parts (priv c), h0, h1]
theorem privPsi_nonce (s : Secrets) (nvv : Message → Digest) (priv : FullGame.FullTable) (m : Message) :
    (privPsi s nvv priv (.inr (.inl m))).extractLsb' 0 128 = nvv m := by
  have h := halves_privPsi s nvv priv _ (nonce_not_secret m)
  rw [dif_pos ⟨m, rfl⟩] at h
  have hm : Classical.choose (⟨m, rfl⟩ : ∃ m', (((.inr (.inl m) : Coordinate), (0 : Fin 2)) : ChainGraph.HalfCoordinate) =
      ((.inr (.inl m') : Coordinate), 0)) = m := by
    have := Classical.choose_spec (⟨m, rfl⟩ : ∃ m', (((.inr (.inl m) : Coordinate), (0 : Fin 2)) :
      ChainGraph.HalfCoordinate) = ((.inr (.inl m') : Coordinate), 0))
    have h1 := congrArg Prod.fst this
    exact (Sum.inl.inj (Sum.inr.inj h1)).symm
  rw [hm] at h
  simpa [ChainGraph.halves] using h
section Public
variable (U : Finset HashInput) (hU : canonInputs ⊆ U) (hE : encInputs ⊆ U)
theorem eagerAnswers_eq (priv : FullGame.FullTable) (pub : U → HashOutput) :
    Wots.eagerAnswers U priv pub = CanonGraph.eagerAnswers priv U pub := by
  funext q
  rcases q with (n | x) | c <;> rfl
end Public
section Coherence
variable (U : Finset HashInput) (hU : canonInputs ⊆ U) (hE : encInputs ⊆ U)
end Coherence
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Samplers
open OracleComp
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (Cell)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
open SigGolfCandidate.T3.Security.LargeCoupling.Samplers
open ClaudeWCT.W9.T3.Security.LargeCoupling (nonceHalf)
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable scoped instance (priority := high) samplerLabels : SampleableType Labels :=
  CanonGraph.instSampleableTypeLabels_1
noncomputable scoped instance (priority := high) samplerSecrets : SampleableType Secrets :=
  CanonGraph.instSampleableTypeSecrets
noncomputable scoped instance (priority := high) samplerOthers : SampleableType OtherHalves :=
  CanonGraph.instSampleableTypeOtherHalves
noncomputable scoped instance (priority := high) samplerLow : SampleableType LowLabels :=
  CanonGraph.instSampleableTypeLowLabels
noncomputable scoped instance (priority := high) samplerVals : SampleableType (Coord → Digest) :=
  SampleableType.ofFintype _
noncomputable scoped instance (priority := high) samplerWorld : SampleableType (WCoord → LargeResidual.Digest) :=
  SampleableType.ofFintype _
noncomputable scoped instance (priority := high) samplerHid : SampleableType (ClaudeWCT.W9.T3.Security.FamResidual.Hid WCoord) :=
  SampleableType.ofFintype _
noncomputable scoped instance (priority := high) samplerJunk : SampleableType (WJunk → LargeResidual.Digest) :=
  SampleableType.ofFintype _
noncomputable scoped instance (priority := high) samplerRows :
    SampleableType (EncLeaf → Fin (2 ^ 22) → HashOutput) := SampleableType.ofFintype _
noncomputable scoped instance (priority := high) samplerRowsFlat :
    SampleableType (EncLeaf × Fin (2 ^ 22) → HashOutput) := SampleableType.ofFintype _
noncomputable scoped instance (priority := high) decEqNonceOutside :
    DecidableEq (SphincsSecurity.Concrete.UniformTableSplit.Outside nonceHalf) := Classical.decEq _
noncomputable scoped instance (priority := high) fintypeNonceOutside :
    Fintype (SphincsSecurity.Concrete.UniformTableSplit.Outside nonceHalf) := Subtype.fintype _
noncomputable scoped instance (priority := high) samplerNonceOutside :
    SampleableType (SphincsSecurity.Concrete.UniformTableSplit.Outside nonceHalf → Digest) := SampleableType.ofFintype _
noncomputable scoped instance (priority := high) samplerEncOutside (U : Finset HashInput) (hE : encInputs ⊆ U)
    (labels : Labels) :
    SampleableType (SphincsSecurity.Concrete.UniformTableSplit.Outside (encCell U hE labels) → HashOutput) :=
  SampleableType.ofFintype _
end ClaudeWCT.W9.T3.Security.LargeCoupling.Samplers
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeCoupling (overwrite_bind uniform_equiv_bind uniform_join_bind uniform_prod_bind
  evalSPMF_bind_comm evalSPMF_unused uniform_mix mix)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
section Law
attribute [local instance] Classical.propDecidable
open ClaudeWCT.W9.T3.Security.LargeCoupling.Samplers SigGolfCandidate.T3.Security.LargeCoupling.Samplers
theorem others_bind {R : Type} (next : OtherHalves → ProbComp R) :
    𝒮[($ᵗ OtherHalves : ProbComp _) >>= next] =
      𝒮[($ᵗ FullGame.FullTable : ProbComp _) >>= fun priv => ($ᵗ (Message → Digest) : ProbComp _) >>= fun nv =>
        next (nonceOver (privateEquiv priv).2 nv)] := by
  rw [private_bind (fun priv => ($ᵗ (Message → Digest) : ProbComp _) >>= fun nv =>
    next (nonceOver (privateEquiv priv).2 nv))]
  simp only [Equiv.apply_symm_apply]
  rw [evalSPMF_unused Secrets]
  unfold nonceOver
  rw [overwrite_bind nonceHalf nonceHalf_injective next]
end Law
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (State Cell AuxQuery retain runWith_query_bind)
open ClaudeWCT.W9.T3.Security.FamResidual (lazyRun finish observedRun run_posterior lazyImpl lazy_aux' view supp)
open SigGolfCandidate.T3.Security.LargeCoupling (completeRows_none_apply completeRows_none probEvent_bind_congr_eq)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
section Chain
attribute [local instance] Classical.propDecidable
open ClaudeWCT.W9.T3.Security.LargeCoupling.Samplers SigGolfCandidate.T3.Security.LargeCoupling.Samplers
theorem cell_univ :
    SphincsSecurity.Concrete.UniformTableCompletion.cell
        (supp (fun _ : WCoord => (Finset.univ : Finset LargeResidual.Digest))) =
      𝒮[($ᵗ (ClaudeWCT.W9.T3.Security.FamResidual.Hid WCoord) : ProbComp _)] := by
  rw [ClaudeWCT.W9.T3.Security.FamResidual.supp_univ]
  apply SPMF.ext
  intro x
  change _ = Pr[= x | ($ᵗ (ClaudeWCT.W9.T3.Security.FamResidual.Hid WCoord) : ProbComp _)]
  rw [SphincsSecurity.Concrete.UniformTableCompletion.cell_apply, if_pos (Finset.mem_univ _), probOutput_uniformSample,
    Finset.card_univ]
section Lazy
variable {U : Finset HashInput}
end Lazy
end Chain
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (State Cell AuxQuery retain runWith_query_bind)
open ClaudeWCT.W9.T3.Security.FamResidual (lazyRun finish observedRun run_posterior lazyImpl lazy_aux' view supp)
open SigGolfCandidate.T3.Security.LargeCoupling (probEvent_bind_le_of uniform_weight weight_self evalSPMF_uniform_inst
  uniform_equiv_bind uniform_prod_bind)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
section Contact
attribute [local instance] Classical.propDecidable
open ClaudeWCT.W9.T3.Security.LargeCoupling.Samplers SigGolfCandidate.T3.Security.LargeCoupling.Samplers
/-- The secrets of a hidden object (leaf-family and FTS coefficients) and the unused junk cells. -/
noncomputable def secOf (x : ClaudeWCT.W9.T3.Security.FamResidual.Hid WCoord) (jk : WJunk → LargeResidual.Digest) :
    Secrets :=
  Sum.elim
    (fun a => if hc : a.chain.val < WCT9.famSize a.layer a.leaf.val then
        x.2 (Sum.inl ⟨(a.layer, a.tree, a.leaf), trivial⟩ : WFam)
          ⟨a.chain.val, by
            have := WCT9.famSize_pos a.layer a.leaf.val
            show a.chain.val < WCT9.famSize a.layer a.leaf.val - 1 + 1; omega⟩
      else jk ⟨a, by omega⟩)
    (fun c => x.2 (Sum.inr (c.1, c.2.1) : WFam) c.2.2)
/-- The coefficient families of a secret table. -/
def famOfSec (sec : Secrets) : (f : WFam) → ClaudeWCT.W9.T3.Security.FamResidual.Coefs
    (ClaudeWCT.W9.T3.Security.FamResidual.Seeds.deg (Coord := WCoord) f)
  | .inl L => fun j => sec (.inl ⟨L.1.1, L.1.2.1, L.1.2.2,
      ⟨j.val, by
        have hj : j.val < WCT9.famSize L.1.1 L.1.2.2.val - 1 + 1 := j.isLt
        have := WCT9.famSize_lt_58 L.1.1 L.1.2.2.val
        omega⟩⟩)
  | .inr f => fun j => sec (.inr (f.1, f.2, j))
noncomputable def worldEquiv : Secrets × ((Message → Digest) × LowLabels) ≃
    ClaudeWCT.W9.T3.Security.FamResidual.Hid WCoord × (WJunk → LargeResidual.Digest) where
  toFun p := (((Sum.elim (Sum.elim p.2.2 (fun t => p.1 (.inl t.1))) p.2.1 : WPlain → LargeResidual.Digest),
    famOfSec p.1), fun jk => p.1 (.inl jk.1))
  invFun y := (secOf y.1 y.2, fun m => y.1.1 (.inr m), fun N => y.1.1 (.inl (.inl N)))
  left_inv p := by
    obtain ⟨sec, nv, low⟩ := p
    refine Prod.ext ?_ rfl
    funext c
    rcases c with a | ⟨i, k, j⟩
    · change (if hc : a.chain.val < WCT9.famSize a.layer a.leaf.val then
          sec (.inl ⟨a.layer, a.tree, a.leaf, ⟨a.chain.val, _⟩⟩) else sec (.inl a)) = sec (.inl a)
      split_ifs <;> rfl
    · rfl
  right_inv y := by
    obtain ⟨⟨L, K⟩, jk⟩ := y
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · funext c
      rcases c with (N | ⟨a, ha⟩) | m
      · rfl
      · exact ha.elim
      · rfl
    · funext f
      rcases f with ⟨⟨lay, tree, leaf⟩, hL⟩ | ⟨i, k⟩
      · funext j
        have hj : j.val < WCT9.famSize lay leaf.val := by
          have h1 : j.val < WCT9.famSize lay leaf.val - 1 + 1 := j.isLt
          have := WCT9.famSize_pos lay leaf.val
          omega
        change (if hc : j.val < WCT9.famSize lay leaf.val then
            K (Sum.inl ⟨(lay, tree, leaf), trivial⟩ : WFam) ⟨j.val, _⟩ else _) = K _ j
        rw [dif_pos hj]
      · rfl
    · funext t
      obtain ⟨a, hc⟩ := t
      show secOf (L, K) jk (.inl a) = jk ⟨a, hc⟩
      unfold secOf
      simp only [Sum.elim_inl]
      rw [dif_neg (by omega)]
theorem world_split {R : Type} (K : Secrets → (Message → Digest) → LowLabels → ProbComp R) :
    𝒮[($ᵗ Secrets : ProbComp _) >>= fun sec => ($ᵗ (Message → Digest) : ProbComp _) >>= fun nv =>
        ($ᵗ LowLabels : ProbComp _) >>= fun low => K sec nv low] =
      𝒮[($ᵗ (ClaudeWCT.W9.T3.Security.FamResidual.Hid WCoord) : ProbComp _) >>= fun x =>
        ($ᵗ (WJunk → LargeResidual.Digest) : ProbComp _) >>= fun jk =>
        K (secOf x jk) (fun m => x.1 (.inr m)) (fun N => x.1 (.inl (.inl N)))] := by
  let _ : SampleableType ((Message → Digest) × LowLabels) := SampleableType.ofFintype _
  let _ : SampleableType (Secrets × ((Message → Digest) × LowLabels)) := SampleableType.ofFintype _
  let _ : SampleableType (ClaudeWCT.W9.T3.Security.FamResidual.Hid WCoord × (WJunk → LargeResidual.Digest)) :=
    SampleableType.ofFintype _
  calc _ = 𝒮[($ᵗ (Secrets × ((Message → Digest) × LowLabels)) : ProbComp _) >>= fun p => K p.1 p.2.1 p.2.2] := by
        rw [uniform_prod_bind]
        refine evalSPMF_bind_congr' _ fun sec => ?_
        rw [uniform_prod_bind]
    _ = 𝒮[($ᵗ (ClaudeWCT.W9.T3.Security.FamResidual.Hid WCoord × (WJunk → LargeResidual.Digest)) : ProbComp _) >>=
          fun y => K (secOf y.1 y.2) (fun m => y.1.1 (.inr m)) (fun N => y.1.1 (.inl (.inl N)))] :=
        uniform_equiv_bind worldEquiv.symm _
    _ = _ := uniform_prod_bind _
theorem ofFn_congr_len {n m : Nat} (h : n = m) (f : Fin n → Digest) (g : Fin m → Digest)
    (hfg : ∀ i (hi : i < n), f ⟨i, hi⟩ = g ⟨i, h ▸ hi⟩) : List.ofFn f = List.ofFn g := by
  subst h
  congr 1
  funext i
  exact hfg i.val i.isLt
theorem seedView_secOf (x : ClaudeWCT.W9.T3.Security.FamResidual.Hid WCoord) (jk : WJunk → LargeResidual.Digest) :
    seedView (secOf x jk) = fun s => view x (.inl (.inr s)) := by
  funext s
  rcases s with a | w
  · change seedsOf (secOf x jk) a = view x (.inl (.inr (.inl a)))
    have hs : (ClaudeWCT.W9.T3.Security.FamResidual.Seeds.split (.inl (.inr (.inl a)) : WCoord)) =
        wsplit (.inl (.inr (.inl a))) := rfl
    unfold view
    rw [hs, wsplit_addr]
    unfold seedsOf
    change ClaudeWCT.Arith.familyEval (List.ofFn (leafFamily (secOf x jk) a.layer a.tree a.leaf))
        (WCT9.famPoint a.layer a.leaf.val a.chain.val) =
      ClaudeWCT.Arith.familyEval
        (List.ofFn (x.2 (Sum.inl ⟨(a.layer, a.tree, famSlot a.layer a.leaf), trivial⟩ : WFam)))
        (WCT9.famPoint a.layer a.leaf.val a.chain.val)
    have hn : WCT9.famSize a.layer (WCT9.famOf a.layer a.leaf.val) =
        WCT9.famSize a.layer (WCT9.famOf a.layer a.leaf.val) - 1 + 1 := by
      have := WCT9.famSize_pos a.layer (WCT9.famOf a.layer a.leaf.val); omega
    congr 1
    apply ofFn_congr_len hn
    intro k hk
    unfold leafFamily secOf
    simp only [Sum.elim_inl]
    split_ifs with h
    · rfl
    · exact absurd hk h
  · rfl
/-- An event's probability under a bind is at most a uniform bound on the continuations. -/
theorem probEvent_bind_le_const {α β : Type} (mx : ProbComp α) (f : α → ProbComp β) (E : β → Prop) (c : ENNReal)
    (h : ∀ x, Pr[E | f x] ≤ c) : Pr[E | mx >>= f] ≤ c := by
  rw [probEvent_bind_eq_tsum]
  calc _ ≤ ∑' x, Pr[= x | mx] * c := ENNReal.tsum_le_tsum fun x => by gcongr; exact h x
    _ = (∑' x, Pr[= x | mx]) * c := ENNReal.tsum_mul_right
    _ ≤ 1 * c := by gcongr; exact tsum_probOutput_le_one
    _ = c := one_mul c
/-- `probEvent_bind_le_of` with an additive pointwise error (top-nonce layer: `CapFail`). -/
theorem probEvent_bind_le_of_add {α β γ : Type} (mx : ProbComp α) (my : SPMF α) (f : α → ProbComp β) (g : α → SPMF γ)
    (E : β → Prop) (F : γ → Prop) (e : α → ENNReal) (hw : ∀ x, Pr[= x | mx] = Pr[= x | my])
    (h : ∀ x, Pr[E | f x] ≤ Pr[F | g x] + e x) :
    Pr[E | mx >>= f] ≤ Pr[F | my >>= g] + ∑' x, Pr[= x | mx] * e x := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun x => ?_
  rw [← hw x, ← mul_add]
  gcongr
  exact h x
/-- `probEvent_bind_le_of` with a constant additive error. -/
theorem probEvent_bind_le_of_add_const {α β γ : Type} (mx : ProbComp α) (my : SPMF α) (f : α → ProbComp β)
    (g : α → SPMF γ) (E : β → Prop) (F : γ → Prop) (c : ENNReal) (hw : ∀ x, Pr[= x | mx] = Pr[= x | my])
    (h : ∀ x, Pr[E | f x] ≤ Pr[F | g x] + c) :
    Pr[E | mx >>= f] ≤ Pr[F | my >>= g] + c := by
  refine (probEvent_bind_le_of_add mx my f g E F (fun _ => c) hw h).trans (add_le_add le_rfl ?_)
  calc _ = (∑' x, Pr[= x | mx]) * c := ENNReal.tsum_mul_right
    _ ≤ 1 * c := by gcongr; exact tsum_probOutput_le_one
    _ = c := one_mul c
end Contact
end ClaudeWCT.W9.T3.Security.LargeCoupling
end

namespace ClaudeWCT.W9.T3.Security.CanonEncoding.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open Correctness (Answers)
open SigGolfCandidate.T3.Security.LargeCoupling (mix PrefixDetermined)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem select_congr_prefix (L : EncLeaf) (floor : Nat) (f g : Fin (2 ^ 22) → HashOutput)
    (h : ∀ c, c.val < WCT9.searchLimit L.1.lay →
      (∀ r, capSel L (SphincsSecurity.Concrete.FirstSuccessTable.select (decodeAt L floor) f) = some r → c ≤ r.1) →
        f c = g c) :
    capSel L (SphincsSecurity.Concrete.FirstSuccessTable.select (decodeAt L floor) g) =
      capSel L (SphincsSecurity.Concrete.FirstSuccessTable.select (decodeAt L floor) f) := by
  cases hs : capSel L (SphincsSecurity.Concrete.FirstSuccessTable.select (decodeAt L floor) f) with
  | none =>
      have hrej : ∀ c : Fin (2 ^ 22), c.val < WCT9.searchLimit L.1.lay → decodeAt L floor (f c) = none := by
        intro c hc
        cases hf : SphincsSecurity.Concrete.FirstSuccessTable.select (decodeAt L floor) f with
        | none => exact (SphincsSecurity.Concrete.FirstSuccessTable.select_none_iff _ _).mp hf c
        | some r =>
            have hge : WCT9.searchLimit L.1.lay ≤ r.1.val := by
              by_contra hlt
              have := (capSel_eq_some (L := L)).mpr ⟨hf, by omega⟩
              rw [hs] at this
              cases this
            exact ((SphincsSecurity.Concrete.FirstSuccessTable.select_some_iff _ f r.1 r.2).mp hf).2 c
              (by rw [Fin.lt_def]; omega)
      have hfg : ∀ c : Fin (2 ^ 22), c.val < WCT9.searchLimit L.1.lay → f c = g c :=
        fun c hc => h c hc (fun r hr => by rw [hs] at hr; cases hr)
      cases hg : SphincsSecurity.Concrete.FirstSuccessTable.select (decodeAt L floor) g with
      | none => rfl
      | some r =>
          obtain ⟨hv, -⟩ := (SphincsSecurity.Concrete.FirstSuccessTable.select_some_iff _ g r.1 r.2).mp hg
          by_cases hlt : r.1.val < WCT9.searchLimit L.1.lay
          · rw [← hfg r.1 hlt, hrej r.1 hlt] at hv
            cases hv
          · cases hc : capSel L (some r) with
            | none => rfl
            | some r' =>
                obtain ⟨hr', hlt'⟩ := capSel_eq_some.mp hc
                cases hr'
                exact absurd hlt' hlt
  | some r =>
      obtain ⟨hraw, hlt⟩ := capSel_eq_some.mp hs
      obtain ⟨i, v⟩ := r
      have hsome := (SphincsSecurity.Concrete.FirstSuccessTable.select_some_iff _ f i v).mp hraw
      have hle : ∀ c, c ≤ i → f c = g c := fun c hc =>
        h c (lt_of_le_of_lt (Fin.le_def.mp hc) hlt) (fun r hr => by rw [hs] at hr; cases hr; exact hc)
      have hg : SphincsSecurity.Concrete.FirstSuccessTable.select (decodeAt L floor) g = some (i, v) := by
        apply (SphincsSecurity.Concrete.FirstSuccessTable.select_some_iff _ g i v).mpr
        refine ⟨by rw [← hle i le_rfl]; exact hsome.1, fun j hj => ?_⟩
        rw [← hle j (le_of_lt hj)]
        exact hsome.2 j hj
      rw [hg]
      exact capSel_eq_some.mpr ⟨rfl, hlt⟩

noncomputable def rowPrefix (f : EncLeaf × Fin (2^22) → HashOutput) (x : EncLeaf × Fin (2^22)) : Prop :=
  ∃ remaining, rowsContext (Function.curry f) x.1.toWots=some remaining ∧
    x.2.val<WCT9.searchLimit x.1.1.lay ∧
    ∀ r, selectionAt (Function.curry f) x.1 remaining=some r → x.2≤r.1

theorem selectionAt_prefix_congr
    (f g : EncLeaf × Fin (2^22) → HashOutput)
    (hfg : ∀ x, rowPrefix f x → f x=g x) (L : EncLeaf) (remaining : Nat)
    (hctx : rowsContext (Function.curry f) L.toWots=some remaining) :
    selectionAt (Function.curry g) L remaining=selectionAt (Function.curry f) L remaining := by
  apply select_congr_prefix L (WCT9.CanonicalPolicy.threshold L.1.lay.val remaining)
  intro c hc hs
  exact hfg (L,c) ⟨remaining,hctx,hc,hs⟩

theorem option_bind_congr_some' {A B : Type} {o : Option A} {f g : A → Option B}
    (h : ∀ a, o = some a → f a = g a) : o.bind f = o.bind g := by
  cases o with
  | none => rfl
  | some a => exact h a rfl

theorem selectionAt_lt {rows : Rows} {L : EncLeaf} {remaining : Nat} {r : Fin (2^22) × Digest}
    (h : selectionAt rows L remaining = some r) : r.1.val < WCT9.searchLimit L.1.lay :=
  (capSel_eq_some.mp h).2

/-- Two row tables with the same selection and the same selected row give the same canonical result. -/
theorem selection_result_congr (f g : Rows) (L : EncLeaf) (remaining floor : Nat)
    (hsel : selectionAt g L remaining = selectionAt f L remaining)
    (hrow : ∀ r, selectionAt f L remaining = some r → g L r.1 = f L r.1) :
    ((selectionAt g L remaining).bind fun r => (WCT9.CanonicalPolicy.producerDecodeOut L.1.lay floor (g L r.1)).map
        fun found => (BitVec.ofNat 32 r.1.val, found)) =
      ((selectionAt f L remaining).bind fun r => (WCT9.CanonicalPolicy.producerDecodeOut L.1.lay floor (f L r.1)).map
        fun found => (BitVec.ofNat 32 r.1.val, found)) := by
  rw [hsel]
  exact option_bind_congr_some' (fun r hr => by rw [hrow r hr])

theorem rowsContext_prefix_congr
    (f g : EncLeaf × Fin (2^22) → HashOutput)
    (hfg : ∀ x, rowPrefix f x → f x=g x) (L : EncLeaf) :
    rowsContext (Function.curry g) L.toWots=rowsContext (Function.curry f) L.toWots := by
  apply Wots.CanonicalRef.context_congr_on WCT9.CanonicalPolicy.credit WotsExtract.SourceLeaf7
    (fun _ h hp => Wots.CanonicalRef.source_parent h hp) _ (source_toWots L)
  intro leaf hleaf remaining hctx
  let E := encLeafOf leaf hleaf
  have he : E.toWots=leaf := encLeafOf_toWots leaf hleaf
  have hc : rowsContext (Function.curry f) E.toWots=some remaining := by rw [he]; exact hctx
  rw [←he,searchRows_toWots,searchRows_toWots]
  exact selection_result_congr (Function.curry f) (Function.curry g) E remaining _
    (selectionAt_prefix_congr f g hfg E remaining hc)
    (fun r hsel => (hfg (E, r.1) ⟨remaining, hc, selectionAt_lt hsel,
      fun r' hr' => by rw [hsel] at hr'; cases hr'; exact le_rfl⟩).symm)

attribute [local irreducible] rowsContext selectionAt

private theorem option_bind_congr_on {A B : Type} {a b : Option A} {f g : A → Option B}
    (he : a=b) (hf : ∀x,b=some x→f x=g x) : a.bind f=b.bind g := by
  subst a
  cases hb : b with
  | none => rfl
  | some x => exact hf x hb

theorem selectionsOfRows_prefix_congr
    (f g : EncLeaf × Fin (2^22) → HashOutput)
    (hfg : ∀ x, rowPrefix f x → f x=g x) (L : EncLeaf) :
    selectionsOfRows (Function.curry g) L=selectionsOfRows (Function.curry f) L :=
  option_bind_congr_on (rowsContext_prefix_congr f g hfg L)
    (fun remaining hc => selectionAt_prefix_congr f g hfg L remaining hc)

theorem rowPrefix_determined : PrefixDetermined rowPrefix := by
  intro f g hfg x
  have hc := rowsContext_prefix_congr f g hfg x.1
  constructor
  · rintro ⟨remaining,hctx,hlimit,hs⟩
    have hctx' := hc.symm.trans hctx
    have he := selectionAt_prefix_congr f g hfg x.1 remaining hctx'
    exact ⟨remaining,hctx',hlimit,fun r hr => hs r (he.symm ▸ hr)⟩
  · rintro ⟨remaining,hctx,hlimit,hs⟩
    have he := selectionAt_prefix_congr f g hfg x.1 remaining hctx
    exact ⟨remaining,hc.trans hctx,hlimit,fun r hr => hs r (he ▸ hr)⟩

end ClaudeWCT.W9.T3.Security.CanonEncoding.Paired

namespace ClaudeWCT.W9.T3.Security.CanonEncoding.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3.Security.CanonGraph
open SigGolfCandidate.T3.Security.LargeCoupling (uniform_equiv_bind uniform_join_bind uniform_mix mix)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance : SampleableType Rows := SampleableType.ofFintype _
noncomputable local instance : SampleableType (EncLeaf × Fin (2^22) → HashOutput) := SampleableType.ofFintype _
noncomputable local instance (U : Finset HashInput) : SampleableType (U → HashOutput) := SampleableType.ofFintype _
noncomputable local instance (U : Finset HashInput) (hE : encInputs ⊆ U) (labels : Labels) :
    SampleableType (SphincsSecurity.Concrete.UniformTableSplit.Outside (encCell U hE labels) → HashOutput) :=
  SampleableType.ofFintype _

noncomputable def residualPsi0 (U : Finset HashInput) (hE : encInputs ⊆ U)
    (labels : Labels) (rows : Rows) (τ : U → HashOutput) : U → HashOutput :=
  SphincsSecurity.Concrete.UniformTableSplit.overwrite (encCell U hE labels) (encCell_injective U hE labels)
    (mix rowPrefix (Function.uncurry rows) (fun x => τ (encCell U hE labels x))) τ

theorem residualPsi0_prefix (U : Finset HashInput) (hE : encInputs ⊆ U)
    (labels : Labels) (rows : Rows) (τ : U → HashOutput)
    (x : EncLeaf × Fin (2^22)) (hx : rowPrefix (Function.uncurry rows) x) :
    residualPsi0 U hE labels rows τ (encCell U hE labels x) = Function.uncurry rows x := by
  unfold residualPsi0
  rw [SphincsSecurity.Concrete.UniformTableSplit.overwrite_embed]
  exact if_pos hx

theorem selections_residualPsi0 (U : Finset HashInput) (hE : encInputs ⊆ U)
    (labels : Labels) (rows : Rows) (τ : U → HashOutput) (L : EncLeaf) :
    selectionsOfRows (fun L c => residualPsi0 U hE labels rows τ (encCell U hE labels (L,c))) L =
      selectionsOfRows rows L :=
  selectionsOfRows_prefix_congr (Function.uncurry rows)
    (fun x => residualPsi0 U hE labels rows τ (encCell U hE labels x))
    (fun x hx => (residualPsi0_prefix U hE labels rows τ x hx).symm) L

theorem residual_bind0 (U : Finset HashInput) (hE : encInputs ⊆ U) (labels : Labels) {R : Type}
    (next : (U → HashOutput) → ProbComp R) :
    𝒮[($ᵗ (U → HashOutput) : ProbComp _) >>= next] =
      𝒮[($ᵗ (EncLeaf → Fin (2 ^ 22) → HashOutput) : ProbComp _) >>= fun rows =>
        ($ᵗ (U → HashOutput) : ProbComp _) >>= fun τ => next (residualPsi0 U hE labels rows τ)] := by
  have hj : ∀ (rows : EncLeaf → Fin (2 ^ 22) → HashOutput) (g : EncLeaf × Fin (2 ^ 22) → HashOutput)
      (out : SphincsSecurity.Concrete.UniformTableSplit.Outside (encCell U hE labels) → HashOutput),
      residualPsi0 U hE labels rows
        (SphincsSecurity.Concrete.UniformTableSplit.join (encCell U hE labels) (encCell_injective U hE labels) g out) =
      SphincsSecurity.Concrete.UniformTableSplit.join (encCell U hE labels) (encCell_injective U hE labels)
        (mix rowPrefix (Function.uncurry rows) g) out := by
    intro rows g out
    unfold residualPsi0
    have hg : (fun x => SphincsSecurity.Concrete.UniformTableSplit.join (encCell U hE labels)
        (encCell_injective U hE labels) g out (encCell U hE labels x)) = g :=
      funext fun x => SphincsSecurity.Concrete.UniformTableSplit.join_embed _ _ _ _ x
    rw [hg, SphincsSecurity.Concrete.UniformTableSplit.overwrite_join]
  rw [evalSPMF_bind_congr' _ (fun rows => uniform_join_bind (encCell U hE labels) (encCell_injective U hE labels)
    (fun τ => next (residualPsi0 U hE labels rows τ)))]
  simp only [hj]
  rw [uniform_equiv_bind (Equiv.curry (EncLeaf) (Fin (2 ^ 22)) HashOutput).symm.symm]
  simp only [Equiv.symm_symm, Equiv.curry_apply, Function.uncurry_curry]
  rw [uniform_mix rowPrefix rowPrefix_determined (fun R =>
    ($ᵗ (SphincsSecurity.Concrete.UniformTableSplit.Outside (encCell U hE labels) → HashOutput) : ProbComp _) >>=
      fun out => next (SphincsSecurity.Concrete.UniformTableSplit.join (encCell U hE labels)
        (encCell_injective U hE labels) R out))]
  rw [uniform_join_bind (encCell U hE labels) (encCell_injective U hE labels) next]

end ClaudeWCT.W9.T3.Security.CanonEncoding.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord seedView)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding (EncLeaf Selections Selection childIndex childIndex_treeBits)
open ClaudeWCT.W9.T3.Security.CanonEncoding.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open SigGolfCandidate.T3.Security.LargeCoupling (mix uniform_equiv_bind)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
attribute [local irreducible] CanonEncoding.Paired.rowsContext CanonEncoding.Paired.selectionAt

def AuxConsistent (a : AuxData) : Prop := a.sel=selectionsOfRows a.rows

section Public
variable (U : Finset HashInput) (hU : CanonGraph.Paired.canonInputs ⊆ U) (hE : encInputs ⊆ U)
noncomputable def presentTable (τ : U → HashOutput) : U → HashOutput := fun x => LargeResidual.Paired.rowPresent x.val (τ x)
noncomputable def presentTableEquiv : (U → HashOutput) ≃ (U → HashOutput) :=
  Equiv.piCongrRight fun x : U => LargeResidual.Paired.rowPresent x.val
noncomputable def residualPsi (labels : Labels) (rows : Rows) (τ : U → HashOutput) : U → HashOutput :=
  CanonEncoding.Paired.residualPsi0 U hE labels rows (presentTable U τ)
noncomputable def tablePsi (sec : Secrets) (vals : LargeResidual.Coord → Digest) (nv : Message → Digest)
    (τ : U → HashOutput) (a : AuxData) : Answers :=
  Wots.eagerAnswers U (privPsi sec nv a.priv)
    (CanonGraph.Paired.Filtered.programmed U hU sec (LargeResidual.Paired.routerLabels vals a)
      (residualPsi U hE (LargeResidual.Paired.routerLabels vals a) a.rows τ))

theorem encCell_row (labels : Labels) (L : EncLeaf) (c : Fin (2^22)) :
    (CanonEncoding.Paired.encCell U hE labels (L,c)).val = Wots.encRow L.toWots (msgLabel labels L) (BitVec.ofNat 32 c.val) 0 := by
  rw [CanonEncoding.Paired.encCell_val,Wots.encRow_zero]
  rfl

theorem paired_ftsLabel_top (labels : Labels) (index : Fin (2^31)) (coord : Fin 9) (b : Fin 2) :
    CanonGraph.Paired.ftsLabel labels index coord 6 b.val =
      Extract.Paired.proj (CanonGraph.Node.wctNode (ftsTopNode index coord b)).toPos
        (labels (.wctNode (ftsTopNode index coord b))) := by
  unfold CanonGraph.Paired.ftsLabel
  rw [if_neg (by omega)]
  unfold ftsNodeAt
  rw [dif_pos (show 6-1<6 ∧ b.val<2^(7-(6-1)-1) by have := b.isLt;omega)]
  rfl

theorem msgLabel_router (vals : LargeResidual.Coord → Digest) (a : AuxData) (L : EncLeaf) :
    msgLabel (LargeResidual.Paired.routerLabels vals a) L = LargeResidual.msgVals vals L := by
  unfold msgLabel LargeResidual.msgVals
  by_cases hl : L.1.lay.val<3
  · rw [dif_pos hl,dif_pos hl]
    congr 1
    · refine (treeLabel_top _ _ _ (childIndex_treeBits L hl) 0).trans ?_
      rw [selNode_of_cap_one (trialCap_lower (fun h => absurd (congrArg Fin.val h) (by simp [topNode])) _) rfl]
      exact CanonGraph.Paired.joinLabels_node _ _ _
    · refine (treeLabel_top _ _ _ (childIndex_treeBits L hl) 1).trans ?_
      rw [selNode_of_cap_one (trialCap_lower (fun h => absurd (congrArg Fin.val h) (by simp [topNode])) _) rfl]
      exact CanonGraph.Paired.joinLabels_node _ _ _
  · rw [dif_neg hl,dif_neg hl]
    congr 1
    · exact (paired_ftsLabel_top _ _ _ 0).trans (CanonGraph.Paired.joinLabels_val _ _ _)
    · exact (paired_ftsLabel_top _ _ _ 1).trans (CanonGraph.Paired.joinLabels_val _ _ _)

theorem sel_psi (a : AuxData) (ha : AuxConsistent a) (labels : Labels) (τ : U → HashOutput) (L : EncLeaf) :
    selectionsOfRows (fun L c => residualPsi U hE labels a.rows τ (CanonEncoding.Paired.encCell U hE labels (L,c))) L = a.sel L :=
  (selections_residualPsi0 U hE labels a.rows (presentTable U τ) L).trans (congrFun ha.symm L)

end Public

private theorem context_prefix_iff (context : Option Nat) (select : Nat → CanonEncoding.Selection)
    (c : Fin (2^22)) (limit : Nat) :
    (∃remaining,context=some remaining ∧ c.val<limit ∧ ∀r,select remaining=some r→c≤r.1) ↔
      context.isSome ∧ c.val<limit ∧ ∀r,context.bind select=some r→c.val≤r.1.val := by
  cases context with
  | none =>
      constructor
      · rintro ⟨remaining,he,_,_⟩;cases he
      · rintro ⟨he,_,_⟩;cases he
  | some n =>
      constructor
      · rintro ⟨remaining,he,hlim,hs⟩
        have hn : n=remaining := Option.some.inj he
        subst remaining
        exact ⟨rfl,hlim,fun r hr => Fin.le_def.mp (hs r hr)⟩
      · rintro ⟨_,hlim,hs⟩
        exact ⟨n,rfl,hlim,fun r hr => Fin.le_def.mpr (hs r hr)⟩

theorem rowPrefix_iff (a : AuxData) (ha : AuxConsistent a) (L : EncLeaf) (c : Fin (2^22)) :
    CanonEncoding.Paired.rowPrefix (Function.uncurry a.rows) (L,c) ↔ LargeResidual.Paired.PrefixRow a L (BitVec.ofNat 32 c.val) := by
  have hc : (BitVec.ofNat 32 c.val).toNat=c.val := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := c.isLt;omega)
  unfold LargeResidual.Paired.PrefixRow
  rw [hc,ha]
  exact context_prefix_iff (rowsContext a.rows L.toWots) (selectionAt a.rows L) c (WCT9.searchLimit L.1.lay)

end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord seedView)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding (EncLeaf Selections Selection childIndex childIndex_treeBits)
open ClaudeWCT.W9.T3.Security.CanonEncoding.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open SigGolfCandidate.T3.Security.LargeCoupling (mix uniform_equiv_bind)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
attribute [local irreducible] CanonEncoding.Paired.rowsContext CanonEncoding.Paired.selectionAt

section Coherence
variable (U : Finset HashInput) (hU : CanonGraph.Paired.canonInputs ⊆ U) (hE : encInputs ⊆ U)
theorem coherent_psi (sec : Secrets) (vals : Coord → Digest) (nv : Message → Digest) (τ : U → HashOutput)
    (a : AuxData) (ha : AuxConsistent a) (hv : seedView sec = fun x => vals (.inr x))
    (hcap : ¬ CanonGraph.CapFail (LargeResidual.Paired.routerLabels vals a)) :
    LargeResidual.Paired.Coherent U (tablePsi U hU hE sec vals nv τ a) vals nv τ a := by
  set s : Secrets := sec with hs
  set labels := LargeResidual.Paired.routerLabels vals a with hlabels
  set res := residualPsi U hE labels a.rows τ with hres
  set o := nonceOver (privateEquiv a.priv).2 nv with ho
  have hT : tablePsi U hU hE sec vals nv τ a = CanonGraph.eagerAnswers (privateEquiv.symm (s, o)) U
      (CanonGraph.Paired.Filtered.programmed U hU s labels res) := by
    unfold tablePsi
    rw [eagerAnswers_eq]
    rfl
  have hsec : secretsOf (tablePsi U hU hE sec vals nv τ a) = s := by
    rw [hT, secretsOf_eager, privateSecrets_symm]
  have hpubX : ∀ (X : HashInput) (hX : X ∈ U), tablePsi U hU hE sec vals nv τ a (.inl (.inr X)) =
      CanonGraph.Paired.Filtered.programmed U hU s labels res ⟨X, hX⟩ := by
    intro X hX
    rw [hT]
    exact eagerAnswers_mem _ U _ ⟨X, hX⟩
  refine ⟨?_, by rw [hsec]; exact hv, ?_, ?_, ?_, ?_, ?_, ?_,ha,hcap⟩
  · rw [hT]
    apply CanonGraph.Paired.Filtered.agrees_of_programmed U hU _ labels res
    intro x
    rw [secretsOf_eager,privateSecrets_symm,eagerAnswers_mem]
  ·
    intro X hX hcell hpre
    rw [hpubX X hX, CanonGraph.Paired.Filtered.programmed_other U hU s labels res ⟨X, hX⟩ (fun N hused => by
      have := hcell N hused
      rw [hsec] at this
      exact this)]
    by_cases hr : (⟨X, hX⟩ : U) ∈ Set.range (CanonEncoding.Paired.encCell U hE labels)
    · obtain ⟨x, hx⟩ := hr
      rw [hres, residualPsi, CanonEncoding.Paired.residualPsi0, ← hx, SphincsSecurity.Concrete.UniformTableSplit.overwrite_embed]
      unfold mix
      rw [if_neg]
      · show LargeResidual.Paired.rowPresent (CanonEncoding.Paired.encCell U hE labels x).val (τ (CanonEncoding.Paired.encCell U hE labels x)) = _
        rw [show (CanonEncoding.Paired.encCell U hE labels x).val = X from congrArg Subtype.val hx]
      intro hpx
      apply hpre
      obtain ⟨L, c⟩ := x
      refine ⟨L, BitVec.ofNat 32 c.val, ?_, (rowPrefix_iff a ha L c).mp hpx⟩
      have hv := congrArg Subtype.val hx
      rw [encCell_row, msgLabel_router] at hv
      exact hv.symm
    · rw [hres, residualPsi, CanonEncoding.Paired.residualPsi0, SphincsSecurity.Concrete.UniformTableSplit.overwrite_outside _ _ _ _ _ hr]
      rfl
  ·
    intro L ctr hp
    have hp1 : ctr.toNat < 2 ^ 22 := lt_of_lt_of_le hp.2.1 (WCT9.searchLimit_le L.1.lay)
    have hc : BitVec.ofNat 32 (⟨ctr.toNat, hp1⟩ : Fin (2 ^ 22)).val = ctr := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by have := hp1; omega)
    have hX : Wots.encRow L.toWots (LargeResidual.msgVals vals L) ctr 0 = (CanonEncoding.Paired.encCell U hE labels (L, ⟨ctr.toNat, hp1⟩)).val := by
      rw [encCell_row, msgLabel_router, hc]
    rw [hX, hpubX _ (CanonEncoding.Paired.encCell U hE labels (L, ⟨ctr.toNat, hp1⟩)).property]
    rw [CanonGraph.Paired.Filtered.programmed_other U hU s labels res _ (fun N _ => CanonEncoding.Paired.encodingQuery_ne_cell _ s N labels)]
    rw [hres, residualPsi, CanonEncoding.Paired.residualPsi0, show (⟨(CanonEncoding.Paired.encCell U hE labels (L, ⟨ctr.toNat, hp1⟩)).val,
      (CanonEncoding.Paired.encCell U hE labels (L, ⟨ctr.toNat, hp1⟩)).property⟩ : U) = CanonEncoding.Paired.encCell U hE labels (L, ⟨ctr.toNat, hp1⟩) from rfl,
      SphincsSecurity.Concrete.UniformTableSplit.overwrite_embed]
    unfold mix
    rw [if_pos ((rowPrefix_iff a ha L _).mpr (by rw [hc]; exact hp))]
    unfold LargeResidual.Paired.prefixValue
    rw [dif_pos hp1]
    rfl
  ·
    intro L
    have hpub : ∀ x : U, tablePsi U hU hE sec vals nv τ a (.inl (.inr x.val)) =
        CanonGraph.Paired.Filtered.programmed U hU (secretsOf (tablePsi U hU hE sec vals nv τ a)) labels res x := by
      intro x
      rw [hsec]
      exact hpubX x.val x.property
    rw [referenceSearch_eq_filtered U hU hE _ labels res hpub L]
    rw [hres,sel_psi U hE a ha labels τ L]
    cases hsel : a.sel L with
    | none => rfl
    | some r =>
      simp only [Option.bind_some]
      have hctxsel : CanonEncoding.Paired.selectionsOfRows a.rows L = some r := by
        rw [← congrFun ha L]; exact hsel
      unfold CanonEncoding.Paired.selectionsOfRows at hctxsel
      cases hctx : CanonEncoding.Paired.rowsContext a.rows L.toWots with
      | none => rw [hctx] at hctxsel; cases hctxsel
      | some remaining =>
        rw [hctx, Option.bind_some] at hctxsel
        have hcap := CanonEncoding.Paired.selectionAt_lt hctxsel
        have hpre : LargeResidual.Paired.PrefixRow a L (BitVec.ofNat 32 r.1.val) := by
          have hc : (BitVec.ofNat 32 r.1.val).toNat = r.1.val := by
            rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := r.1.isLt; omega)
          refine ⟨by rw [hctx]; rfl, by rw [hc]; exact hcap, ?_⟩
          intro r' hr'
          rw [hsel] at hr'; cases hr'
          rw [hc]
        have hrow : residualPsi U hE labels a.rows τ (CanonEncoding.Paired.encCell U hE labels (L, r.1)) =
            a.rows L r.1 := by
          rw [residualPsi, CanonEncoding.Paired.residualPsi0,
            SphincsSecurity.Concrete.UniformTableSplit.overwrite_embed]
          unfold mix
          rw [if_pos ((rowPrefix_iff a ha L r.1).mpr hpre)]
          rfl
        rw [hrow]
  ·
    intro c hc hn
    change privPsi s nv a.priv c = a.priv c
    exact privPsi_other s nv a.priv c hc hn
  ·
    intro X hX
    change SphincsSecurity.Concrete.finiteHashAnswer ∅ U _ X = 0
    unfold SphincsSecurity.Concrete.finiteHashAnswer
    rw [dif_neg hX]
    rfl
  ·
    intro m
    exact privPsi_nonce s nv a.priv m
end Coherence
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord seedView)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding (EncLeaf Selections Selection childIndex childIndex_treeBits)
open ClaudeWCT.W9.T3.Security.CanonEncoding.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open SigGolfCandidate.T3.Security.LargeCoupling (mix uniform_equiv_bind)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
attribute [local irreducible] CanonEncoding.Paired.rowsContext CanonEncoding.Paired.selectionAt

open SigGolfCandidate.T3.Security.LargeCoupling (evalSPMF_bind_comm)
noncomputable local instance : SampleableType FullGame.FullTable := CanonGraph.instSampleableTypeFullTable_canonGraph
noncomputable local instance : SampleableType (Message → Digest) := SigGolfCandidate.T3.Security.LargeCoupling.Samplers.samplerNonces
noncomputable local instance : SampleableType Rows := SampleableType.ofFintype _
noncomputable local instance : SampleableType LowLabels := CanonGraph.instSampleableTypeLowLabels
noncomputable local instance : SampleableType Labels := CanonGraph.instSampleableTypeLabels_1
noncomputable local instance : SampleableType Secrets := CanonGraph.instSampleableTypeSecrets
noncomputable local instance : SampleableType OtherHalves := CanonGraph.instSampleableTypeOtherHalves
noncomputable local instance (U : Finset HashInput) : SampleableType (U → HashOutput) := SampleableType.ofFintype _

theorem tables_bind {Result : Type} (U : Finset HashInput) (hU : CanonGraph.Paired.canonInputs ⊆ U)
    (next : FullGame.FullTable → (U → HashOutput) → ProbComp Result) :
    𝒮[do
      let privateTable ← ($ᵗ FullGame.FullTable : ProbComp _)
      let publicTable ← ($ᵗ (U → HashOutput) : ProbComp _)
      next privateTable publicTable] =
      𝒮[do
        let secrets ← ($ᵗ Secrets : ProbComp _)
        let other ← ($ᵗ OtherHalves : ProbComp _)
        let labels ← ($ᵗ Labels : ProbComp _)
        let residual ← ($ᵗ (U → HashOutput) : ProbComp _)
        next (privateEquiv.symm (secrets, other)) (CanonGraph.Paired.Filtered.programmed U hU secrets labels residual)] := by
  refine (CanonGraph.private_bind (fun privateTable => do
    let publicTable ← ($ᵗ (U → HashOutput) : ProbComp _)
    next privateTable publicTable)).trans ?_
  refine evalSPMF_bind_congr' ($ᵗ Secrets : ProbComp _) fun secrets => ?_
  refine evalSPMF_bind_congr' ($ᵗ OtherHalves : ProbComp _) fun other => ?_
  exact CanonGraph.Paired.Filtered.uniform_bind_programmed U hU secrets (fun table => next (privateEquiv.symm (secrets, other)) table)
theorem residual_bind (U : Finset HashInput) (hE : encInputs ⊆ U) (labels : Labels) {R : Type}
    (next : (U → HashOutput) → ProbComp R) :
    𝒮[($ᵗ (U → HashOutput) : ProbComp _) >>= next] =
      𝒮[($ᵗ Rows : ProbComp _) >>= fun rows =>
        ($ᵗ (U → HashOutput) : ProbComp _) >>= fun τ => next (residualPsi U hE labels rows τ)] := by
  rw [CanonEncoding.Paired.residual_bind0 U hE labels next]
  refine evalSPMF_bind_congr' _ fun rows => ?_
  exact uniform_equiv_bind (presentTableEquiv U)
    (fun τ => next (CanonEncoding.Paired.residualPsi0 U hE labels rows τ))
theorem law_derived (U : Finset HashInput) (hU : CanonGraph.Paired.canonInputs ⊆ U) (hE : encInputs ⊆ U) {R : Type}
    (next : Answers → ProbComp R) :
    𝒮[($ᵗ FullGame.FullTable : ProbComp _) >>= fun priv => ($ᵗ (U → HashOutput) : ProbComp _) >>= fun pub =>
        next (Wots.eagerAnswers U priv pub)] =
      𝒮[($ᵗ Secrets : ProbComp _) >>= fun sec => ($ᵗ FullGame.FullTable : ProbComp _) >>= fun priv' =>
        ($ᵗ (Message → Digest) : ProbComp _) >>= fun nv => ($ᵗ LowLabels : ProbComp _) >>= fun low =>
        ($ᵗ LowLabels : ProbComp _) >>= fun high =>
        ($ᵗ (EncLeaf → Fin (2 ^ 22) → HashOutput) : ProbComp _) >>= fun rows =>
        ($ᵗ (U → HashOutput) : ProbComp _) >>= fun τ =>
        next (CanonGraph.eagerAnswers (privateEquiv.symm (sec, nonceOver (privateEquiv priv').2 nv)) U
          (CanonGraph.Paired.Filtered.programmed U hU sec (CanonGraph.Paired.joinLabels low high) (residualPsi U hE (CanonGraph.Paired.joinLabels low high) rows τ)))] := by
  simp only [eagerAnswers_eq]
  rw [tables_bind U hU (fun priv pub => next (CanonGraph.eagerAnswers priv U pub))]
  refine (evalSPMF_bind_congr' ($ᵗ Secrets : ProbComp _) fun (sec : Secrets) => others_bind _).trans ?_
  refine evalSPMF_bind_congr' ($ᵗ Secrets : ProbComp _) fun sec => ?_
  refine evalSPMF_bind_congr' ($ᵗ FullGame.FullTable : ProbComp _) fun priv' => ?_
  refine evalSPMF_bind_congr' ($ᵗ (Message → Digest) : ProbComp _) fun nv => ?_
  rw [CanonGraph.Paired.labels_bind]
  refine evalSPMF_bind_congr' _ fun low => evalSPMF_bind_congr' _ fun high => ?_
  exact residual_bind U hE (CanonGraph.Paired.joinLabels low high) _
theorem law_target (U : Finset HashInput) (hU : CanonGraph.Paired.canonInputs ⊆ U) (hE : encInputs ⊆ U) {R : Type}
    (next : Answers → ProbComp R) :
    𝒮[($ᵗ FullGame.FullTable : ProbComp _) >>= fun priv => ($ᵗ (U → HashOutput) : ProbComp _) >>= fun pub =>
        next (Wots.eagerAnswers U priv pub)] =
      𝒮[($ᵗ LowLabels : ProbComp _) >>= fun high =>
        ($ᵗ (EncLeaf → Fin (2 ^ 22) → HashOutput) : ProbComp _) >>= fun rows =>
        ($ᵗ FullGame.FullTable : ProbComp _) >>= fun priv' =>
        ($ᵗ Secrets : ProbComp _) >>= fun sec => ($ᵗ (Message → Digest) : ProbComp _) >>= fun nv =>
        ($ᵗ LowLabels : ProbComp _) >>= fun low => ($ᵗ (U → HashOutput) : ProbComp _) >>= fun τ =>
        next (CanonGraph.eagerAnswers (privateEquiv.symm (sec, nonceOver (privateEquiv priv').2 nv)) U
          (CanonGraph.Paired.Filtered.programmed U hU sec (CanonGraph.Paired.joinLabels low high) (residualPsi U hE (CanonGraph.Paired.joinLabels low high) rows τ)))] := by
  rw [law_derived U hU hE next]
  refine (evalSPMF_bind_congr' _ fun _ => evalSPMF_bind_congr' _ fun _ => evalSPMF_bind_congr' _ fun _ =>
    evalSPMF_bind_comm _ _ _).trans ?_
  refine (evalSPMF_bind_congr' _ fun _ => evalSPMF_bind_congr' _ fun _ => evalSPMF_bind_comm _ _ _).trans ?_
  refine (evalSPMF_bind_congr' _ fun _ => evalSPMF_bind_comm _ _ _).trans ?_
  refine (evalSPMF_bind_comm _ _ _).trans ?_
  refine evalSPMF_bind_congr' _ fun _ => ?_
  refine (evalSPMF_bind_congr' _ fun _ => evalSPMF_bind_congr' _ fun _ => evalSPMF_bind_congr' _ fun _ =>
    evalSPMF_bind_comm _ _ _).trans ?_
  refine (evalSPMF_bind_congr' _ fun _ => evalSPMF_bind_congr' _ fun _ => evalSPMF_bind_comm _ _ _).trans ?_
  refine (evalSPMF_bind_congr' _ fun _ => evalSPMF_bind_comm _ _ _).trans ?_
  refine (evalSPMF_bind_comm _ _ _).trans ?_
  refine evalSPMF_bind_congr' _ fun _ => ?_
  refine (evalSPMF_bind_comm _ _ _).trans ?_
  rfl

noncomputable def auxOf (high : LowLabels) (rows : Rows) (priv : FullGame.FullTable) : AuxData :=
  ⟨high,rows,selectionsOfRows rows,priv⟩
theorem auxOf_consistent (high : LowLabels) (rows : Rows) (priv : FullGame.FullTable) :
    AuxConsistent (auxOf high rows priv) := rfl
noncomputable def initComp : ProbComp AuxData :=
  ($ᵗ LowLabels : ProbComp _) >>= fun high =>
    ($ᵗ Rows : ProbComp _) >>= fun rows =>
      ($ᵗ FullGame.FullTable : ProbComp _) >>= fun priv => pure (auxOf high rows priv)
noncomputable def initLaw : PMF AuxData := liftM initComp
theorem initLaw_spmf : (liftM initLaw : SPMF AuxData) = 𝒮[initComp] := by
  apply SPMF.ext
  intro a
  rw [SPMF.liftM_apply, ← PMF.probOutput_eq_apply, ← probEvent_eq_eq_probOutput, initLaw,
    MonitoredPrivate.event_lift, probEvent_eq_eq_probOutput]
  rfl

end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord WCoord WJunk)
open SigGolfCandidate.T3.Security.LargeResidual (State Cell AuxQuery retain runWith_query_bind)
open ClaudeWCT.W9.T3.Security.FamResidual (lazyRun finish observedRun run_posterior lazyImpl lazy_aux' view supp)
open SigGolfCandidate.T3.Security.LargeCoupling (probEvent_bind_le_of uniform_weight weight_self evalSPMF_uniform_inst
  uniform_equiv_bind uniform_prod_bind)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
open ClaudeWCT.W9.T3.Security.LargeCoupling.Samplers SigGolfCandidate.T3.Security.LargeCoupling.Samplers
open SigGolfCandidate.T3.Security.LargeCoupling (completeRows_none probEvent_bind_congr_eq)
section Lazy
variable {U : Finset HashInput}
theorem lazy_aux {β : Type} (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
    (i : AuxQuery) (k : AuxSpec.Range i → OracleComp (RWorld U) β) (s : LargeResidual.State WCoord (Cell U)) :
    lazyRun aux q (liftM ((RWorld U).query (.inl i)) >>= k) s =
      ((liftM (aux i) : SPMF _) >>= fun v => lazyRun aux q (k v) s) := by
  exact lazy_aux' aux q i k s
theorem finish_stop {R : Type} (X : SPMF (Option R × LargeResidual.State WCoord (Cell U)))
    (P : LargeResidual.State WCoord (Cell U) → Prop) :
    Pr[fun r => r.1 = none ∧ P r.2 | X >>= finish] = Pr[fun r => r.1 = none ∧ P r.2 | X] := by
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  apply tsum_congr
  intro r
  rcases r with ⟨v, st⟩
  cases v with
  | none =>
      simp only [finish, probEvent_pure, true_and]
      split_ifs <;> simp
  | some v =>
      simp only [reduceCtorEq, false_and, if_false, mul_eq_zero]
      right
      unfold finish
      simp only [probEvent_bind_eq_tsum, probEvent_pure, reduceCtorEq, false_and, if_false, mul_zero, tsum_zero]
theorem observed_avg {R : Type} (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
    (program : OracleComp (RWorld U) R) (P : LargeResidual.State WCoord (Cell U) → Prop) :
    Pr[fun r => r.1 = none ∧ P r.2 | 𝒮[($ᵗ (ClaudeWCT.W9.T3.Security.FamResidual.Hid WCoord) : ProbComp _)] >>= fun x =>
        𝒮[($ᵗ (Cell U → LargeResidual.HashOutput) : ProbComp _)] >>= fun τ =>
          observedRun aux q (view x) τ program LargeResidual.initial] =
      Pr[fun r => r.1 = none ∧ P r.2 | lazyRun aux q program LargeResidual.initial] := by
  rw [← cell_univ, ← completeRows_none]
  have hpost := run_posterior aux q program (LargeResidual.initial : LargeResidual.State WCoord (Cell U))
    (by change (supp (fun _ : WCoord => (Finset.univ : Finset LargeResidual.Digest))).Nonempty
        rw [ClaudeWCT.W9.T3.Security.FamResidual.supp_univ]; exact Finset.univ_nonempty)
  rw [← finish_stop (lazyRun aux q program LargeResidual.initial) P, ← hpost]
  apply probEvent_bind_congr_eq
  intro labels
  apply probEvent_bind_congr_eq
  intro τ
  rw [probEvent_map]
  congr 1
  funext r
  simp only [Function.comp_apply, retain, Option.map_eq_none_iff]
theorem router_side (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    Pr[fun r => r.1 = none ∧ r.2.counters.calls ≤ q |
        lazyRun (auxLaw initLaw) q (router (Wots.PairedReference.referenceInputs adversary) adversary q) LargeResidual.initial] =
      Pr[fun r => r.1 = none ∧ r.2.counters.calls ≤ q |
        𝒮[($ᵗ LowLabels : ProbComp _)] >>= fun high =>
        𝒮[($ᵗ (EncLeaf → Fin (2 ^ 22) → HashOutput) : ProbComp _)] >>= fun rows =>
        𝒮[($ᵗ FullGame.FullTable : ProbComp _)] >>= fun priv =>
        𝒮[($ᵗ (ClaudeWCT.W9.T3.Security.FamResidual.Hid WCoord) : ProbComp _)] >>= fun x =>
        𝒮[($ᵗ (Cell (Wots.PairedReference.referenceInputs adversary) → LargeResidual.HashOutput) : ProbComp _)] >>= fun τ =>
        observedRun (auxLaw initLaw) q (view x) τ (routerWith (Wots.PairedReference.referenceInputs adversary) adversary q (auxOf high rows priv))
          LargeResidual.initial] := by
  unfold router initReq
  rw [lazy_aux]
  change Pr[_ | (liftM initLaw : SPMF AuxData) >>= _] = _
  rw [initLaw_spmf]
  unfold initComp
  simp only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind]
  apply probEvent_bind_congr_eq
  intro high
  apply probEvent_bind_congr_eq
  intro rows
  apply probEvent_bind_congr_eq
  intro priv
  exact (observed_avg (auxLaw initLaw) q _ (fun st => st.counters.calls ≤ q)).symm
end Lazy
def RealContact (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (x : FirstHit.Recorded Bool × Answers) : Prop :=
  ContactR adversary q x.1 x.2 ∧ NoOvR adversary x.1 x.2
theorem loggedOutputs_short {A T : Answers} (hAT : Wots.Ref.ShortAgree A T) (log : QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) :
    WPair.Paired.loggedOutputs A log = WPair.Paired.loggedOutputs T log := by
  unfold WPair.Paired.loggedOutputs WPair.Paired.signedOutput
  congr 1
  funext entry
  congr 1
  funext σ
  rw [digestSearch_short hAT]
theorem noOvR_short {A T : Answers} (hAT : Wots.Ref.ShortAgree A T) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP)
    (rec : FirstHit.Recorded Bool) : NoOvR adversary rec A ↔ NoOvR adversary rec T := by
  unfold NoOvR LogNoOverflow
  simp only [loggedOutputs_short hAT]
/-- The contact event with the FTS no-overflow side condition (on the recorded trace). -/
def ContactNO (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (z : PairedOuter.PaddedGame.TraceResult × Answers) : Prop :=
  Contact adversary q z ∧ NoOvR adversary (QueryRecorded.recordedTrace z.1) z.2
noncomputable def fixedNext (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (T : Answers) : ProbComp (FirstHit.Recorded Bool × Answers) :=
  (fun r => (r, T)) <$> Wots.Ref.fixedRecord T (PairedOuter.GameWith.idealGame PairedOuter.PaddedGame.checker adversary) (∅, ∅)
theorem contact_real_side (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[ContactNO adversary q | PairedSeccLaw.completedExperiment adversary q hq] =
      Pr[RealContact adversary q |
        ($ᵗ FullGame.FullTable : ProbComp _) >>= fun priv =>
          ($ᵗ (Wots.PairedReference.referenceInputs adversary → HashOutput) : ProbComp _) >>= fun pub =>
            fixedNext adversary (Wots.eagerAnswers (Wots.PairedReference.referenceInputs adversary) priv pub)] := by
  have h1 := Wots.PairedReference.completed_eager_cut adversary q hq (fun rec A => ContactR adversary q rec A ∧ NoOvR adversary rec A)
  rw [show (ContactNO adversary q) = fun z => ContactR adversary q (QueryRecorded.recordedTrace z.1) z.2 ∧
    NoOvR adversary (QueryRecorded.recordedTrace z.1) z.2 from rfl, h1]
  have h2 : (fun x : FirstHit.Recorded Bool × Answers => ContactR adversary q x.1 (Wots.Ref.cut x.1.state x.2) ∧
      NoOvR adversary x.1 (Wots.Ref.cut x.1.state x.2)) = RealContact adversary q := by
    funext x
    exact propext (and_congr (contactR_short (Wots.Ref.cut_shortAgree _ _) adversary q x.1)
      (noOvR_short (Wots.Ref.cut_shortAgree _ _) adversary x.1))
  rw [h2]
  unfold Wots.PairedReference.eagerRecorded
  rw [MonitoredPrivate.event_lift]
  apply probEvent_congr' (fun _ _ => Iff.rfl)
  rw [evalSPMF_bind, evalSPMF_bind, evalSPMF_uniform_inst _ samplerFull]
  congr 1

end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord WCoord WJunk)
open SigGolfCandidate.T3.Security.LargeResidual (State Cell AuxQuery retain runWith_query_bind)
open ClaudeWCT.W9.T3.Security.FamResidual (lazyRun finish observedRun run_posterior lazyImpl lazy_aux' view supp)
open SigGolfCandidate.T3.Security.LargeCoupling (probEvent_bind_le_of uniform_weight weight_self evalSPMF_uniform_inst
  uniform_equiv_bind uniform_prod_bind)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
open ClaudeWCT.W9.T3.Security.LargeCoupling.Samplers SigGolfCandidate.T3.Security.LargeCoupling.Samplers
open SigGolfCandidate.T3.Security.LargeCoupling (completeRows_none probEvent_bind_congr_eq)
/-- The `CapFail` error of the coupling, given the high halves: the probability over the hidden world that the
router labels exhaust a top trial cap. -/
noncomputable def capErr (high : LowLabels) : ENNReal :=
  ∑' x, Pr[= x | ($ᵗ (ClaudeWCT.W9.T3.Security.FamResidual.Hid WCoord) : ProbComp _)] *
    (if CanonGraph.CapFail (CanonGraph.Paired.joinLabels (fun N => x.1 (.inl (.inl N))) high) then 1 else 0)

theorem capErr_le :
    ∑' high, Pr[= high | ($ᵗ LowLabels : ProbComp _)] * capErr high ≤ (2 ^ 142 : ℝ≥0∞)⁻¹ := by
  have e1 : ∀ high, capErr high = Pr[fun l => CanonGraph.CapFail l |
      ($ᵗ (ClaudeWCT.W9.T3.Security.FamResidual.Hid WCoord) : ProbComp _) >>= fun x =>
        (pure (CanonGraph.Paired.joinLabels (fun N => x.1 (.inl (.inl N))) high) : ProbComp Labels)] := by
    intro high
    unfold capErr
    rw [probEvent_bind_eq_tsum]
    refine tsum_congr fun x => ?_
    rw [probEvent_pure]
  have e2 : ∀ high, Pr[fun l => CanonGraph.CapFail l |
      ($ᵗ (ClaudeWCT.W9.T3.Security.FamResidual.Hid WCoord) : ProbComp _) >>= fun x =>
        (pure (CanonGraph.Paired.joinLabels (fun N => x.1 (.inl (.inl N))) high) : ProbComp Labels)] =
      Pr[fun l => CanonGraph.CapFail l | ($ᵗ LowLabels : ProbComp _) >>= fun low =>
        (pure (CanonGraph.Paired.joinLabels low high) : ProbComp Labels)] := by
    intro high
    have hw := world_split (fun (_ : Secrets) (_ : Message → Digest) low =>
      (pure (CanonGraph.Paired.joinLabels low high) : ProbComp Labels))
    have h1 : 𝒮[($ᵗ Secrets : ProbComp _) >>= fun _ => ($ᵗ (Message → Digest) : ProbComp _) >>= fun _ =>
        ($ᵗ LowLabels : ProbComp _) >>= fun low => (pure (CanonGraph.Paired.joinLabels low high) : ProbComp Labels)] =
        𝒮[($ᵗ LowLabels : ProbComp _) >>= fun low => (pure (CanonGraph.Paired.joinLabels low high) : ProbComp Labels)] := by
      rw [OracleComp.DeferredSampling.evalSPMF_bind_const_neverFails _ (by simp) _,
        OracleComp.DeferredSampling.evalSPMF_bind_const_neverFails _ (by simp) _]
    have h2 : 𝒮[($ᵗ (ClaudeWCT.W9.T3.Security.FamResidual.Hid WCoord) : ProbComp _) >>= fun x =>
        ($ᵗ (WJunk → LargeResidual.Digest) : ProbComp _) >>= fun _ =>
          (pure (CanonGraph.Paired.joinLabels (fun N => x.1 (.inl (.inl N))) high) : ProbComp Labels)] =
        𝒮[($ᵗ (ClaudeWCT.W9.T3.Security.FamResidual.Hid WCoord) : ProbComp _) >>= fun x =>
          (pure (CanonGraph.Paired.joinLabels (fun N => x.1 (.inl (.inl N))) high) : ProbComp Labels)] :=
      evalSPMF_bind_congr' _ fun _ => OracleComp.DeferredSampling.evalSPMF_bind_const_neverFails _ (by simp) _
    exact probEvent_congr' (fun _ _ => Iff.rfl) (h2.symm.trans (hw.symm.trans h1))
  simp only [e1, e2]
  rw [← probEvent_bind_eq_tsum]
  let _ : SampleableType Labels := SampleableType.ofFintype _
  have h3 : 𝒮[($ᵗ LowLabels : ProbComp _) >>= fun high => ($ᵗ LowLabels : ProbComp _) >>= fun low =>
      (pure (CanonGraph.Paired.joinLabels low high) : ProbComp Labels)] = 𝒮[($ᵗ Labels : ProbComp Labels)] := by
    rw [OracleComp.DeferredSampling.evalSPMF_bind_comm]
    have := CanonGraph.Paired.labels_bind (fun l => (pure l : ProbComp Labels))
    simp only [bind_pure] at this
    rw [← this]
  rw [probEvent_congr' (fun _ _ => Iff.rfl) h3]
  have hc := CanonGraph.prob_capFail_le
  refine le_trans (le_of_eq ?_) hc
  exact probEvent_congr' (fun _ _ => Iff.rfl) (SigGolfCandidate.T3.Security.LargeCoupling.evalSPMF_uniform_inst _ _)

set_option maxHeartbeats 4000000 in
theorem contact_le_lazy (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[ContactNO adversary q | PairedSeccLaw.completedExperiment adversary q hq] ≤
      Pr[fun r => r.1 = none ∧ r.2.counters.calls ≤ q |
        lazyRun (auxLaw initLaw) q (router (Wots.PairedReference.referenceInputs adversary) adversary q) LargeResidual.initial] +
        (2 ^ 142 : ℝ≥0∞)⁻¹ := by
  have hU : CanonGraph.Paired.canonInputs ⊆ Wots.PairedReference.referenceInputs adversary :=
    CanonGraph.Paired.canonInputs_subset_publicUniverse.trans (Wots.PairedReference.Ref.referenceInputs_universe adversary)
  have hE : CanonGraph.encInputs ⊆ Wots.PairedReference.referenceInputs adversary :=
    CanonGraph.encInputs_subset_publicUniverse.trans (Wots.PairedReference.Ref.referenceInputs_universe adversary)
  rw [contact_real_side, router_side,
    probEvent_congr' (fun _ _ => Iff.rfl) (law_target (Wots.PairedReference.referenceInputs adversary) hU hE (fixedNext adversary))]
  refine le_trans (probEvent_bind_le_of_add _ _ _ _ _ _ capErr (weight_self _) fun high => ?_)
    (add_le_add le_rfl capErr_le)
  refine probEvent_bind_le_of_add_const _ _ _ _ _ _ (capErr high) (weight_self _) fun rows => ?_
  refine probEvent_bind_le_of_add_const _ _ _ _ _ _ (capErr high) (weight_self _) fun priv => ?_
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (world_split _)]
  refine le_trans (probEvent_bind_le_of_add _ _ _ _ _ _
    (fun x => if CanonGraph.CapFail (CanonGraph.Paired.joinLabels (fun N => x.1 (.inl (.inl N))) high) then 1 else 0)
    (weight_self _) fun x => ?_) (add_le_add le_rfl (le_of_eq ?_))
  swap
  · unfold capErr
    refine tsum_congr fun x => ?_
    rw [probOutput_uniformSample]
  by_cases hcf : CanonGraph.CapFail (CanonGraph.Paired.joinLabels (fun N => x.1 (.inl (.inl N))) high)
  · rw [if_pos hcf]
    exact le_trans probEvent_le_one le_add_self
  rw [if_neg hcf, add_zero]
  refine probEvent_bind_le_const _ _ _ _ fun jk => ?_
  have hτ : ∀ (k : (Wots.PairedReference.referenceInputs adversary → HashOutput) → ProbComp (FirstHit.Recorded Bool × Answers)),
      𝒮[(@uniformSample (Wots.PairedReference.referenceInputs adversary → HashOutput) (samplerPublic _) : ProbComp _) >>= k] =
        𝒮[(@uniformSample (Wots.PairedReference.referenceInputs adversary → HashOutput) (samplerCell _) : ProbComp _) >>= k] := by
    intro k
    rw [evalSPMF_bind]
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (hτ _)]
  refine probEvent_bind_le_of _ _ _ _ _ _ (weight_self _) fun τ => ?_
  · have hT : CanonGraph.eagerAnswers (privateEquiv.symm (secOf x jk,
          nonceOver (privateEquiv priv).2 (fun m => x.1 (.inr m)))) (Wots.PairedReference.referenceInputs adversary)
          (CanonGraph.Paired.Filtered.programmed (Wots.PairedReference.referenceInputs adversary) hU (secOf x jk)
            (CanonGraph.Paired.joinLabels (fun N => x.1 (.inl (.inl N))) high)
            (residualPsi (Wots.PairedReference.referenceInputs adversary) hE (CanonGraph.Paired.joinLabels (fun N => x.1 (.inl (.inl N))) high) rows τ)) =
        tablePsi (Wots.PairedReference.referenceInputs adversary) hU hE (secOf x jk) (fun c => view x (.inl c)) (fun m => view x (.inr m)) τ
          (auxOf high rows priv) := by
      unfold tablePsi
      rw [eagerAnswers_eq]
      rfl
    rw [hT]
    unfold fixedNext RealContact
    rw [probEvent_map]
    have hcoh := coherent_psi (Wots.PairedReference.referenceInputs adversary) hU hE (secOf x jk) (fun c => view x (.inl c))
        (fun m => view x (.inr m)) τ (auxOf high rows priv) (auxOf_consistent _ _ _) (seedView_secOf x jk) hcf
    have h := table_contact_le adversary q hq initLaw hcoh
      (hcoh.source (evalWithAnswerFn _ keygen).2 (Correctness.keygen_correct _).2.1)
    have hlab : Sum.elim (fun c => view x (.inl c)) (fun m => view x (.inr m)) = view x := by
      funext c
      rcases c with c | m <;> rfl
    rw [hlab] at h
    exact h

end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
end
-- ==== merged from T3_Secc_LargeCouplingBankLazy ====
section

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section Generic
variable {Coord Cell AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coord] [DecidableEq Coord] [Fintype Cell] [DecidableEq Cell]
theorem ev_runWith_bind {α β : Type}
    (impl : QueryImpl (World auxSpec Coord Cell) (OptionT (StateT (State Coord Cell) SPMF)))
    (comp : OracleComp (World auxSpec Coord Cell) α) (k : α → OracleComp (World auxSpec Coord Cell) β)
    (s : State Coord Cell) (pay : Option β × State Coord Cell → ENNReal) :
    expectedValue (runWith impl (comp >>= k) s) pay =
      expectedValue (runWith impl comp s) (fun r => r.1.elim (pay (none, r.2))
        (fun v => expectedValue (runWith impl (k v) r.2) pay)) := by
  rw [runWith_bind, expectedValue_bind]
  congr 1
  funext r
  rcases r with ⟨v, s'⟩
  cases v with
  | none => simp only [Option.elim_none, expectedValue_pure]
  | some v => rfl
variable (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat)
theorem ev_observe_le {Answer Result : Type} (response : SPMF Answer) (stopped : SPMF Result)
    (next : Answer → SPMF Result) (g : Result → ENNReal) (B : ENNReal)
    (hs : expectedValue stopped g ≤ B) (hn : ∀ y, expectedValue (next y) g ≤ B) :
    expectedValue (observe response stopped next) g ≤ B := by
  unfold observe
  rw [expectedValue_bind]
  apply expectedValue_le_of_le
  intro o
  cases o with
  | none => exact hs
  | some y => exact hn y
theorem ev_bind_le {α β : Type} (mx : SPMF α) (f : α → SPMF β) (g : β → ENNReal) (B : ENNReal)
    (h : ∀ x, expectedValue (f x) g ≤ B) : expectedValue (mx >>= f) g ≤ B := by
  rw [expectedValue_bind]
  exact expectedValue_le_of_le _ h
end Generic
section Router
variable (U : Finset HashInput) (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
def DiscFrame (s s' : State WCoord (Cell U)) : Prop :=
  s'.rows = s.rows ∧ s'.counters = s.counters ∧ ∀ m : Message, s'.candidates (.inr m) = s.candidates (.inr m)
theorem DiscFrame.refl (s : State WCoord (Cell U)) : DiscFrame U s s := ⟨rfl, rfl, fun _ => rfl⟩
theorem DiscFrame.trans {s1 s2 s3 : State WCoord (Cell U)} (h1 : DiscFrame U s1 s2) (h2 : DiscFrame U s2 s3) :
    DiscFrame U s1 s3 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, fun m => (h2.2.2 m).trans (h1.2.2 m)⟩
end Router
end SigGolfCandidate.T3.Security.LargeCoupling
end
-- ==== merged from T3_Secc_LargeCouplingBankState ====
section

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
structure BankInv (U : Finset HashInput) (ws : LargeResidual.State WCoord (Cell U)) (st : RouterState) : Prop where
  calls : ws.counters.calls = st.calls
  mass : ws.counters.mass ≤ ws.counters.calls
  births : st.births.length ≤ st.calls
  nonce : ∀ m, st.memo.lookup m = none → ws.candidates (.inr m) = Finset.univ
  fresh : ∀ (X : HashInput) (hX : X ∈ U), IsDigestRow X → X ∉ st.seen → X ∉ st.trials → ws.rows ⟨X, hX⟩ = none
  seenRows : ∀ (X : HashInput) (hX : X ∈ U), IsDigestRow X → X ∈ st.seen → X ∉ st.trials →
    ∃ y, st.cache X = some y ∧ ws.rows ⟨X, hX⟩ = some y
  bornSeen : ∀ p ∈ st.births, p.1 ∈ st.seen
  trials : ∀ X ∈ st.trials, ∃ rho m c, X = pad64 (digestInput rho m c) ∧ (st.memo.lookup m).isSome
theorem digestTrial_inj {rho rho' : Digest} {m m' : Message} {c c' : Fin (2 ^ 32)}
    (h : Sampling.digestTrial rho m c.val = Sampling.digestTrial rho' m' c'.val) : m = m' ∧ rho = rho' ∧ c = c' := by
  have h' : pad64 (digestInput rho m (BitVec.ofNat 32 c.val)) = pad64 (digestInput rho' m' (BitVec.ofNat 32 c'.val)) := h
  obtain ⟨h1, h2, h3⟩ := BPB.digestInput_injective h'
  refine ⟨h3, h1, Fin.ext ?_⟩
  have := congrArg BitVec.toNat h2
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt c.isLt, Nat.mod_eq_of_lt c'.isLt] using this
theorem tsum_trial_indicator_le (X : HashInput) (a : ENNReal) :
    (∑' m : Message, ∑' p : Digest × Fin (2 ^ 32),
      if Sampling.digestTrial p.1 m p.2.val = X then a else 0) ≤ a := by
  by_cases hex : ∃ (m : Message) (p : Digest × Fin (2 ^ 32)), Sampling.digestTrial p.1 m p.2.val = X
  · obtain ⟨m0, p0, h0⟩ := hex
    have hinner : ∀ m, (∑' p : Digest × Fin (2 ^ 32), if Sampling.digestTrial p.1 m p.2.val = X then a else 0) =
        if m = m0 then a else 0 := by
      intro m
      by_cases hm : m = m0
      · subst hm
        rw [if_pos rfl, tsum_eq_single p0]
        · rw [if_pos h0]
        · intro p hp
          rw [if_neg]
          intro hp'
          obtain ⟨-, h1, h2⟩ := digestTrial_inj (hp'.trans h0.symm)
          exact hp (Prod.ext h1 h2)
      · rw [if_neg hm]
        apply ENNReal.tsum_eq_zero.mpr
        intro p
        rw [if_neg]
        intro hp'
        exact hm (digestTrial_inj (hp'.trans h0.symm)).1
    simp_rw [hinner]
    rw [tsum_ite_eq]
  · push Not at hex
    simp only [hex, if_false, tsum_zero]
    exact zero_le
theorem expectedValue_uniform_reply (f : LargeResidual.HashOutput → ENNReal) :
    expectedValue (liftM (PMF.uniformOfFintype LargeResidual.HashOutput) : SPMF LargeResidual.HashOutput) f =
      expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun y => f y) := by
  simp only [expectedValue_def]
  apply tsum_congr
  intro y
  have h1 : Pr[= y | ($ᵗ HashOutput : ProbComp HashOutput)] =
      (Fintype.card LargeResidual.HashOutput : ENNReal)⁻¹ := probOutput_uniformSample _ y
  have h2 : Pr[= y | (liftM (PMF.uniformOfFintype LargeResidual.HashOutput) : SPMF LargeResidual.HashOutput)] =
      (Fintype.card LargeResidual.HashOutput : ENNReal)⁻¹ := by
    rw [SPMF.probOutput_eq_apply, SPMF.liftM_apply, PMF.uniformOfFintype_apply]
  rw [h1, h2]
end SigGolfCandidate.T3.Security.LargeCoupling
end
-- ==== merged from T3_Secc_LargeCouplingBankStep ====
section

section
namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual CanonGraph CanonEncoding
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section Frame
variable (U : Finset HashInput)
def QFrame (X : HashInput) (s s' : LargeResidual.State WCoord (Cell U)) : Prop :=
  (∀ row : Cell U, row.1 ≠ X → s'.rows row = s.rows row) ∧ s'.counters.calls = s.counters.calls + 1 ∧
    s'.counters.mass = s.counters.mass ∧ ∀ m : Message, s'.candidates (.inr m) = s.candidates (.inr m)
variable (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
def OutcomeLe {α : Type} (X : HashInput) (s : LargeResidual.State WCoord (Cell U))
    (g : Option α × LargeResidual.State WCoord (Cell U) → ENNReal) (B : ENNReal) : Prop :=
  (∀ v s', QFrame U X s s' → g (some v, s') ≤ B) ∧ ∀ s', s'.counters.mass = s.counters.mass → g (none, s') ≤ B
theorem OutcomeLe.map {α β : Type} {X : HashInput} {s : LargeResidual.State WCoord (Cell U)}
    {g : Option β × LargeResidual.State WCoord (Cell U) → ENNReal} {B : ENNReal} (f : α → β)
    (h : OutcomeLe U X s g B) : OutcomeLe U X s (fun r => g (r.1.map f, r.2)) B :=
  ⟨fun v s' hs => h.1 (f v) s' hs, fun s' hs => h.2 s' hs⟩
end Frame
section Invariant
variable {U : Finset HashInput}
theorem BankInv.after {ws ws' : LargeResidual.State WCoord (Cell U)} {st : RouterState} (h : BankInv U ws st)
    (X : HashInput) (hX : ¬(X ∈ U ∧ IsDigestRow X)) (hf : QFrame U X ws ws') : BankInv U ws' (st.after X) := by
  have hne : ∀ X' (hX' : X' ∈ U), IsDigestRow X' → X' ≠ X := fun X' hX' hd he => hX ⟨he ▸ hX', he ▸ hd⟩
  refine ⟨by rw [hf.2.1, h.calls]; rfl, by rw [hf.2.2.1, hf.2.1]; exact (h.mass).trans (Nat.le_succ _),
    (h.births).trans (Nat.le_succ _), fun m hm => by rw [hf.2.2.2 m]; exact h.nonce m hm, ?_, ?_, ?_, h.trials⟩
  · intro X' hX' hd hs ht
    rw [hf.1 ⟨X', hX'⟩ (hne X' hX' hd)]
    exact h.fresh X' hX' hd (fun hm => hs (List.mem_cons_of_mem _ hm)) ht
  · intro X' hX' hd hs ht
    rw [hf.1 ⟨X', hX'⟩ (hne X' hX' hd)]
    have hs' : X' ∈ st.seen := by
      rcases List.mem_cons.mp hs with he | hm
      · exact absurd he (hne X' hX' hd)
      · exact hm
    exact h.seenRows X' hX' hd hs' ht
  · intro p hp
    exact List.mem_cons_of_mem _ (h.bornSeen p hp)
end Invariant
end SigGolfCandidate.T3.Security.LargeCoupling
end
section
namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual CanonGraph CanonEncoding
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section Step
variable {U : Finset HashInput}
theorem birth_pay (m q : Nat) (hm : m < q) (p : ENNReal) :
    p + (CaseC.theta + 1 / 64) / 2 ^ 128 + ((q - (m + 1) : Nat) : ENNReal) / 2 ^ 128 ≤
      p + ((q - m : Nat) : ENNReal) / 2 ^ 128 := by
  rw [add_assoc]
  apply add_le_add le_rfl
  rw [← ENNReal.add_div]
  apply ENNReal.div_le_div_right
  have hq : q - m = (q - (m + 1)) + 1 := by omega
  rw [hq, Nat.cast_add, Nat.cast_one, add_comm ((q - (m + 1) : Nat) : ENNReal)]
  exact add_le_add CaseC.theta_add_sixteenth_le_one le_rfl
variable (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
end Step
end SigGolfCandidate.T3.Security.LargeCoupling
end
end
-- ==== merged from T3_Secc_LargeCouplingBankSearch ====
section

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
section Search
variable {U : Finset HashInput} (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
  (a : AuxData) (rho : Digest) (m : Message)
theorem trial_ne {k c : Nat} (hk : k < 2 ^ 32) (hc : c < 2 ^ 32) (hne : k ≠ c) :
    pad64 (digestInput rho m (BitVec.ofNat 32 k)) ≠ pad64 (digestInput rho m (BitVec.ofNat 32 c)) := by
  intro h
  obtain ⟨-, h2, -⟩ := BPB.digestInput_injective h
  have := congrArg BitVec.toNat h2
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hc] at this
  exact hne this
theorem reply_of_some {rows : ResidualTableCompletion.Cache (Cell U)} {row : Cell U} {u : LargeResidual.HashOutput}
    (h : rows row = some u) : reply rows row = pure u := by
  unfold reply; rw [h]
theorem reply_of_none {rows : ResidualTableCompletion.Cache (Cell U)} {row : Cell U} (h : rows row = none) :
    reply rows row = liftM (PMF.uniformOfFintype LargeResidual.HashOutput) := by
  unfold reply; rw [h]
theorem expectedValue_uniform_ro (f : LargeResidual.HashOutput → ENNReal) :
    expectedValue (liftM (PMF.uniformOfFintype LargeResidual.HashOutput) : SPMF LargeResidual.HashOutput) f =
      expectedValue ($ᵗ (SphincsSecurity.HashSpec.Range (default : HashInput)) : ProbComp _) (fun y => f y) := by
  simp only [expectedValue_def]
  apply tsum_congr
  intro y
  have h1 : Pr[= y | ($ᵗ (SphincsSecurity.HashSpec.Range (default : HashInput)) : ProbComp _)] =
      (Fintype.card LargeResidual.HashOutput : ENNReal)⁻¹ := probOutput_uniformSample _ y
  have h2 : Pr[= y | (liftM (PMF.uniformOfFintype LargeResidual.HashOutput) : SPMF LargeResidual.HashOutput)] =
      (Fintype.card LargeResidual.HashOutput : ENNReal)⁻¹ := by
    rw [SPMF.probOutput_eq_apply, SPMF.liftM_apply, PMF.uniformOfFintype_apply]
  rw [h1, h2]
end Search
end SigGolfCandidate.T3.Security.LargeCoupling
end
-- ==== merged from T3_Secc_LargeCouplingBankSign ====
section

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_largeCouplingBankSign : DecidableEq T3.Cache := Classical.decEq _
section Sign
variable {U : Finset HashInput}
variable (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
theorem expectedValue_cell_univ (f : LargeResidual.Digest → ENNReal) :
    expectedValue (cell (Finset.univ : Finset LargeResidual.Digest)) f =
      expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho => f rho) := by
  simp only [expectedValue_def]
  apply tsum_congr
  intro rho
  have h1 : Pr[= rho | ($ᵗ Digest : ProbComp Digest)] = (Fintype.card LargeResidual.Digest : ENNReal)⁻¹ :=
    probOutput_uniformSample _ rho
  have h2 : Pr[= rho | cell (Finset.univ : Finset LargeResidual.Digest)] =
      (Fintype.card LargeResidual.Digest : ENNReal)⁻¹ := by
    rw [cell, dif_pos Finset.univ_nonempty, SPMF.probOutput_eq_apply, SPMF.liftM_apply,
      PMF.uniformOfFinset_apply, if_pos (Finset.mem_univ _), Finset.card_univ]
  rw [h1, h2]
end Sign
end SigGolfCandidate.T3.Security.LargeCoupling
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_LargeCouplingBankSign ====
section

section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (State Cell Charge Probe readState probeState stoppedState
  disclosedState tickState)
open ClaudeWCT.W9.T3.Security.FamResidual (lazyRun lazyResp discLaw lazy_read lazy_pure lazy_probe_cached
  lazy_probe_fresh lazy_aux' lazy_disclose lazy_tick)
open SigGolfCandidate.T3.Security.LargeCoupling (ev_bind_le)
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
section Router
variable (U : Finset HashInput) (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
def DiscFrame (s s' : State WCoord (Cell U)) : Prop :=
  s'.rows = s.rows ∧ s'.counters = s.counters ∧ ∀ m : Message, s'.candidates (.inr m) = s.candidates (.inr m)
theorem DiscFrame.refl (s : State WCoord (Cell U)) : DiscFrame U s s := ⟨rfl, rfl, fun _ => rfl⟩
theorem DiscFrame.trans {s1 s2 s3 : State WCoord (Cell U)} (h1 : DiscFrame U s1 s2) (h2 : DiscFrame U s2 s3) :
    DiscFrame U s1 s3 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, fun m => (h2.2.2 m).trans (h1.2.2 m)⟩
theorem discFrame_disclose (s : State WCoord (Cell U)) (c : Coord) (v : Digest) :
    DiscFrame U s (disclosedState q s (.inl c) v .none) := by
  refine ⟨rfl, rfl, fun m => ?_⟩
  simp only [disclosedState, discloseTableValue]
  rw [Function.update_of_ne (by simp)]
end Router
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
section
section
namespace ClaudeWCT.Bank.WCT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open CaseC (BankCore BankCore.expose theta)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable (horizon : Nat) (rate : ENNReal) (hexc : ExcessBound horizon rate)
theorem wct_corePotential_rate (rate' : ENNReal) (hexc' : ExcessBound horizon rate') :
    (wctSpecL horizon rate hexc).corePotential = (wctSpecL horizon rate' hexc').corePotential := rfl
theorem wct_core_birth (b : BankCore) (s : Nat) (hs : b.slack = s + 1) (C' : HashOutput → ENNReal)
    (hC : ∀ N, C' N ≤ b.reuse + (wctSpecL horizon rate hexc).admInd N / 2 ^ 128) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
        (fun N => (wctSpecL horizon rate hexc).corePotential
          { b with targets := b.targets ++ [N], slack := s, reuse := C' N }) ≤
      (wctSpecL horizon rate hexc).corePotential b + (theta + 1 / 64) / 2 ^ 128 :=
  (wctSpecL horizon rate hexc).core_birth b s hs C' hC
theorem wct_core_sign (b : BankCore) (cache : Sampling.RCache) (m : Message) (C' : ENNReal)
    (hC : C' + (wctSpecL horizon rate hexc).reuseMass cache m ≤ b.reuse) (secret : BitVec 256) (fuel : Nat)
    (hfuel : fuel ≤ 2 ^ 32) :
    expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho =>
      if (wctSpecL horizon rate hexc).Reuse cache rho m then
        (wctSpecL horizon rate hexc).corePotential { b with reused := true, reuse := C' }
      else expectedValue (Sampling.roRun secret (WCT9.digestSearch rho m 0 fuel) cache)
        (fun result => (wctSpecL horizon rate hexc).corePotential (b.expose C' (result.1.map Prod.snd)))) ≤
      (wctSpecL horizon rate hexc).corePotential b := by
  have h := (wctSpecL horizon rate hexc).core_sign b cache m C' hC secret fuel hfuel
  simp only [← wct_digestSearch_public (wctSpecL horizon rate hexc).toFtsBankSpec rfl] at h
  exact h
theorem wct_core_win (b : BankCore) (halive : ¬horizon < b.exposures.length)
    (h : b.reused = true ∨ ∃ N ∈ b.targets, WCT9.admissible N = true ∧ Covered b.exposures N) :
    1 ≤ (wctSpecL horizon rate hexc).corePotential b :=
  (wctSpecL horizon rate hexc).core_win b halive h
theorem wct_core_initial (budget : Nat) :
    (wctSpecL horizon rate hexc).corePotential ⟨[], [], false, 0, budget⟩ ≤ (budget : ENNReal) * rate / 2 ^ 128 :=
  (wctSpecL horizon rate hexc).core_initial budget
noncomputable abbrev S0 : FtsBankSpec WProposal :=
  (wctSpecL horizon ⊤ (by unfold ExcessBound; exact le_top)).toFtsBankSpec
noncomputable def excessForecast54 (R : Nat) (X : List HashOutput) : ENNReal :=
  ClaudeWCT.Numerics.Law.lawAvg (S0 horizon).law R
    (fun W => (S0 horizon).price ((S0 horizon).proposals X ++ W) - 2031 / 1024)
theorem excessForecast54_step (R : Nat) (X : List HashOutput) :
    expectedValue (S0 horizon).accepted (fun A => excessForecast54 horizon R (X ++ [A])) =
      excessForecast54 horizon (R + 1) X := by
  unfold excessForecast54
  rw [ClaudeWCT.Numerics.Law.lawAvg_succ]
  have hA (A : HashOutput) : ClaudeWCT.Numerics.Law.lawAvg (S0 horizon).law R
      (fun W => (S0 horizon).price ((S0 horizon).proposals (X ++ [A]) ++ W) - 2031 / 1024) =
      (fun p : WProposal => ClaudeWCT.Numerics.Law.lawAvg (S0 horizon).law R
        (fun W => (S0 horizon).price ((S0 horizon).proposals X ++ p :: W) - 2031 / 1024))
        ((S0 horizon).proposal A) := by
    simp [FtsBankSpec.proposals, List.map_append, List.append_assoc]
  simp_rw [hA]
  exact (S0 horizon).expected_accepted_proposal (fun p => ClaudeWCT.Numerics.Law.lawAvg (S0 horizon).law R
    (fun W => (S0 horizon).price ((S0 horizon).proposals X ++ p :: W) - 2031 / 1024))
theorem average_forecast_le_54 (R : Nat) (X : List HashOutput) :
    BPORS.finiteAverage (fun N : HashOutput => (S0 horizon).forecast R X N) ≤
      ((2031 / 1024 : ENNReal) + excessForecast54 horizon R X) / 2 ^ 128 := by
  rw [(S0 horizon).average_forecast]
  apply ENNReal.div_le_div_right
  unfold excessForecast54
  calc
    _ ≤ ClaudeWCT.Numerics.Law.lawAvg (S0 horizon).law R
          (fun W => (2031 / 1024 : ENNReal) + ((S0 horizon).price ((S0 horizon).proposals X ++ W) - 2031 / 1024)) :=
      ClaudeWCT.Numerics.Law.lawAvg_mono (S0 horizon).law R fun W => le_add_tsub
    _ = _ := by
      rw [ClaudeWCT.Numerics.Law.lawAvg_add, ClaudeWCT.Numerics.Law.lawAvg_const (S0 horizon).law (S0 horizon).law_sum]
noncomputable def ledger54 (R : Nat) (targets X : List HashOutput) (slack : Nat) : ENNReal :=
  (targets.map fun N => (S0 horizon).forecast R X N).sum + (slack : ENNReal) * excessForecast54 horizon R X / 2 ^ 128
theorem ledger54_slack_succ (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    ledger54 horizon R targets X (slack + 1) =
      ledger54 horizon R targets X slack + excessForecast54 horizon R X / 2 ^ 128 := by
  unfold ledger54
  rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, ENNReal.add_div, add_assoc]
theorem ledger54_birth (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun a => ledger54 horizon R (targets ++ [a]) X slack) ≤
      ledger54 horizon R targets X (slack + 1) + (2031 / 1024 : ENNReal) / 2 ^ 128 := by
  have hfa : expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun a => (S0 horizon).forecast R X a) ≤
      ((2031 / 1024 : ENNReal) + excessForecast54 horizon R X) / 2 ^ 128 := by
    rw [BPORS.expected_uniform_eq_finiteAverage]
    exact average_forecast_le_54 horizon R X
  have hsplit : ∀ a, ledger54 horizon R (targets ++ [a]) X slack =
      ledger54 horizon R targets X slack + (S0 horizon).forecast R X a := by
    intro a
    simp only [ledger54, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
      List.sum_nil, add_zero]
    ring
  simp_rw [hsplit]
  rw [expectedValue_add, expectedValue_const (by simp : Pr[⊥ | ($ᵗ HashOutput : ProbComp HashOutput)] = 0),
    ledger54_slack_succ, add_assoc]
  exact add_le_add le_rfl (hfa.trans (by rw [ENNReal.add_div, add_comm]))
theorem ledger54_expose (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    expectedValue (S0 horizon).accepted (fun A => ledger54 horizon R targets (X ++ [A]) slack) =
      ledger54 horizon (R + 1) targets X slack := by
  unfold ledger54
  rw [expectedValue_add, CaseC.expectedValue_list_sum']
  refine congrArg₂ (· + ·) (congrArg List.sum ?_) ?_
  · apply List.map_congr_left
    intro N _
    exact (S0 horizon).forecast_step R X N
  · simp only [div_eq_mul_inv]
    rw [show (fun A : HashOutput => (slack : ENNReal) * excessForecast54 horizon R (X ++ [A]) * (2 ^ 128 : ENNReal)⁻¹) =
        fun A => (slack : ENNReal) * (2 ^ 128 : ENNReal)⁻¹ * excessForecast54 horizon R (X ++ [A]) by
      funext A; ring]
    rw [CaseC.pmf_expectedValue_left_mul, excessForecast54_step]
    ring
theorem ledger54_freshPrice (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    (S0 horizon).freshPrice (fun A => ledger54 horizon R targets (X ++ [A]) slack) =
      ledger54 horizon (R + 1) targets X slack := by
  rw [← (S0 horizon).expected_accepted, ledger54_expose]
theorem ledger54_search (secret : BitVec 256) (rho : Digest) (message : Message) (fuel : Nat)
    (hlimit : fuel ≤ 2 ^ 32) (cache : Sampling.RCache)
    (hreject : Sampling.CachedTrialsReject (Sampling.digestTrial rho message) (S0 horizon).decode 0 (2 ^ 32) cache)
    (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    expectedValue (Sampling.roRun secret ((S0 horizon).search rho message 0 fuel) cache)
      (fun result => result.1.elim (ledger54 horizon (R + 1) targets X slack)
        (fun found => ledger54 horizon R targets (X ++ [found.2]) slack)) ≤
      ledger54 horizon (R + 1) targets X slack :=
  (S0 horizon).search_le_price secret rho message fuel hlimit cache hreject _ _ _ le_rfl
    (ledger54_freshPrice horizon R targets X slack).le
theorem ledger54_win (R : Nat) (targets X : List HashOutput) (slack : Nat) (N : HashOutput) (hN : N ∈ targets)
    (hadm : WCT9.admissible N = true) (hcov : Covered X N) :
    1 ≤ ledger54 horizon R targets X slack :=
  calc
    (1 : ENNReal) ≤ (S0 horizon).score X N := (S0 horizon).one_le_score X N hadm hcov
    _ ≤ (S0 horizon).forecast R X N := (S0 horizon).score_le_forecast R X N
    _ ≤ (targets.map fun N => (S0 horizon).forecast R X N).sum := List.le_sum_of_mem (List.mem_map_of_mem hN)
    _ ≤ _ := le_self_add
noncomputable def corePotential54 (b : BankCore) : ENNReal :=
  if horizon < b.exposures.length then 0
  else if b.reused = true then 1 + b.reuse
  else ledger54 horizon (horizon - b.exposures.length) b.targets b.exposures b.slack + b.reuse
theorem wct_core_birth_54 (b : BankCore) (s : Nat) (hs : b.slack = s + 1) (C' : HashOutput → ENNReal)
    (hC : ∀ N, C' N ≤ b.reuse + (S0 horizon).admInd N / 2 ^ 128) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
        (fun N => corePotential54 horizon { b with targets := b.targets ++ [N], slack := s, reuse := C' N }) ≤
      corePotential54 horizon b + (127 / 64 : ENNReal) / 2 ^ 128 := by
  have hadm : expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun N => (S0 horizon).admInd N / 2 ^ 128) ≤
      (S0 horizon).admBound / 2 ^ 128 := by
    simp only [div_eq_mul_inv]
    rw [expectedValue_mul_const]
    exact mul_le_mul' (by simpa [div_eq_mul_inv] using (S0 horizon).expected_admInd_tight) le_rfl
  have h54_adm : (S0 horizon).admBound ≤ 127 / 64 := by
    change (1 / 1024 : ENNReal) ≤ 127 / 64
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_div]
  have h54_sum : (2031 / 1024 : ENNReal) + (S0 horizon).admBound ≤ 127 / 64 := by
    change (2031 / 1024 : ENNReal) + 1 / 1024 ≤ 127 / 64
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_inv,
      ENNReal.toReal_ofNat, ENNReal.toReal_one]
    norm_num
  unfold corePotential54
  simp only
  by_cases hd : horizon < b.exposures.length
  · simp only [hd, if_true]
    exact (expectedValue_le_of_le _ fun _ => le_rfl).trans bot_le
  simp only [hd, if_false]
  by_cases hr : b.reused = true
  · simp only [hr, if_true]
    calc
      _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
            (fun N => (S0 horizon).admInd N / 2 ^ 128 + (1 + b.reuse)) :=
        expectedValue_mono _ fun N => (add_le_add le_rfl (hC N)).trans (le_of_eq (by ring))
      _ ≤ (S0 horizon).admBound / 2 ^ 128 + (1 + b.reuse) :=
        (CaseC.expectedValue_add_const_le _ _ _).trans (add_le_add hadm le_rfl)
      _ ≤ _ := by
        rw [add_comm]
        exact add_le_add le_rfl (ENNReal.div_le_div_right h54_adm _)
  · simp only [hr, Bool.false_eq_true, if_false]
    set R := horizon - b.exposures.length
    calc
      _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
          (fun N => (ledger54 horizon R (b.targets ++ [N]) b.exposures s + (S0 horizon).admInd N / 2 ^ 128) + b.reuse) :=
        expectedValue_mono _ fun N => (add_le_add le_rfl (hC N)).trans (le_of_eq (by ring))
      _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
          (fun N => ledger54 horizon R (b.targets ++ [N]) b.exposures s + (S0 horizon).admInd N / 2 ^ 128) + b.reuse :=
        CaseC.expectedValue_add_const_le _ _ _
      _ ≤ (ledger54 horizon R b.targets b.exposures (s + 1) + (2031 / 1024 : ENNReal) / 2 ^ 128 +
            (S0 horizon).admBound / 2 ^ 128) + b.reuse := by
        rw [expectedValue_add]
        exact add_le_add (add_le_add (ledger54_birth horizon R b.targets b.exposures s) hadm) le_rfl
      _ ≤ _ := by
        rw [← hs, add_assoc (ledger54 _ _ _ _ _), ← ENNReal.add_div,
          show ledger54 horizon R b.targets b.exposures b.slack +
            ((2031 / 1024 : ENNReal) + (S0 horizon).admBound) / 2 ^ 128 + b.reuse =
            (ledger54 horizon R b.targets b.exposures b.slack + b.reuse) +
            ((2031 / 1024 : ENNReal) + (S0 horizon).admBound) / 2 ^ 128 by ring]
        exact add_le_add le_rfl (ENNReal.div_le_div_right h54_sum _)
theorem wct_core_sign_54 (b : BankCore) (cache : Sampling.RCache) (m : Message) (C' : ENNReal)
    (hC : C' + (S0 horizon).reuseMass cache m ≤ b.reuse) (secret : BitVec 256) (fuel : Nat)
    (hfuel : fuel ≤ 2 ^ 32) :
    expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho =>
      if (S0 horizon).Reuse cache rho m then
        corePotential54 horizon { b with reused := true, reuse := C' }
      else expectedValue (Sampling.roRun secret (WCT9.digestSearch rho m 0 fuel) cache)
        (fun result => corePotential54 horizon (b.expose C' (result.1.map Prod.snd)))) ≤
      corePotential54 horizon b := by
  have h : expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho =>
      if (S0 horizon).Reuse cache rho m then corePotential54 horizon { b with reused := true, reuse := C' }
      else expectedValue (Sampling.roRun secret ((S0 horizon).search rho m 0 fuel) cache)
        (fun result => corePotential54 horizon (b.expose C' (result.1.map Prod.snd)))) ≤
      corePotential54 horizon b := by
    have hlenA : ∀ (o : Option HashOutput), b.exposures.length ≤ (b.exposures ++ o.toList).length := by
      intro o; simp
    by_cases hd : horizon < b.exposures.length
    · apply expectedValue_le_of_le
      intro rho
      have h0 : ∀ (o : Option HashOutput), corePotential54 horizon (b.expose C' o) = 0 := by
        intro o
        unfold corePotential54 BankCore.expose
        simp only
        rw [if_pos (lt_of_lt_of_le hd (hlenA o))]
      split_ifs
      · unfold corePotential54; simp only; rw [if_pos hd]; exact bot_le
      · exact (expectedValue_le_of_le _ fun result => (h0 _).le).trans bot_le
    by_cases hr : b.reused = true
    · have hb : corePotential54 horizon b = 1 + b.reuse := by unfold corePotential54; simp [hd, hr]
      rw [hb]
      apply expectedValue_le_of_le
      intro rho
      have hle : ∀ (o : Option HashOutput), corePotential54 horizon (b.expose C' o) ≤ 1 + b.reuse := by
        intro o
        unfold corePotential54 BankCore.expose
        simp only [hr, if_true]
        split_ifs
        · exact bot_le
        · exact add_le_add le_rfl (le_of_add_le_left hC)
      split_ifs
      · unfold corePotential54; simp only [hd, if_false, if_true]; exact add_le_add le_rfl (le_of_add_le_left hC)
      · exact expectedValue_le_of_le _ fun result => hle _
    have hr' : b.reused = false := by simpa using hr
    set R0 := horizon - b.exposures.length with hR0
    have hb : corePotential54 horizon b = ledger54 horizon R0 b.targets b.exposures b.slack + b.reuse := by
      unfold corePotential54; simp only [hd, hr', if_false, Bool.false_eq_true]; rfl
    have hsearch : ∀ rho, ¬(S0 horizon).Reuse cache rho m →
        expectedValue (Sampling.roRun secret ((S0 horizon).search rho m 0 fuel) cache)
          (fun result => corePotential54 horizon (b.expose C' (result.1.map Prod.snd))) ≤
            ledger54 horizon R0 b.targets b.exposures b.slack + C' := by
      intro rho hnr
      have hrej : Sampling.CachedTrialsReject (Sampling.digestTrial rho m) (S0 horizon).decode 0 (2 ^ 32) cache := by
        unfold FtsBankSpec.Reuse at hnr; push Not at hnr; exact hnr
      by_cases hlen : b.exposures.length < horizon
      · obtain ⟨R, hR⟩ : ∃ R, R0 = R + 1 := ⟨R0 - 1, by omega⟩
        calc
          _ ≤ expectedValue (Sampling.roRun secret ((S0 horizon).search rho m 0 fuel) cache)
              (fun result => result.1.elim (ledger54 horizon (R + 1) b.targets b.exposures b.slack)
                (fun found => ledger54 horizon R b.targets (b.exposures ++ [found.2]) b.slack) + C') := by
            apply expectedValue_mono
            intro result
            rcases result with ⟨_ | found, cache'⟩
            · unfold corePotential54 BankCore.expose
              simp only [Option.map_none, Option.toList_none, List.append_nil, hd, if_false, hr',
                Bool.false_eq_true, Option.elim_none]
              rw [← hR]
            · unfold corePotential54 BankCore.expose
              have hl1 : (b.exposures ++ [found.2]).length = b.exposures.length + 1 := by simp
              have hnd : ¬horizon < (b.exposures ++ [found.2]).length := by omega
              simp only [Option.map_some, Option.toList_some, hnd, if_false, hr', Bool.false_eq_true,
                Option.elim_some]
              rw [show horizon - (b.exposures ++ [found.2]).length = R by omega]
          _ ≤ ledger54 horizon (R + 1) b.targets b.exposures b.slack + C' :=
            (CaseC.expectedValue_add_const_le _ _ _).trans
              (add_le_add (ledger54_search horizon secret rho m fuel hfuel cache hrej R b.targets b.exposures b.slack) le_rfl)
          _ = _ := by rw [hR]
      · apply expectedValue_le_of_le
        intro result
        rcases result with ⟨_ | found, cache'⟩
        · unfold corePotential54 BankCore.expose
          simp only [Option.map_none, Option.toList_none, List.append_nil, hd, if_false, hr', Bool.false_eq_true]
          exact le_rfl
        · unfold corePotential54 BankCore.expose
          have hnd : horizon < (b.exposures ++ [found.2]).length := by simp; omega
          simp only [Option.map_some, Option.toList_some, hnd, if_true]
          exact bot_le
    rw [hb]
    calc
      _ ≤ expectedValue ($ᵗ Digest : ProbComp Digest)
          (fun rho => (if (S0 horizon).Reuse cache rho m then 1 else 0) +
            (ledger54 horizon R0 b.targets b.exposures b.slack + C')) := by
        apply expectedValue_mono
        intro rho
        by_cases hre : (S0 horizon).Reuse cache rho m
        · rw [if_pos hre, if_pos hre]
          unfold corePotential54
          simp only [hd, if_false, if_true]
          exact add_le_add le_rfl le_add_self
        · rw [if_neg hre, if_neg hre, zero_add]
          exact hsearch rho hre
      _ ≤ (S0 horizon).reuseMass cache m + (ledger54 horizon R0 b.targets b.exposures b.slack + C') :=
        (CaseC.expectedValue_add_const_le _ _ _).trans (add_le_add ((S0 horizon).reuse_probability_le cache m) le_rfl)
      _ ≤ _ := by
        rw [add_comm (ledger54 _ _ _ _ _), ← add_assoc, add_comm ((S0 horizon).reuseMass cache m),
          add_comm _ (ledger54 _ _ _ _ _)]
        exact add_le_add le_rfl hC
  simp only [← wct_digestSearch_public (S0 horizon) rfl] at h
  exact h
theorem wct_core_win_54 (b : BankCore) (halive : ¬horizon < b.exposures.length)
    (h : b.reused = true ∨ ∃ N ∈ b.targets, WCT9.admissible N = true ∧ Covered b.exposures N) :
    1 ≤ corePotential54 horizon b := by
  unfold corePotential54
  rw [if_neg halive]
  by_cases hr : b.reused = true
  · rw [if_pos hr]; exact le_self_add
  · rw [if_neg hr]
    obtain ⟨N, hN, hadm, hcov⟩ := h.resolve_left hr
    exact (ledger54_win horizon _ _ _ _ N hN hadm hcov).trans le_self_add
end ClaudeWCT.Bank.WCT
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (State Cell IsDigestRow)
open SigGolfCandidate.T3.Security.LargeCoupling (digestTrial_inj tsum_trial_indicator_le expectedValue_uniform_reply)
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
structure BankInv (U : Finset HashInput) (ws : LargeResidual.State WCoord (Cell U)) (st : RouterState) : Prop where
  calls : ws.counters.calls = st.calls
  mass : ws.counters.mass ≤ ws.counters.calls
  births : st.births.length ≤ st.calls
  nonce : ∀ m, st.memo.lookup m = none → ws.candidates (.inr m) = Finset.univ
  fresh : ∀ (X : HashInput) (hX : X ∈ U), IsDigestRow X → X ∉ st.seen → X ∉ st.trials → ws.rows ⟨X, hX⟩ = none
  seenRows : ∀ (X : HashInput) (hX : X ∈ U), IsDigestRow X → X ∈ st.seen → X ∉ st.trials →
    ∃ y, st.cache X = some y ∧ ws.rows ⟨X, hX⟩ = some y
  bornSeen : ∀ p ∈ st.births, p.1 ∈ st.seen
  trials : ∀ X ∈ st.trials, ∃ rho m c, X = pad64 (digestInput rho m c) ∧ (st.memo.lookup m).isSome
def _root_.ClaudeWCT.W9.T3.Security.LargeResidual.RouterState.born (st : RouterState) (X : HashInput)
    (y : LargeResidual.HashOutput) : RouterState :=
  { st.after X with births := (X, y) :: st.births }
theorem cache_birth (st : RouterState) (X Z : HashInput) (y : LargeResidual.HashOutput) :
    (st.born X y).cache Z =
      if Z = X then some y else st.cache Z := by
  simp only [RouterState.born, RouterState.cache, List.lookup_cons]
  by_cases h : Z = X
  · subst h; simp
  · have hb : (Z == X) = false := by simpa using h
    rw [hb, if_neg h]
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (State Cell Probe Hit IsDigestRow runWith_map readState
  probeState)
open ClaudeWCT.W9.T3.Security.FamResidual (lazyRun lazy_pure)
open SigGolfCandidate.T3.Security.LargeCoupling (ev_bind_le ev_observe_le)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
section Frame
variable (U : Finset HashInput)
def QFrame (X : HashInput) (s s' : LargeResidual.State WCoord (Cell U)) : Prop :=
  (∀ row : Cell U, row.1 ≠ X → s'.rows row = s.rows row) ∧ s'.counters.calls = s.counters.calls + 1 ∧
    s'.counters.mass = s.counters.mass ∧ ∀ m : Message, s'.candidates (.inr m) = s.candidates (.inr m)
theorem QFrame.of_disc {X : HashInput} {s1 s2 s3 : LargeResidual.State WCoord (Cell U)} (h1 : DiscFrame U s1 s2)
    (h2 : QFrame U X s2 s3) : QFrame U X s1 s3 :=
  ⟨fun row hr => (h2.1 row hr).trans (by rw [h1.1]), by rw [h2.2.1, h1.2.1], by rw [h2.2.2.1, h1.2.1],
    fun m => (h2.2.2.2 m).trans (h1.2.2 m)⟩
def InlTest (test : Probe WCoord) : Prop :=
  (∀ g ∈ test.guess, ∃ c : Coord, g.1 = Sum.inl c) ∧ ∀ p, test.hit = .label p → ∃ c : Coord, p = Sum.inl c
theorem restrict_inr (test : Probe WCoord) (htest : InlTest test) (cand : WCoord → Finset Digest)
    (y : LargeResidual.HashOutput) (m : Message) :
    (test.effF cand).restrict cand y (.inr m) = cand (.inr m) := by
  have hg : (test.effF cand).guessRestrict cand (.inr m) = cand (.inr m) := by
    unfold LargeResidual.Probe.guessRestrict
    cases hgs : (test.effF cand).guess with
    | none => rfl
    | some g =>
        have hmem : g ∈ test.guess := by
          by_cases hsel : test.hit.isSelected = true
          · simp [LargeResidual.Probe.effF, hsel] at hgs
          · simp only [LargeResidual.Probe.effF, hsel, if_false] at hgs
            exact (Option.filter_eq_some_iff.mp hgs).1
        obtain ⟨c, hc⟩ := htest.1 g hmem
        simp only [eraseTableValue]
        rw [Function.update_of_ne (by rw [hc]; simp)]
  unfold LargeResidual.Probe.restrict
  have hh : (test.effF cand).hit = test.hit := rfl
  cases hhit : test.hit with
  | label p =>
      obtain ⟨c, hc⟩ := htest.2 p hhit
      rw [hh, hhit]
      simp only [LargeResidual.Hit.restrict, eraseTableValue]
      rw [Function.update_of_ne (by rw [hc]; simp), hg]
  | target t =>
      rw [hh, hhit]
      simp only [LargeResidual.Hit.restrict]
      exact hg
  | selectedTarget t pickLow =>
      rw [hh, hhit]
      simp only [LargeResidual.Hit.restrict]
      exact hg
variable (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
def OutcomeLe {α : Type} (X : HashInput) (s : LargeResidual.State WCoord (Cell U))
    (g : Option α × LargeResidual.State WCoord (Cell U) → ENNReal) (B : ENNReal) : Prop :=
  (∀ v s', QFrame U X s s' → g (some v, s') ≤ B) ∧ ∀ s', s'.counters.mass = s.counters.mass → g (none, s') ≤ B
theorem OutcomeLe.map {α β : Type} {X : HashInput} {s : LargeResidual.State WCoord (Cell U)}
    {g : Option β × LargeResidual.State WCoord (Cell U) → ENNReal} {B : ENNReal} (f : α → β)
    (h : OutcomeLe U X s g B) : OutcomeLe U X s (fun r => g (r.1.map f, r.2)) B :=
  ⟨fun v s' hs => h.1 (f v) s' hs, fun s' hs => h.2 s' hs⟩
theorem OutcomeLe.of_disc {α : Type} {X : HashInput} {s s1 : LargeResidual.State WCoord (Cell U)}
    {g : Option α × LargeResidual.State WCoord (Cell U) → ENNReal} {B : ENNReal} (hd : DiscFrame U s s1)
    (h : OutcomeLe U X s g B) : OutcomeLe U X s1 g B :=
  ⟨fun v s' hs => h.1 v s' (QFrame.of_disc U hd hs), fun s' hs => h.2 s' (by rw [hs, hd.2.1])⟩
end Frame
section Invariant
variable {U : Finset HashInput}
theorem BankInv.after {ws ws' : LargeResidual.State WCoord (Cell U)} {st : RouterState} (h : BankInv U ws st)
    (X : HashInput) (hX : ¬(X ∈ U ∧ IsDigestRow X)) (hf : QFrame U X ws ws') : BankInv U ws' (st.after X) := by
  have hne : ∀ X' (hX' : X' ∈ U), IsDigestRow X' → X' ≠ X := fun X' hX' hd he => hX ⟨he ▸ hX', he ▸ hd⟩
  refine ⟨by rw [hf.2.1, h.calls]; rfl, by rw [hf.2.2.1, hf.2.1]; exact (h.mass).trans (Nat.le_succ _),
    (h.births).trans (Nat.le_succ _), fun m hm => by rw [hf.2.2.2 m]; exact h.nonce m hm, ?_, ?_, ?_, h.trials⟩
  · intro X' hX' hd hs ht
    rw [hf.1 ⟨X', hX'⟩ (hne X' hX' hd)]
    exact h.fresh X' hX' hd (fun hm => hs (List.mem_cons_of_mem _ hm)) ht
  · intro X' hX' hd hs ht
    rw [hf.1 ⟨X', hX'⟩ (hne X' hX' hd)]
    have hs' : X' ∈ st.seen := by
      rcases List.mem_cons.mp hs with he | hm
      · exact absurd he (hne X' hX' hd)
      · exact hm
    exact h.seenRows X' hX' hd hs' ht
  · intro p hp
    exact List.mem_cons_of_mem _ (h.bornSeen p hp)
theorem BankInv.cache_none {ws : LargeResidual.State WCoord (Cell U)} {st : RouterState} (h : BankInv U ws st)
    {X : HashInput} (hs : X ∉ st.seen) : st.cache X = none := by
  unfold RouterState.cache
  apply List.lookup_eq_none_iff.mpr
  intro p hp
  simp only [bne_iff_ne, ne_eq]
  intro he
  exact hs (he ▸ h.bornSeen p hp)
theorem BankInv.born {ws : LargeResidual.State WCoord (Cell U)} {st : RouterState} (h : BankInv U ws st) (q : Nat)
    (X : HashInput) (hX : X ∈ U) (hd : IsDigestRow X) (hs : X ∉ st.seen) (y : LargeResidual.HashOutput) :
    BankInv U (readState q ws ⟨X, hX⟩ y .mass) (st.born X y) := by
  refine ⟨?_, ?_, ?_, fun m hm => h.nonce m hm, ?_, ?_, ?_, h.trials⟩
  · simp only [readState, LargeResidual.Counters.charge, RouterState.born, RouterState.after, h.calls]
  · simp only [readState, LargeResidual.Counters.charge]
    have := h.mass
    split_ifs <;> omega
  · simp only [RouterState.born, RouterState.after, List.length_cons]
    exact Nat.succ_le_succ h.births
  · intro X' hX' hd' hs' ht'
    have hne : X' ≠ X := fun he => hs' (by rw [he]; exact List.mem_cons_self)
    simp only [readState]
    rw [Function.update_of_ne (fun he => hne (congrArg Subtype.val he))]
    exact h.fresh X' hX' hd' (fun hm => hs' (List.mem_cons_of_mem _ hm)) ht'
  · intro X' hX' hd' hs' ht'
    by_cases hxe : X' = X
    · subst hxe
      refine ⟨y, ?_, ?_⟩
      · rw [cache_birth, if_pos rfl]
      · simp only [readState, Function.update_self]
    · have hs2 : X' ∈ st.seen := by
        rcases List.mem_cons.mp hs' with he | hm
        · exact absurd he hxe
        · exact hm
      obtain ⟨v, hv1, hv2⟩ := h.seenRows X' hX' hd' hs2 ht'
      refine ⟨v, ?_, ?_⟩
      · rw [cache_birth, if_neg hxe]; exact hv1
      · simp only [readState]
        rw [Function.update_of_ne (fun he => hxe (congrArg Subtype.val he))]
        exact hv2
  · intro p hp
    rcases List.mem_cons.mp hp with he | hm
    · rw [he]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (h.bornSeen p hm)
end Invariant
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (State Cell Probe Hit IsDigestRow readState)
open ClaudeWCT.W9.T3.Security.FamResidual (lazyRun lazy_pure)
open SigGolfCandidate.T3.Security.LargeCoupling (ev_bind_le birth_pay)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
section Step
variable {U : Finset HashInput}
theorem BankInv.after' {ws ws' : LargeResidual.State WCoord (Cell U)} {st : RouterState} (h : BankInv U ws st)
    (X : HashInput) (hrows : ∀ row : Cell U, row.1 ≠ X → ws'.rows row = ws.rows row)
    (hX : ∀ hX : X ∈ U, IsDigestRow X → X ∉ st.trials → ∃ y, st.cache X = some y ∧ ws'.rows ⟨X, hX⟩ = some y)
    (hcalls : ws'.counters.calls = ws.counters.calls + 1) (hmass : ws'.counters.mass ≤ ws'.counters.calls)
    (hcand : ∀ m : Message, ws'.candidates (.inr m) = ws.candidates (.inr m)) : BankInv U ws' (st.after X) := by
  refine ⟨by rw [hcalls, h.calls]; rfl, hmass, (h.births).trans (Nat.le_succ _),
    fun m hm => by rw [hcand m]; exact h.nonce m hm, ?_, ?_, ?_, h.trials⟩
  · intro X' hX' hd hs ht
    have hne : X' ≠ X := fun he => hs (by rw [he]; exact List.mem_cons_self)
    rw [hrows ⟨X', hX'⟩ hne]
    exact h.fresh X' hX' hd (fun hm => hs (List.mem_cons_of_mem _ hm)) ht
  · intro X' hX' hd hs ht
    by_cases hne : X' = X
    · subst hne
      exact hX hX' hd ht
    · rw [hrows ⟨X', hX'⟩ hne]
      have hs' : X' ∈ st.seen := by
        rcases List.mem_cons.mp hs with he | hm
        · exact absurd he hne
        · exact hm
      exact h.seenRows X' hX' hd hs' ht
  · intro p hp
    exact List.mem_cons_of_mem _ (h.bornSeen p hp)
theorem inlTest_guess (c : Coord) (v : Digest) (hit : Hit WCoord) (hh : ∀ p, hit = .label p → ∃ c' : Coord, p = .inl c') :
    InlTest ⟨some (.inl c, v), hit⟩ :=
  ⟨fun g hg => ⟨c, by cases hg; rfl⟩, hh⟩
theorem inlTest_none (hit : Hit WCoord) (hh : ∀ p, hit = .label p → ∃ c' : Coord, p = .inl c') :
    InlTest ⟨none, hit⟩ :=
  ⟨fun g hg => absurd hg (by simp), hh⟩
theorem hit_label_inl (c : Coord) : ∀ p, (LargeResidual.Hit.label (Sum.inl c) : Hit WCoord) = .label p → ∃ c' : Coord, p = .inl c' :=
  fun p hp => ⟨c, by cases hp; rfl⟩
theorem hit_encodingHit (lay : Layer) (t : Digest) :
    ∀ p, (encodingHit lay t : Hit WCoord) = .label p → ∃ c' : Coord, p = .inl c' := by
  intro p hp
  simp [encodingHit] at hp
theorem hit_encodingHitSel (lay : Layer) (t : Digest) :
    ∀ p, (encodingHitSel lay t : Hit WCoord) = .label p → ∃ c' : Coord, p = .inl c' := by
  intro p hp
  simp [encodingHitSel] at hp
variable (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
end Step
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (State Cell IsDigestRow readState)
open ClaudeWCT.W9.T3.Security.FamResidual (lazyRun lazy_pure)
open SigGolfCandidate.T3.Security.LargeCoupling (trial_ne reply_of_some reply_of_none
  expectedValue_uniform_ro)
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
section Search
variable {U : Finset HashInput} (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
  (a : AuxData) (rho : Digest) (m : Message)
def SearchFrame (c fuel : Nat) (found : Option (BitVec 32 × LargeResidual.HashOutput))
    (s s' : LargeResidual.State WCoord (Cell U)) : Prop :=
  s'.candidates = s.candidates ∧ s'.counters = s.counters ∧
    (∀ k' out, found = some (k', out) → c ≤ k'.toNat ∧ k'.toNat < c + fuel) ∧
    ∀ row : Cell U, s'.rows row ≠ s.rows row → ∃ k, c ≤ k ∧ k < c + fuel ∧
      row.1 = pad64 (digestInput rho m (BitVec.ofNat 32 k)) ∧ ∀ k' out, found = some (k', out) → k ≤ k'.toNat
end Search
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (State Cell IsDigestRow disclosedState)
open ClaudeWCT.W9.T3.Security.FamResidual (lazyRun lazy_pure expectedValue_discLaw_le)
open SigGolfCandidate.T3.Security.LargeCoupling (ev_bind_le ev_runWith_bind expectedValue_cell_univ
  digestRow_isDigest digestRow_mem)
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeCouplingBankSign : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
section Sign
variable {U : Finset HashInput}
theorem BankInv.disc {ws ws' : LargeResidual.State WCoord (Cell U)} {st : RouterState} (h : BankInv U ws st)
    (hd : DiscFrame U ws ws') (d : List Coord) : BankInv U ws' { st with disclosed := d } := by
  obtain ⟨hr, hc, hn⟩ := hd
  refine ⟨by rw [hc]; exact h.calls, by rw [hc]; exact h.mass, h.births, fun m hm => by rw [hn m]; exact h.nonce m hm,
    fun X hX hd hs ht => by rw [hr]; exact h.fresh X hX hd hs ht,
    fun X hX hd hs ht => by rw [hr]; exact h.seenRows X hX hd hs ht, h.bornSeen, h.trials⟩
theorem BankInv.discloseSigned {ws : LargeResidual.State WCoord (Cell U)} {st : RouterState} (h : BankInv U ws st)
    (q : Nat) (m : Message) (hm : (st.memo.lookup m).isSome) (rho : Digest) :
    BankInv U (disclosedState q ws (.inr m) rho .none) st := by
  refine ⟨h.calls, h.mass, h.births, fun m' hm' => ?_, h.fresh, h.seenRows, h.bornSeen, h.trials⟩
  have hne : m' ≠ m := by
    intro he; subst he; rw [hm'] at hm; cases hm
  simp only [disclosedState, discloseTableValue]
  rw [Function.update_of_ne (by simpa using hne)]
  exact h.nonce m' hm'
theorem mem_trialRows (rho : Digest) (m : Message) (found : Option (BitVec 32 × LargeResidual.HashOutput)) (k : Nat)
    (hk : k < WCT9.digestAttemptLimit) (hf : ∀ k' out, found = some (k', out) → k ≤ k'.toNat) :
    pad64 (digestInput rho m (BitVec.ofNat 32 k)) ∈ trialRows rho m found := by
  unfold trialRows
  apply List.mem_map.mpr
  refine ⟨k, List.mem_range.mpr ?_, rfl⟩
  cases found with
  | none => exact hk
  | some f =>
      obtain ⟨k', out⟩ := f
      have := hf k' out rfl
      dsimp only
      omega
theorem BankInv.agree {ws : LargeResidual.State WCoord (Cell U)} {st : RouterState} (h : BankInv U ws st)
    (hUpub : SeccLaw.publicUniverse ⊆ U) (m : Message) (hm : st.memo.lookup m = none) (rho : Digest) (k : Nat) :
    ws.rows ⟨_, digestRow_mem hUpub rho m (BitVec.ofNat 32 k)⟩ =
      st.cache (pad64 (digestInput rho m (BitVec.ofNat 32 k))) := by
  have hd : IsDigestRow (pad64 (digestInput rho m (BitVec.ofNat 32 k))) := digestRow_isDigest _ _ _
  have ht : pad64 (digestInput rho m (BitVec.ofNat 32 k)) ∉ st.trials := by
    intro hX
    obtain ⟨rho', m', c', hX', hs'⟩ := h.trials _ hX
    obtain ⟨-, -, hmm⟩ := BPB.digestInput_injective hX'
    subst hmm
    rw [hm] at hs'
    cases hs'
  by_cases hs : pad64 (digestInput rho m (BitVec.ofNat 32 k)) ∈ st.seen
  · obtain ⟨y, h1, h2⟩ := h.seenRows _ _ hd hs ht
    rw [h1, h2]
  · rw [h.fresh _ _ hd hs ht, h.cache_none hs]
variable (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
end Sign
end ClaudeWCT.W9.T3.Security.LargeCoupling
end

namespace ClaudeWCT.Bank.Flexible
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open CaseC (BankCore BankCore.expose)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpec P)
variable (θ : ENNReal) (horizon : Nat)
noncomputable def excessForecast (horizon : Nat) (R : Nat) (X : List HashOutput) : ENNReal :=
  ClaudeWCT.Numerics.Law.lawAvg S.law R
    (fun W => S.price (S.proposals X ++ W) - θ)
theorem excessForecast_step (R : Nat) (X : List HashOutput) :
    expectedValue S.accepted (fun A => excessForecast S θ horizon R (X ++ [A])) =
      excessForecast S θ horizon (R + 1) X := by
  unfold excessForecast
  rw [ClaudeWCT.Numerics.Law.lawAvg_succ]
  have hA (A : HashOutput) : ClaudeWCT.Numerics.Law.lawAvg S.law R
      (fun W => S.price (S.proposals (X ++ [A]) ++ W) - θ) =
      (fun p : P => ClaudeWCT.Numerics.Law.lawAvg S.law R
        (fun W => S.price (S.proposals X ++ p :: W) - θ))
        (S.proposal A) := by
    simp [FtsBankSpec.proposals, List.map_append, List.append_assoc]
  simp_rw [hA]
  exact S.expected_accepted_proposal (fun p => ClaudeWCT.Numerics.Law.lawAvg S.law R
    (fun W => S.price (S.proposals X ++ p :: W) - θ))
theorem average_forecast_le (R : Nat) (X : List HashOutput) :
    BPORS.finiteAverage (fun N : HashOutput => S.forecast R X N) ≤
      (θ + excessForecast S θ horizon R X) / 2 ^ 128 := by
  rw [S.average_forecast]
  apply ENNReal.div_le_div_right
  unfold excessForecast
  calc
    _ ≤ ClaudeWCT.Numerics.Law.lawAvg S.law R
          (fun W => θ + (S.price (S.proposals X ++ W) - θ)) :=
      ClaudeWCT.Numerics.Law.lawAvg_mono S.law R fun W => le_add_tsub
    _ = _ := by
      rw [ClaudeWCT.Numerics.Law.lawAvg_add, ClaudeWCT.Numerics.Law.lawAvg_const S.law S.law_sum]
noncomputable def ledger (R : Nat) (targets X : List HashOutput) (slack : Nat) : ENNReal :=
  (targets.map fun N => S.forecast R X N).sum + (slack : ENNReal) * excessForecast S θ horizon R X / 2 ^ 128
theorem ledger_slack_succ (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    ledger S θ horizon R targets X (slack + 1) =
      ledger S θ horizon R targets X slack + excessForecast S θ horizon R X / 2 ^ 128 := by
  unfold ledger
  rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, ENNReal.add_div, add_assoc]
theorem ledger_birth (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun a => ledger S θ horizon R (targets ++ [a]) X slack) ≤
      ledger S θ horizon R targets X (slack + 1) + θ / 2 ^ 128 := by
  have hfa : expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun a => S.forecast R X a) ≤
      (θ + excessForecast S θ horizon R X) / 2 ^ 128 := by
    rw [BPORS.expected_uniform_eq_finiteAverage]
    exact average_forecast_le S θ horizon R X
  have hsplit : ∀ a, ledger S θ horizon R (targets ++ [a]) X slack =
      ledger S θ horizon R targets X slack + S.forecast R X a := by
    intro a
    simp only [ledger, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
      List.sum_nil, add_zero]
    ring
  simp_rw [hsplit]
  rw [expectedValue_add, expectedValue_const (by simp : Pr[⊥ | ($ᵗ HashOutput : ProbComp HashOutput)] = 0),
    ledger_slack_succ S θ, add_assoc]
  exact add_le_add le_rfl (hfa.trans (by rw [ENNReal.add_div, add_comm]))
theorem ledger_expose (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    expectedValue S.accepted (fun A => ledger S θ horizon R targets (X ++ [A]) slack) =
      ledger S θ horizon (R + 1) targets X slack := by
  unfold ledger
  rw [expectedValue_add, CaseC.expectedValue_list_sum']
  refine congrArg₂ (· + ·) (congrArg List.sum ?_) ?_
  · apply List.map_congr_left
    intro N _
    exact S.forecast_step R X N
  · simp only [div_eq_mul_inv]
    rw [show (fun A : HashOutput => (slack : ENNReal) * excessForecast S θ horizon R (X ++ [A]) * (2 ^ 128 : ENNReal)⁻¹) =
        fun A => (slack : ENNReal) * (2 ^ 128 : ENNReal)⁻¹ * excessForecast S θ horizon R (X ++ [A]) by
      funext A; ring]
    rw [CaseC.pmf_expectedValue_left_mul, excessForecast_step S θ]
    ring
theorem ledger_freshPrice (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    S.freshPrice (fun A => ledger S θ horizon R targets (X ++ [A]) slack) =
      ledger S θ horizon (R + 1) targets X slack := by
  rw [← S.expected_accepted, ledger_expose S θ]
theorem ledger_search (secret : BitVec 256) (rho : Digest) (message : Message) (fuel : Nat)
    (hlimit : fuel ≤ 2 ^ 32) (cache : Sampling.RCache)
    (hreject : Sampling.CachedTrialsReject (Sampling.digestTrial rho message) S.decode 0 (2 ^ 32) cache)
    (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    expectedValue (Sampling.roRun secret (S.search rho message 0 fuel) cache)
      (fun result => result.1.elim (ledger S θ horizon (R + 1) targets X slack)
        (fun found => ledger S θ horizon R targets (X ++ [found.2]) slack)) ≤
      ledger S θ horizon (R + 1) targets X slack :=
  S.search_le_price secret rho message fuel hlimit cache hreject _ _ _ le_rfl
    (ledger_freshPrice S θ horizon R targets X slack).le
theorem ledger_win (R : Nat) (targets X : List HashOutput) (slack : Nat) (N : HashOutput) (hN : N ∈ targets)
    (hadm : S.admissible N = true) (hcov : S.covered X N) :
    1 ≤ ledger S θ horizon R targets X slack :=
  calc
    (1 : ENNReal) ≤ S.score X N := S.one_le_score X N hadm hcov
    _ ≤ S.forecast R X N := S.score_le_forecast R X N
    _ ≤ (targets.map fun N => S.forecast R X N).sum := List.le_sum_of_mem (List.mem_map_of_mem hN)
    _ ≤ _ := le_self_add
noncomputable def corePotential (b : BankCore) : ENNReal :=
  if horizon < b.exposures.length then 0
  else if b.reused = true then 1 + b.reuse
  else ledger S θ horizon (horizon - b.exposures.length) b.targets b.exposures b.slack + b.reuse
theorem core_birth (b : BankCore) (s : Nat) (hs : b.slack = s + 1) (C' : HashOutput → ENNReal)
    (hC : ∀ N, C' N ≤ b.reuse + S.admInd N / 2 ^ 128) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
        (fun N => corePotential S θ horizon { b with targets := b.targets ++ [N], slack := s, reuse := C' N }) ≤
      corePotential S θ horizon b + (θ + S.admBound) / 2 ^ 128 := by
  have hadm : expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun N => S.admInd N / 2 ^ 128) ≤
      S.admBound / 2 ^ 128 := by
    simp only [div_eq_mul_inv]
    rw [expectedValue_mul_const]
    exact mul_le_mul' (by simpa [div_eq_mul_inv] using S.expected_admInd_tight) le_rfl
  have h54_adm : S.admBound ≤ θ + S.admBound := le_add_self
  have h54_sum : θ + S.admBound ≤ θ + S.admBound := le_rfl
  unfold corePotential
  simp only
  by_cases hd : horizon < b.exposures.length
  · simp only [hd, if_true]
    exact (expectedValue_le_of_le _ fun _ => le_rfl).trans bot_le
  simp only [hd, if_false]
  by_cases hr : b.reused = true
  · simp only [hr, if_true]
    calc
      _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
            (fun N => S.admInd N / 2 ^ 128 + (1 + b.reuse)) :=
        expectedValue_mono _ fun N => (add_le_add le_rfl (hC N)).trans (le_of_eq (by ring))
      _ ≤ S.admBound / 2 ^ 128 + (1 + b.reuse) :=
        (CaseC.expectedValue_add_const_le _ _ _).trans (add_le_add hadm le_rfl)
      _ ≤ _ := by
        rw [add_comm]
        exact add_le_add le_rfl (ENNReal.div_le_div_right h54_adm _)
  · simp only [hr, Bool.false_eq_true, if_false]
    set R := horizon - b.exposures.length
    calc
      _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
          (fun N => (ledger S θ horizon R (b.targets ++ [N]) b.exposures s + S.admInd N / 2 ^ 128) + b.reuse) :=
        expectedValue_mono _ fun N => (add_le_add le_rfl (hC N)).trans (le_of_eq (by ring))
      _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
          (fun N => ledger S θ horizon R (b.targets ++ [N]) b.exposures s + S.admInd N / 2 ^ 128) + b.reuse :=
        CaseC.expectedValue_add_const_le _ _ _
      _ ≤ (ledger S θ horizon R b.targets b.exposures (s + 1) + θ / 2 ^ 128 +
            S.admBound / 2 ^ 128) + b.reuse := by
        rw [expectedValue_add]
        exact add_le_add (add_le_add (ledger_birth S θ horizon R b.targets b.exposures s) hadm) le_rfl
      _ ≤ _ := by
        rw [← hs, add_assoc (ledger S θ _ _ _ _ _), ← ENNReal.add_div,
          show ledger S θ horizon R b.targets b.exposures b.slack +
            (θ + S.admBound) / 2 ^ 128 + b.reuse =
            (ledger S θ horizon R b.targets b.exposures b.slack + b.reuse) +
            (θ + S.admBound) / 2 ^ 128 by ring]
theorem core_sign (b : BankCore) (cache : Sampling.RCache) (m : Message) (C' : ENNReal)
    (hC : C' + S.reuseMass cache m ≤ b.reuse) (secret : BitVec 256) (fuel : Nat)
    (hfuel : fuel ≤ 2 ^ 32) :
    expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho =>
      if S.Reuse cache rho m then
        corePotential S θ horizon { b with reused := true, reuse := C' }
      else expectedValue (Sampling.roRun secret (S.search rho m 0 fuel) cache)
        (fun result => corePotential S θ horizon (b.expose C' (result.1.map Prod.snd)))) ≤
      corePotential S θ horizon b := by
  have h : expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho =>
      if S.Reuse cache rho m then corePotential S θ horizon { b with reused := true, reuse := C' }
      else expectedValue (Sampling.roRun secret (S.search rho m 0 fuel) cache)
        (fun result => corePotential S θ horizon (b.expose C' (result.1.map Prod.snd)))) ≤
      corePotential S θ horizon b := by
    have hlenA : ∀ (o : Option HashOutput), b.exposures.length ≤ (b.exposures ++ o.toList).length := by
      intro o; simp
    by_cases hd : horizon < b.exposures.length
    · apply expectedValue_le_of_le
      intro rho
      have h0 : ∀ (o : Option HashOutput), corePotential S θ horizon (b.expose C' o) = 0 := by
        intro o
        unfold corePotential BankCore.expose
        simp only
        rw [if_pos (lt_of_lt_of_le hd (hlenA o))]
      split_ifs
      · unfold corePotential; simp only; rw [if_pos hd]; exact bot_le
      · exact (expectedValue_le_of_le _ fun result => (h0 _).le).trans bot_le
    by_cases hr : b.reused = true
    · have hb : corePotential S θ horizon b = 1 + b.reuse := by unfold corePotential; simp [hd, hr]
      rw [hb]
      apply expectedValue_le_of_le
      intro rho
      have hle : ∀ (o : Option HashOutput), corePotential S θ horizon (b.expose C' o) ≤ 1 + b.reuse := by
        intro o
        unfold corePotential BankCore.expose
        simp only [hr, if_true]
        split_ifs
        · exact bot_le
        · exact add_le_add le_rfl (le_of_add_le_left hC)
      split_ifs
      · unfold corePotential; simp only [hd, if_false, if_true]; exact add_le_add le_rfl (le_of_add_le_left hC)
      · exact expectedValue_le_of_le _ fun result => hle _
    have hr' : b.reused = false := by simpa using hr
    set R0 := horizon - b.exposures.length with hR0
    have hb : corePotential S θ horizon b = ledger S θ horizon R0 b.targets b.exposures b.slack + b.reuse := by
      unfold corePotential; simp only [hd, hr', if_false, Bool.false_eq_true]; rfl
    have hsearch : ∀ rho, ¬S.Reuse cache rho m →
        expectedValue (Sampling.roRun secret (S.search rho m 0 fuel) cache)
          (fun result => corePotential S θ horizon (b.expose C' (result.1.map Prod.snd))) ≤
            ledger S θ horizon R0 b.targets b.exposures b.slack + C' := by
      intro rho hnr
      have hrej : Sampling.CachedTrialsReject (Sampling.digestTrial rho m) S.decode 0 (2 ^ 32) cache := by
        unfold FtsBankSpec.Reuse at hnr; push Not at hnr; exact hnr
      by_cases hlen : b.exposures.length < horizon
      · obtain ⟨R, hR⟩ : ∃ R, R0 = R + 1 := ⟨R0 - 1, by omega⟩
        calc
          _ ≤ expectedValue (Sampling.roRun secret (S.search rho m 0 fuel) cache)
              (fun result => result.1.elim (ledger S θ horizon (R + 1) b.targets b.exposures b.slack)
                (fun found => ledger S θ horizon R b.targets (b.exposures ++ [found.2]) b.slack) + C') := by
            apply expectedValue_mono
            intro result
            rcases result with ⟨_ | found, cache'⟩
            · unfold corePotential BankCore.expose
              simp only [Option.map_none, Option.toList_none, List.append_nil, hd, if_false, hr',
                Bool.false_eq_true, Option.elim_none]
              rw [← hR]
            · unfold corePotential BankCore.expose
              have hl1 : (b.exposures ++ [found.2]).length = b.exposures.length + 1 := by simp
              have hnd : ¬horizon < (b.exposures ++ [found.2]).length := by omega
              simp only [Option.map_some, Option.toList_some, hnd, if_false, hr', Bool.false_eq_true,
                Option.elim_some]
              rw [show horizon - (b.exposures ++ [found.2]).length = R by omega]
          _ ≤ ledger S θ horizon (R + 1) b.targets b.exposures b.slack + C' :=
            (CaseC.expectedValue_add_const_le _ _ _).trans
              (add_le_add (ledger_search S θ horizon secret rho m fuel hfuel cache hrej R b.targets b.exposures b.slack) le_rfl)
          _ = _ := by rw [hR]
      · apply expectedValue_le_of_le
        intro result
        rcases result with ⟨_ | found, cache'⟩
        · unfold corePotential BankCore.expose
          simp only [Option.map_none, Option.toList_none, List.append_nil, hd, if_false, hr', Bool.false_eq_true]
          exact le_rfl
        · unfold corePotential BankCore.expose
          have hnd : horizon < (b.exposures ++ [found.2]).length := by simp; omega
          simp only [Option.map_some, Option.toList_some, hnd, if_true]
          exact bot_le
    rw [hb]
    calc
      _ ≤ expectedValue ($ᵗ Digest : ProbComp Digest)
          (fun rho => (if S.Reuse cache rho m then 1 else 0) +
            (ledger S θ horizon R0 b.targets b.exposures b.slack + C')) := by
        apply expectedValue_mono
        intro rho
        by_cases hre : S.Reuse cache rho m
        · rw [if_pos hre, if_pos hre]
          unfold corePotential
          simp only [hd, if_false, if_true]
          exact add_le_add le_rfl le_add_self
        · rw [if_neg hre, if_neg hre, zero_add]
          exact hsearch rho hre
      _ ≤ S.reuseMass cache m + (ledger S θ horizon R0 b.targets b.exposures b.slack + C') :=
        (CaseC.expectedValue_add_const_le _ _ _).trans (add_le_add (S.reuse_probability_le cache m) le_rfl)
      _ ≤ _ := by
        rw [add_comm (ledger S θ _ _ _ _ _), ← add_assoc, add_comm (S.reuseMass cache m),
          add_comm _ (ledger S θ _ _ _ _ _)]
        exact add_le_add le_rfl hC
  exact h
theorem core_win (b : BankCore) (halive : ¬horizon < b.exposures.length)
    (h : b.reused = true ∨ ∃ N ∈ b.targets, S.admissible N = true ∧ S.covered b.exposures N) :
    1 ≤ corePotential S θ horizon b := by
  unfold corePotential
  rw [if_neg halive]
  by_cases hr : b.reused = true
  · rw [if_pos hr]; exact le_self_add
  · rw [if_neg hr]
    obtain ⟨N, hN, hadm, hcov⟩ := h.resolve_left hr
    exact (ledger_win S θ horizon _ _ _ _ N hN hadm hcov).trans le_self_add
theorem core_initial (rate : ENNReal) (hexc : ClaudeWCT.Numerics.Law.lawAvg S.law (2^32) (fun W => S.price W-θ) ≤ rate) (budget : Nat) :
    corePotential S θ (2 ^ 32) ⟨[], [], false, 0, budget⟩ ≤
      (budget : ENNReal) * rate / 2 ^ 128 := by
  unfold corePotential ledger excessForecast
  simp only [List.length_nil, Nat.not_lt_zero, if_false, Bool.false_eq_true, Nat.sub_zero, add_zero,
    List.map_nil, List.sum_nil, zero_add]
  apply ENNReal.div_le_div_right
  apply mul_le_mul' le_rfl
  exact hexc
end ClaudeWCT.Bank.Flexible

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord WCoord RouterState)
open SigGolfCandidate.T3.Security.LargeResidual (Cell IsDigestRow)
open SigGolfCandidate.T3.Security.LargeCoupling (digestTrial_inj tsum_trial_indicator_le expectedValue_uniform_reply)
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable def reuseC (st : RouterState) : ENNReal :=
  ∑' m : Message, if (st.memo.lookup m).isSome then 0 else ClaudeWCT.Bank.Paired.lawSpec.reuseMass st.cache m
noncomputable def bankOf (q : Nat) (st : RouterState) : CaseC.BankCore :=
  ⟨(st.births.map Prod.snd).reverse, st.exposures, st.reused, reuseC st, q - st.births.length⟩
noncomputable def coeffQ (θ : ENNReal) (_q : Nat) : ENNReal := θ + ClaudeWCT.Bank.Paired.lawSpec.admBound
noncomputable def psi (θ : ENNReal) (q : Nat) (st : RouterState) : ENNReal :=
  ClaudeWCT.Bank.Flexible.corePotential ClaudeWCT.Bank.Paired.lawSpec θ CaseC.horizon (bankOf q st)
noncomputable def slackT {U : Finset HashInput} (θ : ENNReal) (q : Nat)
    (ws : LargeResidual.State WCoord (Cell U)) : ENNReal :=
  coeffQ θ q * ((q-ws.counters.mass : Nat) : ENNReal) / 2^128
variable (θ : ENNReal)
theorem psi_after (q : Nat) (st : RouterState) (X : HashInput) : psi θ q (st.after X) = psi θ q st := rfl
theorem admissibleEntry_birth (st : RouterState) (X Z : HashInput) (y : LargeResidual.HashOutput)
    (hX : st.cache X = none) :
    ClaudeWCT.Bank.Paired.lawSpec.admissibleEntry (st.born X y).cache Z ≤
      ClaudeWCT.Bank.Paired.lawSpec.admissibleEntry st.cache Z + if Z = X then ClaudeWCT.Bank.Paired.lawSpec.admInd y else 0 := by
  unfold ClaudeWCT.Bank.FtsBankSpec.admissibleEntry
  simp only [cache_birth]
  by_cases h : Z = X
  · subst h
    simp only [if_true, hX, Option.elim_none, Option.elim_some, zero_add, ClaudeWCT.Bank.FtsBankSpec.admInd]
    exact le_rfl
  · simp only [h, if_false, add_zero]
    exact le_rfl
theorem reuseC_birth (st : RouterState) (X : HashInput) (y : LargeResidual.HashOutput) (hX : st.cache X = none) :
    reuseC (st.born X y) ≤ reuseC st + ClaudeWCT.Bank.Paired.lawSpec.admInd y / 2 ^ 128 := by
  unfold reuseC ClaudeWCT.Bank.FtsBankSpec.reuseMass
  have hmemo : (st.born X y).memo = st.memo := rfl
  rw [hmemo]
  calc
    _ ≤ ∑' m : Message, ((if (st.memo.lookup m).isSome then 0 else
          (∑' p : Digest × Fin (2 ^ 32),
            ClaudeWCT.Bank.Paired.lawSpec.admissibleEntry st.cache (Sampling.digestTrial p.1 m p.2.val)) / 2 ^ 128) +
          (∑' p : Digest × Fin (2 ^ 32),
            if Sampling.digestTrial p.1 m p.2.val = X then ClaudeWCT.Bank.Paired.lawSpec.admInd y else 0) / 2 ^ 128) := by
      apply ENNReal.tsum_le_tsum
      intro m
      split_ifs
      · exact zero_le
      · rw [← ENNReal.add_div, ← ENNReal.tsum_add]
        apply ENNReal.div_le_div_right
        apply ENNReal.tsum_le_tsum
        intro p
        exact admissibleEntry_birth st X _ y hX
    _ = _ + _ := ENNReal.tsum_add
    _ ≤ _ := by
      apply add_le_add le_rfl
      simp only [div_eq_mul_inv]
      rw [ENNReal.tsum_mul_right]
      exact mul_le_mul' (tsum_trial_indicator_le X _) le_rfl
theorem reuseC_signed (st : RouterState) (rho : Digest) (m : Message)
    (found : Option (BitVec 32 × LargeResidual.HashOutput))
    (hm : st.memo.lookup m = none) :
    reuseC (LargeResidual.Paired.RouterState.signed st rho m found) + ClaudeWCT.Bank.Paired.lawSpec.reuseMass st.cache m = reuseC st := by
  obtain ⟨-, -, -, hb, -, hmemo⟩ := LargeResidual.Paired.RouterState.signed_fields st rho m found
  have hcache : (LargeResidual.Paired.RouterState.signed st rho m found).cache = st.cache := by
    funext X; simp only [RouterState.cache, hb]
  unfold reuseC
  rw [hmemo, hcache, ENNReal.tsum_eq_add_tsum_ite m (f := fun m' => if (st.memo.lookup m').isSome then 0 else
    ClaudeWCT.Bank.Paired.lawSpec.reuseMass st.cache m')]
  simp only [hm, Option.isSome_none, Bool.false_eq_true, if_false]
  rw [add_comm]
  congr 1
  apply tsum_congr
  intro m'
  by_cases h : m' = m
  · subst h
    simp [List.lookup_cons]
  · have hb' : (m' == m) = false := by simpa using h
    simp only [List.lookup_cons, hb', if_neg h]
theorem psi_birth_le (q : Nat) (st : RouterState) (X : HashInput) (hX : st.cache X = none)
    (hlen : st.births.length < q) :
    expectedValue (liftM (PMF.uniformOfFintype LargeResidual.HashOutput) : SPMF LargeResidual.HashOutput)
        (fun y => psi θ q (st.born X y)) ≤ psi θ q st + coeffQ θ q / 2^128 := by
  rw [expectedValue_uniform_reply]
  have hs : (bankOf q st).slack = (q-(st.births.length+1))+1 := by
    change q-st.births.length=_
    omega
  have hb : ∀y : HashOutput, bankOf q (st.born X y) = {bankOf q st with
      targets := (bankOf q st).targets ++ [y]
      slack := q-(st.births.length+1)
      reuse := reuseC (st.born X y)} := by
    intro y
    simp only [bankOf,RouterState.born,List.map_cons,List.reverse_cons,List.length_cons]
    rfl
  have h := ClaudeWCT.Bank.Flexible.core_birth ClaudeWCT.Bank.Paired.lawSpec θ CaseC.horizon
    (bankOf q st) _ hs (fun y=>reuseC (st.born X y)) (fun y=>reuseC_birth st X y hX)
  simpa only [psi,coeffQ,hb] using h

theorem psi_cert (q : Nat) (st : RouterState) (h : CertGhost st) : 1≤psi θ q st := by
  apply ClaudeWCT.Bank.Flexible.core_win ClaudeWCT.Bank.Paired.lawSpec θ CaseC.horizon
    (bankOf q st) (not_lt.mpr h.1)
  rcases h.2 with hr | ⟨p,hp,hadm,hcov⟩
  · exact Or.inl hr
  · refine Or.inr ⟨p.2,?_,hadm,hcov⟩
    change p.2∈(st.births.map Prod.snd).reverse
    rw [List.mem_reverse]
    exact List.mem_map_of_mem hp

theorem psi_initial (q : Nat) (rate : ENNReal)
    (hexc : ClaudeWCT.Numerics.Law.lawAvg ClaudeWCT.Bank.Paired.lawSpec.law (2^32)
      (fun W=>ClaudeWCT.Bank.Paired.lawSpec.price W-θ)≤rate) :
    psi θ q RouterState.initial≤(q:ENNReal)*rate/2^128 := by
  have h0 : reuseC RouterState.initial=0 := by
    unfold reuseC
    apply ENNReal.tsum_eq_zero.mpr
    intro m
    have hc : ∀Z,RouterState.initial.cache Z=none := fun _=>rfl
    have hm : RouterState.initial.memo.lookup m=none := rfl
    simp only [hm,Option.isSome_none,Bool.false_eq_true,if_false,
      ClaudeWCT.Bank.FtsBankSpec.reuseMass,ClaudeWCT.Bank.FtsBankSpec.admissibleEntry,hc,
      Option.elim_none,tsum_zero,ENNReal.zero_div]
  unfold psi bankOf
  rw [h0]
  exact ClaudeWCT.Bank.Flexible.core_initial ClaudeWCT.Bank.Paired.lawSpec θ rate hexc q

end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord WCoord)
open SigGolfCandidate.T3.Security.LargeResidual (State Cell Charge Probe readState probeState stoppedState
  disclosedState tickState runWith_map)
open ClaudeWCT.W9.T3.Security.FamResidual (lazyRun lazyResp discLaw lazy_read lazy_pure lazy_probe_cached
  lazy_probe_fresh lazy_aux' lazy_disclose lazy_tick)
open SigGolfCandidate.T3.Security.LargeCoupling (ev_bind_le ev_observe_le)
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
variable (U : Finset HashInput) (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
theorem lazy_coinReq {β : Type} (n : Nat) (k : Fin (n + 1) → OracleComp (RWorld U) β) (s : State WCoord (Cell U)) :
    lazyRun aux q (coinReq U n >>= k) s = ((liftM (aux (.coin n)) : SPMF _) >>= fun v => lazyRun aux q (k v) s) :=
  lazy_aux' aux q (.coin n) k s
theorem lazy_initReq {β : Type} (k : AuxData → OracleComp (RWorld U) β) (s : State WCoord (Cell U)) :
    lazyRun aux q (initReq U >>= k) s = ((liftM (aux .init) : SPMF _) >>= fun v => lazyRun aux q (k v) s) :=
  lazy_aux' aux q .init k s
theorem lazy_readReq {β : Type} (row : Cell U) (ch : Charge) (k : HashOutput → OracleComp (RWorld U) β)
    (s : State WCoord (Cell U)) :
    lazyRun aux q (readReq U row ch >>= k) s =
      (reply s.rows row >>= fun y => lazyRun aux q (k y) (readState q s row y ch)) :=
  lazy_read aux q row ch k s
theorem lazy_probeReq_cached {β : Type} (row : Cell U) (test : Probe WCoord)
    (k : HashOutput → OracleComp (RWorld U) β) (s : State WCoord (Cell U)) (v : HashOutput)
    (h : s.rows row = some v) :
    lazyRun aux q (probeReq U row test >>= k) s = lazyRun aux q (k v) (readState q s row v .call) :=
  lazy_probe_cached aux q row test k s v h
theorem lazy_probeReq_fresh {β : Type} (row : Cell U) (test : Probe WCoord)
    (k : HashOutput → OracleComp (RWorld U) β) (s : State WCoord (Cell U)) (h : s.rows row = none) :
    lazyRun aux q (probeReq U row test >>= k) s =
      observe (lazyResp s.candidates (test.effF s.candidates)) (pure (none, stoppedState s))
        (fun y => lazyRun aux q (k y) (probeState s row (test.effF s.candidates) y)) :=
  lazy_probe_fresh aux q row test k s h
theorem lazy_discloseReq {β : Type} (c : WCoord) (ch : Charge) (k : Digest → OracleComp (RWorld U) β)
    (s : State WCoord (Cell U)) :
    lazyRun aux q (discloseReq U c ch >>= k) s =
      (discLaw s.candidates c >>= fun v => lazyRun aux q (k v) (disclosedState q s c v ch)) :=
  lazy_disclose aux q c ch k s
theorem lazy_tickReq {β : Type} (ch : Charge) (k : Unit → OracleComp (RWorld U) β) (s : State WCoord (Cell U)) :
    lazyRun aux q (tickReq U ch >>= k) s = lazyRun aux q (k ()) (tickState q s ch) :=
  lazy_tick aux q ch k s
theorem ev_discloseAll_le {β : Type} (cs : List Coord) (k : List (Coord × Digest) → OracleComp (RWorld U) β)
    (pay : Option β × State WCoord (Cell U) → ENNReal) (B : ENNReal) (s : State WCoord (Cell U))
    (h : ∀ pairs s', DiscFrame U s s' → expectedValue (lazyRun aux q (k pairs) s') pay ≤ B) :
    expectedValue (lazyRun aux q (discloseAll U cs >>= k) s) pay ≤ B := by
  induction cs generalizing s k with
  | nil =>
      simp only [discloseAll, pure_bind]
      exact h [] s (DiscFrame.refl U s)
  | cons c rest ih =>
      simp only [discloseAll, bind_assoc]
      rw [lazy_discloseReq]
      apply ev_bind_le
      intro v
      simp only [pure_bind]
      exact ih _ _ fun pairs s' hs' => h _ s' ((discFrame_disclose U q s c v).trans U hs')
theorem ev_lazy_map {α β : Type} (f : α → β) (comp : OracleComp (RWorld U) α) (s : LargeResidual.State WCoord (Cell U))
    (g : Option β × LargeResidual.State WCoord (Cell U) → ENNReal) :
    expectedValue (lazyRun aux q (f <$> comp) s) g = expectedValue (lazyRun aux q comp s) (fun r => g (r.1.map f, r.2)) := by
  rw [lazyRun, runWith_map, expectedValue_map]
  rfl
theorem ev_probeReq_le (row : Cell U) (test : Probe WCoord) (htest : InlTest test) (s : LargeResidual.State WCoord (Cell U))
    (g : Option LargeResidual.HashOutput × LargeResidual.State WCoord (Cell U) → ENNReal) (B : ENNReal)
    (h : OutcomeLe U row.1 s g B) : expectedValue (lazyRun aux q (probeReq U row test) s) g ≤ B := by
  rw [← bind_pure (probeReq U row test)]
  cases hr : s.rows row with
  | some v =>
      rw [lazy_probeReq_cached U aux q row test _ s v hr, lazy_pure, expectedValue_pure]
      apply h.1
      refine ⟨fun row' hne => ?_, rfl, rfl, fun _ => rfl⟩
      simp only [readState]
      rw [Function.update_of_ne (fun he => hne (by rw [he]))]
  | none =>
      rw [lazy_probeReq_fresh U aux q row test _ s hr]
      apply ev_observe_le
      · rw [expectedValue_pure]
        exact h.2 _ rfl
      · intro y
        rw [lazy_pure, expectedValue_pure]
        apply h.1
        refine ⟨fun row' hne => ?_, rfl, rfl, fun m => restrict_inr test htest _ y m⟩
        simp only [probeState]
        rw [Function.update_of_ne (fun he => hne (by rw [he]))]
theorem ev_readReq_call_le (row : Cell U) (s : LargeResidual.State WCoord (Cell U))
    (g : Option LargeResidual.HashOutput × LargeResidual.State WCoord (Cell U) → ENNReal) (B : ENNReal)
    (h : OutcomeLe U row.1 s g B) : expectedValue (lazyRun aux q (readReq U row .call) s) g ≤ B := by
  rw [← bind_pure (readReq U row .call), lazy_readReq]
  apply ev_bind_le
  intro y
  rw [lazy_pure, expectedValue_pure]
  apply h.1
  refine ⟨fun row' hne => ?_, rfl, rfl, fun _ => rfl⟩
  simp only [readState]
  rw [Function.update_of_ne (fun he => hne (by rw [he]))]
theorem ev_testReq_le (first : Bool) (row : Cell U) (test : Probe WCoord) (htest : InlTest test)
    (s : LargeResidual.State WCoord (Cell U))
    (g : Option LargeResidual.HashOutput × LargeResidual.State WCoord (Cell U) → ENNReal) (B : ENNReal)
    (h : OutcomeLe U row.1 s g B) : expectedValue (lazyRun aux q (testReq U first row test) s) g ≤ B := by
  unfold testReq
  split
  · exact ev_probeReq_le U aux q row test htest s g B h
  · exact ev_readReq_call_le U aux q row s g B h

end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord WCoord EncRow encodingHit)
open SigGolfCandidate.T3.Security.LargeResidual (State Cell Probe Hit IsDigestRow runWith_map readState probeState)
open ClaudeWCT.W9.T3.Security.FamResidual (lazyRun lazy_pure)
open SigGolfCandidate.T3.Security.LargeCoupling (ev_bind_le ev_observe_le)
open ClaudeWCT.W9.T3.Security.CanonGraph ClaudeWCT.W9.T3.Security.CanonEncoding
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
variable (θ : ENNReal) {U : Finset HashInput}
theorem slackT_eq_of_mass {s s' : LargeResidual.State WCoord (Cell U)} (q : Nat)
    (h : s'.counters.mass = s.counters.mass) : slackT θ q s' = slackT θ q s := by
  unfold slackT; rw [h]
theorem slackT_le_of_mass {s s' : LargeResidual.State WCoord (Cell U)} (q : Nat)
    (h : s.counters.mass ≤ s'.counters.mass) : slackT θ q s' ≤ slackT θ q s := by
  unfold slackT
  apply ENNReal.div_le_div_right
  apply mul_le_mul' le_rfl
  exact_mod_cast Nat.sub_le_sub_left h q
variable (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
theorem bank_routeQuerySelected (a : AuxData) (st : RouterState) (ws : LargeResidual.State WCoord (Cell U)) (X : HashInput)
    (hinv : BankInv U ws st) (hlt : st.calls < q)
    (g : Option (LargeResidual.HashOutput × RouterState) × LargeResidual.State WCoord (Cell U) → ENNReal)
    (hstop : ∀ ws', g (none, ws') ≤ slackT θ q ws')
    (hcont : ∀ y st' ws', BankInv U ws' st' → st'.calls ≤ q → g (some (y, st'), ws') ≤ psi θ q st' + slackT θ q ws') :
    expectedValue (lazyRun aux q (routeQuerySelected U a st X) ws) g ≤ psi θ q st + slackT θ q ws := by
  have hnd : ¬(X ∈ U ∧ IsDigestRow X) →
      OutcomeLe U X ws (fun r : Option LargeResidual.HashOutput × _ => g (r.1.map fun y => (y, st.after X), r.2))
        (psi θ q st + slackT θ q ws) := by
    intro hX
    refine ⟨fun y s' hs => ?_, fun s' hs => ?_⟩
    · have hinv' := hinv.after X hX hs
      refine (hcont y (st.after X) s' hinv' (by change st.calls + 1 ≤ q; omega)).trans ?_
      rw [psi_after, slackT_eq_of_mass θ q hs.2.2.1]
    · exact (hstop s').trans ((le_of_eq (slackT_eq_of_mass θ q hs)).trans le_add_self)
  unfold routeQuerySelected
  dsimp only
  by_cases hX : X ∈ U
  · rw [dif_pos hX]
    by_cases hp : Parsed X
    · rw [dif_pos hp]
      have hndX : ¬(X ∈ U ∧ IsDigestRow X) := fun h => not_parsed_of_digest h.2 (by obtain ⟨N,_,hn⟩:=hp; exact ⟨N,hn⟩)
      split
      · rename_i cs hfu
        rw [ev_lazy_map]
        exact ev_testReq_le U aux q _ ⟨X, hX⟩ _ (inlTest_guess _ _ _ (hit_label_inl _)) ws _ _ ((hnd hndX).map U _)
      · rename_i hfu
        apply ev_discloseAll_le
        intro pairs s1 hd
        split
        · rw [lazy_discloseReq]
          apply ev_bind_le
          intro v
          rw [lazy_pure, expectedValue_pure]
          apply ((hnd hndX).of_disc U hd).1
          refine ⟨fun row hr => rfl, rfl, rfl, fun m => ?_⟩
          simp only [discloseTableValue]
          rw [Function.update_of_ne (by simp)]
        · rw [ev_lazy_map]
          exact ev_testReq_le U aux q _ ⟨X, hX⟩ _ (inlTest_none _ (hit_label_inl _))
            s1 _ _ (((hnd hndX).of_disc U hd).map U _)
    · rw [dif_neg hp]
      by_cases hph : ∃ n : ClaudeWCT.W9.T3.Security.CanonGraph.TreeNode, X = ClaudeWCT.W9.T3.Security.CanonGraph.phantom n
      · rw [dif_pos hph]
        have hndX : ¬(X ∈ U ∧ IsDigestRow X) := by
          rintro ⟨-, ρ, m, c, hd⟩
          obtain ⟨n, hn⟩ := hph
          have := congrArg List.length (hn.symm.trans hd)
          rw [ClaudeWCT.W9.T3.Security.CanonGraph.phantom_length, Cost.pad64_length] at this
          simp [digestInput, SphincsSecurity.bytesLE_length] at this
        apply ev_discloseAll_le
        intro pairs s1 hd
        split
        · rw [ev_lazy_map]
          exact ev_readReq_call_le U aux q ⟨X,hX⟩ s1 _ _ (((hnd hndX).of_disc U hd).map U _)
        · rw [lazy_discloseReq]
          apply ev_bind_le
          intro v
          rw [lazy_pure, expectedValue_pure]
          apply ((hnd hndX).of_disc U hd).1
          refine ⟨fun row hr => rfl, rfl, rfl, fun m => ?_⟩
          simp only [discloseTableValue]
          rw [Function.update_of_ne (by simp)]
      rw [dif_neg hph]
      by_cases he : EncRow X
      · rw [dif_pos he]
        have hndX : ¬(X ∈ U ∧ IsDigestRow X) := by
          intro h
          obtain ⟨L, m, ctr, pad, -, hXe⟩ := he
          rw [hXe] at h
          exact encRow_not_digest L m ctr pad h.2
        apply ev_discloseAll_le
        intro pairs s1 hd
        split
        · rw [lazy_tickReq, lazy_pure, expectedValue_pure]
          apply ((hnd hndX).of_disc U hd).1
          exact ⟨fun row hr => rfl, rfl, rfl, fun m => rfl⟩
        · split
          · rw [ev_lazy_map]
            exact ev_testReq_le U aux q _ ⟨X,hX⟩ _ (inlTest_none _ (hit_encodingHit _ _))
              s1 _ _ (((hnd hndX).of_disc U hd).map U _)
          · rw [ev_lazy_map]
            exact ev_readReq_call_le U aux q ⟨X,hX⟩ s1 _ _ (((hnd hndX).of_disc U hd).map U _)
      · rw [dif_neg he]
        by_cases hd : IsDigestRow X
        · rw [if_pos hd, ev_lazy_map, ← bind_pure (readReq U ⟨X, hX⟩ .mass), lazy_readReq]
          simp only [lazy_pure, expectedValue_bind, expectedValue_pure, Option.map_some]
          have hcalls : ws.counters.calls + 1 ≤ q := by rw [hinv.calls]; omega
          have hmass_lt : ws.counters.mass < q := by have := hinv.mass; omega
          by_cases hfr : st.Fresh X
          ·
            have hnone : ws.rows ⟨X, hX⟩ = none := hinv.fresh X hX hd hfr.1 hfr.2
            have hc0 : st.cache X = none := hinv.cache_none hfr.1
            have hlen : st.births.length < q := by have := hinv.births; omega
            rw [reply, hnone]
            dsimp only
            simp only [if_pos hfr]
            have hpt : ∀ y : LargeResidual.HashOutput,
                g (some (y, st.born X y), readState q ws ⟨X, hX⟩ y .mass) ≤
                  psi θ q (st.born X y) + coeffQ θ q * ((q - (ws.counters.mass + 1) : Nat) : ENNReal) / 2 ^ 128 := by
              intro y
              refine (hcont y _ _ (hinv.born q X hX hd hfr.1 y) (by
                change st.calls + 1 ≤ q; omega)).trans (le_of_eq ?_)
              congr 1
              unfold slackT
              simp only [readState, LargeResidual.Counters.charge, if_pos hcalls]
            calc
              _ ≤ expectedValue (liftM (PMF.uniformOfFintype LargeResidual.HashOutput) : SPMF LargeResidual.HashOutput)
                  (fun y => psi θ q (st.born X y) + coeffQ θ q * ((q - (ws.counters.mass + 1) : Nat) : ENNReal) / 2 ^ 128) :=
                expectedValue_mono _ hpt
              _ ≤ psi θ q st + coeffQ θ q / 2 ^ 128 + coeffQ θ q * ((q - (ws.counters.mass + 1) : Nat) : ENNReal) / 2 ^ 128 := by
                rw [expectedValue_add]
                exact add_le_add (psi_birth_le θ q st X hc0 hlen) (expectedValue_le_of_le _ fun _ => le_rfl)
              _ ≤ _ := by
                rw [add_assoc]
                apply add_le_add le_rfl
                unfold slackT
                rw [← ENNReal.add_div]
                apply ENNReal.div_le_div_right
                have hsub : (q - ws.counters.mass : Nat) = 1 + (q - (ws.counters.mass + 1)) := by omega
                rw [hsub, Nat.cast_add, Nat.cast_one, mul_add, mul_one]
          · simp only [if_neg hfr]
            by_cases ht : X ∈ st.trials
            ·
              apply expectedValue_le_of_le
              intro y
              have hinv' : BankInv U (readState q ws ⟨X, hX⟩ y .mass) (st.after X) := by
                refine hinv.after' X (fun row hr => ?_) (fun _ _ ht' => absurd ht ht') rfl ?_ (fun _ => rfl)
                · simp only [readState]
                  rw [Function.update_of_ne (fun he' => hr (by rw [he']))]
                · simp only [readState, LargeResidual.Counters.charge, if_pos hcalls]
                  have := hinv.mass; omega
              refine (hcont y _ _ hinv' (by change st.calls + 1 ≤ q; omega)).trans ?_
              · rw [psi_after]
                exact add_le_add le_rfl (slackT_le_of_mass θ q (by
                  simp only [readState, LargeResidual.Counters.charge, if_pos hcalls]; omega))
            ·
              have hs : X ∈ st.seen := by
                by_contra hs'
                exact hfr ⟨hs', ht⟩
              obtain ⟨v, hv1, hv2⟩ := hinv.seenRows X hX hd hs ht
              rw [reply, hv2]
              dsimp only
              rw [expectedValue_pure]
              have hupd : Function.update ws.rows ⟨X, hX⟩ (some v) = ws.rows := by
                rw [← hv2, Function.update_eq_self]
              have hinv' : BankInv U (readState q ws ⟨X, hX⟩ v .mass) (st.after X) := by
                refine hinv.after' X (fun row hr => ?_) (fun _ _ _ => ⟨v, hv1, ?_⟩) rfl ?_ (fun _ => rfl)
                · simp only [readState, hupd]
                · simp only [readState, hupd]; exact hv2
                · simp only [readState, LargeResidual.Counters.charge, if_pos hcalls]
                  have := hinv.mass; omega
              refine (hcont v _ _ hinv' (by change st.calls + 1 ≤ q; omega)).trans ?_
              · rw [psi_after]
                exact add_le_add le_rfl (slackT_le_of_mass θ q (by
                  simp only [readState, LargeResidual.Counters.charge, if_pos hcalls]; omega))
        · rw [if_neg hd, ev_lazy_map]
          exact ev_readReq_call_le U aux q ⟨X, hX⟩ ws _ _ ((hnd fun h => hd h.2).map U _)
  · rw [dif_neg hX, lazy_tickReq, lazy_pure, expectedValue_pure]
    apply (hnd fun h => hX h.1).1
    exact ⟨fun row hr => rfl, rfl, rfl, fun m => rfl⟩

end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord WCoord)
open SigGolfCandidate.T3.Security.LargeResidual (State Cell IsDigestRow readState)
open ClaudeWCT.W9.T3.Security.FamResidual (lazyRun lazy_pure)
open SigGolfCandidate.T3.Security.LargeCoupling (trial_ne reply_of_some reply_of_none expectedValue_uniform_ro)
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable

theorem shared_search_succ (rho : Digest) (m : Message) (c fuel : Nat) :
    SigGolfCandidate.Research.SharedForest.sharedDigestSearch rho m c (fuel+1) =
      (digest rho m (BitVec.ofNat 32 c) >>= fun y=>
        if SigGolfCandidate.Research.SharedForest.digestAccepted y then pure (some (BitVec.ofNat 32 c,y))
        else SigGolfCandidate.Research.SharedForest.sharedDigestSearch rho m (c+1) fuel) := rfl
variable {U : Finset HashInput} (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
  (a : AuxData) (rho : Digest) (m : Message)
theorem readImpl_digest (hU : ∀ c : BitVec 32, pad64 (digestInput rho m c) ∈ U) (c : Nat) :
    simulateQ (readImpl U a) (digest rho m (BitVec.ofNat 32 c)) =
      readReq U ⟨_, hU (BitVec.ofNat 32 c)⟩ .none := by
  change simulateQ (readImpl U a) (liftM (SigGolfCandidate.T3.Spec.query (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 c))))))) = _
  rw [simulateQ_spec_query]
  simp only [readImpl, dif_pos (hU (BitVec.ofNat 32 c))]
theorem lazy_readImpl_digest (hU : ∀ c : BitVec 32, pad64 (digestInput rho m c) ∈ U) (c : Nat) {β : Type}
    (k : HashOutput → OracleComp (RWorld U) β) (s : LargeResidual.State WCoord (Cell U)) :
    lazyRun aux q (simulateQ (readImpl U a) (digest rho m (BitVec.ofNat 32 c)) >>= k) s =
      (reply s.rows ⟨_, hU (BitVec.ofNat 32 c)⟩ >>= fun y =>
        lazyRun aux q (k y) (readState q s ⟨_, hU (BitVec.ofNat 32 c)⟩ y .none)) := by
  rw [readImpl_digest]
  exact lazy_readReq U aux q _ _ k s
theorem bank_search (hU : ∀ c : BitVec 32, pad64 (digestInput rho m c) ∈ U) (secret : BitVec 256) :
    ∀ (fuel c : Nat), c + fuel ≤ 2 ^ 32 → ∀ (s : LargeResidual.State WCoord (Cell U)) (cache : Sampling.RCache),
      (∀ k, c ≤ k → k < 2 ^ 32 →
        s.rows ⟨_, hU (BitVec.ofNat 32 k)⟩ = cache (pad64 (digestInput rho m (BitVec.ofNat 32 k)))) →
      ∀ (G : Option (Option (BitVec 32 × LargeResidual.HashOutput)) × LargeResidual.State WCoord (Cell U) → ENNReal)
        (H : Option (BitVec 32 × LargeResidual.HashOutput) → ENNReal),
        (∀ found s', SearchFrame rho m c fuel found s s' → G (some found, s') ≤ H found) →
        expectedValue (lazyRun aux q (simulateQ (readImpl U a) (SigGolfCandidate.Research.SharedForest.sharedDigestSearch rho m c fuel)) s) G ≤
          expectedValue (Sampling.roRun secret (SigGolfCandidate.Research.SharedForest.sharedDigestSearch rho m c fuel) cache) (fun r => H r.1) := by
  intro fuel
  induction fuel with
  | zero =>
      intro c _ s cache _ G H hG
      simp only [SigGolfCandidate.Research.SharedForest.sharedDigestSearch, simulateQ_pure, Sampling.roRun_pure, expectedValue_pure]
      rw [lazy_pure, expectedValue_pure]
      apply hG
      refine ⟨rfl, rfl, fun k' out h => (by cases h), fun row h => absurd rfl h⟩
  | succ fuel ih =>
      intro c hc s cache hagree G H hG
      have hc32 : c < 2 ^ 32 := by omega
      set X : Cell U := ⟨_, hU (BitVec.ofNat 32 c)⟩ with hXdef
      simp only [shared_search_succ, simulateQ_bind, Sampling.roRun_bind]
      rw [lazy_readImpl_digest aux q a rho m hU c]
      have hro : Sampling.roRun secret (digest rho m (BitVec.ofNat 32 c)) cache =
          (randomOracle (spec := SphincsSecurity.HashSpec) (pad64 (digestInput rho m (BitVec.ofNat 32 c)))).run cache :=
        Sampling.roRun_publicQuery secret _ cache
      simp only [hro, randomOracle.run_eq]
      have hXc := hagree c le_rfl hc32
      have hstep : ∀ (y : LargeResidual.HashOutput) (cache' : Sampling.RCache),
          (∀ k, c + 1 ≤ k → k < 2 ^ 32 →
            cache' (pad64 (digestInput rho m (BitVec.ofNat 32 k))) =
              cache (pad64 (digestInput rho m (BitVec.ofNat 32 k)))) →
          expectedValue (lazyRun aux q (simulateQ (readImpl U a)
              (if SigGolfCandidate.Research.SharedForest.digestAccepted y = true then pure (some (BitVec.ofNat 32 c, y))
                else SigGolfCandidate.Research.SharedForest.sharedDigestSearch rho m (c + 1) fuel)) (readState q s X y .none)) G ≤
            expectedValue (Sampling.roRun secret
              (if SigGolfCandidate.Research.SharedForest.digestAccepted y = true then pure (some (BitVec.ofNat 32 c, y))
                else SigGolfCandidate.Research.SharedForest.sharedDigestSearch rho m (c + 1) fuel) cache') (fun r => H r.1) := by
        intro y cache' hcache'
        have hrowsX : ∀ row : Cell U, (readState q s X y .none).rows row ≠ s.rows row → row = X := by
          intro row hr
          by_contra hne
          apply hr
          simp only [readState]
          rw [Function.update_of_ne hne]
        by_cases hadm : SigGolfCandidate.Research.SharedForest.digestAccepted y = true
        · simp only [hadm, if_true, simulateQ_pure, Sampling.roRun_pure, expectedValue_pure]
          rw [lazy_pure, expectedValue_pure]
          apply hG
          have hcn : (BitVec.ofNat 32 c).toNat = c := by
            simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc32]
          refine ⟨rfl, rfl, fun k' out h => ?_, fun row hr => ?_⟩
          · cases h
            rw [hcn]; omega
          · have hrX := hrowsX row hr
            refine ⟨c, le_rfl, by omega, by rw [hrX], fun k' out h => ?_⟩
            cases h
            rw [hcn]
        · simp only [hadm, Bool.false_eq_true, if_false]
          apply ih (c + 1) (by omega) (readState q s X y .none) cache'
          · intro k hk hk32
            have hne : (⟨_, hU (BitVec.ofNat 32 k)⟩ : Cell U) ≠ X := by
              intro he
              exact trial_ne rho m hk32 hc32 (by omega) (congrArg Subtype.val he)
            simp only [readState]
            rw [Function.update_of_ne hne, hcache' k hk hk32]
            exact hagree k (by omega) hk32
          · intro found s' hf
            apply hG
            obtain ⟨h1, h2, h3, h4⟩ := hf
            refine ⟨h1, h2, fun k' out h => ?_, fun row hr => ?_⟩
            · have := h3 k' out h; omega
            · by_cases hr1 : s'.rows row ≠ (readState q s X y .none).rows row
              · obtain ⟨k, hk1, hk2, hk3, hk4⟩ := h4 row hr1
                exact ⟨k, by omega, by omega, hk3, hk4⟩
              · push Not at hr1
                have hrX := hrowsX row (by rw [← hr1]; exact hr)
                refine ⟨c, le_rfl, by omega, by rw [hrX], fun k' out h => ?_⟩
                have := (h3 k' out h).1; omega
      cases hcache : cache (pad64 (digestInput rho m (BitVec.ofNat 32 c))) with
      | some u =>
          have hsX : s.rows ⟨_, hU (BitVec.ofNat 32 c)⟩ = some u := hXc.trans hcache
          rw [reply_of_some hsX, pure_bind, pure_bind]
          exact hstep u cache (fun _ _ _ => rfl)
      | none =>
          have hsX : s.rows ⟨_, hU (BitVec.ofNat 32 c)⟩ = none := hXc.trans hcache
          rw [reply_of_none hsX, expectedValue_bind, bind_assoc, expectedValue_bind, expectedValue_uniform_ro]
          apply expectedValue_mono
          intro y
          rw [pure_bind]
          dsimp only
          have hc' : ∀ k, c + 1 ≤ k → k < 2 ^ 32 →
              (QueryCache.cacheQuery cache (pad64 (digestInput rho m (BitVec.ofNat 32 c))) y)
                (pad64 (digestInput rho m (BitVec.ofNat 32 k))) = cache (pad64 (digestInput rho m (BitVec.ofNat 32 k))) := by
            intro k hk hk32
            exact QueryCache.cacheQuery_of_ne _ _ (trial_ne rho m hk32 hc32 (by omega))
          exact hstep y _ hc'

end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord WCoord WPlain trialRows)
open SigGolfCandidate.T3.Security.LargeResidual (State Cell IsDigestRow disclosedState)
open ClaudeWCT.W9.T3.Security.FamResidual (lazyRun lazy_pure expectedValue_discLaw_le)
open SigGolfCandidate.T3.Security.LargeCoupling (ev_bind_le ev_runWith_bind expectedValue_cell_univ digestRow_isDigest digestRow_mem)
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9pairedBankSign : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _
variable (θ : ENNReal) {U : Finset HashInput}

theorem decode_eq : ClaudeWCT.Bank.Paired.lawSpec.decode = LargeResidual.Paired.decodeDigest := by
  funext output
  unfold ClaudeWCT.Bank.FtsBankSpec.decode LargeResidual.Paired.decodeDigest
  rw [show ClaudeWCT.Bank.Paired.lawSpec.producer = ClaudeWCT.Bank.Paired.producer from rfl,
    ClaudeWCT.Bank.Paired.producer_source]

theorem reuse_eq (cache : Sampling.RCache) (rho : Digest) (m : Message) :
    LargeResidual.Paired.Reuse cache rho m = ClaudeWCT.Bank.Paired.lawSpec.Reuse cache rho m := by
  unfold LargeResidual.Paired.Reuse ClaudeWCT.Bank.FtsBankSpec.Reuse
  rw [decode_eq]
theorem reuseC_signed_eq (st : RouterState) (rho rho' : Digest) (m : Message)
    (found found' : Option (BitVec 32 × LargeResidual.HashOutput)) :
    reuseC (LargeResidual.Paired.RouterState.signed st rho m found) = reuseC (LargeResidual.Paired.RouterState.signed st rho' m found') := by
  obtain ⟨-, -, -, hb, -, hmemo⟩ := LargeResidual.Paired.RouterState.signed_fields st rho m found
  obtain ⟨-, -, -, hb', -, hmemo'⟩ := LargeResidual.Paired.RouterState.signed_fields st rho' m found'
  unfold reuseC
  have hc : (LargeResidual.Paired.RouterState.signed st rho m found).cache = (LargeResidual.Paired.RouterState.signed st rho' m found').cache := by
    funext X; simp only [LargeResidual.RouterState.cache, hb, hb']
  rw [hc, hmemo, hmemo']
  apply tsum_congr
  intro m'
  by_cases h : m' = m
  · subst h; simp
  · have hb2 : (m' == m) = false := by simpa using h
    simp only [List.lookup_cons, hb2]
noncomputable def corePotentialQ (θ : ENNReal) (_q : Nat) (b : CaseC.BankCore) : ENNReal :=
  ClaudeWCT.Bank.Flexible.corePotential ClaudeWCT.Bank.Paired.lawSpec θ CaseC.horizon b

theorem psi_eq_corePotentialQ (q : Nat) (st : RouterState) :
    psi θ q st = corePotentialQ θ q (bankOf q st) := rfl

theorem wct_core_sign_q (q : Nat) (b : CaseC.BankCore) (cache : Sampling.RCache) (m : Message) (C' : ENNReal)
    (hC : C'+ClaudeWCT.Bank.Paired.lawSpec.reuseMass cache m≤b.reuse) (secret : BitVec 256) (fuel : Nat)
    (hfuel : fuel≤2^32) :
    expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho=>
      if ClaudeWCT.Bank.Paired.lawSpec.Reuse cache rho m then
        corePotentialQ θ q {b with reused:=true,reuse:=C'}
      else expectedValue (Sampling.roRun secret (SigGolfCandidate.Research.SharedForest.sharedDigestSearch rho m 0 fuel) cache)
        (fun result=>corePotentialQ θ q (b.expose C' (result.1.map Prod.snd))))≤corePotentialQ θ q b := by
  have h:=ClaudeWCT.Bank.Flexible.core_sign ClaudeWCT.Bank.Paired.lawSpec θ CaseC.horizon b cache m C' hC secret fuel hfuel
  simpa only [corePotentialQ,←ClaudeWCT.Bank.Paired.digestSearch_public] using h
theorem psi_signed (q : Nat) (st : RouterState) (rho : Digest) (m : Message)
    (found : Option (BitVec 32 × LargeResidual.HashOutput)) :
    psi θ q (LargeResidual.Paired.RouterState.signed st rho m found) =
      if ClaudeWCT.Bank.Paired.lawSpec.Reuse st.cache rho m then
        corePotentialQ θ q { bankOf q st with reused := true, reuse := reuseC (LargeResidual.Paired.RouterState.signed st 0 m none) }
      else corePotentialQ θ q ((bankOf q st).expose (reuseC (LargeResidual.Paired.RouterState.signed st 0 m none)) (found.map Prod.snd)) := by
  rw [← reuseC_signed_eq st rho 0 m found none, psi_eq_corePotentialQ]
  by_cases hr : ClaudeWCT.Bank.Paired.lawSpec.Reuse st.cache rho m
  · rw [if_pos hr]
    congr 1
    unfold bankOf LargeResidual.Paired.RouterState.signed
    rw [reuse_eq,if_pos hr]
  · rw [if_neg hr]
    congr 1
    unfold bankOf CaseC.BankCore.expose LargeResidual.Paired.RouterState.signed
    rw [reuse_eq,if_neg hr]
theorem BankInv.signed {ws s' : LargeResidual.State WCoord (Cell U)} {st : RouterState} (h : BankInv U ws st)
    (q : Nat) (m : Message) (hm : st.memo.lookup m = none) (rho : Digest)
    (found : Option (BitVec 32 × LargeResidual.HashOutput))
    (hf : SearchFrame rho m 0 WCT9.digestAttemptLimit found (disclosedState q ws (.inr m) rho .none) s') :
    BankInv U s' (LargeResidual.Paired.RouterState.signed st rho m found) := by
  obtain ⟨hdisc, hseen, hcalls, hbirths, htrials, hmemo⟩ := LargeResidual.Paired.RouterState.signed_fields st rho m found
  obtain ⟨hcand, hcount, -, hrows⟩ := hf
  have hcache : (LargeResidual.Paired.RouterState.signed st rho m found).cache = st.cache := by
    funext X; simp only [LargeResidual.RouterState.cache, hbirths]
  have hkeep : ∀ (X : HashInput) (hX : X ∈ U), X ∉ trialRows rho m found → s'.rows ⟨X, hX⟩ = ws.rows ⟨X, hX⟩ := by
    intro X hX hnt
    by_contra hne
    obtain ⟨k, -, hk2, hk3, hk4⟩ := hrows ⟨X, hX⟩ hne
    exact hnt (by rw [show X = _ from hk3]; exact mem_trialRows rho m found k (by simpa using hk2) hk4)
  refine ⟨?_, ?_, ?_, fun m' hm' => ?_, fun X hX hd hs ht => ?_, fun X hX hd hs ht => ?_, ?_, ?_⟩
  · rw [hcount, hcalls]; exact h.calls
  · rw [hcount]; exact h.mass
  · rw [hbirths, hcalls]; exact h.births
  · have hne : m' ≠ m := by
      intro he; subst he
      rw [hmemo] at hm'
      simp at hm'
    have hm'' : st.memo.lookup m' = none := by
      rw [hmemo] at hm'
      have hb : (m' == m) = false := by simpa using hne
      simpa only [List.lookup_cons, hb] using hm'
    rw [hcand]
    simp only [disclosedState, discloseTableValue]
    rw [Function.update_of_ne (by simpa using hne)]
    exact h.nonce m' hm''
  · rw [htrials] at ht
    rw [hseen] at hs
    rw [hkeep X hX (fun hm2 => ht (List.mem_append_right _ hm2))]
    exact h.fresh X hX hd hs (fun hm2 => ht (List.mem_append_left _ hm2))
  · rw [htrials] at ht
    rw [hseen] at hs
    rw [hkeep X hX (fun hm2 => ht (List.mem_append_right _ hm2)), hcache]
    exact h.seenRows X hX hd hs (fun hm2 => ht (List.mem_append_left _ hm2))
  · intro p hp
    rw [hbirths] at hp
    rw [hseen]
    exact h.bornSeen p hp
  · intro X hX
    rw [htrials] at hX
    rcases List.mem_append.mp hX with hX | hX
    · obtain ⟨rho', m', c', hX', hs'⟩ := h.trials X hX
      refine ⟨rho', m', c', hX', ?_⟩
      rw [hmemo, List.lookup_cons]
      split
      · rfl
      · exact hs'
    · unfold trialRows at hX
      obtain ⟨k, -, hk⟩ := List.mem_map.mp hX
      refine ⟨rho, m, BitVec.ofNat 32 k, hk.symm, ?_⟩
      rw [hmemo, List.lookup_cons]
      simp
variable (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
theorem ev_signFinish_le (a : AuxData) (st : RouterState) (rho : Digest)
    (found : Option (BitVec 32 × LargeResidual.HashOutput)) (s : LargeResidual.State WCoord (Cell U))
    (g : Option (Option SigGolfCandidate.Research.SharedForest.Signature × RouterState) × LargeResidual.State WCoord (Cell U) → ENNReal) (B : ENNReal)
    (h : ∀ sig (d : List Coord) s', DiscFrame U s s' → g (some (sig, { st with disclosed := d }), s') ≤ B) :
    expectedValue (lazyRun aux q (signFinish U a st rho found) s) g ≤ B := by
  unfold signFinish
  rcases found with _ | ⟨c, N⟩
  · rw [lazy_pure, expectedValue_pure]
    exact h none st.disclosed s (DiscFrame.refl U s)
  · dsimp only
    split
    · apply ev_discloseAll_le
      intro pairs s' hd
      rw [lazy_pure, expectedValue_pure]
      exact h _ _ s' hd
    · rw [lazy_pure, expectedValue_pure]
      exact h none st.disclosed s (DiscFrame.refl U s)
theorem bank_routeSign (hUpub : SeccLaw.publicUniverse ⊆ U) (a : AuxData) (published : SigGolfCandidate.T3.Cache) (st : RouterState)
    (ws : LargeResidual.State WCoord (Cell U)) (request : Security.Request) (hinv : BankInv U ws st)
    (g : Option (Option SigGolfCandidate.Research.SharedForest.Signature × RouterState) × LargeResidual.State WCoord (Cell U) → ENNReal)
    (hcont : ∀ sig st' ws', BankInv U ws' st' → st'.calls = st.calls → g (some (sig, st'), ws') ≤ psi θ q st' + slackT θ q ws') :
    expectedValue (lazyRun aux q (routeSign U a published st request) ws) g ≤ psi θ q st + slackT θ q ws := by
  unfold routeSign
  split_ifs with hpub
  swap
  · rw [lazy_pure, expectedValue_pure]
    exact hcont none st ws hinv rfl
  rw [lazy_discloseReq]
  cases hm : st.memo.lookup request.message with
  | some found =>
      apply ev_bind_le
      intro rho
      apply ev_signFinish_le aux q a st rho found _ g
      intro sig d s' hd
      have hinv1 := hinv.discloseSigned q request.message (by rw [hm]; rfl) rho
      refine (hcont sig _ s' (hinv1.disc hd d) rfl).trans (le_of_eq ?_)
      rw [slackT_eq_of_mass θ q (show s'.counters.mass = ws.counters.mass by rw [hd.2.1] <;> rfl)]
      rfl
  | none =>
      set m := request.message with hmdef
      rw [expectedValue_bind]
      refine (expectedValue_discLaw_le ws.candidates (c := (.inr m : WCoord)) (p := (.inr m : WPlain)) rfl _).trans ?_
      rw [hinv.nonce m hm, expectedValue_cell_univ]
      set C0 := reuseC (LargeResidual.Paired.RouterState.signed st 0 m none) with hC0
      have hC : C0 + ClaudeWCT.Bank.Paired.lawSpec.reuseMass st.cache m ≤ (bankOf q st).reuse := by
        rw [hC0, reuseC_signed st 0 m none hm]; exact le_rfl
      have hcore := wct_core_sign_q θ q (bankOf q st) st.cache m C0 hC 0
        WCT9.digestAttemptLimit WCT9.digestAttemptLimit_le
      have hrho : ∀ rho : Digest,
          expectedValue (lazyRun aux q (simulateQ (readImpl U a) (SigGolfCandidate.Research.SharedForest.sharedDigestSearch rho m 0 WCT9.digestAttemptLimit) >>= fun found =>
              signFinish U a (LargeResidual.Paired.RouterState.signed st rho m found) rho found) (disclosedState q ws (.inr m) rho .none)) g ≤
            (if ClaudeWCT.Bank.Paired.lawSpec.Reuse st.cache rho m then corePotentialQ θ q { bankOf q st with reused := true, reuse := C0 }
              else expectedValue (Sampling.roRun 0 (SigGolfCandidate.Research.SharedForest.sharedDigestSearch rho m 0 WCT9.digestAttemptLimit) st.cache)
                (fun result => corePotentialQ θ q ((bankOf q st).expose C0 (result.1.map Prod.snd)))) +
              slackT θ q ws := by
        intro rho
        rw [lazyRun, ev_runWith_bind, ← lazyRun]
        have hsearch := bank_search aux q a rho m (digestRow_mem hUpub rho m) 0 WCT9.digestAttemptLimit 0
          (by rw [Nat.zero_add]; exact WCT9.digestAttemptLimit_le)
          (disclosedState q ws (.inr m) rho .none) st.cache
          (fun k _ _ => hinv.agree hUpub m hm rho k)
          (fun r => r.1.elim (g (none, r.2)) (fun found =>
            expectedValue (lazyRun aux q (signFinish U a (LargeResidual.Paired.RouterState.signed st rho m found) rho found) r.2) g))
          (fun found => psi θ q (LargeResidual.Paired.RouterState.signed st rho m found) + slackT θ q ws)
          (by
            intro found s' hf
            apply ev_signFinish_le aux q a _ rho found s' g
            intro sig d s'' hd
            have hinv' := (ClaudeWCT.W9.T3.Security.LargeCoupling.Paired.BankInv.signed hinv q m hm rho found hf).disc hd d
            refine (hcont sig _ s'' hinv' ?_).trans (le_of_eq ?_)
            · exact (LargeResidual.Paired.RouterState.signed_fields st rho m found).2.2.1
            · have hmass : s''.counters.mass = ws.counters.mass := by
                rw [hd.2.1, hf.2.1] <;> rfl
              rw [slackT_eq_of_mass θ q hmass]
              rfl)
        refine hsearch.trans ?_
        rw [expectedValue_add]
        refine add_le_add ?_ (expectedValue_le_of_le _ fun _ => le_rfl)
        by_cases hr : ClaudeWCT.Bank.Paired.lawSpec.Reuse st.cache rho m
        · rw [if_pos hr]
          apply expectedValue_le_of_le
          intro result
          rw [psi_signed, if_pos hr]
        · rw [if_neg hr]
          apply le_of_eq
          congr 1
          funext result
          rw [psi_signed, if_neg hr]
      calc
        _ ≤ expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho =>
            (if ClaudeWCT.Bank.Paired.lawSpec.Reuse st.cache rho m then corePotentialQ θ q { bankOf q st with reused := true, reuse := C0 }
              else expectedValue (Sampling.roRun 0 (SigGolfCandidate.Research.SharedForest.sharedDigestSearch rho m 0 WCT9.digestAttemptLimit) st.cache)
                (fun result => corePotentialQ θ q ((bankOf q st).expose C0 (result.1.map Prod.snd)))) +
              slackT θ q ws) := expectedValue_mono _ hrho
        _ ≤ corePotentialQ θ q (bankOf q st) + slackT θ q ws := by
          rw [expectedValue_add]
          exact add_le_add hcore (expectedValue_le_of_le _ fun _ => le_rfl)
        _ = _ := rfl

end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
end
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_LargeCouplingCert ====
section

section


namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_largeCouplingCertShort : DecidableEq T3.Cache := Classical.decEq _
section Short
variable {A T : Answers} (hAT : Wots.Ref.ShortAgree A T)
include hAT
theorem honestNonce_short : honestNonce A = honestNonce T := by
  funext m
  unfold honestNonce
  simp only [T3.privateNonce, privateHash, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  change (A (.inr (.inr (.inl m)))).extractLsb' 0 128 = (T (.inr (.inr (.inl m)))).extractLsb' 0 128
  rw [hAT.priv]
end Short
end SigGolfCandidate.T3.Security.LargeCoupling
end

section






section
namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
  SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual CanonGraph CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_largeCouplingCertInteraction : DecidableEq T3.Cache := Classical.decEq _
end SigGolfCandidate.T3.Security.LargeCoupling
end
section
namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
  SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual CanonGraph CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen
noncomputable local instance instDecidableEqCache_largeCouplingCertTable : DecidableEq T3.Cache := Classical.decEq _
end SigGolfCandidate.T3.Security.LargeCoupling
end
section
namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual CanonGraph CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
section CertChain
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3.Security.LargeCoupling.Samplers
theorem pmf_probEvent_mono_support' {α : Type} (p : PMF α) {F G : α → Prop} (h : ∀ x ∈ p.support, F x → G x) :
    Pr[F | p] ≤ Pr[G | p] := by
  simp only [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : x ∈ p.support
  · by_cases hF : F x
    · simp [hF, h x hx hF]
    · simp [hF]
  · have hp : p x = 0 := by
      rw [PMF.apply_eq_zero_iff]
      exact hx
    simp [hp]
section Lazy
variable {U : Finset HashInput}
theorem probEvent_bind_mono_le {α β γ : Type} (m : SPMF α) (f : α → SPMF β) (g : α → SPMF γ) (E : β → Prop)
    (E' : γ → Prop) (h : ∀ x, Pr[E | f x] ≤ Pr[E' | g x]) : Pr[E | m >>= f] ≤ Pr[E' | m >>= g] := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  exact ENNReal.tsum_le_tsum fun x => by gcongr; exact h x
end Lazy
end CertChain
end SigGolfCandidate.T3.Security.LargeCoupling
end
end

section












section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (State Cell runWith_bind)
open ClaudeWCT.W9.T3.Security.FamResidual (observedRun)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeCouplingCertInteraction : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
section Interaction
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData} {q : Nat} (initLaw : PMF AuxData)
end Interaction
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (State Cell runWith_bind)
open ClaudeWCT.W9.T3.Security.FamResidual (observedRun)
open SigGolfCandidate.T3.Security.LargeCoupling (honestNonce)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen
noncomputable local instance instDecidableEqCache_w9largeCouplingCertTable : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeCoupling (honestNonce honestNonce_short)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeCouplingCertShort : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
section Short
variable {A T : Answers} (hAT : Wots.Ref.ShortAgree A T)
include hAT
end Short
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (State Cell AuxQuery retain runWith_query_bind)
open ClaudeWCT.W9.T3.Security.FamResidual (lazyRun finish observedRun run_posterior lazyImpl view supp)
open SigGolfCandidate.T3.Security.LargeCoupling (pmf_probEvent_mono_support' probEvent_bind_mono_le probEvent_bind_le_of
  weight_self evalSPMF_uniform_inst probEvent_bind_congr_eq completeRows_none)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
section CertChain
attribute [local instance] Classical.propDecidable
open ClaudeWCT.W9.T3.Security.LargeCoupling.Samplers SigGolfCandidate.T3.Security.LargeCoupling.Samplers
section Lazy
variable {U : Finset HashInput}
end Lazy
end CertChain
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
section
namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_largeCouplingBankRun : DecidableEq T3.Cache := Classical.decEq _
end SigGolfCandidate.T3.Security.LargeCoupling
end
section
namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open LargeResidual
open SeccClosing (largeBound excessRate cacheRate largeReserveRate largeReserveAbsolute)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
end SigGolfCandidate.T3.Security.LargeCoupling
end
section
namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
open SeccClosing (largeBound excessRate cacheRate largeReserveRate largeReserveAbsolute)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
end SigGolfCandidate.T3.Security.LargeCoupling
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (State Cell)
open ClaudeWCT.W9.T3.Security.FamResidual (lazyRun lazy_pure)
open SigGolfCandidate.T3.Security.LargeCoupling (ev_bind_le ev_runWith_bind)
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeCouplingBankRun : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
section Run
variable {U : Finset HashInput} (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
end Run
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.LargePotential (Step Charges StepBound FreeStep MassStep TestStep ProbeStep
  continuation hazard terminal expected_stop_le continuation_anti continuation_pay continuation_probe
  initial_potential run_expected_le)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

variable {ι : Type} {spec : OracleSpec ι} {m : Type → Type} [Monad m]
  [LawfulMonad m] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
  [EvalDistCompatible m]

end ClaudeWCT.W9.T3.Security.LargeCoupling
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open ClaudeWCT.W9.T3.Security.LargeResidual
open ClaudeWCT.W9.T3.Security.FamResidual (residual_potential lazyRun)
open ClaudeWCT.W9.T3.Security.SeccClosingW9 (largeBound excessRate excessRate54 cacheRate largeReserveRate largeReserveAbsolute)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (Cell)
open ClaudeWCT.W9.T3.Security.FamResidual (lazyRun lazy_noFail)
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
open ClaudeWCT.W9.T3.Security.SeccClosingW9 (largeBound excessRate excessRate54 cacheRate largeReserveRate largeReserveAbsolute)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
section Bank
variable {U : Finset HashInput}
end Bank
end ClaudeWCT.W9.T3.Security.LargeCoupling
end

/-!
A variable charge for fresh message opportunities.  The existing fixed-rate
security closure above is preserved; these lemmas expose the full payment
available from the same primitive-message potential.
-/
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Flexible
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.LargePotential (Step Charges StepBound FreeStep MassStep TestStep ProbeStep
  continuation hazard terminal expected_stop_le continuation_anti continuation_pay continuation_probe
  initial_potential run_expected_le)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem message_payment_rate (ρ space budget probes remaining : ℝ) (hspace : 0 < space)
    (hρ0 : 0 ≤ ρ) (hprobes : 0 ≤ probes) (hremaining : 0 ≤ remaining)
    (hbudget : probes + remaining + 1 ≤ budget) (hhalf : 2 * budget ≤ space)
    (hrate : ρ * space ≤ 2 * (space - budget)) :
    ρ / space + PrimitiveMessagePotential.value space probes remaining ≤
      PrimitiveMessagePotential.value space probes (remaining + 1) := by
  have hden : 0 < space - probes := by linarith
  have hnum : ρ * space ≤ 2 * (space - probes - remaining) - 1 := by linarith
  have hsq : (space - probes) ^ 2 ≤ space ^ 2 := by nlinarith
  have hpay : ρ / space ≤ (2 * (space - probes - remaining) - 1) / (space - probes) ^ 2 := by
    calc
      ρ / space = (ρ * space) / space ^ 2 := by field_simp
      _ ≤ (ρ * space) / (space - probes) ^ 2 :=
        div_le_div_of_nonneg_left (mul_nonneg hρ0 hspace.le) (sq_pos_of_pos hden) hsq
      _ ≤ _ := (div_le_div_iff_of_pos_right (sq_pos_of_pos hden)).mpr hnum
  rw [← PrimitiveMessagePotential.message_increment space probes remaining (ne_of_gt hden)] at hpay
  linarith

theorem continuation_pay_rate (ρ : ℝ) (space q calls probes : Nat) (hspace : 0 < space)
    (hq : 2 * q ≤ space) (hρ0 : 0 ≤ ρ)
    (hρ : ρ * (space : ℝ) ≤ 2 * ((space : ℝ) - q))
    (hprobes : probes ≤ calls) (hcall : calls + 1 ≤ q) :
    continuation space q (calls + 1) probes + ENNReal.ofReal ρ / space ≤
      continuation space q calls probes := by
  have hs : (0 : ℝ) < space := by exact_mod_cast hspace
  have hb : 2 * (q : ℝ) ≤ space := by exact_mod_cast hq
  have hp : (probes : ℝ) ≤ calls := by exact_mod_cast hprobes
  have hc : (calls : ℝ) + 1 ≤ q := by exact_mod_cast hcall
  unfold continuation
  rw [if_pos hcall, if_pos (by omega)]
  have hpay := message_payment_rate ρ space q probes ((q : ℝ) - ((calls + 1 : Nat) : ℝ)) hs hρ0
    (by positivity) (by push_cast; linarith) (by push_cast; linarith) hb hρ
  have heq : (q : ℝ) - ((calls + 1 : Nat) : ℝ) + 1 = (q : ℝ) - calls := by push_cast; ring
  rw [heq] at hpay
  have hv := (PrimitiveMessagePotential.bounds space probes ((q : ℝ) - ((calls + 1 : Nat) : ℝ))
    (by push_cast; linarith) (by push_cast; linarith)).1
  have hfinal := ENNReal.ofReal_le_ofReal hpay
  have hof : ENNReal.ofReal (ρ / space) = ENNReal.ofReal ρ / space := by
    rw [ENNReal.ofReal_div_of_pos hs, ENNReal.ofReal_natCast]
  rw [ENNReal.ofReal_add (div_nonneg hρ0 hs.le) hv, hof] at hfinal
  rw [add_comm]
  exact hfinal

variable {ι : Type} {spec : OracleSpec ι} {m : Type → Type} [Monad m]
  [LawfulMonad m] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
  [EvalDistCompatible m]

noncomputable def potential (ρ : ℝ) {σ : Type} (ch : Charges σ) (space q : Nat) (state : σ) : ENNReal :=
  continuation space q (ch.calls state) (ch.probes state) + (ENNReal.ofReal ρ) * (ch.mass state : ENNReal) / space
noncomputable def stopValue (ρ : ℝ) {σ : Type} (ch : Charges σ) (space q : Nat) (state : σ) : ENNReal :=
  (if ch.calls state ≤ q then 1 else 0) + (ENNReal.ofReal ρ) * (ch.mass state : ENNReal) / space
noncomputable def doneValue (ρ : ℝ) {σ : Type} (ch : Charges σ) (space : Nat) (state : σ) : ENNReal :=
  (ENNReal.ofReal ρ) * (ch.mass state : ENNReal) / space

theorem terminal_le_of_over (ρ : ℝ) {σ : Type} (ch : Charges σ) (space q : Nat) (state : σ) {β : Type}
    (result : Option β × σ) (hover : q < ch.calls state + 1)
    (hcalls : ch.calls state + 1 ≤ ch.calls result.2) (hmass : ch.mass result.2 ≤ ch.mass state) :
    terminal (stopValue ρ ch space q) (potential ρ ch space q) result ≤
      (ENNReal.ofReal ρ) * (ch.mass state : ENNReal) / space := by
  have hnot : ¬ch.calls result.2 ≤ q := by omega
  have hm : (ENNReal.ofReal ρ) * (ch.mass result.2 : ENNReal) / space ≤
      (ENNReal.ofReal ρ) * (ch.mass state : ENNReal) / space :=
    ENNReal.div_le_div_right (mul_le_mul' le_rfl (by exact_mod_cast hmass)) _
  rcases result with ⟨_ | answer, after⟩
  · simpa [terminal, stopValue, hnot] using hm
  · simpa [terminal, potential, continuation, hnot] using hm

theorem payment_of_stepBound (ρ : ℝ) {σ : Type} (step : Step m spec σ) (ch : Charges σ) (space q : Nat)
    (input : spec.Domain) (state : σ) (h : StepBound step ch space q input state)
    (hspace : 0 < space) (hq2 : 2 * q ≤ space) (hρ0 : 0 ≤ ρ)
    (hρ : ρ * (space : ℝ) ≤ 2 * ((space : ℝ) - q)) (hprobes : ch.probes state ≤ ch.calls state) :
    expectedValue (step input state) (terminal (stopValue ρ ch space q) (potential ρ ch space q)) ≤
      potential ρ ch space q state := by
  have hq : 2 * q ≤ space := hq2
  rcases h with h | h | h | h
  · apply expectedValue_le_of_support
    rintro ⟨answer, after⟩ hresult
    obtain ⟨hcalls, hp, hmass⟩ := h.1 _ hresult
    have hsome : answer ≠ none := by
      have := (probEvent_eq_zero_iff.mp h.2) _ hresult
      simpa using this
    obtain ⟨answer, rfl⟩ := Option.ne_none_iff_exists'.mp hsome
    simp only [terminal, Option.elim_some, potential]
    exact add_le_add (continuation_anti space q _ _ _ _ hspace hq hprobes hcalls hp)
      (ENNReal.div_le_div_right (mul_le_mul' le_rfl (by exact_mod_cast hmass)) _)
  · apply expectedValue_le_of_support
    rintro ⟨answer, after⟩ hresult
    obtain ⟨hcalls, hp, hmass⟩ := h.1 _ hresult
    by_cases hc : ch.calls state + 1 ≤ q
    · rw [if_pos hc] at hmass
      have hsome : answer ≠ none := by
        have := (probEvent_eq_zero_iff.mp h.2) _ hresult
        simpa using this
      obtain ⟨answer, rfl⟩ := Option.ne_none_iff_exists'.mp hsome
      simp only [terminal, Option.elim_some, potential]
      have hcont := continuation_anti space q (ch.calls state + 1) (ch.probes state) (ch.calls after)
        (ch.probes after) hspace hq (by omega) hcalls hp
      have hpay := continuation_pay_rate ρ space q (ch.calls state) (ch.probes state) hspace hq2 hρ0 hρ hprobes hc
      have hm : (ENNReal.ofReal ρ) * (ch.mass after : ENNReal) / space ≤
          (ENNReal.ofReal ρ) * (ch.mass state : ENNReal) / space + (ENNReal.ofReal ρ) / space := by
        rw [← ENNReal.add_div]
        apply ENNReal.div_le_div_right
        calc
          (ENNReal.ofReal ρ) * (ch.mass after : ENNReal) ≤
              (ENNReal.ofReal ρ) * ((ch.mass state + 1 : Nat) : ENNReal) :=
            mul_le_mul' le_rfl (by exact_mod_cast hmass)
          _ = (ENNReal.ofReal ρ) * (ch.mass state : ENNReal) + (ENNReal.ofReal ρ) := by
            rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one]
      calc
        _ ≤ continuation space q (ch.calls state + 1) (ch.probes state) +
            ((ENNReal.ofReal ρ) * (ch.mass state : ENNReal) / space + (ENNReal.ofReal ρ) / space) :=
          add_le_add hcont hm
        _ = (continuation space q (ch.calls state + 1) (ch.probes state) + (ENNReal.ofReal ρ) / space) +
            (ENNReal.ofReal ρ) * (ch.mass state : ENNReal) / space := by ring
        _ ≤ _ := add_le_add hpay le_rfl
    · rw [if_neg hc, add_zero] at hmass
      exact (terminal_le_of_over ρ ch space q state (answer, after) (by omega) hcalls hmass).trans le_add_self
  · by_cases hc : ch.calls state + 1 ≤ q
    · have hpoint : ∀ result ∈ support (step input state),
          terminal (stopValue ρ ch space q) (potential ρ ch space q) result ≤
            (if result.1 = none then 1 else continuation space q (ch.calls state + 1) (ch.probes state)) +
              (ENNReal.ofReal ρ) * (ch.mass state : ENNReal) / space := by
        rintro ⟨answer, after⟩ hresult
        obtain ⟨hcalls, hp, hmass⟩ := h.1 _ hresult
        have hm : (ENNReal.ofReal ρ) * (ch.mass after : ENNReal) / space ≤
            (ENNReal.ofReal ρ) * (ch.mass state : ENNReal) / space :=
          ENNReal.div_le_div_right (mul_le_mul' le_rfl (by exact_mod_cast hmass)) _
        rcases answer with _ | answer
        · simp only [terminal, Option.elim_none, stopValue, if_true]
          exact add_le_add (by split <;> simp) hm
        · simp only [terminal, Option.elim_some, potential, reduceCtorEq, if_false]
          exact add_le_add (continuation_anti space q _ _ _ _ hspace hq (by omega) hcalls hp) hm
      calc
        _ ≤ expectedValue (step input state) (fun result =>
            (if result.1 = none then 1 else continuation space q (ch.calls state + 1) (ch.probes state)) +
              (ENNReal.ofReal ρ) * (ch.mass state : ENNReal) / space) := expectedValue_mono_of_support hpoint
        _ ≤ Pr[fun result => result.1 = none | step input state] +
            (1 - Pr[fun result => result.1 = none | step input state]) *
              continuation space q (ch.calls state + 1) (ch.probes state) +
              (ENNReal.ofReal ρ) * (ch.mass state : ENNReal) / space :=
          expected_stop_le _ _ _
        _ ≤ ((space : ENNReal)⁻¹ + continuation space q (ch.calls state + 1) (ch.probes state)) +
            (ENNReal.ofReal ρ) * (ch.mass state : ENNReal) / space := by
          refine add_le_add (add_le_add h.2 ?_) le_rfl
          exact mul_le_of_le_one_left' tsub_le_self
        _ ≤ _ := by
          rw [add_comm ((space : ENNReal)⁻¹)]
          exact add_le_add (continuation_pay space q _ _ hspace hq hprobes hc) le_rfl
    · apply expectedValue_le_of_support
      rintro ⟨answer, after⟩ hresult
      obtain ⟨hcalls, hp, hmass⟩ := h.1 _ hresult
      exact (terminal_le_of_over ρ ch space q state (answer, after) (by omega) hcalls hmass).trans le_add_self
  · by_cases hc : ch.calls state + 1 ≤ q
    · have hpoint : ∀ result ∈ support (step input state),
          terminal (stopValue ρ ch space q) (potential ρ ch space q) result ≤
            (if result.1 = none then 1 else continuation space q (ch.calls state + 1) (ch.probes state + 1)) +
              (ENNReal.ofReal ρ) * (ch.mass state : ENNReal) / space := by
        rintro ⟨answer, after⟩ hresult
        obtain ⟨hcalls, hp, hmass⟩ := h.1 _ hresult
        have hm : (ENNReal.ofReal ρ) * (ch.mass after : ENNReal) / space ≤
            (ENNReal.ofReal ρ) * (ch.mass state : ENNReal) / space :=
          ENNReal.div_le_div_right (mul_le_mul' le_rfl (by exact_mod_cast hmass)) _
        rcases answer with _ | answer
        · simp only [terminal, Option.elim_none, stopValue, if_true]
          exact add_le_add (by split <;> simp) hm
        · simp only [terminal, Option.elim_some, potential, reduceCtorEq, if_false]
          exact add_le_add (continuation_anti space q _ _ _ _ hspace hq (by omega) hcalls hp) hm
      calc
        _ ≤ expectedValue (step input state) (fun result =>
            (if result.1 = none then 1 else continuation space q (ch.calls state + 1) (ch.probes state + 1)) +
              (ENNReal.ofReal ρ) * (ch.mass state : ENNReal) / space) := expectedValue_mono_of_support hpoint
        _ ≤ Pr[fun result => result.1 = none | step input state] +
            (1 - Pr[fun result => result.1 = none | step input state]) *
              continuation space q (ch.calls state + 1) (ch.probes state + 1) +
              (ENNReal.ofReal ρ) * (ch.mass state : ENNReal) / space :=
          expected_stop_le _ _ _
        _ ≤ _ := add_le_add (continuation_probe space q _ _ hspace hq hprobes hc _ h.2) le_rfl
    · apply expectedValue_le_of_support
      rintro ⟨answer, after⟩ hresult
      obtain ⟨hcalls, hp, hmass⟩ := h.1 _ hresult
      exact (terminal_le_of_over ρ ch space q state (answer, after) (by omega) hcalls hmass).trans le_add_self

theorem stop_add_mass_eq (ρ : ℝ) {β σ : Type} (ch : Charges σ) (space q : Nat) (law : m (Option β × σ)) :
    Pr[fun result => result.1 = none ∧ ch.calls result.2 ≤ q | law] +
      (ENNReal.ofReal ρ) * (∑' result, Pr[= result | law] * (ch.mass result.2 : ENNReal)) / space =
      expectedValue law (terminal (stopValue ρ ch space q) (doneValue ρ ch space)) := by
  have hfun : terminal (stopValue ρ ch space q) (doneValue ρ ch space) = fun result : Option β × σ =>
      (if result.1 = none ∧ ch.calls result.2 ≤ q then 1 else 0) +
        (ENNReal.ofReal ρ) * (ch.mass result.2 : ENNReal) / space := by
    funext result
    rcases result with ⟨_ | answer, after⟩
    · simp [terminal, stopValue]
    · simp [terminal, doneValue]
  rw [hfun, expectedValue_add, expectedValue_ite_one, expectedValue_def]
  congr 1
  simp only [div_eq_mul_inv, ← mul_assoc, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro result
  ring

theorem run_potential_initial (ρ : ℝ) {α σ : Type} (step : Step m spec σ) (ch : Charges σ) (q : Nat)
    (hq2 : q ≤ 2 ^ 127) (hρ0 : 0 ≤ ρ)
    (hρ : ρ * (2 ^ 128 : ℝ) ≤ 2 * ((2 ^ 128 : ℝ) - q)) (inv : σ → Prop)
    (hpreserve : ∀ input state, inv state → ch.probes state ≤ ch.calls state →
      ∀ answer after, (some answer, after) ∈ support (step input state) → inv after)
    (hbound : ∀ input state, inv state → ch.probes state ≤ ch.calls state →
      StepBound step ch (2 ^ 128) q input state)
    (program : OracleComp spec α) (init : σ) (hinit : inv init) (hprobes : ch.probes init = 0)
    (hmass : ch.mass init = 0) :
    Pr[fun result => result.1 = none ∧ ch.calls result.2 ≤ q | LargePotential.run step program init] +
      (ENNReal.ofReal ρ) * (∑' result, Pr[= result | LargePotential.run step program init] *
        (ch.mass result.2 : ENNReal)) / 2 ^ 128 ≤
      ENNReal.ofReal (2 * ((q : ℝ) / 2 ^ 128) - ((q : ℝ) / 2 ^ 128) ^ 2) := by
  have h : Pr[fun result => result.1 = none ∧ ch.calls result.2 ≤ q | LargePotential.run step program init] +
      (ENNReal.ofReal ρ) * (∑' result, Pr[= result | LargePotential.run step program init] *
        (ch.mass result.2 : ENNReal)) / ((2 ^ 128 : Nat) : ENNReal) ≤
      potential ρ ch (2 ^ 128) q init := by
    rw [stop_add_mass_eq ρ]
    refine run_expected_le step (fun state => inv state ∧ ch.probes state ≤ ch.calls state)
      (potential ρ ch (2 ^ 128) q) (stopValue ρ ch (2 ^ 128) q) (doneValue ρ ch (2 ^ 128))
      ?_ ?_ ?_ program init ⟨hinit, by omega⟩
    · intro state _
      exact le_add_self
    · rintro input state ⟨hi, hp⟩ answer after hmem
      exact ⟨hpreserve input state hi hp answer after hmem,
        (hbound input state hi hp).probes_le hp _ hmem⟩
    · rintro input state ⟨hi, hp⟩
      exact payment_of_stepBound ρ step ch (2 ^ 128) q input state (hbound input state hi hp) (by positivity) (by omega) hρ0 (by convert hρ using 1 <;> norm_num) hp
  rw [Nat.cast_pow, Nat.cast_ofNat] at h
  refine h.trans ?_
  have hmono := continuation_anti (2 ^ 128) q 0 0 (ch.calls init) (ch.probes init) (by positivity)
    (by omega) (by omega) (Nat.zero_le _) (by omega)
  unfold potential
  rw [hmass, Nat.cast_zero, mul_zero, ENNReal.zero_div, add_zero]
  refine hmono.trans (le_of_eq ?_)
  unfold continuation
  rw [if_pos (Nat.zero_le q), Nat.cast_zero, Nat.cast_pow, Nat.cast_ofNat]
  exact initial_potential q

theorem residual_potential_rate (ρ : ℝ) {Coord Cell AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
    [ClaudeWCT.W9.T3.Security.FamResidual.Seeds Coord] [Fintype Coord] [DecidableEq Coord] [Fintype Cell]
    [DecidableEq Cell] {Result : Type} (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat)
    (hq : q ≤ 2 ^ 127) (hρ0 : 0 ≤ ρ)
    (hρ : ρ * (2 ^ 128 : ℝ) ≤ 2 * ((2 ^ 128 : ℝ) - q)) (program : OracleComp (SigGolfCandidate.T3.Security.LargeResidual.World auxSpec Coord Cell) Result) :
    Pr[fun result => result.1 = none ∧ result.2.counters.calls ≤ q |
        ClaudeWCT.W9.T3.Security.FamResidual.lazyRun aux q program
          SigGolfCandidate.T3.Security.LargeResidual.initial] +
      ENNReal.ofReal ρ * (∑' result,
        Pr[= result | ClaudeWCT.W9.T3.Security.FamResidual.lazyRun aux q program
          SigGolfCandidate.T3.Security.LargeResidual.initial] *
          (result.2.counters.mass : ENNReal)) / 2 ^ 128 ≤
      ENNReal.ofReal (2 * ((q : ℝ) / 2 ^ 128) - ((q : ℝ) / 2 ^ 128) ^ 2) := by
  have h := run_potential_initial ρ (ClaudeWCT.W9.T3.Security.FamResidual.residualStep aux q)
    SigGolfCandidate.T3.Security.LargeResidual.charges q hq hρ0 hρ
    ClaudeWCT.W9.T3.Security.FamResidual.Inv
    (fun input state hinv _ answer after hafter =>
      ClaudeWCT.W9.T3.Security.FamResidual.residual_preserve aux q input state hinv answer after hafter)
    (fun input state hinv _ => ClaudeWCT.W9.T3.Security.FamResidual.residual_step_bound aux q input state hinv)
    program SigGolfCandidate.T3.Security.LargeResidual.initial
    ClaudeWCT.W9.T3.Security.FamResidual.initial_inv rfl rfl
  rw [ClaudeWCT.W9.T3.Security.FamResidual.run_residual] at h
  exact h
/-- The maximal convenient linear payment used by the continuous schedule. -/
noncomputable def budgetRate (q : Nat) : ℝ := 2 - 2 * (q : ℝ) / 2 ^ 128

theorem budgetRate_nonneg (q : Nat) (hq : q ≤ 2 ^ 127) : 0 ≤ budgetRate q := by
  have hq' : (q : ℝ) ≤ 2 ^ 127 := by exact_mod_cast hq
  unfold budgetRate
  have hdiv : 2 * (q : ℝ) / 2 ^ 128 ≤ 1 := by
    apply (div_le_one (by positivity : (0 : ℝ) < 2 ^ 128)).mpr
    calc
      (2:ℝ)*(q:ℝ) ≤ 2*(2^127) := mul_le_mul_of_nonneg_left hq' (by norm_num)
      _ = 2^128 := by norm_num
  linarith

theorem budgetRate_mul (q : Nat) :
    budgetRate q * (2 ^ 128 : ℝ) = 2 * ((2 ^ 128 : ℝ) - q) := by
  unfold budgetRate
  field_simp <;> ring

end ClaudeWCT.W9.T3.Security.LargeCoupling.Flexible
end

/-! Bank forecasts with an arbitrary stop-loss threshold. -/
section
namespace ClaudeWCT.Bank.WCT.Flexible
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.Bank.WCT
open CaseC (BankCore BankCore.expose)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable (θ : ENNReal) (horizon : Nat)
noncomputable def excessForecast (R : Nat) (X : List HashOutput) : ENNReal :=
  ClaudeWCT.Numerics.Law.lawAvg (S0 horizon).law R
    (fun W => (S0 horizon).price ((S0 horizon).proposals X ++ W) - θ)
theorem excessForecast_step (R : Nat) (X : List HashOutput) :
    expectedValue (S0 horizon).accepted (fun A => excessForecast θ horizon R (X ++ [A])) =
      excessForecast θ horizon (R + 1) X := by
  unfold excessForecast
  rw [ClaudeWCT.Numerics.Law.lawAvg_succ]
  have hA (A : HashOutput) : ClaudeWCT.Numerics.Law.lawAvg (S0 horizon).law R
      (fun W => (S0 horizon).price ((S0 horizon).proposals (X ++ [A]) ++ W) - θ) =
      (fun p : WProposal => ClaudeWCT.Numerics.Law.lawAvg (S0 horizon).law R
        (fun W => (S0 horizon).price ((S0 horizon).proposals X ++ p :: W) - θ))
        ((S0 horizon).proposal A) := by
    simp [FtsBankSpec.proposals, List.map_append, List.append_assoc]
  simp_rw [hA]
  exact (S0 horizon).expected_accepted_proposal (fun p => ClaudeWCT.Numerics.Law.lawAvg (S0 horizon).law R
    (fun W => (S0 horizon).price ((S0 horizon).proposals X ++ p :: W) - θ))
theorem average_forecast_le (R : Nat) (X : List HashOutput) :
    BPORS.finiteAverage (fun N : HashOutput => (S0 horizon).forecast R X N) ≤
      (θ + excessForecast θ horizon R X) / 2 ^ 128 := by
  rw [(S0 horizon).average_forecast]
  apply ENNReal.div_le_div_right
  unfold excessForecast
  calc
    _ ≤ ClaudeWCT.Numerics.Law.lawAvg (S0 horizon).law R
          (fun W => θ + ((S0 horizon).price ((S0 horizon).proposals X ++ W) - θ)) :=
      ClaudeWCT.Numerics.Law.lawAvg_mono (S0 horizon).law R fun W => le_add_tsub
    _ = _ := by
      rw [ClaudeWCT.Numerics.Law.lawAvg_add, ClaudeWCT.Numerics.Law.lawAvg_const (S0 horizon).law (S0 horizon).law_sum]
noncomputable def ledger (R : Nat) (targets X : List HashOutput) (slack : Nat) : ENNReal :=
  (targets.map fun N => (S0 horizon).forecast R X N).sum + (slack : ENNReal) * excessForecast θ horizon R X / 2 ^ 128
theorem ledger_slack_succ (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    ledger θ horizon R targets X (slack + 1) =
      ledger θ horizon R targets X slack + excessForecast θ horizon R X / 2 ^ 128 := by
  unfold ledger
  rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, ENNReal.add_div, add_assoc]
theorem ledger_birth (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun a => ledger θ horizon R (targets ++ [a]) X slack) ≤
      ledger θ horizon R targets X (slack + 1) + θ / 2 ^ 128 := by
  have hfa : expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun a => (S0 horizon).forecast R X a) ≤
      (θ + excessForecast θ horizon R X) / 2 ^ 128 := by
    rw [BPORS.expected_uniform_eq_finiteAverage]
    exact average_forecast_le θ horizon R X
  have hsplit : ∀ a, ledger θ horizon R (targets ++ [a]) X slack =
      ledger θ horizon R targets X slack + (S0 horizon).forecast R X a := by
    intro a
    simp only [ledger, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
      List.sum_nil, add_zero]
    ring
  simp_rw [hsplit]
  rw [expectedValue_add, expectedValue_const (by simp : Pr[⊥ | ($ᵗ HashOutput : ProbComp HashOutput)] = 0),
    ledger_slack_succ θ, add_assoc]
  exact add_le_add le_rfl (hfa.trans (by rw [ENNReal.add_div, add_comm]))
theorem ledger_expose (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    expectedValue (S0 horizon).accepted (fun A => ledger θ horizon R targets (X ++ [A]) slack) =
      ledger θ horizon (R + 1) targets X slack := by
  unfold ledger
  rw [expectedValue_add, CaseC.expectedValue_list_sum']
  refine congrArg₂ (· + ·) (congrArg List.sum ?_) ?_
  · apply List.map_congr_left
    intro N _
    exact (S0 horizon).forecast_step R X N
  · simp only [div_eq_mul_inv]
    rw [show (fun A : HashOutput => (slack : ENNReal) * excessForecast θ horizon R (X ++ [A]) * (2 ^ 128 : ENNReal)⁻¹) =
        fun A => (slack : ENNReal) * (2 ^ 128 : ENNReal)⁻¹ * excessForecast θ horizon R (X ++ [A]) by
      funext A; ring]
    rw [CaseC.pmf_expectedValue_left_mul, excessForecast_step θ]
    ring
theorem ledger_freshPrice (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    (S0 horizon).freshPrice (fun A => ledger θ horizon R targets (X ++ [A]) slack) =
      ledger θ horizon (R + 1) targets X slack := by
  rw [← (S0 horizon).expected_accepted, ledger_expose θ]
theorem ledger_search (secret : BitVec 256) (rho : Digest) (message : Message) (fuel : Nat)
    (hlimit : fuel ≤ 2 ^ 32) (cache : Sampling.RCache)
    (hreject : Sampling.CachedTrialsReject (Sampling.digestTrial rho message) (S0 horizon).decode 0 (2 ^ 32) cache)
    (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    expectedValue (Sampling.roRun secret ((S0 horizon).search rho message 0 fuel) cache)
      (fun result => result.1.elim (ledger θ horizon (R + 1) targets X slack)
        (fun found => ledger θ horizon R targets (X ++ [found.2]) slack)) ≤
      ledger θ horizon (R + 1) targets X slack :=
  (S0 horizon).search_le_price secret rho message fuel hlimit cache hreject _ _ _ le_rfl
    (ledger_freshPrice θ horizon R targets X slack).le
theorem ledger_win (R : Nat) (targets X : List HashOutput) (slack : Nat) (N : HashOutput) (hN : N ∈ targets)
    (hadm : WCT9.admissible N = true) (hcov : Covered X N) :
    1 ≤ ledger θ horizon R targets X slack :=
  calc
    (1 : ENNReal) ≤ (S0 horizon).score X N := (S0 horizon).one_le_score X N hadm hcov
    _ ≤ (S0 horizon).forecast R X N := (S0 horizon).score_le_forecast R X N
    _ ≤ (targets.map fun N => (S0 horizon).forecast R X N).sum := List.le_sum_of_mem (List.mem_map_of_mem hN)
    _ ≤ _ := le_self_add
noncomputable def corePotential (b : BankCore) : ENNReal :=
  if horizon < b.exposures.length then 0
  else if b.reused = true then 1 + b.reuse
  else ledger θ horizon (horizon - b.exposures.length) b.targets b.exposures b.slack + b.reuse
theorem core_birth (b : BankCore) (s : Nat) (hs : b.slack = s + 1) (C' : HashOutput → ENNReal)
    (hC : ∀ N, C' N ≤ b.reuse + (S0 horizon).admInd N / 2 ^ 128) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
        (fun N => corePotential θ horizon { b with targets := b.targets ++ [N], slack := s, reuse := C' N }) ≤
      corePotential θ horizon b + (θ + (S0 horizon).admBound) / 2 ^ 128 := by
  have hadm : expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun N => (S0 horizon).admInd N / 2 ^ 128) ≤
      (S0 horizon).admBound / 2 ^ 128 := by
    simp only [div_eq_mul_inv]
    rw [expectedValue_mul_const]
    exact mul_le_mul' (by simpa [div_eq_mul_inv] using (S0 horizon).expected_admInd_tight) le_rfl
  have h54_adm : (S0 horizon).admBound ≤ θ + (S0 horizon).admBound := le_add_self
  have h54_sum : θ + (S0 horizon).admBound ≤ θ + (S0 horizon).admBound := le_rfl
  unfold corePotential
  simp only
  by_cases hd : horizon < b.exposures.length
  · simp only [hd, if_true]
    exact (expectedValue_le_of_le _ fun _ => le_rfl).trans bot_le
  simp only [hd, if_false]
  by_cases hr : b.reused = true
  · simp only [hr, if_true]
    calc
      _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
            (fun N => (S0 horizon).admInd N / 2 ^ 128 + (1 + b.reuse)) :=
        expectedValue_mono _ fun N => (add_le_add le_rfl (hC N)).trans (le_of_eq (by ring))
      _ ≤ (S0 horizon).admBound / 2 ^ 128 + (1 + b.reuse) :=
        (CaseC.expectedValue_add_const_le _ _ _).trans (add_le_add hadm le_rfl)
      _ ≤ _ := by
        rw [add_comm]
        exact add_le_add le_rfl (ENNReal.div_le_div_right h54_adm _)
  · simp only [hr, Bool.false_eq_true, if_false]
    set R := horizon - b.exposures.length
    calc
      _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
          (fun N => (ledger θ horizon R (b.targets ++ [N]) b.exposures s + (S0 horizon).admInd N / 2 ^ 128) + b.reuse) :=
        expectedValue_mono _ fun N => (add_le_add le_rfl (hC N)).trans (le_of_eq (by ring))
      _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
          (fun N => ledger θ horizon R (b.targets ++ [N]) b.exposures s + (S0 horizon).admInd N / 2 ^ 128) + b.reuse :=
        CaseC.expectedValue_add_const_le _ _ _
      _ ≤ (ledger θ horizon R b.targets b.exposures (s + 1) + θ / 2 ^ 128 +
            (S0 horizon).admBound / 2 ^ 128) + b.reuse := by
        rw [expectedValue_add]
        exact add_le_add (add_le_add (ledger_birth θ horizon R b.targets b.exposures s) hadm) le_rfl
      _ ≤ _ := by
        rw [← hs, add_assoc (ledger θ _ _ _ _ _), ← ENNReal.add_div,
          show ledger θ horizon R b.targets b.exposures b.slack +
            (θ + (S0 horizon).admBound) / 2 ^ 128 + b.reuse =
            (ledger θ horizon R b.targets b.exposures b.slack + b.reuse) +
            (θ + (S0 horizon).admBound) / 2 ^ 128 by ring]
theorem core_sign (b : BankCore) (cache : Sampling.RCache) (m : Message) (C' : ENNReal)
    (hC : C' + (S0 horizon).reuseMass cache m ≤ b.reuse) (secret : BitVec 256) (fuel : Nat)
    (hfuel : fuel ≤ 2 ^ 32) :
    expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho =>
      if (S0 horizon).Reuse cache rho m then
        corePotential θ horizon { b with reused := true, reuse := C' }
      else expectedValue (Sampling.roRun secret (WCT9.digestSearch rho m 0 fuel) cache)
        (fun result => corePotential θ horizon (b.expose C' (result.1.map Prod.snd)))) ≤
      corePotential θ horizon b := by
  have h : expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho =>
      if (S0 horizon).Reuse cache rho m then corePotential θ horizon { b with reused := true, reuse := C' }
      else expectedValue (Sampling.roRun secret ((S0 horizon).search rho m 0 fuel) cache)
        (fun result => corePotential θ horizon (b.expose C' (result.1.map Prod.snd)))) ≤
      corePotential θ horizon b := by
    have hlenA : ∀ (o : Option HashOutput), b.exposures.length ≤ (b.exposures ++ o.toList).length := by
      intro o; simp
    by_cases hd : horizon < b.exposures.length
    · apply expectedValue_le_of_le
      intro rho
      have h0 : ∀ (o : Option HashOutput), corePotential θ horizon (b.expose C' o) = 0 := by
        intro o
        unfold corePotential BankCore.expose
        simp only
        rw [if_pos (lt_of_lt_of_le hd (hlenA o))]
      split_ifs
      · unfold corePotential; simp only; rw [if_pos hd]; exact bot_le
      · exact (expectedValue_le_of_le _ fun result => (h0 _).le).trans bot_le
    by_cases hr : b.reused = true
    · have hb : corePotential θ horizon b = 1 + b.reuse := by unfold corePotential; simp [hd, hr]
      rw [hb]
      apply expectedValue_le_of_le
      intro rho
      have hle : ∀ (o : Option HashOutput), corePotential θ horizon (b.expose C' o) ≤ 1 + b.reuse := by
        intro o
        unfold corePotential BankCore.expose
        simp only [hr, if_true]
        split_ifs
        · exact bot_le
        · exact add_le_add le_rfl (le_of_add_le_left hC)
      split_ifs
      · unfold corePotential; simp only [hd, if_false, if_true]; exact add_le_add le_rfl (le_of_add_le_left hC)
      · exact expectedValue_le_of_le _ fun result => hle _
    have hr' : b.reused = false := by simpa using hr
    set R0 := horizon - b.exposures.length with hR0
    have hb : corePotential θ horizon b = ledger θ horizon R0 b.targets b.exposures b.slack + b.reuse := by
      unfold corePotential; simp only [hd, hr', if_false, Bool.false_eq_true]; rfl
    have hsearch : ∀ rho, ¬(S0 horizon).Reuse cache rho m →
        expectedValue (Sampling.roRun secret ((S0 horizon).search rho m 0 fuel) cache)
          (fun result => corePotential θ horizon (b.expose C' (result.1.map Prod.snd))) ≤
            ledger θ horizon R0 b.targets b.exposures b.slack + C' := by
      intro rho hnr
      have hrej : Sampling.CachedTrialsReject (Sampling.digestTrial rho m) (S0 horizon).decode 0 (2 ^ 32) cache := by
        unfold FtsBankSpec.Reuse at hnr; push Not at hnr; exact hnr
      by_cases hlen : b.exposures.length < horizon
      · obtain ⟨R, hR⟩ : ∃ R, R0 = R + 1 := ⟨R0 - 1, by omega⟩
        calc
          _ ≤ expectedValue (Sampling.roRun secret ((S0 horizon).search rho m 0 fuel) cache)
              (fun result => result.1.elim (ledger θ horizon (R + 1) b.targets b.exposures b.slack)
                (fun found => ledger θ horizon R b.targets (b.exposures ++ [found.2]) b.slack) + C') := by
            apply expectedValue_mono
            intro result
            rcases result with ⟨_ | found, cache'⟩
            · unfold corePotential BankCore.expose
              simp only [Option.map_none, Option.toList_none, List.append_nil, hd, if_false, hr',
                Bool.false_eq_true, Option.elim_none]
              rw [← hR]
            · unfold corePotential BankCore.expose
              have hl1 : (b.exposures ++ [found.2]).length = b.exposures.length + 1 := by simp
              have hnd : ¬horizon < (b.exposures ++ [found.2]).length := by omega
              simp only [Option.map_some, Option.toList_some, hnd, if_false, hr', Bool.false_eq_true,
                Option.elim_some]
              rw [show horizon - (b.exposures ++ [found.2]).length = R by omega]
          _ ≤ ledger θ horizon (R + 1) b.targets b.exposures b.slack + C' :=
            (CaseC.expectedValue_add_const_le _ _ _).trans
              (add_le_add (ledger_search θ horizon secret rho m fuel hfuel cache hrej R b.targets b.exposures b.slack) le_rfl)
          _ = _ := by rw [hR]
      · apply expectedValue_le_of_le
        intro result
        rcases result with ⟨_ | found, cache'⟩
        · unfold corePotential BankCore.expose
          simp only [Option.map_none, Option.toList_none, List.append_nil, hd, if_false, hr', Bool.false_eq_true]
          exact le_rfl
        · unfold corePotential BankCore.expose
          have hnd : horizon < (b.exposures ++ [found.2]).length := by simp; omega
          simp only [Option.map_some, Option.toList_some, hnd, if_true]
          exact bot_le
    rw [hb]
    calc
      _ ≤ expectedValue ($ᵗ Digest : ProbComp Digest)
          (fun rho => (if (S0 horizon).Reuse cache rho m then 1 else 0) +
            (ledger θ horizon R0 b.targets b.exposures b.slack + C')) := by
        apply expectedValue_mono
        intro rho
        by_cases hre : (S0 horizon).Reuse cache rho m
        · rw [if_pos hre, if_pos hre]
          unfold corePotential
          simp only [hd, if_false, if_true]
          exact add_le_add le_rfl le_add_self
        · rw [if_neg hre, if_neg hre, zero_add]
          exact hsearch rho hre
      _ ≤ (S0 horizon).reuseMass cache m + (ledger θ horizon R0 b.targets b.exposures b.slack + C') :=
        (CaseC.expectedValue_add_const_le _ _ _).trans (add_le_add ((S0 horizon).reuse_probability_le cache m) le_rfl)
      _ ≤ _ := by
        rw [add_comm (ledger θ _ _ _ _ _), ← add_assoc, add_comm ((S0 horizon).reuseMass cache m),
          add_comm _ (ledger θ _ _ _ _ _)]
        exact add_le_add le_rfl hC
  simp only [← wct_digestSearch_public (S0 horizon) rfl] at h
  exact h
theorem core_win (b : BankCore) (halive : ¬horizon < b.exposures.length)
    (h : b.reused = true ∨ ∃ N ∈ b.targets, WCT9.admissible N = true ∧ Covered b.exposures N) :
    1 ≤ corePotential θ horizon b := by
  unfold corePotential
  rw [if_neg halive]
  by_cases hr : b.reused = true
  · rw [if_pos hr]; exact le_self_add
  · rw [if_neg hr]
    obtain ⟨N, hN, hadm, hcov⟩ := h.resolve_left hr
    exact (ledger_win θ horizon _ _ _ _ N hN hadm hcov).trans le_self_add
theorem core_initial (rate : ENNReal) (hexc : ExcessBoundAt (2 ^ 32) θ rate) (budget : Nat) :
    corePotential θ (2 ^ 32) ⟨[], [], false, 0, budget⟩ ≤
      (budget : ENNReal) * rate / 2 ^ 128 := by
  unfold corePotential ledger excessForecast
  simp only [List.length_nil, Nat.not_lt_zero, if_false, Bool.false_eq_true, Nat.sub_zero, add_zero,
    List.map_nil, List.sum_nil, zero_add]
  apply ENNReal.div_le_div_right
  apply mul_le_mul' le_rfl
  exact hexc
end ClaudeWCT.Bank.WCT.Flexible
end


namespace ClaudeWCT.Bank.FlexibleGame
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3M.Final
open CaseC (IsDigestInput Birth FreshSigning countOf lazyOf)
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpecL P) (θ : ENNReal)
variable {Sig : Type}

noncomputable def excessForecast (R : Nat) (X : List HashOutput) : ENNReal :=
  ClaudeWCT.Numerics.Law.lawAvg S.law R (fun W => S.price (S.proposals X ++ W)-θ)
theorem excessForecast_step (R : Nat) (X : List HashOutput) :
    expectedValue S.accepted (fun A => excessForecast S θ R (X ++ [A])) =
      excessForecast S θ (R+1) X :=
  Flexible.excessForecast_step S.toFtsBankSpec θ S.horizon R X
theorem average_forecast_le (R : Nat) (X : List HashOutput) :
    BPORS.finiteAverage (fun N : HashOutput => S.forecast R X N) ≤
      (θ+excessForecast S θ R X)/2^128 :=
  Flexible.average_forecast_le S.toFtsBankSpec θ S.horizon R X

noncomputable def birthCharge (budget : Nat) : (Interaction' Sig).Domain → BankState Sig → ENNReal
  | .inl (.inr x), st => if Birth budget x st.2 then (θ+S.admBound)/2^128 else 0
  | _, _ => 0
theorem birthCharge_eq (budget : Nat) (input : (Interaction' Sig).Domain) (st : BankState Sig) :
    birthCharge S θ budget input st = (θ+S.admBound)/2^128*birthWeight budget input st.2 := by
  rcases input with (n|x)|request
  · simp [birthCharge,birthWeight]
  · simp only [birthCharge,birthWeight]
    split_ifs <;> simp
  · simp [birthCharge,birthWeight]
noncomputable def excessTerm (budget count : Nat) (g : Ghost Sig) : ENNReal :=
  ((budget - count : Nat) : ENNReal) * (excessForecast S θ) (S.horizon - g.exposures.length) g.exposures / 2 ^ 128
noncomputable def livePotential (budget count : Nat) (g : Ghost Sig) (lazy : LazyPrivate.State) : ENNReal :=
  if g.dead = true ∨ budget < count then 0
  else if g.reused = true then 1 + S.reusePotential lazy
  else S.bankValue g + S.reusePotential lazy + (excessTerm S θ) budget count g
noncomputable def potential (budget : Nat) (st : BankState Sig) : ENNReal :=
  (livePotential S θ) budget (countOf st.2) st.1 (lazyOf st.2)
theorem livePotential_count_anti (budget : Nat) {count count' : Nat} (h : count ≤ count') (g : Ghost Sig)
    (lazy : LazyPrivate.State) : (livePotential S θ) budget count' g lazy ≤ (livePotential S θ) budget count g lazy := by
  unfold livePotential
  by_cases hd : g.dead = true
  · simp [hd]
  by_cases hb : budget < count'
  · simp [hd, hb]
  have hb0 : ¬budget < count := by omega
  have hd' : g.dead = false := by simpa using hd
  simp only [hd', hb, hb0, Bool.false_eq_true, false_or, if_false]
  by_cases hr : g.reused = true
  · simp only [hr, if_true, le_refl]
  · simp only [hr]
    apply add_le_add le_rfl
    unfold excessTerm
    apply ENNReal.div_le_div_right
    apply mul_le_mul' _ le_rfl
    exact_mod_cast Nat.sub_le_sub_left h budget
theorem livePotential_alive (budget count : Nat) (g : Ghost Sig) (lazy : LazyPrivate.State)
    (hd : g.dead = false) (hb : ¬budget < count) (hr : g.reused = false) :
    (livePotential S θ) budget count g lazy = S.bankValue g + S.reusePotential lazy + (excessTerm S θ) budget count g := by
  simp [livePotential, hd, hb, hr]
theorem livePotential_reused (budget count : Nat) (g : Ghost Sig) (lazy : LazyPrivate.State)
    (hd : g.dead = false) (hb : ¬budget < count) (hr : g.reused = true) :
    (livePotential S θ) budget count g lazy = 1 + S.reusePotential lazy := by
  simp [livePotential, hd, hb, hr]
theorem livePotential_reuse_mono (budget count : Nat) (g : Ghost Sig) {lazy lazy' : LazyPrivate.State}
    (h : S.reusePotential lazy' ≤ S.reusePotential lazy) :
    (livePotential S θ) budget count g lazy' ≤ (livePotential S θ) budget count g lazy := by
  unfold livePotential
  split_ifs
  · exact le_rfl
  · exact add_le_add le_rfl h
  · exact add_le_add (add_le_add le_rfl h) le_rfl
theorem excessTerm_succ (budget count : Nat) (g : Ghost Sig) (hc : count < budget) :
    (excessTerm S θ) budget count g = (excessTerm S θ) budget (count + 1) g +
      (excessForecast S θ) (S.horizon - g.exposures.length) g.exposures / 2 ^ 128 := by
  unfold excessTerm
  have hn : budget - count = (budget - (count + 1)) + 1 := by omega
  rw [hn, Nat.cast_add, Nat.cast_one, add_mul, one_mul, ENNReal.add_div]
theorem livePotential_log (budget count : Nat) (g : Ghost Sig) (l : QueryLog (Requests' Sig))
    (lazy : LazyPrivate.State) :
    (livePotential S θ) budget count { g with log := l } lazy = (livePotential S θ) budget count g lazy := rfl
noncomputable def signWeight (budget count : Nat) (g : Ghost Sig) (A : HashOutput) : ENNReal :=
  S.bankValue { g with exposures := g.exposures ++ [A] } +
    (excessTerm S θ) budget count { g with exposures := g.exposures ++ [A] }
theorem freshPrice_signWeight (budget count : Nat) (g : Ghost Sig) (hlen : g.exposures.length < S.horizon) :
    S.freshPrice ((signWeight S θ) budget count g) = S.bankValue g + (excessTerm S θ) budget count g := by
  rw [← S.expected_accepted]
  have hR' : ∀ A : HashOutput, S.horizon - (g.exposures ++ [A]).length = S.horizon - g.exposures.length - 1 := by
    intro A
    simp only [List.length_append, List.length_singleton]
    omega
  have hRR : S.horizon - g.exposures.length - 1 + 1 = S.horizon - g.exposures.length := by omega
  unfold signWeight FtsBankSpec.bankValue excessTerm
  rw [expectedValue_add]
  simp only [hR']
  rw [CaseC.expectedValue_list_sum]
  congr 1
  · congr 1
    apply List.map_congr_left
    intro N _
    rw [S.forecast_step, hRR]
  · simp only [div_eq_mul_inv]
    rw [show (fun A : HashOutput => ((budget - count : Nat) : ENNReal) *
        (excessForecast S θ) (S.horizon - g.exposures.length - 1) (g.exposures ++ [A]) * (2 ^ 128 : ENNReal)⁻¹) =
        fun A => ((budget - count : Nat) : ENNReal) * (2 ^ 128 : ENNReal)⁻¹ *
          (excessForecast S θ) (S.horizon - g.exposures.length - 1) (g.exposures ++ [A]) by
      funext A; ring]
    rw [CaseC.pmf_expectedValue_left_mul, (excessForecast_step S θ), hRR]
    ring
theorem potential_initial_le_rate (budget : Nat) (rate : ENNReal)
    (hrate : ClaudeWCT.Numerics.Law.lawAvg S.law S.horizon (fun W : List P => S.price W - θ) ≤ rate)
    (generated : (Digest × T3.Cache) × QueryRecorded.State)
    (hg : generated ∈ support (QueryRecorded.run keygen QueryRecorded.initial)) :
    (potential S θ) budget ((Ghost.empty : Ghost Sig), generated.2) ≤ (budget : ENNReal) * rate / 2 ^ 128 := by
  have hreuse : S.reusePotential (lazyOf generated.2) = 0 :=
    S.reusePotential_of_noDigest _ (CaseC.keygen_noDigest generated hg)
  unfold potential livePotential
  split_ifs with h1 h2
  · exact bot_le
  · simp [Ghost.empty] at h2
  · simp only [hreuse, add_zero]
    have hbank : S.bankValue (Ghost.empty : Ghost Sig) = 0 := by simp [FtsBankSpec.bankValue, Ghost.empty]
    rw [hbank, zero_add]
    unfold excessTerm
    apply ENNReal.div_le_div_right
    apply mul_le_mul'
    · exact_mod_cast Nat.sub_le budget _
    · have he : (excessForecast S θ) S.horizon [] ≤ rate := by
        unfold excessForecast
        simpa [FtsBankSpec.proposals] using hrate
      simpa [Ghost.empty] using he

variable (pay : T3.Cache → Digest → HashOutput → M (Option Sig))
theorem world_step (published : T3.Cache) (budget : Nat) (input : SphincsSecurity.OracleWorld.Domain)
    (st : BankState Sig) :
    expectedValue ((S.bankImpl pay published budget (.inl input)).run st) (fun r => (potential S θ) budget r.2) ≤
      (potential S θ) budget st + (birthCharge S θ) budget (.inl input) st := by
  rw [S.world_unfold pay published budget input st ((potential S θ) budget)]
  cases input with
  | inl n =>
      have hb : (birthCharge (Sig := Sig) S θ) budget (.inl (.inl n)) st = 0 := rfl
      rw [hb, add_zero]
      apply expectedValue_le_of_support
      intro r hr
      have hl := CaseC.lazy_world_coin n (lazyOf st.2) (r.1, lazyOf r.2) (CaseC.recorded_lazy_support _ _ r hr)
      have hc := CaseC.recorded_count_le _ _ r hr
      change (livePotential S θ) budget (countOf r.2) st.1 (lazyOf r.2) ≤
        (livePotential S θ) budget (countOf st.2) st.1 (lazyOf st.2)
      rw [show lazyOf r.2 = lazyOf st.2 from hl]
      exact (livePotential_count_anti S θ) budget hc st.1 _
  | inr x =>
      have hcount : ∀ r ∈ support (QueryRecorded.run (forwardWorld (.inr x)) st.2),
          countOf r.2 = countOf st.2 + 1 :=
        fun r hr => CreationGame.recorded_world_hash_count x st.2 r hr
      set g := st.1 with hg
      set c := countOf st.2 with hc
      set lz := lazyOf st.2 with hlz
      calc
        _ ≤ expectedValue (QueryRecorded.run (forwardWorld (.inr x)) st.2)
            (fun r => (livePotential S θ) budget (c + 1) (ghostWorld budget (.inr x) g st.2 r.1) (lazyOf r.2)) := by
          apply expectedValue_mono_of_support
          intro r hr
          change (livePotential S θ) budget (countOf r.2) _ _ ≤ _
          rw [hcount r hr]
        _ = expectedValue (LazyPrivate.run (forwardWorld (.inr x)) lz)
            (fun r => (livePotential S θ) budget (c + 1) (ghostWorld budget (.inr x) g st.2 r.1) r.2) :=
          CaseC.expected_recorded _ _
            (fun r => (livePotential S θ) budget (c + 1) (ghostWorld budget (.inr x) g st.2 r.1) r.2)
        _ ≤ _ := ?_
      cases hx : lz.2 x with
      | some a0 =>
          rw [CaseC.lazy_world_cached x lz a0 hx, expectedValue_pure]
          have hnb : ¬Birth budget x st.2 := fun h => by
            have h2 := h.2.1
            rw [← hlz, hx] at h2
            cases h2
          have hcb : (birthCharge (Sig := Sig) S θ) budget (.inl (.inr x)) st = 0 := by simp [birthCharge, hnb]
          simp only [ghostWorld, hnb, if_false, hcb, add_zero]
          exact (livePotential_count_anti S θ) budget (Nat.le_succ _) g _
      | none =>
          rw [CaseC.lazy_world_fresh x lz hx]
          by_cases hbirth : Birth budget x st.2
          · have hcb : (birthCharge (Sig := Sig) S θ) budget (.inl (.inr x)) st = (θ + S.admBound) / 2 ^ 128 := by
              simp [birthCharge, hbirth]
            rw [hcb]
            have hlt : c < budget := hbirth.2.2
            have hnot : ¬budget < c + 1 := by omega
            have hnot0 : ¬budget < c := by omega
            simp only [ghostWorld, hbirth, if_true]
            by_cases hd : g.dead = true
            · simp only [livePotential, hd, true_or, if_true, expectedValue_const (by simp : Pr[⊥ |
                ($ᵗ HashOutput : ProbComp HashOutput)] = 0), zero_le]
            have hd' : g.dead = false := by simpa using hd
            by_cases hr : g.reused = true
            · have hpt : (potential S θ) budget st = 1 + S.reusePotential lz :=
                (livePotential_reused S θ) budget c g lz hd' hnot0 hr
              rw [hpt]
              calc
                _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
                    (fun a => 1 + S.reusePotential lz + S.admInd a / 2 ^ 128) := by
                  apply expectedValue_mono
                  intro a
                  rw [(livePotential_reused S θ) budget (c + 1) { g with targets := g.targets ++ [a] } _ hd' hnot hr,
                    add_assoc]
                  exact add_le_add le_rfl (S.reusePotential_public_le lz x a hx)
                _ = 1 + S.reusePotential lz +
                    expectedValue ($ᵗ HashOutput : ProbComp HashOutput) S.admInd / 2 ^ 128 := by
                  rw [expectedValue_add, expectedValue_const (by simp)]
                  congr 1
                  simp only [div_eq_mul_inv]
                  rw [expectedValue_mul_const]
                _ ≤ 1 + S.reusePotential lz + S.admBound / 2 ^ 128 :=
                  add_le_add le_rfl (ENNReal.div_le_div_right S.expected_admInd_tight _)
                _ ≤ _ := by
                  apply add_le_add le_rfl
                  apply ENNReal.div_le_div_right
                  exact le_add_self
            · have hr' : g.reused = false := by simpa using hr
              have hpt : (potential S θ) budget st = S.bankValue g + S.reusePotential lz + (excessTerm S θ) budget c g :=
                (livePotential_alive S θ) budget c g lz hd' hnot0 hr'
              rw [hpt]
              set R := S.horizon - g.exposures.length
              have hfa : expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
                  (fun a => S.forecast R g.exposures a) ≤ (θ + (excessForecast S θ) R g.exposures) / 2 ^ 128 := by
                rw [BPORS.expected_uniform_eq_finiteAverage]
                exact (average_forecast_le S θ) R g.exposures
              calc
                _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun a =>
                    S.bankValue g + S.forecast R g.exposures a + (S.reusePotential lz + S.admInd a / 2 ^ 128) +
                      (excessTerm S θ) budget (c + 1) g) := by
                  apply expectedValue_mono
                  intro a
                  rw [(livePotential_alive S θ) budget (c + 1) { g with targets := g.targets ++ [a] } _ hd' hnot hr',
                    S.bankValue_birth]
                  exact add_le_add (add_le_add le_rfl (S.reusePotential_public_le lz x a hx)) le_rfl
                _ = S.bankValue g + expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
                      (fun a => S.forecast R g.exposures a) +
                    (S.reusePotential lz + expectedValue ($ᵗ HashOutput : ProbComp HashOutput) S.admInd / 2 ^ 128) +
                    (excessTerm S θ) budget (c + 1) g := by
                  simp only [expectedValue_add, expectedValue_const (by simp : Pr[⊥ |
                    ($ᵗ HashOutput : ProbComp HashOutput)] = 0), div_eq_mul_inv, expectedValue_mul_const]
                _ ≤ S.bankValue g + (θ + (excessForecast S θ) R g.exposures) / 2 ^ 128 +
                    (S.reusePotential lz + S.admBound / 2 ^ 128) + (excessTerm S θ) budget (c + 1) g := by
                  gcongr
                  exact S.expected_admInd_tight
                _ = S.bankValue g + S.reusePotential lz +
                    ((excessTerm S θ) budget (c + 1) g + (excessForecast S θ) R g.exposures / 2 ^ 128) +
                    (θ + S.admBound) / 2 ^ 128 := by
                  rw [ENNReal.add_div, ENNReal.add_div]
                  ring
                _ = _ := by rw [← (excessTerm_succ S θ) budget c g hlt]
          · have hcb : (birthCharge (Sig := Sig) S θ) budget (.inl (.inr x)) st = 0 := by simp [birthCharge, hbirth]
            simp only [ghostWorld, hbirth, if_false, hcb, add_zero]
            apply expectedValue_le_of_le
            intro a
            by_cases hlt : c < budget
            · have hnd : ¬IsDigestInput x := fun hd => hbirth ⟨hd, by rw [← hlz]; exact hx, hlt⟩
              calc
                _ ≤ (livePotential S θ) budget (c + 1) g lz :=
                  (livePotential_reuse_mono S θ) budget (c + 1) g (S.reusePotential_public_nondigest lz x a hx hnd)
                _ ≤ (livePotential S θ) budget c g lz := (livePotential_count_anti S θ) budget (Nat.le_succ _) g lz
                _ = _ := rfl
            · have hover : budget < c + 1 := by omega
              simp [livePotential, hover]
theorem sign_step (hNotDigest : PayNotDigest pay) (hAvoids : PayAvoids pay) (published : T3.Cache) (budget : Nat)
    (request : Request) (st : BankState Sig) :
    expectedValue ((S.bankImpl pay published budget (.inr request)).run st) (fun r => (potential S θ) budget r.2) ≤
      (potential S θ) budget st := by
  set g := st.1 with hg
  set c := countOf st.2 with hc
  set lz := lazyOf st.2 with hlz
  have hunfold : expectedValue ((S.bankImpl pay published budget (.inr request)).run st)
      (fun r => (potential S θ) budget r.2) =
      expectedValue (QueryRecorded.run (S.authenticatedRecord pay published request) st.2)
        (fun r => (potential S θ) budget (S.ghostSign published request st.1 st.2 (r.1, lazyOf r.2), r.2)) := by
    change expectedValue (PMF.map _ (liftM _)) _ = _
    rw [CaseC.expectedValue_pmf_map, CaseC.expectedValue_liftM]
  rw [hunfold]
  calc
    _ ≤ expectedValue (QueryRecorded.run (S.authenticatedRecord pay published request) st.2)
        (fun r => (livePotential S θ) budget c (S.ghostSign published request g st.2 (r.1, lazyOf r.2)) (lazyOf r.2)) := by
      apply expectedValue_mono_of_support
      intro r hr
      change (livePotential S θ) budget (countOf r.2) (S.ghostSign published request st.1 st.2 (r.1, lazyOf r.2))
        (lazyOf r.2) ≤ _
      exact (livePotential_count_anti S θ) budget (CaseC.recorded_count_le _ _ r hr) _ _
    _ = expectedValue (LazyPrivate.run (S.authenticatedRecord pay published request) lz)
        (fun r => (livePotential S θ) budget c (S.ghostSign published request g st.2 r) r.2) :=
      CaseC.expected_recorded _ _ (fun r => (livePotential S θ) budget c (S.ghostSign published request g st.2 r) r.2)
    _ ≤ (potential S θ) budget st := ?_
  change _ ≤ (livePotential S θ) budget c g lz
  by_cases hfresh : FreshSigning published request st.2
  swap
  ·
    apply expectedValue_le_of_support
    intro r hr
    simp only [FtsBankSpec.ghostSign, hfresh, if_false, livePotential_log]
    apply (livePotential_reuse_mono S θ)
    apply S.reusePotential_sign_stale_le lz r.2 request.message
    · intro hcached hnone
      apply hcached
      cases hcz : lz.1 (.inr (.inl request.message)) with
      | none => rfl
      | some a =>
          have := (SourceReplay.run_extends _ lz r hr).1 hcz
          rw [hnone] at this
          cases this
    · intro hnone
      have hcp : request.cache ≠ published := fun h => hfresh ⟨h, hnone⟩
      obtain ⟨h1, h2⟩ := S.sign_unpublished pay published request hcp lz r hr
      exact ⟨h1.trans hnone, by rw [h2]⟩
    · exact fun m' hm' => S.sign_other_nonce pay hAvoids published request lz r hr m' hm'
    · exact fun m' hm' => S.sign_other_reuseMass pay hNotDigest published request lz r hr m' hm'
  by_cases hhor : S.horizon ≤ g.exposures.length
  · apply expectedValue_le_of_le
    intro r
    simp [FtsBankSpec.ghostSign, hfresh, hhor, livePotential]
  have hlen : g.exposures.length < S.horizon := by omega
  by_cases hd : g.dead = true
  · apply expectedValue_le_of_le
    intro r
    simp [FtsBankSpec.ghostSign, hfresh, hhor, livePotential, hd]
  have hd' : g.dead = false := by simpa using hd
  by_cases hb : budget < c
  · apply expectedValue_le_of_le
    intro r
    simp [FtsBankSpec.ghostSign, hfresh, hhor, livePotential, hb]
  obtain ⟨m, cache⟩ := request
  obtain ⟨hcache, hnonce⟩ := hfresh
  change cache = published at hcache
  subst hcache
  change lz.1 (.inr (.inl m)) = none at hnonce
  have hsign : ∀ r ∈ support (LazyPrivate.run (S.authenticatedRecord pay cache ⟨m, cache⟩) lz),
      S.reusePotential r.2 + S.reuseMass lz.2 m ≤ S.reusePotential lz := fun r hr =>
    S.reusePotential_sign_le lz r.2 m hnonce (S.sign_published_nonce pay cache m lz r hr)
      (fun m' hm' => S.sign_other_nonce pay hAvoids cache ⟨m, cache⟩ lz r hr m' hm')
      (fun m' hm' => S.sign_other_reuseMass pay hNotDigest cache ⟨m, cache⟩ lz r hr m' hm')
  have hfr : FreshSigning cache ⟨m, cache⟩ st.2 := ⟨rfl, hnonce⟩
  have hdead : ∀ r, (S.ghostSign cache ⟨m, cache⟩ g st.2 r).dead = false := by
    intro r; simp [FtsBankSpec.ghostSign, hfr, hhor, hd']
  have hreu : ∀ r, (S.ghostSign cache ⟨m, cache⟩ g st.2 r).reused =
      (g.reused || decide (S.Reuse (lazyOf st.2).2 (CaseC.nonceOf r.2 m) m)) := by
    intro r; simp [FtsBankSpec.ghostSign, hfr, hhor]
  have hexp : ∀ r, (S.ghostSign cache ⟨m, cache⟩ g st.2 r).exposures = g.exposures ++ r.1.2.toList := by
    intro r; simp [FtsBankSpec.ghostSign, hfr, hhor]
  have htar : ∀ r, (S.ghostSign cache ⟨m, cache⟩ g st.2 r).targets = g.targets := by
    intro r; simp [FtsBankSpec.ghostSign, hfr, hhor]
  by_cases hr : g.reused = true
  · apply expectedValue_le_of_support
    intro r hrs
    rw [(livePotential_reused S θ) budget c (S.ghostSign cache ⟨m, cache⟩ g st.2 r) r.2 (hdead r) hb
        (by rw [hreu r, hr, Bool.true_or]),
      (livePotential_reused S θ) budget c g lz hd' hb hr]
    exact add_le_add le_rfl (le_trans le_self_add (hsign r hrs))
  have hr' : g.reused = false := by simpa using hr
  set P' := S.bankValue g + (excessTerm S θ) budget c g with hP
  let Fmain : (Option Sig × Option HashOutput) × LazyPrivate.State → ENNReal := fun r =>
    if S.Reuse lz.2 (CaseC.nonceOf r.2 m) m then 1 else r.1.2.elim P' ((signWeight S θ) budget c g)
  have hpoint : ∀ r, (livePotential S θ) budget c (S.ghostSign cache ⟨m, cache⟩ g st.2 r) r.2 ≤
      Fmain r + S.reusePotential r.2 := by
    intro r
    by_cases hre : S.Reuse lz.2 (CaseC.nonceOf r.2 m) m
    · have hru : (S.ghostSign cache ⟨m, cache⟩ g st.2 r).reused = true := by
        rw [hreu r, hr', Bool.false_or]
        exact decide_eq_true hre
      rw [(livePotential_reused S θ) budget c _ r.2 (hdead r) hb hru]
      simp only [Fmain, hre, if_true, le_refl]
    · have hru : (S.ghostSign cache ⟨m, cache⟩ g st.2 r).reused = false := by
        rw [hreu r, hr', Bool.false_or]
        exact decide_eq_false hre
      rw [(livePotential_alive S θ) budget c _ r.2 (hdead r) hb hru]
      simp only [Fmain, hre, if_false]
      have hbv : S.bankValue (S.ghostSign cache ⟨m, cache⟩ g st.2 r) =
          S.bankValue { g with exposures := g.exposures ++ r.1.2.toList } := by
        unfold FtsBankSpec.bankValue; rw [htar r, hexp r]
      have het : (excessTerm S θ) budget c (S.ghostSign cache ⟨m, cache⟩ g st.2 r) =
          (excessTerm S θ) budget c { g with exposures := g.exposures ++ r.1.2.toList } := by
        unfold excessTerm; rw [hexp r]
      rw [hbv, het]
      cases hsel : r.1.2 with
      | none =>
          simp only [Option.toList_none, List.append_nil, Option.elim_none, hP]
          apply le_of_eq
          ring
      | some A =>
          simp only [Option.toList_some, Option.elim_some, signWeight]
          apply le_of_eq
          ring
  calc
    _ ≤ expectedValue (LazyPrivate.run (S.authenticatedRecord pay cache ⟨m, cache⟩) lz)
        (fun r => Fmain r + S.reusePotential r.2) := expectedValue_mono _ hpoint
    _ = expectedValue (LazyPrivate.run (S.authenticatedRecord pay cache ⟨m, cache⟩) lz) Fmain +
        expectedValue (LazyPrivate.run (S.authenticatedRecord pay cache ⟨m, cache⟩) lz)
          (fun r => S.reusePotential r.2) := expectedValue_add _ _ _
    _ ≤ (P' + S.reuseMass lz.2 m) +
        expectedValue (LazyPrivate.run (S.authenticatedRecord pay cache ⟨m, cache⟩) lz)
          (fun r => S.reusePotential r.2) := by
      apply add_le_add _ le_rfl
      apply S.fresh_signing_kernel pay cache m lz hnonce Fmain ((signWeight S θ) budget c g) P'
        (le_of_eq ((freshPrice_signWeight S θ) budget c g hlen))
      intro r _
      exact le_rfl
    _ = P' + (expectedValue (LazyPrivate.run (S.authenticatedRecord pay cache ⟨m, cache⟩) lz)
          (fun r => S.reusePotential r.2 + S.reuseMass lz.2 m)) := by
      rw [expectedValue_add, expectedValue_const (by simp)]
      ring
    _ ≤ P' + S.reusePotential lz := add_le_add le_rfl (expectedValue_le_of_support hsign)
    _ = (livePotential S θ) budget c g lz := by
      rw [(livePotential_alive S θ) budget c g lz hd' hb hr', hP]
      ring
theorem potential_step (hNotDigest : PayNotDigest pay) (hAvoids : PayAvoids pay) (published : T3.Cache)
    (budget : Nat) (input : (Interaction' Sig).Domain) (st : BankState Sig) :
    expectedValue ((S.bankImpl pay published budget input).run st) (fun r => (potential S θ) budget r.2) ≤
      (potential S θ) budget st + (birthCharge S θ) budget input st := by
  cases input with
  | inl input => exact (world_step S θ) pay published budget input st
  | inr request => exact ((sign_step S θ) pay hNotDigest hAvoids published budget request st).trans le_self_add
theorem potential_run {α : Type} (hNotDigest : PayNotDigest pay) (hAvoids : PayAvoids pay) (published : T3.Cache)
    (budget : Nat) (program : OracleComp (Interaction' Sig) α) (st : BankState Sig) :
    expectedValue ((simulateQ (S.bankImpl pay published budget) program).run st)
        (fun r => (potential S θ) budget r.2) ≤
      (potential S θ) budget st + BPORS.Adaptive.Creation.expectedCharges (S.bankImpl pay published budget)
        ((birthCharge S θ) budget) program st := by
  induction program using OracleComp.inductionOn generalizing st with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, BPORS.Adaptive.Creation.expectedCharges_pure, add_zero]
      rw [expectedValue_pure]
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, expectedValue_bind,
        BPORS.Adaptive.Creation.expectedCharges_query_bind]
      calc
        _ ≤ expectedValue ((S.bankImpl pay published budget input).run st) (fun result =>
            (potential S θ) budget result.2 + BPORS.Adaptive.Creation.expectedCharges (S.bankImpl pay published budget)
              ((birthCharge S θ) budget) (next result.1) result.2) :=
          expectedValue_mono _ fun result => ih result.1 result.2
        _ = expectedValue ((S.bankImpl pay published budget input).run st)
              (fun result => (potential S θ) budget result.2) +
            expectedValue ((S.bankImpl pay published budget input).run st) (fun result =>
              BPORS.Adaptive.Creation.expectedCharges (S.bankImpl pay published budget)
                ((birthCharge S θ) budget) (next result.1) result.2) := expectedValue_add _ _ _
        _ ≤ ((potential S θ) budget st + (birthCharge S θ) budget input st) + _ :=
          add_le_add ((potential_step S θ) pay hNotDigest hAvoids published budget input st) le_rfl
        _ = _ := by ring
theorem bank_charges_eq_births {α : Type} (published : T3.Cache) (budget : Nat)
    (program : OracleComp (Interaction' Sig) α) (s : QueryRecorded.State) (g : Ghost Sig) :
    BPORS.Adaptive.Creation.expectedCharges (S.bankImpl pay published budget) ((birthCharge S θ) budget) program (g, s) =
      (θ + S.admBound) / 2 ^ 128 * BPORS.Adaptive.Creation.expectedCharges (S.recordedImpl pay published)
        (birthWeight budget) program s := by
  have h1 : BPORS.Adaptive.Creation.expectedCharges (S.bankImpl pay published budget) ((birthCharge S θ) budget)
      program (g, s) =
      BPORS.Adaptive.Creation.expectedCharges (S.bankImpl pay published budget)
        (fun input st => (θ + S.admBound) / 2 ^ 128 * birthWeight budget input st.2) program (g, s) := by
    congr 1
    funext input st
    exact (birthCharge_eq S θ) budget input st
  rw [h1, BPORS.Adaptive.Creation.expectedCharges_scale]
  congr 1
  exact BPORS.Adaptive.Creation.expectedCharges_project (S.bankImpl pay published budget)
    (S.recordedImpl pay published) Prod.snd
    (fun input st => S.bank_query_project pay published budget input st)
    (birthWeight budget) program (g, s)
theorem potential_win (budget : Nat) (st : BankState Sig) (halive : st.1.dead = false)
    (hcount : countOf st.2 ≤ budget)
    (h : st.1.reused = true ∨ ∃ N ∈ st.1.targets, S.admissible N = true ∧ S.covered st.1.exposures N) :
    1 ≤ (potential S θ) budget st := by
  have hnot : ¬budget < countOf st.2 := by omega
  unfold potential
  by_cases hr : st.1.reused = true
  · rw [(livePotential_reused S θ) budget _ st.1 _ halive hnot hr]
    exact le_add_right le_rfl
  · have hr' : st.1.reused = false := by simpa using hr
    obtain ⟨N, hN, hadm, hcov⟩ := h.resolve_left hr
    rw [(livePotential_alive S θ) budget _ st.1 _ halive hnot hr']
    calc
      (1 : ENNReal) ≤ S.score st.1.exposures N := S.one_le_score _ N hadm hcov
      _ ≤ S.forecast (S.horizon - st.1.exposures.length) st.1.exposures N := S.score_le_forecast _ _ _
      _ ≤ S.bankValue st.1 := List.le_sum_of_mem (List.mem_map_of_mem hN)
      _ ≤ _ := le_self_add.trans le_self_add
theorem bank_potential_le_rate (hNotDigest : PayNotDigest pay) (hAvoids : PayAvoids pay)
    (rest : Digest → T3.Cache → OracleComp (Interaction' Sig) Bool) (budget : Nat) (rate : ENNReal)
    (hrate : ClaudeWCT.Numerics.Law.lawAvg S.law S.horizon (fun W : List P => S.price W - θ) ≤ rate) :
    expectedValue (S.bankExperiment pay rest budget) (fun r => (potential S θ) budget r.2) ≤
      (θ + S.admBound) / 2 ^ 128 * S.expectedBirths pay rest budget +
        (budget : ENNReal) * rate / 2 ^ 128 := by
  unfold FtsBankSpecL.bankExperiment
  rw [expectedValue_bind]
  calc
    _ ≤ expectedValue (liftM (QueryRecorded.run keygen QueryRecorded.initial) : PMF _) (fun generated =>
        (budget : ENNReal) * rate / 2 ^ 128 +
          (θ + S.admBound) / 2 ^ 128 * BPORS.Adaptive.Creation.expectedCharges (S.recordedImpl pay generated.1.2)
            (birthWeight budget) (rest generated.1.1 generated.1.2) generated.2) := by
      apply CaseC.pmf_expectedValue_mono
      intro generated hg
      rw [MonitoredPrivate.pmf_support] at hg
      refine ((potential_run S θ) pay hNotDigest hAvoids generated.1.2 budget _ _).trans ?_
      rw [(bank_charges_eq_births S θ) pay generated.1.2 budget]
      exact add_le_add ((potential_initial_le_rate S θ) budget rate hrate generated hg) le_rfl
    _ = _ := by
      rw [expectedValue_add, expectedValue_const (by simp), CaseC.pmf_expectedValue_left_mul]
      unfold FtsBankSpecL.expectedBirths
      ring
theorem bank_event_le_rate (hNotDigest : PayNotDigest pay) (hAvoids : PayAvoids pay)
    (rest : Digest → T3.Cache → OracleComp (Interaction' Sig) Bool) (budget : Nat) (rate : ENNReal)
    (hrate : ClaudeWCT.Numerics.Law.lawAvg S.law S.horizon (fun W : List P => S.price W - θ) ≤ rate)
    (weight : Bool × QueryRecorded.State → ENNReal) (hle : ∀ y, weight y ≤ 1)
    (hwin : ∀ b ∈ (S.bankExperiment pay rest budget).support, weight (b.1, b.2.2) ≠ 0 → 1 ≤ (potential S θ) budget b.2) :
    expectedValue (S.recordedExperiment pay rest) weight ≤
      (θ + S.admBound) / 2 ^ 128 * S.expectedBirths pay rest budget +
        (budget : ENNReal) * rate / 2 ^ 128 := by
  rw [← S.bank_experiment_project pay rest budget, PMF.monad_map_eq_map, CaseC.expectedValue_pmf_map]
  refine le_trans ?_ ((bank_potential_le_rate S θ) pay hNotDigest hAvoids rest budget rate hrate)
  apply CaseC.pmf_expectedValue_mono
  intro b hb
  by_cases h0 : weight (b.1, b.2.2) = 0
  · rw [h0]; exact bot_le
  · exact (hle _).trans (hwin b hb h0)

end ClaudeWCT.Bank.FlexibleGame

namespace ClaudeWCT.Bank.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.Research
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

noncomputable def flexiblePotential (θ : ENNReal) (budget : Nat)
    (state : BankState SharedForest.Signature) : ENNReal :=
  FlexibleGame.potential bankSpec θ budget state

theorem flexible_event_le (θ rate : ENNReal)
    (hexc : ClaudeWCT.Numerics.Law.lawAvg honestLaw (2^32) (fun W => price W-θ)≤rate)
    (rest : Digest → T3.Cache → OracleComp (Interaction' SharedForest.Signature) Bool)
    (budget : Nat) (weight : Bool × QueryRecorded.State → ENNReal)
    (hw : ∀ y,weight y≤1)
    (hwin : ∀ b∈(bankSpec.bankExperiment payAfterDigest rest budget).support,
      weight (b.1,b.2.2)≠0 → 1≤flexiblePotential θ budget b.2) :
    expectedValue (bankSpec.recordedExperiment payAfterDigest rest) weight ≤
      (θ+1/1024)/2^128*bankSpec.expectedBirths payAfterDigest rest budget+
      (budget:ENNReal)*rate/2^128 :=
  FlexibleGame.bank_event_le_rate bankSpec θ payAfterDigest payNotDigest payAvoids
    rest budget rate hexc weight hw hwin

theorem flexible_potential_win (θ : ENNReal) (budget : Nat) (state : BankState SharedForest.Signature)
    (halive : state.1.dead=false) (hcount : CaseC.countOf state.2≤budget)
    (h : state.1.reused=true ∨ ∃ N∈state.1.targets,admissible N=true ∧ Covered state.1.exposures N) :
    1≤flexiblePotential θ budget state :=
  FlexibleGame.potential_win bankSpec θ budget state halive hcount h

theorem bankInv_experiment
    (rest : Digest → T3.Cache → OracleComp (Interaction' SharedForest.Signature) Bool)
    (budget : Nat) (b : Bool × BankState SharedForest.Signature)
    (hb : b∈(bankSpec.bankExperiment payAfterDigest rest budget).support) :
    ∃ generated∈support (QueryRecorded.run keygen QueryRecorded.initial),
      bankSpec.BankInv payAfterDigest SharedForest.Signature.rho generated.1.2 budget
        generated.2.events b.2 :=
  bankSpec.bankInv_experiment payAfterDigest SharedForest.Signature.rho payHashOnly payRho payAvoids
    rest budget b hb

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.NearMemory
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.CaseC (BankCore BankCore.expose expectedValue_add_const_le DigestRowOf
  digestRowOf_unique tsum_indicator_le_of_subsingleton)
open SphincsSecurity.Completeness (searchLoop)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpec P)
noncomputable abbrev nearPotential : BankCore → ENNReal := Flexible.corePotential S 0 (2^32)
theorem near_birth (b : BankCore) (s : Nat) (hs : b.slack=s+1) (C' : HashOutput → ENNReal)
    (hC : ∀ N,C' N≤b.reuse+S.admInd N/2^128) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun N => nearPotential S {b with targets:=b.targets++[N],slack:=s,reuse:=C' N}) ≤
      nearPotential S b+S.admBound/2^128 := by
  simpa only [zero_add] using Flexible.core_birth S 0 (2^32) b s hs C' hC

theorem near_sign (b : BankCore) (cache : Sampling.RCache) (m : Message) (C' : ENNReal)
    (hC : C'+S.reuseMass cache m≤b.reuse) (secret : BitVec 256) (fuel : Nat) (hfuel : fuel≤2^32) :
    expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho =>
      if S.Reuse cache rho m then nearPotential S {b with reused:=true,reuse:=C'}
      else expectedValue (Sampling.roRun secret (S.search rho m 0 fuel) cache)
        (fun r => nearPotential S (b.expose C' (r.1.map Prod.snd)))) ≤ nearPotential S b :=
  Flexible.core_sign S 0 (2^32) b cache m C' hC secret fuel hfuel

theorem near_win (b : BankCore) (halive : ¬(2^32)<b.exposures.length)
    (h : b.reused=true ∨ ∃ N∈b.targets,S.admissible N=true ∧ S.covered b.exposures N) :
    1≤nearPotential S b := Flexible.core_win S 0 (2^32) b halive h

theorem near_initial (rate : ENNReal)
    (hrate : ClaudeWCT.Numerics.Law.lawAvg S.law (2^32) S.price≤rate) (q : Nat) :
    nearPotential S ⟨[],[],false,0,q⟩≤(q:ENNReal)*rate/2^128 := by
  apply Flexible.core_initial S 0 rate
  simpa only [tsub_zero] using hrate
noncomputable def reuseC (rows : Sampling.RCache) (nonces : Message → Option Digest) : ENNReal :=
  ∑' m : Message, if nonces m = none then S.reuseMass rows m else 0
theorem reuseC_birth_le (rows : Sampling.RCache) (nonces : Message → Option Digest) (x : HashInput) (a : HashOutput)
    (hx : rows x = none) : (reuseC S) (rows.cacheQuery x a) nonces ≤ (reuseC S) rows nonces + S.admInd a / 2 ^ 128 := by
  unfold reuseC
  calc
    (∑' m : Message, if nonces m = none then S.reuseMass (rows.cacheQuery x a) m else 0) ≤
        ∑' m : Message, ((if nonces m = none then S.reuseMass rows m else 0) +
          (if DigestRowOf x m then S.admInd a / 2 ^ 128 else 0)) := by
      apply ENNReal.tsum_le_tsum
      intro m
      split_ifs with h1 h2
      · simpa [ENNReal.div_eq_inv_mul, h2] using S.reuseMass_cacheQuery_le rows x a hx m
      · simpa [h2] using S.reuseMass_cacheQuery_le rows x a hx m
      · exact bot_le
      · exact bot_le
    _ = _ + _ := ENNReal.tsum_add
    _ ≤ _ := add_le_add le_rfl (tsum_indicator_le_of_subsingleton _ (fun _ _ h h' => digestRowOf_unique h h') _)
theorem reuseC_sign_le (rows rows' : Sampling.RCache) (nonces : Message → Option Digest) (m : Message) (v : Digest)
    (hm : nonces m = none) (hrows : ∀ m', m' ≠ m → S.reuseMass rows' m' = S.reuseMass rows m') :
    (reuseC S) rows' (Function.update nonces m (some v)) + S.reuseMass rows m ≤ (reuseC S) rows nonces := by
  unfold reuseC
  rw [ENNReal.tsum_eq_add_tsum_ite m, ENNReal.tsum_eq_add_tsum_ite m (f := fun m' =>
    if nonces m' = none then S.reuseMass rows m' else 0)]
  simp only [Function.update_self, reduceCtorEq, if_false, zero_add, hm, if_true]
  rw [add_comm]
  apply add_le_add le_rfl
  apply le_of_eq
  apply tsum_congr
  intro m'
  by_cases he : m' = m
  · simp [he]
  · simp only [he, if_false, Function.update_of_ne he, hrows m' he]
theorem reuseC_signed_eq (rows rows' : Sampling.RCache) (nonces : Message → Option Digest) (m : Message)
    (hm : nonces m ≠ none) (hrows : ∀ m', m' ≠ m → S.reuseMass rows' m' = S.reuseMass rows m') :
    (reuseC S) rows' nonces = (reuseC S) rows nonces := by
  unfold reuseC
  apply tsum_congr
  intro m'
  by_cases he : m' = m
  · subst he; simp [hm]
  · simp only [hrows m' he]
theorem search_cache_frame {β γ : Type} (secret : BitVec 256) (inputs : Nat → HashInput)
    (decoder : HashOutput → Option β) (result : Nat → β → γ) :
    ∀ fuel counter (cache : Sampling.RCache) r,
      r ∈ support (Sampling.roRun secret
        (Sampling.publicProgram (searchLoop inputs decoder (fun c v => pure (result c v)) fuel counter)) cache) →
      ∀ y, (∀ k, y ≠ inputs k) → r.2 y = cache y := by
  intro fuel
  induction fuel with
  | zero =>
      intro counter cache r hr y _
      simp only [searchLoop, Sampling.publicProgram, simulateQ_pure] at hr
      change r ∈ support (Sampling.roRun secret (pure none) cache) at hr
      rw [Sampling.roRun_pure, support_pure, Set.mem_singleton_iff] at hr
      rw [hr]
  | succ fuel ih =>
      intro counter cache r hr y hy
      rw [Sampling.publicSearch_succ, Sampling.roRun_bind, Sampling.roRun_publicQuery, mem_support_bind_iff] at hr
      obtain ⟨first, hfirst, hr⟩ := hr
      have hfc : first.2 y = cache y := by
        rw [randomOracle.run_eq] at hfirst
        cases hc : cache (inputs counter) with
        | some a =>
            rw [hc, support_pure, Set.mem_singleton_iff] at hfirst
            rw [hfirst]
        | none =>
            rw [hc, mem_support_bind_iff] at hfirst
            obtain ⟨a, -, hfa⟩ := hfirst
            rw [support_pure, Set.mem_singleton_iff] at hfa
            rw [hfa]
            exact QueryCache.cacheQuery_of_ne cache a (hy counter)
      cases hd : decoder first.1 with
      | none =>
          rw [hd] at hr
          exact (ih (counter + 1) first.2 r hr y hy).trans hfc
      | some value =>
          rw [hd] at hr
          change r ∈ support (Sampling.roRun secret (pure _) first.2) at hr
          rw [Sampling.roRun_pure, support_pure, Set.mem_singleton_iff] at hr
          rw [hr]
          exact hfc
theorem digestSearch_cache_frame (secret : BitVec 256) (rho : Digest) (m : Message) (fuel : Nat)
    (cache : Sampling.RCache) (r) (hr : r ∈ support (Sampling.roRun secret (S.search rho m 0 fuel) cache)) :
    ∀ y, (∀ k, y ≠ Sampling.digestTrial rho m k) → r.2 y = cache y := by
  unfold ClaudeWCT.Bank.FtsBankSpec.search at hr
  exact search_cache_frame secret (Sampling.digestTrial rho m) S.decode _ fuel 0 cache r hr
theorem digestTrial_ne_of_message {rho rho' : Digest} {m m' : Message} (hm : m' ≠ m) (c c' : Nat)
    (hc' : c' < 2 ^ 32) : Sampling.digestTrial rho' m' c' ≠ Sampling.digestTrial rho m c := by
  intro he
  have h1 : DigestRowOf (Sampling.digestTrial rho' m' c') m' := ⟨(rho', ⟨c', hc'⟩), rfl⟩
  have h2 : DigestRowOf (Sampling.digestTrial rho m (c % 2 ^ 32)) m :=
    ⟨(rho, ⟨c % 2 ^ 32, Nat.mod_lt _ (by decide)⟩), rfl⟩
  have h3 : Sampling.digestTrial rho m (c % 2 ^ 32) = Sampling.digestTrial rho m c := by
    unfold Sampling.digestTrial
    congr 2
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofNat]
  rw [h3, ← he] at h2
  exact hm (digestRowOf_unique h1 h2)
theorem digestSearch_reuseMass (secret : BitVec 256) (rho : Digest) (m : Message) (fuel : Nat)
    (cache : Sampling.RCache) (r) (hr : r ∈ support (Sampling.roRun secret (S.search rho m 0 fuel) cache)) :
    ∀ m', m' ≠ m → S.reuseMass r.2 m' = S.reuseMass cache m' := by
  intro m' hm
  unfold ClaudeWCT.Bank.FtsBankSpec.reuseMass ClaudeWCT.Bank.FtsBankSpec.admissibleEntry
  congr 1
  apply tsum_congr
  intro p
  rw [(digestSearch_cache_frame S) secret rho m fuel cache r hr _
    (fun k => digestTrial_ne_of_message hm k p.2.val p.2.isLt)]
noncomputable def nearMemPotential (q : Nat) (births exposures : List HashOutput) (reused : Bool)
    (rows : Sampling.RCache) (nonces : Message → Option Digest) : ENNReal :=
  if q < births.length then 0
  else (nearPotential S) ⟨births, exposures, reused, (reuseC S) rows nonces, q - births.length⟩ +
    ((q - births.length : Nat) : ENNReal) * (S.admBound / 2 ^ 128)
theorem mem_birth (q : Nat) (births exposures : List HashOutput) (reused : Bool) (rows : Sampling.RCache)
    (nonces : Message → Option Digest) (x : HashInput) (hx : rows x = none) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
        (fun a : HashOutput => (nearMemPotential S) q (births ++ [a]) exposures reused (rows.cacheQuery x a) nonces) ≤
      (nearMemPotential S) q births exposures reused rows nonces := by
  by_cases hq : births.length < q
  · obtain ⟨s, hs⟩ : ∃ s, q - births.length = s + 1 := ⟨q - births.length - 1, by omega⟩
    have hb : (nearMemPotential S) q births exposures reused rows nonces =
        (nearPotential S) ⟨births, exposures, reused, (reuseC S) rows nonces, s + 1⟩ + ((s + 1 : Nat) : ENNReal) *
          (S.admBound / 2 ^ 128) := by
      unfold nearMemPotential
      rw [if_neg (by omega), hs]
    have ha : ∀ a : HashOutput, (nearMemPotential S) q (births ++ [a]) exposures reused (rows.cacheQuery x a) nonces =
        (nearPotential S) { (⟨births, exposures, reused, (reuseC S) rows nonces, s + 1⟩ : BankCore) with
          targets := births ++ [a], slack := s, reuse := (reuseC S) (rows.cacheQuery x a) nonces } +
          (s : ENNReal) * (S.admBound / 2 ^ 128) := by
      intro a
      unfold nearMemPotential
      have hl : (births ++ [a]).length = births.length + 1 := by simp
      rw [if_neg (by omega), show q - (births ++ [a]).length = s by omega]
    simp_rw [ha]
    rw [hb]
    calc
      _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun a =>
            (nearPotential S) { (⟨births, exposures, reused, (reuseC S) rows nonces, s + 1⟩ : BankCore) with
              targets := births ++ [a], slack := s, reuse := (reuseC S) (rows.cacheQuery x a) nonces }) +
          (s : ENNReal) * (S.admBound / 2 ^ 128) := expectedValue_add_const_le _ _ _
      _ ≤ ((nearPotential S) ⟨births, exposures, reused, (reuseC S) rows nonces, s + 1⟩ + S.admBound / 2 ^ 128) +
          (s : ENNReal) * (S.admBound / 2 ^ 128) := by
        apply add_le_add _ le_rfl
        exact (near_birth S) ⟨births, exposures, reused, (reuseC S) rows nonces, s + 1⟩ s rfl _
          (fun a => (reuseC_birth_le S) rows nonces x a hx)
      _ = _ := by
        push_cast
        ring
  · apply expectedValue_le_of_le
    intro a
    unfold nearMemPotential
    rw [if_pos (by simp; omega)]
    exact bot_le
theorem mem_sign_fresh (q : Nat) (births exposures : List HashOutput) (reused : Bool) (rows : Sampling.RCache)
    (nonces : Message → Option Digest) (m : Message) (hm : nonces m = none) (secret : BitVec 256) (fuel : Nat)
    (hfuel : fuel ≤ 2 ^ 32) :
    expectedValue ($ᵗ Digest : ProbComp Digest) (fun v =>
      expectedValue (Sampling.roRun secret (S.search v m 0 fuel) rows) (fun r =>
        (nearMemPotential S) q births (exposures ++ (r.1.map Prod.snd).toList)
          (reused || decide (S.Reuse rows v m)) r.2 (Function.update nonces m (some v)))) ≤
      (nearMemPotential S) q births exposures reused rows nonces := by
  by_cases hq : q < births.length
  · apply expectedValue_le_of_le
    intro v
    apply expectedValue_le_of_le
    intro r
    unfold nearMemPotential
    rw [if_pos hq]
    exact bot_le
  push Not at hq
  set C0 := (reuseC S) rows (Function.update nonces m (some 0)) with hC0
  have hupd : ∀ v : Digest, (reuseC S) rows (Function.update nonces m (some v)) = C0 := by
    intro v
    unfold reuseC
    apply tsum_congr
    intro m'
    by_cases he : m' = m
    · subst he; simp
    · simp only [Function.update_of_ne he]
  have hafter : ∀ v r, r ∈ support (Sampling.roRun secret (S.search v m 0 fuel) rows) →
      (reuseC S) r.2 (Function.update nonces m (some v)) = C0 := by
    intro v r hr
    rw [(reuseC_signed_eq S) rows r.2 _ m (by simp) ((digestSearch_reuseMass S) secret v m fuel rows r hr), hupd]
  have hC : C0 + S.reuseMass rows m ≤ (reuseC S) rows nonces := by
    rw [← hupd 0]
    exact (reuseC_sign_le S) rows rows nonces m 0 hm (fun _ _ => rfl)
  set b : BankCore := ⟨births, exposures, reused, (reuseC S) rows nonces, q - births.length⟩ with hb
  set extra : ENNReal := ((q - births.length : Nat) : ENNReal) * (S.admBound / 2 ^ 128) with hextra
  have hbefore : (nearMemPotential S) q births exposures reused rows nonces = (nearPotential S) b + extra := by
    unfold nearMemPotential
    rw [if_neg (by omega)]
  have hpoint : ∀ v r, r ∈ support (Sampling.roRun secret (S.search v m 0 fuel) rows) →
      (nearMemPotential S) q births (exposures ++ (r.1.map Prod.snd).toList)
          (reused || decide (S.Reuse rows v m)) r.2 (Function.update nonces m (some v)) =
        (nearPotential S) ⟨births, exposures ++ (r.1.map Prod.snd).toList,
          reused || decide (S.Reuse rows v m), C0, q - births.length⟩ + extra := by
    intro v r hr
    unfold nearMemPotential
    rw [if_neg (by omega), hafter v r hr]
  have hreuse : ∀ (o : Option HashOutput), (nearPotential S) ⟨births, exposures ++ o.toList, true, C0,
      q - births.length⟩ ≤ (nearPotential S) { b with reused := true, reuse := C0 } := by
    intro o
    have hl : exposures.length ≤ (exposures ++ o.toList).length := by simp
    unfold nearPotential Flexible.corePotential
    rw [hb]
    simp only [if_true]
    by_cases h2 : (2^32) < exposures.length
    · rw [if_pos (lt_of_lt_of_le h2 hl)]; exact bot_le
    · by_cases h1 : (2^32) < (exposures ++ o.toList).length
      · rw [if_pos h1]; exact bot_le
      · rw [if_neg h1, if_neg h2]
  rw [hbefore]
  calc
    _ ≤ expectedValue ($ᵗ Digest : ProbComp Digest) (fun v =>
        (if S.Reuse rows v m then (nearPotential S) { b with reused := true, reuse := C0 }
          else expectedValue (Sampling.roRun secret (S.search v m 0 fuel) rows)
            (fun r => (nearPotential S) (b.expose C0 (r.1.map Prod.snd)))) + extra) := by
      apply expectedValue_mono
      intro v
      calc
        _ ≤ expectedValue (Sampling.roRun secret (S.search v m 0 fuel) rows) (fun r =>
            (if S.Reuse rows v m then (nearPotential S) { b with reused := true, reuse := C0 }
              else (nearPotential S) (b.expose C0 (r.1.map Prod.snd))) + extra) := by
          apply expectedValue_mono_of_support
          intro r hr
          rw [hpoint v r hr]
          apply add_le_add _ le_rfl
          by_cases hre : S.Reuse rows v m
          · simp only [hre, decide_true, Bool.or_true, if_true]
            exact hreuse _
          · simp only [hre, decide_false, Bool.or_false, if_false]
            exact le_of_eq rfl
        _ ≤ expectedValue (Sampling.roRun secret (S.search v m 0 fuel) rows) (fun r =>
            (if S.Reuse rows v m then (nearPotential S) { b with reused := true, reuse := C0 }
              else (nearPotential S) (b.expose C0 (r.1.map Prod.snd)))) + extra := expectedValue_add_const_le _ _ _
        _ ≤ _ := by
          apply add_le_add _ le_rfl
          by_cases hre : S.Reuse rows v m
          · simp only [hre, if_true]
            exact expectedValue_le_of_le _ fun _ => le_rfl
          · simp only [hre, if_false]
            exact le_rfl
    _ ≤ expectedValue ($ᵗ Digest : ProbComp Digest) (fun v =>
        (if S.Reuse rows v m then (nearPotential S) { b with reused := true, reuse := C0 }
          else expectedValue (Sampling.roRun secret (S.search v m 0 fuel) rows)
            (fun r => (nearPotential S) (b.expose C0 (r.1.map Prod.snd))))) + extra := expectedValue_add_const_le _ _ _
    _ ≤ _ := add_le_add ((near_sign S) b rows m C0 hC secret fuel hfuel) le_rfl
theorem mem_initial (rate : ENNReal)
    (hrate : ClaudeWCT.Numerics.Law.lawAvg S.law (2^32) S.price≤rate) (q : Nat) :
    (nearMemPotential S) q [] [] false ∅ (fun _ => none) ≤ (q:ENNReal)*(rate+S.admBound)/2^128 := by
  unfold nearMemPotential
  simp only [List.length_nil,Nat.not_lt_zero,if_false,Nat.sub_zero]
  have hC : (reuseC S) ∅ (fun _ => none)=0 := by
    unfold reuseC ClaudeWCT.Bank.FtsBankSpec.reuseMass ClaudeWCT.Bank.FtsBankSpec.admissibleEntry
    simp
  have hn := (near_initial S) rate hrate q
  rw [show (⟨[],[],false,(reuseC S) ∅ (fun _ => none),q⟩:BankCore)=⟨[],[],false,0,q⟩ by rw [hC]]
  calc
    _ ≤ (q:ENNReal)*rate/2^128+(q:ENNReal)*(S.admBound/2^128) := add_le_add hn le_rfl
    _ = _ := by simp only [div_eq_mul_inv];ring
theorem mem_win (q : Nat) (births exposures : List HashOutput) (reused : Bool) (rows : Sampling.RCache)
    (nonces : Message → Option Digest) (hq : births.length ≤ q) (hlen : exposures.length ≤ (2^32))
    (h : reused = true ∨ ∃ N ∈ births, S.admissible N = true ∧ S.covered exposures N) :
    1 ≤ (nearMemPotential S) q births exposures reused rows nonces := by
  unfold nearMemPotential
  rw [if_neg (by omega)]
  exact ((near_win S) ⟨births, exposures, reused, (reuseC S) rows nonces, q - births.length⟩ (by simp only; omega) h).trans
    le_self_add
end ClaudeWCT.Bank.NearMemory

namespace ClaudeWCT.Bank.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.Research
open ClaudeWCT.W9.T3.Security
open SigGolfCandidate.T3.Security.CaseC (Agrees lazyOf countOf IsDigestInput eventPublic)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

theorem bank_alive {published : T3.Cache} {budget : Nat} {kg : List FirstHit.QueryEvent}
    {state : BankState SharedForest.Signature}
    (hinv : bankSpec.BankInv payAfterDigest SharedForest.Signature.rho published budget kg state)
    (hlen : state.1.log.length≤2^32) : state.1.dead=false := by
  cases hd:state.1.dead
  · rfl
  · have h:=hinv.dead hd
    change 2^32<state.1.log.length at h
    omega

theorem loggedOutputs_exposed {published : T3.Cache} {budget : Nat} {kg : List FirstHit.QueryEvent}
    {state : BankState SharedForest.Signature}
    (hinv : bankSpec.BankInv payAfterDigest SharedForest.Signature.rho published budget kg state)
    (halive : state.1.dead=false) (A : Correctness.Answers) (hA : Agrees A (lazyOf state.2)) :
    ∀ out∈WPair.Paired.loggedOutputs A state.1.log,out∈state.1.exposures := by
  intro out ho
  obtain ⟨entry,he,signature,hsig,hs⟩:=WPair.Paired.mem_loggedOutputs.mp ho
  unfold WPair.Paired.signedOutput at hs
  cases hsearch:evalWithAnswerFn A
      (SharedForest.sharedDigestSearch signature.rho entry.1.message 0 ClaudeWCT.WCT9.digestAttemptLimit) with
  | none => rw [hsearch] at hs;cases hs
  | some found =>
      rcases found with ⟨counter,value⟩
      rw [hsearch] at hs
      simp only [Option.map_some,Option.some.injEq] at hs
      subst out
      apply FtsBankSpecL.BankInv.logged_exposed bankSpec payAfterDigest SharedForest.Signature.rho
        hinv halive entry he signature hsig A hA counter value
      change evalWithAnswerFn A (lawSpec.search signature.rho entry.1.message 0 ClaudeWCT.WCT9.digestAttemptLimit)=_
      rw [←digestSearch_public]
      exact hsearch

theorem bank_covered_exposed {published : T3.Cache} {budget : Nat} {kg : List FirstHit.QueryEvent}
    {state : BankState SharedForest.Signature}
    (hinv : bankSpec.BankInv payAfterDigest SharedForest.Signature.rho published budget kg state)
    (halive : state.1.dead=false) (A : Correctness.Answers) (hA : Agrees A (lazyOf state.2))
    (N : HashOutput) (hcovered : Covered (WPair.Paired.loggedOutputs A state.1.log) N) :
    Covered state.1.exposures N := by
  intro k t
  obtain ⟨p,hp,hi,hc,hd⟩:=hcovered k t
  obtain ⟨out,ho,rfl⟩:=List.mem_map.mp hp
  exact ⟨proposal out,List.mem_map_of_mem (loggedOutputs_exposed hinv halive A hA out ho),hi,hc,hd⟩

theorem bank_target_of_fresh {published : T3.Cache} {budget : Nat} {kg : List FirstHit.QueryEvent}
    {state : BankState SharedForest.Signature}
    (hinv : bankSpec.BankInv payAfterDigest SharedForest.Signature.rho published budget kg state)
    (hcount : countOf state.2≤budget)
    (e : FirstHit.QueryEvent) (he : e∈state.2.events) (hkg : e∉kg)
    (x : HashInput) (N : HashOutput) (hpub : eventPublic e=some (x,N))
    (hd : IsDigestInput x) (hf : e.before.2 x=none)
    (hnot : ¬bankSpec.SignerQueried payAfterDigest published state.1.log (lazyOf state.2) x) :
    N∈state.1.targets := by
  rcases hinv.events e he with hk|ht
  · exact (hkg hk).elim
  · rcases ht x N hpub hd hf with h|hb|hs
    · exact h
    · omega
    · exact (hnot hs).elim

theorem flexible_potential_source_covered (θ : ENNReal)
    {published : T3.Cache} {budget : Nat} {kg : List FirstHit.QueryEvent}
    {state : BankState SharedForest.Signature}
    (hinv : bankSpec.BankInv payAfterDigest SharedForest.Signature.rho published budget kg state)
    (hlen : state.1.log.length≤2^32) (hcount : countOf state.2≤budget)
    (A : Correctness.Answers) (hA : Agrees A (lazyOf state.2)) (N : HashOutput)
    (hN : N∈state.1.targets) (hadm : admissible N=true)
    (hcovered : Covered (WPair.Paired.loggedOutputs A state.1.log) N) :
    1≤flexiblePotential θ budget state :=
  flexible_potential_win θ budget state (bank_alive hinv hlen) hcount
    (Or.inr ⟨N,hN,hadm,bank_covered_exposed hinv (bank_alive hinv hlen) A hA N hcovered⟩)

end ClaudeWCT.Bank.Paired

section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord WCoord)
open SigGolfCandidate.T3.Security.LargeResidual (State Cell runWith_bind)
open ClaudeWCT.W9.T3.Security.FamResidual (observedRun)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeCouplingCert_pairedInteraction : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
section Interaction
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData} {q : Nat} (initLaw : PMF AuxData)
theorem interaction_le' (hcoh : LargeResidual.Paired.Coherent U T vals nv τ a) (hq : q ≤ 2 ^ 127) (hUpub : SeccLaw.publicUniverse ⊆ U)
    (published : SigGolfCandidate.T3.Cache) (hsource : ∀request : Security.Request,request.cache=published →
      evalWithAnswerFn T (PairedOuter.FullGame.authenticatedSign published request)=
        finishOut T vals (nv request.message) (LargeResidual.Paired.signDigest T request.message))
    {α : Type} (program : OracleComp PairedOuter.LazyPrivate.Interaction α) :
    ∀ {β : Type} (Final : Monitor → RouterState → (α × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) → LazyPrivate.State → Prop)
      (K : Option ((α × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) × RouterState) → OracleComp (RWorld U) β)
      (F : Option β × LargeResidual.State WCoord (Cell U) → Prop),
      (∀ mon st ws state v log, Rel U T vals nv τ a q mon st ws → MemoOk T st → Final mon st (v, log) state →
        1 ≤ Pr[F | observedRun (auxLaw initLaw) q (Sum.elim vals nv) τ (K (some ((v, log), st))) ws]) →
      (∀ m s v σ, Final m s v σ → m.contact = true ∨ m.calls ≤ q) →
      (∀ ws' : LargeResidual.State WCoord (Cell U), ws'.counters.calls ≤ q →
        F (none, ws') ∨ ∀ m s v σ, Final m s v σ → m.contact = false) →
      (∀ m s v σ, Final m s v σ → FamOK s) →
      ∀ (mon : Monitor) (st : RouterState) (ws : LargeResidual.State WCoord (Cell U)) (state : LazyPrivate.State),
        Rel U T vals nv τ a q mon st ws → MemoOk T st →
        Pr[fun t => Final (t.steps.foldl (Monitor.step U T q published) mon)
              (t.steps.foldl (routerStep U T nv published) st) t.value t.state |
            taggedFixed T published program state] ≤
          Pr[F | observedRun (auxLaw initLaw) q (Sum.elim vals nv) τ
            (routeInteraction U a published q program st >>= K) ws] := by
  induction program using OracleComp.inductionOn with
  | pure v =>
      intro β Final K F hleaf habort hstop hfin mon st ws state hrel hmemo
      rw [taggedFixed_pure, routeInteraction_pure, pure_bind, probEvent_pure]
      split_ifs with hf
      · exact hleaf mon st ws state v [] hrel hmemo hf
      · exact zero_le
  | query_bind input next ih =>
      intro β Final K F hleaf habort hstop hfin mon st ws state hrel hmemo
      rcases input with (n | X) | request
      ·
        rw [taggedFixed_world, routeInteraction_coin, bind_assoc, observed_coinReq]
        rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
        apply ENNReal.tsum_le_tsum
        intro c
        have hc : Pr[= c | Wots.Ref.fixedWorld T (.inl (.inl n))] =
            Pr[= c | (liftM (auxLaw initLaw (.coin n)) : SPMF (Fin (n + 1)))] := by
          change Pr[= c | (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))] = _
          simp [auxLaw, SPMF.probOutput_eq_apply, SPMF.liftM_apply, PMF.uniformOfFintype_apply]
        rw [hc]
        gcongr
        rw [probEvent_map]
        exact ih c Final K F hleaf habort hstop hfin mon st ws _ hrel hmemo
      ·
        rw [taggedFixed_world, Wots.Ref.fixedWorld_public, pure_bind, probEvent_map, routeInteraction_hash]
        by_cases hb : q ≤ st.calls
        ·
          rw [if_pos hb]
          have hzero : Pr[(fun t => Final (t.steps.foldl (Monitor.step U T q published) mon)
                (t.steps.foldl (routerStep U T nv published) st) t.value t.state) ∘
              (fun last => (⟨last.value, .world ⟨state, .inl (.inr X), T (.inl (.inr X))⟩ :: last.steps,
                last.state⟩ : Tagged α)) |
              taggedFixed T published (next (T (.inl (.inr X))))
                (FirstHit.advance state (.inl (.inr X)) (T (.inl (.inr X))))] = 0 := by
            have h1 := query_over U T q mon hrel.contact (by rw [hrel.calls]; exact hb) X (T (.inl (.inr X)))
            refine le_antisymm ((probEvent_mono'' (q := fun _ => False) ?_).trans (by simp)) (zero_le)
            intro t ht
            simp only [Function.comp_apply, List.foldl_cons] at ht
            have h2 := steps_over U T q published _ h1.1 h1.2 t.steps
            rcases habort _ _ _ _ ht with h | h
            · change (List.foldl (Monitor.step U T q published) (mon.query U T q X (T (.inl (.inr X)))) t.steps).contact
                = true at h
              rw [h2.1] at h
              cases h
            · change (List.foldl (Monitor.step U T q published) (mon.query U T q X (T (.inl (.inr X)))) t.steps).calls
                ≤ q at h
              omega
          rw [hzero]
          exact zero_le
        · by_cases hok : FamOK st
          swap
          · have hzero : Pr[(fun t => Final (t.steps.foldl (Monitor.step U T q published) mon)
                  (t.steps.foldl (routerStep U T nv published) st) t.value t.state) ∘
                (fun last => (⟨last.value, .world ⟨state, .inl (.inr X), T (.inl (.inr X))⟩ :: last.steps,
                  last.state⟩ : Tagged α)) |
                taggedFixed T published (next (T (.inl (.inr X))))
                  (FirstHit.advance state (.inl (.inr X)) (T (.inl (.inr X))))] = 0 := by
              refine le_antisymm ((probEvent_mono'' (q := fun _ => False) ?_).trans (by simp)) (zero_le)
              intro t ht
              exact hok (famOK_mono (steps_disclosed_mono U T nv published _ _) (hfin _ _ _ _ ht))
            rw [hzero]
            exact zero_le
          rw [if_neg hb, bind_assoc]
          have hlt : st.calls < q := by omega
          obtain ⟨ws1, hout⟩ := routeQuery_observed (auxLaw initLaw) hcoh hrel hlt hq hok X
          rcases hout with ⟨hc, hrun, -, hcalls⟩ | ⟨hc, hrun, hrel1⟩
          ·
            rw [observedRun, runWith_bind, ← observedRun, hrun, pure_bind]
            simp only [Option.elim_none]
            rcases hstop ws1 hcalls with hF | hnc
            · rw [probEvent_pure, if_pos hF]
              exact probEvent_le_one
            · have hzero : Pr[(fun t => Final (t.steps.foldl (Monitor.step U T q published) mon)
                    (t.steps.foldl (routerStep U T nv published) st) t.value t.state) ∘
                  (fun last => (⟨last.value, .world ⟨state, .inl (.inr X), T (.inl (.inr X))⟩ :: last.steps,
                    last.state⟩ : Tagged α)) |
                  taggedFixed T published (next (T (.inl (.inr X))))
                    (FirstHit.advance state (.inl (.inr X)) (T (.inl (.inr X))))] = 0 := by
                refine le_antisymm ((probEvent_mono'' (q := fun _ => False) ?_).trans (by simp)) (zero_le)
                intro t ht
                simp only [Function.comp_apply, List.foldl_cons] at ht
                have h1 := hnc _ _ _ _ ht
                change (List.foldl (Monitor.step U T q published) (mon.query U T q X (T (.inl (.inr X)))) t.steps).contact
                  = false at h1
                rw [steps_frozen U T q published _ hc] at h1
                rw [hc] at h1
                cases h1
              rw [hzero]
              exact zero_le
          · rw [observedRun, runWith_bind, ← observedRun, hrun, pure_bind]
            simp only [Option.elim_some]
            have hmemo1 : MemoOk T (st.next U X (T (.inl (.inr X)))) := by
              intro m f hf
              apply hmemo m f
              unfold LargeResidual.RouterState.next at hf
              split_ifs at hf <;> exact hf
            exact ih (T (.inl (.inr X))) Final K F hleaf habort hstop hfin _ _ ws1 _ hrel1 hmemo1
      ·
        rw [taggedFixed_request, Wots.Ref.fixedRecord_hashOnly T _ (Wots.PairedReference.Ref.authenticatedSign_hashOnly _ _),
          pure_bind, probEvent_map, routeInteraction_request, bind_assoc]
        obtain ⟨wsF, hrun, hrelF⟩ := routeSign_observed (auxLaw initLaw) hcoh hUpub published hsource hrel hmemo request
        rw [observedRun, runWith_bind, ← observedRun, hrun, pure_bind]
        simp only [Option.elim_some, bind_assoc, pure_bind]
        have hval : (Wots.Ref.pureRecord T (PairedOuter.FullGame.authenticatedSign published request) state).value =
            evalWithAnswerFn T (PairedOuter.FullGame.authenticatedSign published request) := Wots.Ref.pureRecord_value _ _ _
        rw [hval]
        set out := evalWithAnswerFn T (PairedOuter.FullGame.authenticatedSign published request) with hout
        let Final' : Monitor → RouterState → (α × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) → LazyPrivate.State → Prop :=
          fun m s v σ => Final m s (v.1, ⟨request, out⟩ :: v.2) σ
        let K' : Option ((α × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) × RouterState) → OracleComp (RWorld U) β :=
          fun rest => K (rest.map fun res => ((res.1.1, ⟨request, out⟩ :: res.1.2), res.2))
        have hleaf' : ∀ mon st ws state v log, Rel U T vals nv τ a q mon st ws → MemoOk T st →
            Final' mon st (v, log) state →
            1 ≤ Pr[F | observedRun (auxLaw initLaw) q (Sum.elim vals nv) τ (K' (some ((v, log), st))) ws] :=
          fun mon st ws state v log hrel hmemo hf => hleaf mon st ws state v (⟨request, out⟩ :: log) hrel hmemo hf
        have habort' : ∀ m s v σ, Final' m s v σ → m.contact = true ∨ m.calls ≤ q :=
          fun m s v σ hf => habort _ _ _ _ hf
        have hstop' : ∀ ws' : LargeResidual.State WCoord (Cell U), ws'.counters.calls ≤ q →
            F (none, ws') ∨ ∀ m s v σ, Final' m s v σ → m.contact = false := by
          intro ws' hws
          rcases hstop ws' hws with h | h
          · exact Or.inl h
          · exact Or.inr fun m s v σ hf => h _ _ _ _ hf
        exact ih out Final' K' F hleaf' habort' hstop' (fun m s v σ hf => hfin _ _ _ _ hf) _ _ wsF _ hrelF
          (signedState_memo T nv published st request hmemo)
end Interaction
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
end

section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord WCoord)
open SigGolfCandidate.T3.Security.LargeResidual (State Cell runWith_bind)
open ClaudeWCT.W9.T3.Security.FamResidual (observedRun)
open SigGolfCandidate.T3.Security.LargeCoupling (honestNonce)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen
noncomputable local instance instDecidableEqCache_w9largeCouplingCert_pairedTable : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
noncomputable def verdictCert (U : Finset HashInput) (T : Answers) (q : Nat) (pk : Digest) (mon : Monitor)
    (st : RouterState) (value : Option ClaudeWCT.W9.T3M.Final.Paired.ForgeryP × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) (state : LazyPrivate.State) : Prop :=
  evalWithAnswerFn T (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker pk value) = true ∧
  ((Wots.Ref.pureRecord T (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker pk value) state).events.foldl
    (Monitor.event U T q) mon).contact = false ∧
  ((Wots.Ref.pureRecord T (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker pk value) state).events.foldl
    (Monitor.event U T q) mon).calls ≤ q ∧
  CertGhost ((Wots.Ref.pureRecord T (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker pk value) state).events.foldl
    (routerEvent U) st)
theorem honestNonce_coherent {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
    {τ : Cell U → HashOutput} {a : AuxData} (hcoh : LargeResidual.Paired.Coherent U T vals nv τ a) : nv = honestNonce T := by
  funext m
  exact (hcoh.privateNonce m).symm
theorem table_cert_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) (initLaw : PMF AuxData)
    {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
    {τ : Cell (Wots.PairedReference.referenceInputs adversary) → HashOutput} {a : AuxData}
    (hcoh : LargeResidual.Paired.Coherent (Wots.PairedReference.referenceInputs adversary) T vals nv τ a) :
    Pr[fun rec => CertR adversary q rec T ∧ NoOvR adversary rec T |
        Wots.Ref.fixedRecord T (PairedOuter.GameWith.idealGame PairedOuter.PaddedGame.checker adversary) (∅, ∅)] ≤
      Pr[CertOut |
        observedRun (auxLaw initLaw) q (Sum.elim vals nv) τ (routerWith (Wots.PairedReference.referenceInputs adversary) adversary q a)
          LargeResidual.initial] := by
  have hUpub : SeccLaw.publicUniverse ⊆ Wots.PairedReference.referenceInputs adversary := Wots.PairedReference.Ref.referenceInputs_universe adversary
  obtain ⟨-, hpub, -⟩ := Correctness.keygen_correct T
  have hnv := honestNonce_coherent hcoh
  rw [hcoh.routerWith, Wots.PairedReference.Ref.fixed_game_eq, probEvent_map]
  unfold Wots.PairedReference.Ref.fixedInteraction
  rw [← taggedFixed_untag, probEvent_map]
  refine (probEvent_mono ?_).trans (interaction_le' initLaw hcoh hq hUpub (evalWithAnswerFn T keygen).2 (hcoh.source _ hpub)
    (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2)
    (fun mon st value state => verdictCert (Wots.PairedReference.referenceInputs adversary) T q (evalWithAnswerFn T keygen).1 mon st
      value state ∧ FamOK st)
    (verdictCont (Wots.PairedReference.referenceInputs adversary) a q (evalWithAnswerFn T keygen).1) CertOut
    ?_ ?_ ?_ (fun _ _ _ _ h => h.2) Monitor.initial LargeResidual.RouterState.initial
    (keyState (Wots.PairedReference.referenceInputs adversary) q vals nv) _ rel_initial
    (fun _ _ h => by simp [LargeResidual.RouterState.initial] at h))
  · intro t ht hc
    have hsplit := canonical_split adversary T t ht
    obtain ⟨h1, h2, h3, h4⟩ := hc.1 _ _ _ hsplit
    rw [Wots.Ref.pureRecord_value] at h2 h3 h4
    have hv : (Wots.PairedReference.Ref.verdictRecord T t.untag).value =
        evalWithAnswerFn T (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker (evalWithAnswerFn T keygen).1 t.value) :=
      Wots.Ref.pureRecord_value _ _ _
    refine ⟨⟨hv ▸ h1, h2, h3, ?_⟩, fun f => ?_, fun L => ?_⟩
    · unfold routerFold at h4
      rw [hnv]
      exact h4
    · have hno : LogNoOverflow T t.value.2 := hc.2 _ _ _ hsplit.untag
      have hsub := discSeeds_steps hcoh (evalWithAnswerFn T keygen).2 (hcoh.source _ hpub) _ _ t ht LargeResidual.RouterState.initial f
      rw [discSeeds_initial, Finset.empty_union] at hsub
      exact (Finset.card_le_card hsub).trans ((logSeeds_card T _ hno f).trans (by norm_num))
    · have hsub := discLower_steps (Wots.PairedReference.referenceInputs adversary) T nv (evalWithAnswerFn T keygen).2 t.steps
        LargeResidual.RouterState.initial L
      rw [discLower_initial, Finset.empty_union] at hsub
      have := lowerZeros_card T L
      exact (Finset.card_le_card hsub).trans (by omega)
  · intro mon st ws state v log hrel _ hf
    obtain ⟨out, ws', hrun, hph⟩ := routeVerdict_observed (auxLaw initLaw) hcoh hq
      (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker (evalWithAnswerFn T keygen).1 (v, log))
      (PairedOuter.PaddedGame.verdict_public _ _) mon st ws state hrel hf.2
    change 1 ≤ Pr[_ | observedRun (auxLaw initLaw) q (Sum.elim vals nv) τ
      (routeVerdict (Wots.PairedReference.referenceInputs adversary) a q
        (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker (evalWithAnswerFn T keygen).1 (v, log)) st) ws]
    rw [hrun, probEvent_pure]
    obtain ⟨⟨hval, hnc, hcalls, hcert⟩, -⟩ := hf
    rcases hph with ⟨-, h2, -⟩ | ⟨-, h2, h3⟩ | ⟨h1, -⟩
    · rw [hnc] at h2; cases h2
    · omega
    · rw [if_pos ⟨_, by rw [h1, hval], hcert⟩]
  · intro m s v σ hf
    by_contra hcon
    simp only [not_or, not_le] at hcon
    have hc : m.contact = false := by simpa using hcon.1
    have h := events_over (Wots.PairedReference.referenceInputs adversary) T q m hc (by omega) (Wots.Ref.pureRecord T
      (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker (evalWithAnswerFn T keygen).1 v) σ).events
    have := hf.1.2.2.1
    omega
  · intro ws' _
    right
    intro m s v σ hf
    by_contra hcon
    have hc : m.contact = true := by simpa using hcon
    have h := hf.1.2.1
    rw [events_frozen (Wots.PairedReference.referenceInputs adversary) T q m hc] at h
    rw [hc] at h
    cases h
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
end

section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord WCoord)
open SigGolfCandidate.T3.Security.LargeCoupling (honestNonce)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeCouplingCert_pairedShort : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
theorem routerStep_world (U : Finset HashInput) (A : Answers) (nv : Message → Digest) (published : SigGolfCandidate.T3.Cache)
    (st : RouterState) (e : FirstHit.QueryEvent) : routerStep U A nv published st (.world e) = routerEvent U st e := rfl
theorem routerStep_sign (U : Finset HashInput) (A : Answers) (nv : Message → Digest) (published : SigGolfCandidate.T3.Cache)
    (st : RouterState) (request : Security.Request) (out : Option SigGolfCandidate.Research.SharedForest.Signature) (events : List FirstHit.QueryEvent) :
    routerStep U A nv published st (.sign request out events) = signedState A nv published st request := rfl
section Short
variable {A T : Answers} (hAT : Wots.Ref.ShortAgree A T)
include hAT
theorem honestNonce_short : honestNonce A=honestNonce T := by
  funext m
  unfold honestNonce
  simp only [SigGolfCandidate.T3.privateNonce,privateHash,evalWithAnswerFn_bind,evalWithAnswerFn_pure]
  change (A (.inr (.inr (.inl m)))).extractLsb' 0 128=(T (.inr (.inr (.inl m)))).extractLsb' 0 128
  rw [hAT.priv]
theorem routeOk_short : RouteOk A = RouteOk T := by
  funext index
  apply propext
  unfold RouteOk
  simp only [Wots.CanonicalRef.referenceSearch_short hAT]
theorem signedState_short (nv : Message → Digest) (published : SigGolfCandidate.T3.Cache) (st : RouterState)
    (request : Security.Request) :
    signedState A nv published st request = signedState T nv published st request := by
  have hd : Wots.CanonicalRef.referenceDigits A (Wots.CanonicalRef.sourceMessages A) = Wots.CanonicalRef.referenceDigits T (Wots.CanonicalRef.sourceMessages T) := funext (Wots.CanonicalRef.referenceDigits_short hAT)
  unfold signedState LargeResidual.Paired.signItems
  rw [signDigest_short hAT, hd, routeOk_short hAT]
theorem routerStep_short (U : Finset HashInput) (published : SigGolfCandidate.T3.Cache) (st : RouterState) (s : TaggedStep) :
    routerStep U A (honestNonce A) published st s = routerStep U T (honestNonce T) published st s := by
  cases s with
  | world e => rw [routerStep_world, routerStep_world]
  | sign request out events =>
      rw [routerStep_sign, routerStep_sign, honestNonce_short hAT, signedState_short hAT]
theorem steps_router_short (U : Finset HashInput) (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep) :
    ∀ st, steps.foldl (routerStep U A (honestNonce A) published) st =
      steps.foldl (routerStep U T (honestNonce T) published) st := by
  induction steps with
  | nil => intro st; rw [List.foldl_nil, List.foldl_nil]
  | cons s rest ih =>
      intro st
      rw [List.foldl_cons, List.foldl_cons, routerStep_short hAT, ih]
theorem routerFold_short (U : Finset HashInput) (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep)
    (verdict : List FirstHit.QueryEvent) :
    routerFold U A published steps verdict = routerFold U T published steps verdict := by
  unfold routerFold
  rw [steps_router_short hAT]
end Short
theorem certR_short {A T : Answers} (hAT : Wots.Ref.ShortAgree A T) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat)
    (result : FirstHit.Recorded Bool) : CertR adversary q result A ↔ CertR adversary q result T := by
  unfold CertR
  simp only [monitorRun_short hAT, routerFold_short hAT]
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
end

section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord WCoord)
open SigGolfCandidate.T3.Security.LargeResidual (State Cell AuxQuery retain runWith_query_bind)
open ClaudeWCT.W9.T3.Security.FamResidual (lazyRun finish observedRun run_posterior lazyImpl view supp)
open SigGolfCandidate.T3.Security.LargeCoupling (probEvent_bind_le_of
  weight_self evalSPMF_uniform_inst probEvent_bind_congr_eq completeRows_none)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
theorem probEvent_bind_mono_le {α β γ : Type} (m : SPMF α) (f : α → SPMF β) (g : α → SPMF γ) (E : β → Prop)
    (E' : γ → Prop) (h : ∀ x, Pr[E | f x] ≤ Pr[E' | g x]) : Pr[E | m >>= f] ≤ Pr[E' | m >>= g] := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  exact ENNReal.tsum_le_tsum fun x => by gcongr; exact h x
section CertChain
attribute [local instance] Classical.propDecidable
open ClaudeWCT.W9.T3.Security.LargeCoupling.Samplers SigGolfCandidate.T3.Security.LargeCoupling.Samplers
def RealCert (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (x : FirstHit.Recorded Bool × Answers) : Prop :=
  CertR adversary q x.1 x.2 ∧ NoOvR adversary x.1 x.2
theorem cert_real_side (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => CertR adversary q (QueryRecorded.recordedTrace z.1) z.2 ∧
        NoOvR adversary (QueryRecorded.recordedTrace z.1) z.2 | PairedSeccLaw.completedExperiment adversary q hq] =
      Pr[RealCert adversary q |
        ($ᵗ FullGame.FullTable : ProbComp _) >>= fun priv =>
          ($ᵗ (Wots.PairedReference.referenceInputs adversary → HashOutput) : ProbComp _) >>= fun pub =>
            fixedNext adversary (Wots.eagerAnswers (Wots.PairedReference.referenceInputs adversary) priv pub)] := by
  have h1 := Wots.PairedReference.completed_eager_cut adversary q hq (fun rec A => CertR adversary q rec A ∧ NoOvR adversary rec A)
  rw [h1]
  have h2 : (fun x : FirstHit.Recorded Bool × Answers => CertR adversary q x.1 (Wots.Ref.cut x.1.state x.2) ∧
      NoOvR adversary x.1 (Wots.Ref.cut x.1.state x.2)) = RealCert adversary q := by
    funext x
    exact propext (and_congr (certR_short (Wots.Ref.cut_shortAgree _ _) adversary q x.1)
      (noOvR_short (Wots.Ref.cut_shortAgree _ _) adversary x.1))
  rw [h2]
  unfold Wots.PairedReference.eagerRecorded
  rw [MonitoredPrivate.event_lift]
  apply probEvent_congr' (fun _ _ => Iff.rfl)
  rw [evalSPMF_bind, evalSPMF_bind, evalSPMF_uniform_inst _ samplerFull]
  congr 1
section Lazy
variable {U : Finset HashInput}
theorem finish_some_le {R : Type} (X : SPMF (Option R × LargeResidual.State WCoord (Cell U))) (P : R → Prop) :
    Pr[fun r => ∃ v, r.1 = some v ∧ P v.2.2 | X >>= finish] ≤ Pr[fun r => ∃ v, r.1 = some v ∧ P v | X] := by
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro r
  rcases r with ⟨v, st⟩
  cases v with
  | none =>
      have h0 : Pr[fun r => ∃ v, r.1 = some v ∧ P v.2.2 | finish ((none : Option R), st)] = 0 := by
        simp only [finish, probEvent_pure]
        rw [if_neg]
        rintro ⟨v, hv, -⟩
        cases hv
      rw [h0, mul_zero]
      exact zero_le
  | some v =>
      by_cases hP : P v
      · rw [if_pos ⟨v, rfl, hP⟩]
        exact mul_le_of_le_one_right zero_le probEvent_le_one
      · have h0 : Pr[fun r => ∃ v, r.1 = some v ∧ P v.2.2 | finish (some v, st)] = 0 := by
          rw [probEvent_eq_zero_iff]
          intro x hx hE
          unfold finish at hx
          simp only [mem_support_bind_iff, mem_support_pure_iff] at hx
          obtain ⟨labels, -, table, -, rfl⟩ := hx
          obtain ⟨v', hv', hP'⟩ := hE
          simp only [Option.some.injEq] at hv'
          subst hv'
          exact hP hP'
        rw [h0, mul_zero]
        exact zero_le
theorem observed_avg_le {R : Type} (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
    (program : OracleComp (RWorld U) R) (P : R → Prop) :
    Pr[fun r => ∃ v, r.1 = some v ∧ P v | 𝒮[($ᵗ (ClaudeWCT.W9.T3.Security.FamResidual.Hid WCoord) : ProbComp _)] >>=
        fun x => 𝒮[($ᵗ (Cell U → LargeResidual.HashOutput) : ProbComp _)] >>= fun τ =>
          observedRun aux q (view x) τ program LargeResidual.initial] ≤
      Pr[fun r => ∃ v, r.1 = some v ∧ P v | lazyRun aux q program LargeResidual.initial] := by
  rw [← cell_univ, ← completeRows_none]
  have hpost := run_posterior aux q program (LargeResidual.initial : LargeResidual.State WCoord (Cell U))
    (by change (supp (fun _ : WCoord => (Finset.univ : Finset LargeResidual.Digest))).Nonempty
        rw [ClaudeWCT.W9.T3.Security.FamResidual.supp_univ]; exact Finset.univ_nonempty)
  refine le_trans (le_of_eq ?_) (finish_some_le (lazyRun aux q program LargeResidual.initial) P)
  rw [← hpost]
  apply probEvent_bind_congr_eq
  intro labels
  apply probEvent_bind_congr_eq
  intro τ
  rw [probEvent_map]
  congr 1
  funext r
  apply propext
  rcases r with ⟨_ | v, st⟩
  · simp [retain]
  · simp [retain]
theorem certOut_iff (r : Option (Option (Bool × RouterState)) × LargeResidual.State WCoord (Cell U)) :
    CertOut r ↔ ∃ v, r.1 = some v ∧ ∃ st, v = some (true, st) ∧ CertGhost st := by
  constructor
  · rintro ⟨st, h1, h2⟩
    exact ⟨_, h1, st, rfl, h2⟩
  · rintro ⟨v, h1, st, rfl, h2⟩
    exact ⟨st, h1, h2⟩
theorem router_side_cert (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    Pr[CertOut |
        𝒮[($ᵗ LowLabels : ProbComp _)] >>= fun high =>
        𝒮[($ᵗ (EncLeaf → Fin (2 ^ 22) → HashOutput) : ProbComp _)] >>= fun rows =>
        𝒮[($ᵗ FullGame.FullTable : ProbComp _)] >>= fun priv =>
        𝒮[($ᵗ (ClaudeWCT.W9.T3.Security.FamResidual.Hid WCoord) : ProbComp _)] >>= fun x =>
        𝒮[($ᵗ (Cell (Wots.PairedReference.referenceInputs adversary) → LargeResidual.HashOutput) : ProbComp _)] >>= fun τ =>
        observedRun (auxLaw initLaw) q (view x) τ
          (routerWith (Wots.PairedReference.referenceInputs adversary) adversary q (auxOf high rows priv)) LargeResidual.initial] ≤
      Pr[CertOut |
        lazyRun (auxLaw initLaw) q (router (Wots.PairedReference.referenceInputs adversary) adversary q) LargeResidual.initial] := by
  have hce : (@CertOut (Wots.PairedReference.referenceInputs adversary)) =
      fun r => ∃ v, r.1 = some v ∧ ∃ st, v = some (true, st) ∧ CertGhost st :=
    funext fun r => propext (certOut_iff r)
  rw [hce]
  unfold router initReq
  rw [lazy_aux]
  change _ ≤ Pr[_ | (liftM initLaw : SPMF AuxData) >>= _]
  rw [initLaw_spmf]
  unfold initComp
  simp only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind]
  apply probEvent_bind_mono_le
  intro high
  apply probEvent_bind_mono_le
  intro rows
  apply probEvent_bind_mono_le
  intro priv
  exact observed_avg_le (auxLaw initLaw) q _ _
end Lazy
set_option maxHeartbeats 4000000 in
theorem cert_le_lazy (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => CertR adversary q (QueryRecorded.recordedTrace z.1) z.2 ∧
        NoOvR adversary (QueryRecorded.recordedTrace z.1) z.2 | PairedSeccLaw.completedExperiment adversary q hq] ≤
      Pr[CertOut | lazyRun (auxLaw initLaw) q (router (Wots.PairedReference.referenceInputs adversary) adversary q)
        LargeResidual.initial] + (2 ^ 142 : ℝ≥0∞)⁻¹ := by
  have hU : CanonGraph.Paired.canonInputs ⊆ Wots.PairedReference.referenceInputs adversary :=
    CanonGraph.Paired.canonInputs_subset_publicUniverse.trans (Wots.PairedReference.Ref.referenceInputs_universe adversary)
  have hE : encInputs ⊆ Wots.PairedReference.referenceInputs adversary :=
    encInputs_subset_publicUniverse.trans (Wots.PairedReference.Ref.referenceInputs_universe adversary)
  rw [cert_real_side]
  refine le_trans ?_ (add_le_add (router_side_cert adversary q) le_rfl)
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (law_target (Wots.PairedReference.referenceInputs adversary) hU hE (fixedNext adversary))]
  refine le_trans (probEvent_bind_le_of_add _ _ _ _ _ _ capErr (weight_self _) fun high => ?_)
    (add_le_add le_rfl capErr_le)
  refine probEvent_bind_le_of_add_const _ _ _ _ _ _ (capErr high) (weight_self _) fun rows => ?_
  refine probEvent_bind_le_of_add_const _ _ _ _ _ _ (capErr high) (weight_self _) fun priv => ?_
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (world_split _)]
  refine le_trans (probEvent_bind_le_of_add _ _ _ _ _ _
    (fun x => if CanonGraph.CapFail (CanonGraph.Paired.joinLabels (fun N => x.1 (.inl (.inl N))) high) then 1 else 0)
    (weight_self _) fun x => ?_) (add_le_add le_rfl (le_of_eq ?_))
  swap
  · unfold capErr
    refine tsum_congr fun x => ?_
    rw [probOutput_uniformSample]
  by_cases hcf : CanonGraph.CapFail (CanonGraph.Paired.joinLabels (fun N => x.1 (.inl (.inl N))) high)
  · rw [if_pos hcf]
    exact le_trans probEvent_le_one le_add_self
  rw [if_neg hcf, add_zero]
  refine probEvent_bind_le_const _ _ _ _ fun jk => ?_
  have hτ : ∀ (k : (Wots.PairedReference.referenceInputs adversary → HashOutput) → ProbComp (FirstHit.Recorded Bool × Answers)),
      𝒮[(@uniformSample (Wots.PairedReference.referenceInputs adversary → HashOutput) (samplerPublic _) : ProbComp _) >>= k] =
        𝒮[(@uniformSample (Wots.PairedReference.referenceInputs adversary → HashOutput) (samplerCell _) : ProbComp _) >>= k] := by
    intro k
    rw [evalSPMF_bind]
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (hτ _)]
  refine probEvent_bind_le_of _ _ _ _ _ _ (weight_self _) fun τ => ?_
  · have hT : CanonGraph.eagerAnswers (privateEquiv.symm (secOf x jk,
          nonceOver (privateEquiv priv).2 (fun m => x.1 (.inr m)))) (Wots.PairedReference.referenceInputs adversary)
          (CanonGraph.Paired.Filtered.programmed (Wots.PairedReference.referenceInputs adversary) hU (secOf x jk)
            (CanonGraph.Paired.joinLabels (fun N => x.1 (.inl (.inl N))) high)
            (residualPsi (Wots.PairedReference.referenceInputs adversary) hE (CanonGraph.Paired.joinLabels (fun N => x.1 (.inl (.inl N))) high) rows τ)) =
        tablePsi (Wots.PairedReference.referenceInputs adversary) hU hE (secOf x jk) (fun c => view x (.inl c)) (fun m => view x (.inr m)) τ
          (auxOf high rows priv) := by
      unfold tablePsi
      rw [eagerAnswers_eq]
      rfl
    rw [hT]
    unfold fixedNext RealCert
    rw [probEvent_map]
    have h := table_cert_le adversary q hq initLaw
      (coherent_psi (Wots.PairedReference.referenceInputs adversary) hU hE (secOf x jk) (fun c => view x (.inl c))
        (fun m => view x (.inr m)) τ (auxOf high rows priv) (auxOf_consistent _ _ _) (seedView_secOf x jk) hcf)
    have hlab : Sum.elim (fun c => view x (.inl c)) (fun m => view x (.inr m)) = view x := by
      funext c
      rcases c with c | m <;> rfl
    rw [hlab] at h
    exact h
end CertChain
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
end
namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord WCoord)
open SigGolfCandidate.T3.Security.LargeResidual (State Cell)
open ClaudeWCT.W9.T3.Security.FamResidual (lazyRun lazy_pure)
open SigGolfCandidate.T3.Security.LargeCoupling (ev_bind_le ev_runWith_bind)
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _
variable (θ : ENNReal)
noncomputable def bankPay {U : Finset HashInput} (θ : ENNReal) (q : Nat)
    (r : Option (Option (Bool × RouterState)) × LargeResidual.State WCoord (Cell U)) : ENNReal :=
  (match r.1 with
    | some (some (_, st)) => psi θ q st
    | _ => 0) + slackT θ q r.2
section Run
variable {U : Finset HashInput} (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
theorem bank_interaction (hUpub : SeccLaw.publicUniverse ⊆ U) (a : AuxData) (published : SigGolfCandidate.T3.Cache) {α : Type}
    (program : OracleComp PairedOuter.LazyPrivate.Interaction α) :
    ∀ {β : Type} (K : Option ((α × QueryLog Final.Paired.Requests) × RouterState) → OracleComp (RWorld U) β)
      (pay : Option β × LargeResidual.State WCoord (Cell U) → ENNReal),
      (∀ ws', pay (none, ws') ≤ slackT θ q ws') →
      (∀ v st ws, BankInv U ws st → st.calls ≤ q →
        expectedValue (lazyRun aux q (K (some (v, st))) ws) pay ≤ psi θ q st + slackT θ q ws) →
      (∀ ws, expectedValue (lazyRun aux q (K none) ws) pay ≤ slackT θ q ws) →
      ∀ st ws, BankInv U ws st → st.calls ≤ q →
        expectedValue (lazyRun aux q (routeInteraction U a published q program st >>= K) ws) pay ≤
          psi θ q st + slackT θ q ws := by
  induction program using OracleComp.inductionOn with
  | pure v =>
      intro β K pay _ hleaf _ st ws hinv hcalls
      rw [routeInteraction_pure, pure_bind]
      exact hleaf _ st ws hinv hcalls
  | query_bind input next ih =>
      intro β K pay hstop hleaf hnone st ws hinv hcalls
      rcases input with (n | X) | request
      · rw [routeInteraction_coin, bind_assoc, lazy_coinReq]
        apply ev_bind_le
        intro c
        exact ih c K pay hstop hleaf hnone st ws hinv hcalls
      · rw [routeInteraction_hash]
        split_ifs with hb
        · rw [pure_bind]
          exact (hnone ws).trans le_add_self
        · rw [bind_assoc, lazyRun, ev_runWith_bind, ← lazyRun]
          apply bank_routeQuerySelected θ aux q a st ws X hinv (by omega)
          · intro ws'
            exact hstop ws'
          · intro y st' ws' hinv' hcalls'
            exact ih y K pay hstop hleaf hnone st' ws' hinv' hcalls'
      · rw [routeInteraction_request, bind_assoc, lazyRun, ev_runWith_bind, ← lazyRun]
        apply bank_routeSign θ aux q hUpub a published st ws request hinv
        intro sig st' ws' hinv' hcalls'
        simp only [Option.elim_some, bind_assoc, pure_bind]
        refine ih sig (fun rest => K (rest.map fun res => ((res.1.1, ⟨request, sig⟩ :: res.1.2), res.2))) pay hstop
          ?_ ?_ st' ws' hinv' (by omega)
        · intro v st ws hinv hc
          exact hleaf _ st ws hinv hc
        · intro ws
          exact hnone ws
theorem bank_verdict (a : AuxData) {β : Type} (V : M β) :
    ∀ (pay : Option (Option (β × RouterState)) × LargeResidual.State WCoord (Cell U) → ENNReal),
      (∀ ws', pay (none, ws') ≤ slackT θ q ws') →
      (∀ v st ws, BankInv U ws st → st.calls ≤ q → pay (some (some (v, st)), ws) ≤ psi θ q st + slackT θ q ws) →
      (∀ ws, pay (some none, ws) ≤ slackT θ q ws) →
      ∀ st ws, BankInv U ws st → st.calls ≤ q →
        expectedValue (lazyRun aux q (routeVerdict U a q V st) ws) pay ≤ psi θ q st + slackT θ q ws := by
  induction V using OracleComp.inductionOn with
  | pure v =>
      intro pay _ hleaf _ st ws hinv hcalls
      rw [routeVerdict_pure, lazy_pure, expectedValue_pure]
      exact hleaf v st ws hinv hcalls
  | query_bind input next ih =>
      intro pay hstop hleaf hnone st ws hinv hcalls
      rcases input with (n | X) | c
      · change expectedValue (lazyRun aux q (coinReq U n >>= fun c => routeVerdict U a q (next c) st) ws) pay ≤ _
        rw [lazy_coinReq]
        apply ev_bind_le
        intro c
        exact ih c pay hstop hleaf hnone st ws hinv hcalls
      · rw [routeVerdict_public]
        split_ifs with hb
        · rw [lazy_pure, expectedValue_pure]
          exact (hnone ws).trans le_add_self
        · rw [lazyRun, ev_runWith_bind, ← lazyRun]
          apply bank_routeQuerySelected θ aux q a st ws X hinv (by omega)
          · intro ws'
            exact hstop ws'
          · intro y st' ws' hinv' hcalls'
            exact ih y pay hstop hleaf hnone st' ws' hinv' hcalls'
      · change expectedValue (lazyRun aux q (routeVerdict U a q (next (a.priv c)) st) ws) pay ≤ _
        exact ih (a.priv c) pay hstop hleaf hnone st ws hinv hcalls
theorem bankInv_initial (s : LargeResidual.State WCoord (Cell U)) (hd : DiscFrame U LargeResidual.initial s) :
    BankInv U s LargeResidual.RouterState.initial := by
  obtain ⟨hr, hc, hn⟩ := hd
  refine ⟨by rw [hc]; rfl, by rw [hc]; exact le_rfl, le_rfl, fun m _ => by rw [hn m]; rfl,
    fun X hX _ _ _ => by rw [hr]; rfl, fun X hX _ hs _ => absurd hs (by simp [LargeResidual.RouterState.initial]),
    fun p hp => absurd hp (by simp [LargeResidual.RouterState.initial]), fun X hX => absurd hX (by simp [LargeResidual.RouterState.initial])⟩
theorem bank_router (hUpub : SeccLaw.publicUniverse ⊆ U) (initLaw : PMF AuxData) (adversary : Final.Paired.AdversaryP) :
    expectedValue (lazyRun (auxLaw initLaw) q (router U adversary q) LargeResidual.initial) (bankPay θ q) ≤
      psi θ q LargeResidual.RouterState.initial + coeffQ θ q * (q : ENNReal) / 2 ^ 128 := by
  have hslack0 : slackT θ q (LargeResidual.initial : LargeResidual.State WCoord (Cell U)) =
      coeffQ θ q * (q : ENNReal) / 2 ^ 128 := by
    unfold slackT; rfl
  rw [← hslack0]
  unfold router
  rw [lazy_initReq]
  apply ev_bind_le
  intro a
  unfold routerWith
  apply ev_discloseAll_le
  intro pairs s hd
  have hinv := bankInv_initial s hd
  refine (bank_interaction θ (auxLaw initLaw) q hUpub a _ _ _ (bankPay θ q) ?_ ?_ ?_ LargeResidual.RouterState.initial s hinv
    (Nat.zero_le _)).trans ?_
  · intro ws'
    simp only [bankPay, zero_add]
    exact le_rfl
  · intro v st ws hinv' hc
    apply bank_verdict θ (auxLaw initLaw) q a _ (bankPay θ q)
    · intro ws'
      simp only [bankPay, zero_add]
      exact le_rfl
    · intro v' st' ws' _ _
      simp only [bankPay]
      exact le_rfl
    · intro ws'
      simp only [bankPay, zero_add]
      exact le_rfl
    · exact hinv'
    · exact hc
  · intro ws
    rw [lazy_pure, expectedValue_pure]
    simp only [bankPay, zero_add]
    exact le_rfl
  · rw [slackT_eq_of_mass θ q (show s.counters.mass = (LargeResidual.initial : LargeResidual.State WCoord (Cell U)).counters.mass by
      rw [hd.2.1])]
end Run

end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord WCoord)
open SigGolfCandidate.T3.Security.LargeResidual (State Cell)
open ClaudeWCT.W9.T3.Security.FamResidual (lazyRun lazy_pure lazy_noFail)
open SigGolfCandidate.T3.Security.LargeCoupling (ev_bind_le ev_runWith_bind)
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _
variable (θ : ENNReal)
variable {U : Finset HashInput}
noncomputable def psiOut (θ : ENNReal) (q : Nat) (r : Option (Option (Bool × RouterState)) × LargeResidual.State WCoord (Cell U)) :
    ENNReal :=
  match r.1 with
  | some (some (_, st)) => psi θ q st
  | _ => 0
theorem certOut_le_psi (q : Nat) (r : Option (Option (Bool × RouterState)) × LargeResidual.State WCoord (Cell U)) :
    (if CertOut r then (1 : ENNReal) else 0) ≤ psiOut θ q r := by
  split_ifs with h
  · obtain ⟨st, hr, hc⟩ := h
    unfold psiOut
    rw [hr]
    exact psi_cert θ q st hc
  · exact zero_le
theorem bank_cert_le (hUpub : SeccLaw.publicUniverse ⊆ U) (initLaw : PMF AuxData) (adversary : Final.Paired.AdversaryP) (q : Nat) (htheta : θ≠⊤) (rate : ENNReal)
    (hexc : ClaudeWCT.Numerics.Law.lawAvg ClaudeWCT.Bank.Paired.lawSpec.law (2^32)
      (fun W=>ClaudeWCT.Bank.Paired.lawSpec.price W-θ)≤rate) :
    Pr[CertOut | lazyRun (auxLaw initLaw) q (router U adversary q) LargeResidual.initial] ≤
      (q : ENNReal) * rate / 2 ^ 128 +
        coeffQ θ q * (∑' r, Pr[= r | lazyRun (auxLaw initLaw) q (router U adversary q) LargeResidual.initial] *
          (r.2.counters.mass : ENNReal)) / 2 ^ 128 := by
  set L := lazyRun (auxLaw initLaw) q (router U adversary q) LargeResidual.initial with hL
  have hfail : Pr[⊥ | L] = 0 := lazy_noFail (auxLaw initLaw) q _
  have hbank := bank_router θ q hUpub initLaw adversary
  rw [← hL] at hbank
  have hbp : (bankPay θ q : Option (Option (Bool × RouterState)) × LargeResidual.State WCoord (Cell U) → ENNReal) =
      fun r => psiOut θ q r + slackT θ q r.2 := rfl
  rw [hbp, expectedValue_add] at hbank
  have hcert : Pr[CertOut | L] ≤ expectedValue L (psiOut θ q) := by
    rw [← expectedValue_ite_one]
    exact expectedValue_mono _ (certOut_le_psi θ q)
  set S := expectedValue L (fun r => slackT θ q r.2) with hS
  set Mass := ∑' r, Pr[= r | L] * (r.2.counters.mass : ENNReal) with hMass
  have hmass : coeffQ θ q * (q : ENNReal) / 2 ^ 128 ≤ S + coeffQ θ q * Mass / 2 ^ 128 := by
    have hMass' : coeffQ θ q * Mass / 2 ^ 128 =
        expectedValue L (fun r => coeffQ θ q * (r.2.counters.mass : ENNReal) / 2 ^ 128) := by
      rw [hMass]
      simp only [div_eq_mul_inv, ← mul_assoc, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
      rw [expectedValue_def]
      apply tsum_congr
      intro r
      ring
    rw [hMass', hS, ← expectedValue_add, ← expectedValue_const hfail (coeffQ θ q * (q : ENNReal) / 2 ^ 128)]
    apply expectedValue_mono
    intro r
    unfold slackT
    rw [← ENNReal.add_div, ← mul_add, ← Nat.cast_add]
    apply ENNReal.div_le_div_right
    apply mul_le_mul' le_rfl
    exact_mod_cast (show q ≤ q - r.2.counters.mass + r.2.counters.mass by omega)
  have hcoeff_fin : coeffQ θ q ≠ ⊤ := by unfold coeffQ; exact ENNReal.add_ne_top.mpr ⟨htheta,by change (1/1024:ENNReal)≠⊤; finiteness⟩
  have hSfin : S ≠ ⊤ := by
    apply ne_top_of_le_ne_top (b := coeffQ θ q * (q : ENNReal) / 2 ^ 128)
    · exact ENNReal.div_ne_top (ENNReal.mul_ne_top hcoeff_fin (ENNReal.natCast_ne_top q)) (by positivity)
    · apply expectedValue_le_of_le
      intro r
      unfold slackT
      apply ENNReal.div_le_div_right
      apply mul_le_mul' le_rfl
      exact_mod_cast Nat.sub_le q _
  have hkey : expectedValue L (psiOut θ q) + S ≤ (psi θ q LargeResidual.RouterState.initial + coeffQ θ q * Mass / 2 ^ 128) + S := by
    calc
      _ ≤ psi θ q LargeResidual.RouterState.initial + coeffQ θ q * (q : ENNReal) / 2 ^ 128 := hbank
      _ ≤ psi θ q LargeResidual.RouterState.initial + (S + coeffQ θ q * Mass / 2 ^ 128) := add_le_add le_rfl hmass
      _ = _ := by ring
  have hpsi := (ENNReal.add_le_add_iff_right hSfin).mp hkey
  calc
    _ ≤ expectedValue L (psiOut θ q) := hcert
    _ ≤ psi θ q LargeResidual.RouterState.initial + coeffQ θ q * Mass / 2 ^ 128 := hpsi
    _ ≤ _ := add_le_add (psi_initial θ q rate hexc) le_rfl

end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord WCoord)
open ClaudeWCT.W9.T3.Security.FamResidual (lazyRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable

theorem budgetRate_ge_one (q : Nat) (hq : q≤2^127) : 1≤Flexible.budgetRate q := by
  have hqr : (q:ℝ)≤2^127 := by exact_mod_cast hq
  have hm : 2*(q:ℝ)≤(2:ℝ)^128 := calc
    _ ≤ 2*2^127 := mul_le_mul_of_nonneg_left hqr (by norm_num)
    _ = _ := by norm_num
  have hdiv := (div_le_one (by positivity : (0:ℝ)<2^128)).2 hm
  unfold Flexible.budgetRate
  linarith

theorem coeffQ_budgetRate (q : Nat) (hq:q≤2^127) :
    coeffQ (ENNReal.ofReal (Flexible.budgetRate q-1/1024)) q = ENNReal.ofReal (Flexible.budgetRate q) := by
  have h:=budgetRate_ge_one q hq
  unfold coeffQ
  change ENNReal.ofReal (Flexible.budgetRate q-1/1024)+(1/1024:ENNReal)=_
  rw [show (1/1024:ENNReal)=ENNReal.ofReal (1/1024:ℝ) by rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num,
    ←ENNReal.ofReal_add (by linarith : 0≤Flexible.budgetRate q-1/1024) (by positivity)]
  congr 1
  ring

theorem contact_cert_bound_of_excess (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (rate : ENNReal)
    (hexc : ClaudeWCT.Numerics.Law.lawAvg ClaudeWCT.Bank.Paired.honestLaw (2^32)
      (fun W=>ClaudeWCT.Bank.Paired.price W-ENNReal.ofReal (Flexible.budgetRate q-1/1024))≤rate) :
    Pr[ContactNO adversary q | PairedSeccLaw.completedExperiment adversary q hq] +
      Pr[fun z=>CertR adversary q (QueryRecorded.recordedTrace z.1) z.2 ∧
        NoOvR adversary (QueryRecorded.recordedTrace z.1) z.2 |
        PairedSeccLaw.completedExperiment adversary q hq] ≤
      ENNReal.ofReal (2*((q:ℝ)/2^128)-((q:ℝ)/2^128)^2)+(q:ENNReal)*rate/2^128+
        ((2 ^ 142 : ℝ≥0∞)⁻¹+(2 ^ 142 : ℝ≥0∞)⁻¹) := by
  have hb := bank_cert_le (ENNReal.ofReal (Flexible.budgetRate q-1/1024))
    (Wots.PairedReference.Ref.referenceInputs_universe adversary) initLaw adversary q (by finiteness) rate hexc
  rw [coeffQ_budgetRate q hq] at hb
  have hp := Flexible.residual_potential_rate (Flexible.budgetRate q) (auxLaw initLaw) q hq
    (Flexible.budgetRate_nonneg q hq) (Flexible.budgetRate_mul q).le
    (router (Wots.PairedReference.referenceInputs adversary) adversary q)
  have h:=add_le_add (contact_le_lazy adversary q hq) ((cert_le_lazy adversary q hq).trans (add_le_add hb le_rfl))
  have hsum : ∀a b c e : ENNReal,(a+e)+((b+c)+e)=((a+c)+b)+(e+e) := by intros;ring
  rw [hsum] at h
  exact h.trans (add_le_add (add_le_add hp le_rfl) le_rfl)

end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
end
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_CaseCNearSearch ====
section

section





section
namespace ClaudeWCT.W9.T3.Security.CaseC
open Finset ENNReal
open ClaudeWCT.Numerics.Thinning (ListCovExcept nearEnv)
open SigGolfResearch.Gate6.Moments (finiteAverage)
open SigGolfCandidate.T3.BPORS.History (atIndex)
open SigGolfCandidate.T3 (HashOutput)
open ClaudeWCT.Bank.WCT (WProposal proposal outIdx SlotCoveredP)
open ClaudeWCT.WCT9 (wordDigit Child)
open ClaudeWCT.Guess (nearScore nearPrice NearCoveredAt)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
theorem guess_slotCovered_iff (X : List HashOutput) (N : HashOutput) (k : Fin 9) (t : Fin 6) :
    ClaudeWCT.Guess.SlotCovered X N k t ↔ ClaudeWCT.Bank.WCT.SlotCovered X N k t := by
  unfold ClaudeWCT.Guess.SlotCovered ClaudeWCT.Bank.WCT.SlotCovered
  refine exists_congr fun x => and_congr Iff.rfl (and_congr ?_ Iff.rfl)
  simp only [outIdx, Fin.mk.injEq]
theorem slotCoveredP_iff_atIndex (W : List WProposal) (N : HashOutput) (k : Fin 9) (t : Fin 6) :
    SlotCoveredP W N k t ↔
      ∃ e ∈ atIndex (outIdx N) W, (e k).1 = ((proposal N).2 k).1 ∧
        wordDigit ((proposal N).2 k).2 t ≤ wordDigit (e k).2 t := by
  constructor
  · rintro ⟨p, hp, h1, h2, h3⟩
    refine ⟨p.2, (ClaudeWCT.Numerics.WCTEnvelope.mem_atIndex _ _ _).mpr ?_, h2, h3⟩
    rw [← h1]
    exact hp
  · rintro ⟨e, he, h2, h3⟩
    exact ⟨(outIdx N, e), (ClaudeWCT.Numerics.WCTEnvelope.mem_atIndex _ _ _).mp he, rfl, h2, h3⟩
theorem nearCoveredAt_iff (X : List HashOutput) (N : HashOutput) (k : Fin 9) (t : Fin 6) :
    NearCoveredAt X N k t ↔
      ListCovExcept wordDigit k t (atIndex (outIdx N) (X.map proposal)) (proposal N).2 := by
  unfold NearCoveredAt ListCovExcept
  refine forall_congr' fun k' => forall_congr' fun t' => imp_congr_right fun _ => ?_
  rw [guess_slotCovered_iff, ClaudeWCT.Bank.WCT.slotCovered_iff, slotCoveredP_iff_atIndex]
noncomputable abbrev nearPriceP (W : List WProposal) : ENNReal :=
  ClaudeWCT.Numerics.N600.nearPriceN (C := Child) wordDigit W
theorem nearPrice_eq_nearPriceP (X : List HashOutput) :
    nearPrice X = nearPriceP (X.map proposal) := by
  classical
  set W : List WProposal := X.map proposal with hW
  set g : WProposal → ENNReal := fun p => ∑ k : Fin 9, ∑ t : Fin 6,
    if ListCovExcept wordDigit k t (atIndex p.1 W) p.2 then 1 else 0 with hg
  have hs : ∀ N, nearScore X N = if ClaudeWCT.WCT9.admissible N = true then g (proposal N) else 0 := by
    intro N
    unfold nearScore
    by_cases hadm : ClaudeWCT.WCT9.admissible N = true
    · simp only [hadm, if_true, hg]
      exact sum_congr rfl fun k _ => sum_congr rfl fun t _ =>
        if_congr (nearCoveredAt_iff X N k t) rfl rfl
    · simp [hadm]
  have hsum : ∑ p, g p = ((ClaudeWCT.Numerics.N600.Q ^ 9 : ℕ) : ENNReal) *
      ∑ index : Fin (2 ^ 31), ∑ k : Fin 9, ∑ t : Fin 6, nearEnv wordDigit k t (atIndex index W) := by
    simp only [hg]
    rw [Fintype.sum_prod_type, mul_sum]
    refine sum_congr rfl fun index _ => ?_
    rw [Finset.sum_comm, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm, mul_sum]
    refine sum_congr rfl fun t _ => ?_
    unfold nearEnv finiteAverage
    rw [ClaudeWCT.Numerics.WCTEnvelope.card_coords,
      ENNReal.mul_div_cancel (by simp [ClaudeWCT.Numerics.N600.Q]) (by simp)]
  unfold nearPrice SigGolfCandidate.T3.BPORS.finiteAverage
  simp_rw [hs]
  rw [ClaudeWCT.Bank.WCT.sum_admissible g, hsum, Fintype.card_bitVec, nearPriceP,
    ClaudeWCT.Numerics.N600.nearPriceN, ← ClaudeWCT.Numerics.WCTEnvelope.price_scale]
  unfold ClaudeWCT.WCT9.gateLimit
  simp only [div_eq_mul_inv]
  ring
theorem near_bound_add_charge : (4799 / 16 : ENNReal) + 1 / 16 = 300 := by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num [ENNReal.toReal_div]
theorem near_bound_eq_sub : (4799 / 16 : ENNReal) = 300 - 1 / 16 := by
  rw [← near_bound_add_charge]
  exact (ENNReal.add_sub_cancel_right (by finiteness)).symm
theorem wct_near_bound_2_32 :
    ClaudeWCT.Numerics.Law.lawAvg ClaudeWCT.Bank.WCT.honestLaw (2 ^ 32) nearPriceP ≤ 4799 / 16 := by
  rw [near_bound_eq_sub, ClaudeWCT.Bank.WCT.honestLaw_eq_n4]
  exact ClaudeWCT.Numerics.WCTPrice.wct_near_honest_2_32
end ClaudeWCT.W9.T3.Security.CaseC
end
section
namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.CaseC (BankCore BankCore.expose expectedValue_add_const_le
  pmf_expectedValue_left_mul expectedValue_list_sum' finiteAverage_expectedValue)
open SphincsSecurity.Concrete (independentProposalWord uniformWordAverage)
open ClaudeWCT.Bank.WCT (WProposal)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable abbrev nearSpec : ClaudeWCT.Bank.FtsBankSpec WProposal := bankSpec.toFtsBankSpec
theorem nearSpec_law : nearSpec.law = ClaudeWCT.Bank.WCT.honestLaw := rfl
theorem nearPrice_proposals (X : List HashOutput) :
    Guess.nearPrice X = nearPriceP (nearSpec.proposals X) :=
  nearPrice_eq_nearPriceP X
noncomputable def nearForecast (R : Nat) (X : List HashOutput) (N : HashOutput) : ENNReal :=
  expectedValue (independentProposalWord nearSpec.accepted R) (fun F => Guess.nearScore (X ++ F) N)
theorem nearForecast_step (R : Nat) (X : List HashOutput) (N : HashOutput) :
    expectedValue nearSpec.accepted (fun A => nearForecast R (X ++ [A]) N) = nearForecast (R + 1) X N := by
  unfold nearForecast
  rw [independentProposalWord, ← PMF.monad_bind_eq_bind, expectedValue_bind]
  apply congrArg
  funext A
  rw [← PMF.monad_map_eq_map, expectedValue_map]
  apply congrArg
  funext F
  simp only [List.append_assoc, List.singleton_append]
theorem nearScore_le_forecast (R : Nat) (X : List HashOutput) (N : HashOutput) :
    Guess.nearScore X N ≤ nearForecast R X N := by
  unfold nearForecast
  calc
    Guess.nearScore X N = expectedValue (independentProposalWord nearSpec.accepted R) (fun _ => Guess.nearScore X N) :=
      (expectedValue_const (by simp) _).symm
    _ ≤ _ := expectedValue_mono _ fun F => Guess.nearScore_append_mono X F N
noncomputable def nearPriceForecast (R : Nat) (X : List HashOutput) : ENNReal :=
  ClaudeWCT.Numerics.Law.lawAvg nearSpec.law R (fun W => nearPriceP (nearSpec.proposals X ++ W))
theorem average_nearForecast (R : Nat) (X : List HashOutput) :
    BPORS.finiteAverage (fun N : HashOutput => nearForecast R X N) = nearPriceForecast R X / 2 ^ 128 := by
  unfold nearForecast nearPriceForecast
  rw [finiteAverage_expectedValue]
  have hav : ∀ F : List HashOutput, BPORS.finiteAverage (fun N : HashOutput => Guess.nearScore (X ++ F) N) =
      nearPriceP (nearSpec.proposals X ++ nearSpec.proposals F) / 2 ^ 128 := by
    intro F
    rw [Guess.average_nearScore, nearPrice_proposals, nearSpec.proposals_append]
  simp_rw [hav]
  refine (nearSpec.expected_word_proposals R
    (fun W => nearPriceP (nearSpec.proposals X ++ W) / 2 ^ 128)).trans ?_
  simp only [div_eq_mul_inv]
  rw [show (fun W => nearPriceP (nearSpec.proposals X ++ W) * (2 ^ 128 : ENNReal)⁻¹) =
      fun W => (2 ^ 128 : ENNReal)⁻¹ * nearPriceP (nearSpec.proposals X ++ W) by
    funext W; exact mul_comm _ _, ClaudeWCT.Numerics.Law.lawAvg_mul_left, mul_comm]
theorem nearPriceForecast_step (R : Nat) (X : List HashOutput) :
    expectedValue nearSpec.accepted (fun A => nearPriceForecast R (X ++ [A])) = nearPriceForecast (R + 1) X := by
  unfold nearPriceForecast
  rw [ClaudeWCT.Numerics.Law.lawAvg_succ]
  have hA (A : HashOutput) : ClaudeWCT.Numerics.Law.lawAvg nearSpec.law R
      (fun W => nearPriceP (nearSpec.proposals (X ++ [A]) ++ W)) =
      (fun p : WProposal => ClaudeWCT.Numerics.Law.lawAvg nearSpec.law R
        (fun W => nearPriceP (nearSpec.proposals X ++ p :: W))) (nearSpec.proposal A) := by
    simp [ClaudeWCT.Bank.FtsBankSpec.proposals, List.map_append, List.append_assoc]
  simp_rw [hA]
  exact nearSpec.expected_accepted_proposal (fun p => ClaudeWCT.Numerics.Law.lawAvg nearSpec.law R
    (fun W => nearPriceP (nearSpec.proposals X ++ p :: W)))
noncomputable def nearLedger (R : Nat) (targets X : List HashOutput) (slack : Nat) : ENNReal :=
  (targets.map fun N => nearForecast R X N).sum + (slack : ENNReal) * nearPriceForecast R X / 2 ^ 128
theorem nearLedger_slack_succ (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    nearLedger R targets X (slack + 1) = nearLedger R targets X slack + nearPriceForecast R X / 2 ^ 128 := by
  unfold nearLedger
  rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, ENNReal.add_div, add_assoc]
theorem nearLedger_birth (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun a => nearLedger R (targets ++ [a]) X slack) =
      nearLedger R targets X (slack + 1) := by
  have hfa : expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun a => nearForecast R X a) =
      nearPriceForecast R X / 2 ^ 128 := by
    rw [BPORS.expected_uniform_eq_finiteAverage]
    exact average_nearForecast R X
  have hsplit : ∀ a, nearLedger R (targets ++ [a]) X slack = nearLedger R targets X slack + nearForecast R X a := by
    intro a
    simp only [nearLedger, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
      List.sum_nil, add_zero]
    ring
  simp_rw [hsplit]
  rw [expectedValue_add, expectedValue_const (by simp : Pr[⊥ | ($ᵗ HashOutput : ProbComp HashOutput)] = 0), hfa,
    nearLedger_slack_succ]
theorem nearLedger_expose (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    expectedValue nearSpec.accepted (fun A => nearLedger R targets (X ++ [A]) slack) =
      nearLedger (R + 1) targets X slack := by
  unfold nearLedger
  rw [expectedValue_add, expectedValue_list_sum']
  refine congrArg₂ (· + ·) ?_ ?_
  · refine congrArg List.sum ?_
    apply List.map_congr_left
    intro N _
    exact nearForecast_step R X N
  · simp only [div_eq_mul_inv]
    rw [show (fun A : HashOutput => (slack : ENNReal) * nearPriceForecast R (X ++ [A]) * (2 ^ 128 : ENNReal)⁻¹) =
        fun A => (slack : ENNReal) * (2 ^ 128 : ENNReal)⁻¹ * nearPriceForecast R (X ++ [A]) by
      funext A; ring]
    rw [pmf_expectedValue_left_mul, nearPriceForecast_step]
    ring
theorem nearLedger_freshPrice (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    nearSpec.freshPrice (fun A => nearLedger R targets (X ++ [A]) slack) = nearLedger (R + 1) targets X slack := by
  rw [← nearSpec.expected_accepted, nearLedger_expose]
theorem nearLedger_search (secret : BitVec 256) (rho : Digest) (message : Message) (fuel : Nat)
    (hlimit : fuel ≤ 2 ^ 32) (cache : Sampling.RCache)
    (hreject : Sampling.CachedTrialsReject (Sampling.digestTrial rho message) nearSpec.decode 0 (2 ^ 32) cache)
    (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    expectedValue (Sampling.roRun secret (nearSpec.search rho message 0 fuel) cache)
      (fun result => result.1.elim (nearLedger (R + 1) targets X slack)
        (fun found => nearLedger R targets (X ++ [found.2]) slack)) ≤ nearLedger (R + 1) targets X slack :=
  nearSpec.search_le_price secret rho message fuel hlimit cache hreject _ _ _ le_rfl
    (nearLedger_freshPrice R targets X slack).le
theorem nearLedger_win (R : Nat) (targets X : List HashOutput) (slack : Nat) (N : HashOutput) (hN : N ∈ targets)
    (hadm : WCT9.admissible N = true) (hcov : Guess.NearCoveredBy X N) : 1 ≤ nearLedger R targets X slack :=
  calc
    (1 : ENNReal) ≤ Guess.nearScore X N := Guess.one_le_nearScore hadm hcov
    _ ≤ nearForecast R X N := nearScore_le_forecast R X N
    _ ≤ (targets.map fun N => nearForecast R X N).sum := List.le_sum_of_mem (List.mem_map_of_mem hN)
    _ ≤ _ := le_self_add
theorem nearLedger_initial (budget : Nat) :
    nearLedger horizon [] [] budget ≤ (budget : ENNReal) * (4799 / 16) / 2 ^ 128 := by
  unfold nearLedger nearPriceForecast
  simp only [List.map_nil, List.sum_nil, zero_add]
  apply ENNReal.div_le_div_right
  apply mul_le_mul' le_rfl
  rw [nearSpec_law]
  exact wct_near_bound_2_32
noncomputable def nearPotential (b : BankCore) : ENNReal :=
  if horizon < b.exposures.length then 0
  else if b.reused = true then 1 + b.reuse
  else nearLedger (horizon - b.exposures.length) b.targets b.exposures b.slack + b.reuse
theorem expected_admInd_sixteenth :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput) nearSpec.admInd ≤ 1 / 16 :=
  nearSpec.expected_admInd_tight.trans (ENNReal.div_le_div_left (by norm_num) 1)
theorem near_birth (b : BankCore) (s : Nat) (hs : b.slack = s + 1) (C' : HashOutput → ENNReal)
    (hC : ∀ N, C' N ≤ b.reuse + nearSpec.admInd N / 2 ^ 128) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
        (fun N => nearPotential { b with targets := b.targets ++ [N], slack := s, reuse := C' N }) ≤
      nearPotential b + (1 / 16) / 2 ^ 128 := by
  have hadm : expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun N => nearSpec.admInd N / 2 ^ 128) ≤
      (1 / 16) / 2 ^ 128 := by
    simp only [div_eq_mul_inv]
    rw [expectedValue_mul_const]
    exact mul_le_mul' (by simpa [div_eq_mul_inv] using expected_admInd_sixteenth) le_rfl
  unfold nearPotential
  simp only
  by_cases hd : horizon < b.exposures.length
  · simp only [hd, if_true]
    exact (expectedValue_le_of_le _ fun _ => le_rfl).trans bot_le
  simp only [hd, if_false]
  by_cases hr : b.reused = true
  · simp only [hr, if_true]
    calc
      _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
          (fun N => nearSpec.admInd N / 2 ^ 128 + (1 + b.reuse)) :=
        expectedValue_mono _ fun N => (add_le_add le_rfl (hC N)).trans (le_of_eq (by ring))
      _ ≤ (1 / 16) / 2 ^ 128 + (1 + b.reuse) := (expectedValue_add_const_le _ _ _).trans (add_le_add hadm le_rfl)
      _ = _ := add_comm _ _
  · simp only [hr, Bool.false_eq_true, if_false]
    set R := horizon - b.exposures.length
    calc
      _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
          (fun N => (nearLedger R (b.targets ++ [N]) b.exposures s + nearSpec.admInd N / 2 ^ 128) + b.reuse) :=
        expectedValue_mono _ fun N => (add_le_add le_rfl (hC N)).trans (le_of_eq (by ring))
      _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
          (fun N => nearLedger R (b.targets ++ [N]) b.exposures s + nearSpec.admInd N / 2 ^ 128) + b.reuse :=
        expectedValue_add_const_le _ _ _
      _ ≤ (nearLedger R b.targets b.exposures (s + 1) + (1 / 16) / 2 ^ 128) + b.reuse := by
        rw [expectedValue_add, nearLedger_birth]
        exact add_le_add (add_le_add le_rfl hadm) le_rfl
      _ = _ := by
        rw [hs]
        ring
theorem near_sign (b : BankCore) (cache : Sampling.RCache) (m : Message) (C' : ENNReal)
    (hC : C' + nearSpec.reuseMass cache m ≤ b.reuse) (secret : BitVec 256) (fuel : Nat) (hfuel : fuel ≤ 2 ^ 32) :
    expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho =>
      if nearSpec.Reuse cache rho m then nearPotential { b with reused := true, reuse := C' }
      else expectedValue (Sampling.roRun secret (nearSpec.search rho m 0 fuel) cache)
        (fun result => nearPotential (b.expose C' (result.1.map Prod.snd)))) ≤ nearPotential b := by
  have hlenA : ∀ (o : Option HashOutput), b.exposures.length ≤ (b.exposures ++ o.toList).length := by
    intro o; simp
  by_cases hd : horizon < b.exposures.length
  · apply expectedValue_le_of_le
    intro rho
    have h0 : ∀ (o : Option HashOutput), nearPotential (b.expose C' o) = 0 := by
      intro o
      unfold nearPotential BankCore.expose
      simp only
      rw [if_pos (lt_of_lt_of_le hd (hlenA o))]
    split_ifs
    · unfold nearPotential; simp only; rw [if_pos hd]; exact bot_le
    · exact (expectedValue_le_of_le _ fun result => (h0 _).le).trans bot_le
  by_cases hr : b.reused = true
  · have hb : nearPotential b = 1 + b.reuse := by unfold nearPotential; simp [hd, hr]
    rw [hb]
    apply expectedValue_le_of_le
    intro rho
    have hle : ∀ (o : Option HashOutput), nearPotential (b.expose C' o) ≤ 1 + b.reuse := by
      intro o
      unfold nearPotential BankCore.expose
      simp only [hr, if_true]
      split_ifs
      · exact bot_le
      · exact add_le_add le_rfl (le_of_add_le_left hC)
    split_ifs
    · unfold nearPotential; simp only [hd, if_false, if_true]; exact add_le_add le_rfl (le_of_add_le_left hC)
    · exact expectedValue_le_of_le _ fun result => hle _
  have hr' : b.reused = false := by simpa using hr
  set R0 := horizon - b.exposures.length with hR0
  have hb : nearPotential b = nearLedger R0 b.targets b.exposures b.slack + b.reuse := by
    unfold nearPotential; simp only [hd, hr', if_false, Bool.false_eq_true]; rfl
  have hsearch : ∀ rho, ¬nearSpec.Reuse cache rho m →
      expectedValue (Sampling.roRun secret (nearSpec.search rho m 0 fuel) cache)
        (fun result => nearPotential (b.expose C' (result.1.map Prod.snd))) ≤
          nearLedger R0 b.targets b.exposures b.slack + C' := by
    intro rho hnr
    have hrej : Sampling.CachedTrialsReject (Sampling.digestTrial rho m) nearSpec.decode 0 (2 ^ 32) cache := by
      unfold ClaudeWCT.Bank.FtsBankSpec.Reuse at hnr; push Not at hnr; exact hnr
    by_cases hlen : b.exposures.length < horizon
    · obtain ⟨R, hR⟩ : ∃ R, R0 = R + 1 := ⟨R0 - 1, by omega⟩
      calc
        _ ≤ expectedValue (Sampling.roRun secret (nearSpec.search rho m 0 fuel) cache)
            (fun result => result.1.elim (nearLedger (R + 1) b.targets b.exposures b.slack)
              (fun found => nearLedger R b.targets (b.exposures ++ [found.2]) b.slack) + C') := by
          apply expectedValue_mono
          intro result
          rcases result with ⟨_ | found, cache'⟩
          · unfold nearPotential BankCore.expose
            simp only [Option.map_none, Option.toList_none, List.append_nil, hd, if_false, hr',
              Bool.false_eq_true, Option.elim_none]
            rw [← hR]
          · unfold nearPotential BankCore.expose
            have hnd : ¬horizon < (b.exposures ++ [found.2]).length := by simp; omega
            simp only [Option.map_some, Option.toList_some, hnd, if_false, hr', Bool.false_eq_true,
              Option.elim_some]
            rw [show horizon - (b.exposures ++ [found.2]).length = R by simp; omega]
        _ ≤ nearLedger (R + 1) b.targets b.exposures b.slack + C' :=
          (expectedValue_add_const_le _ _ _).trans
            (add_le_add (nearLedger_search secret rho m fuel hfuel cache hrej R b.targets b.exposures b.slack) le_rfl)
        _ = _ := by rw [hR]
    · apply expectedValue_le_of_le
      intro result
      rcases result with ⟨_ | found, cache'⟩
      · unfold nearPotential BankCore.expose
        simp only [Option.map_none, Option.toList_none, List.append_nil, hd, if_false, hr', Bool.false_eq_true]
        exact le_rfl
      · unfold nearPotential BankCore.expose
        have hnd : horizon < (b.exposures ++ [found.2]).length := by simp; omega
        simp only [Option.map_some, Option.toList_some, hnd, if_true]
        exact bot_le
  rw [hb]
  calc
    _ ≤ expectedValue ($ᵗ Digest : ProbComp Digest)
        (fun rho => (if nearSpec.Reuse cache rho m then 1 else 0) + (nearLedger R0 b.targets b.exposures b.slack + C')) := by
      apply expectedValue_mono
      intro rho
      by_cases hre : nearSpec.Reuse cache rho m
      · rw [if_pos hre, if_pos hre]
        unfold nearPotential
        simp only [hd, if_false, if_true]
        exact add_le_add le_rfl le_add_self
      · rw [if_neg hre, if_neg hre, zero_add]
        exact hsearch rho hre
    _ ≤ nearSpec.reuseMass cache m + (nearLedger R0 b.targets b.exposures b.slack + C') :=
      (expectedValue_add_const_le _ _ _).trans (add_le_add (nearSpec.reuse_probability_le cache m) le_rfl)
    _ ≤ _ := by
      rw [add_comm (nearLedger _ _ _ _), ← add_assoc, add_comm (nearSpec.reuseMass cache m),
        add_comm _ (nearLedger _ _ _ _)]
      exact add_le_add le_rfl hC
theorem near_win (b : BankCore) (halive : ¬horizon < b.exposures.length)
    (h : b.reused = true ∨ ∃ N ∈ b.targets, WCT9.admissible N = true ∧ Guess.NearCoveredBy b.exposures N) :
    1 ≤ nearPotential b := by
  unfold nearPotential
  rw [if_neg halive]
  by_cases hr : b.reused = true
  · rw [if_pos hr]; exact le_self_add
  · rw [if_neg hr]
    obtain ⟨N, hN, hadm, hcov⟩ := h.resolve_left hr
    exact (nearLedger_win _ _ _ _ N hN hadm hcov).trans le_self_add
theorem near_initial (budget : Nat) :
    nearPotential ⟨[], [], false, 0, budget⟩ ≤ (budget : ENNReal) * (4799 / 16) / 2 ^ 128 := by
  unfold nearPotential
  simp only [List.length_nil, Nat.not_lt_zero, if_false, Bool.false_eq_true, Nat.sub_zero, add_zero]
  exact nearLedger_initial budget
end ClaudeWCT.W9.T3.Security.CaseC
end
end

section


section
namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.CaseC (BankCore BankCore.expose expectedValue_add_const_le DigestRowOf
  digestRowOf_unique tsum_indicator_le_of_subsingleton)
open SphincsSecurity.Completeness (searchLoop)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable def reuseC (rows : Sampling.RCache) (nonces : Message → Option Digest) : ENNReal :=
  ∑' m : Message, if nonces m = none then nearSpec.reuseMass rows m else 0
theorem reuseC_birth_le (rows : Sampling.RCache) (nonces : Message → Option Digest) (x : HashInput) (a : HashOutput)
    (hx : rows x = none) : reuseC (rows.cacheQuery x a) nonces ≤ reuseC rows nonces + nearSpec.admInd a / 2 ^ 128 := by
  unfold reuseC
  calc
    (∑' m : Message, if nonces m = none then nearSpec.reuseMass (rows.cacheQuery x a) m else 0) ≤
        ∑' m : Message, ((if nonces m = none then nearSpec.reuseMass rows m else 0) +
          (if DigestRowOf x m then nearSpec.admInd a / 2 ^ 128 else 0)) := by
      apply ENNReal.tsum_le_tsum
      intro m
      split_ifs with h1 h2
      · simpa [ENNReal.div_eq_inv_mul, h2] using nearSpec.reuseMass_cacheQuery_le rows x a hx m
      · simpa [h2] using nearSpec.reuseMass_cacheQuery_le rows x a hx m
      · exact bot_le
      · exact bot_le
    _ = _ + _ := ENNReal.tsum_add
    _ ≤ _ := add_le_add le_rfl (tsum_indicator_le_of_subsingleton _ (fun _ _ h h' => digestRowOf_unique h h') _)
theorem reuseC_sign_le (rows rows' : Sampling.RCache) (nonces : Message → Option Digest) (m : Message) (v : Digest)
    (hm : nonces m = none) (hrows : ∀ m', m' ≠ m → nearSpec.reuseMass rows' m' = nearSpec.reuseMass rows m') :
    reuseC rows' (Function.update nonces m (some v)) + nearSpec.reuseMass rows m ≤ reuseC rows nonces := by
  unfold reuseC
  rw [ENNReal.tsum_eq_add_tsum_ite m, ENNReal.tsum_eq_add_tsum_ite m (f := fun m' =>
    if nonces m' = none then nearSpec.reuseMass rows m' else 0)]
  simp only [Function.update_self, reduceCtorEq, if_false, zero_add, hm, if_true]
  rw [add_comm]
  apply add_le_add le_rfl
  apply le_of_eq
  apply tsum_congr
  intro m'
  by_cases he : m' = m
  · simp [he]
  · simp only [he, if_false, Function.update_of_ne he, hrows m' he]
theorem reuseC_signed_eq (rows rows' : Sampling.RCache) (nonces : Message → Option Digest) (m : Message)
    (hm : nonces m ≠ none) (hrows : ∀ m', m' ≠ m → nearSpec.reuseMass rows' m' = nearSpec.reuseMass rows m') :
    reuseC rows' nonces = reuseC rows nonces := by
  unfold reuseC
  apply tsum_congr
  intro m'
  by_cases he : m' = m
  · subst he; simp [hm]
  · simp only [hrows m' he]
theorem search_cache_frame {β γ : Type} (secret : BitVec 256) (inputs : Nat → HashInput)
    (decoder : HashOutput → Option β) (result : Nat → β → γ) :
    ∀ fuel counter (cache : Sampling.RCache) r,
      r ∈ support (Sampling.roRun secret
        (Sampling.publicProgram (searchLoop inputs decoder (fun c v => pure (result c v)) fuel counter)) cache) →
      ∀ y, (∀ k, y ≠ inputs k) → r.2 y = cache y := by
  intro fuel
  induction fuel with
  | zero =>
      intro counter cache r hr y _
      simp only [searchLoop, Sampling.publicProgram, simulateQ_pure] at hr
      change r ∈ support (Sampling.roRun secret (pure none) cache) at hr
      rw [Sampling.roRun_pure, support_pure, Set.mem_singleton_iff] at hr
      rw [hr]
  | succ fuel ih =>
      intro counter cache r hr y hy
      rw [Sampling.publicSearch_succ, Sampling.roRun_bind, Sampling.roRun_publicQuery, mem_support_bind_iff] at hr
      obtain ⟨first, hfirst, hr⟩ := hr
      have hfc : first.2 y = cache y := by
        rw [randomOracle.run_eq] at hfirst
        cases hc : cache (inputs counter) with
        | some a =>
            rw [hc, support_pure, Set.mem_singleton_iff] at hfirst
            rw [hfirst]
        | none =>
            rw [hc, mem_support_bind_iff] at hfirst
            obtain ⟨a, -, hfa⟩ := hfirst
            rw [support_pure, Set.mem_singleton_iff] at hfa
            rw [hfa]
            exact QueryCache.cacheQuery_of_ne cache a (hy counter)
      cases hd : decoder first.1 with
      | none =>
          rw [hd] at hr
          exact (ih (counter + 1) first.2 r hr y hy).trans hfc
      | some value =>
          rw [hd] at hr
          change r ∈ support (Sampling.roRun secret (pure _) first.2) at hr
          rw [Sampling.roRun_pure, support_pure, Set.mem_singleton_iff] at hr
          rw [hr]
          exact hfc
theorem digestSearch_cache_frame (secret : BitVec 256) (rho : Digest) (m : Message) (fuel : Nat)
    (cache : Sampling.RCache) (r) (hr : r ∈ support (Sampling.roRun secret (nearSpec.search rho m 0 fuel) cache)) :
    ∀ y, (∀ k, y ≠ Sampling.digestTrial rho m k) → r.2 y = cache y := by
  unfold ClaudeWCT.Bank.FtsBankSpec.search at hr
  exact search_cache_frame secret (Sampling.digestTrial rho m) nearSpec.decode _ fuel 0 cache r hr
theorem digestTrial_ne_of_message {rho rho' : Digest} {m m' : Message} (hm : m' ≠ m) (c c' : Nat)
    (hc' : c' < 2 ^ 32) : Sampling.digestTrial rho' m' c' ≠ Sampling.digestTrial rho m c := by
  intro he
  have h1 : DigestRowOf (Sampling.digestTrial rho' m' c') m' := ⟨(rho', ⟨c', hc'⟩), rfl⟩
  have h2 : DigestRowOf (Sampling.digestTrial rho m (c % 2 ^ 32)) m :=
    ⟨(rho, ⟨c % 2 ^ 32, Nat.mod_lt _ (by decide)⟩), rfl⟩
  have h3 : Sampling.digestTrial rho m (c % 2 ^ 32) = Sampling.digestTrial rho m c := by
    unfold Sampling.digestTrial
    congr 2
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofNat]
  rw [h3, ← he] at h2
  exact hm (digestRowOf_unique h1 h2)
theorem digestSearch_reuseMass (secret : BitVec 256) (rho : Digest) (m : Message) (fuel : Nat)
    (cache : Sampling.RCache) (r) (hr : r ∈ support (Sampling.roRun secret (nearSpec.search rho m 0 fuel) cache)) :
    ∀ m', m' ≠ m → nearSpec.reuseMass r.2 m' = nearSpec.reuseMass cache m' := by
  intro m' hm
  unfold ClaudeWCT.Bank.FtsBankSpec.reuseMass ClaudeWCT.Bank.FtsBankSpec.admissibleEntry
  congr 1
  apply tsum_congr
  intro p
  rw [digestSearch_cache_frame secret rho m fuel cache r hr _
    (fun k => digestTrial_ne_of_message hm k p.2.val p.2.isLt)]
noncomputable def nearMemPotential (q : Nat) (births exposures : List HashOutput) (reused : Bool)
    (rows : Sampling.RCache) (nonces : Message → Option Digest) : ENNReal :=
  if q < births.length then 0
  else nearPotential ⟨births, exposures, reused, reuseC rows nonces, q - births.length⟩ +
    ((q - births.length : Nat) : ENNReal) * ((1 / 16) / 2 ^ 128)
theorem mem_birth (q : Nat) (births exposures : List HashOutput) (reused : Bool) (rows : Sampling.RCache)
    (nonces : Message → Option Digest) (x : HashInput) (hx : rows x = none) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
        (fun a : HashOutput => nearMemPotential q (births ++ [a]) exposures reused (rows.cacheQuery x a) nonces) ≤
      nearMemPotential q births exposures reused rows nonces := by
  by_cases hq : births.length < q
  · obtain ⟨s, hs⟩ : ∃ s, q - births.length = s + 1 := ⟨q - births.length - 1, by omega⟩
    have hb : nearMemPotential q births exposures reused rows nonces =
        nearPotential ⟨births, exposures, reused, reuseC rows nonces, s + 1⟩ + ((s + 1 : Nat) : ENNReal) *
          ((1 / 16) / 2 ^ 128) := by
      unfold nearMemPotential
      rw [if_neg (by omega), hs]
    have ha : ∀ a : HashOutput, nearMemPotential q (births ++ [a]) exposures reused (rows.cacheQuery x a) nonces =
        nearPotential { (⟨births, exposures, reused, reuseC rows nonces, s + 1⟩ : BankCore) with
          targets := births ++ [a], slack := s, reuse := reuseC (rows.cacheQuery x a) nonces } +
          (s : ENNReal) * ((1 / 16) / 2 ^ 128) := by
      intro a
      unfold nearMemPotential
      have hl : (births ++ [a]).length = births.length + 1 := by simp
      rw [if_neg (by omega), show q - (births ++ [a]).length = s by omega]
    simp_rw [ha]
    rw [hb]
    calc
      _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun a =>
            nearPotential { (⟨births, exposures, reused, reuseC rows nonces, s + 1⟩ : BankCore) with
              targets := births ++ [a], slack := s, reuse := reuseC (rows.cacheQuery x a) nonces }) +
          (s : ENNReal) * ((1 / 16) / 2 ^ 128) := expectedValue_add_const_le _ _ _
      _ ≤ (nearPotential ⟨births, exposures, reused, reuseC rows nonces, s + 1⟩ + (1 / 16) / 2 ^ 128) +
          (s : ENNReal) * ((1 / 16) / 2 ^ 128) := by
        apply add_le_add _ le_rfl
        exact near_birth ⟨births, exposures, reused, reuseC rows nonces, s + 1⟩ s rfl _
          (fun a => reuseC_birth_le rows nonces x a hx)
      _ = _ := by
        push_cast
        ring
  · apply expectedValue_le_of_le
    intro a
    unfold nearMemPotential
    rw [if_pos (by simp; omega)]
    exact bot_le
theorem mem_sign_fresh (q : Nat) (births exposures : List HashOutput) (reused : Bool) (rows : Sampling.RCache)
    (nonces : Message → Option Digest) (m : Message) (hm : nonces m = none) (secret : BitVec 256) (fuel : Nat)
    (hfuel : fuel ≤ 2 ^ 32) :
    expectedValue ($ᵗ Digest : ProbComp Digest) (fun v =>
      expectedValue (Sampling.roRun secret (nearSpec.search v m 0 fuel) rows) (fun r =>
        nearMemPotential q births (exposures ++ (r.1.map Prod.snd).toList)
          (reused || decide (nearSpec.Reuse rows v m)) r.2 (Function.update nonces m (some v)))) ≤
      nearMemPotential q births exposures reused rows nonces := by
  by_cases hq : q < births.length
  · apply expectedValue_le_of_le
    intro v
    apply expectedValue_le_of_le
    intro r
    unfold nearMemPotential
    rw [if_pos hq]
    exact bot_le
  push Not at hq
  set C0 := reuseC rows (Function.update nonces m (some 0)) with hC0
  have hupd : ∀ v : Digest, reuseC rows (Function.update nonces m (some v)) = C0 := by
    intro v
    unfold reuseC
    apply tsum_congr
    intro m'
    by_cases he : m' = m
    · subst he; simp
    · simp only [Function.update_of_ne he]
  have hafter : ∀ v r, r ∈ support (Sampling.roRun secret (nearSpec.search v m 0 fuel) rows) →
      reuseC r.2 (Function.update nonces m (some v)) = C0 := by
    intro v r hr
    rw [reuseC_signed_eq rows r.2 _ m (by simp) (digestSearch_reuseMass secret v m fuel rows r hr), hupd]
  have hC : C0 + nearSpec.reuseMass rows m ≤ reuseC rows nonces := by
    rw [← hupd 0]
    exact reuseC_sign_le rows rows nonces m 0 hm (fun _ _ => rfl)
  set b : BankCore := ⟨births, exposures, reused, reuseC rows nonces, q - births.length⟩ with hb
  set extra : ENNReal := ((q - births.length : Nat) : ENNReal) * ((1 / 16) / 2 ^ 128) with hextra
  have hbefore : nearMemPotential q births exposures reused rows nonces = nearPotential b + extra := by
    unfold nearMemPotential
    rw [if_neg (by omega)]
  have hpoint : ∀ v r, r ∈ support (Sampling.roRun secret (nearSpec.search v m 0 fuel) rows) →
      nearMemPotential q births (exposures ++ (r.1.map Prod.snd).toList)
          (reused || decide (nearSpec.Reuse rows v m)) r.2 (Function.update nonces m (some v)) =
        nearPotential ⟨births, exposures ++ (r.1.map Prod.snd).toList,
          reused || decide (nearSpec.Reuse rows v m), C0, q - births.length⟩ + extra := by
    intro v r hr
    unfold nearMemPotential
    rw [if_neg (by omega), hafter v r hr]
  have hreuse : ∀ (o : Option HashOutput), nearPotential ⟨births, exposures ++ o.toList, true, C0,
      q - births.length⟩ ≤ nearPotential { b with reused := true, reuse := C0 } := by
    intro o
    have hl : exposures.length ≤ (exposures ++ o.toList).length := by simp
    unfold nearPotential
    rw [hb]
    simp only [if_true]
    by_cases h2 : horizon < exposures.length
    · rw [if_pos (lt_of_lt_of_le h2 hl)]; exact bot_le
    · by_cases h1 : horizon < (exposures ++ o.toList).length
      · rw [if_pos h1]; exact bot_le
      · rw [if_neg h1, if_neg h2]
  rw [hbefore]
  calc
    _ ≤ expectedValue ($ᵗ Digest : ProbComp Digest) (fun v =>
        (if nearSpec.Reuse rows v m then nearPotential { b with reused := true, reuse := C0 }
          else expectedValue (Sampling.roRun secret (nearSpec.search v m 0 fuel) rows)
            (fun r => nearPotential (b.expose C0 (r.1.map Prod.snd)))) + extra) := by
      apply expectedValue_mono
      intro v
      calc
        _ ≤ expectedValue (Sampling.roRun secret (nearSpec.search v m 0 fuel) rows) (fun r =>
            (if nearSpec.Reuse rows v m then nearPotential { b with reused := true, reuse := C0 }
              else nearPotential (b.expose C0 (r.1.map Prod.snd))) + extra) := by
          apply expectedValue_mono_of_support
          intro r hr
          rw [hpoint v r hr]
          apply add_le_add _ le_rfl
          by_cases hre : nearSpec.Reuse rows v m
          · simp only [hre, decide_true, Bool.or_true, if_true]
            exact hreuse _
          · simp only [hre, decide_false, Bool.or_false, if_false]
            exact le_of_eq rfl
        _ ≤ expectedValue (Sampling.roRun secret (nearSpec.search v m 0 fuel) rows) (fun r =>
            (if nearSpec.Reuse rows v m then nearPotential { b with reused := true, reuse := C0 }
              else nearPotential (b.expose C0 (r.1.map Prod.snd)))) + extra := expectedValue_add_const_le _ _ _
        _ ≤ _ := by
          apply add_le_add _ le_rfl
          by_cases hre : nearSpec.Reuse rows v m
          · simp only [hre, if_true]
            exact expectedValue_le_of_le _ fun _ => le_rfl
          · simp only [hre, if_false]
            exact le_rfl
    _ ≤ expectedValue ($ᵗ Digest : ProbComp Digest) (fun v =>
        (if nearSpec.Reuse rows v m then nearPotential { b with reused := true, reuse := C0 }
          else expectedValue (Sampling.roRun secret (nearSpec.search v m 0 fuel) rows)
            (fun r => nearPotential (b.expose C0 (r.1.map Prod.snd))))) + extra := expectedValue_add_const_le _ _ _
    _ ≤ _ := add_le_add (near_sign b rows m C0 hC secret fuel hfuel) le_rfl
theorem mem_initial (q : Nat) :
    nearMemPotential q [] [] false ∅ (fun _ => none) ≤ (q : ENNReal) * 300 / 2 ^ 128 := by
  unfold nearMemPotential
  simp only [List.length_nil, Nat.not_lt_zero, if_false, Nat.sub_zero]
  have hC : reuseC ∅ (fun _ => none) = 0 := by
    unfold reuseC ClaudeWCT.Bank.FtsBankSpec.reuseMass ClaudeWCT.Bank.FtsBankSpec.admissibleEntry
    simp
  have hn := near_initial q
  rw [show (⟨[], [], false, reuseC ∅ (fun _ => none), q⟩ : BankCore) = ⟨[], [], false, 0, q⟩ by rw [hC]]
  calc
    _ ≤ (q : ENNReal) * (4799 / 16) / 2 ^ 128 + (q : ENNReal) * ((1 / 16) / 2 ^ 128) := add_le_add hn le_rfl
    _ = (q : ENNReal) * ((4799 / 16) + 1 / 16) / 2 ^ 128 := by
      simp only [div_eq_mul_inv]
      ring
    _ = _ := by rw [ClaudeWCT.W9.T3.Security.CaseC.near_bound_add_charge]
theorem mem_win (q : Nat) (births exposures : List HashOutput) (reused : Bool) (rows : Sampling.RCache)
    (nonces : Message → Option Digest) (hq : births.length ≤ q) (hlen : exposures.length ≤ horizon)
    (h : reused = true ∨ ∃ N ∈ births, WCT9.admissible N = true ∧ Guess.NearCoveredBy exposures N) :
    1 ≤ nearMemPotential q births exposures reused rows nonces := by
  unfold nearMemPotential
  rw [if_neg (by omega)]
  exact (near_win ⟨births, exposures, reused, reuseC rows nonces, q - births.length⟩ (by simp only; omega) h).trans
    le_self_add
end ClaudeWCT.W9.T3.Security.CaseC
end
section
namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M.Final (AdversaryP)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section Generic
variable {Mem : Type}
variable (impl : QueryImpl WPair.WSpecL (StateT (SecretGuessObservation.State Guess.GCoord Digest Mem) SPMF))
  (Φ : SecretGuessObservation.State Guess.GCoord Digest Mem → ENNReal)
def SuperProg {β : Type} (W : OracleComp WPair.WSpecL β) : Prop :=
  ∀ s, expectedValue (SecretGuessObservation.runWith impl W s) (fun r => Φ r.2) ≤ Φ s
theorem runWith_bind' {β γ : Type} (W : OracleComp WPair.WSpecL β) (K : β → OracleComp WPair.WSpecL γ)
    (s : SecretGuessObservation.State Guess.GCoord Digest Mem) :
    SecretGuessObservation.runWith impl (W >>= K) s =
      SecretGuessObservation.runWith impl W s >>= fun r => SecretGuessObservation.runWith impl (K r.1) r.2 := by
  simp only [SecretGuessObservation.runWith, simulateQ_bind, StateT.run_bind]
theorem runWith_pure' {β : Type} (b : β) (s : SecretGuessObservation.State Guess.GCoord Digest Mem) :
    SecretGuessObservation.runWith impl (pure b) s = pure (b, s) := by
  simp only [SecretGuessObservation.runWith, simulateQ_pure, StateT.run_pure]
theorem superProg_pure {β : Type} (b : β) : SuperProg impl Φ (pure b : OracleComp WPair.WSpecL β) := by
  intro s
  rw [runWith_pure', expectedValue_pure]
theorem superProg_bind {β γ : Type} {W : OracleComp WPair.WSpecL β} {K : β → OracleComp WPair.WSpecL γ}
    (hW : SuperProg impl Φ W) (hK : ∀ b, SuperProg impl Φ (K b)) : SuperProg impl Φ (W >>= K) := by
  intro s
  rw [runWith_bind', expectedValue_bind]
  exact (expectedValue_mono _ fun (r : β × SecretGuessObservation.State Guess.GCoord Digest Mem) =>
    hK r.1 r.2).trans (hW s)
end Generic
section World
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) {Mem : Type}
variable (impl : QueryImpl WPair.WSpecL (StateT (SecretGuessObservation.State Guess.GCoord Digest Mem) SPMF))
  (Φ : SecretGuessObservation.State Guess.GCoord Digest Mem → ENNReal)
noncomputable local instance instDecidableEqCache_w9caseCNearWorld : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
theorem interactionL_pure (ω : CanonTable.Omega U) (published : SigGolfCandidate.T3.Cache) {α : Type} (value : α) :
    WPair.interactionL hU ω published (pure value : OracleComp LazyPrivate.Interaction α) = pure (value, [], []) := rfl
theorem interactionL_coin (ω : CanonTable.Omega U) (published : SigGolfCandidate.T3.Cache) {α : Type} (n : Nat)
    (next : Fin (n + 1) → OracleComp LazyPrivate.Interaction α) :
    WPair.interactionL hU ω published (liftM (LazyPrivate.Interaction.query (.inl (.inl n))) >>= next) =
      (WPair.coinReqL n >>= fun coin => WPair.interactionL hU ω published (next coin)) := rfl
theorem interactionL_public (ω : CanonTable.Omega U) (published : SigGolfCandidate.T3.Cache) {α : Type}
    (x : HashInput) (next : HashOutput → OracleComp LazyPrivate.Interaction α) :
    WPair.interactionL hU ω published (liftM (LazyPrivate.Interaction.query (.inl (.inr x))) >>= next) =
      (WPair.hashL hU ω x >>= fun answer => WPair.interactionL hU ω published (next answer) >>= fun rest =>
        pure (rest.1, rest.2.1, (x, answer) :: rest.2.2)) := rfl
theorem interactionL_request (ω : CanonTable.Omega U) (published : SigGolfCandidate.T3.Cache) {α : Type}
    (request : Request) (next : Option Signature → OracleComp LazyPrivate.Interaction α) :
    WPair.interactionL hU ω published (liftM (LazyPrivate.Interaction.query (.inr request)) >>= next) =
      (WPair.signL hU ω published request >>= fun signature => WPair.interactionL hU ω published (next signature) >>=
        fun rest => pure (rest.1, ⟨request, signature⟩ :: rest.2.1, rest.2.2)) := rfl
theorem programL_pure (ω : CanonTable.Omega U) {β : Type} (value : β) :
    WPair.programL hU ω (pure value : M β) = pure (value, []) := rfl
theorem programL_coin (ω : CanonTable.Omega U) {β : Type} (n : Nat) (next : Fin (n + 1) → M β) :
    WPair.programL hU ω (liftM (SigGolfCandidate.T3.Spec.query (.inl (.inl n))) >>= next) =
      (WPair.coinReqL n >>= fun coin => WPair.programL hU ω (next coin)) := rfl
theorem programL_public (ω : CanonTable.Omega U) {β : Type} (x : HashInput) (next : HashOutput → M β) :
    WPair.programL hU ω (liftM (SigGolfCandidate.T3.Spec.query (.inl (.inr x))) >>= next) =
      (WPair.hashL hU ω x >>= fun answer => WPair.programL hU ω (next answer) >>= fun rest =>
        pure (rest.1, (x, answer) :: rest.2)) := rfl
theorem programL_private (ω : CanonTable.Omega U) {β : Type} (c : Coordinate) (next : HashOutput → M β) :
    WPair.programL hU ω (liftM (SigGolfCandidate.T3.Spec.query (.inr c)) >>= next) =
      WPair.programL hU ω (next 0) := rfl
theorem interactionL_super (ω : CanonTable.Omega U) (published : SigGolfCandidate.T3.Cache)
    (hcoin : ∀ n, SuperProg impl Φ (WPair.coinReqL n))
    (hhash : ∀ x, SuperProg impl Φ (WPair.hashL hU ω x))
    (hsign : ∀ request, SuperProg impl Φ (WPair.signL hU ω published request)) {α : Type}
    (oa : OracleComp LazyPrivate.Interaction α) : SuperProg impl Φ (WPair.interactionL hU ω published oa) := by
  induction oa using OracleComp.inductionOn with
  | pure value =>
      rw [interactionL_pure]
      exact superProg_pure impl Φ _
  | query_bind input next ih =>
      rcases input with (n | x) | request
      · rw [interactionL_coin]
        exact superProg_bind impl Φ (hcoin n) ih
      · rw [interactionL_public]
        exact superProg_bind impl Φ (hhash x) fun a =>
          superProg_bind impl Φ (ih a) fun _ => superProg_pure impl Φ _
      · rw [interactionL_request]
        exact superProg_bind impl Φ (hsign request) fun a =>
          superProg_bind impl Φ (ih a) fun _ => superProg_pure impl Φ _
theorem programL_super (ω : CanonTable.Omega U)
    (hcoin : ∀ n, SuperProg impl Φ (WPair.coinReqL n))
    (hhash : ∀ x, SuperProg impl Φ (WPair.hashL hU ω x)) {β : Type}
    (program : M β) : SuperProg impl Φ (WPair.programL hU ω program) := by
  induction program using OracleComp.inductionOn with
  | pure value =>
      rw [programL_pure]
      exact superProg_pure impl Φ _
  | query_bind input next ih =>
      rcases input with (n | x) | c
      · rw [programL_coin]
        exact superProg_bind impl Φ (hcoin n) ih
      · rw [programL_public]
        exact superProg_bind impl Φ (hhash x) fun a =>
          superProg_bind impl Φ (ih a) fun _ => superProg_pure impl Φ _
      · rw [programL_private]
        exact ih (0 : HashOutput)
theorem worldGameCore_super (ω : CanonTable.Omega U) (adversary : AdversaryP)
    (hcoin : ∀ n, SuperProg impl Φ (WPair.coinReqL n))
    (hhash : ∀ x, SuperProg impl Φ (WPair.hashL hU ω x))
    (hsign : ∀ published request, SuperProg impl Φ (WPair.signL hU ω published request)) :
    SuperProg impl Φ (WPair.worldGameCore hU ω adversary) := by
  unfold WPair.worldGameCore
  exact superProg_bind impl Φ (interactionL_super hU impl Φ ω _ hcoin hhash (hsign _) _) fun _ =>
    superProg_bind impl Φ (programL_super hU impl Φ ω hcoin hhash _) fun _ => superProg_pure impl Φ _
end World
theorem expectedValue_liftM_pmf {α : Type} (p : PMF α) (g : α → ENNReal) :
    expectedValue (liftM p : SPMF α) g = expectedValue p g := by
  unfold expectedValue
  simp [SPMF.probOutput_eq_apply, PMF.probOutput_eq_apply]
theorem expectedValue_uniformOfFintype {α : Type} [Fintype α] [Nonempty α] (g : α → ENNReal) :
    expectedValue (PMF.uniformOfFintype α) g = BPORS.finiteAverage g := by
  unfold expectedValue BPORS.finiteAverage
  simp only [PMF.probOutput_eq_apply, PMF.uniformOfFintype_apply, tsum_fintype]
  rw [div_eq_mul_inv, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
end ClaudeWCT.W9.T3.Security.CaseC
end
section
namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.BPair (AuxL AuxSpecL LazyMem)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
structure NearGhost where
  reused : Bool
  lastFresh : Bool
  fresh : List HashOutput
def NearGhost.empty : NearGhost := ⟨false, false, []⟩
noncomputable def ghostStep (mem : LazyMem) : (i : AuxL) → AuxSpecL.Range i → NearGhost → NearGhost
  | .nonce m, v, g =>
      { g with lastFresh := decide (mem.nonces m = none),
               reused := g.reused || (decide (mem.nonces m = none) && decide (nearSpec.Reuse mem.rows v m)) }
  | .expose o, _, g => if g.lastFresh then { g with fresh := g.fresh ++ o.toList } else g
  | _, _, g => g
def projS (s : SecretGuessObservation.State Guess.GCoord Digest (LazyMem × NearGhost)) : WPair.WStateL :=
  ⟨s.allowed, s.retired, s.guesses, s.probes, s.memory.1⟩
noncomputable def envG (env : SecretGuessObservation.Environment AuxSpecL Guess.GCoord Digest LazyMem) :
    SecretGuessObservation.Environment AuxSpecL Guess.GCoord Digest (LazyMem × NearGhost) where
  auxiliary st i := (fun r => (r.1, (r.2, ghostStep st.memory.1 i r.1 st.memory.2))) <$> env.auxiliary (projS st) i
  trial mem c v hit := (env.trial mem.1 c v hit, mem.2)
  disclosure mem c v := (env.disclosure mem.1 c v, mem.2)
abbrev GState := SecretGuessObservation.State Guess.GCoord Digest (LazyMem × NearGhost)
/-- The family sampler on the ghost-extended memory (it reads only the allowed sets). -/
noncomputable abbrev samplerG : SecretGuessObservation.Sampler Guess.GCoord Digest (LazyMem × NearGhost) :=
  Guess.Fam.sampler (LazyMem × NearGhost)
def initG : GState := SecretGuessObservation.initialState (LazyMem.empty, NearGhost.empty)
theorem projS_initG : projS initG = WPair.initL := rfl
section Project
variable (env : SecretGuessObservation.Environment AuxSpecL Guess.GCoord Digest LazyMem) (slot : Nat)
theorem liftM_map_pmf {α β : Type} (f : α → β) (p : PMF α) :
    (liftM (f <$> p) : SPMF β) = f <$> (liftM p : SPMF α) :=
  evalSPMF_map p f
theorem step_project (q : WPair.WSpecL.Domain) (s : GState) :
    (fun r => (r.1, projS r.2)) <$> (SecretGuessObservation.forcedWithImpl (envG env) samplerG slot q).run s =
      (SecretGuessObservation.forcedWithImpl env WPair.samplerL slot q).run (projS s) := by
  rcases q with i | (⟨c, v⟩ | c)
  · simp only [SecretGuessObservation.forcedWithImpl, SecretGuessObservation.withImpl, SecretGuessObservation.lazyImpl,
    StateT.run_mk]
    change (fun r => (r.1, projS r.2)) <$> ((fun result => (result.1, { s with memory := result.2 })) <$>
      (liftM ((fun r => (r.1, (r.2, ghostStep s.memory.1 i r.1 s.memory.2))) <$> env.auxiliary (projS s) i) :
        SPMF _)) =
      (fun result => (result.1, { projS s with memory := result.2 })) <$> (liftM (env.auxiliary (projS s) i) : SPMF _)
    rw [liftM_map_pmf, Functor.map_map, Functor.map_map]
    rfl
  · simp only [SecretGuessObservation.forcedWithImpl, StateT.run_mk]
    rw [Functor.map_map]
    rfl
  · simp only [SecretGuessObservation.forcedWithImpl, SecretGuessObservation.withImpl, SecretGuessObservation.lazyImpl,
    StateT.run_mk]
    rw [Functor.map_map]
    rfl
theorem run_project {β : Type} (W : OracleComp WPair.WSpecL β) (s : GState) :
    (fun r => (r.1, projS r.2)) <$>
        SecretGuessObservation.runWith (SecretGuessObservation.forcedWithImpl (envG env) samplerG slot) W s =
      SecretGuessObservation.runWith (SecretGuessObservation.forcedWithImpl env WPair.samplerL slot) W (projS s) := by
  induction W using OracleComp.inductionOn generalizing s with
  | pure b =>
      simp only [SecretGuessObservation.runWith, simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind q next ih =>
      rw [SecretGuessObservation.runWith_query_bind, SecretGuessObservation.runWith_query_bind, map_bind]
      simp_rw [ih]
      rw [← step_project env slot q s, bind_map_left]
theorem expectedValue_project {β : Type} (W : OracleComp WPair.WSpecL β) (s : GState)
    (payoff : β × WPair.WStateL → ENNReal) :
    expectedValue (SecretGuessObservation.runWith (SecretGuessObservation.forcedWithImpl env WPair.samplerL slot) W (projS s)) payoff =
      expectedValue (SecretGuessObservation.runWith (SecretGuessObservation.forcedWithImpl (envG env) samplerG slot) W s)
        (fun r => payoff (r.1, projS r.2)) := by
  rw [← run_project env slot W s, expectedValue_map]
end Project
end ClaudeWCT.W9.T3.Security.CaseC
end
section
namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.BPair (AuxL AuxSpecL LazyMem)
open SphincsSecurity.Concrete
open SphincsSecurity.Completeness (searchLoop)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable abbrev implG (slot : Nat) := SecretGuessObservation.forcedWithImpl (envG WPair.envL) samplerG slot
theorem ev_aux_bind {β : Type} (slot : Nat) (i : AuxL) (k : AuxSpecL.Range i → OracleComp WPair.WSpecL β)
    (s : GState) (G : β × GState → ENNReal) :
    expectedValue (SecretGuessObservation.runWith (implG slot) (liftM (WPair.WSpecL.query (.inl i)) >>= k) s) G =
      expectedValue (WPair.envL.auxiliary (projS s) i) (fun r =>
        expectedValue (SecretGuessObservation.runWith (implG slot) (k r.1)
          { s with memory := (r.2, ghostStep s.memory.1 i r.1 s.memory.2) }) G) := by
  rw [SecretGuessObservation.runWith_query_bind, expectedValue_bind]
  simp only [SecretGuessObservation.forcedWithImpl, SecretGuessObservation.withImpl, SecretGuessObservation.lazyImpl,
    StateT.run_mk]
  change expectedValue ((fun result => (result.1, { s with memory := result.2 })) <$>
    (liftM ((fun r => (r.1, (r.2, ghostStep s.memory.1 i r.1 s.memory.2))) <$> WPair.envL.auxiliary (projS s) i) :
      SPMF _)) _ = _
  rw [expectedValue_map, expectedValue_liftM_pmf, expectedValue_map]
theorem searchL_succ (rho : Digest) (m : Message) (c fuel : Nat) :
    WPair.searchL rho m c (fuel + 1) =
      (liftM (WPair.WSpecL.query (.inl (.trial (Sampling.digestTrial rho m c)))) >>= fun output =>
        if WCT9.producerAdmissible output = true then pure (some (BitVec.ofNat 32 c, output))
        else WPair.searchL rho m (c + 1) fuel) := rfl
theorem ev_uniform_eq (g : HashOutput → ENNReal) :
    expectedValue (PMF.uniformOfFintype HashOutput) g = expectedValue ($ᵗ HashOutput : ProbComp HashOutput) g := by
  rw [expectedValue_uniformOfFintype, BPORS.expected_uniform_eq_finiteAverage]
theorem nearSpec_producer : nearSpec.producer = WCT9.producerAdmissible := rfl
theorem nearSpec_decode_some {a : HashOutput} (h : WCT9.producerAdmissible a = true) :
    nearSpec.decode a = some a := by
  simp [ClaudeWCT.Bank.FtsBankSpec.decode, nearSpec_producer, h]
theorem nearSpec_decode_none {a : HashOutput} (h : ¬WCT9.producerAdmissible a = true) :
    nearSpec.decode a = none := by
  simp [ClaudeWCT.Bank.FtsBankSpec.decode, nearSpec_producer, h]
theorem search_law (slot : Nat) (rho : Digest) (m : Message)
    (F : Option (BitVec 32 × HashOutput) → Sampling.RCache → ENNReal) :
    ∀ fuel c (s : GState),
      expectedValue (SecretGuessObservation.runWith (implG slot) (WPair.searchL rho m c fuel) s)
          (fun r => F r.1 r.2.memory.1.rows) =
        expectedValue (Sampling.roRun 0 (nearSpec.search rho m c fuel) s.memory.1.rows) (fun r => F r.1 r.2) := by
  intro fuel
  induction fuel with
  | zero =>
      intro c s
      change expectedValue (SecretGuessObservation.runWith (implG slot) (pure none) s) _ =
        expectedValue (Sampling.roRun 0 (pure none) s.memory.1.rows) _
      simp only [SecretGuessObservation.runWith, simulateQ_pure, StateT.run_pure, Sampling.roRun_pure,
        expectedValue_pure]
  | succ fuel ih =>
      intro c s
      rw [searchL_succ, ev_aux_bind]
      unfold ClaudeWCT.Bank.FtsBankSpec.search
      rw [Sampling.publicSearch_succ, Sampling.roRun_bind, Sampling.roRun_publicQuery, expectedValue_bind,
        randomOracle.run_eq]
      change expectedValue (BPair.rowStep s.memory.1 (Sampling.digestTrial rho m c) false
        (PMF.uniformOfFintype HashOutput)) _ = _
      cases hx : s.memory.1.rows (Sampling.digestTrial rho m c) with
      | some a =>
          simp only [BPair.rowStep, hx]
          rw [expectedValue_pure, expectedValue_pure]
          dsimp only
          by_cases had : WCT9.producerAdmissible a = true
          · simp only [nearSpec_decode_some had, had, if_true]
            simp only [SecretGuessObservation.runWith, simulateQ_pure, StateT.run_pure, Sampling.roRun_pure,
              expectedValue_pure]
            rfl
          · simp only [nearSpec_decode_none had, had, Bool.false_eq_true, if_false]
            rw [ih (c + 1)]
            rfl
      | none =>
          have hdi : Sampling.digestTrial rho m c ∈ BPair.digestInputs := BPair.digestInput_mem _ _ _
          simp only [BPair.rowStep, hx, hdi, if_true]
          rw [expectedValue_map, expectedValue_bind, ev_uniform_eq]
          apply congrArg
          funext a
          rw [expectedValue_pure]
          dsimp only
          by_cases had : WCT9.producerAdmissible a = true
          · simp only [nearSpec_decode_some had, had, if_true]
            simp only [SecretGuessObservation.runWith, simulateQ_pure, StateT.run_pure, Sampling.roRun_pure,
              expectedValue_pure]
            rfl
          · simp only [nearSpec_decode_none had, had, Bool.false_eq_true, if_false]
            rw [ih (c + 1)]
            rfl
def RowsFrame (s s' : GState) : Prop :=
  s'.allowed = s.allowed ∧ s'.retired = s.retired ∧ s'.guesses = s.guesses ∧ s'.probes = s.probes ∧
    s'.memory.2 = s.memory.2 ∧ s'.memory.1.nonces = s.memory.1.nonces ∧ s'.memory.1.births = s.memory.1.births ∧
    s'.memory.1.exposures = s.memory.1.exposures
theorem RowsFrame.refl (s : GState) : RowsFrame s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem RowsFrame.trans {s s' s'' : GState} (h : RowsFrame s s') (h' : RowsFrame s' s'') : RowsFrame s s'' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.1.trans h.2.2.2.1,
    h'.2.2.2.2.1.trans h.2.2.2.2.1, h'.2.2.2.2.2.1.trans h.2.2.2.2.2.1, h'.2.2.2.2.2.2.1.trans h.2.2.2.2.2.2.1,
    h'.2.2.2.2.2.2.2.trans h.2.2.2.2.2.2.2⟩
theorem runWith_bind_nonzero {β γ : Type} (slot : Nat) (W : OracleComp WPair.WSpecL β)
    (K : β → OracleComp WPair.WSpecL γ) (s : GState) (r : γ × GState)
    (hr : SecretGuessObservation.runWith (implG slot) (W >>= K) s r ≠ 0) :
    ∃ mid, SecretGuessObservation.runWith (implG slot) W s mid ≠ 0 ∧
      SecretGuessObservation.runWith (implG slot) (K mid.1) mid.2 r ≠ 0 := by
  rw [runWith_bind', RetainedObservation.bind_nonzero] at hr
  exact hr
theorem runWith_pure_nonzero {β : Type} (slot : Nat) (b : β) (s : GState) (r : β × GState)
    (hr : SecretGuessObservation.runWith (implG slot) (pure b) s r ≠ 0) : r = (b, s) := by
  rw [runWith_pure'] at hr
  simpa only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] using hr
theorem aux_nonzero (slot : Nat) (i : AuxL) (s : GState) (r : AuxSpecL.Range i × GState)
    (hr : SecretGuessObservation.runWith (implG slot) (liftM (WPair.WSpecL.query (.inl i))) s r ≠ 0) :
    ∃ res, WPair.envL.auxiliary (projS s) i res ≠ 0 ∧
      r = (res.1, { s with memory := (res.2, ghostStep s.memory.1 i res.1 s.memory.2) }) := by
  unfold SecretGuessObservation.runWith at hr
  rw [simulateQ_spec_query] at hr
  simp only [SecretGuessObservation.forcedWithImpl, SecretGuessObservation.withImpl, SecretGuessObservation.lazyImpl,
    StateT.run_mk] at hr
  change ((fun result => (result.1, { s with memory := result.2 })) <$>
    (liftM ((fun r => (r.1, (r.2, ghostStep s.memory.1 i r.1 s.memory.2))) <$> WPair.envL.auxiliary (projS s) i) :
      SPMF _)) r ≠ 0 at hr
  rw [liftM_map_pmf, Functor.map_map, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hr
  obtain ⟨res, hres, hr⟩ := hr
  simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
  refine ⟨res, ?_, hr⟩
  simpa [SPMF.liftM_apply] using hres
theorem search_frame (slot : Nat) (rho : Digest) (m : Message) :
    ∀ fuel c (s : GState) r, SecretGuessObservation.runWith (implG slot) (WPair.searchL rho m c fuel) s r ≠ 0 →
      RowsFrame s r.2 := by
  intro fuel
  induction fuel with
  | zero =>
      intro c s r hr
      rw [runWith_pure_nonzero slot none s r hr]
      exact RowsFrame.refl s
  | succ fuel ih =>
      intro c s r hr
      rw [searchL_succ] at hr
      obtain ⟨mid, hmid, hr⟩ := runWith_bind_nonzero slot _ _ s r hr
      obtain ⟨res, hres, rfl⟩ := aux_nonzero slot (.trial (Sampling.digestTrial rho m c)) s mid hmid
      have hf : RowsFrame s { s with memory := (res.2, ghostStep s.memory.1 (.trial (Sampling.digestTrial rho m c))
          res.1 s.memory.2) } := by
        have hres' : res ∈ (BPair.rowStep s.memory.1 (Sampling.digestTrial rho m c) false
            (PMF.uniformOfFintype HashOutput)).support := (PMF.mem_support_iff _ _).mpr hres
        refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
        unfold BPair.rowStep at hres'
        cases hx : s.memory.1.rows (Sampling.digestTrial rho m c) with
        | some a =>
            simp only [hx] at hres'
            rw [PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hres'
            subst hres'
            exact ⟨rfl, rfl, rfl⟩
        | none =>
            simp only [hx] at hres'
            have hdi : Sampling.digestTrial rho m c ∈ BPair.digestInputs := BPair.digestInput_mem _ _ _
            rw [if_pos hdi] at hres'
            rw [PMF.monad_map_eq_map, PMF.mem_support_map_iff] at hres'
            obtain ⟨a, -, rfl⟩ := hres'
            exact ⟨rfl, rfl, rfl⟩
      dsimp only at hr
      split_ifs at hr
      · rw [runWith_pure_nonzero slot _ _ r hr]
        exact hf
      · exact hf.trans (ih (c + 1) _ r hr)
end ClaudeWCT.W9.T3.Security.CaseC
end
end

namespace ClaudeWCT.Bank.NearWorld
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.BPair (AuxL AuxSpecL LazyMem)
open SphincsSecurity.Concrete
open ClaudeWCT.W9.T3.Security
open ClaudeWCT.W9.T3.Security.CaseC (NearGhost projS GState samplerG initG RowsFrame
 runWith_bind' runWith_pure' expectedValue_liftM_pmf expectedValue_uniformOfFintype)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpec P)
noncomputable def searchL (S : FtsBankSpec P) (rho : Digest) (m : Message) (counter : Nat) :
    Nat → OracleComp WPair.WSpecL (Option (BitVec 32 × HashOutput))
  | 0 => pure none
  | fuel+1 => do
      let output ← liftM (WPair.WSpecL.query (.inl (.trial (Sampling.digestTrial rho m counter))))
      if S.producer output=true then pure (some (BitVec.ofNat 32 counter,output))
      else searchL S rho m (counter+1) fuel
noncomputable def ghostStep (S : FtsBankSpec P) (mem : LazyMem) : (i : AuxL) → AuxSpecL.Range i → NearGhost → NearGhost
  | .nonce m, v, g =>
      { g with lastFresh := decide (mem.nonces m = none),
               reused := g.reused || (decide (mem.nonces m = none) && decide (S.Reuse mem.rows v m)) }
  | .expose o, _, g => if g.lastFresh then { g with fresh := g.fresh ++ o.toList } else g
  | _, _, g => g
noncomputable def envG (S : FtsBankSpec P) (env : SecretGuessObservation.Environment AuxSpecL Guess.GCoord Digest LazyMem) :
    SecretGuessObservation.Environment AuxSpecL Guess.GCoord Digest (LazyMem × NearGhost) where
  auxiliary st i := (fun r => (r.1, (r.2, (ghostStep S) st.memory.1 i r.1 st.memory.2))) <$> env.auxiliary (projS st) i
  trial mem c v hit := (env.trial mem.1 c v hit, mem.2)
  disclosure mem c v := (env.disclosure mem.1 c v, mem.2)
section Project
variable (env : SecretGuessObservation.Environment AuxSpecL Guess.GCoord Digest LazyMem) (slot : Nat)
theorem liftM_map_pmf (S : FtsBankSpec P) {α β : Type} (f : α → β) (p : PMF α) :
    (liftM (f <$> p) : SPMF β) = f <$> (liftM p : SPMF α) :=
  evalSPMF_map p f
theorem step_project (S : FtsBankSpec P) (env : SecretGuessObservation.Environment AuxSpecL Guess.GCoord Digest LazyMem) (slot : Nat) (q : WPair.WSpecL.Domain) (s : GState) :
    (fun r => (r.1, projS r.2)) <$> (SecretGuessObservation.forcedWithImpl ((envG S) env) samplerG slot q).run s =
      (SecretGuessObservation.forcedWithImpl env WPair.samplerL slot q).run (projS s) := by
  rcases q with i | (⟨c, v⟩ | c)
  · simp only [SecretGuessObservation.forcedWithImpl, SecretGuessObservation.withImpl, SecretGuessObservation.lazyImpl,
    StateT.run_mk]
    change (fun r => (r.1, projS r.2)) <$> ((fun result => (result.1, { s with memory := result.2 })) <$>
      (liftM ((fun r => (r.1, (r.2, (ghostStep S) s.memory.1 i r.1 s.memory.2))) <$> env.auxiliary (projS s) i) :
        SPMF _)) =
      (fun result => (result.1, { projS s with memory := result.2 })) <$> (liftM (env.auxiliary (projS s) i) : SPMF _)
    rw [(liftM_map_pmf S), Functor.map_map, Functor.map_map]
    rfl
  · simp only [SecretGuessObservation.forcedWithImpl, StateT.run_mk]
    rw [Functor.map_map]
    rfl
  · simp only [SecretGuessObservation.forcedWithImpl, SecretGuessObservation.withImpl, SecretGuessObservation.lazyImpl,
    StateT.run_mk]
    rw [Functor.map_map]
    rfl
theorem run_project (S : FtsBankSpec P) (env : SecretGuessObservation.Environment AuxSpecL Guess.GCoord Digest LazyMem) (slot : Nat) {β : Type} (W : OracleComp WPair.WSpecL β) (s : GState) :
    (fun r => (r.1, projS r.2)) <$>
        SecretGuessObservation.runWith (SecretGuessObservation.forcedWithImpl ((envG S) env) samplerG slot) W s =
      SecretGuessObservation.runWith (SecretGuessObservation.forcedWithImpl env WPair.samplerL slot) W (projS s) := by
  induction W using OracleComp.inductionOn generalizing s with
  | pure b =>
      simp only [SecretGuessObservation.runWith, simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind q next ih =>
      rw [SecretGuessObservation.runWith_query_bind, SecretGuessObservation.runWith_query_bind, map_bind]
      simp_rw [ih]
      rw [← (step_project S) env slot q s, bind_map_left]
theorem expectedValue_project (S : FtsBankSpec P) (env : SecretGuessObservation.Environment AuxSpecL Guess.GCoord Digest LazyMem) (slot : Nat) {β : Type} (W : OracleComp WPair.WSpecL β) (s : GState)
    (payoff : β × WPair.WStateL → ENNReal) :
    expectedValue (SecretGuessObservation.runWith (SecretGuessObservation.forcedWithImpl env WPair.samplerL slot) W (projS s)) payoff =
      expectedValue (SecretGuessObservation.runWith (SecretGuessObservation.forcedWithImpl ((envG S) env) samplerG slot) W s)
        (fun r => payoff (r.1, projS r.2)) := by
  rw [← (run_project S) env slot W s, expectedValue_map]
end Project
noncomputable abbrev implG (S : FtsBankSpec P) (slot : Nat) := SecretGuessObservation.forcedWithImpl ((envG S) WPair.envL) samplerG slot
theorem ev_aux_bind (S : FtsBankSpec P) {β : Type} (slot : Nat) (i : AuxL) (k : AuxSpecL.Range i → OracleComp WPair.WSpecL β)
    (s : GState) (G : β × GState → ENNReal) :
    expectedValue (SecretGuessObservation.runWith ((implG S) slot) (liftM (WPair.WSpecL.query (.inl i)) >>= k) s) G =
      expectedValue (WPair.envL.auxiliary (projS s) i) (fun r =>
        expectedValue (SecretGuessObservation.runWith ((implG S) slot) (k r.1)
          { s with memory := (r.2, (ghostStep S) s.memory.1 i r.1 s.memory.2) }) G) := by
  rw [SecretGuessObservation.runWith_query_bind, expectedValue_bind]
  simp only [SecretGuessObservation.forcedWithImpl, SecretGuessObservation.withImpl, SecretGuessObservation.lazyImpl,
    StateT.run_mk]
  change expectedValue ((fun result => (result.1, { s with memory := result.2 })) <$>
    (liftM ((fun r => (r.1, (r.2, (ghostStep S) s.memory.1 i r.1 s.memory.2))) <$> WPair.envL.auxiliary (projS s) i) :
      SPMF _)) _ = _
  rw [expectedValue_map, expectedValue_liftM_pmf, expectedValue_map]
theorem searchL_succ (S : FtsBankSpec P) (rho : Digest) (m : Message) (c fuel : Nat) :
    (searchL S) rho m c (fuel + 1) =
      (liftM (WPair.WSpecL.query (.inl (.trial (Sampling.digestTrial rho m c)))) >>= fun output =>
        if S.producer output = true then pure (some (BitVec.ofNat 32 c, output))
        else (searchL S) rho m (c + 1) fuel) := rfl
theorem ev_uniform_eq (S : FtsBankSpec P) (g : HashOutput → ENNReal) :
    expectedValue (PMF.uniformOfFintype HashOutput) g = expectedValue ($ᵗ HashOutput : ProbComp HashOutput) g := by
  rw [expectedValue_uniformOfFintype, BPORS.expected_uniform_eq_finiteAverage]
theorem S_decode_some (S : FtsBankSpec P) {a : HashOutput} (h : S.producer a = true) :
    S.decode a = some a := by
  simp [ClaudeWCT.Bank.FtsBankSpec.decode, h]
theorem S_decode_none (S : FtsBankSpec P) {a : HashOutput} (h : ¬S.producer a = true) :
    S.decode a = none := by
  simp [ClaudeWCT.Bank.FtsBankSpec.decode, h]
theorem search_law (S : FtsBankSpec P) (slot : Nat) (rho : Digest) (m : Message)
    (F : Option (BitVec 32 × HashOutput) → Sampling.RCache → ENNReal) :
    ∀ fuel c (s : GState),
      expectedValue (SecretGuessObservation.runWith ((implG S) slot) ((searchL S) rho m c fuel) s)
          (fun r => F r.1 r.2.memory.1.rows) =
        expectedValue (Sampling.roRun 0 (S.search rho m c fuel) s.memory.1.rows) (fun r => F r.1 r.2) := by
  intro fuel
  induction fuel with
  | zero =>
      intro c s
      change expectedValue (SecretGuessObservation.runWith ((implG S) slot) (pure none) s) _ =
        expectedValue (Sampling.roRun 0 (pure none) s.memory.1.rows) _
      simp only [SecretGuessObservation.runWith, simulateQ_pure, StateT.run_pure, Sampling.roRun_pure,
        expectedValue_pure]
  | succ fuel ih =>
      intro c s
      rw [(searchL_succ S), (ev_aux_bind S)]
      unfold ClaudeWCT.Bank.FtsBankSpec.search
      rw [Sampling.publicSearch_succ, Sampling.roRun_bind, Sampling.roRun_publicQuery, expectedValue_bind,
        randomOracle.run_eq]
      change expectedValue (BPair.rowStep s.memory.1 (Sampling.digestTrial rho m c) false
        (PMF.uniformOfFintype HashOutput)) _ = _
      cases hx : s.memory.1.rows (Sampling.digestTrial rho m c) with
      | some a =>
          simp only [BPair.rowStep, hx]
          rw [expectedValue_pure, expectedValue_pure]
          dsimp only
          by_cases had : S.producer a = true
          · simp only [S_decode_some S had, had, if_true]
            simp only [SecretGuessObservation.runWith, simulateQ_pure, StateT.run_pure, Sampling.roRun_pure,
              expectedValue_pure]
            rfl
          · simp only [S_decode_none S had, had, Bool.false_eq_true, if_false]
            rw [ih (c + 1)]
            rfl
      | none =>
          have hdi : Sampling.digestTrial rho m c ∈ BPair.digestInputs := BPair.digestInput_mem _ _ _
          simp only [BPair.rowStep, hx, hdi, if_true]
          rw [expectedValue_map, expectedValue_bind, (ev_uniform_eq S)]
          apply congrArg
          funext a
          rw [expectedValue_pure]
          dsimp only
          by_cases had : S.producer a = true
          · simp only [S_decode_some S had, had, if_true]
            simp only [SecretGuessObservation.runWith, simulateQ_pure, StateT.run_pure, Sampling.roRun_pure,
              expectedValue_pure]
            rfl
          · simp only [S_decode_none S had, had, Bool.false_eq_true, if_false]
            rw [ih (c + 1)]
            rfl
theorem runWith_bind_nonzero (S : FtsBankSpec P) {β γ : Type} (slot : Nat) (W : OracleComp WPair.WSpecL β)
    (K : β → OracleComp WPair.WSpecL γ) (s : GState) (r : γ × GState)
    (hr : SecretGuessObservation.runWith ((implG S) slot) (W >>= K) s r ≠ 0) :
    ∃ mid, SecretGuessObservation.runWith ((implG S) slot) W s mid ≠ 0 ∧
      SecretGuessObservation.runWith ((implG S) slot) (K mid.1) mid.2 r ≠ 0 := by
  rw [runWith_bind', RetainedObservation.bind_nonzero] at hr
  exact hr
theorem runWith_pure_nonzero (S : FtsBankSpec P) {β : Type} (slot : Nat) (b : β) (s : GState) (r : β × GState)
    (hr : SecretGuessObservation.runWith ((implG S) slot) (pure b) s r ≠ 0) : r = (b, s) := by
  rw [runWith_pure'] at hr
  simpa only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] using hr
theorem aux_nonzero (S : FtsBankSpec P) (slot : Nat) (i : AuxL) (s : GState) (r : AuxSpecL.Range i × GState)
    (hr : SecretGuessObservation.runWith ((implG S) slot) (liftM (WPair.WSpecL.query (.inl i))) s r ≠ 0) :
    ∃ res, WPair.envL.auxiliary (projS s) i res ≠ 0 ∧
      r = (res.1, { s with memory := (res.2, (ghostStep S) s.memory.1 i res.1 s.memory.2) }) := by
  unfold SecretGuessObservation.runWith at hr
  rw [simulateQ_spec_query] at hr
  simp only [SecretGuessObservation.forcedWithImpl, SecretGuessObservation.withImpl, SecretGuessObservation.lazyImpl,
    StateT.run_mk] at hr
  change ((fun result => (result.1, { s with memory := result.2 })) <$>
    (liftM ((fun r => (r.1, (r.2, (ghostStep S) s.memory.1 i r.1 s.memory.2))) <$> WPair.envL.auxiliary (projS s) i) :
      SPMF _)) r ≠ 0 at hr
  rw [(liftM_map_pmf S), Functor.map_map, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hr
  obtain ⟨res, hres, hr⟩ := hr
  simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
  refine ⟨res, ?_, hr⟩
  simpa [SPMF.liftM_apply] using hres
theorem search_frame (S : FtsBankSpec P) (slot : Nat) (rho : Digest) (m : Message) :
    ∀ fuel c (s : GState) r, SecretGuessObservation.runWith ((implG S) slot) ((searchL S) rho m c fuel) s r ≠ 0 →
      RowsFrame s r.2 := by
  intro fuel
  induction fuel with
  | zero =>
      intro c s r hr
      rw [(runWith_pure_nonzero S) slot none s r hr]
      exact RowsFrame.refl s
  | succ fuel ih =>
      intro c s r hr
      rw [(searchL_succ S)] at hr
      obtain ⟨mid, hmid, hr⟩ := (runWith_bind_nonzero S) slot _ _ s r hr
      obtain ⟨res, hres, rfl⟩ := (aux_nonzero S) slot (.trial (Sampling.digestTrial rho m c)) s mid hmid
      have hf : RowsFrame s { s with memory := (res.2, (ghostStep S) s.memory.1 (.trial (Sampling.digestTrial rho m c))
          res.1 s.memory.2) } := by
        have hres' : res ∈ (BPair.rowStep s.memory.1 (Sampling.digestTrial rho m c) false
            (PMF.uniformOfFintype HashOutput)).support := (PMF.mem_support_iff _ _).mpr hres
        refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
        unfold BPair.rowStep at hres'
        cases hx : s.memory.1.rows (Sampling.digestTrial rho m c) with
        | some a =>
            simp only [hx] at hres'
            rw [PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hres'
            subst hres'
            exact ⟨rfl, rfl, rfl⟩
        | none =>
            simp only [hx] at hres'
            have hdi : Sampling.digestTrial rho m c ∈ BPair.digestInputs := BPair.digestInput_mem _ _ _
            rw [if_pos hdi] at hres'
            rw [PMF.monad_map_eq_map, PMF.mem_support_map_iff] at hres'
            obtain ⟨a, -, rfl⟩ := hres'
            exact ⟨rfl, rfl, rfl⟩
      dsimp only at hr
      split_ifs at hr
      · rw [(runWith_pure_nonzero S) slot _ _ r hr]
        exact hf
      · exact hf.trans (ih (c + 1) _ r hr)
end ClaudeWCT.Bank.NearWorld
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsSmallContract ====
section

namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Security.Wots (signRatio digestClass)
noncomputable def nearPrice : ENNReal := 150
noncomputable def nearTerm (q : Nat) : ENNReal :=
  (q : ENNReal) * ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ *
    (nearPrice * q / 2 ^ 128 + 63 * (signRatio * q : Nat) * SeccClosingW9.cacheRate / 2 ^ 128 +
      63 * (2 : ENNReal)⁻¹ ^ 700)
/-- Small case-C bound on the runs without FTS overflow (`WPair.NoOverflow`, campaign X1 stage A); the overflow
mass `2^-137` is charged to `SeccClosingW9.smallAbsolute` in `cleanWin_le_cases` / `small_route`. -/
def CaseCSmallBound : Prop :=
  ∀ (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127), 1 ≤ q → q ≤ SeccClosingW9.budgetSplit →
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ CaseC.CaseCFreshPinned adversary z ∧ WPair.NoOverflow adversary z |
        SeccLaw.completedExperiment adversary q hq] ≤
      (1 + SeccClosingW9.cacheRate) / 2 ^ 128 * SeccLaw.expectedCharge adversary q hq digestClass +
        (q : ENNReal) * SeccClosingW9.excessRate / 2 ^ 128 + nearTerm q + BPair.pairTerm q +
        (2 : ENNReal)⁻¹ ^ 700
end ClaudeWCT.W9.T3.Security.Wots
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_CaseCNearFinal ====
section

section
namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.BPair (LazyMem)
open SphincsSecurity.Concrete
open SphincsSecurity.Completeness (searchLoop)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def Extends (rows rows' : Sampling.RCache) : Prop := ∀ x a, rows x = some a → rows' x = some a
theorem Extends.refl (rows : Sampling.RCache) : Extends rows rows := fun _ _ h => h
theorem Extends.trans {r1 r2 r3 : Sampling.RCache} (h1 : Extends r1 r2) (h2 : Extends r2 r3) : Extends r1 r3 :=
  fun x a h => h2 x a (h1 x a h)
theorem search_replays_gen {β γ : Type} (secret : BitVec 256) (inputs : Nat → HashInput)
    (decoder : HashOutput → Option β) (result : Nat → β → γ) :
    ∀ fuel counter (cache : Sampling.RCache) r,
      r ∈ support (Sampling.roRun secret
        (Sampling.publicProgram (searchLoop inputs decoder (fun c v => pure (result c v)) fuel counter)) cache) →
      Extends cache r.2 ∧ ∀ cache', Extends r.2 cache' → ∀ r' ∈ support (Sampling.roRun secret
        (Sampling.publicProgram (searchLoop inputs decoder (fun c v => pure (result c v)) fuel counter)) cache'),
          r' = (r.1, cache') := by
  intro fuel
  induction fuel with
  | zero =>
      intro counter cache r hr
      simp only [searchLoop, Sampling.publicProgram, simulateQ_pure] at hr
      change r ∈ support (Sampling.roRun secret (pure none) cache) at hr
      rw [Sampling.roRun_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr
      refine ⟨Extends.refl _, fun cache' _ r' hr' => ?_⟩
      simp only [searchLoop, Sampling.publicProgram, simulateQ_pure] at hr'
      change r' ∈ support (Sampling.roRun secret (pure none) cache') at hr'
      rw [Sampling.roRun_pure, support_pure, Set.mem_singleton_iff] at hr'
      exact hr'
  | succ fuel ih =>
      intro counter cache r hr
      rw [Sampling.publicSearch_succ, Sampling.roRun_bind, Sampling.roRun_publicQuery, mem_support_bind_iff] at hr
      obtain ⟨first, hfirst, hr⟩ := hr
      have hfirst' : Extends cache first.2 ∧ first.2 (inputs counter) = some first.1 := by
        rw [randomOracle.run_eq] at hfirst
        cases hc : cache (inputs counter) with
        | some a =>
            rw [hc, support_pure, Set.mem_singleton_iff] at hfirst
            subst hfirst
            exact ⟨Extends.refl _, hc⟩
        | none =>
            rw [hc, mem_support_bind_iff] at hfirst
            obtain ⟨a, -, hfa⟩ := hfirst
            rw [support_pure, Set.mem_singleton_iff] at hfa
            subst hfa
            refine ⟨fun x b hx => ?_, QueryCache.cacheQuery_self _ _ _⟩
            have hne : x ≠ inputs counter := fun he => by rw [he, hc] at hx; cases hx
            exact (QueryCache.cacheQuery_of_ne cache a hne).trans hx
      cases hd : decoder first.1 with
      | none =>
          rw [hd] at hr
          obtain ⟨h1, h2⟩ := ih (counter + 1) first.2 r hr
          refine ⟨hfirst'.1.trans h1, fun cache' hc' r' hr' => ?_⟩
          rw [Sampling.publicSearch_succ, Sampling.roRun_bind, Sampling.roRun_publicQuery, mem_support_bind_iff] at hr'
          obtain ⟨first', hf'', hr'⟩ := hr'
          have hq : cache' (inputs counter) = some first.1 := hc' _ _ (h1 _ _ hfirst'.2)
          rw [randomOracle.run_eq, hq, support_pure, Set.mem_singleton_iff] at hf''
          subst hf''
          simp only [hd] at hr'
          exact h2 cache' hc' r' hr'
      | some value =>
          rw [hd] at hr
          simp only at hr
          rw [Sampling.roRun_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr
          refine ⟨hfirst'.1, fun cache' hc' r' hr' => ?_⟩
          rw [Sampling.publicSearch_succ, Sampling.roRun_bind, Sampling.roRun_publicQuery, mem_support_bind_iff] at hr'
          obtain ⟨first', hf'', hr'⟩ := hr'
          have hq : cache' (inputs counter) = some first.1 := hc' _ _ hfirst'.2
          rw [randomOracle.run_eq, hq, support_pure, Set.mem_singleton_iff] at hf''
          subst hf''
          simp only [hd] at hr'
          rw [Sampling.roRun_pure, support_pure, Set.mem_singleton_iff] at hr'
          exact hr'
def Replays (rows : Sampling.RCache) (rho : Digest) (m : Message) (found : Option (BitVec 32 × HashOutput)) : Prop :=
  ∀ cache', Extends rows cache' →
    ∀ r' ∈ support (Sampling.roRun 0 (nearSpec.search rho m 0 WCT9.digestAttemptLimit) cache'), r' = (found, cache')
theorem Replays.mono {rows rows' : Sampling.RCache} {rho : Digest} {m : Message} {found}
    (h : Replays rows rho m found) (hext : Extends rows rows') : Replays rows' rho m found :=
  fun cache' hc => h cache' (hext.trans hc)
theorem replays_of_search (rho : Digest) (m : Message) (rows : Sampling.RCache) (r)
    (hr : r ∈ support (Sampling.roRun 0 (nearSpec.search rho m 0 WCT9.digestAttemptLimit) rows)) :
    Extends rows r.2 ∧ Replays r.2 rho m r.1 := by
  unfold ClaudeWCT.Bank.FtsBankSpec.search at hr
  obtain ⟨h1, h2⟩ := search_replays_gen 0 (Sampling.digestTrial rho m) nearSpec.decode _ _ 0 rows r hr
  refine ⟨h1, fun cache' hc r' hr' => ?_⟩
  unfold ClaudeWCT.Bank.FtsBankSpec.search at hr'
  exact h2 cache' hc r' hr'
def InvM (M : LazyMem × NearGhost) : Prop :=
  (∀ v ∈ M.1.exposures, v ∈ M.2.fresh) ∧ M.2.fresh.length ≤ M.1.exposures.length ∧
    ∀ m rho, M.1.nonces m = some rho → ∃ found, Replays M.1.rows rho m found ∧
      ∀ v ∈ (found.map Prod.snd).toList, v ∈ M.2.fresh
theorem invM_empty : InvM (LazyMem.empty, NearGhost.empty) := by
  refine ⟨fun v hv => by simp [LazyMem.empty] at hv, by simp [LazyMem.empty, NearGhost.empty], ?_⟩
  intro m rho h
  simp [LazyMem.empty] at h
noncomputable def ghostPot (q : Nat) (M : LazyMem × NearGhost) : ENNReal :=
  nearMemPotential q M.1.births M.2.fresh M.2.reused M.1.rows M.1.nonces
noncomputable def ΦI (q : Nat) (s : GState) : ENNReal := if InvM s.memory then ghostPot q s.memory else ⊤
theorem ΦI_initial (q : Nat) : ΦI q initG ≤ (q : ENNReal) * 300 / 2 ^ 128 := by
  unfold ΦI
  rw [if_pos (show InvM initG.memory from invM_empty)]
  exact mem_initial q
theorem nearCoveredBy_mono {X Y : List HashOutput} (h : ∀ v ∈ X, v ∈ Y) {N : HashOutput}
    (hN : Guess.NearCoveredBy X N) : Guess.NearCoveredBy Y N := by
  obtain ⟨k, t, hkt⟩ := hN
  exact ⟨k, t, hkt.mono_log h⟩
theorem payoff_le_ΦI (q : Nat) (r : (Bool × QueryLog Requests × List Wots.Entry) × GState) :
    WPair.nearPayoff q (r.1, projS r.2) ≤ ΦI q r.2 := by
  unfold ΦI
  split_ifs with hinv
  · unfold WPair.nearPayoff
    split_ifs with hp
    · obtain ⟨hb, hl, N, hN, hadm, hcov⟩ := hp
      exact mem_win q _ _ _ _ _ hb (hinv.2.1.trans hl) (Or.inr ⟨N, hN, hadm, nearCoveredBy_mono hinv.1 hcov⟩)
    · exact bot_le
  · exact le_top
end ClaudeWCT.W9.T3.Security.CaseC
end
section
namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.BPair (AuxL AuxSpecL LazyMem)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem spmf_ev_mono {α : Type} (p : SPMF α) {f g : α → ENNReal} (h : ∀ x, p x ≠ 0 → f x ≤ g x) :
    expectedValue p f ≤ expectedValue p g := by
  unfold expectedValue
  apply ENNReal.tsum_le_tsum
  intro x
  rw [SPMF.probOutput_eq_apply]
  by_cases hx : p x = 0
  · simp [hx]
  · exact mul_le_mul' le_rfl (h x hx)
theorem spmf_ev_le {α : Type} (p : SPMF α) {f : α → ENNReal} {c : ENNReal} (h : ∀ x, p x ≠ 0 → f x ≤ c) :
    expectedValue p f ≤ c :=
  (spmf_ev_mono p h).trans (expectedValue_le_of_le p fun _ => le_rfl)
theorem superProg_of_memory {β : Type} (slot q : Nat) (W : OracleComp WPair.WSpecL β)
    (h : ∀ s r, SecretGuessObservation.runWith (implG slot) W s r ≠ 0 → r.2.memory = s.memory) :
    SuperProg (implG slot) (ΦI q) W := by
  intro s
  apply spmf_ev_le
  intro r hr
  unfold ΦI
  rw [h s r hr]
theorem coin_memory (slot n : Nat) (s : GState) (r : Fin (n + 1) × GState)
    (hr : SecretGuessObservation.runWith (implG slot) (WPair.coinReqL n) s r ≠ 0) : r.2.memory = s.memory := by
  obtain ⟨res, hres, rfl⟩ := aux_nonzero slot (.coin n) s r hr
  have hres' : res ∈ (WPair.envL.auxiliary (projS s) (.coin n)).support := (PMF.mem_support_iff _ _).mpr hres
  change res ∈ ((fun c => (c, (projS s).memory)) <$> PMF.uniformOfFintype (Fin (n + 1))).support at hres'
  rw [PMF.monad_map_eq_map, PMF.mem_support_map_iff] at hres'
  obtain ⟨c, -, rfl⟩ := hres'
  rfl
theorem secret_memory {β : Type} (slot : Nat) (p : (Guess.GCoord × Digest) ⊕ Guess.GCoord)
    (s : GState) (r : (WPair.WSpecL.Range (.inr p)) × GState)
    (hr : SecretGuessObservation.runWith (implG slot) (liftM (WPair.WSpecL.query (.inr p))) s r ≠ 0) :
    r.2.memory = s.memory := by
  unfold SecretGuessObservation.runWith at hr
  rw [simulateQ_spec_query] at hr
  rcases p with ⟨c, v⟩ | c
  · change ((fun hit => (hit, SecretGuessObservation.afterTrial (envG WPair.envL) s c v hit)) <$>
      SecretGuessObservation.forcedTrialWith samplerG slot s c v) r ≠ 0 at hr
    simp only [map_eq_bind_pure_comp, RetainedObservation.bind_nonzero, Function.comp_def, ne_eq,
      SPMF.pure_apply_eq_zero_iff, not_not] at hr
    obtain ⟨hit, -, rfl⟩ := hr
    rfl
  · change ((fun value => (value, SecretGuessObservation.afterDisclosure (envG WPair.envL) s c value)) <$>
      samplerG.discloseLaw s c) r ≠ 0 at hr
    simp only [map_eq_bind_pure_comp, RetainedObservation.bind_nonzero, Function.comp_def, ne_eq,
      SPMF.pure_apply_eq_zero_iff, not_not] at hr
    obtain ⟨value, -, rfl⟩ := hr
    rfl
theorem coin_ΦI (slot q n : Nat) : SuperProg (implG slot) (ΦI q) (WPair.coinReqL n) :=
  superProg_of_memory slot q _ fun s r hr => coin_memory slot n s r hr
theorem guess_ΦI (slot q : Nat) (c : Guess.GCoord) (v : Digest) :
    SuperProg (implG slot) (ΦI q) (Guess.trialQ (auxSpec := AuxSpecL) c v) :=
  superProg_of_memory slot q _ fun s r hr => secret_memory (β := Bool) slot (.inl (c, v)) s r hr
theorem disclose_ΦI (slot q : Nat) (c : Guess.GCoord) :
    SuperProg (implG slot) (ΦI q) (Guess.discloseQ (auxSpec := AuxSpecL) (V := Digest) c) :=
  superProg_of_memory slot q _ fun s r hr => secret_memory (β := Digest) slot (.inr c) s r hr
theorem mapM_ΦI {α β : Type} (slot q : Nat) (f : α → OracleComp WPair.WSpecL β)
    (hf : ∀ a, SuperProg (implG slot) (ΦI q) (f a)) :
    ∀ l : List α, SuperProg (implG slot) (ΦI q) (l.mapM f)
  | [] => superProg_pure _ _ _
  | a :: l => by
      rw [List.mapM_cons]
      exact superProg_bind _ _ (hf a) fun _ => superProg_bind _ _ (mapM_ΦI slot q f hf l) fun _ => superProg_pure _ _ _
theorem discloseAll_ΦI (slot q : Nat) (cs : List Guess.GCoord) :
    SuperProg (implG slot) (ΦI q) (Guess.discloseAll (auxSpec := AuxSpecL) (V := Digest) cs) :=
  mapM_ΦI slot q _ (fun c => disclose_ΦI slot q c) cs
theorem probeW_ΦI (slot q : Nat) {R : Type} (step : Guess.ChainAddr → Fin 4 → Digest → R)
    (top : Guess.ChainAddr → R) (miss : R) (a : Guess.ChainAddr) (p : Fin 4) (v : Digest) :
    SuperProg (implG slot) (ΦI q) (Guess.probeW (auxSpec := AuxSpecL) step top miss a p v) := by
  unfold Guess.probeW
  refine superProg_bind _ _ (guess_ΦI slot q (a, p) v) fun hit => ?_
  split
  · split
    · exact superProg_bind _ _ (disclose_ΦI slot q _) fun _ => superProg_pure _ _ _
    · exact superProg_pure _ _ _
  · exact superProg_pure _ _ _
theorem finishL_ΦI {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (slot q : Nat) (ω : CanonTable.Omega U)
    (request : Request) (rho : Digest) (found : Option (BitVec 32 × HashOutput)) :
    SuperProg (implG slot) (ΦI q) (WPair.finishL hU ω request rho found) := by
  rcases found with _ | ⟨c, output⟩
  · exact superProg_pure _ _ _
  · simp only [WPair.finishL]
    generalize WPair.signerLayersW hU ω request output = g
    cases g with
    | none => exact superProg_pure _ _ _
    | some pieces =>
        refine superProg_bind _ _ (discloseAll_ΦI slot q _) ?_
        intro values
        exact superProg_pure _ _ _
theorem ev_uniform_digest (g : Digest → ENNReal) :
    expectedValue (PMF.uniformOfFintype Digest) g = expectedValue ($ᵗ Digest : ProbComp Digest) g := by
  rw [expectedValue_uniformOfFintype, BPORS.expected_uniform_eq_finiteAverage]
theorem ev_single_aux (slot : Nat) (i : AuxL) (s : GState) (G : AuxSpecL.Range i × GState → ENNReal) :
    expectedValue (SecretGuessObservation.runWith (implG slot) (liftM (WPair.WSpecL.query (.inl i))) s) G =
      expectedValue (WPair.envL.auxiliary (projS s) i) (fun r =>
        G (r.1, { s with memory := (r.2, ghostStep s.memory.1 i r.1 s.memory.2) })) := by
  have h := ev_aux_bind slot i pure s G
  rw [bind_pure] at h
  rw [h]
  apply congrArg
  funext r
  rw [runWith_pure', expectedValue_pure]
theorem birth_ΦI (slot q : Nat) (x : HashInput) : SuperProg (implG slot) (ΦI q) (WPair.birthReq x) := by
  intro s
  by_cases hinv : InvM s.memory
  swap
  · unfold ΦI; rw [if_neg hinv]; exact le_top
  unfold WPair.birthReq
  rw [ev_single_aux]
  change expectedValue (BPair.rowStep s.memory.1 x true (PMF.uniformOfFintype HashOutput)) _ ≤ _
  unfold BPair.rowStep
  cases hx : s.memory.1.rows x with
  | some a =>
      simp only
      rw [expectedValue_pure]
      exact le_of_eq rfl
  | none =>
      simp only
      split_ifs with hd
      · rw [expectedValue_map, ev_uniform_eq]
        have hpt : ∀ a : HashOutput, ΦI q { s with memory := (s.memory.1.readRow x a true,
            ghostStep s.memory.1 (.birth x) a s.memory.2) } =
            nearMemPotential q (s.memory.1.births ++ [a]) s.memory.2.fresh s.memory.2.reused
              (s.memory.1.rows.cacheQuery x a) s.memory.1.nonces := by
          intro a
          have hext : Extends s.memory.1.rows (s.memory.1.rows.cacheQuery x a) := by
            intro y b hy
            have hne : y ≠ x := fun he => by rw [he, hx] at hy; cases hy
            exact (QueryCache.cacheQuery_of_ne s.memory.1.rows a hne).trans hy
          have hinv' : InvM (s.memory.1.readRow x a true, ghostStep s.memory.1 (.birth x) a s.memory.2) := by
            obtain ⟨h1, h2, h3⟩ := hinv
            refine ⟨h1, h2, fun m rho hm => ?_⟩
            obtain ⟨found, hrep, hf⟩ := h3 m rho hm
            exact ⟨found, hrep.mono hext, hf⟩
          unfold ΦI
          rw [if_pos hinv']
          rfl
        simp_rw [hpt]
        unfold ΦI
        rw [if_pos hinv]
        exact mem_birth q _ _ _ _ _ x hx
      · rw [expectedValue_pure]
        exact le_of_eq rfl
theorem hashL_ΦI {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (slot q : Nat) (ω : CanonTable.Omega U)
    (x : HashInput) : SuperProg (implG slot) (ΦI q) (WPair.hashL hU ω x) := by
  unfold WPair.hashL
  cases Guess.decodeProbe x with
  | some p => exact probeW_ΦI slot q _ _ _ _ _ _
  | none =>
      simp only
      split_ifs
      · exact birth_ΦI slot q x
      · exact superProg_pure _ _ _
end ClaudeWCT.W9.T3.Security.CaseC
end
section
namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.BPair (AuxL AuxSpecL LazyMem)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem spmf_ev_zero {α : Type} (p : SPMF α) {f : α → ENNReal} (h : expectedValue p f = 0) :
    ∀ x, p x ≠ 0 → f x = 0 := by
  intro x hx
  unfold expectedValue at h
  have h0 := ENNReal.tsum_eq_zero.mp h x
  rw [SPMF.probOutput_eq_apply] at h0
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact absurd h1 hx
  · exact h1
theorem pc_ev_offsupport {α : Type} (p : ProbComp α) :
    expectedValue p (fun r => if r ∈ support p then 0 else 1) = 0 := by
  unfold expectedValue
  apply ENNReal.tsum_eq_zero.mpr
  intro r
  by_cases hr : r ∈ support p
  · simp [hr]
  · simp [hr, probOutput_eq_zero_of_not_mem_support hr]
theorem search_support (slot : Nat) (rho : Digest) (m : Message) (s : GState) (r)
    (hr : SecretGuessObservation.runWith (implG slot) (WPair.searchL rho m 0 WCT9.digestAttemptLimit) s r ≠ 0) :
    (r.1, r.2.memory.1.rows) ∈
      support (Sampling.roRun 0 (nearSpec.search rho m 0 WCT9.digestAttemptLimit) s.memory.1.rows) := by
  have hlaw := search_law slot rho m (fun f rows =>
    if (f, rows) ∈ support (Sampling.roRun 0 (nearSpec.search rho m 0 WCT9.digestAttemptLimit) s.memory.1.rows)
    then 0 else 1) WCT9.digestAttemptLimit 0 s
  simp only [Prod.mk.eta] at hlaw
  rw [pc_ev_offsupport] at hlaw
  have h0 := spmf_ev_zero _ hlaw r hr
  by_contra hc
  rw [if_neg hc] at h0
  exact one_ne_zero h0
theorem ev_nonce_cached {β : Type} (slot : Nat) (m : Message) (rho : Digest)
    (k : Digest → OracleComp WPair.WSpecL β) (s : GState) (hn : s.memory.1.nonces m = some rho)
    (G : β × GState → ENNReal) :
    expectedValue (SecretGuessObservation.runWith (implG slot) (WPair.nonceReq m >>= k) s) G =
      expectedValue (SecretGuessObservation.runWith (implG slot) (k rho)
        ⟨s.allowed, s.retired, s.guesses, s.probes, (s.memory.1, ghostStep s.memory.1 (.nonce m) rho s.memory.2)⟩) G := by
  unfold WPair.nonceReq
  rw [ev_aux_bind]
  change expectedValue (BPair.nonceStep s.memory.1 m (PMF.uniformOfFintype Digest)) _ = _
  unfold BPair.nonceStep
  rw [hn]
  simp only
  rw [expectedValue_pure]
theorem ev_nonce_fresh {β : Type} (slot : Nat) (m : Message) (k : Digest → OracleComp WPair.WSpecL β)
    (s : GState) (hn : s.memory.1.nonces m = none) (G : β × GState → ENNReal) :
    expectedValue (SecretGuessObservation.runWith (implG slot) (WPair.nonceReq m >>= k) s) G =
      expectedValue ($ᵗ Digest : ProbComp Digest) (fun v =>
        expectedValue (SecretGuessObservation.runWith (implG slot) (k v)
          ⟨s.allowed, s.retired, s.guesses, s.probes,
            (s.memory.1.drawNonce m v, ghostStep s.memory.1 (.nonce m) v s.memory.2)⟩) G) := by
  unfold WPair.nonceReq
  rw [ev_aux_bind]
  change expectedValue (BPair.nonceStep s.memory.1 m (PMF.uniformOfFintype Digest)) _ = _
  unfold BPair.nonceStep
  rw [hn]
  simp only
  rw [expectedValue_map, ev_uniform_digest]
theorem ev_expose_finish_le {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (slot q : Nat)
    (ω : CanonTable.Omega U) (request : Request) (rho : Digest) (found : Option (BitVec 32 × HashOutput))
    (s2 : GState) :
    expectedValue (SecretGuessObservation.runWith (implG slot)
      (WPair.exposeReq (found.map Prod.snd) >>= fun _ => WPair.finishL hU ω request rho found) s2)
      (fun r => ΦI q r.2) ≤
    ΦI q ⟨s2.allowed, s2.retired, s2.guesses, s2.probes, (s2.memory.1.expose (found.map Prod.snd),
      ghostStep s2.memory.1 (.expose (found.map Prod.snd)) () s2.memory.2)⟩ := by
  unfold WPair.exposeReq
  rw [ev_aux_bind]
  change expectedValue (pure ((), s2.memory.1.expose (found.map Prod.snd)) : PMF _) _ ≤ _
  rw [expectedValue_pure]
  exact finishL_ΦI hU slot q ω request rho found _
theorem signL_ΦI {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (slot q : Nat) (ω : CanonTable.Omega U)
    (published : SigGolfCandidate.T3.Cache) (request : Request) :
    SuperProg (implG slot) (ΦI q) (WPair.signL hU ω published request) := by
  unfold WPair.signL
  rcases Classical.em (request.cache = published) with hc | hc
  swap
  · simp only [hc, ↓reduceIte]
    exact superProg_pure _ _ _
  simp only [hc, ↓reduceIte]
  intro s
  by_cases hinv : InvM s.memory
  swap
  · unfold ΦI; rw [if_neg hinv]; exact le_top
  set m := request.message with hm
  obtain ⟨hI1, hI2, hI3⟩ := hinv
  have hΦs : ΦI q s = ghostPot q s.memory := by unfold ΦI; rw [if_pos ⟨hI1, hI2, hI3⟩]
  cases hn : s.memory.1.nonces m with
  | some rho =>
      rw [ev_nonce_cached slot m rho _ s hn, runWith_bind', expectedValue_bind]
      apply spmf_ev_le
      intro r hr
      refine (ev_expose_finish_le hU slot q ω request rho r.1 r.2).trans ?_
      obtain ⟨found0, hrep, hf0⟩ := hI3 m rho hn
      have hsupp := search_support slot rho m _ r hr
      obtain ⟨-, -, -, -, hg, hnon, hbir, hexp⟩ := search_frame slot rho m WCT9.digestAttemptLimit 0 _ r hr
      have hrr := hrep s.memory.1.rows (Extends.refl _) _ hsupp
      simp only [Prod.mk.injEq] at hrr
      obtain ⟨hfound, hrows⟩ := hrr
      have hg' : r.2.memory.2 = ⟨s.memory.2.reused, false, s.memory.2.fresh⟩ := by
        rw [hg]
        simp only [ghostStep, hn, reduceCtorEq, decide_false, Bool.false_and, Bool.or_false]
      have hnon' : r.2.memory.1.nonces = s.memory.1.nonces := hnon
      have hbir' : r.2.memory.1.births = s.memory.1.births := hbir
      have hexp' : r.2.memory.1.exposures = s.memory.1.exposures := hexp
      have hinv' : InvM (r.2.memory.1.expose (r.1.map Prod.snd),
          ghostStep r.2.memory.1 (.expose (r.1.map Prod.snd)) () r.2.memory.2) := by
        rw [hg']
        simp only [ghostStep, Bool.false_eq_true, if_false]
        refine ⟨fun v hv => ?_, ?_, fun m' rho' hm' => ?_⟩
        · simp only [LazyMem.expose, List.mem_append] at hv
          rcases hv with hv | hv
          · rw [hexp'] at hv; exact hI1 v hv
          · rw [hfound] at hv; exact hf0 v hv
        · simp only [LazyMem.expose, List.length_append]
          rw [hexp']
          exact hI2.trans (Nat.le_add_right _ _)
        · simp only [LazyMem.expose] at hm' ⊢
          rw [hnon'] at hm'
          rw [hrows]
          exact hI3 m' rho' hm'
      rw [hΦs]
      unfold ΦI
      dsimp only
      rw [if_pos hinv']
      apply le_of_eq
      unfold ghostPot
      rw [hg']
      simp only [ghostStep, Bool.false_eq_true, if_false, LazyMem.expose]
      rw [hbir', hrows, hnon']
  | none =>
      rw [ev_nonce_fresh slot m _ s hn, hΦs]
      refine le_trans ?_ (mem_sign_fresh q _ _ _ _ _ m hn 0 WCT9.digestAttemptLimit WCT9.digestAttemptLimit_le)
      apply expectedValue_mono
      intro v
      rw [runWith_bind', expectedValue_bind]
      set s1 : GState := ⟨s.allowed, s.retired, s.guesses, s.probes, (s.memory.1.drawNonce m v,
        ghostStep s.memory.1 (.nonce m) v s.memory.2)⟩ with hs1
      have hg1 : s1.memory.2 = ⟨(s.memory.2.reused || decide (nearSpec.Reuse s.memory.1.rows v m)), true,
          s.memory.2.fresh⟩ := by
        simp only [hs1, ghostStep, hn, decide_true, Bool.true_and]
      refine le_of_le_of_eq ?_ (search_law slot v m (fun found rows' =>
        nearMemPotential q s.memory.1.births (s.memory.2.fresh ++ (found.map Prod.snd).toList)
          (s.memory.2.reused || decide (nearSpec.Reuse s.memory.1.rows v m)) rows'
          (Function.update s.memory.1.nonces m (some v))) WCT9.digestAttemptLimit 0 s1)
      apply spmf_ev_mono
      intro r hr
      refine (ev_expose_finish_le hU slot q ω request v r.1 r.2).trans (le_of_eq ?_)
      have hsupp := search_support slot v m s1 r hr
      obtain ⟨hext, hrep⟩ := replays_of_search v m _ _ hsupp
      obtain ⟨-, -, -, -, hg, hnon, hbir, hexp⟩ := search_frame slot v m WCT9.digestAttemptLimit 0 s1 r hr
      have hnon1 : r.2.memory.1.nonces = Function.update s.memory.1.nonces m (some v) := hnon
      have hbir1 : r.2.memory.1.births = s.memory.1.births := hbir
      have hexp1 : r.2.memory.1.exposures = s.memory.1.exposures := hexp
      have hext1 : Extends s.memory.1.rows r.2.memory.1.rows := hext
      have hgr : r.2.memory.2 = ⟨(s.memory.2.reused || decide (nearSpec.Reuse s.memory.1.rows v m)), true,
          s.memory.2.fresh⟩ := hg.trans hg1
      have hinv' : InvM (r.2.memory.1.expose (r.1.map Prod.snd),
          ghostStep r.2.memory.1 (.expose (r.1.map Prod.snd)) () r.2.memory.2) := by
        rw [hgr]
        simp only [ghostStep, if_true]
        refine ⟨fun x hx => ?_, ?_, fun m' rho' hm' => ?_⟩
        · simp only [LazyMem.expose, List.mem_append] at hx ⊢
          rcases hx with hx | hx
          · rw [hexp1] at hx; exact Or.inl (hI1 x hx)
          · exact Or.inr hx
        · simp only [LazyMem.expose, List.length_append]
          rw [hexp1]
          exact Nat.add_le_add_right hI2 _
        · simp only [LazyMem.expose] at hm' ⊢
          rw [hnon1] at hm'
          by_cases he : m' = m
          · subst he
            simp only [Function.update_self, Option.some.injEq] at hm'
            subst hm'
            exact ⟨r.1, hrep, fun x hx => List.mem_append_right _ hx⟩
          · rw [Function.update_of_ne he] at hm'
            obtain ⟨f', hrep', hf'⟩ := hI3 m' rho' hm'
            exact ⟨f', hrep'.mono hext1, fun x hx => List.mem_append_left _ (hf' x hx)⟩
      unfold ΦI
      dsimp only
      rw [if_pos hinv']
      unfold ghostPot
      rw [hgr]
      simp only [ghostStep, if_true, LazyMem.expose]
      rw [hbir1, hnon1]
end ClaudeWCT.W9.T3.Security.CaseC
end
section
namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
end SigGolfCandidate.T3.Security.CaseC
end
section
namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M (wrho wdc)
open ClaudeWCT.W9.T3M (WBytes Shaped)
open ClaudeWCT.W9.T3M.Final (AdversaryP ForgeryP)
open SigGolfCandidate.T3M.SecurityExtraction (queried)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem honestMsg_short {A T : Correctness.Answers} (h : SigGolfCandidate.T3.Security.Wots.Ref.ShortAgree A T)
    (index : Nat) (lay : Layer) :
    ClaudeWCT.W9.T3M.Extract.honestMsg A index lay = ClaudeWCT.W9.T3M.Extract.honestMsg T index lay := by
  unfold ClaudeWCT.W9.T3M.Extract.honestMsg
  split_ifs
  · unfold ClaudeWCT.W9.T3M.Extract.honestPair
    rw [ClaudeWCT.W9.T3.Security.Wots.Ref.wotsTree_short h]
  · rw [ClaudeWCT.W9.T3.Security.Wots.Ref.honestTop_short h _]
theorem good_short {A T : Correctness.Answers} (h : SigGolfCandidate.T3.Security.Wots.Ref.ShortAgree A T) (w : WBytes)
    (index : Nat) (lay : Layer) (hg : ClaudeWCT.W9.T3M.Extract.Good A w index lay) :
    ClaudeWCT.W9.T3M.Extract.Good T w index lay := by
  obtain ⟨digits, ⟨hctr, hdec⟩, hpath, hchain, hleaf⟩ := hg
  refine ⟨digits, ⟨hctr, ?_⟩, ?_, ?_, hleaf⟩
  · rw [← honestMsg_short h]
    rw [← ClaudeWCT.W9.T3.Security.Wots.Ref.shortRespects_encodingHash lay _
      (by rw [ClaudeWCT.W9.T3M.BC.layerEncodingRow_length]; unfold SeccLaw.maxInputLength; omega) A T h]
    exact hdec
  · intro j hj
    obtain ⟨h1, h2⟩ := hpath j hj
    exact ⟨by rw [h1, ClaudeWCT.W9.T3.Security.Wots.Ref.wotsTree_short h],
      fun hc => by rw [h2.1 hc, ClaudeWCT.W9.T3.Security.Wots.Ref.honestNonce_short h], h2.2⟩
  · intro i hi
    obtain ⟨h1, h2⟩ := hchain i hi
    refine ⟨?_, h2⟩
    rw [h1]
    unfold WCT9.wotsValue
    rw [ClaudeWCT.W9.T3.Security.Wots.Ref.wotsSeed_short h]
    exact ClaudeWCT.W9.T3.Security.Wots.Ref.chainW_respects _ _ _ _ _ _ _ A T h
theorem goodZ_short {A T : Correctness.Answers} (h : SigGolfCandidate.T3.Security.Wots.Ref.ShortAgree A T)
    (w : WBytes) (index : Nat) (lay : Layer) (hg : ClaudeWCT.W9.T3M.BC.GoodZ A w index lay) :
    ClaudeWCT.W9.T3M.BC.GoodZ T w index lay :=
  ⟨good_short h w index lay hg.1, hg.2⟩
theorem slotDisclosed_short {A T : Correctness.Answers} (h : SigGolfCandidate.T3.Security.Wots.Ref.ShortAgree A T)
    (log : QueryLog Requests) (N : HashOutput) (k : WCT9.Coord) (t : Fin 6) (hd : SlotDisclosed A log N k t) :
    SlotDisclosed T log N k t := by
  obtain ⟨entry, he, signature, output, hs, ho, h1, h2, h3⟩ := hd
  exact ⟨entry, he, signature, output, hs, by rw [← WPair.signedOutput_short h]; exact ho, h1, h2, h3⟩
def NearIn (A : Correctness.Answers) (log : QueryLog Requests) (entries : List Wots.Entry) : Prop :=
  ∃ (m : Message) (w : WBytes) (N : HashOutput) (k : WCT9.Coord) (t : Fin 6) (c : Guess.GCoord),
    (pad64 (digestInput (wrho w) m (wdc w)), N) ∈ entries ∧
    evalWithAnswerFn A (digest (wrho w) m (wdc w)) = N ∧ Shaped N w ∧
    (∀ lay : Layer, ClaudeWCT.W9.T3M.BC.GoodZ A w (WCT9.digestIndex N) lay) ∧ ¬SignedDigest log m w ∧
    log.length ≤ 2 ^ 32 ∧
    c.1 = Guess.chainOf N k t ∧ c.2.val = 4 - Guess.deficit N k t ∧ WPair.GuessedIn A log entries c ∧
    (∀ k' t', (k', t') ≠ (k, t) → SlotDisclosed A log N k' t') ∧ BPB.SignerComplete A
theorem nearIn_short (A T : Correctness.Answers) (log : QueryLog Requests) (entries : List Wots.Entry)
    (h : SigGolfCandidate.T3.Security.Wots.Ref.ShortAgree A T) (hn : NearIn A log entries) : NearIn T log entries := by
  obtain ⟨m, w, N, k, t, c, hx, hN, hS, hgood, hsd, hlen, h1, h2, hguess, hdis, hcomp⟩ := hn
  refine ⟨m, w, N, k, t, c, hx, ?_, hS, fun lay => goodZ_short h w _ lay (hgood lay), hsd, hlen, h1, h2,
    WPair.guessedIn_short h log entries c hguess, fun k' t' hne => slotDisclosed_short h log N k' t' (hdis k' t' hne),
    BPB.signerComplete_short h hcomp⟩
  rw [← WPair.eval_congr_allowed (WPair.digest_short _ _ _) h]
  exact hN
theorem nearIn_mono (A : Correctness.Answers) (log : QueryLog Requests) (entries entries' : List Wots.Entry)
    (hsub : ∀ e ∈ entries, e ∈ entries') (hn : NearIn A log entries) : NearIn A log entries' := by
  obtain ⟨m, w, N, k, t, c, hx, hN, hS, hgood, hsd, hlen, h1, h2, hguess, hdis, hcomp⟩ := hn
  exact ⟨m, w, N, k, t, c, hsub _ hx, hN, hS, hgood, hsd, hlen, h1, h2,
    WPair.guessedIn_mono A log entries entries' hsub c hguess, hdis, hcomp⟩
theorem near_shared (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (z : PaddedGame.TraceResult × Correctness.Answers) (hz : z ∈ (SeccLaw.completedExperiment adversary q hq).support)
    (hclean : QueryRecorded.CleanWin q z.1) (hnear : PinnedC caseCExtraction adversary NearQ z) :
    ∀ generated interaction checked, GameSplit adversary (QueryRecorded.recordedTrace z.1) generated interaction
      checked → NearIn z.2 interaction.value.2 (SigGolfCandidate.T3.Security.BPair.publicEntries checked.events) := by
  obtain ⟨g, i, c, hs, hpk, hlen, f, hf, hfr, m, w, hof, hsd, hCat, hQ⟩ := hnear
  intro g' i' c' hs'
  obtain ⟨hg', hi', hce⟩ := split_events_unique adversary _ g i c g' i' c' hs hs'
  rw [hce, hi']
  have hagree := (SeccLaw.completed_agrees adversary q hq z hz).2
  have hstate : c.state = z.1.2.2.base.source.2 := (congrArg FirstHit.Recorded.state hs.2.2.2).symm
  have hvalue : c.value = true := (congrArg FirstHit.Recorded.value hs.2.2.2).symm.trans hclean.1
  have ha : ∀ input answer, SourceReplay.known c.state input = some answer → z.2 input = answer :=
    fun input answer hk => hagree input answer (by rw [← hstate]; exact hk)
  obtain ⟨N, -, hN, -, hS, hgood, -, hcomp⟩ := (show BPB.CaseCAt z.2 m w _ from hCat)
  obtain ⟨check, hcheck, hev, hst, m', w', hof', hv, hsub⟩ :=
    verdict_accepting g.value.1 i.value i.state c hs.2.2.1 z.2 ha hvalue f hf
  obtain ⟨rfl, rfl⟩ := witnessOf_unique hof hof'
  obtain ⟨N', -, hN', hdq, -⟩ := ClaudeWCT.W9.T3M.WctExtract.verifyP_walk_wct z.2 m g.value.1 w hv
  have hNN : N' = N := hN'.symm.trans hN
  subst hNN
  obtain ⟨prior, hevent⟩ := SigGolfCandidate.T3.Security.PaddedExtraction.public_occurrence _
    (PaddedExtraction.check_hashOnly _ _ f) _ check hcheck z.2 (by rw [hst]; exact ha) _ (hsub _ hdq)
  rw [hev] at hevent
  have hans : z.2 (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w))))) = N' := hN'
  rw [hans] at hevent
  obtain ⟨k, t, c0, h1, h2, hguess, hdis⟩ := hQ
  rw [hN'] at h1 h2 hdis
  exact ⟨m, w, N', k, t, c0, SigGolfCandidate.T3.Security.CaseC.mem_publicEntries hevent, hN', hS, hgood, hsd, hlen,
    h1, h2, hguess, hdis, hcomp⟩
theorem caseC_not_signer_eval (answers : Correctness.Answers) (published : SigGolfCandidate.T3.Cache)
    (log : QueryLog Requests)
    (hsig : ∀ entry ∈ log, entry.2 = evalWithAnswerFn answers (FullGame.authenticatedSign published entry.1))
    (m : Message) (w : WBytes) (hcomp : BPB.SignerComplete answers) (hfresh : ¬SignedDigest log m w) :
    ∀ entry ∈ log, (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : SigGolfCandidate.T3.Spec.Domain) ∉
      queried answers (FullGame.authenticatedSign published entry.1) := by
  intro entry he hq
  obtain ⟨hc, hm, hrho, -⟩ := BPB.signer_digest_query answers published entry.1 _ _ _ hq
  obtain ⟨sig, hsig', hsrho⟩ := BPB.payload_succeeds_of_complete answers hcomp published (wrho w) m
  apply hfresh
  refine ⟨entry, he, hm, sig, ?_, hsrho⟩
  rw [hsig entry he, BPB.eval_authenticatedSign, if_pos hc, ← hrho, hm]
  exact hsig'
end ClaudeWCT.W9.T3.Security.CaseC
end
section
namespace ClaudeWCT.W9.T3.Security.WPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M.Final (AdversaryP)
open SigGolfCandidate.T3.Security.BPair (LazyMem)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section WorldBoundL
open SecretGuessObservation (fixedRun withRun)
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)
/-- The eager family world of the near experiment is bounded by the lazy family engine (`Guess.Fam.fam_erasure`). -/
theorem fts_event_le_worldL (adversary : AdversaryP)
    (event : CanonTable.HiddenF → (Bool × QueryLog Requests × List Wots.Entry) → Prop)
    (wevent : (Bool × QueryLog Requests × List Wots.Entry) × WStateL → Prop)
    (himp : ∀ g result, fixedRun (envE (digestOf ω) (nonceOf ω)) (Guess.Fam.phi g.1 g.2)
      (worldGameL hU ω adversary) initL result ≠ 0 → event g result.1 → wevent result) :
    Pr[fun x => event x.1 x.2 | ftsRun hU ω adversary] ≤
      Pr[wevent | withRun (envE (digestOf ω) (nonceOf ω)) samplerL (worldGameL hU ω adversary) initL] := by
  rw [← Guess.Fam.fam_erasure (envE (digestOf ω) (nonceOf ω)) (worldGameL hU ω adversary) initL
    (Guess.Fam.inv_initial LazyMem.empty)]
  change _ ≤ Pr[wevent | Guess.Fam.hiddenLaw (fun _ => Finset.univ) >>= fun g =>
    fixedRun (envE (digestOf ω) (nonceOf ω)) g (worldGameL hU ω adversary) initL]
  rw [hiddenLaw_univ_bind]
  unfold ftsRun
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro g
  apply mul_le_mul' le_rfl
  rw [probEvent_map, ← fixed_worldGameL hU ω g adversary, probEvent_map]
  apply probEvent_mono
  intro result hr he
  exact himp g result (by simpa only [mem_support_iff, SPMF.probOutput_eq_apply] using hr) he
end WorldBoundL
section Chain
/-- First-guess forcing for the near experiment over FTS seed families; `hno` supplies `¬Guess.Fam.Bad`. -/
theorem near_chain_slot (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (P : Answers → QueryLog Requests → List Wots.Entry → Prop)
    (hshort : ∀ A T log entries, Wots.Ref.ShortAgree A T → P A log entries → P T log entries)
    (hmono : ∀ A log entries entries', (∀ e ∈ entries, e ∈ entries') → P A log entries → P A log entries')
    (hno : ∀ A log entries, P A log entries → ¬OverflowIn A log)
    (payoff : Nat → (Bool × QueryLog Requests × List Wots.Entry) × WStateL → ENNReal)
    (hevent : ∀ ω g r, SecretGuessObservation.fixedRun (envE (digestOf ω) (nonceOf ω)) (Guess.Fam.phi g.1 g.2)
        (worldGameL (canon_subset adversary) ω adversary) initL r ≠ 0 →
      r.1.2.2.length ≤ q → P (wA (canon_subset adversary) ω g) r.1.2.1 r.1.2.2 →
      r.2.guesses.Nonempty ∧ ∀ slot < r.2.probes, 1 ≤ payoff slot r) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ ∀ generated interaction checked,
        CaseC.GameSplit adversary (QueryRecorded.recordedTrace z.1) generated interaction checked →
          P z.2 interaction.value.2 (SigGolfCandidate.T3.Security.BPair.publicEntries checked.events) |
        SeccLaw.completedExperiment adversary q hq] ≤
      ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * ∑ slot ∈ Finset.range q, ∑' ω, Pr[= ω | omegaLaw adversary] *
        ∑' r, Pr[= r | SecretGuessObservation.forcedWithRun envL samplerL slot
          (worldGameL (canon_subset adversary) ω adversary) initL] * payoff slot r := by
  refine (shared_le_pair adversary q hq P hshort hmono).trans ?_
  rw [pairExperiment_avg]
  have hω : ∀ ω : CanonTable.Omega (Wots.referenceInputs adversary),
      Pr[fun x => x.2.2.2.length ≤ q ∧ P (wA (canon_subset adversary) ω x.1) x.2.2.1 x.2.2.2 |
        ftsRun (canon_subset adversary) ω adversary] ≤
      ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * ∑ slot ∈ Finset.range q, ∑' r,
        Pr[= r | SecretGuessObservation.forcedWithRun (envE (digestOf ω) (nonceOf ω)) samplerL slot
          (worldGameL (canon_subset adversary) ω adversary) initL] * payoff slot r := by
    intro ω
    refine (fts_event_le_worldL (canon_subset adversary) ω adversary
      (fun g run => run.2.2.length ≤ q ∧ P (wA (canon_subset adversary) ω g) run.2.1 run.2.2)
      (fun r => r.2.guesses.Nonempty ∧ r.2.probes ≤ q ∧ ¬Guess.Fam.Bad r.2 ∧ ∀ slot < r.2.probes, 1 ≤ payoff slot r)
      ?_).trans ?_
    · rintro g r hr ⟨hlen, hP⟩
      obtain ⟨hg, hp⟩ := hevent ω g r hr hlen hP
      exact ⟨hg, (worldGameL_tracking (canon_subset adversary) ω g adversary r hr).1.trans hlen,
        worldGameL_noBad (canon_subset adversary) ω g adversary r hr (hno _ _ _ hP), hp⟩
    · exact Guess.Fam.fam_event_le_forced_slot (envE (digestOf ω) (nonceOf ω))
        (worldGameL (canon_subset adversary) ω adversary) LazyMem.empty q _ payoff (fun _ _ h => h)
  calc (∑' ω, Pr[= ω | omegaLaw adversary] *
        Pr[fun x => x.2.2.2.length ≤ q ∧ P (wA (canon_subset adversary) ω x.1) x.2.2.1 x.2.2.2 |
          ftsRun (canon_subset adversary) ω adversary])
      ≤ ∑' ω, Pr[= ω | omegaLaw adversary] * (((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * ∑ slot ∈ Finset.range q, ∑' r,
          Pr[= r | SecretGuessObservation.forcedWithRun (envE (digestOf ω) (nonceOf ω)) samplerL slot
            (worldGameL (canon_subset adversary) ω adversary) initL] * payoff slot r) :=
        ENNReal.tsum_le_tsum fun ω => mul_le_mul' le_rfl (hω ω)
    _ = ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * ∑ slot ∈ Finset.range q, ∑' ω, Pr[= ω | omegaLaw adversary] *
          ∑' r, Pr[= r | SecretGuessObservation.forcedWithRun (envE (digestOf ω) (nonceOf ω)) samplerL slot
            (worldGameL (canon_subset adversary) ω adversary) initL] * payoff slot r := by
        simp only [Finset.mul_sum, mul_left_comm (Pr[= _ | omegaLaw adversary])]
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        exact Finset.sum_congr rfl fun slot _ => ENNReal.tsum_mul_left
    _ = _ := congrArg (fun t => ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * t)
        (Finset.sum_congr rfl fun slot _ => forced_avg_eq_lazy adversary slot (payoff slot))
end Chain
end ClaudeWCT.W9.T3.Security.WPair
end
section
namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M (wrho wdc)
open ClaudeWCT.W9.T3M (WBytes Shaped)
open ClaudeWCT.W9.T3M.Final (AdversaryP ForgeryP)
open SigGolfCandidate.T3M.SecurityExtraction (queried)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem interactionT_honest (T : Correctness.Answers) (published : SigGolfCandidate.T3.Cache) {α : Type}
    (oa : OracleComp LazyPrivate.Interaction α) (r : α × QueryLog Requests × List Wots.Entry)
    (hr : r ∈ support (WPair.interactionT T published oa)) :
    (∀ e ∈ r.2.1, e.2 = evalWithAnswerFn T (FullGame.authenticatedSign published e.1)) ∧
      ∀ e ∈ r.2.2, e.2 = T (.inl (.inr e.1)) := by
  induction oa using OracleComp.inductionOn generalizing r with
  | pure value =>
      rw [WPair.interactionT_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr
      simp
  | query_bind input next ih =>
      rcases input with (n | x) | request
      · rw [WPair.interactionT_coin, mem_support_bind_iff] at hr
        obtain ⟨coin, -, hr⟩ := hr
        exact ih coin r hr
      · rw [WPair.interactionT_public, mem_support_bind_iff] at hr
        obtain ⟨rest, hrest, hr⟩ := hr
        rw [support_pure, Set.mem_singleton_iff] at hr
        subst hr
        obtain ⟨h1, h2⟩ := ih _ rest hrest
        refine ⟨h1, fun e he => ?_⟩
        rcases List.mem_cons.mp he with he | he
        · subst he; rfl
        · exact h2 e he
      · rw [WPair.interactionT_request, mem_support_bind_iff] at hr
        obtain ⟨rest, hrest, hr⟩ := hr
        rw [support_pure, Set.mem_singleton_iff] at hr
        subst hr
        obtain ⟨h1, h2⟩ := ih _ rest hrest
        refine ⟨fun e he => ?_, h2⟩
        rcases List.mem_cons.mp he with he | he
        · subst he; rfl
        · exact h1 e he
theorem entriesOf_honest (T : Correctness.Answers) (qs : List SigGolfCandidate.T3.Spec.Domain) :
    ∀ e ∈ Wots.entriesOf T qs, e.2 = T (.inl (.inr e.1)) := by
  intro e he
  unfold Wots.entriesOf at he
  rw [List.mem_filterMap] at he
  obtain ⟨q, -, hq⟩ := he
  rcases q with (c | input) | p
  · cases hq
  · cases hq; rfl
  · cases hq
theorem pairRun_honest (T : Correctness.Answers) (adversary : AdversaryP)
    (r : Bool × QueryLog Requests × List Wots.Entry) (hr : r ∈ support (WPair.pairRun T adversary)) :
    (∀ e ∈ r.2.1, e.2 = evalWithAnswerFn T (FullGame.authenticatedSign
        (evalWithAnswerFn T SigGolfCandidate.T3.keygen).2 e.1)) ∧
      ∀ e ∈ r.2.2, e.2 = T (.inl (.inr e.1)) := by
  unfold WPair.pairRun at hr
  rw [mem_support_bind_iff] at hr
  obtain ⟨interaction, hi, hr⟩ := hr
  rw [support_pure, Set.mem_singleton_iff] at hr
  subst hr
  obtain ⟨h1, h2⟩ := interactionT_honest T _ _ interaction hi
  refine ⟨h1, fun e he => ?_⟩
  rcases List.mem_append.mp he with he | he
  · exact h2 e he
  · exact entriesOf_honest T _ e he
theorem payoff_of_ghosts_birthBudget (q : Nat) (T : Correctness.Answers) (published : SigGolfCandidate.T3.Cache)
    (r : (Bool × QueryLog Requests × List Wots.Entry) × WPair.WStateL)
    (hlog : ∀ e ∈ r.1.2.1, e.2 = evalWithAnswerFn T (FullGame.authenticatedSign published e.1))
    (hexp : ∀ entry ∈ r.1.2.1, ∀ σ output, entry.2 = some σ →
      signedOutput T entry.1.message σ = some output → output ∈ r.2.memory.exposures)
    (hrows : ∀ x a, (x, a) ∈ r.1.2.2 → x ∈ SigGolfCandidate.T3.Security.BPair.digestInputs →
      a ∈ r.2.memory.births ∨ x ∈ r.2.memory.trials)
    (htrials : ∀ x ∈ r.2.memory.trials, ∃ entry ∈ r.1.2.1,
      (.inl (.inr x) : SigGolfCandidate.T3.Spec.Domain) ∈ queried T (FullGame.authenticatedSign published entry.1))
    (hbirths : r.2.memory.births.length ≤ q)
    (hexplen : r.2.memory.exposures.length ≤ r.1.2.1.length)
    (hP : NearIn T r.1.2.1 r.1.2.2) : 1 ≤ WPair.nearPayoff q r := by
  obtain ⟨m, w, N, k, t, c, hx, hN, hS, hgood, hsd, hlen, -, -, -, hdis, hcomp⟩ := hP
  have hbirth : N ∈ r.2.memory.births := by
    rcases hrows _ N hx (SigGolfCandidate.T3.Security.BPair.digestInput_mem _ _ _) with hb | ht
    · exact hb
    · exfalso
      obtain ⟨entry, he, hqe⟩ := htrials _ ht
      exact caseC_not_signer_eval T published r.1.2.1 hlog m w hcomp hsd entry he hqe
  have hcov : Guess.NearCoveredBy r.2.memory.exposures N := by
    refine ⟨k, t, fun k' t' hne => ?_⟩
    obtain ⟨entry, he, σ, output, hσ, hout, h1, h2, h3⟩ := hdis k' t' hne
    exact ⟨output, hexp entry he σ output hσ hout, congrArg Fin.val h1, h2, h3⟩
  unfold WPair.nearPayoff
  rw [if_pos ⟨hbirths, hexplen.trans hlen, N, hbirth, hS, hcov⟩]
end ClaudeWCT.W9.T3.Security.CaseC
end
section
namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M.Final (AdversaryP)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem worldGame_ΦI {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)
    (adversary : AdversaryP) (slot q : Nat) :
    SuperProg (implG slot) (ΦI q) (WPair.worldGameCore hU ω adversary) :=
  worldGameCore_super hU (implG slot) (ΦI q) ω adversary (coin_ΦI slot q) (hashL_ΦI hU slot q ω)
    (fun published request => signL_ΦI hU slot q ω published request)
theorem forced_payoff_le {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)
    (adversary : AdversaryP) (slot q : Nat) :
    expectedValue (SecretGuessObservation.forcedWithRun WPair.envL WPair.samplerL slot
      (WPair.worldGameCore hU ω adversary) WPair.initL) (WPair.nearPayoff q) ≤ (q : ENNReal) * 300 / 2 ^ 128 := by
  unfold SecretGuessObservation.forcedWithRun
  rw [← projS_initG, expectedValue_project WPair.envL slot _ initG (WPair.nearPayoff q)]
  calc
    _ ≤ expectedValue (SecretGuessObservation.runWith (implG slot) (WPair.worldGameCore hU ω adversary) initG)
        (fun r => ΦI q r.2) := expectedValue_mono _ fun r => payoff_le_ΦI q r
    _ ≤ ΦI q initG := worldGame_ΦI hU ω adversary slot q initG
    _ ≤ _ := ΦI_initial q
theorem forced_payoff_sum_le {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)
    (adversary : AdversaryP) (slot q : Nat) :
    ∑' r, Pr[= r | SecretGuessObservation.forcedWithRun WPair.envL WPair.samplerL slot
      (WPair.worldGameCore hU ω adversary) WPair.initL] * WPair.nearPayoff q r ≤ (q : ENNReal) * 300 / 2 ^ 128 :=
  forced_payoff_le hU ω adversary slot q
end ClaudeWCT.W9.T3.Security.CaseC
end
section
namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M (WBytes Shaped)
open ClaudeWCT.W9.T3M.Final (AdversaryP ForgeryP)
open SigGolfCandidate.T3.Security.CaseC (pmf_probEvent_mono_support)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
/-- `NearBound` restricted to runs without FTS overflow (same right-hand side; campaign X1, stage A). -/
abbrev NearBoundNO (nearTerm : Nat → ENNReal) : Prop :=
  NearBoundOn caseCExtraction NearQ WPair.NoOverflow nearTerm
/-- The near event in the game split, together with the absence of FTS overflow. -/
def NearAll (adversary : AdversaryP) (q : Nat) (z : PaddedGame.TraceResult × Correctness.Answers) : Prop :=
  QueryRecorded.CleanWin q z.1 ∧ ∀ generated interaction checked,
    GameSplit adversary (QueryRecorded.recordedTrace z.1) generated interaction checked →
      NearIn z.2 interaction.value.2 (SigGolfCandidate.T3.Security.BPair.publicEntries checked.events) ∧
        ¬WPair.OverflowIn z.2 interaction.value.2
theorem near_le_all (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ PinnedC caseCExtraction adversary NearQ z ∧
        WPair.NoOverflow adversary z | SeccLaw.completedExperiment adversary q hq] ≤
      Pr[NearAll adversary q | SeccLaw.completedExperiment adversary q hq] := by
  apply pmf_probEvent_mono_support
  intro z hz h
  exact ⟨h.1, fun g i c hs => ⟨near_shared adversary q hq z hz h.1 h.2.1 g i c hs, h.2.2 g i c hs⟩⟩
theorem omega_avg_le {Ω : Type} (L : ProbComp Ω) (f : Ω → ENNReal) (B : ENNReal) (h : ∀ ω, f ω ≤ B) :
    ∑' ω, Pr[= ω | L] * f ω ≤ B :=
  calc
    _ ≤ ∑' ω, Pr[= ω | L] * B := ENNReal.tsum_le_tsum fun ω => mul_le_mul' le_rfl (h ω)
    _ = (∑' ω, Pr[= ω | L]) * B := ENNReal.tsum_mul_right
    _ ≤ 1 * B := mul_le_mul' tsum_probOutput_le_one le_rfl
    _ = B := one_mul B
theorem fixed_support_pairRun (adversary : AdversaryP) (ω : CanonTable.Omega (Wots.referenceInputs adversary))
    (g : CanonTable.HiddenF) (r : (Bool × QueryLog Requests × List Wots.Entry) × WPair.WStateL)
    (hr : SphincsSecurity.Concrete.SecretGuessObservation.fixedRun (WPair.envE (WPair.digestOf ω) (WPair.nonceOf ω))
      (Guess.Fam.phi g.1 g.2)
      (WPair.worldGameL (WPair.canon_subset adversary) ω adversary) WPair.initL r ≠ 0) :
    r.1 ∈ support (WPair.pairRun (WPair.wA (WPair.canon_subset adversary) ω g) adversary) := by
  rw [mem_support_iff, probOutput_def, ← WPair.fixed_worldGameL (WPair.canon_subset adversary) ω g adversary,
    map_eq_bind_pure_comp]
  rw [SphincsSecurity.Concrete.RetainedObservation.bind_nonzero]
  refine ⟨r, hr, ?_⟩
  simp only [Function.comp_apply, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not]
theorem near_event_slot (adversary : AdversaryP) (q : Nat) (ω : CanonTable.Omega (Wots.referenceInputs adversary))
    (g : CanonTable.HiddenF) (r : (Bool × QueryLog Requests × List Wots.Entry) × WPair.WStateL)
    (hr : SphincsSecurity.Concrete.SecretGuessObservation.fixedRun (WPair.envE (WPair.digestOf ω) (WPair.nonceOf ω))
      (Guess.Fam.phi g.1 g.2)
      (WPair.worldGameL (WPair.canon_subset adversary) ω adversary) WPair.initL r ≠ 0)
    (hq : r.1.2.2.length ≤ q) (hP : NearIn (WPair.wA (WPair.canon_subset adversary) ω g) r.1.2.1 r.1.2.2) :
    r.2.guesses.Nonempty ∧ ∀ slot < r.2.probes, 1 ≤ WPair.nearPayoff (q - (slot + 1)) r := by
  obtain ⟨hexp, hrows, -, htrack, -, htrials, hexplen⟩ :=
    WPair.worldGameL_bank (WPair.canon_subset adversary) ω g adversary r hr
  have hpb := WPair.worldGameL_probes_births (WPair.canon_subset adversary) ω g adversary r hr
  obtain ⟨hlog, -⟩ := pairRun_honest _ adversary r.1 (fixed_support_pairRun adversary ω g r hr)
  refine ⟨?_, fun slot hslot => payoff_of_ghosts_birthBudget (q - (slot + 1)) _ _ r hlog hexp
    (fun x a hx hd => (hrows x a hx hd).2) htrials (by omega) hexplen hP⟩
  obtain ⟨-, -, -, -, -, c, -, -, -, -, -, -, -, -, hguess, -⟩ := hP
  exact Guess.nonempty_of_prefixIn (htrack c hguess)
theorem sum_range_sub_succ_twice_le (q : Nat) :
    (∑ slot ∈ Finset.range q, (q - (slot + 1))) * 2 ≤ q * q := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Finset.sum_range_succ']
      simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
      nlinarith
theorem sum_range_sub_succ_mul_le (q coefficient : Nat) :
    (∑ slot ∈ Finset.range q, (q - (slot + 1))) * (2 * coefficient) ≤ coefficient * q * q := by
  calc
    _ = coefficient * ((∑ slot ∈ Finset.range q, (q - (slot + 1))) * 2) := by ring
    _ ≤ coefficient * (q * q) := Nat.mul_le_mul_left coefficient (sum_range_sub_succ_twice_le q)
    _ = _ := by ring
noncomputable def nearTermTight (q : Nat) : ENNReal :=
  (q : ENNReal) * ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * (150 * q / 2 ^ 128)
theorem nearBoundTight : NearBoundNO nearTermTight := by
  intro adversary q hq _ _
  have hchain := WPair.near_chain_slot adversary q hq
    (fun A log entries => NearIn A log entries ∧ ¬WPair.OverflowIn A log)
    (fun A T log entries h hP => ⟨nearIn_short A T log entries h hP.1,
      fun ho => hP.2 (WPair.overflowIn_short h.symm log ho)⟩)
    (fun A log entries entries' hsub hP => ⟨nearIn_mono A log entries entries' hsub hP.1, hP.2⟩)
    (fun _ _ _ hP => hP.2) (fun slot => WPair.nearPayoff (q - (slot + 1)))
    (fun ω g r hr hlen hP => near_event_slot adversary q ω g r hr hlen hP.1)
  have hslot : ∀ slot, (∑' ω, Pr[= ω | WPair.omegaLaw adversary] *
      ∑' r, Pr[= r | SphincsSecurity.Concrete.SecretGuessObservation.forcedWithRun WPair.envL WPair.samplerL slot
        (WPair.worldGameL (WPair.canon_subset adversary) ω adversary) WPair.initL] * WPair.nearPayoff (q - (slot + 1)) r) ≤
      ((q - (slot + 1) : Nat) : ENNReal) * 300 / 2 ^ 128 :=
    fun slot => omega_avg_le _ _ _ fun ω => forced_payoff_sum_le (WPair.canon_subset adversary) ω adversary slot (q - (slot + 1))
  calc
    _ ≤ Pr[NearAll adversary q | SeccLaw.completedExperiment adversary q hq] := near_le_all adversary q hq
    _ ≤ _ := hchain
    _ ≤ ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * ∑ slot ∈ Finset.range q, ((q - (slot + 1) : Nat) : ENNReal) * 300 / 2 ^ 128 :=
      mul_le_mul' le_rfl (Finset.sum_le_sum fun slot _ => hslot slot)
    _ = ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ *
          ((((∑ slot ∈ Finset.range q, (q - (slot + 1))) * 300 : Nat) : ENNReal) / 2 ^ 128) := by
      congr 1
      push_cast
      simp only [div_eq_mul_inv, ← Finset.sum_mul]
    _ ≤ ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * (((150 * q * q : Nat) : ENNReal) / 2 ^ 128) :=
      mul_le_mul' le_rfl (ENNReal.div_le_div_right (Nat.cast_le.mpr (by simpa using sum_range_sub_succ_mul_le q 150)) _)
    _ = nearTermTight q := by
      unfold nearTermTight
      push_cast
      simp only [div_eq_mul_inv]
      ring
theorem nearTermTight_le (q : Nat) : nearTermTight q ≤ Wots.nearTerm q := by
  unfold nearTermTight Wots.nearTerm
  apply mul_le_mul' le_rfl
  refine le_trans (le_of_eq ?_) (le_self_add.trans le_self_add)
  rfl
/-- The near bound of case C for FTS seed families: unchanged right-hand side, given no FTS overflow. -/
theorem nearBound : NearBoundNO Wots.nearTerm :=
  fun adversary q hq h1 h2 => (nearBoundTight adversary q hq h1 h2).trans (nearTermTight_le q)
end ClaudeWCT.W9.T3.Security.CaseC
end

namespace ClaudeWCT.W9.T3.Security.WPair.Counted
attribute [local instance] Classical.propDecidable
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Mask (queried_length_bind queried_length_pure
  queried_length_shortHash queried_length_privatePair queried_length_foldlM sum_map_one)
open ClaudeWCT.WCT9
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem queried_length_chain (T : Answers) (index coord selected i start count : Nat) (v : Digest) :
    (SourceReplay.queried T (WCT9.chain index coord selected i start count v)).length = count := by
  unfold WCT9.chain
  rw [queried_length_foldlM T _ _ (fun _ => 1) (fun _ _ _ => SigGolfCandidate.T3.Security.Wots.Mask.queried_length_projHash _ _ _),
    sum_map_one, List.length_range']
theorem queried_length_childStep (T : Answers) (index coord selected : Nat) (word : Rank)
    (coefs : List Digest) (state : List Digest × List Digest) (i : Fin 6) :
    (SourceReplay.queried T (childStep index coord selected word coefs state i)).length = 4 := by
  unfold childStep
  rw [queried_length_bind, queried_length_chain, queried_length_bind, queried_length_chain,
    queried_length_pure]
  have h := wordDigit_le_four word i
  omega
theorem queried_length_childRows (T : Answers) (index coord selected : Nat) (word : Rank)
    (coefs : List Digest) :
    (SourceReplay.queried T (childRows index coord selected word coefs)).length = 24 := by
  unfold childRows
  rw [queried_length_foldlM T _ _ (fun _ => 4)
    (fun i _ state => queried_length_childStep T index coord selected word coefs state i)]
  decide
theorem queried_length_buildChildF (T : Answers) (index coord selected : Nat) (word : Rank)
    (coefs : List Digest) (pad : Digest) :
    (SourceReplay.queried T (buildChildF index coord selected word coefs pad)).length = 25 := by
  rw [buildChildF_factor, queried_length_bind, queried_length_childRows,
    queried_length_bind, queried_length_pure]
  rfl
/-- C1: the paired child of heap `heap` makes the same 25 queries. -/
theorem queried_length_buildChildH (T : Answers) (heap index coord selected : Nat) (word : Rank)
    (coefs : List Digest) (pad : Digest) :
    (SourceReplay.queried T (buildChildH heap index coord selected word coefs pad)).length = 25 := by
  rw [buildChildH_factor, queried_length_bind, queried_length_childRows,
    queried_length_bind, queried_length_pure]
  unfold leafHashH ftsHash
  split <;> rfl
theorem queried_length_ftsCoefs (T : Answers) (index coord : Nat) :
    (SourceReplay.queried T (ftsCoefs index coord)).length = 27 := by
  unfold ftsCoefs
  rw [queried_length_foldlM T _ _ (fun _ => 1) (fun _ _ _ => by
    rw [queried_length_bind, queried_length_pure]
    rfl), sum_map_one]
  rfl
theorem queried_length_coordRows (T : Answers) (index : Nat) (coord : Coord) (selected : Child)
    (word : Rank) (coefs : List Digest) (pad : Digest) :
    (SourceReplay.queried T (coordRows index coord selected word coefs pad)).length = 3200 := by
  unfold coordRows
  rw [queried_length_foldlM T _ _ (fun _ => 25) (fun _ _ _ => by
    rw [queried_length_bind, queried_length_buildChildF, queried_length_pure])]
  decide
theorem queried_length_heapNode (T : Answers) (index coord heap : Nat) (pad left right : Digest) :
    (SourceReplay.queried T (wctHeapNode coord index heap pad left right)).length = 1 := by
  unfold wctHeapNode
  split <;> rfl
theorem queried_length_heapBuild (T : Answers) (index coord : Nat) (pad : Digest) (leaves : List Digest) :
    (SourceReplay.queried T (heapBuild index coord pad leaves)).length = 126 := by
  unfold heapBuild
  rw [queried_length_foldlM T _ _ (fun _ => 1) (fun _ _ _ => by
    rw [queried_length_bind, queried_length_heapNode, queried_length_pure]), sum_map_one]
  simp
theorem queried_length_buildCoordinateF (T : Answers) (index : Nat) (coord : Coord) (selected : Child)
    (word : Rank) (prev : Digest × Digest) :
    (SourceReplay.queried T (buildCoordinateF index coord selected word prev)).length = 3353 := by
  rw [buildCoordinateF_factor, queried_length_bind, queried_length_ftsCoefs,
    queried_length_bind, queried_length_coordRows, queried_length_bind, queried_length_heapBuild,
    queried_length_pure]
theorem queried_length_openingStep (T : Answers) (index : Nat) (output : HashOutput)
    (state : List Opening × List (Digest × Digest)) (coord : Coord) :
    (SourceReplay.queried T (openingStep index output state coord)).length = 3353 := by
  unfold openingStep
  rw [queried_length_bind, queried_length_buildCoordinateF, queried_length_pure]
theorem queried_length_forestRows (T : Answers) (index : Nat) (output : HashOutput) :
    (SourceReplay.queried T (forestRows index output)).length = 30177 := by
  unfold forestRows
  rw [queried_length_foldlM T _ _ (fun _ => 3353) (fun _ _ _ => queried_length_openingStep _ _ _ _ _)]
  decide
theorem queried_length_signForest (T : Answers) (index : Nat) (output : HashOutput) :
    (SourceReplay.queried T (signForest index output)).length = 30177 := by
  unfold signForest
  rw [queried_length_bind, queried_length_forestRows, queried_length_pure]

variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)
theorem queried_free (g g' : CanonTable.HiddenF) {α : Type} {program : M α}
    (hp : AllQueriesSatisfy program WFree) :
    SourceReplay.queried (wA hU ω g) program = SourceReplay.queried (wA hU ω g') program :=
  (ClaudeWCT.WCT9.Wots.respects_of_allQueriesSatisfy hp).queried_eq (answers_free hU ω g g')
theorem queried_length_free (g g' : CanonTable.HiddenF) {α : Type} {program : M α}
    (hp : AllQueriesSatisfy program WFree) :
    (SourceReplay.queried (wA hU ω g) program).length =
      (SourceReplay.queried (wA hU ω g') program).length :=
  congrArg List.length (queried_free hU ω g g' hp)
theorem keygenCharge_eq (g g' : CanonTable.HiddenF) :
    SigGolfCandidate.T3.Security.Wots.keygenCharge (wA hU ω g) =
      SigGolfCandidate.T3.Security.Wots.keygenCharge (wA hU ω g') :=
  queried_length_free hU ω g g' keygen_free

theorem queried_length_pure_option (answers : Answers) {α β : Type} (found : Option α)
    (finish : α → β) (fallback : β) :
    (SourceReplay.queried answers (match found with
      | some value => pure (finish value)
      | _ => pure fallback : M β)).length = 0 := by
  cases found <;> exact queried_length_pure _ _

attribute [local irreducible] WCT9.honestTop WCT9.expectedOpening WCT9.signForest
  WCT9.digestSearch WCT9.signLayersBC

theorem signCharge_congr_free (answers answers' : Answers)
    (heval : ∀ {α : Type} {program : M α}, AllQueriesSatisfy program WFree →
      evalWithAnswerFn answers program = evalWithAnswerFn answers' program)
    (hquery : ∀ {α : Type} {program : M α}, AllQueriesSatisfy program WFree →
      (SourceReplay.queried answers program).length = (SourceReplay.queried answers' program).length)
    (hroot : ∀ index < 2 ^ 31, WCT9.honestTop answers index = WCT9.honestTop answers' index)
    (published : SigGolfCandidate.T3.Cache) (request : Request) :
    Wots.signCharge answers published request = Wots.signCharge answers' published request := by
  classical
  unfold Wots.signCharge FullGame.authenticatedSign
  conv_lhs => rw [queried_length_bind]
  conv_rhs => rw [queried_length_bind]
  rw [hquery (privateMac_free _)]
  apply congrArg (Nat.add _)
  rcases Classical.em (request.cache = published) with hc | hc
  · rw [if_pos hc]
    change (SourceReplay.queried answers (WCT9.Rev3.signPayload request.cache request.message)).length =
      (SourceReplay.queried answers' (WCT9.Rev3.signPayload request.cache request.message)).length
    rw [WCT9.Rev3.signPayload_eq]
    conv_lhs => rw [queried_length_bind]
    conv_rhs => rw [queried_length_bind]
    rw [hquery (privateNonce_free _),
      heval (privateNonce_free _)]
    apply congrArg (Nat.add _)
    generalize evalWithAnswerFn answers' (privateNonce request.message) = rho
    conv_lhs => rw [queried_length_bind]
    conv_rhs => rw [queried_length_bind]
    rw [hquery (wctDigestSearch_free _ _ _ _),
      heval (wctDigestSearch_free _ _ _ _)]
    apply congrArg (Nat.add _)
    cases evalWithAnswerFn answers' (WCT9.digestSearch rho request.message 0 WCT9.digestAttemptLimit) with
    | none => rfl
    | some found =>
        obtain ⟨ctr, output⟩ := found
        simp only
        conv_lhs => rw [queried_length_bind, queried_length_signForest, WCT9.eval_signForest]
        conv_rhs => rw [queried_length_bind, queried_length_signForest, WCT9.eval_signForest]
        apply congrArg (Nat.add _)
        simp only
        rw [hroot (WCT9.digestIndex output) (outIndex_lt output)]
        conv_lhs => rw [queried_length_bind]
        conv_rhs => rw [queried_length_bind]
        rw [hquery (signLayersBC_free _ _ _ _),
          heval (signLayersBC_free _ _ _ _)]
        apply congrArg (Nat.add _)
        split <;> (try split) <;> simp only [queried_length_pure]
  · rw [if_neg hc]
    rfl

theorem signCharge_eq (g g' : CanonTable.HiddenF) (published : SigGolfCandidate.T3.Cache)
    (request : Request) :
    Wots.signCharge (wA hU ω g) published request = Wots.signCharge (wA hU ω g') published request :=
  signCharge_congr_free _ _ (fun hp => eval_free hU ω g g' hp)
    (fun hp => queried_length_free hU ω g g' hp)
    (honestForest_world hU ω g g') published request

end ClaudeWCT.W9.T3.Security.WPair.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Counted
attribute [local instance] Classical.propDecidable
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M.Final (AdversaryP)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- `some x` charges and records an external public query; `none` charges one
    query made internally by key generation or an authenticated signing call. -/
abbrev ClockSpec : OracleSpec (Option HashInput) := Option HashInput →ₒ Unit
abbrev CountAux := unifSpec + ClockSpec
abbrev CountSpec := SecretGuessObservation.World CountAux Guess.GCoord Digest
abbrev CountState := SecretGuessObservation.State Guess.GCoord Digest PUnit

def charged : CountSpec.Domain → Prop
  | .inl (.inr _) => True
  | _ => False
instance chargedDecidable : DecidablePred charged := fun input => by
  rcases input with (n | x) | (p | c) <;> unfold charged <;> infer_instance

def clock (x : Option HashInput) : OracleComp CountSpec Unit :=
  liftM (CountSpec.query (.inl (.inr x)))
def clocks : Nat → OracleComp CountSpec Unit
  | 0 => pure ()
  | n + 1 => clock none >>= fun _ => clocks n
noncomputable def liftW {α : Type} (program : OracleComp WSpec α) : OracleComp CountSpec α :=
  simulateQ (fun input => match input with
    | .inl n => liftM (CountSpec.query (.inl (.inl n)))
    | .inr input => liftM (CountSpec.query (.inr input))) program
noncomputable def countAuxImpl : QueryImpl CountAux ProbComp
  | .inl n => liftM (unifSpec.query n)
  | .inr _ => pure ()
noncomputable def countEnvironment : SecretGuessObservation.Environment CountAux Guess.GCoord Digest PUnit :=
  SecretGuessObservation.environment countAuxImpl
noncomputable def fixedCount (g : CanonTable.HiddenF) : QueryImpl CountSpec ProbComp :=
  SecretGuessObservation.fixedAnswers countAuxImpl (Guess.Fam.phi g.1 g.2)
def countInit : CountState := SecretGuessObservation.initialState PUnit.unit

def publicInputs (inputs : List CountSpec.Domain) : List HashInput :=
  inputs.filterMap fun input => match input with
    | .inl (.inr (some x)) => some x
    | _ => none

variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)
noncomputable def hashC (x : HashInput) : OracleComp CountSpec HashOutput := do
  clock (some x)
  liftW (hashW hU ω x)
noncomputable def signC (published : SigGolfCandidate.T3.Cache) (request : Request) :
    OracleComp CountSpec (Option Signature) := do
  clocks (Wots.signCharge (wA hU ω 0) published request)
  liftW (signW hU ω published request)
noncomputable def interactionC (published : SigGolfCandidate.T3.Cache) {α : Type} :
    OracleComp LazyPrivate.Interaction α → OracleComp CountSpec (α × QueryLog Requests × List Wots.Entry) :=
  OracleComp.construct (fun value => pure (value, [], []))
    (fun input _ next => match input with
      | .inl (.inl n) => do
          let coin ← (liftM (CountSpec.query (.inl (.inl n))) : OracleComp CountSpec (Fin (n + 1)))
          next coin
      | .inl (.inr x) => do
          let answer ← hashC hU ω x
          let rest ← next answer
          pure (rest.1, rest.2.1, (x, answer) :: rest.2.2)
      | .inr request => do
          let signature ← signC hU ω published request
          let rest ← next signature
          pure (rest.1, ⟨request, signature⟩ :: rest.2.1, rest.2.2))
noncomputable def programC {β : Type} : M β → OracleComp CountSpec (β × List Wots.Entry) :=
  OracleComp.construct (fun value => pure (value, []))
    (fun input _ next => match input with
      | .inl (.inl n) => do
          let coin ← (liftM (CountSpec.query (.inl (.inl n))) : OracleComp CountSpec (Fin (n + 1)))
          next coin
      | .inl (.inr x) => do
          let answer ← hashC hU ω x
          let rest ← next answer
          pure (rest.1, (x, answer) :: rest.2)
      | .inr _ => next (0 : HashOutput))
noncomputable def worldC (adversary : AdversaryP) :
    OracleComp CountSpec (Bool × QueryLog Requests × List Wots.Entry) := do
  clocks (SigGolfCandidate.T3.Security.Wots.keygenCharge (wA hU ω 0))
  let generated := evalWithAnswerFn (wA hU ω 0) SigGolfCandidate.T3.keygen
  let interaction ← interactionC hU ω generated.2 (adversary generated.1 generated.2)
  let verdict ← programC hU ω (GameWith.verdict PaddedGame.checker generated.1 (interaction.1, interaction.2.1))
  pure (verdict.1, interaction.2.1, interaction.2.2 ++ verdict.2)
noncomputable def cappedProgram {α : Type} (program : OracleComp CountSpec α) (budget : Nat) :=
  SphincsSecurity.QueryCap.recorded (SphincsSecurity.QueryCap.run charged program budget)
noncomputable def cappedWorld (adversary : AdversaryP) (budget : Nat) :=
  cappedProgram (worldC hU ω adversary) budget

end ClaudeWCT.W9.T3.Security.WPair.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Counted
attribute [local instance] Classical.propDecidable
attribute [local instance] chargedDecidable
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
attribute [local instance] Classical.propDecidable
attribute [local instance] chargedDecidable

theorem probeInput_other (T : Answers) (a : Guess.ChainAddr) (step : Fin 4) (value : Digest) :
    Wots.OtherInput T (Guess.probeInput a step value) := by
  let pos : Extract.Pos := .wctChain a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val step.val
  have hb : pos.Bounded := ⟨a.1.isLt, a.2.1.isLt, a.2.2.1.isLt, a.2.2.2.isLt, step.isLt⟩
  -- #866: `posOf_eq` also takes the input length (a chain row is 64 bytes, `Pos.len` of a chain position).
  refine ⟨pos, Extract.posOf_eq hb (Guess.probeInput_length a step value) ?_, hb, ?_, trivial⟩
  · exact Guess.hdrBlock_probeInput a step value
  · exact ⟨a.1.isLt, a.2.1.isLt, a.2.2.1.isLt, a.2.2.2.isLt, step.isLt⟩
theorem decodeProbe_other (T : Answers) {x : HashInput} {probe : Guess.GCoord × Digest}
    (h : Guess.decodeProbe x = some probe) : Wots.OtherInput T x := by
  rw [Guess.eq_of_decodeProbe h]
  exact probeInput_other T _ _ _
end ClaudeWCT.W9.T3.Security.WPair.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Counted
attribute [local instance] Classical.propDecidable
attribute [local instance] chargedDecidable
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
attribute [local instance] Classical.propDecidable
attribute [local instance] chargedDecidable
noncomputable def probeCount (inputs : List HashInput) : Nat :=
  (inputs.filter fun x => (Guess.decodeProbe x).isSome).length

theorem probeCount_le_other (T : Answers) (pk : Digest) (trace : List Wots.Entry) :
    probeCount (trace.map Prod.fst) ≤ Wots.otherCount ⟨T, pk, trace⟩ := by
  induction trace with
  | nil => rfl
  | cons entry trace ih =>
      obtain ⟨x, a⟩ := entry
      cases hd : Guess.decodeProbe x with
      | none =>
          by_cases ho : Wots.OtherQuery T (.inl (.inr x))
          · have h : probeCount (trace.map Prod.fst) ≤ 1 + Wots.otherCount ⟨T, pk, trace⟩ := by omega
            simpa [probeCount, Wots.otherCount, hd, ho, Nat.add_comm] using h
          · simpa [probeCount, Wots.otherCount, hd, ho] using ih
      | some probe =>
          have ho : Wots.OtherQuery T (.inl (.inr x)) := decodeProbe_other T hd
          simpa [probeCount, Wots.otherCount, hd, ho] using Nat.add_le_add_left ih 1
end ClaudeWCT.W9.T3.Security.WPair.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Counted
attribute [local instance] Classical.propDecidable
attribute [local instance] chargedDecidable
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local instance] chargedDecidable

theorem fixed_liftW (g : CanonTable.HiddenF) {α : Type} (program : OracleComp WSpec α) :
    simulateQ (fixedCount g) (liftW program) = simulateQ (fixedW g) program := by
  induction program using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind input next ih =>
      rcases input with n | (p | c)
      all_goals
        simp only [liftW, simulateQ_bind, simulateQ_spec_query]
        apply bind_congr
        intro answer
        exact ih answer

theorem run_liftW {α : Type} (program : OracleComp WSpec α) (budget : Nat) :
    SphincsSecurity.QueryCap.run charged (liftW program) budget =
      (fun result => some (result, budget)) <$> liftW program := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      rcases input with n | (p | c)
      all_goals
        simp only [liftW, simulateQ_bind, simulateQ_spec_query, SphincsSecurity.QueryCap.run_query_bind,
          charged, if_false, map_bind]
        apply bind_congr
        intro answer
        exact ih answer

theorem fixed_clock (g : CanonTable.HiddenF) (input : Option HashInput) :
    simulateQ (fixedCount g) (clock input) = pure () := rfl
theorem fixed_clocks (g : CanonTable.HiddenF) (n : Nat) :
    simulateQ (fixedCount g) (clocks n) = pure () := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [clocks, simulateQ_bind, fixed_clock, pure_bind, ih]

theorem run_clock_bind {α : Type} (input : Option HashInput) (next : Unit → OracleComp CountSpec α) :
    ∀ budget, SphincsSecurity.QueryCap.run charged (clock input >>= next) budget =
      match budget with
      | 0 => pure none
      | remaining + 1 => clock input >>= fun answer => SphincsSecurity.QueryCap.run charged (next answer) remaining := by
  intro budget
  rw [clock, SphincsSecurity.QueryCap.run_query_bind]
  simp only [charged, if_true]
  cases budget <;> rfl

theorem fixed_run_clocks_bind (g : CanonTable.HiddenF) {α : Type} (n : Nat)
    (next : OracleComp CountSpec α) (budget : Nat) :
    simulateQ (fixedCount g) (SphincsSecurity.QueryCap.run charged (clocks n >>= fun _ => next) budget) =
      if n ≤ budget then simulateQ (fixedCount g) (SphincsSecurity.QueryCap.run charged next (budget - n))
      else pure none := by
  induction n generalizing budget with
  | zero => simp [clocks]
  | succ n ih =>
      simp only [clocks, bind_assoc, run_clock_bind]
      cases budget with
      | zero => simp [simulateQ_pure]
      | succ budget =>
          simp only [simulateQ_bind, fixed_clock, pure_bind, ih, Nat.succ_le_succ_iff,
            Nat.succ_sub_succ_eq_sub]
end ClaudeWCT.W9.T3.Security.WPair.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Counted
attribute [local instance] Classical.propDecidable
attribute [local instance] chargedDecidable
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

open SphincsSecurity.Concrete

/-- Record only charged external hash calls. In particular, private disclosures
    and the internal signing charge do not enter this public transcript. -/
noncomputable def observed (g : CanonTable.HiddenF) {α : Type}
    (program : OracleComp CountSpec α) : ProbComp (α × List HashInput) :=
  OracleComp.construct (fun result => pure (result, []))
    (fun input _ next => do
      let answer ← fixedCount g input
      let rest ← next answer
      pure (rest.1, publicInputs [input] ++ rest.2)) program

theorem observed_pure (g : CanonTable.HiddenF) {α : Type} (result : α) :
    observed g (pure result : OracleComp CountSpec α) = pure (result, []) := rfl

theorem observed_query_bind (g : CanonTable.HiddenF) {α : Type} (input : CountSpec.Domain)
    (next : CountSpec.Range input → OracleComp CountSpec α) :
    observed g (liftM (CountSpec.query input) >>= next) =
      (fixedCount g input >>= fun answer => observed g (next answer) >>= fun rest =>
        pure (rest.1, publicInputs [input] ++ rest.2)) := rfl

theorem observed_bind (g : CanonTable.HiddenF) {α β : Type} (program : OracleComp CountSpec α)
    (next : α → OracleComp CountSpec β) :
    observed g (program >>= next) =
      (observed g program >>= fun first => observed g (next first.1) >>= fun second =>
        pure (second.1, first.2 ++ second.2)) := by
  induction program using OracleComp.inductionOn with
  | pure result => simp only [pure_bind, observed_pure, List.nil_append, Prod.mk.eta, bind_pure]
  | query_bind input continuation ih =>
      simp only [bind_assoc, observed_query_bind, ih, pure_bind, List.append_assoc]

theorem observed_map (g : CanonTable.HiddenF) {α β : Type} (f : α → β) (program : OracleComp CountSpec α) :
    observed g (f <$> program) = (fun result => (f result.1, result.2)) <$> observed g program := by
  rw [← bind_pure_comp, observed_bind]
  simp only [observed_pure, pure_bind, map_pure, List.append_nil, bind_pure_comp]

theorem observed_recorded (g : CanonTable.HiddenF) {α : Type} (program : OracleComp CountSpec α) :
    observed g program = (fun result => (result.1, publicInputs result.2)) <$>
      simulateQ (fixedCount g) (SphincsSecurity.QueryCap.recorded program) := by
  induction program using OracleComp.inductionOn with
  | pure result => rfl
  | query_bind input next ih =>
      simp only [observed_query_bind, ih, SphincsSecurity.QueryCap.recorded_query_bind,
        simulateQ_bind, simulateQ_spec_query, simulateQ_pure, bind_map_left, map_bind, map_pure]
      congr 1
      funext answer
      congr 1
      funext rest
      congr 1
      rcases input with (n | x) | (p | c)
      all_goals try (cases x)
      all_goals simp [publicInputs, List.filterMap_cons]

theorem observed_liftW (g : CanonTable.HiddenF) {α : Type} (program : OracleComp WSpec α) :
    observed g (liftW program) = (fun result => (result, [])) <$> simulateQ (fixedW g) program := by
  induction program using OracleComp.inductionOn with
  | pure result => rfl
  | query_bind input next ih =>
      rcases input with n | (p | c)
      all_goals
        simp only [liftW, simulateQ_bind, simulateQ_spec_query]
        rw [observed_query_bind]
        change (_ >>= fun answer => observed g (liftW (next answer)) >>= fun rest => pure (rest.1, [] ++ rest.2)) = _
        simp only [ih, List.nil_append, Prod.mk.eta, bind_pure, map_bind]
        rfl

theorem observed_clock (g : CanonTable.HiddenF) (input : Option HashInput) :
    observed g (clock input) = pure ((), input.toList) := by
  cases input <;> rfl

theorem observed_clocks (g : CanonTable.HiddenF) (n : Nat) :
    observed g (clocks n) = pure ((), []) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [clocks, observed_bind, observed_clock, pure_bind, ih, Option.toList_none, List.nil_append]

theorem observed_run_clocks_bind (g : CanonTable.HiddenF) {α : Type} (n : Nat)
    (next : OracleComp CountSpec α) (budget : Nat) :
    observed g (SphincsSecurity.QueryCap.run charged (clocks n >>= fun _ => next) budget) =
      if n ≤ budget then observed g (SphincsSecurity.QueryCap.run charged next (budget - n))
      else pure (none, []) := by
  induction n generalizing budget with
  | zero => simp [clocks, observed_pure]
  | succ n ih =>
      simp only [clocks, bind_assoc, run_clock_bind]
      cases budget with
      | zero => simp [observed_pure]
      | succ budget =>
          simp only [observed_bind, observed_clock, pure_bind, Option.toList_none, List.nil_append, ih,
            Nat.succ_le_succ_iff, Nat.succ_sub_succ_eq_sub, Prod.mk.eta, bind_pure]

theorem fixedRun_liftW (g : CanonTable.HiddenF) {α : Type} (program : OracleComp WSpec α)
    (state : CountState) :
    SecretGuessObservation.fixedRun countEnvironment (Guess.Fam.phi g.1 g.2) (liftW program) state =
      SecretGuessObservation.fixedRun env (Guess.Fam.phi g.1 g.2) program state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure result => rfl
  | query_bind input next ih =>
      rcases input with n | (p | c)
      all_goals
        simp only [liftW, simulateQ_bind, simulateQ_spec_query, SecretGuessObservation.fixedRun,
          SecretGuessObservation.runWith_query_bind]
        apply bind_congr
        intro answer
        exact ih answer.1 answer.2

theorem fixedRun_clock (g : CanonTable.HiddenF) (input : Option HashInput) (state : CountState) :
    SecretGuessObservation.fixedRun countEnvironment (Guess.Fam.phi g.1 g.2) (clock input) state =
      pure ((), state) := by
  obtain ⟨allowed, retired, guesses, probes, memory⟩ := state
  cases memory
  simp [SecretGuessObservation.fixedRun, SecretGuessObservation.runWith, clock,
    SecretGuessObservation.fixedImpl, countEnvironment, SecretGuessObservation.environment, countAuxImpl,
    StateT.run_mk, simulateQ_spec_query]

theorem fixedRun_clocks (g : CanonTable.HiddenF) (n : Nat) (state : CountState) :
    SecretGuessObservation.fixedRun countEnvironment (Guess.Fam.phi g.1 g.2) (clocks n) state =
      pure ((), state) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [clocks, SecretGuessObservation.fixedRun, SecretGuessObservation.runWith,
        simulateQ_bind, StateT.run_bind]
      change (SecretGuessObservation.fixedRun countEnvironment (Guess.Fam.phi g.1 g.2) (clock none) state >>=
        fun result => SecretGuessObservation.fixedRun countEnvironment (Guess.Fam.phi g.1 g.2) (clocks n) result.2) = _
      rw [fixedRun_clock, pure_bind, ih]

end ClaudeWCT.W9.T3.Security.WPair.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Counted
attribute [local instance] Classical.propDecidable
attribute [local instance] chargedDecidable
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots (RefWorld RefCharged refImpl tick ticks)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def refPublicInputs (inputs : List RefWorld.Domain) : List HashInput :=
  inputs.filterMap fun input => match input with
    | .inl (.inr x) => some x
    | _ => none

noncomputable def refObserved (T : Answers) {α : Type} (program : OracleComp RefWorld α) :
    ProbComp (α × List HashInput) :=
  OracleComp.construct (fun result => pure (result, []))
    (fun input _ next => do
      let answer ← refImpl T input
      let rest ← next answer
      pure (rest.1, refPublicInputs [input] ++ rest.2)) program

theorem refObserved_pure (T : Answers) {α : Type} (result : α) :
    refObserved T (pure result : OracleComp RefWorld α) = pure (result, []) := rfl

theorem refObserved_query_bind (T : Answers) {α : Type} (input : RefWorld.Domain)
    (next : RefWorld.Range input → OracleComp RefWorld α) :
    refObserved T (liftM (RefWorld.query input) >>= next) =
      (refImpl T input >>= fun answer => refObserved T (next answer) >>= fun rest =>
        pure (rest.1, refPublicInputs [input] ++ rest.2)) := rfl

theorem refObserved_bind (T : Answers) {α β : Type} (program : OracleComp RefWorld α)
    (next : α → OracleComp RefWorld β) :
    refObserved T (program >>= next) =
      (refObserved T program >>= fun first => refObserved T (next first.1) >>= fun second =>
        pure (second.1, first.2 ++ second.2)) := by
  induction program using OracleComp.inductionOn with
  | pure result => simp only [pure_bind, refObserved_pure, List.nil_append, Prod.mk.eta, bind_pure]
  | query_bind input continuation ih =>
      simp only [bind_assoc, refObserved_query_bind, ih, pure_bind, List.append_assoc]

theorem refObserved_map (T : Answers) {α β : Type} (f : α → β) (program : OracleComp RefWorld α) :
    refObserved T (f <$> program) = (fun result => (f result.1, result.2)) <$> refObserved T program := by
  rw [← bind_pure_comp, refObserved_bind]
  simp only [refObserved_pure, pure_bind, map_pure, List.append_nil, bind_pure_comp]

theorem refObserved_recorded (T : Answers) {α : Type} (program : OracleComp RefWorld α) :
    refObserved T program = (fun result => (result.1, refPublicInputs result.2)) <$>
      simulateQ (refImpl T) (SphincsSecurity.QueryCap.recorded program) := by
  induction program using OracleComp.inductionOn with
  | pure result => rfl
  | query_bind input next ih =>
      simp only [refObserved_query_bind, ih, SphincsSecurity.QueryCap.recorded_query_bind,
        simulateQ_bind, simulateQ_spec_query, simulateQ_pure, bind_map_left, map_bind, map_pure]
      congr 1
      funext answer
      congr 1
      funext rest
      congr 1
      rcases input with (n | x) | u <;> simp [refPublicInputs, List.filterMap_cons]

theorem refPublicInputs_eq_trace (T : Answers) (inputs : List RefWorld.Domain) :
    refPublicInputs inputs = (SigGolfCandidate.T3.Security.Wots.traceOf T inputs).map Prod.fst := by
  induction inputs with
  | nil => rfl
  | cons input rest ih =>
      rcases input with (n | x) | u
      · simpa only [refPublicInputs, SigGolfCandidate.T3.Security.Wots.traceOf,
          List.filterMap_cons] using ih
      · simpa only [refPublicInputs, SigGolfCandidate.T3.Security.Wots.traceOf,
          List.filterMap_cons, List.map_cons] using congrArg (List.cons x) ih
      · simpa only [refPublicInputs, SigGolfCandidate.T3.Security.Wots.traceOf,
          List.filterMap_cons] using ih

theorem run_tick_bind {α : Type} (next : Unit → OracleComp RefWorld α) (budget : Nat) :
    SphincsSecurity.QueryCap.run RefCharged (tick >>= next) budget =
      match budget with
      | 0 => pure none
      | remaining + 1 => tick >>= fun answer => SphincsSecurity.QueryCap.run RefCharged (next answer) remaining := by
  rw [tick, SphincsSecurity.QueryCap.run_query_bind]
  simp only [RefCharged, if_true]
  cases budget <;> rfl

theorem refObserved_tick (T : Answers) : refObserved T tick = pure ((), []) := rfl

theorem refObserved_run_ticks_bind (T : Answers) {α : Type} (n : Nat)
    (next : OracleComp RefWorld α) (budget : Nat) :
    refObserved T (SphincsSecurity.QueryCap.run RefCharged (ticks n >>= fun _ => next) budget) =
      if n ≤ budget then refObserved T (SphincsSecurity.QueryCap.run RefCharged next (budget - n))
      else pure (none, []) := by
  induction n generalizing budget with
  | zero => simp [ticks, refObserved_pure]
  | succ n ih =>
      simp only [ticks, bind_assoc, run_tick_bind]
      cases budget with
      | zero => simp [refObserved_pure]
      | succ budget =>
          simp only [refObserved_bind, refObserved_tick, pure_bind, List.nil_append, ih,
            Nat.succ_le_succ_iff, Nat.succ_sub_succ_eq_sub, Prod.mk.eta, bind_pure]

variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)

theorem observed_run_liftW_bind (g : CanonTable.HiddenF) {α β : Type} (program : OracleComp WSpec α)
    (next : α → OracleComp CountSpec β) (budget : Nat) :
    observed g (SphincsSecurity.QueryCap.run charged (liftW program >>= next) budget) =
      (simulateQ (fixedW g) program >>= fun result =>
        observed g (SphincsSecurity.QueryCap.run charged (next result) budget)) := by
  rw [SphincsSecurity.QueryCap.run_bind, run_liftW, bind_map_left, observed_bind, observed_liftW]
  simp only [bind_map_left, List.nil_append, Prod.mk.eta, bind_pure]

theorem observed_run_hashC_bind (g : CanonTable.HiddenF) {α : Type} (x : HashInput)
    (next : HashOutput → OracleComp CountSpec α) (budget : Nat) :
    observed g (SphincsSecurity.QueryCap.run charged (hashC hU ω x >>= next) budget) =
      match budget with
      | 0 => pure (none, [])
      | remaining + 1 =>
          (fun rest => (rest.1, x :: rest.2)) <$>
            observed g (SphincsSecurity.QueryCap.run charged
              (next (wA hU ω g (.inl (.inr x)))) remaining) := by
  simp only [hashC, bind_assoc, run_clock_bind]
  cases budget with
  | zero => rfl
  | succ remaining =>
      rw [observed_bind, observed_clock, pure_bind, observed_run_liftW_bind, fixed_hashW, pure_bind]
      simp only [Option.toList_some, List.singleton_append, bind_pure_comp]

theorem observed_run_signC_bind (g : CanonTable.HiddenF) {α : Type}
    (published : SigGolfCandidate.T3.Cache) (request : Request)
    (next : Option Signature → OracleComp CountSpec α) (budget : Nat) :
    observed g (SphincsSecurity.QueryCap.run charged (signC hU ω published request >>= next) budget) =
      if Wots.signCharge (wA hU ω g) published request ≤ budget then
        observed g (SphincsSecurity.QueryCap.run charged
          (next (evalWithAnswerFn (wA hU ω g) (FullGame.authenticatedSign published request)))
          (budget - Wots.signCharge (wA hU ω g) published request))
      else pure (none, []) := by
  simp only [signC, bind_assoc, observed_run_clocks_bind]
  rw [signCharge_eq hU ω 0 g]
  split_ifs
  · rw [observed_run_liftW_bind, fixed_signW, pure_bind]
  · rfl

end ClaudeWCT.W9.T3.Security.WPair.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Counted
attribute [local instance] Classical.propDecidable
attribute [local instance] chargedDecidable
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots (RefWorld RefCharged refImpl)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)

theorem observed_run_coin_bind (g : CanonTable.HiddenF) {α : Type} (n : Nat)
    (next : Fin (n + 1) → OracleComp CountSpec α) (budget : Nat) :
    observed g (SphincsSecurity.QueryCap.run charged
      (liftM (CountSpec.query (.inl (.inl n))) >>= next) budget) =
      ((liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) >>= fun coin =>
        observed g (SphincsSecurity.QueryCap.run charged (next coin) budget)) := by
  rw [SphincsSecurity.QueryCap.run_query_bind]
  simp only [charged, if_false, observed_query_bind, publicInputs,
    List.filterMap_cons, List.filterMap_nil, List.nil_append, Prod.mk.eta, bind_pure]
  rfl

theorem refObserved_run_coin_bind (T : Answers) {α : Type} (n : Nat)
    (next : Fin (n + 1) → OracleComp RefWorld α) (budget : Nat) :
    refObserved T (SphincsSecurity.QueryCap.run RefCharged
      (liftM (RefWorld.query (.inl (.inl n))) >>= next) budget) =
      ((liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) >>= fun coin =>
        refObserved T (SphincsSecurity.QueryCap.run RefCharged (next coin) budget)) := by
  rw [SphincsSecurity.QueryCap.run_query_bind]
  simp only [RefCharged, if_false, refObserved_query_bind, refPublicInputs,
    List.filterMap_cons, List.filterMap_nil, List.nil_append, Prod.mk.eta, bind_pure]
  rfl

theorem refObserved_run_public_bind (T : Answers) {α : Type} (x : HashInput)
    (next : HashOutput → OracleComp RefWorld α) (budget : Nat) :
    refObserved T (SphincsSecurity.QueryCap.run RefCharged
      (liftM (RefWorld.query (.inl (.inr x))) >>= next) budget) =
      match budget with
      | 0 => pure (none, [])
      | remaining + 1 =>
          (fun rest => (rest.1, x :: rest.2)) <$>
            refObserved T (SphincsSecurity.QueryCap.run RefCharged (next (T (.inl (.inr x)))) remaining) := by
  rw [SphincsSecurity.QueryCap.run_query_bind]
  simp only [RefCharged, if_true]
  cases budget with
  | zero => rfl
  | succ remaining =>
      simp only [refObserved_query_bind, refImpl, pure_bind, refPublicInputs,
        List.filterMap_cons, List.filterMap_nil, List.singleton_append, bind_pure_comp]

theorem refObserved_run_offlineSign_bind (T : Answers) {α : Type}
    (published : SigGolfCandidate.T3.Cache) (request : Request)
    (next : Option Signature → OracleComp RefWorld α) (budget : Nat) :
    refObserved T (SphincsSecurity.QueryCap.run RefCharged
      (Wots.offlineSign T published request >>= next) budget) =
      if Wots.signCharge T published request ≤ budget then
        refObserved T (SphincsSecurity.QueryCap.run RefCharged
          (next (evalWithAnswerFn T (FullGame.authenticatedSign published request)))
          (budget - Wots.signCharge T published request))
      else pure (none, []) := by
  simp only [Wots.offlineSign, bind_assoc, pure_bind, refObserved_run_ticks_bind]

theorem interactionC_pure (published : SigGolfCandidate.T3.Cache) {α : Type} (value : α) :
    interactionC hU ω published (pure value : OracleComp LazyPrivate.Interaction α) = pure (value, [], []) := rfl
theorem interactionC_coin (published : SigGolfCandidate.T3.Cache) {α : Type} (n : Nat)
    (next : Fin (n + 1) → OracleComp LazyPrivate.Interaction α) :
    interactionC hU ω published (liftM (LazyPrivate.Interaction.query (.inl (.inl n))) >>= next) =
      (liftM (CountSpec.query (.inl (.inl n))) >>= fun coin => interactionC hU ω published (next coin)) := rfl
theorem interactionC_public (published : SigGolfCandidate.T3.Cache) {α : Type} (x : HashInput)
    (next : HashOutput → OracleComp LazyPrivate.Interaction α) :
    interactionC hU ω published (liftM (LazyPrivate.Interaction.query (.inl (.inr x))) >>= next) =
      (hashC hU ω x >>= fun answer => interactionC hU ω published (next answer) >>= fun rest =>
        pure (rest.1, rest.2.1, (x, answer) :: rest.2.2)) := rfl
theorem interactionC_request (published : SigGolfCandidate.T3.Cache) {α : Type} (request : Request)
    (next : Option Signature → OracleComp LazyPrivate.Interaction α) :
    interactionC hU ω published (liftM (LazyPrivate.Interaction.query (.inr request)) >>= next) =
      (signC hU ω published request >>= fun signature => interactionC hU ω published (next signature) >>= fun rest =>
        pure (rest.1, ⟨request, signature⟩ :: rest.2.1, rest.2.2)) := rfl

/-- The count world and the reference experiment have the same capped public
    transcript, including the prefix retained when the query budget expires. -/
theorem interactionC_transport (g : CanonTable.HiddenF) (published : SigGolfCandidate.T3.Cache) {α β : Type}
    (program : OracleComp LazyPrivate.Interaction α)
    (nextC : (α × QueryLog Requests) → OracleComp CountSpec β)
    (nextR : (α × QueryLog Requests) → OracleComp RefWorld β)
    (hn : ∀ value budget,
      observed g (SphincsSecurity.QueryCap.run charged (nextC value) budget) =
        refObserved (wA hU ω g) (SphincsSecurity.QueryCap.run RefCharged (nextR value) budget))
    (budget : Nat) :
    observed g (SphincsSecurity.QueryCap.run charged
      (interactionC hU ω published program >>= fun result => nextC (result.1, result.2.1)) budget) =
    refObserved (wA hU ω g) (SphincsSecurity.QueryCap.run RefCharged
      (Wots.offlineInteraction (wA hU ω g) published program >>= nextR) budget) := by
  induction program using OracleComp.inductionOn generalizing nextC nextR budget with
  | pure value =>
      rw [interactionC_pure, Wots.Ref.offlineInteraction_pure, pure_bind, pure_bind]
      exact hn (value, []) budget
  | query_bind input next ih =>
      rcases input with (n | x) | request
      · rw [interactionC_coin, Wots.Ref.offlineInteraction_world, bind_assoc, bind_assoc,
          observed_run_coin_bind, refObserved_run_coin_bind]
        apply bind_congr
        intro coin
        exact ih coin nextC nextR hn budget
      · rw [interactionC_public, Wots.Ref.offlineInteraction_world]
        simp only [bind_assoc, pure_bind]
        rw [observed_run_hashC_bind, refObserved_run_public_bind]
        cases budget with
        | zero => rfl
        | succ remaining => exact congrArg _ (ih _ nextC nextR hn remaining)
      · rw [interactionC_request, Wots.Ref.offlineInteraction_request]
        simp only [bind_assoc, pure_bind, bind_map_left]
        rw [observed_run_signC_bind, refObserved_run_offlineSign_bind]
        split_ifs
        · exact ih _
            (fun value => nextC (value.1, ⟨request, evalWithAnswerFn (wA hU ω g)
              (FullGame.authenticatedSign published request)⟩ :: value.2))
            (fun value => nextR (value.1, ⟨request, evalWithAnswerFn (wA hU ω g)
              (FullGame.authenticatedSign published request)⟩ :: value.2))
            (fun value remaining => hn _ remaining) _
        · rfl

theorem programC_pure {α : Type} (value : α) :
    programC hU ω (pure value : M α) = pure (value, []) := rfl
theorem programC_coin {α : Type} (n : Nat) (next : Fin (n + 1) → M α) :
    programC hU ω (liftM (SigGolfCandidate.T3.Spec.query (.inl (.inl n))) >>= next) =
      (liftM (CountSpec.query (.inl (.inl n))) >>= fun coin => programC hU ω (next coin)) := rfl
theorem programC_public {α : Type} (x : HashInput) (next : HashOutput → M α) :
    programC hU ω (liftM (SigGolfCandidate.T3.Spec.query (.inl (.inr x))) >>= next) =
      (hashC hU ω x >>= fun answer => programC hU ω (next answer) >>= fun rest =>
        pure (rest.1, (x, answer) :: rest.2)) := rfl
theorem programC_private {α : Type} (coordinate : Coordinate) (next : HashOutput → M α) :
    programC hU ω (liftM (SigGolfCandidate.T3.Spec.query (.inr coordinate)) >>= next) =
      programC hU ω (next 0) := rfl

theorem programC_transport (g : CanonTable.HiddenF) {α β : Type} (program : M α)
    (nextC : α → OracleComp CountSpec β) (nextR : α → OracleComp RefWorld β)
    (hn : ∀ value budget,
      observed g (SphincsSecurity.QueryCap.run charged (nextC value) budget) =
        refObserved (wA hU ω g) (SphincsSecurity.QueryCap.run RefCharged (nextR value) budget))
    (budget : Nat) :
    observed g (SphincsSecurity.QueryCap.run charged
      (programC hU ω program >>= fun result => nextC result.1) budget) =
    refObserved (wA hU ω g) (SphincsSecurity.QueryCap.run RefCharged
      (simulateQ SigGolfCandidate.T3.Security.Wots.verdictImpl program >>= nextR) budget) := by
  induction program using OracleComp.inductionOn generalizing nextC nextR budget with
  | pure value =>
      rw [programC_pure, simulateQ_pure, pure_bind, pure_bind]
      exact hn value budget
  | query_bind input next ih =>
      rcases input with (n | x) | coordinate
      · rw [programC_coin, simulateQ_bind, simulateQ_spec_query]
        change observed g (SphincsSecurity.QueryCap.run charged
          ((liftM (CountSpec.query (.inl (.inl n))) >>= fun coin => programC hU ω (next coin)) >>=
            fun result => nextC result.1) budget) =
          refObserved (wA hU ω g) (SphincsSecurity.QueryCap.run RefCharged
            ((liftM (RefWorld.query (.inl (.inl n))) >>= fun coin =>
              simulateQ SigGolfCandidate.T3.Security.Wots.verdictImpl (next coin)) >>= nextR) budget)
        rw [bind_assoc, bind_assoc, observed_run_coin_bind, refObserved_run_coin_bind]
        apply bind_congr
        intro coin
        exact ih coin nextC nextR hn budget
      · rw [programC_public, simulateQ_bind, simulateQ_spec_query]
        change observed g (SphincsSecurity.QueryCap.run charged
          ((hashC hU ω x >>= fun answer => programC hU ω (next answer) >>= fun rest =>
            pure (rest.1, (x, answer) :: rest.2)) >>= fun result => nextC result.1) budget) =
          refObserved (wA hU ω g) (SphincsSecurity.QueryCap.run RefCharged
            ((liftM (RefWorld.query (.inl (.inr x))) >>= fun answer =>
              simulateQ SigGolfCandidate.T3.Security.Wots.verdictImpl (next answer)) >>= nextR) budget)
        simp only [bind_assoc, pure_bind]
        rw [observed_run_hashC_bind, refObserved_run_public_bind]
        cases budget with
        | zero => rfl
        | succ remaining => exact congrArg _ (ih _ nextC nextR hn remaining)
      · rw [programC_private, simulateQ_bind, simulateQ_spec_query]
        change _ = refObserved (wA hU ω g) (SphincsSecurity.QueryCap.run RefCharged
          ((pure (0 : HashOutput) >>= fun answer =>
            simulateQ SigGolfCandidate.T3.Security.Wots.verdictImpl (next answer)) >>= nextR) budget)
        rw [pure_bind]
        exact ih (0 : HashOutput) nextC nextR hn budget

theorem worldC_transport (g : CanonTable.HiddenF) (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP)
    (budget : Nat) :
    observed g (SphincsSecurity.QueryCap.run charged
      (worldC hU ω adversary >>= fun result => pure result.1) budget) =
      refObserved (wA hU ω g) (Wots.referenceGame (wA hU ω g) adversary budget) := by
  unfold worldC Wots.referenceGame Wots.offlineGame
  simp only [bind_assoc, pure_bind]
  rw [observed_run_clocks_bind, refObserved_run_ticks_bind,
    keygenCharge_eq hU ω 0 g, keygen_answers hU ω g]
  split_ifs
  · refine interactionC_transport hU ω g _ _
      (fun result => programC hU ω (GameWith.verdict PaddedGame.checker
        (evalWithAnswerFn (wA hU ω 0) SigGolfCandidate.T3.keygen).1 result) >>= fun checked => pure checked.1)
      (fun result => simulateQ SigGolfCandidate.T3.Security.Wots.verdictImpl
        (GameWith.verdict PaddedGame.checker
          (evalWithAnswerFn (wA hU ω 0) SigGolfCandidate.T3.keygen).1 result)) ?_ _
    intro result remaining
    have h := programC_transport hU ω g
      (GameWith.verdict PaddedGame.checker
        (evalWithAnswerFn (wA hU ω 0) SigGolfCandidate.T3.keygen).1 result)
      (fun value => pure value) (fun value => pure value)
      (fun value remaining => rfl) remaining
    simpa only [bind_pure] using h
  · rfl

theorem run_map_result {Index : Type} {spec : OracleSpec Index} (selected : Index → Prop)
    [DecidablePred selected] {α β : Type} (f : α → β) (program : OracleComp spec α) (budget : Nat) :
    SphincsSecurity.QueryCap.run selected (f <$> program) budget =
      (fun result => result.map (fun value => (f value.1, value.2))) <$>
        SphincsSecurity.QueryCap.run selected program budget := by
  induction program using OracleComp.inductionOn generalizing budget with
  | pure value => rfl
  | query_bind input next ih =>
      simp only [map_bind, SphincsSecurity.QueryCap.run_query_bind]
      by_cases hc : selected input
      · rw [if_pos hc, if_pos hc]
        cases budget <;> simp only [map_pure, map_bind, ih, Option.map_none]
      · simp only [if_neg hc, map_bind, ih]

theorem worldC_public_transport (g : CanonTable.HiddenF) (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP)
    (budget : Nat) :
    (fun result => publicInputs result.2) <$> simulateQ (fixedCount g) (cappedWorld hU ω adversary budget) =
      (fun result => refPublicInputs result.2) <$> Wots.offlineRun (wA hU ω g) adversary budget := by
  have h := congrArg (Functor.map Prod.snd) (worldC_transport hU ω g adversary budget)
  rw [bind_pure_comp, run_map_result, observed_map] at h
  simpa only [observed_recorded, refObserved_recorded, Functor.map_map, cappedWorld, cappedProgram,
    Wots.offlineRun] using h

end ClaudeWCT.W9.T3.Security.WPair.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Counted
attribute [local instance] Classical.propDecidable
attribute [local instance] chargedDecidable
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Concrete.SecretGuessObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- An FTS-labelled external query provides one unit of credit before the
    corresponding hidden-label trial is made. -/
noncomputable def clockCredit : CountSpec.Domain → Nat
  | .inl (.inr (some x)) => if (Guess.decodeProbe x).isSome then 1 else 0
  | _ => 0

/-- Every hidden-label trial has already been charged to an external FTS query.
    The definition is prefix closed, so it also covers aborted runs. -/
noncomputable def Funded {α : Type} (program : OracleComp CountSpec α) : Nat → Prop :=
  OracleComp.construct (fun _ _ => True)
    (fun input _ next credit =>
      probeStep input ≤ credit + clockCredit input ∧
      ∀ answer, next answer (credit + clockCredit input - probeStep input)) program

theorem funded_pure {α : Type} (value : α) (credit : Nat) :
    Funded (pure value : OracleComp CountSpec α) credit := trivial

theorem funded_query_bind {α : Type} (input : CountSpec.Domain)
    (next : CountSpec.Range input → OracleComp CountSpec α) (credit : Nat) :
    Funded (liftM (CountSpec.query input) >>= next) credit ↔
      probeStep input ≤ credit + clockCredit input ∧
        ∀ answer, Funded (next answer) (credit + clockCredit input - probeStep input) := Iff.rfl

theorem funded_bind {α β : Type} (program : OracleComp CountSpec α)
    (next : α → OracleComp CountSpec β) (credit : Nat) (hfirst : Funded program credit)
    (hnext : ∀ value remaining, Funded (next value) remaining) : Funded (program >>= next) credit := by
  induction program using OracleComp.inductionOn generalizing credit with
  | pure value => simpa only [pure_bind] using hnext value credit
  | query_bind input continuation ih =>
      rw [funded_query_bind] at hfirst
      rw [bind_assoc, funded_query_bind]
      exact ⟨hfirst.1, fun answer => ih answer _ (hfirst.2 answer)⟩

theorem funded_run {α : Type} (program : OracleComp CountSpec α) (credit budget : Nat)
    (hfunded : Funded program credit) :
    Funded (SphincsSecurity.QueryCap.run charged program budget) credit := by
  induction program using OracleComp.inductionOn generalizing credit budget with
  | pure value => exact funded_pure _ _
  | query_bind input next ih =>
      rw [funded_query_bind] at hfunded
      rw [SphincsSecurity.QueryCap.run_query_bind]
      by_cases hc : charged input
      · rw [if_pos hc]
        cases budget with
        | zero => exact funded_pure _ _
        | succ budget =>
            rw [funded_query_bind]
            exact ⟨hfunded.1, fun answer => ih answer _ _ (hfunded.2 answer)⟩
      · rw [if_neg hc, funded_query_bind]
        exact ⟨hfunded.1, fun answer => ih answer _ _ (hfunded.2 answer)⟩

theorem funded_recorded_bound {α : Type} (program : OracleComp CountSpec α) (credit : Nat)
    (hfunded : Funded program credit) (result : α × List CountSpec.Domain)
    (hr : result ∈ support (SphincsSecurity.QueryCap.recorded program)) :
    (result.2.map (probeStep (auxSpec := CountAux))).sum ≤ credit + (result.2.map clockCredit).sum := by
  induction program using OracleComp.inductionOn generalizing credit result with
  | pure value =>
      rw [SphincsSecurity.QueryCap.recorded_pure, mem_support_pure_iff] at hr
      subst result
      exact Nat.zero_le _
  | query_bind input next ih =>
      rw [funded_query_bind] at hfunded
      rw [SphincsSecurity.QueryCap.recorded_query_bind, mem_support_bind_iff] at hr
      obtain ⟨answer, -, hr⟩ := hr
      rw [mem_support_bind_iff] at hr
      obtain ⟨tail, ht, hr⟩ := hr
      rw [mem_support_pure_iff] at hr
      subst result
      have hi := ih answer _ (hfunded.2 answer) tail ht
      simp only [List.map_cons, List.sum_cons]
      omega

theorem clockCredit_sum (inputs : List CountSpec.Domain) :
    (inputs.map clockCredit).sum = probeCount (publicInputs inputs) := by
  induction inputs with
  | nil => rfl
  | cons input rest ih =>
      rcases input with (n | x) | (p | c)
      · simpa only [List.map_cons, List.sum_cons, clockCredit, Nat.zero_add, publicInputs,
          List.filterMap_cons] using ih
      · cases x with
        | none => simpa only [List.map_cons, List.sum_cons, clockCredit, Nat.zero_add, publicInputs,
            List.filterMap_cons] using ih
        | some x =>
            simp only [List.map_cons, List.sum_cons, clockCredit, publicInputs, List.filterMap_cons,
              probeCount, List.filter_cons]
            split <;> simp_all [probeCount, publicInputs, Nat.add_comm]
      · simpa only [List.map_cons, List.sum_cons, clockCredit, Nat.zero_add, publicInputs,
          List.filterMap_cons] using ih
      · simpa only [List.map_cons, List.sum_cons, clockCredit, Nat.zero_add, publicInputs,
          List.filterMap_cons] using ih

theorem funded_clocks (n credit : Nat) : Funded (clocks n) credit := by
  induction n with
  | zero => exact funded_pure _ _
  | succ n ih =>
      change 0 ≤ credit + 0 ∧ ∀ _ : Unit, Funded (clocks n) (credit + 0 - 0)
      exact ⟨Nat.zero_le _, fun _ => ih⟩

theorem liftW_pure {α : Type} (value : α) : liftW (pure value : OracleComp WSpec α) = pure value := rfl
theorem liftW_bind {α β : Type} (program : OracleComp WSpec α) (next : α → OracleComp WSpec β) :
    liftW (program >>= next) = liftW program >>= fun value => liftW (next value) :=
  simulateQ_bind _ _ _

theorem funded_disclose_bind {α : Type} (coordinate : Guess.GCoord)
    (next : Digest → OracleComp CountSpec α) (credit : Nat)
    (hn : ∀ value remaining, Funded (next value) remaining) :
    Funded (liftW (Guess.discloseQ (auxSpec := unifSpec) coordinate) >>= next) credit := by
  change 0 ≤ credit + 0 ∧ ∀ value : Digest, Funded (next value) (credit + 0 - 0)
  exact ⟨Nat.zero_le _, fun value => hn value credit⟩

theorem funded_discloseAll_bind {α : Type} (coordinates : List Guess.GCoord)
    (next : List Digest → OracleComp CountSpec α) (credit : Nat)
    (hn : ∀ values remaining, Funded (next values) remaining) :
    Funded (liftW (Guess.discloseAll (auxSpec := unifSpec) (V := Digest) coordinates) >>= next) credit := by
  induction coordinates generalizing next credit with
  | nil => simpa only [Guess.discloseAll, List.mapM_nil, liftW_pure, pure_bind] using hn [] credit
  | cons coordinate coordinates ih =>
      simp only [Guess.discloseAll, List.mapM_cons, liftW_bind, liftW_pure, bind_assoc, pure_bind]
      apply funded_disclose_bind
      intro value remaining
      exact ih (fun values => next (value :: values)) remaining (fun values remaining => hn _ remaining)

theorem funded_probe_bind {α : Type}
    (step : Guess.ChainAddr → Fin 4 → Digest → HashOutput) (top : Guess.ChainAddr → HashOutput)
    (miss : HashOutput) (a : Guess.ChainAddr) (p : Fin 4) (value : Digest)
    (next : HashOutput → OracleComp CountSpec α) (credit : Nat) (hcredit : 1 ≤ credit)
    (hn : ∀ value remaining, Funded (next value) remaining) :
    Funded (liftW (Guess.probeW (auxSpec := unifSpec) step top miss a p value) >>= next) credit := by
  rw [Guess.probeW, liftW_bind, bind_assoc]
  rw [show liftW (Guess.trialQ (auxSpec := unifSpec) (a, p) value) =
    (liftM (CountSpec.query (.inr (.inl ((a, p), value)))) : OracleComp CountSpec Bool) from rfl,
    funded_query_bind]
  simp only [probeStep, clockCredit, Nat.add_zero]
  refine ⟨hcredit, ?_⟩
  intro hit
  cases hit with
  | false =>
      simpa only [Bool.false_eq_true, if_false, liftW_pure, pure_bind] using hn miss (credit - 1)
  | true =>
      simp only [if_true]
      cases hp : Guess.succPos p with
      | none => simpa only [liftW_pure, pure_bind] using hn (top a) (credit - 1)
      | some p' =>
          simp only [liftW_bind, liftW_pure, bind_assoc, pure_bind]
          exact funded_disclose_bind _ _ _ (fun value remaining => hn _ remaining)

attribute [local irreducible] worldC interactionC programC signC hashC cappedWorld
  Wots.signCharge Wots.keygenCharge keygen

variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)

theorem funded_hashC_bind {α : Type} (x : HashInput) (next : HashOutput → OracleComp CountSpec α)
    (credit : Nat) (hn : ∀ value remaining, Funded (next value) remaining) :
    Funded (hashC hU ω x >>= next) credit := by
  rw [hashC, bind_assoc]
  change 0 ≤ credit + (if (Guess.decodeProbe x).isSome then 1 else 0) ∧
    ∀ _ : Unit, Funded (liftW (hashW hU ω x) >>= next)
      (credit + (if (Guess.decodeProbe x).isSome then 1 else 0) - 0)
  refine ⟨Nat.zero_le _, ?_⟩
  intro _
  unfold hashW Guess.ChainTable.hashW
  cases hd : Guess.decodeProbe x with
  | none => simpa only [Option.isSome_none, Bool.false_eq_true, if_false, Nat.add_zero, Nat.sub_zero,
      liftW_pure, pure_bind] using hn _ credit
  | some probe =>
      simp only [Option.isSome_some, if_true, Nat.sub_zero]
      exact funded_probe_bind _ _ _ _ _ _ next (credit + 1) (by omega) hn

theorem funded_signC_bind {α : Type} (published : SigGolfCandidate.T3.Cache) (request : Request)
    (next : Option Signature → OracleComp CountSpec α) (credit : Nat)
    (hn : ∀ value remaining, Funded (next value) remaining) :
    Funded (signC hU ω published request >>= next) credit := by
  rw [signC, bind_assoc]
  apply funded_bind _ _ _ (funded_clocks _ _)
  intro _ remaining
  unfold signW
  rw [liftW_bind, bind_assoc]
  simp only [liftW_pure, pure_bind]
  exact funded_discloseAll_bind _ _ _ (fun values remaining => hn _ remaining)

theorem funded_interactionC_bind {α β : Type} (published : SigGolfCandidate.T3.Cache)
    (program : OracleComp LazyPrivate.Interaction α)
    (next : (α × QueryLog Requests × List Wots.Entry) → OracleComp CountSpec β) (credit : Nat)
    (hn : ∀ value remaining, Funded (next value) remaining) :
    Funded (interactionC hU ω published program >>= next) credit := by
  induction program using OracleComp.inductionOn generalizing next credit with
  | pure value => simpa only [interactionC_pure, pure_bind] using hn (value, [], []) credit
  | query_bind input continuation ih =>
      rcases input with (n | x) | request
      · rw [interactionC_coin, bind_assoc, funded_query_bind]
        refine ⟨Nat.zero_le _, ?_⟩
        intro coin
        exact ih coin next credit hn
      · rw [interactionC_public]
        simp only [bind_assoc, pure_bind]
        apply funded_hashC_bind
        intro answer remaining
        exact ih answer _ remaining (fun result remaining => hn _ remaining)
      · rw [interactionC_request]
        simp only [bind_assoc, pure_bind]
        apply funded_signC_bind
        intro signature remaining
        exact ih signature _ remaining (fun result remaining => hn _ remaining)

theorem funded_programC_bind {α β : Type} (program : M α)
    (next : (α × List Wots.Entry) → OracleComp CountSpec β) (credit : Nat)
    (hn : ∀ value remaining, Funded (next value) remaining) :
    Funded (programC hU ω program >>= next) credit := by
  induction program using OracleComp.inductionOn generalizing next credit with
  | pure value => simpa only [programC_pure, pure_bind] using hn (value, []) credit
  | query_bind input continuation ih =>
      rcases input with (n | x) | coordinate
      · rw [programC_coin, bind_assoc, funded_query_bind]
        refine ⟨Nat.zero_le _, ?_⟩
        intro coin
        exact ih coin next credit hn
      · rw [programC_public]
        simp only [bind_assoc, pure_bind]
        apply funded_hashC_bind
        intro answer remaining
        exact ih answer _ remaining (fun result remaining => hn _ remaining)
      · rw [programC_private]
        exact ih (0 : HashOutput) next credit hn

theorem funded_worldC (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP) (credit : Nat) :
    Funded (worldC hU ω adversary) credit := by
  unfold worldC
  apply funded_bind _ _ _ (funded_clocks _ _)
  intro _ remaining
  apply funded_interactionC_bind
  intro result remaining
  apply funded_programC_bind
  intro verdict remaining
  exact funded_pure _ _

theorem cappedWorld_probe_count (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP) (budget : Nat)
    (result : Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain)
    (hr : result ∈ support (cappedWorld hU ω adversary budget)) :
    (result.2.map (probeStep (auxSpec := CountAux))).sum ≤ probeCount (publicInputs result.2) := by
  rw [cappedWorld] at hr
  have h := funded_recorded_bound _ 0 (funded_run _ 0 budget (funded_worldC hU ω adversary 0)) result hr
  simpa only [Nat.zero_add, clockCredit_sum] using h

theorem withRun_bind_counted {α β : Type}
    (environment : Environment CountAux Guess.GCoord Digest PUnit)
    (sampler : Sampler Guess.GCoord Digest PUnit) (program : OracleComp CountSpec α)
    (next : α → OracleComp CountSpec β) (state : CountState) :
    withRun environment sampler (program >>= next) state =
      (withRun environment sampler program state >>= fun middle =>
        withRun environment sampler (next middle.1) middle.2) := by
  simp only [withRun, runWith, simulateQ_bind, StateT.run_bind]

theorem withRun_result_support {α : Type}
    (environment : Environment CountAux Guess.GCoord Digest PUnit)
    (sampler : Sampler Guess.GCoord Digest PUnit) (program : OracleComp CountSpec α)
    (state : CountState) (result : α × CountState)
    (hr : withRun environment sampler program state result ≠ 0) : result.1 ∈ support program := by
  induction program using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [withRun, runWith_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
      subst result
      exact (mem_support_pure_iff _ _).mpr rfl
  | query_bind input next ih =>
      rw [withRun, runWith_query_bind, SphincsSecurity.Concrete.RetainedObservation.bind_nonzero] at hr
      obtain ⟨middle, hm, hr⟩ := hr
      rw [mem_support_bind_iff]
      exact ⟨middle.1, by simp only [support_query, Set.mem_univ], ih middle.1 middle.2 result hr⟩

theorem withRun_recorded_probes {α : Type}
    (environment : Environment CountAux Guess.GCoord Digest PUnit)
    (sampler : Sampler Guess.GCoord Digest PUnit) (program : OracleComp CountSpec α)
    (state : CountState) (result : (α × List CountSpec.Domain) × CountState)
    (hr : withRun environment sampler (SphincsSecurity.QueryCap.recorded program) state result ≠ 0) :
    result.2.probes = state.probes + (result.1.2.map (probeStep (auxSpec := CountAux))).sum := by
  induction program using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [SphincsSecurity.QueryCap.recorded_pure, withRun, runWith_pure, ne_eq,
        SPMF.pure_apply_eq_zero_iff, not_not] at hr
      subst result
      rfl
  | query_bind input next ih =>
      rw [SphincsSecurity.QueryCap.recorded_query_bind, withRun, runWith_query_bind,
        SphincsSecurity.Concrete.RetainedObservation.bind_nonzero] at hr
      obtain ⟨middle, hm, hr⟩ := hr
      change withRun environment sampler
        (SphincsSecurity.QueryCap.recorded (next middle.1) >>= fun tail => pure (tail.1, input :: tail.2))
        middle.2 result ≠ 0 at hr
      rw [withRun_bind_counted, SphincsSecurity.Concrete.RetainedObservation.bind_nonzero] at hr
      obtain ⟨tail, ht, hr⟩ := hr
      simp only [withRun, runWith_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
      subst result
      have hfirst := withImpl_probes environment sampler state input middle hm
      have htail := ih middle.1 middle.2 tail ht
      simp only [List.map_cons, List.sum_cons]
      omega

theorem recorded_probes_le_class {α : Type}
    (environment : Environment CountAux Guess.GCoord Digest PUnit)
    (sampler : Sampler Guess.GCoord Digest PUnit) (program : OracleComp CountSpec α)
    (hclass : ∀ result : α × List CountSpec.Domain, result ∈ support (SphincsSecurity.QueryCap.recorded program) →
      (result.2.map (probeStep (auxSpec := CountAux))).sum ≤ probeCount (publicInputs result.2))
    (result : (α × List CountSpec.Domain) × CountState)
    (hr : withRun environment sampler (SphincsSecurity.QueryCap.recorded program)
      countInit result ≠ 0) : result.2.probes ≤ probeCount (publicInputs result.1.2) := by
  have hp := withRun_recorded_probes environment sampler program countInit result hr
  have hc := hclass result.1
    (withRun_result_support environment sampler _ countInit result hr)
  simp only [countInit, initialState, Nat.zero_add] at hp
  exact hp.trans_le hc

theorem cappedProgram_probes_le_class {α : Type}
    (environment : Environment CountAux Guess.GCoord Digest PUnit)
    (sampler : Sampler Guess.GCoord Digest PUnit) (program : OracleComp CountSpec α) (budget : Nat)
    (hclass : ∀ result ∈ support (cappedProgram program budget),
      (result.2.map probeStep).sum ≤ probeCount (publicInputs result.2))
    (result : (Option (α × Nat) × List CountSpec.Domain) × CountState)
    (hr : withRun environment sampler (cappedProgram program budget) countInit result ≠ 0) :
    result.2.probes ≤ probeCount (publicInputs result.1.2) := by
  unfold cappedProgram at hclass hr
  exact recorded_probes_le_class environment sampler
    (SphincsSecurity.QueryCap.run charged program budget) hclass result hr

theorem cappedWorld_probes_le_class_for (sampler : Sampler Guess.GCoord Digest PUnit)
    (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP) (budget : Nat)
    (result : (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain) × CountState)
    (hr : withRun countEnvironment sampler (cappedWorld hU ω adversary budget)
      countInit result ≠ 0) : result.2.probes ≤ probeCount (publicInputs result.1.2) := by
  have hc : cappedWorld hU ω adversary budget = cappedProgram (worldC hU ω adversary) budget := by
    unfold cappedWorld; rfl
  have hr' := Eq.mp (congrArg (fun program => withRun countEnvironment sampler program countInit result ≠ 0) hc) hr
  have hp := cappedWorld_probe_count hU ω adversary budget
  have hp' := Eq.mp (congrArg (fun program => ∀ result ∈ support program,
    (result.2.map probeStep).sum ≤ probeCount (publicInputs result.2)) hc) hp
  exact cappedProgram_probes_le_class countEnvironment sampler (worldC hU ω adversary) budget hp' result hr'

theorem cappedWorld_probes_le_class (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP) (budget : Nat)
    (result : (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain) × CountState)
    (hr : withRun countEnvironment (Guess.Fam.sampler PUnit) (cappedWorld hU ω adversary budget)
      countInit result ≠ 0) : result.2.probes ≤ probeCount (publicInputs result.1.2) :=
  cappedWorld_probes_le_class_for hU ω (Guess.Fam.sampler PUnit) adversary budget result hr

theorem clockCredit_le_charged (input : CountSpec.Domain) :
    clockCredit input ≤ if charged input then 1 else 0 := by
  rcases input with (n | x) | (p | c)
  · exact Nat.zero_le _
  · cases x with
    | none => exact Nat.zero_le _
    | some x =>
        simp only [clockCredit, charged, if_true]
        split <;> omega
  · exact Nat.zero_le _
  · exact Nat.zero_le _

theorem clockCredits_le_calls (inputs : List CountSpec.Domain) :
    (inputs.map clockCredit).sum ≤ SphincsSecurity.QueryCap.calls charged inputs := by
  induction inputs with
  | nil => rfl
  | cons input rest ih =>
      rw [List.map_cons, List.sum_cons, SphincsSecurity.QueryCap.calls_cons]
      exact Nat.add_le_add (clockCredit_le_charged input) ih

theorem cappedProgram_calls_le {α : Type} (program : OracleComp CountSpec α) (budget : Nat)
    (result : Option (α × Nat) × List CountSpec.Domain)
    (hr : result ∈ support (cappedProgram program budget)) :
    SphincsSecurity.QueryCap.calls charged result.2 ≤ budget := by
  exact SphincsSecurity.QueryCap.recorded_calls_le charged
    (SphincsSecurity.QueryCap.run charged program budget) (fun _ => budget)
    (fun value hv => SphincsSecurity.QueryCap.counted_le_of_queryBound charged _ budget
      (SphincsSecurity.QueryCap.run_queryBound charged _ budget) value hv) result hr

theorem cappedWorld_probes_le_budget_for (sampler : Sampler Guess.GCoord Digest PUnit)
    (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP) (budget : Nat)
    (result : (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain) × CountState)
    (hr : withRun countEnvironment sampler (cappedWorld hU ω adversary budget)
      countInit result ≠ 0) : result.2.probes ≤ budget := by
  have hs := withRun_result_support countEnvironment sampler
    (cappedWorld hU ω adversary budget) countInit result hr
  have heq : cappedWorld hU ω adversary budget = cappedProgram (worldC hU ω adversary) budget := by
    unfold cappedWorld; rfl
  have hs' := Eq.mp (congrArg (fun program => result.1 ∈ support program) heq) hs
  have hc := cappedProgram_calls_le (worldC hU ω adversary) budget result.1 hs'
  calc
    result.2.probes ≤ probeCount (publicInputs result.1.2) :=
      cappedWorld_probes_le_class_for hU ω sampler adversary budget result hr
    _ = (result.1.2.map clockCredit).sum := (clockCredit_sum _).symm
    _ ≤ SphincsSecurity.QueryCap.calls charged result.1.2 := clockCredits_le_calls _
    _ ≤ budget := hc

theorem cappedWorld_probes_le_budget (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP) (budget : Nat)
    (result : (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain) × CountState)
    (hr : withRun countEnvironment (Guess.Fam.sampler PUnit) (cappedWorld hU ω adversary budget)
      countInit result ≠ 0) : result.2.probes ≤ budget :=
  cappedWorld_probes_le_budget_for hU ω (Guess.Fam.sampler PUnit) adversary budget result hr

end ClaudeWCT.W9.T3.Security.WPair.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Counted
attribute [local instance] Classical.propDecidable
attribute [local instance] chargedDecidable
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Concrete.SecretGuessObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] worldC cappedWorld worldGame Wots.offlineRun

theorem fixed_count_noFail (g : CanonTable.HiddenF) {α : Type}
    (program : OracleComp CountSpec α) (state : CountState) :
    Pr[⊥ | fixedRun countEnvironment (Guess.Fam.phi g.1 g.2) program state] = 0 := by
  have h := congrArg (fun law : SPMF α => Pr[⊥ | law])
    (fixedRun_projection countAuxImpl (Guess.Fam.phi g.1 g.2) program state)
  have hn : Pr[⊥ | 𝒮[simulateQ (fixedAnswers countAuxImpl (Guess.Fam.phi g.1 g.2)) program]] = 0 := by simp
  simpa only [probFailure_map, countEnvironment] using h.trans hn

theorem count_noFail {α : Type} (program : OracleComp CountSpec α) :
    Pr[⊥ | withRun countEnvironment (Guess.Fam.sampler PUnit) program countInit] = 0 := by
  rw [← Guess.Fam.fam_erasure countEnvironment program countInit (Guess.Fam.inv_initial PUnit.unit)]
  change Pr[⊥ | Guess.Fam.hiddenLaw (fun _ => Finset.univ) >>= fun g =>
    fixedRun countEnvironment g program countInit] = 0
  rw [hiddenLaw_univ_bind, probFailure_bind_eq_add_tsum]
  simp only [fixed_count_noFail, mul_zero, tsum_zero, add_zero]
  simp

theorem count_total_mass {α : Type} (program : OracleComp CountSpec α) :
    (∑' result, Pr[= result | withRun countEnvironment (Guess.Fam.sampler PUnit) program countInit]) = 1 :=
  tsum_probOutput_eq_one' (count_noFail program)

end ClaudeWCT.W9.T3.Security.WPair.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Counted
attribute [local instance] Classical.propDecidable
attribute [local instance] chargedDecidable
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Concrete.SecretGuessObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] worldC cappedWorld worldGame Wots.offlineRun

/-- Accounting queries do not change the cryptographic transcript or the
    hidden-family state. This erasure keeps the original near-event semantics. -/
noncomputable def dropClocks {α : Type} (program : OracleComp CountSpec α) : OracleComp WSpec α :=
  simulateQ (fun input => match input with
    | .inl (.inl n) => liftM (WSpec.query (.inl n))
    | .inl (.inr _) => pure ()
    | .inr query => liftM (WSpec.query (.inr query))) program

theorem dropClocks_pure {α : Type} (value : α) :
    dropClocks (pure value : OracleComp CountSpec α) = pure value := rfl

theorem dropClocks_bind {α β : Type} (program : OracleComp CountSpec α)
    (next : α → OracleComp CountSpec β) :
    dropClocks (program >>= next) = (dropClocks program >>= fun value => dropClocks (next value)) :=
  simulateQ_bind _ _ _

theorem dropClocks_liftW {α : Type} (program : OracleComp WSpec α) :
    dropClocks (liftW program) = program := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      rcases input with n | (p | c)
      all_goals
        simp only [liftW, dropClocks, simulateQ_bind, simulateQ_spec_query]
        apply bind_congr
        intro answer
        exact ih answer

theorem dropClocks_clock (input : Option HashInput) : dropClocks (clock input) = pure () := rfl

theorem dropClocks_clocks (n : Nat) : dropClocks (clocks n) = pure () := by
  induction n with
  | zero => rfl
  | succ n ih => rw [clocks, dropClocks_bind, dropClocks_clock, pure_bind, ih]

variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)

theorem dropClocks_hashC (x : HashInput) : dropClocks (hashC hU ω x) = hashW hU ω x := by
  rw [hashC, dropClocks_bind, dropClocks_clock, pure_bind, dropClocks_liftW]

theorem dropClocks_signC (published : SigGolfCandidate.T3.Cache) (request : Request) :
    dropClocks (signC hU ω published request) = signW hU ω published request := by
  rw [signC, dropClocks_bind, dropClocks_clocks, pure_bind, dropClocks_liftW]

theorem dropClocks_interactionC (published : SigGolfCandidate.T3.Cache) {α : Type}
    (program : OracleComp LazyPrivate.Interaction α) :
    dropClocks (interactionC hU ω published program) = interactionW hU ω published program := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      rcases input with (n | x) | request
      · rw [interactionC_coin, interactionW_coin, dropClocks_bind]
        change (liftM (WSpec.query (.inl n)) >>= _) = _
        apply bind_congr
        intro answer
        exact ih answer
      · rw [interactionC_public, dropClocks_bind, dropClocks_hashC]
        change (_ >>= _) = (hashW hU ω x >>= fun answer => interactionW hU ω published (next answer) >>= fun rest =>
          pure (rest.1, rest.2.1, (x, answer) :: rest.2.2))
        apply bind_congr
        intro answer
        rw [dropClocks_bind, ih]
        rfl
      · rw [interactionC_request, dropClocks_bind, dropClocks_signC]
        change (_ >>= _) = (signW hU ω published request >>= fun signature =>
          interactionW hU ω published (next signature) >>= fun rest =>
          pure (rest.1, ⟨request, signature⟩ :: rest.2.1, rest.2.2))
        apply bind_congr
        intro signature
        rw [dropClocks_bind, ih]
        rfl

theorem dropClocks_programC {α : Type} (program : M α) :
    dropClocks (programC hU ω program) = programW hU ω program := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      rcases input with (n | x) | coordinate
      · rw [programC_coin, dropClocks_bind]
        change (_ >>= _) = (liftM (WSpec.query (.inl n)) >>= fun answer => programW hU ω (next answer))
        apply bind_congr
        intro answer
        exact ih answer
      · rw [programC_public, dropClocks_bind, dropClocks_hashC]
        change (_ >>= _) = (hashW hU ω x >>= fun answer => programW hU ω (next answer) >>= fun rest =>
          pure (rest.1, (x, answer) :: rest.2))
        apply bind_congr
        intro answer
        rw [dropClocks_bind, ih]
        rfl
      · rw [programC_private]
        exact ih (0 : HashOutput)

theorem dropClocks_worldC (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP) :
    dropClocks (worldC hU ω adversary) = worldGame hU ω adversary := by
  unfold worldC worldGame
  rw [dropClocks_bind, dropClocks_clocks, pure_bind, dropClocks_bind, dropClocks_interactionC]
  apply bind_congr
  intro interaction
  rw [dropClocks_bind, dropClocks_programC]
  rfl

theorem fixedRun_dropClocks (g : CanonTable.HiddenF) {α : Type} (program : OracleComp CountSpec α)
    (state : CountState) :
    fixedRun countEnvironment (Guess.Fam.phi g.1 g.2) program state =
      fixedRun env (Guess.Fam.phi g.1 g.2) (dropClocks program) state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind input next ih =>
      rcases input with (n | x) | (p | c)
      · simp only [fixedRun, runWith_query_bind, dropClocks, simulateQ_bind, simulateQ_spec_query]
        apply bind_congr
        intro answer
        exact ih answer.1 answer.2
      · change fixedRun countEnvironment (Guess.Fam.phi g.1 g.2) (clock x >>= next) state =
          fixedRun env (Guess.Fam.phi g.1 g.2) (dropClocks (clock x >>= next)) state
        rw [dropClocks_bind, dropClocks_clock, pure_bind]
        simp only [fixedRun, runWith, simulateQ_bind, StateT.run_bind]
        change (fixedRun countEnvironment (Guess.Fam.phi g.1 g.2) (clock x) state >>=
          fun middle => fixedRun countEnvironment (Guess.Fam.phi g.1 g.2) (next middle.1) middle.2) = _
        rw [fixedRun_clock, pure_bind]
        simpa only [fixedRun, runWith] using ih () state
      · simp only [fixedRun, runWith_query_bind, dropClocks, simulateQ_bind, simulateQ_spec_query]
        apply bind_congr
        intro answer
        exact ih answer.1 answer.2
      · simp only [fixedRun, runWith_query_bind, dropClocks, simulateQ_bind, simulateQ_spec_query]
        apply bind_congr
        intro answer
        exact ih answer.1 answer.2

end ClaudeWCT.W9.T3.Security.WPair.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Counted
attribute [local instance] Classical.propDecidable
attribute [local instance] chargedDecidable
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Concrete.SecretGuessObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] worldC cappedWorld worldGame Wots.offlineRun

theorem fixedRun_bind_counted (g : CanonTable.HiddenF) {α β : Type}
    (program : OracleComp CountSpec α) (next : α → OracleComp CountSpec β) (state : CountState) :
    fixedRun countEnvironment (Guess.Fam.phi g.1 g.2) (program >>= next) state =
      (fixedRun countEnvironment (Guess.Fam.phi g.1 g.2) program state >>= fun middle =>
        fixedRun countEnvironment (Guess.Fam.phi g.1 g.2) (next middle.1) middle.2) := by
  simp only [fixedRun, runWith, simulateQ_bind, StateT.run_bind]

/-- A completed capped run is a run of the uncapped program with exactly the
    same secret-family state. Aborted prefixes are intentionally excluded. -/
theorem fixedRun_cap_completed (g : CanonTable.HiddenF) {α : Type}
    (program : OracleComp CountSpec α) (budget : Nat) (state final : CountState)
    (value : α) (remaining : Nat)
    (hr : fixedRun countEnvironment (Guess.Fam.phi g.1 g.2)
      (SphincsSecurity.QueryCap.run charged program budget) state (some (value, remaining), final) ≠ 0) :
    fixedRun countEnvironment (Guess.Fam.phi g.1 g.2) program state (value, final) ≠ 0 := by
  induction program using OracleComp.inductionOn generalizing budget state final remaining with
  | pure result =>
      simp only [SphincsSecurity.QueryCap.run_pure, fixedRun, runWith_pure, ne_eq,
        SPMF.pure_apply_eq_zero_iff, not_not, Prod.mk.injEq, Option.some.injEq] at hr
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hr
      simp [fixedRun, runWith_pure]
  | query_bind input next ih =>
      rw [SphincsSecurity.QueryCap.run_query_bind] at hr
      by_cases hc : charged input
      · rw [if_pos hc] at hr
        cases budget with
        | zero => simpa [fixedRun, runWith_pure] using hr
        | succ budget =>
            simp only [fixedRun, runWith_query_bind, SphincsSecurity.Concrete.RetainedObservation.bind_nonzero] at hr ⊢
            obtain ⟨middle, hm, hr⟩ := hr
            exact ⟨middle, hm, ih middle.1 budget middle.2 final remaining hr⟩
      · rw [if_neg hc] at hr
        simp only [fixedRun, runWith_query_bind, SphincsSecurity.Concrete.RetainedObservation.bind_nonzero] at hr ⊢
        obtain ⟨middle, hm, hr⟩ := hr
        exact ⟨middle, hm, ih middle.1 budget middle.2 final remaining hr⟩

theorem fixedRun_recorded_forget (g : CanonTable.HiddenF) {α : Type}
    (program : OracleComp CountSpec α) (state final : CountState) (value : α) (queries : List CountSpec.Domain)
    (hr : fixedRun countEnvironment (Guess.Fam.phi g.1 g.2)
      (SphincsSecurity.QueryCap.recorded program) state ((value, queries), final) ≠ 0) :
    fixedRun countEnvironment (Guess.Fam.phi g.1 g.2) program state (value, final) ≠ 0 := by
  have hmap : fixedRun countEnvironment (Guess.Fam.phi g.1 g.2)
      (Prod.fst <$> SphincsSecurity.QueryCap.recorded program) state (value, final) ≠ 0 := by
    rw [← bind_pure_comp, fixedRun_bind_counted, SphincsSecurity.Concrete.RetainedObservation.bind_nonzero]
    refine ⟨((value, queries), final), hr, ?_⟩
    simp [fixedRun, runWith_pure]
  simpa only [SphincsSecurity.QueryCap.recorded_forget] using hmap

variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)

theorem fixedRun_recorded_cap_erasure (g : CanonTable.HiddenF) {α : Type}
    (program : OracleComp CountSpec α) (erased : OracleComp WSpec α)
    (herased : dropClocks program = erased) (budget remaining : Nat)
    (value : α) (queries : List CountSpec.Domain) (start final : CountState)
    (hr : fixedRun countEnvironment (Guess.Fam.phi g.1 g.2)
      (cappedProgram program budget)
      start ((some (value, remaining), queries), final) ≠ 0) :
    fixedRun env (Guess.Fam.phi g.1 g.2) erased start (value, final) ≠ 0 := by
  unfold cappedProgram at hr
  have hrec := fixedRun_recorded_forget g
    (SphincsSecurity.QueryCap.run charged program budget) start final (some (value, remaining)) queries hr
  have hfull := fixedRun_cap_completed g program budget start final value remaining hrec
  rw [fixedRun_dropClocks, herased] at hfull
  exact hfull

set_option backward.isDefEq.respectTransparency true in
theorem cappedWorld_completed_support (g : CanonTable.HiddenF)
    (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP) (budget remaining : Nat)
    (result : Bool × QueryLog Requests × List Wots.Entry) (queries : List CountSpec.Domain) (final : CountState)
    (hr : fixedRun countEnvironment (Guess.Fam.phi g.1 g.2)
      (cappedWorld hU ω adversary budget) countInit ((some (result, remaining), queries), final) ≠ 0) :
    fixedRun env (Guess.Fam.phi g.1 g.2) (worldGame hU ω adversary) init (result, final) ≠ 0 := by
  have hc : cappedWorld hU ω adversary budget = cappedProgram (worldC hU ω adversary) budget := by unfold cappedWorld; rfl
  have hr' := Eq.mp (congrArg (fun program => fixedRun countEnvironment (Guess.Fam.phi g.1 g.2)
    program countInit ((some (result, remaining), queries), final) ≠ 0) hc) hr
  have hs := fixedRun_recorded_cap_erasure g (worldC hU ω adversary) (worldGame hU ω adversary)
    (dropClocks_worldC hU ω adversary) budget remaining result queries countInit final hr'
  have hi : countInit = init := rfl
  exact Eq.mp (congrArg (fun state => fixedRun env (Guess.Fam.phi g.1 g.2)
    (worldGame hU ω adversary) state (result, final) ≠ 0) hi) hs

theorem cappedWorld_completed_noBad (g : CanonTable.HiddenF)
    (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP) (budget remaining : Nat)
    (result : Bool × QueryLog Requests × List Wots.Entry) (queries : List CountSpec.Domain) (final : CountState)
    (hr : fixedRun countEnvironment (Guess.Fam.phi g.1 g.2)
      (cappedWorld hU ω adversary budget) countInit ((some (result, remaining), queries), final) ≠ 0)
    (hno : ¬OverflowIn (wA hU ω g) result.2.1) : ¬Guess.Fam.Bad final :=
  worldGame_noBad hU ω g adversary (result, final)
    (cappedWorld_completed_support hU ω g adversary budget remaining result queries final hr) hno

theorem cappedWorld_completed_guessed (g : CanonTable.HiddenF)
    (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP) (budget remaining : Nat)
    (result : Bool × QueryLog Requests × List Wots.Entry) (queries : List CountSpec.Domain) (final : CountState)
    (hr : fixedRun countEnvironment (Guess.Fam.phi g.1 g.2)
      (cappedWorld hU ω adversary budget) countInit ((some (result, remaining), queries), final) ≠ 0)
    (coordinate : Guess.GCoord) (hg : GuessedIn (wA hU ω g) result.2.1 result.2.2 coordinate) :
    final.guesses.Nonempty := by
  have ht := worldGame_tracking hU ω g adversary (result, final)
    (cappedWorld_completed_support hU ω g adversary budget remaining result queries final hr)
  exact Guess.nonempty_of_prefixIn (ht.2 coordinate hg)

end ClaudeWCT.W9.T3.Security.WPair.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Counted
attribute [local instance] Classical.propDecidable
attribute [local instance] chargedDecidable
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Concrete.SecretGuessObservation
set_option maxHeartbeats 1000000

variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)

/-- The first hidden-family hit is paid by actual external FTS probes. Internal
    signing charges and unrelated WOTS queries do not contribute to this cost. -/
theorem first_probe_le_external (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP)
    (budget : Nat) (hbudget : budget < 2 ^ 128) :
    Pr[fun result => ¬Guess.Fam.Bad result.2 ∧ result.2.probes ≤ budget ∧ result.2.guesses.Nonempty |
      withRun countEnvironment (Guess.Fam.sampler PUnit) (cappedWorld hU ω adversary budget) countInit] ≤
      (((2 ^ 128 - budget : Nat) : ENNReal))⁻¹ *
        ∑' result, Pr[= result |
          withRun countEnvironment (Guess.Fam.sampler PUnit) (cappedWorld hU ω adversary budget) countInit] *
            (probeCount (publicInputs result.1.2) : ENNReal) := by
  apply CountedFirst.event_le_class_cost (Guess.Fam.hazardFam countEnvironment budget)
    (cappedWorld hU ω adversary budget) countInit (Guess.Fam.inv_initial PUnit.unit)
    rfl rfl hbudget (count_total_mass _) _ (fun _ _ h => h)
    (fun result => probeCount (publicInputs result.1.2))
  intro result hr
  exact (Nat.min_le_left _ _).trans (cappedWorld_probes_le_class hU ω adversary budget result hr)

end ClaudeWCT.W9.T3.Security.WPair.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Counted
attribute [local instance] Classical.propDecidable
attribute [local instance] chargedDecidable
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Concrete.SecretGuessObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] worldC cappedWorld worldGame Wots.offlineRun

variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)
abbrev CountResult := Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain

noncomputable def countedProgramRun (program : OracleComp CountSpec (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain)) :
    ProbComp (CanonTable.HiddenF × (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain)) := do
  let hidden ← ($ᵗ CanonTable.HiddenF : ProbComp _)
  let result ← simulateQ (fixedCount hidden) program
  pure (hidden, result)
noncomputable def countedFtsRun (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP) (budget : Nat) :
    ProbComp (CanonTable.HiddenF × (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain)) :=
  countedProgramRun (cappedWorld hU ω adversary budget)

/-- Transfer events from the eagerly sampled hidden family to the lazy engine
    before applying the expected-probe estimate. -/
theorem counted_program_event_le_world (program : OracleComp CountSpec (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain))
    (event : CanonTable.HiddenF → (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain) → Prop)
    (wevent : (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain) × CountState → Prop)
    (himp : ∀ hidden result, fixedRun countEnvironment (Guess.Fam.phi hidden.1 hidden.2)
      program countInit result ≠ 0 → event hidden result.1 → wevent result) :
    Pr[fun result => event result.1 result.2 | countedProgramRun program] ≤
      Pr[wevent | withRun countEnvironment (Guess.Fam.sampler PUnit)
        program countInit] := by
  rw [← Guess.Fam.fam_erasure countEnvironment program
    countInit (Guess.Fam.inv_initial PUnit.unit)]
  change _ ≤ Pr[wevent | Guess.Fam.hiddenLaw (fun _ => Finset.univ) >>= fun hidden =>
    fixedRun countEnvironment hidden program countInit]
  rw [hiddenLaw_univ_bind]
  unfold countedProgramRun
  simp only [bind_pure_comp]
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro hidden
  simp only [probOutput_evalSPMF, probOutput_uniformSample]
  apply mul_le_mul' le_rfl
  rw [probEvent_map]
  have hfixed := fixedRun_projection countAuxImpl (Guess.Fam.phi hidden.1 hidden.2)
    program countInit
  change (Prod.fst <$> fixedRun countEnvironment (Guess.Fam.phi hidden.1 hidden.2)
      program countInit) =
    𝒮[simulateQ (fixedCount hidden) program] at hfixed
  rw [← probEvent_evalSPMF, ← hfixed, probEvent_map]
  apply probEvent_mono
  intro result hr he
  exact himp hidden result (by simpa only [mem_support_iff, SPMF.probOutput_eq_apply] using hr) he

set_option backward.isDefEq.respectTransparency true in
theorem counted_event_le_world (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP) (budget : Nat)
    (event : CanonTable.HiddenF → (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain) → Prop)
    (wevent : (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain) × CountState → Prop)
    (himp : ∀ hidden result, fixedRun (Result := (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain)) countEnvironment (Guess.Fam.phi hidden.1 hidden.2)
      (cappedWorld hU ω adversary budget) countInit result ≠ 0 → event hidden result.1 → wevent result) :
    Pr[fun result => event result.1 result.2 | countedProgramRun (cappedWorld hU ω adversary budget)] ≤
      Pr[wevent | withRun (Result := (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain)) countEnvironment (Guess.Fam.sampler PUnit)
        (cappedWorld hU ω adversary budget) countInit] :=
  counted_program_event_le_world (cappedWorld hU ω adversary budget) event wevent himp

noncomputable def fixedSampler (labels : Guess.GCoord → Digest) : Sampler Guess.GCoord Digest PUnit where
  trialLaw _ coordinate value := pure (decide (labels coordinate = value))
  discloseLaw _ coordinate := pure (labels coordinate)

theorem withRun_fixedSampler (labels : Guess.GCoord → Digest) {α : Type}
    (program : OracleComp CountSpec α) (state : CountState) :
    withRun countEnvironment (fixedSampler labels) program state =
      fixedRun countEnvironment labels program state := by
  have he : withImpl countEnvironment (fixedSampler labels) = fixedImpl countEnvironment labels := by
    funext input
    rcases input with auxiliary | (probe | coordinate)
    · rfl
    · rcases probe with ⟨coordinate, value⟩
      funext state
      simp only [withImpl, fixedSampler, fixedImpl, StateT.run_mk, map_pure]
    · funext state
      simp only [withImpl, fixedSampler, fixedImpl, StateT.run_mk, map_pure]
  unfold withRun fixedRun
  rw [he]

theorem fixed_probes_le_budget (hidden : CanonTable.HiddenF)
    (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP) (budget : Nat)
    (result : (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain) × CountState)
    (hr : fixedRun countEnvironment (Guess.Fam.phi hidden.1 hidden.2)
      (cappedWorld hU ω adversary budget) countInit result ≠ 0) : result.2.probes ≤ budget := by
  apply cappedWorld_probes_le_budget_for hU ω
    (fixedSampler (Guess.Fam.phi hidden.1 hidden.2)) adversary budget result
  rwa [withRun_fixedSampler]

/-- All cryptographic hypotheses of the first-hit estimate are checked on
    completed runs; an incomplete run cannot count as a forgery. -/
theorem counted_event_le_external (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP)
    (budget : Nat) (hbudget : budget < 2 ^ 128)
    (event : CanonTable.HiddenF → (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain) → Prop)
    (hevent : ∀ hidden result, event hidden result → ∃ output remaining,
      result.1 = some (output, remaining) ∧
      ¬OverflowIn (wA hU ω hidden) output.2.1 ∧
      ∃ coordinate, GuessedIn (wA hU ω hidden) output.2.1 output.2.2 coordinate) :
    Pr[fun result => event result.1 result.2 | countedProgramRun (cappedWorld hU ω adversary budget)] ≤
      (((2 ^ 128 - budget : Nat) : ENNReal))⁻¹ *
        ∑' result, Pr[= result | withRun (Result := (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain)) countEnvironment (Guess.Fam.sampler PUnit)
          (cappedWorld hU ω adversary budget) countInit] *
            (probeCount (publicInputs result.1.2) : ENNReal) := by
  apply (counted_event_le_world hU ω adversary budget event
    (fun result => ¬Guess.Fam.Bad result.2 ∧ result.2.probes ≤ budget ∧ result.2.guesses.Nonempty) ?_).trans
    (first_probe_le_external hU ω adversary budget hbudget)
  intro hidden result hr he
  obtain ⟨output, remaining, hout, hno, coordinate, hg⟩ := hevent hidden result.1 he
  rcases result with ⟨⟨out, queries⟩, final⟩
  dsimp only at hout
  subst out
  refine ⟨cappedWorld_completed_noBad hU ω hidden adversary budget remaining output queries final hr hno,
    ?_, cappedWorld_completed_guessed hU ω hidden adversary budget remaining output queries final hr coordinate hg⟩
  exact fixed_probes_le_budget hU ω hidden adversary budget _ hr

end ClaudeWCT.W9.T3.Security.WPair.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Counted
attribute [local instance] Classical.propDecidable
attribute [local instance] chargedDecidable
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Concrete.SecretGuessObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] worldC cappedWorld worldGame Wots.offlineRun

variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)

/-- The exact public trace law is the reference experiment's law, including
    a prefix left by an exhausted budget. This is what identifies the payment
    above with the `OtherQuery` budget rather than a fresh global query bound. -/
theorem public_program_distribution (program : OracleComp CountSpec (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain)) :
    (fun result => publicInputs result.1.2) <$>
      withRun (Result := (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain)) countEnvironment (Guess.Fam.sampler PUnit) program countInit =
    𝒮[do
      let hidden ← ($ᵗ CanonTable.HiddenF : ProbComp _)
      let result ← simulateQ (fixedCount hidden) program
      pure (publicInputs result.2)] := by
  rw [← Guess.Fam.fam_erasure countEnvironment program
    countInit (Guess.Fam.inv_initial PUnit.unit), map_bind]
  change (Guess.Fam.hiddenLaw (fun _ => Finset.univ) >>= fun labels =>
    (fun result => publicInputs result.1.2) <$>
      fixedRun (Result := (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain)) countEnvironment labels program countInit) = _
  rw [hiddenLaw_univ_bind]
  apply SPMF.ext
  intro inputs
  rw [← SPMF.probOutput_eq_apply, ← SPMF.probOutput_eq_apply]
  simp only [probOutput_evalSPMF]
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  apply tsum_congr
  intro hidden
  simp only [probOutput_evalSPMF, probOutput_uniformSample]
  congr 1
  have hfixed := congrArg (Functor.map (fun result : (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain) => publicInputs result.2))
    (fixedRun_projection countAuxImpl (Guess.Fam.phi hidden.1 hidden.2)
      program countInit)
  simp only [Functor.map_map] at hfixed
  change ((fun result => publicInputs result.1.2) <$>
    fixedRun (Result := (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain)) countEnvironment (Guess.Fam.phi hidden.1 hidden.2)
      program countInit) =
    (fun result => publicInputs result.2) <$>
      𝒮[simulateQ (fixedCount hidden) program] at hfixed
  rw [hfixed]
  simp only [← evalSPMF_map, probOutput_evalSPMF, bind_pure_comp]

set_option backward.isDefEq.respectTransparency true in
theorem public_distribution (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP) (budget : Nat) :
    (fun result => publicInputs result.1.2) <$>
      withRun (Result := (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain)) countEnvironment (Guess.Fam.sampler PUnit) (cappedWorld hU ω adversary budget) countInit =
    𝒮[do
      let hidden ← ($ᵗ CanonTable.HiddenF : ProbComp _)
      let result ← Wots.offlineRun (wA hU ω hidden) adversary budget
      pure (refPublicInputs result.2)] := by
  rw [public_program_distribution]
  apply congrArg (fun experiment : ProbComp (List HashInput) => 𝒮[experiment])
  apply bind_congr
  intro hidden
  simpa only [bind_pure_comp] using worldC_public_transport hU ω hidden adversary budget

end ClaudeWCT.W9.T3.Security.WPair.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Counted
attribute [local instance] Classical.propDecidable
attribute [local instance] chargedDecidable
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Concrete.SecretGuessObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] worldC cappedWorld worldGame Wots.offlineRun

variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)

/-- The first-hit payment is bounded by the actual reference experiment's
    external `OtherQuery` count, with the same query cap and the same trace. -/
theorem public_payment_le_reference (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP) (budget : Nat) :
    (∑' result, Pr[= result | withRun (Result := (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain)) countEnvironment (Guess.Fam.sampler PUnit)
      (cappedWorld hU ω adversary budget) countInit] *
        (probeCount (publicInputs result.1.2) : ENNReal)) ≤
    ∑' hidden, Pr[= hidden | ($ᵗ CanonTable.HiddenF : ProbComp _)] *
      ∑' run, Pr[= run | Wots.offlineRun (wA hU ω hidden) adversary budget] *
        (Wots.otherCount ⟨wA hU ω hidden, (evalWithAnswerFn (wA hU ω hidden) keygen).1,
          SigGolfCandidate.T3.Security.Wots.traceOf (wA hU ω hidden) run.2⟩ : ENNReal) := by
  rw [← tsum_probOutput_map_mul _ (fun result : (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain) × CountState => publicInputs result.1.2)
    (fun inputs => (probeCount inputs : ENNReal)), public_distribution hU ω adversary budget]
  simp only [bind_pure_comp, evalSPMF_bind, evalSPMF_map]
  rw [tsum_probOutput_bind_mul]
  apply ENNReal.tsum_le_tsum
  intro hidden
  simp only [probOutput_evalSPMF]
  apply mul_le_mul' le_rfl
  rw [tsum_probOutput_map_mul]
  simp only [probOutput_evalSPMF]
  apply ENNReal.tsum_le_tsum
  intro run
  apply mul_le_mul' le_rfl
  rw [refPublicInputs_eq_trace (wA hU ω hidden)]
  exact_mod_cast probeCount_le_other (wA hU ω hidden) _
    (SigGolfCandidate.T3.Security.Wots.traceOf (wA hU ω hidden) run.2)

end ClaudeWCT.W9.T3.Security.WPair.Counted


namespace ClaudeWCT.W9.T3.Security.WPair.Counted
attribute [local instance] Classical.propDecidable
attribute [local instance] chargedDecidable
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Concrete.SecretGuessObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] worldC cappedWorld worldGame Wots.offlineRun
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)
theorem counted_event_le_other (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP)
    (budget : Nat) (hbudget : budget < 2 ^ 128)
    (event : CanonTable.HiddenF → (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain) → Prop)
    (hevent : ∀ hidden result, event hidden result → ∃ output remaining,
      result.1 = some (output, remaining) ∧
      ¬OverflowIn (wA hU ω hidden) output.2.1 ∧
      ∃ coordinate, GuessedIn (wA hU ω hidden) output.2.1 output.2.2 coordinate) :
    Pr[fun result => event result.1 result.2 | countedProgramRun (cappedWorld hU ω adversary budget)] ≤
      (((2 ^ 128 - budget : Nat) : ENNReal))⁻¹ *
      (∑' hidden, Pr[= hidden | ($ᵗ CanonTable.HiddenF : ProbComp _)] *
      ∑' run, Pr[= run | Wots.offlineRun (wA hU ω hidden) adversary budget] *
        (Wots.otherCount ⟨wA hU ω hidden, (evalWithAnswerFn (wA hU ω hidden) keygen).1,
          SigGolfCandidate.T3.Security.Wots.traceOf (wA hU ω hidden) run.2⟩ : ENNReal)) := by
  exact (counted_event_le_external hU ω adversary budget hbudget event hevent).trans
    (mul_le_mul' le_rfl (public_payment_le_reference hU ω adversary budget))

end ClaudeWCT.W9.T3.Security.WPair.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Paired
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Mask (queried_length_bind queried_length_pure
  queried_length_shortHash queried_length_foldlM sum_map_one)
open ClaudeWCT.WCT9
open WPair.Counted (queried_length_buildChildF queried_length_buildChildH queried_length_ftsCoefs queried_free
  queried_length_free)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable local instance : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _

theorem queried_length_sharedNode (answers : Answers) (first : Bool) (coord index heap : Nat)
    (pads : Nat → PairRoot) (left right : Digest) :
    (SourceReplay.queried answers (sharedNode first coord index heap pads left right)).length = 1 := by
  unfold sharedNode sharedOuterHash
  split
  · split <;> rfl
  · split
    · split <;> rfl
    · unfold wctNodeHashH ftsHash
      split <;> rfl

theorem queried_length_sharedHeap (answers : Answers) (first : Bool) (index coord : Nat)
    (pads : Nat → PairRoot) (leaves : List Digest) :
    (SourceReplay.queried answers (sharedHeap first index coord pads leaves)).length =
      if first then 124 else 126 := by
  unfold sharedHeap
  rw [queried_length_foldlM answers _ _ (fun _ => 1) (fun _ _ _ => by
    rw [queried_length_bind, queried_length_sharedNode, queried_length_pure]), sum_map_one,
    List.length_reverse, List.length_range']

theorem queried_length_buildSharedCoordinate (answers : Answers) (first : Bool) (index coord : Nat)
    (selected : Child) (word : Rank) (pads : Nat → PairRoot) :
    (SourceReplay.queried answers (buildSharedCoordinate first index coord selected word pads)).length =
      3227 + (if first then 124 else 126) := by
  unfold buildSharedCoordinate
  rw [queried_length_bind, queried_length_ftsCoefs, queried_length_bind,
    queried_length_foldlM answers _ _ (fun _ => 25) (fun _ _ _ => by
      rw [queried_length_bind, queried_length_buildChildH, queried_length_pure]),
    queried_length_bind, queried_length_sharedHeap, queried_length_pure]
  have : ((List.range 128).map (fun _ => (25 : Nat))).sum = 3200 := by decide
  simp only [this]
  omega

theorem queried_length_buildPair (answers : Answers) (index pair : Nat)
    (selected : SigGolfCandidate.Research.SharedForest.Selection) (aWord bWord : Rank) (prev : PairRoot) :
    (SourceReplay.queried answers (buildPair index pair selected aWord bWord prev)).length = 6704 := by
  unfold buildPair
  rw [queried_length_bind, queried_length_buildSharedCoordinate, queried_length_bind,
    queried_length_buildSharedCoordinate, queried_length_pure]
  decide

theorem queried_length_buildSingleton (answers : Answers) (index : Nat)
    (selected : Child) (word : Rank) (prev : PairRoot) :
    (SourceReplay.queried answers (buildSingleton index selected word prev)).length = 3353 := by
  unfold buildSingleton
  rw [queried_length_bind, queried_length_buildSharedCoordinate, queried_length_pure]
  decide

theorem queried_length_buildForest (answers : Answers) (index : Nat)
    (selected : ForestSelection) (words : ForestWords) :
    (SourceReplay.queried answers (buildForest index selected words)).length = 30169 := by
  unfold buildForest
  rw [queried_length_bind, queried_length_foldlM answers _ _ (fun _ => 6704) (fun _ _ _ => by
    rw [queried_length_bind, queried_length_buildPair, queried_length_pure]),
    queried_length_bind, queried_length_buildSingleton, queried_length_pure]
  decide

variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (omega : CanonTable.Omega U)

attribute [local irreducible] searchPreparedLayers prepareRoots buildForest
  sharedDigestSearch forestCommitment

theorem signFromOutput_charge_eq (hidden hidden' : CanonTable.HiddenF) (cache : SigGolfCandidate.T3.Cache)
    (rho : Digest) (counter : BitVec 32) (output : HashOutput) :
    (SourceReplay.queried (wA hU omega hidden) (signFromOutput cache rho counter output)).length =
      (SourceReplay.queried (wA hU omega hidden') (signFromOutput cache rho counter output)).length := by
  unfold signFromOutput
  conv_lhs => rw [queried_length_bind, queried_length_buildForest]
  conv_rhs => rw [queried_length_bind, queried_length_buildForest]
  apply congrArg (Nat.add _)
  conv_lhs => rw [queried_length_bind]
  conv_rhs => rw [queried_length_bind]
  rw [queried_length_free hU omega hidden hidden' (prepareRoots_free _),
    eval_free hU omega hidden hidden' (prepareRoots_free _),
    buildForest_commitment, buildForest_commitment,
    forestCommitment_world hU omega hidden hidden' (digestIndex output) (digestIndex_lt output)]
  apply congrArg (Nat.add _)
  conv_lhs => rw [queried_length_bind]
  conv_rhs => rw [queried_length_bind]
  rw [queried_length_free hU omega hidden hidden' (searchPreparedLayers_free _ _ _ _),
    eval_free hU omega hidden hidden' (searchPreparedLayers_free _ _ _ _)]
  apply congrArg (Nat.add _)
  trans 0
  · split <;> exact queried_length_pure _ _
  · symm
    split <;> exact queried_length_pure _ _

noncomputable def signCharge (answers : Answers) (published : SigGolfCandidate.T3.Cache) (request : Request) : Nat :=
  (SourceReplay.queried answers (authenticatedSign published request)).length

theorem signCharge_eq (hidden hidden' : CanonTable.HiddenF)
    (published : SigGolfCandidate.T3.Cache) (request : Request) :
    signCharge (wA hU omega hidden) published request = signCharge (wA hU omega hidden') published request := by
  unfold signCharge authenticatedSign
  conv_lhs => rw [queried_length_bind]
  conv_rhs => rw [queried_length_bind]
  rw [queried_length_free hU omega hidden hidden' (privateMac_free _)]
  apply congrArg (Nat.add _)
  by_cases hc : request.cache = published
  · rw [if_pos hc]
    unfold SigGolfCandidate.Research.SharedForest.signPayload
    conv_lhs => rw [queried_length_bind]
    conv_rhs => rw [queried_length_bind]
    rw [queried_length_free hU omega hidden hidden' (privateNonce_free _),
      eval_free hU omega hidden hidden' (privateNonce_free _)]
    apply congrArg (Nat.add _)
    conv_lhs => rw [queried_length_bind]
    conv_rhs => rw [queried_length_bind]
    rw [queried_length_free hU omega hidden hidden' (sharedDigestSearch_free _ _ _ _),
      eval_free hU omega hidden hidden' (sharedDigestSearch_free _ _ _ _)]
    apply congrArg (Nat.add _)
    cases evalWithAnswerFn (wA hU omega hidden') (sharedDigestSearch
        (evalWithAnswerFn (wA hU omega hidden') (privateNonce request.message)) request.message 0 digestAttemptLimit) with
    | none => exact (queried_length_pure _ _).trans (queried_length_pure _ _).symm
    | some found =>
      obtain ⟨counter, output⟩ := found
      dsimp only
      conv_lhs => rw [queried_length_bind]
      conv_rhs => rw [queried_length_bind]
      rw [signFromOutput_charge_eq hU omega hidden hidden']
      apply congrArg (Nat.add _)
      trans 0
      · split <;> exact queried_length_pure _ _
      · symm
        split <;> exact queried_length_pure _ _
  · rw [if_neg hc]
    exact (queried_length_pure _ _).trans (queried_length_pure _ _).symm
end ClaudeWCT.W9.T3.Security.WPair.Paired

namespace ClaudeWCT.W9.T3.Security.WPair.Counted.Generic
attribute [local instance] Classical.propDecidable
attribute [local instance] chargedDecidable
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Concrete.SecretGuessObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable def countedProgramRun {α : Type} (program : OracleComp CountSpec α) :
    ProbComp (CanonTable.HiddenF × α) := do
  let hidden ← ($ᵗ CanonTable.HiddenF : ProbComp _)
  let result ← simulateQ (fixedCount hidden) program
  pure (hidden, result)
theorem counted_program_event_le_world {α : Type} (program : OracleComp CountSpec α)
    (event : CanonTable.HiddenF → α → Prop)
    (wevent : α × CountState → Prop)
    (himp : ∀ hidden result, fixedRun countEnvironment (Guess.Fam.phi hidden.1 hidden.2)
      program countInit result ≠ 0 → event hidden result.1 → wevent result) :
    Pr[fun result => event result.1 result.2 | countedProgramRun program] ≤
      Pr[wevent | withRun countEnvironment (Guess.Fam.sampler PUnit)
        program countInit] := by
  rw [← Guess.Fam.fam_erasure countEnvironment program
    countInit (Guess.Fam.inv_initial PUnit.unit)]
  change _ ≤ Pr[wevent | Guess.Fam.hiddenLaw (fun _ => Finset.univ) >>= fun hidden =>
    fixedRun countEnvironment hidden program countInit]
  rw [hiddenLaw_univ_bind]
  unfold countedProgramRun
  simp only [bind_pure_comp]
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro hidden
  simp only [probOutput_evalSPMF, probOutput_uniformSample]
  apply mul_le_mul' le_rfl
  rw [probEvent_map]
  have hfixed := fixedRun_projection countAuxImpl (Guess.Fam.phi hidden.1 hidden.2)
    program countInit
  change (Prod.fst <$> fixedRun countEnvironment (Guess.Fam.phi hidden.1 hidden.2)
      program countInit) =
    𝒮[simulateQ (fixedCount hidden) program] at hfixed
  rw [← probEvent_evalSPMF, ← hfixed, probEvent_map]
  apply probEvent_mono
  intro result hr he
  exact himp hidden result (by simpa only [mem_support_iff, SPMF.probOutput_eq_apply] using hr) he


theorem capped_probe_count {α : Type} (program : OracleComp CountSpec α) (budget : Nat)
    (hf : Funded program 0) (result : Option (α × Nat) × List CountSpec.Domain)
    (hr : result ∈ support (cappedProgram program budget)) :
    (result.2.map (probeStep (auxSpec := CountAux))).sum ≤ probeCount (publicInputs result.2) := by
  have h := funded_recorded_bound _ 0 (funded_run program 0 budget hf) result hr
  simpa only [Nat.zero_add, clockCredit_sum] using h

theorem capped_probes_le_class {α : Type} (program : OracleComp CountSpec α) (budget : Nat)
    (hf : Funded program 0) (sampler : Sampler Guess.GCoord Digest PUnit)
    (result : (Option (α × Nat) × List CountSpec.Domain) × CountState)
    (hr : withRun countEnvironment sampler (cappedProgram program budget) countInit result ≠ 0) :
    result.2.probes ≤ probeCount (publicInputs result.1.2) :=
  cappedProgram_probes_le_class countEnvironment sampler program budget
    (capped_probe_count program budget hf) result hr

theorem capped_probes_le_budget {α : Type} (program : OracleComp CountSpec α) (budget : Nat)
    (hf : Funded program 0) (sampler : Sampler Guess.GCoord Digest PUnit)
    (result : (Option (α × Nat) × List CountSpec.Domain) × CountState)
    (hr : withRun countEnvironment sampler (cappedProgram program budget) countInit result ≠ 0) :
    result.2.probes ≤ budget := by
  have hs := withRun_result_support countEnvironment sampler (cappedProgram program budget) countInit result hr
  calc
    result.2.probes ≤ probeCount (publicInputs result.1.2) := capped_probes_le_class program budget hf sampler result hr
    _ = (result.1.2.map clockCredit).sum := (clockCredit_sum _).symm
    _ ≤ SphincsSecurity.QueryCap.calls charged result.1.2 := clockCredits_le_calls _
    _ ≤ budget := cappedProgram_calls_le program budget result.1 hs

theorem first_probe_le_external {α : Type} (program : OracleComp CountSpec α)
    (hf : Funded program 0) (budget : Nat) (hbudget : budget < 2 ^ 128) :
    Pr[fun result => ¬Guess.Fam.Bad result.2 ∧ result.2.probes ≤ budget ∧ result.2.guesses.Nonempty |
      withRun countEnvironment (Guess.Fam.sampler PUnit) (cappedProgram program budget) countInit] ≤
      (((2 ^ 128 - budget : Nat) : ENNReal))⁻¹ *
        ∑' result, Pr[= result |
          withRun countEnvironment (Guess.Fam.sampler PUnit) (cappedProgram program budget) countInit] *
            (probeCount (publicInputs result.1.2) : ENNReal) := by
  apply CountedFirst.event_le_class_cost (Guess.Fam.hazardFam countEnvironment budget)
    (cappedProgram program budget) countInit (Guess.Fam.inv_initial PUnit.unit)
    rfl rfl hbudget (count_total_mass _) _ (fun _ _ h => h)
    (fun result => probeCount (publicInputs result.1.2))
  intro result hr
  exact (Nat.min_le_left _ _).trans
    (capped_probes_le_class program budget hf (Guess.Fam.sampler PUnit) result hr)
theorem public_program_distribution {α : Type} (program : OracleComp CountSpec (α × List CountSpec.Domain)) :
    (fun result => publicInputs result.1.2) <$>
      withRun (Result := (α × List CountSpec.Domain)) countEnvironment (Guess.Fam.sampler PUnit) program countInit =
    𝒮[do
      let hidden ← ($ᵗ CanonTable.HiddenF : ProbComp _)
      let result ← simulateQ (fixedCount hidden) program
      pure (publicInputs result.2)] := by
  rw [← Guess.Fam.fam_erasure countEnvironment program
    countInit (Guess.Fam.inv_initial PUnit.unit), map_bind]
  change (Guess.Fam.hiddenLaw (fun _ => Finset.univ) >>= fun labels =>
    (fun result => publicInputs result.1.2) <$>
      fixedRun (Result := (α × List CountSpec.Domain)) countEnvironment labels program countInit) = _
  rw [hiddenLaw_univ_bind]
  apply SPMF.ext
  intro inputs
  rw [← SPMF.probOutput_eq_apply, ← SPMF.probOutput_eq_apply]
  simp only [probOutput_evalSPMF]
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  apply tsum_congr
  intro hidden
  simp only [probOutput_evalSPMF, probOutput_uniformSample]
  congr 1
  have hfixed := congrArg (Functor.map (fun result : (α × List CountSpec.Domain) => publicInputs result.2))
    (fixedRun_projection countAuxImpl (Guess.Fam.phi hidden.1 hidden.2)
      program countInit)
  simp only [Functor.map_map] at hfixed
  change ((fun result => publicInputs result.1.2) <$>
    fixedRun (Result := (α × List CountSpec.Domain)) countEnvironment (Guess.Fam.phi hidden.1 hidden.2)
      program countInit) =
    (fun result => publicInputs result.2) <$>
      𝒮[simulateQ (fixedCount hidden) program] at hfixed
  rw [hfixed]
  simp only [← evalSPMF_map, probOutput_evalSPMF, bind_pure_comp]


end ClaudeWCT.W9.T3.Security.WPair.Counted.Generic

namespace ClaudeWCT.W9.T3.Security.WPair.Paired.Counted
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots (RefWorld RefCharged ticks)
open ClaudeWCT.W9.T3.Security.WPair.Counted
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local instance] ClaudeWCT.W9.T3.Security.WPair.Counted.chargedDecidable
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)
noncomputable def signC (published : SigGolfCandidate.T3.Cache) (request : Request) :
    OracleComp CountSpec (Option SigGolfCandidate.Research.SharedForest.Signature) := do
  clocks (Paired.signCharge (wA hU ω 0) published request)
  liftW (Paired.signW hU ω published request)
noncomputable def interactionC (published : SigGolfCandidate.T3.Cache) {α : Type} :
    OracleComp Paired.Interaction α → OracleComp CountSpec (α × QueryLog Paired.Requests × List Wots.Entry) :=
  OracleComp.construct (fun value => pure (value, [], []))
    (fun input _ next => match input with
      | .inl (.inl n) => do
          let coin ← (liftM (CountSpec.query (.inl (.inl n))) : OracleComp CountSpec (Fin (n + 1)))
          next coin
      | .inl (.inr x) => do
          let answer ← hashC hU ω x
          let rest ← next answer
          pure (rest.1, rest.2.1, (x, answer) :: rest.2.2)
      | .inr request => do
          let signature ← signC hU ω published request
          let rest ← next signature
          pure (rest.1, ⟨request, signature⟩ :: rest.2.1, rest.2.2))

noncomputable def offlineSign (T : Answers) (published : SigGolfCandidate.T3.Cache) (request : Request) :
    OracleComp RefWorld (Option SigGolfCandidate.Research.SharedForest.Signature) :=
  ticks (Paired.signCharge T published request) >>= fun _ =>
    pure (evalWithAnswerFn T (Paired.authenticatedSign published request))
noncomputable def offlineInteraction (T : Answers) (published : SigGolfCandidate.T3.Cache) {α : Type} :
    OracleComp Paired.Interaction α → OracleComp RefWorld (α × QueryLog Paired.Requests) :=
  OracleComp.construct (fun value => pure (value, []))
    (fun input _ next => match input with
      | .inl input => do
          let answer ← (liftM (RefWorld.query (.inl input)) : OracleComp RefWorld (SphincsSecurity.OracleWorld.Range input))
          next answer
      | .inr request => do
          let signature ← offlineSign T published request
          let rest ← next signature
          pure (rest.1, ⟨request, signature⟩ :: rest.2))
theorem offlineInteraction_pure (T : Answers) (published : SigGolfCandidate.T3.Cache) {α : Type} (value : α) :
    offlineInteraction T published (pure value : OracleComp Paired.Interaction α) = pure (value, []) := rfl
theorem offlineInteraction_world (T : Answers) (published : SigGolfCandidate.T3.Cache) {α : Type}
    (input : SphincsSecurity.OracleWorld.Domain)
    (next : SphincsSecurity.OracleWorld.Range input → OracleComp Paired.Interaction α) :
    offlineInteraction T published (liftM (Paired.Interaction.query (.inl input)) >>= next) =
      (liftM (RefWorld.query (.inl input)) >>= fun answer => offlineInteraction T published (next answer)) := rfl
theorem offlineInteraction_request (T : Answers) (published : SigGolfCandidate.T3.Cache) {α : Type}
    (request : Request) (next : Option SigGolfCandidate.Research.SharedForest.Signature → OracleComp Paired.Interaction α) :
    offlineInteraction T published (liftM (Paired.Interaction.query (.inr request)) >>= next) =
      (offlineSign T published request >>= fun signature => offlineInteraction T published (next signature) >>= fun rest =>
        pure (rest.1, ⟨request, signature⟩ :: rest.2)) := rfl
theorem observed_run_signC_bind (g : CanonTable.HiddenF) {α : Type}
    (published : SigGolfCandidate.T3.Cache) (request : Request)
    (next : Option SigGolfCandidate.Research.SharedForest.Signature → OracleComp CountSpec α) (budget : Nat) :
    observed g (SphincsSecurity.QueryCap.run charged (signC hU ω published request >>= next) budget) =
      if Paired.signCharge (wA hU ω g) published request ≤ budget then
        observed g (SphincsSecurity.QueryCap.run charged
          (next (evalWithAnswerFn (wA hU ω g) (Paired.authenticatedSign published request)))
          (budget - Paired.signCharge (wA hU ω g) published request))
      else pure (none, []) := by
  simp only [signC, bind_assoc, observed_run_clocks_bind]
  rw [Paired.signCharge_eq hU ω 0 g]
  split_ifs
  · rw [observed_run_liftW_bind, Paired.fixed_signW, pure_bind]
  · rfl

theorem refObserved_run_offlineSign_bind (T : Answers) {α : Type}
    (published : SigGolfCandidate.T3.Cache) (request : Request)
    (next : Option SigGolfCandidate.Research.SharedForest.Signature → OracleComp RefWorld α) (budget : Nat) :
    refObserved T (SphincsSecurity.QueryCap.run RefCharged
      (offlineSign T published request >>= next) budget) =
      if Paired.signCharge T published request ≤ budget then
        refObserved T (SphincsSecurity.QueryCap.run RefCharged
          (next (evalWithAnswerFn T (Paired.authenticatedSign published request)))
          (budget - Paired.signCharge T published request))
      else pure (none, []) := by
  simp only [offlineSign, bind_assoc, pure_bind, refObserved_run_ticks_bind]

theorem interactionC_pure (published : SigGolfCandidate.T3.Cache) {α : Type} (value : α) :
    interactionC hU ω published (pure value : OracleComp Paired.Interaction α) = pure (value, [], []) := rfl
theorem interactionC_coin (published : SigGolfCandidate.T3.Cache) {α : Type} (n : Nat)
    (next : Fin (n + 1) → OracleComp Paired.Interaction α) :
    interactionC hU ω published (liftM (Paired.Interaction.query (.inl (.inl n))) >>= next) =
      (liftM (CountSpec.query (.inl (.inl n))) >>= fun coin => interactionC hU ω published (next coin)) := rfl
theorem interactionC_public (published : SigGolfCandidate.T3.Cache) {α : Type} (x : HashInput)
    (next : HashOutput → OracleComp Paired.Interaction α) :
    interactionC hU ω published (liftM (Paired.Interaction.query (.inl (.inr x))) >>= next) =
      (hashC hU ω x >>= fun answer => interactionC hU ω published (next answer) >>= fun rest =>
        pure (rest.1, rest.2.1, (x, answer) :: rest.2.2)) := rfl
theorem interactionC_request (published : SigGolfCandidate.T3.Cache) {α : Type} (request : Request)
    (next : Option SigGolfCandidate.Research.SharedForest.Signature → OracleComp Paired.Interaction α) :
    interactionC hU ω published (liftM (Paired.Interaction.query (.inr request)) >>= next) =
      (signC hU ω published request >>= fun signature => interactionC hU ω published (next signature) >>= fun rest =>
        pure (rest.1, ⟨request, signature⟩ :: rest.2.1, rest.2.2)) := rfl

/-- The count world and the reference experiment have the same capped public
    transcript, including the prefix retained when the query budget expires. -/
theorem interactionC_transport (g : CanonTable.HiddenF) (published : SigGolfCandidate.T3.Cache) {α β : Type}
    (program : OracleComp Paired.Interaction α)
    (nextC : (α × QueryLog Paired.Requests) → OracleComp CountSpec β)
    (nextR : (α × QueryLog Paired.Requests) → OracleComp RefWorld β)
    (hn : ∀ value budget,
      observed g (SphincsSecurity.QueryCap.run charged (nextC value) budget) =
        refObserved (wA hU ω g) (SphincsSecurity.QueryCap.run RefCharged (nextR value) budget))
    (budget : Nat) :
    observed g (SphincsSecurity.QueryCap.run charged
      (interactionC hU ω published program >>= fun result => nextC (result.1, result.2.1)) budget) =
    refObserved (wA hU ω g) (SphincsSecurity.QueryCap.run RefCharged
      (offlineInteraction (wA hU ω g) published program >>= nextR) budget) := by
  induction program using OracleComp.inductionOn generalizing nextC nextR budget with
  | pure value =>
      rw [interactionC_pure, offlineInteraction_pure, pure_bind, pure_bind]
      exact hn (value, []) budget
  | query_bind input next ih =>
      rcases input with (n | x) | request
      · rw [interactionC_coin, offlineInteraction_world, bind_assoc, bind_assoc,
          observed_run_coin_bind, refObserved_run_coin_bind]
        apply bind_congr
        intro coin
        exact ih coin nextC nextR hn budget
      · rw [interactionC_public, offlineInteraction_world]
        simp only [bind_assoc, pure_bind]
        rw [observed_run_hashC_bind, refObserved_run_public_bind]
        cases budget with
        | zero => rfl
        | succ remaining => exact congrArg _ (ih _ nextC nextR hn remaining)
      · rw [interactionC_request, offlineInteraction_request]
        simp only [bind_assoc, pure_bind, bind_map_left]
        rw [observed_run_signC_bind, refObserved_run_offlineSign_bind]
        split_ifs
        · exact ih _
            (fun value => nextC (value.1, ⟨request, evalWithAnswerFn (wA hU ω g)
              (Paired.authenticatedSign published request)⟩ :: value.2))
            (fun value => nextR (value.1, ⟨request, evalWithAnswerFn (wA hU ω g)
              (Paired.authenticatedSign published request)⟩ :: value.2))
            (fun value remaining => hn _ remaining) _
        · rfl


end ClaudeWCT.W9.T3.Security.WPair.Paired.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Paired.Counted
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots (RefWorld RefCharged ticks)
open SphincsSecurity.Concrete.SecretGuessObservation
open ClaudeWCT.W9.T3.Security.WPair.Counted
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local instance] ClaudeWCT.W9.T3.Security.WPair.Counted.chargedDecidable
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)
attribute [local irreducible] signC interactionC Paired.signCharge WPair.Counted.hashC WPair.Counted.programC keygen
theorem funded_signC_bind {α : Type} (published : SigGolfCandidate.T3.Cache) (request : Request)
    (next : Option SigGolfCandidate.Research.SharedForest.Signature → OracleComp CountSpec α) (credit : Nat)
    (hn : ∀ value remaining, Funded (next value) remaining) :
    Funded (signC hU ω published request >>= next) credit := by
  rw [signC, bind_assoc]
  apply funded_bind _ _ _ (funded_clocks _ _)
  intro _ remaining
  unfold Paired.signW
  rw [liftW_bind, bind_assoc]
  simp only [liftW_pure, pure_bind]
  exact funded_discloseAll_bind _ _ _ (fun values remaining => hn _ remaining)

theorem funded_interactionC_bind {α β : Type} (published : SigGolfCandidate.T3.Cache)
    (program : OracleComp Paired.Interaction α)
    (next : (α × QueryLog Paired.Requests × List Wots.Entry) → OracleComp CountSpec β) (credit : Nat)
    (hn : ∀ value remaining, Funded (next value) remaining) :
    Funded (interactionC hU ω published program >>= next) credit := by
  induction program using OracleComp.inductionOn generalizing next credit with
  | pure value => simpa only [interactionC_pure, pure_bind] using hn (value, [], []) credit
  | query_bind input continuation ih =>
      rcases input with (n | x) | request
      · rw [interactionC_coin, bind_assoc, funded_query_bind]
        refine ⟨Nat.zero_le _, ?_⟩
        intro coin
        exact ih coin next credit hn
      · rw [interactionC_public]
        simp only [bind_assoc, pure_bind]
        apply funded_hashC_bind
        intro answer remaining
        exact ih answer _ remaining (fun result remaining => hn _ remaining)
      · rw [interactionC_request]
        simp only [bind_assoc, pure_bind]
        apply funded_signC_bind
        intro signature remaining
        exact ih signature _ remaining (fun result remaining => hn _ remaining)

theorem dropClocks_signC (published : SigGolfCandidate.T3.Cache) (request : Request) :
    dropClocks (signC hU ω published request) = Paired.signW hU ω published request := by
  rw [signC, dropClocks_bind, dropClocks_clocks, pure_bind, dropClocks_liftW]

theorem dropClocks_interactionC (published : SigGolfCandidate.T3.Cache) {α : Type}
    (program : OracleComp Paired.Interaction α) :
    dropClocks (interactionC hU ω published program) = Paired.interactionW hU ω published program := by
  induction program using OracleComp.inductionOn with
  | pure value => rw [interactionC_pure, Paired.interactionW_pure, dropClocks_pure]
  | query_bind input next ih =>
      rcases input with (n | x) | request
      · rw [interactionC_coin, Paired.interactionW_coin, dropClocks_bind]
        change (liftM (WSpec.query (.inl n)) >>= _) = _
        apply bind_congr
        intro answer
        exact ih answer
      · rw [interactionC_public, dropClocks_bind, dropClocks_hashC]
        change (_ >>= _) = (hashW hU ω x >>= fun answer => Paired.interactionW hU ω published (next answer) >>= fun rest =>
          pure (rest.1, rest.2.1, (x, answer) :: rest.2.2))
        apply bind_congr
        intro answer
        rw [dropClocks_bind, ih]
        rfl
      · rw [interactionC_request, dropClocks_bind, dropClocks_signC]
        change (_ >>= _) = (Paired.signW hU ω published request >>= fun signature =>
          Paired.interactionW hU ω published (next signature) >>= fun rest =>
          pure (rest.1, ⟨request, signature⟩ :: rest.2.1, rest.2.2))
        apply bind_congr
        intro signature
        rw [dropClocks_bind, ih]
        rfl


noncomputable def experimentC {α β : Type} (published : SigGolfCandidate.T3.Cache)
    (program : OracleComp Paired.Interaction α) (finish : (α × QueryLog Paired.Requests) → M β) :
    OracleComp CountSpec (β × QueryLog Paired.Requests × List Wots.Entry) := do
  let interaction ← interactionC hU ω published program
  let result ← WPair.Counted.programC hU ω (finish (interaction.1, interaction.2.1))
  pure (result.1, interaction.2.1, interaction.2.2 ++ result.2)
noncomputable def experimentR {α β : Type} (answers : Answers) (published : SigGolfCandidate.T3.Cache)
    (program : OracleComp Paired.Interaction α) (finish : (α × QueryLog Paired.Requests) → M β) :
    OracleComp RefWorld β := do
  let interaction ← offlineInteraction answers published program
  simulateQ Wots.verdictImpl (finish interaction)
noncomputable def referenceRun {α β : Type} (answers : Answers) (published : SigGolfCandidate.T3.Cache)
    (program : OracleComp Paired.Interaction α) (finish : (α × QueryLog Paired.Requests) → M β) (budget : Nat) :=
  simulateQ (Wots.refImpl answers)
    (SphincsSecurity.QueryCap.recorded (SphincsSecurity.QueryCap.run RefCharged
      (experimentR answers published program finish) budget))

attribute [local irreducible] experimentC experimentR referenceRun

theorem funded_experimentC {α β : Type} (published : SigGolfCandidate.T3.Cache)
    (program : OracleComp Paired.Interaction α) (finish : (α × QueryLog Paired.Requests) → M β) (credit : Nat) :
    Funded (experimentC hU ω published program finish) credit := by
  unfold experimentC
  apply funded_interactionC_bind
  intro result remaining
  apply WPair.Counted.funded_programC_bind
  intro value remaining
  exact funded_pure _ _

theorem dropClocks_experimentC {α β : Type} (published : SigGolfCandidate.T3.Cache)
    (program : OracleComp Paired.Interaction α) (finish : (α × QueryLog Paired.Requests) → M β) :
    dropClocks (experimentC hU ω published program finish) = Paired.experimentW hU ω published program finish := by
  unfold experimentC Paired.experimentW
  rw [dropClocks_bind, dropClocks_interactionC]
  apply bind_congr
  intro interaction
  rw [dropClocks_bind, WPair.Counted.dropClocks_programC]
  rfl

theorem experimentC_transport (hidden : CanonTable.HiddenF) {α β : Type}
    (published : SigGolfCandidate.T3.Cache) (program : OracleComp Paired.Interaction α)
    (finish : (α × QueryLog Paired.Requests) → M β) (budget : Nat) :
    observed hidden (SphincsSecurity.QueryCap.run charged
      (experimentC hU ω published program finish >>= fun result => pure result.1) budget) =
    refObserved (wA hU ω hidden) (SphincsSecurity.QueryCap.run RefCharged
      (experimentR (wA hU ω hidden) published program finish) budget) := by
  unfold experimentC experimentR
  simp only [bind_assoc, pure_bind]
  refine interactionC_transport hU ω hidden published program
    (fun interaction => WPair.Counted.programC hU ω (finish interaction) >>= fun checked => pure checked.1)
    (fun interaction => simulateQ Wots.verdictImpl (finish interaction)) ?_ budget
  intro interaction remaining
  have ht := WPair.Counted.programC_transport hU ω hidden (finish interaction)
    (fun value => pure value) (fun value => pure value) (fun value remaining => rfl) remaining
  simpa only [bind_pure] using ht

theorem public_transport (hidden : CanonTable.HiddenF) {α β : Type}
    (published : SigGolfCandidate.T3.Cache) (program : OracleComp Paired.Interaction α)
    (finish : (α × QueryLog Paired.Requests) → M β) (budget : Nat) :
    (fun result => publicInputs result.2) <$> simulateQ (fixedCount hidden)
      (cappedProgram (experimentC hU ω published program finish) budget) =
    (fun result => refPublicInputs result.2) <$>
      referenceRun (wA hU ω hidden) published program finish budget := by
  have ht := congrArg (Functor.map Prod.snd)
    (experimentC_transport hU ω hidden published program finish budget)
  rw [bind_pure_comp, run_map_result, observed_map] at ht
  simpa only [observed_recorded, refObserved_recorded, Functor.map_map, cappedProgram,
    referenceRun] using ht

theorem completed_tracks (hidden : CanonTable.HiddenF) {α β : Type}
    (published : SigGolfCandidate.T3.Cache) (program : OracleComp Paired.Interaction α)
    (finish : (α × QueryLog Paired.Requests) → M β)
    (hfinish : ∀ value, PublicVerdict.Only (finish value)) (budget remaining : Nat)
    (value : β × QueryLog Paired.Requests × List Wots.Entry) (queries : List CountSpec.Domain) (final : CountState)
    (hr : fixedRun countEnvironment (Guess.Fam.phi hidden.1 hidden.2)
      (cappedProgram (experimentC hU ω published program finish) budget)
      countInit ((some (value, remaining), queries), final) ≠ 0) :
    Paired.Tracks hU ω hidden init final value.2.1 value.2.2 := by
  apply Paired.experimentW_tracks hU ω hidden published program finish hfinish init (value, final)
  exact fixedRun_recorded_cap_erasure hidden _ _ (dropClocks_experimentC hU ω published program finish)
    budget remaining value queries countInit final hr

theorem event_le_external {α β : Type}
    (published : SigGolfCandidate.T3.Cache) (program : OracleComp Paired.Interaction α)
    (finish : (α × QueryLog Paired.Requests) → M β)
    (hfinish : ∀ value, PublicVerdict.Only (finish value)) (budget : Nat) (hbudget : budget < 2^128)
    (event : CanonTable.HiddenF → (Option ((β × QueryLog Paired.Requests × List Wots.Entry) × Nat) × List CountSpec.Domain) → Prop)
    (hevent : ∀ hidden result, event hidden result → ∃ output remaining,
      result.1 = some (output, remaining) ∧ ¬Paired.OverflowIn (wA hU ω hidden) output.2.1 ∧
      ∃ cell, Paired.GuessedIn (wA hU ω hidden) output.2.1 output.2.2 cell) :
    Pr[fun result => event result.1 result.2 | WPair.Counted.Generic.countedProgramRun
      (cappedProgram (experimentC hU ω published program finish) budget)] ≤
      (((2^128-budget : Nat) : ENNReal))⁻¹ *
      ∑' result, Pr[= result | withRun countEnvironment (Guess.Fam.sampler PUnit)
        (cappedProgram (experimentC hU ω published program finish) budget) countInit] *
        (probeCount (publicInputs result.1.2) : ENNReal) := by
  apply (WPair.Counted.Generic.counted_program_event_le_world _ event
    (fun result => ¬Guess.Fam.Bad result.2 ∧ result.2.probes ≤ budget ∧ result.2.guesses.Nonempty) ?_).trans
    (WPair.Counted.Generic.first_probe_le_external _
      (funded_experimentC hU ω published program finish 0) budget hbudget)
  intro hidden result hr he
  obtain ⟨output, remaining, hout, hno, cell, hg⟩ := hevent hidden result.1 he
  rcases result with ⟨⟨out, queries⟩, final⟩
  dsimp only at hout
  subst out
  have ht := completed_tracks hU ω hidden published program finish hfinish budget remaining output queries final hr
  refine ⟨Paired.tracked_noBad hU ω hidden final _ _ ht hno, ?_,
    Paired.tracked_guessed hU ω hidden final _ _ ht cell hg⟩
  apply WPair.Counted.Generic.capped_probes_le_budget _ budget
    (funded_experimentC hU ω published program finish 0)
    (fixedSampler (Guess.Fam.phi hidden.1 hidden.2)) _
  rwa [withRun_fixedSampler]
end ClaudeWCT.W9.T3.Security.WPair.Paired.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Paired.Counted
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.SecretGuessObservation
open ClaudeWCT.W9.T3.Security.WPair.Counted
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local instance] ClaudeWCT.W9.T3.Security.WPair.Counted.chargedDecidable
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)
variable {α β : Type} (published : SigGolfCandidate.T3.Cache) (program : OracleComp Paired.Interaction α)
  (finish : (α × QueryLog Paired.Requests) → M β) (budget : Nat)

abbrev RunResult := Option ((β × QueryLog Paired.Requests × List Wots.Entry) × Nat) × List CountSpec.Domain

 theorem public_distribution :
    (fun result => publicInputs result.1.2) <$>
      withRun (Result := RunResult (β := β)) countEnvironment (Guess.Fam.sampler PUnit)
        (cappedProgram (experimentC hU ω published program finish) budget) countInit =
    𝒮[do
      let hidden ← ($ᵗ CanonTable.HiddenF : ProbComp _)
      let result ← referenceRun (wA hU ω hidden) published program finish budget
      pure (refPublicInputs result.2)] := by
  rw [WPair.Counted.Generic.public_program_distribution]
  apply congrArg (fun experiment : ProbComp (List HashInput) => 𝒮[experiment])
  apply bind_congr
  intro hidden
  simpa only [bind_pure_comp] using public_transport hU ω hidden published program finish budget

 theorem public_payment_le_reference :
    (∑' result, Pr[= result | withRun (Result := RunResult (β := β)) countEnvironment (Guess.Fam.sampler PUnit)
      (cappedProgram (experimentC hU ω published program finish) budget) countInit] *
      (probeCount (publicInputs result.1.2) : ENNReal)) ≤
    ∑' hidden, Pr[= hidden | ($ᵗ CanonTable.HiddenF : ProbComp _)] *
      ∑' run, Pr[= run | referenceRun (wA hU ω hidden) published program finish budget] *
        (Wots.otherCount ⟨wA hU ω hidden, (evalWithAnswerFn (wA hU ω hidden) keygen).1,
          Wots.traceOf (wA hU ω hidden) run.2⟩ : ENNReal) := by
  rw [← tsum_probOutput_map_mul _ (fun result : RunResult (β := β) × CountState => publicInputs result.1.2)
    (fun inputs => (probeCount inputs : ENNReal)), public_distribution hU ω published program finish budget]
  simp only [bind_pure_comp, evalSPMF_bind, evalSPMF_map]
  rw [tsum_probOutput_bind_mul]
  apply ENNReal.tsum_le_tsum
  intro hidden
  simp only [probOutput_evalSPMF]
  apply mul_le_mul' le_rfl
  rw [tsum_probOutput_map_mul]
  simp only [probOutput_evalSPMF]
  apply ENNReal.tsum_le_tsum
  intro run
  apply mul_le_mul' le_rfl
  rw [refPublicInputs_eq_trace (wA hU ω hidden)]
  exact_mod_cast probeCount_le_other (wA hU ω hidden) _ (Wots.traceOf (wA hU ω hidden) run.2)

 theorem event_le_other
    (hfinish : ∀ value, PublicVerdict.Only (finish value)) (hbudget : budget < 2^128)
    (event : CanonTable.HiddenF → RunResult (β := β) → Prop)
    (hevent : ∀ hidden result, event hidden result → ∃ output remaining,
      result.1 = some (output, remaining) ∧ ¬Paired.OverflowIn (wA hU ω hidden) output.2.1 ∧
      ∃ cell, Paired.GuessedIn (wA hU ω hidden) output.2.1 output.2.2 cell) :
    Pr[fun result => event result.1 result.2 | WPair.Counted.Generic.countedProgramRun
      (cappedProgram (experimentC hU ω published program finish) budget)] ≤
      (((2^128-budget : Nat) : ENNReal))⁻¹ *
      (∑' hidden, Pr[= hidden | ($ᵗ CanonTable.HiddenF : ProbComp _)] *
      ∑' run, Pr[= run | referenceRun (wA hU ω hidden) published program finish budget] *
        (Wots.otherCount ⟨wA hU ω hidden, (evalWithAnswerFn (wA hU ω hidden) keygen).1,
          Wots.traceOf (wA hU ω hidden) run.2⟩ : ENNReal)) :=
  (event_le_external hU ω published program finish hfinish budget hbudget event hevent).trans
    (mul_le_mul' le_rfl (public_payment_le_reference hU ω published program finish budget))
end ClaudeWCT.W9.T3.Security.WPair.Paired.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Paired.Counted
open ENNReal
set_option maxHeartbeats 1000000

theorem hazard_normalized {n q : Nat} (hq : q<n) {event charge : ENNReal}
    (hc : charge≠⊤) (he : event≤((n-q:Nat):ENNReal)⁻¹*charge) :
    (1-(q:ℝ)/(n:ℝ))*event.toReal≤charge.toReal/(n:ℝ) := by
  have hsub : 0<n-q := Nat.sub_pos_of_lt hq
  have hdn : ((n-q:Nat):ENNReal)≠0 := by exact_mod_cast Nat.ne_of_gt hsub
  have hfin : ((n-q:Nat):ENNReal)⁻¹*charge≠⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hdn) hc
  have hr := ENNReal.toReal_mono hfin he
  rw [ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_natCast,
    Nat.cast_sub (Nat.le_of_lt hq)] at hr
  have hnr : (0:ℝ)<n := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le q) hq)
  have hqr : (q:ℝ)<n := by exact_mod_cast hq
  have hh : event.toReal≤charge.toReal/((n:ℝ)-q) := by
    simpa only [div_eq_mul_inv,mul_comm] using hr
  have hp := (le_div_iff₀ (by linarith : (0:ℝ)<n-q)).mp hh
  apply (le_div_iff₀ hnr).mpr
  calc
    ((1-(q:ℝ)/(n:ℝ))*event.toReal)*(n:ℝ) = event.toReal*((n:ℝ)-q) := by field_simp
    _ ≤ charge.toReal := hp
end ClaudeWCT.W9.T3.Security.WPair.Paired.Counted

namespace ClaudeWCT.Bank.NearWorld
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.BPair (AuxL AuxSpecL LazyMem)
open SphincsSecurity.Concrete
open ClaudeWCT.W9.T3.Security
open ClaudeWCT.W9.T3.Security.CaseC (NearGhost projS GState samplerG initG RowsFrame
 runWith_bind' runWith_pure' expectedValue_liftM_pmf expectedValue_uniformOfFintype Extends search_replays_gen
 SuperProg superProg_pure superProg_bind spmf_ev_mono spmf_ev_le)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpec P)
def Replays (S : FtsBankSpec P) (rows : Sampling.RCache) (rho : Digest) (m : Message) (found : Option (BitVec 32 × HashOutput)) : Prop :=
  ∀ cache', Extends rows cache' →
    ∀ r' ∈ support (Sampling.roRun 0 (S.search rho m 0 (2^21)) cache'), r' = (found, cache')
theorem Replays.mono {S : FtsBankSpec P} {rows rows' : Sampling.RCache} {rho : Digest} {m : Message} {found}
    (h : (Replays S) rows rho m found) (hext : Extends rows rows') : (Replays S) rows' rho m found :=
  fun cache' hc => h cache' (hext.trans hc)
theorem replays_of_search (S : FtsBankSpec P) (rho : Digest) (m : Message) (rows : Sampling.RCache) (r)
    (hr : r ∈ support (Sampling.roRun 0 (S.search rho m 0 (2^21)) rows)) :
    Extends rows r.2 ∧ (Replays S) r.2 rho m r.1 := by
  unfold ClaudeWCT.Bank.FtsBankSpec.search at hr
  obtain ⟨h1, h2⟩ := search_replays_gen 0 (Sampling.digestTrial rho m) S.decode _ _ 0 rows r hr
  refine ⟨h1, fun cache' hc r' hr' => ?_⟩
  unfold ClaudeWCT.Bank.FtsBankSpec.search at hr'
  exact h2 cache' hc r' hr'
def InvM (S : FtsBankSpec P) (M : LazyMem × NearGhost) : Prop :=
  (∀ v ∈ M.1.exposures, v ∈ M.2.fresh) ∧ M.2.fresh.length ≤ M.1.exposures.length ∧
    ∀ m rho, M.1.nonces m = some rho → ∃ found, (Replays S) M.1.rows rho m found ∧
      ∀ v ∈ (found.map Prod.snd).toList, v ∈ M.2.fresh
theorem invM_empty (S : FtsBankSpec P) : (InvM S) (LazyMem.empty, NearGhost.empty) := by
  refine ⟨fun v hv => by simp [LazyMem.empty] at hv, by simp [LazyMem.empty, NearGhost.empty], ?_⟩
  intro m rho h
  simp [LazyMem.empty] at h
noncomputable def ghostPot (S : FtsBankSpec P) (q : Nat) (M : LazyMem × NearGhost) : ENNReal :=
  NearMemory.nearMemPotential S q M.1.births M.2.fresh M.2.reused M.1.rows M.1.nonces
noncomputable def ΦI (S : FtsBankSpec P) (q : Nat) (s : GState) : ENNReal := if (InvM S) s.memory then (ghostPot S) q s.memory else ⊤
theorem ΦI_initial (S : FtsBankSpec P) (rate : ENNReal)
    (hrate : ClaudeWCT.Numerics.Law.lawAvg S.law (2^32) S.price ≤ rate) (q : Nat) :
    (ΦI S) q initG ≤ (q:ENNReal)*(rate+S.admBound)/2^128 := by
  unfold ΦI
  rw [if_pos (show (InvM S) initG.memory from (invM_empty S))]
  exact NearMemory.mem_initial S rate hrate q
theorem superProg_of_memory (S : FtsBankSpec P) {β : Type} (slot q : Nat) (W : OracleComp WPair.WSpecL β)
    (h : ∀ s r, SecretGuessObservation.runWith ((implG S) slot) W s r ≠ 0 → r.2.memory = s.memory) :
    SuperProg ((implG S) slot) ((ΦI S) q) W := by
  intro s
  apply spmf_ev_le
  intro r hr
  unfold ΦI
  rw [h s r hr]
theorem coin_memory (S : FtsBankSpec P) (slot n : Nat) (s : GState) (r : Fin (n + 1) × GState)
    (hr : SecretGuessObservation.runWith ((implG S) slot) (WPair.coinReqL n) s r ≠ 0) : r.2.memory = s.memory := by
  obtain ⟨res, hres, rfl⟩ := (aux_nonzero S) slot (.coin n) s r hr
  have hres' : res ∈ (WPair.envL.auxiliary (projS s) (.coin n)).support := (PMF.mem_support_iff _ _).mpr hres
  change res ∈ ((fun c => (c, (projS s).memory)) <$> PMF.uniformOfFintype (Fin (n + 1))).support at hres'
  rw [PMF.monad_map_eq_map, PMF.mem_support_map_iff] at hres'
  obtain ⟨c, -, rfl⟩ := hres'
  rfl
theorem secret_memory (S : FtsBankSpec P) (slot : Nat) (p : (Guess.GCoord × Digest) ⊕ Guess.GCoord)
    (s : GState) (r : (WPair.WSpecL.Range (.inr p)) × GState)
    (hr : SecretGuessObservation.runWith ((implG S) slot) (liftM (WPair.WSpecL.query (.inr p))) s r ≠ 0) :
    r.2.memory = s.memory := by
  unfold SecretGuessObservation.runWith at hr
  rw [simulateQ_spec_query] at hr
  rcases p with ⟨c, v⟩ | c
  · change ((fun hit => (hit, SecretGuessObservation.afterTrial ((envG S) WPair.envL) s c v hit)) <$>
      SecretGuessObservation.forcedTrialWith samplerG slot s c v) r ≠ 0 at hr
    simp only [map_eq_bind_pure_comp, RetainedObservation.bind_nonzero, Function.comp_def, ne_eq,
      SPMF.pure_apply_eq_zero_iff, not_not] at hr
    obtain ⟨hit, -, rfl⟩ := hr
    rfl
  · change ((fun value => (value, SecretGuessObservation.afterDisclosure ((envG S) WPair.envL) s c value)) <$>
      samplerG.discloseLaw s c) r ≠ 0 at hr
    simp only [map_eq_bind_pure_comp, RetainedObservation.bind_nonzero, Function.comp_def, ne_eq,
      SPMF.pure_apply_eq_zero_iff, not_not] at hr
    obtain ⟨value, -, rfl⟩ := hr
    rfl
theorem coin_ΦI (S : FtsBankSpec P) (slot q n : Nat) : SuperProg ((implG S) slot) ((ΦI S) q) (WPair.coinReqL n) :=
  (superProg_of_memory S) slot q _ fun s r hr => (coin_memory S) slot n s r hr
theorem guess_ΦI (S : FtsBankSpec P) (slot q : Nat) (c : Guess.GCoord) (v : Digest) :
    SuperProg ((implG S) slot) ((ΦI S) q) (Guess.trialQ (auxSpec := AuxSpecL) c v) :=
  (superProg_of_memory S) slot q _ fun s r hr => (secret_memory S) slot (.inl (c, v)) s r hr
theorem disclose_ΦI (S : FtsBankSpec P) (slot q : Nat) (c : Guess.GCoord) :
    SuperProg ((implG S) slot) ((ΦI S) q) (Guess.discloseQ (auxSpec := AuxSpecL) (V := Digest) c) :=
  (superProg_of_memory S) slot q _ fun s r hr => (secret_memory S) slot (.inr c) s r hr
theorem mapM_ΦI (S : FtsBankSpec P) {α β : Type} (slot q : Nat) (f : α → OracleComp WPair.WSpecL β)
    (hf : ∀ a, SuperProg ((implG S) slot) ((ΦI S) q) (f a)) :
    ∀ l : List α, SuperProg ((implG S) slot) ((ΦI S) q) (l.mapM f)
  | [] => superProg_pure _ _ _
  | a :: l => by
      rw [List.mapM_cons]
      exact superProg_bind _ _ (hf a) fun _ => superProg_bind _ _ ((mapM_ΦI S) slot q f hf l) fun _ => superProg_pure _ _ _
theorem discloseAll_ΦI (S : FtsBankSpec P) (slot q : Nat) (cs : List Guess.GCoord) :
    SuperProg ((implG S) slot) ((ΦI S) q) (Guess.discloseAll (auxSpec := AuxSpecL) (V := Digest) cs) :=
  (mapM_ΦI S) slot q _ (fun c => (disclose_ΦI S) slot q c) cs
theorem probeW_ΦI (S : FtsBankSpec P) (slot q : Nat) {R : Type} (step : Guess.ChainAddr → Fin 4 → Digest → R)
    (top : Guess.ChainAddr → R) (miss : R) (a : Guess.ChainAddr) (p : Fin 4) (v : Digest) :
    SuperProg ((implG S) slot) ((ΦI S) q) (Guess.probeW (auxSpec := AuxSpecL) step top miss a p v) := by
  unfold Guess.probeW
  refine superProg_bind _ _ ((guess_ΦI S) slot q (a, p) v) fun hit => ?_
  split
  · split
    · exact superProg_bind _ _ ((disclose_ΦI S) slot q _) fun _ => superProg_pure _ _ _
    · exact superProg_pure _ _ _
  · exact superProg_pure _ _ _
theorem ev_single_aux (S : FtsBankSpec P) (slot : Nat) (i : AuxL) (s : GState) (G : AuxSpecL.Range i × GState → ENNReal) :
    expectedValue (SecretGuessObservation.runWith ((implG S) slot) (liftM (WPair.WSpecL.query (.inl i))) s) G =
      expectedValue (WPair.envL.auxiliary (projS s) i) (fun r =>
        G (r.1, { s with memory := (r.2, (ghostStep S) s.memory.1 i r.1 s.memory.2) })) := by
  have h := (ev_aux_bind S) slot i pure s G
  rw [bind_pure] at h
  rw [h]
  apply congrArg
  funext r
  rw [runWith_pure', expectedValue_pure]
theorem birth_ΦI (S : FtsBankSpec P) (slot q : Nat) (x : HashInput) : SuperProg ((implG S) slot) ((ΦI S) q) (WPair.birthReq x) := by
  intro s
  by_cases hinv : (InvM S) s.memory
  swap
  · unfold ΦI; rw [if_neg hinv]; exact le_top
  unfold WPair.birthReq
  rw [(ev_single_aux S)]
  change expectedValue (BPair.rowStep s.memory.1 x true (PMF.uniformOfFintype HashOutput)) _ ≤ _
  unfold BPair.rowStep
  cases hx : s.memory.1.rows x with
  | some a =>
      simp only
      rw [expectedValue_pure]
      exact le_of_eq rfl
  | none =>
      simp only
      split_ifs with hd
      · rw [expectedValue_map, ev_uniform_eq S]
        have hpt : ∀ a : HashOutput, (ΦI S) q { s with memory := (s.memory.1.readRow x a true,
            (ghostStep S) s.memory.1 (.birth x) a s.memory.2) } =
            NearMemory.nearMemPotential S q (s.memory.1.births ++ [a]) s.memory.2.fresh s.memory.2.reused
              (s.memory.1.rows.cacheQuery x a) s.memory.1.nonces := by
          intro a
          have hext : Extends s.memory.1.rows (s.memory.1.rows.cacheQuery x a) := by
            intro y b hy
            have hne : y ≠ x := fun he => by rw [he, hx] at hy; cases hy
            exact (QueryCache.cacheQuery_of_ne s.memory.1.rows a hne).trans hy
          have hinv' : (InvM S) (s.memory.1.readRow x a true, (ghostStep S) s.memory.1 (.birth x) a s.memory.2) := by
            obtain ⟨h1, h2, h3⟩ := hinv
            refine ⟨h1, h2, fun m rho hm => ?_⟩
            obtain ⟨found, hrep, hf⟩ := h3 m rho hm
            exact ⟨found, hrep.mono hext, hf⟩
          unfold ΦI
          rw [if_pos hinv']
          rfl
        simp_rw [hpt]
        unfold ΦI
        rw [if_pos hinv]
        exact NearMemory.mem_birth S q _ _ _ _ _ x hx
      · rw [expectedValue_pure]
        exact le_of_eq rfl
theorem hashL_ΦI (S : FtsBankSpec P) {U : Finset HashInput} (hU : ClaudeWCT.W9.T3.Security.CanonGraph.canonInputs ⊆ U) (slot q : Nat) (ω : ClaudeWCT.W9.CanonTable.Omega U)
    (x : HashInput) : SuperProg ((implG S) slot) ((ΦI S) q) (WPair.hashL hU ω x) := by
  unfold WPair.hashL
  cases Guess.decodeProbe x with
  | some p => exact (probeW_ΦI S) slot q _ _ _ _ _ _
  | none =>
      simp only
      split_ifs
      · exact (birth_ΦI S) slot q x
      · exact superProg_pure _ _ _
end ClaudeWCT.Bank.NearWorld

namespace ClaudeWCT.Bank.NearWorld
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.BPair (AuxL AuxSpecL LazyMem)
open SphincsSecurity.Concrete
open ClaudeWCT.W9.T3.Security
open ClaudeWCT.W9.T3.Security.CaseC (NearGhost projS GState samplerG initG RowsFrame
 runWith_bind' runWith_pure' Extends SuperProg spmf_ev_mono spmf_ev_le spmf_ev_zero pc_ev_offsupport ev_uniform_digest)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpec P)
theorem search_support (S : FtsBankSpec P) (slot : Nat) (rho : Digest) (m : Message) (s : GState) (r)
    (hr : SecretGuessObservation.runWith ((implG S) slot) ((searchL S) rho m 0 (2^21)) s r ≠ 0) :
    (r.1, r.2.memory.1.rows) ∈
      support (Sampling.roRun 0 (S.search rho m 0 (2^21)) s.memory.1.rows) := by
  have hlaw := (search_law S) slot rho m (fun f rows =>
    if (f, rows) ∈ support (Sampling.roRun 0 (S.search rho m 0 (2^21)) s.memory.1.rows)
    then 0 else 1) (2^21) 0 s
  simp only [Prod.mk.eta] at hlaw
  rw [pc_ev_offsupport] at hlaw
  have h0 := spmf_ev_zero _ hlaw r hr
  by_contra hc
  rw [if_neg hc] at h0
  exact one_ne_zero h0
theorem ev_nonce_cached (S : FtsBankSpec P) {β : Type} (slot : Nat) (m : Message) (rho : Digest)
    (k : Digest → OracleComp WPair.WSpecL β) (s : GState) (hn : s.memory.1.nonces m = some rho)
    (G : β × GState → ENNReal) :
    expectedValue (SecretGuessObservation.runWith ((implG S) slot) (WPair.nonceReq m >>= k) s) G =
      expectedValue (SecretGuessObservation.runWith ((implG S) slot) (k rho)
        ⟨s.allowed, s.retired, s.guesses, s.probes, (s.memory.1, (ghostStep S) s.memory.1 (.nonce m) rho s.memory.2)⟩) G := by
  unfold WPair.nonceReq
  rw [(ev_aux_bind S)]
  change expectedValue (BPair.nonceStep s.memory.1 m (PMF.uniformOfFintype Digest)) _ = _
  unfold BPair.nonceStep
  rw [hn]
  simp only
  rw [expectedValue_pure]
theorem ev_nonce_fresh (S : FtsBankSpec P) {β : Type} (slot : Nat) (m : Message) (k : Digest → OracleComp WPair.WSpecL β)
    (s : GState) (hn : s.memory.1.nonces m = none) (G : β × GState → ENNReal) :
    expectedValue (SecretGuessObservation.runWith ((implG S) slot) (WPair.nonceReq m >>= k) s) G =
      expectedValue ($ᵗ Digest : ProbComp Digest) (fun v =>
        expectedValue (SecretGuessObservation.runWith ((implG S) slot) (k v)
          ⟨s.allowed, s.retired, s.guesses, s.probes,
            (s.memory.1.drawNonce m v, (ghostStep S) s.memory.1 (.nonce m) v s.memory.2)⟩) G) := by
  unfold WPair.nonceReq
  rw [(ev_aux_bind S)]
  change expectedValue (BPair.nonceStep s.memory.1 m (PMF.uniformOfFintype Digest)) _ = _
  unfold BPair.nonceStep
  rw [hn]
  simp only
  rw [expectedValue_map, ev_uniform_digest]
theorem ev_expose_finish_le (S : FtsBankSpec P) {β : Type} (slot q : Nat)
    (finish : Digest → Option (BitVec 32 × HashOutput) → OracleComp WPair.WSpecL β)
    (hfinish : ∀ rho found, SuperProg ((implG S) slot) ((ΦI S) q) (finish rho found))
    (rho : Digest) (found : Option (BitVec 32 × HashOutput)) (s2 : GState) :
    expectedValue (SecretGuessObservation.runWith ((implG S) slot)
      (WPair.exposeReq (found.map Prod.snd) >>= fun _ => finish rho found) s2)
      (fun r => (ΦI S) q r.2) ≤
    (ΦI S) q ⟨s2.allowed,s2.retired,s2.guesses,s2.probes,(s2.memory.1.expose (found.map Prod.snd),
      (ghostStep S) s2.memory.1 (.expose (found.map Prod.snd)) () s2.memory.2)⟩ := by
  unfold WPair.exposeReq
  rw [(ev_aux_bind S)]
  change expectedValue (pure ((),s2.memory.1.expose (found.map Prod.snd)):PMF _) _ ≤ _
  rw [expectedValue_pure]
  exact hfinish rho found _

noncomputable def searchWithNonce (S : FtsBankSpec P) {β : Type} (m : Message)
    (finish : Digest → Option (BitVec 32 × HashOutput) → OracleComp WPair.WSpecL β) :
    OracleComp WPair.WSpecL β := do
  let rho ← WPair.nonceReq m
  let found ← (searchL S) rho m 0 (2^21)
  let _ ← WPair.exposeReq (found.map Prod.snd)
  finish rho found

theorem searchWithNonce_ΦI (S : FtsBankSpec P) {β : Type} (slot q : Nat) (m : Message)
    (finish : Digest → Option (BitVec 32 × HashOutput) → OracleComp WPair.WSpecL β)
    (hfinish : ∀ rho found,SuperProg ((implG S) slot) ((ΦI S) q) (finish rho found)) :
    SuperProg ((implG S) slot) ((ΦI S) q) ((searchWithNonce S) m finish) := by
  unfold searchWithNonce
  intro s
  by_cases hinv : (InvM S) s.memory
  swap
  · unfold ΦI; rw [if_neg hinv]; exact le_top
  obtain ⟨hI1, hI2, hI3⟩ := hinv
  have hΦs : ΦI S q s = ghostPot S q s.memory := by unfold ΦI; rw [if_pos ⟨hI1, hI2, hI3⟩]
  cases hn : s.memory.1.nonces m with
  | some rho =>
      rw [(ev_nonce_cached S) slot m rho _ s hn, runWith_bind', expectedValue_bind]
      apply spmf_ev_le
      intro r hr
      refine ((ev_expose_finish_le S) slot q finish hfinish rho r.1 r.2).trans ?_
      obtain ⟨found0, hrep, hf0⟩ := hI3 m rho hn
      have hsupp := (search_support S) slot rho m _ r hr
      obtain ⟨-, -, -, -, hg, hnon, hbir, hexp⟩ := (search_frame S) slot rho m (2^21) 0 _ r hr
      have hrr := hrep s.memory.1.rows (Extends.refl _) _ hsupp
      simp only [Prod.mk.injEq] at hrr
      obtain ⟨hfound, hrows⟩ := hrr
      have hg' : r.2.memory.2 = ⟨s.memory.2.reused, false, s.memory.2.fresh⟩ := by
        rw [hg]
        simp only [ghostStep, hn, reduceCtorEq, decide_false, Bool.false_and, Bool.or_false]
      have hnon' : r.2.memory.1.nonces = s.memory.1.nonces := hnon
      have hbir' : r.2.memory.1.births = s.memory.1.births := hbir
      have hexp' : r.2.memory.1.exposures = s.memory.1.exposures := hexp
      have hinv' : (InvM S) (r.2.memory.1.expose (r.1.map Prod.snd),
          (ghostStep S) r.2.memory.1 (.expose (r.1.map Prod.snd)) () r.2.memory.2) := by
        rw [hg']
        simp only [ghostStep, Bool.false_eq_true, if_false]
        refine ⟨fun v hv => ?_, ?_, fun m' rho' hm' => ?_⟩
        · simp only [LazyMem.expose, List.mem_append] at hv
          rcases hv with hv | hv
          · rw [hexp'] at hv; exact hI1 v hv
          · rw [hfound] at hv; exact hf0 v hv
        · simp only [LazyMem.expose, List.length_append]
          rw [hexp']
          exact hI2.trans (Nat.le_add_right _ _)
        · simp only [LazyMem.expose] at hm' ⊢
          rw [hnon'] at hm'
          rw [hrows]
          exact hI3 m' rho' hm'
      rw [hΦs]
      unfold ΦI
      dsimp only
      rw [if_pos hinv']
      apply le_of_eq
      unfold ghostPot
      rw [hg']
      simp only [ghostStep, Bool.false_eq_true, if_false, LazyMem.expose]
      rw [hbir', hrows, hnon']
  | none =>
      rw [(ev_nonce_fresh S) slot m _ s hn, hΦs]
      refine le_trans ?_ (NearMemory.mem_sign_fresh S q _ _ _ _ _ m hn 0 (2^21) (by decide))
      apply expectedValue_mono
      intro v
      rw [runWith_bind', expectedValue_bind]
      set s1 : GState := ⟨s.allowed, s.retired, s.guesses, s.probes, (s.memory.1.drawNonce m v,
        (ghostStep S) s.memory.1 (.nonce m) v s.memory.2)⟩ with hs1
      have hg1 : s1.memory.2 = ⟨(s.memory.2.reused || decide (S.Reuse s.memory.1.rows v m)), true,
          s.memory.2.fresh⟩ := by
        simp only [hs1, ghostStep, hn, decide_true, Bool.true_and]
      refine le_of_le_of_eq ?_ ((search_law S) slot v m (fun found rows' =>
        NearMemory.nearMemPotential S q s.memory.1.births (s.memory.2.fresh ++ (found.map Prod.snd).toList)
          (s.memory.2.reused || decide (S.Reuse s.memory.1.rows v m)) rows'
          (Function.update s.memory.1.nonces m (some v))) (2^21) 0 s1)
      apply spmf_ev_mono
      intro r hr
      refine ((ev_expose_finish_le S) slot q finish hfinish v r.1 r.2).trans (le_of_eq ?_)
      have hsupp := (search_support S) slot v m s1 r hr
      obtain ⟨hext, hrep⟩ := (replays_of_search S) v m _ _ hsupp
      obtain ⟨-, -, -, -, hg, hnon, hbir, hexp⟩ := (search_frame S) slot v m (2^21) 0 s1 r hr
      have hnon1 : r.2.memory.1.nonces = Function.update s.memory.1.nonces m (some v) := hnon
      have hbir1 : r.2.memory.1.births = s.memory.1.births := hbir
      have hexp1 : r.2.memory.1.exposures = s.memory.1.exposures := hexp
      have hext1 : Extends s.memory.1.rows r.2.memory.1.rows := hext
      have hgr : r.2.memory.2 = ⟨(s.memory.2.reused || decide (S.Reuse s.memory.1.rows v m)), true,
          s.memory.2.fresh⟩ := hg.trans hg1
      have hinv' : (InvM S) (r.2.memory.1.expose (r.1.map Prod.snd),
          (ghostStep S) r.2.memory.1 (.expose (r.1.map Prod.snd)) () r.2.memory.2) := by
        rw [hgr]
        simp only [ghostStep, if_true]
        refine ⟨fun x hx => ?_, ?_, fun m' rho' hm' => ?_⟩
        · simp only [LazyMem.expose, List.mem_append] at hx ⊢
          rcases hx with hx | hx
          · rw [hexp1] at hx; exact Or.inl (hI1 x hx)
          · exact Or.inr hx
        · simp only [LazyMem.expose, List.length_append]
          rw [hexp1]
          exact Nat.add_le_add_right hI2 _
        · simp only [LazyMem.expose] at hm' ⊢
          rw [hnon1] at hm'
          by_cases he : m' = m
          · subst he
            simp only [Function.update_self, Option.some.injEq] at hm'
            subst hm'
            exact ⟨r.1, hrep, fun x hx => List.mem_append_right _ hx⟩
          · rw [Function.update_of_ne he] at hm'
            obtain ⟨f', hrep', hf'⟩ := hI3 m' rho' hm'
            exact ⟨f', hrep'.mono hext1, fun x hx => List.mem_append_left _ (hf' x hx)⟩
      unfold ΦI
      dsimp only
      rw [if_pos hinv']
      unfold ghostPot
      rw [hgr]
      simp only [ghostStep, if_true, LazyMem.expose]
      rw [hbir1, hnon1]
end ClaudeWCT.Bank.NearWorld

namespace ClaudeWCT.Bank.NearWorld
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.BPair (AuxL AuxSpecL LazyMem)
open SphincsSecurity.Concrete
open ClaudeWCT.W9.T3.Security
open ClaudeWCT.W9.T3.Security.CaseC (NearGhost projS GState samplerG initG SuperProg)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpec P)
noncomputable def nearPayoff (q : Nat) (s : WPair.WStateL) : ENNReal :=
  if s.memory.births.length≤q ∧ s.memory.exposures.length≤2^32 ∧
      ∃ N∈s.memory.births,S.admissible N=true ∧ S.covered s.memory.exposures N then 1 else 0

theorem payoff_le_ΦI
    (hmono : ∀ X Y N,(∀ v∈X,v∈Y)→S.covered X N→S.covered Y N)
    (q : Nat) (s : GState) : nearPayoff S q (projS s)≤ΦI S q s := by
  unfold ΦI
  split_ifs with hinv
  · unfold nearPayoff
    split_ifs with hp
    · obtain ⟨hb,hl,N,hN,hadm,hcov⟩:=hp
      exact NearMemory.mem_win S q _ _ _ _ _ hb (hinv.2.1.trans hl)
        (Or.inr ⟨N,hN,hadm,hmono _ _ _ hinv.1 hcov⟩)
    · exact bot_le
  · exact le_top

theorem forced_payoff_le {β : Type}
    (hmono : ∀ X Y N,(∀ v∈X,v∈Y)→S.covered X N→S.covered Y N)
    (rate : ENNReal)
    (hrate : ClaudeWCT.Numerics.Law.lawAvg S.law (2^32) S.price≤rate)
    (slot q : Nat) (W : OracleComp WPair.WSpecL β)
    (hW : SuperProg (implG S slot) (ΦI S q) W) :
    expectedValue (SecretGuessObservation.forcedWithRun WPair.envL WPair.samplerL slot W WPair.initL)
      (fun r => nearPayoff S q r.2)≤(q:ENNReal)*(rate+S.admBound)/2^128 := by
  change expectedValue (SecretGuessObservation.runWith
    (SecretGuessObservation.forcedWithImpl WPair.envL WPair.samplerL slot) W (projS initG)) _≤_
  rw [expectedValue_project S WPair.envL slot W initG]
  exact (expectedValue_mono _ fun (r : β × GState) => payoff_le_ΦI S hmono q r.2).trans
    ((hW initG).trans (ΦI_initial S rate hrate q))

end ClaudeWCT.Bank.NearWorld

namespace ClaudeWCT.Bank.NearWorld.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3.Security
open SphincsSecurity.Concrete
open ClaudeWCT.W9.T3.Security.CaseC (SuperProg superProg_pure superProg_bind)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {P : Type} [Fintype P] [SampleableType P]
noncomputable local instance : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _

theorem nearSearch_eq (S : FtsBankSpec P)
    (hproducer : S.producer=SigGolfCandidate.Research.SharedForest.digestAccepted) (rho : Digest) (m : Message) (counter fuel : Nat) :
    NearWorld.searchL S rho m counter fuel=WPair.Paired.searchL rho m counter fuel := by
  induction fuel generalizing counter with
  | zero => rfl
  | succ fuel ih =>
      simp only [NearWorld.searchL,WPair.Paired.searchL,hproducer]
      apply bind_congr
      intro output
      split <;> first | rfl | exact ih _

section World
variable {U : Finset HashInput} (hU : ClaudeWCT.W9.T3.Security.CanonGraph.canonInputs⊆U)
variable (omega : ClaudeWCT.W9.CanonTable.Omega U) (slot q : Nat)

theorem finishL_ΦI (S : FtsBankSpec P)
    (hproducer : S.producer=SigGolfCandidate.Research.SharedForest.digestAccepted) {U : Finset HashInput} (hU : ClaudeWCT.W9.T3.Security.CanonGraph.canonInputs⊆U)
    (omega : ClaudeWCT.W9.CanonTable.Omega U) (slot q : Nat) (request : Request) (rho : Digest) (found : Option (BitVec 32×HashOutput)) :
    SuperProg (NearWorld.implG S slot) (NearWorld.ΦI S q)
      (WPair.Paired.finishL hU omega request rho found) := by
  rcases found with _ | ⟨c,output⟩
  · exact superProg_pure _ _ _
  · simp only [WPair.Paired.finishL]
    generalize WPair.Paired.signerLayersW hU omega request output=g
    cases g with
    | none => exact superProg_pure _ _ _
    | some layers =>
        exact superProg_bind _ _ (NearWorld.discloseAll_ΦI S slot q _) fun _ => superProg_pure _ _ _

theorem signL_ΦI (S : FtsBankSpec P)
    (hproducer : S.producer=SigGolfCandidate.Research.SharedForest.digestAccepted) {U : Finset HashInput} (hU : ClaudeWCT.W9.T3.Security.CanonGraph.canonInputs⊆U)
    (omega : ClaudeWCT.W9.CanonTable.Omega U) (slot q : Nat) (published : SigGolfCandidate.T3.Cache) (request : Request) :
    SuperProg (NearWorld.implG S slot) (NearWorld.ΦI S q)
      (WPair.Paired.signL hU omega published request) := by
  have h:=NearWorld.searchWithNonce_ΦI S slot q request.message
    (WPair.Paired.finishL hU omega request) (finishL_ΦI S hproducer hU omega slot q request)
  unfold NearWorld.searchWithNonce at h
  simp_rw [nearSearch_eq S hproducer] at h
  unfold WPair.Paired.signL
  split
  · exact h
  · exact superProg_pure _ _ _

theorem interactionL_ΦI (S : FtsBankSpec P)
    (hproducer : S.producer=SigGolfCandidate.Research.SharedForest.digestAccepted) {U : Finset HashInput} (hU : ClaudeWCT.W9.T3.Security.CanonGraph.canonInputs⊆U)
    (omega : ClaudeWCT.W9.CanonTable.Omega U) (slot q : Nat) (published : SigGolfCandidate.T3.Cache) {α : Type}
    (program : OracleComp WPair.Paired.Interaction α) :
    SuperProg (NearWorld.implG S slot) (NearWorld.ΦI S q)
      (WPair.Paired.interactionL hU omega published program) := by
  induction program using OracleComp.inductionOn with
  | pure value => exact superProg_pure _ _ _
  | query_bind input next ih =>
      rcases input with (n|x)|request
      · change SuperProg _ _ (WPair.coinReqL n >>= fun coin => _)
        exact superProg_bind _ _ (NearWorld.coin_ΦI S slot q n) ih
      · change SuperProg _ _ (WPair.hashL hU omega x >>= fun answer => _)
        exact superProg_bind _ _ (NearWorld.hashL_ΦI S hU slot q omega x) fun a =>
          superProg_bind _ _ (ih a) fun _ => superProg_pure _ _ _
      · change SuperProg _ _ (WPair.Paired.signL hU omega published request >>= fun signature => _)
        exact superProg_bind _ _ (signL_ΦI S hproducer hU omega slot q published request) fun a =>
          superProg_bind _ _ (ih a) fun _ => superProg_pure _ _ _

theorem experimentL_ΦI (S : FtsBankSpec P)
    (hproducer : S.producer=SigGolfCandidate.Research.SharedForest.digestAccepted) {U : Finset HashInput} (hU : ClaudeWCT.W9.T3.Security.CanonGraph.canonInputs⊆U)
    (omega : ClaudeWCT.W9.CanonTable.Omega U) (slot q : Nat) {α β : Type} (published : SigGolfCandidate.T3.Cache)
    (program : OracleComp WPair.Paired.Interaction α)
    (finish : (α × QueryLog WPair.Paired.Requests)→M β) :
    SuperProg (NearWorld.implG S slot) (NearWorld.ΦI S q)
      (WPair.Paired.experimentL hU omega published program finish) := by
  unfold WPair.Paired.experimentL
  exact superProg_bind _ _ (interactionL_ΦI S hproducer hU omega slot q published program) fun _ =>
    superProg_bind _ _ (CaseC.programL_super hU _ _ omega
      (NearWorld.coin_ΦI S slot q) (NearWorld.hashL_ΦI S hU slot q omega) _) fun _ =>
        superProg_pure _ _ _

theorem forced_experiment_near_le (S : FtsBankSpec P)
    (hproducer : S.producer=SigGolfCandidate.Research.SharedForest.digestAccepted) {U : Finset HashInput} (hU : ClaudeWCT.W9.T3.Security.CanonGraph.canonInputs⊆U)
    (omega : ClaudeWCT.W9.CanonTable.Omega U) (slot q : Nat)
    (hmono : ∀ X Y N,(∀ v∈X,v∈Y)→S.covered X N→S.covered Y N)
    (rate : ENNReal) (hrate : ClaudeWCT.Numerics.Law.lawAvg S.law (2^32) S.price≤rate)
    {α β : Type} (published : SigGolfCandidate.T3.Cache)
    (program : OracleComp WPair.Paired.Interaction α)
    (finish : (α × QueryLog WPair.Paired.Requests)→M β) :
    expectedValue (SecretGuessObservation.forcedWithRun WPair.envL WPair.samplerL slot
      (WPair.Paired.experimentL hU omega published program finish) WPair.initL)
      (fun r=>NearWorld.nearPayoff S q r.2)≤(q:ENNReal)*(rate+S.admBound)/2^128 :=
  NearWorld.forced_payoff_le S hmono rate hrate slot q _
    (experimentL_ΦI S hproducer hU omega slot q published program finish)
end World
end ClaudeWCT.Bank.NearWorld.Paired

namespace ClaudeWCT.Bank.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3.Security
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem nearCovered_mono (X Y : List HashOutput) (N : HashOutput)
    (hsub : ∀ v∈X,v∈Y) (h : NearCovered X N) : NearCovered Y N := by
  obtain ⟨hole,h⟩:=h
  refine ⟨hole,(nearCoveredAtP_source Y N hole).mpr ?_⟩
  intro k t hne
  obtain ⟨output,ho,hrest⟩:=(nearCoveredAtP_source X N hole).mp h k t hne
  exact ⟨output,hsub output ho,hrest⟩

theorem nearLawSpec_producer : nearLawSpec.producer=SigGolfCandidate.Research.SharedForest.digestAccepted := by
  change producer = _
  exact funext producer_source

theorem nearLawSpec_mean : ClaudeWCT.Numerics.Law.lawAvg nearLawSpec.law (2^32) nearLawSpec.price≤378 :=
  law_nearPrice_mean_bound

theorem forced_near_payoff_le {β : Type} (slot q : Nat)
    (W : OracleComp WPair.WSpecL β)
    (hW : CaseC.SuperProg (NearWorld.implG nearLawSpec slot) (NearWorld.ΦI nearLawSpec q) W) :
    expectedValue (SecretGuessObservation.forcedWithRun WPair.envL WPair.samplerL slot W WPair.initL)
      (fun r => NearWorld.nearPayoff nearLawSpec q r.2)≤
      (q:ENNReal)*(378+1/1024)/2^128 :=
  NearWorld.forced_payoff_le nearLawSpec nearCovered_mono 378 nearLawSpec_mean slot q W hW

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.W9.T3.Security.WPair.Paired
open OracleComp OracleSpec
open SigGolfCandidate.T3
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

theorem slotCovered_bank (X : List HashOutput) (N : HashOutput) (k : Fin 9) (t : Fin 6) :
    SlotCovered X N k t ↔ ClaudeWCT.Bank.Paired.SlotCoveredP (X.map ClaudeWCT.Bank.Paired.proposal) N k t :=
  (ClaudeWCT.Bank.Paired.slotCoveredP_source X N k t).symm

theorem covered_bank (X : List HashOutput) (N : HashOutput) :
    (∀ k t,SlotCovered X N k t)↔ClaudeWCT.Bank.Paired.Covered X N := by
  unfold ClaudeWCT.Bank.Paired.Covered ClaudeWCT.Bank.Paired.CoveredP
  exact forall_congr' fun k=>forall_congr' fun t=>slotCovered_bank X N k t

theorem nearCovered_bank (X : List HashOutput) (N : HashOutput) (k : Fin 9) (t : Fin 6)
    (h : ∀ k' t',(k',t')≠(k,t)→SlotCovered X N k' t') : ClaudeWCT.Bank.Paired.NearCovered X N := by
  refine ⟨(k,t),fun k' t' hne=>(slotCovered_bank X N k' t').mp (h k' t' hne)⟩

end ClaudeWCT.W9.T3.Security.WPair.Paired

namespace ClaudeWCT.Bank.NearWorld
open OracleComp OracleSpec OracleComp.EvalDist ENNReal Finset
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.BPair (LazyMem)
open SphincsSecurity.Concrete
open ClaudeWCT.W9.T3.Security
open ClaudeWCT.W9.T3.Security.CaseC (SuperProg)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpec P)

def NearEvent {β : Type} (q : Nat) (r : β×WPair.WStateL) : Prop :=
  r.2.guesses.Nonempty ∧ r.2.probes+r.2.memory.births.length≤q ∧ ¬Guess.Fam.Bad r.2 ∧
    r.2.memory.exposures.length≤2^32 ∧
    ∃ N∈r.2.memory.births,S.admissible N=true ∧ S.covered r.2.memory.exposures N

theorem event_payoff {β : Type} (q : Nat) (r : β×WPair.WStateL) (h : NearEvent S q r)
    (slot : Nat) (hs : slot<r.2.probes) : 1≤nearPayoff S (q-(slot+1)) r.2 := by
  unfold nearPayoff
  rw [if_pos ⟨by have hb:=h.2.1;omega,h.2.2.2⟩]

theorem triangular_sum_twice (q : Nat) :
    ((Finset.range q).sum (fun i => q - (i + 1)))*2=q*(q-1) := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Finset.sum_range_succ']
      simp only [Nat.succ_sub_succ_eq_sub,Nat.sub_zero]
      change (((Finset.range q).sum (fun i => q - (i + 1))) + q) * 2 = (q+1)*q
      by_cases hq:q=0
      · subst hq;simp
      · have :q-1+1=q:=by omega
        nlinarith

theorem triangular_sum_ennreal (q : Nat) (c : ENNReal) :
    (∑ slot∈Finset.range q,((q-(slot+1):Nat):ENNReal)*c/2^128)=
      ((q*(q-1):Nat):ENNReal)*c/(2*2^128) := by
  have h : (((Finset.range q).sum (fun i => q - (i + 1)) : Nat):ENNReal)*2=
      ((q*(q-1):Nat):ENNReal) := by exact_mod_cast triangular_sum_twice q
  rw [←h]
  simp only [Nat.cast_sum,div_eq_mul_inv,←Finset.sum_mul]
  rw [ENNReal.mul_inv (by simp) (by simp)]
  rw [show (∑ x∈Finset.range q,((q-(x+1):Nat):ENNReal))*2*c*((2:ENNReal)⁻¹*(2^128:ENNReal)⁻¹)=
      (∑ x∈Finset.range q,((q-(x+1):Nat):ENNReal))*c*(2*(2:ENNReal)⁻¹)*(2^128:ENNReal)⁻¹ by ring]
  rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num),mul_one]

theorem near_event_lazy_bound {β : Type}
    (hmono : ∀ X Y N,(∀ v∈X,v∈Y)→S.covered X N→S.covered Y N)
    (rate : ENNReal) (hrate : ClaudeWCT.Numerics.Law.lawAvg S.law (2^32) S.price≤rate)
    (q : Nat) (W : OracleComp WPair.WSpecL β)
    (hW : ∀ slot budget,SuperProg (implG S slot) (ΦI S budget) W) :
    Pr[NearEvent S q | SecretGuessObservation.withRun WPair.envL WPair.samplerL W WPair.initL]≤
      ((2^128-q:Nat):ENNReal)⁻¹*((q*(q-1):Nat):ENNReal)*(rate+S.admBound)/(2*2^128) := by
  have hb:=Guess.Fam.fam_event_le_forced_slot WPair.envL W LazyMem.empty q (NearEvent S q)
    (fun slot r=>nearPayoff S (q-(slot+1)) r.2) (fun r _ h=>
      ⟨h.1,by have hc:=h.2.1;omega,h.2.2.1,event_payoff S q r h⟩)
  have hslot (slot : Nat) :
      (∑' r,Pr[=r|SecretGuessObservation.forcedWithRun WPair.envL WPair.samplerL slot W WPair.initL]*
        nearPayoff S (q-(slot+1)) r.2)≤((q-(slot+1):Nat):ENNReal)*(rate+S.admBound)/2^128 := by
    exact forced_payoff_le S hmono rate hrate slot (q-(slot+1)) W (hW slot _)
  calc
    _≤_:=hb
    _≤((2^128-q:Nat):ENNReal)⁻¹*
        ∑ slot∈Finset.range q,((q-(slot+1):Nat):ENNReal)*(rate+S.admBound)/2^128 :=
      mul_le_mul' le_rfl (Finset.sum_le_sum fun slot _=>hslot slot)
    _=_:=by rw [triangular_sum_ennreal];simp only [div_eq_mul_inv];ring

end ClaudeWCT.Bank.NearWorld

namespace ClaudeWCT.Bank.NearWorld.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Concrete
open ClaudeWCT.W9.T3.Security
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
variable {P : Type} [Fintype P] [SampleableType P]

theorem experiment_near_bound (S : FtsBankSpec P)
    (hproducer : S.producer=SigGolfCandidate.Research.SharedForest.digestAccepted)
    (hmono : ∀ X Y N,(∀ v∈X,v∈Y)→S.covered X N→S.covered Y N)
    (rate : ENNReal) (hrate : ClaudeWCT.Numerics.Law.lawAvg S.law (2^32) S.price≤rate)
    {U : Finset HashInput} (hU : ClaudeWCT.W9.T3.Security.CanonGraph.canonInputs⊆U)
    (omega : ClaudeWCT.W9.CanonTable.Omega U) (q : Nat)
    {α β : Type} (published : SigGolfCandidate.T3.Cache)
    (program : OracleComp WPair.Paired.Interaction α)
    (finish : (α × QueryLog WPair.Paired.Requests)→M β) :
    Pr[NearWorld.NearEvent S q | SecretGuessObservation.withRun WPair.envL WPair.samplerL
      (WPair.Paired.experimentL hU omega published program finish) WPair.initL]≤
      ((2^128-q:Nat):ENNReal)⁻¹*((q*(q-1):Nat):ENNReal)*(rate+S.admBound)/(2*2^128) :=
  NearWorld.near_event_lazy_bound S hmono rate hrate q _
    (fun slot budget=>experimentL_ΦI S hproducer hU omega slot budget published program finish)

end ClaudeWCT.Bank.NearWorld.Paired

namespace ClaudeWCT.W9.T3.Security.WPair.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Concrete
open SecretGuessObservation (fixedRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (omega : CanonTable.Omega U)

theorem experimentL_near_facts (admissible : HashOutput → Bool)
    (covered : List HashOutput → HashOutput → Prop)
    (hmono : ∀ X Y N, (∀ v ∈ X, v ∈ Y) → covered X N → covered Y N)
    (q : Nat) (g : CanonTable.HiddenF) {α β : Type}
    (published : SigGolfCandidate.T3.Cache) (program : OracleComp Interaction α)
    (finish : (α × QueryLog Requests) → M β) (hfinish : ∀ result, PublicVerdict.Only (finish result))
    (r : (β × QueryLog Requests × List Wots.Entry) × WStateL)
    (hr : fixedRun (envE (digestOf omega) (nonceOf omega)) (Guess.Fam.phi g.1 g.2)
      (experimentL hU omega published program finish) initL r ≠ 0)
    (hq : r.1.2.2.length ≤ q) (hlog : r.1.2.1.length ≤ 2^32)
    (hno : ¬OverflowIn (wA hU omega g) r.1.2.1)
    (cell : Guess.GCoord) (hguess : GuessedIn (wA hU omega g) r.1.2.1 r.1.2.2 cell)
    (input : HashInput) (output : HashOutput) (hentry : (input,output) ∈ r.1.2.2)
    (hdigest : input ∈ BPair.digestInputs)
    (hfresh : ∀ entry ∈ r.1.2.1, (.inl (.inr input) : SigGolfCandidate.T3.Spec.Domain) ∉
      SigGolfCandidate.T3M.SecurityExtraction.queried (wA hU omega g) (authenticatedSign published entry.1))
    (hadm : admissible output = true)
    (hcovered : covered (loggedOutputs (wA hU omega g) r.1.2.1) output) :
    r.2.guesses.Nonempty ∧ r.2.probes + r.2.memory.births.length ≤ q ∧ ¬Guess.Fam.Bad r.2 ∧
      r.2.memory.exposures.length ≤ 2^32 ∧
      ∃ output ∈ r.2.memory.births, admissible output = true ∧ covered r.2.memory.exposures output := by
  have hcounts := experimentL_counts hU omega g published program finish r hr
  have hghost := experimentL_ghosts hU omega g published program finish r hr
  have hbirth : output ∈ r.2.memory.births := by
    rcases experimentL_rows_birth_or_trials hU omega g published program finish r hr input output hentry hdigest with hb | ht
    · exact hb
    · obtain ⟨entry, he, hquery⟩ := hcounts.2.1 input ht
      exact False.elim (hfresh entry he hquery)
  refine ⟨experimentL_guesses_nonempty hU omega g published program finish hfinish r hr cell hguess,
    (experimentL_probes_births hU omega g published program finish r hr).trans hq,
    experimentL_noBad hU omega g published program finish hfinish r hr hno,
    hcounts.2.2.trans hlog, output, hbirth, hadm, hmono _ _ output ?_ hcovered⟩
  intro value hv
  obtain ⟨entry, he, signature, hs, hout⟩ := mem_loggedOutputs.mp hv
  exact hghost.1 entry he signature value hs hout

end ClaudeWCT.W9.T3.Security.WPair.Paired

namespace ClaudeWCT.W9.T3.Security.WPair.Paired
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3M.SecurityExtraction (queried queried_bind)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _

theorem sharedDigestSearch_queried (answers : Correctness.Answers) (rho : Digest) (m : Message) :
    ∀ fuel start (q : SigGolfCandidate.T3.Spec.Domain),
      q ∈ queried answers (sharedDigestSearch rho m start fuel) →
      ∃ c, q = .inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 c)))) := by
  intro fuel
  induction fuel with
  | zero => intro start q hq; simp [sharedDigestSearch] at hq
  | succ fuel ih =>
      intro start q hq
      rw [sharedDigestSearch, queried_bind, SigGolfCandidate.T3.Security.BPB.queried_digest] at hq
      rcases List.mem_append.mp hq with hq | hq
      · exact ⟨start, List.mem_singleton.mp hq⟩
      · split at hq
        · simp at hq
        · exact ih (start+1) q hq

theorem signer_digest_query (answers : Correctness.Answers) (published : SigGolfCandidate.T3.Cache)
    (request : Request) (rho : Digest) (m : Message) (ctr : BitVec 32)
    (hq : (.inl (.inr (pad64 (digestInput rho m ctr))) : SigGolfCandidate.T3.Spec.Domain) ∈
      queried answers (authenticatedSign published request)) :
    request.cache = published ∧ request.message = m ∧
      rho = evalWithAnswerFn answers (privateNonce request.message) ∧
      (.inl (.inr (pad64 (digestInput rho m ctr))) : SigGolfCandidate.T3.Spec.Domain) ∈
        queried answers (sharedDigestSearch rho m 0 ClaudeWCT.WCT9.digestAttemptLimit) := by
  unfold authenticatedSign at hq
  rw [queried_bind, SigGolfCandidate.T3.Security.BPB.queried_privateMac] at hq
  rcases List.mem_append.mp hq with hq | hq
  · simp at hq
  by_cases hc : request.cache = published
  swap
  · rw [if_neg hc] at hq; simp at hq
  rw [if_pos hc, ClaudeWCT.Bank.Paired.signPayload_factor, queried_bind,
    SigGolfCandidate.T3.Security.BPB.queried_privateNonce] at hq
  rcases List.mem_append.mp hq with hq | hq
  · simp at hq
  rw [queried_bind] at hq
  rcases List.mem_append.mp hq with hq | hq
  · obtain ⟨c, heq⟩ := sharedDigestSearch_queried answers _ _ ClaudeWCT.WCT9.digestAttemptLimit 0 _ hq
    simp only [Sum.inl.injEq, Sum.inr.injEq] at heq
    obtain ⟨hrho, hctr, hm⟩ := SigGolfCandidate.T3.Security.BPB.digestInput_injective heq
    subst hrho hm
    exact ⟨hc, rfl, rfl, hq⟩
  · exfalso
    generalize evalWithAnswerFn answers (sharedDigestSearch
      (evalWithAnswerFn answers (privateNonce request.message)) request.message
      0 ClaudeWCT.WCT9.digestAttemptLimit) = found at hq
    rcases found with _ | ⟨_, output⟩
    · simp at hq
    · have hnot := SigGolfCandidate.T3.Security.BPB.allQ_queried answers _ _
        (ClaudeWCT.Bank.Paired.payNotDigest request.cache
          (evalWithAnswerFn answers (privateNonce request.message)) output) _ hq
      exact hnot (SigGolfCandidate.T3.Security.BPB.hdrMarker_digestInput rho m ctr)

end ClaudeWCT.W9.T3.Security.WPair.Paired

namespace ClaudeWCT.W9.T3.Security.WPair.Paired
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3M.SecurityExtraction (queried)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _

def SignedDigest (log : QueryLog Paired.Requests) (message : Message) (rho : Digest) : Prop :=
  ∃ entry ∈ log, entry.1.message = message ∧ ∃ signature, entry.2 = some signature ∧ signature.rho = rho

theorem fresh_digest_not_signer_eval (answers : Correctness.Answers) (published : SigGolfCandidate.T3.Cache)
    (log : QueryLog Paired.Requests)
    (hsig : ∀ entry ∈ log, entry.2 = evalWithAnswerFn answers (authenticatedSign published entry.1))
    (message : Message) (rho : Digest) (counter : BitVec 32)
    (hcomp : ∀ m, ∃ signature,
      evalWithAnswerFn answers (SigGolfCandidate.Research.SharedForest.signPayload published m) = some signature)
    (hfresh : ¬SignedDigest log message rho) :
    ∀ entry ∈ log, (.inl (.inr (pad64 (digestInput rho message counter))) : SigGolfCandidate.T3.Spec.Domain) ∉
      queried answers (authenticatedSign published entry.1) := by
  intro entry he hq
  obtain ⟨hc, hm, hrho, -⟩ := signer_digest_query answers published entry.1 _ _ _ hq
  obtain ⟨signature, hsignature⟩ := hcomp message
  have hsrho := payload_rho answers published message signature hsignature
  rw [hm] at hrho
  apply hfresh
  refine ⟨entry, he, hm, signature, ?_, hsrho.trans hrho.symm⟩
  rw [hsig entry he, eval_authenticatedSign, if_pos hc, hc, hm]
  exact hsignature

end ClaudeWCT.W9.T3.Security.WPair.Paired

namespace ClaudeWCT.W9.T3.Security.WPair.Counted
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable
theorem probeInput_other_new (T : Answers) (a : Guess.ChainAddr) (step : Fin 4) (value : Digest) :
    Wots.PairedReference.OtherInput T (Guess.probeInput a step value) := by
  let pos : Extract.Pos := .wctChain a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val step.val
  have hb : pos.Bounded := ⟨a.1.isLt, a.2.1.isLt, a.2.2.1.isLt, a.2.2.2.isLt, step.isLt⟩
  -- #866: `posOf_eq` also takes the input length (a chain row is 64 bytes, `Pos.len` of a chain position).
  refine ⟨pos, Extract.posOf_eq hb (Guess.probeInput_length a step value) ?_, hb, ?_, trivial⟩
  · exact Guess.hdrBlock_probeInput a step value
  · exact ⟨a.1.isLt, a.2.1.isLt, a.2.2.1.isLt, a.2.2.2.isLt, step.isLt⟩
theorem decodeProbe_other_new (T : Answers) {x : HashInput} {probe : Guess.GCoord × Digest}
    (h : Guess.decodeProbe x = some probe) : Wots.PairedReference.OtherInput T x := by
  rw [Guess.eq_of_decodeProbe h]
  exact probeInput_other_new T _ _ _

theorem probeCount_le_other_new (T : Answers) (pk : Digest) (trace : List Wots.Entry) :
    probeCount (trace.map Prod.fst) ≤ Wots.PairedReference.otherCount ⟨T, pk, trace⟩ := by
  induction trace with
  | nil => rfl
  | cons entry trace ih =>
      obtain ⟨x, a⟩ := entry
      cases hd : Guess.decodeProbe x with
      | none =>
          by_cases ho : Wots.PairedReference.OtherQuery T (.inl (.inr x))
          · have h : probeCount (trace.map Prod.fst) ≤ 1 + Wots.PairedReference.otherCount ⟨T, pk, trace⟩ := by omega
            simpa [probeCount, Wots.PairedReference.otherCount, hd, ho, Nat.add_comm] using h
          · simpa [probeCount, Wots.PairedReference.otherCount, hd, ho] using ih
      | some probe =>
          have ho : Wots.PairedReference.OtherQuery T (.inl (.inr x)) := decodeProbe_other_new T hd
          simpa [probeCount, Wots.PairedReference.otherCount, hd, ho] using Nat.add_le_add_left ih 1

end ClaudeWCT.W9.T3.Security.WPair.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Paired.Counted
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.SecretGuessObservation
open ClaudeWCT.W9.T3.Security.WPair.Counted
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local instance] ClaudeWCT.W9.T3.Security.WPair.Counted.chargedDecidable
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)
variable {α β : Type} (published : SigGolfCandidate.T3.Cache) (program : OracleComp Paired.Interaction α)
  (finish : (α × QueryLog Paired.Requests) → M β) (budget : Nat)

 theorem public_payment_le_reference_new :
    (∑' result, Pr[= result | withRun (Result := RunResult (β := β)) countEnvironment (Guess.Fam.sampler PUnit)
      (cappedProgram (experimentC hU ω published program finish) budget) countInit] *
      (probeCount (publicInputs result.1.2) : ENNReal)) ≤
    ∑' hidden, Pr[= hidden | ($ᵗ CanonTable.HiddenF : ProbComp _)] *
      ∑' run, Pr[= run | referenceRun (wA hU ω hidden) published program finish budget] *
        (Wots.PairedReference.otherCount ⟨wA hU ω hidden, (evalWithAnswerFn (wA hU ω hidden) keygen).1,
          Wots.traceOf (wA hU ω hidden) run.2⟩ : ENNReal) := by
  rw [← tsum_probOutput_map_mul _ (fun result : RunResult (β := β) × CountState => publicInputs result.1.2)
    (fun inputs => (probeCount inputs : ENNReal)), public_distribution hU ω published program finish budget]
  simp only [bind_pure_comp, evalSPMF_bind, evalSPMF_map]
  rw [tsum_probOutput_bind_mul]
  apply ENNReal.tsum_le_tsum
  intro hidden
  simp only [probOutput_evalSPMF]
  apply mul_le_mul' le_rfl
  rw [tsum_probOutput_map_mul]
  simp only [probOutput_evalSPMF]
  apply ENNReal.tsum_le_tsum
  intro run
  apply mul_le_mul' le_rfl
  rw [refPublicInputs_eq_trace (wA hU ω hidden)]
  exact_mod_cast probeCount_le_other_new (wA hU ω hidden) _ (Wots.traceOf (wA hU ω hidden) run.2)

 theorem event_le_other_new
    (hfinish : ∀ value, PublicVerdict.Only (finish value)) (hbudget : budget < 2^128)
    (event : CanonTable.HiddenF → RunResult (β := β) → Prop)
    (hevent : ∀ hidden result, event hidden result → ∃ output remaining,
      result.1 = some (output, remaining) ∧ ¬Paired.OverflowIn (wA hU ω hidden) output.2.1 ∧
      ∃ cell, Paired.GuessedIn (wA hU ω hidden) output.2.1 output.2.2 cell) :
    Pr[fun result => event result.1 result.2 | WPair.Counted.Generic.countedProgramRun
      (cappedProgram (experimentC hU ω published program finish) budget)] ≤
      (((2^128-budget : Nat) : ENNReal))⁻¹ *
      (∑' hidden, Pr[= hidden | ($ᵗ CanonTable.HiddenF : ProbComp _)] *
      ∑' run, Pr[= run | referenceRun (wA hU ω hidden) published program finish budget] *
        (Wots.PairedReference.otherCount ⟨wA hU ω hidden, (evalWithAnswerFn (wA hU ω hidden) keygen).1,
          Wots.traceOf (wA hU ω hidden) run.2⟩ : ENNReal)) :=
  (event_le_external hU ω published program finish hfinish budget hbudget event hevent).trans
    (mul_le_mul' le_rfl (public_payment_le_reference_new hU ω published program finish budget))

end ClaudeWCT.W9.T3.Security.WPair.Paired.Counted


namespace ClaudeWCT.W9.T3.Security.WPair.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M.Final.Paired (AdversaryP)
open SphincsSecurity.Concrete
open SecretGuessObservation (fixedRun withRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

noncomputable def worldGameL {U : Finset HashInput} (hU : CanonGraph.canonInputs⊆U)
    (omega : CanonTable.Omega U) (adversary : AdversaryP) :=
  let generated := evalWithAnswerFn (wA hU omega 0) SigGolfCandidate.T3.keygen
  experimentL hU omega generated.2 (adversary generated.1 generated.2)
    (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker generated.1)

variable {U : Finset HashInput} (hU : CanonGraph.canonInputs⊆U) (omega : CanonTable.Omega U)

theorem worldGameL_sameRest {omega1 omega2 : CanonTable.Omega U}
    (h : SameRest omega1 omega2) (adversary : AdversaryP) :
    worldGameL hU omega1 adversary=worldGameL hU omega2 adversary := by
  unfold worldGameL
  rw [eval_sameRest hU h _ BPair.keygen_dn]
  exact experimentL_sameRest hU h _ _ _

theorem fixed_experimentL {α β : Type} (published : SigGolfCandidate.T3.Cache)
    (program : OracleComp Interaction α) (finish : (α × QueryLog Requests)→M β)
    (hfinish : ∀ value,PublicVerdict.Only (finish value)) (g : CanonTable.HiddenF) :
    Prod.fst <$> fixedRun (envE (digestOf omega) (nonceOf omega)) (Guess.Fam.phi g.1 g.2)
      (experimentL hU omega published program finish) initL =
      𝒮[experimentT (wA hU omega g) published program finish] := by
  have h := congrArg (Functor.map Prod.fst)
    (fixed_inline (digestOf omega) (nonceOf omega) (Guess.Fam.phi g.1 g.2)
      (experimentL hU omega published program finish) initL (BPair.consistent_empty _ _))
  rw [Functor.map_map,forget_initL] at h
  change (Prod.fst <$> fixedRun (envE (digestOf omega) (nonceOf omega)) (Guess.Fam.phi g.1 g.2)
      (experimentL hU omega published program finish) initL) =
    Prod.fst <$> fixedRun env (Guess.Fam.phi g.1 g.2)
      (simulateQ (inlineAux omega) (experimentL hU omega published program finish)) init at h
  rw [inline_experimentL hU omega] at h
  exact h.trans (fixed_experimentW hU omega published program finish hfinish g)

theorem fixed_worldGameL (g : CanonTable.HiddenF) (adversary : AdversaryP) :
    Prod.fst <$> fixedRun (envE (digestOf omega) (nonceOf omega)) (Guess.Fam.phi g.1 g.2)
      (worldGameL hU omega adversary) initL = 𝒮[pairRun (wA hU omega g) adversary] := by
  rw [pairRun_world]
  exact fixed_experimentL hU omega _ _ _ (PairedOuter.PaddedGame.verdict_public _) g

theorem worldGameL_tracking (g : CanonTable.HiddenF) (adversary : AdversaryP)
    (r : (Bool × QueryLog Requests × List Wots.Entry) × WStateL)
    (hr : fixedRun (envE (digestOf omega) (nonceOf omega)) (Guess.Fam.phi g.1 g.2)
      (worldGameL hU omega adversary) initL r ≠ 0) :
    r.2.probes ≤ r.1.2.2.length ∧
      ∀ c, GuessedIn (wA hU omega g) r.1.2.1 r.1.2.2 c → Guess.PrefixIn r.2.guesses c.1 c.2.val := by
  have ht := experimentL_tracking hU omega g _ _ _ (PairedOuter.PaddedGame.verdict_public _) r hr
  refine ⟨?_,fun c hc => ?_⟩
  · have hp:=ht.probes
    simp only [init,SecretGuessObservation.initialState] at hp
    simpa only [forget,Nat.zero_add] using hp
  · exact ht.guess (by simp [init,SecretGuessObservation.initialState]) c hc.1 hc.2

theorem worldGameL_noBad (g : CanonTable.HiddenF) (adversary : AdversaryP)
    (r : (Bool × QueryLog Requests × List Wots.Entry) × WStateL)
    (hr : fixedRun (envE (digestOf omega) (nonceOf omega)) (Guess.Fam.phi g.1 g.2)
      (worldGameL hU omega adversary) initL r ≠ 0)
    (hno : ¬OverflowIn (wA hU omega g) r.1.2.1) : ¬Guess.Fam.Bad r.2 :=
  experimentL_noBad hU omega g _ _ _ (PairedOuter.PaddedGame.verdict_public _) r hr hno

attribute [local irreducible] worldGameL experimentT experimentW experimentL SecretGuessObservation.fixedRun

theorem fts_event_le_worldL (adversary : AdversaryP)
    (event : CanonTable.HiddenF → (Bool × QueryLog Requests × List Wots.Entry) → Prop)
    (wevent : (Bool × QueryLog Requests × List Wots.Entry) × WStateL → Prop)
    (himp : ∀ g result, fixedRun (envE (digestOf omega) (nonceOf omega)) (Guess.Fam.phi g.1 g.2)
      (worldGameL hU omega adversary) initL result ≠ 0 → event g result.1 → wevent result) :
    Pr[fun x => event x.1 x.2 | ftsRun hU omega adversary] ≤
      Pr[wevent | withRun (envE (digestOf omega) (nonceOf omega)) samplerL
        (worldGameL hU omega adversary) initL] := by
  rw [← Guess.Fam.fam_erasure (envE (digestOf omega) (nonceOf omega)) (worldGameL hU omega adversary) initL
    (Guess.Fam.inv_initial BPair.LazyMem.empty)]
  change _ ≤ Pr[wevent | Guess.Fam.hiddenLaw (fun _ => Finset.univ) >>= fun g =>
    fixedRun (envE (digestOf omega) (nonceOf omega)) g (worldGameL hU omega adversary) initL]
  rw [WPair.hiddenLaw_univ_bind]
  unfold ftsRun tableRun
  simp only [probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro g
  simp only [probOutput_evalSPMF,probOutput_uniformSample]
  apply mul_le_mul' le_rfl
  rw [probEvent_map,← pairRun_world hU omega g adversary,←fixed_worldGameL hU omega g adversary,probEvent_map]
  apply probEvent_mono
  intro result hr he
  exact himp g result (by simpa only [mem_support_iff,SPMF.probOutput_eq_apply] using hr) he

end ClaudeWCT.W9.T3.Security.WPair.Paired

namespace ClaudeWCT.W9.T3.Security.WPair.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M.Final.Paired (AdversaryP)
open SphincsSecurity.Concrete
open SecretGuessObservation (fixedRun withRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

open ClaudeWCT.W9.T3.Security.CanonGraph
attribute [local instance] instSampleableTypeSecrets instSampleableTypeOtherHalves instSampleableTypeLowLabels instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_canonGraph_1 CanonTable.instSampleableTypeHidden
noncomputable def ftsPart (adversary : AdversaryP) (ω : CanonTable.Omega (Wots.PairedReference.referenceInputs adversary)) :
    ProbComp (Answers × QueryLog Requests × List Wots.Entry) :=
  ($ᵗ CanonTable.HiddenF : ProbComp _) >>= fun g =>
    (fun (run : Bool × QueryLog Requests × List Wots.Entry) => (wA (canon_subset adversary) ω g, run.2.1, run.2.2)) <$>
      pairRun (wA (canon_subset adversary) ω g) adversary
theorem pairExperiment_omega (adversary : AdversaryP) :
    𝒮[pairExperiment adversary] = 𝒮[omegaLaw (Wots.PairedReference.referenceInputs adversary) >>= ftsPart adversary] := by
  rw [pairExperiment_eq]
  unfold omegaLaw ftsPart
  simp only [bind_assoc, pure_bind]
theorem pairExperiment_avg (adversary : AdversaryP) (E : Answers × QueryLog Requests × List Wots.Entry → Prop) :
    Pr[E | pairExperiment adversary] = ∑' ω, Pr[= ω | omegaLaw (Wots.PairedReference.referenceInputs adversary)] *
      Pr[fun x => E (wA (canon_subset adversary) ω x.1, x.2.2.1, x.2.2.2) |
        ftsRun (canon_subset adversary) ω adversary] := by
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (pairExperiment_omega adversary), probEvent_bind_eq_tsum]
  apply tsum_congr
  intro ω
  rw [← inner_fts_eq (canon_subset adversary) ω adversary _ E]
  rfl

end ClaudeWCT.W9.T3.Security.WPair.Paired

namespace ClaudeWCT.W9.T3.Security.WPair.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M.Final.Paired (AdversaryP)
open SphincsSecurity.Concrete
open SecretGuessObservation (fixedRun withRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

open SigGolfCandidate.T3.Security.BPair (LazyMem)
open ClaudeWCT.W9.T3.Security.CanonGraph
theorem digest_subset (adversary : AdversaryP) : BPair.digestInputs ⊆ Wots.PairedReference.referenceInputs adversary :=
  BPair.digestInputs_subset_publicUniverse.trans (Wots.PairedReference.Ref.referenceInputs_universe adversary)
theorem near_chain_slot_budget (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (P : Answers → QueryLog Requests → List Wots.Entry → Prop)
    (hshort : ∀ A T log entries, Wots.Ref.ShortAgree A T → P A log entries → P T log entries)
    (hmono : ∀ A log entries entries', (∀ e ∈ entries, e ∈ entries') → P A log entries → P A log entries')
    (hno : ∀ A log entries, P A log entries → ¬OverflowIn A log)
    (payoff : Nat → (Bool × QueryLog Requests × List Wots.Entry) × WStateL → ENNReal)
    (hevent : ∀ ω g r, SecretGuessObservation.fixedRun (envE (digestOf ω) (nonceOf ω)) (Guess.Fam.phi g.1 g.2)
        (worldGameL (canon_subset adversary) ω adversary) initL r ≠ 0 →
      r.1.2.2.length ≤ q → P (wA (canon_subset adversary) ω g) r.1.2.1 r.1.2.2 →
      r.2.guesses.Nonempty ∧ ∀ slot < r.2.probes, 1 ≤ payoff slot r) :
    Pr[fun z => z.1.2.2.base.source.1 ≤ q ∧ ∀ generated interaction checked,
        Wots.PairedReference.GameSplit adversary (QueryRecorded.recordedTrace z.1) generated interaction checked →
          P z.2 interaction.value.2 (SigGolfCandidate.T3.Security.BPair.publicEntries checked.events) |
        PairedSeccLaw.completedExperiment adversary q hq] ≤
      ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * ∑ slot ∈ Finset.range q, ∑' ω, Pr[= ω | omegaLaw (Wots.PairedReference.referenceInputs adversary)] *
        ∑' r, Pr[= r | SecretGuessObservation.forcedWithRun envL samplerL slot
          (worldGameL (canon_subset adversary) ω adversary) initL] * payoff slot r := by
  refine (shared_budget_le_pair adversary q hq P hshort hmono).trans ?_
  rw [pairExperiment_avg]
  have hω : ∀ ω : CanonTable.Omega (Wots.PairedReference.referenceInputs adversary),
      Pr[fun x => x.2.2.2.length ≤ q ∧ P (wA (canon_subset adversary) ω x.1) x.2.2.1 x.2.2.2 |
        ftsRun (canon_subset adversary) ω adversary] ≤
      ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * ∑ slot ∈ Finset.range q, ∑' r,
        Pr[= r | SecretGuessObservation.forcedWithRun (envE (digestOf ω) (nonceOf ω)) samplerL slot
          (worldGameL (canon_subset adversary) ω adversary) initL] * payoff slot r := by
    intro ω
    refine (fts_event_le_worldL (canon_subset adversary) ω adversary
      (fun g run => run.2.2.length ≤ q ∧ P (wA (canon_subset adversary) ω g) run.2.1 run.2.2)
      (fun r => r.2.guesses.Nonempty ∧ r.2.probes ≤ q ∧ ¬Guess.Fam.Bad r.2 ∧ ∀ slot < r.2.probes, 1 ≤ payoff slot r)
      ?_).trans ?_
    · rintro g r hr ⟨hlen, hP⟩
      obtain ⟨hg, hp⟩ := hevent ω g r hr hlen hP
      exact ⟨hg, (worldGameL_tracking (canon_subset adversary) ω g adversary r hr).1.trans hlen,
        worldGameL_noBad (canon_subset adversary) ω g adversary r hr (hno _ _ _ hP), hp⟩
    · exact Guess.Fam.fam_event_le_forced_slot (envE (digestOf ω) (nonceOf ω))
        (worldGameL (canon_subset adversary) ω adversary) LazyMem.empty q _ payoff (fun _ _ h => h)
  calc (∑' ω, Pr[= ω | omegaLaw (Wots.PairedReference.referenceInputs adversary)] *
        Pr[fun x => x.2.2.2.length ≤ q ∧ P (wA (canon_subset adversary) ω x.1) x.2.2.1 x.2.2.2 |
          ftsRun (canon_subset adversary) ω adversary])
      ≤ ∑' ω, Pr[= ω | omegaLaw (Wots.PairedReference.referenceInputs adversary)] * (((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * ∑ slot ∈ Finset.range q, ∑' r,
          Pr[= r | SecretGuessObservation.forcedWithRun (envE (digestOf ω) (nonceOf ω)) samplerL slot
            (worldGameL (canon_subset adversary) ω adversary) initL] * payoff slot r) :=
        ENNReal.tsum_le_tsum fun ω => mul_le_mul' le_rfl (hω ω)
    _ = ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * ∑ slot ∈ Finset.range q, ∑' ω, Pr[= ω | omegaLaw (Wots.PairedReference.referenceInputs adversary)] *
          ∑' r, Pr[= r | SecretGuessObservation.forcedWithRun (envE (digestOf ω) (nonceOf ω)) samplerL slot
            (worldGameL (canon_subset adversary) ω adversary) initL] * payoff slot r := by
        simp only [Finset.mul_sum, mul_left_comm (Pr[= _ | omegaLaw (Wots.PairedReference.referenceInputs adversary)])]
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        exact Finset.sum_congr rfl fun slot _ => ENNReal.tsum_mul_left
    _ = _ := congrArg (fun t => ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * t)
        (Finset.sum_congr rfl fun slot _ => forced_avg_eq_lazy (Wots.PairedReference.referenceInputs adversary) (digest_subset adversary)
          (fun omega => worldGameL (canon_subset adversary) omega adversary)
          (fun _ _ h => worldGameL_sameRest (canon_subset adversary) h adversary) slot (payoff slot))

end ClaudeWCT.W9.T3.Security.WPair.Paired

namespace ClaudeWCT.W9.T3.Security.WPair.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M.Final.Paired (AdversaryP)
open SphincsSecurity.Concrete
open SecretGuessObservation (fixedRun withRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem interactionT_honest (T : Correctness.Answers) (published : SigGolfCandidate.T3.Cache) {α : Type}
    (oa : OracleComp Interaction α) (r : α × QueryLog Requests × List Wots.Entry)
    (hr : r ∈ support (interactionT T published oa)) :
    (∀ e ∈ r.2.1, e.2 = evalWithAnswerFn T (authenticatedSign published e.1)) ∧
      ∀ e ∈ r.2.2, e.2 = T (.inl (.inr e.1)) := by
  induction oa using OracleComp.inductionOn generalizing r with
  | pure value =>
      rw [interactionT_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr
      simp
  | query_bind input next ih =>
      rcases input with (n | x) | request
      · rw [interactionT_coin, mem_support_bind_iff] at hr
        obtain ⟨coin, -, hr⟩ := hr
        exact ih coin r hr
      · rw [interactionT_public, mem_support_bind_iff] at hr
        obtain ⟨rest, hrest, hr⟩ := hr
        rw [support_pure, Set.mem_singleton_iff] at hr
        subst hr
        obtain ⟨h1, h2⟩ := ih _ rest hrest
        refine ⟨h1, fun e he => ?_⟩
        rcases List.mem_cons.mp he with he | he
        · subst he; rfl
        · exact h2 e he
      · rw [interactionT_request, mem_support_bind_iff] at hr
        obtain ⟨rest, hrest, hr⟩ := hr
        rw [support_pure, Set.mem_singleton_iff] at hr
        subst hr
        obtain ⟨h1, h2⟩ := ih _ rest hrest
        refine ⟨fun e he => ?_, h2⟩
        rcases List.mem_cons.mp he with he | he
        · subst he; rfl
        · exact h1 e he
theorem entriesOf_honest (T : Correctness.Answers) (qs : List SigGolfCandidate.T3.Spec.Domain) :
    ∀ e ∈ Wots.entriesOf T qs, e.2 = T (.inl (.inr e.1)) := by
  intro e he
  unfold Wots.entriesOf at he
  rw [List.mem_filterMap] at he
  obtain ⟨q, -, hq⟩ := he
  rcases q with (c | input) | p
  · cases hq
  · cases hq; rfl
  · cases hq
theorem pairRun_honest (T : Correctness.Answers) (adversary : AdversaryP)
    (r : Bool × QueryLog Requests × List Wots.Entry) (hr : r ∈ support (pairRun T adversary)) :
    (∀ e ∈ r.2.1, e.2 = evalWithAnswerFn T (authenticatedSign
        (evalWithAnswerFn T SigGolfCandidate.T3.keygen).2 e.1)) ∧
      ∀ e ∈ r.2.2, e.2 = T (.inl (.inr e.1)) := by
  unfold pairRun at hr
  rw [mem_support_bind_iff] at hr
  obtain ⟨interaction, hi, hr⟩ := hr
  rw [support_pure, Set.mem_singleton_iff] at hr
  subst hr
  obtain ⟨h1, h2⟩ := interactionT_honest T _ _ interaction hi
  refine ⟨h1, fun e he => ?_⟩
  rcases List.mem_append.mp he with he | he
  · exact h2 e he
  · exact entriesOf_honest T _ e he

end ClaudeWCT.W9.T3.Security.WPair.Paired

namespace ClaudeWCT.W9.T3.Security.WPair.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction (queried)
open ClaudeWCT.W9.T3M.Final.Paired (AdversaryP)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- Every cache with a successful logged signature succeeds on all its logged requests. -/
def CacheCompleteLog (log : QueryLog Requests) : Prop :=
  ∀ prior∈log, (∃ signature,prior.2=some signature) →
    ∀ entry∈log,entry.1.cache=prior.1.cache → ∃ signature,entry.2=some signature

theorem logged_success_cache (A : Answers) (published : SigGolfCandidate.T3.Cache)
    (entry : (request : Requests.Domain) × Requests.Range request)
    (hsig : entry.2=evalWithAnswerFn A (authenticatedSign published entry.1))
    (hs : ∃ signature,entry.2=some signature) : entry.1.cache=published := by
  rw [eval_authenticatedSign] at hsig
  by_contra h
  rw [if_neg h] at hsig
  obtain ⟨signature,hs⟩:=hs
  rw [hsig] at hs
  cases hs

theorem cacheCompleteLog_of_complete (A : Answers) (published : SigGolfCandidate.T3.Cache)
    (log : QueryLog Requests)
    (hsig : ∀ entry∈log,entry.2=evalWithAnswerFn A (authenticatedSign published entry.1))
    (hcomp : ∀ message,∃ signature,evalWithAnswerFn A
      (SigGolfCandidate.Research.SharedForest.signPayload published message)=some signature) :
    CacheCompleteLog log := by
  intro prior hp hs entry he hc
  have hpc:=logged_success_cache A published prior (hsig prior hp) hs
  have hec:=hc.trans hpc
  obtain ⟨signature,hsignature⟩:=hcomp entry.1.message
  refine ⟨signature,?_⟩
  rw [hsig entry he,eval_authenticatedSign,if_pos hec,hec]
  exact hsignature

theorem fresh_digest_not_signer_eval_of_log (A : Answers) (published : SigGolfCandidate.T3.Cache)
    (log : QueryLog Requests)
    (hsig : ∀ entry∈log,entry.2=evalWithAnswerFn A (authenticatedSign published entry.1))
    (hclosed : CacheCompleteLog log)
    (hnonempty : ∃ prior∈log,∃ signature,prior.2=some signature)
    (message : Message) (rho : Digest) (counter : BitVec 32)
    (hfresh : ¬SignedDigest log message rho) :
    ∀ entry∈log,(.inl (.inr (pad64 (digestInput rho message counter))) : SigGolfCandidate.T3.Spec.Domain) ∉
      queried A (authenticatedSign published entry.1) := by
  intro entry he hq
  obtain ⟨hc,hm,hrho,_⟩:=signer_digest_query A published entry.1 _ _ _ hq
  obtain ⟨prior,hprior,priorSig,hpriorSig⟩:=hnonempty
  have hpc:=logged_success_cache A published prior (hsig prior hprior) ⟨priorSig,hpriorSig⟩
  obtain ⟨signature,hs⟩:=hclosed prior hprior ⟨priorSig,hpriorSig⟩ entry he (hc.trans hpc.symm)
  have hpayload : evalWithAnswerFn A
      (SigGolfCandidate.Research.SharedForest.signPayload entry.1.cache entry.1.message)=some signature := by
    rw [hsig entry he,eval_authenticatedSign,if_pos hc] at hs
    exact hs
  have hsrho:=payload_rho A entry.1.cache entry.1.message signature hpayload
  exact hfresh ⟨entry,he,hm,signature,hs,hsrho.trans hrho.symm⟩

def NearCovers (X : List HashOutput) (N : HashOutput) : Prop :=
  ∃ (k : Fin 9) (t : Fin 6),∀ k' t',(k',t')≠(k,t) → SlotCovered X N k' t'

theorem nearCovers_mono (X Y : List HashOutput) (N : HashOutput)
    (hsub : ∀ value∈X,value∈Y) (h : NearCovers X N) : NearCovers Y N := by
  obtain ⟨k,t,h⟩:=h
  refine ⟨k,t,fun k' t' hne=>?_⟩
  obtain ⟨output,ho,hrest⟩:=h k' t' hne
  exact ⟨output,hsub _ ho,hrest⟩

theorem nearCovers_success (A : Answers) (log : QueryLog Requests) (N : HashOutput)
    (h : NearCovers (loggedOutputs A log) N) : ∃ prior∈log,∃ signature,prior.2=some signature := by
  obtain ⟨k,t,h⟩:=h
  obtain ⟨t',hne⟩:=exists_ne t
  obtain ⟨output,ho,_⟩:=h k t' (fun he=>hne (congrArg Prod.snd he))
  obtain ⟨entry,he,signature,hs,_⟩:=mem_loggedOutputs.mp ho
  exact ⟨entry,he,signature,hs⟩

def NearIn (A : Answers) (log : QueryLog Requests) (entries : List Wots.Entry) : Prop :=
  log.length≤2^32 ∧ CacheCompleteLog log ∧
  ∃ (message : Message) (rho : Digest) (counter : BitVec 32) (N : HashOutput) (cell : Guess.GCoord),
    (pad64 (digestInput rho message counter),N)∈entries ∧
    ClaudeWCT.Bank.Paired.admissible N=true ∧ ¬SignedDigest log message rho ∧
    GuessedIn A log entries cell ∧ NearCovers (loggedOutputs A log) N

theorem nearIn_short {A T : Answers} (h : Wots.Ref.ShortAgree A T)
    (log : QueryLog Requests) (entries : List Wots.Entry) (hn : NearIn A log entries) :
    NearIn T log entries := by
  obtain ⟨hlen,hclosed,message,rho,counter,N,cell,he,ha,hfresh,hguess,hcover⟩:=hn
  refine ⟨hlen,hclosed,message,rho,counter,N,cell,he,ha,hfresh,guessedIn_short h log entries cell hguess,?_⟩
  rw [←loggedOutputs_short h]
  exact hcover

theorem nearIn_mono (A : Answers) (log : QueryLog Requests) (entries entries' : List Wots.Entry)
    (hsub : ∀ entry∈entries,entry∈entries') (h : NearIn A log entries) : NearIn A log entries' := by
  obtain ⟨hlen,hclosed,message,rho,counter,N,cell,he,ha,hfresh,hguess,hcover⟩:=h
  exact ⟨hlen,hclosed,message,rho,counter,N,cell,hsub _ he,ha,hfresh,
    guessedIn_mono A log entries entries' hsub cell hguess,hcover⟩

end ClaudeWCT.W9.T3.Security.WPair.Paired

namespace ClaudeWCT.W9.T3.Security.WPair.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction (queried)
open ClaudeWCT.W9.T3M.Final.Paired (AdversaryP)
open SphincsSecurity.Concrete
open SecretGuessObservation (fixedRun forcedWithRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {P : Type} [Fintype P] [SampleableType P]

theorem fixed_support_pairRun (adversary : AdversaryP)
    (omega : CanonTable.Omega (Wots.PairedReference.referenceInputs adversary))
    (g : CanonTable.HiddenF) (r : (Bool × QueryLog Requests × List Wots.Entry) × WStateL)
    (hr : fixedRun (envE (digestOf omega) (nonceOf omega)) (Guess.Fam.phi g.1 g.2)
      (worldGameL (canon_subset adversary) omega adversary) initL r≠0) :
    r.1∈support (pairRun (wA (canon_subset adversary) omega g) adversary) := by
  rw [mem_support_iff,probOutput_def,←fixed_worldGameL (canon_subset adversary) omega g adversary,
    map_eq_bind_pure_comp,RetainedObservation.bind_nonzero]
  refine ⟨r,hr,?_⟩
  simp only [Function.comp_apply,ne_eq,SPMF.pure_apply_eq_zero_iff,not_not]

theorem near_event_facts (S : ClaudeWCT.Bank.FtsBankSpec P)
    (hadmissible : S.admissible=ClaudeWCT.Bank.Paired.admissible)
    (hmono : ∀ X Y N,(∀ value∈X,value∈Y) → S.covered X N → S.covered Y N)
    (hcovered : ∀ X N,NearCovers X N → S.covered X N)
    (adversary : AdversaryP) (q : Nat)
    (omega : CanonTable.Omega (Wots.PairedReference.referenceInputs adversary))
    (g : CanonTable.HiddenF) (r : (Bool × QueryLog Requests × List Wots.Entry) × WStateL)
    (hr : fixedRun (envE (digestOf omega) (nonceOf omega)) (Guess.Fam.phi g.1 g.2)
      (worldGameL (canon_subset adversary) omega adversary) initL r≠0)
    (hq : r.1.2.2.length≤q)
    (hP : NearIn (wA (canon_subset adversary) omega g) r.1.2.1 r.1.2.2)
    (hno : ¬OverflowIn (wA (canon_subset adversary) omega g) r.1.2.1) :
    ClaudeWCT.Bank.NearWorld.NearEvent S q r := by
  obtain ⟨hlen,hclosed,message,rho,counter,N,cell,he,ha,hfresh,hguess,hcover⟩:=hP
  have hlog:=(pairRun_honest _ adversary r.1 (fixed_support_pairRun adversary omega g r hr)).1
  rw [keygen_answers] at hlog
  have hfreshQ:=fresh_digest_not_signer_eval_of_log _ _ _ hlog hclosed
    (nearCovers_success _ _ N hcover) message rho counter hfresh
  exact experimentL_near_facts (canon_subset adversary) omega S.admissible S.covered hmono q g
    _ _ _ (PairedOuter.PaddedGame.verdict_public _) r hr hq hlen hno cell hguess
    (pad64 (digestInput rho message counter)) N he (BPair.mem_digestInputs.mpr ⟨rho,message,counter,rfl⟩) hfreshQ
    (by rw [hadmissible];exact ha) (hcovered _ _ hcover)

theorem near_bound_budget (S : ClaudeWCT.Bank.FtsBankSpec P)
    (hproducer : S.producer=SigGolfCandidate.Research.SharedForest.digestAccepted)
    (hadmissible : S.admissible=ClaudeWCT.Bank.Paired.admissible)
    (hmono : ∀ X Y N,(∀ value∈X,value∈Y) → S.covered X N → S.covered Y N)
    (hcovered : ∀ X N,NearCovers X N → S.covered X N)
    (rate : ENNReal) (hrate : ClaudeWCT.Numerics.Law.lawAvg S.law (2^32) S.price≤rate)
    (adversary : AdversaryP) (q : Nat) (hq : q≤2^127) :
    Pr[fun z => z.1.2.2.base.source.1≤q ∧ ∀ generated interaction checked,
      Wots.PairedReference.GameSplit adversary (QueryRecorded.recordedTrace z.1) generated interaction checked →
        NearIn z.2 interaction.value.2 (BPair.publicEntries checked.events) ∧
          ¬OverflowIn z.2 interaction.value.2 | PairedSeccLaw.completedExperiment adversary q hq] ≤
      ((2^128-q:Nat):ENNReal)⁻¹*((q*(q-1):Nat):ENNReal)*(rate+S.admBound)/(2*2^128) := by
  have hchain:=near_chain_slot_budget adversary q hq
    (fun A log entries=>NearIn A log entries ∧ ¬OverflowIn A log)
    (fun A T log entries h hp=>⟨nearIn_short h log entries hp.1,
      fun ho=>hp.2 (overflowIn_short h.symm log ho)⟩)
    (fun A log entries entries' hsub hp=>⟨nearIn_mono A log entries entries' hsub hp.1,hp.2⟩)
    (fun _ _ _ hp=>hp.2)
    (fun slot r=>ClaudeWCT.Bank.NearWorld.nearPayoff S (q-(slot+1)) r.2)
    (fun omega g r hr hlen hp=>by
      have h:=near_event_facts S hadmissible hmono hcovered adversary q omega g r hr hlen hp.1 hp.2
      exact ⟨h.1,fun slot hs=>ClaudeWCT.Bank.NearWorld.event_payoff S q r h slot hs⟩)
  have hslot (slot : Nat) :
      (∑' omega,Pr[=omega|omegaLaw (Wots.PairedReference.referenceInputs adversary)] *
        ∑' r,Pr[=r|forcedWithRun envL samplerL slot
          (worldGameL (canon_subset adversary) omega adversary) initL] *
            ClaudeWCT.Bank.NearWorld.nearPayoff S (q-(slot+1)) r.2) ≤
      ((q-(slot+1):Nat):ENNReal)*(rate+S.admBound)/2^128 := by
    apply CaseC.omega_avg_le
    intro omega
    exact ClaudeWCT.Bank.NearWorld.Paired.forced_experiment_near_le S hproducer
      (canon_subset adversary) omega slot (q-(slot+1)) hmono rate hrate _ _ _
  calc
    _≤_:=hchain
    _≤((2^128-q:Nat):ENNReal)⁻¹ *
        ∑ slot∈Finset.range q,((q-(slot+1):Nat):ENNReal)*(rate+S.admBound)/2^128 :=
      mul_le_mul' le_rfl (Finset.sum_le_sum fun slot _=>hslot slot)
    _=_:=by rw [ClaudeWCT.Bank.NearWorld.triangular_sum_ennreal];simp only [div_eq_mul_inv];ring

end ClaudeWCT.W9.T3.Security.WPair.Paired

namespace ClaudeWCT.W9.T3.Security.WPair.Counted.Generic
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3.Security.Wots.Ref (probEvent_bind_mono)
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable
/-- Completed capped executions retain both the return value and their whole query list. -/
theorem cap_recorded_completed_le {ι β : Type} {spec : OracleSpec ι}
    (selected : ι → Prop) [DecidablePred selected] (impl : QueryImpl spec ProbComp)
    (computation : OracleComp spec β) (budget : Nat) (event : β → List ι → Prop) :
    Pr[fun result => event result.1 result.2 ∧ SphincsSecurity.QueryCap.calls selected result.2 ≤ budget |
      simulateQ impl (SphincsSecurity.QueryCap.recorded computation)] ≤
    Pr[fun result => ∃ value remaining, result.1 = some (value,remaining) ∧ event value result.2 |
      simulateQ impl (SphincsSecurity.QueryCap.recorded (SphincsSecurity.QueryCap.run selected computation budget))] := by
  induction computation using OracleComp.inductionOn generalizing budget event with
  | pure value =>
      simp only [SphincsSecurity.QueryCap.recorded_pure, SphincsSecurity.QueryCap.run_pure,
        simulateQ_pure, probEvent_pure]
      split_ifs with h1 h2
      · rfl
      · exact False.elim (h2 ⟨value,budget,rfl,h1.1⟩)
      · exact zero_le
      · rfl
  | query_bind input next ih =>
      rw [SphincsSecurity.QueryCap.recorded_query_bind, SphincsSecurity.QueryCap.run_query_bind]
      by_cases hs : selected input
      · rw [if_pos hs]
        cases budget with
        | zero =>
            refine le_trans (le_of_eq ?_) zero_le
            rw [probEvent_eq_zero_iff]
            intro result hresult hevent
            simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, mem_support_bind_iff,
              mem_support_pure_iff] at hresult
            obtain ⟨answer,-,tail,-,rfl⟩ := hresult
            have h := hevent.2
            rw [SphincsSecurity.QueryCap.calls_cons,if_pos hs] at h
            omega
        | succ remaining =>
            rw [SphincsSecurity.QueryCap.recorded_query_bind]
            simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
            apply SigGolfCandidate.T3.Security.Wots.Ref.probEvent_bind_mono
            intro answer
            simp only [bind_pure_comp,probEvent_map]
            refine le_trans (le_of_eq (probEvent_ext ?_)) (ih answer remaining
              (fun value tail => event value (input::tail)))
            intro tail _
            simp only [Function.comp_apply,SphincsSecurity.QueryCap.calls_cons,if_pos hs]
            constructor
            · rintro ⟨he,hc⟩;exact ⟨he,by omega⟩
            · rintro ⟨he,hc⟩;exact ⟨he,by omega⟩
      · rw [if_neg hs,SphincsSecurity.QueryCap.recorded_query_bind]
        simp only [simulateQ_bind,simulateQ_spec_query,simulateQ_pure]
        apply SigGolfCandidate.T3.Security.Wots.Ref.probEvent_bind_mono
        intro answer
        simp only [bind_pure_comp,probEvent_map]
        refine le_trans (le_of_eq (probEvent_ext ?_)) (ih answer budget
          (fun value tail => event value (input::tail)))
        intro tail _
        simp only [Function.comp_apply,SphincsSecurity.QueryCap.calls_cons,if_neg hs,Nat.zero_add]
end ClaudeWCT.W9.T3.Security.WPair.Counted.Generic

namespace ClaudeWCT.W9.T3.Security.WPair.Paired.Counted
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots (RefWorld RefCharged ticks)
open ClaudeWCT.W9.T3M.Final.Paired (AdversaryP)
open SphincsSecurity.Concrete.SecretGuessObservation
open ClaudeWCT.W9.T3.Security.WPair.Counted
set_option maxHeartbeats 150000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local instance] ClaudeWCT.W9.T3.Security.WPair.Counted.chargedDecidable
attribute [local irreducible] keygen
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (omega : CanonTable.Omega U)

theorem offlineInteraction_eq (T : Answers) (published : SigGolfCandidate.T3.Cache) {α : Type}
    (program : OracleComp Paired.Interaction α) :
    offlineInteraction T published program = Wots.PairedReference.offlineInteraction T published program := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
    rcases input with input | request
    · rw [offlineInteraction_world, Wots.PairedReference.Ref.offlineInteraction_world]
      exact bind_congr ih
    · rw [offlineInteraction_request, Wots.PairedReference.Ref.offlineInteraction_request]
      have hs : offlineSign T published request = Wots.PairedReference.offlineSign T published request := rfl
      rw [hs]
      apply bind_congr
      intro signature
      rw [ih,bind_pure_comp]

noncomputable def worldC (adversary : AdversaryP) :
    OracleComp CountSpec (Bool × QueryLog Paired.Requests × List Wots.Entry) := do
  clocks (Wots.keygenCharge (wA hU omega 0))
  let generated := evalWithAnswerFn (wA hU omega 0) keygen
  experimentC hU omega generated.2 (adversary generated.1 generated.2)
    (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker generated.1)
noncomputable def cappedWorld (adversary : AdversaryP) (budget : Nat) :=
  cappedProgram (worldC hU omega adversary) budget
noncomputable def worldRLog (T : Answers) (adversary : AdversaryP) :
    OracleComp RefWorld (Bool × QueryLog Paired.Requests) := do
  ticks (Wots.keygenCharge T)
  let generated := evalWithAnswerFn T keygen
  let interaction ← Wots.PairedReference.offlineInteraction T generated.2
    (adversary generated.1 generated.2)
  let verdict ← simulateQ Wots.verdictImpl
    (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker generated.1 interaction)
  pure (verdict, interaction.2)

attribute [local irreducible] worldC worldRLog cappedWorld experimentC

theorem worldRLog_fst (T : Answers) (adversary : AdversaryP) :
    Prod.fst <$> worldRLog T adversary = Wots.PairedReference.offlineGame T adversary := by
  simp only [worldRLog, Wots.PairedReference.offlineGame, map_bind, map_pure, bind_pure]

theorem worldC_log_transport (g : CanonTable.HiddenF) (adversary : AdversaryP) (budget : Nat) :
    observed g (SphincsSecurity.QueryCap.run charged
      (worldC hU omega adversary >>= fun result => pure (result.1, result.2.1)) budget) =
      refObserved (wA hU omega g) (SphincsSecurity.QueryCap.run RefCharged
        (worldRLog (wA hU omega g) adversary) budget) := by
  unfold worldC worldRLog experimentC
  simp only [bind_assoc, pure_bind]
  rw [observed_run_clocks_bind, refObserved_run_ticks_bind,
    keygenCharge_eq hU omega 0 g, keygen_answers hU omega g]
  split_ifs
  · rw [← offlineInteraction_eq]
    refine interactionC_transport hU omega g _ _
      (fun result => WPair.Counted.programC hU omega
        (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker
          (evalWithAnswerFn (wA hU omega 0) keygen).1 result) >>= fun checked => pure (checked.1, result.2))
      (fun result => simulateQ Wots.verdictImpl
        (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker
          (evalWithAnswerFn (wA hU omega 0) keygen).1 result) >>= fun checked => pure (checked, result.2)) ?_ _
    intro result remaining
    exact WPair.Counted.programC_transport hU omega g _
      (fun value => pure (value,result.2)) (fun value => pure (value,result.2))
      (fun value remaining => rfl) remaining
  · rfl

theorem worldC_transport (g : CanonTable.HiddenF) (adversary : AdversaryP) (budget : Nat) :
    observed g (SphincsSecurity.QueryCap.run charged
      (worldC hU omega adversary >>= fun result => pure result.1) budget) =
      refObserved (wA hU omega g) (Wots.PairedReference.referenceGame (wA hU omega g) adversary budget) := by
  unfold worldC Wots.PairedReference.referenceGame Wots.PairedReference.offlineGame experimentC
  simp only [bind_assoc, pure_bind]
  rw [observed_run_clocks_bind, refObserved_run_ticks_bind,
    keygenCharge_eq hU omega 0 g, keygen_answers hU omega g]
  split_ifs
  · rw [← offlineInteraction_eq]
    refine interactionC_transport hU omega g _ _
      (fun result => WPair.Counted.programC hU omega
        (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker
          (evalWithAnswerFn (wA hU omega 0) keygen).1 result) >>= fun checked => pure checked.1)
      (fun result => simulateQ Wots.verdictImpl
        (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker
          (evalWithAnswerFn (wA hU omega 0) keygen).1 result)) ?_ _
    intro result remaining
    have ht := WPair.Counted.programC_transport hU omega g
      (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker
        (evalWithAnswerFn (wA hU omega 0) keygen).1 result)
      (fun value => pure value) (fun value => pure value)
      (fun value remaining => rfl) remaining
    simpa only [bind_pure] using ht
  · rfl

theorem worldC_public_transport (g : CanonTable.HiddenF) (adversary : AdversaryP) (budget : Nat) :
    (fun result => publicInputs result.2) <$> simulateQ (fixedCount g) (cappedWorld hU omega adversary budget) =
      (fun result => refPublicInputs result.2) <$> Wots.PairedReference.offlineRun (wA hU omega g) adversary budget := by
  have h := congrArg (Functor.map Prod.snd) (worldC_transport hU omega g adversary budget)
  rw [bind_pure_comp, run_map_result, observed_map] at h
  simpa only [observed_recorded, refObserved_recorded, Functor.map_map, cappedWorld, cappedProgram,
    Wots.PairedReference.offlineRun] using h

theorem funded_worldC (adversary : AdversaryP) (credit : Nat) :
    Funded (worldC hU omega adversary) credit := by
  unfold worldC
  apply funded_bind _ _ _ (funded_clocks _ _)
  intro _ remaining
  exact funded_experimentC hU omega _ _ _ remaining

theorem dropClocks_worldC (adversary : AdversaryP) :
    dropClocks (worldC hU omega adversary) =
      Paired.experimentW hU omega (evalWithAnswerFn (wA hU omega 0) keygen).2
        (adversary (evalWithAnswerFn (wA hU omega 0) keygen).1 (evalWithAnswerFn (wA hU omega 0) keygen).2)
        (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker
          (evalWithAnswerFn (wA hU omega 0) keygen).1) := by
  rw [worldC, dropClocks_bind, dropClocks_clocks, pure_bind, dropClocks_experimentC]

set_option backward.isDefEq.respectTransparency true in
theorem world_completed_tracks (hidden : CanonTable.HiddenF) (adversary : AdversaryP)
    (budget remaining : Nat) (value : Bool × QueryLog Paired.Requests × List Wots.Entry)
    (queries : List CountSpec.Domain) (final : CountState)
    (hr : fixedRun countEnvironment (Guess.Fam.phi hidden.1 hidden.2)
      (cappedWorld hU omega adversary budget) countInit ((some (value, remaining), queries), final) ≠ 0) :
    Paired.Tracks hU omega hidden init final value.2.1 value.2.2 := by
  have hc : cappedWorld hU omega adversary budget = cappedProgram (worldC hU omega adversary) budget := by
    unfold cappedWorld
    rfl
  have hr' := Eq.mp (congrArg (fun program => fixedRun countEnvironment (Guess.Fam.phi hidden.1 hidden.2)
    program countInit ((some (value,remaining),queries),final) ≠ 0) hc) hr
  have hs := fixedRun_recorded_cap_erasure hidden (worldC hU omega adversary)
    (Paired.experimentW hU omega (evalWithAnswerFn (wA hU omega 0) keygen).2
      (adversary (evalWithAnswerFn (wA hU omega 0) keygen).1
        (evalWithAnswerFn (wA hU omega 0) keygen).2)
      (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker
        (evalWithAnswerFn (wA hU omega 0) keygen).1))
    (dropClocks_worldC hU omega adversary)
    budget remaining value queries countInit final hr'
  have hi : countInit = init := rfl
  have hs' := Eq.mp (congrArg (fun state => fixedRun env (Guess.Fam.phi hidden.1 hidden.2)
    (Paired.experimentW hU omega (evalWithAnswerFn (wA hU omega 0) keygen).2
      (adversary (evalWithAnswerFn (wA hU omega 0) keygen).1
        (evalWithAnswerFn (wA hU omega 0) keygen).2)
      (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker
        (evalWithAnswerFn (wA hU omega 0) keygen).1)) state (value,final) ≠ 0) hi) hs
  exact Paired.experimentW_tracks hU omega hidden
    (evalWithAnswerFn (wA hU omega 0) keygen).2
    (adversary (evalWithAnswerFn (wA hU omega 0) keygen).1
      (evalWithAnswerFn (wA hU omega 0) keygen).2)
    (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker
      (evalWithAnswerFn (wA hU omega 0) keygen).1)
    (PairedOuter.PaddedGame.verdict_public _) init (value,final) hs'

theorem world_event_le_external (adversary : AdversaryP) (budget : Nat) (hbudget : budget < 2^128)
    (event : CanonTable.HiddenF → RunResult (β := Bool) → Prop)
    (hevent : ∀ hidden result, event hidden result → ∃ output remaining,
      result.1 = some (output, remaining) ∧ ¬Paired.OverflowIn (wA hU omega hidden) output.2.1 ∧
      ∃ cell, Paired.GuessedIn (wA hU omega hidden) output.2.1 output.2.2 cell) :
    Pr[fun result => event result.1 result.2 | WPair.Counted.Generic.countedProgramRun
      (cappedWorld hU omega adversary budget)] ≤
      (((2^128-budget : Nat) : ENNReal))⁻¹ *
      ∑' result, Pr[= result | withRun countEnvironment (Guess.Fam.sampler PUnit)
        (cappedWorld hU omega adversary budget) countInit] *
        (probeCount (publicInputs result.1.2) : ENNReal) := by
  unfold cappedWorld
  apply (WPair.Counted.Generic.counted_program_event_le_world (cappedProgram (worldC hU omega adversary) budget) event
    (fun result => ¬Guess.Fam.Bad result.2 ∧ result.2.probes ≤ budget ∧ result.2.guesses.Nonempty) ?_).trans
    (WPair.Counted.Generic.first_probe_le_external (worldC hU omega adversary)
      (funded_worldC hU omega adversary 0) budget hbudget)
  intro hidden result hr he
  obtain ⟨output, remaining, hout, hno, cell, hg⟩ := hevent hidden result.1 he
  rcases result with ⟨⟨out, queries⟩, final⟩
  dsimp only at hout
  subst out
  have ht := world_completed_tracks hU omega hidden adversary budget remaining output queries final (by simpa only [cappedWorld] using hr)
  refine ⟨Paired.tracked_noBad hU omega hidden final _ _ ht hno, ?_,
    Paired.tracked_guessed hU omega hidden final _ _ ht cell hg⟩
  apply WPair.Counted.Generic.capped_probes_le_budget (worldC hU omega adversary) budget
    (funded_worldC hU omega adversary 0) (fixedSampler (Guess.Fam.phi hidden.1 hidden.2)) _
  rwa [withRun_fixedSampler]
end ClaudeWCT.W9.T3.Security.WPair.Paired.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Paired.Counted
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots (RefWorld RefCharged ticks)
open ClaudeWCT.W9.T3M.Final.Paired (AdversaryP)
open SphincsSecurity.Concrete.SecretGuessObservation
open ClaudeWCT.W9.T3.Security.WPair.Counted
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local instance] ClaudeWCT.W9.T3.Security.WPair.Counted.chargedDecidable
attribute [local irreducible] keygen worldC cappedWorld experimentC
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (omega : CanonTable.Omega U)

def publicEntriesOf (T : Answers) (inputs : List HashInput) : List Wots.Entry :=
  inputs.map (fun x => (x,T (.inl (.inr x))))
theorem publicEntriesOf_append (T : Answers) (xs ys : List HashInput) :
    publicEntriesOf T (xs++ys)=publicEntriesOf T xs++publicEntriesOf T ys := List.map_append

theorem observed_hashC (g : CanonTable.HiddenF) (x : HashInput) :
    observed g (WPair.Counted.hashC hU omega x) = pure (wA hU omega g (.inl (.inr x)),[x]) := by
  rw [WPair.Counted.hashC, observed_bind, observed_clock, pure_bind, observed_liftW, fixed_hashW, map_pure, pure_bind]
  rfl

theorem observed_signC (g : CanonTable.HiddenF) (published : SigGolfCandidate.T3.Cache) (request : Request) :
    observed g (signC hU omega published request) =
      pure (evalWithAnswerFn (wA hU omega g) (Paired.authenticatedSign published request),[]) := by
  rw [signC, observed_bind, observed_clocks, pure_bind, observed_liftW, Paired.fixed_signW, map_pure, pure_bind]
  rfl

theorem interactionC_entries (g : CanonTable.HiddenF) (published : SigGolfCandidate.T3.Cache)
    {α : Type} (program : OracleComp Paired.Interaction α)
    (result : (α × QueryLog Paired.Requests × List Wots.Entry) × List HashInput)
    (hr : result ∈ support (observed g (interactionC hU omega published program))) :
    result.1.2.2 = publicEntriesOf (wA hU omega g) result.2 := by
  induction program using OracleComp.inductionOn generalizing result with
  | pure value =>
      rw [interactionC_pure,observed_pure,mem_support_pure_iff] at hr
      subst result
      rfl
  | query_bind input next ih =>
      rcases input with (n|x)|request
      · rw [interactionC_coin,observed_query_bind] at hr
        simp only [mem_support_bind_iff,mem_support_pure_iff] at hr
        obtain ⟨coin,-,tail,ht,rfl⟩ := hr
        exact ih coin tail ht
      · rw [interactionC_public,observed_bind,observed_hashC] at hr
        simp only [pure_bind,observed_bind,observed_pure,bind_assoc,List.append_nil,List.nil_append] at hr
        simp only [mem_support_bind_iff,mem_support_pure_iff] at hr
        obtain ⟨tail,ht,rfl⟩ := hr
        simpa only [publicEntriesOf,List.map_cons,List.append_nil,List.cons_append,List.nil_append]
          using congrArg (List.cons (x,wA hU omega g (.inl (.inr x)))) (ih _ tail ht)
      · rw [interactionC_request,observed_bind,observed_signC] at hr
        simp only [pure_bind,observed_bind,observed_pure,bind_assoc,List.append_nil,List.nil_append] at hr
        simp only [mem_support_bind_iff,mem_support_pure_iff] at hr
        obtain ⟨tail,ht,rfl⟩ := hr
        simpa only [List.nil_append,List.append_nil] using ih _ tail ht

theorem programC_entries (g : CanonTable.HiddenF) {β : Type} (program : M β)
    (result : (β × List Wots.Entry) × List HashInput)
    (hr : result ∈ support (observed g (WPair.Counted.programC hU omega program))) :
    result.1.2 = publicEntriesOf (wA hU omega g) result.2 := by
  induction program using OracleComp.inductionOn generalizing result with
  | pure value =>
      rw [WPair.Counted.programC_pure,observed_pure,mem_support_pure_iff] at hr
      subst result
      rfl
  | query_bind input next ih =>
      rcases input with (n|x)|coordinate
      · rw [WPair.Counted.programC_coin,observed_query_bind] at hr
        simp only [mem_support_bind_iff,mem_support_pure_iff] at hr
        obtain ⟨coin,-,tail,ht,rfl⟩ := hr
        exact ih coin tail ht
      · rw [WPair.Counted.programC_public,observed_bind,observed_hashC] at hr
        simp only [pure_bind,observed_bind,observed_pure,bind_assoc,List.append_nil,List.nil_append] at hr
        simp only [mem_support_bind_iff,mem_support_pure_iff] at hr
        obtain ⟨tail,ht,rfl⟩ := hr
        simpa only [publicEntriesOf,List.map_cons,List.append_nil,List.cons_append,List.nil_append]
          using congrArg (List.cons (x,wA hU omega g (.inl (.inr x)))) (ih _ tail ht)
      · rw [WPair.Counted.programC_private] at hr
        exact ih _ result hr

theorem worldC_entries (g : CanonTable.HiddenF) (adversary : AdversaryP)
    (result : (Bool × QueryLog Paired.Requests × List Wots.Entry) × List HashInput)
    (hr : result ∈ support (observed g (worldC hU omega adversary))) :
    result.1.2.2=publicEntriesOf (wA hU omega g) result.2 := by
  unfold worldC experimentC at hr
  rw [observed_bind,observed_clocks,pure_bind,observed_bind] at hr
  simp only [observed_bind,observed_pure,pure_bind,bind_assoc,List.append_nil,List.nil_append] at hr
  simp only [mem_support_bind_iff,mem_support_pure_iff] at hr
  obtain ⟨interaction,hi,checked,hc,rfl⟩ := hr
  simp only [List.nil_append,List.append_nil,publicEntriesOf_append]
  rw [interactionC_entries hU omega g _ _ _ hi, programC_entries hU omega g _ _ hc]

/-- This erasure keeps the observed public transcript of every completed run. -/
theorem observed_cap_completed (g : CanonTable.HiddenF) {α : Type}
    (program : OracleComp CountSpec α) (budget remaining : Nat) (value : α) (inputs : List HashInput)
    (hr : (some (value,remaining),inputs) ∈ support
      (observed g (SphincsSecurity.QueryCap.run charged program budget))) :
    (value,inputs) ∈ support (observed g program) := by
  induction program using OracleComp.inductionOn generalizing budget remaining inputs with
  | pure result =>
      simp only [SphincsSecurity.QueryCap.run_pure,observed_pure,mem_support_pure_iff,
        Prod.mk.injEq,Option.some.injEq] at hr
      obtain ⟨⟨rfl,rfl⟩,rfl⟩ := hr
      simp only [observed_pure,mem_support_pure_iff]
  | query_bind input next ih =>
      rw [SphincsSecurity.QueryCap.run_query_bind] at hr
      by_cases hc : charged input
      · rw [if_pos hc] at hr
        cases budget with
        | zero => simpa [observed_pure] using hr
        | succ budget =>
            rw [observed_query_bind] at hr ⊢
            simp only [mem_support_bind_iff,mem_support_pure_iff] at hr ⊢
            obtain ⟨answer,ha,tail,ht,he⟩ := hr
            obtain ⟨hs,hs'⟩ := Prod.mk.inj he
            refine ⟨answer,ha,(value,tail.2),?_,?_⟩
            · apply ih answer budget remaining tail.2
              simpa only [hs,Prod.mk.eta] using ht
            · exact Prod.ext rfl hs'
      · rw [if_neg hc,observed_query_bind] at hr
        rw [observed_query_bind]
        simp only [mem_support_bind_iff,mem_support_pure_iff] at hr ⊢
        obtain ⟨answer,ha,tail,ht,he⟩ := hr
        obtain ⟨hs,hs'⟩ := Prod.mk.inj he
        refine ⟨answer,ha,(value,tail.2),?_,?_⟩
        · apply ih answer budget remaining tail.2
          simpa only [hs,Prod.mk.eta] using ht
        · exact Prod.ext rfl hs'
end ClaudeWCT.W9.T3.Security.WPair.Paired.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Paired.Counted
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots (RefWorld RefCharged ticks)
open ClaudeWCT.W9.T3M.Final.Paired (AdversaryP)
open ClaudeWCT.W9.T3.Security.WPair.Counted
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen worldC worldRLog cappedWorld
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (omega : CanonTable.Omega U)

theorem publicEntriesOf_ref (T : Answers) (queries : List RefWorld.Domain) :
    publicEntriesOf T (refPublicInputs queries)=Wots.traceOf T queries := by
  induction queries with
  | nil => rfl
  | cons input queries ih =>
    rcases input with (n|x)|tick <;> simpa [publicEntriesOf,refPublicInputs,Wots.traceOf] using ih

theorem cappedWorld_entries (g : CanonTable.HiddenF) (adversary : AdversaryP)
    (budget remaining : Nat) (value : Bool × QueryLog Paired.Requests × List Wots.Entry)
    (queries : List CountSpec.Domain)
    (hr : (some (value,remaining),queries) ∈ support
      (simulateQ (fixedCount g) (cappedWorld hU omega adversary budget))) :
    value.2.2=publicEntriesOf (wA hU omega g) (publicInputs queries) := by
  apply worldC_entries hU omega g adversary (value,publicInputs queries)
  apply observed_cap_completed g (worldC hU omega adversary) budget remaining value (publicInputs queries)
  rw [observed_recorded,support_map]
  exact ⟨(some (value,remaining),queries),by simpa only [cappedWorld,cappedProgram] using hr,rfl⟩

theorem worldC_log_distribution (g : CanonTable.HiddenF) (adversary : AdversaryP) (budget : Nat) :
    (fun run : RunResult (β := Bool) =>
      (run.1.map (fun value => ((value.1.1,value.1.2.1),value.2)),publicInputs run.2)) <$>
      simulateQ (fixedCount g) (cappedWorld hU omega adversary budget) =
    (fun run => (run.1,refPublicInputs run.2)) <$>
      simulateQ (Wots.refImpl (wA hU omega g)) (SphincsSecurity.QueryCap.recorded
        (SphincsSecurity.QueryCap.run RefCharged (worldRLog (wA hU omega g) adversary) budget)) := by
  have ht := worldC_log_transport hU omega g adversary budget
  rw [bind_pure_comp,run_map_result,observed_map] at ht
  simpa only [observed_recorded,refObserved_recorded,Functor.map_map,cappedWorld,cappedProgram] using ht

theorem worldRLog_event_eq (g : CanonTable.HiddenF) (adversary : AdversaryP) (budget : Nat)
    (P : QueryLog Paired.Requests → List Wots.Entry → Prop) :
    Pr[fun run => ∃ value remaining,run.1=some (value,remaining) ∧
        P value.2 (Wots.traceOf (wA hU omega g) run.2) |
      simulateQ (Wots.refImpl (wA hU omega g)) (SphincsSecurity.QueryCap.recorded
        (SphincsSecurity.QueryCap.run RefCharged (worldRLog (wA hU omega g) adversary) budget))] =
    Pr[fun run => ∃ value remaining,run.1=some (value,remaining) ∧ P value.2.1 value.2.2 |
      simulateQ (fixedCount g) (cappedWorld hU omega adversary budget)] := by
  have ht := congrArg (fun experiment : ProbComp
      (Option ((Bool × QueryLog Paired.Requests) × Nat) × List HashInput) =>
    Pr[fun run => ∃ value remaining,run.1=some (value,remaining) ∧
      P value.2 (publicEntriesOf (wA hU omega g) run.2) | experiment])
    (worldC_log_distribution hU omega g adversary budget)
  simp only [probEvent_map,Function.comp_def,publicEntriesOf_ref] at ht
  refine ht.symm.trans (probEvent_ext ?_)
  intro run hr
  rcases run with ⟨out,queries⟩
  cases out with
  | none => simp
  | some found =>
    rcases found with ⟨value,remaining⟩
    have he := cappedWorld_entries hU omega g adversary budget remaining value queries hr
    simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq,exists_and_left,
      exists_eq_left,exists_eq_left',he, and_assoc]
end ClaudeWCT.W9.T3.Security.WPair.Paired.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Paired.Counted
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots (RefWorld RefCharged ticks)
open ClaudeWCT.W9.T3M.Final.Paired (AdversaryP ForgeryP)
open ClaudeWCT.W9.T3.Security.WPair.Counted
open SigGolfCandidate.T3.Security.Wots.Ref (cap_recorded_le chargeSum chargeSum_append cut pureRecord pureRecord_value
  fixedRecord_counted fixedRecord_hashOnly pureRecord_charge recorded_bind ticks_recorded verdict_recorded_fixed
  traceOf_append calls_append traceOf_replicate_tick calls_replicate_tick traceOf_map_embed calls_map_embed_public embed)
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen worldRLog
variable (adversary : AdversaryP) (q : Nat) (T : Answers)
  (P : Answers → QueryLog Paired.Requests → List Wots.Entry → Prop)
  (hshort : ∀ A T log entries, Wots.Ref.ShortAgree A T → P A log entries → P T log entries)
  (hmono : ∀ A log entries entries', (∀ e∈entries,e∈entries') → P A log entries → P A log entries')
include hshort in
theorem fixed_step_full_charge (interaction : FirstHit.Recorded (Option ForgeryP × QueryLog Paired.Requests))
    (hi : interaction ∈ support (Wots.PairedReference.Ref.fixedInteraction adversary T))
    (hev : chargeSum (Wots.PairedReference.Ref.combine T interaction).events ≤ q ∧
      ∀ g i c, Wots.PairedReference.GameSplit adversary (Wots.PairedReference.Ref.combine T interaction) g i c →
        P (cut (Wots.PairedReference.Ref.combine T interaction).state T) i.value.2
          (SigGolfCandidate.T3.Security.BPair.publicEntries c.events)) :
    P T interaction.value.2 (Wots.entriesOf T (SourceReplay.queried T (verdictOn T interaction.value))) ∧
      Wots.keygenCharge T + chargeSum interaction.events +
        Wots.PairedReference.Ref.verdictCharge T (evalWithAnswerFn T keygen).1 interaction.value ≤ q := by
  have hp := Paired.fixed_step adversary q T P hshort interaction hi hev
  refine ⟨hp.2,?_⟩
  have hk : chargeSum (pureRecord T keygen (∅,∅)).events = Wots.keygenCharge T :=
    pureRecord_charge T keygen SourceReplay.keygen_hashOnly (∅,∅)
  have hv : chargeSum (Wots.PairedReference.Ref.verdictRecord T interaction).events =
      Wots.PairedReference.Ref.verdictCharge T (evalWithAnswerFn T keygen).1 interaction.value :=
    pureRecord_charge T _ (Wots.PairedReference.Ref.verdict_hashOnly _ _) interaction.state
  have hc : chargeSum (Wots.PairedReference.Ref.combine T interaction).events =
      chargeSum (pureRecord T keygen (∅,∅)).events +
        (chargeSum interaction.events + chargeSum (Wots.PairedReference.Ref.verdictRecord T interaction).events) := by
    simp only [Wots.PairedReference.Ref.combine,chargeSum_append]
  have hb := hev.1
  omega

include hmono in
theorem offline_log_event_le :
    Pr[fun x => P T x.1.2 (Wots.entriesOf T (SourceReplay.queried T (verdictOn T x.1))) ∧
        Wots.keygenCharge T+x.2+Wots.PairedReference.Ref.verdictCharge T (evalWithAnswerFn T keygen).1 x.1≤q |
      simulateQ (Wots.refImpl T) (SphincsSecurity.QueryCap.counted RefCharged
        (Wots.PairedReference.offlineInteraction T (evalWithAnswerFn T keygen).2
          (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2)))] ≤
    Pr[fun run => ∃ value remaining, run.1=some (value,remaining) ∧ P T value.2 (Wots.traceOf T run.2) |
      simulateQ (Wots.refImpl T) (SphincsSecurity.QueryCap.recorded
        (SphincsSecurity.QueryCap.run RefCharged (worldRLog T adversary) q))] := by
  refine le_trans ?_ (WPair.Counted.Generic.cap_recorded_completed_le RefCharged (Wots.refImpl T)
    (worldRLog T adversary) q (fun value queries => P T value.2 (Wots.traceOf T queries)))
  rw [← SphincsSecurity.QueryCap.recorded_counted,simulateQ_map,probEvent_map]
  unfold worldRLog
  rw [recorded_bind,simulateQ_bind,ticks_recorded,pure_bind,recorded_bind,simulateQ_bind]
  simp only [simulateQ_bind,simulateQ_pure,bind_assoc]
  simp only [recorded_bind,simulateQ_bind,verdict_recorded_fixed T _
    (PairedOuter.PaddedGame.verdict_public _ _),pure_bind,SphincsSecurity.QueryCap.recorded_pure,simulateQ_pure]
  rw [bind_pure_comp,probEvent_map]
  apply probEvent_mono
  rintro ⟨result,queries⟩ - ⟨hp,hcharge⟩
  refine ⟨?_,?_⟩
  · change P T result.2 (Wots.traceOf T (List.replicate (Wots.keygenCharge T) (.inr ()) ++ (queries ++
      (List.map embed (SourceReplay.queried T (verdictOn T result)) ++ []))))
    rw [List.append_nil,traceOf_append,traceOf_append,traceOf_replicate_tick,traceOf_map_embed]
    exact hmono _ _ _ _ (fun e he => List.mem_append_right _ (List.mem_append_right _ he)) hp
  · change SphincsSecurity.QueryCap.calls RefCharged (List.replicate (Wots.keygenCharge T) (.inr ()) ++
      (queries ++ (List.map embed (SourceReplay.queried T (verdictOn T result)) ++ []))) ≤ q
    rw [List.append_nil,calls_append,calls_append,calls_replicate_tick,
      calls_map_embed_public T _ (PairedOuter.PaddedGame.verdict_public _ _)]
    simpa only [Wots.PairedReference.Ref.verdictCharge,Nat.add_assoc] using hcharge

include hshort hmono in
theorem fixed_le_worldRLog :
    Pr[fun result => chargeSum result.events≤q ∧
        ∀ g i c,Wots.PairedReference.GameSplit adversary result g i c →
          P (cut result.state T) i.value.2 (SigGolfCandidate.T3.Security.BPair.publicEntries c.events) |
      Wots.Ref.fixedRecord T (PairedOuter.GameWith.idealGame PairedOuter.PaddedGame.checker adversary) (∅,∅)] ≤
    Pr[fun run => ∃ value remaining, run.1=some (value,remaining) ∧ P T value.2 (Wots.traceOf T run.2) |
      simulateQ (Wots.refImpl T) (SphincsSecurity.QueryCap.recorded
        (SphincsSecurity.QueryCap.run RefCharged (worldRLog T adversary) q))] := by
  rw [Wots.PairedReference.Ref.fixed_game_eq,probEvent_map]
  refine le_trans (probEvent_mono fun interaction hi he =>
    fixed_step_full_charge adversary q T P hshort interaction hi he) ?_
  have hcount := fixedRecord_counted T (PairedOuter.FullGame.loggedWith
    (PairedOuter.FullGame.authenticatedSign (evalWithAnswerFn T keygen).2)
      (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2))
    (pureRecord T keygen (∅,∅)).state
  rw [Wots.PairedReference.Ref.interaction_counted] at hcount
  refine le_trans (le_of_eq ?_) (offline_log_event_le adversary q T P hmono)
  rw [← hcount,probEvent_map]
  rfl
end ClaudeWCT.W9.T3.Security.WPair.Paired.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Paired.Counted
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M.Final.Paired (AdversaryP)
open SphincsSecurity.Concrete.SecretGuessObservation
open ClaudeWCT.W9.T3.Security.WPair.Counted
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local instance] ClaudeWCT.W9.T3.Security.WPair.Counted.chargedDecidable
attribute [local irreducible] keygen worldC cappedWorld
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (omega : CanonTable.Omega U)
variable (adversary : AdversaryP) (budget : Nat)
 theorem world_public_distribution :
    (fun result => publicInputs result.1.2) <$>
      withRun (Result := RunResult (β := Bool)) countEnvironment (Guess.Fam.sampler PUnit)
        (cappedWorld hU omega adversary budget) countInit =
    𝒮[do
      let hidden ← ($ᵗ CanonTable.HiddenF : ProbComp _)
      let result ← Wots.PairedReference.offlineRun (wA hU omega hidden) adversary budget
      pure (refPublicInputs result.2)] := by
  rw [WPair.Counted.Generic.public_program_distribution]
  apply congrArg (fun experiment : ProbComp (List HashInput) => 𝒮[experiment])
  apply bind_congr
  intro hidden
  simpa only [bind_pure_comp] using worldC_public_transport hU omega hidden adversary budget

 theorem world_public_payment_le_reference :
    (∑' result, Pr[= result | withRun (Result := RunResult (β := Bool)) countEnvironment (Guess.Fam.sampler PUnit)
      (cappedWorld hU omega adversary budget) countInit] *
      (probeCount (publicInputs result.1.2) : ENNReal)) ≤
    ∑' hidden, Pr[= hidden | ($ᵗ CanonTable.HiddenF : ProbComp _)] *
      ∑' run, Pr[= run | Wots.PairedReference.offlineRun (wA hU omega hidden) adversary budget] *
        (Wots.PairedReference.otherCount ⟨wA hU omega hidden, (evalWithAnswerFn (wA hU omega hidden) keygen).1,
          Wots.traceOf (wA hU omega hidden) run.2⟩ : ENNReal) := by
  rw [← tsum_probOutput_map_mul _ (fun result : RunResult (β := Bool) × CountState => publicInputs result.1.2)
    (fun inputs => (probeCount inputs : ENNReal)), world_public_distribution hU omega adversary budget]
  simp only [bind_pure_comp, evalSPMF_bind, evalSPMF_map]
  rw [tsum_probOutput_bind_mul]
  apply ENNReal.tsum_le_tsum
  intro hidden
  simp only [probOutput_evalSPMF]
  apply mul_le_mul' le_rfl
  rw [tsum_probOutput_map_mul]
  simp only [probOutput_evalSPMF]
  apply ENNReal.tsum_le_tsum
  intro run
  apply mul_le_mul' le_rfl
  rw [refPublicInputs_eq_trace (wA hU omega hidden)]
  exact_mod_cast probeCount_le_other_new (wA hU omega hidden) _ (Wots.traceOf (wA hU omega hidden) run.2)

 theorem world_event_le_other
    (hbudget : budget < 2^128)
    (event : CanonTable.HiddenF → RunResult (β := Bool) → Prop)
    (hevent : ∀ hidden result, event hidden result → ∃ output remaining,
      result.1 = some (output, remaining) ∧ ¬Paired.OverflowIn (wA hU omega hidden) output.2.1 ∧
      ∃ cell, Paired.GuessedIn (wA hU omega hidden) output.2.1 output.2.2 cell) :
    Pr[fun result => event result.1 result.2 | WPair.Counted.Generic.countedProgramRun
      (cappedWorld hU omega adversary budget)] ≤
      (((2^128-budget : Nat) : ENNReal))⁻¹ *
      (∑' hidden, Pr[= hidden | ($ᵗ CanonTable.HiddenF : ProbComp _)] *
      ∑' run, Pr[= run | Wots.PairedReference.offlineRun (wA hU omega hidden) adversary budget] *
        (Wots.PairedReference.otherCount ⟨wA hU omega hidden, (evalWithAnswerFn (wA hU omega hidden) keygen).1,
          Wots.traceOf (wA hU omega hidden) run.2⟩ : ENNReal)) :=
  (world_event_le_external hU omega adversary budget hbudget event hevent).trans
    (mul_le_mul' le_rfl (world_public_payment_le_reference hU omega adversary budget))


end ClaudeWCT.W9.T3.Security.WPair.Paired.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Paired.Counted
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots (RefSample)
open ClaudeWCT.W9.T3M.Final.Paired (AdversaryP)
open ClaudeWCT.W9.T3.Security.CanonGraph
set_option maxHeartbeats 300000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency true
attribute [local instance] Classical.propDecidable
attribute [local instance] instFintypeCoordinate_canonGraph instSampleableTypeFullTable_canonGraph
  instSampleableTypeHashOutput_canonGraph_1 instSampleableTypeLabels_1 instSampleableTypeSecrets
  instSampleableTypeOtherHalves instFintypeSecrets_canonGraph instFintypeOtherHalves_canonGraph
  instSampleableTypeProdSecretsOtherHalves instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_canonGraph_1
  instSampleableTypeLowLabels instSampleableTypeProdLowLabels CanonTable.instSampleableTypeHidden
attribute [local irreducible] keygen Wots.PairedReference.referenceInputs Wots.PairedReference.offlineRun Wots.PairedReference.otherCount

noncomputable def tableAverage {α : Type} (adversary : AdversaryP) (K : Answers → ProbComp α) : ProbComp α :=
  ($ᵗ FullGame.FullTable : ProbComp _) >>= fun privateTable =>
    ($ᵗ (Wots.PairedReference.referenceInputs adversary → HashOutput) : ProbComp _) >>= fun publicTable =>
      K (Wots.eagerAnswers (Wots.PairedReference.referenceInputs adversary) privateTable publicTable)

theorem tableAverage_eq {α : Type} (adversary : AdversaryP) (K : Answers → ProbComp α) :
    𝒮[tableAverage adversary K] =
    𝒮[omegaLaw (Wots.PairedReference.referenceInputs adversary) >>= fun omega =>
      ($ᵗ CanonTable.HiddenF : ProbComp _) >>= fun g => K (wA (canon_subset adversary) omega g)] := by
  unfold tableAverage
  have h1 : (fun privateTable =>
      ($ᵗ (Wots.PairedReference.referenceInputs adversary → HashOutput) : ProbComp _) >>= fun publicTable =>
        K (Wots.eagerAnswers (Wots.PairedReference.referenceInputs adversary) privateTable publicTable)) =
      (fun privateTable =>
      ($ᵗ (Wots.PairedReference.referenceInputs adversary → HashOutput) : ProbComp _) >>= fun publicTable =>
        K (CanonGraph.eagerAnswers privateTable (Wots.PairedReference.referenceInputs adversary) publicTable)) := by
    funext privateTable
    apply bind_congr
    intro publicTable
    simp only [eagerAnswers_eq]
  rw [h1,CanonTable.world_tables_bind (canon_subset adversary) K]
  unfold omegaLaw
  simp only [bind_assoc,pure_bind]

noncomputable def referenceOther (adversary : AdversaryP) (q : Nat) : ENNReal :=
  ∑' s, Wots.PairedReference.referenceExperiment adversary q s * (Wots.PairedReference.otherCount s : ENNReal)

noncomputable def worldOther (adversary : AdversaryP) (q : Nat)
    (omega : CanonTable.Omega (Wots.PairedReference.referenceInputs adversary)) : ENNReal :=
  ∑' g, Pr[=g|($ᵗ CanonTable.HiddenF : ProbComp _)] *
    ∑' run, Pr[=run|Wots.PairedReference.offlineRun (wA (canon_subset adversary) omega g) adversary q] *
      (Wots.PairedReference.otherCount ⟨wA (canon_subset adversary) omega g,
        (evalWithAnswerFn (wA (canon_subset adversary) omega g) keygen).1,
        Wots.traceOf (wA (canon_subset adversary) omega g) run.2⟩ : ENNReal)

theorem lift_prob_apply {α : Type} (c : ProbComp α) (x : α) : (liftM c : PMF α) x = Pr[=x|c] := by
  rw [← PMF.probOutput_eq_apply]
  have h1 : 𝒮[(liftM c : PMF α)] = 𝒮[c] := by
    rw [evalSPMF_eq_simulateQ, PMF.evalSPMF_eq]
    rfl
  unfold probOutput
  rw [h1]

theorem expectation_congr {α : Type} (c d : ProbComp α) (h : 𝒮[c]=𝒮[d]) (f : α → ENNReal) :
    (∑' x, Pr[=x|c]*f x) = ∑' x, Pr[=x|d]*f x := by
  apply tsum_congr
  intro x
  have hp : Pr[=x|c]=Pr[=x|d] := by
    rw [←probOutput_evalSPMF,h,probOutput_evalSPMF]
  rw [hp]

theorem tableAverage_expect {α : Type} (adversary : AdversaryP) (K : Answers → ProbComp α)
    (f : α → ENNReal) :
    (∑' x, Pr[=x|tableAverage adversary K]*f x) =
      ∑' omega,Pr[=omega|omegaLaw (Wots.PairedReference.referenceInputs adversary)] *
      ∑' g,Pr[=g|($ᵗ CanonTable.HiddenF : ProbComp _)] *
      ∑' x,Pr[=x|K (wA (canon_subset adversary) omega g)]*f x := by
  rw [expectation_congr _ _ (tableAverage_eq adversary K),tsum_probOutput_bind_mul]
  apply tsum_congr
  intro omega
  rw [tsum_probOutput_bind_mul]

noncomputable def sampleRun (adversary : AdversaryP) (q : Nat) (T : Answers) : ProbComp RefSample :=
  (fun run => (⟨T,(evalWithAnswerFn T keygen).1,Wots.traceOf T run.2⟩ : RefSample)) <$>
    Wots.PairedReference.offlineRun T adversary q

theorem referenceComp_tableAverage (adversary : AdversaryP) (q : Nat) :
    𝒮[Wots.PairedReference.referenceComp adversary q] =
    𝒮[tableAverage adversary (sampleRun adversary q)] := by
  unfold Wots.PairedReference.referenceComp tableAverage sampleRun
  rw [SigGolfCandidate.T3.Security.BPair.bind_uniform_congr _ instSampleableTypeFullTable_canonGraph]

theorem lift_expect {α : Type} (c : ProbComp α) (f : α → ENNReal) :
    (∑' x,(liftM c : PMF α) x*f x) = ∑' x,Pr[=x|c]*f x := by
  apply tsum_congr
  intro x
  exact congrArg (fun p => p*f x) (lift_prob_apply c x)

theorem referenceOther_eq (adversary : AdversaryP) (q : Nat) :
    referenceOther adversary q = ∑' s,Pr[=s|Wots.PairedReference.referenceComp adversary q]*
      (Wots.PairedReference.otherCount s : ENNReal) := by
  have hd : Wots.PairedReference.referenceExperiment adversary q =
      (liftM (Wots.PairedReference.referenceComp adversary q) : PMF RefSample) := rfl
  exact (congrArg (fun mu : PMF RefSample => ∑' s,mu s*(Wots.PairedReference.otherCount s : ENNReal)) hd).trans
    (lift_expect (Wots.PairedReference.referenceComp adversary q) (fun s=>(Wots.PairedReference.otherCount s : ENNReal)))

theorem worldOther_eq (adversary : AdversaryP) (q : Nat)
    (omega : CanonTable.Omega (Wots.PairedReference.referenceInputs adversary)) :
    worldOther adversary q omega = ∑' g,Pr[=g|($ᵗ CanonTable.HiddenF : ProbComp _)] *
      ∑' s,Pr[=s|sampleRun adversary q (wA (canon_subset adversary) omega g)]*
        (Wots.PairedReference.otherCount s : ENNReal) := by
  unfold worldOther
  apply tsum_congr
  intro g
  unfold sampleRun
  rw [tsum_probOutput_map_mul]

theorem referenceOther_avg (adversary : AdversaryP) (q : Nat) :
    referenceOther adversary q = ∑' omega,
      Pr[=omega|omegaLaw (Wots.PairedReference.referenceInputs adversary)] * worldOther adversary q omega := by
  rw [referenceOther_eq]
  refine (expectation_congr _ _ (referenceComp_tableAverage adversary q) _).trans ?_
  refine (tableAverage_expect adversary (sampleRun adversary q) _).trans ?_
  apply tsum_congr
  intro omega
  rw [worldOther_eq]
end ClaudeWCT.W9.T3.Security.WPair.Paired.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Paired.Counted
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots (RefWorld RefCharged)
open ClaudeWCT.W9.T3M.Final.Paired (AdversaryP)
open ClaudeWCT.W9.T3.Security.WPair.Counted
open ClaudeWCT.W9.T3.Security.CanonGraph
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency true
attribute [local instance] Classical.propDecidable
attribute [local instance] instFintypeCoordinate_canonGraph instSampleableTypeFullTable_canonGraph
  instSampleableTypeHashOutput_canonGraph_1 instSampleableTypeLabels_1 instSampleableTypeSecrets
  instSampleableTypeOtherHalves instFintypeSecrets_canonGraph instFintypeOtherHalves_canonGraph
  instSampleableTypeProdSecretsOtherHalves instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_canonGraph_1
  instSampleableTypeLowLabels instSampleableTypeProdLowLabels CanonTable.instSampleableTypeHidden
attribute [local irreducible] keygen worldRLog cappedWorld

abbrev LogResult := Option ((Bool × QueryLog Paired.Requests) × Nat) × List RefWorld.Domain
noncomputable def logRun (T : Answers) (adversary : AdversaryP) (q : Nat) : ProbComp LogResult :=
  simulateQ (Wots.refImpl T) (SphincsSecurity.QueryCap.recorded
    (SphincsSecurity.QueryCap.run RefCharged (worldRLog T adversary) q))
def logEvent (P : Answers → QueryLog Paired.Requests → List Wots.Entry → Prop)
    (T : Answers) (run : LogResult) : Prop :=
  ∃ value remaining, run.1 = some (value,remaining) ∧ P T value.2 (Wots.traceOf T run.2)
def countEvent (P : Answers → QueryLog Paired.Requests → List Wots.Entry → Prop)
    (T : Answers) (run : RunResult (β := Bool)) : Prop :=
  ∃ value remaining, run.1 = some (value,remaining) ∧ P T value.2.1 value.2.2
noncomputable def logExperiment (adversary : AdversaryP) (q : Nat) :=
  tableAverage adversary (fun T => (fun run => (T,run)) <$> logRun T adversary q)

theorem countedProgram_prob {α : Type} (program : OracleComp CountSpec α)
    (event : CanonTable.HiddenF × α → Prop) :
    Pr[event | WPair.Counted.Generic.countedProgramRun program] =
    ∑' g,Pr[=g|($ᵗ CanonTable.HiddenF : ProbComp _)] *
      Pr[fun run=>event (g,run) | simulateQ (fixedCount g) program] := by
  unfold WPair.Counted.Generic.countedProgramRun
  rw [probEvent_bind_eq_tsum]
  apply tsum_congr
  intro g
  simp only [bind_pure_comp,probEvent_map,Function.comp_def,probOutput_uniformSample]

variable (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2^127)
  (P : Answers → QueryLog Paired.Requests → List Wots.Entry → Prop)
  (hshort : ∀ A T log entries, Wots.Ref.ShortAgree A T → P A log entries → P T log entries)
  (hmono : ∀ A log entries entries', (∀ e∈entries,e∈entries') → P A log entries → P A log entries')

include hshort hmono in
theorem shared_le_logExperiment :
    Pr[fun z => z.1.2.2.base.source.1 ≤ q ∧ ∀ generated interaction checked,
      Wots.PairedReference.GameSplit adversary (QueryRecorded.recordedTrace z.1) generated interaction checked →
        P z.2 interaction.value.2 (SigGolfCandidate.T3.Security.BPair.publicEntries checked.events) |
      PairedSeccLaw.completedExperiment adversary q hq] ≤
    Pr[fun run => logEvent P run.1 run.2 | logExperiment adversary q] := by
  refine (Paired.shared_budget_le_recorded adversary q hq (fun rec A => ∀ g i c,
    Wots.PairedReference.GameSplit adversary rec g i c →
      P A i.value.2 (SigGolfCandidate.T3.Security.BPair.publicEntries c.events))).trans ?_
  rw [Wots.PairedReference.Ref.recorded_eq_eager adversary (fun rec A => Wots.Ref.chargeSum rec.events≤q ∧
    ∀ g i c,Wots.PairedReference.GameSplit adversary rec g i c →
      P A i.value.2 (SigGolfCandidate.T3.Security.BPair.publicEntries c.events))]
  unfold Wots.Ref.eagerSide logExperiment tableAverage
  apply SigGolfCandidate.T3.Security.BPair.probEvent_bind_mono'
  intro privateTable
  apply SigGolfCandidate.T3.Security.BPair.probEvent_bind_mono'
  intro publicTable
  rw [probEvent_map,probEvent_map,Wots.Ref.fillAnswers_empty]
  exact fixed_le_worldRLog adversary q
    (Wots.eagerAnswers (Wots.PairedReference.referenceInputs adversary) privateTable publicTable) P hshort hmono

 theorem logExperiment_avg :
    Pr[fun run => logEvent P run.1 run.2 | logExperiment adversary q] =
    ∑' omega, Pr[=omega|omegaLaw (Wots.PairedReference.referenceInputs adversary)] *
      Pr[fun run => countEvent P (wA (canon_subset adversary) omega run.1) run.2 |
        WPair.Counted.Generic.countedProgramRun (cappedWorld (canon_subset adversary) omega adversary q)] := by
  unfold logExperiment
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (tableAverage_eq adversary _)]
  rw [probEvent_bind_eq_tsum]
  apply tsum_congr
  intro omega
  apply congrArg (fun x => Pr[=omega|omegaLaw (Wots.PairedReference.referenceInputs adversary)]*x)
  rw [countedProgram_prob]
  conv_lhs => rw [probEvent_bind_eq_tsum]
  apply tsum_congr
  intro g
  apply congrArg (fun x => Pr[=g|($ᵗ CanonTable.HiddenF : ProbComp _)]*x)
  simp only [bind_pure_comp,probEvent_map,Function.comp_def,probOutput_uniformSample]
  exact worldRLog_event_eq (canon_subset adversary) omega g adversary q (P (wA (canon_subset adversary) omega g))

include hshort hmono in
theorem completed_event_le_other
    (hno : ∀ A log entries,P A log entries → ¬Paired.OverflowIn A log)
    (hguess : ∀ A log entries,P A log entries → ∃ cell,Paired.GuessedIn A log entries cell) :
    Pr[fun z => z.1.2.2.base.source.1 ≤ q ∧ ∀ generated interaction checked,
      Wots.PairedReference.GameSplit adversary (QueryRecorded.recordedTrace z.1) generated interaction checked →
        P z.2 interaction.value.2 (SigGolfCandidate.T3.Security.BPair.publicEntries checked.events) |
      PairedSeccLaw.completedExperiment adversary q hq] ≤
    (((2^128-q : Nat) : ENNReal))⁻¹ * referenceOther adversary q := by
  refine (shared_le_logExperiment adversary q hq P hshort hmono).trans ?_
  rw [logExperiment_avg,referenceOther_avg,←ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro omega
  rw [← mul_assoc, mul_comm (((2^128-q : Nat) : ENNReal))⁻¹, mul_assoc]
  apply mul_le_mul' le_rfl
  have hg : q < 2^128 := lt_of_le_of_lt hq (by norm_num)
  have hw := world_event_le_other (canon_subset adversary) omega adversary q hg
    (fun g result => countEvent P (wA (canon_subset adversary) omega g) result)
    (by
      intro hidden result he
      obtain ⟨value,remaining,hr,hP⟩ := he
      exact ⟨value,remaining,hr,hno _ _ _ hP,hguess _ _ _ hP⟩)
  simpa only [worldOther,probOutput_uniformSample] using hw
end ClaudeWCT.W9.T3.Security.WPair.Paired.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Paired.Counted
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.Wots (RefSample)
open ClaudeWCT.W9.T3M.Final.Paired (AdversaryP)
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency true
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Wots.PairedReference.referenceExperiment

theorem referenceOther_le (adversary : AdversaryP) (q : Nat) : referenceOther adversary q≤q := by
  unfold referenceOther
  calc
    _ ≤ (∑' s,Wots.PairedReference.referenceExperiment adversary q s*(q:ENNReal)) := by
      apply ENNReal.tsum_le_tsum
      intro s
      rcases Classical.em (Wots.PairedReference.referenceExperiment adversary q s=0) with hs | hs
      · simp only [hs,zero_mul,le_refl]
      · apply mul_le_mul' le_rfl
        have htrace := Wots.PairedReference.reference_trace_length adversary q s ((PMF.mem_support_iff _ _).mpr hs)
        have hc : Wots.PairedReference.otherCount s ≤ s.trace.length := List.length_filter_le _ _
        exact_mod_cast hc.trans htrace
    _ = q := by rw [ENNReal.tsum_mul_right,PMF.tsum_coe,one_mul]

theorem referenceOther_ne_top (adversary : AdversaryP) (q : Nat) : referenceOther adversary q≠⊤ :=
  ne_top_of_le_ne_top (by simp) (referenceOther_le adversary q)
end ClaudeWCT.W9.T3.Security.WPair.Paired.Counted

namespace ClaudeWCT.W9.T3.Security.PairedBankLink
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.CaseC (IsDigestInput countOf lazyOf genRecord genRecord_support Agrees)
open SigGolfCandidate.T3M.SecurityExtraction (queried)
open ClaudeWCT.W9.T3M
open ClaudeWCT.Bank (Ghost FtsBankSpecL)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section GenericPotential
variable {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpecL P)
  (pay : SigGolfCandidate.T3.Cache → Digest → HashOutput → M (Option SigGolfCandidate.Research.SharedForest.Signature))
  (hrecord : ∀ published request, Prod.fst <$> S.authenticatedRecord pay published request =
    PairedOuter.FullGame.authenticatedSign published request)
include hrecord

theorem full_potential
    (hhash : ClaudeWCT.Bank.PayHashOnly pay)
    (hrho : ClaudeWCT.Bank.PayRho pay SigGolfCandidate.Research.SharedForest.Signature.rho)
    (hAvoids : ClaudeWCT.Bank.PayAvoids pay)
    (hsearch : ∀ rho message, S.search rho message 0 S.limit =
      SigGolfCandidate.Research.SharedForest.sharedDigestSearch rho message 0 WCT9.digestAttemptLimit)
    (hcovered : ∀ X N, (∀ k t, WPair.Paired.SlotCovered X N k t) → S.covered X N)
    (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q ≤ 2^127)
    (b : Bool × PairedBankState) (hb : b ∈ (S.bankExperiment pay (rest adversary) q).support)
    (A : Correctness.Answers) (hA : Agrees A (lazyOf b.2.2)) (hcount : countOf b.2.2 ≤ q)
    (gen' : FirstHit.Recorded (Digest × SigGolfCandidate.T3.Cache))
    (int' : FirstHit.Recorded (Option Final.Paired.ForgeryP × QueryLog Final.Paired.Requests))
    (chk' : FirstHit.Recorded Bool)
    (hsplit : Wots.PairedReference.GameSplit adversary ⟨b.1,b.2.2.events,lazyOf b.2.2⟩ gen' int' chk')
    (hlen : int'.value.2.length ≤ S.horizon)
    (input : HashInput) (N : HashOutput) (hdig : IsDigestInput input)
    (prior : LazyPrivate.State)
    (hev : (⟨prior,.inl (.inr input),N⟩ : FirstHit.QueryEvent) ∈ b.2.2.events)
    (hnot : ∀ entry ∈ int'.value.2, (.inl (.inr input) : SigGolfCandidate.T3.Spec.Domain) ∉
      queried A (PairedOuter.FullGame.authenticatedSign gen'.value.2 entry.1))
    (hadm : S.admissible N=true)
    (hfull : ∀ k t, WPair.Paired.SlotCovered (WPair.Paired.loggedOutputs A int'.value.2) N k t) :
    1 ≤ S.potential q b.2 := by
  obtain ⟨generated,hg,int0,hint0,⟨tail,htail⟩,hlog,hinv⟩ :=
    bank_actual S pay SigGolfCandidate.Research.SharedForest.Signature.rho hrecord
      hhash hrho hAvoids adversary q b hb
  obtain ⟨hgen,hint⟩ := split_unique adversary _ (genRecord generated)
    (genRecord_support generated hg) int0 hint0 tail htail gen' int' chk' hsplit
  subst hgen hint
  have halive : b.2.1.dead=false := hinv.alive S pay
    SigGolfCandidate.Research.SharedForest.Signature.rho (by rwa [hlog])
  have hRsupp : (⟨b.1,b.2.2.events,lazyOf b.2.2⟩ : FirstHit.Recorded Bool) ∈
      support (FirstHit.record (PairedOuter.GameWith.idealGame PairedOuter.PaddedGame.checker adversary) (∅,∅)) := by
    have hm : (b.1,b.2.2) ∈ ((fun r : PairedOuter.PaddedGame.TraceResult => (r.1,r.2.2)) <$>
        PairedOuter.PaddedGame.tracedExperiment adversary q hq).support := by
      rw [←bank_traced S pay hrecord adversary q hq,PMF.monad_map_eq_map,PMF.mem_support_map_iff]
      exact ⟨b,hb,rfl⟩
    rw [PMF.monad_map_eq_map,PMF.mem_support_map_iff] at hm
    obtain ⟨r,hr,hre⟩ := hm
    have := traced_record_support adversary q hq r hr
    have hrt : QueryRecorded.recordedTrace r = ⟨b.1,b.2.2.events,lazyOf b.2.2⟩ := by
      unfold QueryRecorded.recordedTrace QueryRecorded.recorded
      rw [hre]
      rfl
    rwa [hrt] at this
  obtain ⟨first,hfirst,hfresh⟩ := FirstHit.first_public_occurrence _ _ hRsupp prior input N hev
  have htarget : N ∈ b.2.1.targets := by
    rcases hinv.events _ hfirst with hk | hp
    · exfalso
      have hkg := FirstHit.recorded_inputs keygen SourceReplay.keygen_hashOnly (∅,∅) (genRecord generated)
        (genRecord_support generated hg) (SourceReplay.answers (genRecord generated).state)
        (fun input answer hk => SourceReplay.answers_known _ input answer hk)
      have hmem : (.inl (.inr input) : SigGolfCandidate.T3.Spec.Domain) ∈
          SourceReplay.queried (SourceReplay.answers (genRecord generated).state) keygen := by
        rw [←hkg]
        exact List.mem_map_of_mem hk
      obtain ⟨rho,message,counter,rfl⟩ := hdig
      exact SigGolfCandidate.T3.Security.CaseC.queried_notDigest_keygen _ _ hmem
        (BPB.hdrMarker_digestInput rho message counter)
    · rcases hp input N rfl hdig hfresh with ht | hb' | hs
      · exact ht
      · exfalso
        change q<countOf b.2.2 at hb'
        omega
      · exfalso
        obtain ⟨entry,hentry,hquery⟩ := hs
        have hqA := hquery A hA
        rw [bank_source S pay hrecord] at hqA
        change (.inl (.inr input) : SigGolfCandidate.T3.Spec.Domain) ∈
          queried A (PairedOuter.FullGame.authenticatedSign generated.1.2 entry.1) at hqA
        rw [hlog] at hentry
        exact hnot entry hentry hqA
  have hcov : S.covered b.2.1.exposures N := by
    apply hcovered
    intro k t
    obtain ⟨out,hout,h1,h2,h3⟩ := hfull k t
    obtain ⟨entry,hentry,signature,hsig,hsigned⟩ := WPair.Paired.mem_loggedOutputs.mp hout
    rw [←hlog] at hentry
    unfold WPair.Paired.signedOutput at hsigned
    cases hs : evalWithAnswerFn A
        (SigGolfCandidate.Research.SharedForest.sharedDigestSearch signature.rho entry.1.message 0 WCT9.digestAttemptLimit) with
    | none => rw [hs] at hsigned; cases hsigned
    | some found =>
        rw [hs] at hsigned
        simp only [Option.map_some,Option.some.injEq] at hsigned
        rcases found with ⟨counter,out'⟩
        simp only at hsigned
        subst hsigned
        have hs' : evalWithAnswerFn A (S.search signature.rho entry.1.message 0 S.limit)=some (counter,out') := by
          rw [hsearch]
          exact hs
        exact ⟨out',ClaudeWCT.Bank.FtsBankSpecL.BankInv.logged_exposed S pay
          SigGolfCandidate.Research.SharedForest.Signature.rho hinv halive entry hentry signature hsig A hA counter out' hs',h1,h2,h3⟩
  exact S.potential_win q b.2 halive hcount (Or.inr ⟨N,htarget,hadm,hcov⟩)
end GenericPotential
end ClaudeWCT.W9.T3.Security.PairedBankLink

namespace ClaudeWCT.W9.T3.Security.PairedBankLink
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.CaseC (IsDigestInput countOf lazyOf genRecord genRecord_support Agrees)
open SigGolfCandidate.T3M.SecurityExtraction (queried)
open ClaudeWCT.W9.T3M
open ClaudeWCT.Bank (Ghost FtsBankSpecL)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section GenericPotential
variable {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpecL P)
  (pay : SigGolfCandidate.T3.Cache → Digest → HashOutput → M (Option SigGolfCandidate.Research.SharedForest.Signature))
  (hrecord : ∀ published request, Prod.fst <$> S.authenticatedRecord pay published request =
    PairedOuter.FullGame.authenticatedSign published request)
include hrecord

theorem full_target_covered
    (hhash : ClaudeWCT.Bank.PayHashOnly pay)
    (hrho : ClaudeWCT.Bank.PayRho pay SigGolfCandidate.Research.SharedForest.Signature.rho)
    (hAvoids : ClaudeWCT.Bank.PayAvoids pay)
    (hsearch : ∀ rho message, S.search rho message 0 S.limit =
      SigGolfCandidate.Research.SharedForest.sharedDigestSearch rho message 0 WCT9.digestAttemptLimit)
    (hcovered : ∀ X N, (∀ k t, WPair.Paired.SlotCovered X N k t) → S.covered X N)
    (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q ≤ 2^127)
    (b : Bool × PairedBankState) (hb : b ∈ (S.bankExperiment pay (rest adversary) q).support)
    (A : Correctness.Answers) (hA : Agrees A (lazyOf b.2.2)) (hcount : countOf b.2.2 ≤ q)
    (gen' : FirstHit.Recorded (Digest × SigGolfCandidate.T3.Cache))
    (int' : FirstHit.Recorded (Option Final.Paired.ForgeryP × QueryLog Final.Paired.Requests))
    (chk' : FirstHit.Recorded Bool)
    (hsplit : Wots.PairedReference.GameSplit adversary ⟨b.1,b.2.2.events,lazyOf b.2.2⟩ gen' int' chk')
    (hlen : int'.value.2.length ≤ S.horizon)
    (input : HashInput) (N : HashOutput) (hdig : IsDigestInput input)
    (prior : LazyPrivate.State)
    (hev : (⟨prior,.inl (.inr input),N⟩ : FirstHit.QueryEvent) ∈ b.2.2.events)
    (hnot : ∀ entry ∈ int'.value.2, (.inl (.inr input) : SigGolfCandidate.T3.Spec.Domain) ∉
      queried A (PairedOuter.FullGame.authenticatedSign gen'.value.2 entry.1))
    (hadm : S.admissible N=true)
    (hfull : ∀ k t, WPair.Paired.SlotCovered (WPair.Paired.loggedOutputs A int'.value.2) N k t) :
    b.2.1.dead=false ∧ N∈b.2.1.targets ∧ S.covered b.2.1.exposures N := by
  obtain ⟨generated,hg,int0,hint0,⟨tail,htail⟩,hlog,hinv⟩ :=
    bank_actual S pay SigGolfCandidate.Research.SharedForest.Signature.rho hrecord
      hhash hrho hAvoids adversary q b hb
  obtain ⟨hgen,hint⟩ := split_unique adversary _ (genRecord generated)
    (genRecord_support generated hg) int0 hint0 tail htail gen' int' chk' hsplit
  subst hgen hint
  have halive : b.2.1.dead=false := hinv.alive S pay
    SigGolfCandidate.Research.SharedForest.Signature.rho (by rwa [hlog])
  have hRsupp : (⟨b.1,b.2.2.events,lazyOf b.2.2⟩ : FirstHit.Recorded Bool) ∈
      support (FirstHit.record (PairedOuter.GameWith.idealGame PairedOuter.PaddedGame.checker adversary) (∅,∅)) := by
    have hm : (b.1,b.2.2) ∈ ((fun r : PairedOuter.PaddedGame.TraceResult => (r.1,r.2.2)) <$>
        PairedOuter.PaddedGame.tracedExperiment adversary q hq).support := by
      rw [←bank_traced S pay hrecord adversary q hq,PMF.monad_map_eq_map,PMF.mem_support_map_iff]
      exact ⟨b,hb,rfl⟩
    rw [PMF.monad_map_eq_map,PMF.mem_support_map_iff] at hm
    obtain ⟨r,hr,hre⟩ := hm
    have := traced_record_support adversary q hq r hr
    have hrt : QueryRecorded.recordedTrace r = ⟨b.1,b.2.2.events,lazyOf b.2.2⟩ := by
      unfold QueryRecorded.recordedTrace QueryRecorded.recorded
      rw [hre]
      rfl
    rwa [hrt] at this
  obtain ⟨first,hfirst,hfresh⟩ := FirstHit.first_public_occurrence _ _ hRsupp prior input N hev
  have htarget : N ∈ b.2.1.targets := by
    rcases hinv.events _ hfirst with hk | hp
    · exfalso
      have hkg := FirstHit.recorded_inputs keygen SourceReplay.keygen_hashOnly (∅,∅) (genRecord generated)
        (genRecord_support generated hg) (SourceReplay.answers (genRecord generated).state)
        (fun input answer hk => SourceReplay.answers_known _ input answer hk)
      have hmem : (.inl (.inr input) : SigGolfCandidate.T3.Spec.Domain) ∈
          SourceReplay.queried (SourceReplay.answers (genRecord generated).state) keygen := by
        rw [←hkg]
        exact List.mem_map_of_mem hk
      obtain ⟨rho,message,counter,rfl⟩ := hdig
      exact SigGolfCandidate.T3.Security.CaseC.queried_notDigest_keygen _ _ hmem
        (BPB.hdrMarker_digestInput rho message counter)
    · rcases hp input N rfl hdig hfresh with ht | hb' | hs
      · exact ht
      · exfalso
        change q<countOf b.2.2 at hb'
        omega
      · exfalso
        obtain ⟨entry,hentry,hquery⟩ := hs
        have hqA := hquery A hA
        rw [bank_source S pay hrecord] at hqA
        change (.inl (.inr input) : SigGolfCandidate.T3.Spec.Domain) ∈
          queried A (PairedOuter.FullGame.authenticatedSign generated.1.2 entry.1) at hqA
        rw [hlog] at hentry
        exact hnot entry hentry hqA
  have hcov : S.covered b.2.1.exposures N := by
    apply hcovered
    intro k t
    obtain ⟨out,hout,h1,h2,h3⟩ := hfull k t
    obtain ⟨entry,hentry,signature,hsig,hsigned⟩ := WPair.Paired.mem_loggedOutputs.mp hout
    rw [←hlog] at hentry
    unfold WPair.Paired.signedOutput at hsigned
    cases hs : evalWithAnswerFn A
        (SigGolfCandidate.Research.SharedForest.sharedDigestSearch signature.rho entry.1.message 0 WCT9.digestAttemptLimit) with
    | none => rw [hs] at hsigned; cases hsigned
    | some found =>
        rw [hs] at hsigned
        simp only [Option.map_some,Option.some.injEq] at hsigned
        rcases found with ⟨counter,out'⟩
        simp only at hsigned
        subst hsigned
        have hs' : evalWithAnswerFn A (S.search signature.rho entry.1.message 0 S.limit)=some (counter,out') := by
          rw [hsearch]
          exact hs
        exact ⟨out',ClaudeWCT.Bank.FtsBankSpecL.BankInv.logged_exposed S pay
          SigGolfCandidate.Research.SharedForest.Signature.rho hinv halive entry hentry signature hsig A hA counter out' hs',h1,h2,h3⟩
  exact ⟨halive,htarget,hcov⟩
end GenericPotential
end ClaudeWCT.W9.T3.Security.PairedBankLink
end
-- ==== merged from T3_Secc_WotsContacts ====
section

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec fixedImpl evaluate IsPrefixQuery observedRun
  realRun idealRun lazyRun TwoEdgeEvent Contact)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
end SigGolfCandidate.T3.Security.Wots
end
-- ==== merged from T3_Secc_WotsRestartBase ====
section

section
namespace SphincsSecurity.QueryCap
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {Index Memory Result : Type} {spec : OracleSpec Index}
  (selected : Index → Prop) [DecidablePred selected]
end SphincsSecurity.QueryCap
end
section
namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result Memory : Type}
  (auxiliary : State → QueryImpl auxSpec PMF)
  (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result)
  (cost : Result → Nat) (budget : Nat)
  (hcharge : ∀ endpoint result, result ∈ support (QueryCap.counted IsPrefixQuery (computation endpoint)) → result.2 ≤ cost result.1)
  (hreal : ∀ result ∈ (realRun auxiliary computation (fun _ _ => none)).support, cost result.2.1 ≤ budget)
  (hsmall : budget < Fintype.card State)
include hcharge hreal hsmall
end SphincsSecurity.Concrete.PartialChainEndpoint
end
section
namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
private theorem scaled_expectation_le {Result : Type} (law : PMF Result) (factor : ENNReal)
    (left right : Result → ENNReal) (h : ∀ result ∈ law.support, factor * left result ≤ right result) :
    factor * (∑' result, law result * left result) ≤ ∑' result, law result * right result := by
  rw [← expectation_scale]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ law.support
  · exact mul_le_mul' le_rfl (h result hr)
  · have hz : law result = 0 := not_not.mp hr
    simp only [hz, zero_mul, le_refl]
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Checkpoint Result : Type}
  (auxiliary : State → QueryImpl auxSpec PMF)
  (before : State → OracleComp (auxSpec + PrefixSpec n State) Checkpoint)
  (after : State → Checkpoint × (Fin n → State → Option State) → OracleComp (auxSpec + PrefixSpec n State) Result)
  (observed : Fin n → State → Option State)
  (marked : State → Checkpoint × (Fin n → State → Option State) → Prop)
theorem realCheckpointRun_mark_probability :
    Pr[fun result => marked result.1 result.2.1 | realCheckpointRun auxiliary before after observed] =
      Pr[fun result => marked result.1 result.2 | realRun auxiliary before observed] := by
  have h := congrArg (fun law : PMF (State × (Checkpoint × (Fin n → State → Option State))) =>
    Pr[fun result => marked result.1 result.2 | law]) (realCheckpointRun_before auxiliary before after observed)
  simpa only [← PMF.monad_map_eq_map, probEvent_map, Function.comp_def] using h
theorem realCheckpointRun_contact_charge (budget : Nat)
    (hmarked : ∀ endpoint middle, marked endpoint middle → ¬Contact middle.2 endpoint)
    (hbudget : ∀ endpoint, ∀ middle ∈ (lazyRun (auxiliary endpoint) (before endpoint) observed).support,
      marked endpoint middle → ∀ result ∈ (lazyRun (auxiliary endpoint)
        (QueryCap.counted IsPrefixQuery (after endpoint middle)) middle.2).support, queryCount result.2 ≤ budget) :
    (1 - (budget : ENNReal) / Fintype.card State) * ((Fintype.card State : ENNReal) *
      Pr[fun result => marked result.1 result.2.1 ∧ Contact result.2.2.2 result.1 |
        realCheckpointRun auxiliary before after observed]) ≤
      ∑' result, realCheckpointRun auxiliary before after observed result *
        (((queryCount result.2.1.2 + 2 * result.2.2.1.2 : Nat) : ENNReal) * if marked result.1 result.2.1 then 1 else 0) := by
  rw [show Pr[fun result => marked result.1 result.2.1 ∧ Contact result.2.2.2 result.1 |
      realCheckpointRun auxiliary before after observed] =
      (∑' result, realCheckpointRun auxiliary before after observed result *
        if marked result.1 result.2.1 ∧ Contact result.2.2.2 result.1 then 1 else 0) by
          simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply, mul_ite, mul_one, mul_zero]]
  rw [realCheckpointRun_density, realCheckpointRun_expectation, ← mul_assoc]
  apply scaled_expectation_le
  intro endpoint _
  apply scaled_expectation_le
  intro middle hmiddle
  by_cases hm : marked endpoint middle
  · simp only [hm, true_and, if_true, mul_one]
    simpa only [mul_assoc] using run_contact_charge_transfer (auxiliary endpoint) (after endpoint middle) middle.2 endpoint
      (hmarked endpoint middle hm) budget (hbudget endpoint middle hmiddle hm)
  · simp only [hm, false_and, if_false, mul_zero, tsum_zero, le_refl]
theorem realCheckpointRun_contact_le_mark (budget : Nat)
    (hmarked : ∀ endpoint middle, marked endpoint middle → ¬Contact middle.2 endpoint)
    (hbudget : ∀ endpoint, ∀ middle ∈ (lazyRun (auxiliary endpoint) (before endpoint) observed).support,
      marked endpoint middle → ∀ result ∈ (lazyRun (auxiliary endpoint)
        (QueryCap.counted IsPrefixQuery (after endpoint middle)) middle.2).support, queryCount result.2 ≤ budget)
    (hcost : ∀ result ∈ (realCheckpointRun auxiliary before after observed).support,
      marked result.1 result.2.1 → queryCount result.2.1.2 + result.2.2.1.2 ≤ budget) :
    (1 - (budget : ENNReal) / Fintype.card State) * ((Fintype.card State : ENNReal) *
      Pr[fun result => marked result.1 result.2.1 ∧ Contact result.2.2.2 result.1 |
        realCheckpointRun auxiliary before after observed]) ≤
      (2 * budget : Nat) * Pr[fun result => marked result.1 result.2 | realRun auxiliary before observed] := by
  apply (realCheckpointRun_contact_charge auxiliary before after observed marked budget hmarked hbudget).trans
  calc
    _ ≤ ∑' result, realCheckpointRun auxiliary before after observed result *
        (((2 * budget : Nat) : ENNReal) * if marked result.1 result.2.1 then 1 else 0) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ (realCheckpointRun auxiliary before after observed).support
      · apply mul_le_mul' le_rfl
        by_cases hm : marked result.1 result.2.1
        · simp only [if_pos hm, mul_one]
          have hc := hcost result hr hm
          exact_mod_cast (show queryCount result.2.1.2 + 2 * result.2.2.1.2 ≤ 2 * budget by omega)
        · simp only [if_neg hm, mul_zero, le_refl]
      · have hz : realCheckpointRun auxiliary before after observed result = 0 := not_not.mp hr
        simp only [hz, zero_mul, le_refl]
    _ = _ := by
      rw [expectation_scale, ← realCheckpointRun_mark_probability auxiliary before after observed marked]
      simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply, mul_ite, mul_one, mul_zero]
end SphincsSecurity.Concrete.PartialChainEndpoint
end
section
namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Checkpoint Result Output : Type}
omit [Fintype State] [Nonempty State] in
theorem observedRun_bind (auxiliary : QueryImpl auxSpec PMF) (tables : Fin n → State → State)
    (before : OracleComp (auxSpec + PrefixSpec n State) Checkpoint)
    (after : Checkpoint → OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State) :
    observedRun auxiliary tables (before >>= after) observed =
      (observedRun auxiliary tables before observed).bind (fun middle => observedRun auxiliary tables (after middle.1) middle.2) := by
  simp only [observedRun, simulateQ_bind, StateT.run_bind, PMF.monad_bind_eq_bind]
omit [Fintype State] [Nonempty State] in
theorem checkpointObservedRun_project (auxiliary : QueryImpl auxSpec PMF) (tables : Fin n → State → State)
    (before : OracleComp (auxSpec + PrefixSpec n State) Checkpoint)
    (after : Checkpoint → OracleComp (auxSpec + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) (project : Checkpoint → Result → Output) :
    (checkpointObservedRun auxiliary tables before (fun middle => after middle.1) observed).map
      (fun result => (project result.1.1 result.2.1.1, result.2.2)) =
    observedRun auxiliary tables (do let middle ← before; let result ← after middle; pure (project middle result)) observed := by
  simp only [checkpointObservedRun, PMF.map_bind, PMF.map_comp, Function.comp_def,
    observedRun_bind, bind_pure_comp, observedRun_map]
  apply congrArg (observedRun auxiliary tables before observed).bind
  funext middle
  rw [← observedRun_map auxiliary tables (QueryCap.counted IsPrefixQuery (after middle.1))
    (fun result => project middle.1 result.1) middle.2]
  rw [← Functor.map_map, QueryCap.counted_forget, observedRun_map]
theorem realCheckpointRun_project (auxiliary : State → QueryImpl auxSpec PMF)
    (before : State → OracleComp (auxSpec + PrefixSpec n State) Checkpoint)
    (after : State → Checkpoint → OracleComp (auxSpec + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) (project : State → Checkpoint → Result → Output) :
    (realCheckpointRun auxiliary before (fun endpoint middle => after endpoint middle.1) observed).map
      (fun result => (result.1, project result.1 result.2.1.1 result.2.2.1.1, result.2.2.2)) =
    realRun auxiliary (fun endpoint => do
      let middle ← before endpoint
      let result ← after endpoint middle
      pure (project endpoint middle result)) observed := by
  simp only [realCheckpointRun, realRun, PMF.map_bind, PMF.map_comp, Function.comp_def]
  apply congrArg (EndpointPreimageDensity.real (completeTables observed) evaluate).bind
  funext pair
  have h := congrArg (fun law => law.map (fun result => (pair.2, result)))
    (checkpointObservedRun_project (auxiliary pair.2) pair.1 (before pair.2) (after pair.2) observed (project pair.2))
  simpa only [PMF.map_comp, Function.comp_def] using h
end SphincsSecurity.Concrete.PartialChainEndpoint
end
section
namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec fixedImpl evaluate IsPrefixQuery observedRun
  observedImpl lazyImpl record realRun idealRun lazyRun TwoEdgeEvent Contact queryCount)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace PrefixGame
def entryOf : (query : RefWorld.Domain) → RefWorld.Range query → List Entry
  | .inl (.inr input), answer => [(input, (answer : HashOutput))]
  | .inl (.inl _), _ => []
  | .inr _, _ => []
def stepTrace (query : RefWorld.Domain) (answer : RefWorld.Range query) (memory : List Entry) : List Entry :=
  memory ++ entryOf query answer
def refAnswer (T : Answers) : (query : RefWorld.Domain) → RefWorld.Range query
  | .inl query => T (.inl query)
  | .inr _ => ()
theorem traceOf_cons (T : Answers) (query : RefWorld.Domain) (qs : List RefWorld.Domain) :
    traceOf T (query :: qs) = entryOf query (refAnswer T query) ++ traceOf T qs := by
  rcases query with (n | input) | u <;> rfl
theorem entryOf_refImpl (T : Answers) (query : RefWorld.Domain) (answer : RefWorld.Range query)
    (h : answer ∈ support (refImpl T query)) : entryOf query answer = entryOf query (refAnswer T query) := by
  rcases query with (n | input) | u
  · rfl
  · simp only [refImpl, mem_support_pure_iff] at h
    subst h
    rfl
  · rfl
theorem entryOf_length_le (query : RefWorld.Domain) (answer : RefWorld.Range query) :
    (entryOf query answer).length ≤ 1 := by
  rcases query with (n | input) | u <;> simp [entryOf]
variable {β : Type}
noncomputable def pausedFull (stop : List Entry → Prop) (G : OracleComp RefWorld β) (memory : List Entry) :
    OracleComp RefWorld (List Entry × (β × List RefWorld.Domain)) := do
  let paused ← SphincsSecurity.QueryPause.run stop stepTrace (SphincsSecurity.QueryCap.recorded G) memory
  let result ← paused.2
  pure (paused.1, result)
theorem pausedFull_snd (stop : List Entry → Prop) (G : OracleComp RefWorld β) (memory : List Entry) :
    Prod.snd <$> pausedFull stop G memory = SphincsSecurity.QueryCap.recorded G := by
  unfold pausedFull
  simp only [map_bind, map_pure]
  conv_rhs => rw [← SphincsSecurity.QueryPause.resume stop stepTrace (SphincsSecurity.QueryCap.recorded G) memory]
  congr 1
  funext paused
  simp only [bind_pure]
theorem run_map {Index Memory α γ : Type} {spec : OracleSpec Index} (stop : Memory → Prop) [DecidablePred stop]
    (step : (input : spec.Domain) → spec.Range input → Memory → Memory) (f : α → γ)
    (computation : OracleComp spec α) (memory : Memory) :
    SphincsSecurity.QueryPause.run stop step (f <$> computation) memory =
      (fun paused => (paused.1, f <$> paused.2)) <$> SphincsSecurity.QueryPause.run stop step computation memory := by
  induction computation using OracleComp.inductionOn generalizing memory with
  | pure value =>
      simp only [map_pure, SphincsSecurity.QueryPause.run_pure]
  | query_bind input next ih =>
      rw [map_bind, SphincsSecurity.QueryPause.run_query_bind, SphincsSecurity.QueryPause.run_query_bind]
      by_cases hs : stop memory
      · simp only [if_pos hs, map_pure, map_bind]
      · simp only [if_neg hs, map_bind, ih]
theorem pausedFull_query_bind (stop : List Entry → Prop) (input : RefWorld.Domain)
    (next : RefWorld.Range input → OracleComp RefWorld β) (memory : List Entry) :
    pausedFull stop (liftM (RefWorld.query input) >>= next) memory =
      if stop memory then
        (fun result => (memory, result)) <$> SphincsSecurity.QueryCap.recorded (liftM (RefWorld.query input) >>= next)
      else liftM (RefWorld.query input) >>= fun answer =>
        (fun paused => (paused.1, (paused.2.1, input :: paused.2.2))) <$>
          pausedFull stop (next answer) (stepTrace input answer memory) := by
  unfold pausedFull
  rw [SphincsSecurity.QueryCap.recorded_query_bind, SphincsSecurity.QueryPause.run_query_bind]
  by_cases hs : stop memory
  · rw [if_pos hs, if_pos hs, pure_bind, ← SphincsSecurity.QueryCap.recorded_query_bind]
    simp only [bind_pure_comp]
  · rw [if_neg hs, if_neg hs, bind_assoc]
    congr 1
    funext answer
    have hmap : (SphincsSecurity.QueryCap.recorded (next answer) >>= fun result =>
        (pure (result.1, input :: result.2) : OracleComp RefWorld _)) =
        (fun result => (result.1, input :: result.2)) <$> SphincsSecurity.QueryCap.recorded (next answer) := by
      simp only [bind_pure_comp]
    rw [hmap, run_map]
    simp only [map_bind, bind_map_left, map_pure]
theorem paused_structure (T : Answers) (stop : List Entry → Prop) (G : OracleComp RefWorld β) :
    ∀ (memory : List Entry) (result : List Entry × (β × List RefWorld.Domain)),
      result ∈ support (simulateQ (refImpl T) (pausedFull stop G memory)) →
        memory.length ≤ result.1.length ∧
        result.1 = (memory ++ traceOf T result.2.2).take result.1.length ∧
        (∀ j, memory.length ≤ j → j < result.1.length → ¬stop ((memory ++ traceOf T result.2.2).take j)) ∧
        (stop result.1 ∨ result.1 = memory ++ traceOf T result.2.2) := by
  induction G using OracleComp.inductionOn with
  | pure value =>
      intro memory result hr
      simp only [pausedFull, SphincsSecurity.QueryCap.recorded_pure, SphincsSecurity.QueryPause.run_pure, pure_bind,
        simulateQ_pure, mem_support_pure_iff] at hr
      subst hr
      refine ⟨le_refl _, ?_, fun j h1 h2 => by simp only at h2; omega, Or.inr ?_⟩
      · simp
      · show memory = memory ++ traceOf T []
        rw [show traceOf T [] = [] from rfl, List.append_nil]
  | query_bind input next ih =>
      intro memory result hr
      rw [pausedFull_query_bind] at hr
      by_cases hs : stop memory
      · rw [if_pos hs] at hr
        rw [simulateQ_map, support_map] at hr
        obtain ⟨tail, -, rfl⟩ := hr
        refine ⟨le_refl _, ?_, fun j h1 h2 => by simp only at h2; omega, Or.inl hs⟩
        show memory = List.take memory.length (memory ++ _)
        rw [List.take_left' rfl]
      · rw [if_neg hs, simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at hr
        obtain ⟨answer, hanswer, hr⟩ := hr
        rw [simulateQ_map, support_map] at hr
        obtain ⟨paused, hpaused, rfl⟩ := hr
        obtain ⟨h1, h2, h3, h4⟩ := ih answer (stepTrace input answer memory) paused hpaused
        have hentry := entryOf_refImpl T input answer hanswer
        have htrace : stepTrace input answer memory ++ traceOf T paused.2.2 =
            memory ++ traceOf T (input :: paused.2.2) := by
          rw [traceOf_cons, stepTrace, hentry, List.append_assoc]
        rw [htrace] at h2 h3 h4
        have hlen : (stepTrace input answer memory).length ≤ memory.length + 1 := by
          have := entryOf_length_le input answer
          simp only [stepTrace, List.length_append]
          omega
        have hlen' : memory.length ≤ (stepTrace input answer memory).length := by
          simp only [stepTrace, List.length_append]
          omega
        refine ⟨le_trans hlen' h1, h2, ?_, h4⟩
        intro j hj1 hj2
        by_cases hj : (stepTrace input answer memory).length ≤ j
        · exact h3 j hj hj2
        · have hjm : j = memory.length := by omega
          rw [hjm, List.take_left' rfl]
          exact hs
variable {adversary : AdversaryP}
theorem lazyRun_bind {d : Nat} {α γ : Type} (first : OracleComp (SeedSpec d) α) (next : α → OracleComp (SeedSpec d) γ)
    (observed : Fin d → Digest → Option Digest) :
    lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl (first >>= next) observed =
      (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl first observed).bind fun r =>
        lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl (next r.1) r.2 := by
  simp only [lazyRun, simulateQ_bind, StateT.run_bind, PMF.monad_bind_eq_bind]
def RowsInv (a : ChainAddr) {d : Nat} (memory : List Entry) (observed : Fin d → Digest → Option Digest) : Prop :=
  ∀ (i : Fin d) (v w : Digest), observed i v = some w ↔ ∃ answer, (chainRow a i v, answer) ∈ memory ∧ low answer = w
theorem rowsInv_nil (a : ChainAddr) (d : Nat) : RowsInv a (d := d) [] (fun _ _ => none) := by
  intro i v w
  simp
end PrefixGame
end SigGolfCandidate.T3.Security.Wots
end
end
-- ==== merged from T3_Secc_WotsRestart ====
section

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec fixedImpl evaluate IsPrefixQuery observedRun
  observedImpl lazyImpl record realRun idealRun lazyRun TwoEdgeEvent Contact queryCount realCheckpointRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace PrefixGame
variable {adversary : AdversaryP}
theorem first_stop_iff {trace memory : List Entry} (S C : List Entry → Prop)
    (hm : memory = trace.take memory.length) (hb : ∀ j, j < memory.length → ¬S (trace.take j))
    (hc : S memory ∨ memory = trace) (hC : ∀ j k, j ≤ k → C (trace.take j) → C (trace.take k)) :
    (∃ k, S (trace.take k) ∧ ¬C (trace.take k) ∧ C trace) ↔ (S memory ∧ ¬C memory ∧ C trace) := by
  constructor
  · rintro ⟨k, hs, hnc, hct⟩
    have hk : memory.length ≤ k := by
      by_contra h
      exact hb k (by omega) hs
    have hnm : ¬C memory := fun hcm => hnc (hC _ _ hk (hm ▸ hcm))
    refine ⟨?_, hnm, hct⟩
    rcases hc with hc | hc
    · exact hc
    · exact absurd (hc ▸ hct) hnm
  · rintro ⟨hs, hnc, hct⟩
    exact ⟨memory.length, hm ▸ hs, hm ▸ hnc, hct⟩
theorem first_stop_exists_iff {trace memory : List Entry} (S : List Entry → Prop)
    (hm : memory = trace.take memory.length) (hb : ∀ j, j < memory.length → ¬S (trace.take j))
    (hc : S memory ∨ memory = trace) : (∃ k, S (trace.take k)) ↔ S memory := by
  constructor
  · rintro ⟨k, hs⟩
    have hk : memory.length ≤ k := by
      by_contra h
      exact hb k (by omega) hs
    rcases hc with hc | hc
    · exact hc
    · have : trace.take k = memory := by
        rw [hc]; exact List.take_of_length_le (by rw [← hc]; exact hk)
      exact this ▸ hs
  · intro hs
    exact ⟨memory.length, hm ▸ hs⟩
end PrefixGame
namespace PrefixGame
variable {adversary : AdversaryP}
end PrefixGame
end SigGolfCandidate.T3.Security.Wots
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsLeafLift ====
section

/-! # The seed-test reduction over the rest tables (campaign X1 stage B, step B3)

`frozen_le_mix` / `mix_le_frozen`: for a lower source chain `a`, the frozen mixture (the reference game) and the
`realRun` mixture (independent seed) give the same probability to every depth-uniform event that is blind to `a`'s
leaf data, up to `errA a`, the rest-table average of `errR`. -/

namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
noncomputable local instance instFintypeCoordinate_wotsLeafLift : Fintype Coordinate := coordinateFintype
namespace Leaf
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open ClaudeWCT.Arith.SideChannel (TSpec Free seedsR)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun)
variable {adversary : AdversaryP}

theorem prob_bind {α β : Type} (P : PMF α) (Q : α → PMF β) (E : β → Prop) :
    Pr[E | P.bind Q] = ∑' x, P x * Pr[E | Q x] := by
  rw [← PMF.monad_bind_eq_bind, probEvent_bind_eq_tsum]
  simp only [PMF.probOutput_eq_apply]

/-- The chain `a` as an unrevealed coordinate of its leaf (depth `≥ 1`). -/
def selfF {a : ChainAddr} (hac : a.chain < chainCount a.key.lay) (R : RefTables adversary)
    (hd1 : 1 ≤ restDepth a R) : Free (revSet a.key R) :=
  ⟨⟨a.chain, hac⟩, by
    unfold revSet
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [restDepth_eq] at hd1
    intro h
    rw [show (⟨a.key, (⟨a.chain, hac⟩ : Fin (chainCount a.key.lay)).val⟩ : ChainAddr) = a from rfl] at h
    omega⟩

/-- Per rest table error (zero at depth `0`). -/
noncomputable def errAR {Res : Type} (a : ChainAddr) (hac : a.chain < chainCount a.key.lay)
    (GD : Answers → OracleComp RefWorld Res) (q : ℕ) (R : RefTables adversary) : ℝ≥0∞ :=
  if hd1 : 1 ≤ restDepth a R then ENNReal.ofReal (errR (a := a) R GD (selfF hac R hd1) q) else 0

theorem restLaw_resampleL_tsum {L : LeafAddr} (hL : L.leaf < 2 ^ 24) (Φ : RefTables adversary → ℝ≥0∞) :
    ∑' R, restLaw adversary R * Φ R =
      ∑' R, restLaw adversary R * ∑' y, PMF.uniformOfFintype (LeafData L) y * Φ (ovL L R y) := by
  have h := restLaw_resampleL (adversary := adversary) hL (fun R => PMF.pure R)
  simp only [PMF.bind_pure] at h
  conv_lhs => rw [h]
  rw [SphincsSecurity.Concrete.PartialChainEndpoint.expectation_bind]
  congr 1
  funext R
  congr 1
  rw [show (PMF.uniformOfFintype (LeafData L)).bind (fun y => PMF.pure (ovL L R y)) =
    (PMF.uniformOfFintype (LeafData L)).map (ovL L R) from rfl,
    SphincsSecurity.Concrete.PartialChainEndpoint.expectation_map]

section Lift
variable {a : ChainAddr} (hac : a.chain < chainCount a.key.lay) (hLleaf : a.key.leaf < 2 ^ 24)
  {Res : Type} (GD : Answers → OracleComp RefWorld Res) (hG : ∀ T T', LeafCongr a.key T T' → GD T' = GD T)
  (q : ℕ) (hGq : ∀ T, OracleComp.IsQueryBoundP (GD T) RefCharged q)
  (F : (d : ℕ) → RefTables adversary → Digest × (Res × TObs d) → Prop)
  (hF : ∀ (R : RefTables adversary) (p : PData a.key (restDepth a R)) (K K' : Fin (WCT9.famCount a.key.lay) → Digest),
    seedsR (ptL a.key) (revSet a.key R) K = seedsR (ptL a.key) (revSet a.key R) K' →
      F (restDepth a R) (ovL a.key R (K, progF p.1.1 p.1.2 K)) =
        F (restDepth a R) (ovL a.key R (K', progF p.1.1 p.1.2 K')))
  (hF0 : ∀ R z, ¬F 0 R z)

theorem prob_zero_of_depth {R : RefTables adversary} (h0 : restDepth a R = 0) {Ω : Type}
    (G : Ω → Digest × (Res × TObs (restDepth a R)) → Prop)
    (hG0 : ∀ w : Ω × (Digest × (Res × TObs (restDepth a R))), ¬G w.1 w.2)
    (P : PMF (Ω × (Digest × (Res × TObs (restDepth a R))))) : Pr[fun w => G w.1 w.2 | P] = 0 := by
  rw [probEvent_eq_tsum_ite]
  exact ENNReal.tsum_eq_zero.mpr fun w => if_neg (hG0 w)

include hac hLleaf hG hGq hF hF0

end Lift

end Leaf
end ClaudeWCT.W9.T3.Security.Wots

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Core
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.Arith.SideChannel (TSpec Free evalT seedsY seedsR seedsH)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] raw normalize answers RawPrefix.fill RawLeaf.ovL
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U)

open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
noncomputable local instance : Fintype Coordinate := coordinateFintype
noncomputable def restLaw (U : Finset HashInput) : PMF (Tables U) := PMF.uniformOfFintype (Tables U)
theorem sourceLeaf_leaf_lt {L : LeafAddr} (hL : WotsExtract.SourceLeaf7 L) : L.leaf<2^24 := by
  have hh : ∀lay:Layer,2^height lay≤2^24 := by intro lay;fin_cases lay<;>decide
  exact hL.2.trans_le (hh L.lay)
/-- The chain `a` as an unrevealed coordinate of its leaf (depth `≥ 1`). -/
def selfF {a : ChainAddr} (hac : a.chain < chainCount a.key.lay) (R : Tables U)
    (hd1 : 1 ≤ RawPrefix.restDepth a R) : Free (revSet a.key R) :=
  ⟨⟨a.chain, hac⟩, by
    unfold revSet
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [RawPrefix.restDepth_eq] at hd1
    intro h
    rw [show (⟨a.key, (⟨a.chain, hac⟩ : Fin (chainCount a.key.lay)).val⟩ : ChainAddr) = a from rfl] at h
    omega⟩

/-- Per rest table error (zero at depth `0`). -/
noncomputable def errAR {Res : Type} (a : ChainAddr) (hac : a.chain < chainCount a.key.lay)
    (GD : Answers → OracleComp RefWorld Res) (q : ℕ) (R : Tables U) : ℝ≥0∞ :=
  if hd1 : 1 ≤ RawPrefix.restDepth a R then ENNReal.ofReal (errR hU (a := a) R GD (selfF hac R hd1) q) else 0

include hU in
theorem restLaw_resampleL_tsum {L : LeafAddr} (hL : L.leaf < 2 ^ 24) (Φ : Tables U → ℝ≥0∞) :
    ∑' R, restLaw U R * Φ R =
      ∑' R, restLaw U R * ∑' y, PMF.uniformOfFintype (LeafData L) y * Φ (RawLeaf.ovL L R y) := by
  unfold restLaw
  have h := RawLeaf.restLaw_resampleL hU hL (fun R => PMF.pure R)
  simp only [PMF.bind_pure] at h
  conv_lhs => rw [h]
  rw [SphincsSecurity.Concrete.PartialChainEndpoint.expectation_bind]
  congr 1
  funext R
  congr 1
  rw [show (PMF.uniformOfFintype (LeafData L)).bind (fun y => PMF.pure (RawLeaf.ovL L R y)) =
    (PMF.uniformOfFintype (LeafData L)).map (RawLeaf.ovL L R) from rfl,
    SphincsSecurity.Concrete.PartialChainEndpoint.expectation_map]

section Lift
variable {a : ChainAddr} (hac : a.chain < chainCount a.key.lay) (hL : WotsExtract.SourceLeaf7 a.key)
  {Res : Type} (GD : Answers → OracleComp RefWorld Res) (hG : ∀ T T', CanonicalRef.Leaf.Congr (sourceMessages T) a.key T T' → GD T' = GD T)
  (q : ℕ) (hGq : ∀ T, OracleComp.IsQueryBoundP (GD T) RefCharged q)
  (F : (d : ℕ) → Tables U → Digest × (Res × TObs d) → Prop)
  (hF : ∀ (R : Tables U) (p : PData a.key (RawPrefix.restDepth a R)) (K K' : Fin (WCT9.famCount a.key.lay) → Digest),
    seedsR (ptL a.key) (revSet a.key R) K = seedsR (ptL a.key) (revSet a.key R) K' →
      F (RawPrefix.restDepth a R) (RawLeaf.ovL a.key R (K, progF p.1.1 p.1.2 K)) =
        F (RawPrefix.restDepth a R) (RawLeaf.ovL a.key R (K', progF p.1.1 p.1.2 K')))
  (hF0 : ∀ R z, ¬F 0 R z)

theorem prob_zero_of_depth {R : Tables U} (h0 : RawPrefix.restDepth a R = 0) {Ω : Type}
    (G : Ω → Digest × (Res × TObs (RawPrefix.restDepth a R)) → Prop)
    (hG0 : ∀ w : Ω × (Digest × (Res × TObs (RawPrefix.restDepth a R))), ¬G w.1 w.2)
    (P : PMF (Ω × (Digest × (Res × TObs (RawPrefix.restDepth a R))))) : Pr[fun w => G w.1 w.2 | P] = 0 := by
  rw [probEvent_eq_tsum_ite]
  exact ENNReal.tsum_eq_zero.mpr fun w => if_neg (hG0 w)

include hac hL hG hGq hF hF0

end Lift
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Core
end
