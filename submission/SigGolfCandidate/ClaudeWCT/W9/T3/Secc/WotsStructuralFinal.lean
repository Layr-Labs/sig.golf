import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsTransportShort
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsEncodingResample
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsStructuralHonest
import SigGolfCandidate.ClaudeWCT.W9.New.G3a.ExtractSrc
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsReferenceInputs
import SigGolfCandidate.T3.Secc.WotsStructuralFinal
import SigGolfCandidate.T3.Secc.WotsTransportCount

section
namespace ClaudeWCT.W9.T3.Security.Wots.Structural
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Structural
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue leafRoot)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] SigGolfCandidate.T3.buildTree SigGolfCandidate.T3.buildLeaf
structure Variant (labels : CanonGraph.Labels) (T T' : Answers) : Prop where
  agrees : CanonGraph.Agrees T labels
  coin : ∀ n, T (.inl (.inl n)) = T' (.inl (.inl n))
  priv : ∀ c, T (.inr c) = T' (.inr c)
  pub : ∀ x : HashInput, (∀ node : CanonGraph.Node, Extract.posOf x = some node.toPos →
    x = CanonGraph.cell (CanonGraph.secretsOf T) node labels) → T (.inl (.inr x)) = T' (.inl (.inr x))
theorem posOf_honestInput (T : Answers) (p : Extract.Pos) (hp : p.Bounded) :
    Extract.posOf (Extract.honestInput T p) = some p :=
  Extract.posOf_eq hp (Extract.hdrBlock_honestInput T p)
theorem Variant.honest {labels : CanonGraph.Labels} {T T' : Answers} (hv : Variant labels T T') :
    ∀ q, HonestQuery T q → T q = T' q
  | .inl (.inl n), _ => hv.coin n
  | .inr c, _ => hv.priv c
  | .inl (.inr x), Or.inl hnone => hv.pub x (fun node h => by rw [hnone] at h; cases h)
  | .inl (.inr x), Or.inr ⟨p, hp, hx⟩ => hv.pub x (fun node h => by
      rw [hx, posOf_honestInput T p hp] at h
      cases h
      rw [hx]
      exact CanonGraph.honestInput_eq hv.agrees node)
theorem Variant.congr {labels : CanonGraph.Labels} {T T' : Answers} (hv : Variant labels T T') {α : Type}
    {program : M α} (hp : QueriesSat T (HonestQuery T) program) :
    evalWithAnswerFn T program = evalWithAnswerFn T' program ∧
      SourceReplay.queried T program = SourceReplay.queried T' program :=
  congr_of_queried T T' program (fun q hq => hv.honest q (hp q hq))
section Game
variable {labels : CanonGraph.Labels} {T T' : Answers}
theorem keygenCharge_variant (hv : Variant labels T T') : keygenCharge T = keygenCharge T' := by
  unfold keygenCharge
  rw [(hv.congr (sat_keygen T)).2]
theorem eval_keygen_variant (hv : Variant labels T T') :
    evalWithAnswerFn T keygen = evalWithAnswerFn T' keygen :=
  (hv.congr (sat_keygen T)).1
theorem signCharge_variant (hv : Variant labels T T') (published : SigGolfCandidate.T3.Cache) (request : Request) :
    signCharge T published request = signCharge T' published request := by
  unfold signCharge
  rw [(hv.congr (sat_authenticatedSign T published request)).2]
theorem eval_sign_variant (hv : Variant labels T T') (published : SigGolfCandidate.T3.Cache) (request : Request) :
    evalWithAnswerFn T (FullGame.authenticatedSign published request) =
      evalWithAnswerFn T' (FullGame.authenticatedSign published request) :=
  (hv.congr (sat_authenticatedSign T published request)).1
theorem offlineSign_variant (hv : Variant labels T T') (published : SigGolfCandidate.T3.Cache) (request : Request) :
    offlineSign T published request = offlineSign T' published request := by
  unfold offlineSign
  rw [signCharge_variant hv, eval_sign_variant hv]
theorem offlineImpl_variant (hv : Variant labels T T') (published : SigGolfCandidate.T3.Cache) :
    offlineImpl T published = offlineImpl T' published := by
  unfold offlineImpl
  have h : offlineSign T published = offlineSign T' published := funext (offlineSign_variant hv published)
  rw [h]
theorem offlineGame_variant (hv : Variant labels T T') (adversary : Final.AdversaryP) :
    offlineGame T adversary = offlineGame T' adversary := by
  unfold offlineGame offlineInteraction
  rw [keygenCharge_variant hv, eval_keygen_variant hv, offlineImpl_variant hv]
theorem referenceGame_variant (hv : Variant labels T T') (adversary : Final.AdversaryP) (q : Nat) :
    referenceGame T adversary q = referenceGame T' adversary q := by
  unfold referenceGame
  rw [offlineGame_variant hv]
end Game
section Depth
variable {labels : CanonGraph.Labels} {T T' : Answers}
theorem wotsTree_variant_top (hv : Variant labels T T') (tree : Nat) (ht : tree < 2 ^ Extract.treeBits 0) :
    WCT9.wotsTree T 0 tree = WCT9.wotsTree T' 0 tree := by
  obtain rfl : tree = 0 := Extract.tree_zero_of_treeBits ht rfl
  rw [WCT9.wotsTree_top, WCT9.wotsTree_top, ← Correctness.eval_buildTopTree, ← Correctness.eval_buildTopTree,
    (hv.congr (sat_buildTopTree T)).1]
theorem wotsTree_take_variant (hv : Variant labels T T') (lay : Layer) (tree : Nat)
    (ht : tree < 2 ^ Extract.treeBits lay) :
    (WCT9.wotsTree T lay tree).take (height lay) = (WCT9.wotsTree T' lay tree).take (height lay) := by
  have htree : tree < 2 ^ 40 := lt_trans (Extract.tree_lt_of_treeBits ht) (by norm_num)
  by_cases hl : lay = 0
  · subst hl
    rw [wotsTree_variant_top hv tree ht]
  · have h0 : 0 < 2 ^ height lay := by positivity
    have hc := (hv.congr (sat_buildTreeP T hl tree 0 [] (Cost.validDigits_nil lay) htree ht)).1
    rw [WCT9.eval_buildTreeP_result T hl tree 0 [] (Cost.validDigits_nil lay) h0,
      WCT9.eval_buildTreeP_result T' hl tree 0 [] (Cost.validDigits_nil lay) h0] at hc
    exact congrArg Prod.fst hc
theorem honestPair_variant (hv : Variant labels T T') (lay : Layer) (tree : Nat)
    (ht : tree < 2 ^ Extract.treeBits lay) :
    Extract.honestPair T lay tree = Extract.honestPair T' lay tree := by
  have hh : height lay - 1 < height lay := by have : 1 ≤ height lay := by fin_cases lay <;> decide
                                              omega
  have key : ∀ x, treeValue (WCT9.wotsTree T lay tree) (height lay - 1) x =
      treeValue (WCT9.wotsTree T' lay tree) (height lay - 1) x := fun x => by
    rw [← WCT9.treeValue_take _ hh, wotsTree_take_variant hv lay tree ht, WCT9.treeValue_take _ hh]
  unfold Extract.honestPair
  rw [key, key]
theorem honestForest_variant (hv : Variant labels T T') (index : Nat) (hindex : index < 2 ^ 31) :
    Extract.honestTop T index = Extract.honestTop T' index := by
  rw [Extract.honestTop_eq_wct9, Extract.honestTop_eq_wct9,
    ← ClaudeWCT.WCT9.signForest_root T index 0, ← ClaudeWCT.WCT9.signForest_root T' index 0,
    (hv.congr (sat_signForest T index hindex 0)).1]
theorem leafMsg_variant (hv : Variant labels T T') (L : LeafAddr) (htree : L.tree < 2 ^ Extract.treeBits L.lay)
    (hleaf : L.leaf < 2 ^ height L.lay) : leafMsg T L = leafMsg T' L := by
  unfold leafMsg
  split
  · rename_i h3
    rw [honestPair_variant hv _ _ (Extract.routed_treeBits_succ h3 htree hleaf)]
  · rw [honestForest_variant hv _ (Nat.mod_lt _ (by decide))]
theorem referenceSearch_variant (hv : Variant labels T T') (L : LeafAddr) (htree : L.tree < 2 ^ Extract.treeBits L.lay)
    (hleaf : L.leaf < 2 ^ height L.lay) : referenceSearch T L = referenceSearch T' L := by
  unfold referenceSearch
  rw [leafMsg_variant hv L htree hleaf]
  exact (hv.congr (sat_layerCounterSearch T _ _ _ _ _ _)).1
theorem referenceDigits_variant (hv : Variant labels T T') (L : LeafAddr) (htree : L.tree < 2 ^ Extract.treeBits L.lay)
    (hleaf : L.leaf < 2 ^ height L.lay) : referenceDigits T L = referenceDigits T' L := by
  unfold referenceDigits
  rw [referenceSearch_variant hv L htree hleaf]
theorem depth_variant (hv : Variant labels T T') (a : ChainAddr) (htree : a.key.tree < 2 ^ Extract.treeBits a.key.lay)
    (hleaf : a.key.leaf < 2 ^ height a.key.lay) : depth T a = depth T' a := by
  unfold depth
  rw [referenceDigits_variant hv a.key htree hleaf]
end Depth
end ClaudeWCT.W9.T3.Security.Wots.Structural
end
section
namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
attribute [local instance] Classical.propDecidable
def OtherInput (answers : Answers) (input : HashInput) : Prop :=
  ∃ position, Extract.posOf input = some position ∧ position.Bounded ∧ WotsExtract.PosSource position ∧
    StructuralClass answers input position
def OtherQuery (answers : Answers) : SigGolfCandidate.T3.Spec.Domain → Prop
  | .inl (.inr input) => OtherInput answers input
  | _ => False
noncomputable def otherCount (sample : RefSample) : Nat :=
  (sample.trace.filter fun e => decide (OtherQuery sample.answers (.inl (.inr e.1)))).length
def TraceInUniverse (adversary : AdversaryP) (q : Nat) : Prop :=
  ∀ sample ∈ (referenceExperiment adversary q).support, ∀ entry ∈ sample.trace,
    entry.1 ∈ referenceInputs adversary
def StructuralHitIn (inputs : Finset HashInput) (answers : Answers) (trace : List Entry) : Prop :=
  ∃ position input answer, (input, answer) ∈ trace ∧ input ∈ inputs ∧ Extract.posOf input = some position ∧
    position.Bounded ∧ WotsExtract.PosSource position ∧ StructuralClass answers input position ∧
    Extract.HashHitAt answers position (Extract.honestInput answers position) input
/-- The two 128-bit halves of an output, swapped. -/
noncomputable def swapHalves : SphincsSecurity.HashOutput ≃ SphincsSecurity.HashOutput :=
  ((SphincsSecurity.splitHashOutputEquiv 128 (by decide)).trans (Equiv.prodComm _ _)).trans
    (SphincsSecurity.splitHashOutputEquiv 128 (by decide)).symm
theorem truncate_swapHalves (a : SphincsSecurity.HashOutput) : SphincsSecurity.truncateHash (swapHalves a) = a.extractLsb' 128 128 := by
  have h := Equiv.apply_symm_apply (SphincsSecurity.splitHashOutputEquiv 128 (by decide))
    ((Equiv.prodComm _ _) (SphincsSecurity.splitHashOutputEquiv 128 (by decide) a))
  exact congrArg Prod.fst h
/-- The high half of a uniform output is uniform (nested FTS r1-1: the top FTS values are high halves). -/
theorem prob_high_eq (target : SphincsSecurity.Digest) :
    Pr[fun answer : HashOutput => answer.extractLsb' 128 128 = target | PMF.uniformOfFintype HashOutput] =
      (Fintype.card SphincsSecurity.Digest : ℝ≥0∞)⁻¹ := by
  rw [← SphincsSecurity.Concrete.HiddenLabelProbe.prob_truncate_eq target]
  simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply, PMF.uniformOfFintype_apply]
  conv_rhs => rw [← swapHalves.tsum_eq]
  simp only [truncate_swapHalves]
  rfl
/-- The used half of a uniform output is uniform at every position. -/
theorem prob_proj_eq (p : Extract.Pos) (target : SphincsSecurity.Digest) :
    Pr[fun answer : HashOutput => p.proj answer = target | PMF.uniformOfFintype HashOutput] =
      (Fintype.card SphincsSecurity.Digest : ℝ≥0∞)⁻¹ := by
  cases p with
  | wctNode i c l n =>
      by_cases hl : l = 5
      · simp only [Extract.Pos.proj, if_pos hl]; exact prob_high_eq target
      · simp only [Extract.Pos.proj, if_neg hl]
        exact SphincsSecurity.Concrete.HiddenLabelProbe.prob_truncate_eq target
  | _ => exact SphincsSecurity.Concrete.HiddenLabelProbe.prob_truncate_eq target
namespace Structural
open SigGolfCandidate.T3.Security.Wots.Structural
open ClaudeWCT.W9.T3.Security.CanonGraph (Node Labels Secrets OtherHalves cell programmed canonInputs privateEquiv)
theorem exists_node_of_posSource {p : Extract.Pos} (h : WotsExtract.PosSource p) : ∃ node : Node, node.toPos = p := by
  apply CanonGraph.exists_toPos
  cases p with
  | chain lay tree leaf i step =>
      obtain ⟨h1, h2, h3, h4⟩ := h
      have hh : 2 ^ height lay ≤ 2 ^ 12 :=
        Nat.pow_le_pow_right (by decide) (Extract.height_le lay)
      have hw : 2 ^ width lay i ≤ 2 ^ 3 :=
        Nat.pow_le_pow_right (by decide) (Extract.width_le lay i)
      have hc := Extract.chainCount_le lay
      exact ⟨Extract.tree_lt_of_treeBits h1, by omega, by omega, by omega⟩
  | leaf lay tree leaf => exact h
  | node lay tree level nd => exact h
  | forest index => exact h
  | wctChain index coord child t step => exact h
  | wctLeaf index coord child => exact h
  | wctNode index coord level nd => exact h
theorem structuralClass_variant {labels : Labels} {T T' : Answers} (hv : Variant labels T T') {x : HashInput}
    {p : Extract.Pos} (hpos : Extract.posOf x = some p) (hsrc : WotsExtract.PosSource p) :
    StructuralClass T x p ↔ StructuralClass T' x p := by
  cases p with
  | chain lay tree leaf i step =>
      obtain ⟨htree, hleaf, -, -⟩ := hsrc
      have key : ∀ (a : ChainAddr) (step' : Nat),
          Extract.posOf x = some (.chain a.key.lay a.key.tree a.key.leaf a.chain step') → depth T a = depth T' a := by
        intro a step' h
        rw [hpos] at h
        simp only [Option.some.injEq, Extract.Pos.chain.injEq] at h
        obtain ⟨hl, ht, hlf, -, -⟩ := h
        exact depth_variant hv a (by rw [← ht, ← hl]; exact htree) (by rw [← hlf, ← hl]; exact hleaf)
      change OtherChainRow T x ↔ OtherChainRow T' x
      constructor
      · rintro ⟨a, step', h, hc⟩
        exact ⟨a, step', h, hc.imp id (fun hd => by rw [← key a step' h]; exact hd)⟩
      · rintro ⟨a, step', h, hc⟩
        exact ⟨a, step', h, hc.imp id (fun hd => by rw [key a step' h]; exact hd)⟩
  | leaf => exact Iff.rfl
  | node => exact Iff.rfl
  | forest => exact Iff.rfl
  | wctChain => exact Iff.rfl
  | wctLeaf => exact Iff.rfl
  | wctNode => exact Iff.rfl
theorem otherInput_variant {labels : Labels} {T T' : Answers} (hv : Variant labels T T') (x : HashInput) :
    OtherInput T x ↔ OtherInput T' x := by
  constructor
  · rintro ⟨p, hpos, hb, hsrc, hc⟩
    exact ⟨p, hpos, hb, hsrc, (structuralClass_variant hv hpos hsrc).mp hc⟩
  · rintro ⟨p, hpos, hb, hsrc, hc⟩
    exact ⟨p, hpos, hb, hsrc, (structuralClass_variant hv hpos hsrc).mpr hc⟩
section Fixed
variable (V : Finset HashInput) (hU : canonInputs ⊆ V) (s : Secrets) (o : OtherHalves) (labels : Labels)
noncomputable def strRows : Finset HashInput :=
  V.filter fun x => ∃ node : Node, Extract.posOf x = some node.toPos ∧ x ≠ cell s node labels
theorem mem_strRows (x : HashInput) :
    x ∈ strRows V s labels ↔ x ∈ V ∧ ∃ node : Node, Extract.posOf x = some node.toPos ∧ x ≠ cell s node labels :=
  Finset.mem_filter
theorem strRows_not_cell {x : HashInput} (hx : x ∈ strRows V s labels) (node : Node) : x ≠ cell s node labels := by
  obtain ⟨-, node₀, hpos, hne⟩ := (mem_strRows V s labels x).mp hx
  intro heq
  have := CanonGraph.cell_eq_of_posOf s labels hpos heq
  subst this
  exact hne heq
def strEmbed : strRows V s labels → V := fun x => ⟨x.val, ((mem_strRows V s labels x.val).mp x.property).1⟩
theorem strEmbed_injective : Function.Injective (strEmbed V s labels) := by
  intro a b h
  exact Subtype.ext (congrArg (fun y : V => y.val) h)
abbrev Rest := SphincsSecurity.Concrete.UniformTableSplit.Outside (strEmbed V s labels) → HashOutput
noncomputable def strTable (rest : Rest V s labels) (ρ : strRows V s labels → HashOutput) : Answers :=
  eagerAnswers V (privateEquiv.symm (s, o))
    (programmed V hU s labels
      (SphincsSecurity.Concrete.UniformTableSplit.join (strEmbed V s labels) (strEmbed_injective V s labels) ρ rest))
variable (rest : Rest V s labels)
theorem strTable_eq_canon (ρ : strRows V s labels → HashOutput) :
    strTable V hU s o labels rest ρ = CanonGraph.eagerAnswers (privateEquiv.symm (s, o)) V
      (programmed V hU s labels
        (SphincsSecurity.Concrete.UniformTableSplit.join (strEmbed V s labels) (strEmbed_injective V s labels) ρ rest)) := by
  funext query
  rcases query with (n | x) | c <;> rfl
theorem strTable_agrees (ρ : strRows V s labels → HashOutput) :
    CanonGraph.Agrees (strTable V hU s o labels rest ρ) labels := by
  rw [strTable_eq_canon]
  exact CanonGraph.eager_programmed_agrees V hU s o labels _
theorem secretsOf_strTable (ρ : strRows V s labels → HashOutput) :
    CanonGraph.secretsOf (strTable V hU s o labels rest ρ) = s := by
  rw [strTable_eq_canon, CanonGraph.secretsOf_eager, CanonGraph.privateSecrets_symm]
theorem strTable_public_mem (ρ : strRows V s labels → HashOutput) (x : HashInput) (hx : x ∈ V) :
    strTable V hU s o labels rest ρ (.inl (.inr x)) =
      programmed V hU s labels
        (SphincsSecurity.Concrete.UniformTableSplit.join (strEmbed V s labels) (strEmbed_injective V s labels) ρ rest)
        ⟨x, hx⟩ :=
  SphincsSecurity.Concrete.finiteHashAnswer_none ∅ V _ x hx rfl
theorem strTable_str (ρ : strRows V s labels → HashOutput) (x : HashInput) (hx : x ∈ strRows V s labels) :
    strTable V hU s o labels rest ρ (.inl (.inr x)) = ρ ⟨x, hx⟩ := by
  have hV := ((mem_strRows V s labels x).mp hx).1
  rw [strTable_public_mem V hU s o labels rest ρ x hV,
    CanonGraph.programmed_other V hU s labels _ ⟨x, hV⟩ (strRows_not_cell V s labels hx)]
  exact SphincsSecurity.Concrete.UniformTableSplit.join_embed (strEmbed V s labels) (strEmbed_injective V s labels)
    ρ rest ⟨x, hx⟩
theorem strTable_out (ρ ρ' : strRows V s labels → HashOutput) (x : HashInput) (hx : x ∉ strRows V s labels) :
    strTable V hU s o labels rest ρ (.inl (.inr x)) = strTable V hU s o labels rest ρ' (.inl (.inr x)) := by
  by_cases hV : x ∈ V
  · rw [strTable_public_mem V hU s o labels rest ρ x hV, strTable_public_mem V hU s o labels rest ρ' x hV]
    by_cases hcell : ∃ node, x = cell s node labels
    · obtain ⟨node, rfl⟩ := hcell
      have he : (⟨cell s node labels, hV⟩ : V) = CanonGraph.cellIn V hU s node labels := rfl
      rw [he, CanonGraph.programmed_at, CanonGraph.programmed_at]
    · have hn : ∀ node, x ≠ cell s node labels := fun node h => hcell ⟨node, h⟩
      rw [CanonGraph.programmed_other V hU s labels _ ⟨x, hV⟩ hn,
        CanonGraph.programmed_other V hU s labels _ ⟨x, hV⟩ hn]
      have hout : (⟨x, hV⟩ : V) ∉ Set.range (strEmbed V s labels) := by
        rintro ⟨y, hy⟩
        apply hx
        have : y.val = x := congrArg Subtype.val hy
        rw [← this]
        exact y.property
      exact (SphincsSecurity.Concrete.UniformTableSplit.join_outside _ _ ρ rest ⟨⟨x, hV⟩, hout⟩).trans
        (SphincsSecurity.Concrete.UniformTableSplit.join_outside _ _ ρ' rest ⟨⟨x, hV⟩, hout⟩).symm
  · change SphincsSecurity.Concrete.finiteHashAnswer ∅ V _ x = SphincsSecurity.Concrete.finiteHashAnswer ∅ V _ x
    simp only [SphincsSecurity.Concrete.finiteHashAnswer, dif_neg hV]
theorem strTable_variant (ρ ρ' : strRows V s labels → HashOutput) :
    Variant labels (strTable V hU s o labels rest ρ) (strTable V hU s o labels rest ρ') where
  agrees := strTable_agrees V hU s o labels rest ρ
  coin := fun _ => rfl
  priv := fun _ => rfl
  pub := fun x hx => by
    apply strTable_out V hU s o labels rest ρ ρ' x
    intro hmem
    obtain ⟨-, node, hpos, hne⟩ := (mem_strRows V s labels x).mp hmem
    have := hx node hpos
    rw [secretsOf_strTable] at this
    exact hne this
def strHit (T0 : Answers) (x : HashInput) (a : HashOutput) : Prop :=
  x ∈ strRows V s labels ∧ OtherInput T0 x ∧ ∃ node : Node, Extract.posOf x = some node.toPos ∧
    node.toPos.proj a = node.toPos.proj (labels node)
theorem strHit_kernel (T0 : Answers) (x : HashInput) (hx : x ∈ strRows V s labels) :
    Pr[strHit V s labels T0 x | (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput)] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * (if OtherInput T0 x then 1 else 0 : ℝ≥0∞) := by
  by_cases hO : OtherInput T0 x
  · rw [if_pos hO, mul_one]
    obtain ⟨-, node₀, hpos₀, -⟩ := (mem_strRows V s labels x).mp hx
    calc Pr[strHit V s labels T0 x | (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput)]
        ≤ Pr[fun a : HashOutput => node₀.toPos.proj a = node₀.toPos.proj (labels node₀) |
            PMF.uniformOfFintype HashOutput] := by
          apply probEvent_mono
          rintro a - ⟨-, -, node, hpos, hlow⟩
          have hn : node = node₀ :=
            CanonGraph.toPos_injective (Option.some.inj (hpos.symm.trans hpos₀))
          subst hn
          exact hlow
      _ = (2 ^ 128 : ℝ≥0∞)⁻¹ := by
          have h := prob_proj_eq node₀.toPos (node₀.toPos.proj (labels node₀))
          rw [card_digest] at h
          exact h
  · have hz : Pr[strHit V s labels T0 x | (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput)] = 0 :=
      probEvent_eq_zero fun _ _ h => hO h.2.1
    rw [hz]
    exact bot_le
theorem hit_bridge (ρ : strRows V s labels → HashOutput) (qs : List RefWorld.Domain)
    (h : StructuralHitIn V (strTable V hU s o labels rest ρ) (traceOf (strTable V hU s o labels rest ρ) qs)) :
    ∃ e ∈ traceOf (strTable V hU s o labels rest ρ) qs,
      strHit V s labels (strTable V hU s o labels rest (fun _ => 0)) e.1 e.2 := by
  obtain ⟨p, x, a, hmem, hxV, hpos, hb, hsrc, hc, hne, hlow⟩ := h
  refine ⟨(x, a), hmem, ?_, ?_, ?_⟩
  · obtain ⟨node, rfl⟩ := exists_node_of_posSource hsrc
    rw [CanonGraph.honestInput_eq (strTable_agrees V hU s o labels rest ρ), secretsOf_strTable] at hne
    exact (mem_strRows V s labels x).mpr ⟨hxV, node, hpos, hne⟩
  · exact ⟨p, hpos, hb, hsrc, (structuralClass_variant (strTable_variant V hU s o labels rest ρ (fun _ => 0))
      hpos hsrc).mp hc⟩
  · obtain ⟨node, rfl⟩ := exists_node_of_posSource hsrc
    refine ⟨node, hpos, ?_⟩
    have ha : a = strTable V hU s o labels rest ρ (.inl (.inr x)) := mem_traceOf hmem
    rw [CanonGraph.honest_answer (strTable_agrees V hU s o labels rest ρ)] at hlow
    change node.toPos.proj a = node.toPos.proj (labels node)
    rw [ha]
    exact hlow
theorem count_bridge (ρ : strRows V s labels → HashOutput) (pk : Digest) (trace : List Entry) :
    otherCount ⟨strTable V hU s o labels rest ρ, pk, trace⟩ =
      (trace.filter fun e => decide (OtherInput (strTable V hU s o labels rest (fun _ => 0)) e.1)).length := by
  unfold otherCount
  congr 1
  apply List.filter_congr
  intro e _
  exact decide_eq_decide.mpr (otherInput_variant (strTable_variant V hU s o labels rest ρ (fun _ => 0)) e.1)
end Fixed
noncomputable def sampleComp (adversary : AdversaryP) (q : Nat) (T : Answers) : ProbComp RefSample :=
  (fun run => (⟨T, (evalWithAnswerFn T keygen).1, traceOf T run.2⟩ : RefSample)) <$> offlineRun T adversary q
section Bound
variable (adversary : AdversaryP) (q : Nat) (V : Finset HashInput) (hU : canonInputs ⊆ V) (s : Secrets)
  (o : OtherHalves) (labels : Labels) (rest : Rest V s labels)
theorem sampleComp_recorded (ρ : strRows V s labels → HashOutput) :
    𝒮[sampleComp adversary q (strTable V hU s o labels rest ρ)] =
      (fun run => (⟨strTable V hU s o labels rest ρ, (evalWithAnswerFn (strTable V hU s o labels rest ρ) keygen).1,
          traceOf (strTable V hU s o labels rest ρ) run.2⟩ : RefSample)) <$>
        𝒮[simulateQ (refImpl (strTable V hU s o labels rest ρ))
          (SphincsSecurity.QueryCap.recorded (referenceGame (strTable V hU s o labels rest (fun _ => 0)) adversary q))] := by
  unfold sampleComp offlineRun
  rw [referenceGame_variant (strTable_variant V hU s o labels rest ρ (fun _ => 0)), evalSPMF_map]
theorem recorded_pair (ρ : strRows V s labels → HashOutput) :
    (fun run => (run.1, traceOf (strTable V hU s o labels rest ρ) run.2)) <$>
        𝒮[simulateQ (refImpl (strTable V hU s o labels rest ρ))
          (SphincsSecurity.QueryCap.recorded (referenceGame (strTable V hU s o labels rest (fun _ => 0)) adversary q))] =
      (fun r => (r.1, r.2.toList)) <$>
        𝒮[simulateQ (refImpl (strTable V hU s o labels rest ρ))
          (SphincsSecurity.QueryPause.traced refObs (referenceGame (strTable V hU s o labels rest (fun _ => 0)) adversary q))] := by
  rw [← evalSPMF_map, ← evalSPMF_map, recorded_traced]
theorem fixed_bound :
    Pr[fun sample => StructuralHitIn V sample.answers sample.trace |
        (liftM (PMF.uniformOfFintype (strRows V s labels → HashOutput)) : SPMF _) >>= fun ρ =>
          𝒮[sampleComp adversary q (strTable V hU s o labels rest ρ)]] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * ∑' sample,
        Pr[= sample | (liftM (PMF.uniformOfFintype (strRows V s labels → HashOutput)) : SPMF _) >>= fun ρ =>
          𝒮[sampleComp adversary q (strTable V hU s o labels rest ρ)]] * (otherCount sample : ℝ≥0∞) := by
  set T := strTable V hU s o labels rest with hT
  set G0 := referenceGame (T fun _ => 0) adversary q with hG0
  set Hit := strHit V s labels (T fun _ => 0) with hHit
  set Charged := OtherInput (T fun _ => 0) with hCharged
  have hlazy := lazy_seen_le (strRows V s labels) T (fun ρ x hx => strTable_str V hU s o labels rest ρ x hx)
    (fun ρ x hx => strTable_out V hU s o labels rest ρ (fun _ => 0) x hx) Hit Charged (2 ^ 128 : ℝ≥0∞)⁻¹
    (fun x a h => h.1) (fun x hx => strHit_kernel V s labels (T fun _ => 0) x hx) G0
  have hevent : Pr[fun sample => StructuralHitIn V sample.answers sample.trace |
        (liftM (PMF.uniformOfFintype (strRows V s labels → HashOutput)) : SPMF _) >>= fun ρ =>
          𝒮[sampleComp adversary q (T ρ)]] ≤
      Pr[fun r => Seen Hit r.2 | (liftM (PMF.uniformOfFintype (strRows V s labels → HashOutput)) : SPMF _) >>= fun ρ =>
          𝒮[simulateQ (refImpl (T ρ)) (SphincsSecurity.QueryPause.traced refObs G0)]] := by
    rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
    refine ENNReal.tsum_le_tsum fun ρ => mul_le_mul' le_rfl ?_
    rw [sampleComp_recorded adversary q V hU s o labels rest ρ, probEvent_map]
    have hpair := recorded_pair adversary q V hU s o labels rest ρ
    have hseen : Pr[fun r => Seen Hit r.2 |
        𝒮[simulateQ (refImpl (T ρ)) (SphincsSecurity.QueryPause.traced refObs G0)]] =
        Pr[fun z => ∃ e ∈ z.2, Hit e.1 e.2 | (fun run => (run.1, traceOf (T ρ) run.2)) <$>
          𝒮[simulateQ (refImpl (T ρ)) (SphincsSecurity.QueryCap.recorded G0)]] := by
      rw [hpair, probEvent_map]
      rfl
    rw [hseen, probEvent_map]
    apply probEvent_mono
    intro run _ h
    exact hit_bridge V hU s o labels rest ρ run.2 h
  have hcount : (∑' sample,
        Pr[= sample | (liftM (PMF.uniformOfFintype (strRows V s labels → HashOutput)) : SPMF _) >>= fun ρ =>
          𝒮[sampleComp adversary q (T ρ)]] * (otherCount sample : ℝ≥0∞)) =
      ∑' r, Pr[= r | (liftM (PMF.uniformOfFintype (strRows V s labels → HashOutput)) : SPMF _) >>= fun ρ =>
          𝒮[simulateQ (refImpl (T ρ)) (SphincsSecurity.QueryPause.traced refObs G0)]] *
            (chargedCount Charged r.2 : ℝ≥0∞) := by
    rw [tsum_probOutput_bind_mul, tsum_probOutput_bind_mul]
    refine tsum_congr fun ρ => congrArg _ ?_
    rw [sampleComp_recorded adversary q V hU s o labels rest ρ, tsum_probOutput_map_mul]
    have hA : ∀ run : Option (Bool × Nat) × List RefWorld.Domain,
        (otherCount (⟨T ρ, (evalWithAnswerFn (T ρ) keygen).1, traceOf (T ρ) run.2⟩ : RefSample) : ℝ≥0∞) =
          (fun z : Option (Bool × Nat) × List Entry => ((z.2.filter fun e => decide (Charged e.1)).length : ℝ≥0∞))
            ((fun run => (run.1, traceOf (T ρ) run.2)) run) := by
      intro run
      rw [count_bridge V hU s o labels rest ρ]
    refine (tsum_congr fun run => congrArg _ (hA run)).trans ?_
    rw [← tsum_probOutput_map_mul _ (fun run : Option (Bool × Nat) × List RefWorld.Domain =>
        (run.1, traceOf (T ρ) run.2))
      (fun z : Option (Bool × Nat) × List Entry => ((z.2.filter fun e => decide (Charged e.1)).length : ℝ≥0∞)),
      recorded_pair adversary q V hU s o labels rest ρ, tsum_probOutput_map_mul]
    rfl
  rw [hcount]
  exact hevent.trans hlazy
end Bound
def BoundOn (V : Finset HashInput) (p : SPMF RefSample) : Prop :=
  Pr[fun sample => StructuralHitIn V sample.answers sample.trace | p] ≤
    (2 ^ 128 : ℝ≥0∞)⁻¹ * ∑' sample, Pr[= sample | p] * (otherCount sample : ℝ≥0∞)
theorem boundOn_bind {X : Type} (V : Finset HashInput) (μ : SPMF X) (K : X → SPMF RefSample)
    (h : ∀ x, BoundOn V (K x)) : BoundOn V (μ >>= K) := by
  unfold BoundOn
  rw [probEvent_bind_eq_tsum, tsum_probOutput_bind_mul]
  calc (∑' x, Pr[= x | μ] * Pr[fun sample => StructuralHitIn V sample.answers sample.trace | K x])
      ≤ ∑' x, Pr[= x | μ] * ((2 ^ 128 : ℝ≥0∞)⁻¹ * ∑' sample, Pr[= sample | K x] * (otherCount sample : ℝ≥0∞)) :=
        ENNReal.tsum_le_tsum fun x => mul_le_mul' le_rfl (h x)
    _ = _ := by simp only [mul_left_comm _ (2 ^ 128 : ℝ≥0∞)⁻¹, ENNReal.tsum_mul_left]
section Assembly
noncomputable local instance instFintypeCoordinate_wotsStructural : Fintype Coordinate := coordinateFintype
noncomputable local instance instSampleableTypeFullTable_wotsStructural : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
theorem referenceInputs_canon (adversary : AdversaryP) : canonInputs ⊆ referenceInputs adversary := by
  unfold referenceInputs
  exact CanonGraph.canonInputs_subset_publicUniverse.trans Finset.subset_union_left
theorem tables_bind_spmf {R : Type} (U : Finset HashInput) (hU : canonInputs ⊆ U)
    (next : FullGame.FullTable → (U → HashOutput) → ProbComp R) :
    ((liftM (PMF.uniformOfFintype FullGame.FullTable) : SPMF _) >>= fun pt =>
      (liftM (PMF.uniformOfFintype (U → HashOutput)) : SPMF _) >>= fun pub => 𝒮[next pt pub]) =
    ((liftM (PMF.uniformOfFintype Secrets) : SPMF _) >>= fun s =>
      (liftM (PMF.uniformOfFintype OtherHalves) : SPMF _) >>= fun o =>
      (liftM (PMF.uniformOfFintype Labels) : SPMF _) >>= fun labels =>
      (liftM (PMF.uniformOfFintype (U → HashOutput)) : SPMF _) >>= fun r =>
        𝒮[next (privateEquiv.symm (s, o)) (programmed U hU s labels r)]) := by
  have h := CanonGraph.tables_bind U hU next
  simp only [evalSPMF_bind, evalSPMF_uniformSample] at h
  exact h
theorem referenceComp_spmf (adversary : AdversaryP) (q : Nat) :
    𝒮[referenceComp adversary q] =
      ((liftM (PMF.uniformOfFintype FullGame.FullTable) : SPMF _) >>= fun pt =>
        (liftM (PMF.uniformOfFintype (referenceInputs adversary → HashOutput)) : SPMF _) >>= fun pub =>
          𝒮[sampleComp adversary q (eagerAnswers (referenceInputs adversary) pt pub)]) := by
  unfold referenceComp
  simp only [evalSPMF_bind, evalSPMF_uniformSample]
  rfl
theorem referenceComp_bound (adversary : AdversaryP) (q : Nat) :
    BoundOn (referenceInputs adversary) 𝒮[referenceComp adversary q] := by
  rw [referenceComp_spmf, tables_bind_spmf _ (referenceInputs_canon adversary)]
  refine boundOn_bind _ _ _ fun s => boundOn_bind _ _ _ fun o => boundOn_bind _ _ _ fun labels => ?_
  rw [uniform_split_bind (strEmbed (referenceInputs adversary) s labels)
    (strEmbed_injective (referenceInputs adversary) s labels)]
  refine boundOn_bind _ _ _ fun rest => ?_
  exact fixed_bound adversary q (referenceInputs adversary) (referenceInputs_canon adversary) s o labels rest
end Assembly
end Structural
theorem referenceExperiment_eq (adversary : AdversaryP) (q : Nat) :
    referenceExperiment adversary q = liftM (referenceComp adversary q) := rfl
theorem reference_structural_in_le (adversary : AdversaryP) (q : Nat) :
    Pr[fun sample => StructuralHitIn (referenceInputs adversary) sample.answers sample.trace |
        referenceExperiment adversary q] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * ∑' sample, referenceExperiment adversary q sample * (otherCount sample : ℝ≥0∞) := by
  have h := Structural.referenceComp_bound adversary q
  unfold Structural.BoundOn at h
  rw [referenceExperiment_eq, probEvent_liftM_pmf]
  simp only [liftM_pmf_apply]
  exact h
theorem reference_structural_le (adversary : AdversaryP) (q : Nat) (hV : TraceInUniverse adversary q) :
    Pr[fun sample => WotsExtract.StructuralHitSrc sample.answers sample.trace | referenceExperiment adversary q] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * ∑' sample, referenceExperiment adversary q sample * (otherCount sample : ℝ≥0∞) := by
  refine le_trans ?_ (reference_structural_in_le adversary q)
  rw [referenceExperiment_eq, probEvent_liftM_pmf', probEvent_liftM_pmf']
  apply probEvent_mono
  intro sample hs h
  have hsupp : sample ∈ (referenceExperiment adversary q).support := by
    rw [referenceExperiment_eq]
    exact mem_support_liftM_pmf _ sample hs
  obtain ⟨position, input, answer, hmem, hpos, hb, hsrc, hc, hhit⟩ := h
  exact ⟨position, input, answer, hmem, hV sample hsupp (input, answer) hmem, hpos, hb, hsrc, hc, hhit⟩
end ClaudeWCT.W9.T3.Security.Wots
end
section
namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
theorem traceInUniverse (adversary : AdversaryP) (q : Nat) : TraceInUniverse adversary q :=
  fun sample hs entry he => reference_trace_mem adversary q sample hs entry he
theorem reference_structural_src_le (adversary : AdversaryP) (q : Nat) :
    Pr[fun sample => WotsExtract.StructuralHitSrc sample.answers sample.trace | referenceExperiment adversary q] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * ∑' sample, referenceExperiment adversary q sample * (otherCount sample : ℝ≥0∞) :=
  reference_structural_le adversary q (traceInUniverse adversary q)
end ClaudeWCT.W9.T3.Security.Wots
end

namespace ClaudeWCT.W9.T3.Security.Wots.PairedStructural
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000

theorem prob_proj_eq (position : Extract.Pos) (target : Digest) :
    Pr[fun answer : HashOutput=>Extract.Paired.proj position answer=target |
      PMF.uniformOfFintype HashOutput]=(Fintype.card Digest:ℝ≥0∞)⁻¹ := by
  cases position with
  | wctNode index coord level node=>
    by_cases h:Extract.Paired.highNodeAt coord level node
    · simp only [Extract.Paired.proj,if_pos h]
      exact prob_high_eq target
    · simp only [Extract.Paired.proj,if_neg h]
      exact SphincsSecurity.Concrete.HiddenLabelProbe.prob_truncate_eq target
  | wctLeaf index coord child=>
    by_cases h:Extract.Paired.highLeafAt coord child
    · simp only [Extract.Paired.proj,if_pos h]
      exact prob_high_eq target
    · simp only [Extract.Paired.proj,if_neg h]
      exact SphincsSecurity.Concrete.HiddenLabelProbe.prob_truncate_eq target
  | _=>exact SphincsSecurity.Concrete.HiddenLabelProbe.prob_truncate_eq target
#print axioms prob_proj_eq
end ClaudeWCT.W9.T3.Security.Wots.PairedStructural

namespace ClaudeWCT.W9.T3.Security.Wots.PairedStructural
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Structural
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

structure Variant (labels : CanonGraph.Labels) (T T' : Answers) : Prop where
  agrees : CanonGraph.Paired.Agrees T labels
  coin : ∀ n, T (.inl (.inl n)) = T' (.inl (.inl n))
  priv : ∀ c, T (.inr c) = T' (.inr c)
  pub : ∀ x : HashInput, (∀ node : CanonGraph.Node, Extract.posOf x = some node.toPos →
    x = CanonGraph.Paired.cell (CanonGraph.secretsOf T) node labels) → T (.inl (.inr x)) = T' (.inl (.inr x))

theorem posOf_honestInput (T : Answers) (p : Extract.Pos) (hp : Extract.Paired.Bounded p) :
    Extract.posOf (Extract.Paired.honestInput T p) = some p :=
  Extract.posOf_eq hp.legacy (Extract.Paired.hdrBlock_honestInput T p)


end ClaudeWCT.W9.T3.Security.Wots.PairedStructural

namespace ClaudeWCT.W9.T3.Security.Wots.PairedStructural
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Structural
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem Variant.honest {labels : CanonGraph.Labels} {T T' : Answers} (hv : Variant labels T T') :
    ∀ q, HonestQuery T q → T q = T' q
  | .inl (.inl n), _ => hv.coin n
  | .inr c, _ => hv.priv c
  | .inl (.inr x), Or.inl hnone => hv.pub x (fun node h => by rw [hnone] at h; cases h)
  | .inl (.inr x), Or.inr ⟨p, hp, hx⟩ => hv.pub x (fun node h => by
      rw [hx,posOf_honestInput T p hp] at h
      cases h
      rw [hx]
      exact CanonGraph.Paired.honestInput_eq T labels hv.agrees node hp)

theorem Variant.congr {labels : CanonGraph.Labels} {T T' : Answers} (hv : Variant labels T T') {α : Type}
    {program : M α} (hp : QueriesSat T (HonestQuery T) program) :
    evalWithAnswerFn T program = evalWithAnswerFn T' program ∧
      SourceReplay.queried T program = SourceReplay.queried T' program :=
  congr_of_queried T T' program (fun q hq => hv.honest q (hp q hq))

theorem eval_keygen_variant {labels : CanonGraph.Labels} {T T' : Answers} (hv : Variant labels T T') :
    evalWithAnswerFn T keygen = evalWithAnswerFn T' keygen :=
  (hv.congr (sat_keygen T)).1

theorem keygen_queries_variant {labels : CanonGraph.Labels} {T T' : Answers} (hv : Variant labels T T') :
    SourceReplay.queried T keygen = SourceReplay.queried T' keygen :=
  (hv.congr (sat_keygen T)).2

#print axioms Variant.congr
#print axioms eval_keygen_variant
#print axioms keygen_queries_variant
end ClaudeWCT.W9.T3.Security.Wots.PairedStructural

namespace ClaudeWCT.W9.T3.Security.Wots.PairedStructural
open OracleComp OracleSpec ENNReal OracleComp.EvalDist
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open CanonGraph
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section Fixed
variable (V : Finset HashInput) (hU : CanonGraph.Paired.canonInputs ⊆ V) (s : CanonGraph.Secrets) (o : CanonGraph.OtherHalves) (labels : CanonGraph.Labels)
noncomputable def strRows : Finset HashInput :=
  V.filter fun x => ∃ node : CanonGraph.Node, Extract.posOf x = some node.toPos ∧ x ≠ CanonGraph.Paired.cell s node labels
theorem mem_strRows (x : HashInput) :
    x ∈ strRows V s labels ↔ x ∈ V ∧ ∃ node : CanonGraph.Node, Extract.posOf x = some node.toPos ∧ x ≠ CanonGraph.Paired.cell s node labels :=
  Finset.mem_filter
theorem strRows_not_cell {x : HashInput} (hx : x ∈ strRows V s labels) (node : CanonGraph.Node) : x ≠ CanonGraph.Paired.cell s node labels := by
  obtain ⟨-, node₀, hpos, hne⟩ := (mem_strRows V s labels x).mp hx
  intro heq
  have := CanonGraph.Paired.cell_eq_of_posOf s labels hpos heq
  subst this
  exact hne heq
def strEmbed : strRows V s labels → V := fun x => ⟨x.val, ((mem_strRows V s labels x.val).mp x.property).1⟩
theorem strEmbed_injective : Function.Injective (strEmbed V s labels) := by
  intro a b h
  exact Subtype.ext (congrArg (fun y : V => y.val) h)
abbrev Rest := SphincsSecurity.Concrete.UniformTableSplit.Outside (strEmbed V s labels) → HashOutput
noncomputable def strTable (rest : Rest V s labels) (ρ : strRows V s labels → HashOutput) : Answers :=
  eagerAnswers V (CanonGraph.privateEquiv.symm (s, o))
    (CanonGraph.Paired.programmed V hU s labels
      (SphincsSecurity.Concrete.UniformTableSplit.join (strEmbed V s labels) (strEmbed_injective V s labels) ρ rest))
variable (rest : Rest V s labels)
theorem strTable_eq_canon (ρ : strRows V s labels → HashOutput) :
    strTable V hU s o labels rest ρ = CanonGraph.eagerAnswers (CanonGraph.privateEquiv.symm (s, o)) V
      (CanonGraph.Paired.programmed V hU s labels
        (SphincsSecurity.Concrete.UniformTableSplit.join (strEmbed V s labels) (strEmbed_injective V s labels) ρ rest)) := by
  funext query
  rcases query with (n | x) | c <;> rfl
theorem strTable_agrees (ρ : strRows V s labels → HashOutput) :
    CanonGraph.Paired.Agrees (strTable V hU s o labels rest ρ) labels := by
  rw [strTable_eq_canon]
  exact CanonGraph.Paired.eager_programmed_agrees V hU s o labels _
theorem secretsOf_strTable (ρ : strRows V s labels → HashOutput) :
    CanonGraph.secretsOf (strTable V hU s o labels rest ρ) = s := by
  rw [strTable_eq_canon, CanonGraph.secretsOf_eager, CanonGraph.privateSecrets_symm]
theorem strTable_public_mem (ρ : strRows V s labels → HashOutput) (x : HashInput) (hx : x ∈ V) :
    strTable V hU s o labels rest ρ (.inl (.inr x)) =
      CanonGraph.Paired.programmed V hU s labels
        (SphincsSecurity.Concrete.UniformTableSplit.join (strEmbed V s labels) (strEmbed_injective V s labels) ρ rest)
        ⟨x, hx⟩ :=
  SphincsSecurity.Concrete.finiteHashAnswer_none ∅ V _ x hx rfl
theorem strTable_str (ρ : strRows V s labels → HashOutput) (x : HashInput) (hx : x ∈ strRows V s labels) :
    strTable V hU s o labels rest ρ (.inl (.inr x)) = ρ ⟨x, hx⟩ := by
  have hV := ((mem_strRows V s labels x).mp hx).1
  rw [strTable_public_mem V hU s o labels rest ρ x hV,
    CanonGraph.Paired.programmed_other V hU s labels _ ⟨x, hV⟩ (strRows_not_cell V s labels hx)]
  exact SphincsSecurity.Concrete.UniformTableSplit.join_embed (strEmbed V s labels) (strEmbed_injective V s labels)
    ρ rest ⟨x, hx⟩
theorem strTable_out (ρ ρ' : strRows V s labels → HashOutput) (x : HashInput) (hx : x ∉ strRows V s labels) :
    strTable V hU s o labels rest ρ (.inl (.inr x)) = strTable V hU s o labels rest ρ' (.inl (.inr x)) := by
  by_cases hV : x ∈ V
  · rw [strTable_public_mem V hU s o labels rest ρ x hV, strTable_public_mem V hU s o labels rest ρ' x hV]
    by_cases hcell : ∃ node, x = CanonGraph.Paired.cell s node labels
    · obtain ⟨node, rfl⟩ := hcell
      have he : (⟨CanonGraph.Paired.cell s node labels, hV⟩ : V) = CanonGraph.Paired.cellIn V hU s node labels := rfl
      rw [he, CanonGraph.Paired.programmed_at, CanonGraph.Paired.programmed_at]
    · have hn : ∀ node, x ≠ CanonGraph.Paired.cell s node labels := fun node h => hcell ⟨node, h⟩
      rw [CanonGraph.Paired.programmed_other V hU s labels _ ⟨x, hV⟩ hn,
        CanonGraph.Paired.programmed_other V hU s labels _ ⟨x, hV⟩ hn]
      have hout : (⟨x, hV⟩ : V) ∉ Set.range (strEmbed V s labels) := by
        rintro ⟨y, hy⟩
        apply hx
        have : y.val = x := congrArg Subtype.val hy
        rw [← this]
        exact y.property
      exact (SphincsSecurity.Concrete.UniformTableSplit.join_outside _ _ ρ rest ⟨⟨x, hV⟩, hout⟩).trans
        (SphincsSecurity.Concrete.UniformTableSplit.join_outside _ _ ρ' rest ⟨⟨x, hV⟩, hout⟩).symm
  · change SphincsSecurity.Concrete.finiteHashAnswer ∅ V _ x = SphincsSecurity.Concrete.finiteHashAnswer ∅ V _ x
    simp only [SphincsSecurity.Concrete.finiteHashAnswer, dif_neg hV]

end Fixed

section Kernel
variable (V : Finset HashInput) (s : CanonGraph.Secrets) (labels : CanonGraph.Labels)
def strHit (Charged : HashInput → Prop) (x : HashInput) (a : HashOutput) : Prop :=
  x ∈ strRows V s labels ∧ Charged x ∧ ∃ node : CanonGraph.Node, Extract.posOf x = some node.toPos ∧
    Extract.Paired.proj node.toPos a = Extract.Paired.proj node.toPos (labels node)
theorem strHit_kernel (Charged : HashInput → Prop) (x : HashInput) (hx : x ∈ strRows V s labels) :
    Pr[strHit V s labels Charged x | (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput)] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * (if Charged x then 1 else 0 : ℝ≥0∞) := by
  by_cases hO : Charged x
  · rw [if_pos hO, mul_one]
    obtain ⟨-, node₀, hpos₀, -⟩ := (mem_strRows V s labels x).mp hx
    calc Pr[strHit V s labels Charged x | (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput)]
        ≤ Pr[fun a : HashOutput => Extract.Paired.proj node₀.toPos a = Extract.Paired.proj node₀.toPos (labels node₀) |
            PMF.uniformOfFintype HashOutput] := by
          apply probEvent_mono
          rintro a - ⟨-, -, node, hpos, hlow⟩
          have hn : node = node₀ :=
            CanonGraph.toPos_injective (Option.some.inj (hpos.symm.trans hpos₀))
          subst hn
          exact hlow
      _ = (2 ^ 128 : ℝ≥0∞)⁻¹ := by
          have h := prob_proj_eq node₀.toPos (Extract.Paired.proj node₀.toPos (labels node₀))
          have hc : Fintype.card Digest = 2^128 := by simp
          simpa only [hc, Nat.cast_pow, Nat.cast_ofNat] using h
  · have hz : Pr[strHit V s labels Charged x | (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput)] = 0 :=
      probEvent_eq_zero fun _ _ h => hO h.2.1
    rw [hz]
    exact bot_le

#print axioms strTable_str
#print axioms strHit_kernel
end Kernel
end ClaudeWCT.W9.T3.Security.Wots.PairedStructural

namespace ClaudeWCT.W9.T3.Security.Wots.PairedStructural
open OracleComp OracleSpec ENNReal OracleComp.EvalDist
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Structural
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open CanonGraph
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem fixed_seen_bound (V : Finset HashInput) (hU : CanonGraph.Paired.canonInputs ⊆ V)
    (s : CanonGraph.Secrets) (o : CanonGraph.OtherHalves) (labels : CanonGraph.Labels) (rest : Rest V s labels)
    (Charged : HashInput → Prop) {α : Type} (program : OracleComp RefWorld α) :
    Pr[fun r => Seen (strHit V s labels Charged) r.2 |
      (liftM (PMF.uniformOfFintype (strRows V s labels → HashOutput)) : SPMF _) >>= fun rows =>
        𝒮[simulateQ (refImpl (strTable V hU s o labels rest rows))
          (SphincsSecurity.QueryPause.traced refObs program)]] ≤
      (2^128 : ℝ≥0∞)⁻¹ * ∑' r,
        Pr[=r | (liftM (PMF.uniformOfFintype (strRows V s labels → HashOutput)) : SPMF _) >>= fun rows =>
          𝒮[simulateQ (refImpl (strTable V hU s o labels rest rows))
            (SphincsSecurity.QueryPause.traced refObs program)]] * (chargedCount Charged r.2 : ℝ≥0∞) := by
  exact lazy_seen_le (strRows V s labels) (strTable V hU s o labels rest)
    (fun rows x hx=>strTable_str V hU s o labels rest rows x hx)
    (fun rows x hx=>strTable_out V hU s o labels rest rows (fun _=>0) x hx)
    (strHit V s labels Charged) Charged (2^128 : ℝ≥0∞)⁻¹
    (fun _ _ h=>h.1) (fun x hx=>strHit_kernel V s labels Charged x hx) program

#print axioms fixed_seen_bound
end ClaudeWCT.W9.T3.Security.Wots.PairedStructural

namespace ClaudeWCT.W9.T3.Security.Wots.PairedReference
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
attribute [local instance] Classical.propDecidable

def OtherInput (answers : Answers) (input : HashInput) : Prop :=
  ∃ position, Extract.posOf input = some position ∧ Extract.Paired.Bounded position ∧
    WotsExtract.PosSource position ∧ CanonicalRef.StructuralClass answers (CanonicalRef.sourceMessages answers) input position

def OtherQuery (answers : Answers) : Spec.Domain → Prop
  | .inl (.inr input) => OtherInput answers input
  | _ => False

noncomputable def otherCount (sample : RefSample) : Nat :=
  (sample.trace.filter fun entry => decide (OtherQuery sample.answers (.inl (.inr entry.1)))).length

def StructuralHitIn (inputs : Finset HashInput) (answers : Answers) (trace : List Entry) : Prop :=
  ∃ position input answer, (input, answer) ∈ trace ∧ input ∈ inputs ∧
    Extract.posOf input = some position ∧ Extract.Paired.Bounded position ∧
    WotsExtract.PosSource position ∧
    CanonicalRef.StructuralClass answers (CanonicalRef.sourceMessages answers) input position ∧
    Extract.Paired.HashHitAt answers position (Extract.Paired.honestInput answers position) input
end ClaudeWCT.W9.T3.Security.Wots.PairedReference

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Ref
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem topLow_short (coord index heap : Nat) (left pad right : Digest) :
    ShortRespects (shortHash (WCT9.wctTopInput coord index heap left pad right)) := by
  apply ShortRespects.shortHash
  apply short_of_le
  rw [WCT9.wctTopInput_length]
  decide

theorem topHigh_short (coord index heap : Nat) (left pad right : Digest) :
    ShortRespects (WCT9.highHash (WCT9.wctTopInput coord index heap left pad right)) := by
  intro A T hAT
  unfold WCT9.highHash
  rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind]
  have hinput : (pad64 (WCT9.wctTopInput coord index heap left pad right)).length ≤ SeccLaw.maxInputLength :=
    short_of_le _ (by rw [WCT9.wctTopInput_length]; decide)
  have hh : evalWithAnswerFn A (publicHash (WCT9.wctTopInput coord index heap left pad right)) =
      evalWithAnswerFn T (publicHash (WCT9.wctTopInput coord index heap left pad right)) := by
    change A (.inl (.inr (pad64 _))) = T (.inl (.inr (pad64 _)))
    exact hAT.public _ hinput
  rw [hh]
  rfl

theorem sharedNode_short (first : Bool) (coord index heap : Nat)
    (pads : Nat → PairRoot) (left right : Digest) :
    ShortRespects (sharedNode first coord index heap pads left right) := by
  unfold sharedNode
  split
  · unfold sharedOuterHash
    split
    · exact topLow_short _ _ _ _ _ _
    · exact topHigh_short _ _ _ _ _ _
  · split
    · split
      · exact topHigh_short _ _ _ _ _ _
      · exact topLow_short _ _ _ _ _ _
    · change ShortRespects (WCT9.ftsHash heap (WCT9.wctTopInput coord index heap left 0 right))
      rw [WCT9.ftsHash_eq]
      split
      · exact topHigh_short _ _ _ _ _ _
      · exact topLow_short _ _ _ _ _ _

theorem sharedHeap_short (first : Bool) (index coord : Nat)
    (pads : Nat → PairRoot) (leaves : List Digest) :
    ShortRespects (sharedHeap first index coord pads leaves) := by
  unfold sharedHeap
  exact ShortRespects.foldlM _ _ (fun _ _ _ =>
    ShortRespects.bind (sharedNode_short _ _ _ _ _ _ _) fun _ => ShortRespects.pure' _) _

theorem sharedLeaves_short {A T : Answers} (hAT : ShortAgree A T)
    (first : Bool) (index : Nat) (coord : Fin 9) (pads : Nat → PairRoot) :
    sharedLeaves A first index coord.val pads = sharedLeaves T first index coord.val pads := by
  unfold sharedLeaves
  apply congrArg List.ofFn
  funext physical
  have hraw : rawChild first physical.val < 128 := by
    have hp := physical.isLt
    cases first <;> simp only [rawChild, Bool.false_eq_true, ↓reduceIte] <;> omega
  exact WCT9.Wots.childRootH_congr (fun query hq => hAT query (WCT9.Wots.ftsQuery_short hq))
    (128 + physical.val) coord ⟨rawChild first physical.val, hraw⟩ _

theorem sharedNodes_short {A T : Answers} (hAT : ShortAgree A T)
    (first : Bool) (index : Nat) (coord : Fin 9) (pads : Nat → PairRoot) :
    sharedNodes A first index coord.val pads = sharedNodes T first index coord.val pads := by
  unfold sharedNodes
  rw [sharedLeaves_short hAT first index coord]
  exact sharedHeap_short first index coord.val pads _ A T hAT

theorem expectedPairRoot_short {A T : Answers} (hAT : ShortAgree A T)
    (index : Nat) (pair : Fin 4) (prev : PairRoot) :
    expectedPairRoot A index pair.val prev = expectedPairRoot T index pair.val prev := by
  have ha : firstNodes A index pair.val prev = firstNodes T index pair.val prev :=
    sharedNodes_short hAT true index ⟨2 * pair.val, by have := pair.isLt; omega⟩ _
  have hb : secondNodes A index pair.val prev = secondNodes T index pair.val prev := by
    unfold secondNodes
    rw [ha]
    exact sharedNodes_short hAT false index ⟨2 * pair.val + 1, by have := pair.isLt; omega⟩ _
  unfold expectedPairRoot
  rw [hb]

theorem forestCommitment_short {A T : Answers} (hAT : ShortAgree A T) (index : Nat) :
    forestCommitment A index = forestCommitment T index := by
  have hpair (pair : Nat) (hp : pair < 4) (prev : PairRoot) :=
    expectedPairRoot_short hAT index ⟨pair, hp⟩ prev
  dsimp only [forestCommitment, SigGolfCandidate.Research.SharedForest.forestCommitment]
  rw [hpair 0 (by decide), hpair 1 (by decide), hpair 2 (by decide), hpair 3 (by decide),
    sharedNodes_short hAT false index ⟨8, by decide⟩]

theorem sourceMessages_short {A T : Answers} (hAT : ShortAgree A T) (L : LeafAddr) :
    sourceMessages A L = sourceMessages T L := by
  unfold sourceMessages
  split
  · unfold ClaudeWCT.W9.T3M.Extract.honestPair
    rw [Ref.wotsTree_short hAT]
  · rw [forestCommitment_short hAT]

theorem layerCounterSearchAt_short (lay : Layer) (floor tree leaf : Nat) (msg : WCT9.LayerMsg)
    (counter fuel : Nat) : ShortRespects (WCT9.CanonicalPolicy.layerCounterSearchAt lay floor tree leaf msg counter fuel) := by
  induction fuel generalizing counter with
  | zero => exact ShortRespects.pure' _
  | succ fuel ih =>
      unfold WCT9.CanonicalPolicy.layerCounterSearchAt
      refine ShortRespects.bind (Ref.shortRespects_encodingHash lay _ ?_) fun answer => ?_
      · rw [← ClaudeWCT.W9.T3M.BC.pad64_layerEncodingInputP_zero, ClaudeWCT.W9.T3M.BC.layerEncodingRow_length]
        unfold SeccLaw.maxInputLength
        omega
      · split
        · exact ih _
        · exact ShortRespects.pure' _

theorem searchOf_short {A T : Answers} (hAT : ShortAgree A T) (L : LeafAddr) (remaining : Nat) :
    searchOf A (sourceMessages A) L remaining = searchOf T (sourceMessages T) L remaining := by
  unfold searchOf
  rw [sourceMessages_short hAT L]
  exact layerCounterSearchAt_short _ _ _ _ _ _ _ A T hAT

theorem referenceContext_short {A T : Answers} (hAT : ShortAgree A T) (L : LeafAddr) :
    referenceContext A (sourceMessages A) L = referenceContext T (sourceMessages T) L := by
  exact congrFun (referenceContext_congr (answers := T) (answers' := A)
    (messages := sourceMessages T) (messages' := sourceMessages A)
    (fun K remaining _ => searchOf_short hAT K remaining)) L

theorem referenceSearch_short {A T : Answers} (hAT : ShortAgree A T) (L : LeafAddr) :
    referenceSearch A (sourceMessages A) L = referenceSearch T (sourceMessages T) L := by
  exact referenceSearch_congr (answers := T) (answers' := A)
    (messages := sourceMessages T) (messages' := sourceMessages A)
    (fun K remaining _ => searchOf_short hAT K remaining) L

theorem referenceDigits_short {A T : Answers} (hAT : ShortAgree A T) (L : LeafAddr) :
    referenceDigits A (sourceMessages A) L = referenceDigits T (sourceMessages T) L := by
  unfold referenceDigits
  rw [referenceSearch_short hAT L]

theorem depth_short {A T : Answers} (hAT : ShortAgree A T) (a : ChainAddr) :
    depth A (sourceMessages A) a = depth T (sourceMessages T) a := by
  unfold depth
  rw [referenceDigits_short hAT a.key]

theorem frontierValue_short {A T : Answers} (hAT : ShortAgree A T) (a : ChainAddr) :
    frontierValue A (sourceMessages A) a = frontierValue T (sourceMessages T) a := by
  unfold frontierValue
  rw [depth_short hAT, Ref.wotsSeed_short hAT]
  exact honestChainValue_short hAT _ _ _ _ _ _

theorem referenceInput_short {A T : Answers} (hAT : ShortAgree A T) (L : LeafAddr) :
    referenceInput A (sourceMessages A) L = referenceInput T (sourceMessages T) L := by
  unfold referenceInput
  rw [referenceSearch_short hAT, sourceMessages_short hAT]
#print axioms forestCommitment_short
#print axioms referenceSearch_short
#print axioms referenceInput_short
#print axioms depth_short
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.PairedReference
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Ref
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem otherInput_short {A T : Answers} (hAT : ShortAgree A T) (x : HashInput) :
    OtherInput A x ↔ OtherInput T x := by
  have hd : CanonicalRef.depth A (CanonicalRef.sourceMessages A) =
      CanonicalRef.depth T (CanonicalRef.sourceMessages T) := funext (CanonicalRef.depth_short hAT)
  have hc (p : Extract.Pos) : CanonicalRef.StructuralClass A (CanonicalRef.sourceMessages A) x p ↔
      CanonicalRef.StructuralClass T (CanonicalRef.sourceMessages T) x p := by
    cases p <;> simp only [CanonicalRef.StructuralClass, CanonicalRef.OtherChainRow, hd]
  constructor
  · rintro ⟨p,hpos,hb,hsource,hclass⟩
    exact ⟨p,hpos,hb,hsource,(hc p).mp hclass⟩
  · rintro ⟨p,hpos,hb,hsource,hclass⟩
    exact ⟨p,hpos,hb,hsource,(hc p).mpr hclass⟩

theorem otherQuery_short : SigGolfCandidate.T3.Security.Wots.ShortCongruent OtherQuery := by
  intro A T hAT query
  rcases query with (coin | input) | coordinate
  · exact Iff.rfl
  · exact otherInput_short hAT input
  · exact Iff.rfl
#print axioms otherQuery_short
end ClaudeWCT.W9.T3.Security.Wots.PairedReference

namespace ClaudeWCT.W9.T3.Security.Wots.PairedReference
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Ref
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem pairPrev_short {A T : Answers} (hAT : ShortAgree A T) (index pair : Nat) (hp : pair ≤ 4) :
    Extract.Paired.pairPrev A index pair = Extract.Paired.pairPrev T index pair := by
  induction pair with
  | zero => rfl
  | succ pair ih =>
      simp only [Extract.Paired.pairPrev]
      rw [ih (by omega)]
      exact CanonicalRef.expectedPairRoot_short hAT index ⟨pair,by omega⟩ _

theorem firstNodes_short {A T : Answers} (hAT : ShortAgree A T) (index pair : Nat)
    (hp : pair<4) (prev : PairRoot) : firstNodes A index pair prev = firstNodes T index pair prev :=
  CanonicalRef.sharedNodes_short hAT true index ⟨2*pair,by omega⟩ _

theorem secondNodes_short {A T : Answers} (hAT : ShortAgree A T) (index pair : Nat)
    (hp : pair<4) (prev : PairRoot) : secondNodes A index pair prev = secondNodes T index pair prev := by
  unfold secondNodes
  rw [firstNodes_short hAT index pair hp]
  exact CanonicalRef.sharedNodes_short hAT false index ⟨2*pair+1,by omega⟩ _

theorem pads_short {A T : Answers} (hAT : ShortAgree A T) (index coord branch : Nat) (hc : coord<9) :
    Extract.Paired.pads A index coord branch = Extract.Paired.pads T index coord branch := by
  unfold Extract.Paired.pads
  split
  · rw [pairPrev_short hAT index 4 (by omega)]
  · rename_i hn
    split
    · rw [pairPrev_short hAT index (coord/2) (by omega)]
    · rw [pairPrev_short hAT index (coord/2) (by omega),firstNodes_short hAT index (coord/2) (by omega)]

theorem nodes_short {A T : Answers} (hAT : ShortAgree A T) (index coord : Nat) (hc : coord<9) :
    Extract.Paired.nodes A index coord = Extract.Paired.nodes T index coord := by
  unfold Extract.Paired.nodes
  split
  · rw [pairPrev_short hAT index 4 (by omega)]
    exact CanonicalRef.sharedNodes_short hAT false index ⟨8,by decide⟩ _
  · rename_i hn
    split
    · rw [pairPrev_short hAT index (coord/2) (by omega),firstNodes_short hAT index (coord/2) (by omega)]
    · rw [pairPrev_short hAT index (coord/2) (by omega),secondNodes_short hAT index (coord/2) (by omega)]

theorem honestInput_short {A T : Answers} (hAT : ShortAgree A T)
    (position : Extract.Pos) (hb : Extract.Paired.Bounded position) :
    Extract.Paired.honestInput A position = Extract.Paired.honestInput T position := by
  cases position with
  | chain | leaf | node | wctChain => exact Ref.honestInput_short hAT _ hb.legacy
  | forest => exact hb.elim
  | wctLeaf index coord child =>
      obtain ⟨hi,hc,hch⟩ := hb
      simp only [Extract.Paired.honestInput]
      rw [pads_short hAT index coord _ hc,Ref.wctEnds_short hAT index coord child hc hch]
  | wctNode index coord level node =>
      have hc := hb.legacy.2.1
      simp only [Extract.Paired.honestInput]
      rw [nodes_short hAT index coord hc,pads_short hAT index coord _ hc]

theorem honestInput_length (T : Answers) (position : Extract.Pos) :
    (Extract.Paired.honestInput T position).length ≤ SeccLaw.maxInputLength := by
  cases position with
  | chain lay tree leaf i step => exact Ref.honestInput_length T (.chain lay tree leaf i step)
  | leaf lay tree leaf => exact Ref.honestInput_length T (.leaf lay tree leaf)
  | node lay tree level node => exact Ref.honestInput_length T (.node lay tree level node)
  | forest index => exact Ref.honestInput_length T (.forest index)
  | wctChain index coord child chain step => exact Ref.honestInput_length T (.wctChain index coord child chain step)
  | wctLeaf index coord child =>
      simp only [Extract.Paired.honestInput]
      apply short_of_le
      simp only [Extract.wctLeafInputP,Extract.listInput_length',List.length_cons,List.length_drop,
        Extract.wctEnds,List.length_ofFn]
      omega
  | wctNode index coord level node =>
      simp only [Extract.Paired.honestInput]
      exact short_of_le _ (by rw [WCT9.wctTopInput_length];decide)
#print axioms honestInput_short
#print axioms honestInput_length
end ClaudeWCT.W9.T3.Security.Wots.PairedReference

namespace ClaudeWCT.W9.T3.Security.Wots.PairedStructural
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Structural
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue)
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
variable {labels : CanonGraph.Labels} {T T' : Answers}
theorem wotsTree_variant_top (hv : Variant labels T T') (tree : Nat) (ht : tree < 2 ^ Extract.treeBits 0) :
    WCT9.wotsTree T 0 tree = WCT9.wotsTree T' 0 tree := by
  obtain rfl : tree = 0 := Extract.tree_zero_of_treeBits ht rfl
  rw [WCT9.wotsTree_top, WCT9.wotsTree_top, ← Correctness.eval_buildTopTree, ← Correctness.eval_buildTopTree,
    (hv.congr (sat_buildTopTree T)).1]
theorem wotsTree_take_variant (hv : Variant labels T T') (lay : Layer) (tree : Nat)
    (ht : tree < 2 ^ Extract.treeBits lay) :
    (WCT9.wotsTree T lay tree).take (height lay) = (WCT9.wotsTree T' lay tree).take (height lay) := by
  have htree : tree < 2 ^ 40 := lt_trans (Extract.tree_lt_of_treeBits ht) (by norm_num)
  by_cases hl : lay = 0
  · subst hl
    rw [wotsTree_variant_top hv tree ht]
  · have h0 : 0 < 2 ^ height lay := by positivity
    have hc := (hv.congr (sat_buildTreeP T hl tree 0 [] (Cost.validDigits_nil lay) htree ht)).1
    rw [WCT9.eval_buildTreeP_result T hl tree 0 [] (Cost.validDigits_nil lay) h0,
      WCT9.eval_buildTreeP_result T' hl tree 0 [] (Cost.validDigits_nil lay) h0] at hc
    exact congrArg Prod.fst hc
theorem honestPair_variant (hv : Variant labels T T') (lay : Layer) (tree : Nat)
    (ht : tree < 2 ^ Extract.treeBits lay) :
    Extract.honestPair T lay tree = Extract.honestPair T' lay tree := by
  have hh : height lay - 1 < height lay := by have : 1 ≤ height lay := by fin_cases lay <;> decide
                                              omega
  have key : ∀ x, treeValue (WCT9.wotsTree T lay tree) (height lay - 1) x =
      treeValue (WCT9.wotsTree T' lay tree) (height lay - 1) x := fun x => by
    rw [← WCT9.treeValue_take _ hh, wotsTree_take_variant hv lay tree ht, WCT9.treeValue_take _ hh]
  unfold Extract.honestPair
  rw [key, key]

theorem forestCommitment_variant (hv : Variant labels T T') (index : Nat) (hi : index<2^31) :
    CanonicalRef.forestCommitment T index = CanonicalRef.forestCommitment T' index := by
  let selected := forestSelectionFromOutput 0
  let words := forestWordsFromOutput 0
  have he : evalWithAnswerFn T (buildForest index selected words) =
      evalWithAnswerFn T' (buildForest index selected words) :=
    (hv.congr (sat_buildForest T index hi selected words)).1
  have hp : (evalWithAnswerFn T (buildForest index selected words)).2 =
      (evalWithAnswerFn T' (buildForest index selected words)).2 :=
    congrArg (fun value : ForestOpening × SigGolfCandidate.Research.SharedForest.PairRoot => value.2) he
  exact (buildForest_commitment T index selected words).symm.trans
    (hp.trans (buildForest_commitment T' index selected words))

theorem sourceMessages_variant (hv : Variant labels T T') (L : LeafAddr)
    (hL : WotsExtract.SourceLeaf7 L) :
    CanonicalRef.sourceMessages T L = CanonicalRef.sourceMessages T' L := by
  unfold CanonicalRef.sourceMessages
  split
  · rename_i h3
    rw [honestPair_variant hv _ _ (Extract.routed_treeBits_succ h3 hL.1 hL.2)]
  · rw [forestCommitment_variant hv _ (Nat.mod_lt _ (by decide))]

theorem source_search_variant (hv : Variant labels T T') (L : LeafAddr)
    (hL : WotsExtract.SourceLeaf7 L) (remaining : Nat) :
    CanonicalRef.searchOf T (CanonicalRef.sourceMessages T) L remaining =
      CanonicalRef.searchOf T' (CanonicalRef.sourceMessages T') L remaining := by
  unfold CanonicalRef.searchOf
  rw [sourceMessages_variant hv L hL]
  exact (hv.congr (sat_canonical_search T _ _ _ _ _ _ _)).1

theorem referenceContext_variant (hv : Variant labels T T') (L : LeafAddr)
    (hL : WotsExtract.SourceLeaf7 L) :
    CanonicalRef.referenceContext T (CanonicalRef.sourceMessages T) L =
      CanonicalRef.referenceContext T' (CanonicalRef.sourceMessages T') L := by
  exact (CanonicalRef.context_congr_on
    (search := CanonicalRef.searchOf T (CanonicalRef.sourceMessages T))
    (search' := CanonicalRef.searchOf T' (CanonicalRef.sourceMessages T')) WCT9.CanonicalPolicy.credit WotsExtract.SourceLeaf7
    (fun _ h hp => CanonicalRef.source_parent h hp)
    (fun leaf hl remaining _ => (source_search_variant hv leaf hl remaining).symm) hL).symm

theorem referenceSearch_variant (hv : Variant labels T T') (L : LeafAddr)
    (hL : WotsExtract.SourceLeaf7 L) :
    CanonicalRef.referenceSearch T (CanonicalRef.sourceMessages T) L =
      CanonicalRef.referenceSearch T' (CanonicalRef.sourceMessages T') L := by
  change (CanonicalRef.referenceContext T (CanonicalRef.sourceMessages T) L).bind
      (CanonicalRef.searchOf T (CanonicalRef.sourceMessages T) L) =
    (CanonicalRef.referenceContext T' (CanonicalRef.sourceMessages T') L).bind
      (CanonicalRef.searchOf T' (CanonicalRef.sourceMessages T') L)
  exact congrArg₂ (@Option.bind Nat (BitVec 32 × List Nat))
    (referenceContext_variant hv L hL)
    (funext fun remaining => source_search_variant hv L hL remaining)


theorem referenceDigits_variant (hv : Variant labels T T') (L : LeafAddr)
    (hL : WotsExtract.SourceLeaf7 L) :
    CanonicalRef.referenceDigits T (CanonicalRef.sourceMessages T) L =
      CanonicalRef.referenceDigits T' (CanonicalRef.sourceMessages T') L := by
  unfold CanonicalRef.referenceDigits
  rw [referenceSearch_variant hv L hL]

theorem depth_variant (hv : Variant labels T T') (a : ChainAddr)
    (hL : WotsExtract.SourceLeaf7 a.key) :
    CanonicalRef.depth T (CanonicalRef.sourceMessages T) a =
      CanonicalRef.depth T' (CanonicalRef.sourceMessages T') a := by
  unfold CanonicalRef.depth
  rw [referenceDigits_variant hv a.key hL]

#print axioms forestCommitment_variant
#print axioms referenceContext_variant
#print axioms referenceSearch_variant
#print axioms depth_variant
end ClaudeWCT.W9.T3.Security.Wots.PairedStructural

namespace ClaudeWCT.W9.T3.Security.Wots.PairedReference
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

private def ClassDepth (D : ChainAddr → Nat) (x : HashInput) (p : Extract.Pos) : Prop :=
  match p with
  | .chain .. => ∃ (a : ChainAddr) (step : Nat), Extract.posOf x = some (.chain a.key.lay a.key.tree a.key.leaf a.chain step) ∧
      ((∀ value, x ≠ chainRow a step value) ∨ D a ≤ step)
  | _ => True

private theorem structuralClass_congr_generic (D D' : ChainAddr → Nat)
    (hdepth : ∀ a : ChainAddr, WotsExtract.SourceLeaf7 a.key →
      D a = D' a)
    {x : HashInput} {p : Extract.Pos} (hpos : Extract.posOf x = some p) (hsrc : WotsExtract.PosSource p) :
    ClassDepth D x p ↔ ClassDepth D' x p := by
  cases p with
  | chain lay tree leaf i step =>
      obtain ⟨htree, hleaf, -, -⟩ := hsrc
      have key : ∀ (a : ChainAddr) (step' : Nat),
          Extract.posOf x = some (.chain a.key.lay a.key.tree a.key.leaf a.chain step') →
          D a = D' a := by
        intro a step' h
        rw [hpos] at h
        simp only [Option.some.injEq, Extract.Pos.chain.injEq] at h
        obtain ⟨hl, ht, hlf, -, -⟩ := h
        apply hdepth a
        constructor
        · rw [← ht, ← hl]; exact htree
        · rw [← hlf, ← hl]; exact hleaf
      constructor
      · rintro ⟨a, step', h, hc⟩
        exact ⟨a, step', h, hc.imp id (fun hd => (Nat.le_of_eq (key a step' h).symm).trans hd)⟩
      · rintro ⟨a, step', h, hc⟩
        exact ⟨a, step', h, hc.imp id (fun hd => (Nat.le_of_eq (key a step' h)).trans hd)⟩
  | leaf | node | forest | wctChain | wctLeaf | wctNode => exact Iff.rfl

theorem structuralClass_congr_of_depth {T T' : Answers}
    (hdepth : ∀ a : ChainAddr, WotsExtract.SourceLeaf7 a.key →
      CanonicalRef.depth T (CanonicalRef.sourceMessages T) a = CanonicalRef.depth T' (CanonicalRef.sourceMessages T') a)
    {x : HashInput} {p : Extract.Pos} (hpos : Extract.posOf x = some p) (hsrc : WotsExtract.PosSource p) :
    CanonicalRef.StructuralClass T (CanonicalRef.sourceMessages T) x p ↔
      CanonicalRef.StructuralClass T' (CanonicalRef.sourceMessages T') x p :=
  structuralClass_congr_generic (CanonicalRef.depth T (CanonicalRef.sourceMessages T))
    (CanonicalRef.depth T' (CanonicalRef.sourceMessages T')) hdepth hpos hsrc

theorem otherInput_congr_of_depth {T T' : Answers}
    (hdepth : ∀ a : ChainAddr, WotsExtract.SourceLeaf7 a.key →
      CanonicalRef.depth T (CanonicalRef.sourceMessages T) a = CanonicalRef.depth T' (CanonicalRef.sourceMessages T') a)
    (x : HashInput) : OtherInput T x ↔ OtherInput T' x := by
  constructor
  · rintro ⟨p, hpos, hb, hsrc, hc⟩
    exact ⟨p, hpos, hb, hsrc, (structuralClass_congr_of_depth (T := T) (T' := T') hdepth hpos hsrc).mp hc⟩
  · rintro ⟨p, hpos, hb, hsrc, hc⟩
    exact ⟨p, hpos, hb, hsrc, (structuralClass_congr_of_depth (T := T) (T' := T') hdepth hpos hsrc).mpr hc⟩
#print axioms otherInput_congr_of_depth
end ClaudeWCT.W9.T3.Security.Wots.PairedReference

namespace ClaudeWCT.W9.T3.Security.Wots.PairedStructural
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)

theorem eval_sign_variant {labels : CanonGraph.Labels} {T T' : Answers}
    (hv : Variant labels T T') (published : SigGolfCandidate.T3.Cache) (request : Request) :
    evalWithAnswerFn T (PairedOuter.FullGame.authenticatedSign published request) =
      evalWithAnswerFn T' (PairedOuter.FullGame.authenticatedSign published request) :=
  (hv.congr (sat_authenticatedSign T published request)).1

theorem sign_queries_variant {labels : CanonGraph.Labels} {T T' : Answers}
    (hv : Variant labels T T') (published : SigGolfCandidate.T3.Cache) (request : Request) :
    SourceReplay.queried T (PairedOuter.FullGame.authenticatedSign published request) =
      SourceReplay.queried T' (PairedOuter.FullGame.authenticatedSign published request) :=
  (hv.congr (sat_authenticatedSign T published request)).2

#print axioms eval_sign_variant
#print axioms sign_queries_variant
end ClaudeWCT.W9.T3.Security.Wots.PairedStructural

namespace ClaudeWCT.W9.T3.Security.Wots.PairedStructural
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem referenceGame_variant {labels : CanonGraph.Labels} {T T' : Answers}
    (hv : Variant labels T T') (adversary : Final.Paired.AdversaryP) (q : Nat) :
    PairedReference.referenceGame T adversary q = PairedReference.referenceGame T' adversary q :=
  PairedReference.referenceGame_congr T T' (eval_keygen_variant hv)
    (congrArg List.length (keygen_queries_variant hv))
    (eval_sign_variant hv) (fun published request => congrArg List.length (sign_queries_variant hv published request))
    adversary q

theorem structuralClass_variant {labels : CanonGraph.Labels} {T T' : Answers}
    (hv : Variant labels T T') {x : HashInput} {p : Extract.Pos}
    (hpos : Extract.posOf x = some p) (hsrc : WotsExtract.PosSource p) :
    CanonicalRef.StructuralClass T (CanonicalRef.sourceMessages T) x p ↔
      CanonicalRef.StructuralClass T' (CanonicalRef.sourceMessages T') x p :=
  PairedReference.structuralClass_congr_of_depth (T:=T) (T':=T') (depth_variant hv) hpos hsrc

theorem otherInput_variant {labels : CanonGraph.Labels} {T T' : Answers}
    (hv : Variant labels T T') (x : HashInput) :
    PairedReference.OtherInput T x ↔ PairedReference.OtherInput T' x :=
  PairedReference.otherInput_congr_of_depth (T:=T) (T':=T') (depth_variant hv) x
end ClaudeWCT.W9.T3.Security.Wots.PairedStructural

namespace ClaudeWCT.W9.T3.Security.Wots.PairedStructural
open OracleComp OracleSpec ENNReal OracleComp.EvalDist OracleComp.DeferredSampling
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Structural
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.CanonGraph (Node Labels Secrets OtherHalves privateEquiv)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section Fixed
variable (V : Finset HashInput) (hU : CanonGraph.Paired.canonInputs ⊆ V) (s : Secrets) (o : OtherHalves) (labels : Labels)
variable (rest : Rest V s labels)
theorem strTable_variant (ρ ρ' : strRows V s labels → HashOutput) :
    Variant labels (strTable V hU s o labels rest ρ) (strTable V hU s o labels rest ρ') where
  agrees := strTable_agrees V hU s o labels rest ρ
  coin := fun _ => rfl
  priv := fun _ => rfl
  pub := fun x hx => by
    apply strTable_out V hU s o labels rest ρ ρ' x
    intro hmem
    obtain ⟨-, node, hpos, hne⟩ := (mem_strRows V s labels x).mp hmem
    have := hx node hpos
    rw [secretsOf_strTable] at this
    exact hne this
theorem hit_bridge (ρ : strRows V s labels → HashOutput) (qs : List RefWorld.Domain)
    (h : PairedReference.StructuralHitIn V (strTable V hU s o labels rest ρ) (traceOf (strTable V hU s o labels rest ρ) qs)) :
    ∃ e ∈ traceOf (strTable V hU s o labels rest ρ) qs,
      strHit V s labels (PairedReference.OtherInput (strTable V hU s o labels rest (fun _ => 0))) e.1 e.2 := by
  obtain ⟨p, x, a, hmem, hxV, hpos, hb, hsrc, hc, hne, hlow⟩ := h
  refine ⟨(x, a), hmem, ?_, ?_, ?_⟩
  · obtain ⟨node, rfl⟩ := Wots.Structural.exists_node_of_posSource hsrc
    rw [CanonGraph.Paired.honestInput_eq _ labels (strTable_agrees V hU s o labels rest ρ) node hb, secretsOf_strTable] at hne
    exact (mem_strRows V s labels x).mpr ⟨hxV, node, hpos, hne⟩
  · exact ⟨p, hpos, hb, hsrc, (structuralClass_variant (strTable_variant V hU s o labels rest ρ (fun _ => 0))
      hpos hsrc).mp hc⟩
  · obtain ⟨node, rfl⟩ := Wots.Structural.exists_node_of_posSource hsrc
    refine ⟨node, hpos, ?_⟩
    have ha : a = strTable V hU s o labels rest ρ (.inl (.inr x)) := mem_traceOf hmem
    rw [CanonGraph.Paired.honest_answer _ labels (strTable_agrees V hU s o labels rest ρ) node hb] at hlow
    change Extract.Paired.proj node.toPos a = Extract.Paired.proj node.toPos (labels node)
    rw [ha]
    exact hlow
theorem count_bridge (ρ : strRows V s labels → HashOutput) (pk : Digest) (trace : List Entry) :
    PairedReference.otherCount ⟨strTable V hU s o labels rest ρ, pk, trace⟩ =
      (trace.filter fun e => decide (PairedReference.OtherInput (strTable V hU s o labels rest (fun _ => 0)) e.1)).length := by
  unfold PairedReference.otherCount
  congr 1
  apply List.filter_congr
  intro e _
  exact decide_eq_decide.mpr (otherInput_variant (strTable_variant V hU s o labels rest ρ (fun _ => 0)) e.1)
end Fixed
noncomputable def sampleComp (adversary : Final.Paired.AdversaryP) (q : Nat) (T : Answers) : ProbComp RefSample :=
  (fun run => (⟨T, (evalWithAnswerFn T keygen).1, traceOf T run.2⟩ : RefSample)) <$> PairedReference.offlineRun T adversary q
section Bound
variable (adversary : Final.Paired.AdversaryP) (q : Nat) (V : Finset HashInput) (hU : CanonGraph.Paired.canonInputs ⊆ V) (s : Secrets)
  (o : OtherHalves) (labels : Labels) (rest : Rest V s labels)
theorem sampleComp_recorded (ρ : strRows V s labels → HashOutput) :
    𝒮[sampleComp adversary q (strTable V hU s o labels rest ρ)] =
      (fun run => (⟨strTable V hU s o labels rest ρ, (evalWithAnswerFn (strTable V hU s o labels rest ρ) keygen).1,
          traceOf (strTable V hU s o labels rest ρ) run.2⟩ : RefSample)) <$>
        𝒮[simulateQ (refImpl (strTable V hU s o labels rest ρ))
          (SphincsSecurity.QueryCap.recorded (PairedReference.referenceGame (strTable V hU s o labels rest (fun _ => 0)) adversary q))] := by
  unfold sampleComp PairedReference.offlineRun
  rw [referenceGame_variant (strTable_variant V hU s o labels rest ρ (fun _ => 0)), evalSPMF_map]
theorem recorded_pair (ρ : strRows V s labels → HashOutput) :
    (fun run => (run.1, traceOf (strTable V hU s o labels rest ρ) run.2)) <$>
        𝒮[simulateQ (refImpl (strTable V hU s o labels rest ρ))
          (SphincsSecurity.QueryCap.recorded (PairedReference.referenceGame (strTable V hU s o labels rest (fun _ => 0)) adversary q))] =
      (fun r => (r.1, r.2.toList)) <$>
        𝒮[simulateQ (refImpl (strTable V hU s o labels rest ρ))
          (SphincsSecurity.QueryPause.traced refObs (PairedReference.referenceGame (strTable V hU s o labels rest (fun _ => 0)) adversary q))] := by
  rw [← evalSPMF_map, ← evalSPMF_map, recorded_traced]
theorem fixed_bound :
    Pr[fun sample => PairedReference.StructuralHitIn V sample.answers sample.trace |
        (liftM (PMF.uniformOfFintype (strRows V s labels → HashOutput)) : SPMF _) >>= fun ρ =>
          𝒮[sampleComp adversary q (strTable V hU s o labels rest ρ)]] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * ∑' sample,
        Pr[= sample | (liftM (PMF.uniformOfFintype (strRows V s labels → HashOutput)) : SPMF _) >>= fun ρ =>
          𝒮[sampleComp adversary q (strTable V hU s o labels rest ρ)]] * (PairedReference.otherCount sample : ℝ≥0∞) := by
  set T := strTable V hU s o labels rest with hT
  set G0 := PairedReference.referenceGame (T fun _ => 0) adversary q with hG0
  set Hit := strHit V s labels (PairedReference.OtherInput (T fun _ => 0)) with hHit
  set Charged := PairedReference.OtherInput (T fun _ => 0) with hCharged
  have hlazy := fixed_seen_bound V hU s o labels rest Charged G0
  have hevent : Pr[fun sample => PairedReference.StructuralHitIn V sample.answers sample.trace |
        (liftM (PMF.uniformOfFintype (strRows V s labels → HashOutput)) : SPMF _) >>= fun ρ =>
          𝒮[sampleComp adversary q (T ρ)]] ≤
      Pr[fun r => Seen Hit r.2 | (liftM (PMF.uniformOfFintype (strRows V s labels → HashOutput)) : SPMF _) >>= fun ρ =>
          𝒮[simulateQ (refImpl (T ρ)) (SphincsSecurity.QueryPause.traced refObs G0)]] := by
    rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
    refine ENNReal.tsum_le_tsum fun ρ => mul_le_mul' le_rfl ?_
    rw [sampleComp_recorded adversary q V hU s o labels rest ρ, probEvent_map]
    have hpair := recorded_pair adversary q V hU s o labels rest ρ
    have hseen : Pr[fun r => Seen Hit r.2 |
        𝒮[simulateQ (refImpl (T ρ)) (SphincsSecurity.QueryPause.traced refObs G0)]] =
        Pr[fun z => ∃ e ∈ z.2, Hit e.1 e.2 | (fun run => (run.1, traceOf (T ρ) run.2)) <$>
          𝒮[simulateQ (refImpl (T ρ)) (SphincsSecurity.QueryCap.recorded G0)]] := by
      rw [hpair, probEvent_map]
      rfl
    rw [hseen, probEvent_map]
    apply probEvent_mono
    intro run _ h
    exact hit_bridge V hU s o labels rest ρ run.2 h
  have hcount : (∑' sample,
        Pr[= sample | (liftM (PMF.uniformOfFintype (strRows V s labels → HashOutput)) : SPMF _) >>= fun ρ =>
          𝒮[sampleComp adversary q (T ρ)]] * (PairedReference.otherCount sample : ℝ≥0∞)) =
      ∑' r, Pr[= r | (liftM (PMF.uniformOfFintype (strRows V s labels → HashOutput)) : SPMF _) >>= fun ρ =>
          𝒮[simulateQ (refImpl (T ρ)) (SphincsSecurity.QueryPause.traced refObs G0)]] *
            (chargedCount Charged r.2 : ℝ≥0∞) := by
    rw [tsum_probOutput_bind_mul, tsum_probOutput_bind_mul]
    refine tsum_congr fun ρ => congrArg _ ?_
    rw [sampleComp_recorded adversary q V hU s o labels rest ρ, tsum_probOutput_map_mul]
    have hA : ∀ run : Option (Bool × Nat) × List RefWorld.Domain,
        (PairedReference.otherCount (⟨T ρ, (evalWithAnswerFn (T ρ) keygen).1, traceOf (T ρ) run.2⟩ : RefSample) : ℝ≥0∞) =
          (fun z : Option (Bool × Nat) × List Entry => ((z.2.filter fun e => decide (Charged e.1)).length : ℝ≥0∞))
            ((fun run => (run.1, traceOf (T ρ) run.2)) run) := by
      intro run
      rw [count_bridge V hU s o labels rest ρ]
    refine (tsum_congr fun run => congrArg _ (hA run)).trans ?_
    rw [← tsum_probOutput_map_mul _ (fun run : Option (Bool × Nat) × List RefWorld.Domain =>
        (run.1, traceOf (T ρ) run.2))
      (fun z : Option (Bool × Nat) × List Entry => ((z.2.filter fun e => decide (Charged e.1)).length : ℝ≥0∞)),
      recorded_pair adversary q V hU s o labels rest ρ, tsum_probOutput_map_mul]
    rfl
  rw [hcount]
  exact hevent.trans hlazy
end Bound
def BoundOn (V : Finset HashInput) (p : SPMF RefSample) : Prop :=
  Pr[fun sample => PairedReference.StructuralHitIn V sample.answers sample.trace | p] ≤
    (2 ^ 128 : ℝ≥0∞)⁻¹ * ∑' sample, Pr[= sample | p] * (PairedReference.otherCount sample : ℝ≥0∞)
theorem boundOn_bind {X : Type} (V : Finset HashInput) (μ : SPMF X) (K : X → SPMF RefSample)
    (h : ∀ x, BoundOn V (K x)) : BoundOn V (μ >>= K) := by
  unfold BoundOn
  rw [probEvent_bind_eq_tsum, tsum_probOutput_bind_mul]
  calc (∑' x, Pr[= x | μ] * Pr[fun sample => PairedReference.StructuralHitIn V sample.answers sample.trace | K x])
      ≤ ∑' x, Pr[= x | μ] * ((2 ^ 128 : ℝ≥0∞)⁻¹ * ∑' sample, Pr[= sample | K x] * (PairedReference.otherCount sample : ℝ≥0∞)) :=
        ENNReal.tsum_le_tsum fun x => mul_le_mul' le_rfl (h x)
    _ = _ := by simp only [mul_left_comm _ (2 ^ 128 : ℝ≥0∞)⁻¹, ENNReal.tsum_mul_left]
section Assembly
noncomputable local instance instFintypeCoordinate_wotsStructural : Fintype Coordinate := coordinateFintype
noncomputable local instance instSampleableTypeFullTable_wotsStructural : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
noncomputable local instance : SampleableType Secrets := SampleableType.ofFintype _
noncomputable local instance : SampleableType OtherHalves := SampleableType.ofFintype _
noncomputable local instance : SampleableType Labels := SampleableType.ofFintype _
noncomputable local instance (U : Finset HashInput) : SampleableType (U → HashOutput) := SampleableType.ofFintype _
theorem referenceInputs_canon (adversary : Final.Paired.AdversaryP) : CanonGraph.Paired.canonInputs ⊆ PairedReference.referenceInputs adversary := by
  unfold PairedReference.referenceInputs
  exact CanonGraph.Paired.canonInputs_subset_publicUniverse.trans Finset.subset_union_left
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
        next (privateEquiv.symm (secrets, other)) (CanonGraph.Paired.programmed U hU secrets labels residual)] := by
  refine (CanonGraph.private_bind (fun privateTable => do
    let publicTable ← ($ᵗ (U → HashOutput) : ProbComp _)
    next privateTable publicTable)).trans ?_
  apply evalSPMF_bind_congr_left
  intro secrets
  apply evalSPMF_bind_congr_left
  intro other
  exact CanonGraph.Paired.uniform_bind_programmed U hU secrets (fun table => next (privateEquiv.symm (secrets, other)) table)
theorem tables_bind_spmf {R : Type} (U : Finset HashInput) (hU : CanonGraph.Paired.canonInputs ⊆ U)
    (next : FullGame.FullTable → (U → HashOutput) → ProbComp R) :
    ((liftM (PMF.uniformOfFintype FullGame.FullTable) : SPMF _) >>= fun pt =>
      (liftM (PMF.uniformOfFintype (U → HashOutput)) : SPMF _) >>= fun pub => 𝒮[next pt pub]) =
    ((liftM (PMF.uniformOfFintype Secrets) : SPMF _) >>= fun s =>
      (liftM (PMF.uniformOfFintype OtherHalves) : SPMF _) >>= fun o =>
      (liftM (PMF.uniformOfFintype Labels) : SPMF _) >>= fun labels =>
      (liftM (PMF.uniformOfFintype (U → HashOutput)) : SPMF _) >>= fun r =>
        𝒮[next (privateEquiv.symm (s, o)) (CanonGraph.Paired.programmed U hU s labels r)]) := by
  have h := tables_bind U hU next
  simp only [evalSPMF_bind, evalSPMF_uniformSample] at h
  exact h
theorem referenceComp_spmf (adversary : Final.Paired.AdversaryP) (q : Nat) :
    𝒮[PairedReference.referenceComp adversary q] =
      ((liftM (PMF.uniformOfFintype FullGame.FullTable) : SPMF _) >>= fun pt =>
        (liftM (PMF.uniformOfFintype (PairedReference.referenceInputs adversary → HashOutput)) : SPMF _) >>= fun pub =>
          𝒮[sampleComp adversary q (eagerAnswers (PairedReference.referenceInputs adversary) pt pub)]) := by
  unfold PairedReference.referenceComp
  simp only [evalSPMF_bind, evalSPMF_uniformSample]
  rfl
theorem referenceComp_bound (adversary : Final.Paired.AdversaryP) (q : Nat) :
    BoundOn (PairedReference.referenceInputs adversary) 𝒮[PairedReference.referenceComp adversary q] := by
  rw [referenceComp_spmf, tables_bind_spmf _ (referenceInputs_canon adversary)]
  refine boundOn_bind _ _ _ fun s => boundOn_bind _ _ _ fun o => boundOn_bind _ _ _ fun labels => ?_
  rw [uniform_split_bind (strEmbed (PairedReference.referenceInputs adversary) s labels)
    (strEmbed_injective (PairedReference.referenceInputs adversary) s labels)]
  refine boundOn_bind _ _ _ fun rest => ?_
  exact fixed_bound adversary q (PairedReference.referenceInputs adversary) (referenceInputs_canon adversary) s o labels rest
end Assembly
end ClaudeWCT.W9.T3.Security.Wots.PairedStructural

namespace ClaudeWCT.W9.T3.Security.Wots.PairedReference
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
theorem referenceExperiment_eq (adversary : Final.Paired.AdversaryP) (q : Nat) :
    referenceExperiment adversary q = liftM (referenceComp adversary q) := rfl
theorem reference_structural_in_le (adversary : Final.Paired.AdversaryP) (q : Nat) :
    Pr[fun sample => StructuralHitIn (referenceInputs adversary) sample.answers sample.trace |
        referenceExperiment adversary q] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * ∑' sample, referenceExperiment adversary q sample * (otherCount sample : ℝ≥0∞) := by
  have h := PairedStructural.referenceComp_bound adversary q
  unfold PairedStructural.BoundOn at h
  rw [referenceExperiment_eq, probEvent_liftM_pmf]
  simp only [liftM_pmf_apply]
  exact h

#print axioms reference_structural_in_le
end ClaudeWCT.W9.T3.Security.Wots.PairedReference

