import SigGolfCandidate.OuterCanonPairedTrials
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option maxErrors 30
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterCanonBase.Paired
open ClaudeWCT
open OracleComp OracleSpec OracleComp.EvalDist OracleComp.DeferredSampling ENNReal
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SphincsSecurity.Concrete FiniteGraphSampling
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers)
attribute [local instance] Classical.propDecidable
theorem ftsLabel_congr (left right : Labels) (index : Fin (2^31)) (coord : Fin 9) (level c : Nat)
    (h : ∀other:Node,other.depth<4096*(5+7*coord.val+level)→left other=right other) :
    ftsLabel left index coord level c=ftsLabel right index coord level c := by
  unfold ftsLabel
  split_ifs with hzero hc
  · rw [h _ (by simp only [Node.depth];omega)]
  · rfl
  all_goals
    cases hn:ftsNodeAt index coord (level-1) c with
    | none=>rfl
    | some n=>
      have hd : ∀ j < wTrialCap n.1.coord.val n.1.level.val,
          left (.wctNode (wWithNonce n j)) = right (.wctNode (wWithNonce n j)) := fun j _ =>
        h _ (depth_wWithNonce_lt n j (by rw [ftsNodeAt_level hn,ftsNodeAt_coord hn]; omega))
      simp only [wSelNode_label_congr hd]

theorem pads_congr (left right : Labels) (index : Fin (2^31)) (coord : Fin 9) (branch : Nat)
    (h : ∀other:Node,other.depth<4096*(4+7*coord.val)→left other=right other) :
    pads left index coord branch=pads right index coord branch := by
  unfold pads
  split_ifs with hz hodd
  · rfl
  all_goals
    dsimp only
    apply Prod.ext
    all_goals dsimp only;apply ftsLabel_congr;intro other ho;apply h;dsimp at ho;omega

theorem cell_congr (secrets : Secrets) (node : Node) (left right : Labels)
    (h : ∀other:Node,other.depth<node.depth→left other=right other) :
    cell secrets node left=cell secrets node right := by
  cases node with
  | wctLeaf L=>
    have hends : (List.ofFn fun t:Fin 6=>wctEndLabel left (L.index,L.coord,L.child,t))=
        (List.ofFn fun t:Fin 6=>wctEndLabel right (L.index,L.coord,L.child,t)) := by
      congr 1
      funext t
      unfold wctEndLabel
      rw [h _ (by show 3<4096*(4+7*L.coord.val);omega)]
    have hpad:=pads_congr left right L.index L.coord (L.child.val%2)
      (fun other ho=>h other ho)
    simp only [cell,hends,hpad]
  | wctNode n=>
    have hl:=ftsLabel_congr left right n.1.index n.1.coord n.1.level.val (2*n.1.idx.val)
      (fun other ho=>h other (by rw [depth_wctNode]; omega))
    have hr:=ftsLabel_congr left right n.1.index n.1.coord n.1.level.val (2*n.1.idx.val+1)
      (fun other ho=>h other (by rw [depth_wctNode]; omega))
    have hpad:=pads_congr left right n.1.index n.1.coord (n.1.idx.val/2)
      (fun other ho=>h other (by rw [depth_wctNode]; omega))
    have ha : WActive left n ↔ WActive right n :=
      wActiveCongr left right n (fun j hj => h _ (depth_wtrial_lt n hj))
    simp only [cell,hl,hr,hpad,ha]
  | _=>exact OuterCanonBase.cell_congr secrets _ left right h

/-- Every paired cell has its position's honest length (length-aware decoding, C3). -/
theorem posOf_cell (secrets : Secrets) (node : Node) (labels : Labels) (hp : ¬ PhantomAt node labels) :
    Extract.posOf (cell secrets node labels)=some node.toPos :=
  Extract.posOf_eq (toPos_bounded node) (cell_length secrets node labels hp) (hdrBlock_cell secrets node labels hp)

theorem cell_eq_of_posOf {input : HashInput} {node node' : Node} (secrets : Secrets) (labels : Labels)
    (hpos : Extract.posOf input=some node.toPos) (h : input=cell secrets node' labels) :
    node'.toPos = node.toPos ∧ ¬ PhantomAt node' labels := by
  subst h
  by_cases hp : PhantomAt node' labels
  · rw [cell_of_phantomAt (secrets := secrets) hp, posOf_phantomOf hp] at hpos; cases hpos
  · rw [posOf_cell secrets node' labels hp] at hpos
    exact ⟨Option.some.inj hpos, hp⟩

noncomputable def canonInputs : Finset HashInput := SeccLaw.publicUniverse
attribute [irreducible] canonInputs

theorem cell_length_le (secrets : Secrets) (node : Node) (labels : Labels) :
    (cell secrets node labels).length≤4096 := by
  cases node with
  | wctLeaf L=>
    simp only [cell,Extract.wctLeafInputP]
    rw [Cost.pad64_length,Extract.listInput_length']
    simp only [List.length_cons,List.length_drop,List.length_ofFn]
    omega
  | wctNode n=>
    by_cases ha : WActive labels n
    · rw [cell_wctNode_active ha,pad64_nodeInputP,nodeInputP,block4]
      simp only [List.length_append,bytesLE_length]
      omega
    · rw [cell_wctNode_inactive ha, wphantom_length]; omega
  | chain v=>exact OuterCanonBase.cell_length_le secrets (.chain v) labels
  | leaf v=>exact OuterCanonBase.cell_length_le secrets (.leaf v) labels
  | node v=>exact OuterCanonBase.cell_length_le secrets (.node v) labels
  | wctChain v=>exact OuterCanonBase.cell_length_le secrets (.wctChain v) labels
  | forest v=>exact OuterCanonBase.cell_length_le secrets (.forest v) labels

set_option maxRecDepth 100000 in
theorem cell_mem (secrets : Secrets) (node : Node) (labels : Labels) : cell secrets node labels∈canonInputs := by
  rw [canonInputs]
  exact SeccLaw.mem_publicUniverse _ (cell_length_le secrets node labels)
theorem canonInputs_subset_publicUniverse : canonInputs⊆SeccLaw.publicUniverse := by
  rw [canonInputs]
noncomputable def cellIn (U : Finset HashInput) (hU : canonInputs ⊆ U) (secrets : Secrets)
    (node : Node) (labels : Labels) : U :=
  ⟨cell secrets node labels, hU (cell_mem secrets node labels)⟩
theorem cellIn_separated (U : Finset HashInput) (hU : canonInputs ⊆ U) (secrets : Secrets) :
    Separated (cellIn U hU secrets) := by
  intro left right hne before after heq
  exact cell_separated secrets left right hne before after (congrArg Subtype.val heq)
theorem cellIn_injective (U : Finset HashInput) (hU : canonInputs ⊆ U) (secrets : Secrets) (labels : Labels) :
    Function.Injective (fun node => cellIn U hU secrets node labels) := by
  intro left right heq
  by_contra hne
  exact cellIn_separated U hU secrets left right hne labels labels heq
noncomputable def graph (U : Finset HashInput) (hU : canonInputs ⊆ U) (secrets : Secrets)
    (table : U → HashOutput) : Labels :=
  read (cellIn U hU secrets) advance table order (fun _ => 0)
noncomputable def programmed (U : Finset HashInput) (hU : canonInputs ⊆ U) (secrets : Secrets)
    (labels : Labels) (residual : U → HashOutput) : U → HashOutput :=
  patch (fun node => cellIn U hU secrets node labels) labels residual order
section Laws
variable (U : Finset HashInput) (hU : canonInputs ⊆ U)
noncomputable local instance instSampleableTypeHashOutput_canonGraph : SampleableType HashOutput := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeLabels : SampleableType Labels := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_canonGraph : SampleableType (U → HashOutput) := SampleableType.ofFintype _
theorem programmed_at (secrets : Secrets) (labels : Labels) (residual : U → HashOutput) (node : Node) :
    programmed U hU secrets labels residual (cellIn U hU secrets node labels) = labels node :=
  patch_at _ (cellIn_injective U hU secrets labels) labels residual order node (mem_order node)
theorem programmed_other (secrets : Secrets) (labels : Labels) (residual : U → HashOutput) (query : U)
    (hquery : ∀ node, query.val ≠ cell secrets node labels) :
    programmed U hU secrets labels residual query = residual query := by
  apply patch_of_forall_ne
  intro node _ heq
  exact hquery node (congrArg Subtype.val heq)
theorem read_eq_plant (secrets : Secrets) (nodes : List Node) (hnodup : nodes.Nodup) (before : Labels) :
    𝒮[do
      let table ← ($ᵗ (U → HashOutput) : ProbComp _)
      pure (read (cellIn U hU secrets) advance table nodes before, table)] =
      𝒮[plant (cellIn U hU secrets) advance nodes before] :=
  evalDist_read_eq_plant (cellIn U hU secrets) advance (cellIn_separated U hU secrets) nodes hnodup before
theorem replay_eq_programmed (secrets : Secrets) (labels : Labels) (residual : U → HashOutput)
    (nodes : List Node) (hsorted : nodes.Pairwise (fun left right => left.depth ≤ right.depth))
    (before : Labels) (hagrees : ∀ node, node ∉ nodes → before node = labels node) :
    replay (cellIn U hU secrets) advance labels residual nodes before =
      (labels, patch (fun node => cellIn U hU secrets node labels) labels residual nodes) := by
  induction nodes generalizing before with
  | nil =>
      have hbefore : before = labels := funext fun node => hagrees node (by simp)
      rw [hbefore]
      rfl
  | cons first rest ih =>
      obtain ⟨hdepth, hsorted⟩ := List.pairwise_cons.mp hsorted
      have hinput : cellIn U hU secrets first before = cellIn U hU secrets first labels := by
        apply Subtype.ext
        apply cell_congr
        intro other hother
        apply hagrees
        intro hmem
        rcases List.mem_cons.mp hmem with heq | hmem
        · rw [heq] at hother; omega
        · have := hdepth _ hmem; omega
      have hafter : ∀ node, node ∉ rest → advance first (labels first) before node = labels node := by
        intro node hnode
        unfold advance
        by_cases heq : node = first
        · subst node; rw [Function.update_self]
        · rw [Function.update_of_ne heq]
          exact hagrees node (fun hmem => (List.mem_cons.mp hmem).elim heq hnode)
      rw [replay, ih hsorted _ hafter, patch, hinput]
theorem plant_eq_uniform_programmed (secrets : Secrets) :
    𝒮[plant (cellIn U hU secrets) advance order (fun _ => 0)] =
      𝒮[do
        let labels ← ($ᵗ Labels : ProbComp _)
        let residual ← ($ᵗ (U → HashOutput) : ProbComp _)
        pure (labels, programmed U hU secrets labels residual)] := by
  rw [evalDist_plant_eq_replay _ _ _ order_nodup]
  apply evalSPMF_bind_congr_left
  intro labels
  apply evalSPMF_bind_congr_left
  intro residual
  rw [replay_eq_programmed U hU secrets labels residual order order_sorted _
    (fun node hnode => (hnode (mem_order node)).elim)]
  rfl
theorem graph_eq_uniform_programmed (secrets : Secrets) :
    𝒮[do
      let table ← ($ᵗ (U → HashOutput) : ProbComp _)
      pure (graph U hU secrets table, table)] =
      𝒮[do
        let labels ← ($ᵗ Labels : ProbComp _)
        let residual ← ($ᵗ (U → HashOutput) : ProbComp _)
        pure (labels, programmed U hU secrets labels residual)] :=
  (read_eq_plant U hU secrets order order_nodup _).trans (plant_eq_uniform_programmed U hU secrets)
theorem graph_bind_eq_uniform_programmed {Result : Type} (secrets : Secrets)
    (next : Labels → (U → HashOutput) → ProbComp Result) :
    𝒮[do
      let table ← ($ᵗ (U → HashOutput) : ProbComp _)
      next (graph U hU secrets table) table] =
      𝒮[do
        let labels ← ($ᵗ Labels : ProbComp _)
        let residual ← ($ᵗ (U → HashOutput) : ProbComp _)
        next labels (programmed U hU secrets labels residual)] := by
  have h := congrArg (fun law : SPMF (Labels × (U → HashOutput)) =>
    law >>= fun result => 𝒮[next result.1 result.2]) (graph_eq_uniform_programmed U hU secrets)
  simpa only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind] using h
theorem uniform_bind_programmed {Result : Type} (secrets : Secrets) (next : (U → HashOutput) → ProbComp Result) :
    𝒮[do let table ← ($ᵗ (U → HashOutput) : ProbComp _); next table] =
      𝒮[do
        let labels ← ($ᵗ Labels : ProbComp _)
        let residual ← ($ᵗ (U → HashOutput) : ProbComp _)
        next (programmed U hU secrets labels residual)] :=
  graph_bind_eq_uniform_programmed U hU secrets (fun _ table => next table)
end Laws

#print axioms uniform_bind_programmed
end OuterCanonBase.Paired
