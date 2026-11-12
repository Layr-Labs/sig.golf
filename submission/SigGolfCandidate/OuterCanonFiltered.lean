import SigGolfCandidate.OuterCanonPairedLaws
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option maxErrors 30
set_option Elab.async false
open ClaudeWCT
namespace OuterCanonBase.Paired.Filtered
open OracleComp OracleSpec OracleComp.EvalDist OracleComp.DeferredSampling ENNReal
open SphincsSecurity.Concrete FiniteGraphSampling
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def Used : Node → Prop
  | .forest _ => False
  | .wctNode n => first n.1.coord.val → n.1.level.val < 5
  | _ => True
instance (n : Node) : Decidable (Used n) := by unfold Used; cases n <;> infer_instance

theorem used_iff_bounded (n : Node) : Used n ↔ Extract.Paired.Bounded n.toPos := by
  cases n with
  | forest i => rfl
  | wctNode n =>
      simp only [Used, Node.toPos, Extract.Paired.Bounded, Extract.Paired.first,
        decide_eq_true_eq]
      exact ⟨fun h => ⟨toPos_bounded (.wctNode n), h⟩, fun h => h.2⟩
  | chain p =>
      change True ↔ (Node.chain p).toPos.Bounded
      exact ⟨fun _ => toPos_bounded _, fun _ => trivial⟩
  | leaf p =>
      change True ↔ (Node.leaf p).toPos.Bounded
      exact ⟨fun _ => toPos_bounded _, fun _ => trivial⟩
  | node p =>
      change True ↔ (Node.node p).toPos.Bounded
      exact ⟨fun _ => toPos_bounded _, fun _ => trivial⟩
  | wctChain p =>
      change True ↔ (Node.wctChain p).toPos.Bounded
      exact ⟨fun _ => toPos_bounded _, fun _ => trivial⟩
  | wctLeaf p =>
      change True ↔ (Node.wctLeaf p).toPos.Bounded
      exact ⟨fun _ => toPos_bounded _, fun _ => trivial⟩

theorem treeLabel_congr (left right : Labels) (lay : Layer) (tree : Fin (2^31)) (level c : Nat)
    (h : ∀ other : Node, Used other → other.depth < levelDepth lay level → left other = right other) :
    treeLabel left lay tree level c = treeLabel right lay tree level c := by
  unfold treeLabel
  split_ifs with hzero
  · cases leafAt lay tree c with
    | none => rfl
    | some L => simp only; rw [h (.leaf L) trivial (by simp only [Node.depth, levelDepth]; omega)]
  · cases hn : treeNodeAt lay tree (level - 1) c with
    | none => rfl
    | some n =>
        simp only
        have hl := treeNodeAt_level hn
        have hlay := treeNodeAt_lay hn
        rw [selNode_label_congr (fun j hj => h _ trivial (by
          have := depth_withNonce_lt n hj (level := level) (by omega)
          rw [hlay] at this; exact this))]

theorem ftsLabel_congr (left right : Labels) (index : Fin (2^31)) (coord : Fin 9) (level c : Nat)
    (hl : first coord.val → level ≤ 5)
    (h : ∀ other : Node, Used other → other.depth < 4096 * (5 + 7 * coord.val + level) → left other = right other) :
    Paired.ftsLabel left index coord level c = Paired.ftsLabel right index coord level c := by
  unfold Paired.ftsLabel
  split_ifs with hzero hc
  · rw [h (.wctLeaf ⟨index,coord,⟨rawLeaf coord.val c,hc⟩⟩) trivial (by simp only [Node.depth]; omega)]
  · rfl
  all_goals
    cases hn : ftsNodeAt index coord (level-1) c with
    | none => rfl
    | some n =>
      have hu : ∀ j, Used (.wctNode (wWithNonce n j)) := by
        intro j
        change first n.1.coord.val → n.1.level.val < 5
        rw [ftsNodeAt_level hn, ftsNodeAt_coord hn]
        intro hf
        have := hl hf
        omega
      have hd : ∀ j < wTrialCap n.1.coord.val n.1.level.val,
          left (.wctNode (wWithNonce n j)) = right (.wctNode (wWithNonce n j)) := fun j _ =>
        h _ (hu j) (depth_wWithNonce_lt n j (by rw [ftsNodeAt_level hn,ftsNodeAt_coord hn]; omega))
      simp only [wSelNode_label_congr hd]

theorem pads_congr (left right : Labels) (index : Fin (2^31)) (coord : Fin 9) (branch : Nat)
    (h : ∀other : Node, Used other → other.depth<4096*(4+7*coord.val) → left other=right other) :
    Paired.pads left index coord branch = Paired.pads right index coord branch := by
  unfold Paired.pads
  split_ifs with hz hodd
  · rfl
  · dsimp only
    apply Prod.ext
    all_goals
      dsimp only
      apply ftsLabel_congr
      · intro _; omega
      · intro other hu ho; apply h other hu; dsimp at ho; omega
  · dsimp only
    apply Prod.ext
    all_goals
      dsimp only
      apply ftsLabel_congr
      · intro hf
        unfold first at hf
        dsimp only at hf
        omega
      · intro other hu ho; apply h other hu; dsimp at ho; omega

theorem cell_congr_nonforest (secrets : Secrets) (node : Node)
    (hnf : ∀i, node≠.forest i) (left right : Labels)
    (h : ∀ other : Node, Used other → other.depth < node.depth → left other = right other) :
    Paired.cell secrets node left = Paired.cell secrets node right := by
  cases node with
  | chain p =>
      change inputW (seedsOf secrets) p (chainLabels left) =
        inputW (seedsOf secrets) p (chainLabels right)
      unfold inputW priorW
      split_ifs with hz
      · rfl
      · have hd := h (.chain (ChainGraph.predecessor p)) trivial (by
          simp only [Node.depth, ChainGraph.predecessor]; omega)
        simp only [chainLabels, hd]
  | leaf L =>
      have hends : (List.range (chainCount L.1.lay)).map (endLabel secrets left L.1) =
          (List.range (chainCount L.1.lay)).map (endLabel secrets right L.1) := by
        apply List.map_congr_left
        intro i _
        -- C3 (#866): a leaf reads the used half of its chains' last-step labels (`endLabel` via `endPt`).
        unfold endLabel
        rw [h (.chain _) trivial (by simp only [Node.depth, endPt]; exact Nat.mod_lt _ (by decide))]
      simp only [Paired.cell, OuterCanonBase.cell, hends]
  | node n =>
      have hl := treeLabel_congr left right n.1.lay n.1.tree n.1.level.val (2*n.1.idx.val)
        (fun other ho hd => h other ho (by rw [depth_node]; omega))
      have hr := treeLabel_congr left right n.1.lay n.1.tree n.1.level.val (2*n.1.idx.val+1)
        (fun other ho hd => h other ho (by rw [depth_node]; omega))
      have ha : Active left n ↔ Active right n :=
        activeCongr left right n (fun j hj => h _ trivial (depth_trial_lt n hj))
      simp only [Paired.cell, OuterCanonBase.cell, hl, hr, ha]
  | wctChain p =>
      have hv : wctValueL secrets left p.1 p.2.val = wctValueL secrets right p.1 p.2.val := by
        unfold wctValueL
        split_ifs with hz
        · rfl
        · rw [h (.wctChain (p.1,⟨(p.2.val-1)%4,Nat.mod_lt _ (by decide)⟩)) trivial (by simp only [Node.depth]; have := p.2.isLt; omega)]
      simp only [Paired.cell, OuterCanonBase.cell, hv]
  | wctLeaf L =>
      have hends : (List.ofFn fun t : Fin 6 => wctEndLabel left (L.index,L.coord,L.child,t)) =
          (List.ofFn fun t : Fin 6 => wctEndLabel right (L.index,L.coord,L.child,t)) := by
        congr 1
        funext t
        unfold wctEndLabel
        rw [h (.wctChain ((L.index,L.coord,L.child,t),3)) trivial (by show 3<4096*(4+7*L.coord.val); omega)]
      have hpad := pads_congr left right L.index L.coord (L.child.val%2)
        (fun other ho hd => h other ho hd)
      simp only [Paired.cell,hends,hpad]
  | wctNode n =>
      have hh : first n.1.coord.val → n.1.level.val ≤ 5 := fun _ => Nat.le_of_lt_succ n.1.level.isLt
      have hl := ftsLabel_congr left right n.1.index n.1.coord n.1.level.val (2*n.1.idx.val) hh
        (fun other ho hd => h other ho (by rw [depth_wctNode]; omega))
      have hr := ftsLabel_congr left right n.1.index n.1.coord n.1.level.val (2*n.1.idx.val+1) hh
        (fun other ho hd => h other ho (by rw [depth_wctNode]; omega))
      have hpad := pads_congr left right n.1.index n.1.coord (n.1.idx.val/2)
        (fun other ho hd => h other ho (by rw [depth_wctNode]; omega))
      have ha : WActive left n ↔ WActive right n := by
        by_cases hu : Used (.wctNode n)
        · exact wActiveCongr left right n (fun j hj => h _ hu (depth_wtrial_lt n hj))
        · have h3 : ¬ OuterExtractGround.ftsNonceLevel n.1.coord.val n.1.level.val := fun h3 =>
            hu (fun _ => by exact OuterExtractBounds.used _ _ h3 ‹first _›)
          unfold WActive
          rw [wTrialCap_off h3]
          exact ⟨fun hx => ⟨hx.1, fun j hj => by omega⟩, fun hx => ⟨hx.1, fun j hj => by omega⟩⟩
      simp only [Paired.cell,hl,hr,hpad,ha]
  | forest i => exact (hnf i rfl).elim

theorem cell_congr (secrets : Secrets) (node : Node) (hu : Used node) (left right : Labels)
    (h : ∀ other : Node, Used other → other.depth < node.depth → left other = right other) :
    Paired.cell secrets node left = Paired.cell secrets node right := by
  apply cell_congr_nonforest secrets node _ left right h
  intro i hi
  subst node
  exact hu

end OuterCanonBase.Paired.Filtered
namespace OuterCanonBase.Paired.Filtered
open OracleComp OracleSpec OracleComp.EvalDist OracleComp.DeferredSampling ENNReal
open SphincsSecurity.Concrete FiniteGraphSampling
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

noncomputable def order : List Node := OuterCanonBase.order.filter (fun n => decide (Used n))
theorem mem_order (n : Node) : n ∈ order ↔ Used n := by
  simp only [order, List.mem_filter, OuterCanonBase.mem_order, true_and, decide_eq_true_eq]
theorem order_nodup : order.Nodup := OuterCanonBase.order_nodup.filter _
theorem order_sorted : order.Pairwise (fun left right => left.depth ≤ right.depth) :=
  OuterCanonBase.order_sorted.filter _

noncomputable def programmed (U : Finset HashInput) (hU : Paired.canonInputs ⊆ U) (secrets : Secrets)
    (labels : Labels) (residual : U → HashOutput) : U → HashOutput :=
  patch (fun node => Paired.cellIn U hU secrets node labels) labels residual order

theorem programmed_at (U : Finset HashInput) (hU : Paired.canonInputs ⊆ U) (secrets : Secrets)
    (labels : Labels) (residual : U → HashOutput) (node : Node) (hu : Used node) :
    programmed U hU secrets labels residual (Paired.cellIn U hU secrets node labels) = labels node :=
  patch_at _ (Paired.cellIn_injective U hU secrets labels) labels residual order node ((mem_order node).2 hu)

theorem programmed_other (U : Finset HashInput) (hU : Paired.canonInputs ⊆ U) (secrets : Secrets)
    (labels : Labels) (residual : U → HashOutput) (query : U)
    (hquery : ∀ node, Used node → query.val ≠ Paired.cell secrets node labels) :
    programmed U hU secrets labels residual query = residual query := by
  apply patch_of_forall_ne
  intro node hn heq
  exact hquery node ((mem_order node).1 hn) (congrArg Subtype.val heq)

theorem replay_snd (U : Finset HashInput) (hU : Paired.canonInputs ⊆ U)
    (secrets : Secrets) (labels : Labels) (residual : U → HashOutput)
    (nodes : List Node) (hsorted : nodes.Pairwise (fun left right => left.depth ≤ right.depth))
    (hused : ∀node∈nodes, Used node)
    (before : Labels) (hagrees : ∀node, Used node → node∉nodes → before node=labels node) :
    (replay (Paired.cellIn U hU secrets) advance labels residual nodes before).2 =
      patch (fun node => Paired.cellIn U hU secrets node labels) labels residual nodes := by
  induction nodes generalizing before with
  | nil => rfl
  | cons first rest ih =>
    obtain ⟨hdepth,hsorted⟩ := List.pairwise_cons.mp hsorted
    have hinput : Paired.cellIn U hU secrets first before = Paired.cellIn U hU secrets first labels := by
      apply Subtype.ext
      apply cell_congr secrets first (hused first (by simp))
      intro other hu ho
      apply hagrees other hu
      intro hmem
      rcases List.mem_cons.mp hmem with heq|hmem
      · rw [heq] at ho; omega
      · have := hdepth _ hmem; omega
    have hafter : ∀node, Used node → node∉rest → advance first (labels first) before node=labels node := by
      intro node hu hn
      unfold advance
      by_cases heq : node=first
      · subst node; rw [Function.update_self]
      · rw [Function.update_of_ne heq]
        exact hagrees node hu (fun hm => (List.mem_cons.mp hm).elim heq hn)
    simp only [replay, patch]
    rw [ih hsorted (fun node hn => hused node (List.mem_cons_of_mem _ hn)) _ hafter, hinput]

section Laws
variable (U : Finset HashInput) (hU : Paired.canonInputs ⊆ U)
noncomputable local instance : SampleableType HashOutput := SampleableType.ofFintype _
noncomputable local instance : SampleableType Labels := SampleableType.ofFintype _
noncomputable local instance : SampleableType (U → HashOutput) := SampleableType.ofFintype _

theorem plant_bind_programmed {Result : Type} (secrets : Secrets)
    (next : (U → HashOutput) → ProbComp Result) :
    𝒮[do let result ← plant (Paired.cellIn U hU secrets) advance order (fun _ => 0); next result.2] =
      𝒮[do
        let labels ← ($ᵗ Labels : ProbComp _)
        let residual ← ($ᵗ (U → HashOutput) : ProbComp _)
        next (programmed U hU secrets labels residual)] := by
  rw [evalSPMF_bind, evalDist_plant_eq_replay _ _ _ order_nodup]
  simp only [evalSPMF_bind, bind_assoc, evalSPMF_pure, pure_bind]
  apply bind_congr
  intro labels
  apply bind_congr
  intro residual
  rw [replay_snd U hU secrets labels residual order order_sorted
    (fun node hn => (mem_order node).1 hn) _
    (fun node hu hn => (hn ((mem_order node).2 hu)).elim)]
  rfl

theorem uniform_bind_programmed {Result : Type} (secrets : Secrets)
    (next : (U → HashOutput) → ProbComp Result) :
    𝒮[do let table ← ($ᵗ (U → HashOutput) : ProbComp _); next table] =
      𝒮[do
        let labels ← ($ᵗ Labels : ProbComp _)
        let residual ← ($ᵗ (U → HashOutput) : ProbComp _)
        next (programmed U hU secrets labels residual)] := by
  have h := congrArg (fun law : SPMF (Labels × (U → HashOutput)) =>
      law >>= fun result => 𝒮[next result.2])
    (Paired.read_eq_plant U hU secrets order order_nodup (fun _ => 0))
  have h' : 𝒮[do let table ← ($ᵗ (U → HashOutput) : ProbComp _); next table] =
      𝒮[do let result ← plant (Paired.cellIn U hU secrets) advance order (fun _ => 0); next result.2] := by
    simpa only [evalSPMF_bind,evalSPMF_pure,bind_assoc,pure_bind] using h
  exact h'.trans (plant_bind_programmed U hU secrets next)
end Laws

def Agrees (answers : Correctness.Answers) (labels : Labels) : Prop :=
  ∀node, Used node → answers (.inl (.inr (Paired.cell (secretsOf answers) node labels)))=labels node

theorem agrees_of_programmed (U : Finset HashInput) (hU : Paired.canonInputs ⊆ U)
    (answers : Correctness.Answers) (labels : Labels) (residual : U → HashOutput)
    (hpub : ∀x : U, answers (.inl (.inr x.val))=programmed U hU (secretsOf answers) labels residual x) :
    Agrees answers labels := by
  intro node hu
  have h := hpub (Paired.cellIn U hU (secretsOf answers) node labels)
  rw [programmed_at _ _ _ _ _ _ hu] at h
  exact h
end OuterCanonBase.Paired.Filtered


#print axioms OuterCanonBase.Paired.Filtered.uniform_bind_programmed
