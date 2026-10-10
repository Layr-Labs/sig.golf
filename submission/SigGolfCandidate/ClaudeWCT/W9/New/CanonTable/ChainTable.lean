import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.CanonGraphHonest
import SigGolfCandidate.ClaudeWCT.GuessV2.WorldHash
import SigGolfCandidate.ClaudeWCT.GuessV2.FamilyEngine

namespace ClaudeWCT.W9.CanonTable
open OracleComp OracleSpec
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs
open ClaudeWCT.W9.T3.Security.CanonGraph
open Correctness (Answers)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
theorem chainAddr_eq : Guess.ChainAddr = WctAddr := rfl
theorem gCoord_eq : Guess.GCoord = WctPoint := rfl
theorem cell_wctChain (secrets : Secrets) (labels : Labels) (p : WctPoint) :
    cell secrets (.wctChain p) labels = Guess.probeInput p.1 p.2 (wctValueL secrets labels p.1 p.2.val) := rfl
theorem probeInput_hdr (a : WctAddr) (p : Fin 4) (c : Digest) :
    Extract.hdrBlock (Guess.probeInput a p c) = bytesLE 16 (Node.toPos (.wctChain (a, p))).hdr :=
  Extract.hdrBlock_wctChainInput _ _ _ _ _ _
theorem probeInput_inj {a a' : WctAddr} {p p' : Fin 4} {c c' : Digest}
    (h : Guess.probeInput a p c = Guess.probeInput a' p' c') : a = a' ∧ p = p' ∧ c = c' := by
  have hh := probeInput_hdr a p c
  rw [h, probeInput_hdr] at hh
  have hn : (Node.wctChain (a', p') : Node) = .wctChain (a, p) :=
    toPos_injective (Extract.Pos.hdr_injective (toPos_bounded _) (toPos_bounded _) (bytesLE_injective hh))
  simp only [Node.wctChain.injEq, Prod.mk.injEq] at hn
  obtain ⟨rfl, rfl⟩ := hn
  refine ⟨rfl, rfl, ?_⟩
  unfold Guess.probeInput at h
  rw [Extract.wctChainInput_block4, Extract.wctChainInput_block4] at h
  exact (block4_injective h).2.2.2
theorem decodeProbe_probe (a : WctAddr) (p : Fin 4) (c : Digest) :
    Guess.decodeProbe (Guess.probeInput a p c) = some ((a, p), c) := by
  have h : ∃ q : Guess.GCoord × Digest, Guess.probeInput a p c = Guess.probeInput q.1.1 q.1.2 q.2 :=
    ⟨((a, p), c), rfl⟩
  delta Guess.decodeProbe
  rw [dif_pos h]
  obtain ⟨h1, h2, h3⟩ := probeInput_inj (Classical.choose_spec h).symm
  exact congrArg some (Prod.ext (Prod.ext h1 h2) h3)
theorem decodeProbe_none {x : HashInput} (h : Guess.decodeProbe x = none) (a : WctAddr) (p : Fin 4) (c : Digest) :
    x ≠ Guess.probeInput a p c := by
  intro hx
  rw [hx, decodeProbe_probe] at h
  cases h
theorem probeInput_mem (a : WctAddr) (p : Fin 4) (c : Digest) : Guess.probeInput a p c ∈ canonInputs := by
  obtain ⟨K, hK⟩ := ClaudeWCT.Arith.familyEval_surjective (n := 54) (t := 1) (by decide)
    (fun _ => WCT9.ftsPoint a.2.2.1.val a.2.2.2.val) (fun i j _ => Subsingleton.elim i j)
    (fun _ => Guess.Fam.ftsPoint_lt a.2.2.1 a.2.2.2) (fun _ => c)
  have hK0 := congrFun hK 0
  have h := cell_mem (fun i => match i with | .inl _ => c | .inr k => K k.2.2) (.wctChain (a, p))
    (fun _ => ChainGraph.joinOutput c 0)
  have hv : wctValueL (fun i => match i with | .inl _ => c | .inr k => K k.2.2)
      (fun _ => ChainGraph.joinOutput c 0) a p.val = c := by
    unfold wctValueL
    split_ifs
    · exact hK0
    · exact ChainGraph.joinOutput_low _ _
  rw [cell_wctChain, hv] at h
  exact h
theorem cell_ne_probe (secrets : Secrets) (labels : Labels) (node : Node) (hnode : ∀ q, node ≠ .wctChain q)
    (a : WctAddr) (p : Fin 4) (c : Digest) : cell secrets node labels ≠ Guess.probeInput a p c := by
  intro he
  have h1 := hdrBlock_cell secrets node labels
  rw [he, probeInput_hdr] at h1
  exact hnode (a, p) (toPos_injective (Extract.Pos.hdr_injective (toPos_bounded _) (toPos_bounded _)
    (bytesLE_injective h1))).symm
def Hidden (node : Node) : Prop := ∃ a : WctAddr, ∃ q : Fin 4, q.val < 3 ∧ node = .wctChain (a, q)
theorem treeLabel_outer (left right : Labels) (h : ∀ node, ¬Hidden node → left node = right node)
    (lay : Layer) (tree : Fin (2^31)) (level c : Nat) :
    treeLabel left lay tree level c = treeLabel right lay tree level c := by
  have hn : ∀ node : Node, (∀ q, node ≠ .wctChain q) → left node = right node := fun node hq =>
    h node (fun ⟨a, q, _, he⟩ => hq (a, q) he)
  unfold treeLabel
  split_ifs with hzero
  · cases leafAt lay tree c with
    | none => rfl
    | some L => simp only; rw [hn _ (fun _ => Node.noConfusion)]
  · cases treeNodeAt lay tree (level - 1) c with
    | none => rfl
    | some n => simp only; rw [hn _ (fun _ => Node.noConfusion)]
theorem ftsLabel_outer (left right : Labels) (h : ∀ node, ¬Hidden node → left node = right node)
    (index : Fin (2^31)) (coord : Fin 9) (level c : Nat) :
    ftsLabel left index coord level c = ftsLabel right index coord level c := by
  have hn : ∀ node : Node, (∀ q, node ≠ .wctChain q) → left node = right node := fun node hq =>
    h node (fun ⟨a, q, _, he⟩ => hq (a, q) he)
  unfold ftsLabel
  split_ifs with hzero hc
  · rw [hn _ (fun _ => Node.noConfusion)]
  · rfl
  · cases ftsNodeAt index coord (level - 1) c with
    | none => rfl
    | some n => simp only; rw [hn _ (fun _ => Node.noConfusion)]
theorem cell_outer (secrets secrets' : Secrets) (labels labels' : Labels)
    (hs : ∀ a, secrets (.inl a) = secrets' (.inl a)) (hl : ∀ node, ¬Hidden node → labels node = labels' node)
    (node : Node) (hnode : ∀ q, node ≠ .wctChain q) :
    cell secrets node labels = cell secrets' node labels' := by
  have hseeds : seedsOf secrets = seedsOf secrets' := by
    have hf : leafFamily secrets = leafFamily secrets' :=
      funext fun lay => funext fun tree => funext fun leaf => funext fun j => hs _
    funext a
    unfold seedsOf
    rw [hf]
  have hchain : chainLabels labels = chainLabels labels' :=
    funext fun point => hl _ (fun ⟨a, q, _, he⟩ => Node.noConfusion he)
  cases node with
  | chain p =>
      change ChainGraph.input (seedsOf secrets) p (chainLabels labels) =
        ChainGraph.input (seedsOf secrets') p (chainLabels labels')
      rw [hseeds, hchain]
  | leaf L =>
      have hends : (List.range (chainCount L.1.lay)).map (endLabel secrets labels L.1) =
          (List.range (chainCount L.1.lay)).map (endLabel secrets' labels' L.1) := by
        apply List.map_congr_left
        intro i _
        unfold endLabel
        rw [hseeds, hchain]
      simp only [cell, hends]
  | node n =>
      simp only [cell, treeLabel_outer labels labels' hl]
  | wctChain p => exact absurd rfl (hnode p)
  | wctLeaf L =>
      have hends : (List.ofFn fun t : Fin 6 => wctEndLabel labels (L.index, L.coord, L.child, t)) =
          (List.ofFn fun t : Fin 6 => wctEndLabel labels' (L.index, L.coord, L.child, t)) := by
        congr 1
        funext t
        unfold wctEndLabel
        rw [hl _ (fun ⟨a, q, hq, he⟩ => by
          simp only [Node.wctChain.injEq, Prod.mk.injEq] at he
          obtain ⟨-, rfl⟩ := he
          exact absurd hq (by decide))]
      simp only [cell, hends]
  | wctNode n =>
      simp only [cell, ftsLabel_outer labels labels' hl]
  | forest index =>
      simp only [cell, ftsLabel_outer labels labels' hl]
def stepNode (c : WctAddr × Fin 3) : Node := .wctChain (c.1, ⟨c.2.val, by omega⟩)
def shiftCoord (c : WctAddr × Fin 3) : WctPoint := (c.1, ⟨c.2.val + 1, by omega⟩)
theorem stepNode_injective : Function.Injective stepNode := by
  rintro ⟨a, q⟩ ⟨a', q'⟩ h
  simp only [stepNode, Node.wctChain.injEq, Prod.mk.injEq, Fin.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  rw [Fin.ext h]
/-- Hidden parameter of the case-C world (campaign X1): FTS family coefficients and step-1..3 labels (T8). -/
abbrev HiddenF := (Guess.Fam.FamIdx → Guess.Fam.Coefs) × (Guess.Fam.LabelIdx → Digest)
/-- Coefficient secret `(index, coord, j)` of the hidden vectors `K`. -/
def coefOf (K : Guess.Fam.FamIdx → Guess.Fam.Coefs) (c : WctCoef) : Digest := K (c.1, c.2.1) c.2.2
theorem inr_injective : Function.Injective (Sum.inr : WctCoef → SecretIndex) := Sum.inr_injective
noncomputable def worldSecrets (secrets : Secrets) (K : Guess.Fam.FamIdx → Guess.Fam.Coefs) : Secrets :=
  Function.extend Sum.inr (coefOf K) secrets
noncomputable def worldLow (low : LowLabels) (g12 : Guess.Fam.LabelIdx → Digest) : LowLabels :=
  Function.extend stepNode g12 low
structure Omega (U : Finset HashInput) where
  secrets : Secrets
  other : OtherHalves
  low : LowLabels
  high : LowLabels
  residual : U → HashOutput
variable {U : Finset HashInput} (hU : canonInputs ⊆ U)
noncomputable def worldLabels (ω : Omega U) (g12 : Guess.Fam.LabelIdx → Digest) : Labels :=
  joinLabels (worldLow ω.low g12) ω.high
noncomputable def worldAnswers (ω : Omega U) (h : HiddenF) : Answers :=
  eagerAnswers (privateEquiv.symm (worldSecrets ω.secrets h.1, ω.other)) U
    (programmed U hU (worldSecrets ω.secrets h.1) (worldLabels ω h.2) ω.residual)
theorem worldSecrets_inr (secrets : Secrets) (K : Guess.Fam.FamIdx → Guess.Fam.Coefs) (c : WctCoef) :
    worldSecrets secrets K (.inr c) = coefOf K c :=
  inr_injective.extend_apply _ _ c
theorem wctFamily_worldSecrets (secrets : Secrets) (K : Guess.Fam.FamIdx → Guess.Fam.Coefs) (i : Fin (2 ^ 31))
    (k : Fin 9) : wctFamily (worldSecrets secrets K) i k = K (i, k) := by
  funext j
  exact worldSecrets_inr secrets K (i, k, j)
theorem worldSecrets_inl (secrets : Secrets) (K : Guess.Fam.FamIdx → Guess.Fam.Coefs) (a : ChainGraph.Address) :
    worldSecrets secrets K (.inl a) = secrets (.inl a) := by
  unfold worldSecrets
  rw [Function.extend_apply']
  rintro ⟨b, hb⟩
  cases hb
theorem worldLabels_step (ω : Omega U) (g12 : Guess.Fam.LabelIdx → Digest) (a : WctAddr) (q : Fin 4)
    (hq : q.val < 3) :
    worldLabels ω g12 (.wctChain (a, q)) =
      ChainGraph.joinOutput (g12 (a, ⟨q.val, hq⟩)) (ω.high (.wctChain (a, q))) := by
  have hs : stepNode (a, ⟨q.val, hq⟩) = .wctChain (a, q) := rfl
  unfold worldLabels joinLabels worldLow
  rw [← hs, stepNode_injective.extend_apply]
theorem worldLabels_outer (ω : Omega U) (g12 : Guess.Fam.LabelIdx → Digest) (node : Node) (hnode : ¬Hidden node) :
    worldLabels ω g12 node = joinLabels ω.low ω.high node := by
  unfold worldLabels joinLabels worldLow
  rw [Function.extend_apply']
  rintro ⟨⟨a, q⟩, hc⟩
  exact hnode ⟨a, ⟨q.val, by omega⟩, q.isLt, hc.symm⟩
theorem not_hidden_top (a : WctAddr) : ¬Hidden (.wctChain (a, 3)) := by
  rintro ⟨b, q, hq, he⟩
  simp only [Node.wctChain.injEq, Prod.mk.injEq] at he
  obtain ⟨-, rfl⟩ := he
  exact absurd hq (by decide)
/-- The world's chain values are the family table `phi`. -/
theorem worldValueL (ω : Omega U) (h : HiddenF) (p : WctPoint) :
    wctValueL (worldSecrets ω.secrets h.1) (worldLabels ω h.2) p.1 p.2.val = Guess.Fam.phi h.1 h.2 p := by
  obtain ⟨a, ⟨s, hs⟩⟩ := p
  show wctValueL (worldSecrets ω.secrets h.1) (worldLabels ω h.2) a s = Guess.Fam.phi h.1 h.2 (a, ⟨s, hs⟩)
  unfold wctValueL
  split_ifs with h0
  · subst h0
    unfold wctSeedsOf
    rw [wctFamily_worldSecrets]
    rfl
  · have hq : (s - 1) % 4 < 3 := by omega
    rw [worldLabels_step ω h.2 a ⟨(s - 1) % 4, Nat.mod_lt _ (by decide)⟩ hq, ChainGraph.joinOutput_low]
    have hne : (⟨s, hs⟩ : Fin 4) ≠ 0 := fun he => h0 (congrArg Fin.val he)
    rw [Guess.Fam.phi_label' _ _ (a, ⟨s, hs⟩) hne]
    apply congrArg h.2
    refine Prod.ext rfl (Fin.ext ?_)
    rw [Fin.coe_pred]
    show (s - 1) % 4 = s - 1
    omega
theorem worldAnswers_public (ω : Omega U) (h : HiddenF) (x : HashInput) (hx : x ∈ U) :
    worldAnswers hU ω h (.inl (.inr x)) =
      programmed U hU (worldSecrets ω.secrets h.1) (worldLabels ω h.2) ω.residual ⟨x, hx⟩ :=
  eagerAnswers_mem _ U _ ⟨x, hx⟩
theorem programmed_outer (ω : Omega U) (h : HiddenF) (x : HashInput) (hx : x ∈ U)
    (hprobe : Guess.decodeProbe x = none) :
    programmed U hU (worldSecrets ω.secrets h.1) (worldLabels ω h.2) ω.residual ⟨x, hx⟩ =
      programmed U hU ω.secrets (joinLabels ω.low ω.high) ω.residual ⟨x, hx⟩ := by
  have hnot : ∀ (secrets : Secrets) (labels : Labels) (q : WctPoint), x ≠ cell secrets (.wctChain q) labels :=
    fun secrets labels q he => decodeProbe_none hprobe q.1 q.2 _ (he.trans (cell_wctChain secrets labels q))
  have hs : ∀ a, worldSecrets ω.secrets h.1 (.inl a) = ω.secrets (.inl a) := worldSecrets_inl ω.secrets h.1
  have hl : ∀ node, ¬Hidden node → worldLabels ω h.2 node = joinLabels ω.low ω.high node :=
    worldLabels_outer ω h.2
  have hcell : ∀ node, (∀ q, node ≠ .wctChain q) →
      cell (worldSecrets ω.secrets h.1) node (worldLabels ω h.2) = cell ω.secrets node (joinLabels ω.low ω.high) :=
    cell_outer _ _ _ _ hs hl
  by_cases hex : ∃ node, x = cell ω.secrets node (joinLabels ω.low ω.high)
  · obtain ⟨node, hnode⟩ := hex
    have hq : ∀ q, node ≠ .wctChain q := by
      rintro q rfl
      exact hnot _ _ q hnode
    have h1 : (⟨x, hx⟩ : U) = cellIn U hU (worldSecrets ω.secrets h.1) node (worldLabels ω h.2) :=
      Subtype.ext (hnode.trans (hcell node hq).symm)
    have h2 : (⟨x, hx⟩ : U) = cellIn U hU ω.secrets node (joinLabels ω.low ω.high) := Subtype.ext hnode
    rw [h1, programmed_at, ← h1, h2, programmed_at]
    exact hl node (fun ⟨a, q, _, he⟩ => hq (a, q) he)
  · push Not at hex
    rw [programmed_other U hU _ _ _ _ (fun node he => ?_), programmed_other U hU _ _ _ _ (fun node he => hex node he)]
    by_cases hq : ∀ q, node ≠ .wctChain q
    · exact hex node (he.trans (hcell node hq))
    · push Not at hq
      obtain ⟨q, rfl⟩ := hq
      exact hnot _ _ q he
theorem seedOf_worldAnswers (ω : Omega U) (h : HiddenF) (a : WctAddr) :
    Guess.seedOf (worldAnswers hU ω h) a = Guess.Fam.phi h.1 h.2 (a, 0) := by
  have hc : WCT9.ftsCoef (worldAnswers hU ω h) a.1.val a.2.1.val = h.1 (a.1, a.2.1) := by
    funext j
    rw [← secretsOf_coef (worldAnswers hU ω h) (a.1, a.2.1, j)]
    unfold worldAnswers
    rw [secretsOf_eager, privateSecrets_symm, worldSecrets_inr]
    rfl
  unfold Guess.seedOf
  rw [hc]
  rfl
noncomputable def chainTable (ω : Omega U) : Guess.ChainTable HiddenF where
  answers := worldAnswers hU ω
  view h := Guess.Fam.phi h.1 h.2
  base := 0
  step a p v := ChainGraph.joinOutput v (ω.high (.wctChain (a, p)))
  top a := joinLabels ω.low ω.high (.wctChain (a, 3))
  miss x := SphincsSecurity.Concrete.finiteHashAnswer ∅ U ω.residual x
  answers_probe := by
    intro h a p c
    have hmem : Guess.probeInput a p c ∈ U := hU (probeInput_mem a p c)
    rw [worldAnswers_public hU ω h _ hmem]
    unfold Guess.probeAnswer
    by_cases hc : Guess.Fam.phi h.1 h.2 (a, p) = c
    · rw [if_pos hc]
      have hx : (⟨Guess.probeInput a p c, hmem⟩ : U) =
          cellIn U hU (worldSecrets ω.secrets h.1) (.wctChain (a, p)) (worldLabels ω h.2) := by
        apply Subtype.ext
        change Guess.probeInput a p c = cell _ (.wctChain (a, p)) _
        rw [cell_wctChain]
        exact congrArg _ ((worldValueL ω h (a, p)).trans hc).symm
      rw [hx, programmed_at]
      unfold Guess.succPos
      split_ifs with hp
      · simp only
        rw [worldLabels_step ω h.2 a p (by omega)]
        have hne : (⟨p.val + 1, hp⟩ : Fin 4) ≠ 0 := fun he => by simpa using congrArg Fin.val he
        rw [Guess.Fam.phi_label' _ _ (a, ⟨p.val + 1, hp⟩) hne]
        congr 3
      · simp only
        have hp2 : p = 3 := Fin.ext (by have := p.isLt; omega)
        subst hp2
        exact worldLabels_outer ω h.2 _ (not_hidden_top a)
    · rw [if_neg hc]
      rw [programmed_other U hU _ _ _ _ (fun node he => ?_)]
      · exact (SphincsSecurity.Concrete.finiteHashAnswer_none ∅ U ω.residual _ hmem rfl).symm
      · by_cases hq : ∀ q, node ≠ .wctChain q
        · exact cell_ne_probe _ _ node hq a p c he.symm
        · push Not at hq
          obtain ⟨q, rfl⟩ := hq
          change Guess.probeInput a p c = cell _ (.wctChain q) _ at he
          rw [cell_wctChain, worldValueL] at he
          obtain ⟨h1, h2, h3⟩ := probeInput_inj he
          subst h1 h2
          exact hc h3.symm
  answers_public := by
    intro h h' x hx
    by_cases hU' : x ∈ U
    · rw [worldAnswers_public hU ω h x hU', worldAnswers_public hU ω h' x hU',
        programmed_outer hU ω h x hU' hx, programmed_outer hU ω h' x hU' hx]
    · change SphincsSecurity.Concrete.finiteHashAnswer ∅ U _ x = SphincsSecurity.Concrete.finiteHashAnswer ∅ U _ x
      unfold SphincsSecurity.Concrete.finiteHashAnswer
      rw [dif_neg hU', dif_neg hU']
  step_low a p v := ChainGraph.joinOutput_low _ _
  seed := seedOf_worldAnswers hU ω
theorem worldAnswers_agrees (ω : Omega U) (h : HiddenF) :
    Agrees (worldAnswers hU ω h) (worldLabels ω h.2) :=
  eager_programmed_agrees U hU _ _ _ _
/-- The hidden values carried by `ω` itself. -/
def trueHidden (ω : Omega U) : HiddenF :=
  (fun f j => ω.secrets (.inr (f.1, f.2, j)), fun l => ω.low (stepNode l))
theorem worldSecrets_true (ω : Omega U) : worldSecrets ω.secrets (trueHidden ω).1 = ω.secrets := by
  funext i
  cases i with
  | inl a => exact worldSecrets_inl _ _ a
  | inr c => rw [worldSecrets_inr]; rfl
theorem worldLow_true (ω : Omega U) : worldLow ω.low (trueHidden ω).2 = ω.low := by
  funext node
  unfold worldLow
  by_cases hn : ∃ c, stepNode c = node
  · obtain ⟨c, rfl⟩ := hn
    rw [stepNode_injective.extend_apply]
    rfl
  · rw [Function.extend_apply' _ _ _ hn]
theorem worldAnswers_true (ω : Omega U) :
    worldAnswers hU ω (trueHidden ω) =
      eagerAnswers (privateEquiv.symm (ω.secrets, ω.other)) U
        (programmed U hU ω.secrets (joinLabels ω.low ω.high) ω.residual) := by
  unfold worldAnswers worldLabels
  rw [worldSecrets_true, worldLow_true]
theorem chainTable_answers (ω : Omega U) : (chainTable hU ω).answers = worldAnswers hU ω := rfl
theorem chainTable_view (ω : Omega U) (h : HiddenF) : (chainTable hU ω).view h = Guess.Fam.phi h.1 h.2 := rfl
end ClaudeWCT.W9.CanonTable
