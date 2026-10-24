import SigGolfCandidate.ClaudeWCT_W9_New_G3b_Shared
import SigGolfCandidate.ClaudeWCT_W9_New_BC_Respects
import SigGolfCandidate.ClaudeWCT_W9_New_Positions_FtsBridge

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
theorem chainInputW_alias {lay : Layer} {tree leaf : Nat} {L : LeafAddr} (h : LeafAlias lay tree leaf L) (i : Nat) :
    WCT9.chainInputW lay tree leaf i = WCT9.chainInputW L.lay L.tree L.leaf i := by
  funext step value
  unfold WCT9.chainInputW
  rw [chainInput_alias h i, chainHeader_congr_old h.1 h.2.1 h.2.2 rfl rfl, h.1]
theorem chainW_alias {lay : Layer} {tree leaf : Nat} {L : LeafAddr} (h : LeafAlias lay tree leaf L) (i : Nat) :
    WCT9.chainW lay tree leaf i = WCT9.chainW L.lay L.tree L.leaf i := by
  funext start count value
  unfold WCT9.chainW
  rw [chainInputW_alias h i, h.1]
theorem eval_chain_one_maskAt {s : Nat} (hs : s < depth answers a) (v : Digest) :
    evalWithAnswerFn (maskAt answers a) (WCT9.chainW a.key.lay a.key.tree a.key.leaf a.chain s 1 v) =
      if s + 1 = depth answers a then frontierValue answers a else 0 := by
  rw [eval_chainW_one', pad64_chainInputW, ← chainRowW_eq, maskAt_prefix answers a v hs]
  split
  · exact halfOf_joinHalf _ _ _
  · exact halfOf_zero _
theorem eval_chain_prefix_maskAt (hd : 1 ≤ depth answers a) (v : Digest) :
    evalWithAnswerFn (maskAt answers a) (WCT9.chainW a.key.lay a.key.tree a.key.leaf a.chain 0 (depth answers a) v) =
      frontierValue answers a := by
  have h1 := eval_chainW_add' (maskAt answers a) a.key.lay a.key.tree a.key.leaf a.chain 0
    (depth answers a - 1) 1 v
  rw [Nat.zero_add, eval_chain_one_maskAt answers a (by omega), if_pos (Nat.sub_add_cancel hd),
    Nat.sub_add_cancel hd] at h1
  exact h1
theorem eval_chain_maskAt (hd : 1 ≤ depth answers a) {count : Nat} (hc : depth answers a ≤ count)
    (hc' : count ≤ 256) (v : Digest) :
    evalWithAnswerFn (maskAt answers a) (WCT9.chainW a.key.lay a.key.tree a.key.leaf a.chain 0 count v) =
      evalWithAnswerFn answers (WCT9.chainW a.key.lay a.key.tree a.key.leaf a.chain 0 count
        (WCT9.wotsSeed answers a.key.lay a.key.tree a.key.leaf a.chain)) := by
  obtain ⟨e, rfl⟩ : ∃ e, count = depth answers a + e := ⟨count - depth answers a, by omega⟩
  rw [eval_chainW_add', eval_chainW_add' answers, Nat.zero_add,
    eval_chain_prefix_maskAt answers a hd]
  change _ = evalWithAnswerFn answers (WCT9.chainW a.key.lay a.key.tree a.key.leaf a.chain (depth answers a) e
    (frontierValue answers a))
  refine Respects.eval_eq (S := fun q => maskAt answers a q = answers q) ?_ (fun q hq => hq)
  refine respects_chainW' _ _ _ _ _ _ _ fun step value hlo hhi => ?_
  rw [pad64_chainInputW, ← chainRowW_eq]
  exact maskAt_row_ge answers a value hlo (by omega)
/-- A WOTS seed only reads the coefficient cells `lowerSeedHeader lay tree p` of its tree (every layer: the seeds
are leaf-family evaluations, campaign X1 stage B, top leaves since campaign T8D). -/
theorem wotsSeed_congr_cells {T T' : Answers} {lay : Layer} (tree leaf i : Nat)
    (h : ∀ p, T (.inr (.inl (WCT9.lowerSeedHeader lay tree p))) = T' (.inr (.inl (WCT9.lowerSeedHeader lay tree p)))) :
    WCT9.wotsSeed T lay tree leaf i = WCT9.wotsSeed T' lay tree leaf i := by
  rw [WCT9.wotsSeed_fam, WCT9.wotsSeed_fam]
  congr 2
  funext j
  unfold WCT9.famCoef WCT9.famCoefN WCT9.lowerSeedPair privatePair privateHash
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  change WCT9.seedHalf ((T (.inr (.inl (header 0 lay.val tree _ 0)))).extractLsb' 0 128,
      (T (.inr (.inl (header 0 lay.val tree _ 0)))).extractLsb' 128 128) _ =
    WCT9.seedHalf ((T' (.inr (.inl (header 0 lay.val tree _ 0)))).extractLsb' 0 128,
      (T' (.inr (.inl (header 0 lay.val tree _ 0)))).extractLsb' 128 128) _
  rw [show header 0 lay.val tree (WCT9.famOrdinal lay leaf j.val / 2) 0 =
    WCT9.lowerSeedHeader lay tree (WCT9.famOrdinal lay leaf j.val / 2) from rfl, h]
/-- A WOTS seed only reads private cells. -/
theorem wotsSeed_congr_private {T T' : Answers} (h : ∀ c, T (.inr c) = T' (.inr c)) (lay : Layer)
    (tree leaf i : Nat) : WCT9.wotsSeed T lay tree leaf i = WCT9.wotsSeed T' lay tree leaf i :=
  wotsSeed_congr_cells tree leaf i fun _ => h _
/-- img-v6 top family (39 coefficients per 4 leaves): aliased top leaves no longer share seeds unless the leaves are
small, so slots need small leaves on every layer (r3-lean-nonsec; every masked address is a source chain, whose leaf
is `< 2^24`, Final.hsize). -/
def SlotOK (a : ChainAddr) (_lay : Layer) (leaf : Nat) : Prop := leaf < 2 ^ 24 ∧ a.key.leaf < 2 ^ 24
def MaskOK (a : ChainAddr) : Prop := a.key.leaf < 2 ^ 24
theorem slotOK_of {a : ChainAddr} {lay : Layer} {leaf : Nat} (h : MaskOK a) (hl : leaf < 2 ^ 24) :
    SlotOK a lay leaf := ⟨hl, h⟩
theorem maskOK_of_lt {a : ChainAddr} (h : a.key.leaf < 2 ^ 24) : MaskOK a := h
theorem wotsSeed_maskAt (lay : Layer) (tree leaf i : Nat) :
    WCT9.wotsSeed (maskAt answers a) lay tree leaf i = WCT9.wotsSeed answers lay tree leaf i :=
  wotsSeed_congr_private (fun c => maskAt_private answers a c) lay tree leaf i
/-- Seeds of aliased leaves agree: the coefficient cells only see `tree % 2 ^ 40` and, for the top layer (one
family of 24 coefficients per leaf, an even count), `leaf % 2 ^ 32`; lower leaves need small leaf indices. -/
theorem wotsSeed_alias (T : Answers) {lay : Layer} {tree leaf : Nat} {L : LeafAddr}
    (h : LeafAlias lay tree leaf L) (hb : leaf < 2 ^ 24 ∧ L.leaf < 2 ^ 24) (i : Nat) :
    WCT9.wotsSeed T lay tree leaf i = WCT9.wotsSeed T L.lay L.tree L.leaf i := by
  obtain ⟨hlay, ht, hlf⟩ := h
  subst hlay
  obtain ⟨hl, hL⟩ := hb
  have he : leaf = L.leaf := by
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hlf
    exact hlf
  rw [WCT9.wotsSeed_fam, WCT9.wotsSeed_fam, WCT9.ofFn_famCoef, WCT9.ofFn_famCoef, he]
  refine congrArg (ClaudeWCT.Arith.familyEval · _) ?_
  unfold WCT9.famCoefL
  apply List.map_congr_left
  intro j _
  unfold WCT9.lowerSeedPair privatePair
  rw [header_normal 0 _ tree, header_normal 0 _ L.tree, ht]
end Mask
namespace Mask
open SigGolfCandidate.T3.Security.Wots.Mask
variable (answers : Answers) (a : ChainAddr)
theorem eval_honestChain_maskAt (lay : Layer) (tree leaf i count : Nat) (hi : i < chainCount lay)
    (hc : count ≤ 256) (hb : SlotOK a lay leaf)
    (halias : LeafAlias lay tree leaf a.key → i = a.chain → depth answers a ≤ count) :
    evalWithAnswerFn (maskAt answers a) (WCT9.chainW lay tree leaf i 0 count (WCT9.wotsSeed (maskAt answers a) lay tree leaf i)) =
      evalWithAnswerFn answers (WCT9.chainW lay tree leaf i 0 count (WCT9.wotsSeed answers lay tree leaf i)) := by
  by_cases hd : depth answers a = 0
  · rw [maskAt_of_depth_zero answers a hd]
  have hi' : i < 2 ^ 24 := by
    have := chainCount_le lay
    simp only [Nat.reducePow]; omega
  have hc' : a.chain < 2 ^ 24 := by
    have := chain_lt_of_depth answers a (by omega)
    have := chainCount_le a.key.lay
    simp only [Nat.reducePow]; omega
  by_cases hal' : LeafAlias lay tree leaf a.key ∧ i = a.chain
  · obtain ⟨hal', rfl⟩ := hal'
    have hb' : leaf < 2 ^ 24 ∧ a.key.leaf < 2 ^ 24 := hb
    rw [chainW_alias hal', wotsSeed_alias _ hal' hb', wotsSeed_alias _ hal' hb']
    exact eval_chain_maskAt answers a (by omega) (halias hal' rfl) hc _
  · rw [wotsSeed_maskAt answers a lay tree leaf i]
    apply eval_maskAt_of_respects
    refine respects_chainW' _ _ _ _ _ _ _ fun step value hlo hhi => ?_
    rw [pad64_chainInputW]
    intro s' v' hs' heq
    have hstep' : step < 256 := by omega
    have h := chainInputW_eq_chainRowW hi' hc' hstep' (by omega) heq
    exact hal' ⟨h.1, h.2.1⟩
theorem wotsEnd_maskAt (lay : Layer) (tree leaf i : Nat) (hi : i < chainCount lay) (hb : SlotOK a lay leaf) :
    WCT9.wotsEnd (maskAt answers a) lay tree leaf i = WCT9.wotsEnd answers lay tree leaf i := by
  unfold WCT9.wotsEnd
  apply eval_honestChain_maskAt answers a lay tree leaf i _ hi (by have := width_le lay i; omega) hb
  intro hal' hia
  obtain ⟨hl', -, -⟩ := hal'
  subst hl' hia
  exact depth_le_width answers a hi
theorem wotsValue_maskAt (lay : Layer) (tree leaf : Nat) (digits : List Nat) (i : Nat) (hi : i < chainCount lay)
    (hdig : digits.getD i 0 ≤ 256) (hb : SlotOK a lay leaf)
    (halias : LeafAlias lay tree leaf a.key → i = a.chain → depth answers a ≤ digits.getD i 0) :
    WCT9.wotsValue (maskAt answers a) lay tree leaf digits i = WCT9.wotsValue answers lay tree leaf digits i :=
  eval_honestChain_maskAt answers a lay tree leaf i _ hi hdig hb halias
theorem wotsRoot_maskAt (lay : Layer) (tree leaf : Nat) (hb : SlotOK a lay leaf) :
    WCT9.wotsRoot (maskAt answers a) lay tree leaf = WCT9.wotsRoot answers lay tree leaf := by
  unfold WCT9.wotsRoot
  rw [List.map_congr_left (fun i hi => wotsEnd_maskAt answers a lay tree leaf i (List.mem_range.mp hi) hb)]
  exact eval_maskAt_of_respects answers a (respectsP_lowerLeafHash a _ _ _ _
    (by simp only [List.length_map, List.length_range]; exact SigGolfCandidate.T3.Security.Wots.Enc.chainCount_ge4 _))
theorem height_pow_le (lay : Layer) : 2 ^ height lay ≤ 2 ^ 12 :=
  Nat.pow_le_pow_right (by decide) (SigGolfCandidate.T3M.Extract.height_le lay)
/-- Top-nonce layer: a top node trial input is the nonce-slot node input, whose header is the top merkle tweak. -/
theorem pad64_topNodeInput_block4 (heap n : Nat) (left right : Digest) :
    pad64 (topNodeInput heap n left right) = block4 left (WCT9.merkleTweak 0 0 heap) (WCT9.nonceDigest n) right := by
  have h : topNodeInput heap n left right = block4 left (WCT9.merkleTweak 0 0 heap) (WCT9.nonceDigest n) right := by
    unfold topNodeInput block4
    rw [WCT9.merkleTweak_top0, WCT9.bytesLE_nonceDigest]
  rw [h]
  unfold pad64
  simp
theorem respectsP_topNodeHashN (heap n : Nat) (left right : Digest) :
    Respects (UntouchedP a) (topNodeHashN heap n left right) := by
  unfold topNodeHashN
  apply Respects.projHash
  rw [pad64_topNodeInput_block4]
  exact untouchedP_of_hdr a _ _ (SigGolfCandidate.T3M.Extract.hdrBlock_block4 left _ _ right)
    fun l tr leaf c step hs => merkleTweak_ne_chainHeader (Or.inl rfl) l tr leaf c step hs
theorem respectsP_topNonceSearch (h heap : Nat) (left right : Digest) :
    ∀ fuel n, Respects (UntouchedP a) (topNonceSearch h heap left right fuel n)
  | 0, n => by
      unfold topNonceSearch
      exact Respects.bind (respectsP_topNodeHashN a _ _ _ _) fun _ => Respects.pure' _
  | fuel + 1, n => by
      unfold topNonceSearch
      refine Respects.bind (respectsP_topNodeHashN a _ _ _ _) fun _ => ?_
      split
      · exact Respects.pure' _
      · exact respectsP_topNonceSearch h heap left right fuel (n + 1)
theorem respectsP_buildTopLevels (leaves : List Digest) :
    Respects (UntouchedP a) (buildTopLevels leaves) := by
  unfold buildTopLevels
  refine Respects.foldlM _ _ (fun level _ levels => Respects.bind ?_ fun _ => Respects.pure' _) _
  unfold buildTopLevel
  refine Respects.mapM _ _ fun i _ => ?_
  split
  · rw [← WCT9.lowerNodeHash_top]
    exact respectsP_lowerNodeHash a 0 0 _ _ _ (Or.inl rfl)
  · unfold topNodeAt
    exact Respects.map _ (respectsP_topNonceSearch a _ _ _ _ _ _)
theorem wotsTree_maskAt (lay : Layer) (tree : Nat) (hal : MaskOK a) :
    WCT9.wotsTree (maskAt answers a) lay tree = WCT9.wotsTree answers lay tree := by
  have hroots : (List.range (2 ^ height lay)).map (WCT9.wotsRoot (maskAt answers a) lay tree) =
      (List.range (2 ^ height lay)).map (WCT9.wotsRoot answers lay tree) :=
    List.map_congr_left (fun leaf hleaf => wotsRoot_maskAt answers a lay tree leaf
      (slotOK_of hal (by have := List.mem_range.mp hleaf; have := height_pow_le lay; omega)))
  unfold WCT9.wotsTree
  rw [hroots]
  split_ifs with h0
  · exact eval_maskAt_of_respects answers a (respectsP_buildTopLevels a _)
  · exact eval_maskAt_of_respects answers a (respectsP_lowerLevels a _ _ _ (by fin_cases lay <;> decide) _
      (by simp only [List.length_map, List.length_range]; exact le_rfl))
theorem builtTree_maskAt_top (hal : MaskOK a) :
    builtTree (maskAt answers a) 0 0 = builtTree answers 0 0 := by
  rw [← WCT9.wotsTree_top, ← WCT9.wotsTree_top, wotsTree_maskAt answers a 0 0 hal]
theorem leafRoot_maskAt_top (leaf : Nat) (hl : leaf < 2 ^ 24) (hal : MaskOK a) :
    Correctness.leafRoot (maskAt answers a) 0 0 leaf = Correctness.leafRoot answers 0 0 leaf := by
  rw [← WCT9.wotsRoot_top, ← WCT9.wotsRoot_top, wotsRoot_maskAt answers a 0 0 leaf (slotOK_of hal hl)]
theorem honestPair_maskAt (lay : Layer) (tree : Nat) (hal : MaskOK a) :
    Extract.honestPair (maskAt answers a) lay tree = Extract.honestPair answers lay tree := by
  unfold Extract.honestPair
  rw [wotsTree_maskAt answers a lay tree hal]
theorem ftsQuery_untouchedP {index : Nat} {q : SigGolfCandidate.T3.Spec.Domain} (h : WCT9.FtsQuery index q) :
    UntouchedP a q :=
  untouchedP_of_untouched a ⟨ClaudeWCT.WCT9.Wots.ftsQuery_untouched a h,
    ClaudeWCT.WCT9.Wots.ftsQuery_untouched (slotAddr a) h⟩
theorem honestTop_maskAt (index : Nat) :
    Extract.honestTop (maskAt answers a) index = Extract.honestTop answers index := by
  rw [Extract.honestTop_eq_wct9, Extract.honestTop_eq_wct9]
  exact ClaudeWCT.WCT9.Wots.honestTop_congr
    (fun _ hq => maskAt_untouched answers a (ftsQuery_untouchedP a hq))
end Mask
theorem leafMsg_maskAt (answers : Answers) (a : ChainAddr) (hal : Mask.MaskOK a) (L : LeafAddr) :
    leafMsg (maskAt answers a) L = leafMsg answers L := by
  unfold leafMsg
  split
  · rw [Mask.honestPair_maskAt answers a _ _ hal]
  · rw [Mask.honestTop_maskAt]
theorem referenceSearch_maskAt (answers : Answers) (a : ChainAddr) (hal : Mask.MaskOK a) (L : LeafAddr) :
    referenceSearch (maskAt answers a) L = referenceSearch answers L := by
  unfold referenceSearch
  rw [leafMsg_maskAt answers a hal]
  exact Mask.eval_maskAt_of_respects answers a (Mask.respectsP_layerCounterSearch a _ _ _ _ _ _)
theorem referenceDigits_maskAt (answers : Answers) (a : ChainAddr) (hal : Mask.MaskOK a) (L : LeafAddr) :
    referenceDigits (maskAt answers a) L = referenceDigits answers L := by
  unfold referenceDigits
  rw [referenceSearch_maskAt answers a hal]
theorem referenceInput_maskAt (answers : Answers) (a : ChainAddr) (hal : Mask.MaskOK a) (L : LeafAddr) :
    referenceInput (maskAt answers a) L = referenceInput answers L := by
  unfold referenceInput
  rw [referenceSearch_maskAt answers a hal, leafMsg_maskAt answers a hal]
theorem depth_maskAt_all (answers : Answers) (a b : ChainAddr) (hal : Mask.MaskOK a) :
    depth (maskAt answers a) b = depth answers b := by
  unfold depth
  rw [referenceDigits_maskAt answers a hal]
theorem frontierValue_maskAt_other (answers : Answers) (a b : ChainAddr) (hb : b.chain < chainCount b.key.lay)
    (hbl : b.key.leaf < 2 ^ 24) (hal : Mask.MaskOK a)
    (halias : Mask.LeafAlias b.key.lay b.key.tree b.key.leaf a.key → b.chain = a.chain → depth answers a ≤ depth answers b) :
    frontierValue (maskAt answers a) b = frontierValue answers b := by
  unfold frontierValue honestChainValueW
  rw [depth_maskAt_all answers a b hal]
  exact Mask.eval_honestChain_maskAt answers a _ _ _ _ _ hb (by have := Mask.depth_le_seven answers b; omega)
    (Mask.slotOK_of hal hbl) halias
theorem frontierValue_maskAt_bounded (answers : Answers) (a b : ChainAddr)
    (ha : a.key.tree < 2 ^ 40 ∧ a.key.leaf < 2 ^ 24) (hb : b.key.tree < 2 ^ 40 ∧ b.key.leaf < 2 ^ 24)
    (hc : b.chain < chainCount b.key.lay) :
    frontierValue (maskAt answers a) b = frontierValue answers b := by
  apply frontierValue_maskAt_other answers a b hc hb.2 ha.2
  intro hal hch
  have hk : b.key = a.key := by
    have := hal.eq_of_lt hb.1 (by omega) ha.1 (by omega)
    cases hbk : b.key
    rw [hbk] at this
    exact this
  have : b = a := by
    cases b; cases a
    simp only at hk hch
    rw [hk, hch]
  rw [this]
end ClaudeWCT.W9.T3.Security.Wots

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
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
noncomputable def prefixStep (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg) (a : ChainAddr) (input : HashInput) : Option Nat :=
  if h : ∃ step value, step < depth answers messages a ∧ input = chainRowW a step value then some (Classical.choose h) else none
/-- Mask of chain `a`: its rows below `depth` answer `0` (the last one answers the frontier, in the half its step
reads, C3 #866). Seeds are evaluations
of their leaf family at every layer (campaign X1 stage B, top leaves since campaign T8D), so no private cell is
blanked. -/
noncomputable def maskAt (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg) (a : ChainAddr) : Answers
  | .inl (.inr input) =>
      match prefixStep answers messages a input with
      | some step => if step + 1 = depth answers messages a then
            joinHalf (WCT9.chainHigh a.key.lay a.chain step) (frontierValue answers messages a) 0
          else (0 : HashOutput)
      | none => answers (.inl (.inr input))
  | .inl (.inl coin) => answers (.inl (.inl coin))
  | .inr c => answers (.inr c)
namespace Mask
open SigGolfCandidate.T3.Security.Wots.Mask
open ClaudeWCT.W9.T3.Security.Wots.Mask
theorem chain_lt_of_depth (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg) (a : ChainAddr) (hd : 1 ≤ depth answers messages a) :
    a.chain < chainCount a.key.lay := by
  by_contra hc
  have hlen := referenceDigits_length answers messages a.key
  have h0 : depth answers messages a = 0 := List.getD_eq_default _ _ (by omega)
  omega
theorem depth_le_seven (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg) (a : ChainAddr) : depth answers messages a ≤ 7 := by
  by_cases hd : 1 ≤ depth answers messages a
  · exact (depth_le answers messages a (chain_lt_of_depth answers messages a hd)).trans (width_le _ _)
  · omega
theorem prefixStep_spec {answers : Answers} {messages : LeafAddr → WCT9.LayerMsg} {a : ChainAddr} {input : HashInput} {step : Nat}
    (h : prefixStep answers messages a input = some step) :
    step < depth answers messages a ∧ ∃ value, input = chainRowW a step value := by
  unfold prefixStep at h
  split at h
  · rename_i hex
    have he := Option.some.inj h
    subst he
    obtain ⟨value, hlt, heq⟩ := Classical.choose_spec hex
    exact ⟨hlt, value, heq⟩
  · cases h
theorem prefixStep_chainRow (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg) (a : ChainAddr) {s : Nat} (v : Digest) (hs : s < 256) :
    prefixStep answers messages a (chainRowW a s v) = if s < depth answers messages a then some s else none := by
  have h7 := depth_le_seven answers messages a
  split
  · rename_i hlt
    unfold prefixStep
    rw [dif_pos ⟨s, v, hlt, rfl⟩]
    obtain ⟨w, hw, heq⟩ := Classical.choose_spec (⟨s, v, hlt, rfl⟩ :
      ∃ step value, step < depth answers messages a ∧ chainRowW a s v = chainRowW a step value)
    exact congrArg some (chainRowW_inj hs (by omega) heq).1.symm
  · rename_i hge
    cases hp : prefixStep answers messages a (chainRowW a s v) with
    | none => rfl
    | some step =>
        obtain ⟨hlt, w, heq⟩ := prefixStep_spec hp
        have := (chainRowW_inj hs (by omega) heq).1
        omega
theorem prefixStep_untouched {answers : Answers} {messages : LeafAddr → WCT9.LayerMsg} {a : ChainAddr} {input : HashInput}
    (h : UntouchedP a (.inl (.inr input))) : prefixStep answers messages a input = none := by
  cases hp : prefixStep answers messages a input with
  | none => rfl
  | some step =>
      obtain ⟨hlt, w, heq⟩ := prefixStep_spec hp
      exact absurd heq (h step w (by have := depth_le_seven answers messages a; omega))
theorem maskAt_public (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg) (a : ChainAddr) (input : HashInput) :
    maskAt answers messages a (.inl (.inr input)) = match prefixStep answers messages a input with
      | some step => if step + 1 = depth answers messages a then
            joinHalf (WCT9.chainHigh a.key.lay a.chain step) (frontierValue answers messages a) 0
          else (0 : HashOutput)
      | none => answers (.inl (.inr input)) := rfl
theorem maskAt_private (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg) (a : ChainAddr) (c : Coordinate) :
    maskAt answers messages a (.inr c) = answers (.inr c) := rfl
theorem maskAt_tweak (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg) (a : ChainAddr) (tweak : BitVec 128) :
    maskAt answers messages a (.inr (.inl tweak)) = answers (.inr (.inl tweak)) := rfl
theorem maskAt_untouched (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg) (a : ChainAddr) {q : Spec.Domain} (h : UntouchedP a q) :
    maskAt answers messages a q = answers q := by
  rcases q with (coin | input) | (tweak | other)
  · rfl
  · rw [maskAt_public, prefixStep_untouched h]
  · rfl
  · rfl
theorem maskAt_prefix (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg) (a : ChainAddr) {s : Nat} (v : Digest) (hs : s < depth answers messages a) :
    maskAt answers messages a (.inl (.inr (chainRowW a s v))) =
      if s + 1 = depth answers messages a then
        joinHalf (WCT9.chainHigh a.key.lay a.chain s) (frontierValue answers messages a) 0 else 0 := by
  have h7 := depth_le_seven answers messages a
  rw [maskAt_public, prefixStep_chainRow answers messages a v (by omega), if_pos hs]
  rfl
theorem maskAt_row_ge (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg) (a : ChainAddr) {s : Nat} (v : Digest) (hs : depth answers messages a ≤ s)
    (hs' : s < 256) : maskAt answers messages a (.inl (.inr (chainRowW a s v))) = answers (.inl (.inr (chainRowW a s v))) := by
  rw [maskAt_public, prefixStep_chainRow answers messages a v hs', if_neg (by omega)]
theorem maskAt_of_depth_zero (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg) (a : ChainAddr) (hd : depth answers messages a = 0) :
    maskAt answers messages a = answers := by
  funext q
  rcases q with (coin | input) | (tweak | other)
  · rfl
  · rw [maskAt_public]
    cases hp : prefixStep answers messages a input with
    | none => rfl
    | some step => have := (prefixStep_spec hp).1; omega
  · rfl
  · rfl
theorem eval_maskAt_of_respects (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg) (a : ChainAddr) {α : Type} {program : M α}
    (h : Respects (UntouchedP a) program) :
    evalWithAnswerFn (maskAt answers messages a) program = evalWithAnswerFn answers program :=
  (h _ _ fun _ hq => maskAt_untouched answers messages a hq).1
theorem queried_maskAt_of_respects (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg) (a : ChainAddr) {α : Type} {program : M α}
    (h : Respects (UntouchedP a) program) :
    SourceReplay.queried (maskAt answers messages a) program = SourceReplay.queried answers program :=
  (h _ _ fun _ hq => maskAt_untouched answers messages a hq).2
end Mask
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
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
open ClaudeWCT.W9.T3.Security.Wots.Mask
variable (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg) (a : ChainAddr)
theorem eval_chain_one_maskAt {s : Nat} (hs : s < depth answers messages a) (v : Digest) :
    evalWithAnswerFn (maskAt answers messages a) (WCT9.chainW a.key.lay a.key.tree a.key.leaf a.chain s 1 v) =
      if s + 1 = depth answers messages a then frontierValue answers messages a else 0 := by
  rw [eval_chainW_one', pad64_chainInputW, ← chainRowW_eq, maskAt_prefix answers messages a v hs]
  split
  · exact halfOf_joinHalf _ _ _
  · exact halfOf_zero _
theorem eval_chain_prefix_maskAt (hd : 1 ≤ depth answers messages a) (v : Digest) :
    evalWithAnswerFn (maskAt answers messages a) (WCT9.chainW a.key.lay a.key.tree a.key.leaf a.chain 0 (depth answers messages a) v) =
      frontierValue answers messages a := by
  have h1 := eval_chainW_add' (maskAt answers messages a) a.key.lay a.key.tree a.key.leaf a.chain 0
    (depth answers messages a - 1) 1 v
  rw [Nat.zero_add, eval_chain_one_maskAt answers messages a (by omega), if_pos (Nat.sub_add_cancel hd),
    Nat.sub_add_cancel hd] at h1
  exact h1
theorem eval_chain_maskAt (hd : 1 ≤ depth answers messages a) {count : Nat} (hc : depth answers messages a ≤ count)
    (hc' : count ≤ 256) (v : Digest) :
    evalWithAnswerFn (maskAt answers messages a) (WCT9.chainW a.key.lay a.key.tree a.key.leaf a.chain 0 count v) =
      evalWithAnswerFn answers (WCT9.chainW a.key.lay a.key.tree a.key.leaf a.chain 0 count
        (WCT9.wotsSeed answers a.key.lay a.key.tree a.key.leaf a.chain)) := by
  obtain ⟨e, rfl⟩ : ∃ e, count = depth answers messages a + e := ⟨count - depth answers messages a, by omega⟩
  rw [eval_chainW_add', eval_chainW_add' answers, Nat.zero_add,
    eval_chain_prefix_maskAt answers messages a hd]
  change _ = evalWithAnswerFn answers (WCT9.chainW a.key.lay a.key.tree a.key.leaf a.chain (depth answers messages a) e
    (frontierValue answers messages a))
  refine Respects.eval_eq (S := fun q => maskAt answers messages a q = answers q) ?_ (fun q hq => hq)
  refine respects_chainW' _ _ _ _ _ _ _ fun step value hlo hhi => ?_
  rw [pad64_chainInputW, ← chainRowW_eq]
  exact maskAt_row_ge answers messages a value hlo (by omega)
theorem wotsSeed_maskAt (lay : Layer) (tree leaf i : Nat) :
    WCT9.wotsSeed (maskAt answers messages a) lay tree leaf i = WCT9.wotsSeed answers lay tree leaf i :=
  wotsSeed_congr_private (fun c => maskAt_private answers messages a c) lay tree leaf i
theorem eval_honestChain_maskAt (lay : Layer) (tree leaf i count : Nat) (hi : i < chainCount lay)
    (hc : count ≤ 256) (hb : SlotOK a lay leaf)
    (halias : LeafAlias lay tree leaf a.key → i = a.chain → depth answers messages a ≤ count) :
    evalWithAnswerFn (maskAt answers messages a) (WCT9.chainW lay tree leaf i 0 count (WCT9.wotsSeed (maskAt answers messages a) lay tree leaf i)) =
      evalWithAnswerFn answers (WCT9.chainW lay tree leaf i 0 count (WCT9.wotsSeed answers lay tree leaf i)) := by
  by_cases hd : depth answers messages a = 0
  · rw [maskAt_of_depth_zero answers messages a hd]
  have hi' : i < 2 ^ 24 := by
    have := chainCount_le lay
    simp only [Nat.reducePow]; omega
  have hc' : a.chain < 2 ^ 24 := by
    have := chain_lt_of_depth answers messages a (by omega)
    have := chainCount_le a.key.lay
    simp only [Nat.reducePow]; omega
  by_cases hal' : LeafAlias lay tree leaf a.key ∧ i = a.chain
  · obtain ⟨hal', rfl⟩ := hal'
    have hb' : leaf < 2 ^ 24 ∧ a.key.leaf < 2 ^ 24 := hb
    rw [chainW_alias hal', wotsSeed_alias _ hal' hb', wotsSeed_alias _ hal' hb']
    exact eval_chain_maskAt answers messages a (by omega) (halias hal' rfl) hc _
  · rw [wotsSeed_maskAt answers messages a lay tree leaf i]
    apply eval_maskAt_of_respects
    refine respects_chainW' _ _ _ _ _ _ _ fun step value hlo hhi => ?_
    rw [pad64_chainInputW]
    intro s' v' hs' heq
    have hstep' : step < 256 := by omega
    have h := chainInputW_eq_chainRowW hi' hc' hstep' (by omega) heq
    exact hal' ⟨h.1, h.2.1⟩
theorem wotsEnd_maskAt (lay : Layer) (tree leaf i : Nat) (hi : i < chainCount lay) (hb : SlotOK a lay leaf) :
    WCT9.wotsEnd (maskAt answers messages a) lay tree leaf i = WCT9.wotsEnd answers lay tree leaf i := by
  unfold WCT9.wotsEnd
  apply eval_honestChain_maskAt answers messages a lay tree leaf i _ hi (by have := width_le lay i; omega) hb
  intro hal' hia
  obtain ⟨hl', -, -⟩ := hal'
  subst hl' hia
  exact depth_le answers messages a hi
theorem wotsValue_maskAt (lay : Layer) (tree leaf : Nat) (digits : List Nat) (i : Nat) (hi : i < chainCount lay)
    (hdig : digits.getD i 0 ≤ 256) (hb : SlotOK a lay leaf)
    (halias : LeafAlias lay tree leaf a.key → i = a.chain → depth answers messages a ≤ digits.getD i 0) :
    WCT9.wotsValue (maskAt answers messages a) lay tree leaf digits i = WCT9.wotsValue answers lay tree leaf digits i :=
  eval_honestChain_maskAt answers messages a lay tree leaf i _ hi hdig hb halias
theorem wotsRoot_maskAt (lay : Layer) (tree leaf : Nat) (hb : SlotOK a lay leaf) :
    WCT9.wotsRoot (maskAt answers messages a) lay tree leaf = WCT9.wotsRoot answers lay tree leaf := by
  unfold WCT9.wotsRoot
  rw [List.map_congr_left (fun i hi => wotsEnd_maskAt answers messages a lay tree leaf i (List.mem_range.mp hi) hb)]
  exact eval_maskAt_of_respects answers messages a (respectsP_lowerLeafHash a _ _ _ _
    (by simp only [List.length_map, List.length_range]; exact SigGolfCandidate.T3.Security.Wots.Enc.chainCount_ge4 _))
theorem wotsTree_maskAt (lay : Layer) (tree : Nat) (hal : MaskOK a) :
    WCT9.wotsTree (maskAt answers messages a) lay tree = WCT9.wotsTree answers lay tree := by
  have hroots : (List.range (2 ^ height lay)).map (WCT9.wotsRoot (maskAt answers messages a) lay tree) =
      (List.range (2 ^ height lay)).map (WCT9.wotsRoot answers lay tree) :=
    List.map_congr_left (fun leaf hleaf => wotsRoot_maskAt answers messages a lay tree leaf
      (slotOK_of hal (by have := List.mem_range.mp hleaf; have := height_pow_le lay; omega)))
  unfold WCT9.wotsTree
  rw [hroots]
  split_ifs with h0
  · exact eval_maskAt_of_respects answers messages a (respectsP_buildTopLevels a _)
  · exact eval_maskAt_of_respects answers messages a (respectsP_lowerLevels a _ _ _ (by fin_cases lay <;> decide) _
      (by simp only [List.length_map, List.length_range]; exact le_rfl))
theorem builtTree_maskAt_top (hal : MaskOK a) :
    builtTree (maskAt answers messages a) 0 0 = builtTree answers 0 0 := by
  rw [← WCT9.wotsTree_top, ← WCT9.wotsTree_top, wotsTree_maskAt answers messages a 0 0 hal]
theorem leafRoot_maskAt_top (leaf : Nat) (hl : leaf < 2 ^ 24) (hal : MaskOK a) :
    Correctness.leafRoot (maskAt answers messages a) 0 0 leaf = Correctness.leafRoot answers 0 0 leaf := by
  rw [← WCT9.wotsRoot_top, ← WCT9.wotsRoot_top, wotsRoot_maskAt answers messages a 0 0 leaf (slotOK_of hal hl)]
theorem honestPair_maskAt (lay : Layer) (tree : Nat) (hal : MaskOK a) :
    Extract.honestPair (maskAt answers messages a) lay tree = Extract.honestPair answers lay tree := by
  unfold Extract.honestPair
  rw [wotsTree_maskAt answers messages a lay tree hal]
end Mask
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Mask
open SigGolfCandidate.T3.Security.Wots.Mask
open ClaudeWCT.W9.T3.Security.Wots.Mask

theorem respects_layerCounterSearchAt (a : ChainAddr) (lay : Layer) (floor tree leaf : Nat)
    (msg : WCT9.LayerMsg) : ∀ fuel counter,
    Respects (Untouched a) (WCT9.CanonicalPolicy.layerCounterSearchAt lay floor tree leaf msg counter fuel) := by
  intro fuel
  induction fuel with
  | zero => intro counter; exact Respects.pure' _
  | succ fuel ih =>
      intro counter
      simp only [WCT9.CanonicalPolicy.layerCounterSearchAt]
      refine Respects.bind (Respects.publicHash _ (untouched_layerEncoding a _ _ _ _ _)) fun answer => ?_
      split
      · exact ih _
      · exact Respects.pure' _

theorem respectsP_layerCounterSearchAt (a : ChainAddr) (lay : Layer) (floor tree leaf : Nat)
    (msg : WCT9.LayerMsg) (fuel counter : Nat) :
    Respects (UntouchedP a) (WCT9.CanonicalPolicy.layerCounterSearchAt lay floor tree leaf msg counter fuel) :=
  Respects.untouchedP (fun c => respects_layerCounterSearchAt c lay floor tree leaf msg fuel counter) a
end Mask

theorem searchOf_maskAt (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (a : ChainAddr) (L : LeafAddr) (remaining : Nat) :
    searchOf (maskAt answers messages a) messages L remaining = searchOf answers messages L remaining := by
  unfold searchOf
  exact Mask.eval_maskAt_of_respects answers messages a
    (Mask.respectsP_layerCounterSearchAt a _ _ _ _ _ _ _)

theorem referenceContext_maskAt (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (a : ChainAddr) :
    referenceContext (maskAt answers messages a) messages = referenceContext answers messages :=
  referenceContext_congr (fun L remaining _ => searchOf_maskAt answers messages a L remaining)

theorem referenceSearch_maskAt (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (a : ChainAddr) (L : LeafAddr) :
    referenceSearch (maskAt answers messages a) messages L = referenceSearch answers messages L :=
  referenceSearch_congr (fun L remaining _ => searchOf_maskAt answers messages a L remaining) L

theorem referenceDigits_maskAt (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (a : ChainAddr) (L : LeafAddr) :
    referenceDigits (maskAt answers messages a) messages L = referenceDigits answers messages L := by
  unfold referenceDigits
  rw [referenceSearch_maskAt]

theorem referenceInput_maskAt (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (a : ChainAddr) (L : LeafAddr) :
    referenceInput (maskAt answers messages a) messages L = referenceInput answers messages L := by
  unfold referenceInput
  rw [referenceSearch_maskAt]

theorem depth_maskAt_all (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (a b : ChainAddr) : depth (maskAt answers messages a) messages b = depth answers messages b := by
  unfold depth
  rw [referenceDigits_maskAt]

theorem frontierValue_maskAt_other (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (a b : ChainAddr) (hb : b.chain < chainCount b.key.lay) (hbl : b.key.leaf < 2 ^ 24)
    (hal : Wots.Mask.MaskOK a)
    (halias : SigGolfCandidate.T3.Security.Wots.Mask.LeafAlias b.key.lay b.key.tree b.key.leaf a.key →
      b.chain = a.chain → depth answers messages a ≤ depth answers messages b) :
    frontierValue (maskAt answers messages a) messages b = frontierValue answers messages b := by
  -- C3 (#866): the frontier is the chain of the current scheme (`honestChainValueW`).
  unfold frontierValue ClaudeWCT.W9.T3.Security.Wots.honestChainValueW
  rw [depth_maskAt_all]
  exact Mask.eval_honestChain_maskAt answers messages a _ _ _ _ _ hb
    (by have := Mask.depth_le_seven answers messages b; omega)
    (Wots.Mask.slotOK_of hal hbl) halias

theorem frontierValue_maskAt_bounded (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (a b : ChainAddr)
    (ha : a.key.tree < 2 ^ 40 ∧ a.key.leaf < 2 ^ 24)
    (hb : b.key.tree < 2 ^ 40 ∧ b.key.leaf < 2 ^ 24)
    (hc : b.chain < chainCount b.key.lay) :
    frontierValue (maskAt answers messages a) messages b = frontierValue answers messages b := by
  apply frontierValue_maskAt_other answers messages a b hc hb.2 ha.2
  intro hal hch
  have hk : b.key = a.key := by
    have := hal.eq_of_lt hb.1 (by omega) ha.1 (by omega)
    cases hbk : b.key
    rw [hbk] at this
    exact this
  have : b = a := by
    cases b; cases a
    simp only at hk hch
    rw [hk, hch]
  rw [this]

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
