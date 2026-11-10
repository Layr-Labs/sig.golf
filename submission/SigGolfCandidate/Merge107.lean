import SigGolfCandidate.Merge019
import SigGolfCandidate.Merge021
import SigGolfCandidate.Merge033
import SigGolfCandidate.Merge057
import SigGolfCandidate.Merge058
import SigGolfCandidate.Merge098
import SigGolfCandidate.Merge105
import SigGolfCandidate.Merge106

-- ==== merged from ClaudeWCT_W9_T3_Secc_LargeContactCase ====
section

section
namespace ClaudeWCT.W9.T3.Security.WotsExtract
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.Wots (LeafAddr ChainAddr Entry low entriesOf word_cases)
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.W9.T3M (wrho wdc layerP wchainPads wchainHeaderPad wmerklePad wpath wvalueFor wbcCtr wbcPad wbcRight
  wmerkleHigh wbcHigh wleafHigh wtopLeafPad)
open SigGolfCandidate.T3.Security.WotsExtract (SourceLeaf SourceChain entriesOf_mono mem_entriesOf routeLeaf
  routeLeaf_source)
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def WotsPrimitiveRoute (index : Nat) (answers : Answers) (trace : List Entry) : Prop :=
  (∃ lay, EncodingMatchAt answers trace (routeLeaf index lay)) ∨ StructuralHitSrc answers trace ∨
    (∃ a, SourceChain a ∧ TwoEdgeAt answers trace a) ∨
    (∃ a b, SourceChain a ∧ SourceChain b ∧ a ≠ b ∧ ContactAt answers trace a ∧ ContactAt answers trace b) ∨
    (∃ a, SourceChain a ∧ MarkerAt answers trace a ∧ ContactAt answers trace a)
theorem WotsPrimitiveRoute.mono {index : Nat} {answers : Answers} {trace trace' : List Entry}
    (h : WotsPrimitiveRoute index answers trace) (hsub : ∀ e ∈ trace, e ∈ trace') :
    WotsPrimitiveRoute index answers trace' := by
  rcases h with ⟨lay, h⟩ | h | ⟨a, ha, h⟩ | ⟨a, b, ha, hb, hab, h1, h2⟩ | ⟨a, ha, hm, hc⟩
  · exact Or.inl ⟨lay, encodingMatchAt_mono h hsub⟩
  · exact Or.inr (Or.inl (structuralHitSrc_mono h hsub))
  · exact Or.inr (Or.inr (Or.inl ⟨a, ha, twoEdgeAt_mono h hsub⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, ha, hb, hab, contactAt_mono h1 hsub, contactAt_mono h2 hsub⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a, ha, markerAt_mono hm hsub, contactAt_mono hc hsub⟩)))
theorem frame_wots_route (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (msg : WCT9.LayerMsg)
    (digits : List Nat) (hidx : index < 2 ^ 31) (hfit : Extract.msgFits lay msg)
    (hframe : Extract.Frame answers w index lay msg digits)
    (qs : List Spec.Domain) (henc : Extract.encodingQuery w index lay msg ∈ qs)
    (hmerkle : ∀ j, j < height lay →
      wpath w lay (route index lay).1 j =
          treeValue (WCT9.wotsTree answers lay (route index lay).2) j ((route index lay).1 / 2 ^ j ^^^ 1) ∧
        (j + 1 < height lay ∨ lay.val = 0 → wmerklePad w lay (route index lay).1 j =
          WCT9.nonceDigest (WCT9.honestNonce answers lay (route index lay).2 j ((route index lay).1 / 2 ^ (j + 1)))) ∧
        (j + 1 < height lay ∨ lay.val = 0 → wmerkleHigh w lay (route index lay).1 j = 0))
    (hleaf : wleafHigh w lay = 0)
    (hchains : ∀ i, i < chainCount lay →
      (depth answers ⟨routeLeaf index lay, i⟩ ≤ digits.getD i 0 →
        wvalueFor w lay digits i = WCT9.wotsValue answers lay (route index lay).2 (route index lay).1 digits i ∧
          (digits.getD i 0 < maxDigit lay i →
            wchainPads w lay i = (0, 0) ∧ wchainHeaderPad w lay i = 0)) ∧
      (digits.getD i 0 < depth answers ⟨routeLeaf index lay, i⟩ →
        ContactAt answers (entriesOf answers qs) ⟨routeLeaf index lay, i⟩ ∧
          (digits.getD i 0 + 2 ≤ depth answers ⟨routeLeaf index lay, i⟩ →
            TwoEdgeAt answers (entriesOf answers qs) ⟨routeLeaf index lay, i⟩))) :
    WotsPrimitiveRoute index answers (entriesOf answers qs) ∨
      (msg = Extract.honestMsg answers index lay ∧ BC.GoodZ answers w index lay) := by
  classical
  have hdec : decode (routeLeaf index lay).lay
      (WCT9.encodingAnswer (routeLeaf index lay).lay (answers (.inl (.inr (encRow (routeLeaf index lay) msg (wbcCtr w index lay) (wbcPad w index lay, wbcRight w, wbcHigh w index lay ^^^ 1)))))) = some digits := by
    rw [encRow_wit]; exact hframe.2
  have hfit' : Extract.msgFits (routeLeaf index lay).lay msg := hfit
  have hencE : (encRow (routeLeaf index lay) msg (wbcCtr w index lay) (wbcPad w index lay, wbcRight w, wbcHigh w index lay ^^^ 1),
      answers (.inl (.inr (encRow (routeLeaf index lay) msg (wbcCtr w index lay) (wbcPad w index lay, wbcRight w, wbcHigh w index lay ^^^ 1))))) ∈
        entriesOf answers qs := by
    rw [encRow_wit]; exact mem_entriesOf henc
  have hsrc : SourceLeaf (routeLeaf index lay) := routeLeaf_source index lay hidx
  have hsrcC : ∀ i, i < chainCount lay → SourceChain ⟨routeLeaf index lay, i⟩ := fun i hi => ⟨hsrc, hi⟩
  have hcontact : ∀ i, i < chainCount lay → digits.getD i 0 < depth answers ⟨routeLeaf index lay, i⟩ →
      ContactAt answers (entriesOf answers qs) ⟨routeLeaf index lay, i⟩ := fun i hi hlt =>
    ((hchains i hi).2 hlt).1
  obtain ⟨refDigest, hr⟩ := referenceDigits_decode answers (routeLeaf index lay)
  rcases word_cases hr hdec with heq | ⟨i, hu⟩ | ⟨i, h2⟩ | ⟨i, j, hij, hi, hj⟩
  · have hshape : Extract.LayerShaped answers w index lay digits := by
      refine ⟨hmerkle, fun i hi => ?_, hleaf⟩
      have hdi : depth answers ⟨routeLeaf index lay, i⟩ = digits.getD i 0 := by
        unfold depth
        rw [heq]
      exact (hchains i hi).1 (le_of_eq hdi)
    by_cases hm : msg = Extract.honestMsg answers index lay
    · by_cases hp : wbcPad w index lay = 0 ∧ wbcHigh w index lay = 1
      · exact Or.inr ⟨hm, ⟨digits, hm ▸ hframe, hshape⟩, hp⟩
      · have hpad : (wbcPad w index lay, wbcRight w, wbcHigh w index lay ^^^ 1).1 ≠ 0 ∨
            (wbcPad w index lay, wbcRight w, wbcHigh w index lay ^^^ 1).2.2 ≠ 0 := by
          by_cases hp1 : wbcPad w index lay = 0
          · right
            intro h1
            apply hp
            refine ⟨hp1, ?_⟩
            simpa using h1
          · exact Or.inl hp1
        refine Or.inl (Or.inl ⟨lay, msg, wbcCtr w index lay, (wbcPad w index lay, wbcRight w, wbcHigh w index lay ^^^ 1), _, hfit', hencE,
          ?_, ?_⟩)
        · exact referenceInput_ne_pad answers _ msg _ _ hfit' hpad
        · rw [← heq]; exact hdec
    · refine Or.inl (Or.inl ⟨lay, msg, wbcCtr w index lay, (wbcPad w index lay, wbcRight w, wbcHigh w index lay ^^^ 1), _, hfit', hencE,
        ?_, ?_⟩)
      · exact referenceInput_ne answers _ msg _ _ hfit' hdec (Or.inl (by rw [leafMsg_route _ _ _ hidx]; exact hm))
      · rw [← heq]; exact hdec
  · have hlow : digits.getD i.val 0 + 1 = (referenceDigits answers (routeLeaf index lay)).getD i.val 0 := hu.2.2.1
    have hne : digits ≠ referenceDigits answers (routeLeaf index lay) := by
      intro he; rw [he] at hlow; omega
    refine Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨routeLeaf index lay, i.val⟩, hsrcC i.val i.isLt,
      ⟨msg, wbcCtr w index lay, (wbcPad w index lay, wbcRight w, wbcHigh w index lay ^^^ 1), _, digits, hfit', hencE,
        referenceInput_ne answers _ msg _ _ hfit' hdec (Or.inr hne), hdec, hlow, ?_⟩,
      hcontact i.val i.isLt (by show _ < (referenceDigits answers (routeLeaf index lay)).getD i.val 0; omega)⟩))))
    intro k hk
    by_cases hkc : k < chainCount lay
    · exact hu.2.2.2 ⟨k, hkc⟩ (fun he => hk (congrArg Fin.val he))
    · rw [List.getD_eq_default _ _ (by rw [referenceDigits_length]; exact not_lt.mp hkc)]
      exact Nat.zero_le _
  · refine Or.inl (Or.inr (Or.inr (Or.inl ⟨⟨routeLeaf index lay, i.val⟩, hsrcC i.val i.isLt, ?_⟩)))
    have hlt : digits.getD i.val 0 < depth answers ⟨routeLeaf index lay, i.val⟩ := by
      have e1 : (decodedWord hdec i).val = digits.getD i.val 0 := rfl
      have e2 : (decodedWord hr i).val = depth answers ⟨routeLeaf index lay, i.val⟩ := rfl
      omega
    exact ((hchains i.val i.isLt).2 hlt).2 h2
  · refine Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨routeLeaf index lay, i.val⟩, ⟨routeLeaf index lay, j.val⟩,
      hsrcC i.val i.isLt, hsrcC j.val j.isLt, ?_, hcontact i.val i.isLt hi, hcontact j.val j.isLt hj⟩))))
    intro he
    exact hij (Fin.ext (ChainAddr.mk.inj he).2)
theorem layer_wots_route (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (msg : WCT9.LayerMsg)
    (digits : List Nat) (hidx : index < 2 ^ 31) (hlay0 : lay = 0) (hfit : Extract.msgFits lay msg)
    (hframe : Extract.Frame answers w index lay msg digits)
    (qs : List Spec.Domain) (henc : Extract.encodingQuery w index lay msg ∈ qs)
    (hsub : ∀ q ∈ queried answers (layerP w index lay digits), q ∈ qs)
    (reaches : evalWithAnswerFn answers (layerP w index lay digits) =
      Extract.honestRoot answers lay (route index lay).2) :
    WotsPrimitiveRoute index answers (entriesOf answers qs) ∨
      (msg = Extract.honestMsg answers index lay ∧ BC.GoodZ answers w index lay) := by
  have hvalid := Cost.validDigits_decode hframe.2
  have hmono := entriesOf_mono (answers := answers) hsub
  rcases layerP_wots answers w index lay digits hidx hlay0 hvalid reaches with hS | ⟨hmerkle, hchains, hleaf⟩
  · exact Or.inl (Or.inr (Or.inl (structuralHitSrc_mono hS hmono)))
  have hl0 : lay.val = 0 := by rw [hlay0]; rfl
  exact frame_wots_route answers w index lay msg digits hidx hfit hframe qs henc
    (fun j hj => ⟨(hmerkle j hj).1, fun _ => (hmerkle j hj).2.1, fun _ => (hmerkle j hj).2.2⟩) hleaf
    (fun i hi => ⟨(hchains i hi).1, fun hlt => ⟨contactAt_mono ((hchains i hi).2 hlt).1 hmono,
      fun h2 => twoEdgeAt_mono (((hchains i hi).2 hlt).2 h2) hmono⟩⟩)
theorem layerPair_wots_route (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (msg : WCT9.LayerMsg)
    (digits : List Nat) (hidx : index < 2 ^ 31) (hlay : lay.val ≠ 0) (hfit : Extract.msgFits lay msg)
    (hframe : Extract.Frame answers w index lay msg digits)
    (qs : List Spec.Domain) (henc : Extract.encodingQuery w index lay msg ∈ qs)
    (hsub : ∀ q ∈ queried answers (layerPairP w index lay digits), q ∈ qs)
    (reaches : evalWithAnswerFn answers (layerPairP w index lay digits) =
      Extract.honestPair answers lay (route index lay).2) :
    WotsPrimitiveRoute index answers (entriesOf answers qs) ∨
      (msg = Extract.honestMsg answers index lay ∧ BC.GoodZ answers w index lay) := by
  have hvalid := Cost.validDigits_decode hframe.2
  have hmono := entriesOf_mono (answers := answers) hsub
  rcases layerPairP_wots answers w index lay digits hidx hvalid hlay reaches with hS | ⟨hmerkle, hchains, hleaf⟩
  · exact Or.inl (Or.inr (Or.inl (structuralHitSrc_mono hS hmono)))
  exact frame_wots_route answers w index lay msg digits hidx hfit hframe qs henc
    (fun j hj => ⟨(hmerkle j hj).1, fun h => by
        rw [WCT9.honestNonce_lower answers (fun h0 => hlay (by rw [h0]; rfl)), WCT9.nonceDigest_zero]
        exact ((hmerkle j hj).2 (h.resolve_right hlay)).1,
      fun h => ((hmerkle j hj).2 (h.resolve_right hlay)).2⟩) hleaf
    (fun i hi => ⟨(hchains i hi).1, fun hlt => ⟨contactAt_mono ((hchains i hi).2 hlt).1 hmono,
      fun h2 => twoEdgeAt_mono (((hchains i hi).2 hlt).2 h2) hmono⟩⟩)
theorem layersBC_wots_walk_route (answers : Answers) (w : WBytes) (index : Nat) (hidx : index < 2 ^ 31) :
    ∀ n, 1 ≤ n → n ≤ 4 → ∀ msg : WCT9.LayerMsg, Extract.msgFits (Fin.ofNat 4 (n - 1)) msg →
    evalWithAnswerFn answers (layersBC w index n msg) = some (Extract.honestRoot answers 0 0) →
    WotsPrimitiveRoute index answers (entriesOf answers (queried answers (layersBC w index n msg))) ∨
    ((∀ l : Layer, l.val < n → BC.GoodZ answers w index l) ∧
      msg = Extract.honestMsg answers index (Fin.ofNat 4 (n - 1)))
  | 0, h1, _, _, _, _ => absurd h1 (by decide)
  | n + 1, _, hn, msg, hfit, h => by
      classical
      obtain ⟨digits, hframe, henc, htop, hlow⟩ := Extract.layersBC_succ_split answers w index n msg _ h
      have hval : (Fin.ofNat 4 n : Layer).val = n := Extract.ofNat_val n (by omega)
      simp only [Nat.add_sub_cancel] at hfit ⊢
      have finish : WotsPrimitiveRoute index answers (entriesOf answers (queried answers (layersBC w index (n + 1) msg))) ∨
          (msg = Extract.honestMsg answers index (Fin.ofNat 4 n) ∧ BC.GoodZ answers w index (Fin.ofNat 4 n)) →
          (∀ l : Layer, l.val < n → BC.GoodZ answers w index l) →
          WotsPrimitiveRoute index answers (entriesOf answers (queried answers (layersBC w index (n + 1) msg))) ∨
          ((∀ l : Layer, l.val < n + 1 → BC.GoodZ answers w index l) ∧
            msg = Extract.honestMsg answers index (Fin.ofNat 4 n)) := by
        intro hx hgood
        rcases hx with hprim | ⟨hmsg, hgoodn⟩
        · exact Or.inl hprim
        · right
          refine ⟨fun l hl => ?_, hmsg⟩
          by_cases hle : l.val < n
          · exact hgood l hle
          · have hl : l = Fin.ofNat 4 n := Fin.ext (by rw [hval]; omega)
            subst hl
            exact hgoodn
      by_cases hn0 : n = 0
      · subst hn0
        obtain ⟨hout, hq⟩ := htop rfl
        have hroot : evalWithAnswerFn answers (layerP w index (Fin.ofNat 4 0) digits) =
            Extract.honestRoot answers (Fin.ofNat 4 0) (route index (Fin.ofNat 4 0)).2 := by
          rw [hout, show (Fin.ofNat 4 0 : Layer) = 0 from rfl, SigGolfCandidate.T3.route_top_tree index hidx]
        exact finish (layer_wots_route answers w index (Fin.ofNat 4 0) msg digits hidx rfl hfit hframe _ henc hq hroot)
          (fun l hl => absurd hl (by omega))
      · obtain ⟨hrest, hqP, hqR⟩ := hlow hn0
        have hfit' : Extract.msgFits (Fin.ofNat 4 (n - 1))
            (.pair (evalWithAnswerFn answers (layerPairP w index (Fin.ofNat 4 n) digits)).1
              (evalWithAnswerFn answers (layerPairP w index (Fin.ofNat 4 n) digits)).2) := trivial
        rcases layersBC_wots_walk_route answers w index hidx n (by omega) (by omega) _ hfit' hrest with
          hprim | ⟨hgood, hmsg⟩
        · exact Or.inl (hprim.mono (entriesOf_mono hqR))
        · rw [Extract.honestMsg_lower answers index n (by omega) (by omega)] at hmsg
          have hpair : evalWithAnswerFn answers (layerPairP w index (Fin.ofNat 4 n) digits) =
              Extract.honestPair answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2 := by
            simp only [WCT9.LayerMsg.pair.injEq] at hmsg
            exact Prod.ext hmsg.1 hmsg.2
          exact finish (layerPair_wots_route answers w index (Fin.ofNat 4 n) msg digits hidx
            (by rw [hval]; exact hn0) hfit hframe _ henc hqP hpair) hgood
theorem verifyP_walk_wots_route (answers : Answers) (m : Message) (pk : Digest) (w : WBytes)
    (hpk : pk = Extract.honestRoot answers 0 0)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true) :
    ∃ N : HashOutput, (wdc w).toNat < WCT9.digestVerifyWindow ∧
      evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N ∧
      (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : Spec.Domain) ∈ queried answers (verifyP m pk w) ∧
      Shaped N w ∧
      (WotsPrimitiveRoute (WCT9.digestIndex N) answers (entriesOf answers (queried answers (verifyP m pk w))) ∨
       ((∀ l : Layer, BC.GoodZ answers w (WCT9.digestIndex N) l) ∧
          evalWithAnswerFn answers
              (recoverFtsP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) N) =
            Extract.honestTop answers (WCT9.digestIndex N) ∧
          ∀ q ∈ queried answers (recoverFtsP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) N),
            q ∈ queried answers (verifyP m pk w))) := by
  classical
  obtain ⟨N, hdc, hN, hdq, hS, hlay, hqF, hqL⟩ := WctExtract.verifyP_walk_wct answers m pk w hv
  refine ⟨N, hdc, hN, hdq, hS, ?_⟩
  have hidx : WCT9.digestIndex N < 2 ^ 31 := Nat.mod_lt _ (by norm_num)
  rcases layersBC_wots_walk_route answers w (WCT9.digestIndex N) hidx 4 (by decide) le_rfl (.pair _ _) trivial
      (hpk ▸ hlay) with
    hprim | ⟨hgood, hroot⟩
  · exact Or.inl (hprim.mono (entriesOf_mono hqL))
  · right
    refine ⟨fun l => hgood l l.isLt, ?_, hqF⟩
    rw [show (4 - 1 : Nat) = 3 from rfl, Extract.honestMsg_three] at hroot
    simp only [WCT9.LayerMsg.pair.injEq] at hroot
    exact Prod.ext hroot.1 hroot.2
theorem verifyP_wots_cases_route (answers : Answers) (m : Message) (pk : Digest) (w : WBytes)
    (hpk : pk = Extract.honestRoot answers 0 0)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true) :
    ∃ N : HashOutput, (wdc w).toNat < WCT9.digestVerifyWindow ∧
      evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N ∧
      (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : Spec.Domain) ∈ queried answers (verifyP m pk w) ∧
      Shaped N w ∧
      (WotsPrimitiveRoute (WCT9.digestIndex N) answers (entriesOf answers (queried answers (verifyP m pk w))) ∨
       ((∀ l : Layer, BC.GoodZ answers w (WCT9.digestIndex N) l) ∧ WctExtract.WctHonest answers N w ∧
         ∀ q ∈ queried answers (recoverFtsP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) N),
            q ∈ queried answers (verifyP m pk w))) := by
  classical
  obtain ⟨N, hdc, hN, hdq, hS, hcase⟩ := verifyP_walk_wots_route answers m pk w hpk hv
  refine ⟨N, hdc, hN, hdq, hS, ?_⟩
  rcases hcase with hprim | ⟨hgood, hR, hqV⟩
  · exact Or.inl hprim
  rcases fts_structural answers N w hS hR with hhit | hshape
  · exact Or.inl (Or.inr (Or.inl (structuralHitSrc_mono hhit (entriesOf_mono hqV))))
  · exact Or.inr ⟨hgood, hshape, hqV⟩
end ClaudeWCT.W9.T3.Security.WotsExtract
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers leafSeed)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (listBlock slotValue routeAddr IsDigestRow)
open SigGolfCandidate.T3.Security.LargeCoupling (wotsAddr)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeContactChain : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
theorem known_secret {D : Coord → Prop} {s : SeedIndex} (h : Known D (.inr s)) : D (.inr s) := by
  cases h with
  | base h => exact h
theorem known_chain_aux {D : Coord → Prop} {c : Coord} (h : Known D c) :
    ∀ p : ChainGraph.Point, c = .inl (.chain p) →
      (∃ s : Fin 7, s.val ≤ p.2.val ∧ D (.inl (.chain (p.1, s)))) ∨ D (.inr (.inl p.1)) := by
  induction h with
  | base hc =>
      intro p hp
      subst hp
      exact Or.inl ⟨p.2, le_rfl, hc⟩
  | @node N hall ih =>
      intro p hp
      simp only [Sum.inl.injEq] at hp
      subst hp
      have hmem : (chainChild p, if WCT9.isG p.1.layer p.1.chain.val then 0 else 3) ∈ childSlots (.chain p) := by simp [childSlots]
      have hk := hall _ hmem
      have hih := ih _ hmem
      unfold chainChild at hk hih
      by_cases h0 : p.2.val = 0
      · rw [if_pos h0] at hk
        exact Or.inr (known_secret hk)
      · rw [if_neg h0] at hih
        rcases hih (ChainGraph.predecessor p) rfl with ⟨s, hs, hd⟩ | hd
        · refine Or.inl ⟨s, ?_, hd⟩
          simp only [ChainGraph.predecessor] at hs
          omega
        · exact Or.inr hd
theorem known_chain {D : Coord → Prop} {p : ChainGraph.Point} (h : Known D (.inl (.chain p))) :
    (∃ s : Fin 7, s.val ≤ p.2.val ∧ D (.inl (.chain (p.1, s)))) ∨ D (.inr (.inl p.1)) :=
  known_chain_aux h p rfl
theorem wctItem_zero (a : CanonGraph.WctAddr) : wctItem a 0 = .inr (.inr a) := rfl
theorem wctItem_succ (a : CanonGraph.WctAddr) (s : Fin 4) :
    wctItem a (s.val + 1) = .inl (.wctChain (a, s)) := by
  have h : (⟨(s.val + 1 - 1) % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4) = s :=
    Fin.ext (by rw [Nat.add_sub_cancel]; exact Nat.mod_eq_of_lt s.isLt)
  unfold wctItem
  rw [if_neg (Nat.succ_ne_zero _), h]
theorem wctItem_pos (a : CanonGraph.WctAddr) (p : Nat) (h0 : p ≠ 0) (hp : p ≤ 4) :
    wctItem a p = .inl (.wctChain (a, ⟨p - 1, by omega⟩)) := by
  have h : (⟨(p - 1) % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4) = ⟨p - 1, by omega⟩ :=
    Fin.ext (Nat.mod_eq_of_lt (by omega))
  unfold wctItem
  rw [if_neg h0, h]
theorem known_wct_aux {D : Coord → Prop} {c : Coord} (h : Known D c) :
    ∀ (a : CanonGraph.WctAddr) (s : Fin 4), c = .inl (.wctChain (a, s)) →
      ∃ p' ≤ s.val + 1, D (wctItem a p') := by
  induction h with
  | base hc =>
      intro a s hs
      subst hs
      exact ⟨s.val + 1, le_rfl, by rw [wctItem_succ]; exact hc⟩
  | @node N hall ih =>
      intro a s hN
      simp only [Sum.inl.injEq] at hN
      subst hN
      have hmem : (wctItem a s.val, if WCT9.ftsIsG a.2.2.2.val then 0 else 3) ∈ childSlots (.wctChain (a, s)) := by
        simp [childSlots]
      have hk := hall _ hmem
      have hih := ih _ hmem
      by_cases h0 : s.val = 0
      · rw [h0, wctItem_zero] at hk
        refine ⟨0, Nat.zero_le _, ?_⟩
        rw [wctItem_zero]
        exact known_secret hk
      · have hs1 : s.val - 1 < 4 := by omega
        have he := wctItem_pos a s.val h0 (by omega)
        obtain ⟨p', hp', hd⟩ := hih a ⟨s.val - 1, hs1⟩ he
        exact ⟨p', by simp only at hp'; omega, hd⟩
theorem known_wctItem {D : Coord → Prop} {a : CanonGraph.WctAddr} {p : Nat} (hp : p ≤ 4)
    (h : Known D (wctItem a p)) : ∃ p' ≤ p, D (wctItem a p') := by
  by_cases h0 : p = 0
  · subst h0
    rw [wctItem_zero] at h
    exact ⟨0, le_rfl, by rw [wctItem_zero]; exact known_secret h⟩
  · have hs : p - 1 < 4 := by omega
    have he := wctItem_pos a p h0 hp
    rw [he] at h
    obtain ⟨p', hp', hd⟩ := known_wct_aux h a ⟨p - 1, hs⟩ rfl
    exact ⟨p', by simp only at hp'; omega, hd⟩
theorem wctItem_injective {a b : CanonGraph.WctAddr} {p q : Nat} (hp : p ≤ 4) (hq : q ≤ 4)
    (h : wctItem a p = wctItem b q) : a = b ∧ p = q := by
  unfold wctItem at h
  by_cases hp0 : p = 0 <;> by_cases hq0 : q = 0
  · rw [if_pos hp0, if_pos hq0] at h
    simp only [Sum.inr.injEq] at h
    exact ⟨h, by omega⟩
  · rw [if_pos hp0, if_neg hq0] at h; cases h
  · rw [if_neg hp0, if_pos hq0] at h; cases h
  · rw [if_neg hp0, if_neg hq0] at h
    simp only [Sum.inl.injEq, CanonGraph.Node.wctChain.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have h3 := congrArg Fin.val h2
    simp only at h3
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h3
    exact ⟨h1, by omega⟩
theorem chainItem_chain {L : CanonGraph.LeafPos} {i d : Nat} {p : ChainGraph.Point}
    (h : chainItem L i d = .inl (.chain p)) :
    p.1 = ⟨L.lay, L.tree, L.leaf, CanonGraph.fin58 i⟩ ∧ d ≠ 0 ∧ p.2.val = (d - 1) % 7 := by
  unfold chainItem at h
  by_cases hd : d = 0
  · rw [if_pos hd] at h
    cases h
  · rw [if_neg hd] at h
    simp only [Sum.inl.injEq, CanonGraph.Node.chain.injEq] at h
    subst h
    exact ⟨rfl, hd, rfl⟩
theorem chainItem_seed {L : CanonGraph.LeafPos} {i d : Nat} {a : ChainGraph.Address}
    (h : chainItem L i d = .inr (.inl a)) :
    a = ⟨L.lay, L.tree, L.leaf, CanonGraph.fin58 i⟩ ∧ d = 0 := by
  unfold chainItem at h
  by_cases hd : d = 0
  · rw [if_pos hd] at h
    simp only [Sum.inr.injEq, Sum.inl.injEq] at h
    exact ⟨h.symm, hd⟩
  · rw [if_neg hd] at h
    cases h
def NotChain (c : Coord) : Prop := (∀ p, c ≠ .inl (.chain p)) ∧ (∀ a, c ≠ .inr (.inl a))
theorem treeChild_not_chain {lay : Layer} {tree : Fin (2^31)} {level n : Nat} {d : Coord}
    (hd : treeChild lay tree level n = some d) : NotChain d := by
  unfold treeChild at hd
  by_cases h0 : level = 0
  · rw [if_pos h0, Option.map_eq_some_iff] at hd
    obtain ⟨L, _, rfl⟩ := hd
    exact ⟨fun p => by simp, fun a => by simp⟩
  · rw [if_neg h0, Option.map_eq_some_iff] at hd
    obtain ⟨m, _, rfl⟩ := hd
    exact ⟨fun p => by simp, fun a => by simp⟩
theorem ftsChild_not_chain {index : Fin (2^31)} {coord : Fin 9} {level n : Nat} {d : Coord}
    (hd : ftsChild index coord level n = some d) : NotChain d := by
  unfold ftsChild at hd
  by_cases h0 : level = 0
  · rw [if_pos h0] at hd
    by_cases h1 : n < 128
    · rw [dif_pos h1, Option.some.injEq] at hd; subst hd; exact ⟨fun p => by simp, fun a => by simp⟩
    · rw [dif_neg h1] at hd; cases hd
  · rw [if_neg h0, Option.map_eq_some_iff] at hd
    obtain ⟨m, _, rfl⟩ := hd
    exact ⟨fun p => by simp, fun a => by simp⟩
theorem wctItem_not_chain (a : CanonGraph.WctAddr) (p : Nat) : NotChain (wctItem a p) := by
  unfold wctItem
  split_ifs
  · exact ⟨fun p => by simp, fun a => by simp⟩
  · exact ⟨fun p => by simp, fun a => by simp⟩
theorem ftsItems_not_chain (index : Fin (2^31)) (N : HashOutput) (c : Coord)
    (hc : c ∈ ftsItems index N) : NotChain c := by
  unfold ftsItems wctOpened wctPath at hc
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_append, List.mem_ofFn,
    List.mem_filterMap, List.mem_range] at hc
  obtain ⟨k, hc | ⟨l, _, hl⟩⟩ := hc
  · obtain ⟨t, rfl⟩ := hc
    exact wctItem_not_chain _ _
  · exact ftsChild_not_chain hl
theorem keygen_not_chain (c : Coord) (hc : c ∈ keygenDisclosed) : NotChain c := by
  rcases ClaudeWCT.W9.T3.Security.LargeResidual.mem_keygenDisclosed.mp hc with hc | hc | hc
  · unfold keygenCacheDisclosed at hc
    simp only [List.mem_flatMap, List.mem_filterMap] at hc
    obtain ⟨_, _, _, _, h⟩ := hc
    exact treeChild_not_chain h
  · rcases encodingDisclosed_shape hc with ⟨n, rfl⟩ | ⟨i, rfl⟩
    all_goals exact ⟨fun p => by simp, fun a => by simp⟩
  · obtain ⟨n, rfl⟩ := ClaudeWCT.W9.T3.Security.LargeResidual.topTrialsDisclosed_shape hc
    exact ⟨fun p => by simp, fun a => by simp⟩
theorem layerItems_chain (A : Answers) (index : Fin (2^31)) (c : Coord)
    (hc : c ∈ layerItems (Wots.referenceDigits A) index) :
    (∀ p, c = .inl (.chain p) → p.2.val + 1 = Wots.depth A (wotsAddr p.1)) ∧
      (∀ a, c = .inr (.inl a) → Wots.depth A (wotsAddr a) = 0) := by
  unfold layerItems at hc
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_append] at hc
  obtain ⟨lay, hc | hc⟩ := hc
  · unfold layerChains at hc
    split_ifs at hc with hb
    · simp only [List.mem_map, List.mem_range] at hc
      obtain ⟨i, hi, rfl⟩ := hc
      have hi58 : i < 58 := lt_of_lt_of_le hi (by fin_cases lay <;> decide)
      have hfin : (CanonGraph.fin58 i).val = i := Nat.mod_eq_of_lt hi58
      have hdepth : ∀ a : ChainGraph.Address,
          a = ⟨lay, ⟨(route index.val lay).2, hb.1⟩, ⟨(route index.val lay).1, hb.2⟩, CanonGraph.fin58 i⟩ →
          Wots.depth A (wotsAddr a) = (Wots.referenceDigits A (routeAddr index.val lay)).getD i 0 := by
        intro a ha
        subst ha
        simp only [Wots.depth, wotsAddr, hfin, routeAddr]
      constructor
      · intro p hp
        obtain ⟨h1, hd, h2⟩ := chainItem_chain hp
        rw [hdepth p.1 h1, h2]
        have hle : (Wots.referenceDigits A (routeAddr index.val lay)).getD i 0 ≤ maxDigit lay i :=
          WotsExtract.depth_le A ⟨routeAddr index.val lay, i⟩ hi
        have hw : maxDigit lay i ≤ 7 := by
          unfold maxDigit; split_ifs <;> norm_num
        omega
      · intro a ha
        obtain ⟨h1, hd⟩ := chainItem_seed ha
        rw [hdepth a h1, hd]
    · cases hc
  · unfold layerPath at hc
    split_ifs at hc with hb
    · simp only [List.mem_filterMap, List.mem_range] at hc
      obtain ⟨j, _, hj⟩ := hc
      have := treeChild_not_chain hj
      exact ⟨fun p hp => absurd hp (this.1 p), fun a ha => absurd ha (this.2 a)⟩
    · cases hc
theorem signDisclosed_chain (A : Answers) (published : SigGolfCandidate.T3.Cache) (request : Security.Request)
    (c : Coord) (hc : c ∈ signDisclosed A published request) :
    (∀ p, c = .inl (.chain p) → p.2.val + 1 = Wots.depth A (wotsAddr p.1)) ∧
      (∀ a, c = .inr (.inl a) → Wots.depth A (wotsAddr a) = 0) := by
  unfold signDisclosed at hc
  split_ifs at hc with hcache
  · split at hc
    · split_ifs at hc with hok
      · unfold signItems signItemsWith at hc
        rcases List.mem_append.mp hc with hc | hc
        · have := ftsItems_not_chain _ _ c hc
          exact ⟨fun p hp => absurd hp (this.1 p), fun a ha => absurd ha (this.2 a)⟩
        · exact layerItems_chain A _ c hc
      · cases hc
    · cases hc
  · cases hc
def Disclosed (A : Answers) (published : SigGolfCandidate.T3.Cache) (c : Coord) : Prop :=
  c ∈ keygenDisclosed ∨ ∃ request, c ∈ signDisclosed A published request
theorem frontier_child_unknown (A : Answers) (published : SigGolfCandidate.T3.Cache) (a : ChainGraph.Address)
    (s : Fin 7) (hs : s.val + 1 = Wots.depth A (wotsAddr a)) :
    ¬Known (Disclosed A published) (chainChild (a, s)) := by
  intro hk
  unfold chainChild at hk
  by_cases h0 : s.val = 0
  · rw [if_pos h0] at hk
    rcases known_secret hk with hd | ⟨request, hd⟩
    · exact (keygen_not_chain _ hd).2 a rfl
    · have := (signDisclosed_chain A published request _ hd).2 a rfl
      omega
  · rw [if_neg h0] at hk
    rcases known_chain hk with ⟨t, ht, hd⟩ | hd
    · rcases hd with hd | ⟨request, hd⟩
      · exact (keygen_not_chain _ hd).1 _ rfl
      · have := (signDisclosed_chain A published request _ hd).1 _ rfl
        simp only [ChainGraph.predecessor] at ht this
        omega
    · simp only [ChainGraph.predecessor] at hd
      rcases hd with hd | ⟨request, hd⟩
      · exact (keygen_not_chain _ hd).2 _ rfl
      · have := (signDisclosed_chain A published request _ hd).2 _ rfl
        omega
theorem treeChild_ne_wctItem {lay : Layer} {tree : Fin (2^31)} {level n : Nat} {d : Coord}
    (hd : treeChild lay tree level n = some d) (a : CanonGraph.WctAddr) (p : Nat) : d ≠ wctItem a p := by
  unfold treeChild at hd
  unfold wctItem
  by_cases h0 : level = 0
  · rw [if_pos h0, Option.map_eq_some_iff] at hd
    obtain ⟨L, _, rfl⟩ := hd
    split_ifs <;> simp
  · rw [if_neg h0, Option.map_eq_some_iff] at hd
    obtain ⟨m, _, rfl⟩ := hd
    split_ifs <;> simp
theorem ftsChild_ne_wctItem {index : Fin (2^31)} {coord : Fin 9} {level n : Nat} {d : Coord}
    (hd : ftsChild index coord level n = some d) (a : CanonGraph.WctAddr) (p : Nat) : d ≠ wctItem a p := by
  unfold ftsChild at hd
  unfold wctItem
  by_cases h0 : level = 0
  · rw [if_pos h0] at hd
    by_cases h1 : n < 128
    · rw [dif_pos h1, Option.some.injEq] at hd; subst hd; split_ifs <;> simp
    · rw [dif_neg h1] at hd; cases hd
  · rw [if_neg h0, Option.map_eq_some_iff] at hd
    obtain ⟨m, _, rfl⟩ := hd
    split_ifs <;> simp
theorem keygen_not_wct (a : CanonGraph.WctAddr) (p : Nat) : wctItem a p ∉ keygenDisclosed := by
  intro hc
  rcases ClaudeWCT.W9.T3.Security.LargeResidual.mem_keygenDisclosed.mp hc with hc | hc | hc
  · unfold keygenCacheDisclosed at hc
    simp only [List.mem_flatMap, List.mem_filterMap] at hc
    obtain ⟨_, _, _, _, h⟩ := hc
    exact treeChild_ne_wctItem h a p rfl
  · rcases encodingDisclosed_shape hc with ⟨n, h⟩ | ⟨i, h⟩
    all_goals unfold wctItem at h; split_ifs at h <;> simp at h
  · obtain ⟨n, h⟩ := ClaudeWCT.W9.T3.Security.LargeResidual.topTrialsDisclosed_shape hc
    unfold wctItem at h; split_ifs at h <;> simp at h
theorem layerItems_not_wct (digitsOf : Wots.LeafAddr → List Nat) (index : Fin (2^31)) (a : CanonGraph.WctAddr)
    (p : Nat) : wctItem a p ∉ layerItems digitsOf index := by
  intro hc
  unfold layerItems at hc
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_append] at hc
  obtain ⟨lay, hc | hc⟩ := hc
  · unfold layerChains at hc
    split_ifs at hc
    · simp only [List.mem_map, List.mem_range] at hc
      obtain ⟨i, -, hi⟩ := hc
      unfold chainItem wctItem at hi
      split_ifs at hi <;> simp at hi
    · cases hc
  · unfold layerPath at hc
    split_ifs at hc
    · simp only [List.mem_filterMap, List.mem_range] at hc
      obtain ⟨j, _, hj⟩ := hc
      exact treeChild_ne_wctItem hj a p rfl
    · cases hc
theorem wctItem_mem_signItemsWith (digitsOf : Wots.LeafAddr → List Nat) (N : HashOutput) (a : CanonGraph.WctAddr)
    (p : Nat) (hp : p ≤ 4) (h : wctItem a p ∈ signItemsWith digitsOf N) :
    a.1 = digestIndex N ∧ a.2.2.1 = WCT9.child N a.2.1 ∧ p = 4 - WCT9.wordDigit (WCT9.rank N a.2.1) a.2.2.2 := by
  unfold signItemsWith at h
  rcases List.mem_append.mp h with h | h
  · unfold ftsItems wctOpened wctPath at h
    simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_append, List.mem_ofFn,
      List.mem_filterMap, List.mem_range] at h
    obtain ⟨k, ⟨t, ht⟩ | ⟨l, _, hl⟩⟩ := h
    · have hle : 4 - WCT9.wordDigit (WCT9.rank N k) t ≤ 4 := Nat.sub_le _ _
      obtain ⟨hab, hpq⟩ := wctItem_injective hle hp ht
      subst hab
      exact ⟨rfl, rfl, hpq.symm⟩
    · exact (ftsChild_ne_wctItem hl a p rfl).elim
  · exact (layerItems_not_wct digitsOf _ a p h).elim
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers leafSeed)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (listBlock slotValue routeAddr IsDigestRow)
open SigGolfCandidate.T3.Security.LargeCoupling (wotsAddr gAddr wotsAddr_gAddr chainCount_le58 chainRow_block4
  slotValue_chainRow slotValue_block4_three honestChainValue_zero')
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def AllClear (A : Answers) (K : Coord → Prop) (qs : List Spec.Domain) : Prop :=
  ∀ X, (.inl (.inr X) : Spec.Domain) ∈ qs → Clear A K X (A (.inl (.inr X)))
/-- Pairing stage 1: the value slot of a chain row (block 0 for a G chain, block 3 for an F chain). -/
def vslot (lay : Layer) (i : Nat) : Nat := if WCT9.isG lay i then 0 else 3
theorem slotValue_chainRowW (a : Wots.ChainAddr) (s : Nat) (v : Digest) :
    slotValue (Wots.chainRowW a s v) (vslot a.key.lay a.chain) = v := by
  unfold vslot
  cases hG : WCT9.isG a.key.lay a.chain
  · rw [Wots.chainRowW_eq, WCT9.chainInputW_F hG]
    exact slotValue_chainRow a s v
  · rw [Wots.chainRowW_eq, WCT9.chainInputW_G hG, if_pos rfl]
    unfold slotValue
    simp only [Nat.mul_zero, List.drop_zero, List.append_assoc]
    rw [List.take_append_of_le_length (by rw [bytesLE_length])]
    rw [List.take_of_length_le (by rw [bytesLE_length])]
    exact Correctness.readDigest_bytesLE v
theorem posOf_chainRow (a : Wots.ChainAddr) (ha : WotsExtract.SourceChain a) (s : Nat) (hs : s < 7) (v : Digest) :
    Extract.posOf (Wots.chainRowW a s v) = some (CanonGraph.Node.chain (gAddr a ha, ⟨s, hs⟩)).toPos := by
  apply Extract.posOf_eq (CanonGraph.toPos_bounded _)
  · unfold Wots.chainRowW
    show _ = 64
    simp [WCT9.chainInputW_length]
  · unfold Wots.chainRowW
    exact WCT9.chainInputW_header _ _ _ _ _ _
theorem honestInput_chainNode (A : Answers) (p : ChainGraph.Point) :
    Extract.honestInput A (CanonGraph.Node.chain p).toPos =
      Wots.chainRowW (wotsAddr p.1) p.2.val (Wots.honestChainValueW A p.1.layer p.1.tree.val p.1.leaf.val
        p.1.chain.val (WCT9.wotsSeed A p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val) p.2.val) := by
  show pad64 _ = _
  rw [WCT9.chainInputW_padded]
  rfl
theorem honestValue_chainNode (A : Answers) (p : ChainGraph.Point) :
    honestValue A (.inl (.chain p)) = Wots.honestChainValueW A p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val
        (WCT9.wotsSeed A p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val) (p.2.val + 1) := by
  rw [← Wots.honestChainValueW_succ]
  rfl
theorem honestValue_chainChild (A : Answers) (p : ChainGraph.Point) :
    honestValue A (chainChild p) = Wots.honestChainValueW A p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val
        (WCT9.wotsSeed A p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val) p.2.val := by
  unfold chainChild
  by_cases h0 : p.2.val = 0
  · rw [if_pos h0, h0, Wots.honestChainValueW_zero]
    exact CanonGraph.seedsOf_secretsOf A p.1
  · rw [if_neg h0, honestValue_chainNode]
    simp only [ChainGraph.predecessor]
    congr 1
    omega
theorem childSlots_chain (p : ChainGraph.Point) :
    childSlots (.chain p) = [(chainChild p, vslot p.1.layer p.1.chain.val)] := rfl
theorem contactAt_false (A : Answers) (published : SigGolfCandidate.T3.Cache) (qs : List Spec.Domain)
    (a : Wots.ChainAddr) (ha : WotsExtract.SourceChain a) (hc : Wots.ContactAt A (Wots.entriesOf A qs) a)
    (hclear : AllClear A (Known (Disclosed A published)) qs) : False := by
  obtain ⟨hd, value, answer, hmem, hlow⟩ := hc
  obtain ⟨hq, hans⟩ := WotsExtract.mem_entriesOf_iff.mp hmem
  have hd7 : Wots.depth A a ≤ 7 := by
    have := WotsExtract.depth_le A a ha.2
    have hw : maxDigit a.key.lay a.chain ≤ 7 := by unfold maxDigit; split_ifs <;> norm_num
    omega
  set s := Wots.depth A a - 1 with hsdef
  have hs7 : s < 7 := by omega
  let p : ChainGraph.Point := (gAddr a ha, ⟨s, hs7⟩)
  have hpos := posOf_chainRow a ha s hs7 value
  obtain ⟨hhit, hsingle, -⟩ := hclear _ hq
  have hcv : honestValue A (chainChild p) = Wots.honestChainValueW A a.key.lay a.key.tree a.key.leaf a.chain
      (WCT9.wotsSeed A a.key.lay a.key.tree a.key.leaf a.chain) s := honestValue_chainChild A p
  by_cases hv : value = honestValue A (chainChild p)
  · have hk := hsingle (.chain p) hpos (chainChild p) (vslot p.1.layer p.1.chain.val) (childSlots_chain p)
      (by rw [show vslot p.1.layer p.1.chain.val = vslot a.key.lay a.chain from rfl, slotValue_chainRowW]; exact hv)
    exact frontier_child_unknown A published (gAddr a ha) ⟨s, hs7⟩ (by
      change s + 1 = Wots.depth A (wotsAddr (gAddr a ha))
      rw [wotsAddr_gAddr]; omega) hk
  · apply hhit (.chain p) hpos
    refine ⟨fun heq => hv ?_, ?_⟩
    · have := congrArg (fun X => slotValue X (vslot a.key.lay a.chain)) heq
      simp only [slotValue_chainRowW] at this
      rw [this, honestInput_chainNode]
      erw [slotValue_chainRowW]
      rw [hcv]
      rfl
    · rw [hans]
      change Wots.rowHalf a s answer = _
      rw [hlow, honestValue_chainNode]
      unfold Wots.frontierValue
      congr 1
      change Wots.depth A a = s + 1
      omega
theorem structuralHitSrc_false (A : Answers) (K : Coord → Prop) (qs : List Spec.Domain)
    (h : WotsExtract.StructuralHitSrc A (Wots.entriesOf A qs)) (hclear : AllClear A K qs) : False := by
  obtain ⟨position, input, answer, hmem, hpos, hb, hsrc, -, hne, hlow⟩ := h
  obtain ⟨hq, hans⟩ := WotsExtract.mem_entriesOf_iff.mp hmem
  have hsp : CanonGraph.SourcePos position := by
    cases position with
    | chain lay tree leaf i step =>
        obtain ⟨h1, h2, h3, h4⟩ := hsrc
        refine ⟨Extract.tree_lt_of_treeBits h1, lt_of_lt_of_le h2 ?_, lt_of_lt_of_le h3 (chainCount_le58 lay), ?_⟩
        · calc 2 ^ height lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (SigGolfCandidate.T3M.Extract.height_le _)
            _ = 4096 := by norm_num
        · have hw : 2 ^ width lay i ≤ 8 := by unfold width; norm_num
          omega
    | leaf lay tree leaf => exact hsrc
    | node lay tree level nd => exact hsrc
    | forest index => exact hsrc
    | wctChain index coord child t step => exact hsrc
    | wctLeaf index coord child => exact hsrc
    | wctNode index coord level nd => exact hsrc
  obtain ⟨N, rfl⟩ := CanonGraph.exists_toPos hsp
  exact (hclear _ hq).1 N hpos ⟨hne, hlow⟩
theorem encodingMatch_route_false (A : Answers) (K : Coord → Prop) (qs : List Spec.Domain) (index : Nat)
    (hidx : index < 2 ^ 31) (lay : Layer)
    (h : Wots.EncodingMatchAt A (Wots.entriesOf A qs) (WotsExtract.routeLeaf index lay))
    (hclear : AllClear A K qs) : False := by
  obtain ⟨m, ctr, pad, answer, hfit, hmem, hne, hdec⟩ := h
  obtain ⟨hq, hans⟩ := WotsExtract.mem_entriesOf_iff.mp hmem
  obtain ⟨L, hL⟩ := CanonEncoding.route_source index hidx lay
  have hL' : L.toWots = WotsExtract.routeLeaf index lay := hL
  have hlay : L.1.lay = lay := congrArg Wots.LeafAddr.lay hL'
  refine (hclear _ hq).2.2 L m ctr pad (by rw [hlay]; exact hfit) (by rw [hL']) ⟨?_, ?_⟩
  · rw [hL']; exact hne
  · rw [hans, hL', hlay]; exact hdec
theorem wotsPrimitiveRoute_false (A : Answers) (published : SigGolfCandidate.T3.Cache) (qs : List Spec.Domain)
    (index : Nat) (hidx : index < 2 ^ 31) (h : WotsExtract.WotsPrimitiveRoute index A (Wots.entriesOf A qs))
    (hclear : AllClear A (Known (Disclosed A published)) qs) : False := by
  rcases h with ⟨lay, h⟩ | h | ⟨a, ha, h⟩ | ⟨a, b, ha, -, -, h, -⟩ | ⟨a, ha, -, h⟩
  · exact encodingMatch_route_false A _ qs index hidx lay h hclear
  · exact structuralHitSrc_false A _ qs h hclear
  · obtain ⟨hd, start, middle, -, hrow⟩ := h
    exact contactAt_false A published qs a ha ⟨by omega, middle, hrow⟩ hclear
  · exact contactAt_false A published qs a ha h hclear
  · exact contactAt_false A published qs a ha h hclear
theorem posOf_honest_wctChain (A : Answers) (a : CanonGraph.WctAddr) (s : Fin 4) :
    Extract.posOf (Extract.honestInput A (CanonGraph.Node.wctChain (a, s)).toPos) =
      some (CanonGraph.Node.wctChain (a, s)).toPos :=
  Extract.posOf_eq (CanonGraph.toPos_bounded _) (Extract.honestInput_length A _) (Extract.hdrBlock_honestInput A _)
theorem honestValue_wctItem (A : Answers) (a : CanonGraph.WctAddr) (p : Nat) (hp : p ≤ 4) :
    honestValue A (wctItem a p) = Extract.wctValue A a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val p := by
  by_cases h0 : p = 0
  · subst h0
    rw [wctItem_zero]
    change CanonGraph.wctSeedsOf (CanonGraph.secretsOf A) a = _
    rw [← CanonGraph.wctSeed_secrets]
    simp [Extract.wctValue, WCT9.chain]
  · rw [wctItem_pos a p h0 hp]
    obtain ⟨s, rfl⟩ : ∃ s, p = s + 1 := ⟨p - 1, by omega⟩
    rw [← WctExtract.wctValue_succ]
    simp only [honestValue, CanonGraph.Node.toPos, Nat.add_sub_cancel, WctExtract.honestInput_wctChain]
    cases hh : WCT9.ftsChainHigh a.2.2.2.val s <;>
      simp [Extract.Pos.proj, Extract.Paired.proj, Extract.Pos.high, hh, Extract.eval_halfHash,
        WCT9.ftsChainInputW_padded, WCT9.halfOf] <;>
      simp only [Extract.honestInput, WCT9.ftsChainInputW_padded] <;> rfl
theorem slotValue_honest_wctChain (A : Answers) (a : CanonGraph.WctAddr) (s : Fin 4) :
    slotValue (Extract.honestInput A (CanonGraph.Node.wctChain (a, s)).toPos)
      (if WCT9.ftsIsG a.2.2.2.val then 0 else 3) = honestValue A (wctItem a s.val) := by
  rw [honestValue_wctItem A a s.val (by omega)]
  have hb : ∀ (x : Digest) (h : BitVec 128),
      SphincsSecurity.bytesLE 16 x ++ SphincsSecurity.bytesLE 16 h ++ zero16 ++ zero16 = block4 x h 0 0 := by
    intro x h; simp only [block4, show zero16 = SphincsSecurity.bytesLE 16 (0 : Digest) by decide]
  cases hG : WCT9.ftsIsG a.2.2.2.val
  · simp only [Bool.false_eq_true, if_false]
    change slotValue (Extract.honestInput A (.wctChain a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val s.val)) 3 = _
    rw [WctExtract.honestInput_wctChain, WCT9.ftsChainInputW_F hG, WctExtract.wctChainInput_block4']
    exact slotValue_block4_three _ _ _ _
  · simp only [if_true]
    change slotValue (Extract.honestInput A (.wctChain a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val s.val)) 0 = _
    rw [WctExtract.honestInput_wctChain, WCT9.ftsChainInputW_G hG, hb]
    unfold block4
    rw [List.append_assoc, List.append_assoc]
    unfold slotValue
    simp only [Nat.mul_zero, List.drop_zero]
    rw [List.take_append_of_le_length (by rw [SphincsSecurity.bytesLE_length])]
    rw [List.take_of_length_le (by rw [SphincsSecurity.bytesLE_length])]
    exact Correctness.readDigest_bytesLE _
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.LargeCoupling (record_inputs)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem trace_inputs (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) (result : PaddedGame.TraceResult)
    (hr : result ∈ (PaddedGame.tracedExperiment adversary q hq).support) :
    ∀ e ∈ (QueryRecorded.recordedTrace result).events, ∀ x, e.input = .inl (.inr x) →
      x ∈ Wots.referenceInputs adversary :=
  record_inputs _ _ (∅, ∅) (Wots.Ref.referenceInputs_inputsIn adversary) _
    (PaddedExtraction.traced_record_support adversary q hq result hr)
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M (wrho wdc)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeCoupling (record_events_known chargeOf EventsAgree)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
end ClaudeWCT.W9.T3.Security.LargeCoupling
end

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (routeAddr)
open SigGolfCandidate.T3.Security.LargeCoupling (wotsAddr)
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _
theorem known_secret {D : Coord → Prop} {s : SeedIndex} (h : LargeResidual.Paired.Known D (.inr s)) : D (.inr s) := by
  cases h with
  | base h => exact h
theorem known_chain_aux {D : Coord → Prop} {c : Coord} (h : LargeResidual.Paired.Known D c) :
    ∀ p : ChainGraph.Point, c = .inl (.chain p) →
      (∃ s : Fin 7, s.val ≤ p.2.val ∧ D (.inl (.chain (p.1, s)))) ∨ D (.inr (.inl p.1)) := by
  induction h with
  | base hc =>
      intro p hp
      subst hp
      exact Or.inl ⟨p.2, le_rfl, hc⟩
  | @node N hall ih =>
      intro p hp
      simp only [Sum.inl.injEq] at hp
      subst hp
      have hmem : (chainChild p, vslot p.1.layer p.1.chain.val) ∈ LargeResidual.Paired.childSlots (.chain p) := by simp [vslot,LargeResidual.Paired.childSlots,LargeResidual.childSlots]
      have hk := hall _ hmem
      have hih := ih _ hmem
      unfold chainChild at hk hih
      by_cases h0 : p.2.val = 0
      · rw [if_pos h0] at hk
        exact Or.inr (known_secret hk)
      · rw [if_neg h0] at hih
        rcases hih (ChainGraph.predecessor p) rfl with ⟨s, hs, hd⟩ | hd
        · refine Or.inl ⟨s, ?_, hd⟩
          simp only [ChainGraph.predecessor] at hs
          omega
        · exact Or.inr hd
theorem known_chain {D : Coord → Prop} {p : ChainGraph.Point} (h : LargeResidual.Paired.Known D (.inl (.chain p))) :
    (∃ s : Fin 7, s.val ≤ p.2.val ∧ D (.inl (.chain (p.1, s)))) ∨ D (.inr (.inl p.1)) :=
  known_chain_aux h p rfl
theorem wctItem_zero (a : CanonGraph.WctAddr) : wctItem a 0 = .inr (.inr a) := rfl
theorem wctItem_succ (a : CanonGraph.WctAddr) (s : Fin 4) :
    wctItem a (s.val + 1) = .inl (.wctChain (a, s)) := by
  have h : (⟨(s.val + 1 - 1) % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4) = s :=
    Fin.ext (by rw [Nat.add_sub_cancel]; exact Nat.mod_eq_of_lt s.isLt)
  unfold wctItem
  rw [if_neg (Nat.succ_ne_zero _), h]
theorem wctItem_pos (a : CanonGraph.WctAddr) (p : Nat) (h0 : p ≠ 0) (hp : p ≤ 4) :
    wctItem a p = .inl (.wctChain (a, ⟨p - 1, by omega⟩)) := by
  have h : (⟨(p - 1) % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4) = ⟨p - 1, by omega⟩ :=
    Fin.ext (Nat.mod_eq_of_lt (by omega))
  unfold wctItem
  rw [if_neg h0, h]
theorem known_wct_aux {D : Coord → Prop} {c : Coord} (h : LargeResidual.Paired.Known D c) :
    ∀ (a : CanonGraph.WctAddr) (s : Fin 4), c = .inl (.wctChain (a, s)) →
      ∃ p' ≤ s.val + 1, D (wctItem a p') := by
  induction h with
  | base hc =>
      intro a s hs
      subst hs
      exact ⟨s.val + 1, le_rfl, by rw [wctItem_succ]; exact hc⟩
  | @node N hall ih =>
      intro a s hN
      simp only [Sum.inl.injEq] at hN
      subst hN
      have hmem : (wctItem a s.val, if WCT9.ftsIsG a.2.2.2.val then 0 else 3) ∈
          LargeResidual.Paired.childSlots (.wctChain (a, s)) := by
        simp [LargeResidual.Paired.childSlots,LargeResidual.childSlots]
      have hk := hall _ hmem
      have hih := ih _ hmem
      by_cases h0 : s.val = 0
      · rw [h0, wctItem_zero] at hk
        refine ⟨0, Nat.zero_le _, ?_⟩
        rw [wctItem_zero]
        exact known_secret hk
      · have hs1 : s.val - 1 < 4 := by omega
        have he := wctItem_pos a s.val h0 (by omega)
        obtain ⟨p', hp', hd⟩ := hih a ⟨s.val - 1, hs1⟩ he
        exact ⟨p', by simp only at hp'; omega, hd⟩
theorem known_wctItem {D : Coord → Prop} {a : CanonGraph.WctAddr} {p : Nat} (hp : p ≤ 4)
    (h : LargeResidual.Paired.Known D (wctItem a p)) : ∃ p' ≤ p, D (wctItem a p') := by
  by_cases h0 : p = 0
  · subst h0
    rw [wctItem_zero] at h
    exact ⟨0, le_rfl, by rw [wctItem_zero]; exact known_secret h⟩
  · have hs : p - 1 < 4 := by omega
    have he := wctItem_pos a p h0 hp
    rw [he] at h
    obtain ⟨p', hp', hd⟩ := known_wct_aux h a ⟨p - 1, hs⟩ rfl
    exact ⟨p', by simp only at hp'; omega, hd⟩
theorem wctItem_injective {a b : CanonGraph.WctAddr} {p q : Nat} (hp : p ≤ 4) (hq : q ≤ 4)
    (h : wctItem a p = wctItem b q) : a = b ∧ p = q := by
  unfold wctItem at h
  by_cases hp0 : p = 0 <;> by_cases hq0 : q = 0
  · rw [if_pos hp0, if_pos hq0] at h
    simp only [Sum.inr.injEq] at h
    exact ⟨h, by omega⟩
  · rw [if_pos hp0, if_neg hq0] at h; cases h
  · rw [if_neg hp0, if_pos hq0] at h; cases h
  · rw [if_neg hp0, if_neg hq0] at h
    simp only [Sum.inl.injEq, CanonGraph.Node.wctChain.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have h3 := congrArg Fin.val h2
    simp only at h3
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h3
    exact ⟨h1, by omega⟩
theorem chainItem_chain {L : CanonGraph.LeafPos} {i d : Nat} {p : ChainGraph.Point}
    (h : chainItem L i d = .inl (.chain p)) :
    p.1 = ⟨L.lay, L.tree, L.leaf, CanonGraph.fin58 i⟩ ∧ d ≠ 0 ∧ p.2.val = (d - 1) % 7 := by
  unfold chainItem at h
  by_cases hd : d = 0
  · rw [if_pos hd] at h
    cases h
  · rw [if_neg hd] at h
    simp only [Sum.inl.injEq, CanonGraph.Node.chain.injEq] at h
    subst h
    exact ⟨rfl, hd, rfl⟩
theorem chainItem_seed {L : CanonGraph.LeafPos} {i d : Nat} {a : ChainGraph.Address}
    (h : chainItem L i d = .inr (.inl a)) :
    a = ⟨L.lay, L.tree, L.leaf, CanonGraph.fin58 i⟩ ∧ d = 0 := by
  unfold chainItem at h
  by_cases hd : d = 0
  · rw [if_pos hd] at h
    simp only [Sum.inr.injEq, Sum.inl.injEq] at h
    exact ⟨h.symm, hd⟩
  · rw [if_neg hd] at h
    cases h
def NotChain (c : Coord) : Prop := (∀ p, c ≠ .inl (.chain p)) ∧ (∀ a, c ≠ .inr (.inl a))
theorem treeChild_not_chain {lay : Layer} {tree : Fin (2^31)} {level n : Nat} {d : Coord}
    (hd : treeChild lay tree level n = some d) : NotChain d := by
  unfold treeChild at hd
  by_cases h0 : level = 0
  · rw [if_pos h0, Option.map_eq_some_iff] at hd
    obtain ⟨L, _, rfl⟩ := hd
    exact ⟨fun p => by simp, fun a => by simp⟩
  · rw [if_neg h0, Option.map_eq_some_iff] at hd
    obtain ⟨m, _, rfl⟩ := hd
    exact ⟨fun p => by simp, fun a => by simp⟩
theorem ftsChild_not_chain {index : Fin (2^31)} {coord : Fin 9} {level n : Nat} {d : Coord}
    (hd : LargeResidual.Paired.ftsChild index coord level n = some d) : NotChain d := by
  unfold LargeResidual.Paired.ftsChild at hd
  by_cases h0 : level = 0
  · rw [if_pos h0] at hd
    by_cases h1 : CanonGraph.Paired.rawLeaf coord.val n < 128
    · rw [dif_pos h1, Option.some.injEq] at hd; subst hd; exact ⟨fun p => by simp, fun a => by simp⟩
    · rw [dif_neg h1] at hd; cases hd
  · rw [if_neg h0, Option.map_eq_some_iff] at hd
    obtain ⟨m, _, rfl⟩ := hd
    exact ⟨fun p => by simp, fun a => by simp⟩
theorem wctItem_not_chain (a : CanonGraph.WctAddr) (p : Nat) : NotChain (wctItem a p) := by
  unfold wctItem
  split_ifs
  · exact ⟨fun p => by simp, fun a => by simp⟩
  · exact ⟨fun p => by simp, fun a => by simp⟩
theorem ftsItems_not_chain (index : Fin (2^31)) (N : HashOutput) (c : Coord)
    (hc : c ∈ LargeResidual.Paired.ftsItems index N) : NotChain c := by
  unfold LargeResidual.Paired.ftsItems LargeResidual.Paired.wctOpened LargeResidual.Paired.wctPath at hc
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_append, List.mem_ofFn,
    List.mem_filterMap, List.mem_range] at hc
  obtain ⟨k, hc | ⟨l, _, hl⟩⟩ := hc
  · obtain ⟨t, rfl⟩ := hc
    exact wctItem_not_chain _ _
  · exact ftsChild_not_chain hl
theorem keygen_not_chain (c : Coord) (hc : c ∈ keygenDisclosed) : NotChain c := by
  rcases ClaudeWCT.W9.T3.Security.LargeResidual.mem_keygenDisclosed.mp hc with hc | hc | hc
  · unfold keygenCacheDisclosed at hc
    simp only [List.mem_flatMap, List.mem_filterMap] at hc
    obtain ⟨_, _, _, _, h⟩ := hc
    exact treeChild_not_chain h
  · rcases encodingDisclosed_shape hc with ⟨n, rfl⟩ | ⟨i, rfl⟩
    all_goals exact ⟨fun p => by simp, fun a => by simp⟩
  · obtain ⟨n, rfl⟩ := ClaudeWCT.W9.T3.Security.LargeResidual.topTrialsDisclosed_shape hc
    exact ⟨fun p => by simp, fun a => by simp⟩
theorem layerItems_chain (A : Answers) (index : Fin (2^31)) (c : Coord)
    (hc : c ∈ layerItems (Wots.CanonicalRef.referenceDigits A (Wots.CanonicalRef.sourceMessages A)) index) :
    (∀ p, c = .inl (.chain p) → p.2.val + 1 = Wots.CanonicalRef.depth A (Wots.CanonicalRef.sourceMessages A) (wotsAddr p.1)) ∧
      (∀ a, c = .inr (.inl a) → Wots.CanonicalRef.depth A (Wots.CanonicalRef.sourceMessages A) (wotsAddr a) = 0) := by
  unfold layerItems at hc
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_append] at hc
  obtain ⟨lay, hc | hc⟩ := hc
  · unfold layerChains at hc
    split_ifs at hc with hb
    · simp only [List.mem_map, List.mem_range] at hc
      obtain ⟨i, hi, rfl⟩ := hc
      have hi58 : i < 58 := lt_of_lt_of_le hi (by fin_cases lay <;> decide)
      have hfin : (CanonGraph.fin58 i).val = i := Nat.mod_eq_of_lt hi58
      have hdepth : ∀ a : ChainGraph.Address,
          a = ⟨lay, ⟨(route index.val lay).2, hb.1⟩, ⟨(route index.val lay).1, hb.2⟩, CanonGraph.fin58 i⟩ →
          Wots.CanonicalRef.depth A (Wots.CanonicalRef.sourceMessages A) (wotsAddr a) = (Wots.CanonicalRef.referenceDigits A (Wots.CanonicalRef.sourceMessages A) (routeAddr index.val lay)).getD i 0 := by
        intro a ha
        subst ha
        simp only [Wots.CanonicalRef.depth, wotsAddr, hfin, routeAddr]
      constructor
      · intro p hp
        obtain ⟨h1, hd, h2⟩ := chainItem_chain hp
        rw [hdepth p.1 h1, h2]
        have hle : (Wots.CanonicalRef.referenceDigits A (Wots.CanonicalRef.sourceMessages A) (routeAddr index.val lay)).getD i 0 ≤ maxDigit lay i :=
          Wots.CanonicalRef.depth_le A (Wots.CanonicalRef.sourceMessages A) ⟨routeAddr index.val lay, i⟩ hi
        have hw : maxDigit lay i ≤ 7 := by
          unfold maxDigit; split_ifs <;> norm_num
        omega
      · intro a ha
        obtain ⟨h1, hd⟩ := chainItem_seed ha
        rw [hdepth a h1, hd]
    · cases hc
  · unfold layerPath at hc
    split_ifs at hc with hb
    · simp only [List.mem_filterMap, List.mem_range] at hc
      obtain ⟨j, _, hj⟩ := hc
      have := treeChild_not_chain hj
      exact ⟨fun p hp => absurd hp (this.1 p), fun a ha => absurd ha (this.2 a)⟩
    · cases hc
theorem signDisclosed_chain (A : Answers) (published : SigGolfCandidate.T3.Cache) (request : Security.Request)
    (c : Coord) (hc : c ∈ LargeResidual.Paired.signDisclosed A published request) :
    (∀ p, c = .inl (.chain p) → p.2.val + 1 = Wots.CanonicalRef.depth A (Wots.CanonicalRef.sourceMessages A) (wotsAddr p.1)) ∧
      (∀ a, c = .inr (.inl a) → Wots.CanonicalRef.depth A (Wots.CanonicalRef.sourceMessages A) (wotsAddr a) = 0) := by
  unfold LargeResidual.Paired.signDisclosed at hc
  split_ifs at hc with hcache
  · split at hc
    · split_ifs at hc with hok
      · unfold LargeResidual.Paired.signItems at hc
        rcases List.mem_append.mp hc with hc | hc
        · have := ftsItems_not_chain _ _ c hc
          exact ⟨fun p hp => absurd hp (this.1 p), fun a ha => absurd ha (this.2 a)⟩
        · exact layerItems_chain A _ c hc
      · cases hc
    · cases hc
  · cases hc
def Disclosed (A : Answers) (published : SigGolfCandidate.T3.Cache) (c : Coord) : Prop :=
  c ∈ keygenDisclosed ∨ ∃ request, c ∈ LargeResidual.Paired.signDisclosed A published request
theorem frontier_child_unknown (A : Answers) (published : SigGolfCandidate.T3.Cache) (a : ChainGraph.Address)
    (s : Fin 7) (hs : s.val + 1 = Wots.CanonicalRef.depth A (Wots.CanonicalRef.sourceMessages A) (wotsAddr a)) :
    ¬LargeResidual.Paired.Known (Disclosed A published) (chainChild (a, s)) := by
  intro hk
  unfold chainChild at hk
  by_cases h0 : s.val = 0
  · rw [if_pos h0] at hk
    rcases known_secret hk with hd | ⟨request, hd⟩
    · exact (keygen_not_chain _ hd).2 a rfl
    · have := (signDisclosed_chain A published request _ hd).2 a rfl
      omega
  · rw [if_neg h0] at hk
    rcases known_chain hk with ⟨t, ht, hd⟩ | hd
    · rcases hd with hd | ⟨request, hd⟩
      · exact (keygen_not_chain _ hd).1 _ rfl
      · have := (signDisclosed_chain A published request _ hd).1 _ rfl
        simp only [ChainGraph.predecessor] at ht this
        omega
    · simp only [ChainGraph.predecessor] at hd
      rcases hd with hd | ⟨request, hd⟩
      · exact (keygen_not_chain _ hd).2 _ rfl
      · have := (signDisclosed_chain A published request _ hd).2 _ rfl
        omega

end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityExtraction SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers leafSeed)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (listBlock slotValue routeAddr IsDigestRow)
open SigGolfCandidate.T3.Security.LargeCoupling (wotsAddr gAddr wotsAddr_gAddr chainCount_le58 chainRow_block4
  slotValue_chainRow slotValue_block4_three honestChainValue_zero')
open ClaudeWCT.W9.T3.Security.WotsExtract (SourceChain7.source)
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def AllClear (A : Answers) (K : Coord → Prop) (qs : List Spec.Domain) : Prop :=
  ∀ X, (.inl (.inr X) : Spec.Domain) ∈ qs → LargeResidual.Paired.Clear A K X (A (.inl (.inr X)))
theorem posOf_chainRow (a : Wots.ChainAddr) (ha : WotsExtract.SourceChain a) (s : Nat) (hs : s < 7) (v : Digest) :
    Extract.posOf (Wots.chainRowW a s v) = some (CanonGraph.Node.chain (gAddr a ha, ⟨s, hs⟩)).toPos := by
  apply Extract.posOf_eq (CanonGraph.toPos_bounded _)
  · unfold Wots.chainRowW
    show _ = 64
    simp [WCT9.chainInputW_length]
  · unfold Wots.chainRowW
    exact WCT9.chainInputW_header _ _ _ _ _ _
theorem honestInput_chainNode (A : Answers) (p : ChainGraph.Point) :
    Extract.Paired.honestInput A (CanonGraph.Node.chain p).toPos =
      Wots.chainRowW (wotsAddr p.1) p.2.val (Wots.honestChainValueW A p.1.layer p.1.tree.val p.1.leaf.val
        p.1.chain.val (WCT9.wotsSeed A p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val) p.2.val) := by
  show pad64 _ = _
  rw [WCT9.chainInputW_padded]
  rfl
theorem honestValue_chainNode (A : Answers) (p : ChainGraph.Point) :
    LargeResidual.Paired.honestValue A (.inl (.chain p)) = Wots.honestChainValueW A p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val
        (WCT9.wotsSeed A p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val) (p.2.val + 1) := by
  -- C3 (#866): the chain value after a step is the half `chainHigh` of the step's output.
  rw [← Wots.honestChainValueW_succ]
  show Extract.Paired.proj (CanonGraph.Node.chain p).toPos _ = _
  rw [CanonGraph.Paired.pairedProj_chain]
  rfl
theorem honestValue_chainChild (A : Answers) (p : ChainGraph.Point) :
    LargeResidual.Paired.honestValue A (chainChild p) = Wots.honestChainValueW A p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val
        (WCT9.wotsSeed A p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val) p.2.val := by
  unfold chainChild
  by_cases h0 : p.2.val = 0
  · rw [if_pos h0, h0, Wots.honestChainValueW_zero]
    exact CanonGraph.seedsOf_secretsOf A p.1
  · rw [if_neg h0, honestValue_chainNode]
    simp only [ChainGraph.predecessor]
    congr 1
    omega
theorem childSlots_chain (p : ChainGraph.Point) :
    LargeResidual.Paired.childSlots (.chain p) = [(chainChild p, vslot p.1.layer p.1.chain.val)] := rfl
theorem contactAt_false (A : Answers) (published : SigGolfCandidate.T3.Cache) (qs : List Spec.Domain)
    (a : Wots.ChainAddr) (ha : WotsExtract.SourceChain7 a) (hc : Wots.CanonicalRef.ContactAt A (Wots.CanonicalRef.sourceMessages A) (Wots.entriesOf A qs) a)
    (hclear : AllClear A (LargeResidual.Paired.Known (Disclosed A published)) qs) : False := by
  obtain ⟨hd, value, answer, hmem, hlow⟩ := hc
  obtain ⟨hq, hans⟩ := WotsExtract.mem_entriesOf_iff.mp hmem
  have hd7 : Wots.CanonicalRef.depth A (Wots.CanonicalRef.sourceMessages A) a ≤ 7 := by
    have := Wots.CanonicalRef.depth_le A (Wots.CanonicalRef.sourceMessages A) a ha.2
    have hw : maxDigit a.key.lay a.chain ≤ 7 := by unfold maxDigit; split_ifs <;> norm_num
    omega
  set s := Wots.CanonicalRef.depth A (Wots.CanonicalRef.sourceMessages A) a - 1 with hsdef
  have hs7 : s < 7 := by omega
  let p : ChainGraph.Point := (gAddr a ha.source, ⟨s, hs7⟩)
  have hpos := posOf_chainRow a ha.source s hs7 value
  obtain ⟨hhit, hsingle, -⟩ := hclear _ hq
  have hb : Extract.Paired.Bounded (CanonGraph.Node.chain p).toPos := by
    change (CanonGraph.Node.chain p).toPos.Bounded
    exact CanonGraph.toPos_bounded _
  have hcv : LargeResidual.Paired.honestValue A (chainChild p) = Wots.honestChainValueW A a.key.lay a.key.tree a.key.leaf a.chain
      (WCT9.wotsSeed A a.key.lay a.key.tree a.key.leaf a.chain) s := honestValue_chainChild A p
  by_cases hv : value = LargeResidual.Paired.honestValue A (chainChild p)
  · have hk := hsingle (.chain p) hb hpos (chainChild p) (vslot p.1.layer p.1.chain.val) (childSlots_chain p)
      (by rw [show vslot p.1.layer p.1.chain.val = vslot a.key.lay a.chain from rfl, slotValue_chainRowW]; exact hv)
    exact frontier_child_unknown A published (gAddr a ha.source) ⟨s, hs7⟩ (by
      change s + 1 = Wots.CanonicalRef.depth A (Wots.CanonicalRef.sourceMessages A) (wotsAddr (gAddr a ha.source))
      rw [wotsAddr_gAddr]; omega) hk
  · apply hhit (.chain p) hb hpos
    refine ⟨fun heq => hv ?_, ?_⟩
    · have := congrArg (fun X => slotValue X (vslot a.key.lay a.chain)) heq
      simp only [slotValue_chainRowW] at this
      rw [this, honestInput_chainNode]
      erw [slotValue_chainRowW]
      rw [hcv]
      rfl
    · rw [hans, CanonGraph.Paired.pairedProj_chain]
      change Wots.rowHalf a s answer = _
      rw [hlow, honestValue_chainNode]
      unfold Wots.CanonicalRef.frontierValue
      congr 1
      change Wots.CanonicalRef.depth A (Wots.CanonicalRef.sourceMessages A) a = s + 1
      omega

end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityExtraction SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open CanonGraph CanonEncoding
open Wots.CanonicalRef
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem paired_hit_false (A : Answers) (K : Coord → Prop) (qs : List Spec.Domain)
    (position : Extract.Pos) (input : HashInput)
    (hq : (.inl (.inr input) : Spec.Domain) ∈ qs)
    (hpos : Extract.posOf input = some position)
    (hb : Extract.Paired.Bounded position) (hsrc : WotsExtract.PosSource position)
    (hhit : Extract.Paired.HashHitAt A position (Extract.Paired.honestInput A position) input)
    (hclear : AllClear A K qs) : False := by
  obtain ⟨node, rfl⟩ := Wots.Structural.exists_node_of_posSource hsrc
  exact (hclear input hq).1 node hb hpos hhit

theorem structuralHitSrc_false (A : Answers) (K : Coord → Prop) (qs : List Spec.Domain)
    (h : CanonicalExtract.StructuralHitSrc A (sourceMessages A) (Wots.entriesOf A qs))
    (hclear : AllClear A K qs) : False := by
  obtain ⟨p,x,a,hm,hp,hb,hs,hc,hmain,hh⟩ := h
  obtain ⟨hq,ha⟩ := WotsExtract.mem_entriesOf_iff.mp hm
  apply paired_hit_false A K qs p x hq hp _ hs _ hclear
  · cases p <;> simp_all [CanonicalExtract.MainPosition, Extract.Paired.Bounded]
  · cases p with
    | chain => unfold Extract.Paired.HashHitAt; rw [Extract.Paired.proj_chain]; exact hh
    | leaf => unfold Extract.Paired.HashHitAt; rw [Extract.Paired.proj_leaf]; exact hh
    | node => unfold Extract.Paired.HashHitAt; rw [Extract.Paired.proj_node]; exact hh
    | _ => simp_all [CanonicalExtract.MainPosition]

theorem source_encLeaf (L : Wots.LeafAddr) (h : WotsExtract.SourceLeaf7 L) :
    ∃ E : ClaudeWCT.W9.T3.Security.CanonEncoding.EncLeaf, E.toWots = L := by
  have ht : L.tree < 2^31 := h.tree_lt
  have hl : L.leaf < 4096 := lt_of_lt_of_le h.2 (by
    calc 2^height L.lay ≤ 2^12 := Nat.pow_le_pow_right (by decide) (SigGolfCandidate.T3M.Extract.height_le _)
         _ = 4096 := by decide)
  refine ⟨⟨⟨L.lay,⟨L.tree,ht⟩,⟨L.leaf,hl⟩⟩,h⟩,?_⟩
  cases L
  rfl

theorem encodingMatch_false (A : Answers) (K : Coord → Prop) (qs : List Spec.Domain)
    (L : Wots.LeafAddr) (hL : WotsExtract.SourceLeaf7 L)
    (hs : referenceSearch A (sourceMessages A) L ≠ none)
    (h : EncodingMatchAt A (sourceMessages A) (Wots.entriesOf A qs) L)
    (hclear : AllClear A K qs) : False := by
  obtain ⟨m,ctr,pad,answer,hfit,hm,hne,hns,hdec⟩ := h
  obtain ⟨hq,ha⟩ := WotsExtract.mem_entriesOf_iff.mp hm
  obtain ⟨E,rfl⟩ := source_encLeaf L hL
  exact (hclear _ hq).2.2 ⟨E,m,ctr,pad,hfit,rfl,hs,hne,hns,by rw [ha];exact hdec⟩

theorem wotsPrimitive_false (A : Answers) (published : SigGolfCandidate.T3.Cache)
    (qs : List Spec.Domain)
    (hs : ∀ L, WotsExtract.SourceLeaf7 L → referenceSearch A (sourceMessages A) L ≠ none)
    (h : CanonicalExtract.WotsPrimitiveSrc A (sourceMessages A) (Wots.entriesOf A qs))
    (hclear : AllClear A (LargeResidual.Paired.Known (Disclosed A published)) qs) : False := by
  rcases h with ⟨L,hL,h⟩ | h | ⟨a,ha,h⟩ | ⟨a,b,ha,hb,hab,h,hh⟩ | ⟨a,ha,hm,h⟩
  · exact encodingMatch_false A _ qs L hL (hs L hL) h hclear
  · exact structuralHitSrc_false A _ qs h hclear
  · obtain ⟨hd,start,middle,-,hrow⟩ := h
    exact contactAt_false A published qs a ha ⟨by omega,middle,hrow⟩ hclear
  · exact contactAt_false A published qs a ha h hclear
  · exact contactAt_false A published qs a ha h hclear
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (routeAddr)
open SigGolfCandidate.T3.Security.LargeCoupling (wotsAddr slotValue_block4_three)
open SigGolfCandidate.T3.Security.LargeResidual (slotValue)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _
theorem treeChild_ne_wctItem {lay : Layer} {tree : Fin (2^31)} {level n : Nat} {d : Coord}
    (hd : treeChild lay tree level n = some d) (a : CanonGraph.WctAddr) (p : Nat) : d ≠ wctItem a p := by
  unfold treeChild at hd
  unfold wctItem
  by_cases h0 : level = 0
  · rw [if_pos h0, Option.map_eq_some_iff] at hd
    obtain ⟨L, _, rfl⟩ := hd
    split_ifs <;> simp
  · rw [if_neg h0, Option.map_eq_some_iff] at hd
    obtain ⟨m, _, rfl⟩ := hd
    split_ifs <;> simp
theorem ftsChild_ne_wctItem {index : Fin (2^31)} {coord : Fin 9} {level n : Nat} {d : Coord}
    (hd : LargeResidual.Paired.ftsChild index coord level n = some d) (a : CanonGraph.WctAddr) (p : Nat) : d ≠ wctItem a p := by
  unfold LargeResidual.Paired.ftsChild at hd
  unfold wctItem
  by_cases h0 : level = 0
  · rw [if_pos h0] at hd
    by_cases h1 : CanonGraph.Paired.rawLeaf coord.val n < 128
    · rw [dif_pos h1, Option.some.injEq] at hd; subst hd; split_ifs <;> simp
    · rw [dif_neg h1] at hd; cases hd
  · rw [if_neg h0, Option.map_eq_some_iff] at hd
    obtain ⟨m, _, rfl⟩ := hd
    split_ifs <;> simp
theorem keygen_not_wct (a : CanonGraph.WctAddr) (p : Nat) : wctItem a p ∉ keygenDisclosed := by
  intro hc
  rcases ClaudeWCT.W9.T3.Security.LargeResidual.mem_keygenDisclosed.mp hc with hc | hc | hc
  · unfold keygenCacheDisclosed at hc
    simp only [List.mem_flatMap, List.mem_filterMap] at hc
    obtain ⟨_, _, _, _, h⟩ := hc
    exact treeChild_ne_wctItem h a p rfl
  · rcases encodingDisclosed_shape hc with ⟨n, h⟩ | ⟨i, h⟩
    all_goals unfold wctItem at h; split_ifs at h <;> simp at h
  · obtain ⟨n, h⟩ := ClaudeWCT.W9.T3.Security.LargeResidual.topTrialsDisclosed_shape hc
    unfold wctItem at h; split_ifs at h <;> simp at h
theorem layerItems_not_wct (digitsOf : Wots.LeafAddr → List Nat) (index : Fin (2^31)) (a : CanonGraph.WctAddr)
    (p : Nat) : wctItem a p ∉ layerItems digitsOf index := by
  intro hc
  unfold layerItems at hc
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_append] at hc
  obtain ⟨lay, hc | hc⟩ := hc
  · unfold layerChains at hc
    split_ifs at hc
    · simp only [List.mem_map, List.mem_range] at hc
      obtain ⟨i, -, hi⟩ := hc
      unfold chainItem wctItem at hi
      split_ifs at hi <;> simp at hi
    · cases hc
  · unfold layerPath at hc
    split_ifs at hc
    · simp only [List.mem_filterMap, List.mem_range] at hc
      obtain ⟨j, _, hj⟩ := hc
      exact treeChild_ne_wctItem hj a p rfl
    · cases hc
theorem wctItem_mem_signItems (A : Answers) (N : HashOutput) (a : CanonGraph.WctAddr)
    (p : Nat) (hp : p ≤ 4) (h : wctItem a p ∈ LargeResidual.Paired.signItems A N) :
    a.1 = digestIndex N ∧ a.2.2.1 = rawChildFromOutput N a.2.1 ∧ p = 4 - WCT9.wordDigit (forestRank N a.2.1.val) a.2.2.2 := by
  unfold LargeResidual.Paired.signItems at h
  rcases List.mem_append.mp h with h | h
  · unfold LargeResidual.Paired.ftsItems LargeResidual.Paired.wctOpened LargeResidual.Paired.wctPath at h
    simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_append, List.mem_ofFn,
      List.mem_filterMap, List.mem_range] at h
    obtain ⟨k, ⟨t, ht⟩ | ⟨l, _, hl⟩⟩ := h
    · have hle : 4 - WCT9.wordDigit (forestRank N k.val) t ≤ 4 := Nat.sub_le _ _
      obtain ⟨hab, hpq⟩ := wctItem_injective hle hp ht
      subst hab
      exact ⟨rfl, rfl, hpq.symm⟩
    · exact (ftsChild_ne_wctItem hl a p rfl).elim
  · exact (layerItems_not_wct _ _ a p h).elim
theorem posOf_honest_wctChain (A : Answers) (a : CanonGraph.WctAddr) (s : Fin 4) :
    Extract.posOf (Extract.Paired.honestInput A (CanonGraph.Node.wctChain (a, s)).toPos) =
      some (CanonGraph.Node.wctChain (a, s)).toPos :=
  Extract.posOf_eq (CanonGraph.toPos_bounded _) (Extract.Paired.honestInput_length A _)
    (Extract.Paired.hdrBlock_honestInput A _)
theorem honestValue_wctItem (A : Answers) (a : CanonGraph.WctAddr) (p : Nat) (hp : p ≤ 4) :
    LargeResidual.Paired.honestValue A (wctItem a p) = Extract.wctValue A a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val p := by
  by_cases h0 : p = 0
  · subst h0
    rw [wctItem_zero]
    change CanonGraph.wctSeedsOf (CanonGraph.secretsOf A) a = _
    rw [← CanonGraph.wctSeed_secrets]
    simp [Extract.wctValue, WCT9.chain]
  · rw [wctItem_pos a p h0 hp]
    obtain ⟨s, rfl⟩ : ∃ s, p = s + 1 := ⟨p - 1, by omega⟩
    rw [← WctExtract.wctValue_succ]
    simp only [LargeResidual.Paired.honestValue, CanonGraph.Node.toPos, Nat.add_sub_cancel]
    cases hh : WCT9.ftsChainHigh a.2.2.2.val s <;>
      simp [Extract.Pos.proj, Extract.Paired.proj, Extract.Pos.high, hh, Extract.eval_halfHash,
        WCT9.ftsChainInputW_padded, WCT9.halfOf, Extract.Paired.honestInput, Extract.honestInput] <;> rfl
theorem slotValue_honest_wctChain (A : Answers) (a : CanonGraph.WctAddr) (s : Fin 4) :
    slotValue (Extract.Paired.honestInput A (CanonGraph.Node.wctChain (a, s)).toPos)
      (if WCT9.ftsIsG a.2.2.2.val then 0 else 3) = LargeResidual.Paired.honestValue A (wctItem a s.val) := by
  rw [honestValue_wctItem A a s.val (by omega)]
  have hb : ∀ (x : Digest) (h : BitVec 128),
      SphincsSecurity.bytesLE 16 x ++ SphincsSecurity.bytesLE 16 h ++ zero16 ++ zero16 = block4 x h 0 0 := by
    intro x h; simp only [block4, show zero16 = SphincsSecurity.bytesLE 16 (0 : Digest) by decide]
  cases hG : WCT9.ftsIsG a.2.2.2.val
  · simp only [Bool.false_eq_true, if_false]
    change slotValue (Extract.honestInput A (.wctChain a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val s.val)) 3 = _
    rw [WctExtract.honestInput_wctChain, WCT9.ftsChainInputW_F hG, WctExtract.wctChainInput_block4']
    exact slotValue_block4_three _ _ _ _
  · simp only [if_true]
    change slotValue (Extract.honestInput A (.wctChain a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val s.val)) 0 = _
    rw [WctExtract.honestInput_wctChain, WCT9.ftsChainInputW_G hG, hb]
    unfold block4
    rw [List.append_assoc, List.append_assoc]
    unfold slotValue
    simp only [Nat.mul_zero, List.drop_zero]
    rw [List.take_append_of_le_length (by rw [SphincsSecurity.bytesLE_length])]
    rw [List.take_of_length_le (by rw [SphincsSecurity.bytesLE_length])]
    exact Correctness.readDigest_bytesLE _
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityExtraction SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.Research.SharedForest
open CanonGraph
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def DisclosedOutputs (A : Answers) (outputs : List HashOutput) (c : Coord) : Prop :=
  c ∈ keygenDisclosed ∨ ∃ output ∈ outputs, c ∈ LargeResidual.Paired.signItems A output

theorem known_wct_covered (A : Answers) (outputs : List HashOutput)
    (a : CanonGraph.WctAddr) (p : Nat) (hp : p ≤ 4)
    (hk : LargeResidual.Paired.Known (DisclosedOutputs A outputs) (wctItem a p)) :
    ∃ output ∈ outputs, a.1 = digestIndex output ∧
      a.2.2.1 = rawChildFromOutput output a.2.1 ∧
      4 - WCT9.wordDigit (forestRank output a.2.1.val) a.2.2.2 ≤ p := by
  obtain ⟨p',hpp',hd⟩ := known_wctItem hp hk
  rcases hd with hkg | ⟨output,hm,hs⟩
  · exact (keygen_not_wct a p' hkg).elim
  · obtain ⟨hi,hc,hp'⟩ := wctItem_mem_signItems A output a p' (by omega) hs
    exact ⟨output,hm,hi,hc,by omega⟩

theorem clear_active_start_covered (A : Answers) (outputs : List HashOutput)
    (qs : List Spec.Domain) (a : CanonGraph.WctAddr) (step : Fin 4)
    (hq : (.inl (.inr (Extract.Paired.honestInput A (CanonGraph.Node.wctChain (a,step)).toPos)) : Spec.Domain) ∈ qs)
    (hclear : AllClear A (LargeResidual.Paired.Known (DisclosedOutputs A outputs)) qs) :
    ∃ output ∈ outputs, a.1 = digestIndex output ∧
      a.2.2.1 = rawChildFromOutput output a.2.1 ∧
      4-WCT9.wordDigit (forestRank output a.2.1.val) a.2.2.2 ≤ step.val := by
  have hb : Extract.Paired.Bounded (CanonGraph.Node.wctChain (a,step)).toPos := by
    change (CanonGraph.Node.wctChain (a,step)).toPos.Bounded
    exact CanonGraph.toPos_bounded _
  have hk := (hclear _ hq).2.1 (.wctChain (a,step)) hb (posOf_honest_wctChain A a step)
    (wctItem a step.val) (if WCT9.ftsIsG a.2.2.2.val then 0 else 3) rfl (slotValue_honest_wctChain A a step)
  exact known_wct_covered A outputs a step.val (by omega) hk

theorem exists_pos_digit (r : WCT9.Rank) : ∃ t : Fin 6, 1 ≤ WCT9.wordDigit r t := by
  by_contra h
  push Not at h
  have hz : ∀ t ∈ (Finset.univ : Finset (Fin 6)), WCT9.wordDigit r t = 0 := fun t _ => by have := h t; omega
  have := WCT9.wordStep_count r
  rw [Finset.sum_eq_zero hz] at this
  omega

theorem clear_slots_covered (A : Answers) (outputs : List HashOutput) (N : HashOutput)
    (qs : List Spec.Domain)
    (hactive : ∀ (k : Fin 9) (t : Fin 6), 1 ≤ WCT9.wordDigit (forestRank N k.val) t →
      (.inl (.inr (Extract.Paired.honestInput A (.wctChain (WCT9.digestIndex N) k.val
        (rawChildFromOutput N k).val t.val (4-WCT9.wordDigit (forestRank N k.val) t)))) : Spec.Domain) ∈ qs)
    (hclear : AllClear A (LargeResidual.Paired.Known (DisclosedOutputs A outputs)) qs) :
    ∀ (k : Fin 9) (t : Fin 6), ∃ output ∈ outputs,
      WCT9.digestIndex output = WCT9.digestIndex N ∧ rawChildFromOutput output k = rawChildFromOutput N k ∧
      WCT9.wordDigit (forestRank N k.val) t ≤ WCT9.wordDigit (forestRank output k.val) t := by
  have hpositive : ∀ (k : Fin 9) (t : Fin 6), 1 ≤ WCT9.wordDigit (forestRank N k.val) t →
      ∃ output ∈ outputs, WCT9.digestIndex output = WCT9.digestIndex N ∧
        rawChildFromOutput output k = rawChildFromOutput N k ∧
        WCT9.wordDigit (forestRank N k.val) t ≤ WCT9.wordDigit (forestRank output k.val) t := by
    intro k t hpos
    have hfour := WCT9.wordDigit_le_four (forestRank N k.val) t
    let a : CanonGraph.WctAddr := (digestIndex N,k,rawChildFromOutput N k,t)
    let step : Fin 4 := ⟨4-WCT9.wordDigit (forestRank N k.val) t,by omega⟩
    obtain ⟨out,hm,hi,hc,hd⟩ := clear_active_start_covered A outputs qs a step (hactive k t hpos) hclear
    have hout := WCT9.wordDigit_le_four (forestRank out k.val) t
    exact ⟨out,hm,(congrArg Fin.val hi).symm,hc.symm,by dsimp [a,step] at hd;omega⟩
  intro k t
  by_cases hpos : 1 ≤ WCT9.wordDigit (forestRank N k.val) t
  · exact hpositive k t hpos
  · obtain ⟨t',ht'⟩ := exists_pos_digit (forestRank N k.val)
    obtain ⟨out,hm,hi,hc,hd⟩ := hpositive k t' ht'
    exact ⟨out,hm,hi,hc,by omega⟩
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.LargeCoupling (record_inputs)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem trace_inputs (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q ≤ 2^127)
    (result : PairedOuter.PaddedGame.TraceResult)
    (hr : result ∈ (PairedOuter.PaddedGame.tracedExperiment adversary q hq).support) :
    ∀ e ∈ (QueryRecorded.recordedTrace result).events, ∀ x, e.input = .inl (.inr x) →
      x ∈ Wots.PairedReference.referenceInputs adversary :=
  record_inputs _ _ (∅,∅) (Wots.PairedReference.Ref.referenceInputs_inputsIn adversary) _
    (PairedBankLink.traced_record_support adversary q hq result hr)
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction (queried)
open ClaudeWCT.W9.T3M

def BankFresh (A : Answers) (published : SigGolfCandidate.T3.Cache)
    (log : QueryLog Final.Paired.Requests) (qs : List Spec.Domain) : Prop :=
  ∃ (message : Message) (rho : Digest) (counter : BitVec 32) (N : HashOutput),
    A (.inl (.inr (pad64 (digestInput rho message counter)))) = N ∧
    (.inl (.inr (pad64 (digestInput rho message counter))) : Spec.Domain) ∈ qs ∧
    ClaudeWCT.Bank.Paired.lawSpec.admissible N = true ∧
    (∀ (k : Fin 9) (t : Fin 6) (s : Fin 4),
      s.val = 4-WCT9.wordDigit (SigGolfCandidate.Research.SharedForest.forestRank N k.val) t →
      (.inl (.inr (Extract.Paired.honestInput A (.wctChain (WCT9.digestIndex N) k.val
        (SigGolfCandidate.Research.SharedForest.rawChildFromOutput N k).val t.val s.val))) : Spec.Domain) ∈ qs) ∧
    (∀ entry ∈ log, (.inl (.inr (pad64 (digestInput rho message counter))) : Spec.Domain) ∉
      queried A (PairedOuter.FullGame.authenticatedSign published entry.1))
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_LargeContactCertClean ====
section

section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (IsDigestRow)
open SigGolfCandidate.T3.Security.LargeCoupling (honestNonce)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeContactCertFold : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
section Fold
variable (U : Finset HashInput) (A : Answers) (published : SigGolfCandidate.T3.Cache)
end Fold
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeCoupling (honestNonce)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeContactCert : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M (wrho wdc)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (IsDigestRow)
open SigGolfCandidate.T3.Security.LargeCoupling (record_events_known chargeOf EventsAgree honestNonce)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeContactCertClean : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
end ClaudeWCT.W9.T3.Security.LargeCoupling
end

section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord WCoord trialRows)
open SigGolfCandidate.T3.Security.LargeResidual (IsDigestRow)
open SigGolfCandidate.T3.Security.LargeCoupling (honestNonce)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeContactCertFold_paired : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
def CoverOk (st : RouterState) : Prop :=
  ∀ m c N, st.memo.lookup m = some (some (c, N)) → N ∈ st.exposures ∨ st.reused = true
def signCount : List TaggedStep → Nat
  | [] => 0
  | .world _ :: rest => signCount rest
  | .sign _ _ _ :: rest => signCount rest + 1
def stepLog : List TaggedStep → QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests
  | [] => []
  | .world _ :: rest => stepLog rest
  | .sign request output _ :: rest => ⟨request, output⟩ :: stepLog rest
theorem signCount_eq_length (steps : List TaggedStep) : signCount steps = (stepLog steps).length := by
  induction steps with
  | nil => rfl
  | cons s rest ih => cases s <;> simp [signCount, stepLog, ih]
theorem taggedRecord_log {α : Type} (program : OracleComp PairedOuter.LazyPrivate.Interaction α) (published : SigGolfCandidate.T3.Cache)
    (state : LazyPrivate.State) (t : Tagged α) (ht : t ∈ support (taggedRecord published program state)) :
    t.value.2 = stepLog t.steps := by
  induction program using OracleComp.inductionOn generalizing state t with
  | pure value =>
      rw [taggedRecord_pure, mem_support_pure_iff] at ht
      subst ht
      rfl
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [taggedRecord_world, mem_support_bind_iff] at ht
          obtain ⟨middle, -, ht⟩ := ht
          rw [support_map] at ht
          obtain ⟨last, hl, rfl⟩ := ht
          exact ih middle.1 middle.2 last hl
      | inr request =>
          rw [taggedRecord_request, mem_support_bind_iff] at ht
          obtain ⟨block, -, ht⟩ := ht
          rw [support_map] at ht
          obtain ⟨last, hl, rfl⟩ := ht
          change ⟨request, block.value⟩ :: last.value.2 = ⟨request, block.value⟩ :: stepLog last.steps
          rw [ih block.value block.state last hl]
theorem sign_mem_stepLog {steps : List TaggedStep} {request : Security.Request} {output : Option SigGolfCandidate.Research.SharedForest.Signature}
    {events : List FirstHit.QueryEvent} (h : TaggedStep.sign request output events ∈ steps) :
    (⟨request, output⟩ : (r : ClaudeWCT.W9.T3M.Final.Paired.Requests.Domain) × ClaudeWCT.W9.T3M.Final.Paired.Requests.Range r) ∈ stepLog steps := by
  induction steps with
  | nil => cases h
  | cons s rest ih =>
      rcases List.mem_cons.mp h with rfl | h'
      · exact List.mem_cons_self
      · cases s with
        | world e => exact ih h'
        | sign r o ev => exact List.mem_cons_of_mem _ (ih h')
section Fold
variable (U : Finset HashInput) (A : Answers) (published : SigGolfCandidate.T3.Cache)
theorem routerEvent_fields (st : RouterState) (e : FirstHit.QueryEvent) :
    (routerEvent U st e).exposures = st.exposures ∧ (routerEvent U st e).reused = st.reused ∧
      (routerEvent U st e).memo = st.memo ∧ (routerEvent U st e).trials = st.trials := by
  rcases e with ⟨b, (n | X) | c, y⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · change (st.next U X y).exposures = _ ∧ (st.next U X y).reused = _ ∧ (st.next U X y).memo = _ ∧
      (st.next U X y).trials = _
    unfold LargeResidual.RouterState.next
    split_ifs <;> exact ⟨rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩
theorem routerEvents_fields (events : List FirstHit.QueryEvent) (st : RouterState) :
    (events.foldl (routerEvent U) st).exposures = st.exposures ∧ (events.foldl (routerEvent U) st).reused = st.reused ∧
      (events.foldl (routerEvent U) st).memo = st.memo ∧ (events.foldl (routerEvent U) st).trials = st.trials := by
  induction events generalizing st with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons e rest ih =>
      rw [List.foldl_cons]
      obtain ⟨h1, h2, h3, h4⟩ := ih (routerEvent U st e)
      obtain ⟨g1, g2, g3, g4⟩ := routerEvent_fields U st e
      exact ⟨h1.trans g1, h2.trans g2, h3.trans g3, h4.trans g4⟩
theorem finishState_bank (st1 : RouterState) (found : Option (BitVec 32 × HashOutput)) :
    (finishState A st1 found).exposures = st1.exposures ∧ (finishState A st1 found).reused = st1.reused ∧
      (finishState A st1 found).memo = st1.memo ∧ (finishState A st1 found).trials = st1.trials := by
  unfold finishState
  cases found with
  | none => exact ⟨rfl, rfl, rfl, rfl⟩
  | some f =>
      obtain ⟨c, N⟩ := f
      dsimp only
      split_ifs <;> exact ⟨rfl, rfl, rfl, rfl⟩
theorem signedState_bank (nv : Message → Digest) (st : RouterState) (request : Security.Request) :
    (request.cache = published →
      (signedState A nv published st request).exposures = (startState A nv st request.message).exposures ∧
      (signedState A nv published st request).reused = (startState A nv st request.message).reused ∧
      (signedState A nv published st request).memo = (startState A nv st request.message).memo ∧
      (signedState A nv published st request).trials = (startState A nv st request.message).trials) ∧
    (request.cache ≠ published → signedState A nv published st request = st) := by
  rw [signedState_eq]
  constructor
  · intro hc
    rw [if_pos hc]
    exact finishState_bank A _ _
  · intro hc
    rw [if_neg hc]
theorem signed_memo_lookup (st : RouterState) (rho : Digest) (m m' : Message)
    (found : Option (BitVec 32 × HashOutput)) :
    (st.signed rho m found).memo.lookup m' = if m' = m then some found else st.memo.lookup m' := by
  rw [(LargeResidual.Paired.RouterState.signed_fields _ _ _ _).2.2.2.2.2, List.lookup_cons]
  by_cases h : m' = m
  · subst h; simp
  · have hne : (m' == m) = false := by simpa using h
    rw [hne, if_neg h]
theorem signed_exposures_reused (st : RouterState) (rho : Digest) (m : Message)
    (found : Option (BitVec 32 × HashOutput)) :
    (∀ N, N ∈ st.exposures → N ∈ (st.signed rho m found).exposures) ∧
      (st.reused = true → (st.signed rho m found).reused = true) ∧
      (∀ c N, found = some (c, N) → N ∈ (st.signed rho m found).exposures ∨ (st.signed rho m found).reused = true) := by
  unfold LargeResidual.Paired.RouterState.signed
  split_ifs
  · exact ⟨fun N h => h, fun _ => rfl, fun _ _ _ => Or.inr rfl⟩
  · refine ⟨fun N h => List.mem_append_left _ h, fun h => h, fun c N hf => Or.inl ?_⟩
    subst hf
    simp
theorem coverOk_startState (nv : Message → Digest) (st : RouterState) (m : Message) (h : CoverOk st)
    (hmemo : MemoOk A st) : CoverOk (startState A nv st m) ∧ MemoOk A (startState A nv st m) := by
  unfold startState
  split_ifs with hs
  · exact ⟨h, hmemo⟩
  · obtain ⟨hx, hr, hnew⟩ := signed_exposures_reused st (nv m) m (LargeResidual.Paired.signDigest A m)
    constructor
    · intro m' c N hl
      rw [signed_memo_lookup] at hl
      split_ifs at hl with hm
      · exact hnew c N (Option.some.inj hl)
      · rcases h m' c N hl with h1 | h1
        · exact Or.inl (hx N h1)
        · exact Or.inr (hr h1)
    · intro m' f hl
      rw [signed_memo_lookup] at hl
      split_ifs at hl with hm
      · subst hm; exact (Option.some.inj hl).symm
      · exact hmemo m' f hl
theorem coverOk_signedState (st : RouterState) (request : Security.Request) (h : CoverOk st) (hmemo : MemoOk A st) :
    CoverOk (signedState A (honestNonce A) published st request) := by
  obtain ⟨hpub, hnpub⟩ := signedState_bank A published (honestNonce A) st request
  by_cases hc : request.cache = published
  · obtain ⟨h1, h2, h3, -⟩ := hpub hc
    intro m c N hl
    rw [h1, h2]
    rw [h3] at hl
    exact (coverOk_startState A (honestNonce A) st request.message h hmemo).1 m c N hl
  · rw [hnpub hc]; exact h
theorem coverOk_event (st : RouterState) (e : FirstHit.QueryEvent) (h : CoverOk st) : CoverOk (routerEvent U st e) := by
  obtain ⟨h1, h2, h3, -⟩ := routerEvent_fields U st e
  intro m c N hl
  rw [h1, h2]
  rw [h3] at hl
  exact h m c N hl
theorem memoOk_event (st : RouterState) (e : FirstHit.QueryEvent) (h : MemoOk A st) : MemoOk A (routerEvent U st e) := by
  intro m f hl
  rw [(routerEvent_fields U st e).2.2.1] at hl
  exact h m f hl
theorem invariants_steps (steps : List TaggedStep) (st : RouterState) (h : CoverOk st) (hmemo : MemoOk A st) :
    CoverOk (steps.foldl (routerStep U A (honestNonce A) published) st) ∧
      MemoOk A (steps.foldl (routerStep U A (honestNonce A) published) st) := by
  induction steps generalizing st with
  | nil => exact ⟨h, hmemo⟩
  | cons s rest ih =>
      rw [List.foldl_cons]
      apply ih
      · cases s with
        | world e => exact coverOk_event U st e h
        | sign request out evs => exact coverOk_signedState A published st request h hmemo
      · cases s with
        | world e => exact memoOk_event U A st e hmemo
        | sign request out evs => exact signedState_memo A (honestNonce A) published st request hmemo
theorem invariants_events (events : List FirstHit.QueryEvent) (st : RouterState) (h : CoverOk st)
    (hmemo : MemoOk A st) :
    CoverOk (events.foldl (routerEvent U) st) ∧ MemoOk A (events.foldl (routerEvent U) st) := by
  induction events generalizing st with
  | nil => exact ⟨h, hmemo⟩
  | cons e rest ih =>
      rw [List.foldl_cons]
      exact ih _ (coverOk_event U st e h) (memoOk_event U A st e hmemo)
theorem memo_isSome_event (st : RouterState) (e : FirstHit.QueryEvent) (m : Message)
    (h : (st.memo.lookup m).isSome) : ((routerEvent U st e).memo.lookup m).isSome := by
  rw [(routerEvent_fields U st e).2.2.1]; exact h
theorem memo_isSome_sign (st : RouterState) (request : Security.Request) (m : Message)
    (h : (st.memo.lookup m).isSome) :
    ((signedState A (honestNonce A) published st request).memo.lookup m).isSome := by
  obtain ⟨hpub, hnpub⟩ := signedState_bank A published (honestNonce A) st request
  by_cases hc : request.cache = published
  · rw [(hpub hc).2.2.1]
    unfold startState
    split_ifs with hs
    · exact h
    · rw [signed_memo_lookup]
      split_ifs <;> simp_all
  · rw [hnpub hc]; exact h
theorem memo_isSome_signed_self (st : RouterState) (request : Security.Request) (hc : request.cache = published) :
    ((signedState A (honestNonce A) published st request).memo.lookup request.message).isSome := by
  rw [((signedState_bank A published (honestNonce A) st request).1 hc).2.2.1]
  unfold startState
  split_ifs with hs
  · exact hs
  · rw [signed_memo_lookup, if_pos rfl]; rfl
theorem memo_isSome_steps (steps : List TaggedStep) (st : RouterState) (m : Message)
    (h : (st.memo.lookup m).isSome) :
    ((steps.foldl (routerStep U A (honestNonce A) published) st).memo.lookup m).isSome := by
  induction steps generalizing st with
  | nil => exact h
  | cons s rest ih =>
      rw [List.foldl_cons]
      apply ih
      cases s with
      | world e => exact memo_isSome_event U st e m h
      | sign request out evs => exact memo_isSome_sign A published st request m h
theorem sign_memo_steps (steps : List TaggedStep) (st : RouterState) (request : Security.Request)
    (out : Option SigGolfCandidate.Research.SharedForest.Signature) (evs : List FirstHit.QueryEvent) (hmem : TaggedStep.sign request out evs ∈ steps)
    (hc : request.cache = published) :
    ((steps.foldl (routerStep U A (honestNonce A) published) st).memo.lookup request.message).isSome := by
  induction steps generalizing st with
  | nil => cases hmem
  | cons s rest ih =>
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact memo_isSome_steps U A published rest _ _ (memo_isSome_signed_self A published st request hc)
      · exact ih _ hmem
theorem covered_fold (steps : List TaggedStep) (verdict : List FirstHit.QueryEvent) (request : Security.Request)
    (out : Option SigGolfCandidate.Research.SharedForest.Signature) (evs : List FirstHit.QueryEvent) (hmem : TaggedStep.sign request out evs ∈ steps)
    (hc : request.cache = published) (c : BitVec 32) (N : HashOutput)
    (hN : LargeResidual.Paired.signDigest A request.message = some (c, N)) :
    N ∈ (routerFold U A published steps verdict).exposures ∨ (routerFold U A published steps verdict).reused = true := by
  unfold routerFold
  have hinv0 : CoverOk LargeResidual.RouterState.initial ∧ MemoOk A LargeResidual.RouterState.initial :=
    ⟨fun m c N h => by simp [LargeResidual.RouterState.initial] at h, fun m f h => by simp [LargeResidual.RouterState.initial] at h⟩
  obtain ⟨h1, h2⟩ := invariants_steps U A published steps _ hinv0.1 hinv0.2
  obtain ⟨h3, h4⟩ := invariants_events U A verdict _ h1 h2
  have hs := sign_memo_steps U A published steps LargeResidual.RouterState.initial request out evs hmem hc
  have hs' : ((verdict.foldl (routerEvent U) (steps.foldl (routerStep U A (honestNonce A) published)
      LargeResidual.RouterState.initial)).memo.lookup request.message).isSome := by
    rw [(routerEvents_fields U verdict _).2.2.1]; exact hs
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp hs'
  have hfe := h4 _ _ hf
  rw [hN] at hfe
  subst hfe
  exact h3 _ c N hf
theorem exposures_signedState_le (st : RouterState) (request : Security.Request) :
    (signedState A (honestNonce A) published st request).exposures.length ≤ st.exposures.length + 1 := by
  obtain ⟨hpub, hnpub⟩ := signedState_bank A published (honestNonce A) st request
  by_cases hc : request.cache = published
  · rw [(hpub hc).1]
    unfold startState
    split_ifs
    · omega
    · unfold LargeResidual.Paired.RouterState.signed
      split_ifs
      · dsimp only; omega
      · dsimp only
        rw [List.length_append]
        have : ((LargeResidual.Paired.signDigest A request.message).map Prod.snd).toList.length ≤ 1 := by
          cases LargeResidual.Paired.signDigest A request.message <;> simp
        omega
  · rw [hnpub hc]; omega
theorem exposures_steps_le (steps : List TaggedStep) (st : RouterState) :
    (steps.foldl (routerStep U A (honestNonce A) published) st).exposures.length ≤
      st.exposures.length + signCount steps := by
  induction steps generalizing st with
  | nil => simp [signCount]
  | cons s rest ih =>
      rw [List.foldl_cons]
      refine (ih _).trans ?_
      cases s with
      | world e =>
          change (routerEvent U st e).exposures.length + signCount rest ≤ st.exposures.length + signCount rest
          rw [(routerEvent_fields U st e).1]
      | sign request out evs =>
          have := exposures_signedState_le A published st request
          change (signedState A (honestNonce A) published st request).exposures.length + signCount rest ≤
            st.exposures.length + (signCount rest + 1)
          omega
theorem exposures_fold_le (steps : List TaggedStep) (verdict : List FirstHit.QueryEvent) :
    (routerFold U A published steps verdict).exposures.length ≤ signCount steps := by
  unfold routerFold
  rw [(routerEvents_fields U verdict _).1]
  have := exposures_steps_le U A published steps LargeResidual.RouterState.initial
  simpa [LargeResidual.RouterState.initial] using this
theorem trials_steps (steps : List TaggedStep) (st : RouterState) (X : HashInput)
    (hX : X ∈ (steps.foldl (routerStep U A (honestNonce A) published) st).trials) :
    X ∈ st.trials ∨ ∃ request out evs, TaggedStep.sign request out evs ∈ steps ∧ request.cache = published ∧
      X ∈ trialRows (honestNonce A request.message) request.message (LargeResidual.Paired.signDigest A request.message) := by
  induction steps generalizing st with
  | nil => exact Or.inl hX
  | cons s rest ih =>
      rw [List.foldl_cons] at hX
      rcases ih _ hX with h | ⟨r, o, e, hm, hc, hr⟩
      · cases s with
        | world e =>
            change X ∈ (routerEvent U st e).trials at h
            rw [(routerEvent_fields U st e).2.2.2] at h
            exact Or.inl h
        | sign request out evs =>
            change X ∈ (signedState A (honestNonce A) published st request).trials at h
            obtain ⟨hpub, hnpub⟩ := signedState_bank A published (honestNonce A) st request
            by_cases hc : request.cache = published
            · rw [(hpub hc).2.2.2] at h
              unfold startState at h
              split_ifs at h
              · exact Or.inl h
              · rw [(LargeResidual.Paired.RouterState.signed_fields _ _ _ _).2.2.2.2.1, List.mem_append] at h
                rcases h with h | h
                · exact Or.inl h
                · exact Or.inr ⟨request, out, evs, List.mem_cons_self, hc, h⟩
            · rw [hnpub hc] at h; exact Or.inl h
      · exact Or.inr ⟨r, o, e, List.mem_cons_of_mem _ hm, hc, hr⟩
theorem seen_event_mono' (st : RouterState) (e : FirstHit.QueryEvent) (Y : HashInput) (h : Y ∈ st.seen) :
    Y ∈ (routerEvent U st e).seen := by
  rcases e with ⟨b, (n | X) | c, y⟩
  · exact h
  · change Y ∈ (st.next U X y).seen
    unfold LargeResidual.RouterState.next
    split_ifs <;> exact List.mem_cons_of_mem _ h
  · exact h
theorem seen_event_self (st : RouterState) (b : LazyPrivate.State) (X : HashInput) (y : HashOutput) :
    X ∈ (routerEvent U st ⟨b, .inl (.inr X), y⟩).seen := by
  change X ∈ (st.next U X y).seen
  unfold LargeResidual.RouterState.next
  split_ifs <;> exact List.mem_cons_self
theorem seen_events_mono' (events : List FirstHit.QueryEvent) (st : RouterState) (Y : HashInput) (h : Y ∈ st.seen) :
    Y ∈ (events.foldl (routerEvent U) st).seen := by
  induction events generalizing st with
  | nil => exact h
  | cons e rest ih => exact ih _ (seen_event_mono' U st e Y h)
theorem seen_signed (st : RouterState) (request : Security.Request) :
    (signedState A (honestNonce A) published st request).seen = st.seen ∧
      (signedState A (honestNonce A) published st request).births = st.births := by
  refine ⟨(signedState_seen A (honestNonce A) published st request).1, ?_⟩
  rw [signedState_eq]
  split_ifs
  · rw [(finishState_fields _ _ _).2.2.2.1, (startState_fields _ _ _ _).2.2.2]
  · rfl
def BirthInv (X : HashInput) (N : HashOutput) (st : RouterState) : Prop := X ∈ st.seen → (X, N) ∈ st.births
theorem birthInv_event (X : HashInput) (N : HashOutput) (hXU : X ∈ U) (hXd : IsDigestRow X)
    (st : RouterState) (e : FirstHit.QueryEvent) (hans : ∀ b y, e = ⟨b, .inl (.inr X), y⟩ → y = N)
    (htr : X ∉ st.trials) (h : BirthInv X N st) : BirthInv X N (routerEvent U st e) := by
  rcases e with ⟨b, (n | Y) | c, y⟩
  · exact h
  · change X ∈ (st.next U Y y).seen → (X, N) ∈ (st.next U Y y).births
    intro hs
    unfold LargeResidual.RouterState.next at hs ⊢
    by_cases hY : Y = X
    · subst hY
      have hy : y = N := hans b y rfl
      subst hy
      by_cases hf : st.Fresh Y
      · rw [if_pos ⟨hXU, hXd, hf⟩]
        exact List.mem_cons_self
      · have hfr : ¬(Y ∈ U ∧ IsDigestRow Y ∧ st.Fresh Y) := fun h' => hf h'.2.2
        rw [if_neg hfr]
        have hseen : Y ∈ st.seen := by
          by_contra hn
          exact hf ⟨hn, htr⟩
        exact h hseen
    · have hs' : X ∈ st.seen := by
        split_ifs at hs <;>
        · rcases List.mem_cons.mp hs with h1 | h1
          · exact absurd h1.symm hY
          · exact h1
      split_ifs
      · exact List.mem_cons_of_mem _ (h hs')
      · exact h hs'
  · exact h
theorem birthInv_events (X : HashInput) (N : HashOutput) (hXU : X ∈ U) (hXd : IsDigestRow X)
    (events : List FirstHit.QueryEvent) (hans : ∀ e ∈ events, ∀ b y, e = ⟨b, .inl (.inr X), y⟩ → y = N)
    (st : RouterState) (htr : X ∉ st.trials) (h : BirthInv X N st) :
    BirthInv X N (events.foldl (routerEvent U) st) := by
  induction events generalizing st with
  | nil => exact h
  | cons e rest ih =>
      rw [List.foldl_cons]
      apply ih (fun e' he' => hans e' (List.mem_cons_of_mem _ he'))
      · rw [(routerEvent_fields U st e).2.2.2]; exact htr
      · exact birthInv_event U X N hXU hXd st e (hans e List.mem_cons_self) htr h
theorem trials_sign_mono (st : RouterState) (request : Security.Request) (Y : HashInput) (h : Y ∈ st.trials) :
    Y ∈ (signedState A (honestNonce A) published st request).trials := by
  obtain ⟨hpub, hnpub⟩ := signedState_bank A published (honestNonce A) st request
  by_cases hc : request.cache = published
  · rw [(hpub hc).2.2.2]
    unfold startState
    split_ifs
    · exact h
    · rw [(LargeResidual.Paired.RouterState.signed_fields _ _ _ _).2.2.2.2.1]; exact List.mem_append_left _ h
  · rw [hnpub hc]; exact h
theorem trials_steps_mono (steps : List TaggedStep) (st : RouterState) (Y : HashInput) (h : Y ∈ st.trials) :
    Y ∈ (steps.foldl (routerStep U A (honestNonce A) published) st).trials := by
  induction steps generalizing st with
  | nil => exact h
  | cons s rest ih =>
      rw [List.foldl_cons]
      apply ih
      cases s with
      | world e =>
          change Y ∈ (routerEvent U st e).trials
          rw [(routerEvent_fields U st e).2.2.2]; exact h
      | sign request out evs => exact trials_sign_mono A published st request Y h
theorem birthInv_steps (X : HashInput) (N : HashOutput) (hXU : X ∈ U) (hXd : IsDigestRow X)
    (steps : List TaggedStep)
    (hans : ∀ s ∈ steps, ∀ e, s = .world e → ∀ b y, e = ⟨b, .inl (.inr X), y⟩ → y = N)
    (st : RouterState) (htr : X ∉ (steps.foldl (routerStep U A (honestNonce A) published) st).trials)
    (h : BirthInv X N st) :
    BirthInv X N (steps.foldl (routerStep U A (honestNonce A) published) st) := by
  induction steps generalizing st with
  | nil => exact h
  | cons s rest ih =>
      rw [List.foldl_cons] at htr ⊢
      have hrest := fun s' hs' => hans s' (List.mem_cons_of_mem _ hs')
      apply ih hrest _ htr
      have hst : X ∉ st.trials := fun hm => htr (trials_steps_mono U A published rest _ X (by
        cases s with
        | world e =>
            change X ∈ (routerEvent U st e).trials
            rw [(routerEvent_fields U st e).2.2.2]; exact hm
        | sign request out evs => exact trials_sign_mono A published st request X hm))
      cases s with
      | world e => exact birthInv_event U X N hXU hXd st e (hans _ List.mem_cons_self e rfl) hst h
      | sign request out evs =>
          change X ∈ (signedState A (honestNonce A) published st request).seen →
            (X, N) ∈ (signedState A (honestNonce A) published st request).births
          rw [(seen_signed A published st request).1, (seen_signed A published st request).2]
          exact h
end Fold
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
end

section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord WCoord trialRows)
open SigGolfCandidate.T3.Security.LargeCoupling (honestNonce)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeContactCert_queries : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
theorem disclosed_steps_mem (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache)
    (steps : List TaggedStep) (mon : Monitor) (d : Coord)
    (hd : d ∈ (steps.foldl (Monitor.step U A q published) mon).disclosed) :
    d ∈ mon.disclosed ∨ ∃ request out evs, TaggedStep.sign request out evs ∈ steps ∧
      d ∈ signDisclosed A published request := by
  induction steps generalizing mon with
  | nil => exact Or.inl hd
  | cons s rest ih =>
      rw [List.foldl_cons] at hd
      rcases ih _ hd with h | ⟨r, o, e, hm, hr⟩
      · cases s with
        | world e =>
            change d ∈ (mon.event U A q e).disclosed at h
            rw [disclosed_event] at h
            exact Or.inl h
        | sign request out evs =>
            change d ∈ (mon.sign A published request).disclosed at h
            unfold Monitor.sign at h
            split_ifs at h
            · exact Or.inl h
            · rcases List.mem_append.mp h with h | h
              · exact Or.inl h
              · exact Or.inr ⟨request, out, evs, List.mem_cons_self, h⟩
      · exact Or.inr ⟨r, o, e, List.mem_cons_of_mem _ hm, hr⟩
theorem search_queried (A : Answers) (rho : Digest) (m : Message) :
    ∀ fuel start k, start ≤ k → k < start + fuel →
      (∀ c', start ≤ c' → c' < k →
        SigGolfCandidate.Research.SharedForest.digestAccepted (evalWithAnswerFn A (digest rho m (BitVec.ofNat 32 c'))) = false) →
      (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 k)))) : SigGolfCandidate.T3.Spec.Domain) ∈
        queried A (SigGolfCandidate.Research.SharedForest.sharedDigestSearch rho m start fuel) := by
  intro fuel
  induction fuel with
  | zero => intro start k h1 h2; omega
  | succ fuel ih =>
      intro start k h1 h2 hrej
      rw [SigGolfCandidate.Research.SharedForest.sharedDigestSearch, queried_bind, SigGolfCandidate.T3.Security.BPB.queried_digest]
      by_cases hk : k = start
      · subst hk
        exact List.mem_append_left _ (List.mem_singleton_self _)
      · apply List.mem_append_right
        rw [if_neg (by rw [hrej start le_rfl (by omega)]; decide)]
        exact ih (start + 1) k (by omega) (by omega) (fun c' h1' h2' => hrej c' (by omega) h2')
theorem search_result (A : Answers) (rho : Digest) (m : Message) :
    ∀ fuel start,
      (∀ c N, evalWithAnswerFn A (SigGolfCandidate.Research.SharedForest.sharedDigestSearch rho m start fuel) = some (c, N) →
        ∃ k, start ≤ k ∧ k < start + fuel ∧ c = BitVec.ofNat 32 k ∧ ∀ c', start ≤ c' → c' < k →
          SigGolfCandidate.Research.SharedForest.digestAccepted (evalWithAnswerFn A (digest rho m (BitVec.ofNat 32 c'))) = false) ∧
      (evalWithAnswerFn A (SigGolfCandidate.Research.SharedForest.sharedDigestSearch rho m start fuel) = none → ∀ c', start ≤ c' → c' < start + fuel →
          SigGolfCandidate.Research.SharedForest.digestAccepted (evalWithAnswerFn A (digest rho m (BitVec.ofNat 32 c'))) = false) := by
  intro fuel
  induction fuel with
  | zero =>
      intro start
      refine ⟨fun c N h => ?_, fun _ c' h1 h2 => by omega⟩
      simp [SigGolfCandidate.Research.SharedForest.sharedDigestSearch] at h
  | succ fuel ih =>
      intro start
      rw [SigGolfCandidate.Research.SharedForest.sharedDigestSearch, evalWithAnswerFn_bind]
      by_cases hadm : SigGolfCandidate.Research.SharedForest.digestAccepted (evalWithAnswerFn A (digest rho m (BitVec.ofNat 32 start))) = true
      · rw [if_pos hadm, evalWithAnswerFn_pure]
        refine ⟨fun c N h => ?_, fun h => by cases h⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact ⟨start, le_rfl, by omega, h.1.symm, fun c' h1 h2 => by omega⟩
      · rw [if_neg hadm]
        have hrej : SigGolfCandidate.Research.SharedForest.digestAccepted (evalWithAnswerFn A (digest rho m (BitVec.ofNat 32 start))) = false := by
          simpa using hadm
        obtain ⟨ih1, ih2⟩ := ih (start + 1)
        refine ⟨fun c N h => ?_, fun h c' h1 h2 => ?_⟩
        · obtain ⟨k, hk1, hk2, hk3, hk4⟩ := ih1 c N h
          refine ⟨k, by omega, by omega, hk3, fun c' h1 h2 => ?_⟩
          by_cases hc : c' = start
          · subst hc; exact hrej
          · exact hk4 c' (by omega) h2
        · by_cases hc : c' = start
          · subst hc; exact hrej
          · exact ih2 h c' (by omega) (by omega)
theorem trialRows_queried (A : Answers) (published : SigGolfCandidate.T3.Cache) (request : Security.Request)
    (hc : request.cache = published) (X : HashInput)
    (hX : X ∈ trialRows (honestNonce A request.message) request.message (LargeResidual.Paired.signDigest A request.message)) :
    (.inl (.inr X) : SigGolfCandidate.T3.Spec.Domain) ∈ queried A (PairedOuter.FullGame.authenticatedSign published request) := by
  set rho := honestNonce A request.message with hrho
  have hsd : LargeResidual.Paired.signDigest A request.message =
      evalWithAnswerFn A (SigGolfCandidate.Research.SharedForest.sharedDigestSearch rho request.message 0 WCT9.digestAttemptLimit) := rfl
  have hq : (.inl (.inr X) : SigGolfCandidate.T3.Spec.Domain) ∈
      queried A (SigGolfCandidate.Research.SharedForest.sharedDigestSearch rho request.message 0 WCT9.digestAttemptLimit) := by
    obtain ⟨r1, r2⟩ := search_result A rho request.message WCT9.digestAttemptLimit 0
    cases hfound : LargeResidual.Paired.signDigest A request.message with
    | none =>
        rw [hfound] at hX
        unfold trialRows at hX
        rw [List.mem_map] at hX
        obtain ⟨k, hk, rfl⟩ := hX
        rw [List.mem_range] at hk
        dsimp only at hk
        exact search_queried A rho request.message WCT9.digestAttemptLimit 0 k (Nat.zero_le _) (by omega)
          (fun c' _ h2 => r2 (hsd ▸ hfound) c' (Nat.zero_le _) (by omega))
    | some found =>
        obtain ⟨c, N⟩ := found
        rw [hfound] at hX
        unfold trialRows at hX
        rw [List.mem_map] at hX
        obtain ⟨k, hk, rfl⟩ := hX
        rw [List.mem_range] at hk
        dsimp only at hk
        obtain ⟨k0, -, hk0, hck, hrej⟩ := r1 c N (hsd ▸ hfound)
        have hlim : WCT9.digestAttemptLimit = 2 ^ 21 := rfl
        have hct : c.toNat = k0 := by
          rw [hck, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
        exact search_queried A rho request.message WCT9.digestAttemptLimit 0 k (Nat.zero_le _) (by omega)
          (fun c' _ h2 => hrej c' (Nat.zero_le _) (by omega))
  unfold PairedOuter.FullGame.authenticatedSign
  rw [queried_bind, SigGolfCandidate.T3.Security.BPB.queried_privateMac]
  apply List.mem_append_right
  rw [if_pos hc]
  change (.inl (.inr X) : SigGolfCandidate.T3.Spec.Domain) ∈ queried A (SigGolfCandidate.Research.SharedForest.signPayload request.cache request.message)
  unfold SigGolfCandidate.Research.SharedForest.signPayload
  rw [queried_bind, SigGolfCandidate.T3.Security.BPB.queried_privateNonce]
  apply List.mem_append_right
  rw [queried_bind]
  exact List.mem_append_left _ hq
theorem seen_events_self (U : Finset HashInput) (events : List FirstHit.QueryEvent) (st : RouterState)
    (b : LazyPrivate.State) (X : HashInput) (y : HashOutput) (he : (⟨b, .inl (.inr X), y⟩ : FirstHit.QueryEvent) ∈ events) :
    X ∈ (events.foldl (routerEvent U) st).seen := by
  induction events generalizing st with
  | nil => cases he
  | cons e rest ih =>
      rw [List.foldl_cons]
      rcases List.mem_cons.mp he with rfl | he
      · exact seen_events_mono' U rest _ X (seen_event_self U st b X y)
      · exact ih _ he
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
end
namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord WCoord)
open SigGolfCandidate.T3.Security.LargeCoupling (honestNonce)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _

theorem router_covered_of_clear (U : Finset HashInput) (A : Answers) (q : Nat)
    (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep) (verdict : List FirstHit.QueryEvent)
    (N : HashOutput)
    (hr : (routerFold U A published steps verdict).reused ≠ true)
    (hclear : ∀ (k : Fin 9) (t : Fin 6) (s : Fin 4),
      s.val = 4-WCT9.wordDigit (forestRank N k.val) t →
      LargeResidual.Paired.Clear A (monitorRun U A q published steps verdict).known
        (Extract.Paired.honestInput A (.wctChain (WCT9.digestIndex N) k.val
          (rawChildFromOutput N k).val t.val s.val))
        (A (.inl (.inr (Extract.Paired.honestInput A (.wctChain (WCT9.digestIndex N) k.val
          (rawChildFromOutput N k).val t.val s.val)))))) :
    ClaudeWCT.Bank.Paired.Covered (routerFold U A published steps verdict).exposures N := by
  apply (ClaudeWCT.Bank.Paired.covered_source _ _).2
  have hposCov : ∀ (k : Fin 9) (tt : Fin 6), 1 ≤ WCT9.wordDigit (forestRank N k.val) tt →
      ∃ x ∈ (routerFold U A published steps verdict).exposures,
        WCT9.digestIndex x = WCT9.digestIndex N ∧
        rawChildFromOutput x k = rawChildFromOutput N k ∧
        WCT9.wordDigit (forestRank N k.val) tt ≤ WCT9.wordDigit (forestRank x k.val) tt := by
    intro k tt hu1
    have hu3 := WCT9.wordDigit_le_four (forestRank N k.val) tt
    let a : CanonGraph.WctAddr := (LargeResidual.digestIndex N,k,rawChildFromOutput N k,tt)
    let s : Fin 4 := ⟨4-WCT9.wordDigit (forestRank N k.val) tt,by omega⟩
    have hcl := hclear k tt s rfl
    have hb : Extract.Paired.Bounded (CanonGraph.Node.wctChain (a,s)).toPos := by
      change (CanonGraph.Node.wctChain (a,s)).toPos.Bounded
      exact CanonGraph.toPos_bounded _
    have hk := hcl.2.1 (CanonGraph.Node.wctChain (a,s)) hb (posOf_honest_wctChain A a s)
      (LargeResidual.wctItem a s.val) (if WCT9.ftsIsG a.2.2.2.val then 0 else 3) rfl
      (slotValue_honest_wctChain A a s)
    obtain ⟨p',hpp',hd⟩ := known_wctItem (by omega : s.val≤4) hk
    rcases hd with hkg | hkd
    · exact (keygen_not_wct a p' hkg).elim
    have hkd' : LargeResidual.wctItem a p' ∈
        (steps.foldl (Monitor.step U A q published) Monitor.initial).disclosed := by
      unfold monitorRun at hkd
      rwa [disclosed_events] at hkd
    rcases disclosed_steps_mem U A q published steps Monitor.initial _ hkd' with h0 | ⟨r,o,e,hmem,hdis⟩
    · cases h0
    unfold signDisclosed at hdis
    split_ifs at hdis with hcr
    · rcases hsr : LargeResidual.Paired.signDigest A r.message with _ | ⟨c',N'⟩
      · rw [hsr] at hdis; cases hdis
      · rw [hsr] at hdis
        dsimp only at hdis
        split_ifs at hdis with hok
        · obtain ⟨hidx,hchild,hpos⟩ := wctItem_mem_signItems A N' a p' (by omega) hdis
          have hd3 := WCT9.wordDigit_le_four (forestRank N' k.val) tt
          rcases covered_fold U A published steps verdict r o e hmem hcr c' N' hsr with hx | hx
          · refine ⟨N',hx,?_,hchild.symm,?_⟩
            · exact (congrArg Fin.val hidx).symm
            · dsimp [a] at hpos
              dsimp [s] at hpp'
              omega
          · exact (hr hx).elim
        · cases hdis
    · cases hdis
  intro k tt
  by_cases hu : 1 ≤ WCT9.wordDigit (forestRank N k.val) tt
  · exact hposCov k tt hu
  · obtain ⟨t',ht'⟩ := exists_pos_digit (forestRank N k.val)
    obtain ⟨x,hx,hidx,hch,-⟩ := hposCov k t' ht'
    exact ⟨x,hx,hidx,hch,by omega⟩
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord WCoord trialRows)
open SigGolfCandidate.T3.Security.LargeResidual (IsDigestRow)
open SigGolfCandidate.T3.Security.LargeCoupling (honestNonce record_events_known chargeOf EventsAgree)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _
theorem cert_of_clean_of_checker (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (z : PairedOuter.PaddedGame.TraceResult × Answers) (hz : z ∈ (PairedSeccLaw.completedExperiment adversary q hq).support)
    (hwin : QueryRecorded.CleanWin q z.1) (hno : ¬Contact adversary q z)
    (hchecker : ∀ (published : SigGolfCandidate.T3.Cache) (pk : Digest)
      (log : QueryLog Final.Paired.Requests) (forgery : Final.Paired.ForgeryP),
      evalWithAnswerFn z.2 keygen = (pk,published) →
      (∀ entry ∈ log, entry.2 = evalWithAnswerFn z.2 (PairedOuter.FullGame.authenticatedSign published entry.1)) →
      evalWithAnswerFn z.2 (Final.Paired.checkForgeryP pk log forgery) = true →
      AllClear z.2 (LargeResidual.Paired.Known (Disclosed z.2 published))
        (queried z.2 (Final.Paired.checkForgeryP pk log forgery)) →
      BankFresh z.2 published log (queried z.2 (Final.Paired.checkForgeryP pk log forgery))) :
    CertR adversary q (QueryRecorded.recordedTrace z.1) z.2 := by
  set U := Wots.PairedReference.referenceInputs adversary with hUdef
  obtain ⟨hz1, hagree⟩ := PairedSeccLaw.completed_agrees adversary q hq z hz
  change ¬ (∀ g t c, TaggedSplit adversary (QueryRecorded.recordedTrace z.1) g t c →
    (monitorRun U z.2 q g.value.2 t.steps c.events).contact = true) at hno
  simp only [not_forall] at hno
  obtain ⟨g, t, c, hsplit, hmon⟩ := hno
  have hmon' : (monitorRun U z.2 q g.value.2 t.steps c.events).contact = false := by simpa using hmon
  intro g' t' c' hsplit'
  obtain ⟨rfl, rfl, rfl⟩ := taggedSplit_unique hsplit hsplit'
  obtain ⟨hg, ht, hc, hres⟩ := hsplit
  have hu := taggedRecord_untag _ _ _ t ht
  have hgt : SourceReplay.Extends g.state t.state :=
    SourceReplay.run_extends _ _ (t.untag.value, t.untag.state) (FirstHit.recorded_support _ _ _ hu)
  have htc : SourceReplay.Extends t.state c.state :=
    SourceReplay.run_extends _ _ (c.value, c.state) (FirstHit.recorded_support _ _ _ hc)
  have hstate : (QueryRecorded.recordedTrace z.1).state = c.state := by rw [hres]
  have hac : ∀ input answer, SourceReplay.known c.state input = some answer → z.2 input = answer := by
    intro input answer h
    apply hagree
    rw [← hstate] at h
    exact h
  have hcval : c.value = true := by
    have h1 : (QueryRecorded.recordedTrace z.1).value = c.value := by rw [hres]
    rw [← h1]; exact hwin.1
  have hgen : evalWithAnswerFn z.2 keygen = g.value :=
    (SourceReplay.resolves_of_run keygen SourceReplay.keygen_hashOnly (∅, ∅) (g.value, g.state)
      (FirstHit.recorded_support _ _ _ hg)).eval z.2
        (fun input answer hk => hac input answer (SourceReplay.known_mono _ _ (hgt.trans htc) hk))
  have husplit : Wots.PairedReference.GameSplit adversary (QueryRecorded.recordedTrace z.1) g t.untag c :=
    ⟨hg,hu,hc,hres⟩
  obtain ⟨_,hpk,hcache,hlogged,hverdictValue⟩ := husplit.facts z.2 hagree hwin.1
  obtain ⟨forgery,hf,hcheck,hqsub⟩ := Wots.PairedReference.Ref.verdict_accepts z.2 g.value.1 t.value hverdictValue
  have hlen : t.value.2.length ≤ 2^32 := by
    change evalWithAnswerFn z.2 (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker g.value.1 t.value) = true at hverdictValue
    unfold PairedOuter.GameWith.verdict at hverdictValue
    rw [hf,evalWithAnswerFn_bind,evalWithAnswerFn_pure] at hverdictValue
    simp only [Bool.and_eq_true,decide_eq_true_eq] at hverdictValue
    exact hverdictValue.1
  have hsub : ∀ X, (.inl (.inr X) : Spec.Domain) ∈ queried z.2 (Final.Paired.checkForgeryP g.value.1 t.value.2 forgery) →
      ∃ prior, (⟨prior,.inl (.inr X),z.2 (.inl (.inr X))⟩ : FirstHit.QueryEvent) ∈ c.events := by
    intro X hX
    exact SigGolfCandidate.T3.Security.PaddedExtraction.public_occurrence _
      (Wots.PairedReference.Ref.verdict_hashOnly _ _) t.state c hc z.2 hac X (hqsub _ hX)
  have hsteps : StepsAgree z.2 t.steps := by
    intro step hstep event heq hi
    have hev : event ∈ t.untag.events := by
      change event ∈ t.steps.flatMap TaggedStep.events
      exact List.mem_flatMap.mpr ⟨step, hstep, by rw [heq]; exact List.mem_singleton_self _⟩
    exact hac _ _ (SourceReplay.known_mono _ _ htc (record_events_known _ _ _ hu event hev hi))
  have hverdict : EventsAgree z.2 c.events := fun event he hi =>
    hac _ _ (record_events_known _ _ _ hc event he hi)
  have hcalls : (monitorRun U z.2 q g.value.2 t.steps c.events).calls ≤ q := by
    have hcost := PairedOuter.PaddedGame.traced_cost_coherent adversary q hq z.1 hz1
    have hle := monitorRun_calls_le U z.2 q g.value.2 t.steps c.events
    have hev : (QueryRecorded.recordedTrace z.1).events = g.events ++ (t.events ++ c.events) := by rw [hres]
    have htot : chargeOf (QueryRecorded.recordedTrace z.1).events = z.1.2.2.base.source.1 := hcost.symm
    rw [hev] at htot
    have hw := hwin.2.1
    have hte : t.events = t.steps.flatMap TaggedStep.events := rfl
    simp only [chargeOf, List.map_append, List.sum_append] at htot hle
    rw [hte] at htot
    omega
  have hXU : ∀ X prior, (⟨prior, .inl (.inr X), z.2 (.inl (.inr X))⟩ : FirstHit.QueryEvent) ∈ c.events → X ∈ U := by
    intro X prior hev
    have hmem := List.mem_append_right g.events (List.mem_append_right t.events hev)
    have hev' : (QueryRecorded.recordedTrace z.1).events = g.events ++ (t.events ++ c.events) := by rw [hres]
    rw [← hev'] at hmem
    exact trace_inputs adversary q hq z.1 hz1 _ hmem X rfl
  have hclearV : ∀ X prior, (⟨prior, .inl (.inr X), z.2 (.inl (.inr X))⟩ : FirstHit.QueryEvent) ∈ c.events →
      LargeResidual.Paired.Clear z.2 (monitorRun U z.2 q g.value.2 t.steps c.events).known X (z.2 (.inl (.inr X))) := by
    intro X prior hev
    have hseen := events_seen U z.2 q c.events _ hmon' _ hev X rfl
    exact monitorRun_clear U z.2 q g.value.2 t.steps c.events hsteps hverdict hmon' hcalls X hseen
      (hXU X prior hev)
  have hclear : AllClear z.2 (LargeResidual.Paired.Known (Disclosed z.2 g.value.2))
      (queried z.2 (Final.Paired.checkForgeryP g.value.1 t.value.2 forgery)) := by
    intro X hX
    obtain ⟨prior,hev⟩ := hsub X hX
    exact (hclearV X prior hev).mono fun d hd =>
      monitorRun_known U z.2 q g.value.2 t.steps c.events d hd
  obtain ⟨m,rho,counter,N,hNz,hdq,hS,hslots,hnot⟩ := hchecker g.value.2 g.value.1 t.value.2 forgery hgen hlogged hcheck hclear
  refine ⟨hcval, hmon', hcalls, ?_⟩
  set st := routerFold U z.2 g.value.2 t.steps c.events with hst
  have hlog : t.value.2 = stepLog t.steps := taggedRecord_log _ _ _ t ht
  have halive : st.exposures.length ≤ CaseC.horizon := by
    have h1 : st.exposures.length ≤ signCount t.steps := exposures_fold_le U z.2 g.value.2 t.steps c.events
    rw [signCount_eq_length, ← hlog] at h1
    have : CaseC.horizon = 2 ^ 32 := rfl
    omega
  refine ⟨halive, ?_⟩
  by_cases hr : st.reused = true
  · exact Or.inl hr
  right
  set Xs := pad64 (digestInput (rho) m (counter)) with hXs
  have hXsU : Xs ∈ U := by
    obtain ⟨prior, hev⟩ := hsub _ hdq
    exact hXU Xs prior hev
  have hXsd : IsDigestRow Xs := ⟨rho, m, counter, rfl⟩
  have hnotrial : Xs ∉ (t.steps.foldl (routerStep U z.2 (honestNonce z.2) g.value.2) LargeResidual.RouterState.initial).trials := by
    intro hm
    rcases trials_steps U z.2 g.value.2 t.steps LargeResidual.RouterState.initial Xs hm with h0 | ⟨r, o, e, hmem, hcr, hrow⟩
    · cases h0
    · have hq' := trialRows_queried z.2 g.value.2 r hcr Xs hrow
      have hlogm : (⟨r, o⟩ : (r : Final.Paired.Requests.Domain) × Final.Paired.Requests.Range r) ∈ t.value.2 := by
        rw [hlog]; exact sign_mem_stepLog hmem
      exact hnot _ hlogm hq'
  have hansSteps : ∀ s ∈ t.steps, ∀ e, s = .world e → ∀ b y, e = ⟨b, .inl (.inr Xs), y⟩ → y = N := by
    intro s hs e hse b y he
    have h1 := hsteps s hs e hse (by rw [he]; trivial)
    rw [he] at h1
    exact h1.symm.trans hNz
  have hansV : ∀ e ∈ c.events, ∀ b y, e = ⟨b, .inl (.inr Xs), y⟩ → y = N := by
    intro e he b y hee
    have h1 := hverdict e he (by rw [hee]; trivial)
    rw [hee] at h1
    exact h1.symm.trans hNz
  have hbirth : (Xs, N) ∈ st.births := by
    have hI := birthInv_steps U z.2 g.value.2 Xs N hXsU hXsd t.steps hansSteps LargeResidual.RouterState.initial hnotrial
      (fun h => by cases h)
    have hI2 := birthInv_events U Xs N hXsU hXsd c.events hansV _ hnotrial hI
    obtain ⟨prior, hev⟩ := hsub _ hdq
    apply hI2
    exact seen_events_self U c.events _ prior Xs _ hev
  refine ⟨(Xs, N), hbirth, hS, ?_⟩
  apply router_covered_of_clear U z.2 q g.value.2 t.steps c.events N hr
  intro k tt ss hss
  obtain ⟨prior,hev⟩ := hsub _ (hslots k tt ss hss)
  exact hclearV _ prior hev
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsLeafCongr ====
section

/-! # Leaf congruence (campaign X1 stage B, step B3)

The honest part of the WOTS reference game is unchanged when a leaf `L`'s family coefficients and its chain
rows below the signed digits change, as long as every chain of `L` keeps its frontier value (its honest value at
the signed digit) and its rows from the digit on (`LeafCongr`). This is the honest-side input of the seed-test
reduction: the leaf's step-0 rows can be programmed at the family seeds without the honest signer noticing. -/

namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace Leaf
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask

/-- Queries outside leaf `L`'s chain rows and family coefficient cells (every layer; top leaves since T8D). -/
def LeafOut (L : LeafAddr) : Spec.Domain → Prop
  | .inl (.inr input) => ∀ c step value, c < chainCount L.lay → step < 7 → input ≠ chainRowW ⟨L, c⟩ step value
  | .inr (.inl tweak) => ∀ j, j < WCT9.famCount L.lay →
      tweak ≠ WCT9.lowerSeedHeader L.lay L.tree (WCT9.famOrdinal L.lay L.leaf j / 2)
  | _ => True

/-- Chain addresses whose `Untouched` classes cover `LeafOut L`: the leaf's chains and, per coefficient cell, the
leaf-0 address whose seed tweak is that cell. -/
def coverAddrs (L : LeafAddr) : List ChainAddr :=
  (List.range (chainCount L.lay)).map (fun c => ⟨L, c⟩) ++
    (List.range (WCT9.famCount L.lay)).map (fun j => ⟨⟨L.lay, L.tree, 0⟩, 2 * (WCT9.famOrdinal L.lay L.leaf j / 2)⟩)

theorem respects_cover {α : Type} {p : M α} (h : ∀ c, Respects (Untouched c) p) :
    ∀ cs : List ChainAddr, Respects (fun q => ∀ c ∈ cs, Untouched c q) p
  | [] => Respects.mono' (h ⟨⟨0, 0, 0⟩, 0⟩) (fun _ _ c hc => absurd hc List.not_mem_nil)
  | c :: cs => Respects.mono' (Respects.inter (h c) (respects_cover h cs)) (fun q hq c' hc' => by
      rcases List.mem_cons.mp hc' with rfl | hc'
      · exact hq.1
      · exact hq.2 c' hc')

theorem leafOut_of_cover {L : LeafAddr} {q : Spec.Domain} (h : ∀ c ∈ coverAddrs L, Untouched c q) :
    LeafOut L q := by
  rcases q with (coin | input) | (tweak | other)
  · trivial
  · intro c step value hc hs heq
    have hu := h ⟨L, c⟩ (List.mem_append_left _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩)) step value
      (by omega)
    unfold chainRowW WCT9.chainInputW at heq
    split at heq
    · exact hu.2 heq
    · exact hu.1 heq
  · intro j hj heq
    apply h ⟨⟨L.lay, L.tree, 0⟩, 2 * (WCT9.famOrdinal L.lay L.leaf j / 2)⟩
      (List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))
    show tweak = seedTweak _
    rw [heq]
    unfold seedTweak WCT9.lowerSeedHeader
    simp only
    rw [show 2 * (WCT9.famOrdinal L.lay L.leaf j / 2) / 2 = WCT9.famOrdinal L.lay L.leaf j / 2 by omega]
  · trivial

/-- A program respecting every chain's `Untouched` class respects `LeafOut L`. -/
theorem respects_leafOut {α : Type} {p : M α} (h : ∀ c, Respects (Untouched c) p) (L : LeafAddr) :
    Respects (LeafOut L) p :=
  Respects.mono' (respects_cover h (coverAddrs L)) fun _ hq => leafOut_of_cover hq

section Programs
variable (L : LeafAddr)
theorem respectsL_signForest (index : Nat) (output : HashOutput) :
    Respects (LeafOut L) (ClaudeWCT.WCT9.signForest index output) :=
  respects_leafOut (fun c => ClaudeWCT.WCT9.Wots.Mask.respects_signForest c index output) L
theorem respectsL_digestSearch (rho : Digest) (message : Message) :
    ∀ fuel counter, Respects (LeafOut L) (ClaudeWCT.WCT9.digestSearch rho message counter fuel) := by
  intro fuel
  induction fuel with
  | zero => intro counter; exact Respects.pure' _
  | succ fuel ih =>
      intro counter
      simp only [ClaudeWCT.WCT9.digestSearch]
      refine Respects.bind (respects_leafOut (fun c => respects_digest c _ _ _) L) fun output => ?_
      split
      · exact Respects.pure' _
      · exact ih _
theorem respectsL_privateMac (region : Region) : Respects (LeafOut L) (privateMac region) :=
  respects_leafOut (fun c => respects_privateMac c region) L
theorem respectsL_privateNonce (message : Message) : Respects (LeafOut L) (privateNonce message) :=
  respects_leafOut (fun c => respects_privateNonce c message) L
theorem respectsL_mask (level index : Nat) : Respects (LeafOut L) (mask level index) :=
  respects_leafOut (fun c => respects_mask c level index) L
theorem respectsL_buildLevels (tag lay tree h : Nat) (leaves : List Digest) (ht : tag % 256 ≠ 1) :
    Respects (LeafOut L) (buildLevels tag lay tree h leaves) :=
  respects_leafOut (fun c => respects_buildLevels c tag lay tree h leaves ht) L
theorem respectsL_leafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    Respects (LeafOut L) (leafHash lay tree leaf ends) :=
  respects_leafOut (fun c => respects_leafHash c lay tree leaf ends) L
theorem respectsL_layerCounterSearch (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (fuel counter : Nat) :
    Respects (LeafOut L) (WCT9.layerCounterSearch lay tree leaf msg counter fuel) :=
  respects_leafOut (fun c => respects_layerCounterSearch c lay tree leaf msg fuel counter) L
theorem leafOut_ftsQuery {index : Nat} {q : SigGolfCandidate.T3.Spec.Domain} (h : WCT9.FtsQuery index q) :
    LeafOut L q :=
  leafOut_of_cover fun c _ => ClaudeWCT.WCT9.Wots.ftsQuery_untouched c h
/-- Chain rows outside `L` (another leaf, or a chain index beyond the leaf's chains). -/
theorem leafOut_chainInput {lay : Layer} {tree leaf i s : Nat} (v : Digest) (hi : i < 2 ^ 24) (hs : s < 256)
    (hna : ¬(LeafAlias lay tree leaf L ∧ i < chainCount L.lay)) :
    LeafOut L (.inl (.inr (pad64 (WCT9.chainInputW lay tree leaf i s v)))) := by
  intro c step value hc hstep heq
  rw [pad64_chainInputW] at heq
  have hc' : c < 2 ^ 24 := by have := chainCount_le L.lay; simp only [Nat.reducePow]; omega
  obtain ⟨hal, rfl, -, -⟩ := chainInputW_eq_chainRowW (a := ⟨L, c⟩) hi hc' hs (by omega) heq
  exact hna ⟨hal, hc⟩
/-- Private cells of other layers or of non-zero tags are outside `L`. -/
theorem leafOut_header {t l tr p ix : Nat} (h : t % 256 ≠ 0 ∨ l % 256 ≠ L.lay.val) :
    LeafOut L (.inr (.inl (header t l tr p ix))) := by
  intro j _ heq
  unfold WCT9.lowerSeedHeader at heq
  have hf := header_fields heq
  have hL : L.lay.val % 256 = L.lay.val := Nat.mod_eq_of_lt (lt_trans L.lay.isLt (by decide))
  rcases h with h | h
  · exact h (by simpa using hf.1)
  · exact h (hf.2.1.trans hL)
theorem respectsL_topPath (cache : Cache) (leaf : Nat) : Respects (LeafOut L) (topPath cache leaf) := by
  unfold topPath
  exact Respects.mapM _ _ fun level _ => Respects.bind (respectsL_mask L _ _) fun _ => Respects.pure' _
/-! C2/C3 (FULL): the lower trees and the chain-0 high half. -/
theorem leafOut_of_hdr (input : HashInput) (h : BitVec 128)
    (hblock : SigGolfCandidate.T3M.Extract.hdrBlock input = SphincsSecurity.bytesLE 16 h)
    (htag : ∀ (l : Layer) tr leaf i step, step < 7 → h ≠ chainHeader l tr leaf i step) :
    LeafOut L (.inl (.inr input)) := by
  intro c step value _ hs heq
  have hb : SigGolfCandidate.T3M.Extract.hdrBlock (chainRowW ⟨L, c⟩ step value) =
      SphincsSecurity.bytesLE 16 (chainHeader L.lay L.tree L.leaf c step) :=
    WCT9.chainInputW_header _ _ _ _ _ _
  rw [heq, hb] at hblock
  exact htag _ _ _ _ _ hs (SphincsSecurity.bytesLE_injective hblock).symm
theorem leafOut_of_length (input : HashInput) (hl : input.length ≠ 64) : LeafOut L (.inl (.inr input)) := by
  intro c step value _ _ heq
  apply hl
  rw [heq, chainRowW_length]
theorem foldOK_leafOut (lay tree h : Nat) (h7 : lay ≠ 0 → h ≤ 7) : Mask.FoldOK (LeafOut L) lay tree h := by
  intro level i left right hlev hi
  refine leafOut_of_hdr L _ _ (SigGolfCandidate.T3M.Extract.hdrBlock_block4 left _ 0 right)
    fun l tr leaf c step hs => Mask.merkleTweak_ne_chainHeader ?_ l tr leaf c step hs
  by_cases h0 : lay = 0
  · exact Or.inl h0
  · exact Or.inr (Mask.lowerHeap_lt' hlev (h7 h0) hi)
theorem respectsL_lowerLevels (lay tree h : Nat) (h7 : lay ≠ 0 → h ≤ 7) (leaves : List Digest)
    (hlen : leaves.length ≤ 2 ^ h) : Respects (LeafOut L) (WCT9.lowerLevels lay tree h leaves) :=
  Mask.respects_lowerLevels' (foldOK_leafOut L lay tree h h7) leaves hlen
theorem respectsL_buildLevelsBelowW (tag lay tree h : Nat) (h7 : lay ≠ 0 → h ≤ 7) (leaves : List Digest)
    (hlen : leaves.length ≤ 2 ^ h) : Respects (LeafOut L) (WCT9.buildLevelsBelow tag lay tree h leaves) :=
  Mask.respects_buildLevelsBelow' (foldOK_leafOut L lay tree h h7) tag leaves hlen
theorem respectsL_lowerLeafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) (hlen : 4 ≤ ends.length) :
    Respects (LeafOut L) (WCT9.lowerLeafHash lay tree leaf ends) :=
  Mask.respects_lowerLeafHash' _ _ _ _ (leafOut_of_length L _ (Mask.pad64_long_length
    (SigGolfCandidate.T3.Security.Wots.Enc.leafInput_long lay tree leaf ends hlen)))
end Programs

/-- `T'` agrees with `T` outside `L` and on the other halves of `L`'s coefficient cells. -/
structure LeafAgree (L : LeafAddr) (T T' : Answers) : Prop where
  out : ∀ q, LeafOut L q → T' q = T q
  half : ∀ o, (∃ j, j < WCT9.famCount L.lay ∧ o / 2 = WCT9.famOrdinal L.lay L.leaf j / 2) →
    (∀ j, j < WCT9.famCount L.lay → o ≠ WCT9.famOrdinal L.lay L.leaf j) →
    WCT9.seedHalf (evalWithAnswerFn T' (WCT9.lowerSeedPair L.lay L.tree (o / 2))) o =
      WCT9.seedHalf (evalWithAnswerFn T (WCT9.lowerSeedPair L.lay L.tree (o / 2))) o

/-- Leaf congruence: `LeafAgree`, plus agreement on the rows of `L`'s chains from their signed digits on and on
every chain's frontier value. -/
structure LeafCongr (L : LeafAddr) (T T' : Answers) : Prop extends LeafAgree L T T' where
  rows : ∀ c, c < chainCount L.lay → ∀ s v, depth T ⟨L, c⟩ ≤ s → s < 256 →
    T' (.inl (.inr (chainRowW ⟨L, c⟩ s v))) = T (.inl (.inr (chainRowW ⟨L, c⟩ s v)))
  front : ∀ c, c < chainCount L.lay → frontierValue T' ⟨L, c⟩ = frontierValue T ⟨L, c⟩

section Agree
variable {L : LeafAddr} {T T' : Answers} (hC : LeafAgree L T T') (hLleaf : L.leaf < 2 ^ 24)
include hC

theorem eval_out {α : Type} {p : M α} (h : Respects (LeafOut L) p) :
    evalWithAnswerFn T' p = evalWithAnswerFn T p :=
  (h.eval_eq hC.out)
theorem queried_out {α : Type} {p : M α} (h : Respects (LeafOut L) p) :
    SourceReplay.queried T' p = SourceReplay.queried T p :=
  (h.queried_eq hC.out)
theorem eval_chain_out {lay : Layer} {tree leaf i : Nat} (hi : i < 2 ^ 24)
    (hna : ¬(LeafAlias lay tree leaf L ∧ i < chainCount L.lay)) {start count : Nat} (hc : start + count ≤ 256)
    (v : Digest) :
    evalWithAnswerFn T' (WCT9.chainW lay tree leaf i start count v) =
      evalWithAnswerFn T (WCT9.chainW lay tree leaf i start count v) := by
  apply eval_out hC
  exact Mask.respects_chainW' _ _ _ _ _ _ _ fun step value _ hhi =>
    leafOut_chainInput L value hi (by omega) hna

theorem honestForest_out (index : Nat) : Extract.honestTop T' index = Extract.honestTop T index := by
  rw [Extract.honestTop_eq_wct9, Extract.honestTop_eq_wct9]
  exact ClaudeWCT.WCT9.Wots.honestTop_congr (fun _ hq => hC.out _ (leafOut_ftsQuery L hq))
end Agree

section Congr
variable {L : LeafAddr} {T T' : Answers} (hC : LeafCongr L T T') (hLleaf : L.leaf < 2 ^ 24)
include hC
end Congr
end Leaf
end ClaudeWCT.W9.T3.Security.Wots

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Leaf
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.W9.T3M SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open ClaudeWCT.W9.T3.Security.Wots.Leaf
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

structure Congr (messages : LeafAddr → WCT9.LayerMsg) (L : LeafAddr) (T T' : Answers) : Prop
    extends LeafAgree L T T' where
  rows : ∀ c, c < chainCount L.lay → ∀ s v, CanonicalRef.depth T messages ⟨L, c⟩ ≤ s → s < 256 →
    T' (.inl (.inr (chainRowW ⟨L,c⟩ s v)))=T (.inl (.inr (chainRowW ⟨L,c⟩ s v)))
  front : ∀ c, c < chainCount L.lay →
    CanonicalRef.frontierValue T' messages ⟨L,c⟩=CanonicalRef.frontierValue T messages ⟨L,c⟩

variable {messages : LeafAddr → WCT9.LayerMsg} {L : LeafAddr} {T T' : Answers}

theorem searchOf_congr (hC : LeafAgree L T T') (K : LeafAddr) (remaining : Nat) :
    CanonicalRef.searchOf T' messages K remaining=CanonicalRef.searchOf T messages K remaining := by
  unfold CanonicalRef.searchOf
  exact eval_out hC (respects_leafOut (fun a => CanonicalRef.Mask.respects_layerCounterSearchAt a _ _ _ _ _ _ _) L)

theorem referenceSearch_congr (hC : LeafAgree L T T') (K : LeafAddr) :
    CanonicalRef.referenceSearch T' messages K=CanonicalRef.referenceSearch T messages K :=
  CanonicalRef.referenceSearch_congr (fun K r _ => searchOf_congr hC K r) K

theorem depth_congr (hC : LeafAgree L T T') (a : ChainAddr) :
    CanonicalRef.depth T' messages a=CanonicalRef.depth T messages a := by
  unfold CanonicalRef.depth CanonicalRef.referenceDigits
  rw [referenceSearch_congr hC]

section Congr
variable (hC : Congr messages L T T') (hLleaf : L.leaf < 2^24)
include hC
include hLleaf in
/-- `L`'s own chains: from the frontier on, the rows agree. -/
theorem eval_chainL {c count : Nat} (hc : c < chainCount L.lay) (hd : CanonicalRef.depth T messages ⟨L, c⟩ ≤ count) (hcount : count ≤ 256) :
    evalWithAnswerFn T' (WCT9.chainW L.lay L.tree L.leaf c 0 count (WCT9.wotsSeed T' L.lay L.tree L.leaf c)) =
      evalWithAnswerFn T (WCT9.chainW L.lay L.tree L.leaf c 0 count (WCT9.wotsSeed T L.lay L.tree L.leaf c)) := by
  obtain ⟨e, rfl⟩ : ∃ e, count = CanonicalRef.depth T messages ⟨L, c⟩ + e := ⟨count - CanonicalRef.depth T messages ⟨L, c⟩, by omega⟩
  have hd' : CanonicalRef.depth T' messages ⟨L, c⟩ = CanonicalRef.depth T messages ⟨L, c⟩ := depth_congr hC.toLeafAgree ⟨L, c⟩
  rw [eval_chainW_add', eval_chainW_add' T, Nat.zero_add]
  have hf := hC.front c hc
  unfold CanonicalRef.frontierValue honestChainValueW at hf
  simp only at hf
  rw [hd'] at hf
  rw [hf]
  refine Respects.eval_eq (S := fun q => T' q = T q) ?_ (fun q hq => hq)
  refine Mask.respects_chainW' _ _ _ _ _ _ _ fun step value hlo hhi => ?_
  rw [pad64_chainInputW]
  exact hC.rows c hc step value hlo (by omega)
end Congr
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Leaf
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsLeafProg ====
section

/-! # Leaf decomposition of the rest tables (campaign X1 stage B, step B3)

`ovL L R (K, f)` overrides leaf `L`'s family coefficient halves (24 top, 17 lower) by `K` and the low halves of the step-0
rows of `L`'s chains by `f`; `rdL` reads them back. The rest-table law is invariant under resampling this part
(`restLaw_resampleL`), and the decomposition leaves every query outside `L` unchanged (`leafAgree_ovL`). -/

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
noncomputable local instance instFintypeCoordinate_wotsLeafProg : Fintype Coordinate := coordinateFintype
namespace Leaf
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high uniform_resample uniform_prod Hidden)
variable {adversary : AdversaryP}

/-- Ordinal of coefficient `j` of leaf `L`. -/
def ordL (L : LeafAddr) (j : Fin (WCT9.famCount L.lay)) : Nat := WCT9.famOrdinal L.lay L.leaf j
/-- Tweak of the cell holding coefficient `j` of leaf `L`. -/
def cellHdr (L : LeafAddr) (j : Fin (WCT9.famCount L.lay)) : BitVec 128 := WCT9.lowerSeedHeader L.lay L.tree (ordL L j / 2)

theorem ordL_pair_lt {L : LeafAddr} (hL : L.leaf < 2 ^ 24) (j : Fin (WCT9.famCount L.lay)) : ordL L j / 2 < 2 ^ 32 :=
  WCT9.famOrdinal_div_lt hL j.isLt
theorem cellHdr_inj {L : LeafAddr} (hL : L.leaf < 2 ^ 24) {j j' : Fin (WCT9.famCount L.lay)} (h : cellHdr L j = cellHdr L j') :
    ordL L j / 2 = ordL L j' / 2 := by
  unfold cellHdr WCT9.lowerSeedHeader at h
  have := (header_fields h).2.2.2.1
  rwa [Nat.mod_eq_of_lt (ordL_pair_lt hL j), Nat.mod_eq_of_lt (ordL_pair_lt hL j')] at this
theorem ordL_inj {L : LeafAddr} {j j' : Fin (WCT9.famCount L.lay)} (h1 : ordL L j / 2 = ordL L j' / 2)
    (h2 : ordL L j % 2 = ordL L j' % 2) : j = j' := by
  apply Fin.ext; unfold ordL WCT9.famOrdinal at h1 h2; omega

/-- The coefficient of `L` stored in half `b` (`0` low, `1` high) of the cell with tweak `tw`, if any. -/
noncomputable def slotAt (L : LeafAddr) (tw : BitVec 128) (b : Nat) : Option (Fin (WCT9.famCount L.lay)) :=
  if h : ∃ j : Fin (WCT9.famCount L.lay), cellHdr L j = tw ∧ ordL L j % 2 = b then some (Classical.choose h) else none
theorem slotAt_some {L : LeafAddr} {tw : BitVec 128} {b : Nat} {j : Fin (WCT9.famCount L.lay)} (h : slotAt L tw b = some j) :
    cellHdr L j = tw ∧ ordL L j % 2 = b := by
  unfold slotAt at h
  split at h
  · rename_i hex
    cases h
    exact Classical.choose_spec hex
  · cases h
theorem slotAt_self {L : LeafAddr} (hL : L.leaf < 2 ^ 24) (j : Fin (WCT9.famCount L.lay)) :
    slotAt L (cellHdr L j) (ordL L j % 2) = some j := by
  have hex : ∃ j' : Fin (WCT9.famCount L.lay), cellHdr L j' = cellHdr L j ∧ ordL L j' % 2 = ordL L j % 2 := ⟨j, rfl, rfl⟩
  unfold slotAt
  rw [dif_pos hex]
  obtain ⟨h1, h2⟩ := Classical.choose_spec hex
  rw [ordL_inj (cellHdr_inj hL h1) h2]
theorem slotAt_none {L : LeafAddr} {tw : BitVec 128} {b : Nat}
    (h : ∀ j : Fin (WCT9.famCount L.lay), cellHdr L j = tw → ordL L j % 2 ≠ b) : slotAt L tw b = none := by
  unfold slotAt
  rw [dif_neg]
  rintro ⟨j, h1, h2⟩
  exact h j h1 h2

/-- Low (`b = 0`) or high half of an output. -/
def halfOf (b : Nat) (output : HashOutput) : Digest := if b = 0 then low output else high output

/-- `priv` with `L`'s coefficient halves replaced by `K`. -/
noncomputable def ovPrivL (L : LeafAddr) (priv : FullGame.FullTable) (K : Fin (WCT9.famCount L.lay) → Digest) : FullGame.FullTable
  | .inl tw => ChainGraph.joinOutput (((slotAt L tw 0).map K).getD (low (priv (.inl tw))))
      (((slotAt L tw 1).map K).getD (high (priv (.inl tw))))
  | .inr x => priv (.inr x)

/-- If `input` is the step-0 row of chain `c < chainCount` of `L` at `v`, that `(c, v)`. -/
noncomputable def zeroOf (L : LeafAddr) (input : HashInput) : Option (Fin (chainCount L.lay) × Digest) :=
  if h : ∃ p : Fin (chainCount L.lay) × Digest, input = chainRowW ⟨L, p.1⟩ 0 p.2 then some (Classical.choose h)
  else none
theorem zeroOf_some {L : LeafAddr} {input : HashInput} {p : Fin (chainCount L.lay) × Digest}
    (h : zeroOf L input = some p) : input = chainRowW ⟨L, p.1⟩ 0 p.2 := by
  unfold zeroOf at h
  split at h
  · rename_i hex
    cases h
    exact Classical.choose_spec hex
  · cases h
theorem chainRowW_zero_inj {L : LeafAddr} {c c' : Nat} {v v' : Digest} (hc : c < chainCount L.lay)
    (h : chainRowW ⟨L, c⟩ 0 v = chainRowW ⟨L, c'⟩ 0 v') (hc' : c' < chainCount L.lay) : c = c' ∧ v = v' := by
  have h1 : c < 2 ^ 24 := by have := chainCount_le L.lay; simp only [Nat.reducePow]; omega
  have h2 : c' < 2 ^ 24 := by have := chainCount_le L.lay; simp only [Nat.reducePow]; omega
  obtain ⟨-, hcc, -, hv⟩ := chainInputW_eq_chainRowW (a := ⟨L, c'⟩) h1 h2 (by omega) (by omega) h
  exact ⟨hcc, hv⟩
theorem zeroOf_chainRow (L : LeafAddr) (c : Fin (chainCount L.lay)) (v : Digest) :
    zeroOf L (chainRowW ⟨L, c⟩ 0 v) = some (c, v) := by
  cases h : zeroOf L (chainRowW ⟨L, c⟩ 0 v) with
  | none =>
      unfold zeroOf at h
      rw [dif_pos ⟨(c, v), rfl⟩] at h
      cases h
  | some p =>
      have he := zeroOf_some h
      obtain ⟨h1, h2⟩ := chainRowW_zero_inj c.isLt he p.1.isLt
      rw [show p = (c, v) from Prod.ext (Fin.ext h1.symm) h2.symm]
theorem zeroOf_none {L : LeafAddr} {input : HashInput} (h : zeroOf L input = none)
    (c : Fin (chainCount L.lay)) (v : Digest) : input ≠ chainRowW ⟨L, c⟩ 0 v := by
  rintro rfl
  rw [zeroOf_chainRow] at h
  cases h

/-- Pairing stage 1: the half of chain `c`'s step-0 row output that the chain uses (`chainHigh lay c 0`, the HIGH
half for a G chain of a lower layer, the low half otherwise). -/
def zh (L : LeafAddr) (c : Nat) : Bool := WCT9.chainHigh L.lay c 0
/-- `pub` with the used halves (`zh`) of `L`'s step-0 rows replaced by `f`. -/
noncomputable def ovPubL (L : LeafAddr) (pub : referenceInputs adversary → HashOutput)
    (f : Fin (chainCount L.lay) → Digest → Digest) : referenceInputs adversary → HashOutput := fun x =>
  match zeroOf L x.val with
  | some p => joinHalf (zh L p.1) (f p.1 p.2) (WCT9.halfOf (!zh L p.1) (pub x))
  | none => pub x

/-- Leaf data: the 17 coefficients and the step-0 row functions of the chains. -/
abbrev LeafData (L : LeafAddr) := (Fin (WCT9.famCount L.lay) → Digest) × (Fin (chainCount L.lay) → Digest → Digest)
noncomputable def ovL (L : LeafAddr) (R : RefTables adversary) (y : LeafData L) : RefTables adversary :=
  (ovPrivL L R.1 y.1, ovPubL L R.2 y.2)
noncomputable def rdL (L : LeafAddr) (R : RefTables adversary) : LeafData L :=
  (fun j => halfOf (ordL L j % 2) (R.1 (.inl (cellHdr L j))),
    fun c v => WCT9.halfOf (zh L c) (R.2 ⟨chainRowW ⟨L, c⟩ 0 v, PrefixGame.chainRowW_mem _ _ _⟩))

theorem ovPubL_zero (L : LeafAddr) (pub : referenceInputs adversary → HashOutput)
    (f : Fin (chainCount L.lay) → Digest → Digest) (c : Fin (chainCount L.lay)) (v : Digest) :
    ovPubL L pub f ⟨chainRowW ⟨L, c⟩ 0 v, PrefixGame.chainRowW_mem _ _ _⟩ =
      joinHalf (zh L c) (f c v) (WCT9.halfOf (!zh L c) (pub ⟨chainRowW ⟨L, c⟩ 0 v, PrefixGame.chainRowW_mem _ _ _⟩)) := by
  unfold ovPubL
  simp only [zeroOf_chainRow]

theorem ovPrivL_inl (L : LeafAddr) (priv : FullGame.FullTable) (K : Fin (WCT9.famCount L.lay) → Digest) (tw : BitVec 128) :
    ovPrivL L priv K (.inl tw) = ChainGraph.joinOutput (((slotAt L tw 0).map K).getD (low (priv (.inl tw))))
      (((slotAt L tw 1).map K).getD (high (priv (.inl tw)))) := rfl
theorem ovPrivL_cell {L : LeafAddr} (hL : L.leaf < 2 ^ 24) (priv : FullGame.FullTable) (K : Fin (WCT9.famCount L.lay) → Digest)
    (j : Fin (WCT9.famCount L.lay)) : halfOf (ordL L j % 2) (ovPrivL L priv K (.inl (cellHdr L j))) = K j := by
  rw [ovPrivL_inl]
  unfold halfOf
  by_cases h0 : ordL L j % 2 = 0
  · rw [if_pos h0]
    have hs := slotAt_self hL j
    rw [h0] at hs
    rw [hs, low, ChainGraph.joinOutput_low]
    rfl
  · rw [if_neg h0]
    have hs := slotAt_self hL j
    rw [show ordL L j % 2 = 1 by omega] at hs
    rw [hs, high, ChainGraph.joinOutput_high]
    rfl

theorem rdL_ovL {L : LeafAddr} (hL : L.leaf < 2 ^ 24) (R : RefTables adversary) (y : LeafData L) :
    rdL L (ovL L R y) = y := by
  obtain ⟨K, f⟩ := y
  unfold rdL ovL
  refine Prod.ext ?_ ?_
  · funext j
    exact ovPrivL_cell hL R.1 K j
  · funext c v
    simp only
    rw [ovPubL_zero, halfOf_joinHalf]

theorem ovL_ovL_rdL {L : LeafAddr} (hL : L.leaf < 2 ^ 24) (R : RefTables adversary) (y : LeafData L) :
    ovL L (ovL L R y) (rdL L R) = R := by
  obtain ⟨priv, pub⟩ := R
  obtain ⟨K, f⟩ := y
  unfold ovL rdL
  simp only
  refine Prod.ext ?_ ?_
  · funext coord
    rcases coord with tw | x
    · show ovPrivL L (ovPrivL L priv K) _ (.inl tw) = priv (.inl tw)
      rw [ovPrivL_inl, ovPrivL_inl]
      have e0 : ((slotAt L tw 0).map (fun j => halfOf (ordL L j % 2) (priv (.inl (cellHdr L j))))).getD
          (low (ChainGraph.joinOutput (((slotAt L tw 0).map K).getD (low (priv (.inl tw))))
            (((slotAt L tw 1).map K).getD (high (priv (.inl tw)))))) = low (priv (.inl tw)) := by
        cases h : slotAt L tw 0 with
        | none => simp only [Option.map_none, Option.getD_none, h, low, ChainGraph.joinOutput_low]
        | some j =>
            obtain ⟨h1, h2⟩ := slotAt_some h
            simp only [Option.map_some, Option.getD_some, halfOf, h2, h1, if_true]
      have e1 : ((slotAt L tw 1).map (fun j => halfOf (ordL L j % 2) (priv (.inl (cellHdr L j))))).getD
          (high (ChainGraph.joinOutput (((slotAt L tw 0).map K).getD (low (priv (.inl tw))))
            (((slotAt L tw 1).map K).getD (high (priv (.inl tw)))))) = high (priv (.inl tw)) := by
        cases h : slotAt L tw 1 with
        | none => simp only [Option.map_none, Option.getD_none, h, high, ChainGraph.joinOutput_high]
        | some j =>
            obtain ⟨h1, h2⟩ := slotAt_some h
            simp only [Option.map_some, Option.getD_some, halfOf, h2, h1]
            rfl
      rw [e0, e1]
      exact ChainGraph.joinOutput_parts _
    · rfl
  · funext x
    dsimp only
    unfold ovPubL
    cases hp : zeroOf L x.val with
    | none => simp only [hp]
    | some p =>
        simp only [hp]
        have hx : x = ⟨chainRowW ⟨L, p.1⟩ 0 p.2, PrefixGame.chainRowW_mem _ _ _⟩ := Subtype.ext (zeroOf_some hp)
        subst hx
        simp only [halfOf_not_joinHalf, joinHalf_halfOf]

noncomputable instance instFintypeLeafData (L : LeafAddr) : Fintype (LeafData L) := by
  unfold LeafData; infer_instance
instance instNonemptyLeafData (L : LeafAddr) : Nonempty (LeafData L) := ⟨(fun _ => 0, fun _ _ => 0)⟩

/-- Resampling `L`'s coefficients and step-0 rows preserves the rest-table law. -/
theorem restLaw_resampleL {L : LeafAddr} (hL : L.leaf < 2 ^ 24) {β : Type} (F : RefTables adversary → PMF β) :
    (restLaw adversary).bind F =
      (restLaw adversary).bind (fun R => (PMF.uniformOfFintype (LeafData L)).bind (fun y => F (ovL L R y))) := by
  have h := uniform_resample (Ω := RefTables adversary) (X := fun _ => LeafData L) (fun _ => 0)
    (fun _ R y => ovL L R y) (fun _ R => rdL L R) (fun R y => rdL_ovL hL R y) (fun R y => ovL_ovL_rdL hL R y)
    (fun _ _ => rfl)
  unfold restLaw
  conv_lhs => rw [← h]
  rw [PMF.bind_bind]
  apply congrArg (PMF.uniformOfFintype (RefTables adversary)).bind
  funext R
  rw [PMF.bind_map]
  rfl

theorem restTable_ovL_zero (L : LeafAddr) (R : RefTables adversary) (y : LeafData L) (c : Fin (chainCount L.lay))
    (v : Digest) : restTable (ovL L R y) (.inl (.inr (chainRowW ⟨L, c⟩ 0 v))) =
      joinHalf (zh L c) (y.2 c v) (WCT9.halfOf (!zh L c) (restTable R (.inl (.inr (chainRowW ⟨L, c⟩ 0 v))))) := by
  rw [PrefixGame.restTable_mem _ _ (PrefixGame.chainRowW_mem _ _ _),
    PrefixGame.restTable_mem _ _ (PrefixGame.chainRowW_mem _ _ _)]
  exact ovPubL_zero L R.2 y.2 c v
theorem restTable_ovL_pub (L : LeafAddr) (R : RefTables adversary) (y : LeafData L) (input : HashInput)
    (h : zeroOf L input = none) :
    restTable (ovL L R y) (.inl (.inr input)) = restTable R (.inl (.inr input)) := by
  by_cases hm : input ∈ referenceInputs adversary
  · rw [PrefixGame.restTable_mem _ _ hm, PrefixGame.restTable_mem _ _ hm]
    show ovPubL L R.2 y.2 ⟨input, hm⟩ = R.2 ⟨input, hm⟩
    unfold ovPubL
    simp only [h]
  · rw [PrefixGame.restTable_nonmem _ _ hm, PrefixGame.restTable_nonmem _ _ hm]
theorem restTable_ovL_tweak (L : LeafAddr) (R : RefTables adversary) (y : LeafData L) (tw : BitVec 128)
    (h : ∀ j, cellHdr L j ≠ tw) : restTable (ovL L R y) (.inr (.inl tw)) = restTable R (.inr (.inl tw)) := by
  rw [PrefixGame.restTable_private, PrefixGame.restTable_private]
  show ovPrivL L R.1 y.1 (.inl tw) = R.1 (.inl tw)
  rw [ovPrivL_inl, slotAt_none (fun j hj => absurd hj (h j)), slotAt_none (fun j hj => absurd hj (h j))]
  exact ChainGraph.joinOutput_parts _
theorem eval_lowerSeedPair (T : Answers) (lay : Layer) (tree p : Nat) :
    evalWithAnswerFn T (WCT9.lowerSeedPair lay tree p) =
      ((T (.inr (.inl (WCT9.lowerSeedHeader lay tree p)))).extractLsb' 0 128,
        (T (.inr (.inl (WCT9.lowerSeedHeader lay tree p)))).extractLsb' 128 128) := by
  unfold WCT9.lowerSeedPair privatePair privateHash
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rfl
/-! ### Programming uniform functions at a point -/

theorem uniform_map_equiv {α β : Type} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β] (e : α ≃ β) :
    (PMF.uniformOfFintype α).map e = PMF.uniformOfFintype β := by
  ext b
  rw [PMF.map_apply, tsum_eq_single (e.symm b)]
  · simp [PMF.uniformOfFintype_apply, Fintype.card_congr e]
  · intro x hx
    rw [if_neg]
    intro h
    apply hx
    rw [h]
    simp

/-- A uniform family of functions is a uniform family of functions programmed at fixed points `Y` with uniform
labels: `f c = update (g c) (Y c) (Lab c)`. -/
theorem uniform_program {ι : Type} [Fintype ι] [DecidableEq ι] (Y : ι → Digest) {β : Type}
    (G : (ι → Digest → Digest) → PMF β) :
    (PMF.uniformOfFintype (ι → Digest → Digest)).bind G =
      (PMF.uniformOfFintype ((ι → Digest → Digest) × (ι → Digest))).bind
        (fun p => G (fun c => Function.update (p.1 c) (Y c) (p.2 c))) := by
  let σ : (ι → Digest → Digest) × (ι → Digest) → (ι → Digest → Digest) × (ι → Digest) :=
    fun p => (fun c => Function.update (p.1 c) (Y c) (p.2 c), fun c => p.1 c (Y c))
  have hσ : ∀ p, σ (σ p) = p := by
    rintro ⟨g, z⟩
    refine Prod.ext ?_ ?_
    · funext c
      simp only [σ, Function.update_idem, Function.update_eq_self]
    · funext c
      simp only [σ, Function.update_self]
  let e : ((ι → Digest → Digest) × (ι → Digest)) ≃ ((ι → Digest → Digest) × (ι → Digest)) :=
    ⟨σ, σ, hσ, hσ⟩
  have h1 : (PMF.uniformOfFintype ((ι → Digest → Digest) × (ι → Digest))).bind
      (fun p => G (fun c => Function.update (p.1 c) (Y c) (p.2 c))) =
      ((PMF.uniformOfFintype ((ι → Digest → Digest) × (ι → Digest))).map e).bind (fun p => G p.1) := by
    rw [PMF.bind_map]
    rfl
  rw [h1, uniform_map_equiv, uniform_prod, PMF.bind_bind]
  congr 1
  funext g
  rw [PMF.bind_map]
  exact (PMF.bind_const _ _).symm

/-- The family seed of chain `c` for coefficients `K`. -/
noncomputable def seedOf {m : Nat} (K : Fin m → Digest) (c : Nat) : Digest :=
  ClaudeWCT.Arith.familyEval (List.ofFn K) (WCT9.lowerPoint c)
/-- Step-0 rows programmed at the family seeds. -/
noncomputable def progF {n m : Nat} (g : Fin n → Digest → Digest) (Lab : Fin n → Digest) (K : Fin m → Digest) :
    Fin n → Digest → Digest :=
  fun c => Function.update (g c) (seedOf K c) (Lab c)

theorem restTable_ov_const (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (R : RefTables adversary) (e s : Digest)
    (input : HashInput) :
    restTable (PrefixGame.ov a d R (fun _ _ => e, s)) (.inl (.inr input)) =
      match PrefixGame.rowOf a d input with
      | some p => joinHalf (WCT9.chainHigh a.key.lay a.chain p.1.val) e
          (WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain p.1.val) (restTable R (.inl (.inr input))))
      | none => restTable R (.inl (.inr input)) := by
  cases hp : PrefixGame.rowOf a d input with
  | some p =>
      have hin := PrefixGame.rowOf_some hp
      simp only
      rw [hin, PrefixGame.restTable_ov_prefix a hd]
  | none =>
      simp only
      rw [PrefixGame.restTable_ov_nonprefix a _ _ _ hp]

/-! ### The honest table of the prefix game with the leaf overridden -/

theorem eval_chain_zero (T : Answers) (lay : Layer) (tree leaf i s : Nat) (v : Digest) :
    evalWithAnswerFn T (chain lay tree leaf i s 0 v) = v := rfl

section Fill
variable {L : LeafAddr} (hLleaf : L.leaf < 2 ^ 24) {a : ChainAddr} (haL : a.key = L)
  (hac : a.chain < chainCount L.lay) (R : RefTables adversary) (hd1 : 1 ≤ restDepth a R)
include hLleaf haL hac hd1

theorem fill_priv (X : LeafData L) (e : Digest) (coord : Coordinate) :
    PrefixGame.fillTable a (ovL L R X) e (.inr coord) = restTable (ovL L R X) (.inr coord) := by
  unfold PrefixGame.fillTable
  exact PrefixGame.restTable_ov_private a _ _ _

end Fill

end Leaf
end ClaudeWCT.W9.T3.Security.Wots

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawLeaf
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high uniform_resample uniform_prod Hidden)
open ClaudeWCT.W9.T3.Security.Wots.Leaf
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
noncomputable local instance : Fintype Coordinate := coordinateFintype
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U)
/-- `pub` with the used halves (`zh`) of `L`'s step-0 rows replaced by `f`. -/
noncomputable def ovPubL (L : LeafAddr) (pub : U → HashOutput)
    (f : Fin (chainCount L.lay) → Digest → Digest) : U → HashOutput := fun x =>
  match zeroOf L x.val with
  | some p => joinHalf (zh L p.1) (f p.1 p.2) (WCT9.halfOf (!zh L p.1) (pub x))
  | none => pub x

/-- Leaf data: the 17 coefficients and the step-0 row functions of the chains. -/
noncomputable def ovL (L : LeafAddr) (R : Tables U) (y : LeafData L) : Tables U :=
  (ovPrivL L R.1 y.1, ovPubL L R.2 y.2)
noncomputable def rdL (L : LeafAddr) (R : Tables U) : LeafData L :=
  (fun j => halfOf (ordL L j % 2) (R.1 (.inl (cellHdr L j))),
    fun c v => WCT9.halfOf (zh L c) (R.2 ⟨chainRowW ⟨L, c⟩ 0 v, RawPrefix.chainRowW_mem hU _ _ _⟩))

theorem ovPubL_zero (L : LeafAddr) (pub : U → HashOutput)
    (f : Fin (chainCount L.lay) → Digest → Digest) (c : Fin (chainCount L.lay)) (v : Digest) :
    ovPubL L pub f ⟨chainRowW ⟨L, c⟩ 0 v, RawPrefix.chainRowW_mem hU _ _ _⟩ =
      joinHalf (zh L c) (f c v) (WCT9.halfOf (!zh L c) (pub ⟨chainRowW ⟨L, c⟩ 0 v, RawPrefix.chainRowW_mem hU _ _ _⟩)) := by
  unfold ovPubL
  simp only [zeroOf_chainRow]

theorem rdL_ovL {L : LeafAddr} (hL : L.leaf < 2 ^ 24) (R : Tables U) (y : LeafData L) :
    rdL hU L (ovL L R y) = y := by
  obtain ⟨K, f⟩ := y
  unfold rdL ovL
  refine Prod.ext ?_ ?_
  · funext j
    exact ovPrivL_cell hL R.1 K j
  · funext c v
    simp only
    rw [ovPubL_zero hU, halfOf_joinHalf]

theorem ovL_ovL_rdL {L : LeafAddr} (hL : L.leaf < 2 ^ 24) (R : Tables U) (y : LeafData L) :
    ovL L (ovL L R y) (rdL hU L R) = R := by
  obtain ⟨priv, pub⟩ := R
  obtain ⟨K, f⟩ := y
  unfold ovL rdL
  simp only
  refine Prod.ext ?_ ?_
  · funext coord
    rcases coord with tw | x
    · show ovPrivL L (ovPrivL L priv K) _ (.inl tw) = priv (.inl tw)
      rw [ovPrivL_inl, ovPrivL_inl]
      have e0 : ((slotAt L tw 0).map (fun j => halfOf (ordL L j % 2) (priv (.inl (cellHdr L j))))).getD
          (low (ChainGraph.joinOutput (((slotAt L tw 0).map K).getD (low (priv (.inl tw))))
            (((slotAt L tw 1).map K).getD (high (priv (.inl tw)))))) = low (priv (.inl tw)) := by
        cases h : slotAt L tw 0 with
        | none => simp only [Option.map_none, Option.getD_none, h, low, ChainGraph.joinOutput_low]
        | some j =>
            obtain ⟨h1, h2⟩ := slotAt_some h
            simp only [Option.map_some, Option.getD_some, halfOf, h2, h1, if_true]
      have e1 : ((slotAt L tw 1).map (fun j => halfOf (ordL L j % 2) (priv (.inl (cellHdr L j))))).getD
          (high (ChainGraph.joinOutput (((slotAt L tw 0).map K).getD (low (priv (.inl tw))))
            (((slotAt L tw 1).map K).getD (high (priv (.inl tw)))))) = high (priv (.inl tw)) := by
        cases h : slotAt L tw 1 with
        | none => simp only [Option.map_none, Option.getD_none, h, high, ChainGraph.joinOutput_high]
        | some j =>
            obtain ⟨h1, h2⟩ := slotAt_some h
            simp only [Option.map_some, Option.getD_some, halfOf, h2, h1]
            rfl
      rw [e0, e1]
      exact ChainGraph.joinOutput_parts _
    · rfl
  · funext x
    dsimp only
    unfold ovPubL
    cases hp : zeroOf L x.val with
    | none => simp only [hp]
    | some p =>
        simp only [hp]
        have hx : x = ⟨chainRowW ⟨L, p.1⟩ 0 p.2, RawPrefix.chainRowW_mem hU _ _ _⟩ := Subtype.ext (zeroOf_some hp)
        subst hx
        simp only [halfOf_not_joinHalf, joinHalf_halfOf]

include hU in
/-- Resampling `L`'s coefficients and step-0 rows preserves the rest-table law. -/
theorem restLaw_resampleL {L : LeafAddr} (hL : L.leaf < 2 ^ 24) {β : Type} (F : Tables U → PMF β) :
    (PMF.uniformOfFintype (Tables U)).bind F =
      (PMF.uniformOfFintype (Tables U)).bind (fun R => (PMF.uniformOfFintype (LeafData L)).bind (fun y => F (ovL L R y))) := by
  have h := uniform_resample (Ω := Tables U) (X := fun _ => LeafData L) (fun _ => 0)
    (fun _ R y => ovL L R y) (fun _ R => rdL hU L R) (fun R y => rdL_ovL hU hL R y) (fun R y => ovL_ovL_rdL hU hL R y)
    (fun _ _ => rfl)
  conv_lhs => rw [← h]
  rw [PMF.bind_bind]
  apply congrArg (PMF.uniformOfFintype (Tables U)).bind
  funext R
  rw [PMF.bind_map]
  rfl

include hU in
theorem raw_ovL_zero (L : LeafAddr) (R : Tables U) (y : LeafData L) (c : Fin (chainCount L.lay))
    (v : Digest) : raw (ovL L R y) (.inl (.inr (chainRowW ⟨L, c⟩ 0 v))) =
      joinHalf (zh L c) (y.2 c v) (WCT9.halfOf (!zh L c) (raw R (.inl (.inr (chainRowW ⟨L, c⟩ 0 v))))) := by
  rw [RawPrefix.raw_mem _ _ (RawPrefix.chainRowW_mem hU _ _ _),
    RawPrefix.raw_mem _ _ (RawPrefix.chainRowW_mem hU _ _ _)]
  exact ovPubL_zero hU L R.2 y.2 c v
theorem raw_ovL_pub (L : LeafAddr) (R : Tables U) (y : LeafData L) (input : HashInput)
    (h : zeroOf L input = none) :
    raw (ovL L R y) (.inl (.inr input)) = raw R (.inl (.inr input)) := by
  by_cases hm : input ∈ U
  · rw [RawPrefix.raw_mem _ _ hm, RawPrefix.raw_mem _ _ hm]
    show ovPubL L R.2 y.2 ⟨input, hm⟩ = R.2 ⟨input, hm⟩
    unfold ovPubL
    simp only [h]
  · rw [RawPrefix.raw_nonmem _ _ hm, RawPrefix.raw_nonmem _ _ hm]
theorem raw_ovL_tweak (L : LeafAddr) (R : Tables U) (y : LeafData L) (tw : BitVec 128)
    (h : ∀ j, cellHdr L j ≠ tw) : raw (ovL L R y) (.inr (.inl tw)) = raw R (.inr (.inl tw)) := by
  rw [RawPrefix.raw_private, RawPrefix.raw_private]
  show ovPrivL L R.1 y.1 (.inl tw) = R.1 (.inl tw)
  rw [ovPrivL_inl, slotAt_none (fun j hj => absurd hj (h j)), slotAt_none (fun j hj => absurd hj (h j))]
  exact ChainGraph.joinOutput_parts _
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawLeaf

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawLeaf
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high uniform_resample uniform_prod Hidden)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate)
open ClaudeWCT.W9.T3.Security.Wots.Leaf

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U)
noncomputable def fillTable (a : ChainAddr) (R : Tables U) (e : Digest) : Answers := raw (RawPrefix.fill a R e)
include hU
theorem raw_ov_const (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (R : Tables U) (e s : Digest)
    (input : HashInput) :
    raw (RawPrefix.ov a d R (fun _ _ => e, s)) (.inl (.inr input)) =
      match PrefixGame.rowOf a d input with
      | some p => joinHalf (WCT9.chainHigh a.key.lay a.chain p.1.val) e
          (WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain p.1.val) (raw R (.inl (.inr input))))
      | none => raw R (.inl (.inr input)) := by
  -- C3 (#866): a prefix row keeps the half `chainHigh` of its step (`restTable_ov_const`).
  cases hp : PrefixGame.rowOf a d input with
  | some p =>
      have hin := PrefixGame.rowOf_some hp
      simp only
      rw [hin, RawPrefix.raw_ov_prefix hU a hd]
  | none =>
      simp only
      rw [RawPrefix.raw_ov_nonprefix a _ _ _ hp]

/-! ### The honest table of the prefix game with the leaf overridden -/

theorem eval_chain_zero (T : Answers) (lay : Layer) (tree leaf i s : Nat) (v : Digest) :
    evalWithAnswerFn T (chain lay tree leaf i s 0 v) = v := rfl

section Fill
variable {L : LeafAddr} (hLleaf : L.leaf < 2 ^ 24) {a : ChainAddr} (haL : a.key = L)
  (hac : a.chain < chainCount L.lay) (R : Tables U) (hd1 : 1 ≤ RawPrefix.restDepth a R)
include hLleaf haL hac hd1

theorem fill_priv (X : LeafData L) (e : Digest) (coord : Coordinate) :
    fillTable a (ovL L R X) e (.inr coord) = raw (ovL L R X) (.inr coord) := by
  unfold fillTable RawPrefix.fill
  exact RawPrefix.raw_ov_private a _ _ _

end Fill
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawLeaf

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Leaf
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.W9.T3M SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open ClaudeWCT.W9.T3.Security.Wots.Leaf
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem respects_coverP {α : Type} {p : M α} (h : ∀ c, Respects (UntouchedP c) p) :
    ∀ cs : List ChainAddr, Respects (fun q => ∀ c ∈ cs, UntouchedP c q) p
  | [] => Respects.mono' (h ⟨⟨0,0,0⟩,0⟩) (fun _ _ c hc => absurd hc List.not_mem_nil)
  | c::cs => Respects.mono' (Respects.inter (h c) (respects_coverP h cs)) (fun _ hq c' hc' => by
      rcases List.mem_cons.mp hc' with rfl | hc'
      · exact hq.1
      · exact hq.2 c' hc')

theorem leafOut_of_coverP {L : LeafAddr} {q : Spec.Domain} (h : ∀ c ∈ coverAddrs L, UntouchedP c q) :
    LeafOut L q := by
  rcases q with (coin | input) | (tweak | other)
  · trivial
  · intro c step value hc hs heq
    exact h ⟨L,c⟩ (List.mem_append_left _ (List.mem_map.mpr ⟨c,List.mem_range.mpr hc,rfl⟩)) step value hs heq
  · intro j hj heq
    apply h ⟨⟨L.lay,L.tree,0⟩,2*(WCT9.famOrdinal L.lay L.leaf j/2)⟩
      (List.mem_append_right _ (List.mem_map.mpr ⟨j,List.mem_range.mpr hj,rfl⟩))
    change tweak=seedTweakP _
    rw [heq]
    unfold seedTweakP seedSlot seedTweak WCT9.lowerOrdinal WCT9.lowerSeedHeader
    simp only
    split <;> simp [Nat.mul_div_cancel_left]
  · trivial

theorem respects_leafOutP {α : Type} {p : M α} (h : ∀ c, Respects (UntouchedP c) p) (L : LeafAddr) :
    Respects (LeafOut L) p :=
  Respects.mono' (respects_coverP h (coverAddrs L)) fun _ hq => leafOut_of_coverP hq

theorem buildForest_out {L : LeafAddr} {T T' : Answers} (hC : LeafAgree L T T')
    (index : Nat) (selected : ForestSelection) (words : ForestWords) :
    ExecEq T T' (buildForest index selected words) (buildForest index selected words) := by
  have h := respects_leafOutP (fun a => CanonicalRef.respectsP_buildForest a index selected words) L
  exact ⟨h.eval_eq hC.out, congrArg List.length (h.queried_eq hC.out)⟩

theorem forestCommitment_out {L : LeafAddr} {T T' : Answers} (hC : LeafAgree L T T') (index : Nat) :
    CanonicalRef.forestCommitment T' index=CanonicalRef.forestCommitment T index := by
  have h := congrArg Prod.snd (buildForest_out hC index (forestSelectionFromOutput 0) (forestWordsFromOutput 0)).1
  simpa only [buildForest_commitment] using h

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Leaf

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawLeaf
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high uniform_resample uniform_prod Hidden)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate)
open ClaudeWCT.W9.T3.Security.Wots.Leaf

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U)
section Program
variable {L : LeafAddr} (hLleaf : L.leaf < 2 ^ 24) {a : ChainAddr} (haL : a.key = L)
  (hac : a.chain < chainCount L.lay) (R : Tables U) (hd1 : 1 ≤ RawPrefix.restDepth a R)
include hU hLleaf haL hac hd1
end Program
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawLeaf

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Leaf
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open ClaudeWCT.W9.T3.Security.Wots.Leaf
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {messages : LeafAddr → LayerMsg} {L : LeafAddr} {T T' : Answers}
variable (hC : Congr messages L T T') (hLleaf : L.leaf<2^24)
include hC
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Leaf

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Leaf
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open ClaudeWCT.W9.T3.Security.Wots.Leaf
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Leaf

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Leaf
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open ClaudeWCT.W9.T3.Security.Wots.Leaf
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem execEq_out {T T' : Answers} {L : LeafAddr} (hC : LeafAgree L T T')
    {α : Type} {p : M α} (h : Respects (LeafOut L) p) : ExecEq T T' p p :=
  ⟨h.eval_eq hC.out,congrArg List.length (h.queried_eq hC.out)⟩
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Leaf

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.W9.T3M SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3.Security.Wots.Leaf
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U)

theorem leafOut_encoding (L : LeafAddr) (e : Wots.Enc.EncIndex) :
    LeafOut L (.inl (.inr (Wots.Enc.encInput e))) := by
  intro c step value _ _ he
  have hn := nonEnc_chainRow ⟨L,c⟩ step value
  apply hn
  rw [←he]
  exact Wots.Enc.encInput_encHeader e

theorem leafAgree_normalize {L : LeafAddr} {R R' : Tables U}
    (hC : LeafAgree L (raw R) (raw R')) (hm : sourceMessages (raw R')=sourceMessages (raw R)) :
    LeafAgree L (answers hU R) (answers hU R') := by
  refine ⟨?_,?_⟩
  · intro query hq
    rcases query with (coin | input) | coordinate
    · exact hC.out _ hq
    · by_cases hu : input∈U
      · rw [show answers hU R' (.inl (.inr input))=(normalize hU R').2 ⟨input,hu⟩ from RawPrefix.raw_mem _ _ hu,
          show answers hU R (.inl (.inr input))=(normalize hU R).2 ⟨input,hu⟩ from RawPrefix.raw_mem _ _ hu]
        change MessageSwap.table zeroMessages (sourceMessages (raw R')) _ _ hU R'.2 ⟨input,hu⟩=
          MessageSwap.table zeroMessages (sourceMessages (raw R)) _ _ hU R.2 ⟨input,hu⟩
        have ht : MessageSwap.table zeroMessages (sourceMessages (raw R')) zeroMessages_fit (sourceMessages_fit (raw R')) hU=
            MessageSwap.table zeroMessages (sourceMessages (raw R)) zeroMessages_fit (sourceMessages_fit (raw R)) hU := by
          congr 1
        rw [ht]
        by_cases he : ∃e,Wots.Enc.encInput e=input
        · obtain ⟨e,rfl⟩ := he
          rw [MessageSwap.table_at,MessageSwap.table_at]
          exact (RawPrefix.raw_mem _ _ _).symm.trans ((hC.out _ (leafOut_encoding L _)).trans (RawPrefix.raw_mem _ _ _))
        · push_neg at he
          rw [MessageSwap.table_other _ _ _ _ _ _ _ he,MessageSwap.table_other _ _ _ _ _ _ _ he]
          exact (RawPrefix.raw_mem _ _ _).symm.trans ((hC.out _ hq).trans (RawPrefix.raw_mem _ _ _))
      · rw [show answers hU R' (.inl (.inr input))=(0 : HashOutput) from RawPrefix.raw_nonmem _ _ hu,
          show answers hU R (.inl (.inr input))=(0 : HashOutput) from RawPrefix.raw_nonmem _ _ hu]
    · exact hC.out _ hq
  · intro o ho hno
    rw [Wots.Leaf.eval_lowerSeedPair,Wots.Leaf.eval_lowerSeedPair,
      nonEnc hU R' _ (by trivial),nonEnc hU R _ (by trivial)]
    simpa only [Wots.Leaf.eval_lowerSeedPair] using hC.half o ho hno

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawLeaf
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.W9.T3.Security.Wots.Leaf
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U)

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawLeaf
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsLeafTest ====
section

/-! # The seed-test program of a lower leaf (campaign X1 stage B, step B3)

Fix a lower source chain `a` of leaf `L`, the rest tables `R` and the depth `d` of `a`. With the step-0 rows of
`L`'s chains programmed at the family seeds (`fY`) and chain `a`'s prefix tables programmed at its seed (`tY`),
the adversary's oracle world of the prefix game is a test program (`testImpl`) over the unrevealed seeds: a query
of a programmed row at `v` is the equality test `seed = v`. `evalT_testRun` identifies the run of the test program
against `y` with the prefix-game run in the world programmed at `y`. -/

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
noncomputable local instance instFintypeCoordinate_wotsLeafTest : Fintype Coordinate := coordinateFintype
namespace Leaf
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open ClaudeWCT.Arith.SideChannel (TSpec coinQ testQ evalT answerImpl Free enT exT tdepth)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec observedImpl record evaluate observedRun)
variable {adversary : AdversaryP}

/-- Chains of `L` revealed (depth `0`) in `R`. -/
noncomputable def revSet (L : LeafAddr) (R : RefTables adversary) : Finset (Fin (chainCount L.lay)) :=
  Finset.univ.filter fun c => depth (restTable R) ⟨L, c⟩ = 0

/-- Parameters of the test program: row functions and labels of `L`'s step-0 rows (`g`, `lab`), of chain `a`'s
prefix tables (`gt`, `labt`), and the revealed seeds `r`. -/
structure TParams (L : LeafAddr) (d : Nat) where
  g : Fin (chainCount L.lay) → Digest → Digest
  lab : Fin (chainCount L.lay) → Digest
  gt : Fin d → Digest → Digest
  labt : Fin d → Digest
  r : Fin (chainCount L.lay) → Digest

section Defs
variable (L : LeafAddr) (a : ChainAddr) (d : Nat) (R : RefTables adversary)
  (Rev : Finset (Fin (chainCount L.lay))) (aF : Free Rev) (P : TParams L d)

/-- Chain `a`'s prefix tables, row `0` programmed at the seed `s` (the other rows at `0`). -/
def tY (s : Digest) : Fin d → Digest → Digest :=
  fun i => Function.update (P.gt i) (if i.val = 0 then s else 0) (P.labt i)

/-- Step-0 rows of `L`'s chains: revealed chains programmed at `r`, unrevealed ones at `y`. -/
noncomputable def fY (y : Free Rev → Digest) : Fin (chainCount L.lay) → Digest → Digest :=
  fun c => Function.update (P.g c) (if hc : c ∈ Rev then P.r c else y ⟨c, hc⟩) (P.lab c)

/-- Observed prefix rows. -/
abbrev TObs := Fin d → Digest → Option Digest

/-- Answer to a prefix query of chain `a`: row `0` is a test on `a`'s seed. -/
noncomputable def prefAns (p : Fin d × Digest) : OracleComp (TSpec (Free Rev) Digest) Digest :=
  if p.1.val = 0 then (fun b => if b then P.labt p.1 else P.gt p.1 p.2) <$> testQ (aF, p.2)
  else pure (Function.update (P.gt p.1) 0 (P.labt p.1) p.2)

/-- Answer to any other public query: step-0 rows of unrevealed chains of `L` are tests. -/
noncomputable def pubAns (input : HashInput) : OracleComp (TSpec (Free Rev) Digest) HashOutput :=
  match zeroOf L input with
  | some cv =>
      if hc : cv.1 ∈ Rev then
        pure (joinHalf (zh L cv.1) (Function.update (P.g cv.1) (P.r cv.1) (P.lab cv.1) cv.2)
          (WCT9.halfOf (!zh L cv.1) (restTable R (.inl (.inr input)))))
      else (fun b => joinHalf (zh L cv.1) (if b then P.lab cv.1 else P.g cv.1 cv.2)
          (WCT9.halfOf (!zh L cv.1) (restTable R (.inl (.inr input))))) <$> testQ (⟨cv.1, hc⟩, cv.2)
  | none => pure (restTable R (.inl (.inr input)))

/-- The test-program implementation of the prefix game's oracle world. -/
noncomputable def testImpl : QueryImpl RefWorld (StateT (TObs d) (OracleComp (TSpec (Free Rev) Digest)))
  | .inl (.inl n) => StateT.lift (coinQ n)
  | .inl (.inr input) =>
      match PrefixGame.rowOf a d input with
      | some p => StateT.mk fun obs =>
          (fun w => (joinHalf (WCT9.chainHigh a.key.lay a.chain p.1.val) w
            (WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain p.1.val) (restTable R (.inl (.inr input)))),
              record obs p w)) <$> prefAns L d Rev aF P p
      | none => StateT.lift (pubAns L d R Rev P input)
  | .inr _ => pure ()
end Defs

/-- Pairing stage 1: the leaf override keeps the half of a step-0 row of `L` that its chain does not read. -/
theorem otherZ_ovL (L : LeafAddr) (R : RefTables adversary) (X : LeafData L) (input : HashInput)
    {cv : Fin (chainCount L.lay) × Digest} (hz : zeroOf L input = some cv) :
    WCT9.halfOf (!zh L cv.1) (restTable (ovL L R X) (.inl (.inr input))) =
      WCT9.halfOf (!zh L cv.1) (restTable R (.inl (.inr input))) := by
  rw [zeroOf_some hz, restTable_ovL_zero, halfOf_not_joinHalf]
/-- A row of chain `a` at a step `s < 256` that is a step-0 row of chain `c` of `L` is step 0 of a chain with the
same layer and parity, hence read through the same half. -/
theorem chainHigh_of_zeroOf {L : LeafAddr} {a : ChainAddr} {s : Nat} {v : Digest} (hs : s < 256)
    (hc : a.chain < 2 ^ 24)
    {cv : Fin (chainCount L.lay) × Digest} (hz : zeroOf L (chainRowW a s v) = some cv) :
    WCT9.chainHigh a.key.lay a.chain s = zh L cv.1 := by
  -- Witness stack: the top G rule (`i ≤ 52`) is not a function of `i % 2^24`, so the chain index is pinned by
  -- the bound `a.chain < 2^24` (the header carries `i % 2^24`).
  have he := zeroOf_some hz
  obtain ⟨hh, -⟩ := chainInputW_fields he
  obtain ⟨hl, -, -, hi, hst⟩ := chainHeader_fields hh
  have hs0 : s = 0 := by simp only [Nat.zero_mod] at hst; omega
  have hcv : cv.1.val < 2 ^ 24 :=
    lt_of_lt_of_le cv.1.isLt (le_trans (SigGolfCandidate.T3.chainCount_bound L.lay) (by norm_num))
  have hac : a.chain = cv.1.val := by
    rw [Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hcv] at hi; exact hi
  subst hs0
  unfold zh
  simp only at hl
  rw [hl, hac]

/-- C3: the half of a chain-`a` row that the prefix game keeps from the rest table is unchanged by the leaf
override: a step-0 row keeps its high half, and the only row whose used half is high (step 6 of a lower chain 0)
is no step-0 row. -/
theorem otherHalf_ovL (L : LeafAddr) (R : RefTables adversary) (X : LeafData L) (a : ChainAddr) (s : Nat)
    (v : Digest)
    (hs : s < 256) (hc : a.chain < 2 ^ 24) :
    WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain s) (restTable (ovL L R X) (.inl (.inr (chainRowW a s v)))) =
      WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain s) (restTable R (.inl (.inr (chainRowW a s v)))) := by
  cases hz : zeroOf L (chainRowW a s v) with
  | none => rw [restTable_ovL_pub L R X _ hz]
  | some cv => rw [chainHigh_of_zeroOf hs hc hz, otherZ_ovL L R X _ hz]
theorem ite_decide_update (g : Digest → Digest) (y lab v : Digest) :
    (if decide (y = v) then lab else g v) = Function.update g y lab v := by
  rw [Function.update_apply]
  by_cases h : v = y
  · subst h; simp
  · rw [if_neg h, if_neg (by simpa [eq_comm] using h)]

section Bridge
variable {L : LeafAddr} {a : ChainAddr} {d : Nat} (R : RefTables adversary) {Rev : Finset (Fin (chainCount L.lay))}
  (aF : Free Rev) (P : TParams L d)

theorem evalT_map {ι : Type} [Fintype ι] [DecidableEq ι] {α β : Type} (y : ι → Digest) (f : α → β)
    (oa : OracleComp (TSpec ι Digest) α) : evalT y (f <$> oa) = (evalT y oa).map f := by
  unfold evalT
  rw [simulateQ_map]
  rfl

theorem evalT_prefAns (y : Free Rev → Digest) (p : Fin d × Digest) :
    evalT y (prefAns L d Rev aF P p) = PMF.pure (tY L d P (y aF) p.1 p.2) := by
  unfold prefAns tY
  split_ifs with h0
  · rw [evalT_map, ClaudeWCT.Arith.SideChannel.evalT_testQ, PMF.pure_map, ite_decide_update]
  · rfl

theorem evalT_pubAns (y : Free Rev → Digest) (K : Fin (WCT9.famCount L.lay) → Digest) (input : HashInput) :
    evalT y (pubAns L d R Rev P input) = PMF.pure (restTable (ovL L R (K, fY L d Rev P y)) (.inl (.inr input))) := by
  unfold pubAns
  cases hz : zeroOf L input with
  | none =>
      simp only
      rw [restTable_ovL_pub L R _ input hz]
      rfl
  | some cv =>
      simp only
      rw [zeroOf_some hz, restTable_ovL_zero, ← zeroOf_some hz]
      unfold fY
      simp only
      split_ifs with hc
      · rfl
      · rw [evalT_map, ClaudeWCT.Arith.SideChannel.evalT_testQ, PMF.pure_map, ite_decide_update]

/-- Per-query identification of the test program, run against `y`, with the programmed prefix-game world. -/
theorem testImpl_bridge (hd : d ≤ 256) (hc : a.chain < 2 ^ 24) (y : Free Rev → Digest) (K : Fin (WCT9.famCount L.lay) → Digest)
    (q : RefWorld.Domain) :
    (StateT.mk fun s => evalT y ((testImpl L a d R Rev aF P q).run s) : StateT (TObs d) PMF _) =
      simulateQ (observedImpl SphincsSecurity.Concrete.OtsPrefix.uniformImpl (tY L d P (y aF)))
        (PrefixGame.routeImpl a d (ovL L R (K, fY L d Rev P y)) q) := by
  rcases q with (n | input) | u
  · funext s
    simp only [testImpl, PrefixGame.routeImpl, simulateQ_spec_query, StateT.run_lift]
    show evalT y (ClaudeWCT.Arith.SideChannel.coinQ n >>= fun a => pure (a, s)) =
      (SphincsSecurity.Concrete.OtsPrefix.uniformImpl n).map (fun answer => (answer, s))
    rw [ClaudeWCT.Arith.SideChannel.evalT_bind, ClaudeWCT.Arith.SideChannel.evalT_coinQ]
    rfl
  · funext s
    simp only [testImpl, PrefixGame.routeImpl]
    cases hp : PrefixGame.rowOf a d input with
    | some p =>
        simp only [simulateQ_map, simulateQ_spec_query]
        show evalT y ((fun w => (joinHalf (WCT9.chainHigh a.key.lay a.chain p.1.val) w
          (WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain p.1.val) (restTable R (.inl (.inr input)))),
            record s p w)) <$> prefAns L d Rev aF P p) = _
        rw [evalT_map, evalT_prefAns, PMF.pure_map, PrefixGame.rowOf_some hp,
          otherHalf_ovL L R _ _ _ _ (by have := p.1.isLt; omega) hc]
        change _ = StateT.run (_ <$> observedImpl SphincsSecurity.Concrete.OtsPrefix.uniformImpl _ (Sum.inr p)) s
        rw [StateT.run_map]
        change _ = (fun x => _) <$> PMF.pure _
        rw [PMF.monad_map_eq_map, PMF.pure_map]
    | none =>
        simp only [simulateQ_pure, StateT.run_lift]
        show evalT y (pubAns L d R Rev P input >>= fun a => pure (a, s)) = _
        rw [ClaudeWCT.Arith.SideChannel.evalT_bind, evalT_pubAns R P y K input, PMF.pure_bind]
        rfl
  · funext s
    rfl

/-- **Bridge.** The test program run against `y` is the prefix-game run in the world programmed at `y`. -/
theorem evalT_testRun (hd : d ≤ 256) (hc : a.chain < 2 ^ 24) (y : Free Rev → Digest) (K : Fin (WCT9.famCount L.lay) → Digest) {α : Type}
    (G : OracleComp RefWorld α)
    (obs : TObs d) :
    evalT y ((simulateQ (testImpl L a d R Rev aF P) G).run obs) =
      observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl (tY L d P (y aF))
        (simulateQ (PrefixGame.routeImpl a d (ovL L R (K, fY L d Rev P y))) G) obs := by
  unfold evalT observedRun
  rw [ClaudeWCT.Arith.SideChannel.simulateQ_run_stateT, ← QueryImpl.simulateQ_compose]
  congr 2
  funext q
  rw [QueryImpl.apply_compose]
  exact testImpl_bridge R aF P hd hc y K q
end Bridge

/-! ### Test counts and depth -/

/-- Queries answered by a test: chain `a`'s prefix row `0`, and step-0 rows of unrevealed chains of `L`. -/
noncomputable def isTestQ (L : LeafAddr) (a : ChainAddr) (d : Nat) (Rev : Finset (Fin (chainCount L.lay))) :
    RefWorld.Domain → Prop
  | .inl (.inr input) =>
      match PrefixGame.rowOf a d input with
      | some p => p.1.val = 0
      | none =>
          match zeroOf L input with
          | some cv => cv.1 ∉ Rev
          | none => False
  | _ => False

theorem tdepth_map_le {ι : Type} [Fintype ι] [DecidableEq ι] {α β : Type} (f : α → β)
    (oa : OracleComp (TSpec ι Digest) α) : tdepth (f <$> oa) ≤ tdepth oa := by
  rw [map_eq_bind_pure_comp]
  exact (ClaudeWCT.Arith.SideChannel.tdepth_bind_le oa _ 0 fun _ => le_rfl).trans (by omega)
theorem enT_map {ι : Type} [Fintype ι] [DecidableEq ι] {α β : Type} (y : ι → Digest) (f : α → β)
    (oa : OracleComp (TSpec ι Digest) α) : enT y (f <$> oa) = enT y oa := by
  rw [map_eq_bind_pure_comp, ClaudeWCT.Arith.SideChannel.enT_bind]
  simp only [Function.comp_apply]
  rw [show (fun x => enT y (pure (f x) : OracleComp (TSpec ι Digest) β)) = fun _ => (0 : ℝ) from rfl,
    ClaudeWCT.Arith.SideChannel.exT_const, add_zero]
theorem tdepth_testQ {ι : Type} [Fintype ι] [DecidableEq ι] (p : ι × Digest) :
    tdepth (testQ p : OracleComp (TSpec ι Digest) Bool) = 1 := by
  have h := ClaudeWCT.Arith.SideChannel.tdepth_test (V := Digest) p (fun b => pure b)
  rw [bind_pure] at h
  rw [h]
  rfl
theorem enT_testQ {ι : Type} [Fintype ι] [DecidableEq ι] (y : ι → Digest) (p : ι × Digest) :
    enT y (testQ p : OracleComp (TSpec ι Digest) Bool) = 1 := by
  have h := ClaudeWCT.Arith.SideChannel.enT_test y p (fun b => pure b)
  rw [bind_pure] at h
  rw [h]
  simp [ClaudeWCT.Arith.SideChannel.enT_pure]

section Counts
variable {L : LeafAddr} {a : ChainAddr} {d : Nat} (R : RefTables adversary) {Rev : Finset (Fin (chainCount L.lay))}
  (aF : Free Rev) (P : TParams L d)

theorem tdepth_testImpl (q : RefWorld.Domain) (s : TObs d) :
    tdepth ((testImpl L a d R Rev aF P q).run s) ≤ if RefCharged q then 1 else 0 := by
  rcases q with (n | input) | u
  · simp only [testImpl, StateT.run_lift]
    rw [if_neg (by simp [RefCharged])]
    refine (ClaudeWCT.Arith.SideChannel.tdepth_bind_le _ _ 0 fun _ => le_rfl).trans ?_
    rw [Nat.add_zero, show coinQ n = (coinQ n >>= pure : OracleComp (TSpec (Free Rev) Digest) _) from
      (bind_pure _).symm, ClaudeWCT.Arith.SideChannel.tdepth_coin]
    simp [ClaudeWCT.Arith.SideChannel.tdepth_pure]
  · rw [if_pos (by simp [RefCharged])]
    cases hp : PrefixGame.rowOf a d input with
    | some p =>
        simp only [testImpl, hp, StateT.run_mk]
        refine (tdepth_map_le _ _).trans ?_
        unfold prefAns
        split_ifs with h0
        · exact (tdepth_map_le _ _).trans (le_of_eq (tdepth_testQ _))
        · exact Nat.zero_le _
    | none =>
        simp only [testImpl, hp, StateT.run_lift]
        refine (ClaudeWCT.Arith.SideChannel.tdepth_bind_le _ _ 0 fun _ => le_rfl).trans ?_
        rw [Nat.add_zero]
        unfold pubAns
        cases hz : zeroOf L input with
        | none => exact Nat.zero_le _
        | some cv =>
            simp only
            split_ifs with hc
            · exact Nat.zero_le _
            · exact (tdepth_map_le _ _).trans (le_of_eq (tdepth_testQ _))
  · exact Nat.zero_le _

theorem enT_testImpl (y : Free Rev → Digest) (q : RefWorld.Domain) (s : TObs d) :
    enT y ((testImpl L a d R Rev aF P q).run s) = if isTestQ L a d Rev q then 1 else 0 := by
  rcases q with (n | input) | u
  · rw [if_neg (by simp [isTestQ])]
    simp only [testImpl, StateT.run_lift]
    rw [ClaudeWCT.Arith.SideChannel.enT_bind, show coinQ n = (coinQ n >>= pure : OracleComp (TSpec (Free Rev) Digest) _)
      from (bind_pure _).symm, ClaudeWCT.Arith.SideChannel.enT_coin]
    simp [ClaudeWCT.Arith.SideChannel.enT_pure, ClaudeWCT.Arith.SideChannel.exT_const]
  · cases hp : PrefixGame.rowOf a d input with
    | some p =>
        have hT : isTestQ L a d Rev (.inl (.inr input)) ↔ p.1.val = 0 := by simp only [isTestQ, hp]
        simp only [testImpl, hp, StateT.run_mk]
        rw [enT_map]
        unfold prefAns
        split_ifs with h0 h1 h1
        · rw [enT_map, enT_testQ]
        · exact absurd (hT.mpr h0) h1
        · exact absurd (hT.mp h1) h0
        · rfl
    | none =>
        simp only [testImpl, hp, StateT.run_lift]
        rw [ClaudeWCT.Arith.SideChannel.enT_bind,
          show (fun x => enT y (pure (x, s) : OracleComp (TSpec (Free Rev) Digest) _)) = fun _ => (0 : ℝ) from rfl,
          ClaudeWCT.Arith.SideChannel.exT_const, add_zero]
        unfold pubAns
        cases hz : zeroOf L input with
        | none =>
            rw [if_neg (by simp only [isTestQ, hp, hz]; exact id)]
            rfl
        | some cv =>
            have hT : isTestQ L a d Rev (.inl (.inr input)) ↔ cv.1 ∉ Rev := by simp only [isTestQ, hp, hz]
            simp only
            split_ifs with hc h1 h1
            · exact absurd hc (hT.mp h1)
            · rfl
            · rw [enT_map, enT_testQ]
            · exact absurd (hT.mpr hc) h1
  · rw [if_neg (by simp [isTestQ])]
    rfl
end Counts

/-- Expected number of tests of a state-passing simulation that tests exactly on the `C`-queries. -/
theorem enT_simulate {ι ιs σ : Type} [Fintype ι] [DecidableEq ι] {spec : OracleSpec ιs} (y : ι → Digest)
    (impl : QueryImpl spec (StateT σ (OracleComp (TSpec ι Digest)))) (C : ιs → Prop) [DecidablePred C]
    (himpl : ∀ q s, enT y ((impl q).run s) = if C q then 1 else 0) {α : Type} (G : OracleComp spec α) (s : σ) :
    enT y ((simulateQ impl G).run s) =
      exT y (fun out => (out.1.2 : ℝ)) ((simulateQ impl (SphincsSecurity.QueryCap.counted C G)).run s) := by
  induction G using OracleComp.inductionOn generalizing s with
  | pure x =>
      rw [SphincsSecurity.QueryCap.counted_pure, simulateQ_pure, simulateQ_pure, StateT.run_pure, StateT.run_pure,
        ClaudeWCT.Arith.SideChannel.enT_pure, ClaudeWCT.Arith.SideChannel.exT_pure]
      simp
  | query_bind q k ih =>
      rw [SphincsSecurity.QueryCap.counted_query_bind]
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, simulateQ_pure]
      rw [ClaudeWCT.Arith.SideChannel.enT_bind, ClaudeWCT.Arith.SideChannel.exT_bind, himpl]
      simp only [ih]
      rw [← ClaudeWCT.Arith.SideChannel.exT_add_const]
      congr 1
      funext p
      rw [ClaudeWCT.Arith.SideChannel.exT_bind, ← ClaudeWCT.Arith.SideChannel.exT_add_const]
      congr 1
      funext r
      simp only [StateT.run_pure]
      rw [ClaudeWCT.Arith.SideChannel.exT_pure]
      push_cast
      split_ifs <;> simp

end Leaf
end ClaudeWCT.W9.T3.Security.Wots

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Test
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open ClaudeWCT.Arith.SideChannel (TSpec coinQ testQ evalT answerImpl Free enT exT tdepth)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec observedImpl record evaluate observedRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

noncomputable def publicAt (L : LeafAddr) (B : Answers) (f : Fin (chainCount L.lay) → Digest → Digest) (input : HashInput) : HashOutput :=
  match zeroOf L input with
  | some cv => joinHalf (zh L cv.1) (f cv.1 cv.2) (WCT9.halfOf (!zh L cv.1) (B (.inl (.inr input))))
  | none => B (.inl (.inr input))
noncomputable def withPublic (L : LeafAddr) (B : Answers) (f : Fin (chainCount L.lay) → Digest → Digest) : Answers
  | .inl (.inr input) => publicAt L B f input
  | .inl (.inl coin) => B (.inl (.inl coin))
  | .inr coordinate => B (.inr coordinate)

section Defs
variable (L : LeafAddr) (a : ChainAddr) (d : Nat) (B : Answers)
  (Rev : Finset (Fin (chainCount L.lay))) (aF : Free Rev) (P : TParams L d)
/-- Answer to any other public query: step-0 rows of unrevealed chains of `L` are tests. -/
noncomputable def pubAns (input : HashInput) : OracleComp (TSpec (Free Rev) Digest) HashOutput :=
  match zeroOf L input with
  | some cv =>
      if hc : cv.1 ∈ Rev then
        pure (joinHalf (zh L cv.1) (Function.update (P.g cv.1) (P.r cv.1) (P.lab cv.1) cv.2)
          (WCT9.halfOf (!zh L cv.1) (B (.inl (.inr input)))))
      else (fun b => joinHalf (zh L cv.1) (if b then P.lab cv.1 else P.g cv.1 cv.2)
          (WCT9.halfOf (!zh L cv.1) (B (.inl (.inr input))))) <$> testQ (⟨cv.1, hc⟩, cv.2)
  | none => pure (B (.inl (.inr input)))

/-- The test-program implementation of the prefix game's oracle world. -/
noncomputable def testImpl : QueryImpl RefWorld (StateT (TObs d) (OracleComp (TSpec (Free Rev) Digest)))
  | .inl (.inl n) => StateT.lift (coinQ n)
  | .inl (.inr input) =>
      match PrefixGame.rowOf a d input with
      | some p => StateT.mk fun obs =>
          (fun w => (joinHalf (WCT9.chainHigh a.key.lay a.chain p.1.val) w
            (WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain p.1.val) (B (.inl (.inr input)))),
              record obs p w)) <$> prefAns L d Rev aF P p
      | none => StateT.lift (pubAns L d B Rev P input)
  | .inr _ => pure ()
end Defs


section Bridge
variable {L : LeafAddr} {a : ChainAddr} {d : Nat} (B : Answers)
  {Rev : Finset (Fin (chainCount L.lay))} (aF : Free Rev) (P : TParams L d)

theorem evalT_pubAns (y : Free Rev → Digest) (input : HashInput) :
    evalT y (pubAns L d B Rev P input)=PMF.pure (publicAt L B (fY L d Rev P y) input) := by
  unfold pubAns publicAt
  cases hz : zeroOf L input with
  | none => rfl
  | some cv =>
    simp only
    unfold fY
    split_ifs with hc
    · rfl
    · rw [evalT_map,ClaudeWCT.Arith.SideChannel.evalT_testQ,PMF.pure_map,ite_decide_update]
/-- Per-query identification of the test program, run against `y`, with the programmed prefix-game world. -/
theorem testImpl_bridge (y : Free Rev → Digest) (q : RefWorld.Domain) :
    (StateT.mk fun s => evalT y ((testImpl L a d B Rev aF P q).run s) : StateT (TObs d) PMF _) =
      simulateQ (observedImpl SphincsSecurity.Concrete.OtsPrefix.uniformImpl (tY L d P (y aF)))
        (Route.routeImpl a d B (withPublic L B (fY L d Rev P y)) q) := by
  rcases q with (n | input) | u
  · funext s
    simp only [testImpl, Route.routeImpl, simulateQ_spec_query, StateT.run_lift]
    show evalT y (ClaudeWCT.Arith.SideChannel.coinQ n >>= fun a => pure (a, s)) =
      (SphincsSecurity.Concrete.OtsPrefix.uniformImpl n).map (fun answer => (answer, s))
    rw [ClaudeWCT.Arith.SideChannel.evalT_bind, ClaudeWCT.Arith.SideChannel.evalT_coinQ]
    rfl
  · funext s
    simp only [testImpl, Route.routeImpl]
    cases hp : PrefixGame.rowOf a d input with
    | some p =>
        simp only [simulateQ_map, simulateQ_spec_query]
        show evalT y ((fun w => (joinHalf (WCT9.chainHigh a.key.lay a.chain p.1.val) w
          (WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain p.1.val) (B (.inl (.inr input)))),
            record s p w)) <$> prefAns L d Rev aF P p) = _
        rw [evalT_map, evalT_prefAns, PMF.pure_map]
        change _ = StateT.run (_ <$> observedImpl SphincsSecurity.Concrete.OtsPrefix.uniformImpl _ (Sum.inr p)) s
        rw [StateT.run_map]
        change _ = (fun x => _) <$> PMF.pure _
        rw [PMF.monad_map_eq_map, PMF.pure_map]
    | none =>
        simp only [simulateQ_pure, StateT.run_lift]
        show evalT y (pubAns L d B Rev P input >>= fun a => pure (a, s)) = _
        rw [ClaudeWCT.Arith.SideChannel.evalT_bind, evalT_pubAns B P y input, PMF.pure_bind]
        rfl
  · funext s
    rfl

/-- **Bridge.** The test program run against `y` is the prefix-game run in the world programmed at `y`. -/
theorem evalT_testRun (y : Free Rev → Digest) {α : Type} (G : OracleComp RefWorld α)
    (obs : TObs d) :
    evalT y ((simulateQ (testImpl L a d B Rev aF P) G).run obs) =
      observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl (tY L d P (y aF))
        (simulateQ (Route.routeImpl a d B (withPublic L B (fY L d Rev P y))) G) obs := by
  unfold evalT observedRun
  rw [ClaudeWCT.Arith.SideChannel.simulateQ_run_stateT, ← QueryImpl.simulateQ_compose]
  congr 2
  funext q
  rw [QueryImpl.apply_compose]
  exact testImpl_bridge B aF P y q
end Bridge

section Counts
variable {L : LeafAddr} {a : ChainAddr} {d : Nat} (B : Answers) {Rev : Finset (Fin (chainCount L.lay))}
  (aF : Free Rev) (P : TParams L d)

theorem tdepth_testImpl (q : RefWorld.Domain) (s : TObs d) :
    tdepth ((testImpl L a d B Rev aF P q).run s) ≤ if RefCharged q then 1 else 0 := by
  rcases q with (n | input) | u
  · simp only [testImpl, StateT.run_lift]
    rw [if_neg (by simp [RefCharged])]
    refine (ClaudeWCT.Arith.SideChannel.tdepth_bind_le _ _ 0 fun _ => le_rfl).trans ?_
    rw [Nat.add_zero, show coinQ n = (coinQ n >>= pure : OracleComp (TSpec (Free Rev) Digest) _) from
      (bind_pure _).symm, ClaudeWCT.Arith.SideChannel.tdepth_coin]
    simp [ClaudeWCT.Arith.SideChannel.tdepth_pure]
  · rw [if_pos (by simp [RefCharged])]
    cases hp : PrefixGame.rowOf a d input with
    | some p =>
        simp only [testImpl, hp, StateT.run_mk]
        refine (tdepth_map_le _ _).trans ?_
        unfold prefAns
        split_ifs with h0
        · exact (tdepth_map_le _ _).trans (le_of_eq (tdepth_testQ _))
        · exact Nat.zero_le _
    | none =>
        simp only [testImpl, hp, StateT.run_lift]
        refine (ClaudeWCT.Arith.SideChannel.tdepth_bind_le _ _ 0 fun _ => le_rfl).trans ?_
        rw [Nat.add_zero]
        unfold pubAns
        cases hz : zeroOf L input with
        | none => exact Nat.zero_le _
        | some cv =>
            simp only
            split_ifs with hc
            · exact Nat.zero_le _
            · exact (tdepth_map_le _ _).trans (le_of_eq (tdepth_testQ _))
  · exact Nat.zero_le _

theorem enT_testImpl (y : Free Rev → Digest) (q : RefWorld.Domain) (s : TObs d) :
    enT y ((testImpl L a d B Rev aF P q).run s) = if isTestQ L a d Rev q then 1 else 0 := by
  rcases q with (n | input) | u
  · rw [if_neg (by simp [isTestQ])]
    simp only [testImpl, StateT.run_lift]
    rw [ClaudeWCT.Arith.SideChannel.enT_bind, show coinQ n = (coinQ n >>= pure : OracleComp (TSpec (Free Rev) Digest) _)
      from (bind_pure _).symm, ClaudeWCT.Arith.SideChannel.enT_coin]
    simp [ClaudeWCT.Arith.SideChannel.enT_pure, ClaudeWCT.Arith.SideChannel.exT_const]
  · cases hp : PrefixGame.rowOf a d input with
    | some p =>
        have hT : isTestQ L a d Rev (.inl (.inr input)) ↔ p.1.val = 0 := by simp only [isTestQ, hp]
        simp only [testImpl, hp, StateT.run_mk]
        rw [enT_map]
        unfold prefAns
        split_ifs with h0 h1 h1
        · rw [enT_map, enT_testQ]
        · exact absurd (hT.mpr h0) h1
        · exact absurd (hT.mp h1) h0
        · rfl
    | none =>
        simp only [testImpl, hp, StateT.run_lift]
        rw [ClaudeWCT.Arith.SideChannel.enT_bind,
          show (fun x => enT y (pure (x, s) : OracleComp (TSpec (Free Rev) Digest) _)) = fun _ => (0 : ℝ) from rfl,
          ClaudeWCT.Arith.SideChannel.exT_const, add_zero]
        unfold pubAns
        cases hz : zeroOf L input with
        | none =>
            rw [if_neg (by simp only [isTestQ, hp, hz]; exact id)]
            rfl
        | some cv =>
            have hT : isTestQ L a d Rev (.inl (.inr input)) ↔ cv.1 ∉ Rev := by simp only [isTestQ, hp, hz]
            simp only
            split_ifs with hc h1 h1
            · exact absurd hc (hT.mp h1)
            · rfl
            · rw [enT_map, enT_testQ]
            · exact absurd (hT.mpr hc) h1
  · rw [if_neg (by simp [isTestQ])]
    rfl
end Counts


end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Test

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawLeaf
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U)
include hU
attribute [local irreducible] raw normalize answers RawPrefix.fill ovL

theorem otherZ_ovL (L : LeafAddr) (R : Tables U) (X : LeafData L) (input : HashInput)
    {cv : Fin (chainCount L.lay) × Digest} (hz : zeroOf L input = some cv) :
    WCT9.halfOf (!zh L cv.1) (raw (ovL L R X) (.inl (.inr input))) =
      WCT9.halfOf (!zh L cv.1) (raw R (.inl (.inr input))) := by
  rw [zeroOf_some hz, raw_ovL_zero hU, halfOf_not_joinHalf]

/-- Stage 2 (C3, #866 `otherHalf_ovL`): the half of a chain-`a` row that the prefix game keeps from the rest
table (the half its step does not read) is unchanged by the leaf override: a step-0 row keeps its high half,
and the only row whose used half is high (step 6 of a lower chain 0) is no step-0 row. -/
theorem otherHalf_ovL (L : LeafAddr) (R : Tables U) (X : LeafData L) (a : ChainAddr) (s : Nat) (v : Digest)
    (hs : s < 256) (hc : a.chain < 2 ^ 24) :
    WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain s) (raw (ovL L R X) (.inl (.inr (chainRowW a s v)))) =
      WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain s) (raw R (.inl (.inr (chainRowW a s v)))) := by
  cases hz : zeroOf L (chainRowW a s v) with
  | none => rw [raw_ovL_pub _ _ _ _ hz]
  | some cv => rw [chainHigh_of_zeroOf hs hc hz, otherZ_ovL hU L R X _ hz]

/-- Stage 2 (C3): the filled table keeps `R`'s other half (the one the step does not read) of a chain-`a` row. -/
theorem otherHalf_fill (a : ChainAddr) (R : Tables U) (e : Digest) (s : Nat) (v : Digest) (hs : s < 256) :
    WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain s) (raw (RawPrefix.fill a R e) (.inl (.inr (chainRowW a s v)))) =
      WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain s) (raw R (.inl (.inr (chainRowW a s v)))) := by
  unfold RawPrefix.fill
  rw [raw_ov_const hU a (by have := RawPrefix.restDepth_le a R;omega)]
  cases hp : PrefixGame.rowOf a (RawPrefix.restDepth a R) (chainRowW a s v) with
  | none => rfl
  | some p =>
      simp only
      have hin := PrefixGame.rowOf_some hp
      have hps : p.1.val = s :=
        (ClaudeWCT.W9.T3.Security.Wots.chainRowW_inj
          (by have := p.1.isLt; have := RawPrefix.restDepth_le a R; omega) hs hin.symm).1
      rw [hps, halfOf_not_joinHalf]

/-- The filled table agrees with `R` on the high half of every non-prefix query. -/
theorem high_fill_nonprefix (a : ChainAddr) (R : Tables U) (e : Digest) (input : HashInput)
    (hn : PrefixGame.rowOf a (RawPrefix.restDepth a R) input = none) (b : Bool) :
    WCT9.halfOf b (raw (RawPrefix.fill a R e) (.inl (.inr input))) = WCT9.halfOf b (raw R (.inl (.inr input))) := by
  unfold RawPrefix.fill
  rw [RawPrefix.raw_ov_nonprefix a R _ input hn]

theorem normalized_public_congr {L : LeafAddr} {R R' : Tables U}
    (hC : LeafAgree L (raw R) (raw R')) (hm : sourceMessages (raw R')=sourceMessages (raw R))
    (input : HashInput) (heq : raw R' (.inl (.inr input))=raw R (.inl (.inr input))) :
    answers hU R' (.inl (.inr input))=answers hU R (.inl (.inr input)) := by
  by_cases hn : Wots.Enc.NonEnc (.inl (.inr input))
  · rw [nonEnc hU R' _ hn,nonEnc hU R _ hn,heq]
  · apply (leafAgree_normalize hU hC hm).out
    intro c step value hc hs he
    have hne := nonEnc_chainRow ⟨L,c⟩ step value
    apply hn
    rw [he]
    exact hne

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawLeaf
end
-- ==== merged from ClaudeWCT_WCT9_LowerReveal ====
section

/-!
# Revealed seeds of a lower leaf (campaign X1, stage B)

A lower WOTS signature reveals the seed of chain `i` exactly when its digit is `0`. Lower digits are `≤ 7` and sum
to `target lay`, so for `target lay ≥ 197` at most 14 of the 43 digits are zero (`lower_zero_count_le`): with
17 coefficients per leaf family, every unrevealed seed keeps `17 - 14 = 3` degrees of freedom, which is what the
side-channel bound (`ClaudeWCT.Arith.SideChannel.family_side_channel`, `|R| + 3 ≤ 17`) needs. With
`target ≤ 196` the bound becomes 15 and the margin is lost (DESIGN-A-SEC §3, attack A1).
-/

namespace ClaudeWCT.WCT9
open SigGolfCandidate.T3 SigGolfCandidate.T3.Cost

/-- A list of digits `≤ 7` sums to at most `7` times the number of its nonzero entries. -/
theorem sum_le_seven_mul_nonzero (ds : List Nat) (h : ∀ d ∈ ds, d ≤ 7) :
    ds.sum ≤ 7 * (ds.length - (ds.filter (· = 0)).length) := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
      have hd := h d List.mem_cons_self
      have ih' := ih fun x hx => h x (List.mem_cons_of_mem d hx)
      have hle : (ds.filter (· = 0)).length ≤ ds.length := List.length_filter_le _ _
      by_cases h0 : d = 0
      · subst h0
        have e : ((0 :: ds).filter (· = 0)).length = (ds.filter (· = 0)).length + 1 := by
          simp [List.filter_cons]
        rw [e, List.sum_cons, List.length_cons]
        omega
      · have e : ((d :: ds).filter (· = 0)).length = (ds.filter (· = 0)).length := by
          simp [List.filter_cons, h0]
        rw [e, List.sum_cons, List.length_cons]
        omega

/-- **At most 14 revealed seeds per lower leaf** (for lower targets `≥ 197`). -/
theorem lower_zero_count_le {lay : Layer} (hlay : lay ≠ 0) (htarget : 197 ≤ target lay) {value : Digest}
    {digits : List Nat} (h : decode lay value = some digits) : (digits.filter (· = 0)).length ≤ 14 := by
  obtain ⟨hlen, hsum⟩ := decode_length_sum h
  have hcc : chainCount lay = 43 := Cost.chainCount_lower hlay
  have hmax : ∀ d ∈ digits, d ≤ 7 := by
    intro d hd
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
    have := decode_digit_max h i (by omega)
    rw [List.getD_eq_getElem _ _ hi, Cost.maxDigit_lower hlay] at this
    exact this
  have hs := sum_le_seven_mul_nonzero digits hmax
  have hle : (digits.filter (· = 0)).length ≤ digits.length := List.length_filter_le _ _
  omega

/-- The current lower targets satisfy the hypothesis of `lower_zero_count_le`. -/
theorem lower_target_ge (lay : Layer) (hlay : lay ≠ 0) : 197 ≤ target lay := by
  revert hlay; fin_cases lay <;> decide

/-! ### Revealed seeds of a top leaf (campaign T51)

The T51 top WOTS has 27 radix-6 chains (digits `≤ 5`), 21 radix-5 chains (`≤ 4`), the radix-7 pair (`≤ 6`) and the
radix-6 checksum chain (`≤ 5`): capacity `27·5 + 21·4 + 2·6 + 5 = 236`. A zero digit loses at least `4` from the
capacity, so a top codeword with digit sum `T` has at most `(236 - T)/4` zero digits: `≤ 21` for `T ≥ 152`
(`top_zero_count_le`). With 31 coefficients per 4-leaf top family (`famCount_top`) every unrevealed top seed keeps
`31 - 21 ≥ 3` degrees of freedom even without the producer cap (the producer cap is 7). The dummy top codeword has no
zero digit. (#938: 54 chains, capacity 225, `≤ 20` zeros for `T ≥ 142`, 24 coefficients.) -/

/-- Digits bounded entrywise by `ms`, every bound `≥ 4`: the sum plus `4` per zero digit is at most `ms.sum`. -/
theorem sum_add_four_zero_le : ∀ (ds ms : List Nat), ds.length = ms.length →
    (∀ i, ds.getD i 0 ≤ ms.getD i 0) → (∀ m ∈ ms, 4 ≤ m) →
    ds.sum + 4 * (ds.filter (· = 0)).length ≤ ms.sum
  | [], [], _, _, _ => by simp
  | d :: ds, m :: ms, hl, hle, hm => by
      have ih := sum_add_four_zero_le ds ms (by simpa using hl) (fun i => by simpa using hle (i + 1))
        (fun x hx => hm x (List.mem_cons_of_mem m hx))
      have hd : d ≤ m := by simpa using hle 0
      have h4 : 4 ≤ m := hm m List.mem_cons_self
      by_cases h0 : d = 0
      · subst h0; simp only [List.filter_cons, decide_true, if_true, List.length_cons, List.sum_cons]; omega
      · simp only [List.filter_cons, h0, decide_false, Bool.false_eq_true, if_false, List.sum_cons]; omega
  | [], _ :: _, hl, _, _ => by simp at hl
  | _ :: _, [], hl, _, _ => by simp at hl

/-- Campaign T51: 27·5 + 21·4 + 2·6 + 5. -/
theorem top_capacity : ((List.range (chainCount 0)).map (maxDigit 0)).sum = 236 := by decide

theorem top_maxDigit_ge (i : Nat) : 4 ≤ maxDigit 0 i := by unfold maxDigit; split_ifs <;> omega

/-- **At most 21 revealed seeds per top leaf** (for top targets `≥ 152`; campaign T51, restated from `≤ 20` for
`≥ 142` on #938's capacity 225). -/
theorem top_zero_count_le (htarget : 152 ≤ target 0) {value : Digest} {digits : List Nat}
    (h : decode 0 value = some digits) : (digits.filter (· = 0)).length ≤ 21 := by
  obtain ⟨hlen, hsum⟩ := decode_length_sum h
  have key := sum_add_four_zero_le digits ((List.range (chainCount 0)).map (maxDigit 0)) (by simp [hlen])
    (fun i => by
      by_cases hi : i < chainCount 0
      · have hm : ((List.range (chainCount 0)).map (maxDigit 0)).getD i 0 = maxDigit 0 i := by
          rw [List.getD_eq_getElem _ _ (by simpa using hi)]; simp
        rw [hm]; exact decode_digit_max h i hi
      · rw [List.getD_eq_default _ _ (by omega)]; exact Nat.zero_le _)
    (by
      intro m hm
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hm
      exact top_maxDigit_ge i)
  rw [top_capacity] at key
  omega

/-- The current top target satisfies the hypothesis of `top_zero_count_le`. -/
theorem top_target_ge : 152 ≤ target 0 := by decide

/-- The dummy top codeword has no zero digit. -/
theorem dummyTop_zero : (dummyTop.filter (· = 0)).length = 0 := by decide

end ClaudeWCT.WCT9
end
