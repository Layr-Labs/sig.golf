import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMaskRef
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.SeccLaw
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.CanonEncoding

namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue leafRoot)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace Enc
open SigGolfCandidate.T3.Security.Wots.Enc
section Programs
theorem respects_forestPk (index : Nat) (pairs : List (Digest × Digest)) :
    Respects Enc.NonEnc (ClaudeWCT.WCT9.forestPk index pairs) :=
  ClaudeWCT.WCT9.Wots.Enc.respects_forestPk index pairs
theorem respects_signForest (index : Nat) (output : HashOutput) :
    Respects Enc.NonEnc (ClaudeWCT.WCT9.signForest index output) :=
  ClaudeWCT.WCT9.Wots.Enc.respects_signForest index output
theorem respects_digestSearch (rho : Digest) (message : Message) :
    ∀ fuel counter, Respects Enc.NonEnc (ClaudeWCT.WCT9.digestSearch rho message counter fuel) :=
  ClaudeWCT.WCT9.Wots.Enc.respects_digestSearch rho message
theorem respects_packedSecret (lay : Layer) (tree q : Nat) (carry : Digest) :
    Respects Enc.NonEnc (WCT9.packedSecret (WCT9.lowerSeedPair lay tree) q carry) := by
  unfold WCT9.packedSecret WCT9.lowerSeedPair
  split
  · exact Respects.bind (respects_privatePair _ _ _ _ _) fun _ => Respects.pure' _
  · exact Respects.pure' _
theorem respects_buildLeafP (lay : Layer) (tree leaf : Nat) (digits : List Nat) (carry : Digest) :
    Respects Enc.NonEnc (WCT9.buildLeafP lay tree leaf digits carry) := by
  unfold WCT9.buildLeafP
  refine Respects.bind (Respects.foldlM _ _ (fun i _ state => ?_) _) fun state =>
    Respects.bind (respects_leafHash _ _ _ _) fun _ => Respects.pure' _
  exact Respects.bind (respects_packedSecret _ _ _ _) fun sc =>
    Respects.bind (respects_chain _ _ _ _ _ _ _) fun _ =>
      Respects.bind (respects_chain _ _ _ _ _ _ _) fun _ => Respects.pure' _
theorem respects_buildTreeP (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    Respects Enc.NonEnc (WCT9.buildTreeP lay tree selected digits) := by
  unfold WCT9.buildTreeP
  exact Respects.bind (Respects.foldlM _ _ (fun leaf _ state =>
    Respects.bind (respects_buildLeafP _ _ _ _ _) fun _ => Respects.pure' _) _) fun state =>
      Respects.bind (respects_buildLevels _ _ _ _ _ (by decide)) fun _ => Respects.pure' _
end Programs
def RejPair (T T' : Answers) (q : Spec.Domain) : Prop :=
  ∃ (input : HashInput) (lay : Layer) (tr p ix : Nat), q = .inl (.inr input) ∧
    SigGolfCandidate.T3M.Extract.hdrBlock input = bytesLE 16 (header 4 lay.val tr p ix) ∧
    WCT9.producerDecode lay (low (T (.inl (.inr input)))) = none ∧
      WCT9.producerDecode lay (low (T' (.inl (.inr input)))) = none
theorem RejPair.layer {T T' : Answers} {input : HashInput} {lay : Layer} {tr p ix : Nat}
    (h : RejPair T T' (.inl (.inr input)))
    (hh : SigGolfCandidate.T3M.Extract.hdrBlock input = bytesLE 16 (header 4 lay.val tr p ix)) :
    WCT9.producerDecode lay (low (T (.inl (.inr input)))) = none ∧
      WCT9.producerDecode lay (low (T' (.inl (.inr input)))) = none := by
  obtain ⟨input', lay', tr', p', ix', hq, hh', h1, h2⟩ := h
  have hi : input' = input := (Sum.inr.inj (Sum.inl.inj hq)).symm
  subst hi
  rw [hh] at hh'
  have hf := (Mask.header_fields (bytesLE_injective hh')).2.1
  have hl : lay' = lay := Fin.ext (by have := lay.isLt; have := lay'.isLt; omega)
  subst hl
  exact ⟨h1, h2⟩
theorem RejPair.mk {T T' : Answers} {input : HashInput} {lay : Layer} {tr p ix : Nat}
    (hh : SigGolfCandidate.T3M.Extract.hdrBlock input = bytesLE 16 (header 4 lay.val tr p ix))
    (h1 : WCT9.producerDecode lay (low (T (.inl (.inr input)))) = none)
    (h2 : WCT9.producerDecode lay (low (T' (.inl (.inr input)))) = none) : RejPair T T' (.inl (.inr input)) :=
  ⟨input, lay, tr, p, ix, rfl, hh, h1, h2⟩
theorem RejPair.encHeader {T T' : Answers} {q : Spec.Domain} (h : RejPair T T' q) :
    ∃ input, q = .inl (.inr input) ∧ Enc.EncHeader input := by
  obtain ⟨input, lay, tr, p, ix, hq, hh, -, -⟩ := h
  exact ⟨input, hq, lay.val, tr, p, ix, hh⟩
def AgreeOn (S : Spec.Domain → Prop) (T T' : Answers) : Prop :=
  ∀ q, S q → T' q = T q ∨ RejPair T T' q
theorem AgreeOn.of_eq {S : Spec.Domain → Prop} {T T' : Answers} (h : ∀ q, S q → T' q = T q) : AgreeOn S T T' :=
  fun q hq => Or.inl (h q hq)
theorem AgreeOn.nonEnc {S : Spec.Domain → Prop} {T T' : Answers} (h : AgreeOn S T T')
    (hS : ∀ q, Enc.NonEnc q → S q) : ∀ q, Enc.NonEnc q → T' q = T q := by
  intro q hq
  rcases h q (hS q hq) with he | hr
  · exact he
  · obtain ⟨input, rfl, henc⟩ := hr.encHeader
    exact absurd henc hq
def RespAt (T : Answers) (S : Spec.Domain → Prop) {α : Type} (p : M α) : Prop :=
  ∀ T' : Answers, AgreeOn S T T' →
    evalWithAnswerFn T' p = evalWithAnswerFn T p ∧ SourceReplay.queried T' p = SourceReplay.queried T p
section RespAt
variable {T : Answers} {S : Spec.Domain → Prop}
theorem RespAt.of_respects {α : Type} {p : M α} (h : Respects Enc.NonEnc p)
    (hS : ∀ q, Enc.NonEnc q → S q) : RespAt T S p := by
  intro T' hT'
  obtain ⟨he, hq⟩ := h T' T (hT'.nonEnc hS)
  exact ⟨he, hq⟩
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
theorem respAt_layerCounterSearch (T : Answers) (S : Spec.Domain → Prop) (lay : Layer) (tree leaf : Nat)
    (msg : WCT9.LayerMsg) : ∀ fuel start,
      (∀ c < fuel, (∀ c' < c, WCT9.producerDecode lay (low (T (.inl (.inr (pad64 (WCT9.layerEncodingInput lay tree leaf msg
          (BitVec.ofNat 32 (start + c')))))))) = none) →
        S (.inl (.inr (pad64 (WCT9.layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 (start + c))))))) →
      RespAt T S (WCT9.layerCounterSearch lay tree leaf msg start fuel) := by
  intro fuel
  induction fuel with
  | zero => intro start _; exact RespAt.pure' _
  | succ fuel ih =>
      intro start hS T' hT'
      have hS0 : S (.inl (.inr (pad64 (WCT9.layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 start))))) := by
        have := hS 0 (Nat.zero_lt_succ _) (fun c' hc' => absurd hc' (Nat.not_lt_zero _))
        rwa [Nat.add_zero] at this
      have hrest : WCT9.producerDecode lay (low (T (.inl (.inr (pad64 (WCT9.layerEncodingInput lay tree leaf msg
          (BitVec.ofNat 32 start))))))) = none →
          RespAt T S (WCT9.layerCounterSearch lay tree leaf msg (start + 1) fuel) := by
        intro hnone
        apply ih (start + 1)
        intro c hc hprev
        have h := hS (c + 1) (by omega) (fun c' hc' => by
          rcases c' with _ | c''
          · rw [Nat.add_zero]
            exact hnone
          · have := hprev c'' (by omega)
            rwa [show start + (c'' + 1) = start + 1 + c'' by omega])
        rwa [show start + (c + 1) = start + 1 + c by omega] at h
      rw [WCT9.layerCounterSearch]
      rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, SourceReplay.queried_bind, SourceReplay.queried_bind]
      have hq0 : SourceReplay.queried T' (shortHash (WCT9.layerEncodingInput lay tree leaf msg
          (BitVec.ofNat 32 start))) = SourceReplay.queried T (shortHash (WCT9.layerEncodingInput lay tree leaf msg
          (BitVec.ofNat 32 start))) := rfl
      rw [hq0]
      rcases hT' _ hS0 with heq | hrej
      · have hev : evalWithAnswerFn T' (shortHash (WCT9.layerEncodingInput lay tree leaf msg
            (BitVec.ofNat 32 start))) = evalWithAnswerFn T (shortHash (WCT9.layerEncodingInput lay tree leaf msg
            (BitVec.ofNat 32 start))) :=
          congrArg (fun x : HashOutput => x.extractLsb' 0 128) heq
        rw [hev]
        cases hd : WCT9.producerDecode lay (evalWithAnswerFn T (shortHash (WCT9.layerEncodingInput lay tree leaf msg
            (BitVec.ofNat 32 start)))) with
        | none =>
            obtain ⟨h1, h2⟩ := hrest hd T' hT'
            dsimp only
            exact ⟨h1, by rw [h2]⟩
        | some digits => exact ⟨rfl, rfl⟩
      · obtain ⟨hTn, hTn'⟩ := hrej.layer
          (ClaudeWCT.W9.T3M.BC.hdrBlock_layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 start))
        have hl : WCT9.producerDecode lay (evalWithAnswerFn T (shortHash (WCT9.layerEncodingInput lay tree leaf msg
            (BitVec.ofNat 32 start)))) = none := hTn
        have hl' : WCT9.producerDecode lay (evalWithAnswerFn T' (shortHash (WCT9.layerEncodingInput lay tree leaf msg
            (BitVec.ofNat 32 start)))) = none := hTn'
        obtain ⟨h1, h2⟩ := hrest hTn T' hT'
        rw [hl, hl']
        dsimp only
        exact ⟨h1, by rw [h2]⟩
def Reached (T : Answers) (L : LeafAddr) (input : HashInput) : Prop :=
  ∃ c < WCT9.searchLimit L.lay, input = encRow L (leafMsg T L) (BitVec.ofNat 32 c) 0 ∧
    ∀ c' < c, WCT9.producerDecode L.lay (low (T (.inl (.inr (encRow L (leafMsg T L) (BitVec.ofNat 32 c') 0))))) = none
def leafOf (L : CanonGraph.LeafPos) : LeafAddr := ⟨L.lay, L.tree.val, L.leaf.val⟩
def HonestQ (T : Answers) : Spec.Domain → Prop
  | .inl (.inr input) => ¬ EncHeader input ∨ ∃ L : CanonGraph.LeafPos, Reached T (leafOf L) input
  | _ => True
theorem honestQ_of_nonEnc {T : Answers} {q : Spec.Domain} (h : Enc.NonEnc q) : HonestQ T q := by
  rcases q with (coin | input) | coordinate
  · trivial
  · exact Or.inl h
  · trivial
theorem respAt_referenceSearch (T : Answers) (S : Spec.Domain → Prop) (L : LeafAddr)
    (hS : ∀ input, Reached T L input → S (.inl (.inr input))) :
    RespAt T S (WCT9.layerCounterSearch L.lay L.tree L.leaf (leafMsg T L) 0 (WCT9.searchLimit L.lay)) := by
  apply respAt_layerCounterSearch
  intro c hc hprev
  apply hS
  refine ⟨c, hc, ?_, fun c' hc' => ?_⟩
  · rw [encRow_zero, Nat.zero_add]
  · have := hprev c' hc'
    rw [Nat.zero_add] at this
    rw [encRow_zero]
    exact this
def routePos (index : Nat) (hindex : index < 2 ^ 31) (lay : Layer) : CanonGraph.LeafPos :=
  ⟨lay, ⟨(route index lay).2, lt_of_le_of_lt (Nat.div_le_self _ _) hindex⟩,
    ⟨(route index lay).1, lt_of_lt_of_le (route_leaf_bound index lay)
      (by calc 2 ^ height lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (SigGolfCandidate.T3M.Extract.height_le lay)
            _ = 4096 := by norm_num)⟩⟩
theorem leafOf_routePos (index : Nat) (hindex : index < 2 ^ 31) (lay : Layer) :
    leafOf (routePos index hindex lay) = routeLeaf index lay := rfl
theorem respAt_routeSearch (T : Answers) (index : Nat) (hindex : index < 2 ^ 31) (lay : Layer) :
    RespAt T (HonestQ T) (WCT9.layerCounterSearch lay (route index lay).2 (route index lay).1
      (leafMsg T (routeLeaf index lay)) 0 (WCT9.searchLimit lay)) :=
  respAt_referenceSearch T (HonestQ T) (routeLeaf index lay)
    (fun input h => Or.inr ⟨routePos index hindex lay, h⟩)
theorem respAt_signLayers (T : Answers) (cache : T3.Cache) (index : Nat) (hindex : index < 2 ^ 31) :
    ∀ n, n ≤ 4 → ∀ msg, (∀ m, n = m + 1 → msg = leafMsg T (routeLeaf index (Fin.ofNat 4 m))) →
      RespAt T (HonestQ T) (WCT9.signLayersBC cache index n msg) := by
  intro n
  induction n with
  | zero => intro _ _ _; exact RespAt.pure' _
  | succ n ih =>
      intro hn msg hmsg
      simp only [WCT9.signLayersBC]
      refine RespAt.bind ?_ ?_
      · rw [hmsg n rfl]
        exact respAt_routeSearch T index hindex _
      · cases hs : evalWithAnswerFn T (WCT9.layerCounterSearch (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2
          (route index (Fin.ofNat 4 n)).1 msg 0 (WCT9.searchLimit (Fin.ofNat 4 n))) with
        | none =>
            dsimp only
            split_ifs with hn0
            · exact RespAt.bind (RespAt.of_respects (respects_signTop _ _ _) fun _ h => honestQ_of_nonEnc h)
                (RespAt.pure' _)
            · exact RespAt.pure' _
        | some found =>
            obtain ⟨counter, digits⟩ := found
            have hd := (WCT9.layerCounterSearch_some T _ _ _ msg (WCT9.searchLimit (Fin.ofNat 4 n)) 0 counter digits
              (by have := WCT9.searchLimit_le (Fin.ofNat 4 n); unfold counterLimit at this; omega) hs).2.2
            have hvalid := Cost.validDigits_decode hd
            dsimp only
            split_ifs with hn0
            · exact RespAt.bind (RespAt.of_respects (respects_signTop _ _ _) fun _ h => honestQ_of_nonEnc h)
                (RespAt.pure' _)
            · have hl0 : (Fin.ofNat 4 n : Layer) ≠ 0 := by
                intro h
                have hv : (Fin.ofNat 4 n : Layer).val = n := Nat.mod_eq_of_lt (by omega)
                rw [h] at hv
                exact hn0 hv.symm
              refine RespAt.bind (RespAt.of_respects (respects_buildTreeP _ _ _ _)
                fun _ h => honestQ_of_nonEnc h) ?_
              rw [WCT9.eval_buildTreeP_result T hl0 _ _ digits hvalid (route_leaf_bound index _)]
              dsimp only
              obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
              refine RespAt.bind (ih (by omega) _ (fun m' hm' => ?_)) ?_
              · obtain rfl : m = m' := by omega
                exact Mask.signedMsg_succ T index m (by omega)
              · cases evalWithAnswerFn T (WCT9.signLayersBC cache index (m + 1) _) <;> exact RespAt.pure' _
theorem respAt_signPayload (T : Answers) (cache : T3.Cache) (message : Message) :
    RespAt T (HonestQ T) (signPayload cache message) := by
  change RespAt T (HonestQ T) (ClaudeWCT.WCT9.Rev3.signPayload cache message)
  rw [ClaudeWCT.WCT9.Rev3.signPayload_eq]
  refine RespAt.bind (RespAt.of_respects (respects_privateNonce message) fun _ h => honestQ_of_nonEnc h) ?_
  refine RespAt.bind (RespAt.of_respects (respects_digestSearch _ _ _ _) fun _ h => honestQ_of_nonEnc h) ?_
  generalize evalWithAnswerFn T (ClaudeWCT.WCT9.digestSearch (evalWithAnswerFn T (privateNonce message)) message 0
    ClaudeWCT.WCT9.digestAttemptLimit) = found
  rcases found with _ | ⟨counter, output⟩
  · exact RespAt.pure' _
  · dsimp only
    refine RespAt.bind (RespAt.of_respects (respects_signForest _ _) fun _ h => honestQ_of_nonEnc h) ?_
    refine RespAt.bind (respAt_signLayers T cache _ (Nat.mod_lt _ (by decide)) 4 le_rfl _ (fun m hm => ?_)) ?_
    · obtain rfl : m = 3 := by omega
      rw [ClaudeWCT.WCT9.signForest_root, ← Extract.honestForest_eq_wct9]
      exact Mask.signedMsg_top T _ (Nat.mod_lt _ (by decide))
    · generalize evalWithAnswerFn T (WCT9.signLayersBC cache (output.toNat % 2 ^ 31) 4 _) = pieces
      rcases pieces with _ | pieces <;> exact RespAt.pure' _
theorem respAt_sign (T : Answers) (published : T3.Cache) (request : Request) :
    RespAt T (HonestQ T) (FullGame.authenticatedSign published request) := by
  unfold FullGame.authenticatedSign
  refine RespAt.bind (RespAt.of_respects (respects_privateMac _) fun _ h => honestQ_of_nonEnc h) ?_
  split
  · exact respAt_signPayload T _ _
  · exact RespAt.pure' _
theorem respAt_keygen (T : Answers) : RespAt T (HonestQ T) keygen :=
  RespAt.of_respects respects_keygen fun _ h => honestQ_of_nonEnc h
end Enc
open ClaudeWCT.W9.T3.Security.Wots.Enc
theorem keygenCharge_congr {T T' : Answers} (h : AgreeOn (HonestQ T) T T') :
    keygenCharge T' = keygenCharge T := by
  unfold keygenCharge
  rw [(respAt_keygen T).queried_eq h]
theorem signCharge_congr {T T' : Answers} (h : AgreeOn (HonestQ T) T T') (published : T3.Cache)
    (request : Request) : signCharge T' published request = signCharge T published request := by
  unfold signCharge
  rw [(respAt_sign T published request).queried_eq h]
theorem offlineSign_congr {T T' : Answers} (h : AgreeOn (HonestQ T) T T') (published : T3.Cache)
    (request : Request) : offlineSign T' published request = offlineSign T published request := by
  unfold offlineSign
  rw [signCharge_congr h, (respAt_sign T published request).eval_eq h]
theorem offlineImpl_congr {T T' : Answers} (h : AgreeOn (HonestQ T) T T') (published : T3.Cache) :
    offlineImpl T' published = offlineImpl T published := by
  unfold offlineImpl
  have hs : offlineSign T' published = offlineSign T published := funext (offlineSign_congr h published)
  rw [hs]
theorem offlineGame_congr {T T' : Answers} (h : AgreeOn (HonestQ T) T T') (adversary : Final.AdversaryP) :
    offlineGame T' adversary = offlineGame T adversary := by
  unfold offlineGame offlineInteraction
  rw [keygenCharge_congr h, (respAt_keygen T).eval_eq h, offlineImpl_congr h]
theorem referenceGame_congr_honest {T T' : Answers} (h : AgreeOn (HonestQ T) T T')
    (adversary : Final.AdversaryP) (q : Nat) : referenceGame T' adversary q = referenceGame T adversary q := by
  unfold referenceGame
  rw [offlineGame_congr h]
theorem honestForest_congr_nonEnc {T T' : Answers} (h : ∀ q, Enc.NonEnc q → T' q = T q) (index : Nat) :
    Extract.honestForest T' index = Extract.honestForest T index := by
  rw [Extract.honestForest_eq_wct9, Extract.honestForest_eq_wct9]
  exact ClaudeWCT.WCT9.Wots.Enc.honestForest_congr h index
theorem wotsTree_congr_nonEnc {T T' : Answers} (h : ∀ q, Enc.NonEnc q → T' q = T q) (lay : Layer) (tree : Nat) :
    WCT9.wotsTree T' lay tree = WCT9.wotsTree T lay tree := by
  by_cases hl : lay = 0
  · subst hl
    rw [WCT9.wotsTree_top, WCT9.wotsTree_top]
    exact SigGolfCandidate.T3.Security.Wots.builtTree_congr_nonEnc h 0 tree
  · have h0 : 0 < 2 ^ height lay := by positivity
    have he := (Enc.respects_buildTreeP lay tree 0 []).eval_eq h
    rw [WCT9.eval_buildTreeP_result T' hl tree 0 [] (Cost.validDigits_nil lay) h0,
      WCT9.eval_buildTreeP_result T hl tree 0 [] (Cost.validDigits_nil lay) h0] at he
    exact congrArg Prod.fst he
theorem leafMsg_congr_nonEnc {T T' : Answers} (h : ∀ q, Enc.NonEnc q → T' q = T q) (L : LeafAddr) :
    leafMsg T' L = leafMsg T L := by
  unfold leafMsg
  split
  · unfold Extract.honestPair
    rw [wotsTree_congr_nonEnc h]
  · rw [honestForest_congr_nonEnc h _]
theorem nonEnc_of_honest {T T' : Answers} (h : AgreeOn (HonestQ T) T T') : ∀ q, Enc.NonEnc q → T' q = T q :=
  h.nonEnc fun _ hq => honestQ_of_nonEnc hq
theorem referenceSearch_congr_honest {T T' : Answers} (h : AgreeOn (HonestQ T) T T')
    (L : CanonGraph.LeafPos) : referenceSearch T' (leafOf L) = referenceSearch T (leafOf L) := by
  unfold referenceSearch
  rw [leafMsg_congr_nonEnc (nonEnc_of_honest h)]
  exact (respAt_referenceSearch T (HonestQ T) (leafOf L) (fun input hr => Or.inr ⟨L, hr⟩)).eval_eq h
theorem referenceDigits_congr_honest {T T' : Answers} (h : AgreeOn (HonestQ T) T T')
    (L : CanonGraph.LeafPos) : referenceDigits T' (leafOf L) = referenceDigits T (leafOf L) := by
  unfold referenceDigits
  rw [referenceSearch_congr_honest h]
theorem referenceInput_congr_honest {T T' : Answers} (h : AgreeOn (HonestQ T) T T')
    (L : CanonGraph.LeafPos) : referenceInput T' (leafOf L) = referenceInput T (leafOf L) := by
  unfold referenceInput
  rw [referenceSearch_congr_honest h, leafMsg_congr_nonEnc (nonEnc_of_honest h)]
end ClaudeWCT.W9.T3.Security.Wots
