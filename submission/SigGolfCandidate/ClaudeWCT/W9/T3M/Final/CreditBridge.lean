import SigGolfCandidate.ClaudeWCT.W9.T3M.Final.Budgets
import SigGolfCandidate.T3M.Verify.HashAgree

section
open OracleComp OracleSpec
namespace ClaudeWCT.W9.T3M.Final.Credit
open SigGolfCandidate.Legacy
open SigGolfCandidate.T3 (M Spec Layer Digest HashOutput HashInput route counterLimit decode shortHash
  publicHash pad64 header chainCount height maxDigit rowTweak nodeTweak digestHeader)
open SigGolfCandidate.T3M (mrealize mrealize_bind mrealize_map mrealize_shortHash toQ toQ_injOn Aligned PubGood
  isPublic allQ_pure allQ_bind allQ_map allQ_ite allQ_foldlM allQ_mapM)
open SigGolfCandidate.T3M.Verify (EncQ HashOk Agree agree_bind agree_bind_iff agree_map_iff agree_eval okHash
  okHash_eq okHash_eq_of_not_enc hashOk_okHash BadAns eval_liftQ)
open SigGolfCandidate.T3.Security.Wots.Enc (NonEnc nonEnc_prefixed nonEnc_chainInput nonEnc_of_hdr
  nodeTweak_ne_row rowTweak_layer)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
def NotEncS : Spec.Domain → Prop
  | .inl (.inr input) => ∀ lay : Layer, ¬ EncQ lay.val (toQ input)
  | _ => False
theorem rowWord_eq_rowTweak (lay : Layer) (routed : Nat) :
    (1#64 ++ SigGolfCandidate.T3.hyperWord lay.val routed) =
      rowTweak lay (routed / 2 ^ height lay) (routed % 2 ^ height lay) := by
  unfold rowTweak
  rw [Nat.div_add_mod']
theorem notEncS_of {input : HashInput} (hal : Aligned input) (hn : NonEnc (.inl (.inr input))) :
    NotEncS (.inl (.inr input)) := by
  rintro lay ⟨i, hi, hq, routed, hb⟩
  have hi' : Aligned i := ⟨by omega, by omega⟩
  have e : input = i := toQ_injOn hal hi' hq
  refine hn ⟨lay, routed / 2 ^ height lay, routed % 2 ^ height lay, ?_⟩
  rw [e, ← rowWord_eq_rowTweak]
  exact hb
theorem pad64_aligned' (y : HashInput) (hy : 0 < y.length) : Aligned (pad64 y) :=
  ⟨SigGolfCandidate.T3.Cost.pad64_positive y hy, SigGolfCandidate.T3.Cost.pad64_aligned y⟩
theorem notEnc_publicHash (y : HashInput) (hy : 0 < y.length) (hn : NonEnc (.inl (.inr (pad64 y)))) :
    AllQueriesSatisfy (publicHash y) NotEncS :=
  (allQueriesSatisfy_query_iff _ _).mpr (notEncS_of (pad64_aligned' y hy) hn)
theorem notEnc_shortHash (y : HashInput) (hy : 0 < y.length) (hn : NonEnc (.inl (.inr (pad64 y)))) :
    AllQueriesSatisfy (shortHash y) NotEncS := by
  unfold shortHash
  exact allQ_bind (notEnc_publicHash y hy hn) fun _ => allQ_pure _
theorem allQ_and {α : Type} {P P' : Spec.Domain → Prop} {p : M α} (h : AllQueriesSatisfy p P)
    (h' : AllQueriesSatisfy p P') : AllQueriesSatisfy p (fun q => P q ∧ P' q) := by
  induction p using OracleComp.inductionOn with
  | pure a => exact allQueriesSatisfy_pure _ _
  | query_bind q k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at h h' ⊢
    exact ⟨⟨h.1, h'.1⟩, fun u => ih u (h.2 u) (h'.2 u)⟩
theorem allQ_mono' {α : Type} {P P' : Spec.Domain → Prop} {p : M α} (h : AllQueriesSatisfy p P)
    (hP : ∀ q, P q → P' q) : AllQueriesSatisfy p P' := by
  induction p using OracleComp.inductionOn with
  | pure a => exact allQueriesSatisfy_pure _ _
  | query_bind q k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at h ⊢
    exact ⟨hP _ h.1, fun u => ih u (h.2 u)⟩
theorem notEnc_digest (rho : Digest) (m : SigGolfCandidate.T3.Message) (c : BitVec 32) :
    AllQueriesSatisfy (SigGolfCandidate.T3.digest rho m c) NotEncS := by
  unfold SigGolfCandidate.T3.digest
  apply notEnc_publicHash _ (by simp [SigGolfCandidate.T3.digestInput, bytesLE_length])
  apply nonEnc_of_hdr _ (digestHeader c) _
    (fun _ _ _ => SigGolfCandidate.T3.digestHeader_ne_rowTweak c _ _ _)
  unfold SigGolfCandidate.T3.digestInput
  rw [SigGolfCandidate.T3M.Extract.hdrBlock_pad64 _ (by simp only [List.length_append, bytesLE_length]; omega),
    SigGolfCandidate.T3M.Extract.hdrBlock_prefix]
theorem notEnc_recoverFts (sig : ClaudeWCT.WCT9.Signature) (index : Nat) (output : HashOutput) :
    AllQueriesSatisfy (ClaudeWCT.WCT9.recoverFts sig index output) NotEncS := by
  have h1 : AllQueriesSatisfy (ClaudeWCT.WCT9.recoverFts sig index output) (ClaudeWCT.WCT9.FtsQuery index) :=
    ClaudeWCT.WCT9.allQueriesSatisfy_of_bound (ClaudeWCT.WCT9.ftsBound_recoverFts index sig output)
  have h2 := ClaudeWCT.W9.T3M.pubGood_recoverFts sig index output
  refine allQ_mono' (allQ_and h1 h2) ?_
  rintro ((n | input) | c) ⟨hf, hg⟩
  · exact hg.1.elim
  · exact notEncS_of ⟨hg.2.1, hg.2.2⟩ (ClaudeWCT.WCT9.Wots.ftsQuery_nonEnc hf)
  · exact hg.1.elim
theorem notEnc_chain (lay : Layer) (tree leaf i start count : Nat) (v : Digest) :
    AllQueriesSatisfy (SigGolfCandidate.T3.chain lay tree leaf i start count v) NotEncS :=
  allQ_foldlM _ _ (fun _ _ => notEnc_shortHash _
    (by simp [SigGolfCandidate.T3.chainInput, bytesLE_length, SigGolfCandidate.T3.zero16])
    (nonEnc_chainInput _ _ _ _ _ _)) _
theorem notEnc_leafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    AllQueriesSatisfy (SigGolfCandidate.T3.leafHash lay tree leaf ends) NotEncS := by
  unfold SigGolfCandidate.T3.leafHash
  refine notEnc_shortHash _ ?_ (nonEnc_of_hdr _ _ (SigGolfCandidate.T3M.Extract.hdrBlock_leafInput _ _ _ _)
    (fun _ _ _ => SigGolfCandidate.T3.leafTweak_ne_rowTweak _ _ _ _ _ _))
  unfold SigGolfCandidate.T3.leafInput
  split <;> simp [bytesLE_length, SigGolfCandidate.T3.zero16]
theorem notEnc_nodeHash (lay tree heap : Nat) (left right : Digest)
    (hroot : 1 ≤ lay → lay < 4 → heap % 2 ^ 64 ≠ 1) :
    AllQueriesSatisfy (SigGolfCandidate.T3.nodeHash 3 lay tree heap left right) NotEncS := by
  unfold SigGolfCandidate.T3.nodeHash
  rw [List.append_assoc (bytesLE 16 left ++ bytesLE 16 (nodeTweak 3 lay tree heap))]
  refine notEnc_shortHash _ (by simp [bytesLE_length]) (nonEnc_of_hdr _ _ ?_
    (nodeTweak_ne_row 3 lay tree heap (by decide) (fun _ => hroot)))
  rw [SigGolfCandidate.T3M.Extract.hdrBlock_pad64 _ (by simp only [List.length_append, bytesLE_length]; omega),
    SigGolfCandidate.T3M.Extract.hdrBlock_prefix]
theorem notEnc_recoverLayer (sig : SigGolfCandidate.T3.Signature) (index : Nat) (lay : Layer) (digits : List Nat)
    (hlay : lay.val = 0) :
    AllQueriesSatisfy (SigGolfCandidate.T3.recoverLayer sig index lay digits) NotEncS := by
  unfold SigGolfCandidate.T3.recoverLayer
  exact allQ_bind (allQ_mapM _ _ fun _ => notEnc_chain _ _ _ _ _ _ _) fun _ =>
    allQ_bind (notEnc_leafHash _ _ _ _) fun _ =>
      allQ_foldlM _ _ (fun _ _ => notEnc_nodeHash _ _ _ _ _ (fun h1 _ => by omega)) _
theorem heap_ne_one {h j x : Nat} (hj : j + 1 < h) (hh : h ≤ 12) (hx : x < 2 ^ h) :
    (2 ^ (h - j - 1) + x / 2 ^ (j + 1)) % 2 ^ 64 ≠ 1 := by
  have h2 : 2 ≤ 2 ^ (h - j - 1) :=
    (show 2 = 2 ^ 1 by norm_num).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have h3 : 2 ^ (h - j - 1) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (by omega)
  have h4 : 2 ^ h ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) hh
  have h5 : x / 2 ^ (j + 1) ≤ x := Nat.div_le_self _ _
  have h6 : 2 ≤ 2 ^ (h - j - 1) + x / 2 ^ (j + 1) := le_trans h2 (Nat.le_add_right _ _)
  rw [Nat.mod_eq_of_lt (by omega)]
  omega
theorem notEnc_recoverLayerPair (sig : ClaudeWCT.WCT9.Signature) (index : Nat) (lay : Layer) (digits : List Nat) :
    AllQueriesSatisfy (ClaudeWCT.WCT9.recoverLayerPair sig index lay digits) NotEncS := by
  have hh : height lay ≤ 12 := by fin_cases lay <;> decide
  unfold ClaudeWCT.WCT9.recoverLayerPair
  exact allQ_bind (allQ_mapM _ _ fun _ => notEnc_chain _ _ _ _ _ _ _) fun _ =>
    allQ_bind (notEnc_leafHash _ _ _ _) fun _ =>
      allQ_bind (allQ_foldlM _ _ (fun _ j => notEnc_nodeHash _ _ _ _ _ (fun _ _ =>
        heap_ne_one (by have := j.isLt; omega) hh (Nat.mod_lt _ (Nat.two_pow_pos _)))) _) fun _ => allQ_pure _
theorem encInput_hdr (lay : Layer) (tree leaf : Nat) (msg : ClaudeWCT.WCT9.LayerMsg) (c : BitVec 32) :
    ((pad64 (ClaudeWCT.WCT9.layerEncodingInput lay tree leaf msg c)).drop 16).take 16 =
      bytesLE 16 (rowTweak lay tree leaf) := by
  cases msg with
  | forest root =>
    change SigGolfCandidate.T3M.Extract.hdrBlock (pad64 (bytesLE 16 root ++ bytesLE 16 (rowTweak lay tree leaf) ++
      bytesLE 4 c)) = _
    rw [SigGolfCandidate.T3M.Extract.hdrBlock_pad64 _ (by simp [bytesLE_length]),
      SigGolfCandidate.T3M.Extract.hdrBlock_prefix]
  | pair left right =>
    change SigGolfCandidate.T3M.Extract.hdrBlock (pad64 (bytesLE 16 left ++ bytesLE 16 (rowTweak lay tree leaf) ++
      bytesLE 4 c ++ bytesLE 12 (0 : BitVec 96) ++ bytesLE 16 right)) = _
    simp only [List.append_assoc]
    rw [← List.append_assoc (bytesLE 16 left)]
    rw [SigGolfCandidate.T3M.Extract.hdrBlock_pad64 _ (by simp [bytesLE_length]),
      SigGolfCandidate.T3M.Extract.hdrBlock_prefix]
theorem encInput_pos (lay : Layer) (tree leaf : Nat) (msg : ClaudeWCT.WCT9.LayerMsg) (c : BitVec 32) :
    0 < (ClaudeWCT.WCT9.layerEncodingInput lay tree leaf msg c).length := by
  cases msg <;> simp [ClaudeWCT.WCT9.layerEncodingInput, SigGolfCandidate.T3.encodingInput,
    ClaudeWCT.WCT9.pairEncodingInputP, bytesLE_length]
theorem encQ_layer (lay lay' : Layer) (tree leaf : Nat) (msg : ClaudeWCT.WCT9.LayerMsg) (c : BitVec 32)
    (h : EncQ lay'.val (toQ (pad64 (ClaudeWCT.WCT9.layerEncodingInput lay tree leaf msg c)))) : lay' = lay := by
  obtain ⟨i, hi, hq, routed, hb⟩ := h
  have hi' : Aligned i := ⟨by omega, by omega⟩
  have e := toQ_injOn (pad64_aligned' _ (encInput_pos lay tree leaf msg c)) hi' hq
  rw [← e, encInput_hdr, rowWord_eq_rowTweak] at hb
  exact (rowTweak_layer (bytesLE_injective hb)).symm
variable {f g : Hash}
theorem agree_mrealize {α : Type} {p : M α} (hp : AllQueriesSatisfy p NotEncS)
    (hfg : ∀ q, (∀ lay : Layer, ¬ EncQ lay.val q) → f q = g q) : Agree f g (mrealize 0 p) := by
  induction p using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind q k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at hp
    rw [mrealize_bind]
    rcases q with (n | input) | c
    · exact hp.1.elim
    · have e : mrealize 0 (liftM (Spec.query (.inl (.inr input))) : M _) =
          (liftM (OracleSpec.query (spec := HashSpec) (toQ input)) : OracleComp HashSpec _) := by
        simp [mrealize, SigGolfCandidate.T3M.machineHandler]; exact id_map _
      rw [e]
      exact agree_bind ⟨hfg _ hp.1, trivial⟩ (ih _ (hp.2 _))
    · exact hp.1.elim
theorem agree_mrealize_bind {α β : Type} (p : M α) (k : α → M β) :
    Agree f g (mrealize 0 (p >>= k)) ↔
      Agree f g (mrealize 0 p) ∧
        Agree f g (mrealize 0 (k (evalWithAnswerFn (machineAnswers f 0) p))) := by
  rw [mrealize_bind, agree_bind_iff, eval_mrealize]
theorem eval_shortHash (hash : Hash) (y : HashInput) :
    evalWithAnswerFn (machineAnswers hash 0) (shortHash y) =
      (hash (toQ (pad64 y))).extractLsb' 0 128 := by
  rw [← eval_mrealize, mrealize_shortHash, evalWithAnswerFn_map, eval_liftQ]
theorem hfg_ok (hash : Hash) : ∀ q, (∀ lay : Layer, ¬ EncQ lay.val q) → hash q = okHash hash q :=
  fun _ h => (okHash_eq_of_not_enc hash h).symm
theorem okHash_producer (hash : Hash) (lay : Layer) (tree leaf : Nat) (msg : ClaudeWCT.WCT9.LayerMsg)
    (c : BitVec 32) {digits : List Nat}
    (hp : ClaudeWCT.WCT9.producerDecode lay
      ((hash (toQ (pad64 (ClaudeWCT.WCT9.layerEncodingInput lay tree leaf msg c)))).extractLsb' 0 128) =
        some digits) :
    hash (toQ (pad64 (ClaudeWCT.WCT9.layerEncodingInput lay tree leaf msg c))) =
      okHash hash (toQ (pad64 (ClaudeWCT.WCT9.layerEncodingInput lay tree leaf msg c))) := by
  refine (okHash_eq hash ?_).symm
  rintro ⟨lay', hq, ds, hds, hlow⟩
  obtain rfl := encQ_layer lay lay' tree leaf msg c hq
  rw [ClaudeWCT.WCT9.producerDecode_decode hp] at hds
  cases hds
  have := ClaudeWCT.WCT9.producerDecode_credit hp
  omega
theorem agree_layers (hash : Hash) (sig : ClaudeWCT.WCT9.Signature) (index : Nat) :
    ∀ n, n ≤ 4 → ∀ msg root counters,
      evalWithAnswerFn (machineAnswers hash 0) (ClaudeWCT.WCT9.expandLayersBC sig index n msg) =
        some (root, counters) →
      ∀ w : ClaudeWCT.WCT9.Witness, w.signature = sig →
        (∀ lay : Layer, lay.val < n → w.counters lay = counters.getD lay.val 0) →
        Agree hash (okHash hash) (mrealize 0 (ClaudeWCT.WCT9.verifyLayersBC w index n msg)) := by
  intro n
  induction n with
  | zero =>
      intro _ msg root counters he
      simp [ClaudeWCT.WCT9.expandLayersBC] at he
  | succ n ih =>
      intro hn msg root counters he w hw hc
      simp only [ClaudeWCT.WCT9.expandLayersBC, evalWithAnswerFn_bind] at he
      cases hs : evalWithAnswerFn (machineAnswers hash 0) (ClaudeWCT.WCT9.layerCounterSearch (Fin.ofNat 4 n)
        (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 msg 0
        (ClaudeWCT.WCT9.searchLimit (Fin.ofNat 4 n))) with
      | none => simp only [hs, evalWithAnswerFn_pure, reduceCtorEq] at he
      | some found =>
          obtain ⟨counter, digits⟩ := found
          have hlim := ClaudeWCT.WCT9.searchLimit_le (Fin.ofNat 4 n)
          obtain ⟨_, hbound, hsd⟩ := ClaudeWCT.WCT9.layerCounterSearch_some_search (machineAnswers hash 0)
            (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 msg
            (ClaudeWCT.WCT9.searchLimit (Fin.ofNat 4 n)) 0 counter digits
            (by unfold counterLimit at hlim; omega) hs
          have hdecode := ClaudeWCT.WCT9.producerDecode_decode hsd
          have hnot : ¬counter.toNat ≥ counterLimit := by omega
          have hlay := ClaudeWCT.WCT9.ofNat_layer_val n (by omega)
          simp only [hs] at he
          rw [eval_shortHash] at hsd
          have hq := okHash_producer hash _ _ _ msg counter hsd
          by_cases hn0 : n = 0
          · subst hn0
            simp only [if_true, evalWithAnswerFn_bind, evalWithAnswerFn_pure, Option.some.injEq,
              Prod.mk.injEq] at he
            obtain ⟨-, rfl⟩ := he
            have hcounter : w.counters (Fin.ofNat 4 0) = counter := by
              rw [hc _ (by rw [hlay]; omega), hlay]; rfl
            simp only [ClaudeWCT.WCT9.verifyLayersBC, hcounter, hnot, ite_false]
            refine (agree_mrealize_bind _ _).mpr ⟨?_, ?_⟩
            · rw [mrealize_shortHash, agree_map_iff]
              exact ⟨hq, trivial⟩
            · simp only [if_true, ↓reduceIte]
              rw [ClaudeWCT.WCT9.verifyTop_of_decode _ _ hdecode, mrealize_map, agree_map_iff]
              exact agree_mrealize (notEnc_recoverLayer _ _ _ _ (by rfl)) (hfg_ok hash)
          · simp only [hn0, if_false, evalWithAnswerFn_bind] at he
            cases hr : evalWithAnswerFn (machineAnswers hash 0) (ClaudeWCT.WCT9.expandLayersBC sig index n
              (.pair (evalWithAnswerFn (machineAnswers hash 0)
                (ClaudeWCT.WCT9.recoverLayerPair sig index (Fin.ofNat 4 n) digits)).1
                (evalWithAnswerFn (machineAnswers hash 0)
                (ClaudeWCT.WCT9.recoverLayerPair sig index (Fin.ofNat 4 n) digits)).2)) with
            | none => simp only [hr, evalWithAnswerFn_pure, reduceCtorEq] at he
            | some previous =>
                obtain ⟨previousRoot, previousCounters⟩ := previous
                simp only [hr, evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at he
                obtain ⟨-, rfl⟩ := he
                have hlen := (ClaudeWCT.WCT9.expandLayersBC_verified _ sig index n (by omega) _ _ _ hr).1
                have hcounter : w.counters (Fin.ofNat 4 n) = counter := by
                  rw [hc _ (by rw [hlay]; omega), hlay,
                    List.getD_append_right previousCounters [counter] 0 n (by omega), hlen]
                  simp
                simp only [ClaudeWCT.WCT9.verifyLayersBC, hcounter, hnot, ite_false]
                refine (agree_mrealize_bind _ _).mpr ⟨?_, ?_⟩
                · rw [mrealize_shortHash, agree_map_iff]
                  exact ⟨hq, trivial⟩
                · rw [hdecode]
                  simp only [hn0, if_false]
                  refine (agree_mrealize_bind _ _).mpr
                    ⟨agree_mrealize (notEnc_recoverLayerPair _ _ _ _) (hfg_ok hash), ?_⟩
                  rw [hw]
                  refine ih (by omega) _ _ _ hr w hw (fun lay hsmall => ?_)
                  rw [hc lay (by omega), List.getD_append previousCounters [counter] 0 lay.val (by omega)]
theorem expandN_layers (A : SigGolfCandidate.T3.Correctness.Answers) (m : SigGolfCandidate.T3.Message) (pk : Digest)
    (σ : ClaudeWCT.WCT9.Signature) (N : HashOutput) (wt : ClaudeWCT.WCT9.Witness)
    (he : evalWithAnswerFn A (ClaudeWCT.W9.T3M.expandN m pk σ) = some (N, wt)) :
    ∃ root counters, evalWithAnswerFn A (ClaudeWCT.WCT9.expandLayersBC σ (ClaudeWCT.WCT9.digestIndex N) 4
        (.forest (evalWithAnswerFn A (ClaudeWCT.WCT9.recoverFts σ (ClaudeWCT.WCT9.digestIndex N) N)))) = some (root, counters) ∧
      ∀ lay : Layer, wt.counters lay = counters.getD lay.val 0 := by
  simp only [ClaudeWCT.W9.T3M.expandN, evalWithAnswerFn_bind] at he
  cases hd : evalWithAnswerFn A (ClaudeWCT.WCT9.digestSearch σ.rho m 0 ClaudeWCT.WCT9.digestAttemptLimit) with
  | none => simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some found =>
      obtain ⟨counter, output⟩ := found
      simp only [hd, evalWithAnswerFn_bind] at he
      cases hl : evalWithAnswerFn A (ClaudeWCT.WCT9.expandLayersBC σ (ClaudeWCT.WCT9.digestIndex output) 4
          (.forest (evalWithAnswerFn A (ClaudeWCT.WCT9.recoverFts σ (ClaudeWCT.WCT9.digestIndex output) output)))) with
      | none => simp only [hl, evalWithAnswerFn_pure, reduceCtorEq] at he
      | some layers =>
          obtain ⟨root, counters⟩ := layers
          simp only [hl] at he
          split at he
          · simp only [evalWithAnswerFn_pure, reduceCtorEq] at he
          · simp only [evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            exact ⟨root, counters, hl, fun _ => rfl⟩
theorem agree_verifyP (hash : Hash) (m : SigGolfCandidate.T3.Message) (pk : Digest) (σ : ClaudeWCT.WCT9.Signature)
    (N : HashOutput) (wt : ClaudeWCT.WCT9.Witness)
    (hx : evalWithAnswerFn (machineAnswers hash 0) (ClaudeWCT.W9.T3M.expandN m pk σ) = some (N, wt)) :
    Agree hash (okHash hash) (mrealize 0 (ClaudeWCT.W9.T3M.verifyP m pk (ClaudeWCT.W9.T3M.witEnc N wt))) := by
  have F := ClaudeWCT.W9.T3M.expandN_facts _ m pk σ N wt hx
  obtain ⟨root, counters, hl, hcs⟩ := expandN_layers _ m pk σ N wt hx
  have hv : ClaudeWCT.W9.T3M.verifyP m pk (ClaudeWCT.W9.T3M.witEnc N wt) =
      SigGolfCandidate.T3.digest wt.signature.rho m wt.digestCounter >>=
        ClaudeWCT.W9.T3M.verifyTailP pk (ClaudeWCT.W9.T3M.witEnc N wt) := by
    rw [ClaudeWCT.W9.T3M.verifyP_eq_tail]
    unfold ClaudeWCT.W9.T3M.digestP
    rw [ClaudeWCT.W9.T3M.wdcWord_witEnc, ClaudeWCT.W9.T3M.wdc_witEnc, ClaudeWCT.W9.T3M.wrho_witEnc,
      if_neg (by have := F.dc; omega), bind_map_left]
  rw [hv, agree_mrealize_bind]
  refine ⟨agree_mrealize (notEnc_digest _ _ _) (hfg_ok hash), ?_⟩
  rw [F.sig, F.digest, ClaudeWCT.W9.T3M.verifyTailP_shaped pk N _ F.adm, ClaudeWCT.W9.T3M.witDecP_witEnc,
    ClaudeWCT.W9.T3M.padDecP_witEnc]
  have hidx : ClaudeWCT.WCT9.digestIndex N < 2 ^ 31 := ClaudeWCT.WCT9.digestIndex_lt N
  unfold ClaudeWCT.W9.T3M.verifyPadsTail
  simp only [F.adm, Bool.not_true, Bool.false_eq_true, if_false, ClaudeWCT.W9.T3M.recoverFtsP_zero,
    ClaudeWCT.W9.T3M.verifyLayersBCP_zero _ _ hidx]
  refine (agree_mrealize_bind _ _).mpr ⟨agree_mrealize (notEnc_recoverFts _ _ _) (hfg_ok hash), ?_⟩
  refine (agree_mrealize_bind _ _).mpr ⟨?_, ?_⟩
  · rw [F.sig]
    exact agree_layers hash σ _ 4 le_rfl _ root counters hl wt F.sig (fun lay _ => hcs lay)
  · split <;> trivial
theorem digestCap_okHash (hash : Hash) (m : SigGolfCandidate.T3.Message) (pk : Digest)
    (σ : ClaudeWCT.WCT9.Signature) (N : HashOutput) (wt : ClaudeWCT.WCT9.Witness)
    (hx : evalWithAnswerFn (machineAnswers hash 0) (ClaudeWCT.W9.T3M.expandN m pk σ) = some (N, wt)) :
    DigestCapOk (okHash hash) m (ClaudeWCT.W9.T3M.witEnc N wt) := by
  have F := ClaudeWCT.W9.T3M.expandN_facts _ m pk σ N wt hx
  have hd : ClaudeWCT.W9.T3M.digestP m (ClaudeWCT.W9.T3M.witEnc N wt) =
      some <$> SigGolfCandidate.T3.digest wt.signature.rho m wt.digestCounter := by
    unfold ClaudeWCT.W9.T3M.digestP
    rw [ClaudeWCT.W9.T3M.wdcWord_witEnc, ClaudeWCT.W9.T3M.wdc_witEnc, ClaudeWCT.W9.T3M.wrho_witEnc,
      if_neg (by have := F.dc; omega)]
  have hag : Agree hash (okHash hash) (mrealize 0 (ClaudeWCT.W9.T3M.digestP m (ClaudeWCT.W9.T3M.witEnc N wt))) := by
    rw [hd, mrealize_map, agree_map_iff]
    exact agree_mrealize (notEnc_digest _ _ _) (hfg_ok hash)
  intro N' hN'
  rw [← agree_eval hag, eval_mrealize, hd, evalWithAnswerFn_map, F.sig, F.digest] at hN'
  cases hN'
  exact F.cap
variable {I : ClaudeWCT.W9.T3M.Images}
set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits ClaudeWCT.W9.T3M.submission
  SigGolfCandidate.Legacy.Output SigGolfCandidate.Legacy.Input
set_option maxRecDepth 100000 in
theorem expand_witness (P : Pending I) (hash : Hash) (m : Message) (pk : PublicKey) (s : Bytes 5456)
    (w : Bytes 21488) (he : ((ClaudeWCT.W9.T3M.submission I).runWith hash .expand (m, pk, s)).value = some w) :
    ∃ N wt, evalWithAnswerFn (machineAnswers hash 0) (ClaudeWCT.W9.T3M.expandN m pk (sigDec s)) = some (N, wt) ∧
      w = ClaudeWCT.W9.T3M.witEnc N wt := by
  have h := congrArg (evalWithAnswerFn hash) (expand_value P m pk s)
  rw [evalWithAnswerFn_map, eval_mrealize hash 0 (ClaudeWCT.W9.T3M.expandB m pk (sigDec s)),
    ClaudeWCT.W9.T3M.eval_expandB] at h
  unfold Submission.runWith at he
  rw [h] at he
  cases hx : evalWithAnswerFn (machineAnswers hash 0) (ClaudeWCT.W9.T3M.expandN m pk (sigDec s)) with
  | none => rw [hx] at he; cases he
  | some x =>
      rw [hx] at he
      obtain ⟨N, wt⟩ := x
      exact ⟨N, wt, rfl, (Option.some.inj he).symm⟩
set_option maxRecDepth 100000 in
theorem verify_run_ok (P : Pending I) (hash : Hash) (m : Message) (pk : PublicKey) (w : Bytes 21488)
    (hagree : Agree hash (okHash hash) (mrealize 0 (ClaudeWCT.W9.T3M.verifyP m pk w))) :
    (ClaudeWCT.W9.T3M.submission I).runWith hash .verify (m, pk, w) =
      (ClaudeWCT.W9.T3M.submission I).runWith (okHash hash) .verify (m, pk, w) := by
  have ha : Agree hash (okHash hash) ((ClaudeWCT.W9.T3M.submission I).run .verify (m, pk, w)) := by
    rw [← agree_map_iff (fun r => r.value.isSome), verify_value P m pk w]
    exact hagree
  exact agree_eval ha
theorem honest_success_verify_cf (sub : Submission) (hash : Hash) (sk : SecretKey) (m : Message)
    (h : (evalWithAnswerFn hash (sub.honest sk m)).success = true) :
    ∃ pk σ w, (sub.runWith hash .expand (m, pk, σ)).value = some w ∧
      (sub.runWith hash .verify (m, pk, w)).value.isSome = true ∧
      (evalWithAnswerFn hash (sub.honest sk m)).verificationCycles =
        (sub.runWith hash .verify (m, pk, w)).cycles + witnessCycles sub.sizes.witness := by
  unfold Submission.honest at h ⊢
  simp only [evalWithAnswerFn_bind] at h ⊢
  generalize evalWithAnswerFn hash (sub.run .keygen sk) = k at h ⊢
  rcases hk : k.value with _ | ⟨pk, cache⟩
  · simp [hk] at h
  simp only [hk, evalWithAnswerFn_bind] at h ⊢
  generalize evalWithAnswerFn hash (sub.run .sign (sk, cache, m)) = s at h ⊢
  rcases hs : s.value with _ | σ
  · simp [hs] at h
  simp only [hs, evalWithAnswerFn_bind] at h ⊢
  generalize he : evalWithAnswerFn hash (sub.run .expand (m, pk, σ)) = e at h ⊢
  rcases he' : e.value with _ | w
  · simp [he'] at h
  simp only [he', evalWithAnswerFn_bind, evalWithAnswerFn_pure] at h ⊢
  refine ⟨pk, σ, w, ?_, h, rfl⟩
  unfold Submission.runWith
  rw [he, he']
end ClaudeWCT.W9.T3M.Final.Credit
end
