import SigGolfCandidate.Research_V7Composed198Gate
import SigGolfCandidate.ClaudeWCT_W9_T3M_Final_Budgets
import SigGolfCandidate.T3M_Verify_HashAgree

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
  nodeTweak_ne_row rowTweak_layer hyperH_layer NotHyper notHyper_of_marker nonEnc_pad64_long leafInput_long
  chainCount_ge4)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
def NotEncS : Spec.Domain → Prop
  | .inl (.inr input) => ∀ lay : Layer, ¬ EncQ lay.val (toQ input)
  | _ => False
/-- C2/C3 (FULL): an encoding query has any row-tweak high word (EncQ), so a non-encoding query is told apart by its
length or a non-hyper 16-byte header (`NonEnc`, S23b). Adapted from b3cc11b. -/
theorem notEncS_of {input : HashInput} (hal : Aligned input) (hn : NonEnc (.inl (.inr input))) :
    NotEncS (.inl (.inr input)) := by
  rintro lay ⟨i, hi, hq, routed, hp, hb⟩
  have hi' : Aligned i := ⟨by omega, by omega⟩
  have e : input = i := toQ_injOn hal hi' hq
  refine hn ⟨by rw [e]; exact hi, lay, routed / 2 ^ height lay, routed % 2 ^ height lay, hp, ?_⟩
  rw [e, Nat.div_add_mod']
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
theorem notEnc_halfHash (high : Bool) (y : HashInput) (hy : 0 < y.length) (hn : NonEnc (.inl (.inr (pad64 y)))) :
    AllQueriesSatisfy (ClaudeWCT.WCT9.halfHash high y) NotEncS := by
  rw [ClaudeWCT.WCT9.halfHash_eq]
  exact allQ_bind (notEnc_publicHash y hy hn) fun _ => allQ_pure _
theorem allQ_bind_support {α β : Type} {P : Spec.Domain → Prop} {p : M α} {f : α → M β}
    (hp : AllQueriesSatisfy p P) (hf : ∀ a ∈ support p, AllQueriesSatisfy (f a) P) :
    AllQueriesSatisfy (p >>= f) P := by
  induction p using OracleComp.inductionOn with
  | pure a =>
    rw [pure_bind]
    exact hf a (by simp)
  | query_bind t mx ih =>
    rw [bind_assoc]
    rw [allQueriesSatisfy_query_bind_iff] at hp ⊢
    refine ⟨hp.1, fun u => ih u (hp.2 u) fun a ha => hf a ?_⟩
    rw [mem_support_bind_iff]
    exact ⟨u, by simp, ha⟩
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
    (notHyper_of_marker (by rw [SigGolfCandidate.T3.digestHeader_marker]; decide))
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
/-- C3: a leaf block carries its leaf's hyper label; its length (at least 4 chain ends) keeps it apart. -/
theorem notEnc_leafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) (hlen : 4 ≤ ends.length) :
    AllQueriesSatisfy (SigGolfCandidate.T3.leafHash lay tree leaf ends) NotEncS := by
  unfold SigGolfCandidate.T3.leafHash
  have hl := leafInput_long lay tree leaf ends hlen
  exact notEnc_shortHash _ (by omega) (nonEnc_pad64_long _ hl)
/-- Pairing stage 1: a chain row of the current scheme (F or G format) is no encoding row (header marker). -/
theorem nonEnc_chainInputW (lay : Layer) (tree leaf i s : Nat) (v : Digest) :
    NonEnc (.inl (.inr (pad64 (ClaudeWCT.WCT9.chainInputW lay tree leaf i s v)))) := by
  apply nonEnc_of_hdr _ (SigGolfCandidate.T3.chainHeader lay tree leaf i s) _
    (notHyper_of_marker (by
      unfold SigGolfCandidate.T3.tweakMarker
      have := SigGolfCandidate.T3.chainHeader_firstByte lay tree leaf i s; omega))
  rw [ClaudeWCT.WCT9.chainInputW_padded]
  exact ClaudeWCT.WCT9.chainInputW_header _ _ _ _ _ _
theorem notEnc_chainW (lay : Layer) (tree leaf i start count : Nat) (v : Digest) :
    AllQueriesSatisfy (ClaudeWCT.WCT9.chainW lay tree leaf i start count v) NotEncS :=
  allQ_foldlM _ _ (fun _ _ => notEnc_halfHash _ _
    (by rw [ClaudeWCT.WCT9.chainInputW_length]; omega)
    (nonEnc_chainInputW _ _ _ _ _ _)) _
/-- Witness stack: the WOTS chain of the T3 text (`topChain = chainW 0 0` on the top, `chain` below). -/
theorem notEnc_layChain (lay : Layer) (tree leaf i start count : Nat) (v : Digest) :
    AllQueriesSatisfy (SigGolfCandidate.T3.layChain lay tree leaf i start count v) NotEncS := by
  unfold SigGolfCandidate.T3.layChain
  split
  · rw [← ClaudeWCT.WCT9.chainW_top_eq]; exact notEnc_chainW _ _ _ _ _ _ _
  · exact notEnc_chain _ _ _ _ _ _ _
theorem notEnc_lowerLeafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) (hlen : 4 ≤ ends.length) :
    AllQueriesSatisfy (ClaudeWCT.WCT9.lowerLeafHash lay tree leaf ends) NotEncS := by
  have hl := leafInput_long lay tree leaf ends hlen
  have e := ClaudeWCT.W9.T3M.leafInputW_length lay tree leaf 0 0 ends
  unfold ClaudeWCT.WCT9.lowerLeafHash ClaudeWCT.WCT9.leafHashW ClaudeWCT.WCT9.lowerHash
  exact notEnc_halfHash _ _ (by rw [e]; omega) (nonEnc_pad64_long _ (by rw [e]; exact hl))
/-- C2: a packed lower node word has marker `128 + heap`, so it is no hyper word. -/
theorem lowerTweak_notHyper (lay tree heap : Nat) (hh : heap < 128) :
    NotHyper (ClaudeWCT.WCT9.lowerTweak lay tree heap) := by
  apply notHyper_of_marker
  unfold ClaudeWCT.WCT9.lowerTweak ClaudeWCT.WCT9.lowerNodeWord ClaudeWCT.WCT9.lowerK
  rw [SigGolfCandidate.T3.append64_marker, BitVec.toNat_add, BitVec.toNat_ofNat, SigGolfCandidate.T3.hyperWord_toNat]
  omega
theorem notEnc_lowerNodeHash (lay tree heap : Nat) (left right : Digest) (hh : lay ≠ 0 → heap < 128) :
    AllQueriesSatisfy (ClaudeWCT.WCT9.lowerNodeHash lay tree heap left right) NotEncS := by
  unfold ClaudeWCT.WCT9.lowerNodeHash ClaudeWCT.WCT9.lowerHash ClaudeWCT.WCT9.merkleNodeInput
  rw [List.append_assoc (bytesLE 16 left ++ bytesLE 16 (ClaudeWCT.WCT9.merkleTweak lay tree heap))]
  refine notEnc_halfHash _ _ (by simp [bytesLE_length])
    (nonEnc_of_hdr _ (ClaudeWCT.WCT9.merkleTweak lay tree heap) ?_ ?_)
  · rw [SigGolfCandidate.T3M.Extract.hdrBlock_pad64 _ (by simp only [List.length_append, bytesLE_length]; omega),
      SigGolfCandidate.T3M.Extract.hdrBlock_prefix]
  · by_cases h0 : lay = 0
    · subst h0; rw [ClaudeWCT.WCT9.merkleTweak_top]; exact nodeTweak_ne_row 3 0 tree heap (by decide) (fun _ _ => rfl)
    · rw [ClaudeWCT.WCT9.merkleTweak_lower h0]; exact lowerTweak_notHyper _ _ _ (hh h0)
theorem mapM_support_length {α β : Type} (f : α → M β) :
    ∀ (xs : List α) (ys : List β), ys ∈ support (xs.mapM f) → ys.length = xs.length
  | [], ys, h => by simpa using h
  | x :: xs, ys, h => by
    rw [List.mapM_cons, mem_support_bind_iff] at h
    obtain ⟨y, -, h⟩ := h
    rw [mem_support_bind_iff] at h
    obtain ⟨zs, hzs, h⟩ := h
    simp only [support_pure, Set.mem_singleton_iff] at h
    subst h
    simp [mapM_support_length f xs zs hzs]
/-- Legacy node hash, top tree only (C2/C3: a legacy lower node tweak is a hyper word with high word `heap`, which
`EncQ` no longer tells apart by its header). -/
theorem notEnc_nodeHash (lay tree heap : Nat) (left right : Digest)
    (hroot : lay < 4 → lay = 0) :
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
  exact allQ_bind_support (allQ_mapM _ _ fun _ => notEnc_layChain _ _ _ _ _ _ _) fun _ hends =>
    allQ_bind (notEnc_leafHash _ _ _ _ (by
      rw [mapM_support_length _ _ _ hends, List.length_finRange]; exact chainCount_ge4 _)) fun _ =>
      allQ_foldlM _ _ (fun _ _ => notEnc_nodeHash _ _ _ _ _ (fun _ => hlay)) _
/-- img-v6: a top node hash with a nonce pad is a node row (node tweak header), never an encoding row. -/
theorem notEnc_topNodeHashN (heap n : Nat) (left right : Digest) :
    AllQueriesSatisfy (SigGolfCandidate.T3.topNodeHashN heap n left right) NotEncS := by
  unfold SigGolfCandidate.T3.topNodeHashN SigGolfCandidate.T3.topNodeInput SigGolfCandidate.T3.nonceBytes
  rw [← ClaudeWCT.WCT9.halfHash_eq_projHash,
    List.append_assoc (bytesLE 16 left ++ bytesLE 16 (nodeTweak 3 0 0 heap))]
  refine notEnc_halfHash _ _ (by simp [bytesLE_length]) (nonEnc_of_hdr _ _ ?_
    (nodeTweak_ne_row 3 0 0 heap (by decide) (fun _ _ => rfl)))
  rw [SigGolfCandidate.T3M.Extract.hdrBlock_pad64 _ (by simp only [List.length_append, bytesLE_length]; omega),
    SigGolfCandidate.T3M.Extract.hdrBlock_prefix]
/-- img-v6: the nonce-reading top verifier makes no encoding query once its answer decodes. -/
theorem notEnc_verifyTopN (sig : ClaudeWCT.WCT9.Signature) (nonces : List Nat) (index : Nat) {answer : Digest}
    {digits : List Nat} (h : decode 0 answer = some digits) :
    AllQueriesSatisfy (ClaudeWCT.WCT9.verifyTopN sig nonces index answer) NotEncS := by
  unfold ClaudeWCT.WCT9.verifyTopN
  rw [ClaudeWCT.WCT9.topDecodeRun_of_decode h]
  refine allQ_map _ (allQ_bind_support (allQ_mapM _ _ fun _ => notEnc_layChain _ _ _ _ _ _ _) fun _ hends =>
    allQ_bind (notEnc_leafHash _ _ _ _ (by
      rw [mapM_support_length _ _ _ hends, List.length_finRange]; exact chainCount_ge4 _)) fun _ =>
      allQ_foldlM _ _ (fun _ _ => ?_) _)
  dsimp only
  split
  · exact notEnc_topNodeHashN _ _ _ _
  · exact notEnc_nodeHash _ _ _ _ _ (fun _ => rfl)
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
theorem heap_lt128 {h j x : Nat} (hj : j + 1 < h) (hh : h ≤ 7) (hx : x < 2 ^ h) :
    2 ^ (h - j - 1) + x / 2 ^ (j + 1) < 128 := by
  have h5 : x / 2 ^ (j + 1) < 2 ^ (h - j - 1) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show h - j - 1 + (j + 1) = h by omega]
    exact hx
  have h3 : 2 ^ (h - j - 1) ≤ 2 ^ 6 := Nat.pow_le_pow_right (by decide) (by omega)
  have h64 : (2 : Nat) ^ 6 = 64 := by norm_num
  omega
theorem notEnc_recoverLayerPair (sig : ClaudeWCT.WCT9.Signature) (index : Nat) (lay : Layer) (digits : List Nat) :
    AllQueriesSatisfy (ClaudeWCT.WCT9.recoverLayerPair sig index lay digits) NotEncS := by
  have hh : lay.val ≠ 0 → height lay ≤ 7 := by fin_cases lay <;> decide
  unfold ClaudeWCT.WCT9.recoverLayerPair
  exact allQ_bind_support (allQ_mapM _ _ fun _ => notEnc_chainW _ _ _ _ _ _ _) fun _ hends =>
    allQ_bind (notEnc_lowerLeafHash _ _ _ _ (by
      rw [mapM_support_length _ _ _ hends, List.length_finRange]; exact chainCount_ge4 _)) fun _ =>
      allQ_bind (allQ_foldlM _ _ (fun _ j => notEnc_lowerNodeHash _ _ _ _ _ (fun h0 =>
        heap_lt128 (by have := j.isLt; omega) (hh h0) (Nat.mod_lt _ (Nat.two_pow_pos _)))) _) fun _ => allQ_pure _
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
  obtain ⟨i, hi, hq, routed, hp, hb⟩ := h
  have hi' : Aligned i := ⟨by omega, by omega⟩
  have e := toQ_injOn (pad64_aligned' _ (encInput_pos lay tree leaf msg c)) hi' hq
  rw [← e, encInput_hdr] at hb
  have hb' := bytesLE_injective hb
  unfold rowTweak at hb'
  exact (hyperH_layer hb').symm
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
theorem mrealize_encodingHash (lay : Layer) (y : HashInput) :
    mrealize 0 (ClaudeWCT.WCT9.encodingHash lay y) =
      ClaudeWCT.WCT9.encodingAnswer lay <$> (liftM (HashSpec.query (toQ (pad64 y))) : OracleComp HashSpec _) := by
  rw [ClaudeWCT.WCT9.encodingHash, mrealize_map, SigGolfCandidate.T3M.mrealize_publicHash]
theorem eval_encodingHash (hash : Hash) (lay : Layer) (y : HashInput) :
    evalWithAnswerFn (machineAnswers hash 0) (ClaudeWCT.WCT9.encodingHash lay y) =
      ClaudeWCT.WCT9.encodingAnswer lay (hash (toQ (pad64 y))) := by
  rw [← eval_mrealize, mrealize_encodingHash, evalWithAnswerFn_map, eval_liftQ]
theorem hfg_ok (hash : Hash) : ∀ q, (∀ lay : Layer, ¬ EncQ lay.val q) → hash q = okHash hash q :=
  fun _ h => (okHash_eq_of_not_enc hash h).symm
theorem okHash_producer (hash : Hash) (lay : Layer) (tree leaf : Nat) (msg : ClaudeWCT.WCT9.LayerMsg)
    (c : BitVec 32) {digits : List Nat}
    (hp : ClaudeWCT.WCT9.producerDecode lay
      (ClaudeWCT.WCT9.encodingAnswer lay (hash (toQ (pad64 (ClaudeWCT.WCT9.layerEncodingInput lay tree leaf msg c))))) =
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
      split at he
      next counter digits hs =>
          have hlim := ClaudeWCT.WCT9.searchLimit_le (Fin.ofNat 4 n)
          obtain ⟨_, hbound, hsd⟩ := ClaudeWCT.WCT9.layerCounterSearch_some_search (machineAnswers hash 0)
            _ _ _ _ _ 0 counter digits
            (by unfold counterLimit at hlim; omega) hs
          have hdecode := ClaudeWCT.WCT9.producerDecode_decode hsd
          have hnot : ¬counter.toNat ≥ ClaudeWCT.WCT9.verifyWindow := ClaudeWCT.WCT9.ctr_not_ge_verifyWindow counter
          have hlay := ClaudeWCT.WCT9.ofNat_layer_val n (by omega)
          have hproducerRaw := hsd
          rw [eval_encodingHash] at hsd
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
            · rw [mrealize_encodingHash, agree_map_iff]
              exact ⟨hq, trivial⟩
            · simp only [if_true, ↓reduceIte]
              rw [ClaudeWCT.WCT9.verifyTop_of_decode _ _ hdecode, mrealize_map, agree_map_iff]
              exact agree_mrealize (notEnc_recoverLayer _ _ _ _ (by rfl)) (hfg_ok hash)
          · simp only [hn0, if_false, evalWithAnswerFn_bind] at he
            split at he
            next previousRoot previousCounters hr =>
                simp only [evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at he
                obtain ⟨-, rfl⟩ := he
                have hlen := (ClaudeWCT.WCT9.expandLayersBC_verified _ sig index n (by omega) _ _ _ hr).1
                have hcounter : w.counters (Fin.ofNat 4 n) = counter := by
                  rw [hc _ (by rw [hlay]; omega), hlay,
                    List.getD_append_right previousCounters [counter] 0 n (by omega), hlen]
                  simp
                simp only [ClaudeWCT.WCT9.verifyLayersBC, hcounter, hnot, ite_false]
                refine (agree_mrealize_bind _ _).mpr ⟨?_, ?_⟩
                · rw [mrealize_encodingHash, agree_map_iff]
                  exact ⟨hq, trivial⟩
                · rw [hdecode]
                  have hgood := ClaudeWCT.WCT9.producerDecode_lowerRankGood
                    (lay := Fin.ofNat 4 n) (by intro h; have := congrArg Fin.val h; rw [hlay] at this; exact hn0 this) hproducerRaw
                  simp only [hn0, if_false,
                    ClaudeWCT.WCT9.recoverLayerPairGuard_of_good _ _ _ _ _ hgood, bind_map_left]
                  refine (agree_mrealize_bind _ _).mpr
                    ⟨agree_mrealize (notEnc_recoverLayerPair _ _ _ _) (hfg_ok hash), ?_⟩
                  rw [hw]
                  refine ih (by omega) _ _ _ hr w hw (fun lay hsmall => ?_)
                  rw [hc lay (by omega), List.getD_append previousCounters [counter] 0 lay.val (by omega)]
            next => simp only [evalWithAnswerFn_pure, reduceCtorEq] at he
      next => simp only [evalWithAnswerFn_pure, reduceCtorEq] at he
theorem expandN_layers (A : SigGolfCandidate.T3.Correctness.Answers) (m : SigGolfCandidate.T3.Message) (pk : Digest)
    (σ : ClaudeWCT.WCT9.Signature) (N : HashOutput) (wt : ClaudeWCT.WCT9.Witness)
    (he : evalWithAnswerFn A (ClaudeWCT.W9.T3M.expandN0 m pk σ) = some (N, wt)) :
    ∃ root counters, evalWithAnswerFn A (ClaudeWCT.WCT9.expandLayersBC σ (ClaudeWCT.WCT9.digestIndex N) 4
        (.pair (evalWithAnswerFn A (ClaudeWCT.WCT9.recoverFts σ (ClaudeWCT.WCT9.digestIndex N) N)).1
          (evalWithAnswerFn A (ClaudeWCT.WCT9.recoverFts σ (ClaudeWCT.WCT9.digestIndex N) N)).2)) = some (root, counters) ∧
      ∀ lay : Layer, wt.counters lay = counters.getD lay.val 0 := by
  simp only [ClaudeWCT.W9.T3M.expandN0, evalWithAnswerFn_bind] at he
  cases hd : evalWithAnswerFn A (ClaudeWCT.WCT9.digestSearch σ.rho m 0 ClaudeWCT.WCT9.digestAttemptLimit) with
  | none => simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some found =>
      obtain ⟨counter, output⟩ := found
      simp only [hd, evalWithAnswerFn_bind] at he
      cases hl : evalWithAnswerFn A (ClaudeWCT.WCT9.expandLayersBC σ (ClaudeWCT.WCT9.digestIndex output) 4
          (.pair (evalWithAnswerFn A (ClaudeWCT.WCT9.recoverFts σ (ClaudeWCT.WCT9.digestIndex output) output)).1
            (evalWithAnswerFn A (ClaudeWCT.WCT9.recoverFts σ (ClaudeWCT.WCT9.digestIndex output) output)).2)) with
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
    (hx : evalWithAnswerFn (machineAnswers hash 0) (ClaudeWCT.W9.T3M.expandN0 m pk σ) = some (N, wt)) :
    Agree hash (okHash hash) (mrealize 0 (ClaudeWCT.W9.T3M.verifyP m pk (ClaudeWCT.W9.T3M.witEnc N wt))) := by
  have F := ClaudeWCT.W9.T3M.expandN0_facts _ m pk σ N wt hx
  obtain ⟨root, counters, hl, hcs⟩ := expandN_layers _ m pk σ N wt hx
  have hv : ClaudeWCT.W9.T3M.verifyP m pk (ClaudeWCT.W9.T3M.witEnc N wt) =
      SigGolfCandidate.T3.digest wt.signature.rho m wt.digestCounter >>=
        ClaudeWCT.W9.T3M.verifyTailP pk (ClaudeWCT.W9.T3M.witEnc N wt) := by
    rw [ClaudeWCT.W9.T3M.verifyP_eq_tail]
    unfold ClaudeWCT.W9.T3M.digestP
    rw [ClaudeWCT.W9.T3M.wdc_witEnc, ClaudeWCT.W9.T3M.wrho_witEnc,
      if_neg (by have := wt.digestCounter.isLt; unfold ClaudeWCT.WCT9.digestVerifyWindow; omega), bind_map_left]
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
  · rw [F.sig, ClaudeWCT.W9.T3M.verifyLayersBCP_zero _ _ hidx 4 le_rfl]
    exact agree_layers hash σ _ 4 le_rfl _ root counters hl wt F.sig (fun lay _ => hcs lay)
  · split <;> trivial
theorem digestCap_okHash (hash : Hash) (m : SigGolfCandidate.T3.Message) (pk : Digest)
    (σ : ClaudeWCT.WCT9.Signature) (N : HashOutput) (wt : ClaudeWCT.WCT9.Witness)
    (hx : evalWithAnswerFn (machineAnswers hash 0) (ClaudeWCT.W9.T3M.expandN0 m pk σ) = some (N, wt)) :
    DigestCapOk (okHash hash) m (ClaudeWCT.W9.T3M.witEnc N wt) := by
  have F := ClaudeWCT.W9.T3M.expandN0_facts _ m pk σ N wt hx
  have hd : ClaudeWCT.W9.T3M.digestP m (ClaudeWCT.W9.T3M.witEnc N wt) =
      some <$> SigGolfCandidate.T3.digest wt.signature.rho m wt.digestCounter := by
    unfold ClaudeWCT.W9.T3M.digestP
    rw [ClaudeWCT.W9.T3M.wdc_witEnc, ClaudeWCT.W9.T3M.wrho_witEnc,
      if_neg (by have := wt.digestCounter.isLt; unfold ClaudeWCT.WCT9.digestVerifyWindow; omega)]
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
-- r3h HonestN: legacy (5310) expand_witness / verify_run_ok removed (legacy Budgets pipeline removed).
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

namespace ClaudeWCT.W9.T3M.Final.Credit
open OracleComp OracleSpec
open SigGolfCandidate.Legacy
open SigGolfCandidate.T3 (Layer Digest HashInput pad64)
open SigGolfCandidate.T3M (toQ mrealize mrealize_map)
open SigGolfCandidate.T3M.Verify

theorem hfg_okBy (floors : Layer → Nat) (high : Bool) (hash : Hash) :
    ∀ q, (∀ lay : Layer, ¬ EncQ lay.val q) → hash q = okHashBy floors high hash q :=
  fun _ h => (okHashBy_eq_of_not_enc floors high hash h).symm

theorem mrealize_verificationHash (lay : Layer) (high : Bool) (y : HashInput) :
    mrealize 0 (ClaudeWCT.WCT9.verificationHash lay high y) =
      ClaudeWCT.WCT9.verificationAnswer lay high <$>
        (liftM (HashSpec.query (toQ (pad64 y))) : OracleComp HashSpec _) := by
  rw [ClaudeWCT.WCT9.verificationHash, mrealize_map, SigGolfCandidate.T3M.mrealize_publicHash]

/-- An encoding answer accepted by the canonical producer (with the honest hint on the top) is not replaced by
`okHashBy` once its path-aware credit reaches the floor. -/
theorem okHashBy_accepted_credit (floors : Layer → Nat) (high : Bool) (hash : Hash) (lay : Layer)
    (floor tree leaf : Nat) (msg : ClaudeWCT.WCT9.LayerMsg) (c : BitVec 32)
    {digits : List Nat} {low : Bool}
    (hhigh : lay = 0 → high = ClaudeWCT.WCT9.encodingHigh 0
      (hash (toQ (pad64 (ClaudeWCT.WCT9.layerEncodingInput lay tree leaf msg c)))))
    (hf : floors lay ≤ ClaudeWCT.WCT9.CanonicalPolicy.credit lay low digits)
    (hp : ClaudeWCT.WCT9.CanonicalPolicy.producerDecodeOut lay floor
        (hash (toQ (pad64 (ClaudeWCT.WCT9.layerEncodingInput lay tree leaf msg c)))) = some (digits, low)) :
    hash (toQ (pad64 (ClaudeWCT.WCT9.layerEncodingInput lay tree leaf msg c))) =
      okHashBy floors high hash (toQ (pad64 (ClaudeWCT.WCT9.layerEncodingInput lay tree leaf msg c))) := by
  refine (okHashBy_eq floors high hash ?_).symm
  rintro ⟨lay', hq, ds, hds, hlow⟩
  have hll := encQ_layer lay lay' tree leaf msg c hq
  subst lay'
  obtain ⟨hl, hpd⟩ := ClaudeWCT.WCT9.CanonicalPolicy.producerDecodeOut_spec hp
  have hs := ClaudeWCT.WCT9.CanonicalPolicy.producerDecodeAt_spec hpd
  set a := hash (toQ (pad64 (ClaudeWCT.WCT9.layerEncodingInput lay tree leaf msg c)))
  have hva : ClaudeWCT.WCT9.verificationAnswer lay high a = ClaudeWCT.WCT9.encodingAnswer lay a ∧
      ClaudeWCT.WCT9.verificationLow lay high a = low := by
    by_cases h0 : lay = 0
    · subst h0
      rw [hhigh rfl, ClaudeWCT.WCT9.verificationAnswer_honest, ClaudeWCT.WCT9.verificationLow_honest, hl]
      exact ⟨rfl, rfl⟩
    · rw [ClaudeWCT.WCT9.verificationAnswer_lower lay h0, ClaudeWCT.WCT9.verificationLow_lower lay h0, hl]
      exact ⟨rfl, rfl⟩
  rw [hva.1, hs.1] at hds
  cases hds
  rw [hva.2] at hlow
  have hc := hs.2.1
  unfold ClaudeWCT.WCT9.CanonicalPolicy.credit at hf
  omega
end ClaudeWCT.W9.T3M.Final.Credit

namespace ClaudeWCT.W9.T3M.Final.Credit.Paired
open OracleComp OracleSpec
open SigGolfCandidate.Legacy
open SigGolfCandidate.T3 (Layer Digest route counterLimit)
open SigGolfCandidate.T3M (mrealize)
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem agree_layers (floors : Layer → Nat) (hash : Hash) (sig : SigGolfCandidate.Research.SharedForest.Signature) (index : Nat) :
    ∀ n, n ≤ 4 → ∀ msg result,
      evalWithAnswerFn (machineAnswers hash 0)
        (recoverHintedLayers sig index ((sig.layers 0).path topJ) n msg) = some result →
      (∀ lay : Layer, lay.val < n →
        floors lay ≤ CanonicalPolicy.credit lay (result.lows.getD lay.val true) (result.digits.getD lay.val [])) →
      ∀ w : SigGolfCandidate.Research.SharedForest.Witness, w.signature = sig →
        (∀ lay : Layer, lay.val < n → w.counters lay = result.counters.getD lay.val 0) →
        w.topHigh = !(result.lows.getD 0 true) →
        Agree hash (okHashBy floors w.topHigh hash) (mrealize 0 (verifyLayers w index n msg)) := by
  intro n
  induction n with
  | zero =>
      intro _ msg result he
      simp [recoverHintedLayers] at he
  | succ n ih =>
      intro hn msg result he hf w hw hc hh
      simp only [recoverHintedLayers, evalWithAnswerFn_bind] at he
      split at he
      next counter digits low hs =>
          have hlim := searchLimit_le (Fin.ofNat 4 n)
          obtain ⟨_, hbound, hproducer⟩ := canonical_search_some (machineAnswers hash 0) _
            _ _ _ _
            _ 0 counter digits low (by unfold counterLimit at hlim; omega) hs
          have hpd := (CanonicalPolicy.producerDecodeOut_spec hproducer)
          have hdecode := (CanonicalPolicy.producerDecodeAt_spec hpd.2).1
          have hnot : ¬counter.toNat ≥ verifyWindow := ctr_not_ge_verifyWindow counter
          have hlay := ofNat_layer_val n (by omega)
          have hevp : evalWithAnswerFn (machineAnswers hash 0)
              (SigGolfCandidate.T3.publicHash (layerEncodingInput (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2
                (route index (Fin.ofNat 4 n)).1 msg counter)) =
              hash (SigGolfCandidate.T3M.toQ (SigGolfCandidate.T3.pad64 (layerEncodingInput (Fin.ofNat 4 n)
                (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 msg counter))) := by
            rw [← eval_mrealize, SigGolfCandidate.T3M.mrealize_publicHash, eval_liftQ]
          rw [hevp] at hproducer
          by_cases hn0 : n = 0
          · subst n
            simp only [if_true, evalWithAnswerFn_bind, evalWithAnswerFn_pure, Option.some.injEq] at he
            subst result
            have hfloor : floors (Fin.ofNat 4 0) ≤ CanonicalPolicy.credit (Fin.ofNat 4 0) low digits :=
              hf _ (by decide)
            have hhigh : w.topHigh = encodingHigh 0 (hash (SigGolfCandidate.T3M.toQ (SigGolfCandidate.T3.pad64
                (layerEncodingInput (Fin.ofNat 4 0) (route index (Fin.ofNat 4 0)).2
                  (route index (Fin.ofNat 4 0)).1 msg counter)))) := by
              rw [hh, encodingHigh_top]
              simp only [List.getD_cons_zero]
              rw [hpd.1, hevp]
              rfl
            have hq := okHashBy_accepted_credit floors w.topHigh hash _ _ _ _ msg counter
              (fun _ => hhigh) hfloor hproducer
            have hcounter : w.counters (Fin.ofNat 4 0) = counter := by
              rw [hc _ (by rw [hlay]; omega), hlay]; rfl
            simp only [verifyLayers, hcounter, hnot, ite_false]
            refine (agree_mrealize_bind _ _).mpr ⟨?_, ?_⟩
            · rw [mrealize_verificationHash, agree_map_iff]
              exact ⟨hq, trivial⟩
            · simp only [if_true, ↓reduceIte]
              have hva : evalWithAnswerFn (machineAnswers hash 0) (verificationHash (Fin.ofNat 4 0) w.topHigh
                  (layerEncodingInput (Fin.ofNat 4 0) (route index (Fin.ofNat 4 0)).2 (route index (Fin.ofNat 4 0)).1
                    msg counter)) =
                  evalWithAnswerFn (machineAnswers hash 0) (encodingHash (Fin.ofNat 4 0)
                    (layerEncodingInput (Fin.ofNat 4 0) (route index (Fin.ofNat 4 0)).2 (route index (Fin.ofNat 4 0)).1
                      msg counter)) := by
                rw [← eval_mrealize, ← eval_mrealize, mrealize_verificationHash, mrealize_encodingHash,
                  evalWithAnswerFn_map, evalWithAnswerFn_map, eval_liftQ, hhigh]
                exact verificationAnswer_honest 0 _
              have hdec' : CanonicalPolicy.decode (Fin.ofNat 4 0) (evalWithAnswerFn (machineAnswers hash 0)
                  (encodingHash (Fin.ofNat 4 0) (layerEncodingInput (Fin.ofNat 4 0) (route index (Fin.ofNat 4 0)).2
                    (route index (Fin.ofNat 4 0)).1 msg counter))) = some digits := hdecode
              rw [hva]
              exact agree_mrealize (notEnc_verifyTopN _ _ _ hdec') (hfg_okBy floors w.topHigh hash)
          · simp only [hn0, if_false, evalWithAnswerFn_bind] at he
            split at he
            next previous hr =>
                simp only [evalWithAnswerFn_pure, Option.some.injEq] at he
                subst result
                obtain ⟨hlen, hdlen, hllen, _⟩ :=
                  recoverHintedLayers_verified (machineAnswers hash 0) sig index n (by omega) _ _ hr
                have hfloor : floors (Fin.ofNat 4 n) ≤ CanonicalPolicy.credit (Fin.ofNat 4 n) low digits := by
                  have h := hf (Fin.ofNat 4 n) (by rw [hlay]; omega)
                  simpa only [hlay, List.getD_append_right previous.digits [digits] [] n (by omega),
                    List.getD_append_right previous.lows [low] true n (by omega),
                    hdlen, hllen, Nat.sub_self, List.getD_cons_zero] using h
                have hnonzero : (Fin.ofNat 4 n : Layer) ≠ 0 := by
                  intro h; have := congrArg Fin.val h; rw [hlay] at this; exact hn0 this
                have hq := okHashBy_accepted_credit floors w.topHigh hash _ _ _ _ msg counter
                  (fun h0 => absurd h0 hnonzero) hfloor hproducer
                have hcounter : w.counters (Fin.ofNat 4 n) = counter := by
                  rw [hc _ (by rw [hlay]; omega), hlay,
                    List.getD_append_right previous.counters [counter] 0 n (by omega), hlen]
                  simp
                simp only [verifyLayers, hcounter, hnot, ite_false,
                  verificationHash_lower (Fin.ofNat 4 n) hnonzero]
                refine (agree_mrealize_bind _ _).mpr ⟨?_, ?_⟩
                · rw [mrealize_encodingHash, agree_map_iff]
                  exact ⟨hq, trivial⟩
                · have hgood := (CanonicalPolicy.producerDecodeAt_spec hpd.2).2.2.2.resolve_left hnonzero
                  have hdecode' : CanonicalPolicy.decode (Fin.ofNat 4 n) (evalWithAnswerFn (machineAnswers hash 0)
                      (encodingHash (Fin.ofNat 4 n) (layerEncodingInput (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2
                        (route index (Fin.ofNat 4 n)).1 msg counter))) = some digits := by
                    rw [eval_encodingHash]; rw [hevp] at hdecode; exact hdecode
                  have hgood' : lowerRankGood (evalWithAnswerFn (machineAnswers hash 0)
                      (encodingHash (Fin.ofNat 4 n) (layerEncodingInput (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2
                        (route index (Fin.ofNat 4 n)).1 msg counter))) := by
                    rw [eval_encodingHash]; rw [hevp] at hgood; exact hgood
                  simp only [hn0, if_false, hdecode',
                    recoverLayerPairGuard_of_good _ _ _ _ _ hgood', bind_map_left]
                  refine (agree_mrealize_bind _ _).mpr
                    ⟨agree_mrealize (notEnc_recoverLayerPair _ _ _ _) (hfg_okBy floors w.topHigh hash), ?_⟩
                  rw [hw]
                  refine ih (by omega) _ _ hr (fun lay hsmall => ?_) w hw (fun lay hsmall => ?_) ?_
                  · have h := hf lay (by omega)
                    simpa only [List.getD_append previous.digits [digits] [] lay.val (by omega),
                      List.getD_append previous.lows [low] true lay.val (by omega)] using h
                  · rw [hc lay (by omega), List.getD_append previous.counters [counter] 0 lay.val (by omega)]
                  · rw [hh, List.getD_append previous.lows [low] true 0 (by omega)]
            next => simp only [evalWithAnswerFn_pure, reduceCtorEq] at he
      next => simp only [evalWithAnswerFn_pure, reduceCtorEq] at he
end ClaudeWCT.W9.T3M.Final.Credit.Paired

namespace ClaudeWCT.W9.T3M.Final.Credit.Paired
open OracleComp OracleSpec
open SigGolfCandidate.Legacy
open SigGolfCandidate.T3 (Layer Digest HashOutput HashInput pad64 shortHash)
open SigGolfCandidate.T3M (mrealize allQ_bind allQ_mapM allQ_foldlM allQ_pure)
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
open SigGolfCandidate.T3.Security.Wots.Enc (nonEnc_of_hdr notHyper_of_marker notHyper_of_tag)
open SphincsSecurity (bytesLE bytesLE_length)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem notEnc_ftsChain (index coord selected i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (WCT9.chain index coord selected i start count value) NotEncS := by
  unfold WCT9.chain
  refine allQ_foldlM _ _ (fun v step => ?_) _
  rw [← WCT9.halfHash_eq_projHash]
  refine notEnc_halfHash _ _ (by rw [WCT9.ftsChainInputW_length]; omega) ?_
  -- witness stack: G chains 1, 3 (`value | header | 0 | 0`) carry the same header block
  unfold WCT9.ftsChainInputW
  split
  · rw [List.append_assoc (bytesLE 16 v ++ _)]
    exact nonEnc_of_hdr _ _ (hdrBlock_pad64_prefix _ _ _ (bytesLE_length _ _))
      (notHyper_of_marker
        (ne_of_gt (lt_of_lt_of_le (by decide) (ftsChainHeaderP_tweakMarker _ _ _ _ _ 0))))
  · unfold WCT9.chainInput
    rw [List.append_assoc (SigGolfCandidate.T3.zero16 ++ _)]
    -- C2/C3 (#866): `NonEnc` excludes every hyper tweak whatever its high word (`NotHyper`).
    exact nonEnc_of_hdr _ _ (hdrBlock_pad64_prefix _ _ _ (by simp [SigGolfCandidate.T3.zero16]))
      (notHyper_of_marker
        (ne_of_gt (lt_of_lt_of_le (by decide) (ftsChainHeaderP_tweakMarker _ _ _ _ _ 0))))

theorem notEnc_ftsLeaf (index coord selected : Nat) (pad : Digest) (ends : List Digest) :
    AllQueriesSatisfy (leafHashP index coord selected pad ends) NotEncS := by
  unfold leafHashP
  apply notEnc_shortHash _ (by simp [leafInputP, bytesLE_length])
  unfold leafInputP
  rw [List.append_assoc (bytesLE 16 _ ++ _)]
  exact nonEnc_of_hdr _ _ (hdrBlock_pad64_prefix _ _ _ (bytesLE_length _ _))
    (notHyper_of_tag (by rw [ftsLeafHeader_tweakTag]; decide))

/-- C1: the paired leaf of heap `heap` (either half) makes the same non-encoding query. -/
theorem notEnc_ftsLeafH (heap index coord selected : Nat) (pad : Digest) (ends : List Digest) :
    AllQueriesSatisfy (leafHashH heap index coord selected pad ends) NotEncS :=
  allQ_ftsHash_of_shortHash _ _ (notEnc_ftsLeaf index coord selected pad ends)

theorem notEnc_topLow (coord index heap : Nat) (hcoord : coord < 9) (left pad right : Digest) :
    AllQueriesSatisfy (shortHash (wctTopInput coord index heap left pad right)) NotEncS := by
  apply notEnc_shortHash _ (by simp [wctTopInput, bytesLE_length])
  apply nonEnc_of_hdr _ (wctNodeHeader coord index heap) ?_
    (notHyper_of_tag (by rw [wctNodeHeader_tweakTag hcoord]; split <;> decide))
  unfold wctTopInput
  rw [List.append_assoc (bytesLE 16 left ++ bytesLE 16 _)]
  exact hdrBlock_pad64_prefix _ _ _ (bytesLE_length _ _)

theorem notEnc_outer (coord index heap : Nat) (hcoord : coord < 9) (left right : Digest) :
    AllQueriesSatisfy (sharedOuterHash coord index heap left right) NotEncS := by
  unfold sharedOuterHash
  split
  · exact notEnc_topLow _ _ _ hcoord _ _ _
  · exact allQ_highHash_of_shortHash _ (notEnc_topLow _ _ _ hcoord _ _ _)

theorem notEnc_node (first : Bool) (coord index heap : Nat) (hcoord : coord < 9)
    (pads : Nat → PairRoot) (left right : Digest) :
    AllQueriesSatisfy (sharedNode first coord index heap pads left right) NotEncS := by
  unfold sharedNode
  split
  · exact notEnc_outer _ _ _ hcoord _ _
  · split
    · split
      · exact allQ_highHash_of_shortHash _ (notEnc_topLow _ _ _ hcoord _ _ _)
      · exact notEnc_topLow _ _ _ hcoord _ _ _
    · change AllQueriesSatisfy (ftsHash heap (wctTopInput coord index heap left 0 right)) NotEncS
      exact allQ_ftsHash_of_shortHash _ _ (notEnc_topLow _ _ _ hcoord _ _ _)

theorem notEnc_inner (first : Bool) (index coord : Nat) (hcoord : coord < 9) (selected : Child)
    (word : Rank) (values : Fin 6 → Digest) (path : Nat → Digest) (prev : PairRoot) :
    AllQueriesSatisfy (recoverSharedInner first index coord selected word values path prev) NotEncS := by
  unfold recoverSharedInner
  exact allQ_bind (allQ_mapM _ _ fun _ => notEnc_ftsChain _ _ _ _ _ _ _) fun _ =>
    allQ_bind (notEnc_ftsLeafH _ _ _ _ _ _) fun _ =>
      allQ_foldlM _ _ (fun _ _ => notEnc_node _ _ _ _ hcoord _ _ _) _

theorem notEnc_pair (index : Nat) (pair : Fin 4) (selected : Selection) (aWord bWord : Rank)
    (opened : PairOpening) (prev : PairRoot) :
    AllQueriesSatisfy (recoverPair index pair.val selected aWord bWord opened prev) NotEncS := by
  unfold recoverPair
  have hpair := pair.isLt
  exact allQ_bind (notEnc_inner _ _ _ (by omega) _ _ _ _ _) fun _ =>
    allQ_bind (notEnc_inner _ _ _ (by omega) _ _ _ _ _) fun _ =>
      allQ_bind (notEnc_outer _ _ _ (by omega) _ _) fun _ => allQ_pure _

theorem notEnc_singleton (index : Nat) (selected : Child) (word : Rank) (opened : SingletonOpening)
    (prev : PairRoot) : AllQueriesSatisfy (recoverSingleton index selected word opened prev) NotEncS := by
  unfold recoverSingleton
  exact allQ_bind (notEnc_inner _ _ _ (by decide) _ _ _ _ _) fun _ =>
    allQ_bind (notEnc_outer _ _ _ (by decide) _ _) fun _ => allQ_pure _

theorem notEnc_forest (index : Nat) (selected : ForestSelection) (words : ForestWords) (opened : ForestOpening) :
    AllQueriesSatisfy (recoverForest index selected words opened) NotEncS := by
  unfold recoverForest
  exact allQ_bind (allQ_foldlM _ _ (fun _ _ => notEnc_pair _ _ _ _ _ _ _) _) fun _ =>
    notEnc_singleton _ _ _ _ _

theorem recovered_credit_floors (answers : SigGolfCandidate.T3.Correctness.Answers)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (index : Nat) (other : Digest)
    (msg : LayerMsg) (result : RecoveredLayers)
    (he : evalWithAnswerFn answers (recoverHintedLayers sig index other 4 msg) = some result)
    (hh : policyHintsValid sig.policyHints result.digits result.lows = true) :
    CreditFloors (fun lay => min 74
      (CanonicalPolicy.credit lay (result.lows.getD lay.val true) (result.digits.getD lay.val []))) := by
  apply creditFloors_clip
  exact policyHints_credit_sum _ _ _ hh (fun lay =>
    (recoverHintedLayers_credit answers sig index other 4 le_rfl msg result he).2.2 lay lay.isLt)

theorem agree_verify (hash : Hash) (message : SigGolfCandidate.T3.Message) (pk : Digest)
    (w : SigGolfCandidate.Research.SharedForest.Witness) (output : HashOutput) (result : RecoveredLayers)
    (hd : evalWithAnswerFn (machineAnswers hash 0) (SigGolfCandidate.T3.digest w.signature.rho message w.digestCounter) = output)
    (hr : evalWithAnswerFn (machineAnswers hash 0)
      (recoverHintedLayers w.signature (digestIndex output) ((w.signature.layers 0).path topJ) 4
        (.pair (evalWithAnswerFn (machineAnswers hash 0) (recoverForest (digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) w.signature.forest)).1
          (evalWithAnswerFn (machineAnswers hash 0) (recoverForest (digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) w.signature.forest)).2)) = some result)
    (hh : policyHintsValid w.signature.policyHints result.digits result.lows = true)
    (hc : ∀ lay, w.counters lay = result.counters.getD lay.val 0)
    (htop : w.topHigh = !(result.lows.getD 0 true)) :
    ∃ floors : Layer → Nat, CreditFloors floors ∧
      Agree hash (okHashBy floors w.topHigh hash)
        (mrealize 0 (SigGolfCandidate.Research.SharedForest.verify message pk w)) := by
  let floors : Layer → Nat := fun lay =>
    min 74 (CanonicalPolicy.credit lay (result.lows.getD lay.val true) (result.digits.getD lay.val []))
  refine ⟨floors, recovered_credit_floors _ _ _ _ _ result hr hh, ?_⟩
  unfold SigGolfCandidate.Research.SharedForest.verify
  split
  · trivial
  · refine (agree_mrealize_bind _ _).mpr ⟨agree_mrealize (notEnc_digest _ _ _) (hfg_okBy floors w.topHigh hash), ?_⟩
    rw [hd]
    split
    · trivial
    · refine (agree_mrealize_bind _ _).mpr
        ⟨agree_mrealize (notEnc_forest _ _ _ _) (hfg_okBy floors w.topHigh hash), ?_⟩
      refine (agree_mrealize_bind _ _).mpr ⟨?_, ?_⟩
      · exact agree_layers floors hash w.signature (digestIndex output) 4 le_rfl _ result hr
          (fun lay _ => Nat.min_le_right _ _) w rfl (fun lay _ => hc lay) htop
      · split <;> trivial
end ClaudeWCT.W9.T3M.Final.Credit.Paired

namespace ClaudeWCT.W9.T3M.Final.Credit.Paired
open OracleComp OracleSpec SigGolfCandidate.Legacy
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.T3M (mrealize)
open SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.T3M.Final.Paired
variable {I : ClaudeWCT.W9.T3M.Images}
set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits ClaudeWCT.W9.T3M.Paired.submission
  SigGolfCandidate.Legacy.Output SigGolfCandidate.Legacy.Input
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem expand_witness (E : EncodingFacts) (F : SourceQueries) (P : Final.Paired.Pending I)
    (hash : Hash) (m : Message) (pk : PublicKey) (s : Bytes 5239) (w : Bytes 22012)
    (he : ((Final.Paired.submission I).runWith hash .expand (m,pk,s)).value=some w) :
    ∃sig output wt,evalWithAnswerFn (machineAnswers hash 0)
      (ClaudeWCT.W9.T3M.Paired.expandN m pk sig)=some (output,wt) ∧
      w=ClaudeWCT.W9.T3M.Paired.witEncN output wt := by
  have h := congrArg (evalWithAnswerFn hash) (Final.Paired.expand_value E F P m pk s)
  rw [evalWithAnswerFn_map,eval_mrealize hash 0 (ClaudeWCT.W9.T3M.Paired.expandB m pk (Final.Paired.sigDecC s)),
    ClaudeWCT.W9.T3M.Paired.eval_expandB] at h
  unfold Submission.runWith at he
  rw [h] at he
  cases hx : evalWithAnswerFn (machineAnswers hash 0) (ClaudeWCT.W9.T3M.Paired.expandN m pk (Final.Paired.sigDecC s)) with
  | none => rw [hx] at he; cases he
  | some x =>
    rw [hx] at he
    obtain ⟨output,wt⟩ := x
    exact ⟨_,output,wt,hx,(Option.some.inj he).symm⟩

theorem verify_run_agree (E : EncodingFacts) (F : SourceQueries) (P : Final.Paired.Pending I)
    (f g : Hash) (m : Message) (pk : PublicKey) (w : Bytes 22012)
    (hagree : Agree f g (mrealize 0 (ClaudeWCT.W9.T3M.Paired.verifyP m pk w))) :
    (Final.Paired.submission I).runWith f .verify (m,pk,w)=
      (Final.Paired.submission I).runWith g .verify (m,pk,w) := by
  have ha : Agree f g ((Final.Paired.submission I).run .verify (m,pk,w)) := by
    rw [←agree_map_iff (fun r=>r.value.isSome),Final.Paired.verify_value E F P m pk w]
    exact hagree
  exact agree_eval ha
end ClaudeWCT.W9.T3M.Final.Credit.Paired

namespace ClaudeWCT.W9.T3M.Final.Credit.Paired
open OracleComp OracleSpec SigGolfCandidate.Legacy
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.T3M (mrealize)
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M.Paired (ftsP_accepted)
open W9Machine
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem agree_verifyP_source_of (f g : Hash) (message : SigGolfCandidate.T3.Message) (pk : Digest)
    (wb : WBytes) (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (hrho : wrho wb=w.signature.rho) (hdc : wdc wb=w.digestCounter)
    (hd : evalWithAnswerFn (machineAnswers f 0)
      (SigGolfCandidate.T3.digest w.signature.rho message w.digestCounter)=output)
    (hg : output.toNat/2^242%16384<734)
    (hr : ∀ k : Fin 9,rawForestRank output k.val<563)
    (hf : SharedV3.forest wb (WCT9.digestIndex output) (rawChildFromOutput output)
      (fun k=>WCT9.embed (forestRank output k.val)) =
      recoverForest (WCT9.digestIndex output) (forestSelectionFromOutput output)
        (forestWordsFromOutput output) w.signature.forest)
    (hl : ∀left right,layersCanonicalBC wb (WCT9.digestIndex output) 4 (.pair left right)=
      SigGolfCandidate.Research.SharedForest.verifyLayers w (WCT9.digestIndex output) 4 (.pair left right))
    (hagree : Agree f g (mrealize 0 (SigGolfCandidate.Research.SharedForest.verify message pk w))) :
    Agree f g (mrealize 0 (ClaudeWCT.W9.T3M.Paired.verifyP message pk wb)) := by
  have hb : ¬w.digestCounter.toNat≥WCT9.digestVerifyWindow := by
    exact Nat.not_le.mpr w.digestCounter.isLt
  have ha : verifyDigestAccepted output=true := by
    simp only [verifyDigestAccepted,hg,decide_true,Bool.true_and]
    exact (ranksAccepted_iff output).mpr hr
  simp only [SigGolfCandidate.Research.SharedForest.verify,hb,↓reduceIte] at hagree
  rw [agree_mrealize_bind] at hagree
  obtain ⟨hDigest,hNext⟩ := hagree
  rw [hd] at hNext
  simp only [ha,Bool.not_true,Bool.false_eq_true,↓reduceIte] at hNext
  unfold ClaudeWCT.W9.T3M.Paired.verifyP digestP
  rw [hdc,hrho,if_neg hb,bind_map_left,agree_mrealize_bind]
  refine ⟨hDigest,?_⟩
  rw [hd]
  dsimp only
  rw [ftsP_accepted wb output hg hr,hf]
  simp only [bind_map_left,bind_assoc,pure_bind,hl]
  convert hNext using 1
  rfl
end ClaudeWCT.W9.T3M.Final.Credit.Paired

namespace ClaudeWCT.W9.T3M.Final.Credit.Paired
open OracleComp OracleSpec SigGolfCandidate.Legacy
open SigGolfCandidate.T3 (Digest HashOutput Layer)
open SigGolfCandidate.T3M (mrealize mrealize_publicHash)
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Research.SharedForest
open W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem agree_verifyP (hash : Hash) (message : SigGolfCandidate.T3.Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness)
    (he : evalWithAnswerFn (machineAnswers hash 0) (ClaudeWCT.W9.T3M.Paired.expandN message pk sig)=some (output,w)) :
    ∃ floors : Layer → Nat,CreditFloors floors ∧
      Agree hash (okHashBy floors w.topHigh hash)
        (mrealize 0 (ClaudeWCT.W9.T3M.Paired.verifyP message pk (ClaudeWCT.W9.T3M.Paired.witEncN output w))) := by
  obtain ⟨result,hr,hh,hc,hd,ha,htop⟩ := ClaudeWCT.W9.T3M.Paired.expandN_recovered _ message pk sig output w he
  simp only [ClaudeWCT.W9.T3M.Paired.recoveredWitness,evalWithAnswerFn_bind] at hr
  obtain ⟨floors,hfloors,hagree⟩ := agree_verify hash message pk w output result hd hr hh hc htop
  obtain ⟨hg,hrank,_⟩ := accepted_conditions output ha
  refine ⟨floors,hfloors,agree_verifyP_source_of hash (okHashBy floors w.topHigh hash) message pk _ output w
    (ClaudeWCT.W9.T3M.Paired.wrho_witEncN output w)
    (ClaudeWCT.W9.T3M.Paired.wdc_witEncN output w) hd hg hrank
    (W9Drv.SharedCanonical.forest_witEncN output w _ (WCT9.digestIndex_lt output))
    (fun left right=>ClaudeWCT.W9.T3M.Paired.layersCanonicalBC_witEncN output w 4 left right (by decide)) hagree⟩

theorem digestCap_okHashBy (floors : Layer → Nat) (high : Bool) (hash : Hash)
    (message : SigGolfCandidate.T3.Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness)
    (he : evalWithAnswerFn (machineAnswers hash 0) (ClaudeWCT.W9.T3M.Paired.expandN message pk sig)=some (output,w)) :
    Final.Paired.DigestCapOk (okHashBy floors high hash) message (ClaudeWCT.W9.T3M.Paired.witEncN output w) := by
  obtain ⟨_,_,_,_,hd,ha,_⟩ := ClaudeWCT.W9.T3M.Paired.expandN_recovered _ message pk sig output w he
  have hagree := agree_mrealize (notEnc_digest w.signature.rho message w.digestCounter) (hfg_okBy floors high hash)
  have hd' : evalWithAnswerFn (machineAnswers (okHashBy floors high hash) 0)
      (SigGolfCandidate.T3.digest w.signature.rho message w.digestCounter)=output := by
    rw [←eval_mrealize,←agree_eval hagree,eval_mrealize,hd]
  rw [←eval_mrealize] at hd'
  unfold SigGolfCandidate.T3.digest at hd'
  rw [mrealize_publicHash,eval_liftQ] at hd'
  unfold Final.Paired.DigestCapOk
  rw [ClaudeWCT.W9.T3M.Paired.wrho_witEncN,ClaudeWCT.W9.T3M.Paired.wdc_witEncN,hd']
  exact (accepted_conditions output ha).2.2.trans (by norm_num)
end ClaudeWCT.W9.T3M.Final.Credit.Paired
