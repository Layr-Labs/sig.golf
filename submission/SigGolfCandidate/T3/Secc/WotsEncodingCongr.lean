import SigGolfCandidate.T3.Secc.WotsMaskRef
import SigGolfCandidate.T3.Secc.WotsExtractWord
import SigGolfCandidate.T3.Secc.CanonEncoding

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue leafRoot)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open Mask
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace Enc
def EncHeader (input : HashInput) : Prop :=
  ∃ (lay : Layer) (tree leaf : Nat), Extract.hdrBlock input = bytesLE 16 (rowTweak lay tree leaf)
def NonEnc : Spec.Domain → Prop
  | .inl (.inr input) => ¬ EncHeader input
  | _ => True
theorem nonEnc_of_hdr (input : HashInput) (h : BitVec 128) (hblock : Extract.hdrBlock input = bytesLE 16 h)
    (htag : ∀ (lay : Layer) (tree leaf : Nat), h ≠ rowTweak lay tree leaf) : NonEnc (.inl (.inr input)) := by
  rintro ⟨l, tr, lf, he⟩
  rw [hblock] at he
  exact htag l tr lf (bytesLE_injective he)
theorem tag_ne_four {t : Nat} (ht : t % 256 ≠ 2) (l tr p ix : Nat) :
    ∀ (lay : Layer) (tree leaf : Nat), header t l tr p ix ≠ rowTweak lay tree leaf := fun _ _ _ =>
  (rowTweak_ne_header _ _ _ ht _ _ _ _).symm
theorem nodeTweak_ne_row (tag lay tree heap : Nat) (ht : tag % 256 ≠ 2)
    (hroot : tag = 3 → 1 ≤ lay → lay < 4 → heap % 2 ^ 64 ≠ 1) :
    ∀ (lay' : Layer) (tree' leaf' : Nat), nodeTweak tag lay tree heap ≠ rowTweak lay' tree' leaf' := by
  intro lay' tree' leaf'
  by_cases h : tag = 3 ∧ lay < 4
  · obtain ⟨rfl, h4⟩ := h
    by_cases h0 : lay = 0
    · subst h0; exact ne_of_tweakMarker (by rw [nodeTweak_top_marker, rowTweak_marker]; decide)
    · exact ne_of_tweakHigh (by rw [nodeTweak_hyper_high h4, rowTweak_high]; exact hroot rfl (by omega) h4)
  · by_cases hf : tag = 3 ∧ lay < 13
    · obtain ⟨rfl, h13⟩ := hf
      exact nodeTweak_fts_ne_rowTweak (by omega) h13 _ _ _ _ _
    · rw [nodeTweak_other hf]; exact tag_ne_four ht _ _ _ _ _ _ _
theorem rowTweak_layer {lay lay' : Layer} {tree leaf tree' leaf' : Nat}
    (h : rowTweak lay tree leaf = rowTweak lay' tree' leaf') : lay = lay' := by
  have hw := (append64_inj h).2
  have hl := congrArg (fun w : BitVec 64 => w.toNat / 2 ^ 48 % 256) hw
  simp only [hyperWord_toNat] at hl
  have h1 := lay.isLt
  have h2 := lay'.isLt
  have := Nat.mod_lt (tree * 2 ^ height lay + leaf) (show 0 < 2 ^ 32 by decide)
  have := Nat.mod_lt (tree' * 2 ^ height lay' + leaf') (show 0 < 2 ^ 32 by decide)
  exact Fin.ext (by omega)
theorem nonEnc_prefixed (x : Digest) (rest : HashInput) {t : Nat} (ht : t % 256 ≠ 2) (l tr p ix : Nat) :
    NonEnc (.inl (.inr (pad64 (bytesLE 16 x ++ bytesLE 16 (header t l tr p ix) ++ rest)))) := by
  apply nonEnc_of_hdr _ _ _ (tag_ne_four ht l tr p ix)
  rw [Extract.hdrBlock_pad64 _ (by simp only [List.length_append, bytesLE_length]; omega), Extract.hdrBlock_prefix]
theorem nonEnc_chainInput (lay : Layer) (tree leaf i s : Nat) (v : Digest) :
    NonEnc (.inl (.inr (pad64 (chainInput lay tree leaf i s v)))) := by
  rintro ⟨l, tr, lf, he⟩
  rw [chainInput_padded] at he
  change ((chainInput lay tree leaf i s v).drop 16).take 16 = _ at he
  rw [chainInput_header] at he
  exact chainHeader_ne_rowTweak lay tree leaf i s l tr lf (bytesLE_injective he)
section Programs
theorem respects_nodeHash (tag lay tree heap : Nat) (left right : Digest) (ht : tag % 256 ≠ 2)
    (hroot : tag = 3 → 1 ≤ lay → lay < 4 → heap % 2 ^ 64 ≠ 1) :
    Respects NonEnc (nodeHash tag lay tree heap left right) := by
  rw [nodeHash_eq_shortHash]
  apply Respects.shortHash
  rw [pad64_nodeInputP]
  exact nonEnc_of_hdr _ _ (Extract.hdrBlock_block4 left _ 0 right) (nodeTweak_ne_row tag lay tree heap ht hroot)
theorem respects_buildLevel (tag lay tree h level : Nat) (nodes : List Digest) (ht : tag % 256 ≠ 2)
    (hlow : tag = 3 → lay = 0 ∨ 4 ≤ lay) :
    Respects NonEnc (buildLevel tag lay tree h level nodes) :=
  Respects.mapM _ _ fun _ _ => respects_nodeHash _ _ _ _ _ _ ht
    (fun h3 h1 h4 => by rcases hlow h3 with h | h <;> omega)
theorem respects_buildLevels (tag lay tree h : Nat) (leaves : List Digest) (ht : tag % 256 ≠ 2)
    (hlow : tag = 3 → lay = 0 ∨ 4 ≤ lay) :
    Respects NonEnc (buildLevels tag lay tree h leaves) := by
  unfold buildLevels
  exact Respects.foldlM _ _ (fun level _ levels =>
    Respects.bind (respects_buildLevel tag lay tree h level _ ht hlow) fun _ => Respects.pure' _) _
theorem respects_leafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    Respects NonEnc (leafHash lay tree leaf ends) := by
  unfold leafHash
  exact Respects.shortHash _ (nonEnc_of_hdr _ _ (Extract.hdrBlock_leafInput _ _ _ _)
    (fun _ _ _ => leafTweak_ne_rowTweak _ _ _ _ _ _))
theorem respects_privatePair (tag lay tree position index : Nat) :
    Respects NonEnc (privatePair tag lay tree position index) :=
  Respects.privatePair _ _ _ _ _ trivial
theorem respects_mask (level index : Nat) : Respects NonEnc (mask level index) := by
  unfold mask pairedMask
  exact Respects.bind (respects_privatePair _ _ _ _ _) fun _ => Respects.pure' _
theorem respects_privateMac (region : Region) : Respects NonEnc (privateMac region) := by
  unfold privateMac privateMacKey
  exact Respects.bind (Respects.bind (Respects.privateHash _ trivial) fun _ =>
    Respects.bind (Respects.privateHash _ trivial) fun _ => Respects.pure' _) fun _ => Respects.pure' _
theorem respects_maskedLevel (nodes : List Digest) (level : Nat) : Respects NonEnc (maskedLevel nodes level) := by
  unfold maskedLevel pairedMask
  exact Respects.bind (Respects.mapM _ _ fun _ _ =>
    Respects.bind (respects_privatePair _ _ _ _ _) fun _ => Respects.pure' _) fun _ => Respects.pure' _
theorem respects_privateNonce (message : Message) : Respects NonEnc (privateNonce message) := by
  unfold privateNonce
  exact Respects.bind (Respects.privateHash _ trivial) fun _ => Respects.pure' _
theorem respects_digest (rho : Digest) (message : Message) (counter : BitVec 32) :
    Respects NonEnc (digest rho message counter) := by
  unfold digest
  apply Respects.publicHash
  apply nonEnc_of_hdr _ (digestHeader counter) _ (fun _ _ _ => digestHeader_ne_rowTweak counter _ _ _)
  unfold digestInput
  rw [Extract.hdrBlock_pad64 _ (by simp only [List.length_append, bytesLE_length]; omega),
    Extract.hdrBlock_prefix]
theorem respects_chain (lay : Layer) (tree leaf i start count : Nat) (v : Digest) :
    Respects NonEnc (chain lay tree leaf i start count v) := by
  unfold chain
  exact Respects.foldlM _ _ (fun step _ value => Respects.shortHash _ (nonEnc_chainInput _ _ _ _ _ _)) v
theorem respects_leafHalf (lay : Layer) (tree leaf : Nat) (digits : List Nat) (signatureOnly : Bool)
    (pair : Nat) (seeds : Digest × Digest) (rows : List Digest × List Digest) (half : Nat) :
    Respects NonEnc (Correctness.leafHalf lay tree leaf digits signatureOnly pair seeds rows half) := by
  unfold Correctness.leafHalf
  by_cases hc : chainCount lay ≤ 2 * pair + half
  · simp only [hc, ↓reduceIte]
    exact Respects.pure' _
  · simp only [hc, ↓reduceIte]
    refine Respects.bind (respects_chain _ _ _ _ _ _ _) fun value => ?_
    cases signatureOnly
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact Respects.bind (respects_chain _ _ _ _ _ _ _) fun _ => Respects.pure' _
    · simp only [↓reduceIte]
      exact Respects.pure' _
theorem respects_leafRows (lay : Layer) (tree leaf : Nat) (digits : List Nat) (signatureOnly : Bool) :
    Respects NonEnc (Correctness.leafRows lay tree leaf digits signatureOnly) := by
  unfold Correctness.leafRows
  refine Respects.foldlM _ _ (fun pair _ rows => ?_) _
  refine Respects.bind (respects_privatePair _ _ _ _ _) fun seeds => ?_
  exact Respects.foldlM _ _ (fun half _ rows => respects_leafHalf _ _ _ _ _ _ _ _ _) _
theorem respects_buildLeaf (lay : Layer) (tree leaf : Nat) (digits : List Nat) (signatureOnly : Bool) :
    Respects NonEnc (buildLeaf lay tree leaf digits signatureOnly) := by
  rw [Correctness.buildLeaf_eq]
  refine Respects.bind (respects_leafRows _ _ _ _ _) fun rows => ?_
  split
  · exact Respects.pure' _
  · exact Respects.bind (respects_leafHash _ _ _ _) fun _ => Respects.pure' _
theorem respects_treeRows (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    Respects NonEnc (Correctness.treeRows lay tree selected digits) := by
  unfold Correctness.treeRows
  refine Respects.foldlM _ _ (fun leaf _ rows => ?_) _
  refine Respects.bind (respects_buildLeaf _ _ _ _ _) ?_
  rintro ⟨root, values⟩
  exact Respects.pure' _
theorem respects_buildTree (lay : Layer) (tree selected : Nat) (digits : List Nat) (hlay : lay = 0) :
    Respects NonEnc (buildTree lay tree selected digits) := by
  rw [Correctness.buildTree_eq]
  exact Respects.bind (respects_treeRows _ _ _ _) fun rows =>
    Respects.bind (respects_buildLevels 3 _ _ _ _ (by decide) (fun _ => Or.inl (by simp [hlay]))) fun _ =>
      Respects.pure' _
theorem respects_topCoefs (leaf : Nat) : Respects NonEnc (topCoefs leaf) := by
  unfold topCoefs topSeedPair
  exact Respects.foldlM _ _ (fun _ _ _ =>
    Respects.bind (respects_privatePair _ _ _ _ _) fun _ => Respects.pure' _) _
theorem respects_buildLeafTop (leaf : Nat) (digits : List Nat) (signatureOnly : Bool) :
    Respects NonEnc (buildLeafTop leaf digits signatureOnly) := by
  rw [Correctness.buildLeafTop_eq]
  refine Respects.bind (respects_topCoefs _) fun coefs => ?_
  refine Respects.bind (Respects.foldlM _ _ (fun i _ state => ?_) _) fun rows => ?_
  · unfold Correctness.topLeafStep
    refine Respects.bind (respects_chain _ _ _ _ _ _ _) fun value => ?_
    split
    · exact Respects.pure' _
    · exact Respects.bind (respects_chain _ _ _ _ _ _ _) fun _ => Respects.pure' _
  · split
    · exact Respects.pure' _
    · exact Respects.bind (respects_leafHash _ _ _ _) fun _ => Respects.pure' _
theorem respects_buildTopTree : Respects NonEnc buildTopTree := by
  unfold buildTopTree
  exact Respects.bind (Respects.foldlM _ _ (fun _ _ _ =>
    Respects.bind (respects_buildLeafTop _ _ _) fun _ => Respects.pure' _) _) fun _ =>
    respects_buildLevels 3 _ _ _ _ (by decide) (fun _ => Or.inl rfl)
theorem respects_keygen : Respects NonEnc keygen := by
  unfold keygen
  rw [Correctness.keygenPayload_eq]
  unfold Correctness.cachePayloadProgram
  refine Respects.bind (Respects.bind respects_buildTopTree fun levels => ?_) fun payload => ?_
  · exact Respects.bind (Respects.mapM _ _ fun level _ => respects_maskedLevel _ _) fun _ => Respects.pure' _
  · rcases payload with ⟨publicKey, region⟩
    exact Respects.bind (respects_privateMac region) fun _ => Respects.pure' _
theorem respects_topPath (cache : Cache) (leaf : Nat) : Respects NonEnc (topPath cache leaf) := by
  unfold topPath
  exact Respects.mapM _ _ fun level _ =>
    Respects.bind (respects_mask _ _) fun _ => Respects.pure' _
theorem respects_signTop (cache : Cache) (leaf : Nat) (digits : List Nat) :
    Respects NonEnc (signTop cache leaf digits) := by
  unfold signTop
  refine Respects.bind (respects_buildLeafTop _ _ _) ?_
  rintro ⟨_, values⟩
  exact Respects.bind (respects_topPath _ _) fun _ => Respects.pure' _
end Programs
def leafOf (L : CanonGraph.LeafPos) : LeafAddr := ⟨L.lay, L.tree.val, L.leaf.val⟩
abbrev EncIndex := CanonGraph.LeafPos × Digest × BitVec 32
def encInput (e : EncIndex) : HashInput := encodingRow (leafOf e.1) e.2.1 e.2.2
theorem encInput_length (e : EncIndex) : (encInput e).length = 64 := by
  simp [encInput, encodingRow, encodingInput, pad64, bytesLE_length]
def RejPair (T T' : Answers) (q : Spec.Domain) : Prop :=
  ∃ (input : HashInput) (lay : Layer) (tr lf : Nat), q = .inl (.inr input) ∧
    Extract.hdrBlock input = bytesLE 16 (rowTweak lay tr lf) ∧
    searchDecode lay (low (T (.inl (.inr input)))) = none ∧ searchDecode lay (low (T' (.inl (.inr input)))) = none
theorem RejPair.layer {T T' : Answers} {input : HashInput} {lay : Layer} {tr lf : Nat}
    (h : RejPair T T' (.inl (.inr input))) (hh : Extract.hdrBlock input = bytesLE 16 (rowTweak lay tr lf)) :
    searchDecode lay (low (T (.inl (.inr input)))) = none ∧
      searchDecode lay (low (T' (.inl (.inr input)))) = none := by
  obtain ⟨input', lay', tr', lf', hq, hh', h1, h2⟩ := h
  have hi : input' = input := (Sum.inr.inj (Sum.inl.inj hq)).symm
  subst hi
  rw [hh] at hh'
  have hl : lay' = lay := (rowTweak_layer (bytesLE_injective hh')).symm
  subst hl
  exact ⟨h1, h2⟩
theorem RejPair.mk {T T' : Answers} {input : HashInput} {lay : Layer} {tr lf : Nat}
    (hh : Extract.hdrBlock input = bytesLE 16 (rowTweak lay tr lf))
    (h1 : searchDecode lay (low (T (.inl (.inr input)))) = none)
    (h2 : searchDecode lay (low (T' (.inl (.inr input)))) = none) : RejPair T T' (.inl (.inr input)) :=
  ⟨input, lay, tr, lf, rfl, hh, h1, h2⟩
def AgreeOn (S : Spec.Domain → Prop) (T T' : Answers) : Prop :=
  ∀ q, S q → T' q = T q ∨ RejPair T T' q
def RespAt (T : Answers) (S : Spec.Domain → Prop) {α : Type} (p : M α) : Prop :=
  ∀ T' : Answers, AgreeOn S T T' →
    evalWithAnswerFn T' p = evalWithAnswerFn T p ∧ SourceReplay.queried T' p = SourceReplay.queried T p
section RespAt
variable {T : Answers} {S : Spec.Domain → Prop}
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
end Enc
open Enc
theorem leafSeed_congr_nonEnc {T T' : Answers} (h : ∀ q, NonEnc q → T' q = T q) (lay : Layer) (tree leaf i : Nat) :
    leafSeed T' lay tree leaf i = leafSeed T lay tree leaf i := by
  unfold leafSeed
  split_ifs
  · unfold Correctness.topLeafSeed Correctness.topCoefList
    congr 2
    funext j
    unfold Correctness.topCoef Correctness.topCoefN topSeedPair
    rw [(Enc.respects_privatePair 0 0 0 _ 0).eval_eq h]
  all_goals rw [(Enc.respects_privatePair 0 lay.val tree (i / 2) leaf).eval_eq h]
theorem leafEnd_congr_nonEnc {T T' : Answers} (h : ∀ q, NonEnc q → T' q = T q) (lay : Layer) (tree leaf i : Nat) :
    leafEnd T' lay tree leaf i = leafEnd T lay tree leaf i := by
  unfold leafEnd
  rw [leafSeed_congr_nonEnc h]
  exact (Enc.respects_chain _ _ _ _ _ _ _).eval_eq h
theorem leafRoot_congr_nonEnc {T T' : Answers} (h : ∀ q, NonEnc q → T' q = T q) (lay : Layer) (tree leaf : Nat) :
    leafRoot T' lay tree leaf = leafRoot T lay tree leaf := by
  unfold leafRoot
  have he : (List.range (chainCount lay)).map (leafEnd T' lay tree leaf) =
      (List.range (chainCount lay)).map (leafEnd T lay tree leaf) :=
    List.map_congr_left fun i _ => leafEnd_congr_nonEnc h lay tree leaf i
  rw [he]
  exact (Enc.respects_leafHash _ _ _ _).eval_eq h
theorem builtTree_congr_nonEnc {T T' : Answers} (h : ∀ q, NonEnc q → T' q = T q) (lay : Layer) (tree : Nat)
    (hlay : lay = 0) : builtTree T' lay tree = builtTree T lay tree := by
  unfold builtTree
  have hr : Correctness.leafRoot T' lay tree = Correctness.leafRoot T lay tree :=
    funext (leafRoot_congr_nonEnc h lay tree)
  rw [hr]
  exact (Enc.respects_buildLevels 3 _ _ _ _ (by decide) (fun _ => Or.inl (by simp [hlay]))).eval_eq h
end SigGolfCandidate.T3.Security.Wots
