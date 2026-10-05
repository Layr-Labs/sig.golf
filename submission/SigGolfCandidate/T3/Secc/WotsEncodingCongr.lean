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
  ∃ l tr p ix, Extract.hdrBlock input = bytesLE 16 (header 4 l tr p ix)
def NonEnc : Spec.Domain → Prop
  | .inl (.inr input) => ¬ EncHeader input
  | _ => True
theorem nonEnc_of_hdr (input : HashInput) (h : BitVec 128) (hblock : Extract.hdrBlock input = bytesLE 16 h)
    (htag : ∀ l tr p ix, h ≠ header 4 l tr p ix) : NonEnc (.inl (.inr input)) := by
  rintro ⟨l, tr, p, ix, he⟩
  rw [hblock] at he
  exact htag l tr p ix (bytesLE_injective he)
theorem tag_ne_four {t : Nat} (ht : t % 256 ≠ 4) (l tr p ix : Nat) :
    ∀ l' tr' p' ix', header t l tr p ix ≠ header 4 l' tr' p' ix' := fun _ _ _ _ =>
  header_ne_of_tag (by simpa using ht)
theorem nonEnc_block4 (x y z : Digest) {t : Nat} (ht : t % 256 ≠ 4) (l tr p ix : Nat) :
    NonEnc (.inl (.inr (block4 x (header t l tr p ix) y z))) :=
  nonEnc_of_hdr _ _ (Extract.hdrBlock_block4 x _ y z) (tag_ne_four ht l tr p ix)
theorem nonEnc_prefixed (x : Digest) (rest : HashInput) {t : Nat} (ht : t % 256 ≠ 4) (l tr p ix : Nat) :
    NonEnc (.inl (.inr (pad64 (bytesLE 16 x ++ bytesLE 16 (header t l tr p ix) ++ rest)))) := by
  apply nonEnc_of_hdr _ _ _ (tag_ne_four ht l tr p ix)
  rw [Extract.hdrBlock_pad64 _ (by simp only [List.length_append, bytesLE_length]; omega), Extract.hdrBlock_prefix]
theorem nonEnc_chainInput (lay : Layer) (tree leaf i s : Nat) (v : Digest) :
    NonEnc (.inl (.inr (pad64 (chainInput lay tree leaf i s v)))) := by
  rintro ⟨l, tr, p, ix, he⟩
  rw [chainInput_padded] at he
  change ((chainInput lay tree leaf i s v).drop 16).take 16 = _ at he
  rw [chainInput_header] at he
  exact chainHeader_ne_header lay tree leaf i s 4 l tr p ix
    (bytesLE_injective he)
theorem nonEnc_private (c : Coordinate) : NonEnc (.inr c) := trivial
section Programs
theorem respects_nodeHash (tag lay tree heap : Nat) (left right : Digest) (ht : tag % 256 ≠ 4) :
    Respects NonEnc (nodeHash tag lay tree heap left right) := by
  rw [nodeHash_eq_shortHash]
  apply Respects.shortHash
  rw [pad64_nodeInputP]
  exact nonEnc_block4 left 0 right ht lay tree 0 heap
theorem respects_buildLevel (tag lay tree h level : Nat) (nodes : List Digest) (ht : tag % 256 ≠ 4) :
    Respects NonEnc (buildLevel tag lay tree h level nodes) :=
  Respects.mapM _ _ fun _ _ => respects_nodeHash _ _ _ _ _ _ ht
theorem respects_buildLevels (tag lay tree h : Nat) (leaves : List Digest) (ht : tag % 256 ≠ 4) :
    Respects NonEnc (buildLevels tag lay tree h leaves) := by
  unfold buildLevels
  exact Respects.foldlM _ _ (fun level _ levels =>
    Respects.bind (respects_buildLevel tag lay tree h level _ ht) fun _ => Respects.pure' _) _
theorem respects_leafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    Respects NonEnc (leafHash lay tree leaf ends) := by
  unfold leafHash
  exact Respects.shortHash _ (nonEnc_prefixed _ _ (by decide) _ _ _ _)
theorem respects_forestPk (index : Nat) (roots : List Digest) :
    Respects NonEnc (forestPk index roots) := by
  unfold forestPk
  exact Respects.shortHash _ (nonEnc_prefixed _ _ (by decide) _ _ _ _)
theorem respects_ftsLeaf (index coord leaf : Nat) (secret : Digest) :
    Respects NonEnc (ftsLeaf index coord leaf secret) := by
  rw [ftsLeaf_eq_shortHash]
  apply Respects.shortHash
  rw [pad64_ftsLeafInputP]
  exact nonEnc_block4 0 secret 0 (by decide) coord index 0 leaf
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
theorem respects_ftsRows (index coord : Nat) : Respects NonEnc (Correctness.ftsRows index coord) := by
  unfold Correctness.ftsRows
  refine Respects.foldlM _ _ (fun pair _ state => ?_) _
  refine Respects.bind (respects_privatePair _ _ _ _ _) ?_
  rintro ⟨left, right⟩
  exact Respects.bind (respects_ftsLeaf _ _ _ _) fun _ =>
    Respects.bind (respects_ftsLeaf _ _ _ _) fun _ => Respects.pure' _
theorem respects_buildFts (index coord : Nat) : Respects NonEnc (buildFts index coord) := by
  rw [Correctness.buildFts_eq]
  exact Respects.bind (respects_ftsRows index coord) fun rows =>
    Respects.bind (respects_buildLevels 10 coord index 11 rows.1 (by decide)) fun _ => Respects.pure' _
theorem respects_signForest (index : Nat) (chosen : List Selection) :
    Respects NonEnc (Correctness.signForest index chosen) := by
  unfold Correctness.signForest
  refine Respects.foldlM _ _ (fun coord _ state => ?_) _
  refine Respects.bind (respects_buildFts index coord) ?_
  rintro ⟨levels, secrets⟩
  exact Respects.pure' _
theorem respects_digest (rho : Digest) (message : Message) (counter : BitVec 32) :
    Respects NonEnc (digest rho message counter) := by
  unfold digest
  apply Respects.publicHash
  unfold digestInput
  exact nonEnc_prefixed _ _ (by decide) _ _ _ _
theorem respects_digestSearch (rho : Digest) (message : Message) :
    ∀ fuel counter, Respects NonEnc (digestSearch rho message counter fuel) := by
  intro fuel
  induction fuel with
  | zero => intro counter; exact Respects.pure' _
  | succ fuel ih =>
      intro counter
      simp only [digestSearch]
      refine Respects.bind (respects_digest _ _ _) fun output => ?_
      split
      · exact Respects.pure' _
      · exact ih _
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
theorem respects_buildTree (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    Respects NonEnc (buildTree lay tree selected digits) := by
  rw [Correctness.buildTree_eq]
  exact Respects.bind (respects_treeRows _ _ _ _) fun rows =>
    Respects.bind (respects_buildLevels 3 _ _ _ _ (by decide)) fun _ => Respects.pure' _
theorem respects_keygen : Respects NonEnc keygen := by
  unfold keygen
  rw [Correctness.keygenPayload_eq]
  unfold Correctness.cachePayloadProgram
  refine Respects.bind (Respects.bind (respects_buildTree _ _ _ _) fun levels => ?_) fun payload => ?_
  · rcases levels with ⟨levels, _⟩
    exact Respects.bind (Respects.mapM _ _ fun level _ => respects_maskedLevel _ _) fun _ => Respects.pure' _
  · rcases payload with ⟨publicKey, region⟩
    exact Respects.bind (respects_privateMac region) fun _ => Respects.pure' _
theorem respects_topPath (cache : Cache) (leaf : Nat) : Respects NonEnc (topPath cache leaf) := by
  unfold topPath
  exact Respects.mapM _ _ fun level _ =>
    Respects.bind (respects_mask _ _) fun _ => Respects.pure' _
theorem respects_signTop (cache : Cache) (leaf : Nat) (digits : List Nat) :
    Respects NonEnc (signTop cache leaf digits) := by
  unfold signTop
  refine Respects.bind (respects_buildLeaf _ _ _ _ _) ?_
  rintro ⟨_, values⟩
  exact Respects.bind (respects_topPath _ _) fun _ => Respects.pure' _
end Programs
def leafOf (L : CanonGraph.LeafPos) : LeafAddr := ⟨L.lay, L.tree.val, L.leaf.val⟩
abbrev EncIndex := CanonGraph.LeafPos × Digest × BitVec 32
def encInput (e : EncIndex) : HashInput := encodingRow (leafOf e.1) e.2.1 e.2.2
theorem encInput_length (e : EncIndex) : (encInput e).length = 64 := by
  simp [encInput, encodingRow, encodingInput, pad64, bytesLE_length]
theorem encInput_injective : Function.Injective encInput := by
  rintro ⟨L, m, c⟩ ⟨L', m', c'⟩ he
  have he' := Sampling.pad64_inj_of_length (by simp only [encodingInput, List.length_append, bytesLE_length]) he
  have ht : L.tree.val < 2 ^ 40 := lt_of_lt_of_le L.tree.isLt (by norm_num)
  have ht' : L'.tree.val < 2 ^ 40 := lt_of_lt_of_le L'.tree.isLt (by norm_num)
  have hl : L.leaf.val < 2 ^ 32 := lt_of_lt_of_le L.leaf.isLt (by norm_num)
  have hl' : L'.leaf.val < 2 ^ 32 := lt_of_lt_of_le L'.leaf.isLt (by norm_num)
  obtain ⟨h1, h2, h3, h4, h5⟩ := QuerySpace.encodingInput_injective ht ht' hl hl' he'
  obtain ⟨lay, tree, leaf⟩ := L
  obtain ⟨lay', tree', leaf'⟩ := L'
  simp only [leafOf] at h1 h2 h3
  subst h1 h4 h5
  have : tree = tree' := Fin.ext h2
  have : leaf = leaf' := Fin.ext h3
  subst tree leaf
  rfl
theorem encInput_encHeader (e : EncIndex) : EncHeader (encInput e) := by
  refine ⟨e.1.lay.val, e.1.tree.val, 0, e.1.leaf.val, ?_⟩
  unfold encInput encodingRow encodingInput leafOf
  rw [Extract.hdrBlock_pad64 _ (by simp only [List.length_append, bytesLE_length]; omega)]
  simp [Extract.hdrBlock, List.append_assoc, bytesLE_length]
theorem encInput_hdr (e : EncIndex) :
    Extract.hdrBlock (encInput e) = bytesLE 16 (header 4 e.1.lay.val e.1.tree.val 0 e.1.leaf.val) := by
  unfold encInput encodingRow encodingInput leafOf
  rw [Extract.hdrBlock_pad64 _ (by simp only [List.length_append, bytesLE_length]; omega)]
  simp [Extract.hdrBlock, List.append_assoc, bytesLE_length]
/-- Two answer tables differ at `q` only on an encoding row (of any layout) that the producers' search decoder
rejects in both tables: the row's header names its layer. -/
def RejPair (T T' : Answers) (q : Spec.Domain) : Prop :=
  ∃ (input : HashInput) (lay : Layer) (tr p ix : Nat), q = .inl (.inr input) ∧
    Extract.hdrBlock input = bytesLE 16 (header 4 lay.val tr p ix) ∧
    searchDecode lay (low (T (.inl (.inr input)))) = none ∧ searchDecode lay (low (T' (.inl (.inr input)))) = none
theorem RejPair.layer {T T' : Answers} {input : HashInput} {lay : Layer} {tr p ix : Nat}
    (h : RejPair T T' (.inl (.inr input))) (hh : Extract.hdrBlock input = bytesLE 16 (header 4 lay.val tr p ix)) :
    searchDecode lay (low (T (.inl (.inr input)))) = none ∧
      searchDecode lay (low (T' (.inl (.inr input)))) = none := by
  obtain ⟨input', lay', tr', p', ix', hq, hh', h1, h2⟩ := h
  have hi : input' = input := (Sum.inr.inj (Sum.inl.inj hq)).symm
  subst hi
  rw [hh] at hh'
  have hf := (Mask.header_fields (bytesLE_injective hh')).2.1
  have hl : lay' = lay := Fin.ext (by have := lay.isLt; have := lay'.isLt; omega)
  subst hl
  exact ⟨h1, h2⟩
theorem RejPair.mk {T T' : Answers} {input : HashInput} {lay : Layer} {tr p ix : Nat}
    (hh : Extract.hdrBlock input = bytesLE 16 (header 4 lay.val tr p ix))
    (h1 : searchDecode lay (low (T (.inl (.inr input)))) = none)
    (h2 : searchDecode lay (low (T' (.inl (.inr input)))) = none) : RejPair T T' (.inl (.inr input)) :=
  ⟨input, lay, tr, p, ix, rfl, hh, h1, h2⟩
theorem RejPair.encHeader {T T' : Answers} {q : Spec.Domain} (h : RejPair T T' q) :
    ∃ input, q = .inl (.inr input) ∧ EncHeader input := by
  obtain ⟨input, lay, tr, p, ix, hq, hh, -, -⟩ := h
  exact ⟨input, hq, lay.val, tr, p, ix, hh⟩
def AgreeOn (S : Spec.Domain → Prop) (T T' : Answers) : Prop :=
  ∀ q, S q → T' q = T q ∨ RejPair T T' q
theorem AgreeOn.of_eq {S : Spec.Domain → Prop} {T T' : Answers} (h : ∀ q, S q → T' q = T q) : AgreeOn S T T' :=
  fun q hq => Or.inl (h q hq)
theorem AgreeOn.nonEnc {S : Spec.Domain → Prop} {T T' : Answers} (h : AgreeOn S T T')
    (hS : ∀ q, NonEnc q → S q) : ∀ q, NonEnc q → T' q = T q := by
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
theorem RespAt.of_respects {α : Type} {p : M α} (h : Respects NonEnc p)
    (hS : ∀ q, NonEnc q → S q) : RespAt T S p := by
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
theorem respAt_counterSearch (T : Answers) (S : Spec.Domain → Prop) (L : CanonGraph.LeafPos)
    (message : Digest) : ∀ fuel start,
      (∀ c < fuel, (∀ c' < c, searchDecode L.lay (low (T (.inl (.inr (encInput
          (L, message, BitVec.ofNat 32 (start + c'))))))) = none) →
        S (.inl (.inr (encInput (L, message, BitVec.ofNat 32 (start + c)))))) →
      RespAt T S (counterSearch L.lay L.tree.val L.leaf.val message start fuel) := by
  intro fuel
  induction fuel with
  | zero => intro start _; exact RespAt.pure' _
  | succ fuel ih =>
      intro start hS T' hT'
      have hS0 : S (.inl (.inr (encInput (L, message, BitVec.ofNat 32 start)))) := by
        have := hS 0 (Nat.zero_lt_succ _) (fun c' hc' => absurd hc' (Nat.not_lt_zero _))
        rwa [Nat.add_zero] at this
      have hrest : searchDecode L.lay (low (T (.inl (.inr (encInput (L, message, BitVec.ofNat 32 start)))))) = none →
          RespAt T S (counterSearch L.lay L.tree.val L.leaf.val message (start + 1) fuel) := by
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
      rw [counterSearch]
      rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, SourceReplay.queried_bind, SourceReplay.queried_bind]
      have hq0 : SourceReplay.queried T' (shortHash (encodingInput L.lay L.tree.val L.leaf.val message
          (BitVec.ofNat 32 start))) = SourceReplay.queried T (shortHash (encodingInput L.lay L.tree.val L.leaf.val
          message (BitVec.ofNat 32 start))) := rfl
      rw [hq0]
      rcases hT' _ hS0 with heq | hrej
      · have hev : evalWithAnswerFn T' (shortHash (encodingInput L.lay L.tree.val L.leaf.val message
            (BitVec.ofNat 32 start))) = evalWithAnswerFn T (shortHash (encodingInput L.lay L.tree.val L.leaf.val
            message (BitVec.ofNat 32 start))) :=
          congrArg (fun x : HashOutput => x.extractLsb' 0 128) heq
        rw [hev]
        cases hd : searchDecode L.lay (evalWithAnswerFn T (shortHash (encodingInput L.lay L.tree.val L.leaf.val
            message (BitVec.ofNat 32 start)))) with
        | none =>
            obtain ⟨h1, h2⟩ := hrest hd T' hT'
            dsimp only
            exact ⟨h1, by rw [h2]⟩
        | some digits => exact ⟨rfl, rfl⟩
      · obtain ⟨hTn, hTn'⟩ := hrej.layer (encInput_hdr (L, message, BitVec.ofNat 32 start))
        have hl : searchDecode L.lay (evalWithAnswerFn T (shortHash (encodingInput L.lay L.tree.val L.leaf.val
            message (BitVec.ofNat 32 start)))) = none := hTn
        have hl' : searchDecode L.lay (evalWithAnswerFn T' (shortHash (encodingInput L.lay L.tree.val L.leaf.val
            message (BitVec.ofNat 32 start)))) = none := hTn'
        obtain ⟨h1, h2⟩ := hrest hTn T' hT'
        rw [hl, hl']
        dsimp only
        exact ⟨h1, by rw [h2]⟩
def Reached (T : Answers) (L : LeafAddr) (input : HashInput) : Prop :=
  ∃ c < counterLimit, input = encodingRow L (leafMsg T L) (BitVec.ofNat 32 c) ∧
    ∀ c' < c, searchDecode L.lay (low (T (.inl (.inr (encodingRow L (leafMsg T L) (BitVec.ofNat 32 c')))))) = none
def HonestQ (T : Answers) : Spec.Domain → Prop
  | .inl (.inr input) => ¬ EncHeader input ∨ ∃ L : CanonGraph.LeafPos, Reached T (leafOf L) input
  | _ => True
theorem honestQ_of_nonEnc {T : Answers} {q : Spec.Domain} (h : NonEnc q) : HonestQ T q := by
  rcases q with (coin | input) | coordinate
  · trivial
  · exact Or.inl h
  · trivial
theorem respAt_referenceSearch (T : Answers) (S : Spec.Domain → Prop) (L : CanonGraph.LeafPos)
    (hS : ∀ input, Reached T (leafOf L) input → S (.inl (.inr input))) :
    RespAt T S (counterSearch (leafOf L).lay (leafOf L).tree (leafOf L).leaf (leafMsg T (leafOf L)) 0
      counterLimit) := by
  apply respAt_counterSearch T S L
  intro c hc hprev
  apply hS
  refine ⟨c, hc, ?_, fun c' hc' => ?_⟩
  · simp only [encInput, Nat.zero_add]
  · have := hprev c' hc'
    rw [Nat.zero_add] at this
    exact this
def routePos (index : Nat) (hindex : index < 2 ^ 31) (lay : Layer) : CanonGraph.LeafPos :=
  ⟨lay, ⟨(route index lay).2, lt_of_le_of_lt (Nat.div_le_self _ _) hindex⟩,
    ⟨(route index lay).1, lt_of_lt_of_le (route_leaf_bound index lay)
      (by calc 2 ^ height lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (Extract.height_le lay)
            _ = 4096 := by norm_num)⟩⟩
theorem leafOf_routePos (index : Nat) (hindex : index < 2 ^ 31) (lay : Layer) :
    leafOf (routePos index hindex lay) = routeLeaf index lay := rfl
theorem respAt_routeSearch (T : Answers) (index : Nat) (hindex : index < 2 ^ 31) (lay : Layer) :
    RespAt T (HonestQ T) (counterSearch lay (route index lay).2 (route index lay).1
      (leafMsg T (routeLeaf index lay)) 0 counterLimit) :=
  respAt_referenceSearch T (HonestQ T) (routePos index hindex lay)
    (fun input h => Or.inr ⟨routePos index hindex lay, h⟩)
theorem respAt_signLayers (T : Answers) (cache : Cache) (index : Nat) (hindex : index < 2 ^ 31) :
    ∀ n, n ≤ 4 → ∀ msg, (∀ m, n = m + 1 → msg = leafMsg T (routeLeaf index (Fin.ofNat 4 m))) →
      RespAt T (HonestQ T) (signLayers cache index n msg) := by
  intro n
  induction n with
  | zero => intro _ _ _; exact RespAt.pure' _
  | succ n ih =>
      intro hn msg hmsg
      simp only [signLayers]
      refine RespAt.bind ?_ ?_
      · rw [hmsg n rfl]
        exact respAt_routeSearch T index hindex _
      · cases hs : evalWithAnswerFn T (counterSearch (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2
          (route index (Fin.ofNat 4 n)).1 msg 0 counterLimit) with
        | none =>
            dsimp only
            split_ifs with hn0
            · exact RespAt.bind (RespAt.of_respects (respects_signTop _ _ _) fun _ h => honestQ_of_nonEnc h)
                (RespAt.pure' _)
            · exact RespAt.pure' _
        | some found =>
            obtain ⟨counter, digits⟩ := found
            have hd := (Correctness.counterSearch_some T _ _ _ msg counterLimit 0 counter digits
              (by decide) hs).2.2
            have hvalid := Cost.validDigits_decode hd
            dsimp only
            split_ifs with hn0
            · exact RespAt.bind (RespAt.of_respects (respects_signTop _ _ _) fun _ h => honestQ_of_nonEnc h)
                (RespAt.pure' _)
            · refine RespAt.bind (RespAt.of_respects (respects_buildTree _ _ _ _)
                fun _ h => honestQ_of_nonEnc h) ?_
              rw [Correctness.eval_buildTree_result T _ _ _ digits hvalid (route_leaf_bound index _)]
              dsimp only
              obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
              refine RespAt.bind (ih (by omega) _ (fun m' hm' => ?_)) ?_
              · obtain rfl : m = m' := by omega
                exact signedMsg_succ T index m (by omega)
              · cases evalWithAnswerFn T (signLayers cache index (m + 1) _) <;> exact RespAt.pure' _
theorem respAt_signPayload (T : Answers) (cache : Cache) (message : Message) :
    RespAt T (HonestQ T) (signPayload cache message) := by
  rw [Correctness.signPayload_eq]
  refine RespAt.bind (RespAt.of_respects (respects_privateNonce message) fun _ h => honestQ_of_nonEnc h) ?_
  refine RespAt.bind (RespAt.of_respects (respects_digestSearch _ _ _ _) fun _ h => honestQ_of_nonEnc h) ?_
  generalize evalWithAnswerFn T (digestSearch (evalWithAnswerFn T (privateNonce message)) message 0
    attemptLimit) = found
  rcases found with _ | ⟨counter, output⟩
  · exact RespAt.pure' _
  · dsimp only
    refine RespAt.bind (RespAt.of_respects (respects_signForest _ _) fun _ h => honestQ_of_nonEnc h) ?_
    refine RespAt.bind (RespAt.of_respects (respects_forestPk _ _) fun _ h => honestQ_of_nonEnc h) ?_
    refine RespAt.bind (respAt_signLayers T cache _ (Nat.mod_lt _ (by decide)) 4 le_rfl _ (fun m hm => ?_)) ?_
    · obtain rfl : m = 3 := by omega
      rw [Correctness.eval_signForest]
      exact signedMsg_top T _
    · generalize evalWithAnswerFn T (signLayers cache (output.toNat % 2 ^ 31) 4 _) = pieces
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
open Enc
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
theorem leafSeed_congr_nonEnc {T T' : Answers} (h : ∀ q, NonEnc q → T' q = T q) (lay : Layer) (tree leaf i : Nat) :
    leafSeed T' lay tree leaf i = leafSeed T lay tree leaf i := by
  unfold leafSeed
  rw [(Enc.respects_privatePair 0 lay.val tree (i / 2) leaf).eval_eq h]
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
theorem builtTree_congr_nonEnc {T T' : Answers} (h : ∀ q, NonEnc q → T' q = T q) (lay : Layer) (tree : Nat) :
    builtTree T' lay tree = builtTree T lay tree := by
  unfold builtTree
  have hr : Correctness.leafRoot T' lay tree = Correctness.leafRoot T lay tree :=
    funext (leafRoot_congr_nonEnc h lay tree)
  rw [hr]
  exact (Enc.respects_buildLevels 3 _ _ _ _ (by decide)).eval_eq h
theorem honestForest_congr_nonEnc {T T' : Answers} (h : ∀ q, NonEnc q → T' q = T q) (index : Nat) :
    Extract.honestForest T' index = Extract.honestForest T index := by
  rw [Mask.honestForest_eq, Mask.honestForest_eq]
  have hl : ((List.range 7).map fun c => treeValue (evalWithAnswerFn T' (buildFts index c)).1 11 0) =
      (List.range 7).map fun c => treeValue (evalWithAnswerFn T (buildFts index c)).1 11 0 :=
    List.map_congr_left fun c _ => congrArg (fun x : List (List Digest) × List Digest => treeValue x.1 11 0)
      ((Enc.respects_buildFts index c).eval_eq h)
  rw [hl]
  exact (Enc.respects_forestPk _ _).eval_eq h
theorem leafMsg_congr_nonEnc {T T' : Answers} (h : ∀ q, NonEnc q → T' q = T q) (L : LeafAddr) :
    leafMsg T' L = leafMsg T L := by
  unfold leafMsg
  split
  · unfold Extract.honestRoot
    rw [builtTree_congr_nonEnc h]
  · exact honestForest_congr_nonEnc h _
theorem nonEnc_of_honest {T T' : Answers} (h : AgreeOn (HonestQ T) T T') : ∀ q, NonEnc q → T' q = T q :=
  h.nonEnc fun _ hq => honestQ_of_nonEnc hq
theorem referenceSearch_congr_honest {T T' : Answers} (h : AgreeOn (HonestQ T) T T')
    (L : CanonGraph.LeafPos) : referenceSearch T' (leafOf L) = referenceSearch T (leafOf L) := by
  unfold referenceSearch
  rw [leafMsg_congr_nonEnc (nonEnc_of_honest h)]
  exact (respAt_referenceSearch T (HonestQ T) L (fun input hr => Or.inr ⟨L, hr⟩)).eval_eq h
theorem referenceDigits_congr_honest {T T' : Answers} (h : AgreeOn (HonestQ T) T T')
    (L : CanonGraph.LeafPos) : referenceDigits T' (leafOf L) = referenceDigits T (leafOf L) := by
  unfold referenceDigits
  rw [referenceSearch_congr_honest h]
theorem referenceInput_congr_honest {T T' : Answers} (h : AgreeOn (HonestQ T) T T')
    (L : CanonGraph.LeafPos) : referenceInput T' (leafOf L) = referenceInput T (leafOf L) := by
  unfold referenceInput
  rw [referenceSearch_congr_honest h, leafMsg_congr_nonEnc (nonEnc_of_honest h)]
end SigGolfCandidate.T3.Security.Wots
