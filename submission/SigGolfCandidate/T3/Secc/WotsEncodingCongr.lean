import SigGolfCandidate.T3.Secc.WotsMaskRef
import SigGolfCandidate.T3.Secc.WotsExtractWord
import SigGolfCandidate.T3.Secc.SeccLaw
import SigGolfCandidate.T3.Secc.WotsEvents
import SigGolfCandidate.SphincsSecurity.Proof.Base.FirstSuccessFamily
import SigGolfCandidate.SphincsSecurity.Proof.Base.UniformTableOverwrite

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
/-- Campaign S1: an encoding block is a 64-byte input whose tweak is a one-word hyper label (byte0 1, type byte
193) with any high word (the verifier reads that word from the witness, the signer writes 0). Leaf blocks share
the label but are longer. -/
def EncHeader (input : HashInput) : Prop :=
  input.length = 64 ∧ ∃ (lay : Layer) (tree leaf : Nat) (hp : BitVec 64),
    Extract.hdrBlock input = bytesLE 16 (hp ++ hyperWord lay.val (tree * 2 ^ height lay + leaf))
def NonEnc : Spec.Domain → Prop
  | .inl (.inr input) => ¬ EncHeader input
  | _ => True
/-- `h` is no hyper tweak, whatever its high word. -/
def NotHyper (h : BitVec 128) : Prop :=
  ∀ (lay : Layer) (tree leaf : Nat) (hp : BitVec 64), h ≠ hp ++ hyperWord lay.val (tree * 2 ^ height lay + leaf)
theorem notHyper_of_low {h : BitVec 128} (hl : ∀ lay routed : Nat, tweakLow h ≠ (hyperWord lay routed).toNat) :
    NotHyper h := by
  intro lay tree leaf hp he
  apply hl lay.val (tree * 2 ^ height lay + leaf)
  rw [he, append64_lowNat]
theorem tweakMarker_eq_low (h : BitVec 128) : tweakMarker h = tweakLow h % 256 := by
  unfold tweakMarker tweakLow
  rw [Nat.mod_mod_of_dvd _ (by norm_num)]
theorem tweakTag_eq_low (h : BitVec 128) : tweakTag h = tweakLow h / 256 % 256 := by
  unfold tweakTag tweakLow
  have := Nat.mod_add_div h.toNat (2 ^ 64)
  omega
theorem notHyper_of_marker {h : BitVec 128} (hm : tweakMarker h ≠ 1) : NotHyper h :=
  notHyper_of_low fun lay routed he => hm (by rw [tweakMarker_eq_low, he, hyperWord_marker])
theorem notHyper_of_tag {h : BitVec 128} (ht : tweakTag h ≠ 2) : NotHyper h :=
  notHyper_of_low fun lay routed he => ht (by rw [tweakTag_eq_low, he, hyperWord_tag])
theorem notHyper_of_lt {h : BitVec 128} (hl : tweakLow h < 193 * 2 ^ 56) : NotHyper h :=
  notHyper_of_low fun lay routed he => by
    have := hyperWord_type lay routed
    rw [he] at hl
    omega
theorem nonEnc_of_hdr (input : HashInput) (h : BitVec 128) (hblock : Extract.hdrBlock input = bytesLE 16 h)
    (htag : NotHyper h) : NonEnc (.inl (.inr input)) := by
  rintro ⟨-, l, tr, lf, hp, he⟩
  rw [hblock] at he
  exact htag l tr lf hp (bytesLE_injective he)
theorem nonEnc_of_length (input : HashInput) (hl : input.length ≠ 64) : NonEnc (.inl (.inr input)) :=
  fun he => hl he.1
theorem nonEnc_pad64_long (input : HashInput) (hl : 64 < input.length) : NonEnc (.inl (.inr (pad64 input))) := by
  apply nonEnc_of_length
  have : input.length ≤ (pad64 input).length := by
    simp only [pad64, List.length_append, List.length_replicate]; omega
  omega
theorem tag_ne_four {t : Nat} (ht : t % 256 ≠ 2) (l tr p ix : Nat) : NotHyper (header t l tr p ix) :=
  notHyper_of_tag (by rw [header_tag]; exact ht)
theorem nodeTweak_ne_row (tag lay tree heap : Nat) (ht : tag % 256 ≠ 2)
    (hroot : tag = 3 → 1 ≤ lay → lay < 4 → heap % 128 ≠ 1) : NotHyper (nodeTweak tag lay tree heap) := by
  by_cases h : tag = 3 ∧ lay < 4
  · obtain ⟨rfl, h4⟩ := h
    by_cases h0 : lay = 0
    · subst h0
      apply notHyper_of_lt
      rw [nodeTweak_top_low]
      have := topNodeWord_lt heap
      omega
    · exact notHyper_of_marker (by rw [nodeTweak_lower_marker h0 h4]; exact hroot rfl (by omega) h4)
  · by_cases hf : tag = 3 ∧ lay < 13
    · obtain ⟨rfl, h13⟩ := hf
      apply notHyper_of_tag
      rw [tweakTag_eq_low, nodeTweak_fts_low (by omega) h13]
      split_ifs with hn
      · rw [ftsNodeWordH_toNat]
        obtain ⟨h8, h128⟩ := hn
        omega
      · rw [ftsNodeWord_toNat]
        omega
    · rw [nodeTweak_other hf]; exact tag_ne_four ht _ _ _ _
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
/-- The layer of a hyper tweak, whatever the high words. -/
theorem hyperH_layer {lay lay' : Layer} {r r' : Nat} {hp hp' : BitVec 64}
    (h : hp ++ hyperWord lay.val r = hp' ++ hyperWord lay'.val r') : lay = lay' := by
  have hw := (append64_inj h).2
  have hl := congrArg (fun w : BitVec 64 => w.toNat / 2 ^ 48 % 256) hw
  simp only [hyperWord_toNat] at hl
  have h1 := lay.isLt
  have h2 := lay'.isLt
  have := Nat.mod_lt r (show 0 < 2 ^ 32 by decide)
  have := Nat.mod_lt r' (show 0 < 2 ^ 32 by decide)
  exact Fin.ext (by omega)
theorem nonEnc_prefixed (x : Digest) (rest : HashInput) {t : Nat} (ht : t % 256 ≠ 2) (l tr p ix : Nat) :
    NonEnc (.inl (.inr (pad64 (bytesLE 16 x ++ bytesLE 16 (header t l tr p ix) ++ rest)))) := by
  apply nonEnc_of_hdr _ _ _ (tag_ne_four ht l tr p ix)
  rw [Extract.hdrBlock_pad64 _ (by simp only [List.length_append, bytesLE_length]; omega), Extract.hdrBlock_prefix]
theorem nonEnc_chainInput (lay : Layer) (tree leaf i s : Nat) (v : Digest) :
    NonEnc (.inl (.inr (pad64 (chainInput lay tree leaf i s v)))) := by
  apply nonEnc_of_hdr _ (chainHeader lay tree leaf i s) _
    (notHyper_of_marker (by unfold tweakMarker; have := chainHeader_firstByte lay tree leaf i s; omega))
  rw [chainInput_padded]
  change ((chainInput lay tree leaf i s v).drop 16).take 16 = _
  rw [chainInput_header]
section Programs
theorem respects_nodeHash (tag lay tree heap : Nat) (left right : Digest) (ht : tag % 256 ≠ 2)
    (hroot : tag = 3 → 1 ≤ lay → lay < 4 → heap % 128 ≠ 1) :
    Respects NonEnc (nodeHash tag lay tree heap left right) := by
  rw [nodeHash_eq_projHash]
  apply Respects.projHash
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
/-- Campaign S1: a leaf block carries its leaf's encoding label; it is no encoding block because it is longer
(it hashes `≥ 4` chain ends; every leaf hashes `chainCount lay ≥ 43`). -/
theorem respects_leafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) (hlen : 4 ≤ ends.length) :
    Respects NonEnc (leafHash lay tree leaf ends) := by
  unfold leafHash
  refine Respects.projHash _ _ (nonEnc_pad64_long _ ?_)
  rw [leafInput_length]
  split_ifs <;> omega
theorem chainCount_ge4 (lay : Layer) : 4 ≤ chainCount lay := by fin_cases lay <;> decide
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
  apply nonEnc_of_hdr _ (digestHeader counter) _ (notHyper_of_lt (by rw [digestHeader_lowNat]; norm_num))
  unfold digestInput
  rw [Extract.hdrBlock_pad64 _ (by simp only [List.length_append, bytesLE_length]; omega),
    Extract.hdrBlock_prefix]
theorem respects_chain (lay : Layer) (tree leaf i start count : Nat) (v : Digest) :
    Respects NonEnc (chain lay tree leaf i start count v) := by
  unfold chain
  exact Respects.foldlM _ _ (fun step _ value => Respects.projHash _ _ (nonEnc_chainInput _ _ _ _ _ _)) v
theorem respects_topCoefs (leaf : Nat) : Respects NonEnc (topCoefs leaf) := by
  unfold topCoefs topSeedPair
  exact Respects.foldlM _ _ (fun _ _ _ =>
    Respects.bind (respects_privatePair _ _ _ _ _) fun _ => Respects.pure' _) _
theorem respects_topPath (cache : Cache) (leaf : Nat) : Respects NonEnc (topPath cache leaf) := by
  unfold topPath
  exact Respects.mapM _ _ fun level _ =>
    Respects.bind (respects_mask _ _) fun _ => Respects.pure' _
/-- `Respects.bind` whose continuation only needs to respect `S` on values satisfying an invariant of `p`. -/
theorem respects_bind_invT {S : Spec.Domain → Prop} {α β : Type} {p : M α} {f : α → M β} (P : α → Prop)
    (hp : Respects S p) (hP : ∀ T, P (evalWithAnswerFn T p)) (hf : ∀ x, P x → Respects S (f x)) :
    Respects S (p >>= f) := by
  intro T T' hT
  obtain ⟨he, hq⟩ := hp T T' hT
  obtain ⟨he', hq'⟩ := hf (evalWithAnswerFn T' p) (hP T') T T' hT
  refine ⟨?_, ?_⟩
  · rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, he]
    exact he'
  · rw [SourceReplay.queried_bind, SourceReplay.queried_bind, hq, he, hq']
/-- Campaign S2: the top leaf hashes all `chainCount 0 ≥ 4` chain ends (so its block is longer than an encoding
block). -/
theorem respects_buildLeafTop (leaf : Nat) (digits : List Nat) (signatureOnly : Bool) :
    Respects NonEnc (buildLeafTop leaf digits signatureOnly) := by
  rw [Correctness.buildLeafTop_eq]
  refine Respects.bind (respects_topCoefs _) fun coefs => ?_
  refine respects_bind_invT
    (fun rows : List Digest × List Digest => signatureOnly = false → rows.1.length = chainCount 0)
    (Respects.foldlM _ _ (fun i _ state => ?_) _) (fun T => ?_) fun rows hrows => ?_
  · unfold Correctness.topLeafStep
    refine Respects.bind (respects_chain _ _ _ _ _ _ _) fun value => ?_
    split
    · exact Respects.pure' _
    · exact Respects.bind (respects_chain _ _ _ _ _ _ _) fun _ => Respects.pure' _
  · intro hso
    exact Correctness.eval_foldlM_range_inv T (chainCount 0) _
      (fun done (state : List Digest × List Digest) => state.1.length = done) ([], []) rfl
      (fun i _ state hs => by
        unfold Correctness.topLeafStep
        simp only [hso, evalWithAnswerFn_bind, evalWithAnswerFn_pure, Bool.false_eq_true, ↓reduceIte,
          List.length_append, List.length_singleton, hs])
  · split
    · exact Respects.pure' _
    · rename_i hso
      exact Respects.bind (respects_leafHash _ _ _ _ (by rw [hrows (by simpa using hso)]; exact chainCount_ge4 0))
        fun _ => Respects.pure' _
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
theorem respects_signTop (cache : Cache) (leaf : Nat) (digits : List Nat) :
    Respects NonEnc (signTop cache leaf digits) := by
  unfold signTop
  refine Respects.bind (respects_buildLeafTop _ _ _) ?_
  rintro ⟨_, values⟩
  exact Respects.bind (respects_topPath _ _) fun _ => Respects.pure' _
end Programs
section RespAt
variable {T : Answers} {S : Spec.Domain → Prop}
end RespAt
end Enc
open Enc
end SigGolfCandidate.T3.Security.Wots
