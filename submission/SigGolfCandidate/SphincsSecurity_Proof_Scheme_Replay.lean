import SigGolfCandidate.SphincsSecurity_Proof_Ots_EncodingCached
import SigGolfCandidate.SphincsSecurity_Proof_Scheme_ForgeryClassify

namespace SphincsSecurity.Concrete
open OracleComp OracleSpec
theorem messageDigestPayload_injective (root : Digest) {leftMessage rightMessage : Message}
    {leftRandomness rightRandomness : Randomness}
    (h : messageDigestPayload root leftMessage leftRandomness
      = messageDigestPayload root rightMessage rightRandomness) :
    leftMessage = rightMessage ∧ leftRandomness = rightRandomness := by
  simp only [messageDigestPayload] at h
  obtain ⟨hrandomness, hrest⟩ := List.append_inj h (by simp [bytesLE_length]; exact (bytesLE_length 16 _).trans (bytesLE_length 16 _).symm)
  have hrandomness' := List.append_cancel_right hrandomness
  exact ⟨bytesLE_injective hrest, bytesLE_injective hrandomness'⟩
end SphincsSecurity.Concrete
