import SigGolfCandidate.ClaudeWCT.W9.T3M.Final.Pending
import SigGolfCandidate.T3M.Keygen.Main

namespace ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.Legacy OracleComp
open ClaudeWCT.W9.T3M (Images submission)
variable (I : Images)
theorem run_keygen_congr {sA wA sB wB c : Nat} {lA lB : Layout} {iA iB : Phase → Riscv.Image}
    (hk : iA .keygen = iB .keygen) (hvA : (iA .keygen).Valid ⟨sA, wA, c⟩ lA)
    (hvB : (iB .keygen).Valid ⟨sB, wB, c⟩ lB) (hsk : lA.secretKey = lB.secretKey)
    (hpk : lA.publicKey = lB.publicKey) (hc : lA.cache = lB.cache) (sk : SecretKey) :
    Submission.run ⟨⟨sA, wA, c⟩, lA, iA⟩ .keygen sk = Submission.run ⟨⟨sB, wB, c⟩, lB, iB⟩ .keygen sk := by
  obtain ⟨mA, skA, pkA, cA, sgA, wtA⟩ := lA
  obtain ⟨mB, skB, pkB, cB, sgB, wtB⟩ := lB
  dsimp only at hsk hpk hc
  subst hsk hpk hc
  have hinit : initialState ⟨⟨sA, wA, c⟩, ⟨mA, skA, pkA, cA, sgA, wtA⟩, iA⟩ .keygen sk =
      initialState ⟨⟨sB, wB, c⟩, ⟨mB, skA, pkA, cA, sgB, wtB⟩, iB⟩ .keygen sk := by
    unfold initialState
    dsimp only
    rw [if_pos hvA, if_pos hvB, hk]
    rfl
  unfold Submission.run
  rw [hinit]
  dsimp only
  rw [hk]
  rfl
theorem keygen_run_eq (hadm : (submission I).Admissible) (sk : SecretKey) :
    (submission I).run .keygen sk = SigGolfCandidate.T3M.submission.run .keygen sk := by
  have hvA : ((submission I).image .keygen).Valid ⟨5456, 21484, 131072⟩ ⟨0x5BF0, 0x80, 0xA0, 0x80000, 0x7000, 0x800⟩ :=
    hadm.2 .keygen
  have hvB : (SigGolfCandidate.T3M.submission.image .keygen).Valid
      ⟨SigGolfCandidate.T3M.submission.sizes.signature, SigGolfCandidate.T3M.submission.sizes.witness, 131072⟩
      SigGolfCandidate.T3M.submission.layout := SigGolfCandidate.T3M.submission_keygen_valid
  have hk : (submission I).image .keygen = SigGolfCandidate.T3M.submission.image .keygen := by
    rw [ClaudeWCT.W9.T3M.submission_keygen, SigGolfCandidate.T3M.submission_keygen]
  exact run_keygen_congr (iA := (submission I).image) (iB := SigGolfCandidate.T3M.submission.image) hk hvA hvB
    (by rw [SigGolfCandidate.T3M.submission_layout]) (by rw [SigGolfCandidate.T3M.submission_layout])
    (by rw [SigGolfCandidate.T3M.submission_layout]) sk
theorem keygen_run_counts_holds (hadm : (submission I).Admissible) : KeygenRunCounts I := fun sk => by
  rw [keygen_run_eq I hadm sk]
  exact SigGolfCandidate.T3M.Keygen.keygen_run_counts sk
theorem keygen_runWith_holds (hadm : (submission I).Admissible) : KeygenRunWith I := fun hash sk => by
  unfold Submission.runWith
  rw [keygen_run_eq I hadm sk]
  exact SigGolfCandidate.T3M.Keygen.keygen_runWith hash sk
end ClaudeWCT.W9.T3M.Final
