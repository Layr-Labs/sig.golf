import SigGolfCandidate.OuterAdmissible
import SigGolfCandidate.Merge098
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterKeygenRun
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.T3M OracleComp
open OuterImageValidity

theorem run_eq (sk : SecretKey) : sub.run .keygen sk=SigGolfCandidate.T3M.submission.run .keygen sk := by
  have hk : sub.image .keygen=SigGolfCandidate.T3M.submission.image .keygen:=rfl
  exact ClaudeWCT.W9.T3M.Final.run_keygen_congr (iA:=sub.image) (iB:=SigGolfCandidate.T3M.submission.image)
    hk OuterAdmissible.keygen SigGolfCandidate.T3M.submission_keygen_valid rfl rfl rfl sk

theorem counts (sk : SecretKey) :
    (fun r=>(r.value,r.hashCalls,r.hashCompressions)) <$> sub.run .keygen sk=
      (fun p=>(some ((p.1.1 : PublicKey),cacheB p.1.2),p.2.1,p.2.2)) <$>
        countBoth (mrealize sk SigGolfCandidate.T3.keygen) := by
  rw [run_eq]
  exact SigGolfCandidate.T3M.Keygen.keygen_run_counts sk

theorem runWith_eq (hash : Hash) (sk : SecretKey) :
    sub.runWith hash .keygen sk=SigGolfCandidate.T3M.submission.runWith hash .keygen sk :=
  congrArg (evalWithAnswerFn hash) (run_eq sk)
#print axioms run_eq
#print axioms counts
#print axioms runWith_eq
end OuterKeygenRun
