import SigGolfCandidate.OuterSignFrontCodes
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterSignNonceSearch
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.Research
open SigGolfCandidate.T3M.Sign SigGolfCandidate.T3M.Sign.Boundary
open ClaudeWCT.W9.Machine.Sign ClaudeWCT.W9.Machine.Sign.SharedDigestBoundary
open ClaudeWCT.W9.Machine.Sign.SharedFront
theorem nonce_search {sk : SecretKey} {cache : Bytes 131072} {msg : SigGolfCandidate.T3.Message}
    {α : Type} {W : Nat} {Q : Option α→MachineState→Prop}
    (htables : ∀rho t,NoncePost sk cache msg rho t → SharedDigest.TablesAt false t)
    (K : BitVec 128→BitVec 32→BitVec 256→SigGolfCandidate.T3.M (Option α))
    (hfail : ∀t,JoinedPost OuterImages.signImage t none t → Q none t)
    (hrest : ∀rho s,NoncePost sk cache msg rho s → ∀c a t,
      JoinedPost OuterImages.signImage s (some (c,a)) t → TBSim OuterImages.signImage sk t W (K rho c a) Q) :
    TBSim OuterImages.signImage sk (sinit sk cache msg) (SigGolfCandidate.T3M.Sign.frontC+(1+((11*2^17)*200+20+W))) (do
      let tag ← SigGolfCandidate.T3.privateMac (cacheDec cache).region
      if tag ≠ (cacheDec cache).tag then pure none else do
        let rho ← SigGolfCandidate.T3.privateNonce msg
        let r ← SharedForest.sharedDigestSearch rho msg 0 ((11*2^17))
        match r with
        | none => pure none
        | some (c,a) => K rho c a) Q := by
  letI : DigestLabel.Code OuterImages.signImage false:=OuterSignFrontCodes.label
  apply Sign.Boundary.Generic.nonce_front OuterImages.signImage OuterSignFrontCodes.front OuterSignFrontCodes.mac
  · intro t ht
    exact hfail t ⟨ht.pc,ht.x5,ht.x10,(OuterSignFrontCodes.halt.fetch t ht.pc).trans rfl⟩
  · intro rho s hn
    obtain ⟨u,su,pu,ru,fu⟩:=SharedNonceJump.steps OuterSignFrontCodes.jump s hn.search.pc
    have hp : SharedDigest.Pre false rho msg u := by
      refine ⟨(ru.get (by simp)).trans hn.search.x5,?_,?_,?_⟩
      · exact hn.search.rho.frame fu (by unfold SigGolfCandidate.T3M.Sign.DIG;decide) (by tauto) (by tauto)
      · intro k hk
        rw [fu.get (by unfold ClaudeWCT.W9.Machine.Sign.DIG;omega) (by tauto)]
        exact hn.search.msg k hk
      · exact (htables rho s hn).frame (fu.mono (fun _ _ h=>h.elim))
    apply TBSim.steps su
    refine TBSim.bind (search_to_forest OuterSignFrontCodes.look OuterSignFrontCodes.success OuterSignFrontCodes.failureJump OuterSignFrontCodes.failure OuterSignFrontCodes.halt hp pu) (W₂:=W) ?_
    intro r t ht
    cases r with
    | none => exact (TBSim.pure (hfail t ht)).mono (by omega) (fun _ _ h=>h)
    | some r => exact hrest rho s hn r.1 r.2 t (joined_prepend fu ht)

#print axioms nonce_search
end OuterSignNonceSearch
