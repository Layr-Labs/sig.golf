import SigGolfCandidate.OuterSignLook
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterSignCoordinateCode
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Verify ClaudeWCT.W9.Machine.Sign

theorem reuse : SharedReuse.Fetch OuterImages.signImage := by
  constructor
  · exact OuterSignLook.transfer _ SharedReuse.installed_fetch.head (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro c hc
    have h : ∀c:Fin 9,SharedReuse.coordLook c.val 1977=none ∧ SharedReuse.coordLook c.val 25338=none ∧ SharedReuse.coordLook c.val 25963=none := by decide +kernel
    exact OuterSignLook.transfer _ (SharedReuse.installed_fetch.coordinate c hc) (h ⟨c,hc⟩).1 (h ⟨c,hc⟩).2.1 (h ⟨c,hc⟩).2.2

structure Code (c : Nat) : Prop where
  field : LookOK OuterImages.signImage (SharedField.look c)
  leaf : LookOK OuterImages.signImage (SharedLeaf.look c)
  hook : LookOK OuterImages.signImage (SharedLeaf.hookLook c)
  next : LookOK OuterImages.signImage (SharedNext.look c)
  node : LookOK OuterImages.signImage (SharedNode.look c)
  tail : LookOK OuterImages.signImage (SharedTail.look c)
  finish : LookOK OuterImages.signImage (SharedFinish.look c)
  path : LookOK OuterImages.signImage (SharedPath.look c)
  ending : LookOK OuterImages.signImage (SharedEnd.look c)

theorem installed (c : Nat) (hc : c<9) : Code c := by
  have ho:=SharedCoordinate.installed_Code c hc
  constructor
  · have h : ∀c:Fin 9,SharedField.look c.val 1977=none ∧ SharedField.look c.val 25338=none ∧ SharedField.look c.val 25963=none := by decide +kernel
    exact OuterSignLook.transfer _ ho.field (h ⟨c,hc⟩).1 (h ⟨c,hc⟩).2.1 (h ⟨c,hc⟩).2.2
  · have h : ∀c:Fin 9,SharedLeaf.look c.val 1977=none ∧ SharedLeaf.look c.val 25338=none ∧ SharedLeaf.look c.val 25963=none := by decide +kernel
    exact OuterSignLook.transfer _ ho.leaf (h ⟨c,hc⟩).1 (h ⟨c,hc⟩).2.1 (h ⟨c,hc⟩).2.2
  · have h : ∀c:Fin 9,SharedLeaf.hookLook c.val 1977=none ∧ SharedLeaf.hookLook c.val 25338=none ∧ SharedLeaf.hookLook c.val 25963=none := by decide +kernel
    exact OuterSignLook.transfer _ ho.hook (h ⟨c,hc⟩).1 (h ⟨c,hc⟩).2.1 (h ⟨c,hc⟩).2.2
  · have h : ∀c:Fin 9,SharedNext.look c.val 1977=none ∧ SharedNext.look c.val 25338=none ∧ SharedNext.look c.val 25963=none := by decide +kernel
    exact OuterSignLook.transfer _ ho.next (h ⟨c,hc⟩).1 (h ⟨c,hc⟩).2.1 (h ⟨c,hc⟩).2.2
  · have h : ∀c:Fin 9,SharedNode.look c.val 1977=none ∧ SharedNode.look c.val 25338=none ∧ SharedNode.look c.val 25963=none := by decide +kernel
    exact OuterSignLook.transfer _ ho.node (h ⟨c,hc⟩).1 (h ⟨c,hc⟩).2.1 (h ⟨c,hc⟩).2.2
  · have h : ∀c:Fin 9,SharedTail.look c.val 1977=none ∧ SharedTail.look c.val 25338=none ∧ SharedTail.look c.val 25963=none := by decide +kernel
    exact OuterSignLook.transfer _ ho.tail (h ⟨c,hc⟩).1 (h ⟨c,hc⟩).2.1 (h ⟨c,hc⟩).2.2
  · have h : ∀c:Fin 9,SharedFinish.look c.val 1977=none ∧ SharedFinish.look c.val 25338=none ∧ SharedFinish.look c.val 25963=none := by decide +kernel
    exact OuterSignLook.transfer _ ho.finish (h ⟨c,hc⟩).1 (h ⟨c,hc⟩).2.1 (h ⟨c,hc⟩).2.2
  · have h : ∀c:Fin 9,SharedPath.look c.val 1977=none ∧ SharedPath.look c.val 25338=none ∧ SharedPath.look c.val 25963=none := by decide +kernel
    exact OuterSignLook.transfer _ ho.path (h ⟨c,hc⟩).1 (h ⟨c,hc⟩).2.1 (h ⟨c,hc⟩).2.2
  · have h : ∀c:Fin 9,SharedEnd.look c.val 1977=none ∧ SharedEnd.look c.val 25338=none ∧ SharedEnd.look c.val 25963=none := by decide +kernel
    exact OuterSignLook.transfer _ ho.ending (h ⟨c,hc⟩).1 (h ⟨c,hc⟩).2.1 (h ⟨c,hc⟩).2.2

#print axioms reuse
#print axioms installed
end OuterSignCoordinateCode
