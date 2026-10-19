import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Sign_Common
set_option Elab.async false

/-!
# Machine-side unfoldings of the stage-A FTS signer (`buildCoordinateF`, `buildChildF`, `ftsCoefs`)

Kept local to the sign machine (stream A-SIGN) so that the spec-level files owned by A-SPEC can change freely.
All factorizations hold by `rfl`.
-/

namespace ClaudeWCT.W9.Machine.Sign
open OracleComp
open SigGolfCandidate.T3 (M Digest)

/-- One chain of `WCT9.buildChildF`: the seed is the family value at `ftsPoint sel i`. -/
def fChildStep (index coord sel : Nat) (word : WCT9.Rank) (coefs : List Digest)
    (state : List Digest × List Digest) (i : Fin 6) : M (List Digest × List Digest) := do
  let secret := WCT9.ftsFamilySeed coefs sel i.val
  let deficit := WCT9.wordDigit word i
  let value ← WCT9.chain index coord sel i.val 0 (4 - deficit) secret
  let last ← WCT9.chain index coord sel i.val (4 - deficit) deficit value
  pure (state.1 ++ [last], state.2 ++ [value])

/-- The six chains of one child. -/
def fChildRows (index coord sel : Nat) (word : WCT9.Rank) (coefs : List Digest) :
    M (List Digest × List Digest) :=
  (List.finRange 6).foldlM (fChildStep index coord sel word coefs) ([], [])

theorem buildChildF_factor (index coord sel : Nat) (word : WCT9.Rank) (coefs : List Digest) (padL : Digest) :
    WCT9.buildChildF index coord sel word coefs padL = (do
      let rows ← fChildRows index coord sel word coefs
      let root ← WCT9.leafHashP index coord sel padL rows.1
      pure (root, rows.2)) := rfl

/-- C1: `WCT9.buildChildH` (leaf of heap `heap`) factors through the same six chains. -/
theorem buildChildH_factorS (heap index coord sel : Nat) (word : WCT9.Rank) (coefs : List Digest) (padL : Digest) :
    WCT9.buildChildH heap index coord sel word coefs padL = (do
      let rows ← fChildRows index coord sel word coefs
      let root ← WCT9.leafHashH heap index coord sel padL rows.1
      pure (root, rows.2)) := rfl

/-- The 128 children of one coordinate (leaf roots, selected child's chain values). -/
def fCoordRows (index : Nat) (coord : WCT9.Coord) (selected : WCT9.Child) (word : WCT9.Rank)
    (coefs : List Digest) (padL : Digest) : M (List Digest × List Digest) :=
  (List.range 128).foldlM (fun (state : List Digest × List Digest) j => do
      let (root, values) ← WCT9.buildChildF index coord.val j word coefs padL
      pure (state.1 ++ [root], (if j = selected.val then values else state.2))) ([], [])

theorem buildCoordinateF_factor (index : Nat) (coord : WCT9.Coord) (selected : WCT9.Child) (word : WCT9.Rank)
    (prev : Digest × Digest) :
    WCT9.buildCoordinateF index coord selected word prev = (do
      let coefs ← WCT9.ftsCoefs index coord.val
      let rows ← fCoordRows index coord selected word coefs prev.1
      let nodes ← WCT9.heapBuild index coord.val prev.2 rows.1
      pure (WCT9.heapLevels nodes, rows.2)) := rfl

/-- One coefficient query of `WCT9.ftsCoefs`. -/
def coefStep (index coord : Nat) (acc : List Digest) (j : Nat) : M (List Digest) := do
  let p ← WCT9.ftsSeedPair index coord j
  pure (acc ++ [p.1, p.2])

theorem ftsCoefs_eq (index coord : Nat) :
    WCT9.ftsCoefs index coord = (List.range' 0 27).foldlM (coefStep index coord) [] := by
  unfold WCT9.ftsCoefs WCT9.ftsCoefPairs
  rw [List.range_eq_range']
  rfl

end ClaudeWCT.W9.Machine.Sign
