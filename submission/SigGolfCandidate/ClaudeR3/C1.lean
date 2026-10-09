import SigGolfCandidate.ClaudeWCT.Numerics.N600Cover
import SigGolfCandidate.ClaudeR3.D1

namespace ClaudeR3.Tab
open ClaudeWCT.Numerics.N600 (T6 lookup pT zipT mapT histT g1T g2T words noFree)

def selW (t : Nat) (P : List (List Nat × Nat)) : List (List Nat × Nat) :=
  P.filterMap fun p => match p.1 with
    | [] => none
    | h :: r => if h = t then some (r, p.2) else none

def indW : Nat → List (List Nat × Nat) → T6
  | 0, P => .leaf (P.foldr (fun p s => p.2 + s) 0)
  | n + 1, P => .node (indW n (selW 0 P)) (indW n (selW 1 P)) (indW n (selW 2 P)) (indW n (selW 3 P))
      (indW n (selW 4 P)) (indW n (selW 5 P))

def keyItems : List (List Nat × Nat) := List.zipWith (fun w l => (w, 1024 ^ l)) words levs

inductive KB where
  | nil
  | node (l : KB) (k i : Nat) (r : KB)

noncomputable def KB.find (t : KB) (x : Nat) : Nat :=
  KB.rec (motive := fun _ => Nat) 0
    (fun _ k i _ rl rr => cond (Nat.blt x k) rl (cond (Nat.blt k x) rr (i + 1))) t

def build : Nat → List (Nat × Nat) → KB
  | 0, _ => .nil
  | n + 1, l =>
    match l.drop (l.length / 2) with
    | [] => .nil
    | (k, i) :: rest => .node (build n (l.take (l.length / 2))) k i (build n rest)

abbrev Tab := List (Nat × Int)

def keyIdxOf (tab : Tab) : List (Nat × Nat) := (tab.map (·.1)).zipIdx

noncomputable section
def keyT : T6 := pT (indW 6 keyItems)
def bstOf (tab : Tab) : KB := build 16 (keyIdxOf tab)
def idxOf (tab : Tab) : T6 := mapT (fun k => KB.find (bstOf tab) k) keyT
def chunkT (x : T6) (lo len : Nat) : T6 := mapT (fun i => cond (Nat.blt lo i && Nat.ble i (lo + len)) (i - lo) 0) x
def fourT : Nat → Nat → T6
  | 0, a => .leaf a
  | n + 1, a => .node (fourT n a) (fourT n a) (fourT n a) (fourT n a) (fourT n a) (fourT n (a + 1))
def gNearT : T6 := zipT Nat.mul g1T (fourT 6 0)
end

def posPart (z : Int) : Nat := z.toNat
def negPart (z : Int) : Nat := (-z).toNat

def chunkData (tab : Tab) (lo len : Nat) (s0 : Int) : List (Nat × Int) :=
  (0, s0) :: (((tab.drop lo).take len).zipIdx.map fun p => (p.2 + 1, p.1.2))

def packS (hb : Nat) (d : List (Nat × Int)) (neg : Bool) : Nat :=
  d.foldr (fun e s => (if neg then negPart e.2 else posPart e.2) * hb ^ e.1 + s) 0

noncomputable section
def missCheck (tab : Tab) (g : T6) : Bool := histT 0 (idxOf tab) noFree g false == (0, 0)
def histBound (tab : Tab) (g : T6) (m : Nat) : Bool :=
  let h := histT 1 (idxOf tab) noFree g false
  Nat.blt h.1 (2 ^ (m - 1)) && Nat.blt h.2 (2 ^ (m - 1))
def chunkCheck (tab : Tab) (g : T6) (m lo len : Nat) (s0 : Int) : Bool :=
  let h := histT (2 ^ m) (chunkT (idxOf tab) lo len) noFree g false
  let d := chunkData tab lo len s0
  Nat.beq (h.1 + packS (2 ^ m) d true) (h.2 + packS (2 ^ m) d false) &&
    Nat.blt (packS 1 d true) (2 ^ (m - 1)) && Nat.blt (packS 1 d false) (2 ^ (m - 1))
end

end ClaudeR3.Tab
