import SigGolfCandidate.ClaudeWCT_Numerics_N600PriceChecks_C

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000



namespace ClaudeWCT.Numerics.SharedFees
open ClaudeWCT.Numerics.SharedPathReflection ClaudeWCT.Numerics.SharedMoments
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
set_option Elab.async false

def paidDots : List (Nat × Nat) → Nat → Nat × Nat × Nat
  | (m,t) :: fs, p =>
    if p = 0 then (0,0,0) else
    let n := p &&& (2^4096-1)
    let v := paidDots fs (p >>> 4096)
    (n+v.1,n*m+v.2.1,n*t+v.2.2)
  | [], _ => (0,0,0)

def paidTree : Nat → List (Nat × Nat) → Nat → Nat × Nat × Nat
  | 0, fs, p => paidDots fs p
  | fuel+1, fs, p =>
    if p = 0 then (0,0,0) else
    let half := fs.length / 2
    let lower := p % 2^(4096*half)
    let higher := p >>> (4096*half)
    let a := paidTree fuel (fs.take half) lower
    let b := paidTree fuel (fs.drop half) higher
    (a.1+b.1,a.2.1+b.2.1,a.2.2+b.2.2)

end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.SharedPathList
open ClaudeWCT.Numerics.SharedPathReflection
open ClaudeWCT.Numerics.Kernel (fact)
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
set_option Elab.async false
abbrev Cell := Nat × Nat

def bucket : List Nat → Nat → Nat → Cell
  | [], _, _ => (0,0)
  | b :: bs, c, p =>
    if p = 0 then (0,0) else
    let n := p &&& (2^512-1)
    let v := bucket bs (c+1) (p >>> 512)
    if n = 0 then v else
      ((n <<< (1024*b)) + v.1, ((c*n) <<< (1024*b)) + v.2)

def coordinate (K r : Nat) : Cell :=
  bucket (0 :: binPairs.map Prod.snd) 0 (coordinatePacked 512 K r)

def decode : Nat → Nat → Nat → List Cell
  | 0, _, _ => []
  | fuel+1, p, f =>
    if p = 0 then [] else
    (p &&& (2^1024-1),f &&& (2^1024-1)) :: decode fuel (p >>> 1024) (f >>> 1024)

def product (p : Cell) : List Cell := decode 2047 (p.1^2) (p.2^2)

def cellAdd (a b : Cell) : Cell := (a.1+b.1,a.2+b.2)
def cellSub (a b : Cell) : Cell := (a.1-b.1,a.2-b.2)
def cellScale (w : Nat) (a : Cell) : Cell := (w*a.1,w*a.2)
def cellCross (a b : Cell) : Cell := (a.1*b.1,a.2*b.1+a.1*b.2)

def plus : List Cell → List Cell → List Cell
  | [], bs => bs
  | as, [] => as
  | a::as,b::bs => cellAdd a b :: plus as bs

def prefixes : List Cell → Cell → List Cell
  | [], acc => [acc]
  | a::as, acc => acc :: prefixes as (cellAdd acc a)

def directed (lo hi shift : Nat) (a b : List Cell) : List Cell :=
  let pref := (prefixes (b ++ List.replicate (a.length-b.length) (0,0)) (0,0)).tail
  let win := List.zipWith cellSub
    (List.replicate lo (0,0) ++ pref)
    (List.replicate (hi+1) (0,0) ++ pref)
  List.replicate shift (0,0) ++ List.zipWith cellCross a win

-- Ranges inserted by the scratch generator.
def addRuns : List (Nat × Nat × Nat) := [(0,1,70),(2,3,69),(4,5,68),(6,7,67),(8,9,66),(10,11,65),(12,13,64),(14,15,63),(16,18,62),(19,20,61),(21,22,60),(23,24,59),(25,27,58),(28,29,57),(30,31,56),(32,34,55),(35,36,54),(37,39,53),(40,41,52),(42,44,51),(45,46,50),(47,49,49),(50,51,48),(52,54,47),(55,57,46),(58,60,45),(61,63,44),(64,65,43),(66,68,42),(69,71,41),(72,75,40),(76,78,39),(79,81,38),(82,84,37),(85,87,36),(88,91,35),(92,94,34),(95,98,33),(99,102,32),(103,106,31),(107,110,30),(111,114,29),(115,118,28),(119,122,27),(123,127,26),(128,131,25),(132,136,24),(137,141,23),(142,146,22),(147,152,21),(153,157,20),(158,163,19),(164,169,18),(170,176,17),(177,183,16),(184,191,15),(192,198,14),(199,207,13),(208,216,12),(217,226,11),(227,237,10),(238,250,9),(251,264,8),(265,280,7),(281,299,6),(300,321,5),(322,351,4),(352,392,3),(393,462,2),(463,2046,1)]

def add (a b : List Cell) : List Cell :=
  addRuns.foldl (fun acc e =>
    let forward := directed e.1 e.2.1 e.2.2 a b
    let reverse := if e.2.1 = 0 then [] else directed (max 1 e.1) e.2.1 e.2.2 b a
    plus acc (plus forward reverse)) []

def pair (r : Nat) : List Cell :=
  let branches := (List.range (r+1)).map fun t => product (coordinate 64 t)
  (List.range (r+1)).foldl (fun acc t =>
    let a := branches.getD t []
    let b := branches.getD (r-t) []
    let row := if t=0 then b else if r-t=0 then a else add a b
    let w := fact r / (fact t * fact (r-t))
    plus acc (row.map (cellScale w))) []

def packFirst (xs : List Cell) : Nat := xs.foldr (fun e acc => e.2 + (acc <<< 4096)) 0

def forest (r : Nat) : Nat :=
  packFirst (pair r)^4 * packFirst (decode 1024 (coordinate 128 r).1 (coordinate 128 r).2)
end ClaudeWCT.Numerics.SharedPathList


namespace ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedPathList (Cell coordinate addRuns)
open ClaudeWCT.Numerics.Kernel (fact)
set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000
set_option Elab.async false

def cutMask : Nat := (1 <<< (1024*2048))-1

def hadamard : Nat → Nat → Nat → Nat
  | 0, a, b => a*b
  | h+1, a, b =>
    if a = 0 ∨ b = 0 then 0 else
    let bits := 1024*(2^h)
    let mask := (1 <<< bits)-1
    hadamard h (a &&& mask) (b &&& mask) +
      (hadamard h (a >>> bits) (b >>> bits) <<< bits)

def spread : Nat → Nat → Nat
  | 0, a => a
  | h+1, a =>
    if a=0 then 0 else
    let bits := 1024*(2^h)
    spread h (a &&& ((1 <<< bits)-1)) +
      (spread h (a >>> bits) <<< (4096*(2^h)))

def prefixes (a : Nat) : Nat :=
  (a * (cutMask / ((1 <<< 1024)-1))) &&& cutMask

def window (a lo hi : Nat) : Nat :=
  ((a <<< (1024*lo)) &&& cutMask) - ((a <<< (1024*(hi+1))) &&& cutMask)

def directedFirst (a pref : Cell) (lo hi shift : Nat) : Nat :=
  ((hadamard 11 a.2 (window pref.1 lo hi) +
    hadamard 11 a.1 (window pref.2 lo hi)) <<< (1024*shift)) &&& cutMask

def addFirst (a b : Cell) : Nat :=
  let ap := (prefixes a.1, prefixes a.2)
  let bp := (prefixes b.1, prefixes b.2)
  addRuns.foldl (fun acc e => acc +
    directedFirst a bp e.1 e.2.1 e.2.2 +
    (if e.2.1=0 then 0 else directedFirst b ap (max 1 e.1) e.2.1 e.2.2)) 0

def product (a : Cell) : Cell := (a.1^2,a.2^2)

def pairFirst (r : Nat) : Nat :=
  let branches := (List.range (r+1)).map fun t => product (coordinate 64 t)
  (List.range (r+1)).foldl (fun acc t =>
    let a := branches.getD t (0,0)
    let b := branches.getD (r-t) (0,0)
    let row := if t=0 then b.2 else if r-t=0 then a.2 else addFirst a b
    acc + fact r / (fact t * fact (r-t)) * row) 0

def forest (r : Nat) : Nat :=
  (spread 11 (pairFirst r))^4 * spread 10 (coordinate 128 r).2
end ClaudeWCT.Numerics.SharedPathPacked

/-! Kernel-friendly evaluation of the packed paired-forest arithmetic.  The functions below compute
exactly the same natural numbers as `hadamard`, `spread`, `directedFirst`, `addFirst`, `pairFirst`
and `forest` (see the `*_eq_fast` theorems), but are written with an explicit `Nat.rec`, primitive
`Nat` operations (GMP-accelerated in the kernel) and one fused traversal for the two Hadamard
products of `directedFirst`, so that `decide +kernel` performs far fewer reduction steps. -/
namespace ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedPathList (Cell coordinate addRuns)
open ClaudeWCT.Numerics.Kernel (fact)
set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000
set_option Elab.async false

/-- `had2 h a w c v = hadamard h a w + hadamard h c v` (theorem `had2_eq`). -/
def had2 (h : Nat) : Nat → Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat)
    (fun a w c v => Nat.add (Nat.mul a w) (Nat.mul c v))
    (fun h ih a w c v =>
      cond ((Nat.beq a 0 || Nat.beq w 0) && (Nat.beq c 0 || Nat.beq v 0)) 0
        (Nat.add
          (ih (Nat.land a (Nat.sub (Nat.shiftLeft 1 (Nat.mul 1024 (Nat.pow 2 h))) 1))
              (Nat.land w (Nat.sub (Nat.shiftLeft 1 (Nat.mul 1024 (Nat.pow 2 h))) 1))
              (Nat.land c (Nat.sub (Nat.shiftLeft 1 (Nat.mul 1024 (Nat.pow 2 h))) 1))
              (Nat.land v (Nat.sub (Nat.shiftLeft 1 (Nat.mul 1024 (Nat.pow 2 h))) 1)))
          (Nat.shiftLeft
            (ih (Nat.shiftRight a (Nat.mul 1024 (Nat.pow 2 h)))
                (Nat.shiftRight w (Nat.mul 1024 (Nat.pow 2 h)))
                (Nat.shiftRight c (Nat.mul 1024 (Nat.pow 2 h)))
                (Nat.shiftRight v (Nat.mul 1024 (Nat.pow 2 h))))
            (Nat.mul 1024 (Nat.pow 2 h))))) h

theorem hadamard_zero_left (h b : Nat) : hadamard h 0 b = 0 := by
  cases h with
  | zero => exact Nat.zero_mul b
  | succ h => rw [hadamard, if_pos (Or.inl rfl)]

theorem hadamard_zero_right (h a : Nat) : hadamard h a 0 = 0 := by
  cases h with
  | zero => exact Nat.mul_zero a
  | succ h => rw [hadamard, if_pos (Or.inr rfl)]

theorem hadamard_succ_split (h a b : Nat) :
    hadamard (h+1) a b =
      hadamard h (a &&& ((1 <<< (1024*2^h))-1)) (b &&& ((1 <<< (1024*2^h))-1)) +
        (hadamard h (a >>> (1024*2^h)) (b >>> (1024*2^h)) <<< (1024*2^h)) := by
  rw [hadamard]
  by_cases hz : a = 0 ∨ b = 0
  · rw [if_pos hz]
    rcases hz with rfl | rfl
    · simp only [Nat.zero_and, Nat.zero_shiftRight, hadamard_zero_left, Nat.zero_shiftLeft,
        Nat.add_zero]
    · simp only [Nat.zero_and, Nat.zero_shiftRight, hadamard_zero_right, Nat.zero_shiftLeft,
        Nat.add_zero]
  · rw [if_neg hz]

theorem had2_eq (h a w c v : Nat) : had2 h a w c v = hadamard h a w + hadamard h c v := by
  induction h generalizing a w c v with
  | zero => rfl
  | succ h ih =>
    cases hb : ((Nat.beq a 0 || Nat.beq w 0) && (Nat.beq c 0 || Nat.beq v 0)) with
    | true =>
      have e : had2 (h+1) a w c v = 0 := by
        show cond _ 0 _ = 0
        rw [hb]
        rfl
      simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq] at hb
      have h1 : hadamard (h+1) a w = 0 := by
        rcases hb.1 with h1 | h1
        · subst h1; exact hadamard_zero_left _ _
        · subst h1; exact hadamard_zero_right _ _
      have h2 : hadamard (h+1) c v = 0 := by
        rcases hb.2 with h2 | h2
        · subst h2; exact hadamard_zero_left _ _
        · subst h2; exact hadamard_zero_right _ _
      simp only [e, h1, h2, Nat.add_zero]
    | false =>
      have e : had2 (h+1) a w c v =
          had2 h (a &&& ((1 <<< (1024*2^h))-1)) (w &&& ((1 <<< (1024*2^h))-1))
              (c &&& ((1 <<< (1024*2^h))-1)) (v &&& ((1 <<< (1024*2^h))-1)) +
            (had2 h (a >>> (1024*2^h)) (w >>> (1024*2^h)) (c >>> (1024*2^h)) (v >>> (1024*2^h))
              <<< (1024*2^h)) := by
        show cond _ 0 _ = _
        rw [hb]
        rfl
      rw [e, ih, ih, hadamard_succ_split h a w, hadamard_succ_split h c v]
      simp only [Nat.shiftLeft_eq, Nat.add_mul]
      omega

/-- `spreadFast = spread` (theorem `spread_eq_fast`). -/
def spreadFast (h : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun a => a)
    (fun h ih a =>
      cond (Nat.beq a 0) 0
        (Nat.add (ih (Nat.land a (Nat.sub (Nat.shiftLeft 1 (Nat.mul 1024 (Nat.pow 2 h))) 1)))
          (Nat.shiftLeft (ih (Nat.shiftRight a (Nat.mul 1024 (Nat.pow 2 h))))
            (Nat.mul 4096 (Nat.pow 2 h))))) h

theorem spread_eq_fast : spread = spreadFast := by
  funext h a
  induction h generalizing a with
  | zero => rfl
  | succ h ih =>
    rw [spread]
    by_cases hz : a = 0
    · subst hz
      rw [if_pos rfl]
      rfl
    · rw [if_neg hz]
      have hb : Nat.beq a 0 = false := by
        cases hc : Nat.beq a 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true hc) hz
      have e : spreadFast (h+1) a =
          spreadFast h (a &&& ((1 <<< (1024*2^h))-1)) +
            (spreadFast h (a >>> (1024*2^h)) <<< (4096*2^h)) := by
        show cond _ 0 _ = _
        rw [hb]
        rfl
      rw [e]
      show spread h (a &&& ((1 <<< (1024*2^h))-1)) + (spread h (a >>> (1024*2^h)) <<< (4096*2^h)) = _
      rw [ih, ih]

def directedFirstFast (a pref : Cell) (lo hi shift : Nat) : Nat :=
  Nat.land (Nat.shiftLeft (had2 11 a.2 (window pref.1 lo hi) a.1 (window pref.2 lo hi))
    (Nat.mul 1024 shift)) cutMask

theorem directedFirst_eq_fast : directedFirst = directedFirstFast := by
  funext a pref lo hi shift
  unfold directedFirst directedFirstFast
  rw [had2_eq]
  rfl

def addFirstFast (a b : Cell) : Nat :=
  let ap := (prefixes a.1, prefixes a.2)
  let bp := (prefixes b.1, prefixes b.2)
  addRuns.foldl (fun acc e => acc +
    directedFirstFast a bp e.1 e.2.1 e.2.2 +
    (if e.2.1=0 then 0 else directedFirstFast b ap (max 1 e.1) e.2.1 e.2.2)) 0

theorem addFirst_eq_fast : addFirst = addFirstFast := by
  funext a b
  unfold addFirst addFirstFast
  rw [directedFirst_eq_fast]

def pairFirstFast (r : Nat) : Nat :=
  let branches := (List.range (r+1)).map fun t => product (coordinate 64 t)
  (List.range (r+1)).foldl (fun acc t =>
    let a := branches.getD t (0,0)
    let b := branches.getD (r-t) (0,0)
    let row := if t=0 then b.2 else if r-t=0 then a.2 else addFirstFast a b
    acc + fact r / (fact t * fact (r-t)) * row) 0

theorem pairFirst_eq_fast : pairFirst = pairFirstFast := by
  funext r
  unfold pairFirst pairFirstFast
  rw [addFirst_eq_fast]

def forestFast (r : Nat) : Nat :=
  (spreadFast 11 (pairFirstFast r))^4 * spreadFast 10 (coordinate 128 r).2

theorem forest_eq_fast : forest = forestFast := by
  funext r
  unfold forest forestFast
  rw [spread_eq_fast, pairFirst_eq_fast]

end ClaudeWCT.Numerics.SharedPathPacked
