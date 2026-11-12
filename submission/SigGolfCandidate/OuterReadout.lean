import SigGolfCandidate.OuterCanonicalCoordinate
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterReadout
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3M W9Machine W9Drv.SharedCanonical
open SigGolfCandidate.Research.SharedForest

structure Path (w : SharedV3.WBytes) (coord : Fin 9) (raw : Child) (path : Nat → Digest) (p3 p2 : Digest) : Prop where
  headerPads : ∀ l,l≤SharedV3.lastLevel coord.val → SharedV3.nodeHPad w coord.val (SharedV3.physical coord.val raw.val) l=0
  nodePads : ∀ l,l≤SharedV3.lastLevel coord.val → l<5 → l≠4 → l≠3 → l≠2 → SharedV3.nodePad w coord.val (SharedV3.physical coord.val raw.val) l=0
  nodePad3 : SharedV3.nodePad w coord.val (SharedV3.physical coord.val raw.val) 3=p3
  nodePad2 : SharedV3.nodePad w coord.val (SharedV3.physical coord.val raw.val) 2=p2
  siblings : ∀ l,l≤SharedV3.lastLevel coord.val → SharedV3.sibling w coord.val (SharedV3.physical coord.val raw.val) l=path l
  topOther : SharedV3.topOther w coord.val (SharedV3.physical coord.val raw.val)=path (SharedV3.lastLevel coord.val+1)

theorem of_old {w : SharedV3.WBytes} {coord : Fin 9} {raw : Child} {path : Nat → Digest} {p3 p2 : Digest}
    (h : PathReadout w coord raw path p3 p2) : Path w coord raw path p3 p2 :=
  ⟨h.headerPads,(fun l hl _=>h.nodePads l hl),h.nodePad3,h.nodePad2,h.siblings,h.topOther⟩

theorem to_old_first {w : SharedV3.WBytes} {coord : Fin 9} {raw : Child} {path : Nat → Digest} {p3 p2 : Digest}
    (h : Path w coord raw path p3 p2) (hf : SharedV3.first coord.val=true) : PathReadout w coord raw path p3 p2 := by
  have hn : SharedV3.lastLevel coord.val=4 := by simp only [SharedV3.lastLevel,hf,if_true]
  exact ⟨h.headerPads,(fun l hl=>h.nodePads l hl (by omega)),h.nodePad3,h.nodePad2,h.siblings,h.topOther⟩

theorem childInput (w : SharedV3.WBytes) (index : Nat) (coord : Fin 9)
    (raw : Child) (path : Nat  →  Digest) (padR p3 p2 value : Digest) (level : Nat)
    (h : Path w coord raw path p3 p2) (hl : level ≤ SharedV3.lastLevel coord.val) (hl5 : level<5) :
    SharedV3.childInput w index coord.val (SharedV3.physical coord.val raw.val) padR value level =
      let child := SharedV3.physical coord.val raw.val
      let other := path level
      let left := if child / 2 ^ level % 2 = 0 then value else other
      let right := if child / 2 ^ level % 2 = 0 then other else value
      wctTopInput coord.val index ((128 + child) / 2 ^ (level + 1)) left
        (if level = 4 then padR else if level = 3 then p3 else if level = 2 then p2 else 0) right := by
  simp only [SharedV3.childInput, h.siblings level hl, h.headerPads level hl,
    nodeInput_zero_header]
  by_cases he : level = 4
  · simp only [if_pos he]
  · by_cases h3 : level = 3
    · subst h3; simp only [if_neg he, if_true, h.nodePad3]
    · by_cases h2 : level = 2
      · subst h2; simp only [if_neg he, if_neg h3, if_true, h.nodePad2]
      · simp only [if_neg he, if_neg h3, if_neg h2, h.nodePads level hl hl5 he h3 h2]


#print axioms childInput
#print axioms to_old_first
end OuterReadout
