import SigGolfCandidate.ClaudeWCT.Numerics.N600Data
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.IntervalCases
import SigGolfCandidate.ClaudeWCT.Numerics.CoverWF

section


namespace ClaudeWCT.Numerics.N600
inductive T5 where
  | leaf (z : Nat)
  | node (a b c d e : T5)
def lookup : T5 → List Nat → Nat
  | .leaf z, _ => z
  | .node _ _ _ _ _, [] => 0
  | .node a _ _ _ _, 0 :: l => lookup a l
  | .node _ b _ _ _, 1 :: l => lookup b l
  | .node _ _ c _ _, 2 :: l => lookup c l
  | .node _ _ _ d _, 3 :: l => lookup d l
  | .node _ _ _ _ e, _ :: l => lookup e l
def sel (t : Nat) (P : List (List Nat)) : List (List Nat) :=
  P.filterMap fun p => match p with
    | [] => none
    | h :: r => if h = t then some r else none
def indT : Nat → List (List Nat) → T5
  | 0, P => .leaf P.length
  | n + 1, P => .node (indT n (sel 0 P)) (indT n (sel 1 P)) (indT n (sel 2 P)) (indT n (sel 3 P)) (indT n (sel 4 P))
def spair (b : Bool) (h : Nat) : Nat × Nat := cond b (0, h) (h, 0)
def padd (x y : Nat × Nat) : Nat × Nat := (Nat.add x.1 y.1, Nat.add x.2 y.2)
noncomputable section
def zipT (op : Nat → Nat → Nat) (x : T5) : T5 → T5 :=
  T5.rec (motive := fun _ => T5 → T5)
    (fun a y => T5.casesOn (motive := fun _ => T5) y (fun b => .leaf (op a b)) (fun _ _ _ _ _ => .leaf a))
    (fun _ _ _ _ _ ra rb rc rd re y => T5.casesOn (motive := fun _ => T5) y (fun _ => .leaf 0)
      (fun a' b' c' d' e' => .node (ra a') (rb b') (rc c') (rd d') (re e')))
    x
def mapT (op : Nat → Nat) (x : T5) : T5 :=
  T5.rec (motive := fun _ => T5) (fun a => .leaf (op a)) (fun _ _ _ _ _ ra rb rc rd re => .node ra rb rc rd re) x
def pT (x : T5) : T5 :=
  T5.rec (motive := fun _ => T5) (fun a => .leaf a)
    (fun _ _ _ _ _ a' b' c' d' _ =>
      let s2 := zipT Nat.add a' b'
      let s3 := zipT Nat.add s2 c'
      .node (mapT (fun _ => 0) a') a' s2 s3 (zipT Nat.add s3 d')) x
def dT (x : T5) : T5 :=
  T5.rec (motive := fun _ => T5) (fun a => .leaf a)
    (fun _ _ _ _ _ a' b' c' d' e' =>
      .node (zipT Nat.sub b' a') (zipT Nat.sub c' b') (zipT Nat.sub d' c') (zipT Nat.sub e' d') e') x
def histT (hb : Nat) (c : T5) : List Bool → T5 → Bool → Nat × Nat :=
  T5.rec (motive := fun _ => List Bool → T5 → Bool → Nat × Nat)
    (fun cv _ g neg => T5.casesOn (motive := fun _ => Nat × Nat) g
      (fun gv => cond (Nat.beq gv 0) (0, 0) (spair neg (Nat.mul gv (Nat.pow hb cv))))
      (fun _ _ _ _ _ => (0, 0)))
    (fun _ _ _ _ _ r0 r1 r2 r3 r4 fr g neg => List.casesOn (motive := fun _ => Nat × Nat) fr (0, 0)
      (fun f fs => T5.casesOn (motive := fun _ => Nat × Nat) g (fun _ => (0, 0))
        (fun g0 g1 g2 g3 g4 => cond f (r4 fs g4 neg)
          (padd (r0 fs g0 (!neg)) (padd (r1 fs g1 (!neg)) (padd (r2 fs g2 (!neg))
            (padd (r3 fs g3 (!neg)) (r4 fs g4 neg))))))))
    c
def cntT : T5 := pT (indT 7 words)
def g1T : T5 := dT cntT
def g2T : T5 := dT (mapT (fun z => Nat.mul z z) cntT)
end
def noFree : List Bool := [false, false, false, false, false, false, false]
def freeList (t : Nat) : List Bool := [t == 0, t == 1, t == 2, t == 3, t == 4, t == 5, t == 6]
open ClaudeWCT.Numerics.Kernel (HB histEq massOk)
noncomputable section
def w1Check : Bool := histEq (histT HB cntT noFree g1T false) w1Data
def w1MassCheck : Bool := massOk (histT 1 cntT noFree g1T false) w1Data
def wfCheck (t : Nat) : Bool := histEq (histT HB cntT (freeList t) g1T false) (wfData t)
def wfMassCheck (t : Nat) : Bool := massOk (histT 1 cntT (freeList t) g1T false) (wfData t)
def w2Check : Bool := histEq (histT HB cntT noFree g2T false) w2Data
def w2MassCheck : Bool := massOk (histT 1 cntT noFree g2T false) w2Data
end
end ClaudeWCT.Numerics.N600
end

section




namespace ClaudeWCT.Numerics.N600
open Finset
def Full : ℕ → T5 → Prop
  | 0, .leaf _ => True
  | 0, .node _ _ _ _ _ => False
  | _ + 1, .leaf _ => False
  | n + 1, .node a b c d e => Full n a ∧ Full n b ∧ Full n c ∧ Full n d ∧ Full n e
def pick (t : ℕ) (a b c d e : T5) : T5 :=
  match t with
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d
  | _ => e
theorem lookup_node_cons (a b c d e : T5) (t : ℕ) (l : List ℕ) :
    lookup (.node a b c d e) (t :: l) = lookup (pick t a b c d e) l := by
  rcases t with _ | _ | _ | _ | t <;> rfl
theorem full_pick {n : ℕ} {a b c d e : T5} (h : Full (n + 1) (.node a b c d e)) (t : ℕ) :
    Full n (pick t a b c d e) := by
  obtain ⟨ha, hb, hc, hd, he⟩ := h
  rcases t with _ | _ | _ | _ | t <;> assumption
@[simp] theorem zipT_leaf_leaf (op : ℕ → ℕ → ℕ) (a b : ℕ) :
    zipT op (.leaf a) (.leaf b) = .leaf (op a b) := rfl
@[simp] theorem zipT_node_node (op : ℕ → ℕ → ℕ) (a b c d e a' b' c' d' e' : T5) :
    zipT op (.node a b c d e) (.node a' b' c' d' e') =
      .node (zipT op a a') (zipT op b b') (zipT op c c') (zipT op d d') (zipT op e e') := rfl
@[simp] theorem mapT_leaf (op : ℕ → ℕ) (a : ℕ) : mapT op (.leaf a) = .leaf (op a) := rfl
@[simp] theorem mapT_node (op : ℕ → ℕ) (a b c d e : T5) :
    mapT op (.node a b c d e) = .node (mapT op a) (mapT op b) (mapT op c) (mapT op d) (mapT op e) := rfl
@[simp] theorem pT_leaf (a : ℕ) : pT (.leaf a) = .leaf a := rfl
theorem pT_node (a b c d e : T5) :
    pT (.node a b c d e) = .node (mapT (fun _ => 0) (pT a)) (pT a) (zipT Nat.add (pT a) (pT b))
      (zipT Nat.add (zipT Nat.add (pT a) (pT b)) (pT c))
      (zipT Nat.add (zipT Nat.add (zipT Nat.add (pT a) (pT b)) (pT c)) (pT d)) := rfl
@[simp] theorem dT_leaf (a : ℕ) : dT (.leaf a) = .leaf a := rfl
theorem dT_node (a b c d e : T5) :
    dT (.node a b c d e) = .node (zipT Nat.sub (dT b) (dT a)) (zipT Nat.sub (dT c) (dT b))
      (zipT Nat.sub (dT d) (dT c)) (zipT Nat.sub (dT e) (dT d)) (dT e) := rfl
theorem full_zipT (op : ℕ → ℕ → ℕ) : ∀ n x y, Full n x → Full n y → Full n (zipT op x y)
  | 0, .leaf _, .leaf _, _, _ => trivial
  | n + 1, .node a b c d e, .node a' b' c' d' e', ⟨ha, hb, hc, hd, he⟩, ⟨ha', hb', hc', hd', he'⟩ =>
    ⟨full_zipT op n a a' ha ha', full_zipT op n b b' hb hb', full_zipT op n c c' hc hc',
      full_zipT op n d d' hd hd', full_zipT op n e e' he he'⟩
theorem full_mapT (op : ℕ → ℕ) : ∀ n x, Full n x → Full n (mapT op x)
  | 0, .leaf _, _ => trivial
  | n + 1, .node a b c d e, ⟨ha, hb, hc, hd, he⟩ =>
    ⟨full_mapT op n a ha, full_mapT op n b hb, full_mapT op n c hc, full_mapT op n d hd, full_mapT op n e he⟩
theorem full_pT : ∀ n x, Full n x → Full n (pT x)
  | 0, .leaf _, _ => trivial
  | n + 1, .node a b c d e, ⟨ha, hb, hc, hd, he⟩ => by
    have ha' := full_pT n a ha
    have hb' := full_pT n b hb
    have hc' := full_pT n c hc
    have hd' := full_pT n d hd
    rw [pT_node]
    exact ⟨full_mapT _ n _ ha', ha', full_zipT _ n _ _ ha' hb', full_zipT _ n _ _ (full_zipT _ n _ _ ha' hb') hc',
      full_zipT _ n _ _ (full_zipT _ n _ _ (full_zipT _ n _ _ ha' hb') hc') hd'⟩
theorem full_dT : ∀ n x, Full n x → Full n (dT x)
  | 0, .leaf _, _ => trivial
  | n + 1, .node a b c d e, ⟨ha, hb, hc, hd, he⟩ => by
    have ha' := full_dT n a ha
    have hb' := full_dT n b hb
    have hc' := full_dT n c hc
    have hd' := full_dT n d hd
    have he' := full_dT n e he
    rw [dT_node]
    exact ⟨full_zipT _ n _ _ hb' ha', full_zipT _ n _ _ hc' hb', full_zipT _ n _ _ hd' hc',
      full_zipT _ n _ _ he' hd', he'⟩
theorem full_indT : ∀ n P, Full n (indT n P)
  | 0, _ => trivial
  | n + 1, _ => ⟨full_indT n _, full_indT n _, full_indT n _, full_indT n _, full_indT n _⟩
theorem lookup_zipT (op : ℕ → ℕ → ℕ) : ∀ n x y l, Full n x → Full n y → l.length = n →
    lookup (zipT op x y) l = op (lookup x l) (lookup y l)
  | 0, .leaf _, .leaf _, [], _, _, _ => rfl
  | n + 1, .node a b c d e, .node a' b' c' d' e', t :: l, hx, hy, hl => by
    have hl' : l.length = n := by simpa using hl
    rw [zipT_node_node, lookup_node_cons, lookup_node_cons, lookup_node_cons]
    rcases t with _ | _ | _ | _ | t
    · exact lookup_zipT op n a a' l hx.1 hy.1 hl'
    · exact lookup_zipT op n b b' l hx.2.1 hy.2.1 hl'
    · exact lookup_zipT op n c c' l hx.2.2.1 hy.2.2.1 hl'
    · exact lookup_zipT op n d d' l hx.2.2.2.1 hy.2.2.2.1 hl'
    · exact lookup_zipT op n e e' l hx.2.2.2.2 hy.2.2.2.2 hl'
theorem lookup_mapT (op : ℕ → ℕ) : ∀ n x l, Full n x → l.length = n → lookup (mapT op x) l = op (lookup x l)
  | 0, .leaf _, [], _, _ => rfl
  | n + 1, .node a b c d e, t :: l, hx, hl => by
    have hl' : l.length = n := by simpa using hl
    rw [mapT_node, lookup_node_cons, lookup_node_cons]
    rcases t with _ | _ | _ | _ | t
    · exact lookup_mapT op n a l hx.1 hl'
    · exact lookup_mapT op n b l hx.2.1 hl'
    · exact lookup_mapT op n c l hx.2.2.1 hl'
    · exact lookup_mapT op n d l hx.2.2.2.1 hl'
    · exact lookup_mapT op n e l hx.2.2.2.2 hl'
def ltB : List ℕ → List ℕ → Bool
  | [], [] => true
  | a :: p, b :: l => decide (a < b) && ltB p l
  | _, _ => false
def mtB : List ℕ → List ℕ → Bool
  | [], [] => true
  | a :: p, b :: l => (b == 4 || a == b) && mtB p l
  | _, _ => false
@[simp] theorem ltB_cons (a b : ℕ) (p l : List ℕ) : ltB (a :: p) (b :: l) = (decide (a < b) && ltB p l) := rfl
@[simp] theorem mtB_cons (a b : ℕ) (p l : List ℕ) : mtB (a :: p) (b :: l) = ((b == 4 || a == b) && mtB p l) := rfl
@[simp] theorem ltB_nil_cons (b : ℕ) (l : List ℕ) : ltB [] (b :: l) = false := rfl
@[simp] theorem mtB_nil_cons (b : ℕ) (l : List ℕ) : mtB [] (b :: l) = false := rfl
theorem mem_sel {t : ℕ} {P : List (List ℕ)} {r : List ℕ} : r ∈ sel t P ↔ t :: r ∈ P := by
  unfold sel
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨p, hp, h⟩
    rcases p with _ | ⟨hd, tl⟩
    · simp at h
    · by_cases hh : hd = t
      · subst hh
        simp only [if_true, Option.some.injEq] at h
        rw [← h]; exact hp
      · simp [hh] at h
  · intro h
    exact ⟨t :: r, h, by simp⟩
theorem sel_cons_cons (t h : ℕ) (r : List ℕ) (P : List (List ℕ)) :
    sel t ((h :: r) :: P) = if h = t then r :: sel t P else sel t P := by
  unfold sel; by_cases hh : h = t <;> simp [hh]
theorem sel_cons_nil (t : ℕ) (P : List (List ℕ)) : sel t ([] :: P) = sel t P := by
  unfold sel; simp
theorem countP_sel_succ (s : ℕ) (m : List ℕ) : ∀ P : List (List ℕ),
    P.countP (fun p => ltB p ((s + 1) :: m)) = P.countP (fun p => ltB p (s :: m)) + (sel s P).countP (ltB · m)
  | [] => rfl
  | [] :: P => by
    have h := countP_sel_succ s m P
    rw [sel_cons_nil, List.countP_cons, List.countP_cons]
    simpa using h
  | (h :: r) :: P => by
    have ih := countP_sel_succ s m P
    rw [sel_cons_cons, List.countP_cons, List.countP_cons, ih]
    by_cases hh : h = s
    · subst hh
      rw [if_pos rfl, List.countP_cons]
      cases hb : ltB r m <;> simp [hb]
      omega
    · rw [if_neg hh]
      have hlt : (h < s + 1) ↔ (h < s) := by omega
      by_cases hs : h < s <;> cases hb : ltB r m <;> simp [hb, hs, hlt]
      all_goals omega
theorem countP_sel_zero (m : List ℕ) (P : List (List ℕ)) : P.countP (fun p => ltB p (0 :: m)) = 0 := by
  rw [List.countP_eq_zero]
  intro p _
  rcases p with _ | ⟨h, r⟩ <;> simp
theorem sel_length {n t : ℕ} {P : List (List ℕ)} (hP : ∀ p ∈ P, p.length = n + 1) :
    ∀ p ∈ sel t P, p.length = n := by
  intro p hp
  have := hP _ (mem_sel.mp hp)
  simpa using this
theorem lookup_mapT_zero : ∀ n x l, Full n x → l.length = n → lookup (mapT (fun _ => 0) x) l = 0 :=
  fun n x l hx hl => lookup_mapT _ n x l hx hl
theorem lookup_cnt : ∀ n (P : List (List ℕ)), (∀ p ∈ P, p.length = n) →
    ∀ l : List ℕ, l.length = n → (∀ v ∈ l, v ≤ 4) → lookup (pT (indT n P)) l = P.countP (fun p => ltB p l)
  | 0, P, hP, [], _, _ => by
    show P.length = _
    rw [eq_comm, List.countP_eq_length]
    intro p hp
    rw [List.length_eq_zero_iff.mp (hP p hp)]
    rfl
  | n + 1, P, hP, s :: m, hl, hv => by
    have hm : m.length = n := by simpa using hl
    have hs : s ≤ 4 := hv s (by simp)
    have IH : ∀ t, lookup (pT (indT n (sel t P))) m = (sel t P).countP (ltB · m) := fun t =>
      lookup_cnt n (sel t P) (sel_length hP) m hm (fun v hv' => hv v (by simp [hv']))
    have F : ∀ t, Full n (pT (indT n (sel t P))) := fun t => full_pT n _ (full_indT n _)
    have h1 := countP_sel_succ 0 m P
    have h2 := countP_sel_succ 1 m P
    have h3 := countP_sel_succ 2 m P
    have h4 := countP_sel_succ 3 m P
    have h0 := countP_sel_zero m P
    show lookup (pT (.node _ _ _ _ _)) (s :: m) = _
    rw [pT_node, lookup_node_cons]
    interval_cases s
    · exact (lookup_mapT_zero n _ m (F 0) hm).trans h0.symm
    · show lookup (pT (indT n (sel 0 P))) m = _
      rw [IH, h1, h0, zero_add]
    · show lookup (zipT Nat.add _ _) m = _
      rw [lookup_zipT _ n _ _ m (F 0) (F 1) hm, IH, IH, h2, h1, h0]
      first | omega | simp [Nat.add_eq]
    · show lookup (zipT Nat.add (zipT Nat.add _ _) _) m = _
      rw [lookup_zipT _ n _ _ m (full_zipT _ n _ _ (F 0) (F 1)) (F 2) hm,
        lookup_zipT _ n _ _ m (F 0) (F 1) hm, IH, IH, IH, h3, h2, h1, h0]
      first | omega | simp [Nat.add_eq]
    · show lookup (zipT Nat.add (zipT Nat.add (zipT Nat.add _ _) _) _) m = _
      rw [lookup_zipT _ n _ _ m (full_zipT _ n _ _ (full_zipT _ n _ _ (F 0) (F 1)) (F 2)) (F 3) hm,
        lookup_zipT _ n _ _ m (full_zipT _ n _ _ (F 0) (F 1)) (F 2) hm,
        lookup_zipT _ n _ _ m (F 0) (F 1) hm, IH, IH, IH, IH, h4, h3, h2, h1, h0]
      first | omega | simp [Nat.add_eq]
section DT
variable {ι : Type*}
abbrev hd (p : List ℕ) : ℕ := p.headD 0
theorem filter_ltB_cons (X : Finset ι) (pt : ι → List ℕ) (n : ℕ) (hX : ∀ i ∈ X, (pt i).length = n + 1)
    (t : ℕ) (m : List ℕ) :
    #{i ∈ X | ltB (pt i) (t :: m)} = #{i ∈ X.filter (fun i => hd (pt i) < t) | ltB (pt i).tail m} := by
  rw [Finset.filter_filter]
  congr 1
  refine Finset.filter_congr fun i hi => ?_
  have hlen := hX i hi
  rcases h : pt i with _ | ⟨a, r⟩
  · rw [h] at hlen; simp at hlen
  · simp [hd]
theorem lookup_dT : ∀ (n : ℕ) (X : Finset ι) (pt : ι → List ℕ) (x : T5), Full n x →
    (∀ i ∈ X, (pt i).length = n ∧ ∀ v ∈ pt i, v ≤ 3) →
    (∀ l : List ℕ, l.length = n → (∀ v ∈ l, v ≤ 4) → lookup x l = #{i ∈ X | ltB (pt i) l}) →
    ∀ l : List ℕ, l.length = n → (∀ v ∈ l, v ≤ 4) → lookup (dT x) l = #{i ∈ X | mtB (pt i) l}
  | 0, X, pt, .leaf z, _, hX, hx, [], _, _ => by
    have h := hx [] rfl (by simp)
    show z = _
    rw [show z = lookup (.leaf z) [] from rfl, h]
    congr 1
    refine Finset.filter_congr fun i hi => ?_
    rw [List.length_eq_zero_iff.mp (hX i hi).1]
    rfl
  | n + 1, X, pt, .node a b c d e, hfull, hX, hx, s :: m, hl, hv => by
    have hm : m.length = n := by simpa using hl
    have hs : s ≤ 4 := hv s (by simp)
    have hmv : ∀ v ∈ m, v ≤ 4 := fun v hv' => hv v (by simp [hv'])
    have hchild : ∀ t, t ≤ 4 → lookup (dT (pick t a b c d e)) m =
        #{i ∈ X.filter (fun i => hd (pt i) < t) | mtB (pt i).tail m} := by
      intro t ht
      refine lookup_dT n (X.filter (fun i => hd (pt i) < t)) (fun i => (pt i).tail) _ (full_pick hfull t) ?_ ?_ m hm hmv
      · intro i hi
        have h := hX i (Finset.mem_filter.mp hi).1
        refine ⟨by simp [h.1], fun v hv' => h.2 v (List.mem_of_mem_tail hv')⟩
      · intro l hl' hlv
        rw [← lookup_node_cons a b c d e t l, hx (t :: l) (by simp [hl']) (by
          intro v hv'; rcases List.mem_cons.mp hv' with rfl | hv'; exact ht; exact hlv v hv')]
        exact filter_ltB_cons X pt n (fun i hi => (hX i hi).1) t l
    have F : ∀ t, Full n (dT (pick t a b c d e)) := fun t => full_dT n _ (full_pick hfull t)
    have hsplit : ∀ t, t ≤ 3 → #{i ∈ X.filter (fun i => hd (pt i) < t + 1) | mtB (pt i).tail m} =
        #{i ∈ X.filter (fun i => hd (pt i) < t) | mtB (pt i).tail m} +
          #{i ∈ X | mtB (pt i) (t :: m)} := by
      intro t ht3
      classical
      simp only [Finset.filter_filter]
      rw [← Finset.card_union_of_disjoint]
      · congr 1
        ext i
        simp only [Finset.mem_union, Finset.mem_filter]
        have hlen := (hX i)
        constructor
        · rintro ⟨hi, hlt, hmt⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | heq
          · exact Or.inl ⟨hi, hlt', hmt⟩
          · refine Or.inr ⟨hi, ?_⟩
            rcases h : pt i with _ | ⟨a', r⟩
            · rw [h] at hlen; simp at hlen; exact absurd (hlen hi) (by simp)
            · rw [h] at heq hmt; simp only [hd, List.headD_cons] at heq
              simp only [List.tail_cons] at hmt
              simp [heq, hmt]
        · rintro (⟨hi, hlt, hmt⟩ | ⟨hi, hmt⟩)
          · exact ⟨hi, by omega, hmt⟩
          · rcases h : pt i with _ | ⟨a', r⟩
            · rw [h] at hmt; simp at hmt
            · rw [h] at hmt
              simp only [mtB_cons, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hmt
              have ha3 : a' ≤ 3 := (hX i hi).2 a' (by simp [h])
              refine ⟨hi, ?_, ?_⟩
              · simp only [hd, List.headD_cons]
                rcases hmt.1 with h4 | h4 <;> omega
              · simpa using hmt.2
      · rw [Finset.disjoint_filter]
        intro i hi ⟨hlt, _⟩ hmt
        rcases h : pt i with _ | ⟨a', r⟩
        · rw [h] at hmt; simp at hmt
        · rw [h] at hmt hlt
          simp only [mtB_cons, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hmt
          simp only [hd, List.headD_cons] at hlt
          have ha3 : a' ≤ 3 := (hX i hi).2 a' (by simp [h])
          rcases hmt.1 with h4 | h4 <;> omega
    have hfour : #{i ∈ X.filter (fun i => hd (pt i) < 4) | mtB (pt i).tail m} = #{i ∈ X | mtB (pt i) (4 :: m)} := by
      rw [Finset.filter_filter]
      congr 1
      refine Finset.filter_congr fun i hi => ?_
      rcases h : pt i with _ | ⟨a', r⟩
      · have := (hX i hi).1; rw [h] at this; simp at this
      · have ha3 : a' ≤ 3 := (hX i hi).2 a' (by simp [h])
        have h4 : a' < 4 := by omega
        simp [hd, h4]
    have hc : ∀ t, t ≤ 3 → lookup (dT (pick (t + 1) a b c d e)) m - lookup (dT (pick t a b c d e)) m =
        #{i ∈ X | mtB (pt i) (t :: m)} := by
      intro t ht
      rw [hchild (t + 1) (by omega), hchild t (by omega), hsplit t ht]
      omega
    rw [dT_node, lookup_node_cons]
    interval_cases s
    · exact (lookup_zipT _ n _ _ m (F 1) (F 0) hm).trans (hc 0 (by norm_num))
    · exact (lookup_zipT _ n _ _ m (F 2) (F 1) hm).trans (hc 1 (by norm_num))
    · exact (lookup_zipT _ n _ _ m (F 3) (F 2) hm).trans (hc 2 (by norm_num))
    · exact (lookup_zipT _ n _ _ m (F 4) (F 3) hm).trans (hc 3 (by norm_num))
    · exact (hchild 4 le_rfl).trans hfour
end DT
def digitsOf {n : ℕ} (u : Fin n → Fin 5) : List ℕ := List.ofFn fun i => (u i : ℕ)
theorem digitsOf_length {n : ℕ} (u : Fin n → Fin 5) : (digitsOf u).length = n := List.length_ofFn
theorem digitsOf_le {n : ℕ} (u : Fin n → Fin 5) : ∀ v ∈ digitsOf u, v ≤ 4 := by
  intro v hv
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
  exact Nat.lt_succ_iff.mp (u i).isLt
theorem digitsOf_cons {n : ℕ} (t : Fin 5) (u : Fin n → Fin 5) :
    digitsOf (Fin.cons t u : Fin (n + 1) → Fin 5) = (t : ℕ) :: digitsOf u := by
  simp [digitsOf, List.ofFn_succ]
def parU {n : ℕ} (u : Fin n → Fin 5) : Bool := #{i | u i ≠ 4} % 2 == 1
theorem parU_cons {n : ℕ} (t : Fin 5) (u : Fin n → Fin 5) :
    parU (Fin.cons t u : Fin (n + 1) → Fin 5) = (decide (t ≠ 4) ^^ parU u) := by
  unfold parU
  rw [Fin.card_filter_univ_succ']
  simp only [Fin.cons_zero, Fin.cons_succ]
  by_cases ht : t = 4
  · simp [ht]
  · simp only [ht, ne_eq, not_false_eq_true, if_true, decide_true, Bool.true_xor]
    rcases Nat.mod_two_eq_zero_or_one (#{i | u i ≠ 4}) with h | h <;> simp [h, Nat.add_mod]
def FrOk {n : ℕ} (fr : List Bool) (u : Fin n → Fin 5) : Prop := ∀ i : Fin n, fr.getD i false = true → u i = 4
instance {n : ℕ} (fr : List Bool) : DecidablePred (FrOk (n := n) fr) := fun _ => Fintype.decidableForallFintype
theorem frOk_cons {n : ℕ} (f : Bool) (fs : List Bool) (t : Fin 5) (u : Fin n → Fin 5) :
    FrOk (f :: fs) (Fin.cons t u : Fin (n + 1) → Fin 5) ↔ (f = true → t = 4) ∧ FrOk fs u := by
  unfold FrOk
  rw [Fin.forall_fin_succ]
  simp
theorem spair_eq (b : Bool) (h : ℕ) : spair b h = Kernel.signedPair b h := by
  cases b <;> rfl
theorem padd_eq (x y : ℕ × ℕ) : padd x y = x + y := by
  cases x; cases y; rfl
theorem histT_leaf_leaf (hb cv gv : ℕ) (fr : List Bool) (neg : Bool) :
    histT hb (.leaf cv) fr (.leaf gv) neg = cond (Nat.beq gv 0) (0, 0) (spair neg (Nat.mul gv (Nat.pow hb cv))) :=
  rfl
theorem histT_node_node (hb : ℕ) (c0 c1 c2 c3 c4 g0 g1 g2 g3 g4 : T5) (f : Bool) (fs : List Bool) (neg : Bool) :
    histT hb (.node c0 c1 c2 c3 c4) (f :: fs) (.node g0 g1 g2 g3 g4) neg =
      cond f (histT hb c4 fs g4 neg) (padd (histT hb c0 fs g0 (!neg)) (padd (histT hb c1 fs g1 (!neg))
        (padd (histT hb c2 fs g2 (!neg)) (padd (histT hb c3 fs g3 (!neg)) (histT hb c4 fs g4 neg))))) := rfl
theorem sum_fin_cons {M : Type*} [AddCommMonoid M] {n : ℕ} (F : (Fin (n + 1) → Fin 5) → M) :
    ∑ u, F u = ∑ t : Fin 5, ∑ u : Fin n → Fin 5, F (Fin.cons t u) := by
  rw [← (Fin.consEquiv fun _ => Fin 5).sum_comp, Fintype.sum_prod_type]
  rfl
theorem histT_eq (hb : ℕ) : ∀ (n : ℕ) (c g : T5) (fr : List Bool) (neg : Bool), Full n c → Full n g →
    fr.length = n →
    histT hb c fr g neg = ∑ u : Fin n → Fin 5,
      if FrOk fr u then Kernel.signedPair (neg ^^ parU u) (lookup g (digitsOf u) * hb ^ lookup c (digitsOf u))
      else 0
  | 0, .leaf cv, .leaf gv, [], neg, _, _, _ => by
    rw [histT_leaf_leaf, Fintype.sum_unique, if_pos (show FrOk _ _ from fun i => i.elim0)]
    have hpar : ∀ u : Fin 0 → Fin 5, parU u = false := fun u => by simp [parU]
    rw [hpar, Bool.xor_false]
    show _ = Kernel.signedPair neg (gv * hb ^ cv)
    by_cases hg : gv = 0
    · subst hg; cases neg <;> simp [Kernel.signedPair]
    · have : Nat.beq gv 0 = false := Bool.eq_false_iff.mpr fun h => hg (Nat.eq_of_beq_eq_true h)
      rw [this, cond_false, spair_eq]; rfl
  | n + 1, .node c0 c1 c2 c3 c4, .node g0 g1 g2 g3 g4, f :: fs, neg, hc, hg, hfr => by
    have hfs : fs.length = n := by simpa using hfr
    have IH : ∀ (t : Fin 5) (neg' : Bool), histT hb (pick t c0 c1 c2 c3 c4) fs (pick t g0 g1 g2 g3 g4) neg' =
        ∑ u : Fin n → Fin 5, if FrOk fs u then Kernel.signedPair (neg' ^^ parU u)
          (lookup (pick t g0 g1 g2 g3 g4) (digitsOf u) * hb ^ lookup (pick t c0 c1 c2 c3 c4) (digitsOf u)) else 0 :=
      fun t neg' => histT_eq hb n _ _ fs neg' (full_pick hc t) (full_pick hg t) hfs
    have e0 : histT hb c0 fs g0 (!neg) = _ := IH 0 (!neg)
    have e1 : histT hb c1 fs g1 (!neg) = _ := IH 1 (!neg)
    have e2 : histT hb c2 fs g2 (!neg) = _ := IH 2 (!neg)
    have e3 : histT hb c3 fs g3 (!neg) = _ := IH 3 (!neg)
    have e4 : histT hb c4 fs g4 neg = _ := IH 4 neg
    rw [sum_fin_cons, Fin.sum_univ_five]
    simp only [frOk_cons, parU_cons, digitsOf_cons, lookup_node_cons]
    rw [histT_node_node, e0, e1, e2, e3, e4]
    have d0 : decide ((0 : Fin 5) ≠ 4) = true := rfl
    have d1 : decide ((1 : Fin 5) ≠ 4) = true := rfl
    have d2 : decide ((2 : Fin 5) ≠ 4) = true := rfl
    have d3 : decide ((3 : Fin 5) ≠ 4) = true := rfl
    have d4 : decide ((4 : Fin 5) ≠ 4) = false := rfl
    have q0 : ((0 : Fin 5) = 4) = False := eq_false (by decide)
    have q1 : ((1 : Fin 5) = 4) = False := eq_false (by decide)
    have q2 : ((2 : Fin 5) = 4) = False := eq_false (by decide)
    have q3 : ((3 : Fin 5) = 4) = False := eq_false (by decide)
    cases f
    · simp only [cond_false, padd_eq, Bool.false_eq_true, false_implies, true_and, d0, d1, d2, d3, d4,
        Bool.true_xor, Bool.false_xor, Bool.xor_not, Bool.not_xor, add_assoc]
    · simp only [cond_true, q0, q1, q2, q3, imp_false, not_true_eq_false, false_and, if_false,
        Finset.sum_const_zero, zero_add, d4, Bool.false_xor, implies_true, true_and]
end ClaudeWCT.Numerics.N600
end

section

namespace ClaudeWCT.Numerics.N600
theorem w1_group0 : (w1Check && w1MassCheck && wfCheck 0 && wfMassCheck 0) = true := by decide +kernel
theorem w1_group1 : (wfCheck 1 && wfMassCheck 1 && wfCheck 2 && wfMassCheck 2) = true := by decide +kernel
theorem w1_group2 : (wfCheck 3 && wfMassCheck 3 && wfCheck 4 && wfMassCheck 4) = true := by decide +kernel
theorem w1_group3 : (wfCheck 5 && wfMassCheck 5 && wfCheck 6 && wfMassCheck 6) = true := by decide +kernel
end ClaudeWCT.Numerics.N600
end

section

namespace ClaudeWCT.Numerics.N600
theorem w2_all : (w2Check && w2MassCheck) = true := by decide +kernel
end ClaudeWCT.Numerics.N600
end

section





namespace ClaudeWCT.Numerics.N600
open Finset
section IE
variable {β : Type*} [Fintype β] (val : β → Fin 7 → ℕ)
def CovMask {p : ℕ} (free : Fin 7 → Bool) (v : Fin 7 → ℕ) (E : Fin p → β) : Prop :=
  ∀ j, free j = false → ∃ e, v j ≤ val (E e) j
instance {p : ℕ} (free : Fin 7 → Bool) (v : Fin 7 → ℕ) : DecidablePred (CovMask val (p := p) free v) :=
  fun _ => Fintype.decidableForallFintype
def cntU (u : Fin 7 → Fin 5) : ℕ := #{x : β | ∀ j, val x j < u j}
def sgnU (u : Fin 7 → Fin 5) : ℤ := (-1) ^ #{j | u j ≠ 4}
def Compat (free : Fin 7 → Bool) (v : Fin 7 → ℕ) (u : Fin 7 → Fin 5) : Prop :=
  ∀ j, u j = 4 ∨ (free j = false ∧ (u j : ℕ) = v j)
instance (free : Fin 7 → Bool) (v : Fin 7 → ℕ) : DecidablePred (Compat free v) :=
  fun _ => Fintype.decidableForallFintype
theorem sum_fin5_single (v : ℕ) (hv : v ≤ 3) (b : Prop) [Decidable b] (X : ℕ → ℤ) :
    ∑ t : Fin 5, (if t = 4 then 1 else if b ∧ (t : ℕ) = v then X t else 0) = 1 + if b then X v else 0 := by
  rw [Fin.sum_univ_five]
  by_cases hb : b <;> interval_cases v <;> simp [hb] <;> ring
omit [Fintype β] in
theorem indicator_covMask {p : ℕ} (free : Fin 7 → Bool) (v : Fin 7 → ℕ) (hv : ∀ j, v j ≤ 3)
    (h3 : ∀ x j, val x j ≤ 3) (E : Fin p → β) :
    (if CovMask val free v E then (1 : ℤ) else 0) =
      ∑ u : Fin 7 → Fin 5, if Compat free v u then
        sgnU u * ∏ e, (if ∀ j, val (E e) j < u j then (1 : ℤ) else 0) else 0 := by
  set A : Fin 7 → ℕ → ℤ := fun j t => ∏ e, (if val (E e) j < t then (1 : ℤ) else 0) with hA
  have h1 : (if CovMask val free v E then (1 : ℤ) else 0) =
      ∏ j, (if free j = false then 1 - A j (v j) else 1) := by
    by_cases hc : CovMask val free v E
    · rw [if_pos hc]
      symm
      refine prod_eq_one fun j _ => ?_
      split_ifs with hf
      · obtain ⟨e, he⟩ := hc j hf
        simp only [hA]
        rw [prod_eq_zero (mem_univ e) (if_neg (Nat.not_lt.mpr he)), sub_zero]
      · rfl
    · rw [if_neg hc]
      have : ∃ j, free j = false ∧ ∀ e, val (E e) j < v j := by
        by_contra hn
        push Not at hn
        exact hc fun j hj => by
          obtain ⟨e, he⟩ := hn j hj
          exact ⟨e, he⟩
      obtain ⟨j, hj, hlt⟩ := this
      symm
      refine prod_eq_zero (mem_univ j) ?_
      rw [if_pos hj, hA]
      simp only
      rw [prod_eq_one (fun e _ => by rw [if_pos (hlt e)]), sub_self]
  have h2 : ∀ j, (if free j = false then 1 - A j (v j) else 1) =
      ∑ t : Fin 5, (if t = 4 then 1 else if free j = false ∧ (t : ℕ) = v j then -A j t else 0) := by
    intro j
    rw [sum_fin5_single (v j) (hv j) (free j = false) (fun t => -A j t)]
    split_ifs <;> ring
  rw [h1]
  simp_rw [h2]
  rw [Fintype.prod_sum]
  refine sum_congr rfl fun u _ => ?_
  by_cases hc : Compat free v u
  · rw [if_pos hc]
    have h4 : ∀ j, (if u j = 4 then (1 : ℤ) else if free j = false ∧ (u j : ℕ) = v j then -A j (u j) else 0) =
        (if u j ≠ 4 then (-1 : ℤ) else 1) * A j (u j) := by
      intro j
      by_cases hu : u j = 4
      · rw [if_pos hu, if_neg (not_not.mpr hu), one_mul, hA]
        symm
        refine prod_eq_one fun e _ => ?_
        rw [if_pos]
        rw [hu]
        have := h3 (E e) j
        show val (E e) j < 4
        omega
      · rw [if_neg hu, if_pos ((hc j).resolve_left hu), if_pos hu]
        ring
    rw [prod_congr rfl fun j _ => h4 j, prod_mul_distrib]
    congr 1
    · rw [sgnU, prod_ite, prod_const_one, mul_one, prod_const]
    · rw [hA]
      simp only
      rw [prod_comm]
      refine prod_congr rfl fun e _ => ?_
      by_cases hall : ∀ j, val (E e) j < u j
      · rw [if_pos hall]
        exact prod_eq_one fun j _ => by rw [if_pos (hall j)]
      · rw [if_neg hall]
        push Not at hall
        obtain ⟨j, hj⟩ := hall
        exact prod_eq_zero (mem_univ j) (by rw [if_neg (by omega)])
  · rw [if_neg hc]
    have : ∃ j, u j ≠ 4 ∧ ¬(free j = false ∧ (u j : ℕ) = v j) := by
      by_contra hn
      push Not at hn
      exact hc fun j => by
        by_cases hu : u j = 4
        · exact Or.inl hu
        · exact Or.inr (hn j hu)
    obtain ⟨j, hu, hn⟩ := this
    exact prod_eq_zero (mem_univ j) (by rw [if_neg hu, if_neg hn])
theorem card_covMask (p : ℕ) (free : Fin 7 → Bool) (v : Fin 7 → ℕ) (hv : ∀ j, v j ≤ 3)
    (h3 : ∀ x j, val x j ≤ 3) :
    (#{E : Fin p → β | CovMask val free v E} : ℤ) =
      ∑ u : Fin 7 → Fin 5, if Compat free v u then sgnU u * (cntU val u : ℤ) ^ p else 0 := by
  rw [natCast_card_filter]
  simp_rw [indicator_covMask val free v hv h3]
  rw [sum_comm]
  refine sum_congr rfl fun u _ => ?_
  split_ifs
  · rw [← mul_sum, cntU, natCast_card_filter, Fintype.sum_pow]
  · exact sum_const_zero
def M1 (u : Fin 7 → Fin 5) : ℕ := #{a : β | ∀ j, u j ≠ 4 → val a j = u j}
def M2 (u : Fin 7 → Fin 5) : ℕ := #{ab : β × β | ∀ j, u j ≠ 4 → max (val ab.1 j) (val ab.2 j) = u j}
def FreeOk (free : Fin 7 → Bool) (u : Fin 7 → Fin 5) : Prop := ∀ j, free j = true → u j = 4
instance (free : Fin 7 → Bool) : DecidablePred (FreeOk free) := fun _ => Fintype.decidableForallFintype
theorem compat_iff (free : Fin 7 → Bool) (v : Fin 7 → ℕ) (u : Fin 7 → Fin 5) :
    Compat free v u ↔ FreeOk free u ∧ ∀ j, u j ≠ 4 → v j = u j := by
  constructor
  · intro h
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · rcases h j with h' | ⟨h', _⟩
      · exact h'
      · rw [hj] at h'; exact absurd h' (by simp)
    · exact ((h j).resolve_left hj).2.symm
  · rintro ⟨hf, hv⟩ j
    by_cases hu : u j = 4
    · exact Or.inl hu
    · refine Or.inr ⟨?_, (hv j hu).symm⟩
      by_contra hfj
      exact hu (hf j (by simpa using hfj))
theorem sum_card_covMask (p : ℕ) (free : Fin 7 → Bool) (h3 : ∀ x j, val x j ≤ 3) :
    ∑ a : β, (#{E : Fin p → β | CovMask val free (val a) E} : ℤ) =
      ∑ u : Fin 7 → Fin 5, if FreeOk free u then sgnU u * (M1 val u : ℤ) * (cntU val u : ℤ) ^ p else 0 := by
  simp_rw [card_covMask val p free _ (fun j => h3 _ j) h3]
  rw [sum_comm]
  refine sum_congr rfl fun u _ => ?_
  simp_rw [compat_iff]
  by_cases hf : FreeOk free u
  · simp only [hf, true_and, if_true]
    rw [← sum_filter, sum_const, nsmul_eq_mul, M1]
    ring
  · simp [hf]
theorem sum_card_covMask_pair (p : ℕ) (h3 : ∀ x j, val x j ≤ 3) :
    ∑ ab : β × β, (#{E : Fin p → β | CovMask val (fun _ => false) (fun j => max (val ab.1 j) (val ab.2 j)) E} : ℤ) =
      ∑ u : Fin 7 → Fin 5, sgnU u * (M2 val u : ℤ) * (cntU val u : ℤ) ^ p := by
  simp_rw [card_covMask val p (fun _ => false) _ (fun j => max_le (h3 _ j) (h3 _ j)) h3]
  rw [sum_comm]
  refine sum_congr rfl fun u _ => ?_
  have hfree : FreeOk (fun _ => false) u := fun j hj => absurd hj (by simp)
  simp_rw [compat_iff, hfree, true_and]
  rw [← sum_filter, sum_const, nsmul_eq_mul, M2]
  ring
omit [Fintype β] in
theorem coversT_max' {p : ℕ} (v₁ v₂ : Fin 7 → ℕ) (E : Fin p → β) :
    CoversT val (fun i => max (v₁ i) (v₂ i)) E ↔ CoversT val v₁ E ∧ CoversT val v₂ E := by
  unfold CoversT
  constructor
  · intro h
    exact ⟨fun i => (h i).imp fun m hm => le_trans (le_max_left _ _) hm,
      fun i => (h i).imp fun m hm => le_trans (le_max_right _ _) hm⟩
  · rintro ⟨h₁, h₂⟩ i
    rcases le_total (v₁ i) (v₂ i) with hle | hle
    · obtain ⟨m, hm⟩ := h₂ i
      exact ⟨m, max_le (hle.trans hm) hm⟩
    · obtain ⟨m, hm⟩ := h₁ i
      exact ⟨m, max_le hm (hle.trans hm)⟩
omit [Fintype β] in
theorem covMask_false_iff {p : ℕ} (v : Fin 7 → ℕ) (E : Fin p → β) :
    CovMask val (fun _ => false) v E ↔ CoversT val v E := by
  unfold CovMask CoversT
  simp
omit [Fintype β] in
theorem covMask_free_iff {p : ℕ} (i : Fin 7) (v : Fin 7 → ℕ) (E : Fin p → β) :
    CovMask val (fun j => decide (j = i)) v E ↔ CoversExcept val i v E := by
  unfold CovMask CoversExcept
  simp
end IE
section Bridge
variable {β : Type*} [Fintype β] (val : β → Fin 7 → ℕ)
def WordsOf : Prop := (Finset.univ.val.map fun x => List.ofFn (val x)) = (words : Multiset (List ℕ))
theorem countP_words {val : β → Fin 7 → ℕ} (hW : WordsOf val) (q : List ℕ → Bool) :
    words.countP q = #{x : β | q (List.ofFn (val x)) = true} := by
  have h : words.countP q = Multiset.countP (fun l => q l = true) (words : Multiset (List ℕ)) := by
    rw [Multiset.coe_countP]; simp
  rw [h, ← hW, Multiset.countP_map]
  rfl
theorem digitsOf_succ {n : ℕ} (u : Fin (n + 1) → Fin 5) : digitsOf u = (u 0 : ℕ) :: digitsOf (Fin.tail u) := by
  simp [digitsOf, List.ofFn_succ, Fin.tail]
theorem ltB_ofFn_iff : ∀ {n : ℕ} (f : Fin n → ℕ) (u : Fin n → Fin 5),
    ltB (List.ofFn f) (digitsOf u) = true ↔ ∀ j, f j < u j
  | 0, _, _ => by simp [digitsOf, ltB]
  | n + 1, f, u => by
    rw [List.ofFn_succ, digitsOf_succ u, ltB_cons, Bool.and_eq_true, decide_eq_true_iff,
      ltB_ofFn_iff (fun j => f j.succ) (Fin.tail u), Fin.forall_fin_succ]
    rfl
theorem mtB_ofFn_iff : ∀ {n : ℕ} (f : Fin n → ℕ) (u : Fin n → Fin 5),
    mtB (List.ofFn f) (digitsOf u) = true ↔ ∀ j, u j ≠ 4 → f j = u j
  | 0, _, _ => by simp [digitsOf, mtB]
  | n + 1, f, u => by
    rw [List.ofFn_succ, digitsOf_succ u, mtB_cons, Bool.and_eq_true,
      mtB_ofFn_iff (fun j => f j.succ) (Fin.tail u), Fin.forall_fin_succ]
    have h4 : ((u 0 : ℕ) = 4) ↔ u 0 = 4 := by rw [Fin.ext_iff]; rfl
    simp only [Bool.or_eq_true, beq_iff_eq, h4, Fin.tail]
    constructor
    · rintro ⟨h0 | h0, h⟩
      · exact ⟨fun h' => absurd h0 h', h⟩
      · exact ⟨fun _ => h0, h⟩
    · rintro ⟨h0, h⟩
      refine ⟨?_, h⟩
      by_cases hu : u 0 = 4
      · exact Or.inl hu
      · exact Or.inr (h0 hu)
theorem words_length : ∀ p ∈ words, p.length = 7 := by decide +kernel
theorem cntT_eq {val : β → Fin 7 → ℕ} (hW : WordsOf val) (u : Fin 7 → Fin 5) :
    lookup cntT (digitsOf u) = cntU val u := by
  rw [cntT, lookup_cnt 7 words words_length _ (digitsOf_length u) (digitsOf_le u), countP_words hW, cntU]
  congr 1
  refine Finset.filter_congr fun x _ => ?_
  exact ltB_ofFn_iff _ u
theorem lookup_cntT {val : β → Fin 7 → ℕ} (hW : WordsOf val) (l : List ℕ) (hl : l.length = 7)
    (hv : ∀ v ∈ l, v ≤ 4) : lookup cntT l = #{x : β | ltB (List.ofFn (val x)) l} := by
  rw [cntT, lookup_cnt 7 words words_length l hl hv, countP_words hW]
theorem full_cntT : Full 7 cntT := full_pT 7 _ (full_indT 7 _)
theorem g1T_eq {val : β → Fin 7 → ℕ} (hW : WordsOf val) (h3 : ∀ x j, val x j ≤ 3) (u : Fin 7 → Fin 5) :
    lookup g1T (digitsOf u) = M1 val u := by
  rw [g1T, lookup_dT 7 univ (fun x => List.ofFn (val x)) cntT full_cntT
    (fun x _ => ⟨List.length_ofFn, fun v hv => by obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv; exact h3 x j⟩)
    (fun l hl hv => lookup_cntT hW l hl hv) _ (digitsOf_length u) (digitsOf_le u), M1]
  congr 1
  refine Finset.filter_congr fun x _ => ?_
  exact mtB_ofFn_iff _ u
theorem ltB_max (p q l : List ℕ) (hp : p.length = l.length) (hq : q.length = l.length) :
    ltB (List.zipWith max p q) l = (ltB p l && ltB q l) := by
  induction l generalizing p q with
  | nil =>
    rw [List.length_eq_zero_iff.mp (show p.length = 0 by simpa using hp),
      List.length_eq_zero_iff.mp (show q.length = 0 by simpa using hq)]
    rfl
  | cons b l ih =>
    rcases p with _ | ⟨a, p⟩
    · simp at hp
    rcases q with _ | ⟨c, q⟩
    · simp at hq
    simp only [List.zipWith_cons_cons, ltB_cons]
    rw [ih p q (by simpa using hp) (by simpa using hq)]
    rw [show decide (max a c < b) = (decide (a < b) && decide (c < b)) by simp]
    cases decide (a < b) <;> cases decide (c < b) <;> cases ltB p l <;> cases ltB q l <;> rfl
theorem ofFn_max (f g : Fin 7 → ℕ) :
    List.ofFn (fun j => max (f j) (g j)) = List.zipWith max (List.ofFn f) (List.ofFn g) := by
  apply List.ext_getElem <;> simp
theorem g2T_eq {val : β → Fin 7 → ℕ} (hW : WordsOf val) (h3 : ∀ x j, val x j ≤ 3) (u : Fin 7 → Fin 5) :
    lookup g2T (digitsOf u) = M2 val u := by
  have hsq : ∀ l : List ℕ, l.length = 7 → (∀ v ∈ l, v ≤ 4) →
      lookup (mapT (fun z => Nat.mul z z) cntT) l =
        #{ab ∈ (univ : Finset (β × β)) | ltB (List.ofFn fun j => max (val ab.1 j) (val ab.2 j)) l} := by
    intro l hl hv
    rw [lookup_mapT _ 7 cntT l full_cntT hl, lookup_cntT hW l hl hv, Nat.mul_eq, ← card_product,
      ← Finset.filter_product, Finset.univ_product_univ]
    congr 1
    refine Finset.filter_congr fun ab _ => ?_
    rw [ofFn_max, ltB_max _ _ _ (by simp [hl]) (by simp [hl])]
    simp
  rw [g2T, lookup_dT 7 univ (fun ab : β × β => List.ofFn fun j => max (val ab.1 j) (val ab.2 j)) _
    (full_mapT _ 7 cntT full_cntT)
    (fun ab _ => ⟨List.length_ofFn, fun v hv => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv; exact max_le (h3 _ j) (h3 _ j)⟩)
    hsq _ (digitsOf_length u) (digitsOf_le u), M2]
  congr 1
  refine Finset.filter_congr fun ab _ => ?_
  exact mtB_ofFn_iff _ u
end Bridge
section Decode
variable {β : Type*} [Fintype β] {val : β → Fin 7 → ℕ}
theorem frOk_iff_freeOk (fr : List Bool) (free : Fin 7 → Bool) (hfr : ∀ j : Fin 7, fr.getD j false = free j)
    (u : Fin 7 → Fin 5) : FrOk fr u ↔ FreeOk free u := by
  unfold FrOk FreeOk
  simp only [hfr]
theorem sgnU_eq (u : Fin 7 → Fin 5) : sgnU u = if parU u then -1 else 1 := by
  rw [sgnU, parU, ClaudeWCT.Numerics.WCT9.neg_one_pow_eq]
theorem decode_hist (fr : List Bool) (hfr : fr.length = 7) (g : T5) (hg : Full 7 g) (d : List (ℕ × ℤ))
    (hEq : Kernel.histEq (histT Kernel.HB cntT fr g false) d = true)
    (hMass : Kernel.massOk (histT 1 cntT fr g false) d = true) (p : ℕ) :
    ∑ u : Fin 7 → Fin 5, (if FrOk fr u then (if parU u then (-1 : ℤ) else 1) * (lookup g (digitsOf u) : ℤ) *
        ((lookup cntT (digitsOf u) : ℕ) : ℤ) ^ p else 0) =
      (d.map fun e => e.2 * (e.1 : ℤ) ^ p).sum := by
  rw [histT_eq _ 7 cntT g fr false full_cntT hg hfr] at hEq hMass
  simp only [Bool.false_xor] at hEq hMass
  exact Kernel.decode univ (FrOk fr) parU (fun u => lookup g (digitsOf u)) (fun u => lookup cntT (digitsOf u)) d
    hEq hMass p
end Decode
section Tables
variable {β : Type*} [Fintype β] {val : β → Fin 7 → ℕ}
theorem checks_w1 : w1Check = true ∧ w1MassCheck = true := by
  have h := w1_group0
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2⟩
theorem checks_wf : ∀ t : Fin 7, wfCheck t = true ∧ wfMassCheck t = true := by
  have h0 := w1_group0
  have h1 := w1_group1
  have h2 := w1_group2
  have h3 := w1_group3
  simp only [Bool.and_eq_true] at h0 h1 h2 h3
  intro t
  fin_cases t
  · exact ⟨h0.1.2, h0.2⟩
  · exact ⟨h1.1.1.1, h1.1.1.2⟩
  · exact ⟨h1.1.2, h1.2⟩
  · exact ⟨h2.1.1.1, h2.1.1.2⟩
  · exact ⟨h2.1.2, h2.2⟩
  · exact ⟨h3.1.1.1, h3.1.1.2⟩
  · exact ⟨h3.1.2, h3.2⟩
theorem checks_w2 : w2Check = true ∧ w2MassCheck = true := by
  have h := w2_all
  simp only [Bool.and_eq_true] at h
  exact h
theorem full_g1T : Full 7 g1T := full_dT 7 _ full_cntT
theorem full_g2T : Full 7 g2T := full_dT 7 _ (full_mapT _ 7 _ full_cntT)
theorem w1_table (hW : WordsOf val) (h3 : ∀ x j, val x j ≤ 3) (p : ℕ) :
    (#{x : β × (Fin p → β) | CoversT val (val x.1) x.2} : ℤ) = (w1Data.map fun e => e.2 * (e.1 : ℤ) ^ p).sum := by
  have hcard : (#{x : β × (Fin p → β) | CoversT val (val x.1) x.2} : ℤ) =
      ∑ a : β, (#{E : Fin p → β | CovMask val (fun _ => false) (val a) E} : ℤ) := by
    rw [natCast_card_filter, Fintype.sum_prod_type]
    refine sum_congr rfl fun a _ => ?_
    rw [natCast_card_filter]
    simp only [covMask_false_iff]
  rw [hcard, sum_card_covMask val p _ h3,
    ← decode_hist noFree rfl g1T full_g1T w1Data checks_w1.1 checks_w1.2 p]
  refine sum_congr rfl fun u _ => ?_
  refine if_congr (frOk_iff_freeOk noFree (fun _ => false) (fun j => by fin_cases j <;> rfl) u).symm ?_ rfl
  rw [g1T_eq hW h3, cntT_eq hW, sgnU_eq]
theorem wf_table (hW : WordsOf val) (h3 : ∀ x j, val x j ≤ 3) (i : Fin 7) (p : ℕ) :
    (#{x : β × (Fin p → β) | CoversExcept val i (val x.1) x.2} : ℤ) =
      ((wfData i).map fun e => e.2 * (e.1 : ℤ) ^ p).sum := by
  have hcard : (#{x : β × (Fin p → β) | CoversExcept val i (val x.1) x.2} : ℤ) =
      ∑ a : β, (#{E : Fin p → β | CovMask val (fun j => decide (j = i)) (val a) E} : ℤ) := by
    rw [natCast_card_filter, Fintype.sum_prod_type]
    refine sum_congr rfl fun a _ => ?_
    rw [natCast_card_filter]
    simp only [covMask_free_iff]
  rw [hcard, sum_card_covMask val p _ h3,
    ← decode_hist (freeList i) rfl g1T full_g1T (wfData i) (checks_wf i).1 (checks_wf i).2 p]
  refine sum_congr rfl fun u _ => ?_
  refine if_congr (frOk_iff_freeOk (freeList i) (fun j => decide (j = i)) (fun j => by
      fin_cases i <;> fin_cases j <;> rfl) u).symm ?_ rfl
  rw [g1T_eq hW h3, cntT_eq hW, sgnU_eq]
theorem w2_table (hW : WordsOf val) (h3 : ∀ x j, val x j ≤ 3) (p : ℕ) :
    (#{x : β × β × (Fin p → β) | CoversT val (val x.1) x.2.2 ∧ CoversT val (val x.2.1) x.2.2} : ℤ) =
      (w2Data.map fun e => e.2 * (e.1 : ℤ) ^ p).sum := by
  have hcard : (#{x : β × β × (Fin p → β) | CoversT val (val x.1) x.2.2 ∧ CoversT val (val x.2.1) x.2.2} : ℤ) =
      ∑ ab : β × β, (#{E : Fin p → β |
        CovMask val (fun _ => false) (fun j => max (val ab.1 j) (val ab.2 j)) E} : ℤ) := by
    rw [natCast_card_filter, ← (Equiv.prodAssoc β β (Fin p → β)).sum_comp, Fintype.sum_prod_type]
    refine sum_congr rfl fun ab _ => ?_
    rw [natCast_card_filter]
    refine sum_congr rfl fun E _ => ?_
    simp only [Equiv.prodAssoc_apply, covMask_false_iff, coversT_max']
  rw [hcard, sum_card_covMask_pair val p h3,
    ← decode_hist noFree rfl g2T full_g2T w2Data checks_w2.1 checks_w2.2 p]
  refine sum_congr rfl fun u _ => ?_
  have hok : FrOk noFree u := (frOk_iff_freeOk noFree (fun _ => false) (fun j => by fin_cases j <;> rfl) u).mpr
    (fun j hj => absurd hj (by simp))
  rw [if_pos hok, g2T_eq hW h3, cntT_eq hW, sgnU_eq]
end Tables
end ClaudeWCT.Numerics.N600
end
