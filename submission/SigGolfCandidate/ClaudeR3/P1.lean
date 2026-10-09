import SigGolfCandidate.ClaudeR3.C1

namespace ClaudeR3.Tab
open Finset Polynomial
open ClaudeWCT.Numerics.N600
open ClaudeWCT.Numerics.Kernel (signedPair histOf histPoly histOf_eq dataPoly)

def wsum (P : List (List ℕ × ℕ)) (q : List ℕ → Bool) : ℕ := (P.map fun p => if q p.1 then p.2 else 0).sum

theorem selW_cons_cons (t h : ℕ) (r : List ℕ) (w : ℕ) (P : List (List ℕ × ℕ)) :
    selW t ((h :: r, w) :: P) = if h = t then (r, w) :: selW t P else selW t P := by
  unfold selW; by_cases hh : h = t <;> simp [hh]

theorem selW_cons_nil (t w : ℕ) (P : List (List ℕ × ℕ)) : selW t (([], w) :: P) = selW t P := by
  unfold selW; simp

theorem mem_selW {t : ℕ} {P : List (List ℕ × ℕ)} {p : List ℕ × ℕ} : p ∈ selW t P → (t :: p.1, p.2) ∈ P := by
  unfold selW
  rw [List.mem_filterMap]
  rintro ⟨⟨l, w⟩, hp, h⟩
  rcases l with _ | ⟨hd, tl⟩
  · simp at h
  · by_cases hh : hd = t
    · subst hh
      simp only [if_true, Option.some.injEq] at h
      rw [← h]; exact hp
    · simp [hh] at h

theorem selW_length {n t : ℕ} {P : List (List ℕ × ℕ)} (hP : ∀ p ∈ P, p.1.length = n + 1) :
    ∀ p ∈ selW t P, p.1.length = n := by
  intro p hp
  have := hP _ (mem_selW hp)
  simpa using this

theorem wsum_cons (p : List ℕ × ℕ) (P : List (List ℕ × ℕ)) (q : List ℕ → Bool) :
    wsum (p :: P) q = (if q p.1 then p.2 else 0) + wsum P q := by
  simp [wsum]

theorem wsum_selW_succ (s : ℕ) (m : List ℕ) : ∀ P : List (List ℕ × ℕ),
    wsum P (fun p => ltB p ((s + 1) :: m)) = wsum P (fun p => ltB p (s :: m)) + wsum (selW s P) (ltB · m)
  | [] => rfl
  | ([], w) :: P => by
    have h := wsum_selW_succ s m P
    rw [selW_cons_nil, wsum_cons, wsum_cons, h]
    simp
  | (h :: r, w) :: P => by
    have ih := wsum_selW_succ s m P
    rw [selW_cons_cons, wsum_cons, wsum_cons, ih]
    by_cases hh : h = s
    · subst hh
      rw [if_pos rfl, wsum_cons]
      cases hb : ltB r m <;> simp [hb] <;> omega
    · rw [if_neg hh]
      have hlt : (h < s + 1) ↔ (h < s) := by omega
      by_cases hs : h < s <;> cases hb : ltB r m <;> simp [hb, hs, hlt] <;> omega

theorem wsum_selW_zero (m : List ℕ) (P : List (List ℕ × ℕ)) : wsum P (fun p => ltB p (0 :: m)) = 0 := by
  induction P with
  | nil => rfl
  | cons p P ih =>
    rw [wsum_cons, ih]
    rcases p with ⟨_ | ⟨h, r⟩, w⟩ <;> simp

theorem full_indW : ∀ n P, Full n (indW n P)
  | 0, _ => trivial
  | n + 1, _ => ⟨full_indW n _, full_indW n _, full_indW n _, full_indW n _, full_indW n _, full_indW n _⟩

theorem foldr_w_eq (P : List (List ℕ × ℕ)) : P.foldr (fun p s => p.2 + s) 0 = (P.map (·.2)).sum := by
  induction P with
  | nil => rfl
  | cons p P ih => simp [ih]

theorem lookupW : ∀ n (P : List (List ℕ × ℕ)), (∀ p ∈ P, p.1.length = n) →
    ∀ l : List ℕ, l.length = n → (∀ v ∈ l, v ≤ 5) → lookup (pT (indW n P)) l = wsum P (fun p => ltB p l)
  | 0, P, hP, [], _, _ => by
    show P.foldr (fun p s => p.2 + s) 0 = _
    rw [foldr_w_eq, wsum]
    congr 1
    refine List.map_congr_left fun p hp => ?_
    rw [List.length_eq_zero_iff.mp (hP p hp)]
    rfl
  | n + 1, P, hP, s :: m, hl, hv => by
    have hm : m.length = n := by simpa using hl
    have hs : s ≤ 5 := hv s (by simp)
    have IH : ∀ t, lookup (pT (indW n (selW t P))) m = wsum (selW t P) (ltB · m) := fun t =>
      lookupW n (selW t P) (selW_length hP) m hm (fun v hv' => hv v (by simp [hv']))
    have F : ∀ t, Full n (pT (indW n (selW t P))) := fun t => full_pT n _ (full_indW n _)
    have h1 := wsum_selW_succ 0 m P
    have h2 := wsum_selW_succ 1 m P
    have h3 := wsum_selW_succ 2 m P
    have h4 := wsum_selW_succ 3 m P
    have h5 := wsum_selW_succ 4 m P
    have h0 := wsum_selW_zero m P
    show lookup (pT (.node _ _ _ _ _ _)) (s :: m) = _
    rw [pT_node, lookup_node_cons]
    interval_cases s
    · exact (lookup_mapT_zero n _ m (F 0) hm).trans h0.symm
    · show lookup (pT (indW n (selW 0 P))) m = _
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
    · show lookup (zipT Nat.add (zipT Nat.add (zipT Nat.add (zipT Nat.add _ _) _) _) _) m = _
      rw [lookup_zipT _ n _ _ m (full_zipT _ n _ _ (full_zipT _ n _ _ (full_zipT _ n _ _ (F 0) (F 1)) (F 2)) (F 3))
          (F 4) hm,
        lookup_zipT _ n _ _ m (full_zipT _ n _ _ (full_zipT _ n _ _ (F 0) (F 1)) (F 2)) (F 3) hm,
        lookup_zipT _ n _ _ m (full_zipT _ n _ _ (F 0) (F 1)) (F 2) hm,
        lookup_zipT _ n _ _ m (F 0) (F 1) hm, IH, IH, IH, IH, IH, h5, h4, h3, h2, h1, h0]
      first | omega | simp [Nat.add_eq]

theorem full_fourT : ∀ n a, Full n (fourT n a)
  | 0, _ => trivial
  | n + 1, _ => ⟨full_fourT n _, full_fourT n _, full_fourT n _, full_fourT n _, full_fourT n _, full_fourT n _⟩

theorem lookup_fourT : ∀ n a (l : List ℕ), l.length = n → (∀ v ∈ l, v ≤ 5) →
    lookup (fourT n a) l = a + l.count 5
  | 0, a, [], _, _ => rfl
  | n + 1, a, s :: m, hl, hv => by
    have hm : m.length = n := by simpa using hl
    have hs : s ≤ 5 := hv s (by simp)
    have hv' : ∀ v ∈ m, v ≤ 5 := fun v h => hv v (by simp [h])
    show lookup (.node _ _ _ _ _ _) (s :: m) = _
    rw [lookup_node_cons]
    interval_cases s <;> simp [pick, lookup_fourT n _ m hm hv', List.count_cons] <;> omega

theorem count_digitsOf {n : ℕ} (u : Fin n → Fin 6) :
    (digitsOf u).count 5 = ∑ j, if u j = 5 then 1 else 0 := by
  induction n with
  | zero => simp [digitsOf]
  | succ n ih =>
    rw [digitsOf_succ, List.count_cons, ih (Fin.tail u), Fin.sum_univ_succ]
    have key : (if ((u 0 : ℕ) == 5) = true then 1 else 0) = (if u 0 = 5 then 1 else 0) := by
      by_cases h : u 0 = 5
      · rw [if_pos h, if_pos]; rw [h]; rfl
      · rw [if_neg h, if_neg]
        intro h'
        apply h
        exact Fin.ext (by simpa using h')
    rw [key, add_comm]
    rfl

theorem count_digitsOf' {n : ℕ} (u : Fin n → Fin 6) : (digitsOf u).count 5 = #{j | u j = 5} := by
  rw [count_digitsOf, card_filter]

def KB.Mem : KB → ℕ → ℕ → Prop
  | .nil, _, _ => False
  | .node l k i r, x, j => KB.Mem l x j ∨ (k = x ∧ i = j) ∨ KB.Mem r x j

theorem KB.find_node (l : KB) (k i : ℕ) (r : KB) (x : ℕ) :
    KB.find (.node l k i r) x = cond (Nat.blt x k) (KB.find l x) (cond (Nat.blt k x) (KB.find r x) (i + 1)) :=
  rfl

theorem KB.find_spec : ∀ (t : KB) (x j : ℕ), KB.find t x = j + 1 → KB.Mem t x j
  | .nil, _, _, h => by simp [KB.find] at h
  | .node l k i r, x, j, h => by
    rw [KB.find_node] at h
    cases hxk : Nat.blt x k
    · cases hkx : Nat.blt k x
      · rw [hxk, hkx] at h
        simp only [cond_false, Nat.add_right_cancel_iff] at h
        have h1 : ¬ x < k := by
          intro h; rw [← Nat.blt_eq] at h; rw [h] at hxk; cases hxk
        have h2 : ¬ k < x := by
          intro h; rw [← Nat.blt_eq] at h; rw [h] at hkx; cases hkx
        exact Or.inr (Or.inl ⟨by omega, h⟩)
      · rw [hxk, hkx] at h
        exact Or.inr (Or.inr (KB.find_spec r x j h))
    · rw [hxk] at h
      exact Or.inl (KB.find_spec l x j h)

theorem build_mem : ∀ (n : ℕ) (l : List (ℕ × ℕ)) (x j : ℕ), KB.Mem (build n l) x j → (x, j) ∈ l
  | 0, _, _, _, h => by simp [build, KB.Mem] at h
  | n + 1, l, x, j, h => by
    unfold build at h
    split at h
    · simp [KB.Mem] at h
    · rename_i k i rest hd
      have hdrop : ∀ p, p ∈ (k, i) :: rest → p ∈ l := fun p hp => by
        rw [← hd] at hp; exact List.mem_of_mem_drop hp
      rcases h with h | ⟨rfl, rfl⟩ | h
      · exact List.mem_of_mem_take (build_mem n _ x j h)
      · exact hdrop _ (by simp)
      · exact hdrop _ (by simp [build_mem n rest x j h])

theorem find_tab_spec (tab : Tab) (x j : ℕ) (h : KB.find (bstOf tab) x = j + 1) :
    ∃ e, tab[j]? = some e ∧ e.1 = x := by
  have hm := build_mem 16 (keyIdxOf tab) x j (KB.find_spec (build 16 (keyIdxOf tab)) x j h)
  unfold keyIdxOf at hm
  simp only [List.mem_zipIdx_iff_getElem?, List.getElem?_map] at hm
  cases he : tab[j]? with
  | none => rw [he] at hm; simp at hm
  | some e =>
    rw [he] at hm
    simp only [Option.map_some, Option.some.injEq] at hm
    exact ⟨e, rfl, hm⟩

section Decode
variable {ι : Type*} {M : Type*} [AddCommGroup M]

noncomputable def funSum (Φ : ℕ → M) : ℕ[X] →+ M where
  toFun f := f.sum (fun j a => a • Φ j)
  map_zero' := by simp
  map_add' f g := Polynomial.sum_add_index f g (fun j a => a • Φ j) (fun _ => zero_smul ℕ _)
    (fun _ _ _ => add_smul _ _ _)

theorem funSum_monomial (Φ : ℕ → M) (a c : ℕ) : funSum Φ (C a * X ^ c) = a • Φ c := by
  show (C a * X ^ c).sum (fun j b => b • Φ j) = _
  rw [C_mul_X_pow_eq_monomial, sum_monomial_index]
  exact zero_smul ℕ _

theorem funSum_natCast_monomial (Φ : ℕ → M) (a c : ℕ) : funSum Φ ((a : ℕ[X]) * X ^ c) = a • Φ c := by
  rw [← funSum_monomial, ← Polynomial.C_eq_natCast, Nat.cast_id]

theorem funSum_data (Φ : ℕ → M) (d : List (ℕ × ℤ)) :
    funSum Φ (dataPoly d false) - funSum Φ (dataPoly d true) = (d.map (fun e => e.2 • Φ e.1)).sum := by
  induction d with
  | nil => simp [dataPoly]
  | cons e d ih =>
    simp only [dataPoly, List.foldr_cons, map_add, Bool.false_eq_true, if_false, if_true,
      List.map_cons, List.sum_cons] at ih ⊢
    rw [funSum_monomial, funSum_monomial, ← ih]
    have h : e.2 • Φ e.1 = e.2.toNat • Φ e.1 - (-e.2).toNat • Φ e.1 := by
      rw [← natCast_zsmul, ← natCast_zsmul, ← sub_smul, Int.toNat_sub_toNat_neg]
    rw [h]
    abel

theorem decodeF (T : Finset ι) (cond : ι → Prop) [DecidablePred cond] (sgn : ι → Bool) (amt cnt : ι → ℕ)
    (m : ℕ) (d : List (ℕ × ℤ))
    (hEq : (histOf T cond sgn amt cnt (2 ^ m)).1 + (dataPoly d true).eval (2 ^ m) =
      (histOf T cond sgn amt cnt (2 ^ m)).2 + (dataPoly d false).eval (2 ^ m))
    (hM1 : (histOf T cond sgn amt cnt 1).1 + (dataPoly d true).eval 1 < 2 ^ m)
    (hM2 : (histOf T cond sgn amt cnt 1).2 + (dataPoly d false).eval 1 < 2 ^ m) (Φ : ℕ → M) :
    ∑ i ∈ T, (if cond i then (if sgn i then (-1 : ℤ) else 1) • (amt i • Φ (cnt i)) else 0) =
      (d.map (fun e => e.2 • Φ e.1)).sum := by
  rw [histOf_eq] at hEq hM1 hM2
  simp only at hEq hM1 hM2
  have hB : 0 < 2 ^ m := by positivity
  have hpoly : histPoly T cond sgn amt cnt false + dataPoly d true =
      histPoly T cond sgn amt cnt true + dataPoly d false := by
    refine ClaudeWCT.Numerics.eq_of_eval_eq hB (fun j => ?_) (fun j => ?_) (by simpa [eval_add] using hEq)
    · exact lt_of_le_of_lt (ClaudeWCT.Numerics.coeff_le_eval_one _ j) (by rw [eval_add]; exact hM1)
    · exact lt_of_le_of_lt (ClaudeWCT.Numerics.coeff_le_eval_one _ j) (by rw [eval_add]; exact hM2)
  have hL := congrArg (funSum Φ) hpoly
  rw [map_add, map_add] at hL
  have hD := funSum_data Φ d
  have hH : funSum Φ (histPoly T cond sgn amt cnt false) - funSum Φ (histPoly T cond sgn amt cnt true) =
      ∑ i ∈ T, (if cond i then (if sgn i then (-1 : ℤ) else 1) • (amt i • Φ (cnt i)) else 0) := by
    simp only [histPoly, map_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    by_cases hc : cond i <;> cases hs : sgn i <;> simp [hc, hs, funSum_natCast_monomial]
  rw [← hH, ← hD]
  have : funSum Φ (histPoly T cond sgn amt cnt false) - funSum Φ (histPoly T cond sgn amt cnt true) =
      funSum Φ (dataPoly d false) - funSum Φ (dataPoly d true) := by
    rw [sub_eq_sub_iff_add_eq_add, add_comm (funSum Φ (dataPoly d false)), hL]
  exact this

end Decode

theorem packS_eq (hb : ℕ) (d : List (ℕ × ℤ)) (b : Bool) : packS hb d b = (dataPoly d b).eval hb := by
  induction d with
  | nil => simp [packS, dataPoly]
  | cons e d ih =>
    simp only [packS, dataPoly, List.foldr_cons] at ih ⊢
    rw [eval_add, ← ih]
    cases b <;> simp [posPart, negPart]

theorem full_keyT : Full 6 keyT := full_pT 6 _ (full_indW 6 _)
theorem full_idxOf (tab : Tab) : Full 6 (idxOf tab) := full_mapT _ 6 _ full_keyT
theorem full_chunkT (tab : Tab) (lo len : ℕ) : Full 6 (chunkT (idxOf tab) lo len) := full_mapT _ 6 _ (full_idxOf tab)
theorem full_g1T' : Full 6 g1T := full_dT 6 _ full_cntT
theorem full_g2T' : Full 6 g2T := full_dT 6 _ (full_mapT _ 6 _ full_cntT)
theorem full_gNearT : Full 6 gNearT := full_zipT _ 6 _ _ full_g1T' (full_fourT 6 0)

theorem frOk_noFree (u : Fin 6 → Fin 6) : FrOk noFree u := by
  intro i h
  fin_cases i <;> exact absurd h (by decide)

theorem histT_tree (hb : ℕ) (c g : T6) (hc : Full 6 c) (hg : Full 6 g) :
    histT hb c noFree g false =
      histOf (univ : Finset (Fin 6 → Fin 6)) (FrOk (n := 6) noFree) (parU (n := 6))
        (fun u : Fin 6 → Fin 6 => lookup g (digitsOf u)) (fun u : Fin 6 → Fin 6 => lookup c (digitsOf u)) hb := by
  rw [histT_eq hb 6 c g noFree false hc hg rfl]
  simp only [Bool.false_xor]
  rfl

theorem histOf_one {ι : Type*} (T : Finset ι) (cond : ι → Prop) [DecidablePred cond] (sgn : ι → Bool)
    (amt cnt cnt' : ι → ℕ) : histOf T cond sgn amt cnt 1 = histOf T cond sgn amt cnt' 1 := by
  simp [histOf]

theorem miss_free (tab : Tab) (g : T6) (hg : Full 6 g) (h : missCheck tab g = true) (u : Fin 6 → Fin 6)
    (hu : lookup g (digitsOf u) ≠ 0) : lookup (idxOf tab) (digitsOf u) ≠ 0 := by
  unfold missCheck at h
  have h' : histT 0 (idxOf tab) noFree g false = (0, 0) := by simpa using h
  rw [histT_tree 0 _ g (full_idxOf tab) hg] at h'
  unfold histOf at h'
  have h1 := congrArg Prod.fst h'
  have h2 := congrArg Prod.snd h'
  simp only [Prod.fst_sum, Prod.snd_sum] at h1 h2
  have e1 := (Finset.sum_eq_zero_iff.mp h1) u (mem_univ u)
  have e2 := (Finset.sum_eq_zero_iff.mp h2) u (mem_univ u)
  rw [if_pos (frOk_noFree u)] at e1 e2
  have hz : lookup g (digitsOf u) * 0 ^ lookup (idxOf tab) (digitsOf u) = 0 := by
    cases hp : parU u <;> simp_all [signedPair]
  intro h0
  rw [h0, pow_zero, mul_one] at hz
  exact hu hz

theorem chunk_decode {M : Type*} [AddCommGroup M] (tab : Tab) (g : T6) (hg : Full 6 g) (m lo len : ℕ) (s0 : ℤ)
    (hm : 1 ≤ m) (hbd : histBound tab g m = true) (hc : chunkCheck tab g m lo len s0 = true) (Φ : ℕ → M) :
    ∑ u : Fin 6 → Fin 6, (if parU u then (-1 : ℤ) else 1) •
        (lookup g (digitsOf u) • Φ (lookup (chunkT (idxOf tab) lo len) (digitsOf u))) =
      ((chunkData tab lo len s0).map (fun e => e.2 • Φ e.1)).sum := by
  unfold chunkCheck at hc
  unfold histBound at hbd
  simp only [Bool.and_eq_true, Nat.beq_eq_true_eq, Nat.blt_eq] at hc hbd
  obtain ⟨⟨hEq0, hd1⟩, hd2⟩ := hc
  have hEq := Nat.eq_of_beq_eq_true hEq0
  obtain ⟨hb1, hb2⟩ := hbd
  rw [packS_eq, packS_eq] at hEq
  rw [packS_eq] at hd1 hd2
  rw [histT_tree _ _ g (full_chunkT tab lo len) hg] at hEq
  rw [histT_tree _ _ g (full_idxOf tab) hg] at hb1 hb2
  have hpow : 2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ m := by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]; ring
  have key := decodeF (univ : Finset (Fin 6 → Fin 6)) (FrOk (n := 6) noFree) (parU (n := 6))
    (fun u => lookup g (digitsOf u)) (fun u => lookup (chunkT (idxOf tab) lo len) (digitsOf u)) m
    (chunkData tab lo len s0) hEq
    (by rw [histOf_one _ _ _ _ _ (fun u => lookup (idxOf tab) (digitsOf u))]; omega)
    (by rw [histOf_one _ _ _ _ _ (fun u => lookup (idxOf tab) (digitsOf u))]; omega) Φ
  rw [← key]
  refine sum_congr rfl fun u _ => ?_
  rw [if_pos (frOk_noFree u)]

theorem lookup_chunkT (tab : Tab) (lo len : ℕ) (u : Fin 6 → Fin 6) :
    lookup (chunkT (idxOf tab) lo len) (digitsOf u) =
      if lo < lookup (idxOf tab) (digitsOf u) ∧ lookup (idxOf tab) (digitsOf u) ≤ lo + len
      then lookup (idxOf tab) (digitsOf u) - lo else 0 := by
  rw [chunkT, lookup_mapT _ 6 _ _ (full_idxOf tab) (digitsOf_length u)]
  by_cases h : lo < lookup (idxOf tab) (digitsOf u) ∧ lookup (idxOf tab) (digitsOf u) ≤ lo + len
  · rw [if_pos h]
    have h1 : Nat.blt lo (lookup (idxOf tab) (digitsOf u)) = true := Nat.blt_eq.mpr h.1
    have h2 : Nat.ble (lookup (idxOf tab) (digitsOf u)) (lo + len) = true := Nat.ble_eq.mpr h.2
    simp [h1, h2]
  · rw [if_neg h]
    by_cases h1 : lo < lookup (idxOf tab) (digitsOf u)
    · have h2 : ¬ lookup (idxOf tab) (digitsOf u) ≤ lo + len := fun h2 => h ⟨h1, h2⟩
      have h2' : Nat.ble (lookup (idxOf tab) (digitsOf u)) (lo + len) = false := by
        cases hb : Nat.ble (lookup (idxOf tab) (digitsOf u)) (lo + len)
        · rfl
        · exact absurd (Nat.ble_eq.mp hb) h2
      simp [h2']
    · have h1' : Nat.blt lo (lookup (idxOf tab) (digitsOf u)) = false := by
        cases hb : Nat.blt lo (lookup (idxOf tab) (digitsOf u))
        · rfl
        · exact absurd (Nat.blt_eq.mp hb) h1
      simp [h1']

def phiC {M : Type*} [AddCommGroup M] (tab : Tab) (lo : ℕ) (Ψ : ℕ → M) (j : ℕ) : M :=
  match j with
  | 0 => 0
  | j + 1 => match tab[lo + j]? with
    | some e => Ψ e.1
    | none => 0

theorem phiC_succ {M : Type*} [AddCommGroup M] (tab : Tab) (lo : ℕ) (Ψ : ℕ → M) (t : ℕ) :
    phiC tab lo Ψ (t + 1) = match tab[lo + t]? with
      | some e => Ψ e.1
      | none => 0 := rfl

theorem chunkData_sum {M : Type*} [AddCommGroup M] (tab : Tab) (lo len : ℕ) (s0 : ℤ) (Ψ : ℕ → M) :
    ((chunkData tab lo len s0).map (fun e => e.2 • phiC tab lo Ψ e.1)).sum =
      (((tab.drop lo).take len).map (fun e => e.2 • Ψ e.1)).sum := by
  unfold chunkData
  rw [List.map_cons, List.sum_cons]
  have h0 : (s0 • phiC tab lo Ψ 0 : M) = 0 := by simp [phiC]
  simp only []
  rw [h0, zero_add, List.map_map]
  have hz : ∀ p ∈ ((tab.drop lo).take len).zipIdx,
      ((fun e : ℕ × ℤ => e.2 • phiC tab lo Ψ e.1) ∘ (fun p : (ℕ × ℤ) × ℕ => (p.2 + 1, p.1.2))) p =
        (fun e : ℕ × ℤ => e.2 • Ψ e.1) p.1 := by
    intro p hp
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_take, List.getElem?_drop] at hp
    show p.1.2 • phiC tab lo Ψ (p.2 + 1) = p.1.2 • Ψ p.1.1
    split_ifs at hp with hlt
    all_goals first | (simp only [phiC, hp]; done) | simp at hp
  rw [List.map_congr_left hz]
  rw [show (fun p : (ℕ × ℤ) × ℕ => (fun e : ℕ × ℤ => e.2 • Ψ e.1) p.1) =
    (fun e : ℕ × ℤ => e.2 • Ψ e.1) ∘ Prod.fst from rfl, ← List.map_map, List.zipIdx_map_fst]

theorem sum_chunks {M : Type*} [AddCommMonoid M] (f : ℕ × ℤ → M) (len : ℕ) :
    ∀ (nc : ℕ) (l : List (ℕ × ℤ)), l.length = nc * len →
      ∑ c ∈ range nc, (((l.drop (c * len)).take len).map f).sum = (l.map f).sum
  | 0, l, h => by
    have hl : l = [] := List.length_eq_zero_iff.mp (by simpa using h)
    subst hl
    simp
  | nc + 1, l, h => by
    rw [Finset.sum_range_succ']
    have hl : (l.drop len).length = nc * len := by rw [List.length_drop, h, Nat.succ_mul, Nat.add_sub_cancel]
    have ih := sum_chunks f len nc (l.drop len) hl
    have e : ∀ c ∈ range nc, (((l.drop ((c + 1) * len)).take len).map f).sum =
        ((((l.drop len).drop (c * len)).take len).map f).sum := by
      intro c _
      rw [List.drop_drop, show (c + 1) * len = len + c * len by ring]
    rw [sum_congr rfl e, ih, zero_mul, List.drop_zero]
    conv_rhs => rw [← List.take_append_drop len l]
    rw [List.map_append, List.sum_append, add_comm]

theorem tab_key {M : Type*} [AddCommGroup M] (tab : Tab) (g : T6) (hg : Full 6 g) (m len nc : ℕ) (s0 : ℕ → ℤ)
    (hm : 1 ≤ m) (hlen : tab.length = nc * len) (hmiss : missCheck tab g = true) (hbd : histBound tab g m = true)
    (hch : ∀ c < nc, chunkCheck tab g m (c * len) len (s0 c) = true) (Ψ : ℕ → M) :
    ∑ u : Fin 6 → Fin 6, (if parU u then (-1 : ℤ) else 1) •
        (lookup g (digitsOf u) • Ψ (lookup keyT (digitsOf u))) =
      (tab.map (fun e => e.2 • Ψ e.1)).sum := by
  have hdec : ∀ c ∈ range nc, ∑ u : Fin 6 → Fin 6, (if parU u then (-1 : ℤ) else 1) •
      (lookup g (digitsOf u) • phiC tab (c * len) Ψ (lookup (chunkT (idxOf tab) (c * len) len) (digitsOf u))) =
      (((tab.drop (c * len)).take len).map (fun e => e.2 • Ψ e.1)).sum := by
    intro c hc
    rw [chunk_decode tab g hg m (c * len) len (s0 c) hm hbd (hch c (mem_range.mp hc)), chunkData_sum]
  rw [← sum_chunks _ len nc tab hlen, ← sum_congr rfl hdec, sum_comm]
  refine sum_congr rfl fun u _ => ?_
  rw [← smul_sum, ← smul_sum]
  by_cases hg0 : lookup g (digitsOf u) = 0
  · simp [hg0]
  congr 2
  have hi := miss_free tab g hg hmiss u hg0
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hi
  have hf : KB.find (bstOf tab) (lookup keyT (digitsOf u)) = j + 1 :=
    (lookup_mapT (fun k => KB.find (bstOf tab) k) 6 keyT (digitsOf u) full_keyT (digitsOf_length u)).symm.trans hj
  obtain ⟨e, he1, he2⟩ := find_tab_spec tab _ j hf
  have hjlt : j < nc * len := by rw [← hlen]; exact (List.getElem?_eq_some_iff.mp he1).1
  have hlen0 : 0 < len := by
    rcases Nat.eq_zero_or_pos len with h0 | h0
    · rw [h0, mul_zero] at hjlt; omega
    · exact h0
  have hc0 : j / len ∈ range nc := mem_range.mpr ((Nat.div_lt_iff_lt_mul hlen0).mpr hjlt)
  rw [sum_eq_single (j / len)]
  · rw [lookup_chunkT, hj]
    have h1 : j / len * len ≤ j := Nat.div_mul_le_self j len
    have h2 : j < j / len * len + len := by
      have := Nat.lt_div_mul_add (a := j) hlen0
      linarith
    rw [if_pos ⟨by omega, by omega⟩]
    have hsub : j.succ - j / len * len = (j - j / len * len) + 1 := by omega
    rw [hsub, phiC_succ, show j / len * len + (j - j / len * len) = j by omega, he1]
    exact congrArg Ψ he2.symm
  · intro c _ hne
    rw [lookup_chunkT, hj]
    have hn : ¬ (c * len < j.succ ∧ j.succ ≤ c * len + len) := by
      rintro ⟨h1, h2⟩
      apply hne
      have hcl : c * len ≤ j := by omega
      have hcu : j < (c + 1) * len := by rw [add_mul, one_mul]; omega
      have := (Nat.le_div_iff_mul_le hlen0).mpr hcl
      have := (Nat.div_lt_iff_lt_mul hlen0).mpr hcu
      omega
    rw [if_neg hn, phiC]
  · intro h; exact absurd hc0 h

end ClaudeR3.Tab
