import SigGolfCandidate.ClaudeWCT.W9.T3M.SigCodec
import SigGolfCandidate.ClaudeWCT.WCT9.Omit

/-! # The compact (H2) signature bytes

5,310 bytes: the 332 digests of `sigDigests` with digest 183 (the top layer's level-11 sibling) cut out, then that
digest's low 14 bytes. `sigBC` encodes, `sigDecC` decodes (the omitted 16 bits decode as zero), and
`sigDecC (sigBC σ) = proj σ`, `sigBC (sigDecC b) = b`, `sigBC (proj σ) = sigBC σ`. -/

namespace ClaudeWCT.W9.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SigGolfCandidate.T3M (digNat digNat_lt digNat_digit digNat_eq_of_digits getD_append_left' getD_append_right'
  getD_ofFn' chainCount_0 chainCount_1 chainCount_2 chainCount_3 height_0 height_1 height_2 height_3)
set_option maxRecDepth 10000

abbrev CBytes := Bytes 5310
def sibIdx : Nat := 183
def cDig (b : CBytes) (k : Nat) : Digest := b.extractLsb' (128 * k) 128
/-- The digest at full-layout index `k` of the compact bytes. -/
def digC (b : CBytes) (k : Nat) : Digest :=
  if k < 183 then cDig b k else if k = 183 then cDig b 331 else cDig b (k - 1)
def sigDecC (b : CBytes) : WCT9.Signature where
  rho := digC b 0
  openings := fun k => ⟨fun t => digC b (1 + 13 * k.val + t.val), fun l => digC b (1 + 13 * k.val + 6 + l.val)⟩
  layers := fun lay => ⟨fun i => digC b (layIdx lay + i.val), fun j => digC b (layIdx lay + (chainCount lay + j.val))⟩
def sigBC (s : WCT9.Signature) : CBytes :=
  BitVec.ofNat _ (digNat ((sigDigests s).eraseIdx 183) + 2 ^ (128 * 331) * (((sigDigests s).getD 183 0).toNat % 2 ^ 112))

theorem sigDigests_sigDecC (b : CBytes) (k : Nat) (hk : k < 332) :
    (sigDigests (sigDecC b)).getD k 0 = digC b k := by
  by_cases h0 : k = 0
  · subst h0; exact sigDigests_rho _
  by_cases h1 : k < 118
  · have hq : (k - 1) / 13 < 9 := by omega
    have e : k = 1 + 13 * (⟨(k - 1) / 13, hq⟩ : WCT9.Coord).val + (k - 1) % 13 := by simp; omega
    by_cases hr : (k - 1) % 13 < 6
    · have := sigDigests_value (sigDecC b) ⟨(k - 1) / 13, hq⟩ ⟨(k - 1) % 13, hr⟩
      simp only at this
      rw [← e] at this
      rw [this]
      show digC b (1 + 13 * ((k - 1) / 13) + (k - 1) % 13) = digC b k
      rw [← e]
    · have := sigDigests_path (sigDecC b) ⟨(k - 1) / 13, hq⟩ ⟨(k - 1) % 13 - 6, by omega⟩
      simp only at this
      rw [show 1 + 13 * ((k - 1) / 13) + 6 + ((k - 1) % 13 - 6) = k by omega] at this
      rw [this]
      show digC b (1 + 13 * ((k - 1) / 13) + 6 + ((k - 1) % 13 - 6)) = digC b k
      rw [show 1 + 13 * ((k - 1) / 13) + 6 + ((k - 1) % 13 - 6) = k by omega]
  have key : ∀ (lay : Layer) (i : Nat), i < chainCount lay + height lay → layIdx lay + i = k →
      (sigDigests (sigDecC b)).getD k 0 = digC b k := by
    intro lay i hi he
    subst he
    rw [sigDigests_layer _ lay i hi]
    unfold layerList
    by_cases hc : i < chainCount lay
    · rw [getD_append_left' (by simpa using hc), getD_ofFn' _ i hc]; rfl
    · rw [getD_append_right' (by simp; omega), List.length_ofFn, getD_ofFn' _ (i - chainCount lay) (by omega)]
      show digC b (layIdx lay + (chainCount lay + (i - chainCount lay))) = _
      rw [show chainCount lay + (i - chainCount lay) = i by omega]
  by_cases h3 : k < 184
  · exact key 0 (k - 118) (by rw [chainCount_0, height_0]; omega) (by simp [layIdx]; omega)
  by_cases h4 : k < 234
  · exact key 1 (k - 184) (by rw [chainCount_1, height_1]; omega) (by simp [layIdx]; omega)
  by_cases h5 : k < 283
  · exact key 2 (k - 234) (by rw [chainCount_2, height_2]; omega) (by simp [layIdx]; omega)
  · exact key 3 (k - 283) (by rw [chainCount_3, height_3]; omega) (by simp [layIdx]; omega)

theorem cDig_toNat (b : CBytes) (k : Nat) : (cDig b k).toNat = b.toNat / 2 ^ (128 * k) % 2 ^ 128 := by
  rw [cDig, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

theorem cTail_lt (b : CBytes) : b.toNat / 2 ^ (128 * 331) < 2 ^ 112 := by
  have hb := b.isLt
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
  exact lt_of_lt_of_eq hb (by norm_num)

theorem getD_eraseIdx {α : Type} (l : List α) (i j : Nat) (d : α) :
    (l.eraseIdx i).getD j d = if j < i then l.getD j d else l.getD (j + 1) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx]
  split <;> rfl

theorem length_eraseIdx_sig (s : WCT9.Signature) : ((sigDigests s).eraseIdx 183).length = 331 := by
  rw [List.length_eraseIdx, length_sigDigests]; decide

theorem mod_digit (B n k : Nat) (hk : k < n) :
    B % 2 ^ (128 * n) / 2 ^ (128 * k) % 2 ^ 128 = B / 2 ^ (128 * k) % 2 ^ 128 := by
  rw [show 2 ^ (128 * n) = 2 ^ (128 * k) * 2 ^ (128 * (n - k)) by rw [← pow_add]; congr 1; omega,
    Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd]
  exact pow_dvd_pow 2 (by omega)

theorem lt_split (X y A M : Nat) (hX : X < 2 ^ A) (hy : y < M) : X + 2 ^ A * y < 2 ^ A * M := by
  have : 2 ^ A * y + 2 ^ A ≤ 2 ^ A * M := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hy
  omega

theorem split_mod (D T A : Nat) (hD : D < 2 ^ A) : (D + 2 ^ A * T) % 2 ^ A = D := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hD]

theorem split_div (D T A : Nat) (hD : D < 2 ^ A) : (D + 2 ^ A * T) / 2 ^ A = T := by
  rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hD, Nat.zero_add]

theorem pow_5310 : (2 : Nat) ^ (8 * 5310) = 2 ^ (128 * 331) * 2 ^ 112 := by rw [← pow_add]

set_option exponentiation.threshold 50000 in
theorem sigBC_sigDecC (b : CBytes) : sigBC (sigDecC b) = b := by
  apply BitVec.eq_of_toNat_eq
  unfold sigBC
  rw [BitVec.toNat_ofNat]
  have h331 : digNat ((sigDigests (sigDecC b)).eraseIdx 183) = b.toNat % 2 ^ (128 * 331) := by
    apply digNat_eq_of_digits
    · rw [length_eraseIdx_sig]; exact Nat.mod_lt _ (by positivity)
    · intro k hk
      rw [length_eraseIdx_sig] at hk
      rw [getD_eraseIdx, mod_digit _ 331 k hk]
      split
      · rename_i hlt
        rw [sigDigests_sigDecC b k (by omega), digC, if_pos hlt, cDig_toNat]
      · rename_i hge
        rw [sigDigests_sigDecC b (k + 1) (by omega), digC, if_neg (by omega), if_neg (by omega),
          show k + 1 - 1 = k by omega, cDig_toNat]
  have htail : ((sigDigests (sigDecC b)).getD 183 0).toNat % 2 ^ 112 = b.toNat / 2 ^ (128 * 331) := by
    rw [sigDigests_sigDecC b 183 (by decide), digC, if_neg (by decide), if_pos rfl, cDig_toNat]
    have := cTail_lt b
    rw [Nat.mod_eq_of_lt (show b.toNat / 2 ^ (128 * 331) < 2 ^ 128 from
      lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) (by norm_num))), Nat.mod_eq_of_lt this]
  rw [h331, htail, Nat.mod_add_div]
  exact Nat.mod_eq_of_lt b.isLt

/-- Two signatures that agree everywhere but the omitted bits have the same digests away from index 183. -/
theorem sigDigests_proj_getD (s : WCT9.Signature) (k : Nat) (hk : k < 332) (h183 : k ≠ 183) :
    (sigDigests (WCT9.proj s)).getD k 0 = (sigDigests s).getD k 0 := by
  by_cases h0 : k = 0
  · subst h0; rw [sigDigests_rho, sigDigests_rho]; rfl
  by_cases h1 : k < 118
  · have hq : (k - 1) / 13 < 9 := by omega
    have e : k = 1 + 13 * (⟨(k - 1) / 13, hq⟩ : WCT9.Coord).val + (k - 1) % 13 := by simp; omega
    rw [e, sigDigests_opening _ _ _ (by omega), sigDigests_opening _ _ _ (by omega)]
    rfl
  have key : ∀ (lay : Layer) (i : Nat), i < chainCount lay + height lay → layIdx lay + i = k →
      (sigDigests (WCT9.proj s)).getD k 0 = (sigDigests s).getD k 0 := by
    intro lay i hi he
    subst he
    rw [sigDigests_layer _ lay i hi, sigDigests_layer _ lay i hi]
    unfold layerList
    have hl : (WCT9.proj s).layers lay = WCT9.fillLayer lay (s.layers lay) 0 := rfl
    rw [hl]
    by_cases hc : i < chainCount lay
    · rw [getD_append_left' (by simpa using hc), getD_append_left' (by simpa using hc)]; rfl
    · rw [getD_append_right' (by simp; omega), getD_append_right' (by simp; omega), List.length_ofFn,
        List.length_ofFn, getD_ofFn' _ (i - chainCount lay) (by omega), getD_ofFn' _ (i - chainCount lay) (by omega)]
      apply WCT9.fillLayer_path_ne
      intro hh
      have hlay : lay = 0 := Fin.ext hh.1
      subst hlay
      simp only [Fin.val_mk] at hh
      apply h183
      show layIdx 0 + i = 183
      rw [chainCount_0] at hc hh
      simp only [layIdx]
      norm_num at hh ⊢
      omega
  by_cases h3 : k < 184
  · exact key 0 (k - 118) (by rw [chainCount_0, height_0]; omega) (by simp [layIdx]; omega)
  by_cases h4 : k < 234
  · exact key 1 (k - 184) (by rw [chainCount_1, height_1]; omega) (by simp [layIdx]; omega)
  by_cases h5 : k < 283
  · exact key 2 (k - 234) (by rw [chainCount_2, height_2]; omega) (by simp [layIdx]; omega)
  · exact key 3 (k - 283) (by rw [chainCount_3, height_3]; omega) (by simp [layIdx]; omega)

theorem sigDigests_183 (s : WCT9.Signature) : (sigDigests s).getD 183 0 = WCT9.topSib s := by
  have := sigDigests_layPath s 0 11 (by decide)
  exact this

theorem sigBC_proj (s : WCT9.Signature) : sigBC (WCT9.proj s) = sigBC s := by
  have hL : (sigDigests (WCT9.proj s)).eraseIdx 183 = (sigDigests s).eraseIdx 183 := by
    apply List.ext_getElem?
    intro j
    by_cases hj : j < 331
    · have e1 := getD_eraseIdx (sigDigests (WCT9.proj s)) 183 j 0
      have e2 := getD_eraseIdx (sigDigests s) 183 j 0
      have l1 : ((sigDigests (WCT9.proj s)).eraseIdx 183).length = 331 := length_eraseIdx_sig _
      have l2 : ((sigDigests s).eraseIdx 183).length = 331 := length_eraseIdx_sig _
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)]
      refine congrArg some ?_
      rw [← List.getD_eq_getElem _ 0, ← List.getD_eq_getElem _ 0, e1, e2]
      split
      · exact sigDigests_proj_getD s j (by omega) (by omega)
      · exact sigDigests_proj_getD s (j + 1) (by omega) (by omega)
    · rw [List.getElem?_eq_none (by rw [length_eraseIdx_sig]; omega),
        List.getElem?_eq_none (by rw [length_eraseIdx_sig]; omega)]
  have hT : ((sigDigests (WCT9.proj s)).getD 183 0).toNat % 2 ^ 112 =
      ((sigDigests s).getD 183 0).toNat % 2 ^ 112 := by
    rw [sigDigests_183, sigDigests_183]
    unfold WCT9.proj
    rw [WCT9.topSib_fillTop, WCT9.setTop_toNat]
    try simp
  unfold sigBC
  rw [hL, hT]

theorem digC_183 (b : CBytes) : digC b 183 = cDig b 331 := by
  unfold digC; rw [if_neg (by decide), if_pos rfl]

theorem proj_sigDecC (b : CBytes) : WCT9.proj (sigDecC b) = sigDecC b := by
  unfold WCT9.proj WCT9.fillTop
  show (⟨(sigDecC b).rho, (sigDecC b).openings, _⟩ : WCT9.Signature) = sigDecC b
  congr 1
  funext lay
  unfold WCT9.fillLayer
  congr 1
  funext j
  split
  · rename_i hh
    have hlay : lay = 0 := Fin.ext hh.1
    subst hlay
    have hj : j = WCT9.topJ := Fin.ext hh.2
    subst hj
    show WCT9.setTop (digC b (layIdx 0 + (chainCount 0 + 11))) 0 = digC b (layIdx 0 + (chainCount 0 + 11))
    rw [show layIdx 0 + (chainCount 0 + 11) = 183 by decide, digC_183]
    apply BitVec.eq_of_toNat_eq
    rw [WCT9.setTop_toNat, cDig_toNat]
    have := cTail_lt b
    have h1 : b.toNat / 2 ^ (128 * 331) % 2 ^ 128 = b.toNat / 2 ^ (128 * 331) := Nat.mod_eq_of_lt (by omega)
    rw [h1, Nat.mod_eq_of_lt this]
    simp
  · rfl

theorem sigDecC_sigBC (s : WCT9.Signature) : sigDecC (sigBC s) = WCT9.proj s := by
  have hb := sigBC_sigDecC (sigBC s)
  -- both sides are projected signatures with the same compact bytes
  have key : ∀ t u : WCT9.Signature, WCT9.proj t = t → WCT9.proj u = u → sigBC t = sigBC u → t = u := by
    intro t u ht hu he
    have hd : ∀ k < 332, (sigDigests t).getD k 0 = (sigDigests u).getD k 0 := by
      intro k hk
      have hbt := congrArg BitVec.toNat he
      unfold sigBC at hbt
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at hbt
      have hlt : ∀ v : WCT9.Signature, digNat ((sigDigests v).eraseIdx 183) +
          2 ^ (128 * 331) * (((sigDigests v).getD 183 0).toNat % 2 ^ 112) < 2 ^ (8 * 5310) := by
        intro v
        have h1 := digNat_lt ((sigDigests v).eraseIdx 183)
        rw [length_eraseIdx_sig] at h1
        rw [pow_5310]
        exact lt_split _ _ _ _ h1 (Nat.mod_lt _ (by positivity))
      rw [Nat.mod_eq_of_lt (hlt t), Nat.mod_eq_of_lt (hlt u)] at hbt
      have hDl : ∀ v : WCT9.Signature, digNat ((sigDigests v).eraseIdx 183) < 2 ^ (128 * 331) := fun v => by
        have h1 := digNat_lt ((sigDigests v).eraseIdx 183); rwa [length_eraseIdx_sig] at h1
      have hD : digNat ((sigDigests t).eraseIdx 183) = digNat ((sigDigests u).eraseIdx 183) := by
        have h := congrArg (fun x => x % 2 ^ (128 * 331)) hbt
        rwa [split_mod _ _ _ (hDl t), split_mod _ _ _ (hDl u)] at h
      have hT : ((sigDigests t).getD 183 0).toNat % 2 ^ 112 = ((sigDigests u).getD 183 0).toNat % 2 ^ 112 := by
        have h := congrArg (fun x => x / 2 ^ (128 * 331)) hbt
        rwa [split_div _ _ _ (hDl t), split_div _ _ _ (hDl u)] at h
      have hsmall : ∀ v : WCT9.Signature, WCT9.proj v = v →
          ((sigDigests v).getD 183 0).toNat % 2 ^ 112 = ((sigDigests v).getD 183 0).toNat := by
        intro v hv
        rw [sigDigests_183, ← hv]
        unfold WCT9.proj
        rw [WCT9.topSib_fillTop, WCT9.setTop_toNat]
        simp [Nat.mod_mod]
      have hE : ∀ j, ((sigDigests t).eraseIdx 183).getD j 0 = ((sigDigests u).eraseIdx 183).getD j 0 := fun j => by
        apply BitVec.eq_of_toNat_eq
        rw [← digNat_digit, ← digNat_digit, hD]
      by_cases h183 : k = 183
      · subst h183
        apply BitVec.eq_of_toNat_eq
        rw [← hsmall t ht, ← hsmall u hu]
        exact hT
      · by_cases hk183 : k < 183
        · have h := hE k
          rwa [getD_eraseIdx, getD_eraseIdx, if_pos hk183, if_pos hk183] at h
        · have h := hE (k - 1)
          rwa [getD_eraseIdx, getD_eraseIdx, if_neg (by omega), if_neg (by omega),
            show k - 1 + 1 = k by omega] at h
    have hlist : sigDigests t = sigDigests u := by
      apply List.ext_getElem?
      intro k
      by_cases hk : k < 332
      · rw [List.getElem?_eq_getElem (by rw [length_sigDigests]; omega),
          List.getElem?_eq_getElem (by rw [length_sigDigests]; omega)]
        congr 1
        rw [← List.getD_eq_getElem _ 0, ← List.getD_eq_getElem _ 0]
        exact hd k hk
      · rw [List.getElem?_eq_none (by rw [length_sigDigests]; omega),
          List.getElem?_eq_none (by rw [length_sigDigests]; omega)]
    have hB : sigB t = sigB u := by
      apply BitVec.eq_of_toNat_eq
      rw [sigB_toNat, sigB_toNat, hlist]
    calc t = sigDec (sigB t) := (sigDec_sigB t).symm
      _ = sigDec (sigB u) := by rw [hB]
      _ = u := sigDec_sigB u
  apply key
  · exact proj_sigDecC _
  · exact WCT9.proj_proj s
  · rw [hb, sigBC_proj]

end ClaudeWCT.W9.T3M

namespace ClaudeWCT.W9.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SigGolfCandidate.T3M (digNat digNat_lt digNat_cons digNat_nil)

/-- Full-layout digest index of compact digest slot `k` (slot 331 holds the top sibling). -/
def cIdx (k : Nat) : Nat := if k < 183 then k else if k < 331 then k + 1 else 183
def compactList (s : WCT9.Signature) : List Digest := (List.range 332).map fun k => (sigDigests s).getD (cIdx k) 0

theorem digNat_append (L1 L2 : List Digest) : digNat (L1 ++ L2) = digNat L1 + 2 ^ (128 * L1.length) * digNat L2 := by
  induction L1 with
  | nil => simp [digNat_nil]
  | cons d L ih =>
    rw [List.cons_append, digNat_cons, digNat_cons, ih, List.length_cons,
      show 128 * (L.length + 1) = 128 + 128 * L.length by ring, pow_add]
    ring

theorem compactList_eq (s : WCT9.Signature) :
    compactList s = (sigDigests s).eraseIdx 183 ++ [(sigDigests s).getD 183 0] := by
  apply List.ext_getElem?
  intro k
  have hl := length_eraseIdx_sig s
  by_cases hk : k < 332
  · rw [List.getElem?_eq_getElem (by simp only [compactList, List.length_map, List.length_range]; omega),
      List.getElem?_eq_getElem (by simp only [List.length_append, hl, List.length_singleton]; omega)]
    refine congrArg some ?_
    simp only [compactList, List.getElem_map, List.getElem_range]
    by_cases h331 : k < 331
    · rw [List.getElem_append_left (by omega), ← List.getD_eq_getElem _ 0, getD_eraseIdx]
      unfold cIdx
      split <;> first | rfl | omega | (split <;> first | rfl | omega)
    · rw [List.getElem_append_right (by omega)]
      simp only [hl, show k - 331 = 0 by omega, List.getElem_cons_zero]
      unfold cIdx; rw [if_neg (by omega), if_neg (by omega)]
  · rw [List.getElem?_eq_none (by simp only [compactList, List.length_map, List.length_range]; omega),
      List.getElem?_eq_none (by simp only [List.length_append, hl, List.length_singleton]; omega)]

theorem mod_split (X y A M : Nat) (hX : X < 2 ^ A) (hM : 0 < M) :
    (X + 2 ^ A * y) % (2 ^ A * M) = X + 2 ^ A * (y % M) := by
  conv_lhs => rw [← Nat.div_add_mod y M]
  rw [show X + 2 ^ A * (M * (y / M) + y % M) = (X + 2 ^ A * (y % M)) + (2 ^ A * M) * (y / M) by ring,
    Nat.add_mul_mod_self_left]
  apply Nat.mod_eq_of_lt
  have hr : y % M < M := Nat.mod_lt _ hM
  have h1 : 2 ^ A * (y % M) + 2 ^ A ≤ 2 ^ A * M := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hr
  omega
theorem sigBC_toNat_compact (s : WCT9.Signature) :
    (sigBC s).toNat = digNat (compactList s) % 2 ^ (8 * 5310) := by
  rw [compactList_eq, digNat_append, length_eraseIdx_sig, digNat_cons, digNat_nil, Nat.mul_zero, Nat.add_zero]
  unfold sigBC
  rw [BitVec.toNat_ofNat]
  have h1 := digNat_lt ((sigDigests s).eraseIdx 183)
  rw [length_eraseIdx_sig] at h1
  have e : (2 : Nat) ^ (8 * 5310) = 2 ^ (128 * 331) * 2 ^ 112 := by rw [← pow_add]
  rw [e, mod_split _ _ _ _ h1 (by positivity), mod_split _ _ _ _ h1 (by positivity), Nat.mod_mod]
end ClaudeWCT.W9.T3M
