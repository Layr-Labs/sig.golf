import SigGolfCandidate.ClaudeWCT.W9.T3M.SigCodec
import SigGolfCandidate.ClaudeWCT.WCT9.Omit
import SigGolfCandidate.Research.V7Composed198Gate

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

/-! Compact serialization for the shared forest. -/
namespace ClaudeWCT.W9.T3M.SharedCodec
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
abbrev SharedSignature := SigGolfCandidate.Research.SharedForest.Signature
open SigGolfCandidate.T3M (digNat getD_append_left' getD_append_right' getD_ofFn'
  chainCount_0 chainCount_1 chainCount_2 chainCount_3 height_0 height_1 height_2 height_3)

def pairList (p : PairOpening) : List Digest :=
  ((List.ofFn p.firstValues ++ List.ofFn p.firstPath) ++
    List.ofFn p.secondValues) ++ List.ofFn p.secondPath
def singletonList (p : SingletonOpening) : List Digest :=
  List.ofFn p.values ++ List.ofFn p.path
def layerList (s : SharedSignature) (lay : Layer) : List Digest :=
  List.ofFn (s.layers lay).values ++ List.ofFn (s.layers lay).path
def sigDigests (s : SharedSignature) : List Digest :=
  (([s.rho] ++ (List.ofFn s.forest.pairs).flatMap pairList) ++ singletonList s.forest.singleton) ++
    (layerList s 0 ++ (layerList s 1 ++ (layerList s 2 ++ layerList s 3)))
def layIdx (lay : Layer) : Nat := (![114,180,230,279] : Layer → Nat) lay
theorem pairList_length (p : PairOpening) : (pairList p).length = 25 := by simp [pairList]
theorem singletonList_length (p : SingletonOpening) : (singletonList p).length = 13 := by
  simp [singletonList]
theorem pairs_length (s : SharedSignature) : ((List.ofFn s.forest.pairs).flatMap pairList).length = 100 := by
  rw [List.length_flatMap]
  simp only [List.map_ofFn, Function.comp_def, pairList_length]
  rfl
theorem layerList_length (s : SharedSignature) (lay : Layer) :
    (layerList s lay).length = chainCount lay + height lay := by
  simp only [layerList, List.length_append, List.length_ofFn]
theorem sigDigests_length (s : SharedSignature) : (sigDigests s).length = 328 := by
  simp only [sigDigests, List.length_append, List.length_singleton, pairs_length,
    singletonList_length, layerList_length]
  rfl

abbrev CBytes := Bytes 5248
def cDig (b : CBytes) (k : Nat) : Digest := b.extractLsb' (128 * k) 128
/-- Full index179 is stored as the trailing112-bit top sibling. -/
def digC (b : CBytes) (k : Nat) : Digest :=
  if k < 179 then cDig b k else if k = 179 then (b.extractLsb' (128 * 327) 112).setWidth 128 else cDig b (k - 1)
def sigDecC (b : CBytes) : SharedSignature where
  rho := digC b 0
  policyHints := b.extractLsb' (8 * 5246) 16
  forest := {
    pairs := fun p => {
      firstValues := fun i => digC b (1 + 25 * p.val + i.val)
      firstPath := fun i => digC b (1 + 25 * p.val + 6 + i.val)
      secondValues := fun i => digC b (1 + 25 * p.val + 12 + i.val)
      secondPath := fun i => digC b (1 + 25 * p.val + 18 + i.val) }
    singleton := {
      values := fun i => digC b (101 + i.val)
      path := fun i => digC b (107 + i.val) } }
  layers := fun lay => {
    values := fun i => digC b (layIdx lay + i.val)
    path := fun i => digC b (layIdx lay + chainCount lay + i.val) }
def sigBC (s : SharedSignature) : CBytes :=
  BitVec.ofNat _ (digNat ((sigDigests s).eraseIdx 179) +
    2 ^ (128 * 327) * (((sigDigests s).getD 179 0).toNat % 2 ^ 112) +
    2 ^ (8 * 5246) * s.policyHints.toNat)
theorem compact_length : 327 * 16 + 14 + 2 = 5248 := by decide
theorem sigDigests_rho (s : SharedSignature) : (sigDigests s).getD 0 0 = s.rho := by rfl
theorem sigDigests_pair (s : SharedSignature) (p : Fin 4) (i : Nat) (hi : i < 25) :
    (sigDigests s).getD (1 + 25 * p.val + i) 0 = (pairList (s.forest.pairs p)).getD i 0 := by
  unfold sigDigests
  rw [getD_append_left' (by simp only [List.length_append, List.length_singleton,
        pairs_length, singletonList_length]; omega),
    getD_append_left' (by simp only [List.length_append, List.length_singleton, pairs_length]; omega),
    getD_append_right' (by simp; omega), List.length_singleton,
    show 1 + 25 * p.val + i - 1 = 25 * p.val + i by omega,
    ClaudeWCT.W9.T3M.getD_flatMap_chunks pairList 25 0 pairList_length _ p.val i (by simp) hi,
    List.getElem_ofFn]
theorem pairList_firstValue (p : PairOpening) (i : Fin 6) :
    (pairList p).getD i.val 0 = p.firstValues i := by
  unfold pairList
  rw [getD_append_left' (by simp; omega), getD_append_left' (by simp; omega),
    getD_append_left' (by simp), getD_ofFn']
theorem pairList_firstPath (p : PairOpening) (i : Fin 6) :
    (pairList p).getD (6 + i.val) 0 = p.firstPath i := by
  unfold pairList
  rw [getD_append_left' (by simp; omega), getD_append_left' (by simp; omega),
    getD_append_right' (by simp), List.length_ofFn, Nat.add_sub_cancel_left, getD_ofFn']
theorem pairList_secondValue (p : PairOpening) (i : Fin 6) :
    (pairList p).getD (12 + i.val) 0 = p.secondValues i := by
  unfold pairList
  rw [getD_append_left' (by simp; omega), getD_append_right' (by simp)]
  simp only [List.length_append, List.length_ofFn]
  rw [show 12 + i.val - (6 + 6) = i.val by omega, getD_ofFn']
theorem pairList_secondPath (p : PairOpening) (i : Fin 7) :
    (pairList p).getD (18 + i.val) 0 = p.secondPath i := by
  unfold pairList
  rw [getD_append_right' (by simp)]
  simp only [List.length_append, List.length_ofFn]
  rw [show 18 + i.val - (6 + 6 + 6) = i.val by omega, getD_ofFn']
theorem sigDigests_singleton (s : SharedSignature) (i : Nat) (hi : i < 13) :
    (sigDigests s).getD (101 + i) 0 = (singletonList s.forest.singleton).getD i 0 := by
  unfold sigDigests
  rw [getD_append_left' (by simp only [List.length_append, List.length_singleton,
      pairs_length, singletonList_length]; omega), getD_append_right' (by
      simp only [List.length_append, List.length_singleton, pairs_length]; omega)]
  simp only [List.length_append, List.length_singleton, pairs_length]
  rw [show 101 + i - (1 + 100) = i by omega]
theorem sigDigests_tail (s : SharedSignature) (k : Nat) (hk : 114 ≤ k) : (sigDigests s).getD k 0 =
    (layerList s 0 ++ (layerList s 1 ++ (layerList s 2 ++ layerList s 3))).getD (k - 114) 0 := by
  unfold sigDigests
  rw [getD_append_right' (by simp only [List.length_append, List.length_singleton, pairs_length, singletonList_length]; omega)]
  simp only [List.length_append, List.length_singleton, pairs_length, singletonList_length]
theorem sigDigests_layer (s : SharedSignature) (lay : Layer) (i : Nat) (hi : i < chainCount lay + height lay) :
    (sigDigests s).getD (layIdx lay + i) 0 = (layerList s lay).getD i 0 := by
  have l0 := layerList_length s 0
  have l1 := layerList_length s 1
  have l2 := layerList_length s 2
  rw [chainCount_0, height_0] at l0
  rw [chainCount_1, height_1] at l1
  rw [chainCount_2, height_2] at l2
  fin_cases lay
  · show (sigDigests s).getD (114 + i) 0 = (layerList s 0).getD i 0
    have hi' : i < 66 := hi
    rw [sigDigests_tail s _ (by omega), show 114 + i - 114 = i by omega, getD_append_left' (by omega)]
  · show (sigDigests s).getD (180 + i) 0 = (layerList s 1).getD i 0
    have hi' : i < 50 := hi
    rw [sigDigests_tail s _ (by omega), getD_append_right' (by omega), l0, getD_append_left' (by omega),
      show 180 + i - 114 - 66 = i by omega]
  · show (sigDigests s).getD (230 + i) 0 = (layerList s 2).getD i 0
    have hi' : i < 49 := hi
    rw [sigDigests_tail s _ (by omega), getD_append_right' (by omega), l0, getD_append_right' (by omega), l1,
      getD_append_left' (by omega), show 230 + i - 114 - 66 - 50 = i by omega]
  · show (sigDigests s).getD (279 + i) 0 = (layerList s 3).getD i 0
    rw [sigDigests_tail s _ (by omega), getD_append_right' (by omega), l0, getD_append_right' (by omega), l1,
      getD_append_right' (by omega), l2, show 279 + i - 114 - 66 - 50 - 49 = i by omega]
theorem sigDigests_layValue (s : SharedSignature) (lay : Layer) (i : Nat) (hi : i < chainCount lay) :
    (sigDigests s).getD (layIdx lay + i) 0 = (s.layers lay).values ⟨i, hi⟩ := by
  rw [sigDigests_layer s lay i (by omega), layerList, getD_append_left' (by simpa using hi), getD_ofFn']
theorem sigDigests_layPath (s : SharedSignature) (lay : Layer) (j : Nat) (hj : j < height lay) :
    (sigDigests s).getD (layIdx lay + (chainCount lay + j)) 0 = (s.layers lay).path ⟨j, hj⟩ := by
  rw [sigDigests_layer s lay _ (by omega), layerList, getD_append_right' (by simp), List.length_ofFn,
    Nat.add_sub_cancel_left, getD_ofFn']

end ClaudeWCT.W9.T3M.SharedCodec


namespace ClaudeWCT.W9.T3M.SharedCodec
/-- Internal expansion retains the four unused seventh A-path slots. -/
def internalFullIndex (k : Nat) : Nat :=
  k + (if 13 ≤ k then 1 else 0) + (if 38 ≤ k then 1 else 0) +
    (if 63 ≤ k then 1 else 0) + (if 88 ≤ k then 1 else 0)
def externalFullIndex (k : Nat) : Nat :=
  k - ((if 13 < k then 1 else 0) + (if 39 < k then 1 else 0) +
    (if 65 < k then 1 else 0) + (if 91 < k then 1 else 0))
def internalDummy (k : Nat) : Bool := decide (k = 13 ∨ k = 39 ∨ k = 65 ∨ k = 91)
theorem internalFullIndex_spec (k : Nat) :
    internalFullIndex k = k + (([13,38,63,88].filter fun skip => decide (skip ≤ k)).length) := by
  by_cases h13 : 13 ≤ k
  · by_cases h38 : 38 ≤ k
    · by_cases h63 : 63 ≤ k
      · by_cases h88 : 88 ≤ k
        · simp [internalFullIndex,h13,h38,h63,h88]
        · simp [internalFullIndex,h13,h38,h63,h88]
      · have h88 : ¬88 ≤ k := by omega
        simp [internalFullIndex,h13,h38,h63,h88]
    · have h63 : ¬63 ≤ k := by omega
      have h88 : ¬88 ≤ k := by omega
      simp [internalFullIndex,h13,h38,h63,h88]
  · have h38 : ¬38 ≤ k := by omega
    have h63 : ¬63 ≤ k := by omega
    have h88 : ¬88 ≤ k := by omega
    simp [internalFullIndex,h13,h38,h63,h88]
theorem internalFullIndex_bound (k : Nat) (hk : k < 328) : internalFullIndex k < 332 := by
  unfold internalFullIndex
  split_ifs <;> omega
theorem internalFullIndex_dummy (k : Nat) : internalDummy (internalFullIndex k) = false := by
  simp only [internalDummy, decide_eq_false_iff_not]
  unfold internalFullIndex
  split_ifs <;> omega
theorem internalFullIndex_inverse (k : Nat) : externalFullIndex (internalFullIndex k) = k := by
  unfold externalFullIndex internalFullIndex
  split_ifs <;> omega
def inflatedRead {α : Type} (zero : α) (read : Nat → α) (k : Nat) : α :=
  if internalDummy k then zero else read (externalFullIndex k)
theorem inflatedRead_internal {α : Type} (zero : α) (read : Nat → α) (k : Nat) :
    inflatedRead zero read (internalFullIndex k) = read k := by
  simp only [inflatedRead, internalFullIndex_dummy, Bool.false_eq_true, ↓reduceIte,
    internalFullIndex_inverse]
theorem internalFullIndex_main (k : Nat) (hk : 114 ≤ k) : internalFullIndex k = k + 4 := by
  unfold internalFullIndex
  rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega)]
theorem internalFullIndex_tail : internalFullIndex 179 = 183 := by rfl
end ClaudeWCT.W9.T3M.SharedCodec

namespace ClaudeWCT.W9.T3M.SharedCodec
open SigGolfCandidate.T3
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

def serializedWord (read : Nat → BitVec 64) (k : Nat) : BitVec 64 :=
  if k < 26 then read k else if k < 28 then 0 else
  if k < 78 then read (k - 2) else if k < 80 then 0 else
  if k < 130 then read (k - 4) else if k < 132 then 0 else
  if k < 182 then read (k - 6) else if k < 184 then 0 else
  if k < 366 then read (k - 8) else if k = 366 then read 654 else
  if k = 367 then (read 655 <<< 16) >>> 16 else read (k - 10)

theorem serializedWord_index (read : Nat → BitVec 64) (k i : Nat) (hi : i < 2) :
    serializedWord read (2*k+i) =
      if internalDummy k then 0 else if k = 183 then
        (if i = 0 then read 654 else (read 655 <<< 16) >>> 16)
      else read (2*(if externalFullIndex k < 179 then externalFullIndex k else externalFullIndex k - 1)+i) := by
  have hi' : i = 0 ∨ i = 1 := by omega
  rcases hi' with rfl | rfl
  all_goals unfold serializedWord internalDummy externalFullIndex
  all_goals split_ifs <;> simp_all only [decide_eq_true_eq, decide_eq_false_iff_not, not_true_eq_false, not_false_eq_true, ↓reduceIte]
  all_goals try (first | rfl | omega | (congr 1 <;> omega))

theorem externalFullIndex_tail_iff (k : Nat) : externalFullIndex k = 179 ↔ k = 183 := by
  unfold externalFullIndex
  split_ifs <;> omega

theorem extract_digest_word {n : Nat} (x : BitVec n) (a i : Nat) (hi : i < 2) :
    (x.extractLsb' a 128).extractLsb' (64*i) 64 = x.extractLsb' (a+64*i) 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and]
  rw [show decide (64*i+j < 128) = true from decide_eq_true (by omega), Bool.true_and]
  congr 1
  omega

theorem tail_low_word (b : CBytes) :
    ((b.extractLsb' (128*327) 112).setWidth 128).extractLsb' 0 64 =
      b.extractLsb' (64*654) 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, Nat.zero_add,
    hj, decide_true, Bool.true_and]
  rw [show decide (j < 128) = true from decide_eq_true (by omega), Bool.true_and,
    show decide (j < 112) = true from decide_eq_true (by omega), Bool.true_and]

theorem tail_high_word (b : CBytes) :
    ((b.extractLsb' (128*327) 112).setWidth 128).extractLsb' 64 64 =
      (b.extractLsb' (64*655) 64 <<< 16) >>> 16 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    hj, decide_true, Bool.true_and]
  by_cases h : j < 48
  · simp only [show decide (64+j < 128) = true from decide_eq_true (by omega),
      show decide (64+j < 112) = true from decide_eq_true (by omega),
      show decide (16+j < 64) = true from decide_eq_true (by omega),
      show decide (16+j < 16) = false from decide_eq_false (by omega),
      Bool.not_false, Bool.true_and, Nat.add_sub_cancel_left, hj, decide_true]
    congr 1
    omega
  · simp only [show decide (64+j < 112) = false from decide_eq_false (by omega),
      show decide (16+j < 64) = false from decide_eq_false (by omega),
      Bool.false_and, Bool.and_false]

theorem serializedWord_digC (b : CBytes) (k i : Nat) (hi : i < 2) :
    serializedWord (fun j => b.extractLsb' (64*j) 64) (2*k+i) =
      (inflatedRead (0 : Digest) (digC b) k).extractLsb' (64*i) 64 := by
  rw [serializedWord_index _ k i hi]
  cases hd : internalDummy k
  · simp only [hd, Bool.false_eq_true, ↓reduceIte, inflatedRead]
    by_cases ht : k = 183
    · subst k
      simp only [if_pos rfl, show externalFullIndex 183 = 179 from rfl, digC,
        show ¬(179 < 179) from by omega, if_neg, if_pos rfl]
      have hi' : i = 0 ∨ i = 1 := by omega
      rcases hi' with rfl | rfl
      · simpa only [Nat.mul_zero, ↓reduceIte] using (tail_low_word b).symm
      · simpa using (tail_high_word b).symm
    · rw [if_neg ht]
      have he : externalFullIndex k ≠ 179 := by
        intro h
        exact ht ((externalFullIndex_tail_iff k).mp h)
      unfold digC
      by_cases hl : externalFullIndex k < 179
      · simp only [if_pos hl, cDig]
        rw [extract_digest_word b _ i hi]
        congr 1
        omega
      · simp only [if_neg hl, if_neg he, cDig]
        rw [extract_digest_word b _ i hi]
        congr 1
        omega
  · simp [hd, inflatedRead]

end ClaudeWCT.W9.T3M.SharedCodec

namespace ClaudeWCT.W9.T3M.SharedCodec
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3M (digNat digNat_lt digNat_digit)
open ClaudeWCT.W9.T3M (getD_eraseIdx mod_digit lt_split split_mod split_div)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 50000

theorem length_eraseIdx_sig (s : SharedSignature) :
    ((sigDigests s).eraseIdx 179).length = 327 := by
  rw [List.length_eraseIdx,sigDigests_length];decide

theorem sigBC_toNat (s : SharedSignature) :
    (sigBC s).toNat = digNat ((sigDigests s).eraseIdx 179) +
      2^(128*327)*(((sigDigests s).getD 179 0).toNat%2^112)+
      2^(8*5246)*s.policyHints.toNat := by
  unfold sigBC
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have hD := digNat_lt ((sigDigests s).eraseIdx 179)
  rw [length_eraseIdx_sig] at hD
  have hT := lt_split _ _ _ _ hD (Nat.mod_lt ((sigDigests s).getD 179 0).toNat (show 0<2^112 by positivity))
  have hx : digNat ((sigDigests s).eraseIdx 179)+
      2^(128*327)*(((sigDigests s).getD 179 0).toNat%2^112)<2^(8*5246) := by
    simpa only [←pow_add] using hT
  have hn := lt_split _ _ _ _ hx s.policyHints.isLt
  simpa only [←pow_add] using hn

theorem encoded_low (s : SharedSignature) :
    (sigBC s).toNat%2^(128*327)=digNat ((sigDigests s).eraseIdx 179) := by
  have hD := digNat_lt ((sigDigests s).eraseIdx 179)
  rw [length_eraseIdx_sig] at hD
  rw [sigBC_toNat,show 2^(8*5246)=2^(128*327)*2^112 by rw [←pow_add]]
  rw [mul_assoc,add_assoc,←mul_add,split_mod _ _ _ hD]

theorem encoded_tail (s : SharedSignature) :
    (sigBC s).toNat/2^(128*327)%2^112=((sigDigests s).getD 179 0).toNat%2^112 := by
  have hD := digNat_lt ((sigDigests s).eraseIdx 179)
  rw [length_eraseIdx_sig] at hD
  rw [sigBC_toNat,show 2^(8*5246)=2^(128*327)*2^112 by rw [←pow_add]]
  rw [mul_assoc,add_assoc,←mul_add,split_div _ _ _ hD,Nat.add_mul_mod_self_left,Nat.mod_mod]

theorem encoded_hints (s : SharedSignature) :
    (sigBC s).toNat/2^(8*5246)=s.policyHints.toNat := by
  have hD := digNat_lt ((sigDigests s).eraseIdx 179)
  rw [length_eraseIdx_sig] at hD
  have hT := lt_split _ _ _ _ hD (Nat.mod_lt ((sigDigests s).getD 179 0).toNat (show 0<2^112 by positivity))
  rw [sigBC_toNat,split_div _ _ _ (by simpa only [←pow_add] using hT)]

theorem cDig_sigBC (s : SharedSignature) (j : Nat) (hj : j<327) :
    cDig (sigBC s) j=((sigDigests s).eraseIdx 179).getD j 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [cDig,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,←digNat_digit]
  rw [←mod_digit _ 327 j hj,encoded_low]

theorem digC_sigBC (s : SharedSignature) (k : Nat) (hk : k<328) :
    digC (sigBC s) k=if k=179 then ClaudeWCT.WCT9.setTop ((sigDigests s).getD k 0) 0
      else (sigDigests s).getD k 0 := by
  by_cases hlt : k<179
  · rw [digC,if_pos hlt,cDig_sigBC s k (by omega),getD_eraseIdx,if_pos hlt,if_neg (by omega)]
  · by_cases he : k=179
    · subst he
      rw [digC,if_neg (by decide),if_pos rfl,if_pos rfl]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,encoded_tail,
        ClaudeWCT.WCT9.setTop_toNat]
      simp only [Nat.zero_mod,Nat.mul_zero,Nat.add_zero]
      apply Nat.mod_eq_of_lt
      exact (Nat.mod_lt _ (by positivity)).trans_le (Nat.pow_le_pow_right (by decide) (by decide))
    · rw [digC,if_neg hlt,if_neg he,cDig_sigBC s (k-1) (by omega),getD_eraseIdx,
        if_neg (by omega),show k-1+1=k by omega,if_neg he]

theorem policyHints_sigDecC_sigBC (s : SharedSignature) :
    (sigDecC (sigBC s)).policyHints=s.policyHints := by
  apply BitVec.eq_of_toNat_eq
  change ((sigBC s).extractLsb' (8*5246) 16).toNat=s.policyHints.toNat
  rw [BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,encoded_hints,Nat.mod_eq_of_lt s.policyHints.isLt]

end ClaudeWCT.W9.T3M.SharedCodec

namespace ClaudeWCT.W9.T3M.SharedCodec
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3M (getD_append_left' getD_append_right' getD_ofFn')
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

theorem forest_sigDecC_sigBC (s : SharedSignature) :
    (sigDecC (sigBC s)).forest=s.forest := by
  have hp : (sigDecC (sigBC s)).forest.pairs=s.forest.pairs := by
    funext p
    have h1 : ((sigDecC (sigBC s)).forest.pairs p).firstValues=(s.forest.pairs p).firstValues := by
      funext i
      change digC (sigBC s) (1+25*p.val+i.val)=_
      rw [digC_sigBC s _ (by omega),if_neg (by omega),sigDigests_pair s p i.val (by omega),pairList_firstValue]
    have h2 : ((sigDecC (sigBC s)).forest.pairs p).firstPath=(s.forest.pairs p).firstPath := by
      funext i
      change digC (sigBC s) (1+25*p.val+6+i.val)=_
      rw [digC_sigBC s _ (by omega),if_neg (by omega),show 1+25*p.val+6+i.val=1+25*p.val+(6+i.val) by omega,
        sigDigests_pair s p (6+i.val) (by omega),pairList_firstPath]
    have h3 : ((sigDecC (sigBC s)).forest.pairs p).secondValues=(s.forest.pairs p).secondValues := by
      funext i
      change digC (sigBC s) (1+25*p.val+12+i.val)=_
      rw [digC_sigBC s _ (by omega),if_neg (by omega),show 1+25*p.val+12+i.val=1+25*p.val+(12+i.val) by omega,
        sigDigests_pair s p (12+i.val) (by omega),pairList_secondValue]
    have h4 : ((sigDecC (sigBC s)).forest.pairs p).secondPath=(s.forest.pairs p).secondPath := by
      funext i
      change digC (sigBC s) (1+25*p.val+18+i.val)=_
      rw [digC_sigBC s _ (by omega),if_neg (by omega),show 1+25*p.val+18+i.val=1+25*p.val+(18+i.val) by omega,
        sigDigests_pair s p (18+i.val) (by omega),pairList_secondPath]
    cases h : (sigDecC (sigBC s)).forest.pairs p
    cases h' : s.forest.pairs p
    simp only [h,h'] at h1 h2 h3 h4
    cases h1;cases h2;cases h3;cases h4;rfl
  have hs : (sigDecC (sigBC s)).forest.singleton=s.forest.singleton := by
    have h1 : (sigDecC (sigBC s)).forest.singleton.values=s.forest.singleton.values := by
      funext i
      change digC (sigBC s) (101+i.val)=_
      rw [digC_sigBC s _ (by omega),if_neg (by omega),sigDigests_singleton s i.val (by omega),singletonList,
        getD_append_left' (by simp),getD_ofFn']
    have h2 : (sigDecC (sigBC s)).forest.singleton.path=s.forest.singleton.path := by
      funext i
      change digC (sigBC s) (107+i.val)=_
      rw [digC_sigBC s _ (by omega),if_neg (by omega),show 107+i.val=101+(6+i.val) by omega,
        sigDigests_singleton s (6+i.val) (by omega),singletonList,getD_append_right' (by simp),
        List.length_ofFn,Nat.add_sub_cancel_left,getD_ofFn']
    cases h : (sigDecC (sigBC s)).forest.singleton
    cases h' : s.forest.singleton
    simp only [h,h'] at h1 h2
    cases h1;cases h2;rfl
  cases h : (sigDecC (sigBC s)).forest
  cases h' : s.forest
  simp only [h,h'] at hp hs
  cases hp;cases hs;rfl

theorem sigDecC_sigBC (s : SharedSignature) :
    sigDecC (sigBC s)=fillTopSignature s 0 := by
  have hr : (sigDecC (sigBC s)).rho=s.rho := by
    change digC (sigBC s) 0=s.rho
    rw [digC_sigBC s 0 (by decide),if_neg (by decide),sigDigests_rho]
  have hh := policyHints_sigDecC_sigBC s
  have hf := forest_sigDecC_sigBC s
  have hl : (sigDecC (sigBC s)).layers=(fillTopSignature s 0).layers := by
    funext lay
    have hc : layIdx lay+chainCount lay≤328 := by fin_cases lay <;> decide
    have hp : layIdx lay+chainCount lay+height lay≤328 := by fin_cases lay <;> decide
    have hv : ((sigDecC (sigBC s)).layers lay).values=((fillTopSignature s 0).layers lay).values := by
      funext i
      change digC (sigBC s) (layIdx lay+i.val)=(s.layers lay).values i
      have hn : layIdx lay+i.val≠179 := by
        fin_cases lay <;> simp [layIdx,chainCount] at * <;> omega
      rw [digC_sigBC s _ (by omega),if_neg hn,sigDigests_layValue]
    have hpath : ((sigDecC (sigBC s)).layers lay).path=((fillTopSignature s 0).layers lay).path := by
      funext i
      change digC (sigBC s) (layIdx lay+chainCount lay+i.val)=(ClaudeWCT.WCT9.fillLayer lay (s.layers lay) 0).path i
      have he : layIdx lay+(chainCount lay+i.val)=179 ↔ lay.val=0 ∧ i.val=11 := by
        fin_cases lay <;> simp [layIdx,chainCount] at * <;> omega
      rw [show layIdx lay+chainCount lay+i.val=layIdx lay+(chainCount lay+i.val) by omega,
        digC_sigBC s _ (by omega)]
      rw [sigDigests_layPath s lay i.val i.isLt]
      simp only [he,ClaudeWCT.WCT9.fillLayer]
    cases h : (sigDecC (sigBC s)).layers lay
    cases h' : (fillTopSignature s 0).layers lay
    simp only [h,h'] at hv hpath
    cases hv;cases hpath;rfl
  have hf' : (sigDecC (sigBC s)).forest=(fillTopSignature s 0).forest := hf
  have hr' : (sigDecC (sigBC s)).rho=(fillTopSignature s 0).rho := hr
  have hh' : (sigDecC (sigBC s)).policyHints=(fillTopSignature s 0).policyHints := hh
  cases h : sigDecC (sigBC s)
  cases h' : fillTopSignature s 0
  simp only [h,h'] at hr' hh' hf' hl
  cases hr';cases hh';cases hf';cases hl;rfl

end ClaudeWCT.W9.T3M.SharedCodec

namespace ClaudeWCT.W9.T3M.SharedCodec
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3M (digNat digNat_eq_of_digits getD_append_left' getD_append_right' getD_ofFn'
 chainCount_0 chainCount_1 chainCount_2 chainCount_3 height_0 height_1 height_2 height_3)
open ClaudeWCT.W9.T3M (getD_eraseIdx mod_digit)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 50000

theorem sigDigests_sigDecC (b : CBytes) (k : Nat) (hk : k<328) :
    (sigDigests (sigDecC b)).getD k 0=digC b k := by
  by_cases h0:k=0
  · subst h0;exact sigDigests_rho _
  by_cases hp:k<101
  · have hq:(k-1)/25<4:=by omega
    let p : Fin 4:=⟨(k-1)/25,hq⟩
    let j : Nat:=(k-1)%25
    have hj:j<25:=Nat.mod_lt _ (by decide)
    have he:k=1+25*p.val+j:=by dsimp [p,j];omega
    rw [he,sigDigests_pair _ p j hj]
    by_cases h1:j<6
    · rw [pairList_firstValue _ ⟨j,h1⟩]
      change digC b _=digC b _
      congr 1 <;> simp only [Fin.val_mk] <;> omega
    · by_cases h2:j<12
      · rw [show j=6+(j-6) by omega,pairList_firstPath _ ⟨j-6,by omega⟩]
        change digC b _=digC b _
        congr 1 <;> simp only [Fin.val_mk] <;> omega
      · by_cases h3:j<18
        · rw [show j=12+(j-12) by omega,pairList_secondValue _ ⟨j-12,by omega⟩]
          change digC b _=digC b _
          congr 1 <;> simp only [Fin.val_mk] <;> omega
        · rw [show j=18+(j-18) by omega,pairList_secondPath _ ⟨j-18,by omega⟩]
          change digC b _=digC b _
          congr 1 <;> simp only [Fin.val_mk] <;> omega
  by_cases hs:k<114
  · have he:k=101+(k-101):=by omega
    rw [he,sigDigests_singleton _ (k-101) (by omega)]
    by_cases h1:k-101<6
    · unfold singletonList
      rw [getD_append_left' (by simp;omega),getD_ofFn' _ (k-101) h1]
      change digC b _=digC b _
      congr 1 <;> simp only [Fin.val_mk] <;> omega
    · unfold singletonList
      rw [getD_append_right' (by simp;omega),List.length_ofFn,getD_ofFn' _ ((k-101)-6) (by omega)]
      change digC b _=digC b _
      congr 1 <;> simp only [Fin.val_mk] <;> omega
  have key:∀ (lay:Layer) (i:Nat),i<chainCount lay+height lay→layIdx lay+i=k→
      (sigDigests (sigDecC b)).getD k 0=digC b k := by
    intro lay i hi he
    subst he
    rw [sigDigests_layer _ lay i hi]
    unfold layerList
    by_cases hc:i<chainCount lay
    · rw [getD_append_left' (by simpa using hc),getD_ofFn' _ i hc];rfl
    · rw [getD_append_right' (by simp;omega),List.length_ofFn,getD_ofFn' _ (i-chainCount lay) (by omega)]
      change digC b (layIdx lay+chainCount lay+(i-chainCount lay))=_
      congr 1;omega
  by_cases h1:k<180
  · exact key 0 (k-114) (by rw [chainCount_0,height_0];omega) (by simp [layIdx];omega)
  by_cases h2:k<230
  · exact key 1 (k-180) (by rw [chainCount_1,height_1];omega) (by simp [layIdx];omega)
  by_cases h3:k<279
  · exact key 2 (k-230) (by rw [chainCount_2,height_2];omega) (by simp [layIdx];omega)
  · exact key 3 (k-279) (by rw [chainCount_3,height_3];omega) (by simp [layIdx];omega)

theorem sigBC_sigDecC (b : CBytes) : sigBC (sigDecC b)=b := by
  apply BitVec.eq_of_toNat_eq
  rw [sigBC_toNat]
  have hD : digNat ((sigDigests (sigDecC b)).eraseIdx 179)=b.toNat%2^(128*327) := by
    apply digNat_eq_of_digits
    · rw [length_eraseIdx_sig];exact Nat.mod_lt _ (by positivity)
    · intro k hk
      rw [length_eraseIdx_sig] at hk
      rw [getD_eraseIdx,mod_digit _ 327 k hk]
      split
      · rename_i hlt
        rw [sigDigests_sigDecC b k (by omega),digC,if_pos hlt,cDig,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow]
      · rename_i hge
        rw [sigDigests_sigDecC b (k+1) (by omega),digC,if_neg (by omega),if_neg (by omega),
          show k+1-1=k by omega,cDig,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow]
  have hT : ((sigDigests (sigDecC b)).getD 179 0).toNat%2^112=b.toNat/2^(128*327)%2^112 := by
    rw [sigDigests_sigDecC b 179 (by decide),digC,if_neg (by decide),if_pos rfl,
      BitVec.toNat_setWidth,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,Nat.mod_mod_of_dvd]
    · exact Nat.mod_mod _ _
    · exact Nat.pow_dvd_pow 2 (by decide)
  have hH : (sigDecC b).policyHints.toNat=b.toNat/2^(8*5246) := by
    change (b.extractLsb' (8*5246) 16).toNat=_
    rw [BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,Nat.mod_eq_of_lt]
    rw [Nat.div_lt_iff_lt_mul (by positivity),←pow_add]
    exact b.isLt
  rw [hD,hT,hH]
  have he : b.toNat/2^(8*5246)=b.toNat/2^(128*327)/2^112 := by
    rw [Nat.div_div_eq_div_mul,←pow_add]
  rw [he,show 2^(8*5246)=2^(128*327)*2^112 by rw [←pow_add]]
  calc
    _=b.toNat%2^(128*327)+2^(128*327)*(b.toNat/2^(128*327)%2^112+
        2^112*(b.toNat/2^(128*327)/2^112)):=by ring
    _=b.toNat%2^(128*327)+2^(128*327)*(b.toNat/2^(128*327)):=by rw [Nat.mod_add_div]
    _=b.toNat:=Nat.mod_add_div _ _
end ClaudeWCT.W9.T3M.SharedCodec

namespace ClaudeWCT.W9.T3M.SharedCodec
open SigGolfCandidate.Research.SharedForest

theorem sigBC_fillTopSignature (sig : SharedSignature) (c : Nat) :
    sigBC (fillTopSignature sig c) = sigBC sig := by
  calc
    sigBC (fillTopSignature sig c) = sigBC (sigDecC (sigBC (fillTopSignature sig c))) :=
      (sigBC_sigDecC _).symm
    _ = sigBC (fillTopSignature (fillTopSignature sig c) 0) := by rw [sigDecC_sigBC]
    _ = sigBC (fillTopSignature sig 0) := by rw [fillTopSignature_fillTopSignature]
    _ = sigBC (sigDecC (sigBC sig)) := by rw [sigDecC_sigBC]
    _ = sigBC sig := sigBC_sigDecC _

end ClaudeWCT.W9.T3M.SharedCodec
