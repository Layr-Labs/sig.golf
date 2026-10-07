import Mathlib.Tactic
import Mathlib.Data.List.GetD

namespace ClaudeWCT.WCT9
def compositions (width : Nat) : Nat → Nat → List (List Nat)
  | 0, total => if total = 0 then [[]] else []
  | parts + 1, total =>
    (List.range (min width (total + 1))).flatMap fun x =>
      (compositions width parts (total - x)).map (x :: ·)
theorem mem_compositions {width parts total : Nat} {xs : List Nat}
    (h : xs ∈ compositions width parts total) :
    xs.length = parts ∧ xs.sum = total ∧ ∀ x ∈ xs, x < width := by
  induction parts generalizing total xs with
  | zero =>
      simp only [compositions] at h
      split_ifs at h with ht
      · simp only [List.mem_singleton] at h
        subst xs
        simp [ht]
      · simp at h
  | succ parts ih =>
      simp only [compositions, List.mem_flatMap, List.mem_range, List.mem_map] at h
      obtain ⟨x, hx, ys, hy, rfl⟩ := h
      obtain ⟨hlen, hsum, hbound⟩ := ih hy
      have hxw : x < width := lt_of_lt_of_le hx (Nat.min_le_left _ _)
      have hxt : x < total + 1 := lt_of_lt_of_le hx (Nat.min_le_right _ _)
      refine ⟨by simp [hlen], by simp [hsum]; omega, ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hxw
      · exact hbound y hy
theorem compositions_nodup (width parts total : Nat) :
    (compositions width parts total).Nodup := by
  induction parts generalizing total with
  | zero => simp [compositions]; split_ifs <;> simp
  | succ parts ih =>
      rw [compositions, List.nodup_flatMap]
      refine ⟨fun x _ => (ih (total - x)).map (fun xs ys h => (List.cons.inj h).2), ?_⟩
      exact List.nodup_range.imp fun {x y} hne zs hx hy => by
        obtain ⟨xs, _, rfl⟩ := List.mem_map.mp hx
        obtain ⟨ys, _, he⟩ := List.mem_map.mp hy
        exact hne (List.cons.inj he).1.symm
theorem valid_mem {width parts total : Nat} {values : List Nat}
    (hlen : values.length = parts) (hsum : values.sum = total)
    (hbound : ∀ value ∈ values, value < width) : values ∈ compositions width parts total := by
  induction parts generalizing total values with
  | zero =>
      have hv : values = [] := List.length_eq_zero_iff.mp hlen
      subst values
      simp only [List.sum_nil] at hsum
      simp [compositions, ← hsum]
  | succ parts ih =>
      cases values with
      | nil => simp at hlen
      | cons value rest =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          have hs : value + rest.sum = total := hsum
          have hv := hbound value (by simp)
          have hx : value < min width (total + 1) := by omega
          apply List.mem_flatMap.mpr
          refine ⟨value, List.mem_range.mpr hx, ?_⟩
          apply List.mem_map.mpr
          refine ⟨rest, ?_, rfl⟩
          apply ih hlen (by omega)
          intro x hx
          exact hbound x (List.mem_cons_of_mem _ hx)
theorem mem_compositions_iff {width parts total : Nat} {xs : List Nat} :
    xs ∈ compositions width parts total ↔
      xs.length = parts ∧ xs.sum = total ∧ ∀ x ∈ xs, x < width :=
  ⟨mem_compositions, fun ⟨hlen, hsum, hbound⟩ => valid_mem hlen hsum hbound⟩
theorem compositions_lex (width parts total : Nat) :
    (compositions width parts total).Pairwise (List.Lex (· < ·)) := by
  induction parts generalizing total with
  | zero =>
      simp only [compositions]
      split_ifs <;> simp
  | succ parts ih =>
      rw [compositions, List.pairwise_flatMap]
      refine ⟨fun x _ => (ih (total - x)).map _ (fun xs ys h => List.Lex.cons h), ?_⟩
      refine List.pairwise_lt_range.imp_of_mem ?_
      intro x y _ _ hxy xs hx ys hy
      obtain ⟨xs', _, rfl⟩ := List.mem_map.mp hx
      obtain ⟨ys', _, rfl⟩ := List.mem_map.mp hy
      exact List.Lex.rel hxy
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem codebook_card : (compositions 4 7 6).length = 728 := by decide
def codeword (rank : Fin 728) : List Nat :=
  (compositions 4 7 6)[rank.val]'(by rw [codebook_card]; exact rank.isLt)
def digit (rank : Fin 728) (chain : Fin 7) : Nat :=
  (codeword rank).getD chain.val 0
theorem codeword_valid (rank : Fin 728) :
    (codeword rank).length = 7 ∧ (codeword rank).sum = 6 ∧
      ∀ value ∈ codeword rank, value < 4 :=
  mem_compositions (List.getElem_mem _)
theorem codeword_injective : Function.Injective codeword := by
  intro left right he
  apply Fin.ext
  exact (compositions_nodup 4 7 6).getElem_inj_iff.mp he
theorem codeword_mem (rank : Fin 728) : codeword rank ∈ compositions 4 7 6 :=
  List.getElem_mem _
theorem codeword_surjective {values : List Nat} (hlen : values.length = 7)
    (hsum : values.sum = 6) (hbound : ∀ value ∈ values, value < 4) :
    ∃ rank : Fin 728, codeword rank = values := by
  have hm := valid_mem hlen hsum hbound
  obtain ⟨n, hn, he⟩ := List.mem_iff_getElem.mp hm
  exact ⟨⟨n, by rwa [codebook_card] at hn⟩, he⟩
set_option maxRecDepth 100000 in
theorem codeword_zero : codeword 0 = [0, 0, 0, 0, 0, 3, 3] := by decide +kernel
set_option maxRecDepth 100000 in
theorem codeword_one : codeword 1 = [0, 0, 0, 0, 1, 2, 3] := by decide +kernel
set_option maxRecDepth 100000 in
theorem codeword_last : codeword 727 = [3, 3, 0, 0, 0, 0, 0] := by decide +kernel
theorem digit_lt (rank : Fin 728) (chain : Fin 7) : digit rank chain < 4 := by
  have hi : chain.val < (codeword rank).length := by
    rw [(codeword_valid rank).1]
    exact chain.isLt
  rw [digit, List.getD_eq_getElem _ _ hi]
  exact (codeword_valid rank).2.2 _ (List.getElem_mem hi)
theorem digit_le_three (rank : Fin 728) (chain : Fin 7) : digit rank chain ≤ 3 := by
  have := digit_lt rank chain
  omega
theorem ofFn_digit (rank : Fin 728) :
    List.ofFn (fun chain : Fin 7 => digit rank chain) = codeword rank := by
  apply List.ext_getElem
  · simp [(codeword_valid rank).1]
  · intro i hi hj
    simp only [List.getElem_ofFn, digit, List.getD_eq_getElem _ _ hj]
theorem step_count (rank : Fin 728) : (∑ chain : Fin 7, digit rank chain) = 6 := by
  rw [← List.sum_ofFn, ofFn_digit, (codeword_valid rank).2.1]
theorem revealed_count (rank : Fin 728) : (∑ chain : Fin 7, (3 - digit rank chain)) = 15 := by
  have h := step_count rank
  have hle := digit_le_three rank
  have hsum : (∑ chain : Fin 7, (3 - digit rank chain)) + (∑ chain : Fin 7, digit rank chain) =
      ∑ _chain : Fin 7, 3 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun chain _ => Nat.sub_add_cancel (hle chain))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  omega
abbrev Encoding := Fin 7 → Fin 4
abbrev ValidEncoding := {values : Encoding // (∑ chain, (values chain).val) = 6}
def encode (rank : Fin 728) : ValidEncoding :=
  ⟨fun chain => ⟨digit rank chain, digit_lt rank chain⟩, step_count rank⟩
theorem encode_injective : Function.Injective encode := by
  intro left right he
  apply codeword_injective
  apply List.ext_getElem
  · rw [(codeword_valid left).1, (codeword_valid right).1]
  · intro i hi hj
    have hi7 : i < 7 := by rwa [(codeword_valid left).1] at hi
    have hd := congrArg (fun value : ValidEncoding => (value.val ⟨i, hi7⟩).val) he
    simpa only [encode, digit, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] using hd
theorem encode_surjective : Function.Surjective encode := by
  intro values
  let xs := List.ofFn fun chain : Fin 7 => (values.val chain).val
  have hlen : xs.length = 7 := List.length_ofFn
  have hsum : xs.sum = 6 := by rw [List.sum_ofFn]; exact values.property
  have hbound : ∀ value ∈ xs, value < 4 := by
    intro value hv
    obtain ⟨chain, rfl⟩ := List.mem_ofFn.mp hv
    exact (values.val chain).isLt
  obtain ⟨rank, hr⟩ := codeword_surjective hlen hsum hbound
  refine ⟨rank, ?_⟩
  apply Subtype.ext
  funext chain
  apply Fin.ext
  change digit rank chain = (values.val chain).val
  rw [digit, hr, List.getD_eq_getElem _ _ (by rw [hlen]; exact chain.isLt)]
  exact List.getElem_ofFn _
theorem encode_bijective : Function.Bijective encode :=
  ⟨encode_injective, encode_surjective⟩
noncomputable def equivalence : Fin 728 ≃ ValidEncoding :=
  Equiv.ofBijective encode encode_bijective
theorem validEncoding_card : Fintype.card ValidEncoding = 728 := by
  rw [← Fintype.card_fin 728]
  exact (Fintype.card_congr equivalence).symm
theorem antichain (left right : Fin 728)
    (h : ∀ chain, digit left chain ≤ digit right chain) : left = right := by
  have hsum : (∑ chain, digit left chain) = ∑ chain, digit right chain := by
    rw [step_count, step_count]
  have he := (Finset.sum_eq_sum_iff_of_le (fun chain _ => h chain)).mp hsum
  apply encode_injective
  apply Subtype.ext
  funext chain
  apply Fin.ext
  exact he chain (Finset.mem_univ chain)
def codeRanks : List Nat :=
  [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,62,63,65,66,67,68,69,70,71,72,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,149,150,153,154,156,157,158,159,160,161,162,165,166,168,169,170,171,172,173,174,175,176,177,178,181,182,184,185,186,187,190,196,197,199,202,203,204,205,206,207,208,209,210,212,213,214,215,216,218,221,222,223,224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,252,254,255,256,257,258,259,260,261,262,263,264,265,266,267,268,269,270,273,274,276,277,279,282,283,284,285,286,287,288,289,290,291,292,293,295,296,297,298,299,300,301,302,303,304,305,306,307,308,309,310,311,312,313,314,315,316,317,318,319,320,321,322,323,324,325,326,327,328,329,330,331,332,333,334,335,336,337,338,339,340,341,342,343,344,345,346,347,348,349,350,351,354,355,357,358,359,360,361,362,363,364,366,367,368,369,370,371,372,373,374,375,376,377,378,379,382,383,385,386,387,388,391,397,398,400,403,404,405,406,407,408,409,410,411,413,414,415,416,417,419,422,423,424,425,426,427,428,429,430,431,432,433,434,435,436,437,438,439,440,443,444,446,447,448,449,458,459,464,465,467,468,471,477,487,488,490,493,497,498,499,500,501,502,503,504,505,506,508,509,510,511,512,517,518,520,521,522,524,527,531,532,533,534,535,536,537,538,539,540,541,542,543,545,546,547,548,549,550,551,552,553,554,555,556,557,558,559,560,561,562,563,564,565,566,567,568,570,571,572,573,574,575,576,577,578,579,580,581,582,583,584,585,586,587,589,590,591,592,593,595,598,599,600,601,602,603,604,605,606,607,608,609,610,611,612,613,614,615,616,617,618,619,620,621,623,624,625,626,627,632,633,635,636,637,639,642,646,647,648,649,650,651,652,653,654,655,656,657,658,660,661,662,663,664,665,666,667,668,669,670,671,672,673,674,675,676,677,678,679,680,681,682,683,684,685,686,687,688,689,690,691,692,693,694,695,696,697,698,699,700,701,702,703,704,705,706,707,708,709,710,711,712,713,715,716,717,718,719,720,721,722,723,724,725,726,727]
def codeWords : List (List Nat) :=[[0,0,0,0,0,3,3],[0,0,0,0,1,2,3],[0,0,0,0,1,3,2],[0,0,0,0,2,1,3],[0,0,0,0,2,2,2],[0,0,0,0,2,3,1],[0,0,0,0,3,0,3],[0,0,0,0,3,1,2],[0,0,0,0,3,2,1],[0,0,0,0,3,3,0],[0,0,0,1,0,2,3],[0,0,0,1,0,3,2],[0,0,0,1,1,1,3],[0,0,0,1,1,2,2],[0,0,0,1,1,3,1],[0,0,0,1,2,0,3],[0,0,0,1,2,1,2],[0,0,0,1,2,2,1],[0,0,0,1,2,3,0],[0,0,0,1,3,0,2],[0,0,0,1,3,1,1],[0,0,0,1,3,2,0],[0,0,0,2,0,1,3],[0,0,0,2,0,2,2],[0,0,0,2,0,3,1],[0,0,0,2,1,0,3],[0,0,0,2,1,1,2],[0,0,0,2,1,2,1],[0,0,0,2,1,3,0],[0,0,0,2,2,0,2],[0,0,0,2,2,1,1],[0,0,0,2,2,2,0],[0,0,0,2,3,0,1],[0,0,0,2,3,1,0],[0,0,0,3,0,0,3],[0,0,0,3,0,1,2],[0,0,0,3,0,2,1],[0,0,0,3,0,3,0],[0,0,0,3,1,0,2],[0,0,0,3,1,1,1],[0,0,0,3,1,2,0],[0,0,0,3,2,0,1],[0,0,0,3,2,1,0],[0,0,0,3,3,0,0],[0,0,1,0,0,2,3],[0,0,1,0,0,3,2],[0,0,1,0,1,1,3],[0,0,1,0,1,2,2],[0,0,1,0,1,3,1],[0,0,1,0,2,0,3],[0,0,1,0,2,1,2],[0,0,1,0,2,2,1],[0,0,1,0,2,3,0],[0,0,1,0,3,0,2],[0,0,1,0,3,1,1],[0,0,1,0,3,2,0],[0,0,1,1,0,1,3],[0,0,1,1,0,2,2],[0,0,1,1,0,3,1],[0,0,1,1,1,0,3],[0,0,1,1,1,3,0],[0,0,1,1,2,0,2],[0,0,1,1,2,2,0],[0,0,1,1,3,0,1],[0,0,1,1,3,1,0],[0,0,1,2,0,0,3],[0,0,1,2,0,1,2],[0,0,1,2,0,2,1],[0,0,1,2,0,3,0],[0,0,1,2,1,0,2],[0,0,1,2,1,2,0],[0,0,1,2,2,0,1],[0,0,1,2,2,1,0],[0,0,1,2,3,0,0],[0,0,1,3,0,0,2],[0,0,1,3,0,1,1],[0,0,1,3,0,2,0],[0,0,1,3,1,0,1],[0,0,1,3,1,1,0],[0,0,1,3,2,0,0],[0,0,2,0,0,1,3],[0,0,2,0,0,2,2],[0,0,2,0,0,3,1],[0,0,2,0,1,0,3],[0,0,2,0,1,1,2],[0,0,2,0,1,2,1],[0,0,2,0,1,3,0],[0,0,2,0,2,0,2],[0,0,2,0,2,1,1],[0,0,2,0,2,2,0],[0,0,2,0,3,0,1],[0,0,2,0,3,1,0],[0,0,2,1,0,0,3],[0,0,2,1,0,1,2],[0,0,2,1,0,2,1],[0,0,2,1,0,3,0],[0,0,2,1,1,0,2],[0,0,2,1,1,2,0],[0,0,2,1,2,0,1],[0,0,2,1,2,1,0],[0,0,2,1,3,0,0],[0,0,2,2,0,0,2],[0,0,2,2,0,1,1],[0,0,2,2,0,2,0],[0,0,2,2,1,0,1],[0,0,2,2,1,1,0],[0,0,2,2,2,0,0],[0,0,2,3,0,0,1],[0,0,2,3,0,1,0],[0,0,2,3,1,0,0],[0,0,3,0,0,0,3],[0,0,3,0,0,1,2],[0,0,3,0,0,2,1],[0,0,3,0,0,3,0],[0,0,3,0,1,0,2],[0,0,3,0,1,1,1],[0,0,3,0,1,2,0],[0,0,3,0,2,0,1],[0,0,3,0,2,1,0],[0,0,3,0,3,0,0],[0,0,3,1,0,0,2],[0,0,3,1,0,1,1],[0,0,3,1,0,2,0],[0,0,3,1,1,0,1],[0,0,3,1,1,1,0],[0,0,3,1,2,0,0],[0,0,3,2,0,0,1],[0,0,3,2,0,1,0],[0,0,3,2,1,0,0],[0,0,3,3,0,0,0],[0,1,0,0,0,2,3],[0,1,0,0,0,3,2],[0,1,0,0,1,1,3],[0,1,0,0,1,2,2],[0,1,0,0,1,3,1],[0,1,0,0,2,0,3],[0,1,0,0,2,1,2],[0,1,0,0,2,2,1],[0,1,0,0,2,3,0],[0,1,0,0,3,0,2],[0,1,0,0,3,1,1],[0,1,0,0,3,2,0],[0,1,0,1,0,1,3],[0,1,0,1,0,3,1],[0,1,0,1,1,0,3],[0,1,0,1,1,3,0],[0,1,0,1,2,0,2],[0,1,0,1,2,2,0],[0,1,0,1,3,0,1],[0,1,0,1,3,1,0],[0,1,0,2,0,0,3],[0,1,0,2,0,1,2],[0,1,0,2,0,2,1],[0,1,0,2,0,3,0],[0,1,0,2,1,2,0],[0,1,0,2,2,0,1],[0,1,0,2,3,0,0],[0,1,0,3,0,0,2],[0,1,0,3,0,1,1],[0,1,0,3,0,2,0],[0,1,0,3,1,0,1],[0,1,0,3,1,1,0],[0,1,0,3,2,0,0],[0,1,1,0,0,1,3],[0,1,1,0,0,2,2],[0,1,1,0,0,3,1],[0,1,1,0,1,0,3],[0,1,1,0,1,3,0],[0,1,1,0,2,0,2],[0,1,1,0,2,2,0],[0,1,1,0,3,0,1],[0,1,1,0,3,1,0],[0,1,1,1,0,0,3],[0,1,1,1,0,3,0],[0,1,1,1,3,0,0],[0,1,1,2,0,0,2],[0,1,1,2,0,2,0],[0,1,1,2,2,0,0],[0,1,1,3,0,0,1],[0,1,1,3,0,1,0],[0,1,1,3,1,0,0],[0,1,2,0,0,0,3],[0,1,2,0,0,1,2],[0,1,2,0,0,2,1],[0,1,2,0,0,3,0],[0,1,2,0,1,0,2],[0,1,2,0,1,2,0],[0,1,2,0,2,0,1],[0,1,2,0,2,1,0],[0,1,2,0,3,0,0],[0,1,2,1,0,0,2],[0,1,2,1,0,2,0],[0,1,2,1,2,0,0],[0,1,2,2,0,0,1],[0,1,2,2,0,1,0],[0,1,2,2,1,0,0],[0,1,2,3,0,0,0],[0,1,3,0,0,0,2],[0,1,3,0,0,1,1],[0,1,3,0,0,2,0],[0,1,3,0,1,0,1],[0,1,3,0,1,1,0],[0,1,3,0,2,0,0],[0,1,3,1,0,0,1],[0,1,3,1,0,1,0],[0,1,3,1,1,0,0],[0,1,3,2,0,0,0],[0,2,0,0,0,1,3],[0,2,0,0,0,2,2],[0,2,0,0,0,3,1],[0,2,0,0,1,0,3],[0,2,0,0,1,1,2],[0,2,0,0,1,2,1],[0,2,0,0,1,3,0],[0,2,0,0,2,0,2],[0,2,0,0,2,1,1],[0,2,0,0,2,2,0],[0,2,0,0,3,0,1],[0,2,0,0,3,1,0],[0,2,0,1,0,0,3],[0,2,0,1,0,1,2],[0,2,0,1,0,2,1],[0,2,0,1,0,3,0],[0,2,0,1,1,0,2],[0,2,0,1,1,2,0],[0,2,0,1,2,0,1],[0,2,0,1,2,1,0],[0,2,0,1,3,0,0],[0,2,0,2,0,0,2],[0,2,0,2,0,1,1],[0,2,0,2,0,2,0],[0,2,0,2,1,0,1],[0,2,0,2,1,1,0],[0,2,0,2,2,0,0],[0,2,0,3,0,0,1],[0,2,0,3,0,1,0],[0,2,0,3,1,0,0],[0,2,1,0,0,0,3],[0,2,1,0,0,1,2],[0,2,1,0,0,2,1],[0,2,1,0,0,3,0],[0,2,1,0,1,2,0],[0,2,1,0,2,0,1],[0,2,1,0,3,0,0],[0,2,1,1,0,0,2],[0,2,1,1,0,2,0],[0,2,1,1,2,0,0],[0,2,1,2,0,0,1],[0,2,1,2,0,1,0],[0,2,1,2,1,0,0],[0,2,1,3,0,0,0],[0,2,2,0,0,0,2],[0,2,2,0,0,1,1],[0,2,2,0,0,2,0],[0,2,2,0,1,0,1],[0,2,2,0,1,1,0],[0,2,2,0,2,0,0],[0,2,2,1,0,0,1],[0,2,2,1,1,0,0],[0,2,2,2,0,0,0],[0,2,3,0,0,0,1],[0,2,3,0,0,1,0],[0,2,3,0,1,0,0],[0,2,3,1,0,0,0],[0,3,0,0,0,0,3],[0,3,0,0,0,1,2],[0,3,0,0,0,2,1],[0,3,0,0,0,3,0],[0,3,0,0,1,0,2],[0,3,0,0,1,1,1],[0,3,0,0,1,2,0],[0,3,0,0,2,0,1],[0,3,0,0,2,1,0],[0,3,0,0,3,0,0],[0,3,0,1,0,0,2],[0,3,0,1,0,1,1],[0,3,0,1,0,2,0],[0,3,0,1,1,0,1],[0,3,0,1,1,1,0],[0,3,0,1,2,0,0],[0,3,0,2,0,0,1],[0,3,0,2,0,1,0],[0,3,0,2,1,0,0],[0,3,0,3,0,0,0],[0,3,1,0,0,0,2],[0,3,1,0,0,1,1],[0,3,1,0,0,2,0],[0,3,1,0,1,0,1],[0,3,1,0,1,1,0],[0,3,1,0,2,0,0],[0,3,1,1,0,0,1],[0,3,1,1,0,1,0],[0,3,1,1,1,0,0],[0,3,1,2,0,0,0],[0,3,2,0,0,0,1],[0,3,2,0,0,1,0],[0,3,2,0,1,0,0],[0,3,2,1,0,0,0],[0,3,3,0,0,0,0],[1,0,0,0,0,2,3],[1,0,0,0,0,3,2],[1,0,0,0,1,1,3],[1,0,0,0,1,2,2],[1,0,0,0,1,3,1],[1,0,0,0,2,0,3],[1,0,0,0,2,1,2],[1,0,0,0,2,2,1],[1,0,0,0,2,3,0],[1,0,0,0,3,0,2],[1,0,0,0,3,1,1],[1,0,0,0,3,2,0],[1,0,0,1,0,1,3],[1,0,0,1,0,2,2],[1,0,0,1,0,3,1],[1,0,0,1,1,0,3],[1,0,0,1,1,3,0],[1,0,0,1,2,0,2],[1,0,0,1,2,2,0],[1,0,0,1,3,0,1],[1,0,0,1,3,1,0],[1,0,0,2,0,0,3],[1,0,0,2,0,1,2],[1,0,0,2,0,2,1],[1,0,0,2,0,3,0],[1,0,0,2,1,0,2],[1,0,0,2,1,2,0],[1,0,0,2,2,0,1],[1,0,0,2,2,1,0],[1,0,0,2,3,0,0],[1,0,0,3,0,0,2],[1,0,0,3,0,1,1],[1,0,0,3,0,2,0],[1,0,0,3,1,0,1],[1,0,0,3,1,1,0],[1,0,0,3,2,0,0],[1,0,1,0,0,1,3],[1,0,1,0,0,2,2],[1,0,1,0,0,3,1],[1,0,1,0,1,0,3],[1,0,1,0,1,3,0],[1,0,1,0,2,0,2],[1,0,1,0,2,2,0],[1,0,1,0,3,0,1],[1,0,1,0,3,1,0],[1,0,1,1,0,0,3],[1,0,1,1,0,3,0],[1,0,1,1,3,0,0],[1,0,1,2,0,0,2],[1,0,1,2,0,2,0],[1,0,1,2,2,0,0],[1,0,1,3,0,0,1],[1,0,1,3,0,1,0],[1,0,1,3,1,0,0],[1,0,2,0,0,0,3],[1,0,2,0,0,1,2],[1,0,2,0,0,2,1],[1,0,2,0,0,3,0],[1,0,2,0,1,0,2],[1,0,2,0,1,2,0],[1,0,2,0,2,0,1],[1,0,2,0,2,1,0],[1,0,2,0,3,0,0],[1,0,2,1,0,0,2],[1,0,2,1,0,2,0],[1,0,2,1,2,0,0],[1,0,2,2,0,0,1],[1,0,2,2,0,1,0],[1,0,2,2,1,0,0],[1,0,2,3,0,0,0],[1,0,3,0,0,0,2],[1,0,3,0,0,1,1],[1,0,3,0,0,2,0],[1,0,3,0,1,0,1],[1,0,3,0,1,1,0],[1,0,3,0,2,0,0],[1,0,3,1,0,0,1],[1,0,3,1,0,1,0],[1,0,3,1,1,0,0],[1,0,3,2,0,0,0],[1,1,0,0,0,1,3],[1,1,0,0,0,2,2],[1,1,0,0,0,3,1],[1,1,0,0,1,0,3],[1,1,0,0,1,3,0],[1,1,0,0,2,0,2],[1,1,0,0,2,2,0],[1,1,0,0,3,0,1],[1,1,0,0,3,1,0],[1,1,0,1,0,0,3],[1,1,0,1,3,0,0],[1,1,0,2,0,0,2],[1,1,0,2,2,0,0],[1,1,0,3,0,0,1],[1,1,0,3,1,0,0],[1,1,1,0,0,0,3],[1,1,1,0,0,3,0],[1,1,1,0,3,0,0],[1,1,1,3,0,0,0],[1,1,2,0,0,0,2],[1,1,2,0,0,2,0],[1,1,2,0,2,0,0],[1,1,2,2,0,0,0],[1,1,3,0,0,0,1],[1,1,3,0,0,1,0],[1,1,3,0,1,0,0],[1,1,3,1,0,0,0],[1,2,0,0,0,0,3],[1,2,0,0,0,1,2],[1,2,0,0,0,2,1],[1,2,0,0,0,3,0],[1,2,0,0,1,0,2],[1,2,0,0,1,2,0],[1,2,0,0,2,0,1],[1,2,0,0,2,1,0],[1,2,0,0,3,0,0],[1,2,0,1,0,0,2],[1,2,0,1,2,0,0],[1,2,0,2,0,0,1],[1,2,0,2,1,0,0],[1,2,0,3,0,0,0],[1,2,1,0,0,0,2],[1,2,1,0,0,2,0],[1,2,1,0,2,0,0],[1,2,1,2,0,0,0],[1,2,2,0,0,0,1],[1,2,2,0,0,1,0],[1,2,2,0,1,0,0],[1,2,2,1,0,0,0],[1,2,3,0,0,0,0],[1,3,0,0,0,0,2],[1,3,0,0,0,1,1],[1,3,0,0,0,2,0],[1,3,0,0,1,0,1],[1,3,0,0,1,1,0],[1,3,0,0,2,0,0],[1,3,0,1,0,0,1],[1,3,0,1,1,0,0],[1,3,0,2,0,0,0],[1,3,1,0,0,0,1],[1,3,1,0,0,1,0],[1,3,1,0,1,0,0],[1,3,1,1,0,0,0],[1,3,2,0,0,0,0],[2,0,0,0,0,1,3],[2,0,0,0,0,2,2],[2,0,0,0,0,3,1],[2,0,0,0,1,0,3],[2,0,0,0,1,1,2],[2,0,0,0,1,2,1],[2,0,0,0,1,3,0],[2,0,0,0,2,0,2],[2,0,0,0,2,1,1],[2,0,0,0,2,2,0],[2,0,0,0,3,0,1],[2,0,0,0,3,1,0],[2,0,0,1,0,0,3],[2,0,0,1,0,1,2],[2,0,0,1,0,2,1],[2,0,0,1,0,3,0],[2,0,0,1,1,0,2],[2,0,0,1,1,2,0],[2,0,0,1,2,0,1],[2,0,0,1,2,1,0],[2,0,0,1,3,0,0],[2,0,0,2,0,0,2],[2,0,0,2,0,1,1],[2,0,0,2,0,2,0],[2,0,0,2,1,0,1],[2,0,0,2,1,1,0],[2,0,0,2,2,0,0],[2,0,0,3,0,0,1],[2,0,0,3,0,1,0],[2,0,0,3,1,0,0],[2,0,1,0,0,0,3],[2,0,1,0,0,1,2],[2,0,1,0,0,2,1],[2,0,1,0,0,3,0],[2,0,1,0,1,0,2],[2,0,1,0,1,2,0],[2,0,1,0,2,0,1],[2,0,1,0,2,1,0],[2,0,1,0,3,0,0],[2,0,1,1,0,0,2],[2,0,1,1,0,2,0],[2,0,1,1,2,0,0],[2,0,1,2,0,0,1],[2,0,1,2,0,1,0],[2,0,1,2,1,0,0],[2,0,1,3,0,0,0],[2,0,2,0,0,0,2],[2,0,2,0,0,1,1],[2,0,2,0,0,2,0],[2,0,2,0,1,0,1],[2,0,2,0,1,1,0],[2,0,2,0,2,0,0],[2,0,2,1,0,0,1],[2,0,2,1,0,1,0],[2,0,2,1,1,0,0],[2,0,2,2,0,0,0],[2,0,3,0,0,0,1],[2,0,3,0,0,1,0],[2,0,3,0,1,0,0],[2,0,3,1,0,0,0],[2,1,0,0,0,0,3],[2,1,0,0,0,1,2],[2,1,0,0,0,2,1],[2,1,0,0,0,3,0],[2,1,0,0,1,0,2],[2,1,0,0,1,2,0],[2,1,0,0,2,0,1],[2,1,0,0,2,1,0],[2,1,0,0,3,0,0],[2,1,0,1,0,0,2],[2,1,0,1,2,0,0],[2,1,0,2,0,0,1],[2,1,0,2,1,0,0],[2,1,0,3,0,0,0],[2,1,1,0,0,0,2],[2,1,1,0,0,2,0],[2,1,1,0,2,0,0],[2,1,1,2,0,0,0],[2,1,2,0,0,0,1],[2,1,2,0,0,1,0],[2,1,2,0,1,0,0],[2,1,2,1,0,0,0],[2,1,3,0,0,0,0],[2,2,0,0,0,0,2],[2,2,0,0,0,1,1],[2,2,0,0,0,2,0],[2,2,0,0,1,0,1],[2,2,0,0,1,1,0],[2,2,0,0,2,0,0],[2,2,0,1,0,0,1],[2,2,0,1,1,0,0],[2,2,0,2,0,0,0],[2,2,1,0,0,0,1],[2,2,1,0,0,1,0],[2,2,1,0,1,0,0],[2,2,1,1,0,0,0],[2,2,2,0,0,0,0],[2,3,0,0,0,0,1],[2,3,0,0,0,1,0],[2,3,0,0,1,0,0],[2,3,0,1,0,0,0],[2,3,1,0,0,0,0],[3,0,0,0,0,0,3],[3,0,0,0,0,1,2],[3,0,0,0,0,2,1],[3,0,0,0,0,3,0],[3,0,0,0,1,0,2],[3,0,0,0,1,1,1],[3,0,0,0,1,2,0],[3,0,0,0,2,0,1],[3,0,0,0,2,1,0],[3,0,0,0,3,0,0],[3,0,0,1,0,0,2],[3,0,0,1,0,1,1],[3,0,0,1,0,2,0],[3,0,0,1,1,0,1],[3,0,0,1,1,1,0],[3,0,0,1,2,0,0],[3,0,0,2,0,0,1],[3,0,0,2,0,1,0],[3,0,0,2,1,0,0],[3,0,0,3,0,0,0],[3,0,1,0,0,0,2],[3,0,1,0,0,1,1],[3,0,1,0,0,2,0],[3,0,1,0,1,0,1],[3,0,1,0,1,1,0],[3,0,1,0,2,0,0],[3,0,1,1,0,0,1],[3,0,1,1,0,1,0],[3,0,1,1,1,0,0],[3,0,1,2,0,0,0],[3,0,2,0,0,0,1],[3,0,2,0,0,1,0],[3,0,2,0,1,0,0],[3,0,2,1,0,0,0],[3,0,3,0,0,0,0],[3,1,0,0,0,0,2],[3,1,0,0,0,1,1],[3,1,0,0,0,2,0],[3,1,0,0,1,0,1],[3,1,0,0,1,1,0],[3,1,0,0,2,0,0],[3,1,0,1,0,0,1],[3,1,0,1,1,0,0],[3,1,0,2,0,0,0],[3,1,1,0,0,0,1],[3,1,1,0,0,1,0],[3,1,1,0,1,0,0],[3,1,1,1,0,0,0],[3,1,2,0,0,0,0],[3,2,0,0,0,0,1],[3,2,0,0,0,1,0],[3,2,0,0,1,0,0],[3,2,0,1,0,0,0],[3,2,1,0,0,0,0],[3,3,0,0,0,0,0]]
def routineCosts : List Nat :=
  [67,70,70,70,71,70,70,70,70,70,74,74,72,73,72,73,73,73,73,73,72,73,73,74,73,74,73,73,73,74,73,74,73,74,70,73,73,73,74,72,73,73,74,70,74,74,76,77,76,77,77,77,77,77,76,77,76,77,76,76,75,76,76,75,76,73,76,76,76,77,76,76,77,73,73,75,76,76,76,73,73,74,73,77,76,76,76,77,76,77,76,77,74,77,77,77,77,76,76,77,73,74,76,77,77,77,74,73,77,74,70,73,73,73,77,75,76,76,77,73,74,76,77,76,76,73,73,77,74,70,74,74,76,77,76,77,77,77,77,77,76,77,80,80,80,79,80,80,79,80,77,80,80,80,80,80,77,77,79,80,80,80,77,76,77,76,80,79,80,80,79,80,76,79,75,76,79,76,75,79,76,73,76,76,76,80,79,79,80,76,77,80,76,76,80,77,73,73,75,76,79,79,76,76,80,76,73,73,74,73,77,76,76,76,77,76,77,76,77,77,80,80,80,80,79,79,80,76,77,79,80,80,80,77,76,80,77,74,77,77,77,80,80,77,77,80,76,76,80,77,73,74,76,77,80,80,77,77,77,74,73,77,77,74,70,73,73,73,77,75,76,76,77,73,77,79,80,79,79,76,76,80,77,73,74,76,77,80,80,77,76,80,76,73,73,77,77,74,70,70,70,72,73,72,73,73,73,73,73,72,73,76,77,76,76,75,76,76,75,76,73,76,76,76,77,76,76,77,73,73,75,76,76,76,73,76,77,76,80,79,80,80,79,80,76,79,75,76,79,76,75,79,76,73,76,76,76,80,79,79,80,76,77,80,76,76,80,77,73,73,75,76,79,79,76,76,80,76,73,76,77,76,80,79,80,80,79,80,80,79,80,80,79,80,76,79,79,75,76,79,79,76,75,79,79,76,73,76,76,76,80,79,79,80,76,80,79,79,80,76,77,80,80,76,76,80,80,77,73,73,75,76,79,79,76,79,79,76,76,80,80,76,73,69,70,69,73,72,72,72,73,72,73,72,73,73,76,76,76,76,75,75,76,72,73,75,76,76,76,73,72,76,73,73,76,76,76,80,79,79,80,76,76,79,75,75,79,76,72,73,75,76,79,79,76,76,80,76,73,72,76,76,73,73,76,76,76,80,79,79,80,76,80,79,79,80,76,76,79,79,75,75,79,79,76,72,73,75,76,79,79,76,79,79,76,76,80,80,76,73,72,76,76,76,73,66,69,69,69,73,71,72,72,73,69,73,75,76,75,75,72,72,76,73,69,73,75,76,79,79,76,75,79,75,72,72,76,76,73,69,73,75,76,79,79,76,79,79,76,75,79,79,75,72,72,76,76,76,73,69]
def codeSize : Nat := 600
def activeCount (word : List Nat) : Nat := (word.filter (· ≠ 0)).length
set_option maxRecDepth 100000 in
theorem codeRanks_length : codeRanks.length = 600 := by decide
set_option maxRecDepth 100000 in
theorem codeWords_length : codeWords.length = 600 := by decide
set_option maxRecDepth 100000 in
theorem routineCosts_length : routineCosts.length = 600 := by decide
set_option maxRecDepth 100000 in
theorem codeWords_shape : ∀ word ∈ codeWords,
    word.length = 7 ∧ word.sum = 6 ∧ (∀ value ∈ word, value < 4) ∧ activeCount word ≤ 4 := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem codeRanks_chain : codeRanks.IsChain (· < ·) := by decide +kernel
theorem codeRanks_sorted : codeRanks.Pairwise (· < ·) :=
  List.isChain_iff_pairwise.mp codeRanks_chain
set_option maxRecDepth 100000 in
theorem codeRanks_lt : ∀ rank ∈ codeRanks, rank < 728 := by decide +kernel
set_option maxRecDepth 100000 in
theorem codeRanks_map : codeRanks.map (fun rank => (compositions 4 7 6).getD rank []) = codeWords := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem routineCosts_bounds : ∀ cost ∈ routineCosts, 66 ≤ cost ∧ cost ≤ 80 := by decide +kernel
def embed (rank : Fin 600) : Fin 728 :=
  ⟨codeRanks[rank.val]'(by rw [codeRanks_length]; exact rank.isLt), codeRanks_lt _ (List.getElem_mem _)⟩
def wordDigit (rank : Fin 600) (chain : Fin 7) : Nat := digit (embed rank) chain
def routineCost (rank : Fin 600) : Nat :=
  routineCosts[rank.val]'(by rw [routineCosts_length]; exact rank.isLt)
theorem codeword_embed (rank : Fin 600) :
    codeword (embed rank) = codeWords[rank.val]'(by rw [codeWords_length]; exact rank.isLt) := by
  have hl : rank.val < (codeRanks.map (fun rank => (compositions 4 7 6).getD rank [])).length := by
    rw [List.length_map, codeRanks_length]; exact rank.isLt
  have h := List.getElem_of_eq codeRanks_map hl
  rw [List.getElem_map] at h
  unfold codeword
  rw [← h, List.getD_eq_getElem]
  rfl
theorem embed_strictMono : StrictMono embed := by
  intro a b hab
  change codeRanks[a.val]'_ < codeRanks[b.val]'_
  exact List.pairwise_iff_getElem.mp codeRanks_sorted _ _ _ _ hab
theorem embed_injective : Function.Injective embed := embed_strictMono.injective
theorem embed_active (rank : Fin 600) : activeCount (codeword (embed rank)) ≤ 4 := by
  rw [codeword_embed]; exact (codeWords_shape _ (List.getElem_mem _)).2.2.2
theorem routineCost_bounds (rank : Fin 600) : 66 ≤ routineCost rank ∧ routineCost rank ≤ 80 :=
  routineCosts_bounds _ (List.getElem_mem _)
theorem embed_zero : embed 0 = 0 := rfl
set_option maxRecDepth 100000 in
theorem embed_last : embed 599 = 727 := by decide +kernel
theorem wordDigit_lt (rank : Fin 600) (chain : Fin 7) : wordDigit rank chain < 4 := digit_lt _ _
theorem wordDigit_le_three (rank : Fin 600) (chain : Fin 7) : wordDigit rank chain ≤ 3 := digit_le_three _ _
theorem ofFn_wordDigit (rank : Fin 600) :
    List.ofFn (fun chain : Fin 7 => wordDigit rank chain) = codeword (embed rank) := ofFn_digit _
theorem wordStep_count (rank : Fin 600) : (∑ chain : Fin 7, wordDigit rank chain) = 6 := step_count _
theorem wordRevealed_count (rank : Fin 600) : (∑ chain : Fin 7, (3 - wordDigit rank chain)) = 15 :=
  revealed_count _
theorem wordActive_le (rank : Fin 600) :
    activeCount (List.ofFn (fun chain : Fin 7 => wordDigit rank chain)) ≤ 4 := by
  rw [ofFn_wordDigit]; exact embed_active rank
def wordEncode (rank : Fin 600) : ValidEncoding := encode (embed rank)
theorem wordEncode_injective : Function.Injective wordEncode :=
  encode_injective.comp embed_injective
theorem wordDigit_injective : Function.Injective wordDigit := by
  intro left right he
  apply wordEncode_injective
  apply Subtype.ext; funext chain; apply Fin.ext
  exact congrFun he chain
theorem wordAntichain (left right : Fin 600)
    (h : ∀ chain, wordDigit left chain ≤ wordDigit right chain) : left = right :=
  embed_injective (antichain _ _ h)
theorem card_rank : Fintype.card (Fin 600) = codeSize := Fintype.card_fin 600
structure CodeSpec where
  size : Nat
  digit : Fin size → Fin 7 → Nat
  digit_lt : ∀ rank chain, digit rank chain < 4
  step_count : ∀ rank, (∑ chain : Fin 7, digit rank chain) = 6
  injective : Function.Injective digit
def code600 : CodeSpec where
  size := 600
  digit := wordDigit
  digit_lt := wordDigit_lt
  step_count := wordStep_count
  injective := wordDigit_injective
theorem CodeSpec.antichain (code : CodeSpec) (left right : Fin code.size)
    (h : ∀ chain, code.digit left chain ≤ code.digit right chain) : left = right := by
  have hsum : (∑ chain, code.digit left chain) = ∑ chain, code.digit right chain := by
    rw [code.step_count, code.step_count]
  have he := (Finset.sum_eq_sum_iff_of_le (fun chain _ => h chain)).mp hsum
  exact code.injective (funext fun chain => he chain (Finset.mem_univ chain))
section Walk
variable {Value : Type}
def walk (step : Nat → Value → Value) (start : Nat) : Nat → Value → Value
  | 0, value => value
  | count + 1, value => step (start + count) (walk step start count value)
theorem walk_add (step : Nat → Value → Value) (start first second : Nat) (value : Value) :
    walk step start (first + second) value =
      walk step (start + first) second (walk step start first value) := by
  induction second with
  | zero => simp [walk]
  | succ second ih =>
      change step (start + (first + second)) (walk step start (first + second) value) =
        step ((start + first) + second)
          (walk step (start + first) second (walk step start first value))
      rw [ih, Nat.add_assoc]
def opening (step : Fin 7 → Nat → Value → Value) (secrets : Fin 7 → Value)
    (rank : Fin 728) (chain : Fin 7) : Value :=
  walk (step chain) 0 (3 - digit rank chain) (secrets chain)
def recover (step : Fin 7 → Nat → Value → Value) (rank : Fin 728)
    (values : Fin 7 → Value) (chain : Fin 7) : Value :=
  walk (step chain) (3 - digit rank chain) (digit rank chain) (values chain)
theorem recover_opening (step : Fin 7 → Nat → Value → Value) (secrets : Fin 7 → Value)
    (rank : Fin 728) (chain : Fin 7) :
    recover step rank (opening step secrets rank) chain = walk (step chain) 0 3 (secrets chain) := by
  have hd := digit_lt rank chain
  unfold recover opening
  have h := (walk_add (step chain) 0 (3 - digit rank chain)
    (digit rank chain) (secrets chain)).symm
  simpa only [Nat.zero_add, Nat.sub_add_cancel (by omega : digit rank chain ≤ 3)] using h
theorem padded_backward_hit {Input : Type} (hash : Input → Value)
    (actualInput : Nat → Value → Input) (honestInput : Nat → Input)
    (honest : Nat → Value)
    (honest_step : ∀ position, honest (position + 1) = hash (honestInput position))
    (decode_input : ∀ position value, actualInput position value = honestInput position →
      value = honest position)
    (start count : Nat) (value : Value)
    (endpoint : walk (fun position value => hash (actualInput position value)) start count value =
      honest (start + count)) :
    (value = honest start ∧ ∀ offset < count,
      actualInput (start + offset)
        (walk (fun position value => hash (actualInput position value)) start offset value) =
      honestInput (start + offset)) ∨
    ∃ offset < count,
      actualInput (start + offset)
        (walk (fun position value => hash (actualInput position value)) start offset value) ≠
      honestInput (start + offset) ∧
      hash (actualInput (start + offset)
        (walk (fun position value => hash (actualInput position value)) start offset value)) =
      honest (start + offset + 1) := by
  induction count with
  | zero =>
      refine Or.inl ⟨?_, ?_⟩
      · simpa only [walk, Nat.add_zero] using endpoint
      · intro offset ho
        omega
  | succ count ih =>
      rcases Classical.em (actualInput (start + count)
          (walk (fun position value => hash (actualInput position value)) start count value) =
          honestInput (start + count)) with he | he
      · have hprior := decode_input (start + count) _ he
        rcases ih hprior with ⟨hv, hinputs⟩ | ⟨offset, ho, hne, hhash⟩
        · refine Or.inl ⟨hv, ?_⟩
          intro offset ho
          by_cases hc : offset < count
          · exact hinputs offset hc
          · have hoff : offset = count := by omega
            subst offset
            exact he
        · exact Or.inr ⟨offset, by omega, hne, hhash⟩
      · refine Or.inr ⟨count, by omega, he, ?_⟩
        have hcollision :
            hash (actualInput (start + count)
              (walk (fun position value => hash (actualInput position value)) start count value)) =
            hash (honestInput (start + count)) := by
          rw [← honest_step]
          simpa only [walk, Nat.add_assoc] using endpoint
        exact hcollision.trans (honest_step (start + count)).symm
end Walk
end ClaudeWCT.WCT9
