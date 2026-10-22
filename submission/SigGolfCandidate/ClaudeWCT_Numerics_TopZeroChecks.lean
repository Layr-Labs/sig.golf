import SigGolfCandidate.ClaudeWCT_Numerics_N600PriceChecks

/-! # Top layer (campaign T51): the canonical top histograms and the T51 signing-moment packet
The canonical top producer accepts a word only if at most 7 of its 51 digits (the checksum included) are zero
(`ClaudeWCT.WCT9.producerZeroCap 0 = 7`), at the top floor 14 with the d6b LOW bonus 2. This module provides
* the canonical statistics of the T51 model word (`SigGolfResearch.T51Top`): the zero-fibered packed generating
  polynomial (`stat = 32712·zeros + 141·weight + score`, radix `2^128`, zero counts `< 8`), whose windows are the
  exact top credit histograms `topCountsT51` / `topFreeCountsT51` (kernel checks), and the bridge from the T51 top
  digests to the model (`wordCredit`, `savedCopies`, `topDispatchPenalty`, zero digits, `TopChoice.blocked`);
* the canonical top API at the T51 floor (`ClaudeWCT.W9.T3.ProducerV5.Canonical`: `topWordCount`, `topFreeCount_eq`,
  `topHighWeight`, `selected_top_path_card`, `producerDecodeAt_top_credit_lt`);
* the T51 signing-moment packet (`ClaudeWCT.Numerics.TopZero`): top counts (credit ≥ 12), the d6b split histogram,
  the initial bound (floor 14, pool 69), the fixed power (fixed sign work 112326) and the full moment
  (1.999750417 < 1.99976; RC: gate 791, cap 777). -/

namespace SigGolfResearch.T51Top
open Finset
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false
set_option linter.unusedSimpArgs false

/-- The canonical statistic `32712 * zeros + 141 * weight + score`. -/
def canonS : GStat := ⟨fun g r => tstat 6 (decide (g.val = 0)) false r, fun j r => tstat 5 false (pen j) r, pstat⟩
theorem canonS_eval (w : «Word») : canonS.eval w = SigGolfResearch.T51Top.stat w := rfl

/-- Zero counts below 8. -/
def cutExp : Nat := 32712 * 8
def packedT (free : Bool) : Nat := packedG cutExp canonS free
attribute [irreducible] packedT

def Sk (free : Bool) (k : Nat) (w : «Word») : Prop := (free = true → isFree w) ∧ SigGolfResearch.T51Top.stat w = k
instance (free : Bool) (k : Nat) : DecidablePred (Sk free k) := fun w => by unfold Sk; infer_instance
def cnt (free : Bool) (k : Nat) : Nat := (univ.filter (Sk free k)).card
attribute [irreducible] cnt

theorem packedT_cnt (free : Bool) (k : Nat) (hk : k < cutExp) : packedT free / B ^ k % B = cnt free k := by
  rw [packedT, packedG_digit _ _ _ _ hk, cnt]
  rfl

/-! ### Histogram windows
A credit `c` (no path bonus) of an accepted top word is `score + [checksum = 4] - 3`; the checksum digit is
`d = 152 - weight ∈ [0, 5]`, and the zero filter is `zeros + [d = 0] ≤ 7`. For each admissible `(d, z)` the
coefficients of the credits `12 ..< 138` form one window of 126 radix-`B` digits. -/
def pairsL : List (Nat × Nat) :=
  ((List.range 6).flatMap fun d => (List.range 8).map fun z => (d, z)).filter
    fun pr => decide (pr.2 + ind (pr.1 = 0) ≤ 7)
def pos (pr : Nat × Nat) (c : Nat) : Nat := 32712 * pr.2 + 141 * (152 - pr.1) + (c + 3 - ind (pr.1 = 4))
def winLen : Nat := 126
def window (p : Nat) (pr : Nat × Nat) : Nat := (p >>> (128 * pos pr 12)) % B ^ winLen
def windows (free : Bool) : List Nat := pairsL.map (window (packedT free))
attribute [irreducible] windows
def digitAt (i W : Nat) : Nat := (W >>> (128 * i)) % B
def histAt (ws : List Nat) (i : Nat) : Nat := (ws.map (digitAt i)).sum
def histW (h : List (Nat × Nat)) (c : Nat) : Nat := (h.map fun e => if e.1 = c then e.2 else 0).sum
def histCheck (counts : List (Nat × Nat)) (free : Bool) : Bool :=
  (List.range winLen).all fun i => histW counts (12 + i) == histAt (windows free) i

theorem pairsL_nodup : pairsL.Nodup := by decide
theorem mem_pairsL (d z : Nat) : (d, z) ∈ pairsL ↔ d < 6 ∧ z < 8 ∧ z + ind (d = 0) ≤ 7 := by
  simp only [pairsL, List.mem_filter, List.mem_flatMap, List.mem_map, List.mem_range, Prod.mk.injEq,
    decide_eq_true_eq]
  constructor
  · rintro ⟨⟨a, ha, b, hb, rfl, rfl⟩, h⟩; exact ⟨ha, hb, h⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨d, h1, z, h2, rfl, rfl⟩, h3⟩

attribute [irreducible] pairsL

theorem shiftRight_B (p n : Nat) : p >>> (128 * n) = p / B ^ n := by
  rw [Nat.shiftRight_eq_div_pow, B, ← pow_mul]

theorem window_digit (p : Nat) (pr : Nat × Nat) (i : Nat) (hi : i < winLen) :
    (window p pr >>> (128 * i)) % B = p / B ^ (pos pr 12 + i) % B := by
  rw [window, shiftRight_B, shiftRight_B, digit_mod_pow _ _ _ _ hi, Nat.div_div_eq_div_mul, ← pow_add]

theorem pos_add (pr : Nat × Nat) (i : Nat) : pos pr (12 + i) = pos pr 12 + i := by
  unfold pos ind; split_ifs <;> omega

theorem pos_lt (d z : Nat) (hpr : (d, z) ∈ pairsL) (c : Nat) (hc : c < 138) : pos (d, z) c < cutExp := by
  obtain ⟨h1, h2, h3⟩ := (mem_pairsL d z).mp hpr
  have hi := ind_le (d = 4)
  show 32712 * z + 141 * (152 - d) + (c + 3 - ind (d = 4)) < 32712 * 8
  omega

theorem sum_map_map_congr {α β : Type} (l : List α) (f : α → β) (g : β → Nat) (h : α → Nat)
    (H : ∀ a ∈ l, g (f a) = h a) : ((l.map f).map g).sum = (l.map h).sum := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [H a (by simp), ih (fun b hb => H b (by simp [hb]))]

theorem histAt_eq (free : Bool) (i : Nat) (hi : i < winLen) :
    histAt (windows free) i = (pairsL.map fun pr => cnt free (pos pr (12 + i))).sum := by
  have hmap : ∀ pr ∈ pairsL, digitAt i (window (packedT free) pr) = cnt free (pos pr (12 + i)) := by
    intro pr hpr
    obtain ⟨d, z⟩ := pr
    rw [digitAt, window_digit _ _ _ hi, ← pos_add]
    exact packedT_cnt free _ (pos_lt d z hpr _ (by unfold winLen at hi; omega))
  unfold histAt
  rw [windows]
  exact sum_map_map_congr pairsL (window (packedT free)) (digitAt i) _ hmap

/-- The model predicate of an accepted top word of credit `c` (no path bonus). -/
def accepts (c : Nat) (w : «Word») : Prop :=
  147 ≤ SigGolfResearch.T51Top.weight w ∧ SigGolfResearch.T51Top.weight w ≤ 152 ∧ SigGolfResearch.T51Top.zeros w + ind (SigGolfResearch.T51Top.weight w = 152) ≤ 7 ∧ SigGolfResearch.T51Top.score w + ind (SigGolfResearch.T51Top.weight w = 148) = c + 3
def Qc (free : Bool) (c : Nat) (w : «Word») : Prop := (free = true → isFree w) ∧ accepts c w
instance (free : Bool) (c : Nat) : DecidablePred (Qc free c) := fun w => by unfold Qc accepts; infer_instance

theorem accepts_le {c : Nat} {w : «Word»} (h : accepts c w) : c ≤ 137 := by
  have := score_le w
  have := ind_le (SigGolfResearch.T51Top.weight w = 148)
  unfold accepts at h
  omega

theorem key_mem (c : Nat) (w : «Word») (h : accepts c w) : (152 - SigGolfResearch.T51Top.weight w, SigGolfResearch.T51Top.zeros w) ∈ pairsL := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine (mem_pairsL _ _).mpr ⟨by omega, ?_, ?_⟩
  · have := ind_le (SigGolfResearch.T51Top.weight w = 152); omega
  · by_cases w3 : SigGolfResearch.T51Top.weight w = 152
    · rw [ind_pos w3] at h3; rw [ind_pos (by omega)]; omega
    · rw [ind_neg w3] at h3; rw [ind_neg (by omega)]; omega

theorem fiber_eq (free : Bool) (c : Nat) (hc2 : c < 138) (d z : Nat) (hd : d < 6) (hz8 : z < 8)
    (hz7 : z + ind (d = 0) ≤ 7) (w : «Word») :
    (Qc free c w ∧ (152 - SigGolfResearch.T51Top.weight w, SigGolfResearch.T51Top.zeros w) = (d, z)) ↔ Sk free (pos (d, z) c) w := by
  have hs := stat_eq w
  have hsc := score_le w
  have hw := weight_le w
  unfold Qc accepts Sk
  rw [Prod.mk.injEq]
  show _ ↔ _ ∧ SigGolfResearch.T51Top.stat w = 32712 * z + 141 * (152 - d) + (c + 3 - ind (d = 4))
  rcases ind_cases (d = 4) with ⟨i4, e4⟩ | ⟨i4, e4⟩ <;> rw [e4] <;>
  rcases ind_cases (d = 0) with ⟨i0, e0⟩ | ⟨i0, e0⟩ <;> rw [e0] at hz7 <;>
  rcases ind_cases (SigGolfResearch.T51Top.weight w = 152) with ⟨i3, e3⟩ | ⟨i3, e3⟩ <;> rw [e3] <;>
  rcases ind_cases (SigGolfResearch.T51Top.weight w = 148) with ⟨i7, e7⟩ | ⟨i7, e7⟩ <;> rw [e7] <;>
  · constructor
    · intro h
      have g1 := h.1.2.1
      have g2 := h.1.2.2.1
      have g3 := h.1.2.2.2.1
      have g4 := h.1.2.2.2.2
      have g5 := h.2.1
      have g6 := h.2.2
      exact ⟨h.1.1, by omega⟩
    · intro h
      have g := h.2
      have k1 : 147 ≤ SigGolfResearch.T51Top.weight w := by omega
      have k2 : SigGolfResearch.T51Top.weight w ≤ 152 := by omega
      have k3 : SigGolfResearch.T51Top.zeros w = z := by omega
      have k4 : 152 - SigGolfResearch.T51Top.weight w = d := by omega
      exact ⟨⟨h.1, k1, k2, by omega, by omega⟩, k4, k3⟩

theorem model_count (free : Bool) (c : Nat) (hc1 : 12 ≤ c) (hc2 : c < 138) :
    (univ.filter (Qc free c)).card = histAt (windows free) (c - 12) := by
  rw [histAt_eq free _ (by unfold winLen; omega), show 12 + (c - 12) = c by omega,
    ← List.sum_toFinset _ pairsL_nodup]
  rw [fiber_card_filter (Qc free c) (fun w => (152 - SigGolfResearch.T51Top.weight w, SigGolfResearch.T51Top.zeros w)) pairsL.toFinset
    (fun w hq => List.mem_toFinset.mpr (key_mem c w hq.2))]
  apply Finset.sum_congr rfl
  intro pr hpr
  obtain ⟨d, z⟩ := pr
  obtain ⟨hd, hz8, hz7⟩ := (mem_pairsL d z).mp (List.mem_toFinset.mp hpr)
  rw [cnt, Finset.filter_filter]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro w _
  exact fiber_eq free c hc2 d z hd hz8 hz7 w

theorem model_count_of_check (counts : List (Nat × Nat)) (free : Bool) (h : histCheck counts free = true)
    (c : Nat) (hc1 : 12 ≤ c) (hc2 : c < 138) :
    (univ.filter (Qc free c)).card = histW counts c := by
  rw [model_count free c hc1 hc2]
  unfold histCheck at h
  rw [List.all_eq_true] at h
  have := h (c - 12) (List.mem_range.mpr (by unfold winLen; omega))
  rw [beq_iff_eq, show 12 + (c - 12) = c by omega] at this
  exact this.symm

end SigGolfResearch.T51Top

namespace SigGolfResearch.T51Top
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Accepted top words (digit sum 152, zeros `≤ 7`, the checksum included) by credit `c ≥ 12` (reward - penalty, no
path bonus). -/
def topCountsT51 : List (Nat × Nat) := [(12,315267888952829519964878148817408),(13,502581346701182045522268145774137),(14,752511626605814064391474231634097),(15,1065558889020304945675904928167367),(16,1435173543730904921684088400733665),(17,1847358414495983032061822829906264),(18,2281059026126517901177221012090047),(19,2710088137917419774744565183673440),(20,3106381285222563864679340438895972),(21,3443101210383762587339493452981998),(22,3697164833100889464932241878451900),(23,3851950020861338549606416396512391),(24,3899466402443270255183300791298816),(25,3840497083895266749755782060534290),(26,3683438290245130298421569470678936),(27,3443246811490046271672743583069683),(28,3139756159292829995297839335681433),(29,2794787539114124815693836628274285),(30,2429665578785143309544744767521438),(31,2063911680114308962796572867575890),(32,1713979195232822763579746142893595),(33,1392034529852189954508107526852456),(34,1105873428300327158397997185708580),(35,859565447621140307361943490363595),(36,653882477690401234607090421926351),(37,486856173817396099173657622031378),(38,354782414252248455204523845017178),(39,253070632192734928840467446199840),(40,176719187273282712210967289445601),(41,120779088503944530431991335270023),(42,80776907135688649363243261396168),(43,52870350636583016492232039516898),(44,33860738089922211619787018377115),(45,21208781064250528632644276779374),(46,12989906571273476445322356097518),(47,7780272589154649898193776372287),(48,4554308446783618596549660812911),(49,2603689645505090258870517889338),(50,1453957434519794999076766650058),(51,792910168967510598376785179942),(52,421760455281535110174513103031),(53,218725672809233917248828043613),(54,110652438871872713032333839247),(55,54543565521105730781452342433),(56,26150796855825835062166991600),(57,12205435648988997694899471032),(58,5547018465369871787926613938),(59,2446663600613089231928625868),(60,1046684360751594765503422443),(61,435598336819529787498090077),(62,175805023853601196223333167),(63,68449619613514022562097299),(64,25841717283341691968204252),(65,9478773374051756905910165),(66,3336656681249301760085315),(67,1128696760071200189970841),(68,372452471932842146413249),(69,117949362025534644968846),(70,35221179476225672079433),(71,10260006775364160419227),(72,2913115076880581317101),(73,758493754933562958424),(74,188769225925145507859),(75,47894625739629217091),(76,10845676719716212822),(77,2151833132882470252),(78,474642317931986090),(79,97255931088472544),(80,14591562005458974),(81,2630076595352220),(82,492925440180390),(83,40324945858980),(84,4360291116622),(85,1324310968456),(86,121038590736),(87,875923776),(88,287165088)]
/-- The same restricted to words whose LOW half is not forced (r6 group 8 rank `≥ 64`). -/
def topFreeCountsT51 : List (Nat × Nat) := [(12,282559939817465342628440835330478),(13,449531826473941812198654424498336),(14,671679536679118155878398264670365),(15,949057367256986544053436168665683),(16,1275426698651883430286602707781017),(17,1637974563793195715116183500128883),(18,2017746308622482177055320174126433),(19,2391428081759058874794028308265531),(20,2734273530578908023550395197329282),(21,3022865586093975226088057177011379),(22,3237339642185944724382107443046154),(23,3363715886763297140030052612232182),(24,3395714150629552737366614323529813),(25,3334783194955924198019678398722140),(26,3188999364365112193419670485694138),(27,2972052559251269626688486169073355),(28,2701696952482902936298571014698086),(29,2397206605668107613542592052829741),(30,2077218548921436478696536057990486),(31,1758604203314945787643422806975417),(32,1455405459748317766481802777336458),(33,1177845305972739623289320776378780),(34,932311767924861340017826228798971),(35,721951883754901994367106738366398),(36,547085919166208939675385961604751),(37,405727266483366872683046760520036),(38,294458183401020090678486524487479),(39,209160020741517175284617157422083),(40,145425112359276469462165621902767),(41,98948296698660984995805535996470),(42,65872682151013422232937140888836),(43,42910875740502999387981667569020),(44,27347650257872154980318498794920),(45,17042716743870458778912047755059),(46,10383797773248711267716064175854),(47,6185739861010776354509842024312),(48,3600666351570151960274832520261),(49,2046588482550212720390308249196),(50,1136010319426713325811546594119),(51,615661961726518426056776402538),(52,325366048026888809860727947349),(53,167606751600724338628670539398),(54,84200995815721530265899996678),(55,41203774548537734283675193327),(56,19606321244714397760341317705),(57,9079157552056602903276001467),(58,4092313872661107374797735123),(59,1789563098014996372126636777),(60,758757584155293036256466929),(61,312816715263099117499892103),(62,125007309410924000394275131),(63,48172731806094265959772715),(64,17991480177433442045135942),(65,6523968894065580486182764),(66,2268997670619973617082938),(67,758003385439166096761128),(68,246821159731968159030052),(69,77053382146070805879863),(70,22671091355759130442382),(71,6503108629079711373764),(72,1815242636058569509472),(73,464174467719285920610),(74,113491077189466389625),(75,28237502074863276668),(76,6248281254779921656),(77,1212323783156267194),(78,261840165059759183),(79,52179972917130331),(80,7618366411112909),(81,1345792409546788),(82,242026514474962),(83,18571403401158),(84,2050132798658),(85,599959642891),(86,50925893655),(87,329325360),(88,110625732)]

theorem histCheck_all : histCheck topCountsT51 false = true := by decide +kernel
theorem histCheck_free : histCheck topFreeCountsT51 true = true := by decide +kernel


/-- `|C_L∖B|`: canonical top words that are LOW-good (credit ≥ 12, i.e. floor 14 with the LOW bonus 2) and whose LOW
half is not forced. -/
def freeCountT51 : Nat := 50025990371737199867992306903047594
theorem freeCountT51_hist : ((List.range' 12 126).map (histW topFreeCountsT51)).sum = freeCountT51 := by
  decide +kernel
theorem topCountsT51_lt : ∀ e ∈ topCountsT51, e.1 < 138 := by decide
theorem histW_eq_zero (h : List (Nat × Nat)) (c : Nat) (hc : ∀ e ∈ h, e.1 ≠ c) : histW h c = 0 := by
  unfold histW
  induction h with
  | nil => rfl
  | cons e t ih =>
    rw [List.map_cons, List.sum_cons, if_neg (hc e (by simp)), Nat.zero_add]
    exact ih (fun e' he' => hc e' (by simp [he']))

#print axioms histCheck_all
#print axioms histCheck_free
end SigGolfResearch.T51Top

namespace SigGolfResearch.T51Top
open Finset SigGolfCandidate.T3 SigGolfCandidate.T3.Nonbinary ClaudeWCT.WCT9
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false
set_option linter.unusedSimpArgs false

theorem wordCredit_encode (w : «Word») (chk : Nat) :
    wordCredit 0 (dataDigits 0 (encode w) ++ [chk]) = credits w + ind (chk + 1 = 5) := by
  unfold wordCredit
  rw [show chainCount 0 = 51 from rfl, filter_range_length, sum_51, getD48, getD49, getD50,
    show maxDigit 0 48 = 6 from rfl, show maxDigit 0 49 = 6 from rfl, show maxDigit 0 50 = 5 from rfl]
  unfold credits pcredit
  congr 2
  congr 1
  · apply Finset.sum_congr rfl; intro g _
    obtain ⟨a0, a1, a2, m0, m1, m2⟩ := blk6 w chk g
    rw [a0, a1, a2, m0, m1, m2]; rfl
  · apply Finset.sum_congr rfl; intro j _
    obtain ⟨a0, a1, a2, m0, m1, m2⟩ := blk5 w chk j
    rw [a0, a1, a2, m0, m1, m2]; rfl

set_option maxHeartbeats 4000000 in
theorem savedCopies_encode (w : «Word») (chk : Nat) :
    savedCopies 0 (dataDigits 0 (encode w) ++ [chk]) = copies w := by
  unfold savedCopies
  rw [show chainCount 0 = 51 from rfl, filter_range_length, sum_51]
  have h50 : ind (safeZeroCopy 0 (dataDigits 0 (encode w) ++ [chk]) 50) = 0 := by
    apply ind_neg; unfold safeZeroCopy; simp
  have h48 : ind (safeZeroCopy 0 (dataDigits 0 (encode w) ++ [chk]) 48) = 0 := by
    apply ind_neg; unfold safeZeroCopy; simp
  have h49 : ind (safeZeroCopy 0 (dataDigits 0 (encode w) ++ [chk]) 49) = pcopies w.2.2.val := by
    unfold pcopies
    apply ind_congr; unfold safeZeroCopy
    rw [getD49, show 49 - 1 = 48 from rfl, getD48, show maxDigit 0 49 = 6 from rfl,
      show maxDigit 0 48 = 6 from rfl]
    constructor
    · rintro ⟨h1, h2 | ⟨h2, _⟩ | ⟨_, _, _, h3⟩⟩
      · omega
      · exact absurd rfl h2
      · exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, Or.inr (Or.inr ⟨by omega, by omega, by omega, h2⟩)⟩
  rw [h50, h48, h49, Nat.add_zero, Nat.zero_add]
  unfold copies
  congr 1
  congr 1
  · apply Finset.sum_congr rfl; intro g _
    obtain ⟨a0, a1, a2, m0, m1, m2⟩ := blk6 w chk g
    have hg := g.isLt
    unfold tcopies
    congr 1; congr 1
    · apply ind_congr; unfold safeZeroCopy; rw [a0, m0]
      constructor
      · rintro ⟨h1, h2 | ⟨h2, _⟩ | ⟨_, h2, _⟩⟩
        · exact ⟨by simp; omega, h1⟩
        · exact absurd rfl h2
        · omega
      · rintro ⟨h1, h2⟩; exact ⟨h2, Or.inl (by simp at h1; omega)⟩
    · apply ind_congr; unfold safeZeroCopy
      rw [a1, m1, show 3 * g.val + 1 - 1 = 3 * g.val by omega, a0, m0]
      constructor
      · rintro ⟨h1, h2 | ⟨h2, _⟩ | ⟨_, _, _, h3⟩⟩
        · omega
        · exact absurd rfl h2
        · exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, Or.inr (Or.inr ⟨by omega, by omega, by omega, h2⟩)⟩
    · apply ind_congr; unfold safeZeroCopy
      rw [a2, m2, show 3 * g.val + 2 - 1 = 3 * g.val + 1 by omega, a1, m1]
      constructor
      · rintro ⟨h1, h2 | ⟨h2, _⟩ | ⟨_, _, _, h3⟩⟩
        · omega
        · exact absurd rfl h2
        · exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, Or.inr (Or.inr ⟨by omega, by omega, by omega, h2⟩)⟩
  · apply Finset.sum_congr rfl; intro j _
    obtain ⟨a0, a1, a2, m0, m1, m2⟩ := blk5 w chk j
    have hj := j.isLt
    unfold tcopies
    congr 1; congr 1
    · apply ind_congr; unfold safeZeroCopy; rw [a0, m0]
      constructor
      · rintro ⟨h1, h2 | ⟨h2, _⟩ | ⟨_, h2, _⟩⟩
        · omega
        · exact absurd rfl h2
        · omega
      · rintro ⟨h1, _⟩; exact absurd h1 (by simp)
    · apply ind_congr; unfold safeZeroCopy
      rw [a1, m1, show 3 * (9 + j.val) + 1 - 1 = 3 * (9 + j.val) by omega, a0, m0]
      constructor
      · rintro ⟨h1, h2 | ⟨h2, _⟩ | ⟨_, _, _, h3⟩⟩
        · omega
        · exact absurd rfl h2
        · exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, Or.inr (Or.inr ⟨by omega, by omega, by omega, h2⟩)⟩
    · apply ind_congr; unfold safeZeroCopy
      rw [a2, m2, show 3 * (9 + j.val) + 2 - 1 = 3 * (9 + j.val) + 1 by omega, a1, m1]
      constructor
      · rintro ⟨h1, h2 | ⟨h2, _⟩ | ⟨_, _, _, h3⟩⟩
        · omega
        · exact absurd rfl h2
        · exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, Or.inr (Or.inr ⟨by omega, by omega, by omega, h2⟩)⟩

theorem penalty_encode (w : «Word») (chk : Nat) :
    topDispatchPenalty (dataDigits 0 (encode w) ++ [chk]) = penalty w := by
  unfold topDispatchPenalty
  rw [filter_range_length, show 17 = 9 + (7 + 1) by rfl, Finset.sum_range_add, Finset.sum_range_add,
    Finset.sum_range, Finset.sum_range, Finset.sum_range_one]
  have h0 : (∑ g : Fin 9, ind ((g.val = 10 ∨ g.val = 11 ∨ g.val = 12) ∧
      (dataDigits 0 (encode w) ++ [chk]).getD (3 * g.val) 0 + (dataDigits 0 (encode w) ++ [chk]).getD (3 * g.val + 1) 0 +
        (dataDigits 0 (encode w) ++ [chk]).getD (3 * g.val + 2) 0 < 3)) = 0 := by
    apply Finset.sum_eq_zero; intro g _; apply ind_neg; have := g.isLt; omega
  have h16 : ind ((9 + (7 + 0) = 10 ∨ 9 + (7 + 0) = 11 ∨ 9 + (7 + 0) = 12) ∧
      (dataDigits 0 (encode w) ++ [chk]).getD (3 * (9 + (7 + 0))) 0 +
        (dataDigits 0 (encode w) ++ [chk]).getD (3 * (9 + (7 + 0)) + 1) 0 +
        (dataDigits 0 (encode w) ++ [chk]).getD (3 * (9 + (7 + 0)) + 2) 0 < 3) = 0 := by
    apply ind_neg; omega
  rw [h0, h16, Nat.zero_add, Nat.add_zero]
  unfold penalty
  apply Finset.sum_congr rfl; intro j _
  obtain ⟨a0, a1, a2, -, -, -⟩ := blk5 w chk j
  rw [a0, a1, a2]
  apply ind_congr
  unfold pen tsum
  have := j.isLt
  simp only [decide_eq_true_eq]
  omega

theorem zeros_encode (w : «Word») (chk : Nat) :
    ((dataDigits 0 (encode w) ++ [chk]).filter (· = 0)).length = SigGolfResearch.T51Top.zeros w + ind (chk = 0) := by
  rw [List.filter_append, List.length_append]
  congr 1
  · unfold dataDigits
    rw [show dataCount 0 = 50 from rfl, List.filter_map, List.length_map]
    rw [show ((List.range 50).filter ((fun x => decide (x = 0)) ∘ coreDigit 0 (encode w))) =
      (List.range 50).filter (fun i => decide (coreDigit 0 (encode w) i = 0)) from rfl, filter_range_length, sum_50]
    unfold zeros pzeros
    congr 1
    congr 1
    · apply Finset.sum_congr rfl; intro g _
      rw [show 3 * g.val = 3 * g.val + 0 by rfl, core_encode6 w g 0 (by decide), core_encode6 w g 1 (by decide),
        core_encode6 w g 2 (by decide)]; rfl
    · apply Finset.sum_congr rfl; intro j _
      rw [show 3 * (9 + j.val) = 3 * (9 + j.val) + 0 by rfl, core_encode5 w j 0 (by decide),
        core_encode5 w j 1 (by decide), core_encode5 w j 2 (by decide)]; rfl
    · have e0 := core_encode7 w 0 (by decide)
      have e1 := core_encode7 w 1 (by decide)
      simp only [Nat.add_zero, Nat.reduceAdd] at e0 e1
      rw [e0, e1]
  · unfold ind; by_cases h : chk = 0 <;> simp [h]

theorem score_penalty (w : «Word») : SigGolfResearch.T51Top.score w + penalty w = credits w + 4 * copies w + 3 := by
  have hb (j : Fin 7) : (if pen j = true then ind (3 ≤ tsum 5 (w.2.1 j).val) else 0) +
      ind (pen j = true ∧ tsum 5 (w.2.1 j).val < 3) = ind (pen j = true) := by
    unfold ind; by_cases hp : pen j = true <;> by_cases ht : 3 ≤ tsum 5 (w.2.1 j).val <;> simp [hp, ht] <;> omega
  have h3 : (∑ j : Fin 7, ind (pen j = true)) = 3 := by decide
  have hs := Finset.sum_congr rfl (fun j (_ : j ∈ (univ : Finset (Fin 7))) => hb j)
  rw [Finset.sum_add_distrib, h3] at hs
  unfold score credits copies penalty tscore pscore
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Bool.false_eq_true, ↓reduceIte, Nat.add_zero,
    Finset.sum_const_zero] at hs ⊢
  omega

/-! ### The canonical top producer (no path bonus) on model words -/
/-- The canonical top producer accepts `v` at floor 0 without the path bonus, with credit `c`. -/
def acc (c : Nat) (v : Digest) : Prop :=
  match CanonicalPolicy.producerDecodeAt 0 0 false v with
  | none => False
  | some ds => CanonicalPolicy.credit 0 false ds = c
instance (c : Nat) : DecidablePred (acc c) := fun v => by
  unfold acc; split <;> infer_instance

theorem acc_iff (c : Nat) (v : Digest) :
    acc c v ↔ ∃ ds, CanonicalPolicy.producerDecodeAt 0 0 false v = some ds ∧ CanonicalPolicy.credit 0 false ds = c := by
  unfold acc; cases CanonicalPolicy.producerDecodeAt 0 0 false v <;> simp

theorem decode_canonical_top (v : Digest) : CanonicalPolicy.decode 0 v = decode 0 v := by
  simp [CanonicalPolicy.decode, CanonicalPolicy.normalLayer]

theorem acc_valid (c : Nat) (v : Digest) (h : acc c v) : topRanksValid v = true := by
  obtain ⟨ds, hd, -⟩ := (acc_iff c v).mp h
  have hs := (CanonicalPolicy.producerDecodeAt_spec hd).1
  rw [decode_canonical_top] at hs
  exact (decode_top_some hs).2.1

theorem acc_encode_iff (c : Nat) (w : «Word») : acc c (encode w) ↔ accepts c w := by
  rw [acc_iff]
  have hd0 := decode_top_encode w
  unfold accepts
  by_cases hdec : 147 ≤ SigGolfResearch.T51Top.weight w ∧ SigGolfResearch.T51Top.weight w ≤ 152
  · rw [if_pos hdec] at hd0
    unfold CanonicalPolicy.producerDecodeAt
    rw [decode_canonical_top, hd0]
    simp only
    set chk := 152 - SigGolfResearch.T51Top.weight w with hchk
    have hz := zeros_encode w chk
    have hc := wordCredit_encode w chk
    have hp := penalty_encode w chk
    have hcp := savedCopies_encode w chk
    have hsp := score_penalty w
    have e1 : ind (chk + 1 = 5) = ind (SigGolfResearch.T51Top.weight w = 148) := ind_congr (by omega)
    have e2 : ind (chk = 0) = ind (SigGolfResearch.T51Top.weight w = 152) := ind_congr (by omega)
    have i1 := ind_le (SigGolfResearch.T51Top.weight w = 148)
    simp only [CanonicalPolicy.pathReward, CanonicalPolicy.reward, CanonicalPolicy.pathBonus_false, Nat.add_zero,
      CanonicalPolicy.credit, dispatchPenalty, if_true, canonicalZeroBound, producerZeroCap, producerRankBound,
      true_or, and_true]
    rw [hz, hc, hp, hcp, e1, e2]
    constructor
    · rintro ⟨ds, hds, hcr⟩
      split_ifs at hds with hcond
      · cases hds
        refine ⟨hdec.1, hdec.2, hcond.2, by omega⟩
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨_, if_pos ⟨by omega, h3⟩, by omega⟩
  · rw [if_neg hdec] at hd0
    unfold CanonicalPolicy.producerDecodeAt
    rw [decode_canonical_top, hd0]
    simp only [reduceCtorEq, false_and, exists_false, false_iff, not_and]
    intro h1 h2
    exact absurd ⟨h1, h2⟩ hdec

theorem high_bits (X r : Nat) (h8 : X / 2 ^ 120 % 256 = r) (hlt : X < 2 ^ 128) :
    X < 2 ^ 126 ↔ r < 64 := by
  simp only [Nat.reducePow] at *
  omega

theorem blocked_encode (w : «Word») : TopChoice.blocked (encode w) ↔ ¬ isFree w := by
  have h8 : r6Raw (encode w) 8 = (w.1 8).val := by
    have := r6Raw_encode w 8
    rw [if_neg (by decide)] at this
    exact this
  unfold r6Raw r6Shift at h8
  rw [if_neg (by decide)] at h8
  have hlt : topCode (encode w) < 2 ^ 128 := by rw [topCode_encode]; exact code_lt w
  have key := high_bits _ _ h8 hlt
  unfold TopChoice.blocked isFree
  rw [← topCode_lt_iff _ 126 (by decide), key]
  omega

/-- Exact count of the top words of credit `c` accepted by the canonical producer (no path bonus). -/
theorem card_acc (c : Nat) (hc1 : 12 ≤ c) (hc2 : c < 138) :
    (univ.filter (acc c)).card = histW topCountsT51 c := by
  rw [card_encode (acc c) (acc_valid c), ← model_count_of_check topCountsT51 false histCheck_all c hc1 hc2]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro w _
  rw [acc_encode_iff]
  unfold Qc
  simp

/-- Exact count of those whose LOW half is not forced. -/
theorem card_acc_free (c : Nat) (hc1 : 12 ≤ c) (hc2 : c < 138) :
    (univ.filter fun v => acc c v ∧ ¬ TopChoice.blocked v).card = histW topFreeCountsT51 c := by
  rw [card_encode (fun v => acc c v ∧ ¬ TopChoice.blocked v) (fun v h => acc_valid c v h.1),
    ← model_count_of_check topFreeCountsT51 true histCheck_free c hc1 hc2]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro w _
  rw [acc_encode_iff, blocked_encode]
  unfold Qc
  simp only [not_not, forall_const]
  exact And.comm

/-- Every accepted top word has credit at most 137 (no path bonus). -/
theorem acc_le (c : Nat) (v : Digest) (h : acc c v) : c ≤ 137 := by
  have hv := acc_valid c v h
  rw [← encode_wordOf v hv, acc_encode_iff] at h
  exact accepts_le h

end SigGolfResearch.T51Top

/-! ### The canonical top API at the T51 floor (restated from #938's NF17 bridge) -/
namespace ClaudeWCT.W9.T3.ProducerV5.Canonical
open OracleComp OracleSpec ENNReal Finset
open SigGolfCandidate.T3 ClaudeWCT.WCT9
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

theorem pda_zero_of {floor : Nat} {v : Digest} {ds : List Nat}
    (h : CanonicalPolicy.producerDecodeAt 0 floor false v = some ds) :
    CanonicalPolicy.producerDecodeAt 0 0 false v = some ds :=
  producerDecodeAt_floor_zero (fun _ h => absurd h (by simp)) h

/-- Campaign T51: accepted top words of credit `c` (canonical producer at floor 0, no path bonus). -/
noncomputable def topWordCount (c : Nat) : Nat :=
  (univ.filter (accepted 0 0 (fun ds => CanonicalPolicy.credit 0 false ds = c))).card

theorem card_filter_congr' {α : Type} [Fintype α] (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (h : ∀ a, p a ↔ q a) : (univ.filter p).card = (univ.filter q).card :=
  congrArg Finset.card (Finset.filter_congr fun a _ => h a)

theorem accepted_credit_acc (c : Nat) (v : Digest) :
    accepted 0 0 (fun ds => CanonicalPolicy.credit 0 false ds = c) v ↔ SigGolfResearch.T51Top.acc c v := by
  rw [accepted_iff, SigGolfResearch.T51Top.acc_iff]

theorem accepted_credit_floor_iff (floor c : Nat) (hf : floor ≤ c) (v : Digest) :
    accepted 0 floor (fun ds => CanonicalPolicy.credit 0 false ds = c) v ↔
      accepted 0 0 (fun ds => CanonicalPolicy.credit 0 false ds = c) v := by
  rw [accepted_iff, accepted_iff]
  apply exists_congr; intro ds
  constructor
  · rintro ⟨hd, hc⟩; exact ⟨pda_zero_of hd, hc⟩
  · rintro ⟨hd, hc⟩
    refine ⟨?_, hc⟩
    have hs := (producerDecodeAt_eq_some_iff _ _ _ _ _).mp hd
    apply (producerDecodeAt_eq_some_iff _ _ _ _ _).mpr
    refine ⟨hs.1, ?_, hs.2.2⟩
    have h1 := hs.2.1
    simp only [CanonicalPolicy.credit] at hc
    omega

theorem accepted_top_credit_card (floor credit : Nat) (hf : floor ≤ credit) :
    (univ.filter (accepted 0 floor (fun ds => CanonicalPolicy.credit 0 false ds = credit))).card =
      topWordCount credit :=
  card_filter_congr' _ _ (accepted_credit_floor_iff floor credit hf)

/-- Campaign T51: the exact top credit law (credits `≥ 12`), from the T51 generating polynomial. -/
theorem topWordCount_eq (c : Nat) (hc : 12 ≤ c) :
    topWordCount c = SigGolfResearch.T51Top.histW SigGolfResearch.T51Top.topCountsT51 c := by
  by_cases h138 : c < 138
  · unfold topWordCount
    rw [card_filter_congr' _ (SigGolfResearch.T51Top.acc c) (accepted_credit_acc c),
      SigGolfResearch.T51Top.card_acc c hc h138]
  · have h0 : topWordCount c = 0 := by
      unfold topWordCount
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro v _ hv
      have := SigGolfResearch.T51Top.acc_le c v ((accepted_credit_acc c v).mp hv)
      omega
    rw [h0, SigGolfResearch.T51Top.histW_eq_zero _ _
      (fun e he => by have := SigGolfResearch.T51Top.topCountsT51_lt e he; omega)]

/-- Campaign T51 (top floor 14, LOW bonus 2): the LOW-good predicate is acceptance at 12 without the bonus. -/
theorem topGood_iff (v : Digest) : topGood v ↔ accepted 0 12 (fun _ => True) v := by
  unfold topGood
  rw [show CanonicalPolicy.topFloor = 14 from rfl, producerDecodeAt_top_true 14 (by decide), accepted_iff]
  simp only [and_true]
  exact Option.isSome_iff_exists

/-- The credit of a top word (0 when the producer rejects it at floor 0). -/
def creditOf (v : Digest) : Nat :=
  match CanonicalPolicy.producerDecodeAt 0 0 false v with
  | none => 0
  | some ds => CanonicalPolicy.credit 0 false ds

theorem creditOf_of_acc {c : Nat} {v : Digest} (h : SigGolfResearch.T51Top.acc c v) : creditOf v = c := by
  obtain ⟨ds, hd, hc⟩ := (SigGolfResearch.T51Top.acc_iff c v).mp h
  unfold creditOf; rw [hd]; exact hc

theorem accepted12_iff (v : Digest) :
    accepted 0 12 (fun _ => True) v ↔ ∃ c, 12 ≤ c ∧ SigGolfResearch.T51Top.acc c v := by
  rw [accepted_iff]
  constructor
  · rintro ⟨ds, hd, -⟩
    have hc := CanonicalPolicy.producerDecodeAt_credit hd
    exact ⟨_, hc, (SigGolfResearch.T51Top.acc_iff _ v).mpr ⟨ds, pda_zero_of hd, rfl⟩⟩
  · rintro ⟨c, hc, ha⟩
    have h := (accepted_credit_floor_iff 12 c hc v).mpr ((accepted_credit_acc c v).mpr ha)
    obtain ⟨ds, hd, -⟩ := (accepted_iff _ _ _ v).mp h
    exact ⟨ds, hd, trivial⟩

theorem fiber_free (c : Nat) (hc : 12 ≤ c) (v : Digest) :
    ((accepted 0 12 (fun _ => True) v ∧ ¬ TopChoice.blocked v) ∧ creditOf v = c) ↔
      (SigGolfResearch.T51Top.acc c v ∧ ¬ TopChoice.blocked v) := by
  constructor
  · rintro ⟨⟨ha, hb⟩, he⟩
    obtain ⟨c', -, hc'⟩ := (accepted12_iff v).mp ha
    have := creditOf_of_acc hc'
    subst he
    rw [this]; exact ⟨hc', hb⟩
  · rintro ⟨ha, hb⟩
    exact ⟨⟨(accepted12_iff v).mpr ⟨c, hc, ha⟩, hb⟩, creditOf_of_acc ha⟩

/-- Campaign T51: the exact number of LOW-good top words whose LOW is not forced. -/
theorem topFreeCount_eq : topFreeCount = SigGolfResearch.T51Top.freeCountT51 := by
  unfold topFreeCount
  rw [card_filter_congr' _ (fun v => accepted 0 12 (fun _ => True) v ∧ ¬ TopChoice.blocked v)
    (fun v => and_congr_left' (topGood_iff v))]
  rw [SigGolfResearch.T51Top.fiber_card_filter (fun v => accepted 0 12 (fun _ => True) v ∧ ¬ TopChoice.blocked v)
    creditOf (List.range' 12 126).toFinset (fun v hv => by
      obtain ⟨c, hc, ha⟩ := (accepted12_iff v).mp hv.1
      rw [creditOf_of_acc ha, List.mem_toFinset, List.mem_range'_1]
      have := SigGolfResearch.T51Top.acc_le c v ha
      omega)]
  rw [← SigGolfResearch.T51Top.freeCountT51_hist, ← List.sum_toFinset _ List.nodup_range']
  apply Finset.sum_congr rfl
  intro c hc
  have hc' := List.mem_range'_1.mp (List.mem_toFinset.mp hc)
  rw [Finset.filter_filter, card_filter_congr' _ (fun v => SigGolfResearch.T51Top.acc c v ∧ ¬ TopChoice.blocked v)
    (fun v => fiber_free c hc'.1 v)]
  exact SigGolfResearch.T51Top.card_acc_free c hc'.1 (by omega)

/-- Campaign T51: the HIGH half is selected with weight `3*2^126 - freeCount` per accepted HIGH word. -/
def topHighWeight : Nat := 3*2^126 - SigGolfResearch.T51Top.freeCountT51

theorem topFreeCount_eq_filter :
    (univ.filter fun v : Digest => topGood v ∧ ¬ TopChoice.blocked v).card = SigGolfResearch.T51Top.freeCountT51 :=
  topFreeCount_eq

theorem freeCount_add_top :
    TopChoice.freeCount topGood + SigGolfResearch.T51Top.freeCountT51 = 3 * 2 ^ 126 := by
  have h := TopChoice.freeCount_add topGood
  rw [topFreeCount_eq_filter] at h
  exact h

/-- Pure arithmetic (keeps `TopChoice.freeCount topGood` abstract for the kernel). -/
theorem highWeight_arith (F : Nat) (h : F + SigGolfResearch.T51Top.freeCountT51 = 3 * 2 ^ 126) :
    F = topHighWeight := by
  unfold topHighWeight
  omega

theorem freeCount_eq_compl : TopChoice.freeCount topGood = topHighWeight :=
  highWeight_arith _ freeCount_add_top

/-- The d6b top selection count at credit `c ≥ floor ≥ 14`: weight `2^128` through LOW (credit `c - 2`),
`topHighWeight` through HIGH (credit `c`). -/
theorem selected_top_path_card (floor c : Nat) (hf : 14 ≤ floor) (hc : floor ≤ c) :
    (univ.filter fun answer : HashOutput => ∃ dl, CanonicalPolicy.producerDecodeOut 0 floor answer = some dl ∧
        CanonicalPolicy.credit 0 dl.2 dl.1 = c).card =
      topWordCount (c - 2) * 2^128 + topHighWeight * topWordCount c := by
  have he : (univ.filter fun answer : HashOutput => ∃ dl, CanonicalPolicy.producerDecodeOut 0 floor answer = some dl ∧
        CanonicalPolicy.credit 0 dl.2 dl.1 = c) =
      (univ.filter fun a : HashOutput => if topGood (a.extractLsb' 0 128) ∨ TopChoice.blocked (a.extractLsb' 0 128)
        then accepted 0 (floor - 2) (fun ds => CanonicalPolicy.credit 0 false ds + 2 = c) (a.extractLsb' 0 128)
        else accepted 0 floor (fun ds => CanonicalPolicy.credit 0 false ds = c) (a.extractLsb' 128 128)) :=
    Finset.filter_congr fun a _ => top_decoder_event floor c (by omega) a
  have hlo : (univ.filter (accepted 0 (floor - 2) (fun ds => CanonicalPolicy.credit 0 false ds + 2 = c))).card =
      topWordCount (c - 2) := by
    have hq : (univ.filter (accepted 0 (floor - 2) (fun ds => CanonicalPolicy.credit 0 false ds + 2 = c))) =
        univ.filter (accepted 0 (floor - 2) (fun ds => CanonicalPolicy.credit 0 false ds = c - 2)) := by
      apply Finset.filter_congr
      intro v _
      unfold accepted
      cases CanonicalPolicy.producerDecodeAt 0 (floor - 2) false v with
      | none => rfl
      | some ds => simp only; omega
    rw [hq, accepted_top_credit_card (floor - 2) (c - 2) (by omega)]
  have hhi : (univ.filter (accepted 0 floor (fun ds => CanonicalPolicy.credit 0 false ds = c))).card =
      topWordCount c := accepted_top_credit_card floor c hc
  have hfree : TopChoice.freeCount topGood = topHighWeight := freeCount_eq_compl
  rw [he, card_choose_path_generic topGood _ _ (fun d h => accepted_topGood (by omega) h), hlo, hhi, hfree]

theorem accepted_top_credit_le {floor credit : Nat} {v : Digest}
    (h : accepted 0 floor (fun ds => CanonicalPolicy.credit 0 false ds = credit) v) : credit ≤ 137 := by
  obtain ⟨ds, hd, hc⟩ := (accepted_iff 0 floor _ v).mp h
  exact SigGolfResearch.T51Top.acc_le credit v
    ((SigGolfResearch.T51Top.acc_iff credit v).mpr ⟨ds, pda_zero_of hd, hc⟩)

theorem producerDecodeAt_top_credit_lt {floor : Nat} (hf : 3 ≤ floor) {low : Bool} {value : Digest}
    {ds : List Nat} (h : CanonicalPolicy.producerDecodeAt 0 floor low value = some ds) :
    CanonicalPolicy.credit 0 low ds < 220 := by
  have ha : accepted 0 0 (fun digits => CanonicalPolicy.credit 0 false digits =
      CanonicalPolicy.credit 0 false ds) value :=
    (accepted_iff 0 0 _ value).mpr ⟨ds, producerDecodeAt_floor_zero (fun _ _ => hf) h, rfl⟩
  have hb := accepted_top_credit_le ha
  rw [CanonicalPolicy.credit_top] at hb ⊢
  cases low <;> simp at hb ⊢ <;> omega

end ClaudeWCT.W9.T3.ProducerV5.Canonical
#print axioms ClaudeWCT.W9.T3.ProducerV5.Canonical.topFreeCount_eq
#print axioms ClaudeWCT.W9.T3.ProducerV5.Canonical.selected_top_path_card
#print axioms ClaudeWCT.W9.T3.ProducerV5.Canonical.producerDecodeAt_top_credit_lt

namespace ClaudeWCT.Numerics.TopZero
open CanonicalCompression hiding topChoiceFree topHighW topCounts topAcceptedHistogram
open CanonicalHistogram hiding topHistogramCheck top_histogram_checked
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 10000000
set_option Elab.async false

/-- Campaign T51: zero-capped top word counts at target 152 by credit (no path bonus), credit ≥ 12, ≤ 7 zero digits
(the checksum included). -/
def topCounts : List (Nat × Nat) := SigGolfResearch.T51Top.topCountsT51

/-- Zero-capped canonical free top words (`|C_L∖B|`, top floor 14). -/
def topChoiceFree : Nat := SigGolfResearch.T51Top.freeCountT51
/-- Weight (over `2^256`) of an accepted HIGH top word: the LOW halves that are neither good nor forced. -/
def topHighW : Nat := 3 * 2 ^ 126 - topChoiceFree

/-- d6b split with the zero cap: LOW (credit `c + 2`, weight `2^128`) or HIGH (credit `c`, weight `topHighW`).
Entries below the top floor 14 never matter. -/
def topAcceptedHistogram : List (Nat × Nat) :=
  topCounts.flatMap fun e => [(e.1 + 2, e.2 * 2 ^ 128), (e.1, e.2 * topHighW)]

def initialBound : Nat := 366648481088737248065818665243608968537

/-- T51 fixed sign cost (PINNED P12, measured): 4 + 112142 + 16 top family pairs + 152 + 12 = 112326 compressions. -/
def fixedSignCost : Nat := 112326

/-- Fixed power for the T51 fixed sign cost 112326. -/
def fixedBound : Nat := 616334705435489293055497825014826663607

theorem initial_checked :
    recurrenceCheck topDen topAcceptedHistogram 14 69 rowOne initialBound = true := by
  decide +kernel

theorem fixed_power_checked :
    powerUp (ceilDiv (zNum * scale) zDen) fixedSignCost ≤ fixedBound := by
  decide +kernel

/-- The T51 signing moment 1.999750417 < 1.99976 (claim 199976, the least integer claim that passes). -/
theorem full_moment_checked :
    mulUp (mulUp fixedBound ftsBound) initialBound * 100000 < 199976 * scale := by
  decide +kernel

/-- Top tail at the 2^20 top counter window (block 256 = 2^20 / 4096), floor 14. -/
theorem top_tail_checked : tailCheck (acceptedMass topAcceptedHistogram 14) topDen 256 = true := by
  decide +kernel

theorem initialBound_ge_scale : scale ≤ initialBound := by norm_num [scale, initialBound]

#print axioms initial_checked
#print axioms fixed_power_checked
#print axioms full_moment_checked
#print axioms top_tail_checked
end ClaudeWCT.Numerics.TopZero

namespace ClaudeWCT.Numerics.TopZero
open CanonicalCompression hiding topChoiceFree topHighW topCounts topAcceptedHistogram
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem fixed_ratio_bound : ((zNum:ℝ)/zDen)^fixedSignCost≤(fixedBound:ℝ)/scale := by
  have hs : (0:ℝ)<scale := by norm_num [scale]
  have hceil := ceilDiv_ratio_le (zNum*scale) zDen (by norm_num [zDen])
  have hc : ((zNum:ℝ)/zDen)≤(ceilDiv (zNum*scale) zDen:ℝ)/scale := by
    apply (le_div_iff₀ hs).mpr
    simpa only [Nat.cast_mul,mul_div_assoc,div_mul_eq_mul_div] using hceil
  have hp := powerUp_ratio_ge (ceilDiv (zNum*scale) zDen) fixedSignCost
  calc
    _ ≤ ((ceilDiv (zNum*scale) zDen:ℝ)/scale)^fixedSignCost := by gcongr
    _ ≤ _ := hp.trans (div_le_div_of_nonneg_right (by exact_mod_cast fixed_power_checked) hs.le)

theorem envelope_ratio_le_two_of (F X : Nat) (hX : X ≤ 200000)
    (hn : mulUp (mulUp F ftsBound) initialBound * 100000 < X * scale) :
    ((F:ℝ)/scale)*(((ftsBound:ℝ)/scale)*((initialBound:ℝ)/scale))≤2 := by
  have hs : (0:ℝ)<scale := by norm_num [scale]
  have hmul2 := mulUp_ratio_ge (mulUp F ftsBound) initialBound
  have hnum : (mulUp (mulUp F ftsBound) initialBound:ℝ)/scale<X/100000 := by
    have hreal : (mulUp (mulUp F ftsBound) initialBound:ℝ)*100000<X*(scale:ℝ) := by exact_mod_cast hn
    apply (div_lt_iff₀ hs).mpr
    nlinarith
  have hX' : (X:ℝ)/100000 ≤ 2 := by
    have : (X:ℝ) ≤ 200000 := by exact_mod_cast hX
    rw [div_le_iff₀ (by norm_num)]
    linarith
  calc
    _ = (((F:ℝ)/scale)*((ftsBound:ℝ)/scale))*((initialBound:ℝ)/scale) := by ring
    _ ≤ ((mulUp F ftsBound:ℝ)/scale)*((initialBound:ℝ)/scale) := by
        gcongr
        exact mulUp_ratio_ge F ftsBound
    _ ≤ _ := hmul2
    _ ≤ 2 := hnum.le.trans hX'

/-- Full moment ≤ 2 (1.99976) for the T51 fixed sign cost 112326 (cap 777, pool 69, floor 14, d6b). -/
theorem envelope_ratio_le_two : ((fixedBound:ℝ)/scale)*
    (((ftsBound:ℝ)/scale)*((initialBound:ℝ)/scale))≤2 :=
  envelope_ratio_le_two_of fixedBound 199976 (by norm_num) full_moment_checked

#print axioms fixed_ratio_bound
#print axioms envelope_ratio_le_two
end ClaudeWCT.Numerics.TopZero
