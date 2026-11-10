import SigGolfCandidate.Merge040
set_option debug.skipKernelTC true
set_option linter.all false

-- ==== merged from ClaudeWCT_Numerics_TopZeroChecks ====
section

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
def topCountsT51 : List (Nat × Nat) := [(12,229422744315677625956884431363989),(13,373366367435532868890245256619134),(14,571404616176976902492946760976038),(15,827875674929964943170650834997466),(16,1141940228531676081371408376597889),(17,1506523563371124109799061161322526),(18,1907727235961469130025537497156057),(19,2325535011954626580529728614872844),(20,2735913589629744625320672412046241),(21,3113171115363979385189631461277700),(22,3432202122673243400133284652025820),(23,3671364839078079014874733412270921),(24,3815377843816683370556200596322877),(25,3856585583036085048495769070475836),(26,3794936799484314271168484023760576),(27,3637975477467931621099726287822997),(28,3400068260618406898007183078472438),(29,3099991948884401435690821601623982),(30,2758412008329867120888836165375163),(31,2396313082796977183848344384807205),(32,2033289136405986506513393542580628),(33,1685609305370973455474183424109288),(34,1365427434225287595723527662872892),(35,1080958313386102206506022835823683),(36,836533048095671822543380546117000),(37,632864332563931540389394191953677),(38,468008750652997035448087631818200),(39,338338494618364229065773984682952),(40,239135054784264584145770717610936),(41,165210225149556536123984617115001),(42,111543924009957793029367870261741),(43,73605433266289080037909317231236),(44,47465460953688051482011338307925),(45,29897738180599907058173548666906),(46,18391888820399473829225224451065),(47,11050693105675549422198287427184),(48,6481915884724992691065219346554),(49,3709174024993528191980077512133),(50,2070989439452237600396416282338),(51,1128143137028504336506195334225),(52,598857243672947826876794991063),(53,309654803468988607389588692044),(54,156063782726181304681957340501),(55,76583700498038393019644329415),(56,36526969213690294513566352471),(57,16948380970302682667304325152),(58,7653380181945929901245644479),(59,3352309430364175787975898645),(60,1423386779480332522149740288),(61,587748873098241691425146591),(62,235270643075359560708796428),(63,90804137878969951146188189),(64,33978940839565761240307626),(65,12352629946696959651851362),(66,4306401022394068480534451),(67,1442538940095881445340952),(68,471659779247495719668423),(69,147852036155870763691004),(70,43672393731101486059523),(71,12609482021494900948039),(72,3545641609240553733692),(73,911321134588956528971),(74,224614503792540313007),(75,56540318889174244403),(76,12619647507582436930),(77,2479819028486668782),(78,546120549135174746),(79,109620685285910004),(80,16000249651839764),(81,2904149570095592),(82,544373267134158),(83,44340455540268),(84,4767115931634),(85,1367670346336),(86,121038590736),(87,875923776),(88,322545216)]
/-- The same restricted to words whose LOW half is not forced (r6 group 8 rank `≥ 64`). -/
def topFreeCountsT51 : List (Nat × Nat) := [(12,206051117236290189800657820964677),(13,334669146661090045356207018415321),(14,511138686870962503299896499289791),(15,739003683971550323971938155678961),(16,1017141848315034090559985043555720),(17,1338872759690824052810807481522903),(18,1691505029841364445212136264739329),(19,2057037691028690685753361246361202),(20,2414082257701522771393351323782430),(21,2739994877905090766877833695107336),(22,3012888702087810748639455268547969),(23,3214161344206829691399368432665270),(24,3330988174223641211810318955046816),(25,3357361436545912591368540190842131),(26,3293995039006593149122970571129612),(27,3148218322123029941633270182480627),(28,2933198810438599758027466652563699),(29,2665776767292851264025398620163392),(30,2364240876302167912904198814898974),(31,2046939223572419458136910862390230),(32,1730799956006520016530783683713402),(33,1429706268744178580083771872357581),(34,1153867744603645196437108582278035),(35,910013883961171928334518446736906),(36,701496137927464344124206168038016),(37,528573805911149379702367209378670),(38,389270149057886368704873667167468),(39,280218992978702288942440652641871),(40,197188536928652229106288554225283),(41,135615575038341893741574714477992),(42,91136822905297923475375432767414),(43,59850766577915533648788047675413),(44,38404463637560605400670384456365),(45,24066810188027216766985225972092),(46,14726922549368705219857695120612),(47,8800394594835526870693952040936),(48,5132881347242300796291438061393),(49,2920109826031398381000705648405),(50,1620596491713352091147002575488),(51,877276456987077751761599109024),(52,462670961137781274687677259115),(53,237630955260255418650684145393),(54,118928223790710698195586399682),(55,57936209056641634747692034770),(56,27424580085168422745076584143),(57,12625052161510473759577601466),(58,5654229004836592911078589483),(59,2455417156925132059012585861),(60,1033281638558677399785335342),(61,422673840093110708572765483),(62,167525387295921539462234188),(63,63994832454096132096022926),(64,23690205953529432100156183),(65,8513996478078424654508626),(66,2932573263382319575163619),(67,970149740177609976534338),(68,313012187110758074325616),(69,96723988966074131388912),(70,28150853209084020281919),(71,8004076900418413917509),(72,2212580212178782106422),(73,558473262409158315504),(74,135238239896804464259),(75,33381773235471115559),(76,7279911844055941103),(77,1399573793077619274),(78,301832852472499518),(79,58865038531768714),(80,8356603624638797),(81,1488790351163318),(82,267950092831904),(83,20493660124272),(84,2243469038454),(85,619210072495),(86,50925893655),(87,329325360),(88,125007120)]

theorem histCheck_all : histCheck topCountsT51 false = true := by decide +kernel
theorem histCheck_free : histCheck topFreeCountsT51 true = true := by decide +kernel


/-- `|C_L∖B|`: canonical top words that are LOW-good (credit ≥ 12, i.e. floor 14 with the LOW bonus 2) and whose LOW
half is not forced. -/
def freeCountT51 : Nat := 48331618305674191902401536030000308
theorem freeCountT51_hist : ((List.range' 16 122).map (histW topFreeCountsT51)).sum = freeCountT51 := by
  decide +kernel
theorem topCountsT51_lt : ∀ e ∈ topCountsT51, e.1 < 138 := by decide
theorem histW_eq_zero (h : List (Nat × Nat)) (c : Nat) (hc : ∀ e ∈ h, e.1 ≠ c) : histW h c = 0 := by
  unfold histW
  induction h with
  | nil => rfl
  | cons e t ih =>
    rw [List.map_cons, List.sum_cons, if_neg (hc e (by simp)), Nat.zero_add]
    exact ih (fun e' he' => hc e' (by simp [he']))

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
    · rintro ⟨h1, h2 | h2 | ⟨_, _, _, h3⟩⟩
      · omega
      · omega
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
      · rintro ⟨h1, h2 | h2 | ⟨_, h2, _⟩⟩
        · exact ⟨by simp; omega, h1⟩
        · omega
        · omega
      · rintro ⟨h1, h2⟩; exact ⟨h2, Or.inl (by simp at h1; omega)⟩
    · apply ind_congr; unfold safeZeroCopy
      rw [a1, m1, show 3 * g.val + 1 - 1 = 3 * g.val by omega, a0, m0]
      simp only [decide_eq_true_eq]
      constructor
      · rintro ⟨h1, h2 | h2 | ⟨_, _, _, h3⟩⟩
        · omega
        · exact ⟨h1, Or.inl (by omega)⟩
        · exact ⟨h1, Or.inr h3⟩
      · rintro ⟨h1, h2 | h2⟩
        · exact ⟨h1, Or.inr (Or.inl (by omega))⟩
        · exact ⟨h1, Or.inr (Or.inr ⟨by omega, by omega, by omega, h2⟩)⟩
    · apply ind_congr; unfold safeZeroCopy
      rw [a2, m2, show 3 * g.val + 2 - 1 = 3 * g.val + 1 by omega, a1, m1]
      constructor
      · rintro ⟨h1, h2 | h2 | ⟨_, _, _, h3⟩⟩
        · omega
        · omega
        · exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, Or.inr (Or.inr ⟨by omega, by omega, by omega, h2⟩)⟩
  · apply Finset.sum_congr rfl; intro j _
    obtain ⟨a0, a1, a2, m0, m1, m2⟩ := blk5 w chk j
    have hj := j.isLt
    unfold tcopies
    congr 1; congr 1
    · apply ind_congr; unfold safeZeroCopy; rw [a0, m0]
      constructor
      · rintro ⟨h1, h2 | h2 | ⟨_, h2, _⟩⟩
        · omega
        · omega
        · omega
      · rintro ⟨h1, _⟩; exact absurd h1 (by simp)
    · apply ind_congr; unfold safeZeroCopy
      rw [a1, m1, show 3 * (9 + j.val) + 1 - 1 = 3 * (9 + j.val) by omega, a0, m0]
      simp only [Bool.false_eq_true, false_or]
      constructor
      · rintro ⟨h1, h2 | h2 | ⟨_, _, _, h3⟩⟩
        · omega
        · omega
        · exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, Or.inr (Or.inr ⟨by omega, by omega, by omega, h2⟩)⟩
    · apply ind_congr; unfold safeZeroCopy
      rw [a2, m2, show 3 * (9 + j.val) + 2 - 1 = 3 * (9 + j.val) + 1 by omega, a1, m1]
      constructor
      · rintro ⟨h1, h2 | h2 | ⟨_, _, _, h3⟩⟩
        · omega
        · omega
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
    have hlr : ∀ ds, CanonicalPolicy.ladderReward 0 ds = 0 := fun _ => by simp [CanonicalPolicy.ladderReward]
    simp only [CanonicalPolicy.pathReward, CanonicalPolicy.reward, CanonicalPolicy.pathBonus_false, Nat.add_zero,
      CanonicalPolicy.credit, dispatchPenalty, if_true, canonicalZeroBound, producerZeroCap, producerRankBound,
      true_or, and_true, hlr]
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
theorem topGood_iff (v : Digest) : topGood v ↔ accepted 0 16 (fun _ => True) v := by
  unfold topGood
  rw [show CanonicalPolicy.topFloor = 18 from rfl, producerDecodeAt_top_true 18 (by decide), accepted_iff]
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
    accepted 0 16 (fun _ => True) v ↔ ∃ c, 16 ≤ c ∧ SigGolfResearch.T51Top.acc c v := by
  rw [accepted_iff]
  constructor
  · rintro ⟨ds, hd, -⟩
    have hc := CanonicalPolicy.producerDecodeAt_credit hd
    exact ⟨_, hc, (SigGolfResearch.T51Top.acc_iff _ v).mpr ⟨ds, pda_zero_of hd, rfl⟩⟩
  · rintro ⟨c, hc, ha⟩
    have h := (accepted_credit_floor_iff 16 c hc v).mpr ((accepted_credit_acc c v).mpr ha)
    obtain ⟨ds, hd, -⟩ := (accepted_iff _ _ _ v).mp h
    exact ⟨ds, hd, trivial⟩

theorem fiber_free (c : Nat) (hc : 16 ≤ c) (v : Digest) :
    ((accepted 0 16 (fun _ => True) v ∧ ¬ TopChoice.blocked v) ∧ creditOf v = c) ↔
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
  rw [card_filter_congr' _ (fun v => accepted 0 16 (fun _ => True) v ∧ ¬ TopChoice.blocked v)
    (fun v => and_congr_left' (topGood_iff v))]
  rw [SigGolfResearch.T51Top.fiber_card_filter (fun v => accepted 0 16 (fun _ => True) v ∧ ¬ TopChoice.blocked v)
    creditOf (List.range' 16 122).toFinset (fun v hv => by
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
  exact SigGolfResearch.T51Top.card_acc_free c (by omega) (by omega)

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
theorem selected_top_path_card (floor c : Nat) (hf : 18 ≤ floor) (hc : floor ≤ c) :
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

/-- Exact upward-rounded initial bound for the revised top-copy law at pool 72, top floor 18 (Z7: R1 law and f25ef952 L1/L2 floors). -/
def initialBound : Nat := 366955953512426661266192607702299586245

/-- T51 fixed sign cost (PINNED P12, measured): 4 + 112142 + 16 top family pairs + 152 + 12 = 112326 compressions. -/
def fixedSignCost : Nat := 112326

/-- Fixed power for the T51 fixed sign cost 112326. -/
def fixedBound : Nat := 616334705435489293055497825014826663607

theorem initial_checked :
    recurrenceCheck topDen topAcceptedHistogram 18 72 rowOne initialBound = true := by
  decide +kernel

theorem fixed_power_checked :
    powerUp (ceilDiv (zNum * scale) zDen) fixedSignCost ≤ fixedBound := by
  decide +kernel

/-- Revised top-copy law at pool 67: a conservative legacy signing-moment bound. -/
theorem full_moment_checked :
    mulUp (mulUp fixedBound ftsBound) initialBound * 100000 < 199999 * scale := by
  decide +kernel

/-- Top tail at the 2^20 top counter window (block 256 = 2^20 / 4096), floor 14. -/
theorem top_tail_checked : tailCheck (acceptedMass topAcceptedHistogram 18) topDen 256 = true := by
  decide +kernel

theorem initialBound_ge_scale : scale ≤ initialBound := by norm_num [scale, initialBound]

/-- E8 (P1) fixed sign cost: the T51 cost 112326 minus the first trial of each of the 90 lower and 72 FTS ground nodes;
Y5: and of the 64 heap-16..31 FTS ground nodes (coordinates 0..3). -/
def fixedSignCostU16 : Nat := 112088

/-- Fixed power for the Y5 fixed sign cost 112088. -/
def fixedBoundU16 : Nat := 615559463982217984050911006729266188597

/-- Ground node factors `m_b` (over `2^128`, `b = 1, 2, 3, 4`): rounded-up `z p / (1 - z (1 - p))`, `p = 2^-b`,
for the sign `z = zNum/zDen` (equal to `keygenM 3, 4, 5`). -/
def groundM (b : Nat) : Nat :=
  if b = 1 then 340285965984933645675468342432275971788
  else if b = 2 then 340289565125062062546873124227847124433
  else if b = 3 then 340296763633728263433442488925276359072
  else 340311161564765781666276742203532247926

/-- Z3, Y5: the 226 ground nodes (N7g-B, soispoke f25ef952): 128 with `b = 1`, 80 with `b = 2`, 12 with `b = 3`, 6 with
`b = 4` (lower (4,3,2,1) × 3: 48 / 24 / 12 / 6; FTS heap 8..15: 16 / 56; Y5 FTS heap 16..31 of coordinates 0..3: 64). -/
def groundBound : Nat :=
  mulUp (powerUp (groundM 1) 128) (mulUp (powerUp (groundM 2) 80) (mulUp (powerUp (groundM 3) 12) (powerUp (groundM 4) 6)))

theorem fixed_power_checked_U16 :
    powerUp (ceilDiv (zNum * scale) zDen) fixedSignCostU16 ≤ fixedBoundU16 := by
  decide +kernel

/-- Z4 (Z3 + P1' L3 bonus 3) on the revised top-copy law: pool 72, top floor 18, gate 929, R1 law, joint cost ≤ 776, lower E11 V29 + 72 FTS ground nodes; Y5: hint trim (radix 360) + 64 heap-16..31 FTS ground nodes: signing moment
< 1.99990 (claim 199990). -/
theorem full_moment_checked_U16 :
    mulUp (mulUp (mulUp fixedBoundU16 groundBound) ftsBound) initialBound * 100000 < 199990 * scale := by
  decide +kernel

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
  envelope_ratio_le_two_of fixedBound 199999 (by norm_num) full_moment_checked

/-- Geometric retry step for a ground node with `b ∈ {1,2,3}` zero bits, at the sign `z = zNum/zDen`. -/
theorem groundM_step_z (b : Nat) (hb1 : 1 ≤ b) (hb3 : b ≤ 4) :
    (zNum:ℝ)/zDen * (1/2^b + (1 - 1/2^b) * ((groundM b:ℝ)/scale)) ≤ (groundM b:ℝ)/scale ∧
      (zNum:ℝ)/zDen ≤ (groundM b:ℝ)/scale := by
  interval_cases b <;> norm_num [groundM, zNum, zDen, scale]

theorem groundM_step (b : Nat) (hb1 : 1 ≤ b) (hb3 : b ≤ 4) (z : ℝ) (hz : z ≤ (zNum:ℝ)/zDen) :
    z * (1/2^b + (1 - 1/2^b) * ((groundM b:ℝ)/scale)) ≤ (groundM b:ℝ)/scale ∧ z ≤ (groundM b:ℝ)/scale := by
  obtain ⟨h1, h2⟩ := groundM_step_z b hb1 hb3
  have hq : (1:ℝ)/2^b ≤ 1 := by
    rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  have hp : 0 ≤ (1:ℝ)/2^b + (1 - 1/2^b) * ((groundM b:ℝ)/scale) := by
    have : 0 ≤ 1 - (1:ℝ)/2^b := by linarith
    positivity
  exact ⟨(mul_le_mul_of_nonneg_right hz hp).trans h1, hz.trans h2⟩

theorem fixed_ratio_bound_U16 : ((zNum:ℝ)/zDen)^fixedSignCostU16≤(fixedBoundU16:ℝ)/scale := by
  have hs : (0:ℝ)<scale := by norm_num [scale]
  have hceil := ceilDiv_ratio_le (zNum*scale) zDen (by norm_num [zDen])
  have hc : ((zNum:ℝ)/zDen)≤(ceilDiv (zNum*scale) zDen:ℝ)/scale := by
    apply (le_div_iff₀ hs).mpr
    simpa only [Nat.cast_mul,mul_div_assoc,div_mul_eq_mul_div] using hceil
  have hp := powerUp_ratio_ge (ceilDiv (zNum*scale) zDen) fixedSignCostU16
  calc
    _ ≤ ((ceilDiv (zNum*scale) zDen:ℝ)/scale)^fixedSignCostU16 := by gcongr
    _ ≤ _ := hp.trans (div_le_div_of_nonneg_right (by exact_mod_cast fixed_power_checked_U16) hs.le)

/-- N7g (B): the ground factor with widths 128 / 80 (Y5; N7g: 64 / 80 / 12 / 6 (b = 1, 2, 3, 4)). -/
theorem groundBound_ratio_ge :
    ((groundM 1:ℝ)/scale)^128 * (((groundM 2:ℝ)/scale)^80 * (((groundM 3:ℝ)/scale)^12 * ((groundM 4:ℝ)/scale)^6)) ≤
      (groundBound:ℝ)/scale := by
  unfold groundBound
  calc
    _ ≤ ((groundM 1:ℝ)/scale)^128 * ((powerUp (groundM 2) 80:ℝ)/scale * ((powerUp (groundM 3) 12:ℝ)/scale *
          ((powerUp (groundM 4) 6:ℝ)/scale))) := by
        gcongr
        · exact powerUp_ratio_ge _ _
        · exact powerUp_ratio_ge _ _
        · exact powerUp_ratio_ge _ _
    _ ≤ ((groundM 1:ℝ)/scale)^128 * ((powerUp (groundM 2) 80:ℝ)/scale *
          ((mulUp (powerUp (groundM 3) 12) (powerUp (groundM 4) 6):ℝ)/scale)) := by
        gcongr
        exact mulUp_ratio_ge _ _
    _ ≤ (powerUp (groundM 1) 128:ℝ)/scale *
          ((mulUp (powerUp (groundM 2) 80) (mulUp (powerUp (groundM 3) 12) (powerUp (groundM 4) 6)):ℝ)/scale) := by
        gcongr
        · exact powerUp_ratio_ge _ _
        · exact mulUp_ratio_ge _ _
    _ ≤ _ := mulUp_ratio_ge _ _

/-- U16b full moment ≤ 2 (1.99931): fixed `z^112236`, the 90 ground node factors, FTS and the initial bound. -/
theorem envelope_ratio_le_two_U16 : (((fixedBoundU16:ℝ)/scale)*((groundBound:ℝ)/scale))*
    (((ftsBound:ℝ)/scale)*((initialBound:ℝ)/scale))≤2 := by
  have hm := mulUp_ratio_ge fixedBoundU16 groundBound
  have he := envelope_ratio_le_two_of (mulUp fixedBoundU16 groundBound) 199990 (by norm_num)
    full_moment_checked_U16
  have h0 : (0:ℝ) ≤ ((ftsBound:ℝ)/scale)*((initialBound:ℝ)/scale) :=
    mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  exact (mul_le_mul_of_nonneg_right hm h0).trans he

end ClaudeWCT.Numerics.TopZero
end
