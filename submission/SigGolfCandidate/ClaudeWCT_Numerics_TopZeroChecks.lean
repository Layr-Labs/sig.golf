import SigGolfCandidate.ClaudeWCT_Numerics_N600PriceChecks

/-! # Top-bytes layer: the top producer zero cap (numerics)
The canonical top producer accepts a word only if at most 9 of its 54 digits are zero
(`ClaudeWCT.WCT9.producerZeroCap 0 = 9`). This module provides
* the zero-fibered packed generating polynomial of the top word statistics (radix `2^136`,
  `zstat = 65536·zeros + 256·weight + score`) and its free-word variant (LOW not forced);
* the exact zero-capped free count `|C_L∖B|` (`zeroFreeCard_eq`);
* the zero-capped moment certificate: top counts (credit ≥ 15, zeros ≤ 9), the d6b split histogram,
  the initial bound, the fixed power (img-v6: 112324) and the full moment (< 2). -/

namespace SigGolfResearch.NonbinaryTop.ZeroCounting
open scoped BigOperators
open Finset Codec Counting EffectiveCounting
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000000
set_option Elab.async false
set_option linter.constructorNameAsVariable false

def zstat5 (first penalized : Bool) (d : Triple5) : Nat := 65536 * zeros5 d + stat5 first penalized d
def zstat8 (d : Triple8) : Nat := 65536 * zeros8 d + stat8 d
def zstat (w : Codec.Word) : Nat :=
  (∑ q : Fin 17, zstat5 (decide (q.val = 0)) (hasPenalty q) (w.1 q)) + zstat8 w.2

theorem zstat_eq (w : Codec.Word) : zstat w = 65536 * zeros w + (256 * weight w + score w) := by
  rw [← stat_eq]
  simp only [zstat, zstat5, zstat8, zeros, stat, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

def zgroup5 (y : Nat) (first penalized : Bool) : Nat := ∑ d : Triple5, y ^ zstat5 first penalized d
def zgroup8 (y : Nat) : Nat := ∑ d : Triple8, y ^ zstat8 d

theorem zweighted_words (y : Nat) :
    (∑ w : Codec.Word, y ^ zstat w) =
      zgroup5 y true true * zgroup5 y false true ^ 11 * zgroup5 y false false ^ 5 * zgroup8 y := by
  rw [Fintype.sum_prod_type]
  simp only [zstat, pow_add]
  rw [← Finset.sum_mul_sum]
  have h : (∑ f : Fin 17 → Triple5,
      y ^ (∑ q : Fin 17, zstat5 (decide (q.val = 0)) (hasPenalty q) (f q))) =
      ∏ q : Fin 17, zgroup5 y (decide (q.val = 0)) (hasPenalty q) := by
    simpa only [zgroup5, ← Finset.prod_pow_eq_pow_sum] using
      (Fintype.prod_sum fun (q : Fin 17) (d : Triple5) =>
        y ^ zstat5 (decide (q.val = 0)) (hasPenalty q) d).symm
  rw [h]
  change (∏ q : Fin 17, zgroup5 y (decide (q.val = 0)) (hasPenalty q)) * zgroup8 y = _
  norm_num [Fin.prod_univ_succ, hasPenalty]
  ring_nf
  simp

/-- The zero-fibered top polynomial: the coefficient of `radix^(65536·z + 256·T + s)` counts the top words
with `z` zero digits, weight `T` and score `s`. -/
def zpacked : Nat := zgroup5 radix true true * zgroup5 radix false true ^ 11 *
  zgroup5 radix false false ^ 5 * zgroup8 radix

/-- The packed weighted sum at the literal radix `2^136` (stated without unfolding `zpacked`). -/
theorem zpacked_weighted : (∑ w : Codec.Word, (2^136 : Nat)^zstat w) = zpacked := by
  rw [show (2:Nat)^136 = radix from rfl]
  exact zweighted_words radix

/-! Free words: LOW is not forced iff the digit of top chain 52 is at least 2 (`EffectiveCounting.freeWord`). -/
abbrev FreeTriple := {d : Triple8 // 2 ≤ (d 1).val}
abbrev FreeWord := (Fin 17 → Triple5) × FreeTriple
def toWord (w : FreeWord) : Codec.Word := (w.1, w.2.val)

theorem toWord_injective : Function.Injective toWord := by
  intro a b h
  simp only [toWord, Prod.mk.injEq] at h
  exact Prod.ext h.1 (Subtype.ext h.2)

theorem free_card_small : Fintype.card FreeWord < radix - 1 :=
  (Fintype.card_le_of_injective toWord toWord_injective).trans_lt word_card_small

def zfgroup8 (y : Nat) : Nat := ∑ d : FreeTriple, y ^ zstat8 d.val

theorem zfree_weighted_words (y : Nat) :
    (∑ w : FreeWord, y ^ zstat (toWord w)) =
      zgroup5 y true true * zgroup5 y false true ^ 11 * zgroup5 y false false ^ 5 * zfgroup8 y := by
  rw [Fintype.sum_prod_type]
  simp only [toWord, zstat, pow_add]
  rw [← Finset.sum_mul_sum]
  have h : (∑ f : Fin 17 → Triple5,
      y ^ (∑ q : Fin 17, zstat5 (decide (q.val = 0)) (hasPenalty q) (f q))) =
      ∏ q : Fin 17, zgroup5 y (decide (q.val = 0)) (hasPenalty q) := by
    simpa only [zgroup5, ← Finset.prod_pow_eq_pow_sum] using
      (Fintype.prod_sum fun (q : Fin 17) (d : Triple5) =>
        y ^ zstat5 (decide (q.val = 0)) (hasPenalty q) d).symm
  rw [h]
  change (∏ q : Fin 17, zgroup5 y (decide (q.val = 0)) (hasPenalty q)) * zfgroup8 y = _
  norm_num [Fin.prod_univ_succ, hasPenalty]
  ring_nf
  simp

def zfpacked : Nat := zgroup5 radix true true * zgroup5 radix false true ^ 11 *
  zgroup5 radix false false ^ 5 * zfgroup8 radix

theorem zfree_truncated_card (cut : Nat) (hc : 0 < cut) :
    (univ.filter fun w : FreeWord => zstat (toWord w) < cut).card =
      (zfpacked % radix ^ cut) % (radix - 1) := by
  classical
  unfold zfpacked
  rw [← zfree_weighted_words radix]
  symm
  rw [SigGolfResearch.Gate6.mod_pow_sum_generic hc _ (fun w : FreeWord => zstat (toWord w))
      (by simpa only [Finset.card_univ] using Nat.lt_of_lt_of_le free_card_small (Nat.sub_le _ _)),
    SigGolfResearch.Gate6.sum_pow_mod_pred_generic (by norm_num [radix]),
    Nat.mod_eq_of_lt ((Finset.card_filter_le _ _).trans_lt (by simpa using free_card_small))]

def zfreeWindow (z : Nat) : Nat :=
  (zfpacked % radix ^ (65536*z+256*146+256)) % (radix - 1) -
  (zfpacked % radix ^ (65536*z+256*146+32)) % (radix - 1)

theorem zfree_window_card (z : Nat) :
    (univ.filter fun w : FreeWord => weight (toWord w) = 146 ∧ 32 ≤ score (toWord w) ∧
      zeros (toWord w) = z).card = zfreeWindow z := by
  classical
  have heq : (univ.filter fun w : FreeWord => weight (toWord w) = 146 ∧ 32 ≤ score (toWord w) ∧
        zeros (toWord w) = z) =
      (univ.filter fun w : FreeWord => zstat (toWord w) < 65536*z+256*146+256) \
        (univ.filter fun w : FreeWord => zstat (toWord w) < 65536*z+256*146+32) := by
    ext w
    have hc := score_le (toWord w)
    have hw := weight_le_225 (toWord w)
    have he := zstat_eq (toWord w)
    simp only [mem_filter, mem_univ, true_and, mem_sdiff]
    omega
  rw [heq, card_sdiff_of_subset]
  · exact congrArg₂ Nat.sub (zfree_truncated_card _ (by omega)) (zfree_truncated_card _ (by omega))
  · intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw ⊢
    omega

theorem toWord_mk (v : Codec.Word) (h : freeWord v) : toWord (v.1, ⟨v.2, h⟩) = v := rfl

theorem free_card_transfer (P : Codec.Word → Prop) [DecidablePred P] :
    (univ.filter fun w : Codec.Word => P w ∧ freeWord w).card =
      (univ.filter fun w : FreeWord => P (toWord w)).card := by
  symm
  apply Finset.card_bij (fun w _ => toWord w)
  · intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw ⊢
    exact ⟨hw, w.2.2⟩
  · intro a _ b _ h
    exact toWord_injective h
  · intro v hv
    simp only [mem_filter, mem_univ, true_and] at hv
    refine ⟨(v.1, ⟨v.2, hv.2⟩), ?_, toWord_mk v hv.2⟩
    simp only [mem_filter, mem_univ, true_and, toWord_mk v hv.2]
    exact hv.1

theorem zeroFreeCard_windows : zeroFreeCard = ∑ z ∈ range 10, zfreeWindow z := by
  classical
  have h1 : zeroFreeCard = (univ.filter fun w : Codec.Word =>
      (weight w = 146 ∧ 32 ≤ score w ∧ zeros w ≤ 9) ∧ freeWord w).card := by
    unfold zeroFreeCard
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro w _
    constructor
    · rintro ⟨a, b, c, d⟩; exact ⟨⟨a, b, d⟩, c⟩
    · rintro ⟨⟨a, b, d⟩, c⟩; exact ⟨a, b, c, d⟩
  rw [h1, free_card_transfer]
  rw [card_eq_sum_card_fiberwise (f := fun w : FreeWord => zeros (toWord w))
      (s := univ.filter fun w : FreeWord =>
        weight (toWord w) = 146 ∧ 32 ≤ score (toWord w) ∧ zeros (toWord w) ≤ 9)
      (t := range 10) (by
    intro w hw
    change w ∈ (univ.filter fun w : FreeWord =>
      weight (toWord w) = 146 ∧ 32 ≤ score (toWord w) ∧ zeros (toWord w) ≤ 9) at hw
    change zeros (toWord w) ∈ range 10
    simp only [mem_filter, mem_univ, true_and] at hw
    simp only [mem_range]
    omega)]
  apply sum_congr rfl
  intro z hz
  rw [← zfree_window_card z]
  apply congrArg Finset.card
  ext w
  simp only [mem_filter, mem_univ, true_and]
  have := mem_range.mp hz
  constructor
  · rintro ⟨⟨h1, h2, _⟩, h4⟩
    exact ⟨h1, h2, h4⟩
  · rintro ⟨h1, h2, h4⟩
    exact ⟨⟨h1, h2, by omega⟩, h4⟩

/-- `|C_L∖B|` with the zero cap: top words of weight 146, score ≥ 32 (floor 22, d6b LOW bonus 2), LOW not forced, ≤ 9 zero digits. -/
def zeroFreeCount : Nat := 59170261448886803489697968615038982

theorem zfree_windows_eq : (∑ z ∈ range 10, zfreeWindow z) = zeroFreeCount := by
  decide +kernel

theorem zeroFreeCard_eq : zeroFreeCard = zeroFreeCount :=
  zeroFreeCard_windows.trans zfree_windows_eq

#print axioms zeroFreeCard_eq
end SigGolfResearch.NonbinaryTop.ZeroCounting

namespace ClaudeWCT.Numerics.TopZero
open CanonicalCompression hiding topChoiceFree topHighW topCounts topAcceptedHistogram
open CanonicalHistogram hiding topHistogramCheck top_histogram_checked
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 10000000
set_option Elab.async false

/-- Zero-capped top word counts at target 146 by credit (`score = credit + 12`), credit ≥ 15, ≤ 9 zero digits. -/
def topCounts : List (Nat × Nat) := [(15,254454868345687844046530995737173),(16,395128924041581076208696123100881),(17,584559070444546010192814901796421),(18,827503787637773066008591477256262),(19,1124886722773366575268314049215977),(20,1472729956473700827669937397560224),(21,1861687900689856355065908041711403),(22,2277196206631366277074304988726337),(23,2700192643799800966852552738354924),(24,3108566742753244606763909514515669),(25,3479268303244682013836160976502264),(26,3790523314538125336957069684214701),(27,4023812806996004350095213325317354),(28,4165684908687251794095985785507651),(29,4209132743646785815037331109296086),(30,4153995813204262603765085856002001),(31,4006519916824402189675249161253972),(32,3778538122722706617615991186296089),(33,3486163996977921222931090334775470),(34,3147924447761675410038432087153590),(35,2782922224282744073246904806315589),(36,2409405826856677347161115987289540),(37,2043507446141571468439449202164602),(38,1698234475588566246924460263377995),(39,1383063252174583904541554230214566),(40,1104014918425978758392571533021140),(41,863883314068552511205269391596383),(42,662685587900404789571302070552061),(43,498353621280585954339863999205141),(44,367417497325178865623842069023470),(45,265565990526854848813319789036887),(46,188162849929798608348152659482904),(47,130677962286059409114416739139572),(48,88950728987854464868223084611030),(49,59335089171038305072047627009895),(50,38778315188886037547152019048516),(51,24826247420341602401959052750766),(52,15567119964133578774610252110494),(53,9557622815494594463281278582708),(54,5743802605669245296957935086903),(55,3378123584276502695116092671685),(56,1943814272993629228003408084101),(57,1093796796193822078668712312094),(58,601706301587397814455608478229),(59,323520026839738102823470278194),(60,169929782518337814197613891145),(61,87142530003352801076080343371),(62,43619018038291306017761239073),(63,21302160897672517008335582561),(64,10140980499960185054363757279),(65,4702966575958947477312162085),(66,2124056008785968384403632374),(67,933260446417219926043052410),(68,398319125213838242871568601),(69,165058920017514313706245583),(70,66343409142118036856993464),(71,25801425491160654945226676),(72,9691503645309855609931928),(73,3513897534435079157889933),(74,1226135268650021847267690),(75,409876087556538468457743),(76,131161531497775494253614),(77,40068153371484216179147),(78,11599176511165632226123),(79,3163955650966675155206),(80,813497463244243895084),(81,195267239231240604186),(82,42958048446034025293),(83,8717035194309020139),(84,1603478789067385406),(85,260107413423084348),(86,36291192407977727),(87,4289982798688672),(88,482986488145722),(89,38831502615447),(90,1331387465760),(91,18646071774),(92,2292737436),(93,88996380)]

/-- The zero-capped counts are the sums over the zero fibers `z = 0..9` of the weight-146 coefficients of the
zero-fibered top polynomial. -/
def topHistogramCheck : Bool :=
  let p := SigGolfResearch.NonbinaryTop.ZeroCounting.zpacked
  let actual := (List.range 10).foldl (fun s zeros =>
    s + ((p >>> (136 * (65536 * zeros + 256 * 146 + 27))) % 2 ^ (136 * 205))) 0
  decide (packHistogram 136 15 205 topCounts = actual)

theorem top_histogram_checked : topHistogramCheck = true := by decide +kernel

theorem top_histogram_digits : ∀ c : Fin 205,
    coefficient 136 (packHistogram 136 15 205 topCounts) c.val =
      histogramWeight topCounts (c.val+15) := by decide +kernel
#print axioms top_histogram_checked

/-- Zero-capped canonical free top words (`|C_L∖B|`). -/
def topChoiceFree : Nat := SigGolfResearch.NonbinaryTop.ZeroCounting.zeroFreeCount
/-- Weight (over `2^256`) of an accepted HIGH top word: the LOW halves that are neither good nor forced. -/
def topHighW : Nat := 3 * 2 ^ 126 - topChoiceFree

/-- d6b split with the zero cap: LOW (credit `c + 2`, weight `2^128`) or HIGH (credit `c`, weight `topHighW`).
Entries below the top floor 22 never matter. -/
def topAcceptedHistogram : List (Nat × Nat) :=
  topCounts.flatMap fun e => [(e.1 + 2, e.2 * 2 ^ 128), (e.1, e.2 * topHighW)]

def initialBound : Nat := 366685143351398408834324695003550351732

/-- img-v6 fixed sign cost (opus-crumbs PORT v6 C): 112324 compressions. -/
def fixedSignCost : Nat := 112324

/-- Fixed power for the img-v6 fixed sign cost 112324. -/
def fixedBound : Nat := 616328186735326113110974222695394189508

theorem initial_checked :
    recurrenceCheck topDen topAcceptedHistogram 22 77 rowOne initialBound = true := by
  decide +kernel

theorem fixed_power_checked :
    powerUp (ceilDiv (zNum * scale) zDen) fixedSignCost ≤ fixedBound := by
  decide +kernel

theorem full_moment_checked :
    mulUp (mulUp fixedBound ftsBound) initialBound * 100000 < 200000 * scale := by
  decide +kernel

/-- Top tail at the 2^20 top counter window (block 256 = 2^20 / 4096), floor 22. -/
theorem top_tail_checked : tailCheck (acceptedMass topAcceptedHistogram 22) topDen 256 = true := by
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

/-- Full moment ≤ 2 (approximately 1.9999293) for the img-v6 fixed sign cost 112324 (cap 777, pool 77, floor 22, d6b). -/
theorem envelope_ratio_le_two : ((fixedBound:ℝ)/scale)*
    (((ftsBound:ℝ)/scale)*((initialBound:ℝ)/scale))≤2 :=
  envelope_ratio_le_two_of fixedBound 200000 (by norm_num) full_moment_checked

#print axioms fixed_ratio_bound
#print axioms envelope_ratio_le_two
end ClaudeWCT.Numerics.TopZero
