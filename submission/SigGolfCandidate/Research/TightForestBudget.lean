import SigGolfCandidate.ClaudeWCT.WCT9.Forest
import SigGolfCandidate.ClaudeWCT.WCT9.Cost
import SigGolfCandidate.ClaudeWCT.W9.T3M.SigCodecC
import SigGolfCandidate.ClaudeWCT.W9.T3.FullCache.NativeBudgetB1_EnvelopesV5

/-!
Research-only budget refinement for the *unchanged* signing program.
Imported by Solution only for the r42 hosted elaboration probe; the certified
scheme is unchanged. Compilation is delegated to the hosted verifier.
The existing forestRows bound is 31329; signForest now returns those rows
without a forestPk hash. The historical 31334 bound therefore has five spare
compressions. This lemma does NOT establish the 51-compression cap773 target.
-/

namespace ClaudeWCT.WCT9.Research
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Cost

/-- Tighten the existing FTS-specific bound without changing its query policy. -/
theorem ftsBound_signForest_tight (index : Nat) (output : HashOutput) :
    Bound (FtsQuery index)
      (fun result : List Opening × (Digest × Digest) => result.1.length = 9)
      31329 (signForest index output) := by
  unfold signForest
  exact (ftsBound_forestRows index output).bind' (l := 0)
    (fun state hstate => .pure _ 0 hstate.1) (by decide)

/-- The same five-compression refinement under the admitted query policy. -/
theorem bound_signForest_tight (index : Nat) (output : HashOutput) :
    CBound (fun result : List Opening × (Digest × Digest) => result.1.length = 9)
      31329 (signForest index output) :=
  cbound_of_ftsBound (ftsBound_signForest_tight index output)

end ClaudeWCT.WCT9.Research

/-! This rational obstruction tests the retained cubic envelope family only.
`topPUpper` is the generic quarter-selector upper rate at the known raw count;
even replacing the top factor by this optimistic rate cannot close cap773 at
gate1316 after taking the five forest compressions. No exact count of the
blocked/good intersection is assumed, and no changed machine is proposed. -/
namespace SigGolfResearch.Cap773TopOnlyObstruction
open ClaudeWCT.W9.T3.BaseAudit

def z : ℚ := 1 / (1 - 6931471808 / (10000000000 * 131072))
def cap773J : ℕ := 50909050606799227590778865501806642546081792
def digestP : ℚ := 1316 * cap773J / 2^167
def topN : ℕ := 61400435184999209708243105926444986
def topPUpper : ℚ := (topN : ℚ) * (7 * 2^126) / 2^256
def geom (p : ℚ) : ℚ := z * p / (1 - z + z * p)
def cubicAllowance (fixed : ℕ) : ℚ :=
  let x : ℚ := (6931471803 / 10000000000) * ((131072 : ℚ) - fixed) / 131072
  1 + x + x^2 / 2 + x^3 / 6

/-- Positivity needed to use the infinite-geometric lower factors. -/
theorem geom_denominators_pos :
    0 < 1 - z + z * digestP ∧ 0 < 1 - z + z * topPUpper := by
  norm_num [z, digestP, cap773J, topPUpper, topN]

/-- Arithmetic failure even at the optimistic top rate; not a universal
impossibility result for other moment methods or lower-layer changes. -/
theorem optimistic_top_still_exceeds_cubic :
    cubicAllowance 112649 <
      geom digestP * geom topPUpper * V5.b2 * V5.b3 * V5.b4 := by
  norm_num [cubicAllowance, geom, z, digestP, cap773J, topPUpper, topN,
    V5.b2, V5.b3, V5.b4]

end SigGolfResearch.Cap773TopOnlyObstruction

/-!
## Adaptive pooled-credit candidate (iteration31)

Research only: no production import, claim change, or certificate. The selector
REMAINS the existing floor22 selector. We only tighten acceptance after that
selector. In particular the cardinality at floor f is NOT the cardinality for a
selector reparameterized by f. Fresh-answer stopping kernels, final security,
completeness, and machine links still require hosted proofs.
-/
namespace ClaudeWCT.WCT9.Research.PooledCredit
open OracleComp OracleSpec SigGolfCandidate.T3

/-- Actual nonnegative effective verification credit of a decoded word. -/
def effectiveCredit (lay : Layer) (digits : List Nat) : Nat :=
  wordCredit lay digits + 4 * savedCopies lay digits - dispatchPenalty lay digits

/-- Cap each lower score at30, and the carried surplus at the desired gain.
No extra hash calls are needed to compute these pure functions. -/
def advanceCarry (gain carry : Nat) (lay : Layer) (digits : List Nat) : Nat :=
  min gain (carry + (min 30 (effectiveCredit lay digits) - producerFloor lay))

def requiredTopFloor (gain carry : Nat) : Nat := 22 + (gain - carry)

theorem top_floor_never_relaxed (gain carry : Nat) :
    22 ≤ requiredTopFloor gain carry := by
  unfold requiredTopFloor
  omega

theorem carry_le_gain (gain carry : Nat) (lay : Layer) (digits : List Nat) :
    advanceCarry gain carry lay digits ≤ gain := Nat.min_le_left _ _

theorem carry_increment_bounded (gain carry : Nat) (lay : Layer) (digits : List Nat) :
    advanceCarry gain carry lay digits ≤
      carry + (effectiveCredit lay digits - producerFloor lay) := by
  have hm := Nat.min_le_right gain
    (carry + (min 30 (effectiveCredit lay digits) - producerFloor lay))
  have hc := Nat.min_le_right 30 (effectiveCredit lay digits)
  unfold advanceCarry
  omega

/-- Keep the canonical floor22 selector and original producer safety checks;
only reject more top words when lower layers have insufficient surplus. -/
def decodeTopWithCarry (gain carry : Nat) (answer : Digest) : Option (List Nat) :=
  match producerDecode 0 answer with
  | none => none
  | some digits =>
      if requiredTopFloor gain carry + dispatchPenalty 0 digits ≤
          wordCredit 0 digits + 4 * savedCopies 0 digits then some digits else none

theorem decodeTopWithCarry_base {gain carry : Nat} {answer : Digest} {digits : List Nat}
    (h : decodeTopWithCarry gain carry answer = some digits) :
    producerDecode 0 answer = some digits := by
  cases hp : producerDecode 0 answer with
  | none => simp [decodeTopWithCarry, hp] at h
  | some ds =>
      simp only [decodeTopWithCarry, hp] at h
      split_ifs at h
      · cases h
        exact hp
      · simp at h

theorem decodeTopWithCarry_credit {gain carry : Nat} {answer : Digest} {digits : List Nat}
    (h : decodeTopWithCarry gain carry answer = some digits) :
    requiredTopFloor gain carry + dispatchPenalty 0 digits ≤
      wordCredit 0 digits + 4 * savedCopies 0 digits := by
  cases hp : producerDecode 0 answer with
  | none => simp [decodeTopWithCarry, hp] at h
  | some ds =>
      simp only [decodeTopWithCarry, hp] at h
      split_ifs at h with hc
      · cases h
        exact hc
      · simp at h

/-- Retain the original selector hint from the successful public-hash answer.
Empty fuel returns none; failure does not manufacture a dummy top word. -/
def searchTopWithCarry (gain carry tree leaf : Nat) (msg : LayerMsg) (counter : Nat) :
    Nat → M (Option (BitVec 32 × List Nat × BitVec 64))
  | 0 => pure none
  | fuel + 1 => do
      let answer ← publicHash (layerEncodingInput 0 tree leaf msg (BitVec.ofNat 32 counter))
      match decodeTopWithCarry gain carry (encodingAnswer 0 answer) with
      | none => searchTopWithCarry gain carry tree leaf msg (counter + 1) fuel
      | some digits => pure (some (BitVec.ofNat 32 counter, digits, encodingHint 0 answer))

/-- A model-level signer producing the same pieces plus the already existing top
hint. Lower searches, tree builders and order3,2,1 are unchanged. This is NOT
installed as the submission's signing/expansion program. Expansion must rerun
the same policy, including counters and carry, before any machine-link claim. -/
def signLayersWithCarry (cache : Cache) (index gain : Nat) :
    Nat → Nat → LayerMsg → M (Option (List Pieces × BitVec 64))
  | 0, _, _ => pure (some ([], 0))
  | n + 1, carry, msg => do
      let lay : Layer := Fin.ofNat 4 n
      let (leaf, tree) := route index lay
      if n = 0 then
        let some (_, digits, hint) ←
          searchTopWithCarry gain carry tree leaf msg 0 (searchLimit 0) | pure none
        let part ← signTop cache leaf digits
        pure (some ([part], hint))
      else
        let some (_, digits) ← layerCounterSearch lay tree leaf msg 0 (searchLimit lay) | pure none
        let (levels, values) ← buildTreeP lay tree leaf digits
        let path := (List.range (height lay)).map fun j =>
          (levels.getD j []).getD (leaf / 2 ^ j ^^^ 1) 0
        let top := topPair lay levels
        let carry' := advanceCarry gain carry lay digits
        let some (previous, hint) ←
          signLayersWithCarry cache index gain n carry' (.pair top.1 top.2) | pure none
        pure (some (previous ++ [(values, path)], hint))

/-- Deterministic accounting underlying the policy. Not a machine-cycle theorem.
The lower credited amounts include their fixed floors10,9,9. -/
theorem total_credit {gain carry top c1 c2 c3 : Nat}
    (h1 : 10 ≤ c1) (h2 : 9 ≤ c2) (h3 : 9 ≤ c3)
    (hc : carry ≤ (c1 - 10) + (c2 - 9) + (c3 - 9))
    (ht : requiredTopFloor gain carry ≤ top) :
    50 + gain ≤ top + c1 + c2 + c3 := by
  unfold requiredTopFloor at ht
  omega

end ClaudeWCT.WCT9.Research.PooledCredit

/-! Finite arithmetic packet for gain8, cap775/gate1353. The arrays are external
DP outputs, NOT Lean-proved cardinalities. Compiling these arithmetic statements
does not prove the fresh-answer law, the array/count links, or a certificate. -/
namespace ClaudeWCT.WCT9.Research.PooledCreditPacket

def n202 : List Nat := [44444210514614632453013305786840214, 43270547465047728058677790349033924, 41638240191617962951793025493843981, 39519142012181130951313701394522033, 36932462237659353802654691028823546, 33938695241273962698044050625507951, 30628501601218537764038958691967944, 27118955945433625862311616013112528, 23544556756865226968976372771210898]
def n201 : List Nat := [54408112790925688753987891000775297, 52205271644720435491391227169461376, 49374072630607869054258945664192558, 45952123965212487041454738440237319, 42029416161260738105653905283368946, 37732487237534268109769523863508583, 33219077116456466734442605936680683, 28664985933359420873343381352063905, 24235153322760640239450316665361627]
def badNumerator : Nat :=
  (Finset.range 8).sum fun a => (Finset.range (8-a)).sum fun b =>
    (n202.getD a 0 - n202.getD (a+1) 0) *
    (n202.getD b 0 - n202.getD (b+1) 0) *
    (n201.getD 0 0 - n201.getD (8-a-b) 0)
def badDenominator : Nat := (n202.getD 0 0)^2 * n201.getD 0 0

theorem low_carry_probability_bound : 50 * badNumerator ≤ badDenominator := by
  decide +kernel

def z : ℚ := 1 / (1 - 6931471808 / (10000000000 * 131072))
def geom (p : ℚ) : ℚ := z*p / (1-z+z*p)
def pDigest : ℚ := 1353 * 51668613533684827311648164987144309062238208 / 2^167
def p202 : ℚ := 7 * 44444210514614632453013305786840214 / (4 * 2^128)
def p201 : ℚ := 7 * 54408112790925688753987891000775297 / (4 * 2^128)
def pTop22 : ℚ := (61400435184999209708243105926444986 : ℚ) *
    (7 * 2^126 - 61400435184999209708243105926444986) / 2^256
def pTop30 : ℚ := (33556494098373355261802670185067659 : ℚ) *
    (7 * 2^126 - 61400435184999209708243105926444986) / 2^256

theorem factor_bounds :
    geom pDigest ≤ 1014355/1000000 ∧
    geom p201 * (geom p202)^2 ≤ 1068118/1000000 ∧
    geom pTop22 ≤ 1017035/1000000 ∧
    geom pTop30 ≤ 1031617/1000000 := by
  norm_num [geom, z, pDigest, p201, p202, pTop22, pTop30]

/-- Coarse two-bin upper model: with probability at most1/50 ask for floor30;
otherwise ask for floor22. Every actual requested threshold lies in22..30. -/
def packetFactor : ℚ :=
  (1014355/1000000) * (1068118/1000000) *
    ((49/50) * (1017035/1000000) + (1/50) * (1031617/1000000))
def cubicAllowance : ℚ :=
  let x : ℚ := (6931471803/10000000000) * (131072-112654) / 131072
  1+x+x^2/2+x^3/6

theorem coarse_envelope_fits : packetFactor ≤ cubicAllowance := by
  norm_num [packetFactor, cubicAllowance]

/-- Conditional accounting only, NOT the VerificationCycles contract. -/
theorem target_cycles : (7032 : Nat) - 8 = 7024 := by decide
theorem target_product : (5310 : Nat) * 7024 = 37297440 := by decide

end ClaudeWCT.WCT9.Research.PooledCreditPacket

/-!
## Finite-fuel pooled-credit supersolution (iteration32)

Research only, NOT imported by Solution and NOT a certificate. The generic
finite-fuel lemma retains timeout cost: fuel0 has moment1, not0. The integer
packet uses gain13, cap775/gate1353, the original floor22 top selector, and the
unchanged lower searches. External DP tables still need cardinality proofs;
fresh conditional kernels, security, and machine/expansion links remain open.
No local Lean compilation was performed.
-/
namespace ClaudeWCT.WCT9.Research.FiniteCreditKernel
open SigGolfCandidate.T3

/-- `accepted` already includes each accepted type's continuation bound.
A fuel-exhausted search still has terminal weight1. -/
def finiteMoment (z reject accepted : ℚ) : Nat → ℚ
  | 0 => 1
  | n+1 => z * (accepted + reject * finiteMoment z reject accepted n)

/-- The successful-only transform is NOT the full cost transform. -/
def successfulMoment (z reject accepted : ℚ) : Nat → ℚ
  | 0 => 0
  | n+1 => z * (accepted + reject * successfulMoment z reject accepted n)

/-- Explicit timeout correction, valid even at fuel0 and reject0. -/
theorem finite_eq_success_add_timeout (z reject accepted : ℚ) (n : Nat) :
    finiteMoment z reject accepted n =
      successfulMoment z reject accepted n + (z*reject)^n := by
  induction n with
  | zero => simp [finiteMoment, successfulMoment]
  | succ n ih =>
      simp only [finiteMoment, successfulMoment, ih, pow_succ]
      ring

/-- A one-step Bellman supersolution bounds every finite search, including
failed paths. This is an algebraic lemma, not an oracle execution-law theorem. -/
theorem finite_le_supersolution {z reject accepted bound : ℚ}
    (hz : 0 ≤ z) (hr : 0 ≤ reject) (hb : 1 ≤ bound)
    (hstep : z * (accepted + reject*bound) ≤ bound) (n : Nat) :
    finiteMoment z reject accepted n ≤ bound := by
  induction n with
  | zero => exact hb
  | succ n ih =>
      change z * (accepted + reject * finiteMoment z reject accepted n) ≤ bound
      calc
        z * (accepted + reject * finiteMoment z reject accepted n) ≤
            z * (accepted + reject * bound) :=
          mul_le_mul_of_nonneg_left
            (add_le_add_left (mul_le_mul_of_nonneg_left ih hr) accepted) hz
        _ ≤ bound := hstep

/-- Concrete specialization of the model signer; not an installed image. -/
def signGain13 (cache : Cache) (index : Nat) (msg : LayerMsg) :=
  PooledCredit.signLayersWithCarry cache index 13 4 0 msg

/-- Credit accounting only. The machine proof must retain rather than discard
lower surplus before this arithmetic can imply C7019. -/
theorem credit63 {carry top c1 c2 c3 : Nat}
    (h1 : 10 ≤ c1) (h2 : 9 ≤ c2) (h3 : 9 ≤ c3)
    (hc : carry ≤ (c1-10)+(c2-9)+(c3-9))
    (ht : PooledCredit.requiredTopFloor 13 carry ≤ top) :
    63 ≤ top+c1+c2+c3 := by
  exact PooledCredit.total_credit h1 h2 h3 hc ht

end ClaudeWCT.WCT9.Research.FiniteCreditKernel

namespace ClaudeWCT.WCT9.Research.Gain13Packet

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

-- BEGIN GENERATED NUMERAL DATA (external DP, not certified cardinalities)
def tail202 : List Nat := [44444210514614632453013305786840214, 43270547465047728058677790349033924, 41638240191617962951793025493843981, 39519142012181130951313701394522033, 36932462237659353802654691028823546, 33938695241273962698044050625507951, 30628501601218537764038958691967944, 27118955945433625862311616013112528, 23544556756865226968976372771210898, 20035460936274711397956848027222226, 16702112927114157723026801121707550, 13634676664941173437298540260835089, 10899946103222341084509908275940421, 8532840114673252322982302606282604, 6538694663634745651817691106662084, 4904014634779156866118516287689970, 3600868121141033724962085329108155, 2588446996344715075918422701594176, 1820596106065863815301062825650921, 1252964778269687912828951323007990, 844181127621537566382905185176676, 556587263569874292126677090542478, 0]

def tail201 : List Nat := [54408112790925688753987891000775297, 52205271644720435491391227169461376, 49374072630607869054258945664192558, 45952123965212487041454738440237319, 42029416161260738105653905283368946, 37732487237534268109769523863508583, 33219077116456466734442605936680683, 28664985933359420873343381352063905, 24235153322760640239450316665361627, 20065435145178632167443389224887757, 16263529072464441716121015897211781, 12905382641046880545393600877316626, 10025445665860223537158612684490582, 7621599354625958305222293312435845, 5669547627220668879271331480744985, 4128193821255747260672218325421066, 2942048706503813034899113231613428, 2051022613339333562521797093110122, 1398798886881335108310354544410070, 933764142327532692446042567822983, 609829887999743907751787127862225, 0]

def topRaw : List Nat := [61400435184999209708243105926444986, 59118617930026709864893449254178315, 56412336783017058316068591023786605, 53295959781860291461652388304869136, 49806927014954033575633984287066893, 46004495892090709324135340347215286, 41966509284957565736683815445044472, 37784346796747798898882944075578719, 33556494098373355261802670185067659, 29381705508090847735214416823465620, 25352598451633301895212418337094824, 21550055138460539121005712498594116, 18038922516042673169712366729388162, 14865576200900011763143189603295225]

def topBounds : List Nat := [1074321458, 1060456645, 1050112874, 1042278850, 1036270873, 1031615721, 1027979123, 1025120827, 1022865461, 1021083030, 1019675668, 1018568546, 1017703483, 1017034363]

def lowerBounds0 : List Nat := [1086633740, 1086522645, 1086446145, 1086394710, 1086361096, 1086339862, 1086326984, 1086319551, 1086315516, 1086313492, 1086312578, 1086312223, 1086312115, 1086312095]

def lowerBounds1 : List Nat := [1063555479, 1062852065, 1062333236, 1061955772, 1061686153, 1061498063, 1061370711, 1061287671, 1061236061, 1061205928, 1061189767, 1061182108, 1061179145, 1061178399]

def lowerBounds2 : List Nat := [1050678140, 1047114487, 1044390826, 1042303386, 1040705939, 1039490993, 1038577523, 1037902911, 1037417511, 1037080904, 1036859479, 1036725015, 1036653827, 1036626214]

def digestBound : Nat := 1014354564
-- END GENERATED NUMERAL DATA

def scale : Nat := 1000000000
def zNum : Nat := 10000000000 * 131072
def zDen : Nat := zNum - 6931471808
def lowerQ : Nat := 4 * 2^128
def topQ : Nat := 2^256

/-- Last bin is score AT LEAST30, so all carried scores are capped at30. -/
def bins (tails : List Nat) (s : Nat) : Nat :=
  7 * (tails.getD s 0 - tails.getD (s+1) 0)
def mass (tails : List Nat) : Nat :=
  ((List.range (tails.length-1)).map (bins tails)).sum

def weighted (tails next : List Nat) (carry : Nat) : Nat :=
  ((List.range (tails.length-1)).map fun s =>
    bins tails s * next.getD (min 13 (carry+s)) 0).sum

/-- Existing floor22 selector is fixed. It is NOT reparameterized by carry. -/
def topN (carry : Nat) : Nat :=
  topRaw.getD (13-carry) 0 * (7*2^126 - topRaw.getD 0 0)

def topOK (carry : Nat) : Prop :=
  topN carry ≤ topQ ∧ scale ≤ topBounds.getD carry 0 ∧
    zNum * (topN carry * scale + (topQ-topN carry) * topBounds.getD carry 0) ≤
      zDen * topQ * topBounds.getD carry 0

def lowerOK (tails next current : List Nat) (carry : Nat) : Prop :=
  mass tails ≤ lowerQ ∧ scale ≤ current.getD carry 0 ∧
    zNum * (weighted tails next carry + (lowerQ-mass tails) * current.getD carry 0) ≤
      zDen * lowerQ * current.getD carry 0

/-- Compact integer arithmetic, avoiding a huge nested rational denominator.
These statements do not identify any table row with the actual decoder law. -/
theorem top_guards : ∀ carry : Fin 14, topOK carry.val := by
  decide +kernel

theorem lower_guards : ∀ carry : Fin 14,
    lowerOK tail201 topBounds lowerBounds2 carry.val ∧
    lowerOK tail202 lowerBounds2 lowerBounds1 carry.val ∧
    lowerOK tail202 lowerBounds1 lowerBounds0 carry.val := by
  decide +kernel

def digestQ : Nat := 2^167
def digestN : Nat := 1353 * 51668613533684827311648164987144309062238208

theorem digest_guard :
    digestN ≤ digestQ ∧ scale ≤ digestBound ∧
      zNum * (digestN * scale + (digestQ-digestN) * digestBound) ≤
        zDen * digestQ * digestBound := by
  decide +kernel

def packetFactor : ℚ :=
  (digestBound : ℚ) * (lowerBounds0.getD 0 0 : ℚ) / (scale : ℚ)^2

def cubicAllowance : ℚ :=
  let x : ℚ := (6931471803/10000000000) * (131072-112654) / 131072
  1+x+x^2/2+x^3/6

theorem rounded_envelope_fits : packetFactor ≤ cubicAllowance := by
  norm_num [packetFactor, cubicAllowance, digestBound, lowerBounds0, scale]

/-- New uniform top search lower rate: at worst floor35, NOT the old floor22
rate900. Converting this into a timeout theorem requires the fresh-answer law. -/
theorem worst_top_rate231 :
    (231 : ℚ) * (6931471808/10000000000) ≤
      (2^21 : ℚ) * (topN 0 : ℚ) / (topQ : ℚ) := by
  norm_num [topN, topRaw, topQ]

theorem target_cycles : (7032 : Nat) - 13 = 7019 := by decide
theorem target_product : (5310 : Nat) * 7019 = 37270890 := by decide

end ClaudeWCT.WCT9.Research.Gain13Packet

/-!
## Continuation-weighted fresh public search

Unlike `V_publicSearch`, a successful answer need not have continuation moment1.
The bound retains that answer-dependent continuation cost inside the fresh-answer
expectation. The invariant and continuation obligations are explicit; they are
not discharged for the pooled signer by this generic candidate theorem.
-/
namespace ClaudeWCT.WCT9.Research.WeightedPublicSearch
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling

/-- Search one fresh public domain and then run a result-dependent continuation.
Failure at empty fuel is retained as a normal `none` result, not dropped. -/
def searchContinue {β γ : Type} (inputs : Nat → HashInput)
    (decoder : HashOutput → Option β) (next : Nat → β → M (Option γ)) :
    Nat → Nat → M (Option γ)
  | 0, _ => pure none
  | fuel+1, counter => do
      let answer ← publicQuery (inputs counter)
      match decoder answer with
      | none => searchContinue inputs decoder next fuel (counter+1)
      | some value => next counter value

/-- Exact oracle-semantic bridge for a weighted Bellman step. All queried inputs
must be fresh; domain injectivity preserves freshness after rejected trials.
`Inv` tracks whatever cache/program facts the successful continuation requires.
No independence of the continuation from the accepted answer is assumed. -/
theorem V_searchContinue {β γ : Type} (secret : BitVec 256) (z b : ENNReal)
    (hb : 1 ≤ b) (inputs : Nat → HashInput) (decoder : HashOutput → Option β)
    (next : Nat → β → M (Option γ)) (payoff : HashOutput → ENNReal)
    (bound : Nat) (Inv : Nat → RCache → Prop)
    (hinput : ∀ counter, counter < bound → (inputs counter).length = 64)
    (hinj : ∀ left right, left < bound → right < bound →
      inputs left = inputs right → left = right)
    (hInv : ∀ counter cache, counter < bound → Inv counter cache →
      ∀ answer, decoder answer = none →
        Inv (counter+1) (cache.cacheQuery (inputs counter) answer))
    (hnext : ∀ counter cache, counter < bound → Inv counter cache →
      ∀ answer value, decoder answer = some value →
        V secret z (next counter value) (cache.cacheQuery (inputs counter) answer) ≤ payoff answer)
    (hstep : z * expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun answer => match decoder answer with
        | none => b
        | some _ => payoff answer) ≤ b) :
    ∀ fuel counter, counter+fuel ≤ bound → ∀ cache : RCache,
      Inv counter cache →
      (∀ c, counter ≤ c → c < bound → cache (inputs c) = none) →
      V secret z (searchContinue inputs decoder next fuel counter) cache ≤ b := by
  intro fuel
  induction fuel with
  | zero =>
      intro counter _ cache _ _
      simpa [searchContinue] using hb
  | succ fuel ih =>
      intro counter hlimit cache hI hfresh
      rw [searchContinue, V_publicQuery, hinput counter (by omega)]
      simp only [show (64 : Nat)/64 = 1 by decide, pow_one]
      rw [expectedValue_fresh _ _ (hfresh counter le_rfl (by omega))]
      calc
        _ ≤ z * expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
            (fun answer => match decoder answer with
              | none => b
              | some _ => payoff answer) := by
          apply mul_le_mul' le_rfl
          apply expectedValue_mono
          intro answer
          cases hd : decoder answer with
          | some value =>
              simp only [hd]
              exact hnext counter cache (by omega) hI answer value hd
          | none =>
              simp only [hd]
              apply ih (counter+1) (by omega) _
                (hInv counter cache (by omega) hI answer hd)
              intro c hstart hc
              rw [QueryCache.cacheQuery_of_ne]
              · exact hfresh c (by omega) hc
              · intro he
                have he' := hinj c counter hc (by omega) he
                omega
        _ ≤ b := hstep

end ClaudeWCT.WCT9.Research.WeightedPublicSearch

/-!
## Strict subset after the fixed canonical top selector

The selector still prefers ANY base producer-good low half; a tighter top
threshold is applied only to the selected word. The following fiber formula
accounts for base-good low words shadowing strict-good high words. It must not
be replaced by the cardinality of a newly retuned selector.
-/
namespace ClaudeWCT.WCT9.Research.StrictSelector
open Finset SigGolfCandidate.Choice

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A fixed selector's strict output event has a disjoint two-rectangle form. -/
theorem event_eq (good blocked strict : Finset α) (hs : strict ⊆ good) :
    (univ.filter fun pair : α × α => Gated.choose good blocked pair ∈ strict) =
      strict ×ˢ univ ∪ (univ \ (blocked ∪ good)) ×ˢ strict := by
  ext pair
  by_cases hsLow : pair.1 ∈ strict
  · have hgLow := hs hsLow
    simp [Gated.choose, hsLow, hgLow]
  · by_cases hg : pair.1 ∈ good <;> by_cases hb : pair.1 ∈ blocked <;>
      simp [Gated.choose, hsLow, hg, hb]

/-- Exact strict selected count, with base rather than strict exclusion on low. -/
theorem event_card (good blocked strict : Finset α) (hs : strict ⊆ good) :
    (univ.filter fun pair : α × α => Gated.choose good blocked pair ∈ strict).card =
      strict.card * (Fintype.card α + (Fintype.card α - (blocked ∪ good).card)) := by
  rw [event_eq good blocked strict hs]
  have hd : Disjoint (strict ×ˢ (univ : Finset α))
      ((univ \ (blocked ∪ good)) ×ˢ strict) := by
    apply disjoint_left.mpr
    intro pair hleft hright
    exact (mem_sdiff.mp (mem_product.mp hright).1).2
      (mem_union_right _ (hs (mem_product.mp hleft).1))
  rw [card_union_of_disjoint hd]
  simp only [card_product, card_univ, card_sdiff_of_subset (subset_univ _)]
  ring

/-- The factor used by the arithmetic packet: every strict word has at least
`7*D - |good|` preimages when the low blocked set occupies a quarter. -/
theorem event_card_lower (good blocked strict : Finset α) (hs : strict ⊆ good)
    (D : Nat) (hspace : Fintype.card α = 4*D) (hblocked : blocked.card = D) :
    strict.card * (7*D - good.card) ≤
      (univ.filter fun pair : α × α => Gated.choose good blocked pair ∈ strict).card := by
  rw [event_card good blocked strict hs, hspace]
  have hu := card_union_le blocked good
  rw [hblocked] at hu
  apply Nat.mul_le_mul_left
  omega

/-- The existing canonical hint is retained even on rows rejected by the tighter
predicate. Successful rows therefore require no selector/image modification. -/
theorem strict_hint {lay : SigGolfCandidate.T3.Layer}
    (answer : SigGolfCandidate.T3.HashOutput) (P : SigGolfCandidate.T3.Digest → Prop)
    (h : P (encodingAnswer lay answer)) :
    P (verificationAnswer lay (encodingHint lay answer) answer) := by
  rw [verificationAnswer_honest]
  exact h

end ClaudeWCT.WCT9.Research.StrictSelector

/-!
## Carry-dependent canonical selector: repair for rejected-row shadowing

Fixed floor22 selection followed by a strict post-filter admits a row where a
base-good/strict-bad low word shadows a strict-good high word. Re-select with the
STRICT set instead. The verifier already supports the resulting0/16 hint.
These definitions are research only and are not installed in Core or an image.
-/
namespace ClaudeWCT.WCT9.Research.RetunedPooledTop
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.Choice

/-- Producer restriction retains all original rank/zero/checksum conditions. -/
def strictWords (floor : Nat) : Finset Digest :=
  Finset.univ.filter fun word => (producerDecode 0 word).isSome ∧
    floor ≤ PooledCredit.effectiveCredit 0 (dataDigits 0 word)

@[simp] theorem mem_strictWords (floor : Nat) (word : Digest) :
    word ∈ strictWords floor ↔ (producerDecode 0 word).isSome = true ∧
      floor ≤ PooledCredit.effectiveCredit 0 (dataDigits 0 word) := by
  simp [strictWords]

def answer (floor : Nat) (raw : HashOutput) : Digest :=
  Gated.choose (strictWords floor) Selector.blocked (Selector.splitEquiv raw)

def hint (floor : Nat) (raw : HashOutput) : BitVec 64 :=
  if raw.extractLsb' 0 128 ∈ strictWords floor ∨
      raw.extractLsb' 0 128 ∈ Selector.blocked then 0 else 16

/-- No verifier-image change is needed: the existing branch reads the new hint. -/
theorem honest_hint (floor : Nat) (raw : HashOutput) :
    verificationAnswer 0 (hint floor raw) raw = answer floor raw := by
  simp only [verificationAnswer, if_true, hint, answer]
  exact Selector.branchRead_canonical (strictWords floor) (Selector.splitEquiv raw)

/-- Restored rejected-row exclusion for EVERY allowed verifier hint, not just
for the producer's canonical hint. This is what post-filtering cannot provide. -/
theorem rejected_no_witness (floor : Nat) (raw : HashOutput)
    (hrej : answer floor raw ∉ strictWords floor) (arbitraryHint : BitVec 64) :
    verificationAnswer 0 arbitraryHint raw ∉ strictWords floor := by
  have h := Gated.rejected_row_no_read (strictWords floor) Selector.blocked
    (Selector.splitEquiv raw) hrej (decide (arbitraryHint &&& 16 = 16))
  rw [← Selector.branchRead_eq_read] at h
  exact h

/-- Retuned selection has its own first-success coupling, parameterized by the
already-chosen carry/threshold. This does not prove cross-layer security. -/
theorem prefix_contact_eq (floor : Nat) (target : Digest)
    (rows : Nat → Digest × Digest) (reference counter : Nat)
    (before : ∀ i < reference,
      Gated.choose (strictWords floor) Selector.blocked (rows i) ∉ strictWords floor)
    (hcounter : counter ≤ reference) (ht : target ∈ strictWords floor)
    (hit : Gated.targetRead Selector.blocked target (rows counter) = target) :
    counter = reference :=
  Gated.prefix_hit_eq_reference (strictWords floor) Selector.blocked target rows
    reference counter before hcounter ht hit

/-- Fixed decoder, retuned selector, normal search exhaustion. -/
def search (floor : Nat) (tree leaf : Nat) (msg : LayerMsg) (counter : Nat) :
    Nat → M (Option (BitVec 32 × List Nat × BitVec 64))
  | 0 => pure none
  | fuel+1 => do
      let raw ← publicHash (layerEncodingInput 0 tree leaf msg (BitVec.ofNat 32 counter))
      let word := answer floor raw
      match producerDecode 0 word with
      | none => search floor tree leaf msg (counter+1) fuel
      | some digits =>
          if floor ≤ PooledCredit.effectiveCredit 0 digits then
            pure (some (BitVec.ofNat 32 counter, digits, hint floor raw))
          else search floor tree leaf msg (counter+1) fuel

/-- Selected success count lower bound for the retuned selector. The gain13
arithmetic conservatively used the larger base set's exclusion instead, so its
floor-dependent rate can only improve under this repair (after count links). -/
theorem selected_count_lower (floor : Nat) :
    (strictWords floor).card * (7*2^126 - (strictWords floor).card) ≤
      (Gated.accepted (strictWords floor) Selector.blocked).card :=
  Selector.accepted_lower (strictWords floor)

end ClaudeWCT.WCT9.Research.RetunedPooledTop

/-!
## Full-table completeness arithmetic for gain13

The old top fuel2^21 gives only231 certified failure bits at floor35; it cannot
feed a union over2^301 encoding families. Raise ONLY the retuned top fuel to2^23.
Infinite-horizon Bellman guards dominate every finite fuel, including this one.
This file is arithmetic, not a theorem connecting a decoder law or all tables.
-/
namespace ClaudeWCT.WCT9.Research.Gain13Completeness
open Gain13Packet

def topFuel : Nat := 2^23

theorem top_rate900 :
    (900 : ℚ) * (6931471808/10000000000) ≤
      (topFuel : ℚ) * (topN 0 : ℚ) / (topQ : ℚ) := by
  norm_num [topFuel, topN, topRaw, topQ]

/-- At most14 carry-dependent top predicates. Reuse the old full family as a
conservative ambient family for each carry; lower predicates are unchanged. -/
theorem union_slack :
    (2 : ℚ)^256 / 2^450 + (14 : ℚ)*2^301 / 2^600 ≤ 1/2^193 := by
  norm_num

end ClaudeWCT.WCT9.Research.Gain13Completeness

namespace ClaudeWCT.WCT9.Research.RetunedPooledTop
open SigGolfCandidate.T3

/-- Research-level signer, selecting the strict top predicate BEFORE choosing a
hash half. Uses2^23 top fuel to preserve full-table completeness slack; lower
searches, targets, rank/zero constraints, and signature format are unchanged.
It is NOT the production sign entry point and has no new RV64 machine link. -/
def signLayers (cache : Cache) (index : Nat) :
    Nat → Nat → LayerMsg → M (Option (List Pieces × BitVec 64))
  | 0, _, _ => pure (some ([], 0))
  | n+1, carry, msg => do
      let lay : Layer := Fin.ofNat 4 n
      let (leaf, tree) := route index lay
      if n = 0 then
        let some (_, digits, selectedHint) ←
          search (PooledCredit.requiredTopFloor 13 carry) tree leaf msg 0
            Gain13Completeness.topFuel | pure none
        let part ← signTop cache leaf digits
        pure (some ([part], selectedHint))
      else
        let some (_, digits) ← layerCounterSearch lay tree leaf msg 0 (searchLimit lay) |
          pure none
        let (levels, values) ← buildTreeP lay tree leaf digits
        let path := (List.range (height lay)).map fun j =>
          (levels.getD j []).getD (leaf / 2^j ^^^ 1) 0
        let top := topPair lay levels
        let carry' := PooledCredit.advanceCarry 13 carry lay digits
        let some (previous, selectedHint) ←
          signLayers cache index n carry' (.pair top.1 top.2) | pure none
        pure (some (previous ++ [(values, path)], selectedHint))

def signGain13 (cache : Cache) (index : Nat) (msg : LayerMsg) :=
  signLayers cache index 4 0 msg

end ClaudeWCT.WCT9.Research.RetunedPooledTop


/-!
## Iteration33: key-coherent ancestry, not descendant-conditioned top searches

Research only. Compilation/replay delegated to the host. This repairs no
production signer automatically and asserts no security or cycle certificate.

The rate1/8192 obstruction reported in iteration32 was overinterpreted: its
only generic moment uses are signs; FTS honestLaw concerns producerAdmissible,
not a layer WOTS rate. The new problem is preserving ONE reference per key.
-/
namespace SigGolfCandidate.Choice.Gated
section CoherentReference
variable {α : Type} [Fintype α] [DecidableEq α]

/-- The reference must belong to THIS key's good set. A larger verifier set is
not enough. This lemma is agnostic about any positive search-rate lower bound. -/
theorem coherent_target_contact (good blocked : Finset α)
    (target : α) (a : α × α) (high : Bool) (ht : target ∈ good)
    (hit : read blocked high a = target) : choose good blocked a ∈ good := by
  apply read_implies_choose good blocked high a
  simpa only [hit] using ht

/-- The full target membership hypothesis is what an adaptive floor must retain
across all uses of one WOTS key. It cannot be inferred just from base validity. -/
theorem coherent_prefix_contact (good blocked : Finset α)
    (target : α) (rows : Nat → α × α) (reference counter : Nat)
    (before : ∀ i < reference, choose good blocked (rows i) ∉ good)
    (hc : counter ≤ reference) (ht : target ∈ good)
    (high : Bool) (hit : read blocked high (rows counter) = target) :
    counter = reference := by
  apply prefix_hit_eq_reference good blocked target rows reference counter before hc ht
  exact read_hit_implies_probe_hit blocked target high (rows counter) hit

/-- Finite model: a base-good word rejected at a strict state may be opened at
an earlier row, even though the later selected reference is strict-good. -/
def twoRow (i : Nat) : Fin 2 × Fin 2 :=
  if i = 0 then (0,0) else (1,1)

theorem twoRow_reference_split :
    choose ({0,1} : Finset (Fin 2)) ∅ (twoRow 0) = 0 ∧
    choose ({1} : Finset (Fin 2)) ∅ (twoRow 0) ∉ ({1} : Finset (Fin 2)) ∧
    read (∅ : Finset (Fin 2)) false (twoRow 0) = 0 ∧
    choose ({1} : Finset (Fin 2)) ∅ (twoRow 1) = 1 := by
  decide +kernel

end CoherentReference
end SigGolfCandidate.Choice.Gated

namespace ClaudeWCT.WCT9.Research.AncestorCredit
open SigGolfCandidate.T3

/-- Carry may flow from ancestors toward descendants, never the reverse. The
last layer absorbs whatever part of the gain the fixed ancestors did not earn. -/
def terminalFloor (gain carry : Nat) : Nat := producerFloor 3 + (gain - carry)

theorem terminal_floor_not_relaxed (gain carry : Nat) :
    producerFloor 3 ≤ terminalFloor gain carry := by
  unfold terminalFloor
  omega

/-- Exact gain12 optimized packet chooses these floors at layer2. Layer0 and1
remain at22 and10; layer3's floor is9+(12-carry). -/
def layer2Floor12 (carry : Nat) : Nat :=
  if carry = 0 then 12 else if carry ≤ 2 then 11 else if carry = 3 then 10 else 9

theorem layer2_floor_range (carry : Nat) :
    9 ≤ layer2Floor12 carry ∧ layer2Floor12 carry ≤ 12 := by
  unfold layer2Floor12
  split_ifs <;> omega

theorem carry_path_gain (gain c s : Nat) (hs : gain - c ≤ s) :
    gain ≤ c+s := by omega

/-- Functionality: a key-local policy fed key-local ancestor credits has one
floor for each key. This is an interface invariant, NOT a proof the current
bottom-up signer has it. -/
theorem key_floor_congr {Key : Type} (ancestorCarry : Key → Nat)
    (policy : Nat → Nat) {left right : Key} (hkey : left = right) :
    policy (ancestorCarry left) = policy (ancestorCarry right) := by
  cases hkey
  rfl

/-- The actual route has many descendants per top key. These exact indices
already differ at layer1 while sharing the top WOTS address. -/
theorem route_collision :
    route 0 0 = (0,0) ∧ route 4096 0 = (0,0) ∧
    route 0 1 = (0,0) ∧ route 4096 1 = (1,0) := by
  decide +kernel

theorem every_top_descendant (i : Nat) (hi : i < 2^19) : route i 0 = (0,0) := by
  have hd : i / 2^19 = 0 := Nat.div_eq_of_lt hi
  change (i / 2^19 % 2^12, i / 2^(19+12)) = (0,0)
  have hi' : i < 2^(19+12) := lt_of_lt_of_le hi (by norm_num)
  rw [hd, Nat.div_eq_of_lt hi']
  rfl

/-- Accounting arithmetic only. No VerificationCycles contract is claimed. -/
theorem conditional_cycle_target : (7032 : Nat) - 12 = 7020 := by decide
theorem conditional_product : (5310 : Nat) * 7020 = 37276200 := by decide

end ClaudeWCT.WCT9.Research.AncestorCredit

/-! Research-only integer packet. DP cardinalities and actual oracle links
are external. Every continuation bound is >=1, hence timeout boundary1 is kept.
No compilation was run locally. -/
namespace ClaudeWCT.WCT9.Research.AncestorPacket12
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
open Gain13Packet
def b0 : List Nat := [1086610611, 1086502692, 1086429311, 1086381197, 1086350951, 1086332783, 1086322399, 1086316805, 1086314014, 1086312759, 1086312272, 1086312123, 1086312096]
def b1 : List Nat := [1070314719, 1069638673, 1069133562, 1068768041, 1068515594, 1068349588, 1068245247, 1068182739, 1068147581, 1068129440, 1068121186, 1068118130, 1068117396]
def b2 : List Nat := [1058740604, 1056189048, 1054076226, 1052288482, 1050865220, 1049822354, 1049098906, 1048611856, 1048297351, 1048105945, 1047999354, 1047948162, 1047930373]
def b3 : List Nat := [1104166256, 1081569240, 1065605777, 1054100282, 1045668906, 1039412304, 1034739388, 1031245232, 1028639937, 1026715263, 1025321214, 1024342762, 1023684704]
def b4 : List Nat := [1000000000, 1000000000, 1000000000, 1000000000, 1000000000, 1000000000, 1000000000, 1000000000, 1000000000, 1000000000, 1000000000, 1000000000, 1000000000]
def scale : Nat := 1000000000
def base (lay : Nat) : Nat := if lay = 0 then 22 else if lay = 1 then 10 else 9
def tail (lay credit : Nat) : Nat :=
  if lay = 0 then topRaw.getD (credit-22) 0
  else if lay = 1 then tail201.getD (credit-10) 0
  else tail202.getD (credit-9) 0

def policy (lay carry : Nat) : Nat :=
  if lay = 0 then 22 else if lay = 1 then 10
  else if lay = 2 then AncestorCredit.layer2Floor12 carry else 9+(12-carry)

def table (lay : Nat) : List Nat :=
  if lay = 0 then b0 else if lay = 1 then b1
  else if lay = 2 then b2 else if lay = 3 then b3 else b4

def q (lay : Nat) : Nat := if lay = 0 then 2^256 else 4*2^128

def coefficient (lay : Nat) : Nat := if lay = 0 then 7*2^126 - topRaw.getD 0 0 else 7

def acceptedN (lay carry : Nat) : Nat := coefficient lay * tail lay (policy lay carry)

def weighted (lay carry : Nat) : Nat :=
  let f := policy lay carry
  let threshold := base lay + (12-carry)
  let nxt := table (lay+1)
  ((Finset.range (threshold-f)).sum fun j =>
    (tail lay (f+j) - tail lay (f+j+1)) *
      nxt.getD (min 12 (carry + (f+j-base lay))) 0) +
        tail lay threshold * nxt.getD 12 0

def guard (lay carry : Nat) : Prop :=
  1310720000000000 * (coefficient lay * weighted lay carry +
    (q lay - acceptedN lay carry) * (table lay).getD carry 0) ≤
      1310713068528192 * q lay * (table lay).getD carry 0

theorem all_guards : ∀ lay ∈ Finset.range 4, ∀ c ∈ Finset.range 13, guard lay c := by
  decide +kernel

theorem timeout_boundary : ∀ lay ∈ Finset.range 5, ∀ c ∈ Finset.range 13,
    scale ≤ (table lay).getD c 0 := by
  decide +kernel

theorem all_rates_valid : ∀ lay ∈ Finset.range 4, ∀ c ∈ Finset.range 13,
    0 < acceptedN lay c ∧ acceptedN lay c ≤ q lay := by
  decide +kernel
def digestBound : Nat := 1014354564
theorem digest_guard :
    1310720000000000 * (1353 * 51668613533684827311648164987144309062238208 * scale +
      (2^167-1353*51668613533684827311648164987144309062238208) * digestBound) ≤
        1310713068528192 * 2^167 * digestBound := by decide +kernel

def factor : ℚ := (digestBound : ℚ) * (b0.getD 0 0 : ℚ) / (scale:ℚ)^2

def allowance : ℚ :=
  let x : ℚ := (6931471803/10000000000) * (131072-112654)/131072
  1+x+x^2/2+x^3/6

theorem rounded_fits_original_fixed_bound : factor ≤ allowance := by
  norm_num [factor, allowance, digestBound, b0, scale]

/-- Minimum lower success at floor21 gives >=600 failure bits at raised fuel2^23.
This arithmetic is not yet a theorem about the implemented decoder's law. -/
theorem lower_rate600 :
  (600:ℚ) * (6931471808/10000000000) ≤
    2^23 * (7 * (tail202.getD 12 0 : ℚ)) / (4*2^128) := by
  norm_num [tail202]
end ClaudeWCT.WCT9.Research.AncestorPacket12

/-!
## Ancestor-first execution: retain intermediate chain values

Research only. Compute each selected lower leaf's complete chains while making
its ordinary endpoint tree; retain all eight values per chain. After ancestor
searches determine a floor, extract the signature values without new queries.
The fixed-cost budget is plausible only after this is integrated with buildLeafPF,
tree construction, memory layout and machine links. No such full link is claimed.
-/
namespace ClaudeWCT.WCT9.Research.RetainedChains
open OracleComp OracleSpec SigGolfCandidate.T3

/-- Eight entries for a radix8 chain, including its seed and endpoint. No empty
`getD` case arises: every recursion returns at least the initial value. -/
def values (lay : Layer) (tree leaf i start : Nat) : Nat → Digest → M (List Digest)
  | 0, seed => pure [seed]
  | count+1, seed => do
      let rows ← values lay tree leaf i start count seed
      let next ← halfHash (chainHigh lay i (start+count))
        (SigGolfCandidate.T3.chainInput lay tree leaf i (start+count) (rows.getLastD 0))
      pure (rows ++ [next])

/-- Splitting an ordinary chain at any valid digit preserves its endpoint.
This existing semantic identity motivates retaining intermediate values, but it
is NOT an extraction/length/resource proof for `values` above. -/
theorem split_at_digit (lay : Layer) (tree leaf i digit : Nat) (seed : Digest)
    (hd : digit ≤ maxDigit lay i) :
    (do
      let prefix ← chainW lay tree leaf i 0 digit seed
      chainW lay tree leaf i digit (maxDigit lay i - digit) prefix) =
        chainW lay tree leaf i 0 (maxDigit lay i) seed := by
  have h := chainW_add lay tree leaf i 0 digit (maxDigit lay i - digit) seed
  rw [Nat.zero_add, Nat.add_sub_of_le hd] at h
  exact h.symm

/-- Pure storage/address calculation only. Each selected lower leaf has43
radix8 chains, eight16-byte values each; three selected leaves need16,512 bytes.
The ISA program-data limit and runtime memory layout still need separate proofs. -/
theorem storage_payload : (3 : Nat) * 43 * 8 * 16 = 16512 := by decide

/-- Safe default lookup is defined even on malformed retained rows. Actual
honest extraction needs length and digit-validity hypotheses, not this definition. -/
def extract (rows : List (List Digest)) (digits : List Nat) : List Digest :=
  (List.range 43).map fun i => (rows.getD i []).getD (digits.getD i 0) 0

end ClaudeWCT.WCT9.Research.RetainedChains

/-!
The top-first kernel needs the distribution of top credit, not only its success
rate. `StrictSelector.event_card` supplies a COMMON selected-word multiplicity
for every tail subset of the fixed top good set. Increasing that multiplicity
preserves a Bellman guard when continuation is no larger than the bound.
-/
namespace ClaudeWCT.WCT9.Research.AncestorPrefactor
open Finset SigGolfCandidate.Choice
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem selected_subset_common_factor (good blocked subset : Finset α)
    (hsub : subset ⊆ good) :
    (univ.filter fun pair : α × α => Gated.choose good blocked pair ∈ subset).card =
      subset.card * (Fintype.card α + (Fintype.card α - (blocked ∪ good).card)) :=
  StrictSelector.event_card good blocked subset hsub

/-- Pure algebra only. The caller must prove the actual cardinality, probability,
and invariant links. In particular `hgap` is a continuation inequality, not an
assumption that the next state has exactly the same continuation bound. -/
theorem larger_prefactor_preserves_guard (z q low actual weight count bound : ℚ)
    (hz : 0 ≤ z) (hk : low ≤ actual) (hgap : weight ≤ count * bound)
    (hguard : z * (low * weight + (q - low * count) * bound) ≤ q * bound) :
    z * (actual * weight + (q - actual * count) * bound) ≤ q * bound := by
  have h := mul_nonneg (sub_nonneg.mpr hk) (sub_nonneg.mpr hgap)
  have hstep : actual * weight + (q - actual * count) * bound ≤
      low * weight + (q - low * count) * bound := by nlinarith
  exact (mul_le_mul_of_nonneg_left hstep hz).trans hguard

end ClaudeWCT.WCT9.Research.AncestorPrefactor


/-!
Research-only extension: pool ABSOLUTE effective credit, not merely nonnegative
surplus over each layer's old floor. This allows a lower ancestor to incur a
credit deficit while keeping the final total unchanged. The top selector is
still fixed at floor22. No production entry point imports this module.
Compilation/replay and oracle, security, resource and machine links are pending.
-/
namespace ClaudeWCT.WCT9.Research.DeficitCredit

/-- The old floors sum to50. A successful four-layer path must attain50+gain. -/
def required (gain : Nat) : Nat := 50 + gain

def advance (gain credit earned : Nat) : Nat := min (required gain) (credit + earned)

def lastFloor (gain credit : Nat) : Nat := required gain - credit

/-- Final acceptance covers the entire remaining deficit, including any deficit
created by relaxing a preceding lower floor. This is pure accounting only. -/
theorem final_covers_deficit (gain credit earned : Nat)
    (h : lastFloor gain credit ≤ earned) : required gain ≤ credit + earned := by
  unfold lastFloor at h
  omega

theorem advance_reached (gain credit earned : Nat)
    (h : required gain ≤ credit + earned) :
    advance gain credit earned = required gain := by
  unfold advance
  exact Nat.min_eq_left h

/-- Natural subtraction of per-layer surplus can erase a deficit. Use absolute
credit (or signed carry), never sum truncated individual surpluses. -/
theorem truncated_surplus_is_unsound :
    ((7 : Nat) - 10) + ((12 : Nat) - 9) = 3 ∧
    (7 : Nat) + 12 = 10 + 9 := by decide

/-- The retained kernel deliberately clips each earned score, not the decoder's
acceptance set. Actual credit may be larger; it is never overcounted. -/
def clippedEarned (lay earned : Nat) : Nat := min (if lay = 0 then 60 else 30) earned

theorem clippedEarned_le (lay earned : Nat) : clippedEarned lay earned ≤ earned := by
  exact Nat.min_le_right _ _

/-- A policy is key-coherent only when its accumulated credit is itself a
function of that key's fixed ancestors. This is an interface, not a security proof. -/
theorem ancestor_policy_congr {Key : Type} (credit : Key → Nat)
    (policy : Nat → Nat) {a b : Key} (hab : a = b) :
    policy (credit a) = policy (credit b) := by cases hab; rfl

end ClaudeWCT.WCT9.Research.DeficitCredit

/-!
Iteration34 research-only packet. Every literal is a finite cardinality or
upward-rounded continuation bound. Theorems below check arithmetic, not the
actual machine or oracle law. Compile/replay externally; do not run Lean locally.
-/
namespace ClaudeWCT.WCT9.Research.DeficitPacket17
open scoped BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option Elab.async false

def topTail : List Nat := [61400435184999209708243105926444986, 59118617930026709864893449254178315, 56412336783017058316068591023786605, 53295959781860291461652388304869136, 49806927014954033575633984287066893, 46004495892090709324135340347215286, 41966509284957565736683815445044472, 37784346796747798898882944075578719, 33556494098373355261802670185067659, 29381705508090847735214416823465620, 25352598451633301895212418337094824, 21550055138460539121005712498594116, 18038922516042673169712366729388162, 14865576200900011763143189603295225, 12057313039939885305450975013665789, 9623171885634974026218476078963163, 7556017413940276147324030195764337, 5835641688348896382215925195925468, 4432272059926264843964730197382742, 3310014002440564320154415039403910, 2430075159226334904481208195618824, 1753548587265206240940716861370008, 1243507298933139131847504226685855, 866422363871016789661605025290933, 593024484449256649376703914897957, 398648194099359675586553324521462, 263143289819068731882542857793680, 170520932313612603616040297997315, 108452029234913937207210744399775, 67681528061020731133017041223140, 41434666577435726199206098673876, 24876434705568674870072937628657, 14642570109732014272361070643747, 8447610390764332318052875708640, 4775231069063915297196063992764, 2643863793922806413096479059218, 1433287116216187295616415326790, 760562908146087760448865965031, 394868546845875750082277964728]

def lower201 : List Nat := [58310357933255944251288942793955306, 58310336012616914532263309980386610, 58309964133770526751364164401473901, 58306966094947086560817020393648221, 58291665272054065360300937168071823, 58235979209929063613485945202021484, 58081065070836601986435334001201303, 57734422269950804638245936422699817, 57082284908894457343149900469675755, 56008308245340494107407867421618550, 54408112790925688753987891000775297, 52205271644720435491391227169461376, 49374072630607869054258945664192558, 45952123965212487041454738440237319, 42029416161260738105653905283368946, 37732487237534268109769523863508583, 33219077116456466734442605936680683, 28664985933359420873343381352063905, 24235153322760640239450316665361627, 20065435145178632167443389224887757, 16263529072464441716121015897211781, 12905382641046880545393600877316626, 10025445665860223537158612684490582, 7621599354625958305222293312435845, 5669547627220668879271331480744985, 4128193821255747260672218325421066, 2942048706503813034899113231613428, 2051022613339333562521797093110122, 1398798886881335108310354544410070, 933764142327532692446042567822983, 609829887999743907751787127862225]

def lower202 : List Nat := [46095893039550580864177812822640627, 46095878730828114658310970930783511, 46095632698271399271903924557007149, 46093622162280767402854262400034781, 46083220051762603203197505455308382, 46044839038753628463163023920930993, 45936596838824362937551402714118524, 45691135823106665795476360474637864, 45223465703457967253341632145154723, 44444210514614632453013305786840214, 43270547465047728058677790349033924, 41638240191617962951793025493843981, 39519142012181130951313701394522033, 36932462237659353802654691028823546, 33938695241273962698044050625507951, 30628501601218537764038958691967944, 27118955945433625862311616013112528, 23544556756865226968976372771210898, 20035460936274711397956848027222226, 16702112927114157723026801121707550, 13634676664941173437298540260835089, 10899946103222341084509908275940421, 8532840114673252322982302606282604, 6538694663634745651817691106662084, 4904014634779156866118516287689970, 3600868121141033724962085329108155, 2588446996344715075918422701594176, 1820596106065863815301062825650921, 1252964778269687912828951323007990, 844181127621537566382905185176676, 556587263569874292126677090542478]

def b0 : List Nat := [1086171346629]

def p0 : List Nat := [22]

def b1 : List Nat := [1077047675271, 1074983940133, 1073144514684, 1071573221381, 1070236969056, 1069100122598, 1068153578326, 1067381606228, 1066762159562, 1066274688519, 1065898966561, 1065615310090, 1065405489853, 1065253474878, 1065145698701, 1065071012999, 1065020491341, 1064987173534, 1064965781243, 1064952426945, 1064944333948, 1064939581083, 1064936881856, 1064935403217, 1064934624217, 1064934230851, 1064934041180, 1064933954215, 1064933916470, 1064933901038, 1064933895127, 1064933893018, 1064933892321, 1064933892109, 1064933892050, 1064933892036, 1064933892032, 1064933892032, 1064933892032]

def p1 : List Nat := [11, 10, 10, 9, 8, 8, 7, 6, 5, 4, 3, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def b2 : List Nat := [1074772560009, 1069706091086, 1065494813609, 1061702597689, 1058583859820, 1055996744515, 1053832426794, 1051997411802, 1050520688082, 1049345666259, 1048427495956, 1047727656790, 1047210382528, 1046841005784, 1046586418890, 1046416933982, 1046307942813, 1046240381394, 1046200187363, 1046177372781, 1046165103859, 1046158903202, 1046155985111, 1046154719602, 1046154219671, 1046154042045, 1046153986074, 1046153970677, 1046153967047, 1046153966330, 1046153966214, 1046153966200, 1046153966199, 1046153966198, 1046153966198]

def p2 : List Nat := [15, 14, 14, 13, 12, 11, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def b3 : List Nat := [1065605776736, 1054100281156, 1045668905792, 1039412303538, 1034739387847, 1031245231188, 1028639936477, 1026715262260, 1025321213075, 1024342761500, 1023684703318, 1023267091464, 1023023458887, 1022897616646, 1022842559370, 1022823100442, 1022817832347, 1022816814402, 1022816689841, 1022816682597]

def p3 : List Nat := [19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]

def scale : Nat := 1000000000000
def requirement : Nat := 67
def lo (l : Nat) : Nat := if l = 0 then 0 else if l = 1 then 22 else if l = 2 then 33 else if l = 3 then 48 else 67
def hi (l : Nat) : Nat := if l = 0 then 0 else if l = 1 then 60 else 67
def domain (l : Nat) : Finset Nat := Finset.Icc (lo l) (hi l)
def bound (l c : Nat) : Nat :=
  if l = 0 then b0.getD (c-lo l) 0 else if l = 1 then b1.getD (c-lo l) 0
  else if l = 2 then b2.getD (c-lo l) 0 else if l = 3 then b3.getD (c-lo l) 0 else scale
def policy (l c : Nat) : Nat :=
  if l = 0 then p0.getD (c-lo l) 0 else if l = 1 then p1.getD (c-lo l) 0
  else if l = 2 then p2.getD (c-lo l) 0 else p3.getD (c-lo l) 0
def cap (l : Nat) : Nat := if l = 0 then 60 else 30
def tail (l f : Nat) : Nat :=
  if cap l < f then 0 else
  if l = 0 then (if 22 ≤ f then topTail.getD (f-22) 0 else 0)
  else if l = 1 then lower201.getD f 0 else lower202.getD f 0
def q (l : Nat) : Nat := if l = 0 then 2^256 else 4*2^128
def coefficient (l : Nat) : Nat := if l = 0 then 7*2^126 - tail 0 22 else 7
def accepted (l c : Nat) : Nat := coefficient l * tail l (policy l c)
def nextCredit (c s : Nat) : Nat := min requirement (c+s)
def weight (l c : Nat) : Nat :=
  ((Finset.range (cap l+1-policy l c)).sum fun j =>
    let s := policy l c+j
    (tail l s-tail l (s+1))*bound (l+1) (nextCredit c s))
def guard (l c : Nat) : Prop :=
  1310720000000000 * (coefficient l * weight l c + (q l-accepted l c)*bound l c) ≤
  1310713068528192 * q l * bound l c

theorem all95_guards : ∀ l ∈ Finset.range 4, ∀ c ∈ domain l, guard l c := by decide +kernel

theorem timeout_boundary : ∀ l ∈ Finset.range 5, ∀ c ∈ domain l, scale ≤ bound l c := by decide +kernel

theorem rates_valid : ∀ l ∈ Finset.range 4, ∀ c ∈ domain l,
    0 < accepted l c ∧ accepted l c ≤ q l := by decide +kernel

/-- Needed to replace the conservative common top preimage coefficient with
its larger actual value without invalidating the continuation Bellman guard. -/
theorem continuation_gap : ∀ l ∈ Finset.range 4, ∀ c ∈ domain l,
    coefficient l * weight l c ≤ accepted l c * bound l c := by decide +kernel

theorem policy_in_cap : ∀ l ∈ Finset.range 4, ∀ c ∈ domain l,
    policy l c ≤ cap l := by decide +kernel

theorem tail_monotone : ∀ l ∈ Finset.range 4, ∀ c ∈ domain l,
    ∀ j ∈ Finset.range (cap l+1-policy l c),
    tail l (policy l c+j+1) ≤ tail l (policy l c+j) := by decide +kernel

/-- Every positive-mass transition stays within the next layer's proved domain. -/
theorem domain_closed : ∀ l ∈ Finset.range 4, ∀ c ∈ domain l,
    ∀ j ∈ Finset.range (cap l+1-policy l c),
    0 < tail l (policy l c+j)-tail l (policy l c+j+1) →
      nextCredit c (policy l c+j) ∈ domain (l+1) := by decide +kernel

theorem final_domain : domain 4 = {67} := by decide +kernel

theorem terminal_covers_deficit : ∀ c ∈ domain 3,
    67 ≤ c + policy 3 c := by decide +kernel

def digestBound : Nat := 1014354563596
theorem digest_guard :
  1310720000000000 * (1353 * 51668613533684827311648164987144309062238208 * scale +
    (2^167-1353*51668613533684827311648164987144309062238208)*digestBound) ≤
  1310713068528192 * 2^167 * digestBound := by decide +kernel

def factor : ℚ := (digestBound:ℚ)*(bound 0 0:ℚ)/(scale:ℚ)^2
def allowance : ℚ :=
  let x : ℚ := (6931471803/10000000000) * (131072-112654)/131072
  1+x+x^2/2+x^3/6

theorem rounded_fits_original_fixed_bound : factor ≤ allowance := by
  norm_num [factor, allowance, digestBound, bound, b0, lo, scale]

/-- 900 conservative timeout bits at fuel2^23 for every reachable layer search.
This does not prove completeness until indexed fresh-output laws are linked. -/
theorem every_rate900 : ∀ l ∈ Finset.range 4, ∀ c ∈ domain l,
    900*6931471808*q l ≤ 2^23*accepted l c*10000000000 := by decide +kernel

theorem conditional_cycle_target : (7032:Nat)-17 = 7015 := by decide
theorem conditional_product : (5310:Nat)*7015 = 37249650 := by decide
end ClaudeWCT.WCT9.Research.DeficitPacket17

/-!
Research-only relaxed producer. Unlike the surplus-only proposal, it must start
from the broad decoder, NOT `producerDecode`: that would silently discard the
words which pay a local deficit. All original zero/rank safety guards survive.
This module is not used by Solution. No machine/resource/security link is claimed.
-/
namespace ClaudeWCT.WCT9.Research.DeficitProducer
open SigGolfCandidate.T3

def decodeWithFloor (lay : Layer) (floor : Nat) (answer : Digest) : Option (List Nat) :=
  match decode lay answer with
  | some digits =>
      if floor + dispatchPenalty lay digits ≤ wordCredit lay digits + 4 * savedCopies lay digits ∧
          producerZeroBound lay digits ∧ producerRankBound lay answer then some digits else none
  | none => none

/-- The original producer is the special case where no floor is relaxed. -/
theorem original_floor (lay : Layer) (answer : Digest) :
    decodeWithFloor lay (producerFloor lay) answer = producerDecode lay answer := rfl

/-- Broader floor acceptance still decodes under the unchanged verifier codebook. -/
theorem sound {lay : Layer} {floor : Nat} {answer : Digest} {digits : List Nat}
    (h : decodeWithFloor lay floor answer = some digits) : decode lay answer = some digits := by
  cases hd : decode lay answer with
  | none => simp [decodeWithFloor, hd] at h
  | some ds =>
      simp only [decodeWithFloor, hd] at h
      split_ifs at h
      · cases h
        exact hd
      · simp at h

theorem accepted_guards {lay : Layer} {floor : Nat} {answer : Digest} {digits : List Nat}
    (h : decodeWithFloor lay floor answer = some digits) :
    floor + dispatchPenalty lay digits ≤ wordCredit lay digits + 4 * savedCopies lay digits ∧
      producerZeroBound lay digits ∧ producerRankBound lay answer := by
  cases hd : decode lay answer with
  | none => simp [decodeWithFloor, hd] at h
  | some ds =>
      simp only [decodeWithFloor, hd] at h
      split_ifs at h with hg
      · cases h
        exact hg
      · simp at h

/-- Absolute credit accounting is sound for an accepted word even at floor0. -/
theorem accepted_credit {lay : Layer} {floor : Nat} {answer : Digest} {digits : List Nat}
    (h : decodeWithFloor lay floor answer = some digits) :
    floor ≤ wordCredit lay digits + 4 * savedCopies lay digits - dispatchPenalty lay digits := by
  have hguard := (accepted_guards h).1
  omega

/-- A key-local, fixed-floor canonical search. For layer0 the policy supplies
floor22, so the old selector is unchanged. For lower layers the reserved-bit
selector is independent of the floor. Empty fuel fails; no dummy word is signed.
The ancestor-first caller and compiled machine link are not implemented here. -/
def counterSearch (lay : Layer) (floor tree leaf : Nat) (msg : LayerMsg)
    (counter : Nat) : Nat → M (Option (BitVec 32 × List Nat × BitVec 64))
  | 0 => pure none
  | fuel+1 => do
      let answer ← publicHash (layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 counter))
      match decodeWithFloor lay floor (encodingAnswer lay answer) with
      | some digits => pure (some (BitVec.ofNat 32 counter, digits, encodingHint lay answer))
      | none => counterSearch lay floor tree leaf msg (counter+1) fuel

def SearchResult (lay : Layer) (floor : Nat)
    (out : Option (BitVec 32 × List Nat × BitVec 64)) : Prop :=
  ∀ counter digits hint, out = some (counter,digits,hint) →
    ∃ answer, decodeWithFloor lay floor answer = some digits

/-- One admitted compression per probe, including rejected probes and timeouts.
This is a deterministic fuel bound, not the missing signing exponential moment. -/
theorem bound_counterSearch (lay : Layer) (floor tree leaf : Nat) (msg : LayerMsg) :
    ∀ fuel counter, SigGolfCandidate.T3.Cost.CBound (SearchResult lay floor) fuel
      (counterSearch lay floor tree leaf msg counter fuel) := by
  intro fuel
  induction fuel with
  | zero =>
      intro counter
      exact .pure none 0 (by simp [SearchResult])
  | succ fuel ih =>
      intro counter
      unfold counterSearch
      refine (ClaudeWCT.WCT9.Cost.bound_layerEncodingRaw lay tree leaf msg
        (BitVec.ofNat 32 counter)).bind' (l := fuel) (fun answer _ => ?_) (by omega)
      cases hs : decodeWithFloor lay floor (encodingAnswer lay answer) with
      | none => exact ih (counter+1)
      | some digits =>
          refine .pure (some (BitVec.ofNat 32 counter, digits, encodingHint lay answer)) fuel ?_
          intro other values hint hv
          obtain ⟨rfl, heq⟩ := Prod.mk.inj (Option.some.inj hv)
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          exact ⟨encodingAnswer lay answer, hs⟩

end ClaudeWCT.WCT9.Research.DeficitProducer

/-! Isolated conditional arithmetic and concrete decoder witnesses.
No honest-oracle realization, security consequence, or machine bound is claimed. -/
namespace ClaudeWCT.WCT9.Research.DeficitAuxiliary
open scoped BigOperators
open DeficitPacket17
set_option maxHeartbeats 1500000
set_option exponentiation.threshold 4096
set_option maxRecDepth 100000
set_option Elab.async false

def factor : ℚ := (digestBound : ℚ) * (bound 0 0 : ℚ) / (scale : ℚ)^2
def allowance (fixed : Nat) : ℚ :=
  let x := (6931471803 / 10000000000 : ℚ) * ((131072 : ℚ)-fixed) / 131072
  1 + x + x^2/2 + x^3/6

theorem fixed_headroom91 : factor ≤ allowance 112745 := by
  norm_num [factor, allowance, digestBound, bound, b0, lo, scale]
theorem next_fixed_fails : allowance 112746 < factor := by
  norm_num [factor, allowance, digestBound, bound, b0, lo, scale]

/-- The finite model's conservative minimum rate supports519 failure bits at
lower fuel2^22. Actual oracle-law and indexed completeness transport is pending. -/
theorem fuel2_22_519 : ∀ l ∈ Finset.range 4, ∀ c ∈ domain l,
    (519 : ℚ) * (6931471808/10000000000) ≤
      (2^22 : ℚ) * (accepted l c : ℚ)/(q l : ℚ) := by decide +kernel

theorem indexed_completeness_arithmetic :
    (2 : ℚ)^256 * (1/2^450) + 95*2^301*(1/2^519) ≤ 1/2^193 := by
  norm_num

/-- Credit accounting for a replacement total-cost bridge. This does NOT prove
that the current machine cost theorems expose the four hypotheses. -/
theorem aggregate_cost {a b c d x y z w p q r s ba bb bc bd : Nat}
    (ha : a+x ≤ ba+p) (hb : b+y ≤ bb+q)
    (hc : c+z ≤ bc+r) (hd : d+w ≤ bd+s)
    (hcredit : 67+p+q+r+s ≤ x+y+z+w) :
    a+b+c+d+67 ≤ ba+bb+bc+bd := by omega

open SigGolfCandidate.T3

def witness1 : Digest := BitVec.ofNat 128 291670600217947254399813484094883514660
def witness2 : Digest := BitVec.ofNat 128 291670600217947254399813484094900291876

theorem relaxed_word1 :
    DeficitProducer.decodeWithFloor 1 0 witness1 ≠ none ∧
    producerDecode 1 witness1 = none ∧
    wordCredit 1 (dataDigits 1 witness1 ++ [0]) +
      4 * savedCopies 1 (dataDigits 1 witness1 ++ [0]) = 0 := by decide +kernel

theorem relaxed_word2 :
    DeficitProducer.decodeWithFloor 2 0 witness2 ≠ none ∧
    producerDecode 2 witness2 = none ∧
    wordCredit 2 (dataDigits 2 witness2 ++ [0]) +
      4 * savedCopies 2 (dataDigits 2 witness2 ++ [0]) = 0 := by decide +kernel

end ClaudeWCT.WCT9.Research.DeficitAuxiliary

/-!
Iteration35 research-only: public one-byte replay hint for an ancestor-first
credit policy. Top floor22, first lower floor8, second lower floor <=12,
last lower floor closes absolute requirement67. No production import.
This packet is NOT locally compiled. Cardinality, indexed oracle laws,
retained-chain signer, expander/machine, and total-credit cycle links remain open.
-/
namespace ClaudeWCT.WCT9.Research.ReplayHintPacket
open scoped BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option Elab.async false

def topTail : List (Nat) := [61400435184999209708243105926444986, 59118617930026709864893449254178315, 56412336783017058316068591023786605, 53295959781860291461652388304869136, 49806927014954033575633984287066893, 46004495892090709324135340347215286, 41966509284957565736683815445044472, 37784346796747798898882944075578719, 33556494098373355261802670185067659, 29381705508090847735214416823465620, 25352598451633301895212418337094824, 21550055138460539121005712498594116, 18038922516042673169712366729388162, 14865576200900011763143189603295225, 12057313039939885305450975013665789, 9623171885634974026218476078963163, 7556017413940276147324030195764337, 5835641688348896382215925195925468, 4432272059926264843964730197382742, 3310014002440564320154415039403910, 2430075159226334904481208195618824, 1753548587265206240940716861370008, 1243507298933139131847504226685855, 866422363871016789661605025290933, 593024484449256649376703914897957, 398648194099359675586553324521462, 263143289819068731882542857793680, 170520932313612603616040297997315, 108452029234913937207210744399775, 67681528061020731133017041223140, 41434666577435726199206098673876, 24876434705568674870072937628657, 14642570109732014272361070643747, 8447610390764332318052875708640, 4775231069063915297196063992764, 2643863793922806413096479059218, 1433287116216187295616415326790, 760562908146087760448865965031, 394868546845875750082277964728]

def lower201 : List (Nat) := [58310357933255944251288942793955306, 58310336012616914532263309980386610, 58309964133770526751364164401473901, 58306966094947086560817020393648221, 58291665272054065360300937168071823, 58235979209929063613485945202021484, 58081065070836601986435334001201303, 57734422269950804638245936422699817, 57082284908894457343149900469675755, 56008308245340494107407867421618550, 54408112790925688753987891000775297, 52205271644720435491391227169461376, 49374072630607869054258945664192558, 45952123965212487041454738440237319, 42029416161260738105653905283368946, 37732487237534268109769523863508583, 33219077116456466734442605936680683, 28664985933359420873343381352063905, 24235153322760640239450316665361627, 20065435145178632167443389224887757, 16263529072464441716121015897211781, 12905382641046880545393600877316626, 10025445665860223537158612684490582, 7621599354625958305222293312435845, 5669547627220668879271331480744985, 4128193821255747260672218325421066, 2942048706503813034899113231613428, 2051022613339333562521797093110122, 1398798886881335108310354544410070, 933764142327532692446042567822983, 609829887999743907751787127862225]

def lower202 : List (Nat) := [46095893039550580864177812822640627, 46095878730828114658310970930783511, 46095632698271399271903924557007149, 46093622162280767402854262400034781, 46083220051762603203197505455308382, 46044839038753628463163023920930993, 45936596838824362937551402714118524, 45691135823106665795476360474637864, 45223465703457967253341632145154723, 44444210514614632453013305786840214, 43270547465047728058677790349033924, 41638240191617962951793025493843981, 39519142012181130951313701394522033, 36932462237659353802654691028823546, 33938695241273962698044050625507951, 30628501601218537764038958691967944, 27118955945433625862311616013112528, 23544556756865226968976372771210898, 20035460936274711397956848027222226, 16702112927114157723026801121707550, 13634676664941173437298540260835089, 10899946103222341084509908275940421, 8532840114673252322982302606282604, 6538694663634745651817691106662084, 4904014634779156866118516287689970, 3600868121141033724962085329108155, 2588446996344715075918422701594176, 1820596106065863815301062825650921, 1252964778269687912828951323007990, 844181127621537566382905185176676, 556587263569874292126677090542478]

def b0 : List (Nat) := [1086627496771]

def p0 : List (Nat) := [22]

def b1 : List (Nat) := [1080657742435, 1076797816289, 1073999742475, 1071918164088, 1070340410421, 1069128473106, 1068189536289, 1067459344434, 1066892097950, 1066455234294, 1066125081626, 1065881250588, 1065704968866, 1065580545027, 1065495011493, 1065437858989, 1065400797777, 1065377505256, 1065363339237, 1065355021778, 1065350323320, 1065347781163, 1065346470767, 1065345831249, 1065345537857, 1065345412361, 1065345362776, 1065345344867, 1065345339025, 1065345337326, 1065345336892, 1065345336797, 1065345336779, 1065345336776, 1065345336776, 1065345336776, 1065345336776, 1065345336776, 1065345336776]

def p1 : List (Nat) := [8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8]

def b2 : List (Nat) := [1141947436964, 1113148863132, 1094496490948, 1081826634640, 1072944598838, 1066583685177, 1061964900927, 1058583859820, 1055996744515, 1053832426794, 1051997411802, 1050520688082, 1049345666259, 1048427495956, 1047727656790, 1047210382528, 1046841005784, 1046586418890, 1046416933982, 1046307942813, 1046240381394, 1046200187363, 1046177372781, 1046165103859, 1046158903202, 1046155985111, 1046154719602, 1046154219671, 1046154042045, 1046153986074, 1046153970677, 1046153967047, 1046153966330, 1046153966214, 1046153966200, 1046153966199, 1046153966198, 1046153966198]

def p2 : List (Nat) := [12, 12, 12, 12, 12, 12, 12, 12, 11, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def b3 : List (Nat) := [1399713564538, 1265316566082, 1186609472111, 1137022677555, 1104166255105, 1081569239841, 1065605776736, 1054100281156, 1045668905792, 1039412303538, 1034739387847, 1031245231188, 1028639936477, 1026715262260, 1025321213075, 1024342761500, 1023684703318, 1023267091464, 1023023458887, 1022897616646, 1022842559370, 1022823100442, 1022817832347, 1022816814402, 1022816689841, 1022816682597]

def p3 : List (Nat) := [25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]

def domainLo : List (Nat) := [0, 22, 30, 42, 67]

def domainHi : List (Nat) := [0, 60, 67, 67, 67]

def scale : Nat := 1000000000000
def requirement : Nat := 67
def lo (l : Nat) : Nat := domainLo.getD l 67
def hi (l : Nat) : Nat := domainHi.getD l 67
def domain (l : Nat) : Finset Nat := Finset.Icc (lo l) (hi l)
def bound (l c : Nat) : Nat :=
  if l = 0 then b0.getD (c-lo l) 0 else if l = 1 then b1.getD (c-lo l) 0
  else if l = 2 then b2.getD (c-lo l) 0 else if l = 3 then b3.getD (c-lo l) 0 else scale
def policy (l c : Nat) : Nat :=
  if l = 0 then p0.getD (c-lo l) 0 else if l = 1 then p1.getD (c-lo l) 0
  else if l = 2 then p2.getD (c-lo l) 0 else p3.getD (c-lo l) 0
def cap (l : Nat) : Nat := if l = 0 then 60 else 30
def tail (l f : Nat) : Nat :=
  if cap l < f then 0 else
  if l = 0 then (if 22 ≤ f then topTail.getD (f-22) 0 else 0)
  else if l = 1 then lower201.getD f 0 else lower202.getD f 0
def q (l : Nat) : Nat := if l = 0 then 2^256 else 4*2^128
def coefficient (l : Nat) : Nat := if l = 0 then 7*2^126 - tail 0 22 else 7
def accepted (l c : Nat) : Nat := coefficient l * tail l (policy l c)
def nextCredit (c s : Nat) : Nat := min requirement (c+s)
def weight (l c : Nat) : Nat :=
  ((Finset.range (cap l+1-policy l c)).sum fun j =>
    let s := policy l c+j
    (tail l s-tail l (s+1))*bound (l+1) (nextCredit c s))
def guard (l c : Nat) : Prop :=
  1310720000000000 * (coefficient l * weight l c + (q l-accepted l c)*bound l c) ≤
  1310713068528192 * q l * bound l c

theorem all104_guards : ∀ l ∈ Finset.range 4, ∀ c ∈ domain l, guard l c := by decide +kernel

theorem timeout_boundary : ∀ l ∈ Finset.range 5, ∀ c ∈ domain l, scale ≤ bound l c := by decide +kernel

theorem rates_valid : ∀ l ∈ Finset.range 4, ∀ c ∈ domain l,
    0 < accepted l c ∧ accepted l c ≤ q l := by decide +kernel

theorem continuation_gap : ∀ l ∈ Finset.range 4, ∀ c ∈ domain l,
    coefficient l * weight l c ≤ accepted l c * bound l c := by decide +kernel

theorem policy_in_cap : ∀ l ∈ Finset.range 4, ∀ c ∈ domain l,
    policy l c ≤ cap l := by decide +kernel

theorem tail_monotone : ∀ l ∈ Finset.range 4, ∀ c ∈ domain l,
    ∀ j ∈ Finset.range (cap l+1-policy l c),
    tail l (policy l c+j+1) ≤ tail l (policy l c+j) := by decide +kernel

theorem domain_closed : ∀ l ∈ Finset.range 4, ∀ c ∈ domain l,
    ∀ j ∈ Finset.range (cap l+1-policy l c),
    0 < tail l (policy l c+j)-tail l (policy l c+j+1) →
      nextCredit c (policy l c+j) ∈ domain (l+1) := by decide +kernel

theorem final_domain : domain 4 = {67} := by decide +kernel

theorem terminal_covers_deficit : ∀ c ∈ domain 3,
    67 ≤ c + policy 3 c := by decide +kernel

theorem first_lower_fixed : ∀ c ∈ domain 1, policy 1 c = 8 := by decide +kernel

theorem second_lower_capped : ∀ c ∈ domain 2, policy 2 c ≤ 12 := by decide +kernel

def digestBound : Nat := 1014354563596
theorem digest_guard :
  1310720000000000 * (1353 * 51668613533684827311648164987144309062238208 * scale +
    (2^167-1353*51668613533684827311648164987144309062238208)*digestBound) ≤
  1310713068528192 * 2^167 * digestBound := by decide +kernel

def factor : ℚ := (digestBound:ℚ)*(bound 0 0:ℚ)/(scale:ℚ)^2
def allowance (fixed : Nat) : ℚ :=
  let x : ℚ := (6931471803/10000000000) * (131072-(fixed:ℚ))/131072
  1+x+x^2/2+x^3/6

theorem rounded_fits_original_fixed_bound : factor ≤ allowance 112654 := by
  norm_num [factor, allowance, digestBound, bound, b0, lo, domainLo, scale]

/-- Conservative timeout arithmetic; actual indexed fresh laws remain unproved. -/
theorem every_rate800 : ∀ l ∈ Finset.range 4, ∀ c ∈ domain l,
    800*6931471808*q l ≤ 2^25*accepted l c*10000000000 := by decide +kernel

theorem fuel_below_counter_window : (2:Nat)^25 < 2^32 := by decide

theorem conditional_product : (5311:Nat)*7015 = 37256665 := by decide
theorem conditional_improvement : (5310:Nat)*7031-5311*7015 = 77945 := by decide

def hintPairs : List (Nat × Nat) := [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (0, 15), (0, 16), (0, 17), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (1, 14), (1, 15), (1, 16), (1, 17), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (2, 14), (2, 15), (2, 16), (2, 17), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13), (3, 14), (3, 15), (3, 16), (3, 17), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (4, 14), (4, 15), (4, 16), (4, 17), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (5, 13), (5, 14), (5, 15), (5, 16), (5, 17), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (6, 14), (6, 15), (6, 16), (6, 17), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (7, 13), (7, 14), (7, 15), (7, 16), (7, 17), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (8, 13), (8, 14), (8, 15), (8, 16), (8, 17), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (9, 11), (9, 12), (9, 13), (9, 14), (9, 15), (9, 16), (9, 17), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (10, 10), (10, 11), (10, 12), (10, 13), (10, 14), (10, 15), (10, 16), (10, 17), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (11, 6), (11, 7), (11, 8), (11, 9), (11, 10), (11, 11), (11, 12), (11, 13), (11, 14), (11, 15), (11, 16), (11, 17), (11, 18), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (12, 5), (12, 6), (12, 7), (12, 8), (12, 9), (12, 10), (12, 11), (12, 12), (12, 13), (12, 14), (12, 15), (12, 16), (12, 17), (12, 18), (12, 19), (12, 20), (12, 21), (12, 22), (12, 23), (12, 24), (12, 25)]

def decodeHint (tag : Fin 256) : Option (Nat × Nat) := hintPairs[tag.val]?
def encodeHint (pair : Nat × Nat) : Option (Fin 256) :=
  let ix := hintPairs.idxOf pair
  if h : ix < hintPairs.length ∧ ix < 256 then some ⟨ix, h.2⟩ else none

theorem hint_table_length : hintPairs.length = 243 := by decide +kernel

theorem hint_table_nodup : hintPairs.Nodup := by decide +kernel

theorem byte_roundtrip : ∀ tag : Fin 256,
    (decodeHint tag).bind encodeHint = (if tag.val < 243 then some tag else none) := by decide +kernel

theorem pair_roundtrip : ∀ pair ∈ hintPairs,
    (encodeHint pair).bind decodeHint = some pair := by decide +kernel

/-- Every reachable positive-mass clipped prefix has an encodable replay pair.
Counts and realizability of these score bins still require actual oracle links. -/
theorem reachable_pair_in_table :
    ∀ s0 ∈ Finset.Icc 22 60, ∀ s1 ∈ Finset.Icc 8 30,
    let c2 := nextCredit s0 s1
    ∀ s2 ∈ Finset.Icc (policy 2 c2) 30,
    (policy 2 c2, 67-nextCredit c2 s2) ∈ hintPairs := by decide +kernel

end ClaudeWCT.WCT9.Research.ReplayHintPacket

/-!
Prototype floor-guided expander. The hint is input to EXPAND only and is not
part of the old witness or checked by the unchanged verifier. An invalid hint
fails before any oracle query. A wrong valid hint can fail search/root recovery
or canonical credit rebinding;
it never makes the verifier accept by itself. Honest hint/replay equivalence,
codec/machine links and expansion budget are not established by this function.
-/
namespace ClaudeWCT.WCT9.Research.ReplayHintExpand
open SigGolfCandidate.T3

def replayFloor (pair : Nat × Nat) (lay : Layer) : Nat :=
  if lay = 0 then 22 else if lay = 1 then 8 else if lay = 2 then pair.1 else pair.2

/-- Canonical public hint is computed from the recovered selected words, not
accepted solely because it fits the byte table. This guard is necessary for
signature-pair freshness; sufficiency still needs the actual security proof. -/
def replayPair (credits : List Nat) : Nat × Nat :=
  let c2 := ReplayHintPacket.nextCredit (credits.getD 0 0) (credits.getD 1 0)
  let c3 := ReplayHintPacket.nextCredit c2 (credits.getD 2 0)
  (ReplayHintPacket.policy 2 c2, 67-c3)

def score (lay : Layer) (digits : List Nat) : Nat :=
  min (if lay = 0 then 60 else 30) (PooledCredit.effectiveCredit lay digits)

def layers (sig : Signature) (index : Nat) (pair : Nat × Nat) :
    Nat → LayerMsg → M (Option (Digest × List (BitVec 32) × BitVec 64 × List Nat))
  | 0, _ => pure none
  | n+1, msg => do
      let lay : Layer := Fin.ofNat 4 n
      let (leaf, tree) := route index lay
      let some (counter, digits, hint) ← DeficitProducer.counterSearch lay
        (replayFloor pair lay) tree leaf msg 0 (2^25) | pure none
      if n = 0 then
        let root ← recoverLayer (toT3Signature sig) index lay digits
        pure (some (root, [counter], hint, [score lay digits]))
      else
        let rootPair ← recoverLayerPair sig index lay digits
        let some (root, counters, topHint, credits) ← layers sig index pair n (.pair rootPair.1 rootPair.2) | pure none
        pure (some (root, counters ++ [counter], topHint, credits ++ [score lay digits]))

/-- Same old signature payload plus an external public byte. No new witness field. -/
def expand (message : Message) (pk : Digest) (sig : Signature) (tag : Fin 256) :
    M (Option Witness) := do
  let some pair := ReplayHintPacket.decodeHint tag | pure none
  let some (counter, output) ← digestSearch sig.rho message 0 attemptLimit | pure none
  let index := digestIndex output
  let top ← recoverFts sig index output
  let some (root, counters, topHint, credits) ← layers sig index pair 4 (.pair top.1 top.2) | pure none
  if root ≠ pk then return none
  if replayPair credits ≠ pair then return none
  pure (some ⟨sig, counter, fun lay => counters.getD lay.val 0, topHint⟩)

/-- Pure model: extra byte is expansion advice; verifier consumes only the old
witness. This is definitional erasure ONLY for the witness branch. The contract's
signature branch requires canonical byte binding; never infer a general
security reduction from verifier erasure. -/
def verifyWithAdvice (message : Message) (pk : Digest) (_tag : Fin 256) (w : Witness) : M Bool :=
  ClaudeWCT.WCT9.verify message pk w

theorem verifier_erases_hint (message : Message) (pk : Digest) (a b : Fin 256) (w : Witness) :
    verifyWithAdvice message pk a w = verifyWithAdvice message pk b w := rfl

end ClaudeWCT.WCT9.Research.ReplayHintExpand

/-!
Research-only integration of the r35 public replay-floor byte with the actual
5,310-byte compact payload. Not imported by Solution. No production size/cycle
claim changes. Compilation, machine links, resource bounds and security remain
external obligations. Unlike ReplayHintExpand.expand, this expander completes
the omitted sibling once, after recovering the top level-11 node.
-/
namespace ClaudeWCT.WCT9.Research.CompactReplayHint
open OracleComp OracleSpec SigGolfCandidate.Legacy SigGolfCandidate.T3
open ClaudeWCT.W9.T3M

abbrev HBytes := Bytes 5311

def payloadBase : Nat := 2^(8*5310)

def pack (payload : CBytes) (tag : Fin 256) : HBytes :=
  BitVec.ofNat _ (payload.toNat + payloadBase * tag.val)

def payload (bytes : HBytes) : CBytes := BitVec.ofNat _ bytes.toNat

def tag (bytes : HBytes) : Fin 256 :=
  ⟨bytes.toNat / payloadBase % 256, Nat.mod_lt _ (by decide)⟩

/-- The public hint is the final byte, not an ignored witness field. -/
theorem payloadBase_pos : 0 < payloadBase := by
  unfold payloadBase
  positivity

/-- No reduction of a 42,480-bit numeral is needed for the byte split. -/
theorem totalBase : (2 : Nat) ^ (8*5311) = payloadBase * 256 := by
  change (2 : Nat) ^ (42480+8) = 2^42480 * 2^8
  rw [pow_add]

theorem pack_toNat (p : CBytes) (t : Fin 256) :
    (pack p t).toNat = p.toNat + payloadBase * t.val := by
  unfold pack
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  rw [totalBase]
  exact lt_split _ _ _ _ p.isLt t.isLt

theorem payload_pack (p : CBytes) (t : Fin 256) : payload (pack p t) = p := by
  apply BitVec.eq_of_toNat_eq
  rw [payload, BitVec.toNat_ofNat, pack_toNat]
  exact split_mod _ _ _ p.isLt

theorem tag_pack (p : CBytes) (t : Fin 256) : tag (pack p t) = t := by
  apply Fin.ext
  change (pack p t).toNat / payloadBase % 256 = t.val
  rw [pack_toNat, split_div _ _ _ p.isLt, Nat.mod_eq_of_lt t.isLt]

theorem pack_payload_tag (b : HBytes) : pack (payload b) (tag b) = b := by
  apply BitVec.eq_of_toNat_eq
  rw [pack_toNat]
  have ht : b.toNat / payloadBase < 256 := by
    apply (Nat.div_lt_iff_lt_mul payloadBase_pos).2
    rw [Nat.mul_comm, ← totalBase]
    exact b.isLt
  change b.toNat % payloadBase + payloadBase * (b.toNat / payloadBase % 256) = b.toNat
  rw [Nat.mod_eq_of_lt ht]
  exact Nat.mod_add_div _ _

/-- Semantic replay: return the shared top level-11 node as well as its root.
The omitted sibling does not affect any selected word, credit, or counter. -/
def layers (sig : Signature) (index : Nat) (pair : Nat × Nat) :
    Nat → LayerMsg → M (Option (Digest × Digest × List (BitVec 32) × BitVec 64 × List Nat))
  | 0, _ => pure none
  | n+1, msg => do
      let lay : Layer := Fin.ofNat 4 n
      let (leaf, tree) := route index lay
      let some (counter, digits, hint) ← DeficitProducer.counterSearch lay
        (ReplayHintExpand.replayFloor pair lay) tree leaf msg 0 (2^25) | pure none
      if n = 0 then
        let v ← topFold sig index digits
        let root ← topNode index v (topSib sig)
        pure (some (v, root, [counter], hint, [ReplayHintExpand.score lay digits]))
      else
        let rootPair ← recoverLayerPair sig index lay digits
        let some (v, root, counters, topHint, credits) ←
          layers sig index pair n (.pair rootPair.1 rootPair.2) | pure none
        pure (some (v, root, counters ++ [counter], topHint,
          credits ++ [ReplayHintExpand.score lay digits]))

/-- Canonical floor binding is checked before completion search. It does not
refer to the omitted sibling. One retained top-node search, never full replay
for each of the 65,536 completions. This definition alone is not a budget proof. -/
def expand (message : Message) (pk : Digest) (bytes : HBytes) : M (Option Witness) := do
  let some pair := ReplayHintPacket.decodeHint (tag bytes) | pure none
  let sig := sigDecC (payload bytes)
  let some (counter, output) ← digestSearch sig.rho message 0 digestAttemptLimit | pure none
  let index := digestIndex output
  let forest ← recoverFts sig index output
  let some (v, root, counters, topHint, credits) ←
    layers sig index pair 4 (.pair forest.1 forest.2) | pure none
  if ReplayHintExpand.replayPair credits ≠ pair then return none
  if root = pk then
    return some ⟨sig, counter, fun lay => counters.getD lay.val 0, topHint⟩
  let some completion ← searchTop index v (topSib sig) pk searchFuel 1 | pure none
  pure (some ⟨fillTop sig completion, counter,
    fun lay => counters.getD lay.val 0, topHint⟩)

/-- Signer-side serialization is partial: an unencodable pair must fail rather
than silently emit a default byte. Retained-chain signing is not implemented. -/
def encode (sig : Signature) (pair : Nat × Nat) : Option HBytes := do
  let hint ← ReplayHintPacket.encodeHint pair
  pure (pack (sigBC sig) hint)

/-- Conditional resource bridge constants. Search/recovery equivalence with a
new honest signer is NOT proved by these arithmetic checks. If its search work
is shared, expansion is bounded by signing work plus this entire old recovery
ceiling and the retained top-sibling completion search. -/
def replayOverhead : Nat := 621 + searchFuel

theorem replay_overhead_eq : replayOverhead = 66156 := by decide

theorem replay_overhead_le_sign_budget : replayOverhead ≤ 131072 := by decide

theorem expand_budget_ratio : (8 : Nat) * 131072 = 1048576 := by decide

/-- Weighted AM-GM/concavity gives x^(1/8) ≤ (7+x)/8. If the shared-search
pathwise domination is proved, the signing exponential moment ≤2 therefore
implies an expansion moment ≤(9/8)^2, below2. This lemma checks ONLY the rational
last step; the real/ENNReal law transport is a separate hosted obligation. -/
theorem conditional_moment_arithmetic :
    (9 : ℚ)/8 * ((7+2)/8) = 81/64 ∧ (81 : ℚ)/64 < 2 := by norm_num

theorem conditional_product : (5311 : Nat) * 7015 = 37256665 := by decide

end ClaudeWCT.WCT9.Research.CompactReplayHint

/-!
Iteration37 research-only: retain the selected lower WOTS chains while preparing
message-independent lower roots, then search ancestor first. This program is not
an image, certificate, or proof of adaptive oracle laws. Compression bounds for
the primitive retained chain are included; whole-tree coupling and machine
refinement remain hosted obligations. No production entry point changes.
-/
namespace ClaudeWCT.WCT9.Research.RetainedAncestor
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Legacy SigGolfCandidate.T3.Correctness SigGolfCandidate.T3.Cost
open ClaudeWCT.W9.T3M

abbrev Rows := List (List Digest)
abbrev Prepared := List (List Digest) × Rows

/-- Include the seed and every intermediate value. Use chainW, NOT T3.chain:
lower chain0's final step uses the high half. One hash per transition. -/
def chainTable (lay : Layer) (tree leaf i start : Nat) : Nat → Digest → M (List Digest)
  | 0, value => pure [value]
  | count+1, value => do
      let next ← chainW lay tree leaf i start 1 value
      let rest ← chainTable lay tree leaf i (start+1) count next
      pure (value :: rest)

/-- Actual OracleComp bound: retaining intermediate values costs no extra
compression and always returns count+1 values, including the seed. -/
theorem bound_chainTable (lay : Layer) (tree leaf i : Nat) :
    ∀ count start value, SigGolfCandidate.T3.Cost.CBound
      (fun row : List Digest => row.length = count+1) count
      (chainTable lay tree leaf i start count value) := by
  intro count
  induction count with
  | zero =>
      intro start value
      exact .pure _ 0 rfl
  | succ count ih =>
      intro start value
      simp only [chainTable]
      refine (Cost.bound_chainW lay tree leaf i start 1 value).bind'
        (l := count) (fun next _ => ?_) (by omega)
      refine (ih (start+1) next).bind' (l := 0) (fun row hrow => ?_) (by omega)
      exact .pure _ 0 (by simp only [List.length_cons]; omega)

/-- Fixed-answer projection at every retained position, not just the endpoint.
The index in chainW is the absolute step; the special high half is preserved. -/
theorem eval_chainTable_at (answers : Answers) (lay : Layer) (tree leaf i : Nat) :
    ∀ count start value j, j ≤ count →
      (evalWithAnswerFn answers (chainTable lay tree leaf i start count value)).getD j 0 =
        evalWithAnswerFn answers (chainW lay tree leaf i start j value) := by
  intro count
  induction count with
  | zero =>
      intro start value j hj
      have hj0 : j = 0 := by omega
      subst j
      rfl
  | succ count ih =>
      intro start value j hj
      cases j with
      | zero =>
          simpa only [chainTable, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
            List.getD_cons_zero]
      | succ j =>
          simp only [chainTable, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
            List.getD_cons_succ]
          rw [ih (start+1) (evalWithAnswerFn answers (chainW lay tree leaf i start 1 value)) j
            (by omega)]
          simpa only [Nat.add_comm 1 j] using
            (eval_chainW_add answers lay tree leaf i start 1 j value).symm

/-- Completing any valid cached position gives the original chain endpoint.
This is one deterministic ingredient of bottom-up recovery, not the entire
sign/expand replay theorem or an oracle-distribution claim. -/
theorem cached_value_completes (answers : Answers) (lay : Layer)
    (tree leaf i start count digit : Nat) (seed : Digest) (hd : digit ≤ count) :
    evalWithAnswerFn answers (chainW lay tree leaf i (start+digit) (count-digit)
      ((evalWithAnswerFn answers (chainTable lay tree leaf i start count seed)).getD digit 0)) =
        evalWithAnswerFn answers (chainW lay tree leaf i start count seed) := by
  rw [eval_chainTable_at answers lay tree leaf i count start seed digit hd]
  have h := eval_chainW_add answers lay tree leaf i start digit (count-digit) seed
  rw [Nat.add_sub_of_le hd] at h
  exact h.symm

/-- Prepare only the selected leaf's full table. All 43 end points are used in
the unchanged leaf hash; coefficient carry follows the ordinary leaf order. -/
def prepareLeaf (lay : Layer) (tree leaf : Nat) (carry : Digest) :
    M ((Digest × Rows) × Digest) := do
  let (coefs, carry) ← lowerCoefs lay tree leaf carry
  let rows ← (List.range (chainCount lay)).foldlM (fun (rows : Rows) i => do
    let row ← chainTable lay tree leaf i 0 (maxDigit lay i) (lowerFamilySeed coefs i)
    pure (rows ++ [row])) []
  let ends := (List.range (chainCount lay)).map fun i =>
    (rows.getD i []).getD (maxDigit lay i) 0
  let root ← lowerLeafHash lay tree leaf ends
  pure ((root, rows), carry)

/-- Actual retained selected-leaf program has the old fixed leaf bound. -/
theorem bound_prepareLeaf (lay : Layer) (tree leaf : Nat) (carry : Digest) :
    SigGolfCandidate.T3.Cost.CBound
      (fun result : (Digest × Rows) × Digest => result.1.2.length = chainCount lay)
      (Cost.leafCostP lay leaf) (prepareLeaf lay tree leaf carry) := by
  unfold prepareLeaf
  refine (Cost.bound_lowerCoefs lay tree leaf carry).bind'
    (l := Cost.digitTotal lay + leafHashCost lay) (fun res _ => ?_)
    (by unfold Cost.leafCostP; omega)
  refine Bound.bind' (l := leafHashCost lay) (Bound.foldlM_range (chainCount lay) _
    (fun i (rows : Rows) => rows.length = i) (fun i => maxDigit lay i) [] rfl
    (fun i _ rows hrows => ?_)) (fun rows hrows => ?_) ?_
  · refine (bound_chainTable lay tree leaf i (maxDigit lay i) 0
      (lowerFamilySeed res.1 i)).bind' (l := 0) (fun row _ => ?_) (by omega)
    exact .pure _ 0 (by simp only [List.length_append, List.length_singleton]; omega)
  · refine (Cost.bound_lowerLeafHash lay tree leaf _
      (by simp only [List.length_map, List.length_range])).bind'
      (l := 0) (fun root _ => ?_) (by omega)
    exact .pure _ 0 hrows
  · exact le_refl _

/-- Full tree, no child message or credit floor needed. Only the selected leaf
retains its chains. Non-selected leaves run the old builder unchanged. -/
def prepareTree (lay : Layer) (tree selected : Nat) : M Prepared := do
  let state ← (List.range (2^height lay)).foldlM
    (fun (state : List Digest × Rows × Digest) leaf => do
      if leaf = selected then
        let result ← prepareLeaf lay tree leaf state.2.2
        pure (state.1 ++ [result.1.1], result.1.2, result.2)
      else
        let result ← buildLeafPF lay tree leaf [] state.2.2
        pure (state.1 ++ [result.1.1], state.2.1, result.2)) ([], [], 0)
  let levels ← buildLevelsBelow 3 lay.val tree (height lay) state.1
  pure (levels, state.2.1)

/-- The actual prepared tree, including selected-chain retention, has exactly
the previous tree's compression bound. No second selected-leaf pass is hidden. -/
theorem bound_prepareTree (lay : Layer) (tree selected : Nat) :
    SigGolfCandidate.T3.Cost.CBound
      (fun result => SigGolfCandidate.T3.Cost.LevelShape (height lay) (height lay-1) result.1)
      (Cost.treeCostP lay) (prepareTree lay tree selected) := by
  unfold prepareTree
  refine Bound.bind' (l := 2^height lay-2) (Bound.foldlM_range (2^height lay) _
    (fun i (state : List Digest × Rows × Digest) => state.1.length = i)
    (Cost.leafCostP lay) ([],[],0) rfl (fun leaf _ state hstate => ?_))
    (fun state hstate => ?_) le_rfl
  · by_cases hs : leaf = selected
    · simp only [if_pos hs]
      refine (bound_prepareLeaf lay tree leaf state.2.2).bind' (l := 0)
        (fun result _ => ?_) (by omega)
      exact .pure _ 0 (by simp only [List.length_append, List.length_singleton]; omega)
    · simp only [if_neg hs]
      refine (Cost.bound_buildLeafPF lay tree leaf []
        (SigGolfCandidate.T3.Cost.validDigits_nil lay) state.2.2).bind' (l := 0)
        (fun result _ => ?_) (by omega)
      exact .pure _ 0 (by simp only [List.length_append, List.length_singleton]; omega)
  · refine (Cost.bound_buildLevelsBelow 3 lay.val tree (height lay) state.1 hstate
      (by fin_cases lay <;> decide)).bind' (l := 0)
      (fun levels hlevels => .pure _ 0 hlevels) (by omega)

def prepare (index : Nat) : M (List Prepared) :=
  ([1,2,3] : List Layer).mapM fun lay => do
    let (leaf, tree) := route index lay
    prepareTree lay tree leaf

/-- Selecting a signature value is now a lookup, never a prefix rehash. -/
def values (prepared : Prepared) (digits : List Nat) : List Digest :=
  (List.range prepared.2.length).map fun i =>
    (prepared.2.getD i []).getD (digits.getD i 0) 0

def piece (prepared : Prepared) (lay : Layer) (index : Nat) (digits : List Nat) : Pieces :=
  let path := (List.range (height lay)).map fun j =>
    (prepared.1.getD j []).getD ((route index lay).1 / 2^j ^^^ 1) 0
  (values prepared digits, path)

abbrev Selected := BitVec 32 × List Nat × BitVec 64

/-- Absolute/clipped credit is carried from stage0 to stage3. The input to stage
0 is the root pair of prepared layer1, not the forest; stage3 uses the forest.
Results are returned in layer order0,1,2,3. Search failures are propagated. -/
def select (index : Nat) (prepared : List Prepared) (forest : Digest × Digest)
    (fuel : Nat) : Nat → Nat → M (Option (List Selected))
  | 0, _ => pure (some [])
  | n+1, credit => do
      let stage := 4-(n+1)
      let lay : Layer := Fin.ofNat 4 stage
      let msg := if stage = 3 then LayerMsg.pair forest.1 forest.2 else
        let child : Layer := Fin.ofNat 4 (stage+1)
        let pair := topPair child (prepared.getD stage ([],[])).1
        LayerMsg.pair pair.1 pair.2
      let floor := ReplayHintPacket.policy stage credit
      let (leaf, tree) := route index lay
      let some found ← DeficitProducer.counterSearch lay floor tree leaf msg 0 fuel | pure none
      let next := ReplayHintPacket.nextCredit credit
        (min (ReplayHintPacket.cap stage) (ReplayHintExpand.score lay found.2.1))
      let some rest ← select index prepared forest fuel n next | pure none
      pure (some (found :: rest))

/-- Canonical replay pair computed from top and layer1 credits, exactly as in
the replay expander. It cannot silently be replaced by an external hint. -/
def replayPair (selected : List Selected) : Nat × Nat :=
  let s0 := min 60 (ReplayHintExpand.score 0 ((selected.getD 0 (0,[],0)).2.1))
  let s1 := min 30 (ReplayHintExpand.score 1 ((selected.getD 1 (0,[],0)).2.1))
  let s2 := min 30 (ReplayHintExpand.score 2 ((selected.getD 2 (0,[],0)).2.1))
  let c2 := ReplayHintPacket.nextCredit s0 s1
  (ReplayHintPacket.policy 2 c2, 67-ReplayHintPacket.nextCredit c2 s2)

/-- Compact research signer. The three prepared trees replace, not supplement,
the three old lower-tree builds. Top cached signing remains unchanged. This is
an executable design candidate, NOT a completeness/resource/security theorem. -/
def sign (cache : Cache) (message : Message) :
    M (Option CompactReplayHint.HBytes) := do
  let auth ← privateMac cache.region
  if auth ≠ cache.tag then return none
  let rho ← privateNonce message
  let some (counter, output) ← digestSearch rho message 0 digestAttemptLimit | pure none
  let index := digestIndex output
  let prepared ← prepare index
  let forest ← signForest index output
  let some selected ← select index prepared forest.2 (2^25) 4 0 | pure none
  let some tag := ReplayHintPacket.encodeHint (replayPair selected) | pure none
  let top ← SigGolfCandidate.T3.signTop cache (route index 0).1 (selected.getD 0 (0,[],0)).2.1
  let lower := ([1,2,3] : List Layer).map fun lay =>
    piece (prepared.getD (lay.val-1) ([],[])) lay index
      (selected.getD lay.val (0,[],0)).2.1
  let sig := assembledSignature rho forest.1 (top :: lower)
  -- digest/layer counters and top hint are intentionally replayed, not serialized.
  let _ := counter
  pure (some (CompactReplayHint.pack (sigBC sig) tag))

/-- Raw cryptographic values only: not a Lean heap/RISC-V peak-memory theorem. -/
theorem selected_table_bytes : (3 : Nat)*43*(7+1)*16 = 16512 := by decide

/-- Each old split chain costs d+(7-d)=7 for any valid digit. Retaining all
states also costs7, independent of the as-yet-unknown selected digit. -/
theorem split_chain_cost (digit : Nat) (h : digit ≤ 7) : digit+(7-digit) = 7 := by omega

/-- B4 totals, not the old 17-coefficient tree: four private pairs, 301 chain
compressions and11 leaf compressions, plus170 for the unchanged cached top
signer. No extra fixed hash is introduced here. -/
theorem unchanged_lower_fixed :
    (4+43*7+11 = (316 : Nat)) ∧
    (128*316+126 + 2*(64*316+62) + 170 = (81316 : Nat)) ∧
    (2+2+31334+81316 = (112654 : Nat)) := by decide

/-- Each search starts at zero; its counter cannot wrap under this fuel. This
is NOT a whole-machine termination bound or a search-success theorem. -/
theorem search_window : (2 : Nat)^25 < 2^32 := by decide

end ClaudeWCT.WCT9.Research.RetainedAncestor

/-!
Iteration38 research-only deterministic bridge. All theorem terms below require
hosted Lean compilation. A fixed answer function is NOT an adaptive freshness law.
No production entry point, claim, image, or signing policy is changed.
-/
namespace ClaudeWCT.WCT9.Research.RetainedAncestor
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Legacy SigGolfCandidate.T3.Correctness

/-- B4 starts every leaf at an even ordinal. Incoming carry therefore needs no
cross-leaf invariant; the first coefficient query overwrites it. -/
theorem carryOk_lower_start (answers : Answers) (lay : Layer) (tree leaf : Nat)
    (carry : Digest) :
    CarryOk answers (lowerSeedPair lay tree) (lowerCoefOrdinal leaf 0) carry := by
  exact carryOk_even answers _ _ carry (by
    unfold lowerCoefOrdinal lowerCoefCount
    omega)

theorem eval_lowerCoefs_any_carry (answers : Answers) (lay : Layer)
    (tree leaf : Nat) (carry : Digest) :
    evalWithAnswerFn answers (lowerCoefs lay tree leaf carry) =
      (List.ofFn (lowerCoef answers lay tree leaf), leafCarryOut answers lay tree leaf) :=
  eval_lowerCoefs answers lay tree leaf carry (carryOk_lower_start answers lay tree leaf carry)

/-- Specification keeps actual chainTable evaluations, rather than replacing
position-dependent halves by a legacy chain. -/
def honestRows (answers : Answers) (lay : Layer) (tree leaf : Nat) : Rows :=
  (List.range (chainCount lay)).map fun i =>
    evalWithAnswerFn answers (chainTable lay tree leaf i 0 (maxDigit lay i)
      (wotsSeed answers lay tree leaf i))

theorem honestRows_length (answers : Answers) (lay : Layer) (tree leaf : Nat) :
    (honestRows answers lay tree leaf).length = chainCount lay := by
  simp [honestRows]

theorem honestRows_at (answers : Answers) (lay : Layer) (tree leaf i j : Nat)
    (hi : i < chainCount lay) (hj : j ≤ maxDigit lay i) :
    ((honestRows answers lay tree leaf).getD i []).getD j 0 =
      evalWithAnswerFn answers (chainW lay tree leaf i 0 j (wotsSeed answers lay tree leaf i)) := by
  have hrow : (honestRows answers lay tree leaf).getD i [] =
      evalWithAnswerFn answers (chainTable lay tree leaf i 0 (maxDigit lay i)
        (wotsSeed answers lay tree leaf i)) := by
    simp [honestRows, List.getD_eq_getElem, hi]
  rw [hrow]
  exact eval_chainTable_at answers lay tree leaf i (maxDigit lay i) 0 _ j hj

def tableRows (lay : Layer) (tree leaf : Nat) (coefs : List Digest) : M Rows :=
  (List.range (chainCount lay)).foldlM (fun (rows : Rows) i => do
    let row ← chainTable lay tree leaf i 0 (maxDigit lay i) (lowerFamilySeed coefs i)
    pure (rows ++ [row])) []

theorem prepareLeaf_factor (lay : Layer) (tree leaf : Nat) (carry : Digest) :
    prepareLeaf lay tree leaf carry = (do
      let coefs ← lowerCoefs lay tree leaf carry
      let rows ← tableRows lay tree leaf coefs.1
      let ends := (List.range (chainCount lay)).map fun i =>
        (rows.getD i []).getD (maxDigit lay i) 0
      let root ← lowerLeafHash lay tree leaf ends
      pure ((root, rows), coefs.2)) := by
  rfl

/-- Lower-layer hypothesis is essential: top seeds use 24 coefficients, not8. -/
theorem eval_tableRows (answers : Answers) {lay : Layer} (hlay : lay ≠ 0)
    (tree leaf : Nat) :
    evalWithAnswerFn answers (tableRows lay tree leaf (List.ofFn (lowerCoef answers lay tree leaf))) =
      honestRows answers lay tree leaf := by
  unfold tableRows honestRows
  refine eval_foldlM_range_inv answers (chainCount lay) _
    (fun n rows => rows = (List.range n).map fun i =>
      evalWithAnswerFn answers (chainTable lay tree leaf i 0 (maxDigit lay i)
        (wotsSeed answers lay tree leaf i))) [] rfl ?_
  intro i _ rows hrows
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure,
    lowerFamilySeed_eq answers hlay, hrows]
  rw [List.range_succ, List.map_append, List.map_singleton]

/-- Actual selected-leaf root, table, AND outgoing carry. No assumption about
incoming carry remains. This is stronger than the old cost/row-count bound. -/
theorem eval_prepareLeaf_result (answers : Answers) {lay : Layer} (hlay : lay ≠ 0)
    (tree leaf : Nat) (carry : Digest) :
    evalWithAnswerFn answers (prepareLeaf lay tree leaf carry) =
      ((wotsRoot answers lay tree leaf, honestRows answers lay tree leaf),
        leafCarryOut answers lay tree leaf) := by
  rw [prepareLeaf_factor, evalWithAnswerFn_bind,
    eval_lowerCoefs_any_carry answers lay tree leaf carry]
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rw [eval_tableRows answers hlay tree leaf]
  have he : (List.range (chainCount lay)).map
      (fun i => ((honestRows answers lay tree leaf).getD i []).getD (maxDigit lay i) 0) =
      (List.range (chainCount lay)).map (wotsEnd answers lay tree leaf) := by
    apply List.map_congr_left
    intro i hi
    exact honestRows_at answers lay tree leaf i (maxDigit lay i) (List.mem_range.mp hi) le_rfl
  rw [he]
  rfl

/-- A definitially identical factor of prepareTree's leaf-loop body. -/
def prepareStep (lay : Layer) (tree selected : Nat)
    (state : List Digest × Rows × Digest) (leaf : Nat) : M (List Digest × Rows × Digest) := do
  if leaf = selected then
    let result ← prepareLeaf lay tree leaf state.2.2
    pure (state.1 ++ [result.1.1], result.1.2, result.2)
  else
    let result ← buildLeafPF lay tree leaf [] state.2.2
    pure (state.1 ++ [result.1.1], state.2.1, result.2)

theorem eval_prepareStep (answers : Answers) {lay : Layer} (hlay : lay ≠ 0)
    (tree selected leaf : Nat) (state : List Digest × Rows × Digest) :
    evalWithAnswerFn answers (prepareStep lay tree selected state leaf) =
      (state.1 ++ [wotsRoot answers lay tree leaf],
        (if leaf = selected then honestRows answers lay tree leaf else state.2.1),
        leafCarryOut answers lay tree leaf) := by
  unfold prepareStep
  by_cases hs : leaf = selected
  · simp only [if_pos hs, evalWithAnswerFn_bind,
      eval_prepareLeaf_result answers hlay tree leaf state.2.2, evalWithAnswerFn_pure]
  · simp only [if_neg hs, evalWithAnswerFn_bind,
      buildLeafPF_result answers hlay tree leaf [] (SigGolfCandidate.T3.Cost.validDigits_nil lay) state.2.2
        (carryOk_lower_start answers lay tree leaf state.2.2), evalWithAnswerFn_pure]

def prepareTreeRows (lay : Layer) (tree selected : Nat) : M (List Digest × Rows × Digest) :=
  (List.range (2^height lay)).foldlM (prepareStep lay tree selected) ([], [], 0)

theorem prepareTree_factor (lay : Layer) (tree selected : Nat) :
    prepareTree lay tree selected = (do
      let state ← prepareTreeRows lay tree selected
      let levels ← buildLevelsBelow 3 lay.val tree (height lay) state.1
      pure (levels, state.2.1)) := by
  rfl

/-- No carry clause is needed: both branches work for arbitrary incoming carry.
The selected branch's semantic table must nevertheless be preserved exactly. -/
def PreparedRows (answers : Answers) (lay : Layer) (tree selected done : Nat)
    (state : List Digest × Rows × Digest) : Prop :=
  state.1 = (List.range done).map (wotsRoot answers lay tree) ∧
    state.2.1 = if selected < done then honestRows answers lay tree selected else []

theorem eval_prepareTreeRows (answers : Answers) {lay : Layer} (hlay : lay ≠ 0)
    (tree selected : Nat) :
    PreparedRows answers lay tree selected (2^height lay)
      (evalWithAnswerFn answers (prepareTreeRows lay tree selected)) := by
  unfold prepareTreeRows
  refine eval_foldlM_range_inv answers (2^height lay) _
    (PreparedRows answers lay tree selected) ([], [], 0) (by simp [PreparedRows]) ?_
  intro done _ state hstate
  rcases hstate with ⟨hroots, hret⟩
  rw [eval_prepareStep answers hlay tree selected done state]
  refine ⟨?_, ?_⟩
  · rw [hroots, List.range_succ, List.map_append, List.map_singleton]
  · by_cases hs : done = selected
    · subst selected
      simp only [if_pos rfl, if_pos (show done < done+1 by omega)]
    · have hiff : selected < done+1 ↔ selected < done := by omega
      simp only [if_neg hs, hret, hiff]

/-- Whole prepared-tree semantics, including the selected retained table. The
selected-in-range and lower-layer hypotheses cannot be dropped. -/
theorem eval_prepareTree_result (answers : Answers) {lay : Layer} (hlay : lay ≠ 0)
    (tree selected : Nat) (hsel : selected < 2^height lay) :
    evalWithAnswerFn answers (prepareTree lay tree selected) =
      ((wotsTree answers lay tree).take (height lay), honestRows answers lay tree selected) := by
  let state := evalWithAnswerFn answers (prepareTreeRows lay tree selected)
  have hr : PreparedRows answers lay tree selected (2^height lay) state :=
    eval_prepareTreeRows answers hlay tree selected
  rcases hr with ⟨hroots, hret⟩
  rw [if_pos hsel] at hret
  rw [prepareTree_factor, evalWithAnswerFn_bind]
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  change (evalWithAnswerFn answers (buildLevelsBelow 3 lay.val tree (height lay) state.1),
    state.2.1) = _
  rw [hroots, hret, eval_buildLevelsBelow answers 3 lay.val tree (height lay) _ (by simp)
    (by fin_cases lay <;> decide)]
  rfl

/-- Retained lookup equals each honest prefix only for valid digits. In
particular digit8 on a seven-step lower chain would default to0, not rehash. -/
theorem values_honest (answers : Answers) (lay : Layer) (tree leaf : Nat)
    (levels : List (List Digest)) (digits : List Nat) (hvalid : SigGolfCandidate.T3.Cost.ValidDigits lay digits) :
    values (levels, honestRows answers lay tree leaf) digits =
      (List.range (chainCount lay)).map (wotsValue answers lay tree leaf digits) := by
  unfold values
  rw [honestRows_length]
  apply List.map_congr_left
  intro i hi
  exact honestRows_at answers lay tree leaf i (digits.getD i 0) (List.mem_range.mp hi)
    (hvalid i (List.mem_range.mp hi))

/-- Concrete lookup/path output equals the existing honest-piece specification;
prepared levels may omit the root, but never an authentication-path level. -/
theorem piece_honest (answers : Answers) {lay : Layer} (hlay : lay ≠ 0)
    (index : Nat) (digits : List Nat) (hvalid : SigGolfCandidate.T3.Cost.ValidDigits lay digits) :
    piece (evalWithAnswerFn answers (prepareTree lay (route index lay).2 (route index lay).1))
      lay index digits =
      wotsPieces answers lay (route index lay).2 (route index lay).1 digits := by
  rw [eval_prepareTree_result answers hlay _ _ (route_leaf_bound index lay)]
  unfold piece wotsPieces
  refine Prod.ext (values_honest answers lay _ _ _ digits hvalid) ?_
  simpa only [treeValue] using
    (map_range_take_path (wotsTree answers lay (route index lay).2) (height lay)
      (fun j => (route index lay).1 / 2^j ^^^ 1))

/-- A layer assembled from an actual prepared piece recovers the *same prepared
root pair* used by the ancestor-first signer. This closes one deterministic
per-layer replay edge, not the whole compact signer/expander composition. -/
theorem eval_recoverLayerPair_prepared (answers : Answers) (sig : Signature)
    {lay : Layer} (hlay : lay ≠ 0) (index : Nat) (digits : List Nat)
    (hvalid : SigGolfCandidate.T3.Cost.ValidDigits lay digits)
    (hlayer : sig.layers lay = piecesSignature lay
      (piece (evalWithAnswerFn answers (prepareTree lay (route index lay).2 (route index lay).1))
        lay index digits)) :
    evalWithAnswerFn answers (recoverLayerPair sig index lay digits) =
      topPair lay (evalWithAnswerFn answers
        (prepareTree lay (route index lay).2 (route index lay).1)).1 := by
  rw [piece_honest answers hlay index digits hvalid] at hlayer
  rw [eval_prepareTree_result answers hlay _ _ (route_leaf_bound index lay), topPair_take]
  apply eval_recoverLayerPair_honest answers sig index lay digits hvalid
  · intro i
    rw [hlayer]
    simp [piecesSignature, wotsPieces, List.getD_eq_getElem, i.isLt]
  · intro j
    rw [hlayer]
    simp [piecesSignature, wotsPieces, List.getD_eq_getElem, j.isLt]

end ClaudeWCT.WCT9.Research.RetainedAncestor

/-!
Iteration39 research-only: deterministic four-stage replay composition.
These theorem candidates are NOT locally elaborated. In particular they do not
establish fresh adaptive oracle laws, the selected-search hypotheses from sign,
or compact completion/security/machine links. Searches are compared separately
under a fixed total answer function; no equality of reordered transcripts is
asserted. The projected sibling can change the last root but not replay data.
-/
namespace ClaudeWCT.WCT9.Research.ReplayComposition
open OracleComp OracleSpec SigGolfCandidate.T3
open ClaudeWCT.W9.T3M

abbrev Selected := RetainedAncestor.Selected

/-- Each selected score is already clipped; clipping again in select/replayPair
is redundant. This is purely arithmetic, not a search-success statement. -/
theorem score_le_cap (lay : Layer) (digits : List Nat) :
    ReplayHintExpand.score lay digits ≤ ReplayHintPacket.cap lay.val := by
  unfold ReplayHintExpand.score ReplayHintPacket.cap
  by_cases h : lay = 0
  · subst lay
    change min 60 (PooledCredit.effectiveCredit 0 digits) ≤ 60
    exact Nat.min_le_left _ _
  · have hv : lay.val ≠ 0 := fun hv => h (Fin.ext hv)
    simp only [if_neg h, if_neg hv]
    exact Nat.min_le_left _ _

/-- The public byte restores precisely the four ancestor-selected floors on all
valid clipped prefixes. Not a probability/cardinality proof. Includes the
terminal floor, whose dependency on all three earlier scores is easy to miss. -/
theorem replay_floors_agree :
    ∀ s0 ∈ Finset.Icc 22 60, ∀ s1 ∈ Finset.Icc 8 30,
    let c1 := ReplayHintPacket.nextCredit 0 s0
    let c2 := ReplayHintPacket.nextCredit c1 s1
    ∀ s2 ∈ Finset.Icc (ReplayHintPacket.policy 2 c2) 30,
    let c3 := ReplayHintPacket.nextCredit c2 s2
    let pair := (ReplayHintPacket.policy 2 c2, 67-c3)
    ReplayHintExpand.replayFloor pair 0 = ReplayHintPacket.policy 0 0 ∧
    ReplayHintExpand.replayFloor pair 1 = ReplayHintPacket.policy 1 c1 ∧
    ReplayHintExpand.replayFloor pair 2 = ReplayHintPacket.policy 2 c2 ∧
    ReplayHintExpand.replayFloor pair 3 = ReplayHintPacket.policy 3 c3 := by
  decide +kernel

/-- For four selected words the signer and expander use the very same canonical
pair, including the nested min67 saturation. This does not assert existence or
uniqueness of a completed signature. -/
theorem canonical_pair_four (f0 f1 f2 f3 : Selected) :
    RetainedAncestor.replayPair [f0,f1,f2,f3] =
      ReplayHintExpand.replayPair
        [ReplayHintExpand.score 0 f0.2.1, ReplayHintExpand.score 1 f1.2.1,
         ReplayHintExpand.score 2 f2.2.1, ReplayHintExpand.score 3 f3.2.1] := by
  have h0 : ReplayHintExpand.score 0 f0.2.1 ≤ 60 := score_le_cap 0 f0.2.1
  have h1 : ReplayHintExpand.score 1 f1.2.1 ≤ 30 := score_le_cap 1 f1.2.1
  have h2 : ReplayHintExpand.score 2 f2.2.1 ≤ 30 := score_le_cap 2 f2.2.1
  simp [RetainedAncestor.replayPair, ReplayHintExpand.replayPair,
    Nat.min_eq_right h0, Nat.min_eq_right h1, Nat.min_eq_right h2]

/-- Four search replays plus the three prepared-tree recovery edges compose
into one complete layer replay. All search and recovery premises are explicit;
in particular this is NOT a theorem that sign implies those premises.
The output counters/credits are in layer order, although evaluation is3,2,1,0.
No condition on the final root is required to compose the replay. -/
theorem eval_layers_four (answers : Answers) (sig : Signature) (index : Nat)
    (pair : Nat × Nat) (p0 p1 p2 p3 : Digest × Digest)
    (f0 f1 f2 f3 : Selected) (v : Digest)
    (hs0 : evalWithAnswerFn answers (DeficitProducer.counterSearch 0
      (ReplayHintExpand.replayFloor pair 0) (route index 0).2 (route index 0).1
      (.pair p0.1 p0.2) 0 (2^25)) = some f0)
    (hs1 : evalWithAnswerFn answers (DeficitProducer.counterSearch 1
      (ReplayHintExpand.replayFloor pair 1) (route index 1).2 (route index 1).1
      (.pair p1.1 p1.2) 0 (2^25)) = some f1)
    (hs2 : evalWithAnswerFn answers (DeficitProducer.counterSearch 2
      (ReplayHintExpand.replayFloor pair 2) (route index 2).2 (route index 2).1
      (.pair p2.1 p2.2) 0 (2^25)) = some f2)
    (hs3 : evalWithAnswerFn answers (DeficitProducer.counterSearch 3
      (ReplayHintExpand.replayFloor pair 3) (route index 3).2 (route index 3).1
      (.pair p3.1 p3.2) 0 (2^25)) = some f3)
    (hr1 : evalWithAnswerFn answers (recoverLayerPair sig index 1 f1.2.1) = p0)
    (hr2 : evalWithAnswerFn answers (recoverLayerPair sig index 2 f2.2.1) = p1)
    (hr3 : evalWithAnswerFn answers (recoverLayerPair sig index 3 f3.2.1) = p2)
    (ht : evalWithAnswerFn answers (topFold sig index f0.2.1) = v) :
    evalWithAnswerFn answers (CompactReplayHint.layers sig index pair 4 (.pair p3.1 p3.2)) =
      some (v, evalWithAnswerFn answers (topNode index v (topSib sig)),
        [f0.1, f1.1, f2.1, f3.1], f0.2.2,
        [ReplayHintExpand.score 0 f0.2.1, ReplayHintExpand.score 1 f1.2.1,
         ReplayHintExpand.score 2 f2.2.1, ReplayHintExpand.score 3 f3.2.1]) := by
  rcases f0 with ⟨c0, d0, h0⟩
  rcases f1 with ⟨c1, d1, h1⟩
  rcases f2 with ⟨c2, d2, h2⟩
  rcases f3 with ⟨c3, d3, h3⟩
  simp [CompactReplayHint.layers, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
    hs0, hs1, hs2, hs3, hr1, hr2, hr3, ht]

/-- Compact encoding preserves every lower recovery edge. This uses the actual
codec inverse/projection theorem, rather than pretending omitted bits survive
serialization. The nonzero-layer premise is essential. -/
theorem recoverPair_compact (sig : Signature) (index : Nat) (lay : Layer)
    (digits : List Nat) (hlay : lay ≠ 0) :
    recoverLayerPair (sigDecC (sigBC sig)) index lay digits =
      recoverLayerPair sig index lay digits := by
  rw [sigDecC_sigBC]
  exact recoverLayerPair_fill sig index lay digits 0 hlay

/-- Likewise the shared top level11 node is not affected by serialization.
The final topNode root generally IS affected and must still be completed. -/
theorem topFold_compact (sig : Signature) (index : Nat) (digits : List Nat) :
    topFold (sigDecC (sigBC sig)) index digits = topFold sig index digits := by
  rw [sigDecC_sigBC, topFold_proj]

/-- The decoded sibling is already projected. Thus completion0 is exactly
its uncompleted final-root attempt, not a different candidate. -/
theorem decoded_sibling_zero (payload : CBytes) :
    setTop (topSib (sigDecC payload)) 0 = topSib (sigDecC payload) := by
  have h := topSib_proj (sigDecC payload)
  rw [proj_sigDecC] at h
  exact h.symm

/-- Conditional completeness of the actual 5311-byte expander, including the
canonical hint check and the retained-node completion search. Search replay,
root consistency, and existence of an honest completion are explicit premises.
No assumption that the original omitted bits are the FIRST matching completion
is made; that would require a false uniqueness shortcut in a general oracle.
-/
theorem eval_expand_complete (answers : Answers) (message : Message) (pk : Digest)
    (bytes : CompactReplayHint.HBytes) (pair : Nat × Nat)
    (counter : BitVec 32) (output : HashOutput) (v root : Digest)
    (counters : List (BitVec 32)) (topHint : BitVec 64) (credits : List Nat)
    (completion : Nat)
    (htag : ReplayHintPacket.decodeHint (CompactReplayHint.tag bytes) = some pair)
    (hdigest : evalWithAnswerFn answers (digestSearch
      (sigDecC (CompactReplayHint.payload bytes)).rho message 0 digestAttemptLimit) =
        some (counter, output))
    (hlayers : evalWithAnswerFn answers (CompactReplayHint.layers
      (sigDecC (CompactReplayHint.payload bytes)) (digestIndex output) pair 4
      (.pair
        (evalWithAnswerFn answers (recoverFts (sigDecC (CompactReplayHint.payload bytes))
          (digestIndex output) output)).1
        (evalWithAnswerFn answers (recoverFts (sigDecC (CompactReplayHint.payload bytes))
          (digestIndex output) output)).2)) =
        some (v, root, counters, topHint, credits))
    (hcanonical : ReplayHintExpand.replayPair credits = pair)
    (hroot : root = evalWithAnswerFn answers (topNode (digestIndex output) v
      (topSib (sigDecC (CompactReplayHint.payload bytes)))))
    (hcompletion : completion < 2^16)
    (hmatch : evalWithAnswerFn answers (topNode (digestIndex output) v
      (setTop (topSib (sigDecC (CompactReplayHint.payload bytes))) completion)) = pk) :
    ∃ witness, evalWithAnswerFn answers (CompactReplayHint.expand message pk bytes) =
      some witness := by
  unfold CompactReplayHint.expand
  simp only [evalWithAnswerFn_bind, htag, hdigest, hlayers]
  simp only [hcanonical, ne_eq, not_true_eq_false, if_false]
  by_cases hpk : root = pk
  · simp [hpk, evalWithAnswerFn_pure]
  · have hc0 : completion ≠ 0 := by
      intro hz
      rw [hz, decoded_sibling_zero] at hmatch
      exact hpk (hroot.trans hmatch)
    obtain ⟨c, hc⟩ := searchTop_complete answers (digestIndex output) v
      (topSib (sigDecC (CompactReplayHint.payload bytes))) pk searchFuel 1 completion
      (by omega) (by unfold searchFuel; omega) hmatch
    simp [hpk, evalWithAnswerFn_bind, hc, evalWithAnswerFn_pure]

end ClaudeWCT.WCT9.Research.ReplayComposition

/-!
Iteration40 research-only: extract replay premises from successful *actual*
RetainedAncestor.select evaluation. These are theorem candidates, not locally
elaborated. Fixed-answer determinism is not adaptive freshness or a resource law.
-/
namespace ClaudeWCT.WCT9.Research.SelectorTrace
open OracleComp OracleSpec SigGolfCandidate.T3

abbrev Selected := RetainedAncestor.Selected

/-- Exactly select's message, including its prepared-list index (not stage+1). -/
def messageAt (index : Nat) (prepared : List RetainedAncestor.Prepared)
    (forest : Digest × Digest) (stage : Nat) : LayerMsg :=
  if stage = 3 then .pair forest.1 forest.2 else
    let child : Layer := Fin.ofNat 4 (stage+1)
    let pair := topPair child (prepared.getD stage ([],[])).1
    .pair pair.1 pair.2

def nextAt (stage credit : Nat) (found : Selected) : Nat :=
  ReplayHintPacket.nextCredit credit
    (min (ReplayHintPacket.cap stage)
      (ReplayHintExpand.score (Fin.ofNat 4 stage) found.2.1))

def searchAt (index : Nat) (prepared : List RetainedAncestor.Prepared)
    (forest : Digest × Digest) (fuel stage credit : Nat) : M (Option Selected) :=
  let lay : Layer := Fin.ofNat 4 stage
  DeficitProducer.counterSearch lay (ReplayHintPacket.policy stage credit)
    (route index lay).2 (route index lay).1 (messageAt index prepared forest stage) 0 fuel

/-- Success yields a genuinely accepted answer, even after rejected probes.
No counter uniqueness, distribution, or equality of whole transcripts is used. -/
theorem search_accepted (answers : Answers) (lay : Layer)
    (floor tree leaf : Nat) (msg : LayerMsg) :
    ∀ fuel counter found,
      evalWithAnswerFn answers
        (DeficitProducer.counterSearch lay floor tree leaf msg counter fuel) = some found →
      ∃ answer, DeficitProducer.decodeWithFloor lay floor answer = some found.2.1 := by
  intro fuel
  induction fuel with
  | zero =>
      intro counter found h
      simp [DeficitProducer.counterSearch, evalWithAnswerFn_pure] at h
  | succ fuel ih =>
      intro counter found h
      simp only [DeficitProducer.counterSearch, evalWithAnswerFn_bind] at h
      cases hd : DeficitProducer.decodeWithFloor lay floor
          (encodingAnswer lay (evalWithAnswerFn answers
            (publicHash (layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 counter))))) with
      | none =>
          simp only [hd] at h
          exact ih (counter+1) found h
      | some digits =>
          simp only [hd, evalWithAnswerFn_pure, Option.some.injEq] at h
          subst found
          exact ⟨_, hd⟩

/-- Both digit validity and the *unclipped* effective-credit floor follow from
search success; the clipped floor additionally needs floor ≤ the stage cap. -/
theorem search_guards (answers : Answers) (lay : Layer)
    (floor tree leaf : Nat) (msg : LayerMsg) (fuel counter : Nat) (found : Selected)
    (h : evalWithAnswerFn answers
      (DeficitProducer.counterSearch lay floor tree leaf msg counter fuel) = some found) :
    SigGolfCandidate.T3.Cost.ValidDigits lay found.2.1 ∧
      floor ≤ PooledCredit.effectiveCredit lay found.2.1 := by
  obtain ⟨answer, ha⟩ := search_accepted answers lay floor tree leaf msg fuel counter found h
  exact ⟨SigGolfCandidate.T3.Cost.validDigits_decode (DeficitProducer.sound ha),
    DeficitProducer.accepted_credit ha⟩

/-- One actual selector step, with no search-success assumptions supplied by the
caller. Failure of either search or suffix cannot be hidden by list defaults. -/
theorem eval_select_cons (answers : Answers) (index : Nat)
    (prepared : List RetainedAncestor.Prepared) (forest : Digest × Digest)
    (fuel n credit : Nat) (selected : List Selected)
    (h : evalWithAnswerFn answers
      (RetainedAncestor.select index prepared forest fuel (n+1) credit) = some selected) :
    ∃ found rest, selected = found :: rest ∧
      evalWithAnswerFn answers (searchAt index prepared forest fuel (4-(n+1)) credit) = some found ∧
      evalWithAnswerFn answers (RetainedAncestor.select index prepared forest fuel n
        (nextAt (4-(n+1)) credit found)) = some rest := by
  change (evalWithAnswerFn answers (do
    let some found ← searchAt index prepared forest fuel (4-(n+1)) credit | pure none
    let some rest ← RetainedAncestor.select index prepared forest fuel n
      (nextAt (4-(n+1)) credit found) | pure none
    pure (some (found :: rest)))) = some selected at h
  simp only [evalWithAnswerFn_bind] at h
  cases hs : evalWithAnswerFn answers (searchAt index prepared forest fuel (4-(n+1)) credit) with
  | none => simp [hs, evalWithAnswerFn_pure] at h
  | some found =>
      simp only [hs, evalWithAnswerFn_bind] at h
      cases ht : evalWithAnswerFn answers (RetainedAncestor.select index prepared forest fuel n
          (nextAt (4-(n+1)) credit found)) with
      | none => simp [ht, evalWithAnswerFn_pure] at h
      | some rest =>
          simp only [ht, evalWithAnswerFn_pure, Option.some.injEq] at h
          exact ⟨found, rest, h.symm, hs, ht⟩

/-- A successful actual selector has exactly n words, even for nonstandard n.
This theorem does not legitimize stage wrapping for n>4. -/
theorem selected_length (answers : Answers) (index : Nat)
    (prepared : List RetainedAncestor.Prepared) (forest : Digest × Digest) (fuel : Nat) :
    ∀ n credit selected, evalWithAnswerFn answers
      (RetainedAncestor.select index prepared forest fuel n credit) = some selected →
      selected.length = n := by
  intro n
  induction n with
  | zero =>
      intro credit selected h
      have he : ([] : List Selected) = selected := by
        simpa [RetainedAncestor.select, evalWithAnswerFn_pure] using h
      subst selected
      rfl
  | succ n ih =>
      intro credit selected h
      obtain ⟨found, rest, rfl, _, ht⟩ :=
        eval_select_cons answers index prepared forest fuel n credit selected h
      simpa using congrArg Nat.succ (ih _ rest ht)

/-- Replay certificate indexed by the *actual* remaining-step count and credit.
It records successful searches, valid digits and accepted raw floors recursively.
It is evidence extracted from select, not a replacement signer. -/
def Trace (answers : Answers) (index : Nat) (prepared : List RetainedAncestor.Prepared)
    (forest : Digest × Digest) (fuel : Nat) : Nat → Nat → List Selected → Prop
  | 0, _, selected => selected = []
  | n+1, credit, selected =>
      ∃ found rest, selected = found :: rest ∧
        evalWithAnswerFn answers (searchAt index prepared forest fuel (4-(n+1)) credit) = some found ∧
        SigGolfCandidate.T3.Cost.ValidDigits (Fin.ofNat 4 (4-(n+1))) found.2.1 ∧
        ReplayHintPacket.policy (4-(n+1)) credit ≤
          PooledCredit.effectiveCredit (Fin.ofNat 4 (4-(n+1))) found.2.1 ∧
        Trace answers index prepared forest fuel n (nextAt (4-(n+1)) credit found) rest

theorem eval_select_trace (answers : Answers) (index : Nat)
    (prepared : List RetainedAncestor.Prepared) (forest : Digest × Digest) (fuel : Nat) :
    ∀ n credit selected, evalWithAnswerFn answers
      (RetainedAncestor.select index prepared forest fuel n credit) = some selected →
      Trace answers index prepared forest fuel n credit selected := by
  intro n
  induction n with
  | zero =>
      intro credit selected h
      have he : ([] : List Selected) = selected := by
        simpa [RetainedAncestor.select, evalWithAnswerFn_pure] using h
      exact he.symm
  | succ n ih =>
      intro credit selected h
      obtain ⟨found, rest, he, hs, ht⟩ :=
        eval_select_cons answers index prepared forest fuel n credit selected h
      have hg := search_guards answers (Fin.ofNat 4 (4-(n+1)))
        (ReplayHintPacket.policy (4-(n+1)) credit)
        (route index (Fin.ofNat 4 (4-(n+1)))).2
        (route index (Fin.ofNat 4 (4-(n+1)))).1
        (messageAt index prepared forest (4-(n+1))) fuel 0 found hs
      exact ⟨found, rest, he, hs, hg.1, hg.2, ih _ rest ht⟩

/-- The finite part of clipped-floor reasoning, kept separate from the actual
search proof above. In particular a clipped score cannot be claimed ≥floor
without the second premise. -/
theorem score_floor (lay : Layer) (floor : Nat) (digits : List Nat)
    (he : floor ≤ PooledCredit.effectiveCredit lay digits)
    (hc : floor ≤ ReplayHintPacket.cap lay.val) :
    floor ≤ ReplayHintExpand.score lay digits := by
  have hcap : ReplayHintPacket.cap lay.val = (if lay = 0 then 60 else 30) := by
    unfold ReplayHintPacket.cap
    by_cases h : lay = 0
    · subst lay; rfl
    · have hv : lay.val ≠ 0 := fun hv => h (Fin.ext hv)
      simp [h, hv]
  unfold ReplayHintExpand.score
  rw [hcap] at hc
  exact le_min hc he

end ClaudeWCT.WCT9.Research.SelectorTrace

namespace ClaudeWCT.WCT9.Research.SelectorTrace
open OracleComp OracleSpec SigGolfCandidate.T3

/-- The extra min in the executable selector is redundant on its four stages.
The finite-layer premise prevents mistaking Nat subtraction/wrap for routing. -/
theorem nextAt_eq (lay : Layer) (credit : Nat) (found : Selected) :
    nextAt lay.val credit found = ReplayHintPacket.nextCredit credit
      (ReplayHintExpand.score lay found.2.1) := by
  have hf : (Fin.ofNat 4 lay.val : Layer) = lay := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt lay.isLt
  unfold nextAt
  rw [hf, Nat.min_eq_right (ReplayComposition.score_le_cap lay found.2.1)]

/-- Finite policy facts needed BEFORE clipping a successful raw search credit.
A successful search alone would not justify this clipping step. -/
theorem prefix_caps : ∀ s0 ∈ Finset.Icc 22 60,
    let c1 := ReplayHintPacket.nextCredit 0 s0
    ReplayHintPacket.policy 1 c1 = 8 ∧
      ∀ s1 ∈ Finset.Icc 8 30,
        ReplayHintPacket.policy 2 (ReplayHintPacket.nextCredit c1 s1) ≤ 30 := by
  decide +kernel

def ReplaySearchAt (answers : Answers) (index : Nat)
    (prepared : List RetainedAncestor.Prepared) (forest : Digest × Digest)
    (fuel : Nat) (pair : Nat × Nat) (lay : Layer) (found : Selected) : Prop :=
  evalWithAnswerFn answers (DeficitProducer.counterSearch lay
    (ReplayHintExpand.replayFloor pair lay) (route index lay).2 (route index lay).1
    (messageAt index prepared forest lay.val) 0 fuel) = some found

/-- Actual successful select now supplies all four replay-search equations,
valid digits, an encodable canonical pair and the three clipped prefix ranges.
This has ONE success premise, not four assumed search replays. It does not yet
assemble/recover signature layers or assert adaptive oracle/resource laws. -/
theorem eval_select_replay_searches (answers : Answers) (index : Nat)
    (prepared : List RetainedAncestor.Prepared) (forest : Digest × Digest)
    (fuel : Nat) (selected : List Selected)
    (h : evalWithAnswerFn answers
      (RetainedAncestor.select index prepared forest fuel 4 0) = some selected) :
    ∃ f0 f1 f2 f3 : Selected,
      selected = [f0,f1,f2,f3] ∧
      RetainedAncestor.replayPair selected ∈ ReplayHintPacket.hintPairs ∧
      ReplaySearchAt answers index prepared forest fuel (RetainedAncestor.replayPair selected) 0 f0 ∧
      ReplaySearchAt answers index prepared forest fuel (RetainedAncestor.replayPair selected) 1 f1 ∧
      ReplaySearchAt answers index prepared forest fuel (RetainedAncestor.replayPair selected) 2 f2 ∧
      ReplaySearchAt answers index prepared forest fuel (RetainedAncestor.replayPair selected) 3 f3 ∧
      SigGolfCandidate.T3.Cost.ValidDigits 0 f0.2.1 ∧
      SigGolfCandidate.T3.Cost.ValidDigits 1 f1.2.1 ∧
      SigGolfCandidate.T3.Cost.ValidDigits 2 f2.2.1 ∧
      SigGolfCandidate.T3.Cost.ValidDigits 3 f3.2.1 := by
  have ht := eval_select_trace answers index prepared forest fuel 4 0 selected h
  rcases ht with ⟨f0, r0, he0, hs0, hv0, hg0, ht⟩
  rcases ht with ⟨f1, r1, he1, hs1, hv1, hg1, ht⟩
  rcases ht with ⟨f2, r2, he2, hs2, hv2, hg2, ht⟩
  rcases ht with ⟨f3, r3, he3, hs3, hv3, hg3, ht⟩
  change r3 = [] at ht
  have he : selected = [f0,f1,f2,f3] := by rw [he0, he1, he2, he3, ht]
  simp only [nextAt_eq (0 : Layer), nextAt_eq (1 : Layer), nextAt_eq (2 : Layer)]
    at hs1 hg1 hs2 hg2 hs3 hg3
  let s0 := ReplayHintExpand.score 0 f0.2.1
  let s1 := ReplayHintExpand.score 1 f1.2.1
  let s2 := ReplayHintExpand.score 2 f2.2.1
  let c1 := ReplayHintPacket.nextCredit 0 s0
  let c2 := ReplayHintPacket.nextCredit c1 s1
  let c3 := ReplayHintPacket.nextCredit c2 s2
  have hu0 : s0 ≤ 60 := ReplayComposition.score_le_cap 0 f0.2.1
  have hu1 : s1 ≤ 30 := ReplayComposition.score_le_cap 1 f1.2.1
  have hu2 : s2 ≤ 30 := ReplayComposition.score_le_cap 2 f2.2.1
  have hl0 : 22 ≤ s0 := score_floor 0 22 f0.2.1
    (by simpa only [show ReplayHintPacket.policy 0 0 = 22 from by decide] using hg0) (by decide)
  have hc1 : ReplayHintPacket.policy 1 c1 = 8 := (prefix_caps s0 ⟨hl0, hu0⟩).1
  have hl1 : 8 ≤ s1 := score_floor 1 8 f1.2.1
    (by simpa only [hc1] using hg1) (by decide)
  have hcap2 : ReplayHintPacket.policy 2 c2 ≤ 30 := (prefix_caps s0 ⟨hl0, hu0⟩).2 s1 ⟨hl1, hu1⟩
  have hl2 : ReplayHintPacket.policy 2 c2 ≤ s2 :=
    score_floor 2 (ReplayHintPacket.policy 2 c2) f2.2.1 hg2 hcap2
  have hc1id : c1 = s0 := by
    change min 67 (0+s0) = s0
    omega
  have hp : RetainedAncestor.replayPair selected = (ReplayHintPacket.policy 2 c2, 67-c3) := by
    rw [he, ReplayComposition.canonical_pair_four]
    change (ReplayHintPacket.policy 2 (ReplayHintPacket.nextCredit s0 s1),
      67-ReplayHintPacket.nextCredit (ReplayHintPacket.nextCredit s0 s1) s2) = _
    simp only [c2, c3, hc1id]
  have hm : RetainedAncestor.replayPair selected ∈ ReplayHintPacket.hintPairs := by
    rw [hp]
    have hm := ReplayHintPacket.reachable_pair_in_table s0 ⟨hl0, hu0⟩ s1 ⟨hl1, hu1⟩
    rw [← hc1id] at hm
    exact hm s2 ⟨hl2, hu2⟩
  obtain ⟨hf0, hf1, hf2, hf3⟩ := ReplayComposition.replay_floors_agree
    s0 ⟨hl0, hu0⟩ s1 ⟨hl1, hu1⟩ s2 ⟨hl2, hu2⟩
  refine ⟨f0, f1, f2, f3, he, hm, ?_, ?_, ?_, ?_, hv0, hv1, hv2, hv3⟩
  · simpa only [ReplaySearchAt, hp, hf0, searchAt] using hs0
  · simpa only [ReplaySearchAt, hp, hf1, searchAt] using hs1
  · simpa only [ReplaySearchAt, hp, hf2, searchAt] using hs2
  · simpa only [ReplaySearchAt, hp, hf3, searchAt] using hs3

end ClaudeWCT.WCT9.Research.SelectorTrace

namespace ClaudeWCT.WCT9.Research.SelectorTrace
open OracleComp OracleSpec SigGolfCandidate.T3

/-- Table membership entails a real byte and its inverse, not just an optional
round-trip identity. This discharges the signer's post-selection hint-failure
branch once the successful-select theorem is elaborated. -/
theorem hint_exists (pair : Nat × Nat) (hm : pair ∈ ReplayHintPacket.hintPairs) :
    ∃ tag, ReplayHintPacket.encodeHint pair = some tag ∧
      ReplayHintPacket.decodeHint tag = some pair := by
  have hr := ReplayHintPacket.pair_roundtrip pair hm
  cases ht : ReplayHintPacket.encodeHint pair with
  | none => simp [ht] at hr
  | some tag =>
      exact ⟨tag, ht, by simpa only [ht, Option.bind_some] using hr⟩

theorem eval_select_has_hint (answers : Answers) (index : Nat)
    (prepared : List RetainedAncestor.Prepared) (forest : Digest × Digest)
    (fuel : Nat) (selected : List Selected)
    (h : evalWithAnswerFn answers
      (RetainedAncestor.select index prepared forest fuel 4 0) = some selected) :
    ∃ tag, ReplayHintPacket.encodeHint (RetainedAncestor.replayPair selected) = some tag ∧
      ReplayHintPacket.decodeHint tag = some (RetainedAncestor.replayPair selected) := by
  obtain ⟨f0, f1, f2, f3, _, hm, _⟩ :=
    eval_select_replay_searches answers index prepared forest fuel selected h
  exact hint_exists _ hm

end ClaudeWCT.WCT9.Research.SelectorTrace

namespace ClaudeWCT.WCT9.Research.SelectorTrace
open OracleComp OracleSpec SigGolfCandidate.T3
open ClaudeWCT.W9.T3M

/-- Compose the actual selector with reverse replay. Only the still-missing
signature/tree recovery edges remain as hypotheses; the four replay searches,
valid digits and canonical hint membership are now extracted from select.
This is deterministic completeness under one Answers, not adaptive freshness. -/
theorem eval_layers_from_select (answers : Answers) (sig : Signature) (index : Nat)
    (prepared : List RetainedAncestor.Prepared) (forest : Digest × Digest)
    (selected : List Selected)
    (hselect : evalWithAnswerFn answers
      (RetainedAncestor.select index prepared forest (2^25) 4 0) = some selected)
    (hrecover : ∀ lay : Layer, lay ≠ 0 →
      evalWithAnswerFn answers (recoverLayerPair sig index lay
        (selected.getD lay.val (0,[],0)).2.1) =
        topPair lay (prepared.getD (lay.val-1) ([],[])).1) :
    ∃ (tag : Fin 256) (f0 f1 f2 f3 : Selected),
      selected = [f0,f1,f2,f3] ∧
      ReplayHintPacket.encodeHint (RetainedAncestor.replayPair selected) = some tag ∧
      ReplayHintPacket.decodeHint tag = some (RetainedAncestor.replayPair selected) ∧
      let v := evalWithAnswerFn answers (topFold sig index f0.2.1)
      evalWithAnswerFn answers (CompactReplayHint.layers sig index
        (RetainedAncestor.replayPair selected) 4 (.pair forest.1 forest.2)) =
      some (v, evalWithAnswerFn answers (topNode index v (topSib sig)),
        [f0.1,f1.1,f2.1,f3.1], f0.2.2,
        [ReplayHintExpand.score 0 f0.2.1, ReplayHintExpand.score 1 f1.2.1,
         ReplayHintExpand.score 2 f2.2.1, ReplayHintExpand.score 3 f3.2.1]) := by
  obtain ⟨f0, f1, f2, f3, he, hm, hs0, hs1, hs2, hs3, hv0, hv1, hv2, hv3⟩ :=
    eval_select_replay_searches answers index prepared forest (2^25) selected hselect
  obtain ⟨tag, henc, hdec⟩ := hint_exists _ hm
  refine ⟨tag, f0, f1, f2, f3, he, henc, hdec, ?_⟩
  let p0 := topPair (1 : Layer) (prepared.getD 0 ([],[])).1
  let p1 := topPair (2 : Layer) (prepared.getD 1 ([],[])).1
  let p2 := topPair (3 : Layer) (prepared.getD 2 ([],[])).1
  have hr1 : evalWithAnswerFn answers (recoverLayerPair sig index 1 f1.2.1) = p0 := by
    simpa [he] using hrecover 1 (by decide)
  have hr2 : evalWithAnswerFn answers (recoverLayerPair sig index 2 f2.2.1) = p1 := by
    simpa [he] using hrecover 2 (by decide)
  have hr3 : evalWithAnswerFn answers (recoverLayerPair sig index 3 f3.2.1) = p2 := by
    simpa [he] using hrecover 3 (by decide)
  apply ReplayComposition.eval_layers_four answers sig index
    (RetainedAncestor.replayPair selected) p0 p1 p2 forest f0 f1 f2 f3
    (evalWithAnswerFn answers (topFold sig index f0.2.1))
  · simpa only [ReplaySearchAt, messageAt] using hs0
  · simpa only [ReplaySearchAt, messageAt] using hs1
  · simpa only [ReplaySearchAt, messageAt] using hs2
  · simpa only [ReplaySearchAt, messageAt] using hs3
  · exact hr1
  · exact hr2
  · exact hr3
  · rfl

end ClaudeWCT.WCT9.Research.SelectorTrace

/-!
Iteration41 research-only: close the selected-piece and honest-top premises of
actual-selector replay, then compose successful retained signing with compact
expansion. These are proof CANDIDATES pending external elaboration, not certified
resource/security/machine links. No local Lean build is authorized.
-/
namespace ClaudeWCT.WCT9.Research.SignReplay
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness SigGolfCandidate.T3.Cost
open ClaudeWCT.W9.T3M

/-- Indexing the actual three-tree preparation, not an arbitrary prepared list.
Only layers1,2,3 have retained tables. -/
theorem prepared_at (answers : Answers) (index : Nat) (lay : Layer) (hlay : lay ≠ 0) :
    (evalWithAnswerFn answers (RetainedAncestor.prepare index)).getD
      (lay.val-1) ([],[]) =
      evalWithAnswerFn answers (RetainedAncestor.prepareTree lay
        (route index lay).2 (route index lay).1) := by
  fin_cases lay
  · exact False.elim (hlay rfl)
  all_goals simp [RetainedAncestor.prepare, eval_mapM, evalWithAnswerFn_bind, evalWithAnswerFn_pure]

/-- Expose validity independently of recovery: a caller must not assume a
recovery equation in order to learn that its selected digits are valid. -/
theorem selected_valid (answers : Answers) (index : Nat)
    (prepared : List RetainedAncestor.Prepared) (forest : Digest × Digest)
    (fuel : Nat) (selected : List RetainedAncestor.Selected)
    (hs : evalWithAnswerFn answers
      (RetainedAncestor.select index prepared forest fuel 4 0) = some selected)
    (lay : Layer) : ValidDigits lay (selected.getD lay.val (0,[],0)).2.1 := by
  obtain ⟨f0,f1,f2,f3,he,_,_,_,_,_,hv0,hv1,hv2,hv3⟩ :=
    SelectorTrace.eval_select_replay_searches answers index prepared forest fuel selected hs
  subst selected
  fin_cases lay <;> first | exact hv0 | exact hv1 | exact hv2 | exact hv3

/-- Index-aware assembly. Keeping index explicit prevents silently signing the
right retained values with authentication paths routed for another index. -/
def assembledAt (index : Nat) (rho : Digest) (forest : List Opening × (Digest × Digest))
    (prepared : List RetainedAncestor.Prepared) (selected : List RetainedAncestor.Selected)
    (top : Pieces) : Signature :=
  assembledSignature rho forest.1 (top :: ([1,2,3] : List Layer).map fun lay =>
    RetainedAncestor.piece (prepared.getD (lay.val-1) ([],[])) lay index
      (selected.getD lay.val (0,[],0)).2.1)

/-- No length premise about selected is used to project the lower pieces;
validity is supplied separately from the actual successful selector. -/
theorem assembled_lower (index : Nat) (rho : Digest)
    (forest : List Opening × (Digest × Digest))
    (prepared : List RetainedAncestor.Prepared) (selected : List RetainedAncestor.Selected)
    (top : Pieces) (lay : Layer) (hlay : lay ≠ 0) :
    (assembledAt index rho forest prepared selected top).layers lay =
      piecesSignature lay (RetainedAncestor.piece
        (prepared.getD (lay.val-1) ([],[])) lay index
        (selected.getD lay.val (0,[],0)).2.1) := by
  fin_cases lay
  · exact False.elim (hlay rfl)
  all_goals rfl

theorem assembled_top (index : Nat) (rho : Digest)
    (forest : List Opening × (Digest × Digest))
    (prepared : List RetainedAncestor.Prepared) (selected : List RetainedAncestor.Selected)
    (top : Pieces) :
    (assembledAt index rho forest prepared selected top).layers 0 =
      piecesSignature 0 top := rfl

/-- This discharges exactly the three SELECTED recovery premises from r40.
There is no universal recovery assumption at unselected digit vectors. -/
theorem selected_recovery (answers : Answers) (index : Nat) (rho : Digest)
    (forest : List Opening × (Digest × Digest))
    (selected : List RetainedAncestor.Selected) (top : Pieces)
    (hs : evalWithAnswerFn answers (RetainedAncestor.select index
      (evalWithAnswerFn answers (RetainedAncestor.prepare index)) forest.2 (2^25) 4 0) =
        some selected) (lay : Layer) (hlay : lay ≠ 0) :
    evalWithAnswerFn answers (recoverLayerPair
      (assembledAt index rho forest
        (evalWithAnswerFn answers (RetainedAncestor.prepare index)) selected top)
      index lay (selected.getD lay.val (0,[],0)).2.1) =
      topPair lay ((evalWithAnswerFn answers (RetainedAncestor.prepare index)).getD
        (lay.val-1) ([],[])).1 := by
  have hp := prepared_at answers index lay hlay
  have hv := selected_valid answers index _ forest.2 (2^25) selected hs lay
  rw [hp]
  apply RetainedAncestor.eval_recoverLayerPair_prepared answers _ hlay index _ hv
  rw [assembled_lower index rho forest _ selected top lay hlay, hp]

/-- A well-formed cached TOP piece completes to the honest public root. MAC
success alone is not this premise: hcache is an explicit key-consistency fact. -/
theorem honest_top_root (answers : Answers) (cache : Cache) (index : Nat)
    (sig : Signature) (digits : List Nat)
    (hcache : cache.region = cacheRegion (maskedTop answers))
    (hindex : index < 2^31) (hv : ValidDigits 0 digits)
    (htop : sig.layers 0 = piecesSignature 0
      (evalWithAnswerFn answers (SigGolfCandidate.T3.signTop cache (route index 0).1 digits))) :
    evalWithAnswerFn answers (topNode index
      (evalWithAnswerFn answers (topFold sig index digits)) (topSib sig)) =
      treeValue (builtTree answers 0 0) 12 0 := by
  rw [eval_signTop_honest answers cache _ digits hcache (route_leaf_bound index 0) hv]
    at htop
  have hr := recoverLayer_honestPieces answers (toT3Signature sig) index 0 digits hv
    (by simpa only [route_top_tree index hindex] using htop)
  rw [recoverLayer_top, evalWithAnswerFn_bind] at hr
  simpa only [route_top_tree index hindex] using hr

/-- The original omitted high bits witness existence of a completion. They need
not be the FIRST matching bits; only the completed root is used. -/
theorem honest_completion (answers : Answers) (sig : Signature) (index : Nat)
    (digits : List Nat) (pk : Digest)
    (hroot : evalWithAnswerFn answers (topNode index
      (evalWithAnswerFn answers (topFold sig index digits)) (topSib sig)) = pk) :
    evalWithAnswerFn answers (topNode index
      (evalWithAnswerFn answers (topFold (sigDecC (sigBC sig)) index digits))
      (setTop (topSib (sigDecC (sigBC sig))) ((topSib sig).toNat / 2^112))) = pk := by
  rw [ReplayComposition.topFold_compact, sigDecC_sigBC, topSib_proj,
    setTop_setTop, setTop_self]
  exact hroot

/-- An encode result is canonical by construction; no second assumption that
its decoded byte names the chosen pair is needed. -/
theorem decode_of_encode (pair : Nat × Nat) (tag : Fin 256)
    (hm : pair ∈ ReplayHintPacket.hintPairs)
    (he : ReplayHintPacket.encodeHint pair = some tag) :
    ReplayHintPacket.decodeHint tag = some pair := by
  have hr := ReplayHintPacket.pair_roundtrip pair hm
  simpa only [he, Option.bind_some] using hr

end ClaudeWCT.WCT9.Research.SignReplay

namespace ClaudeWCT.WCT9.Research.SignReplay
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness SigGolfCandidate.T3.Cost
open ClaudeWCT.W9.T3M

/-- Invert only successful signing. Failure of the MAC, digest search, selector,
or byte encoding cannot produce this result. Preparation/forest/top evaluation
are deterministic functions of the same Answers, not new independent premises. -/
theorem sign_success_data (answers : Answers) (cache : Cache) (message : Message)
    (bytes : CompactReplayHint.HBytes)
    (hs : evalWithAnswerFn answers (RetainedAncestor.sign cache message) = some bytes) :
    ∃ (counter : BitVec 32) (output : HashOutput)
      (selected : List RetainedAncestor.Selected) (tag : Fin 256),
      evalWithAnswerFn answers (digestSearch
        (evalWithAnswerFn answers (privateNonce message)) message 0 digestAttemptLimit) =
          some (counter,output) ∧
      evalWithAnswerFn answers (RetainedAncestor.select (digestIndex output)
        (evalWithAnswerFn answers (RetainedAncestor.prepare (digestIndex output)))
        (evalWithAnswerFn answers (signForest (digestIndex output) output)).2
        (2^25) 4 0) = some selected ∧
      ReplayHintPacket.encodeHint (RetainedAncestor.replayPair selected) = some tag ∧
      bytes = CompactReplayHint.pack (sigBC (assembledAt (digestIndex output)
        (evalWithAnswerFn answers (privateNonce message))
        (evalWithAnswerFn answers (signForest (digestIndex output) output))
        (evalWithAnswerFn answers (RetainedAncestor.prepare (digestIndex output))) selected
        (evalWithAnswerFn answers (SigGolfCandidate.T3.signTop cache
          (route (digestIndex output) 0).1 (selected.getD 0 (0,[],0)).2.1)))) tag := by
  simp only [RetainedAncestor.sign, evalWithAnswerFn_bind] at hs
  by_cases hm : evalWithAnswerFn answers (privateMac cache.region) ≠ cache.tag
  · simp [hm, evalWithAnswerFn_pure] at hs
  · simp only [hm, if_false, evalWithAnswerFn_bind] at hs
    cases hd : evalWithAnswerFn answers (digestSearch
      (evalWithAnswerFn answers (privateNonce message)) message 0 digestAttemptLimit) with
    | none => simp [hd, evalWithAnswerFn_pure] at hs
    | some found =>
        obtain ⟨counter,output⟩ := found
        simp only [hd, evalWithAnswerFn_bind] at hs
        cases hsel : evalWithAnswerFn answers (RetainedAncestor.select (digestIndex output)
          (evalWithAnswerFn answers (RetainedAncestor.prepare (digestIndex output)))
          (evalWithAnswerFn answers (signForest (digestIndex output) output)).2
          (2^25) 4 0) with
        | none => simp [hsel, evalWithAnswerFn_pure] at hs
        | some selected =>
            simp only [hsel] at hs
            cases he : ReplayHintPacket.encodeHint (RetainedAncestor.replayPair selected) with
            | none => simp [he, evalWithAnswerFn_pure] at hs
            | some tag =>
                simp only [he, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
                  Option.some.injEq] at hs
                exact ⟨counter,output,selected,tag,hd,hsel,he,
                  by simpa only [assembledAt] using hs.symm⟩

/-- Complete deterministic bridge for the actual retained signer. Successful
signing supplies its own searches and hint; the only key premise is honest
cached-top contents and the corresponding public root. No global assumption
that all searches succeed, no omitted-bit uniqueness, and no adaptive oracle
law are used. Elaboration and machine/security/resource links remain external. -/
theorem sign_expands (answers : Answers) (cache : Cache) (message : Message)
    (bytes : CompactReplayHint.HBytes)
    (hcache : cache.region = cacheRegion (maskedTop answers))
    (hsign : evalWithAnswerFn answers (RetainedAncestor.sign cache message) = some bytes) :
    ∃ witness, evalWithAnswerFn answers (CompactReplayHint.expand message
      (treeValue (builtTree answers 0 0) 12 0) bytes) = some witness := by
  obtain ⟨counter,output,selected,tag,hd,hs,he,hbytes⟩ :=
    sign_success_data answers cache message bytes hsign
  let index := digestIndex output
  let rho := evalWithAnswerFn answers (privateNonce message)
  let prepared := evalWithAnswerFn answers (RetainedAncestor.prepare index)
  let forest := evalWithAnswerFn answers (signForest index output)
  let top := evalWithAnswerFn answers (SigGolfCandidate.T3.signTop cache (route index 0).1
    (selected.getD 0 (0,[],0)).2.1)
  let sig := assembledAt index rho forest prepared selected top
  have hb : bytes = CompactReplayHint.pack (sigBC sig) tag := hbytes
  have hrecovery : ∀ lay : Layer, lay ≠ 0 →
      evalWithAnswerFn answers (recoverLayerPair (sigDecC (sigBC sig)) index lay
        (selected.getD lay.val (0,[],0)).2.1) =
        topPair lay (prepared.getD (lay.val-1) ([],[])).1 := by
    intro lay hlay
    rw [ReplayComposition.recoverPair_compact sig index lay _ hlay]
    exact selected_recovery answers index rho forest selected top hs lay hlay
  obtain ⟨tag',f0,f1,f2,f3,hslist,henc,hdec,hl⟩ :=
    SelectorTrace.eval_layers_from_select answers (sigDecC (sigBC sig)) index
      prepared forest.2 selected hs hrecovery
  have htag : tag' = tag := Option.some.inj (henc.symm.trans he)
  subst tag'
  have hforest : evalWithAnswerFn answers
      (recoverFts (sigDecC (sigBC sig)) index output) = forest.2 := by
    rw [sigDecC_sigBC]
    change evalWithAnswerFn answers (recoverFts (fillTop sig 0) index output) = forest.2
    rw [recoverFts_fillTop]
    exact assembled_forest_recovery answers rho index output _
  have hrho : (sigDecC (sigBC sig)).rho = rho := by
    rw [sigDecC_sigBC]
    rfl
  have hd' : evalWithAnswerFn answers (digestSearch
      (sigDecC (sigBC sig)).rho message 0 digestAttemptLimit) = some (counter,output) := by
    rw [hrho]
    exact hd
  have hv := selected_valid answers index prepared forest.2 (2^25) selected hs 0
  have hfull := honest_top_root answers cache index sig
    (selected.getD 0 (0,[],0)).2.1 hcache (digestIndex_lt output) hv
    (assembled_top index rho forest prepared selected top)
  have hmatch := honest_completion answers sig index
    (selected.getD 0 (0,[],0)).2.1 (treeValue (builtTree answers 0 0) 12 0) hfull
  have hf0 : (selected.getD 0 (0,[],0)).2.1 = f0.2.1 := by simp [hslist]
  rw [hf0] at hmatch
  apply ReplayComposition.eval_expand_complete answers message
    (treeValue (builtTree answers 0 0) 12 0) bytes (RetainedAncestor.replayPair selected)
    counter output
    (evalWithAnswerFn answers (topFold (sigDecC (sigBC sig)) index f0.2.1))
    (evalWithAnswerFn answers (topNode index
      (evalWithAnswerFn answers (topFold (sigDecC (sigBC sig)) index f0.2.1))
      (topSib (sigDecC (sigBC sig)))))
    [f0.1,f1.1,f2.1,f3.1] f0.2.2
    [ReplayHintExpand.score 0 f0.2.1, ReplayHintExpand.score 1 f1.2.1,
      ReplayHintExpand.score 2 f2.2.1, ReplayHintExpand.score 3 f3.2.1]
    ((topSib sig).toNat / 2^112)
  · simpa only [hb, CompactReplayHint.tag_pack] using hdec
  · simpa only [hb, CompactReplayHint.payload_pack] using hd'
  · simpa only [hb, CompactReplayHint.payload_pack, hforest] using hl
  · rw [hslist, ReplayComposition.canonical_pair_four]
  · simp only [hb, CompactReplayHint.payload_pack]
  · exact top_lt (topSib sig)
  · simpa only [hb, CompactReplayHint.payload_pack] using hmatch

/-- Public-key form of the bridge. The cache-tag part of KeygenCorrect is not
needed AGAIN after a successful sign, but the honest cache contents are. -/
theorem sign_expands_of_keygen (answers : Answers) (keys : Digest × Cache)
    (hkeys : KeygenCorrect answers keys) (message : Message)
    (bytes : CompactReplayHint.HBytes)
    (hs : evalWithAnswerFn answers (RetainedAncestor.sign keys.2 message) = some bytes) :
    ∃ witness, evalWithAnswerFn answers (CompactReplayHint.expand message keys.1 bytes) =
      some witness := by
  rw [hkeys.1]
  exact sign_expands answers keys.2 message bytes hkeys.2.1 hs

end ClaudeWCT.WCT9.Research.SignReplay
