import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsEncodingResample
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsExtractLayer
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.SeccSufRoute

namespace ClaudeWCT.W9.T3.Security.BSuf
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers treeValue)
open ClaudeWCT.W9.T3M (expandN0 witEnc expandN0_facts wreveal_witEnc wsib_witEnc)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem expandN_unfold (answers : Answers) (m : Message) (pk : Digest) (σ : WCT9.Signature) (N : HashOutput)
    (wit : WCT9.Witness) (he : evalWithAnswerFn answers (expandN0 m pk σ) = some (N, wit)) :
    ∃ counter cs,
      evalWithAnswerFn answers (WCT9.digestSearch σ.rho m 0 WCT9.digestAttemptLimit) = some (counter, N) ∧
      evalWithAnswerFn answers (WCT9.expandLayersBC σ (WCT9.digestIndex N) 4
        (.pair (evalWithAnswerFn answers (WCT9.recoverFts σ (WCT9.digestIndex N) N)).1
          (evalWithAnswerFn answers (WCT9.recoverFts σ (WCT9.digestIndex N) N)).2)) = some (pk, cs) ∧
      wit = ⟨σ, counter, fun lay => cs.getD lay.val 0⟩ := by
  simp only [expandN0, evalWithAnswerFn_bind] at he
  cases hd : evalWithAnswerFn answers (WCT9.digestSearch σ.rho m 0 WCT9.digestAttemptLimit) with
  | none => simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some found =>
      obtain ⟨counter, output⟩ := found
      simp only [hd, evalWithAnswerFn_bind] at he
      cases hl : evalWithAnswerFn answers (WCT9.expandLayersBC σ (WCT9.digestIndex output) 4
          (.pair (evalWithAnswerFn answers (WCT9.recoverFts σ (WCT9.digestIndex output) output)).1
            (evalWithAnswerFn answers (WCT9.recoverFts σ (WCT9.digestIndex output) output)).2)) with
      | none => simp only [hl, evalWithAnswerFn_pure, reduceCtorEq] at he
      | some layers =>
          obtain ⟨root, cs⟩ := layers
          simp only [hl] at he
          split at he
          · simp only [evalWithAnswerFn_pure, reduceCtorEq] at he
          · rename_i hne
            simp only [evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            have hroot : root = pk := by simpa using hne
            subst hroot
            exact ⟨counter, cs, rfl, hl, rfl⟩
theorem layer_of_shaped (answers : Answers) (N : HashOutput) (wit : WCT9.Witness) (lay : Layer) (digits : List Nat)
    (hs : ClaudeWCT.W9.T3M.Extract.LayerShaped answers (witEnc N wit) (WCT9.digestIndex N) lay digits) :
    wit.signature.layers lay = piecesSignature lay (WCT9.wotsPieces answers lay
      (route (WCT9.digestIndex N) lay).2 (route (WCT9.digestIndex N) lay).1 digits) := by
  apply SigGolfCandidate.T3M.LayerSignature.ext'
  · funext i
    have hv : ClaudeWCT.W9.T3M.wvalueFor (witEnc N wit) lay digits i.val =
        (wit.signature.layers lay).values i := by
      unfold ClaudeWCT.W9.T3M.wvalueFor
      split
      · exact ClaudeWCT.W9.T3M.wbuffer_witEnc N wit lay i
      · exact ClaudeWCT.W9.T3M.wvalue_witEnc N wit lay i
    rw [← hv, (hs.2 i.val i.isLt).1]
    simp [piecesSignature, WCT9.wotsPieces]
  · funext j
    rw [← ClaudeWCT.W9.T3M.wpath_witEnc N wit lay j, (hs.1 j.val j.isLt).1]
    simp [piecesSignature, WCT9.wotsPieces]
theorem layers_payload (answers : Answers) (published : SigGolfCandidate.T3.Cache)
    (hcache : published.region = Correctness.cacheRegion (Correctness.maskedTop answers))
    (N : HashOutput) (wit : WCT9.Witness)
    (hgood : ∀ lay : Layer, ClaudeWCT.W9.T3M.Extract.Good answers (witEnc N wit) (WCT9.digestIndex N) lay) :
    ∀ n, n ≤ 4 → ∀ (msg : WCT9.LayerMsg) (root : Digest) (cs : List (BitVec 32)),
      (∀ k, n = k + 1 → msg = ClaudeWCT.W9.T3M.Extract.honestMsg answers (WCT9.digestIndex N) (Fin.ofNat 4 k)) →
      evalWithAnswerFn answers (WCT9.expandLayersBC wit.signature (WCT9.digestIndex N) n msg) = some (root, cs) →
      (∀ lay : Layer, lay.val < n → wit.counters lay = cs.getD lay.val 0) →
      ∃ pieces, evalWithAnswerFn answers (WCT9.signLayersBC published (WCT9.digestIndex N) n msg) = some pieces ∧
        pieces.length = n ∧ ∀ lay : Layer, lay.val < n →
          wit.signature.layers lay = piecesSignature lay (pieces.getD lay.val ([], [])) := by
  have hidx : WCT9.digestIndex N < 2 ^ 31 := Nat.mod_lt _ (by decide)
  intro n
  induction n with
  | zero =>
      intro _ msg root cs _ hexp _
      simp [WCT9.expandLayersBC] at hexp
  | succ n ih =>
      intro hn msg root cs hval hexp hctr
      have hv : (Fin.ofNat 4 n : Layer).val = n := Nat.mod_eq_of_lt (by omega)
      have hmsg := hval n rfl
      have hlenAll := (WCT9.expandLayersBC_verified answers wit.signature (WCT9.digestIndex N) (n + 1) hn msg root cs
        hexp).1
      simp only [WCT9.expandLayersBC, evalWithAnswerFn_bind] at hexp
      cases hs : evalWithAnswerFn answers (WCT9.layerCounterSearch (Fin.ofNat 4 n)
          (route (WCT9.digestIndex N) (Fin.ofNat 4 n)).2 (route (WCT9.digestIndex N) (Fin.ofNat 4 n)).1 msg 0
          (WCT9.searchLimit (Fin.ofNat 4 n))) with
      | none => simp only [hs, evalWithAnswerFn_pure, reduceCtorEq] at hexp
      | some found =>
          obtain ⟨counter, digits⟩ := found
          have hsome := WCT9.layerCounterSearch_some answers (Fin.ofNat 4 n)
            (route (WCT9.digestIndex N) (Fin.ofNat 4 n)).2
            (route (WCT9.digestIndex N) (Fin.ofNat 4 n)).1 msg (WCT9.searchLimit (Fin.ofNat 4 n)) 0 counter digits
            (ClaudeWCT.W9.T3.Security.Wots.searchLimit_fits _) hs
          have hvalid := Cost.validDigits_decode hsome.2.2
          simp only [hs] at hexp
          have hcounter : wit.counters (Fin.ofNat 4 n) = counter := by
            by_cases hn0 : n = 0
            · subst hn0
              simp only [if_true, evalWithAnswerFn_bind, evalWithAnswerFn_pure, Option.some.injEq,
                Prod.mk.injEq] at hexp
              obtain ⟨-, hcs⟩ := hexp
              rw [hctr _ (by rw [hv]; omega), ← hcs, hv]
              rfl
            · simp only [hn0, if_false, evalWithAnswerFn_bind] at hexp
              generalize evalWithAnswerFn answers (WCT9.expandLayersBC wit.signature (WCT9.digestIndex N) n
                (.pair (evalWithAnswerFn answers (WCT9.recoverLayerPair wit.signature (WCT9.digestIndex N)
                  (Fin.ofNat 4 n) digits)).1 (evalWithAnswerFn answers (WCT9.recoverLayerPair wit.signature
                    (WCT9.digestIndex N) (Fin.ofNat 4 n) digits)).2)) = res at hexp
              rcases res with _ | ⟨root', cs'⟩
              · simp at hexp
              · simp only [evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at hexp
                obtain ⟨-, hcs⟩ := hexp
                have hlen' : cs'.length = n := by rw [← hcs] at hlenAll; simpa using hlenAll
                rw [hctr _ (by rw [hv]; omega), ← hcs, hv, List.getD_append_right _ _ _ _ (by omega), hlen']
                simp
          obtain ⟨digitsG, ⟨_, hdec⟩, hshape⟩ := hgood (Fin.ofNat 4 n)
          have hright : ClaudeWCT.W9.T3M.wbcRight (witEnc N wit) = 0 := ClaudeWCT.W9.T3M.wright3_witEnc N wit
          rw [ClaudeWCT.W9.T3M.wbcCtr_witEnc, ClaudeWCT.W9.T3M.wbcPad_witEnc, hright, hcounter, ← hmsg,
            ClaudeWCT.W9.T3M.encodingHash_layerEncodingInputP_zero] at hdec
          rw [hsome.2.2, Option.some.injEq] at hdec
          subst hdec
          rename' digits => digitsG
          have hlayer := layer_of_shaped answers N wit (Fin.ofNat 4 n) digitsG hshape
          by_cases hn0 : n = 0
          · subst hn0
            have ht : (route (WCT9.digestIndex N) 0).2 = 0 := route_top_tree (WCT9.digestIndex N) hidx
            have htop := Correctness.eval_signTop_honest answers published (route (WCT9.digestIndex N) 0).1
              digitsG hcache (route_leaf_bound (WCT9.digestIndex N) 0) hvalid
            refine ⟨[WCT9.wotsPieces answers 0 0 (route (WCT9.digestIndex N) 0).1 digitsG], ?_, rfl, ?_⟩
            · simp only [WCT9.signLayersBC, evalWithAnswerFn_bind, hs, ite_true, evalWithAnswerFn_pure,
                Option.map_some, Option.getD_some]
              rw [show (Fin.ofNat 4 0 : Layer) = 0 from rfl, htop, WCT9.wotsPieces_top]
            · intro lay hlay
              have hl0 : lay = 0 := Fin.ext (by simp at hlay ⊢; omega)
              subst hl0
              rw [show (Fin.ofNat 4 0 : Layer) = 0 from rfl, ht] at hlayer
              exact hlayer
          · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
            have hrecover : evalWithAnswerFn answers (WCT9.recoverLayerPair wit.signature (WCT9.digestIndex N)
                (Fin.ofNat 4 (k + 1)) digitsG) =
                WCT9.builtPair answers (Fin.ofNat 4 (k + 1)) (route (WCT9.digestIndex N) (Fin.ofNat 4 (k + 1))).2 := by
              apply WCT9.eval_recoverLayerPair_honest answers wit.signature _ _ digitsG hvalid
              · intro i
                rw [hlayer]
                simp [piecesSignature, WCT9.wotsPieces, List.getD_eq_getElem, i.isLt]
              · intro j
                rw [hlayer]
                simp [piecesSignature, WCT9.wotsPieces, List.getD_eq_getElem, j.isLt]
            have hnext : WCT9.LayerMsg.pair (WCT9.builtPair answers (Fin.ofNat 4 (k + 1))
                (route (WCT9.digestIndex N) (Fin.ofNat 4 (k + 1))).2).1
                (WCT9.builtPair answers (Fin.ofNat 4 (k + 1)) (route (WCT9.digestIndex N) (Fin.ofNat 4 (k + 1))).2).2 =
                ClaudeWCT.W9.T3M.Extract.honestMsg answers (WCT9.digestIndex N) (Fin.ofNat 4 k) := by
              rw [ClaudeWCT.W9.T3.Security.BPB.honestMsg_lower answers (WCT9.digestIndex N) k (by omega)]
              rfl
            simp only [show k + 1 ≠ 0 by omega, if_false, evalWithAnswerFn_bind, hrecover] at hexp
            generalize hres : evalWithAnswerFn answers (WCT9.expandLayersBC wit.signature (WCT9.digestIndex N) (k + 1)
              (.pair (WCT9.builtPair answers (Fin.ofNat 4 (k + 1)) (route (WCT9.digestIndex N) (Fin.ofNat 4 (k + 1))).2).1
                (WCT9.builtPair answers (Fin.ofNat 4 (k + 1))
                  (route (WCT9.digestIndex N) (Fin.ofNat 4 (k + 1))).2).2)) = res at hexp
            rcases res with _ | ⟨root', cs'⟩
            · simp at hexp
            simp only [evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at hexp
            obtain ⟨-, hcs⟩ := hexp
            have hlen' : cs'.length = k + 1 := by rw [← hcs] at hlenAll; simpa using hlenAll
            obtain ⟨pieces, hpieces, hplen, hpagree⟩ := ih (by omega) _ root' cs'
              (fun k' hk' => by rw [hnext]; congr; omega) hres
              (fun lay hlay => by
                rw [hctr lay (by omega), ← hcs, List.getD_append _ _ _ _ (by omega)])
            have hl0 : (Fin.ofNat 4 (k + 1) : Layer) ≠ 0 := by
              intro h
              have := congrArg Fin.val h
              rw [hv] at this
              simp at this
            have htree := WCT9.eval_buildTreeP_result answers hl0
              (route (WCT9.digestIndex N) (Fin.ofNat 4 (k + 1))).2
              (route (WCT9.digestIndex N) (Fin.ofNat 4 (k + 1))).1 digitsG hvalid
              (route_leaf_bound (WCT9.digestIndex N) _)
            refine ⟨pieces ++ [WCT9.wotsPieces answers (Fin.ofNat 4 (k + 1))
              (route (WCT9.digestIndex N) (Fin.ofNat 4 (k + 1))).2
              (route (WCT9.digestIndex N) (Fin.ofNat 4 (k + 1))).1 digitsG], ?_,
              by simp [hplen], ?_⟩
            · rw [WCT9.signLayersBC]
              simp only [evalWithAnswerFn_bind, hs, htree, show k + 1 ≠ 0 by omega, ite_false, WCT9.topPair_take,
                WCT9.map_range_take_path]
              have hpair : WCT9.topPair (Fin.ofNat 4 (k + 1)) (WCT9.wotsTree answers (Fin.ofNat 4 (k + 1))
                  (route (WCT9.digestIndex N) (Fin.ofNat 4 (k + 1))).2) =
                  WCT9.builtPair answers (Fin.ofNat 4 (k + 1)) (route (WCT9.digestIndex N) (Fin.ofNat 4 (k + 1))).2 :=
                rfl
              rw [hpair, hpieces]
              rfl
            · intro lay hlay
              by_cases hlt : lay.val < k + 1
              · rw [hpagree lay hlt, List.getD_append _ _ _ _ (by omega)]
              · have hle : lay = Fin.ofNat 4 (k + 1) := Fin.ext (by rw [hv]; omega)
                subst hle
                rw [hlayer, hv, List.getD_append_right _ _ _ _ (by omega), hplen]
                simp
theorem opening_ext {a b : WCT9.Opening} (hv : ∀ t, a.values t = b.values t) (hp : ∀ l, a.path l = b.path l) :
    a = b := by
  cases a
  cases b
  simp only [WCT9.Opening.mk.injEq]
  exact ⟨funext hv, funext hp⟩
theorem openings_of_honest (answers : Answers) (N : HashOutput) (wit : WCT9.Witness)
    (hH : ClaudeWCT.W9.T3M.WctExtract.WctHonest answers N (witEnc N wit)) (k : WCT9.Coord) :
    wit.signature.openings k = WCT9.expectedOpening answers (WCT9.digestIndex N) N k := by
  obtain ⟨hval, hsib⟩ := hH.2.1 k
  apply opening_ext
  · intro t
    rw [← wreveal_witEnc N wit k t (WCT9.wordDigit (WCT9.rank N k) t), (hval t).1]
    unfold WCT9.expectedOpening WCT9.honestOpening
    rw [WCT9.buildCoordinateF_result]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp
    rfl
  · intro l
    rw [← wsib_witEnc N wit k l, (hsib l.val l.isLt).1]
    unfold WCT9.expectedOpening WCT9.honestOpening
    rw [WCT9.buildCoordinateF_result]
    simp only [List.getD_eq_getElem?_getD]
    simp [treeValue, List.getD_eq_getElem?_getD, ClaudeWCT.W9.T3M.Extract.ftsLevels]
    rfl
theorem caseC_expansion_is_payload (answers : Answers) (published : SigGolfCandidate.T3.Cache)
    (message : Message) (pk : Digest) (signature : WCT9.Signature) (N : HashOutput) (wit : WCT9.Witness)
    (hcache : published.region = Correctness.cacheRegion (Correctness.maskedTop answers))
    (he : evalWithAnswerFn answers (expandN0 message pk signature) = some (N, wit))
    (hgood : ∀ lay : Layer, ClaudeWCT.W9.T3M.Extract.Good answers (witEnc N wit) (WCT9.digestIndex N) lay)
    (hfts : ClaudeWCT.W9.T3M.WctExtract.WctHonest answers N (witEnc N wit)) :
    evalWithAnswerFn answers (ClaudeWCT.W9.T3.Security.BPB.payloadForNonce published signature.rho message) =
      some signature := by
  have F := expandN0_facts answers message pk signature N wit he
  obtain ⟨counter, cs, hds, hel, hwit⟩ := expandN_unfold answers message pk signature N wit he
  have hopen : ∀ coord, signature.openings coord = WCT9.expectedOpening answers (WCT9.digestIndex N) N coord := by
    intro coord
    rw [← F.sig]
    exact openings_of_honest answers N wit hfts coord
  have hrf : evalWithAnswerFn answers (WCT9.recoverFts signature (WCT9.digestIndex N) N) =
      WCT9.honestTop answers (WCT9.digestIndex N) :=
    WCT9.recoverFts_honest answers signature _ N hopen
  obtain ⟨pieces, hpieces, -, hpagree⟩ := layers_payload answers published hcache N wit hgood 4 le_rfl
    (.pair (WCT9.honestTop answers (WCT9.digestIndex N)).1 (WCT9.honestTop answers (WCT9.digestIndex N)).2) pk cs
    (fun k hk => by
      obtain rfl : k = 3 := by omega
      exact (ClaudeWCT.W9.T3.Security.BPB.honestMsg_three answers _).symm)
    (by rw [F.sig, ← hrf]; exact hel)
    (fun lay _ => by rw [hwit])
  have hO : ∀ coord : WCT9.Coord,
      (List.ofFn (WCT9.expectedOpening answers (WCT9.digestIndex N) N)).getD coord.val ⟨fun _ => 0, fun _ => 0⟩ =
        signature.openings coord := by
    intro coord
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact coord.isLt), List.getElem_ofFn]
    exact (hopen coord).symm
  have hL : ∀ lay : Layer, piecesSignature lay (pieces.getD lay.val ([], [])) = signature.layers lay := by
    intro lay
    have := hpagree lay lay.isLt
    rw [F.sig] at this
    exact this.symm
  unfold ClaudeWCT.W9.T3.Security.BPB.payloadForNonce
  simp only [evalWithAnswerFn_bind, hds, WCT9.eval_signForest, hpieces, evalWithAnswerFn_pure]
  congr 1
  clear hpieces hpagree hrf hopen hel hwit F he hds
  cases signature
  simp only [WCT9.assembledSignature, WCT9.Signature.mk.injEq]
  exact ⟨trivial, funext hO, funext hL⟩
end ClaudeWCT.W9.T3.Security.BSuf
namespace ClaudeWCT.W9.T3.Security.BPB
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M (wrho wdc)
open ClaudeWCT.W9.T3M (WBytes expandN witEnc expandN_facts eval_expandB wrho_witEnc wdc_witEnc)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem gameCaseC_signed_false (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP) (answers : Correctness.Answers)
    (result : FirstHit.Recorded Bool)
    (ha : ∀ input answer, SourceReplay.known result.state input = some answer → answers input = answer) :
    ¬GameCaseC adversary answers id result := by
  rintro ⟨generated, hg, interaction, hi, hext, hpk, -, forgery, hforgery, hfresh, message, witness, hof, hsigned,
    hC⟩
  have hirun := FirstHit.recorded_support _ _ _ hi
  have hgext : SourceReplay.Extends generated.state interaction.state :=
    SourceReplay.run_extends _ generated.state _ hirun
  have hai : ∀ input answer, SourceReplay.known interaction.state input = some answer → answers input = answer :=
    fun input answer hk => ha input answer (SourceReplay.known_mono _ _ hext hk)
  have hgen : evalWithAnswerFn answers keygen = generated.value :=
    (SourceReplay.resolves_of_run keygen SourceReplay.keygen_hashOnly (∅, ∅)
      (generated.value, generated.state) (FirstHit.recorded_support _ _ _ hg)).eval answers
        (fun input answer hk => hai input answer (SourceReplay.known_mono _ _ hgext hk))
  have hcache : generated.value.2.region = Correctness.cacheRegion (Correctness.maskedTop answers) := by
    rw [← hgen]
    exact (Correctness.keygen_correct answers).2.1
  obtain ⟨entry, hentry, hmsg, σm, hσm, hrho⟩ := hsigned
  have hres := logged_resolves generated.value.2 _ generated.state _ hirun entry hentry
  have hlog : evalWithAnswerFn answers (FullGame.authenticatedSign generated.value.2 entry.1) = some σm := by
    rw [hres.eval answers hai, hσm]
  obtain ⟨-, -, hpay⟩ := authenticatedSign_payload answers generated.value.2 entry.1 σm hlog
  cases forgery with
  | witness m w =>
      exact hfresh ⟨entry, hentry, by rw [hmsg]; exact hof.1, by rw [hσm]; rfl⟩
  | signature m σ =>
      obtain ⟨hm, hexp⟩ := hof
      rw [eval_expandB] at hexp
      cases hx : evalWithAnswerFn answers (expandN m generated.value.1 σ) with
      | none => rw [hx] at hexp; simp at hexp
      | some x =>
          obtain ⟨N, wit⟩ := x
          rw [hx] at hexp
          simp only [Option.map_some, Option.some.injEq] at hexp
          subst hexp
          have F := expandN_facts answers m _ σ N wit hx
          obtain ⟨N', -, hN', -, -, hgood, hfts, -⟩ := hC
          have hNN : N' = N := by
            rw [← hN', wrho_witEnc, wdc_witEnc, F.rho, hm]
            exact F.digest
          subst hNN
          obtain ⟨c, -, -, h0⟩ := F.fill
          have hpayσ := BSuf.caseC_expansion_is_payload answers generated.value.2 m _ (WCT9.fillTop σ c) N' wit
            hcache h0 (fun lay => (hgood lay).good) hfts
          rw [WCT9.fillTop_rho] at hpayσ
          have hrhoσ : σm.rho = σ.rho := by rw [hrho, wrho_witEnc, F.rho]
          rw [hmsg, hrhoσ, hm, hpayσ, Option.some.injEq] at hpay
          subst hpay
          exact hfresh ⟨entry, hentry, by rw [hmsg, hm], by rw [hσm]; simp only [Option.map_some, WCT9.proj_fillTop]⟩
theorem caseC_signed_impossible (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (z : PaddedGame.TraceResult × Correctness.Answers) (hz : z ∈ (SeccLaw.completedExperiment adversary q hq).support)
    (_hclean : QueryRecorded.CleanWin q z.1) : ¬CaseCSigned adversary z :=
  gameCaseC_signed_false adversary z.2 _ (SeccLaw.completed_agrees adversary q hq z hz).2
end ClaudeWCT.W9.T3.Security.BPB

namespace ClaudeWCT.W9.T3.Security.CanonicalExtract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots (LeafAddr)
open SigGolfCandidate.T3.Security.WotsExtract (routeLeaf)
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem layer_of_shaped_readout (answers : Answers) (index : Nat) (wb : WBytes)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (lay : Layer) (digits : List Nat)
    (hs : Extract.LayerShaped answers wb index lay digits)
    (hval : ∀ i : Fin (chainCount lay), wvalueFor wb lay digits i.val = (sig.layers lay).values i)
    (hpath : ∀ j : Fin (height lay), wpath wb lay (route index lay).1 j.val = (sig.layers lay).path j) :
    sig.layers lay = piecesSignature lay (WCT9.wotsPieces answers lay
      (route index lay).2 (route index lay).1 digits) := by
  apply SigGolfCandidate.T3M.LayerSignature.ext'
  · funext i
    rw [← hval i, (hs.2 i.val i.isLt).1]
    simp [piecesSignature, WCT9.wotsPieces]
  · funext j
    rw [← hpath j, (hs.1 j.val j.isLt).1]
    simp [piecesSignature, WCT9.wotsPieces]

theorem good_shape_readout (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (index : Nat) (wb : WBytes) (sig : SigGolfCandidate.Research.SharedForest.Signature)
    (counters : Layer → BitVec 32)
    (hg : ∀ lay, Good answers messages wb index lay)
    (hctr : ∀ lay, wbcCtr wb index lay = counters lay)
    (hpair : ∀ lay, ∃ left right, messages (routeLeaf index lay) = .pair left right)
    (hval : ∀ lay digits (i : Fin (chainCount lay)),
      wvalueFor wb lay digits i.val = (sig.layers lay).values i)
    (hpath : ∀ lay (j : Fin (height lay)),
      wpath wb lay (route index lay).1 j.val = (sig.layers lay).path j) :
    ∀ lay, ∃ digits, WCT9.CanonicalPolicy.decode lay
      (evalWithAnswerFn answers (WCT9.encodingHash lay (WCT9.layerEncodingInput lay
        (route index lay).2 (route index lay).1 (messages (routeLeaf index lay)) (counters lay)))) = some digits ∧
      sig.layers lay = piecesSignature lay (WCT9.wotsPieces answers lay
        (route index lay).2 (route index lay).1 digits) := by
  intro lay
  obtain ⟨⟨digits, hframe, hs⟩, hpad⟩ := hg lay
  have hd := hframe.2
  have he (counter : BitVec 32) :
      WCT9.encodingHash lay (layerEncodingInputP lay (route index lay).2 (route index lay).1
        (messages (routeLeaf index lay)) counter 0 (wbcRight wb)) =
      WCT9.encodingHash lay (WCT9.layerEncodingInput lay (route index lay).2 (route index lay).1
        (messages (routeLeaf index lay)) counter) := by
    obtain ⟨left,right,hm⟩ := hpair lay
    rw [hm]
    rfl
  rw [hctr, hpad, he] at hd
  exact ⟨digits, hd, layer_of_shaped_readout answers index wb sig lay digits hs (hval lay digits) (hpath lay)⟩
#print axioms good_shape_readout
end ClaudeWCT.W9.T3.Security.CanonicalExtract

namespace ClaudeWCT.W9.T3.Security.CanonicalExtract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.WotsExtract (routeLeaf)
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem sourceMessages_pair (answers : Answers) (leaf : SigGolfCandidate.T3.Security.Wots.LeafAddr) :
    ∃ left right, CanonicalRef.sourceMessages answers leaf = .pair left right := by
  unfold CanonicalRef.sourceMessages
  split <;> exact ⟨_,_,rfl⟩

attribute [local irreducible] Paired.witEnc CanonicalRef.sourceMessages

theorem good_shape_witEnc (answers : Answers) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness)
    (hg : ∀ lay, Good answers (CanonicalRef.sourceMessages answers) (Paired.witEnc output w)
      (WCT9.digestIndex output) lay) :
    ∀ lay, ∃ digits, WCT9.CanonicalPolicy.decode lay
      (evalWithAnswerFn answers (WCT9.encodingHash lay (WCT9.layerEncodingInput lay
        (route (WCT9.digestIndex output) lay).2 (route (WCT9.digestIndex output) lay).1
        (CanonicalRef.sourceMessages answers (routeLeaf (WCT9.digestIndex output) lay)) (w.counters lay)))) =
      some digits ∧ w.signature.layers lay = piecesSignature lay (WCT9.wotsPieces answers lay
        (route (WCT9.digestIndex output) lay).2 (route (WCT9.digestIndex output) lay).1 digits) := by
  exact good_shape_readout answers (CanonicalRef.sourceMessages answers) (WCT9.digestIndex output)
    (Paired.witEnc output w) w.signature w.counters hg (Paired.wbcCtr_witEnc output w)
    (fun lay => sourceMessages_pair answers (routeLeaf (WCT9.digestIndex output) lay))
    (Paired.wvalueFor_witEnc output w) (Paired.wpath_witEnc output w)
#print axioms good_shape_witEnc
end ClaudeWCT.W9.T3.Security.CanonicalExtract

namespace ClaudeWCT.W9.T3M.Extract.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
open W9Machine
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] T3M.Paired.witEnc

theorem forest_openings_shape (answers : Answers) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness)
    (ho : ForestOpenings answers (T3M.Paired.witEnc output w) (digestIndex output)
      (rawChildFromOutput output) (fun coord => embed (forestRank output coord.val))) :
    w.signature.forest = (evalWithAnswerFn answers (buildForest (digestIndex output)
      (forestSelectionFromOutput output) (forestWordsFromOutput output))).1 := by
  apply T3M.Paired.forest_eq_of_coordinates
  · intro coord i
    rw [buildForest_coordinateValues]
    have hc := ((ho.2 coord).2.1 i).1
    change V3.reveal (T3M.Paired.witEnc output w) coord.val i.val
      (wordDigit (forestRank output coord.val) i) =
      ClaudeWCT.WCT9.chainValue answers (digestIndex output) coord.val
        (rawChildFromOutput output coord).val (forestRank output coord.val) i at hc
    have hr : V3.reveal (T3M.Paired.witEnc output w) coord.val i.val
        (wordDigit (forestRank output coord.val) i) =
        T3M.Paired.coordinateValues w.signature.forest coord i := by
      unfold V3.reveal
      split
      · exact T3M.Paired.wleafValue_witEnc output w coord i
      · exact T3M.Paired.wchainValue_witEnc output w coord i
    exact hr.symm.trans hc
  · intro coord level hl
    rw [buildForest_coordinatePath answers output coord level hl]
    have hp := SharedV3.physical_lt coord.val (rawChildFromOutput output coord).val
      (rawChildFromOutput output coord).isLt
    have hmax : level≤SharedV3.lastLevel coord.val+1 := by
      by_cases he : coord.val < 8 ∧ coord.val % 2 = 0
      · simp only [if_pos he] at hl
        simp [SharedV3.lastLevel, SharedV3.first, he]
        omega
      · simp only [if_neg he] at hl
        simp [SharedV3.lastLevel, SharedV3.first, he]
        omega
    have hc := (ho.2 coord).2
    by_cases hle : level≤SharedV3.lastLevel coord.val
    · have hl6 : level<6 := by
        unfold SharedV3.lastLevel at hle
        split_ifs at hle <;> omega
      have hs := PathStepGood.sibling_eq answers (T3M.Paired.witEnc output w)
        (digestIndex output) coord.val (SharedV3.physical coord.val (rawChildFromOutput output coord).val)
        level hp hl6 _ (hc.2.1 level hle)
      rw [T3M.Paired.wsibling_witEnc output w coord level (by omega)] at hs
      exact hs
    · have he : level=SharedV3.lastLevel coord.val+1 := by omega
      subst level
      rw [←T3M.Paired.wtopOther_witEnc output w coord]
      exact hc.2.2
#print axioms forest_openings_shape
end ClaudeWCT.W9.T3M.Extract.Paired
