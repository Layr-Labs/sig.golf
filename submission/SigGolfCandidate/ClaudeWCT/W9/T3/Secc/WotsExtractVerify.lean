import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsExtractLayer
import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.VerifyP

namespace ClaudeWCT.W9.T3.Security.WotsExtract
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.Wots (LeafAddr ChainAddr Entry low entriesOf)
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
open ClaudeWCT.W9.T3M.WctExtract (wctChainP_eq_hashPath wctChainInputP_block4 queried_hashPath queried_mapM
  hdrBlock_block4W leafHash_eq_shortHash hdrBlock_merkleInput recoverCoordinateP_dec wctTopInput_block4)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.W9.T3M (wrho wdc layerP)
open SigGolfCandidate.T3.Security.WotsExtract (SourceLeaf SourceChain mem_entriesOf entriesOf_mono)
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (bytesLE bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem layersBC_wots_walk (answers : Answers) (w : WBytes) (index : Nat) (hidx : index < 2 ^ 31) :
    ∀ n, 1 ≤ n → n ≤ 4 → ∀ msg : WCT9.LayerMsg, Extract.msgFits (Fin.ofNat 4 (n - 1)) msg →
    evalWithAnswerFn answers (layersBC w index n msg) = some (Extract.honestRoot answers 0 0) →
    WotsPrimitiveSrc answers (entriesOf answers (queried answers (layersBC w index n msg))) ∨
    ((∀ l : Layer, l.val < n → BC.GoodZ answers w index l) ∧
      msg = Extract.honestMsg answers index (Fin.ofNat 4 (n - 1)))
  | 0, h1, _, _, _, _ => absurd h1 (by decide)
  | n + 1, _, hn, msg, hfit, h => by
      classical
      obtain ⟨digits, hframe, henc, htop, hlow⟩ := Extract.layersBC_succ_split answers w index n msg _ h
      have hval : (Fin.ofNat 4 n : Layer).val = n := Extract.ofNat_val n (by omega)
      simp only [Nat.add_sub_cancel] at hfit ⊢
      have finish : WotsPrimitiveSrc answers (entriesOf answers (queried answers (layersBC w index (n + 1) msg))) ∨
          (msg = Extract.honestMsg answers index (Fin.ofNat 4 n) ∧ BC.GoodZ answers w index (Fin.ofNat 4 n)) →
          (∀ l : Layer, l.val < n → BC.GoodZ answers w index l) →
          WotsPrimitiveSrc answers (entriesOf answers (queried answers (layersBC w index (n + 1) msg))) ∨
          ((∀ l : Layer, l.val < n + 1 → BC.GoodZ answers w index l) ∧
            msg = Extract.honestMsg answers index (Fin.ofNat 4 n)) := by
        intro hx hgood
        rcases hx with hprim | ⟨hmsg, hgoodn⟩
        · exact Or.inl hprim
        · right
          refine ⟨fun l hl => ?_, hmsg⟩
          by_cases hle : l.val < n
          · exact hgood l hle
          · have hl : l = Fin.ofNat 4 n := Fin.ext (by rw [hval]; omega)
            subst hl
            exact hgoodn
      by_cases hn0 : n = 0
      · subst hn0
        obtain ⟨hout, hq⟩ := htop rfl
        have hroot : evalWithAnswerFn answers (layerP w index (Fin.ofNat 4 0) digits) =
            Extract.honestRoot answers (Fin.ofNat 4 0) (route index (Fin.ofNat 4 0)).2 := by
          rw [hout, show (Fin.ofNat 4 0 : Layer) = 0 from rfl, route_top_tree index hidx]
        exact finish (layer_wots answers w index (Fin.ofNat 4 0) msg digits hidx rfl hfit hframe _ henc hq hroot)
          (fun l hl => absurd hl (by omega))
      · obtain ⟨hrest, hqP, hqR⟩ := hlow hn0
        have hfit' : Extract.msgFits (Fin.ofNat 4 (n - 1))
            (.pair (evalWithAnswerFn answers (layerPairP w index (Fin.ofNat 4 n) digits)).1
              (evalWithAnswerFn answers (layerPairP w index (Fin.ofNat 4 n) digits)).2) := trivial
        rcases layersBC_wots_walk answers w index hidx n (by omega) (by omega) _ hfit' hrest with
          hprim | ⟨hgood, hmsg⟩
        · exact Or.inl (hprim.mono (entriesOf_mono hqR))
        · rw [Extract.honestMsg_lower answers index n (by omega) (by omega)] at hmsg
          have hpair : evalWithAnswerFn answers (layerPairP w index (Fin.ofNat 4 n) digits) =
              Extract.honestPair answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2 := by
            simp only [WCT9.LayerMsg.pair.injEq] at hmsg
            exact Prod.ext hmsg.1 hmsg.2
          exact finish (layerPair_wots answers w index (Fin.ofNat 4 n) msg digits hidx (by rw [hval]; exact hn0)
            hfit hframe _ henc hqP hpair) hgood
theorem verifyP_walk_wots (answers : Answers) (m : Message) (pk : Digest) (w : WBytes)
    (hpk : pk = Extract.honestRoot answers 0 0)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true) :
    ∃ N : HashOutput, (wdc w).toNat < WCT9.digestVerifyWindow ∧
      evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N ∧
      (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : Spec.Domain) ∈ queried answers (verifyP m pk w) ∧
      Shaped N w ∧
      (WotsPrimitiveSrc answers (entriesOf answers (queried answers (verifyP m pk w))) ∨
       ((∀ l : Layer, BC.GoodZ answers w (WCT9.digestIndex N) l) ∧
          evalWithAnswerFn answers
              (recoverFtsP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) N) =
            Extract.honestTop answers (WCT9.digestIndex N) ∧
          ∀ q ∈ queried answers (recoverFtsP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) N),
            q ∈ queried answers (verifyP m pk w))) := by
  classical
  obtain ⟨N, hdc, hN, hdq, hS, hlay, hqF, hqL⟩ := WctExtract.verifyP_walk_wct answers m pk w hv
  refine ⟨N, hdc, hN, hdq, hS, ?_⟩
  have hidx : WCT9.digestIndex N < 2 ^ 31 := Nat.mod_lt _ (by norm_num)
  rcases layersBC_wots_walk answers w (WCT9.digestIndex N) hidx 4 (by decide) le_rfl (.pair _ _) trivial (hpk ▸ hlay) with
    hprim | ⟨hgood, hroot⟩
  · exact Or.inl (hprim.mono (entriesOf_mono hqL))
  · right
    refine ⟨fun l => hgood l l.isLt, ?_, hqF⟩
    rw [show (4 - 1 : Nat) = 3 from rfl, Extract.honestMsg_three] at hroot
    simp only [WCT9.LayerMsg.pair.injEq] at hroot
    exact Prod.ext hroot.1 hroot.2
def FtsPos : Extract.Pos → Prop
  | .wctChain .. => True
  | .wctLeaf .. => True
  | .wctNode .. => True
  | _ => False
/-- C4: the query also has the position's length (`Pos.hdr_injective` needs it). -/
def FtsQueryPos (actual : HashInput) : Prop :=
  ∃ pos : Extract.Pos, pos.Bounded ∧ PosSource pos ∧ FtsPos pos ∧ actual.length = pos.len ∧
    Extract.canonicalHeader (Extract.hdrBlock actual) = bytesLE 16 pos.hdr
theorem ftsQueryPos_of_hdr {actual : HashInput} {pos : Extract.Pos} (hb : pos.Bounded) (hsrc : PosSource pos)
    (hfts : FtsPos pos) (hlen : actual.length = pos.len) (hdr : Extract.hdrBlock actual = bytesLE 16 pos.hdr) :
    FtsQueryPos actual :=
  ⟨pos, hb, hsrc, hfts, hlen, by rw [hdr, Extract.Pos.canonicalHeader_eq hb]⟩
theorem chain_queries_pos (answers : Answers) (index coord child t d : Nat) (hd : d ≤ 4) (p0 : Digest)
    (pb : BitVec 64) (p1 v : Digest) (hb : index < 2 ^ 31 ∧ coord < 9 ∧ child < 128 ∧ t < 6) :
    ∀ q ∈ queried answers (wctChainP index coord child t (4 - d) d p0 pb p1 v),
      ∃ actual, q = .inl (.inr actual) ∧ FtsQueryPos actual := by
  intro q hq
  rw [wctChainP_eq_hashPath, queried_hashPath] at hq
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hq
  have hs := List.mem_range.mp hs
  obtain ⟨hi, hc, hj, ht⟩ := hb
  have hbd : (Extract.Pos.wctChain index coord child t (4 - d + s)).Bounded := ⟨hi, hc, hj, ht, by omega⟩
  refine ⟨_, rfl, .wctChain index coord child t (4 - d + s), hbd, ⟨hi, hc, hj, ht, by omega⟩, trivial, ?_, ?_⟩
  · simp only [pathInput, wctChainInputP_block4, pad64_block4, Extract.Pos.len]
    simp [block4, SphincsSecurity.bytesLE_length]
  simp only [pathInput, wctChainInputP_block4, pad64_block4, hdrBlock_block4W, Extract.Pos.hdr]
  rw [WctExtract.canonicalHeader_ftsChainHeaderP]
  have hk := Extract.Pos.canonicalHeader_eq hbd
  simp only [Extract.Pos.hdr] at hk
  exact hk
theorem leaf_queries_pos (answers : Answers) (index coord child : Nat) (pad : Digest) (ends : List Digest)
    (hb : index < 2 ^ 31 ∧ coord < 9 ∧ child < 128) (hends : ends.length = 6) :
    ∀ q ∈ queried answers (WCT9.leafHashP index coord child pad ends),
      ∃ actual, q = .inl (.inr actual) ∧ FtsQueryPos actual := by
  intro q hq
  rw [WctExtract.leafHashP_eq_shortHash, queried_shortHash] at hq
  rw [List.mem_singleton] at hq
  subst hq
  obtain ⟨hi, hc, hj⟩ := hb
  refine ⟨_, rfl, ftsQueryPos_of_hdr (pos := .wctLeaf index coord child) ⟨hi, hc, hj⟩ ⟨hi, hc, hj⟩ trivial ?_ ?_⟩
  · unfold Extract.wctLeafInputP
    rw [Extract.pad64_length_of_mod (by rw [Extract.listInput_length]; simp [hends]), Extract.listInput_length]
    simp [hends, Extract.Pos.len]
  rw [Extract.hdrBlock_wctLeafInputP]
  rfl
theorem merkle_queries_pos (answers : Answers) (index : Nat) (c : WCT9.Coord) (j : Nat) (hj : j < 128)
    (hidx : index < 2 ^ 31) (path pads : Nat → Digest) (hpads : Nat → BitVec 64) (leaf : Digest) :
    ∀ q ∈ queried answers (hashPath (merkleInputH 3 (WCT9.nodeLayer c.val) index 7 j path pads hpads) 5 leaf),
      ∃ actual, q = .inl (.inr actual) ∧ FtsQueryPos actual := by
  intro q hq
  rw [queried_hashPath] at hq
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hq
  have hs := List.mem_range.mp hs
  have hn : j / 2 ^ (s + 1) < 2 ^ (7 - s - 1) := by
    have := Correctness.div_pow_bound (node := j) (height := 7) (start := 0) (level := s + 1) (by omega)
      (by norm_num; omega)
    simpa [Nat.sub_sub] using this
  have hbd : (Extract.Pos.wctNode index c.val s (j / 2 ^ (s + 1))).Bounded := ⟨hidx, c.isLt, by omega, hn⟩
  refine ⟨_, rfl, .wctNode index c.val s (j / 2 ^ (s + 1)), hbd, hbd, trivial, ?_, ?_⟩
  · simp [pathInput, merkleInputH, nodeInputPH, block4, SphincsSecurity.bytesLE_length, pad64,
      Extract.Pos.len]
  have he : (Extract.Pos.wctNode index c.val s (j / 2 ^ (s + 1))).hdr =
      nodeTweak 3 (WCT9.nodeLayer c.val) index (2 ^ (7 - s - 1) + j / 2 ^ (s + 1)) := rfl
  have hk := Extract.Pos.canonicalHeader_eq hbd
  rw [he] at hk
  rw [he, pathInput, WctExtract.hdrBlock_merkleInputH, WctExtract.canonicalHeader_withHigh, hk]
theorem top_queries_pos (answers : Answers) (index : Nat) (c : WCT9.Coord) (j : Nat) (hj : j < 128)
    (hidx : index < 2 ^ 31) (l z r : Digest) :
    ∀ q ∈ queried answers (WCT9.wctTopHash c.val index (2 + j / 2 ^ 6) l z r),
      ∃ actual, q = .inl (.inr actual) ∧ FtsQueryPos actual := by
  intro q hq
  have hqry : queried answers (WCT9.wctTopHash c.val index (2 + j / 2 ^ 6) l z r) =
      [.inl (.inr (pad64 (WCT9.wctTopInput c.val index (2 + j / 2 ^ 6) l z r)))] := rfl
  rw [hqry, List.mem_singleton] at hq
  subst hq
  have hn : j / 2 ^ 6 < 2 := (Nat.div_lt_iff_lt_mul (by positivity)).mpr (by norm_num; omega)
  have hbd : (Extract.Pos.wctNode index c.val 5 (j / 2 ^ 6)).Bounded :=
    ⟨hidx, c.isLt, by norm_num, by norm_num; omega⟩
  refine ⟨_, rfl, ftsQueryPos_of_hdr (pos := .wctNode index c.val 5 (j / 2 ^ 6)) hbd hbd trivial ?_ ?_⟩
  · rw [wctTopInput_block4, pad64_block4]
    simp [block4, SphincsSecurity.bytesLE_length, Extract.Pos.len]
  rw [wctTopInput_block4, pad64_block4, hdrBlock_block4W]
  rfl
theorem coord_queries_pos (answers : Answers) (N : HashOutput) (w : WBytes) (c : WCT9.Coord)
    (prev : Digest × Digest) :
    ∀ q ∈ queried answers
        (recoverCoordinateP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) N c prev),
      ∃ actual, q = .inl (.inr actual) ∧ FtsQueryPos actual := by
  intro q hq
  have hidx : WCT9.digestIndex N < 2 ^ 31 := Nat.mod_lt _ (by norm_num)
  have hj := (WCT9.child N c).isLt
  rw [recoverCoordinateP_dec] at hq
  rw [queried_bind, queried_bind, queried_bind, queried_bind] at hq
  rcases List.mem_append.mp hq with hq | hq
  · rw [queried_mapM] at hq
    obtain ⟨t, -, hq⟩ := List.mem_flatMap.mp hq
    exact chain_queries_pos answers (WCT9.digestIndex N) c.val (WCT9.child N c).val t.val
      (WCT9.wordDigit (WCT9.rank N c) t) (WCT9.wordDigit_le_four _ t) _ _ _ _ ⟨hidx, c.isLt, hj, t.isLt⟩ q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact leaf_queries_pos answers (WCT9.digestIndex N) c.val (WCT9.child N c).val _ _ ⟨hidx, c.isLt, hj⟩
      (by rw [SigGolfCandidate.T3.Correctness.eval_mapM]; simp) q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact merkle_queries_pos answers (WCT9.digestIndex N) c (WCT9.child N c).val hj hidx _ _ _ _ q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact top_queries_pos answers (WCT9.digestIndex N) c (WCT9.child N c).val hj hidx _ _ _ q hq
  · simp [queried_pure] at hq
theorem fts_queries_pos (answers : Answers) (N : HashOutput) (w : WBytes) :
    ∀ q ∈ queried answers (recoverFtsP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) N),
      ∃ actual, q = .inl (.inr actual) ∧ FtsQueryPos actual := by
  intro q hq
  rw [WctExtract.recoverFtsP_nfold, queried_bind] at hq
  rcases List.mem_append.mp hq with hq | hq
  · obtain ⟨c, -, hq⟩ := WctExtract.queried_nfold answers _ _ 9 le_rfl q hq
    exact coord_queries_pos answers N w c _ q hq
  · simp [queried_pure] at hq
/-! C3 (FULL): an FTS query cannot decode as a lower/top leaf. The leaf key keeps only the low header word, and every
FTS header differs from every leaf tweak in its low word (marker and tag). -/
theorem canonicalHeader_take8 {hdr : HashInput} (h : 8 ≤ hdr.length) :
    (Extract.canonicalHeader hdr).take 8 = hdr.take 8 := by
  unfold SigGolfCandidate.T3M.Extract.canonicalHeader
  split
  · exact List.take_left' (by simp; omega)
  · rfl
theorem take8_bytesLE16 (a : BitVec 128) : (bytesLE 16 a).take 8 = bytesLE 8 (a.extractLsb' 0 64) := by
  have ha : a = a.extractLsb' 64 64 ++ a.extractLsb' 0 64 :=
    (BitVec.extractLsb'_append_extractLsb' (w := 64) (len := 64) (x := a)).symm
  conv_lhs => rw [ha]
  rw [SigGolfCandidate.T3M.Extract.bytesLE_header_words, List.take_left' (SphincsSecurity.bytesLE_length 8 _)]
/-- C4: the header of an FTS position (chain, leaf or node; the FTS recompute never queries the forest) has its low
word in `[2 ^ 16, 2 ^ 58)`: above every top label (coordinate nibble `coord + 1`) and below every WOTS leaf tweak
(type byte 193). -/
theorem ftsPos_low {p : Extract.Pos} (hb : p.Bounded) (h : FtsPos p) :
    2 ^ 16 ≤ tweakLow p.hdr ∧ tweakLow p.hdr < 2 ^ 58 := by
  cases p with
  | wctChain index coord child t step =>
      obtain ⟨-, hk, -, -, -⟩ := hb
      have h1 := WCT9.ftsChainLow_ge (show coord < 15 by omega) index child t step
      have h2 := WCT9.ftsChainLow_lt index coord child t step
      simp only [Extract.Pos.hdr, WCT9.ftsChainHeader]
      rw [Extract.tweakLow_eq_low, WCT9.ftsChainHeaderP_low, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (lt_trans h2 (by norm_num))]
      exact ⟨h1, h2⟩
  | wctLeaf index coord child =>
      obtain ⟨-, hk, -⟩ := hb
      have h1 := WCT9.ftsLeafLow_ge (show coord < 15 by omega) index child
      have h2 := WCT9.ftsLeafLow_lt index coord child
      simp only [Extract.Pos.hdr, WCT9.ftsLeafHeader]
      rw [append64_lowNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_trans h2 (by norm_num))]
      exact ⟨h1, h2⟩
  | wctNode index coord level nd =>
      obtain ⟨-, hk, -, -⟩ := hb
      have hlow := WCT9.wctNodeHeader_toNat hk index (2 ^ (7 - level - 1) + nd)
      have hge := WCT9.ftsLeafLow_ge (show coord < 15 by omega) index 0
      have hlt := WCT9.ftsLeafLow_lt index coord 0
      have hgeN : 2 ^ 16 ≤ WCT9.ftsNodeLowN index coord (2 ^ (7 - level - 1) + nd) := by
        rw [WCT9.ftsNodeLowN_eq, Nat.mod_eq_of_lt (show coord + 1 < 16 by omega)]; omega
      have hltN := WCT9.ftsNodeLowN_lt index coord (2 ^ (7 - level - 1) + nd)
      simp only [Extract.Pos.hdr]
      unfold tweakLow
      rw [hlow]
      split_ifs <;> omega
  | _ => exact h.elim
theorem structuralHitSrc_of_fts_hitIn (answers : Answers) (N : HashOutput) (w : WBytes)
    (h : Extract.HitIn answers
      (queried answers (recoverFtsP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) N))) :
    StructuralHitSrc answers (entriesOf answers
      (queried answers (recoverFtsP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) N))) := by
  obtain ⟨pos, actual, hb, hq, hh, hs⟩ := h
  obtain ⟨actual', hqe, pos', hb', hsrc', hfts', hlenQ, hdr'⟩ := fts_queries_pos answers N w _ hq
  have hae : actual = actual' := by simpa using hqe
  subst hae
  have hkey : Extract.hdrKey actual = bytesLE 16 pos.hdr := hs.2.trans (Extract.hdrKey_honestInput answers hb)
  have hlen : actual.length = pos.len := hs.1.trans (Extract.honestInput_length answers pos)
  have h16 : 8 ≤ (Extract.hdrBlock actual).length := by
    have : 64 ≤ actual.length := by
      rw [hlen]; cases pos <;> simp only [Extract.Pos.len] <;> (try split) <;> omega
    simp [Extract.hdrBlock]; omega
  -- C4: the actual header's low word is the FTS position's, in `[2 ^ 16, 2 ^ 58)`.
  have h8 : readLE ((Extract.hdrBlock actual).take 8) = tweakLow pos'.hdr := by
    rw [← canonicalHeader_take8 h16, hdr', Extract.readLE_take8]
  have hlo := ftsPos_low hb' hfts'
  by_cases hl : actual.length = 704 ∨ actual.length = 896
  · exfalso
    rw [hlenQ] at hl
    cases pos' <;> (try exact hfts'.elim) <;> simp [Extract.Pos.len] at hl
  · have hT : ¬ (actual.length = 64 ∧ Extract.TopLow (Extract.hdrBlock actual)) := by
      rintro ⟨-, ht⟩
      unfold Extract.TopLow at ht
      rw [h8] at ht
      omega
    have hkey' : Extract.hdrKey actual = bytesLE 16 pos'.hdr := by
      rw [Extract.hdrKey_of_not_leafLen hl hT, hdr']
    have hhdr : pos.hdr = pos'.hdr := bytesLE_injective (hkey.symm.trans hkey')
    have hpos : pos = pos' := Extract.Pos.hdr_injective hb hb' (hlen.symm.trans hlenQ) hhdr
    subst hpos
    refine ⟨pos, actual, _, mem_entriesOf hq, Extract.posOf_key_eq hb hlen hkey, hb, hsrc', ?_, hh⟩
    cases pos <;> first | trivial | exact hfts'.elim
theorem fts_structural (answers : Answers) (N : HashOutput) (w : WBytes) (hS : Shaped N w)
    (hrun : evalWithAnswerFn answers
        (recoverFtsP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) N) =
      Extract.honestTop answers (WCT9.digestIndex N)) :
    StructuralHitSrc answers (entriesOf answers (queried answers
        (recoverFtsP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) N))) ∨
      WctExtract.WctHonest answers N w :=
  (WctExtract.wct_extract answers N w hS hrun).imp_left (structuralHitSrc_of_fts_hitIn answers N w)
theorem verifyP_wots_cases_src (answers : Answers) (m : Message) (pk : Digest) (w : WBytes)
    (hpk : pk = Extract.honestRoot answers 0 0)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true) :
    ∃ N : HashOutput, (wdc w).toNat < WCT9.digestVerifyWindow ∧
      evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N ∧
      (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : Spec.Domain) ∈ queried answers (verifyP m pk w) ∧
      Shaped N w ∧
      (WotsPrimitiveSrc answers (entriesOf answers (queried answers (verifyP m pk w))) ∨
       ((∀ l : Layer, BC.GoodZ answers w (WCT9.digestIndex N) l) ∧ WctExtract.WctHonest answers N w)) := by
  classical
  obtain ⟨N, hdc, hN, hdq, hS, hcase⟩ := verifyP_walk_wots answers m pk w hpk hv
  refine ⟨N, hdc, hN, hdq, hS, ?_⟩
  rcases hcase with hprim | ⟨hgood, hR, hqV⟩
  · exact Or.inl hprim
  rcases fts_structural answers N w hS hR with hhit | hshape
  · exact Or.inl (Or.inr (Or.inl (structuralHitSrc_mono hhit (entriesOf_mono hqV))))
  · exact Or.inr ⟨hgood, hshape⟩
end ClaudeWCT.W9.T3.Security.WotsExtract
namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.W9.T3M (wrho wdc)
open ClaudeWCT.W9.T3.Security.WotsExtract
open SigGolfCandidate.T3.Security.Wots (entriesOf)
open SigGolfCandidate.T3.Correctness (Answers)
end ClaudeWCT.W9.T3.Security.Wots

namespace ClaudeWCT.W9.T3.Security.CanonicalExtract
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.Wots (LeafAddr ChainAddr Entry low entriesOf)
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate.T3.Security.WotsExtract (routeLeaf)
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open ClaudeWCT.W9.T3M.WctExtract (wctChainP_eq_hashPath wctChainInputP_block4 queried_hashPath queried_mapM
  hdrBlock_block4W leafHash_eq_shortHash hdrBlock_merkleInput recoverCoordinateP_dec wctTopInput_block4)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.W9.T3M (wrho wdc layerP)
open SigGolfCandidate.T3.Security.WotsExtract (SourceLeaf SourceChain mem_entriesOf entriesOf_mono)
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (bytesLE bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem layersCanonicalBC_wots_walk (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (w : WBytes) (index : Nat) (hidx : index < 2 ^ 31)
    (hfitRef : ∀ lay, Extract.msgFits lay (messages (routeLeaf index lay)))
    (hlower : ∀ n, 1 ≤ n → n < 4 → messages (routeLeaf index (Fin.ofNat 4 (n-1))) =
      WCT9.LayerMsg.pair
        (Extract.honestPair answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2).1
        (Extract.honestPair answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2).2) :
    ∀ n, 1 ≤ n → n ≤ 4 → ∀ msg : WCT9.LayerMsg, Extract.msgFits (Fin.ofNat 4 (n - 1)) msg →
    evalWithAnswerFn answers (layersCanonicalBC w index n msg) = some (Extract.honestRoot answers 0 0) →
    WotsPrimitiveSrc answers messages (entriesOf answers (queried answers (layersCanonicalBC w index n msg))) ∨
    ((∀ l : Layer, l.val < n → Good answers messages w index l) ∧
      msg = messages (routeLeaf index (Fin.ofNat 4 (n - 1))))
  | 0, h1, _, _, _, _ => absurd h1 (by decide)
  | n + 1, _, hn, msg, hfit, h => by
      classical
      obtain ⟨digits, hframe, henc, htop, hlow⟩ := Extract.layersCanonicalBC_succ_split answers w index n msg _ h
      have hval : (Fin.ofNat 4 n : Layer).val = n := Extract.ofNat_val n (by omega)
      simp only [Nat.add_sub_cancel] at hfit ⊢
      have finish : WotsPrimitiveSrc answers messages (entriesOf answers (queried answers (layersCanonicalBC w index (n + 1) msg))) ∨
          (msg = messages (routeLeaf index (Fin.ofNat 4 n)) ∧ Good answers messages w index (Fin.ofNat 4 n)) →
          (∀ l : Layer, l.val < n → Good answers messages w index l) →
          WotsPrimitiveSrc answers messages (entriesOf answers (queried answers (layersCanonicalBC w index (n + 1) msg))) ∨
          ((∀ l : Layer, l.val < n + 1 → Good answers messages w index l) ∧
            msg = messages (routeLeaf index (Fin.ofNat 4 n))) := by
        intro hx hgood
        rcases hx with hprim | ⟨hmsg, hgoodn⟩
        · exact Or.inl hprim
        · right
          refine ⟨fun l hl => ?_, hmsg⟩
          by_cases hle : l.val < n
          · exact hgood l hle
          · have hl : l = Fin.ofNat 4 n := Fin.ext (by rw [hval]; omega)
            subst hl
            exact hgoodn
      by_cases hn0 : n = 0
      · subst hn0
        obtain ⟨hout, hq⟩ := htop rfl
        have hroot : evalWithAnswerFn answers (layerP w index (Fin.ofNat 4 0) digits) =
            Extract.honestRoot answers (Fin.ofNat 4 0) (route index (Fin.ofNat 4 0)).2 := by
          rw [hout, show (Fin.ofNat 4 0 : Layer) = 0 from rfl, route_top_tree index hidx]
        exact finish (layer_wots (messages := messages) answers w index (Fin.ofNat 4 0) msg digits hidx rfl hfit (hfitRef _) hframe _ henc hq hroot)
          (fun l hl => absurd hl (by omega))
      · obtain ⟨hrest, hqP, hqR⟩ := hlow hn0
        have hfit' : Extract.msgFits (Fin.ofNat 4 (n - 1))
            (.pair (evalWithAnswerFn answers (layerPairP w index (Fin.ofNat 4 n) digits)).1
              (evalWithAnswerFn answers (layerPairP w index (Fin.ofNat 4 n) digits)).2) := trivial
        rcases layersCanonicalBC_wots_walk answers messages w index hidx hfitRef hlower n (by omega) (by omega) _ hfit' hrest with
          hprim | ⟨hgood, hmsg⟩
        · exact Or.inl (hprim.mono (entriesOf_mono hqR))
        · rw [hlower n (by omega) (by omega)] at hmsg
          have hpair : evalWithAnswerFn answers (layerPairP w index (Fin.ofNat 4 n) digits) =
              Extract.honestPair answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2 := by
            simp only [WCT9.LayerMsg.pair.injEq] at hmsg
            exact Prod.ext hmsg.1 hmsg.2
          exact finish (layerPair_wots (messages := messages) answers w index (Fin.ofNat 4 n) msg digits hidx (by rw [hval]; exact hn0)
            hfit (hfitRef _) hframe _ henc hqP hpair) hgood

#print axioms layersCanonicalBC_wots_walk
end ClaudeWCT.W9.T3.Security.CanonicalExtract
