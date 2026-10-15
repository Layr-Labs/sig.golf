import SigGolfCandidate.T3M.Extract.FtsPart3
import SigGolfCandidate.T3M.Extract.VerifyP

section
namespace SigGolfCandidate.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3 SecurityInputs SecurityExtraction
open Correctness (Answers)
open SphincsSecurity (bytesLE bytesLE_injective)
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
theorem hdrBlock_honestInput (answers : Answers) (p : Pos) :
    hdrBlock (honestInput answers p) = bytesLE 16 p.hdr := by
  cases p with
  | chain lay tree lf i step =>
      simp only [honestInput, Pos.hdr, chainInput_padded, hdrBlock, chainInput_header]
  | leaf lay tree lf => simp only [honestInput, Pos.hdr]; rw [hdrBlock_leafInput]
  | node lay tree level nd =>
      simp only [honestInput, Pos.hdr]; rw [pad64_nodeInputP, nodeInputP, hdrBlock_block4]
  | forest index => simp only [honestInput, Pos.hdr, forestInput]; rw [hdrBlock_listInput]
  | ftsLeaf index coord lf =>
      simp only [honestInput, Pos.hdr]; rw [pad64_ftsLeafInputP, ftsLeafInputP, hdrBlock_block4]
  | ftsNode index coord level nd =>
      simp only [honestInput, Pos.hdr]
      rw [pad64_nodeInputP, nodeInputP, hdrBlock_block4, nodeTweak_other (by omega)]
theorem heap_lt {e x : Nat} (hx : x < 2 ^ e) (he : e ≤ 12) : 2 ^ e + x < 2 ^ 32 := by
  have : 2 ^ e ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) he
  have : (2 : Nat) ^ 12 = 4096 := by norm_num
  have : (2 : Nat) ^ 32 = 4294967296 := by norm_num
  omega
theorem heap_inj {e f x y : Nat} (hx : x < 2 ^ e) (hy : y < 2 ^ f) (h : 2 ^ e + x = 2 ^ f + y) : e = f ∧ x = y := by
  have key : ∀ {e f x y : Nat}, x < 2 ^ e → e < f → 2 ^ e + x < 2 ^ f + y := by
    intro e f x y hx hef
    have : 2 ^ (e + 1) ≤ 2 ^ f := Nat.pow_le_pow_right (by decide) hef
    rw [pow_succ] at this
    omega
  rcases Nat.lt_trichotomy e f with hlt | heq | hgt
  · exact absurd h (ne_of_lt (key hx hlt))
  · subst heq; exact ⟨rfl, by omega⟩
  · exact absurd h.symm (ne_of_lt (key hy hgt))
theorem Pos.hdr_view (p : Pos) (hb : p.Bounded) :
    (∀ lay tree lf i step, p = .chain lay tree lf i step → 128 ≤ tweakMarker p.hdr) ∧
    (∀ lay tree lf, p = .leaf lay tree lf →
      tweakMarker p.hdr = 1 ∧ tweakTag p.hdr = 2 ∧ tweakHigh p.hdr = 0) ∧
    (∀ lay tree level nd, p = .node lay tree level nd →
      (lay = 0 ∧ tweakMarker p.hdr = 64) ∨
        (lay ≠ 0 ∧ tweakMarker p.hdr = 1 ∧ tweakTag p.hdr = 2 ∧ 1 ≤ tweakHigh p.hdr)) ∧
    (∀ index, p = .forest index → tweakMarker p.hdr = 1 ∧ tweakTag p.hdr = 11) ∧
    (∀ index coord lf, p = .ftsLeaf index coord lf → tweakMarker p.hdr = 1 ∧ tweakTag p.hdr = 9) ∧
    (∀ index coord level nd, p = .ftsNode index coord level nd → tweakMarker p.hdr = 1 ∧ tweakTag p.hdr = 10) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro lay tree lf i step rfl; exact chainHeader_tweakMarker ..
  · rintro lay tree lf rfl; exact ⟨leafTweak_marker .., leafTweak_tag .., leafTweak_high ..⟩
  · rintro lay tree level nd rfl
    simp only [Pos.hdr]
    by_cases h0 : lay = 0
    · subst h0; exact Or.inl ⟨rfl, nodeTweak_top_marker ..⟩
    · have hv : lay.val ≠ 0 := fun h => h0 (Fin.ext h)
      have hlt := lay.isLt
      obtain ⟨_, _, hl, hnd⟩ := hb
      have hheap : 2 ^ (height lay - level - 1) + nd < 2 ^ 64 :=
        lt_trans (heap_lt hnd (le_trans (Nat.sub_le _ _) (le_trans (Nat.sub_le _ _) (height_le lay))))
          (by norm_num)
      refine Or.inr ⟨h0, nodeTweak_lower_marker hv hlt _ _, nodeTweak_lower_tag hv hlt _ _, ?_⟩
      rw [nodeTweak_hyper_high hlt, Nat.mod_eq_of_lt hheap]
      have := Nat.one_le_two_pow (n := height lay - level - 1)
      omega
  · rintro index rfl; exact ⟨header_marker .., by rw [Pos.hdr, header_tag]⟩
  · rintro index coord lf rfl; exact ⟨header_marker .., by rw [Pos.hdr, header_tag]⟩
  · rintro index coord level nd rfl; exact ⟨header_marker .., by rw [Pos.hdr, header_tag]⟩
theorem Pos.hdr_injective {p p' : Pos} (hb : p.Bounded) (hb' : p'.Bounded)
    (h : p.hdr = p'.hdr) : p = p' := by
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := Pos.hdr_view p hb
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := Pos.hdr_view p' hb'
  rw [h] at c1 c2 c3 c4 c5 c6
  cases p with
  | chain lay tree lf i step =>
      have e := c1 _ _ _ _ _ rfl
      cases p' with
      | chain lay' tree' lf' i' step' =>
          obtain ⟨ht, hf, hi, hs⟩ := hb
          obtain ⟨ht', hf', hi', hs'⟩ := hb'
          obtain ⟨hl, ht, hf, hi, hs⟩ := chainHeader_low_injective ht hf hi hs ht' hf' hi' hs'
            (congrArg (BitVec.extractLsb' 0 64) h)
          subst_vars; rfl
      | leaf => have := (d2 _ _ _ rfl).1; omega
      | node => rcases d3 _ _ _ _ rfl with ⟨_, hm⟩ | ⟨_, hm, _⟩ <;> omega
      | forest => have := (d4 _ rfl).1; omega
      | ftsLeaf => have := (d5 _ _ _ rfl).1; omega
      | ftsNode => have := (d6 _ _ _ _ rfl).1; omega
  | leaf lay tree lf =>
      obtain ⟨m1, t1, h1⟩ := c2 _ _ _ rfl
      cases p' with
      | chain => have := d1 _ _ _ _ _ rfl; omega
      | leaf lay' tree' lf' =>
          obtain ⟨hl, hr⟩ := hb
          obtain ⟨hl', hr'⟩ := hb'
          obtain ⟨a, b, c⟩ := leafTweak_injective hl hr hl' hr' h
          subst_vars; rfl
      | node => rcases d3 _ _ _ _ rfl with ⟨_, hm⟩ | ⟨_, _, _, hh⟩ <;> omega
      | forest => have := (d4 _ rfl).2; omega
      | ftsLeaf => have := (d5 _ _ _ rfl).2; omega
      | ftsNode => have := (d6 _ _ _ _ rfl).2; omega
  | node lay tree level nd =>
      have cv := c3 _ _ _ _ rfl
      cases p' with
      | chain => have := d1 _ _ _ _ _ rfl; rcases cv with ⟨_, hm⟩ | ⟨_, hm, _⟩ <;> omega
      | leaf => have := d2 _ _ _ rfl; rcases cv with ⟨_, hm⟩ | ⟨_, _, _, hh⟩ <;> omega
      | node lay' tree' level' nd' =>
          obtain ⟨ht, h0, hl, hnd⟩ := hb
          obtain ⟨ht', h0', hl', hnd'⟩ := hb'
          simp only [Pos.hdr] at h
          have hh := heap_lt hnd (le_trans (Nat.sub_le _ _) (le_trans (Nat.sub_le _ _) (height_le lay)))
          have hh' := heap_lt hnd' (le_trans (Nat.sub_le _ _) (le_trans (Nat.sub_le _ _) (height_le lay')))
          obtain ⟨hlay, htree, hheap⟩ := nodeTweak_hyper_injective lay.isLt lay'.isLt ht ht'
            (fun e => h0 (Fin.ext e)) (fun e => h0' (Fin.ext e))
            (lt_trans hh (by norm_num)) (lt_trans hh' (by norm_num)) h
          have hla : lay = lay' := Fin.ext hlay
          subst hla htree
          obtain ⟨e, x⟩ := heap_inj hnd hnd' hheap
          subst x
          have : level = level' := by omega
          subst this; rfl
      | forest => have := d4 _ rfl; rcases cv with ⟨_, hm⟩ | ⟨_, _, ht, _⟩ <;> omega
      | ftsLeaf => have := d5 _ _ _ rfl; rcases cv with ⟨_, hm⟩ | ⟨_, _, ht, _⟩ <;> omega
      | ftsNode => have := d6 _ _ _ _ rfl; rcases cv with ⟨_, hm⟩ | ⟨_, _, ht, _⟩ <;> omega
  | forest index =>
      obtain ⟨m1, t1⟩ := c4 _ rfl
      cases p' with
      | chain => have := d1 _ _ _ _ _ rfl; omega
      | leaf => have := (d2 _ _ _ rfl).2.1; omega
      | node => rcases d3 _ _ _ _ rfl with ⟨_, hm⟩ | ⟨_, _, ht, _⟩ <;> omega
      | forest index' =>
          simp only [Pos.hdr] at h
          obtain ⟨-, -, e, -, -⟩ := header_injective (by decide) (by decide) hb (by decide) (by decide)
            (by decide) (by decide) hb' (by decide) (by decide) h
          rw [e]
      | ftsLeaf => have := (d5 _ _ _ rfl).2; omega
      | ftsNode => have := (d6 _ _ _ _ rfl).2; omega
  | ftsLeaf index coord lf =>
      obtain ⟨m1, t1⟩ := c5 _ _ _ rfl
      cases p' with
      | chain => have := d1 _ _ _ _ _ rfl; omega
      | leaf => have := (d2 _ _ _ rfl).2.1; omega
      | node => rcases d3 _ _ _ _ rfl with ⟨_, hm⟩ | ⟨_, _, ht, _⟩ <;> omega
      | forest => have := (d4 _ rfl).2; omega
      | ftsLeaf index' coord' lf' =>
          simp only [Pos.hdr] at h
          obtain ⟨hc, hi, hl⟩ := hb
          obtain ⟨hc', hi', hl'⟩ := hb'
          obtain ⟨-, e1, e2, -, e3⟩ := header_injective (by decide) hc hi (by decide) hl
            (by decide) hc' hi' (by decide) hl' h
          rw [e1, e2, e3]
      | ftsNode => have := (d6 _ _ _ _ rfl).2; omega
  | ftsNode index coord level nd =>
      obtain ⟨m1, t1⟩ := c6 _ _ _ _ rfl
      cases p' with
      | chain => have := d1 _ _ _ _ _ rfl; omega
      | leaf => have := (d2 _ _ _ rfl).2.1; omega
      | node => rcases d3 _ _ _ _ rfl with ⟨_, hm⟩ | ⟨_, _, ht, _⟩ <;> omega
      | forest => have := (d4 _ rfl).2; omega
      | ftsLeaf => have := (d5 _ _ _ rfl).2; omega
      | ftsNode index' coord' level' nd' =>
          simp only [Pos.hdr] at h
          obtain ⟨hc, hi, hl, hnd⟩ := hb
          obtain ⟨hc', hi', hl', hnd'⟩ := hb'
          obtain ⟨-, e1, e2, -, e3⟩ := header_injective (by decide) hc hi (by decide) (heap_lt hnd (by omega))
            (by decide) hc' hi' (by decide) (heap_lt hnd' (by omega)) h
          subst e1 e2
          obtain ⟨e, x⟩ := heap_inj hnd hnd' e3
          subst x
          have : level = level' := by omega
          subst this; rfl
theorem Pos.canonicalHeader_eq {p : Pos} (hb : p.Bounded) :
    canonicalHeader (bytesLE 16 p.hdr) = bytesLE 16 p.hdr := by
  cases p with
  | chain lay tree leaf i step =>
      exact canonicalHeader_high_zero _
        (T3M.chainHeader_high_zero lay tree leaf i step hb.1 hb.2.1 hb.2.2.1 hb.2.2.2)
  | _ =>
      apply canonicalHeader_marker_ne
      have hv := Pos.hdr_view _ hb
      first
        | (have := hv.2.1 _ _ _ rfl; exact lt_of_eq_of_lt this.1 (by decide))
        | (rcases hv.2.2.1 _ _ _ _ rfl with ⟨_, hm⟩ | ⟨_, hm, _⟩ <;>
            exact lt_of_eq_of_lt hm (by decide))
        | (have := hv.2.2.2.1 _ rfl; exact lt_of_eq_of_lt this.1 (by decide))
        | (have := hv.2.2.2.2.1 _ _ _ rfl; exact lt_of_eq_of_lt this.1 (by decide))
        | (have := hv.2.2.2.2.2 _ _ _ _ rfl; exact lt_of_eq_of_lt this.1 (by decide))
noncomputable def posOf (input : HashInput) : Option Pos := by
  classical
  exact if h : ∃ p : Pos, p.Bounded ∧ canonicalHeader (hdrBlock input) = bytesLE 16 p.hdr
    then some (Classical.choose h) else none
theorem posOf_key_eq {input : HashInput} {p : Pos} (hb : p.Bounded)
    (h : canonicalHeader (hdrBlock input) = bytesLE 16 p.hdr) :
    posOf input = some p := by
  classical
  have hex : ∃ p : Pos, p.Bounded ∧ canonicalHeader (hdrBlock input) = bytesLE 16 p.hdr := ⟨p, hb, h⟩
  unfold posOf
  rw [dif_pos hex]
  have hs := Classical.choose_spec hex
  exact congrArg some (Pos.hdr_injective hs.1 hb (bytesLE_injective (hs.2.symm.trans h)))
theorem posOf_eq {input : HashInput} {p : Pos} (hb : p.Bounded)
    (h : hdrBlock input = bytesLE 16 p.hdr) : posOf input = some p := by
  apply posOf_key_eq hb
  rw [h, Pos.canonicalHeader_eq hb]
theorem hitIn_posOf {answers : Answers} {qs : List Spec.Domain} (h : HitIn answers qs) :
    ∃ pos actual, pos.Bounded ∧ .inl (.inr actual) ∈ qs ∧ posOf actual = some pos ∧
      HashHit answers (honestInput answers pos) actual := by
  obtain ⟨pos, actual, hb, hq, hh, hs⟩ := h
  refine ⟨pos, actual, hb, hq, posOf_key_eq hb ?_, hh⟩
  rw [hs, hdrBlock_honestInput, Pos.canonicalHeader_eq hb]
end SigGolfCandidate.T3M.Extract
end
section
end
section
namespace SigGolfCandidate.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3 SecurityExtraction
open Correctness (Answers)
theorem ftsExtractSpecN_FtsShaped : FtsExtractSpecN FtsExtract.FtsShaped :=
  fun answers N w hS hrun => FtsExtract.ftsExtractSpecN_holds answers N w hS hrun
theorem verifyP_extract_full (answers : Answers) (m : Message) (pk : Digest) (w : WBytes)
    (hpk : pk = honestRoot answers 0 0)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true) :
    ∃ N : HashOutput, (wdc w).toNat < attemptLimit ∧
      evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N ∧
      (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : Spec.Domain) ∈ queried answers (verifyP m pk w) ∧
      Shaped N w ∧
      (HitIn answers (queried answers (verifyP m pk w)) ∨
       (∃ lay : Layer, Diverge answers w (N.toNat % 2 ^ 31) lay (queried answers (verifyP m pk w)) ∧
          ∀ l : Layer, l.val < lay.val → Good answers w (N.toNat % 2 ^ 31) l) ∨
       ((∀ l : Layer, Good answers w (N.toNat % 2 ^ 31) l) ∧ FtsExtract.FtsShaped answers N w)) :=
  verifyP_extract_normal ftsExtractSpecN_FtsShaped answers m pk w hpk hv
end SigGolfCandidate.T3M.Extract
end
section
end
