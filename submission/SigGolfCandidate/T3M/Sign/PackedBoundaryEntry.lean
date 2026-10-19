import SigGolfCandidate.T3M.Sign.PackedLowTree
import SigGolfCandidate.T3M.SigCodec
import SigGolfCandidate.T3M.Search.BCCounterSearch
import SigGolfCandidate.T3M.Sign.Kernels


section









namespace SigGolfCandidate.T3M.Sign.Packed
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest counterLimit buildLeaf)
open Keygen (LeafArgs LeafW leafRegs)
def L0W (A : Nat) : Prop :=
  ¬ (SIG ≤ A ∧ A < SIG + 2192) ∧ ¬ (SIG + 3248 ≤ A ∧ A < SIG + 5616)
/-- Campaign T8D: the scratch of the top seed routines (COEFGEN/HORN register saves at `0x60000`, the 24 top
coefficients at `0x61000`). -/
def TopScr (A : Nat) : Prop := 0x60000 ≤ A ∧ A < 0x61180
/-- Cycle bound of one signature-only top leaf (prologue, COEFGEN, 52 x (HORN + chain), exit; campaign R6). -/
def topLeafC : Nat := 225300
end SigGolfCandidate.T3M.Sign.Packed
section
namespace SigGolfCandidate.T3M.Sign.Packed
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (M Digest Cache readDigest readLE mask header privateInput)
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN NODE NOUT LOUT LEAFPK MOUT ZDIG DUMMY TOP REGION)
def topSlot (leaf level : Nat) : Nat := 8192 - 2 ^ (13 - level) + (leaf / 2 ^ level ^^^ 1)
def topNode (cache : Bytes 131072) (leaf level : Nat) : Digest :=
  readDigest (List.ofFn fun i : Fin 16 =>
    (cacheDec cache).region ⟨(16 * topSlot leaf level + i.val) % 131040, Nat.mod_lt _ (by decide)⟩)
theorem topSlot_lt {leaf level : Nat} (hl : leaf < 4096) (h11 : level ≤ 11) :
    leaf / 2 ^ level ^^^ 1 < 2 ^ (12 - level) ∧ topSlot leaf level < 8190 := by
  have hp : 2 ^ level * 2 ^ (12 - level) = 2 ^ 12 := by rw [← Nat.pow_add]; congr 1; omega
  have hq : leaf / 2 ^ level < 2 ^ (12 - level) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    rw [Nat.mul_comm, hp]; omega
  have hx : leaf / 2 ^ level ^^^ 1 < 2 ^ (12 - level) :=
    Nat.xor_lt_two_pow hq (Nat.one_lt_two_pow (by omega))
  have h13 : 2 ^ (13 - level) = 2 * 2 ^ (12 - level) := by
    rw [show 13 - level = (12 - level) + 1 by omega, Nat.pow_succ]; ring
  have hc2 : 2 ≤ 2 ^ (12 - level) := by
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (show 1 ≤ 12 - level by omega); simpa using this
  refine ⟨hx, ?_⟩
  unfold topSlot
  have : 2 ^ (13 - level) ≤ 8192 := by
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (show 13 - level ≤ 13 by omega); simpa using this
  omega
theorem topNode_toNat (cache : Bytes 131072) (leaf level : Nat) (hq : topSlot leaf level < 8190) :
    (topNode cache leaf level).toNat = cache.toNat / 2 ^ (8 * (32 + 16 * topSlot leaf level)) % 2 ^ 128 := by
  have e : (List.ofFn fun i : Fin 16 =>
      (cacheDec cache).region ⟨(16 * topSlot leaf level + i.val) % 131040, Nat.mod_lt _ (by decide)⟩) =
      List.ofFn fun i : Fin 16 =>
        UInt8.ofNat (cache.toNat / 256 ^ (32 + 16 * topSlot leaf level) / 256 ^ i.val % 256) := by
    refine congrArg List.ofFn (funext fun i => ?_)
    show UInt8.ofNat (cache.toNat / 256 ^ (32 + (16 * topSlot leaf level + i.val) % 131040) % 256) = _
    rw [Nat.mod_eq_of_lt (show 16 * topSlot leaf level + i.val < 131040 by have := i.isLt; omega),
      ← Nat.add_assoc, pow_add, ← Nat.div_div_eq_div_mul]
  unfold topNode readDigest
  rw [e, readLE_ofFn_digits, BitVec.toNat_ofNat, show (256 : Nat) ^ 16 = 2 ^ 128 by norm_num,
    Nat.mod_mod, show (256 : Nat) ^ (32 + 16 * topSlot leaf level) = 2 ^ (8 * (32 + 16 * topSlot leaf level)) by
      rw [pow_mul]; norm_num]
theorem topNode_lo (cache : Bytes 131072) (leaf level : Nat) (hq : topSlot leaf level < 8190) :
    (topNode cache leaf level).extractLsb' 0 64 = cache.extractLsb' (64 * (2 * topSlot leaf level + 4)) 64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat, topNode_toNat cache leaf level hq,
    Nat.shiftRight_zero, Nat.shiftRight_eq_div_pow, Nat.mod_mod_of_dvd _ (by norm_num : 2 ^ 64 ∣ 2 ^ 128)]
  congr 3; ring
theorem topNode_hi (cache : Bytes 131072) (leaf level : Nat) (hq : topSlot leaf level < 8190) :
    (topNode cache leaf level).extractLsb' 64 64 = cache.extractLsb' (64 * (2 * topSlot leaf level + 5)) 64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat, topNode_toNat cache leaf level hq,
    Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num, Nat.mod_mul_right_div_self, Nat.mod_mod,
    Nat.div_div_eq_div_mul, ← Nat.pow_add]
  congr 3; ring
def TMW (X : Nat) : Prop :=
  X=PRIV+16 ∨ X=PRIV+24 ∨ (MOUT≤X ∧ X<MOUT+32) ∨ (SIG+3056≤X ∧ X<SIG+3248)
def tmRegs : List Reg := [.x6,.x7,.x10,.x11,.x12,.x20,.x22,.x23,.x24,.x28,.x29]
structure MInv (w0 : MachineState) (pre : List Digest) (w : MachineState) : Prop where
  pc : w.pc = if pre.length<12 then pcOf 1438 else pcOf 1482
  x22 : w.getReg .x22 = BitVec.ofNat 64 pre.length
  x24 : w.getReg .x24 = BitVec.ofNat 64 (SIG+3056+16*pre.length)
  x20 : w.getReg .x20 = BitVec.ofNat 64 (2^(12-pre.length))
  regs : RegsExcept w0 w tmRegs
  frame : Frame w0 w TMW
  out : DigsAt w (SIG+3056) pre
section masks
variable {sk : SecretKey} {cache : Bytes 131072} {w0 : MachineState} {leaf : Nat}
  (hb : Base sk cache w0) (hl : leaf<4096) (h14 : w0.getReg .x14=BitVec.ofNat 64 leaf)
include hb hl h14
theorem tp_mask_one {pre : List Digest} (hpl : pre.length<12) {w : MachineState}
    (hw : MInv w0 pre w) :
    TSim image sk w 44 51 1 1
      (mask pre.length (leaf/2^pre.length ^^^ 1) >>= fun m =>
        pure (topNode cache leaf pre.length ^^^ m))
      (fun d v => MInv w0 (pre++[d]) v) := by
  set lv := pre.length with hlv
  have g : ∀ r, r∉tmRegs → w.getReg r=w0.getReg r := fun r hr => hw.regs.get hr
  obtain ⟨hsib,hslot⟩ := topSlot_lt hl (show lv≤11 by omega)
  obtain ⟨t2,st2,t2pc,t2x10,t2x11,t2x12,t2x23,t2a,t2b,t2r,t2f⟩ :=
    blk1438_spec w (by rw [hw.pc, if_pos hpl]) leaf lv hl (by omega)
      (by rw [g _ (by decide),h14]) hw.x22
  have fr : ∀ X, X<2^64 → BaseA X → t2.getMem (BitVec.ofNat 64 X)=w0.getMem (BitVec.ofNat 64 X) :=
    fun X hX hba => (t2f.get hX (by unfold BaseA NeverW Search.TOP_DATA at hba; sg_omega)).trans
      (hw.frame.get hX (by unfold BaseA NeverW Search.TOP_DATA at hba; unfold TMW; sg_omega))
  have hq : hashInput t2=toQ (privateInput sk (.inl (header 13 0 0 lv ((leaf/2^lv ^^^ 1)/2)))) := by
    refine hashInput_toQ t2 _ 0 PRIV (privateInput_tweak_length _ _) t2x10 (by decide) (by decide) t2x11
      (by decide) ?_
    rw [wordsOf_privateInput_tweak,header_lo,header_hi,readWords_eight,
      fr PRIV (by decide) (by unfold BaseA; simp),fr (PRIV+8) (by decide) (by unfold BaseA; simp),t2a,t2b,
      fr (PRIV+32) (by decide) (by unfold BaseA; simp),fr (PRIV+40) (by decide) (by unfold BaseA; simp),
      fr (PRIV+48) (by decide) (by unfold BaseA; simp),fr (PRIV+56) (by decide) (by unfold BaseA; simp),
      hb.p0,hb.p8,hb.p32,hb.p40,hb.p48,hb.p56]
    rfl
  have hv : hashArgumentsValid t2=true :=
    hashArgs_const t2 PRIV 64 MOUT t2x10 t2x11 t2x12 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h5 : t2.getReg .x5=0 := by rw [t2r.get (by decide),g _ (by decide),hb.x5]
  refine (TSim.steps st2 (TSim.mask_bind (k:=25) (c:=25) (n:=0) (b:=0)
    (fetch_1456 t2 t2pc) h5 hv hq (fun a => ?_))).of_eq rfl rfl rfl rfl rfl
  have hwf := Frame.writeHash t2 a MOUT t2x12 (by decide)
  have upc : (writeHash t2 a).pc=pcOf 1457 := by rw [pc_writeHash,t2pc,pcOf_add4]
  have hmo : DigAt (writeHash t2 a) (MOUT+16*((leaf/2^lv ^^^ 1)%2))
      (if (leaf/2^lv ^^^ 1)%2=0 then a.extractLsb' 0 128 else a.extractLsb' 128 128) := by
    have hmod := Nat.mod_lt (leaf/2^lv ^^^ 1) (by decide : 0<2)
    by_cases hz : (leaf/2^lv ^^^ 1)%2=0
    · simpa [hz] using DigAt.writeHash_lo t2 a MOUT t2x12 (by decide)
    · have ho : (leaf/2^lv ^^^ 1)%2=1 := by omega
      simpa [ho] using DigAt.writeHash_hi t2 a MOUT t2x12 (by decide)
  have rw2 : RegsExcept w (writeHash t2 a) [.x6,.x7,.x10,.x11,.x12,.x23,.x28] := fun r hr => by
    rw [getReg_writeHash]; exact t2r.get hr
  have hlo2 : 2≤2^(12-lv) := by
    have := Nat.pow_le_pow_right (by norm_num : 0<2) (show 1≤12-lv by omega); simpa using this
  have hlo : 2^(12-lv)≤4096 := by
    have := Nat.pow_le_pow_right (by norm_num : 0<2) (show 12-lv≤12 by omega); simpa using this
  obtain ⟨t3,st3,t3pc,t3a,t3b,t3x24,t3x20,t3x22,t3r,t3f⟩ :=
    blk1457_spec (writeHash t2 a) upc (leaf/2^lv ^^^ 1) (2^(12-lv)) lv
      (SIG+3056+16*pre.length) hlo2 hlo hsib (by omega)
      (by sg_omega) (by sg_omega) (by sg_omega)
      (by rw [getReg_writeHash]; exact t2x23)
      (by rw [rw2.get (by decide)]; exact hw.x20)
      (by rw [rw2.get (by decide)]; exact hw.x22)
      (by rw [rw2.get (by decide)]; exact hw.x24)
      (by rw [getReg_writeHash]; exact t2x12)
  have hst : 2*2^(12-lv)=2^(13-lv) := by
    rw [show 13-lv=(12-lv)+1 by omega,Nat.pow_succ]; ring
  have hslot' : REGION+16*(8192-2*2^(12-lv)+(leaf/2^lv ^^^ 1))=REGION+8*(2*topSlot leaf lv) := by
    unfold topSlot; rw [hst]; ring
  have fsu := hw.frame.trans (t2f.trans hwf)
  have reg : ∀ k<16380, (writeHash t2 a).getMem (BitVec.ofNat 64 (REGION+8*k))=
      cache.extractLsb' (64*(k+4)) 64 := fun k hk => by
    rw [fsu.get (by sg_omega) (by unfold TMW; sg_omega)]; exact hb.region k hk
  refine TSim.pure_steps st3 ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [List.length_append,List.length_singleton] using t3pc
  · rw [t3x22,List.length_append,List.length_singleton]
  · rw [t3x24,List.length_append,List.length_singleton]; congr 1
  · rw [t3x20,List.length_append,List.length_singleton,
      show 12-lv=(12-(pre.length+1))+1 by omega,Nat.pow_succ,Nat.mul_div_cancel _ (by norm_num)]
  · exact (hw.regs.trans (rw2.trans t3r)).mono (by decide)
  · refine (fsu.trans t3f).mono (fun X _ h => ?_)
    unfold TMW at h ⊢
    sg_omega
  · refine DigsAt.snoc (hw.out.frame ((t2f.trans hwf).trans t3f) (by sg_omega)
      (fun B h1 h2 h => by sg_omega)) ?_
    constructor
    · rw [t3a,hslot',reg _ (by omega),hmo.1,BitVec.extractLsb'_xor,topNode_lo cache leaf lv hslot]
    · rw [t3b,
        show REGION+16*(8192-2*2^(12-lv)+(leaf/2^lv ^^^ 1))+8=REGION+8*(2*topSlot leaf lv+1) by
          rw [hslot']; ring,
        reg _ (by omega),hmo.2,BitVec.extractLsb'_xor,topNode_hi cache leaf lv hslot]
theorem tp_masks {w : MachineState} (hw : MInv w0 [] w) :
    TSim image sk w 528 612 12 12
      ((List.range 12).mapM fun level => mask level (leaf/2^level ^^^ 1) >>= fun m =>
        pure (topNode cache leaf level ^^^ m))
      (fun ds v => ds.length=12 ∧ MInv w0 ds v) := by
  refine (TSim.mapM_range 12 _ (fun _ => 44) (fun _ => 51) (fun _ => 1) (fun _ => 1) (MInv w0)
    (fun pre t hpl ht => tp_mask_one hb hl h14 hpl ht) hw).of_eq rfl ?_ ?_ ?_ ?_ <;> simp [sumTo_const]
end masks
end SigGolfCandidate.T3M.Sign.Packed
end
section
namespace SigGolfCandidate.T3M.Sign.Packed.Boundary
variable {leafFn : LeafFn}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open ClaudeWCT
open SigGolfCandidate.T3 (Layer Digest Pieces Cache signTop topPath counterLimit buildLeaf
  nodeHash mask route height chainCount width maxDigit target decode header zero16 pad64 shortHash)
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN NODE NOUT LOUT LEAFPK MOUT ZDIG DUMMY TOP REGION
  LeafArgs LeafW leafRegs n4)
open SphincsSecurity (bytesLE bytesLE_length)
private theorem extractByte_zero_top (k : Nat) : extractByte (0 : Word) k = 0 := by
  simp [extractByte]
theorem route_0 {index : Nat} (h : index < 2 ^ 31) : route index 0 = (index / 2 ^ 19 % 4096, 0) := by
  show (index / 2 ^ 19 % 2 ^ 12, index / 2 ^ (19 + 12)) = _
  rw [Nat.div_eq_of_lt (by omega : index < 2 ^ (19 + 12))]
  rfl
def tl0 (leaf : Nat) (ds : List Nat) (dest : Nat) : LeafArgs :=
  ⟨0, 0, leaf, ds, true, DIGITS, SIG + 2224, dest, 447⟩
section top
variable {sk : SecretKey} {cache : Bytes 131072}
theorem leafPreS_of {s : MachineState} {A : LeafArgs} (hb : Base sk cache s) (hlay : A.lay = 0) (hso : A.so = true)
    (h1 : s.getReg .x1 = pcOf A.ret) (h8 : s.getReg .x8 = BitVec.ofNat 64 0)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 A.tree) (h18 : s.getReg .x18 = BitVec.ofNat 64 A.leaf)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 A.digp) (h23 : s.getReg .x23 = BitVec.ofNat 64 A.valp)
    (h25 : s.getReg .x25 = BitVec.ofNat 64 A.dest) (h26 : s.getReg .x26 = BitVec.ofNat 64 52)
    (h27 : s.getReg .x27 = BitVec.ofNat 64 51) (h31 : s.getReg .x31 = BitVec.ofNat 64 (if A.so then 1 else 0))
    (htree : A.tree < 2 ^ 32) (hleaf : A.leaf < 2 ^ 32)
    (hdig : ∀ i < 52, s.getByte (BitVec.ofNat 64 (A.digp + i)) = BitVec.ofNat 8 (A.d i))
    (hdigb : ∀ i < 52, A.d i < 256 ∧ (A.so = false → A.d i ≤ maxDigit 0 i))
    (hdigp : A.digp + 52 ≤ 2 ^ 24) (hdigW : ∀ i < 52, ¬ LeafW A ((A.digp + i) / 8 * 8))
    (hdigC : A.digp + 52 ≤ 0x201C0 ∨ 0x20210 ≤ A.digp)
    (hv8 : A.valp % 8 = 0) (hv : A.valp + 16 * 52 ≤ 2 ^ 24)
    (hvs : A.valp + 16 * 52 ≤ PRIV ∨ LEAFPK + 960 ≤ A.valp) (hd8 : A.so = false → A.dest % 8 = 0)
    (hd : A.dest + 16 ≤ 2 ^ 24) (hds : A.dest + 16 ≤ PRIV ∨ LEAFPK + 960 ≤ A.dest ∨ (CHAIN + 80 ≤ A.dest ∧ A.dest + 16 ≤ LOUT))
    (hdv : A.dest + 16 ≤ A.valp ∨ A.valp + 16 * 52 ≤ A.dest)
    (hroute : A.tree * 2 ^ height A.lay + A.leaf < 2 ^ 31)
    (hleafHeight : A.leaf < 2 ^ height A.lay)
    (hsteps : ∀ i < A.n, A.e i ≤ 8) : LeafPreS sk s A := by
  have hn : A.n = 52 := by show chainCount A.lay = 52; rw [hlay]; rfl
  have h4 : n4 A.lay = 51 := by rw [hlay]; rfl
  exact
    { x1 := h1
      x5 := hb.x5
      x8 := by rw [h8, hlay]; rfl
      x9 := h9
      x18 := h18
      x22 := h22
      x23 := h23
      x25 := h25
      x26 := by rw [h26, hn]
      x27 := by rw [h27, h4]
      x31 := h31
      htree := htree
      hleaf := hleaf
      hroute := hroute
      hleafHeight := hleafHeight
      hsteps := hsteps
      p0 := hb.p0
      p8 := hb.p8
      p32 := hb.p32
      p40 := hb.p40
      p48 := hb.p48
      p56 := hb.p56
      z0 := hb.zero _ (by packed_sgo) (by unfold NeverW; simp)
      z8 := hb.zero _ (by packed_sgo) (by unfold NeverW; simp)
      hsl := fun h => absurd (h.symm.trans hso) (by decide)
      hdig := fun i hi => hdig i (by rw [hn] at hi; exact hi)
      hdigb := fun i hi => by rw [hlay]; exact hdigb i (by rw [hn] at hi; exact hi)
      hdigp := by rw [hn]; exact hdigp
      hdigW := fun i hi => hdigW i (by rw [hn] at hi; exact hi)
      hdigC := by rw [hn]; exact hdigC
      hv8 := hv8
      hv := by rw [hn]; exact hv
      hvs := by rw [hn]; exact hvs
      hd8 := hd8
      hd := hd
      hds := hds
      hdv := by rw [hn]; exact hdv }
theorem base_leaf {s t : MachineState} {A : LeafArgs} (hb : Base sk cache s) (hlay : A.lay = 0)
    (hf : Frame s t (fun X => LeafW A X ∨ TopScr X)) (hr : RegsExcept s t leafRegs)
    (hvB : A.valp + 16 * 52 ≤ PRIV ∨ LEAFPK + 960 ≤ A.valp) (hvR : A.valp + 16 * 52 ≤ REGION ∨ REGION + 131040 ≤ A.valp)
    (hdB : A.dest + 16 ≤ PRIV) (hdZ : A.dest + 16 ≤ ZDIG ∨ ZDIG + 64 ≤ A.dest)
    (hvZ : A.valp + 16 * 52 ≤ ZDIG ∨ ZDIG + 64 ≤ A.valp)
    (hvT : A.valp + 16 * 52 ≤ Search.TOP_DATA) : Base sk cache t := by
  have hn : A.n = 52 := by show chainCount A.lay = 52; rw [hlay]; rfl
  refine hb.frame hf hr (by decide) (fun X _ hB hW => ?_)
  unfold BaseA NeverW Search.TOP_DATA at hB
  unfold Search.TOP_DATA at hvT
  rcases hW with hW | hW
  · unfold LeafW at hW
    rw [hn, if_pos hlay] at hW
    packed_sgo
  · unfold TopScr at hW
    packed_sgo
structure TopRegs (leaf : Nat) (s : MachineState) : Prop where
  x8 : s.getReg .x8 = BitVec.ofNat 64 0
  x9 : s.getReg .x9 = BitVec.ofNat 64 0
  x14 : s.getReg .x14 = BitVec.ofNat 64 leaf
  x26 : s.getReg .x26 = BitVec.ofNat 64 52
  x27 : s.getReg .x27 = BitVec.ofNat 64 51
theorem TopRegs.of {leaf : Nat} {s t : MachineState} {l : List Reg} (h : TopRegs leaf s) (hr : RegsExcept s t l)
    (hl : Reg.x8 ∉ l ∧ Reg.x9 ∉ l ∧ Reg.x14 ∉ l ∧ Reg.x26 ∉ l ∧ Reg.x27 ∉ l) : TopRegs leaf t :=
  ⟨by rw [hr.get hl.1, h.x8], by rw [hr.get hl.2.1, h.x9], by rw [hr.get hl.2.2.1, h.x14],
    by rw [hr.get hl.2.2.2.1, h.x26], by rw [hr.get hl.2.2.2.2, h.x27]⟩
theorem zdig_byte {s : MachineState} (hb : Base sk cache s) {i : Nat} (hi : i < 54) :
    s.getByte (BitVec.ofNat 64 (ZDIG + i)) = BitVec.ofNat 8 0 := by
  rw [getByte_eq_word s _ (by packed_sgo), hb.zero _ (by packed_sgo) (by unfold NeverW; packed_sgo), extractByte_zero_top]
  rfl
theorem frame_l0 {s t : MachineState} {W : Nat → Prop} (h : Frame s t W) (hW : ∀ A, W A → L0W A) :
    Frame s t L0W := h.mono (fun A _ hA => hW A hA)
theorem frame_l0_trans {s t u : MachineState} (h1 : Frame s t L0W) (h2 : Frame t u L0W) : Frame s u L0W :=
  (h1.trans h2).mono (fun A _ h => by rcases h with h | h <;> exact h)
theorem leafW_l0 {A : LeafArgs} (hlay : A.lay = 0)
    (hv : A.valp + 16 * 52 ≤ SIG ∨ (SIG + 2192 ≤ A.valp ∧ A.valp + 16 * 52 ≤ SIG + 3248) ∨ SIG + 5616 ≤ A.valp)
    (hd : A.dest + 16 ≤ SIG ∨ (SIG + 2192 ≤ A.dest ∧ A.dest + 16 ≤ SIG + 3248) ∨ SIG + 5616 ≤ A.dest) :
    ∀ X, (LeafW A X ∨ TopScr X) → L0W X := by
  have hn : A.n = 52 := by show chainCount A.lay = 52; rw [hlay]; rfl
  intro X hX
  rcases hX with hX | hX
  swap
  · unfold TopScr at hX; unfold L0W; constructor <;> packed_sgo
  unfold LeafW at hX
  rw [hn, if_pos hlay] at hX
  unfold L0W
  constructor <;> packed_sgo
def KeepI (s t : MachineState) (lo hi : Nat) : Prop :=
  ∀ A, A < 2 ^ 64 → lo ≤ A → A < hi → t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A)
theorem KeepI.of_frame {s t : MachineState} {W : Nat → Prop} (h : Frame s t W) {lo hi : Nat}
    (hW : ∀ A, lo ≤ A → A < hi → ¬ W A) : KeepI s t lo hi := fun A hA h1 h2 => h.get hA (hW A h1 h2)
theorem KeepI.trans {s t u : MachineState} {lo hi : Nat} (h1 : KeepI s t lo hi) (h2 : KeepI t u lo hi) :
    KeepI s u lo hi := fun A hA a b => (h2 A hA a b).trans (h1 A hA a b)
theorem KeepI.mono {s t : MachineState} {lo hi lo' hi' : Nat} (h : KeepI s t lo hi) (h1 : lo ≤ lo')
    (h2 : hi' ≤ hi) : KeepI s t lo' hi' := fun A hA a b => h A hA (by omega) (by omega)
theorem KeepI.digAt {s t : MachineState} {lo hi A : Nat} {d : Digest} (h : KeepI s t lo hi) (hd : DigAt s A d)
    (h1 : lo ≤ A) (h2 : A + 16 ≤ hi) (h3 : A + 16 ≤ 2 ^ 64) : DigAt t A d :=
  ⟨(h A (by omega) h1 (by omega)).trans hd.1, (h (A + 8) (by omega) (by omega) (by omega)).trans hd.2⟩
-- r3-lean-sign: legacy `l0Spec_of` (old BC top search, target 145) removed; it had no users.
end top
end SigGolfCandidate.T3M.Sign.Packed.Boundary
end
-- r3-lean-sign: legacy `counterSearchSpec`/`layers_checked`/`entry370`/`layers_from370` (old BC search) removed.
end
namespace SigGolfCandidate.T3M.Sign.SharedTopPath
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (M Digest Cache readDigest readLE mask header privateInput)
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN NODE NOUT LOUT LEAFPK MOUT ZDIG DUMMY TOP REGION)
open SigGolfCandidate.T3M.Sign.Packed
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
structure StateBase (sk : SecretKey) (cache : Bytes 131072) (t : MachineState)  : Prop where
  x5 : t.getReg .x5 = 0
  p0 : t.getMem (BitVec.ofNat 64 PRIV) = sk.extractLsb' 0 64
  p8 : t.getMem (BitVec.ofNat 64 (PRIV + 8)) = sk.extractLsb' 64 64
  p32 : t.getMem (BitVec.ofNat 64 (PRIV + 32)) = sk.extractLsb' 128 64
  p40 : t.getMem (BitVec.ofNat 64 (PRIV + 40)) = sk.extractLsb' 192 64
  p48 : t.getMem (BitVec.ofNat 64 (PRIV + 48)) = 0
  p56 : t.getMem (BitVec.ofNat 64 (PRIV + 56)) = 0
  region : ∀ k < 16380, t.getMem (BitVec.ofNat 64 (REGION + 8 * k)) = cache.extractLsb' (64 * (k + 4)) 64
  zero : ∀ A < 2 ^ 64, NeverW A → t.getMem (BitVec.ofNat 64 A) = 0
theorem StateBase.frame {sk : SecretKey} {cache : Bytes 131072} {t u : MachineState} {W : Nat → Prop}
    {l : List Reg} (h : StateBase sk cache t) (hf : Frame t u W) (hr : RegsExcept t u l) (h5 : .x5 ∉ l)
    (hW : ∀ A, A < 2 ^ 64 → BaseA A → ¬ W A) : StateBase sk cache u := by
  have g : ∀ A, A < 2 ^ 64 → BaseA A → u.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) :=
    fun A hA hb => hf.get hA (hW A hA hb)
  refine ⟨by rw [hr.get h5, h.x5], ?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_, fun A hA hn => ?_⟩
  · rw [g _ (by sg_omega) (by unfold BaseA; simp), h.p0]
  · rw [g _ (by sg_omega) (by unfold BaseA; simp), h.p8]
  · rw [g _ (by sg_omega) (by unfold BaseA; simp), h.p32]
  · rw [g _ (by sg_omega) (by unfold BaseA; simp), h.p40]
  · rw [g _ (by sg_omega) (by unfold BaseA; simp), h.p48]
  · rw [g _ (by sg_omega) (by unfold BaseA; simp), h.p56]
  · rw [g _ (by sg_omega) (by unfold BaseA; right; right; right; right; right; right; left; sg_omega),
      h.region k hk]
  · rw [g _ hA (by unfold BaseA; right; right; right; right; right; right; right; left; exact hn), h.zero A hA hn]

variable {im : Image} (hcode : SharedTopBlocks.Code im)
section masks
variable {sk : SecretKey} {cache : Bytes 131072} {w0 : MachineState} {leaf : Nat}
  (hb : StateBase sk cache w0) (hl : leaf<4096) (h14 : w0.getReg .x14=BitVec.ofNat 64 leaf)
include hcode hb hl h14
theorem tp_mask_one {pre : List Digest} (hpl : pre.length<12) {w : MachineState}
    (hw : MInv w0 pre w) :
    TSim im sk w 44 51 1 1
      (mask pre.length (leaf/2^pre.length ^^^ 1) >>= fun m =>
        pure (topNode cache leaf pre.length ^^^ m))
      (fun d v => MInv w0 (pre++[d]) v) := by
  set lv := pre.length with hlv
  have g : ∀ r, r∉tmRegs → w.getReg r=w0.getReg r := fun r hr => hw.regs.get hr
  obtain ⟨hsib,hslot⟩ := topSlot_lt hl (show lv≤11 by omega)
  obtain ⟨t2,st2,t2pc,t2x10,t2x11,t2x12,t2x23,t2a,t2b,t2r,t2f⟩ :=
    SharedTopBlocks.blk1438_spec hcode w (by rw [hw.pc, if_pos hpl]) leaf lv hl (by omega)
      (by rw [g _ (by decide),h14]) hw.x22
  have fr : ∀ X, X<2^64 → BaseA X → t2.getMem (BitVec.ofNat 64 X)=w0.getMem (BitVec.ofNat 64 X) :=
    fun X hX hba => (t2f.get hX (by unfold BaseA NeverW Search.TOP_DATA at hba; sg_omega)).trans
      (hw.frame.get hX (by unfold BaseA NeverW Search.TOP_DATA at hba; unfold TMW; sg_omega))
  have hq : hashInput t2=toQ (privateInput sk (.inl (header 13 0 0 lv ((leaf/2^lv ^^^ 1)/2)))) := by
    refine hashInput_toQ t2 _ 0 PRIV (privateInput_tweak_length _ _) t2x10 (by decide) (by decide) t2x11
      (by decide) ?_
    rw [wordsOf_privateInput_tweak,header_lo,header_hi,readWords_eight,
      fr PRIV (by decide) (by unfold BaseA; simp),fr (PRIV+8) (by decide) (by unfold BaseA; simp),t2a,t2b,
      fr (PRIV+32) (by decide) (by unfold BaseA; simp),fr (PRIV+40) (by decide) (by unfold BaseA; simp),
      fr (PRIV+48) (by decide) (by unfold BaseA; simp),fr (PRIV+56) (by decide) (by unfold BaseA; simp),
      hb.p0,hb.p8,hb.p32,hb.p40,hb.p48,hb.p56]
    rfl
  have hv : hashArgumentsValid t2=true :=
    hashArgs_const t2 PRIV 64 MOUT t2x10 t2x11 t2x12 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h5 : t2.getReg .x5=0 := by rw [t2r.get (by decide),g _ (by decide),hb.x5]
  refine (TSim.steps st2 (TSim.mask_bind (k:=25) (c:=25) (n:=0) (b:=0)
    (SharedTopBlocks.fetch_1456 hcode t2 t2pc) h5 hv hq (fun a => ?_))).of_eq rfl rfl rfl rfl rfl
  have hwf := Frame.writeHash t2 a MOUT t2x12 (by decide)
  have upc : (writeHash t2 a).pc=pcOf 1457 := by rw [pc_writeHash,t2pc,pcOf_add4]
  have hmo : DigAt (writeHash t2 a) (MOUT+16*((leaf/2^lv ^^^ 1)%2))
      (if (leaf/2^lv ^^^ 1)%2=0 then a.extractLsb' 0 128 else a.extractLsb' 128 128) := by
    have hmod := Nat.mod_lt (leaf/2^lv ^^^ 1) (by decide : 0<2)
    by_cases hz : (leaf/2^lv ^^^ 1)%2=0
    · simpa [hz] using DigAt.writeHash_lo t2 a MOUT t2x12 (by decide)
    · have ho : (leaf/2^lv ^^^ 1)%2=1 := by omega
      simpa [ho] using DigAt.writeHash_hi t2 a MOUT t2x12 (by decide)
  have rw2 : RegsExcept w (writeHash t2 a) [.x6,.x7,.x10,.x11,.x12,.x23,.x28] := fun r hr => by
    rw [getReg_writeHash]; exact t2r.get hr
  have hlo2 : 2≤2^(12-lv) := by
    have := Nat.pow_le_pow_right (by norm_num : 0<2) (show 1≤12-lv by omega); simpa using this
  have hlo : 2^(12-lv)≤4096 := by
    have := Nat.pow_le_pow_right (by norm_num : 0<2) (show 12-lv≤12 by omega); simpa using this
  obtain ⟨t3,st3,t3pc,t3a,t3b,t3x24,t3x20,t3x22,t3r,t3f⟩ :=
    SharedTopBlocks.blk1457_spec hcode (writeHash t2 a) upc (leaf/2^lv ^^^ 1) (2^(12-lv)) lv
      (SIG+3056+16*pre.length) hlo2 hlo hsib (by omega)
      (by sg_omega) (by sg_omega) (by sg_omega)
      (by rw [getReg_writeHash]; exact t2x23)
      (by rw [rw2.get (by decide)]; exact hw.x20)
      (by rw [rw2.get (by decide)]; exact hw.x22)
      (by rw [rw2.get (by decide)]; exact hw.x24)
      (by rw [getReg_writeHash]; exact t2x12)
  have hst : 2*2^(12-lv)=2^(13-lv) := by
    rw [show 13-lv=(12-lv)+1 by omega,Nat.pow_succ]; ring
  have hslot' : REGION+16*(8192-2*2^(12-lv)+(leaf/2^lv ^^^ 1))=REGION+8*(2*topSlot leaf lv) := by
    unfold topSlot; rw [hst]; ring
  have fsu := hw.frame.trans (t2f.trans hwf)
  have reg : ∀ k<16380, (writeHash t2 a).getMem (BitVec.ofNat 64 (REGION+8*k))=
      cache.extractLsb' (64*(k+4)) 64 := fun k hk => by
    rw [fsu.get (by sg_omega) (by unfold TMW; sg_omega)]; exact hb.region k hk
  refine TSim.pure_steps st3 ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [List.length_append,List.length_singleton] using t3pc
  · rw [t3x22,List.length_append,List.length_singleton]
  · rw [t3x24,List.length_append,List.length_singleton]; congr 1
  · rw [t3x20,List.length_append,List.length_singleton,
      show 12-lv=(12-(pre.length+1))+1 by omega,Nat.pow_succ,Nat.mul_div_cancel _ (by norm_num)]
  · exact (hw.regs.trans (rw2.trans t3r)).mono (by decide)
  · refine (fsu.trans t3f).mono (fun X _ h => ?_)
    unfold TMW at h ⊢
    sg_omega
  · refine DigsAt.snoc (hw.out.frame ((t2f.trans hwf).trans t3f) (by sg_omega)
      (fun B h1 h2 h => by sg_omega)) ?_
    constructor
    · rw [t3a,hslot',reg _ (by omega),hmo.1,BitVec.extractLsb'_xor,topNode_lo cache leaf lv hslot]
    · rw [t3b,
        show REGION+16*(8192-2*2^(12-lv)+(leaf/2^lv ^^^ 1))+8=REGION+8*(2*topSlot leaf lv+1) by
          rw [hslot']; ring,
        reg _ (by omega),hmo.2,BitVec.extractLsb'_xor,topNode_hi cache leaf lv hslot]
theorem tp_masks {w : MachineState} (hw : MInv w0 [] w) :
    TSim im sk w 528 612 12 12
      ((List.range 12).mapM fun level => mask level (leaf/2^level ^^^ 1) >>= fun m =>
        pure (topNode cache leaf level ^^^ m))
      (fun ds v => ds.length=12 ∧ MInv w0 ds v) := by
  refine (TSim.mapM_range 12 _ (fun _ => 44) (fun _ => 51) (fun _ => 1) (fun _ => 1) (MInv w0)
    (fun pre t hpl ht => tp_mask_one hcode hb hl h14 hpl ht) hw).of_eq rfl ?_ ?_ ?_ ?_ <;> simp [sumTo_const]
end masks

#print axioms tp_masks
end SigGolfCandidate.T3M.Sign.SharedTopPath

namespace SigGolfCandidate.T3M.Sign.SharedTopContinuation
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open ClaudeWCT
open SigGolfCandidate.T3 (Layer Digest Pieces Cache signTop topPath counterLimit buildLeaf nodeHash mask route height chainCount width maxDigit target decode header zero16 pad64 shortHash)
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN NODE NOUT LOUT LEAFPK MOUT ZDIG DUMMY TOP REGION LeafArgs LeafW leafRegs n4)
open SigGolfCandidate.T3M.Sign.Packed SigGolfCandidate.T3M.Sign.Packed.Boundary
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable {im : Image} {sk : SecretKey} {cache : Bytes 131072}
theorem leafPreS_of {s : MachineState} {A : LeafArgs} (hb : SharedTopPath.StateBase sk cache s) (hlay : A.lay = 0) (hso : A.so = true)
    (h1 : s.getReg .x1 = pcOf A.ret) (h8 : s.getReg .x8 = BitVec.ofNat 64 0)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 A.tree) (h18 : s.getReg .x18 = BitVec.ofNat 64 A.leaf)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 A.digp) (h23 : s.getReg .x23 = BitVec.ofNat 64 A.valp)
    (h25 : s.getReg .x25 = BitVec.ofNat 64 A.dest) (h26 : s.getReg .x26 = BitVec.ofNat 64 52)
    (h27 : s.getReg .x27 = BitVec.ofNat 64 51) (h31 : s.getReg .x31 = BitVec.ofNat 64 (if A.so then 1 else 0))
    (htree : A.tree < 2 ^ 32) (hleaf : A.leaf < 2 ^ 32)
    (hdig : ∀ i < 52, s.getByte (BitVec.ofNat 64 (A.digp + i)) = BitVec.ofNat 8 (A.d i))
    (hdigb : ∀ i < 52, A.d i < 256 ∧ (A.so = false → A.d i ≤ maxDigit 0 i))
    (hdigp : A.digp + 52 ≤ 2 ^ 24) (hdigW : ∀ i < 52, ¬ LeafW A ((A.digp + i) / 8 * 8))
    (hdigC : A.digp + 52 ≤ 0x201C0 ∨ 0x20210 ≤ A.digp)
    (hv8 : A.valp % 8 = 0) (hv : A.valp + 16 * 52 ≤ 2 ^ 24)
    (hvs : A.valp + 16 * 52 ≤ PRIV ∨ LEAFPK + 960 ≤ A.valp) (hd8 : A.so = false → A.dest % 8 = 0)
    (hd : A.dest + 16 ≤ 2 ^ 24) (hds : A.dest + 16 ≤ PRIV ∨ LEAFPK + 960 ≤ A.dest ∨ (CHAIN + 80 ≤ A.dest ∧ A.dest + 16 ≤ LOUT))
    (hdv : A.dest + 16 ≤ A.valp ∨ A.valp + 16 * 52 ≤ A.dest)
    (hroute : A.tree * 2 ^ height A.lay + A.leaf < 2 ^ 31)
    (hleafHeight : A.leaf < 2 ^ height A.lay)
    (hsteps : ∀ i < A.n, A.e i ≤ 8) : LeafPreS sk s A := by
  have hn : A.n = 52 := by show chainCount A.lay = 52; rw [hlay]; rfl
  have h4 : n4 A.lay = 51 := by rw [hlay]; rfl
  exact
    { x1 := h1
      x5 := hb.x5
      x8 := by rw [h8, hlay]; rfl
      x9 := h9
      x18 := h18
      x22 := h22
      x23 := h23
      x25 := h25
      x26 := by rw [h26, hn]
      x27 := by rw [h27, h4]
      x31 := h31
      htree := htree
      hleaf := hleaf
      hroute := hroute
      hleafHeight := hleafHeight
      hsteps := hsteps
      p0 := hb.p0
      p8 := hb.p8
      p32 := hb.p32
      p40 := hb.p40
      p48 := hb.p48
      p56 := hb.p56
      z0 := hb.zero _ (by packed_sgo) (by unfold NeverW; simp)
      z8 := hb.zero _ (by packed_sgo) (by unfold NeverW; simp)
      hsl := fun h => absurd (h.symm.trans hso) (by decide)
      hdig := fun i hi => hdig i (by rw [hn] at hi; exact hi)
      hdigb := fun i hi => by rw [hlay]; exact hdigb i (by rw [hn] at hi; exact hi)
      hdigp := by rw [hn]; exact hdigp
      hdigW := fun i hi => hdigW i (by rw [hn] at hi; exact hi)
      hdigC := by rw [hn]; exact hdigC
      hv8 := hv8
      hv := by rw [hn]; exact hv
      hvs := by rw [hn]; exact hvs
      hd8 := hd8
      hd := hd
      hds := hds
      hdv := by rw [hn]; exact hdv }
theorem base_leaf {s t : MachineState} {A : LeafArgs} (hb : SharedTopPath.StateBase sk cache s) (hlay : A.lay = 0)
    (hf : Frame s t (fun X => LeafW A X ∨ TopScr X)) (hr : RegsExcept s t leafRegs)
    (hvB : A.valp + 16 * 52 ≤ PRIV ∨ LEAFPK + 960 ≤ A.valp) (hvR : A.valp + 16 * 52 ≤ REGION ∨ REGION + 131040 ≤ A.valp)
    (hdB : A.dest + 16 ≤ PRIV) (hdZ : A.dest + 16 ≤ ZDIG ∨ ZDIG + 64 ≤ A.dest)
    (hvZ : A.valp + 16 * 52 ≤ ZDIG ∨ ZDIG + 64 ≤ A.valp)
    (hvT : A.valp + 16 * 52 ≤ Search.TOP_DATA) : SharedTopPath.StateBase sk cache t := by
  have hn : A.n = 52 := by show chainCount A.lay = 52; rw [hlay]; rfl
  refine hb.frame hf hr (by decide) (fun X _ hB hW => ?_)
  unfold BaseA NeverW Search.TOP_DATA at hB
  unfold Search.TOP_DATA at hvT
  rcases hW with hW | hW
  · unfold LeafW at hW
    rw [hn, if_pos hlay] at hW
    packed_sgo
  · unfold TopScr at hW
    packed_sgo
def topLeafC : Nat := 260000
def LeafSpec (im : Image) : Prop :=
  ∀ (sk : SecretKey) (A : LeafArgs) (s : MachineState),
    A.lay = 0 → A.so = true → A.tree = 0 → (∀ i < A.n, A.d i ≤ 7) →
    A.valp + 16*A.n ≤ 0x60000 → A.digp+A.n ≤ 0x60000 → A.dest+16 ≤ 0x60000 →
    LeafPreS sk s A → SigGolfCandidate.T3M.Sign.Seed.Z32 s → s.pc=pcOf (1013+27) →
    TBSim im sk s topLeafC (SigGolfCandidate.T3.buildLeafTop A.leaf A.digits A.so)
      (fun r t => t.pc=pcOf A.ret ∧ DigsAt t A.valp r.2 ∧ r.2.length=A.n ∧
        RegsExcept s t leafRegs ∧ Frame s t (fun X => LeafW A X ∨ SigGolfCandidate.T3M.Sign.Packed.TopScr X))

def Post (s : MachineState) (p : Pieces) (t : MachineState) : Prop :=
  t.pc=pcOf 540 ∧ (∀ i<52,DigAt t (SIG+2224+16*i) (p.1.getD i 0)) ∧
    (∀ j<12,DigAt t (SIG+3056+16*j) (p.2.getD j 0)) ∧ Frame s t L0W ∧
    (∀ A, (A=0x66000 ∨ A=0x66008) → t.getMem (BitVec.ofNat 64 A)=s.getMem (BitVec.ofNat 64 A))

theorem top_only (hcode : SharedTopBlocks.Code im) (hTop : LeafSpec im)
    (leaf : Nat) (hl : leaf<4096) (ds : List Nat) (u : MachineState) (upc : u.pc=pcOf 441)
    (hbu : SharedTopPath.StateBase sk cache u) (hregs : TopRegs leaf u)
    (h18 : u.getReg .x18=BitVec.ofNat 64 leaf) (hx25 : (u.getReg .x25).toNat≤201)
    (hd7 : ∀ i<52,ds.getD i 0≤7)
    (udig : ∀ i<52,u.getByte (BitVec.ofNat 64 (DIGITS+i))=BitVec.ofNat 8 (ds.getD i 0)) :
    TBSim im sk u (topLeafC+30006) (signTop (cacheDec cache) leaf ds) (Post u) := by
  have hSIG : SIG=28672 := rfl
  set dest0 := (u.getReg .x25).toNat with hdest0
  obtain ⟨u1, su1, u1pc, u1x1, u1x31, u1x22, u1x23, u1r, u1f⟩ := SharedTopBlocks.blk441_spec hcode u upc
  have g1 : ∀ r, r ∉ [.x1, .x22, .x23, .x31] → u1.getReg r = u.getReg r := fun r hr => u1r.get hr
  have hbu1 : SharedTopPath.StateBase sk cache u1 := hbu.frame u1f u1r (by decide) (fun _ _ _ h => h)
  have tr1 : TopRegs leaf u1 :=
    ⟨by rw [g1 _ (by decide)]; exact hregs.x8, by rw [g1 _ (by decide)]; exact hregs.x9,
      by rw [g1 _ (by decide)]; exact hregs.x14, by rw [g1 _ (by decide)]; exact hregs.x26,
      by rw [g1 _ (by decide)]; exact hregs.x27⟩
  have hp0 : LeafPreS sk u1 (tl0 leaf ds dest0) :=
    leafPreS_of hbu1 rfl rfl u1x1 tr1.x8 tr1.x9 (by rw [g1 _ (by decide)]; exact h18) u1x22 u1x23
      (by rw [g1 _ (by decide)]; show u.getReg .x25 = BitVec.ofNat 64 (u.getReg .x25).toNat
          rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
      tr1.x26 tr1.x27 u1x31 (by show 0 < 2 ^ 32; norm_num) (by show leaf < 2 ^ 32; omega)
      (fun i hi => by
        show u1.getByte (BitVec.ofNat 64 (DIGITS + i)) = _
        rw [u1f.getByte (by packed_sgo) (fun h => h)]; exact udig i hi)
      (fun i hi => ⟨by show ds.getD i 0 < 256; have := hd7 i hi; omega, fun h => by simp [tl0] at h⟩)
      (by show DIGITS + 52 ≤ 2 ^ 24; packed_sgo) (fun i hi => by unfold LeafW; simp only [tl0, LeafArgs.n, chainCount, Matrix.cons_val_zero, ↓reduceIte]; packed_sgo)
      (Or.inr (by show 0x20210 ≤ DIGITS; packed_sgo))
      (by show (SIG + 2224) % 8 = 0; packed_sgo) (by show SIG + 2224 + 16 * 52 ≤ 2 ^ 24; packed_sgo)
      (Or.inl (by show SIG + 2224 + 16 * 52 ≤ PRIV; packed_sgo)) (fun h => by simp [tl0] at h)
      (by show dest0 + 16 ≤ 2 ^ 24; omega) (Or.inl (by show dest0 + 16 ≤ PRIV; packed_sgo))
      (Or.inl (by show dest0 + 16 ≤ SIG + 2224; packed_sgo))
      (by change 0 * 2 ^ 12 + leaf < 2 ^ 31; omega)
      (by change leaf < 4096; omega)
      (fun i hi => by have := hd7 i hi; change ds.getD i 0 ≤ 8; omega)
  have hL0 := hTop sk (tl0 leaf ds dest0) u1 rfl rfl rfl hd7 (by show SIG + 2224 + 16 * 52 ≤ 0x60000; packed_sgo)
    (by show DIGITS + 52 ≤ 0x60000; packed_sgo) (by show dest0 + 16 ≤ 0x60000; omega) hp0
    ⟨hbu1.zero _ (by decide) (by unfold NeverW; simp), hbu1.zero _ (by decide) (by unfold NeverW; simp)⟩ u1pc
  try dsimp only
  rw [signTop]
  refine TBSim.mono (TBSim.steps su1 (TBSim.bind (W₂ := 30000) hL0 (fun r0 v0 hv0 => ?_)))
    (Nat.le_of_eq (by ring)) (fun _ _ h => h)
  obtain ⟨root0, values⟩ := r0
  obtain ⟨v0pc, v0vals, v0len, v0r, v0f⟩ := hv0
  have hbv0 : SharedTopPath.StateBase sk cache v0 := base_leaf hbu1 rfl v0f v0r (Or.inl (by show SIG + 2224 + 16 * 52 ≤ PRIV; packed_sgo))
    (Or.inl (by show SIG + 2224 + 16 * 52 ≤ REGION; packed_sgo)) (by show dest0 + 16 ≤ PRIV; packed_sgo)
    (Or.inl (by show dest0 + 16 ≤ ZDIG; packed_sgo)) (Or.inl (by show SIG + 2224 + 16 * 52 ≤ ZDIG; packed_sgo))
    (by show SIG + 2224 + 16 * 52 ≤ Search.TOP_DATA; unfold Search.TOP_DATA; packed_sgo)
  have trv0 : TopRegs leaf v0 := tr1.of v0r (by decide)
  have fv0 : Frame u v0 L0W := frame_l0_trans (frame_l0 u1f (fun _ h => h.elim))
    (frame_l0 v0f (leafW_l0 rfl (by simp only [tl0]; packed_sgo) (by simp only [tl0]; packed_sgo)))
  show TBSim im sk v0 30000 (topPath (cacheDec cache) leaf >>= fun path => pure (values,path)) (Post u)
  simp only [topPath, bind_assoc, pure_bind]
  obtain ⟨v1,s447,v1pc,v1r,v1f⟩ := SharedTopBlocks.blk447_spec hcode v0 v0pc
  obtain ⟨w,s1433,wpc,wx22,wx24,wx20,wr,wf⟩ := SharedTopBlocks.blk1433_spec hcode v1 v1pc
  have hbw : SharedTopPath.StateBase sk cache w := (hbv0.frame v1f v1r (by decide) (fun _ _ _ h => h)).frame wf wr
    (by decide) (fun _ _ _ h => h)
  have w14 : w.getReg .x14=BitVec.ofNat 64 leaf := by
    rw [wr.get (by decide),v1r.get (by decide),trv0.x14]
  have hm := SharedTopPath.tp_masks hcode hbw hl w14 (w:=w)
    ⟨wpc,wx22,by simpa using wx24,wx20,RegsExcept.refl _ _,Frame.refl _ _,DigsAt.nil _ _⟩
  refine TBSim.mono (TBSim.steps (s447.trans s1433)
    (TBSim.bind (W₂:=3) (TSim.toTBSim hm (by norm_num)) (fun path x hx => ?_)))
      (by omega) (fun _ _ h => h)
  obtain ⟨hlen,hx⟩ := hx
  obtain ⟨x1,s1482,x1pc,x1r,x1f⟩ := SharedTopBlocks.blk1482_spec hcode x (by simpa [hlen] using hx.pc)
  refine TBSim.mono (TBSim.pure_steps s1482 ?_) (by omega) (fun _ _ h => h)
  have fwx := hx.frame.trans x1f
  have keep : KeepI v0 x1 SIG (SIG+3056) :=
    ((KeepI.of_frame v1f (fun _ _ _ h => h)).trans
      (KeepI.of_frame wf (fun _ _ _ h => h))).trans
      (KeepI.of_frame fwx (fun A h1 h2 hA => by
        rcases hA with hA | hA
        · unfold TMW at hA; packed_sgo
        · exact hA))
  refine ⟨x1pc, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact keep.digAt (v0vals i (by rw [v0len]; exact hi)) (by omega) (by omega) (by packed_sgo)
  · intro j hj
    have hd := hx.out j (by rw [hlen]; exact hj)
    exact hd.frame x1f (by packed_sgo) (fun h => h) (fun h => h)
  · exact frame_l0_trans (frame_l0_trans (frame_l0_trans fv0
      (frame_l0 v1f (fun _ h => h.elim))) (frame_l0 wf (fun _ h => h.elim)))
      (frame_l0 fwx (fun A hA => by
        rcases hA with hA | hA
        · unfold TMW at hA; unfold L0W; constructor <;> packed_sgo
        · exact hA.elim))

  · intro A hA
    have ha : A < 2^64 := by rcases hA with rfl | rfl <;> decide
    have n0 : ¬ (LeafW (tl0 leaf ds dest0) A ∨ TopScr A) := by
      unfold LeafW TopScr tl0 LeafArgs.n chainCount
      simp only [Matrix.cons_val_zero, ↓reduceIte]
      rcases hA with rfl | rfl <;> packed_sgo
    have n1 : ¬ TMW A := by
      unfold TMW
      rcases hA with rfl | rfl <;> packed_sgo
    rw [x1f.get ha (fun h => h), hx.frame.get ha n1,
      wf.get ha (fun h => h), v1f.get ha (fun h => h),
      v0f.get ha n0, u1f.get ha (fun h => h)]

#print axioms top_only
end SigGolfCandidate.T3M.Sign.SharedTopContinuation
