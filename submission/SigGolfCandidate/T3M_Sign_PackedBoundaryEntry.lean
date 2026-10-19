import SigGolfCandidate.T3M_Sign_PackedLowTree
import SigGolfCandidate.T3M_SigCodec
import SigGolfCandidate.T3M_Search_BCCounterSearch
import SigGolfCandidate.T3M_Sign_Kernels
set_option Elab.async false

section


namespace SigGolfCandidate.T3M.Sign.Packed
open SigGolfCandidate.T3
open ClaudeWCT
def signLayersP (leafFn : LeafFn) (cache : Cache) (index : Nat) : Nat → WCT9.LayerMsg → M (Option (List Pieces))
  | 0, _ => pure (some [])
  | n + 1, msg => do
      let lay : Layer := Fin.ofNat 4 n
      let (leaf, tree) := route index lay
      let found ← WCT9.layerCounterSearch lay tree leaf msg 0 (WCT9.searchLimit lay)
      if n = 0 then
        let part ← signTop cache leaf ((found.map Prod.snd).getD dummyTop)
        pure (some [part])
      else
        let some (_, digits) := found | pure none
        let (levels, values) ← buildTreeP leafFn lay tree leaf digits
        let path := (List.range (height lay)).map fun j =>
          (levels.getD j []).getD (leaf / 2 ^ j ^^^ 1) 0
        let top := WCT9.topPair lay levels
        let some previous ← signLayersP leafFn cache index n (.pair top.1 top.2) | pure none
        pure (some (previous ++ [(values, path)]))
end SigGolfCandidate.T3M.Sign.Packed
end

section









namespace SigGolfCandidate.T3M.Sign.Packed
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest counterLimit buildLeaf)
open Keygen (LeafArgs LeafW leafRegs)
theorem blk370_spec (s : MachineState) (hpc : s.pc = pcOf 370) (idx : Nat) (hidx : idx < 2 ^ 31)
    (hm : s.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 idx) :
    ∃ t, Steps image s 26 26 t ∧ t.pc = pcOf 646 ∧ t.getReg .x1 = pcOf 396 ∧
      t.getMem (BitVec.ofNat 64 ENC) = s.getMem (BitVec.ofNat 64 FOUT) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 8)) = s.getMem (BitVec.ofNat 64 (FOUT + 8)) ∧
      t.getReg .x2 = BitVec.ofNat 64 LOW ∧ t.getReg .x31 = BitVec.ofNat 64 0 ∧
      t.getReg .x26 = BitVec.ofNat 64 43 ∧ t.getReg .x27 = BitVec.ofNat 64 0 ∧
      t.getReg .x8 = BitVec.ofNat 64 3 ∧ t.getReg .x15 = BitVec.ofNat 64 6 ∧
      t.getReg .x16 = BitVec.ofNat 64 (SIG + 4832) ∧ t.getReg .x17 = BitVec.ofNat 64 202 ∧
      t.getReg .x18 = BitVec.ofNat 64 (idx % 64) ∧ t.getReg .x14 = BitVec.ofNat 64 (idx % 64) ∧
      t.getReg .x9 = BitVec.ofNat 64 (idx / 64) ∧
      RegsExcept s t [.x1, .x2, .x6, .x7, .x8, .x9, .x14, .x15, .x16, .x17, .x18, .x26, .x27, .x28, .x29, .x30,
        .x31] ∧ Frame s t (fun A => A = ENC ∨ A = ENC + 8) := by
  have hand : ∀ x : Nat, x < 2 ^ 64 → (BitVec.ofNat 64 x >>> 0 &&& 63#64) = BitVec.ofNat 64 (x % 64) := by
    intro x hx
    rw [ofNat_shr x 0 hx, pow_zero, Nat.div_one]
    exact ofNat_and_mask x 6 (by norm_num)
  refine ⟨_, symRun_sound blk_370 codeAt_370 s hpc (by simp [blk_370.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_370.res, E.eval]
  · simp [blk_370.res, rv_simp]
  · simp only [Result.toState_getMem, blk_370.res, ENC, FOUT]; t3n []
  · simp only [Result.toState_getMem, blk_370.res, ENC, FOUT]; t3n []
  · simp [blk_370.res, rv_simp]
  · simp [blk_370.res, rv_simp]
  · simp [blk_370.res, rv_simp]
  · simp [blk_370.res, rv_simp]
  · simp [blk_370.res, rv_simp]
  · simp [blk_370.res, rv_simp]
  · simp [blk_370.res, rv_simp]
  · simp [blk_370.res, rv_simp]
  · simp only [Result.toState_getReg, blk_370.res]; t3n []
    rw [show (132432#64 : Word) = BitVec.ofNat 64 IDXV from rfl, hm, hand idx (by omega)]
  · simp only [Result.toState_getReg, blk_370.res]; t3n []
    rw [show (132432#64 : Word) = BitVec.ofNat 64 IDXV from rfl, hm, hand idx (by omega)]
  · simp only [Result.toState_getReg, blk_370.res]; t3n []
    rw [show (132432#64 : Word) = BitVec.ofNat 64 IDXV from rfl, hm, ofNat_shr idx 6 (by omega)]; rfl
  · intro r hr; simp at hr; cases r <;> simp_all [blk_370.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [ENC] at hn
    simp only [Result.toState_getMem, blk_370.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega)]
theorem blkBT_spec {a : Nat} {seg : List (BitVec 32)} {r : Result} (hc : CodeAt image (pcOf a) seg)
    (hrun : symRun { noAlias := true } seg (pcOf a) 100 = some r) (s : MachineState) (hpc : s.pc = pcOf a)
    (hobl : r.obligs s) (hpcE : (r.toState s).pc = pcOf 1173) (h1 : (r.toState s).getReg .x1 = pcOf (a + 1))
    (hregs : RegsExcept s (r.toState s) [.x1]) (hfr : Frame s (r.toState s) (fun _ => False)) :
    ∃ t, Steps image s r.steps r.cycles t ∧ t.pc = pcOf 1173 ∧ t.getReg .x1 = pcOf (a + 1) ∧
      RegsExcept s t [.x1] ∧ Frame s t (fun _ => False) :=
  ⟨_, symRun_sound hrun hc s hpc hobl, hpcE, h1, hregs, hfr⟩
theorem blk396_spec (s : MachineState) (hpc : s.pc = pcOf 396) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 1173 ∧ t.getReg .x1 = pcOf 397 ∧
      RegsExcept s t [.x1] ∧ Frame s t (fun _ => False) :=
  blkBT_spec codeAt_396 blk_396 s hpc (by simp [blk_396.res, rv_simp]) (by simp [blk_396.res, E.eval])
    (by simp [blk_396.res, rv_simp]) (by intro r hr; simp at hr; cases r <;> simp_all [blk_396.res, rv_simp] <;> rfl)
    (by intro A _ _; simp [blk_396.res, rv_simp])
theorem blk411_spec (s : MachineState) (hpc : s.pc = pcOf 411) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 1173 ∧ t.getReg .x1 = pcOf 412 ∧
      RegsExcept s t [.x1] ∧ Frame s t (fun _ => False) :=
  blkBT_spec codeAt_411 blk_411 s hpc (by simp [blk_411.res, rv_simp]) (by simp [blk_411.res, E.eval])
    (by simp [blk_411.res, rv_simp]) (by intro r hr; simp at hr; cases r <;> simp_all [blk_411.res, rv_simp] <;> rfl)
    (by intro A _ _; simp [blk_411.res, rv_simp])
theorem blk426_spec (s : MachineState) (hpc : s.pc = pcOf 426) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 1173 ∧ t.getReg .x1 = pcOf 427 ∧
      RegsExcept s t [.x1] ∧ Frame s t (fun _ => False) :=
  blkBT_spec codeAt_426 blk_426 s hpc (by simp [blk_426.res, rv_simp]) (by simp [blk_426.res, E.eval])
    (by simp [blk_426.res, rv_simp]) (by intro r hr; simp at hr; cases r <;> simp_all [blk_426.res, rv_simp] <;> rfl)
    (by intro A _ _; simp [blk_426.res, rv_simp])
theorem blk397_spec (s : MachineState) (hpc : s.pc = pcOf 397) (idx : Nat) (hidx : idx < 2 ^ 31)
    (hm : s.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 idx) :
    ∃ t, Steps image s 14 14 t ∧ t.pc = pcOf 646 ∧ t.getReg .x1 = pcOf 411 ∧
      t.getReg .x8 = BitVec.ofNat 64 2 ∧ t.getReg .x15 = BitVec.ofNat 64 6 ∧
      t.getReg .x16 = BitVec.ofNat 64 (SIG + 4048) ∧ t.getReg .x17 = BitVec.ofNat 64 202 ∧
      t.getReg .x18 = BitVec.ofNat 64 (idx / 64 % 64) ∧ t.getReg .x14 = BitVec.ofNat 64 (idx / 64 % 64) ∧
      t.getReg .x9 = BitVec.ofNat 64 (idx / 4096) ∧
      RegsExcept s t [.x1, .x6, .x7, .x8, .x9, .x14, .x15, .x16, .x17, .x18, .x28] ∧
      Frame s t (fun _ => False) := by
  have hand : ∀ x : Nat, x < 2 ^ 64 → (BitVec.ofNat 64 x >>> 6 &&& 63#64) = BitVec.ofNat 64 (x / 64 % 64) := by
    intro x hx
    rw [ofNat_shr x 6 hx]
    exact ofNat_and_mask (x / 2 ^ 6) 6 (by norm_num)
  refine ⟨_, symRun_sound blk_397 codeAt_397 s hpc (by simp [blk_397.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_397.res, E.eval]
  · simp [blk_397.res, rv_simp]
  · simp [blk_397.res, rv_simp]
  · simp [blk_397.res, rv_simp]
  · simp [blk_397.res, rv_simp]
  · simp [blk_397.res, rv_simp]
  · simp only [Result.toState_getReg, blk_397.res]; t3n []
    rw [show (132432#64 : Word) = BitVec.ofNat 64 IDXV from rfl, hm, hand idx (by omega)]
  · simp only [Result.toState_getReg, blk_397.res]; t3n []
    rw [show (132432#64 : Word) = BitVec.ofNat 64 IDXV from rfl, hm, hand idx (by omega)]
  · simp only [Result.toState_getReg, blk_397.res]; t3n []
    rw [show (132432#64 : Word) = BitVec.ofNat 64 IDXV from rfl, hm, ofNat_shr idx 12 (by omega)]; rfl
  · intro r hr; simp at hr; cases r <;> simp_all [blk_397.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_397.res, rv_simp]
theorem blk412_spec (s : MachineState) (hpc : s.pc = pcOf 412) (idx : Nat) (hidx : idx < 2 ^ 31)
    (hm : s.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 idx) :
    ∃ t, Steps image s 14 14 t ∧ t.pc = pcOf 646 ∧ t.getReg .x1 = pcOf 426 ∧
      t.getReg .x8 = BitVec.ofNat 64 1 ∧ t.getReg .x15 = BitVec.ofNat 64 7 ∧
      t.getReg .x16 = BitVec.ofNat 64 (SIG + 3248) ∧ t.getReg .x17 = BitVec.ofNat 64 201 ∧
      t.getReg .x18 = BitVec.ofNat 64 (idx / 4096 % 128) ∧ t.getReg .x14 = BitVec.ofNat 64 (idx / 4096 % 128) ∧
      t.getReg .x9 = BitVec.ofNat 64 (idx / 2 ^ 19) ∧
      RegsExcept s t [.x1, .x6, .x7, .x8, .x9, .x14, .x15, .x16, .x17, .x18, .x28] ∧
      Frame s t (fun _ => False) := by
  have hand : ∀ x : Nat, x < 2 ^ 64 → (BitVec.ofNat 64 x >>> 12 &&& 127#64) = BitVec.ofNat 64 (x / 4096 % 128) := by
    intro x hx
    rw [ofNat_shr x 12 hx]
    exact ofNat_and_mask (x / 2 ^ 12) 7 (by norm_num)
  refine ⟨_, symRun_sound blk_412 codeAt_412 s hpc (by simp [blk_412.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_412.res, E.eval]
  · simp [blk_412.res, rv_simp]
  · simp [blk_412.res, rv_simp]
  · simp [blk_412.res, rv_simp]
  · simp [blk_412.res, rv_simp]
  · simp [blk_412.res, rv_simp]
  · simp only [Result.toState_getReg, blk_412.res]; t3n []
    rw [show (132432#64 : Word) = BitVec.ofNat 64 IDXV from rfl, hm, hand idx (by omega)]
  · simp only [Result.toState_getReg, blk_412.res]; t3n []
    rw [show (132432#64 : Word) = BitVec.ofNat 64 IDXV from rfl, hm, hand idx (by omega)]
  · simp only [Result.toState_getReg, blk_412.res]; t3n []
    rw [show (132432#64 : Word) = BitVec.ofNat 64 IDXV from rfl, hm, ofNat_shr idx 19 (by omega)]; rfl
  · intro r hr; simp at hr; cases r <;> simp_all [blk_412.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_412.res, rv_simp]
def L0W (A : Nat) : Prop :=
  ¬ (SIG ≤ A ∧ A < SIG + 2192) ∧ ¬ (SIG + 3248 ≤ A ∧ A < SIG + 5616)
/-- Campaign T8D: the scratch of the top seed routines (COEFGEN/HORN register saves at `0x60000`, the 40 top
coefficients at `0x61000`). -/
def TopScr (A : Nat) : Prop := 0x60000 ≤ A ∧ A < 0x61280
/-- Cycle bound of one signature-only top leaf (prologue, COEFGEN, 54 x (HORN + chain), exit). -/
def topLeafC : Nat := 225300
def L0Cost : Nat := counterLimit * 270 + topLeafC + 38800
/-- Campaign T8D (NF17): the top leaf with family seeds (`T3.buildLeafTop`). -/
def TopLeafSpec : Prop :=
  ∀ (sk : SecretKey) (A : LeafArgs) (s : MachineState),
    A.lay = 0 → A.so = true → A.tree = 0 → (∀ i < A.n, A.d i ≤ 7) →
    A.valp + 16 * A.n ≤ 0x60000 → A.digp + A.n ≤ 0x60000 → A.dest + 16 ≤ 0x60000 →
    LeafPreS sk s A → s.pc = pcOf (1013 + 27) →
    TBSim image sk s topLeafC (T3.buildLeafTop A.leaf A.digits A.so)
      (fun r t => t.pc = pcOf A.ret ∧ DigsAt t A.valp r.2 ∧ r.2.length = A.n ∧
        RegsExcept s t leafRegs ∧ Frame s t (fun X => LeafW A X ∨ TopScr X))
end SigGolfCandidate.T3M.Sign.Packed
section
namespace SigGolfCandidate.T3M.Sign.Packed.Boundary
variable {leafFn : LeafFn}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Layer counterLimit)
open ClaudeWCT
abbrev CsPre := Search.BC.CsPreS 543
abbrev DummyRet := Search.BC.DummyOutS
def CsPost (s : MachineState) (lay : Layer) (ret : Nat) :
    Option (BitVec 32 × List Nat) → MachineState → Prop
  | none, t => if lay = 0 then DummyRet s ret t else Failed t
  | some (_, ds), t => t.pc = pcOf ret ∧ t.getReg .x5 = 0 ∧
      (∃ v, T3.decode lay v = some ds) ∧
      (∀ i < T3.chainCount lay, t.getByte (BitVec.ofNat 64 (DIGITS + i)) =
        BitVec.ofNat 8 (ds.getD i 0)) ∧
      (t.getMem (BitVec.ofNat 64 (ENC + 32))).toNat < 2 ^ 32 ∧
      RegsExcept s t csRegs ∧ Frame s t CsW ∧
      (t.getReg .x25).toNat ≤ T3.target lay
abbrev csCost := Search.BC.csCostS
def CounterSearchSpec (sk : BitVec 256) : Prop :=
  ∀ (s : MachineState) (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (ret : Nat),
    CsPre s lay tree leaf msg ret →
      TBSim image sk s (csCost lay) (WCT9.layerCounterSearch lay tree leaf msg 0 (WCT9.searchLimit lay))
        (CsPost s lay ret)
end SigGolfCandidate.T3M.Sign.Packed.Boundary
end
section
namespace SigGolfCandidate.T3M.Sign.Packed.Boundary
variable {leafFn : LeafFn}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Pieces signLayers)
open ClaudeWCT
structure L0Pre (sk : SecretKey) (cache : Bytes 131072) (index : Nat) (message : WCT9.LayerMsg)
    (t : MachineState) : Prop where
  pc : t.pc = pcOf 427
  base : Base sk cache t
  hidx : index < 2 ^ 31
  idx : t.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 index
  enc : DigAt t ENC (Search.BC.left message)
  right : DigAt t (ENC + 48) (Search.BC.right message)
  c32 : (t.getMem (BitVec.ofNat 64 (ENC + 32))).toNat < 2 ^ 32
def L0Post (t : MachineState) : Option (List Pieces) → MachineState → Prop
  | none, u => Failed u
  | some ps, u => ∃ vals path : List Digest, ps = [(vals, path)] ∧ u.pc = pcOf 540 ∧
      (∀ i < 54, DigAt u (SIG + 2192 + 16 * i) (vals.getD i 0)) ∧
      (∀ j < 12, DigAt u (SIG + 3056 + 16 * j) (path.getD j 0)) ∧ Frame t u L0W
def L0Spec (leafFn : LeafFn) (sk : SecretKey) (cache : Bytes 131072) : Prop :=
  ∀ (index : Nat) (root : WCT9.LayerMsg) (t : MachineState), L0Pre sk cache index root t →
    TBSim image sk t L0Cost (signLayersP leafFn (cacheDec cache) index 1 root) (L0Post t)
end SigGolfCandidate.T3M.Sign.Packed.Boundary
end
section
namespace SigGolfCandidate.T3M.Sign.Packed
open SigGolfCandidate.T3 (Layer Digest decode dataDigits dataCount chainCount maxDigit)
theorem dataDigits_getD (lay : Layer) (v : Digest) (i : Nat) (hi : i < dataCount lay) :
    (dataDigits lay v).getD i 0 ≤ maxDigit lay i := by
  rw [T3.dataDigits_getD lay v i hi]
  exact T3.Nonbinary.coreDigit_le lay v i
theorem length_dataDigits (lay : Layer) (v : Digest) : (dataDigits lay v).length = dataCount lay := by
  simp [dataDigits]
theorem decode_digits {lay : Layer} {v : Digest} {ds : List Nat} (h : decode lay v = some ds) :
    ds.length = chainCount lay ∧ ∀ i < chainCount lay, ds.getD i 0 ≤ maxDigit lay i :=
  ⟨(T3.decode_length_sum h).1, T3.decode_digit_max h⟩
end SigGolfCandidate.T3M.Sign.Packed
end
section
namespace SigGolfCandidate.T3M.Sign.Packed.Boundary
variable {leafFn : LeafFn}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open ClaudeWCT
open SigGolfCandidate.T3 (Layer Digest Pieces counterLimit buildTree height chainCount
  target route decode width Cache)
open SigGolfCandidate.T3M.Keygen (LevW n4)
def lstart : Nat → Nat
  | 0 => 137
  | 1 => 203
  | 2 => 253
  | 3 => 302
  | _ => 351
theorem lstart_mono (n : Nat) : lstart n ≤ lstart (n + 1) := by
  rcases n with _ | _ | _ | _ | n <;> simp [lstart]
def LayW (n : Nat) (A : Nat) : Prop :=
  ¬ (SIG ≤ A ∧ A < SIG + 2192) ∧ ¬ (SIG + 16 * lstart n ≤ A ∧ A < SIG + 5616)
def PieceAt (u : MachineState) (lay : Layer) (p : Pieces) : Prop :=
  (∀ i < chainCount lay, DigAt u (SIG + 16 * (layIdx lay + i)) (p.1.getD i 0)) ∧
    ∀ j < height lay, DigAt u (SIG + 16 * (layIdx lay + chainCount lay + j)) (p.2.getD j 0)
def SLPost (t : MachineState) (n : Nat) : Option (List Pieces) → MachineState → Prop
  | none, u => Failed u
  | some ps, u => u.pc = pcOf 540 ∧ ps.length = n ∧ (∀ lay : Layer, lay.val < n → PieceAt u lay (ps.getD lay.val ([], []))) ∧
      Frame t u (LayW n)
theorem SLPost.pre {s t : MachineState} {n : Nat} (hf : Frame s t (fun _ => False)) :
    ∀ r u, SLPost t n r u → SLPost s n r u
  | none, _, h => h
  | some _, _, ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, (hf.trans h4).mono (fun _ _ h => by
      rcases h with h | h
      · exact h.elim
      · exact h)⟩
theorem lay_cases {lay : Layer} (hlay : lay ≠ 0) :
    (lay.val = 1 ∧ layIdx lay = 203 ∧ height lay = 7) ∨ (lay.val = 2 ∧ layIdx lay = 253 ∧ height lay = 6) ∨
      (lay.val = 3 ∧ layIdx lay = 302 ∧ height lay = 6) := by
  fin_cases lay
  · exact absurd rfl hlay
  · left; exact ⟨rfl, rfl, rfl⟩
  · right; left; exact ⟨rfl, rfl, rfl⟩
  · right; right; exact ⟨rfl, rfl, rfl⟩
theorem lay_facts {lay : Layer} (hlay : lay ≠ 0) :
    lstart lay.val = layIdx lay ∧ lstart (lay.val + 1) = layIdx lay + 43 + height lay ∧ 203 ≤ layIdx lay ∧
      layIdx lay + 43 + height lay ≤ 351 := by
  rcases lay_cases hlay with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> rw [h1, h2, h3] <;> simp [lstart]
theorem csW_layW {n A : Nat} (h : CsW A) : LayW n A := by
  have := lstart_mono n
  unfold CsW at h
  unfold LayW
  constructor <;> packed_sgo
theorem btAllW_layW {lay : Layer} (hlay : lay ≠ 0) {tree A : Nat} (h : BtAllW lay tree (SIG + 16 * layIdx lay) A) :
    LayW (lay.val + 1) A := by
  unfold BtAllW BtW LevW at h
  simp only [btLev] at h
  unfold LayW
  obtain ⟨-, hls, -, -⟩ := lay_facts hlay
  rw [hls]
  rcases lay_cases hlay with ⟨-, h2, h3⟩ | ⟨-, h2, h3⟩ | ⟨-, h2, h3⟩ <;> rw [h2, h3] at h <;> rw [h2, h3] <;>
    simp only [Nat.reduceAdd, Nat.reducePow, Nat.reduceMul] at h ⊢ <;> constructor <;> packed_sgo
theorem layW_succ {n A : Nat} (h : LayW n A) : LayW (n + 1) A := by
  have := lstart_mono n
  exact ⟨h.1, fun h2 => h.2 ⟨by omega, h2.2⟩⟩
theorem route_lt {index : Nat} (h : index < 2 ^ 31) (lay : Layer) :
    (route index lay).1 < 2 ^ height lay ∧ (route index lay).2 < 2 ^ 32 := by
  simp only [route]
  exact ⟨Nat.mod_lt _ (Nat.two_pow_pos _), lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩
theorem route_3 (index : Nat) : route index 3 = (index % 64, index / 64) := by
  show (index / 2 ^ 0 % 2 ^ 6, index / 2 ^ (0 + 6)) = _
  simp
theorem route_2 (index : Nat) : route index 2 = (index / 64 % 64, index / 4096) := by
  show (index / 2 ^ 6 % 2 ^ 6, index / 2 ^ (6 + 6)) = _
  simp
theorem route_1 (index : Nat) : route index 1 = (index / 4096 % 128, index / 2 ^ 19) := by
  show (index / 2 ^ 12 % 2 ^ 7, index / 2 ^ (12 + 7)) = _
  simp
def jalBT (lay : Layer) : Nat := (![0, 426, 411, 396] : Layer → Nat) lay
theorem blkJal_spec {lay : Layer} (hlay : lay ≠ 0) (s : MachineState) (hpc : s.pc = pcOf (jalBT lay)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 1173 ∧ t.getReg .x1 = pcOf (jalBT lay + 1) ∧
      RegsExcept s t [.x1] ∧ Frame s t (fun _ => False) := by
  fin_cases lay
  · exact absurd rfl hlay
  · exact blk426_spec s hpc
  · exact blk411_spec s hpc
  · exact blk396_spec s hpc
structure LayEntry (sk : SecretKey) (cache : Bytes 131072) (lay : Layer) (index : Nat) (msg : WCT9.LayerMsg)
    (t : MachineState) : Prop where
  pc : t.pc = pcOf 646
  x1 : t.getReg .x1 = pcOf (jalBT lay)
  x2 : t.getReg .x2 = BitVec.ofNat 64 LOW
  x8 : t.getReg .x8 = BitVec.ofNat 64 lay.val
  x9 : t.getReg .x9 = BitVec.ofNat 64 (route index lay).2
  x14 : t.getReg .x14 = BitVec.ofNat 64 (route index lay).1
  x15 : t.getReg .x15 = BitVec.ofNat 64 (height lay)
  x16 : t.getReg .x16 = BitVec.ofNat 64 (SIG + 16 * layIdx lay)
  x17 : t.getReg .x17 = BitVec.ofNat 64 (target lay)
  x18 : t.getReg .x18 = BitVec.ofNat 64 (route index lay).1
  x26 : t.getReg .x26 = BitVec.ofNat 64 43
  x27 : t.getReg .x27 = BitVec.ofNat 64 0
  x31 : t.getReg .x31 = BitVec.ofNat 64 0
  base : Base sk cache t
  hlay : lay ≠ 0
  hidx : index < 2 ^ 31
  idx : t.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 index
  enc : DigAt t ENC (Search.BC.left msg)
  right : DigAt t (ENC + 48) (Search.BC.right msg)
  c32 : (t.getMem (BitVec.ofNat 64 (ENC + 32))).toNat < 2 ^ 32
structure LayNext (sk : SecretKey) (cache : Bytes 131072) (ret index : Nat) (root : WCT9.LayerMsg) (t : MachineState) :
    Prop where
  pc : t.pc = pcOf ret
  x2 : t.getReg .x2 = BitVec.ofNat 64 LOW
  x26 : t.getReg .x26 = BitVec.ofNat 64 43
  x27 : t.getReg .x27 = BitVec.ofNat 64 0
  x31 : t.getReg .x31 = BitVec.ofNat 64 0
  base : Base sk cache t
  hidx : index < 2 ^ 31
  idx : t.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 index
  enc : DigAt t ENC (Search.BC.left root)
  right : DigAt t (ENC + 48) (Search.BC.right root)
  c32 : (t.getMem (BitVec.ofNat 64 (ENC + 32))).toNat < 2 ^ 32
theorem signLayers_low (cache : Cache) (index : Nat) {lay : Layer} (hlay : lay ≠ 0) (msg : WCT9.LayerMsg) :
    signLayersP leafFn cache index (lay.val + 1) msg = (do
      let some (_, digits) ← WCT9.layerCounterSearch lay (route index lay).2 (route index lay).1 msg 0
        (WCT9.searchLimit lay)
        | pure none
      let (levels, values) ← Packed.buildTreeP leafFn lay (route index lay).2 (route index lay).1 digits
      let some previous ← signLayersP leafFn cache index lay.val (.pair (WCT9.topPair lay levels).1 (WCT9.topPair lay levels).2) | pure none
      pure (some (previous ++ [(values, (List.range (height lay)).map fun j =>
        (levels.getD j []).getD ((route index lay).1 / 2 ^ j ^^^ 1) 0)]))) := by
  fin_cases lay
  · exact absurd rfl hlay
  all_goals rfl
section layer
variable {sk : SecretKey} {cache : Bytes 131072}
-- (witness stack) removed: legacy reference-image lower tree (LeafW now covers CHAIN+32..112; no users).
theorem entry2 {index : Nat} {root : WCT9.LayerMsg} {v : MachineState} (h : LayNext sk cache 397 index root v) :
    ∃ t, Steps image v 14 14 t ∧ LayEntry sk cache 2 index root t ∧ Frame v t (fun _ => False) := by
  obtain ⟨t, st, tpc, tx1, tx8, tx15, tx16, tx17, tx18, tx14, tx9, tr, tf⟩ := blk397_spec v h.pc index h.hidx h.idx
  have g : ∀ r, r ∉ [.x1, .x6, .x7, .x8, .x9, .x14, .x15, .x16, .x17, .x18, .x28] → t.getReg r = v.getReg r :=
    fun r hr => tr.get hr
  refine ⟨t, st, ?_, tf⟩
  exact
    { pc := tpc
      x1 := tx1
      x2 := by rw [g _ (by decide), h.x2]
      x8 := tx8
      x9 := by rw [tx9, route_2]
      x14 := by rw [tx14, route_2]
      x15 := tx15
      x16 := tx16
      x17 := tx17
      x18 := by rw [tx18, route_2]
      x26 := by rw [g _ (by decide), h.x26]
      x27 := by rw [g _ (by decide), h.x27]
      x31 := by rw [g _ (by decide), h.x31]
      base := h.base.frame tf tr (by decide) (fun _ _ _ h => h)
      hlay := by decide
      hidx := h.hidx
      idx := by rw [tf.get (by packed_sgo) (fun h => h)]; exact h.idx
      enc := h.enc.frame tf (by packed_sgo) (fun h => h) (fun h => h)
      right := h.right.frame tf (by packed_sgo) (fun h => h) (fun h => h)
      c32 := by rw [tf.get (by packed_sgo) (fun h => h)]; exact h.c32 }
theorem entry1 {index : Nat} {root : WCT9.LayerMsg} {v : MachineState} (h : LayNext sk cache 412 index root v) :
    ∃ t, Steps image v 14 14 t ∧ LayEntry sk cache 1 index root t ∧ Frame v t (fun _ => False) := by
  obtain ⟨t, st, tpc, tx1, tx8, tx15, tx16, tx17, tx18, tx14, tx9, tr, tf⟩ := blk412_spec v h.pc index h.hidx h.idx
  have g : ∀ r, r ∉ [.x1, .x6, .x7, .x8, .x9, .x14, .x15, .x16, .x17, .x18, .x28] → t.getReg r = v.getReg r :=
    fun r hr => tr.get hr
  refine ⟨t, st, ?_, tf⟩
  exact
    { pc := tpc
      x1 := tx1
      x2 := by rw [g _ (by decide), h.x2]
      x8 := tx8
      x9 := by rw [tx9, route_1]
      x14 := by rw [tx14, route_1]
      x15 := tx15
      x16 := tx16
      x17 := tx17
      x18 := by rw [tx18, route_1]
      x26 := by rw [g _ (by decide), h.x26]
      x27 := by rw [g _ (by decide), h.x27]
      x31 := by rw [g _ (by decide), h.x31]
      base := h.base.frame tf tr (by decide) (fun _ _ _ h => h)
      hlay := by decide
      hidx := h.hidx
      idx := by rw [tf.get (by packed_sgo) (fun h => h)]; exact h.idx
      enc := h.enc.frame tf (by packed_sgo) (fun h => h) (fun h => h)
      right := h.right.frame tf (by packed_sgo) (fun h => h) (fun h => h)
      c32 := by rw [tf.get (by packed_sgo) (fun h => h)]; exact h.c32 }
theorem layer0_link (hL0 : L0Spec leafFn sk cache) {index : Nat} {root : WCT9.LayerMsg} {v : MachineState}
    (h : LayNext sk cache 427 index root v) :
    TBSim image sk v L0Cost (signLayersP leafFn (cacheDec cache) index 1 root) (SLPost v 1) := by
  refine TBSim.mono (hL0 index root v ⟨h.pc, h.base, h.hidx, h.idx, h.enc, h.right, h.c32⟩) le_rfl (fun r u hu => ?_)
  rcases r with _ | ps
  · exact hu
  obtain ⟨vals, path, rfl, uh, uv, up, uf⟩ := hu
  refine ⟨uh, rfl, fun lay hlay => ?_, uf.mono (fun A _ hA => hA)⟩
  have h0 : lay = 0 := Fin.ext (by omega)
  subst h0
  refine ⟨fun i hi => ?_, fun j hj => ?_⟩
  · have := uv i hi
    rw [show SIG + 2192 + 16 * i = SIG + 16 * (layIdx 0 + i) by simp [layIdx]; ring] at this
    exact this
  · have := up j hj
    rw [show SIG + 3056 + 16 * j = SIG + 16 * (layIdx 0 + chainCount 0 + j) by simp [layIdx, chainCount]; ring]
      at this
    exact this
def layW1 : Nat := L0Cost
def layW2 : Nat := 14 + (csCost 1 + (1 + (btCost + layW1)))
def layW3 : Nat := 14 + (csCost 2 + (1 + (btCost + layW2)))
def layersC : Nat := csCost 3 + (1 + (btCost + layW3))
-- (witness stack) removed: legacy reference-image lower tree (LeafW now covers CHAIN+32..112; no users).
end layer
end SigGolfCandidate.T3M.Sign.Packed.Boundary
end
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
theorem signLayers_one (cache : Cache) (index : Nat) (root : WCT9.LayerMsg) :
    signLayersP leafFn cache index 1 root = (do
      let found ← WCT9.layerCounterSearch 0 (route index 0).2 (route index 0).1 root 0 (WCT9.searchLimit 0)
      let part ← signTop cache (route index 0).1 ((found.map Prod.snd).getD T3.dummyTop)
      pure (some [part])) := by
  simp only [signLayersP, Fin.ofNat_zero, if_true]
  try rfl
theorem route_0 {index : Nat} (h : index < 2 ^ 31) : route index 0 = (index / 2 ^ 19 % 4096, 0) := by
  show (index / 2 ^ 19 % 2 ^ 12, index / 2 ^ (19 + 12)) = _
  rw [Nat.div_eq_of_lt (by omega : index < 2 ^ (19 + 12))]
  rfl
def tl0 (leaf : Nat) (ds : List Nat) (dest : Nat) : LeafArgs :=
  ⟨0, 0, leaf, ds, true, DIGITS, SIG + 2192, dest, 447⟩
section top
variable {sk : SecretKey} {cache : Bytes 131072}
theorem leafPreS_of {s : MachineState} {A : LeafArgs} (hb : Base sk cache s) (hlay : A.lay = 0) (hso : A.so = true)
    (h1 : s.getReg .x1 = pcOf A.ret) (h8 : s.getReg .x8 = BitVec.ofNat 64 0)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 A.tree) (h18 : s.getReg .x18 = BitVec.ofNat 64 A.leaf)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 A.digp) (h23 : s.getReg .x23 = BitVec.ofNat 64 A.valp)
    (h25 : s.getReg .x25 = BitVec.ofNat 64 A.dest) (h26 : s.getReg .x26 = BitVec.ofNat 64 54)
    (h27 : s.getReg .x27 = BitVec.ofNat 64 51) (h31 : s.getReg .x31 = BitVec.ofNat 64 (if A.so then 1 else 0))
    (htree : A.tree < 2 ^ 32) (hleaf : A.leaf < 2 ^ 32)
    (hdig : ∀ i < 54, s.getByte (BitVec.ofNat 64 (A.digp + i)) = BitVec.ofNat 8 (A.d i))
    (hdigb : ∀ i < 54, A.d i < 256 ∧ (A.so = false → A.d i ≤ maxDigit 0 i))
    (hdigp : A.digp + 54 ≤ 2 ^ 24) (hdigW : ∀ i < 54, ¬ LeafW A ((A.digp + i) / 8 * 8))
    (hdigC : A.digp + 54 ≤ 0x201C0 ∨ 0x20210 ≤ A.digp)
    (hv8 : A.valp % 8 = 0) (hv : A.valp + 16 * 54 ≤ 2 ^ 24)
    (hvs : A.valp + 16 * 54 ≤ PRIV ∨ LEAFPK + 960 ≤ A.valp) (hd8 : A.so = false → A.dest % 8 = 0)
    (hd : A.dest + 16 ≤ 2 ^ 24) (hds : A.dest + 16 ≤ PRIV ∨ LEAFPK + 960 ≤ A.dest ∨ (CHAIN + 80 ≤ A.dest ∧ A.dest + 16 ≤ LOUT))
    (hdv : A.dest + 16 ≤ A.valp ∨ A.valp + 16 * 54 ≤ A.dest)
    (hroute : A.tree * 2 ^ height A.lay + A.leaf < 2 ^ 31)
    (hleafHeight : A.leaf < 2 ^ height A.lay)
    (hsteps : ∀ i < A.n, A.e i ≤ 8) : LeafPreS sk s A := by
  have hn : A.n = 54 := by show chainCount A.lay = 54; rw [hlay]; rfl
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
structure TopRegs (leaf : Nat) (s : MachineState) : Prop where
  x8 : s.getReg .x8 = BitVec.ofNat 64 0
  x9 : s.getReg .x9 = BitVec.ofNat 64 0
  x14 : s.getReg .x14 = BitVec.ofNat 64 leaf
  x26 : s.getReg .x26 = BitVec.ofNat 64 54
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
    (hv : A.valp + 16 * 54 ≤ SIG ∨ (SIG + 2192 ≤ A.valp ∧ A.valp + 16 * 54 ≤ SIG + 3248) ∨ SIG + 5616 ≤ A.valp)
    (hd : A.dest + 16 ≤ SIG ∨ (SIG + 2192 ≤ A.dest ∧ A.dest + 16 ≤ SIG + 3248) ∨ SIG + 5616 ≤ A.dest) :
    ∀ X, (LeafW A X ∨ TopScr X) → L0W X := by
  have hn : A.n = 54 := by show chainCount A.lay = 54; rw [hlay]; rfl
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
  /-- (witness stack) the F pads `CHAIN+32/40` are not tracked: the top leaf's G chains (even `i ≤ 52`) write them. -/
  zero : ∀ A < 2 ^ 64, NeverW A → A ≠ CHAIN + 32 → A ≠ CHAIN + 40 → t.getMem (BitVec.ofNat 64 A) = 0
theorem StateBase.frame {sk : SecretKey} {cache : Bytes 131072} {t u : MachineState} {W : Nat → Prop}
    {l : List Reg} (h : StateBase sk cache t) (hf : Frame t u W) (hr : RegsExcept t u l) (h5 : .x5 ∉ l)
    (hW : ∀ A, A < 2 ^ 64 → BaseA A → ¬ W A) : StateBase sk cache u := by
  have g : ∀ A, A < 2 ^ 64 → BaseA A → u.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) :=
    fun A hA hb => hf.get hA (hW A hA hb)
  refine ⟨by rw [hr.get h5, h.x5], ?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_, fun A hA hn h32 h40 => ?_⟩
  · rw [g _ (by sg_omega) (by unfold BaseA; simp), h.p0]
  · rw [g _ (by sg_omega) (by unfold BaseA; simp), h.p8]
  · rw [g _ (by sg_omega) (by unfold BaseA; simp), h.p32]
  · rw [g _ (by sg_omega) (by unfold BaseA; simp), h.p40]
  · rw [g _ (by sg_omega) (by unfold BaseA; simp), h.p48]
  · rw [g _ (by sg_omega) (by unfold BaseA; simp), h.p56]
  · rw [g _ (by sg_omega) (by unfold BaseA; right; right; right; right; right; right; left; sg_omega),
      h.region k hk]
  · rw [g _ hA (by unfold BaseA; right; right; right; right; right; right; right; left; exact hn), h.zero A hA hn h32 h40]

/-- `StateBase.frame` when the only base cells written are the untracked F pads `CHAIN+32/40`. -/
theorem StateBase.frame_pads {sk : SecretKey} {cache : Bytes 131072} {t u : MachineState} {W : Nat → Prop}
    {l : List Reg} (h : StateBase sk cache t) (hf : Frame t u W) (hr : RegsExcept t u l) (h5 : .x5 ∉ l)
    (hW : ∀ A, A < 2 ^ 64 → BaseA A → W A → A = CHAIN + 32 ∨ A = CHAIN + 40) : StateBase sk cache u := by
  have g : ∀ A, A < 2 ^ 64 → BaseA A → A ≠ CHAIN + 32 → A ≠ CHAIN + 40 →
      u.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) :=
    fun A hA hb h32 h40 => hf.get hA (fun hw => by rcases hW A hA hb hw with h' | h' <;> contradiction)
  refine ⟨by rw [hr.get h5, h.x5], ?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_, fun A hA hn h32 h40 => ?_⟩
  · rw [g _ (by sg_omega) (by unfold BaseA; simp) (by packed_sgo) (by packed_sgo), h.p0]
  · rw [g _ (by sg_omega) (by unfold BaseA; simp) (by packed_sgo) (by packed_sgo), h.p8]
  · rw [g _ (by sg_omega) (by unfold BaseA; simp) (by packed_sgo) (by packed_sgo), h.p32]
  · rw [g _ (by sg_omega) (by unfold BaseA; simp) (by packed_sgo) (by packed_sgo), h.p40]
  · rw [g _ (by sg_omega) (by unfold BaseA; simp) (by packed_sgo) (by packed_sgo), h.p48]
  · rw [g _ (by sg_omega) (by unfold BaseA; simp) (by packed_sgo) (by packed_sgo), h.p56]
  · rw [g _ (by sg_omega) (by unfold BaseA; right; right; right; right; right; right; left; sg_omega)
      (by packed_sgo) (by packed_sgo), h.region k hk]
  · rw [g _ hA (by unfold BaseA; right; right; right; right; right; right; right; left; exact hn) h32 h40,
      h.zero A hA hn h32 h40]

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
    (h25 : s.getReg .x25 = BitVec.ofNat 64 A.dest) (h26 : s.getReg .x26 = BitVec.ofNat 64 54)
    (h27 : s.getReg .x27 = BitVec.ofNat 64 51) (h31 : s.getReg .x31 = BitVec.ofNat 64 (if A.so then 1 else 0))
    (htree : A.tree < 2 ^ 32) (hleaf : A.leaf < 2 ^ 32)
    (hdig : ∀ i < 54, s.getByte (BitVec.ofNat 64 (A.digp + i)) = BitVec.ofNat 8 (A.d i))
    (hdigb : ∀ i < 54, A.d i < 256 ∧ (A.so = false → A.d i ≤ maxDigit 0 i))
    (hdigp : A.digp + 54 ≤ 2 ^ 24) (hdigW : ∀ i < 54, ¬ LeafW A ((A.digp + i) / 8 * 8))
    (hdigC : A.digp + 54 ≤ 0x201C0 ∨ 0x20210 ≤ A.digp)
    (hv8 : A.valp % 8 = 0) (hv : A.valp + 16 * 54 ≤ 2 ^ 24)
    (hvs : A.valp + 16 * 54 ≤ PRIV ∨ LEAFPK + 960 ≤ A.valp) (hd8 : A.so = false → A.dest % 8 = 0)
    (hd : A.dest + 16 ≤ 2 ^ 24) (hds : A.dest + 16 ≤ PRIV ∨ LEAFPK + 960 ≤ A.dest ∨ (CHAIN + 80 ≤ A.dest ∧ A.dest + 16 ≤ LOUT))
    (hdv : A.dest + 16 ≤ A.valp ∨ A.valp + 16 * 54 ≤ A.dest)
    (hroute : A.tree * 2 ^ height A.lay + A.leaf < 2 ^ 31)
    (hleafHeight : A.leaf < 2 ^ height A.lay)
    (hsteps : ∀ i < A.n, A.e i ≤ 8) : LeafPreS sk s A := by
  have hn : A.n = 54 := by show chainCount A.lay = 54; rw [hlay]; rfl
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
      z0 := hb.zero _ (by packed_sgo) (by unfold NeverW; simp) (by packed_sgo) (by packed_sgo)
      z8 := hb.zero _ (by packed_sgo) (by unfold NeverW; simp) (by packed_sgo) (by packed_sgo)
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
    (hvB : A.valp + 16 * 54 ≤ PRIV ∨ LEAFPK + 960 ≤ A.valp) (hvR : A.valp + 16 * 54 ≤ REGION ∨ REGION + 131040 ≤ A.valp)
    (hdB : A.dest + 16 ≤ PRIV) (hdZ : A.dest + 16 ≤ ZDIG ∨ ZDIG + 64 ≤ A.dest)
    (hvZ : A.valp + 16 * 54 ≤ ZDIG ∨ ZDIG + 64 ≤ A.valp)
    (hvT : A.valp + 16 * 54 ≤ 16691072) : SharedTopPath.StateBase sk cache t := by
  have hn : A.n = 54 := by show chainCount A.lay = 54; rw [hlay]; rfl
  refine hb.frame_pads hf hr (by decide) (fun X _ hB hW => ?_)
  unfold BaseA NeverW Search.TOP_DATA at hB
  rcases hW with hW | hW
  · unfold LeafW at hW
    rw [hn, if_pos hlay] at hW
    packed_sgo
  · unfold TopScr at hW
    packed_sgo
def topLeafC : Nat := 305000
def LeafSpec (im : Image) : Prop :=
  ∀ (sk : SecretKey) (A : LeafArgs) (s : MachineState),
    A.lay = 0 → A.so = true → A.tree = 0 → (∀ i < A.n, A.d i ≤ SigGolfCandidate.T3.maxDigit 0 i) →
    A.valp + 16*A.n ≤ 0x60000 → A.digp+A.n ≤ 0x60000 → A.dest+16 ≤ 0x60000 →
    LeafPreS sk s A → s.pc=pcOf (1013+27) →
    TBSim im sk s topLeafC (SigGolfCandidate.T3.buildLeafTop A.leaf A.digits A.so)
      (fun r t => t.pc=pcOf A.ret ∧ DigsAt t A.valp r.2 ∧ r.2.length=A.n ∧
        RegsExcept s t leafRegs ∧ Frame s t (fun X => LeafW A X ∨ SigGolfCandidate.T3M.Sign.Packed.TopScr X))

def Post (s : MachineState) (p : Pieces) (t : MachineState) : Prop :=
  t.pc=pcOf 540 ∧ (∀ i<54,DigAt t (SIG+2192+16*i) (p.1.getD i 0)) ∧
    (∀ j<12,DigAt t (SIG+3056+16*j) (p.2.getD j 0)) ∧ Frame s t L0W ∧
    (∀ A, (A=0x66000 ∨ A=0x66008) → t.getMem (BitVec.ofNat 64 A)=s.getMem (BitVec.ofNat 64 A))

theorem top_only (hcode : SharedTopBlocks.Code im) (hTop : LeafSpec im)
    (leaf : Nat) (hl : leaf<4096) (ds : List Nat) (u : MachineState) (upc : u.pc=pcOf 441)
    (hbu : SharedTopPath.StateBase sk cache u) (hregs : TopRegs leaf u)
    (h18 : u.getReg .x18=BitVec.ofNat 64 leaf) (hx25 : (u.getReg .x25).toNat≤201)
    (hdm : ∀ i<54,ds.getD i 0≤SigGolfCandidate.T3.maxDigit 0 i)
    (udig : ∀ i<54,u.getByte (BitVec.ofNat 64 (DIGITS+i))=BitVec.ofNat 8 (ds.getD i 0)) :
    TBSim im sk u (topLeafC+30006) (signTop (cacheDec cache) leaf ds) (Post u) := by
  have hd7 : ∀ i<54,ds.getD i 0≤7 := fun i hi =>
    (hdm i hi).trans (by unfold SigGolfCandidate.T3.maxDigit; split_ifs <;> omega)
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
      (by show DIGITS + 54 ≤ 2 ^ 24; packed_sgo) (fun i hi => by unfold LeafW; simp only [tl0, LeafArgs.n, chainCount, Matrix.cons_val_zero, ↓reduceIte]; packed_sgo)
      (Or.inr (by show 0x20210 ≤ DIGITS; packed_sgo))
      (by show (SIG + 2192) % 8 = 0; packed_sgo) (by show SIG + 2192 + 16 * 54 ≤ 2 ^ 24; packed_sgo)
      (Or.inl (by show SIG + 2192 + 16 * 54 ≤ PRIV; packed_sgo)) (fun h => by simp [tl0] at h)
      (by show dest0 + 16 ≤ 2 ^ 24; omega) (Or.inl (by show dest0 + 16 ≤ PRIV; packed_sgo))
      (Or.inl (by show dest0 + 16 ≤ SIG + 2192; packed_sgo))
      (by change 0 * 2 ^ 12 + leaf < 2 ^ 31; omega)
      (by change leaf < 4096; omega)
      (fun i hi => by have := hd7 i hi; change ds.getD i 0 ≤ 8; omega)
  have hL0 := hTop sk (tl0 leaf ds dest0) u1 rfl rfl rfl hdm (by show SIG + 2192 + 16 * 54 ≤ 0x60000; packed_sgo)
    (by show DIGITS + 54 ≤ 0x60000; packed_sgo) (by show dest0 + 16 ≤ 0x60000; omega) hp0 u1pc
  try dsimp only
  rw [signTop]
  refine TBSim.mono (TBSim.steps su1 (TBSim.bind (W₂ := 30000) hL0 (fun r0 v0 hv0 => ?_)))
    (Nat.le_of_eq (by ring)) (fun _ _ h => h)
  obtain ⟨root0, values⟩ := r0
  obtain ⟨v0pc, v0vals, v0len, v0r, v0f⟩ := hv0
  have hbv0 : SharedTopPath.StateBase sk cache v0 := base_leaf hbu1 rfl v0f v0r (Or.inl (by show SIG + 2192 + 16 * 54 ≤ PRIV; packed_sgo))
    (Or.inl (by show SIG + 2192 + 16 * 54 ≤ REGION; packed_sgo)) (by show dest0 + 16 ≤ PRIV; packed_sgo)
    (Or.inl (by show dest0 + 16 ≤ ZDIG; packed_sgo)) (Or.inl (by show SIG + 2192 + 16 * 54 ≤ ZDIG; packed_sgo))
    (by show SIG + 2192 + 16 * 54 ≤ 16691072; packed_sgo)
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
