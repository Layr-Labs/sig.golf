import SigGolfCandidate.ClaudeR3.Data
import Mathlib.Data.Nat.Choose.Basic
import SigGolfCandidate.ClaudeR3.Tables

section
namespace ClaudeR3.Ev
open ClaudeR3.Tab (levs tabM tabN tabS)
open ClaudeR3.BonfData

noncomputable def lsum {α : Type} (f : α → ℕ) (l : List α) : ℕ := List.rec 0 (fun a _ ih => f a + ih) l

noncomputable def nsum (n : ℕ) (f : ℕ → ℕ) : ℕ := Nat.rec 0 (fun i ih => f i + ih) n

def dig (k l : ℕ) : ℕ := k / 1024 ^ l % 1024

def extC : ℕ → ℕ
  | 0 => 2
  | 1 => 72
  | 2 => 52
  | 3 => 2
  | _ => 0

noncomputable def dsumN (key : ℕ) : ℕ := nsum 15 fun l => dig key l
noncomputable def rhoN (key x : ℕ) : ℕ := nsum 15 fun l => dig key l * x ^ l
noncomputable def RtN (x : ℕ) : ℕ := lsum (fun l => x ^ l) levs
noncomputable def EtN (x : ℕ) : ℕ := nsum 4 fun e => extC e * x ^ e
noncomputable def AN (e x : ℕ) : ℕ := (EtN x - x ^ e) * RtN x
noncomputable def AN2 (e f x : ℕ) : ℕ := (EtN x - x ^ e - x ^ f) * RtN x

noncomputable def posT (tab : List (ℕ × ℤ)) : List (ℕ × ℕ) :=
  List.rec [] (fun a _ ih => @Int.rec (fun _ => List (ℕ × ℕ)) (fun n => (a.1, n) :: ih) (fun _ => ih) a.2) tab

noncomputable def negT (tab : List (ℕ × ℤ)) : List (ℕ × ℕ) :=
  List.rec [] (fun a _ ih => @Int.rec (fun _ => List (ℕ × ℕ)) (fun _ => ih) (fun n => (a.1, n + 1) :: ih) a.2) tab

structure SN where
  s0 : ℕ
  s1x : ℕ
  s1y : ℕ
  s2 : ℕ

noncomputable def aB (base j : ℕ) (a : ℕ × ℕ) : ℕ := a.2 * (base + dsumN a.1) ^ j

noncomputable def sumsN (tab : List (ℕ × ℕ)) (base j x y : ℕ) : SN :=
  ⟨lsum (fun a => aB base j a) tab,
    lsum (fun a => aB base j a * rhoN a.1 x) tab,
    nsum 15 fun l => y ^ l * lsum (fun a => aB base j a * dig a.1 l) tab,
    nsum 15 fun l => y ^ l * lsum (fun a => aB base j a * dig a.1 l * rhoN a.1 x) tab⟩

noncomputable def combineN (S : SN) (x y : ℕ) : ℕ :=
  nsum 4 fun e => extC e *
    (AN e x * AN e y * S.s0 + AN e x * y ^ e * S.s1y + x ^ e * AN e y * S.s1x + x ^ e * y ^ e * S.s2)

noncomputable def famP (tab : List (ℕ × ℤ)) (k L x : ℕ) : ℕ := combineN (sumsN (posT tab) 71501 k x (x ^ L)) x (x ^ L)
noncomputable def famN (tab : List (ℕ × ℤ)) (k L x : ℕ) : ℕ := combineN (sumsN (negT tab) 71501 k x (x ^ L)) x (x ^ L)

noncomputable def sums1N (tab : List (ℕ × ℕ)) (base j : ℕ) : SN :=
  ⟨lsum (fun a => aB base j a) tab,
    lsum (fun a => aB base j a * dsumN a.1) tab,
    lsum (fun a => aB base j a * dsumN a.1) tab,
    lsum (fun a => aB base j a * dsumN a.1 * dsumN a.1) tab⟩

noncomputable def famP1 (tab : List (ℕ × ℤ)) (k : ℕ) : ℕ := combineN (sums1N (posT tab) 71501 k) 1 1
noncomputable def famN1 (tab : List (ℕ × ℤ)) (k : ℕ) : ℕ := combineN (sums1N (negT tab) 71501 k) 1 1

noncomputable def nineN (e f x y : ℕ) (P Q : SN) : ℕ :=
  AN2 e f x * AN2 e f y * P.s0 * Q.s0 + AN2 e f x * y ^ e * P.s1y * Q.s0 + AN2 e f x * y ^ f * P.s0 * Q.s1y
    + x ^ e * AN2 e f y * P.s1x * Q.s0 + x ^ e * y ^ e * P.s2 * Q.s0 + x ^ e * y ^ f * P.s1x * Q.s1y
    + x ^ f * AN2 e f y * P.s0 * Q.s1x + x ^ f * y ^ e * P.s1y * Q.s1x + x ^ f * y ^ f * P.s0 * Q.s2

def nPairN (e f : ℕ) : ℕ := extC e * extC f - if e = f then extC e else 0

noncomputable def dTerm (t₁ t₂ : List (ℕ × ℕ)) (k L x j : ℕ) : ℕ :=
  nsum 4 fun e => nsum 4 fun f => nPairN e f *
    nineN e f x (x ^ L) (sumsN t₁ 70938 j x (x ^ L)) (sumsN t₂ 0 (k - j) x (x ^ L))

noncomputable def famDP (tab : List (ℕ × ℤ)) (k L x : ℕ) : ℕ :=
  nsum (k + 1) fun j => k.choose j * (dTerm (posT tab) (posT tab) k L x j + dTerm (negT tab) (negT tab) k L x j)
noncomputable def famDN (tab : List (ℕ × ℤ)) (k L x : ℕ) : ℕ :=
  nsum (k + 1) fun j => k.choose j * (dTerm (posT tab) (negT tab) k L x j + dTerm (negT tab) (posT tab) k L x j)

noncomputable def WvF (tab : List (ℕ × ℤ)) (k B : ℕ) : ℕ := famP tab k 154 B - famN tab k 154 B
noncomputable def WvF1 (tab : List (ℕ × ℤ)) (k : ℕ) : ℕ := famP1 tab k - famN1 tab k
noncomputable def Wv2F (k B : ℕ) : ℕ :=
  (famP tabS k 154 B + famDP tabM k 154 B) - (famN tabS k 154 B + famDN tabM k 154 B)

def nsumRF (n : ℕ) (f : ℕ → ℕ) : ℕ := (List.range n).foldr (fun i s => f i + s) 0
def maskVF (n₁ n₂ B : ℕ) : ℕ := nsumRF n₁ (fun i => B ^ i) * nsumRF n₂ (fun j => B ^ (154 * j))
def NtopF : ℕ := 153 + 154 * 153
def bonfNF (P1 PB A r' B : ℕ) : ℕ :=
  (P1 + r'.choose 2 * (PB * maskVF (153 - A) (153 - A) B / B ^ NtopF % B)) -
    r' * (PB * maskVF (153 - A) 154 B / B ^ NtopF % B)

noncomputable def meanCheckF (r : ℕ) : Bool :=
  decide (WvF1 tabM (r - 2) ^ 9 * ((153 - 104) * 154) < 2 ^ meanBB.getD r 0) &&
    Nat.ble (bonfNF (WvF1 tabM (r - 2) ^ 9) (WvF tabM (r - 2) (2 ^ meanBB.getD r 0) ^ 9) 104 (meanRp.getD r 0)
      (2 ^ meanBB.getD r 0)) (meanD.getD r 0)

noncomputable def nearCheckF (r : ℕ) : Bool :=
  decide (9 * (WvF1 tabM (r - 2) ^ 8 * WvF1 tabN (r - 2)) * ((153 - 104) * 154) < 2 ^ nearBB.getD r 0) &&
    Nat.ble (bonfNF (9 * (WvF1 tabM (r - 2) ^ 8 * WvF1 tabN (r - 2)))
      (9 * (WvF tabM (r - 2) (2 ^ nearBB.getD r 0) ^ 8 * WvF tabN (r - 2) (2 ^ nearBB.getD r 0))) 104
      (nearRp.getD r 0) (2 ^ nearBB.getD r 0)) (nearD.getD r 0)

noncomputable def diagCheckF (r : ℕ) : Bool :=
  decide (Wv2F (r - 2) 1 ^ 9 * ((153 - 104) * 154) < 2 ^ diagBB.getD r 0) &&
    Nat.ble (bonfNF (Wv2F (r - 2) 1 ^ 9) (Wv2F (r - 2) (2 ^ diagBB.getD r 0) ^ 9) 104 (diagRp.getD r 0)
      (2 ^ diagBB.getD r 0)) (diagD.getD r 0)

end ClaudeR3.Ev
end

section
namespace ClaudeR3.Ev
open ClaudeR3.Tab (tabM)

def sidx (l m : ℕ) : ℕ := 16 + 15 * l - l * (l - 1) / 2 + (m - l)

noncomputable def tq0 (t : List (ℕ × ℕ)) (base j : ℕ) : ℕ := lsum (fun a => aB base j a) t
noncomputable def tq1 (t : List (ℕ × ℕ)) (base j l : ℕ) : ℕ := lsum (fun a => aB base j a * dig a.1 l) t
noncomputable def tq2 (t : List (ℕ × ℕ)) (base j l m : ℕ) : ℕ :=
  lsum (fun a => aB base j a * dig a.1 l * dig a.1 m) t

noncomputable def tqOk (t : List (ℕ × ℕ)) (base j : ℕ) (lit : List ℕ) : Bool :=
  (tq0 t base j == lit.getD 0 0) &&
    ((List.range 15).all fun l => tq1 t base j l == lit.getD (1 + l) 0) &&
    ((List.range 15).all fun l => (List.range (15 - l)).all fun i =>
      tq2 t base j l (l + i) == lit.getD (sidx l (l + i)) 0)

end ClaudeR3.Ev
end

section
namespace ClaudeR3.Ev
open ClaudeR3.Tab (tabM tabS)
open ClaudeR3.BonfData

noncomputable def sumsL (lit : List ℕ) (x y : ℕ) : SN :=
  ⟨lit.getD 0 0,
    nsum 15 fun m => x ^ m * lit.getD (1 + m) 0,
    nsum 15 fun l => y ^ l * lit.getD (1 + l) 0,
    nsum 15 fun l => y ^ l * nsum 15 fun m => x ^ m * lit.getD (sidx (min l m) (max l m)) 0⟩

noncomputable def dTermL (P Q : List (List ℕ)) (k L x j : ℕ) : ℕ :=
  nsum 4 fun e => nsum 4 fun f => nPairN e f *
    nineN e f x (x ^ L) (sumsL (P.getD j []) x (x ^ L)) (sumsL (Q.getD (k - j) []) x (x ^ L))

noncomputable def famDPL0 (k L x : ℕ) : ℕ :=
  nsum (k + 1) fun j => k.choose j * (dTermL tqPA tqPB k L x j + dTermL tqNA tqNB k L x j)
noncomputable def famDNL0 (k L x : ℕ) : ℕ :=
  nsum (k + 1) fun j => k.choose j * (dTermL tqPA tqNB k L x j + dTermL tqNA tqPB k L x j)

structure N9 where
  c0 : ℕ
  c1 : ℕ
  c2 : ℕ
  c3 : ℕ
  c4 : ℕ
  c5 : ℕ
  c6 : ℕ
  c7 : ℕ
  c8 : ℕ

def pairsN (P Q : SN) : N9 :=
  ⟨P.s0 * Q.s0, P.s1y * Q.s0, P.s0 * Q.s1y, P.s1x * Q.s0, P.s2 * Q.s0, P.s1x * Q.s1y, P.s0 * Q.s1x,
    P.s1y * Q.s1x, P.s0 * Q.s2⟩

noncomputable def nine9 (e f x y : ℕ) (c : N9) : ℕ :=
  AN2 e f x * AN2 e f y * c.c0 + AN2 e f x * y ^ e * c.c1 + AN2 e f x * y ^ f * c.c2
    + x ^ e * AN2 e f y * c.c3 + x ^ e * y ^ e * c.c4 + x ^ e * y ^ f * c.c5
    + x ^ f * AN2 e f y * c.c6 + x ^ f * y ^ e * c.c7 + x ^ f * y ^ f * c.c8

noncomputable def convN (P Q : List (List ℕ)) (k L x : ℕ) : N9 :=
  let g := fun j => pairsN (sumsL (P.getD j []) x (x ^ L)) (sumsL (Q.getD (k - j) []) x (x ^ L))
  ⟨nsum (k + 1) fun j => k.choose j * (g j).c0, nsum (k + 1) fun j => k.choose j * (g j).c1,
    nsum (k + 1) fun j => k.choose j * (g j).c2, nsum (k + 1) fun j => k.choose j * (g j).c3,
    nsum (k + 1) fun j => k.choose j * (g j).c4, nsum (k + 1) fun j => k.choose j * (g j).c5,
    nsum (k + 1) fun j => k.choose j * (g j).c6, nsum (k + 1) fun j => k.choose j * (g j).c7,
    nsum (k + 1) fun j => k.choose j * (g j).c8⟩

noncomputable def dSumL (P Q : List (List ℕ)) (k L x : ℕ) : ℕ :=
  nsum 4 fun e => nsum 4 fun f => nPairN e f * nine9 e f x (x ^ L) (convN P Q k L x)

noncomputable def famDPL (k L x : ℕ) : ℕ := dSumL tqPA tqPB k L x + dSumL tqNA tqNB k L x
noncomputable def famDNL (k L x : ℕ) : ℕ := dSumL tqPA tqNB k L x + dSumL tqNA tqPB k L x

noncomputable def Wv2L (k B : ℕ) : ℕ :=
  (famP tabS k 154 B + famDPL k 154 B) - (famN tabS k 154 B + famDNL k 154 B)

noncomputable def Wv2L1 (k : ℕ) : ℕ :=
  (famP1 tabS k + famDPL k 154 1) - (famN1 tabS k + famDNL k 154 1)

noncomputable def diagCheckL (r : ℕ) : Bool :=
  decide (Wv2L1 (r - 2) ^ 9 * ((153 - 104) * 154) < 2 ^ diagBB.getD r 0) &&
    Nat.ble (bonfNF (Wv2L1 (r - 2) ^ 9) (Wv2L (r - 2) (2 ^ diagBB.getD r 0) ^ 9) 104 (diagRp.getD r 0)
      (2 ^ diagBB.getD r 0)) (diagD.getD r 0)

end ClaudeR3.Ev
end

section
namespace ClaudeR3.Ev

set_option maxRecDepth 100000
theorem meanF_r2 : meanCheckF 2 = true := by decide +kernel
theorem meanF_r3 : meanCheckF 3 = true := by decide +kernel
theorem meanF_r4 : meanCheckF 4 = true := by decide +kernel
theorem meanF_r5 : meanCheckF 5 = true := by decide +kernel
theorem meanF_r6 : meanCheckF 6 = true := by decide +kernel
theorem meanF_r7 : meanCheckF 7 = true := by decide +kernel
theorem meanF_r8 : meanCheckF 8 = true := by decide +kernel
theorem meanF_r9 : meanCheckF 9 = true := by decide +kernel
theorem meanF_r10 : meanCheckF 10 = true := by decide +kernel
theorem meanF_r11 : meanCheckF 11 = true := by decide +kernel
theorem meanF_r12 : meanCheckF 12 = true := by decide +kernel
theorem meanF_r13 : meanCheckF 13 = true := by decide +kernel
theorem meanF_r14 : meanCheckF 14 = true := by decide +kernel
theorem meanF_r15 : meanCheckF 15 = true := by decide +kernel
theorem meanF_r16 : meanCheckF 16 = true := by decide +kernel
theorem meanF_r17 : meanCheckF 17 = true := by decide +kernel
theorem meanF_r18 : meanCheckF 18 = true := by decide +kernel
theorem meanF_r19 : meanCheckF 19 = true := by decide +kernel
theorem meanF_r20 : meanCheckF 20 = true := by decide +kernel

end ClaudeR3.Ev
end

section
namespace ClaudeR3.Ev

set_option maxRecDepth 100000
theorem nearF_r2 : nearCheckF 2 = true := by decide +kernel
theorem nearF_r3 : nearCheckF 3 = true := by decide +kernel
theorem nearF_r4 : nearCheckF 4 = true := by decide +kernel
theorem nearF_r5 : nearCheckF 5 = true := by decide +kernel
theorem nearF_r6 : nearCheckF 6 = true := by decide +kernel
theorem nearF_r7 : nearCheckF 7 = true := by decide +kernel
theorem nearF_r8 : nearCheckF 8 = true := by decide +kernel
theorem nearF_r9 : nearCheckF 9 = true := by decide +kernel
theorem nearF_r10 : nearCheckF 10 = true := by decide +kernel
theorem nearF_r11 : nearCheckF 11 = true := by decide +kernel
theorem nearF_r12 : nearCheckF 12 = true := by decide +kernel
theorem nearF_r13 : nearCheckF 13 = true := by decide +kernel
theorem nearF_r14 : nearCheckF 14 = true := by decide +kernel
theorem nearF_r15 : nearCheckF 15 = true := by decide +kernel
theorem nearF_r16 : nearCheckF 16 = true := by decide +kernel
theorem nearF_r17 : nearCheckF 17 = true := by decide +kernel
theorem nearF_r18 : nearCheckF 18 = true := by decide +kernel
theorem nearF_r19 : nearCheckF 19 = true := by decide +kernel
theorem nearF_r20 : nearCheckF 20 = true := by decide +kernel

end ClaudeR3.Ev
end

section
namespace ClaudeR3.Ev
open ClaudeR3.Tab (tabM)

set_option maxRecDepth 100000
theorem tqPA_ok0 : tqOk (posT tabM) 70938 0 (tqPA.getD 0 []) = true := by decide +kernel
theorem tqPA_ok1 : tqOk (posT tabM) 70938 1 (tqPA.getD 1 []) = true := by decide +kernel
theorem tqPA_ok2 : tqOk (posT tabM) 70938 2 (tqPA.getD 2 []) = true := by decide +kernel
theorem tqPA_ok3 : tqOk (posT tabM) 70938 3 (tqPA.getD 3 []) = true := by decide +kernel
theorem tqPA_ok4 : tqOk (posT tabM) 70938 4 (tqPA.getD 4 []) = true := by decide +kernel
theorem tqPA_ok5 : tqOk (posT tabM) 70938 5 (tqPA.getD 5 []) = true := by decide +kernel
theorem tqPA_ok6 : tqOk (posT tabM) 70938 6 (tqPA.getD 6 []) = true := by decide +kernel
theorem tqPA_ok7 : tqOk (posT tabM) 70938 7 (tqPA.getD 7 []) = true := by decide +kernel
theorem tqPA_ok8 : tqOk (posT tabM) 70938 8 (tqPA.getD 8 []) = true := by decide +kernel
theorem tqPA_ok9 : tqOk (posT tabM) 70938 9 (tqPA.getD 9 []) = true := by decide +kernel
theorem tqPA_ok10 : tqOk (posT tabM) 70938 10 (tqPA.getD 10 []) = true := by decide +kernel
theorem tqPA_ok11 : tqOk (posT tabM) 70938 11 (tqPA.getD 11 []) = true := by decide +kernel
theorem tqPA_ok12 : tqOk (posT tabM) 70938 12 (tqPA.getD 12 []) = true := by decide +kernel
theorem tqPA_ok13 : tqOk (posT tabM) 70938 13 (tqPA.getD 13 []) = true := by decide +kernel
theorem tqPA_ok14 : tqOk (posT tabM) 70938 14 (tqPA.getD 14 []) = true := by decide +kernel
theorem tqPA_ok15 : tqOk (posT tabM) 70938 15 (tqPA.getD 15 []) = true := by decide +kernel
theorem tqPA_ok16 : tqOk (posT tabM) 70938 16 (tqPA.getD 16 []) = true := by decide +kernel
theorem tqPA_ok17 : tqOk (posT tabM) 70938 17 (tqPA.getD 17 []) = true := by decide +kernel
theorem tqPA_ok18 : tqOk (posT tabM) 70938 18 (tqPA.getD 18 []) = true := by decide +kernel

theorem tqPA_all : ∀ j : ℕ, j < 19 → tqOk (posT tabM) 70938 j (tqPA.getD j []) = true
  | 0, _ => tqPA_ok0
  | 1, _ => tqPA_ok1
  | 2, _ => tqPA_ok2
  | 3, _ => tqPA_ok3
  | 4, _ => tqPA_ok4
  | 5, _ => tqPA_ok5
  | 6, _ => tqPA_ok6
  | 7, _ => tqPA_ok7
  | 8, _ => tqPA_ok8
  | 9, _ => tqPA_ok9
  | 10, _ => tqPA_ok10
  | 11, _ => tqPA_ok11
  | 12, _ => tqPA_ok12
  | 13, _ => tqPA_ok13
  | 14, _ => tqPA_ok14
  | 15, _ => tqPA_ok15
  | 16, _ => tqPA_ok16
  | 17, _ => tqPA_ok17
  | 18, _ => tqPA_ok18
  | _ + 19, h => absurd h (by omega)

end ClaudeR3.Ev
end

section
namespace ClaudeR3.Ev
open ClaudeR3.Tab (tabM)

set_option maxRecDepth 100000
theorem tqNA_ok0 : tqOk (negT tabM) 70938 0 (tqNA.getD 0 []) = true := by decide +kernel
theorem tqNA_ok1 : tqOk (negT tabM) 70938 1 (tqNA.getD 1 []) = true := by decide +kernel
theorem tqNA_ok2 : tqOk (negT tabM) 70938 2 (tqNA.getD 2 []) = true := by decide +kernel
theorem tqNA_ok3 : tqOk (negT tabM) 70938 3 (tqNA.getD 3 []) = true := by decide +kernel
theorem tqNA_ok4 : tqOk (negT tabM) 70938 4 (tqNA.getD 4 []) = true := by decide +kernel
theorem tqNA_ok5 : tqOk (negT tabM) 70938 5 (tqNA.getD 5 []) = true := by decide +kernel
theorem tqNA_ok6 : tqOk (negT tabM) 70938 6 (tqNA.getD 6 []) = true := by decide +kernel
theorem tqNA_ok7 : tqOk (negT tabM) 70938 7 (tqNA.getD 7 []) = true := by decide +kernel
theorem tqNA_ok8 : tqOk (negT tabM) 70938 8 (tqNA.getD 8 []) = true := by decide +kernel
theorem tqNA_ok9 : tqOk (negT tabM) 70938 9 (tqNA.getD 9 []) = true := by decide +kernel
theorem tqNA_ok10 : tqOk (negT tabM) 70938 10 (tqNA.getD 10 []) = true := by decide +kernel
theorem tqNA_ok11 : tqOk (negT tabM) 70938 11 (tqNA.getD 11 []) = true := by decide +kernel
theorem tqNA_ok12 : tqOk (negT tabM) 70938 12 (tqNA.getD 12 []) = true := by decide +kernel
theorem tqNA_ok13 : tqOk (negT tabM) 70938 13 (tqNA.getD 13 []) = true := by decide +kernel
theorem tqNA_ok14 : tqOk (negT tabM) 70938 14 (tqNA.getD 14 []) = true := by decide +kernel
theorem tqNA_ok15 : tqOk (negT tabM) 70938 15 (tqNA.getD 15 []) = true := by decide +kernel
theorem tqNA_ok16 : tqOk (negT tabM) 70938 16 (tqNA.getD 16 []) = true := by decide +kernel
theorem tqNA_ok17 : tqOk (negT tabM) 70938 17 (tqNA.getD 17 []) = true := by decide +kernel
theorem tqNA_ok18 : tqOk (negT tabM) 70938 18 (tqNA.getD 18 []) = true := by decide +kernel

theorem tqNA_all : ∀ j : ℕ, j < 19 → tqOk (negT tabM) 70938 j (tqNA.getD j []) = true
  | 0, _ => tqNA_ok0
  | 1, _ => tqNA_ok1
  | 2, _ => tqNA_ok2
  | 3, _ => tqNA_ok3
  | 4, _ => tqNA_ok4
  | 5, _ => tqNA_ok5
  | 6, _ => tqNA_ok6
  | 7, _ => tqNA_ok7
  | 8, _ => tqNA_ok8
  | 9, _ => tqNA_ok9
  | 10, _ => tqNA_ok10
  | 11, _ => tqNA_ok11
  | 12, _ => tqNA_ok12
  | 13, _ => tqNA_ok13
  | 14, _ => tqNA_ok14
  | 15, _ => tqNA_ok15
  | 16, _ => tqNA_ok16
  | 17, _ => tqNA_ok17
  | 18, _ => tqNA_ok18
  | _ + 19, h => absurd h (by omega)

end ClaudeR3.Ev
end

section
namespace ClaudeR3.Ev
open ClaudeR3.Tab (tabM)

set_option maxRecDepth 100000
theorem tqPB_ok0 : tqOk (posT tabM) 0 0 (tqPB.getD 0 []) = true := by decide +kernel
theorem tqPB_ok1 : tqOk (posT tabM) 0 1 (tqPB.getD 1 []) = true := by decide +kernel
theorem tqPB_ok2 : tqOk (posT tabM) 0 2 (tqPB.getD 2 []) = true := by decide +kernel
theorem tqPB_ok3 : tqOk (posT tabM) 0 3 (tqPB.getD 3 []) = true := by decide +kernel
theorem tqPB_ok4 : tqOk (posT tabM) 0 4 (tqPB.getD 4 []) = true := by decide +kernel
theorem tqPB_ok5 : tqOk (posT tabM) 0 5 (tqPB.getD 5 []) = true := by decide +kernel
theorem tqPB_ok6 : tqOk (posT tabM) 0 6 (tqPB.getD 6 []) = true := by decide +kernel
theorem tqPB_ok7 : tqOk (posT tabM) 0 7 (tqPB.getD 7 []) = true := by decide +kernel
theorem tqPB_ok8 : tqOk (posT tabM) 0 8 (tqPB.getD 8 []) = true := by decide +kernel
theorem tqPB_ok9 : tqOk (posT tabM) 0 9 (tqPB.getD 9 []) = true := by decide +kernel
theorem tqPB_ok10 : tqOk (posT tabM) 0 10 (tqPB.getD 10 []) = true := by decide +kernel
theorem tqPB_ok11 : tqOk (posT tabM) 0 11 (tqPB.getD 11 []) = true := by decide +kernel
theorem tqPB_ok12 : tqOk (posT tabM) 0 12 (tqPB.getD 12 []) = true := by decide +kernel
theorem tqPB_ok13 : tqOk (posT tabM) 0 13 (tqPB.getD 13 []) = true := by decide +kernel
theorem tqPB_ok14 : tqOk (posT tabM) 0 14 (tqPB.getD 14 []) = true := by decide +kernel
theorem tqPB_ok15 : tqOk (posT tabM) 0 15 (tqPB.getD 15 []) = true := by decide +kernel
theorem tqPB_ok16 : tqOk (posT tabM) 0 16 (tqPB.getD 16 []) = true := by decide +kernel
theorem tqPB_ok17 : tqOk (posT tabM) 0 17 (tqPB.getD 17 []) = true := by decide +kernel
theorem tqPB_ok18 : tqOk (posT tabM) 0 18 (tqPB.getD 18 []) = true := by decide +kernel

theorem tqPB_all : ∀ j : ℕ, j < 19 → tqOk (posT tabM) 0 j (tqPB.getD j []) = true
  | 0, _ => tqPB_ok0
  | 1, _ => tqPB_ok1
  | 2, _ => tqPB_ok2
  | 3, _ => tqPB_ok3
  | 4, _ => tqPB_ok4
  | 5, _ => tqPB_ok5
  | 6, _ => tqPB_ok6
  | 7, _ => tqPB_ok7
  | 8, _ => tqPB_ok8
  | 9, _ => tqPB_ok9
  | 10, _ => tqPB_ok10
  | 11, _ => tqPB_ok11
  | 12, _ => tqPB_ok12
  | 13, _ => tqPB_ok13
  | 14, _ => tqPB_ok14
  | 15, _ => tqPB_ok15
  | 16, _ => tqPB_ok16
  | 17, _ => tqPB_ok17
  | 18, _ => tqPB_ok18
  | _ + 19, h => absurd h (by omega)

end ClaudeR3.Ev
end

section
namespace ClaudeR3.Ev
open ClaudeR3.Tab (tabM)

set_option maxRecDepth 100000
theorem tqNB_ok0 : tqOk (negT tabM) 0 0 (tqNB.getD 0 []) = true := by decide +kernel
theorem tqNB_ok1 : tqOk (negT tabM) 0 1 (tqNB.getD 1 []) = true := by decide +kernel
theorem tqNB_ok2 : tqOk (negT tabM) 0 2 (tqNB.getD 2 []) = true := by decide +kernel
theorem tqNB_ok3 : tqOk (negT tabM) 0 3 (tqNB.getD 3 []) = true := by decide +kernel
theorem tqNB_ok4 : tqOk (negT tabM) 0 4 (tqNB.getD 4 []) = true := by decide +kernel
theorem tqNB_ok5 : tqOk (negT tabM) 0 5 (tqNB.getD 5 []) = true := by decide +kernel
theorem tqNB_ok6 : tqOk (negT tabM) 0 6 (tqNB.getD 6 []) = true := by decide +kernel
theorem tqNB_ok7 : tqOk (negT tabM) 0 7 (tqNB.getD 7 []) = true := by decide +kernel
theorem tqNB_ok8 : tqOk (negT tabM) 0 8 (tqNB.getD 8 []) = true := by decide +kernel
theorem tqNB_ok9 : tqOk (negT tabM) 0 9 (tqNB.getD 9 []) = true := by decide +kernel
theorem tqNB_ok10 : tqOk (negT tabM) 0 10 (tqNB.getD 10 []) = true := by decide +kernel
theorem tqNB_ok11 : tqOk (negT tabM) 0 11 (tqNB.getD 11 []) = true := by decide +kernel
theorem tqNB_ok12 : tqOk (negT tabM) 0 12 (tqNB.getD 12 []) = true := by decide +kernel
theorem tqNB_ok13 : tqOk (negT tabM) 0 13 (tqNB.getD 13 []) = true := by decide +kernel
theorem tqNB_ok14 : tqOk (negT tabM) 0 14 (tqNB.getD 14 []) = true := by decide +kernel
theorem tqNB_ok15 : tqOk (negT tabM) 0 15 (tqNB.getD 15 []) = true := by decide +kernel
theorem tqNB_ok16 : tqOk (negT tabM) 0 16 (tqNB.getD 16 []) = true := by decide +kernel
theorem tqNB_ok17 : tqOk (negT tabM) 0 17 (tqNB.getD 17 []) = true := by decide +kernel
theorem tqNB_ok18 : tqOk (negT tabM) 0 18 (tqNB.getD 18 []) = true := by decide +kernel

theorem tqNB_all : ∀ j : ℕ, j < 19 → tqOk (negT tabM) 0 j (tqNB.getD j []) = true
  | 0, _ => tqNB_ok0
  | 1, _ => tqNB_ok1
  | 2, _ => tqNB_ok2
  | 3, _ => tqNB_ok3
  | 4, _ => tqNB_ok4
  | 5, _ => tqNB_ok5
  | 6, _ => tqNB_ok6
  | 7, _ => tqNB_ok7
  | 8, _ => tqNB_ok8
  | 9, _ => tqNB_ok9
  | 10, _ => tqNB_ok10
  | 11, _ => tqNB_ok11
  | 12, _ => tqNB_ok12
  | 13, _ => tqNB_ok13
  | 14, _ => tqNB_ok14
  | 15, _ => tqNB_ok15
  | 16, _ => tqNB_ok16
  | 17, _ => tqNB_ok17
  | 18, _ => tqNB_ok18
  | _ + 19, h => absurd h (by omega)

end ClaudeR3.Ev
end

section
namespace ClaudeR3.Ev

set_option maxRecDepth 100000
theorem diagF_r2 : diagCheckL 2 = true := by decide +kernel
theorem diagF_r3 : diagCheckL 3 = true := by decide +kernel
theorem diagF_r4 : diagCheckL 4 = true := by decide +kernel
theorem diagF_r5 : diagCheckL 5 = true := by decide +kernel
theorem diagF_r6 : diagCheckL 6 = true := by decide +kernel
theorem diagF_r7 : diagCheckL 7 = true := by decide +kernel
theorem diagF_r8 : diagCheckL 8 = true := by decide +kernel
theorem diagF_r9 : diagCheckL 9 = true := by decide +kernel
theorem diagF_r10 : diagCheckL 10 = true := by decide +kernel

end ClaudeR3.Ev
end

section
namespace ClaudeR3.Ev

set_option maxRecDepth 100000
theorem diagF_r11 : diagCheckL 11 = true := by decide +kernel
theorem diagF_r12 : diagCheckL 12 = true := by decide +kernel
theorem diagF_r13 : diagCheckL 13 = true := by decide +kernel
theorem diagF_r14 : diagCheckL 14 = true := by decide +kernel

end ClaudeR3.Ev
end

section
namespace ClaudeR3.Ev

set_option maxRecDepth 100000
theorem diagF_r15 : diagCheckL 15 = true := by decide +kernel
theorem diagF_r16 : diagCheckL 16 = true := by decide +kernel
theorem diagF_r17 : diagCheckL 17 = true := by decide +kernel

end ClaudeR3.Ev
end

section
namespace ClaudeR3.Ev

set_option maxRecDepth 100000
theorem diagF_r18 : diagCheckL 18 = true := by decide +kernel
theorem diagF_r19 : diagCheckL 19 = true := by decide +kernel
theorem diagF_r20 : diagCheckL 20 = true := by decide +kernel

end ClaudeR3.Ev
end
