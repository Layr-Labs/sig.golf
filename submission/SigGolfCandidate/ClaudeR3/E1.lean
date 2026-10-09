import SigGolfCandidate.ClaudeR3.D1
import SigGolfCandidate.ClaudeR3.D3
import Mathlib.Data.Nat.Choose.Basic

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
