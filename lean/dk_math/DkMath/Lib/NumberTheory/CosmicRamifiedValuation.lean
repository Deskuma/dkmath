/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GTail
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# 整数 GN の分岐深度

自然数版 `GTailCongruence` / `GTailPadic` と同じ境界を、符号付きの整数座標で扱う。
LTE を呼ばず、`GN = p*u^(p-1) + x*GTail p 2 x u` と次の tail の再帰式から
二次以上の項を p² で括る。従って x=0 も合同式と GN の exact-one 結論に含む。
積の付値には零の規約があるため、`x*GN=c^p` の指数配分には c≠0 を要求する。
-/

open DkMath.CosmicFormula

namespace DkMath.Lib.NumberTheory

/-- p≥3 と p∣x なら、整数上で `GN = p*u^(p-1) + p²*M`。
最初の項を保存し、残りを GTail の再帰で括る。u の原始性はまだ不要。 -/
theorem integral_GN_eq_head_add_prime_sq_mul
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) {x u : ℤ} (hx : (p : ℤ) ∣ x) :
    ∃ M : ℤ, GTail p 1 x u = (p : ℤ) * u ^ (p - 1) + (p : ℤ) ^ 2 * M := by
  have hchoose : (p : ℤ) ∣ (Nat.choose p 2 : ℤ) := by
    exact_mod_cast hp.dvd_choose_self (by decide : 2 ≠ 0) (by omega : 2 < p)
  have hnext : (p : ℤ) ∣ GTail p 2 x u := by
    rw [GTail_rec p 2 x u (by omega)]
    exact dvd_add (dvd_mul_of_dvd_left hchoose _) (dvd_mul_of_dvd_left hx _)
  obtain ⟨M, hM⟩ := (show (p : ℤ) ^ 2 ∣ x * GTail p 2 x u by
    simpa only [pow_two] using mul_dvd_mul hx hnext)
  refine ⟨M, ?_⟩
  rw [GN_tail_rec p x u hp.one_lt, Nat.choose_one_right, hM]

/-- GN の整数版 mod p² 合同式。負の u を含むので FLT の `u=-b` に直接使える。 -/
theorem integral_GN_modEq_head_mod_prime_sq
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) {x u : ℤ} (hx : (p : ℤ) ∣ x) :
    GTail p 1 x u ≡ (p : ℤ) * u ^ (p - 1) [ZMOD (p : ℤ) ^ 2] := by
  obtain ⟨M, hM⟩ := integral_GN_eq_head_add_prime_sq_mul hp hp3 hx (u := u)
  apply Int.ModEq.symm
  apply Int.modEq_iff_dvd.mpr
  exact ⟨M, by rw [hM]; ring⟩

/-- p∣x, p∤u の素数分岐側では GN は p を含むが p² を含まない。
この可除性の対が、円分体に依存しない整数上の exact-one 情報である。 -/
theorem integral_GN_prime_dvd_and_not_sq
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) {x u : ℤ}
    (hx : (p : ℤ) ∣ x) (hu : ¬ (p : ℤ) ∣ u) :
    (p : ℤ) ∣ GTail p 1 x u ∧ ¬ (p : ℤ) ^ 2 ∣ GTail p 1 x u := by
  obtain ⟨M, hM⟩ := integral_GN_eq_head_add_prime_sq_mul hp hp3 hx (u := u)
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  constructor
  · rw [hM]
    exact dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_left (dvd_pow_self _ (by decide : 2 ≠ 0)) _)
  · intro hs
    have hh : (p : ℤ) ^ 2 ∣ (p : ℤ) * u ^ (p - 1) := by
      have := dvd_sub hs (dvd_mul_right ((p : ℤ) ^ 2) M)
      simpa only [hM, add_sub_cancel_right] using this
    obtain ⟨q, hq⟩ := hh
    have hpow : (p : ℤ) ∣ u ^ (p - 1) := ⟨q, mul_left_cancel₀ hp0 (by
      simpa only [pow_two, mul_assoc] using hq)⟩
    exact hu ((Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow hpow)

/-- GN の整数 p 進付値はちょうど1。GN=0 は p² 非可除性が排除する。 -/
theorem padicValInt_GN_eq_one_of_dvd_gap
    {p : ℕ} [hp : Fact p.Prime] (hp3 : 3 ≤ p) {x u : ℤ}
    (hx : (p : ℤ) ∣ x) (hu : ¬ (p : ℤ) ∣ u) :
    padicValInt p (GTail p 1 x u) = 1 := by
  obtain ⟨hd, hsq⟩ := integral_GN_prime_dvd_and_not_sq hp.out hp3 hx hu
  have hn : GTail p 1 x u ≠ 0 := fun h => hsq (h ▸ dvd_zero _)
  have h1 : 1 ≤ padicValInt p (GTail p 1 x u) := by
    exact ((padicValInt_dvd_iff 1 _).mp (by simpa using hd)).resolve_left hn
  have h2 : ¬ 2 ≤ padicValInt p (GTail p 1 x u) :=
    fun h => hsq ((padicValInt_dvd_iff 2 _).mpr (Or.inr h))
  omega

/-- `x*GN=c^p` の全分岐深度を整数付値で保存する。
非零条件は c にのみ課し、x と GN の非零性は積等式から導く。 -/
theorem padicValInt_gap_add_one_eq_prime_mul
    {p : ℕ} [hp : Fact p.Prime] (hp3 : 3 ≤ p) {x u c : ℤ}
    (hx : (p : ℤ) ∣ x) (hu : ¬ (p : ℤ) ∣ u)
    (hc : c ≠ 0) (heq : x * GTail p 1 x u = c ^ p) :
    padicValInt p x + 1 = p * padicValInt p c := by
  have hn : x * GTail p 1 x u ≠ 0 := by rw [heq]; exact pow_ne_zero _ hc
  have hval := congrArg (padicValInt p) heq
  rw [padicValInt.mul (mul_ne_zero_iff.mp hn).1 (mul_ne_zero_iff.mp hn).2,
    padicValInt_GN_eq_one_of_dvd_gap hp3 hx hu] at hval
  simpa only [padicValInt, Int.natAbs_pow, padicValNat.pow] using hval

end DkMath.Lib.NumberTheory
