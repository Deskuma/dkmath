import DkMath.CFBRC

/-! # DkMathTest.CFBRC

`DkMath.CFBRC` 公開 API の回帰検証ファイル。

- `TrigBridge` (`d=2`) の橋定理
- core/GN の除法橋
- `BoundarySide` 高位 API（valuation / existence）

を `example` で固定し、将来の型崩れ・命名変更を検知する。
-/

#print "file: DkMathTest.CFBRC"

namespace DkMathTest.CFBRC

open DkMath.CFBRC
open DkMath.CFBRC.TrigBridge
open DkMath.CosmicFormulaBinom

-- d=2 三角置換 bridge
example (a φ : ℝ) :
    body2 (a * (1 - Real.sin φ)) (a * Real.sin φ)
      = Complex.re (cfbrcR 2 (a * Real.cos φ) (a * Real.sin φ)) :=
  body2_eq_re_cfbrc2 a φ

example (a φ : ℝ) :
    (a * (1 - Real.sin φ)) * ((a * (1 - Real.sin φ)) + 2 * (a * Real.sin φ))
      = Complex.re (cfbrcR 2 (a * Real.cos φ) (a * Real.sin φ)) :=
  factor_eq_re_cfbrc2 a φ

-- core と GN の橋
example {p x u q : ℕ} (hq : Nat.Prime q) (hqx : ¬ q ∣ x) :
    q ∣ ((x + u) ^ p - u ^ p) ↔ q ∣ cyclotomicPrimeCore p x u :=
  prime_dvd_sub_pow_iff_dvd_cyclotomicPrimeCore_nat
    (p := p) (x := x) (u := u) (q := q) hq hqx

example {d x u : ℕ} (hx : 0 < x) :
    cyclotomicPrimeCore d x u = GN d x u :=
  cyclotomicPrimeCore_eq_GN_nat (p := d) (x := x) (u := u) hx

-- general d の Re/Im 補助
example (X Θ : ℝ) :
    cfbrcRe 1 X Θ = X := by
  exact cfbrcRe_one X Θ

example (d : ℕ) (X Θ : ℝ) :
    cfbrcRe (d + 1) X Θ =
      X * cfbrcRe d X Θ - Θ * cfbrcIm d X Θ + X * Complex.re ((Complex.I * Θ) ^ d) := by
  simpa using cfbrcRe_succ' d X Θ

example (d : ℕ) (X Θ : ℝ) :
    cfbrcIm (d + 1) X Θ =
      X * cfbrcIm d X Θ + Θ * cfbrcRe d X Θ + X * Complex.im ((Complex.I * Θ) ^ d) := by
  simpa using cfbrcIm_succ' d X Θ

example (n : ℕ) (Θ : ℝ) :
    Complex.re ((Complex.I * Θ) ^ (2 * n)) = (-1 : ℝ) ^ n * Θ ^ (2 * n) := by
  simpa using pure_phase_pow_even_re n Θ

example (n : ℕ) (Θ : ℝ) :
    Complex.im ((Complex.I * Θ) ^ (2 * n + 1)) = (-1 : ℝ) ^ n * Θ ^ (2 * n + 1) := by
  simpa using pure_phase_pow_odd_im n Θ

example (n : ℕ) (Θ : ℝ) :
    Complex.re ((Complex.I * Θ) ^ (4 * n + 2)) = -(Θ ^ (4 * n + 2)) := by
  simpa using pure_phase_pow_mod4_two_re n Θ

example (n : ℕ) (Θ : ℝ) :
    Complex.im ((Complex.I * Θ) ^ (4 * n + 3)) = -(Θ ^ (4 * n + 3)) := by
  simpa using pure_phase_pow_mod4_three_im n Θ

example (n : ℕ) (X Θ : ℝ) :
    cfbrcIm (2 * n + 2) X Θ =
      X * cfbrcIm (2 * n + 1) X Θ + Θ * cfbrcRe (2 * n + 1) X Θ +
        X * ((-1 : ℝ) ^ n * Θ ^ (2 * n + 1)) := by
  simpa using cfbrcIm_even_from_odd n X Θ

example (n : ℕ) (X Θ : ℝ) :
    cfbrcRe (4 * n + 3) X Θ =
      X * cfbrcRe (4 * n + 2) X Θ - Θ * cfbrcIm (4 * n + 2) X Θ - X * Θ ^ (4 * n + 2) := by
  simpa using cfbrcRe_mod4_three_from_two n X Θ

example (n : ℕ) (X Θ : ℝ) :
    cfbrcIm (4 * n + 4) X Θ =
      X * cfbrcIm (4 * n + 3) X Θ + Θ * cfbrcRe (4 * n + 3) X Θ - X * Θ ^ (4 * n + 3) := by
  simpa using cfbrcIm_mod4_four_from_three n X Θ

-- BoundarySide 高位 API（valuation）
example (side : BoundarySide) {d x u q : ℕ}
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u)
    (hcop : Nat.Coprime x u) (hqP : Nat.Prime q)
    (hq_dvd_boundary : match side with
      | .right => q ∣ u
      | .left => q ∣ x) :
    padicValNat q (boundaryDiffPow side d x u) =
      padicValNat q (boundaryGN side d x u) :=
  padicValNat_boundaryDiffPow_eq_boundaryGN_of_coprime_of_dvd_boundary
    side hd2 hx hu hcop hqP hq_dvd_boundary

example (side : BoundarySide) {d x u q : ℕ}
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u)
    (hcop : Nat.Coprime x u) (hqP : Nat.Prime q)
    (hq_dvd_boundary : match side with
      | .right => q ∣ u
      | .left => q ∣ x) :
    padicValNat q (boundaryDiffPow side d x u) =
      padicValNat q (boundaryCyclotomicPrimeCore side d x u) :=
  padicValNat_boundaryDiffPow_eq_boundaryCyclotomicPrimeCore_of_coprime_of_dvd_boundary
    side hd2 hx hu hcop hqP hq_dvd_boundary

-- BoundarySide 高位 API（existence）
example (side : BoundarySide) {d x u : ℕ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with
      | .right => ¬ d ∣ x
      | .left => ¬ d ∣ u) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ boundaryCyclotomicPrimeCore side d x u ∧
      (match side with
        | .right => ¬ q ∣ x
        | .left => ¬ q ∣ u) ∧
      (∀ {k : ℕ}, 0 < k → k < d → ¬ q ∣ boundaryDiffPow side k x u) :=
  exists_primitive_prime_factor_dvd_boundaryCore_of_prime_exp_boundary_of_coprime
    side hd_prime hd_ge hx hu hcop hpnd

example (side : BoundarySide) {d x u : ℕ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with
      | .right => ¬ d ∣ x
      | .left => ¬ d ∣ u) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ boundaryDiffPow side d x u ∧
      (match side with
        | .right => ¬ q ∣ x
        | .left => ¬ q ∣ u) ∧
      (∀ {k : ℕ}, 0 < k → k < d → ¬ q ∣ boundaryDiffPow side k x u) :=
  exists_primitive_prime_factor_boundaryDiffPow_of_prime_exp_boundary_of_coprime
    side hd_prime hd_ge hx hu hcop hpnd

-- 依存公理の確認（回帰用）
#print axioms factor_eq_re_cfbrc2
#print axioms prime_dvd_sub_pow_iff_dvd_cyclotomicPrimeCore_nat
#print axioms cfbrcRe_succ'
#print axioms pure_phase_pow_odd_im
#print axioms pure_phase_pow_mod4_three_im
#print axioms cfbrcIm_mod4_four_from_three
#print axioms padicValNat_boundaryDiffPow_eq_boundaryGN_of_coprime_of_dvd_boundary
#print axioms exists_primitive_prime_factor_dvd_boundaryCore_of_prime_exp_boundary_of_coprime
#print axioms exists_primitive_prime_factor_boundaryDiffPow_of_prime_exp_boundary_of_coprime

end DkMathTest.CFBRC
