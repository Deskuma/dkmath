import DkMath.CFBRC

#print "file: DkMathTest.CFBRC"

namespace DkMathTest.CFBRC

open DkMath.CFBRC
open DkMath.CFBRC.TrigBridge
open DkMath.CosmicFormulaBinom

example (a φ : ℝ) :
    body2 (a * (1 - Real.sin φ)) (a * Real.sin φ)
      = Complex.re (cfbrcR 2 (a * Real.cos φ) (a * Real.sin φ)) :=
  body2_eq_re_cfbrc2 a φ

example (a φ : ℝ) :
    (a * (1 - Real.sin φ)) * ((a * (1 - Real.sin φ)) + 2 * (a * Real.sin φ))
      = Complex.re (cfbrcR 2 (a * Real.cos φ) (a * Real.sin φ)) :=
  factor_eq_re_cfbrc2 a φ

example {p x u q : ℕ} (hq : Nat.Prime q) (hqx : ¬ q ∣ x) :
    q ∣ ((x + u) ^ p - u ^ p) ↔ q ∣ cyclotomicPrimeCore p x u :=
  prime_dvd_sub_pow_iff_dvd_cyclotomicPrimeCore_nat
    (p := p) (x := x) (u := u) (q := q) hq hqx

example {d x u : ℕ} (hx : 0 < x) :
    cyclotomicPrimeCore d x u = GN d x u :=
  cyclotomicPrimeCore_eq_GN_nat (p := d) (x := x) (u := u) hx

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

#print axioms factor_eq_re_cfbrc2
#print axioms prime_dvd_sub_pow_iff_dvd_cyclotomicPrimeCore_nat
#print axioms padicValNat_boundaryDiffPow_eq_boundaryGN_of_coprime_of_dvd_boundary
#print axioms exists_primitive_prime_factor_dvd_boundaryCore_of_prime_exp_boundary_of_coprime

end DkMathTest.CFBRC
