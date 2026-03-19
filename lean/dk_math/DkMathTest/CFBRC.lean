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

#print axioms factor_eq_re_cfbrc2
#print axioms prime_dvd_sub_pow_iff_dvd_cyclotomicPrimeCore_nat

end DkMathTest.CFBRC
