import DkMath.FLT.Three.EisensteinEuclidean
import DkMath.Lib.NumberTheory.PrincipalIdealPower

/-!
Research-only audit: principal ideal square-factor descent with a free residual.
No assertion that a shell already supplies the ideal factorization is made here.
-/

open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.Lib.NumberTheory

namespace ABC_EisensteinLandingAudit

#synth EuclideanDomain (TraceOneInt (-1))
#synth IsPrincipalIdealRing (TraceOneInt (-1))
#synth UniqueFactorizationMonoid (TraceOneInt (-1))
#synth IsDedekindDomain (TraceOneInt (-1))

/-- A free residual absorbs the unit from principal-ideal equality. -/
theorem exists_exact_factor_of_principal_ideal_factor
    {R : Type*} [CommRing R] [IsDomain R]
    {alpha : R} {b g : Ideal R}
    (hb : b.IsPrincipal) (hg : g.IsPrincipal)
    (h : Ideal.span ({alpha} : Set R) = b * g ^ 2) :
    ∃ beta gamma : R,
      Ideal.span ({beta} : Set R) = b ∧
      Ideal.span ({gamma} : Set R) = g ∧
      alpha = beta * gamma ^ 2 := by
  letI : b.IsPrincipal := hb
  letI : g.IsPrincipal := hg
  let beta0 : R := Submodule.IsPrincipal.generator b
  let gamma : R := Submodule.IsPrincipal.generator g
  have hb0 : Ideal.span ({beta0} : Set R) = b := Ideal.span_singleton_generator b
  have hg0 : Ideal.span ({gamma} : Set R) = g := Ideal.span_singleton_generator g
  have heq : Ideal.span ({alpha} : Set R) =
      Ideal.span ({beta0 * gamma ^ 2} : Set R) := by
    rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow]
    rw [hb0, hg0]
    exact h
  rcases associated_of_span_singleton_eq_span_singleton heq with ⟨u, hu⟩
  have hexact : alpha = ((↑(u⁻¹) : R) * beta0) * gamma ^ 2 := by
    calc
      alpha = alpha * (u : R) * (↑(u⁻¹) : R) := by simp [mul_assoc]
      _ = (beta0 * gamma ^ 2) * (↑(u⁻¹) : R) := by rw [hu]
      _ = _ := by ring
  refine ⟨(↑(u⁻¹) : R) * beta0, gamma, ?_, hg0, hexact⟩
  rw [← hb0, Ideal.span_singleton_eq_span_singleton]
  exact associated_unit_mul_left _ _ (u⁻¹).isUnit

/-- The existing Eisenstein PID instance discharges both principalization inputs. -/
theorem eisenstein_exact_factor_of_ideal_factor
    {alpha : TraceOneInt (-1)} {b g : Ideal (TraceOneInt (-1))}
    (h : Ideal.span ({alpha} : Set (TraceOneInt (-1))) = b * g ^ 2) :
    ∃ beta gamma : TraceOneInt (-1),
      Ideal.span ({beta} : Set (TraceOneInt (-1))) = b ∧
      Ideal.span ({gamma} : Set (TraceOneInt (-1))) = g ∧
      alpha = beta * gamma ^ 2 := by
  exact exists_exact_factor_of_principal_ideal_factor inferInstance inferInstance h

#print axioms exists_exact_factor_of_principal_ideal_factor
#print axioms eisenstein_exact_factor_of_ideal_factor

end ABC_EisensteinLandingAudit
