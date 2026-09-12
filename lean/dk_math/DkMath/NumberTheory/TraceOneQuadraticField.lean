/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.CyclotomicQRIntegralDescent
import DkMath.NumberTheory.PrimeQuadraticDiscriminant
import DkMath.NumberTheory.RationalSquarefreePrime
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.TraceOneQuadraticField"

namespace DkMath.NumberTheory.TraceOneQuadraticField

open DkMath.NumberTheory.PrimeQuadraticDiscriminant
open DkMath.NumberTheory.RationalSquarefreePrime
open DkMath.NumberTheory.CyclotomicQRIntegralDescent
open DkMath.NumberTheory.TraceOneQuadratic

noncomputable section

/-- The rational quadratic companion of the integral trace-one coordinates. -/
abbrev TraceOneRat (s : ℤ) := QuadraticAlgebra ℚ (s : ℚ) 1

instance traceOneInt_moduleFinite (s : ℤ) : Module.Finite ℤ (TraceOneInt s) := by
  let f : (Fin 2 → ℤ) →ₗ[ℤ] TraceOneInt s :=
    { toFun := fun v => ⟨v 0, v 1⟩
      map_add' := by
        intro v w
        ext <;> simp
      map_smul' := by
        intro c v
        have hc : (c : TraceOneInt s) = ⟨c, 0⟩ := rfl
        ext <;> simp [Algebra.smul_def, hc] }
  apply Module.Finite.of_surjective f
  intro x
  refine ⟨![x.fst, x.snd], ?_⟩
  rfl

/-- The coordinate-preserving map from trace-one integers to the rational
quadratic companion. -/
def traceOneRatHom (s : ℤ) : TraceOneInt s →+* TraceOneRat s where
  toFun x := ⟨x.fst, x.snd⟩
  map_one' := by
    rfl
  map_mul' x y := by
    ext
    · simp only [QuadraticAlgebra.re_mul, TraceOneQuadratic.fst_mul]
      push_cast
      ring
    · simp only [QuadraticAlgebra.im_mul, TraceOneQuadratic.snd_mul]
      push_cast
      ring
  map_zero' := by
    rfl
  map_add' x y := by
    ext <;> simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add,
      TraceOneQuadratic.fst_add, TraceOneQuadratic.snd_add] <;>
      push_cast <;> ring

@[simp] theorem traceOneRatHom_re (s : ℤ) (x : TraceOneInt s) :
    (traceOneRatHom s x).re = (x.fst : ℚ) := rfl

@[simp] theorem traceOneRatHom_im (s : ℤ) (x : TraceOneInt s) :
    (traceOneRatHom s x).im = (x.snd : ℚ) := rfl

theorem traceOneRatHom_injective (s : ℤ) :
    Function.Injective (traceOneRatHom s) := by
  intro x y h
  apply traceOne_ext
  · have hre := congrArg QuadraticAlgebra.re h
    change (x.fst : ℚ) = (y.fst : ℚ) at hre
    exact_mod_cast hre
  · have him := congrArg QuadraticAlgebra.im h
    change (x.snd : ℚ) = (y.snd : ℚ) at him
    exact_mod_cast him

/-- The trace-one map is also the scalar map for the companion algebra. -/
noncomputable instance traceOneRatAlgebra (s : ℤ) :
    Algebra (TraceOneInt s) (TraceOneRat s) :=
  (traceOneRatHom s).toAlgebra

@[simp] theorem traceOneRatHom_algebraMap (s : ℤ) :
    (algebraMap (TraceOneInt s) (TraceOneRat s)) = traceOneRatHom s := by
  exact RingHom.algebraMap_toAlgebra _

@[simp] theorem traceOneRatHom_tau (s : ℤ) :
    traceOneRatHom s (tau s) = (QuadraticAlgebra.omega : TraceOneRat s) := by
  rfl

@[simp] theorem traceOneRatHom_conj (s : ℤ) (x : TraceOneInt s) :
    star (traceOneRatHom s x) = traceOneRatHom s (conj x) := by
  ext <;> simp [traceOneRatHom, conj]

/-- The quadratic trace in the companion, written using its conjugation. -/
def quadraticTrace (s : ℤ) (x : TraceOneRat s) : ℚ := x.re + (star x).re

theorem traceOneRatHom_trace (s : ℤ) (x : TraceOneInt s) :
    quadraticTrace s (traceOneRatHom s x) = (trace x : ℚ) := by
  simp [quadraticTrace, traceOneRatHom, trace]; ring

theorem traceOneRatHom_norm (s : ℤ) (x : TraceOneInt s) :
    QuadraticAlgebra.norm (traceOneRatHom s x) = (norm x : ℚ) := by
  simp [QuadraticAlgebra.norm_def, traceOneRatHom,
    DkMath.NumberTheory.TraceOneQuadratic.norm]; ring

theorem traceOneRat_trace_eq_add_star (s : ℤ) (x : TraceOneRat s) :
    algebraMap ℚ (TraceOneRat s) (quadraticTrace s x) = x + star x := by
  ext <;> simp [quadraticTrace]

theorem traceOneRat_norm_eq_mul_star (s : ℤ) (x : TraceOneRat s) :
    algebraMap ℚ (TraceOneRat s) (QuadraticAlgebra.norm x) = x * star x := by
  exact QuadraticAlgebra.algebraMap_norm_eq_mul_star x

theorem traceOneRat_isIntegralClosure
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    IsIntegralClosure (TraceOneInt (signedPrimeParameter p)) ℤ
      (TraceOneRat (signedPrimeParameter p)) := by
  constructor
  · exact traceOneRatHom_injective _
  · intro x
    constructor
    · intro hx
      have hstar : IsIntegral ℤ (star x) :=
        map_isIntegral_int (starRingEnd _) hx
      have htrace : IsIntegral ℤ (x + star x) := hx.add hstar
      have hnorm : IsIntegral ℤ (x * star x) := hx.mul hstar
      have halg_injective :
          Function.Injective (algebraMap ℚ (TraceOneRat (signedPrimeParameter p))) := by
        intro q₁ q₂ hq
        have hre := congrArg QuadraticAlgebra.re hq
        simpa using hre
      have htraceRat : IsIntegral ℤ (quadraticTrace _ x) := by
        apply (isIntegral_algebraMap_iff halg_injective).mp
        rw [traceOneRat_trace_eq_add_star]
        exact htrace
      have hnormRat : IsIntegral ℤ (QuadraticAlgebra.norm x) := by
        apply (isIntegral_algebraMap_iff halg_injective).mp
        rw [traceOneRat_norm_eq_mul_star]
        exact hnorm
      obtain ⟨t, ht⟩ :=
        (rat_isIntegral_iff_exists_int (quadraticTrace _ x)).mp htraceRat
      obtain ⟨n, hn⟩ :=
        (rat_isIntegral_iff_exists_int (QuadraticAlgebra.norm x)).mp hnormRat
      have ht' : (t : ℚ) = quadraticTrace _ x := by simpa using ht
      have hn' : (n : ℚ) = QuadraticAlgebra.norm x := by simpa using hn
      have htracecoord : (t : ℚ) = 2 * x.re + x.im := by
        calc
          (t : ℚ) = quadraticTrace _ x := ht'
          _ = 2 * x.re + x.im := by simp [quadraticTrace]; ring
      have hnormcoord : (n : ℚ) = x.re ^ 2 + x.re * x.im -
          (signedPrimeParameter p : ℚ) * x.im ^ 2 := by
        calc
          (n : ℚ) = QuadraticAlgebra.norm x := hn'
          _ = x.re ^ 2 + x.re * x.im -
              (signedPrimeParameter p : ℚ) * x.im ^ 2 := by
            simp [QuadraticAlgebra.norm_def]
            ring
      have hdiscrQ : (discr (signedPrimeParameter p) : ℚ) =
          (signedPrimeDiscriminant p : ℚ) := by
        exact_mod_cast discr_signedPrimeParameter hp hp2
      have hdiscEq : (t : ℚ) ^ 2 - 4 * (n : ℚ) =
          (signedPrimeDiscriminant p : ℚ) * x.im ^ 2 := by
        rw [htracecoord, hnormcoord]
        rw [← hdiscrQ]
        simp [TraceOneQuadratic.discr]
        ring
      obtain ⟨b, hb⟩ := rat_eq_int_of_signedPrime_mul_sq hp
        (signedPrimeDiscriminant_eq_or_neg p) x.im (by
          refine ⟨t ^ 2 - 4 * n, ?_⟩
          calc
            ((t ^ 2 - 4 * n : ℤ) : ℚ) = (t : ℚ) ^ 2 - 4 * (n : ℚ) := by
              push_cast
              ring
            _ = (signedPrimeDiscriminant p : ℚ) * x.im ^ 2 := hdiscEq)
      have hfourQ : 4 * (n : ℚ) = (t : ℚ) ^ 2 -
          (signedPrimeDiscriminant p : ℚ) * (b : ℚ) ^ 2 := by
        rw [hb]
        linarith [hdiscEq]
      have hfour : 4 * n = t ^ 2 - signedPrimeDiscriminant p * b ^ 2 := by
        exact_mod_cast hfourQ
      have hpodd : Odd (p : ℤ) := by
        obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
        refine ⟨k, ?_⟩
        exact_mod_cast hk
      have hDodd : Odd (signedPrimeDiscriminant p) := by
        rcases signedPrimeDiscriminant_eq_or_neg p with hD | hD
        · simpa [hD] using hpodd
        · rw [hD]
          exact hpodd.neg
      have hdiff_even : Even (t ^ 2 - signedPrimeDiscriminant p * b ^ 2) := by
        rw [← hfour]
        refine ⟨2 * n, ?_⟩
        ring
      have hpar : Even (t ^ 2) ↔
          Even (signedPrimeDiscriminant p * b ^ 2) :=
        (Int.even_sub).mp hdiff_even
      have hpar' : Even t ↔ Even b := by
        have hDnotEven : ¬ Even (signedPrimeDiscriminant p) :=
          Int.not_even_iff_odd.mpr hDodd
        simpa [Int.even_pow, Int.even_mul, hDnotEven] using hpar
      have heven : Even (t - b) := (Int.even_sub).mpr hpar'
      rcases heven with ⟨k, hk⟩
      have hkQ : (t : ℚ) - (b : ℚ) = (k : ℚ) + (k : ℚ) := by
        exact_mod_cast hk
      have hxa : x.re = (k : ℚ) := by
        rw [show x.re = ((2 * x.re) / 2) by ring]
        rw [show (2 * x.re : ℚ) = (t : ℚ) - x.im by linarith [htracecoord]]
        rw [← hb]
        field_simp
        linarith [hkQ]
      refine ⟨⟨k, b⟩, ?_⟩
      apply QuadraticAlgebra.ext
      · exact hxa.symm
      · exact hb
    · rintro ⟨y, rfl⟩
      exact map_isIntegral_int (traceOneRatHom _)
        (IsIntegral.of_finite ℤ y)

private theorem signedPrimeDiscriminant_rat_not_isSquare
    {p : ℕ} (hp : p.Prime) (_hp2 : p ≠ 2) :
    ¬ IsSquare (signedPrimeDiscriminant p : ℚ) := by
  intro hsquare
  rcases hsquare with ⟨q, hq⟩
  have hDmul : ∃ z : ℤ,
      (z : ℚ) = (signedPrimeDiscriminant p : ℚ) * q ^ 2 := by
    refine ⟨signedPrimeDiscriminant p ^ 2, ?_⟩
    push_cast
    rw [hq]
    ring
  obtain ⟨z, hz⟩ := rat_eq_int_of_signedPrime_mul_sq hp
    (signedPrimeDiscriminant_eq_or_neg p) q hDmul
  have hqz : (z : ℚ) ^ 2 = (signedPrimeDiscriminant p : ℚ) := by
    calc
      (z : ℚ) ^ 2 = q ^ 2 := by rw [hz]
      _ = (signedPrimeDiscriminant p : ℚ) := by simpa [pow_two] using hq.symm
  have hqz_int : z ^ 2 = signedPrimeDiscriminant p := by
    exact_mod_cast hqz
  rcases signedPrimeDiscriminant_eq_or_neg p with hD | hD
  · rw [hD] at hqz_int
    have hp_dvd : p ∣ z.natAbs ^ 2 := by
      rw [← Int.natAbs_pow, hqz_int, Int.natAbs_natCast]
    have hp_dvd_z : p ∣ z.natAbs := hp.dvd_of_dvd_pow hp_dvd
    obtain ⟨k, hk⟩ := hp_dvd_z
    have hzsq : z.natAbs ^ 2 = p := by
      simpa only [Int.natAbs_pow, Int.natAbs_natCast] using
        congrArg Int.natAbs hqz_int
    rw [hk] at hzsq
    have hkpos : 0 < k := by
      by_contra hk0
      have hkzero : k = 0 := Nat.eq_zero_of_not_pos hk0
      subst k
      exact hp.ne_zero hzsq.symm
    have hpk : p ≤ p * k := by
      simpa using Nat.mul_le_mul_left p (show 1 ≤ k by omega)
    have hpow : p ^ 2 ≤ (p * k) ^ 2 := by
      gcongr
    rw [hzsq] at hpow
    nlinarith [hp.two_le]
  · rw [hD] at hqz_int
    have hz_nonneg : 0 ≤ z ^ 2 := sq_nonneg z
    have hp_pos : 0 < (p : ℤ) := by exact_mod_cast hp.pos
    omega

theorem traceOneRat_no_rational_root
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∀ r : ℚ,
      r ^ 2 ≠ (signedPrimeParameter p : ℚ) + 1 * r := by
  intro r hr
  apply signedPrimeDiscriminant_rat_not_isSquare hp hp2
  refine ⟨2 * r - 1, ?_⟩
  have hdiscr := discr_signedPrimeParameter hp hp2
  have hdiscrQ : (discr (signedPrimeParameter p) : ℚ) =
      (signedPrimeDiscriminant p : ℚ) := by
    exact_mod_cast hdiscr
  calc
    (signedPrimeDiscriminant p : ℚ) = (discr (signedPrimeParameter p) : ℚ) :=
      hdiscrQ.symm
    _ = (2 * r - 1) ^ 2 := by
      rw [show (discr (signedPrimeParameter p) : ℚ) =
          1 + 4 * (signedPrimeParameter p : ℚ) by
            norm_num [TraceOneQuadratic.discr]]
      have hs : (signedPrimeParameter p : ℚ) = r ^ 2 - r := by
        linarith [hr]
      rw [hs]
      ring
    _ = (2 * r - 1) * (2 * r - 1) := by ring

/-- A usable field structure for the rational companion at an odd prime. -/
@[reducible] noncomputable def traceOneRatField
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Field (TraceOneRat (signedPrimeParameter p)) := by
  letI : Fact (∀ r : ℚ,
      r ^ 2 ≠ (signedPrimeParameter p : ℚ) + 1 * r) :=
    ⟨traceOneRat_no_rational_root hp hp2⟩
  exact inferInstance

theorem traceOneRat_numberField
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ inst : Field (TraceOneRat (signedPrimeParameter p)),
      @NumberField (TraceOneRat (signedPrimeParameter p)) inst := by
  let inst : Field (TraceOneRat (signedPrimeParameter p)) :=
    traceOneRatField hp hp2
  letI : Field (TraceOneRat (signedPrimeParameter p)) := inst
  refine ⟨inst, ?_⟩
  exact {
    to_charZero := inferInstance
    to_finiteDimensional := inferInstance
  }

theorem traceOneRat_ringOfIntegers_equiv
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    letI : Fact (∀ r : ℚ,
        r ^ 2 ≠ (signedPrimeParameter p : ℚ) + 1 * r) :=
      ⟨traceOneRat_no_rational_root hp hp2⟩
    letI : Field (TraceOneRat (signedPrimeParameter p)) := inferInstance
    Nonempty (NumberField.RingOfIntegers (TraceOneRat (signedPrimeParameter p))
      ≃+* TraceOneInt (signedPrimeParameter p)) := by
  letI : Fact (∀ r : ℚ,
      r ^ 2 ≠ (signedPrimeParameter p : ℚ) + 1 * r) :=
    ⟨traceOneRat_no_rational_root hp hp2⟩
  letI : Field (TraceOneRat (signedPrimeParameter p)) := inferInstance
  have halg_injective :
      Function.Injective (algebraMap ℚ (TraceOneRat (signedPrimeParameter p))) := by
    intro q₁ q₂ hq
    have hre := congrArg QuadraticAlgebra.re hq
    simpa using hre
  letI : NumberField (TraceOneRat (signedPrimeParameter p)) := {
    to_charZero := charZero_of_injective_algebraMap halg_injective
    to_finiteDimensional := inferInstance
  }
  letI : IsIntegralClosure (TraceOneInt (signedPrimeParameter p)) ℤ
      (TraceOneRat (signedPrimeParameter p)) :=
    traceOneRat_isIntegralClosure hp hp2
  exact ⟨NumberField.RingOfIntegers.equiv _⟩

theorem traceOneRat_isDedekindDomain
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    letI : Fact (∀ r : ℚ,
        r ^ 2 ≠ (signedPrimeParameter p : ℚ) + 1 * r) :=
      ⟨traceOneRat_no_rational_root hp hp2⟩
    letI : Field (TraceOneRat (signedPrimeParameter p)) := inferInstance
    letI : NumberField (TraceOneRat (signedPrimeParameter p)) := {
      to_charZero := charZero_of_injective_algebraMap (by
        intro q₁ q₂ hq
        have hre := congrArg QuadraticAlgebra.re hq
        change q₁ = q₂ at hre
        exact hre)
      to_finiteDimensional := inferInstance
    }
    letI : IsIntegralClosure (TraceOneInt (signedPrimeParameter p)) ℤ
        (TraceOneRat (signedPrimeParameter p)) :=
      traceOneRat_isIntegralClosure hp hp2
    IsDedekindDomain (TraceOneInt (signedPrimeParameter p)) := by
  letI : Fact (∀ r : ℚ,
      r ^ 2 ≠ (signedPrimeParameter p : ℚ) + 1 * r) :=
    ⟨traceOneRat_no_rational_root hp hp2⟩
  letI : Field (TraceOneRat (signedPrimeParameter p)) := inferInstance
  have halg_injective :
      Function.Injective (algebraMap ℚ (TraceOneRat (signedPrimeParameter p))) := by
    intro q₁ q₂ hq
    have hre := congrArg QuadraticAlgebra.re hq
    simpa using hre
  letI : NumberField (TraceOneRat (signedPrimeParameter p)) := {
    to_charZero := charZero_of_injective_algebraMap halg_injective
    to_finiteDimensional := inferInstance
  }
  letI : IsIntegralClosure (TraceOneInt (signedPrimeParameter p)) ℤ
      (TraceOneRat (signedPrimeParameter p)) :=
    traceOneRat_isIntegralClosure hp hp2
  letI : IsDomain (TraceOneInt (signedPrimeParameter p)) :=
    (traceOneRatHom_injective _).isDomain (traceOneRatHom _)
  exact IsIntegralClosure.isDedekindDomain ℤ ℚ
    (TraceOneRat (signedPrimeParameter p)) (TraceOneInt (signedPrimeParameter p))

end

end DkMath.NumberTheory.TraceOneQuadraticField
