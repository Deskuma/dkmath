/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.TraceOneQuadraticField
import DkMath.Lib.NumberTheory.UnitPowerSector
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.Data.Complex.Basic

#print "file: DkMath.NumberTheory.TraceOnePrimeUnitSectors"

/-!
# Unit sectors for prime-discriminant TraceOne orders

This module proves the imaginary quadratic unit collapse for primes at least
seven.  The real quadratic Dirichlet-sector construction is intentionally not
asserted here until the explicit quadratic signature bridge is available.
-/

namespace DkMath.NumberTheory.TraceOnePrimeUnitSectors

open scoped nonZeroDivisors

open DkMath.Lib.NumberTheory
open DkMath.NumberTheory.PrimeQuadraticDiscriminant
open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.NumberTheory.TraceOneQuadraticField

private theorem complex_im_eq_zero_of_sq_eq_self_add
    {z : ℂ} {s : ℝ} (hz : z ^ 2 = z + (s : ℂ))
    (hs : 0 < 1 + 4 * s) : z.im = 0 := by
  have hreal := congrArg Complex.re hz
  have himag := congrArg Complex.im hz
  simp only [pow_two, Complex.mul_re, Complex.add_re, Complex.ofReal_re] at hreal
  simp only [pow_two, Complex.mul_im, Complex.add_im, Complex.ofReal_im] at himag
  by_contra hy
  have hprod : z.im * (2 * z.re - 1) = 0 := by
    nlinarith [himag]
  have hxy : 2 * z.re = 1 := by
    rcases mul_eq_zero.mp hprod with hzero | hzero
    · exact (hy hzero).elim
    · nlinarith [hzero]
  nlinarith [hreal, sq_nonneg z.im]

private theorem traceOneRat_generator_image_real
    {p : ℕ} (hp : Nat.Prime p) (hmod : p % 4 = 1)
    (φ : TraceOneRat (signedPrimeParameter p) →+* ℂ) :
    (φ (QuadraticAlgebra.omega : TraceOneRat (signedPrimeParameter p))).im = 0 := by
  have hp2 : p ≠ 2 := by omega
  have hdiscr : discr (signedPrimeParameter p) = (p : ℤ) := by
    rw [discr_signedPrimeParameter hp hp2]
    simp [signedPrimeDiscriminant, hmod]
  have hrel :
      (QuadraticAlgebra.omega : TraceOneRat (signedPrimeParameter p)) ^ 2 =
        algebraMap ℚ (TraceOneRat (signedPrimeParameter p))
            (signedPrimeParameter p : ℚ) +
          QuadraticAlgebra.omega := by
    rw [pow_two, QuadraticAlgebra.omega_mul_omega_eq_add]
    simp [Algebra.smul_def]
  have hz :
      (φ (QuadraticAlgebra.omega : TraceOneRat (signedPrimeParameter p))) ^ 2 =
        φ (QuadraticAlgebra.omega : TraceOneRat (signedPrimeParameter p)) +
          ((signedPrimeParameter p : ℚ) : ℂ) := by
    calc
      _ = φ ((QuadraticAlgebra.omega : TraceOneRat (signedPrimeParameter p)) ^ 2) := by
        rw [map_pow]
      _ = φ (algebraMap ℚ (TraceOneRat (signedPrimeParameter p))
          (signedPrimeParameter p : ℚ) + QuadraticAlgebra.omega) := by
        rw [hrel]
      _ = φ (algebraMap ℚ (TraceOneRat (signedPrimeParameter p))
          (signedPrimeParameter p : ℚ)) +
          φ (QuadraticAlgebra.omega : TraceOneRat (signedPrimeParameter p)) := by
        rw [map_add]
      _ = φ (QuadraticAlgebra.omega : TraceOneRat (signedPrimeParameter p)) +
          ((signedPrimeParameter p : ℚ) : ℂ) := by
        simp [add_comm]
  apply complex_im_eq_zero_of_sq_eq_self_add hz
  have hdiscrQ : (1 : ℝ) + 4 * (signedPrimeParameter p : ℝ) = p := by
    exact_mod_cast hdiscr
  simpa [hdiscrQ] using (show (0 : ℝ) < p by exact_mod_cast hp.pos)

private theorem traceOneRat_all_images_real
    {p : ℕ} (hp : Nat.Prime p) (hmod : p % 4 = 1)
    (φ : TraceOneRat (signedPrimeParameter p) →+* ℂ) :
    ∀ x : TraceOneRat (signedPrimeParameter p),
      (φ x).im = 0 := by
  intro x
  rcases x with ⟨a, b⟩
  have hω := traceOneRat_generator_image_real hp hmod φ
  have hx :
      (⟨a, b⟩ : TraceOneRat (signedPrimeParameter p)) =
        algebraMap ℚ (TraceOneRat (signedPrimeParameter p)) a +
          b • (QuadraticAlgebra.omega : TraceOneRat (signedPrimeParameter p)) := by
    exact QuadraticAlgebra.mk_eq_add_smul_omega a b
  rw [hx, map_add]
  simp [Algebra.smul_def, hω]

theorem traceOneRat_isTotallyReal_of_prime_mod_four_eq_one
    {p : ℕ} (hp : Nat.Prime p) (hmod : p % 4 = 1) :
    letI : Fact (∀ r : ℚ,
        r ^ 2 ≠ (signedPrimeParameter p : ℚ) + 1 * r) :=
      ⟨traceOneRat_no_rational_root hp (by omega)⟩
    letI : Field (TraceOneRat (signedPrimeParameter p)) := inferInstance
    letI : NumberField (TraceOneRat (signedPrimeParameter p)) := {
      to_charZero := charZero_of_injective_algebraMap (by
        intro q₁ q₂ hq
        have hre := congrArg QuadraticAlgebra.re hq
        change q₁ = q₂ at hre
        exact hre)
      to_finiteDimensional := inferInstance
    }
    NumberField.IsTotallyReal (TraceOneRat (signedPrimeParameter p)) := by
  letI : Fact (∀ r : ℚ,
      r ^ 2 ≠ (signedPrimeParameter p : ℚ) + 1 * r) :=
    ⟨traceOneRat_no_rational_root hp (by omega)⟩
  letI : Field (TraceOneRat (signedPrimeParameter p)) := inferInstance
  letI : NumberField (TraceOneRat (signedPrimeParameter p)) := {
    to_charZero := charZero_of_injective_algebraMap (by
      intro q₁ q₂ hq
      have hre := congrArg QuadraticAlgebra.re hq
      change q₁ = q₂ at hre
      exact hre)
    to_finiteDimensional := inferInstance
  }
  refine ⟨?_⟩
  intro w
  rw [NumberField.InfinitePlace.isReal_iff]
  rw [NumberField.ComplexEmbedding.isReal_iff]
  apply RingHom.ext
  intro x
  apply Complex.conj_eq_iff_im.mpr
  exact traceOneRat_all_images_real hp hmod w.embedding x

theorem traceOnePrimeReal_signature
    {p : ℕ} (hp : Nat.Prime p) (hmod : p % 4 = 1) :
    letI : Fact (∀ r : ℚ,
        r ^ 2 ≠ (signedPrimeParameter p : ℚ) + 1 * r) :=
      ⟨traceOneRat_no_rational_root hp (by omega)⟩
    letI : Field (TraceOneRat (signedPrimeParameter p)) := inferInstance
    letI : NumberField (TraceOneRat (signedPrimeParameter p)) := {
      to_charZero := charZero_of_injective_algebraMap (by
        intro q₁ q₂ hq
        have hre := congrArg QuadraticAlgebra.re hq
        change q₁ = q₂ at hre
        exact hre)
      to_finiteDimensional := inferInstance
    }
    Module.finrank ℚ (TraceOneRat (signedPrimeParameter p)) = 2 ∧
      NumberField.InfinitePlace.nrComplexPlaces
          (TraceOneRat (signedPrimeParameter p)) = 0 ∧
      NumberField.InfinitePlace.nrRealPlaces
          (TraceOneRat (signedPrimeParameter p)) = 2 ∧
      NumberField.Units.rank (TraceOneRat (signedPrimeParameter p)) = 1 := by
  letI : Fact (∀ r : ℚ,
      r ^ 2 ≠ (signedPrimeParameter p : ℚ) + 1 * r) :=
    ⟨traceOneRat_no_rational_root hp (by omega)⟩
  letI : Field (TraceOneRat (signedPrimeParameter p)) := inferInstance
  letI : NumberField (TraceOneRat (signedPrimeParameter p)) := {
    to_charZero := charZero_of_injective_algebraMap (by
      intro q₁ q₂ hq
      have hre := congrArg QuadraticAlgebra.re hq
      change q₁ = q₂ at hre
      exact hre)
    to_finiteDimensional := inferInstance
  }
  have htot : NumberField.IsTotallyReal
      (TraceOneRat (signedPrimeParameter p)) :=
    traceOneRat_isTotallyReal_of_prime_mod_four_eq_one hp hmod
  letI : NumberField.IsTotallyReal
      (TraceOneRat (signedPrimeParameter p)) := htot
  have hfin : Module.finrank ℚ
      (TraceOneRat (signedPrimeParameter p)) = 2 := by
    exact QuadraticAlgebra.finrank_eq_two _ _
  have hcomplex := NumberField.IsTotallyReal.nrComplexPlaces_eq_zero
    (TraceOneRat (signedPrimeParameter p))
  have hsignature := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank
    (TraceOneRat (signedPrimeParameter p))
  have hreal : NumberField.InfinitePlace.nrRealPlaces
      (TraceOneRat (signedPrimeParameter p)) = 2 := by
    omega
  have hcard : Fintype.card
      (NumberField.InfinitePlace (TraceOneRat (signedPrimeParameter p))) = 2 := by
    rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
    omega
  have hrank : NumberField.Units.rank
      (TraceOneRat (signedPrimeParameter p)) = 1 := by
    simp [NumberField.Units.rank, hcard]
  exact ⟨hfin, hcomplex, hreal, hrank⟩

private theorem traceOneReal_torsion_eq_one_or_neg_one
    {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (hreal : NumberField.InfinitePlace.nrRealPlaces K = 2)
    (ζ : NumberField.Units.torsion K) :
    (ζ : (NumberField.RingOfIntegers K)ˣ) = 1 ∨
      (ζ : (NumberField.RingOfIntegers K)ˣ) = -1 := by
  let n := orderOf (ζ : (NumberField.RingOfIntegers K)ˣ)
  have hnpos : 0 < n := by
    exact orderOf_pos_iff.mpr ((CommGroup.mem_torsion ζ.1).1 ζ.2)
  by_cases hngt : 2 < n
  · have hngt' : 2 < orderOf (ζ.1 : K) := by
      have horder :
          orderOf ((algebraMap (NumberField.RingOfIntegers K) K)
              (ζ : (NumberField.RingOfIntegers K)ˣ)) = n := by
        exact orderOf_injective
          ((algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom.comp
            (Units.coeHom (NumberField.RingOfIntegers K)))
          (NumberField.Units.coe_injective K) ζ
      rw [horder]
      exact hngt
    have hnzero := NumberField.InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt
      hngt' (IsPrimitiveRoot.orderOf (ζ.1 : K))
    omega
  · have hnle : n ≤ 2 := by omega
    have hncases : n = 1 ∨ n = 2 := by omega
    rcases hncases with hnone | hntwo
    · left
      exact orderOf_eq_one_iff.mp hnone
    · right
      change orderOf (ζ : (NumberField.RingOfIntegers K)ˣ) = 2 at hntwo
      rw [← orderOf_units,
        CharP.orderOf_eq_two_iff 0 (by decide)] at hntwo
      simp [← Units.val_inj, Units.val_neg, Units.val_one, hntwo]

private def traceOneReal_rankOneIndex
    {K : Type*} [Field K] [NumberField K]
    (hrank : NumberField.Units.rank K = 1) :
    Fin (NumberField.Units.rank K) :=
  ⟨0, by rw [hrank]; exact Nat.zero_lt_succ 0⟩

private theorem traceOneReal_ringOfIntegers_unit_sector_complete
    {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    {p : ℕ} (hp : Nat.Prime p) (hpodd : Odd p)
    (hreal : NumberField.InfinitePlace.nrRealPlaces K = 2)
    (hrank : NumberField.Units.rank K = 1) :
    ∀ u : (NumberField.RingOfIntegers K)ˣ,
      ∃ i : Fin p, ∃ e : (NumberField.RingOfIntegers K)ˣ,
        u = NumberField.Units.fundSystem K (traceOneReal_rankOneIndex hrank) ^
            (i : ℕ) * e ^ p := by
  classical
  intro u
  let j : Fin (NumberField.Units.rank K) := traceOneReal_rankOneIndex hrank
  obtain ⟨⟨ζ, exponent⟩, hu, _⟩ :=
    NumberField.Units.exist_unique_eq_mul_prod K u
  have hu' : u = (ζ : (NumberField.RingOfIntegers K)ˣ) *
      NumberField.Units.fundSystem K j ^ exponent j := by
    letI : Unique (Fin (NumberField.Units.rank K)) :=
      { default := j
        uniq := by
          intro a
          apply Fin.ext
          have ha := a.isLt
          have hj := j.isLt
          omega }
    have hprod :
        (∏ i : Fin (NumberField.Units.rank K),
          NumberField.Units.fundSystem K i ^ exponent i) =
          NumberField.Units.fundSystem K j ^ exponent j := by
      have hprod0 :=
        Fintype.prod_unique
          (fun i : Fin (NumberField.Units.rank K) =>
            NumberField.Units.fundSystem K i ^ exponent i)
      simpa only [Subsingleton.elim (default : Fin (NumberField.Units.rank K)) j]
        using hprod0
    exact hu.trans (by rw [hprod])
  have hζ : (ζ : (NumberField.RingOfIntegers K)ˣ) = 1 ∨
      (ζ : (NumberField.RingOfIntegers K)ˣ) = -1 :=
    traceOneReal_torsion_eq_one_or_neg_one hreal ζ
  have hsign : ∃ v : (NumberField.RingOfIntegers K)ˣ,
      (ζ : (NumberField.RingOfIntegers K)ˣ) = v ^ p := by
    rcases hζ with hζ | hζ
    · refine ⟨1, ?_⟩
      simp [hζ]
    · refine ⟨-1, ?_⟩
      simp [hζ, hpodd.neg_pow]
  let n : ℤ := exponent j
  let q : ℤ := n / p
  let r : ℤ := n % p
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hrnonneg : 0 ≤ r := by
    exact Int.emod_nonneg _ hpne
  have hrlt : r < (p : ℤ) := by
    have hlt := Int.emod_lt n hpne
    have hpabs : Int.natAbs (p : ℤ) = p := by simp
    simpa [r, hpabs] using hlt
  let i : Fin p := ⟨Int.toNat r, by
    rw [Int.toNat_lt hrnonneg]
    exact_mod_cast hrlt⟩
  have hdecomp : n = r + (p : ℤ) * q := by
    calc
      n = n / (p : ℤ) * (p : ℤ) + n % (p : ℤ) :=
        (Int.ediv_mul_add_emod n (p : ℤ)).symm
      _ = r + (p : ℤ) * q := by ring
  have hir : ((i : ℕ) : ℤ) = r := by
    simpa [i] using (Int.toNat_of_nonneg hrnonneg)
  have hpow :
      NumberField.Units.fundSystem K j ^ n =
        NumberField.Units.fundSystem K j ^ (i : ℕ) *
          (NumberField.Units.fundSystem K j ^ q) ^ p := by
    calc
      NumberField.Units.fundSystem K j ^ n =
          NumberField.Units.fundSystem K j ^ (r + (p : ℤ) * q) := by rw [hdecomp]
      _ = NumberField.Units.fundSystem K j ^ r *
          NumberField.Units.fundSystem K j ^ ((p : ℤ) * q) :=
        zpow_add (NumberField.Units.fundSystem K j) r ((p : ℤ) * q)
      _ = NumberField.Units.fundSystem K j ^ (i : ℕ) *
          (NumberField.Units.fundSystem K j ^ q) ^ p := by
        calc
          _ = NumberField.Units.fundSystem K j ^ r *
              NumberField.Units.fundSystem K j ^ (q * (p : ℤ)) := by
            congr 2
            ring
          _ = NumberField.Units.fundSystem K j ^ r *
              (NumberField.Units.fundSystem K j ^ q) ^ (p : ℤ) := by
            rw [zpow_mul]
          _ = NumberField.Units.fundSystem K j ^ (i : ℕ) *
              (NumberField.Units.fundSystem K j ^ q) ^ p := by
            rw [← hir, zpow_natCast, zpow_natCast]
  obtain ⟨v, hv⟩ := hsign
  refine ⟨i, v * NumberField.Units.fundSystem K j ^ q, ?_⟩
  change u = NumberField.Units.fundSystem K j ^ (i : ℕ) *
    (v * NumberField.Units.fundSystem K j ^ q) ^ p
  rw [hu', hv, hpow]
  simp only [mul_pow]
  simp [mul_assoc, mul_comm]

private noncomputable def traceOneRealRingOfIntegersFinSectorSystem
    {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    {p : ℕ} (hp : Nat.Prime p) (hpodd : Odd p)
    (hreal : NumberField.InfinitePlace.nrRealPlaces K = 2)
    (hrank : NumberField.Units.rank K = 1) :
    UnitPowerSectorSystem (NumberField.RingOfIntegers K) p := {
  Sector := Fin p
  rep := fun i => NumberField.Units.fundSystem K
    (traceOneReal_rankOneIndex hrank) ^ (i : ℕ)
  complete := by
    intro u
    exact traceOneReal_ringOfIntegers_unit_sector_complete hp hpodd hreal hrank u
}

/-- The genuine finite unit-power sectors in the real prime-discriminant branch.

The representatives are transported from the rank-one Dirichlet fundamental
unit in the ring of integers of `TraceOneRat` to the integral TraceOne order by
the explicit ring equivalence from the quadratic-field API.
-/
noncomputable def traceOnePrimeRealFinSectorSystem
    {p : ℕ} (hp : Nat.Prime p) (hmod : p % 4 = 1) :
    letI : Fact (∀ r : ℚ,
        r ^ 2 ≠ (signedPrimeParameter p : ℚ) + 1 * r) :=
      ⟨traceOneRat_no_rational_root hp (by omega)⟩
    letI : Field (TraceOneRat (signedPrimeParameter p)) := inferInstance
    letI : NumberField (TraceOneRat (signedPrimeParameter p)) := {
      to_charZero := charZero_of_injective_algebraMap (by
        intro q₁ q₂ hq
        have hre := congrArg QuadraticAlgebra.re hq
        change q₁ = q₂ at hre
        exact hre)
      to_finiteDimensional := inferInstance
    }
    UnitPowerSectorSystem (TraceOneInt (signedPrimeParameter p)) p := by
  classical
  letI : Fact (∀ r : ℚ,
      r ^ 2 ≠ (signedPrimeParameter p : ℚ) + 1 * r) :=
    ⟨traceOneRat_no_rational_root hp (by omega)⟩
  letI : Field (TraceOneRat (signedPrimeParameter p)) := inferInstance
  letI : NumberField (TraceOneRat (signedPrimeParameter p)) := {
    to_charZero := charZero_of_injective_algebraMap (by
      intro q₁ q₂ hq
      have hre := congrArg QuadraticAlgebra.re hq
      change q₁ = q₂ at hre
      exact hre)
    to_finiteDimensional := inferInstance
  }
  letI : NumberField.IsTotallyReal
      (TraceOneRat (signedPrimeParameter p)) :=
    traceOneRat_isTotallyReal_of_prime_mod_four_eq_one hp hmod
  have hsignature := traceOnePrimeReal_signature hp hmod
  have hreal := hsignature.2.2.1
  have hrank := hsignature.2.2.2
  let e : NumberField.RingOfIntegers (TraceOneRat (signedPrimeParameter p))
      ≃+* TraceOneInt (signedPrimeParameter p) :=
    Classical.choice (traceOneRat_ringOfIntegers_equiv hp (by omega))
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  let S₀ : UnitPowerSectorSystem
      (NumberField.RingOfIntegers (TraceOneRat (signedPrimeParameter p))) p :=
    traceOneRealRingOfIntegersFinSectorSystem hp hpodd hreal hrank
  let mapU : (NumberField.RingOfIntegers
      (TraceOneRat (signedPrimeParameter p)))ˣ →*
      (TraceOneInt (signedPrimeParameter p))ˣ :=
    Units.map e.toMonoidHom
  let invU : (TraceOneInt (signedPrimeParameter p))ˣ →*
      (NumberField.RingOfIntegers
        (TraceOneRat (signedPrimeParameter p)))ˣ :=
    Units.map e.symm.toMonoidHom
  refine {
    Sector := Fin p
    rep := fun i => mapU (S₀.rep i)
    complete := ?_ }
  intro u
  let uO := invU u
  obtain ⟨i, eO, heO⟩ :=
    S₀.complete uO
  have hinv : mapU (invU u) = u := by
    apply Units.ext
    simp [mapU, invU]
  refine ⟨i, mapU eO, ?_⟩
  calc
    u = mapU (invU u) := hinv.symm
    _ = mapU (S₀.rep i * eO ^ p) := by
      change mapU uO = _
      rw [heO]
    _ = mapU (S₀.rep i) * (mapU eO) ^ p := by
      simp [mapU]

/-- Conditional Phase-18 endpoint with the real finite unit sector system. -/
theorem traceOnePrimeReal_exists_sector_mul_pow_of_span_eq_pow
    {p : ℕ} (hp : Nat.Prime p) (hmod : p % 4 = 1) :
    letI : Fact (∀ r : ℚ,
        r ^ 2 ≠ (signedPrimeParameter p : ℚ) + 1 * r) :=
      ⟨traceOneRat_no_rational_root hp (by omega)⟩
    letI : Field (TraceOneRat (signedPrimeParameter p)) := inferInstance
    letI : NumberField (TraceOneRat (signedPrimeParameter p)) := {
      to_charZero := charZero_of_injective_algebraMap (by
        intro q₁ q₂ hq
        have hre := congrArg QuadraticAlgebra.re hq
        change q₁ = q₂ at hre
        exact hre)
      to_finiteDimensional := inferInstance
    }
    letI : IsDomain (TraceOneInt (signedPrimeParameter p)) :=
      (traceOneRatHom_injective _).isDomain (traceOneRatHom _)
    letI : IsDedekindDomain (TraceOneInt (signedPrimeParameter p)) :=
      traceOneRat_isDedekindDomain hp (by omega)
    ∀ {I : Ideal (TraceOneInt (signedPrimeParameter p))}
      {a : TraceOneInt (signedPrimeParameter p)},
      I ∈ (Ideal (TraceOneInt (signedPrimeParameter p)))⁰ →
      classGroupPTorsionFreeAt (TraceOneInt (signedPrimeParameter p)) p →
      Ideal.span ({a} : Set (TraceOneInt (signedPrimeParameter p))) = I ^ p →
      ∃ i : Fin p,
        ∃ delta : TraceOneInt (signedPrimeParameter p),
        a = (traceOnePrimeRealFinSectorSystem hp hmod).rep i * delta ^ p := by
  classical
  letI : Fact (∀ r : ℚ,
      r ^ 2 ≠ (signedPrimeParameter p : ℚ) + 1 * r) :=
    ⟨traceOneRat_no_rational_root hp (by omega)⟩
  letI : Field (TraceOneRat (signedPrimeParameter p)) := inferInstance
  letI : NumberField (TraceOneRat (signedPrimeParameter p)) := {
    to_charZero := charZero_of_injective_algebraMap (by
      intro q₁ q₂ hq
      have hre := congrArg QuadraticAlgebra.re hq
      change q₁ = q₂ at hre
      exact hre)
    to_finiteDimensional := inferInstance
  }
  letI : IsDomain (TraceOneInt (signedPrimeParameter p)) :=
    (traceOneRatHom_injective _).isDomain (traceOneRatHom _)
  letI : IsDedekindDomain (TraceOneInt (signedPrimeParameter p)) :=
    traceOneRat_isDedekindDomain hp (by omega)
  intro I a hI0 hfree hspan
  exact exists_sector_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt
    (traceOnePrimeRealFinSectorSystem hp hmod) hI0 hfree hspan

private theorem discr_signedPrimeParameter_eq_neg
    {p : ℕ} (hp : Nat.Prime p) (hmod : p % 4 = 3) :
    discr (signedPrimeParameter p) = -(p : ℤ) := by
  rw [discr_signedPrimeParameter hp (by omega)]
  simp [signedPrimeDiscriminant, hmod]

private theorem traceOnePrimeImaginary_norm_pos
    {p : ℕ} (hp : Nat.Prime p) (hp7 : 7 ≤ p) (hmod : p % 4 = 3)
    (x : TraceOneInt (signedPrimeParameter p)) (hx : x ≠ 0) :
    0 < norm x := by
  have hD := discr_signedPrimeParameter_eq_neg hp hmod
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp.pos
  rcases x with ⟨a, b⟩
  have hsum :
      4 * norm (⟨a, b⟩ : TraceOneInt (signedPrimeParameter p)) =
        (2 * a + b) ^ 2 + (p : ℤ) * b ^ 2 := by
    rw [four_mul_traceOneNorm_eq_discriminant, hD]
    simp [trace]
  have hnonneg :
      0 ≤ norm (⟨a, b⟩ : TraceOneInt (signedPrimeParameter p)) := by
    nlinarith [sq_nonneg (2 * a + b), sq_nonneg b]
  have hne :
      norm (⟨a, b⟩ : TraceOneInt (signedPrimeParameter p)) ≠ 0 := by
    intro hn
    have hsum0 : (2 * a + b) ^ 2 + (p : ℤ) * b ^ 2 = 0 := by
      nlinarith [hsum]
    have hb : b = 0 := by
      nlinarith [sq_nonneg (2 * a + b), sq_nonneg b]
    have ha : a = 0 := by
      rw [hb] at hsum0
      nlinarith [sq_nonneg a]
    apply hx
    apply traceOne_ext <;> simp [ha, hb]
  omega

private theorem traceOnePrimeImaginary_norm_eq_one_of_isUnit
    {p : ℕ} (hp : Nat.Prime p) (hp7 : 7 ≤ p) (hmod : p % 4 = 3)
    (x : TraceOneInt (signedPrimeParameter p)) (hx : IsUnit x) :
    norm x = 1 := by
  obtain ⟨y, hxy⟩ := isUnit_iff_exists_inv.mp hx
  have hy : IsUnit y := by
    apply isUnit_iff_exists_inv.mpr
    exact ⟨x, by simpa [mul_comm] using hxy⟩
  have hprod : norm x * norm y = 1 := by
    rw [← traceOne_norm_mul, hxy]
    norm_num [DkMath.NumberTheory.TraceOneQuadratic.norm]
  have hx0 : x ≠ 0 := by
    intro hx0
    have hzero : (0 : TraceOneInt (signedPrimeParameter p)) = 1 := by
      simpa [hx0] using hxy
    have hfst := congrArg TraceOneInt.fst hzero
    norm_num at hfst
  have hy0 : y ≠ 0 := by
    intro hy0
    have hzero : (0 : TraceOneInt (signedPrimeParameter p)) = 1 := by
      simpa [hy0] using hxy
    have hfst := congrArg TraceOneInt.fst hzero
    norm_num at hfst
  have hxpos := traceOnePrimeImaginary_norm_pos hp hp7 hmod x hx0
  have hypos := traceOnePrimeImaginary_norm_pos hp hp7 hmod y hy0
  rcases (Int.mul_eq_one_iff_eq_one_or_neg_one).mp hprod with h | h
  · exact h.1
  · nlinarith [hxpos, h.1]

private theorem traceOnePrimeImaginary_eq_one_or_neg_one_of_norm_eq_one
    {p : ℕ} (hp : Nat.Prime p) (hp7 : 7 ≤ p) (hmod : p % 4 = 3)
    {x : TraceOneInt (signedPrimeParameter p)}
    (hx : norm x = 1) :
    x = 1 ∨ x = -1 := by
  have hD := discr_signedPrimeParameter_eq_neg hp hmod
  have hpz : (7 : ℤ) ≤ p := by exact_mod_cast hp7
  rcases x with ⟨a, b⟩
  have hsum :
      4 * norm (⟨a, b⟩ : TraceOneInt (signedPrimeParameter p)) =
        (2 * a + b) ^ 2 + (p : ℤ) * b ^ 2 := by
    rw [four_mul_traceOneNorm_eq_discriminant, hD]
    simp [trace]
  rw [hx] at hsum
  have hb_sq_lt : b ^ 2 < 1 := by
    nlinarith [sq_nonneg (2 * a + b), sq_nonneg b]
  have hb : b = 0 := by
    nlinarith [sq_nonneg b]
  have hfactor : (a - 1) * (a + 1) = 0 := by
    rw [hb] at hsum
    nlinarith
  rcases mul_eq_zero.mp hfactor with ha | ha
  · left
    have ha' : a = 1 := by omega
    apply traceOne_ext <;> simp [ha', hb]
  · right
    have ha' : a = -1 := by omega
    apply traceOne_ext <;> simp [ha', hb]

/-- For `p >= 7` in the `p % 4 = 3` branch, every unit is a sign. -/
theorem traceOnePrimeImaginary_unit_eq_one_or_neg_one
    {p : ℕ} (hp : Nat.Prime p) (hp7 : 7 ≤ p) (hmod : p % 4 = 3)
    (u : (TraceOneInt (signedPrimeParameter p))ˣ) :
    (u : TraceOneInt (signedPrimeParameter p)) = 1 ∨
      (u : TraceOneInt (signedPrimeParameter p)) = -1 := by
  exact traceOnePrimeImaginary_eq_one_or_neg_one_of_norm_eq_one hp hp7 hmod
    (traceOnePrimeImaginary_norm_eq_one_of_isUnit hp hp7 hmod (u : _) u.isUnit)

private theorem traceOnePrimeImaginary_unit_pow_surjective
    {p : ℕ} (hp : Nat.Prime p) (hp7 : 7 ≤ p) (hmod : p % 4 = 3) :
    ∀ u : (TraceOneInt (signedPrimeParameter p))ˣ,
      ∃ e : (TraceOneInt (signedPrimeParameter p))ˣ, u = e ^ p := by
  intro u
  rcases traceOnePrimeImaginary_unit_eq_one_or_neg_one hp hp7 hmod u with h | h
  · refine ⟨1, ?_⟩
    apply Units.ext
    simpa using h
  · refine ⟨-1, ?_⟩
    apply Units.ext
    have hpodd : Odd p := hp.odd_of_ne_two (by omega)
    simpa [Units.val_pow_eq_pow_val, hpodd.neg_pow] using h

/-- The imaginary prime-discriminant branch has a singleton unit sector. -/
def traceOnePrimeImaginarySingletonSectorSystem
    {p : ℕ} (hp : Nat.Prime p) (hp7 : 7 ≤ p) (hmod : p % 4 = 3) :
    UnitPowerSectorSystem (TraceOneInt (signedPrimeParameter p)) p :=
  singletonUnitPowerSectorSystem
    (traceOnePrimeImaginary_unit_pow_surjective hp hp7 hmod)

/-- Conditional exact-power extraction for the imaginary branch. -/
theorem traceOnePrimeImaginary_exists_eq_pow_of_span_eq_pow
    {p : ℕ} (hp : Nat.Prime p) (hp7 : 7 ≤ p) (hmod : p % 4 = 3) :
    letI : Fact (∀ r : ℚ,
        r ^ 2 ≠ (signedPrimeParameter p : ℚ) + 1 * r) :=
      ⟨traceOneRat_no_rational_root hp (by omega)⟩
    letI : Field (TraceOneRat (signedPrimeParameter p)) := inferInstance
    letI : IsDomain (TraceOneInt (signedPrimeParameter p)) :=
      (traceOneRatHom_injective _).isDomain (traceOneRatHom _)
    letI : IsDedekindDomain (TraceOneInt (signedPrimeParameter p)) :=
      traceOneRat_isDedekindDomain hp (by omega)
    ∀ {I : Ideal (TraceOneInt (signedPrimeParameter p))}
      {a : TraceOneInt (signedPrimeParameter p)},
      I ∈ (Ideal (TraceOneInt (signedPrimeParameter p)))⁰ →
      classGroupPTorsionFreeAt (TraceOneInt (signedPrimeParameter p)) p →
      Ideal.span ({a} : Set (TraceOneInt (signedPrimeParameter p))) = I ^ p →
      ∃ delta : TraceOneInt (signedPrimeParameter p), a = delta ^ p := by
  letI : Fact (∀ r : ℚ,
      r ^ 2 ≠ (signedPrimeParameter p : ℚ) + 1 * r) :=
    ⟨traceOneRat_no_rational_root hp (by omega)⟩
  letI : Field (TraceOneRat (signedPrimeParameter p)) := inferInstance
  letI : IsDomain (TraceOneInt (signedPrimeParameter p)) :=
    (traceOneRatHom_injective _).isDomain (traceOneRatHom _)
  letI : IsDedekindDomain (TraceOneInt (signedPrimeParameter p)) :=
    traceOneRat_isDedekindDomain hp (by omega)
  intro I a hI0 hfree hspan
  exact exists_eq_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt_of_unit_pow_surjective
    hI0 hfree (traceOnePrimeImaginary_unit_pow_surjective hp hp7 hmod) hspan

end DkMath.NumberTheory.TraceOnePrimeUnitSectors
