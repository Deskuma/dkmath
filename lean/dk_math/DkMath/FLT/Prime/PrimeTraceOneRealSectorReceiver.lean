/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Prime.PrimeTraceOneConditionalDescent
import DkMath.FLT.Prime.PrimeTraceOneFiveSectorClosure
import DkMath.Lib.NumberTheory.TraceOnePowerLanding
import DkMath.NumberTheory.PrimeQuadraticDiscriminant
import Mathlib.Tactic

#print "file: DkMath.FLT.Prime.PrimeTraceOneRealSectorReceiver"

namespace DkMath.FLT.Prime

open DkMath.Lib.NumberTheory
open DkMath.FLT.Five
open DkMath.NumberTheory.CyclotomicQRTraceOneBridge
open DkMath.NumberTheory.PrimeQuadraticDiscriminant
open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.NumberTheory.TraceOneQuadraticField
open DkMath.NumberTheory.TraceOnePrimeUnitSectors

noncomputable section

local notation "traceNorm" => DkMath.NumberTheory.TraceOneQuadratic.norm

/-! ## Small neutral landing helper -/

/-- A unit in a TraceOne carrier has nonzero quadratic norm. -/
theorem traceOne_norm_ne_zero_of_isUnit
    {s : ℤ} {x : TraceOneInt s} (hx : IsUnit x) : traceNorm x ≠ 0 := by
  obtain ⟨y, hxy⟩ := isUnit_iff_exists_inv.mp hx
  have hprod : traceNorm x * traceNorm y = 1 := by
    rw [← traceOne_norm_mul, hxy]
    norm_num [DkMath.NumberTheory.TraceOneQuadratic.norm]
  intro hx0
  rw [hx0, zero_mul] at hprod
  norm_num at hprod

private theorem exists_powCoords_of_sector_mul_pow
    {s : ℤ} {p : ℕ} (S : UnitPowerSectorSystem (TraceOneInt s) p)
    {alpha : TraceOneInt s}
    (hfactor : ∃ i : S.Sector, ∃ delta : TraceOneInt s,
      alpha = (S.rep i : TraceOneInt s) * delta ^ p) :
    ∃ i : S.Sector, ∃ m n : ℤ,
      (alpha * conj (S.rep i : TraceOneInt s)).fst =
          traceNorm (S.rep i : TraceOneInt s) *
            (traceOnePowCoords s m n p).1 ∧
      (alpha * conj (S.rep i : TraceOneInt s)).snd =
          traceNorm (S.rep i : TraceOneInt s) *
            (traceOnePowCoords s m n p).2 := by
  obtain ⟨i, delta, hdelta⟩ := hfactor
  have hnorm : traceNorm (S.rep i : TraceOneInt s) ≠ 0 :=
    traceOne_norm_ne_zero_of_isUnit (S.rep i).isUnit
  obtain ⟨m, n, hfst, hsnd⟩ :=
    (traceOne_pow_core_landing_iff
      (alpha := alpha)
      (beta := (S.rep i : TraceOneInt s))
      (r := p) hnorm).mp ⟨delta, hdelta⟩
  exact ⟨i, m, n, hfst, hsnd⟩

/-! ## Generic real-sector coordinate receiver -/

/-- The generic real sector endpoint in explicit TraceOne power coordinates. -/
theorem exists_realSector_powCoords_of_primeTraceOneStrippedIdealPacket
    {L : Type*} [Field L] [Algebra ℚ L]
    {p g u x : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ p}
    (P0 : PrimeAdicFactorPacket p g u x)
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ)
    (Q : PrimeTraceOneStrippedIdealPacket L P0 P)
    (hmod : p % 4 = 1) :
    let : Fact (∀ r : ℚ,
        r ^ 2 ≠ (signedPrimeParameter p : ℚ) + 1 * r) :=
      ⟨traceOneRat_no_rational_root P0.prime (by omega)⟩
    let : Field (TraceOneRat (signedPrimeParameter p)) :=
      traceOneRatField P0.prime (by omega)
    let : NumberField (TraceOneRat (signedPrimeParameter p)) := {
      to_charZero := charZero_of_injective_algebraMap (by
        intro q₁ q₂ hq
        have hre := congrArg QuadraticAlgebra.re hq
        change q₁ = q₂ at hre
        exact hre)
      to_finiteDimensional := inferInstance }
    let : IsDomain (TraceOneInt (signedPrimeParameter p)) :=
      (traceOneRatHom_injective _).isDomain (traceOneRatHom _)
    let : IsDedekindDomain (TraceOneInt (signedPrimeParameter p)) :=
      traceOneRat_isDedekindDomain P0.prime (by omega)
    classGroupPTorsionFreeAt (TraceOneInt (signedPrimeParameter p)) p →
      ∃ i : Fin p, ∃ m n : ℤ,
        (Q.residual * conj
          ((traceOnePrimeRealFinSectorSystem P0.prime hmod).rep i :
            TraceOneInt (signedPrimeParameter p))).fst =
            traceNorm ((traceOnePrimeRealFinSectorSystem P0.prime hmod).rep i :
              TraceOneInt (signedPrimeParameter p)) *
              (traceOnePowCoords (signedPrimeParameter p) m n p).1 ∧
        (Q.residual * conj
          ((traceOnePrimeRealFinSectorSystem P0.prime hmod).rep i :
            TraceOneInt (signedPrimeParameter p))).snd =
            traceNorm ((traceOnePrimeRealFinSectorSystem P0.prime hmod).rep i :
              TraceOneInt (signedPrimeParameter p)) *
              (traceOnePowCoords (signedPrimeParameter p) m n p).2 := by
  let : Fact (∀ r : ℚ,
      r ^ 2 ≠ (signedPrimeParameter p : ℚ) + 1 * r) :=
    ⟨traceOneRat_no_rational_root P0.prime (by omega)⟩
  let : Field (TraceOneRat (signedPrimeParameter p)) :=
    traceOneRatField P0.prime (by omega)
  let : NumberField (TraceOneRat (signedPrimeParameter p)) := {
    to_charZero := charZero_of_injective_algebraMap (by
      intro q₁ q₂ hq
      have hre := congrArg QuadraticAlgebra.re hq
      change q₁ = q₂ at hre
      exact hre)
    to_finiteDimensional := inferInstance }
  let : IsDomain (TraceOneInt (signedPrimeParameter p)) :=
    (traceOneRatHom_injective _).isDomain (traceOneRatHom _)
  let : IsDedekindDomain (TraceOneInt (signedPrimeParameter p)) :=
    traceOneRat_isDedekindDomain P0.prime (by omega)
  dsimp
  intro hfree
  obtain ⟨i, delta, hdelta⟩ :=
    exists_sector_mul_pow_of_primeTraceOneRealStrippedIdealPacket
      P0 P Q hmod hfree
  exact exists_powCoords_of_sector_mul_pow
    (traceOnePrimeRealFinSectorSystem P0.prime hmod) ⟨i, delta, hdelta⟩

/-! ## Terminal-axis and base-norm consequences -/

/-- The residual packet is not divisible by the prime on the norm side. -/
theorem PrimeTraceOneStrippedIdealPacket.residual_natAbs_norm_not_dvd
    {L : Type*} [Field L] [Algebra ℚ L]
    {p g u x : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ p}
    (P0 : PrimeAdicFactorPacket p g u x)
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ)
    (Q : PrimeTraceOneStrippedIdealPacket L P0 P) :
    ¬ p ∣ Int.natAbs (traceNorm Q.residual) := by
  let DP : PrimeDiscriminantPacket p (signedPrimeParameter p) :=
    signedPrimeDiscriminantPacket P0.prime (by
      have hodd := P0.odd
      omega)
  intro hnorm
  apply Q.residual_axis_terminal
  exact (DP.discrAxis_dvd_iff_prime_dvd_natAbs_norm Q.residual).mpr hnorm

/-- A terminal sector factor has a p-th-power base whose norm is prime to p. -/
theorem primeTraceOne_base_norm_not_dvd_of_sector_factor
    {p : ℕ} {s : ℤ} (P : PrimeDiscriminantPacket p s)
    {residual beta delta : TraceOneInt s}
    (hterminal : ¬ discrAxis s ∣ residual)
    (hfactor : residual = beta * delta ^ p) :
    ¬ p ∣ Int.natAbs (traceNorm delta) := by
  intro hdelta
  apply hterminal
  apply (P.discrAxis_dvd_iff_prime_dvd_natAbs_norm residual).mpr
  rw [hfactor, traceOne_norm_mul, traceOne_norm_pow, Int.natAbs_mul,
    Int.natAbs_pow]
  exact dvd_mul_of_dvd_right
    (hdelta.trans (dvd_pow_self (Int.natAbs (traceNorm delta)) P.prime.pos.ne')) _

/-- The real sector factorization and its terminal base-norm obstruction together. -/
theorem exists_realSector_mul_pow_with_baseNorm_not_dvd
    {L : Type*} [Field L] [Algebra ℚ L]
    {p g u x : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ p}
    (P0 : PrimeAdicFactorPacket p g u x)
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ)
    (Q : PrimeTraceOneStrippedIdealPacket L P0 P)
    (hmod : p % 4 = 1) :
    let : Fact (∀ r : ℚ,
        r ^ 2 ≠ (signedPrimeParameter p : ℚ) + 1 * r) :=
      ⟨traceOneRat_no_rational_root P0.prime (by omega)⟩
    let : Field (TraceOneRat (signedPrimeParameter p)) :=
      traceOneRatField P0.prime (by omega)
    let : NumberField (TraceOneRat (signedPrimeParameter p)) := {
      to_charZero := charZero_of_injective_algebraMap (by
        intro q₁ q₂ hq
        have hre := congrArg QuadraticAlgebra.re hq
        change q₁ = q₂ at hre
        exact hre)
      to_finiteDimensional := inferInstance }
    let : IsDomain (TraceOneInt (signedPrimeParameter p)) :=
      (traceOneRatHom_injective _).isDomain (traceOneRatHom _)
    let : IsDedekindDomain (TraceOneInt (signedPrimeParameter p)) :=
      traceOneRat_isDedekindDomain P0.prime (by omega)
    classGroupPTorsionFreeAt (TraceOneInt (signedPrimeParameter p)) p →
      ∃ i : Fin p, ∃ delta : TraceOneInt (signedPrimeParameter p),
        Q.residual =
          (traceOnePrimeRealFinSectorSystem P0.prime hmod).rep i * delta ^ p ∧
        ¬ p ∣ Int.natAbs (traceNorm delta) := by
  let : Fact (∀ r : ℚ,
      r ^ 2 ≠ (signedPrimeParameter p : ℚ) + 1 * r) :=
    ⟨traceOneRat_no_rational_root P0.prime (by omega)⟩
  let : Field (TraceOneRat (signedPrimeParameter p)) :=
    traceOneRatField P0.prime (by omega)
  let : NumberField (TraceOneRat (signedPrimeParameter p)) := {
    to_charZero := charZero_of_injective_algebraMap (by
      intro q₁ q₂ hq
      have hre := congrArg QuadraticAlgebra.re hq
      change q₁ = q₂ at hre
      exact hre)
    to_finiteDimensional := inferInstance }
  let : IsDomain (TraceOneInt (signedPrimeParameter p)) :=
    (traceOneRatHom_injective _).isDomain (traceOneRatHom _)
  let : IsDedekindDomain (TraceOneInt (signedPrimeParameter p)) :=
    traceOneRat_isDedekindDomain P0.prime (by omega)
  dsimp
  intro hfree
  obtain ⟨i, delta, hdelta⟩ :=
    exists_sector_mul_pow_of_primeTraceOneRealStrippedIdealPacket
      P0 P Q hmod hfree
  let DP : PrimeDiscriminantPacket p (signedPrimeParameter p) :=
    signedPrimeDiscriminantPacket P0.prime (by omega)
  refine ⟨i, delta, hdelta, ?_⟩
  exact primeTraceOne_base_norm_not_dvd_of_sector_factor DP
    Q.residual_axis_terminal hdelta

/-! ## Explicit p=5 Golden calibration -/

/-- The p=5 residual transported to the explicit Golden `s = 1` carrier. -/
noncomputable def traceOneFiveResidualToGolden
    {L : Type*} [Field L] [Algebra ℚ L]
    {g u x : ℕ} [Fact (Nat.Prime 5)]
    [IsCyclotomicExtension {5} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ 5}
    (P0 : PrimeAdicFactorPacket 5 g u x)
    (P : PrimeTraceOneCoordinatePacket L 5 ζ hζ)
    (Q : PrimeTraceOneStrippedIdealPacket L P0 P) : TraceOneInt 1 := by
  let hcarrier : TraceOneInt (signedPrimeParameter 5) = TraceOneInt 1 :=
    congrArg TraceOneInt signedPrimeParameter_five
  exact hcarrier ▸ Q.residual

/-- The p=5 Golden endpoint in the same explicit TraceOne coordinates. -/
theorem exists_goldenSector_powCoords_of_primeTraceOneStrippedIdealPacket_five
    {L : Type*} [Field L] [Algebra ℚ L]
    {g u x : ℕ} [Fact (Nat.Prime 5)]
    [IsCyclotomicExtension {5} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ 5}
    (P0 : PrimeAdicFactorPacket 5 g u x)
    (P : PrimeTraceOneCoordinatePacket L 5 ζ hζ)
    (Q : PrimeTraceOneStrippedIdealPacket L P0 P) :
    ∃ i : Fin 5, ∃ m n : ℤ,
      (traceOneFiveResidualToGolden P0 P Q * conj
        (goldenTraceOneFifthUnitPowerSectorSystem.rep i : TraceOneInt 1)).fst =
          traceNorm (goldenTraceOneFifthUnitPowerSectorSystem.rep i :
            TraceOneInt 1) * (traceOnePowCoords 1 m n 5).1 ∧
      (traceOneFiveResidualToGolden P0 P Q * conj
        (goldenTraceOneFifthUnitPowerSectorSystem.rep i : TraceOneInt 1)).snd =
          traceNorm (goldenTraceOneFifthUnitPowerSectorSystem.rep i :
            TraceOneInt 1) * (traceOnePowCoords 1 m n 5).2 := by
  let hcarrier : TraceOneInt (signedPrimeParameter 5) = TraceOneInt 1 :=
    congrArg TraceOneInt signedPrimeParameter_five
  let alpha : TraceOneInt 1 := hcarrier ▸ Q.residual
  let : EuclideanDomain (TraceOneInt (signedPrimeParameter 5)) :=
    hcarrier.symm ▸
      goldenTraceOneRingEquiv.symm.euclideanDomain
  let : IsDomain (TraceOneInt (signedPrimeParameter 5)) :=
    EuclideanDomain.instIsDomain _
  let : Fact (∀ r : ℚ,
      r ^ 2 ≠ (signedPrimeParameter 5 : ℚ) + 1 * r) :=
    ⟨traceOneRat_no_rational_root P0.prime (by norm_num)⟩
  let : Field (TraceOneRat (signedPrimeParameter 5)) :=
    traceOneRatField P0.prime (by norm_num)
  have hfactor :=
    exists_goldenSector_mul_fifth_of_primeTraceOneStrippedIdealPacket_five
      P0 P Q
  have hfactor' : ∃ i : Fin 5, ∃ delta : TraceOneInt 1,
      alpha = (goldenTraceOneFifthUnitPowerSectorSystem.rep i : TraceOneInt 1) *
        delta ^ 5 := by
    rcases hfactor with ⟨i, delta, hdelta⟩
    refine ⟨i, delta, ?_⟩
    change hcarrier ▸ Q.residual = _
    rw [hdelta]
    rfl
  exact exists_powCoords_of_sector_mul_pow
    goldenTraceOneFifthUnitPowerSectorSystem hfactor'

end

end DkMath.FLT.Prime
