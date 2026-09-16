/-
Copyright (c) 2026 DkMath contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: DkMath contributors.
-/

import DkMath.NumberTheory.MultiGauge.Basic
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.MultiGauge.RawNormalization"

/-!
# Raw/primitive normalization for the multi-gauge observer

The primitive `GNGaugeStage` is the coprime core.  This module adds the raw
coordinate layer above it.  A common scale is retained in the raw pair,
normalized by its gcd, and transported through the homogeneous observer.
All statements here are finite natural-number identities; this module does
not provide a prime or a Goldbach provider.
-/

namespace DkMath.NumberTheory.MultiGauge

open DkMath.CosmicFormula

/-! ## Raw stages and synchronized scaling -/

/-- An unrestricted natural-number coordinate pair for the GN observer. -/
structure GNRawGaugeStage (d : ℕ) where
  x : ℕ
  u : ℕ

/-- The raw `r = 1` GN tail. -/
def GNRawGaugeStage.gnValue {d : ℕ} (s : GNRawGaugeStage d) : ℕ :=
  GTail d 1 s.x s.u

/-- The raw GN observer, before removing a common coordinate scale. -/
def GNRawGaugeStage.value {d : ℕ} (s : GNRawGaugeStage d) : ℕ :=
  s.x * s.gnValue

/-- The common coordinate scale of a raw stage. -/
def GNRawGaugeStage.scale {d : ℕ} (s : GNRawGaugeStage d) : ℕ :=
  Nat.gcd s.x s.u

/-- Synchronized multiplication of both raw coordinates. -/
def GNRawGaugeStage.scaleBy {d : ℕ} (k : ℕ) (s : GNRawGaugeStage d) :
    GNRawGaugeStage d :=
  { x := k * s.x
    u := k * s.u }

/-- Raw prime capture. -/
def RawPrimeCaught {d : ℕ} (q : ℕ) (s : GNRawGaugeStage d) : Prop :=
  q ∣ s.value

/-- Raw prime escape. -/
def RawPrimeEscapes {d : ℕ} (q : ℕ) (s : GNRawGaugeStage d) : Prop :=
  ¬ q ∣ s.value

/-- The raw observer is homogeneous of degree `d` under synchronized scaling. -/
theorem GNRawGaugeStage.value_scaleBy
    (k : ℕ) (s : GNRawGaugeStage d) :
    (s.scaleBy k).value = k ^ d * s.value := by
  change (k * s.x) * GTail d 1 (k * s.x) (k * s.u) =
    k ^ d * (s.x * GTail d 1 s.x s.u)
  have hbase := add_pow_eq_mul_GTail_one_add_gap d s.x s.u
  have hscaled := add_pow_eq_mul_GTail_one_add_gap d (k * s.x) (k * s.u)
  have hcancel :
      (k * s.x) * GTail d 1 (k * s.x) (k * s.u) + k ^ d * s.u ^ d =
        k ^ d * (s.x * GTail d 1 s.x s.u) + k ^ d * s.u ^ d := by
    calc
      (k * s.x) * GTail d 1 (k * s.x) (k * s.u) + k ^ d * s.u ^ d =
          (k * s.x) * GTail d 1 (k * s.x) (k * s.u) + (k * s.u) ^ d := by
            rw [mul_pow]
      _ = (k * s.x + k * s.u) ^ d := hscaled.symm
      _ = (k * (s.x + s.u)) ^ d := by rw [Nat.mul_add]
      _ = k ^ d * (s.x + s.u) ^ d := by rw [mul_pow]
      _ = k ^ d * (s.x * GTail d 1 s.x s.u + s.u ^ d) := by rw [hbase]
      _ = k ^ d * (s.x * GTail d 1 s.x s.u) + k ^ d * s.u ^ d := by
        rw [Nat.mul_add]
  exact Nat.add_right_cancel hcancel

/-! ## Gcd normalization -/

/-- The underlying raw pair of the gcd-normalized coordinates. -/
def GNRawGaugeStage.primitiveRawStage
    (s : GNRawGaugeStage d) : GNRawGaugeStage d :=
  { x := s.x / s.scale
    u := s.u / s.scale }

/-- The coprime stage obtained from a raw stage with positive gcd scale. -/
def GNRawGaugeStage.primitiveStage
    (s : GNRawGaugeStage d) (hg : 0 < s.scale) : GNGaugeStage d :=
  { x := (s.primitiveRawStage).x
    u := (s.primitiveRawStage).u
    coprime := Nat.coprime_div_gcd_div_gcd hg }

theorem GNRawGaugeStage.x_eq_scale_mul_primitiveX
    (s : GNRawGaugeStage d) (hg : 0 < s.scale) :
    s.x = s.scale * (s.primitiveStage hg).x := by
  dsimp [GNRawGaugeStage.primitiveStage]
  rw [Nat.mul_comm]
  exact (Nat.div_mul_cancel (Nat.gcd_dvd_left s.x s.u)).symm

theorem GNRawGaugeStage.u_eq_scale_mul_primitiveU
    (s : GNRawGaugeStage d) (hg : 0 < s.scale) :
    s.u = s.scale * (s.primitiveStage hg).u := by
  dsimp [GNRawGaugeStage.primitiveStage]
  rw [Nat.mul_comm]
  exact (Nat.div_mul_cancel (Nat.gcd_dvd_right s.x s.u)).symm

theorem GNRawGaugeStage.scaleBy_primitiveStage_eq
    (s : GNRawGaugeStage d) (hg : 0 < s.scale) :
    GNRawGaugeStage.scaleBy s.scale (s.primitiveRawStage) = s := by
  cases s with
  | mk x u =>
    simp only [GNRawGaugeStage.scaleBy, GNRawGaugeStage.primitiveRawStage,
      GNRawGaugeStage.scale]
    congr 1
    · rw [Nat.mul_comm]
      exact Nat.div_mul_cancel (Nat.gcd_dvd_left x u)
    · rw [Nat.mul_comm]
      exact Nat.div_mul_cancel (Nat.gcd_dvd_right x u)

/-- Exact factorization of a raw observer into scale and primitive observer. -/
theorem GNRawGaugeStage.value_eq_scale_pow_mul_primitiveValue
    (s : GNRawGaugeStage d) (hg : 0 < s.scale) :
    s.value = s.scale ^ d * (s.primitiveStage hg).value := by
  have hstage := s.scaleBy_primitiveStage_eq hg
  have hvalue := congrArg GNRawGaugeStage.value hstage
  calc
    s.value = (GNRawGaugeStage.scaleBy s.scale (s.primitiveRawStage)).value := hvalue.symm
    _ = s.scale ^ d * (s.primitiveStage hg).value :=
      by
        rw [GNRawGaugeStage.value_scaleBy]
        rfl

/-! ## Prime support of the factorization -/

theorem prime_dvd_scale_pow_iff
    {d q a : ℕ} (hq : Nat.Prime q) (hd : 1 ≤ d) :
    q ∣ a ^ d ↔ q ∣ a := by
  constructor
  · exact hq.dvd_of_dvd_pow
  · exact fun h => dvd_pow h (by omega)

/-- A prime in a raw observer is either in the common scale or in the
primitive observer.  The degree assumption is explicit because the scale
support enters through `scale ^ d`. -/
theorem rawPrimeCaught_iff_scale_or_primitiveCaught
    {d q : ℕ} (hq : Nat.Prime q) (hd : 1 ≤ d)
    (s : GNRawGaugeStage d) (hg : 0 < s.scale) :
    RawPrimeCaught q s ↔
      q ∣ s.scale ∨ PrimeCaught q (s.primitiveStage hg) := by
  change q ∣ s.value ↔ q ∣ s.scale ∨ q ∣ (s.primitiveStage hg).value
  rw [s.value_eq_scale_pow_mul_primitiveValue hg, hq.dvd_mul,
    prime_dvd_scale_pow_iff hq hd]

/-- The corresponding escape decomposition. -/
theorem rawPrimeEscapes_iff_scale_and_primitiveEscapes
    {d q : ℕ} (hq : Nat.Prime q) (hd : 1 ≤ d)
    (s : GNRawGaugeStage d) (hg : 0 < s.scale) :
    RawPrimeEscapes q s ↔
      (¬ q ∣ s.scale) ∧ PrimeEscapes q (s.primitiveStage hg) := by
  change (¬ q ∣ s.value) ↔
    (¬ q ∣ s.scale) ∧ (¬ q ∣ (s.primitiveStage hg).value)
  rw [s.value_eq_scale_pow_mul_primitiveValue hg, hq.dvd_mul,
    prime_dvd_scale_pow_iff hq hd]
  simp only [not_or]

/-! ## Concrete common-scale prime transport -/

/-- A prime escaping a raw stage cannot be captured after synchronized scaling
unless it divides the newly introduced scale factor. -/
theorem prime_dvd_scale_factor_of_rawEscape_of_scaledCaught
    {d q k : ℕ} (hq : Nat.Prime q) (s : GNRawGaugeStage d)
    (hEscape : RawPrimeEscapes q s)
    (hCaught : RawPrimeCaught q (s.scaleBy k)) :
    q ∣ k := by
  rw [RawPrimeCaught, GNRawGaugeStage.value_scaleBy] at hCaught
  rcases hq.dvd_mul.mp hCaught with hpow | hvalue
  · exact hq.dvd_of_dvd_pow hpow
  · exact False.elim (hEscape hvalue)

/-- Existing raw capture persists under every synchronized scaling. -/
theorem rawCaught_scaleBy_of_rawCaught
    {d q k : ℕ} (s : GNRawGaugeStage d)
    (hCaught : RawPrimeCaught q s) :
    RawPrimeCaught q (s.scaleBy k) := by
  rw [RawPrimeCaught, GNRawGaugeStage.value_scaleBy]
  exact dvd_mul_of_dvd_right hCaught _

/-! ## Executable/provable regressions -/

def regressionRawStage : GNRawGaugeStage 2 :=
  { x := 1
    u := 2 }

theorem regression_scale_grows :
    (regressionRawStage.scaleBy 3).scale = 3 := by
  norm_num [regressionRawStage, GNRawGaugeStage.scaleBy,
    GNRawGaugeStage.scale]

theorem regression_value_scales :
    (regressionRawStage.scaleBy 3).value = 3 ^ 2 * regressionRawStage.value := by
  exact GNRawGaugeStage.value_scaleBy 3 regressionRawStage

theorem regression_primitive_coordinates_recover :
    let h : 0 < regressionRawStage.scale := by norm_num [regressionRawStage,
      GNRawGaugeStage.scale]
    (regressionRawStage.primitiveStage h).x = 1 ∧
      (regressionRawStage.primitiveStage h).u = 2 := by
  norm_num [regressionRawStage, GNRawGaugeStage.scale,
    GNRawGaugeStage.primitiveStage, GNRawGaugeStage.primitiveRawStage]

theorem regression_new_prime_is_scale_support :
    RawPrimeCaught 3 (regressionRawStage.scaleBy 3) ∧
      ¬ RawPrimeCaught 3 regressionRawStage ∧
      3 ∣ (regressionRawStage.scaleBy 3).scale := by
  norm_num [RawPrimeCaught, regressionRawStage, GNRawGaugeStage.scaleBy,
    GNRawGaugeStage.value, GNRawGaugeStage.gnValue,
    GNRawGaugeStage.scale, GTail, Finset.sum_range_succ]

end DkMath.NumberTheory.MultiGauge
