/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Gauge.Value
import DkMath.Lib.NumberTheory.TraceOnePowerLanding

#print "file: DkMath.NumberTheory.Gauge.Landing"

/-!
# Neutral power and additive landing vocabulary

This module names ordinary power-image landing, Core-image landing, and
positive additive landing without making primality or an FLT conclusion part
of the definitions.  The TraceOne adapter below reuses the neutral
`DkMath.Lib.NumberTheory` receiver; no FLT module is imported here.
-/

namespace DkMath.NumberTheory.Gauge

/-! ## Neutral landing predicates -/

/-- Landing in the image of the `n`-th power map. -/
def PowerLanding {R : Type*} [Monoid R] (n : ℕ) (a : R) : Prop :=
  ∃ b : R, a = b ^ n

/-- Landing in `beta` times the image of the `n`-th power map. -/
def CorePowerLanding {R : Type*} [Monoid R]
    (n : ℕ) (alpha beta : R) : Prop :=
  ∃ gamma : R, alpha = beta * gamma ^ n

/-- An additive `n`-th-power landing over the natural numbers. -/
def AdditiveLanding (n x y : ℕ) : Prop :=
  ∃ z : ℕ, x ^ n + y ^ n = z ^ n

/-- A positive additive `n`-th-power landing over the natural numbers. -/
def PositiveAdditiveLanding (n x y : ℕ) : Prop :=
  ∃ z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
    x ^ n + y ^ n = z ^ n

/-! ## Thin neutral bridges -/

theorem powerLanding_iff_exists {R : Type*} [Monoid R]
    (n : ℕ) (a : R) :
    PowerLanding n a ↔ ∃ b : R, a = b ^ n :=
  Iff.rfl

theorem corePowerLanding_iff_exists {R : Type*} [Monoid R]
    (n : ℕ) (alpha beta : R) :
    CorePowerLanding n alpha beta ↔ ∃ gamma : R, alpha = beta * gamma ^ n :=
  Iff.rfl

theorem positiveAdditiveLanding_to_additiveLanding
    {n x y : ℕ} (h : PositiveAdditiveLanding n x y) :
    AdditiveLanding n x y := by
  rcases h with ⟨z, hx, hy, hz, hEq⟩
  exact ⟨z, hEq⟩

/-! ## ValueGauge necessary conditions -/

/-- A nonzero power landing has zero ValueGauge defect. -/
theorem powerLanding_valueGaugePure
    {n a : ℕ} (ha : a ≠ 0) (h : PowerLanding n a) :
    ValueGaugePure n a := by
  rcases h with ⟨b, hba⟩
  cases n with
  | zero =>
      rw [pow_zero] at hba
      rw [hba]
      simpa using (valueGaugePure_pow (n := 0) (a := 1) (by norm_num))
  | succ n =>
      have hb : b ≠ 0 := by
        intro hb0
        apply ha
        rw [hba, hb0]
        simp
      rw [hba]
      exact valueGaugePure_pow hb

/-- A positive additive landing has zero ValueGauge defect at its landed sum. -/
theorem positiveAdditiveLanding_valueGaugePure
    {n x y : ℕ} (h : PositiveAdditiveLanding n x y) :
    ValueGaugePure n (x ^ n + y ^ n) := by
  rcases h with ⟨z, hx, hy, hz, hEq⟩
  rw [hEq]
  exact valueGaugePure_pow (Nat.ne_of_gt hz)

/-! ## TraceOne CorePowerLanding adapter -/

open DkMath.NumberTheory.TraceOneQuadratic

/-- The existing TraceOne arbitrary-power receiver through `CorePowerLanding`.

This is only a definitional wrapper around
`traceOne_pow_core_landing_iff`; the coordinate reconstruction remains owned
by `DkMath.Lib.NumberTheory.TraceOnePowerLanding`.
-/
theorem corePowerLanding_traceOne_iff
    {s : ℤ} {alpha beta : TraceOneInt s} {r : ℕ}
    (hNorm : DkMath.NumberTheory.TraceOneQuadratic.norm beta ≠ 0) :
    CorePowerLanding r alpha beta ↔
      ∃ m n : ℤ,
        (alpha * conj beta).fst =
            DkMath.NumberTheory.TraceOneQuadratic.norm beta *
              (DkMath.Lib.NumberTheory.traceOnePowCoords s m n r).1 ∧
          (alpha * conj beta).snd =
            DkMath.NumberTheory.TraceOneQuadratic.norm beta *
              (DkMath.Lib.NumberTheory.traceOnePowCoords s m n r).2 := by
  change (∃ gamma : TraceOneInt s, alpha = beta * gamma ^ r) ↔ _
  exact DkMath.Lib.NumberTheory.traceOne_pow_core_landing_iff hNorm

end DkMath.NumberTheory.Gauge

#print axioms DkMath.NumberTheory.Gauge.positiveAdditiveLanding_to_additiveLanding
#print axioms DkMath.NumberTheory.Gauge.powerLanding_valueGaugePure
#print axioms DkMath.NumberTheory.Gauge.positiveAdditiveLanding_valueGaugePure
#print axioms DkMath.NumberTheory.Gauge.corePowerLanding_traceOne_iff
