/-
Copyright (c) 2026 DkMath contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: DkMath contributors.
-/

import DkMath.Lib.Cosmic.GTailBoundary

#print "file: DkMath.NumberTheory.MultiGauge.Basic"

/-!
# Basic two-stage multi-gauge data

This module provides the natural-number observer and balance packet used by
the first multi-gauge divisibility checkpoint.  The transition law is kept at
the level of cross multiplication, so later applications can supply their own
normalization semantics without changing the prime-transport API.
-/

namespace DkMath.NumberTheory.MultiGauge

open DkMath.CosmicFormula

/-! ## One-stage observer -/

/-- A coprime natural-number coordinate pair for the GN observer. -/
structure GNGaugeStage (d : ℕ) where
  x : ℕ
  u : ℕ
  coprime : Nat.Coprime x u

/-- The canonical `r = 1` normalized tail observed at a stage. -/
def GNGaugeStage.gnValue {d : ℕ} (s : GNGaugeStage d) : ℕ :=
  GTail d 1 s.x s.u

/-- The full natural-number divisibility observer at a stage. -/
def GNGaugeStage.value {d : ℕ} (s : GNGaugeStage d) : ℕ :=
  s.x * s.gnValue

/-- A prime is caught when it divides the stage observer. -/
def PrimeCaught {d : ℕ} (q : ℕ) (s : GNGaugeStage d) : Prop :=
  q ∣ s.value

/-- A prime escapes when it does not divide the stage observer. -/
def PrimeEscapes {d : ℕ} (q : ℕ) (s : GNGaugeStage d) : Prop :=
  ¬ q ∣ s.value

/-! ## Concrete two-stage transition -/

/--
A two-stage transition with positive cross-multiplication coefficients.

The balance orientation is `second.value * denominator =
first.value * numerator`.  Thus numerator support can introduce a prime at
the second stage, while denominator support can remove one from the first.
-/
structure GNGaugeTransition (d : ℕ) where
  first : GNGaugeStage d
  second : GNGaugeStage d
  numerator : ℕ
  denominator : ℕ
  numerator_pos : 0 < numerator
  denominator_pos : 0 < denominator
  balance : second.value * denominator = first.value * numerator

end DkMath.NumberTheory.MultiGauge
