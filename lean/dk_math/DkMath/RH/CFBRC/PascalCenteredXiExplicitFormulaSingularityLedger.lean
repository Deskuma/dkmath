/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiExplicitFormulaContourGeometry

/-!
# Singularity ledger for the symmetric explicit-formula window

This module records where the three summands in the XDP-008 completed-zeta
log-derivative decomposition may require separate contour bookkeeping.  The
ledger is intentionally pointwise and qualitative: it does not assign a
residue, identify a totalized value with a Laurent coefficient, or assert that
a contour may cross any listed location.

In particular, `Complex.Gammaℝ` is Mathlib's totalized meromorphic
representation.  Its zero set is recorded as an exceptional locus, but no
point value at that locus is interpreted as a classical pole value.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

/-! ## Location classes -/

/-- The location classes that have to be kept visible in a symmetric contour
transport argument. -/
inductive PascalExplicitFormulaSingularityClass
  | sZero
  | sOne
  | nontrivialZetaZero
  | trivialZetaZero
  | gammaExceptional
  deriving DecidableEq, Repr

/-- The ordinary-zeta, archimedean, and elementary summands of the XDP-008
decomposition. -/
inductive PascalExplicitFormulaTerm
  | ordinaryZeta
  | archimedean
  | elementary
  deriving DecidableEq, Repr

/-- The point `s = 0`, kept separate because the elementary correction has a
different bookkeeping role there from the zeta pole at `s = 1`. -/
def pascalExplicitFormulaAtSZero (s : ℂ) : Prop := s = 0

/-- The point `s = 1`, where the ordinary zeta factor has its classical
singularity in the contour ledger. -/
def pascalExplicitFormulaAtSOne (s : ℂ) : Prop := s = 1

/-- A nontrivial zeta-zero location, expressed with the open critical strip
conditions needed by the contour contract. -/
def pascalExplicitFormulaAtNontrivialZetaZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1

/-- A negative-even candidate location for the trivial zeta-zero class.

The definition records the classical location pattern without asserting a
residue or using a totalized pole value. -/
def pascalExplicitFormulaAtTrivialZetaZero (s : ℂ) : Prop :=
  ∃ n : ℕ, s = -(2 * (n : ℂ))

/-- The exceptional locus exposed by Mathlib's `Gammaℝ` zero-set API. -/
def pascalExplicitFormulaAtGammaExceptional (s : ℂ) : Prop :=
  Complex.Gammaℝ s = 0

/-- Membership of a point in one of the five singularity classes. -/
def pascalExplicitFormulaSingularityAt
    (c : PascalExplicitFormulaSingularityClass) (s : ℂ) : Prop :=
  match c with
  | .sZero => pascalExplicitFormulaAtSZero s
  | .sOne => pascalExplicitFormulaAtSOne s
  | .nontrivialZetaZero => pascalExplicitFormulaAtNontrivialZetaZero s
  | .trivialZetaZero => pascalExplicitFormulaAtTrivialZetaZero s
  | .gammaExceptional => pascalExplicitFormulaAtGammaExceptional s

/-! ## Term-by-class risk table -/

/-- A term/class pair is marked when that class can affect its contour
regularity or its factorization ledger.  This is a bookkeeping predicate, not
a theorem that the term is singular at every point satisfying the predicate.
-/
def pascalExplicitFormulaTermAtRisk
    (term : PascalExplicitFormulaTerm)
    (c : PascalExplicitFormulaSingularityClass) : Prop :=
  match term with
  | .ordinaryZeta =>
      c = .sOne ∨ c = .nontrivialZetaZero ∨ c = .trivialZetaZero
  | .archimedean => c = .gammaExceptional
  | .elementary => c = .sZero ∨ c = .sOne

/-- The ledger entry at a point: it lists every class whose location predicate
holds there. -/
def pascalExplicitFormulaSingularityLedger (s : ℂ) :
    Set PascalExplicitFormulaSingularityClass :=
  {c | pascalExplicitFormulaSingularityAt c s}

/-- The ordinary-zeta term is marked at the zeta-pole class. -/
theorem ordinaryZeta_termAtRisk_sOne :
    pascalExplicitFormulaTermAtRisk .ordinaryZeta .sOne := by
  simp [pascalExplicitFormulaTermAtRisk]

/-- The ordinary-zeta term is marked at the nontrivial-zero class. -/
theorem ordinaryZeta_termAtRisk_nontrivialZetaZero :
    pascalExplicitFormulaTermAtRisk .ordinaryZeta .nontrivialZetaZero := by
  simp [pascalExplicitFormulaTermAtRisk]

/-- The ordinary-zeta term is marked at the trivial-zero class. -/
theorem ordinaryZeta_termAtRisk_trivialZetaZero :
    pascalExplicitFormulaTermAtRisk .ordinaryZeta .trivialZetaZero := by
  simp [pascalExplicitFormulaTermAtRisk]

/-- The archimedean term is marked at the Gammaℝ exceptional class. -/
theorem archimedean_termAtRisk_gammaExceptional :
    pascalExplicitFormulaTermAtRisk .archimedean .gammaExceptional := by
  simp [pascalExplicitFormulaTermAtRisk]

/-- The elementary term is marked at both distinguished elementary locations.
-/
theorem elementary_termAtRisk_sZero_sOne :
    pascalExplicitFormulaTermAtRisk .elementary .sZero ∧
      pascalExplicitFormulaTermAtRisk .elementary .sOne := by
  constructor <;> simp [pascalExplicitFormulaTermAtRisk]

end DkMath.RH.CFBRCProjection
