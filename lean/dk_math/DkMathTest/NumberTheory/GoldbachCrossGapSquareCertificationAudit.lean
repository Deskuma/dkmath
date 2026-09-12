/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Goldbach

#print "file: DkMathTest.NumberTheory.GoldbachCrossGapSquareCertificationAudit"

/-!
# Cross-Gap square-shell certification audit

The generator in the concrete replay has degree one, while certification uses
the existing degree-two SquareBody envelope.  The examples do not assert any
near-balanced existence theorem.
-/

namespace DkMathTest.NumberTheory.GoldbachCrossGapSquareCertificationAudit

open DkMath.NumberTheory
open DkMath.NumberTheory.GoldbachCrossGapExchange
open DkMath.NumberTheory.GoldbachCrossGapEscape
open DkMath.NumberTheory.GoldbachCrossGapSquareCertification
open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic

/-- Coprimality alone does not certify a prime pair. -/
example : 25 + 27 = 52 ∧ Nat.Coprime 25 27 ∧
    ¬ (Nat.Prime 25 ∧ Nat.Prime 27) := by
  norm_num [Nat.Coprime]

/-- The diagonal prime pair is not a coprime pair. -/
example : 3 + 3 = 6 ∧ ¬ Nat.Coprime 3 3 ∧
    Nat.Prime 3 ∧ Nat.Prime 3 := by
  norm_num [Nat.Coprime]

lemma hthree_disjoint : SupportDisjointFrom (primeScalesUpTo 2) 3 := by
  apply supportDisjointFrom_primeScalesUpTo_iff.mpr
  intro q hq hqle hqd
  have hqeq : q = 2 := by
    have hq2 : 2 ≤ q := hq.two_le
    omega
  subst q
  norm_num at hqd

lemma hthree_certified : CrossGapSquareCertified 2 1 2 1 1 2 1 := by
  refine ⟨?_, ?_, ?_, ?_, hthree_disjoint, hthree_disjoint⟩ <;>
    decide +kernel

/-- Degree-one generators can use the independent degree-two square envelope. -/
example : CrossGapEvenFiberAt 3 1 2 1 1 2 1 := by
  decide +kernel

example :
    crossPairHeight 1 2 1 1 2 1 = 3 ∧
      2 < 3 ∧ 3 ≤ squareBody 2 := by
  decide +kernel

/-- The balanced window `n ± 0` enters the common shell anchored at `P=2`. -/
example :
    2 < 3 ∧ 3 ≤ squareBody 2 ∧ 2 < 3 ∧ 3 ≤ squareBody 2 := by
  apply crossPair_in_squareShell_of_balanced_window
    (n := 3) (w := 0) (P := 2)
    (d₁ := 1) (x₁ := 2) (u₁ := 1)
    (d₂ := 1) (x₂ := 2) (u₂ := 1)
  all_goals decide +kernel

example : ¬ Nat.Prime 9 := by
  norm_num

example : ¬ SupportDisjointFrom (primeScalesUpTo 3) 9 := by
  intro hdisj
  have hnotmem : 3 ∉ primeScalesUpTo 3 :=
    hdisj (q := 3) (by norm_num) (by norm_num)
  exact hnotmem (by norm_num [primeScalesUpTo])

/-- The concrete square-certified configuration closes to a local Goldbach pair. -/
example : GoldbachPairAt 3 := by
  exact goldbachPairAt_of_crossGapSquareCertified
    (n := 3) (P := 2)
    (d₁ := 1) (x₁ := 2) (u₁ := 1)
    (d₂ := 1) (x₂ := 2) (u₂ := 1)
    (by decide +kernel) hthree_certified

end DkMathTest.NumberTheory.GoldbachCrossGapSquareCertificationAudit

#print axioms DkMath.NumberTheory.GoldbachCrossGapSquareCertification.prime_pair_of_crossGapSquareCertified
#print axioms DkMath.NumberTheory.GoldbachCrossGapSquareCertification.crossPair_lower_bounds_of_balanced_window
#print axioms DkMath.NumberTheory.GoldbachCrossGapSquareCertification.crossPair_in_squareShell_of_balanced_window
#print axioms DkMath.NumberTheory.GoldbachCrossGapSquareCertification.crossGapSquareCertified_of_balanced_window
#print axioms DkMath.NumberTheory.GoldbachCrossGapSquareCertification.goldbachPairAt_of_crossGapSquareCertified
