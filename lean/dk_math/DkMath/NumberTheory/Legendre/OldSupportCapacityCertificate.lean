/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.OldSupportCapacity

#print "file: DkMath.NumberTheory.Legendre.OldSupportCapacityCertificate"

/-! Computable bounded-divisibility certificates for the existing support-capacity consumer. -/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic

/-- Exact computable normal form of the actual bounded support observer. -/
def boundedSquareSupport (n r : ℕ) : Finset ℕ :=
  (primeScalesUpTo n).filter (fun q => q ∣ n ^ 2 + r)

theorem squareOffsetPrimeSupport_eq_boundedSquareSupport (n r : ℕ) :
    squareOffsetPrimeSupport n r = boundedSquareSupport n r := by
  ext q
  simp [boundedSquareSupport, mem_squareOffsetPrimeSupport, and_assoc]

/-- Seats of an explicitly supplied family on one divisibility wave. -/
def oldSupportSeatFiber (n : ℕ) (R : Finset ℕ) (q : ℕ) : Finset ℕ :=
  R.filter (fun r => q ∣ n ^ 2 + r)

/-- Fiber occupancy at most one is equivalent to actual support disjointness. -/
theorem pairwiseDisjoint_squareSupport_iff_fiber_card (n : ℕ) (R : Finset ℕ) :
    (R : Set ℕ).PairwiseDisjoint (squareOffsetPrimeSupport n) ↔
      ∀ q ∈ primeScalesUpTo n, (oldSupportSeatFiber n R q).card ≤ 1 := by
  classical
  constructor
  · intro hfree q hq
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have ha' := Finset.mem_filter.mp ha
    have hb' := Finset.mem_filter.mp hb
    by_contra hne
    have hdisj := hfree ha'.1 hb'.1 hne
    have hp := mem_primeScalesUpTo.mp hq
    exact Finset.disjoint_left.mp hdisj
      (mem_squareOffsetPrimeSupport.mpr ⟨hp.1, hp.2, ha'.2⟩)
      (mem_squareOffsetPrimeSupport.mpr ⟨hp.1, hp.2, hb'.2⟩)
  · intro hcard a ha b hb hne
    change Disjoint (squareOffsetPrimeSupport n a) (squareOffsetPrimeSupport n b)
    rw [Finset.disjoint_left]
    intro q hqa hqb
    have hpa := mem_squareOffsetPrimeSupport.mp hqa
    have hpb := mem_squareOffsetPrimeSupport.mp hqb
    have he := Finset.card_le_one.mp (hcard q (mem_primeScalesUpTo.mpr ⟨hpa.1, hpa.2.1⟩))
      a (Finset.mem_filter.mpr ⟨ha, hpa.2.2⟩) b (Finset.mem_filter.mpr ⟨hb, hpb.2.2⟩)
    exact hne he

/-- The semantic certificate contains exactly the existing family and capacity hypotheses. -/
def OldSupportCapacityCertificate (n : ℕ) (R : Finset ℕ) : Prop :=
  PairwiseOldSupportDisjointSquareSeatFamily n R ∧ (primeScalesUpTo n).card < R.card

/-- The checker recomputes actual divisibility; support labels are not inputs. -/
def checkOldSupportCapacityCertificate (n : ℕ) (R : Finset ℕ) : Bool :=
  decide ((∀ r ∈ R, 1 ≤ r ∧ r ≤ 2 * n) ∧
    (∀ q ∈ primeScalesUpTo n, (oldSupportSeatFiber n R q).card ≤ 1) ∧
    (primeScalesUpTo n).card < R.card)

theorem checkOldSupportCapacityCertificate_eq_true_iff (n : ℕ) (R : Finset ℕ) :
    checkOldSupportCapacityCertificate n R = true ↔ OldSupportCapacityCertificate n R := by
  simp only [checkOldSupportCapacityCertificate, decide_eq_true_eq,
    OldSupportCapacityCertificate, PairwiseOldSupportDisjointSquareSeatFamily,
    pairwiseDisjoint_squareSupport_iff_fiber_card, SquareOffset]
  tauto

/-- This wrapper delegates to the existing capacity consumer without duplicating its proof. -/
theorem exists_prime_squareCell_of_oldSupportCapacityCertificate {n : ℕ} {R : Finset ℕ}
    (hn : 0 < n) (hc : OldSupportCapacityCertificate n R) : ∃ p, p.Prime ∧ SquareCell n p :=
  exists_prime_squareCell_of_primeWorld_card_lt_pairwiseOldSupportDisjointSquareSeatFamilies hn hc.1 hc.2

end DkMath.NumberTheory.Legendre
