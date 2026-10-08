/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.CoarseTownSourceMultiplicity
import DkMathTest.NumberTheory.LegendreSurvivor297Calibration
import DkMathTest.NumberTheory.LegendreDeletion1031Data
import DkMathTest.NumberTheory.LegendreHandoffRegression
import DkMathTest.NumberTheory.LegendreRetained297Calibration
import DkMathTest.NumberTheory.LegendreRetained1031Calibration

#print "file: DkMathTest.NumberTheory.LegendreTerminalProductCalibration"

namespace DkMathTest.LegendreTerminalProductCalibration

open DkMath.NumberTheory.Legendre DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open DkMathTest.LegendreSurvivor297Calibration DkMathTest.LegendreDeletion1031Data
open scoped BigOperators

set_option maxRecDepth 100000

/-- Compute endpoints over the certified actual town without recomputing support at every seat. -/
private theorem terminal_computation {S : Finset ℕ} (hS : KnownPrimeScales S)
    {n a : ℕ} (ha : a ∈ coarsePrimeWorldFullTown S n) :
    coarseTownTerminalPrimesAt S n a = (squareOffsetPrimeSupport n a).filter
      (fun q => ∀ b ∈ coarsePrimeWorldFullTown S n, q ∣ n ^ 2 + b → b ≤ a) := by
  classical
  apply Finset.filter_congr
  intro q hq
  have ho := coarse_survivor_support_outside (coarseFullTown_survivor hS ha) hq
  have hf := coarseFullTownPrimeFiber_eq_divisibility_of_mem ho
  change (a ∈ coarseFullTownPrimeFiber S n q ∧ ∀ b ∈ coarseFullTownPrimeFiber S n q, b ≤ a) ↔ _
  rw [hf]
  unfold coarseTownDivisibilityFiber oldSupportSeatFiber
  have hd := (mem_squareOffsetPrimeSupport.mp hq).2.2
  simp only [Finset.mem_filter,ha,hd,true_and,and_imp]

private theorem continuing_computation {S : Finset ℕ} (hS : KnownPrimeScales S)
    {n a : ℕ} (ha : a ∈ coarsePrimeWorldFullTown S n) :
    coarseTownDeletionWitnessPrimes S n a = squareOffsetPrimeSupport n a \ coarseTownTerminalPrimesAt S n a := by
  have h := coarseTown_terminal_continuing_partition hS ha
  ext q
  constructor
  · intro hq
    exact Finset.mem_sdiff.mpr ⟨coarseTownDeletionWitnessPrimes_subset_support _ _ _ hq,
      fun ht => Finset.disjoint_left.mp h.2 ht hq⟩
  · intro hq
    have hs := (Finset.mem_sdiff.mp hq).1
    rw [← h.1] at hs
    rcases Finset.mem_union.mp hs with ht | hc
    · exact False.elim ((Finset.mem_sdiff.mp hq).2 ht)
    · exact hc

private theorem support_computation (n a : ℕ) :
    squareOffsetPrimeSupport n a = (primeScalesUpTo n).filter (fun q => q ∣ n ^ 2 + a) := by
  rw [squareOffsetPrimeSupport_eq_boundedSquareSupport]
  rfl

private theorem seat11 : 19 ∈ coarsePrimeWorldFullTown ({3} : Finset ℕ) 11 := by decide +kernel
private theorem scales3 : KnownPrimeScales ({3} : Finset ℕ) := by
  intro q hq
  simp only [Finset.mem_singleton] at hq
  subst q
  decide +kernel

theorem support11_checked : squareOffsetPrimeSupport 11 19 = ({2,5,7} : Finset ℕ) := by
  rw [support_computation]
  decide +kernel

theorem terminal11_checked : coarseTownTerminalPrimesAt ({3} : Finset ℕ) 11 19 = ({5,7} : Finset ℕ) := by
  rw [terminal_computation scales3 seat11,support11_checked]
  decide +kernel

theorem continuing11_checked : coarseTownDeletionWitnessPrimes ({3} : Finset ℕ) 11 19 = ({2} : Finset ℕ) := by
  rw [continuing_computation scales3 seat11,support11_checked,terminal11_checked]
  decide +kernel

theorem partition11_checked :
    coarseTownTerminalPrimesAt ({3} : Finset ℕ) 11 19 ∪ coarseTownDeletionWitnessPrimes ({3} : Finset ℕ) 11 19 =
      squareOffsetPrimeSupport 11 19 ∧
      Disjoint (coarseTownTerminalPrimesAt ({3} : Finset ℕ) 11 19) (coarseTownDeletionWitnessPrimes ({3} : Finset ℕ) 11 19) :=
  coarseTown_terminal_continuing_partition scales3 seat11

theorem products11_checked :
    (coarseTownTerminalPrimesAt ({3} : Finset ℕ) 11 19).prod id = 35 ∧
    (coarseTownDeletionWitnessPrimes ({3} : Finset ℕ) 11 19).prod id = 2 ∧
    (squareOffsetPrimeSupport 11 19).prod id = 70 := by
  rw [terminal11_checked,continuing11_checked,support11_checked]
  decide +kernel

theorem divisibility11_checked :
    (coarseTownTerminalPrimesAt ({3} : Finset ℕ) 11 19).prod id *
      (coarseTownDeletionWitnessPrimes ({3} : Finset ℕ) 11 19).prod id ∣ 11 ^ 2 + 19 :=
  coarseTown_terminal_continuing_product_dvd scales3 seat11

theorem power11_checked : 2 ^ (squareOffsetPrimeSupport 11 19).card ≤ 11 ^ 2 + 19 := by
  have h := squareOffsetPrimeSupport_power_bounds (n := 11) (a := 19) (B := 2)
    (by constructor <;> decide)
    (fun _q hq => (mem_squareOffsetPrimeSupport.mp hq).1.two_le)
  exact h.1.trans h.2.1

private theorem seat297_350 : 350 ∈ coarsePrimeWorldFullTown (primeScalesUpTo 10) 297 := by
  rw [town297Seats_eq_production]
  decide +kernel

private theorem seat297_44 : 44 ∈ coarsePrimeWorldFullTown (primeScalesUpTo 10) 297 := by
  rw [town297Seats_eq_production]
  decide +kernel

theorem support297_shared_checked : squareOffsetPrimeSupport 297 350 = ({19,59,79} : Finset ℕ) := by
  rw [support_computation,oldPrimes297_eq_production]
  decide +kernel

theorem terminal297_shared_checked : coarseTownTerminalPrimesAt (primeScalesUpTo 10) 297 350 = ({59,79} : Finset ℕ) := by
  rw [terminal_computation (knownPrimeScales_primeScalesUpTo 10) seat297_350,
    support297_shared_checked,town297Seats_eq_production]
  decide +kernel

theorem continuing297_shared_checked : coarseTownDeletionWitnessPrimes (primeScalesUpTo 10) 297 350 = ({19} : Finset ℕ) := by
  rw [continuing_computation (knownPrimeScales_primeScalesUpTo 10) seat297_350,
    support297_shared_checked,terminal297_shared_checked]
  decide +kernel

theorem products297_shared_checked :
    (coarseTownTerminalPrimesAt (primeScalesUpTo 10) 297 350).prod id = 4661 ∧
    (coarseTownDeletionWitnessPrimes (primeScalesUpTo 10) 297 350).prod id = 19 ∧
    (squareOffsetPrimeSupport 297 350).prod id = 88559 := by
  rw [terminal297_shared_checked,continuing297_shared_checked,support297_shared_checked]
  decide +kernel

theorem partition297_shared_checked :
    coarseTownTerminalPrimesAt (primeScalesUpTo 10) 297 350 ∪ coarseTownDeletionWitnessPrimes (primeScalesUpTo 10) 297 350 =
      squareOffsetPrimeSupport 297 350 ∧
    Disjoint (coarseTownTerminalPrimesAt (primeScalesUpTo 10) 297 350) (coarseTownDeletionWitnessPrimes (primeScalesUpTo 10) 297 350) :=
  coarseTown_terminal_continuing_partition (knownPrimeScales_primeScalesUpTo 10) seat297_350

theorem divisibility297_shared_checked :
    (coarseTownTerminalPrimesAt (primeScalesUpTo 10) 297 350).prod id *
      (coarseTownDeletionWitnessPrimes (primeScalesUpTo 10) 297 350).prod id ∣ 297 ^ 2 + 350 :=
  coarseTown_terminal_continuing_product_dvd (knownPrimeScales_primeScalesUpTo 10) seat297_350

theorem power297_shared_checked :
    11 ^ (squareOffsetPrimeSupport 297 350).card ≤ 297 ^ 2 + 350 :=
  (coarseTown_initial_support_power_bounds seat297_350).1.trans
    (coarseTown_initial_support_power_bounds seat297_350).2.1

theorem support297_branch_checked : squareOffsetPrimeSupport 297 44 = ({11,71,113} : Finset ℕ) := by
  rw [support_computation,oldPrimes297_eq_production]
  decide +kernel

theorem terminal297_branch_checked : coarseTownTerminalPrimesAt (primeScalesUpTo 10) 297 44 = ({113} : Finset ℕ) := by
  rw [terminal_computation (knownPrimeScales_primeScalesUpTo 10) seat297_44,
    support297_branch_checked,town297Seats_eq_production]
  decide +kernel

theorem continuing297_branch_checked : coarseTownDeletionWitnessPrimes (primeScalesUpTo 10) 297 44 = ({11,71} : Finset ℕ) := by
  rw [continuing_computation (knownPrimeScales_primeScalesUpTo 10) seat297_44,
    support297_branch_checked,terminal297_branch_checked]
  decide +kernel

theorem products297_branch_checked :
    (coarseTownTerminalPrimesAt (primeScalesUpTo 10) 297 44).prod id = 113 ∧
    (coarseTownDeletionWitnessPrimes (primeScalesUpTo 10) 297 44).prod id = 781 ∧
    (squareOffsetPrimeSupport 297 44).prod id = 88253 := by
  rw [terminal297_branch_checked,continuing297_branch_checked,support297_branch_checked]
  decide +kernel

theorem partition297_branch_checked :
    coarseTownTerminalPrimesAt (primeScalesUpTo 10) 297 44 ∪ coarseTownDeletionWitnessPrimes (primeScalesUpTo 10) 297 44 =
      squareOffsetPrimeSupport 297 44 ∧
    Disjoint (coarseTownTerminalPrimesAt (primeScalesUpTo 10) 297 44) (coarseTownDeletionWitnessPrimes (primeScalesUpTo 10) 297 44) :=
  coarseTown_terminal_continuing_partition (knownPrimeScales_primeScalesUpTo 10) seat297_44

theorem divisibility297_branch_checked :
    (coarseTownTerminalPrimesAt (primeScalesUpTo 10) 297 44).prod id *
      (coarseTownDeletionWitnessPrimes (primeScalesUpTo 10) 297 44).prod id ∣ 297 ^ 2 + 44 :=
  coarseTown_terminal_continuing_product_dvd (knownPrimeScales_primeScalesUpTo 10) seat297_44

theorem power297_branch_checked : 11 ^ (squareOffsetPrimeSupport 297 44).card ≤ 297 ^ 2 + 44 :=
  (coarseTown_initial_support_power_bounds seat297_44).1.trans
    (coarseTown_initial_support_power_bounds seat297_44).2.1

private theorem seat1031_90 : 90 ∈ coarsePrimeWorldFullTown (primeScalesUpTo 10) 1031 := by
  rw [town1031Seats_eq_production]
  decide +kernel

theorem support1031_checked : squareOffsetPrimeSupport 1031 90 = ({11,241,401} : Finset ℕ) := by
  rw [support_computation,oldPrimes1031_eq_production]
  decide +kernel

theorem terminal1031_checked : coarseTownTerminalPrimesAt (primeScalesUpTo 10) 1031 90 = ({241,401} : Finset ℕ) := by
  rw [terminal_computation (knownPrimeScales_primeScalesUpTo 10) seat1031_90,
    support1031_checked,town1031Seats_eq_production]
  decide +kernel

theorem continuing1031_checked : coarseTownDeletionWitnessPrimes (primeScalesUpTo 10) 1031 90 = ({11} : Finset ℕ) := by
  rw [continuing_computation (knownPrimeScales_primeScalesUpTo 10) seat1031_90,
    support1031_checked,terminal1031_checked]
  decide +kernel

theorem products1031_checked :
    (coarseTownTerminalPrimesAt (primeScalesUpTo 10) 1031 90).prod id = 96641 ∧
    (coarseTownDeletionWitnessPrimes (primeScalesUpTo 10) 1031 90).prod id = 11 ∧
    (squareOffsetPrimeSupport 1031 90).prod id = 1063051 := by
  rw [terminal1031_checked,continuing1031_checked,support1031_checked]
  decide +kernel

theorem partition1031_checked :
    coarseTownTerminalPrimesAt (primeScalesUpTo 10) 1031 90 ∪ coarseTownDeletionWitnessPrimes (primeScalesUpTo 10) 1031 90 =
      squareOffsetPrimeSupport 1031 90 ∧
    Disjoint (coarseTownTerminalPrimesAt (primeScalesUpTo 10) 1031 90) (coarseTownDeletionWitnessPrimes (primeScalesUpTo 10) 1031 90) :=
  coarseTown_terminal_continuing_partition (knownPrimeScales_primeScalesUpTo 10) seat1031_90

theorem divisibility1031_checked :
    (coarseTownTerminalPrimesAt (primeScalesUpTo 10) 1031 90).prod id *
      (coarseTownDeletionWitnessPrimes (primeScalesUpTo 10) 1031 90).prod id ∣ 1031 ^ 2 + 90 :=
  coarseTown_terminal_continuing_product_dvd (knownPrimeScales_primeScalesUpTo 10) seat1031_90

theorem power1031_checked : 11 ^ (squareOffsetPrimeSupport 1031 90).card ≤ 1031 ^ 2 + 90 :=
  (coarseTown_initial_support_power_bounds seat1031_90).1.trans
    (coarseTown_initial_support_power_bounds seat1031_90).2.1

theorem terminal_sums297_checked :
    (∑ a ∈ coarseTownDeletionVertices (primeScalesUpTo 10) 297,
      (coarseTownTerminalPrimesAt (primeScalesUpTo 10) 297 a).card) = 9 ∧
    (∑ a ∈ coarseTownRightDeletionVertices (primeScalesUpTo 10) 297,
      (coarseTownMinimumTerminalPrimesAt (primeScalesUpTo 10) 297 a).card) = 8 := by
  rw [← coarseTown_missing_card_eq_terminal_sum (knownPrimeScales_primeScalesUpTo 10),
    ← coarseTown_rightMissing_card_eq_terminal_sum (knownPrimeScales_primeScalesUpTo 10)]
  exact ⟨DkMathTest.LegendreRetained297Calibration.left_loss_decomposition_checked.2.1,
    DkMathTest.LegendreRetained297Calibration.right_loss_decomposition_checked.2.1⟩

theorem terminal_sums1031_checked :
    (∑ a ∈ coarseTownDeletionVertices (primeScalesUpTo 10) 1031,
      (coarseTownTerminalPrimesAt (primeScalesUpTo 10) 1031 a).card) = 48 ∧
    (∑ a ∈ coarseTownRightDeletionVertices (primeScalesUpTo 10) 1031,
      (coarseTownMinimumTerminalPrimesAt (primeScalesUpTo 10) 1031 a).card) = 53 := by
  rw [← coarseTown_missing_card_eq_terminal_sum (knownPrimeScales_primeScalesUpTo 10),
    ← coarseTown_rightMissing_card_eq_terminal_sum (knownPrimeScales_primeScalesUpTo 10)]
  exact ⟨DkMathTest.LegendreRetained1031Calibration.left_loss_decomposition_checked.2.1,
    DkMathTest.LegendreRetained1031Calibration.right_loss_decomposition_checked.2.1⟩

theorem smallest_weaker_budget_checked :
    squareOffsetPrimeSupport 2 2 = ({2} : Finset ℕ) ∧
    coarseTownTerminalPrimesAt (∅ : Finset ℕ) 2 2 = ∅ ∧
    coarseTownDeletionWitnessPrimes (∅ : Finset ℕ) 2 2 = ({2} : Finset ℕ) ∧
    2 ^ 2 ≤ 2 ^ 2 + 2 ∧ 2 ^ 2 + 2 < 2 ^ 3 := by
  have hs : squareOffsetPrimeSupport 2 2 = ({2} : Finset ℕ) := by rw [support_computation]; decide +kernel
  have hS : KnownPrimeScales (∅ : Finset ℕ) := by intro q hq; exact False.elim (Finset.notMem_empty q hq)
  have ha : 2 ∈ coarsePrimeWorldFullTown (∅ : Finset ℕ) 2 := by decide +kernel
  have ht : coarseTownTerminalPrimesAt (∅ : Finset ℕ) 2 2 = ∅ := by
    rw [terminal_computation hS ha,hs]
    decide +kernel
  have hc : coarseTownDeletionWitnessPrimes (∅ : Finset ℕ) 2 2 = ({2} : Finset ℕ) := by
    rw [continuing_computation hS ha,hs,ht]
    decide +kernel
  exact ⟨hs,ht,hc,by decide,by decide⟩

theorem one_base_no_exponent_bound : ∀ t : ℕ, 1 ^ (t + 1) ≤ (1 : ℕ) := by simp

theorem shared_support_not_valuation_one : 5 ^ 2 ∣ 7 ^ 2 + 1 := by decide +kernel

end DkMathTest.LegendreTerminalProductCalibration
