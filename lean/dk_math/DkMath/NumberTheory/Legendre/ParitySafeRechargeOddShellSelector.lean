/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeRechargeDualBaseCapacity

#print "file: DkMath.NumberTheory.Legendre.ParitySafeRechargeOddShellSelector"

/-!
## ParitySafeRechargeOddShellSelector

PRIM-L053 refines the L052 dual-base capacity universe.  For a dual product
`c = b*t` over the anchor, a shell quotient can only be the first quotient
above `n^2/c` or its successor.  An odd third prime selects the unique odd
one of these two candidates.  The actual recharge third prime is therefore
an explicit arithmetic function of `(n,b,t)`, and the L052 over-anchor image
can be filtered by the selector's prime and shell conditions.

This is a finite upper-capacity refinement.  It does not estimate the
filtered universe asymptotically, create a smaller anchor, or prove a global
contradiction or Legendre's conjecture.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open DkMath.NumberTheory.Legendre.Internal
noncomputable section
local instance classicalDecidableOddShell (p : Prop) : Decidable p :=
  Classical.propDecidable p
open scoped BigOperators

/-! ### PRIM-L053.1: explicit odd shell selector -/

/-- The unique odd candidate among the two possible shell quotients. -/
def paritySafeRechargeOddShellQuotient
    (n b t : ℕ) : ℕ :=
  let k := n ^ 2 / (b * t) + 1
  if Odd k then k else k + 1

/-- The odd shell selector is odd whenever its dual product is positive. -/
theorem paritySafeRechargeOddShellQuotient_odd
    {n b t : ℕ}
    (_hbt : 0 < b * t) :
    Odd (paritySafeRechargeOddShellQuotient n b t) := by
  dsimp [paritySafeRechargeOddShellQuotient]
  by_cases hk : Odd (n ^ 2 / (b * t) + 1)
  · simp [hk]
  · have hkEven : Even (n ^ 2 / (b * t) + 1) :=
      Nat.not_odd_iff_even.mp hk
    simpa [hk] using hkEven.add_one

/-! ### PRIM-L053.2: at-most-two shell quotients -/

/-- A shell quotient is one of the first quotient or its successor. -/
theorem paritySafeRecharge_shellQuotient_eq_next_or_succ
    {n b t s : ℕ}
    (hover : n < b * t)
    (hshell :
      n ^ 2 < (b * t) * s ∧
      (b * t) * s ≤ n ^ 2 + 2 * n) :
    s = n ^ 2 / (b * t) + 1 ∨
      s = n ^ 2 / (b * t) + 2 := by
  have hc : 0 < b * t := by omega
  let c := b * t
  let k := n ^ 2 / c + 1
  have hdivle : c * (n ^ 2 / c) ≤ n ^ 2 := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (n ^ 2) c
  have hquot_lower : n ^ 2 / c < s := by
    by_contra hnot
    have hsle : s ≤ n ^ 2 / c := Nat.le_of_not_gt hnot
    have hmul : c * s ≤ c * (n ^ 2 / c) :=
      Nat.mul_le_mul_left c hsle
    have hlower : n ^ 2 < c * s := by
      simpa [c, Nat.mul_assoc] using hshell.1
    nlinarith [hlower, hdivle, hmul]
  have hk_le : k ≤ s := by
    dsimp [k]
    omega
  have hrem : n ^ 2 % c < c := Nat.mod_lt _ hc
  have hdecomp : c * (n ^ 2 / c) + n ^ 2 % c = n ^ 2 :=
    Nat.div_add_mod (n ^ 2) c
  have hnext : n ^ 2 < c * k := by
    dsimp [k]
    nlinarith
  have htwoc : 2 * n < 2 * c := by
    have htwo_pos : 0 < (2 : ℕ) := by omega
    simpa [c] using (Nat.mul_lt_mul_left htwo_pos).mpr hover
  have hupper : s ≤ k + 1 := by
    by_contra hnot
    have hks : k + 2 ≤ s := by omega
    have hmul : c * (k + 2) ≤ c * s :=
      Nat.mul_le_mul_left c hks
    have hupper' : c * s ≤ n ^ 2 + 2 * n := by
      simpa [c, Nat.mul_assoc] using hshell.2
    nlinarith [hnext, htwoc, hupper', hmul]
  dsimp [k, c] at hk_le hupper
  omega

/-! ### PRIM-L053.3: odd quotient uniqueness -/

/-- Oddness chooses the unique member of the two-element shell quotient pair. -/
theorem paritySafeRecharge_shellOddQuotient_eq_selector
    {n b t s : ℕ}
    (hover : n < b * t)
    (hshell :
      n ^ 2 < (b * t) * s ∧
      (b * t) * s ≤ n ^ 2 + 2 * n)
    (hsodd : Odd s) :
    s = paritySafeRechargeOddShellQuotient n b t := by
  rcases paritySafeRecharge_shellQuotient_eq_next_or_succ hover hshell with hsk | hsk
  · unfold paritySafeRechargeOddShellQuotient
    dsimp
    by_cases hk : Odd (n ^ 2 / (b * t) + 1)
    · simp [hk, hsk]
    · exact False.elim (hk (by simpa [hsk] using hsodd))
  · unfold paritySafeRechargeOddShellQuotient
    dsimp
    by_cases hk : Odd (n ^ 2 / (b * t) + 1)
    · have heven : Even (n ^ 2 / (b * t) + 1 + 1) := hk.add_one
      rcases heven with ⟨r, hr⟩
      rcases hsodd with ⟨u, hu⟩
      omega
    · simp [hk, hsk]

/-! ### PRIM-L053.4: actual recharge third prime -/

/-- The third prime of a recharge key is the odd shell selector. -/
theorem paritySafeRechargeSurvivingFarProductKey_thirdPrime_eq_oddShellQuotient
    {n p q s : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeRechargeSurvivingFarProductKeys n) :
    s = paritySafeRechargeOddShellQuotient n (p * q)
      (paritySafeFarProductWaveNextQuotient n (p, (q, s))) := by
  have hsurv := mem_paritySafeSurvivingFarProductKeys.mp
    (mem_paritySafeRechargeSurvivingFarProductKeys.mp hkey).1
  have hgate := mem_paritySafeTripleGateTriples.mp
    (Finset.mem_filter.mp hsurv.1).1
  have hsactive := hgate.2.2.1
  have hsprime := (mem_squareAnchorOddActivePrimes.mp hsactive).1
  have hsodd : Odd s := hsprime.odd_of_ne_two
    (mem_squareAnchorOddActivePrimes.mp hgate.2.2.1).2.2.2
  exact paritySafeRecharge_shellOddQuotient_eq_selector
    (paritySafeRechargeSurvivingFarProductKey_anchor_lt_pairProduct_mul_nextQuotient
      hkey)
    (paritySafeRechargeSurvivingFarProductKey_dualProduct_shell_packet hkey)
    hsodd

/-! ### PRIM-L053.5: prime-admissible dual-base universe -/

/-- Dual-base pairs whose odd selector is active, shell-valid, and far. -/
noncomputable def paritySafeRechargePrimeAdmissibleDualBasePairs
    (n : ℕ) : Finset (ℕ × ℕ) :=
  (paritySafeRechargeOverAnchorDualBasePairs n).filter
    (fun bt =>
      let s := paritySafeRechargeOddShellQuotient n bt.1 bt.2
      s ∈ squareAnchorOddActivePrimes n ∧
      n ^ 2 < (bt.1 * bt.2) * s ∧
      (bt.1 * bt.2) * s ≤ n ^ 2 + 2 * n ∧
      2 * n < bt.1 * s)

@[simp] theorem mem_paritySafeRechargePrimeAdmissibleDualBasePairs
    {n b t : ℕ} :
    (b, t) ∈ paritySafeRechargePrimeAdmissibleDualBasePairs n ↔
      (b, t) ∈ paritySafeRechargeOverAnchorDualBasePairs n ∧
      let s := paritySafeRechargeOddShellQuotient n b t
      s ∈ squareAnchorOddActivePrimes n ∧
      n ^ 2 < (b * t) * s ∧
      (b * t) * s ≤ n ^ 2 + 2 * n ∧
      2 * n < b * s := by
  simp [paritySafeRechargePrimeAdmissibleDualBasePairs, and_assoc]

/-- The actual dual-base image lands in the prime-admissible refinement. -/
theorem paritySafeRechargeDualBaseKey_mem_primeAdmissible
    {n : ℕ} {key : ℕ × (ℕ × ℕ)}
    (hkey : key ∈ paritySafeRechargeSurvivingFarProductKeys n) :
    paritySafeRechargeDualBaseKey n key ∈
      paritySafeRechargePrimeAdmissibleDualBasePairs n := by
  rcases key with ⟨p, q, s⟩
  have hsurv := mem_paritySafeSurvivingFarProductKeys.mp
    (mem_paritySafeRechargeSurvivingFarProductKeys.mp hkey).1
  have hgate := mem_paritySafeTripleGateTriples.mp
    (Finset.mem_filter.mp hsurv.1).1
  have hsactive := hgate.2.2.1
  have hsprime := (mem_squareAnchorOddActivePrimes.mp hsactive).1
  have hfar := (Finset.mem_filter.mp hsurv.1).2
  have hshell := paritySafeRechargeSurvivingFarProductKey_dualProduct_shell_packet hkey
  have hselector :=
    paritySafeRechargeSurvivingFarProductKey_thirdPrime_eq_oddShellQuotient hkey
  rw [paritySafeRechargeDualBaseKey]
  apply mem_paritySafeRechargePrimeAdmissibleDualBasePairs.mpr
  refine ⟨paritySafeRechargeDualBaseKey_mem_overAnchor hkey, ?_⟩
  rw [← hselector]
  refine ⟨hsactive, ?_, ?_, ?_⟩
  · simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hshell.1
  · simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hshell.2
  · simpa [paritySafeTripleProductModulus, Nat.mul_assoc, Nat.mul_left_comm,
      Nat.mul_comm] using hfar

/-! ### PRIM-L053.6: refined capacity -/

/-- The L052 image is contained in the prime-admissible dual-base universe. -/
theorem paritySafeRechargeDualBaseImage_subset_primeAdmissible
    (n : ℕ) :
    paritySafeRechargeDualBaseImage n ⊆
      paritySafeRechargePrimeAdmissibleDualBasePairs n := by
  intro bt hbt
  rcases Finset.mem_image.mp hbt with ⟨key, hkey, rfl⟩
  exact paritySafeRechargeDualBaseKey_mem_primeAdmissible hkey

/-- Recharge cardinality is bounded by the refined dual-base universe. -/
theorem paritySafeRechargeSurvivingFarProductKeys_card_le_primeAdmissibleDualBasePairs
    (n : ℕ) :
    (paritySafeRechargeSurvivingFarProductKeys n).card ≤
      (paritySafeRechargePrimeAdmissibleDualBasePairs n).card := by
  rw [← paritySafeRechargeDualBaseImage_card_eq_recharge]
  exact Finset.card_le_card
    (paritySafeRechargeDualBaseImage_subset_primeAdmissible n)

/-- The refined recharge capacity feeds the exact L050 far-residual split. -/
theorem paritySafeCanonicalFarResidual_card_le_terminal_add_primeAdmissibleDualBase
    (n : ℕ) :
    (paritySafeCanonicalFarResidualTripleIncidences n).card ≤
      (paritySafeTerminalSurvivingFarProductKeys n).card +
      (paritySafeRechargePrimeAdmissibleDualBasePairs n).card := by
  rw [paritySafeCanonicalFarResidual_card_eq_terminal_add_recharge]
  exact Nat.add_le_add_left
    (paritySafeRechargeSurvivingFarProductKeys_card_le_primeAdmissibleDualBasePairs n)
    _

/-! ### PRIM-L053.7: refinement relation -/

/-- The prime-admissible universe refines the L052 over-anchor universe. -/
theorem paritySafeRechargePrimeAdmissibleDualBasePairs_subset_overAnchor
    (n : ℕ) :
    paritySafeRechargePrimeAdmissibleDualBasePairs n ⊆
      paritySafeRechargeOverAnchorDualBasePairs n := by
  intro bt hbt
  exact (mem_paritySafeRechargePrimeAdmissibleDualBasePairs.mp hbt).1

/-- The refined universe has no more elements than the L052 universe. -/
theorem paritySafeRechargePrimeAdmissibleDualBasePairs_card_le_overAnchor
    (n : ℕ) :
    (paritySafeRechargePrimeAdmissibleDualBasePairs n).card ≤
      (paritySafeRechargeOverAnchorDualBasePairs n).card :=
  Finset.card_le_card (paritySafeRechargePrimeAdmissibleDualBasePairs_subset_overAnchor n)

/-! ### PRIM-L053.8: arithmetic false beams -/

/-- An over-anchor pair can have a composite odd shell selector. -/
theorem paritySafeRechargeOddShellSelector_composite_false_beam :
    62 < 33 * 3 ∧
      paritySafeRechargeOddShellQuotient 62 33 3 = 39 ∧
      62 ^ 2 < (33 * 3) * 39 ∧
      (33 * 3) * 39 ≤ 62 ^ 2 + 2 * 62 ∧
      ¬ Nat.Prime 39 := by
  norm_num [paritySafeRechargeOddShellQuotient]

end
end DkMath.NumberTheory.Legendre
