/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeRechargeOddShellSelector

#print "file: DkMath.NumberTheory.Legendre.ParitySafeRechargeExactDualBase"

/-!
## ParitySafeRechargeExactDualBase

PRIM-L054 sharpens the L053 prime-admissible upper universe to an exact
finite description of the surviving recharge image.  The missing data are
an ordered active-prime factorization of `b` and the canonical-minimum
roughness condition on `t`.  The third prime is already the L053 odd-shell
selector, so these data reconstruct a recharge key.

The reverse construction is restricted to the recharge coordinate and does
not create a generic semiprime factorization API, a smaller anchor, or an
analytic counting result.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open DkMath.NumberTheory.Legendre.Internal
noncomputable section
local instance classicalDecidableExactDualBase (p : Prop) : Decidable p :=
  Classical.propDecidable p
open scoped BigOperators

/-! ### PRIM-L054.1: exact ordered-pair witness -/

/-- The ordered-prime and roughness witness carried by an exact coordinate. -/
def ParitySafeRechargeExactPairWitness
    (n b t p q : ℕ) : Prop :=
  p ∈ paritySafeTripleGatePrimes n ∧
  q ∈ squareAnchorOddActivePrimes n ∧
  p < q ∧
  p * q = b ∧
  q < paritySafeRechargeOddShellQuotient n b t ∧
  ∀ a ∈ squareAnchorOddActivePrimes n,
    a < p → ¬ a ∣ t

/-! ### PRIM-L054.2: exact dual-base Finset -/

/-- Dual-base pairs carrying an ordered active-prime and roughness witness. -/
noncomputable def paritySafeRechargeExactDualBasePairs
    (n : ℕ) : Finset (ℕ × ℕ) :=
  (paritySafeRechargePrimeAdmissibleDualBasePairs n).filter
    (fun bt =>
      ∃ p q, ParitySafeRechargeExactPairWitness n bt.1 bt.2 p q)

@[simp] theorem mem_paritySafeRechargeExactDualBasePairs
    {n b t : ℕ} :
    (b, t) ∈ paritySafeRechargeExactDualBasePairs n ↔
      (b, t) ∈ paritySafeRechargePrimeAdmissibleDualBasePairs n ∧
      ∃ p q, ParitySafeRechargeExactPairWitness n b t p q := by
  simp [paritySafeRechargeExactDualBasePairs]

/-- The exact dual-base universe refines the L053 prime-admissible universe. -/
theorem paritySafeRechargeExactDualBasePairs_subset_primeAdmissible
    (n : ℕ) :
    paritySafeRechargeExactDualBasePairs n ⊆
      paritySafeRechargePrimeAdmissibleDualBasePairs n := by
  intro bt hbt
  exact (mem_paritySafeRechargeExactDualBasePairs.mp hbt).1

/-! ### PRIM-L054.3: shell quotient recovery -/

private theorem paritySafeRecharge_eq_div_add_one_of_mul_in_shell
    {N m t : ℕ}
    (hm : 0 < m)
    (hlo : N < m * t)
    (hhi : m * t < N + m) :
    t = N / m + 1 := by
  have hdecomp : m * (N / m) + N % m = N := Nat.div_add_mod N m
  have hrem : N % m < m := Nat.mod_lt N hm
  have hmul_lo : m * (N / m) < m * t := by
    exact lt_of_le_of_lt (by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self N m) hlo
  have hquot_lo : N / m < t := (Nat.mul_lt_mul_left hm).mp hmul_lo
  have hmul_hi : m * t < m * (N / m + 2) := by
    nlinarith
  have hquot_hi : t < N / m + 2 := (Nat.mul_lt_mul_left hm).mp hmul_hi
  omega

private theorem paritySafeRecharge_nextQuotient_eq_of_far_shell
    {n p q s t : ℕ}
    (hfar : (p, (q, s)) ∈ paritySafeTripleGateFarTriples n)
    (hshell :
      n ^ 2 < (p * q * s) * t ∧
      (p * q * s) * t ≤ n ^ 2 + 2 * n) :
    paritySafeFarProductWaveNextQuotient n (p, (q, s)) = t := by
  have hgate := mem_paritySafeTripleGateTriples.mp
    (Finset.mem_filter.mp hfar).1
  rcases hgate with ⟨hp, hq, hs, hpq, hqs⟩
  have hmpos : 0 < p * q * s := by
    exact Nat.mul_pos
      (Nat.mul_pos
        (mem_squareAnchorOddActivePrimes.mp
          (mem_paritySafeTripleGatePrimes.mp hp).1).1.pos
        (mem_squareAnchorOddActivePrimes.mp hq).1.pos)
      (mem_squareAnchorOddActivePrimes.mp hs).1.pos
  have hfarwidth : 2 * n < p * q * s := (Finset.mem_filter.mp hfar).2
  have hhi : p * q * s * t < n ^ 2 + p * q * s := by
    have hlt : n ^ 2 + 2 * n < n ^ 2 + p * q * s := by omega
    exact lt_of_le_of_lt hshell.2 hlt
  unfold paritySafeFarProductWaveNextQuotient
  rw [paritySafeTripleProductModulus]
  exact (paritySafeRecharge_eq_div_add_one_of_mul_in_shell hmpos hshell.1 hhi).symm

/-! ### PRIM-L054.4: actual recharge image lands in the exact universe -/

/-- Every surviving recharge coordinate carries an exact pair witness. -/
theorem paritySafeRechargeDualBaseKey_mem_exact
    {n : ℕ} {key : ℕ × (ℕ × ℕ)}
    (hkey : key ∈ paritySafeRechargeSurvivingFarProductKeys n) :
    paritySafeRechargeDualBaseKey n key ∈
      paritySafeRechargeExactDualBasePairs n := by
  rcases key with ⟨p, q, s⟩
  have hrecharge := mem_paritySafeRechargeSurvivingFarProductKeys.mp hkey
  have hsurv := mem_paritySafeSurvivingFarProductKeys.mp hrecharge.1
  have hgate := mem_paritySafeTripleGateTriples.mp
    (Finset.mem_filter.mp hsurv.1).1
  rcases hgate with ⟨hp, hq, hs, hpq, hqs⟩
  have hselector :=
    paritySafeRechargeSurvivingFarProductKey_thirdPrime_eq_oddShellQuotient hkey
  have hrough := hsurv.2.2.2
  rw [paritySafeRechargeDualBaseKey]
  apply mem_paritySafeRechargeExactDualBasePairs.mpr
  refine ⟨paritySafeRechargeDualBaseKey_mem_primeAdmissible hkey, p, q, ?_⟩
  refine ⟨hp, hq, hpq, rfl, ?_, ?_⟩
  · rw [← hselector]
    exact hqs
  · exact hrough

/-- The L053 dual-base image is contained in the exact witness universe. -/
theorem paritySafeRechargeDualBaseImage_subset_exact
    (n : ℕ) :
    paritySafeRechargeDualBaseImage n ⊆
      paritySafeRechargeExactDualBasePairs n := by
  intro bt hbt
  rcases Finset.mem_image.mp hbt with ⟨key, hkey, rfl⟩
  exact paritySafeRechargeDualBaseKey_mem_exact hkey

/-! ### PRIM-L054.5: exact pair to recharge reverse reconstruction -/

theorem paritySafeRechargeExactDualBasePairs_exists_recharge_key
    {n b t : ℕ}
    (hbt : (b, t) ∈ paritySafeRechargeExactDualBasePairs n) :
    ∃ key ∈ paritySafeRechargeSurvivingFarProductKeys n,
      paritySafeRechargeDualBaseKey n key = (b, t) := by
  have hexact := mem_paritySafeRechargeExactDualBasePairs.mp hbt
  rcases hexact with ⟨hprime, p, q, hp, hq, hpq, hprod, hqs, hrough⟩
  let s := paritySafeRechargeOddShellQuotient n b t
  have hprime' := mem_paritySafeRechargePrimeAdmissibleDualBasePairs.mp hprime
  rcases hprime' with ⟨hover, hsactive, hslower, hsupper, hfar⟩
  have htrip : (p, (q, s)) ∈ paritySafeTripleGateTriples n := by
    apply mem_paritySafeTripleGateTriples.mpr
    exact ⟨hp, hq, hsactive, hpq, by simpa [s] using hqs⟩
  have hfar' : (p, (q, s)) ∈ paritySafeTripleGateFarTriples n := by
    apply Finset.mem_filter.mpr
    refine ⟨htrip, ?_⟩
    simpa [s, hprod, paritySafeTripleProductModulus,
      Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hfar
  have hquot : paritySafeFarProductWaveNextQuotient n (p, (q, s)) = t := by
    apply paritySafeRecharge_nextQuotient_eq_of_far_shell hfar'
    constructor
    · simpa [s, hprod, paritySafeTripleProductModulus,
        Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hslower
    · simpa [s, hprod, paritySafeTripleProductModulus,
        Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hsupper
  have hbase := (mem_paritySafeRechargeOverAnchorDualBasePairs.mp hover)
  have htbounds := mem_paritySafeFarCofactorBaseOffsets.mp hbase.2.1
  have hfit : ParitySafeFarProductKeyFitsShell n (p, (q, s)) := by
    unfold ParitySafeFarProductKeyFitsShell
    change p * q * s * paritySafeFarProductWaveNextQuotient n (p, (q, s)) ≤
      n ^ 2 + 2 * n
    rw [hquot, hprod]
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hsupper
  have hsurv : (p, (q, s)) ∈ paritySafeSurvivingFarProductKeys n := by
    apply mem_paritySafeSurvivingFarProductKeys.mpr
    refine ⟨hfar', hfit, ?_, ?_⟩
    · rw [hquot]
      exact htbounds.2.2
    intro a ha hap
    rw [hquot]
    exact hrough a ha hap
  have htgt : 1 < t := by
    have hble : b ≤ n :=
      (mem_paritySafeFarCofactorBaseOffsets.mp hbase.1).2.1
    by_contra hnot
    have htle : t ≤ 1 := by omega
    have hmul : b * t ≤ b := by
      simpa using Nat.mul_le_mul_left b htle
    omega
  have hrecharge : (p, (q, s)) ∈
      paritySafeRechargeSurvivingFarProductKeys n :=
    mem_paritySafeRechargeSurvivingFarProductKeys.mpr ⟨hsurv, by simpa [hquot] using htgt⟩
  refine ⟨(p, (q, s)), hrecharge, ?_⟩
  apply Prod.ext
  · change p * q = b
    exact hprod
  · change paritySafeFarProductWaveNextQuotient n (p, (q, s)) = t
    exact hquot

/-! ### PRIM-L054.6: exact image equality and cardinality -/

/-- Exact dual-base membership is equivalent to originating from recharge. -/
theorem mem_paritySafeRechargeExactDualBasePairs_iff_exists_recharge_key
    {n b t : ℕ} :
    (b, t) ∈ paritySafeRechargeExactDualBasePairs n ↔
      ∃ key ∈ paritySafeRechargeSurvivingFarProductKeys n,
        paritySafeRechargeDualBaseKey n key = (b, t) := by
  constructor
  · exact paritySafeRechargeExactDualBasePairs_exists_recharge_key
  · rintro ⟨key, hkey, hcoord⟩
    have hmem := paritySafeRechargeDualBaseKey_mem_exact hkey
    rw [hcoord] at hmem
    exact hmem

/-- The L053 image is exactly the exact recharge dual-base universe. -/
theorem paritySafeRechargeDualBaseImage_eq_exactDualBasePairs
    (n : ℕ) :
    paritySafeRechargeDualBaseImage n =
      paritySafeRechargeExactDualBasePairs n := by
  ext bt
  constructor
  · intro hbt
    rcases Finset.mem_image.mp hbt with ⟨key, hkey, rfl⟩
    exact mem_paritySafeRechargeExactDualBasePairs_iff_exists_recharge_key.mpr
      ⟨key, hkey, rfl⟩
  · intro hbt
    rcases mem_paritySafeRechargeExactDualBasePairs_iff_exists_recharge_key.mp hbt with
      ⟨key, hkey, hcoord⟩
    have hcoord' : paritySafeRechargeDualBaseKey n key = bt := by
      simpa using hcoord
    exact Finset.mem_image.mpr ⟨key, hkey, hcoord'⟩

/-- Recharge cardinality equals the exact dual-base cardinality. -/
theorem paritySafeRechargeSurvivingFarProductKeys_card_eq_exactDualBasePairs
    (n : ℕ) :
    (paritySafeRechargeSurvivingFarProductKeys n).card =
      (paritySafeRechargeExactDualBasePairs n).card := by
  calc
    (paritySafeRechargeSurvivingFarProductKeys n).card =
        (paritySafeRechargeDualBaseImage n).card :=
      (paritySafeRechargeDualBaseImage_card_eq_recharge n).symm
    _ = (paritySafeRechargeExactDualBasePairs n).card := by
      rw [paritySafeRechargeDualBaseImage_eq_exactDualBasePairs]

/-- The far residual has an exact terminal plus exact-recharge decomposition. -/
theorem paritySafeCanonicalFarResidual_card_eq_terminal_add_exactDualBase
    (n : ℕ) :
    (paritySafeCanonicalFarResidualTripleIncidences n).card =
      (paritySafeTerminalSurvivingFarProductKeys n).card +
      (paritySafeRechargeExactDualBasePairs n).card := by
  rw [paritySafeCanonicalFarResidual_card_eq_terminal_add_recharge]
  rw [paritySafeRechargeSurvivingFarProductKeys_card_eq_exactDualBasePairs]

/-! ### PRIM-L054.7: arithmetic boundary witness -/

/-- A prime-admissible-looking numerical selector need not have a prime-pair
factorization witness. -/
theorem paritySafeRechargeExactDualBase_pairWitness_false_beam :
    paritySafeRechargeOddShellQuotient 8 5 3 = 5 ∧
      ¬ ∃ p q : ℕ,
        Nat.Prime p ∧ Nat.Prime q ∧ p < q ∧ p * q = 5 := by
  constructor
  · norm_num [paritySafeRechargeOddShellQuotient]
  · rintro ⟨p, q, hp, hq, hpq, hprod⟩
    have hp2 := hp.two_le
    have hq2 := hq.two_le
    nlinarith

end
end DkMath.NumberTheory.Legendre
