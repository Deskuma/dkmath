/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeRechargePairProduct

#print "file: DkMath.NumberTheory.Legendre.ParitySafeRechargeDualBaseCapacity"

/-!
## ParitySafeRechargeDualBaseCapacity

PRIM-L052 upgrades the L051 pair-product return to a two-coordinate finite
capacity statement.  A surviving recharge key is sent to
`(b,t) = (p*q,nextQuotient)`.  The shell places this product strictly above
the anchor; fixed `(b,t)` determines the third active prime by the shell
width, while unique factorization of the ordered prime pair recovers `p` and
`q`.

The resulting injection is restricted to recharge surviving keys.  It does
not mix terminal keys into the coordinate map, create a smaller anchor, or
prove a global contradiction or Legendre's conjecture.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open DkMath.NumberTheory.Legendre.Internal
noncomputable section
local instance classicalDecidableDualBase (p : Prop) : Decidable p :=
  Classical.propDecidable p
open scoped BigOperators

/-! ### PRIM-L052.1: dual product shell and over-anchor return -/

/-- The shell packet for the product of the pair-product and next quotient. -/
theorem paritySafeRechargeSurvivingFarProductKey_dualProduct_shell_packet
    {n p q s : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeRechargeSurvivingFarProductKeys n) :
    n ^ 2 <
        ((p * q) * paritySafeFarProductWaveNextQuotient n (p, (q, s))) * s ∧
      ((p * q) * paritySafeFarProductWaveNextQuotient n (p, (q, s))) * s ≤
        n ^ 2 + 2 * n := by
  have hrecharge := mem_paritySafeRechargeSurvivingFarProductKeys.mp hkey
  have hsurv := mem_paritySafeSurvivingFarProductKeys.mp hrecharge.1
  have hgate := hsurv.1
  have hwave := (mem_squareWaveOffsets_farKey_iff_eq_nextSeat hgate).mpr
    ⟨hsurv.2.1, rfl⟩
  have hcofactor := paritySafeFarProductWaveCofactor_nextSeat_eq_nextQuotient
    hgate hsurv.2.1
  have hpacket := paritySafeFarProductWaveCofactor_packet hgate hwave
  rcases hpacket with ⟨_, hfactor, _⟩
  rw [hcofactor] at hfactor
  have hoff := (mem_squareWaveOffsets.mp hwave).1
  dsimp [SquareOffset] at hoff
  constructor
  · calc
      n ^ 2 < n ^ 2 + paritySafeFarProductWaveNextSeat n (p, (q, s)) := by
        omega
      _ = (p * q * s) *
          paritySafeFarProductWaveNextQuotient n (p, (q, s)) := by
        exact hfactor.symm
      _ = ((p * q) * paritySafeFarProductWaveNextQuotient n (p, (q, s))) * s := by
        ring
  · have hfit := hsurv.2.1
    unfold ParitySafeFarProductKeyFitsShell at hfit
    simpa [paritySafeTripleProductModulus, Nat.mul_assoc, Nat.mul_left_comm,
      Nat.mul_comm] using hfit

/-- The dual product `b*t₀` strictly exceeds the original anchor. -/
theorem paritySafeRechargeSurvivingFarProductKey_anchor_lt_pairProduct_mul_nextQuotient
    {n p q s : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeRechargeSurvivingFarProductKeys n) :
    n < (p * q) * paritySafeFarProductWaveNextQuotient n (p, (q, s)) := by
  have hshell :=
    paritySafeRechargeSurvivingFarProductKey_dualProduct_shell_packet hkey
  have hrecharge := mem_paritySafeRechargeSurvivingFarProductKeys.mp hkey
  have hsurv := mem_paritySafeSurvivingFarProductKeys.mp hrecharge.1
  have hgate := mem_paritySafeTripleGateTriples.mp
    (Finset.mem_filter.mp hsurv.1).1
  have hsle := (mem_squareAnchorOddActivePrimes.mp hgate.2.2.1).2.1
  by_contra hnot
  have hbt : (p * q) *
      paritySafeFarProductWaveNextQuotient n (p, (q, s)) ≤ n :=
    Nat.le_of_not_gt hnot
  have hprod : ((p * q) *
      paritySafeFarProductWaveNextQuotient n (p, (q, s))) * s ≤ n * n := by
    exact Nat.mul_le_mul hbt hsle
  have hprod' : ((p * q) *
      paritySafeFarProductWaveNextQuotient n (p, (q, s))) * s ≤ n ^ 2 := by
    simpa [pow_two] using hprod
  nlinarith [hshell.1, hprod']

/-! ### PRIM-L052.2: fixed dual coordinate determines the third prime -/

/-- Equal `(b,t)` coordinates force the same third active prime. -/
theorem paritySafeRecharge_thirdPrime_eq_of_pairProduct_eq_of_nextQuotient_eq
    {n p₁ q₁ s₁ p₂ q₂ s₂ : ℕ}
    (h₁ : (p₁, (q₁, s₁)) ∈ paritySafeRechargeSurvivingFarProductKeys n)
    (h₂ : (p₂, (q₂, s₂)) ∈ paritySafeRechargeSurvivingFarProductKeys n)
    (hb : p₁ * q₁ = p₂ * q₂)
    (ht : paritySafeFarProductWaveNextQuotient n (p₁, (q₁, s₁)) =
      paritySafeFarProductWaveNextQuotient n (p₂, (q₂, s₂))) :
    s₁ = s₂ := by
  have hshell₁ :=
    paritySafeRechargeSurvivingFarProductKey_dualProduct_shell_packet h₁
  have hshell₂ :=
    paritySafeRechargeSurvivingFarProductKey_dualProduct_shell_packet h₂
  have hrecharge₁ := mem_paritySafeRechargeSurvivingFarProductKeys.mp h₁
  have hrecharge₂ := mem_paritySafeRechargeSurvivingFarProductKeys.mp h₂
  have hsurv₁ := mem_paritySafeSurvivingFarProductKeys.mp hrecharge₁.1
  have hsurv₂ := mem_paritySafeSurvivingFarProductKeys.mp hrecharge₂.1
  have hgate₁ := mem_paritySafeTripleGateTriples.mp
    (Finset.mem_filter.mp hsurv₁.1).1
  have hgate₂ := mem_paritySafeTripleGateTriples.mp
    (Finset.mem_filter.mp hsurv₂.1).1
  have hsprime₁ := (mem_squareAnchorOddActivePrimes.mp hgate₁.2.2.1).1
  have hsprime₂ := (mem_squareAnchorOddActivePrimes.mp hgate₂.2.2.1).1
  have hsodd₁ : Odd s₁ := hsprime₁.odd_of_ne_two
    (mem_squareAnchorOddActivePrimes.mp hgate₁.2.2.1).2.2.2
  have hsodd₂ : Odd s₂ := hsprime₂.odd_of_ne_two
    (mem_squareAnchorOddActivePrimes.mp hgate₂.2.2.1).2.2.2
  by_contra hne
  have hlt : s₁ < s₂ ∨ s₂ < s₁ := by omega
  rcases hlt with hlt | hlt
  · have hspacing : s₁ + 2 ≤ s₂ := by
      rcases hsodd₁ with ⟨k₁, hk₁⟩
      rcases hsodd₂ with ⟨k₂, hk₂⟩
      omega
    have hscale :
        ((p₁ * q₁) * paritySafeFarProductWaveNextQuotient n (p₁, (q₁, s₁))) *
            (s₁ + 2) ≤
          ((p₂ * q₂) * paritySafeFarProductWaveNextQuotient n (p₂, (q₂, s₂))) * s₂ := by
      rw [hb, ht]
      exact Nat.mul_le_mul_left _ hspacing
    nlinarith [hshell₁.1, hshell₁.2, hshell₂.2,
      paritySafeRechargeSurvivingFarProductKey_anchor_lt_pairProduct_mul_nextQuotient h₁,
      hscale]
  · have hspacing : s₂ + 2 ≤ s₁ := by
      rcases hsodd₁ with ⟨k₁, hk₁⟩
      rcases hsodd₂ with ⟨k₂, hk₂⟩
      omega
    have hscale :
        ((p₂ * q₂) * paritySafeFarProductWaveNextQuotient n (p₂, (q₂, s₂))) *
            (s₂ + 2) ≤
          ((p₁ * q₁) * paritySafeFarProductWaveNextQuotient n (p₁, (q₁, s₁))) * s₁ := by
      rw [hb, ht]
      exact Nat.mul_le_mul_left _ hspacing
    nlinarith [hshell₂.1, hshell₂.2, hshell₁.2,
      paritySafeRechargeSurvivingFarProductKey_anchor_lt_pairProduct_mul_nextQuotient h₂,
      hscale]

/-! ### PRIM-L052.3: ordered pair recovery -/

private theorem ordered_prime_pair_eq_of_mul_eq_dual_base
    {p₁ q₁ p₂ q₂ : ℕ}
    (hp₁ : Nat.Prime p₁) (_hq₁ : Nat.Prime q₁)
    (hp₂ : Nat.Prime p₂) (hq₂ : Nat.Prime q₂)
    (hlt₁ : p₁ < q₁) (hlt₂ : p₂ < q₂)
    (hmul : p₁ * q₁ = p₂ * q₂) :
    p₁ = p₂ ∧ q₁ = q₂ := by
  have hdiv : p₁ ∣ p₂ * q₂ := by
    rw [← hmul]
    exact dvd_mul_right p₁ q₁
  rcases (hp₁.dvd_mul).mp hdiv with hp_eq | hq_eq
  · have hp_eq' := ((Nat.dvd_prime hp₂).mp hp_eq).resolve_left hp₁.ne_one
    subst p₁
    have hq_eq' : q₁ = q₂ := Nat.mul_left_cancel hp₂.pos hmul
    exact ⟨rfl, hq_eq'⟩
  · have hq_eq' := ((Nat.dvd_prime hq₂).mp hq_eq).resolve_left hp₁.ne_one
    subst p₁
    have hcross : q₁ = p₂ := by
      apply Nat.mul_right_cancel hq₂.pos
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
    omega

/-- Equal pair-products recover the ordered first prime pair of recharge keys. -/
theorem paritySafeRecharge_firstPair_eq_of_pairProduct_eq
    {n p₁ q₁ s₁ p₂ q₂ s₂ : ℕ}
    (h₁ : (p₁, (q₁, s₁)) ∈ paritySafeRechargeSurvivingFarProductKeys n)
    (h₂ : (p₂, (q₂, s₂)) ∈ paritySafeRechargeSurvivingFarProductKeys n)
    (hb : p₁ * q₁ = p₂ * q₂) :
    p₁ = p₂ ∧ q₁ = q₂ := by
  have hsurv₁ :=
    mem_paritySafeSurvivingFarProductKeys.mp
      (mem_paritySafeRechargeSurvivingFarProductKeys.mp h₁).1
  have hsurv₂ :=
    mem_paritySafeSurvivingFarProductKeys.mp
      (mem_paritySafeRechargeSurvivingFarProductKeys.mp h₂).1
  have hgate₁ := mem_paritySafeTripleGateTriples.mp
    (Finset.mem_filter.mp hsurv₁.1).1
  have hgate₂ := mem_paritySafeTripleGateTriples.mp
    (Finset.mem_filter.mp hsurv₂.1).1
  have hp₁' := (mem_squareAnchorOddActivePrimes.mp
    (mem_paritySafeTripleGatePrimes.mp hgate₁.1).1).1
  have hq₁' := (mem_squareAnchorOddActivePrimes.mp hgate₁.2.1).1
  have hp₂' := (mem_squareAnchorOddActivePrimes.mp
    (mem_paritySafeTripleGatePrimes.mp hgate₂.1).1).1
  have hq₂' := (mem_squareAnchorOddActivePrimes.mp hgate₂.2.1).1
  exact ordered_prime_pair_eq_of_mul_eq_dual_base hp₁' hq₁' hp₂' hq₂'
    hgate₁.2.2.2.1 hgate₂.2.2.2.1 hb

/-! ### PRIM-L052.4: finite dual-base coordinate universe -/

/-- The same-anchor dual coordinate `(b,t)` of a recharge key. -/
def paritySafeRechargeDualBaseKey
    (n : ℕ) (key : ℕ × (ℕ × ℕ)) : ℕ × ℕ :=
  (key.1 * key.2.1, paritySafeFarProductWaveNextQuotient n key)

/-- Reduced-base pairs whose product is over the original anchor. -/
noncomputable def paritySafeRechargeOverAnchorDualBasePairs
    (n : ℕ) : Finset (ℕ × ℕ) :=
  ((paritySafeFarCofactorBaseOffsets n).product
    (paritySafeFarCofactorBaseOffsets n)).filter
      (fun bt => n < bt.1 * bt.2)

@[simp] theorem mem_paritySafeRechargeOverAnchorDualBasePairs
    {n b t : ℕ} :
    (b, t) ∈ paritySafeRechargeOverAnchorDualBasePairs n ↔
      b ∈ paritySafeFarCofactorBaseOffsets n ∧
      t ∈ paritySafeFarCofactorBaseOffsets n ∧ n < b * t := by
  simp [paritySafeRechargeOverAnchorDualBasePairs, and_assoc]

/-- Every recharge key returns to the over-anchor dual-base universe. -/
theorem paritySafeRechargeDualBaseKey_mem_overAnchor
    {n : ℕ} {key : ℕ × (ℕ × ℕ)}
    (hkey : key ∈ paritySafeRechargeSurvivingFarProductKeys n) :
    paritySafeRechargeDualBaseKey n key ∈
      paritySafeRechargeOverAnchorDualBasePairs n := by
  rcases key with ⟨p, q, s⟩
  rw [paritySafeRechargeDualBaseKey]
  apply mem_paritySafeRechargeOverAnchorDualBasePairs.mpr
  refine ⟨?_, ?_, ?_⟩
  · exact paritySafeRechargeSurvivingFarProductKey_firstPairProduct_mem_farCofactorBase hkey
  · exact paritySafeRechargeSurvivingFarProductKey_nextQuotient_mem_farCofactorBase hkey
  · exact paritySafeRechargeSurvivingFarProductKey_anchor_lt_pairProduct_mul_nextQuotient hkey

/-- The dual-base coordinate is injective on surviving recharge keys. -/
theorem paritySafeRechargeDualBaseKey_injectiveOn
    (n : ℕ) :
    Set.InjOn (paritySafeRechargeDualBaseKey n)
      (paritySafeRechargeSurvivingFarProductKeys n :
        Set (ℕ × (ℕ × ℕ))) := by
  intro key₁ h₁ key₂ h₂ hcoord
  rcases key₁ with ⟨p₁, q₁, s₁⟩
  rcases key₂ with ⟨p₂, q₂, s₂⟩
  change (p₁, (q₁, s₁)) ∈ paritySafeRechargeSurvivingFarProductKeys n at h₁
  change (p₂, (q₂, s₂)) ∈ paritySafeRechargeSurvivingFarProductKeys n at h₂
  have hb : p₁ * q₁ = p₂ * q₂ := by
    simpa [paritySafeRechargeDualBaseKey] using congrArg Prod.fst hcoord
  have ht : paritySafeFarProductWaveNextQuotient n (p₁, (q₁, s₁)) =
      paritySafeFarProductWaveNextQuotient n (p₂, (q₂, s₂)) := by
    simpa [paritySafeRechargeDualBaseKey] using congrArg Prod.snd hcoord
  have hpq := paritySafeRecharge_firstPair_eq_of_pairProduct_eq h₁ h₂ hb
  have hs := paritySafeRecharge_thirdPrime_eq_of_pairProduct_eq_of_nextQuotient_eq
    h₁ h₂ hb ht
  rcases hpq with ⟨rfl, rfl⟩
  rcases hs with rfl
  rfl

/-! ### PRIM-L052.5: image and finite capacity -/

/-- The finite image of surviving recharge keys under the dual coordinate. -/
noncomputable def paritySafeRechargeDualBaseImage (n : ℕ) :
    Finset (ℕ × ℕ) :=
  (paritySafeRechargeSurvivingFarProductKeys n).image
    (paritySafeRechargeDualBaseKey n)

/-- The dual-base image is contained in the over-anchor universe. -/
theorem paritySafeRechargeDualBaseImage_subset_overAnchor
    (n : ℕ) :
    paritySafeRechargeDualBaseImage n ⊆
      paritySafeRechargeOverAnchorDualBasePairs n := by
  intro bt hbt
  rcases Finset.mem_image.mp hbt with ⟨key, hkey, rfl⟩
  exact paritySafeRechargeDualBaseKey_mem_overAnchor hkey

/-- The dual-base image preserves the recharge cardinality. -/
theorem paritySafeRechargeDualBaseImage_card_eq_recharge
    (n : ℕ) :
    (paritySafeRechargeDualBaseImage n).card =
      (paritySafeRechargeSurvivingFarProductKeys n).card := by
  unfold paritySafeRechargeDualBaseImage
  apply Finset.card_image_of_injOn
  exact (paritySafeRechargeDualBaseKey_injectiveOn n)

/-- Recharge cardinality is bounded by the finite over-anchor dual-base world. -/
theorem paritySafeRechargeSurvivingFarProductKeys_card_le_overAnchorDualBasePairs
    (n : ℕ) :
    (paritySafeRechargeSurvivingFarProductKeys n).card ≤
      (paritySafeRechargeOverAnchorDualBasePairs n).card := by
  rw [← paritySafeRechargeDualBaseImage_card_eq_recharge]
  exact Finset.card_le_card
    (paritySafeRechargeDualBaseImage_subset_overAnchor n)

/-- The exact L050 split yields a far-residual capacity bound. -/
theorem paritySafeCanonicalFarResidual_card_le_terminal_add_overAnchorDualBase
    (n : ℕ) :
    (paritySafeCanonicalFarResidualTripleIncidences n).card ≤
      (paritySafeTerminalSurvivingFarProductKeys n).card +
      (paritySafeRechargeOverAnchorDualBasePairs n).card := by
  rw [paritySafeCanonicalFarResidual_card_eq_terminal_add_recharge]
  exact Nat.add_le_add_left
    (paritySafeRechargeSurvivingFarProductKeys_card_le_overAnchorDualBasePairs n)
    _

/-! ### PRIM-L052.6: arithmetic boundary witnesses -/

/-- Arithmetic witnesses showing that `b` or `t` alone does not determine a
key, while the pair `(b,t)` is the intended coordinate. -/
theorem paritySafeRechargeDualBase_arithmetic_boundary_witnesses :
    37 ^ 2 + 56 = 3 * 5 * 19 * 5 ∧
      37 ^ 2 + 26 = 3 * 5 * 31 * 3 ∧
      32 ^ 2 + 11 = 3 * 5 * 23 * 3 ∧
      32 ^ 2 + 47 = 3 * 7 * 17 * 3 := by
  norm_num

end
end DkMath.NumberTheory.Legendre
