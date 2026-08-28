/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeLowCostResidualSplit

#print "file: DkMath.NumberTheory.Legendre.ParitySafeNearFirstPrimeWaveCapacity"

/-!
## ParitySafeNearFirstPrimeWaveCapacity

PRIM-L063 refines the Near branch by its first prime.  The resulting ordered
pair fibers retain the exact finite product-wave occupancy, so the Near
residual is bounded by an explicit finite wave budget.  The final arithmetic
form records complete local periods together with `squareWaveCarry`.

This module is a finite fiber and incidence transport only.  It does not
claim Near elimination, wave occupancy at most one, analytic estimates,
fourth-direction counting, descent, or a Legendre/RH conclusion.
-/

open scoped BigOperators

namespace DkMath.NumberTheory.Legendre

/-! ### PRIM-L063.1: the Near first-prime gate -/

/-- Near first primes selected by the canonical cube bound. -/
noncomputable def paritySafeNearFirstPrimes (n : ℕ) : Finset ℕ :=
  (paritySafeTripleGatePrimes n).filter (fun p => p ^ 3 < 2 * n)

@[simp] theorem mem_paritySafeNearFirstPrimes {n p : ℕ} :
    p ∈ paritySafeNearFirstPrimes n ↔
      p ∈ paritySafeTripleGatePrimes n ∧ p ^ 3 < 2 * n := by
  simp [paritySafeNearFirstPrimes]

theorem paritySafeTripleGateNear_firstPrime_mem
    {n p q s : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeTripleGateNearTriples n) :
    p ∈ paritySafeNearFirstPrimes n := by
  apply mem_paritySafeNearFirstPrimes.mpr
  exact ⟨(mem_paritySafeTripleGateTriples.mp
    (Finset.mem_filter.mp hkey).1).1,
    paritySafeTripleGateNear_canonical_cube_lt_two_mul hkey⟩

/-! ### PRIM-L063.2: ordered pair fibers at the first prime -/

/-- Ordered active-prime pairs admitted by a fixed Near first prime. -/
noncomputable def paritySafeNearPrimePairsAtFirst
    (n p : ℕ) : Finset (ℕ × ℕ) :=
  ((squareAnchorOddActivePrimes n).product (squareAnchorOddActivePrimes n)).filter
    (fun qs => p < qs.1 ∧ qs.1 < qs.2 ∧ p * qs.1 * qs.2 ≤ 2 * n)

@[simp] theorem mem_paritySafeNearPrimePairsAtFirst
    {n p q s : ℕ} :
    (q, s) ∈ paritySafeNearPrimePairsAtFirst n p ↔
      q ∈ squareAnchorOddActivePrimes n ∧
      s ∈ squareAnchorOddActivePrimes n ∧
      p < q ∧ q < s ∧ p * q * s ≤ 2 * n := by
  simp [paritySafeNearPrimePairsAtFirst, and_assoc, and_left_comm]

@[simp] theorem mem_paritySafeTripleGateNearTriples_iff_firstPrime_pair
    {n p q s : ℕ} :
    (p, (q, s)) ∈ paritySafeTripleGateNearTriples n ↔
      p ∈ paritySafeNearFirstPrimes n ∧
      (q, s) ∈ paritySafeNearPrimePairsAtFirst n p := by
  constructor
  · intro hkey
    refine ⟨paritySafeTripleGateNear_firstPrime_mem hkey, ?_⟩
    have htriple := mem_paritySafeTripleGateTriples.mp
      (Finset.mem_filter.mp hkey).1
    have hnear := (Finset.mem_filter.mp hkey).2
    rcases htriple with ⟨_, hq, hs, hpq, hqs⟩
    exact mem_paritySafeNearPrimePairsAtFirst.mpr
      ⟨hq, hs, hpq, hqs, by simpa [paritySafeTripleProductModulus] using hnear⟩
  · rintro ⟨hp, hqs⟩
    have hp' := (mem_paritySafeNearFirstPrimes.mp hp).1
    have hqs' := mem_paritySafeNearPrimePairsAtFirst.mp hqs
    apply Finset.mem_filter.mpr
    have htriple : (p, (q, s)) ∈ paritySafeTripleGateTriples n :=
      mem_paritySafeTripleGateTriples.mpr
        ⟨hp', hqs'.1, hqs'.2.1, hqs'.2.2.1, hqs'.2.2.2.1⟩
    exact ⟨htriple, by
      simpa [paritySafeTripleProductModulus] using hqs'.2.2.2.2⟩

/-! ### PRIM-L063.3: exact first-prime fiber decomposition -/

/-- The Near key card is exactly the sum of its first-prime pair fibers. -/
theorem paritySafeTripleGateNearTriples_card_eq_sum_firstPrime_pairFibers
    (n : ℕ) :
    (paritySafeTripleGateNearTriples n).card =
      ∑ p ∈ paritySafeNearFirstPrimes n,
        (paritySafeNearPrimePairsAtFirst n p).card := by
  classical
  let s := paritySafeTripleGateNearTriples n
  let seats := paritySafeNearFirstPrimes n
  let g := fun key : ℕ × (ℕ × ℕ) => key.1
  have hfilter : s.filter (fun key => g key ∈ seats) = s := by
    apply Finset.filter_eq_self.mpr
    intro key hkey
    exact paritySafeTripleGateNear_firstPrime_mem hkey
  have hfiber := Finset.sum_card_fiberwise_eq_card_filter s seats g
  change s.card = ∑ p ∈ seats,
    (paritySafeNearPrimePairsAtFirst n p).card
  rw [← hfilter, hfiber.symm]
  apply Finset.sum_congr rfl
  intro p hp
  symm
  simpa only [Finset.card_eq_sum_ones] using
    (Finset.sum_bij (s := paritySafeNearPrimePairsAtFirst n p)
      (t := s.filter (fun key => g key = p))
      (fun qs hqs => (p, qs)) (by
        intro qs hqs
        apply Finset.mem_filter.mpr
        exact ⟨mem_paritySafeTripleGateNearTriples_iff_firstPrime_pair.mpr
          ⟨hp, hqs⟩, rfl⟩) (by
        intro qs₁ hqs₁ qs₂ hqs₂ hEq
        exact congrArg Prod.snd hEq) (by
        intro key hkey
        rcases key with ⟨p', qs⟩
        have hpEq : p' = p := (Finset.mem_filter.mp hkey).2
        subst p'
        exact ⟨qs, (mem_paritySafeTripleGateNearTriples_iff_firstPrime_pair.mp
          (Finset.mem_filter.mp hkey).1).2, rfl⟩) (by
        intro qs hqs
        simp))

/-! ### PRIM-L063.4: finite Near product-wave capacity -/

/-- The Near product-wave budget written over first-prime pair fibers. -/
noncomputable def paritySafeNearFirstPrimeWaveBudget (n : ℕ) : ℕ :=
  ∑ p ∈ paritySafeNearFirstPrimes n,
    ∑ qs ∈ paritySafeNearPrimePairsAtFirst n p,
      (squareWaveOffsets n (p * qs.1 * qs.2)).card

theorem paritySafeNearFirstPrimeWaveBudget_eq_nearTriple_sum
    (n : ℕ) :
    paritySafeNearFirstPrimeWaveBudget n =
      ∑ key ∈ paritySafeTripleGateNearTriples n,
        (squareWaveOffsets n
          (paritySafeTripleProductModulus key)).card := by
  classical
  unfold paritySafeNearFirstPrimeWaveBudget
  let s := paritySafeTripleGateNearTriples n
  let seats := paritySafeNearFirstPrimes n
  let g := fun key : ℕ × (ℕ × ℕ) => key.1
  have hfilter : s.filter (fun key => g key ∈ seats) = s := by
    apply Finset.filter_eq_self.mpr
    intro key hkey
    exact paritySafeTripleGateNear_firstPrime_mem hkey
  have hsum := Finset.sum_fiberwise_eq_sum_filter s seats g
    (fun key => (squareWaveOffsets n
      (paritySafeTripleProductModulus key)).card)
  rw [hfilter] at hsum
  change (∑ p ∈ seats,
      ∑ qs ∈ paritySafeNearPrimePairsAtFirst n p,
        (squareWaveOffsets n (p * qs.1 * qs.2)).card) =
    ∑ key ∈ s, (squareWaveOffsets n
      (paritySafeTripleProductModulus key)).card
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_bij (s := paritySafeNearPrimePairsAtFirst n p)
    (t := s.filter (fun key => g key = p)) (fun qs hqs => (p, qs))
  · intro qs hqs
    apply Finset.mem_filter.mpr
    exact ⟨mem_paritySafeTripleGateNearTriples_iff_firstPrime_pair.mpr
      ⟨hp, hqs⟩, rfl⟩
  · intro qs₁ hqs₁ qs₂ hqs₂ hEq
    exact congrArg Prod.snd hEq
  · intro key hkey
    rcases key with ⟨p', qs⟩
    have hpEq : p' = p := (Finset.mem_filter.mp hkey).2
    subst p'
    exact ⟨qs, (mem_paritySafeTripleGateNearTriples_iff_firstPrime_pair.mp
      (Finset.mem_filter.mp hkey).1).2, rfl⟩
  · intro qs hqs
    rfl

/-! ### PRIM-L063.5: actual Near incidences in the wave upper ledger -/

/-- Near product-wave incidences, retaining the key and its possible seats. -/
noncomputable def paritySafeNearFirstPrimeWaveUpperIncidences (n : ℕ) :
    Finset ((ℕ × (ℕ × ℕ)) × ℕ) :=
  ((paritySafeTripleGateNearTriples n).product (squareOffsets n)).filter
    (fun hit => hit.2 ∈ squareWaveOffsets n
      (paritySafeTripleProductModulus hit.1))

theorem paritySafeNearFirstPrimeWaveUpperIncidences_card_eq_budget (n : ℕ) :
    (paritySafeNearFirstPrimeWaveUpperIncidences n).card =
      paritySafeNearFirstPrimeWaveBudget n := by
  classical
  unfold paritySafeNearFirstPrimeWaveUpperIncidences
  rw [paritySafeNearFirstPrimeWaveBudget_eq_nearTriple_sum]
  calc
    (((paritySafeTripleGateNearTriples n).product (squareOffsets n)).filter
        (fun hit => hit.2 ∈ squareWaveOffsets n
          (paritySafeTripleProductModulus hit.1))).card =
        ∑ hit ∈ (paritySafeTripleGateNearTriples n).product (squareOffsets n),
          if hit.2 ∈ squareWaveOffsets n
              (paritySafeTripleProductModulus hit.1) then 1 else 0 := by simp
    _ = ∑ key ∈ paritySafeTripleGateNearTriples n,
          (squareWaveOffsets n (paritySafeTripleProductModulus key)).card := by
      calc
        _ = ∑ key ∈ paritySafeTripleGateNearTriples n,
            ∑ r ∈ squareOffsets n,
              if r ∈ squareWaveOffsets n
                  (paritySafeTripleProductModulus key) then 1 else 0 := by
          exact Finset.sum_product' (paritySafeTripleGateNearTriples n)
            (squareOffsets n) (fun key r => if r ∈ squareWaveOffsets n
              (paritySafeTripleProductModulus key) then 1 else 0)
        _ = _ := by
          apply Finset.sum_congr rfl
          intro key hkey
          rw [Finset.sum_boole]
          apply congrArg Finset.card
          ext r
          simp only [Finset.mem_filter]
          constructor
          · exact And.right
          · intro hr
            exact ⟨mem_squareOffsets.mpr (mem_squareWaveOffsets.mp hr).1, hr⟩
    _ = _ := rfl

theorem paritySafeCanonicalNearResidualTripleIncidences_card_le_nearFirstPrimeWaveBudget
    (n : ℕ) :
    (paritySafeCanonicalNearResidualTripleIncidences n).card ≤
      paritySafeNearFirstPrimeWaveBudget n := by
  classical
  let f : ℕ × (ℕ × ℕ) → ((ℕ × (ℕ × ℕ)) × ℕ) := fun triple =>
    ((paritySafeCanonicalSupportPrime n triple.1, triple.2), triple.1)
  have hinj : Set.InjOn f
      (paritySafeCanonicalNearResidualTripleIncidences n :
        Set (ℕ × (ℕ × ℕ))) := by
    intro a ha b hb hab
    have hr : a.1 = b.1 := congrArg Prod.snd hab
    have hqs : a.2 = b.2 := congrArg (fun z => z.1.2) hab
    exact Prod.ext hr hqs
  have hcard :
      (paritySafeCanonicalNearResidualTripleIncidences n).card =
        ((paritySafeCanonicalNearResidualTripleIncidences n).image f).card := by
    exact (Finset.card_image_of_injOn hinj).symm
  have hsubset :
      (paritySafeCanonicalNearResidualTripleIncidences n).image f ⊆
        paritySafeNearFirstPrimeWaveUpperIncidences n := by
    intro hit hhit
    rcases Finset.mem_image.mp hhit with ⟨triple, htriple, rfl⟩
    have hnear := mem_paritySafeCanonicalNearResidualTripleIncidences.mp htriple
    have hwave := paritySafeCanonicalResidualTripleIncidence_mem_productWave
      hnear.1
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨hnear.2,
      mem_squareOffsets.mpr (mem_squareWaveOffsets.mp hwave).1⟩, hwave⟩
  have hupper := Finset.card_le_card hsubset
  rw [← hcard] at hupper
  rw [paritySafeNearFirstPrimeWaveUpperIncidences_card_eq_budget] at hupper
  exact hupper

/-! ### PRIM-L063.6: exact local-period and carry arithmetic -/

/-- The Near wave budget is the exact quotient-plus-carry sum. -/
theorem paritySafeNearFirstPrimeWaveBudget_eq_div_add_carry
    (n : ℕ) :
    paritySafeNearFirstPrimeWaveBudget n =
      ∑ p ∈ paritySafeNearFirstPrimes n,
        ∑ qs ∈ paritySafeNearPrimePairsAtFirst n p,
          ((2 * n) / (p * qs.1 * qs.2) +
            squareWaveCarry n (p * qs.1 * qs.2)) := by
  unfold paritySafeNearFirstPrimeWaveBudget
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro qs hqs
  rw [card_squareWaveOffsets_eq_div_add_carry]
  have hactive := (mem_paritySafeNearPrimePairsAtFirst.mp hqs)
  have hp' := (mem_squareAnchorOddActivePrimes.mp
    (mem_paritySafeTripleGatePrimes.mp
      (mem_paritySafeNearFirstPrimes.mp hp).1).1).1.pos
  have hq' := (mem_squareAnchorOddActivePrimes.mp hactive.1).1.pos
  have hs' := (mem_squareAnchorOddActivePrimes.mp hactive.2.1).1.pos
  exact Nat.mul_pos (Nat.mul_pos hp' hq') hs'

/-! ### PRIM-L063.7: the LowCost upper-control consumer -/

/-- LowCost is controlled by Near waves, L018 depth, and raw Fourth. -/
theorem paritySafeLowCostResidualMass_le_nearWaveBudget_add_L018Depth_add_fourth
    (n : ℕ) :
    paritySafeLowCostResidualMass n ≤
      paritySafeNearFirstPrimeWaveBudget n +
      squareAnchorCoprimePrimeSquareDepthBudget n +
      (paritySafeRechargeExactFourthDirectionPairs n).card := by
  unfold paritySafeLowCostResidualMass
  have hnear :=
    paritySafeCanonicalNearResidualTripleIncidences_card_le_nearFirstPrimeWaveBudget n
  have hdepth := paritySafeRechargeExactDepthNonCollisionSeats_card_le_primeSquareDepthBudget n
  omega

end DkMath.NumberTheory.Legendre
