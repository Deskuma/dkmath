/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.GnomonDivisorCarry

#print "file: DkMath.NumberTheory.Legendre.GnomonCarryFiber"

/-! Same-base large-carry fibers have exact consecutive exponent geometry.
The cutoff-only upper budget remains conditional as a global prime provider. -/

namespace DkMath.NumberTheory.Legendre

open scoped BigOperators

/-- Exponents of old large power divisors of the indicated target. -/
def gnomonLargeCarryExponents (n p y : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.log p (n ^ 2))).filter (fun a => 2 * n < p ^ a ∧ p ^ a ∣ y)

/-- A divisible large grid necessarily crosses the square boundary. -/
theorem gnomonLarge_divisor_carry {n d y : ℕ} (hd : 2 * n < d)
    (hy : SquareCell n y) (hdy : d ∣ y) : gnomonLowDivisorCarryBit n d = 1 := by
  have ht : y ≤ n ^ 2 + 2 * n := by have h := hy.2; nlinarith
  have hm : y ∈ (Finset.Icc (n ^ 2 + 1) (n ^ 2 + 2 * n)).filter (d ∣ ·) :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by have h := hy.1; omega, ht⟩, hdy⟩
  have hpos := Finset.card_pos.mpr ⟨y, hm⟩
  rw [← gnomonShellMultipleCount_eq_card n d (by omega),
    gnomonShellMultipleCount_eq_div_add_carry (by omega), Nat.div_eq_of_lt hd] at hpos
  have hb := gnomonLowDivisorCarryBit_le_one n d
  omega

/-- This exponent fiber is exactly the routing fiber, not merely an admissible universe. -/
theorem mem_gnomonLargeCarryExponents_iff_route {n p y a : ℕ} (hn : 3 ≤ n)
    (hp : p.Prime) (hy : SquareCell n y) :
    a ∈ gnomonLargeCarryExponents n p y ↔
      p ^ a ∈ gnomonPascalLargeCarryEvents n ∧ gnomonNextShellMultiple n (p ^ a) = y := by
  constructor
  · intro ha
    have h := Finset.mem_filter.mp ha
    have hi := Finset.mem_Icc.mp h.1
    have hold := Nat.pow_le_of_le_log (by nlinarith : n ^ 2 ≠ 0) hi.2
    have hc := gnomonLarge_divisor_carry h.2.1 hy h.2.2
    have hpp := (isPrimePow_nat_iff (p ^ a)).mpr ⟨p, a, hp, hi.1, rfl⟩
    refine ⟨Finset.mem_filter.mpr ⟨mem_gnomonPascalLowCarryEvents.mpr
      ⟨(pow_pos hp.pos a), hold, hpp, hc⟩, h.2.1⟩, ?_⟩
    exact (gnomonNextShellMultiple_unique h.2.1 hc hy h.2.2).symm
  · rintro ⟨ha, he⟩
    have h := Finset.mem_filter.mp ha
    have hi := mem_gnomonPascalLowCarryEvents.mp h.1
    have ha0 : 1 ≤ a := by
      by_contra hnot
      have hz : a = 0 := by omega
      simp only [hz, pow_zero] at h
      omega
    have hdiv := (gnomonNextShellMultiple_packet h.2 hi.2.2.2).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨ha0, Nat.le_log_of_pow_le hp.one_lt hi.2.1⟩, h.2, he ▸ hdiv⟩

/-- The full fiber is a consecutive interval, cut off by both age and valuation. -/
theorem gnomonLargeCarryExponents_eq_Icc {n p y : ℕ} (hn : 3 ≤ n)
    (hp : p.Prime) (hy : SquareCell n y) :
    gnomonLargeCarryExponents n p y =
      Finset.Icc (Nat.log p (2 * n) + 1) (min (Nat.log p (n ^ 2)) (y.factorization p)) := by
  have hy0 : y ≠ 0 := by have h := hy.1; omega
  have hw0 : 2 * n ≠ 0 := by omega
  ext a
  simp only [gnomonLargeCarryExponents, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨ha, hu⟩, hd, hv⟩
    have hl := Nat.log_lt_of_lt_pow hw0 hd
    exact ⟨by omega, le_min hu ((hp.pow_dvd_iff_le_factorization hy0).mp hv)⟩
  · intro h
    exact ⟨⟨by omega, (le_min_iff.mp h.2).1⟩,
      Nat.lt_pow_of_log_lt hp.one_lt (by omega),
      (hp.pow_dvd_iff_le_factorization hy0).mpr (le_min_iff.mp h.2).2⟩

/-- Exact cardinal; the natural subtraction handles empty fibers. -/
theorem card_gnomonLargeCarryExponents {n p y : ℕ} (hn : 3 ≤ n)
    (hp : p.Prime) (hy : SquareCell n y) :
    (gnomonLargeCarryExponents n p y).card =
      min (Nat.log p (n ^ 2)) (y.factorization p) - Nat.log p (2 * n) := by
  rw [gnomonLargeCarryExponents_eq_Icc hn hp hy, Nat.card_Icc]
  omega

/-- A nontrivial width bound independent of the target's actual valuation height. -/
theorem card_gnomonLargeCarryExponents_le_cutoff {n p y : ℕ} (hn : 3 ≤ n)
    (hp : p.Prime) (hy : SquareCell n y) :
    (gnomonLargeCarryExponents n p y).card ≤ Nat.log p (n ^ 2) - Nat.log p (2 * n) := by
  rw [card_gnomonLargeCarryExponents hn hp hy]
  exact Nat.sub_le_sub_right (min_le_left _ _) _

/-- Bases above the width have only depth one; repeated-power compression cannot help them. -/
theorem gnomonLargeCarryExponents_large_base_subset {n p y : ℕ}
    (hn : 3 ≤ n) (hpw : 2 * n < p) : gnomonLargeCarryExponents n p y ⊆ {1} := by
  intro a ha
  have h := Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1
  have hu : Nat.log p (n ^ 2) < 2 :=
    Nat.log_lt_of_lt_pow (by nlinarith : n ^ 2 ≠ 0) (by nlinarith : n ^ 2 < p ^ 2)
  have he : a = 1 := by omega
  simpa only [Finset.mem_singleton] using he

/-- Every label in a same-base fiber contributes one base log, rather than log(label). -/
theorem gnomonLargeCarryExponents_weight {n p y : ℕ} (hn : 3 ≤ n)
    (hp : p.Prime) (hy : SquareCell n y) :
    (∑ a ∈ gnomonLargeCarryExponents n p y, ArithmeticFunction.vonMangoldt (p ^ a)) =
      ((min (Nat.log p (n ^ 2)) (y.factorization p) - Nat.log p (2 * n) : ℕ) : ℝ) *
        Real.log (p : ℝ) := by
  calc
    _ = ∑ _a ∈ gnomonLargeCarryExponents n p y, Real.log (p : ℝ) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact gnomonCarry_prime_pow_weight hp (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, card_gnomonLargeCarryExponents hn hp hy]

/-- Canonical prime-base/target pairs avoid choosing an inverse routing label. -/
def gnomonLargeCarryTargets (n : ℕ) : Finset (ℕ × ℕ) :=
  (gnomonPascalLargeCarryEvents n).image (fun d => (d.minFac, gnomonNextShellMultiple n d))

theorem gnomonLargeCarryTarget_packet {n p y : ℕ}
    (ht : (p, y) ∈ gnomonLargeCarryTargets n) : p.Prime ∧ SquareCell n y := by
  obtain ⟨d, hd, he⟩ := Finset.mem_image.mp ht
  have h := Finset.mem_filter.mp hd
  have hi := mem_gnomonPascalLowCarryEvents.mp h.1
  have hp := Nat.minFac_prime hi.2.2.1.ne_one
  have hy := (gnomonNextShellMultiple_packet h.2 hi.2.2.2).1
  have he1 : d.minFac = p := congrArg Prod.fst he
  have he2 : gnomonNextShellMultiple n d = y := congrArg Prod.snd he
  exact ⟨he1 ▸ hp, he2 ▸ hy⟩

/-- Same-target canonical pairs have the same base; label injection is not asserted. -/
theorem gnomonLargeCarryTargets_target_injective {n : ℕ} (hn : 3 ≤ n) :
    Set.InjOn (fun t : ℕ × ℕ => t.2) (gnomonLargeCarryTargets n) := by
  rintro ⟨p, y⟩ ht ⟨q, z⟩ hu htarget
  obtain ⟨d, hd, he⟩ := Finset.mem_image.mp ht
  obtain ⟨e, he', hf⟩ := Finset.mem_image.mp hu
  have hdl := Finset.mem_filter.mp hd
  have hel := Finset.mem_filter.mp he'
  have hdpp := (mem_gnomonPascalLowCarryEvents.mp hdl.1).2.2.1
  have hepp := (mem_gnomonPascalLowCarryEvents.mp hel.1).2.2.1
  have hdp := gnomonNextShellMultiple_packet hdl.2
    (mem_gnomonPascalLowCarryEvents.mp hdl.1).2.2.2
  have hep := gnomonNextShellMultiple_packet hel.2
    (mem_gnomonPascalLowCarryEvents.mp hel.1).2.2.2
  have hnext : gnomonNextShellMultiple n d = gnomonNextShellMultiple n e := by
    have h1 := congrArg Prod.snd he
    have h2 := congrArg Prod.snd hf
    exact h1.trans (htarget.trans h2.symm)
  have hpq := gnomonLarge_prime_power_divisors_same_base
    (a := d.factorization d.minFac) (b := e.factorization e.minFac) hn hdp.1
    (Nat.minFac_prime hdpp.ne_one) (Nat.minFac_prime hepp.ne_one)
    (by simpa only [hdpp.minFac_pow_factorization_eq] using hdl.2)
    (by simpa only [hepp.minFac_pow_factorization_eq] using hel.2)
    (by simpa only [hdpp.minFac_pow_factorization_eq] using hdp.2)
    (by simpa only [hepp.minFac_pow_factorization_eq] using (hnext.symm ▸ hep.2))
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.fst hf
  exact Prod.ext (h1.symm.trans (hpq.trans h2)) htarget

/-- Exact label/exponent weight reindexing inside one routing fiber. -/
theorem gnomonLargeCarry_label_fiber_weight {n p y : ℕ} (hn : 3 ≤ n)
    (hp : p.Prime) (hy : SquareCell n y) :
    (∑ d ∈ (gnomonPascalLargeCarryEvents n).filter
      (fun d => (d.minFac, gnomonNextShellMultiple n d) = (p, y)),
      ArithmeticFunction.vonMangoldt d) =
    (∑ a ∈ gnomonLargeCarryExponents n p y, ArithmeticFunction.vonMangoldt (p ^ a)) := by
  symm
  apply Finset.sum_bij (fun a _ => p ^ a)
  · intro a ha
    have hr := (mem_gnomonLargeCarryExponents_iff_route hn hp hy).mp ha
    have ha0 := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1
    exact Finset.mem_filter.mpr ⟨hr.1, Prod.ext (hp.pow_minFac (by omega)) hr.2⟩
  · intro a _ b _ hab; exact (Nat.pow_right_inj hp.one_lt).mp hab
  · intro d hd
    have he := (Finset.mem_filter.mp hd).2
    have hr := (Finset.mem_filter.mp hd).1
    have hpp := (mem_gnomonPascalLowCarryEvents.mp (Finset.mem_filter.mp hr).1).2.2.1
    have hbase : d.minFac = p := congrArg Prod.fst he
    have htarget : gnomonNextShellMultiple n d = y := congrArg Prod.snd he
    have hpow := hpp.minFac_pow_factorization_eq
    rw [hbase] at hpow
    refine ⟨d.factorization p, ?_, hpow⟩
    apply (mem_gnomonLargeCarryExponents_iff_route hn hp hy).mpr
    rw [hpow]
    exact ⟨hr, htarget⟩
  · intro a _; rfl

/-- The large mass groups exactly by its canonical same-base target fibers. -/
theorem gnomonPascalLargeCarryMass_eq_fibers {n : ℕ} (hn : 3 ≤ n) :
    gnomonPascalLargeCarryMass n =
      ∑ t ∈ gnomonLargeCarryTargets n,
        ((min (Nat.log t.1 (n ^ 2)) (t.2.factorization t.1) - Nat.log t.1 (2 * n) : ℕ) : ℝ) *
          Real.log (t.1 : ℝ) := by
  classical
  unfold gnomonPascalLargeCarryMass
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun d hd => Finset.mem_image_of_mem (fun d => (d.minFac, gnomonNextShellMultiple n d)) hd)]
  apply Finset.sum_congr rfl
  rintro ⟨p, y⟩ ht
  have h := gnomonLargeCarryTarget_packet ht
  rw [gnomonLargeCarry_label_fiber_weight hn h.1 h.2,
    gnomonLargeCarryExponents_weight hn h.1 h.2]

/-- Cutoff-only capacity of occupied same-base target fibers. -/
noncomputable def gnomonLargeCarryFiberBudget (n : ℕ) : ℝ :=
  ∑ t ∈ gnomonLargeCarryTargets n,
    ((Nat.log t.1 (n ^ 2) - Nat.log t.1 (2 * n) : ℕ) : ℝ) * Real.log (t.1 : ℝ)

/-- Universal finite fiber bound; it does not estimate the occupied-image weights. -/
theorem gnomonPascalLargeCarryMass_le_fiberBudget {n : ℕ} (hn : 3 ≤ n) :
    gnomonPascalLargeCarryMass n ≤ gnomonLargeCarryFiberBudget n := by
  rw [gnomonPascalLargeCarryMass_eq_fibers hn]
  apply Finset.sum_le_sum
  intro t ht
  have hp := (gnomonLargeCarryTarget_packet ht).1
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast Nat.sub_le_sub_right (min_le_left _ _) (Nat.log t.1 (2 * n)))
    (Real.log_nonneg (by exact_mod_cast hp.one_le))

/-- Insertion into the old ledger yields an upper envelope, not a strict saving. -/
theorem gnomonPascalOldLogBudget_le_fiber_envelope {n : ℕ} (hn : 3 ≤ n) :
    gnomonPascalOldLogBudget n ≤ gnomonPascalShellHigherPrimePowerMass n +
      gnomonPascalSmallCarryMass n + gnomonLargeCarryFiberBudget n := by
  rw [gnomonPascalOldLogBudget_eq_higher_add_lowCarryMass hn,
    gnomonPascalLowCarryMass_eq_small_add_large]
  have h := gnomonPascalLargeCarryMass_le_fiberBudget hn
  linarith

/-- The entire excess of the cutoff envelope is exactly its unused fiber capacity. -/
theorem gnomonPascalOldLogBudget_fiber_excess {n : ℕ} (hn : 3 ≤ n) :
    gnomonPascalShellHigherPrimePowerMass n + gnomonPascalSmallCarryMass n +
      gnomonLargeCarryFiberBudget n = gnomonPascalOldLogBudget n +
        (gnomonLargeCarryFiberBudget n - gnomonPascalLargeCarryMass n) := by
  rw [gnomonPascalOldLogBudget_eq_higher_add_lowCarryMass hn,
    gnomonPascalLowCarryMass_eq_small_add_large]
  ring

/-- The fiber envelope feeds the existing exact band-wise conditional consumer. -/
theorem exists_prime_squareCell_of_fiberBudget_lt {n : ℕ} (hn : 3 ≤ n)
    (hstrict : gnomonPascalSmallCarryMass n + gnomonLargeCarryFiberBudget n +
      shellHigherPrimePowerLogLogBudget n < Real.log (GnomonPascalCell n : ℝ)) :
    ∃ p, p.Prime ∧ SquareCell n p := by
  apply exists_prime_squareCell_of_logLogBudget_lt hn
  exact gnomonShellVM_margin_of_band_bounds hn le_rfl
    (gnomonPascalLargeCarryMass_le_fiberBudget hn) hstrict

end DkMath.NumberTheory.Legendre
