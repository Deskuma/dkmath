/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNJointPressureOddPrime
import DkMath.ABC.GNHighLift

#print "file: DkMath.ABC.GNDepthPressure"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# Finite depth layers and the support--multiplicity pincer

This module rewrites non-exceptional GN valuation excess as a finite stack of
prime-support layers.  It then records the exact finite dichotomy behind the
support-heavy / multiplicity-heavy attack:

* either every local exponent is at most a chosen threshold, so excess is
  bounded by the first support layer;
* or one fresh non-exceptional prime survives to the next depth.

The second branch is only a witness packet.  No global rarity or exclusion of
deep lifts is asserted here.
-/

namespace DkMath.ABC

open DkMath.CosmicFormulaBinom

/-- Non-exceptional GN primes whose factorization exponent reaches depth `k`. -/
def GNNonExceptionalDepthSupport
    (p a b k : ℕ) : Finset ℕ :=
  (GNNonExceptionalSupport p a b).filter
    (fun q => k ≤ (GN p a b).factorization q)

/-- Logarithmic mass of one non-exceptional GN depth layer. -/
noncomputable def GNNonExceptionalDepthMass
    (p a b k : ℕ) : ℝ :=
  ∑ q ∈ GNNonExceptionalDepthSupport p a b k,
    Real.log (q : ℝ)

/-- Logarithmic mass of the first non-exceptional GN support layer. -/
noncomputable def GNNonExceptionalSupportLogMass
    (p a b : ℕ) : ℝ :=
  ∑ q ∈ GNNonExceptionalSupport p a b,
    Real.log (q : ℝ)

theorem mem_GNNonExceptionalDepthSupport_iff
    {p a b k q : ℕ} :
    q ∈ GNNonExceptionalDepthSupport p a b k ↔
      q ∈ GNNonExceptionalSupport p a b ∧
        k ≤ (GN p a b).factorization q := by
  simp [GNNonExceptionalDepthSupport]

/--
The contribution of one support prime is the sum of one copy of `log q` at
each higher depth `2, ..., v_q`.
-/
theorem factorization_pred_mul_log_eq_sum_depths
    {m q : ℕ}
    (hq : q ∈ m.factorization.support) :
    (((m.factorization q - 1 : ℕ) : ℝ) * Real.log (q : ℝ)) =
      ∑ _k ∈ Finset.Icc 2 (m.factorization q),
        Real.log (q : ℝ) := by
  have hq_one : 1 ≤ m.factorization q :=
    one_le_factorization_of_mem_support hq
  have hcard :
      (Finset.Icc 2 (m.factorization q)).card =
        m.factorization q - 1 := by
    rw [Nat.card_Icc]
    omega
  rw [Finset.sum_const, hcard]
  simp [nsmul_eq_mul]

/-- Prime-first finite layer-cake decomposition of non-exceptional excess. -/
theorem GNNonExceptionalValuationExcess_eq_sum_prime_depths
    (p a b : ℕ) :
    GNNonExceptionalValuationExcess p a b =
      ∑ q ∈ GNNonExceptionalSupport p a b,
        ∑ _k ∈ Finset.Icc 2 ((GN p a b).factorization q),
          Real.log (q : ℝ) := by
  classical
  unfold GNNonExceptionalValuationExcess
  change
    (∑ q ∈ GNNonExceptionalSupport p a b,
      ((((GN p a b).factorization q - 1 : ℕ) : ℝ) *
        Real.log (q : ℝ))) =
      ∑ q ∈ GNNonExceptionalSupport p a b,
        ∑ _k ∈ Finset.Icc 2 ((GN p a b).factorization q),
          Real.log (q : ℝ)
  apply Finset.sum_congr rfl
  intro q hq
  exact factorization_pred_mul_log_eq_sum_depths
    (Finset.mem_filter.mp hq).1

/--
Depth-first finite layer-cake decomposition of non-exceptional excess.

The ambient range is finite and intrinsic: every exponent in the
factorization of `GN p a b` is strictly smaller than `GN p a b`.
-/
theorem GNNonExceptionalValuationExcess_eq_sum_depthMass
    (p a b : ℕ) :
    GNNonExceptionalValuationExcess p a b =
      ∑ k ∈ (Finset.range (GN p a b)).filter (fun k => 2 ≤ k),
        GNNonExceptionalDepthMass p a b k := by
  classical
  have hIcc (q : ℕ) (hq : q ∈ GNNonExceptionalSupport p a b) :
      Finset.Icc 2 ((GN p a b).factorization q) =
        (Finset.range (GN p a b)).filter
          (fun k => 2 ≤ k ∧ k ≤ (GN p a b).factorization q) := by
    have hGN : GN p a b ≠ 0 :=
      (mem_support_factorization_iff.mp
        (Finset.mem_filter.mp hq).1).1
    ext k
    simp only [Finset.mem_Icc, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro hk
      exact
        ⟨lt_of_le_of_lt hk.2
          (Nat.factorization_lt q hGN), hk⟩
    · intro hk
      exact hk.2
  calc
    GNNonExceptionalValuationExcess p a b =
        ∑ q ∈ GNNonExceptionalSupport p a b,
          ∑ k ∈ Finset.range (GN p a b),
            if 2 ≤ k ∧ k ≤ (GN p a b).factorization q then
              Real.log (q : ℝ)
            else 0 := by
              rw [GNNonExceptionalValuationExcess_eq_sum_prime_depths]
              apply Finset.sum_congr rfl
              intro q hq
              rw [← Finset.sum_filter]
              apply Finset.sum_congr (hIcc q hq)
              intro k hk
              rfl
    _ = ∑ k ∈ Finset.range (GN p a b),
          ∑ q ∈ GNNonExceptionalSupport p a b,
            if 2 ≤ k ∧ k ≤ (GN p a b).factorization q then
              Real.log (q : ℝ)
            else 0 := Finset.sum_comm
    _ = ∑ k ∈ Finset.range (GN p a b),
          if 2 ≤ k then GNNonExceptionalDepthMass p a b k else 0 := by
            apply Finset.sum_congr rfl
            intro k hk
            by_cases hkTwo : 2 ≤ k
            · rw [ite_eq_left hkTwo]
              simp only [hkTwo, true_and]
              unfold GNNonExceptionalDepthMass
              rw [← Finset.sum_filter]
              rfl
            · rw [ite_eq_right hkTwo]
              simp only [hkTwo, false_and, ↓reduceIte, Finset.sum_const_zero]
    _ = ∑ k ∈ (Finset.range (GN p a b)).filter (fun k => 2 ≤ k),
          GNNonExceptionalDepthMass p a b k := by
            rw [Finset.sum_filter]

/-- The first-layer log mass is exactly the log of the support product. -/
theorem GNNonExceptionalSupportLogMass_eq_log_product
    (p a b : ℕ) :
    GNNonExceptionalSupportLogMass p a b =
      Real.log (GNNonExceptionalSupportProduct p a b : ℝ) := by
  classical
  unfold GNNonExceptionalSupportLogMass
  have hpos :
      ∀ q ∈ GNNonExceptionalSupport p a b, 0 < (q : ℝ) := by
    intro q hq
    exact_mod_cast
      Nat.Prime.pos
        (mem_support_factorization_iff.mp
          (Finset.mem_filter.mp hq).1).2.1
  simpa [GNNonExceptionalSupportProduct] using
    DkMath.NumberTheory.PrimitiveSet.real_sum_log_eq_log_prod_of_pos
      (GNNonExceptionalSupport p a b) (fun q : ℕ => (q : ℝ)) hpos

/--
If every non-exceptional support exponent is at most `K`, the valuation excess
is at most `(K - 1)` copies of the first support layer.
-/
theorem GNNonExceptionalValuationExcess_le_pred_mul_supportLogMass_of_cap
    {p a b K : ℕ}
    (hcap :
      ∀ q ∈ GNNonExceptionalSupport p a b,
        (GN p a b).factorization q ≤ K) :
    GNNonExceptionalValuationExcess p a b ≤
      (((K - 1 : ℕ) : ℝ) *
        GNNonExceptionalSupportLogMass p a b) := by
  classical
  unfold GNNonExceptionalValuationExcess
  change
    (∑ q ∈ GNNonExceptionalSupport p a b,
      ((((GN p a b).factorization q - 1 : ℕ) : ℝ) *
        Real.log (q : ℝ))) ≤
      (((K - 1 : ℕ) : ℝ) *
        GNNonExceptionalSupportLogMass p a b)
  calc
    (∑ q ∈ GNNonExceptionalSupport p a b,
      ((((GN p a b).factorization q - 1 : ℕ) : ℝ) *
        Real.log (q : ℝ)))
        ≤
      ∑ q ∈ GNNonExceptionalSupport p a b,
        (((K - 1 : ℕ) : ℝ) * Real.log (q : ℝ)) := by
          apply Finset.sum_le_sum
          intro q hq
          have hsub :
              (GN p a b).factorization q - 1 ≤ K - 1 :=
            Nat.sub_le_sub_right (hcap q hq) 1
          have hlog : 0 ≤ Real.log (q : ℝ) := by
            apply Real.log_nonneg
            exact_mod_cast
              (mem_support_factorization_iff.mp
                (Finset.mem_filter.mp hq).1).2.1.one_le
          exact mul_le_mul_of_nonneg_right
            (by exact_mod_cast hsub) hlog
    _ = (((K - 1 : ℕ) : ℝ) *
        GNNonExceptionalSupportLogMass p a b) := by
          simp only [GNNonExceptionalSupportLogMass, Finset.mul_sum]

/--
Finite weighted pincer: either excess is controlled by `K - 1` support layers,
or a non-exceptional prime reaches factorization depth `K + 1`.
-/
theorem GNNonExceptionalValuationExcess_le_or_exists_deep
    (p a b K : ℕ) :
    GNNonExceptionalValuationExcess p a b ≤
        (((K - 1 : ℕ) : ℝ) *
          GNNonExceptionalSupportLogMass p a b) ∨
      ∃ q ∈ GNNonExceptionalSupport p a b,
        K + 1 ≤ (GN p a b).factorization q := by
  classical
  by_cases hcap :
      ∀ q ∈ GNNonExceptionalSupport p a b,
        (GN p a b).factorization q ≤ K
  · exact Or.inl
      (GNNonExceptionalValuationExcess_le_pred_mul_supportLogMass_of_cap hcap)
  · right
    push Not at hcap
    obtain ⟨q, hq, hqK⟩ := hcap
    exact ⟨q, hq, by omega⟩

/-- Product-log form of the finite weighted pincer. -/
theorem GNNonExceptionalValuationExcess_le_log_product_or_exists_deep
    (p a b K : ℕ) :
    GNNonExceptionalValuationExcess p a b ≤
        (((K - 1 : ℕ) : ℝ) *
          Real.log (GNNonExceptionalSupportProduct p a b : ℝ)) ∨
      ∃ q ∈ GNNonExceptionalSupport p a b,
        K + 1 ≤ (GN p a b).factorization q := by
  rw [← GNNonExceptionalSupportLogMass_eq_log_product]
  exact GNNonExceptionalValuationExcess_le_or_exists_deep p a b K

/--
The full deterministic packet carried by a deep non-exceptional support prime.

This structure deliberately records a witness rather than claiming that such a
witness is rare or impossible.
-/
structure GNNonExceptionalDeepPrimePacket
    (T : Triple) (p K q : ℕ) : Prop where
  mem_support :
    q ∈ GNNonExceptionalSupport p T.a T.b
  prime : Nat.Prime q
  not_dvd_exp : ¬ q ∣ p
  gn_ne_zero : GN p T.a T.b ≠ 0
  dvd_GN : q ∣ GN p T.a T.b
  depth :
    K + 1 ≤ (GN p T.a T.b).factorization q
  pow_dvd_GN :
    q ^ (K + 1) ∣ GN p T.a T.b
  pow_dvd_powerDiff :
    q ^ (K + 1) ∣ T.c ^ p - T.b ^ p
  pow_dvd_lift_a :
    q ^ (K + 1) ∣ (T.gnPowerLift p).a
  not_dvd_a : ¬ q ∣ T.a
  not_dvd_b : ¬ q ∣ T.b
  not_dvd_c : ¬ q ∣ T.c
  not_dvd_abc : ¬ q ∣ T.a * T.b * T.c
  padic_GN_depth :
    K + 1 ≤ padicValNat q (GN p T.a T.b)
  padic_powerDiff_eq_GN :
    padicValNat q (T.c ^ p - T.b ^ p) =
      padicValNat q (GN p T.a T.b)
  padic_powerDiff_depth :
    K + 1 ≤ padicValNat q (T.c ^ p - T.b ^ p)

/-- Build the deep-prime packet from support membership and factorization depth. -/
theorem Triple.GNNonExceptionalDeepPrimePacket_of_mem
    (T : Triple) {p K q : ℕ}
    (hpTwo : 2 ≤ p)
    (ha : 0 < T.a) (hb : 0 < T.b)
    (hq : q ∈ GNNonExceptionalSupport p T.a T.b)
    (hdepth : K + 1 ≤ (GN p T.a T.b).factorization q) :
    GNNonExceptionalDeepPrimePacket T p K q := by
  have hqFilter := Finset.mem_filter.mp hq
  rcases mem_support_factorization_iff.mp hqFilter.1 with
    ⟨hGN, hqPrime, hqGN⟩
  have hfresh :=
    T.nonExceptionalSupport_fresh
      (Nat.one_le_of_lt hpTwo) ha hq
  have hpowGN :
      q ^ (K + 1) ∣ GN p T.a T.b :=
    (hqPrime.pow_dvd_iff_le_factorization hGN).2 hdepth
  have hpowDiff :
      q ^ (K + 1) ∣ T.c ^ p - T.b ^ p := by
    rw [T.powerDiff_eq_boundary_mul_GN p]
    exact dvd_mul_of_dvd_right hpowGN T.a
  have hpowLift :
      q ^ (K + 1) ∣ (T.gnPowerLift p).a := by
    rw [T.gnPowerLift_a]
    exact dvd_mul_of_dvd_right hpowGN T.a
  have hpadicGN :
      K + 1 ≤ padicValNat q (GN p T.a T.b) :=
    (DkMath.ABC.padicValNat_le_iff_dvd
      hqPrime hGN (K + 1)).2 hpowGN
  have hpadicEq :
      padicValNat q (T.c ^ p - T.b ^ p) =
        padicValNat q (GN p T.a T.b) :=
    T.padic_powerDiff_eq_GN_of_not_dvd_exp_of_dvd_GN
      hpTwo ha hb hqPrime hqFilter.2 hqGN
  refine
    { mem_support := hq
      prime := hqPrime
      not_dvd_exp := hqFilter.2
      gn_ne_zero := hGN
      dvd_GN := hqGN
      depth := hdepth
      pow_dvd_GN := hpowGN
      pow_dvd_powerDiff := hpowDiff
      pow_dvd_lift_a := hpowLift
      not_dvd_a := hfresh.2.2.1
      not_dvd_b := hfresh.2.2.2.1
      not_dvd_c := hfresh.2.2.2.2.1
      not_dvd_abc := hfresh.2.2.2.2.2
      padic_GN_depth := hpadicGN
      padic_powerDiff_eq_GN := hpadicEq
      padic_powerDiff_depth := ?_ }
  rw [hpadicEq]
  exact hpadicGN

/-- At threshold at least one, a deep packet is a non-exceptional high lift. -/
theorem GNNonExceptionalDeepPrimePacket.highLift
    {T : Triple} {p K q : ℕ}
    (H : GNNonExceptionalDeepPrimePacket T p K q)
    (hK : 1 ≤ K) :
    GNNonExceptionalHighLiftPrime q p T.a T.b := by
  refine ⟨⟨H.prime, ?_⟩, H.not_dvd_exp⟩
  have htwo : 2 ≤ (GN p T.a T.b).factorization q := by
    exact (Nat.succ_le_succ hK).trans H.depth
  exact (H.prime.pow_dvd_iff_le_factorization H.gn_ne_zero).2 htwo

/--
Packet-valued pincer for positive ABC triples: the multiplicity-heavy branch
returns all safe divisibility, freshness, and valuation data at once.
-/
theorem Triple.GNNonExceptionalValuationExcess_le_log_product_or_exists_deepPacket
    (T : Triple) {p K : ℕ}
    (hpTwo : 2 ≤ p)
    (ha : 0 < T.a) (hb : 0 < T.b) :
    GNNonExceptionalValuationExcess p T.a T.b ≤
        (((K - 1 : ℕ) : ℝ) *
          Real.log
            (GNNonExceptionalSupportProduct p T.a T.b : ℝ)) ∨
      ∃ q, GNNonExceptionalDeepPrimePacket T p K q := by
  rcases
      GNNonExceptionalValuationExcess_le_log_product_or_exists_deep
        p T.a T.b K with hlight | ⟨q, hq, hdepth⟩
  · exact Or.inl hlight
  · exact Or.inr
      ⟨q, T.GNNonExceptionalDeepPrimePacket_of_mem
        hpTwo ha hb hq hdepth⟩

end DkMath.ABC
