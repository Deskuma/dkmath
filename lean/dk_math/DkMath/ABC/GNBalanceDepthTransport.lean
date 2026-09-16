/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNBalanceDepthLayers
import DkMath.ABC.GNLegacyTailCountingBridge

#print "file: DkMath.ABC.GNBalanceDepthTransport"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# Finite depth transport for the GN balance ruler

This module separates the algebraic effect of an exact valuation successor
from finite Hensel transport of divisibility roots.  The latter is downward
transport plus injectivity under the existing simple-root hypotheses; no lift
existence or equality of successive cardinalities is asserted.
-/

namespace DkMath.ABC

open DkMath.CosmicFormulaBinom

/-! ## Level A: exact local-coordinate successor laws -/

/-- An exact one-step valuation increase adds one local `log q` mass unit. -/
theorem GNNonExceptionalLocalMass_eq_add_log_of_factorization_succ
    {p a a' b q : ℕ}
    (hstep : (GN p a' b).factorization q =
      (GN p a b).factorization q + 1) :
    GNNonExceptionalLocalMass p a' b q =
      GNNonExceptionalLocalMass p a b q + Real.log (q : ℝ) := by
  unfold GNNonExceptionalLocalMass
  rw [hstep, Nat.cast_add]
  ring

/-- An exact one-step valuation increase subtracts one local `log q` balance. -/
theorem GNNonExceptionalLocalBalance_eq_sub_log_of_factorization_succ
    {p a a' b q : ℕ}
    (hstep : (GN p a' b).factorization q =
      (GN p a b).factorization q + 1) :
    GNNonExceptionalLocalBalance p a' b q =
      GNNonExceptionalLocalBalance p a b q - Real.log (q : ℝ) := by
  unfold GNNonExceptionalLocalBalance
  rw [hstep, Nat.cast_add]
  ring

/-! ## Level B: canonical downward depth transport -/

/-- A canonical depth-`k+1` root reduces to a canonical depth-`k` root. -/
theorem GNDeepLiftResidues_succ_reduction_mem
    {p q b k r : ℕ}
    (hq : Nat.Prime q)
    (_hk : 0 < k)
    (hr : r ∈ GNDeepLiftResidues p q b (k + 1)) :
    r % q ^ k ∈ GNDeepLiftResidues p q b k := by
  have hr' := mem_GNDeepLiftResidues_iff.mp hr
  have hqpow : q ^ k ∣ q ^ (k + 1) := by
    rw [pow_succ]
    exact dvd_mul_right _ _
  have hzero : Nat.ModEq (q ^ k) (GN p r b) 0 :=
    Nat.modEq_zero_iff_dvd.mpr (hqpow.trans hr'.2)
  have hmod : Nat.ModEq (q ^ k)
      (GN p (r % q ^ k) b) (GN p r b) :=
    GN_modEq_left (Nat.mod_modEq r (q ^ k))
  apply mem_GNDeepLiftResidues_iff.mpr
  constructor
  · exact Nat.mod_lt _ (pow_pos hq.pos _)
  · exact Nat.modEq_zero_iff_dvd.mp (hmod.trans hzero)

/-! ## Level C: successor injectivity and finite cardinality -/

/--
Congruence uniqueness at depth `k+1` makes reduction modulo `q^k` injective
on canonical depth-`k+1` roots.
-/
theorem GNDeepLiftSuccessorReductionInjective_of_congruenceUnique
    {p q b k : ℕ}
    (_hq : Nat.Prime q)
    (hk : 0 < k)
    (hunique : GNDeepLiftCongruenceUnique p q b (k + 1)) :
    Set.InjOn (fun r => r % q ^ k)
      (GNDeepLiftResidues p q b (k + 1) : Set ℕ) := by
  intro r hr s hs hred
  have hr' := mem_GNDeepLiftResidues_iff.mp hr
  have hs' := mem_GNDeepLiftResidues_iff.mp hs
  have hqpow : q ∣ q ^ k := by
    obtain ⟨j, rfl⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    exact dvd_pow_self q (by omega)
  have hmodq : Nat.ModEq q r s := by
    change r % q = s % q
    change r % q ^ k = s % q ^ k at hred
    rw [← Nat.mod_mod_of_dvd r hqpow,
      ← Nat.mod_mod_of_dvd s hqpow, hred]
  have hmodqk := hunique hr'.2 hs'.2 hmodq
  exact hmodqk.eq_of_lt_of_lt hr'.1 hs'.1

/-- Simple-root hypotheses give injective successor reduction. -/
theorem GNDeepLiftSuccessorReductionInjective_of_simpleRoot
    {p q b k : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hqp : ¬ q ∣ p)
    (hqb : ¬ q ∣ b)
    (hk : 0 < k) :
    Set.InjOn (fun r => r % q ^ k)
      (GNDeepLiftResidues p q b (k + 1) : Set ℕ) :=
  GNDeepLiftSuccessorReductionInjective_of_congruenceUnique hq hk
    (GNDeepLiftCongruenceUnique_of_simpleRoot
      hp hq hqp hqb (by omega))

/-- Successor depth has no more canonical roots under congruence uniqueness. -/
theorem GNDeepLiftResidues_card_succ_le_of_congruenceUnique
    {p q b k : ℕ}
    (hq : Nat.Prime q)
    (hk : 0 < k)
    (hunique : GNDeepLiftCongruenceUnique p q b (k + 1)) :
    (GNDeepLiftResidues p q b (k + 1)).card ≤
      (GNDeepLiftResidues p q b k).card := by
  classical
  let S := GNDeepLiftResidues p q b (k + 1)
  let T := GNDeepLiftResidues p q b k
  let f := fun r : ℕ => r % q ^ k
  have hmap : S.image f ⊆ T := by
    intro r hr
    obtain ⟨a, haS, rfl⟩ := Finset.mem_image.mp hr
    exact GNDeepLiftResidues_succ_reduction_mem hq hk haS
  have hinj : Set.InjOn f (S : Set ℕ) := by
    exact GNDeepLiftSuccessorReductionInjective_of_congruenceUnique
      hq hk hunique
  calc
    S.card = (S.image f).card := by
      symm
      apply Finset.card_image_iff.mpr
      intro a ha a' ha' haa'
      exact hinj ha ha' haa'
    _ ≤ T.card := Finset.card_le_card hmap

/-- Under simple-root hypotheses, canonical root branches decrease with depth. -/
theorem GNDeepLiftResidues_card_succ_le_of_simpleRoot
    {p q b k : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hqp : ¬ q ∣ p)
    (hqb : ¬ q ∣ b)
    (hk : 0 < k) :
    (GNDeepLiftResidues p q b (k + 1)).card ≤
      (GNDeepLiftResidues p q b k).card := by
  apply GNDeepLiftResidues_card_succ_le_of_congruenceUnique hq hk
  exact GNDeepLiftCongruenceUnique_of_simpleRoot
    hp hq hqp hqb (by omega)

end DkMath.ABC
