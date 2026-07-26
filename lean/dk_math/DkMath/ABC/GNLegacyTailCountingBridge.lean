/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNDepthPressure
import DkMath.ABC.SquareTailBasic
import DkMath.ABC.LayerCakeBasic

#print "file: DkMath.ABC.GNLegacyTailCountingBridge"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# Legacy tail and counting bridges for the non-exceptional GN channel

This module reconnects two earlier ABC proof vocabularies to the current
odd-prime joint-pressure campaign.

First, it packages the complete non-exceptional prime-power part of `GN` as a
natural number. Its radical is the current non-exceptional support product, and
its valuation excess is the current non-exceptional excess. Consequently the
old `piSqRad`/`twoTail` decomposition gives an exact two-layer representation
of that excess.

Second, it packages the old residue-class counting and finite layer-cake APIs.
A finite residue cover gives the desired interval-cardinality bound, while a
separate wrapper feeds GN p-adic depths into `exp_layer_cake`.

The module constructs the canonical Hensel residue cover and proves its
finite simple-root uniqueness in the non-exceptional `q ∤ p`, `q ∤ b`
channel.  It also composes those residue counts with a finite layer-cake to
obtain fixed-prime and finite-family average GN depth-mass bounds.  It does
not turn those average estimates into the pointwise
`ABCGNOddPrimeJointContract`.
-/

namespace DkMath.ABC

open DkMath.CosmicFormulaBinom

/--
The natural number carrying exactly the non-exceptional prime powers of `GN`.

Unlike `GNNonExceptionalSupportProduct`, this retains the full factorization
depth at every non-exceptional prime.
-/
noncomputable def GNNonExceptionalPart (p a b : ℕ) : ℕ :=
  (GNNonExceptionalSupport p a b).prod
    (fun q => q ^ (GN p a b).factorization q)

/-- Factorization of the packaged non-exceptional GN part. -/
theorem GNNonExceptionalPart_factorization
    (p a b r : ℕ) :
    (GNNonExceptionalPart p a b).factorization r =
      if r ∈ GNNonExceptionalSupport p a b then
        (GN p a b).factorization r
      else 0 := by
  classical
  let S := GNNonExceptionalSupport p a b
  let f := fun q => q ^ (GN p a b).factorization q
  have hprime :
      ∀ q ∈ S, Nat.Prime q := by
    intro q hq
    exact (mem_support_factorization_iff.mp
      (Finset.mem_filter.mp hq).1).2.1
  have hnonzero :
      ∀ q ∈ S, f q ≠ 0 := by
    intro q hq
    exact pow_ne_zero _ (hprime q hq).ne_zero
  have hfac :=
    congrArg (fun g : ℕ →₀ ℕ => g r)
      (Nat.factorization_prod hnonzero)
  have hfac' :
      (GNNonExceptionalPart p a b).factorization r =
        (∑ q ∈ S, (f q).factorization r) := by
    simpa only [GNNonExceptionalPart, S, f,
      Finsupp.coe_finset_sum, Finset.sum_apply] using hfac
  change
    (GNNonExceptionalPart p a b).factorization r =
      if r ∈ GNNonExceptionalSupport p a b then
        (GN p a b).factorization r
      else 0
  rw [hfac']
  simp only [f, Nat.factorization_pow, Finsupp.coe_smul,
    Pi.smul_apply, nsmul_eq_mul]
  by_cases hr : r ∈ S
  · rw [if_pos hr]
    calc
      ∑ q ∈ S,
          (GN p a b).factorization q * q.factorization r =
        (GN p a b).factorization r * r.factorization r := by
          apply Finset.sum_eq_single r
          · intro q hq hqr
            rw [(hprime q hq).factorization, Finsupp.single_apply]
            simp [hqr]
          · intro hrnot
            exact False.elim (hrnot hr)
      _ = (GN p a b).factorization r := by
          rw [(hprime r hr).factorization, Finsupp.single_eq_same]
          simp
  · rw [if_neg hr]
    apply Finset.sum_eq_zero
    intro q hq
    rw [(hprime q hq).factorization, Finsupp.single_apply]
    simp only [mul_eq_zero]
    right
    simp only [ite_eq_right_iff]
    intro hqr
    subst q
    exact False.elim (hr hq)

/-- The packaged non-exceptional GN part is always positive. -/
theorem GNNonExceptionalPart_pos (p a b : ℕ) :
    0 < GNNonExceptionalPart p a b := by
  classical
  unfold GNNonExceptionalPart
  exact Finset.prod_pos fun q hq =>
    pow_pos (mem_support_factorization_iff.mp
      (Finset.mem_filter.mp hq).1).2.1.pos _

/-- The packaged part has exactly the non-exceptional factorization support. -/
theorem GNNonExceptionalPart_factorization_support
    (p a b : ℕ) :
    (GNNonExceptionalPart p a b).factorization.support =
      GNNonExceptionalSupport p a b := by
  classical
  ext r
  rw [Finsupp.mem_support_iff,
    GNNonExceptionalPart_factorization]
  by_cases hr : r ∈ GNNonExceptionalSupport p a b
  · rw [if_pos hr]
    exact iff_of_true
      (Finsupp.mem_support_iff.mp
        (Finset.mem_filter.mp hr).1)
      hr
  · simp [hr]

/-- Its radical is the current non-exceptional support product. -/
theorem rad_GNNonExceptionalPart_eq_supportProduct
    (p a b : ℕ) :
    rad (GNNonExceptionalPart p a b) =
      GNNonExceptionalSupportProduct p a b := by
  unfold rad GNNonExceptionalSupportProduct
  rw [GNNonExceptionalPart_factorization_support]
  simp

/-- Its generic valuation excess is exactly the current non-exceptional excess. -/
theorem valuationExcess_GNNonExceptionalPart_eq
    (p a b : ℕ) :
    valuationExcess (GNNonExceptionalPart p a b) =
      GNNonExceptionalValuationExcess p a b := by
  classical
  unfold valuationExcess GNNonExceptionalValuationExcess
  rw [GNNonExceptionalPart_factorization_support]
  apply Finset.sum_congr rfl
  intro q hq
  rw [GNNonExceptionalPart_factorization, if_pos hq]

/--
The current non-exceptional valuation excess is the logarithm of the old
square-free tail quotient.
-/
theorem GNNonExceptionalValuationExcess_eq_log_sqTail
    (p a b : ℕ) :
    GNNonExceptionalValuationExcess p a b =
      Real.log (sqTail (GNNonExceptionalPart p a b) : ℝ) := by
  let N := GNNonExceptionalPart p a b
  have hN : N ≠ 0 := Nat.ne_of_gt (GNNonExceptionalPart_pos p a b)
  have hlog := log_eq_log_rad_add_valuationExcess hN
  have hdecomp := nat_eq_sqTail_mul_rad_real N hN
  have hsquare : (sqTail N : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (by
      rw [sqTail_eq_piSqRad_mul_twoTail N hN]
      exact Nat.mul_pos
        (Nat.lt_of_lt_of_le Nat.zero_lt_one (piSqRad_ge_one N))
        (by
          unfold twoTail
          exact Finset.prod_pos fun q hq => pow_pos
            (mem_support_factorization_iff.mp hq).2.1.pos _))
  have hrad : (rad N : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (rad_pos (Nat.pos_of_ne_zero hN))
  have hmul :
      Real.log (N : ℝ) =
        Real.log (sqTail N : ℝ) + Real.log (rad N : ℝ) := by
    rw [hdecomp, Real.log_mul hsquare hrad]
  rw [valuationExcess_GNNonExceptionalPart_eq] at hlog
  linarith

/--
Exact bridge from the current excess to the legacy second-layer and deep-tail
coordinates.
-/
theorem GNNonExceptionalValuationExcess_eq_log_piSqRad_add_log_twoTail
    (p a b : ℕ) :
    GNNonExceptionalValuationExcess p a b =
      Real.log (piSqRad (GNNonExceptionalPart p a b) : ℝ) +
        Real.log (twoTail (GNNonExceptionalPart p a b) : ℝ) := by
  let N := GNNonExceptionalPart p a b
  have hN : N ≠ 0 := Nat.ne_of_gt (GNNonExceptionalPart_pos p a b)
  have hsquare := sqTail_eq_piSqRad_mul_twoTail_real N hN
  have hpi : (piSqRad N : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt
      (Nat.lt_of_lt_of_le Nat.zero_lt_one (piSqRad_ge_one N))
  have htail : (twoTail N : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (by
      unfold twoTail
      exact Finset.prod_pos fun q hq => pow_pos
        (mem_support_factorization_iff.mp hq).2.1.pos _)
  rw [GNNonExceptionalValuationExcess_eq_log_sqTail,
    hsquare, Real.log_mul hpi htail]

/-- `GN` respects congruence in its left coordinate. -/
theorem GN_modEq_left
    {m p a r b : ℕ}
    (har : Nat.ModEq m a r) :
    Nat.ModEq m (GN p a b) (GN p r b) := by
  rw [GN_eq_sum, GN_eq_sum]
  apply Nat.ModEq.sum
  intro i hi
  exact
    ((Nat.ModEq.refl _).mul (har.pow i)).mul
      (Nat.ModEq.refl _)

/--
The canonical residue addresses of depth-`k` GN lifts.

Unlike an abstract cover, this set contains exactly the representatives in
`[0, q^k)` on which `q^k` divides `GN`.
-/
def GNDeepLiftResidues (p q b k : ℕ) : Finset ℕ :=
  (Finset.range (q ^ k)).filter
    (fun r => q ^ k ∣ GN p r b)

@[simp] theorem mem_GNDeepLiftResidues_iff
    {p q b k r : ℕ} :
    r ∈ GNDeepLiftResidues p q b k ↔
      r < q ^ k ∧ q ^ k ∣ GN p r b := by
  simp [GNDeepLiftResidues]

/--
`GN(p, X, b)` as a polynomial in the left coordinate.

The coefficient formula is the same canonical binomial-tail formula as
`GN_eq_sum`; in particular, for positive `p` this polynomial is monic and its
degree is bounded by `p - 1`.
-/
noncomputable def GNPolynomial
    (p b : ℕ) (R : Type*) [CommSemiring R] :
    Polynomial R :=
  ∑ i ∈ Finset.range p,
    Polynomial.C
      ((Nat.choose p (i + 1) *
        b ^ (p - (i + 1)) : ℕ) : R) *
      Polynomial.X ^ i

/-- The GN polynomial commutes with change of coefficient semiring. -/
theorem map_GNPolynomial
    {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (p b : ℕ) :
    (GNPolynomial p b R).map f =
      GNPolynomial p b S := by
  simp only [GNPolynomial, Polynomial.map_sum,
    Polynomial.map_mul, map_natCast,
    Polynomial.map_pow, Polynomial.map_X]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.map_natCast]

/-- Evaluation of `GNPolynomial` recovers the natural-number GN kernel. -/
theorem eval_GNPolynomial
    (p a b : ℕ) (R : Type*) [CommSemiring R] :
    Polynomial.eval (a : R) (GNPolynomial p b R) =
      (GN p a b : ℕ) := by
  rw [GN_eq_sum]
  simp only [GNPolynomial, Polynomial.eval_finset_sum,
    Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hip : i < p := Finset.mem_range.mp hi
  rw [show p - (i + 1) = p - 1 - i by omega]
  push_cast
  ring

/--
First-order Taylor expansion with an explicit quadratic remainder.

This is the local replacement for a stronger convenience lemma that is not
available in the Mathlib revision used by this project.
-/
theorem exists_eval_add_eq_eval_add_derivative_mul_add_sq
    {R : Type*} [CommRing R]
    (P : Polynomial R) (x y : R) :
    ∃ c : R,
      P.eval (x + y) =
        P.eval x + P.derivative.eval x * y + c * y ^ 2 := by
  let T :=
    P.taylor x -
      Polynomial.C (P.eval x) -
      Polynomial.C (P.derivative.eval x) * Polynomial.X
  have hXT : Polynomial.X ^ 2 ∣ T := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    interval_cases d <;> simp [T]
  obtain ⟨Q, hQ⟩ := hXT
  refine ⟨Q.eval y, ?_⟩
  have hEval := congrArg (Polynomial.eval y) hQ
  simp [T] at hEval
  rw [add_comm x y, ← Polynomial.taylor_eval]
  linear_combination hEval

/-- `GNPolynomial` is the generic semiring-valued GN kernel at `X`. -/
theorem GNPolynomial_eq_GN
    (p b : ℕ) (R : Type*) [CommSemiring R] :
    GNPolynomial p b R =
      GN p (Polynomial.X : Polynomial R)
        (Polynomial.C (b : R)) := by
  rw [GN_eq_sum]
  simp only [GNPolynomial]
  apply Finset.sum_congr rfl
  intro i hi
  have hip : i < p := Finset.mem_range.mp hi
  rw [show p - (i + 1) = p - 1 - i by omega]
  push_cast
  simp [Polynomial.C_pow, Polynomial.C_mul]
  ring

/-- The GN polynomial is monic whenever the exponent is positive. -/
theorem GNPolynomial_monic
    {p b : ℕ} (hp : 0 < p)
    (R : Type*) [CommSemiring R] :
    (GNPolynomial p b R).Monic := by
  apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one
    (p - 1)
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    exact (Polynomial.natDegree_C_mul_X_pow_le _ i).trans
      (by simpa using
        Nat.le_pred_of_lt (Finset.mem_range.mp hi))
  · rw [GNPolynomial, Polynomial.finset_sum_coeff]
    rw [Finset.sum_eq_single (p - 1)]
    · have hpred : p - 1 + 1 = p := by omega
      simp [hpred]
    · intro i hi hne
      change
        (Polynomial.C
          ((Nat.choose p (i + 1) *
            b ^ (p - (i + 1)) : ℕ) : R) *
            Polynomial.X ^ i).coeff (p - 1) = 0
      rw [Polynomial.coeff_C_mul_X_pow, if_neg]
      exact Ne.symm hne
    · intro hnot
      exact
        (hnot (Finset.mem_range.mpr (by omega))).elim

/-- The degree of the GN polynomial is at most `p - 1`. -/
theorem GNPolynomial_natDegree_le
    {p b : ℕ}
    (R : Type*) [CommSemiring R] :
    (GNPolynomial p b R).natDegree ≤ p - 1 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  exact (Polynomial.natDegree_C_mul_X_pow_le _ i).trans
    (by simpa using
      Nat.le_pred_of_lt (Finset.mem_range.mp hi))

/--
Every GN root modulo `q` is simple when `q` divides neither the prime exponent
nor the boundary coordinate.

This is the derivative input for the remaining Hensel uniqueness theorem.
-/
theorem eval_derivative_GNPolynomial_ne_zero
    {p q b : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hqp : ¬ q ∣ p)
    (hqb : ¬ q ∣ b)
    {r : ZMod q}
    (hroot :
      Polynomial.eval r
        (GNPolynomial p b (ZMod q)) = 0) :
    Polynomial.eval r
        (Polynomial.derivative
          (GNPolynomial p b (ZMod q))) ≠ 0 := by
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  have hp0 : (p : ZMod q) ≠ 0 := by
    intro h
    exact hqp ((ZMod.natCast_eq_zero_iff p q).mp h)
  have hb0 : (b : ZMod q) ≠ 0 := by
    intro h
    exact hqb ((ZMod.natCast_eq_zero_iff b q).mp h)
  have hrb0 : r + (b : ZMod q) ≠ 0 := by
    intro hrb
    have hcos :=
      cosmic_id_csr' p
        (Polynomial.X : Polynomial (ZMod q))
        (Polynomial.C (b : ZMod q))
    rw [← GNPolynomial_eq_GN] at hcos
    have heval := congrArg (Polynomial.eval r) hcos
    simp [Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_X, hroot, hrb] at heval
    have hbp : (b : ZMod q) ^ p = 0 := by
      simpa [hp.ne_zero] using heval.symm
    exact hb0 (eq_zero_of_pow_eq_zero hbp)
  have hcos :=
    cosmic_id_csr' p
      (Polynomial.X : Polynomial (ZMod q))
      (Polynomial.C (b : ZMod q))
  rw [← GNPolynomial_eq_GN] at hcos
  have hderiv := congrArg Polynomial.derivative hcos
  have heval := congrArg (Polynomial.eval r) hderiv
  intro hzero
  have hrhs :
      (p : ZMod q) *
          (r + (b : ZMod q)) ^ (p - 1) ≠ 0 :=
    mul_ne_zero hp0 (pow_ne_zero _ hrb0)
  apply hrhs
  simpa [Polynomial.derivative_add,
    Polynomial.derivative_mul,
    Polynomial.derivative_pow,
    Polynomial.derivative_X,
    Polynomial.derivative_C,
    Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, hroot, hzero,
    Nat.cast_ofNat] using heval

/--
The canonical GN roots modulo a prime `q` number at most `p - 1`.

This is the base layer proposed in the memo.  It follows directly from the
monic degree-`p - 1` polynomial `GNPolynomial`, without an affine change of
variables or the extra assumptions `q ∤ p` and `q ∤ b`.
-/
theorem GNDeepLiftResidues_card_base_le
    {p q b : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q) :
    (GNDeepLiftResidues p q b 1).card ≤ p - 1 := by
  classical
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  let S := GNDeepLiftResidues p q b 1
  let f := fun r : ℕ => (r : ZMod q)
  let P := GNPolynomial p b (ZMod q)
  have hmonic : P.Monic :=
    GNPolynomial_monic hp.pos (ZMod q)
  have hinj : Set.InjOn f (S : Set ℕ) := by
    intro x hx y hy hxy
    have hxlt : x < q := by
      have := (mem_GNDeepLiftResidues_iff.mp hx).1
      simpa using this
    have hylt : y < q := by
      have := (mem_GNDeepLiftResidues_iff.mp hy).1
      simpa using this
    have := congrArg ZMod.val hxy
    simpa [f, ZMod.val_natCast,
      Nat.mod_eq_of_lt hxlt,
      Nat.mod_eq_of_lt hylt] using this
  have hroots : (S.image f).val ⊆ P.roots := by
    intro x hx
    have hx' : x ∈ S.image f := by simpa using hx
    obtain ⟨r, hrS, rfl⟩ := Finset.mem_image.mp hx'
    have hrGN :=
      (mem_GNDeepLiftResidues_iff.mp hrS).2
    have hcast :
        ((GN p r b : ℕ) : ZMod q) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      simpa using hrGN
    rw [Polynomial.mem_roots hmonic.ne_zero]
    change
      Polynomial.eval (r : ZMod q)
        (GNPolynomial p b (ZMod q)) = 0
    rw [eval_GNPolynomial]
    exact hcast
  calc
    S.card = (S.image f).card :=
      (Finset.card_image_iff.mpr hinj).symm
    _ ≤ P.natDegree :=
      Polynomial.card_le_degree_of_subset_roots hroots
    _ ≤ p - 1 :=
      GNPolynomial_natDegree_le (ZMod q)

/--
A finite set of residue addresses covering every deep GN lift at fixed
`p`, `q`, `b`, and depth `k`.

The Hensel/cyclotomic argument proving that the canonical cover has size at
most `p - 1` is deliberately a separate arithmetic obligation.
-/
def GNDeepLiftResidueCover
    (p q b k : ℕ) (R : Finset ℕ) : Prop :=
  ∀ a, q ^ k ∣ GN p a b →
    ∃ r ∈ R, Nat.ModEq (q ^ k) a r

/-- The canonical depth-`k` residue set covers every depth-`k` GN lift. -/
theorem GNDeepLiftResidues_cover
    {p q b k : ℕ}
    (hq : Nat.Prime q) :
    GNDeepLiftResidueCover p q b k
      (GNDeepLiftResidues p q b k) := by
  intro a ha
  let m := q ^ k
  have hm : 0 < m := pow_pos hq.pos _
  let r := a % m
  have hra : Nat.ModEq m r a := Nat.mod_modEq a m
  have hGNmod : Nat.ModEq m (GN p r b) (GN p a b) :=
    GN_modEq_left hra
  have hGNzero : Nat.ModEq m (GN p a b) 0 :=
    Nat.modEq_zero_iff_dvd.mpr ha
  have hrGN : m ∣ GN p r b :=
    Nat.modEq_zero_iff_dvd.mp (hGNmod.trans hGNzero)
  refine ⟨r, ?_, hra.symm⟩
  exact mem_GNDeepLiftResidues_iff.mpr
    ⟨Nat.mod_lt _ hm, hrGN⟩

/--
Injectivity of reduction modulo `q` on canonical depth-`k` GN residues.

This is the exact finite-set form of the Hensel uniqueness obligation: two
depth-`k` roots with the same residue modulo `q` must already be the same
canonical representative modulo `q^k`.
-/
def GNDeepLiftReductionInjective
    (p q b k : ℕ) : Prop :=
  Set.InjOn (fun r => r % q)
    (GNDeepLiftResidues p q b k : Set ℕ)

/--
Pointwise Hensel uniqueness in the exact congruence form suggested by the
memo: two depth-`k` GN roots in the same mod-`q` branch coincide mod `q^k`.
-/
def GNDeepLiftCongruenceUnique
    (p q b k : ℕ) : Prop :=
  ∀ ⦃a r : ℕ⦄,
    q ^ k ∣ GN p a b →
    q ^ k ∣ GN p r b →
    Nat.ModEq q a r →
    Nat.ModEq (q ^ k) a r

/-- Pointwise Hensel uniqueness implies injectivity on canonical residues. -/
theorem GNDeepLiftReductionInjective_of_congruenceUnique
    {p q b k : ℕ}
    (hunique : GNDeepLiftCongruenceUnique p q b k) :
    GNDeepLiftReductionInjective p q b k := by
  intro a ha r hr har
  have ha' := mem_GNDeepLiftResidues_iff.mp ha
  have hr' := mem_GNDeepLiftResidues_iff.mp hr
  have hmodq : Nat.ModEq q a r := by
    change a % q = r % q
    exact har
  have hmodqk := hunique ha'.2 hr'.2 hmodq
  exact hmodqk.eq_of_lt_of_lt ha'.1 hr'.1

/--
Injectivity on canonical depth-`k` residues implies pointwise congruence
uniqueness.  Thus the finite-set and arbitrary-root formulations of the
Hensel obligation carry exactly the same information.
-/
theorem GNDeepLiftCongruenceUnique_of_reductionInjective
    {p q b k : ℕ}
    (hq : Nat.Prime q)
    (hk : 0 < k)
    (hinj : GNDeepLiftReductionInjective p q b k) :
    GNDeepLiftCongruenceUnique p q b k := by
  intro a r ha hr har
  let m := q ^ k
  have hm : 0 < m := pow_pos hq.pos _
  have hqpow : q ∣ m := by
    dsimp [m]
    obtain ⟨j, rfl⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    exact dvd_pow_self q (by omega)
  have haS : a % m ∈ GNDeepLiftResidues p q b k := by
    have hmod : Nat.ModEq m (GN p (a % m) b) (GN p a b) :=
      GN_modEq_left (Nat.mod_modEq a m)
    exact mem_GNDeepLiftResidues_iff.mpr
      ⟨Nat.mod_lt _ hm,
        Nat.modEq_zero_iff_dvd.mp
          (hmod.trans (Nat.modEq_zero_iff_dvd.mpr ha))⟩
  have hrS : r % m ∈ GNDeepLiftResidues p q b k := by
    have hmod : Nat.ModEq m (GN p (r % m) b) (GN p r b) :=
      GN_modEq_left (Nat.mod_modEq r m)
    exact mem_GNDeepLiftResidues_iff.mpr
      ⟨Nat.mod_lt _ hm,
        Nat.modEq_zero_iff_dvd.mp
          (hmod.trans (Nat.modEq_zero_iff_dvd.mpr hr))⟩
  change a % m = r % m
  apply hinj haS hrS
  change (a % m) % q = (r % m) % q
  rw [Nat.mod_mod_of_dvd a hqpow, Nat.mod_mod_of_dvd r hqpow]
  exact har

/-- The canonical-residue and pointwise forms of Hensel uniqueness are equivalent. -/
theorem GNDeepLiftReductionInjective_iff_congruenceUnique
    {p q b k : ℕ}
    (hq : Nat.Prime q)
    (hk : 0 < k) :
    GNDeepLiftReductionInjective p q b k ↔
      GNDeepLiftCongruenceUnique p q b k :=
  ⟨GNDeepLiftCongruenceUnique_of_reductionInjective hq hk,
    GNDeepLiftReductionInjective_of_congruenceUnique⟩

/--
An element of `ZMod (q^k)` whose reduction modulo the prime `q` is nonzero is
a unit.  This is the prime-power cancellation input used by finite Hensel
uniqueness.
-/
theorem isUnit_zmod_primePow_of_castHom_ne_zero
    {q k : ℕ}
    (hq : Nat.Prime q)
    (hk : 0 < k)
    (a : ZMod (q ^ k))
    (ha :
      ZMod.castHom
        (show q ∣ q ^ k by
          obtain ⟨j, rfl⟩ :=
            Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
          exact dvd_pow_self q (by omega))
        (ZMod q) a ≠ 0) :
    IsUnit a := by
  have hqpow_pos : 0 < q ^ k := pow_pos hq.pos _
  letI : NeZero (q ^ k) := ⟨Nat.ne_of_gt hqpow_pos⟩
  let b : ℕ := a.val
  have hb_not_dvd_q : ¬ q ∣ b := by
    intro hqdb
    have hb_zero_q : (b : ZMod q) = 0 :=
      (ZMod.natCast_eq_zero_iff b q).2 hqdb
    have hcast_a_q :
        ZMod.castHom
          (show q ∣ q ^ k by
            obtain ⟨j, rfl⟩ :=
              Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
            exact dvd_pow_self q (by omega))
          (ZMod q) a = (b : ZMod q) := by
      rw [ZMod.castHom_apply, ZMod.cast_eq_val]
    exact ha (hcast_a_q.trans hb_zero_q)
  have hb_coprime : Nat.Coprime b (q ^ k) :=
    hq.coprime_pow_of_not_dvd hb_not_dvd_q
  have hb_unit : IsUnit (b : ZMod (q ^ k)) :=
    (ZMod.isUnit_iff_coprime b (q ^ k)).2 hb_coprime
  convert hb_unit using 1
  change a = (a.val : ZMod (q ^ k))
  exact (ZMod.natCast_zmod_val a).symm

/--
Finite Hensel uniqueness for the GN polynomial.

If `q` divides neither the prime exponent `p` nor the boundary coordinate
`b`, every GN root modulo `q` is simple.  The Taylor quadratic remainder then
shows that two roots modulo `q^k` in the same mod-`q` branch coincide modulo
`q^k`.
-/
theorem GNDeepLiftCongruenceUnique_of_simpleRoot
    {p q b k : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hqp : ¬ q ∣ p)
    (hqb : ¬ q ∣ b)
    (hk : 0 < k) :
    GNDeepLiftCongruenceUnique p q b k := by
  intro a r ha hr har
  let m := q ^ k
  have hm : 0 < m := pow_pos hq.pos _
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hdiv : q ∣ m := by
    dsimp [m]
    obtain ⟨j, rfl⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    exact dvd_pow_self q (by omega)
  let f := ZMod.castHom hdiv (ZMod q)
  let P := GNPolynomial p b (ZMod m)
  have ha0 : Polynomial.eval (a : ZMod m) P = 0 := by
    dsimp [P]
    rw [eval_GNPolynomial, ZMod.natCast_eq_zero_iff]
    exact ha
  have hr0 : Polynomial.eval (r : ZMod m) P = 0 := by
    dsimp [P]
    rw [eval_GNPolynomial, ZMod.natCast_eq_zero_iff]
    exact hr
  let d : ZMod m := (a : ZMod m) - (r : ZMod m)
  obtain ⟨c, hc⟩ :=
    exists_eval_add_eq_eval_add_derivative_mul_add_sq
      P (r : ZMod m) d
  have hrd : (r : ZMod m) + d = (a : ZMod m) := by
    dsimp [d]
    ring
  rw [hrd, ha0, hr0] at hc
  let u : ZMod m :=
    Polynomial.eval (r : ZMod m) P.derivative + c * d
  have hdu : d * u = 0 := by
    change
      d * (Polynomial.eval (r : ZMod m) P.derivative + c * d) = 0
    calc
      d * (Polynomial.eval (r : ZMod m) P.derivative + c * d) =
          Polynomial.eval (r : ZMod m) P.derivative * d +
            c * d ^ 2 := by ring
      _ = 0 := by simpa only [zero_add] using hc.symm
  have harq : (a : ZMod q) = (r : ZMod q) :=
    (ZMod.natCast_eq_natCast_iff a r q).2 har
  have hfd : f d = 0 := by
    change
      f ((a : ZMod m) - (r : ZMod m)) = 0
    rw [map_sub]
    simpa [f] using sub_eq_zero.mpr harq
  have hrrootq :
      Polynomial.eval (r : ZMod q)
        (GNPolynomial p b (ZMod q)) = 0 := by
    rw [eval_GNPolynomial, ZMod.natCast_eq_zero_iff]
    exact hdiv.trans hr
  have hderivativeq :
      Polynomial.eval (r : ZMod q)
        (Polynomial.derivative
          (GNPolynomial p b (ZMod q))) ≠ 0 :=
    eval_derivative_GNPolynomial_ne_zero
      hp hq hqp hqb hrrootq
  have hderivemap :
      f (Polynomial.eval (r : ZMod m) P.derivative) =
        Polynomial.eval (r : ZMod q)
          (Polynomial.derivative
            (GNPolynomial p b (ZMod q))) := by
    have hmap :=
      Polynomial.eval_map_apply
        (p := P.derivative) f (r : ZMod m)
    simpa [P, f, ← Polynomial.derivative_map,
      map_GNPolynomial] using hmap.symm
  have hfu :
      f u =
        Polynomial.eval (r : ZMod q)
          (Polynomial.derivative
            (GNPolynomial p b (ZMod q))) := by
    dsimp [u]
    rw [map_add, map_mul, hfd, mul_zero, add_zero]
    exact hderivemap
  have hfu0 : f u ≠ 0 := by
    rw [hfu]
    exact hderivativeq
  have hu : IsUnit u :=
    isUnit_zmod_primePow_of_castHom_ne_zero
      hq hk u hfu0
  have hd0 : d = 0 := hu.mul_left_eq_zero.mp hdu
  apply (ZMod.natCast_eq_natCast_iff a r m).1
  exact sub_eq_zero.mp hd0

/-- Simple GN roots give injective reduction on canonical depth-`k` residues. -/
theorem GNDeepLiftReductionInjective_of_simpleRoot
    {p q b k : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hqp : ¬ q ∣ p)
    (hqb : ¬ q ∣ b)
    (hk : 0 < k) :
    GNDeepLiftReductionInjective p q b k :=
  GNDeepLiftReductionInjective_of_congruenceUnique
    (GNDeepLiftCongruenceUnique_of_simpleRoot
      hp hq hqp hqb hk)

/-- At depth one the Hensel uniqueness condition is tautological. -/
theorem GNDeepLiftCongruenceUnique_one
    (p q b : ℕ) :
    GNDeepLiftCongruenceUnique p q b 1 := by
  intro a r ha hr har
  simpa using har

/--
Hensel reduction injectivity bounds the number of depth-`k` residues by the
number of roots modulo `q`.
-/
theorem GNDeepLiftResidues_card_le_base
    {p q b k : ℕ}
    (hq : Nat.Prime q)
    (hk : 0 < k)
    (hinj : GNDeepLiftReductionInjective p q b k) :
    (GNDeepLiftResidues p q b k).card ≤
      (GNDeepLiftResidues p q b 1).card := by
  classical
  let S := GNDeepLiftResidues p q b k
  let T := GNDeepLiftResidues p q b 1
  let f := fun r : ℕ => r % q
  have hmap : S.image f ⊆ T := by
    intro r hr
    obtain ⟨a, haS, rfl⟩ := Finset.mem_image.mp hr
    have ha := mem_GNDeepLiftResidues_iff.mp haS
    have hqpow : q ∣ q ^ k := by
      obtain ⟨j, rfl⟩ :=
        Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
      exact dvd_pow_self q (by omega)
    have hqGN : q ∣ GN p a b := hqpow.trans ha.2
    have hmod :
        Nat.ModEq q (GN p (a % q) b) (GN p a b) :=
      GN_modEq_left (Nat.mod_modEq a q)
    have hz : Nat.ModEq q (GN p a b) 0 :=
      Nat.modEq_zero_iff_dvd.mpr hqGN
    apply mem_GNDeepLiftResidues_iff.mpr
    constructor
    · simpa using Nat.mod_lt a hq.pos
    · simpa using
        Nat.modEq_zero_iff_dvd.mp (hmod.trans hz)
  calc
    S.card = (S.image f).card := by
      symm
      apply Finset.card_image_iff.mpr
      intro a ha a' ha' haa'
      exact hinj ha ha' haa'
    _ ≤ T.card := Finset.card_le_card hmap

/--
The two independent arithmetic obligations that imply the canonical
depth-`k` cardinality bound: at most `p - 1` roots modulo `q`, and unique
lifting from each such root.
-/
theorem GNDeepLiftResidues_card_le
    {p q b k : ℕ}
    (hq : Nat.Prime q)
    (hk : 0 < k)
    (hbase :
      (GNDeepLiftResidues p q b 1).card ≤ p - 1)
    (hinj : GNDeepLiftReductionInjective p q b k) :
    (GNDeepLiftResidues p q b k).card ≤ p - 1 :=
  (GNDeepLiftResidues_card_le_base hq hk hinj).trans hbase

/--
For prime exponent `p`, Hensel reduction injectivity is now the only remaining
input needed for the canonical depth-`k` cardinality bound.
-/
theorem GNDeepLiftResidues_card_le_of_reduction
    {p q b k : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hk : 0 < k)
    (hinj : GNDeepLiftReductionInjective p q b k) :
    (GNDeepLiftResidues p q b k).card ≤ p - 1 :=
  GNDeepLiftResidues_card_le hq hk
    (GNDeepLiftResidues_card_base_le hp hq) hinj

/-- The canonical GN residue set has at most `p - 1` elements at every depth. -/
theorem GNDeepLiftResidues_card_le_of_simpleRoot
    {p q b k : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hqp : ¬ q ∣ p)
    (hqb : ¬ q ∣ b)
    (hk : 0 < k) :
    (GNDeepLiftResidues p q b k).card ≤ p - 1 :=
  GNDeepLiftResidues_card_le_of_reduction
    hp hq hk
      (GNDeepLiftReductionInjective_of_simpleRoot
        hp hq hqp hqb hk)

/-- A finite residue cover gives the corresponding interval count. -/
theorem card_gn_deep_lift_range_le_of_residueCover
    {p q b k X : ℕ} {R : Finset ℕ}
    (hq : Nat.Prime q)
    (hcover : GNDeepLiftResidueCover p q b k R) :
    ((Finset.range (X + 1)).filter
      (fun a => q ^ k ∣ GN p a b)).card ≤
        R.card * ((X + 1) / q ^ k + 1) := by
  classical
  let m := q ^ k
  let C := fun r =>
    (Finset.range (X + 1)).filter (fun a => Nat.ModEq m a r)
  have hm : 0 < m := pow_pos hq.pos _
  have hsub :
      (Finset.range (X + 1)).filter
          (fun a => q ^ k ∣ GN p a b) ⊆
        R.biUnion C := by
    intro a ha
    rcases Finset.mem_filter.mp ha with ⟨haX, haGN⟩
    obtain ⟨r, hrR, har⟩ := hcover a haGN
    exact Finset.mem_biUnion.mpr
      ⟨r, hrR, Finset.mem_filter.mpr ⟨haX, har⟩⟩
  calc
    ((Finset.range (X + 1)).filter
        (fun a => q ^ k ∣ GN p a b)).card
        ≤ (R.biUnion C).card :=
          Finset.card_le_card hsub
    _ ≤ ∑ r ∈ R, (C r).card :=
          Finset.card_biUnion_le
    _ ≤ ∑ _r ∈ R, ((X + 1) / m + 1) := by
          apply Finset.sum_le_sum
          intro r _hr
          have hcount :=
            Nat.count_modEq_card (X + 1) hm r
          have hcount' :
              (C r).card =
                (X + 1) / m +
                  if r % m < (X + 1) % m then 1 else 0 := by
            simpa [C, Nat.count_eq_card_filter_range] using hcount
          rw [hcount']
          split_ifs <;> omega
    _ = R.card * ((X + 1) / q ^ k + 1) := by
          simp [m]

/-- A cover with at most `p - 1` addresses gives the memo's GN count shape. -/
theorem card_gn_deep_lift_range_le
    {p q b k X : ℕ} {R : Finset ℕ}
    (hq : Nat.Prime q)
    (hcard : R.card ≤ p - 1)
    (hcover : GNDeepLiftResidueCover p q b k R) :
    ((Finset.range (X + 1)).filter
      (fun a => q ^ k ∣ GN p a b)).card ≤
        (p - 1) * ((X + 1) / q ^ k + 1) := by
  calc
    ((Finset.range (X + 1)).filter
      (fun a => q ^ k ∣ GN p a b)).card
        ≤ R.card * ((X + 1) / q ^ k + 1) :=
          card_gn_deep_lift_range_le_of_residueCover hq hcover
    _ ≤ (p - 1) * ((X + 1) / q ^ k + 1) :=
          Nat.mul_le_mul_right _ hcard

/-- `Finset.Icc` form of the finite-address GN count. -/
theorem card_gn_deep_lift_residue_classes_le
    {p q b k X : ℕ} {R : Finset ℕ}
    (hq : Nat.Prime q)
    (hcard : R.card ≤ p - 1)
    (hcover : GNDeepLiftResidueCover p q b k R) :
    ((Finset.Icc 0 X).filter
      (fun a => q ^ k ∣ GN p a b)).card ≤
        (p - 1) * ((X + 1) / q ^ k + 1) := by
  rw [← Nat.range_succ_eq_Icc_zero]
  exact card_gn_deep_lift_range_le hq hcard hcover

/--
Canonical-cover form of the deep-lift count.

After `GNDeepLiftResidues_cover`, the only arithmetic input left here is the
cardinality bound for the canonical residue set.
-/
theorem card_gn_deep_lift_residue_classes_le_of_canonical
    {p q b k X : ℕ}
    (hq : Nat.Prime q)
    (hcard : (GNDeepLiftResidues p q b k).card ≤ p - 1) :
    ((Finset.Icc 0 X).filter
      (fun a => q ^ k ∣ GN p a b)).card ≤
        (p - 1) * ((X + 1) / q ^ k + 1) :=
  card_gn_deep_lift_residue_classes_le
    hq hcard (GNDeepLiftResidues_cover hq)

/--
Deep-lift interval count from the two arithmetic frontier statements:
the mod-`q` root count and Hensel reduction injectivity.
-/
theorem card_gn_deep_lift_residue_classes_le_of_base_and_reduction
    {p q b k X : ℕ}
    (hq : Nat.Prime q)
    (hk : 0 < k)
    (hbase :
      (GNDeepLiftResidues p q b 1).card ≤ p - 1)
    (hinj : GNDeepLiftReductionInjective p q b k) :
    ((Finset.Icc 0 X).filter
      (fun a => q ^ k ∣ GN p a b)).card ≤
        (p - 1) * ((X + 1) / q ^ k + 1) :=
  card_gn_deep_lift_residue_classes_le_of_canonical
    hq (GNDeepLiftResidues_card_le hq hk hbase hinj)

/--
Prime-exponent deep-lift count with only the Hensel reduction-injectivity
frontier left explicit.
-/
theorem card_gn_deep_lift_residue_classes_le_of_reduction
    {p q b k X : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hk : 0 < k)
    (hinj : GNDeepLiftReductionInjective p q b k) :
    ((Finset.Icc 0 X).filter
      (fun a => q ^ k ∣ GN p a b)).card ≤
        (p - 1) * ((X + 1) / q ^ k + 1) :=
  card_gn_deep_lift_residue_classes_le_of_canonical
    hq (GNDeepLiftResidues_card_le_of_reduction
      hp hq hk hinj)

/--
Unconditional finite GN deep-lift count in the non-exceptional
`q ∤ p`, `q ∤ b` channel.
-/
theorem card_gn_deep_lift_residue_classes_le_of_simpleRoot
    {p q b k X : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hqp : ¬ q ∣ p)
    (hqb : ¬ q ∣ b)
    (hk : 0 < k) :
    ((Finset.Icc 0 X).filter
      (fun a => q ^ k ∣ GN p a b)).card ≤
        (p - 1) * ((X + 1) / q ^ k + 1) :=
  card_gn_deep_lift_residue_classes_le_of_canonical
    hq (GNDeepLiftResidues_card_le_of_simpleRoot
      hp hq hqp hqb hk)

/--
Final deep-lift count interface in the memo's pointwise Hensel-congruence
vocabulary.
-/
theorem card_gn_deep_lift_residue_classes_le_of_congruenceUnique
    {p q b k X : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hk : 0 < k)
    (hunique : GNDeepLiftCongruenceUnique p q b k) :
    ((Finset.Icc 0 X).filter
      (fun a => q ^ k ∣ GN p a b)).card ≤
        (p - 1) * ((X + 1) / q ^ k + 1) :=
  card_gn_deep_lift_residue_classes_le_of_reduction
    hp hq hk
      (GNDeepLiftReductionInjective_of_congruenceUnique
        hunique)

/-- Divisibility layers and p-adic-depth layers are the same when GN is nonzero. -/
theorem gn_deep_lift_filter_eq_padic_depth_filter
    {p q b k X : ℕ}
    (hq : Nat.Prime q)
    (hGN :
      ∀ a ∈ Finset.Icc 0 X, GN p a b ≠ 0) :
    (Finset.Icc 0 X).filter
        (fun a => q ^ k ∣ GN p a b) =
      (Finset.Icc 0 X).filter
        (fun a => k ≤ padicValNat q (GN p a b)) := by
  ext a
  simp only [Finset.mem_filter]
  constructor
  · intro ha
    exact ⟨ha.1,
      (padicValNat_le_iff_dvd hq (hGN a ha.1) k).2 ha.2⟩
  · intro ha
    exact ⟨ha.1,
      (padicValNat_le_iff_dvd hq (hGN a ha.1) k).1 ha.2⟩

/--
Exact finite layer-cake identity for a bounded natural-valued function.

The sum of the values is the sum, over all positive depth layers, of the
number of points reaching that layer.
-/
theorem sum_nat_eq_sum_card_ge
    {α : Type*}
    (s : Finset α) (V : α → ℕ) (K : ℕ)
    (hV : ∀ a ∈ s, V a ≤ K) :
    ∑ a ∈ s, V a =
      ∑ k ∈ Finset.Icc 1 K,
        (s.filter (fun a => k ≤ V a)).card := by
  classical
  calc
    ∑ a ∈ s, V a =
        ∑ a ∈ s, ∑ k ∈ Finset.Icc 1 K,
          if k ≤ V a then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      have hcard : (Finset.Icc 1 (V a)).card = V a := by
        rw [Nat.card_Icc]
        omega
      calc
        V a = (Finset.Icc 1 (V a)).card := hcard.symm
        _ = ((Finset.Icc 1 K).filter (fun k => k ≤ V a)).card := by
          congr 1
          ext k
          simp only [Finset.mem_Icc, Finset.mem_filter]
          constructor
          · intro hk
            exact ⟨⟨hk.1, hk.2.trans (hV a ha)⟩, hk.2⟩
          · intro hk
            exact ⟨hk.1.1, hk.2⟩
        _ = ∑ k ∈ Finset.Icc 1 K,
              if k ≤ V a then 1 else 0 := by simp
    _ = ∑ k ∈ Finset.Icc 1 K, ∑ a ∈ s,
          if k ≤ V a then 1 else 0 := by
      exact Finset.sum_comm
    _ = ∑ k ∈ Finset.Icc 1 K,
        (s.filter (fun a => k ≤ V a)).card := by
      apply Finset.sum_congr rfl
      intro k hk
      simp

/--
Uniform elementary size bound for GN on `a ∈ [0,X]`.

The geometric-sum form of GN has `p` terms, each bounded by `(X+b)^p`.
-/
theorem GN_le_mul_interval_add_pow
    {p a b X : ℕ}
    (hb : 0 < b)
    (ha : a ≤ X) :
    GN p a b ≤ p * (X + b) ^ p := by
  rw [GN_eq_geom_sum₂]
  calc
    ∑ i ∈ Finset.range p,
        (a + b) ^ i * b ^ (p - 1 - i) ≤
        ∑ _i ∈ Finset.range p, (X + b) ^ p := by
      apply Finset.sum_le_sum
      intro i hi
      have hip : i < p := Finset.mem_range.mp hi
      have hab : a + b ≤ X + b := Nat.add_le_add_right ha b
      have hbX : b ≤ X + b := Nat.le_add_left b X
      calc
        (a + b) ^ i * b ^ (p - 1 - i) ≤
            (X + b) ^ i * (X + b) ^ (p - 1 - i) :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hab i)
            (Nat.pow_le_pow_left hbX (p - 1 - i))
        _ = (X + b) ^ (p - 1) := by
          rw [← pow_add]
          congr 1
          omega
        _ ≤ (X + b) ^ p := by
          exact Nat.pow_le_pow_right (by omega) (by omega)
    _ = p * (X + b) ^ p := by simp

/-- GN is nonzero for prime exponent and nonzero right coordinate. -/
theorem GN_ne_zero_of_prime_of_right_ne_zero
    {p a b : ℕ}
    (hp : Nat.Prime p)
    (hb : b ≠ 0) :
    GN p a b ≠ 0 := by
  cases a with
  | zero =>
      rw [show GN p 0 b = p * b ^ (p - 1) by
        simpa [GN] using
          (DkMath.CosmicFormula.GN_zero_eval (R := ℕ) p b)]
      exact Nat.mul_ne_zero hp.ne_zero (pow_ne_zero _ hb)
  | succ a =>
      exact GN_ne_zero_nat_of_two_le
        hp.two_le (Nat.succ_pos a) (Nat.pos_of_ne_zero hb)

/--
The sum of the integer quotients `N / q^k` over any finite positive depth
range is at most `N`.

This is a finite consequence of Legendre's formula for the valuation of
`N!`; the auxiliary Legendre range is enlarged when necessary.
-/
theorem sum_div_prime_pow_Icc_le
    {q N K : ℕ}
    (hq : Nat.Prime q) :
    ∑ k ∈ Finset.Icc 1 K, N / q ^ k ≤ N := by
  let B := max (K + 1) (Nat.log q N + 1)
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  have hlog : Nat.log q N < B := by
    exact (Nat.lt_succ_self _).trans_le
      (Nat.le_max_right _ _)
  have hsub : Finset.Icc 1 K ⊆ Finset.Ico 1 B := by
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    exact Finset.mem_Ico.mpr
      ⟨hk'.1, (Nat.lt_succ_of_le hk'.2).trans_le
        (Nat.le_max_left _ _)⟩
  calc
    ∑ k ∈ Finset.Icc 1 K, N / q ^ k ≤
        ∑ k ∈ Finset.Ico 1 B, N / q ^ k := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun i hi₁ hi₂ => Nat.zero_le _)
    _ = padicValNat q N.factorial := by
      symm
      exact padicValNat_factorial hlog
    _ ≤ N := padicValNat_factorial_le q N

/--
Layer-explicit average GN valuation bound for one non-exceptional prime.

The cutoff is intrinsic and explicit: the elementary size bound on GN gives
`v_q(GN) ≤ log_q (p (X+b)^p)`.
-/
theorem sum_padicValNat_GN_le_of_simpleRoot_layers
    {p q b X : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hqp : ¬ q ∣ p)
    (hqb : ¬ q ∣ b) :
    ∑ a ∈ Finset.Icc 0 X, padicValNat q (GN p a b) ≤
      (p - 1) *
        ∑ k ∈ Finset.Icc 1 (Nat.log q (p * (X + b) ^ p)),
          ((X + 1) / q ^ k + 1) := by
  have hb0 : b ≠ 0 := by
    intro hb
    subst b
    exact hqb (dvd_zero q)
  have hb : 0 < b := Nat.pos_of_ne_zero hb0
  let V := fun a => padicValNat q (GN p a b)
  let K := Nat.log q (p * (X + b) ^ p)
  have hGN :
      ∀ a ∈ Finset.Icc 0 X, GN p a b ≠ 0 := by
    intro a ha
    exact GN_ne_zero_of_prime_of_right_ne_zero hp hb0
  have hV :
      ∀ a ∈ Finset.Icc 0 X, V a ≤ K := by
    intro a ha
    dsimp [V, K]
    exact (padicValNat_le_nat_log (GN p a b)).trans
      (Nat.log_mono_right
        (GN_le_mul_interval_add_pow hb
          (Finset.mem_Icc.mp ha).2))
  rw [sum_nat_eq_sum_card_ge (Finset.Icc 0 X) V K hV]
  calc
    ∑ k ∈ Finset.Icc 1 K,
        ((Finset.Icc 0 X).filter
          (fun a => k ≤ V a)).card ≤
        ∑ k ∈ Finset.Icc 1 K,
          (p - 1) * ((X + 1) / q ^ k + 1) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkpos : 0 < k := (Finset.mem_Icc.mp hk).1
      have heq :=
        congrArg Finset.card
          (gn_deep_lift_filter_eq_padic_depth_filter
            (p := p) (q := q) (b := b) (k := k) (X := X)
            hq hGN)
      change
        ((Finset.Icc 0 X).filter
          (fun a => k ≤ padicValNat q (GN p a b))).card ≤
            (p - 1) * ((X + 1) / q ^ k + 1)
      rw [← heq]
      exact card_gn_deep_lift_residue_classes_le_of_simpleRoot
        hp hq hqp hqb hkpos
    _ = (p - 1) *
        ∑ k ∈ Finset.Icc 1 K,
          ((X + 1) / q ^ k + 1) := by
      rw [Finset.mul_sum]

/--
Explicit average valuation bound for a fixed non-exceptional prime:

`∑_{a=0}^X v_q(GN_p(a,b))`
is at most `(p-1) * (X+1 + log_q (p (X+b)^p))`.
-/
theorem sum_padicValNat_GN_le_of_simpleRoot
    {p q b X : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hqp : ¬ q ∣ p)
    (hqb : ¬ q ∣ b) :
    ∑ a ∈ Finset.Icc 0 X, padicValNat q (GN p a b) ≤
      (p - 1) *
        ((X + 1) + Nat.log q (p * (X + b) ^ p)) := by
  let K := Nat.log q (p * (X + b) ^ p)
  calc
    ∑ a ∈ Finset.Icc 0 X, padicValNat q (GN p a b) ≤
        (p - 1) *
          ∑ k ∈ Finset.Icc 1 K,
            ((X + 1) / q ^ k + 1) :=
      sum_padicValNat_GN_le_of_simpleRoot_layers
        hp hq hqp hqb
    _ = (p - 1) *
        ((∑ k ∈ Finset.Icc 1 K, (X + 1) / q ^ k) +
          (Finset.Icc 1 K).card) := by
      congr 1
      rw [Finset.sum_add_distrib]
      simp
    _ ≤ (p - 1) * ((X + 1) + K) := by
      apply Nat.mul_le_mul_left
      have hdiv :=
        sum_div_prime_pow_Icc_le
          (q := q) (N := X + 1) (K := K) hq
      have hcard : (Finset.Icc 1 K).card = K := by
        rw [Nat.card_Icc]
        omega
      rw [hcard]
      omega

/--
Log-weighted form of the fixed-prime average valuation bound.

This is the local weighted input needed before summing over non-exceptional
primes in an averaged GN depth-mass estimate.
-/
theorem sum_padicValNat_GN_mul_log_le_of_simpleRoot
    {p q b X : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hqp : ¬ q ∣ p)
    (hqb : ¬ q ∣ b) :
    ∑ a ∈ Finset.Icc 0 X,
        (padicValNat q (GN p a b) : ℝ) *
          Real.log (q : ℝ) ≤
      (((p - 1) *
        ((X + 1) + Nat.log q (p * (X + b) ^ p)) : ℕ) : ℝ) *
          Real.log (q : ℝ) := by
  have hsum :=
    sum_padicValNat_GN_le_of_simpleRoot
      (X := X) hp hq hqp hqb
  have hsumR :
      (∑ a ∈ Finset.Icc 0 X,
        (padicValNat q (GN p a b) : ℝ)) ≤
      (((p - 1) *
        ((X + 1) + Nat.log q (p * (X + b) ^ p)) : ℕ) : ℝ) := by
    exact_mod_cast hsum
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right hsumR
    (Real.log_nonneg (by exact_mod_cast hq.one_le))

/--
Finite-family weighted GN depth-mass bound.

This sums the fixed-prime estimate over any finite family of primes avoiding
both the exponent `p` and the boundary coordinate `b`.  It is the averaged
multi-prime interface; selecting a useful family and turning this average into
a pointwise compensation statement remain separate obligations.
-/
theorem sum_GN_depthMass_over_interval_le
    {p b X : ℕ}
    (Q : Finset ℕ)
    (hp : Nat.Prime p)
    (hQprime : ∀ q ∈ Q, Nat.Prime q)
    (hQp : ∀ q ∈ Q, ¬ q ∣ p)
    (hQb : ∀ q ∈ Q, ¬ q ∣ b) :
    ∑ a ∈ Finset.Icc 0 X,
        ∑ q ∈ Q,
          (padicValNat q (GN p a b) : ℝ) *
            Real.log (q : ℝ) ≤
      ∑ q ∈ Q,
        ((((p - 1) *
          ((X + 1) + Nat.log q (p * (X + b) ^ p)) : ℕ) : ℝ) *
            Real.log (q : ℝ)) := by
  calc
    ∑ a ∈ Finset.Icc 0 X,
        ∑ q ∈ Q,
          (padicValNat q (GN p a b) : ℝ) *
            Real.log (q : ℝ) =
        ∑ q ∈ Q,
          ∑ a ∈ Finset.Icc 0 X,
            (padicValNat q (GN p a b) : ℝ) *
              Real.log (q : ℝ) := Finset.sum_comm
    _ ≤ ∑ q ∈ Q,
        ((((p - 1) *
          ((X + 1) + Nat.log q (p * (X + b) ^ p)) : ℕ) : ℝ) *
            Real.log (q : ℝ)) := by
      apply Finset.sum_le_sum
      intro q hq
      exact sum_padicValNat_GN_mul_log_le_of_simpleRoot
        hp (hQprime q hq) (hQp q hq) (hQb q hq)

/-- Feed GN p-adic depth directly into the legacy finite exponential layer-cake. -/
theorem exp_gn_padic_layer_cake
    {p q b X : ℕ} {t : ℝ}
    (ht : 0 < t)
    (hVbd :
      ∀ a ≤ X, padicValNat q (GN p a b) ≤ X + 1) :
    (∑ a ∈ Finset.Icc 0 X,
        Real.exp (t * (padicValNat q (GN p a b) : ℝ))) ≤
      (X + 1 : ℝ) + (Real.exp t - 1) *
        (∑ k ∈ Finset.Icc 1 (X + 1),
          Real.exp (t * ((k : ℝ) - 1)) *
            (((Finset.Icc 0 X).filter
              (fun a =>
                a ≤ X ∧
                  k ≤ padicValNat q (GN p a b))).card : ℝ)) := by
  exact exp_layer_cake X t ht
    (fun a => padicValNat q (GN p a b)) hVbd

end DkMath.ABC
