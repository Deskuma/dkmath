/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.Basic
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Data.Nat.Prime.Pow
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.Legendre.SquareShellPrimePower"

/-! Finite square-shell power gaps. No prime-existence provider is asserted. -/

namespace DkMath.NumberTheory.Legendre

/-- Consecutive squares leave no room for another square. -/
theorem not_squareCell_square (n m : ℕ) : ¬ SquareCell n (m ^ 2) := by
  rintro ⟨hl, hu⟩
  have hnm : n < m := by nlinarith
  have hmn : m < n + 1 := by nlinarith
  omega

/-- Every even power is a square, independently of the base. -/
theorem not_squareCell_even_power (n p a : ℕ) (ha : Even a) :
    ¬ SquareCell n (p ^ a) := by
  obtain ⟨b, rfl⟩ := ha
  simpa only [pow_add, ← pow_two] using not_squareCell_square n (p ^ b)

/-- A nonprime prime power in the shell has odd depth at least three. -/
theorem shell_nonprime_power_depth {n p a : ℕ} (hp : p.Prime)
    (hcell : SquareCell n (p ^ a)) (hnot : ¬ (p ^ a).Prime) :
    3 ≤ a ∧ Odd a := by
  have hne : a ≠ 1 := by intro h; subst a; exact hnot (by simpa using hp)
  have he : ¬ Even a := fun h => not_squareCell_even_power n p a h hcell
  have ho : Odd a := (Nat.even_or_odd a).resolve_left he
  have ha : a ≠ 0 := by intro h; subst a; exact he (by decide)
  have htwo : a ≠ 2 := by intro h; subst a; exact he (by decide)
  exact ⟨by omega, ho⟩

/-- Powers of depth at least two in a square shell have base at most the anchor. -/
theorem squareCell_power_base_le {n x a : ℕ} (ha : 2 ≤ a)
    (hcell : SquareCell n (x ^ a)) : x ≤ n := by
  by_contra h
  have hx : 1 ≤ x := by omega
  have hpow : x ^ 2 ≤ x ^ a := Nat.pow_le_pow_right hx ha
  have hnx : n + 1 ≤ x := by omega
  have hs : (n + 1) ^ 2 ≤ x ^ 2 := Nat.pow_le_pow_left hnx 2
  exact (not_lt_of_ge (hs.trans hpow)) hcell.2

/-- Canonical base and depth, using the existing factorization identity. -/
theorem shell_higher_primePower_canonical {n q : ℕ}
    (hcell : SquareCell n q) (hq : IsPrimePow q) (hnot : ¬ q.Prime) :
    q.minFac.Prime ∧ 3 ≤ q.factorization q.minFac ∧
      Odd (q.factorization q.minFac) ∧
      q = q.minFac ^ q.factorization q.minFac ∧
      q.minFac ≤ n ∧ q.minFac ^ 3 < (n + 1) ^ 2 := by
  have hp := Nat.minFac_prime hq.ne_one
  have heq := hq.minFac_pow_factorization_eq.symm
  have hc : SquareCell n (q.minFac ^ q.factorization q.minFac) := by
    rw [← heq]; exact hcell
  have hd := shell_nonprime_power_depth hp hc (by rw [← heq]; exact hnot)
  refine ⟨hp, hd.1, hd.2, heq, squareCell_power_base_le (by omega) hc, ?_⟩
  exact lt_of_le_of_lt (Nat.pow_le_pow_right hp.one_lt.le hd.1) hc.2

/-- Adjacent powers of a fixed base are farther apart than the shell ratio. -/
theorem squareCell_prime_power_exponent_unique {n p a b : ℕ} (hn : 3 ≤ n)
    (hp : p.Prime) (ha : SquareCell n (p ^ a)) (hb : SquareCell n (p ^ b)) :
    a = b := by
  have gap : (n + 1) ^ 2 < 2 * n ^ 2 := by nlinarith
  have order : ∀ i j, SquareCell n (p ^ i) → SquareCell n (p ^ j) → i < j → False := by
    intro i j hi hj hij
    have hpows := Nat.pow_le_pow_right hp.one_lt.le (show i + 1 ≤ j by omega)
    rw [pow_succ] at hpows
    have hmul : 2 * p ^ i ≤ p ^ i * p := by simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (p ^ i) hp.two_le
    have : 2 * n ^ 2 < p ^ j := lt_of_lt_of_le (by nlinarith [hi.1]) (hmul.trans hpows)
    nlinarith [hj.2]
  by_contra h
  rcases lt_or_gt_of_ne h with hab | hba
  · exact order a b ha hb hab
  · exact order b a hb ha hba

/-- The minFac map is injective on prime-power labels in one shell. -/
theorem squareCell_primePower_minFac_injective {n q r : ℕ} (hn : 3 ≤ n)
    (hq : IsPrimePow q) (hr : IsPrimePow r)
    (hcq : SquareCell n q) (hcr : SquareCell n r) (he : q.minFac = r.minFac) :
    q = r := by
  have hp := Nat.minFac_prime hq.ne_one
  have eqQ := hq.minFac_pow_factorization_eq
  have eqR := hr.minFac_pow_factorization_eq
  have eqR' : q.minFac ^ r.factorization r.minFac = r := by
    rw [he]; exact eqR
  have ha : SquareCell n (q.minFac ^ q.factorization q.minFac) := by rw [eqQ]; exact hcq
  have hb : SquareCell n (q.minFac ^ r.factorization r.minFac) := by rw [eqR']; exact hcr
  have hab := squareCell_prime_power_exponent_unique hn hp ha hb
  rw [← eqQ, ← eqR', hab]

/-- The preceding power exceeds the anchor whenever depth is at least three. -/
theorem squareCell_power_previous_gt {n x a : ℕ} (ha : 3 ≤ a)
    (hcell : SquareCell n (x ^ a)) : n < x ^ (a - 1) := by
  have hx := squareCell_power_base_le (by omega) hcell
  have he : a - 1 + 1 = a := by omega
  have hp : x ^ a = x ^ (a - 1) * x := by rw [← pow_succ, he]
  by_contra h
  have hprev : x ^ (a - 1) ≤ n := by omega
  have hm := Nat.mul_le_mul hprev hx
  rw [← hp] at hm
  nlinarith [hcell.1]

/-- Fixed depth at least three admits at most one natural power in the shell. -/
theorem squareCell_fixed_exponent_unique {n x y a : ℕ} (ha : 3 ≤ a)
    (hx : SquareCell n (x ^ a)) (hy : SquareCell n (y ^ a)) : x = y := by
  have gap : ∀ u v, u < v → SquareCell n (u ^ a) → SquareCell n (v ^ a) → False := by
    intro u v huv hu hv
    have hprev := squareCell_power_previous_gt ha hu
    have hder := pow_add_mul_le_add_pow (show 0 ≤ u by omega)
      (show 0 ≤ 2 * u + 1 by omega) a
    simp only [Nat.cast_id, mul_one] at hder
    have hmono : (u + 1) ^ a ≤ v ^ a := Nat.pow_le_pow_left (by omega) a
    have hmul : 3 * u ^ (a - 1) ≤ a * u ^ (a - 1) := Nat.mul_le_mul_right _ ha
    nlinarith [hu.1, hv.2]
  by_contra h
  rcases lt_or_gt_of_ne h with hxy | hyx
  · exact gap x y hxy hx hy
  · exact gap y x hyx hy hx

/-- Prime bases enforce a finite binary logarithmic exponent cutoff. -/
theorem squareCell_prime_power_exponent_le_log {n p a : ℕ} (hp : p.Prime)
    (hcell : SquareCell n (p ^ a)) : a ≤ Nat.log 2 ((n + 1) ^ 2) := by
  have htwo : 2 ^ a ≤ p ^ a := Nat.pow_le_pow_left hp.two_le a
  exact Nat.le_log_of_pow_le (by decide) (htwo.trans hcell.2.le)

/-- Exact finite labels of nonprime prime-power events. -/
def shellHigherPrimePowerEvents (n : ℕ) : Finset ℕ :=
  (Finset.Icc (n ^ 2 + 1) (n ^ 2 + 2 * n)).filter
    (fun q => IsPrimePow q ∧ ¬ q.Prime)

@[simp] theorem mem_shellHigherPrimePowerEvents {n q : ℕ} :
    q ∈ shellHigherPrimePowerEvents n ↔ SquareCell n q ∧ IsPrimePow q ∧ ¬ q.Prime := by
  simp only [shellHigherPrimePowerEvents, Finset.mem_filter, Finset.mem_Icc]
  unfold SquareCell
  have he : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
  rw [he]
  constructor
  · rintro ⟨⟨hl, hu⟩, hp, hn⟩
    exact ⟨⟨by omega, by omega⟩, hp, hn⟩
  · rintro ⟨⟨hl, hu⟩, hp, hn⟩
    exact ⟨⟨by omega, by omega⟩, hp, hn⟩

/-- Exponent-indexed prime bases; depth at least two guarantees this finite bound. -/
def shellPrimePowerBasesAtExponent (n a : ℕ) : Finset ℕ :=
  (Nat.primesLE n).filter (fun p => n ^ 2 < p ^ a ∧ p ^ a < (n + 1) ^ 2)

@[simp] theorem mem_shellPrimePowerBasesAtExponent {n a p : ℕ} :
    p ∈ shellPrimePowerBasesAtExponent n a ↔ p.Prime ∧ p ≤ n ∧ SquareCell n (p ^ a) := by
  simp only [shellPrimePowerBasesAtExponent, Finset.mem_filter, Nat.mem_primesLE, SquareCell]
  tauto

/-- Even exponents contribute no bases. -/
theorem shellPrimePowerBasesAtExponent_even (n a : ℕ) (ha : Even a) :
    shellPrimePowerBasesAtExponent n a = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  exact not_squareCell_even_power n p a ha (mem_shellPrimePowerBasesAtExponent.mp hp).2.2

/-- Each depth at least three contributes at most one prime base. -/
theorem shellPrimePowerBasesAtExponent_card_le_one (n a : ℕ) (ha : 3 ≤ a) :
    (shellPrimePowerBasesAtExponent n a).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp q hq
  exact squareCell_fixed_exponent_unique ha
    (mem_shellPrimePowerBasesAtExponent.mp hp).2.2
    (mem_shellPrimePowerBasesAtExponent.mp hq).2.2

/-- Canonical depths are injective, using the fixed-exponent power gap. -/
theorem shellHigherPrimePower_depth_injective (n : ℕ) :
    Set.InjOn (fun q : ℕ => q.factorization q.minFac) (↑(shellHigherPrimePowerEvents n) : Set ℕ) := by
  intro q hq r hr he
  have hq' := mem_shellHigherPrimePowerEvents.mp hq
  have hr' := mem_shellHigherPrimePowerEvents.mp hr
  have cq := shell_higher_primePower_canonical hq'.1 hq'.2.1 hq'.2.2
  have cr := shell_higher_primePower_canonical hr'.1 hr'.2.1 hr'.2.2
  change q.factorization q.minFac = r.factorization r.minFac at he
  have eqr : r = r.minFac ^ q.factorization q.minFac := by rw [he]; exact cr.2.2.2.1
  have hbase := squareCell_fixed_exponent_unique cq.2.1
    (show SquareCell n (q.minFac ^ q.factorization q.minFac) by rw [← cq.2.2.2.1]; exact hq'.1)
    (show SquareCell n (r.minFac ^ q.factorization q.minFac) by rw [← eqr]; exact hr'.1)
  rw [cq.2.2.2.1, eqr, hbase]

/-- A simple explicit logarithmic event-count bound. -/
theorem shellHigherPrimePowerEvents_card_le (n : ℕ) :
    (shellHigherPrimePowerEvents n).card ≤ Nat.log 2 ((n + 1) ^ 2) + 1 := by
  have hc : (shellHigherPrimePowerEvents n).card ≤
      (Finset.range (Nat.log 2 ((n + 1) ^ 2) + 1)).card := by
    apply Finset.card_le_card_of_injOn (fun q : ℕ => q.factorization q.minFac)
    · intro q hq
      have h := mem_shellHigherPrimePowerEvents.mp hq
      have c := shell_higher_primePower_canonical h.1 h.2.1 h.2.2
      have he := squareCell_prime_power_exponent_le_log c.1
        (show SquareCell n (q.minFac ^ q.factorization q.minFac) by rw [← c.2.2.2.1]; exact h.1)
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le he)
    · exact shellHigherPrimePower_depth_injective n
  simpa only [Finset.card_range] using hc

/-- Finite depth-by-base certificates discharge the complete event carrier. -/
theorem shellHigherPrimePowerEvents_eq_empty_of_bases_empty (n : ℕ)
    (h : ∀ a ∈ Finset.Icc 3 (Nat.log 2 ((n + 1) ^ 2)),
      shellPrimePowerBasesAtExponent n a = ∅) : shellHigherPrimePowerEvents n = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hq
  have e := mem_shellHigherPrimePowerEvents.mp hq
  have c := shell_higher_primePower_canonical e.1 e.2.1 e.2.2
  have hc : SquareCell n (q.minFac ^ q.factorization q.minFac) := by
    rw [← c.2.2.2.1]; exact e.1
  have hcut := squareCell_prime_power_exponent_le_log c.1 hc
  have hm := mem_shellPrimePowerBasesAtExponent.mpr ⟨c.1, c.2.2.2.2.1, hc⟩
  rw [h _ (Finset.mem_Icc.mpr ⟨c.2.1, hcut⟩)] at hm
  exact Finset.notMem_empty _ hm

/-- A cube cutoff and finite base/depth check certify absence of higher events. -/
theorem shellHigherPrimePowerEvents_eq_empty_of_bounded_exclusion (n B : ℕ)
    (hcut : (n + 1) ^ 2 ≤ (B + 1) ^ 3)
    (hex : ∀ p ∈ Nat.primesLE B, ∀ a ∈ Finset.Icc 3 (Nat.log 2 ((n + 1) ^ 2)),
      ¬ SquareCell n (p ^ a)) : shellHigherPrimePowerEvents n = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hq
  have e := mem_shellHigherPrimePowerEvents.mp hq
  have c := shell_higher_primePower_canonical e.1 e.2.1 e.2.2
  have hc : SquareCell n (q.minFac ^ q.factorization q.minFac) := by
    rw [← c.2.2.2.1]; exact e.1
  have hb : q.minFac ≤ B := by
    by_contra h
    have hpow := Nat.pow_le_pow_left (show B + 1 ≤ q.minFac by omega) 3
    exact (not_lt_of_ge (hcut.trans hpow)) c.2.2.2.2.2
  exact hex _ (Nat.mem_primesLE.mpr ⟨hb, c.1⟩) _
    (Finset.mem_Icc.mpr ⟨c.2.1, squareCell_prime_power_exponent_le_log c.1 hc⟩) hc

/-- The full gnomon top row is not a global prime-power boundary.
This says nothing by itself about a fresh factor in a selected Pascal cell. -/
theorem gnomon_top_not_isPrimePow {n : ℕ} (hn : 3 ≤ n) :
    ¬ IsPrimePow (n * (n + 2)) := by
  intro h
  let p := (n * (n + 2)).minFac
  have hp : Nat.Prime p := Nat.minFac_prime h.ne_one
  have he : p ^ (n * (n + 2)).factorization p = n * (n + 2) :=
    h.minFac_pow_factorization_eq
  have dn : n ∣ p ^ (n * (n + 2)).factorization p := by
    rw [he]; exact dvd_mul_right n (n + 2)
  have dn2 : n + 2 ∣ p ^ (n * (n + 2)).factorization p := by
    rw [he]; exact dvd_mul_left (n + 2) n
  obtain ⟨a, _, ea⟩ := (Nat.dvd_prime_pow hp).mp dn
  obtain ⟨b, _, eb⟩ := (Nat.dvd_prime_pow hp).mp dn2
  have ha : a ≠ 0 := by intro hz; rw [hz] at ea; simp only [pow_zero] at ea; omega
  have hb : b ≠ 0 := by intro hz; rw [hz] at eb; simp only [pow_zero] at eb; omega
  have dpn : p ∣ n := by rw [ea]; exact dvd_pow_self p ha
  have dpn2 : p ∣ n + 2 := by rw [eb]; exact dvd_pow_self p hb
  have dp2 : p ∣ 2 := (Nat.dvd_add_iff_right dpn).mpr dpn2
  have ep : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp dp2
  rw [ep] at ea eb
  have ha2 : 2 ≤ a := by
    by_contra hlt
    have : a ≤ 1 := by omega
    interval_cases a <;> norm_num at ea <;> omega
  have hb2 : 2 ≤ b := by
    by_contra hlt
    have : b ≤ 1 := by omega
    interval_cases b <;> norm_num at eb
    all_goals omega
  have d4n : 4 ∣ n := by rw [ea]; exact pow_dvd_pow 2 ha2
  have d4n2 : 4 ∣ n + 2 := by rw [eb]; exact pow_dvd_pow 2 hb2
  have : 4 ∣ 2 := (Nat.dvd_add_iff_right d4n).mpr d4n2
  norm_num at this

end DkMath.NumberTheory.Legendre
