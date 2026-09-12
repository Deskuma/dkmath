/-
Copyright (c) 2026 DkMath contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: DkMath contributors.
-/
import DkMath.NumberTheory.GNPrimeTargetResidue
import DkMath.NumberTheory.Goldbach.Basic

/-! # Two unit-boundary cosmic formulas

The sum of two Bodies is the Goldbach target. The additive conservation
law holds independently of primality. Allowing arbitrary prime degrees
includes degree two on both sides, hence includes all odd prime pairs.
-/

namespace DkMath.NumberTheory.GoldbachPairGN

open DkMath.CosmicFormulaBinom

def pairBig (d e u v : ℕ) : ℕ := (1 + u) ^ d + (1 + v) ^ e
def pairGap (d e u v : ℕ) : ℕ := u ^ d + v ^ e
def pairBody (d e u v : ℕ) : ℕ := GN d 1 u + GN e 1 v

theorem pairBody_add_pairGap (d e u v : ℕ) :
    pairBody d e u v + pairGap d e u v = pairBig d e u v := by
  have hl := DkMath.CosmicFormula.add_pow_eq_mul_GTail_one_add_gap (R := ℕ) d 1 u
  have hr := DkMath.CosmicFormula.add_pow_eq_mul_GTail_one_add_gap (R := ℕ) e 1 v
  change (1 + u) ^ d = 1 * GN d 1 u + u ^ d at hl
  change (1 + v) ^ e = 1 * GN e 1 v + v ^ e at hr
  simp only [one_mul] at hl hr
  unfold pairBody pairGap pairBig
  omega

theorem pairBig_sub_pairGap (d e u v : ℕ) :
    pairBig d e u v - pairGap d e u v = pairBody d e u v := by
  have h := pairBody_add_pairGap d e u v
  omega

/-- The complement in a single unit-boundary universe is a pure power. -/
theorem singleBig_sub_GN (d u : ℕ) : (1 + u) ^ d - GN d 1 u = u ^ d := by
  have h := cosmic_id_csr' (R := ℕ) d 1 u
  simp only [one_mul] at h
  omega

theorem single_complement_not_prime {d : ℕ} (hd : 2 ≤ d) (u : ℕ) :
    ¬ Nat.Prime ((1 + u) ^ d - GN d 1 u) := by
  rw [singleBig_sub_GN]
  exact Nat.Prime.not_prime_pow hd

/-- Package the existing necessary degree and residue filters without a converse. -/
theorem prime_unitGN_constraints {d u : ℕ} (hd : 2 ≤ d) (hu : 0 < u)
    (hp : Nat.Prime (GN d 1 u)) :
    Nat.Prime d ∧ d ∣ GN d 1 u - 1 ∧ d < GN d 1 u := by
  have hrep : GNPositiveRepresentation (GN d 1 u) d 1 u := ⟨hd, by omega, hu, rfl⟩
  exact ⟨hrep.degree_prime_of_target_prime hp,
    hrep.degree_dvd_target_sub_one_of_target_prime hp, hrep.bounds.2.2.2.1⟩

/-- A prime degree has an exact nonnegative Beam quotient at unit boundary. -/
theorem prime_unitGN_quotient {d : ℕ} (hd : Nat.Prime d) (u : ℕ) :
    ∃ A : ℕ, GN d 1 u = 1 + d * A := by
  obtain ⟨A, hA⟩ := prime_exists_GN_eq_mul_add_rightBoundary (x := 1) (u := u) hd
  exact ⟨A, by simpa [add_comm] using hA⟩

/-- This equivalence retains the two polynomial representation equations.
The linear equation alone is weaker. No primality is needed for the outputs. -/
theorem pairBody_eq_iff_weighted_quotients {d e : ℕ}
    (hd : Nat.Prime d) (he : Nat.Prime e) {n u v : ℕ} (hn : 1 ≤ n) :
    pairBody d e u v = 2 * n ↔
      ∃ A B : ℕ, GN d 1 u = 1 + d * A ∧ GN e 1 v = 1 + e * B ∧
        d * A + e * B = 2 * (n - 1) := by
  obtain ⟨A, hA⟩ := prime_unitGN_quotient hd u
  obtain ⟨B, hB⟩ := prime_unitGN_quotient he v
  constructor
  · intro h
    refine ⟨A, B, hA, hB, ?_⟩
    unfold pairBody at h
    omega
  · rintro ⟨A', B', hA', hB', hsum⟩
    unfold pairBody
    omega

/-- Positive parameters, with primality of both outputs explicitly required. -/
def UnitPairAt (n d e : ℕ) : Prop :=
  ∃ u v : ℕ, 0 < u ∧ 0 < v ∧ Nat.Prime (GN d 1 u) ∧ Nat.Prime (GN e 1 v) ∧
    pairBody d e u v = 2 * n

theorem unitPairAt_swap (n d e : ℕ) : UnitPairAt n d e ↔ UnitPairAt n e d := by
  have swap : ∀ a b : ℕ, UnitPairAt n a b → UnitPairAt n b a := by
    intro a b
    rintro ⟨u, v, hu, hv, hp, hq, hsum⟩
    refine ⟨v, u, hv, hu, hq, hp, ?_⟩
    change GN b 1 v + GN a 1 u = 2 * n
    rw [Nat.add_comm]
    exact hsum
  exact ⟨swap d e, swap e d⟩

/-- The combined Big is strictly greater than its combined Body in the positive region. -/
theorem pairBody_lt_pairBig {d e u v : ℕ} (hu : 0 < u) (hv : 0 < v) :
    pairBody d e u v < pairBig d e u v := by
  have h := pairBody_add_pairGap d e u v
  have hgap : 0 < pairGap d e u v := add_pos (Nat.pow_pos hu) (Nat.pow_pos hv)
  omega

theorem goldbachPairAt_of_unitPairAt {n d e : ℕ} (h : UnitPairAt n d e) :
    GoldbachPairAt n := by
  obtain ⟨u, v, _, _, hp, hq, hsum⟩ := h
  exact ⟨GN d 1 u, GN e 1 v, hp, hq, hsum⟩

/-- Every odd prime is represented in the degree-two unit row. -/
theorem exists_unitGN_two_of_odd_prime {p : ℕ} (hp : Nat.Prime p) (hodd : p % 2 = 1) :
    ∃ u : ℕ, 0 < u ∧ GN 2 1 u = p := by
  refine ⟨p / 2, ?_, ?_⟩
  · have := hp.two_le
    omega
  · rw [goldbach_GN_two]
    omega

/-- At centers above two, both members of any prime pair are odd. -/
theorem prime_pair_odd {n p q : ℕ} (hn : 3 ≤ n)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hsum : p + q = 2 * n) :
    p % 2 = 1 ∧ q % 2 = 1 := by
  rcases hp.eq_two_or_odd with hp2 | hpodd <;>
    rcases hq.eq_two_or_odd with hq2 | hqodd <;> omega

theorem goldbachPairAt_iff_unitPairAt_two_two {n : ℕ} (hn : 3 ≤ n) :
    GoldbachPairAt n ↔ UnitPairAt n 2 2 := by
  constructor
  · rintro ⟨p, q, hp, hq, hsum⟩
    obtain ⟨hpodd, hqodd⟩ := prime_pair_odd hn hp hq hsum
    obtain ⟨u, hu, heqp⟩ := exists_unitGN_two_of_odd_prime hp hpodd
    obtain ⟨v, hv, heqq⟩ := exists_unitGN_two_of_odd_prime hq hqodd
    exact ⟨u, v, hu, hv, heqp.symm ▸ hp, heqq.symm ▸ hq,
      by change GN 2 1 u + GN 2 1 v = 2 * n; rw [heqp, heqq]; exact hsum⟩
  · exact goldbachPairAt_of_unitPairAt

/-- Arbitrary prime degrees do not strengthen the existence criterion:
the two degree-two rows already represent every odd prime pair. -/
theorem exists_prime_degrees_iff_goldbach {n : ℕ} (hn : 3 ≤ n) :
    (∃ d e : ℕ, Nat.Prime d ∧ Nat.Prime e ∧ UnitPairAt n d e) ↔ GoldbachPairAt n := by
  constructor
  · rintro ⟨d, e, _, _, h⟩
    exact goldbachPairAt_of_unitPairAt h
  · intro h
    exact ⟨2, 2, Nat.prime_two, Nat.prime_two,
      (goldbachPairAt_iff_unitPairAt_two_two hn).mp h⟩

/-- Restore the exceptional 2+2 target explicitly in the universal equivalence. -/
theorem strongGoldbach_iff_unitPairAt_two_two :
    StrongGoldbach ↔ ∀ n : ℕ, 3 ≤ n → UnitPairAt n 2 2 := by
  constructor
  · intro h n hn
    exact (goldbachPairAt_iff_unitPairAt_two_two hn).mp (h n (by omega))
  · intro h n hn
    by_cases hn2 : n = 2
    · subst n
      exact ⟨2, 2, Nat.prime_two, Nat.prime_two, by omega⟩
    · exact goldbachPairAt_of_unitPairAt (h n (by omega))

end DkMath.NumberTheory.GoldbachPairGN
