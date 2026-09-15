/-
Copyright (c) 2026 DkMath contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: DkMath contributors.
-/
import DkMath.NumberTheory.FixedBigGauge.SquareCertificate
import DkMath.NumberTheory.Goldbach.Capacity

/-! # Fixed physical edge versus fixed natural Goldbach center

Changing resolution changes the sum required of the natural prime labels.
At the original resolution the gauge criterion is exactly the existing
Goldbach criterion. No universal survivor is assumed or constructed here.
-/

namespace DkMath.NumberTheory.FixedBigGauge

noncomputable section

/-- Prime labels whose physical lengths sum to twice the fixed edge. -/
def GaugePrimePairAt (R : ℝ) (k : ℕ) : Prop :=
  ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧
    ((p : ℝ) + (q : ℝ)) * fixedBigUnit R k = 2 * R

theorem scaled_sum_eq_iff {R a b : ℝ} {k : ℕ}
    (hR : 0 < R) (hk : 0 < k) :
    (a + b) * fixedBigUnit R k = 2 * R ↔ a + b = 2 * (k : ℝ) := by
  have hu := (fixedBigUnit_pos hR hk).ne'
  have hright : 2 * R = (2 * (k : ℝ)) * fixedBigUnit R k := by
    rw [mul_assoc, scale_unit_conservation R hk]
  rw [hright]
  exact mul_left_inj' hu

/-- A variable gauge asks Goldbach at `k`, even when the edge is `n`. -/
theorem gaugePrimePairAt_iff {R : ℝ} {k : ℕ} (hR : 0 < R) (hk : 0 < k) :
    GaugePrimePairAt R k ↔ GoldbachPairAt k := by
  constructor
  · rintro ⟨p, q, hp, hq, heq⟩
    have h := (scaled_sum_eq_iff hR hk).mp heq
    exact ⟨p, q, hp, hq, by exact_mod_cast h⟩
  · rintro ⟨p, q, hp, hq, heq⟩
    refine ⟨p, q, hp, hq, (scaled_sum_eq_iff hR hk).mpr ?_⟩
    exact_mod_cast heq

/-- Choosing some gauge is automatic: resolution two always uses labels 2+2. -/
theorem exists_gaugePrimePairAt {R : ℝ} (hR : 0 < R) :
    ∃ k : ℕ, 0 < k ∧ GaugePrimePairAt R k := by
  refine ⟨2, by omega, (gaugePrimePairAt_iff hR (by omega)).mpr ?_⟩
  exact ⟨2, 2, Nat.prime_two, Nat.prime_two, by omega⟩

/-- Preserving both the original label sum and physical edge forces `k=n`. -/
theorem resolution_eq_original_of_preserved_sum {n k p q : ℕ}
    (hn : 0 < n) (hk : 0 < k) (hsum : p + q = 2 * n)
    (hphysical : ((p : ℝ) + (q : ℝ)) * fixedBigUnit (n : ℝ) k = 2 * (n : ℝ)) :
    k = n := by
  have h := (scaled_sum_eq_iff (by exact_mod_cast hn) hk).mp hphysical
  have hnat : p + q = 2 * k := by exact_mod_cast h
  omega

theorem unit_eq_one_of_preserved_sum {n k p q : ℕ}
    (hn : 0 < n) (hk : 0 < k) (hsum : p + q = 2 * n)
    (hphysical : ((p : ℝ) + (q : ℝ)) * fixedBigUnit (n : ℝ) k = 2 * (n : ℝ)) :
    fixedBigUnit (n : ℝ) k = 1 := by
  rw [resolution_eq_original_of_preserved_sum hn hk hsum hphysical]
  exact div_self (by exact_mod_cast hn.ne')

/-- The original gauge has exactly the old finite-capacity obligation. -/
theorem original_gauge_iff_capacity {n : ℕ} (hn : 2 ≤ n) :
    GaugePrimePairAt (n : ℝ) n ↔
      (goldbachCoveredSeats n (goldbachSmallPrimes n)).card < n - 1 := by
  rw [gaugePrimePairAt_iff (by exact_mod_cast (show 0 < n by omega)) (by omega),
    goldbachPairAt_iff_covered_card_lt]

theorem strongGoldbach_iff_original_gauge :
    StrongGoldbach ↔ ∀ n : ℕ, 2 ≤ n → GaugePrimePairAt (n : ℝ) n := by
  apply forall_congr'
  intro n
  apply forall_congr'
  intro hn
  exact (gaugePrimePairAt_iff (by exact_mod_cast (show 0 < n by omega)) (by omega)).symm

/-- Multiplying a prime label by a natural scale preserves primality only at scale one. -/
theorem prime_scaled_label_iff {p c : ℕ} (hp : Nat.Prime p) :
    Nat.Prime (c * p) ↔ c = 1 := by
  simp [Nat.prime_mul_iff, hp, hp.ne_one]

/-- Positive coordinate changes preserve strict interval membership. -/
theorem scaled_lt_iff {a b s : ℝ} (hs : 0 < s) : a * s < b * s ↔ a < b :=
  mul_lt_mul_iff_left₀ hs

/-- Rescaling a child and its boundary together cannot relocate that child. -/
theorem scaled_child_in_interval_iff {R : ℝ} {k : ℕ}
    (hR : 0 < R) (hk : 0 < k) (n r j M : ℕ) :
    (r + j * M : ℕ) * fixedBigUnit R k < (n - 1 : ℕ) * fixedBigUnit R k ↔
      r + j * M < n - 1 := by
  rw [scaled_lt_iff (fixedBigUnit_pos hR hk)]
  exact_mod_cast (Iff.rfl : r + j * M < n - 1 ↔ r + j * M < n - 1)

end
end DkMath.NumberTheory.FixedBigGauge
