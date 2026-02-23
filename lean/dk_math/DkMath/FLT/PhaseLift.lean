/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PetalDetect

namespace DkMath.FLT

open DkMath.FLT.PetalDetect

/--
`S0_nat c b` の素因子が二乗で刺さらないことをまとめた条件。
-/
def NoSqOnS0 (c b : ℕ) : Prop :=
  ∀ {q : ℕ}, Nat.Prime q → q ∣ S0_nat c b → ¬ q ^ 2 ∣ S0_nat c b

/--
`q ∣ (c^3-b^3)` かつ `q ∤ (c-b)` なら `q ∣ S0_nat c b`。
-/
lemma prime_dvd_S0_of_dvd_cube_sub_not_dvd_diff {c b q : ℕ}
    (hbc : b < c)
    (hq : Nat.Prime q)
    (hq_dvd : q ∣ c ^ 3 - b ^ 3)
    (hq_ndvd : ¬ q ∣ c - b) :
    q ∣ S0_nat c b := by
  have hdiff : c ^ 3 - b ^ 3 = (c - b) * (c ^ 2 + c * b + b ^ 2) := by
    have h_pow : b ^ 3 ≤ c ^ 3 := Nat.pow_le_pow_left hbc.le 3
    zify [hbc, h_pow]
    ring_nf
  have hfact : c ^ 3 - b ^ 3 = (c - b) * S0_nat c b := by
    simpa [S0_nat] using hdiff
  have hmul : q ∣ (c - b) * S0_nat c b := by
    simpa [hfact] using hq_dvd
  exact (hq.dvd_mul.mp hmul).resolve_left hq_ndvd

/--
`NoSqOnS0 c b` から `Main` で使う `hS0_not_sq` 形の仮定を作るブリッジ。
-/
lemma hS0_not_sq_of_NoSqOnS0 {c b : ℕ}
    (hNoSq : NoSqOnS0 c b) :
    ∀ {q : ℕ}, Nat.Prime q → q ∣ c ^ 3 - b ^ 3 → ¬ q ∣ c - b → ¬ q ^ 2 ∣ S0_nat c b := by
  intro q hq hq_dvd hq_ndvd
  have hbc : b < c := by
    by_contra hbc_not
    have hcb : c ≤ b := Nat.not_lt.mp hbc_not
    have hdiff_zero : c - b = 0 := Nat.sub_eq_zero_of_le hcb
    exact hq_ndvd (hdiff_zero ▸ dvd_zero q)
  have hqS0 : q ∣ S0_nat c b :=
    prime_dvd_S0_of_dvd_cube_sub_not_dvd_diff hbc hq hq_dvd hq_ndvd
  exact hNoSq hq hqS0

end DkMath.FLT
