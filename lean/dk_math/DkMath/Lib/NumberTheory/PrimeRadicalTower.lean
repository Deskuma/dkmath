/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from P2M/Sol/S_ValuationSubring_exists_tame_generator_inertiaSubgroupIn.lean,
commit 115356cbc627159d0d16add0da6e9a2bb3655ed8.
Modified: named compatible radical tower, arbitrary algebraically closed fields.
-/

import Mathlib.FieldTheory.IsAlgClosed.Basic

#print "file: DkMath.Lib.NumberTheory.PrimeRadicalTower"

/-!
# 実際に構成した互換な p 冪根の塔

根の存在を provider にせず、代数閉性から各次段を選ぶ。同じ塔の全段を保つ。
-/
namespace DkMath.Lib.NumberTheory.PrimeRadicalTower
noncomputable section
variable {L : Type*} [Field L] [IsAlgClosed L] (p : ℕ) (hp : 0 < p) (a : L)

/-- 代数閉性から逐次選ぶ、同じ基点 a の p 冪根の塔。 -/
def tower : ℕ → L := Nat.rec a (fun _ b => Classical.choose (IsAlgClosed.exists_pow_nat_eq b hp))

/-- 第0段は元の同じ基点。 -/
theorem tower_zero : tower p hp a 0 = a := rfl

/-- 各次段の p 乗は前段そのもの。 -/
theorem tower_succ_pow (n : ℕ) : tower p hp a (n + 1) ^ p = tower p hp a n :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (tower p hp a n) hp)

/-- 任意の二段の互換性。 -/
theorem tower_compat (n d : ℕ) : tower p hp a (n + d) ^ (p ^ d) = tower p hp a n := by
  induction d with
  | zero => rw [pow_zero, pow_one, Nat.add_zero]
  | succ d ih =>
    rw [pow_succ', pow_mul]
    change (tower p hp a (n + d + 1) ^ p) ^ (p ^ d) = _
    rw [tower_succ_pow, ih]

/-- 各段は元の同じ基点の p^n 乗根。 -/
theorem tower_pow (n : ℕ) : tower p hp a n ^ (p ^ n) = a := by
  simpa only [Nat.zero_add, tower_zero] using tower_compat p hp a 0 n

/-- 基点が非零なら、実際の塔の全段も非零。 -/
theorem tower_ne_zero (ha : a ≠ 0) (n : ℕ) : tower p hp a n ≠ 0 := by
  intro hz
  apply ha
  rw [← tower_pow p hp a n, hz, zero_pow (pow_ne_zero n hp.ne')]

end
end DkMath.Lib.NumberTheory.PrimeRadicalTower
