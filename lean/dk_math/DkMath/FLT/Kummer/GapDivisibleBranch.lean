/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.Basic

#print "file: DkMath.FLT.Kummer.GapDivisibleBranch"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

open DkMath.CosmicFormulaBinom

/-!
# Gap-Divisible Branch の Isolate

## 背景

`2m-global` と `2m-pure` の formal gap を解析した結果、
gap-divisible branch（`q | (z-y)` かつ `q ≠ p`）が
genuinely global な open content の源泉であることが判明した。

このモジュールは `2m-pure` を 2 つの branch に分離する:

1. **Regular branch** (`q ∤ (z-y)`):
   CyclotomicExistence が `¬ q ∣ (z-y)` を保証する actual DescentChain path。
   このケースでは witness R の Φ_p(R) = 0 が自動充足されるため、
   `2m-global` が直接使える。

2. **Gap-divisible branch** (`q | (z-y)`, `q ≠ p`):
   `2m-global` が vacuously true になるケース。
   ここが Kummer 的 principalization の本線。

## 分離の構造

```
2m-pure = Regular branch ∧ Gap-divisible branch
         ↑ concrete path     ↑ Kummer territory
```
-/

namespace DkMath.FLT

/-!
## §1. Regular branch target

`q ∤ (z-y)` の場合。DescentChain の actual path はこちら。
`2m-global` の witness 条件が自動充足されるため、
`2m-global` から直接閉じる。
-/

/--
Regular branch: `q ∤ (z-y)` の場合の descent existence。

CyclotomicExistence が保証する actual path ではこちらが使われる。
`2m-global` の witness R は `q ∤ (z-y)` のとき Φ_p(R) = 0 が自動なので、
`2m-global` から直接供給できる。
-/
abbrev PrimeGe5BranchAPrimitiveQAdicGapReductionRegularBranchTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ x →
      ¬ q ∣ (z - y) →
      ∃ g' : ℕ, g' * GN p g' y = (x / q) ^ p

/-!
## §2. Gap-divisible branch target

`q | (z-y)` かつ `q ≠ p` の場合。
`2m-global` が vacuously true（Φ_p(R) = 0 を満たす R が存在しない）
になるケースであり、Kummer 理論が必要な本線。
-/

/--
Gap-divisible branch: `q | (z-y)` かつ `q ≠ p` の場合の descent existence。

このケースでは:
- R = z · y⁻¹ ≡ 1 (mod q) なので Φ_p(R) ≡ p ≢ 0 (mod q) when q ≠ p
- `2m-global` は vacuously true（witness 条件を満たす R が存在しない）
- descent existence を示すには Kummer 的 principalization が必要

数論的意味:
- `q | (z-y)` かつ `q | x` なので `v_q(x^p) = v_q(gap · GN) = v_q(gap)`
  （∵ q ≠ p, q ∤ y → q ∤ GN）
- よって `q^p | gap`（∵ v_q(x^p) ≥ p）
- `(x/q)^p = (gap/q^p) · GN(p, gap, y)` だが `GN(p, gap, y) ≠ GN(p, gap/q^p, y)`
- 単純な gap の q^p 除算では descent existence にならない
-/
abbrev PrimeGe5BranchAPrimitiveQAdicGapReductionGapDivisibleBranchTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ x →
      q ≠ p →
      q ∣ (z - y) →
      ∃ g' : ℕ, g' * GN p g' y = (x / q) ^ p

/-!
## §3. 分離橋: Regular + GapDivisible → 2m-pure

2 つの branch を合成すると `2m-pure` が得られる。
ただし `q = p` かつ `q | (z-y)` のケースも処理する必要がある。
（このケースは peel 側 / p | gap の territory だが、
 pack の構造から `p | x → p | (z-y)` であるかは文脈依存。）

設計選択: まず `q ≠ p` のケースのみを gap-divisible branch に入れ、
`q = p` は別途処理する。
-/

/--
`q ≠ p` のケースで、Regular + GapDivisible → ∃ g'。
`q | (z-y)` かどうかで場合分けする。
-/
theorem qAdicGapReduction_qNeP_of_regularAndGapDivisible
    (hReg : PrimeGe5BranchAPrimitiveQAdicGapReductionRegularBranchTarget)
    (hGap : PrimeGe5BranchAPrimitiveQAdicGapReductionGapDivisibleBranchTarget) :
    ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
      ∀ {q : ℕ}, Nat.Prime q →
        q ∣ x →
        q ≠ p →
        ∃ g' : ℕ, g' * GN p g' y = (x / q) ^ p := by
  intro p x y z hpack q hq hq_dvd_x hq_ne_p
  by_cases hgap : q ∣ (z - y)
  · exact hGap hpack hq hq_dvd_x hq_ne_p hgap
  · exact hReg hpack hq hq_dvd_x hgap

/-!
## §4. Regular branch は `2m-global` から閉じる

actual DescentChain path では `CyclotomicExistenceTarget` が q を選ぶ際に
`¬ q ∣ (z-y)` を保証する。このケースでは witness R の
Φ_p(R) = 0 が自動充足されるので、`2m-global` → regular branch は直結。

証明の代数的骨格:
1. pack の `Coprime x y` + `q ∣ x` → `¬ q ∣ y` → y は ZMod(q^p) で可逆
2. R := z · y⁻¹ in ZMod(q^p), z = R · y は定義
3. q^p ∣ x^p (∵ q ∣ x) → z^p ≡ y^p (mod q^p) → R^p = 1
4. `¬ q ∣ (z-y)` → z - y ≡ (R-1)·y (mod q^p) → R - 1 ≢ 0 (mod q)
   → gcd(R-1, q) = 1 → gcd(R-1, q^p) = 1 → R - 1 は ZMod(q^p) で可逆
5. `geom_sum_mul`: (R-1) · Φ_p(R) = R^p - 1 = 0, R-1 可逆 → Φ_p(R) = 0
6. hGlobal に R, Φ_p(R) = 0, z = R·y を渡す
-/

/--
純代数補題: R^p = 1 かつ IsUnit(R - 1) → ∑_{i < p} R^i = 0。

`geom_sum_mul` の帰結。
-/
private theorem geom_sum_eq_zero_of_pow_eq_one_of_sub_one_isUnit
    {n : ℕ} {R : ZMod n} {p : ℕ}
    (hRp : R ^ p = 1)
    (hUnit : IsUnit (R - 1)) :
    ∑ i ∈ Finset.range p, R ^ i = 0 := by
  have hGeom := geom_sum_mul R p
  rw [hRp, sub_self] at hGeom
  rwa [mul_comm, IsUnit.mul_right_eq_zero hUnit] at hGeom

/-
`q ∤ (z-y)` のとき witness R を自動構成して `2m-global` に渡す。

証明戦略:
1. Coprime x y + q|x → gcd(y,q) = 1 → y は ZMod(q^p) の unit
2. R := z · y⁻¹
3. z^p ≡ y^p mod q^p → R^p = 1
4. q ∤ (z-y) → R-1 は unit
5. geom_sum_eq_zero... で Φ_p(R) = 0
6. hGlobal に渡す

各 step は individually straightforward だが、
ZMod の nat cast / unit lifting の formal 化が detailed。
-/

/--
補助: z * ↑u⁻¹ - 1 = (z - ↑u) * ↑u⁻¹ in ZMod (unit 分解)。
-/
private lemma sub_one_eq_sub_mul_inv {n : ℕ} (z : ZMod n) (u : (ZMod n)ˣ) :
    z * (↑u⁻¹ : ZMod n) - 1 = (z - ↑u) * (↑u⁻¹ : ZMod n) := by
  calc z * ↑u⁻¹ - 1
      = z * ↑u⁻¹ - ↑u * ↑u⁻¹ := by rw [Units.mul_inv u]
    _ = (z - ↑u) * ↑u⁻¹ := by ring

/--
補助: z^p = ↑u^p → (z * ↑u⁻¹)^p = 1 in ZMod (unit べき消去)。
-/
private lemma pow_mul_unit_inv_eq_one {n p : ℕ} (z : ZMod n) (u : (ZMod n)ˣ)
    (heq : z ^ p = (↑u : ZMod n) ^ p) :
    (z * (↑u⁻¹ : ZMod n)) ^ p = 1 := by
  rw [mul_pow]
  conv_lhs => rw [heq]
  rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val]
  rw [← Units.val_mul]
  simp only [inv_pow, mul_inv_cancel, Units.val_one]

/--
補助: x^p+y^p=z^p かつ q ∣ x → z^p = y^p in ZMod(q^p)。
-/
private lemma zpow_eq_ypow_zmod {x y z q p : ℕ}
    (hEq : x ^ p + y ^ p = z ^ p) (hyz : y ≤ z) (hqx : q ∣ x) :
    (z : ZMod (q ^ p)) ^ p = (y : ZMod (q ^ p)) ^ p := by
  have hle : y ^ p ≤ z ^ p := Nat.pow_le_pow_left hyz p
  have hzp_sub : z ^ p - y ^ p = x ^ p := by omega
  have hqp_dvd : q ^ p ∣ (z ^ p - y ^ p) := by
    rw [hzp_sub]; exact pow_dvd_pow_of_dvd hqx p
  have hmod : ((z ^ p - y ^ p : ℕ) : ZMod (q ^ p)) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hqp_dvd
  have hsplit : (z ^ p : ℕ) = y ^ p + (z ^ p - y ^ p) := (Nat.add_sub_cancel' hle).symm
  have key : ((z ^ p : ℕ) : ZMod (q ^ p)) = ((y ^ p : ℕ) : ZMod (q ^ p)) := by
    conv_lhs => rw [hsplit, Nat.cast_add, hmod, add_zero]
  exact_mod_cast key

/--
補助: ¬ q ∣ (z-y) → IsUnit ((z : ZMod(q^p)) - (y : ZMod(q^p)))。
-/
private lemma isUnit_sub_of_not_dvd_gap {z y q p : ℕ} (hq : Nat.Prime q) (hyz : y ≤ z)
    (hgap : ¬ q ∣ (z - y)) :
    IsUnit ((z : ZMod (q ^ p)) - (y : ZMod (q ^ p))) := by
  rw [show (z : ZMod (q ^ p)) - (y : ZMod (q ^ p)) = ((z - y : ℕ) : ZMod (q ^ p))
      from (Nat.cast_sub hyz).symm]
  rw [ZMod.isUnit_iff_coprime]
  exact Nat.Coprime.pow_right p ((hq.coprime_iff_not_dvd.mpr hgap).symm)

theorem qAdicGapReductionRegularBranch_of_global
    (hGlobal : PrimeGe5BranchAPrimitiveQAdicGapReductionGlobalTarget) :
    PrimeGe5BranchAPrimitiveQAdicGapReductionRegularBranchTarget := by
  intro p x y z hpack q hq hq_dvd_x hq_not_dvd_gap
  -- Step 1: y coprime to q → y is a unit in ZMod(q^p)
  have hq_not_dvd_y : ¬ q ∣ y := by
    intro hqy
    exact Nat.not_coprime_of_dvd_of_dvd (Nat.Prime.one_lt hq) hq_dvd_x hqy hpack.hxy
  have hy_coprime_qp : Nat.Coprime y (q ^ p) :=
    Nat.Coprime.pow_right p ((hq.coprime_iff_not_dvd.mpr hq_not_dvd_y).symm)
  -- y as a unit
  let u : (ZMod (q ^ p))ˣ := ZMod.unitOfCoprime y hy_coprime_qp
  have hu_val : (u : ZMod (q ^ p)) = (y : ZMod (q ^ p)) := ZMod.coe_unitOfCoprime y hy_coprime_qp
  -- Step 2: R := z · y⁻¹ in ZMod(q^p)
  let R : ZMod (q ^ p) := (z : ZMod (q ^ p)) * (↑u⁻¹ : ZMod (q ^ p))
  -- Step 3: z^p = y^p in ZMod(q^p) → R^p = 1
  have hzp_eq : (z : ZMod (q ^ p)) ^ p = (y : ZMod (q ^ p)) ^ p :=
    zpow_eq_ypow_zmod hpack.hEq hpack.hyz hq_dvd_x
  rw [← hu_val] at hzp_eq
  have hRp : R ^ p = 1 := pow_mul_unit_inv_eq_one _ u hzp_eq
  -- Step 4: q ∤ (z-y) → IsUnit (R - 1)
  have hzy_unit : IsUnit ((z : ZMod (q ^ p)) - (y : ZMod (q ^ p))) :=
    isUnit_sub_of_not_dvd_gap hq hpack.hyz hq_not_dvd_gap
  rw [← hu_val] at hzy_unit
  have hR_sub_unit : IsUnit (R - 1) := by
    change IsUnit ((z : ZMod (q ^ p)) * ↑u⁻¹ - 1)
    rw [sub_one_eq_sub_mul_inv]
    exact IsUnit.mul hzy_unit (Units.isUnit u⁻¹)
  -- Step 5: Φ_p(R) = 0
  have hPhi : ∑ i ∈ Finset.range p, R ^ i = 0 :=
    geom_sum_eq_zero_of_pow_eq_one_of_sub_one_isUnit hRp hR_sub_unit
  -- Step 6: z = R · y in ZMod(q^p) (by definition of R)
  have hz_eq : (z : ZMod (q ^ p)) = R * (y : ZMod (q ^ p)) := by
    change (z : ZMod (q ^ p)) = (z : ZMod (q ^ p)) * ↑u⁻¹ * (y : ZMod (q ^ p))
    rw [← hu_val, mul_assoc, Units.inv_mul, mul_one]
  -- Apply hGlobal
  exact hGlobal hpack hq hq_dvd_x hPhi hz_eq

end DkMath.FLT
