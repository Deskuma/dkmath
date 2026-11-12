/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from P2M/Sol/S_ValuationSubring_exists_tame_generator_inertiaSubgroupIn.lean,
commit 115356cbc627159d0d16add0da6e9a2bb3655ed8.
Modified: actual DkMath inertia/unit-power rigidity and named unit-valued characters.
-/

import DkMath.Lib.NumberTheory.PrimeRadicalTower
import DkMath.Lib.NumberTheory.ValuationInertiaPower

#print "file: DkMath.Lib.NumberTheory.InertiaRadicalCharacter"

/-!
# 同じ q の根の塔に作用する実際の慣性 Kummer 指標

q 上の慣性は全ての p 冪根の1を固定する。従って根の作用比は交差準同型でなく
通常の単元値準同型となる。p≠q と元の付値環を保持する。
-/
namespace DkMath.Lib.NumberTheory.InertiaRadical
open ValuationInertia PrimeRadicalTower
noncomputable section
variable {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)

/-- 同じ有理素数 q を基点とする、実際の互換な根。 -/
abbrev radical (p q : ℕ) (hp : p.Prime) : ℕ → AlgebraicClosure ℚ := tower p hp.pos (q : AlgebraicClosure ℚ)

/-- 同じ根に対する作用比。 -/
def ratio (base : ℕ) (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (n : ℕ) : AlgebraicClosure ℚ :=
  σ (radical p base hp n) / radical p base hp n

include hq in
/-- 根の非零性は q の素数性から供給する。 -/
theorem radical_ne_zero (n : ℕ) : radical p q hp n ≠ 0 :=
  tower_ne_zero p hp.pos (q : AlgebraicClosure ℚ) (Nat.cast_ne_zero.mpr hq.ne_zero) n

include hq in
/-- 任意の Galois 元の作用比は p^n 乗根の1。 -/
theorem ratio_pow (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (n : ℕ) : ratio hp q σ n ^ (p ^ n) = 1 := by
  rw [ratio, div_pow, ← map_pow, tower_pow, map_natCast, div_self (Nat.cast_ne_zero.mpr hq.ne_zero)]

/-- 同じ作用比の段間互換性。 -/
theorem ratio_compat (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (n d : ℕ) :
    ratio hp q σ (n + d) ^ (p ^ d) = ratio hp q σ n := by
  rw [ratio, div_pow, ← map_pow, tower_compat]
  rfl

include hq in
/-- 比が1であることと、元の同じ根を固定することは同値。 -/
theorem ratio_eq_one_iff (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (n : ℕ) :
    ratio hp q σ n = 1 ↔ σ (radical p q hp n) = radical p q hp n :=
  div_eq_one_iff_eq (radical_ne_zero hp hq n)

include hp hq hpq hA in
/-- 実際の q 上の付値環で p は単元。 -/
theorem valuation_prime_eq_one : A.valuation (p : AlgebraicClosure ℚ) = 1 := by
  apply ValuationPrimeSupport.valuation_intCast_eq_one_of_not_dvd A hq
    ((ValuationSubring.mem_nonunits_iff A).mp hA) (z := (p : ℤ))
  intro hd
  rcases (Nat.dvd_prime hp).mp (Int.natCast_dvd_natCast.mp hd) with he | he
  · exact hq.ne_one he
  · exact hpq he.symm

include hp hq hpq hA in
/-- 全 p 冪根の1は、同じ実際の慣性群に固定される。 -/
theorem inertia_fixes_primePower_root (σ : inertiaSubgroupIn A ℚ) (n : ℕ)
    (z : AlgebraicClosure ℚ) (hz : z ^ (p ^ n) = 1) : σ.val z = z := by
  apply ValuationInertiaPower.inertia_fixed_of_pow_eq_one A ℚ (pow_ne_zero n hp.ne_zero)
    (n := p ^ n) ?_ σ.val σ.property hz
  rw [Nat.cast_pow, map_pow, valuation_prime_eq_one hp hq hpq A hA, one_pow]

/-- 根の作用比を値とする、実際の単元値慣性準同型。 -/
def character (n : ℕ) : inertiaSubgroupIn A ℚ →* (AlgebraicClosure ℚ)ˣ where
  toFun σ := Units.mk0 (ratio hp q σ.val n)
    (div_ne_zero (by
      intro hz
      apply radical_ne_zero hp hq n
      exact σ.val.injective (hz.trans (map_zero σ.val).symm)) (radical_ne_zero hp hq n))
  map_one' := by
    apply Units.ext
    change radical p q hp n / radical p q hp n = 1
    exact div_self (radical_ne_zero hp hq n)
  map_mul' σ τ := by
    apply Units.ext
    change σ.val (τ.val (radical p q hp n)) / radical p q hp n = ratio hp q σ.val n * ratio hp q τ.val n
    have hf := inertia_fixes_primePower_root hp hq hpq A hA σ n _ (ratio_pow hp hq τ.val n)
    have he : τ.val (radical p q hp n) = ratio hp q τ.val n * radical p q hp n :=
      (div_mul_cancel₀ _ (radical_ne_zero hp hq n)).symm
    rw [he, map_mul, hf, mul_div_assoc, mul_comm]
    rfl

/-- 単元として保持しても、元の同じ作用比を回収する。 -/
theorem character_val (n : ℕ) (σ : inertiaSubgroupIn A ℚ) :
    (character hp hq hpq A hA n σ : AlgebraicClosure ℚ) = ratio hp q σ.val n := rfl

/-- 同じ慣性指標の全ての値は、元の p^n 乗で1になる。 -/
theorem character_pow (n : ℕ) (σ : inertiaSubgroupIn A ℚ) :
    (character hp hq hpq A hA n σ : AlgebraicClosure ℚ) ^ (p ^ n) = 1 := ratio_pow hp hq σ.val n

/-- 同じ慣性指標の段間互換性を単元の中で保持する。 -/
theorem character_compat (n d : ℕ) (σ : inertiaSubgroupIn A ℚ) :
    character hp hq hpq A hA (n + d) σ ^ (p ^ d) = character hp hq hpq A hA n σ := by
  apply Units.ext
  exact ratio_compat hp σ.val n d

end
end DkMath.Lib.NumberTheory.InertiaRadical
