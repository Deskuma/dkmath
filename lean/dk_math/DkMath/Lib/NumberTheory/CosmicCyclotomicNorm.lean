/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GNPhaseFactorization
import DkMath.Lib.Cosmic.GTailCyclotomic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.NumberTheory.NumberField.Norm

#print "file: DkMath.Lib.NumberTheory.CosmicCyclotomicNorm"

/-!
# GN から円分ノルムへ

`GTail p 1 x u` は二項係数で定義された多項式である。
まず形式変数で自明な因子を除去した既存の因子分解を使い、
次に円分体の Galois 群を非零剰余類で数え直す。
これにより GN が共役因子の積、すなわち体ノルムであることを示す。
最後に整数環のノルムへ戻す。`x = 0` でも成立し、FLT 反例を仮定しない。

素数次数で全ての非自明な根が原始根になる点が重要である。
一般の切断 `GTail p r` (`r > 1`) のノルム表示は主張しない。
-/

namespace DkMath.Lib.NumberTheory

open scoped BigOperators NumberField
open DkMath.CosmicFormula DkMath.NumberTheory.GapFocusing

/-- 素数法の単元を `1, …, p-1` で数え直す。
この有限積の補題が、Galois 群によるノルムと GN の添字を接続する。 -/
theorem prod_zmod_units_eq_prod_erase_zero
    {p : ℕ} [hp : Fact p.Prime] {M : Type*} [CommMonoid M] (f : ℕ → M) :
    ∏ v : (ZMod p)ˣ, f v.val.val = ∏ j ∈ (Finset.range p).erase 0, f j := by
  let : NeZero p := ⟨hp.out.ne_zero⟩
  apply Finset.prod_nbij (fun v : (ZMod p)ˣ => v.val.val)
  · intro v _
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_range.mpr (ZMod.val_lt _)⟩
    intro h
    have hc := ZMod.val_coe_unit_coprime v
    simp only [h, Nat.Coprime, Nat.gcd_zero_left] at hc
    exact hp.out.ne_one hc
  · intro v _ w _ h
    exact Units.ext (ZMod.val_injective p h)
  · intro j hj
    have hn := (Finset.mem_erase.mp hj).1
    have hl := Finset.mem_range.mp (Finset.mem_erase.mp hj).2
    have hc : Nat.Coprime j p :=
      (hp.out.coprime_iff_not_dvd.mpr
        (fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega))).symm
    exact ⟨ZMod.unitOfCoprime j hc, Finset.mem_univ _,
      by simp [ZMod.coe_unitOfCoprime, ZMod.val_natCast_of_lt hl]⟩
  · intro _ _
    rfl

/-- 有理数座標での GN は `x + (1 - ζ)u` の円分体ノルムである。
ノルムを自己同型の積として展開し、各自己同型の `ζ` への作用を
`ζ ↦ ζ^j` と読み替える。GN の等式は評価前に証明されているので、
数値 `x` による除算も非零条件も必要ない。 -/
theorem norm_phaseFactor_eq_GTail
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (x u : ℚ) :
    Algebra.norm ℚ ((x : K) + (1 - ζ) * (u : K)) = GTail p 1 x u := by
  let : NeZero p := ⟨hp.out.ne_zero⟩
  let := IsCyclotomicExtension.finiteDimensional {p} ℚ K
  let := IsCyclotomicExtension.isGalois {p} ℚ K
  apply (algebraMap ℚ K).injective
  rw [Algebra.norm_eq_prod_automorphisms, map_GN]
  calc
    (∏ σ : Gal(K/ℚ), σ ((x : K) + (1 - ζ) * (u : K))) =
        ∏ v : (ZMod p)ˣ, ((x : K) + (1 - ζ ^ v.val.val) * (u : K)) := by
      apply Fintype.prod_equiv (IsCyclotomicExtension.Rat.galEquivZMod p K)
      intro σ
      simp only [map_add, map_mul, map_sub, map_one]
      rw [IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq p K σ hζ.pow_eq_one]
      simp
    _ = ∏ j ∈ (Finset.range p).erase 0,
        ((x : K) + (1 - ζ ^ j) * (u : K)) :=
      prod_zmod_units_eq_prod_erase_zero (p := p)
        (fun j => (x : K) + (1 - ζ ^ j) * (u : K))
    _ = GTail p 1 (x : K) (u : K) :=
      (GN_eq_nontrivial_phase_prod_range hp.out.pos hζ _ _).symm

/-- 整数座標での厳密なノルム等式。
`hζ.toInteger` は円分体の整数環に属する原始根であり、左辺は
`𝓞 K → ℤ` のノルム、右辺は `ℤ` 上の GN 多項式値である。
体ノルムとの整合性を使って有理数上の等式から降ろす。 -/
theorem integral_norm_phaseFactor_eq_GTail
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (x u : ℤ) :
    Algebra.norm ℤ ((x : 𝓞 K) + (1 - hζ.toInteger) * (u : 𝓞 K)) =
      GTail p 1 x u := by
  apply Int.cast_injective (α := ℚ)
  rw [Algebra.coe_norm_int]
  have h := norm_phaseFactor_eq_GTail hζ (x : ℚ) (u : ℚ)
  have hz : algebraMap (𝓞 K) K hζ.toInteger = ζ := hζ.coe_toInteger
  simpa [map_GN, GTail, hz] using h

/-- 奇素数次数の分岐因子 λ=ζ−1 の整数ノルムは +p。
GN の x=0, u=−1 評価から計算するので、符号は `(−1)^(p−1)=1` に現れる。
既存の体ノルムによる計算法とは別に、GN の先頭係数 p を直接観察できる。 -/
theorem integral_norm_ramifier_eq_prime
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hodd : Odd p) :
    Algebra.norm ℤ (hζ.toInteger - 1) = (p : ℤ) := by
  have h := integral_norm_phaseFactor_eq_GTail hζ 0 (-1)
  have heven : Even (p - 1) := Nat.Odd.sub_odd hodd (by decide : Odd (1 : ℕ))
  simpa only [Int.cast_zero, Int.cast_neg, Int.cast_one, zero_add, mul_neg_one,
    neg_sub, GTail_eval_zero, Nat.choose_one_right, heven.neg_one_pow, mul_one] using h

end DkMath.Lib.NumberTheory
