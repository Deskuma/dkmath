/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.CosmicCyclotomicNorm
import DkMath.Lib.NumberTheory.CosmicIdealBridge
import DkMath.CosmicFormula.Defs
import Mathlib.NumberTheory.NumberField.ClassNumber

/-!
# GN 版 Kummer 構造定理への入口

読む順序は `signed_GN_identity`、`GN_eq_integral_norm`、
`GN_kummer_structure_of_regular` である。
`a^p+b^p=c^p` を `x=a+b, u=-b` で GN 座標へ移すと、
円分因子は教科書の `a+ζ^i b` になる。

最後の定理では原始性と `a+b` の非分岐性を整数上の互いに素性で与える。
イデアルの互いに素性やイデアル冪の存在を結論と同じ形で仮定せず、
GN の因子分解と共通素イデアル解析から導く。
正則性は類群の位数との互いに素性であり、PID 性を要求しない。

到達点は各因子 `a+ζ^i b=εγ^p` である。単元 `ε` が p 乗であるとは
主張しない。正則素数に対する FLT 全体の再証明には、単元の合同解析と
分岐側の Kummer 補題・降下をさらに実装する必要がある。
-/

open scoped BigOperators NumberField
open DkMath.CosmicFormula DkMath.Lib.NumberTheory

namespace DkMath.FLT.Kummer

/-- 奇数次数の FLT 方程式を GN 座標に移す恒等式。
符号付き座標 `u=-b` を使うので、自然数の切り捨て減算は現れない。
奇数条件は `(-b)^p=-b^p` のために必要である。 -/
theorem signed_GN_identity
    {R : Type*} [CommRing R] {p : ℕ} (hp : Odd p) (a b : R) :
    (a + b) * GN p (a + b) (-b) = a ^ p + b ^ p := by
  have h := add_pow_eq_mul_GTail_one_add_gap p (a + b) (-b)
  rw [add_neg_cancel_right, hp.neg_pow] at h
  linear_combination -h

/-- GN の整数値を円分整数環のノルムとして読む。
これは反例にも非零座標にも依存しない多項式恒等式である。 -/
theorem GN_eq_integral_norm
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (x u : ℤ) :
    GN p x u = Algebra.norm ℤ ((x : 𝓞 K) + (1 - hζ.toInteger) * (u : 𝓞 K)) :=
  (integral_norm_phaseFactor_eq_GTail hζ x u).symm

/-- 教科書の `a+ζb` のノルムは GN の符号付き評価そのものである。 -/
theorem norm_kummerFactor_eq_GN
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (a b : ℤ) :
    Algebra.norm ℤ ((a : 𝓞 K) + hζ.toInteger * (b : 𝓞 K)) = GN p (a + b) (-b) := by
  rw [GN_eq_integral_norm hζ]
  congr 1
  push_cast
  ring

/-- **GN 版 Kummer 構造定理（非分岐側）**。

入力は整数上の FLT 方程式、原始性 `IsCoprime a b`、
非分岐条件 `IsCoprime (a+b) p`、および円分体の類数条件である。
出力は全円分因子のイデアル根・その生成元・単元倍の p 乗表示。

証明の各段階:
* 奇数次数の GN 恒等式を整数環へ写す。
* Bezout の等式を整数環へ写して原始性を保存する。
* `ζ-1 ∣ p` により非分岐条件を分岐因子との互いに素性へ移す。
* 共通素イデアル解析、イデアル冪抽出、類群の torsion 消滅を適用する。

`i=0` は因子 `a+b`。他の添字は非自明な共役因子である。
`IsCoprime (a+b) p` を落とすことはできず、分岐側には別の証明が要る。
単元を残したこの結論だけから FLT の矛盾は出ない。 -/
theorem GN_kummer_structure_of_regular
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hodd : Odd p)
    {a b c : ℤ} (hc : c ≠ 0) (heq : a ^ p + b ^ p = c ^ p)
    (hprim : IsCoprime a b) (hcase : IsCoprime (a + b) (p : ℤ))
    (hreg : Nat.Coprime p (Fintype.card (ClassGroup (𝓞 K))))
    {i : ℕ} (hi : i < p) :
    ∃ (I : Ideal (𝓞 K)) (ε γ : 𝓞 K), I ≠ ⊥ ∧
      Ideal.span ({(a : 𝓞 K) + hζ.toInteger ^ i * (b : 𝓞 K)} : Set (𝓞 K)) = I ^ p ∧
      IsUnit ε ∧ Ideal.span ({γ} : Set (𝓞 K)) = I ∧
      (a : 𝓞 K) + hζ.toInteger ^ i * (b : 𝓞 K) = ε * γ ^ p := by
  have hprim' : IsCoprime (a + b) (-b) := by
    simpa using (hprim.add_mul_left_left 1).neg_right
  have hxu := hprim'.map (Int.castRingHom (𝓞 K))
  have hxp := hcase.map (Int.castRingHom (𝓞 K))
  have hxζ : IsCoprime ((a + b : ℤ) : 𝓞 K) (hζ.toInteger - 1) :=
    hxp.of_isCoprime_of_dvd_right (by simpa using hζ.toInteger_sub_one_dvd_prime')
  have hcR : (c : 𝓞 K) ≠ 0 := by exact_mod_cast hc
  have heqR : ((a + b : ℤ) : 𝓞 K) *
      GTail p 1 ((a + b : ℤ) : 𝓞 K) ((-b : ℤ) : 𝓞 K) = (c : 𝓞 K) ^ p := by
    have hcast : (a : 𝓞 K) ^ p + (b : 𝓞 K) ^ p = (c : 𝓞 K) ^ p := by
      exact_mod_cast heq
    simpa only [Int.cast_add, Int.cast_neg] using
      (signed_GN_identity hodd (a : 𝓞 K) (b : 𝓞 K)).trans hcast
  have h := GN_kummer_structure_of_unramified hp.out hζ.toInteger_isPrimitiveRoot hcR heqR
    hxu hxζ (classGroupPTorsionFreeAt_of_coprime_card hreg) hi
  have hf : ((a + b : ℤ) : 𝓞 K) + (1 - hζ.toInteger ^ i) * ((-b : ℤ) : 𝓞 K) =
      (a : 𝓞 K) + hζ.toInteger ^ i * (b : 𝓞 K) := by push_cast; ring
  simpa only [hf] using h

end DkMath.FLT.Kummer
