/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.TraceOneQuadratic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant

#print "file: DkMath.Lib.NumberTheory.QuinticGoldenNorm"

/-!
# 五次円分整数の黄金比座標と相対ノルム

四次の整数冪基底 `1,ζ,ζ²,ζ³` を、黄金比整数上の `1,ζ` に組み替える。
黄金比は `φ=1+ζ+ζ⁴=−ζ²−ζ³` と固定する。整数係数を明示するので、
有理数上のノルム値だけでなく、相対ノルムの整数性と元の来歴を追跡できる。
中立な黄金比整数モデルは `TraceOneInt 1`。FLT の仮定を使用しない。
-/

namespace DkMath.Lib.NumberTheory

open NumberField
open DkMath.NumberTheory.TraceOneQuadratic

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {5} ℚ K] {ζ : K}

omit [NumberField K] [IsCyclotomicExtension {5} ℚ K] in
/-- 原始五乗根の最小多項式を、整数環内の等式として使う。 -/
theorem quintic_root_sum (hζ : IsPrimitiveRoot ζ 5) :
    hζ.toInteger ^ 4 + hζ.toInteger ^ 3 + hζ.toInteger ^ 2 + hζ.toInteger + 1 = 0 := by
  apply RingOfIntegers.coe_injective
  change ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0
  have hf : Polynomial.cyclotomic 5 K = Polynomial.X ^ 4 + Polynomial.X ^ 3 +
      Polynomial.X ^ 2 + Polynomial.X + 1 := by
    let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    rw [Polynomial.cyclotomic_prime K 5]
    simp [Finset.sum_range_succ]
    ring
  simpa [hf] using hζ.isRoot_cyclotomic (by decide)

/-- 五次円分体内の黄金比。埋め込みの向きをこの定義で固定する。 -/
def quinticPhi (hζ : IsPrimitiveRoot ζ 5) : 𝓞 K :=
  -hζ.toInteger ^ 2 - hζ.toInteger ^ 3

omit [NumberField K] [IsCyclotomicExtension {5} ℚ K] in
/-- `φ=1+ζ+ζ⁻¹` の、逆元を使わない整数環上の形。 -/
theorem quinticPhi_eq (hζ : IsPrimitiveRoot ζ 5) :
    quinticPhi hζ = 1 + hζ.toInteger + hζ.toInteger ^ 4 := by
  dsimp only [quinticPhi]
  linear_combination -(quintic_root_sum hζ)

omit [NumberField K] [IsCyclotomicExtension {5} ℚ K] in
/-- 黄金比の二次関係。 -/
theorem quinticPhi_sq (hζ : IsPrimitiveRoot ζ 5) :
    quinticPhi hζ ^ 2 = quinticPhi hζ + 1 := by
  dsimp only [quinticPhi]
  linear_combination (hζ.toInteger ^ 2 + hζ.toInteger - 1) * quintic_root_sum hζ

/-- 黄金比整数の実際の元を円分整数環へ送る環準同型。 -/
def goldenCyclotomicEmbedding (hζ : IsPrimitiveRoot ζ 5) : TraceOneInt 1 →+* 𝓞 K where
  toFun x := (x.fst : 𝓞 K) + (x.snd : 𝓞 K) * quinticPhi hζ
  map_zero' := by simp
  map_one' := by simp
  map_add' x y := by simp only [fst_add, snd_add, Int.cast_add]; ring
  map_mul' x y := by
    simp only [fst_mul, snd_mul, Int.cast_add, Int.cast_mul, one_mul]
    linear_combination -(x.snd : 𝓞 K) * (y.snd : 𝓞 K) * quinticPhi_sq hζ

/-- 整数冪基底を明示的な `Fin 4` に揃える。 -/
noncomputable def quinticBasis (hζ : IsPrimitiveRoot ζ 5) : Module.Basis (Fin 4) ℤ (𝓞 K) :=
  hζ.integralPowerBasis.basis.reindex (finCongr (by norm_num [IsPrimitiveRoot.integralPowerBasis_dim, Nat.totient_prime Nat.prime_five]))

/-- 冪基底の計算規則。 -/
@[simp] theorem quinticBasis_apply (hζ : IsPrimitiveRoot ζ 5) (i : Fin 4) :
    quinticBasis hζ i = hζ.toInteger ^ (i : ℕ) := by
  simp [quinticBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]

/-- 円分整数の四つの整数座標。 -/
noncomputable def quinticCoordinates (hζ : IsPrimitiveRoot ζ 5) :
    𝓞 K ≃ₗ[ℤ] (Fin 4 → ℤ) := (quinticBasis hζ).equivFun

/-- 四次座標から元に戻す展開。 -/
theorem quinticCoordinates_expansion (hζ : IsPrimitiveRoot ζ 5) (x : 𝓞 K) :
    x = (quinticCoordinates hζ x 0 : 𝓞 K) +
      (quinticCoordinates hζ x 1 : 𝓞 K) * hζ.toInteger +
      (quinticCoordinates hζ x 2 : 𝓞 K) * hζ.toInteger ^ 2 +
      (quinticCoordinates hζ x 3 : 𝓞 K) * hζ.toInteger ^ 3 := by
  have h := (quinticBasis hζ).sum_repr x
  simpa [quinticCoordinates, Module.Basis.equivFun_apply, Fin.sum_univ_succ,
    Algebra.smul_def, add_assoc] using h.symm

/-- 四次座標から取り出す、黄金比基底 `1,ζ` の定数係数。 -/
noncomputable def quinticGoldenA (hζ : IsPrimitiveRoot ζ 5) (x : 𝓞 K) : TraceOneInt 1 :=
  let v := quinticCoordinates hζ x
  ⟨v 0 - v 2 + v 3, -v 3⟩

/-- 四次座標から取り出す、黄金比基底 `1,ζ` の一次係数。 -/
noncomputable def quinticGoldenB (hζ : IsPrimitiveRoot ζ 5) (x : 𝓞 K) : TraceOneInt 1 :=
  let v := quinticCoordinates hζ x
  ⟨v 1 - v 2 + v 3, v 2 - v 3⟩

/-- `ζ²=(φ−1)ζ−1` による整数上の二次基底への組み替え。 -/
theorem quinticGolden_expansion (hζ : IsPrimitiveRoot ζ 5) (x : 𝓞 K) :
    x = goldenCyclotomicEmbedding hζ (quinticGoldenA hζ x) +
      goldenCyclotomicEmbedding hζ (quinticGoldenB hζ x) * hζ.toInteger := by
  conv_lhs => rw [quinticCoordinates_expansion hζ x]
  change _ =
    (((quinticCoordinates hζ x 0 - quinticCoordinates hζ x 2 + quinticCoordinates hζ x 3 : ℤ) : 𝓞 K) +
      ((-quinticCoordinates hζ x 3 : ℤ) : 𝓞 K) * quinticPhi hζ) +
    (((quinticCoordinates hζ x 1 - quinticCoordinates hζ x 2 + quinticCoordinates hζ x 3 : ℤ) : 𝓞 K) +
      ((quinticCoordinates hζ x 2 - quinticCoordinates hζ x 3 : ℤ) : 𝓞 K) * quinticPhi hζ) * hζ.toInteger
  simp only [quinticPhi, Int.cast_add, Int.cast_sub, Int.cast_neg]
  linear_combination
    ((quinticCoordinates hζ x 2 : 𝓞 K) - (quinticCoordinates hζ x 3 : 𝓞 K)) * quintic_root_sum hζ

/-- 四次座標の逆写像も整数係数の有限和である。 -/
theorem quinticCoordinates_symm_apply (hζ : IsPrimitiveRoot ζ 5) (v : Fin 4 → ℤ) :
    (quinticCoordinates hζ).symm v = (v 0 : 𝓞 K) + (v 1 : 𝓞 K) * hζ.toInteger +
      (v 2 : 𝓞 K) * hζ.toInteger ^ 2 + (v 3 : 𝓞 K) * hζ.toInteger ^ 3 := by
  simp [quinticCoordinates, Module.Basis.equivFun_symm_apply, Fin.sum_univ_succ,
    Algebra.smul_def, add_assoc]

/-- 相対二次拡大の整数モデル。ω²=(φ−1)ω−1 とする。 -/
abbrev QuinticGoldenOrder := QuadraticAlgebra (TraceOneInt 1) (-1) (tau 1 - 1)

/-- 二次モデルの元 A+Bω を、実際の円分整数 A+Bζ に送る。 -/
def quinticGoldenToInteger (hζ : IsPrimitiveRoot ζ 5) : QuinticGoldenOrder →+* 𝓞 K where
  toFun x := goldenCyclotomicEmbedding hζ x.re + goldenCyclotomicEmbedding hζ x.im * hζ.toInteger
  map_one' := by
    change goldenCyclotomicEmbedding hζ 1 + goldenCyclotomicEmbedding hζ 0 * hζ.toInteger = 1
    simp
  map_zero' := by simp
  map_add' x y := by simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, map_add]; ring
  map_mul' x y := by
    have hz : hζ.toInteger ^ 2 = (quinticPhi hζ - 1) * hζ.toInteger - 1 := by
      dsimp only [quinticPhi]
      linear_combination quintic_root_sum hζ
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, map_add, map_mul,
      map_neg, map_one, map_sub]
    change _ = _
    have ht : goldenCyclotomicEmbedding hζ (tau 1) = quinticPhi hζ := by
      norm_num [goldenCyclotomicEmbedding, tau]
    rw [ht]
    linear_combination -(goldenCyclotomicEmbedding hζ x.im) *
      (goldenCyclotomicEmbedding hζ y.im) * hz

/-- 整数基底の変換行列を元の等式として固定する。 -/
theorem quinticGoldenToInteger_eq (hζ : IsPrimitiveRoot ζ 5) (x : QuinticGoldenOrder) :
    quinticGoldenToInteger hζ x = (quinticCoordinates hζ).symm
      ![x.re.fst + x.im.snd, x.im.fst + x.im.snd, -x.re.snd + x.im.snd, -x.re.snd] := by
  rw [quinticCoordinates_symm_apply]
  change (x.re.fst : 𝓞 K) + (x.re.snd : 𝓞 K) * quinticPhi hζ +
    ((x.im.fst : 𝓞 K) + (x.im.snd : 𝓞 K) * quinticPhi hζ) * hζ.toInteger = _
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    quinticPhi, Int.cast_add, Int.cast_neg]
  linear_combination -(x.im.snd : 𝓞 K) * quintic_root_sum hζ

/-- 逆の座標行列も整数係数であるため、写像は全単射となる。 -/
theorem quinticGoldenToInteger_bijective (hζ : IsPrimitiveRoot ζ 5) :
    Function.Bijective (quinticGoldenToInteger hζ) := by
  constructor
  · intro x y h
    rw [quinticGoldenToInteger_eq, quinticGoldenToInteger_eq] at h
    have hv := (quinticCoordinates hζ).symm.injective h
    have h0 := congrFun hv 0
    have h1 := congrFun hv 1
    have h2 := congrFun hv 2
    have h3 := congrFun hv 3
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h0 h1 h2 h3
    apply QuadraticAlgebra.ext <;> apply traceOne_ext <;> omega
  · intro x
    refine ⟨⟨quinticGoldenA hζ x, quinticGoldenB hζ x⟩, ?_⟩
    exact (quinticGolden_expansion hζ x).symm

/-- 四次円分整数環と、黄金比整数上の二次拡大の環同型。
相対ノルムを取る前に、この元の対応を証明することが要点である。 -/
noncomputable def quinticGoldenEquiv (hζ : IsPrimitiveRoot ζ 5) : QuinticGoldenOrder ≃+* 𝓞 K :=
  RingEquiv.ofBijective (quinticGoldenToInteger hζ) (quinticGoldenToInteger_bijective hζ)

/-- 定数部分は黄金比整数の埋め込みそのもの。 -/
@[simp] theorem quinticGoldenEquiv_algebraMap (hζ : IsPrimitiveRoot ζ 5) (x : TraceOneInt 1) :
    quinticGoldenEquiv hζ (algebraMap _ QuinticGoldenOrder x) = goldenCyclotomicEmbedding hζ x := by
  change goldenCyclotomicEmbedding hζ x + goldenCyclotomicEmbedding hζ 0 * hζ.toInteger = _
  simp

/-- ω は選択した原始五乗根に送られる。 -/
@[simp] theorem quinticGoldenEquiv_omega (hζ : IsPrimitiveRoot ζ 5) :
    quinticGoldenEquiv hζ (⟨0, 1⟩ : QuinticGoldenOrder) = hζ.toInteger := by
  change goldenCyclotomicEmbedding hζ 0 + goldenCyclotomicEmbedding hζ 1 * hζ.toInteger = _
  simp

/-- 黄金比整数の埋め込みの単射性。ノルム値の比較から推測しない。 -/
theorem goldenCyclotomicEmbedding_injective (hζ : IsPrimitiveRoot ζ 5) :
    Function.Injective (goldenCyclotomicEmbedding hζ) := by
  intro x y h
  have h' := (quinticGoldenEquiv hζ).injective
    (show quinticGoldenEquiv hζ (algebraMap _ QuinticGoldenOrder x) =
      quinticGoldenEquiv hζ (algebraMap _ QuinticGoldenOrder y) by
      simpa only [quinticGoldenEquiv_algebraMap] using h)
  exact congrArg QuadraticAlgebra.re h'

/-- 円分整数から黄金比整数への相対ノルム。二次モデルのノルムを環同型で輸送する。
そのノルムは左乗法の行列式であることが Mathlib で証明されている。 -/
noncomputable def quinticGoldenNorm (hζ : IsPrimitiveRoot ζ 5) : 𝓞 K →* TraceOneInt 1 :=
  QuadraticAlgebra.norm.comp (quinticGoldenEquiv hζ).symm.toMonoidHom

/-- 相対共役も同じ環同型で輸送する。 -/
noncomputable def quinticConj (hζ : IsPrimitiveRoot ζ 5) : 𝓞 K ≃+* 𝓞 K :=
  (quinticGoldenEquiv hζ).symm.trans
    ((starRingAut : QuinticGoldenOrder ≃+* QuinticGoldenOrder).trans (quinticGoldenEquiv hζ))

/-- 相対ノルムを埋め戻すと、元と相対共役の積になる。 -/
theorem quinticGoldenNorm_embedding (hζ : IsPrimitiveRoot ζ 5) (x : 𝓞 K) :
    goldenCyclotomicEmbedding hζ (quinticGoldenNorm hζ x) = x * quinticConj hζ x := by
  change goldenCyclotomicEmbedding hζ
    (QuadraticAlgebra.norm ((quinticGoldenEquiv hζ).symm x)) = _
  rw [← quinticGoldenEquiv_algebraMap, QuadraticAlgebra.algebraMap_norm_eq_mul_star]
  simp [quinticConj]

/-- 黄金比整数を定数として相対二次拡大へ戻す。 -/
@[simp] theorem quinticGoldenEquiv_symm_embedding (hζ : IsPrimitiveRoot ζ 5) (a : TraceOneInt 1) :
    (quinticGoldenEquiv hζ).symm (goldenCyclotomicEmbedding hζ a) =
      algebraMap _ QuinticGoldenOrder a := by
  rw [← quinticGoldenEquiv_algebraMap, RingEquiv.symm_apply_apply]

/-- 原始根の逆輸送。 -/
@[simp] theorem quinticGoldenEquiv_symm_root (hζ : IsPrimitiveRoot ζ 5) :
    (quinticGoldenEquiv hζ).symm hζ.toInteger = (⟨0, 1⟩ : QuinticGoldenOrder) := by
  rw [← quinticGoldenEquiv_omega, RingEquiv.symm_apply_apply]

/-- 相対ノルムは実際の左右二つの円分因子を黄金比の共役へ送る。
`N(a+ζb)=conj⟨a²+b²,−ab⟩` という符号を固定する。 -/
theorem quinticGoldenNorm_phase (hζ : IsPrimitiveRoot ζ 5) (a b : ℤ) :
    quinticGoldenNorm hζ ((a : 𝓞 K) + hζ.toInteger * (b : 𝓞 K)) =
      conj (⟨a ^ 2 + b ^ 2, -(a * b)⟩ : TraceOneInt 1) := by
  change QuadraticAlgebra.norm ((quinticGoldenEquiv hζ).symm _) = _
  rw [map_add, map_mul, map_intCast, map_intCast, quinticGoldenEquiv_symm_root]
  rw [QuadraticAlgebra.norm_def]
  simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_mul,
    QuadraticAlgebra.im_mul, QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast,
    zero_mul, mul_zero, zero_add, add_zero, one_mul]
  change (⟨a, 0⟩ : TraceOneInt 1) * ⟨a, 0⟩ + (tau 1 - 1) * ⟨a, 0⟩ * ⟨b, 0⟩ -
    (-1) * ⟨b, 0⟩ * ⟨b, 0⟩ = _
  ext <;> simp [conj, tau]
  all_goals ring

/-- 分岐因子も同じ規約で輸送される。値5だけでなく元の等式である。 -/
theorem quinticGoldenNorm_ramifier (hζ : IsPrimitiveRoot ζ 5) :
    quinticGoldenNorm hζ (hζ.toInteger - 1) = conj (⟨2, 1⟩ : TraceOneInt 1) := by
  have h := quinticGoldenNorm_phase hζ (-1) 1
  simpa [sub_eq_add_neg, add_comm] using h

/-- 相対共役は原始根を逆根 ζ⁴ に送る。 -/
theorem quinticConj_root (hζ : IsPrimitiveRoot ζ 5) :
    quinticConj hζ hζ.toInteger = hζ.toInteger ^ 4 := by
  change quinticGoldenEquiv hζ (star ((quinticGoldenEquiv hζ).symm hζ.toInteger)) = _
  rw [quinticGoldenEquiv_symm_root]
  change goldenCyclotomicEmbedding hζ (tau 1 - 1) +
    goldenCyclotomicEmbedding hζ (-1) * hζ.toInteger = _
  rw [map_sub, map_one, map_neg, map_one]
  have ht : goldenCyclotomicEmbedding hζ (tau 1) = quinticPhi hζ := by
    norm_num [goldenCyclotomicEmbedding, tau]
  rw [ht, quinticPhi_eq]
  ring

/-- 相対共役は黄金比整数部分を固定する。 -/
theorem quinticConj_embedding (hζ : IsPrimitiveRoot ζ 5) (a : TraceOneInt 1) :
    quinticConj hζ (goldenCyclotomicEmbedding hζ a) = goldenCyclotomicEmbedding hζ a := by
  change quinticGoldenEquiv hζ (star ((quinticGoldenEquiv hζ).symm _)) = _
  rw [quinticGoldenEquiv_symm_embedding]
  have hs : star (algebraMap _ QuinticGoldenOrder a) = algebraMap _ QuinticGoldenOrder a := by
    apply QuadraticAlgebra.ext <;> simp
  rw [hs]
  exact quinticGoldenEquiv_algebraMap hζ a

/-- 黄金比整数を底環とする代数構造。根 ζ と黄金比の埋め込みの選択に依存する。 -/
@[instance_reducible] def quinticGoldenAlgebra (hζ : IsPrimitiveRoot ζ 5) : Algebra (TraceOneInt 1) (𝓞 K) :=
  (goldenCyclotomicEmbedding hζ).toAlgebra

/-- 相対二次モデルの同型は、この底環に関して代数同型でもある。 -/
noncomputable def quinticGoldenAlgEquiv (hζ : IsPrimitiveRoot ζ 5) :
    letI := quinticGoldenAlgebra hζ
    QuinticGoldenOrder ≃ₐ[TraceOneInt 1] 𝓞 K :=
  letI := quinticGoldenAlgebra hζ
  { quinticGoldenEquiv hζ with commutes' := quinticGoldenEquiv_algebraMap hζ }

/-- 実装した相対ノルムは `Algebra.norm` と一致する。
二次モデルでのノルム＝左乗法の行列式と、代数同型に沿うノルムの不変性を使う。 -/
theorem quinticGoldenNorm_eq_algebraNorm (hζ : IsPrimitiveRoot ζ 5) (x : 𝓞 K) :
    quinticGoldenNorm hζ x = letI := quinticGoldenAlgebra hζ; Algebra.norm (TraceOneInt 1) x := by
  let := quinticGoldenAlgebra hζ
  have hn (z : QuinticGoldenOrder) : Algebra.norm (TraceOneInt 1) z = QuadraticAlgebra.norm z := by
    rw [Algebra.norm_apply]
    exact QuadraticAlgebra.det_toLinearMap_eq_norm z
  rw [← Algebra.norm_eq_of_algEquiv (quinticGoldenAlgEquiv hζ).symm, hn]
  rfl

end DkMath.Lib.NumberTheory
