/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.QuinticGoldenNorm
import DkMath.FLT.Five.TraceOneBridge

/-!
# FLT5 の既存 GoldenInt への相対ノルム

中立な `TraceOneInt 1` の相対ノルムを、既存環との環同型で GoldenInt に運ぶ。
`N(a+ζb)=conj⟨a²+b²,−ab⟩`、`N(ζ−1)=conj(2+φ)` という
元の等式が接合点であり、ノルム値5の一致だけから元を同定しない。
-/

open scoped NumberField

namespace DkMath.FLT.Kummer

open DkMath.FLT.Five
open DkMath.Lib.NumberTheory

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {5} ℚ K] {ζ : K}

/-- GoldenInt の黄金比を `1+ζ+ζ⁴` として埋め込む。 -/
def fiveGoldenEmbedding (hζ : IsPrimitiveRoot ζ 5) : GoldenInt →+* 𝓞 K :=
  (goldenCyclotomicEmbedding hζ).comp goldenTraceOneRingEquiv.toRingHom

/-- 既存 GoldenInt を値域とする相対ノルム。 -/
noncomputable def fiveGoldenRelativeNorm (hζ : IsPrimitiveRoot ζ 5) : 𝓞 K →* GoldenInt :=
  goldenTraceOneRingEquiv.symm.toMonoidHom.comp (quinticGoldenNorm hζ)

/-- 埋め込みの単射性。 -/
theorem fiveGoldenEmbedding_injective (hζ : IsPrimitiveRoot ζ 5) :
    Function.Injective (fiveGoldenEmbedding hζ) :=
  (goldenCyclotomicEmbedding_injective hζ).comp goldenTraceOneRingEquiv.injective

/-- 元 a+ζb の相対ノルムは、指定された平方境界の黄金比共役になる。 -/
theorem fiveGoldenRelativeNorm_phase (hζ : IsPrimitiveRoot ζ 5) (a b : ℤ) :
    fiveGoldenRelativeNorm hζ ((a : 𝓞 K) + hζ.toInteger * (b : 𝓞 K)) =
      goldenConj ⟨a ^ 2 + b ^ 2, -(a * b)⟩ := by
  change traceOneToGolden (quinticGoldenNorm hζ _) = _
  rw [quinticGoldenNorm_phase]
  rfl

/-- 円分分岐因子と、既存の黄金比分岐因子の対応。 -/
theorem fiveGoldenRelativeNorm_ramifier (hζ : IsPrimitiveRoot ζ 5) :
    fiveGoldenRelativeNorm hζ (hζ.toInteger - 1) = goldenConj goldenTau := by
  change traceOneToGolden (quinticGoldenNorm hζ _) = _
  rw [quinticGoldenNorm_ramifier]
  rfl

/-- 相対ノルムは二つの共役因子の積であることを元として再確認する。 -/
theorem fiveGoldenRelativeNorm_embedding (hζ : IsPrimitiveRoot ζ 5) (x : 𝓞 K) :
    fiveGoldenEmbedding hζ (fiveGoldenRelativeNorm hζ x) = x * quinticConj hζ x := by
  change goldenCyclotomicEmbedding hζ (goldenTraceOneRingEquiv
    (goldenTraceOneRingEquiv.symm (quinticGoldenNorm hζ x))) = _
  rw [RingEquiv.apply_symm_apply]
  exact quinticGoldenNorm_embedding hζ x

/-- 黄金比共役を環同型として束ねる。単元・五乗・可除性を同時に運べる。 -/
def goldenConjRingEquiv : GoldenInt ≃+* GoldenInt where
  toFun := goldenConj
  invFun := goldenConj
  left_inv := goldenConj_invol
  right_inv := goldenConj_invol
  map_add' x y := by ext <;> simp [goldenConj] <;> ring
  map_mul' := goldenConj_mul

/-- ノルムの整数合同を黄金比整数上に保持する。
二次ノルムの有限恒等式による証明であり、商環での根の選択を仮定しない。 -/
theorem fiveGoldenRelativeNorm_congruent_integer (hζ : IsPrimitiveRoot ζ 5)
    {x : 𝓞 K} {n : ℤ} (h : (5 : 𝓞 K) ∣ x - (n : 𝓞 K)) :
    (5 : GoldenInt) ∣ fiveGoldenRelativeNorm hζ x - (n : GoldenInt) ^ 2 := by
  obtain ⟨w, hw⟩ := h
  let e := quinticGoldenEquiv hζ
  let z := e.symm w
  have hx : e.symm x = (n : QuinticGoldenOrder) + 5 * z := by
    have hx : x = (n : 𝓞 K) + 5 * w := by linear_combination hw
    rw [hx, map_add, map_mul, map_intCast, map_ofNat]
  let k : DkMath.NumberTheory.TraceOneQuadratic.TraceOneInt 1 :=
    (n : _) * (2 * z.re + (DkMath.NumberTheory.TraceOneQuadratic.tau 1 - 1) * z.im) +
      5 * QuadraticAlgebra.norm z
  refine ⟨goldenTraceOneRingEquiv.symm k, ?_⟩
  apply goldenTraceOneRingEquiv.injective
  rw [map_sub, map_pow, map_intCast, map_mul, map_ofNat, RingEquiv.apply_symm_apply]
  change goldenTraceOneRingEquiv (goldenTraceOneRingEquiv.symm
    (QuadraticAlgebra.norm (e.symm x))) - (n : _) ^ 2 = 5 * k
  rw [RingEquiv.apply_symm_apply, hx]
  dsimp only [k]
  simp only [QuadraticAlgebra.norm_def, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add,
    QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_intCast,
    QuadraticAlgebra.im_intCast, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]
  ring

end DkMath.FLT.Kummer
