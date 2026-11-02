/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.CyclicKummerIntegral
import DkMath.Lib.NumberTheory.KummerSelmer

#print "file: DkMath.Lib.NumberTheory.CyclotomicKummerArithmetic"

/-!
# 元の円分 Kummer ベクトルを整数環・付値へ渡す

同じ表示を非零整数でスカラー倍し、根・定数を整数環の実際の元にする。
Kummer 類・ベクトル・各素点の付値剰余は元のままである。
全素点の付値条件への所属を仮定なしに供給したとは主張しない。
-/

namespace DkMath.Lib.NumberTheory.CyclotomicKummerArithmetic

open CyclotomicRootModule CyclotomicKernelField CyclotomicCharacterField CyclicKummer
open CyclotomicKummerWeight CyclicKummerIntegral IsDedekindDomain
open DkMath.Lib.Algebra
set_option backward.isDefEq.respectTransparency false
noncomputable section

variable {p : ℕ} [Fact p.Prime] {C : Type*} [AddCommGroup C]
    (ψ : (cyclotomicCharacter (K := ℚ) p).ker →* Multiplicative C)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)

local instance instRootFieldNumberField : NumberField (rootField ζ) := rootField_numberField ζ

variable (P : (letI := extensionAlgebra ψ hζ; Presentation p (rootField ζ) (characterField ψ)))

/-- スカラー倍した定数は、元の同じ Kummer 類を表す。 -/
theorem rescale_constantClass (c : rootField ζ) (hc : c ≠ 0) :
    letI := extensionAlgebra ψ hζ
    constantClass ψ hζ (rescale P c hc) = constantClass ψ hζ P := by
  let := extensionAlgebra ψ hζ
  let u : (rootField ζ)ˣ := Units.mk0 c hc
  have he : constantUnit ψ hζ (rescale P c hc) = u ^ p * constantUnit ψ hζ P := by
    apply Units.ext
    rfl
  change (↑(constantUnit ψ hζ (rescale P c hc)) : KummerClass (rootField ζ) p) = _
  rw [he, QuotientGroup.mk_mul]
  have hp : ((u ^ p : (rootField ζ)ˣ) : KummerClass (rootField ζ) p) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨u, rfl⟩
  rw [hp, one_mul]
  rfl

/-- 同じ非零ベクトルを保ち、新しい固有ベクトルに置き換えない。 -/
theorem rescale_constantVector (c : rootField ζ) (hc : c ≠ 0) :
    letI := extensionAlgebra ψ hζ
    constantVector ψ hζ (rescale P c hc) = constantVector ψ hζ P :=
  congrArg Additive.ofMul (rescale_constantClass ψ hζ P c hc)

/-- 整数化の存在と元のベクトルとの一致をまとめた公開接続。 -/
theorem exists_integral_model_same_vector :
    letI := extensionAlgebra ψ hζ
    ∃ D : IntegralModel P, constantVector ψ hζ D.presentation = constantVector ψ hζ P := by
  let := extensionAlgebra ψ hζ
  obtain ⟨D⟩ := exists_integral_model P
  exact ⟨D, rescale_constantVector ψ hζ P _ D.denominator_ne_zero⟩

/-- 整数化後も、同じ整数環の各素点で元の付値剰余を保つ。 -/
theorem rescale_valuationLinear (c : rootField ζ) (hc : c ≠ 0)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers (rootField ζ))) :
    letI := extensionAlgebra ψ hζ
    KummerSelmer.valuationLinear p v (constantVector ψ hζ (rescale P c hc)) =
      KummerSelmer.valuationLinear p v (constantVector ψ hζ P) :=
  congrArg (KummerSelmer.valuationLinear p v) (rescale_constantVector ψ hζ P c hc)

/-- 整数代表の Selmer 所属は元のベクトルの所属と同値。分母払いでは所属を捏造できない。 -/
theorem rescale_mem_valuationSpace_iff (c : rootField ζ) (hc : c ≠ 0) :
    letI := extensionAlgebra ψ hζ
    constantVector ψ hζ (rescale P c hc) ∈
        KummerSelmer.valuationSpace (R := NumberField.RingOfIntegers (rootField ζ)) p ↔
      constantVector ψ hζ P ∈
        KummerSelmer.valuationSpace (R := NumberField.RingOfIntegers (rootField ζ)) p := by
  let := extensionAlgebra ψ hζ
  rw [rescale_constantVector ψ hζ P c hc]

/-- 元の同じベクトルに残る付値条件を、主分数イデアルの指数で正確に書く。 -/
theorem constantVector_mem_valuationSpace_iff :
    letI := extensionAlgebra ψ hζ
    constantVector ψ hζ P ∈
        KummerSelmer.valuationSpace (R := NumberField.RingOfIntegers (rootField ζ)) p ↔
      ∀ v : HeightOneSpectrum (NumberField.RingOfIntegers (rootField ζ)),
        (p : ℤ) ∣ FractionalIdeal.count (rootField ζ) v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers (rootField ζ)))
            P.constant) := by
  let := extensionAlgebra ψ hζ
  exact KummerSelmer.mem_valuationSpace_mk_iff p (constantUnit ψ hζ P)

end
end DkMath.Lib.NumberTheory.CyclotomicKummerArithmetic
