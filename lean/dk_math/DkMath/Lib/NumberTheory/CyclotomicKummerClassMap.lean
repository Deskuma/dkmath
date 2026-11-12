/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.CyclotomicKummerArithmetic
import DkMath.Lib.NumberTheory.KummerSelmerExact

#print "file: DkMath.Lib.NumberTheory.CyclotomicKummerClassMap"

/-!
# 同じ円分 Kummer ベクトルの類群像と単元への復帰

元のベクトルの Selmer 所属を明示入力に残し、同じ類の実際の類群像を定義する。
像が零なら同じ定数を整数環の単元と底体の `p` 乗に分解する。
その単元冪商の類は非自明である。所属・像の消滅・Galois 同変性を仮定なしに供給しない。
-/

namespace DkMath.Lib.NumberTheory.CyclotomicKummerClassMap

open CyclotomicRootModule CyclotomicKernelField CyclotomicCharacterField CyclicKummer
open CyclotomicKummerWeight KummerSelmer KummerSelmerClassMap KummerSelmerExact
open CyclicKummerIntegral IsDedekindDomain
set_option backward.isDefEq.respectTransparency false
noncomputable section

variable {p : ℕ} [Fact p.Prime] {C : Type*} [AddCommGroup C]
    (ψ : (cyclotomicCharacter (K := ℚ) p).ker →* Multiplicative C)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)

local instance instRootFieldNumberField : NumberField (rootField ζ) := rootField_numberField ζ

variable (P : (letI := extensionAlgebra ψ hζ; Presentation p (rootField ζ) (characterField ψ)))
    (hval : constantVector ψ hζ P ∈
      valuationSpace (R := NumberField.RingOfIntegers (rootField ζ)) p)

/-- 元の同じベクトルを同じ Selmer 群の元として包装する。 -/
def selmerElement : Selmer (NumberField.RingOfIntegers (rootField ζ)) (rootField ζ) p :=
  ofValuationSpace p ⟨constantVector ψ hζ P, hval⟩

/-- 元の同じ類の、実際の円分類群の `p` 捩れへの像。 -/
def classImage : ClassTorsion (NumberField.RingOfIntegers (rootField ζ)) p :=
  toClassTorsion p (Fact.out : p.Prime).pos (selmerElement ψ hζ P hval)

/-- 元の定数の任意の同じイデアル冪根で類群像を計算できる。 -/
theorem classImage_via_root
    (J : (FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers (rootField ζ))) (rootField ζ))ˣ)
    (hJ : J ^ p = toPrincipalIdeal (NumberField.RingOfIntegers (rootField ζ)) (rootField ζ)
      (constantUnit ψ hζ P)) :
    (classImage ψ hζ P hval).val = ClassGroup.mk (rootField ζ) J := by
  have hr : rootIdeal p (constantUnit ψ hζ P) hval = J :=
    idealUnits_pow_injective (Fact.out : p.Prime).pos (by
      dsimp only
      rw [rootIdeal_pow, hJ])
  change classMapValue p (selmerElement ψ hζ P hval) = _
  rw [classMapValue_eq (Fact.out : p.Prime).pos _ (constantUnit ψ hζ P) hval rfl, hr]

/-- 整数化の前後で同じ類群像を保つ。所属の証明を取り替えても像は変わらない。 -/
theorem rescale_classImage (c : rootField ζ) (hc : c ≠ 0) :
    letI := extensionAlgebra ψ hζ
    let hv := (CyclotomicKummerArithmetic.rescale_mem_valuationSpace_iff ψ hζ P c hc).mpr hval
    classImage ψ hζ (rescale P c hc) hv = classImage ψ hζ P hval := by
  let := extensionAlgebra ψ hζ
  apply congrArg (toClassTorsion p (Fact.out : p.Prime).pos)
  apply Subtype.ext
  exact CyclotomicKummerArithmetic.rescale_constantClass ψ hζ P c hc

/-- 類群像が零なら同じ定数を単元倍冪へ戻し、非零 Kummer ベクトルを同じ単元類で表す。
Selmer 所属と類群像の零化は、ここでは別の明示的な仮定である。 -/
theorem unit_of_classImage_eq_one (hzero : classImage ψ hζ P hval = 1) :
    letI := extensionAlgebra ψ hζ
    ∃ (u : (NumberField.RingOfIntegers (rootField ζ))ˣ) (c : (rootField ζ)ˣ),
      P.constant = algebraMap (NumberField.RingOfIntegers (rootField ζ)) (rootField ζ) u * (c : rootField ζ) ^ p ∧
      constantVector ψ hζ P = Additive.ofMul
        ((Units.map (algebraMap (NumberField.RingOfIntegers (rootField ζ)) (rootField ζ)).toMonoidHom u :
          (rootField ζ)ˣ) : KummerClass (rootField ζ) p) ∧
      (u : UnitClass (NumberField.RingOfIntegers (rootField ζ)) p) ≠ 1 := by
  let := extensionAlgebra ψ hζ
  have hz : toClassGroup p (Fact.out : p.Prime).pos (selmerElement ψ hζ P hval) = 1 :=
    congrArg Subtype.val hzero
  obtain ⟨u, c, he⟩ := unit_decomposition p (Fact.out : p.Prime).pos
    (selmerElement ψ hζ P hval) hz (constantUnit ψ hζ P) rfl
  have hq : constantClass ψ hζ P =
      ((Units.map (algebraMap (NumberField.RingOfIntegers (rootField ζ)) (rootField ζ)).toMonoidHom u :
        (rootField ζ)ˣ) : KummerClass (rootField ζ) p) := by
    change (↑(constantUnit ψ hζ P) : KummerClass (rootField ζ) p) = _
    rw [he, QuotientGroup.mk_mul]
    have hcq : ((c ^ p : (rootField ζ)ˣ) : KummerClass (rootField ζ) p) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨c, rfl⟩
    rw [hcq, mul_one]
  refine ⟨u, c, congrArg Units.val he, congrArg Additive.ofMul hq, ?_⟩
  intro hu
  obtain ⟨v, hv⟩ := (QuotientGroup.eq_one_iff u).mp hu
  change v ^ p = u at hv
  apply constantClass_ne_one ψ hζ P
  rw [hq, ← hv, map_pow, QuotientGroup.mk_pow]
  exact class_pow (rootField ζ) p _

end
end DkMath.Lib.NumberTheory.CyclotomicKummerClassMap
