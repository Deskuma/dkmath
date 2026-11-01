/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicCharacterField
import DkMath.Lib.NumberTheory.CyclotomicCharacterKummer

#print "file: DkMath.FLT.FreyCyclotomicKummer"

/-!
# Frey の非分裂から、同じ体内の非自明 Kummer 根へ

同じ巡回段から得た指標の同じ核の固定体を `F(α)` と表示する。
`α^p=b` と既約性、生成性を同時に得るので、`b` は底体の `p` 乗ではない。
元の指標核は同じ根の固定群であり、同じ付値環での局所固定性も保たれる。
根・多項式・生成性の provider は要求しない。
`ω²` 固有成分、整数化、類群・単数による消滅は引き続き未実装である。
-/

namespace DkMath.FLT.Frey.Source

open DkMath.Lib.Algebra DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation CyclotomicRootModule CyclotomicKernelField
open CyclotomicCharacterField CyclicKummer ValuationInertia DkMath.Lib.RepresentationTheory

set_option backward.isDefEq.respectTransparency false
noncomputable section

variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance instIsEllipticCyclotomicKummer : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
variable (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (K : AddSubgroup (Points S.rationalCurve)) [Finite K] [IsAddCyclic K]
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ K, pointAction S.rationalCurve σ x ∈ K)
    {m : ℕ} (hm : 1 ≤ m) (hcard : Nat.card K = p ^ m)
    (hbase : pointSubgroup S.rationalCurve p L ≤ K)

include hline hcofixed hstable hm hcard hbase

/-- 非分裂から同じ構成体の Kummer 表示を内部供給する。
定数が `p` 乗でないことは `Presentation.constant_not_pow` で取り出せる。 -/
theorem residual_nonsplit_has_kummer_presentation (hp5 : 5 ≤ p)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)
    (hns : ¬ ∃ D : Submodule (ZMod p) (TorsionPreimageQuotient.Quotient p K),
      IsCompl (TorsionPreimageQuotient.torsionImage p K) D ∧
        IsStable (preimageRepresentation S.rationalCurve p K hstable) D) :
    ∃ v : TorsionPreimageQuotient.Quotient p K,
      Function.Surjective (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v) ∧
      (letI := extensionAlgebra
        (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v) hζ
       Nonempty (Presentation p (rootField ζ)
         (S.residualCharacterField L hline hcofixed K hstable hm hcard hbase v))) := by
  obtain ⟨v, hv⟩ := S.residual_cyclic_extension_nonsplit_has_surjective_character
    L hline hcofixed K hstable hm hcard hbase hp5 hns
  refine ⟨v, hv, ?_⟩
  exact CyclotomicCharacterKummer.exists_presentation
    (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v) hζ
    (S.residual_cyclic_extension_character_kernel_isOpen L hline hcofixed K hstable hm hcard hbase v)
    hv (card_torsionImage_of_cyclic S.rationalCurve K hm hcard)
    (S.residual_cyclic_extension_character_conjugate L hline hcofixed K hstable hm hcard hbase v)

variable {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)
    (v : TorsionPreimageQuotient.Quotient p K)

variable (P : (letI := extensionAlgebra (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v) hζ;
  Presentation p (rootField ζ) (S.residualCharacterField L hline hcofixed K hstable hm hcard hbase v)))

/-- 元の指標の零化と、同じ根の固定性は同値。 -/
theorem residual_character_eq_one_iff_fix_kummer_radical
    (g : (cyclotomicCharacter (K := ℚ) p).ker) :
    letI := extensionAlgebra
      (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v) hζ
    S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v g = 1 ↔
      kernelEquiv hζ g P.radical.val = P.radical.val :=
  CyclotomicCharacterKummer.character_eq_one_iff_fix_radical _ hζ
    (S.residual_cyclic_extension_character_kernel_isOpen L hline hcofixed K hstable hm hcard hbase v) P g

/-- `p` 上の同じ分解群は、同じ Kummer 根を固定する。 -/
theorem residual_kummer_radical_decomposition_fixed_at_p (hp5 : 5 ≤ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A p)
    (g : (cyclotomicCharacter (K := ℚ) p).ker)
    (hg : kernelEquiv hζ g ∈ A.decompositionSubgroup (rootField ζ)) :
    letI := extensionAlgebra
      (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v) hζ
    kernelEquiv hζ g P.radical.val = P.radical.val := by
  let := extensionAlgebra
    (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v) hζ
  exact S.residual_characterField_decomposition_fixed_at_p L hline hcofixed K hstable hm hcard hbase
    hp5 hζ v A hA g hg P.radical

/-- `p` 外では元の共鳴住所の吸収だけを入力に残し、同じ根を慣性が固定する。 -/
theorem residual_kummer_radical_inertia_fixed_away (hp5 : 5 ≤ p)
    (hbad : ∀ q : ℕ, q.Prime → q ≠ p → 5 ≤ q → (q : ℤ) ∣ S.a * S.b * S.c →
      ((q : ZMod p) = 1 ∨ (q : ZMod p) = -1) →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), LiesOverPrime A q →
        ∀ τ ∈ inertiaSubgroupIn A ℚ, ∀ y : Points S.rationalCurve,
          p • y ∈ K → pointAction S.rationalCurve τ y - y ∈ K)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (g : (cyclotomicCharacter (K := ℚ) p).ker)
    (hg : kernelEquiv hζ g ∈ inertiaSubgroupIn A (rootField ζ)) :
    letI := extensionAlgebra
      (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v) hζ
    kernelEquiv hζ g P.radical.val = P.radical.val := by
  let := extensionAlgebra
    (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v) hζ
  exact S.residual_characterField_inertia_fixed_away L hline hcofixed K hstable hm hcard hbase
    hp5 hζ hbad hq hqp v A hA g hg P.radical

end
end DkMath.FLT.Frey.Source
