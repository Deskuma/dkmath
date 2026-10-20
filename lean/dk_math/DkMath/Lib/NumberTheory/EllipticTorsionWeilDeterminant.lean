/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticTorsionGL2
import DkMath.Lib.NumberTheory.RootPairingDeterminant

#print "file: DkMath.Lib.NumberTheory.EllipticTorsionWeilDeterminant"

/-!
# 実際のE[p]上のWeil対の受け口と、条件付きの円分行列式

WeilPairingDataは実際のねじれ点上の乗法的な対とその法則を記録する。
幾何学的な対の構成を仮定から消したものではない。現在のライブラリには
関数体・付値・平行移動からこのデータを作るproviderがなく、それが未実装境界である。
一旦このデータが供給されれば、証明済みの次元2と一般の交代対の線形代数によって、
基底対の値の原始性と行列式指標の円分指標との一致が得られる。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open Module DkMath.Lib.RepresentationTheory CyclotomicRootModule
variable {K : Type*} [Field K] (E : WeierstrassCurve K) (p : ℕ)

/-- 実際の点に対するWeil対の供給契約。法則と同変性を全て明示し、存在は主張しない。 -/
structure WeilPairingData where
  pairing : RootPairing (AlgebraicClosure K) p (Torsion E p)
  equivariant : ∀ σ P Q,
    (pairing.value (representation E p σ P) (representation E p σ Q) : AlgebraicClosure K) =
      σ.toAlgHom (pairing.value P Q : AlgebraicClosure K)

variable [CharZero K] [E.IsElliptic] [Fact p.Prime]

/-- 非退化性により基底対の値は1ではない。単に二次元というだけではこの結論は出ない。 -/
theorem weil_basis_value_ne_one (w : WeilPairingData E p) :
    w.pairing.value (torsionBasis E p 0) (torsionBasis E p 1) ≠ 1 := by
  intro h
  have hn := alternating_basis_ne_zero w.pairing.rootForm
    w.pairing.rootForm_alternating w.pairing.rootForm_nondegenerate (torsionBasis E p)
  exact hn ((w.pairing.rootValue_eq_zero _ _).mpr h)

/-- 素数pでは、基底対の値は非自明なp乗根なので原始p乗根となる。 -/
theorem weil_basis_isPrimitiveRoot (w : WeilPairingData E p) :
    IsPrimitiveRoot (w.pairing.value (torsionBasis E p 0) (torsionBasis E p 1) : AlgebraicClosure K) p := by
  let z := w.pairing.value (torsionBasis E p 0) (torsionBasis E p 1)
  have hp : (z : AlgebraicClosure K) ^ p = 1 :=
    congrArg (fun u : (AlgebraicClosure K)ˣ => (u : AlgebraicClosure K)) (w.pairing.value_pow _ _)
  have hn : (z : AlgebraicClosure K) ≠ 1 := fun h => weil_basis_value_ne_one E p w (Units.ext h)
  have ho : orderOf (z : AlgebraicClosure K) = p := orderOf_eq_prime hp hn
  have hprim := IsPrimitiveRoot.orderOf (z : AlgebraicClosure K)
  rw [ho] at hprim
  exact hprim

/-- 同じ実際のE[p]の行列式指標は、Weil対を入力すれば円分指標に一致する。 -/
theorem torsion_determinant_eq_cyclotomic_of_pairing (w : WeilPairingData E p) :
    determinantCharacterWithBasis (representation E p) (torsionBasis E p) = cyclotomicCharacter p :=
  RootPairing.determinant_eq_cyclotomic_of_pairing (representation E p) (torsionBasis E p)
    w.pairing w.equivariant

/-- 任意のp乗根への作用が、同じ実際の線形作用素の行列式の冪となる。
明示的なWeil対入力を必要とするので、無条件の楕円曲線定理とは区別する。 -/
theorem torsion_apply_eq_pow_det_of_pairing (w : WeilPairingData E p)
    (σ : Field.absoluteGaloisGroup K) (ζ : AlgebraicClosure K) (hζ : ζ ^ p = 1) :
    σ.toAlgHom ζ = ζ ^ (LinearMap.det (representation E p σ)).val := by
  have hn : ζ ≠ 0 := by
    intro h
    rw [h, zero_pow (Fact.out : p.Prime).ne_zero] at hζ
    exact zero_ne_one hζ
  let z : rootsOfUnity p (AlgebraicClosure K) :=
    ⟨Units.mk0 ζ hn, (mem_rootsOfUnity p _).mpr (Units.ext hζ)⟩
  have h := cyclotomicCharacter_spec p σ z
  have hd := congrArg (fun χ : Field.absoluteGaloisGroup K →* (ZMod p)ˣ => (χ σ : ZMod p))
    (torsion_determinant_eq_cyclotomic_of_pairing E p w)
  rw [determinantCharacterWithBasis_val] at hd
  rw [← hd] at h
  exact h

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
