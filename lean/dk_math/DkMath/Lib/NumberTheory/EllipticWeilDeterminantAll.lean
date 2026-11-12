/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.RepresentationTheory.AlternatingDeterminantRing
import DkMath.Lib.NumberTheory.EllipticGeometricWeilPairing

#print "file: DkMath.Lib.NumberTheory.EllipticWeilDeterminantAll"

/-!
# 全ての非零捩れ段の幾何学的 Weil 対と円分行列式

法 n は体とは限らない。実際の幾何学的対の非退化性から係数の忠実性を使い、
同じ表現の行列式を全 n 乗根への作用で定まる指標と同定する。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open Module CyclotomicRootModule DkMath.Lib.RepresentationTheory
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

/-- 同じ代数閉包の全 n 乗根への作用を表す、標準有限円分指標。 -/
def torsionCyclotomicCharacter (n : ℕ) (hn : n ≠ 0) : Field.absoluteGaloisGroup K →* (ZMod n)ˣ := by
  let : NeZero n := ⟨hn⟩
  exact (modularCyclotomicCharacter (AlgebraicClosure K)
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure K) n)).comp
      { toFun := fun σ => σ.toRingEquiv
        map_one' := rfl
        map_mul' := fun _ _ => rfl }

/-- 有限円分指標の、同じ全 n 乗根への実際の作用公式。 -/
theorem torsionCyclotomicCharacter_spec (n : ℕ) (hn : n ≠ 0) (σ : Field.absoluteGaloisGroup K)
    (z : rootsOfUnity n (AlgebraicClosure K)) :
    σ.toAlgHom (z.val : AlgebraicClosure K) =
      (z.val : AlgebraicClosure K) ^ (torsionCyclotomicCharacter n hn σ : ZMod n).val := by
  let : NeZero n := ⟨hn⟩
  exact modularCyclotomicCharacter.spec (AlgebraicClosure K)
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure K) n) σ.toRingEquiv z.property

variable (E : WeierstrassCurve K) [E.IsElliptic]

/-- 実際の全 n 捩れ基底に対して、同じ行列式は有限円分指標に一致する。
対の存在・非退化性・同変性を新しい provider として要求しない。 -/
theorem torsion_determinant_all (n : ℕ) (hn : n ≠ 0) (b : Basis (Fin 2) (ZMod n) (Torsion E n))
    (σ : Field.absoluteGaloisGroup K) :
    LinearMap.det (representation E n σ) = (torsionCyclotomicCharacter n hn σ : ZMod n) := by
  let : NeZero n := ⟨hn⟩
  let w := geometricWeilPairingData E n hn
  apply AlternatingDeterminantRing.det_eq_of_equivariant w.pairing.rootForm
    w.pairing.rootForm_alternating b w.pairing.rootForm_nondegenerate
  change w.pairing.rootValue _ _ = (torsionCyclotomicCharacter n hn σ : ZMod n) • w.pairing.rootValue _ _
  apply Additive.ext
  rw [smul_toMul]
  apply Subtype.ext
  apply Units.ext
  exact (w.equivariant σ (b 0) (b 1)).trans
    (torsionCyclotomicCharacter_spec n hn σ
      ⟨w.pairing.value (b 0) (b 1), (mem_rootsOfUnity n _).mpr (w.pairing.value_pow _ _)⟩)

end
end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
