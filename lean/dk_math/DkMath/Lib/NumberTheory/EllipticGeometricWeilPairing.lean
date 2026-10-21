/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticWeilNondegenerate
import DkMath.Lib.NumberTheory.EllipticTorsionWeilDeterminant

#print "file: DkMath.Lib.NumberTheory.EllipticGeometricWeilPairing"

/-!
# 実際に構成したWeil対から円分行列式へ

NOTE-025の同じ移動比例定数へ、双加法性・交代性・ガロア同変性・非退化性を全て証明して与える。
ここで初めて既存のRootPairingとWeilPairingDataの供給契約を実際のデータで満たす。
従って行列式と円分指標の一致から、対データの追加入力を除去できる。
Frey表現の既約性やモジュラー性・レベル降下は別の算術であり、この定理の結論に含めない。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open DkMath.Lib.RepresentationTheory CyclotomicRootModule
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]

/-- 同じ実際の交代双指標の単元値から、法則を証明した非退化交代対を構成する。 -/
noncomputable def geometricRootPairing (n : ℕ) (hn : n ≠ 0) :
    RootPairing (AlgebraicClosure K) n (Torsion E n) where
  value S T := weilTranslationUnit E n hn T S
  add_left S R T := weilTranslationUnit_add E n hn T S R
  add_right S T R := weilTranslationUnit_add_right E n hn S T R
  alternating T := weilTranslationUnit_self E n hn T
  nondegenerate S hS := weilAlternatingBicharacter_nondegenerate_left E n hn S
    (fun T => Subtype.ext (hS T))

/-- 構成した対の値は、前章までの同じ双指標の単元値である。 -/
theorem geometricRootPairing_value (n : ℕ) (hn : n ≠ 0) (S T : Torsion E n) :
    (geometricRootPairing E n hn).value S T = (weilAlternatingBicharacter E n hn S T).val := rfl

/-- 実際のWeil対データを無条件に供給する。n≠0・標数0・楕円曲線性は保持する。 -/
noncomputable def geometricWeilPairingData (n : ℕ) (hn : n ≠ 0) : WeilPairingData E n where
  pairing := geometricRootPairing E n hn
  equivariant σ S T := congrArg (fun u : (AlgebraicClosure K)ˣ => (u : AlgebraicClosure K))
    (weilTranslationUnit_galois E n hn σ S T)

variable (p : ℕ) [Fact p.Prime]

/-- 同じ実際のp-torsion表現の行列式は円分指標である。対データを入力に取らない終点。 -/
theorem torsion_determinant_eq_cyclotomic :
    determinantCharacterWithBasis (representation E p) (torsionBasis E p) = cyclotomicCharacter p :=
  torsion_determinant_eq_cyclotomic_of_pairing E p
    (geometricWeilPairingData E p (Fact.out : p.Prime).ne_zero)

/-- 同じ表現の行列式の冪が、任意のp乗根への実際の係数作用と一致する。 -/
theorem torsion_apply_eq_pow_det (σ : Field.absoluteGaloisGroup K) (ζ : AlgebraicClosure K)
    (hζ : ζ ^ p = 1) : σ.toAlgHom ζ = ζ ^ (LinearMap.det (representation E p σ)).val :=
  torsion_apply_eq_pow_det_of_pairing E p
    (geometricWeilPairingData E p (Fact.out : p.Prime).ne_zero) σ ζ hζ

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
