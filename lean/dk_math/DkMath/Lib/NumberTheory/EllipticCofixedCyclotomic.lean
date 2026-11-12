/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.RepresentationTheory.CofixedDeterminant
import DkMath.Lib.NumberTheory.EllipticGeometricWeilPairing
import DkMath.Lib.NumberTheory.EllipticStableLine

#print "file: DkMath.Lib.NumberTheory.EllipticCofixedCyclotomic"

/-!
# NOTE-032-005B: 同じ実際のCofixed捩れ直線上の円分作用

[DkMath.Lib] 標数0の楕円曲線のE[p]について、一次元Lの商がガロア固定なら
L上の作用はmod p円分指標によるスカラー倍となる。
行列式と円分指標の一致は、同じ曲線から構成済みの幾何学的Weil対の定理で供給する。
Weil対の存在や直線の安定性を外部providerとして重複させない。

ZModスカラーを自然数代表の倍点へ戻し、同じ点群内のpointSubgroupへも運ぶ。
この群はisogenyの核の候補であり、商楕円曲線やisogenyの存在は本章に含めない。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open Module DkMath.Lib.RepresentationTheory CyclotomicRootModule
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
variable (p : ℕ) [Fact p.Prime]

/-- [DkMath.Lib] 同じ実際のE[p]のCofixed直線は円分指標で作用される。
行列式公式は構成済みの幾何学的Weil対から供給する。直線の存在は仮定に残す。 -/
theorem cofixed_torsion_apply_eq_cyclotomic_smul
    (L : Submodule (ZMod p) (Torsion E p)) (hline : finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn (representation E p) L)
    (σ : Field.absoluteGaloisGroup K) {P : Torsion E p} (hP : P ∈ L) :
    representation E p σ P = (cyclotomicCharacter p σ : ZMod p) • P := by
  apply CofixedDeterminant.apply_eq_character_smul_of_cofixed (representation E p) L hline hcofixed
    (cyclotomicCharacter p) ?_ σ hP
  intro τ
  have hd := congrArg (fun χ : Field.absoluteGaloisGroup K →* (ZMod p)ˣ => (χ τ : ZMod p))
    (torsion_determinant_eq_cyclotomic E p)
  rw [determinantCharacterWithBasis_val] at hd
  exact hd.symm

/-- [DkMath.Lib] 円分スカラー作用を、同じ曲線の点群内の実際の倍点へ戻す。
mod p指標の自然数代表を使い、別の点や形式的な座標ベクトルへ置き換えない。 -/
theorem cofixed_pointAction_eq_cyclotomic_nsmul
    (L : Submodule (ZMod p) (Torsion E p)) (hline : finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn (representation E p) L)
    (σ : Field.absoluteGaloisGroup K) {P : Torsion E p} (hP : P ∈ L) :
    pointAction E σ P.val = (cyclotomicCharacter p σ : ZMod p).val • P.val := by
  have he := cofixed_torsion_apply_eq_cyclotomic_smul E p L hline hcofixed σ hP
  rw [← ZMod.natCast_zmod_val (cyclotomicCharacter p σ : ZMod p), Nat.cast_smul_eq_nsmul] at he
  exact congrArg Subtype.val he

/-- [DkMath.Lib] 同じ直線を実点群へ埋めたpointSubgroup上にも円分倍点公式が成立する。
この部分群の既存の位数p・巡回性と併用できるが、商曲線の構成とは区別する。 -/
theorem cofixed_pointSubgroup_action_eq_cyclotomic_nsmul
    (L : Submodule (ZMod p) (Torsion E p)) (hline : finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn (representation E p) L)
    (σ : Field.absoluteGaloisGroup K) {Q : Points E} (hQ : Q ∈ pointSubgroup E p L) :
    pointAction E σ Q = (cyclotomicCharacter p σ : ZMod p).val • Q := by
  obtain ⟨P, hP, rfl⟩ := hQ
  exact cofixed_pointAction_eq_cyclotomic_nsmul E p L hline hcofixed σ hP

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
