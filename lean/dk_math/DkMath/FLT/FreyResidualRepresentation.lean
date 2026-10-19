/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCounterexample
import DkMath.Lib.NumberTheory.EllipticTorsionContinuity
import DkMath.Lib.RepresentationTheory.PascalDifference

#print "file: DkMath.FLT.FreyResidualRepresentation"

/-!
# NOTE-010: 同じFrey SourceのE[p]と残余ガロア表現への入口

`Source.rationalCurve`の実際の代数閉包上のp-torsionを取り、その点への
絶対ガロア群の座標作用をFₚ線形表現として構成する。Krull位相から離散点群への
同時連続性も証明する。反例からSourceを作る場合も、同じ選択済み曲線を使う。

最小判別式の付値は同じ曲線の算術的入力として保持するが、それを慣性作用の
消滅やArtin導手と同一視しない。位数p²・次元2・行列式・既約性・有限平坦性・
不分岐性・モジュラー性は今後の別の定理である。
Pascal差分恒等式は実際の表現に適用するが、ガロア元のp乗作用に条件を置く
冪零性から、全慣性群の自明性を結論してはならない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory
open DkMath.Lib.RepresentationTheory.PascalDifference
variable {p : ℕ} (S : Source p)

/-- 同じ有理Frey曲線の、実際の幾何学的なp-torsion点群。 -/
noncomputable abbrev ResidualSpace := EllipticTorsionRepresentation.Torsion S.rationalCurve p

/-- 基底を選ばない残余ガロア表現。pの素数性は線形体として読む時に要求する。 -/
noncomputable def residualRepresentation :
    Representation (ZMod p) (Field.absoluteGaloisGroup ℚ) S.ResidualSpace :=
  EllipticTorsionRepresentation.representation S.rationalCurve p

/-- 同じ表現の可逆な線形作用素としての実現。GL₂という次元の主張は足さない。 -/
noncomputable def residualAutomorphisms :
    Field.absoluteGaloisGroup ℚ →* Units (Module.End (ZMod p) S.ResidualSpace) :=
  S.residualRepresentation.asGroupHom

/-- 可逆作用素を元のEndへ戻すと同じ表現になる。 -/
theorem residualAutomorphisms_coe (σ : Field.absoluteGaloisGroup ℚ) :
    (S.residualAutomorphisms σ : Module.End (ZMod p) S.ResidualSpace) = S.residualRepresentation σ :=
  Representation.asGroupHom_apply _ σ

/-- 表現の値を実際の曲線の点へ戻すと、同じ座標のガロア作用となる。 -/
theorem residual_underlying (σ : Field.absoluteGaloisGroup ℚ) (P : S.ResidualSpace) :
    EllipticTorsionRepresentation.underlying S.rationalCurve (S.residualRepresentation σ P) =
      EllipticTorsionRepresentation.pointAction S.rationalCurve σ
        (EllipticTorsionRepresentation.underlying S.rationalCurve P) := rfl

/-- 絶対ガロア群のKrull位相と離散E[p]について、作用は二変数で連続である。 -/
theorem residual_action_continuous :
    Continuous (fun z : Field.absoluteGaloisGroup ℚ × S.ResidualSpace => S.residualRepresentation z.1 z.2) := by
  change Continuous (fun z : Field.absoluteGaloisGroup ℚ × S.ResidualSpace => z.1 • z.2)
  fun_prop

/-- Pascal行の内部係数のp可除性を、同じ残余表現の差分へ輸送する。 -/
theorem residual_difference_pow [Fact p.Prime] (σ : Field.absoluteGaloisGroup ℚ) :
    (S.residualRepresentation σ - 1) ^ p = S.residualRepresentation (σ ^ p) - 1 :=
  representation_difference_pow _ σ

/-- 一つのガロア元のp乗が自明に作用するときの条件付き冪零性。 -/
theorem residual_difference_nilpotent [Fact p.Prime] (σ : Field.absoluteGaloisGroup ℚ)
    (hσ : S.residualRepresentation (σ ^ p) = 1) :
    (S.residualRepresentation σ - 1) ^ p = 0 :=
  difference_pow_eq_zero_of_image_pow _ σ hσ

/-- 任意の非零整数反例から、同じ曲線の実際のE[p]への連続作用と
全素数での最小判別式入力までを一つの入口で保持する。局所表現論の結論は足さない。 -/
theorem ofCounterexample_residual_entrance (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (he : a ^ p + b ^ p = c ^ p) :
    let S := Source.ofCounterexample p hp hp5 a b c ha hb hc he
    S.rationalCurve.IsElliptic ∧
      Continuous (fun z : Field.absoluteGaloisGroup ℚ × S.ResidualSpace => S.residualRepresentation z.1 z.2) ∧
      ∀ (ℓ : ℕ) [Fact ℓ.Prime],
        WeierstrassCurve.IsMinimal (FreyLocalReduction.LocalRing ℓ) S.rationalCurve ∧
        (WeierstrassCurve.HasGoodReduction (FreyLocalReduction.LocalRing ℓ) S.rationalCurve ∨
          WeierstrassCurve.HasMultiplicativeReduction (FreyLocalReduction.LocalRing ℓ) S.rationalCurve) ∧
        ((p : ℤ) ∣ padicValRat ℓ S.rationalCurve.Δ ↔ ℓ ≠ 2) := by
  let S := Source.ofCounterexample p hp hp5 a b c ha hb hc he
  have h := Source.ofCounterexample_local_profile p hp hp5 a b c ha hb hc he
  exact ⟨h.1, S.residual_action_continuous, h.2⟩

end DkMath.FLT.Frey.Source
