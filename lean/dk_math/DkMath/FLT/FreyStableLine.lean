/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyGeometricWeilPairing
import DkMath.Lib.NumberTheory.EllipticStableLine
import DkMath.Lib.NumberTheory.FoldedValuationOrbit

#print "file: DkMath.FLT.FreyStableLine"

/-!
# NOTE-029: 同じFrey Sourceの安定直線とcofixedへの条件付き接続

029-Aは幾何学的な次元2だけで閉じる。可約性から得られる部分群は、元の曲線の
実際の点でできており、位数p・巡回性・ガロア安定性を持つ。
029-Bの局所慣性による二択と、029-Cの有理p-torsion排除はまだ算術入力である。
両方を供給すれば、一般の降下と線形代数だけでcofixed直線へ進める。

`Source p`自体はp≥5やa≡3 mod4・bの偶数性をフィールドとして保持しない。
これらを暗黙に補うことはしない。将来の2進付値論では`FreyCounterexample`の
向き付け付き存在定理から条件を取り出す必要がある。このファイルは指数に関する
例外分岐を使わず、既約性や一般FLTの完成を主張しない。
-/

namespace DkMath.FLT.Frey.Source
open Module
open DkMath.Lib.NumberTheory EllipticTorsionRepresentation CyclotomicRootModule
open DkMath.Lib.RepresentationTheory
variable {p : ℕ} (S : Source p) [Fact p.Prime]

/-- 同じ残余空間の可約性から、実際の位数pの安定巡回部分群を得る029-A。 -/
theorem residual_exists_stable_pointSubgroup (hred : ¬ S.ResidualIsIrreducible) :
    ∃ L : Submodule (ZMod p) S.ResidualSpace, Module.finrank (ZMod p) L = 1 ∧
      S.IsGaloisStable L ∧ Nat.card (pointSubgroup S.rationalCurve p L) = p ∧
      IsAddCyclic (pointSubgroup S.rationalCurve p L) ∧
      (∀ P ∈ pointSubgroup S.rationalCurve p L, p • P = 0) ∧
      (∀ σ P, P ∈ pointSubgroup S.rationalCurve p L →
        pointAction S.rationalCurve σ P ∈ pointSubgroup S.rationalCurve p L) := by
  have := S.rationalCurve_isElliptic
  exact exists_stable_pointSubgroup_of_reducible S.rationalCurve p hred

omit [Fact p.Prime] in
/-- ガロア固定残余点の不存在は、同じ正規化Frey曲線の有理p-torsion排除と同値。 -/
theorem residual_noNonzeroFixed_iff_rational_torsion :
    NoNonzeroFixed S.residualRepresentation ↔
      ∀ Q : S.rationalCurve.toAffine.Point, p • Q = 0 → Q = 0 :=
  noNonzeroFixed_iff_rational_torsion S.rationalCurve p

/-- 二択と有理torsion排除を別に証明した場合のcofixed直線。
二入力は未解決の算術を表し、この条件付き結論を無条件の既約性とは呼ばない。 -/
theorem residual_exists_cofixed_line (hred : ¬ S.ResidualIsIrreducible)
    (hcases : ∀ L : Submodule (ZMod p) S.ResidualSpace, Module.finrank (ZMod p) L = 1 →
      S.IsGaloisStable L → IsFixedOn S.residualRepresentation L ∨ IsCofixedOn S.residualRepresentation L)
    (hrat : ∀ Q : S.rationalCurve.toAffine.Point, p • Q = 0 → Q = 0) :
    ∃ L : Submodule (ZMod p) S.ResidualSpace, Module.finrank (ZMod p) L = 1 ∧
      S.IsGaloisStable L ∧ IsCofixedOn S.residualRepresentation L := by
  have := S.rationalCurve_isElliptic
  exact exists_cofixed_line_of_reducible S.rationalCurve p hred hcases hrat

/-- 将来の既約性証明の三つの算術入力を、同じSourceで固定する。
cofixed直線の不存在は、固定点の不存在だけでは代用できない。 -/
theorem residual_isIrreducible_of_no_cofixed_line
    (hcases : ∀ L : Submodule (ZMod p) S.ResidualSpace, Module.finrank (ZMod p) L = 1 →
      S.IsGaloisStable L → IsFixedOn S.residualRepresentation L ∨ IsCofixedOn S.residualRepresentation L)
    (hrat : ∀ Q : S.rationalCurve.toAffine.Point, p • Q = 0 → Q = 0)
    (hno : ¬ ∃ L : Submodule (ZMod p) S.ResidualSpace, Module.finrank (ZMod p) L = 1 ∧
      S.IsGaloisStable L ∧ IsCofixedOn S.residualRepresentation L) : S.ResidualIsIrreducible :=
  isIrreducible_of_no_cofixed_line S.residualRepresentation S.residual_finrank_eq_two hcases
    (S.residual_noNonzeroFixed_iff_rational_torsion.mpr hrat) hno

/-- 安定直線への適合基底では対角成分の積が実際の円分指標になる。
NOTE-028の幾何学的Weil対から供給し、対データを追加仮定に取らない。 -/
theorem residual_stable_line_diagonal_product
    (b : Basis (Fin 2) (ZMod p) S.ResidualSpace)
    (hstable : S.IsGaloisStable (Submodule.span (ZMod p) ({b 0} : Set S.ResidualSpace)))
    (σ : Field.absoluteGaloisGroup ℚ) :
    (S.residualGL2WithBasis b σ : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 *
      (S.residualGL2WithBasis b σ : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1 =
        (cyclotomicCharacter p σ : ZMod p) :=
  S.residual_stable_line_diagonal_product_of_pairing S.residual_geometricWeilPairingData b hstable σ

/-- 有理torsion排除の付値軌道に現れる法の約分。上下界・加法公式はまだ供給しない。 -/
theorem residual_valuation_modulus_cancel (hp2 : p ≠ 2) (m : ℤ)
    (hm : 2 * ((p : ℤ) * (padicValInt 2 S.b : ℤ) - 4) ∣ (p : ℤ) * m) :
    2 * ((p : ℤ) * (padicValInt 2 S.b : ℤ) - 4) ∣ m :=
  FoldedValuationOrbit.cancel_prime_modulus p Fact.out hp2 (padicValInt 2 S.b) m hm

end DkMath.FLT.Frey.Source
