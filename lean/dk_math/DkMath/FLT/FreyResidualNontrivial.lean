/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidualDimensionBound
import DkMath.Lib.NumberTheory.EllipticTorsionNontrivial

#print "file: DkMath.FLT.FreyResidualNontrivial"

/-!
# 同じFrey曲線の残余空間は零空間ではない

Source.rationalCurveの楕円曲線性を、根から非零torsion点を作る一般定理へ供給する。
素数pでは有限性・非零点・位数を仮定せず、同じ残余空間の次元が1か2であると分かる。
NOTE-013の上界と合わせ、p≤|E[p]|≤p²と既存の有限レベルを保持する。
非零のベクトルが存在することと、既約性に必要な非零の安定直線の有無は別の問題である。
次元2・GL₂実現・Weil対・行列式・既約性は今回の結論に含めない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
variable {p : ℕ} (S : Source p) [Fact p.Prime]

/-- 同じSourceの楕円曲線性から実際の非零p-torsion点を得る。 -/
theorem residual_exists_ne_zero : ∃ P : S.ResidualSpace, P ≠ 0 := by
  have := S.rationalCurve_isElliptic
  exact exists_nonzero_torsion_of_one_lt S.rationalCurve p (Fact.out : p.Prime).one_lt

/-- 人工的な二点集合ではなく、同じ実際の残余空間のNontrivialを供給する。 -/
theorem residual_nontrivial : Nontrivial S.ResidualSpace := by
  have := S.rationalCurve_isElliptic
  infer_instance

/-- 残余空間の次元は正である。楕円曲線性はSourceから供給する。 -/
theorem residual_finrank_pos : 0 < Module.finrank (ZMod p) S.ResidualSpace := by
  have := S.rationalCurve_isElliptic
  exact finrank_torsion_pos S.rationalCurve p

/-- 上下の評価を同じSource上で保持する。下界は1であり、2ではない。 -/
theorem residual_finrank_bounds :
    1 ≤ Module.finrank (ZMod p) S.ResidualSpace ∧
      Module.finrank (ZMod p) S.ResidualSpace ≤ 2 :=
  ⟨S.residual_finrank_pos, S.residual_finrank_le_two⟩

/-- 楕円曲線性を持つFrey曲線では、次元0の候補を取り除ける。 -/
theorem residual_finrank_one_or_two :
    Module.finrank (ZMod p) S.ResidualSpace = 1 ∨
      Module.finrank (ZMod p) S.ResidualSpace = 2 := by
  have := S.rationalCurve_isElliptic
  exact finrank_torsion_one_or_two S.rationalCurve p

/-- 位数の候補はpかp²。正確にp²個あることはまだ結論しない。 -/
theorem residual_card_prime_or_prime_sq :
    Nat.card S.ResidualSpace = p ∨ Nat.card S.ResidualSpace = p ^ 2 := by
  have := S.rationalCurve_isElliptic
  exact card_torsion_prime_or_prime_sq S.rationalCurve p

/-- 同じ曲線の実際の点数に、pとp²による上下の評価を与える。 -/
theorem residual_card_bounds : p ≤ Nat.card S.ResidualSpace ∧ Nat.card S.ResidualSpace ≤ p ^ 2 := by
  have := S.rationalCurve_isElliptic
  exact card_torsion_bounds S.rationalCurve p

/-- 次元の上下界・点数の上下界・有限レベルを、追加の幾何学的仮定なしでまとめる。 -/
theorem residual_nontrivial_profile :
    (1 ≤ Module.finrank (ZMod p) S.ResidualSpace ∧
      Module.finrank (ZMod p) S.ResidualSpace ≤ 2) ∧
      (p ≤ Nat.card S.ResidualSpace ∧ Nat.card S.ResidualSpace ≤ p ^ 2) ∧
      S.ResidualFactorsThroughFiniteLevel :=
  ⟨S.residual_finrank_bounds, S.residual_card_bounds,
    S.residual_factorsThroughFiniteLevel_of_prime⟩

end DkMath.FLT.Frey.Source
