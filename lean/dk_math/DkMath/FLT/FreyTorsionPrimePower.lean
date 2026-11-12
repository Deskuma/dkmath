/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTorsionAllCard
import DkMath.Lib.NumberTheory.EllipticTorsionPrimePower
import DkMath.Lib.NumberTheory.EllipticTorsionNonSplit

#print "file: DkMath.FLT.FreyTorsionPrimePower"

/-!
# 同じFrey曲線の素数冪自由加群と非分裂な塔

Sourceの指数pと、ねじれ点を調べる素数qを独立に扱う。
同じ実際の有理曲線上でE[qᵏ]の二元基底・線形座標同型と、q²の列の非分裂性を供給する。
各段の自由性は、段間の直和分解や互換的な基底の選択とは異なる。
Weil対・円分行列式の無条件化・Tate加群の構成はこの章の結論に含めない。
-/
namespace DkMath.FLT.Frey.Source
open Module DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
variable {p : ℕ} (S : Source p) (q : ℕ) [Fact q.Prime]

/-- 同じSourceの曲線のq冪ねじれ点の線形座標同型。非標準的な選択である。 -/
noncomputable def curve_primePowerEquiv (k : ℕ) :
    Torsion S.rationalCurve (q ^ k) ≃ₗ[ZMod (q ^ k)] (Fin 2 → ZMod (q ^ k)) := by
  have := S.rationalCurve_isElliptic
  exact primePowerEquiv S.rationalCurve q k

/-- 同じ実際の点群の二元基底。k=0では係数環も零環である。 -/
noncomputable def curve_primePowerBasis (k : ℕ) :
    Basis (Fin 2) (ZMod (q ^ k)) (Torsion S.rationalCurve (q ^ k)) :=
  Basis.ofEquivFun (S.curve_primePowerEquiv q k)

/-- 各段の自由性。 -/
theorem curve_primePower_free (k : ℕ) : Module.Free (ZMod (q ^ k)) (Torsion S.rationalCurve (q ^ k)) :=
  Module.Free.of_basis (S.curve_primePowerBasis q k)

/-- 正指数では自由階数は2である。 -/
theorem curve_primePower_finrank (k : ℕ) :
    finrank (ZMod (q ^ (k + 1))) (Torsion S.rationalCurve (q ^ (k + 1))) = 2 := by
  have := S.rationalCurve_isElliptic
  exact primePower_finrank S.rationalCurve q k

/-- 塔の全ての遷移は、同じ曲線上の全射なq倍写像である。 -/
theorem curve_primePower_transition_surjective (k : ℕ) :
    Function.Surjective (primePowerTransition S.rationalCurve q k) := by
  have := S.rationalCurve_isElliptic
  exact primePowerTransition_surjective S.rationalCurve q k

/-- 同じ曲線のq²-torsionは、位数ちょうどq²の点を含む。 -/
theorem curve_prime_square_order : ∃ P : Torsion S.rationalCurve (q * q), addOrderOf P = q ^ 2 := by
  have := S.rationalCurve_isElliptic
  exact exists_prime_square_order S.rationalCurve q

/-- q²の制限倍写像は加法準同型による右逆を持たない。 -/
theorem curve_prime_square_no_section :
    ¬ ∃ s : Torsion S.rationalCurve q →+ Torsion S.rationalCurve (q * q),
      Function.RightInverse s (torsionMultiply S.rationalCurve q q) := by
  have := S.rationalCurve_isElliptic
  exact prime_square_no_additive_section S.rationalCurve q

/-- 各段が自由でも、q²の群は二つのq-torsion群の直積にはならない。 -/
theorem curve_prime_square_not_product :
    ¬ Nonempty (Torsion S.rationalCurve (q * q) ≃+
      (Torsion S.rationalCurve q × Torsion S.rationalCurve q)) := by
  have := S.rationalCurve_isElliptic
  exact prime_square_not_product S.rationalCurve q

end DkMath.FLT.Frey.Source
