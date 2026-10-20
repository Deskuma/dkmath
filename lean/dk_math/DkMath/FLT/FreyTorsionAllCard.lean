/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidualGeometry
import DkMath.Lib.NumberTheory.EllipticTorsionAllCard

#print "file: DkMath.FLT.FreyTorsionAllCard"

/-!
# 同じFrey曲線の全指数ねじれ点の位数と短完全列

Sourceの指数pと、調べるねじれ点の指数nは別のものである。
同じ有理曲線について任意のn≠0の位数n²を供給し、以前の有限レベルとまとめる。
特に素数pの残余空間だけでなくp冪、合成数、n=1にも適用できる。
Sourceの指数に一致させる場合も、必要な条件はp≠0であり素数性ではない。
Weil対・既約性・Tate加群の自由性や階数をここから先取りしない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
variable {p : ℕ} (S : Source p)

/-- 同じSourceの曲線の全ての正指数ねじれ点の位数。 -/
theorem curve_torsion_card_sq (n : ℕ) (hn : n ≠ 0) :
    Nat.card (Torsion S.rationalCurve n) = n ^ 2 := by
  have := S.rationalCurve_isElliptic
  exact card_torsion_sq S.rationalCurve n hn

/-- Sourceの指数とtorsion指数を一致させても、素数性を要求しない。 -/
theorem residual_card_sq (hp : p ≠ 0) : Nat.card S.ResidualSpace = p ^ 2 :=
  S.curve_torsion_card_sq p hp

/-- 同じ実際の曲線のねじれ点の位数の乗法性。互いに素性は不要。 -/
theorem curve_torsion_card_mul (m n : ℕ) (hn : n ≠ 0) :
    Nat.card (Torsion S.rationalCurve (m * n)) =
      Nat.card (Torsion S.rationalCurve m) * Nat.card (Torsion S.rationalCurve n) := by
  have := S.rationalCurve_isElliptic
  exact card_torsion_mul S.rationalCurve m n hn

/-- 全ての非零底の自然数冪における同じ位数公式。k=0も含める。 -/
theorem curve_torsion_pow_card (n k : ℕ) (hn : n ≠ 0) :
    Nat.card (Torsion S.rationalCurve (n ^ k)) = n ^ (2 * k) := by
  have := S.rationalCurve_isElliptic
  exact card_torsion_pow S.rationalCurve n k hn

/-- 有限性・単射・完全性・全射性を同じ点群と二つの写像でまとめる。 -/
theorem curve_torsion_finite_short_exact (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    Finite (Torsion S.rationalCurve (m * n)) ∧
      Function.Injective (torsionInclusion S.rationalCurve m n) ∧
      Function.Exact (torsionInclusion S.rationalCurve m n) (torsionMultiply S.rationalCurve m n) ∧
      Function.Surjective (torsionMultiply S.rationalCurve m n) := by
  have := S.rationalCurve_isElliptic
  exact torsion_finite_short_exact S.rationalCurve m n hm hn

/-- 任意の正指数について、正確な位数と同じ表現の有限レベルを同時に供給する。 -/
theorem curve_torsion_card_finite_level (n : ℕ) (hn : n ≠ 0) :
    Nat.card (Torsion S.rationalCurve n) = n ^ 2 ∧ FactorsThroughFiniteLevel S.rationalCurve n := by
  have := S.rationalCurve_isElliptic
  exact ⟨S.curve_torsion_card_sq n hn, factorsThroughFiniteLevel_of_ne_zero S.rationalCurve n hn⟩

end DkMath.FLT.Frey.Source
