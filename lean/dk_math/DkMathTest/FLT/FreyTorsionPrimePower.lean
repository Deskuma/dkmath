/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTorsionPrimePower
import DkMathTest.FLT.FreyResidualRepresentation

#print "file: DkMathTest.FLT.FreyTorsionPrimePower"

/-!
# NOTE-020: 実在する曲線の37冪の自由性と、同じ位数でも非同型な二つの群

Source 2の曲線を固定し、そのE[37²]とE[37³]の構造を検査する。
自由加群同型は同じ点の持ち上げから構成され、移したガロア作用と同変になる。
一方、E[37²]とE[37]×E[37]は同じ位数でも非同型であり、加法的sectionも存在しない。
素数2と指数0も検査し、正指数での階数2と零環上の退化した段を区別する。
-/
namespace FreyTorsionPrimePowerTest
open Module
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open FreyResidualRepresentationTest
local instance : sample.rationalCurve.IsElliptic := sample.rationalCurve_isElliptic
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

/-- 仮想Source 37によらず、同じ実在する曲線の37²-torsionはZMod 1369上の二元自由加群。 -/
theorem actual37square_equiv :
    Nonempty (Torsion sample.rationalCurve (37 ^ 2) ≃ₗ[ZMod (37 ^ 2)] (Fin 2 → ZMod (37 ^ 2))) :=
  ⟨primePowerEquiv sample.rationalCurve 37 2⟩

/-- 37³も同じ一般定理で自由である。係数環を体と仮定しない。 -/
theorem actual37cube_free : Module.Free (ZMod (37 ^ 3)) (Torsion sample.rationalCurve (37 ^ 3)) :=
  primePower_free _ 37 3

/-- 正指数の有限自由階数は2。 -/
theorem actual37cube_rank : finrank (ZMod (37 ^ 3)) (Torsion sample.rationalCurve (37 ^ 3)) = 2 :=
  primePower_finrank _ 37 2

/-- 素数2の4-torsionもZMod 4上の二元自由加群となる。 -/
theorem actual4_free : Module.Free (ZMod (2 ^ 2)) (Torsion sample.rationalCurve (2 ^ 2)) :=
  primePower_free _ 2 2

/-- 指数0ではp⁰=1であり、実際の群は零群である。階数2という正指数の主張と混同しない。 -/
theorem zero_stage_all_zero (P : Torsion sample.rationalCurve (37 ^ 0)) : P = 0 :=
  torsion_one_eq_zero _ P

/-- 零環上の零加群同士についても、一般の座標同型は定義される。 -/
theorem zero_stage_equiv :
    Nonempty (Torsion sample.rationalCurve (37 ^ 0) ≃ₗ[ZMod (37 ^ 0)] (Fin 2 → ZMod (37 ^ 0))) :=
  ⟨primePowerEquiv sample.rationalCurve 37 0⟩

/-- 選ばれた37²-torsion点の37倍は、元の実際の37-torsionの基底に一致する。 -/
theorem actual37square_lifts (i : Fin 2) :
    37 • (primePowerLifts sample.rationalCurve 37 1 i).val = (torsionBasis sample.rationalCurve 37 i).val :=
  primePowerLifts_spec _ 37 1 i

/-- 選ばれた第一持ち上げは、座標同型の逆による(1,0)の像そのものである。 -/
theorem actual37square_first_coordinate :
    (primePowerSuccEquiv sample.rationalCurve 37 1).symm ![1, 0] = primePowerLifts sample.rationalCurve 37 1 0 := by
  rw [primePowerSuccEquiv_symm_apply]
  simp

/-- 最高段の基底を持ち上げる任意の二点から、同じ構造同型を作れる。 -/
theorem any_lifts_bijective (P : Fin 2 → Torsion sample.rationalCurve (37 ^ 2))
    (hP : ∀ i, 37 • (P i).val = (torsionBasis sample.rationalCurve 37 i).val) :
    Function.Bijective (primePowerPresentation sample.rationalCurve 37 1 P) :=
  primePowerPresentation_bijective _ 37 1 P hP

/-- 実際の37²→37の遷移は全射である。 -/
theorem actual37square_transition_surjective :
    Function.Surjective (primePowerTransition sample.rationalCurve 37 1) :=
  sample.curve_primePower_transition_surjective 37 1

/-- 同じ遷移はガロア作用と可換する。 -/
theorem actual37square_transition_equivariant (σ : Field.absoluteGaloisGroup ℚ)
    (P : Torsion sample.rationalCurve (37 ^ 2)) :
    primePowerTransition sample.rationalCurve 37 1 (representation sample.rationalCurve (37 ^ 2) σ P) =
      representation sample.rationalCurve 37 σ (primePowerTransition sample.rationalCurve 37 1 P) :=
  primePowerTransition_equivariant _ 37 1 σ P

/-- 自由加群同型には、元の同じガロア作用を運ぶ。自明な表現に置き換えない。 -/
theorem actual37square_coordinate_equivariant (σ : Field.absoluteGaloisGroup ℚ)
    (P : Torsion sample.rationalCurve (37 ^ 2)) :
    primePowerEquiv sample.rationalCurve 37 2 (representation sample.rationalCurve (37 ^ 2) σ P) =
      primePowerCoordinateRepresentation sample.rationalCurve 37 2 σ (primePowerEquiv sample.rationalCurve 37 2 P) :=
  primePowerCoordinate_equivariant _ 37 2 σ P

/-- 実在する同じ群の中に位数1369の点がある。 -/
theorem actual37square_order : ∃ P : Torsion sample.rationalCurve (37 * 37), addOrderOf P = 1369 :=
  sample.curve_prime_square_order 37

/-- 同じ位数でも直積にはならない。 -/
theorem same_card_not_product :
    Nat.card (Torsion sample.rationalCurve (37 * 37)) =
      Nat.card (Torsion sample.rationalCurve 37 × Torsion sample.rationalCurve 37) ∧
    ¬ Nonempty (Torsion sample.rationalCurve (37 * 37) ≃+
      (Torsion sample.rationalCurve 37 × Torsion sample.rationalCurve 37)) := by
  constructor
  · rw [card_torsion_sq _ _ (by decide), Nat.card_prod, card_torsion_sq _ 37 (by decide), mul_pow]
  · exact sample.curve_prime_square_not_product 37

/-- 37²の短完全列は、加法準同型のsectionを持たない。 -/
theorem actual37square_no_section :
    ¬ ∃ s : Torsion sample.rationalCurve 37 →+ Torsion sample.rationalCurve (37 * 37),
      Function.RightInverse s (torsionMultiply sample.rationalCurve 37 37) :=
  sample.curve_prime_square_no_section 37

/-- 素数2でも非分裂性は成立する。 -/
theorem actual4_not_product :
    ¬ Nonempty (Torsion sample.rationalCurve (2 * 2) ≃+
      (Torsion sample.rationalCurve 2 × Torsion sample.rationalCurve 2)) :=
  sample.curve_prime_square_not_product 2

end FreyTorsionPrimePowerTest
