/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.FreyFiniteKernelDepthProduct
import DkMath.FLT.FreyDyadicZeroComponent
import DkMath.FLT.FreyPrimeProfile
import DkMath.Lib.NumberTheory.EllipticFiniteKernelDiscriminantProduct

#print "file: DkMath.FLT.FreyFiniteKernelDiscriminantDepth"

/-!
# Frey Source からの判別式積供給

一般の奇数有限核に対して証明済みの `kernelModel_discriminant_product_of_odd_card` を、
Frey Source の `pointSubgroup` と `residualKernelModel` へ特殊化する。これにより、
既存の特異・滑らか枝の局所付値定理から `hprod` を利用側の仮定として取り除ける。

このファイルが証明するのは Source 固有のモデル同一視と局所付値輸送である。
`q ≠ p`、還元の特異・滑らか条件、一次元残余核などの局所仮定は保持し、`hno` や
大域的な有理捩れ排除を主張しない。
-/

namespace DkMath.FLT.Frey.Source

open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation
open EllipticGoodReductionSeparation ValuationInertia ValuationPrimeSupport
open ValuationRationalPrimeSupport
open DkMath.Lib.RepresentationTheory

noncomputable local instance instDecidableEqFreyFiniteKernelDiscriminantDepth
    {α : Type*} : DecidableEq α := Classical.decEq _

variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic

/-- [DkMath.Lib] Frey の一次元残余核に対する `hprod` を一般奇数核定理から供給する。 -/
theorem residual_kernel_discriminant_product (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace)
    (hl : Module.finrank (ZMod p) L = 1) :
    letI := S.finite_residualPointSubgroup L hl
    letI := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
    (S.residualKernelModel L hl).Δ *
        (∏ Q : halfKernel S.rationalCurve (pointSubgroup S.rationalCurve p L),
          (2 * Q.val.val.yc +
            (S.rationalCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).a₁ * Q.val.val.xc +
            (S.rationalCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).a₃) ^ 2) ^ 4 =
      (S.rationalCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).Δ ^ p := by
  let := S.finite_residualPointSubgroup L hl
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  have ho := S.residual_pointSubgroup_odd hp2 L hl
  have h := kernelModel_discriminant_product_of_odd_card
    S.rationalCurve (pointSubgroup S.rationalCurve p L) ho
  rw [card_pointSubgroup S.rationalCurve p L hl] at h
  simpa [residualKernelModel] using h

/-- [DkMath.Lib] Frey 特異枝の付値関係。`hprod` は内部で構成する。 -/
theorem residual_singular_discriminant_value (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace)
    (hl : Module.finrank (ZMod p) L = 1)
    {q : ℕ} [Fact q.Prime] (hqp : q ≠ p)
    (hbad : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hd : Disjoint L (S.residualZeroComponent A)) :
    A.valuation (S.residualKernelModel L hl).Δ ^ p =
      A.valuation (S.rationalCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).Δ := by
  let := S.finite_residualPointSubgroup L hl
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact residual_singular_discriminant_value_of_product_identity S hp5 L hl hqp hbad A hA hd
    (residual_kernel_discriminant_product S (by omega) L hl)

/-- [DkMath.Lib] Frey 滑らか枝の付値関係。`hprod` は内部で構成する。 -/
theorem residual_smooth_discriminant_value (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace)
    (hl : Module.finrank (ZMod p) L = 1)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hle : L ≤ S.residualZeroComponent A) :
    A.valuation (S.residualKernelModel L hl).Δ =
      A.valuation (S.rationalCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).Δ ^ p := by
  let := S.finite_residualPointSubgroup L hl
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact residual_smooth_discriminant_value_of_product_identity S hp2 L hl hq hqp A hA hle
    (residual_kernel_discriminant_product S hp2 L hl)

/-- [DkMath.Lib] `q ≠ p` で整数標的と代数閉包上の商標的の判別式付値を同一視する。

整数モデルと付値環モデルの比較、付値環モデルと `residualKernelModel` の基底変換を
順に合成する。整数化の分母や商曲線の再構成をここで再証明せず、既存の二つのモデル
比較定理だけを消費する教材用の橋である。
-/
theorem residual_integer_kernel_discriminant_value_eq (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace)
    (hl : Module.finrank (ZMod p) L = 1)
    (hs : IsStable S.residualRepresentation L)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : LiesOverPrime A q) :
    A.valuation ((S.residualIntegerKernelModel L hl hs).Δ : AlgebraicClosure ℚ) =
      A.valuation (S.residualKernelModel L hl).Δ := by
  have hv := S.residual_integer_valuation_kernel_values hp2 L hl hs hq hqp A hA
  have hm := S.residual_valuation_kernel_model_map hp2 L hl hq hqp A hA
  have hd := congrArg WeierstrassCurve.Δ hm
  rw [map_Δ] at hd
  exact hv.1.trans (congrArg A.valuation hd)

/-- [DkMath.Lib] Frey 特異枝の判別式深さを整数標的へ輸送する。

`residual_singular_discriminant_value` の左辺を、直前のモデル比較等式で一度だけ
置換する。整数モデルの局所最小性や `hno` の大域算術はこの定理の結論に含めない。
-/
theorem residual_integer_singular_discriminant_value (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace)
    (hl : Module.finrank (ZMod p) L = 1)
    (hs : IsStable S.residualRepresentation L)
    {q : ℕ} [Fact q.Prime] (hqp : q ≠ p)
    (hbad : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hd : Disjoint L (S.residualZeroComponent A)) :
    A.valuation ((S.residualIntegerKernelModel L hl hs).Δ : AlgebraicClosure ℚ) ^ p =
      A.valuation (S.rationalCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).Δ := by
  have hq : q.Prime := Fact.out
  have hsrc := residual_singular_discriminant_value S hp5 L hl hqp hbad A hA hd
  have hbridge := residual_integer_kernel_discriminant_value_eq S (by omega) L hl hs hq hqp A hA
  rw [hbridge]
  exact hsrc

/-- [DkMath.Lib] Frey 滑らか枝の判別式深さを整数標的へ輸送する。 -/
theorem residual_integer_smooth_discriminant_value (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace)
    (hl : Module.finrank (ZMod p) L = 1)
    (hs : IsStable S.residualRepresentation L)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hle : L ≤ S.residualZeroComponent A) :
    A.valuation ((S.residualIntegerKernelModel L hl hs).Δ : AlgebraicClosure ℚ) =
      A.valuation (S.rationalCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).Δ ^ p := by
  have hsrc := residual_smooth_discriminant_value S hp2 L hl hq hqp A hA hle
  have hbridge := residual_integer_kernel_discriminant_value_eq S hp2 L hl hs hq hqp A hA
  rw [hbridge]
  exact hsrc

/-- [DkMath.Lib] 素数 `p ≥ 5` では、2で特異核となる安定一次元核は存在しない。

整数標的の特異枝深さを `padicValInt` の指数へ戻し、源判別式の `-8 mod p` と衝突させる。
この定理は `q = p` の局所理論や `hno` を仮定せず、2上の特異枝だけを排除する。
-/
theorem residual_disjoint_kernel_impossible_at_two (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace)
    (hl : Module.finrank (ZMod p) L = 1)
    (hs : IsStable S.residualRepresentation L)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : LiesOverPrime A 2) :
    ¬ Disjoint L (S.residualZeroComponent A) := by
  intro hd
  have hp2 : p ≠ 2 := by omega
  have hdepth := residual_integer_singular_discriminant_value S hp5 L hl hs
    (q := 2) (by omega) (Or.inl rfl) A hA hd
  have hΔZ := residual_integer_kernel_model_discriminant_ne_zero S hp2 L hl hs
  have hΔA : A.valuation ((S.residualIntegerKernelModel L hl hs).Δ : AlgebraicClosure ℚ) =
      A.valuation (2 : AlgebraicClosure ℚ) ^
        padicValInt 2 (S.residualIntegerKernelModel L hl hs).Δ :=
    valuation_intCast_eq_pow_padicValInt A Nat.prime_two
      ((ValuationSubring.mem_nonunits_iff _).mp hA) hΔZ
  have hcurveA : A.valuation (S.rationalCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).Δ =
      A.valuation (S.curve.Δ : AlgebraicClosure ℚ) := by
    have h := congrArg
      (fun W : WeierstrassCurve ℚ => A.valuation (W.map (algebraMap ℚ (AlgebraicClosure ℚ))).Δ)
      S.curve_map
    simpa only [map_map, map_Δ, RingHom.coe_comp, Function.comp_apply,
      Int.coe_castRingHom, map_intCast] using h.symm
  rw [hΔA, hcurveA] at hdepth
  rw [valuation_intCast_eq_pow_padicValInt A Nat.prime_two
      ((ValuationSubring.mem_nonunits_iff _).mp hA) S.curve_discriminant_ne_zero] at hdepth
  rw [← pow_mul] at hdepth
  have hval_lt : A.valuation (2 : AlgebraicClosure ℚ) < 1 :=
    (ValuationSubring.mem_nonunits_iff _).mp hA
  have hval_ne_one : A.valuation (2 : AlgebraicClosure ℚ) ≠ 1 :=
    ne_of_lt hval_lt
  have hval_ne_zero : A.valuation (2 : AlgebraicClosure ℚ) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (Nat.cast_ne_zero.mpr Nat.prime_two.ne_zero)
  have hexp : padicValInt 2 (S.residualIntegerKernelModel L hl hs).Δ * p =
      padicValInt 2 S.curve.Δ := by
    exact (IsMulTorsionFree.pow_right_injective₀ hval_ne_one hval_ne_zero) hdepth
  have hdvd : p ∣ padicValInt 2 S.curve.Δ := by
    rw [← hexp]
    exact dvd_mul_left _ _
  exact S.not_exponent_dvd_curve_two_valuation hp5 hdvd

/-- [DkMath.Lib] `p ≥ 5` の安定一次元核は、2上では必ず零成分に入る。

`residual_line_smooth_or_disjoint` の二分法に、直前の特異枝排除を重ねる。
ここで得るのは局所的な包含であり、残余表現全体の `hno` や大域的な捩れ排除ではない。
-/
theorem residual_stable_line_le_zeroComponent_at_two (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace)
    (hl : Module.finrank (ZMod p) L = 1)
    (hs : IsStable S.residualRepresentation L)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : LiesOverPrime A 2) :
    L ≤ S.residualZeroComponent A := by
  rcases S.residual_line_smooth_or_disjoint L hl A with hle | hd
  · exact hle
  · exact (residual_disjoint_kernel_impossible_at_two S hp5 L hl hs A hA hd).elim

/-- [DkMath.Lib] 2上の安定一次元核は、零成分の一次元性により一致する。

直前の包含と `residualZeroComponent_finrank_eq_one_at_two` を
`Submodule.eq_of_le_of_finrank_le` で組み合わせる。これは局所住所での同定であり、
大域的な `hno` や Cofixed 性を追加しない。
-/
theorem residual_stable_line_eq_zeroComponent_at_two (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace)
    (hl : Module.finrank (ZMod p) L = 1)
    (hs : IsStable S.residualRepresentation L)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : LiesOverPrime A 2) :
    L = S.residualZeroComponent A := by
  exact Submodule.eq_of_le_of_finrank_le
    (residual_stable_line_le_zeroComponent_at_two S hp5 L hl hs A hA)
    (by rw [S.residualZeroComponent_finrank_eq_one_at_two hp5 A hA, hl])

end DkMath.FLT.Frey.Source
