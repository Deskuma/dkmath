/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFunctionEigenvalue

#print "file: DkMath.Lib.NumberTheory.EllipticPointOrderAlgebra"

/-!
# 全点の位数の積法則と定数判定

同じ実際の付値の乗法性を−logで読み、非零関数の積の位数を和へ送る。
有限積も帰納で処理する。全点で位数0なら、関数1との比較をNOTE-025へ渡して
一意な非零定数を得る。零関数の位数は定義せず、全ての積で非零性を明示する。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open WeierstrassCurve WeierstrassCurve.Affine WithZero
variable {K : Type*} [Field K] (E : WeierstrassCurve K) [E.IsElliptic]

/-- 非零関数の積の位数は和。有限点とOの両方を同じ付値の乗法性で扱う。 -/
theorem pointOrder_mul (P : Points E) (f g : (E.toAffine⁄(AlgebraicClosure K)).FunctionField)
    (hf : f ≠ 0) (hg : g ≠ 0) :
    pointOrder E P (f * g) (mul_ne_zero hf hg) = pointOrder E P f hf + pointOrder E P g hg := by
  rw [pointOrder_eq_neg_log, pointOrder_eq_neg_log, pointOrder_eq_neg_log, map_mul,
    log_mul ((pointValuation E P).ne_zero_iff.mpr hf) ((pointValuation E P).ne_zero_iff.mpr hg)]
  omega

/-- 関数1の位数は全点で0である。 -/
theorem pointOrder_one (P : Points E) :
    pointOrder E P (1 : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) one_ne_zero = 0 := by
  rw [pointOrder_eq_neg_log, map_one, log_one, neg_zero]

/-- 全ての因子が非零の有限積の位数は、各因子の位数の有限和である。 -/
theorem pointOrder_prod {ι : Type*} (P : Points E) (s : Finset ι)
    (f : ι → (E.toAffine⁄(AlgebraicClosure K)).FunctionField) (hf : ∀ i, f i ≠ 0) :
    pointOrder E P (∏ i ∈ s, f i) (Finset.prod_ne_zero_iff.mpr (fun i _ => hf i)) =
      ∑ i ∈ s, pointOrder E P (f i) (hf i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Finset.sum_empty, pointOrder_one]
  | @insert a s ha ih =>
    have hs : (∏ i ∈ s, f i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hf i)
    calc
      _ = pointOrder E P (f a * ∏ i ∈ s, f i) (mul_ne_zero (hf a) hs) := by
        rw [pointOrder_eq_neg_log, pointOrder_eq_neg_log]
        exact congrArg (fun z => -log (pointValuation E P z)) (Finset.prod_insert ha)
      _ = pointOrder E P (f a) (hf a) + pointOrder E P (∏ i ∈ s, f i) hs :=
        pointOrder_mul E P _ _ (hf a) hs
      _ = _ := by rw [ih, Finset.sum_insert ha]

/-- 全点で位数0の非零関数は、一意な係数体の単元に一致する。
NOTE-025の一般の比例定数判定を、比較する関数g=1に適用する。 -/
theorem existsUnique_unit_of_pointOrder_zero (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField)
    (hf : f ≠ 0) (h : ∀ P : Points E, pointOrder E P f hf = 0) :
    ∃! c : (AlgebraicClosure K)ˣ,
      f = algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField (c : AlgebraicClosure K) := by
  have ho : ∀ P : Points E, pointOrder E P f hf = pointOrder E P 1 one_ne_zero := by
    intro P
    rw [h P, pointOrder_one]
  simpa only [mul_one] using existsUnique_scalar_of_pointOrder_eq E f 1 hf one_ne_zero ho

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
