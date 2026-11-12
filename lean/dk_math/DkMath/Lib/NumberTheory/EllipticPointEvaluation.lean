/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticPoleDegree
import DkMath.Lib.NumberTheory.EllipticFiniteKernelDegree

#print "file: DkMath.Lib.NumberTheory.EllipticPointEvaluation"

/-!
# 点で正則な有理関数を、係数体の値へ特殊化する

[DkMath.Lib] 点Pの付値環内の元fに対して、v_P(f−c)<1となるcを一意に構成する。
剰余体を係数体と同一視する未証明の仮定は置かない。
既存の最高項相殺定理を、Pへ移した一般x座標の極に適用する。
この評価は正則な関数だけを扱い、極に便宜的な有限値を割り当てない。
-/
namespace DkMath.Lib.NumberTheory.EllipticPointEvaluation
open WeierstrassCurve WeierstrassCurve.Affine WithZero
open EllipticFunctionField EllipticTorsionRepresentation
open DkMath.Lib.Algebra
attribute [local instance] geometricCoordinateRing_isDedekindDomain
variable {K : Type*} [Field K] (E : WeierstrassCurve K) [E.IsElliptic]
noncomputable local instance : DecidableEq (AlgebraicClosure K) := Classical.decEq _

/-- [DkMath.Lib] 任意の点Pで極を持つ関数を、平行移動した一般x座標から構成する。 -/
theorem exists_pole (P : Points E) :
    ∃ x : (E.toAffine⁄(AlgebraicClosure K)).FunctionField,
      Transcendental (AlgebraicClosure K) x ∧ 1 < pointValuation E P x := by
  let x := transEquiv E (AlgebraicClosure K) (-P) (genericX E (AlgebraicClosure K))
  have hx : pointValuation E P x = exp (2 : ℤ) := by
    dsimp only [x]
    have ht : pointValuation E P (transEquiv E (AlgebraicClosure K) (-P)
        (genericX E (AlgebraicClosure K))) = pointValuation E (P + -P)
          (genericX E (AlgebraicClosure K)) := pointValuation_transEquiv E P (-P) _
    rw [ht, add_neg_cancel]
    exact pointValuation_zero_genericX E
  have hp : 1 < pointValuation E P x := by rw [hx, ← exp_zero, exp_lt_exp]; decide
  exact ⟨x, transcendental_of_point_pole E P x hp, hp⟩

/-- [DkMath.Lib] Pで正則な関数は、同じ係数体に剰余値を持つ。 -/
theorem exists_value (P : Points E)
    (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) (hf : pointValuation E P f ≤ 1) :
    ∃ c : AlgebraicClosure K, (pointValuation E P).Cong f (algebraMap _ _ c) := by
  rcases lt_or_eq_of_le hf with hlt | heq
  · exact ⟨0, by simpa only [Valuation.Cong, map_zero, sub_zero] using hlt⟩
  · obtain ⟨x, hx, hp⟩ := exists_pole E P
    let := EllipticFiniteKernel.finiteDimensional_over_transcendental E x hx
    exact ValuationPoleSpace.exists_const_sub_lt (pointValuation E P)
      (fun c hc => pointValuation_const_eq_one E P hc) x hx hp f heq

/-- [DkMath.Lib] 係数体の異なる二定数は、同じ点で合同にならない。 -/
theorem constants_eq (P : Points E) {a b : AlgebraicClosure K}
    (h : (pointValuation E P).Cong (algebraMap _ _ a) (algebraMap _ _ b)) : a = b := by
  by_contra hn
  have he := pointValuation_const_eq_one E P (sub_ne_zero.mpr hn)
  rw [map_sub] at he
  exact (ne_of_lt h) he

/-- [DkMath.Lib] 関数の有限値は一意。値を選ぶ際の証明や表示に依存しない。 -/
theorem value_unique (P : Points E)
    {f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField} {a b : AlgebraicClosure K}
    (ha : (pointValuation E P).Cong f (algebraMap _ _ a))
    (hb : (pointValuation E P).Cong f (algebraMap _ _ b)) : a = b :=
  constants_eq E P (ha.symm.trans hb)

/-- [DkMath.Lib] 正則関数の実際の係数体値。正則性の証明を必須入力とする。 -/
noncomputable def value (P : Points E)
    (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) (hf : pointValuation E P f ≤ 1) :
    AlgebraicClosure K := Classical.choose (exists_value E P f hf)

/-- [DkMath.Lib] 選んだ有限値は、元の関数と同じ点で合同である。 -/
theorem value_spec (P : Points E)
    (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) (hf : pointValuation E P f ≤ 1) :
    (pointValuation E P).Cong f (algebraMap _ _ (value E P f hf)) :=
  Classical.choose_spec (exists_value E P f hf)

/-- [DkMath.Lib] 合同を証明すれば、選ばれた有限値を具体定数に同定できる。 -/
theorem value_eq (P : Points E)
    (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) (hf : pointValuation E P f ≤ 1)
    (c : AlgebraicClosure K) (hc : (pointValuation E P).Cong f (algebraMap _ _ c)) :
    value E P f hf = c := value_unique E P (value_spec E P f hf) hc

/-- [DkMath.Lib] 正則性の証明を変更しても同じ値となる。 -/
theorem value_proof_irrel (P : Points E)
    (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField)
    (hf hg : pointValuation E P f ≤ 1) : value E P f hf = value E P f hg := rfl

/-- [DkMath.Lib] 定数関数の有限値は元の定数である。 -/
theorem value_const (P : Points E) (c : AlgebraicClosure K) :
    value E P (algebraMap _ _ c) (pointValuation_const_le_one E P c) = c :=
  value_eq E P _ _ c Valuation.Cong.rfl

/-- [DkMath.Lib] 正則関数の有限値が零であることは、その点に零点を持つことと同値。 -/
theorem value_eq_zero_iff (P : Points E)
    (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) (hf : pointValuation E P f ≤ 1) :
    value E P f hf = 0 ↔ pointValuation E P f < 1 := by
  constructor
  · intro he
    have h := value_spec E P f hf
    simpa only [he, map_zero, Valuation.Cong, sub_zero] using h
  · intro he
    apply value_eq
    simpa only [map_zero, Valuation.Cong, sub_zero] using he


/-- [DkMath.Lib] 同じ点で正則な関数全体は、係数体上の部分代数である。 -/
noncomputable def regularAlgebra (P : Points E) :
    Subalgebra (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField where
  carrier := {f | pointValuation E P f ≤ 1}
  algebraMap_mem' := pointValuation_const_le_one E P
  zero_mem' := by simp
  add_mem' := fun hf hg => ((pointValuation E P).map_add _ _).trans (max_le hf hg)
  mul_mem' := by
    intro a b hf hg
    change pointValuation E P (a * b) ≤ 1
    rw [map_mul]
    exact (mul_le_mul' hf hg).trans_eq (one_mul 1)

/-- [DkMath.Lib] 正則な和の値は、二つの値の和である。 -/
theorem value_add (P : Points E)
    (f g : (E.toAffine⁄(AlgebraicClosure K)).FunctionField)
    (hf : pointValuation E P f ≤ 1) (hg : pointValuation E P g ≤ 1) :
    value E P (f + g) (((pointValuation E P).map_add _ _).trans (max_le hf hg)) =
      value E P f hf + value E P g hg := by
  apply value_eq
  simpa only [map_add] using (value_spec E P f hf).add (value_spec E P g hg)

/-- [DkMath.Lib] 正則な積の値は値の積。正則性を失う極の相殺とは区別する。 -/
theorem value_mul (P : Points E)
    (f g : (E.toAffine⁄(AlgebraicClosure K)).FunctionField)
    (hf : pointValuation E P f ≤ 1) (hg : pointValuation E P g ≤ 1) :
    value E P (f * g) (by rw [map_mul]; exact (mul_le_mul' hf hg).trans_eq (one_mul 1)) =
      value E P f hf * value E P g hg := by
  apply value_eq
  simpa only [map_mul] using (value_spec E P f hf).mul (value_spec E P g hg)
    (pointValuation_const_le_one E P _) (pointValuation_const_le_one E P _)

/-- [DkMath.Lib] Pで正則な部分代数から係数体への実際の評価準同型。 -/
noncomputable def evalHom (P : Points E) : regularAlgebra E P →ₐ[AlgebraicClosure K] AlgebraicClosure K where
  toFun f := value E P f.val f.property
  map_zero' := by
    apply value_eq
    simpa only [Subalgebra.coe_zero, map_zero] using (Valuation.Cong.rfl (v := pointValuation E P) (a := 0))
  map_one' := by
    apply value_eq
    simpa only [Subalgebra.coe_one, map_one] using (Valuation.Cong.rfl (v := pointValuation E P) (a := 1))
  map_add' f g := value_add E P f.val g.val f.property g.property
  map_mul' f g := value_mul E P f.val g.val f.property g.property
  commutes' c := value_const E P c

/-- [DkMath.Lib] 評価準同型を、元の正則関数の有限値として読む。 -/
theorem evalHom_apply (P : Points E) (f : regularAlgebra E P) :
    evalHom E P f = value E P f.val f.property := rfl

/-- [DkMath.Lib] 評価準同型は全射。各係数体元は同じ定数関数の評価として得られる。 -/
theorem evalHom_surjective (P : Points E) : Function.Surjective (evalHom E P) :=
  fun c => ⟨algebraMap (AlgebraicClosure K) (regularAlgebra E P) c, (evalHom E P).commutes c⟩


/-- [DkMath.Lib] 有限点で一般x座標を評価すると、その実点のx座標へ戻る。 -/
theorem value_genericX (P : Points E) (hP : P ≠ 0) :
    value E P (genericX E (AlgebraicClosure K)) (pointValuation_genericX_le_one E P hP) = P.xc := by
  apply value_eq
  unfold pointValuation
  split_ifs with hz
  · exact (hP hz).elim
  · exact cong_genericX E _ P hP

/-- [DkMath.Lib] 有限点で一般y座標を評価すると、同じ実点のy座標へ戻る。 -/
theorem value_genericY (P : Points E) (hP : P ≠ 0) :
    value E P (genericY E (AlgebraicClosure K)) (pointValuation_genericY_le_one E P hP) = P.yc := by
  apply value_eq
  unfold pointValuation
  split_ifs with hz
  · exact (hP hz).elim
  · exact cong_genericY E _ P hP

/-- [DkMath.Lib] 平行移動引き戻しの有限値は、移動先での元の有限値である。 -/
theorem value_translation (P Q : Points E)
    (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField)
    (hf : pointValuation E (P + Q) f ≤ 1) :
    value E P (transEquiv E (AlgebraicClosure K) Q f)
      (by exact (pointValuation_transEquiv E P Q f).trans_le hf) = value E (P + Q) f hf := by
  apply value_eq
  have h := value_spec E (P + Q) f hf
  change pointValuation E (P + Q) (f - algebraMap _ _ (value E (P + Q) f hf)) < 1 at h
  have ht := pointValuation_transEquiv E P Q (f - algebraMap _ _ (value E (P + Q) f hf))
  rw [map_sub, AlgEquiv.commutes] at ht
  exact ht.trans_lt h

/-- [DkMath.Lib] 正則な二関数のWeierstrass方程式は、同じ点の有限値へ特殊化できる。
結論はEquationであり、Nonsingularを無条件には含めない。 -/
theorem equation_value (P : Points E) (W : WeierstrassCurve (AlgebraicClosure K))
    (f g : (E.toAffine⁄(AlgebraicClosure K)).FunctionField)
    (hf : pointValuation E P f ≤ 1) (hg : pointValuation E P g ≤ 1)
    (he : (W.toAffine⁄(E.toAffine⁄(AlgebraicClosure K)).FunctionField).Equation f g) :
    W.toAffine.Equation (value E P f hf) (value E P g hg) := by
  let x : regularAlgebra E P := ⟨f, hf⟩
  let y : regularAlgebra E P := ⟨g, hg⟩
  have hs : y ^ 2 + algebraMap (AlgebraicClosure K) (regularAlgebra E P) W.a₁ * x * y +
      algebraMap (AlgebraicClosure K) (regularAlgebra E P) W.a₃ * y =
      x ^ 3 + algebraMap (AlgebraicClosure K) (regularAlgebra E P) W.a₂ * x ^ 2 +
      algebraMap (AlgebraicClosure K) (regularAlgebra E P) W.a₄ * x +
      algebraMap (AlgebraicClosure K) (regularAlgebra E P) W.a₆ := by
    apply Subtype.ext
    exact (equation_iff _ _).mp he
  have ht := congrArg (evalHom E P) hs
  rw [equation_iff]
  simpa only [map_add, map_mul, map_pow, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
    evalHom_apply, x, y] using ht

end DkMath.Lib.NumberTheory.EllipticPointEvaluation
