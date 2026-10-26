/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticWeilTransport
import DkMath.Lib.NumberTheory.ValuationDivisor

#print "file: DkMath.Lib.NumberTheory.EllipticWeilDivisor"

/-!
# 既存のWeil関数の位数を、実際の有限支持主因子へまとめる

[DkMath.Lib] [n]の有限ファイバーの点を重み1で足し、TのファイバーとOのファイバーの
差を有限支持因子にする。n≠0とnT=0を保ち、既存の同じWeil関数による全点位数の
実現を供給する。任意の非零関数について支持有限性を仮定する必要はない。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open WeierstrassCurve WeierstrassCurve.Affine WithZero
open scoped BigOperators
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]

/-- [DkMath.Lib] 同じn倍写像の有限ファイバーの、重み1の実際の有限支持因子。 -/
noncomputable def fiberDivisor (n : ℕ) (hn : n ≠ 0) (T : Points E) : Points E →₀ ℤ :=
  ∑ P ∈ (fiber_finite E n hn T).toFinset, Finsupp.single P 1

open Classical in
/-- [DkMath.Lib] ファイバー因子の係数は、同じn倍条件を満たすときだけ1となる。 -/
theorem fiberDivisor_apply (n : ℕ) (hn : n ≠ 0) (T P : Points E) :
    fiberDivisor E n hn T P = if n • P = T then 1 else 0 := by
  simp only [fiberDivisor, Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_ite_eq',
    Set.Finite.mem_toFinset, mem_fiberSet]

/-- [DkMath.Lib] 同じ二つのファイバーの差。定義の段階ではTのtorsion条件を要求しない。 -/
noncomputable def weilDivisor (n : ℕ) (hn : n ≠ 0) (T : Points E) : Points E →₀ ℤ :=
  fiberDivisor E n hn T - fiberDivisor E n hn 0

/-- [DkMath.Lib] nT=0なら、同じ既存のWeil関数がこの有限支持因子を全点で実現する。 -/
theorem weilDivisor_isPrincipal (n : ℕ) (hn : n ≠ 0) (T : Points E) (hT : n • T = 0) :
    ValuationDivisor.IsPrincipal (pointValuation E) (weilDivisor E n hn T) := by
  classical
  refine ⟨weilFunction E n hn T hT, weilFunction_ne_zero E n hn T hT, ?_⟩
  change ∀ P : Points E, weilDivisor E n hn T P = -log (pointValuation E P (weilFunction E n hn T hT))
  intro P
  have hcoef : weilDivisor E n hn T P =
      (if n • P = T then 1 else 0) - (if n • P = 0 then 1 else 0) := by
    change fiberDivisor E n hn T P - fiberDivisor E n hn 0 P = _
    exact congrArg₂ (· - ·) (fiberDivisor_apply E n hn T P) (fiberDivisor_apply E n hn 0 P)
  exact hcoef.trans ((pointOrder_weilFunction E n hn T hT P).symm.trans
    (pointOrder_eq_neg_log E P _ (weilFunction_ne_zero E n hn T hT)))

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
