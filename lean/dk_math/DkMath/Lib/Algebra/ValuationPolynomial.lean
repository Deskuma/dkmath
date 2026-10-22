/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: ../NumberTheory/RegularKummer/LICENSE
Upstream notices: ../NumberTheory/RegularKummer/ANTHROPIC-NOTICE
Leading-term argument adapted from S_WeierstrassCurve_eq_zero_of_smul_eq_zero_of_reducePoint_eq_zero.lean,
blob 6d9088ee96d5303a6b9112c87260486777330a27.
Modified: arbitrary ordered valuation, no DVR or elliptic-curve hypotheses.
-/

import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Polynomial.Eval.Degree

#print "file: DkMath.Lib.Algebra.ValuationPolynomial"

/-!
# NOTE-031-002A: 単元最高係数を持つ整な多項式の根に極はない

係数の乗法的付値が全て1以下、最高係数の付値が1なら、
v(x)>1において最高次項だけが他の全項より大きい付値を持つ。
非Archimedes的な和の公式からv(f(x))=v(x)^degree(f)となり、f(x)=0は不可能である。
離散性・完備性・数体・楕円曲線をこの核の仮定に置かない。
-/
namespace DkMath.Lib.Algebra.ValuationPolynomial
open Polynomial
variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]

/-- v(x)>1では単元最高係数の項が支配する。低次項の和を厳密に小さく評価する。 -/
theorem valuation_eval_of_pole (v : Valuation K Γ₀) {f : K[X]} {x : K}
    (hc : ∀ i, v (f.coeff i) ≤ 1) (hl : v f.leadingCoeff = 1) (hx : 1 < v x) :
    v (f.eval x) = v x ^ f.natDegree := by
  classical
  have hx0 : v x ≠ 0 := (zero_lt_one.trans hx).ne'
  have htop : v (f.coeff f.natDegree * x ^ f.natDegree) = v x ^ f.natDegree := by
    rw [map_mul, map_pow, show v (f.coeff f.natDegree) = 1 from hl, one_mul]
  have hlower : v (∑ i ∈ Finset.range f.natDegree, f.coeff i * x ^ i) < v x ^ f.natDegree := by
    refine v.map_sum_lt (pow_ne_zero _ hx0) ?_
    intro i hi
    rw [Finset.mem_range] at hi
    rw [map_mul, map_pow]
    calc v (f.coeff i) * v x ^ i ≤ 1 * v x ^ i := mul_le_mul' (hc i) le_rfl
      _ = v x ^ i := one_mul _
      _ < v x ^ f.natDegree := pow_lt_pow_right₀ hx hi
  rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ,
    Valuation.map_add_eq_of_lt_right _ (htop ▸ hlower), htop]

/-- 整な係数と単元最高係数を持つ多項式の根の乗法的付値は1以下である。 -/
theorem valuation_root_le_one (v : Valuation K Γ₀) {f : K[X]} {x : K}
    (hc : ∀ i, v (f.coeff i) ≤ 1) (hl : v f.leadingCoeff = 1) (hroot : f.eval x = 0) :
    v x ≤ 1 := by
  by_contra h
  have hx : 1 < v x := lt_of_not_ge h
  have hv := valuation_eval_of_pole v hc hl hx
  rw [hroot, map_zero] at hv
  exact pow_ne_zero _ ((zero_lt_one.trans hx).ne') hv.symm

end DkMath.Lib.Algebra.ValuationPolynomial
