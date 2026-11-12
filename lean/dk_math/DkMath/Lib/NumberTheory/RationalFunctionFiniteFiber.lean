/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

#print "file: DkMath.Lib.NumberTheory.RationalFunctionFiniteFiber"

/-!
# 無限遠に極を持つ既約有理関数の、全ての有限値への到達

[DkMath.Lib] 分子の次数が分母より大きいなら、num−c denは正次数である。
代数閉性で根を取り、分子分母の互いに素性で分母の零を排除する。
「非零多項式の根への包含」から「任意の有限値への到達」へ進むための補題。
-/
namespace DkMath.Lib.NumberTheory.RationalFunctionFiniteFiber
open Polynomial
variable {k : Type*} [Field k] [IsAlgClosed k]

/-- [DkMath.Lib] 無限遠に極を持つ既約有理関数は、各有限値cを分母非零の点で取る。 -/
theorem exists_finite_fiber (r : RatFunc k) (hdeg : r.denom.natDegree < r.num.natDegree) (c : k) :
    ∃ a : k, r.num.eval a = c * r.denom.eval a ∧ r.denom.eval a ≠ 0 := by
  let p := r.num - C c * r.denom
  have hp : p.natDegree = r.num.natDegree := natDegree_sub_eq_left_of_natDegree_lt
    ((natDegree_C_mul_le c r.denom).trans_lt hdeg)
  have hpos : 0 < p.natDegree := by rw [hp]; omega
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p (fun hd =>
    (Nat.ne_of_gt hpos) (natDegree_eq_of_degree_eq_some hd))
  have he : r.num.eval a = c * r.denom.eval a := by
    have h : p.eval a = 0 := ha
    simpa only [p, eval_sub, eval_mul, eval_C, sub_eq_zero] using h
  refine ⟨a, he, ?_⟩
  intro hd
  have hn : r.num.eval a = 0 := by rw [he, hd, mul_zero]
  obtain ⟨u, v, huv⟩ := r.isCoprime_num_denom
  have hh := congrArg (Polynomial.eval a) huv
  simp only [eval_add, eval_mul, hn, hd, mul_zero, zero_add, eval_one] at hh
  exact zero_ne_one hh

end DkMath.Lib.NumberTheory.RationalFunctionFiniteFiber
