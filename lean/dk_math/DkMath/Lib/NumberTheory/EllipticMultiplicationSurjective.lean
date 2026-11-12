/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticTorsionRegularFiber

#print "file: DkMath.Lib.NumberTheory.EllipticMultiplicationSurjective"

/-!
# 正の次数の倍写像は代数閉包上で全射

有限座標点Q=(c,y)を任意に固定する。Φₙ−cΨSqₙは次数n²>0なので根を持つ。
その根を実際の点へ持ち上げると、符号を調整して[n]P=Qを得る。
無限遠点は無限遠点自身の像である。良い分離的ファイバーを選ぶ必要はなく、
全ての目標点を扱える。NOTE-016の短縮経路から独立に取り出した無条件の幾何学的定理であり、
Weil対の存在・非退化性の代わりにはならない。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open Polynomial WeierstrassCurve
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]

/-- 標数0の楕円曲線の代数閉包上の点群は、任意の非零自然数で割れる。 -/
theorem multiplication_surjective (n : ℕ) (hn : n ≠ 0) :
    Function.Surjective (nsmulAddMonoidHom n : Points E →+ Points E) := by
  intro Q
  cases Q with
  | zero => exact ⟨0, map_zero _⟩
  | some c y hQ =>
    have hd : 0 < (multiplicationFiberPolynomial E n c).natDegree := by
      rw [multiplication_fiber_natDegree E n hn c]
      exact pow_pos (Nat.pos_of_ne_zero hn) _
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (multiplicationFiberPolynomial E n c)
      (ne_of_gt (natDegree_pos_iff_degree_pos.mp hd))
    obtain ⟨P, hP, _⟩ := exists_aligned_multiplication_preimage E n hQ hx
    exact ⟨P, hP⟩

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
