/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.FiniteAdditiveTorsionCard
import Lean.Util.CollectAxioms

#print "file: DkMathTest.Lib.Algebra.FiniteAdditiveTorsionCard"

/-!
# 有限加法群の素数捩れ補題の回帰入口

このテストは、成分群を構成せずに、後段の局所幾何学が供給する
「非零な `q`-捩れ像」から群の位数の可除性へ進める最小橋を確認する。
有限群 `G` の具体例には `ZMod 3` を使い、`q • Q = 0` と `Q ≠ 0` から
`3 ∣ Nat.card (ZMod 3)` を得る。
-/

namespace DkMathTest.Lib.Algebra.FiniteAdditiveTorsionCard

open DkMath.Lib.Algebra

example : 3 ∣ Nat.card (ZMod 3) := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  apply prime_dvd_natCard_of_nsmul_eq_zero_of_ne_zero (G := ZMod 3) (q := 3) 1
  · change (3 : ZMod 3) = 0
    decide
  · decide

example : 3 ∣ Nat.card (ZMod 3) := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  let φ : ZMod 3 →+ ZMod 3 := AddMonoidHom.id (ZMod 3)
  apply prime_dvd_natCard_of_addMonoidHom_map_nsmul_eq_zero_of_map_ne_zero φ 1
  · change (3 : ZMod 3) = 0
    decide
  · decide

/-- The identity map has trivial `3`-torsion kernel, so the kernel criterion
turns the same nonzero torsion point into the cardinality divisibility. -/
example : 3 ∣ Nat.card (ZMod 3) := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  let φ : ZMod 3 →+ ZMod 3 := AddMonoidHom.id (ZMod 3)
  refine prime_dvd_natCard_of_torsion_kernel_trivial (φ := φ) (R := 1) ?_ ?_ ?_
  · intro x _ hx
    simpa [φ] using hx
  · change (3 : ZMod 3) = 0
    decide
  · decide

#print axioms prime_dvd_natCard_of_nsmul_eq_zero_of_ne_zero
#print axioms prime_dvd_natCard_of_addMonoidHom_map_nsmul_eq_zero_of_map_ne_zero
#print axioms prime_dvd_natCard_of_torsion_kernel_trivial

end DkMathTest.Lib.Algebra.FiniteAdditiveTorsionCard
