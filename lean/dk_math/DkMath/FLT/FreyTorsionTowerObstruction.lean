/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyStableLine
import DkMath.Lib.NumberTheory.EllipticTorsionTowerObstruction

#print "file: DkMath.FLT.FreyTorsionTowerObstruction"

/-!
# Frey の同じ残余直線を底とする捩れ塔の最終矛盾

底の群は新たな形式的群ではなく、`L ⊆ E[p]` を実際の幾何学的点群へ写した
`pointSubgroup S.rationalCurve p L` である。その濃度 `p`、`#E[p]=p²`、
点群の可除性は全て既存の幾何学が供給する。

ここで算術側に残るのは、同じ点群内の上段 `K`、`K[p] ⊆ L`、そして実際の
Galois 元の商上固定性と Frobenius の Cayley–Hamilton 関係である。
本章はそれらの**同時成立が不可能**と証明する。それらを Cofixed 性から
構成する大域理論はまだ別工程であり、一般 hno の完成とは区別する。
-/

namespace DkMath.FLT.Frey.Source

open DkMath.Lib.NumberTheory EllipticTorsionRepresentation

variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic

/-- 同じ Source・同じ直線について、最終捩れ塔の scalar absorption は不可能。
一次元性から底の濃度を内部供給する。 -/
theorem residual_line_tower_scalar_absorption_impossible
    (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (K : AddSubgroup (Points S.rationalCurve)) {N : ℕ} (hN : 0 < N)
    (hdown : ∀ x ∈ K, p • x = 0 → x ∈ pointSubgroup S.rationalCurve p L)
    (habsorb : ∀ y : Points S.rationalCurve, p ^ N • y = 0 → N • y ∈ K) : False :=
  false_of_prime_torsion_tower_scalar_absorbs S.rationalCurve
    (pointSubgroup S.rationalCurve p L) K hN
    (card_pointSubgroup S.rationalCurve p L hline) hdown habsorb

/-- 実際の幾何学的 Galois 作用に対する最終矛盾。
任意の自己準同型による代替作用へ置き換えない。Frobenius 性・慣性の吸収・
塔の構成を仮定の外に供給した段階で、この定理が `False` を返す。 -/
theorem residual_line_tower_frobenius_impossible
    (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (K : AddSubgroup (Points S.rationalCurve)) {N : ℕ} (hN : 0 < N)
    (hdown : ∀ x ∈ K, p • x = 0 → x ∈ pointSubgroup S.rationalCurve p L)
    (σ : Field.absoluteGaloisGroup ℚ) (ell : ℤ)
    (hfixed : ∀ y : Points S.rationalCurve, p ^ N • y = 0 →
      pointAction S.rationalCurve σ y - y ∈ K)
    (hCH : ∀ y : Points S.rationalCurve, p ^ N • y = 0 →
      pointAction S.rationalCurve σ (pointAction S.rationalCurve σ y) + ell • y =
        (ell + 1 - (N : ℤ)) • pointAction S.rationalCurve σ y) : False :=
  false_of_prime_torsion_tower_frobenius S.rationalCurve
    (pointSubgroup S.rationalCurve p L) K hN
    (card_pointSubgroup S.rationalCurve p L hline) hdown
    (pointAction S.rationalCurve σ) ell hfixed hCH

end DkMath.FLT.Frey.Source
