/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GTailCyclotomic
import Mathlib.RingTheory.Coprime.Basic

#print "file: DkMath.Lib.Cosmic.GNSuccessor"

/-!
# Successor identities for the existing gap-normalized kernel

Both recurrence identities hold in every commutative semiring, including
zero gaps, zero divisors, and degree zero. The unit-anchor identity is a
Bézout witness in every commutative ring; no division by the gap is used.

## 教科書としての読み方

[DkMath.Lib] GN-LIB-001として既存の一般核を移管した。
namespaceは `DkMath.NumberTheory.GapFocusing` を維持するが、証明の所有者は
このLibモジュールである。旧importからも同じ定理へ到達できる。

`G_d = GTail d 1 x u`、`v = x + u` と書くと、
`G_(d+1) = u G_d + v^d = v G_d + u^d` が二つの再帰である。
有限和の恒等式なので、gapの約分・正性・整域性を仮定しない。
anchorが1なら剰余が1となり、可換環ではそのままBézoutの証人になる。
`G_0 = 0`、`G_1 = 1` もこの再帰に含まれる。

-/

namespace DkMath.NumberTheory.GapFocusing

open DkMath.CosmicFormula

/--
[DkMath.Lib] 昇格元: `DkMath.NumberTheory.GapFocusing.GN_succ_right`
（`DkMath.NumberTheory.GapFocusing.Successor`）。全修飾名・型・証明を維持してLib所有へ移管。
旧モジュールは本モジュールをimportする互換入口である。

係数型は任意の可換半環、次数は0を含む。有限和の末尾を取り出すため、gapの非零性や約分を必要としない。

Successor recurrence retaining the power of the sum coordinate.
-/
theorem GN_succ_right {R : Type*} [CommSemiring R] (d : ℕ) (x u : R) :
    GTail (d + 1) 1 x u = u * GTail d 1 x u + (x + u) ^ d := by
  rw [GTail_one_eq_GTailCyclotomicShell,
    GTailCyclotomicShell_succ, GTail_one_eq_GTailCyclotomicShell]

/--
[DkMath.Lib] 昇格元: `DkMath.NumberTheory.GapFocusing.GN_succ_left`
（`DkMath.NumberTheory.GapFocusing.Successor`）。全修飾名・型・証明を維持してLib所有へ移管。
旧モジュールは本モジュールをimportする互換入口である。

右側再帰へ完成等式を代入し、同じ有限和をsum座標側から組み直す。零因子のある可換半環でも成立する。

Successor recurrence retaining the anchor power.
-/
theorem GN_succ_left {R : Type*} [CommSemiring R] (d : ℕ) (x u : R) :
    GTail (d + 1) 1 x u = (x + u) * GTail d 1 x u + u ^ d := by
  rw [GN_succ_right, add_pow_eq_mul_GTail_one_add_gap]
  ring

/--
[DkMath.Lib] 昇格元: `DkMath.NumberTheory.GapFocusing.GN_succ_unit_anchor`
（`DkMath.NumberTheory.GapFocusing.Successor`）。全修飾名・型・証明を維持してLib所有へ移管。
旧モジュールは本モジュールをimportする互換入口である。

anchorを1に固定すると剰余が1になる。次数0も含み、次のBézout関係の算術入力となる。

At a unit anchor, the recurrence has a constant one remainder.
-/
theorem GN_succ_unit_anchor {R : Type*} [CommSemiring R] (d : ℕ) (x : R) :
    GTail (d + 1) 1 x 1 = (x + 1) * GTail d 1 x 1 + 1 := by
  simpa only [one_pow] using GN_succ_left d x (1 : R)

/--
[DkMath.Lib] 昇格元: `DkMath.NumberTheory.GapFocusing.GN_succ_bezout`
（`DkMath.NumberTheory.GapFocusing.Successor`）。全修飾名・型・証明を維持してLib所有へ移管。
旧モジュールは本モジュールをimportする互換入口である。

単位anchorの再帰を環の減算で書き直す。整域・体・gapの非零性は仮定せず、隣接二項から1を作る。

The unit-anchor recurrence is an explicit Bézout identity in any ring.
-/
theorem GN_succ_bezout {R : Type*} [CommRing R] (d : ℕ) (x : R) :
    GTail (d + 1) 1 x 1 - (x + 1) * GTail d 1 x 1 = 1 := by
  rw [GN_succ_unit_anchor]
  exact add_sub_cancel_left _ _

/--
[DkMath.Lib] 昇格元: `DkMath.NumberTheory.GapFocusing.GN_succ_isCoprime_unit_anchor`
（`DkMath.NumberTheory.GapFocusing.Successor`）。全修飾名・型・証明を維持してLib所有へ移管。
旧モジュールは本モジュールをimportする互換入口である。

係数−(x+1)と1をBézoutの証人にする。共通素因数がないという数値的主張より一般に、任意の可換環で単位イデアルを生成する。

Universal unit-anchor coprimality, as a Bézout relation.
-/
theorem GN_succ_isCoprime_unit_anchor {R : Type*} [CommRing R] (d : ℕ) (x : R) :
    IsCoprime (GTail d 1 x 1) (GTail (d + 1) 1 x 1) := by
  refine ⟨-(x + 1), 1, ?_⟩
  rw [GN_succ_unit_anchor]
  ring

end DkMath.NumberTheory.GapFocusing
