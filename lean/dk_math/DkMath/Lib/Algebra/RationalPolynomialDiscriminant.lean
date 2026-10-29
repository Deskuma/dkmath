/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import Mathlib.RingTheory.Polynomial.Resultant.Basic
import DkMath.Lib.Algebra.RationalPolynomialFiber

#print "file: DkMath.Lib.Algebra.RationalPolynomialDiscriminant"

/-!
# 判別式の係数写像と有理ファイバー族

このモジュールは楕円曲線を仮定せず、係数環の準同型で多項式を特殊化したときの
判別式の振る舞いを固定する。判別式の定義には多項式の次数が現れるため、単に
係数を写すだけでは不十分である。次数と先頭係数の非零性を明示してから、
resultant の写像公式と `resultant_deriv` を組み合わせるのが安全な経路である。
-/
namespace DkMath.Lib.Algebra.RationalPolynomialDiscriminant

open Polynomial

variable {R S : Type*} [CommRing R] [Field S]

variable {k : Type*} [Field k]

/-- [DkMath.Lib] `F(X) - YG(X)` を係数環 `k[Y]` 上の `X` 多項式として構成する。

外側の多項式変数 `X` と、係数環の変数 `Y` を型で分離する。`F` と `G` の
係数を `Polynomial.C : k →+* k[Y]` で持ち上げ、`Y` による係数環の一次式を
掛けることで、ファイバー多項式を一つの二重多項式へまとめる。
-/
noncomputable def fiberPolynomialFamily (F G : k[X]) : (k[X])[X] :=
  F.map (Polynomial.C : k →+* k[X]) -
    Polynomial.C (Polynomial.X : k[X]) * G.map (Polynomial.C : k →+* k[X])

/-- [DkMath.Lib] `X` 方向の判別式を取り、ファイバー判別式族を得る。

`fiberPolynomialFamily F G` は `k[Y]` を係数環とする `X` の多項式なので、
その `Polynomial.discr` は再び `k[Y]` の多項式になる。評価写像との特殊化は
次数保存を要するため、後続の評価定理では `discr_map_of_natDegree_eq` を使う。
-/
noncomputable def fiberDiscriminantFamily (F G : k[X]) : k[X] :=
  (fiberPolynomialFamily F G).discr

/-- [DkMath.Lib] 次数を保ち先頭係数が消えない係数写像は判別式と可換する。

`Polynomial.discr` は Sylvester 行列のサイズを `natDegree` で決めるため、
係数写像との可換性には次数保存が必要である。証明では `resultant_map_map` を
先に適用し、`resultant_deriv` の両辺を比較して、写像された先頭係数の非零性で
共通因子を消去する。従って評価写像のように単射でない特殊化も、次数条件を
別途供給できればこの API で扱える。
-/
theorem discr_map_of_natDegree_eq
    (φ : R →+* S) {p : R[X]} (hp : 0 < p.degree)
    (hdeg : (p.map φ).natDegree = p.natDegree)
    (hlc : φ p.leadingCoeff ≠ 0) :
    (p.map φ).discr = φ p.discr := by
  have hp_nat : 0 < p.natDegree := (natDegree_pos_iff_degree_pos).mpr hp
  have hmap_degree : 0 < (p.map φ).degree := by
    rw [← natDegree_pos_iff_degree_pos, hdeg]
    exact hp_nat
  have hres := resultant_deriv (R := R) hp
  have hres_map := resultant_deriv (R := S) (f := p.map φ) hmap_degree
  have hmap := resultant_map_map p p.derivative p.natDegree (p.natDegree - 1) φ
  rw [derivative_map, hdeg] at hres_map
  rw [hmap] at hres_map
  have hres_apply := congrArg φ hres
  rw [hres_apply] at hres_map
  simp only [map_mul, map_pow, map_neg, map_one, leadingCoeff, coeff_map, hdeg] at hres_map
  have hscalar : φ ((-1 : R) ^ (p.natDegree * (p.natDegree - 1) / 2) *
      p.leadingCoeff) ≠ 0 := by
    simpa only [map_mul, map_pow, map_neg, map_one] using
      mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hlc
  apply (mul_left_cancel₀ hscalar)
  simpa [mul_assoc, mul_left_comm, mul_comm] using hres_map.symm

/-- [DkMath.Lib] 判別式族の係数特殊化は、通常のファイバー多項式を与える。

`evalRingHom c` は係数環の変数 `Y` を `c` に送る。`map_map` と評価写像の
基本則だけで、二重多項式の特殊化が `fiberPolynomial F G c` と一致することを
固定する。この補題は判別式そのものの次数条件とは独立した、係数レベルの橋である。
-/
theorem fiberPolynomialFamily_map_evalRingHom (F G : k[X]) (c : k) :
    (fiberPolynomialFamily F G).map (Polynomial.evalRingHom c) =
      DkMath.Lib.Algebra.RationalPolynomialFiber.fiberPolynomial F G c := by
  have hcomp : (Polynomial.evalRingHom c).comp (Polynomial.C : k →+* k[X]) =
      RingHom.id k := by
    ext x
    simp
  simp only [fiberPolynomialFamily]
  rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_map, Polynomial.map_map,
    hcomp, Polynomial.map_id]
  simp [DkMath.Lib.Algebra.RationalPolynomialFiber.fiberPolynomial]

/-- [DkMath.Lib] 判別式族の評価を、次数保存のもとで通常のファイバー判別式へ戻す。

判別式の `natDegree` 依存性を隠さないため、`X` 方向の正次数、特殊化後の次数保存、
および写像された先頭係数の非零性を仮定する。固定係数対では、これらの条件を
`deg G < deg F` と先頭係数不変性から供給する。
-/
theorem fiberDiscriminantFamily_eval_of_natDegree_eq
    (F G : k[X]) (c : k)
    (hp : 0 < (fiberPolynomialFamily F G).degree)
    (hdeg : ((fiberPolynomialFamily F G).map (Polynomial.evalRingHom c)).natDegree =
      (fiberPolynomialFamily F G).natDegree)
    (hlc : Polynomial.evalRingHom c (fiberPolynomialFamily F G).leadingCoeff ≠ 0) :
    (fiberDiscriminantFamily F G).eval c =
      (DkMath.Lib.Algebra.RationalPolynomialFiber.fiberPolynomial F G c).discr := by
  have hmap := discr_map_of_natDegree_eq (Polynomial.evalRingHom c) hp hdeg hlc
  rw [fiberPolynomialFamily_map_evalRingHom] at hmap
  exact hmap.symm

end DkMath.Lib.Algebra.RationalPolynomialDiscriminant
