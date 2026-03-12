/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CFBRC.Bridge
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-!
# CFBRC Cyclotomic Product (general `d` kickoff)

Phase D (D-GO) の着手として、
- 円分多項式の評価器
- divisors product bridge
を `CFBRC` 側で再利用しやすい形に定義する。
-/

namespace DkMath.CFBRC

open scoped BigOperators
open DkMath.CosmicFormulaBinom

noncomputable section

/-- 円分多項式 `Φ_m` の単変数評価器（係数は `ℤ` から射影）。 -/
@[simp] def cyclotomicEval {R : Type _} [CommRing R]
    (m : ℕ) (X : R) : R :=
  Polynomial.eval₂ (Int.castRingHom R) X (Polynomial.cyclotomic m ℤ)

/--
`∏_{m|d,m>1} Φ_m(X) = ∑_{i=0}^{d-1} X^i`
の評価版。mathlib の `prod_cyclotomic_eq_geom_sum` を `ℤ` で評価して得る。
-/
theorem prod_cyclotomicEval_eq_geomSum {R : Type _} [CommRing R]
    {d : ℕ} (hd : 0 < d) (X : R) :
    (∏ m ∈ d.divisors.erase 1, cyclotomicEval m X) =
      ∑ i ∈ Finset.range d, X ^ i := by
  have hpoly :
      (∏ m ∈ d.divisors.erase 1, Polynomial.cyclotomic m ℤ) =
        ∑ i ∈ Finset.range d, (Polynomial.X : Polynomial ℤ) ^ i :=
    Polynomial.prod_cyclotomic_eq_geom_sum hd ℤ
  have hEval := congrArg (Polynomial.eval₂ (Int.castRingHom R) X) hpoly
  simpa [cyclotomicEval, Polynomial.eval₂_finset_prod, Polynomial.eval₂_finset_sum] using hEval

/--
shifted 版の局所評価器（`u=1` で plain eval に戻る形）。

`m-1-k` での指数は `k ≥ m` で 0 になるため、`range m` 上で定義する。
-/
@[simp] def cyclotomicShiftedEval {R : Type _} [CommRing R]
    (m : ℕ) (x u : R) : R :=
  let pR : Polynomial R := (Polynomial.cyclotomic m ℤ).map (Int.castRingHom R)
  MvPolynomial.eval ![x + u, u] (pR.homogenize (Polynomial.cyclotomic m ℤ).natDegree)

/-- divisors product の shifted 版（Phase D の product bridge 本体）。 -/
@[simp] def cyclotomicDivisorsProductShifted {R : Type _} [CommRing R]
    (d : ℕ) (x u : R) : R :=
  ∏ m ∈ d.divisors.erase 1, cyclotomicShiftedEval m x u

/-- `u = 1` では shifted evaluator は plain evaluator（入力 `x+1`）に一致する。 -/
theorem cyclotomicShiftedEval_one_eq_cyclotomicEval_add_one
    {R : Type _} [Field R] (m : ℕ) (x : R) :
    cyclotomicShiftedEval m x 1 = cyclotomicEval m (x + 1) := by
  have hmain := Polynomial.eval_homogenize
    (p := (Polynomial.cyclotomic m ℤ).map (Int.castRingHom R))
    (n := (Polynomial.cyclotomic m ℤ).natDegree)
    (hn := by
      simpa using
        (Polynomial.natDegree_map_le (p := Polynomial.cyclotomic m ℤ) (f := Int.castRingHom R)))
    (x := ![x + 1, (1 : R)]) (by simp)
  unfold cyclotomicShiftedEval
  simp [cyclotomicEval, Polynomial.eval₂_eq_eval_map] at hmain ⊢
  simpa using hmain

/--
`u=1` の divisors product bridge:
`∏_{m|d,m>1} shiftedEval(m,x,1) = ∑_{i=0}^{d-1}(x+1)^i`。
-/
theorem cyclotomicDivisorsProductShifted_one_eq_geomSum
    {R : Type _} [Field R] {d : ℕ} (hd : 0 < d) (x : R) :
    cyclotomicDivisorsProductShifted d x 1 =
      ∑ i ∈ Finset.range d, (x + 1) ^ i := by
  unfold cyclotomicDivisorsProductShifted
  have hprod :
      (∏ m ∈ d.divisors.erase 1, cyclotomicShiftedEval m x 1) =
        (∏ m ∈ d.divisors.erase 1, cyclotomicEval m (x + 1)) := by
    apply Finset.prod_congr rfl
    intro m hm
    rw [cyclotomicShiftedEval_one_eq_cyclotomicEval_add_one]
  exact hprod.trans (prod_cyclotomicEval_eq_geomSum (R := R) (d := d) hd (x + 1))

/-- `u=1` では CFBRC core は幾何和に一致する。 -/
theorem cyclotomicPrimeCore_one_eq_geomSum
    {R : Type _} [CommSemiring R] (d : ℕ) (x : R) :
    cyclotomicPrimeCore d x 1 = ∑ i ∈ Finset.range d, (x + 1) ^ i := by
  unfold cyclotomicPrimeCore
  simp

/--
`u=1` での general-`d` product bridge（Phase D kickoff の接続点）:
divisors product shifted と CFBRC core の一致。
-/
theorem cyclotomicDivisorsProductShifted_one_eq_cyclotomicPrimeCore
    {R : Type _} [Field R] {d : ℕ} (hd : 0 < d) (x : R) :
    cyclotomicDivisorsProductShifted d x 1 = cyclotomicPrimeCore d x 1 := by
  rw [cyclotomicDivisorsProductShifted_one_eq_geomSum hd]
  rw [cyclotomicPrimeCore_one_eq_geomSum]

end

end DkMath.CFBRC
