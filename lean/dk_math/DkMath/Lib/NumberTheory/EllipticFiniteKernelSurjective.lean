/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelFibers
import DkMath.Lib.NumberTheory.RationalFunctionFiniteFiber
import DkMath.Lib.NumberTheory.EllipticFiniteKernelPointDescent
import DkMath.Lib.Algebra.RationalPolynomialFiber

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelSurjective"

/-!
# 同じ全点関数は同じ標的の全点へ到達する

[DkMath.Lib] X_Hの既約有理式を元のxに戻し、Oでの極位数2から分子次数が分母より
ちょうど1大きいことを証明する。num−c denの根は分母非零なので源の有限点を選べる。
標的の二つのy値は反転で交換され、既存の反転公式で望む方の点へ到達する。
全射性の証明に点群写像の加法性は使用しない。
-/
namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open Polynomial WeierstrassCurve WeierstrassCurve.Affine WithZero
open EllipticFunctionField EllipticTorsionRepresentation EllipticPointEvaluation
open DkMath.Lib.Algebra.RationalPolynomialFiber
open scoped Polynomial.Bivariate
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
noncomputable local instance instDecidableEqEllipticFiniteKernelSurjective :
    DecidableEq (AlgebraicClosure K) := Classical.decEq _

omit [CharZero K] in
/-- [DkMath.Lib] 同じ幾何学的楕円曲線の任意の有限x値には実際の非零点が存在する。 -/
theorem exists_finite_point_with_x (a : AlgebraicClosure K) :
    ∃ P : Points E, P ≠ 0 ∧ P.xc = a := by
  let k := AlgebraicClosure K
  let W := E.toAffine⁄k
  let : W.IsElliptic := by
    change (E.map (algebraMap K k)).IsElliptic
    infer_instance
  let q : k[X] := C 1 * X ^ 2 + C (W.a₁ * a + W.a₃) * X +
    C (-(a ^ 3 + W.a₂ * a ^ 2 + W.a₄ * a + W.a₆))
  have hd : q.natDegree = 2 := natDegree_quadratic one_ne_zero
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root q (degree_ne_of_natDegree_ne (by omega : q.natDegree ≠ 0))
  have he : W.Equation a y := by
    rw [equation_iff]
    have h : q.eval y = 0 := hy
    simp only [q, eval_add, eval_mul, eval_pow, eval_C, eval_X, one_mul] at h
    linear_combination h
  exact ⟨.some a y (equation_iff_nonsingular.mp he), Point.some_ne_zero _, rfl⟩

/-- [DkMath.Lib] 同じX_Hの既約有理式は、分子次数=分母次数+1で分子次数=|H|。
元のxとX_HがともにOで極位数2であることを使い、有限値での次数落ちを排除する。 -/
theorem exists_veluX_rational_at_infinity (H : AddSubgroup (Points E)) [Fintype H] :
    ∃ r : RatFunc (AlgebraicClosure K), r.num.natDegree = r.denom.natDegree + 1 ∧
      r.num.natDegree = Nat.card H ∧
      veluX E H = aeval (genericX E (AlgebraicClosure K)) r.num /
        aeval (genericX E (AlgebraicClosure K)) r.denom := by
  obtain ⟨r, hmax, hr⟩ := exists_veluX_rational E H
  have hn : r.num ≠ 0 := by
    intro h
    have hz := hr
    rw [h, map_zero, zero_div] at hz
    exact veluX_ne_zero E H hz
  let v := pointValuation E (0 : Points E)
  have hx : v (genericX E (AlgebraicClosure K)) = exp (2 : ℤ) := pointValuation_zero_genericX E
  have hpoly (p : (AlgebraicClosure K)[X]) (hp : p ≠ 0) :
      v (aeval (genericX E (AlgebraicClosure K)) p) = exp (2 * (p.natDegree : ℤ)) := by
    rw [v.map_aeval_eq_pow_of_one_lt (fun _ hc => pointValuation_const_eq_one E 0 hc)
      (by rw [hx, ← exp_zero, exp_lt_exp]; decide) hp, hx, ← exp_nsmul]
    congr 1
    simp [mul_comm]
  have he : v (veluX E H) = exp (2 : ℤ) := veluX_valuation_zero E H
  rw [hr, map_div₀, hpoly _ hn, hpoly _ r.denom_ne_zero, ← exp_sub, exp_inj] at he
  have hd : r.num.natDegree = r.denom.natDegree + 1 := by omega
  refine ⟨r, hd, ?_, hr⟩
  rw [max_eq_left (by omega)] at hmax
  exact hmax

set_option linter.unusedFintypeInType false in
/-- [DkMath.Lib] Vélu 有理式の有限ファイバー分子は、核位数を正確な次数に持つ。

`exists_veluX_rational_at_infinity` は分子次数が分母次数より1大きく、かつ
分子次数が `|H|` であることを供給する。一般補題
`fiberPolynomial_natDegree_eq_of_natDegree_lt` を適用すると、任意の有限値 `c`
に対する `F-cG` の次数落ちがないことが分かる。ここでは次段の根多重度証明へ
渡すため、ファイバー多項式の非零性も同時に記録する。 -/
theorem exists_veluX_fiber_polynomial_exact_degree
    (H : AddSubgroup (Points E)) [Fintype H] (c : AlgebraicClosure K) :
    ∃ r : RatFunc (AlgebraicClosure K),
      r.num.natDegree = Nat.card H ∧
        (fiberPolynomial r.num r.denom c).natDegree = Nat.card H ∧
          fiberPolynomial r.num r.denom c ≠ 0 := by
  obtain ⟨r, hgap, hnum, _⟩ := exists_veluX_rational_at_infinity E H
  have hdeg : (fiberPolynomial r.num r.denom c).natDegree = r.num.natDegree :=
    fiberPolynomial_natDegree_eq_of_natDegree_lt (c := c) (by omega)
  have hcard : 0 < Nat.card H := by omega
  refine ⟨r, hnum, hdeg.trans hnum, ?_⟩
  intro hz
  have hzdeg : (fiberPolynomial r.num r.denom c).natDegree = 0 := by simp [hz]
  exact (Nat.ne_of_gt hcard) (by rw [hdeg, hnum] at hzdeg; exact hzdeg)

/-- [DkMath.Lib] Vélu 分子・分母を保った有限ファイバーの exact degree 形。

`exists_veluX_coprime_rational` は、標準 RatFunc 表示から互いに素な
`F,G` と `X_H = F/G` を供給する。一方、無限遠点での極位数2の比較は
`deg G < deg F = |H|` を与えるので、一般補題
`fiberPolynomial_natDegree_eq_of_natDegree_lt` により、有限値 `c` に対する
`F-cG` の次数は常に `|H|` である。ここで非零性も同時に記録することで、
後段の Wronskian と根多重度の議論が、同じ係数対 `F,G` をそのまま再利用できる。
-/
theorem exists_veluX_coprime_fiber_polynomial_exact_degree
    (H : AddSubgroup (Points E)) [Fintype H] (c : AlgebraicClosure K) :
    ∃ F G : (AlgebraicClosure K)[X],
      IsCoprime F G ∧ F.natDegree = Nat.card H ∧ G.natDegree < F.natDegree ∧
        veluX E H = aeval (genericX E (AlgebraicClosure K)) F /
          aeval (genericX E (AlgebraicClosure K)) G ∧
        fiberPolynomial F G c ≠ 0 ∧
          (fiberPolynomial F G c).natDegree = Nat.card H := by
  obtain ⟨r, hgap, hnum, hr⟩ := exists_veluX_rational_at_infinity E H
  have hdeg : (fiberPolynomial r.num r.denom c).natDegree = r.num.natDegree :=
    fiberPolynomial_natDegree_eq_of_natDegree_lt (c := c) (by omega)
  have hcard : 0 < Nat.card H := by omega
  have hpoly : fiberPolynomial r.num r.denom c ≠ 0 := by
    intro hz
    have hzdeg : (fiberPolynomial r.num r.denom c).natDegree = 0 := by simp [hz]
    exact (Nat.ne_of_gt hcard) (by rw [hdeg, hnum] at hzdeg; exact hzdeg)
  refine ⟨r.num, r.denom, r.isCoprime_num_denom, hnum, ?_, hr, hpoly, ?_⟩
  · omega
  · exact hdeg.trans hnum

/-- [DkMath.Lib] Vélu 有理式には、任意の有限例外集合を避ける分離ファイバーがある。

分子・分母の互いに素性と `deg G < deg F` から Wronskian の非零性を得て、
一般補題 `exists_separable_fiber_avoiding` を適用する。従って、重根を持つ
有限値は有限集合に閉じ込められ、例外を避けた値では `F-cG` は分離的である。
同時に無限遠点次数を再利用して、そのファイバーの次数が `|H|` であることを
保持する。これは幾何学的な軌道根を因子分解へ渡す前の、分岐値を除外する
教科書的な前処理である。
-/
theorem exists_veluX_separable_coprime_fiber_avoiding
    (H : AddSubgroup (Points E)) [Fintype H]
    {s : Set (AlgebraicClosure K)} (hs : s.Finite) :
    ∃ F G : (AlgebraicClosure K)[X], ∃ c : AlgebraicClosure K,
      IsCoprime F G ∧ F.natDegree = Nat.card H ∧ G.natDegree < F.natDegree ∧
        veluX E H = aeval (genericX E (AlgebraicClosure K)) F /
          aeval (genericX E (AlgebraicClosure K)) G ∧
        (fiberPolynomial F G c).Separable ∧ c ∉ s ∧
          (fiberPolynomial F G c).natDegree = Nat.card H := by
  obtain ⟨r, hgap, hnum, hr⟩ := exists_veluX_rational_at_infinity E H
  let F : (AlgebraicClosure K)[X] := r.num
  let G : (AlgebraicClosure K)[X] := r.denom
  have hcop : IsCoprime F G := by
    simpa [F, G] using r.isCoprime_num_denom
  have hF : F.natDegree = Nat.card H := by simpa [F] using hnum
  have hGlt : G.natDegree < F.natDegree := by
    dsimp [F, G]
    omega
  have hw : wronskian F G ≠ 0 :=
    wronskian_ne_zero hcop (by rw [hF]; omega)
  obtain ⟨c, hcsep, hcs⟩ := exists_separable_fiber_avoiding hcop hw hs
  have hdeg : (fiberPolynomial F G c).natDegree = Nat.card H := by
    rw [fiberPolynomial_natDegree_eq_of_natDegree_lt (c := c) hGlt, hF]
  have hrel : veluX E H = aeval (genericX E (AlgebraicClosure K)) F /
      aeval (genericX E (AlgebraicClosure K)) G := by
    simpa [F, G] using hr
  exact ⟨F, G, c, hcop, hF, hGlt, hrel, hcsep, hcs, hdeg⟩

/-- [DkMath.Lib] 同じX_Hは各有限値を、同じ核の外の実際の点で取る。
分母非零・源の有限性・核外性・有限評価との一致を全て内部供給する。 -/
theorem exists_kernelXAt_eq (H : AddSubgroup (Points E)) [Fintype H] (c : AlgebraicClosure K) :
    ∃ (P : Points E) (hP : P ∉ H), kernelXAt E H P hP = c := by
  let k := AlgebraicClosure K
  let F := (E.toAffine⁄k).FunctionField
  let x := genericX E k
  obtain ⟨r, hdeg, _, hr⟩ := exists_veluX_rational_at_infinity E H
  obtain ⟨a, ha, hda⟩ := RationalFunctionFiniteFiber.exists_finite_fiber r (by omega) c
  obtain ⟨P, hP₀, hPx⟩ := exists_finite_point_with_x E a
  have hc (b : k) := pointValuation_const_le_one E P b
  have hxc : (pointValuation E P).Cong x (algebraMap k F a) := by
    have hh := value_spec E P x (pointValuation_genericX_le_one E P hP₀)
    rw [value_genericX E P hP₀, hPx] at hh
    exact hh
  have hpoly (p : k[X]) : (pointValuation E P).Cong (aeval x p) (algebraMap k F (p.eval a)) := by
    have hh := (Valuation.Cong.eval₂ (algebraMap k F) hc hxc (hc a) p).1
    rw [eval₂_at_apply] at hh
    exact hh
  have hd : pointValuation E P (aeval x r.denom) = 1 :=
    (hpoly r.denom).eq_of_eq_one (pointValuation_const_eq_one E P hda)
  have hreg : pointValuation E P (veluX E H) ≤ 1 := by
    rw [hr, map_div₀, hd, div_one]
    exact (hpoly r.num).le_one (hc _)
  have hP : P ∉ H := fun hm => (not_le_of_gt ((velu_pole_support E H P).1.mpr hm)) hreg
  refine ⟨P, hP, ?_⟩
  apply value_eq
  have hdiv := (hpoly r.num).div (hpoly r.denom) (hc _) (pointValuation_const_eq_one E P hda)
  have hconst : algebraMap k F (r.num.eval a) / algebraMap k F (r.denom.eval a) =
      algebraMap k F c := by
    rw [← map_div₀ (algebraMap k F), ha, mul_div_cancel_right₀ _ hda]
  rw [hconst] at hdiv
  exact hr.symm ▸ hdiv

/-- [DkMath.Lib] 同じ全点関数は同じ標的の全ての実点へ全射。
有限x値への到達と反転を使い、二つのy値のどちらにも到達する。OにはOを使う。 -/
theorem oddKernelPointMap_surjective (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) : Function.Surjective (oddKernelPointMap E H hodd) := by
  let := kernelModel_isElliptic_of_odd_card E H hodd
  intro T
  cases T with
  | zero => exact ⟨0, (oddKernelPointMap_eq_zero_iff E H hodd 0).mpr H.zero_mem⟩
  | some a b hT =>
    obtain ⟨P, hP, hx⟩ := exists_kernelXAt_eq E H a
    have heMap : oddKernelPointMap E H hodd P =
        Point.some _ _ (kernelAt_nonsingular E H P hP) := kernelPointMap_of_not_mem E H P hP
    have he : oddKernelPointMap E H hodd P = Point.some a b hT ∨
        oddKernelPointMap E H hodd P = -Point.some a b hT := by
      rw [heMap]
      exact Point.X_eq_iff.mp hx
    rcases he with he | he
    · exact ⟨P, he⟩
    · refine ⟨-P, ?_⟩
      have hn := congrArg Neg.neg he
      rw [neg_neg] at hn
      exact (oddKernelPointMap_neg E H hodd P).trans hn

/-- [DkMath.Lib] 標的の任意の点Tのファイバーには正確に|H|個の実点がある。
非空性を外部仮定にせず、同じ全点関数の全射性から内部供給する。 -/
theorem card_kernel_fiber (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (T : (kernelModel E H).toAffine.Point) :
    Nat.card {P : Points E // oddKernelPointMap E H hodd P = T} = Nat.card H := by
  obtain ⟨P, rfl⟩ := oddKernelPointMap_surjective E H hodd T
  exact card_kernel_image_fiber E H hodd P

/-- [DkMath.Lib] 安定核のK係数モデルへ移送した同じ全点関数も全射である。 -/
theorem descendedKernelPointMap_surjective (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (hH : ∀ σ P, P ∈ H → pointAction E σ P ∈ H) :
    Function.Surjective (descendedKernelPointMap E H hodd hH) :=
  (pointModelEquiv (descendedKernelModel_map E H hH)).symm.surjective.comp
    (oddKernelPointMap_surjective E H hodd)

/-- [DkMath.Lib] 同じK係数モデルへの移送でも、ファイバーは同じH剰余類のままである。 -/
theorem descendedKernelPointMap_eq_iff_sub_mem (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (hH : ∀ σ P, P ∈ H → pointAction E σ P ∈ H)
    (P R : Points E) :
    descendedKernelPointMap E H hodd hH P = descendedKernelPointMap E H hodd hH R ↔ R - P ∈ H := by
  rw [← oddKernelPointMap_eq_iff_sub_mem E H hodd P R]
  constructor
  · intro he
    have hh := congrArg (pointModelEquiv (descendedKernelModel_map E H hH)) he
    simpa only [descendedKernelPointMap_transport] using hh
  · intro he
    exact congrArg (pointModelEquiv (descendedKernelModel_map E H hH)).symm he

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
