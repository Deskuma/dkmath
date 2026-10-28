/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: ../NumberTheory/RegularKummer/LICENSE
Upstream notices: ../NumberTheory/RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_WeierstrassCurve_card_torsion_of_isAlgClosed.lean, finite_not_squarefree_fiber.
Modified for DkMath: generic polynomial API, characteristic zero, separability and coprime derivative proof.
-/

import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

#print "file: DkMath.Lib.Algebra.RationalPolynomialFiber"

/-!
# 有理関数の通常のファイバーと、有限個の例外値

互いに素な分子F・分母GからH_c=F−cGを作る。Wronskian F'G−FG'が非零なら、
H_cが重根を持つようなcは有限個しかない。重根xではH_c(x)=H_c'(x)=0なので、
Wronskianもxで消える。共通根がないためG(x)≠0となり、c=F(x)/G(x)と復元できる。
従って例外値はWronskianの有限根集合の像に含まれる。

標数0では、Fが非定数でFとGが互いに素ならWronskianは非零である。
もし零ならFがF'Gを割り、互いに素性からFがF'を割って次数の減少に反する。
楕円曲線やFLTの定理には依存しない。有限な例外を避ける際には、代数閉体が無限であることを使う。
-/
namespace DkMath.Lib.Algebra.RationalPolynomialFiber
open Polynomial
variable {K : Type*} [Field K]

/-- 分子・分母の比の変化を検出する多項式。符号の規約をここで固定する。 -/
noncomputable def wronskian (F G : K[X]) : K[X] := F.derivative * G - F * G.derivative

/-- ファイバーのx座標を与える一変数多項式。 -/
noncomputable def fiberPolynomial (F G : K[X]) (c : K) : K[X] := F - C c * G

/-- [DkMath.Lib] 分母次数が小さいファイバーは分子次数を保つ。

`H_c = F-cG` で `deg G < deg F` なら、`cG` の次数は `F` より小さいため、
最高次係数の打消しは起こらない。従って有限値 `c` に依らず
`natDegree (H_c) = natDegree F` となる。Vélu の `X_H` では、無限遠点の極位数
からこの次数条件を供給できるので、ファイバーの次数上界を exact degree へ
強化するための基本補題になる。 -/
theorem fiberPolynomial_natDegree_eq_of_natDegree_lt
    {F G : K[X]} {c : K} (hdeg : G.natDegree < F.natDegree) :
    (fiberPolynomial F G c).natDegree = F.natDegree := by
  rw [fiberPolynomial, natDegree_sub_eq_left_of_natDegree_lt]
  exact (natDegree_C_mul_le c G).trans_lt hdeg

/-- 互いに素な多項式は共通根を持たない。 -/
theorem eval_denominator_ne_zero {F G : K[X]} (h : IsCoprime F G) {x c : K}
    (hx : (fiberPolynomial F G c).IsRoot x) : G.eval x ≠ 0 := by
  intro hG
  have hF : F.eval x = 0 := by
    have hh := hx
    change (F - C c * G).eval x = 0 at hh
    simpa only [eval_sub, eval_mul, eval_C, hG, mul_zero, sub_zero] using hh
  obtain ⟨a, b, hab⟩ := h
  have hh := congrArg (Polynomial.eval x) hab
  simp only [eval_add, eval_mul, eval_one, hF, hG, mul_zero, zero_add] at hh
  exact zero_ne_one hh

/-- [DkMath.Lib] ファイバーの重根条件を Wronskian の根条件へ移す。

`H_c = F - cG` の根 `x` では、`G(x) ≠ 0` が互いに素性から従う。
したがって `H_c'(x) = 0` は
`F'(x)G(x) - F(x)G'(x) = 0`、すなわち Wronskian が `x` で消えることと
同値である。この補題は「ファイバー側の微分零点」と「分子・分母比の
臨界点」を結ぶ、有限例外値論の基本的な橋である。 -/
theorem fiberPolynomial_derivative_isRoot_iff_wronskian_isRoot
    {F G : K[X]} (h : IsCoprime F G) {x c : K}
    (hx : (fiberPolynomial F G c).IsRoot x) :
    (fiberPolynomial F G c).derivative.IsRoot x ↔
      (wronskian F G).IsRoot x := by
  have hg : G.eval x ≠ 0 := eval_denominator_ne_zero h hx
  have hFx : F.eval x = c * G.eval x := by
    have hx' := hx
    change (fiberPolynomial F G c).eval x = 0 at hx'
    simpa only [fiberPolynomial, eval_sub, eval_mul, eval_C, sub_eq_zero] using hx'
  constructor
  · intro hdx
    have hdx' := hdx
    change (fiberPolynomial F G c).derivative.eval x = 0 at hdx'
    have hFdx : F.derivative.eval x - c * G.derivative.eval x = 0 := by
      simpa only [fiberPolynomial, derivative_sub, derivative_C_mul, eval_sub, eval_mul,
        eval_C, sub_eq_zero] using hdx'
    change (wronskian F G).eval x = 0
    simp only [wronskian, eval_sub, eval_mul]
    rw [hFx]
    calc
      F.derivative.eval x * G.eval x - (c * G.eval x) * G.derivative.eval x =
          (F.derivative.eval x - c * G.derivative.eval x) * G.eval x := by ring
      _ = 0 := by rw [hFdx, zero_mul]
  · intro hw
    change (fiberPolynomial F G c).derivative.eval x = 0
    have hprod : (F.derivative.eval x - c * G.derivative.eval x) * G.eval x = 0 := by
      have hw' := hw
      change (wronskian F G).eval x = 0 at hw'
      simp only [wronskian, eval_sub, eval_mul] at hw'
      change F.derivative.eval x * G.eval x - F.eval x * G.derivative.eval x = 0 at hw'
      rw [hFx] at hw'
      calc
        (F.derivative.eval x - c * G.derivative.eval x) * G.eval x =
            F.derivative.eval x * G.eval x - (c * G.eval x) * G.derivative.eval x := by ring
        _ = 0 := hw'
    have hFdx : F.derivative.eval x - c * G.derivative.eval x = 0 :=
      (mul_eq_zero.mp hprod).resolve_right hg
    simpa only [fiberPolynomial, derivative_sub, derivative_C_mul, eval_sub, eval_mul,
      eval_C, sub_eq_zero] using hFdx

/-- [DkMath.Lib] Wronskian の零点は、対応するファイバーの二重根を与える。

非零ファイバー多項式 `H_c` の根 `x` で Wronskian も消えるなら、前補題により
`H_c'(x) = 0` である。従って `Polynomial.one_lt_rootMultiplicity_iff_isRoot`
を適用すれば、`x` の根多重度は少なくとも2になる。これは有限ファイバーの
「分岐点なら二重因子」という主張を、幾何学的な分岐理論なしに使える
一変数多項式の教科書形へ落としたものである。 -/
theorem rootMultiplicity_ge_two_of_fiberPolynomial_root_of_wronskian_root
    {F G : K[X]} (h : IsCoprime F G) {x c : K}
    (hp : fiberPolynomial F G c ≠ 0)
    (hx : (fiberPolynomial F G c).IsRoot x)
    (hw : (wronskian F G).IsRoot x) :
    2 ≤ (fiberPolynomial F G c).rootMultiplicity x := by
  have hdx : (fiberPolynomial F G c).derivative.IsRoot x :=
    (fiberPolynomial_derivative_isRoot_iff_wronskian_isRoot h hx).mpr hw
  have hlt : 1 < (fiberPolynomial F G c).rootMultiplicity x :=
    (Polynomial.one_lt_rootMultiplicity_iff_isRoot hp).mpr ⟨hx, hdx⟩
  omega

/-- [DkMath.Lib] 分離ファイバーの根では Wronskian は消えない。

前定理は、ファイバー根と Wronskian 零点の同時成立が二重根を生むことを
示した。分離性は全ての根の多重度を高々1に抑えるので、その対偶として
`Separable (F-cG)` の根では Wronskian が非零となる。この補題は、有限個の
分岐値を避ける一般論と、軌道全体で Wronskian 零点を要求する因子同定経路を
明確に分離するための教科書的な境界である。
-/
theorem not_wronskian_isRoot_of_separable_fiberPolynomial
    {F G : K[X]} (h : IsCoprime F G) {x c : K}
    (hp : (fiberPolynomial F G c).Separable)
    (hx : (fiberPolynomial F G c).IsRoot x) :
    ¬ (wronskian F G).IsRoot x := by
  intro hw
  have hmult : 2 ≤ (fiberPolynomial F G c).rootMultiplicity x :=
    rootMultiplicity_ge_two_of_fiberPolynomial_root_of_wronskian_root h
      (by
        exact hp.ne_zero)
      hx hw
  have hle : (fiberPolynomial F G c).rootMultiplicity x ≤ 1 :=
    Polynomial.rootMultiplicity_le_one_of_separable hp x
  omega

/-- 標数0の非定数の分子では、互いに素性と微分の次数減少からWronskianが非零となる。 -/
theorem wronskian_ne_zero [CharZero K] {F G : K[X]} (h : IsCoprime F G) (hF : 0 < F.natDegree) :
    wronskian F G ≠ 0 := by
  intro hw
  have he : F.derivative * G = F * G.derivative := sub_eq_zero.mp hw
  have hdvd : F ∣ F.derivative := h.dvd_of_dvd_mul_right (by rw [he]; exact dvd_mul_right _ _)
  have hder : F.derivative ≠ 0 := Polynomial.derivative_ne_zero.mpr hF.ne'
  have hle := Polynomial.natDegree_le_of_dvd hdvd hder
  have hlt := Polynomial.natDegree_derivative_lt hF.ne'
  exact (not_le_of_gt hlt) hle

/-- 重根を持つファイバーの値はWronskianの根の像に含まれ、従って有限である。 -/
theorem finite_not_separable_fiber [IsAlgClosed K] {F G : K[X]} (h : IsCoprime F G)
    (hw : wronskian F G ≠ 0) : {c : K | ¬ (fiberPolynomial F G c).Separable}.Finite := by
  classical
  have hr : {x : K | (wronskian F G).IsRoot x}.Finite := Polynomial.finite_setOfPred_isRoot hw
  apply (hr.image (fun x => F.eval x / G.eval x)).subset
  intro c hc
  have hn : ¬ IsCoprime (fiberPolynomial F G c) (fiberPolynomial F G c).derivative := hc
  rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := K) (K := K)] at hn
  push Not at hn
  obtain ⟨x, hx, hdx⟩ := hn
  rw [coe_aeval_eq_eval] at hx hdx
  have hg := eval_denominator_ne_zero h (show (fiberPolynomial F G c).IsRoot x from hx)
  have hFx : F.eval x = c * G.eval x := by
    simpa only [fiberPolynomial, eval_sub, eval_mul, eval_C, sub_eq_zero] using hx
  have hFdx : F.derivative.eval x = c * G.derivative.eval x := by
    simpa only [fiberPolynomial, derivative_sub, derivative_C_mul, eval_sub, eval_mul,
      eval_C, sub_eq_zero] using hdx
  refine ⟨x, ?_, ?_⟩
  · change (wronskian F G).eval x = 0
    simp only [wronskian, eval_sub, eval_mul, hFx, hFdx]
    ring
  · change F.eval x / G.eval x = c
    rw [hFx, mul_div_cancel_right₀ _ hg]

/-- 平方因子を持つファイバーも有限個しかない。分離的なら平方因子を持たない。 -/
theorem finite_not_squarefree_fiber [IsAlgClosed K] {F G : K[X]} (h : IsCoprime F G)
    (hw : wronskian F G ≠ 0) : {c : K | ¬ Squarefree (fiberPolynomial F G c)}.Finite :=
  (finite_not_separable_fiber h hw).subset (fun _ hc hs => hc hs.squarefree)

/-- 例外値を避けた分離的なファイバーが存在する。追加の有限集合も同時に避けられる。 -/
theorem exists_separable_fiber_avoiding [IsAlgClosed K] {F G : K[X]} (h : IsCoprime F G)
    (hw : wronskian F G ≠ 0) {s : Set K} (hs : s.Finite) :
    ∃ c : K, (fiberPolynomial F G c).Separable ∧ c ∉ s := by
  obtain ⟨c, hc⟩ := ((finite_not_separable_fiber h hw).union hs).infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hc
  exact ⟨c, hc⟩

end DkMath.Lib.Algebra.RationalPolynomialFiber
