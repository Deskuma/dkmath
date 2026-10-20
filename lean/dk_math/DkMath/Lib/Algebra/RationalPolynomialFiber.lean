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
