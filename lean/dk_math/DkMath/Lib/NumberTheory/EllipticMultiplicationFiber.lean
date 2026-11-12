/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_WeierstrassCurve_Affine_valuation_weilNum.lean.
Upstream blob: 74864cced2b6198ce5ee7d72f60cb748f7647cab
Modified for DkMath: use natural-number fibers and proved DkMath cardinality/surjectivity; expose the general sum nT.
-/

import DkMath.Lib.Algebra.FiniteTorsionSum
import DkMath.Lib.NumberTheory.EllipticTorsionAllCard

#print "file: DkMath.Lib.NumberTheory.EllipticMultiplicationFiber"

/-!
# 実際の倍写像のファイバーとその総和

標数0の楕円曲線の代数閉包上の点群を使う。原像Rを一つ選ぶと
[n]P=Tの解はE[n]+Rとなり、同じ点を保持する全単射が得られる。
既存の全射性・有限核・位数公式から非空性・有限性・位数n²を供給する。
逆元による相殺と実際のE[2]の四元性から核の総和が零となり、
任意のファイバーの総和はnT、特にT∈E[n]なら零となる。
n=0は無限な核を持ち得るので有限ファイバーの定理から除く。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open DkMath.Lib.Algebra.FiniteTorsionSum
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]

open Classical in
/-- n倍写像の実際のファイバー。Tがtorsionであることは定義には要求しない。 -/
def fiberSet (n : ℕ) (T : Points E) : Set (Points E) := {P | n • P = T}

omit [CharZero K] [E.IsElliptic] in
open Classical in
/-- ファイバーへの所属は同じ点のn倍が目標点になること。 -/
@[simp] theorem mem_fiberSet (n : ℕ) (T P : Points E) : P ∈ fiberSet E n T ↔ n • P = T := Iff.rfl

open Classical in
/-- 原像Rを固定したとき、核とファイバーは平行移動で全単射になる。 -/
noncomputable def fiberEquiv (n : ℕ) (T R : Points E) (hR : n • R = T) :
    Torsion E n ≃ fiberSet E n T where
  toFun P := ⟨P.val + R, by rw [mem_fiberSet, smul_add, (show n • P.val = 0 from P.property), hR, zero_add]⟩
  invFun P := ⟨P.val - R, by
    change n • (P.val - R) = 0
    rw [smul_sub, (mem_fiberSet E n T P.val).mp P.property, hR, sub_self]⟩
  left_inv P := Subtype.ext (add_sub_cancel_right _ _)
  right_inv P := Subtype.ext (sub_add_cancel _ _)

open Classical in
/-- 非零指数の全射性から、全てのファイバーは非空である。 -/
theorem fiber_nonempty (n : ℕ) (hn : n ≠ 0) (T : Points E) : (fiberSet E n T).Nonempty :=
  multiplication_surjective E n hn T

open Classical in
/-- 核との平行移動全単射で有限性を運ぶ。有限性を仮定として受け取らない。 -/
theorem fiber_finite (n : ℕ) (hn : n ≠ 0) (T : Points E) : (fiberSet E n T).Finite := by
  obtain ⟨R, hR⟩ := fiber_nonempty E n hn T
  have := finite_torsion_of_ne_zero E n hn
  exact Set.finite_coe_iff.mp (Finite.of_equiv (Torsion E n) (fiberEquiv E n T R hR))

open Classical in
/-- 目標点によらずファイバーの点数はn²である。 -/
theorem fiber_card (n : ℕ) (hn : n ≠ 0) (T : Points E) : (fiberSet E n T).ncard = n ^ 2 := by
  obtain ⟨R, hR⟩ := fiber_nonempty E n hn T
  rw [← Nat.card_coe_set_eq, ← Nat.card_congr (fiberEquiv E n T R hR)]
  exact card_torsion_sq E n hn

open Classical in
/-- 核の有限点集合としての標準表示。 -/
noncomputable def torsionFinset (n : ℕ) (hn : n ≠ 0) : Finset (Points E) :=
  (fiber_finite E n hn 0).toFinset

open Classical in
/-- 有限集合への所属も同じn倍零条件である。 -/
@[simp] theorem mem_torsionFinset (n : ℕ) (hn : n ≠ 0) (P : Points E) :
    P ∈ torsionFinset E n hn ↔ n • P = 0 := (fiber_finite E n hn 0).mem_toFinset

open Classical in
/-- 実際のE[2]の四元性を一般群の相殺補題へ供給する。 -/
theorem sum_torsionFinset (n : ℕ) (hn : n ≠ 0) : ∑ P ∈ torsionFinset E n hn, P = 0 := by
  classical
  apply sum_kernel_eq_zero ?_ n _ (mem_torsionFinset E n hn)
  change Nat.card (Torsion E 2) = 4
  simpa only [show (2 : ℕ) ^ 2 = 4 from rfl] using card_torsion_sq E 2 (by decide)

open Classical in
/-- ファイバーは実際の核の有限集合をRだけ平行移動した集合である。 -/
theorem fiber_toFinset_eq_image (n : ℕ) (hn : n ≠ 0) (T R : Points E) (hR : n • R = T) :
    (fiber_finite E n hn T).toFinset = (torsionFinset E n hn).image (· + R) := by
  classical
  ext P
  simp only [Set.Finite.mem_toFinset, mem_fiberSet, Finset.mem_image, mem_torsionFinset]
  constructor
  · intro hP
    exact ⟨P - R, by rw [smul_sub, hP, hR, sub_self], sub_add_cancel _ _⟩
  · rintro ⟨Q, hQ, rfl⟩
    rw [smul_add, hQ, hR, zero_add]

open Classical in
/-- ファイバー総和の一般公式。Tがtorsionでない場合も総和はnTになる。 -/
theorem sum_fiber (n : ℕ) (hn : n ≠ 0) (T : Points E) :
    ∑ P ∈ (fiber_finite E n hn T).toFinset, P = n • T := by
  classical
  obtain ⟨R, hR⟩ := fiber_nonempty E n hn T
  rw [fiber_toFinset_eq_image E n hn T R hR,
    Finset.sum_image (fun _ _ _ _ h => add_right_cancel h), Finset.sum_add_distrib,
    sum_torsionFinset E n hn, zero_add, Finset.sum_const]
  have hc : (torsionFinset E n hn).card = n ^ 2 := by
    change (fiber_finite E n hn 0).toFinset.card = _
    rw [← Set.ncard_eq_toFinset_card (fiberSet E n 0) (fiber_finite E n hn 0),
      fiber_card E n hn 0]
  rw [hc, pow_two, mul_smul, hR]

open Classical in
/-- T∈E[n]のとき、ファイバーの総和は群の零点になる。n=1も含む。 -/
theorem sum_fiber_eq_zero (n : ℕ) (hn : n ≠ 0) (T : Points E) (hT : n • T = 0) :
    ∑ P ∈ (fiber_finite E n hn T).toFinset, P = 0 := by
  rw [sum_fiber E n hn T, hT]

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
