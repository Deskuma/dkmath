/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_WeierstrassCurve_Affine_weilPairing0_self.lean.
Upstream blob: 9a0a55370677bf36f3a3b4e49cfc56626dd7c024
Modified for DkMath: telescope integer point orders, use the existing unique-constant
criterion, retain explicit nonzero factors, and expose the same translation eigenvalue.
-/

import DkMath.Lib.NumberTheory.EllipticWeilRightAdd

#print "file: DkMath.Lib.NumberTheory.EllipticWeilAlternating"

/-!
# 軌道積の位数の相殺から交代性を得る

nU=Tを選び、H=∏ᵢ₌₀ⁿ⁻¹τ(iU)*w(T)を作る。各因子は非零である。
各点の位数はd(i−1)−d(i)となり、nT=Oによる周期性で端点も相殺する。
従ってHは非零定数で、Uによる移動で固定される。積の共通する非零因子を消すと
τ(nU)*w(T)=w(T)を得る。一意な固有値は1であり、c(T,T)=1が従う。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open WeierstrassCurve WeierstrassCurve.Affine
open EllipticFunctionField

/-- 周期的な整数列の差分を一周期足すと0となる。添字−1も端点として明示する。 -/
theorem sum_range_periodic_difference (n : ℕ) (d : ℤ → ℤ)
    (hd : ∀ j, d (j + n) = d j) :
    (∑ i ∈ Finset.range n, (d ((i : ℤ) - 1) - d i)) = 0 := by
  cases n with
  | zero => simp
  | succ m =>
    rw [Finset.sum_sub_distrib, Finset.sum_range_succ', Finset.sum_range_succ]
    have hi : (fun i : ℕ => d (((i + 1 : ℕ) : ℤ) - 1)) = fun i : ℕ => d i := by
      funext i
      congr 1
      omega
    rw [hi]
    have he : d (m : ℤ) = d (-1) := by
      have hidx : (-1 : ℤ) + (m + 1 : ℕ) = (m : ℤ) := by omega
      simpa only [hidx] using hd (-1)
    simp only [Nat.cast_zero, zero_sub, he]
    omega

variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]

open Classical in
/-- 任意の移動点Uに沿うn個の実際の引き戻しの有限積。nU=Tは位数の相殺に使う条件。 -/
noncomputable def weilTranslateOrbitProduct (n : ℕ) (hn : n ≠ 0) (T : Points E)
    (hT : n • T = 0) (U : Points E) : (E.toAffine⁄(AlgebraicClosure K)).FunctionField :=
  ∏ i ∈ Finset.range n, transEquiv E (AlgebraicClosure K) (i • U) (weilFunction E n hn T hT)

open Classical in
/-- 全ての因子は非零関数の自己同型像なので、軌道積も非零である。 -/
theorem weilTranslateOrbitProduct_ne_zero (n : ℕ) (hn : n ≠ 0) (T : Points E)
    (hT : n • T = 0) (U : Points E) : weilTranslateOrbitProduct E n hn T hT U ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact (transEquiv E (AlgebraicClosure K) (i • U)).toRingEquiv.map_ne_zero_iff.mpr
    (weilFunction_ne_zero E n hn T hT)

/-- nU=Tなら軌道積の位数は全点で0。有限点とOを別々に数え直す必要はない。 -/
theorem pointOrder_weilTranslateOrbitProduct (n : ℕ) (hn : n ≠ 0) (T : Points E)
    (hT : n • T = 0) (U : Points E) (hU : n • U = T) (P : Points E) :
    pointOrder E P (weilTranslateOrbitProduct E n hn T hT U)
      (weilTranslateOrbitProduct_ne_zero E n hn T hT U) = 0 := by
  classical
  let d : ℤ → ℤ := fun j => if n • P + j • T = 0 then 1 else 0
  have hd : ∀ j, d (j + n) = d j := by
    intro j
    simp only [d, add_smul, natCast_zsmul, hT, add_zero]
  have hi (i : ℕ) :
      pointOrder E P (transEquiv E (AlgebraicClosure K) (i • U) (weilFunction E n hn T hT))
        ((transEquiv E (AlgebraicClosure K) (i • U)).toRingEquiv.map_ne_zero_iff.mpr
          (weilFunction_ne_zero E n hn T hT)) = d ((i : ℤ) - 1) - d i := by
    have hs : n • (P + i • U) = n • P + (i : ℤ) • T := by
      rw [smul_add, smul_comm n i U, hU, natCast_zsmul]
    have e1 : n • (P + i • U) = T ↔ n • P + ((i : ℤ) - 1) • T = 0 := by
      rw [hs, sub_smul, one_smul, ← add_sub_assoc, sub_eq_zero]
    have e2 : n • (P + i • U) = 0 ↔ n • P + (i : ℤ) • T = 0 := by rw [hs]
    apply (pointOrder_transEquiv_weilFunction E n hn T hT P (i • U)).trans
    simp only [e1, e2, d]
  have hp := pointOrder_prod E P (Finset.range n)
    (fun i => transEquiv E (AlgebraicClosure K) (i • U) (weilFunction E n hn T hT))
    (fun i => (transEquiv E (AlgebraicClosure K) (i • U)).toRingEquiv.map_ne_zero_iff.mpr
      (weilFunction_ne_zero E n hn T hT))
  exact hp.trans ((Finset.sum_congr rfl (fun i _ => hi i)).trans (sum_range_periodic_difference n d hd))

/-- 位数0の軌道積は一意な非零定数に一致する。定数性を独立の仮定として置かない。 -/
theorem existsUnique_unit_weilTranslateOrbitProduct (n : ℕ) (hn : n ≠ 0) (T : Points E)
    (hT : n • T = 0) (U : Points E) (hU : n • U = T) :
    ∃! a : (AlgebraicClosure K)ˣ,
      weilTranslateOrbitProduct E n hn T hT U =
        algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField (a : AlgebraicClosure K) :=
  existsUnique_unit_of_pointOrder_zero E _ (weilTranslateOrbitProduct_ne_zero E n hn T hT U)
    (pointOrder_weilTranslateOrbitProduct E n hn T hT U hU)

open Classical in
/-- 軌道積を一つずらし、共通因子を消去することで、目標T自身による移動がw(T)を固定する。 -/
theorem transEquiv_weilFunction_self (n : ℕ) (hn : n ≠ 0) (T : Points E) (hT : n • T = 0) :
    transEquiv E (AlgebraicClosure K) T (weilFunction E n hn T hT) = weilFunction E n hn T hT := by
  obtain ⟨U, hU⟩ := multiplication_surjective E n hn T
  change n • U = T at hU
  let a : ℕ → (E.toAffine⁄(AlgebraicClosure K)).FunctionField :=
    fun i => transEquiv E (AlgebraicClosure K) (i • U) (weilFunction E n hn T hT)
  have ha (i : ℕ) : a i ≠ 0 :=
    (transEquiv E (AlgebraicClosure K) (i • U)).toRingEquiv.map_ne_zero_iff.mpr
      (weilFunction_ne_zero E n hn T hT)
  have hstep (i : ℕ) : transEquiv E (AlgebraicClosure K) U (a i) = a (i + 1) := by
    have hs : U + i • U = (i + 1) • U := by rw [succ_nsmul, add_comm]
    exact (transEquiv_comp_apply E U (i • U) _).trans
      (congrArg (fun Q => transEquiv E (AlgebraicClosure K) Q (weilFunction E n hn T hT)) hs)
  obtain ⟨c, hc, -⟩ := existsUnique_unit_weilTranslateOrbitProduct E n hn T hT U hU
  have hfix : transEquiv E (AlgebraicClosure K) U (∏ i ∈ Finset.range n, a i) =
      ∏ i ∈ Finset.range n, a i := by
    change transEquiv E (AlgebraicClosure K) U (weilTranslateOrbitProduct E n hn T hT U) = _
    rw [hc, AlgEquiv.commutes]
    exact hc.symm
  have hshift : (∏ i ∈ Finset.range n, a (i + 1)) = ∏ i ∈ Finset.range n, a i := by
    calc
      _ = transEquiv E (AlgebraicClosure K) U (∏ i ∈ Finset.range n, a i) := by
        rw [map_prod]
        exact Finset.prod_congr rfl (fun i _ => (hstep i).symm)
      _ = _ := hfix
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [hm, Finset.prod_range_succ, Finset.prod_range_succ' a] at hshift
  have hcancel := mul_left_cancel₀ (Finset.prod_ne_zero_iff.mpr (fun i _ => ha (i + 1))) hshift
  have hlast : a (m + 1) = transEquiv E (AlgebraicClosure K) T (weilFunction E n hn T hT) := by
    dsimp only [a]
    have hs : (m + 1) • U = T := by simpa only [hm] using hU
    exact congrArg (fun Q => transEquiv E (AlgebraicClosure K) Q (weilFunction E n hn T hT)) hs
  have hzero : a 0 = weilFunction E n hn T hT := by
    change transEquiv E (AlgebraicClosure K) 0 (weilFunction E n hn T hT) = _
    rw [transEquiv_zero]
    rfl
  exact hlast.symm.trans (hcancel.trans hzero)

/-- 同じ実際の移動固有値の交代性。単なる二乗1より強いc(T,T)=1を固定する。 -/
theorem weilTranslationUnit_self (n : ℕ) (hn : n ≠ 0) (T : Torsion E n) :
    weilTranslationUnit E n hn T T = 1 := by
  classical
  apply Eq.symm
  apply weilTranslationUnit_unique E n hn T T 1
  have hT : n • T.val = 0 := T.property
  change transEquiv E (AlgebraicClosure K) T.val (weilFunction E n hn T.val hT) =
    algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField (1 : AlgebraicClosure K) *
      weilFunction E n hn T.val hT
  simpa only [map_one, one_mul] using transEquiv_weilFunction_self E n hn T.val hT

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
