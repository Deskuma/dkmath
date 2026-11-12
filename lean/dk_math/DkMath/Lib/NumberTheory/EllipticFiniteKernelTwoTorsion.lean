/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Reconstructed from the orbit/fiber argument in
S_WeierstrassCurve_veluX_oddOrderSummingSet_injOn_psi2Sq_roots.lean,
blob 7d20d1868f13706680f16addb3fdaaeb58be9c51.
Modified: arbitrary odd finite subgroup; entire orbits and one strict x-fiber;
use the proved function-field degree instead of explicit Velu numerator formulas.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelRationalFiber
import DkMath.Lib.Algebra.StrictFiberCardinality

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelTwoTorsion"

/-!
# 奇数核の2捩れ像を、軌道とファイバーの個数で分離する

[DkMath.Lib] 異なる二つの反転固定点のH軌道は互いに素で、合計2|H|点。
x座標のファイバーは高々2点だが、反転固定点のファイバーは1点しかない。
従って軌道のx座標は|H|個より多い。一方、同じX_H値のファイバーは高々|H|個。
この矛盾が二つの2捩れ像を分離する。巡回生成元や半軌道の代表系を選ぶ必要はない。
-/
namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open Polynomial IntermediateField WeierstrassCurve WeierstrassCurve.Affine
open EllipticFunctionField EllipticTorsionRepresentation EllipticPointEvaluation
open DkMath.Lib.Algebra
variable {K : Type*} [Field K] [NeZero (2 : K)] (E : WeierstrassCurve K) [E.IsElliptic]
noncomputable local instance : DecidableEq (AlgebraicClosure K) := Classical.decEq _

omit [NeZero (2 : K)] [E.IsElliptic] in
/-- [DkMath.Lib] 奇数位数の核内の反転固定点はOだけである。 -/
theorem eq_zero_of_mem_odd_kernel_fixed (H : AddSubgroup (Points E))
    (hodd : Odd (Nat.card H)) (P : Points E) (hP : P ∈ H) (hn : -P = P) : P = 0 := by
  have htwo : 2 • P = 0 := by rw [two_nsmul]; simpa only [hn] using add_neg_cancel P
  have hd := addOrderOf_dvd_iff_nsmul_eq_zero.mpr htwo
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
  · simpa only [h1, one_nsmul] using addOrderOf_nsmul_eq_zero P
  · have hc := H.addOrderOf_dvd_natCard hP
    rw [h2] at hc
    have hm := Nat.mod_eq_zero_of_dvd hc
    have ho := Nat.odd_iff.mp hodd
    omega

omit [NeZero (2 : K)] [E.IsElliptic] in
/-- [DkMath.Lib] 有限点の同じx座標を持つ二点は、同じ点か互いの負である。 -/
theorem point_eq_or_eq_neg_of_xc_eq (P R : Points E) (hP : P ≠ 0) (hR : R ≠ 0)
    (hx : P.xc = R.xc) : P = R ∨ P = -R := by
  cases P with
  | zero => exact (hP rfl).elim
  | some x y h =>
    cases R with
    | zero => exact (hR rfl).elim
    | some x' y' h' => exact Point.X_eq_iff.mp hx

omit [NeZero (2 : K)] [E.IsElliptic] in
/-- [DkMath.Lib] 無限遠点を含まない有限集合の、x座標ファイバーは高々2点。 -/
theorem card_xc_fiber_le_two (s : Finset (Points E))
    (hs : ∀ P ∈ s, P ≠ 0) (a : AlgebraicClosure K) :
    (s.filter (fun P => P.xc = a)).card ≤ 2 := by
  classical
  by_cases he : (s.filter (fun P => P.xc = a)).Nonempty
  · obtain ⟨P, hP⟩ := he
    obtain ⟨hPs, hPa⟩ := Finset.mem_filter.mp hP
    have hsub : s.filter (fun R => R.xc = a) ⊆ {P, -P} := by
      intro R hR
      obtain ⟨hRs, hRa⟩ := Finset.mem_filter.mp hR
      simpa only [Finset.mem_insert, Finset.mem_singleton] using
        point_eq_or_eq_neg_of_xc_eq E R P (hs R hRs) (hs P hPs) (hRa.trans hPa.symm)
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  · simp only [Finset.not_nonempty_iff_eq_empty.mp he, Finset.card_empty, zero_le]

omit [NeZero (2 : K)] [E.IsElliptic] in
/-- [DkMath.Lib] 反転固定点のx座標ファイバーは高々1点。厳密計数の余裕をここで得る。 -/
theorem card_xc_fiber_le_one_of_fixed (s : Finset (Points E))
    (hs : ∀ P ∈ s, P ≠ 0) (P : Points E) (hP : P ≠ 0) (hn : -P = P) :
    (s.filter (fun R => R.xc = P.xc)).card ≤ 1 := by
  classical
  apply (Finset.card_le_card (show s.filter (fun R => R.xc = P.xc) ⊆ {P} from ?_)).trans_eq
    (Finset.card_singleton P)
  intro R hR
  obtain ⟨hRs, hRx⟩ := Finset.mem_filter.mp hR
  rcases point_eq_or_eq_neg_of_xc_eq E R P (hs R hRs) hP hRx with he | he
  · exact Finset.mem_singleton.mpr he
  · exact Finset.mem_singleton.mpr (he.trans hn)

/-- [DkMath.Lib] 奇数位数の同じ有限核の外にある非零反転固定点のx像は単射。
数値次数やファイバー上界は外部入力にせず、同じ有理関数から内部供給する。 -/
theorem kernelXAt_injective_on_twoTorsion (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (P R : Points E)
    (hPn : -P = P) (hRn : -R = R) (hP : P ∉ H) (hR : R ∉ H)
    (he : kernelXAt E H P hP = kernelXAt E H R hR) : P = R := by
  classical
  by_contra hne
  let sP := Finset.univ.image (fun Q : H => P + Q.val)
  let sR := Finset.univ.image (fun Q : H => R + Q.val)
  let s := sP ∪ sR
  let t := s.image (fun Q => Q.xc)
  have hmemP (Q : Points E) : Q ∈ sP ↔ Q - P ∈ H := by
    constructor
    · rintro h
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp h
      simpa only [add_sub_cancel_left] using q.property
    · intro h
      exact Finset.mem_image.mpr ⟨⟨Q - P, h⟩, Finset.mem_univ _, by change P + (Q - P) = Q; abel⟩
  have hmemR (Q : Points E) : Q ∈ sR ↔ Q - R ∈ H := by
    constructor
    · rintro h
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp h
      simpa only [add_sub_cancel_left] using q.property
    · intro h
      exact Finset.mem_image.mpr ⟨⟨Q - R, h⟩, Finset.mem_univ _, by change R + (Q - R) = Q; abel⟩
  have hdisj : Disjoint sP sR := by
    apply Finset.disjoint_left.mpr
    intro Q hQp hQr
    have hd : P - R ∈ H := by
      have h := H.sub_mem ((hmemR Q).mp hQr) ((hmemP Q).mp hQp)
      convert h using 1; abel
    have hn : -(P - R) = P - R := by
      calc -(P - R) = -P - -R := by abel
        _ = P - R := congrArg₂ (fun a b : Points E => a - b) hPn hRn
    exact hne (sub_eq_zero.mp (eq_zero_of_mem_odd_kernel_fixed E H hodd _ hd hn))
  have hcP : sP.card = Fintype.card H := by
    rw [Finset.card_image_of_injective _ (fun a b h => Subtype.ext (add_left_cancel h)), Finset.card_univ]
  have hcR : sR.card = Fintype.card H := by
    rw [Finset.card_image_of_injective _ (fun a b h => Subtype.ext (add_left_cancel h)), Finset.card_univ]
  have hcs : s.card = 2 * Nat.card H := by
    dsimp only [s]
    rw [Finset.card_union_of_disjoint hdisj, hcP, hcR, Nat.card_eq_fintype_card]
    omega
  have hout : ∀ Q ∈ s, Q ∉ H := by
    intro Q hQ hQH
    rcases Finset.mem_union.mp hQ with hp | hr
    · have h := H.sub_mem hQH ((hmemP Q).mp hp)
      exact hP (by convert h using 1; abel)
    · have h := H.sub_mem hQH ((hmemR Q).mp hr)
      exact hR (by convert h using 1; abel)
  have hs0 : ∀ Q ∈ s, Q ≠ 0 := fun Q hQ hz => hout Q hQ (hz ▸ H.zero_mem)
  have hPs : P ∈ s := Finset.mem_union_left _ ((hmemP P).mpr (by simp))
  have htcard : t.card ≤ Nat.card H := by
    apply card_veluX_fiber_le E H (kernelXAt E H P hP) t
    intro a ha
    obtain ⟨Q, hQs, rfl⟩ := Finset.mem_image.mp ha
    refine ⟨Q, hout Q hQs, rfl, ?_⟩
    rcases Finset.mem_union.mp hQs with hQp | hQr
    · obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hQp
      exact kernelXAt_translation E H P hP q
    · obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hQr
      exact (kernelXAt_translation E H R hR q).trans he.symm
  have hstrict : s.card < 2 * t.card := StrictFiberCardinality.card_lt_mul s t (fun Q => Q.xc) 2
    (fun Q hQ => Finset.mem_image_of_mem _ hQ)
    (fun a _ => card_xc_fiber_le_two E s hs0 a) P.xc (Finset.mem_image_of_mem _ hPs)
    ((card_xc_fiber_le_one_of_fixed E s hs0 P (hs0 P hPs) hPn).trans_lt (by decide))
  omega

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
