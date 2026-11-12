/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Invariant reconstruction inspired by
P2M/Sol/S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_c4_c6_discriminant_of_nodal.lean,
blob fbe8b46b385ec6f97df009c8cb22a7e62c104cc8.
Modified: existing DkMath Frame and tc; arbitrary indexed inversion halves;
explicit injective kernel hom instead of a new normal-form quotient.
-/

import DkMath.Lib.NumberTheory.WeierstrassNodalFrame
import DkMath.Lib.NumberTheory.OddRootPairMoments
import DkMath.Lib.Algebra.FiniteInversionHalf

#print "file: DkMath.Lib.NumberTheory.WeierstrassNodalVelu"

/-!
# 同じ節点曲線・同じ半核による商の不変量

[DkMath.Lib] 核を選び直さず、単射な準同型fと巡回表示eを使い、既存の半核sの和を正の半周へ移す。
反転不変性で代表の選び方を吸収し、既存節点比tcの原始根と有限モーメントを適用する。
判別式零は専用の整数証明書から直接示す。c₄³−c₆²=1728Δを約分しない。
-/
namespace DkMath.Lib.NumberTheory.WeierstrassNodalVelu
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassVeluPolynomial
open EllipticNodalTorsion.NodalTorsion WeierstrassNodalFrame
open DkMath.Lib.Algebra.FiniteInversionHalf
open scoped BigOperators

/-- [DkMath.Lib] b₈の補正式。関係式の4による約分を避け、係数から直接証明する。 -/
theorem polynomialModel_b8 {R ι : Type*} [CommRing R] (W : WeierstrassCurve R)
    (s : Finset ι) (x y : ι → R) :
    (polynomialModel W s x y).b₈ = W.b₈ - W.b₂ ^ 2 * (∑ i ∈ s, momentT W (x i))
      + 5 * W.b₄ * (∑ i ∈ s, momentT W (x i)) - 7 * W.b₂ * (∑ i ∈ s, momentW W (x i) (y i))
      - 25 * (∑ i ∈ s, momentT W (x i)) ^ 2 := by
  simp only [polynomialModel,b₂,b₄,b₈]
  ring

/-- [DkMath.Lib] 曲線上ではwをxだけの三次式として書ける。無限遠の便宜座標には適用しない。 -/
theorem momentW_eq_cubic {k : Type*} [Field k] (W : WeierstrassCurve k) {x y : k}
    (he : W.toAffine.Equation x y) :
    momentW W x y = 10 * x ^ 3 + 2 * W.b₂ * x ^ 2 + 3 * W.b₄ * x + W.b₆ := by
  rw [equation_iff] at he
  simp only [momentW,momentT,b₂,b₄,b₆]
  linear_combination 4 * he

variable {k : Type*} [Field k] [DecidableEq k] (W : WeierstrassCurve k)

omit [DecidableEq k] in
/-- [DkMath.Lib] 実点の反転は二つのモーメントを保つ。OはO自身として別に処理する。 -/
theorem point_moments_neg (P : W.toAffine.Point) :
    momentT W (-P).xc = momentT W P.xc ∧ momentW W (-P).xc (-P).yc = momentW W P.xc P.yc := by
  rcases P with _ | ⟨x,y,h⟩
  · exact ⟨rfl,rfl⟩
  · rw [Point.neg_some]
    exact ⟨rfl,momentW_negY W x y⟩

/-- [DkMath.Lib] 単射な同じ巡回核と任意の同じ半集合から作る節点商の不変量。
標数0や2,3可逆性を仮定せず、源の楕円性も要求しない。剰余の節点へ適用するためである。 -/
theorem polynomialModel_invariants {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {n : ℕ} (hn : Odd n) (e : ZMod n ≃+ G) (f : G →+ W.toAffine.Point) (hf : Function.Injective f)
    (s : Finset G) (hs : IsHalf s) {x₀ y₀ α : k} (F : Frame W x₀ y₀ α)
    (hsep : α ≠ -W.a₁ - α) :
    (polynomialModel W s (fun q => (f q).xc) (fun q => (f q).yc)).c₄ = (n : k) ^ 4 * W.c₄ ∧
      (polynomialModel W s (fun q => (f q).xc) (fun q => (f q).yc)).c₆ = (n : k) ^ 6 * W.c₆ ∧
      (polynomialModel W s (fun q => (f q).xc) (fun q => (f q).yc)).Δ = 0 := by
  let P := f (e 1)
  have hord : addOrderOf P = n :=
    (addOrderOf_injective f hf (e 1)).trans ((e.addOrderOf_eq 1).trans (ZMod.addOrderOf_one n))
  let u := tc W x₀ y₀ α P
  let δ := 2 * α + W.a₁
  let z := fun j : ℕ => u ^ j / (1 - u ^ j) ^ 2
  have hu : IsPrimitiveRoot u n := hord ▸ primitiveRoot_tc F hsep P
  have hz (j : ℕ) (hj : j ∈ Finset.Icc 1 (n/2)) : z j * (1 - u ^ j) ^ 2 = u ^ j := by
    have hj' := Finset.mem_Icc.mp hj
    have hjn : j < n := lt_of_le_of_lt hj'.2 (Nat.div_lt_self hn.pos (by decide))
    exact div_mul_cancel₀ _ (pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm
      (hu.pow_ne_one_of_pos_of_lt (by omega) hjn))))
  obtain ⟨hT,hW,hD⟩ := OddRootPairMoments.weighted_moments hu hn z hz
  let τ := ∑ j ∈ Finset.Icc 1 (n/2), (z j + 6 * z j ^ 2)
  let ω := ∑ j ∈ Finset.Icc 1 (n/2), (2 * z j ^ 2 + 10 * z j ^ 3)
  obtain ⟨hb2,hb4,hb6,hb8⟩ := b_invariants F
  have he (j : ℕ) : f (e (j : ZMod n)) = j • P := by
    rw [← Nat.smul_one_eq_cast, map_nsmul, map_nsmul]
  have hxc (j : ℕ) (hj : j ∈ Finset.Icc 1 (n/2)) : (f (e (j : ZMod n))).xc = x₀ + δ ^ 2 * z j := by
    rw [he]
    exact nsmul_xc F hsep P hord (Finset.mem_Icc.mp hj).1
      (lt_of_le_of_lt (Finset.mem_Icc.mp hj).2 (Nat.div_lt_self hn.pos (by decide)))
  have hsumT : (∑ q ∈ s, momentT W (f q).xc) = δ ^ 4 * τ := by
    rw [sum_eq_cyclic hn e hs _ (fun q => by rw [map_neg]; exact (point_moments_neg W (f q)).1)]
    dsimp only [τ]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [momentT,hxc j hj,hb2,hb4]
    dsimp only [δ]
    ring
  have hsumW : (∑ q ∈ s, momentW W (f q).xc (f q).yc) = δ ^ 6 * ω + x₀ * (δ ^ 4 * τ) := by
    rw [sum_eq_cyclic hn e hs _ (fun q => by rw [map_neg]; exact (point_moments_neg W (f q)).2)]
    dsimp only [τ,ω]
    rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hne : f (e (j : ZMod n)) ≠ 0 := by
      intro hh
      have ha : addOrderOf P ∣ j := addOrderOf_dvd_iff_nsmul_eq_zero.mpr ((he j).symm ▸ hh)
      rw [hord] at ha
      exact (not_le.mpr (lt_of_le_of_lt (Finset.mem_Icc.mp hj).2 (Nat.div_lt_self hn.pos (by decide))))
        (Nat.le_of_dvd (Finset.mem_Icc.mp hj).1 ha)
    rw [momentW_eq_cubic W (Point.nonsingular_xc_yc hne).1,hxc j hj,hb2,hb4,hb6]
    dsimp only [δ]
    ring
  have hb := polynomialModel_b_invariants W s (fun q => (f q).xc) (fun q => (f q).yc)
  have hb8' := polynomialModel_b8 W s (fun q => (f q).xc) (fun q => (f q).yc)
  have hc := c_invariants F
  have hci := polynomialModel_c_invariants W s (fun q => (f q).xc) (fun q => (f q).yc)
  refine ⟨?_,?_,?_⟩
  · rw [hci.1,hsumT,hc.1]
    change δ ^ 4 + 240 * (δ ^ 4 * τ) = (n : k) ^ 4 * δ ^ 4
    linear_combination δ ^ 4 * hT
  · rw [hci.2,hsumT,hsumW,hc.2,hb2]
    change -δ ^ 6 + 504 * (δ ^ 2 - 12 * x₀) * (δ ^ 4 * τ) +
      6048 * (δ ^ 6 * ω + x₀ * (δ ^ 4 * τ)) = (n : k) ^ 6 * -δ ^ 6
    linear_combination δ ^ 6 * hW
  · simp only [WeierstrassCurve.Δ,hb.1,hb.2.1,hb.2.2,hb8',hsumT,hsumW,hb2,hb4,hb6,hb8]
    change -(δ ^ 2 - 12 * x₀) ^ 2 *
      (3 * x₀ ^ 4 - δ ^ 2 * x₀ ^ 3 - (δ ^ 2 - 12 * x₀) ^ 2 * (δ ^ 4 * τ) +
        5 * (6 * x₀ ^ 2 - δ ^ 2 * x₀) * (δ ^ 4 * τ) -
        7 * (δ ^ 2 - 12 * x₀) * (δ ^ 6 * ω + x₀ * (δ ^ 4 * τ)) - 25 * (δ ^ 4 * τ) ^ 2) -
      8 * (6 * x₀ ^ 2 - δ ^ 2 * x₀ - 10 * (δ ^ 4 * τ)) ^ 3 -
      27 * (δ ^ 2 * x₀ ^ 2 - 4 * x₀ ^ 3 - 4 * (δ ^ 2 - 12 * x₀) * (δ ^ 4 * τ) -
        28 * (δ ^ 6 * ω + x₀ * (δ ^ 4 * τ))) ^ 2 +
      9 * (δ ^ 2 - 12 * x₀) * (6 * x₀ ^ 2 - δ ^ 2 * x₀ - 10 * (δ ^ 4 * τ)) *
        (δ ^ 2 * x₀ ^ 2 - 4 * x₀ ^ 3 - 4 * (δ ^ 2 - 12 * x₀) * (δ ^ 4 * τ) -
          28 * (δ ^ 6 * ω + x₀ * (δ ^ 4 * τ))) = 0
    linear_combination δ ^ 12 * hD

end DkMath.Lib.NumberTheory.WeierstrassNodalVelu
