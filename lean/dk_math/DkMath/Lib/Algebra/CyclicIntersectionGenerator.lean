/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.FiniteSubgroupIntersection
import Mathlib.GroupTheory.SpecificGroups.Cyclic

#print "file: DkMath.Lib.Algebra.CyclicIntersectionGenerator"

/-!
# 同じ巡回群の交叉生成元と商生成元の厳密位数

同じ ZMod 座標の1を生成元とし、濃度指数を実際の倍点へ戻す。
-/
namespace DkMath.Lib.Algebra.CyclicIntersectionGenerator
variable {G : Type*} [AddCommGroup G] {p m : ℕ} [Fact p.Prime]
    (K H : AddSubgroup G) (e : ZMod (p ^ m) ≃+ K)

/-- 実際の座標生成元は元の同じ K 全体を生成する。 -/
theorem zmultiples_generator : AddSubgroup.zmultiples (e 1).val = K := by
  apply le_antisymm (AddSubgroup.zmultiples_le.mpr (e 1).property)
  intro x hx
  let z : K := ⟨x, hx⟩
  have he : (e.symm z).val • e 1 = z := by
    rw [← map_nsmul]
    simp only [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val, AddEquiv.apply_symm_apply]
  refine ⟨((e.symm z).val : ℤ), ?_⟩
  have hv := congrArg K.subtype he
  rw [map_nsmul] at hv
  change (e.symm z).val • (e 1).val = x at hv
  simpa only [natCast_zsmul] using hv

/-- 同じ局所商生成元の位数は、元の K の実際の商像濃度。 -/
theorem quotient_generator_order :
    addOrderOf ((QuotientAddGroup.mk' H) (e 1).val) = Nat.card (K.map (QuotientAddGroup.mk' H)) := by
  have hs := congrArg (fun J : AddSubgroup G => J.map (QuotientAddGroup.mk' H)) (zmultiples_generator K e)
  rw [AddMonoidHom.map_zmultiples] at hs
  have hc := congrArg (fun J : AddSubgroup (G ⧸ H) => Nat.card J) hs
  rwa [Nat.card_zmultiples] at hc

/-- 交叉の濃度 p^r が既知なら、商生成元の位数は正確に p^(m-r)。 -/
theorem quotient_generator_order_prime_power (hK : Nat.card K = p ^ m)
    {r : ℕ} (hr : r ≤ m) (hI : Nat.card ↥(K ⊓ H) = p ^ r) :
    addOrderOf ((QuotientAddGroup.mk' H) (e 1).val) = p ^ (m - r) := by
  rw [quotient_generator_order K H e]
  apply mul_left_cancel₀ (pow_ne_zero r (Fact.out : p.Prime).ne_zero)
  rw [← hI, ← FiniteSubgroupIntersection.card_intersection_mul_image, hK, hI,
    ← pow_add, Nat.add_sub_of_le hr]

/-- 元の同じ交叉は、座標生成元の p^(m-r) 倍が生成する部分群そのもの。 -/
theorem intersection_eq_zmultiples (hK : Nat.card K = p ^ m)
    {r : ℕ} (hr : r ≤ m) (hI : Nat.card ↥(K ⊓ H) = p ^ r) :
    K ⊓ H = AddSubgroup.zmultiples (p ^ (m - r) • (e 1).val) := by
  have hqo := quotient_generator_order_prime_power K H e hK hr hI
  have hz : p ^ (m - r) • (QuotientAddGroup.mk' H) (e 1).val = 0 := by
    rw [← hqo]
    exact addOrderOf_nsmul_eq_zero _
  have hmem : p ^ (m - r) • (e 1).val ∈ H := by
    apply (QuotientAddGroup.eq_zero_iff _).mp
    change (QuotientAddGroup.mk' H) (p ^ (m - r) • (e 1).val) = 0
    rwa [map_nsmul]
  have hle : AddSubgroup.zmultiples (p ^ (m - r) • (e 1).val) ≤ K ⊓ H :=
    AddSubgroup.zmultiples_le.mpr ⟨K.nsmul_mem (e 1).property _, hmem⟩
  have hgo : addOrderOf (e 1).val = p ^ m := by
    rw [← Nat.card_zmultiples, zmultiples_generator K e, hK]
  have hd : p ^ (m - r) ∣ addOrderOf (e 1).val := by
    rw [hgo]
    exact pow_dvd_pow p (by omega)
  have hcard : Nat.card (AddSubgroup.zmultiples (p ^ (m - r) • (e 1).val)) = p ^ r := by
    rw [Nat.card_zmultiples, addOrderOf_nsmul_of_dvd
      (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) hd,
      hgo, Nat.pow_div (by omega) (Fact.out : p.Prime).pos]
    congr 1
    omega
  let : Finite K := Nat.finite_of_card_ne_zero (hK ▸ pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  let : Finite ↥(K ⊓ H) := Finite.of_injective
    (AddSubgroup.inclusion (show K ⊓ H ≤ K from inf_le_left)) (AddSubgroup.inclusion_injective _)
  exact (AddSubgroup.eq_of_le_of_card_ge hle (by rw [hI, hcard])).symm

end DkMath.Lib.Algebra.CyclicIntersectionGenerator
