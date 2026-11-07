/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.Nat.Prime.Basic

#print "file: DkMath.Lib.Algebra.FiniteSubgroupIntersection"

/-!
# 同じ部分群の交叉と実際の商像の濃度

交叉・商像を元の群の中で保持する。素数冪の濃度を持つ場合は、
二つの濃度を相補的な指数に分解する。商を局所成分群と同定する算術は含まない。
-/
namespace DkMath.Lib.Algebra.FiniteSubgroupIntersection
variable {G : Type*} [AddCommGroup G] (K H : AddSubgroup G)

/-- 同じ K の H による商像への写像の核は、元の同じ交叉である。 -/
def intersectionKerEquiv :
    ↥(K ⊓ H) ≃+ ((QuotientAddGroup.mk' H).comp K.subtype).ker where
  toFun x := ⟨⟨x.val, x.property.1⟩, (QuotientAddGroup.eq_zero_iff x.val).mpr x.property.2⟩
  invFun x := ⟨x.val.val, ⟨x.val.property, (QuotientAddGroup.eq_zero_iff x.val.val).mp x.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- 第一同型定理による実際の濃度積。 -/
theorem card_intersection_mul_image :
    Nat.card K = Nat.card ↥(K ⊓ H) * Nat.card (K.map (QuotientAddGroup.mk' H)) := by
  let f := (QuotientAddGroup.mk' H).comp K.subtype
  have hr : f.range = K.map (QuotientAddGroup.mk' H) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  calc
    Nat.card K = Nat.card (K ⧸ f.ker) * Nat.card f.ker :=
      f.ker.card_eq_card_quotient_mul_card_addSubgroup
    _ = Nat.card f.range * Nat.card ↥(K ⊓ H) := by
      rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv,
        ← Nat.card_congr (intersectionKerEquiv K H).toEquiv]
    _ = _ := by rw [hr, Nat.mul_comm]

/-- 濃度 p^m の部分群の交叉と商像は p^r と p^(m-r) に正確に分かれる。 -/
theorem prime_power_profile {p m : ℕ} (hp : p.Prime) (hcard : Nat.card K = p ^ m) :
    ∃ r ≤ m, Nat.card ↥(K ⊓ H) = p ^ r ∧
      Nat.card (K.map (QuotientAddGroup.mk' H)) = p ^ (m - r) := by
  have hd : Nat.card ↥(K ⊓ H) ∣ p ^ m := by
    rw [← hcard]
    exact AddSubgroup.card_dvd_of_le inf_le_left
  obtain ⟨r, hr, he⟩ := (Nat.dvd_prime_pow hp).mp hd
  refine ⟨r, hr, he, ?_⟩
  have hc := card_intersection_mul_image K H
  rw [hcard, he] at hc
  apply mul_left_cancel₀ (pow_ne_zero r hp.ne_zero)
  calc
    p ^ r * Nat.card (K.map (QuotientAddGroup.mk' H)) = p ^ m := hc.symm
    _ = p ^ r * p ^ (m - r) := by rw [← pow_add, Nat.add_sub_of_le hr]

end DkMath.Lib.Algebra.FiniteSubgroupIntersection
