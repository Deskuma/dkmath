/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Quadratic residue argument adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_FreyPackage_frey_exists_decomposition_branch_swap_of_a_mod_eight.lean,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
Modified: expose characteristic-two algebra and actual valuation Frobenius separately.
-/

import DkMath.Lib.NumberTheory.ValuationTameCharacter

#print "file: DkMath.Lib.NumberTheory.ValuationQuadraticFrobenius"

/-!
# NOTE-032-003C: 標数2の二次式の根を動かすFrobenius

[DkMath.Lib] z²+z=1なら、標数2ではz²−z=1である。
従って2乗Frobeniusはzを固定せず、もう一方の根へ移す。
この剰余体の等式を付値環へ戻すと、実際のFrobenius元σに対しv(σz−z)=1となる。
慣性による変化量v(τz−z)<1とは異なり、非自明な剰余作用を使う。
-/
namespace DkMath.Lib.NumberTheory.ValuationQuadraticFrobenius
open ValuationFrobenius ValuationTameCharacter.TameCharacter IsLocalRing

/-- [DkMath.Lib] 標数2の二次式の根は、2乗作用との差が正確に1となる。 -/
theorem square_sub_eq_one {k : Type*} [Field k] [CharP k 2] {z : k}
    (hz : z ^ 2 + z = 1) : z ^ 2 - z = 1 := by
  have h2 : (2 : k) = 0 := CharP.cast_eq_zero k 2
  linear_combination hz - z * h2

/-- [DkMath.Lib] 同じ根は2乗Frobeniusに固定されない。根の存在は別の入力である。 -/
theorem square_ne_self {k : Type*} [Field k] [CharP k 2] {z : k}
    (hz : z ^ 2 + z = 1) : z ^ 2 ≠ z := by
  intro he
  have h := square_sub_eq_one hz
  rw [he, sub_self] at h
  exact zero_ne_one h

/-- [DkMath.Lib] 二次式の根へ還元する整元のFrobenius変化量は単元となる。
指定した同じ付値環の実際のFrobenius所属を使用し、剰余体の標数2を明示する。 -/
theorem valuation_apply_sub_eq_one {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) [CharP (ResidueField A) 2]
    {σ : L ≃ₐ[K] L} (hσ : IsFrobeniusAt A σ 2) {z : L} (hz : z ∈ A)
    (hquad : residue A (⟨z, hz⟩ : A) ^ 2 + residue A (⟨z, hz⟩ : A) = 1) :
    A.valuation (σ z - z) = 1 := by
  have hσz : σ z ∈ A := (apply_mem_iff hσ.mem_decompositionSubgroup z).mpr hz
  have he : residue A (⟨σ z, hσz⟩ : A) = residue A (⟨z, hz⟩ : A) ^ 2 := by
    simpa only [rq_of_mem hz, rq_of_mem hσz] using rq_apply_eq_pow_of_isFrobeniusAt hσ hz
  let d : A := ⟨σ z - z, sub_mem hσz hz⟩
  have hd : residue A d = 1 := by
    change residue A ((⟨σ z, hσz⟩ : A) - ⟨z, hz⟩) = 1
    rw [map_sub, he]
    exact square_sub_eq_one hquad
  have hunit : IsUnit d := (residue_ne_zero_iff_isUnit d).mp (by rw [hd]; exact one_ne_zero)
  exact (A.valuation_eq_one_iff _).mp hunit

end DkMath.Lib.NumberTheory.ValuationQuadraticFrobenius
