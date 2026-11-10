/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.ValuationFrobenius

#print "file: DkMath.Lib.NumberTheory.FrobeniusInertiaCoset"

/-! # 同じ剰余 Frobenius を持つ二つの持ち上げの差は、元の慣性に入る -/
namespace DkMath.Lib.NumberTheory.ValuationFrobenius
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) {q : ℕ}

/-- 同じ全剰余体上の Frobenius 作用を持つ元は、同じ剰余自己同型を与える。 -/
theorem residue_action_eq_of_frobenius (φ ψ : A.decompositionSubgroup K)
    (hφ : IsFrobeniusAt A φ.val q) (hψ : IsFrobeniusAt A ψ.val q) :
    MulSemiringAction.toRingAut (A.decompositionSubgroup K) (IsLocalRing.ResidueField A) φ =
      MulSemiringAction.toRingAut (A.decompositionSubgroup K) (IsLocalRing.ResidueField A) ψ := by
  apply RingEquiv.ext
  intro x
  exact (hφ.smul_residue_eq x).trans (hψ.smul_residue_eq x).symm

/-- 二つの実際の Frobenius 持ち上げの商は、元の分解群内の慣性に属する。 -/
theorem frobenius_div_mem_inertia (φ ψ : A.decompositionSubgroup K)
    (hφ : IsFrobeniusAt A φ.val q) (hψ : IsFrobeniusAt A ψ.val q) :
    φ / ψ ∈ A.inertiaSubgroup K := by
  change MulSemiringAction.toRingAut (A.decompositionSubgroup K) (IsLocalRing.ResidueField A) (φ / ψ) = 1
  rw [map_div, residue_action_eq_of_frobenius A φ ψ hφ hψ, div_self']
end DkMath.Lib.NumberTheory.ValuationFrobenius
