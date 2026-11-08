/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from P2M/Sol/S_ValuationSubring_exists_mem_inertiaSubgroupIn_pow_eq_of_forall_apply_eq.lean,
commit 115356cbc627159d0d16add0da6e9a2bb3655ed8.
Modified: actual DkMath inertia fixed field and internally supplied prime-power root lifts.
-/

import DkMath.Lib.NumberTheory.AlgebraicResiduePowers
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

#print "file: DkMath.Lib.NumberTheory.InertiaResidueRootLifts"

/-!
# 元の慣性固定体にある根の1で、実際の剰余の p 冪根の1を持ち上げる

還元の単射性と根数上界を使う。持ち上げや慣性固定性を provider にしない。
-/
namespace DkMath.Lib.NumberTheory.InertiaResidue
open ValuationInertia IsLocalRing Finset
noncomputable section
/-- 単元指数の根の1は、同じ剰余を持てば一致する。 -/
theorem eq_of_pow_eq_one_of_sub_mem {R : Type*} [CommRing R] [IsLocalRing R] {m : ℕ} (hm : m ≠ 0)
    (hmu : IsUnit ((m : ℕ) : R)) (x y : R) (hx : x ^ m = 1) (hy : y ^ m = 1)
    (hxy : x - y ∈ IsLocalRing.maximalIdeal R) : x = y := by
  have htel : (∑ i ∈ range m, x ^ i * y ^ (m - 1 - i)) * (x - y) = 0 := by
    rw [geom_sum₂_mul, hx, hy, sub_self]
  have hres : IsLocalRing.residue R x = IsLocalRing.residue R y := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]; exact hxy
  have hyu : IsUnit y := IsUnit.of_pow_eq_one hy hm
  have hS : IsUnit (∑ i ∈ range m, x ^ i * y ^ (m - 1 - i)) := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff]
    have hr : IsLocalRing.residue R (∑ i ∈ range m, x ^ i * y ^ (m - 1 - i)) =
        (m : IsLocalRing.ResidueField R) * IsLocalRing.residue R y ^ (m - 1) := by
      rw [map_sum]; simp only [map_mul, map_pow, hres]; exact geom_sum₂_self _ _
    rw [hr]
    have h1 : IsUnit (m : IsLocalRing.ResidueField R) := by
      simpa using hmu.map (IsLocalRing.residue R)
    exact (h1.mul ((hyu.map (IsLocalRing.residue R)).pow (m - 1))).ne_zero
  exact sub_eq_zero.mp ((hS.mul_right_eq_zero).mp htel)

variable {L : Type*} [Field L]

/-- 非零指数の根の1は、同じ付値環に属する。 -/
theorem root_mem (A : ValuationSubring L) {μ : L} {m : ℕ} (hm : m ≠ 0) (hμ : μ ^ m = 1) : μ ∈ A := by
  have hv : A.valuation μ = 1 := by
    apply pow_left_injective (M := A.ValueGroup) hm
    change A.valuation μ ^ m = 1 ^ m
    rw [← map_pow, hμ, map_one, one_pow]
  exact (A.valuation_le_one_iff μ).mp hv.le

/-- 根の1を実際の付値剰余体へ写す。 -/
def residueRoot (A : ValuationSubring L) {m : ℕ} (hm : m ≠ 0)
    (ζ : L) (hζ : ζ ^ m = 1) : IsLocalRing.ResidueField A :=
  IsLocalRing.residue A ⟨ζ, root_mem A hm hζ⟩

/-- 同じ剰余の値も同じ冪で1となる。 -/
theorem residueRoot_pow (A : ValuationSubring L) {m : ℕ} (hm : m ≠ 0)
    (ζ : L) (hζ : ζ ^ m = 1) : (residueRoot A hm ζ hζ) ^ m = 1 := by
  rw [residueRoot, ← map_pow, ← map_one (IsLocalRing.residue A)]
  congr 1
  exact Subtype.ext (by simpa using hζ)

/-- 単元指数の根の還元は単射。 -/
theorem residueRoot_injective (A : ValuationSubring L) {m : ℕ} (hm : m ≠ 0)
    (hmu : IsUnit ((m : ℕ) : A)) (ζ ξ : L) (hζ : ζ ^ m = 1) (hξ : ξ ^ m = 1)
    (hres : residueRoot A hm ζ hζ = residueRoot A hm ξ hξ) : ζ = ξ := by
  set x : A := ⟨ζ, root_mem A hm hζ⟩
  set y : A := ⟨ξ, root_mem A hm hξ⟩
  have hx : x ^ m = 1 := Subtype.ext (by simpa using hζ)
  have hy : y ^ m = 1 := Subtype.ext (by simpa using hξ)
  have hxy : x - y ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]; exact hres
  exact congrArg Subtype.val (eq_of_pow_eq_one_of_sub_mem hm hmu x y hx hy hxy)

/-- 原始根の還元の単射性と根数上界から、剰余の根の1を持ち上げる。 -/
theorem exists_root_lift (A : ValuationSubring L) {m : ℕ} (hm : m ≠ 0)
    (hmu : IsUnit ((m : ℕ) : A)) (ζ₀ : L) (hζ₀ : IsPrimitiveRoot ζ₀ m)
    (η : IsLocalRing.ResidueField A) (hη : η ^ m = 1) :
    ∃ (ζ : L) (hζ : ζ ^ m = 1), residueRoot A hm ζ hζ = η := by
  classical
  have hm' : 0 < m := Nat.pos_of_ne_zero hm
  set f : Fin m → IsLocalRing.ResidueField A := fun i =>
    residueRoot A hm (ζ₀ ^ (i : ℕ)) (by rw [← pow_mul, mul_comm, pow_mul, hζ₀.pow_eq_one,
      one_pow])
  have hfmem : ∀ i : Fin m, f i ∈ Polynomial.nthRootsFinset m (1 : IsLocalRing.ResidueField A) := by
    intro i
    rw [Polynomial.mem_nthRootsFinset hm']
    exact residueRoot_pow A hm _ _
  have hfinj : Function.Injective f := by
    intro i j hij
    have hpow : ζ₀ ^ (i : ℕ) = ζ₀ ^ (j : ℕ) :=
      residueRoot_injective A hm hmu _ _ _ _ hij
    exact Fin.ext (hζ₀.pow_inj i.2 j.2 hpow)
  have hcard : (Polynomial.nthRootsFinset m (1 : IsLocalRing.ResidueField A)).card ≤ m := by
    classical
    rw [Polynomial.nthRootsFinset_def]
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots m 1)
  have himage : (Finset.univ.image f) = Polynomial.nthRootsFinset m (1 : IsLocalRing.ResidueField A) := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact hfmem i
    · rw [Finset.card_image_of_injective _ hfinj, Finset.card_univ, Fintype.card_fin]
      exact hcard
  have hηmem : η ∈ Polynomial.nthRootsFinset m (1 : IsLocalRing.ResidueField A) :=
    (Polynomial.mem_nthRootsFinset hm' 1).mpr hη
  rw [← himage] at hηmem
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hηmem
  exact ⟨ζ₀ ^ (i : ℕ), _, rfl⟩


/-- 元の同じ絶対慣性群の固定体。 -/
def fixedField (A : ValuationSubring (AlgebraicClosure ℚ)) : IntermediateField ℚ (AlgebraicClosure ℚ) :=
  IntermediateField.fixedField (inertiaSubgroupIn A ℚ)

/-- 全ての剰余 p 冪根の1は、同じ慣性固定体内の実際の根の1へ持ち上がる。 -/
theorem primePower_root_lift {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (i : ℕ) (y : IsLocalRing.ResidueField A) (hy : y ^ (p ^ i) = 1) :
    ∃ ζ : AlgebraicClosure ℚ, ζ ∈ fixedField A ∧ ζ ^ (p ^ i) = 1 ∧
      ∃ hζA : ζ ∈ A, IsLocalRing.residue A ⟨ζ, hζA⟩ = y := by
  have hm : p ^ i ≠ 0 := pow_ne_zero i hp.ne_zero
  have hunitp : IsUnit (p : A) := (A.valuation_eq_one_iff (p : A)).mpr
    (InertiaRadical.valuation_prime_eq_one hp hq hpq A hA)
  have hunitm : IsUnit ((p ^ i : ℕ) : A) := by simpa only [Nat.cast_pow] using hunitp.pow i
  let : NeZero ((p ^ i : ℕ) : AlgebraicClosure ℚ) := ⟨Nat.cast_ne_zero.mpr hm⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) (p ^ i)
  obtain ⟨ζ, hζ, hres⟩ := exists_root_lift A hm hunitm ζ₀ hζ₀ y hy
  refine ⟨ζ, ?_, hζ, root_mem A hm hζ, hres⟩
  rw [fixedField, IntermediateField.mem_fixedField_iff]
  intro τ hτ
  exact InertiaRadical.inertia_fixes_primePower_root hp hq hpq A hA ⟨τ, hτ⟩ i ζ hζ

end
end DkMath.Lib.NumberTheory.InertiaResidue
