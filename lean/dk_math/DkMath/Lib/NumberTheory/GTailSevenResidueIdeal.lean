/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.GTailSevenEisensteinResidue
import Mathlib.RingTheory.Ideal.Maps

#print "file: DkMath.Lib.NumberTheory.GTailSevenResidueIdeal"

/-!
# Root-guarded residue homomorphisms and kernel ideals

The kernels record oriented residue membership in the existing integral ring.
No principal ideal product, cyclotomic transfer or descent is asserted.
-/

namespace DkMath.Lib.NumberTheory

open DkMath.NumberTheory.TraceOneQuadratic

/-- Package the previously checked evaluation laws at a supplied quadratic root. -/
def eisensteinResidueRingHom {q : ℕ} (t : ZMod q) (ht : t ^ 2 - t + 1 = 0) :
    TraceOneInt (-1) →+* ZMod q where
  toFun := eisensteinResidueEval t
  map_one' := by simp [eisensteinResidueEval]
  map_zero' := by simp [eisensteinResidueEval]
  map_add' := eisensteinResidueEval_add t
  map_mul' := eisensteinResidueEval_mul t ht

/-- Bundling preserves exactly the Step 013 evaluation function. -/
theorem eisensteinResidueRingHom_apply {q : ℕ} (t : ZMod q)
    (ht : t ^ 2 - t + 1 = 0) (z : TraceOneInt (-1)) :
    eisensteinResidueRingHom t ht z = eisensteinResidueEval t z := rfl

/-- Embedded integers map to their residue casts. -/
theorem eisensteinResidueRingHom_ofInt {q : ℕ} (t : ZMod q)
    (ht : t ^ 2 - t + 1 = 0) (n : ℤ) :
    eisensteinResidueRingHom t ht (ofInt (-1) n) = (n : ZMod q) := by
  simp [eisensteinResidueRingHom, eisensteinResidueEval, ofInt]

/-- The integral generator maps to the chosen root. -/
theorem eisensteinResidueRingHom_tau {q : ℕ} (t : ZMod q)
    (ht : t ^ 2 - t + 1 = 0) :
    eisensteinResidueRingHom t ht (tau (-1)) = t := by
  simp [eisensteinResidueRingHom, eisensteinResidueEval, tau]

/-- The conjugate parameter satisfies the same supplied root relation. -/
theorem eisensteinResidue_conjugate_root {q : ℕ} (t : ZMod q)
    (ht : t ^ 2 - t + 1 = 0) : (1 - t) ^ 2 - (1 - t) + 1 = 0 := by
  linear_combination ht

/-- Conjugation switches the two bundled evaluations. -/
theorem eisensteinResidueRingHom_conj {q : ℕ} (t : ZMod q)
    (ht : t ^ 2 - t + 1 = 0) (z : TraceOneInt (-1)) :
    eisensteinResidueRingHom t ht (conj z) =
      eisensteinResidueRingHom (1 - t) (eisensteinResidue_conjugate_root t ht) z :=
  eisensteinResidueEval_conj t z

/-- An actual ideal in the existing integral TraceOne ring. -/
def eisensteinResidueIdeal {q : ℕ} (t : ZMod q) (ht : t ^ 2 - t + 1 = 0) :
    Ideal (TraceOneInt (-1)) := RingHom.ker (eisensteinResidueRingHom t ht)

/-- Kernel membership is precisely zero evaluation at the chosen root. -/
theorem mem_eisensteinResidueIdeal_iff {q : ℕ} (t : ZMod q)
    (ht : t ^ 2 - t + 1 = 0) (z : TraceOneInt (-1)) :
    z ∈ eisensteinResidueIdeal t ht ↔ eisensteinResidueEval t z = 0 :=
  RingHom.mem_ker

/-- The existing element-conjugation equality gives the normalized residue norm product. -/
theorem norm_cast_eq_eisensteinResidue_product {q : ℕ} (t : ZMod q)
    (ht : t ^ 2 - t + 1 = 0) (z : TraceOneInt (-1)) :
    (norm z : ZMod q) = eisensteinResidueEval t z * eisensteinResidueEval (1 - t) z := by
  have h := congrArg (eisensteinResidueRingHom t ht) (traceOne_mul_conj z)
  rw [map_mul, eisensteinResidueRingHom_ofInt] at h
  simpa only [eisensteinResidueRingHom_apply, eisensteinResidueEval_conj] using h.symm

/-- At a prime with a supplied root, norm divisibility means membership in one kernel. -/
theorem prime_dvd_norm_iff_mem_eisensteinResidueIdeals {q : ℕ}
    (hq : Nat.Prime q) (t : ZMod q) (ht : t ^ 2 - t + 1 = 0)
    (z : TraceOneInt (-1)) :
    (q : ℤ) ∣ norm z ↔ z ∈ eisensteinResidueIdeal t ht ∨
      z ∈ eisensteinResidueIdeal (1 - t) (eisensteinResidue_conjugate_root t ht) := by
  let : Fact (Nat.Prime q) := ⟨hq⟩
  rw [← CharP.intCast_eq_zero_iff (ZMod q) q (norm z),
    norm_cast_eq_eisensteinResidue_product t ht,
    mem_eisensteinResidueIdeal_iff, mem_eisensteinResidueIdeal_iff]
  exact mul_eq_zero

/-- The scalar modulus lies in every supplied-root kernel. -/
theorem scalar_mem_eisensteinResidueIdeal {q : ℕ} (t : ZMod q)
    (ht : t ^ 2 - t + 1 = 0) : ofInt (-1) (q : ℤ) ∈ eisensteinResidueIdeal t ht := by
  change eisensteinResidueRingHom t ht (ofInt (-1) (q : ℤ)) = 0
  rw [eisensteinResidueRingHom_ofInt]
  simp

/-- Every residue is attained by an embedded integral representative. -/
theorem eisensteinResidueRingHom_surjective {q : ℕ} (t : ZMod q)
    (ht : t ^ 2 - t + 1 = 0) : Function.Surjective (eisensteinResidueRingHom t ht) := by
  intro x
  obtain ⟨n, hn⟩ := ZMod.intCast_surjective x
  exact ⟨ofInt (-1) n, (eisensteinResidueRingHom_ofInt t ht n).trans hn⟩

/-- Optional maximality gate: the proved surjection has prime-field codomain. -/
theorem eisensteinResidueIdeal_isMaximal {q : ℕ} (hq : Nat.Prime q)
    (t : ZMod q) (ht : t ^ 2 - t + 1 = 0) : (eisensteinResidueIdeal t ht).IsMaximal := by
  let : Fact (Nat.Prime q) := ⟨hq⟩
  exact RingHom.ker_isMaximal_of_surjective (eisensteinResidueRingHom t ht)
    (eisensteinResidueRingHom_surjective t ht)

/-- The canonical first slot contains the selected integral coordinate. -/
theorem gtailSevenNormCoord_mem_residueIdeal {q a b : ℕ} [Fact (Nat.Prime q)]
    (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hb : ¬ q ∣ b) :
    gtailSevenNormCoord a b ∈ eisensteinResidueIdeal (gtailSevenResidueRoot q a b)
      (gtailSevenResidueRoot_polynomial hQ hb) := by
  rw [mem_eisensteinResidueIdeal_iff]
  exact eisensteinResidueEval_gtailSevenNormCoord_zero hb

/-- Away from three, the same coordinate is excluded from the conjugate ideal. -/
theorem gtailSevenNormCoord_not_mem_conjugate_residueIdeal {q a b : ℕ}
    [Fact (Nat.Prime q)] (hq3 : q ≠ 3)
    (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hb : ¬ q ∣ b) :
    gtailSevenNormCoord a b ∉ eisensteinResidueIdeal (1 - gtailSevenResidueRoot q a b)
      (gtailSevenResidueRoot_conjugate_polynomial hQ hb) := by
  rw [mem_eisensteinResidueIdeal_iff]
  exact eisensteinResidueEval_gtailSevenNormCoord_conjugate_ne_zero hq3 hQ hb

/-- A witnessed difference of memberships proves the oriented kernels differ. -/
theorem gtailSevenResidueIdeals_ne_conjugate {q a b : ℕ} [Fact (Nat.Prime q)]
    (hq3 : q ≠ 3) (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hb : ¬ q ∣ b) :
    eisensteinResidueIdeal (gtailSevenResidueRoot q a b)
        (gtailSevenResidueRoot_polynomial hQ hb) ≠
      eisensteinResidueIdeal (1 - gtailSevenResidueRoot q a b)
        (gtailSevenResidueRoot_conjugate_polynomial hQ hb) := by
  intro heq
  have hm := gtailSevenNormCoord_mem_residueIdeal hQ hb
  rw [heq] at hm
  exact gtailSevenNormCoord_not_mem_conjugate_residueIdeal hq3 hQ hb hm

end DkMath.Lib.NumberTheory
