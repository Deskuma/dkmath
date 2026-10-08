/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.Int.GCD

#print "file: DkMath.Lib.Algebra.PowerSubgroup"

/-!+# Coprime power subgroups and the quotient Chinese remainder theorem

For an arbitrary commutative group, coprime power subgroups generate the whole
group and intersect in the product-exponent power subgroup. The resulting CRT
is a multiplicative equivalence of quotient groups, including exponents zero
and one. No finiteness, torsion-freeness, or power-surjectivity hypothesis is used.
-/

namespace DkMath.Lib.Algebra

variable (G : Type*) [CommGroup G]

/-- The subgroup of `n`th powers in a commutative group. -/
def powerSubgroup (n : ℕ) : Subgroup G :=
  (powMonoidHom n : G →* G).range

variable {G}

@[simp]
theorem mem_powerSubgroup {n : ℕ} {x : G} :
    x ∈ powerSubgroup G n ↔ ∃ a : G, a ^ n = x := Iff.rfl

@[simp]
theorem powerSubgroup_zero : powerSubgroup G 0 = ⊥ := by
  ext x
  simp [eq_comm]

@[simp]
theorem powerSubgroup_one : powerSubgroup G 1 = ⊤ := by
  ext x
  simp

/-- The explicit multiplicative form of integer Bézout coefficients. -/
theorem coprime_pow_bezout {n m : ℕ} (h : n.Coprime m) (x : G) :
    (x ^ Nat.gcdA n m) ^ n * (x ^ Nat.gcdB n m) ^ m = x := by
  have hab : (n : ℤ) * Nat.gcdA n m + (m : ℤ) * Nat.gcdB n m = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, h.gcd_eq_one]
    rfl
  rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul,
    mul_comm (Nat.gcdA n m), mul_comm (Nat.gcdB n m), ← zpow_add, hab, zpow_one]

/-- Any element is a product of an `n`th power and an `m`th power. -/
theorem exists_mul_pow_of_coprime {n m : ℕ} (h : n.Coprime m) (x : G) :
    ∃ a b : G, a ^ n * b ^ m = x :=
  ⟨x ^ Nat.gcdA n m, x ^ Nat.gcdB n m, coprime_pow_bezout h x⟩

/-- Coprime power subgroups generate the whole group. -/
theorem powerSubgroup_sup_eq_top_of_coprime {n m : ℕ} (h : n.Coprime m) :
    powerSubgroup G n ⊔ powerSubgroup G m = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨a, b, hab⟩ := exists_mul_pow_of_coprime h x
  exact Subgroup.mem_sup.mpr ⟨a ^ n, ⟨a, rfl⟩, b ^ m, ⟨b, rfl⟩, hab⟩

/-- A product-exponent power is simultaneously a power for each exponent. -/
theorem powerSubgroup_mul_le_inf (n m : ℕ) :
    powerSubgroup G (n * m) ≤ powerSubgroup G n ⊓ powerSubgroup G m := by
  rintro x ⟨a, rfl⟩
  exact ⟨⟨a ^ m, by change (a ^ m) ^ n = a ^ (n * m); rw [← pow_mul, Nat.mul_comm]⟩,
    ⟨a ^ n, by change (a ^ n) ^ m = a ^ (n * m); rw [← pow_mul]⟩⟩

/-- For coprime exponents, simultaneous powers are exactly product-exponent powers. -/
theorem powerSubgroup_inf_eq_mul_of_coprime {n m : ℕ} (h : n.Coprime m) :
    powerSubgroup G n ⊓ powerSubgroup G m = powerSubgroup G (n * m) := by
  apply le_antisymm _ (powerSubgroup_mul_le_inf n m)
  rintro x ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  change a ^ n = x at ha
  change b ^ m = x at hb
  refine ⟨a ^ Nat.gcdB n m * b ^ Nat.gcdA n m, ?_⟩
  have hab : (n : ℤ) * Nat.gcdA n m + (m : ℤ) * Nat.gcdB n m = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, h.gcd_eq_one]
    rfl
  calc
    (a ^ Nat.gcdB n m * b ^ Nat.gcdA n m) ^ (n * m) =
        (a ^ n) ^ ((m : ℤ) * Nat.gcdB n m) *
          (b ^ m) ^ ((n : ℤ) * Nat.gcdA n m) := by
      rw [mul_pow]
      simp only [← zpow_natCast, ← zpow_mul, Int.natCast_mul]
      congr 1 <;> congr 1 <;> ac_rfl
    _ = x ^ ((m : ℤ) * Nat.gcdB n m) * x ^ ((n : ℤ) * Nat.gcdA n m) := by
      rw [ha, hb]
    _ = x := by rw [← zpow_add, add_comm, hab, zpow_one]

/-- The canonical map to the two power quotients. -/
def powerQuotientPair (n m : ℕ) :
    G →* (G ⧸ powerSubgroup G n) × (G ⧸ powerSubgroup G m) :=
  (QuotientGroup.mk' (powerSubgroup G n)).prod
    (QuotientGroup.mk' (powerSubgroup G m))

@[simp]
theorem powerQuotientPair_apply (n m : ℕ) (x : G) :
    powerQuotientPair n m x =
      ((x : G ⧸ powerSubgroup G n), (x : G ⧸ powerSubgroup G m)) := rfl

/-- The kernel of the canonical quotient pair is the intersection. -/
theorem powerQuotientPair_ker (n m : ℕ) :
    (powerQuotientPair (G := G) n m).ker = powerSubgroup G n ⊓ powerSubgroup G m := by
  ext x
  simp [MonoidHom.mem_ker, Prod.ext_iff, QuotientGroup.eq_one_iff]

/-- Coprime exponents make the canonical quotient pair surjective. -/
theorem powerQuotientPair_surjective {n m : ℕ} (h : n.Coprime m) :
    Function.Surjective (powerQuotientPair (G := G) n m) := by
  rintro ⟨qa, qb⟩
  induction qa using Quotient.inductionOn with
  | h a =>
    induction qb using Quotient.inductionOn with
    | h b =>
      have hab : a⁻¹ * b ∈ powerSubgroup G n ⊔ powerSubgroup G m := by
        rw [powerSubgroup_sup_eq_top_of_coprime h]
        trivial
      obtain ⟨s, hs, t, ht, hst⟩ := Subgroup.mem_sup.mp hab
      refine ⟨a * s, Prod.ext ?_ ?_⟩
      · change (↑(a * s) : G ⧸ powerSubgroup G n) = ↑a
        rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff s).mpr hs, mul_one]
      · change (↑(a * s) : G ⧸ powerSubgroup G m) = ↑b
        apply QuotientGroup.eq.mpr
        have hb : b = a * (s * t) := by rw [hst]; simp
        rw [hb]
        simpa [mul_assoc] using ht

/-- CRT for quotient groups by coprime power images. -/
noncomputable def powerQuotientCRT {n m : ℕ} (h : n.Coprime m) :
    G ⧸ powerSubgroup G (n * m) ≃*
      (G ⧸ powerSubgroup G n) × (G ⧸ powerSubgroup G m) :=
  QuotientGroup.liftEquiv (powerSubgroup G (n * m))
    (powerQuotientPair_surjective h)
    ((powerSubgroup_inf_eq_mul_of_coprime h).symm.trans (powerQuotientPair_ker n m).symm)

@[simp]
theorem powerQuotientCRT_apply_mk {n m : ℕ} (h : n.Coprime m) (x : G) :
    powerQuotientCRT h (x : G ⧸ powerSubgroup G (n * m)) =
      ((x : G ⧸ powerSubgroup G n), (x : G ⧸ powerSubgroup G m)) := rfl

/-- Adjacent power subgroups generate the group, including `n = 0`. -/
theorem powerSubgroup_sup_successor (n : ℕ) :
    powerSubgroup G n ⊔ powerSubgroup G (n + 1) = ⊤ :=
  powerSubgroup_sup_eq_top_of_coprime (by simp [Nat.Coprime, Nat.add_comm n 1])

/-- Adjacent power subgroups intersect in the product-exponent subgroup. -/
theorem powerSubgroup_inf_successor (n : ℕ) :
    powerSubgroup G n ⊓ powerSubgroup G (n + 1) = powerSubgroup G (n * (n + 1)) :=
  powerSubgroup_inf_eq_mul_of_coprime (by simp [Nat.Coprime, Nat.add_comm n 1])

/-- Every group element is a product of powers at adjacent exponents. -/
theorem exists_mul_pow_successor (n : ℕ) (x : G) :
    ∃ a b : G, a ^ n * b ^ (n + 1) = x :=
  exists_mul_pow_of_coprime (by simp [Nat.Coprime, Nat.add_comm n 1]) x

/-- CRT for adjacent exponents, without a positivity assumption. -/
noncomputable def powerQuotientSuccessorCRT (n : ℕ) :
    G ⧸ powerSubgroup G (n * (n + 1)) ≃*
      (G ⧸ powerSubgroup G n) × (G ⧸ powerSubgroup G (n + 1)) :=
  powerQuotientCRT (by simp [Nat.Coprime, Nat.add_comm n 1])

@[simp]
theorem powerQuotientSuccessorCRT_apply_mk (n : ℕ) (x : G) :
    powerQuotientSuccessorCRT n (x : G ⧸ powerSubgroup G (n * (n + 1))) =
      ((x : G ⧸ powerSubgroup G n), (x : G ⧸ powerSubgroup G (n + 1))) := rfl

section Units

variable (R : Type*) [CommMonoid R]

/-- The `n`th-power subgroup of the unit group of a commutative monoid. -/
abbrev unitPowerSubgroup (n : ℕ) : Subgroup Rˣ := powerSubgroup Rˣ n

/-- Adjacent unit-power subgroups generate the unit group. -/
theorem unitPowerSubgroup_sup_successor (n : ℕ) :
    unitPowerSubgroup R n ⊔ unitPowerSubgroup R (n + 1) = ⊤ :=
  powerSubgroup_sup_successor n

/-- Adjacent unit-power subgroups intersect in the product-exponent subgroup. -/
theorem unitPowerSubgroup_inf_successor (n : ℕ) :
    unitPowerSubgroup R n ⊓ unitPowerSubgroup R (n + 1) =
      unitPowerSubgroup R (n * (n + 1)) :=
  powerSubgroup_inf_successor n

/-- Quotient CRT for adjacent unit powers, valid for every commutative monoid. -/
noncomputable def unitPowerQuotientSuccessorCRT (n : ℕ) :
    Rˣ ⧸ unitPowerSubgroup R (n * (n + 1)) ≃*
      (Rˣ ⧸ unitPowerSubgroup R n) × (Rˣ ⧸ unitPowerSubgroup R (n + 1)) :=
  powerQuotientSuccessorCRT n

@[simp]
theorem unitPowerQuotientSuccessorCRT_apply_mk (n : ℕ) (x : Rˣ) :
    unitPowerQuotientSuccessorCRT R n (x : Rˣ ⧸ unitPowerSubgroup R (n * (n + 1))) =
      ((x : Rˣ ⧸ unitPowerSubgroup R n), (x : Rˣ ⧸ unitPowerSubgroup R (n + 1))) := rfl

end Units

end DkMath.Lib.Algebra
