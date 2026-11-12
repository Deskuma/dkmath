/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from P2M/Sol/S_ValuationSubring_exists_mem_inertiaSubgroupIn_pow_eq_of_forall_apply_eq.lean,
commit 115356cbc627159d0d16add0da6e9a2bb3655ed8.
Modified: actual named radical overfield and internally constructed unit-root approximation inputs.
-/

import DkMath.Lib.NumberTheory.InertiaResidueUnitRoots

#print "file: DkMath.Lib.NumberTheory.InertiaRadicalTailField"

/-!
# 同じ慣性固定体と全 q 根を含む実際の tail 体

同じ互換根の塔と、単元の p 乗根近似を内部構成する。近似を正確な体内冪根へ変える
単根持ち上げや、慣性の tail の p 可除性そのものは、まだ結論しない。
-/
namespace DkMath.Lib.NumberTheory.InertiaResidue
open ValuationInertia
noncomputable section

/-- 同じ有理数 q の全 p 冪根の集合。 -/
def radicals (p q : ℕ) : Set (AlgebraicClosure ℚ) := {z | ∃ n : ℕ, z ^ (p ^ n) = (q : AlgebraicClosure ℚ)}

/-- 元の慣性固定体と全 p 冪根を添加した、実際の中間体。 -/
def tailField (A : ValuationSubring (AlgebraicClosure ℚ)) (p q : ℕ) : IntermediateField ℚ (AlgebraicClosure ℚ) :=
  IntermediateField.adjoin ℚ ((fixedField A : Set (AlgebraicClosure ℚ)) ∪ radicals p q)

/-- 元の同じ慣性固定体は、同じ tail 体に含まれる。 -/
theorem fixedField_le_tailField (A : ValuationSubring (AlgebraicClosure ℚ)) (p q : ℕ) :
    fixedField A ≤ tailField A p q := fun _ hz => IntermediateField.subset_adjoin ℚ _ (Or.inl hz)

/-- q の任意の同じ p 冪根は、構成した tail 体に入る。 -/
theorem radical_mem_tailField (A : ValuationSubring (AlgebraicClosure ℚ)) {p q n : ℕ}
    {z : AlgebraicClosure ℚ} (hz : z ^ (p ^ n) = (q : AlgebraicClosure ℚ)) : z ∈ tailField A p q :=
  IntermediateField.subset_adjoin ℚ _ (Or.inr ⟨n, hz⟩)

/-- 以前の同じ互換根の塔を、同じ tail 体内へ戻す。 -/
theorem tower_mem_tailField (A : ValuationSubring (AlgebraicClosure ℚ)) {p q : ℕ}
    (hp : p.Prime) (n : ℕ) : InertiaRadical.radical p q hp n ∈ tailField A p q :=
  radical_mem_tailField A (PrimeRadicalTower.tower_pow p hp.pos (q : AlgebraicClosure ℚ) n)

/-- tail 体内に、元の同じ互換根の全段を持つ実際の塔が存在する。 -/
theorem compatible_roots_in_tailField (A : ValuationSubring (AlgebraicClosure ℚ)) {p q : ℕ} (hp : p.Prime) :
    ∃ α : ℕ → tailField A p q, α 0 = (q : tailField A p q) ∧
      (∀ n d, α (n + d) ^ (p ^ d) = α n) ∧ ∀ n, α n ^ (p ^ n) = (q : tailField A p q) := by
  let α : ℕ → tailField A p q := fun n => ⟨InertiaRadical.radical p q hp n, tower_mem_tailField A hp n⟩
  exact ⟨α, rfl, fun n d => Subtype.ext (PrimeRadicalTower.tower_compat p hp.pos (q : AlgebraicClosure ℚ) n d),
    fun n => Subtype.ext (PrimeRadicalTower.tower_pow p hp.pos (q : AlgebraicClosure ℚ) n)⟩

/-- 剰余の p 冪根の1は、同じ tail 体内の実際の根の1へ持ち上がる。 -/
theorem tailField_primePower_root_lifts {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (i : ℕ) (y : IsLocalRing.ResidueField A) (hy : y ^ (p ^ i) = 1) :
    ∃ ζ : tailField A p q, ζ ^ (p ^ i) = 1 ∧
      ∃ hζA : (ζ : AlgebraicClosure ℚ) ∈ A, IsLocalRing.residue A ⟨(ζ : AlgebraicClosure ℚ), hζA⟩ = y := by
  obtain ⟨ζ, hζK, hζ, hζA, hres⟩ := primePower_root_lift hp hq hpq A hA i y hy
  exact ⟨⟨ζ, fixedField_le_tailField A p q hζK⟩, Subtype.ext hζ, hζA, hres⟩

/-- 同じ tail 体の単元に、実際の単元 p 乗根近似を供給する。 -/
theorem tailField_unit_roots {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (u : A.comap (algebraMap (tailField A p q) (AlgebraicClosure ℚ))) (hu : IsUnit u) :
    ∃ z : A.comap (algebraMap (tailField A p q) (AlgebraicClosure ℚ)), IsUnit z ∧
      z ^ p - u ∈ IsLocalRing.maximalIdeal (A.comap (algebraMap (tailField A p q) (AlgebraicClosure ℚ))) :=
  approximate_unit_pRoot_isUnit hp hq hpq A hA (tailField A p q) (fixedField_le_tailField A p q) u hu

/-- 同じ tail 体を含む任意の実際の中間体でも、同じ単元近似入力を内部供給する。 -/
theorem tailOverfield_unit_roots {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (E : IntermediateField ℚ (AlgebraicClosure ℚ)) (hE : tailField A p q ≤ E)
    (u : A.comap (algebraMap E (AlgebraicClosure ℚ))) (hu : IsUnit u) :
    ∃ z : A.comap (algebraMap E (AlgebraicClosure ℚ)), IsUnit z ∧
      z ^ p - u ∈ IsLocalRing.maximalIdeal (A.comap (algebraMap E (AlgebraicClosure ℚ))) :=
  approximate_unit_pRoot_isUnit hp hq hpq A hA E ((fixedField_le_tailField A p q).trans hE) u hu

end
end DkMath.Lib.NumberTheory.InertiaResidue
