/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Basis argument adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_ExtCitation_Cyclotomic_finrank_unitsOmegaEigenspace_two.lean.
Upstream blob: 6801f82a5eec740ce4d5d658b7a1dc35040f2aba
Modified: use the SAME DkMath UnitClass and its actual quotient map,
prove finite-dimensionality directly from Dirichlet's finite generation.
-/

import DkMath.Lib.NumberTheory.CyclotomicPrimaryUnitSpace
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

#print "file: DkMath.Lib.NumberTheory.NumberFieldUnitPowerDimension"

/-!
# 実際の整数環単元冪商の有限次元性と基底

任意の数体で有限生成性を証明する。素数 p が捩れ単元群の位数を割る場合は、
捩れ群の巡回生成元1個と Dirichlet の基本単元から実際の UnitClass の基底を作る。
Galois 作用の指標・固有空間の次元をここで仮定しない。
-/

namespace DkMath.Lib.NumberTheory.NumberFieldUnitPowerDimension

open KummerSelmerExact DkMath.Lib.Algebra NumberField NumberField.Units
open scoped NumberField
noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-- 既存の単元冪商への実際の加法準同型。別の商を定義しない。 -/
def unitProjection (p : ℕ) : Additive (𝓞 F)ˣ →+ Additive (UnitClass (𝓞 F) p) :=
  (QuotientGroup.mk' (powerSubgroup (𝓞 F)ˣ p)).toAdditive

omit [NumberField F] in
theorem unitProjection_surjective (p : ℕ) : Function.Surjective (unitProjection (F := F) p) := by
  intro x
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (powerSubgroup (𝓞 F)ˣ p) x.toMul
  exact ⟨Additive.ofMul u, congrArg Additive.ofMul hu⟩

omit [NumberField F] in
/-- 零類は、同じ単元群の実際の p 倍（乗法記法では p 乗）と同値。 -/
theorem unitProjection_eq_zero_iff (p : ℕ) (a : Additive (𝓞 F)ˣ) :
    unitProjection p a = 0 ↔ ∃ b : Additive (𝓞 F)ˣ, p • b = a := by
  change (a.toMul : UnitClass (𝓞 F) p) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨Additive.ofMul u, congrArg Additive.ofMul hu⟩
  · rintro ⟨b, hb⟩
    exact ⟨b.toMul, congrArg Additive.toMul hb⟩

/-- Dirichlet の有限生成性の全射像。p の素数性すら不要。 -/
instance unitClassFinite (p : ℕ) : Module.Finite (ZMod p) (Additive (UnitClass (𝓞 F) p)) := by
  have : Module.Finite ℤ (Additive (UnitClass (𝓞 F) p)) :=
    Module.Finite.of_surjective (unitProjection p).toIntLinearMap (unitProjection_surjective p)
  exact Module.Finite.of_restrictScalars_finite ℤ (ZMod p) _

variable {p : ℕ} [hp : Fact p.Prime]

/-- 捩れ生成元と同じ基本単元の類からなる、実際の単元冪商の基底。 -/
theorem exists_unitClass_basis (F : Type*) [Field F] [NumberField F] (hdiv : p ∣ torsionOrder F) (t : torsion F)
    (ht : ∀ x : torsion F, x ∈ Subgroup.zpowers t) :
    ∃ b : Module.Basis (Option (Fin (rank F))) (ZMod p) (Additive (UnitClass (𝓞 F) p)),
      b none = unitProjection (F := F) p (Additive.ofMul (t : (𝓞 F)ˣ)) ∧
      ∀ i, b (some i) = unitProjection (F := F) p (Additive.ofMul (fundSystem F i)) := by
  classical
  have hord : orderOf t = torsionOrder F := by
    rw [torsionOrder]
    exact orderOf_eq_card_of_forall_mem_zpowers ht
  -- 捩れ部分の生成元と自由部分の基本単元を同じ族にまとめる。
  let a : Option (Fin (rank F)) → Additive (𝓞 F)ˣ := fun o =>
    o.elim (Additive.ofMul ((t : (𝓞 F)ˣ))) (fun i => Additive.ofMul (fundSystem F i))
  let v : Option (Fin (rank F)) → Additive (UnitClass (𝓞 F) p) := fun o => unitProjection (F := F) p (a o)
  have ha_none : Additive.toMul (a none) = (t : (𝓞 F)ˣ) := rfl
  have ha_some : ∀ i, Additive.toMul (a (some i)) = fundSystem F i := fun i => rfl
  -- 一次関係を実際の単元群の p 乗関係へ戻す。
  have hli : LinearIndependent (ZMod p) v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have key : ∑ o, g o • v o = unitProjection (F := F) p (∑ o, (g o).val • a o) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun o _ => ?_
      rw [map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
    rw [key, unitProjection_eq_zero_iff] at hg
    obtain ⟨b, hb⟩ := hg
    set u : (𝓞 F)ˣ := Additive.toMul b with hu_def
    -- 同じ単元について、Dirichlet 分解の一意性を適用する。
    have hb' : u ^ p = (t : (𝓞 F)ˣ) ^ (g none).val *
        ∏ i, fundSystem F i ^ (((g (some i)).val : ℕ) : ℤ) := by
      have := congrArg Additive.toMul hb
      rw [toMul_nsmul, toMul_sum, Fintype.prod_option] at this
      simp only [toMul_nsmul, ha_none, ha_some, zpow_natCast] at this ⊢
      exact this
    -- 自由部分の指数と捩れ部分の指数をそれぞれ比較する。
    obtain ⟨⟨ζu, eu⟩, hu, -⟩ := exist_unique_eq_mul_prod F u
    have h1 : u ^ p = ((⟨t ^ (g none).val, fun i => (((g (some i)).val : ℕ) : ℤ)⟩ :
        torsion F × (Fin (rank F) → ℤ))).1 * ∏ i, fundSystem F i ^
          ((⟨t ^ (g none).val, fun i => (((g (some i)).val : ℕ) : ℤ)⟩ :
            torsion F × (Fin (rank F) → ℤ))).2 i := by
      simpa only [Subgroup.coe_pow] using hb'
    have h2 : u ^ p = ((⟨ζu ^ p, fun i => (p : ℤ) * eu i⟩ :
        torsion F × (Fin (rank F) → ℤ))).1 * ∏ i, fundSystem F i ^
          ((⟨ζu ^ p, fun i => (p : ℤ) * eu i⟩ : torsion F × (Fin (rank F) → ℤ))).2 i := by
      simp only [Subgroup.coe_pow]
      conv_lhs => rw [hu]
      rw [mul_pow, ← Finset.prod_pow]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← zpow_natCast, ← zpow_mul, mul_comm]
    have huniq := (exist_unique_eq_mul_prod F (u ^ p)).unique h1 h2
    simp only [Prod.mk.injEq] at huniq
    obtain ⟨htor, hfun⟩ := huniq
    intro o
    cases o with
    | some i =>
      have hi := congrFun hfun i
      -- 自由部分の係数は p の倍数なので mod p で零になる。
      rw [← ZMod.natCast_zmod_val (g (some i)), ← Int.cast_natCast, hi]
      push_cast
      rw [ZMod.natCast_self, zero_mul]
    | none =>
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (ht ζu)
      have : t ^ ((g none).val : ℤ) = t ^ (m * p) := by
        rw [zpow_natCast, htor, ← hm, ← zpow_natCast, ← zpow_mul]
      rw [zpow_eq_zpow_iff_modEq, hord] at this
      have hmod := this.of_dvd (Int.natCast_dvd_natCast.mpr hdiv)
      rw [← ZMod.natCast_zmod_val (g none), ← Int.cast_natCast,
        (ZMod.intCast_eq_intCast_iff _ _ _).mpr hmod]
      push_cast
      rw [ZMod.natCast_self, mul_zero]
  -- 任意の単元の Dirichlet 分解が、この族の生成性も与える。
  have hsp : ⊤ ≤ Submodule.span (ZMod p) (Set.range v) := by
    rintro x -
    obtain ⟨y, rfl⟩ := unitProjection_surjective (F := F) p x
    obtain ⟨⟨ζu, eu⟩, hu, -⟩ := exist_unique_eq_mul_prod F (Additive.toMul y)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (ht ζu)
    have hy : y = m • a none + ∑ i, eu i • a (some i) := by
      apply Additive.toMul.injective
      rw [toMul_add, toMul_zsmul, toMul_sum, ha_none]
      simp only [toMul_zsmul, ha_some]
      rw [hu, ← hm, Subgroup.coe_zpow]
    rw [hy, map_add, map_zsmul, map_sum]
    refine Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun i _ => ?_)
    · rw [← Int.cast_smul_eq_zsmul (ZMod p)]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨none, rfl⟩)
    · rw [map_zsmul, ← Int.cast_smul_eq_zsmul (ZMod p)]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨some i, rfl⟩)
  refine ⟨Module.Basis.mk hli hsp, ?_, fun i => ?_⟩
  · rw [Module.Basis.mk_apply]; rfl
  · rw [Module.Basis.mk_apply]; rfl

/-- p が実際の捩れ位数を割るとき、単元商の次元は単元階数+1。 -/
theorem finrank_unitClass (F : Type*) [Field F] [NumberField F] (hdiv : p ∣ torsionOrder F) :
    Module.finrank (ZMod p) (Additive (UnitClass (𝓞 F) p)) = rank F + 1 := by
  obtain ⟨t, ht⟩ := IsCyclic.exists_generator (α := torsion F)
  obtain ⟨b, -, -⟩ := exists_unitClass_basis (p := p) F hdiv t ht
  rw [Module.finrank_eq_card_basis b, Fintype.card_option, Fintype.card_fin]


end
end DkMath.Lib.NumberTheory.NumberFieldUnitPowerDimension
