/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCofixedTorsionTower
import DkMath.FLT.FreyPrimeFiltration
import DkMath.Lib.Algebra.AbsorbingTorsionFiltration
import DkMath.Lib.NumberTheory.CyclotomicInertia
import DkMath.Lib.NumberTheory.EllipticNodalPrimePowerKernel

#print "file: DkMath.FLT.FreyPrimePowerFiltration"

/-!
# `p` 上の実際の高次還元核と局所分裂

同じ付値環・整数モデルにおける還元核と `E[p^m]` の交わりを作る。
整な残余捩れ点から底の上界を、円分指標の慣性上の全射性から非自明性を供給し、
全段の濃度 `p^m` と巡回性を証明する。良還元・乗法還元を内部で場合分けする。
元の Cofixed 直線を含む大域安定な巡回段は、この同じ局所段に一致する。
次段の像が分解群安定な補直線となる。局所群や分裂の存在を仮定しない。
大域 extension 消滅、悪い `q≠p` の吸収、一般 `hno` は依然別の算術である。
-/

namespace DkMath.FLT.Frey.Source

open DkMath.Lib.Algebra DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation EllipticReductionKernel EllipticDyadicSeparation
open ValuationInertia CyclotomicRootModule
open ValuationTameCharacter.TameCharacter
open DkMath.Lib.RepresentationTheory WeierstrassCurve

noncomputable section

local instance instDecidableEqPrimePowerFiltration : DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _

variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance instIsEllipticPrimePowerFiltration : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic

/-- 同じ整数モデルに由来する実際の全点群の還元核。 -/
def valuationReductionKernel (A : ValuationSubring (AlgebraicClosure ℚ)) :
    AddSubgroup (Points S.rationalCurve) :=
  ofIntegral A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)) (S.integral_at_valuation A)

/-- `p` 上の高次局所部分群。幾何学的点と還元核を選び直さない。 -/
abbrev primePowerReductionFiltration (A : ValuationSubring (AlgebraicClosure ℚ)) (m : ℕ) :=
  AbsorbingTorsionFiltration.stage p m (S.valuationReductionKernel A)

/-- 全高次捩れの慣性変化量は同じ還元核に入る。`p` の単元性は使わない。 -/
theorem prime_power_reductionKernel_absorbs_at_p (hp2 : p ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A p)
    (m : ℕ) (τ : Field.absoluteGaloisGroup ℚ) (hτ : τ ∈ inertiaSubgroupIn A ℚ)
    {y : Points S.rationalCurve} (hy : p ^ m • y = 0) :
    pointAction S.rationalCurve τ y - y ∈ S.valuationReductionKernel A := by
  classical
  by_cases hbad : (p : ℤ) ∣ S.a * S.b * S.c
  · let : CharP (IsLocalRing.ResidueField A) p := ValuationPrimeSupport.charP_residueField A Fact.out hA
    obtain ⟨C, _, _⟩ := S.exists_criticalCentre_at_bad_prime (Fact.out : p.Prime).pos hp2 hbad A hA
    have hs := S.inertia_difference_smooth_at_bad_prime hp2 hbad A hA τ hτ y
    have ht : p ^ m • (pointAction S.rationalCurve τ y - y) = 0 := by
      rw [nsmul_sub, ← map_nsmul, hy, map_zero, sub_self]
    apply (mem_ofIntegral_iff A _ _ _).mpr
    exact EllipticNodalReductionKernel.pole_of_smooth_prime_power_torsion_of_model
      (S.valuationModel A) _ (S.valuationModel_map A) C hs m ht
  · have hg : (((S.integral_at_valuation A).model).map (IsLocalRing.residue A)).Δ ≠ 0 := by
      have he : (S.integral_at_valuation A).model = S.valuationModel A := by
        apply WeierstrassCurve.map_injective (f := A.subtype) Subtype.val_injective
        change (S.integral_at_valuation A).model.map A.subtype = (S.valuationModel A).map A.subtype
        rw [Integral.model_map, S.valuationModel_map A]
      rw [he]
      exact isUnit_iff_ne_zero.mp ((WeierstrassCurve.isElliptic_iff _).mp
        (S.valuation_reduction_isElliptic (Fact.out : p.Prime).pos hp2 hbad A hA))
    exact EllipticGoodReductionKernel.inertia_difference_mem S.rationalCurve A
      (S.integral_at_valuation A) hg τ hτ y

omit [Fact p.Prime] in
/-- 同じ還元核は分解群で安定。無限遠・極という座標条件を保存する。 -/
theorem valuationReductionKernel_stable
    (A : ValuationSubring (AlgebraicClosure ℚ)) (σ : Field.absoluteGaloisGroup ℚ)
    (hσ : σ ∈ A.decompositionSubgroup ℚ) {y : Points S.rationalCurve}
    (hy : y ∈ S.valuationReductionKernel A) : pointAction S.rationalCurve σ y ∈ S.valuationReductionKernel A := by
  classical
  cases y with
  | zero => exact (S.valuationReductionKernel A).zero_mem
  | some x y h =>
    have hx : x ∉ A := by
      have hpole := (mem_ofIntegral_iff A (S.rationalCurve.baseChange (AlgebraicClosure ℚ))
        (S.integral_at_valuation A) (Affine.Point.some x y h)).mp hy
      rw [poleOrZero_some_iff] at hpole
      exact fun hx => not_lt_of_ge ((A.valuation_le_one_iff _).mpr hx) hpole
    apply (mem_ofIntegral_iff A (S.rationalCurve.baseChange (AlgebraicClosure ℚ))
      (S.integral_at_valuation A) _).mpr
    change PoleOrZero A (S.rationalCurve.baseChange (AlgebraicClosure ℚ))
      (Affine.Point.map σ.toAlgHom (Affine.Point.some x y h))
    rw [Affine.Point.map_some, poleOrZero_some_iff]
    exact lt_of_not_ge (fun hv => hx ((apply_mem_iff hσ x).mp ((A.valuation_le_one_iff _).mp hv)))

/-- 円分指標の慣性上の全射性を、元の同じ底の点を動かす元へ接続する。 -/
theorem residual_cofixed_inertia_moves_base_at_p (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A p) :
    ∃ τ ∈ inertiaSubgroupIn A ℚ, ∃ x ∈ pointSubgroup S.rationalCurve p L,
      p • x = 0 ∧ pointAction S.rationalCurve τ x ≠ x := by
  have hbot := ((proper_nonzero_iff_finrank_one S.residual_finrank_eq_two L).mpr hline).1
  obtain ⟨P, hPL, hP⟩ : ∃ P ∈ L, P ≠ 0 := by
    by_contra h
    push Not at h
    exact hbot ((Submodule.eq_bot_iff L).mpr h)
  obtain ⟨τ, hτ, hχ⟩ := CyclotomicInertia.exists_inertia_cyclotomic_eq A hA (-1)
  refine ⟨τ, hτ, P.val, ⟨P, hPL, rfl⟩, P.property, ?_⟩
  intro hfix
  have hfix' : S.residualRepresentation τ P = P := Subtype.ext hfix
  have hact := S.residual_cofixed_line_apply_eq_cyclotomic_smul L hline hcofixed τ hPL
  have hχv : (cyclotomicCharacter p τ : ZMod p) = -1 := by
    simpa only [Units.val_neg, Units.val_one] using congrArg Units.val hχ
  rw [hχv, neg_one_smul, hfix'] at hact
  have h2 : (2 : ZMod p) • P = 0 := by
    rw [two_smul]
    calc P + P = -P + P := congrArg (fun z => z + P) hact
      _ = 0 := neg_add_cancel P
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp hz
    have := Nat.le_of_dvd (by decide : 0 < 2) hd
    omega
  exact hP ((smul_eq_zero.mp h2).resolve_left h2ne)

/-- 整な有限残余点から、還元核の底の濃度を `p` 以下に抑える。 -/
theorem prime_reductionKernel_card_le (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hstable : IsStable S.residualRepresentation L)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A p) :
    Nat.card (TorsionMultiplication.Kernel (Points S.rationalCurve) p ⊓
      S.valuationReductionKernel A : AddSubgroup (Points S.rationalCurve)) ≤ p := by
  let e : (TorsionMultiplication.Kernel (Points S.rationalCurve) p ⊓ S.valuationReductionKernel A :
      AddSubgroup (Points S.rationalCurve)) ≃ S.residualReductionKernel A := {
    toFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
    invFun x := ⟨x.val.val, ⟨x.val.property, x.property⟩⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have hproper := (proper_nonzero_iff_finrank_one S.residual_finrank_eq_two L).mpr hline
  have hne := S.residualReductionKernel_ne_top hp5 A hA L hstable hproper.1 hproper.2
  have hd := Submodule.finrank_lt hne
  rw [S.residual_finrank_eq_two] at hd
  rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  calc p ^ Module.finrank (ZMod p) (S.residualReductionKernel A) ≤ p ^ 1 :=
      pow_le_pow_right' (Fact.out : p.Prime).one_le (by omega)
    _ = p := pow_one p

/-- 全段の還元核の正確な位数と巡回性。局所群を同じ交わりとして構成する。 -/
theorem primePowerReductionFiltration_cyclic_and_card (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A p)
    {m : ℕ} (hm : 1 ≤ m) :
    IsAddCyclic (S.primePowerReductionFiltration A m) ∧
      Nat.card (S.primePowerReductionFiltration A m) = p ^ m := by
  let : Finite (TorsionMultiplication.Kernel (Points S.rationalCurve) p) :=
    finite_torsion_of_ne_zero S.rationalCurve p (Fact.out : p.Prime).ne_zero
  let : Finite (TorsionMultiplication.Kernel (Points S.rationalCurve) (p ^ m)) :=
    finite_torsion_of_ne_zero S.rationalCurve _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  apply AbsorbingTorsionFiltration.cyclic_and_card (Fact.out : p.Prime) hm
    (S.valuationReductionKernel A)
    (S.prime_reductionKernel_card_le hp5 L hline hcofixed.isStable A hA)
    (pointActionEndHom S.rationalCurve)
    {τ : Field.absoluteGaloisGroup ℚ | τ ∈ inertiaSubgroupIn A ℚ} ?_ ?_
    (multiplication_surjective S.rationalCurve _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero))
  · intro τ hτ y hy
    exact S.prime_power_reductionKernel_absorbs_at_p (by omega) A hA m τ hτ hy
  · obtain ⟨τ, hτ, x, _, hx, hmove⟩ := S.residual_cofixed_inertia_moves_base_at_p hp5 L hline hcofixed A hA
    exact ⟨τ, hτ, x, hx, hmove⟩

/-- 大域安定な巡回段は、指定した同じ `p` 上の局所段そのもの。 -/
theorem cyclic_tower_eq_primePowerReductionFiltration (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (K : AddSubgroup (Points S.rationalCurve)) [Finite K] [IsAddCyclic K]
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ K, pointAction S.rationalCurve σ x ∈ K)
    {m : ℕ} (hm : 1 ≤ m) (hcard : Nat.card K = p ^ m)
    (hbase : pointSubgroup S.rationalCurve p L ≤ K)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A p) :
    K = S.primePowerReductionFiltration A m := by
  have hexp (x : Points S.rationalCurve) (hx : x ∈ K) : p ^ m • x = 0 :=
    congrArg (fun z : K => z.val) (hcard ▸ card_nsmul_eq_zero' (x := (⟨x, hx⟩ : K)))
  obtain ⟨τ, hτ, x, hx, hpx, hmove⟩ := S.residual_cofixed_inertia_moves_base_at_p hp5 L hline hcofixed A hA
  have hle : K ≤ S.primePowerReductionFiltration A m := by
    apply AbsorbingTorsionFiltration.le_of_nontrivial_socle (Fact.out : p.Prime) K _ hexp
      (pointAction S.rationalCurve τ) (hstable τ) ⟨x, hbase hx, hpx, hmove⟩
    intro y hy
    refine ⟨?_, S.prime_power_reductionKernel_absorbs_at_p (by omega) A hA m τ hτ (hexp y hy)⟩
    change p ^ m • (pointAction S.rationalCurve τ y - y) = 0
    rw [nsmul_sub, ← map_nsmul, hexp y hy, map_zero, sub_self]
  have hFcard := (S.primePowerReductionFiltration_cyclic_and_card hp5 L hline hcofixed A hA hm).2
  let : Finite (S.primePowerReductionFiltration A m) :=
    Nat.finite_of_card_ne_zero (hFcard ▸ pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  apply SetLike.coe_injective
  refine Set.eq_of_subset_of_ncard_le hle ?_ (Set.toFinite _)
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, SetLike.coe_sort_coe,
    hcard, hFcard]

/-- 同じ Source と巡回段から `p` 上の局所分裂を内部構成する。 -/
theorem residual_cofixed_cyclic_extension_locally_split_at_p (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (K : AddSubgroup (Points S.rationalCurve)) [Finite K] [IsAddCyclic K]
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ K, pointAction S.rationalCurve σ x ∈ K)
    {m : ℕ} (hm : 1 ≤ m) (hcard : Nat.card K = p ^ m)
    (hbase : pointSubgroup S.rationalCurve p L ≤ K)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A p) :
    ∃ C' : Submodule (ZMod p) (TorsionPreimageQuotient.Quotient p K),
      IsCompl (TorsionPreimageQuotient.torsionImage p K) C' ∧
      (∀ σ ∈ A.decompositionSubgroup ℚ, ∀ v ∈ C',
        preimageRepresentation S.rationalCurve p K hstable σ v ∈ C') ∧
      TorsionPreimageQuotient.liftSubmodule p K C' = S.primePowerReductionFiltration A (m + 1) := by
  have hK := S.cyclic_tower_eq_primePowerReductionFiltration hp5 L hline hcofixed K hstable hm hcard hbase A hA
  apply S.residual_cyclic_extension_complement_of_local_subgroup K hstable hm hcard A
    (S.primePowerReductionFiltration A (m + 1))
  · intro x hx
    rw [hK] at hx
    refine ⟨?_, hx.2⟩
    change p ^ (m + 1) • x = 0
    rw [pow_succ', mul_nsmul', show p ^ m • x = 0 from hx.1, nsmul_zero]
  · intro x hx
    rw [hK]
    refine ⟨?_, (S.valuationReductionKernel A).nsmul_mem hx.2 p⟩
    change p ^ m • (p • x) = 0
    rw [← mul_nsmul', ← pow_succ]
    exact hx.1
  · exact (S.primePowerReductionFiltration_cyclic_and_card hp5 L hline hcofixed A hA (by omega : 1 ≤ m + 1)).2
  · intro x hx hpx
    rw [hK]
    refine ⟨?_, hx.2⟩
    change p ^ m • x = 0
    rw [← Nat.sub_add_cancel hm, pow_succ, mul_nsmul', hpx, nsmul_zero]
  · intro σ hσ x hx
    refine ⟨?_, S.valuationReductionKernel_stable A σ hσ hx.2⟩
    change p ^ (m + 1) • pointAction S.rationalCurve σ x = 0
    rw [← map_nsmul, show p ^ (m + 1) • x = 0 from hx.1, map_zero]

/-- 同じ指数の巡回段では、`p` 上の全高次捩れの慣性差が段自体へ吸収される。 -/
theorem prime_power_pointAction_sub_mem_cyclic_tower_at_p (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (K : AddSubgroup (Points S.rationalCurve)) [Finite K] [IsAddCyclic K]
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ K, pointAction S.rationalCurve σ x ∈ K)
    {N : ℕ} (hN : 0 < N) (hcard : Nat.card K = p ^ N)
    (hbase : pointSubgroup S.rationalCurve p L ≤ K)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A p)
    (τ : Field.absoluteGaloisGroup ℚ) (hτ : τ ∈ inertiaSubgroupIn A ℚ)
    {y : Points S.rationalCurve} (hy : p ^ N • y = 0) :
    pointAction S.rationalCurve τ y - y ∈ K := by
  rw [S.cyclic_tower_eq_primePowerReductionFiltration hp5 L hline hcofixed K hstable
    (by omega : 1 ≤ N) hcard hbase A hA]
  refine ⟨?_, S.prime_power_reductionKernel_absorbs_at_p (by omega) A hA N τ hτ hy⟩
  change p ^ N • (pointAction S.rationalCurve τ y - y) = 0
  rw [nsmul_sub, ← map_nsmul, hy, map_zero, sub_self]

/-- 最終矛盾の `p` 上の吸収仮定も内部供給する。
残す局所仮定は `q≠p` かつ `q=2` または `q∣abc` の住所だけ。
巡回段の存在と実際の Frobenius 関係はなお明示入力である。 -/
theorem residual_cofixed_cyclic_tower_inertia_frobenius_impossible (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (K : AddSubgroup (Points S.rationalCurve)) [Finite K] [IsAddCyclic K]
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ K, pointAction S.rationalCurve σ x ∈ K)
    {N : ℕ} (hN : 0 < N) (hcard : Nat.card K = p ^ N)
    (hbase : pointSubgroup S.rationalCurve p L ≤ K)
    (hbad : ∀ q : ℕ, q.Prime → q ≠ p → (q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), LiesOverPrime A q →
        ∀ τ ∈ inertiaSubgroupIn A ℚ, ∀ y : Points S.rationalCurve,
          p ^ N • y = 0 → pointAction S.rationalCurve τ y - y ∈ K)
    (σ : Field.absoluteGaloisGroup ℚ) (ell : ℤ)
    (hCH : ∀ y : Points S.rationalCurve, p ^ N • y = 0 →
      pointAction S.rationalCurve σ (pointAction S.rationalCurve σ y) + ell • y =
        (ell + 1 - (N : ℤ)) • pointAction S.rationalCurve σ y) : False := by
  apply S.residual_cyclic_tower_inertia_frobenius_impossible L hline K (by omega : 1 ≤ N)
    hcard hbase hN ?_ σ ell hCH
  intro q hq hsupport A hA τ hτ y hy
  by_cases hqp : q = p
  · subst q
    exact S.prime_power_pointAction_sub_mem_cyclic_tower_at_p hp5 L hline hcofixed K hstable
      hN hcard hbase A hA τ hτ hy
  · apply hbad q hq hqp ?_ A hA τ hτ y hy
    rcases hsupport with h2 | hp | habc
    · exact Or.inl h2
    · exact (hqp hp).elim
    · exact Or.inr habc

end
end DkMath.FLT.Frey.Source
