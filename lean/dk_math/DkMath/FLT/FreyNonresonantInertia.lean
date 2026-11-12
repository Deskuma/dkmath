/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyPrimePowerFiltration
import DkMath.Lib.Algebra.CyclicSignSeparation
import DkMath.Lib.NumberTheory.CyclotomicFrobenius
import DkMath.Lib.NumberTheory.EllipticNodalDecomposition

#print "file: DkMath.FLT.FreyNonresonantInertia"

/-!
# `q mod p ≠ ±1` の悪い素点で高次巡回段を零成分へ同定する

Frobenius の実際の底の作用は `q mod p`。同じ段の生成元についての二枝比較は、
作用差または和が滑らかになることを与える。底での `±1` からの分離により、
段全体が滑らかな部分群に入る。滑らかな高次捩れの上界から、その全体とも一致する。

この実際の一致は高次捩れと逆像上の慣性吸収を供給する。
残る悪い素点は `q mod p = ±1` の場合。一般 hno や大域分裂は結論しない。
-/

namespace DkMath.FLT.Frey.Source

open DkMath.Lib.Algebra DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation EllipticGoodReductionSeparation
open EllipticCriticalCentre EllipticTangentDirections EllipticNodalDecomposition
open ValuationInertia ValuationPrimeSupport ValuationFrobenius CyclotomicRootModule
open DkMath.Lib.RepresentationTheory

noncomputable section

variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance instIsEllipticNonresonantInertia : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic

/-- 同じ整数モデルの滑らかな点からなる実際の全点部分群。 -/
def valuationSmoothSubgroup (A : ValuationSubring (AlgebraicClosure ℚ)) :
    AddSubgroup (Points S.rationalCurve) :=
  smoothSubgroupOfModel (S.valuationModel A) _ (S.valuationModel_map A)

omit [Fact p.Prime] in
/-- 所属条件は、同じ点の同じモデルでの滑らかな還元。 -/
theorem mem_valuationSmoothSubgroup_iff (A : ValuationSubring (AlgebraicClosure ℚ))
    (P : Points S.rationalCurve) :
    P ∈ S.valuationSmoothSubgroup A ↔ HasSmoothReduction (S.valuationModel A) P :=
  mem_smoothSubgroupOfModel_iff (S.valuationModel A) _ (S.valuationModel_map A) P

/-- 2と悪い奇素数を同じ既存の中心・方向の構成へ統合する。 -/
theorem exists_geometry_at_bad_address (hp5 : 5 ≤ p) {q : ℕ} [Fact q.Prime]
    (hbad : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q) :
    ∃ C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)), Nonempty (TangentDirections C) := by
  by_cases hq2 : q = 2
  · subst q
    obtain ⟨C, D, _, _⟩ := S.exists_dyadic_geometry hp5 A hA
    exact ⟨C, ⟨D⟩⟩
  · have habc : (q : ℤ) ∣ S.a * S.b * S.c := hbad.resolve_left hq2
    obtain ⟨C, D, _, _⟩ := S.exists_criticalCentre_directions_at_bad_prime
      (Fact.out : p.Prime).pos hq2 habc A hA
    exact ⟨C, ⟨D⟩⟩

/-- Frobenius は底の同じ非零点上で、恒等・符号反転のどちらとも異なる。 -/
theorem residual_cofixed_frobenius_sign_separated
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) (hq1 : (q : ZMod p) ≠ 1) (hqneg : (q : ZMod p) ≠ -1)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (σ : Field.absoluteGaloisGroup ℚ) (hσ : IsFrobeniusAt A σ q) :
    ∃ x ∈ pointSubgroup S.rationalCurve p L, p • x = 0 ∧
      pointAction S.rationalCurve σ x ≠ x ∧ pointAction S.rationalCurve σ x ≠ -x := by
  have hbot := ((proper_nonzero_iff_finrank_one S.residual_finrank_eq_two L).mpr hline).1
  obtain ⟨P, hPL, hP⟩ : ∃ P ∈ L, P ≠ 0 := by
    by_contra h
    push Not at h
    exact hbot ((Submodule.eq_bot_iff L).mpr h)
  have hc := CyclotomicFrobenius.cyclotomicCharacter_eq_natCast hq hqp A hA hσ
  have hact := S.residual_cofixed_line_apply_eq_cyclotomic_smul L hline hcofixed σ hPL
  rw [hc] at hact
  have hne (c : ZMod p) (hcq : (q : ZMod p) ≠ c) : S.residualRepresentation σ P ≠ c • P := by
    intro heq
    have hz : ((q : ZMod p) - c) • P = 0 := by rw [sub_smul, ← hact, heq, sub_self]
    exact hP ((smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hcq))
  refine ⟨P.val, ⟨P, hPL, rfl⟩, P.property, ?_, ?_⟩
  · intro h
    exact hne 1 hq1 (by simpa only [one_smul] using (Subtype.ext h : S.residualRepresentation σ P = P))
  · intro h
    exact hne (-1) hqneg (by
      simpa only [neg_one_smul] using (Subtype.ext h : S.residualRepresentation σ P = -P))

/-- 符号から分離した悪い素点では、巡回段は全ての同次数の滑らかな捩れに一致する。 -/
theorem cyclic_tower_eq_smooth_torsion_of_nonresonant (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (K : AddSubgroup (Points S.rationalCurve)) [Finite K] [IsAddCyclic K]
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ K, pointAction S.rationalCurve σ x ∈ K)
    {m : ℕ} (hm : 1 ≤ m) (hcard : Nat.card K = p ^ m)
    (hbase : pointSubgroup S.rationalCurve p L ≤ K)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) (hbad : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (hq1 : (q : ZMod p) ≠ 1) (hqneg : (q : ZMod p) ≠ -1)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q) :
    K = AbsorbingTorsionFiltration.stage p m (S.valuationSmoothSubgroup A) := by
  classical
  let : Fact q.Prime := ⟨hq⟩
  obtain ⟨C, ⟨D⟩⟩ := S.exists_geometry_at_bad_address hp5 hbad A hA
  obtain ⟨σ, hσ⟩ := exists_isFrobeniusAt_of_liesOverPrime hq A hA
  obtain ⟨x, hxB, hpx, hnot1, hnotneg⟩ :=
    S.residual_cofixed_frobenius_sign_separated L hline hcofixed hq hqp hq1 hqneg A hA σ hσ
  have hexp (x : Points S.rationalCurve) (hx : x ∈ K) : p ^ m • x = 0 :=
    congrArg (fun z : K => z.val) (hcard ▸ card_nsmul_eq_zero' (x := (⟨x, hx⟩ : K)))
  have hpunit : A.valuation (p : AlgebraicClosure ℚ) = 1 :=
    valuation_intCast_eq_one_of_not_dvd A hq ((ValuationSubring.mem_nonunits_iff _).mp hA) (by
      intro h
      exact hqp ((Nat.prime_dvd_prime_iff_eq hq Fact.out).mp (by exact_mod_cast h)))
  have hunit : A.valuation ((p ^ m : ℕ) : AlgebraicClosure ℚ) = 1 := by
    rw [Nat.cast_pow, map_pow, hpunit, one_pow]
  have hn3 : 3 ≤ p ^ m := by
    have hpow := Nat.pow_le_pow_right (Fact.out : p.Prime).pos hm
    rw [pow_one] at hpow
    omega
  have hKH : K ≤ S.valuationSmoothSubgroup A := by
    apply CyclicSignSeparation.le_of_sub_or_add_mem (Fact.out : p.Prime) K _ hexp
      (pointAction S.rationalCurve σ) (hstable σ)
      ⟨x, hbase hxB, hpx, hnot1⟩ ⟨x, hbase hxB, hpx, hnotneg⟩
    intro y hy hout
    have hd := sub_or_add_smooth_of_odd_torsion S.rationalCurve A (S.valuationModel A)
      (S.valuationModel_map A) C D ((Fact.out : p.Prime).odd_of_ne_two (by omega)).pow
      hn3 hunit σ hσ.mem_decompositionSubgroup (hexp y hy)
      (fun h => hout ((S.mem_valuationSmoothSubgroup_iff A y).mpr h))
    exact hd.imp ((S.mem_valuationSmoothSubgroup_iff A _).mpr) ((S.mem_valuationSmoothSubgroup_iff A _).mpr)
  have hle : K ≤ AbsorbingTorsionFiltration.stage p m (S.valuationSmoothSubgroup A) :=
    fun x hx => ⟨hexp x hx, hKH hx⟩
  have hbound : Nat.card (AbsorbingTorsionFiltration.stage p m (S.valuationSmoothSubgroup A)) ≤ p ^ m := by
    apply EllipticNodalTorsionBound.card_le_of_injective_smooth_torsion (S.valuationModel A)
      _ (S.valuationModel_map A) C D (pow_pos (Fact.out : p.Prime).pos m) hunit Subtype.val Subtype.val_injective
    · intro y
      exact (S.mem_valuationSmoothSubgroup_iff A y.val).mp y.property.2
    · intro y
      exact y.property.1
  let : Finite (TorsionMultiplication.Kernel (Points S.rationalCurve) (p ^ m)) :=
    finite_torsion_of_ne_zero S.rationalCurve _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  let : Finite (AbsorbingTorsionFiltration.stage p m (S.valuationSmoothSubgroup A)) :=
    AbsorbingTorsionFiltration.finiteStage p m (S.valuationSmoothSubgroup A)
  apply SetLike.coe_injective
  refine Set.eq_of_subset_of_ncard_le hle ?_ (Set.toFinite _)
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, SetLike.coe_sort_coe, hcard]
  exact hbound

/-- 悪い住所で、全点の慣性差は同じモデルで滑らかに還元する。 -/
theorem inertia_difference_smooth_at_bad_address (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime)
    (hbad : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (τ : Field.absoluteGaloisGroup ℚ) (hτ : τ ∈ inertiaSubgroupIn A ℚ) (y : Points S.rationalCurve) :
    HasSmoothReduction (S.valuationModel A) (pointAction S.rationalCurve τ y - y) := by
  classical
  let : Fact q.Prime := ⟨hq⟩
  obtain ⟨C, ⟨D⟩⟩ := S.exists_geometry_at_bad_address hp5 hbad A hA
  have hd := (ValuationTameCharacter.TameCharacter.mem_inertiaSubgroupIn_iff.mp hτ).1
  exact EllipticNodalInertia.inertia_difference_smooth S.rationalCurve A (S.valuationModel A)
    (S.valuationModel_map A) C D τ hτ (centre_decomposition_fixed S.rationalCurve A C τ hd) y

/-- 非共鳴の悪い素点では、同じ次数の高次捩れの慣性差が巡回段自体に入る。 -/
theorem prime_power_pointAction_sub_mem_of_nonresonant_bad (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (K : AddSubgroup (Points S.rationalCurve)) [Finite K] [IsAddCyclic K]
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ K, pointAction S.rationalCurve σ x ∈ K)
    {N : ℕ} (hN : 0 < N) (hcard : Nat.card K = p ^ N)
    (hbase : pointSubgroup S.rationalCurve p L ≤ K)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) (hbad : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (hq1 : (q : ZMod p) ≠ 1) (hqneg : (q : ZMod p) ≠ -1)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (τ : Field.absoluteGaloisGroup ℚ) (hτ : τ ∈ inertiaSubgroupIn A ℚ)
    {y : Points S.rationalCurve} (hy : p ^ N • y = 0) : pointAction S.rationalCurve τ y - y ∈ K := by
  rw [S.cyclic_tower_eq_smooth_torsion_of_nonresonant hp5 L hline hcofixed K hstable
    (by omega : 1 ≤ N) hcard hbase hq hqp hbad hq1 hqneg A hA]
  refine ⟨?_, (S.mem_valuationSmoothSubgroup_iff A _).mpr
    (S.inertia_difference_smooth_at_bad_address hp5 hq hbad A hA τ hτ y)⟩
  change p ^ N • (pointAction S.rationalCurve τ y - y) = 0
  rw [nsmul_sub, ← map_nsmul, hy, map_zero, sub_self]

/-- 非共鳴の悪い素点では逆像 `p⁻¹K` 上の慣性差も同じ `K` に吸収される。
底の滑らかな点の慣性固定性により、差の捩れ次数を一段下げる。 -/
theorem preimage_pointAction_sub_mem_of_nonresonant_bad (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (K : AddSubgroup (Points S.rationalCurve)) [Finite K] [IsAddCyclic K]
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ K, pointAction S.rationalCurve σ x ∈ K)
    {m : ℕ} (hm : 1 ≤ m) (hcard : Nat.card K = p ^ m)
    (hbase : pointSubgroup S.rationalCurve p L ≤ K)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) (hbad : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (hq1 : (q : ZMod p) ≠ 1) (hqneg : (q : ZMod p) ≠ -1)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (τ : Field.absoluteGaloisGroup ℚ) (hτ : τ ∈ inertiaSubgroupIn A ℚ)
    {y : Points S.rationalCurve} (hy : p • y ∈ K) : pointAction S.rationalCurve τ y - y ∈ K := by
  have hK := S.cyclic_tower_eq_smooth_torsion_of_nonresonant hp5 L hline hcofixed K hstable
    hm hcard hbase hq hqp hbad hq1 hqneg A hA
  have hyt : p ^ (m + 1) • y = 0 := by
    rw [pow_succ, mul_nsmul']
    exact congrArg (fun z : K => z.val) (hcard ▸ card_nsmul_eq_zero' (x := (⟨p • y, hy⟩ : K)))
  have htop : p ^ m • y ∈ K := by
    rw [← Nat.sub_add_cancel hm, pow_succ, mul_nsmul']
    exact K.nsmul_mem hy (p ^ (m - 1))
  have hptop : p • (p ^ m • y) = 0 := by rwa [← mul_nsmul', ← pow_succ']
  have hsm : HasSmoothReduction (S.valuationModel A) (p ^ m • y) := by
    rw [hK] at htop
    exact (S.mem_valuationSmoothSubgroup_iff A _).mp htop.2
  have hfix : pointAction S.rationalCurve τ (p ^ m • y) = p ^ m • y :=
    congrArg Subtype.val (S.residual_fixed_of_smooth_reduction hq hqp A hA τ hτ
      (⟨p ^ m • y, hptop⟩ : S.ResidualSpace) hsm)
  rw [hK]
  refine ⟨?_, (S.mem_valuationSmoothSubgroup_iff A _).mpr
    (S.inertia_difference_smooth_at_bad_address hp5 hq hbad A hA τ hτ y)⟩
  change p ^ m • (pointAction S.rationalCurve τ y - y) = 0
  rw [nsmul_sub, ← map_nsmul, hfix, sub_self]

/-- 2・3は `p≥5` で符号共鳴しない。小住所を未実装条件に残さないための算術。 -/
theorem small_prime_sign_separated (hp5 : 5 ≤ p) (q : ℕ) (hsmall : q = 2 ∨ q = 3) :
    (q : ZMod p) ≠ 1 ∧ (q : ZMod p) ≠ -1 := by
  have hq : 2 ≤ q ∧ q ≤ 3 := by rcases hsmall with rfl | rfl <;> omega
  constructor
  · intro heq
    have hz : ((q - 1 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one, heq, sub_self]
    have hd := (CharP.cast_eq_zero_iff (ZMod p) p (q - 1)).mp hz
    have := Nat.le_of_dvd (by omega : 0 < q - 1) hd
    omega
  · intro heq
    have hz : ((q + 1 : ℕ) : ZMod p) = 0 := by rw [Nat.cast_add, Nat.cast_one, heq, neg_add_cancel]
    have hd := (CharP.cast_eq_zero_iff (ZMod p) p (q + 1)).mp hz
    have := Nat.le_of_dvd (by omega : 0 < q + 1) hd
    omega

/-- 残る符号共鳴住所は必ず5以上。 -/
theorem five_le_of_prime_sign_resonance (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime)
    (hres : (q : ZMod p) = 1 ∨ (q : ZMod p) = -1) : 5 ≤ q := by
  by_contra h
  have hsmall : q = 2 ∨ q = 3 := by
    have hq4 : q ≠ 4 := by intro heq; subst q; norm_num at hq
    have := hq.two_le
    omega
  have hsep := small_prime_sign_separated hp5 q hsmall
  exact hres.elim hsep.1 hsep.2

/-- 商表現の全 `p` 外の不分岐性。未実装入力は共鳴する悪い住所だけ。 -/
theorem residual_preimage_unramified_away_of_resonant_inertia (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (K : AddSubgroup (Points S.rationalCurve)) [Finite K] [IsAddCyclic K]
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ K, pointAction S.rationalCurve σ x ∈ K)
    {m : ℕ} (hm : 1 ≤ m) (hcard : Nat.card K = p ^ m)
    (hbase : pointSubgroup S.rationalCurve p L ≤ K)
    (hbad : ∀ q : ℕ, q.Prime → q ≠ p → 5 ≤ q → (q : ℤ) ∣ S.a * S.b * S.c →
      ((q : ZMod p) = 1 ∨ (q : ZMod p) = -1) →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), LiesOverPrime A q →
        ∀ τ ∈ inertiaSubgroupIn A ℚ, ∀ y : Points S.rationalCurve,
          p • y ∈ K → pointAction S.rationalCurve τ y - y ∈ K)
    (q : ℕ) (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (τ : Field.absoluteGaloisGroup ℚ) (hτ : τ ∈ inertiaSubgroupIn A ℚ)
    (v : TorsionPreimageQuotient.Quotient p K) : preimageRepresentation S.rationalCurve p K hstable τ v = v := by
  apply S.residual_preimage_unramified_away_of_bad_inertia K hstable hcard ?_ q hq hqp A hA τ hτ v
  intro r hr hrp hsupport B hB η hη y hy
  by_cases hres : (r : ZMod p) = 1 ∨ (r : ZMod p) = -1
  · have hr5 := five_le_of_prime_sign_resonance hp5 hr hres
    have habc := hsupport.resolve_left (by omega : r ≠ 2)
    exact hbad r hr hrp hr5 habc hres B hB η hη y hy
  · exact S.preimage_pointAction_sub_mem_of_nonresonant_bad hp5 L hline hcofixed K hstable hm hcard
      hbase hr hrp hsupport (fun h => hres (Or.inl h)) (fun h => hres (Or.inr h)) B hB η hη hy

/-- 最終矛盾の局所仮定を、`q≥5`, `q≠p`, `q∣abc`, `q mod p=±1` へ限定する。
共鳴する住所の吸収、大域巡回塔の存在、実際の Frobenius 関係は依然入力である。 -/
theorem residual_cofixed_tower_resonant_inertia_frobenius_impossible (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (K : AddSubgroup (Points S.rationalCurve)) [Finite K] [IsAddCyclic K]
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ K, pointAction S.rationalCurve σ x ∈ K)
    {N : ℕ} (hN : 0 < N) (hcard : Nat.card K = p ^ N)
    (hbase : pointSubgroup S.rationalCurve p L ≤ K)
    (hbad : ∀ q : ℕ, q.Prime → q ≠ p → 5 ≤ q → (q : ℤ) ∣ S.a * S.b * S.c →
      ((q : ZMod p) = 1 ∨ (q : ZMod p) = -1) →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), LiesOverPrime A q →
        ∀ τ ∈ inertiaSubgroupIn A ℚ, ∀ y : Points S.rationalCurve,
          p ^ N • y = 0 → pointAction S.rationalCurve τ y - y ∈ K)
    (σ : Field.absoluteGaloisGroup ℚ) (ell : ℤ)
    (hCH : ∀ y : Points S.rationalCurve, p ^ N • y = 0 →
      pointAction S.rationalCurve σ (pointAction S.rationalCurve σ y) + ell • y =
        (ell + 1 - (N : ℤ)) • pointAction S.rationalCurve σ y) : False := by
  apply S.residual_cofixed_cyclic_tower_inertia_frobenius_impossible hp5 L hline hcofixed K hstable
    hN hcard hbase ?_ σ ell hCH
  intro q hq hqp hsupport A hA τ hτ y hy
  by_cases hres : (q : ZMod p) = 1 ∨ (q : ZMod p) = -1
  · have hq5 := five_le_of_prime_sign_resonance hp5 hq hres
    exact hbad q hq hqp hq5 (hsupport.resolve_left (by omega : q ≠ 2)) hres A hA τ hτ y hy
  · exact S.prime_power_pointAction_sub_mem_of_nonresonant_bad hp5 L hline hcofixed K hstable hN hcard
      hbase hq hqp hsupport (fun h => hres (Or.inl h)) (fun h => hres (Or.inr h)) A hA τ hτ hy

end
end DkMath.FLT.Frey.Source
