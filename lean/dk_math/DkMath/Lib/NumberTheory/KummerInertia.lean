/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_FreyPackage_frey_exists_inertia_not_fixed_at_two.lean,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
Modified: arbitrary distinct primes p,q; public Kummer API; DkMath finite lifts,
place conjugacy and unit-power rigidity replace upstream private interfaces.
-/

import DkMath.Lib.NumberTheory.ValuationInertiaPower
import DkMath.Lib.NumberTheory.IntegralClosureInertiaLift
import DkMath.Lib.NumberTheory.ValuationInertiaLift
import DkMath.Lib.NumberTheory.ValuationPlaceConjugacy
import Mathlib.FieldTheory.SplittingField.IsSplittingField
import Mathlib.NumberTheory.RamificationInertia.HilbertTheory

#print "file: DkMath.Lib.NumberTheory.KummerInertia"

/-!
# NOTE-032-002A: 深さのp非可除性からKummer根を動かす慣性元へ

[DkMath.Lib] 相異なる素数p,qについて、sᵖ=qᵐかつp∤mなら、
指定したq上の付値環Aの慣性群にはsを動かす元が存在する。
これは任意の根sと任意のAの組についての主張であり、付値環を結論で選び直さない。

証明の台帳は次のとおり。
1. Xᵖ−qᵐの有限分解体Lとq上の素イデアルQを取る。
2. Qの慣性がsを固定すると、p乗根の1の枝も固定するのでL全体を固定する。
3. 慣性群の位数＝分岐指数よりe(Q/q)=1となる。
4. (s)ᵖ=(q)ᵐのQ重複度を比較するとp∣mとなり矛盾する。
5. 有限慣性元を絶対慣性へ持ち上げる。付値環の共役でAへ戻す際に現れる
   g(s)/sもp乗根なので、再び単元の剛性を使って同じsが動くことを保証する。

円分整数環の類群や正則素数は仮定しない。Freyのp捩れ点への適用には、
その点の座標差と判別式深さとの関係を別に供給する必要がある。
-/
namespace DkMath.Lib.NumberTheory.KummerInertia
open ValuationInertia
open scoped Pointwise
noncomputable section

private def kumPoly (q p m : ℕ) : Polynomial ℚ := Polynomial.X ^ p - Polynomial.C ((q : ℚ) ^ m)

private def kumField (q p m : ℕ) : IntermediateField ℚ (AlgebraicClosure ℚ) :=
  IntermediateField.adjoin ℚ ((kumPoly q p m).rootSet (AlgebraicClosure ℚ))

private scoped instance (q p m : ℕ) : Polynomial.IsSplittingField ℚ (kumField q p m) (kumPoly q p m) :=
  IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)

private scoped instance (q p m : ℕ) : FiniteDimensional ℚ (kumField q p m) :=
  Polynomial.IsSplittingField.finiteDimensional (kumField q p m) (kumPoly q p m)

private scoped instance (q p m : ℕ) : Normal ℚ (kumField q p m) :=
  Normal.of_isSplittingField (kumPoly q p m)

private scoped instance (q p m : ℕ) : IsGalois ℚ (kumField q p m) := ⟨⟩

private scoped instance (q p m : ℕ) : NumberField (kumField q p m) := ⟨⟩

-- 分解体の整数環・剰余体・ガロア群を同時に扱う型クラス探索のため局所的に増やす。
set_option maxHeartbeats 1600000 in
-- 有限分解体上の整数環・剰余体・分岐指数の照合に使う証明の局所上限。
set_option synthInstance.maxHeartbeats 400000 in
/-- [DkMath.Lib] p≠qとp∤mのとき、sᵖ=qᵐの任意の根はq上の慣性に動かされる。
有限分解体で慣性が根を固定すると分岐指数が1となり、主イデアルの素因数重複度からp∣mが出る。
有限慣性元の持ち上げと付値環の共役によって、指定された同じ付値環Aでの結論へ戻す。 -/
theorem exists_inertia_ne_of_pow_eq {q : ℕ} (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : LiesOverPrime A q) {p m : ℕ} (hq : q.Prime) (hp : p.Prime) (hpq : p ≠ q) (hm : ¬ p ∣ m)
    {s : AlgebraicClosure ℚ} (hs : s ^ p = (q : AlgebraicClosure ℚ) ^ m) :
    ∃ τ ∈ inertiaSubgroupIn A ℚ, τ s ≠ s := by
  have hqne : (q : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, zero_pow hp.ne_zero] at hs
    exact pow_ne_zero m hqne hs.symm
  -- 第1段階：同じ根sを含む有限分解体とq上の素点を取る。
  set L := kumField q p m with hLdef
  have : FiniteDimensional ℚ L := inferInstanceAs (FiniteDimensional ℚ (kumField q p m))
  have hNorm : Normal ℚ L := inferInstanceAs (Normal ℚ (kumField q p m))
  have : IsGalois ℚ L := inferInstanceAs (IsGalois ℚ (kumField q p m))
  have : NumberField L := inferInstanceAs (NumberField (kumField q p m))
  have hfne : kumPoly q p m ≠ 0 := Polynomial.X_pow_sub_C_ne_zero hp.pos _
  have hroot : ∀ r : AlgebraicClosure ℚ, r ^ p = (q : AlgebraicClosure ℚ) ^ m →
      r ∈ (kumPoly q p m).rootSet (AlgebraicClosure ℚ) := by
    intro r hr
    rw [Polynomial.mem_rootSet]
    refine ⟨hfne, ?_⟩
    rw [kumPoly, map_sub, Polynomial.aeval_X_pow, Polynomial.aeval_C, hr]
    rw [map_pow]
    simp
  have hsL : s ∈ L := IntermediateField.subset_adjoin ℚ _ (hroot s hs)
  set shat : L := ⟨s, hsL⟩ with hshat
  have hshat0 : shat ≠ 0 := by
    intro h
    exact hs0 (by simpa [hshat] using congrArg (Subtype.val) h)
  have hshatpow : shat ^ p = (q : L) ^ m := by
    apply Subtype.coe_injective
    push_cast
    exact hs
  have hmaxq : (Ideal.span {(q : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hq).irreducible
  obtain ⟨Q, hQmax, hQover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := NumberField.RingOfIntegers L)
      (Ideal.span {(q : ℤ)})
  have := hQmax
  have := hQover
  have hqQ : (q : NumberField.RingOfIntegers L) ∈ Q := by
    have hqspan : (q : ℤ) ∈ Ideal.span {(q : ℤ)} := Ideal.subset_span rfl
    have := hQover.over ▸ hqspan
    rw [Ideal.mem_comap] at this
    simpa using this
  have hqQne : (q : NumberField.RingOfIntegers L) ≠ 0 := by
    intro h
    have : ((q : NumberField.RingOfIntegers L) : L) = 0 := by rw [h]; simp
    exact (Nat.cast_ne_zero.mpr hq.ne_zero : (q : L) ≠ 0) this
  have hQ0 : Q ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hqQ
    exact hqQne hqQ
  -- 相異なる素数p,qのBezout等式をQへ写し、pが剰余体で零でないことを示す。
  have hpnotQ : (p : NumberField.RingOfIntegers L) ∉ Q := by
    intro hpQ
    have hnd : ¬ (q : ℤ) ∣ (p : ℤ) := by
      intro hd
      rcases (Nat.dvd_prime hp).mp (Int.natCast_dvd_natCast.mp hd) with h | h
      · exact hq.ne_one h
      · exact hpq h.symm
    obtain ⟨u, v, huv⟩ := ((Nat.prime_iff_prime_int.mp hq).coprime_iff_not_dvd.mpr hnd).map
      (Int.castRingHom (NumberField.RingOfIntegers L))
    simp only [Int.coe_castRingHom, Int.cast_natCast] at huv
    have h1Q : (1 : NumberField.RingOfIntegers L) ∈ Q := by
      rw [← huv]
      exact Q.add_mem (Ideal.mul_mem_left _ _ hqQ) (Ideal.mul_mem_left _ _ hpQ)
    exact hQmax.ne_top ((Ideal.eq_top_iff_one Q).mpr h1Q)
  -- 主イデアルを比較するため、sを同じ体の整数環へ戻す。
  have hsint : IsIntegral ℤ shat := by
    refine ⟨Polynomial.X ^ p - Polynomial.C ((q : ℤ) ^ m),
      Polynomial.monic_X_pow_sub_C _ hp.ne_zero, ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, hshatpow, map_pow,
      map_natCast, sub_self]
  set shatO : NumberField.RingOfIntegers L := ⟨shat, hsint⟩ with hshatO
  have hshatOpow : shatO ^ p = (q : NumberField.RingOfIntegers L) ^ m := by
    apply Subtype.ext
    change shat ^ p = (q : L) ^ m
    exact hshatpow
  by_contra hall
  push Not at hall
  have hclaim : ∃ τbar : L ≃ₐ[ℚ] L, τbar ∈ Q.inertia (L ≃ₐ[ℚ] L) ∧ τbar shat ≠ shat := by
    by_contra hfin
    push Not at hfin
    -- 第2段階：慣性の剰余合同とpの非消滅から、1のp乗根は固定される。
    have hζfix : ∀ τbar : L ≃ₐ[ℚ] L, τbar ∈ Q.inertia (L ≃ₐ[ℚ] L) →
        ∀ ζ : L, ζ ^ p = 1 → τbar ζ = ζ := by
      intro τbar hτbar ζ hζp
      have hζint : IsIntegral ℤ ζ := by
        refine ⟨Polynomial.X ^ p - Polynomial.C (1 : ℤ),
          Polynomial.monic_X_pow_sub_C _ hp.ne_zero, ?_⟩
        rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, hζp, map_one,
          sub_self]
      set ζO : NumberField.RingOfIntegers L := ⟨ζ, hζint⟩ with hζO
      have hζOpow : ζO ^ p = 1 := by
        apply Subtype.ext
        change ζ ^ p = 1
        exact hζp
      have hmem := AddSubgroup.mem_inertia.mp hτbar ζO
      have hsmulcoe : ((τbar • ζO : NumberField.RingOfIntegers L) : L) = τbar ζ := rfl
      set ζ' : NumberField.RingOfIntegers L := (τbar • ζO) * ζO ^ (p - 1) with hζ'
      have hζζ : ζO * ζO ^ (p - 1) = 1 := by
        rw [← pow_succ', Nat.sub_add_cancel hp.one_le]
        exact hζOpow
      have hζ'pow : ζ' ^ p = 1 := by
        have h1 : (τbar • ζO) ^ p = 1 := by
          rw [← smul_pow', hζOpow, smul_one]
        rw [hζ', mul_pow, h1, one_mul, ← pow_mul, mul_comm (p - 1) p, pow_mul, hζOpow,
          one_pow]
      have hζ'sub : ζ' - 1 = (τbar • ζO - ζO) * ζO ^ (p - 1) := by
        rw [hζ', sub_mul, hζζ]
      have hζ'Q : ζ' - 1 ∈ Q := by
        rw [hζ'sub]
        exact Ideal.mul_mem_right _ _ hmem
      by_cases hζ'1 : ζ' = 1
      · have hτζ : τbar • ζO = ζO := by
          have key : τbar • ζO = ζ' * ζO := by
            rw [hζ', mul_assoc, mul_comm (ζO ^ (p - 1)) ζO, hζζ, mul_one]
          rw [key, hζ'1, one_mul]
        calc τbar ζ = ((τbar • ζO : NumberField.RingOfIntegers L) : L) := hsmulcoe.symm
          _ = ((ζO : NumberField.RingOfIntegers L) : L) := by rw [hτζ]
          _ = ζ := rfl
      · exfalso
        have hpfact := ValuationInertiaPower.natCast_eq_one_sub_mul_sum hζ'pow hζ'1
        have hpQ : ((p : ℕ) : NumberField.RingOfIntegers L) ∈ Q := by
          rw [hpfact]
          refine Ideal.mul_mem_right _ _ ?_
          have : (1 : NumberField.RingOfIntegers L) - ζ' = -(ζ' - 1) := by ring
          rw [this]
          exact Q.neg_mem hζ'Q
        exact hpnotQ hpQ
    -- 他の根rもr/sが1のp乗根なので固定され、分解体全体の作用が恒等になる。
    have hfixall : ∀ τbar : L ≃ₐ[ℚ] L, τbar ∈ Q.inertia (L ≃ₐ[ℚ] L) → τbar = 1 := by
      intro τbar hτbar
      have hsfix : τbar shat = shat := hfin τbar hτbar
      have hroots : ∀ r (hr : r ∈ (kumPoly q p m).rootSet (AlgebraicClosure ℚ)),
          τbar ⟨r, IntermediateField.subset_adjoin ℚ _ hr⟩
            = ⟨r, IntermediateField.subset_adjoin ℚ _ hr⟩ := by
        intro r hr
        set rhat : L := ⟨r, IntermediateField.subset_adjoin ℚ _ hr⟩ with hrhat
        have hrpow : rhat ^ p = (q : L) ^ m := by
          apply Subtype.coe_injective
          push_cast [hrhat]
          have := (Polynomial.mem_rootSet.mp hr).2
          rw [kumPoly, map_sub, Polynomial.aeval_X_pow, Polynomial.aeval_C] at this
          have hqm : (algebraMap ℚ (AlgebraicClosure ℚ)) ((q:ℚ) ^ m)
              = (q : AlgebraicClosure ℚ) ^ m := by
            rw [map_pow, map_natCast]
          rw [hqm] at this
          exact sub_eq_zero.mp this
        have hζpow : (rhat * shat⁻¹) ^ p = 1 := by
          rw [mul_pow, hrpow, inv_pow, hshatpow, mul_inv_eq_one₀]
          exact pow_ne_zero m (Nat.cast_ne_zero.mpr hq.ne_zero)
        have hζ := hζfix τbar hτbar (rhat * shat⁻¹) hζpow
        calc τbar rhat = τbar (rhat * shat⁻¹ * shat) := by
              rw [inv_mul_cancel_right₀ hshat0]
          _ = τbar (rhat * shat⁻¹) * τbar shat := map_mul τbar _ _
          _ = rhat * shat⁻¹ * shat := by rw [hζ, hsfix]
          _ = rhat := inv_mul_cancel_right₀ hshat0 _
      have hhom : (τbar : L →ₐ[ℚ] L) = AlgHom.id ℚ L :=
        IntermediateField.adjoin_algHom_ext ℚ fun r hr => hroots r hr
      exact AlgEquiv.ext fun x => DFunLike.congr_fun hhom x
    have hbot : Q.inertia (L ≃ₐ[ℚ] L) = ⊥ :=
      (Subgroup.eq_bot_iff_forall _).mpr hfixall
    have hcard : Nat.card (Q.inertia (L ≃ₐ[ℚ] L)) = 1 := by
      rw [hbot]
      exact Subgroup.card_bot
    -- 第3段階：有限剰余体の完全性を供給し、慣性群位数＝分岐指数を使う。
    let : Field (ℤ ⧸ Ideal.span {(q:ℤ)}) := Ideal.Quotient.field _
    let : Field (NumberField.RingOfIntegers L ⧸ Q) := Ideal.Quotient.field Q
    let : NeZero q := ⟨hq.ne_zero⟩
    have : Finite (ℤ ⧸ Ideal.span {(q:ℤ)}) :=
      Finite.of_equiv _ (Int.quotientSpanEquivZMod q).symm.toEquiv
    have : PerfectField (ℤ ⧸ Ideal.span {(q:ℤ)}) := PerfectField.ofFinite
    have : Algebra.IsIntegral (ℤ ⧸ Ideal.span {(q:ℤ)}) (NumberField.RingOfIntegers L ⧸ Q) :=
      Ideal.Quotient.algebra_isIntegral_of_liesOver Q (Ideal.span {(q:ℤ)})
    have : Algebra.IsSeparable (ℤ ⧸ Ideal.span {(q:ℤ)}) (NumberField.RingOfIntegers L ⧸ Q) :=
      inferInstance
    have hcountq : (UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span {(q : NumberField.RingOfIntegers L)})).count Q = 1 := by
      have hmap : Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers L))
          (Ideal.span {(q:ℤ)}) = Ideal.span {(q : NumberField.RingOfIntegers L)} := by
        rw [Ideal.map_span]
        simp
      have hmapne : Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers L))
          (Ideal.span {(q:ℤ)}) ≠ ⊥ := by
        rw [hmap]
        intro h
        rw [Ideal.span_singleton_eq_bot] at h
        exact hqQne h
      rw [← hmap]
      rw [← Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hmapne
        inferInstance hQ0]
      rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ (by simp [hq.ne_zero])]
      rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(q:ℤ)}) Q (L ≃ₐ[ℚ] L)]
      rw [← Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[ℚ] L) (Ideal.span {(q:ℤ)}) Q]
      exact hcard
    -- 第4段階：(s)^p=(q)^mのQ重複度を比較するとp∣mとなる。
    have hspan : Ideal.span {shatO} ^ p = Ideal.span {(q : NumberField.RingOfIntegers L)} ^ m := by
      rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow, hshatOpow]
    have hcounts : p * (UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span {shatO})).count Q = m * (UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span {(q : NumberField.RingOfIntegers L)})).count Q := by
      have hc := congrArg
        (fun I => (UniqueFactorizationMonoid.normalizedFactors I).count Q) hspan
      simpa [UniqueFactorizationMonoid.normalizedFactors_pow, Multiset.count_nsmul] using hc
    rw [hcountq, mul_one] at hcounts
    exact hm ⟨_, hcounts.symm⟩
  obtain ⟨τbar, hτbar, hτbarne⟩ := hclaim
  -- 第5段階：有限慣性元を持ち上げ、まずあるq上の付値環で動くことを得る。
  obtain ⟨σ, hres, 𝔔, h𝔔max, hq𝔔, hσ𝔔⟩ :=
    IntegralClosureInertiaLift.exists_lift_mem_inertia_integralClosure L Q (q := q)
      (by exact_mod_cast hqQ) τbar hτbar
  have := h𝔔max
  obtain ⟨A₁, hA₁, hσA₁⟩ :=
    ValuationInertiaLift.exists_valuation_inertia_of_integral_congruence 𝔔 hq hq𝔔 σ hσ𝔔
  have hσs : σ s ≠ s := by
    have happ : (AlgEquiv.restrictNormalHom L σ shat : AlgebraicClosure ℚ) = σ s :=
      @AlgEquiv.restrictNormalHom_apply ℚ _ _ _ _ L hNorm σ shat
    rw [hres] at happ
    intro heq
    apply hτbarne
    apply Subtype.coe_injective
    change ((τbar shat : L) : AlgebraicClosure ℚ) = ((shat : L) : AlgebraicClosure ℚ)
    rw [happ, heq]
  -- Aへ共役を戻す。g(s)/sという枝の比が慣性固定なので同じsが動く。
  obtain ⟨g, hg⟩ :=
    ValuationPlaceConjugacy.exists_smul_eq hq hA hA₁
  have hθ : g⁻¹ * σ * g ∈ inertiaSubgroupIn A ℚ := by
    have h1 : g⁻¹ * σ * (g⁻¹)⁻¹ ∈ inertiaSubgroupIn (g⁻¹ • A₁) ℚ :=
      ValuationPlaceConjugacy.conj_mem_inertia_smul A₁ g⁻¹ σ hσA₁
    rw [inv_inv] at h1
    rw [← hg, inv_smul_smul] at h1
    exact h1
  have hθs : (g⁻¹ * σ * g) s = s := hall _ hθ
  have hσgs : σ (g s) = g s := by
    have h1 : g⁻¹ (σ (g s)) = s := by
      have := hθs
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply] at this
      exact this
    have h2 := congrArg g h1
    rw [AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply] at h2
    exact h2
  have hgs_pow : (g s) ^ p = (q : AlgebraicClosure ℚ) ^ m := by
    rw [← map_pow, hs, map_pow, map_natCast]
  have hζ2pow : (g s / s) ^ p = 1 := by
    rw [div_pow, hgs_pow, hs, div_self]
    exact pow_ne_zero m hqne
  have hζ2fix : σ (g s / s) = g s / s := by
    have hvq : A₁.valuation (q : AlgebraicClosure ℚ) < 1 :=
      (ValuationSubring.mem_nonunits_iff A₁).mp hA₁
    have hpunit : A₁.valuation (p : AlgebraicClosure ℚ) = 1 :=
      ValuationPrimeSupport.valuation_intCast_eq_one_of_not_dvd A₁ hq hvq (by
        intro hd
        rcases (Nat.dvd_prime hp).mp (Int.natCast_dvd_natCast.mp hd) with h | h
        · exact hq.ne_one h
        · exact hpq h.symm)
    exact ValuationInertiaPower.inertia_fixed_of_pow_eq_one A₁ ℚ hp.ne_zero hpunit σ hσA₁ hζ2pow
  have hgs_eq : g s = (g s / s) * s := (div_mul_cancel₀ _ hs0).symm
  have hζ2ne : (g s / s) ≠ 0 := by
    intro h
    rw [h, zero_pow hp.ne_zero] at hζ2pow
    exact zero_ne_one hζ2pow
  apply hσs
  have hσgs' : σ (g s / s) * σ s = (g s / s) * s := by
    rw [← map_mul, ← hgs_eq]
    exact hσgs
  rw [hζ2fix] at hσgs'
  exact mul_left_cancel₀ hζ2ne hσgs'

/-- [DkMath.Lib] 冪の付値がqᵐの付値に等しく、p∤mなら、慣性は元tを動かす。
等式tᵖ=qᵐそのものは不要。tᵖ/qᵐのp乗根wを取り、v(w)=1を示す。
全慣性がtを固定すると単元の冪の剛性からwも固定するため、
s=t/wが固定されたKummer根となり、前定理に反する。 -/
theorem exists_inertia_ne_of_valuation_pow_eq {q p m : ℕ}
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hq : q.Prime) (hp : p.Prime) (hpq : p ≠ q) (hm : ¬ p ∣ m)
    {t : AlgebraicClosure ℚ}
    (hdepth : A.valuation t ^ p = A.valuation (q : AlgebraicClosure ℚ) ^ m) :
    ∃ τ ∈ inertiaSubgroupIn A ℚ, τ t ≠ t := by
  have hq0 : (q : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  have hvq0 : A.valuation (q : AlgebraicClosure ℚ) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr hq0
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, _root_.map_zero, zero_pow hp.ne_zero] at hdepth
    exact pow_ne_zero m hvq0 hdepth.symm
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (t ^ p / (q : AlgebraicClosure ℚ) ^ m) hp.pos
  have hvw : A.valuation w = 1 := by
    apply pow_left_injective (M := A.ValueGroup) hp.ne_zero
    change A.valuation w ^ p = 1 ^ p
    rw [← map_pow, hw, one_pow, map_div₀, map_pow, map_pow, hdepth,
      div_self (pow_ne_zero m hvq0)]
  have hwp : (t / w) ^ p = (q : AlgebraicClosure ℚ) ^ m := by
    rw [div_pow, hw, div_div_eq_mul_div, mul_comm, mul_div_assoc,
      div_self (pow_ne_zero p ht0), mul_one]
  have hpunit : A.valuation (p : AlgebraicClosure ℚ) = 1 :=
    ValuationPrimeSupport.valuation_intCast_eq_one_of_not_dvd A hq
      ((ValuationSubring.mem_nonunits_iff A).mp hA) (by
        intro hd
        rcases (Nat.dvd_prime hp).mp (Int.natCast_dvd_natCast.mp hd) with h | h
        · exact hq.ne_one h
        · exact hpq h.symm)
  obtain ⟨τ, hτ, hτs⟩ := exists_inertia_ne_of_pow_eq A hA hq hp hpq hm hwp
  refine ⟨τ, hτ, fun ht => hτs ?_⟩
  have hfixpow : τ (w ^ p) = w ^ p := by
    rw [hw, map_div₀, map_pow, map_pow, ht, map_natCast]
  have hfixw := ValuationInertiaPower.inertia_fixed_of_unit_pow A ℚ hp.ne_zero hpunit τ hτ hvw hfixpow
  rw [map_div₀, ht, hfixw]

/-- [DkMath.Lib] 逆向きの読み方：全慣性に固定される元の深さの分子はpの倍数。
付値環を固定したままの必要条件であり、逆の十分条件は主張しない。 -/
theorem dvd_depth_of_inertia_fixed {q p m : ℕ}
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hq : q.Prime) (hp : p.Prime) (hpq : p ≠ q) {t : AlgebraicClosure ℚ}
    (hdepth : A.valuation t ^ p = A.valuation (q : AlgebraicClosure ℚ) ^ m)
    (hfix : ∀ τ ∈ inertiaSubgroupIn A ℚ, τ t = t) : p ∣ m := by
  by_contra hm
  obtain ⟨τ, hτ, hne⟩ := exists_inertia_ne_of_valuation_pow_eq A hA hq hp hpq hm hdepth
  exact hne (hfix τ hτ)


end
end DkMath.Lib.NumberTheory.KummerInertia
