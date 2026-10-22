/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: ../Lib/NumberTheory/RegularKummer/LICENSE
Upstream notices: ../Lib/NumberTheory/RegularKummer/ANTHROPIC-NOTICE
Adapted from S_FreyPackage_frey_exists_p_torsion_integral_abscissa_of_stable_line.lean,
blob aa678c2894fcf3bab25d6a4bd9e4a7878dd58eb5.
Modified: actual DkMath Source, nsmul kernel, representation and existing integer model;
reuse single-slope lemma and previously proved valuation support and torsion cardinality.
-/

import DkMath.FLT.FreyValuationArithmetic
import DkMath.FLT.FreyResidualRankTwo
import DkMath.Lib.Algebra.SingleSlopeRoot
import Mathlib.FieldTheory.Galois.Infinite

#print "file: DkMath.FLT.FreyIntegralTorsionWitness"

/-!
# NOTE-031-004C: 安定直線の存在から、整な有限p捩れ点の存在へ

全有限p捩れ点が極を持つと仮定する。整モデルのp除法多項式は次数d=(p²-1)/2、
最高係数pであり、整数係数の付値の二分から全根はv(x)^d v(p)=1を満たす。
一方、安定直線の非零点のx座標を集めた軌道多項式gは有理係数で次数がp-1以下。
有理係数の付値はv(p)の整数冪なので、次数差がd未満の異なる項の付値は一致しない。
唯一の最大項を持つgはその根で零になれず、矛盾する。
この証明は良還元・悪い還元の両方に使う。点が安定直線自身に属するという結論には
強めない。Sourceの同じ実際のE[p]内に、有限な整x座標の点を得る。
-/
namespace DkMath.FLT.Frey.Source
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point Polynomial
open DkMath.Lib.NumberTheory EllipticTorsionRepresentation ValuationInertia ValuationPrimeSupport
open DkMath.Lib.RepresentationTheory
local notation "Kb" => AlgebraicClosure ℚ
noncomputable local instance instDecidableEqFreyIntegralTorsionWitness : DecidableEq Kb := Classical.decEq _

private theorem integer_gap {K : Type*} [Field K] (A : ValuationSubring K) {q : ℕ}
    (hq : q.Prime) (hA : LiesOverPrime A q) (m : ℤ) :
    A.valuation (m : K) = 1 ∨ A.valuation (m : K) ≤ A.valuation (q : K) := by
  by_cases hd : (q : ℤ) ∣ m
  · obtain ⟨k, rfl⟩ := hd
    right
    rw [Int.cast_mul, Int.cast_natCast, map_mul]
    exact mul_le_of_le_one_right' ((A.valuation_le_one_iff _).mpr (intCast_mem A k))
  · exact Or.inl (valuation_intCast_eq_one_of_not_dvd A hq
      ((ValuationSubring.mem_nonunits_iff _).mp hA) hd)

private theorem rational_value_powers {K : Type*} [Field K] [CharZero K] (A : ValuationSubring K)
    {q : ℕ} (hq : q.Prime) (hA : LiesOverPrime A q) (c : ℚ) (hc : c ≠ 0) :
    ∃ a b : ℕ, A.valuation (c : K) * A.valuation (q : K) ^ b = A.valuation (q : K) ^ a := by
  have hqv := (ValuationSubring.mem_nonunits_iff _).mp hA
  refine ⟨padicValInt q c.num, padicValInt q (c.den : ℤ), ?_⟩
  rw [← valuation_intCast_eq_pow_padicValInt A hq hqv (Rat.num_ne_zero.mpr hc),
    ← valuation_intCast_eq_pow_padicValInt A hq hqv (by exact_mod_cast c.den_nz)]
  rw [← map_mul, Rat.cast_def]
  push_cast
  rw [div_mul_cancel₀ _ (by exact_mod_cast c.den_nz)]

private noncomputable def absc {F : Type*} [Field F] {W : Affine F} : W.Point → F
  | .zero => 0
  | .some x _ _ => x

variable {p : ℕ} [Fact p.Prime] (S : Source p)

omit [Fact p.Prime] in
/-- 同じ整数モデルの除法多項式の係数は、代数閉包へ移しても同じ整数の像である。 -/
theorem coeff_prePsi_baseChange (n j : ℕ) :
    ((S.rationalCurve.baseChange Kb).preΨ' n).coeff j = ((S.curve.preΨ' n).coeff j : Kb) := by
  have hc : S.rationalCurve.baseChange Kb = S.curve.map (Int.castRingHom Kb) := by
    rw [← S.curve_map, WeierstrassCurve.baseChange, WeierstrassCurve.map_map]
    congr 1
  rw [hc, WeierstrassCurve.map_preΨ', coeff_map, eq_intCast]

omit [Fact p.Prime] in
private theorem prePsi_torsion_iff (hn : Odd p) {x y : Kb}
    (h : (S.rationalCurve.baseChange Kb).toAffine.Nonsingular x y) :
    p • (Point.some x y h : (S.rationalCurve.baseChange Kb).toAffine.Point) = 0 ↔
      ((S.rationalCurve.baseChange Kb).preΨ' p).eval x = 0 := by
  let W := S.rationalCurve.baseChange Kb
  have hh := EllipticDivision.WeierstrassCurve.smul_eq_zero_iff_evalEval_ψ W h (p : ℤ)
  calc p • (Point.some x y h : W.toAffine.Point) = 0
      ↔ (W.ψ (p : ℤ)).evalEval x y = 0 := by simpa only [natCast_zsmul] using hh
    _ ↔ (W.ψ (p : ℤ)).evalEval x y ^ 2 = 0 := (sq_eq_zero_iff).symm
    _ ↔ (W.preΨ' p).eval x = 0 := by
      rw [EllipticDivision.WeierstrassCurve.evalEval_ψ_sq W h.1,
        WeierstrassCurve.ΨSq_ofNat, ite_eq_right (Nat.not_even_iff_odd.mpr hn),
        mul_one, eval_pow, sq_eq_zero_iff]

/-- 全ガロア安定な真の非零直線があれば、同じE[p]に整な有限x座標を持つ点が存在する。
剰余標数pでは全torsion点の整性を仮定できないため、この存在証明を別に供給する。 -/
theorem exists_integral_torsion_of_stable_line (hp5 : 5 ≤ p)
    (A : ValuationSubring Kb) (hA : LiesOverPrime A p)
    (N : Submodule (ZMod p) S.ResidualSpace) (hN : IsStable S.residualRepresentation N)
    (hbot : N ≠ ⊥) (htop : N ≠ ⊤) :
    ∃ (t : S.ResidualSpace) (x y : Kb) (h : (S.rationalCurve.baseChange Kb).toAffine.Nonsingular x y),
      t.val = Point.some x y h ∧ x ∈ A := by
  classical
  by_contra hcon
  push Not at hcon
  have hp : p.Prime := Fact.out
  have hp5 := hp5
  have hodd : Odd p := (Nat.Prime.odd_of_ne_two hp (by omega))
  have hneven : ¬ Even p := Nat.not_even_iff_odd.mpr hodd
  have hpK : ((p : ℕ) : Kb) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have := S.rationalCurve_isElliptic
  have : (S.rationalCurve⁄Kb).IsElliptic := by
    change (S.rationalCurve.map (algebraMap ℚ Kb)).IsElliptic
    infer_instance
  have hvp1 : A.valuation ((p : ℕ) : Kb) < 1 := A.mem_nonunits_iff.mp hA
  have hvp0 : A.valuation ((p : ℕ) : Kb) ≠ 0 := (Valuation.ne_zero_iff _).mpr hpK
  have hvp0' : 0 < A.valuation ((p : ℕ) : Kb) := zero_lt_iff.mpr hvp0
  set f : Polynomial Kb := (S.rationalCurve⁄Kb).preΨ' p with hf
  set d : ℕ := (p ^ 2 - 1) / 2 with hd
  have hdeg : f.natDegree = d := by
    rw [hf, (S.rationalCurve⁄Kb).natDegree_preΨ' hpK, ite_eq_right hneven]
  have hlead : f.leadingCoeff = ((p : ℕ) : Kb) := by
    rw [hf, (S.rationalCurve⁄Kb).leadingCoeff_preΨ' hpK, ite_eq_right hneven]
  have hf0 : f ≠ 0 := (S.rationalCurve⁄Kb).preΨ'_ne_zero hpK
  have hroots : ∀ r ∈ f.roots, 1 < A.valuation r := by
    intro r hr
    have hev : f.eval r = 0 := (Polynomial.mem_roots hf0).mp hr
    set b₁ : Kb := (S.rationalCurve⁄Kb).a₁ * r + (S.rationalCurve⁄Kb).a₃ with hb₁
    set c₁ : Kb := -(r ^ 3 + (S.rationalCurve⁄Kb).a₂ * r ^ 2 + (S.rationalCurve⁄Kb).a₄ * r
      + (S.rationalCurve⁄Kb).a₆) with hc₁
    obtain ⟨y, hy⟩ : ∃ y : Kb, IsRoot (C 1 * X ^ 2 + C b₁ * X + C c₁) y :=
      IsAlgClosed.exists_root _ (by rw [Polynomial.degree_quadratic one_ne_zero]; decide)
    have heq : (S.rationalCurve⁄Kb).toAffine.Equation r y := by
      rw [WeierstrassCurve.Affine.equation_iff]
      have := hy
      simp only [IsRoot.def, eval_add, eval_mul, eval_C, eval_pow, eval_X, one_mul] at this
      rw [hb₁, hc₁] at this
      linear_combination this
    have hns : (S.rationalCurve⁄Kb).toAffine.Nonsingular r y :=
      ((S.rationalCurve⁄Kb).toAffine.equation_iff_nonsingular).mp heq
    have htor : p • (Point.some r y hns : (S.rationalCurve⁄Kb).Point) = 0 :=
      (prePsi_torsion_iff S hodd
        hns).mpr hev
    have hnotA : r ∉ A := hcon ⟨_, htor⟩ r y hns rfl
    exact not_le.mp fun hle => hnotA ((A.valuation_le_one_iff _).mp hle)
  have hslope : ∀ r ∈ f.roots,
      A.valuation r ^ d * A.valuation ((p : ℕ) : Kb) = 1 := by
    intro r hr
    have hmain := DkMath.Lib.Algebra.SingleSlopeRoot.root_pow_natDegree_mul_leadingCoeff_eq_one A.valuation (f := f)
      (Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits f))
      (fun j => by
        rw [hf, S.coeff_prePsi_baseChange]
        exact (A.valuation_le_one_iff _).mpr (intCast_mem A _))
      (fun j => by
        rw [hlead, hf, S.coeff_prePsi_baseChange]
        exact integer_gap A hp hA _)
      hroots hr
    rwa [hdeg, hlead, map_mul, map_pow] at hmain
  obtain ⟨T₀, hT₀N, hT₀0⟩ := (Submodule.ne_bot_iff N).mp hbot
  obtain ⟨x₀, y₀, h₀, hT₀eq⟩ : ∃ (x₀ y₀ : Kb) (h₀ : (S.rationalCurve⁄Kb).toAffine.Nonsingular x₀ y₀),
      (T₀.val : (S.rationalCurve⁄Kb).Point) = Point.some x₀ y₀ h₀ := by
    rcases hT : (T₀.val : (S.rationalCurve⁄Kb).Point) with _ | ⟨x₀, y₀, h₀⟩
    · exact absurd (Subtype.ext hT) hT₀0
    · exact ⟨x₀, y₀, h₀, rfl⟩
  have hx₀root : x₀ ∈ f.roots := by
    refine (Polynomial.mem_roots hf0).mpr ?_
    have htor : p • (T₀.val : (S.rationalCurve⁄Kb).Point) = 0 := T₀.property
    rw [hT₀eq] at htor
    exact (prePsi_torsion_iff S
      hodd h₀).mp htor
  have hx₀A : x₀ ∉ A := hcon T₀ x₀ y₀ h₀ hT₀eq
  have hx₀0 : x₀ ≠ 0 := fun h => hx₀A (h ▸ A.zero_mem)
  have hvx₀ : A.valuation x₀ ^ d * A.valuation ((p : ℕ) : Kb) = 1 := hslope x₀ hx₀root
  have hvx₀0 : A.valuation x₀ ≠ 0 := (Valuation.ne_zero_iff _).mpr hx₀0
  have hcardT : Nat.card (Torsion S.rationalCurve p) = p ^ 2 :=
    card_torsion_prime_sq S.rationalCurve p
  have hfinT : Finite (Torsion S.rationalCurve p) :=
    Nat.finite_of_card_ne_zero (by rw [hcardT]; exact pow_ne_zero _ hp.ne_zero)
  have hcardN : Nat.card N ≤ p := by
    have hdvd : Nat.card N ∣ p ^ 2 := by
      rw [← hcardT]
      exact AddSubgroup.card_addSubgroup_dvd_card N.toAddSubgroup
    obtain ⟨z, hzN⟩ : ∃ z : Torsion S.rationalCurve p, z ∉ N := by
      by_contra hall
      push Not at hall
      exact htop (Submodule.eq_top_iff'.mpr hall)
    have hlt : Nat.card N < p ^ 2 := by
      rw [← hcardT]
      exact Finite.card_subtype_lt (p := fun z => z ∈ N) hzN
    obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hk2 : k ≠ 2 := by
      rintro rfl
      exact (lt_irrefl _) (hkeq ▸ hlt)
    have hk1 : k ≤ 1 := by omega
    rw [hkeq]
    calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hk1
      _ = p := pow_one _
  have : Fintype N := Fintype.ofFinite N
  set Xs : Finset Kb := ((Finset.univ : Finset N).filter (fun T : N => T ≠ 0)).image
    (fun T : N => absc (W := S.rationalCurve⁄Kb) T.1.1) with hS
  have hScard : Xs.card ≤ p - 1 := by
    refine (Finset.card_image_le).trans ?_
    rw [Finset.filter_ne' Finset.univ (0 : N), Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, ← Nat.card_eq_fintype_card]
    omega
  have hx₀S : x₀ ∈ Xs := by
    rw [hS, Finset.mem_image]
    refine ⟨⟨T₀, hT₀N⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · intro h0
      exact hT₀0 (congrArg Subtype.val h0)
    · change absc T₀.1 = x₀
      have : T₀.1 = Point.some x₀ y₀ h₀ := hT₀eq
      rw [this]
      rfl
  have absc_smul : ∀ (σ : Kb ≃ₐ[ℚ] Kb) (Q : (S.rationalCurve⁄Kb).Point), absc (pointAction S.rationalCurve σ Q) = σ (absc Q) := by
    intro σ Q
    rcases Q with _ | ⟨x, y, h⟩
    · change absc (pointAction S.rationalCurve σ (0 : (S.rationalCurve⁄Kb).Point)) = σ 0
      rw [_root_.map_zero]
      rfl
    · rfl
  have hSstab : ∀ σ : Kb ≃ₐ[ℚ] Kb, Xs.image σ = Xs := by
    intro σ
    apply Finset.eq_of_subset_of_card_le
    · intro s hs
      rw [Finset.mem_image] at hs
      obtain ⟨s', hs', rfl⟩ := hs
      rw [hS, Finset.mem_image] at hs' ⊢
      obtain ⟨T, hT, rfl⟩ := hs'
      have hT0 : T ≠ 0 := (Finset.mem_filter.mp hT).2
      refine ⟨⟨S.residualRepresentation σ T.1, hN σ _ T.2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · intro h0
        apply hT0
        have h1 : S.residualRepresentation σ T.1 = 0 := congrArg Subtype.val h0
        have h2 : T.1 = 0 := by
          apply (S.residualRepresentation.apply_bijective σ).injective
          exact h1.trans (_root_.map_zero _).symm
        exact Subtype.ext h2
      · exact absc_smul σ T.1.1
    · rw [Finset.card_image_of_injective _ σ.injective]
  set g : Polynomial Kb := ∏ s ∈ Xs, (X - C s) with hg
  have hgmonic : g.Monic := monic_prod_X_sub_C id Xs
  have hgdeg : g.natDegree = Xs.card := natDegree_finsetProd_X_sub_C_eq_card Xs id
  have hgx₀ : g.eval x₀ = 0 := by
    rw [hg, eval_prod]
    exact Finset.prod_eq_zero hx₀S (by simp)
  have hgmap : ∀ σ : Kb ≃ₐ[ℚ] Kb, g.map (σ : Kb →+* Kb) = g := by
    intro σ
    rw [hg, Polynomial.map_prod]
    simp only [Polynomial.map_sub, map_X, map_C]
    have hinj : ∀ x ∈ Xs, ∀ y ∈ Xs, (σ : Kb →+* Kb) x = (σ : Kb →+* Kb) y → x = y :=
      fun x _ y _ hxy => σ.injective hxy
    rw [← Finset.prod_image (g := (σ : Kb →+* Kb)) (f := fun s => X - C s) hinj]
    have : Xs.image (σ : Kb →+* Kb) = Xs := by
      have h := hSstab σ
      convert h using 2
      rfl
    rw [this]
  have : IsGalois ℚ Kb := by
    have h : @IsGalois ℚ _ Kb _ (AlgebraicClosure.instAlgebra ℚ) := inferInstance
    exact h
  have hcoeffQ : ∀ i, ∃ c : ℚ, (c : Kb) = g.coeff i := by
    intro i
    have hfix : ∀ σ : Kb ≃ₐ[ℚ] Kb, σ (g.coeff i) = g.coeff i := by
      intro σ
      have := congrArg (fun q : Polynomial Kb => q.coeff i) (hgmap σ)
      simp only [Polynomial.coeff_map] at this
      exact this
    obtain ⟨c, hc⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := ℚ) (g.coeff i)).mpr
      hfix
    exact ⟨c, by rw [← hc]; exact (eq_ratCast _ c).symm⟩
  have hdS : Xs.card < d := by
    obtain ⟨k, hk⟩ := hodd
    have hsq : (2 * k + 1) ^ 2 = 2 * (2 * k ^ 2 + 2 * k) + 1 := by ring
    have hd' : d = 2 * k ^ 2 + 2 * k := by
      rw [hd, hk, hsq, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    have hk2 : 2 ≤ k := by omega
    have h1 : Xs.card ≤ 2 * k := by omega
    have h2 : 2 * k < 2 * k ^ 2 + 2 * k := by nlinarith
    omega
  have hterm_ne : ∀ i j : ℕ, i < j → j ≤ Xs.card → g.coeff i ≠ 0 → g.coeff j ≠ 0 →
      A.valuation (g.coeff i * x₀ ^ i) ≠ A.valuation (g.coeff j * x₀ ^ j) := by
    intro i j hij hjS hci hcj heqv
    obtain ⟨ci, hci'⟩ := hcoeffQ i
    obtain ⟨cj, hcj'⟩ := hcoeffQ j
    have hci0 : ci ≠ 0 := by rintro rfl; apply hci; rw [← hci']; push_cast; rfl
    have hcj0 : cj ≠ 0 := by rintro rfl; apply hcj; rw [← hcj']; push_cast; rfl
    obtain ⟨ai, bi, hvi⟩ := rational_value_powers A hp hA ci hci0
    obtain ⟨aj, bj, hvj⟩ := rational_value_powers A hp hA cj hcj0
    rw [← hci', ← hcj', map_mul, map_mul, map_pow, map_pow] at heqv
    set vq := A.valuation ((p : ℕ) : Kb) with hvq
    set vx := A.valuation x₀ with hvx
    set vi := A.valuation (ci : Kb) with hvi'
    set vj := A.valuation (cj : Kb) with hvj'
    obtain ⟨e, rfl⟩ : ∃ e, j = i + e := ⟨j - i, by omega⟩
    have he0 : 0 < e := by omega
    have hed : e < d := by omega
    have heqv' : vi = vj * vx ^ e := by
      rw [pow_add, mul_comm (vx ^ i) (vx ^ e), ← mul_assoc] at heqv
      exact mul_right_cancel₀ (pow_ne_zero i hvx₀0) heqv
    have E1 : vq ^ (ai + bj) = vq ^ (aj + bi) * vx ^ e := by
      rw [pow_add, pow_add, ← hvi, ← hvj, heqv']
      simp only [mul_assoc, mul_comm, mul_left_comm]
    have hxd : vx ^ d * vq = 1 := hvx₀
    have E2 : vq ^ ((ai + bj) * d + e) = vq ^ ((aj + bi) * d) := by
      have h1 : (vq ^ (ai + bj)) ^ d * vq ^ e = (vq ^ (aj + bi) * vx ^ e) ^ d * vq ^ e :=
        by rw [E1]
      rw [← pow_mul, ← pow_add] at h1
      rw [h1, mul_pow, ← pow_mul, mul_assoc,
        show (vx ^ e) ^ d * vq ^ e = (vx ^ d * vq) ^ e by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm e d],
        hxd, one_pow, mul_one]
    have E3 : (ai + bj) * d + e = (aj + bi) * d :=
      (pow_right_strictAnti₀ hvp0' hvp1).injective E2
    rcases Nat.lt_or_ge (ai + bj) (aj + bi) with hlt | hge
    · have h3 : (ai + bj + 1) * d ≤ (aj + bi) * d := Nat.mul_le_mul_right d hlt
      rw [Nat.succ_mul] at h3
      linarith
    · have h3 : (aj + bi) * d ≤ (ai + bj) * d := Nat.mul_le_mul_right d hge
      linarith
  set I : Finset ℕ := (Finset.range (g.natDegree + 1)).filter (fun i => g.coeff i ≠ 0) with hI
  have hnI : g.natDegree ∈ I := by
    rw [hI, Finset.mem_filter]
    exact ⟨Finset.self_mem_range_succ _, by rw [hgmonic.coeff_natDegree]; exact one_ne_zero⟩
  obtain ⟨j, hjI, hjmax⟩ := I.exists_max_image (fun i => A.valuation (g.coeff i * x₀ ^ i))
    ⟨_, hnI⟩
  have hjcoeff : g.coeff j ≠ 0 := (Finset.mem_filter.mp hjI).2
  have hjle : j ≤ Xs.card := by
    have := Finset.mem_range.mp (Finset.mem_filter.mp hjI).1
    omega
  have hvj0 : A.valuation (g.coeff j * x₀ ^ j) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (mul_ne_zero hjcoeff (pow_ne_zero _ hx₀0))
  have hsum : A.valuation (g.eval x₀) = A.valuation (g.coeff j * x₀ ^ j) := by
    rw [Polynomial.eval_eq_sum_range]
    refine Valuation.map_sum_eq_of_lt _ ?_ ?_
    · exact Finset.mem_range.mpr (by have := Finset.mem_range.mp (Finset.mem_filter.mp hjI).1; omega)
    · intro i hi
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
      by_cases hci : g.coeff i = 0
      · rw [hci, zero_mul, _root_.map_zero]
        exact zero_lt_iff.mpr hvj0
      · have hiI : i ∈ I := Finset.mem_filter.mpr ⟨hi.1, hci⟩
        refine lt_of_le_of_ne (hjmax i hiI) ?_
        have hile : i ≤ Xs.card := by
          have := Finset.mem_range.mp hi.1
          omega
        rcases lt_or_gt_of_ne hi.2 with hlt | hgt
        · exact hterm_ne i j hlt hjle hci hjcoeff
        · exact (hterm_ne j i hgt hile hjcoeff hci).symm
  rw [hgx₀, _root_.map_zero] at hsum
  exact hvj0 hsum.symm

end DkMath.FLT.Frey.Source
