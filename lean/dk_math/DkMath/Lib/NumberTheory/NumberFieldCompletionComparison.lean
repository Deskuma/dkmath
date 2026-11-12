/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

#print "file: DkMath.Lib.NumberTheory.NumberFieldCompletionComparison"

/-!
# 同じ有限素点の e=f=1 から自然な完備化写像の全射性へ

剰余次数1は実際の剰余体写像の全射性を与える。分岐指数1なら底体の一様化元は
上の体でも一様化元であり、桁を順に合わせることで底体の稠密性を証明できる。
自然な完備化写像は一様埋め込みで、完備な像は閉じているので全射となる。
局所次数比較を仮定せず、この場合の次数1を最後に導く。
-/

namespace DkMath.Lib.NumberTheory.NumberFieldCompletionComparison

open IsDedekindDomain HeightOneSpectrum WithZero UniformSpace MonoidWithZeroHom
open scoped NumberField Topology
noncomputable section

variable {F M : Type*} [Field F] [NumberField F] [Field M] [NumberField M] [Algebra F M]
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 M))
    [w.asIdeal.LiesOver v.asIdeal]

include v in
/-- 剰余次数1なら、局所整数 x の先頭の剰余を同じ底体整数で合わせられる。 -/
theorem exists_integer_digit_of_inertiaDeg_eq_one
    (hf : w.asIdeal.inertiaDeg (𝓞 F) = 1) (x : M) (hx : w.valuation M x ≤ 1) :
    ∃ a : 𝓞 F, w.valuation M (x - algebraMap F M (algebraMap (𝓞 F) F a)) < 1 := by
  let : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  let : Field (𝓞 M ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal
  have hdim : Module.finrank (𝓞 F ⧸ v.asIdeal) (𝓞 M ⧸ w.asIdeal) = 1 := by
    rwa [← Ideal.inertiaDeg_eq_of_isMaximal v.asIdeal w.asIdeal]
  have hsurj := (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hdim).surjective
  obtain ⟨n, d, hnd⟩ := w.exists_primeCompl_mul_eq_of_integer x hx
  have hdq : Ideal.Quotient.mk w.asIdeal (d : 𝓞 M) ≠ 0 := by
    rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact d.prop
  obtain ⟨a₀, ha₀⟩ := hsurj
    (Ideal.Quotient.mk w.asIdeal n / Ideal.Quotient.mk w.asIdeal (d : 𝓞 M))
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a₀
  rw [Ideal.Quotient.algebraMap_mk_of_liesOver] at ha₀
  have hmem : n - algebraMap (𝓞 F) (𝓞 M) a * (d : 𝓞 M) ∈ w.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, sub_eq_zero]
    exact ((eq_div_iff hdq).mp ha₀).symm
  have hdval : w.valuation M (algebraMap (𝓞 M) M (d : 𝓞 M)) = 1 := by
    rw [valuation_of_algebraMap]
    exact (w.intValuation_eq_one_iff_mem_primeCompl _).mpr d.prop
  have hdM : algebraMap (𝓞 M) M (d : 𝓞 M) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hdval
    exact zero_ne_one hdval
  have ha : algebraMap (𝓞 M) M (algebraMap (𝓞 F) (𝓞 M) a) =
      algebraMap F M (algebraMap (𝓞 F) F a) := by
    simp only [← IsScalarTower.algebraMap_apply]
  have he : x - algebraMap F M (algebraMap (𝓞 F) F a) =
      algebraMap (𝓞 M) M (n - algebraMap (𝓞 F) (𝓞 M) a * (d : 𝓞 M)) /
        algebraMap (𝓞 M) M (d : 𝓞 M) := by
    rw [eq_div_iff hdM, sub_mul, hnd, map_sub, map_mul, ha]
  refine ⟨a, ?_⟩
  rw [he, map_div₀, hdval, div_one, valuation_of_algebraMap]
  exact (w.intValuation_lt_one_iff_mem _).mpr hmem

private theorem le_exp_neg_one_of_lt_one {z : ℤᵐ⁰} (h : z < 1) : z ≤ exp (-1) := by
  apply (lt_mul_exp_iff_le (show exp (-1 : ℤ) ≠ 0 from exp_ne_zero)).mp
  simpa only [← exp_add, neg_add_cancel, exp_zero] using h

/-- 同じ一様化元で桁を合わせ、任意の局所整数を底体の元で n 桁まで近似する。 -/
theorem exists_approximation_of_ef_eq_one
    (he : v.asIdeal.ramificationIdx' w.asIdeal = 1)
    (hf : w.asIdeal.inertiaDeg (𝓞 F) = 1) (n : ℕ) (x : M) (hx : w.valuation M x ≤ 1) :
    ∃ a : F, w.valuation M (x - algebraMap F M a) ≤ exp (-(n : ℤ)) := by
  have hv (a : F) : w.valuation M (algebraMap F M a) = v.valuation F a := by
    rw [← valuation_liesOver M v w, he, pow_one]
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hπw : w.valuation M (algebraMap F M π) = exp (-1) := (hv π).trans hπ
  have hπ0 : algebraMap F M π ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hπw
    exact exp_ne_zero hπw.symm
  induction n generalizing x with
  | zero => exact ⟨0, by simpa using hx⟩
  | succ n ih =>
    obtain ⟨r, hr⟩ := exists_integer_digit_of_inertiaDeg_eq_one v w hf x hx
    let d : F := algebraMap (𝓞 F) F r
    let y : M := (x - algebraMap F M d) / algebraMap F M π
    have hy : w.valuation M y ≤ 1 := by
      dsimp only [y]
      rw [map_div₀, hπw, div_le_one₀ (show (0 : ℤᵐ⁰) < exp (-1 : ℤ) from exp_pos)]
      exact le_exp_neg_one_of_lt_one hr
    obtain ⟨a, ha⟩ := ih y hy
    refine ⟨d + π * a, ?_⟩
    have heq : x - algebraMap F M (d + π * a) =
        algebraMap F M π * (y - algebraMap F M a) := by
      dsimp only [y]
      rw [map_add, map_mul]
      field_simp [hπ0]
      ring
    rw [heq, map_mul, hπw]
    calc
      exp (-1) * w.valuation M (y - algebraMap F M a) ≤ exp (-1) * exp (-(n : ℤ)) :=
        mul_le_mul_of_nonneg_left ha (zero_le : (0 : ℤᵐ⁰) ≤ exp (-1 : ℤ))
      _ = exp (-(↑(n + 1) : ℤ)) := by rw [← exp_add]; congr 1; omega

/-- 任意の体元を、指定した非零の付値半径以内まで同じ底体から近似する。 -/
theorem exists_valuation_sub_lt_of_ef_eq_one
    (he : v.asIdeal.ramificationIdx' w.asIdeal = 1)
    (hf : w.asIdeal.inertiaDeg (𝓞 F) = 1) (x : M) (γ : ℤᵐ⁰ˣ) :
    ∃ a : F, w.valuation M (x - algebraMap F M a) < γ := by
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  have hxval : w.valuation M x ≠ 0 := by simpa using hx
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hπw : w.valuation M (algebraMap F M π) = exp (-1) := by
    rw [← valuation_liesOver M v w, he, pow_one, hπ]
  obtain ⟨k, hk⟩ := exists_exp_neg_natCast_lt (inv_ne_zero hxval)
  let d : F := π ^ k
  have hdval : w.valuation M (algebraMap F M d) = exp (-(k : ℤ)) := by
    dsimp only [d]
    rw [map_pow, map_pow, hπw, ← exp_nsmul]
    congr 1
    simp only [nsmul_eq_mul, mul_neg, mul_one]
  have hdM : algebraMap F M d ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hdval
    exact exp_ne_zero hdval.symm
  let z : M := algebraMap F M d * x
  have hz : w.valuation M z ≤ 1 := by
    dsimp only [z]
    rw [map_mul, hdval]
    apply le_of_lt
    calc
      exp (-(k : ℤ)) * w.valuation M x < (w.valuation M x)⁻¹ * w.valuation M x :=
        mul_lt_mul_of_pos_right hk (pos_iff_ne_zero.mpr hxval)
      _ = 1 := inv_mul_cancel₀ hxval
  obtain ⟨n, hn⟩ := exists_exp_neg_natCast_lt
    (mul_ne_zero (Units.ne_zero γ) (show exp (-(k : ℤ)) ≠ 0 from exp_ne_zero))
  obtain ⟨a, ha⟩ := exists_approximation_of_ef_eq_one v w he hf n z hz
  refine ⟨a / d, ?_⟩
  have heq : x - algebraMap F M (a / d) = (z - algebraMap F M a) / algebraMap F M d := by
    dsimp only [z]
    rw [map_div₀]
    field_simp [hdM]
  rw [heq, map_div₀, hdval, div_lt_iff₀ (show (0 : ℤᵐ⁰) < exp (-(k : ℤ)) from exp_pos)]
  exact ha.trans_lt hn

private theorem uniformInducing_of_valuation_preserving
    {A B : Type*} [Field A] [Field B] [Valued A ℤᵐ⁰] [Valued B ℤᵐ⁰]
    (f : A →+* B) (hc : UniformContinuous f)
    (hv : ∀ a : A, Valued.v (f a) = Valued.v a) : IsUniformInducing f := by
  apply ((Valued.hasBasis_uniformity A ℤᵐ⁰).isUniformInducing_iff
    (Valued.hasBasis_uniformity B ℤᵐ⁰)).mpr
  refine ⟨((Valued.hasBasis_uniformity A ℤᵐ⁰).uniformContinuous_iff
    (Valued.hasBasis_uniformity B ℤᵐ⁰)).mp hc, ?_⟩
  intro γ _
  obtain ⟨a, ha⟩ := ValueGroup₀.restrict₀_surjective (.ofClass (Valued.v : Valuation A ℤᵐ⁰)) γ.val
  change Valued.v.restrict a = γ.val at ha
  have ha0 : (Valued.v : Valuation A ℤᵐ⁰) a ≠ 0 := by
    intro h0
    apply Units.ne_zero γ
    rw [← ha]
    exact (Valuation.restrict_eq_zero_iff _).mpr h0
  have hb0 : (Valued.v : Valuation B ℤᵐ⁰).restrict (f a) ≠ 0 := by
    intro h0
    apply ha0
    rw [← hv a]
    exact (Valuation.restrict_eq_zero_iff _).mp h0
  refine ⟨Units.mk0 _ hb0, trivial, ?_⟩
  intro x y hxy
  change (Valued.v : Valuation A ℤᵐ⁰).restrict (y - x) < γ.val
  rw [← ha, Valuation.restrict_lt_iff]
  change (Valued.v : Valuation B ℤᵐ⁰).restrict (f y - f x) < Valued.v.restrict (f a) at hxy
  rw [Valuation.restrict_lt_iff, ← map_sub, hv, hv] at hxy
  exact hxy

/-- 元の包含から、指定した同じ二つの adicCompletion の間へ延長した自然な環準同型。 -/
def completionMap : v.adicCompletion F →+* w.adicCompletion M := by
  let f : WithVal (v.valuation F) →+* WithVal (w.valuation M) := algebraMap _ _
  let hf : Continuous f := (uniformContinuous_algebraMap_liesOver F M v w).continuous
  let fm : Completion (WithVal (v.valuation F)) →+* Completion (WithVal (w.valuation M)) :=
    Completion.mapRingHom f hf
  exact (adicCompletion.equiv M w).symm.toRingHom.comp
    (fm.comp (adicCompletion.equiv F v).toRingHom)

/-- 完備化写像の可換性。底体元を先に上げても、先に完備化しても同じ像となる。 -/
theorem completionMap_algebraMap (a : F) :
    completionMap v w (algebraMap F (v.adicCompletion F) a) =
      algebraMap M (w.adicCompletion M) (algebraMap F M a) := by
  apply (adicCompletion.equiv M w).injective
  change Completion.mapRingHom
    (algebraMap (WithVal (v.valuation F)) (WithVal (w.valuation M)))
    (uniformContinuous_algebraMap_liesOver F M v w).continuous
    ((WithVal.equiv (v.valuation F)).symm a : Completion (WithVal (v.valuation F))) =
      ((WithVal.equiv (w.valuation M)).symm (algebraMap F M a) : Completion (WithVal (w.valuation M)))
  rw [Completion.mapRingHom_coe]
  rfl

/-- e=1 なら、自然な完備化写像は一様埋め込みである。 -/
theorem completionMap_isUniformInducing_of_ramification_eq_one
    (he : v.asIdeal.ramificationIdx' w.asIdeal = 1) :
    IsUniformInducing (completionMap v w) := by
  let f := algebraMap (WithVal (v.valuation F)) (WithVal (w.valuation M))
  have hc : UniformContinuous f := uniformContinuous_algebraMap_liesOver F M v w
  have hi : IsUniformInducing f := uniformInducing_of_valuation_preserving f hc (by
    intro a
    change w.valuation M (algebraMap F M a.ofVal) = v.valuation F a.ofVal
    rw [← valuation_liesOver M v w, he, pow_one])
  have hm : IsUniformInducing (Completion.mapRingHom f hc.continuous) :=
    Completion.isUniformInducing_extension ((Completion.isUniformInducing_coe _).comp hi)
  exact (adicCompletion.uniformEquiv M w).symm.isUniformEmbedding.isUniformInducing.comp
    (hm.comp (adicCompletion.uniformEquiv F v).isUniformEmbedding.isUniformInducing)

/-- e=f=1 のとき、元の包含は上の付値体に稠密な像を持つ。 -/
theorem denseRange_valuedMap_of_ef_eq_one
    (he : v.asIdeal.ramificationIdx' w.asIdeal = 1)
    (hf : w.asIdeal.inertiaDeg (𝓞 F) = 1) :
    DenseRange (algebraMap (WithVal (v.valuation F)) (WithVal (w.valuation M))) := by
  intro x
  rw [mem_closure_iff_nhds]
  intro U hU
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hU
  let δ : ℤᵐ⁰ˣ := Units.map
    (ValueGroup₀.embedding (f := .ofClass (Valued.v : Valuation (WithVal (w.valuation M)) ℤᵐ⁰))) γ
  obtain ⟨a, ha⟩ := exists_valuation_sub_lt_of_ef_eq_one v w he hf x.ofVal δ
  refine ⟨algebraMap (WithVal (v.valuation F)) (WithVal (w.valuation M))
    (WithVal.toVal (v.valuation F) a), ?_, ⟨_, rfl⟩⟩
  apply hγ
  change (Valued.v : Valuation (WithVal (w.valuation M)) ℤᵐ⁰).restrict
    (algebraMap (WithVal (v.valuation F)) (WithVal (w.valuation M))
      (WithVal.toVal (v.valuation F) a) - x) < γ.val
  rw [Valuation.restrict_lt_iff_lt_embedding]
  change w.valuation M (algebraMap F M a - x.ofVal) < δ.val
  rw [Valuation.map_sub_swap]
  exact ha

/-- e=f=1 のとき、自然な完備化写像の像は稠密である。 -/
theorem completionMap_denseRange_of_ef_eq_one
    (he : v.asIdeal.ramificationIdx' w.asIdeal = 1)
    (hf : w.asIdeal.inertiaDeg (𝓞 F) = 1) : DenseRange (completionMap v w) := by
  let e : WithVal (w.valuation M) → w.adicCompletion M := fun x =>
    (adicCompletion.uniformEquiv M w).symm (x : Completion (WithVal (w.valuation M)))
  have hde : DenseRange e :=
    (adicCompletion.ofCompletion_surjective M w).denseRange.comp
      Completion.denseRange_coe (adicCompletion.continuous_ofCompletion M w)
  have hce : Continuous e := (adicCompletion.continuous_ofCompletion M w).comp
    (Completion.continuous_coe _)
  have hd := hde.comp (denseRange_valuedMap_of_ef_eq_one v w he hf) hce
  have hd' : DenseRange (fun a : WithVal (v.valuation F) =>
      completionMap v w (algebraMap F (v.adicCompletion F) a.ofVal)) := by
    convert hd using 1
    funext a
    exact completionMap_algebraMap v w a.ofVal
  exact hd'.of_comp

/-- 稠密な像は e=1 による完備な閉像でもあるため、自然な写像は実際に全単射となる。 -/
theorem completionMap_bijective_of_ef_eq_one
    (he : v.asIdeal.ramificationIdx' w.asIdeal = 1)
    (hf : w.asIdeal.inertiaDeg (𝓞 F) = 1) : Function.Bijective (completionMap v w) := by
  refine ⟨(completionMap v w).injective, ?_⟩
  have hc := (completionMap_isUniformInducing_of_ramification_eq_one v w he).isComplete_range.isClosed
  intro x
  have hx := completionMap_denseRange_of_ef_eq_one v w he hf x
  rw [hc.closure_eq] at hx
  exact hx

/-- 同じ素点の完備体を結ぶ自然な環同型。元の包含との可換性は completionMap のまま保つ。 -/
def completionEquivOfEFOne
    (he : v.asIdeal.ramificationIdx' w.asIdeal = 1)
    (hf : w.asIdeal.inertiaDeg (𝓞 F) = 1) : v.adicCompletion F ≃+* w.adicCompletion M :=
  RingEquiv.ofBijective (completionMap v w) (completionMap_bijective_of_ef_eq_one v w he hf)

/-- 自然な完備化写像による拡大構造。選択した同じ v,w を型に保持する。 -/
@[instance_reducible] def completionAlgebra : Algebra (v.adicCompletion F) (w.adicCompletion M) :=
  (completionMap v w).toAlgebra

/-- 自然な拡大構造での局所次数は実際に1。次数比較を入力とせず、上で証明した全単射から得る。 -/
theorem finrank_completion_eq_one_of_ef_eq_one
    (he : v.asIdeal.ramificationIdx' w.asIdeal = 1)
    (hf : w.asIdeal.inertiaDeg (𝓞 F) = 1) :
    letI := completionAlgebra v w
    Module.finrank (v.adicCompletion F) (w.adicCompletion M) = 1 := by
  let := completionAlgebra v w
  exact Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
    (completionMap_bijective_of_ef_eq_one v w he hf)

end
end DkMath.Lib.NumberTheory.NumberFieldCompletionComparison
