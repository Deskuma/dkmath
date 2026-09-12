/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.CyclotomicQRProduct

#print "file: DkMath.NumberTheory.CyclotomicQRGaloisAction"

namespace DkMath.NumberTheory.CyclotomicQRGaloisAction

open scoped BigOperators

open DkMath.NumberTheory.CyclotomicQRProduct

noncomputable section

/-! ## Homogeneous QR/QNR factor polynomials -/

def rootFactorPoly {K : Type*} [Field K] {p : ℕ} [NeZero p]
    (ζ : K) (a : ZMod p) : MvPolynomial (Fin 2) K :=
  MvPolynomial.X 0 - MvPolynomial.C (ζ ^ a.val) * MvPolynomial.X 1

def qrFactorPoly {K : Type*} [Field K] {p : ℕ} [Fact p.Prime]
    (ζ : K) : MvPolynomial (Fin 2) K :=
  (qrFinset p).prod (fun a => rootFactorPoly ζ a)

def qnrFactorPoly {K : Type*} [Field K] {p : ℕ} [Fact p.Prime]
    (ζ : K) : MvPolynomial (Fin 2) K :=
  (qnrFinset p).prod (fun a => rootFactorPoly ζ a)

theorem eval_rootFactorPoly
    {K : Type*} [Field K] {p : ℕ} [NeZero p]
    (ζ : K) (a : ZMod p) (X Y : K) :
    MvPolynomial.eval ![X, Y] (rootFactorPoly ζ a) =
      rootFactor ζ a X Y := by
  simp [rootFactorPoly, rootFactor]

theorem eval_qrFactorPoly
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime]
    (ζ : K) (X Y : K) :
    MvPolynomial.eval ![X, Y] (qrFactorPoly (p := p) ζ) =
      (qrFinset p).prod (fun a => rootFactor ζ a X Y) := by
  classical
  simp [qrFactorPoly, eval_rootFactorPoly]

theorem eval_qnrFactorPoly
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime]
    (ζ : K) (X Y : K) :
    MvPolynomial.eval ![X, Y] (qnrFactorPoly (p := p) ζ) =
      (qnrFinset p).prod (fun a => rootFactor ζ a X Y) := by
  classical
  simp [qnrFactorPoly, eval_rootFactorPoly]

/-! ## Multiplication by a nonzero exponent -/

theorem mulBy_t_nonzero_bijective
    {p : ℕ} [Fact p.Prime] {t : ZMod p} (ht : t ≠ 0) :
    Function.Bijective (fun a : ZMod p => t * a) := by
  constructor
  · intro a b hab
    apply (mul_left_cancel₀ ht)
    exact hab
  · intro b
    refine ⟨t⁻¹ * b, ?_⟩
    simp [ht]

theorem mulBy_t_permutes_nonzeroResidues
    {p : ℕ} [Fact p.Prime] {t : ZMod p} (ht : t ≠ 0) :
    (nonzeroResidues p).image (fun a : ZMod p => t * a) =
      nonzeroResidues p := by
  classical
  ext b
  constructor
  · intro hb
    rcases Finset.mem_image.mp hb with ⟨a, ha, rfl⟩
    simp only [nonzeroResidues, Finset.mem_erase, Finset.mem_univ] at ha ⊢
    constructor
    · exact mul_ne_zero ht ha.1
    · trivial
  · intro hb
    refine Finset.mem_image.mpr ⟨t⁻¹ * b, ?_, ?_⟩
    · simp only [nonzeroResidues, Finset.mem_erase, Finset.mem_univ] at hb ⊢
      constructor
      · exact mul_ne_zero (inv_ne_zero ht) hb.1
      · trivial
    · simp [ht]

theorem isSquare_mul_iff
    {p : ℕ} [Fact p.Prime] {a b : ZMod p}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    IsSquare (a * b) ↔ (IsSquare a ↔ IsSquare b) := by
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  rw [← quadraticChar_one_iff_isSquare hab]
  rw [map_mul]
  have hqa := quadraticChar_dichotomy ha
  have hqb := quadraticChar_dichotomy hb
  constructor
  · intro hprod
    constructor
    · intro hsa
      have hqa' := (quadraticChar_one_iff_isSquare ha).mpr hsa
      rw [hqa', one_mul] at hprod
      exact (quadraticChar_one_iff_isSquare hb).mp hprod
    · intro hsb
      have hqb' := (quadraticChar_one_iff_isSquare hb).mpr hsb
      rw [hqb', mul_one] at hprod
      exact (quadraticChar_one_iff_isSquare ha).mp hprod
  · intro heq
    rcases hqa with hqa | hqa <;> rcases hqb with hqb | hqb
    · simp [hqa, hqb]
    · exfalso
      have hsa : IsSquare a := (quadraticChar_one_iff_isSquare ha).mp hqa
      have hsb : IsSquare b := heq.mp hsa
      have : quadraticChar (ZMod p) b = 1 :=
        (quadraticChar_one_iff_isSquare hb).mpr hsb
      omega
    · exfalso
      have hsb : IsSquare b := (quadraticChar_one_iff_isSquare hb).mp hqb
      have hsa : IsSquare a := heq.mpr hsb
      have : quadraticChar (ZMod p) a = 1 :=
        (quadraticChar_one_iff_isSquare ha).mpr hsa
      omega
    · simp [hqa, hqb]

private theorem mem_nonzeroResidues_iff
    {p : ℕ} [Fact p.Prime] {a : ZMod p} :
    a ∈ nonzeroResidues p ↔ a ≠ 0 := by
  simp [nonzeroResidues]

theorem mulBy_t_maps_qr_of_square
    {p : ℕ} [Fact p.Prime] {t : ZMod p} (ht : t ≠ 0)
    (htsq : IsSquare t) :
    (qrFinset p).image (fun a : ZMod p => t * a) = qrFinset p := by
  classical
  ext b
  constructor
  · intro hb
    rcases Finset.mem_image.mp hb with ⟨a, ha, rfl⟩
    exact Finset.mem_filter.mpr ⟨
      mem_nonzeroResidues_iff.mpr
        (mul_ne_zero ht (mem_nonzeroResidues_iff.mp (Finset.mem_filter.mp ha).1)),
      IsSquare.mul htsq (Finset.mem_filter.mp ha).2⟩
  · intro hb
    refine Finset.mem_image.mpr ⟨t⁻¹ * b, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨
        mem_nonzeroResidues_iff.mpr
          (mul_ne_zero (inv_ne_zero ht)
            (mem_nonzeroResidues_iff.mp (Finset.mem_filter.mp hb).1)),
        IsSquare.mul htsq.inv (Finset.mem_filter.mp hb).2⟩
    · simp [ht]

theorem mulBy_t_maps_qnr_of_square
    {p : ℕ} [Fact p.Prime] {t : ZMod p} (ht : t ≠ 0)
    (htsq : IsSquare t) :
    (qnrFinset p).image (fun a : ZMod p => t * a) = qnrFinset p := by
  classical
  ext b
  constructor
  · intro hb
    rcases Finset.mem_image.mp hb with ⟨a, ha, rfl⟩
    have ha0 := mem_nonzeroResidues_iff.mp (Finset.mem_filter.mp ha).1
    have hprod : ¬IsSquare (t * a) := by
      rw [isSquare_mul_iff ht ha0]
      simp [htsq, (Finset.mem_filter.mp ha).2]
    exact Finset.mem_filter.mpr ⟨
      mem_nonzeroResidues_iff.mpr (mul_ne_zero ht ha0), hprod⟩
  · intro hb
    have hb0 := mem_nonzeroResidues_iff.mp (Finset.mem_filter.mp hb).1
    have hprod : ¬IsSquare (t⁻¹ * b) := by
      rw [isSquare_mul_iff (inv_ne_zero ht) hb0]
      simp [htsq.inv, (Finset.mem_filter.mp hb).2]
    refine Finset.mem_image.mpr ⟨t⁻¹ * b, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨
        mem_nonzeroResidues_iff.mpr (mul_ne_zero (inv_ne_zero ht) hb0), hprod⟩
    · simp [ht]

theorem mulBy_t_maps_qr_to_qnr_of_nonsquare
    {p : ℕ} [Fact p.Prime] {t : ZMod p} (ht : t ≠ 0)
    (htnsq : ¬IsSquare t) :
    (qrFinset p).image (fun a : ZMod p => t * a) = qnrFinset p := by
  classical
  ext b
  constructor
  · intro hb
    rcases Finset.mem_image.mp hb with ⟨a, ha, rfl⟩
    have ha0 := mem_nonzeroResidues_iff.mp (Finset.mem_filter.mp ha).1
    have hprod : ¬IsSquare (t * a) := by
      rw [isSquare_mul_iff ht ha0]
      simp [htnsq, (Finset.mem_filter.mp ha).2]
    exact Finset.mem_filter.mpr ⟨
      mem_nonzeroResidues_iff.mpr (mul_ne_zero ht ha0), hprod⟩
  · intro hb
    have hb0 := mem_nonzeroResidues_iff.mp (Finset.mem_filter.mp hb).1
    have htinv : ¬IsSquare t⁻¹ := by
      simpa using htnsq
    have hprod : IsSquare (t⁻¹ * b) := by
      rw [isSquare_mul_iff (inv_ne_zero ht) hb0]
      simp [htinv, (Finset.mem_filter.mp hb).2]
    refine Finset.mem_image.mpr ⟨t⁻¹ * b, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨
        mem_nonzeroResidues_iff.mpr (mul_ne_zero (inv_ne_zero ht) hb0), hprod⟩
    · simp [ht]

theorem mulBy_t_maps_qnr_to_qr_of_nonsquare
    {p : ℕ} [Fact p.Prime] {t : ZMod p} (ht : t ≠ 0)
    (htnsq : ¬IsSquare t) :
    (qnrFinset p).image (fun a : ZMod p => t * a) = qrFinset p := by
  classical
  ext b
  constructor
  · intro hb
    rcases Finset.mem_image.mp hb with ⟨a, ha, rfl⟩
    have ha0 := mem_nonzeroResidues_iff.mp (Finset.mem_filter.mp ha).1
    have hprod : IsSquare (t * a) := by
      rw [isSquare_mul_iff ht ha0]
      simp [htnsq, (Finset.mem_filter.mp ha).2]
    exact Finset.mem_filter.mpr ⟨
      mem_nonzeroResidues_iff.mpr (mul_ne_zero ht ha0), hprod⟩
  · intro hb
    have hb0 := mem_nonzeroResidues_iff.mp (Finset.mem_filter.mp hb).1
    have htinv : ¬IsSquare t⁻¹ := by
      simpa using htnsq
    have hprod : ¬IsSquare (t⁻¹ * b) := by
      rw [isSquare_mul_iff (inv_ne_zero ht) hb0]
      simp [htinv, (Finset.mem_filter.mp hb).2]
    refine Finset.mem_image.mpr ⟨t⁻¹ * b, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨
        mem_nonzeroResidues_iff.mpr (mul_ne_zero (inv_ne_zero ht) hb0), hprod⟩
    · simp [ht]

private theorem primitive_pow_mul_val_eq
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (t a : ZMod p) :
    ζ ^ (t.val * a.val) = ζ ^ (t * a).val := by
  apply pow_eq_pow_of_modEq _ hζ.pow_eq_one
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  rw [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  exact (ZMod.natCast_zmod_val (t * a)).symm

theorem map_rootFactorPoly
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (t : ZMod p) (a : ZMod p)
    (σ : K ≃+* K)
    (hσζ : σ ζ = ζ ^ t.val) :
    MvPolynomial.map σ.toRingHom (rootFactorPoly ζ a) =
      rootFactorPoly ζ (t * a) := by
  have hpow : σ (ζ ^ a.val) = ζ ^ (t * a).val := by
    rw [map_pow, hσζ, ← pow_mul]
    exact primitive_pow_mul_val_eq ζ hζ t a
  simp only [rootFactorPoly, map_sub, map_mul, MvPolynomial.map_X,
    MvPolynomial.map_C]
  change MvPolynomial.X 0 - MvPolynomial.C (σ (ζ ^ a.val)) * MvPolynomial.X 1 =
    MvPolynomial.X 0 - MvPolynomial.C (ζ ^ (t * a).val) * MvPolynomial.X 1
  rw [hpow]

/-! ## Product-polynomial actions -/

theorem map_qrFactorPoly_of_square
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (t : ZMod p)
    (σ : K ≃+* K) (ht : t ≠ 0) (htsq : IsSquare t)
    (hσζ : σ ζ = ζ ^ t.val) :
    MvPolynomial.map σ.toRingHom (qrFactorPoly (p := p) ζ) =
      qrFactorPoly (p := p) ζ := by
  classical
  rw [qrFactorPoly, map_prod]
  calc
    (qrFinset p).prod
        (fun a => MvPolynomial.map σ.toRingHom (rootFactorPoly ζ a)) =
        (qrFinset p).prod (fun a => rootFactorPoly ζ (t * a)) := by
      apply Finset.prod_congr rfl
      intro a ha
      exact map_rootFactorPoly ζ hζ t a σ hσζ
    _ = ((qrFinset p).image (fun a : ZMod p => t * a)).prod
        (fun a => rootFactorPoly ζ a) := by
      symm
      exact Finset.prod_image (f := fun a => rootFactorPoly ζ a)
        (mulBy_t_nonzero_bijective ht).1.injOn
    _ = (qrFinset p).prod (fun a => rootFactorPoly ζ a) := by
      rw [mulBy_t_maps_qr_of_square ht htsq]

theorem map_qnrFactorPoly_of_square
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (t : ZMod p)
    (σ : K ≃+* K) (ht : t ≠ 0) (htsq : IsSquare t)
    (hσζ : σ ζ = ζ ^ t.val) :
    MvPolynomial.map σ.toRingHom (qnrFactorPoly (p := p) ζ) =
      qnrFactorPoly (p := p) ζ := by
  classical
  rw [qnrFactorPoly, map_prod]
  calc
    (qnrFinset p).prod
        (fun a => MvPolynomial.map σ.toRingHom (rootFactorPoly ζ a)) =
        (qnrFinset p).prod (fun a => rootFactorPoly ζ (t * a)) := by
      apply Finset.prod_congr rfl
      intro a ha
      exact map_rootFactorPoly ζ hζ t a σ hσζ
    _ = ((qnrFinset p).image (fun a : ZMod p => t * a)).prod
        (fun a => rootFactorPoly ζ a) := by
      symm
      exact Finset.prod_image (f := fun a => rootFactorPoly ζ a)
        (mulBy_t_nonzero_bijective ht).1.injOn
    _ = (qnrFinset p).prod (fun a => rootFactorPoly ζ a) := by
      rw [mulBy_t_maps_qnr_of_square ht htsq]

theorem map_qrFactorPoly_to_qnr_of_nonsquare
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (t : ZMod p)
    (σ : K ≃+* K) (ht : t ≠ 0) (htnsq : ¬IsSquare t)
    (hσζ : σ ζ = ζ ^ t.val) :
    MvPolynomial.map σ.toRingHom (qrFactorPoly (p := p) ζ) =
      qnrFactorPoly (p := p) ζ := by
  classical
  rw [qrFactorPoly, map_prod]
  calc
    (qrFinset p).prod
        (fun a => MvPolynomial.map σ.toRingHom (rootFactorPoly ζ a)) =
        (qrFinset p).prod (fun a => rootFactorPoly ζ (t * a)) := by
      apply Finset.prod_congr rfl
      intro a ha
      exact map_rootFactorPoly ζ hζ t a σ hσζ
    _ = ((qrFinset p).image (fun a : ZMod p => t * a)).prod
        (fun a => rootFactorPoly ζ a) := by
      symm
      exact Finset.prod_image (f := fun a => rootFactorPoly ζ a)
        (mulBy_t_nonzero_bijective ht).1.injOn
    _ = (qnrFinset p).prod (fun a => rootFactorPoly ζ a) := by
      rw [mulBy_t_maps_qr_to_qnr_of_nonsquare ht htnsq]

theorem map_qnrFactorPoly_to_qr_of_nonsquare
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (t : ZMod p)
    (σ : K ≃+* K) (ht : t ≠ 0) (htnsq : ¬IsSquare t)
    (hσζ : σ ζ = ζ ^ t.val) :
    MvPolynomial.map σ.toRingHom (qnrFactorPoly (p := p) ζ) =
      qrFactorPoly (p := p) ζ := by
  classical
  rw [qnrFactorPoly, map_prod]
  calc
    (qnrFinset p).prod
        (fun a => MvPolynomial.map σ.toRingHom (rootFactorPoly ζ a)) =
        (qnrFinset p).prod (fun a => rootFactorPoly ζ (t * a)) := by
      apply Finset.prod_congr rfl
      intro a ha
      exact map_rootFactorPoly ζ hζ t a σ hσζ
    _ = ((qnrFinset p).image (fun a : ZMod p => t * a)).prod
        (fun a => rootFactorPoly ζ a) := by
      symm
      exact Finset.prod_image (f := fun a => rootFactorPoly ζ a)
        (mulBy_t_nonzero_bijective ht).1.injOn
    _ = (qrFinset p).prod (fun a => rootFactorPoly ζ a) := by
      rw [mulBy_t_maps_qnr_to_qr_of_nonsquare ht htnsq]

/-! ## Symmetric and antisymmetric polynomial axes -/

def Rpoly {K : Type*} [Field K] {p : ℕ} [Fact p.Prime]
    (ζ : K) : MvPolynomial (Fin 2) K :=
  qrFactorPoly (p := p) ζ + qnrFactorPoly (p := p) ζ

def Dpoly {K : Type*} [Field K] {p : ℕ} [Fact p.Prime]
    (ζ : K) : MvPolynomial (Fin 2) K :=
  qrFactorPoly (p := p) ζ - qnrFactorPoly (p := p) ζ

theorem map_Rpoly_of_square
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (t : ZMod p)
    (σ : K ≃+* K) (ht : t ≠ 0) (htsq : IsSquare t)
    (hσζ : σ ζ = ζ ^ t.val) :
    MvPolynomial.map σ.toRingHom (Rpoly (p := p) ζ) = Rpoly (p := p) ζ := by
  rw [Rpoly, map_add, map_qrFactorPoly_of_square ζ hζ t σ ht htsq hσζ,
    map_qnrFactorPoly_of_square ζ hζ t σ ht htsq hσζ]

theorem map_Dpoly_of_square
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (t : ZMod p)
    (σ : K ≃+* K) (ht : t ≠ 0) (htsq : IsSquare t)
    (hσζ : σ ζ = ζ ^ t.val) :
    MvPolynomial.map σ.toRingHom (Dpoly (p := p) ζ) = Dpoly (p := p) ζ := by
  rw [Dpoly, map_sub, map_qrFactorPoly_of_square ζ hζ t σ ht htsq hσζ,
    map_qnrFactorPoly_of_square ζ hζ t σ ht htsq hσζ]

theorem map_Rpoly_of_nonsquare
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (t : ZMod p)
    (σ : K ≃+* K) (ht : t ≠ 0) (htnsq : ¬IsSquare t)
    (hσζ : σ ζ = ζ ^ t.val) :
    MvPolynomial.map σ.toRingHom (Rpoly (p := p) ζ) = Rpoly (p := p) ζ := by
  rw [Rpoly, map_add,
    map_qrFactorPoly_to_qnr_of_nonsquare ζ hζ t σ ht htnsq hσζ,
    map_qnrFactorPoly_to_qr_of_nonsquare ζ hζ t σ ht htnsq hσζ]
  ring

theorem map_Dpoly_of_nonsquare
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (t : ZMod p)
    (σ : K ≃+* K) (ht : t ≠ 0) (htnsq : ¬IsSquare t)
    (hσζ : σ ζ = ζ ^ t.val) :
    MvPolynomial.map σ.toRingHom (Dpoly (p := p) ζ) = -(Dpoly (p := p) ζ) := by
  rw [Dpoly, map_sub,
    map_qrFactorPoly_to_qnr_of_nonsquare ζ hζ t σ ht htnsq hσζ,
    map_qnrFactorPoly_to_qr_of_nonsquare ζ hζ t σ ht htnsq hσζ]
  ring

theorem map_Dpoly_sq_of_square
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (t : ZMod p)
    (σ : K ≃+* K) (ht : t ≠ 0) (htsq : IsSquare t)
    (hσζ : σ ζ = ζ ^ t.val) :
    MvPolynomial.map σ.toRingHom (Dpoly (p := p) ζ ^ 2) =
      Dpoly (p := p) ζ ^ 2 := by
  rw [map_pow, map_Dpoly_of_square ζ hζ t σ ht htsq hσζ]

theorem map_Dpoly_sq_of_nonsquare
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (t : ZMod p)
    (σ : K ≃+* K) (ht : t ≠ 0) (htnsq : ¬IsSquare t)
    (hσζ : σ ζ = ζ ^ t.val) :
    MvPolynomial.map σ.toRingHom (Dpoly (p := p) ζ ^ 2) =
      Dpoly (p := p) ζ ^ 2 := by
  rw [map_pow, map_Dpoly_of_nonsquare ζ hζ t σ ht htnsq hσζ]
  simp

end

end DkMath.NumberTheory.CyclotomicQRGaloisAction
