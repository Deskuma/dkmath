/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CFBRC.Basic
import DkMath.CFBRC.CyclotomicProduct
import DkMath.NumberTheory.CyclotomicQRProduct
import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.NumberTheory.NumberField.Norm

#print "file: DkMath.CFBRC.CyclotomicNorm"

/-!
# CFBRC cyclotomic carrier and complex norm bridge

This module keeps the complete gap factor together with the homogeneous
cyclotomic shell.  It is the first norm-aware layer requested by the FLT7
generalization handoff:

```text
gap * GN
  = gap * homogeneous cyclotomic shell
  = power difference.
```

The root-product carrier is independent of any nonzero-gap cancellation.  Its
individual complex factors also carry the standard `Complex.normSq` norm.
-/

namespace DkMath.CFBRC

open scoped BigOperators

open DkMath.CosmicFormula
open DkMath.CosmicFormulaBinom
open DkMath.NumberTheory.CyclotomicQRProduct
open ComplexConjugate
open NumberField

noncomputable section

/-! ## Field and ring-of-integers norm carrier -/

/-- The chosen primitive linear factor in the ring of integers of `K`.

The arguments are gap/base coordinates.  Unlike the endpoint presentation
used by the older Kummer theorem, this definition does not use natural
subtraction.
-/
def cyclotomicLinearFactorInRingOfIntegers
    {K : Type*} [Field K] [NumberField K] [CharZero K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (x u : ℕ) : 𝓞 K :=
  ((x + u : ℕ) : 𝓞 K) - hζ.toInteger * (u : 𝓞 K)

private lemma norm_sub_primitiveRoot_eq_eval_cyclotomic_rat
    {K : Type*} [Field K] [CharZero K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (a : ℚ) :
    Algebra.norm ℚ ((a : K) - ζ) =
      Polynomial.eval a (Polynomial.cyclotomic p ℚ) := by
  let E := AlgebraicClosure K
  let : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root
    (Polynomial.cyclotomic p E)
    (Polynomial.degree_cyclotomic_pos p E (NeZero.pos _)).ne.symm
  have hirr : Irreducible (Polynomial.cyclotomic p ℚ) :=
    Polynomial.cyclotomic.irreducible_rat (Nat.Prime.pos (Fact.out : Nat.Prime p))
  apply (algebraMap ℚ E).injective
  let _ := IsCyclotomicExtension.finiteDimensional {p} ℚ K
  let _ := IsCyclotomicExtension.isGalois {p} ℚ K
  rw [Algebra.norm_eq_prod_embeddings]
  conv_lhs =>
    congr
    rfl
    ext
    rw [map_sub]
    simp
  have hProd :
      ∏ σ : K →ₐ[ℚ] E, ((a : E) - σ ζ) =
        Polynomial.eval (a : E) (Polynomial.cyclotomic' p E) := by
    rw [Polynomial.cyclotomic', Polynomial.eval_prod,
      ← @Finset.prod_attach E E, ← Finset.univ_eq_attach]
    refine Fintype.prod_equiv (hζ.embeddingsEquivPrimitiveRoots E hirr) _ _ ?_
    intro σ
    simp
  rw [hProd, Polynomial.cyclotomic',
    ← Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots
      (Polynomial.isRoot_cyclotomic_iff.1 hz),
    ← Polynomial.map_cyclotomic p (algebraMap ℚ E)]
  calc
    Polynomial.eval (a : E)
        (Polynomial.map (algebraMap ℚ E) (Polynomial.cyclotomic p ℚ))
        = Polynomial.eval₂ (algebraMap ℚ E) (a : E)
            (Polynomial.cyclotomic p ℚ) := by
            simpa [Polynomial.aeval_def] using
              (Polynomial.eval_map_algebraMap (Polynomial.cyclotomic p ℚ) (a : E))
    _ = (algebraMap ℚ E) (Polynomial.eval a (Polynomial.cyclotomic p ℚ)) := by
          simpa using
            (Polynomial.eval₂_at_apply (p := Polynomial.cyclotomic p ℚ)
              (algebraMap ℚ E) a)

private lemma cyclotomicEval_nat_gap_mul_pow_eq_GN
    {K : Type*} [Field K] [CharZero K]
    {p x u : ℕ} [Fact p.Prime] (hu0 : u ≠ 0) :
    DkMath.CFBRC.cyclotomicEval p
        ((((x + u : ℕ) : ℚ) / (u : ℚ) : ℚ) : K) * (u : K) ^ (p - 1) =
      ((DkMath.CosmicFormulaBinom.GN p x u : ℕ) : K) := by
  have huK : (u : K) ≠ 0 := by exact_mod_cast hu0
  have hp0 : 0 < p := (Fact.out : Nat.Prime p).pos
  have hshift :=
    DkMath.CFBRC.cyclotomicShiftedEval_eq_cyclotomicEval_div_mul_pow
      (R := K) p (x : K) (u : K) huK
  have hdeg : (Polynomial.cyclotomic p ℤ).natDegree = p - 1 := by
    simpa [Nat.totient_prime (Fact.out : Nat.Prime p)] using
      (Polynomial.natDegree_cyclotomic p ℤ)
  have hratio :
      (((x : K) + (u : K)) / (u : K)) =
        ((((x + u : ℕ) : ℚ) / (u : ℚ) : ℚ) : K) := by
    norm_num [hu0, huK]
  have hprod :
    DkMath.CFBRC.cyclotomicShiftedEval p (x : K) (u : K) =
        ((DkMath.CosmicFormulaBinom.GN p x u : ℕ) : K) := by
    have hdiv :=
      DkMath.CFBRC.cyclotomicDivisorsProductShifted_eq_cyclotomicPrimeCore
        (R := K) hp0 (x : K) (u : K) huK
    have hsingleton :
        DkMath.CFBRC.cyclotomicDivisorsProductShifted p (x : K) (u : K) =
          DkMath.CFBRC.cyclotomicShiftedEval p (x : K) (u : K) := by
      unfold DkMath.CFBRC.cyclotomicDivisorsProductShifted
      rw [(Fact.out : Nat.Prime p).divisors]
      have hp1 : ¬ (1 : ℕ) = p :=
        (Fact.out : Nat.Prime p).ne_one.symm
      simp [hp1]
    rw [← hsingleton, hdiv,
      DkMath.CFBRC.cyclotomicPrimeCore_eq_GN]
    simp [DkMath.CosmicFormula.GN]
  calc
    DkMath.CFBRC.cyclotomicEval p
          ((((x + u : ℕ) : ℚ) / (u : ℚ) : ℚ) : K) * (u : K) ^ (p - 1) =
        DkMath.CFBRC.cyclotomicEval p
          ((((x : K) + (u : K)) / (u : K))) * (u : K) ^
            (Polynomial.cyclotomic p ℤ).natDegree := by
          rw [hdeg, hratio]
    _ = DkMath.CFBRC.cyclotomicShiftedEval p (x : K) (u : K) := hshift.symm
    _ = ((DkMath.CosmicFormulaBinom.GN p x u : ℕ) : K) := hprod

theorem cyclotomicLinearFactor_norm_eq_GN_ratCast
    {K : Type*} [Field K] [NumberField K] [CharZero K]
    {p x u : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hu0 : u ≠ 0) :
    ((Algebra.norm ℤ
        (cyclotomicLinearFactorInRingOfIntegers hζ x u) : ℤ) : ℚ) =
      ((DkMath.CosmicFormulaBinom.GN p x u : ℕ) : ℚ) := by
  let lin : 𝓞 K := cyclotomicLinearFactorInRingOfIntegers hζ x u
  have huK : (u : K) ≠ 0 := by exact_mod_cast hu0
  have hfinrank : Module.finrank ℚ K = p - 1 := by
    rw [IsCyclotomicExtension.finrank K
      (Polynomial.cyclotomic.irreducible_rat (Nat.Prime.pos (Fact.out : Nat.Prime p)))]
    simp [Nat.totient_prime (Fact.out : Nat.Prime p)]
  have hlin :
      (lin : K) = (u : K) *
        (((((x + u : ℕ) : ℚ) / (u : ℚ) : ℚ) : K) - ζ) := by
    have hratio :
        (u : K) * ((((x + u : ℕ) : ℚ) / (u : ℚ) : ℚ) : K) =
          ((x + u : ℕ) : K) := by
      norm_num [hu0]
      field_simp [huK]
    have hcast : (hζ.toInteger : K) = ζ := IsPrimitiveRoot.coe_toInteger hζ
    simp [lin, cyclotomicLinearFactorInRingOfIntegers, hcast]
    field_simp [huK]
  have hnormU : Algebra.norm ℚ (u : K) = (u : ℚ) ^ (p - 1) := by
    calc
      Algebra.norm ℚ (u : K) = (u : ℚ) ^ Module.finrank ℚ K := by
        rw [show (u : K) = algebraMap ℚ K (u : ℚ) by simp,
          Algebra.norm_algebraMap]
      _ = (u : ℚ) ^ (p - 1) := by rw [hfinrank]
  have hnormField :
      Algebra.norm ℚ (lin : K) =
        (u : ℚ) ^ (p - 1) *
          Polynomial.eval (((x + u : ℕ) : ℚ) / (u : ℚ))
            (Polynomial.cyclotomic p ℚ) := by
    rw [hlin, map_mul, hnormU,
      norm_sub_primitiveRoot_eq_eval_cyclotomic_rat hζ]
  have heval :
      Polynomial.eval (((x + u : ℕ) : ℚ) / (u : ℚ))
          (Polynomial.cyclotomic p ℚ) =
        DkMath.CFBRC.cyclotomicEval p
          (((x + u : ℕ) : ℚ) / (u : ℚ)) := by
    unfold DkMath.CFBRC.cyclotomicEval
    calc
      Polynomial.eval (((x + u : ℕ) : ℚ) / (u : ℚ))
          (Polynomial.cyclotomic p ℚ) =
          Polynomial.eval₂ (algebraMap ℚ ℚ)
            (((x + u : ℕ) : ℚ) / (u : ℚ))
            (Polynomial.cyclotomic p ℚ) := by
            simp
      _ = Polynomial.eval
          (((x + u : ℕ) : ℚ) / (u : ℚ))
          ((Polynomial.cyclotomic p ℚ).map (algebraMap ℚ ℚ)) := by
            exact Polynomial.eval₂_eq_eval_map
              (p := Polynomial.cyclotomic p ℚ)
              (f := algebraMap ℚ ℚ)
              (x := ((x + u : ℕ) : ℚ) / (u : ℚ))
      _ = DkMath.CFBRC.cyclotomicEval p
          (((x + u : ℕ) : ℚ) / (u : ℚ)) := by
            rw [show (Polynomial.cyclotomic p ℚ).map (algebraMap ℚ ℚ) =
                (Polynomial.cyclotomic p ℤ).map (Int.castRingHom ℚ) by
              ext n
              simp]
            exact (Polynomial.eval₂_eq_eval_map
              (p := Polynomial.cyclotomic p ℤ)
              (f := Int.castRingHom ℚ)
              (x := ((x + u : ℕ) : ℚ) / (u : ℚ))).symm
  have hGNQ :=
    cyclotomicEval_nat_gap_mul_pow_eq_GN
      (K := ℚ) (p := p) (x := x) (u := u) hu0
  have hfield :
      Algebra.norm ℚ (lin : K) =
        ((DkMath.CosmicFormulaBinom.GN p x u : ℕ) : ℚ) := by
    rw [hnormField, heval]
    calc
      (u : ℚ) ^ (p - 1) *
          DkMath.CFBRC.cyclotomicEval p
            (((x + u : ℕ) : ℚ) / (u : ℚ)) =
          DkMath.CFBRC.cyclotomicEval p
            (((x + u : ℕ) : ℚ) / (u : ℚ)) *
            (u : ℚ) ^ (p - 1) := by ring
      _ = ((DkMath.CosmicFormulaBinom.GN p x u : ℕ) : ℚ) := hGNQ
  have hcoe :
      ((Algebra.norm ℤ lin : ℤ) : ℚ) = Algebra.norm ℚ (lin : K) :=
    Algebra.coe_norm_int lin
  simpa [lin] using hcoe.trans hfield

theorem cyclotomicLinearFactor_norm_eq_GN
    {K : Type*} [Field K] [NumberField K] [CharZero K]
    {p x u : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hu0 : u ≠ 0) :
    Algebra.norm ℤ (cyclotomicLinearFactorInRingOfIntegers hζ x u) =
      ((DkMath.CosmicFormulaBinom.GN p x u : ℕ) : ℤ) := by
  exact Int.cast_injective
    (cyclotomicLinearFactor_norm_eq_GN_ratCast hζ hu0)

/-- The complete nonzero-root cyclotomic product in gap/base coordinates. -/
def cyclotomicRootProduct
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime]
    (ζ : K) (x u : K) : K :=
  (nonzeroResidues p).prod (fun a => rootFactor ζ a (x + u) u)

/-- The complete root product is the homogeneous cyclotomic shell. -/
theorem cyclotomicRootProduct_eq_shell
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (x u : K) :
    cyclotomicRootProduct (p := p) ζ x u = GTailCyclotomicShell p x u := by
  simpa [cyclotomicRootProduct, GTailCyclotomicShell] using
    nonzeroRoot_product_eq_shell ζ hζ (x + u) u

/-- The complete root product is exactly the one-gap `GTail` kernel. -/
theorem cyclotomicRootProduct_eq_GTail_one
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (x u : K) :
    cyclotomicRootProduct (p := p) ζ x u = GTail p 1 x u := by
  rw [cyclotomicRootProduct_eq_shell ζ hζ]
  exact (GTail_one_eq_GTailCyclotomicShell p x u).symm

/-- The complete root product is exactly the canonical `GN` kernel. -/
theorem cyclotomicRootProduct_eq_GN
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (x u : K) :
    cyclotomicRootProduct (p := p) ζ x u = CosmicFormulaBinom.GN p x u := by
  exact cyclotomicRootProduct_eq_GTail_one ζ hζ x u

/--
The complete gap times the cyclotomic root product is the original power
difference.  This keeps the boundary factor that is lost when one looks only
at the cyclotomic quotient.
-/
theorem gap_mul_cyclotomicRootProduct_eq_sub_pow
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (x u : K) :
    x * cyclotomicRootProduct (p := p) ζ x u = (x + u) ^ p - u ^ p := by
  rw [cyclotomicRootProduct_eq_GTail_one ζ hζ]
  rw [eq_sub_iff_add_eq]
  exact (add_pow_eq_mul_GTail_one_add_gap p x u).symm

/-- One complex cyclotomic factor paired with its conjugate is its norm square. -/
theorem complex_rootFactor_mul_conj_eq_normSq
    {p : ℕ} [Fact p.Prime]
    (ζ : ℂ) (a : ZMod p) (x u : ℂ) :
    rootFactor (p := p) ζ a (x + u) u *
        conj (rootFactor ζ a (x + u) u) =
      Complex.normSq (rootFactor ζ a (x + u) u) := by
  exact Complex.mul_conj _

/-- The complex norm square of the full carrier is the norm square of `GN`. -/
theorem complex_normSq_cyclotomicRootProduct_eq_GN
    {p : ℕ} [Fact p.Prime]
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ p) (x u : ℂ) :
    Complex.normSq (cyclotomicRootProduct (p := p) ζ x u) =
      Complex.normSq (CosmicFormulaBinom.GN p x u) := by
  rw [cyclotomicRootProduct_eq_GN ζ hζ]

/--
The complex norm square also preserves the complete gap/product identity.
This is deliberately stated before any conjugate-pair half-product
compression.
-/
theorem complex_normSq_gap_mul_cyclotomicRootProduct_eq_sub_pow
    {p : ℕ} [Fact p.Prime]
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ p) (x u : ℂ) :
    Complex.normSq (x * cyclotomicRootProduct (p := p) ζ x u) =
      Complex.normSq ((x + u) ^ p - u ^ p) := by
  rw [gap_mul_cyclotomicRootProduct_eq_sub_pow ζ hζ]

end

end DkMath.CFBRC
