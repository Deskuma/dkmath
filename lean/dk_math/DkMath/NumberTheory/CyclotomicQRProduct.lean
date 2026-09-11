/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Basic
import DkMath.Lib.Cosmic.GTailCyclotomic

#print "file: DkMath.NumberTheory.CyclotomicQRProduct"

namespace DkMath.NumberTheory.CyclotomicQRProduct

open scoped BigOperators Polynomial

open DkMath.CosmicFormula

noncomputable section

/-! ## The finite QR/QNR partition -/

def nonzeroResidues (p : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  Finset.univ.erase 0

def qrFinset (p : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  (nonzeroResidues p).filter IsSquare

def qnrFinset (p : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  (nonzeroResidues p).filter (fun a => ¬IsSquare a)

theorem qr_qnr_disjoint (p : ℕ) [Fact p.Prime] :
    Disjoint (qrFinset p) (qnrFinset p) := by
  classical
  rw [Finset.disjoint_left]
  intro a ha hb
  exact (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp ha).2

theorem qr_qnr_union (p : ℕ) [Fact p.Prime] :
    qrFinset p ∪ qnrFinset p = nonzeroResidues p := by
  classical
  ext a
  by_cases ha : a = 0
  · simp [qrFinset, qnrFinset, nonzeroResidues, ha]
  · have hchar := quadraticChar_dichotomy (F := ZMod p) ha
    rcases hchar with hchar | hchar
    · have hsquare : IsSquare a :=
        (quadraticChar_one_iff_isSquare ha).mp hchar
      simp [qrFinset, qnrFinset, hsquare]
    · have hnonsquare : ¬IsSquare a :=
        (quadraticChar_neg_one_iff_not_isSquare).mp hchar
      simp [qrFinset, qnrFinset, hnonsquare]

/-! The product recombination is the reusable finite part of the QR/QNR split. -/

theorem qr_product_mul_qnr_product
    {R : Type*} [CommMonoid R]
    (p : ℕ) [Fact p.Prime] (f : ZMod p → R) :
    (qrFinset p).prod f * (qnrFinset p).prod f =
      (nonzeroResidues p).prod f := by
  rw [← Finset.prod_union (qr_qnr_disjoint p), qr_qnr_union p]

/-! ## Primitive-root factors -/

def rootFactor {K : Type*} [Field K] {p : ℕ} [NeZero p]
    (ζ : K) (a : ZMod p) (X Y : K) : K :=
  X - ζ ^ a.val * Y

def rootPowerSet {K : Type*} [Field K] {p : ℕ} [Fact p.Prime]
    (ζ : K) : Finset K :=
  by
    classical
    exact (nonzeroResidues p).image (fun a : ZMod p => ζ ^ a.val)

theorem rootPowerSet_eq_primitiveRoots
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) :
    rootPowerSet (p := p) ζ = primitiveRoots p K := by
  classical
  have hp : p.Prime := Fact.out
  have hpos : 0 < p := hp.pos
  ext η
  constructor
  · intro hη
    rcases Finset.mem_image.mp hη with ⟨a, ha, rfl⟩
    apply (mem_primitiveRoots hpos).2
    apply hζ.pow_of_coprime a.val
    exact (Nat.coprime_of_lt_prime (n := a.val) (p := p)
      (ZMod.val_ne_zero a |>.2 (Finset.mem_erase.mp ha).1) a.val_lt hp).symm
  · intro hη
    have hη' : IsPrimitiveRoot η p := (mem_primitiveRoots hpos).1 hη
    obtain ⟨i, hi, hpow⟩ := hζ.eq_pow_of_pow_eq_one hη'.pow_eq_one
    have hcop : i.Coprime p := by
      apply (hζ.pow_iff_coprime hpos i).mp
      exact hpow.symm ▸ hη'
    have hi0 : i ≠ 0 := by
      intro hi0
      subst i
      have hpone : p = 1 := by simpa using hcop
      exact hp.ne_one hpone
    let a : ZMod p := i
    have ha0 : a ≠ 0 := by
      intro hz
      apply hi0
      have hv : a.val = 0 := by rw [hz, ZMod.val_zero]
      simpa [a, ZMod.val_cast_of_lt hi] using hv
    have ha : a ∈ nonzeroResidues p := by
      simp only [nonzeroResidues, Finset.mem_erase, Finset.mem_univ]
      constructor
      · exact ha0
      · trivial
    refine Finset.mem_image.2 ⟨a, ha, ?_⟩
    rw [ZMod.val_cast_of_lt hi]
    exact hpow

theorem rootPowerSet_card
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) :
    (rootPowerSet (p := p) ζ).card = p - 1 := by
  rw [rootPowerSet_eq_primitiveRoots ζ hζ]
  simpa [Nat.totient_prime Fact.out] using hζ.card_primitiveRoots

/-! ## Homogeneous prime cyclotomic shell -/

theorem primitiveRoots_product_eq_shell
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (X Y : K) :
    (primitiveRoots p K).prod (fun μ => X - μ * Y) =
      ∑ k ∈ Finset.range p, X ^ k * Y ^ (p - 1 - k) := by
  classical
  have hp : p.Prime := Fact.out
  have hcard : (primitiveRoots p K).card = p - 1 := by
    simpa [Nat.totient_prime hp] using hζ.card_primitiveRoots
  have hpoly :
      Polynomial.cyclotomic p K =
        ∏ μ ∈ primitiveRoots p K, (Polynomial.X - Polynomial.C μ) :=
    Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ
  have hprod :=
    Polynomial.homogenize_finsetProd
      (s := primitiveRoots p K)
      (p := fun μ : K => Polynomial.X - Polynomial.C μ)
      (n := fun _ => 1)
      (by
        intro μ hμ
        simp)
  have hcardone :
      (∑ _μ ∈ primitiveRoots p K, (1 : ℕ)) = p - 1 := by
    simp [hcard]
  have hprod' :
      Polynomial.homogenize
          (∏ μ ∈ primitiveRoots p K, (Polynomial.X - Polynomial.C μ))
          (p - 1) =
        ∏ μ ∈ primitiveRoots p K,
          (MvPolynomial.X 0 - MvPolynomial.C μ * MvPolynomial.X 1) := by
    rw [hcardone] at hprod
    simpa [Polynomial.homogenize_sub, Polynomial.homogenize_X,
      Polynomial.homogenize_C] using hprod
  have hsum :
      Polynomial.homogenize (Polynomial.cyclotomic p K) (p - 1) =
        ∑ k ∈ Finset.range p,
          MvPolynomial.X 0 ^ k * MvPolynomial.X 1 ^ (p - 1 - k) := by
    rw [Polynomial.cyclotomic_prime K p]
    rw [Polynomial.homogenize_finsetSum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k < p := Finset.mem_range.mp hk
    have hk_le : k ≤ p - 1 := by omega
    rw [Polynomial.homogenize_X_pow hk_le]
  have hprod_eval := congrArg (MvPolynomial.eval ![X, Y]) hprod'
  have hsum_eval := congrArg (MvPolynomial.eval ![X, Y]) hsum
  calc
    (primitiveRoots p K).prod (fun μ => X - μ * Y) =
        MvPolynomial.eval ![X, Y]
          (∏ μ ∈ primitiveRoots p K,
            (MvPolynomial.X 0 - MvPolynomial.C μ * MvPolynomial.X 1)) := by simp
    _ = MvPolynomial.eval ![X, Y]
          (Polynomial.homogenize
            (∏ μ ∈ primitiveRoots p K, (Polynomial.X - Polynomial.C μ))
            (p - 1)) := by
      rw [hprod']
    _ = MvPolynomial.eval ![X, Y]
          (Polynomial.homogenize (Polynomial.cyclotomic p K) (p - 1)) := by
      rw [hpoly]
    _ = MvPolynomial.eval ![X, Y]
          (∑ k ∈ Finset.range p,
            MvPolynomial.X 0 ^ k * MvPolynomial.X 1 ^ (p - 1 - k)) := by
      rw [hsum]
    _ = ∑ k ∈ Finset.range p, X ^ k * Y ^ (p - 1 - k) := by
      simp

/-! The exponent image has no repetitions on the nonzero residue classes. -/

theorem rootPowerMap_injective_on_nonzero
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) :
    Set.InjOn (fun a : ZMod p => ζ ^ a.val) (nonzeroResidues p) := by
  intro a ha b hb hab
  apply ZMod.val_injective p
  exact hζ.pow_inj a.val_lt b.val_lt hab

theorem nonzeroRoot_product_eq_shell
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (X Y : K) :
    (nonzeroResidues p).prod (fun a => rootFactor ζ a X Y) =
      ∑ k ∈ Finset.range p, X ^ k * Y ^ (p - 1 - k) := by
  classical
  have hinj := rootPowerMap_injective_on_nonzero ζ hζ
  calc
    (nonzeroResidues p).prod (fun a => rootFactor ζ a X Y) =
        (nonzeroResidues p).prod (fun a => X - ζ ^ a.val * Y) := by
      rfl
    _ = (rootPowerSet (p := p) ζ).prod (fun μ => X - μ * Y) := by
      change (nonzeroResidues p).prod (fun a => X - ζ ^ a.val * Y) =
        ((nonzeroResidues p).image (fun a : ZMod p => ζ ^ a.val)).prod
          (fun μ => X - μ * Y)
      rw [Finset.prod_image hinj]
    _ = (primitiveRoots p K).prod (fun μ => X - μ * Y) := by
      rw [rootPowerSet_eq_primitiveRoots ζ hζ]
    _ = ∑ k ∈ Finset.range p, X ^ k * Y ^ (p - 1 - k) :=
      primitiveRoots_product_eq_shell ζ hζ X Y

/-! ## The exact DkMath QR/QNR shell bridge -/

theorem qr_qnr_product_eq_shell
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (x u : K) :
    (qrFinset p).prod (fun a => rootFactor ζ a (x + u) u) *
        (qnrFinset p).prod (fun a => rootFactor ζ a (x + u) u) =
      GTailCyclotomicShell p x u := by
  rw [qr_product_mul_qnr_product p (fun a => rootFactor ζ a (x + u) u)]
  rw [nonzeroRoot_product_eq_shell ζ hζ]
  rfl

theorem qr_qnr_product_eq_shell_endpoint
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (z y : K) :
    (qrFinset p).prod (fun a => rootFactor ζ a ((z - y) + y) y) *
        (qnrFinset p).prod (fun a => rootFactor ζ a ((z - y) + y) y) =
      GTailCyclotomicShell p (z - y) y := by
  simpa [sub_add_cancel] using qr_qnr_product_eq_shell ζ hζ (z - y) y

#print axioms qr_qnr_disjoint
#print axioms qr_qnr_union
#print axioms qr_product_mul_qnr_product
#print axioms rootPowerSet_eq_primitiveRoots
#print axioms rootPowerSet_card
#print axioms rootPowerMap_injective_on_nonzero
#print axioms primitiveRoots_product_eq_shell
#print axioms nonzeroRoot_product_eq_shell
#print axioms qr_qnr_product_eq_shell
#print axioms qr_qnr_product_eq_shell_endpoint

end

end DkMath.NumberTheory.CyclotomicQRProduct
