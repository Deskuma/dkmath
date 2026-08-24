/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.QuotientSupport

#print "file: DkMath.NumberTheory.Legendre.SmallCofactor"

/-!
## SmallCofactor

This module identifies two finite factorizations of a coprime square-cell
point.  The generic Primitive layer removes a possible fresh prime
`ℓ > n` first and leaves a bounded old-generated cofactor `k ≤ n`.  The
Legendre quotient layer removes an old support prime `p ≤ n` first and leaves
a quotient above the anchor.  Under a specified fresh split these are the
same factor geometry, with

```text
squareOffsetSupportQuotient n p r = ℓ * (k / p).
```

Consequently the L016 singleton-support/depth-one condition is exactly
`k = p`.  All freshness here is relative to the finite world
`primeScalesUpTo n`; this module does not assert a fresh factor exists for
every square point, does not use Zsigmondy or `PrimitiveBeam` origin, and does
not prove Legendre's conjecture.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic

/-! ### PRIM-L022.1: square-point bounds and coprimality -/

/-- A square offset point lies in the generic square Body at its anchor. -/
theorem squarePoint_le_squareBody_of_squareOffset
    {n r : ℕ}
    (hr : SquareOffset n r) :
    n ^ 2 + r ≤ squareBody n := by
  dsimp [SquareOffset] at hr
  dsimp [squareBody]
  omega

/-- A positive square offset point is positive. -/
theorem squarePoint_pos_of_squareOffset
    {n r : ℕ}
    (hr : SquareOffset n r) :
    0 < n ^ 2 + r := by
  dsimp [SquareOffset] at hr
  omega

/-- Coprimality of the offset transfers to its anchored square point. -/
theorem coprime_anchor_squarePoint_of_coprimeOffset
    {n r : ℕ}
    (hr : r ∈ squareAnchorCoprimeOffsets n) :
    Nat.Coprime n (n ^ 2 + r) := by
  have hr' := mem_squareAnchorCoprimeOffsets.mp hr
  have hpoint : Nat.Coprime n (n ^ 2 + r) ↔ Nat.Coprime n r := by
    simpa only [pow_two] using Nat.coprime_mul_left_add_right n r n
  exact hpoint.mpr hr'.2

/-! ### PRIM-L022.2: the generic fresh split on one square offset -/

/-- Apply the generic small-cofactor dichotomy to one square offset. -/
theorem squareOffset_oldGenerated_or_uniqueFresh_small_split
    {n r : ℕ}
    (hr : SquareOffset n r) :
    PrimeScaleGeneratedBy (primeScalesUpTo n) (n ^ 2 + r) ∨
      ∃ ℓ k,
        Nat.Prime ℓ ∧
        n < ℓ ∧
        0 < k ∧
        k ≤ n ∧
        FreshPrimeDirection (primeScalesUpTo n) (n ^ 2 + r) ℓ ∧
        ℓ * k = n ^ 2 + r ∧
        PrimeScaleGeneratedBy (primeScalesUpTo n) k ∧
        Nat.Coprime ℓ k ∧
        (∀ ⦃q : ℕ⦄,
          FreshPrimeDirection (primeScalesUpTo n) (n ^ 2 + r) q → q = ℓ) := by
  exact primeScaleGeneratedBy_or_uniqueFresh_small_split_of_le_squareBody
    (squarePoint_pos_of_squareOffset hr)
    (squarePoint_le_squareBody_of_squareOffset hr)

/-- A fresh small cofactor on a coprime seat is a canonical base offset. -/
theorem smallCofactor_mem_coprimeBase_of_fresh_split
    {n r ℓ k : ℕ}
    (hr : r ∈ squareAnchorCoprimeOffsets n)
    (hkpos : 0 < k)
    (hkLe : k ≤ n)
    (hfac : ℓ * k = n ^ 2 + r) :
    k ∈ squareAnchorCoprimeBaseOffsets n := by
  have hpointcop := coprime_anchor_squarePoint_of_coprimeOffset hr
  have hkdiv : k ∣ n ^ 2 + r := by
    rw [← hfac]
    exact dvd_mul_left k ℓ
  have hkcop : Nat.Coprime n k :=
    Nat.Coprime.of_dvd_right hkdiv hpointcop
  exact mem_squareAnchorCoprimeBaseOffsets.mpr ⟨by omega, hkLe, hkcop⟩

/-! ### PRIM-L022.3: old support transfer and the dual quotient -/

/-- An old nondivisor support prime divides the bounded fresh cofactor. -/
theorem selectedSupport_dvd_smallCofactor_of_fresh_split
    {n p r ℓ k : ℕ}
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r)
    (hℓ : Nat.Prime ℓ)
    (hℓlarge : n < ℓ)
    (hfac : ℓ * k = n ^ 2 + r) :
    p ∣ k := by
  have hp' := mem_squareOffsetAnchorNondivisorSupport.mp hp
  have hprod : p ∣ ℓ * k := by
    rw [hfac]
    exact hp'.2.2.2
  rcases (Nat.Prime.dvd_mul hp'.1).mp hprod with hpℓ | hpk
  · have hpeq : p = ℓ :=
      ((Nat.dvd_prime hℓ).mp hpℓ).resolve_left hp'.1.ne_one
    omega
  · exact hpk

/-- The old-prime quotient is the fresh prime times the residual small factor. -/
theorem squareOffsetSupportQuotient_eq_fresh_mul_smallResidual
    {n p r ℓ k : ℕ}
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r)
    (hℓ : Nat.Prime ℓ)
    (hℓlarge : n < ℓ)
    (hfac : ℓ * k = n ^ 2 + r) :
    squareOffsetSupportQuotient n p r = ℓ * (k / p) := by
  have hp' := mem_squareOffsetAnchorNondivisorSupport.mp hp
  have hpk := selectedSupport_dvd_smallCofactor_of_fresh_split
    hp hℓ hℓlarge hfac
  have hpointfac := mul_squareOffsetSupportQuotient_eq hp'.2.2.2
  have hkfac : p * (k / p) = k := Nat.mul_div_cancel' hpk
  have hres : p * (ℓ * (k / p)) = n ^ 2 + r := by
    calc
      p * (ℓ * (k / p)) = ℓ * (p * (k / p)) := by ring
      _ = ℓ * k := by rw [hkfac]
      _ = n ^ 2 + r := hfac
  apply Nat.eq_of_mul_eq_mul_left hp'.1.pos
  exact hpointfac.trans hres.symm

/-! ### PRIM-L022.4: the compressed prime criterion -/

/-- The quotient is prime exactly when the bounded cofactor is the selected prime. -/
theorem prime_squareOffsetSupportQuotient_iff_smallCofactor_eq_selectedPrime
    {n p r ℓ k : ℕ}
    (_hn : 0 < n)
    (_hr : r ∈ squareAnchorCoprimeOffsets n)
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r)
    (hℓ : Nat.Prime ℓ)
    (hℓlarge : n < ℓ)
    (hfac : ℓ * k = n ^ 2 + r) :
    Nat.Prime (squareOffsetSupportQuotient n p r) ↔ k = p := by
  have hp' := mem_squareOffsetAnchorNondivisorSupport.mp hp
  have hpk := selectedSupport_dvd_smallCofactor_of_fresh_split
    hp hℓ hℓlarge hfac
  have hdual := squareOffsetSupportQuotient_eq_fresh_mul_smallResidual
    hp hℓ hℓlarge hfac
  constructor
  · intro hqprime
    have hℓdiv : ℓ ∣ squareOffsetSupportQuotient n p r := by
      rw [hdual]
      exact dvd_mul_right ℓ (k / p)
    have hℓq : ℓ = squareOffsetSupportQuotient n p r :=
      ((Nat.dvd_prime hqprime).mp hℓdiv).resolve_left hℓ.ne_one
    have hres : ℓ * (k / p) = ℓ := by
      calc
        ℓ * (k / p) = squareOffsetSupportQuotient n p r := hdual.symm
        _ = ℓ := hℓq.symm
    have hresone : k / p = 1 := by
      apply Nat.eq_of_mul_eq_mul_left hℓ.pos
      exact hres.trans (by simp)
    have hpkfac : p * (k / p) = k := Nat.mul_div_cancel' hpk
    have hpk_eq : p = k := by simpa [hresone] using hpkfac
    exact hpk_eq.symm
  · intro hkp
    rw [hdual, hkp, Nat.div_self hp'.1.pos]
    simpa using hℓ

/-- L016 singleton support and depth one are exactly `k = p`. -/
theorem singleton_support_and_depth_one_iff_smallCofactor_eq_selectedPrime
    {n p r ℓ k : ℕ}
    (hn : 0 < n)
    (hr : r ∈ squareAnchorCoprimeOffsets n)
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r)
    (hℓ : Nat.Prime ℓ)
    (hℓlarge : n < ℓ)
    (hfac : ℓ * k = n ^ 2 + r) :
    (squareOffsetAnchorNondivisorSupport n r = {p} ∧
      ¬ p ^ 2 ∣ n ^ 2 + r) ↔
      k = p := by
  exact (prime_squareOffsetSupportQuotient_iff_singleton_support_and_depth_one
    hn hr hp).symm.trans
    (prime_squareOffsetSupportQuotient_iff_smallCofactor_eq_selectedPrime
      hn hr hp hℓ hℓlarge hfac)

/-! ### PRIM-L022.5: the covered fresh branch -/

/-- A covered fresh split has a nontrivial bounded cofactor. -/
theorem two_le_smallCofactor_of_covered_fresh_split
    {n r ℓ k : ℕ}
    (_hr : SquareOffset n r)
    (hcovered : SquareOffsetCovered n r)
    (hℓ : Nat.Prime ℓ)
    (hℓlarge : n < ℓ)
    (hkpos : 0 < k)
    (hfac : ℓ * k = n ^ 2 + r) :
    2 ≤ k := by
  obtain ⟨p, hp, hpLe, hpdiv⟩ :=
    squareOffsetCovered_iff_exists_prime_dvd.mp hcovered
  have hpk : p ∣ k := by
    have hprod : p ∣ ℓ * k := by
      rw [hfac]
      exact hpdiv
    rcases (Nat.Prime.dvd_mul hp).mp hprod with hpℓ | hpk
    · have hpeq : p = ℓ :=
        ((Nat.dvd_prime hℓ).mp hpℓ).resolve_left hp.ne_one
      omega
    · exact hpk
  have hpkle : p ≤ k := Nat.le_of_dvd hkpos hpk
  exact le_trans hp.two_le hpkle

/-! ### PRIM-L022.6: the full-cover coprime-seat normal form -/

/--
Under full cover, a coprime square seat is either old-generated or has one
unique fresh prime, a nontrivial bounded cofactor, and a canonical coprime
base cofactor.  This is a necessary finite normal form, not a contradiction
and not a proof that the old-generated branch is impossible.
-/
theorem oldGenerated_or_uniqueFresh_nontrivialSmall_of_fullyCovered
    {n r : ℕ}
    (_hn : 0 < n)
    (hr : r ∈ squareAnchorCoprimeOffsets n)
    (hfull : SquareOffsetsFullyCovered n) :
    PrimeScaleGeneratedBy (primeScalesUpTo n) (n ^ 2 + r) ∨
      ∃ ℓ k,
        Nat.Prime ℓ ∧
        n < ℓ ∧
        2 ≤ k ∧
        k ≤ n ∧
        k ∈ squareAnchorCoprimeBaseOffsets n ∧
        FreshPrimeDirection (primeScalesUpTo n) (n ^ 2 + r) ℓ ∧
        ℓ * k = n ^ 2 + r ∧
        PrimeScaleGeneratedBy (primeScalesUpTo n) k ∧
        Nat.Coprime ℓ k ∧
    (∀ ⦃q : ℕ⦄,
      FreshPrimeDirection (primeScalesUpTo n) (n ^ 2 + r) q → q = ℓ) := by
  have hr' := mem_squareAnchorCoprimeOffsets.mp hr
  rcases squareOffset_oldGenerated_or_uniqueFresh_small_split
      hr'.1 with hgen | ⟨ℓ, k, hℓ, hℓlarge, hkpos, hkLe, hfresh, hfac,
        hkgen, hcop, huniq⟩
  · exact Or.inl hgen
  · have hcovered : SquareOffsetCovered n r := hfull r hr'.1
    have hkbase := smallCofactor_mem_coprimeBase_of_fresh_split
      hr hkpos hkLe hfac
    have hk2 := two_le_smallCofactor_of_covered_fresh_split
      hr'.1 hcovered hℓ hℓlarge hkpos hfac
    exact Or.inr ⟨ℓ, k, hℓ, hℓlarge, hk2, hkLe, hkbase, hfresh,
      hfac, hkgen, hcop, huniq⟩

end DkMath.NumberTheory.Legendre
