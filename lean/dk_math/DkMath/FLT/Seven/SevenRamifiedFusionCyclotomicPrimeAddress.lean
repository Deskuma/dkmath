/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionRealPairCoprimalityNormGate

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicPrimeAddress"

namespace DkMath.FLT.Seven

noncomputable section

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩
set_option maxRecDepth 4000
set_option linter.style.longLine false

namespace RamifiedSignedRootDepthPacket

/-- A prime divisor of the signed quotient root cannot be the ramified
prime seven. -/
theorem quotientPrime_ne_seven
    (p : RamifiedSignedRootDepthPacket)
    {q : ℕ}
    (_hq : Nat.Prime q)
    (hqe : (q : ℤ) ∣ p.quotientRoot) :
    q ≠ 7 := by
  intro hq7
  subst q
  exact p.quotientRoot_not_seven_dvd hqe

/-- The quotient root vanishes in the residue field at any one of its
prime divisors. -/
private theorem quotientRoot_cast_eq_zero
    (p : RamifiedSignedRootDepthPacket)
    {q : ℕ}
    (hqe : (q : ℤ) ∣ p.quotientRoot) :
    (p.quotientRoot : ZMod q) = 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr hqe

/-- The signed seventh quotient vanishes at a prime address of the
integer quotient root. -/
private theorem signedSeventhQuotient_cast_eq_zero
    (p : RamifiedSignedRootDepthPacket)
    {q : ℕ}
    (hqe : (q : ℤ) ∣ p.quotientRoot) :
    (signedSeventhQuotient
        p.signedRightRoot p.signedLeftRoot : ZMod q) = 0 := by
  have h := congrArg (fun z : ℤ => (z : ZMod q))
    p.signedQuotient_eq
  push_cast at h
  rw [p.quotientRoot_cast_eq_zero hqe, mul_zero] at h
  exact h

/-- Neither signed root vanishes at a quotient-prime address.  The
proof uses the quotient polynomial and the integral Bezout identity,
not a choice of a root in the residue field. -/
private theorem signedLeftRoot_cast_ne_zero
    (p : RamifiedSignedRootDepthPacket)
    {q : ℕ}
    (hq : Nat.Prime q)
    (hqe : (q : ℤ) ∣ p.quotientRoot) :
    (p.signedLeftRoot : ZMod q) ≠ 0 := by
  let : Fact (Nat.Prime q) := ⟨hq⟩
  intro hl
  have hquot := p.signedSeventhQuotient_cast_eq_zero hqe
  have hrpow :
      (p.signedRightRoot : ZMod q) ^ 6 = 0 := by
    simpa [signedSeventhQuotient, hl] using hquot
  have hr : (p.signedRightRoot : ZMod q) = 0 :=
    eq_zero_of_pow_eq_zero hrpow
  rcases p.signedRoots_isCoprime with ⟨a, b, hab⟩
  have habq := congrArg (fun z : ℤ => (z : ZMod q)) hab
  push_cast at habq
  rw [hr, hl, mul_zero, mul_zero, zero_add] at habq
  exact zero_ne_one habq

/-- The signed right root is nonzero at the same address. -/
private theorem signedRightRoot_cast_ne_zero
    (p : RamifiedSignedRootDepthPacket)
    {q : ℕ}
    (hq : Nat.Prime q)
    (hqe : (q : ℤ) ∣ p.quotientRoot) :
    (p.signedRightRoot : ZMod q) ≠ 0 := by
  let : Fact (Nat.Prime q) := ⟨hq⟩
  intro hr
  have hquot := p.signedSeventhQuotient_cast_eq_zero hqe
  have hlpow :
      (p.signedLeftRoot : ZMod q) ^ 6 = 0 := by
    simpa [signedSeventhQuotient, hr] using hquot
  have hl : (p.signedLeftRoot : ZMod q) = 0 :=
    eq_zero_of_pow_eq_zero hlpow
  rcases p.signedRoots_isCoprime with ⟨a, b, hab⟩
  have habq := congrArg (fun z : ℤ => (z : ZMod q)) hab
  push_cast at habq
  rw [hr, hl, mul_zero, mul_zero, zero_add] at habq
  exact zero_ne_one habq

/-- The canonical residue-field ratio of the two signed roots. -/
private def quotientPrimeRatioVal
    (p : RamifiedSignedRootDepthPacket)
    {q : ℕ}
    (hq : Nat.Prime q)
    (_hqe : (q : ℤ) ∣ p.quotientRoot) :
    ZMod q := by
  let : Fact (Nat.Prime q) := ⟨hq⟩
  exact
    (p.signedRightRoot : ZMod q) /
      (p.signedLeftRoot : ZMod q)

private theorem quotientPrimeRatioVal_ne_zero
    (p : RamifiedSignedRootDepthPacket)
    {q : ℕ}
    (hq : Nat.Prime q)
    (hqe : (q : ℤ) ∣ p.quotientRoot) :
    p.quotientPrimeRatioVal hq hqe ≠ 0 := by
  let : Fact (Nat.Prime q) := ⟨hq⟩
  exact div_ne_zero
    (p.signedRightRoot_cast_ne_zero hq hqe)
    (p.signedLeftRoot_cast_ne_zero hq hqe)

/-- The canonical multiplicative unit ratio `signedRightRoot /
signedLeftRoot` at a prime divisor of the quotient root. -/
private def quotientPrimeRatio
    (p : RamifiedSignedRootDepthPacket)
    {q : ℕ}
    (hq : Nat.Prime q)
    (hqe : (q : ℤ) ∣ p.quotientRoot) :
    (ZMod q)ˣ := by
  let : Fact (Nat.Prime q) := ⟨hq⟩
  exact
    Units.mk0 (p.quotientPrimeRatioVal hq hqe)
      (p.quotientPrimeRatioVal_ne_zero hq hqe)

private theorem signedRoots_pow_seven_cast_eq
    (p : RamifiedSignedRootDepthPacket)
    {q : ℕ}
    (hqe : (q : ℤ) ∣ p.quotientRoot) :
    (p.signedRightRoot : ZMod q) ^ 7 =
      (p.signedLeftRoot : ZMod q) ^ 7 := by
  have hfactor := congrArg (fun z : ℤ => (z : ZMod q))
    (signed_pow_seven_sub_factorization
      p.signedRightRoot p.signedLeftRoot)
  push_cast at hfactor
  rw [p.signedSeventhQuotient_cast_eq_zero hqe,
    mul_zero] at hfactor
  exact sub_eq_zero.mp hfactor

private theorem quotientPrimeRatio_pow_seven
    (p : RamifiedSignedRootDepthPacket)
    {q : ℕ}
    (hq : Nat.Prime q)
    (hqe : (q : ℤ) ∣ p.quotientRoot) :
    p.quotientPrimeRatio hq hqe ^ 7 = 1 := by
  let : Fact (Nat.Prime q) := ⟨hq⟩
  apply Units.ext
  simp only [quotientPrimeRatio, Units.val_pow_eq_pow_val,
    Units.val_mk0, Units.val_one]
  rw [quotientPrimeRatioVal, div_pow,
    p.signedRoots_pow_seven_cast_eq hqe]
  exact div_self
    (pow_ne_zero 7 (p.signedLeftRoot_cast_ne_zero hq hqe))

/-- The gap root is nonzero at a prime divisor of the coprime quotient
root. -/
private theorem gapRoot_cast_ne_zero
    (p : RamifiedSignedRootDepthPacket)
    {q : ℕ}
    (hq : Nat.Prime q)
    (hqe : (q : ℤ) ∣ p.quotientRoot) :
    (p.gapRoot : ZMod q) ≠ 0 := by
  let : Fact (Nat.Prime q) := ⟨hq⟩
  intro hgap
  rcases p.gapRoot_isCoprime_quotientRoot with ⟨a, b, hab⟩
  have habq := congrArg (fun z : ℤ => (z : ZMod q)) hab
  push_cast at habq
  rw [hgap, p.quotientRoot_cast_eq_zero hqe,
    mul_zero, mul_zero, zero_add] at habq
  exact zero_ne_one habq

private theorem seven_cast_ne_zero_at_quotientPrime
    (p : RamifiedSignedRootDepthPacket)
    {q : ℕ}
    (hq : Nat.Prime q)
    (hqe : (q : ℤ) ∣ p.quotientRoot) :
    (7 : ZMod q) ≠ 0 := by
  let : Fact (Nat.Prime q) := ⟨hq⟩
  intro hseven
  have hdivNat : q ∣ 7 :=
    (ZMod.natCast_eq_zero_iff 7 q).mp hseven
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hdivNat with
    hq1 | hq7
  · exact hq.ne_one hq1
  · exact p.quotientPrime_ne_seven hq hqe hq7

private theorem signedRootGap_cast_ne_zero
    (p : RamifiedSignedRootDepthPacket)
    {q : ℕ}
    (hq : Nat.Prime q)
    (hqe : (q : ℤ) ∣ p.quotientRoot) :
    (p.signedRightRoot : ZMod q) -
      (p.signedLeftRoot : ZMod q) ≠ 0 := by
  let : Fact (Nat.Prime q) := ⟨hq⟩
  have hgap := congrArg (fun z : ℤ => (z : ZMod q))
    p.signedGap_eq
  push_cast at hgap
  rw [hgap]
  rw [show (2401 : ZMod q) = (7 : ZMod q) ^ 4 by norm_num]
  exact mul_ne_zero
    (pow_ne_zero 4
      (p.seven_cast_ne_zero_at_quotientPrime hq hqe))
    (p.gapRoot_cast_ne_zero hq hqe)

private theorem quotientPrimeRatio_ne_one
    (p : RamifiedSignedRootDepthPacket)
    {q : ℕ}
    (hq : Nat.Prime q)
    (hqe : (q : ℤ) ∣ p.quotientRoot) :
    p.quotientPrimeRatio hq hqe ≠ 1 := by
  let : Fact (Nat.Prime q) := ⟨hq⟩
  intro ht
  have htval := congrArg Units.val ht
  simp only [quotientPrimeRatio, Units.val_mk0,
    Units.val_one, quotientPrimeRatioVal] at htval
  have hrl :
      (p.signedRightRoot : ZMod q) =
        (p.signedLeftRoot : ZMod q) := by
    exact (div_eq_one_iff_eq
      (p.signedLeftRoot_cast_ne_zero hq hqe)).mp htval
  exact p.signedRootGap_cast_ne_zero hq hqe
    (sub_eq_zero.mpr hrl)

/-- Every prime divisor of the signed quotient root is one modulo
seven.  The proof records the primitive seventh root supplied by the
signed-root ratio and uses its multiplicative order. -/
theorem prime_dvd_quotientRoot_modSeven_eq_one
    (p : RamifiedSignedRootDepthPacket)
    {q : ℕ}
    (hq : Nat.Prime q)
    (hqe : (q : ℤ) ∣ p.quotientRoot) :
    q % 7 = 1 := by
  let : Fact (Nat.Prime q) := ⟨hq⟩
  let t := p.quotientPrimeRatio hq hqe
  have ht7 : t ^ 7 = 1 :=
    p.quotientPrimeRatio_pow_seven hq hqe
  have ht1 : t ≠ 1 :=
    p.quotientPrimeRatio_ne_one hq hqe
  have htOrder : orderOf t = 7 :=
    orderOf_eq_prime ht7 ht1
  have hdiv : 7 ∣ q - 1 := by
    rw [← htOrder]
    exact ZMod.orderOf_units_dvd_card_sub_one t
  have hmod : q ≡ 1 [MOD 7] :=
    ((Nat.modEq_iff_dvd' hq.one_le).mpr hdiv).symm
  simpa [Nat.ModEq] using hmod

/-- In fact every quotient prime is one modulo fourteen: after the
seventh-cyclotomic congruence it cannot be the even prime. -/
theorem prime_dvd_quotientRoot_modFourteen_eq_one
    (p : RamifiedSignedRootDepthPacket)
    {q : ℕ}
    (hq : Nat.Prime q)
    (hqe : (q : ℤ) ∣ p.quotientRoot) :
    q % 14 = 1 := by
  have hmodSeven :=
    p.prime_dvd_quotientRoot_modSeven_eq_one hq hqe
  have hqTwo : q ≠ 2 := by
    intro h
    rw [h] at hmodSeven
    norm_num at hmodSeven
  rcases hq.odd_of_ne_two hqTwo with ⟨k, hk⟩
  have htwo : 2 ∣ q - 1 := by
    refine ⟨k, ?_⟩
    omega
  have hseven : 7 ∣ q - 1 := by
    have hmod : q ≡ 1 [MOD 7] := by
      simpa [Nat.ModEq] using hmodSeven
    exact (Nat.modEq_iff_dvd' hq.one_le).mp hmod.symm
  have hfourteen : 14 ∣ q - 1 := by
    simpa using
      (show Nat.Coprime 2 7 by norm_num).mul_dvd_of_dvd_of_dvd
        htwo hseven
  have hmod : q ≡ 1 [MOD 14] :=
    ((Nat.modEq_iff_dvd' hq.one_le).mpr hfourteen).symm
  simpa [Nat.ModEq] using hmod

/-- Canonical local address carried by a prime divisor of the signed
quotient root.  Its `ratio` below is definitionally reconstructed from
the two signed roots, rather than stored as arbitrary packet data. -/
structure QuotientPrimeMuSevenAddress
    (p : RamifiedSignedRootDepthPacket) (q : ℕ) : Type where
  prime : Nat.Prime q
  dividesQuotientRoot : (q : ℤ) ∣ p.quotientRoot

namespace QuotientPrimeMuSevenAddress

variable {p : RamifiedSignedRootDepthPacket} {q : ℕ}

/-- The canonical primitive seventh root at this quotient-prime
address. -/
def ratio (a : QuotientPrimeMuSevenAddress p q) :
    (ZMod q)ˣ :=
  p.quotientPrimeRatio a.prime a.dividesQuotientRoot

/-- Multiplying the canonical ratio by the left signed root recovers
the right signed root in the residue field. -/
theorem ratio_mul_signedLeftRoot
    (a : QuotientPrimeMuSevenAddress p q) :
    (a.ratio : ZMod q) *
        (p.signedLeftRoot : ZMod q) =
      (p.signedRightRoot : ZMod q) := by
  let : Fact (Nat.Prime q) := ⟨a.prime⟩
  change
    ((p.signedRightRoot : ZMod q) /
        (p.signedLeftRoot : ZMod q)) *
      (p.signedLeftRoot : ZMod q) =
        (p.signedRightRoot : ZMod q)
  exact div_mul_cancel₀ _
    (p.signedLeftRoot_cast_ne_zero
      a.prime a.dividesQuotientRoot)

theorem ratio_pow_seven
    (a : QuotientPrimeMuSevenAddress p q) :
    a.ratio ^ 7 = 1 :=
  p.quotientPrimeRatio_pow_seven
    a.prime a.dividesQuotientRoot

theorem ratio_ne_one
    (a : QuotientPrimeMuSevenAddress p q) :
    a.ratio ≠ 1 :=
  p.quotientPrimeRatio_ne_one
    a.prime a.dividesQuotientRoot

theorem ratio_orderOf
    (a : QuotientPrimeMuSevenAddress p q) :
    orderOf a.ratio = 7 := by
  let : Fact (Nat.Prime q) := ⟨a.prime⟩
  exact orderOf_eq_prime a.ratio_pow_seven a.ratio_ne_one

theorem prime_ne_seven
    (a : QuotientPrimeMuSevenAddress p q) :
    q ≠ 7 :=
  p.quotientPrime_ne_seven
    a.prime a.dividesQuotientRoot

/-- The inversion-invariant real-pair coordinate attached to the
oriented seventh root ratio. -/
def beta (a : QuotientPrimeMuSevenAddress p q) :
    ZMod q :=
  1 + (a.ratio : ZMod q) + (a.ratio⁻¹ : ZMod q)

/-- The local real-pair coordinate is a root of the defining
discriminant-49 cubic. -/
theorem beta_cubic_relation
    (a : QuotientPrimeMuSevenAddress p q) :
    a.beta ^ 3 - 2 * a.beta ^ 2 - a.beta + 1 = 0 := by
  let : Fact (Nat.Prime q) := ⟨a.prime⟩
  let t : ZMod q := (a.ratio : ZMod q)
  have ht0 : t ≠ 0 := a.ratio.ne_zero
  have ht7 : t ^ 7 = 1 := by
    exact congrArg Units.val a.ratio_pow_seven
  have ht1 : t ≠ 1 := by
    intro ht
    apply a.ratio_ne_one
    exact Units.ext ht
  have hsum :
      t ^ 6 + t ^ 5 + t ^ 4 + t ^ 3 +
          t ^ 2 + t + 1 = 0 := by
    have hprod :
        (t - 1) *
            (t ^ 6 + t ^ 5 + t ^ 4 + t ^ 3 +
              t ^ 2 + t + 1) = 0 := by
      linear_combination ht7
    exact (mul_eq_zero.mp hprod).resolve_left
      (sub_ne_zero.mpr ht1)
  dsimp only [beta]
  change
    (1 + t + t⁻¹) ^ 3 -
        2 * (1 + t + t⁻¹) ^ 2 -
        (1 + t + t⁻¹) + 1 = 0
  field_simp [ht0]
  linear_combination hsum

/-- The real-pair coordinate is not the ramified root `3`; evaluating
the cubic there would make seven vanish at a non-seven prime. -/
theorem beta_ne_three
    (a : QuotientPrimeMuSevenAddress p q) :
    a.beta ≠ 3 := by
  let : Fact (Nat.Prime q) := ⟨a.prime⟩
  intro hbeta
  have hrel := a.beta_cubic_relation
  rw [hbeta] at hrel
  norm_num at hrel
  exact
    p.seven_cast_ne_zero_at_quotientPrime
      a.prime a.dividesQuotientRoot hrel

/-- Evaluation of the real cubic order at the local real-pair
coordinate `beta`.  The multiplication proof is exactly the defining
cubic relation, expanded in the integral coordinate basis. -/
def evalAlphaRoot
    (a : QuotientPrimeMuSevenAddress p q) :
    SevenRealCubicInt →+* ZMod q where
  toFun x :=
    (x.fst : ZMod q) +
      (x.snd : ZMod q) * a.beta +
      (x.thd : ZMod q) * a.beta ^ 2
  map_zero' := by
    norm_num
  map_one' := by
    norm_num
  map_add' := by
    intro x y
    simp only [SevenRealCubicInt.fst_add,
      SevenRealCubicInt.snd_add,
      SevenRealCubicInt.thd_add, Int.cast_add]
    ring
  map_mul' := by
    intro x y
    rcases x with ⟨x0, x1, x2⟩
    rcases y with ⟨y0, y1, y2⟩
    simp only [SevenRealCubicInt.fst_mul,
      SevenRealCubicInt.snd_mul,
      SevenRealCubicInt.thd_mul,
      Int.cast_sub, Int.cast_mul, Int.cast_add,
      Int.cast_ofNat]
    linear_combination
      -((x1 : ZMod q) * (y2 : ZMod q) +
          (x2 : ZMod q) * (y1 : ZMod q) +
          (x2 : ZMod q) * (y2 : ZMod q) * a.beta +
          2 * (x2 : ZMod q) * (y2 : ZMod q)) *
        a.beta_cubic_relation

@[simp] theorem evalAlphaRoot_apply
    (a : QuotientPrimeMuSevenAddress p q)
    (x : SevenRealCubicInt) :
    a.evalAlphaRoot x =
      (x.fst : ZMod q) +
        (x.snd : ZMod q) * a.beta +
        (x.thd : ZMod q) * a.beta ^ 2 :=
  rfl

@[simp] theorem evalAlphaRoot_alpha
    (a : QuotientPrimeMuSevenAddress p q) :
    a.evalAlphaRoot SevenRealCubicInt.alpha = a.beta := by
  norm_num [evalAlphaRoot, SevenRealCubicInt.alpha]

@[simp] theorem evalAlphaRoot_eisensteinAxis
    (a : QuotientPrimeMuSevenAddress p q) :
    a.evalAlphaRoot SevenRealCubicInt.eisensteinAxis =
      a.beta - 3 := by
  norm_num [evalAlphaRoot, SevenRealCubicInt.eisensteinAxis]
  ring

/-- The zeroth real-pair carrier vanishes at the local address selected
by the signed-root ratio. -/
theorem evalAlphaRoot_realPairCarrier_zero
    (a : QuotientPrimeMuSevenAddress p q) :
    a.evalAlphaRoot (p.realPairCarrier 0) = 0 := by
  let : Fact (Nat.Prime q) := ⟨a.prime⟩
  let r : ZMod q := (p.signedRightRoot : ZMod q)
  let l : ZMod q := (p.signedLeftRoot : ZMod q)
  let t : ZMod q := (a.ratio : ZMod q)
  have hratio : t * l = r := by
    exact a.ratio_mul_signedLeftRoot
  have htinv : (a.ratio⁻¹ : ZMod q) * t = 1 := by
    change
      (a.ratio⁻¹ : ZMod q) * (a.ratio : ZMod q) = 1
    exact Units.inv_mul' a.ratio
  simp only [RamifiedSignedRootDepthPacket.realPairCarrier,
    SevenRealCubicInt.cyclicAlpha, ite_eq_left, map_sub, map_add,
    map_mul, map_pow, map_intCast, a.evalAlphaRoot_alpha]
  change
    r ^ 2 + r * l + l ^ 2 -
      a.beta * (r * l) = 0
  rw [← hratio]
  dsimp only [beta]
  change
    (t * l) ^ 2 + (t * l) * l + l ^ 2 -
      (1 + t + (a.ratio⁻¹ : ZMod q)) *
        ((t * l) * l) = 0
  linear_combination -(l ^ 2) * htinv

/-- Evaluated form of the exact carrier identity
`P₀ = l² * ratio * (beta - alpha)`. -/
theorem evalAlphaRoot_realPairCarrier_ratio_identity
    (a : QuotientPrimeMuSevenAddress p q) :
    a.evalAlphaRoot (p.realPairCarrier 0) =
      (p.signedLeftRoot : ZMod q) ^ 2 *
        (a.ratio : ZMod q) *
        (a.beta -
          a.evalAlphaRoot SevenRealCubicInt.alpha) := by
  rw [a.evalAlphaRoot_realPairCarrier_zero,
    a.evalAlphaRoot_alpha]
  ring

/-- Since the ramified axis evaluates to the nonzero element
`beta - 3`, vanishing of the carrier descends to its normalized
real-pair core. -/
theorem evalAlphaRoot_realPairCore_zero
    (a : QuotientPrimeMuSevenAddress p q) :
    a.evalAlphaRoot (p.realPairCore 0) = 0 := by
  let : Fact (Nat.Prime q) := ⟨a.prime⟩
  have hfactor := congrArg a.evalAlphaRoot
    (p.realPairCarrier_eq_eisensteinAxis_mul_core 0)
  rw [map_mul, a.evalAlphaRoot_realPairCarrier_zero,
    a.evalAlphaRoot_eisensteinAxis] at hfactor
  exact
    (mul_eq_zero.mp hfactor.symm).resolve_left
      (sub_ne_zero.mpr a.beta_ne_three)

/-- The normalized zeroth core belongs to the explicit residue-field
kernel selected by the quotient-prime ratio. -/
theorem realPairCore_mem_evalAlphaRoot_ker
    (a : QuotientPrimeMuSevenAddress p q) :
    p.realPairCore 0 ∈ RingHom.ker a.evalAlphaRoot := by
  exact a.evalAlphaRoot_realPairCore_zero

/-- The ramified axis is not in that kernel, so carrier vanishing
really addresses the normalized core rather than the prime above
seven. -/
theorem eisensteinAxis_not_mem_evalAlphaRoot_ker
    (a : QuotientPrimeMuSevenAddress p q) :
    SevenRealCubicInt.eisensteinAxis ∉
      RingHom.ker a.evalAlphaRoot := by
  rw [RingHom.mem_ker, a.evalAlphaRoot_eisensteinAxis]
  exact sub_ne_zero.mpr a.beta_ne_three

end QuotientPrimeMuSevenAddress

end RamifiedSignedRootDepthPacket

end

end DkMath.FLT.Seven
