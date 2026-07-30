/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicLinearPrimeAddress

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicConjugatePrimePair"

namespace DkMath.FLT.Seven

noncomputable section

set_option linter.style.longLine false

namespace SevenCyclotomicDegreeSixInt

/-- Quadratic conjugation exchanges the two displayed seventh roots. -/
@[simp] theorem star_zeta :
    star zeta = zetaInv := by
  ext <;> simp [zeta, zetaInv]

/-- The inverse-root orientation conjugates back to `zeta`. -/
@[simp] theorem star_zetaInv :
    star zetaInv = zeta := by
  rw [← star_zeta, star_star]

/-- The real cubic suborder is pointwise fixed by quadratic conjugation. -/
@[simp] theorem star_ofReal (x : SevenRealCubicInt) :
    star (ofReal x) = ofReal x := by
  ext <;> simp [ofReal, QuadraticAlgebra.algebraMap_eq]

end SevenCyclotomicDegreeSixInt

namespace RamifiedSignedRootDepthPacket

open SevenCyclotomicDegreeSixInt

/-- Quadratic conjugation exchanges the two oriented linear carriers. -/
@[simp] theorem star_cyclotomicDegreeSixCarrier
    (p : RamifiedSignedRootDepthPacket) :
    star p.cyclotomicDegreeSixCarrier =
      p.cyclotomicDegreeSixCarrierConj := by
  simp only [cyclotomicDegreeSixCarrier,
    cyclotomicDegreeSixCarrierConj, star_sub, star_mul,
    star_ofReal, star_zeta]
  rw [mul_comm]

/-- The reverse exchange of the conjugate linear carrier. -/
@[simp] theorem star_cyclotomicDegreeSixCarrierConj
    (p : RamifiedSignedRootDepthPacket) :
    star p.cyclotomicDegreeSixCarrierConj =
      p.cyclotomicDegreeSixCarrier := by
  simp only [cyclotomicDegreeSixCarrier,
    cyclotomicDegreeSixCarrierConj, star_sub, star_mul,
    star_ofReal, star_zetaInv]
  rw [mul_comm]

end RamifiedSignedRootDepthPacket

namespace RamifiedSignedRootRoutingPacket

open SevenCyclotomicDegreeSixInt

namespace CyclotomicLinearPrimeAddress

variable {p : RamifiedSignedRootRoutingPacket} {q : ℕ}

/-- The conjugate degree-six evaluation, obtained by precomposing the
oriented evaluation with the quadratic star automorphism. -/
def conjugateEval
    (a : CyclotomicLinearPrimeAddress p q) :
    SevenCyclotomicDegreeSixInt.Ring →+* ZMod q :=
  a.eval.comp
    (starRingEnd SevenCyclotomicDegreeSixInt.Ring)

/-- The second degree-one prime above the same real-cubic address. -/
def conjugateEvalKernel
    (a : CyclotomicLinearPrimeAddress p q) :
    Ideal SevenCyclotomicDegreeSixInt.Ring :=
  RingHom.ker a.conjugateEval

/-- The conjugate linear factor belongs to the second kernel. -/
theorem conjugateCarrier_mem_conjugateEvalKernel
    (a : CyclotomicLinearPrimeAddress p q) :
    p.signedDepth.cyclotomicDegreeSixCarrierConj ∈
      a.conjugateEvalKernel := by
  change
    a.eval
      (star p.signedDepth.cyclotomicDegreeSixCarrierConj) = 0
  rw [p.signedDepth.star_cyclotomicDegreeSixCarrierConj]
  exact a.eval_cyclotomicDegreeSixCarrier_zero

/-- The original orientation is excluded from the conjugate kernel. -/
theorem carrier_not_mem_conjugateEvalKernel
    (a : CyclotomicLinearPrimeAddress p q) :
    p.signedDepth.cyclotomicDegreeSixCarrier ∉
      a.conjugateEvalKernel := by
  change
    a.eval
      (star p.signedDepth.cyclotomicDegreeSixCarrier) ≠ 0
  rw [p.signedDepth.star_cyclotomicDegreeSixCarrier]
  exact a.eval_cyclotomicDegreeSixCarrierConj_ne_zero

/-- The conjugate evaluation is surjective.  Quadratic conjugation fixes
the embedded constants used by the first evaluation's surjectivity proof. -/
theorem conjugateEval_surjective
    (a : CyclotomicLinearPrimeAddress p q) :
    Function.Surjective a.conjugateEval := by
  letI : Fact (Nat.Prime q) := ⟨a.quotientAddress.prime⟩
  intro z
  refine
    ⟨SevenCyclotomicDegreeSixInt.ofReal
        (z.val : SevenRealCubicInt), ?_⟩
  change
    a.eval
      (star
        (SevenCyclotomicDegreeSixInt.ofReal
          (z.val : SevenRealCubicInt))) = z
  rw [SevenCyclotomicDegreeSixInt.star_ofReal]
  rw [eval, SevenCyclotomicDegreeSixInt.localEval_ofReal]
  simpa only [map_natCast] using ZMod.natCast_zmod_val z

/-- The conjugate kernel is maximal. -/
theorem conjugateEvalKernel_isMaximal
    (a : CyclotomicLinearPrimeAddress p q) :
    a.conjugateEvalKernel.IsMaximal := by
  letI : Fact (Nat.Prime q) := ⟨a.quotientAddress.prime⟩
  exact RingHom.ker_isMaximal_of_surjective
    a.conjugateEval a.conjugateEval_surjective

/-- The two oriented degree-six kernels are distinct. -/
theorem evalKernel_ne_conjugateEvalKernel
    (a : CyclotomicLinearPrimeAddress p q) :
    a.evalKernel ≠ a.conjugateEvalKernel := by
  intro heq
  exact a.carrier_not_mem_conjugateEvalKernel
    (heq ▸ a.cyclotomicDegreeSixCarrier_mem_evalKernel)

/-- Distinct maximal conjugate primes are comaximal. -/
theorem evalKernel_sup_conjugateEvalKernel
    (a : CyclotomicLinearPrimeAddress p q) :
    a.evalKernel ⊔ a.conjugateEvalKernel = ⊤ :=
  a.evalKernel_isMaximal.coprime_of_ne
    a.conjugateEvalKernel_isMaximal
    a.evalKernel_ne_conjugateEvalKernel

/-- Both conjugate degree-six primes contract to the same real-cubic
`beta`-evaluation kernel. -/
theorem conjugateEvalKernel_comap_ofReal
    (a : CyclotomicLinearPrimeAddress p q) :
    Ideal.comap SevenCyclotomicDegreeSixInt.ofReal
        a.conjugateEvalKernel =
      RingHom.ker a.quotientAddress.evalAlphaRoot := by
  ext x
  change
    a.eval
        (star (SevenCyclotomicDegreeSixInt.ofReal x)) = 0 ↔
      a.quotientAddress.evalAlphaRoot x = 0
  rw [SevenCyclotomicDegreeSixInt.star_ofReal,
    eval, SevenCyclotomicDegreeSixInt.localEval_ofReal]

/-- The conjugate prime has the same rational contraction `(q)`. -/
theorem conjugateEvalKernel_comap_intCast
    (a : CyclotomicLinearPrimeAddress p q) :
    Ideal.comap
        (Int.castRingHom SevenCyclotomicDegreeSixInt.Ring)
        a.conjugateEvalKernel =
      Ideal.span ({(q : ℤ)} : Set ℤ) := by
  ext z
  rw [Ideal.mem_comap, Ideal.mem_span_singleton]
  change
    a.eval
        (star
          (SevenCyclotomicDegreeSixInt.ofReal
            (z : SevenRealCubicInt))) = 0 ↔
      (q : ℤ) ∣ z
  rw [SevenCyclotomicDegreeSixInt.star_ofReal,
    eval, SevenCyclotomicDegreeSixInt.localEval_ofReal,
    map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- The conjugate residue quotient also has exactly `q` elements. -/
theorem conjugateEvalKernel_cardQuot
    (a : CyclotomicLinearPrimeAddress p q) :
    Submodule.cardQuot a.conjugateEvalKernel = q := by
  letI : Fact (Nat.Prime q) := ⟨a.quotientAddress.prime⟩
  rw [Submodule.cardQuot_apply]
  calc
    Nat.card
        (SevenCyclotomicDegreeSixInt.Ring ⧸
          a.conjugateEvalKernel) =
        Nat.card (ZMod q) :=
      Nat.card_congr
        (RingHom.quotientKerEquivOfSurjective
          a.conjugateEval_surjective).toEquiv
    _ = q := Nat.card_zmod q

/-- Extension of the common real-cubic prime to the degree-six carrier. -/
def realPrimeFiberIdeal
    (a : CyclotomicLinearPrimeAddress p q) :
    Ideal SevenCyclotomicDegreeSixInt.Ring :=
  Ideal.map SevenCyclotomicDegreeSixInt.ofReal
    (RingHom.ker a.quotientAddress.evalAlphaRoot)

/-- The extended real prime is contained in the product of its two
comaximal conjugate degree-one primes. -/
theorem realPrimeFiberIdeal_le_conjugateProduct
    (a : CyclotomicLinearPrimeAddress p q) :
    a.realPrimeFiberIdeal ≤
      a.evalKernel * a.conjugateEvalKernel := by
  have hleft :
      a.realPrimeFiberIdeal ≤ a.evalKernel := by
    rw [realPrimeFiberIdeal, Ideal.map_le_iff_le_comap,
      a.evalKernel_comap_ofReal]
  have hright :
      a.realPrimeFiberIdeal ≤ a.conjugateEvalKernel := by
    rw [realPrimeFiberIdeal, Ideal.map_le_iff_le_comap,
      a.conjugateEvalKernel_comap_ofReal]
  rw [Ideal.mul_eq_inf_of_coprime
    a.evalKernel_sup_conjugateEvalKernel]
  exact le_inf hleft hright

/-- Exact remaining ideal-fibre obligation.  The proved inclusion is the
extension-to-product direction; the reverse inclusion requires an explicit
description of the extended quadratic fibre or an equivalent finite-index
calculation. -/
def ConjugatePrimeFiberProductEqualityObligation
    (a : CyclotomicLinearPrimeAddress p q) : Prop :=
  a.realPrimeFiberIdeal =
    a.evalKernel * a.conjugateEvalKernel

/-- Because the forward inclusion is already proved, the fibre-product
equality is equivalent to precisely one reverse containment. -/
theorem conjugatePrimeFiberProductEqualityObligation_iff
    (a : CyclotomicLinearPrimeAddress p q) :
    a.ConjugatePrimeFiberProductEqualityObligation ↔
      a.evalKernel * a.conjugateEvalKernel ≤
        a.realPrimeFiberIdeal := by
  constructor
  · intro h
    rw [← h]
  · intro h
    exact le_antisymm
      a.realPrimeFiberIdeal_le_conjugateProduct h

/-- Complete conjugate-prime-pair packet at one canonical quotient prime. -/
theorem conjugatePrimePair_packet
    (a : CyclotomicLinearPrimeAddress p q) :
    a.evalKernel.IsMaximal ∧
      a.conjugateEvalKernel.IsMaximal ∧
      a.evalKernel ≠ a.conjugateEvalKernel ∧
      a.evalKernel ⊔ a.conjugateEvalKernel = ⊤ ∧
      Ideal.comap SevenCyclotomicDegreeSixInt.ofReal a.evalKernel =
        RingHom.ker a.quotientAddress.evalAlphaRoot ∧
      Ideal.comap SevenCyclotomicDegreeSixInt.ofReal
          a.conjugateEvalKernel =
        RingHom.ker a.quotientAddress.evalAlphaRoot ∧
      Ideal.comap
          (Int.castRingHom SevenCyclotomicDegreeSixInt.Ring)
          a.evalKernel =
        Ideal.span ({(q : ℤ)} : Set ℤ) ∧
      Ideal.comap
          (Int.castRingHom SevenCyclotomicDegreeSixInt.Ring)
          a.conjugateEvalKernel =
        Ideal.span ({(q : ℤ)} : Set ℤ) ∧
      Submodule.cardQuot a.evalKernel = q ∧
      Submodule.cardQuot a.conjugateEvalKernel = q :=
  ⟨a.evalKernel_isMaximal,
    a.conjugateEvalKernel_isMaximal,
    a.evalKernel_ne_conjugateEvalKernel,
    a.evalKernel_sup_conjugateEvalKernel,
    a.evalKernel_comap_ofReal,
    a.conjugateEvalKernel_comap_ofReal,
    a.evalKernel_comap_intCast,
    a.conjugateEvalKernel_comap_intCast,
    a.evalKernel_cardQuot,
    a.conjugateEvalKernel_cardQuot⟩

end CyclotomicLinearPrimeAddress

end RamifiedSignedRootRoutingPacket

#print axioms SevenCyclotomicDegreeSixInt.star_zeta
#print axioms
  RamifiedSignedRootRoutingPacket.CyclotomicLinearPrimeAddress.evalKernel_ne_conjugateEvalKernel
#print axioms
  RamifiedSignedRootRoutingPacket.CyclotomicLinearPrimeAddress.evalKernel_sup_conjugateEvalKernel
#print axioms
  RamifiedSignedRootRoutingPacket.CyclotomicLinearPrimeAddress.conjugateEvalKernel_comap_ofReal
#print axioms
  RamifiedSignedRootRoutingPacket.CyclotomicLinearPrimeAddress.conjugateEvalKernel_comap_intCast
#print axioms
  RamifiedSignedRootRoutingPacket.CyclotomicLinearPrimeAddress.conjugateEvalKernel_cardQuot
#print axioms
  RamifiedSignedRootRoutingPacket.CyclotomicLinearPrimeAddress.realPrimeFiberIdeal_le_conjugateProduct
#print axioms
  RamifiedSignedRootRoutingPacket.CyclotomicLinearPrimeAddress.conjugatePrimePair_packet

end

end DkMath.FLT.Seven
