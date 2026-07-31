/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicDegreeSixCarrier
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicLinearPrimeAddress"

namespace DkMath.FLT.Seven

noncomputable section

set_option linter.style.longLine false

namespace RamifiedSignedRootRoutingPacket

open SevenCyclotomicDegreeSixInt

/-- An oriented degree-six prime address above a canonical prime divisor of
the signed quotient root.  The underlying real-pair address is not chosen
again: it is exactly the canonical signed-root ratio already constructed in
FUSION-003F. -/
structure CyclotomicLinearPrimeAddress
    (p : RamifiedSignedRootRoutingPacket) (q : ℕ) where
  quotientAddress :
    p.signedDepth.QuotientPrimeMuSevenAddress q

/-- Canonical wrapper for any proved quotient-prime address. -/
def cyclotomicLinearPrimeAddress
    (p : RamifiedSignedRootRoutingPacket)
    {q : ℕ}
    (a : p.signedDepth.QuotientPrimeMuSevenAddress q) :
    CyclotomicLinearPrimeAddress p q :=
  ⟨a⟩

namespace CyclotomicLinearPrimeAddress

variable {p : RamifiedSignedRootRoutingPacket} {q : ℕ}

/-- The oriented degree-six residue-field evaluation. -/
def eval
    (a : CyclotomicLinearPrimeAddress p q) :
    SevenCyclotomicDegreeSixInt.Ring →+* ZMod q :=
  SevenCyclotomicDegreeSixInt.localEval a.quotientAddress

/-- The degree-one prime ideal selected by the canonical oriented ratio. -/
def evalKernel
    (a : CyclotomicLinearPrimeAddress p q) :
    Ideal SevenCyclotomicDegreeSixInt.Ring :=
  RingHom.ker a.eval

/-- The explicit oriented linear carrier vanishes at its canonical
degree-six address. -/
theorem eval_cyclotomicDegreeSixCarrier_zero
    (a : CyclotomicLinearPrimeAddress p q) :
    a.eval p.signedDepth.cyclotomicDegreeSixCarrier = 0 := by
  rw [eval, RamifiedSignedRootDepthPacket.cyclotomicDegreeSixCarrier,
    map_sub, map_mul, localEval_ofReal, localEval_ofReal,
    localEval_zeta]
  simp only [map_intCast]
  rw [a.quotientAddress.ratio_mul_signedLeftRoot, sub_self]

/-- Ideal-membership form of the oriented-carrier address. -/
theorem cyclotomicDegreeSixCarrier_mem_evalKernel
    (a : CyclotomicLinearPrimeAddress p q) :
    p.signedDepth.cyclotomicDegreeSixCarrier ∈ a.evalKernel :=
  a.eval_cyclotomicDegreeSixCarrier_zero

/-- The inverse-root conjugate linear carrier is excluded from the selected
orientation. -/
theorem eval_cyclotomicDegreeSixCarrierConj_ne_zero
    (a : CyclotomicLinearPrimeAddress p q) :
    a.eval p.signedDepth.cyclotomicDegreeSixCarrierConj ≠ 0 := by
  have h :=
    p.degreeSixLocalRatioProvider
      |>.localEval_conjugateLinearCarrier_ne_zero
        a.quotientAddress
  change
    (SevenCyclotomicDegreeSixInt.localEval a.quotientAddress)
        p.signedDepth.cyclotomicDegreeSixCarrierConj ≠ 0
  rw [← provider_conjugateLinearCarrier_eq (p := p)]
  exact h

/-- Kernel-exclusion form of the conjugate-orientation theorem. -/
theorem cyclotomicDegreeSixCarrierConj_not_mem_evalKernel
    (a : CyclotomicLinearPrimeAddress p q) :
    p.signedDepth.cyclotomicDegreeSixCarrierConj ∉ a.evalKernel :=
  a.eval_cyclotomicDegreeSixCarrierConj_ne_zero

/-- The oriented degree-six evaluation is surjective because the embedded
integer constants already cover `ZMod q`. -/
theorem eval_surjective
    (a : CyclotomicLinearPrimeAddress p q) :
    Function.Surjective a.eval := by
  letI : Fact (Nat.Prime q) := ⟨a.quotientAddress.prime⟩
  intro z
  refine
    ⟨SevenCyclotomicDegreeSixInt.ofReal
        (z.val : SevenRealCubicInt), ?_⟩
  rw [eval, localEval_ofReal]
  simpa only [map_natCast] using ZMod.natCast_zmod_val z

/-- The explicit degree-six kernel is maximal and therefore prime. -/
theorem evalKernel_isMaximal
    (a : CyclotomicLinearPrimeAddress p q) :
    a.evalKernel.IsMaximal := by
  letI : Fact (Nat.Prime q) := ⟨a.quotientAddress.prime⟩
  exact RingHom.ker_isMaximal_of_surjective
    a.eval a.eval_surjective

/-- Contracting the oriented degree-six prime to the real cubic suborder
recovers exactly the existing `beta`-evaluation kernel. -/
theorem evalKernel_comap_ofReal
    (a : CyclotomicLinearPrimeAddress p q) :
    Ideal.comap SevenCyclotomicDegreeSixInt.ofReal a.evalKernel =
      RingHom.ker a.quotientAddress.evalAlphaRoot := by
  ext x
  change
    a.eval (SevenCyclotomicDegreeSixInt.ofReal x) = 0 ↔
      a.quotientAddress.evalAlphaRoot x = 0
  rw [eval, localEval_ofReal]

/-- The contraction of the oriented linear prime to the integers is the
rational prime ideal `(q)`. -/
theorem evalKernel_comap_intCast
    (a : CyclotomicLinearPrimeAddress p q) :
    Ideal.comap
        (Int.castRingHom SevenCyclotomicDegreeSixInt.Ring)
        a.evalKernel =
      Ideal.span ({(q : ℤ)} : Set ℤ) := by
  ext z
  rw [Ideal.mem_comap, Ideal.mem_span_singleton]
  change
    a.eval
        (SevenCyclotomicDegreeSixInt.ofReal
          (z : SevenRealCubicInt)) = 0 ↔
      (q : ℤ) ∣ z
  rw [eval, localEval_ofReal, map_intCast,
    ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- The oriented degree-six residue prime has residue degree one: the
quotient contains exactly `q` elements. -/
theorem evalKernel_cardQuot
    (a : CyclotomicLinearPrimeAddress p q) :
    Submodule.cardQuot a.evalKernel = q := by
  letI : Fact (Nat.Prime q) := ⟨a.quotientAddress.prime⟩
  rw [Submodule.cardQuot_apply]
  calc
    Nat.card
        (SevenCyclotomicDegreeSixInt.Ring ⧸ a.evalKernel) =
        Nat.card (ZMod q) :=
      Nat.card_congr
        (RingHom.quotientKerEquivOfSurjective
          a.eval_surjective).toEquiv
    _ = q := Nat.card_zmod q

/-- Complete local linear-prime packet: maximality, real/integer
contractions, residue degree one, and separation of the two conjugate
linear factors are all retained together. -/
theorem linearPrimeAddress_packet
    (a : CyclotomicLinearPrimeAddress p q) :
    a.evalKernel.IsMaximal ∧
      Ideal.comap SevenCyclotomicDegreeSixInt.ofReal a.evalKernel =
        RingHom.ker a.quotientAddress.evalAlphaRoot ∧
      Ideal.comap
          (Int.castRingHom SevenCyclotomicDegreeSixInt.Ring)
          a.evalKernel =
        Ideal.span ({(q : ℤ)} : Set ℤ) ∧
      Submodule.cardQuot a.evalKernel = q ∧
      p.signedDepth.cyclotomicDegreeSixCarrier ∈ a.evalKernel ∧
      p.signedDepth.cyclotomicDegreeSixCarrierConj ∉
        a.evalKernel :=
  ⟨a.evalKernel_isMaximal,
    a.evalKernel_comap_ofReal,
    a.evalKernel_comap_intCast,
    a.evalKernel_cardQuot,
    a.cyclotomicDegreeSixCarrier_mem_evalKernel,
    a.cyclotomicDegreeSixCarrierConj_not_mem_evalKernel⟩

end CyclotomicLinearPrimeAddress

end RamifiedSignedRootRoutingPacket


end

end DkMath.FLT.Seven
