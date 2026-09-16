/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.CyclotomicQRGaloisAction
import DkMathTest.FLT.Prime.CyclotomicQRProductProbe

#print "file: DkMathTest.FLT.Prime.CyclotomicQRGaloisActionProbe"

namespace DkMathTest.FLT.Prime

open scoped BigOperators

open DkMath.NumberTheory.CyclotomicQRProduct
open DkMath.NumberTheory.CyclotomicQRGaloisAction

noncomputable section

/-! The polynomial evaluator agrees with the typed QR/QNR factors. -/

example (X Y : ℂ) :
    MvPolynomial.eval ![X, Y]
        (qrFactorPoly (p := 3) (complexZeta 3)) =
      (qrFinset 3).prod
        (fun a => rootFactor (complexZeta 3) a X Y) := by
  exact eval_qrFactorPoly (complexZeta 3) X Y

example (X Y : ℂ) :
    MvPolynomial.eval ![X, Y]
        (qnrFactorPoly (p := 5) (complexZeta 5)) =
      (qnrFinset 5).prod
        (fun a => rootFactor (complexZeta 5) a X Y) := by
  exact eval_qnrFactorPoly (complexZeta 5) X Y

example (X Y : ℂ) :
    MvPolynomial.eval ![X, Y]
        (qrFactorPoly (p := 7) (complexZeta 7)) =
      (qrFinset 7).prod
        (fun a => rootFactor (complexZeta 7) a X Y) := by
  exact eval_qrFactorPoly (complexZeta 7) X Y

example (X Y : ℂ) :
    MvPolynomial.eval ![X, Y]
        (qnrFactorPoly (p := 11) (complexZeta 11)) =
      (qnrFinset 11).prod
        (fun a => rootFactor (complexZeta 11) a X Y) := by
  exact eval_qnrFactorPoly (complexZeta 11) X Y

example (X Y : ℂ) :
    MvPolynomial.eval ![X, Y]
        (qrFactorPoly (p := 13) (complexZeta 13)) =
      (qrFinset 13).prod
        (fun a => rootFactor (complexZeta 13) a X Y) := by
  exact eval_qrFactorPoly (complexZeta 13) X Y

/-! The abstract action API specializes to the identity square action. -/

example {p : ℕ} [Fact p.Prime]
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ p) :
    MvPolynomial.map (RingEquiv.refl ℂ).toRingHom
        (Rpoly (p := p) ζ) = Rpoly (p := p) ζ := by
  exact map_Rpoly_of_square ζ hζ (1 : ZMod p) (RingEquiv.refl ℂ)
    (by simp) ⟨1, by simp⟩ (by
      have hp : Nat.Prime p := Fact.out
      rw [ZMod.val_one'' hp.ne_one]
      simp)

example {p : ℕ} [Fact p.Prime]
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ p)
    (t : ZMod p) (σ : ℂ ≃+* ℂ)
    (ht : t ≠ 0) (htnsq : ¬IsSquare t)
    (hσζ : σ ζ = ζ ^ t.val) :
    MvPolynomial.map σ.toRingHom (Dpoly (p := p) ζ) =
      -(Dpoly (p := p) ζ) := by
  exact map_Dpoly_of_nonsquare ζ hζ t σ ht htnsq hσζ

#print axioms eval_rootFactorPoly
#print axioms eval_qrFactorPoly
#print axioms eval_qnrFactorPoly
#print axioms mulBy_t_nonzero_bijective
#print axioms mulBy_t_permutes_nonzeroResidues
#print axioms isSquare_mul_iff
#print axioms mulBy_t_maps_qr_of_square
#print axioms mulBy_t_maps_qnr_of_square
#print axioms mulBy_t_maps_qr_to_qnr_of_nonsquare
#print axioms mulBy_t_maps_qnr_to_qr_of_nonsquare
#print axioms map_rootFactorPoly
#print axioms map_qrFactorPoly_of_square
#print axioms map_qnrFactorPoly_of_square
#print axioms map_qrFactorPoly_to_qnr_of_nonsquare
#print axioms map_qnrFactorPoly_to_qr_of_nonsquare
#print axioms map_Rpoly_of_square
#print axioms map_Dpoly_of_square
#print axioms map_Rpoly_of_nonsquare
#print axioms map_Dpoly_of_nonsquare
#print axioms map_Dpoly_sq_of_square
#print axioms map_Dpoly_sq_of_nonsquare

end

end DkMathTest.FLT.Prime
