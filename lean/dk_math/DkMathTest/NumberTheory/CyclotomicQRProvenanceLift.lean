import DkMath.NumberTheory.CyclotomicQRProvenanceLift
import DkMath.FLT.Prime.PrimeCyclotomicTraceOne

open DkMath.NumberTheory.CyclotomicQRProvenanceLift
open DkMath.NumberTheory.CyclotomicQRTraceOneBridge
open DkMath.NumberTheory.CyclotomicQRGaloisAction
open DkMath.NumberTheory.CyclotomicQRGaussNormalization
open DkMath.NumberTheory.PrimeQuadraticDiscriminant
open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.NumberTheory.TraceOneQuadraticField

noncomputable section
variable {L : Type*} [Field L] [Algebra ℚ L]
variable {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ L]
variable {ζ : L} {hζ : IsPrimitiveRoot ζ p}

-- Check that retained provenance selects QR and that conjugation selects QNR.
example (hp2 : p ≠ 2) (P : PrimeTraceOneCoordinatePacket L p ζ hζ) (z y : ℤ) :
    (qrInteger hp2 P z y : L) = MvPolynomial.eval ![(z : L), (y : L)] (qrFactorPoly (p := p) ζ) ∧
    (qnrInteger hp2 P z y : L) = MvPolynomial.eval ![(z : L), (y : L)] (qnrFactorPoly (p := p) ζ) :=
  ⟨qrInteger_coe hp2 P z y, qnrInteger_coe hp2 P z y⟩

-- Equal norm with opposite Gauss signs is a real element-level distinction.
example (hp2 : p ≠ 2) :
    norm (discrAxis (signedPrimeParameter p)) =
      norm (conj (discrAxis (signedPrimeParameter p))) ∧
    integralEmbedding (ζ := ζ) (hζ := hζ) hp2 (discrAxis (signedPrimeParameter p)) ≠
      integralEmbedding (ζ := ζ) (hζ := hζ) hp2 (conj (discrAxis (signedPrimeParameter p))) := by
  constructor
  · rw [conj_discrAxis, discrAxis_eq]
    simp [DkMath.NumberTheory.TraceOneQuadratic.norm]
  · exact axis_images_distinct hp2

example (hp2 : p ≠ 2) (P Q : PrimeTraceOneCoordinatePacket L p ζ hζ) (z y : ℤ) :
    P.coord z y = Q.coord z y := coordinate_packet_unique hp2 P Q z y

example (hp2 : p ≠ 2) : Module.finrank ℚ (gaussSubfield (ζ := ζ) (hζ := hζ) hp2) = 2 :=
  gaussSubfield_finrank hp2

example (hp2 : p ≠ 2) (P : PrimeTraceOneCoordinatePacket L p ζ hζ) (z y : ℤ) :
    Algebra.norm ℚ (gaussSubfieldEquiv (ζ := ζ) (hζ := hζ) hp2
      (traceOneRatHom (signedPrimeParameter p) (P.coord z y))) =
      ((DkMath.CosmicFormula.GTailCyclotomicShell p (z - y) y : ℤ) : ℚ) :=
  subfield_coord_relative_norm hp2 P z y

end

noncomputable section
variable {L : Type*} [Field L] [NumberField L] [CharZero L]
variable {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ L]
variable {ζ : L} {hζ : IsPrimitiveRoot ζ p}

-- Compatibility with the existing ideal scalar endpoint does not identify
-- the QR half-product ideal with the ideal of a single cyclotomic linear factor.
example
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ) (g u : ℕ) :
    Algebra.norm ℚ (traceOneRatHom (signedPrimeParameter p)
      (P.coord ((g + u : ℕ) : ℤ) (u : ℤ))) =
    (Ideal.absNorm (DkMath.CFBRC.cyclotomicLinearFactorIdeal (K := L) hζ g u) : ℚ) := by
  have h := DkMath.FLT.Prime.TraceOneScalar.coord_norm_eq_cyclotomicIdeal_absNorm P g u
  rw [P.coord_norm_eq] at h
  rw [coord_relative_norm]
  exact_mod_cast h

end

example : signedPrimeParameter 3 = -1 := by decide
example : signedPrimeParameter 5 = 1 := by decide
example : signedPrimeParameter 7 = -2 := by decide

#print axioms gaussEmbedding_injective
#print axioms gaussSubfieldEquiv
#print axioms gaussSubfield_finrank
#print axioms coord_image_eq_qr
#print axioms conj_coord_image_eq_qnr
#print axioms subfield_coord_relative_norm
#print axioms integerEmbedding
#print axioms qrInteger_mul_qnrInteger
#print axioms map_coordinate_ideal
#print axioms qr_qnr_ideal_product
#print axioms qrInteger_mem_iff
#print axioms qrInteger_not_mem_power
#print axioms axis_images_distinct
#print axioms coordinate_packet_unique

#print axioms DkMath.FLT.Prime.TraceOneScalar.coord_norm_eq_cyclotomicIdeal_absNorm
