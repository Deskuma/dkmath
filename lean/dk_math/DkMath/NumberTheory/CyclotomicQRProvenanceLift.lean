/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.CyclotomicQRTraceOneBridge
import DkMath.NumberTheory.TraceOneQuadraticField
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Ideal.Maps
import DkMath.Lib.NumberTheory.ConjugatePrimeIdealOwnership

#print "file: DkMath.NumberTheory.CyclotomicQRProvenanceLift"

/-! The retained Gauss difference identifies the QR element, rather than only
its scalar norm. The chosen primitive root fixes the sign of the embedding. -/
namespace DkMath.NumberTheory.CyclotomicQRProvenanceLift

open DkMath.NumberTheory.CyclotomicQRTraceOneBridge
open DkMath.NumberTheory.CyclotomicQRGaussNormalization
open DkMath.NumberTheory.CyclotomicQRGaloisAction
open DkMath.NumberTheory.PrimeQuadraticDiscriminant
open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.NumberTheory.TraceOneQuadraticField

noncomputable section
variable {L : Type*} [Field L] [Algebra ℚ L]
variable {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ L]
local instance : CharZero L := Algebra.charZero_of_charZero ℚ L

variable {ζ : L} {hζ : IsPrimitiveRoot ζ p}

/-- The Gauss choice fixes which root of the TraceOne relation is used. -/
def gaussTau (ζ : L) (hζ : IsPrimitiveRoot ζ p) : L :=
  (1 + quadraticGauss ζ hζ) / 2

theorem gaussTau_relation (hp2 : p ≠ 2) :
    gaussTau ζ hζ * gaussTau ζ hζ =
      algebraMap ℚ L (signedPrimeParameter p : ℚ) + gaussTau ζ hζ := by
  have hg := quadraticGauss_sq hp2 ζ hζ
  have hd := congrArg (algebraMap ℤ L)
    (discr_signedPrimeParameter (Fact.out : p.Prime) hp2)
  simp only [discr, map_add, map_mul, map_one, map_ofNat] at hd
  simp only [gaussTau]
  simp only [map_intCast, eq_intCast] at hd hg ⊢
  linear_combination (norm := ring_nf) hg / 4 - hd / 4

/-- An algebra embedding with the chosen Gauss sign. -/
def gaussEmbedding (hp2 : p ≠ 2) :
    TraceOneRat (signedPrimeParameter p) →ₐ[ℚ] L :=
  QuadraticAlgebra.lift ⟨gaussTau ζ hζ, by
    simpa [Algebra.smul_def] using gaussTau_relation (ζ := ζ) (hζ := hζ) hp2⟩

theorem gaussEmbedding_apply (hp2 : p ≠ 2)
    (w : TraceOneRat (signedPrimeParameter p)) :
    gaussEmbedding (ζ := ζ) (hζ := hζ) hp2 w =
      algebraMap ℚ L w.re + algebraMap ℚ L w.im * gaussTau ζ hζ := by
  simp [gaussEmbedding, QuadraticAlgebra.lift, Algebra.smul_def]

theorem gaussEmbedding_injective (hp2 : p ≠ 2) :
    Function.Injective (gaussEmbedding (ζ := ζ) (hζ := hζ) hp2) := by
  let : Field (TraceOneRat (signedPrimeParameter p)) :=
    traceOneRatField (Fact.out : p.Prime) hp2
  exact (gaussEmbedding (ζ := ζ) (hζ := hζ) hp2).injective

/-- The explicit embedded quadratic subfield; its source is the existing
rational TraceOne field, not a carrier reconstructed from a norm. -/
def gaussSubfield (hp2 : p ≠ 2) : IntermediateField ℚ L := by
  let : Field (TraceOneRat (signedPrimeParameter p)) :=
    traceOneRatField (Fact.out : p.Prime) hp2
  exact (gaussEmbedding (ζ := ζ) (hζ := hζ) hp2).fieldRange

/-- Use the inherited intermediate-field algebra for this named image. -/
instance (priority := 2000) gaussSubfieldAlgebra (hp2 : p ≠ 2) : Algebra ℚ (gaussSubfield (ζ := ζ) (hζ := hζ) hp2) :=
  (gaussSubfield (ζ := ζ) (hζ := hζ) hp2).algebra'

set_option backward.isDefEq.respectTransparency false in
/-- The quadratic companion is algebra-isomorphic to its explicit field image. -/
def gaussSubfieldEquiv (hp2 : p ≠ 2) :
    TraceOneRat (signedPrimeParameter p) ≃ₐ[ℚ]
      gaussSubfield (ζ := ζ) (hζ := hζ) hp2 := by
  let : Field (TraceOneRat (signedPrimeParameter p)) :=
    traceOneRatField (Fact.out : p.Prime) hp2
  exact (gaussEmbedding (ζ := ζ) (hζ := hζ) hp2).equivFieldRange

set_option backward.isDefEq.respectTransparency false in
theorem gaussSubfield_finrank (hp2 : p ≠ 2) :
    Module.finrank ℚ (gaussSubfield (ζ := ζ) (hζ := hζ) hp2) = 2 := by
  rw [← (gaussSubfieldEquiv (ζ := ζ) (hζ := hζ) hp2).toLinearEquiv.finrank_eq]
  exact QuadraticAlgebra.finrank_eq_two (signedPrimeParameter p : ℚ) 1

/-- The existing integral coordinates enter the cyclotomic field through a ring map. -/
def integralEmbedding (hp2 : p ≠ 2) : TraceOneInt (signedPrimeParameter p) →+* L :=
  (gaussEmbedding (ζ := ζ) (hζ := hζ) hp2).toRingHom.comp
    (traceOneRatHom (signedPrimeParameter p))

theorem integralEmbedding_apply (hp2 : p ≠ 2)
    (w : TraceOneInt (signedPrimeParameter p)) :
    integralEmbedding (ζ := ζ) (hζ := hζ) hp2 w =
      (w.fst : L) + (w.snd : L) * gaussTau ζ hζ := by
  simp [integralEmbedding, gaussEmbedding_apply]

omit [Algebra ℚ L] [Fact p.Prime] [IsCyclotomicExtension {p} ℚ L] in
private theorem eval_int_cast (f : MvPolynomial (Fin 2) ℤ) (z y : ℤ) :
    MvPolynomial.eval₂ (algebraMap ℤ L) ![(z : L), (y : L)] f =
      (MvPolynomial.eval ![z, y] f : L) := by
  symm
  have hv : (algebraMap ℤ L) ∘ ![z, y] = ![(z : L), (y : L)] := by
    funext i
    fin_cases i <;> simp
  have h := MvPolynomial.eval₂_comp (algebraMap ℤ L) ![z, y] f
  rw [hv] at h
  simpa only [eq_intCast] using h

/-- The packet's half relation and signed Gauss difference identify the QR product. -/
theorem coord_image_eq_qr (hp2 : p ≠ 2)
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ) (z y : ℤ) :
    integralEmbedding (ζ := ζ) (hζ := hζ) hp2 (P.coord z y) =
      MvPolynomial.eval ![(z : L), (y : L)] (qrFactorPoly (p := p) ζ) := by
  have hr := congrArg (MvPolynomial.eval ![(z : L), (y : L)]) P.map_RZ
  have hd := congrArg (MvPolynomial.eval ![(z : L), (y : L)]) P.gauss_difference
  have hh := congrArg (fun f => algebraMap ℤ L (MvPolynomial.eval ![z, y] f))
    P.half_relation
  simp only [MvPolynomial.eval_map, Rpoly, Dpoly, map_add, map_sub,
    map_mul, MvPolynomial.eval_C] at hr hd
  simp at hh
  rw [eval_int_cast] at hr hd
  rw [integralEmbedding_apply]
  simp only [PrimeTraceOneCoordinatePacket.coord, gaussTau]
  linear_combination (norm := ring_nf) (hr - hh + hd) / 2

/-- Conjugation swaps the two products, with no omitted sign or unit. -/
theorem conj_coord_image_eq_qnr (hp2 : p ≠ 2)
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ) (z y : ℤ) :
    integralEmbedding (ζ := ζ) (hζ := hζ) hp2 (conj (P.coord z y)) =
      MvPolynomial.eval ![(z : L), (y : L)] (qnrFactorPoly (p := p) ζ) := by
  have hr := congrArg (MvPolynomial.eval ![(z : L), (y : L)]) P.map_RZ
  have hd := congrArg (MvPolynomial.eval ![(z : L), (y : L)]) P.gauss_difference
  have hh := congrArg (fun f => algebraMap ℤ L (MvPolynomial.eval ![z, y] f))
    P.half_relation
  simp only [MvPolynomial.eval_map, Rpoly, Dpoly, map_add, map_sub,
    map_mul, MvPolynomial.eval_C] at hr hd
  simp at hh
  rw [eval_int_cast] at hr hd
  rw [integralEmbedding_apply]
  simp only [PrimeTraceOneCoordinatePacket.coord, conj, gaussTau, Int.cast_add, Int.cast_neg]
  linear_combination (norm := ring_nf) (hr - hh - hd) / 2

/-- The relative norm of the quadratic element is an actual determinant norm. -/
theorem coord_relative_norm (P : PrimeTraceOneCoordinatePacket L p ζ hζ) (z y : ℤ) :
    Algebra.norm ℚ (traceOneRatHom (signedPrimeParameter p) (P.coord z y)) =
      ((DkMath.CosmicFormula.GTailCyclotomicShell p (z - y) y : ℤ) : ℚ) := by
  rw [Algebra.norm_apply]
  change (DistribSMul.toLinearMap ℚ (TraceOneRat (signedPrimeParameter p))
    (traceOneRatHom (signedPrimeParameter p) (P.coord z y))).det = _
  rw [QuadraticAlgebra.det_toLinearMap_eq_norm, traceOneRatHom_norm, P.coord_norm_eq]

set_option backward.isDefEq.respectTransparency false in
/-- The relative norm is preserved when the element is placed in the explicit subfield. -/
theorem subfield_coord_relative_norm (hp2 : p ≠ 2)
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ) (z y : ℤ) :
    Algebra.norm ℚ (gaussSubfieldEquiv (ζ := ζ) (hζ := hζ) hp2
      (traceOneRatHom (signedPrimeParameter p) (P.coord z y))) =
      ((DkMath.CosmicFormula.GTailCyclotomicShell p (z - y) y : ℤ) : ℚ) := by
  rw [Algebra.norm_eq_of_algEquiv, coord_relative_norm]

/-- The embedded coordinate really lies in the explicit quadratic subfield. -/
theorem qr_mem_gaussSubfield (hp2 : p ≠ 2)
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ) (z y : ℤ) :
    MvPolynomial.eval ![(z : L), (y : L)] (qrFactorPoly (p := p) ζ) ∈
      gaussSubfield (ζ := ζ) (hζ := hζ) hp2 := by
  change ∃ w, gaussEmbedding (ζ := ζ) (hζ := hζ) hp2 w = _
  exact ⟨traceOneRatHom (signedPrimeParameter p) (P.coord z y),
    coord_image_eq_qr hp2 P z y⟩

/-- The discriminant axis maps to the chosen Gauss element, fixing its sign. -/
theorem integralEmbedding_discrAxis (hp2 : p ≠ 2) :
    integralEmbedding (ζ := ζ) (hζ := hζ) hp2
      (discrAxis (signedPrimeParameter p)) = quadraticGauss ζ hζ := by
  rw [integralEmbedding_apply, discrAxis_eq]
  simp only [gaussTau, Int.cast_neg, Int.cast_one, Int.cast_ofNat]
  ring_nf

/-- Reversing the axis reverses the Gauss sign. -/
theorem integralEmbedding_conj_discrAxis (hp2 : p ≠ 2) :
    integralEmbedding (ζ := ζ) (hζ := hζ) hp2
      (conj (discrAxis (signedPrimeParameter p))) = -quadraticGauss ζ hζ := by
  rw [conj_discrAxis, map_neg, integralEmbedding_discrAxis]

/-- The Gauss generator belongs to the named quadratic field image. -/
theorem gauss_mem_gaussSubfield (hp2 : p ≠ 2) : quadraticGauss ζ hζ ∈
    gaussSubfield (ζ := ζ) (hζ := hζ) hp2 := by
  change ∃ w, gaussEmbedding (ζ := ζ) (hζ := hζ) hp2 w = _
  exact ⟨traceOneRatHom (signedPrimeParameter p) (discrAxis (signedPrimeParameter p)),
    integralEmbedding_discrAxis hp2⟩

/-- Equal axis norms do not identify the two signed element images. -/
theorem axis_images_distinct (hp2 : p ≠ 2) :
    integralEmbedding (ζ := ζ) (hζ := hζ) hp2 (discrAxis (signedPrimeParameter p)) ≠
      integralEmbedding (ζ := ζ) (hζ := hζ) hp2 (conj (discrAxis (signedPrimeParameter p))) := by
  rw [integralEmbedding_discrAxis, integralEmbedding_conj_discrAxis]
  intro h
  apply quadraticGauss_ne_zero hp2 ζ hζ
  linear_combination (norm := ring_nf) h / 2

/-- Coordinate witnesses with the same QR provenance agree as elements. -/
theorem coordinate_packet_unique (hp2 : p ≠ 2)
    (P Q : PrimeTraceOneCoordinatePacket L p ζ hζ) (z y : ℤ) :
    P.coord z y = Q.coord z y := by
  apply traceOneRatHom_injective (signedPrimeParameter p)
  apply gaussEmbedding_injective (ζ := ζ) (hζ := hζ) hp2
  exact (coord_image_eq_qr hp2 P z y).trans (coord_image_eq_qr hp2 Q z y).symm

/-- The integral image lies in the actual integer ring of the ambient field. -/
def integerEmbedding (hp2 : p ≠ 2) :
    TraceOneInt (signedPrimeParameter p) →+* NumberField.RingOfIntegers L where
  toFun w := ⟨integralEmbedding (ζ := ζ) (hζ := hζ) hp2 w,
    map_isIntegral_int (integralEmbedding (ζ := ζ) (hζ := hζ) hp2)
      (IsIntegral.of_finite ℤ w)⟩
  map_one' := by
    ext
    change integralEmbedding (ζ := ζ) (hζ := hζ) hp2 1 = 1
    exact map_one _
  map_zero' := by
    ext
    change integralEmbedding (ζ := ζ) (hζ := hζ) hp2 0 = 0
    exact map_zero _
  map_add' x y := by
    ext
    change integralEmbedding (ζ := ζ) (hζ := hζ) hp2 (x + y) = _
    exact map_add (integralEmbedding (ζ := ζ) (hζ := hζ) hp2) x y
  map_mul' x y := by
    ext
    change integralEmbedding (ζ := ζ) (hζ := hζ) hp2 (x * y) = _
    exact map_mul (integralEmbedding (ζ := ζ) (hζ := hζ) hp2) x y

/-- Integral QR element, with its packet and root choice retained. -/
def qrInteger (hp2 : p ≠ 2) (P : PrimeTraceOneCoordinatePacket L p ζ hζ) (z y : ℤ) :
    NumberField.RingOfIntegers L := integerEmbedding (ζ := ζ) (hζ := hζ) hp2 (P.coord z y)

/-- Integral QNR element obtained using precisely the conjugate coordinates. -/
def qnrInteger (hp2 : p ≠ 2) (P : PrimeTraceOneCoordinatePacket L p ζ hζ) (z y : ℤ) :
    NumberField.RingOfIntegers L := integerEmbedding (ζ := ζ) (hζ := hζ) hp2 (conj (P.coord z y))

theorem qrInteger_coe (hp2 : p ≠ 2)
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ) (z y : ℤ) :
    (qrInteger hp2 P z y : L) =
      MvPolynomial.eval ![(z : L), (y : L)] (qrFactorPoly (p := p) ζ) :=
  coord_image_eq_qr hp2 P z y

theorem qnrInteger_coe (hp2 : p ≠ 2)
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ) (z y : ℤ) :
    (qnrInteger hp2 P z y : L) =
      MvPolynomial.eval ![(z : L), (y : L)] (qnrFactorPoly (p := p) ζ) :=
  conj_coord_image_eq_qnr hp2 P z y

/-- The norm pair identity follows by applying the ring map to the element identity. -/
theorem qrInteger_mul_qnrInteger (hp2 : p ≠ 2)
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ) (z y : ℤ) :
    qrInteger hp2 P z y * qnrInteger hp2 P z y =
      (norm (P.coord z y) : NumberField.RingOfIntegers L) := by
  rw [qrInteger, qnrInteger, ← map_mul, traceOne_mul_conj]
  change integerEmbedding (ζ := ζ) (hζ := hζ) hp2 (norm (P.coord z y) : TraceOneInt _) = _
  exact map_intCast _ _

/-- Extension of the principal coordinate ideal is the integral QR ideal. -/
theorem map_coordinate_ideal (hp2 : p ≠ 2)
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ) (z y : ℤ) :
    Ideal.map (integerEmbedding (ζ := ζ) (hζ := hζ) hp2)
      (Ideal.span {P.coord z y}) = Ideal.span {qrInteger hp2 P z y} := by
  rw [Ideal.map_span, Set.image_singleton]
  rfl

/-- Exact ideal product; this does not principalize an arbitrary ideal. -/
theorem qr_qnr_ideal_product (hp2 : p ≠ 2)
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ) (z y : ℤ) :
    Ideal.span {qrInteger hp2 P z y} * Ideal.span {qnrInteger hp2 P z y} =
      Ideal.span {(norm (P.coord z y) : NumberField.RingOfIntegers L)} := by
  rw [Ideal.span_singleton_mul_span_singleton, qrInteger_mul_qnrInteger]

/-- Ownership is transported by contraction along the explicit integral map. -/
theorem qrInteger_mem_iff (hp2 : p ≠ 2)
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ) (z y : ℤ)
    (J : Ideal (NumberField.RingOfIntegers L)) :
    qrInteger hp2 P z y ∈ J ↔ P.coord z y ∈
      Ideal.comap (integerEmbedding (ζ := ζ) (hζ := hζ) hp2) J := Iff.rfl

/-- The existing ownership cutoff applies with the proven QR/QNR norm pair.
The conjugate ownership, ideal extension and contraction hypotheses remain explicit. -/
theorem qrInteger_not_mem_power (hp2 : p ≠ 2)
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ) (z y : ℤ)
    (Q : Ideal ℤ) (J Jbar : Ideal (NumberField.RingOfIntegers L)) (m : ℕ)
    (hconj : qrInteger hp2 P z y ∈ J ^ (m + 1) →
      qnrInteger hp2 P z y ∈ Jbar ^ (m + 1))
    (hmap : Ideal.map (Int.castRingHom (NumberField.RingOfIntegers L)) (Q ^ (m + 1)) =
      J ^ (m + 1) * Jbar ^ (m + 1))
    (hcontract : Ideal.comap (Int.castRingHom (NumberField.RingOfIntegers L))
      (Ideal.map (Int.castRingHom (NumberField.RingOfIntegers L)) (Q ^ (m + 1))) =
        Q ^ (m + 1))
    (hcutoff : norm (P.coord z y) ∉ Q ^ (m + 1)) :
    qrInteger hp2 P z y ∉ J ^ (m + 1) := by
  exact DkMath.Lib.NumberTheory.not_mem_primePower_succ_of_conjugate_norm_cutoff
    (Int.castRingHom (NumberField.RingOfIntegers L)) Q J Jbar
    (qrInteger hp2 P z y) (qnrInteger hp2 P z y) (norm (P.coord z y)) m
    hconj (qrInteger_mul_qnrInteger hp2 P z y) hmap hcontract hcutoff

end
end DkMath.NumberTheory.CyclotomicQRProvenanceLift
