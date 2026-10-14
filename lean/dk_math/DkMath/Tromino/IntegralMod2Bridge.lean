/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.LocalFrameEquiv
import DkMath.Tromino.PortV4Chains
import DkMath.Lib.NumberTheory.EisensteinCoordinates
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

#print "file: DkMath.Tromino.IntegralMod2Bridge"

namespace DkMath.Tromino

open DkMath.Lib.NumberTheory
open DkMath.NumberTheory.TraceOneQuadratic
open scoped BigOperators

/-!
# Integral coordinate parity

This module reduces Gaussian and trace-one Eisenstein coordinates modulo `2`
to the same four-element additive carrier used by the Tromino state layer.
The reduction preserves addition and is surjective. It also transports the
two ambient multiplications to two different finite multiplication laws;
the final obstruction shows that these multiplicative structures need not be
identified merely because their additive parity data agree.
-/

/-- Gaussian integer coordinates reduced to the additive four-state carrier. -/
def gaussianParity : GaussianInt →+ TrominoState where
  toFun z := ((z.re : ZMod 2), (z.im : ZMod 2))
  map_zero' := by
    apply Prod.ext <;> simp
  map_add' x y := by
    apply Prod.ext <;> simp

/-- Gaussian parity is given by the two coordinate residues modulo `2`. -/
@[simp] theorem gaussianParity_apply (z : GaussianInt) :
    gaussianParity z = ((z.re : ZMod 2), (z.im : ZMod 2)) := rfl

/-- The zero Gaussian integer has zero parity. -/
@[simp] theorem gaussianParity_zero : gaussianParity 0 = 0 := by
  ext <;> simp

/-- The Gaussian unit `1` represents the first nonzero state. -/
@[simp] theorem gaussianParity_one : gaussianParity 1 = deltaA := by
  decide

/-- The Gaussian coordinate corresponding to the imaginary unit. -/
def gaussianI : GaussianInt := ⟨0, 1⟩

/-- The imaginary unit represents the second nonzero state. -/
@[simp] theorem gaussianParity_i : gaussianParity gaussianI = deltaB := by
  decide

/-- The Gaussian coordinate `1 + i` represents the third nonzero state. -/
@[simp] theorem gaussianParity_one_add_i :
    gaussianParity (⟨1, 1⟩ : GaussianInt) = deltaC := by
  decide

/-- Every Tromino state has a Gaussian integer representative modulo `2`. -/
theorem gaussianParity_surjective : Function.Surjective gaussianParity := by
  intro s
  fin_cases s
  · exact ⟨(⟨0, 0⟩ : GaussianInt), by decide⟩
  · exact ⟨(⟨0, 1⟩ : GaussianInt), by decide⟩
  · exact ⟨(⟨1, 0⟩ : GaussianInt), by decide⟩
  · exact ⟨(⟨1, 1⟩ : GaussianInt), by decide⟩

/-- Trace-one Eisenstein coordinates reduced to the same additive carrier. -/
def eisensteinParity : TraceOneInt (-1) →+ TrominoState where
  toFun z := ((z.fst : ZMod 2), (z.snd : ZMod 2))
  map_zero' := by
    apply Prod.ext <;> simp
  map_add' x y := by
    apply Prod.ext <;> simp

/-- Eisenstein parity is given by the two trace-one coordinate residues. -/
@[simp] theorem eisensteinParity_apply (z : TraceOneInt (-1)) :
    eisensteinParity z = ((z.fst : ZMod 2), (z.snd : ZMod 2)) := rfl

/-- The zero trace-one coordinate has zero parity. -/
@[simp] theorem eisensteinParity_zero : eisensteinParity 0 = 0 := by
  ext <;> simp

/-- Coordinate construction commutes with reduction modulo `2`. -/
@[simp] theorem eisensteinParity_eisensteinCoord (m n : ℤ) :
    eisensteinParity (eisensteinCoord m n) =
      ((m : ZMod 2), (n : ZMod 2)) := by
  apply Prod.ext
  · rfl
  · simp [eisensteinCoord]

/-- The coordinate `(0, 0)` represents the zero state. -/
@[simp] theorem eisensteinParity_coord_00 :
    eisensteinParity (eisensteinCoord 0 0) = 0 := by
  decide

/-- The coordinate `(1, 0)` represents the first nonzero state. -/
@[simp] theorem eisensteinParity_coord_10 :
    eisensteinParity (eisensteinCoord 1 0) = deltaA := by
  decide

/-- The coordinate `(0, 1)` represents the second nonzero state. -/
@[simp] theorem eisensteinParity_coord_01 :
    eisensteinParity (eisensteinCoord 0 1) = deltaB := by
  decide

/-- The coordinate `(1, 1)` represents the third nonzero state. -/
@[simp] theorem eisensteinParity_coord_11 :
    eisensteinParity (eisensteinCoord 1 1) = deltaC := by
  decide

/-- Every Tromino state has a trace-one Eisenstein representative modulo `2`. -/
theorem eisensteinParity_surjective : Function.Surjective eisensteinParity := by
  intro s
  fin_cases s
  · exact ⟨eisensteinCoord 0 0, by decide⟩
  · exact ⟨eisensteinCoord 0 1, by decide⟩
  · exact ⟨eisensteinCoord 1 0, by decide⟩
  · exact ⟨eisensteinCoord 1 1, by decide⟩

/-- The canonical Gaussian representative of a four-state parity class. -/
def gaussianStateRep (s : TrominoState) : GaussianInt :=
  if s = 0 then ⟨0, 0⟩ else
    if s = deltaA then ⟨1, 0⟩ else
      if s = deltaB then ⟨0, 1⟩ else ⟨1, 1⟩

/-- The canonical trace-one Eisenstein representative of a four-state parity
class. -/
def eisensteinStateRep (s : TrominoState) : TraceOneInt (-1) :=
  if s = 0 then eisensteinCoord 0 0 else
    if s = deltaA then eisensteinCoord 1 0 else
      if s = deltaB then eisensteinCoord 0 1 else eisensteinCoord 1 1

/-- The Gaussian representative is a section of Gaussian parity. -/
@[simp] theorem gaussianParity_gaussianStateRep (s : TrominoState) :
    gaussianParity (gaussianStateRep s) = s := by
  fin_cases s <;> decide

/-- The Eisenstein representative is a section of Eisenstein parity. -/
@[simp] theorem eisensteinParity_eisensteinStateRep (s : TrominoState) :
    eisensteinParity (eisensteinStateRep s) = s := by
  fin_cases s <;> decide

/-!
## The Gaussian block and the frame equivalence

The Gaussian exchange frame is represented by integer coordinates. Relative
subtraction from its gap panel and reduction modulo `2` recover the frame's
finite direction labels.
-/

/-- The integer coordinate attached to a Gaussian exchange-frame panel. -/
def gaussianPanelIntegral (p : gaussianExchangeFrame.Panel) : GaussianInt :=
  ⟨p.1.1, p.1.2⟩

/-- Reduction of a panel coordinate recovers its frame color. -/
theorem gaussianPanelIntegral_parity (p : gaussianExchangeFrame.Panel) :
    gaussianParity (gaussianPanelIntegral p) = frameColor gaussianExchangeFrame p := by
  fin_cases p <;> decide

/-- Reduction of the relative panel displacement recovers the frame delta. -/
theorem gaussian_relative_parity (p : gaussianExchangeFrame.Panel) :
    gaussianParity
        (gaussianPanelIntegral gaussianExchangeFrame.gap - gaussianPanelIntegral p) =
      frameDelta gaussianExchangeFrame p := by
  fin_cases p <;> decide

/-- The frame equivalence agrees with relative Gaussian parity on each panel. -/
theorem gaussianEisensteinFrameEquiv_panelEquiv_relative_parity
    (p : gaussianExchangeFrame.Panel) :
    gaussianEisensteinFrameEquiv.panelEquiv p =
      gaussianParity
        (gaussianPanelIntegral gaussianExchangeFrame.gap - gaussianPanelIntegral p) := by
  change gaussianEisensteinPanelEquiv p = _
  rw [gaussianEisensteinPanelEquiv_apply, gaussian_relative_parity]

/-- The three nonzero relative directions occur in the expected order. -/
theorem gaussian_relative_direction_order :
    gaussianParity
          (gaussianPanelIntegral gaussianExchangeFrame.gap - gaussianPanelIntegral gaussianPanel00) =
        deltaC ∧
      gaussianParity
          (gaussianPanelIntegral gaussianExchangeFrame.gap - gaussianPanelIntegral gaussianPanel10) =
        deltaB ∧
      gaussianParity
          (gaussianPanelIntegral gaussianExchangeFrame.gap - gaussianPanelIntegral gaussianPanel01) =
        deltaA := by
  exact ⟨by decide, by decide, by decide⟩

/-- The three canonical nonzero Gaussian directions. -/
def gaussianCanonicalDirections : Finset GaussianInt :=
  {⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩}

/-- The three canonical nonzero trace-one Eisenstein directions. -/
def eisensteinCanonicalDirections : Finset (TraceOneInt (-1)) :=
  {eisensteinCoord 1 0, eisensteinCoord 0 1, eisensteinCoord 1 1}

/-- The Gaussian canonical directions after reduction modulo `2`. -/
def gaussianNonzeroDirectionParities : Finset TrominoState :=
  gaussianCanonicalDirections.image gaussianParity

/-- The Eisenstein canonical directions after reduction modulo `2`. -/
def eisensteinNonzeroDirectionParities : Finset TrominoState :=
  eisensteinCanonicalDirections.image eisensteinParity

/-- The Gaussian nonzero direction parities are exactly the three nonzero
Tromino states. -/
theorem gaussianNonzeroDirectionParities_eq :
    gaussianNonzeroDirectionParities = {deltaA, deltaB, deltaC} := by
  ext s
  simp only [gaussianNonzeroDirectionParities, gaussianCanonicalDirections, Int.reduceNeg,
    Finset.image_insert, gaussianParity_apply, Int.cast_one, Int.cast_zero, Finset.image_singleton,
    Finset.mem_insert, Finset.mem_singleton]
  fin_cases s <;> decide

/-- The Eisenstein nonzero direction parities are exactly the three nonzero
Tromino states. -/
theorem eisensteinNonzeroDirectionParities_eq :
    eisensteinNonzeroDirectionParities = {deltaA, deltaB, deltaC} := by
  ext s
  simp only [eisensteinNonzeroDirectionParities, Int.reduceNeg, eisensteinCanonicalDirections,
    Finset.image_insert, eisensteinParity_apply, eisensteinCoord_fst, Int.cast_one,
    eisensteinCoord_snd, neg_zero, Int.cast_zero, Int.cast_neg, ZMod.neg_eq_self_mod_two,
    Finset.image_singleton, Finset.mem_insert, Finset.mem_singleton]
  fin_cases s <;> decide

/-- Both integral coordinate systems produce the same finite nonzero direction
set after parity reduction. -/
theorem gaussian_eisenstein_nonzero_direction_parities_eq :
    gaussianNonzeroDirectionParities = eisensteinNonzeroDirectionParities := by
  rw [gaussianNonzeroDirectionParities_eq, eisensteinNonzeroDirectionParities_eq]

/-!
## The two induced multiplications on the common additive carrier

Gaussian multiplication and trace-one Eisenstein multiplication induce two
operations on the same additive four-state set. The formulas differ in the
second coordinate, so the resulting finite multiplicative structures must be
kept distinct even though their additive parity data agree.
-/

/-- The multiplication induced by Gaussian integer multiplication modulo `2`. -/
def gaussianMulMod2 (x y : TrominoState) : TrominoState :=
  (x.1 * y.1 + x.2 * y.2, x.1 * y.2 + x.2 * y.1)

/-- The multiplication induced by trace-one Eisenstein multiplication modulo
`2`. -/
def eisensteinMulMod2 (x y : TrominoState) : TrominoState :=
  (x.1 * y.1 + x.2 * y.2,
    x.1 * y.2 + x.2 * y.1 + x.2 * y.2)

/-- Gaussian parity is multiplicative for the induced Gaussian operation. -/
theorem gaussianParity_mul (x y : GaussianInt) :
    gaussianParity (x * y) =
      gaussianMulMod2 (gaussianParity x) (gaussianParity y) := by
  apply Prod.ext <;>
    simp [gaussianParity, gaussianMulMod2, Zsqrtd.re_mul, Zsqrtd.im_mul]


/-- Eisenstein parity is multiplicative for the induced Eisenstein operation. -/
theorem eisensteinParity_mul (x y : TraceOneInt (-1)) :
    eisensteinParity (x * y) =
      eisensteinMulMod2 (eisensteinParity x) (eisensteinParity y) := by
  apply Prod.ext <;>
    simp [eisensteinParity, eisensteinMulMod2]

/-- Multiplicativity specialized to trace-one coordinate representatives. -/
theorem eisensteinCoord_mulMod2 (a b c d : ℤ) :
    eisensteinParity (eisensteinCoord a b * eisensteinCoord c d) =
      eisensteinMulMod2 (eisensteinParity (eisensteinCoord a b))
        (eisensteinParity (eisensteinCoord c d)) := by
  exact eisensteinParity_mul _ _

/-- The square of the second Gaussian direction is the first direction. -/
theorem gaussianMulMod2_deltaB_deltaB :
    gaussianMulMod2 deltaB deltaB = deltaA := by
  decide

/-- The square of the third Gaussian direction is zero. -/
theorem gaussianMulMod2_deltaC_deltaC :
    gaussianMulMod2 deltaC deltaC = 0 := by
  decide

/-- The square of the second Eisenstein direction is the third direction. -/
theorem eisensteinMulMod2_deltaB_deltaB :
    eisensteinMulMod2 deltaB deltaB = deltaC := by
  decide

/-- The square of the third Eisenstein direction is the second direction. -/
theorem eisensteinMulMod2_deltaC_deltaC :
    eisensteinMulMod2 deltaC deltaC = deltaB := by
  decide

/-- Every nonzero state has a nonzero square for the Eisenstein operation. -/
theorem eisensteinMulMod2_sq_ne_zero {x : TrominoState} (hx : x ≠ 0) :
    eisensteinMulMod2 x x ≠ 0 := by
  fin_cases x
  · exact (hx rfl).elim
  · decide
  · decide
  · decide

/-- No zero-preserving permutation intertwines the two induced multiplications. -/
theorem no_zero_preserving_mul_equiv_gaussian_eisenstein :
    ¬ ∃ φ : TrominoState ≃ TrominoState,
        φ 0 = 0 ∧
          ∀ x y,
            φ (gaussianMulMod2 x y) =
              eisensteinMulMod2 (φ x) (φ y) := by
  rintro ⟨φ, hzero, hmul⟩
  have hφC : φ deltaC ≠ 0 := by
    intro h
    apply deltaC_ne_zero
    apply φ.injective
    calc
      φ deltaC = 0 := h
      _ = φ 0 := hzero.symm
  have hsq := hmul deltaC deltaC
  rw [gaussianMulMod2_deltaC_deltaC, hzero] at hsq
  exact eisensteinMulMod2_sq_ne_zero hφC hsq.symm

/-- The two parity systems agree additively while retaining the multiplicative
obstruction. -/
theorem additive_parity_frame_agreement :
    Function.Surjective gaussianParity ∧
      Function.Surjective eisensteinParity ∧
      gaussianNonzeroDirectionParities = eisensteinNonzeroDirectionParities ∧
      (¬ ∃ φ : TrominoState ≃ TrominoState,
        φ 0 = 0 ∧
          ∀ x y,
            φ (gaussianMulMod2 x y) =
              eisensteinMulMod2 (φ x) (φ y)) := by
  exact ⟨gaussianParity_surjective, eisensteinParity_surjective,
    gaussian_eisenstein_nonzero_direction_parities_eq,
    no_zero_preserving_mul_equiv_gaussian_eisenstein⟩

/-!
## Finite connection to the V4 coefficient conventions

The canonical integral directions reduce to the three nonzero coefficients of
the Klein-four state carrier. Their sum is zero, providing the finite
coefficient identity used by the triangle-dual convention.
-/

/-- The three canonical Gaussian parity coefficients form the nonzero V4 set. -/
theorem integral_parity_coefficients :
    ({gaussianParity (⟨1, 0⟩ : GaussianInt),
      gaussianParity (⟨0, 1⟩ : GaussianInt),
      gaussianParity (⟨1, 1⟩ : GaussianInt)} : Finset TrominoState) =
      {deltaA, deltaB, deltaC} := by
  decide

/-- The three nonzero V4 directions sum to the zero state. -/
theorem triangle_dual_integral_parity_balance :
    deltaA + deltaB + deltaC = 0 := deltaA_add_deltaB_add_deltaC

end DkMath.Tromino

#print axioms DkMath.Tromino.gaussianParity
#print axioms DkMath.Tromino.eisensteinParity
#print axioms DkMath.Tromino.gaussianParity_mul
#print axioms DkMath.Tromino.eisensteinParity_mul
#print axioms DkMath.Tromino.no_zero_preserving_mul_equiv_gaussian_eisenstein
