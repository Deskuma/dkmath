/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicCanonicalCommonFactor
import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSquareIdealSupport
import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSquareTwistObstruction

#print "file: DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicTrivialCommonFactor"

namespace DkMath.FLT.Seven

noncomputable section

open SevenRealCubicInt
open scoped NumberField Pointwise

set_option linter.style.longLine false
set_option linter.style.setOption false

namespace SevenRealCubic

def directOrbitTrivialCommonFactor_scalarIdealU
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p) : Ideal O :=
  Ideal.span {modelEquivRingOfIntegers (h.u : SevenRealCubicInt)}

def directOrbitTrivialCommonFactor_scalarIdealV
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p) : Ideal O :=
  Ideal.span {modelEquivRingOfIntegers (h.v : SevenRealCubicInt)}

private theorem directOrbitTrivialCommonFactor_span_model_ne_bot
    {s : SevenRealCubicInt} (hs : s ≠ 0) :
    Ideal.span ({modelEquivRingOfIntegers s} : Set O) ≠ ⊥ := by
  intro h
  have hm : modelEquivRingOfIntegers s ∈ (⊥ : Ideal O) := by
    rw [← h]
    exact Ideal.mem_span_singleton_self _
  have hm0 : modelEquivRingOfIntegers s = 0 := by
    simpa using hm
  apply hs
  apply modelEquivRingOfIntegers.injective
  simpa using hm0

theorem directOrbit_norm_coprime_ideal_coprime
    {S : Type} [CommRing S] [IsDedekindDomain S]
    [Module.Free ℤ S] [Module.Finite ℤ S] [Infinite S]
    {I J : Ideal S}
    (hcop : Nat.Coprime (Ideal.absNorm I) (Ideal.absNorm J))
    (_hI : I ≠ ⊥) (_hJ : J ≠ ⊥) :
    IsCoprime I J := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra htop
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (I ⊔ J) htop
  have hMI : I ≤ M := le_sup_left.trans hle
  have hMJ : J ≤ M := le_sup_right.trans hle
  have hnormMI : Ideal.absNorm M ∣ Ideal.absNorm I :=
    Ideal.absNorm_dvd_absNorm_of_le hMI
  have hnormMJ : Ideal.absNorm M ∣ Ideal.absNorm J :=
    Ideal.absNorm_dvd_absNorm_of_le hMJ
  have hnormM_one : Ideal.absNorm M = 1 := by
    apply Nat.dvd_one.mp
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd hnormMI hnormMJ
  exact hM.ne_top (Ideal.absNorm_eq_one_iff.mp hnormM_one)

theorem directOrbitTrivialCommonFactor_scalarIdealU_absNorm
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p) :
    Ideal.absNorm (directOrbitTrivialCommonFactor_scalarIdealU h) = h.u ^ 3 := by
  rw [directOrbitTrivialCommonFactor_scalarIdealU,
    directOrbitSquareRefinement_absNorm_span_model]
  norm_num [SevenRealCubicInt.norm]

theorem directOrbitTrivialCommonFactor_scalarIdealV_absNorm
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p) :
    Ideal.absNorm (directOrbitTrivialCommonFactor_scalarIdealV h) = h.v ^ 3 := by
  rw [directOrbitTrivialCommonFactor_scalarIdealV,
    directOrbitSquareRefinement_absNorm_span_model]
  norm_num [SevenRealCubicInt.norm]

theorem directOrbitTrivialCommonFactor_gapIdeal_absNorm_of_c_eq_one
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p) (hc : h.c = 1) :
    Ideal.absNorm (gapSquareIdeal h.squareRefinement) = h.u ^ 3 := by
  rw [gapSquareIdeal, directOrbitSquareRefinement_absNorm_span_model]
  simpa [hc] using h.gapNorm_eq

theorem directOrbitTrivialCommonFactor_quotientIdeal_absNorm_of_c_eq_one
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p) (hc : h.c = 1) :
    Ideal.absNorm (quotientSquareIdeal h.squareRefinement) = h.v ^ 3 := by
  rw [quotientSquareIdeal, directOrbitSquareRefinement_absNorm_span_model]
  simpa [hc] using h.quotientNorm_eq

private theorem directOrbitTrivialCommonFactor_gapRoot_ne_zero
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p) :
    h.squareRefinement.gapSquareRoot ≠ 0 :=
  directOrbit_squareTwist_squareRoot_ne_zero h.squareRefinement

private theorem directOrbitTrivialCommonFactor_quotientRoot_ne_zero
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p) :
    h.squareRefinement.quotientSquareRoot ≠ 0 := by
  intro hz
  have hpos := directOrbitSquareRefinement_quotient_square_norm_pos
    h.squareRefinement
  rw [hz] at hpos
  norm_num [SevenRealCubicInt.norm] at hpos

theorem directOrbitTrivialCommonFactor_cross_coprime
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p) (hc : h.c = 1) :
    IsCoprime (gapSquareIdeal h.squareRefinement)
        (directOrbitTrivialCommonFactor_scalarIdealV h) ∧
      IsCoprime (directOrbitTrivialCommonFactor_scalarIdealU h)
        (quotientSquareIdeal h.squareRefinement) := by
  have hpowcop : Nat.Coprime (h.u ^ 3) (h.v ^ 3) :=
    (h.u_v_coprime.pow_left 3).pow_right 3
  have hgap0 : gapSquareIdeal h.squareRefinement ≠ ⊥ := by
    apply directOrbitTrivialCommonFactor_span_model_ne_bot
    exact directOrbitTrivialCommonFactor_gapRoot_ne_zero h
  have hquot0 : quotientSquareIdeal h.squareRefinement ≠ ⊥ := by
    apply directOrbitTrivialCommonFactor_span_model_ne_bot
    exact directOrbitTrivialCommonFactor_quotientRoot_ne_zero h
  have hu0 : directOrbitTrivialCommonFactor_scalarIdealU h ≠ ⊥ := by
    apply directOrbitTrivialCommonFactor_span_model_ne_bot
    intro hz
    have hzfst := congrArg SevenRealCubicInt.fst hz
    have hz' : h.u = 0 := by simpa using hzfst
    exact h.u_pos.ne' hz'
  have hv0 : directOrbitTrivialCommonFactor_scalarIdealV h ≠ ⊥ := by
    apply directOrbitTrivialCommonFactor_span_model_ne_bot
    intro hz
    have hzfst := congrArg SevenRealCubicInt.fst hz
    have hz' : h.v = 0 := by simpa using hzfst
    exact h.v_pos.ne' hz'
  have hgap_norm := directOrbitTrivialCommonFactor_gapIdeal_absNorm_of_c_eq_one h hc
  have hquot_norm :=
    directOrbitTrivialCommonFactor_quotientIdeal_absNorm_of_c_eq_one h hc
  have hu_norm := directOrbitTrivialCommonFactor_scalarIdealU_absNorm h
  have hv_norm := directOrbitTrivialCommonFactor_scalarIdealV_absNorm h
  constructor
  · apply directOrbit_norm_coprime_ideal_coprime _ hgap0 hv0
    simpa [hgap_norm, hv_norm] using hpowcop
  · apply directOrbit_norm_coprime_ideal_coprime _ hu0 hquot0
    simpa [hu_norm, hquot_norm] using hpowcop

theorem directOrbitTrivialCommonFactor_ideal_product_of_c_eq_one
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p) (hc : h.c = 1) :
    gapSquareIdeal h.squareRefinement * quotientSquareIdeal h.squareRefinement =
      directOrbitTrivialCommonFactor_scalarIdealU h *
        directOrbitTrivialCommonFactor_scalarIdealV h := by
  have ha : h.squareRefinement.powerSplit.gapSplit.a = h.u * h.v := by
    simpa [hc] using h.unitPart_eq
  calc
    gapSquareIdeal h.squareRefinement * quotientSquareIdeal h.squareRefinement =
        Ideal.span {modelEquivRingOfIntegers
          (h.squareRefinement.powerSplit.gapSplit.a : SevenRealCubicInt)} :=
      directOrbitSquareRefinement_principal_ideal_scalar_split h.squareRefinement
    _ = Ideal.span {modelEquivRingOfIntegers
          ((h.u * h.v : ℕ) : SevenRealCubicInt)} := by rw [ha]
    _ = Ideal.span {modelEquivRingOfIntegers (h.u : SevenRealCubicInt) *
          modelEquivRingOfIntegers (h.v : SevenRealCubicInt)} := by
      simp only [Nat.cast_mul, map_mul]
    _ = directOrbitTrivialCommonFactor_scalarIdealU h *
        directOrbitTrivialCommonFactor_scalarIdealV h := by
      change Ideal.span {modelEquivRingOfIntegers (h.u : SevenRealCubicInt) *
          modelEquivRingOfIntegers (h.v : SevenRealCubicInt)} =
        Ideal.span {modelEquivRingOfIntegers (h.u : SevenRealCubicInt)} *
          Ideal.span {modelEquivRingOfIntegers (h.v : SevenRealCubicInt)}
      exact (Ideal.span_singleton_mul_span_singleton _ _).symm

theorem directOrbitTrivialCommonFactor_ideal_eq_scalar_of_c_eq_one
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p) (hc : h.c = 1) :
    gapSquareIdeal h.squareRefinement =
        directOrbitTrivialCommonFactor_scalarIdealU h ∧
      quotientSquareIdeal h.squareRefinement =
        directOrbitTrivialCommonFactor_scalarIdealV h := by
  let A := gapSquareIdeal h.squareRefinement
  let B := quotientSquareIdeal h.squareRefinement
  let X := directOrbitTrivialCommonFactor_scalarIdealU h
  let Y := directOrbitTrivialCommonFactor_scalarIdealV h
  have hprod : A * B = X * Y := by
    simpa [A, B, X, Y] using
      directOrbitTrivialCommonFactor_ideal_product_of_c_eq_one h hc
  have hcross := directOrbitTrivialCommonFactor_cross_coprime h hc
  have hAdvdXY : A ∣ X * Y := by
    rw [← hprod]
    exact dvd_mul_right A B
  have hXdvdAB : X ∣ A * B := by
    rw [hprod]
    exact dvd_mul_right X Y
  have hAdvdX : A ∣ X := hcross.1.dvd_of_dvd_mul_right hAdvdXY
  have hXdvdA : X ∣ A := by
    apply hcross.2.dvd_of_dvd_mul_left
    simpa [mul_comm] using hXdvdAB
  have hBdvdXY : B ∣ X * Y := by
    rw [← hprod]
    exact dvd_mul_left B A
  have hYdvdAB : Y ∣ A * B := by
    rw [hprod]
    exact dvd_mul_left Y X
  have hBdvdY : B ∣ Y := by
    apply hcross.2.symm.dvd_of_dvd_mul_right
    simpa [mul_comm] using hBdvdXY
  have hYdvdB : Y ∣ B := by
    apply hcross.1.symm.dvd_of_dvd_mul_left
    exact hYdvdAB
  have hAX : A = X := le_antisymm
    (Ideal.dvd_iff_le.mp hXdvdA) (Ideal.dvd_iff_le.mp hAdvdX)
  have hBY : B = Y := le_antisymm
    (Ideal.dvd_iff_le.mp hYdvdB) (Ideal.dvd_iff_le.mp hBdvdY)
  exact ⟨by simpa [A, X] using hAX, by simpa [B, Y] using hBY⟩

private theorem directOrbitTrivialCommonFactor_model_scalar_unit
    {r : SevenRealCubicInt} {u : ℕ}
    (hideal : Ideal.span ({modelEquivRingOfIntegers r} : Set O) =
      Ideal.span ({modelEquivRingOfIntegers (u : SevenRealCubicInt)} : Set O)) :
    ∃ eta : SevenRealCubicIntˣ,
      r = (eta : SevenRealCubicInt) * (u : SevenRealCubicInt) := by
  obtain ⟨w, hw⟩ := Ideal.span_singleton_eq_span_singleton.mp hideal
  let eta : SevenRealCubicIntˣ :=
    Units.map modelEquivRingOfIntegers.symm.toMonoidHom w⁻¹
  let wInv : Oˣ := w⁻¹
  have hw' : modelEquivRingOfIntegers r =
      (wInv : O) * modelEquivRingOfIntegers (u : SevenRealCubicInt) := by
    calc
      modelEquivRingOfIntegers r =
          modelEquivRingOfIntegers r * 1 := by simp
      _ = modelEquivRingOfIntegers r * ((w : O) * (wInv : O)) := by simp [wInv]
      _ = (modelEquivRingOfIntegers r * (w : O)) * (wInv : O) := by ring
      _ = modelEquivRingOfIntegers (u : SevenRealCubicInt) *
          (wInv : O) := by rw [hw]
      _ = (wInv : O) * modelEquivRingOfIntegers (u : SevenRealCubicInt) := by
        ac_rfl
  refine ⟨eta, ?_⟩
  have heta_val : modelEquivRingOfIntegers (eta : SevenRealCubicInt) =
      (wInv : O) := by
    simp [eta, wInv]
  apply modelEquivRingOfIntegers.injective
  simp only [map_mul, heta_val, map_natCast]
  simpa using hw'

theorem directOrbitTrivialCommonFactor_gap_scalar_unit_of_c_eq_one
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p) (hc : h.c = 1) :
    ∃ eta : SevenRealCubicIntˣ,
      h.squareRefinement.gapSquareRoot =
        (eta : SevenRealCubicInt) * (h.u : SevenRealCubicInt) := by
  apply directOrbitTrivialCommonFactor_model_scalar_unit
  simpa [gapSquareIdeal, directOrbitTrivialCommonFactor_scalarIdealU] using
    (directOrbitTrivialCommonFactor_ideal_eq_scalar_of_c_eq_one h hc).1

theorem directOrbitTrivialCommonFactor_quotient_scalar_unit_of_c_eq_one
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p) (hc : h.c = 1) :
    ∃ xi : SevenRealCubicIntˣ,
      h.squareRefinement.quotientSquareRoot =
        (xi : SevenRealCubicInt) * (h.v : SevenRealCubicInt) := by
  apply directOrbitTrivialCommonFactor_model_scalar_unit
  simpa [quotientSquareIdeal, directOrbitTrivialCommonFactor_scalarIdealV] using
    (directOrbitTrivialCommonFactor_ideal_eq_scalar_of_c_eq_one h hc).2

theorem directOrbitTrivialCommonFactor_gap_rotate_scalar_unit
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p)
    {eta : SevenRealCubicIntˣ}
    (heta : h.squareRefinement.gapSquareRoot =
      (eta : SevenRealCubicInt) * (h.u : SevenRealCubicInt)) :
    rotateEquiv h.squareRefinement.gapSquareRoot =
        (directOrbitRotateUnit eta : SevenRealCubicInt) *
          (h.u : SevenRealCubicInt) := by
  rw [heta, map_mul, directOrbitRotateUnit_val]
  change rotateEquiv (eta : SevenRealCubicInt) * (h.u : SevenRealCubicInt) =
    rotateEquiv (eta : SevenRealCubicInt) * (h.u : SevenRealCubicInt)
  rfl

theorem directOrbitTrivialCommonFactor_gap_twice_rotate_scalar_unit
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p)
    {eta : SevenRealCubicIntˣ}
    (heta : h.squareRefinement.gapSquareRoot =
      (eta : SevenRealCubicInt) * (h.u : SevenRealCubicInt)) :
    rotateEquiv (rotateEquiv h.squareRefinement.gapSquareRoot) =
        (directOrbitRotateUnit (directOrbitRotateUnit eta) : SevenRealCubicInt) *
          (h.u : SevenRealCubicInt) := by
  rw [directOrbitTrivialCommonFactor_gap_rotate_scalar_unit h heta,
    map_mul, directOrbitRotateUnit_val]
  change rotateEquiv (rotateEquiv (eta : SevenRealCubicInt)) *
      (h.u : SevenRealCubicInt) =
    rotateEquiv (rotateEquiv (eta : SevenRealCubicInt)) *
      (h.u : SevenRealCubicInt)
  rfl

set_option maxHeartbeats 800000 in
-- The ring normalization below factors the seventh-power identity without
-- unfolding the quotient-ring representation of `SevenRealCubicInt`.
theorem directOrbitTrivialCommonFactor_unit_twisted_eq
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p) (_hc : h.c = 1)
    (eta : SevenRealCubicIntˣ)
    (heta : h.squareRefinement.gapSquareRoot =
      (eta : SevenRealCubicInt) * (h.u : SevenRealCubicInt)) :
    (directOrbitSquareTwistCoeff0 h.squareRefinement : SevenRealCubicInt) *
          ((eta : SevenRealCubicInt) ^ 7) ^ 2 +
        (directOrbitSquareTwistCoeff1 h.squareRefinement : SevenRealCubicInt) *
          ((directOrbitRotateUnit eta : SevenRealCubicInt) ^ 7) ^ 2 +
        (directOrbitSquareTwistCoeff2 h.squareRefinement : SevenRealCubicInt) *
          ((directOrbitRotateUnit (directOrbitRotateUnit eta) :
            SevenRealCubicInt) ^ 7) ^ 2 = 0 := by
  have hU : (h.u : SevenRealCubicInt) ≠ 0 := by
    intro hz
    have hzfst := congrArg SevenRealCubicInt.fst hz
    have hz' : h.u = 0 := by simpa using hzfst
    exact h.u_pos.ne' hz'
  have hEq := directOrbit_squareTwist_twisted_eq h.squareRefinement
  rw [heta] at hEq
  simp only [map_mul, map_natCast] at hEq
  simp only [mul_pow] at hEq
  have hfactor :
      ((directOrbitSquareTwistCoeff0 h.squareRefinement : SevenRealCubicInt) *
          ((eta : SevenRealCubicInt) ^ 7) ^ 2 +
        (directOrbitSquareTwistCoeff1 h.squareRefinement : SevenRealCubicInt) *
          (rotateEquiv (eta : SevenRealCubicInt) ^ 7) ^ 2 +
        (directOrbitSquareTwistCoeff2 h.squareRefinement : SevenRealCubicInt) *
          (rotateEquiv (rotateEquiv (eta : SevenRealCubicInt)) ^ 7) ^ 2) *
        ((h.u : SevenRealCubicInt) ^ 7) ^ 2 = 0 := by
    calc
      _ = (directOrbitSquareTwistCoeff0 h.squareRefinement : SevenRealCubicInt) *
            (((eta : SevenRealCubicInt) ^ 7) ^ 2 *
              ((h.u : SevenRealCubicInt) ^ 7) ^ 2) +
          (directOrbitSquareTwistCoeff1 h.squareRefinement : SevenRealCubicInt) *
            ((rotateEquiv (eta : SevenRealCubicInt) ^ 7) ^ 2 *
              ((h.u : SevenRealCubicInt) ^ 7) ^ 2) +
          (directOrbitSquareTwistCoeff2 h.squareRefinement : SevenRealCubicInt) *
            ((rotateEquiv (rotateEquiv (eta : SevenRealCubicInt)) ^ 7) ^ 2 *
              ((h.u : SevenRealCubicInt) ^ 7) ^ 2) := by ring
      _ = 0 := hEq
  have hcancel :=
    (mul_eq_zero.mp hfactor).resolve_right (pow_ne_zero 2 (pow_ne_zero 7 hU))
  simpa only [directOrbitRotateUnit_val] using hcancel

end SevenRealCubic
end
end DkMath.FLT.Seven
