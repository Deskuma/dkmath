/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicCubeDefect
import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSquareGaloisSupport
import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSquareIdealSupport

#print "file: DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicPrimeAllocation"

namespace DkMath.FLT.Seven

noncomputable section

open SevenRealCubicInt
open scoped NumberField

set_option linter.style.longLine false
set_option linter.style.setOption false

namespace SevenRealCubic

def gapSquareIdeal
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) : Ideal O :=
  Ideal.span {modelEquivRingOfIntegers t.gapSquareRoot}

def quotientSquareIdeal
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) : Ideal O :=
  Ideal.span {modelEquivRingOfIntegers t.quotientSquareRoot}

private theorem principal_span_mul_eq_of_unit_mul
    {A : Type*} [CommRing A] {r s a : A} {u : Aˣ}
    (hu : IsUnit (u : A)) (h : r * s = (u : A) * a) :
    Ideal.span ({r} : Set A) * Ideal.span ({s} : Set A) =
      Ideal.span ({a} : Set A) := by
  calc
    Ideal.span ({r} : Set A) * Ideal.span ({s} : Set A) =
        Ideal.span ({r * s} : Set A) :=
      Ideal.span_singleton_mul_span_singleton r s
    _ = Ideal.span ({(u : A) * a} : Set A) := by rw [h]
    _ = Ideal.span ({a} : Set A) := by
      rw [mul_comm]
      exact Ideal.span_singleton_mul_right_unit hu a

theorem directOrbitSquareRefinement_principal_ideal_scalar_split
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    Ideal.span ({modelEquivRingOfIntegers t.gapSquareRoot} : Set O) *
        Ideal.span ({modelEquivRingOfIntegers t.quotientSquareRoot} : Set O) =
      Ideal.span ({modelEquivRingOfIntegers
        (t.powerSplit.gapSplit.a : SevenRealCubicInt)} : Set O) := by
  obtain ⟨u, hu⟩ := directOrbitSquareRefinement_squareRoots_unit_split t
  let uO : Oˣ := Units.map modelEquivRingOfIntegers.toMonoidHom u
  have hmap :
      modelEquivRingOfIntegers (t.gapSquareRoot * t.quotientSquareRoot) =
        modelEquivRingOfIntegers (u : SevenRealCubicInt) *
          modelEquivRingOfIntegers
            (t.powerSplit.gapSplit.a : SevenRealCubicInt) := by
    simpa only [map_mul] using congrArg modelEquivRingOfIntegers hu
  exact principal_span_mul_eq_of_unit_mul
    (A := O)
    (r := modelEquivRingOfIntegers t.gapSquareRoot)
    (s := modelEquivRingOfIntegers t.quotientSquareRoot)
    (a := modelEquivRingOfIntegers
      (t.powerSplit.gapSplit.a : SevenRealCubicInt))
    (u := uO) uO.isUnit (by simpa [uO] using hmap)

theorem directOrbitSquareRefinement_ideal_coprime
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    IsCoprime (gapSquareIdeal t) (quotientSquareIdeal t) := by
  exact directOrbitSquareRefinement_squareRoots_isCoprime_ringOfIntegers t

theorem directOrbitSquareRefinement_common_prime_dvd_scalar
    {x y z q : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    (hq : q.Prime)
    (hqR : q ∣ Int.natAbs (norm t.gapSquareRoot))
    (_hqS : q ∣ Int.natAbs (norm t.quotientSquareRoot)) :
    q ∣ t.powerSplit.gapSplit.a := by
  have hqcube : q ∣ t.powerSplit.gapSplit.a ^ 3 := by
    rw [← directOrbitSquareRefinement_squareRoots_norm_product t]
    exact dvd_mul_of_dvd_left hqR _
  exact hq.dvd_of_dvd_pow hqcube

theorem directOrbitSquareRefinement_prime_ideal_allocation_xor
    {x y z q : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    (hq : q.Prime)
    (hqR : q ∣ Int.natAbs (norm t.gapSquareRoot))
    (hqS : q ∣ Int.natAbs (norm t.quotientSquareRoot))
    (P : Ideal O) (hPprime : P.IsPrime)
    (hPover : P.LiesOver (Ideal.span {(q : ℤ)})) :
    Xor (gapSquareIdeal t ≤ P) (quotientSquareIdeal t ≤ P) := by
  have hqa := directOrbitSquareRefinement_common_prime_dvd_scalar
    t hq hqR hqS
  have hqmem : (q : O) ∈ P := by
    apply (Ideal.mem_under ℤ P).mp
    rw [← hPover.over]
    exact Ideal.mem_span_singleton_self _
  have hamem :
      modelEquivRingOfIntegers
          (t.powerSplit.gapSplit.a : SevenRealCubicInt) ∈ P := by
    obtain ⟨k, hk⟩ := hqa
    have hkO : (t.powerSplit.gapSplit.a : O) = (q : O) * (k : O) := by
      exact_mod_cast hk
    rw [show modelEquivRingOfIntegers
        (t.powerSplit.gapSplit.a : SevenRealCubicInt) =
          (t.powerSplit.gapSplit.a : O) by simp, hkO]
    exact P.mul_mem_right _ hqmem
  have hprodmem :
      modelEquivRingOfIntegers t.gapSquareRoot *
          modelEquivRingOfIntegers t.quotientSquareRoot ∈ P := by
    have hspan :
        Ideal.span {modelEquivRingOfIntegers
          (t.powerSplit.gapSplit.a : SevenRealCubicInt)} ≤ P :=
      (Ideal.span_singleton_le_iff_mem P).mpr hamem
    have hprodideal : gapSquareIdeal t * quotientSquareIdeal t ≤ P := by
      change (Ideal.span ({modelEquivRingOfIntegers t.gapSquareRoot} : Set O) *
          Ideal.span ({modelEquivRingOfIntegers t.quotientSquareRoot} : Set O)) ≤ P
      rw [directOrbitSquareRefinement_principal_ideal_scalar_split t]
      exact hspan
    exact hprodideal (Ideal.mul_mem_mul
      (Ideal.mem_span_singleton_self _) (Ideal.mem_span_singleton_self _))
  rcases hPprime.mem_or_mem hprodmem with hr | hs
  · refine Or.inl ⟨(Ideal.span_singleton_le_iff_mem P).mpr hr, ?_⟩
    intro hs'
    exact hPprime.ne_top (top_unique ((directOrbitSquareRefinement_ideal_coprime t).sup_eq ▸
      sup_le ((Ideal.span_singleton_le_iff_mem P).mpr hr) hs') )
  · refine Or.inr ⟨(Ideal.span_singleton_le_iff_mem P).mpr hs, ?_⟩
    intro hr'
    exact hPprime.ne_top (top_unique ((directOrbitSquareRefinement_ideal_coprime t).sup_eq ▸
      sup_le hr' ((Ideal.span_singleton_le_iff_mem P).mpr hs)) )

end SevenRealCubic
end
end DkMath.FLT.Seven
