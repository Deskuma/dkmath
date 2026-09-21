/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSquarePrimeSupport
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

#print "file: DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSquareIdealSupport"

namespace DkMath.FLT.Seven

noncomputable section

open SevenRealCubicInt
open Module
open scoped NumberField

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 500000

private def directSquareIdealSupportCoordinateAddEquiv :
    SevenRealCubicInt ≃+ (Fin 3 → ℤ) where
  toFun x i :=
    if i = 0 then x.fst else
    if i = 1 then x.snd else x.thd
  invFun f := ⟨f 0, f 1, f 2⟩
  left_inv x := by
    ext <;> simp
  right_inv f := by
    funext i
    fin_cases i <;> simp
  map_add' x y := by
    funext i
    fin_cases i <;> simp

private def directSquareIdealSupportCoordinateBasis :
    Basis (Fin 3) ℤ SevenRealCubicInt :=
  Basis.ofEquivFun directSquareIdealSupportCoordinateAddEquiv.toIntLinearEquiv

local instance directSquareIdealSupportModuleFree :
    Module.Free ℤ SevenRealCubicInt :=
  Module.Free.of_basis directSquareIdealSupportCoordinateBasis

local instance directSquareIdealSupportModuleFinite :
    Module.Finite ℤ SevenRealCubicInt :=
  Module.Finite.of_basis directSquareIdealSupportCoordinateBasis

private theorem directSquareIdealSupport_algebraNorm_eq_norm
    (x : SevenRealCubicInt) :
    Algebra.norm ℤ x = norm x := by
  rw [Algebra.norm_eq_matrix_det directSquareIdealSupportCoordinateBasis,
    Matrix.det_fin_three]
  simp [Algebra.leftMulMatrix_eq_repr_mul,
    directSquareIdealSupportCoordinateBasis,
    directSquareIdealSupportCoordinateAddEquiv,
    SevenRealCubicInt.norm]
  ring

private theorem directSquareIdealSupport_ringOfIntegersNorm_eq_norm
    (x : SevenRealCubicInt) :
    Algebra.norm ℤ (SevenRealCubic.modelEquivRingOfIntegers x) = norm x := by
  have h := Algebra.norm_eq_of_equiv_equiv
    (RingEquiv.refl ℤ) SevenRealCubic.modelEquivRingOfIntegers (by
      ext n
      simp) x
  simpa [directSquareIdealSupport_algebraNorm_eq_norm] using h.symm

/-! ## Principal-ideal norm bridge -/

theorem directOrbitSquareRefinement_absNorm_span_model
    (x : SevenRealCubicInt) :
    Ideal.absNorm
        (Ideal.span
          ({SevenRealCubic.modelEquivRingOfIntegers x} :
            Set (𝓞 SevenRealCubic.Field))) =
      Int.natAbs (norm x) := by
  rw [Ideal.absNorm_span_singleton,
    directSquareIdealSupport_ringOfIntegersNorm_eq_norm]

/-! ## Ideal-divisor membership and coprime transport -/

theorem directOrbitSquareRefinement_mem_of_principal_dvd
    {x : SevenRealCubicInt} {P : Ideal (𝓞 SevenRealCubic.Field)}
    (hP : P ∣
      Ideal.span
        ({SevenRealCubic.modelEquivRingOfIntegers x} :
          Set (𝓞 SevenRealCubic.Field))) :
    SevenRealCubic.modelEquivRingOfIntegers x ∈ P := by
  exact (Ideal.dvd_iff_le.mp hP) (Ideal.mem_span_singleton_self _)

theorem directOrbitSquareRefinement_squareRoots_isCoprime_ringOfIntegers
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    IsCoprime
      (Ideal.span
        ({SevenRealCubic.modelEquivRingOfIntegers t.gapSquareRoot} :
          Set (𝓞 SevenRealCubic.Field)))
      (Ideal.span
        ({SevenRealCubic.modelEquivRingOfIntegers t.quotientSquareRoot} :
          Set (𝓞 SevenRealCubic.Field))) := by
  rw [Ideal.isCoprime_span_singleton_iff]
  exact
    (directOrbitSquareRefinement_squareRoots_isCoprime t).map
      SevenRealCubic.modelEquivRingOfIntegers.toRingHom

/-! ## Two distinct prime ideals above a common norm prime -/

theorem directOrbitSquareRefinement_exists_distinct_prime_ideals
    {x y z q : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    (hq : q.Prime)
    (hqR : q ∣ Int.natAbs (norm t.gapSquareRoot))
    (hqS : q ∣ Int.natAbs (norm t.quotientSquareRoot)) :
    ∃ P Q : Ideal (𝓞 SevenRealCubic.Field),
      P.IsMaximal ∧
      Q.IsMaximal ∧
      P.under ℤ = Ideal.span {(q : ℤ)} ∧
      Q.under ℤ = Ideal.span {(q : ℤ)} ∧
      P.LiesOver (Ideal.span {(q : ℤ)}) ∧
      Q.LiesOver (Ideal.span {(q : ℤ)}) ∧
      P ∣
        Ideal.span
          ({SevenRealCubic.modelEquivRingOfIntegers t.gapSquareRoot} :
            Set (𝓞 SevenRealCubic.Field)) ∧
      Q ∣
        Ideal.span
          ({SevenRealCubic.modelEquivRingOfIntegers t.quotientSquareRoot} :
            Set (𝓞 SevenRealCubic.Field)) ∧
      P ≠ Q := by
  let rI : Ideal (𝓞 SevenRealCubic.Field) :=
    Ideal.span
      ({SevenRealCubic.modelEquivRingOfIntegers t.gapSquareRoot} :
        Set (𝓞 SevenRealCubic.Field))
  let sI : Ideal (𝓞 SevenRealCubic.Field) :=
    Ideal.span
      ({SevenRealCubic.modelEquivRingOfIntegers t.quotientSquareRoot} :
        Set (𝓞 SevenRealCubic.Field))
  have hqR' : q ∣ Ideal.absNorm rI := by
    change q ∣ Ideal.absNorm
      (Ideal.span
        ({SevenRealCubic.modelEquivRingOfIntegers t.gapSquareRoot} :
          Set (𝓞 SevenRealCubic.Field)))
    rw [directOrbitSquareRefinement_absNorm_span_model]
    exact hqR
  have hqS' : q ∣ Ideal.absNorm sI := by
    change q ∣ Ideal.absNorm
      (Ideal.span
        ({SevenRealCubic.modelEquivRingOfIntegers t.quotientSquareRoot} :
          Set (𝓞 SevenRealCubic.Field)))
    rw [directOrbitSquareRefinement_absNorm_span_model]
    exact hqS
  obtain ⟨P, hPmax, hPunder, hPdiv⟩ :=
    Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hq rI hqR'
  obtain ⟨Q, hQmax, hQunder, hQdiv⟩ :=
    Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hq sI hqS'
  have hcop : IsCoprime rI sI := by
    simpa only [rI, sI] using
      directOrbitSquareRefinement_squareRoots_isCoprime_ringOfIntegers t
  have hrmem :
      SevenRealCubic.modelEquivRingOfIntegers t.gapSquareRoot ∈ P :=
    directOrbitSquareRefinement_mem_of_principal_dvd hPdiv
  have hsmem :
      SevenRealCubic.modelEquivRingOfIntegers t.quotientSquareRoot ∈ Q :=
    directOrbitSquareRefinement_mem_of_principal_dvd hQdiv
  have hne : P ≠ Q := by
    intro hPQ
    have hrmem' :
        SevenRealCubic.modelEquivRingOfIntegers t.gapSquareRoot ∈ Q := by
      simpa [hPQ] using hrmem
    have hPmem : rI ≤ Q := by
      change Ideal.span
        ({SevenRealCubic.modelEquivRingOfIntegers t.gapSquareRoot} :
          Set (𝓞 SevenRealCubic.Field)) ≤ Q
      rw [Ideal.span_singleton_le_iff_mem]
      exact hrmem'
    have hQmem : sI ≤ Q := by
      change Ideal.span
        ({SevenRealCubic.modelEquivRingOfIntegers t.quotientSquareRoot} :
          Set (𝓞 SevenRealCubic.Field)) ≤ Q
      rw [Ideal.span_singleton_le_iff_mem]
      exact hsmem
    have htop : (⊤ : Ideal (𝓞 SevenRealCubic.Field)) ≤ Q := by
      rw [← hcop.sup_eq]
      exact sup_le hPmem hQmem
    exact hQmax.ne_top (top_unique htop)
  refine ⟨P, Q, hPmax, hQmax, hPunder, hQunder, ⟨hPunder.symm⟩,
    ⟨hQunder.symm⟩, ?_, ?_, hne⟩
  · exact hPdiv
  · exact hQdiv

/-! ## Cardinality consequence -/

theorem directOrbitSquareRefinement_two_primes_over_common_norm_prime
    {x y z q : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    (hq : q.Prime)
    (hqR : q ∣ Int.natAbs (norm t.gapSquareRoot))
    (hqS : q ∣ Int.natAbs (norm t.quotientSquareRoot)) :
    2 ≤
      (Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 SevenRealCubic.Field)).ncard := by
  obtain ⟨P, Q, hPmax, hQmax, hPunder, hQunder, _, _, _, _, hne⟩ :=
    directOrbitSquareRefinement_exists_distinct_prime_ideals t hq hqR hqS
  have hPmem :
      P ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 SevenRealCubic.Field) :=
    ⟨hPmax.isPrime, ⟨hPunder.symm⟩⟩
  have hQmem :
      Q ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 SevenRealCubic.Field) :=
    ⟨hQmax.isPrime, ⟨hQunder.symm⟩⟩
  have hqZ : Prime (q : ℤ) := by
    exact Int.prime_iff_natAbs_prime.mpr (by simpa using hq)
  let base : Ideal ℤ := Ideal.span {(q : ℤ)}
  have hbaseMax : base.IsMaximal := by
    dsimp [base]
    exact (Ideal.span_singleton_prime hqZ.ne_zero).mpr hqZ |>.isMaximal
      (by simpa using hqZ.ne_zero)
  let : base.IsMaximal := hbaseMax
  have hbase_ne_bot : base ≠ (⊥ : Ideal ℤ) := by
    intro hzero
    have hmem : (q : ℤ) ∈ base := by
      exact Ideal.mem_span_singleton_self _
    rw [hzero, Ideal.mem_bot] at hmem
    exact hqZ.ne_zero hmem
  have hfinite : (base.primesOver (𝓞 SevenRealCubic.Field)).Finite := by
    rw [← IsDedekindDomain.coe_primesOverFinset hbase_ne_bot]
    exact Set.toFinite _
  have hsubset :
      ({P, Q} : Set (Ideal (𝓞 SevenRealCubic.Field))) ⊆
        Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 SevenRealCubic.Field) := by
    intro I hI
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hI
    rcases hI with rfl | rfl
    · exact hPmem
    · exact hQmem
  have hcard := Set.ncard_le_ncard hsubset hfinite
  rw [Set.ncard_pair hne] at hcard
  exact hcard

end
end DkMath.FLT.Seven
