/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRealCubicCurrentCommonPrimePacket
import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicCommonPrimeKummer
import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicResidueSupport

#print "file: DkMath.FLT.Seven.SevenRealCubicCurrentOrientedGapTransport"

namespace DkMath.FLT.Seven

noncomputable section

open SevenRealCubicInt
open scoped NumberField

namespace SevenRealCubic

set_option linter.style.longLine false
set_option linter.style.haveILetI false

/-! The oriented gap-prime evaluation, kept separate from the quotient-side
    evaluation in `CurrentCommonPrimeResiduePacket`. -/

structure CurrentOrientedGapPrimeTransport
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p) (q : ℕ) where
  q_prime : q.Prime
  q_dvd_c : q ∣ h.c
  P : Ideal O
  P_maximal : P.IsMaximal
  P_prime : P.IsPrime
  P_liesOver : P.LiesOver (Ideal.span {(q : ℤ)})
  evalEquiv : P.ResidueField ≃+* ZMod q
  f0 : SevenRealCubicInt →+* ZMod q
  f0_formula : f0 = evalEquiv.toRingHom.comp
      (@directOrbitCommonPrimeEval P P_prime)
  gap_mem : modelEquivRingOfIntegers h.squareRefinement.gapSquareRoot ∈ P
  gap_zero : f0 h.squareRefinement.gapSquareRoot = 0
  rotate_gap_ne_zero : f0 (rotateEquiv h.squareRefinement.gapSquareRoot) ≠ 0
  rotate2_gap_ne_zero : f0
      (rotateEquiv (rotateEquiv h.squareRefinement.gapSquareRoot)) ≠ 0

theorem currentOrientedGapPrimeTransport
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p)
    (q : ℕ) (hq : q.Prime) (hqc : q ∣ h.c) :
    Nonempty (CurrentOrientedGapPrimeTransport h q) := by
  obtain ⟨P, hPmax, hPlies, hgap, hrot1, hrot2⟩ :=
    directOrbitCommonPrime_oriented_gap_prime h q hq hqc
  let hPprime : P.IsPrime := hPmax.isPrime
  letI : P.IsMaximal := hPmax
  letI : P.IsPrime := hPprime
  letI : P.LiesOver (Ideal.span {(q : ℤ)}) := hPlies
  letI : Fintype P.ResidueField := Fintype.ofFinite P.ResidueField
  letI : Fact q.Prime := ⟨hq⟩
  have hdata := directOrbitCommonPrime_dvd_data h q hqc
  have hsplit := common_norm_prime_complete_split
    h.squareRefinement hq hdata.1 hdata.2.1
  have hinertia : P.inertiaDeg ℤ = 1 := by
    rw [← Ideal.inertiaDegIn_eq_inertiaDeg
      (Ideal.span {(q : ℤ)}) P Gal(Field / ℚ)]
    exact hsplit.2.2.2
  have hcardNat : Nat.card P.ResidueField = q :=
    residueField_card_of_inertiaDeg_one hinertia
  have hcard : Fintype.card P.ResidueField = q := by
    rw [Fintype.card_eq_nat_card, hcardNat]
  let e : P.ResidueField ≃+* ZMod q :=
    FiniteField.ringEquivOfCardEq (K := P.ResidueField) (K' := ZMod q) (by
      simpa [ZMod.card] using hcard)
  let f : SevenRealCubicInt →+* ZMod q :=
    e.toRingHom.comp (directOrbitCommonPrimeEval P)
  have hzero {a : SevenRealCubicInt}
      (ha : modelEquivRingOfIntegers a ∈ P) : f a = 0 := by
    have ha' : modelToRingOfIntegers a ∈ P := by
      simpa only [modelEquivRingOfIntegers_apply] using ha
    simp [f, directOrbitCommonPrimeEval,
      Ideal.algebraMap_residueField_eq_zero.mpr ha']
  have hne {a : SevenRealCubicInt}
      (ha : modelEquivRingOfIntegers a ∉ P) : f a ≠ 0 := by
    intro hz
    apply ha
    have hz' : algebraMap O P.ResidueField
        (modelEquivRingOfIntegers a) = 0 := by
      simpa [f, directOrbitCommonPrimeEval] using congrArg e.symm hz
    exact Ideal.algebraMap_residueField_eq_zero.mp hz'
  refine ⟨{
    q_prime := hq
    q_dvd_c := hqc
    P := P
    P_maximal := hPmax
    P_prime := hPprime
    P_liesOver := hPlies
    evalEquiv := e
    f0 := f
    f0_formula := by rfl
    gap_mem := hgap
    gap_zero := hzero hgap
    rotate_gap_ne_zero := hne hrot1
    rotate2_gap_ne_zero := hne hrot2 }⟩

def CurrentOrientedGapPrimeTransport.f1
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}
    (a : CurrentOrientedGapPrimeTransport h q) :
    SevenRealCubicInt →+* ZMod q :=
  a.f0.comp SevenRealCubicInt.rotateEquiv.symm.toRingHom

def CurrentOrientedGapPrimeTransport.f2
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}
    (a : CurrentOrientedGapPrimeTransport h q) :
    SevenRealCubicInt →+* ZMod q :=
  a.f0.comp (SevenRealCubicInt.rotateEquiv.symm.toRingHom.comp
    SevenRealCubicInt.rotateEquiv.symm.toRingHom)

theorem CurrentOrientedGapPrimeTransport.f1_rotate
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}
    (a : CurrentOrientedGapPrimeTransport h q) (u : SevenRealCubicInt) :
    a.f1 (rotateEquiv u) = a.f0 u := by
  change a.f0 (rotateEquiv.symm (rotateEquiv u)) = a.f0 u
  rw [RingEquiv.symm_apply_apply]

theorem CurrentOrientedGapPrimeTransport.f2_rotate_twice
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}
    (a : CurrentOrientedGapPrimeTransport h q) (u : SevenRealCubicInt) :
    a.f2 (rotateEquiv (rotateEquiv u)) = a.f0 u := by
  have hinv (v : SevenRealCubicInt) :
      rotateEquiv.symm v = rotateEquiv (rotateEquiv v) := by
    apply rotateEquiv.injective
    simp only [RingEquiv.apply_symm_apply, rotateEquiv_three]
  change a.f0 (rotateEquiv.symm
      (rotateEquiv.symm (rotateEquiv (rotateEquiv u)))) = a.f0 u
  rw [hinv, hinv, rotateEquiv_three, rotateEquiv_three]

theorem CurrentOrientedGapPrimeTransport.f1_gap_rotate_zero
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}
    (a : CurrentOrientedGapPrimeTransport h q) :
    a.f1 (rotateEquiv h.squareRefinement.gapSquareRoot) = 0 := by
  rw [a.f1_rotate, a.gap_zero]

theorem CurrentOrientedGapPrimeTransport.f1_gap_rotate2_ne_zero
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}
    (a : CurrentOrientedGapPrimeTransport h q) :
    a.f1 (rotateEquiv (rotateEquiv h.squareRefinement.gapSquareRoot)) ≠ 0 := by
  intro hz
  have := a.f1_rotate (rotateEquiv h.squareRefinement.gapSquareRoot)
  rw [hz] at this
  exact a.rotate_gap_ne_zero this.symm

theorem CurrentOrientedGapPrimeTransport.f2_gap_rotate2_zero
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}
    (a : CurrentOrientedGapPrimeTransport h q) :
    a.f2 (rotateEquiv (rotateEquiv h.squareRefinement.gapSquareRoot)) = 0 := by
  rw [a.f2_rotate_twice, a.gap_zero]

theorem CurrentOrientedGapPrimeTransport.f1_gap_zero_ne_zero
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}
    (a : CurrentOrientedGapPrimeTransport h q) :
    a.f1 h.squareRefinement.gapSquareRoot ≠ 0 := by
  intro hz
  have hh := a.f1_rotate
    (rotateEquiv (rotateEquiv h.squareRefinement.gapSquareRoot))
  rw [rotateEquiv_three, hz] at hh
  exact a.rotate2_gap_ne_zero hh.symm

theorem CurrentOrientedGapPrimeTransport.f2_gap_zero_ne_zero
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}
    (a : CurrentOrientedGapPrimeTransport h q) :
    a.f2 h.squareRefinement.gapSquareRoot ≠ 0 := by
  intro hz
  have hh := a.f2_rotate_twice
    (rotateEquiv h.squareRefinement.gapSquareRoot)
  rw [rotateEquiv_three, hz] at hh
  exact a.rotate_gap_ne_zero hh.symm

theorem CurrentOrientedGapPrimeTransport.f2_gap_rotate_ne_zero
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}
    (a : CurrentOrientedGapPrimeTransport h q) :
    a.f2 (rotateEquiv h.squareRefinement.gapSquareRoot) ≠ 0 := by
  intro hz
  have hh : a.f2 (rotateEquiv h.squareRefinement.gapSquareRoot) =
      a.f0 (rotateEquiv (rotateEquiv h.squareRefinement.gapSquareRoot)) := by
    simpa only [rotateEquiv_three] using a.f2_rotate_twice
      (rotateEquiv (rotateEquiv h.squareRefinement.gapSquareRoot))
  rw [hz] at hh
  exact a.rotate2_gap_ne_zero hh.symm

theorem CurrentOrientedGapPrimeTransport.zero_nonzero_pattern
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}
    (a : CurrentOrientedGapPrimeTransport h q) :
    a.f0 h.squareRefinement.gapSquareRoot = 0 ∧
      a.f0 (rotateEquiv h.squareRefinement.gapSquareRoot) ≠ 0 ∧
      a.f0 (rotateEquiv (rotateEquiv h.squareRefinement.gapSquareRoot)) ≠ 0 ∧
      a.f1 h.squareRefinement.gapSquareRoot ≠ 0 ∧
      a.f1 (rotateEquiv h.squareRefinement.gapSquareRoot) = 0 ∧
      a.f1 (rotateEquiv (rotateEquiv h.squareRefinement.gapSquareRoot)) ≠ 0 ∧
      a.f2 h.squareRefinement.gapSquareRoot ≠ 0 ∧
      a.f2 (rotateEquiv h.squareRefinement.gapSquareRoot) ≠ 0 ∧
      a.f2 (rotateEquiv (rotateEquiv h.squareRefinement.gapSquareRoot)) = 0 := by
  exact ⟨a.gap_zero, a.rotate_gap_ne_zero, a.rotate2_gap_ne_zero,
    a.f1_gap_zero_ne_zero, a.f1_gap_rotate_zero,
    a.f1_gap_rotate2_ne_zero, a.f2_gap_zero_ne_zero,
    a.f2_gap_rotate_ne_zero, a.f2_gap_rotate2_zero⟩

end SevenRealCubic
end
end DkMath.FLT.Seven
