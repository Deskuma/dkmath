/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRealCubicCurrentResidueKernel

#print "file: DkMath.FLT.Seven.SevenRealCubicCurrentOrientationRatio"

namespace DkMath.FLT.Seven

noncomputable section

open SevenRealCubicInt
open scoped NumberField Pointwise

namespace SevenRealCubic

set_option linter.style.longLine false
set_option linter.style.haveILetI false

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

section CurrentPackets

variable {x y z : ℕ} {source : CounterexamplePack x y z}
variable {r : PrimitiveCounterexampleRamifiedProvenance source}
variable {p : DirectRealCubicRootPacket source r}
variable {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}

private theorem current_gap_zero_at_f0
    (b : CurrentOrientedGapPrimeTransport h q) :
    b.f0 (directOrbitGap p) = 0 := by
  have hfactor : directOrbitGap p =
      eisensteinAxis ^ (32 + 42 * h.squareRefinement.powerSplit.gapSplit.k) *
        (h.squareRefinement.powerSplit.gapUnit : SevenRealCubicInt) *
        (h.squareRefinement.gapSquareUnit : SevenRealCubicInt) ^ 7 *
        h.squareRefinement.gapSquareRoot ^ 14 := by
    rw [h.squareRefinement.powerSplit.gap_eq,
      h.squareRefinement.powerSplit.gapCore_eq,
      h.squareRefinement.gapRoot_eq]
    ring
  rw [hfactor]
  simp [map_mul, map_pow, b.gap_zero]

private theorem current_gap_f0_rotate_eq
    (b : CurrentOrientedGapPrimeTransport h q) :
    b.f0 (rotateEquiv p.rho) = b.f0 p.rho := by
  have hz := congrArg b.f0 (show directOrbitGap p =
      rotateEquiv p.rho - p.rho by rfl)
  have hz' : b.f0 (rotateEquiv p.rho) - b.f0 p.rho = 0 := by
    rw [← map_sub]
    simpa [current_gap_zero_at_f0] using hz.symm
  exact sub_eq_zero.mp hz'

private theorem current_f1_rho_zero_eq_f0_rho_two
    (b : CurrentOrientedGapPrimeTransport h q) :
    b.f1 p.rho = b.f0 (rotateEquiv (rotateEquiv p.rho)) := by
  change b.f0 (rotateEquiv.symm p.rho) = _
  have hinv (u : SevenRealCubicInt) :
      rotateEquiv.symm u = rotateEquiv (rotateEquiv u) := by
    apply rotateEquiv.injective
    simp only [RingEquiv.apply_symm_apply, rotateEquiv_three]
  rw [hinv]

private theorem current_f2_rho_zero_eq_f0_rho_one
    (b : CurrentOrientedGapPrimeTransport h q) :
    b.f2 p.rho = b.f0 (rotateEquiv p.rho) := by
  change b.f0 (rotateEquiv.symm (rotateEquiv.symm p.rho)) = _
  have hinv (u : SevenRealCubicInt) :
      rotateEquiv.symm u = rotateEquiv (rotateEquiv u) := by
    apply rotateEquiv.injective
    simp only [RingEquiv.apply_symm_apply, rotateEquiv_three]
  rw [hinv, hinv, rotateEquiv_three]

private theorem current_f2_rho_one_eq_f0_rho_two
    (b : CurrentOrientedGapPrimeTransport h q) :
    b.f2 (rotateEquiv p.rho) =
      b.f0 (rotateEquiv (rotateEquiv p.rho)) := by
  have hh := b.f2_rotate_twice (rotateEquiv (rotateEquiv p.rho))
  simpa only [rotateEquiv_three] using hh

theorem currentOrientedGap_f0_rho_orbit_ne_zero
    (a : CurrentCommonPrimeResiduePacket h q)
    (b : CurrentOrientedGapPrimeTransport h q) :
    b.f0 p.rho ≠ 0 ∧
      b.f0 (rotateEquiv p.rho) ≠ 0 ∧
      b.f0 (rotateEquiv (rotateEquiv p.rho)) ≠ 0 := by
  have hrot : b.f0 (rotateEquiv p.rho) = b.f0 p.rho :=
    current_gap_f0_rotate_eq b
  rcases currentCommonPrime_quotient_oriented_gap_orbit a b with hQ | hQ
  · have hmap := currentCommonPrime_evalReal_eq_f1 a b hQ
    have h0 : b.f0 p.rho ≠ 0 := by
      rw [← b.f1_rotate p.rho, ← hmap]
      exact a.rotate_rho_ne_zero
    have h2 : b.f0 (rotateEquiv (rotateEquiv p.rho)) ≠ 0 := by
      rw [← current_f1_rho_zero_eq_f0_rho_two b, ← hmap]
      exact a.rho_ne_zero
    exact ⟨h0, hrot ▸ h0, h2⟩
  · have hmap := currentCommonPrime_evalReal_eq_f2 a b hQ
    have h1 : b.f0 (rotateEquiv p.rho) ≠ 0 := by
      rw [← current_f2_rho_zero_eq_f0_rho_one b, ← hmap]
      exact a.rho_ne_zero
    have h2 : b.f0 (rotateEquiv (rotateEquiv p.rho)) ≠ 0 := by
      rw [← current_f2_rho_one_eq_f0_rho_two b, ← hmap]
      exact a.rotate_rho_ne_zero
    exact ⟨hrot ▸ h1, h1, h2⟩

def currentGapDelta
    (a : CurrentCommonPrimeResiduePacket h q)
    (b : CurrentOrientedGapPrimeTransport h q) : (ZMod q)ˣ := by
  letI : Fact q.Prime := ⟨a.q_prime⟩
  exact Units.mk0
    (b.f0 p.rho / b.f0 (rotateEquiv (rotateEquiv p.rho)))
    (div_ne_zero
      (currentOrientedGap_f0_rho_orbit_ne_zero a b).1
      (currentOrientedGap_f0_rho_orbit_ne_zero a b).2.2)

theorem currentCommonPrime_tau_eq_currentGapDelta_of_f1
    (a : CurrentCommonPrimeResiduePacket h q)
    (b : CurrentOrientedGapPrimeTransport h q)
    (hQ : a.Q = (directOrbitGaloisSigma : Gal(Field/ℚ)) • b.P) :
    a.tau = currentGapDelta a b := by
  letI : Fact q.Prime := ⟨a.q_prime⟩
  have hmap := currentCommonPrime_evalReal_eq_f1 a b hQ
  apply Units.ext
  change a.evalReal (rotateEquiv p.rho) / a.evalReal p.rho = _
  rw [hmap, b.f1_rotate, current_f1_rho_zero_eq_f0_rho_two]
  rfl

theorem currentCommonPrime_tau_eq_currentGapDelta_inv_of_f2
    (a : CurrentCommonPrimeResiduePacket h q)
    (b : CurrentOrientedGapPrimeTransport h q)
    (hQ : a.Q = (directOrbitGaloisSigma : Gal(Field/ℚ)) ^ 2 • b.P) :
    a.tau = (currentGapDelta a b)⁻¹ := by
  letI : Fact q.Prime := ⟨a.q_prime⟩
  have hmap := currentCommonPrime_evalReal_eq_f2 a b hQ
  have horbit := currentOrientedGap_f0_rho_orbit_ne_zero a b
  have hrot := current_gap_f0_rotate_eq b
  apply Units.ext
  change a.evalReal (rotateEquiv p.rho) / a.evalReal p.rho = _
  rw [hmap, current_f2_rho_one_eq_f0_rho_two,
    current_f2_rho_zero_eq_f0_rho_one, hrot]
  simp only [currentGapDelta, Units.val_inv_eq_inv_val, Units.val_mk0]
  field_simp [horbit.1, horbit.2.2]

theorem currentGapDelta_pow_seven
    (a : CurrentCommonPrimeResiduePacket h q)
    (b : CurrentOrientedGapPrimeTransport h q) :
    currentGapDelta a b ^ 7 = 1 := by
  rcases currentCommonPrime_quotient_oriented_gap_orbit a b with hQ | hQ
  · rw [← currentCommonPrime_tau_eq_currentGapDelta_of_f1 a b hQ]
    exact a.tau_pow_seven
  · have hinv : (currentGapDelta a b)⁻¹ ^ 7 = 1 := by
      rw [← currentCommonPrime_tau_eq_currentGapDelta_inv_of_f2 a b hQ]
      exact a.tau_pow_seven
    have := congrArg Inv.inv hinv
    simpa only [inv_pow, inv_one, inv_inv] using this

theorem currentGapDelta_ne_one
    (a : CurrentCommonPrimeResiduePacket h q)
    (b : CurrentOrientedGapPrimeTransport h q) :
    currentGapDelta a b ≠ 1 := by
  rcases currentCommonPrime_quotient_oriented_gap_orbit a b with hQ | hQ
  · intro hdelta
    apply a.tau_ne_one
    rw [currentCommonPrime_tau_eq_currentGapDelta_of_f1 a b hQ,
      hdelta]
  · intro hdelta
    apply a.tau_ne_one
    rw [currentCommonPrime_tau_eq_currentGapDelta_inv_of_f2 a b hQ,
      hdelta, inv_one]

theorem currentGapDelta_orderOf
    (a : CurrentCommonPrimeResiduePacket h q)
    (b : CurrentOrientedGapPrimeTransport h q) :
    orderOf (currentGapDelta a b) = 7 :=
  orderOf_eq_prime (currentGapDelta_pow_seven a b)
    (currentGapDelta_ne_one a b)

theorem currentCommonPrime_tau_orientation_law
    (a : CurrentCommonPrimeResiduePacket h q)
    (b : CurrentOrientedGapPrimeTransport h q) :
    a.tau = currentGapDelta a b ∨
      a.tau = (currentGapDelta a b)⁻¹ := by
  rcases currentCommonPrime_quotient_oriented_gap_orbit a b with hQ | hQ
  · exact Or.inl (currentCommonPrime_tau_eq_currentGapDelta_of_f1 a b hQ)
  · exact Or.inr (currentCommonPrime_tau_eq_currentGapDelta_inv_of_f2 a b hQ)

theorem currentCommonPrime_cyclotomic_ratio_orientation_law
    (c : CurrentCommonPrimeCyclotomicPacket h q)
    (b : CurrentOrientedGapPrimeTransport h q) :
    c.ratio = (currentGapDelta c.residue b) ^ (c.phase.val + 1) ∨
      c.ratio = ((currentGapDelta c.residue b) ^ (c.phase.val + 1))⁻¹ := by
  rcases currentCommonPrime_tau_orientation_law c.residue b with hdelta | hdelta
  · left
    rw [c.ratio_eq, c.tau_eq, hdelta]
  · right
    rw [c.ratio_eq, c.tau_eq, hdelta, inv_pow]

theorem currentCommonPrime_cyclotomic_degree_six_kernel_orientation
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    Ideal.comap SevenCyclotomicDegreeSixInt.ofReal
        c.address.currentKernel = RingHom.ker c.address.evalReal ∧
      Ideal.comap SevenCyclotomicDegreeSixInt.ofReal
        c.address.conjugate.currentKernel = RingHom.ker c.address.evalReal := by
  exact ⟨c.address.currentKernel_comap_ofReal,
    c.address.currentKernel_conjugate_comap_ofReal⟩

end CurrentPackets

end SevenRealCubic
end
end DkMath.FLT.Seven
