/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionRealPairCarrier

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionRealPairCoprimalityNormGate"

namespace DkMath.FLT.Seven

noncomputable section

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩
set_option maxRecDepth 4000
set_option linter.style.longLine false

namespace RamifiedSignedRootDepthPacket

open SevenRealCubicInt

/-- The product of the two signed roots is coprime to the depth-four
gap root.  This is a direct Bezout substitution; no prime factorization
or seven-primitivity is used. -/
theorem signedRootsProduct_isCoprime_gapRoot
    (p : RamifiedSignedRootDepthPacket) :
    IsCoprime
      (p.signedRightRoot * p.signedLeftRoot)
      p.gapRoot := by
  rcases p.signedRoots_isCoprime with ⟨u, v, huv⟩
  have hright :
      IsCoprime p.signedRightRoot p.gapRoot := by
    refine ⟨u + v, -(u * 7 ^ 4), ?_⟩
    linear_combination huv + u * p.signedGap_eq
  have hleft :
    IsCoprime p.signedLeftRoot p.gapRoot := by
    refine ⟨u + v, v * 7 ^ 4, ?_⟩
    linear_combination huv - v * p.signedGap_eq
  exact hright.mul_left hleft

/-- Cubic scalar abbreviating the signed-root product. -/
def pairScalar (p : RamifiedSignedRootDepthPacket) :
    SevenRealCubicInt :=
  ((p.signedRightRoot * p.signedLeftRoot : ℤ) :
    SevenRealCubicInt)

/-- Cubic scalar abbreviating the signed gap root. -/
def pairGapScalar (p : RamifiedSignedRootDepthPacket) :
    SevenRealCubicInt :=
  (p.gapRoot : SevenRealCubicInt)

/-- The common high-depth term in all three real-pair cores. -/
def pairHighTerm (p : RamifiedSignedRootDepthPacket) :
    SevenRealCubicInt :=
  eisensteinAxis ^ 23 * thetaSevenUnit ^ 8 *
    p.pairGapScalar ^ 2

theorem pairScalar_isCoprime_pairGapScalar
    (p : RamifiedSignedRootDepthPacket) :
    IsCoprime p.pairScalar p.pairGapScalar := by
  simpa [pairScalar, pairGapScalar] using
    p.signedRootsProduct_isCoprime_gapRoot.map
      (Int.castRingHom SevenRealCubicInt)

/-- The neutral modulo-seven residue of the signed-root product gives an
explicit Bezout identity between that scalar and theta. -/
theorem pairScalar_isCoprime_eisensteinAxis
    (p : RamifiedSignedRootDepthPacket) :
    IsCoprime p.pairScalar eisensteinAxis := by
  have hzero :
      (((p.signedRightRoot * p.signedLeftRoot - 1 : ℤ) : ZMod 7)) = 0 := by
    push_cast
    exact sub_eq_zero.mpr
      (by simpa only [Int.cast_mul] using
        p.signedRoots_product_modSeven_eq_one)
  have hdiv :
      (7 : ℤ) ∣
        p.signedRightRoot * p.signedLeftRoot - 1 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp hzero
  rcases hdiv with ⟨k, hk⟩
  have hkC := congrArg
    (fun z : ℤ => (z : SevenRealCubicInt)) hk
  push_cast at hkC
  refine
    ⟨1,
      -(eisensteinAxis ^ 2 * thetaSevenUnit *
        (k : SevenRealCubicInt)), ?_⟩
  simp only [one_mul, pairScalar, Int.cast_mul]
  rw [seven_eq_eisensteinAxis_cube_mul_unit] at hkC
  linear_combination hkC

theorem pairScalar_isCoprime_pairHighTerm
    (p : RamifiedSignedRootDepthPacket) :
    IsCoprime p.pairScalar p.pairHighTerm := by
  have htheta :
      IsCoprime p.pairScalar (eisensteinAxis ^ 23) :=
    p.pairScalar_isCoprime_eisensteinAxis.pow_right
  have hunit :
      IsCoprime p.pairScalar (thetaSevenUnit ^ 8) := by
    rcases isUnit_iff_exists_inv'.mp
        (thetaSevenUnit_isUnit.pow 8) with ⟨b, hb⟩
    exact ⟨0, b, by simpa using hb⟩
  have hgap :
      IsCoprime p.pairScalar (p.pairGapScalar ^ 2) :=
    p.pairScalar_isCoprime_pairGapScalar.pow_right
  exact (htheta.mul_right hunit).mul_right hgap

theorem realPairCore_eq_pairHighTerm_sub
    (p : RamifiedSignedRootDepthPacket) (i : Fin 3) :
    p.realPairCore i =
      p.pairHighTerm - pairAxisUnit i * p.pairScalar := by
  simp only [realPairCore, pairHighTerm, pairGapScalar, pairScalar,
    Int.cast_mul]

/-- The signed-root product is coprime to every normalized real-pair core. -/
theorem pairScalar_isCoprime_realPairCore
    (p : RamifiedSignedRootDepthPacket) (i : Fin 3) :
    IsCoprime p.pairScalar (p.realPairCore i) := by
  have h := p.pairScalar_isCoprime_pairHighTerm
  have h' :=
    h.add_mul_right_right (-pairAxisUnit i)
  rw [p.realPairCore_eq_pairHighTerm_sub]
  simpa [sub_eq_add_neg, mul_assoc] using h'

end RamifiedSignedRootDepthPacket

namespace SevenRealCubicInt

/-- Any two distinct pair-axis units have a unit difference. -/
theorem pairAxisUnit_sub_isUnit
    {i j : Fin 3} (hij : i ≠ j) :
    IsUnit (pairAxisUnit i - pairAxisUnit j) := by
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · change IsUnit (pairAxisUnit 0 - pairAxisUnit 1)
    rw [show pairAxisUnit 0 - pairAxisUnit 1 =
        -(pairAxisUnit 1 - pairAxisUnit 0) by ring]
    exact pairAxisUnit_one_sub_zero_isUnit.neg
  · change IsUnit (pairAxisUnit 0 - pairAxisUnit 2)
    rw [show pairAxisUnit 0 - pairAxisUnit 2 =
        -(pairAxisUnit 2 - pairAxisUnit 0) by ring]
    exact pairAxisUnit_two_sub_zero_isUnit.neg
  · exact pairAxisUnit_one_sub_zero_isUnit
  · exact (hij rfl).elim
  · change IsUnit (pairAxisUnit 1 - pairAxisUnit 2)
    rw [show pairAxisUnit 1 - pairAxisUnit 2 =
        -(pairAxisUnit 2 - pairAxisUnit 1) by ring]
    exact pairAxisUnit_two_sub_one_isUnit.neg
  · exact pairAxisUnit_two_sub_zero_isUnit
  · exact pairAxisUnit_two_sub_one_isUnit
  · exact (hij rfl).elim

theorem rotateEquiv_cyclicAlpha_zero :
    rotateEquiv (cyclicAlpha 0) = cyclicAlpha 1 := by
  rw [show cyclicAlpha 0 = alpha by rfl,
    show cyclicAlpha 1 = alpha ^ 2 - 2 * alpha by rfl]
  exact rotateEquiv_alpha

theorem rotateEquiv_cyclicAlpha_one :
    rotateEquiv (cyclicAlpha 1) = cyclicAlpha 2 := by
  rw [show cyclicAlpha 1 = rotateEquiv alpha by
      exact rotateEquiv_alpha.symm,
    show cyclicAlpha 2 = rotateEquiv (rotateEquiv alpha) by
      exact rotateEquiv_sq_alpha.symm]

theorem rotateEquiv_cyclicAlpha_two :
    rotateEquiv (cyclicAlpha 2) = cyclicAlpha 0 := by
  rw [show cyclicAlpha 2 = rotateEquiv (rotateEquiv alpha) by
      exact rotateEquiv_sq_alpha.symm,
    rotateEquiv_three]
  rfl

theorem rotateEquiv_eisensteinAxis_eq_axis_mul_pairAxisUnit_one :
    rotateEquiv eisensteinAxis =
      eisensteinAxis * pairAxisUnit 1 := by
  rw [pairAxisUnit_one]
  ext <;>
    norm_num [rotateEquiv, rotateHom, eisensteinAxis, alpha, mul, pow_two]

theorem rotateEquiv_sq_eisensteinAxis_eq_axis_mul_pairAxisUnit_two :
    rotateEquiv (rotateEquiv eisensteinAxis) =
      eisensteinAxis * pairAxisUnit 2 := by
  rw [pairAxisUnit_two]
  ext <;>
    norm_num [rotateEquiv, rotateHom, eisensteinAxis, alpha, mul, pow_two]

set_option maxHeartbeats 800000 in
-- The coordinate expansion of the cubic rotation norm is large.
theorem norm_rotateEquiv (x : SevenRealCubicInt) :
    norm (rotateEquiv x) = norm x := by
  rcases x with ⟨a, b, c⟩
  simp [rotateEquiv, rotateHom, norm]
  ring

theorem norm_pairAxisUnit_one :
    norm (pairAxisUnit 1) = 1 := by
  rw [pairAxisUnit_one]
  norm_num [norm, alpha]

theorem norm_pairAxisUnit_two :
    norm (pairAxisUnit 2) = 1 := by
  rw [pairAxisUnit_two]
  norm_num [norm, alpha, mul, pow_two]

theorem norm_eisensteinAxis :
    norm eisensteinAxis = -7 := by
  norm_num [norm, eisensteinAxis]

end SevenRealCubicInt

namespace RamifiedSignedRootDepthPacket

open SevenRealCubicInt

/-- The common high-depth term cancels from the difference of two cores. -/
theorem realPairCore_sub
    (p : RamifiedSignedRootDepthPacket) (i j : Fin 3) :
    p.realPairCore i - p.realPairCore j =
      -(pairAxisUnit i - pairAxisUnit j) * p.pairScalar := by
  rw [p.realPairCore_eq_pairHighTerm_sub,
    p.realPairCore_eq_pairHighTerm_sub]
  ring

/-- The three normalized real-pair cores are pairwise Bezout-coprime. -/
theorem realPairCores_pairwiseCoprime
    (p : RamifiedSignedRootDepthPacket) :
    Pairwise
      (fun i j : Fin 3 =>
        IsCoprime (p.realPairCore i) (p.realPairCore j)) := by
  intro i j hij
  have hunit :
      IsUnit (-(pairAxisUnit i - pairAxisUnit j)) :=
    (pairAxisUnit_sub_isUnit hij).neg
  have hmul :
      IsCoprime (p.realPairCore i)
        (-(pairAxisUnit i - pairAxisUnit j) * p.pairScalar) :=
    (isCoprime_mul_unit_left_right hunit
      (p.realPairCore i) p.pairScalar).mpr
        (p.pairScalar_isCoprime_realPairCore i).symm
  have hdiff :
      IsCoprime (p.realPairCore i)
        (p.realPairCore i - p.realPairCore j) := by
    rwa [p.realPairCore_sub]
  have hneg :
      IsCoprime (p.realPairCore i) (-p.realPairCore j) := by
    apply IsCoprime.of_add_mul_left_right (z := 1)
    simpa [sub_eq_add_neg, add_comm] using hdiff
  exact (IsCoprime.neg_right_iff _ _).mp hneg

/-- Rotation cycles the three real conjugate-pair carriers. -/
theorem rotate_realPairCarrier_zero
    (p : RamifiedSignedRootDepthPacket) :
    rotateEquiv (p.realPairCarrier 0) = p.realPairCarrier 1 := by
  simp only [realPairCarrier, map_sub, map_add, map_mul, map_pow,
    map_intCast, rotateEquiv_cyclicAlpha_zero]

theorem rotate_realPairCarrier_one
    (p : RamifiedSignedRootDepthPacket) :
    rotateEquiv (p.realPairCarrier 1) = p.realPairCarrier 2 := by
  simp only [realPairCarrier, map_sub, map_add, map_mul, map_pow,
    map_intCast, rotateEquiv_cyclicAlpha_one]

theorem rotate_realPairCarrier_two
    (p : RamifiedSignedRootDepthPacket) :
    rotateEquiv (p.realPairCarrier 2) = p.realPairCarrier 0 := by
  simp only [realPairCarrier, map_sub, map_add, map_mul, map_pow,
    map_intCast, rotateEquiv_cyclicAlpha_two]

private theorem eisensteinAxis_ne_zero :
    eisensteinAxis ≠ 0 := by
  intro h
  have hsnd := congrArg SevenRealCubicInt.snd h
  norm_num [eisensteinAxis] at hsnd

/-- The first nontrivial core is a unit-twisted Galois conjugate of
the zeroth core. -/
theorem realPairCore_one_eq_unit_mul_rotate
    (p : RamifiedSignedRootDepthPacket) :
    p.realPairCore 1 =
      pairAxisUnit 1 * rotateEquiv (p.realPairCore 0) := by
  apply mul_left_cancel₀ eisensteinAxis_ne_zero
  calc
    eisensteinAxis * p.realPairCore 1 =
        p.realPairCarrier 1 :=
      (p.realPairCarrier_eq_eisensteinAxis_mul_core 1).symm
    _ = rotateEquiv (p.realPairCarrier 0) :=
      p.rotate_realPairCarrier_zero.symm
    _ = rotateEquiv
        (eisensteinAxis * p.realPairCore 0) := by
      rw [p.realPairCarrier_eq_eisensteinAxis_mul_core 0]
    _ = eisensteinAxis *
        (pairAxisUnit 1 * rotateEquiv (p.realPairCore 0)) := by
      rw [map_mul,
        rotateEquiv_eisensteinAxis_eq_axis_mul_pairAxisUnit_one]
      ring

/-- The last core is the corresponding twist of the second Galois
conjugate of the zeroth core. -/
theorem realPairCore_two_eq_unit_mul_rotate_sq
    (p : RamifiedSignedRootDepthPacket) :
    p.realPairCore 2 =
      pairAxisUnit 2 *
        rotateEquiv (rotateEquiv (p.realPairCore 0)) := by
  apply mul_left_cancel₀ eisensteinAxis_ne_zero
  calc
    eisensteinAxis * p.realPairCore 2 =
        p.realPairCarrier 2 :=
      (p.realPairCarrier_eq_eisensteinAxis_mul_core 2).symm
    _ = rotateEquiv (rotateEquiv (p.realPairCarrier 0)) := by
      rw [p.rotate_realPairCarrier_zero,
        p.rotate_realPairCarrier_one]
    _ = rotateEquiv (rotateEquiv
        (eisensteinAxis * p.realPairCore 0)) := by
      rw [p.realPairCarrier_eq_eisensteinAxis_mul_core 0]
    _ = eisensteinAxis *
        (pairAxisUnit 2 *
          rotateEquiv (rotateEquiv (p.realPairCore 0))) := by
      rw [map_mul, map_mul,
        rotateEquiv_sq_eisensteinAxis_eq_axis_mul_pairAxisUnit_two]
      ring

/-- The zeroth carrier has norm equal to the signed seventh quotient. -/
theorem norm_realPairCarrier_zero
    (p : RamifiedSignedRootDepthPacket) :
    norm (p.realPairCarrier 0) =
      signedSeventhQuotient
        p.signedRightRoot p.signedLeftRoot := by
  have h :
      (norm (p.realPairCarrier 0) : SevenRealCubicInt) =
        (signedSeventhQuotient
          p.signedRightRoot p.signedLeftRoot :
          SevenRealCubicInt) := by
    calc
      (norm (p.realPairCarrier 0) : SevenRealCubicInt) =
          p.realPairCarrier 0 *
            rotateEquiv (p.realPairCarrier 0) *
            rotateEquiv (rotateEquiv (p.realPairCarrier 0)) :=
        (mul_rotateEquiv_mul_rotateEquiv_sq_eq_norm _).symm
      _ = p.realPairCarrier 0 *
            p.realPairCarrier 1 * p.realPairCarrier 2 := by
        rw [p.rotate_realPairCarrier_zero,
          p.rotate_realPairCarrier_one]
      _ = (signedSeventhQuotient
            p.signedRightRoot p.signedLeftRoot :
            SevenRealCubicInt) :=
        p.realPairCarrier_product_eq_signedSeventhQuotient
  have hfst := congrArg SevenRealCubicInt.fst h
  simpa using hfst

/-- The norm of every normalized pair core is exactly the negative
signed quotient root. -/
theorem norm_realPairCore
    (p : RamifiedSignedRootDepthPacket) (i : Fin 3) :
    norm (p.realPairCore i) = -p.quotientRoot := by
  have hzero :
      norm (p.realPairCore 0) = -p.quotientRoot := by
    have hcarrier := p.norm_realPairCarrier_zero
    rw [p.signedQuotient_eq] at hcarrier
    rw [p.realPairCarrier_eq_eisensteinAxis_mul_core 0,
      norm_mul, norm_eisensteinAxis] at hcarrier
    omega
  fin_cases i
  · exact hzero
  · change norm (p.realPairCore 1) = -p.quotientRoot
    rw [p.realPairCore_one_eq_unit_mul_rotate,
      norm_mul, norm_pairAxisUnit_one, norm_rotateEquiv, one_mul]
    exact hzero
  · change norm (p.realPairCore 2) = -p.quotientRoot
    rw [p.realPairCore_two_eq_unit_mul_rotate_sq,
      norm_mul, norm_pairAxisUnit_two, norm_rotateEquiv,
      norm_rotateEquiv, one_mul]
    exact hzero

/-- A unit-times-seventh-power description of any pair core forces the
integer quotient root to be a signed seventh power.  This is a guard,
not an extraction theorem. -/
theorem quotientRoot_signedSeventhPower_of_core_unit_mul_pow
    (p : RamifiedSignedRootDepthPacket) (i : Fin 3)
    (h :
      ∃ u : SevenRealCubicIntˣ,
        ∃ x : SevenRealCubicInt,
          p.realPairCore i = (u : SevenRealCubicInt) * x ^ 7) :
    ∃ z : ℤ,
      p.quotientRoot = z ^ 7 ∨
        p.quotientRoot = -(z ^ 7) := by
  rcases h with ⟨u, x, hcore⟩
  have hunorm :
      IsUnit (norm (u : SevenRealCubicInt)) := by
    have hmul :
        (u : SevenRealCubicInt) *
            (↑(u⁻¹) : SevenRealCubicInt) = 1 := by
      simp
    have hnorm :
        SevenRealCubicInt.norm (u : SevenRealCubicInt) *
            SevenRealCubicInt.norm
              (↑(u⁻¹) : SevenRealCubicInt) = 1 := by
      have hnorm_one : SevenRealCubicInt.norm (1 : SevenRealCubicInt) = 1 := by
        norm_num [SevenRealCubicInt.norm]
      simpa only [SevenRealCubicInt.norm_mul,
        SevenRealCubicInt.norm_intCast, one_pow, hnorm_one] using
          congrArg SevenRealCubicInt.norm hmul
    exact
      IsUnit.of_mul_eq_one
        (SevenRealCubicInt.norm
          (↑(u⁻¹) : SevenRealCubicInt)) hnorm
  have hgate := p.norm_realPairCore i
  rw [hcore, SevenRealCubicInt.norm_mul,
    SevenRealCubicInt.norm_pow] at hgate
  rcases Int.isUnit_eq_one_or hunorm with hu | hu
  · refine ⟨SevenRealCubicInt.norm x, Or.inr ?_⟩
    rw [hu, one_mul] at hgate
    omega
  · refine ⟨SevenRealCubicInt.norm x, Or.inl ?_⟩
    rw [hu] at hgate
    omega

/-- A signed seventh-power quotient makes the product of the three
pairwise-coprime cores associated to a seventh power. -/
theorem pairCore_product_associated_pow_seven_of_quotientRoot
    (p : RamifiedSignedRootDepthPacket)
    (h :
      ∃ z : ℤ,
        p.quotientRoot = z ^ 7 ∨
          p.quotientRoot = -(z ^ 7)) :
    ∃ z : SevenRealCubicInt,
      Associated (z ^ 7)
        (p.realPairCore 0 *
          (p.realPairCore 1 * p.realPairCore 2)) := by
  rcases h with ⟨z, hz | hz⟩
  · refine ⟨(z : SevenRealCubicInt), ?_⟩
    have hproduct :
        -(eisensteinAxis + 1) ^ 2 *
            (p.realPairCore 0 *
              (p.realPairCore 1 * p.realPairCore 2)) =
          (z : SevenRealCubicInt) ^ 7 := by
      calc
        _ = -(eisensteinAxis + 1) ^ 2 *
              p.realPairCore 0 * p.realPairCore 1 *
                p.realPairCore 2 := by ring
        _ = (p.quotientRoot : SevenRealCubicInt) :=
          p.pairCore_product_eq_quotientRoot
        _ = ((z ^ 7 : ℤ) : SevenRealCubicInt) := by rw [hz]
        _ = (z : SevenRealCubicInt) ^ 7 := by norm_cast
    have hunit :
        IsUnit (-(eisensteinAxis + 1) ^ 2) := by
      have hbase :
          IsUnit ((eisensteinAxis + 1) ^ 2) := by
        simpa [eisensteinAxisUnit] using
          (eisensteinAxisUnit_isUnit.pow 2)
      exact hbase.neg
    exact
      (Associated.of_eq hproduct.symm).trans
        (associated_unit_mul_left _ _ hunit)
  · refine ⟨((-z : ℤ) : SevenRealCubicInt), ?_⟩
    have hproduct :
        -(eisensteinAxis + 1) ^ 2 *
            (p.realPairCore 0 *
              (p.realPairCore 1 * p.realPairCore 2)) =
          ((-z : ℤ) : SevenRealCubicInt) ^ 7 := by
      calc
        _ = -(eisensteinAxis + 1) ^ 2 *
              p.realPairCore 0 * p.realPairCore 1 *
                p.realPairCore 2 := by ring
        _ = (p.quotientRoot : SevenRealCubicInt) :=
          p.pairCore_product_eq_quotientRoot
        _ = ((-(z ^ 7) : ℤ) : SevenRealCubicInt) := by rw [hz]
        _ = ((-z : ℤ) : SevenRealCubicInt) ^ 7 := by
          norm_cast
          ring_nf
    have hunit :
        IsUnit (-(eisensteinAxis + 1) ^ 2) := by
      have hbase :
          IsUnit ((eisensteinAxis + 1) ^ 2) := by
        simpa [eisensteinAxisUnit] using
          (eisensteinAxisUnit_isUnit.pow 2)
      exact hbase.neg
    exact
      (Associated.of_eq hproduct.symm).trans
        (associated_unit_mul_left _ _ hunit)

/-- PID extraction witnesses for all three pair cores, conditional only on
the exact signed seventh-power quotient gate. -/
structure RealPairCoreAssociatedPowerSplit
    (p : RamifiedSignedRootDepthPacket) where
  root0 : SevenRealCubicInt
  root1 : SevenRealCubicInt
  root2 : SevenRealCubicInt
  associated0 : Associated (root0 ^ 7) (p.realPairCore 0)
  associated1 : Associated (root1 ^ 7) (p.realPairCore 1)
  associated2 : Associated (root2 ^ 7) (p.realPairCore 2)

/-- Once the routing gate supplies a signed seventh-power quotient, the
pairwise-coprime product admits the three legitimate PID extractions. -/
theorem nonempty_realPairCoreAssociatedPowerSplit
    (p : RamifiedSignedRootDepthPacket)
    (h :
      ∃ z : ℤ,
        p.quotientRoot = z ^ 7 ∨
          p.quotientRoot = -(z ^ 7)) :
    Nonempty (RealPairCoreAssociatedPowerSplit p) := by
  rcases p.pairCore_product_associated_pow_seven_of_quotientRoot h with
    ⟨z, hproduct⟩
  have h01 :
      IsCoprime (p.realPairCore 0) (p.realPairCore 1) :=
    p.realPairCores_pairwiseCoprime (by decide)
  have h02 :
      IsCoprime (p.realPairCore 0) (p.realPairCore 2) :=
    p.realPairCores_pairwiseCoprime (by decide)
  have h12 :
      IsCoprime (p.realPairCore 1) (p.realPairCore 2) :=
    p.realPairCores_pairwiseCoprime (by decide)
  rcases exists_associated_pow_of_associated_pow_mul
      (h01.mul_right h02) hproduct with
    ⟨root0, hroot0⟩
  have hproduct1 :
      Associated (z ^ 7)
        (p.realPairCore 1 *
          (p.realPairCore 0 * p.realPairCore 2)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hproduct
  rcases exists_associated_pow_of_associated_pow_mul
      (h01.symm.mul_right h12) hproduct1 with
    ⟨root1, hroot1⟩
  have hproduct2 :
      Associated (z ^ 7)
        (p.realPairCore 2 *
          (p.realPairCore 0 * p.realPairCore 1)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hproduct
  rcases exists_associated_pow_of_associated_pow_mul
      (h02.symm.mul_right h12.symm) hproduct2 with
    ⟨root2, hroot2⟩
  exact ⟨⟨root0, root1, root2, hroot0, hroot1, hroot2⟩⟩

end RamifiedSignedRootDepthPacket

namespace RamifiedSignedRootRoutingPacket

/-- The first unresolved row-two cell is the canonical gcd address of the
quotient root and the left cubic column margin. -/
theorem c21_eq_quotientRoot_innerFst_gcd
    (p : RamifiedSignedRootRoutingPacket) :
    p.routing.c21 =
      Nat.gcd (Int.natAbs p.signedDepth.quotientRoot)
        (Int.natAbs
          p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket.quadratic.innerRoot.fst) := by
  let q :=
    p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket
  have hAN : IsCoprime q.quadratic.innerRoot.fst
      (q.quadratic.innerRoot.fst + q.quadratic.innerRoot.snd) := by
    simpa [add_comm] using
      q.quadratic.innerRoot_coordinates_isCoprime.add_mul_right_right 1
  have hAM7 : IsCoprime q.quadratic.innerRoot.fst
      (q.innerSndRoot ^ 7) := by
    have h := q.quadratic.innerRoot_coordinates_isCoprime
    rw [q.innerSnd_eq] at h
    exact h.of_mul_right_right
  apply p.routing.c21_eq_gcd
  · simpa [q] using
      (Int.isCoprime_iff_nat_coprime.mp hAN)
  · simpa [q, Int.natAbs_pow] using
      (Int.isCoprime_iff_nat_coprime.mp hAM7)

/-- The second unresolved row-two cell is the canonical gcd address of the
quotient root and the right cubic column margin. -/
theorem c22_eq_quotientRoot_innerFst_add_innerSnd_gcd
    (p : RamifiedSignedRootRoutingPacket) :
    p.routing.c22 =
      Nat.gcd (Int.natAbs p.signedDepth.quotientRoot)
        (Int.natAbs
          (p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket.quadratic.innerRoot.fst +
            p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket.quadratic.innerRoot.snd)) := by
  let q :=
    p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket
  have hAN : IsCoprime q.quadratic.innerRoot.fst
      (q.quadratic.innerRoot.fst + q.quadratic.innerRoot.snd) := by
    simpa [add_comm] using
      q.quadratic.innerRoot_coordinates_isCoprime.add_mul_right_right 1
  have hANM7 : IsCoprime
      (q.quadratic.innerRoot.fst + q.quadratic.innerRoot.snd)
      (q.innerSndRoot ^ 7) := by
    rw [q.innerSnd_eq]
    have h := q.rightSource_coordinates_isCoprime
    rw [q.innerSnd_eq] at h
    exact h.of_mul_right_right
  apply p.routing.c22_eq_gcd
  · simpa [q] using
      (Int.isCoprime_iff_nat_coprime.mp hAN)
  · simpa [q, Int.natAbs_pow] using
      (Int.isCoprime_iff_nat_coprime.mp hANM7)

/-- Explicit seventh roots for all three cells in the pure seventh-power
column of the coherent signed routing board. -/
structure Col3SeventhPowerSplit
    (p : RamifiedSignedRootRoutingPacket) where
  root13 : ℕ
  root23 : ℕ
  root33 : ℕ
  c13_eq : p.routing.c13 = root13 ^ 7
  c23_eq : p.routing.c23 = root23 ^ 7
  c33_eq : p.routing.c33 = root33 ^ 7

/-- Pairwise coprimality in column three splits its exact seventh-power
margin cell by cell. -/
theorem nonempty_col3SeventhPowerSplit
    (p : RamifiedSignedRootRoutingPacket) :
    Nonempty (Col3SeventhPowerSplit p) := by
  have hthird := p.thirdRow_eq_one
  have hcol :
      p.routing.c13 * p.routing.c23 =
        Int.natAbs
          p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket.innerSndRoot ^
            7 := by
    have h := p.routing.col3
    rw [hthird.2.2, mul_one] at h
    simpa [Int.natAbs_pow] using h.symm
  rcases seventh_power_factor_split
      p.routing.col3_coprime.1 hcol with
    ⟨⟨root13, h13⟩, ⟨root23, h23⟩⟩
  exact ⟨⟨root13, root23, 1, h13, h23, by simp [hthird.2.2]⟩⟩

/-- After the pure seventh-power column has been split, the absolute
quotient-root row consists of exactly the two unresolved scalar cells
times one seventh power. -/
theorem exists_row2_twoCellSeventhPowerFactor
    (p : RamifiedSignedRootRoutingPacket) :
    ∃ t : ℕ,
      Int.natAbs p.signedDepth.quotientRoot =
        p.routing.c21 * p.routing.c22 * t ^ 7 := by
  rcases p.nonempty_col3SeventhPowerSplit with ⟨split⟩
  refine ⟨split.root23, ?_⟩
  calc
    Int.natAbs p.signedDepth.quotientRoot =
        p.routing.c21 * p.routing.c22 * p.routing.c23 :=
      p.routing.row2
    _ = p.routing.c21 * p.routing.c22 * split.root23 ^ 7 := by
      rw [split.c23_eq]

/-- A signed integer is a signed seventh power as soon as its absolute
value is a natural seventh power. -/
private theorem signedSeventhPower_of_natAbs_eq_pow
    {q : ℤ} {t : ℕ} (h : Int.natAbs q = t ^ 7) :
    ∃ z : ℤ, q = z ^ 7 ∨ q = -(z ^ 7) := by
  have hcast :
      (Int.natAbs q : ℤ) = (t : ℤ) ^ 7 := by
    exact_mod_cast h
  rcases Int.natAbs_eq q with hq | hq
  · exact ⟨t, Or.inl (hq.trans hcast)⟩
  · refine ⟨t, Or.inr ?_⟩
    omega

/-- If the two unresolved row-two cells are seventh powers, then the
quotient root is a signed seventh power. -/
theorem quotientRoot_signedSeventhPower_of_row2_cells
    (p : RamifiedSignedRootRoutingPacket)
    (h21 : ∃ a : ℕ, p.routing.c21 = a ^ 7)
    (h22 : ∃ b : ℕ, p.routing.c22 = b ^ 7) :
    ∃ z : ℤ,
      p.signedDepth.quotientRoot = z ^ 7 ∨
        p.signedDepth.quotientRoot = -(z ^ 7) := by
  rcases h21 with ⟨a, ha⟩
  rcases h22 with ⟨b, hb⟩
  rcases p.exists_row2_twoCellSeventhPowerFactor with ⟨t, ht⟩
  apply signedSeventhPower_of_natAbs_eq_pow (t := a * b * t)
  calc
    Int.natAbs p.signedDepth.quotientRoot =
        p.routing.c21 * p.routing.c22 * t ^ 7 := ht
    _ = (a * b * t) ^ 7 := by rw [ha, hb]; ring

/-- Conversely, a signed seventh-power quotient root forces both
unresolved row-two cells to split as natural seventh powers. -/
theorem row2_cells_seventhPowers_of_quotientRoot_signedSeventhPower
    (p : RamifiedSignedRootRoutingPacket)
    (h :
      ∃ z : ℤ,
        p.signedDepth.quotientRoot = z ^ 7 ∨
          p.signedDepth.quotientRoot = -(z ^ 7)) :
    (∃ a : ℕ, p.routing.c21 = a ^ 7) ∧
      (∃ b : ℕ, p.routing.c22 = b ^ 7) := by
  rcases h with ⟨z, hz | hz⟩
  · have hrow :
        p.routing.c21 *
            (p.routing.c22 * p.routing.c23) =
          Int.natAbs z ^ 7 := by
      calc
        p.routing.c21 * (p.routing.c22 * p.routing.c23) =
            p.routing.c21 * p.routing.c22 * p.routing.c23 := by ring
        _ = Int.natAbs p.signedDepth.quotientRoot :=
          p.routing.row2.symm
        _ = Int.natAbs z ^ 7 := by rw [hz, Int.natAbs_pow]
    have hcop :
        Nat.Coprime p.routing.c21
          (p.routing.c22 * p.routing.c23) :=
      p.routing.row2_coprime.1.mul_right
        p.routing.row2_coprime.2.1
    rcases seventh_power_factor_split hcop hrow with
      ⟨h21, ⟨bc, hbc⟩⟩
    have h22 :=
      (seventh_power_factor_split
        p.routing.row2_coprime.2.2 hbc).1
    exact ⟨h21, h22⟩
  · have hrow :
        p.routing.c21 *
            (p.routing.c22 * p.routing.c23) =
          Int.natAbs z ^ 7 := by
      calc
        p.routing.c21 * (p.routing.c22 * p.routing.c23) =
            p.routing.c21 * p.routing.c22 * p.routing.c23 := by ring
        _ = Int.natAbs p.signedDepth.quotientRoot :=
          p.routing.row2.symm
        _ = Int.natAbs z ^ 7 := by
          rw [hz, Int.natAbs_neg, Int.natAbs_pow]
    have hcop :
        Nat.Coprime p.routing.c21
          (p.routing.c22 * p.routing.c23) :=
      p.routing.row2_coprime.1.mul_right
        p.routing.row2_coprime.2.1
    rcases seventh_power_factor_split hcop hrow with
      ⟨h21, ⟨bc, hbc⟩⟩
    have h22 :=
      (seventh_power_factor_split
        p.routing.row2_coprime.2.2 hbc).1
    exact ⟨h21, h22⟩

/-- Exact routing gate: after column three is discharged, signed
seventh-power extraction for the quotient root is equivalent to the two
remaining row-two cells being seventh powers. -/
theorem quotientRoot_signedSeventhPower_iff_row2_cells
    (p : RamifiedSignedRootRoutingPacket) :
    (∃ z : ℤ,
        p.signedDepth.quotientRoot = z ^ 7 ∨
          p.signedDepth.quotientRoot = -(z ^ 7)) ↔
      (∃ a : ℕ, p.routing.c21 = a ^ 7) ∧
        (∃ b : ℕ, p.routing.c22 = b ^ 7) := by
  constructor
  · exact p.row2_cells_seventhPowers_of_quotientRoot_signedSeventhPower
  · rintro ⟨h21, h22⟩
    exact p.quotientRoot_signedSeventhPower_of_row2_cells h21 h22

/-- Complete conditional Branch A: seventh-power witnesses for the two
unresolved routing cells produce legitimate PID seventh-power
extractions for all three real-pair cores. -/
theorem nonempty_realPairCoreAssociatedPowerSplit_of_row2_cells
    (p : RamifiedSignedRootRoutingPacket)
    (h21 : ∃ a : ℕ, p.routing.c21 = a ^ 7)
    (h22 : ∃ b : ℕ, p.routing.c22 = b ^ 7) :
    Nonempty
      (RamifiedSignedRootDepthPacket.RealPairCoreAssociatedPowerSplit
        p.signedDepth) := by
  exact
    p.signedDepth.nonempty_realPairCoreAssociatedPowerSplit
      (p.quotientRoot_signedSeventhPower_of_row2_cells h21 h22)

/-- The particularly strong terminal outcome `c21 = c22 = 1` is enough
to discharge the exact routing gate and open all three PID extractions. -/
theorem nonempty_realPairCoreAssociatedPowerSplit_of_row2_cells_eq_one
    (p : RamifiedSignedRootRoutingPacket)
    (h21 : p.routing.c21 = 1)
    (h22 : p.routing.c22 = 1) :
    Nonempty
      (RamifiedSignedRootDepthPacket.RealPairCoreAssociatedPowerSplit
        p.signedDepth) := by
  apply p.nonempty_realPairCoreAssociatedPowerSplit_of_row2_cells
  · exact ⟨1, by simpa using h21⟩
  · exact ⟨1, by simpa using h22⟩

end RamifiedSignedRootRoutingPacket

#print axioms
  RamifiedSignedRootDepthPacket.realPairCores_pairwiseCoprime
#print axioms RamifiedSignedRootDepthPacket.norm_realPairCore
#print axioms
  RamifiedSignedRootDepthPacket.nonempty_realPairCoreAssociatedPowerSplit
#print axioms
  RamifiedSignedRootRoutingPacket.nonempty_col3SeventhPowerSplit
#print axioms
  RamifiedSignedRootRoutingPacket.quotientRoot_signedSeventhPower_iff_row2_cells

end

end DkMath.FLT.Seven
