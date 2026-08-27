/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.PrimePowerCellAudit

#print "file: DkMath.FLT.Seven.PrimePowerUnitOrbit"

namespace DkMath.FLT.Seven

/-- The inverse 3/7 parametrization, formulated without putting an inverse
operation on an arbitrary commutative ring. -/
structure ThreeSevenUnitParametrization {R : Type*} [CommRing R]
    (C v w : R) : Type _ where
  scale : R
  scale_isUnit : IsUnit scale
  v_eq : v = C ^ 2 * scale ^ 3
  w_eq : w = C ^ 5 * scale ^ 7

set_option linter.flexible false in
/-- Commutative rearrangement is intentionally handled by `simp` after the
unit equation has cancelled the two independent unit generators. -/
theorem unit_three_seven_parametrization {R : Type*} [CommRing R]
    {C v w : R} (hC : IsUnit C) (hv : IsUnit v) (hw : IsUnit w)
    (h : w ^ 3 = C * v ^ 7) :
    Nonempty (ThreeSevenUnitParametrization C v w) := by
  rcases hC with ⟨C, rfl⟩
  rcases hv with ⟨v, rfl⟩
  rcases hw with ⟨w, rfl⟩
  have hu : w ^ 3 = C * v ^ 7 := Units.ext h
  let s : Rˣ := v ^ 5 * (w⁻¹) ^ 2
  have hv53 : (v ^ 5) ^ 3 = v ^ 15 := by group
  have hw23 : ((w⁻¹) ^ 2) ^ 3 = (w ^ 3)⁻¹ ^ 2 := by group
  have hv57 : (v ^ 5) ^ 7 = v ^ 35 := by group
  have hw27 : ((w⁻¹) ^ 2) ^ 7 = (w ^ 3)⁻¹ ^ 5 * w := by group
  have hv' : v = C ^ 2 * s ^ 3 := by
    symm
    calc
      C ^ 2 * s ^ 3 = C ^ 2 * v ^ 15 * (w ^ 3)⁻¹ ^ 2 := by
        simp only [s, mul_pow, hv53, hw23, mul_assoc]
      _ = C ^ 2 * v ^ 15 * (C * v ^ 7)⁻¹ ^ 2 := by rw [hu]
      _ = v := by
        rw [mul_inv_rev, mul_pow]
        simp [mul_assoc, mul_comm, mul_left_comm]
        rw [← pow_mul]
        norm_num
        group
  have hw' : w = C ^ 5 * s ^ 7 := by
    symm
    calc
      C ^ 5 * s ^ 7 = C ^ 5 * v ^ 35 * (w ^ 3)⁻¹ ^ 5 * w := by
        simp only [s, mul_pow, hv57, hw27, mul_assoc]
      _ = C ^ 5 * v ^ 35 * (C * v ^ 7)⁻¹ ^ 5 * w := by rw [hu]
      _ = w := by
        rw [mul_inv_rev, mul_pow]
        simp only [inv_pow, mul_eq_right]
        rw [← pow_mul]
        norm_num
  exact ⟨{
    scale := (s : R)
    scale_isUnit := s.isUnit
    v_eq := congrArg Units.val hv'
    w_eq := congrArg Units.val hw' }⟩

/-- Weighted unit action: root coordinates have weight 3 and endpoint
coordinates have weight 7. -/
def scalePrimePowerSolution {M : ℕ} {row : EndpointRoutingRow}
    {column : RootRoutingColumn} (a : AwayRoutingPrimePowerSolution M row column)
    (s : ZMod M) (hs : IsUnit s) : AwayRoutingPrimePowerSolution M row column := by
  refine {
    u := a.u * s ^ 3
    v := a.v * s ^ 3
    y := a.y * s ^ 7
    z := a.z * s ^ 7
    endpoint_nondegenerate := ?_
    endpoint_equation := ?_
    root_nondegenerate := ?_
    root_equation := ?_
    first_coordinate_equation := ?_ }
  · cases row <;> simp only [AwayEndpointPrimePowerNondegenerate] at a ⊢
    · exact a.endpoint_nondegenerate.mul (hs.pow 7)
    · exact a.endpoint_nondegenerate.mul (hs.pow 7)
    · exact ⟨a.endpoint_nondegenerate.1.mul (hs.pow 7),
        a.endpoint_nondegenerate.2.mul (hs.pow 7)⟩
  · cases row <;>
      simp only [AwayEndpointPrimePowerEquation, AwayEndpointLocalEquation] at a ⊢
    · rw [a.endpoint_equation, zero_mul]
    · rw [a.endpoint_equation, zero_mul]
    · rw [← add_mul, a.endpoint_equation, zero_mul]
  · cases column <;> simp only [AwayRootPrimePowerNondegenerate] at a ⊢
    · exact a.root_nondegenerate.mul (hs.pow 3)
    · exact a.root_nondegenerate.mul (hs.pow 3)
    · exact a.root_nondegenerate.mul (hs.pow 3)
  · cases column <;>
      simp only [AwayRootPrimePowerEquation, AwayRootLocalEquation] at a ⊢
    · rw [a.root_equation, zero_mul]
    · rw [show leftCubicZMod (a.u * s ^ 3) (a.v * s ^ 3) =
          s ^ 9 * leftCubicZMod a.u a.v by
          simp [leftCubicZMod]; ring, a.root_equation, mul_zero]
    · rw [show rightCubicZMod (a.u * s ^ 3) (a.v * s ^ 3) =
          s ^ 9 * rightCubicZMod a.u a.v by
          simp [rightCubicZMod]; ring, a.root_equation, mul_zero]
  · cases row <;> cases column <;>
      have ha := a.first_coordinate_equation <;>
      simp only [AwayFirstCoordinatePrimePowerEquation,
        AwayFirstCoordinateLocalEquation, leftCorrectionZMod,
        rightCorrectionZMod] at ha ⊢ <;>
      calc
        _ = s ^ 21 * 0 := by rw [← ha]; ring
        _ = 0 := mul_zero _

@[simp] theorem scalePrimePowerSolution_one {M : ℕ} {row : EndpointRoutingRow}
    {column : RootRoutingColumn} (a : AwayRoutingPrimePowerSolution M row column) :
    scalePrimePowerSolution a 1 isUnit_one = a := by
  cases a
  simp [scalePrimePowerSolution]

def canonicalPrimePowerSolution_sevenV (M : ℕ) (row : EndpointRoutingRow) :
    AwayRoutingPrimePowerSolution M row .sevenV := by
  cases row with
  | y => exact ⟨1, 0, 0, 1, isUnit_one, rfl, isUnit_one, rfl, by
      norm_num [AwayFirstCoordinatePrimePowerEquation, AwayFirstCoordinateLocalEquation]⟩
  | z => exact ⟨-1, 0, 1, 0, isUnit_one, rfl, isUnit_one.neg, rfl, by
      simp [AwayFirstCoordinatePrimePowerEquation, AwayFirstCoordinateLocalEquation]; ring⟩
  | sum => exact ⟨-1, 0, 1, -1, ⟨isUnit_one, isUnit_one.neg⟩, by
      simp [AwayEndpointPrimePowerEquation, AwayEndpointLocalEquation],
      isUnit_one.neg, rfl, by
      simp [AwayFirstCoordinatePrimePowerEquation, AwayFirstCoordinateLocalEquation]; ring⟩

def leftOrbitCoefficient {q e : ℕ} (t : ZMod (q ^ e)) :
    EndpointRoutingRow → ZMod (q ^ e)
  | .y => -49 * leftCorrectionNormalizedZMod t
  | .z | .sum => 49 * leftCorrectionNormalizedZMod t

def rightOrbitCoefficient {q e : ℕ} (t : ZMod (q ^ e)) :
    EndpointRoutingRow → ZMod (q ^ e)
  | .y => 49 * rightCorrectionNormalizedZMod t
  | .z | .sum => -49 * rightCorrectionNormalizedZMod t

def canonicalPrimePowerSolution_leftCubic {q e : ℕ} (hq : Nat.Prime q)
    (hq7 : q ≠ 7) (he : 0 < e) (t : ZMod (q ^ e))
    (ht : leftCubicNormalizedZMod t = 0) (row : EndpointRoutingRow) :
    AwayRoutingPrimePowerSolution (q ^ e) row .leftCubic := by
  let L := leftCorrectionNormalizedZMod t
  have hL := leftCorrection_isUnit_of_leftCubic_eq_zero_primePower hq hq7 he t ht
  have h49 := fortyNine_isUnit_zmod_primePower hq hq7 he
  cases row with
  | y =>
      let C : ZMod (q ^ e) := -49 * L
      have hC : IsUnit C := h49.neg.mul hL
      exact ⟨t*C^2, C^2, 0, C^5, hC.pow 5, rfl, hC.pow 2,
        left_scaled_root_pp t C ht, by
          simp only [AwayFirstCoordinatePrimePowerEquation,
            AwayFirstCoordinateLocalEquation]
          rw [left_scaled_correction_pp]; dsimp [C, L]; ring⟩
  | z =>
      let C : ZMod (q ^ e) := 49 * L
      have hC : IsUnit C := h49.mul hL
      exact ⟨t*C^2, C^2, C^5, 0, hC.pow 5, rfl, hC.pow 2,
        left_scaled_root_pp t C ht, by
          simp only [AwayFirstCoordinatePrimePowerEquation,
            AwayFirstCoordinateLocalEquation]
          rw [left_scaled_correction_pp]; dsimp [C, L]; ring⟩
  | sum =>
      let C : ZMod (q ^ e) := 49 * L
      have hC : IsUnit C := h49.mul hL
      exact ⟨t*C^2, C^2, C^5, -(C^5), ⟨hC.pow 5, (hC.pow 5).neg⟩,
        by simp [AwayEndpointPrimePowerEquation, AwayEndpointLocalEquation], hC.pow 2,
        left_scaled_root_pp t C ht, by
          simp only [AwayFirstCoordinatePrimePowerEquation,
            AwayFirstCoordinateLocalEquation]
          rw [left_scaled_correction_pp]; dsimp [C, L]; ring⟩

def canonicalPrimePowerSolution_rightCubic {q e : ℕ} (hq : Nat.Prime q)
    (hq7 : q ≠ 7) (he : 0 < e) (t : ZMod (q ^ e))
    (ht : rightCubicNormalizedZMod t = 0) (row : EndpointRoutingRow) :
    AwayRoutingPrimePowerSolution (q ^ e) row .rightCubic := by
  let R := rightCorrectionNormalizedZMod t
  have hR := rightCorrection_isUnit_of_rightCubic_eq_zero_primePower hq hq7 he t ht
  have h49 := fortyNine_isUnit_zmod_primePower hq hq7 he
  cases row with
  | y =>
      let C : ZMod (q ^ e) := 49 * R
      have hC : IsUnit C := h49.mul hR
      exact ⟨t*C^2, C^2, 0, C^5, hC.pow 5, rfl, hC.pow 2,
        right_scaled_root_pp t C ht, by
          simp only [AwayFirstCoordinatePrimePowerEquation,
            AwayFirstCoordinateLocalEquation]
          rw [right_scaled_correction_pp]; dsimp [C, R]; ring⟩
  | z =>
      let C : ZMod (q ^ e) := -49 * R
      have hC : IsUnit C := h49.neg.mul hR
      exact ⟨t*C^2, C^2, C^5, 0, hC.pow 5, rfl, hC.pow 2,
        right_scaled_root_pp t C ht, by
          simp only [AwayFirstCoordinatePrimePowerEquation,
            AwayFirstCoordinateLocalEquation]
          rw [right_scaled_correction_pp]; dsimp [C, R]; ring⟩
  | sum =>
      let C : ZMod (q ^ e) := -49 * R
      have hC : IsUnit C := h49.neg.mul hR
      exact ⟨t*C^2, C^2, C^5, -(C^5), ⟨hC.pow 5, (hC.pow 5).neg⟩,
        by simp [AwayEndpointPrimePowerEquation, AwayEndpointLocalEquation], hC.pow 2,
        right_scaled_root_pp t C ht, by
          simp only [AwayFirstCoordinatePrimePowerEquation,
            AwayFirstCoordinateLocalEquation]
          rw [right_scaled_correction_pp]; dsimp [C, R]; ring⟩

structure PrimePowerOrbitWitness {M : ℕ} {row : EndpointRoutingRow}
    {column : RootRoutingColumn} (actual model :
      AwayRoutingPrimePowerSolution M row column) : Type where
  scale : ZMod M
  scale_isUnit : IsUnit scale
  actual_eq : actual = scalePrimePowerSolution model scale scale_isUnit

theorem sevenV_primePower_orbit_complete {M : ℕ} {row : EndpointRoutingRow}
    (a : AwayRoutingPrimePowerSolution M row .sevenV) :
    Nonempty (PrimePowerOrbitWitness a (canonicalPrimePowerSolution_sevenV M row)) := by
  cases row with
  | y =>
      have hay : a.y = 0 := a.endpoint_equation
      have hav : a.v = 0 := a.root_equation
      have h : a.z ^ 3 = (1 : ZMod M) * a.u ^ 7 := by
        simpa [AwayFirstCoordinatePrimePowerEquation,
          AwayFirstCoordinateLocalEquation] using
          (sub_eq_zero.mp a.first_coordinate_equation).symm
      rcases unit_three_seven_parametrization isUnit_one a.root_nondegenerate
        a.endpoint_nondegenerate h with ⟨p⟩
      exact ⟨{
        scale := p.scale
        scale_isUnit := p.scale_isUnit
        actual_eq := by
          apply AwayRoutingPrimePowerSolution.ext
          · simpa [canonicalPrimePowerSolution_sevenV,
              scalePrimePowerSolution] using p.v_eq
          · simpa [canonicalPrimePowerSolution_sevenV,
              scalePrimePowerSolution] using hav
          · simpa [canonicalPrimePowerSolution_sevenV,
              scalePrimePowerSolution] using hay
          · simpa [canonicalPrimePowerSolution_sevenV,
              scalePrimePowerSolution] using p.w_eq }⟩
  | z =>
      have haz : a.z = 0 := a.endpoint_equation
      have hav : a.v = 0 := a.root_equation
      have h : a.y ^ 3 = (1 : ZMod M) * (-a.u) ^ 7 := by
        have ha : a.u ^ 7 + a.y ^ 3 = 0 := a.first_coordinate_equation
        calc
          a.y ^ 3 = -(a.u ^ 7) := by linear_combination ha
          _ = (-a.u) ^ 7 := by ring
          _ = 1 * (-a.u) ^ 7 := by ring
      rcases unit_three_seven_parametrization isUnit_one a.root_nondegenerate.neg
        a.endpoint_nondegenerate h with ⟨p⟩
      exact ⟨{
        scale := p.scale
        scale_isUnit := p.scale_isUnit
        actual_eq := by
          apply AwayRoutingPrimePowerSolution.ext
          · change a.u = (-1) * p.scale ^ 3
            calc
              a.u = -(-a.u) := by ring
              _ = -(p.scale ^ 3) := congrArg Neg.neg (by simpa using p.v_eq)
              _ = (-1) * p.scale ^ 3 := by ring
          · simpa [canonicalPrimePowerSolution_sevenV,
              scalePrimePowerSolution] using hav
          · simpa [canonicalPrimePowerSolution_sevenV,
              scalePrimePowerSolution] using p.w_eq
          · simpa [canonicalPrimePowerSolution_sevenV,
              scalePrimePowerSolution] using haz }⟩
  | sum =>
      have hend : a.y + a.z = 0 := a.endpoint_equation
      have hav : a.v = 0 := a.root_equation
      have h : a.y ^ 3 = (1 : ZMod M) * (-a.u) ^ 7 := by
        have ha : a.u ^ 7 + a.y ^ 3 = 0 := a.first_coordinate_equation
        calc
          a.y ^ 3 = -(a.u ^ 7) := by linear_combination ha
          _ = (-a.u) ^ 7 := by ring
          _ = 1 * (-a.u) ^ 7 := by ring
      rcases unit_three_seven_parametrization isUnit_one a.root_nondegenerate.neg
        a.endpoint_nondegenerate.1 h with ⟨p⟩
      exact ⟨{
        scale := p.scale
        scale_isUnit := p.scale_isUnit
        actual_eq := by
          apply AwayRoutingPrimePowerSolution.ext
          · change a.u = (-1) * p.scale ^ 3
            calc
              a.u = -(-a.u) := by ring
              _ = -(p.scale ^ 3) := congrArg Neg.neg (by simpa using p.v_eq)
              _ = (-1) * p.scale ^ 3 := by ring
          · simpa [canonicalPrimePowerSolution_sevenV,
              scalePrimePowerSolution] using hav
          · simpa [canonicalPrimePowerSolution_sevenV,
              scalePrimePowerSolution] using p.w_eq
          · change a.z = (-1) * p.scale ^ 7
            have hp : a.y = p.scale ^ 7 := by simpa using p.w_eq
            calc
              a.z = -a.y := (eq_neg_iff_add_eq_zero).2 (by
                simpa [add_comm] using hend)
              _ = -(p.scale ^ 7) := congrArg Neg.neg hp
              _ = (-1) * p.scale ^ 7 := by ring }⟩

theorem leftCubic_primePower_orbit_complete {q e : ℕ} (hq : Nat.Prime q)
    (hq7 : q ≠ 7) (he : 0 < e) {row : EndpointRoutingRow}
    (a : AwayRoutingPrimePowerSolution (q ^ e) row .leftCubic) :
    let t := a.u * a.v⁻¹
    let ht := left_normalized_root_of_primePowerSolution a
    Nonempty (PrimePowerOrbitWitness a
      (canonicalPrimePowerSolution_leftCubic hq hq7 he t ht row)) := by
  let t := a.u * a.v⁻¹
  have ht : leftCubicNormalizedZMod t = 0 :=
    left_normalized_root_of_primePowerSolution a
  have huv : t * a.v = a.u := by
    dsimp [t]
    calc
      (a.u * a.v⁻¹) * a.v = a.u * (a.v * a.v⁻¹) := by ring
      _ = a.u := by rw [a.v.mul_inv_of_unit a.root_nondegenerate, mul_one]
  have hcorr : leftCorrectionZMod a.u a.v =
      a.v ^ 2 * leftCorrectionNormalizedZMod t := by
    rw [← huv]
    simp [leftCorrectionZMod, leftCorrectionNormalizedZMod]
    ring
  have hL := leftCorrection_isUnit_of_leftCubic_eq_zero_primePower hq hq7 he t ht
  have h49 := fortyNine_isUnit_zmod_primePower hq hq7 he
  cases row with
  | y =>
      let C := (-49 : ZMod (q ^ e)) * leftCorrectionNormalizedZMod t
      have hC : IsUnit C := h49.neg.mul hL
      have hay : a.y = 0 := a.endpoint_equation
      have hpow : a.z ^ 3 = C * a.v ^ 7 := by
        have ha := a.first_coordinate_equation
        simp only [AwayFirstCoordinatePrimePowerEquation,
          AwayFirstCoordinateLocalEquation] at ha
        rw [hcorr] at ha
        dsimp [C]
        linear_combination ha
      rcases unit_three_seven_parametrization hC a.root_nondegenerate
        a.endpoint_nondegenerate hpow with ⟨p⟩
      exact ⟨{
        scale := p.scale
        scale_isUnit := p.scale_isUnit
        actual_eq := by
          apply AwayRoutingPrimePowerSolution.ext
          · change a.u = (t * C ^ 2) * p.scale ^ 3
            calc a.u = t * a.v := huv.symm
              _ = t * (C ^ 2 * p.scale ^ 3) := congrArg (t * ·) p.v_eq
              _ = (t * C ^ 2) * p.scale ^ 3 := by ring
          · change a.v = C ^ 2 * p.scale ^ 3
            exact p.v_eq
          · simpa [canonicalPrimePowerSolution_leftCubic,
              scalePrimePowerSolution] using hay
          · change a.z = C ^ 5 * p.scale ^ 7
            exact p.w_eq }⟩
  | z =>
      let C := (49 : ZMod (q ^ e)) * leftCorrectionNormalizedZMod t
      have hC : IsUnit C := h49.mul hL
      have haz : a.z = 0 := a.endpoint_equation
      have hpow : a.y ^ 3 = C * a.v ^ 7 := by
        have ha := a.first_coordinate_equation
        simp only [AwayFirstCoordinatePrimePowerEquation,
          AwayFirstCoordinateLocalEquation] at ha
        rw [hcorr] at ha
        dsimp [C]
        calc
          a.y ^ 3 = 49 * a.v ^ 5 *
              (a.v ^ 2 * leftCorrectionNormalizedZMod t) :=
            (sub_eq_zero.mp ha).symm
          _ = 49 * leftCorrectionNormalizedZMod t * a.v ^ 7 := by ring
      rcases unit_three_seven_parametrization hC a.root_nondegenerate
        a.endpoint_nondegenerate hpow with ⟨p⟩
      exact ⟨{
        scale := p.scale
        scale_isUnit := p.scale_isUnit
        actual_eq := by
          apply AwayRoutingPrimePowerSolution.ext
          · change a.u = (t * C ^ 2) * p.scale ^ 3
            calc a.u = t * a.v := huv.symm
              _ = t * (C ^ 2 * p.scale ^ 3) := congrArg (t * ·) p.v_eq
              _ = (t * C ^ 2) * p.scale ^ 3 := by ring
          · change a.v = C ^ 2 * p.scale ^ 3
            exact p.v_eq
          · change a.y = C ^ 5 * p.scale ^ 7
            exact p.w_eq
          · simpa [canonicalPrimePowerSolution_leftCubic,
              scalePrimePowerSolution] using haz }⟩
  | sum =>
      let C := (49 : ZMod (q ^ e)) * leftCorrectionNormalizedZMod t
      have hC : IsUnit C := h49.mul hL
      have hend : a.y + a.z = 0 := a.endpoint_equation
      have hpow : a.y ^ 3 = C * a.v ^ 7 := by
        have ha := a.first_coordinate_equation
        simp only [AwayFirstCoordinatePrimePowerEquation,
          AwayFirstCoordinateLocalEquation] at ha
        rw [hcorr] at ha
        dsimp [C]
        calc
          a.y ^ 3 = 49 * a.v ^ 5 *
              (a.v ^ 2 * leftCorrectionNormalizedZMod t) :=
            (sub_eq_zero.mp ha).symm
          _ = 49 * leftCorrectionNormalizedZMod t * a.v ^ 7 := by ring
      rcases unit_three_seven_parametrization hC a.root_nondegenerate
        a.endpoint_nondegenerate.1 hpow with ⟨p⟩
      exact ⟨{
        scale := p.scale
        scale_isUnit := p.scale_isUnit
        actual_eq := by
          apply AwayRoutingPrimePowerSolution.ext
          · change a.u = (t * C ^ 2) * p.scale ^ 3
            calc a.u = t * a.v := huv.symm
              _ = t * (C ^ 2 * p.scale ^ 3) := congrArg (t * ·) p.v_eq
              _ = (t * C ^ 2) * p.scale ^ 3 := by ring
          · change a.v = C ^ 2 * p.scale ^ 3
            exact p.v_eq
          · change a.y = C ^ 5 * p.scale ^ 7
            exact p.w_eq
          · change a.z = -(C ^ 5) * p.scale ^ 7
            calc
              a.z = -a.y := (eq_neg_iff_add_eq_zero).2 (by
                simpa [add_comm] using hend)
              _ = -(C ^ 5 * p.scale ^ 7) := congrArg Neg.neg p.w_eq
              _ = -(C ^ 5) * p.scale ^ 7 := by ring }⟩

theorem rightCubic_primePower_orbit_complete {q e : ℕ} (hq : Nat.Prime q)
    (hq7 : q ≠ 7) (he : 0 < e) {row : EndpointRoutingRow}
    (a : AwayRoutingPrimePowerSolution (q ^ e) row .rightCubic) :
    let t := a.u * a.v⁻¹
    let ht := right_normalized_root_of_primePowerSolution a
    Nonempty (PrimePowerOrbitWitness a
      (canonicalPrimePowerSolution_rightCubic hq hq7 he t ht row)) := by
  let t := a.u * a.v⁻¹
  have ht : rightCubicNormalizedZMod t = 0 :=
    right_normalized_root_of_primePowerSolution a
  have huv : t * a.v = a.u := by
    dsimp [t]
    calc
      (a.u * a.v⁻¹) * a.v = a.u * (a.v * a.v⁻¹) := by ring
      _ = a.u := by rw [a.v.mul_inv_of_unit a.root_nondegenerate, mul_one]
  have hcorr : rightCorrectionZMod a.u a.v =
      a.v ^ 2 * rightCorrectionNormalizedZMod t := by
    rw [← huv]
    simp [rightCorrectionZMod, rightCorrectionNormalizedZMod]
    ring
  have hR := rightCorrection_isUnit_of_rightCubic_eq_zero_primePower hq hq7 he t ht
  have h49 := fortyNine_isUnit_zmod_primePower hq hq7 he
  cases row with
  | y =>
      let C := (49 : ZMod (q ^ e)) * rightCorrectionNormalizedZMod t
      have hC : IsUnit C := h49.mul hR
      have hay : a.y = 0 := a.endpoint_equation
      have hpow : a.z ^ 3 = C * a.v ^ 7 := by
        have ha := a.first_coordinate_equation
        simp only [AwayFirstCoordinatePrimePowerEquation,
          AwayFirstCoordinateLocalEquation] at ha
        rw [hcorr] at ha
        dsimp [C]
        calc
          a.z ^ 3 = 49 * a.v ^ 5 *
              (a.v ^ 2 * rightCorrectionNormalizedZMod t) := sub_eq_zero.mp ha
          _ = 49 * rightCorrectionNormalizedZMod t * a.v ^ 7 := by ring
      rcases unit_three_seven_parametrization hC a.root_nondegenerate
        a.endpoint_nondegenerate hpow with ⟨p⟩
      exact ⟨{
        scale := p.scale
        scale_isUnit := p.scale_isUnit
        actual_eq := by
          apply AwayRoutingPrimePowerSolution.ext
          · change a.u = (t * C ^ 2) * p.scale ^ 3
            calc a.u = t * a.v := huv.symm
              _ = t * (C ^ 2 * p.scale ^ 3) := congrArg (t * ·) p.v_eq
              _ = (t * C ^ 2) * p.scale ^ 3 := by ring
          · change a.v = C ^ 2 * p.scale ^ 3
            exact p.v_eq
          · simpa [canonicalPrimePowerSolution_rightCubic,
              scalePrimePowerSolution] using hay
          · change a.z = C ^ 5 * p.scale ^ 7
            exact p.w_eq }⟩
  | z =>
      let C := (-49 : ZMod (q ^ e)) * rightCorrectionNormalizedZMod t
      have hC : IsUnit C := h49.neg.mul hR
      have haz : a.z = 0 := a.endpoint_equation
      have hpow : a.y ^ 3 = C * a.v ^ 7 := by
        have ha := a.first_coordinate_equation
        simp only [AwayFirstCoordinatePrimePowerEquation,
          AwayFirstCoordinateLocalEquation] at ha
        rw [hcorr] at ha
        dsimp [C]
        linear_combination ha
      rcases unit_three_seven_parametrization hC a.root_nondegenerate
        a.endpoint_nondegenerate hpow with ⟨p⟩
      exact ⟨{
        scale := p.scale
        scale_isUnit := p.scale_isUnit
        actual_eq := by
          apply AwayRoutingPrimePowerSolution.ext
          · change a.u = (t * C ^ 2) * p.scale ^ 3
            calc a.u = t * a.v := huv.symm
              _ = t * (C ^ 2 * p.scale ^ 3) := congrArg (t * ·) p.v_eq
              _ = (t * C ^ 2) * p.scale ^ 3 := by ring
          · change a.v = C ^ 2 * p.scale ^ 3
            exact p.v_eq
          · change a.y = C ^ 5 * p.scale ^ 7
            exact p.w_eq
          · simpa [canonicalPrimePowerSolution_rightCubic,
              scalePrimePowerSolution] using haz }⟩
  | sum =>
      let C := (-49 : ZMod (q ^ e)) * rightCorrectionNormalizedZMod t
      have hC : IsUnit C := h49.neg.mul hR
      have hend : a.y + a.z = 0 := a.endpoint_equation
      have hpow : a.y ^ 3 = C * a.v ^ 7 := by
        have ha := a.first_coordinate_equation
        simp only [AwayFirstCoordinatePrimePowerEquation,
          AwayFirstCoordinateLocalEquation] at ha
        rw [hcorr] at ha
        dsimp [C]
        linear_combination ha
      rcases unit_three_seven_parametrization hC a.root_nondegenerate
        a.endpoint_nondegenerate.1 hpow with ⟨p⟩
      exact ⟨{
        scale := p.scale
        scale_isUnit := p.scale_isUnit
        actual_eq := by
          apply AwayRoutingPrimePowerSolution.ext
          · change a.u = (t * C ^ 2) * p.scale ^ 3
            calc a.u = t * a.v := huv.symm
              _ = t * (C ^ 2 * p.scale ^ 3) := congrArg (t * ·) p.v_eq
              _ = (t * C ^ 2) * p.scale ^ 3 := by ring
          · change a.v = C ^ 2 * p.scale ^ 3
            exact p.v_eq
          · change a.y = C ^ 5 * p.scale ^ 7
            exact p.w_eq
          · change a.z = -(C ^ 5) * p.scale ^ 7
            calc
              a.z = -a.y := (eq_neg_iff_add_eq_zero).2 (by
                simpa [add_comm] using hend)
              _ = -(C ^ 5 * p.scale ^ 7) := congrArg Neg.neg p.w_eq
              _ = -(C ^ 5) * p.scale ^ 7 := by ring }⟩

end DkMath.FLT.Seven
