/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.RoutingLocalSystems

#print "file: DkMath.FLT.Seven.RoutingLocalSolubility"

namespace DkMath.FLT.Seven

private theorem fortyNine_ne_zero {q : ℕ} [Fact (Nat.Prime q)]
    (hq7 : q ≠ 7) : (49 : ZMod q) ≠ 0 := by
  intro h
  have hqd : q ∣ 49 := (ZMod.natCast_eq_zero_iff 49 q).1 h
  have hqprod : q ∣ 7 * 7 := by norm_num at hqd ⊢; exact hqd
  have hq7d : q ∣ 7 := by
    rcases (Fact.out : Nat.Prime q).dvd_mul.mp hqprod with h | h
    · exact h
    · exact h
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hq7d with hq1 | hqeq
  · exact (Fact.out : Nat.Prime q).ne_one hq1
  · exact hq7 hqeq

theorem nonempty_localSolution_sevenV {q : ℕ} [Fact (Nat.Prime q)]
    (row : EndpointRoutingRow) :
    Nonempty (AwayRoutingLocalSolution q row .sevenV) := by
  cases row with
  | y =>
      exact ⟨{
        u := 1, v := 0, y := 0, z := 1
        endpoint_nonzero := one_ne_zero
        endpoint_equation := rfl
        root_nonzero := one_ne_zero
        root_equation := rfl
        first_coordinate_equation := by norm_num [AwayFirstCoordinateLocalEquation] }⟩
  | z =>
      exact ⟨{
        u := -1, v := 0, y := 1, z := 0
        endpoint_nonzero := one_ne_zero
        endpoint_equation := rfl
        root_nonzero := neg_ne_zero.mpr one_ne_zero
        root_equation := rfl
        first_coordinate_equation := by
          simp [AwayFirstCoordinateLocalEquation]
          ring }⟩
  | sum =>
      exact ⟨{
        u := -1, v := 0, y := 1, z := -1
        endpoint_nonzero := ⟨one_ne_zero, neg_ne_zero.mpr one_ne_zero⟩
        endpoint_equation := by simp [AwayEndpointLocalEquation]
        root_nonzero := neg_ne_zero.mpr one_ne_zero
        root_equation := rfl
        first_coordinate_equation := by
          simp [AwayFirstCoordinateLocalEquation]
          ring }⟩

private theorem left_scaled_root {q : ℕ} [Fact (Nat.Prime q)]
    (t C : ZMod q) (hroot : leftCubicNormalizedZMod t = 0) :
    leftCubicZMod (t * C ^ 2) (C ^ 2) = 0 := by
  rw [show leftCubicZMod (t * C ^ 2) (C ^ 2) =
      C ^ 6 * leftCubicNormalizedZMod t by
    simp [leftCubicZMod, leftCubicNormalizedZMod]
    ring]
  rw [hroot, mul_zero]

private theorem left_scaled_correction {q : ℕ} [Fact (Nat.Prime q)]
    (t C : ZMod q) :
    leftCorrectionZMod (t * C ^ 2) (C ^ 2) =
      C ^ 4 * leftCorrectionNormalizedZMod t := by
  simp [leftCorrectionZMod, leftCorrectionNormalizedZMod]
  ring

theorem nonempty_localSolution_leftCubic_of_root {q : ℕ}
    [Fact (Nat.Prime q)] (hq7 : q ≠ 7) (t : ZMod q)
    (hroot : leftCubicNormalizedZMod t = 0) (row : EndpointRoutingRow) :
    Nonempty (AwayRoutingLocalSolution q row .leftCubic) := by
  let L := leftCorrectionNormalizedZMod t
  have hL : L ≠ 0 := leftCorrection_ne_zero_of_leftCubic_eq_zero hq7 t hroot
  have h49 := fortyNine_ne_zero hq7
  cases row with
  | y =>
      let C : ZMod q := -49 * L
      have hC : C ≠ 0 := mul_ne_zero (neg_ne_zero.mpr h49) hL
      exact ⟨{
        u := t * C ^ 2, v := C ^ 2, y := 0, z := C ^ 5
        endpoint_nonzero := pow_ne_zero 5 hC
        endpoint_equation := rfl
        root_nonzero := pow_ne_zero 2 hC
        root_equation := left_scaled_root t C hroot
        first_coordinate_equation := by
          simp only [AwayFirstCoordinateLocalEquation]
          rw [left_scaled_correction]
          dsimp [C, L]
          ring }⟩
  | z =>
      let C : ZMod q := 49 * L
      have hC : C ≠ 0 := mul_ne_zero h49 hL
      exact ⟨{
        u := t * C ^ 2, v := C ^ 2, y := C ^ 5, z := 0
        endpoint_nonzero := pow_ne_zero 5 hC
        endpoint_equation := rfl
        root_nonzero := pow_ne_zero 2 hC
        root_equation := left_scaled_root t C hroot
        first_coordinate_equation := by
          simp only [AwayFirstCoordinateLocalEquation]
          rw [left_scaled_correction]
          dsimp [C, L]
          ring }⟩
  | sum =>
      let C : ZMod q := 49 * L
      have hC : C ≠ 0 := mul_ne_zero h49 hL
      exact ⟨{
        u := t * C ^ 2, v := C ^ 2, y := C ^ 5, z := -(C ^ 5)
        endpoint_nonzero := ⟨pow_ne_zero 5 hC, neg_ne_zero.mpr (pow_ne_zero 5 hC)⟩
        endpoint_equation := by simp [AwayEndpointLocalEquation]
        root_nonzero := pow_ne_zero 2 hC
        root_equation := left_scaled_root t C hroot
        first_coordinate_equation := by
          simp only [AwayFirstCoordinateLocalEquation]
          rw [left_scaled_correction]
          dsimp [C, L]
          ring }⟩

private theorem right_scaled_root {q : ℕ} [Fact (Nat.Prime q)]
    (t C : ZMod q) (hroot : rightCubicNormalizedZMod t = 0) :
    rightCubicZMod (t * C ^ 2) (C ^ 2) = 0 := by
  rw [show rightCubicZMod (t * C ^ 2) (C ^ 2) =
      C ^ 6 * rightCubicNormalizedZMod t by
    simp [rightCubicZMod, rightCubicNormalizedZMod]
    ring]
  rw [hroot, mul_zero]

private theorem right_scaled_correction {q : ℕ} [Fact (Nat.Prime q)]
    (t C : ZMod q) :
    rightCorrectionZMod (t * C ^ 2) (C ^ 2) =
      C ^ 4 * rightCorrectionNormalizedZMod t := by
  simp [rightCorrectionZMod, rightCorrectionNormalizedZMod]
  ring

theorem nonempty_localSolution_rightCubic_of_root {q : ℕ}
    [Fact (Nat.Prime q)] (hq7 : q ≠ 7) (t : ZMod q)
    (hroot : rightCubicNormalizedZMod t = 0) (row : EndpointRoutingRow) :
    Nonempty (AwayRoutingLocalSolution q row .rightCubic) := by
  let R := rightCorrectionNormalizedZMod t
  have hR : R ≠ 0 := rightCorrection_ne_zero_of_rightCubic_eq_zero hq7 t hroot
  have h49 := fortyNine_ne_zero hq7
  cases row with
  | y =>
      let C : ZMod q := 49 * R
      have hC : C ≠ 0 := mul_ne_zero h49 hR
      exact ⟨{
        u := t * C ^ 2, v := C ^ 2, y := 0, z := C ^ 5
        endpoint_nonzero := pow_ne_zero 5 hC
        endpoint_equation := rfl
        root_nonzero := pow_ne_zero 2 hC
        root_equation := right_scaled_root t C hroot
        first_coordinate_equation := by
          simp only [AwayFirstCoordinateLocalEquation]
          rw [right_scaled_correction]
          dsimp [C, R]
          ring }⟩
  | z =>
      let C : ZMod q := -49 * R
      have hC : C ≠ 0 := mul_ne_zero (neg_ne_zero.mpr h49) hR
      exact ⟨{
        u := t * C ^ 2, v := C ^ 2, y := C ^ 5, z := 0
        endpoint_nonzero := pow_ne_zero 5 hC
        endpoint_equation := rfl
        root_nonzero := pow_ne_zero 2 hC
        root_equation := right_scaled_root t C hroot
        first_coordinate_equation := by
          simp only [AwayFirstCoordinateLocalEquation]
          rw [right_scaled_correction]
          dsimp [C, R]
          ring }⟩
  | sum =>
      let C : ZMod q := -49 * R
      have hC : C ≠ 0 := mul_ne_zero (neg_ne_zero.mpr h49) hR
      exact ⟨{
        u := t * C ^ 2, v := C ^ 2, y := C ^ 5, z := -(C ^ 5)
        endpoint_nonzero := ⟨pow_ne_zero 5 hC, neg_ne_zero.mpr (pow_ne_zero 5 hC)⟩
        endpoint_equation := by simp [AwayEndpointLocalEquation]
        root_nonzero := pow_ne_zero 2 hC
        root_equation := right_scaled_root t C hroot
        first_coordinate_equation := by
          simp only [AwayFirstCoordinateLocalEquation]
          rw [right_scaled_correction]
          dsimp [C, R]
          ring }⟩

private theorem zmod_zero_of_int_dvd {q : ℕ} [Fact (Nat.Prime q)]
    {a : ℤ} (h : (q : ℤ) ∣ a) : (a : ZMod q) = 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd a q).2 h

private theorem prime_not_one {q : ℕ} [Fact (Nat.Prime q)] : q ≠ 1 :=
  (Fact.out : Nat.Prime q).ne_one

-- The dependent row/column split deliberately simplifies both the copied
-- divisibility hypothesis and its indexed target in one step.
set_option linter.flexible false in
noncomputable def AwayRoutingPrimeWitness.toLocalSolution {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} (w : AwayRoutingPrimeWitness r)
    (hq7 : w.q ≠ 7) : AwayRoutingLocalSolution w.q w.row w.column := by
  letI : Fact (Nat.Prime w.q) := ⟨w.q_prime⟩
  let u : ZMod w.q := r.cubic.rootTriple.normal.root.fst
  let v : ZMod w.q := r.cubic.rootTriple.normal.root.snd
  let yy : ZMod w.q := y
  let zz : ZMod w.q := z
  have hendpointDvd := w.q_dvd_cell.trans
    (routingCell_dvd_endpoint r w.row w.column)
  have hendpoint : AwayEndpointLocalEquation w.row yy zz := by
    cases hr : w.row with
    | y =>
        have hd : w.q ∣ y := by simpa [hr, endpointRoutingFactor] using hendpointDvd
        exact (ZMod.natCast_eq_zero_iff y w.q).2 hd
    | z =>
        have hd : w.q ∣ z := by simpa [hr, endpointRoutingFactor] using hendpointDvd
        exact (ZMod.natCast_eq_zero_iff z w.q).2 hd
    | sum =>
        have hd : w.q ∣ y + z := by simpa [hr, endpointRoutingFactor] using hendpointDvd
        have hz := (ZMod.natCast_eq_zero_iff (y + z) w.q).2 hd
        simpa [yy, zz, Nat.cast_add] using hz
  have hendpoint_ne : AwayEndpointLocalNondegenerate w.row yy zz := by
    cases hr : w.row with
    | y =>
        simp only [AwayEndpointLocalNondegenerate]
        have hqd : w.q ∣ y := by simpa [hr, endpointRoutingFactor] using hendpointDvd
        intro hz0
        have hqz : w.q ∣ z := (ZMod.natCast_eq_zero_iff z w.q).1 hz0
        exact prime_not_one (Nat.eq_one_of_dvd_coprimes
          r.cubic.endpointTriple.coprime_first_second hqd hqz)
    | z =>
        simp only [AwayEndpointLocalNondegenerate]
        have hqd : w.q ∣ z := by simpa [hr, endpointRoutingFactor] using hendpointDvd
        intro hy0
        have hqy : w.q ∣ y := (ZMod.natCast_eq_zero_iff y w.q).1 hy0
        exact prime_not_one (Nat.eq_one_of_dvd_coprimes
          r.cubic.endpointTriple.coprime_first_second hqy hqd)
    | sum =>
        simp only [AwayEndpointLocalNondegenerate]
        have hqd : w.q ∣ y + z := by simpa [hr, endpointRoutingFactor] using hendpointDvd
        constructor
        · intro hy0
          have hqy : w.q ∣ y := (ZMod.natCast_eq_zero_iff y w.q).1 hy0
          exact prime_not_one (Nat.eq_one_of_dvd_coprimes
            r.cubic.endpointTriple.coprime_first_third hqy hqd)
        · intro hz0
          have hqz : w.q ∣ z := (ZMod.natCast_eq_zero_iff z w.q).1 hz0
          exact prime_not_one (Nat.eq_one_of_dvd_coprimes
            r.cubic.endpointTriple.coprime_second_third hqz hqd)
  have hrootDvd : (w.q : ℤ) ∣ rootRoutingFactor r w.column :=
    w.root_condition.resolve_left hq7
  have hroot : AwayRootLocalEquation w.column u v := by
    have hd := hrootDvd
    cases hc : w.column <;> simp [hc, AwayRootLocalEquation, rootRoutingFactor, u, v,
      leftCubicZMod, rightCubicZMod] at hd ⊢
    all_goals
      have hz := zmod_zero_of_int_dvd hd
      simpa [seventhPowerSndLeftCubic, seventhPowerSndRightCubic] using hz
  have hroot_ne : AwayRootLocalNondegenerate w.column u v := by
    cases hc : w.column with
    | sevenV =>
        simp only [AwayRootLocalNondegenerate]
        have hd : (w.q : ℤ) ∣ r.cubic.rootTriple.normal.root.snd := by
          simpa [hc, rootRoutingFactor] using hrootDvd
        intro hu0
        have hqu : w.q ∣ Int.natAbs r.cubic.rootTriple.normal.root.fst := by
          apply Int.natCast_dvd.mp
          exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (by simpa [u] using hu0)
        have hqv : w.q ∣ r.cubic.rootTriple.vPart := by
          rw [r.cubic.rootTriple.vPart_eq]
          exact Int.natCast_dvd.mp hd
        exact prime_not_one (Nat.eq_one_of_dvd_coprimes
          r.cubic.rootTriple.normal.root_coordinates_natAbs_coprime hqu (by
            simpa [r.cubic.rootTriple.vPart_eq] using hqv))
    | leftCubic =>
        simp only [AwayRootLocalNondegenerate]
        have hd : (w.q : ℤ) ∣ seventhPowerSndLeftCubic
            r.cubic.rootTriple.normal.root.fst r.cubic.rootTriple.normal.root.snd := by
          simpa [hc, rootRoutingFactor] using hrootDvd
        intro hv0
        have hqv : w.q ∣ r.cubic.rootTriple.vPart := by
          rw [r.cubic.rootTriple.vPart_eq]
          apply Int.natCast_dvd.mp
          exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (by simpa [v] using hv0)
        have hqP : w.q ∣ r.cubic.rootTriple.leftPart := by
          rw [r.cubic.rootTriple.leftPart_eq]
          exact Int.natCast_dvd.mp hd
        exact prime_not_one (Nat.eq_one_of_dvd_coprimes
          r.cubic.rootTriple.coprime_v_left hqv hqP)
    | rightCubic =>
        simp only [AwayRootLocalNondegenerate]
        have hd : (w.q : ℤ) ∣ seventhPowerSndRightCubic
            r.cubic.rootTriple.normal.root.fst r.cubic.rootTriple.normal.root.snd := by
          simpa [hc, rootRoutingFactor] using hrootDvd
        intro hv0
        have hqv : w.q ∣ r.cubic.rootTriple.vPart := by
          rw [r.cubic.rootTriple.vPart_eq]
          apply Int.natCast_dvd.mp
          exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (by simpa [v] using hv0)
        have hqQ : w.q ∣ r.cubic.rootTriple.rightPart := by
          rw [r.cubic.rootTriple.rightPart_eq]
          exact Int.natCast_dvd.mp hd
        exact prime_not_one (Nat.eq_one_of_dvd_coprimes
          r.cubic.rootTriple.coprime_v_right hqv hqQ)
  have hfirstDvd : (w.q : ℤ) ∣ routingFirstCoordinateValue r w.row w.column :=
    w.firstCoordinate_condition.resolve_left hq7
  have hfirst : AwayFirstCoordinateLocalEquation w.row w.column u v yy zz := by
    have hd := hfirstDvd
    cases hr : w.row <;> cases hc : w.column
    all_goals
      have hz := zmod_zero_of_int_dvd (by
        simpa [hr, hc, routingFirstCoordinateValue] using hd)
      simpa [hr, hc, AwayFirstCoordinateLocalEquation,
        u, v, yy, zz, leftCorrectionZMod, rightCorrectionZMod,
        leftFstCorrection, rightFstCorrection] using hz
  exact {
    u := u, v := v, y := yy, z := zz
    endpoint_nonzero := hendpoint_ne
    endpoint_equation := hendpoint
    root_nonzero := hroot_ne
    root_equation := hroot
    first_coordinate_equation := hfirst }

end DkMath.FLT.Seven
