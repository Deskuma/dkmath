/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.FirstCoordinateRoutingAudit

#print "file: DkMath.FLT.Seven.RoutingLocalSystems"

namespace DkMath.FLT.Seven

def leftCubicNormalized (t : ℤ) : ℤ := t ^ 3 - 2 * t ^ 2 - t + 1
def rightCubicNormalized (t : ℤ) : ℤ := t ^ 3 + 5 * t ^ 2 + 6 * t + 1
def leftCorrectionNormalized (t : ℤ) : ℤ := 10 * t ^ 2 + 2 * t - 5
def rightCorrectionNormalized (t : ℤ) : ℤ := 10 * t ^ 2 + 18 * t + 3

theorem leftCubic_scale (t s : ℤ) :
    seventhPowerSndLeftCubic (t * s) s = s ^ 3 * leftCubicNormalized t := by
  simp [seventhPowerSndLeftCubic, leftCubicNormalized]
  ring

theorem rightCubic_scale (t s : ℤ) :
    seventhPowerSndRightCubic (t * s) s = s ^ 3 * rightCubicNormalized t := by
  simp [seventhPowerSndRightCubic, rightCubicNormalized]
  ring

theorem leftCorrection_scale (t s : ℤ) :
    leftFstCorrection (t * s) s = s ^ 2 * leftCorrectionNormalized t := by
  simp [leftFstCorrection, leftCorrectionNormalized]
  ring

theorem rightCorrection_scale (t s : ℤ) :
    rightFstCorrection (t * s) s = s ^ 2 * rightCorrectionNormalized t := by
  simp [rightFstCorrection, rightCorrectionNormalized]
  ring

theorem rightCubicNormalized_eq_left_transform (t : ℤ) :
    rightCubicNormalized t = -leftCubicNormalized (-t - 1) := by
  simp [leftCubicNormalized, rightCubicNormalized]
  ring

theorem rightCorrectionNormalized_eq_left_transform (t : ℤ) :
    rightCorrectionNormalized t = leftCorrectionNormalized (-t - 1) := by
  simp [leftCorrectionNormalized, rightCorrectionNormalized]
  ring

theorem left_cubic_correction_bezout (t : ℤ) :
    (60 * t - 88) * leftCubicNormalized t +
      (-6 * t ^ 2 + 22 * t - 19) * leftCorrectionNormalized t = 7 := by
  simp [leftCubicNormalized, leftCorrectionNormalized]
  ring

theorem right_cubic_correction_bezout (t : ℤ) :
    (60 * t + 148) * rightCubicNormalized t +
      (-6 * t ^ 2 - 34 * t - 47) * rightCorrectionNormalized t = 7 := by
  simp [rightCubicNormalized, rightCorrectionNormalized]
  ring

def leftCubicNormalizedZMod {q : ℕ} (t : ZMod q) : ZMod q :=
  t ^ 3 - 2 * t ^ 2 - t + 1
def rightCubicNormalizedZMod {q : ℕ} (t : ZMod q) : ZMod q :=
  t ^ 3 + 5 * t ^ 2 + 6 * t + 1
def leftCorrectionNormalizedZMod {q : ℕ} (t : ZMod q) : ZMod q :=
  10 * t ^ 2 + 2 * t - 5
def rightCorrectionNormalizedZMod {q : ℕ} (t : ZMod q) : ZMod q :=
  10 * t ^ 2 + 18 * t + 3

theorem leftCorrection_ne_zero_of_leftCubic_eq_zero {q : ℕ}
    [Fact (Nat.Prime q)] (hq7 : q ≠ 7) (t : ZMod q)
    (hP : leftCubicNormalizedZMod t = 0) :
    leftCorrectionNormalizedZMod t ≠ 0 := by
  intro hL
  have h7 : (7 : ZMod q) = 0 := by
    calc
      (7 : ZMod q) = (60 * t - 88) * leftCubicNormalizedZMod t +
          (-6 * t ^ 2 + 22 * t - 19) * leftCorrectionNormalizedZMod t := by
        simp [leftCubicNormalizedZMod, leftCorrectionNormalizedZMod]
        ring
      _ = 0 := by rw [hP, hL]; ring
  have hqd : q ∣ 7 := (ZMod.natCast_eq_zero_iff 7 q).1 h7
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hqd with hq1 | hqeq
  · exact (Fact.out : Nat.Prime q).ne_one hq1
  · exact hq7 hqeq

theorem rightCorrection_ne_zero_of_rightCubic_eq_zero {q : ℕ}
    [Fact (Nat.Prime q)] (hq7 : q ≠ 7) (t : ZMod q)
    (hQ : rightCubicNormalizedZMod t = 0) :
    rightCorrectionNormalizedZMod t ≠ 0 := by
  intro hR
  have h7 : (7 : ZMod q) = 0 := by
    calc
      (7 : ZMod q) = (60 * t + 148) * rightCubicNormalizedZMod t +
          (-6 * t ^ 2 - 34 * t - 47) * rightCorrectionNormalizedZMod t := by
        simp [rightCubicNormalizedZMod, rightCorrectionNormalizedZMod]
        ring
      _ = 0 := by rw [hQ, hR]; ring
  have hqd : q ∣ 7 := (ZMod.natCast_eq_zero_iff 7 q).1 h7
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hqd with hq1 | hqeq
  · exact (Fact.out : Nat.Prime q).ne_one hq1
  · exact hq7 hqeq

def AwayEndpointLocalNondegenerate {q : ℕ} :
    EndpointRoutingRow → ZMod q → ZMod q → Prop
  | .y, _, z => z ≠ 0
  | .z, y, _ => y ≠ 0
  | .sum, y, z => y ≠ 0 ∧ z ≠ 0

def AwayEndpointLocalEquation {q : ℕ} :
    EndpointRoutingRow → ZMod q → ZMod q → Prop
  | .y, y, _ => y = 0
  | .z, _, z => z = 0
  | .sum, y, z => y + z = 0

def leftCubicZMod {q : ℕ} (u v : ZMod q) : ZMod q :=
  u ^ 3 - 2 * u ^ 2 * v - u * v ^ 2 + v ^ 3
def rightCubicZMod {q : ℕ} (u v : ZMod q) : ZMod q :=
  u ^ 3 + 5 * u ^ 2 * v + 6 * u * v ^ 2 + v ^ 3
def leftCorrectionZMod {q : ℕ} (u v : ZMod q) : ZMod q :=
  10 * u ^ 2 + 2 * u * v - 5 * v ^ 2
def rightCorrectionZMod {q : ℕ} (u v : ZMod q) : ZMod q :=
  10 * u ^ 2 + 18 * u * v + 3 * v ^ 2

def AwayRootLocalNondegenerate {q : ℕ} :
    RootRoutingColumn → ZMod q → ZMod q → Prop
  | .sevenV, u, _ => u ≠ 0
  | .leftCubic, _, v => v ≠ 0
  | .rightCubic, _, v => v ≠ 0

def AwayRootLocalEquation {q : ℕ} :
    RootRoutingColumn → ZMod q → ZMod q → Prop
  | .sevenV, _, v => v = 0
  | .leftCubic, u, v => leftCubicZMod u v = 0
  | .rightCubic, u, v => rightCubicZMod u v = 0

def AwayFirstCoordinateLocalEquation {q : ℕ} :
    EndpointRoutingRow → RootRoutingColumn →
      ZMod q → ZMod q → ZMod q → ZMod q → Prop
  | .y, .sevenV, u, _, _, z => u ^ 7 - z ^ 3 = 0
  | .z, .sevenV, u, _, y, _ => u ^ 7 + y ^ 3 = 0
  | .sum, .sevenV, u, _, y, _ => u ^ 7 + y ^ 3 = 0
  | .y, .leftCubic, u, v, _, z =>
      z ^ 3 + 49 * v ^ 5 * leftCorrectionZMod u v = 0
  | .z, .leftCubic, u, v, y, _ =>
      49 * v ^ 5 * leftCorrectionZMod u v - y ^ 3 = 0
  | .sum, .leftCubic, u, v, y, _ =>
      49 * v ^ 5 * leftCorrectionZMod u v - y ^ 3 = 0
  | .y, .rightCubic, u, v, _, z =>
      z ^ 3 - 49 * v ^ 5 * rightCorrectionZMod u v = 0
  | .z, .rightCubic, u, v, y, _ =>
      y ^ 3 + 49 * v ^ 5 * rightCorrectionZMod u v = 0
  | .sum, .rightCubic, u, v, y, _ =>
      y ^ 3 + 49 * v ^ 5 * rightCorrectionZMod u v = 0

structure AwayRoutingLocalSolution (q : ℕ)
    (row : EndpointRoutingRow) (column : RootRoutingColumn) : Type where
  u : ZMod q
  v : ZMod q
  y : ZMod q
  z : ZMod q
  endpoint_nonzero : AwayEndpointLocalNondegenerate row y z
  endpoint_equation : AwayEndpointLocalEquation row y z
  root_nonzero : AwayRootLocalNondegenerate column u v
  root_equation : AwayRootLocalEquation column u v
  first_coordinate_equation : AwayFirstCoordinateLocalEquation row column u v y z

end DkMath.FLT.Seven
