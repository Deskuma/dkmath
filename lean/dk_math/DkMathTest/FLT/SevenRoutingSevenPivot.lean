import DkMath.FLT.Seven

open DkMath.FLT.Seven

example (z y : ℤ) : cyclotomicSevenFst z y - z ^ 3 = y * (z - y) * (z + y) :=
  cyclotomicSevenFst_sub_right_cube z y

example (z y : ℤ) : cyclotomicSevenFst z y + y ^ 3 = z ^ 2 * (z + y) :=
  cyclotomicSevenFst_add_left_cube z y

example (u v : ℤ) :
    seventhPowerFst u v = u ^ 7 + v ^ 2 * seventhPowerFstVResidual u v :=
  seventhPowerFst_eq_u_seven_add_v_sq u v

example (u v : ℤ) : seventhPowerFst u v =
    seventhPowerSndLeftCubic u v * leftFstQuotient u v -
      49 * v ^ 5 * leftFstCorrection u v :=
  seventhPowerFst_leftCubic_division u v

example (u v : ℤ) : seventhPowerFst u v =
    seventhPowerSndRightCubic u v * rightFstQuotient u v +
      49 * v ^ 5 * rightFstCorrection u v :=
  seventhPowerFst_rightCubic_division u v

example {x y z : ℕ} (p : AwayCoordinateNormalForm x y z) :
    AwayRootResidueSector x y z p := awayRootResidueSector_of_packet p

example {x y z : ℕ} (p : AwayCoordinateNormalForm x y z) :
    awayRootLinearModSeven p ≠ 0 := p.rootLinear_ne_zero

example {x y z : ℕ} (r : AwayCubicRoutingPacket x y z) :
    AwayRoutingSevenPivot r := awayRoutingSevenPivot_of_packet r

example {x y z : ℕ} (r : AwayCubicRoutingPacket x y z) :
    Nonempty (AwayRoutingPivotDepth r) := nonempty_awayRoutingPivotDepth r

example {x y z : ℕ} (r : AwayCubicRoutingPacket x y z)
    (h : AwayRoutingSevenPivot r) :
    (7 ∣ r.routing.c11 ∧ ¬ 7 ∣ r.routing.c12 ∧ ¬ 7 ∣ r.routing.c13) ∨
    (7 ∣ r.routing.c21 ∧ ¬ 7 ∣ r.routing.c22 ∧ ¬ 7 ∣ r.routing.c23) ∨
    (7 ∣ r.routing.c31 ∧ ¬ 7 ∣ r.routing.c32 ∧ ¬ 7 ∣ r.routing.c33) := by
  cases h with
  | rowY h11 h12 h13 => exact Or.inl ⟨h11, h12, h13⟩
  | rowZ h21 h11 h12 h13 h22 h23 => exact Or.inr (Or.inl ⟨h21, h22, h23⟩)
  | rowSum h31 h11 h12 h13 h21 h22 h23 h32 h33 =>
      exact Or.inr (Or.inr ⟨h31, h32, h33⟩)

#print axioms awayRootResidueSector_of_packet
#print axioms awayRoutingSevenPivot_of_packet
#print axioms nonempty_awayRoutingPivotDepth

