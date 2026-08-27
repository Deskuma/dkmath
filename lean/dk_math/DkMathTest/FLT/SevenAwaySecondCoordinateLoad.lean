import DkMath.FLT.Seven

open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.FLT.Seven

example {x y z : ℕ} (p : AwayCoordinateNormalForm x y z) :
    ¬ (7 : ℤ) ∣ norm p.root := p.root_norm_not_seven_dvd

example {x y z : ℕ} (p : AwayCoordinateNormalForm x y z) :
    y * z * (y + z) =
      Int.natAbs (seventhPowerSnd p.root.fst p.root.snd) :=
  away_endpoint_product_eq_natAbs_seventhPowerSnd p

example {x y z : ℕ} (p : AwayCoordinateNormalForm x y z) :
    y * z * (y + z) = 7 * Int.natAbs p.root.snd *
      Int.natAbs (seventhPowerSndCore p.root.fst p.root.snd) :=
  away_endpoint_product_load_eq p

example {x y z : ℕ} (p : AwayCoordinateNormalForm x y z) :
    p.root.snd ≠ 0 := p.root_snd_ne_zero

example {x y z : ℕ} (p : AwayCoordinateNormalForm x y z) :
    seventhPowerSndCore p.root.fst p.root.snd ≠ 0 := p.sndCore_ne_zero

#print axioms AwayCoordinateNormalForm.root_norm_not_seven_dvd
#print axioms away_endpoint_product_load_eq
#print axioms padicValNat_unique_factor_of_triple
#print axioms padicValNat_seven_mul_of_core_not_dvd
