import DkMath.FLT.Seven

open DkMath.FLT.Seven
open DkMath.NumberTheory.TraceOneQuadratic

example (u v : ℤ) :
    seventhPowerSndCore u v =
      seventhPowerSndLeftCubic u v * seventhPowerSndRightCubic u v :=
  seventhPowerSndCore_factor u v

example (u v : ℤ) :
    seventhPowerSndRightCubic u v - seventhPowerSndLeftCubic u v =
      7 * u * v * (u + v) :=
  seventhPowerSnd_cubic_sub u v

example (u v : ℤ) :
    seventhPowerSndLeftCubic u v + seventhPowerSndRightCubic u v =
      (2 * u + v) * norm (⟨u, v⟩ : TraceOneInt (-2)) :=
  seventhPowerSnd_cubic_add u v

example {x y z : ℕ} (p : AwayCoordinateNormalForm x y z) :
    IsCoprime p.root.fst p.root.snd := p.root_coordinates_isCoprime

example {x y z : ℕ} (p : AwayCoordinateNormalForm x y z) :
    Nat.Coprime (Int.natAbs p.root.snd)
      (Int.natAbs (seventhPowerSndLeftCubic p.root.fst p.root.snd)) :=
  p.coprime_rootSnd_leftCubic

example {x y z : ℕ} (p : AwayCoordinateNormalForm x y z) :
    Nat.Coprime (Int.natAbs p.root.snd)
      (Int.natAbs (seventhPowerSndRightCubic p.root.fst p.root.snd)) :=
  p.coprime_rootSnd_rightCubic

example {x y z : ℕ} (p : AwayCoordinateNormalForm x y z) :
    Nat.Coprime
      (Int.natAbs (seventhPowerSndLeftCubic p.root.fst p.root.snd))
      (Int.natAbs (seventhPowerSndRightCubic p.root.fst p.root.snd)) :=
  p.coprime_leftCubic_rightCubic

example {x y z : ℕ} (p : AwayCoordinateNormalForm x y z) :
    y * z * (y + z) =
      7 * Int.natAbs p.root.snd *
        Int.natAbs (seventhPowerSndLeftCubic p.root.fst p.root.snd) *
        Int.natAbs (seventhPowerSndRightCubic p.root.fst p.root.snd) :=
  away_endpoint_product_cubic_load_eq p

#print axioms seventhPowerSndCore_factor
#print axioms AwayCoordinateNormalForm.root_coordinates_isCoprime
#print axioms AwayCoordinateNormalForm.coprime_leftCubic_rightCubic
#print axioms away_endpoint_product_cubic_load_eq

