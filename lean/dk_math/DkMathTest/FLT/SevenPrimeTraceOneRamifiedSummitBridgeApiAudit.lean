import DkMath.FLT.Seven.PrimeTraceOneRamifiedSummitBridge

open DkMath.FLT.Seven
open DkMath.NumberTheory.TraceOneQuadratic

#check SevenQuadraticSeventhPowerPacket.toPrimitiveRamifiedSummitPacket
#check SevenQuadraticSeventhPowerPacket.rootSnd_padicValNat_exact

example {x y z : ℕ} (p : SevenQuadraticSeventhPowerPacket x y z) :
    p.toPrimitiveRamifiedSummitPacket.root = p.root := by
  rfl

example {x y z : ℕ} (p : SevenQuadraticSeventhPowerPacket x y z) :
    p.toPrimitiveRamifiedSummitPacket.gapRoot =
      p.residual.powerSplit.a := by
  rfl

example {x y z : ℕ} (p : SevenQuadraticSeventhPowerPacket x y z) :
    p.toPrimitiveRamifiedSummitPacket.residualRoot =
      p.residual.powerSplit.b := by
  rfl

example {x y z : ℕ} (p : SevenQuadraticSeventhPowerPacket x y z) :
    p.toPrimitiveRamifiedSummitPacket.endpointLeft = (z : ℤ) ∧
      p.toPrimitiveRamifiedSummitPacket.endpointRight = (y : ℤ) ∧
      p.toPrimitiveRamifiedSummitPacket.distinguished = (x : ℤ) := by
  constructor
  · rfl
  constructor <;> rfl

example {x y z : ℕ} (p : SevenQuadraticSeventhPowerPacket x y z) :
    padicValNat 7 (Int.natAbs p.root.snd) =
      5 + 7 * padicValNat 7 p.residual.powerSplit.a :=
  p.rootSnd_padicValNat_exact
