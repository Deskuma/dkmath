import DkMath.FLT.Seven

open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.FLT.Seven

example {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hgap : ¬ 7 ∣ z - y) (root : TraceOneInt (-2))
    (heq : cyclotomicSevenToTraceOne (z : ℤ) (y : ℤ) = root ^ 7) :
    AwayCoordinateNormalForm x y z :=
  awayCoordinateNormalForm_of_route hPack hgap root heq

example {x y z : ℕ} (packet : SevenQuadraticSeventhPowerPacket x y z) :
    RamifiedCoordinateNormalForm x y z :=
  ramifiedCoordinateNormalForm_of_packet packet

example {x y z : ℕ} (p : AwayCoordinateNormalForm x y z) :
    AwayExceptionalFactor y z := awayExceptionalFactor_of_packet p

example {x y z : ℕ} (t : ModSeven) (ht : t ≠ 0)
    (hx : (x : ModSeven) = 0) (hy : (y : ModSeven) = t)
    (hz : (z : ModSeven) = t) : SevenEndpointResidueSector x y z :=
  .ramified t ht hx hy hz

example {x y z : ℕ} (t : ModSeven) (ht : t ≠ 0)
    (hx : (x : ModSeven) = t) (hy : (y : ModSeven) = 0)
    (hz : (z : ModSeven) = t) : SevenEndpointResidueSector x y z :=
  .awayRight t ht hx hy hz

example {x y z : ℕ} (t : ModSeven) (ht : t ≠ 0)
    (hx : (x : ModSeven) = -t) (hy : (y : ModSeven) = t)
    (hz : (z : ModSeven) = 0) : SevenEndpointResidueSector x y z :=
  .awayLeft t ht hx hy hz

example {x y z : ℕ} (t : ModSeven) (ht : t ≠ 0)
    (hx : (x : ModSeven) = -2 * t) (hy : (y : ModSeven) = t)
    (hz : (z : ModSeven) = -t) : SevenEndpointResidueSector x y z :=
  .awaySum t ht hx hy hz

example {x y z : ℕ} (hPack : CounterexamplePack x y z) :
    SevenEndpointResidueSector x y z :=
  sevenEndpointResidueSector_of_counterexample hPack

#print axioms coordinateCounterexampleRoute_of_pack
#print axioms seven_dvd_endpoint_product_of_away
#print axioms awayExceptionalFactor_of_packet
#print axioms sevenEndpointResidueSector_of_counterexample
