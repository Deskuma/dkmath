import DkMath.FLT.Seven

open DkMath.FLT.Seven

example {x y z : ℕ} (r : AwayCubicRoutingPacket x y z) :
    Nonempty (AwayFirstCoordinateRoutingConstraints r) :=
  nonempty_awayFirstCoordinateRoutingConstraints r

example {x y z : ℕ} (r : AwayCubicRoutingPacket x y z)
    (c : AwayFirstCoordinateRoutingConstraints r) :
    (r.routing.c12 : ℤ) ∣ routingFirstCoordinateValue r .y .leftCubic :=
  c.c12_constraint

example {x y z : ℕ} (r : AwayCubicRoutingPacket x y z)
    (c : AwayFirstCoordinateRoutingConstraints r) :
    (r.routing.c33 : ℤ) ∣ routingFirstCoordinateValue r .sum .rightCubic :=
  c.c33_constraint

example {x y z q : ℕ} (r : AwayCubicRoutingPacket x y z)
    (c : AwayFirstCoordinateRoutingConstraints r) (hq : Nat.Prime q)
    (hq7 : q ≠ 7) (h : q ∣ r.routing.c21) :
    (q : ℤ) ∣ routingFirstCoordinateValue r .z .sevenV :=
  c.c21_nonSeven_constraint q hq hq7 h

example {x y z : ℕ} (r : AwayCubicRoutingPacket x y z)
    (c : AwayFirstCoordinateRoutingConstraints r)
    (h : routingCell r.routing .y .leftCubic ≠ 1) :
    Nonempty (AwayRoutingPrimeWitness r) :=
  routingPrimeWitness_of_cell_ne_one r c .y .leftCubic h

example {x y z : ℕ} (r : AwayCubicRoutingPacket x y z)
    (resolution : AwayFirstCoordinateClosureResolution r) :
    Nonempty (AwayDescentClosureProvider x y z r.cubic.transfer) :=
  awayDescentClosureProvider_of_firstCoordinateResolution r resolution

example {x y z : ℕ} (p : RamifiedCoordinateNormalForm x y z) :
    FirstCoordinateClosureAuditResult x y z := .ramified p

example {x y z : ℕ} (r : AwayCubicRoutingPacket x y z)
    (c : AwayFirstCoordinateRoutingConstraints r) :
    FirstCoordinateClosureAuditResult x y z := .awayConstrained r c

example {x y z : ℕ} (h : CounterexamplePack x y z) :
    Nonempty (FirstCoordinateClosureAuditResult x y z) :=
  firstCoordinateClosureAuditResult_of_pack h

#print axioms nonempty_awayFirstCoordinateRoutingConstraints
#print axioms routingPrimeWitness_of_cell_ne_one
#print axioms awayDescentClosureProvider_of_firstCoordinateResolution
#print axioms firstCoordinateClosureAuditResult_of_pack
