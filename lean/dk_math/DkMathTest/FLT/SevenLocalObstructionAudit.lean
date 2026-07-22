import DkMath.FLT.Seven

open DkMath.FLT.Seven

noncomputable section

example {q : ℕ} [Fact (Nat.Prime q)] :
    Nonempty (AwayRoutingLocalSolution q .y .sevenV) :=
  nonempty_localSolution_sevenV .y

example {q : ℕ} [Fact (Nat.Prime q)] :
    Nonempty (AwayRoutingLocalSolution q .z .sevenV) :=
  nonempty_localSolution_sevenV .z

example {q : ℕ} [Fact (Nat.Prime q)] :
    Nonempty (AwayRoutingLocalSolution q .sum .sevenV) :=
  nonempty_localSolution_sevenV .sum

example {q : ℕ} [Fact (Nat.Prime q)] (hq7 : q ≠ 7) (t : ZMod q)
    (h : leftCubicNormalizedZMod t = 0) (row : EndpointRoutingRow) :
    Nonempty (AwayRoutingLocalSolution q row .leftCubic) :=
  nonempty_localSolution_leftCubic_of_root hq7 t h row

example {q : ℕ} [Fact (Nat.Prime q)] (hq7 : q ≠ 7) (t : ZMod q)
    (h : rightCubicNormalizedZMod t = 0) (row : EndpointRoutingRow) :
    Nonempty (AwayRoutingLocalSolution q row .rightCubic) :=
  nonempty_localSolution_rightCubic_of_root hq7 t h row

example {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (w : AwayRoutingPrimeWitness r) (hq7 : w.q ≠ 7) :
    AwayRoutingLocalSolution w.q w.row w.column :=
  w.toLocalSolution hq7

example {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (w : AwayRoutingPrimeWitness r) (hq7 : w.q ≠ 7) :
    Nonempty (AwayNonSevenLocalSolubilitySource w.q w.row w.column) :=
  localSolubilitySource_of_primeWitness w hq7

example {x y z : ℕ} (h : CounterexamplePack x y z) :
    Nonempty (FirstResidueLocalAuditResult x y z) :=
  firstResidueLocalAuditResult_of_pack h

#print axioms nonempty_localSolution_sevenV
#print axioms nonempty_localSolution_leftCubic_of_root
#print axioms nonempty_localSolution_rightCubic_of_root
#print axioms AwayRoutingPrimeWitness.toLocalSolution
#print axioms localSolubilitySource_of_primeWitness
#print axioms firstResidueLocalAuditResult_of_pack
