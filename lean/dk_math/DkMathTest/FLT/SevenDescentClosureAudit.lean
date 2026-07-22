import DkMath.FLT.Seven

open DkMath.FLT.Seven

example {x y z : ℕ} (p : AwayCoordinateNormalForm x y z) :
    Nat.Coprime y z ∧ Nat.Coprime y (y + z) ∧ Nat.Coprime z (y + z) := by
  let t := awayEndpointCoprimeTriple p
  exact ⟨t.coprime_first_second, t.coprime_first_third,
    t.coprime_second_third⟩

example {a₁ a₂ a₃ b₁ b₂ b₃ : ℕ}
    (ha_pos : 0 < a₁ ∧ 0 < a₂ ∧ 0 < a₃)
    (hb_pos : 0 < b₁ ∧ 0 < b₂ ∧ 0 < b₃)
    (ha12 : Nat.Coprime a₁ a₂) (ha13 : Nat.Coprime a₁ a₃)
    (ha23 : Nat.Coprime a₂ a₃) (hb12 : Nat.Coprime b₁ b₂)
    (hb13 : Nat.Coprime b₁ b₃) (hb23 : Nat.Coprime b₂ b₃)
    (hprod : a₁ * a₂ * a₃ = b₁ * b₂ * b₃) :
    Nonempty (CoprimeTripleRouting a₁ a₂ a₃ b₁ b₂ b₃) :=
  nonempty_coprimeTripleRouting ha_pos hb_pos ha12 ha13 ha23 hb12 hb13 hb23 hprod

example {a₁ a₂ a₃ b₁ b₂ b₃ : ℕ}
    (r : CoprimeTripleRouting a₁ a₂ a₃ b₁ b₂ b₃) :
    a₁ = r.c11 * r.c12 * r.c13 ∧ b₁ = r.c11 * r.c21 * r.c31 :=
  ⟨r.row1, r.col1⟩

example {x y z : ℕ} (p : AwayCoordinateNormalForm x y z) :
    Nonempty (AwayCubicRoutingPacket x y z) :=
  nonempty_awayCubicRoutingPacket p

example {x y z : ℕ} (p : AwayValuationTransferPacket x y z)
    (mock : AwayDescentClosureProvider x y z p) :
    padicValNat 7 mock.nextRoute.carrier < padicValNat 7 p.carrier :=
  away_depth_descent_of_closureProvider p mock

example {x y z : ℕ} (p : AwayValuationTransferPacket x y z) :
    Nonempty (AwayClosureAuditResult x y z p) :=
  nonempty_awayClosureAuditResult_open p

example {x y z : ℕ} (hPack : CounterexamplePack x y z) :
    Nonempty (ClosureAuditCounterexampleRoute x y z) :=
  closureAuditCounterexampleRoute_of_pack hPack

#print axioms nonempty_coprimeTripleRouting
#print axioms nonempty_awayCubicRoutingPacket
#print axioms away_depth_descent_of_closureProvider
#print axioms nonempty_awayClosureAuditResult_open
#print axioms closureAuditCounterexampleRoute_of_pack
