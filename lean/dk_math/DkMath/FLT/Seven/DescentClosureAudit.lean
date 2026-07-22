/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.CoprimeTripleRouting

#print "file: DkMath.FLT.Seven.DescentClosureAudit"

namespace DkMath.FLT.Seven

/-- The additional data needed to turn the away depth drop into a recursive
FLT7 step.  In particular, the smaller carrier must occur in a newly
constructed primitive counterexample; it is not enough to exhibit a smaller
natural number. -/
structure AwayDescentClosureProvider
    (x y z : ℕ) (p : AwayValuationTransferPacket x y z) : Type where
  nextX : ℕ
  nextY : ℕ
  nextZ : ℕ
  nextPack : CounterexamplePack nextX nextY nextZ
  nextRoute : AwayValuationTransferPacket nextX nextY nextZ
  carrier_match : nextRoute.carrier = Int.natAbs p.normal.root.snd

theorem away_depth_descent_of_closureProvider {x y z : ℕ}
    (p : AwayValuationTransferPacket x y z)
    (c : AwayDescentClosureProvider x y z p) :
    padicValNat 7 c.nextRoute.carrier < padicValNat 7 p.carrier := by
  rw [c.carrier_match]
  exact p.root_snd_depth_lt_carrier

/-- A formal description of the reconstruction statement not supplied by the
cubic product and its routing grid.  This record stores the proposition itself,
not a proof of it, so it does not assert that reconstruction is impossible. -/
structure MissingClosureProviderStatement
    (x y z : ℕ) (p : AwayValuationTransferPacket x y z)
    (_routing : AwayCubicRoutingPacket x y z) : Type where
  targetCarrier : ℕ
  targetCarrier_eq : targetCarrier = Int.natAbs p.normal.root.snd
  reconstructionObligation : Prop
  reconstructionObligation_eq :
    reconstructionObligation = Nonempty (AwayDescentClosureProvider x y z p)

def missingClosureProviderStatement {x y z : ℕ}
    (p : AwayValuationTransferPacket x y z)
    (routing : AwayCubicRoutingPacket x y z) :
    MissingClosureProviderStatement x y z p routing where
  targetCarrier := Int.natAbs p.normal.root.snd
  targetCarrier_eq := rfl
  reconstructionObligation := Nonempty (AwayDescentClosureProvider x y z p)
  reconstructionObligation_eq := rfl

inductive AwayClosureAuditResult
    (x y z : ℕ) (p : AwayValuationTransferPacket x y z) : Type
  | closed (provider : AwayDescentClosureProvider x y z p)
  | open (routing : AwayCubicRoutingPacket x y z)
      (missing : MissingClosureProviderStatement x y z p routing)

/-- The APIs through FLT7-012 produce the routing grid and expose, but do not
inhabit, the remaining reconstruction obligation. -/
theorem nonempty_awayClosureAuditResult_open {x y z : ℕ}
    (p : AwayValuationTransferPacket x y z) :
    Nonempty (AwayClosureAuditResult x y z p) := by
  rcases nonempty_awayCubicRoutingPacket p.normal with ⟨routing⟩
  exact ⟨.open routing (missingClosureProviderStatement p routing)⟩

inductive ClosureAuditCounterexampleRoute (x y z : ℕ) : Type
  | ramified (packet : RamifiedCoordinateNormalForm x y z)
  | awayClosed (packet : AwayValuationTransferPacket x y z)
      (provider : AwayDescentClosureProvider x y z packet)
  | awayOpen (packet : AwayCubicRoutingPacket x y z)

/-- Every primitive counterexample reaches the ramified branch or the explicit
away routing grid.  No closure provider is selected or fabricated here. -/
theorem closureAuditCounterexampleRoute_of_pack {x y z : ℕ}
    (hPack : CounterexamplePack x y z) :
    Nonempty (ClosureAuditCounterexampleRoute x y z) := by
  rcases coordinateCounterexampleRoute_of_pack hPack with ⟨route⟩
  cases route with
  | ramified p => exact ⟨.ramified p⟩
  | away p =>
      rcases nonempty_awayCubicRoutingPacket p with ⟨routing⟩
      exact ⟨.awayOpen routing⟩

end DkMath.FLT.Seven
