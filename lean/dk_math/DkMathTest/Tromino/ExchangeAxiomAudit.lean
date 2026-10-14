/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.Exchange

#print "file: DkMathTest.Tromino.ExchangeAxiomAudit"

namespace DkMathTest.Tromino.ExchangeAxiomAudit

open DkMath.Tromino

example : Nat.card TrominoState = 4 := card_state

example (x : TrominoState) : (waitingStates x).card = 3 :=
  card_waitingStates x

example (x : TrominoState) : exchange 0 x = x :=
  exchange_zero x

example (delta x : TrominoState) :
    exchange delta (exchange delta x) = x :=
  exchange_self_inverse delta x

example (alpha beta x : TrominoState) :
    exchange alpha (exchange beta x) = exchange (alpha + beta) x :=
  exchange_comp alpha beta x

example (alpha beta x : TrominoState) :
    exchange alpha (exchange beta x) = exchange beta (exchange alpha x) :=
  exchange_commute alpha beta x

example {x y : TrominoState} (hxy : x ≠ y) :
    ∃! delta, delta ≠ 0 ∧ exchange delta x = y :=
  existsUnique_nonzero_exchange_to hxy

example :
    Finset.filter (fun x : TrominoState => x ≠ 0) Finset.univ =
      waitingStates 0 :=
  nonzeroStates_eq_waitingStates_zero

#print axioms DkMath.Tromino.card_state
#print axioms DkMath.Tromino.card_waitingStates
#print axioms DkMath.Tromino.exchange_self_inverse
#print axioms DkMath.Tromino.exchange_comp
#print axioms DkMath.Tromino.exchange_commute
#print axioms DkMath.Tromino.existsUnique_nonzero_exchange_to

end DkMathTest.Tromino.ExchangeAxiomAudit
