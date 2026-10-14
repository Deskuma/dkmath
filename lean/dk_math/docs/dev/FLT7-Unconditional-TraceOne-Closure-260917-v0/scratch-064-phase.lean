import DkMath.FLT.Seven.SevenRealCubicCurrentCyclotomicPhase

namespace DkMath.FLT.Seven.SevenRealCubic

open SevenRealCubicInt

example {q : ℕ} [Fact (Nat.Prime q)]
    (r : (ZMod q)ˣ) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1)
    (x : ZMod q)
    (hroot : x ^ 3 - 2 * x ^ 2 - x + 1 = 0) :
    ∃ k : Fin 3, x = currentBeta r (k.val + 1) := by
  exact current_phase_alignment r hr7 hr1 hroot

example {q : ℕ} [Fact (Nat.Prime q)]
    (a : CurrentMuSevenResidueAddress q)
    (hroot : (a.evalReal alpha) ^ 3 - 2 * (a.evalReal alpha) ^ 2 -
        a.evalReal alpha + 1 = 0) :
    ∃ k : Fin 3, a.evalReal alpha = currentBeta a.ratio (k.val + 1) := by
  exact a.phase_alignment hroot

end DkMath.FLT.Seven.SevenRealCubic

#print axioms DkMath.FLT.Seven.SevenRealCubic.current_phase_alignment
#print axioms DkMath.FLT.Seven.SevenRealCubic.CurrentMuSevenResidueAddress.phase_alignment
