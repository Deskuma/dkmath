/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.PrimeQuadraticDiscriminant
import DkMath.NumberTheory.TraceOneDiscriminantAxis

#print "file: DkMath.NumberTheory.TraceOnePrimeDiscriminant"

namespace DkMath.NumberTheory.TraceOneQuadratic

open DkMath.NumberTheory.PrimeQuadraticDiscriminant

/-! The signed-prime parameter as the generic prime-discriminant packet. -/

/-- The signed-prime TraceOne parameter satisfies the generic prime packet
interface used by the axis and ideal kernels. -/
theorem signedPrimeDiscriminantPacket
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    PrimeDiscriminantPacket p (signedPrimeParameter p) :=
  { prime := hp
    discr_natAbs := by
      rw [discr_signedPrimeParameter hp hp2]
      exact signedPrimeDiscriminant_natAbs p }

end DkMath.NumberTheory.TraceOneQuadratic
