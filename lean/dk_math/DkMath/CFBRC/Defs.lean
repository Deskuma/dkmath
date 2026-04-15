/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.CosmicFormulaBinom

#print "file: DkMath.CFBRC.Defs"

namespace DkMath.CFBRC

open scoped BigOperators

open DkMath.CosmicFormulaBinom

/--
prime case の shifted homogeneous cyclotomic core:
`∑_{k=0}^{p-1} (x+u)^k * u^(p-1-k)`.
-/
@[simp] def cyclotomicPrimeCore {R : Type _} [CommSemiring R]
    (p : ℕ) (x u : R) : R :=
  ∑ k ∈ Finset.range p, (x + u) ^ k * u ^ (p - 1 - k)

end DkMath.CFBRC
