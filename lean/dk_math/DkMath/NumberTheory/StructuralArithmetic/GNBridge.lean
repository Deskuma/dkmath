/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Five.GN5
import DkMath.NumberTheory.PrimitiveBeam
import DkMath.NumberTheory.StructuralArithmetic.FinitePrimeEscapeBridge

#print "file: DkMath.NumberTheory.StructuralArithmetic.GNBridge"

/-!
## Generic GN and FLT5 structural bridge

This module connects existing arithmetic providers to the raw
StructuralArithmetic direction vocabulary.  A PrimitiveBeam witness gives a
prime divisor of the generic GN factor; an explicit absence from the known
finite scale set then makes it a `FreshPrimeDirection` and hence proves
non-generation.  The degree argument of GN is kept distinct from any
PowerGauge observation period.

The degree-five equality with `FLT.Five.GN5` is an exact kernel identity.  It
does not identify degree five with additive congruence modulo five or with
PowerGauge period five.
-/

namespace DkMath.NumberTheory.StructuralArithmetic

open DkMath.NumberTheory.PrimitiveBeam

/--
An existing PrimitiveBeam prime factor of `(x + u)^d - u^d` becomes a fresh
StructuralArithmetic direction for the generic GN target when it is absent
from the explicitly supplied known scale set `S`.
-/
theorem freshPrimeDirection_GN_of_primitivePrimeFactor
    {S : Finset ℕ} {q x u d : ℕ}
    (hq : PrimitivePrimeFactorOfDiffPow q (x + u) u d)
    (hd : 0 < d) (hd1 : 1 < d) (hqS : q ∉ S) :
    FreshPrimeDirection S (DkMath.CosmicFormulaBinom.GN d x u) q := by
  have hqGN : q ∣ DkMath.CosmicFormulaBinom.GN d x u :=
    primitive_prime_dvd_GN_body hq hd hd1
  exact freshPrimeDirection_of_prime_dvd_not_mem hq.1 hqGN hqS

/-- The generic GN fresh-direction bridge immediately proves non-generation. -/
theorem not_primeScaleGeneratedBy_GN_of_primitivePrimeFactor
    {S : Finset ℕ} {q x u d : ℕ}
    (hq : PrimitivePrimeFactorOfDiffPow q (x + u) u d)
    (hd : 0 < d) (hd1 : 1 < d) (hqS : q ∉ S) :
    ¬ PrimeScaleGeneratedBy S (DkMath.CosmicFormulaBinom.GN d x u) :=
  not_primeScaleGeneratedBy_of_freshPrimeDirection
    (freshPrimeDirection_GN_of_primitivePrimeFactor hq hd hd1 hqS)

/--
The explicit FLT5 polynomial is the generic natural-number GN at degree five.
The numeral `5` here is the Cosmic Formula degree, not a PowerGauge period.
-/
theorem GN5_eq_generic_GN (g y : ℕ) :
    DkMath.FLT.Five.GN5 g y = DkMath.CosmicFormulaBinom.GN 5 g y := by
  norm_num [DkMath.FLT.Five.GN5, DkMath.CosmicFormulaBinom.GN,
    DkMath.CosmicFormula.GN, DkMath.CosmicFormula.GTail,
    DkMath.CosmicFormula.d1k, DkMath.CosmicFormula.d_sub_one_k,
    DkMath.CosmicFormula.d_sub_n_k, Finset.sum_range_succ, Nat.choose] ; ring

/-- The existing generic GN5 escape witness rewritten to the explicit FLT5 GN5. -/
theorem GN5_one_one_has_freshPrimeDirection :
    ∃ q,
      FreshPrimeDirection
        ({2, 3, 5} : Finset ℕ)
        (DkMath.FLT.Five.GN5 1 1) q := by
  rw [GN5_eq_generic_GN]
  exact GN5_escape_has_freshPrimeDirection

/--
The existing `{2, 3, 5}` finite escape proves non-generation for the explicit
FLT5 `GN5 1 1` target by rewriting through the exact degree-five identity.
-/
theorem GN5_one_one_not_primeScaleGeneratedBy_two_three_five :
    ¬ PrimeScaleGeneratedBy
      ({2, 3, 5} : Finset ℕ)
      (DkMath.FLT.Five.GN5 1 1) := by
  rw [GN5_eq_generic_GN]
  exact GN5_escape_not_primeScaleGeneratedBy_two_three_five

end DkMath.NumberTheory.StructuralArithmetic
