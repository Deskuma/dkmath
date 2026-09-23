# Review-002 — GAGE-002 prime-power purity detector

Result: APPROVED — Outcome A

## 1. Judgment

GAGE-002 correctly closes the reverse Pascal-support direction for nontrivial rows.

The implementation is mathematically and architecturally aligned with the campaign:

- it reuses the pinned Mathlib Lucas converse;
- it preserves the same support prime p in the resulting prime-power witness;
- it makes the 1 < n boundary explicit;
- it exposes the Pascal interior gcd as a row-level prime-power purity detector;
- it does not duplicate Lucas/Kummer arithmetic.

No review change is required before GAGE-003.

## 2. Reverse theorem boundary

The key theorem has the correct shape:

~~~text
1 < n
InnerRowSupportPrime n p
-------------------------
exists e > 0, n = p^e
~~~

The explicit 1 < n hypothesis is essential because rows n = 0 and n = 1 have no interior coefficients and the support predicate is vacuous there.

The implementation correctly proves positivity of the canonical multiplicity exponent instead of choosing an unrelated witness.

## 3. Purity detector

The new quantity:

~~~text
exponentGaugeInteriorGCD n
  = gcd { choose n k | 1 <= k <= n-1 }
~~~

is a thin wrapper over the pinned Mathlib row gcd.

The two wrappers:

~~~text
prime-power row     -> interior gcd = minFac n
non-prime-power row -> interior gcd = 1
~~~

are sufficient for the v0 detector surface. An extra iff theorem was not necessary at this checkpoint.

## 4. Important design information for GAGE-003

The intended value-side gauge is already latent in the existing StructuralArithmetic modules.

Existing production definitions:

~~~text
DkMath.NumberTheory.StructuralArithmetic.projectExponent d v
  = v % d

DkMath.NumberTheory.StructuralArithmetic.primeExponentCoordinates a
  = (p |-> padicValNat p a)

DkMath.NumberTheory.StructuralArithmetic.projectPrimeCoordinates d a
  = (p |-> padicValNat p a % d)
~~~

and existing theorem:

~~~text
projectPrimeCoordinates_mul_pow
  projectPrimeCoordinates d (n * a^d)
    = projectPrimeCoordinates d n
~~~

show that the planned ValueGauge should be a semantic bridge over this existing implementation, not a competing definition.

This is the point where the earlier separation from StructuralArithmetic.PowerGauge becomes an explicit, proved connection: the exponent-side Pascal Gauge remains distinct, while the value-side Gauge is legitimately implemented by the existing prime-coordinate period projection.

## 5. Next checkpoint

Proceed to instruction-003.md.

GAGE-003 should expose value-side residue/coordinate vocabulary, prove exact compatibility with StructuralArithmetic, and show that nonzero n-th powers land in the zero residue sector. It should not attempt general additive landing or FLT.