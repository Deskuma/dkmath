# FLGNB FermatLittleGNBridge Summary

## Position

`FLGNB-FermatLittleGNBridge-Discussion.md` records the point where the
Pascal/Beam/GN route meets Fermat's little theorem.

The implemented result is not a new proof of Fermat's little theorem.  The
Lean implementation uses the Mathlib theorem:

```lean
Nat.ModEq.pow_card_sub_one_eq_one
```

The DkMath contribution is the bridge that carries the existing Beam / `GTail`
/ `GN` structure to the classical endpoint.

## Current Implemented Endpoint

The important theorem chain is:

```text
Pascal prime row
  -> inner coefficients are divisible by p
  -> weighted one-gap GTail inner Beam is divisible by p
  -> GN p x u = inner Beam + x^(p-1)
  -> GN p x u ≡ x^(p-1) [MOD p]
  -> p ∤ x implies x^(p-1) ≡ 1 [MOD p]
  -> GN p x u ≡ 1 [MOD p]
  -> p ∤ GN p x u
```

Core Lean file:

```text
DkMath.NumberTheory.WeightedGNBridge
```

Core theorem names:

```lean
theorem prime_GN_modEq_rightBoundary
theorem prime_GN_modEq_one_of_not_dvd_x
theorem prime_not_dvd_GN_of_not_dvd_x
```

The endpoint is:

```lean
theorem prime_not_dvd_GN_of_not_dvd_x
    {p x u : Nat} (hp : p.Prime) (hx : ¬ p ∣ x) :
    ¬ p ∣ GN p x u
```

Mathematically:

```text
if p is prime and p does not divide x,
then p does not divide GN(p, x, u).
```

## Conceptual Meaning

The discussion identifies the following principle:

```text
The inner Beam sinks modulo p.
The right boundary remains.
If the boundary axis is a p-unit, Fermat's little theorem reads the boundary as 1.
Therefore GN is not divisible by p.
```

In formula form:

```text
GN(p, x, u) = p * B + x^(p-1)
```

and if `p ∤ x`, then:

```text
GN(p, x, u) ≡ x^(p-1) ≡ 1 [MOD p]
```

This matters because it separates the row prime `p` from primitive primes that
may appear in the `GN` factor.  It is a guardrail against mixing:

```text
row prime p
primitive prime q
```

In the difference-power factorization:

```text
a^p - b^p = (a - b) * GN p (a - b) b
```

the bridge reads:

```text
p ∤ (a - b)  ->  p ∤ GN p (a - b) b
```

This is directly useful for future `PrimitiveBeam`, `Zsigmondy`, and gcd-control
work.

## Fermat Little Theorem As A Boundary Principle

The discussion reframes Fermat's little theorem through `GN`.

Classically:

```text
p prime and p ∤ x  ->  x^(p-1) ≡ 1 [MOD p]
```

GN interpretation:

```text
x^(p-1) is not an arbitrary exponent.
It is the right-boundary term left after the prime-row inner Beam vanishes.
```

Thus Fermat's little theorem becomes:

```text
The remaining GN right boundary returns to the unit 1
by the permutation symmetry of the nonzero residues modulo p.
```

This gives a principle-level explanation:

```text
Pascal Beam cancellation
  + boundary residue
  + nonzero residue permutation symmetry
  = Fermat boundary unit return
```

The exponent `p - 1` has two simultaneous meanings:

```text
1. the size of the nonzero residue world modulo p;
2. the right-boundary degree of the p-th GN difference kernel.
```

## GN Should Be The Main Subject

The discussion then reverses the usual direction.

Traditional view:

```text
Pascal triangle
  -> binomial coefficients
  -> GN / Tail
```

DkMath view:

```text
GN / difference kernel
  -> natural-number expansion
  -> Pascal triangle
```

The proposed hierarchy is:

```text
Level 0: difference kernel
  (x + u)^d - u^d

Level 1: GN normalization
  ((x + u)^d - u^d) / x

Level 2: natural-number expansion
  binomial coefficients appear

Level 3: Pascal triangle
  coefficient table C(d,k)

Level 4: prime-row observation
  inner coefficients vanish modulo p

Level 5: GN boundary residue
  GN(p,x,u) ≡ x^(p-1) [MOD p]

Level 6: Fermat boundary unit return
  p ∤ x -> x^(p-1) ≡ 1 [MOD p]
```

This is a major design point:

```text
Pascal triangle is the natural-number coefficient section of the GN difference kernel.
```

With this direction, Gamma-function completion is not the first move.  Real or
analytic generalization can start from the difference kernel itself.

## Dynamic Pascal And Conservation View

The discussion proposes lifting the static theorem to a dynamic reading of
Pascal rows.

Static prime-row principle:

```text
GN(p,x,u) = p * B + x^(p-1)
```

Dynamic principle to extract:

```text
boundary
inner Beam
normalization
vanishing
remaining boundary
unit return
```

Pascal recurrence:

```text
C(n+1,k) = C(n,k-1) + C(n,k)
```

is read as a local flow or conservation law.  A normalized row:

```text
mu_n(k) = C(n,k) / 2^n
```

has total mass `1`, while `padicValNat p (C(n,k))` tracks prime-channel height.

The target abstraction suggested by the discussion is:

```text
Dynamic Boundary-Beam Residue Principle
```

or:

```text
Pascal Beam Conservation Principle
```

The core claim to test is:

```text
In suitable observation systems, inner Beam mass can vanish,
while boundary residue remains and may normalize to a unit.
```

## Analysis Direction: Use Existing GN / powerKernel Lemmas

The discussion explicitly recommends not starting with Gamma-completed Pascal
rows.  Instead, use the existing GN and derivative-kernel infrastructure.

Existing names mentioned:

```lean
powerKernel_eq_GN_swap
sub_pow_eq_u_mul_powerKernel
cosmicKernel_pow_eq_powerKernel_of_ne_zero
continuous_powerKernel
powerKernel_zero
tendsto_powerKernel_zero
tendsto_powerKernel_zero_punctured
```

The intended route is:

```text
WeightedGNBridge:
  prime-row boundary residue

CosmicDerivativePower / powerKernel:
  real/analytic difference-kernel behavior

tendsto_powerKernel_zero:
  derivative limit
```

Interpretation:

```text
Pascal is a discrete natural-number section.
GN is the difference kernel.
powerKernel is the analysis bridge.
The derivative limit is the continuous shadow of the Beam/kernel structure.
```

Gamma completion remains useful later, but it is not the first route.

## Gamma Avoidance And Relative Polygon Numbers

The discussion notes that if Pascal rows are generalized directly, Gamma
functions appear:

```text
n! -> Gamma(n+1)
```

But if GN is primary, the starting point is:

```text
GN_R(d,x,u) = ((x + u)^d - u^d) / x
```

No factorial is needed at this level.

This motivates the relative polygon number viewpoint:

```text
factorial:
  completed ordering structure

binomial coefficient:
  relative split count of a completed structure

Pascal triangle:
  integer-lattice coefficient section of GN

GN:
  difference kernel / layer-generation kernel
```

This suggests that Gamma is one possible completion of coefficient sections, but
DkMath can instead generalize the generation structure before factorials appear.

## Petal / Relative Polygon Inventory Needed

The discussion concludes that before pushing deeper into real/Gamma analysis,
the Petal and relative polygon tools should be inventoried.

Existing families mentioned:

```text
DkMath.UnitCycle.RelPolygon
DkMath.FLT.PetalCoreUnit
DkMath.FLT.PetalDetect
DkMath.FLT.CosmicPetalBridge
```

Important existing connection:

```text
GN(3, c - b, b) = S0_nat(c,b)
```

Representative Lean names mentioned:

```lean
RPState
g
T
I
S0
S1
S0_nat
S1_nat
diff_kernel
GN_three_sub_eq_S0_nat
prime_dvd_S0_via_cosmic_bridge
```

The key warning is that these pieces are spread across several files and do not
yet have a unified API.

Recommended next documentation or bridge target:

```text
DkMath.FLT.PetalGNBridge
```

or an inventory document such as:

```text
DkMath/FLT/docs/PetalGNInventory.md
```

## Immediate Next Implementation Candidates

The discussion suggests a conservative next step: do not jump to Gamma or full
dynamic Pascal yet.  First fix the Petal/GN bridge inventory.

Candidate wrapper:

```lean
theorem S0_nat_eq_GN_three_of_sub
    {c b : Nat} (hbc : b < c) :
    S0_nat c b = GN 3 (c - b) b
```

Candidate Fermat-GN-to-Petal specialization:

```lean
theorem three_not_dvd_S0_nat_of_not_dvd_sub
    {c b : Nat} (hbc : b < c) (h3 : ¬ 3 ∣ c - b) :
    ¬ 3 ∣ S0_nat c b
```

Reason:

```text
prime_not_dvd_GN_of_not_dvd_x
  with p = 3
  plus GN_three_sub_eq_S0_nat
```

This would move the new `WeightedGNBridge` endpoint into the Petal `S0` world.

## Recommended Next Step

The clean next checkpoint is:

```text
Petal / RelPolygon / GN inventory
```

Then:

```text
1. Add thin PetalGNBridge wrappers.
2. Prove the p = 3 S0 non-divisibility bridge.
3. Only after that, return to dynamic Pascal / GN analysis.
```

This keeps the project aligned with the new main direction:

```text
GN -> Pascal
GN -> Petal
GN -> RelPolygon
```

instead of treating Pascal, Petal, and relative polygon numbers as separate
starting points.
