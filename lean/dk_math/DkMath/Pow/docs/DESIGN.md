# DkMath.Pow Design Specification

- Authors: D. and Wise Wolf
- Created: 2026-08-05
- Status: design specification before Lean implementation
- Conversation reachability key (`cid`): `6a721382-8e50-83ee-a3f3-b75e77a93476`

## 1. Design thesis

`DkMath.Pow` treats a power not only as an expression to rewrite, but as a presentation carrying structural information.

The ordinary equality

```text
N = x^d
```

contains three pieces of data:

```text
value      N
base       x
exponent   d
```

Mathlib already provides the algebra needed to manipulate these data. `DkMath.Pow` packages the relation into fibers and maps between fibers.

The central design principle is:

> Mathlib proves power laws. `DkMath.Pow` turns those laws into reusable structural operations.

## 2. Core vocabulary

## 2.1 Power value

A power value is the observed result `N`.

The generic theory does not assume that `N` has a unique root or a canonical root.

## 2.2 Power fiber

For a monoid `M`, exponent `d`, and value `N`, define:

```text
PowFiber d N = {x : M // x^d = N}
```

The fiber contains proof-carrying bases realizing `N` at exponent `d`.

This is intentionally different from:

- a multiset of polynomial roots;
- a chosen `nthRoot` function;
- a proposition asserting that a root exists.

`PowFiber` is a type of witnesses.

## 2.3 Root existence

```text
HasPowRoot d N = Nonempty (PowFiber d N)
```

This separates witness-carrying computation from propositional existence.

## 2.4 Power presentation

A power presentation contains both exponent and root witness.

```text
PowerPresentation N = Σ d : PNat, PowFiber d N
```

This makes it possible to place

```text
64 = 8^2 = 4^3 = 2^6
```

inside one same-value presentation space.

## 2.5 Fusion

Fusion combines powered states.

For equal exponent `d`:

```text
A = a^d
B = b^d
-----------------
A * B = (a * b)^d
```

At fiber level:

```text
PowFiber d A × PowFiber d B
  → PowFiber d (A * B)
```

## 2.6 Rebasing

Rebasing changes the exponent while preserving the value.

If `d = k * m`, then:

```text
N = x^d
  = (x^m)^k
```

At fiber level:

```text
PowFiber d N
  → PowFiber k N
```

The primitive API should use the explicit factorization witness `d = k * m`. A divisibility-based API is then derived.

## 2.7 Normalization

Normalization chooses or proves a preferred presentation.

Normalization is not part of the first core because the appropriate notion depends on the ambient type:

```text
ℕ / ℤ
  arithmetic integrality and factorization matter

ℝ≥0
  a canonical nonnegative root may exist

ℂ
  multiple roots form a root-of-unity orbit

general monoids
  no canonical root need exist
```

The initial package represents possibilities without choosing one globally.

## 3. Mathematical laws

## 3.1 Equal-exponent closure

For a commutative monoid:

```text
a^d * b^d = (a * b)^d
```

This is the closure law for fixed-exponent power fibers under multiplication.

## 3.2 Multiple fusion

Repeated use of fiber multiplication should later support finite products:

```text
∏ i, x_i^d = (∏ i, x_i)^d
```

A `Finset` or `Fintype` API may be added after the binary API stabilizes. It is not required for the initial milestone.

## 3.3 Mixed-exponent gcd preservation

For exponents `d` and `e`, let `g = gcd d e`.

Then:

```text
a^d * b^e
  = (a^(d/g) * b^(e/g))^g
```

This means fusion of different power levels preserves at least the common exponent `g`.

Important special cases:

```text
d = e
  full exponent is preserved

gcd d e = 1
  no nontrivial common exponent is guaranteed by exponent data alone
```

The actual product can still possess a higher power presentation because of arithmetic interaction between the bases. The theorem guarantees a presentation; it does not assert maximality.

## 3.4 Divisor rebasing

For `k ∣ d`:

```text
PowFiber d N → PowFiber k N
```

This induces a divisibility-directed family of maps among the fibers of a fixed value.

The exponent divisibility order points from finer exponent presentations toward coarser divisor exponents.

## 3.5 Square specialization

If `2 ∣ d`, every `d`-power witness yields a square witness.

This is the generic source of the DkMath reading called standard square-core normalization.

The generic theorem should not use that DkMath-specific name.

## 4. Relationship to Mathlib

## 4.1 Reused Mathlib concepts

Expected underlying APIs include:

```text
pow_zero
pow_succ
pow_add
pow_mul
mul_pow
map_pow
PNat
Nat.gcd
Nat.div_mul_cancel
IsSquare
Nat.nthRoot
Polynomial.nthRoots
rootsOfUnity
```

The exact import and theorem names must be confirmed in the active Mathlib version during implementation.

## 4.2 What must not be duplicated

`DkMath.Pow` should not introduce cosmetic copies such as:

```text
DkMath_pow_add
DkMath_pow_mul
DkMath_mul_pow
```

A wrapper is justified only when it:

- fixes a repeatedly useful orientation;
- packages a theorem into a typed map;
- joins several Mathlib facts into a reusable structural result;
- hides unstable low-level proof plumbing behind a stable public API.

## 4.3 Difference from root enumeration

`Polynomial.nthRoots` enumerates roots in an algebraic setting and requires stronger ring assumptions.

`PowFiber` merely records witnesses of `x^d = N` and therefore works under a minimal `Monoid` assumption.

These APIs are complementary rather than competing.

## 4.4 Difference from `IsSquare`

`IsSquare N` is propositional existence for exponent two.

`PowFiber 2 N` is the type of square-root witnesses.

The future API may provide bridges:

```text
Nonempty (PowFiber 2 N) ↔ IsSquare N
```

when the ambient multiplication conventions align. This is not required in the first checkpoint.

## 5. Typeclass design

## 5.1 `Monoid`

Sufficient for:

- defining powers;
- defining fibers;
- mapping fibers through monoid homomorphisms;
- rebasing one root witness.

## 5.2 `CommMonoid`

Sufficient for the simplest binary fusion API because Mathlib's unrestricted `mul_pow` uses commutativity.

A later noncommutative extension can accept:

```text
Commute a b
```

or package commuting witness conditions. That extension must not complicate the initial API.

## 5.3 Stronger algebraic structures

Cancellation, domains, fields, order, and unique factorization should appear only in specialized modules where required.

The core definition must not be specialized to `ℕ` merely because the first examples are natural numbers.

## 6. Edge cases

## 6.1 Exponent zero

For every base:

```text
x^0 = 1
```

Therefore:

```text
PowFiber 0 1
```

contains every base, while `PowFiber 0 N` is empty when `N ≠ 1` in ordinary nontrivial settings.

The fixed-exponent fiber should permit exponent zero because it is mathematically valid and keeps the definition general.

The all-exponent `PowerPresentation` should use positive exponents to avoid making the value `1` degenerate by construction.

## 6.2 Values zero and one

For natural numbers and many rings:

```text
0 = 0^d
1 = 1^d
```

for every positive exponent `d`.

Thus a maximal finite power depth does not exist for `0` and `1`.

Any future `Nat.powerDepth` design must either:

- return `WithTop ℕ`;
- restrict its domain to `2 ≤ n`;
- or encode the exceptional cases explicitly.

## 6.3 Nonunique roots

The theory must not assume root uniqueness.

Examples include:

- even powers over ordered rings with positive and negative roots;
- complex roots differing by roots of unity;
- rings with zero divisors.

Fiber language is chosen precisely because it preserves this multiplicity.

## 6.4 Empty fibers

`PowFiber d N` may be empty.

Operations should either consume explicit witnesses or state existence assumptions. They should not silently invoke classical choice to manufacture a root.

## 7. Equality and extensionality

Because `PowFiber` is a subtype, equality of witnesses is usually equality of underlying bases; the proof components are propositions.

A later theorem may expose:

```lean
@[ext]
theorem PowFiber.ext ...
```

but only if the automatically available subtype extensionality is not ergonomic enough.

Avoid unnecessary custom equality infrastructure.

## 8. Mapping and functorial behavior

For a monoid homomorphism `f`:

```text
x ∈ PowFiber d N
----------------------
f(x) ∈ PowFiber d f(N)
```

Expected laws:

```text
PowFiber.map id = id
PowFiber.map (g.comp f) = PowFiber.map g ∘ PowFiber.map f
PowFiber.map f (x.mul y) = (x.map f).mul (y.map f)
```

These functorial laws can be introduced after the basic `map` and `mul` definitions stabilize.

They are important for eventual transport between concrete number systems and abstract algebraic models.

## 9. Fiber organization by exponent

For a fixed value `N`, the family

```text
d ↦ PowFiber d N
```

is indexed by natural exponents.

Divisibility creates rebase maps:

```text
k ∣ d
PowFiber d N → PowFiber k N
```

This suggests a diagram over the divisibility preorder.

The initial implementation should not prematurely encode category-theoretic machinery. First establish the maps and their laws:

```text
rebase along reflexivity = identity
rebase along transitivity = composition
```

Only then decide whether a functorial abstraction adds practical value.

## 10. Same-value presentation space and PowerSwap

`DkMath.PowerSwap` studies equality between power expressions, including base-exponent exchanges and normal forms.

`DkMath.Pow` supplies the underlying presentation language.

```text
DkMath.Pow
  asks: which base-exponent witnesses realize N?

DkMath.PowerSwap
  asks: how are distinct presentations related or exchanged?
```

The intended bridge is:

```text
PowerPresentation N
  ↓ relation or transformation
PowerSwap / Exchange / NormalForm
```

Existing `DkMath.PowerSwap.NormalForm` must be audited before introducing a new `PowNormalForm` to avoid two competing normal-form theories.

## 11. DkMath interpretation layer

The generic package should remain ordinary mathematical API.

DkMath-specific terminology belongs in bridge documentation or aliases:

```text
PowFiber
  DkMath reading: true-core fiber

PowFiber.mul
  DkMath reading: true-core fusion

PowFiber.rebase
  DkMath reading: standard-core normalization

PowerPresentation
  DkMath reading: same-value power universe
```

The distinction allows the public mathematical surface to remain understandable without requiring CosmicFormula vocabulary, while preserving the research interpretation above it.

## 12. Future `DkMathlib` boundary

The long-term package split is:

```text
Lean
  ↓
Mathlib
  ↓
DkMathlib
  reusable structural mathematics
  ↓
DkMath
  research programs and bridges
```

The initial implementation remains in `DkMath.Pow` to mature inside the current repository.

Extraction readiness requires:

1. generic imports only;
2. stable names and docstrings;
3. use by multiple independent modules;
4. no research-specific assumptions in the core;
5. examples demonstrating general utility;
6. a clean aggregator and dependency graph.

After extraction, compatibility can be maintained by re-exporting `DkMathlib.Pow` from `DkMath.Pow` and retaining DkMath-specific bridges in the DkMath repository.

## 13. Naming policy

Preferred names:

```text
PowFiber
HasPowRoot
PowerPresentation
PowFiber.mul
PowFiber.map
PowFiber.rebase
sameExponentFusion
gcdExponentFusion
```

Avoid in the generic layer:

```text
TrueMagicCore
MagicCoreFusion
CosmicPowerWorld
StandardMagicCore
```

Those names may exist only as interpretive aliases in a CosmicFormula bridge if they prove useful.

Use uppercase module namespace `Pow`, following Lean and repository conventions.

## 14. Notation policy

No custom notation in the initial implementation.

A future scoped notation such as a compact fiber display may be considered only after real caller experience shows that the standard name is too verbose.

Any notation must be placed behind:

```lean
open scoped DkMath.Pow
```

and must not alter global parsing behavior.

## 15. Documentation and provenance policy

Each implementation report and major handoff should retain:

```text
cid: 6a721382-8e50-83ee-a3f3-b75e77a93476
```

This is the reachability key for the discussion that introduced:

- fixed-exponent true-core fusion;
- power fibers rather than a single selected root;
- gcd-exponent fusion;
- square-core rebasing;
- the future `Mathlib + DkMathlib` public architecture.

The key is provenance, not a Lean dependency.

## 16. Design boundary summary

The package begins with a deliberately small claim:

```text
power equality witnesses form fibers,
and Mathlib power laws induce maps between those fibers.
```

From that claim, the initial structural API follows:

```text
fiber
  → map
  → equal-exponent fusion
  → divisor rebasing
  → gcd-exponent fusion
  → same-value presentations
```

Normal forms, maximal depth, roots of unity, and research interpretations are later layers.

## 17. Provenance

Reachability key:

```text
cid: 6a721382-8e50-83ee-a3f3-b75e77a93476
```

This design specification should remain the reference boundary for the first `DkMath.Pow` implementation campaign.