# DkMath.Lib

## 1. Purpose

`DkMath.Lib.*` is the reusable intermediate layer extracted from DkMath research code.

Its purpose is to separate **neutral mathematical kernels** from theorem-owner-specific experiments such as FLT, ABC, RH, Goldbach, or one fixed GN degree.

Recommended public development import for the current aggregator-exposed subset:

```lean
import DkMath.Lib
```

`DkMath.Lib.lean` intentionally exposes a promoted subset without importing the whole experimental DkMath workspace. Some neutral modules in this directory are currently direct-import APIs and are not yet listed by the aggregator.

For GN and completion arithmetic, use the narrower public entry:

```lean
import DkMath.Lib.Cosmic.Completion
```

It directly imports the owners of GN basics, completion arithmetic and deficits,
divisibility, primitive additive triples, and prime addresses. It does not import
the `DkMath.Lib` aggregator or application consumers. Existing theorem namespaces
and hypotheses remain unchanged.

The Completion entry also exposes `NumberTheory.PerfectPowerValuation` and
`NumberTheory.PrimePowerCompensation`: a nonzero perfect-power valuation criterion,
and a construction at y=1 that completes all primes in a finite set locally while
producing an outside prime with an exponent obstruction. `NumberTheory.PrimePowerCompensationShift` extends this to a positive lower coordinate y.
Primitive coordinates suffice for the exact local valuations (zero at primes of y,
p at the remaining controlled primes). An explicit power-gap size hypothesis is
required for the outside prime with an exponent obstruction. `NumberTheory.PrimePowerCompensationLift` explicitly selects the extra factor
T=(p M₀ y)y^p+1, preserves the controlled valuations, and attains this hypothesis.
For every finite control set it constructs a primitive nonpower with the stated
local valuations, retaining the odd-prime and p∤y hypotheses. The constructed
upper coordinate and residual depend on the control set. This is a special
construction, not an FLT descent.

The intended flow is:

```text
research owner
  -> repeated useful structure
  -> remove owner-specific assumptions / names
  -> DkMath.Lib.*
  -> reuse from later owners
```

## 1.1 Aggregator coverage in this snapshot

`DkMath.Lib.lean` currently imports the following promoted families directly:

```text
NumberTheory.FiniteIdealPowerAggregation
Basic
Algebra.BinomTail
Algebra.SquareCompletion
Algebra.PowerSubgroup
TwoChannel
NumberTheory.PadicValNat
NumberTheory.BinomialPrimePower
NumberTheory.PowerDifferenceCofactorGcd
NumberTheory.PowerDifferenceCofactorValuation
NumberTheory.CompletionDefectGcd
NumberTheory.PrimeRatioOrder
NumberTheory.CyclotomicAddress
NumberTheory.CyclotomicLayerValuation
NumberTheory.PowerDifferenceCofactorPrimeAddress
NumberTheory.HomogeneousCyclotomic
NumberTheory.HomogeneousCyclotomicAddress
NumberTheory.HomogeneousCyclotomicBoundary
NumberTheory.HomogeneousCyclotomicPrimeAddress
NumberTheory.HomogeneousPowerQuotient
NumberTheory.ClassGroupTorsionBridge
NumberTheory.TraceOneLatticeLanding
NumberTheory.FiniteFreeLatticeLanding
NumberTheory.QuadraticResidueType
NumberTheory.PolynomialHenselDigit
NumberTheory.TraceOnePowerLanding
NumberTheory.EisensteinCoordinates
NumberTheory.EisensteinLatticeLanding
NumberTheory.SquarefreePowerFactor
Cosmic.Completion
Cosmic.GTail
Cosmic.CompletionCoprime
Cosmic.PowerDifferenceCofactor
Cosmic.CompletionDefect
Cosmic.PowerDifferenceCofactorArithmetic
NumberTheory.PowerDifferenceCofactorStrongDivisibility
Cosmic.CompletionLoan
Cosmic.GNProductDegree
Cosmic.CyclicDeterminant
Cosmic.GTailCyclotomic
Cosmic.GTailPascal
Cosmic.GTailBoundary
Cosmic.GTailNat
Cosmic.GTailCongruence
Cosmic.GTailPadic
Cosmic.GTailSelection
Cosmic.GTailFactor
Cosmic.GTailTransport
Cosmic.GTailSeven
Cosmic.GTailSevenArithmetic
```

The following neutral modules exist under `DkMath.Lib.NumberTheory` and are used by current research through direct imports, but are not directly listed by `DkMath.Lib.lean` in this snapshot:

```text
PowerFactor
IdealPowerFactor
PrincipalIdealPower
UnitPowerSector
```

`IdealPowerFactor` is already transitively reachable through the current aggregator; the other three remain direct-import APIs. This distinguishes direct listing from transitive exposure, not mathematical reusability.

## 2. Cosmic family: `GTail`

The main promoted cosmic/binomial kernel is `GTail`.

For a commutative semiring, `GTail d r x u` is defined so that

$$
\begin{aligned}
(x+u)^d &\;=\; \sum_{j<r}\binom dj x^j u^{d-j}\\
&\qquad +x^r\operatorname{GTail}(d,r,x,u).
\end{aligned}
$$

The standard gap-normalized `GN` layer is the $r=1$ specialization:

$$
GN_d(x,u)=\operatorname{GTail}(d,1,x,u).
$$

This is the main abstraction shift behind the `[GNZC]` promotion work: new neutral code should use the `GTail` theorem family when the statement is not intrinsically tied to a legacy `GN` surface.

### `DkMath.Lib.Cosmic.GTail`

Core decomposition and recursion.

Representative APIs:

```text
add_pow_eq_prefix_add_xpow_mul_GTail
higher_tail_eq_pow_mul_GTail
add_pow_eq_mul_GTail_one_add_gap
GTail_rec
GN_tail_rec
GN_tail_decomposition
GTail_eval_zero
GN_zero_eval
```

### `PowerDifferenceCofactor`, `CompletionDefect`

The division-free geometric cofactor `powerDifferenceCofactor n x y` (R_n)
includes the diagonal x=y and degree zero. It connects to GTail at gap x-y
in rings; the natural subtraction bridge explicitly requires y≤x.
The cancellation-free recurrence is `R_(k+2)+xy R_k=(x+y)R_(k+1)`.

Over naturals, `R_n≤(x+y)^(n-1)` makes `completionDefect` an exact deficit.
It satisfies `D_(k+3)=(x+y)D_(k+2)+xy R_(k+1)` and is positive for n≥3
when both coordinates are positive. `signedCompletionDefect` is the separate
ring version. A cofactor can still be a square or cube with another base.

### `PowerDifferenceCofactorArithmetic`, `CompletionLoan`

The cofactor addition and degree-product identities hold in every commutative
semiring. In particular `R_(2m)=(x+y)R_m(x²,y²)` and the odd borrowed sum has
an `(x+y)²` factor. Changing the bases is explicit and does not prove height descent.

For primitive natural coordinates the exact common factor of `R_n` and
`xy R_(n-2)` is 1 in odd degrees and x+y in even degrees (n≥2).
`CompletionLoan` divides all three numerators in
`R_n+xy R_(n-2)=(x+y)R_(n-1)` by that factor, proves exact reconstruction,
and for n≥3 and positive primitive coordinates constructs positive pairwise
coprime entries A+B=C. This is an additive triple, without an ABC radical bound.

### `GTailSelection`, `GTailFactor`, `GTailTransport`

These three modules are explicitly promoted through `import DkMath.Lib`.
Term index k is the exponent of x in `(choose d k : R) * x^k * u^(d-k)`.
Body sums selected active indices in `S ∩ range(d+1)`; Gap sums the other
indices in `range(d+1)`. Thus `(x+u)^d = selectedGap + selectedBody` in a
CommSemiring, including empty selections and zero coordinates.

Active lower/upper bounds i,j extract the forced monomial
`x^i * u^(d-j)` with an explicit residual. The active min/max adapter requires
a nonempty active set. This factor need not be the maximal evaluated factor.
`coeffGCD` is the gcd of selected Pascal coefficients, distinct from the gcd
of evaluated term values. Interior prime rows have coefficient gcd p and a
joint `p*x*u` divisor. Endpoint insertion can change coefficient content.

Transport tracks exactly the entering/departing terms. The modular observation
`selected_modEq_of_dvd_moved` requires every moved term to be divisible by
the modulus; no unconditional gcd or valuation preservation is asserted.

### `GTailSeven`, `GTailSevenArithmetic`

Also explicitly promoted through `DkMath.Lib`. Degree-seven interior balance:

```text
(x+u)^7 = (u^7+x^7) + 7*x*u*(x+u)*(x^2+x*u+u^2)^2
```

This is a norm-shaped polynomial identity in a CommSemiring. Its subtraction
reading uses CommRing; it supplies no map to an FLT7 cyclotomic carrier.
The degree-seven cuts and endpoint transport reuse the generic layers.
Over naturals, `Nat.Coprime a b` makes a, b, a+b and their product coprime to
`a^2+a*b+b^2`. The exact-seven-layer endpoint requires both `7 ∣ g` and
`¬ 7 ∣ c`, giving `7 ∣ GTail 7 1 g c` and `¬ 49 ∣ GTail 7 1 g c`.
It does not assume or infer `Nat.Coprime g c`.

The hypothesis-bearing `GTailBridge` and `GTailConstraintAudit` remain
FLT7 owner APIs, exposed by `import DkMath.FLT.Seven`; they are not imported
into this neutral entrance. Their conditional results establish neither
nonexistence nor constructive descent.

### `GTailBoundary`

Exact gcd / first-boundary structure.

Representative APIs:

```text
gcd_GTail_eq_gcd_boundary
gcd_GTail_eq_gcd_choose
gcd_GN_eq_gcd_of_one_le
gcd_GN_prime_eq_one_of_not_dvd
gcd_GN_prime_eq_prime_of_dvd
```

### `GTailCongruence`

Natural-number congruence propagation and head-collapse results.

Representative APIs include:

```text
GTail_congr_of_modEq
GTail_modEq_eval_zero_of_dvd_x
prime_dvd_GN_iff_dvd_gap
GN_mod_p2_head
GN_mod_p3_head
```

### `GTailCyclotomic`

Neutral algebraic bridge between the $r=1$ tail and cyclotomic shells.

Representative APIs:

```text
prod_cyclotomicEval_eq_geomSum
add_pow_eq_mul_GTailCyclotomicShell_add_gap
GTail_one_eq_cyclotomicHomEval_of_prime
```

### `GTailNat`

Natural-number divisibility consequences.

Representative APIs:

```text
pow_dvd_higher_tail
GTail_not_dvd_of_head_unit_of_prime_dvd_x
GN_not_dvd_of_head_unit_of_prime_dvd_x
```

### `GTailPadic`

`padicValNat` consequences of the tail decomposition.

Representative APIs:

```text
padicValNat_GTail_eq_zero_of_head_unit_of_prime_dvd_x
padicValNat_tail_exact_of_head_unit
padicValNat_GN_exact_of_head_unit
not_prime_sq_dvd_GN_of_dvd_gap
padicValNat_GN_prime_eq_one_of_dvd_gap
```

### `GTailPascal`

Finite-depth Pascal filtration.

Main API:

```text
GTail_split_at
```

## 3. Number-theory family

### `PadicValNat`

Reusable natural-number valuation utilities, independent of ABC/FLT/RH owners.

Includes zero criteria, bounds, powers, carrier-shape lemmas, and prime-power divisibility tools.

### `BinomialPrimePower`

Exact coefficient valuations for prime-power Pascal rows, for every prime:
`v_p(choose (p^n) k) + v_p(k) = n` when `0 < k ≤ p^n`.
Includes the subtractive formula and two prime-power divisibility consequences.
The original NumberTheory names remain wrappers; filtered-beam carriers stay
with that owner. Prime regularity is not an assumption or a conclusion.

### `PowerDifferenceCofactorGcd`

For primitive coordinates x,y and odd n, the geometric cofactor R_n is
coprime to x+y and to its natural completion deficit D_n. The ring argument
uses `R_(2k+1) ≡ (-xy)^k (mod x+y)`; natural gcd results follow by casting.
Ring Bezout coprimality also applies to the signed deficit. The module
translates the existing GN gap-gcd and adjacent-coprime APIs. Even degrees
and nonprimitive coordinates can have a nontrivial cofactor/deficit gcd.

### `PowerDifferenceCofactorStrongDivisibility`

At primitive natural coordinates, `gcd(R_m,R_n)=R_gcd(m,n)`, including zero
indices. The sequence is registered with `Nat.IsStrongDvdSequence`.
The proof uses the cofactor addition formula and Euclid's algorithm.
Divisibility of indices alone implies divisibility of cofactors without
requiring primitive coordinates. The exact gcd with `xy R_(n-2)` remains
distinct from the even-degree completion-deficit gcd.

### `PrimeRatioOrder`, `CyclotomicAddress`, `CyclotomicLayerValuation`

Neutral owners for the existing GapFocusing residue-ratio/order, cyclotomic
root-address and valuation APIs. Historical namespaces and old imports remain
compatible. The general order kernel has no Zsigmondy dependency.
Odd-prime LTE and the two-adic sum correction are retained separately.

### `PowerDifferenceCofactorPrimeAddress`

The whole cofactor R_n detects `r ∣ n` when the residue-ratio order r is greater
than one. At order one it instead detects `q ∣ n`. A single cyclotomic layer
has the distinct address `n=r*q^k`; the homogeneous evaluator and its CFBRC compatibility spellings are now
owned by the neutral GN-LIB-006b modules. No valuation-one assumption is imposed on the
fundamental address: `R_3(18,1)=7³` is a checked boundary example.

### `HomogeneousCyclotomic`, `HomogeneousCyclotomicAddress`, `HomogeneousCyclotomicBoundary`

The polynomial evaluator at coordinates (a,b), its historical CFBRC shifted
spelling at (a-b,b), the support/first-appearance definitions and all neutral
layer-address proofs live in Lib. Original names and bodies are retained.
Compatibility is given by definitional and explicit coordinate equalities;
these owners import no CFBRC application or Zsigmondy carrier.

### `HomogeneousCyclotomicPrimeAddress`

The direct-coordinate interface classifies positive single-layer addresses
by `n=r*q^k`, treats vanishing coordinates separately, and exposes mapping,
unit-anchor and zero-anchor formulas. At degree zero the value is 1.
The first positive and first nontrivial layers differ when r=1. Valuation at
the basic address may exceed one. These are polynomial/divisibility results.

### `PowerDifferenceCofactorValuation`, `CompletionDefectGcd`

At a prime q dividing x+y, squared primitive bases satisfy
`v_q(R_m(x²,y²))=v_q(m)`. Odd-prime LTE and the four-divisible two-adic
LTE branch are proved separately. Natural LTE uses strict ordering and a
nonzero exponent; the final gcd formula removes the ordering by symmetry
and handles the primitive diagonal directly.

For every primitive natural pair and m>0:
`gcd(R_(2m),D_(2m))=(x+y)*gcd(m,(x+y)^(2m-2))`.
The positive-degree parity API combines this with the odd gcd-one result.
Degree zero has a separate gcd-one theorem. Primitive zero coordinates,
reversed pairs and n=2 are included; primitiveness and positive degree remain
explicit. The borrowed correction has a different even gcd from D_n.

### `PowerFactor`

Neutral coprime power-factor splitting.

Representative APIs:

```text
associated_prime_power_of_coprime_mul_eq_pow
eq_pow_of_associated_pow_of_unit_pow_surjective
power_factor_split
```

### `IdealPowerFactor`

Neutral ideal-power / class-group kernel.

Key definition:

```lean
def classGroupPTorsionFreeAt (R : Type*) (p : ℕ) : Prop := ...
```

Representative APIs:

```text
ideal_isPrincipal_of_classGroupPTorsionFreeAt
ideal_isPrincipal_of_pow_isPrincipal_of_classGroupPTorsionFreeAt
exists_eq_pow_of_isCoprime_mul_eq_pow
```

This module deliberately stops at the ideal/class-group layer; unit absorption is separated.

### `PrincipalIdealPower`

Bridges principal-ideal equality to associated / unit-times-power element statements.

Representative APIs:

```text
associated_of_span_singleton_eq_span_singleton
exists_unit_mul_pow_of_span_eq_pow_of_isPrincipal
exists_unit_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt
exists_eq_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt
```

### `UnitPowerSector`

Neutral interface for unit groups modulo $p$-th powers.

The abstraction provides representatives and completeness without asserting global surjectivity of the unit $p$-th-power map.

### `TraceOneLatticeLanding`

Integral-coordinate divisibility criterion for the existing `TraceOneInt s` carrier.

The key equivalence converts element divisibility into divisibility of the coordinates of multiplication by the conjugate, under the explicit nonzero-norm hypothesis.

Representative API:

```text
traceOne_dvd_iff_norm_dvd_mul_conj_coordinates
```

### `TraceOnePowerLanding`

Current power-image receiver layer for `TraceOneInt s`. The present production theorem explicitly records square coordinates and square-core landing; it does not provide a general arbitrary-power root provider.

Representative APIs:

```text
traceOne_sq_coordinates
traceOne_norm_pow
traceOne_sq_core_landing_iff
```

### `EisensteinCoordinates`

Neutral standard Eisenstein coordinates represented inside `TraceOneInt (-1)`.

```lean
def eisensteinCoord (m n : ℤ) : TraceOneInt (-1) := ...
```

The module reuses the existing TraceOne ring/norm instead of defining a second arithmetic carrier.

### `EisensteinLatticeLanding`

Integral-coordinate divisibility criterion specialized to the standard Eisenstein model.

Representative API:

```text
eisenstein_dvd_iff_norm_dvd_conjugate_coordinates
```

### `SquarefreePowerFactor`

Neutral UFD-side square-factor extraction:

```text
exists_squarefree_mul_sq
```

This was extracted from ABC Eisenstein provider work but is not ABC-specific.

## 4. Other promoted kernel

### `TwoChannel`

A neutral real-linear sum/difference coordinate kernel

$$
(u,v)\longmapsto(u+v,u-v),
$$

with domain-specific interpretation left to owner modules.

## 5. Promotion policy

A theorem is a good `DkMath.Lib.*` candidate when:

- its statement is not inherently tied to one research conjecture or checkpoint;
- owner-specific assumptions can be removed or made explicit parameters;
- its dependencies can point downward into Mathlib / neutral DkMath kernels;
- a later owner can reasonably import it without inheriting unrelated research machinery.

Avoid promoting a theorem merely to rename it. The promoted statement should expose a genuinely reusable mathematical boundary.

## 6. GN5 and the origin of the promoted layer

GN5 / FLT5 work was a major source of reusable structures: binomial-tail identities, divisibility, p-adic splitting, power-factor extraction, algebraic coordinate landing, and unit-sector organization.

The current architecture treats the fixed-degree GN5 project as an important historical success and test case, while `DkMath.Lib.*` is the long-lived home for the abstractions that survived generalization.

## 7. Current status

As of the 2026-10-09 integration snapshot, `DkMath.Lib` is an established promoted layer but is still evolving. Some reusable mathematics remains in older owner namespaces and may be migrated in later refactors.

## Cofixed branch-swap obstruction (NOTE-032)

`DkMath.Lib.RepresentationTheory.CofixedBranchSwap` proves a conditional obstruction
for one-dimensional cofixed subspaces. It retains a proper absorbing subspace,
a nontrivial local action, a quotient sign-reversing element, and 2≠0 in the field.
It uses containment of the line in the absorber; ambient rank two is not required.
Frey arithmetic supplies these inputs separately through `DkMath.FLT.FreyCofixedBranchSwap`.
[Implementation report](../../docs/dev/FLT-GN-regular-261018-v0/IMPLEMENTATION-NOTE032-001-261025.md).

`FreyModEight`, `ValuationQuadraticFrobenius`, and `EllipticFrobeniusBranchSwap`
separate odd-exponent mod-eight arithmetic, characteristic-two residue action,
and actual tangent/point branch exchange. Their public theorems retain the model,
centre, Frobenius and shallow-point hypotheses. The Frey consumer supplies these
for a≡3 mod8; the a≡7 mod8 case remains separate.
[003C report](../../docs/dev/FLT-GN-regular-261018-v0/IMPLEMENTATION-NOTE032-003C-261025.md).

`ValuationPrimeExistence.exists_liesOverPrime` supplies a valuation subring above
any prime in any characteristic-zero field, using lying-over in the integral closure.
The Frey consumer uses it to supply the dyadic address internally in the a≡3 mod8
hno and irreducibility endpoints.
[004 report](../../docs/dev/FLT-GN-regular-261018-v0/IMPLEMENTATION-NOTE032-004-261025.md).

`FreySplitModEight`, `ValuationSplitQuadratic`, and `EllipticSplitDyadic`
handle the a≡7 mod8 split tangent cone. The decomposition group fixes each
direction and sends actual point differences into the smooth zero component.
The Frey consumer identifies a possible global cofixed line with the same E₀[p];
the global escape needed for hno remains unproved.
[005A report](../../docs/dev/FLT-GN-regular-261018-v0/IMPLEMENTATION-NOTE032-005A-261025.md).

`RepresentationTheory.CofixedDeterminant` identifies the action on a cofixed line
with the determinant, for any finite ambient dimension. The endomorphism need not
be invertible. `NumberTheory.EllipticCofixedCyclotomic` uses the constructed Weil
pairing to identify that action with the cyclotomic character on the same actual
torsion points and point subgroup. The adapted matrix retains its upper-right entry.
[005B report](../../docs/dev/FLT-GN-regular-261018-v0/IMPLEMENTATION-NOTE032-005B-261025.md).

`RepresentationTheory.CofixedImage` transports cofixedness through an equivariant
linear map with the specified kernel and identifies the quotient with the same image.
`NumberTheory.EllipticCofixedImage` restricts an actual point homomorphism to torsion;
given its kernel and Galois equivariance, the image has order p and supplies a nonzero
rational p-torsion point on the target curve. Quotient-curve and isogeny existence remain open.
[005C1 report](../../docs/dev/FLT-GN-regular-261018-v0/IMPLEMENTATION-NOTE032-005C1-261025.md).
