# GTail Cyclotomic Norm Bridge Roadmap

Branch: **research/GTail-Cyclotomic-Norm-Bridge-260922-v0**

Base: **develop** at **0e1e8468f8110b65e58bb7a8d5455696281a7d2e**

This roadmap begins at the generalization handoff from the closed
research/FLT7-Unconditional-TraceOne-Closure-260917-v0 branch.

The campaign is intentionally representation-first:

~~~text
GTail / GN
  -> homogeneous cyclotomic shell
  -> complete cyclotomic root product
  -> field norm
  -> ideals / valuations / p-th powers
  -> Prime/TraceOne compatibility
  -> p=3,5,7 regressions
  -> possible FLT7 re-entry.
~~~

A later layer may use an earlier one, but it must not silently replace a
missing field-norm or ideal theorem by a complex absolute-value identity.

## GCNB-000 — Branch bootstrap and current-state freeze

Create the branch documentation after the initial implementation landed and
record exactly what is already kernel checked.

Freeze the distinction between:

~~~text
PROVED:
  cancellation-free GTail = shell
  CFBRC core = GTail = GN
  prime nonzero-root product = shell
  gap * root product = power difference
  Complex.normSq transport

NOT YET PROVED:
  cyclotomic field norm
  principal ideal identity
  norm/valuation/p-power transport
  full TraceOne compatibility
  FLT7 endpoint consequence
~~~

Status: **completed — documentation bootstrap after CI GREEN**.

Baseline validation:

~~~text
PR #105
Lean CI #1017
Build DkMath: SUCCESS
~~~

## GCNB-001 — Cancellation-free one-gap kernel identification

Replace the old cancellation route

~~~text
x * GTail = x * shell
x != 0
Field cancellation
~~~

by a direct polynomial identity over CommSemiring:

~~~lean
GTail d 1 x u = GTailCyclotomicShell d x u
~~~

Retain the former field/nonzero theorem only as compatibility API.

Use the theorem to identify the CFBRC cyclotomicPrimeCore directly with GTail
and GN.

Required regression: x = 0 must remain valid.

Status: **completed — Outcome A**.

## GCNB-002 — Prime root-product and complete-gap carrier

For prime p, reuse CyclotomicQRProduct to define a complete root-product
carrier and prove:

~~~text
cyclotomicRootProduct
  = GTailCyclotomicShell p x u
  = GTail p 1 x u
  = GN p x u
~~~

Then retain the boundary factor:

~~~text
x * cyclotomicRootProduct
  = (x+u)^p - u^p.
~~~

Add the first complex conjugation / norm-square compatibility theorem.

Do not call this a cyclotomic field-norm theorem.

Status: **completed — Outcome A**.

## GCNB-003 — Canonical cyclotomic field carrier and field Norm

This is the next genuine mathematical checkpoint.

Audit the pinned Mathlib v4.34.0 APIs for:

~~~text
IsCyclotomicExtension
AdjoinRoot / cyclotomic field models
FiniteDimensional
Algebra.norm
primitive-root embeddings / conjugates
RingOfIntegers where needed
~~~

Choose the smallest reusable carrier on which the element

~~~text
alpha = (x + u) - u * zeta_p
~~~

has a checked field norm equal to the homogeneous prime cyclotomic value.

Target theorem shape, subject to the exact available carrier API:

~~~text
Norm(alpha) = GN p x u
~~~

or an equivalent statement after explicit coefficient embeddings.

A successful checkpoint must distinguish Complex.normSq alpha from
Algebra.norm alpha.

For odd prime p, a later corollary may express the full field norm as a product
of complex conjugate-pair norm squares, but that decomposition is not a
substitute for the field-norm theorem itself.

Status: **completed — Outcome B**.

A genuine dependency-neutral Algebra.norm = GN theorem is now production
code. The only remaining hypothesis is u != 0, inherited from the ratio-based
proof route.

## GCNB-003R — Remove the nonzero-base proof boundary

Before opening the ideal layer, attempt to remove the remaining u != 0
hypothesis from the public norm theorem.

Prefer a direct homogeneous proof:

~~~text
Norm((x+u) - zeta*u)
  = product over embeddings / primitive roots
  = GTailCyclotomicShell p x u
  = GN p x u
~~~

which should avoid division entirely.

A simpler explicit u = 0 branch is acceptable if it yields the same stable
public theorem without introducing stronger assumptions.

Required boundary regressions include u = 0 and, ideally, x = u = 0.

Status: **completed — Outcome A**.

The canonical public Algebra.norm = GN theorem is now assumption-free in u.
The old nonzero-base route remains only as a compatibility wrapper.

## GCNB-004 — Principal ideal and valuation transport

Once GCNB-003 supplies a genuine field/integer carrier, connect the element
identity to ideals.

Investigate theorem shapes around:

~~~text
Ideal.span
Norm of principal ideals
valuation of Norm(alpha)
prime support of alpha
~~~

and compatibility with the existing:

~~~text
DkMath.CFBRC.Bridge
DkMath.FLT.Kummer.CyclotomicPrincipalization
primitive-prime / Zsigmondy bridges
~~~

The aim is not merely to re-prove GN = cyclotomic product, but to preserve the
arithmetic information required by FLT:

~~~text
divisibility
prime multiplicity
p-adic valuation
principal-ideal powers
p-th-power aggregation
~~~

Status: **completed — Outcome A**.

The canonical cyclotomic principal ideal now satisfies exact absNorm = GN,
retains the complete gap product, and exposes global rational-prime
padicValNat transport. Individual prime-ideal multiplicity is deliberately
deferred.

### GCNB-004L — Local prime-ideal multiplicity aggregation

Deferred follow-up.

This checkpoint should be opened only when a downstream theorem actually needs
a chosen prime ideal above q or an aggregate residue-degree formula. It must
not identify padicValNat q (Ideal.absNorm I) with one prime-ideal exponent
without a checked sum formula over primes above q.

Status: **deferred; not the next checkpoint**.

## GCNB-005 — Generic FLT gap packet compatibility

Connect the complete carrier to the generic FLT front end without specializing
to p = 7.

The desired route is:

~~~text
primitive odd-prime FLT packet
  -> gap g and base u
  -> g * GN p g u
  -> complete cyclotomic carrier
  -> norm / ideal / valuation packet
~~~

Preserve the existing away/ramified branch distinction. Do not assume p | g
for every counterexample.

The output should be a reusable packet or theorem family, not an FLT7-specific
adapter.

Status: **next checkpoint**.

## GCNB-006 — Prime/TraceOne shadow compatibility

Relate the full cyclotomic carrier to the existing quadratic TraceOne shadow.

Existing production infrastructure already provides:

~~~text
CyclotomicQRTraceOneBridge
PrimeTraceOneCoordinatePacket
TraceOnePowerLanding
TraceOneLatticeLanding
~~~

The checkpoint must state exactly what is preserved under the projection.

Possible outputs include checked compatibility of:

~~~text
norms
principal ideals
prime support
valuation data
p-th-power residual equations
~~~

Do not infer equality of full cyclotomic elements from equality of TraceOne
norms.

Status: **blocked on GCNB-004/005**.

## GCNB-007 — Conjugate-pair complex norm decomposition

For odd prime p, pair exponents k and p-k and prove a finite product formula of
the conceptual form:

~~~text
GN p x u
  = product_{k=1}^{(p-1)/2}
      Complex.normSq ((x+u) - u * zeta_p^k)
~~~

after the necessary real/complex coercions.

A trigonometric corollary may then expose:

~~~text
|(x+u) - u exp(2*pi*i*k/p)|^2
  = x^2 + 4*u*(x+u)*sin(pi*k/p)^2.
~~~

This layer is useful for CFBRC geometry, but it must remain downstream of the
algebraic carrier identity and must not erase integer divisibility information.

Status: **open; may proceed independently after carrier API stabilizes**.

## GCNB-008 — p = 3, 5, 7 calibration

Specialize the generic theorems to the exponents with existing strong DkMath
infrastructure.

### p = 3

Compare with the Eisenstein / TraceOneInt (-1) carrier and the completed FLT3
route.

### p = 5

Compare with the Golden / TraceOneInt 1 bridge and the completed FLT5 route.

### p = 7

Compare with:

~~~text
PrimeAdicPowerSplit
CyclotomicQRTraceOneBridge
the closed FLT7 TraceOne branch
the deferred degree-six carrier / common-prime aggregation frontier
~~~

Regression means representation compatibility, not reusing the completed
FLT3/FLT5 contradictions as generic black boxes.

Status: **blocked on the stable GCNB-003..006 API**.

## GCNB-009 — FLT7 re-entry gate

Return to a new FLT7 branch only if the generic campaign supplies at least one
new theorem that specializes to a previously deferred obligation.

The handoff names two useful classes of input:

~~~text
1. a norm/ideal theorem strong enough to lift selected-factor multiplicity
   to the degree-six carrier cutoff;

2. a principal-ideal / p-th-power aggregation theorem capable of combining
   local oriented factors across common primes.
~~~

If no such theorem is produced, do not reopen the old FLT7 tower merely
because the same identities have been rewritten in cyclotomic notation.

Status: **re-entry gate closed**.

## Global stop rules

Stop and report rather than forcing a theorem if:

- Complex.normSq is the only available norm but a field norm is required;
- a root-product equality loses the complete gap factor needed by FLT;
- a norm equality is used as element equality;
- a principal-ideal theorem would require an unproved class-group or PID
  hypothesis;
- a p-th-power ideal is promoted to an element p-th power without a unit /
  class-group argument;
- a TraceOne shadow is treated as the full cyclotomic carrier;
- a fixed-p calculation is advertised as a generic theorem;
- the composite-d shell is identified with a single Phi_d factor;
- a local valuation statement is promoted to a global FLT descent provider.

## Next implementation document

Use instruction-003.md for GCNB-005.

The next bounded checkpoint connects the stabilized cyclotomic
Norm/ideal/valuation carrier to the existing generic odd-prime FLT arithmetic
packet. GCNB-004L local prime-ideal aggregation remains deferred until a
downstream theorem requires it.
