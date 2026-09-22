# GTail Cyclotomic Norm Bridge

Branch: **research/GTail-Cyclotomic-Norm-Bridge-260922-v0**

Base: **develop** at **0e1e8468f8110b65e58bb7a8d5455696281a7d2e**

## Mission

This branch extracts the reusable algebraic content identified at the close of
the FLT7 TraceOne campaign and moves it into the generic
GTail / GN / cyclotomic / norm layer.

The main question is not a fixed-exponent FLT7 question. It is:

~~~text
Can the one-gap Cosmic Formula kernel be identified canonically with the
homogeneous cyclotomic carrier, while retaining the complete gap factor and
then transporting that carrier through norm / ideal / valuation / p-power
structures?
~~~

The intended representation chain is:

~~~text
GTail d 1 x u
    |
    v
GTailCyclotomicShell d x u
    |
    | prime p
    v
homogeneous Phi_p(x+u,u)
    |
    v
product of nonzero primitive-root factors
    |
    v
cyclotomic / complex carrier
    |
    v
Norm / ideal / valuation / p-power transport
~~~

At the same time, the complete power-difference quantity must be retained:

~~~text
(x + u)^d - u^d
  = x * GTail d 1 x u
  = x * GTailCyclotomicShell d x u.
~~~

For prime p, the cyclotomic root-product layer gives the corresponding
complete carrier identity.

## Why this branch exists

The closed FLT7 branch reached a point where further fixed-p = 7 work would
have duplicated a more general phenomenon. Its GENERALIZATION_HANDOFF.md
therefore required the next work to move into a generic
FLT/GN/cyclotomic/norm layer.

The essential observation is that several DkMath objects that had been
developed separately are presentations of the same algebraic kernel:

- the promoted one-gap GTail row;
- GTailCyclotomicShell;
- the CFBRC cyclotomicPrimeCore;
- the canonical GN kernel;
- for prime p, the homogeneous prime cyclotomic factor;
- for prime p, the complete product over the nonzero cyclotomic roots.

The first purpose of this branch is to make those identifications explicit
without unnecessary field or nonzero-gap assumptions.

## Current checked surface

### 1. Cancellation-free GTail / cyclotomic-shell identity

DkMath.Lib.Cosmic.GTailCyclotomic now exposes the conceptual theorem:

~~~lean
GTail_one_eq_GTailCyclotomicShell
    {R : Type _} [CommSemiring R] (d : Nat) (x u : R) :
    GTail d 1 x u = GTailCyclotomicShell d x u
~~~

This is a polynomial identity. It no longer depends on:

~~~text
Field R
x != 0
multiplicative cancellation
~~~

The former GTail_one_eq_GTailCyclotomicShell_of_ne_zero theorem remains as a
compatibility wrapper. In particular the identity is valid at the boundary
x = 0.

### 2. CFBRC core = promoted GTail = GN

DkMath.CFBRC.Basic now identifies the previously duplicated CFBRC core with
the promoted kernel:

~~~text
cyclotomicPrimeCore d x u
  = GTail d 1 x u
  = GN d x u
~~~

over an arbitrary commutative semiring, again without nonzero-gap
cancellation.

### 3. Prime cyclotomic root-product carrier

DkMath.CFBRC.CyclotomicNorm introduces cyclotomicRootProduct for a prime
exponent and a chosen primitive p-th root.

Using the existing production theorem
CyclotomicQRProduct.nonzeroRoot_product_eq_shell, the branch proves:

~~~text
cyclotomicRootProduct
  = GTailCyclotomicShell p x u
  = GTail p 1 x u
  = GN p x u.
~~~

The complete gap factor is retained by:

~~~text
x * cyclotomicRootProduct
  = (x + u)^p - u^p.
~~~

This is the first direct implementation of the FLT7 handoff requirement that
the generalized bridge preserve the complete product, not merely the
quotient-like GN factor.

### 4. First complex norm-square layer

For a complex root factor, the branch proves the standard conjugate identity:

~~~text
factor * conj(factor) = Complex.normSq factor.
~~~

It also transports equality of the complete cyclotomic carrier and the power
difference through Complex.normSq.

This is intentionally only the first norm-aware layer.

## Field norm bridge: extracted, with one remaining boundary

GCNB-003 extracted a genuine algebraic norm theorem into
DkMath.CFBRC.CyclotomicNorm.

For a prime p, a cyclotomic extension K/Q, a primitive p-th root zeta, and
natural gap/base coordinates x,u with u != 0, the branch now proves the
ring-of-integers norm identity

~~~text
Algebra.norm Z ( (x+u) - zeta*u ) = GN p x u
~~~

with the exact Lean carrier supplied by
cyclotomicLinearFactorInRingOfIntegers.

The public theorems are:

~~~text
cyclotomicLinearFactor_norm_eq_GN_ratCast
cyclotomicLinearFactor_norm_eq_GN
~~~

This is a genuine Algebra.norm result and is distinct from the earlier
Complex.normSq layer.

The remaining GCNB-003 boundary is the proof-path hypothesis u != 0. The
current implementation reaches the homogeneous cyclotomic value through the
ratio (x+u)/u; the mathematical identity itself is expected to extend across
u = 0. GCNB-003R is assigned to remove that accidental division boundary if
the pinned API permits a clean direct homogeneous proof.

The branch still does not yet provide:

- a principal-ideal identity for the new generic carrier;
- ideal-level p-power transport;
- valuation transport through the carrier norm;
- a conjugate-pair half-product theorem;
- a generic bridge from the full cyclotomic carrier back to the existing
  Prime/TraceOne residual packets.

## General-d versus prime-p

For prime p,

~~~text
GTail p 1 x u = homogeneous Phi_p(x+u,u).
~~~

For composite d, the corresponding shell is not a single Phi_d factor. It is
the product of the nontrivial cyclotomic divisor factors:

~~~text
((x+u)^d - u^d) / x
  ~ product_{m | d, m > 1} Phi_m(x+u,u).
~~~

The existing DkMath.CFBRC.CyclotomicProduct layer is the relevant general-d
infrastructure. Future refactoring should avoid conflating the prime and
composite statements.

## FLT interpretation

In gap/base coordinates g, u with endpoint g + u,

~~~text
(g + u)^p - u^p = g * GN p g u.
~~~

The purpose of the new carrier is to let an FLT packet keep this entire
integer-side quantity while changing representation:

~~~text
integer gap product
    -> homogeneous cyclotomic carrier
    -> norm / ideal / valuation representation
    -> existing TraceOne or power-landing receivers.
~~~

A representation change is not itself a contradiction. It becomes useful only
when a later theorem preserves enough divisibility / valuation / perfect-power
information to close an actual FLT obligation.

## Current validation

The initial implementation is kernel checked under Lean v4.34.0.

PR #105 reached:

~~~text
Lean CI #1017
Build DkMath: SUCCESS
~~~

The repair commit at the time this README was created was:

~~~text
53b26d04f66b7cc913755dcf300156f61006a850
fix: errors
~~~

## Non-claims

This branch currently does **not** claim:

- FLT7 unconditionality;
- a new proof of general FLT;
- an assumption-free u = 0-inclusive cyclotomic field-norm theorem;
- cyclotomic principalization from the new carrier;
- a new class-group theorem;
- a p-th-power root of the carrier;
- a contradiction from GN being a perfect power;
- resolution of the deferred FLT7 degree-six carrier cutoff.

These require further checked bridges.

## Working rules

- Lean decides theorem validity.
- No sorry, admit, new axiom, or unsafe proof shortcut.
- Preserve the complete gap factor when an FLT theorem needs it.
- Do not infer element equality from norm equality.
- Do not call Complex.normSq the cyclotomic field norm.
- Do not identify the TraceOne shadow with the full cyclotomic carrier without
  a checked bridge.
- Keep prime-p and general-d cyclotomic statements distinct.
- Reuse existing production cyclotomic, valuation, Kummer, and TraceOne APIs
  instead of rebuilding parallel theories.

## Checkpoint workflow

Further work should use:

~~~text
instruction-NNN.md
report-NNN.md
~~~

The initial implementation predates these branch documents, so ROADMAP.md
records the already completed algebraic checkpoints retroactively before
opening the next norm/ideal checkpoint.
