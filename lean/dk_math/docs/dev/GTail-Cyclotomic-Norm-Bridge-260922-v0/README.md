# GTail Cyclotomic Norm Bridge

cid: `6ab15403-df28-83e8-bd7c-af7177767135`

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

GCNB-003R has now removed the remaining proof-path hypothesis u != 0.
The canonical public Norm = GN theorem is unconditional in the natural
gap/base coordinates x,u. The former nonzero-base results remain available as
compatibility lemmas with the suffix _of_ne_zero.

The u = 0 branch is proved directly: the carrier reduces to the scalar x, its
field norm is x^(p-1), and GN p x 0 is proved to be the same power. Thus the
stable API no longer exposes the ratio-based proof restriction.

GCNB-004 now also attaches the principal ideal

~~~text
I_alpha = (alpha)
~~~

and proves

~~~text
Ideal.absNorm I_alpha = GN p x u
x * Ideal.absNorm I_alpha = (x+u)^p - u^p
padicValNat q (Ideal.absNorm I_alpha) = padicValNat q (GN p x u)
~~~

together with the existing-hypothesis bridge to the valuation of the complete
power difference.

This is intentionally a **global rational-prime valuation** layer. It does not
identify the multiplicity of any one prime ideal above q.

GCNB-005 now connects the generic FLT arithmetic packet to the carrier. For
a PrimeAdicFactorPacket one has

~~~text
g * Ideal.absNorm I_alpha = x^p,
padicValNat p (Ideal.absNorm I_alpha) = 1,
p divides Ideal.absNorm I_alpha,
p^2 does not divide Ideal.absNorm I_alpha.
~~~

For PrimeAdicPowerSplit the same carrier satisfies

~~~text
Ideal.absNorm I_alpha = p * b^p.
~~~

A PrimeGe5CounterexamplePack reaches the complete carrier identity without
assuming p divides the gap; that divisibility is introduced only by the local
ramified constructor.

GCNB-006 now proves that the arbitrary-prime TraceOne coordinate shadow and
the full cyclotomic ideal carrier have exactly the same scalar norm:

~~~text
TraceOne.norm (P.coord (g+u) u)
  = (Ideal.absNorm I_alpha : Z),

natAbs (TraceOne.norm (P.coord (g+u) u))
  = Ideal.absNorm I_alpha.
~~~

The same equality is available through rational-prime divisibility and
padicValNat, and through PrimeAdicFactorPacket / PrimeAdicPowerSplit. The
Nat/Int GTail-shell bridge is now unconditional at g = 0.

GCNB-008 now calibrates the generic scalar bridge against all three existing
fixed-prime carrier families:

~~~text
p = 3:
  cyclotomic ideal absNorm
    = Eisenstein / TraceOneInt (-1) norm

p = 5:
  cyclotomic ideal absNorm
    = Golden square-link / TraceOneInt 1 norm
    = GoldenNorm square-link

p = 7:
  cyclotomic ideal absNorm
    = norm (cyclotomicSevenToTraceOne ...)
~~~

For p = 3,5,7 the arbitrary-prime PrimeTraceOneCoordinatePacket norm is also
proved equal to the corresponding dedicated fixed-prime scalar. The
calibration remains scalar-only.

The branch still does not yet provide:

- local prime-ideal multiplicity ownership for the new carrier;
- an exact local upper-cutoff theorem for a chosen oriented cyclotomic prime;
- ideal-level p-power transport from a norm p-th power alone;
- principalization/class-group consequences from the new carrier;
- a conjugate-pair complex norm decomposition;
- identification of cyclotomic elements or ideals with TraceOne elements or
  ideals;
- any FLT7 endpoint theorem.

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

PR #105 has reached multiple green checkpoints. The current GCNB-004 code
state was confirmed by:

~~~text
Lean CI #1029
Build DkMath: SUCCESS

GCNB-005 also passed all focused/full local builds recorded in report-003.md;
the corresponding GitHub CI run is tracked separately as the branch advances.
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
- cyclotomic principalization from the new carrier;
- local prime-ideal multiplicity transport from the new carrier;
- a new class-group theorem;
- a p-th-power root of the carrier;
- a contradiction from GN being a perfect power;
- resolution of the deferred FLT7 degree-six carrier cutoff.

These require further checked bridges.

## FLT7 re-entry audit after GCNB-008

The completed generic stack now supplies the norm-aware carrier machinery
requested by the closed FLT7 handoff, but this alone does not reopen FLT7.

The R64 endpoint already proves an exact multiplicity 14 * eQ for the selected
real factor. Its deferred obstruction is the **exact upper cutoff in the
current phase-corrected degree-six oriented kernel**.

The generic absNorm / rational-prime padicValNat layer is an aggregate scalar
statement and does not by itself determine the exponent of one chosen prime
ideal.

A final bounded checkpoint, GCNB-009A, therefore targets a reusable
conjugate-prime / relative-norm ownership theorem. The FLT7 re-entry gate opens
only if that generic theorem can be instantiated, in a scratch/test
specialization, to recover the missing R64 current-carrier upper cutoff.

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
