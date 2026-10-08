# Instruction 049 - Centered GN polynomial and canonical endpoint uniqueness

## Mission

Continue from Instruction 048.  The depth-four FLT7 reconstruction
obligation is equivalent to a divisor-supported OR of two exact scalar
receivers over positive coprime r,s with

  M = r*s,  D = 7^27*r^49,  target = 7*s^49.

Instruction 046 routes each fixed allocation to at most one branch;
047-048 filter allocations by exact modular constraints.  Remaining scalar
endpoint existence or exclusion is unresolved.

Stop adding unrelated modular filters.  This checkpoint should reveal
a common exact polynomial behind the GN and alternating branches and,
if possible, finish canonical endpoint uniqueness.

## Main algebraic insight

Define the natural centered sextic polynomial

  P D q =
    7*q^6 + 35*D^2*q^4 + 21*D^4*q^2 + D^6.

The following polynomial identities are proposed for Lean verification:

  64 * GN 7 D u = P D (D+2*u),

and, for nonnegative u<=v with D=u+v,

  64 * alternatingCyclotomicSeven u v = P D (v-u).

They are manifestations of the integer identity

  64*((x+D)^7-x^7)
    = D * P D (2*x+D),

valid for signed integer x and natural D cast to integers.

The RHS chart uses x=-u, D=u+v; GN uses x=u.
Do not divide by D before proving D>0.  Avoid treating signed
subtraction as truncated Nat subtraction.

## Primary formal targets

1. Prove both exact polynomial identities in the existing
   GN/alternating APIs.  Reuse Instruction 046's signed
   fixed-sum/product identity if convenient.

2. For fixed D, prove StrictMono (P D) on natural q.  The leading
   7*q^6 term is strictly increasing and all remaining even-power
   terms are nondecreasing.  No calculus needed.

3. Specialize each exact nested receiver to the SAME equation

      P D q = 64*7*s^49,

   with the exact center coordinate:

      GN branch: q=D+2*u > D;
      alternating branch: after ordering 0<u<=v,
                          q=v-u < D,  D=u+v.

   Prove P D D = 64*D^6.  The 046 allocation threshold is thereby
   reinterpreted as the position of the unique possible q relative to D.

4. Since P D is injective, prove that for fixed positive r,s at most
   one center coordinate q can satisfy the common equation.
   Deduce GN endpoint uniqueness (already available as regression) and
   alternating ordered endpoint uniqueness (new).
   Do NOT assert raw ordered-pair uniqueness without the canonical
   u<=v orientation; swapping endpoints preserves the alternating chart.

## Canonical receiver, optional if thin

A single centered equation can eliminate the separate endpoint searches,
but it must preserve chart provenance.

If useful, define a small centered-candidate predicate carrying

  q>=0,  P D q = 64*7*s^49,

and one of:

  q>D with q=D+2*u and GN primitive endpoint conditions;

  q<D with D-q=2*u, 0<u<=D-u, and alternating primitive conditions.

A parity condition q congruent to D modulo 2 is essential.
Prove equivalence to the existing selected-branch receiver, not merely
a necessary numerical equality.

Do not allow q=D: it represents the degenerate endpoint u=0.
Do not drop positivity or primitive coprimality in a reverse
construction.  The actual source remains the 048
SixthPowerSievedNestedCondition.

The preferred substantial result is that every eligible factor allocation
has at most one canonical center candidate across both branches, together
with a complete chart reconstruction theorem if the existing APIs permit it.

## Stopping boundary

These identities and uniqueness theorems alone do NOT prove a solution
exists or that no solution exists.  They are an exact compression of
the scalar problem, not a proof of FLT7.

After establishing the common monotone polynomial, explicitly identify
which unproved assertion would decide the equation

  P D q = 448*s^49

at source-supported allocations.  If it requires a genuinely global
Diophantine obstruction, report that as the remaining boundary.
No brute-force enumeration of astronomical endpoint ranges;
no recursive descent until one-step reconstruction is settled.
Legendre stays parked.

## Calibration

Verify algebra at:

- D=2, u=v=1: q=0, alternating residual=1, P 2 0=64;
- D=1, u=0: q=1, GN residual=1, P 1 1=64 (degenerate boundary);
- positive GN endpoints and ordered unequal alternating endpoints;
- midpoint and swapped-endpoint behavior;
- retained 048 factor allocations M=64002 (r=1) and
  M=1890024 (r=3), without inventing any scalar solution.

## Outcome classification

Outcome A: complete source-supported exclusion, genuine one-step
descent, or new terminal impossibility is proved.

Outcome B: a shared centered-polynomial theorem and canonical
endpoint uniqueness for both branches are kernel-checked; existence
and global exclusion remain open.

Outcome C: the proposed common polynomial bridge fails or
does not sharpen the exact scalar receiver beyond already-known facts.

All outcomes are acceptable.

## Validation and report

Follow focused build, new-declaration axiom audit, FLT Seven facade,
and root build.  Preserve the project headers and source audit.

Write

  lean/dk_math/docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/report-049.md

State the exact centered identities, monotonicity and uniqueness
theorems, source-indexed receiver equivalence (if obtained), what
provenance is retained, calibration/build/axiom outcomes, whether any
allocation or endpoint is actually excluded, Outcome A/B/C, and
the precise remaining arithmetic theorem.  Do not predesign 050.
