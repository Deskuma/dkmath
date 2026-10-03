# DkMath Research Connections — 2026-10-03

cid: `6ac0a596-64f0-83ee-bca3-723e780ff66d`
cid: `6ac0ab4e-9cf4-83ee-b4e3-7dedd3e7d6a8`
cdl: `codex://threads/01a101ab-fa58-7ac3-9bdb-d864215f6ad2`

Branch: **research/DkMath-ResearchConnections-261003-v0**

Base: **develop** at **f16282e5b44bd5fe5afa1a15d29f1598cae575cd**

## Mission

This campaign kernel-checks the reusable mathematical connections extracted by
the 2026-10-03 whole-repository research survey.

The survey's central structural proposal is to lift the Cosmic Formula / GN
view from a factorization statement

~~~text
(g + u)^d - u^d = g * GN d g u
~~~

into a reusable chain

~~~text
factorization
  -> finite-free norm / determinant
  -> lattice landing
  -> local ideal ownership
  -> power-image landing
  -> downstream descent or arithmetic receiver.
~~~

The campaign does **not** treat the survey itself as a proof.  Every promoted
claim must be re-expressed as a Lean theorem and accepted by the kernel.

## Frozen source state

The survey analyzed exactly the same commit from which this branch starts:

~~~text
f16282e5b44bd5fe5afa1a15d29f1598cae575cd
~~~

That alignment is intentional: source observations and implementation work
begin from one fixed repository state.

## Important de-duplication result: GN product degree already exists

The survey proposed the exponent-composition identity

~~~text
GN (a * b) x u
  = GN a x u * GN b (x * GN a x u) (u ^ a).
~~~

A production theorem already proves this over Nat:

~~~lean
DkMath.NumberTheory.GN_mul_degree
    {a b x u : Nat}
    (hx : 0 < x) :
    GN (a * b) x u
      = GN a x u * GN b (x * GN a x u) (u ^ a)
~~~

in:

~~~text
DkMath/NumberTheory/GNDegreeFactorization.lean
~~~

Therefore this branch must **not** add a duplicate GN_ab theorem.

A future checkpoint may strengthen this theorem only if an audit confirms that
the genuinely stronger cancellation-free statement over a commutative
semiring is absent.  Such a theorem would be a generalization of the existing
Nat theorem, not a new discovery of the product-degree identity.

## First implementation target

The first new kernel target is the survey's finite-free lattice landing
principle.

At matrix level over the integers, for a square matrix M, coordinate vector v,
and nonzero determinant D = det(M), the target is conceptually

~~~text
exists w, M * w = v

iff

for every coordinate i,
D divides (adjugate(M) * v)_i.
~~~

This is the higher-rank form of the information already used by
TraceOneLatticeLanding: norm/determinant divisibility alone records only an
aggregate index, whereas all adjugate coordinates retain the exact integral
lattice landing condition.

The implementation should first establish the smallest reusable matrix theorem.
A finite-free algebra wrapper may be added only after the matrix kernel is
stable and the required Mathlib Basis / LinearMap APIs are clear.

## Research connections to be kernel-checked

The campaign keeps the following candidates separate.

1. **Finite-free lattice landing** — adjugate / determinant coordinate
   criterion, then optional algebra wrapper.
2. **GN product-degree generic lift** — only if the CommSemiring,
   cancellation-free strengthening is not already present.
3. **Cyclic norm carrier** — multiplication by z - uT in a cyclic quotient,
   recovering z^n - u^n and hence the complete Cosmic Formula carrier.
4. **Prime cyclic glue** — integral fiber-product / congruence reconstruction
   and p-th-root gluing with all unit hypotheses exposed.
5. **Prime-shell Hensel** — general non-ramified simple-root lifting and exact
   depth construction.
6. **TraceOne residue type** — split / inert / ramified finite residue models,
   keeping common additive structure distinct from multiplication.
7. **Cyclotomic QR provenance lift** — element / relative-norm compatibility,
   stronger than scalar norm coincidence.
8. **FLT7 current aggregation** — parallel downstream work using the current
   carrier and current ownership cutoff, without reverting to historical
   packets.

Each checkpoint may reveal that part of the proposed mathematics already
exists.  In that case the correct outcome is to record and reuse it rather
than create parallel API.

## Existing infrastructure that must be reused

Before adding a theorem, audit the relevant production modules, especially:

~~~text
DkMath.Lib.Cosmic.*
DkMath.NumberTheory.GNDegreeFactorization
DkMath.NumberTheory.AKSBridge
DkMath.CFBRC.CyclotomicNorm
DkMath.Lib.NumberTheory.TraceOneLatticeLanding
DkMath.Lib.NumberTheory.TraceOnePowerLanding
DkMath.Lib.NumberTheory.ClassGroupTorsionBridge
DkMath.Lib.NumberTheory.ConjugatePrimeIdealOwnership
DkMath.Lib.NumberTheory.UnitPowerSector
~~~

Representation changes must preserve the information needed by downstream
theorems.  In particular:

~~~text
norm equality != element equality
norm divisibility != lattice divisibility
principal ideal p-th power != element p-th power
local ownership != global aggregation
unit removal != preservation of an additive descent chart
~~~

## Working rules

- Lean decides theorem validity.
- No `sorry`, `admit`, new `axiom`, or unsafe proof shortcut.
- Search for an existing theorem before implementing a new one.
- Prefer a small neutral theorem over a fixed-problem wrapper.
- Keep scalar norm, ideal norm, lattice coordinates, unit sectors, and element
  identities distinct.
- A finite computation may guide theorem design but is not a proof.
- Every checkpoint ends with focused build, relevant regression build, full
  build when practical, and `#print axioms` on new public endpoints.
- New production modules enter `DkMath.Lib` only after their API is stable.

## Non-claims

This branch does not claim:

- a new proof of FLT3 or FLT5;
- completion of FLT7;
- resolution of ABC, RH, Goldbach, Legendre, Collatz, or four-color;
- mathematical novelty merely because a connection is new inside DkMath;
- that the 2026-10-03 survey's Python/SymPy verification is a Lean proof.

The purpose is narrower and stronger: convert useful structural observations
into explicit, reusable, kernel-checked DkMath API.
