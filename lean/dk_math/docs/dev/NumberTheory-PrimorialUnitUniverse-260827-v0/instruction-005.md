# PUU-L005 — Finite Prime-Scale Synchronization / Minimal Reservation Period

## 0. Current state

PUU-L001 through PUU-L004 are complete.

- L001 fixed a finite ordinary-prime basis `S`, its product `finitePrimeBasisProduct S`, reservation by divisibility, and the Euclidean escape point.
- L002 fixed unit-relative natural coordinates and showed that synchronized refinement can turn a prime coordinate into a nonprime coordinate without absorbing the old prime factor.
- L003 proved that a coprime two-unit synchronization has the exact common-coordinate fiber `(a*t,b*t)`.
- L004 closed the two-unit intersection classification: complete synchronization, partial synchronization, or no positive common lattice point.

This checkpoint leaves the two-unit layer and begins the finite multi-prime synchronization layer.

## 1. Goal

Show that the existing product of a finite prime basis is the canonical minimal common synchronization period of all prime scales in that basis, in the divisibility order.

Do **not** introduce primorial wheel survivor sets yet.  First fix the period itself and the exact periodicity of the reservation sheet.

The mathematical picture is:

```text
finite prime basis S
        ↓
M(S) = ∏ p∈S p
        ↓
every p∈S divides M(S)
        ↓
if every p∈S divides T, then M(S) divides T
        ↓
M(S) is the minimal common prime-scale period
        ↓
reservation pattern repeats modulo M(S)
```

For an initial prime basis this is the primorial period, e.g.

```text
{2,3}       -> 6
{2,3,5}     -> 30
{2,3,5,7}   -> 210
```

## 2. Suggested module

Create:

```text
DkMath/NumberTheory/PrimorialUniverse/FinitePrimeSynchronization.lean
```

Import the existing L001/L004 surface only as needed.  Prefer reusing
`IsFinitePrimeBasis`, `finitePrimeBasisProduct`, and `ReservedByPrimeBasis`
rather than introducing duplicate prime-basis/product definitions.

Add the module to:

```text
DkMath/NumberTheory/PrimorialUniverse.lean
```

and therefore to the existing public facade path.

## 3. Minimal vocabulary

A small predicate is sufficient:

```lean
def IsCommonMultipleOfPrimeBasis (S : Finset ℕ) (T : ℕ) : Prop :=
  ∀ p ∈ S, p ∣ T
```

Name may be adjusted if an existing Mathlib/DkMath name is clearly better.

Do not define a generic lattice/module abstraction.

## 4. Required theorem layer

### 4.1 Product is a common period

Reuse the existing member-divides-product theorem where possible.

Target shape:

```lean
theorem finitePrimeBasisProduct_isCommonMultiple
    {S : Finset ℕ} :
    IsCommonMultipleOfPrimeBasis S (finitePrimeBasisProduct S)
```

This theorem should not require `IsFinitePrimeBasis S`; membership alone is enough for divisibility into a finite product.

### 4.2 Minimality in divisibility order

For a finite prime basis, prove that any simultaneous period is divisible by the product.

Target shape:

```lean
theorem finitePrimeBasisProduct_dvd_of_commonMultiple
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) {T : ℕ}
    (hT : IsCommonMultipleOfPrimeBasis S T) :
    finitePrimeBasisProduct S ∣ T
```

This is the main theorem of PUU-L005.

The proof must use the fact that distinct members of a `Finset` of primes are pairwise coprime, so their product divides every common multiple.  Do not replace this with a theorem about infinitude of primes or analytic information.

If Mathlib already exposes a direct theorem for a finite product of pairwise-coprime divisors, use it.  Otherwise prove the result by finite induction, keeping the proof local and reusable.

### 4.3 Exact minimal-period characterization

Package the two directions as an iff:

```lean
theorem finitePrimeBasisProduct_dvd_iff_commonMultiple
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) {T : ℕ} :
    finitePrimeBasisProduct S ∣ T ↔
      IsCommonMultipleOfPrimeBasis S T
```

This is the preferred consumer theorem: `M(S)` is the least synchronization period with respect to divisibility.

Do not claim leastness under ordinary `≤` unless separately justified and useful.  Divisibility is the intended ordering here.

## 5. Reservation-sheet periodicity

Let:

```text
M := finitePrimeBasisProduct S
```

For each `p ∈ S`, `p ∣ M`, hence adding any multiple of `M` does not change whether `p` divides a seat.

Prove an exact periodicity theorem, preferably first for an arbitrary natural multiplier `k`:

```lean
theorem reservedByPrimeBasis_add_mul_period_iff
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    (n k : ℕ) :
    ReservedByPrimeBasis S
        (n + k * finitePrimeBasisProduct S) ↔
      ReservedByPrimeBasis S n
```

If a cleaner orientation is easier in Lean (`n + M*k`, `k*M + n`, etc.), choose one canonical public theorem and optionally give simp aliases.

Also expose the survivor/non-reserved form by negation:

```lean
theorem not_reserved_add_mul_period_iff ... :
    ¬ ReservedByPrimeBasis S
        (n + k * finitePrimeBasisProduct S) ↔
      ¬ ReservedByPrimeBasis S n
```

This is the first exact theorem saying that the finite reservation sheet repeats with period `M(S)`.

The basis-prime hypothesis is acceptable here because it gives nonzero/nonunit semantics and is already the branch contract, even if the raw divisibility periodicity could be proved under weaker assumptions.

## 6. Optional lcm bridge

Only if Mathlib's API is clean and the bridge is short, add a theorem identifying the product with a finite-lcm construction for a prime basis.

This is optional.

The mandatory semantic statement is the divisibility iff from §4.3.  Do not spend the checkpoint fighting a particular `Finset.lcm` API if the least-common-period theorem is already exact.

## 7. Regressions

Add small arithmetic regressions for the canonical first prime bases:

```text
{2,3}       -> product 6
{2,3,5}     -> product 30
{2,3,5,7}   -> product 210
```

L001 already contains the `{2,3}` product theorem, so reuse it or add only missing regressions.

Also add at least one visible periodicity example, for example that the `{2,3,5}` reservation status at `7` agrees with the status at `37 = 7 + 30` (both survivors), or another similarly small check.  Keep examples subordinate to the general theorem.

## 8. Semantic interpretation to preserve in docstrings/report

The intended reading is:

> A finite family of prime-scale reservation patterns has a smallest common period in the divisibility sense.  Because the scales are distinct primes, that period is their product.  The old-prime reservation sheet therefore repeats exactly modulo this finite product.

For an initial segment of primes this product is the ordinary primorial.

Do not yet claim:

- a reduced-residue survivor set has been defined,
- reflection symmetry has been proved,
- the next prime deletes exactly one lift,
- a fractal/self-similar wheel theorem has been proved,
- Legendre follows.

This checkpoint fixes only the finite common period and repetition law.

## 9. Stop boundary

Do **not** proceed in PUU-L005 to:

- canonical `primeBasisUpTo n` / initial-prime enumeration unless a tiny helper is unavoidable,
- reduced residues / Euler phi counts,
- wheel reflection,
- next-prime lift / unique deletion / replication,
- arbitrary rational/irrational unit ratios,
- PowerSwap,
- GN / CosmicFormula,
- Legendre / square anchors,
- PNT / RH / analytic sieve.

Stop once the minimal finite prime synchronization period and reservation periodicity are public and reported.

## 10. Verification / report

Create a report under the current docs directory summarizing:

- definitions added,
- the divisibility-minimality proof,
- reservation periodicity,
- regressions,
- semantic boundary.

Use the normal project verification gates already established for this branch.