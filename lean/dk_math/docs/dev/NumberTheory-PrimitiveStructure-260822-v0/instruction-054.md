# instruction-054 — PRIM-L039 Two-Adic Möbius Pairing / Odd-Quotient Correction Lean Judgment

Date: 2026-08-26
Branch: `wip/number-theory-primitive-structure-260822-v2`
Environment: Lean / Mathlib v4.32.2

## 0. Purpose

PRIM-L038 opened every parity-safe active wave occupancy as an exact signed Möbius divisor-floor ledger over divisors of `2*n`.

Do **not** proceed by merely extracting the `d = 1` term from that ledger.  The next checkpoint must use the special modulus `2*n` materially.

The target is to fold the `2`-adic part of the Möbius ledger exactly: pair the divisor channels corresponding to `d` and `2*d`, or prove an equivalent odd-filter Möbius identity, so that the prime `2` disappears from the correction term.

Conceptually the desired normal form is

```text
parity-safe wave occupancy
  = raw odd quotient count
    + signed correction from odd divisors of n
```

with the signed correction proved nonpositive.

This checkpoint is proof-backed reconnaissance.  Do not add analytic estimates, PNT, Mertens bounds, Jacobsthal bounds, RH/CFBRC, or a general sieve framework.

## 1. New module

Create, preferably:

```text
DkMath/NumberTheory/Legendre/ParitySafeMobiusOddCorrection.lean
```

Import at least:

```lean
import DkMath.NumberTheory.Legendre.ParitySafeMobiusWave
```

Add the module to the `DkMath.NumberTheory.Legendre` facade.

## 2. Raw odd quotient interval

For the L037 quotient endpoints

```text
A(n,q) = (n^2) / q
B(n,q) = (n^2 + 2*n) / q
```

define the unfiltered odd quotient interval, for example:

```lean
noncomputable def paritySafeOddRawQuotientInterval
    (n q : ℕ) : Finset ℕ :=
  (Finset.Ioc ((n ^ 2) / q) ((n ^ 2 + 2 * n) / q)).filter Odd
```

Prove the exact containment

```text
paritySafeReducedQuotientInterval n q
  ⊆ paritySafeOddRawQuotientInterval n q.
```

Also prove an exact cardinal formula for the odd raw interval.  A formula equivalent to

```text
rawOdd.card
  = ((B + 1) / 2) - ((A + 1) / 2)
```

is acceptable.

The theorem must be finite arithmetic; do not replace it by an asymptotic or inequality-only statement.

## 3. Exact odd-filter Möbius ledger

The main theorem must remove the prime `2` from the Möbius correction exactly.

Preferred mathematical form:

```text
# {k ∈ (A,B] : gcd(2*n,k)=1}
  = # {k ∈ (A,B] : Odd k}
    + OddCorrection(n,A,B)
```

where `OddCorrection` is a signed `ℤ` sum over odd divisors of `n` different from `1`.

A direct literal pairing theorem of the form

```text
Σ D ∣ 2*n, μ(D) * Δ(D)
  = Σ d ∣ n, Odd d,
      μ(d) * (Δ(d) - Δ(2*d))
```

is ideal.

However, if the Mathlib Möbius multiplicativity API makes literal divisor pairing unnecessarily brittle, the following equivalent proof route is explicitly acceptable:

1. use
   `Coprime (2*n) k ↔ Coprime n k ∧ Odd k`;
2. perform Möbius inclusion-exclusion only on divisors of `n`, inside the odd-filtered interval;
3. prove that this signed sum is equal to the L038 divisor-floor sum because both equal the same reduced-residue cardinality;
4. then isolate the `d = 1` odd raw term exactly.

Do not leave the relation to the L038 ledger implicit.

## 4. Odd-multiple channel

Introduce an exact finite count for one divisor channel, for example

```text
odd multiples of d in (A,B]
```

and, for odd positive `d`, connect it to the paired floor difference

```text
(B / d - A / d)
  - (B / (2*d) - A / (2*d)).
```

An equivalent Nat-safe cardinal identity is acceptable if the direct subtraction normal form is awkward.

The point is to prove that the `d` / `2d` pair leaves precisely the **odd multiples of d**.

## 5. Wave specialization and signed correction

Define a wave-level signed correction, for example

```lean
noncomputable def paritySafeOddMobiusCorrection (n q : ℕ) : ℤ := ...
```

and prove an exact decomposition for active `q`:

```text
((paritySafeActiveWaveOffsets n q).card : ℤ)
  = (paritySafeOddRawQuotientInterval n q).card
    + paritySafeOddMobiusCorrection n q.
```

The correction must no longer contain the prime-`2` parity channel as an independent divisor obstruction.  It should represent only exclusion caused by the anchor-side odd divisor structure.

## 6. Mandatory sign theorem

Prove

```text
paritySafeOddMobiusCorrection n q ≤ 0
```

for every active `q`.

This should be proved from the exact set containment / cardinal difference, not from a crude absolute-value bound on Möbius sums.

Also prove a strictness characterization or at least a clean one-direction theorem showing that the correction is strictly negative when the raw odd quotient interval contains an odd quotient not coprime to `n`.

Preferred exact form if it closes cleanly:

```text
paritySafeOddMobiusCorrection n q < 0
  ↔ ∃ k ∈ paritySafeOddRawQuotientInterval n q,
      ¬ Nat.Coprime n k.
```

A slightly weaker but still material implication is acceptable if the exact iff becomes API noise.

## 7. Concrete strict-correction witness

Lean-check the supplied witness

```text
n = 6
q = 5
A = 36 / 5 = 7
B = 48 / 5 = 9
raw odd quotient interval = {9}
gcd(12,9) = 3
reduced quotient interval = ∅
```

Require production theorems showing at least:

```text
5 ∈ squareAnchorOddActivePrimes 6
(paritySafeOddRawQuotientInterval 6 5).card = 1
(paritySafeReducedQuotientInterval 6 5).card = 0
paritySafeOddMobiusCorrection 6 5 = -1
```

This witness is important: it proves the correction is not identically zero and identifies its meaning as anchor-divisor exclusion after parity has already been removed.

## 8. Global upper ledger

If it remains thin after the local work, add the global consequence

```text
paritySafeIncidenceCount n
  ≤ Σ q ∈ squareAnchorOddActivePrimes n,
      (paritySafeOddRawQuotientInterval n q).card.
```

Optionally define the raw odd-wave bound and connect the duplicate budget to it.

Do **not** claim that this upper bound proves the L035 universal cardinal inequality unless Lean actually proves that implication with no new external hypothesis.

## 9. Stronger-beam judgment

The report must answer explicitly:

1. Did the `2*n` Möbius ledger collapse exactly to odd divisor channels of `n`?
2. Is the prime `2` completely absent from the remaining signed correction?
3. Is the correction universally nonpositive?
4. Is strict negativity exactly or materially characterized by odd quotient factors sharing anchor divisors?
5. Does the resulting raw odd-wave upper bound materially improve the L035/L036 frontier, or is a new universal estimate still missing?

## 10. Outcome classification

Use one of:

### Outcome A — EXACT TWO-ADIC FOLD / NONPOSITIVE ODD-DIVISOR CORRECTION

Require all of:

- exact odd raw interval;
- exact connection to the L038 Möbius ledger;
- parity / prime-`2` channel folded away;
- exact wave = raw odd + correction decomposition;
- correction `≤ 0`;
- `(6,5)` strict-correction witness.

### Outcome B — ODD-RAW DECOMPOSITION ONLY

Use if the raw odd decomposition and sign theorem close, but literal/equivalent Möbius pairing with L038 remains incomplete.

### Outcome C — NO MATERIAL TWO-ADIC COLLAPSE

Use if the new API is only a rename/subset bound and does not expose a genuinely smaller signed correction world.

## 11. Stop boundary

Do not continue in this checkpoint to:

- analytic estimates for the correction;
- PNT / Mertens / Rosser-Schoenfeld;
- Jacobsthal bounds;
- generic sieve libraries;
- graph / matching abstractions;
- descent;
- RH/CFBRC;
- `LegendreConjecture` theorem.

After the exact two-adic fold is Lean-checked, stop and report whether the residual correction is now genuinely an odd-anchor-divisor problem.

## 12. Validation

Run:

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeMobiusOddCorrection
lake build DkMath.NumberTheory.Legendre
git diff --check
```

Also audit the new Lean source for trailing whitespace and forbidden placeholders:

```text
sorry
admit
axiom
native_decide
```

No full repository build is required unless an unexpected dependency change occurs.

## 13. Report

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
  primitive-parity-safe-mobius-two-adic-odd-correction-260826.md
```

Record the exact theorem surface, the `(6,5)` witness, the Outcome classification, and the remaining arithmetic frontier.
