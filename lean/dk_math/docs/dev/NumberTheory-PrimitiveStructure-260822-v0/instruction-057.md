# instruction-057 — PRIM-L042 Triple-Product Shell Gate / Third-Order Product-Wave Localization Lean Judgment

## 0. Scope

Continue on branch:

```text
wip/number-theory-primitive-structure-260822-v2
```

Base the implementation on the current repository state, especially:

- `DkMath.NumberTheory.Legendre.ParitySafePairResidual` (PRIM-L041)
- `DkMath.NumberTheory.Legendre.Wave`
- `DkMath.NumberTheory.Legendre.LocalizedObstruction`

Do **not** extend the support hierarchy to general 4-tuples / k-tuples in this checkpoint.
The purpose of L042 is to stop the combinatorial lift at three distinct directions and use the actual square-shell size / product-wave geometry.

Suggested focused module:

```text
DkMath/NumberTheory/Legendre/ParitySafeTripleProductGate.lean
```

Add it to the `DkMath.NumberTheory.Legendre` facade.

---

## 1. PRIM-L042.1 — Canonical cube gate

For a residual triple incidence from L041, write

```text
p := paritySafeCanonicalSupportPrime n r
```

and use `paritySafeCanonicalResidualTripleIncidence_packet`.

Prove the shell-size packet, preferably as a reusable theorem:

```text
p < q
p < s
q < s
p * q * s ∣ n^2 + r
p * q * s ≤ n^2 + r
n^2 + r ≤ squareBody n
p^3 < p*q*s
p^3 < squareBody n
```

The strict `p^3 < p*q*s` should come from three **distinct ordered prime directions**, not from an analytic estimate.

Define a finite gate such as:

```lean
noncomputable def paritySafeTripleGatePrimes (n : ℕ) : Finset ℕ :=
  (squareAnchorOddActivePrimes n).filter
    (fun p => p ^ 3 < squareBody n)
```

with exact membership theorem.

Then prove:

```text
residual triple incidence
  -> canonical selected prime ∈ paritySafeTripleGatePrimes n
```

This is the first main compression: support-size `≥ 3` cannot be rooted at an arbitrary active prime.

---

## 2. PRIM-L042.2 — Active ordered triple keys

Define one canonical finite set of ordered active prime triples, for example:

```text
(p,q,s)
all active
p < q < s
p^3 < squareBody n
```

Nested pairs are fine if Lean ergonomics are better.
Do not introduce a general hypergraph abstraction.

Every L041 residual triple incidence must determine one member of this key set, with `p` the canonical selected prime.

Also expose the product modulus:

```text
m := p*q*s
```

and prove that the seat belongs to the existing generic product wave:

```text
r ∈ squareWaveOffsets n (p*q*s)
```

Use the L041 divisibility packet and existing `SquareOffset` membership; do not duplicate divisibility definitions.

---

## 3. PRIM-L042.3 — Third-order product-wave upper incidence

Define a finite **upper incidence set** consisting of

```text
(tripleKey, r)
```

where `r` is a square-wave hit for the triple product modulus.

Prove that the canonical residual triple incidence set from L041 injects / embeds into this upper incidence set.
Hence prove a finite upper ledger of the conceptual form

```text
paritySafeResidualPairMass n
  ≤ Σ triple ∈ paritySafeTripleGateTriples n,
      (squareWaveOffsets n (p*q*s)).card
```

If convenient, define the RHS as a named budget such as:

```text
paritySafeTripleProductWaveBudget n
```

and prove

```text
paritySafeResidualPairMass n ≤ paritySafeTripleProductWaveBudget n
```

This theorem is materially stronger than merely restating `p*q*s ∣ n^2+r`: it transposes the seat-side residual mass into a product-modulus occupancy ledger.

---

## 4. PRIM-L042.4 — Exact wave arithmetic and near/far split

For every active triple key, `p*q*s > 0`. Reuse the generic wave theorem:

```text
card_squareWaveOffsets_eq_div_add_carry
```

so the third-order budget rewrites to

```text
Σ triple,
  ((2*n)/(p*q*s) + squareWaveCarry n (p*q*s))
```

Define a bounded near/far split by the **actual square-window width**:

```text
near: p*q*s ≤ 2*n
far:  2*n < p*q*s
```

Prove the exact partition and budget decomposition if it stays local and clean.

For a near triple, prove the sharper canonical-prime gate:

```text
p^3 < 2*n
```

because `p^3 < p*q*s ≤ 2*n`.

For a far triple, reuse:

```text
card_squareWaveOffsets_le_one_of_two_mul_lt_modulus
```

or the equivalent carry theorem to prove:

```text
(squareWaveOffsets n (p*q*s)).card ≤ 1
```

Thus the third-order obstruction must split into:

```text
near triples rooted at very small canonical p (p^3 < 2*n)
+
far triples, each triple key hitting at most one square seat
```

Do not claim this by itself gives the universal cardinal inequality.

---

## 5. PRIM-L042.5 — Concrete witness `(n,r)=(16,17)`

Reuse / extend the L041 witness:

```text
16^2 + 17 = 273 = 3*7*13
```

Verify materially that:

```text
p = 3, q = 7, s = 13
3^3 < squareBody 16
2*16 < 3*7*13
```

and therefore this residual triple lies in the **far** triple-product regime.

Also verify the corresponding triple-product wave has cardinality `≤ 1` (exactly `1` is welcome if easy and informative).

This witness should show that the new near/far split is not vacuous and that the existing L041 triple is handled by the far one-hit beam.

---

## 6. Stronger-beam judgment

The report must answer explicitly:

1. Does every residual triple force the canonical selected prime into `p^3 < squareBody n`?
2. Can the entire `paritySafeResidualPairMass` be charged to a finite triple-product wave budget?
3. Can that budget be rewritten using the existing exact wave `div + carry` formula?
4. Do near triples satisfy the sharper gate `p^3 < 2*n`?
5. Do far triple keys have occupancy at most one?
6. Does this produce any **new universal bound strong enough** to close the L035/L036 frontier? If not, stop and say exactly what finite quantity remains uncontrolled.

Do not manufacture a Legendre theorem from the gate alone.

---

## 7. Outcomes

### Outcome A — EXACT TRIPLE-PRODUCT SHELL GATE / THIRD-ORDER WAVE LOCALIZATION

Use this if all of the following are Lean-proved:

- canonical cube gate;
- residual-to-triple-product-wave upper ledger;
- exact `div + carry` rewrite;
- near/far split;
- near `p^3 < 2*n` and far one-hit theorem.

### Outcome B — CUBE GATE / PRODUCT DIVISIBILITY ONLY

Use this if the local shell gate and product-wave membership are proved but the global finite ledger / near-far budget does not close cleanly.

### Outcome C — PROPOSED PRODUCT-WAVE LOCALIZATION IS FALSE

Use this if a concrete counterexample invalidates the proposed embedding or one-hit interpretation. Formalize the smallest practical counterexample and stop.

---

## 8. Report

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
  primitive-parity-safe-triple-product-shell-gate-260826.md
```

Record:

- exact public theorem surface;
- Outcome A/B/C;
- whether the cube gate is strict `<` or only `≤` in the final Lean statement;
- exact relationship between residual mass and the triple-product upper budget;
- near/far arithmetic;
- `(16,17)` witness;
- the remaining uncontrolled finite frontier.

---

## 9. Validation

Run at least:

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeTripleProductGate
lake build DkMath.NumberTheory.Legendre
git diff --check
```

Audit the new Lean source for trailing whitespace and forbidden placeholders (`sorry`, `admit`, `axiom`, `native_decide`).

No full repository build unless dependencies materially change.

---

## 10. Non-goals

Do not add in this checkpoint:

- general k-tuple / hypergraph APIs;
- fourth-order support hierarchy;
- PNT / Mertens / Rosser--Schoenfeld / Jacobsthal estimates;
- analytic sieve machinery;
- RH/CFBRC dependencies;
- descent claims;
- `LegendreConjecture` theorem without an actually proved universal provider.

The intended move is:

```text
L041 residual triple direction
        ↓
three-prime product divisor
        ↓
square-shell size gate p^3 < squareBody
        ↓
triple-product wave occupancy
        ↓
near: very small canonical p
far: one hit per triple key
```

Stop there and let Lean decide whether this third-order localization is genuinely stronger.