# instruction-004 — GNIP-004 successor gnomon preservation / firewall audit

## Goal

Determine whether the `n -> n+1` unit-gnomon growth admits a mathematically meaningful support-preservation law, with `30 -> 31` as the primary regression boundary.

This checkpoint is **not** a Legendre proof attempt.  It is a bounded structural audit that must distinguish:

```text
exact conservation law
exact anti-preservation / firewall law
cardinality coincidence only
no useful bridge
```

Do not claim a general inversion/projection theorem unless the Lean statements actually justify it.

## Read first

Production modules:

```text
DkMath/Gnomon/Algebra.lean
DkMath/Gnomon/CosmicBridge.lean
DkMath/NumberTheory/Legendre/GnomonBridge.lean
DkMath/NumberTheory/Legendre/PrimorialWheelSuccessor.lean
DkMath/NumberTheory/Legendre/Basic.lean
DkMath/NumberTheory/Legendre/OldSupportGcd.lean
DkMath/NumberTheory/Legendre/Frontier.lean
```

Prior stop-route audit:

```text
docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
  primitive-square-shell-wave-transport-audit-260825.md
```

That audit already established that the tautological rewrite

```text
(n+1)^2 + r = n^2 + (2*n+1+r)
```

does **not** provide a map from `squareOffsets (n+1)` back into `squareOffsets n`.
Do not repeat that route as if it were new.

---

## 1. Preferred production module

Create only if the results justify production theorems:

```text
DkMath/NumberTheory/Legendre/GnomonSuccessor.lean
```

Import the smallest existing sources necessary, preferably:

```text
DkMath.NumberTheory.Legendre.GnomonBridge
DkMath.NumberTheory.Legendre.PrimorialWheelSuccessor
```

Export from `DkMath.NumberTheory.Legendre` only if production theorems are obtained.

If the useful outcome is negative/audit-only, keep scratch evidence and the report without adding decorative production API.

---

## 2. Exact shell-growth balance

First certify the elementary cardinality growth in existing vocabulary:

```text
(squareOffsets (n+1)).card = (squareOffsets n).card + 2
```

or an orientation-equivalent theorem.

Relate this to the open-gnomon lengths:

```text
oddGnomon (n+1) = oddGnomon n + 2.
```

This is a bookkeeping identity only.  Do not call it support preservation yet.

---

## 3. Threshold seats

Reuse the existing prime-threshold theorem from `PrimorialWheelSuccessor`:

```text
(n+1) | r ↔ r = n+1 ∨ r = 2*(n+1)
```

inside the successor shell, under `Nat.Prime (n+1)`.

Introduce a small finite set only if it improves the proofs, for example:

```lean
def successorThresholdOffsets (n : ℕ) : Finset ℕ :=
  {n + 1, 2 * (n + 1)}
```

Prove, under the needed positivity/prime assumptions:

```text
successorThresholdOffsets n ⊆ squareOffsets (n+1)
card (successorThresholdOffsets n) = 2
```

and connect membership exactly to threshold-prime reservation.

Then define or characterize the threshold-removed successor shell:

```text
squareOffsets (n+1) \ successorThresholdOffsets n
```

and prove its cardinality equals the old shell cardinality:

```text
card (...) = card (squareOffsets n).
```

Interpretation:

```text
successor shell gains 2 seats
new threshold prime controls exactly 2 seats
removing those seats restores the old shell cardinality
```

This is an exact cardinal balance, not yet a support transport theorem.

---

## 4. Canonical order-preserving seat reindex

Test the most natural bijection suggested by the cardinal balance.

For old offset `r`, define a candidate such as

```lean
def successorThresholdInsert (n r : ℕ) : ℕ :=
  if r < n + 1 then r else r + 1
```

The intended map skips the threshold seat `n+1`; the terminal threshold seat `2*(n+1)` remains excluded automatically by the old upper bound.

Attempt to prove:

```text
SquareOffset n r
  -> successorThresholdInsert n r ∈
       squareOffsets (n+1) \ successorThresholdOffsets n
```

and preferably an exact finite-set image equality / bijection.

If a simpler existing Finset equivalence API is available, use it.  Do not introduce a large custom equivalence framework merely to prove cardinality already known from §3.

---

## 5. Main candidate: same-offset common-support firewall

This is the most important new structural test.

From

```text
(n+1)^2 + r = (n^2 + r) + oddGnomon n
```

prove a common-divisor consequence such as:

```lean
theorem dvd_oddGnomon_of_dvd_adjacent_square_points
    {n r q : ℕ}
    (hold : q ∣ n^2 + r)
    (hnew : q ∣ (n+1)^2 + r) :
    q ∣ DkMath.Gnomon.oddGnomon n
```

A stronger gcd identity is preferred if it is cleanly supported by existing Nat gcd API:

```text
gcd (n^2+r) ((n+1)^2+r)
  = gcd (n^2+r) (oddGnomon n).
```

Do not spend excessive engineering effort on the exact gcd equality if the divisibility firewall states the same usable content.

Then derive a prime-support form:

```text
if q is an old prime direction and q does not divide oddGnomon n,
then q cannot cover the same offset at both anchors.
```

This is an **anti-preservation / persistence firewall**, not a full support transport theorem.

---

## 6. Candidate reindex firewall

For `successorThresholdInsert`, compute the exact point displacement.

Expected split:

```text
r < n+1:
  ((n+1)^2 + insert(r)) - (n^2+r) = oddGnomon n

n+1 ≤ r:
  ((n+1)^2 + insert(r)) - (n^2+r) = 2*(n+1)
```

Prefer subtraction-free additive equalities in Nat.

Derive the corresponding common-divisor restrictions:

```text
lower region: common prime support must divide oddGnomon n
upper region: common prime support must divide 2*(n+1)
```

This identifies exactly which channels can persist under the most natural cardinality-preserving seat reindex.

---

## 7. Required `30 -> 31` audit

Kernel-check the concrete boundary `n=30`, `q=31`.

Required exact arithmetic:

```text
oddGnomon 30 = 61
oddGnomon 31 = 63
card (squareOffsets 30) = 60
card (squareOffsets 31) = 62
```

For the threshold-prime transition:

```text
primeScalesUpTo 31 = insert 31 (primeScalesUpTo 30)
```

and the threshold seats in the `31` shell are exactly:

```text
31, 62.
```

After removing those two seats, cardinality must be `60`.

### Support-preservation falsification test

Do not assume the canonical reindex preserves coverage.  Test it.

Try to kernel-check at least one explicit mismatch in each direction if convenient.  Useful candidates are:

```text
old n=30, r=6  -> successor inserted offset 6
old point 906 is old-basis covered;
successor point 967 is old-basis unreserved.

old n=30, r=7  -> successor inserted offset 7
old point 907 is old-basis unreserved;
successor point 968 is old-basis covered.
```

Use existing `SquareOffsetCovered`, `SuccessorOldBasisReserved`, support-disjointness, primality, or `native_decide` only where repository policy permits.  These are regression witnesses, not general theorems.

If either suggested witness is awkward because of noncomputability/API shape, choose another concrete mismatch and report it.

### Stronger `30 -> 31` firewall

For lower-half same-offset / inserted seats, common old-prime support must divide `61`.
Because `61` is prime and every old prime satisfies `q ≤ 30`, conclude no old prime direction can persist identically there.

For the upper inserted region, common support must divide `62 = 2*31`.  With `q ≤ 30` prime, the only possible persistent old prime is `2`.

Formalize these specializations if they remain small and robust.

---

## 8. Relation to the historical rational inversion projection

Audit whether current production source contains the historical continuous projection API

```text
Pi(P) = -P/(P+1)
U(P)  =  1/(P+1)
Pi(P)+1 = U(P)
```

or an exact modern equivalent.

Important scope rule:

- If a production API exists and an exact bridge to this discrete gnomon transition is immediate, state/prove the smallest bridge.
- If it does not exist on this branch, or the relation is only conceptual, record **NOT CONNECTED** in the report.
- Do **not** introduce a new `ℝ`/`ℚ` analytic projection theory in GNIP-004 merely to force a connection.

The current checkpoint is integer/finitary first.

---

## 9. Decision questions

The report must answer explicitly:

1. Is the `+2` shell growth exactly balanced by the two threshold-prime seats?
2. Does the natural threshold-skipping bijection preserve `SquareOffsetCovered` / old-basis reservation?
3. If not, what exact arithmetic controls common support across the transition?
4. Does `oddGnomon n` act as a firewall for same-offset support persistence?
5. At `30 -> 31`, which old prime channels can persist under the canonical reindex?
6. Does any result here imply full-cover propagation or full-cover failure?  Expected answer unless a genuinely new theorem appears: **no**.
7. Is the historical rational inversion projection mathematically connected by current production API, or still a separate observer?
8. Is there a justified GNIP-005, and if so what is its single bounded target?

---

## 10. Outcome policy

Use one of:

```text
A — STRUCTURAL FIREWALL FOUND
    Exact +2 / two-seat balance established, natural reindex audited,
    and a nontrivial common-support firewall controlled by oddGnomon is proved.

B — CARDINAL BALANCE ONLY
    +2 / two-seat balance is exact but no useful support theorem beyond
    existing successor decomposition is obtained.

C — NO NEW LEVERAGE / PRIOR STOP ROUTE CONFIRMED
    Results reduce entirely to the previous transport audit and existing
    PrimorialWheelSuccessor facts.
```

A does not mean Legendre is proved.  It means a new exact transition invariant/obstruction has been isolated.

---

## 11. Validation

If production Lean is added, run focused builds for the new module and:

```text
lake build DkMath.NumberTheory.Legendre
lake build DkMath.Gnomon
```

Also:

```text
git diff --check
```

Scan changed Lean files for `sorry`, `admit`, and `axiom`.

Create:

```text
docs/dev/NumberTheory-Gnomon-Inversion-Projection-260914-v0/report-004.md
```

Include theorem inventory, concrete 30→31 regressions, negative/counterexample results, and the final route judgment.
