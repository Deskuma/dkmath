# PUU-L030 — Mixed-Radix Coordinate Equivalence / Information-Gain Audit

## 0. Status / purpose

PUU-L029 completed the exact static/dynamic identification

```text
old representative      r_S(n) = n mod M
fresh-prime digit       d_q(n) = (n / M) mod q
enlarged representative = r_S(n) + d_q(n) * M
Pplus                   = d_q(n) in ZMod q
```

for `M = finitePrimeBasisProduct S` and fresh prime `q`.

This checkpoint is an **anti-maze / information-gain audit**.  Do not add another layer of quotient, carry, monodromy, or affine notation unless it is needed by the audit itself.

The central question is:

> Does the mixed-radix transport impose any genuine restriction on the finite fresh-prime fiber, or is it a complete reparameterization of the already-known `q` raw lift seats?

A negative result is a successful outcome if it is proved exactly.  The objective is to determine whether the current provider dynamics already contains an independent coverage obstruction or merely canonical coordinates.

Remain entirely inside `DkMath.NumberTheory.PrimorialUniverse`.  Do not import Legendre consumers.

Preferred module:

```lean
DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseMixedRadixAudit
```

Preferred import:

```lean
import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseMixedRadixTransport
```

Export through `DkMath.NumberTheory.PrimorialUniverse` and update the facade docstring.

---

## 1. Raw mixed-radix coordinate domain

For a fixed old basis `S` and fresh prime `q`, the canonical enlarged period is

```text
q * M,
M := finitePrimeBasisProduct S.
```

Introduce a lightweight coordinate predicate or finite type for pairs `(r,d)` satisfying

```text
r < M
d < q.
```

Avoid a large structure hierarchy.  A predicate plus existence/uniqueness theorems is acceptable.

The decoder is the existing raw lift expression

```text
r + d * M
```

or `primeBasisWheelLift S r d`.

The encoder of `x < q*M` should be

```text
r := x % M
d := x / M
```

(note that `d < q` under the enlarged-period bound, so no extra `% q` is needed inside one enlarged period).

---

## 2. Exact encode/decode theorem

Prove the Euclidean mixed-radix decomposition for every

```text
x < q * M:
```

```text
x = (x % M) + (x / M) * M
x % M < M
x / M < q.
```

Then prove uniqueness:

```text
r₁ < M, d₁ < q,
r₂ < M, d₂ < q,
r₁ + d₁*M = r₂ + d₂*M
→ r₁ = r₂ ∧ d₁ = d₂.
```

Preferred public theorem names:

```lean
freshPrimeMixedRadix_exists_unique
freshPrimeMixedRadix_eq_iff
```

or equivalent clear names.

This should establish that one enlarged period is exactly the rectangular finite grid

```text
[0,M) × [0,q).
```

Do not invoke CRT when ordinary Euclidean division is sufficient.

---

## 3. Canonical orbit is surjective onto every raw digit over a fixed old representative

Fix any `r < M` and any `d < q`.

Use the explicit witness

```text
n := r + d*M.
```

Prove:

```text
squareAnchorPhaseRepresentative S n = r
squareAnchorFreshPrimeBlockDigit S q n = d
squareAnchorPhaseRepresentative (insert q S) n = primeBasisWheelLift S r d
```

under the usual finite-basis / fresh-prime hypotheses.

Package the semantic statement:

```lean
forall_raw_lift_digit_realized_by_canonical_orbit
```

Conceptually:

```text
∀ r < M, ∀ d < q,
  ∃ n < q*M,
    oldRepresentative(n) = r ∧
    freshDigit(n) = d.
```

Prefer the explicit witness `r + d*M` and prove its enlarged-period bound.

This is the key information-gain audit theorem.

---

## 4. Fixed-old-representative digit orbit is complete

For fixed `r < M`, prove that

```text
r,
r + M,
r + 2*M,
...
r + (q-1)*M
```

realize exactly the digits

```text
0,1,...,q-1.
```

Equivalent acceptable theorem shapes:

```lean
squareAnchorFreshPrimeBlockDigit_lift
```

with

```text
digit_q(r + d*M) = d
```

for `r < M`, `d < q`, or a Finset image/equality theorem if it remains concise.

Do **not** prove a second cardinality theorem for the same fact unless it clarifies the audit.

Mathematical reading:

> The dynamic monodromy visits every raw fresh-prime lift seat over every old coordinate.  The transport itself forbids no digit.

---

## 5. Reservation classification in mixed-radix coordinates

Connect the coordinate grid back to the existing reservation layer.

For `r < M`, `d < q`, prove a theorem equivalent to

```text
ReservedByPrimeBasis (insert q S) (r + d*M)
↔
ReservedByPrimeBasis S r ∨ q ∣ (r + d*M).
```

Use existing `ReservedByPrimeBasis`, fresh insertion, periodicity, and raw-lift APIs.  Do not recreate wheel theory from scratch.

For an old wheel survivor `r`, simplify this to

```text
ReservedByPrimeBasis (insert q S) (r + d*M)
↔ q ∣ (r + d*M).
```

and connect the right side to the existing unique deleted lift index.

Thus over an old survivor:

```text
q digits
  = 1 deleted/reserved digit
  + (q-1) surviving digits.
```

This theorem should explicitly reuse the L007/L008 semantics rather than present it as new replication information.

---

## 6. Information-gain verdict theorem / report

The Lean module cannot literally prove a meta-level statement such as “no future theorem can follow”.  Instead, formalize the strongest exact finite statement supporting the audit:

```text
for every allowed old coordinate r and every fresh digit d,
there exists a canonical moving anchor n realizing exactly (r,d).
```

Therefore the current mixed-radix transport alone imposes no forbidden raw coordinate in one enlarged period.

The report must classify the result explicitly as one of:

### Outcome A — NEW-OBSTRUCTION-FOUND

Only if the implementation discovers a theorem, stated independently of square-shell escape, that excludes some otherwise admissible coordinate/reservation pattern.

If this occurs, stop and report the exact new obstruction before extending the module.

### Outcome B — COORDINATE-COMPLETE / NO-OBSTRUCTION-YET

Expected if the encode/decode and realization theorems show that every raw `(r,d)` coordinate is dynamically realizable and reservation is exactly the already-known wheel deletion rule.

This is a successful audit result.  It means:

```text
L016–L029 provide a complete and useful coordinate system,
but transport alone has not yet produced the missing coverage obstruction.
```

Do not disguise Outcome B as progress toward prime existence.  Record it plainly.

---

## 7. Consequence for the roadmap

If Outcome B is obtained, close the current “pure coordinate refinement” route.

The next research step must add a genuinely new interaction, not another encoding identity.  Candidate directions to evaluate **after** the audit are:

1. interaction of the moving square-value coordinate `n^2 mod M` with the anchor mixed-radix digit;
2. simultaneous transport of a **window of offsets** rather than one anchor coordinate;
3. basis-growth compatibility involving multiple fresh primes at once;
4. reconnecting Unit Universe / PowerSwap only if it introduces an invariant not equivalent to the current finite coordinates.

Do not choose among these inside L030 unless a theorem found during the audit clearly selects one.

---

## 8. Visible regression

Use

```text
S = {2,3}
M = 6
q = 5
```

and preferably the old coordinate `r = 4`.

Show that

```text
d = 0,1,2,3,4
n = 4,10,16,22,28
```

realize all five raw digits exactly, and that the enlarged representatives are the corresponding seats

```text
4,10,16,22,28  in [0,30).
```

If useful for the reservation classification, choose an old survivor such as `r = 1` and show the five raw lifts

```text
1,7,13,19,25
```

with exactly the already-known fresh-5 deletion at `25`.

The regression should use the new audit APIs rather than only `norm_num`.

---

## 9. STOP conditions

Do not add:

- Legendre imports or square-shell escape statements;
- Jacobsthal / wheel-gap estimates;
- primality/compositeness claims for neutral seats;
- PNT, RH, analytic density;
- PowerSwap / GN / CosmicFormula;
- prime powers;
- least-period claims;
- another carry/quotient/radius/center synonym;
- arbitrary asymptotic counting.

If the audit yields Outcome B, stop the coordinate route and say so.

---

## 10. Report

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimorialUnitUniverse-260827-v0/
primorial-unit-universe-mixed-radix-information-audit-260828.md
```

The report must contain:

1. exact encode/decode result;
2. exact raw-coordinate realization theorem;
3. reservation classification;
4. whether any forbidden coordinate was found;
5. explicit Outcome A or Outcome B;
6. what this means for the original Primorial Unit Universe objective;
7. the next mathematically justified direction, without pre-committing to another coordinate lemma.

## A+ rubric

PUU-L030 is A+ if it gives an exact, Lean-checked answer to the information-gain question, including a negative answer if that is what the finite geometry proves.
