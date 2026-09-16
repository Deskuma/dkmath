# MG-000 review — two-stage prime transport kernel

cid: `6aa763a7-1a14-83e8-9041-1029d978663c`

## Verdict

**APPROVED — MG-000 is a sound production base for MG-001.**

No repair checkpoint is required before finite-path generalization.

Reviewed production files:

```text
DkMath/NumberTheory/MultiGauge/Basic.lean
DkMath/NumberTheory/MultiGauge/PrimeTransport.lean
DkMath/NumberTheory/MultiGauge.lean
report-000.md
```

---

## 1. Stage semantics

`GNGaugeStage d` stores exactly the intended arithmetic coordinates:

```text
x
u
Nat.Coprime x u
```

with

```text
gnValue = GTail d 1 x u
value   = x * gnValue.
```

The predicates

```text
PrimeCaught q s := q | s.value
PrimeEscapes q s := not (q | s.value)
```

faithfully encode the campaign vocabulary.

Although the names say `Prime`, the definitions themselves do not require a `Nat.Prime q` field. This is acceptable: primality is required only by theorems that use prime divisibility of a product.

---

## 2. Transition semantics

`GNGaugeTransition d` freezes the intended balance law

```text
second.value * denominator = first.value * numerator.
```

This realizes the intended support interpretation:

```text
numerator   = possible source of newly visible prime support
denominator = possible sink of previously visible prime support.
```

The positive coefficient fields are not yet used in MG-000 proofs. This is not a defect. Retain them for path composition and future concrete normalization bridges; they prevent degenerate zero-coefficient transition packets from becoming canonical witnesses.

---

## 3. Prime transport theorem audit

The two elementary localization theorems are exactly justified by the balance law and `Nat.Prime.dvd_mul`:

```text
q | second.value
-> q | first.value OR q | numerator

q | first.value
-> q | second.value OR q | denominator.
```

The derived escape transport theorems are therefore sound:

```text
escape first + q ∤ numerator
-> escape second

escape second + q ∤ denominator
-> escape first.
```

Outside both transition coefficients, visibility and escape are both conserved by iff.

This is the correct two-stage induction atom for MG-001.

---

## 4. Boundary / GN channel audit

The production theorem

```text
PrimeCaught q s
<->
q | s.x OR q | s.gnValue
```

correctly exposes the two channels of the stage observer.

More importantly, the implementation proved the stronger reusable theorem

```text
q | s.x
q | s.gnValue
1 <= d
-> q | d
```

without requiring `q` prime.

This is stronger and cleaner than the minimum MG-000 target. It correctly reuses

```text
DkMath.CosmicFormula.gcd_GN_eq_gcd_of_one_le
```

rather than re-proving the GTail gcd firewall.

Thus for any `q` with `q ∤ d`, simultaneous boundary/GN occupancy is impossible.

---

## 5. Architecture audit

Approved properties:

```text
Generic MultiGauge has no ABC / FLT / Legendre dependency.
No Norm / Eisenstein / TraceOne dependency was introduced.
The public MultiGauge facade exposes only the MG-000 front half.
No existing GTail/GN theorem ownership was moved.
No broad DkMath root-facade integration was forced.
No sorry / admit / new axiom was introduced.
```

The reported focused builds and `git diff --check` are sufficient for this checkpoint.

---

## 6. What MG-001 should add

MG-001 should now formalize finite composition of the same transition law.

The preferred mathematical invariant is the telescoped path balance.

For a path

```text
A0 --(nu0,delta0)--> A1 --(nu1,delta1)--> ... --(nu{k-1},delta{k-1})--> Ak
```

define

```text
Nu    = product of all transition numerators
Delta = product of all transition denominators.
```

The path should prove

```text
Ak * Delta = A0 * Nu.
```

This gives the global support localization

```text
q | Ak
-> q | A0 OR q | Nu
```

and dually

```text
q | A0
-> q | Ak OR q | Delta.
```

For the central escape question, prove more than endpoint transport:

```text
q escapes at A0
and q divides no transition numerator
-> q escapes at every stage of the path.
```

If capture occurs after initial escape, prove an exact transition witness:

```text
there exists a transition t in the path such that
  q escapes at t.first,
  q is caught at t.second,
  q | t.numerator.
```

This is the finite-path form of the research question:

```text
How far can a prime keep escaping?
It escapes until a transition whose numerator support contains it;
if no such transition occurs, it escapes through the whole finite path.
```

A product-localization theorem

```text
initial escape + final capture
-> q | product(numerators)
```

should also be exported, because later arithmetic applications may naturally expose only the total transition support.

---

## 7. Stop rule after MG-001

Do not proceed directly to Norm / lattice landing.

After MG-001, review whether the finite escape-path API is strong enough to support:

```text
MG-L2 — Legendre degree-two bridge
```

In particular, compare first-capture numerator support with the existing tied-successor obstruction

```text
q | 2*n + 1.
```

The Legendre bridge remains downstream and must not be imported into generic MultiGauge production code.
