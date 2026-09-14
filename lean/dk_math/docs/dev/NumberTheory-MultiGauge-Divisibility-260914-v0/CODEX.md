# Codex context — Multi-Gauge Divisibility 260914 v0

cid: `6aa763a7-1a14-83e8-9041-1029d978663c`

## Read order

Before editing Lean code, read:

```text
lean/dk_math/docs/dev/NumberTheory-MultiGauge-Divisibility-260914-v0/README.md
lean/dk_math/docs/dev/NumberTheory-MultiGauge-Divisibility-260914-v0/ROADMAP.md
lean/dk_math/docs/dev/NumberTheory-MultiGauge-Divisibility-260914-v0/instruction-000.md

docs/not_implements/260912-MultiGauge-Divisibility-Norm-Lattice-Landing.md
```

Then inspect the current production sources rather than guessing theorem signatures:

```text
DkMath/Lib/Cosmic/GTail.lean
DkMath/Lib/Cosmic/GTailBoundary.lean
DkMath/NumberTheory/FixedBigGauge/Basic.lean
DkMath/NumberTheory/PrimorialUniverse/SquareAnchorOffsetSuccessorPairFreshPrimeTransport.lean
```

The PrimorialUniverse file is downstream motivation only. Do not import it into generic MultiGauge modules.

---

## Mathematical context

DkMath already has the one-stage GN/GTail gcd firewall.

For `1 <= d` and `Coprime x u`:

$$
\gcd(x,GTail(d,1,x,u))=\gcd(x,d).
$$

This is already production-proved. Reuse it.

The new question is not another one-stage gcd theorem.

The new question is:

```text
A prime q is invisible in stage 1.
After changing the arithmetic unit / gauge, is q still invisible in stage 2?
If q becomes visible for the first time, which transition factor introduced it?
```

The campaign vocabulary is:

```text
escape  := q does not divide the stage observer
capture := q divides the stage observer
```

The first stage observer is intentionally elementary:

```text
gnValue    = GTail d 1 x u
stageValue = x * gnValue
```

Do not replace this with Norm, valuation, ideals, real-valued units, or a new quotient type in MG-000.

---

## Frozen design decision for MG-000

The first transition object is governed by the natural-number balance law

$$
A_2\delta=A_1\nu.
$$

Interpret:

```text
A₁ = first stage value
A₂ = second stage value
ν  = numerator
δ  = denominator
```

Semantic meaning:

```text
numerator support
  = possible source of newly captured prime support;

denominator support
  = possible sink of previously visible prime support.
```

The balance law is deliberately expressed by cross multiplication so that prime divisibility transport is proved in `ℕ` without rational arithmetic.

Do not replace this with an abstract `transition : Prop` in this checkpoint.

Do not bake in application-specific formulas for `u₂` from `u₁` yet.

The generic transition is a carrier for facts proved by later concrete bridges.

---

## Expected core proof mechanism

For prime `q`:

```text
q | A₂
-> q | A₂*δ
-> q | A₁*ν
-> q | A₁ OR q | ν.
```

Therefore:

```text
q ∤ A₁
q ∤ ν
-> q ∤ A₂.
```

Dually:

```text
q | A₁
-> q | A₁*ν
-> q | A₂*δ
-> q | A₂ OR q | δ.
```

Therefore:

```text
q ∤ A₂
q ∤ δ
-> q ∤ A₁.
```

If `q` avoids both transition coefficients:

```text
q | A₁ <-> q | A₂
```

and equivalently:

```text
q ∤ A₁ <-> q ∤ A₂.
```

These are elementary consequences of primality + divisibility of a product. Keep the proofs small and transparent.

---

## One-stage channel theorem

For a prime `q`:

```text
q | stageValue
<->
q | stage.x OR q | stage.gnValue.
```

Under the existing firewall assumptions:

```text
1 <= d
Coprime stage.x stage.u
q ∤ d
```

simultaneous capture in both channels is impossible:

```text
NOT (q | stage.x AND q | stage.gnValue).
```

A stronger reusable bridge is acceptable if it follows directly from the existing gcd equality, for example:

```text
q | stage.x
q | stage.gnValue
-> q | d
```

without requiring `q` prime.

Prefer the stronger theorem if it is no harder to prove.

---

## What MG-000 must not do

Do not implement:

```text
finite gauge paths
List/Fin state automata
Norm divisibility
Eisenstein coordinates
TraceOne lattice landing
power/Core landing
ABC bridges
FLT bridges
Legendre bridges
new analytic/counting arguments
```

Do not change existing one-stage GN theorem ownership.

Do not move `GTailBoundary` declarations into MultiGauge.

Do not make generic MultiGauge depend on:

```text
DkMath.ABC.*
DkMath.FLT.*
DkMath.NumberTheory.Legendre.*
```

---

## Naming / ownership guidance

Preferred namespace:

```lean
namespace DkMath.NumberTheory.MultiGauge
```

Preferred production paths:

```text
DkMath/NumberTheory/MultiGauge/Basic.lean
DkMath/NumberTheory/MultiGauge/PrimeTransport.lean
DkMath/NumberTheory/MultiGauge.lean
```

Use existing naming conventions after inspecting nearby NumberTheory modules.

Do not force the exact suggested theorem names if Lean/library conventions clearly favor better ones. Preserve the mathematical interface.

---

## Proof / repository discipline

```text
No sorry.
No admit.
No new axiom declarations.
No theorem whose conclusion is stronger than the hypotheses justify.
No application-specific import cycle.
```

If the proposed packet conflicts with an existing canonical abstraction, report the conflict before making a broad refactor. A small local adaptation is allowed when it preserves the stated transition semantics.

Focused builds are mandatory.

Record:

```text
files changed
theorems added
exact build commands
build result
warnings/errors
any deviation from instruction
```

in `report-000.md`.

---

## Why this matters downstream

The current Legendre/PrimorialUnitUniverse development has a production theorem of the form:

```text
fresh prime delays a tied successor-square pair
-> q | 2*n + 1.
```

The degree-two GN view reads the successor increment through the `GN₂` / `GTail 2 1` boundary.

The MultiGauge core is intended to determine whether such an obstruction is an instance of a more general rule:

```text
new prime capture after changing gauge
must enter through explicit transition support.
```

MG-000 does not prove this Legendre bridge. It builds the generic arithmetic tool needed to ask that question cleanly.
