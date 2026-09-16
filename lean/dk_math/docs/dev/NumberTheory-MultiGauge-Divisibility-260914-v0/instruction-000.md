# instruction-000 — MG-000 two-stage prime escape transport

cid: `6aa763a7-1a14-83e8-9041-1029d978663c`

## Role

Act as the production Lean implementer for the first Multi-Gauge Divisibility checkpoint.

This is a bounded implementation task.

Do not expand into finite paths, Norm/lattice landing, ABC, FLT, or Legendre application work in this pass.

The mathematical target is the smallest generic theorem package answering:

```text
If prime q escapes divisibility in gauge stage 1,
when must it still escape in gauge stage 2?

If q becomes newly visible in stage 2,
which transition factor must contain q?
```

---

## Repository / branch

```text
repository: Deskuma/dkmath
branch:     wip/number-theory-multi-gauge-divisibility-260914-v0
```

Work only on this branch.

Read first:

```text
lean/dk_math/docs/dev/NumberTheory-MultiGauge-Divisibility-260914-v0/README.md
lean/dk_math/docs/dev/NumberTheory-MultiGauge-Divisibility-260914-v0/ROADMAP.md
lean/dk_math/docs/dev/NumberTheory-MultiGauge-Divisibility-260914-v0/CODEX.md

docs/not_implements/260912-MultiGauge-Divisibility-Norm-Lattice-Landing.md
```

Inspect the current source declarations before writing proofs:

```text
DkMath/Lib/Cosmic/GTail.lean
DkMath/Lib/Cosmic/GTailBoundary.lean
DkMath/NumberTheory/FixedBigGauge/Basic.lean
```

For downstream motivation only, inspect if useful:

```text
DkMath/NumberTheory/PrimorialUniverse/SquareAnchorOffsetSuccessorPairFreshPrimeTransport.lean
```

Do not import that PrimorialUniverse module into MultiGauge.

---

## Existing production facts

The one-stage gcd theorem is already available:

```lean
gcd_GN_eq_gcd_of_one_le
```

with the mathematical content:

$$
\gcd(x,GTail(d,1,x,u))=\gcd(x,d)
$$

under `1 <= d` and `Nat.Coprime x u`.

Prime specializations also already exist:

```lean
gcd_GN_prime_eq_one_of_not_dvd
gcd_GN_prime_eq_prime_of_dvd
```

MG-000 must reuse these facts. Do not re-prove the internal `GTail` recursion or the gcd boundary identity.

---

## Task 0 — audit exact APIs and ownership

Before editing:

1. Confirm the exact namespace and theorem signatures in `GTail`, `GTailBoundary`, and nearby `NumberTheory` modules.
2. Confirm there is no existing generic two-stage gauge/transport abstraction that already owns the intended API.
3. Check whether `GN` is an existing canonical alias/definition in the relevant namespace or whether production should stay with `GTail d 1`.
4. Preserve existing import layering. Generic MultiGauge must not depend on application modules.

If a canonical existing abstraction already matches the requested packet, reuse it and document the adaptation in `report-000.md` rather than introducing a duplicate type.

---

## Task 1 — implement the basic stage packet

Create, unless an existing ownership boundary clearly suggests a smaller equivalent:

```text
DkMath/NumberTheory/MultiGauge/Basic.lean
```

Preferred namespace:

```lean
namespace DkMath.NumberTheory.MultiGauge
```

Implement a stage packet carrying the natural-number GN coordinates:

```lean
structure GNGaugeStage (d : ℕ) where
  x : ℕ
  u : ℕ
  coprime : Nat.Coprime x u
```

Add small derived definitions equivalent to:

```lean
def GNGaugeStage.gnValue (s : GNGaugeStage d) : ℕ :=
  GTail d 1 s.x s.u


def GNGaugeStage.value (s : GNGaugeStage d) : ℕ :=
  s.x * s.gnValue
```

Add semantic predicates equivalent to:

```lean
def PrimeCaught (q : ℕ) (s : GNGaugeStage d) : Prop :=
  q ∣ s.value


def PrimeEscapes (q : ℕ) (s : GNGaugeStage d) : Prop :=
  ¬ q ∣ s.value
```

Keep these reducible/simple unless existing style strongly favors theorem wrappers.

Do not add a finite-state enum in MG-000.

---

## Task 2 — implement the concrete two-stage transition

In `Basic.lean`, or another minimal file if import ownership requires it, implement the transition packet with the frozen arithmetic semantics:

```lean
structure GNGaugeTransition (d : ℕ) where
  first : GNGaugeStage d
  second : GNGaugeStage d
  numerator : ℕ
  denominator : ℕ
  numerator_pos : 0 < numerator
  denominator_pos : 0 < denominator
  balance :
    second.value * denominator = first.value * numerator
```

The balance orientation is intentional:

$$
A_2\delta=A_1\nu.
$$

Do not reverse it silently.

Vocabulary:

```text
numerator ν:
  possible source of new prime support

denominator δ:
  possible sink of old prime support
```

Positivity records quotient/refinement semantics and prevents degenerate zero transition factors. If the exact Lean design can prove the transport theorems more cleanly with nonzero fields instead, keep positivity unless there is a concrete repository-wide convention that strongly favors nonzero; document any change.

Do not add an abstract `transition : Prop` field in addition to `balance` unless it is needed for a clearly identified future-compatible reason.

---

## Task 3 — prime capture localization

Create:

```text
DkMath/NumberTheory/MultiGauge/PrimeTransport.lean
```

Prove the forward capture-localization theorem.

Target mathematical statement:

$$
q\mid A_2
\Longrightarrow
q\mid A_1\;\lor\;q\mid\nu
$$

for prime `q`.

Suggested theorem shape, naming adjustable to local convention:

```lean
theorem prime_dvd_second_value_imp_dvd_first_or_numerator
    {d q : ℕ} (hq : Nat.Prime q)
    (t : GNGaugeTransition d)
    (hq2 : q ∣ t.second.value) :
    q ∣ t.first.value ∨ q ∣ t.numerator := by
  ...
```

Expected proof mechanism:

```text
q | A₂
-> q | A₂*δ
-> rewrite by balance
-> q | A₁*ν
-> Nat.Prime.dvd_mul
```

Keep the proof direct. Do not route through gcd, valuations, or factorization.

---

## Task 4 — forward prime escape transport

Prove the central MG-000 theorem:

$$
q\nmid A_1
\land
q\nmid\nu
\Longrightarrow
q\nmid A_2.
$$

Suggested interface:

```lean
theorem primeEscapes_second_of_first_of_not_dvd_numerator
    {d q : ℕ} (hq : Nat.Prime q)
    (t : GNGaugeTransition d)
    (hEscape : PrimeEscapes q t.first)
    (hNum : ¬ q ∣ t.numerator) :
    PrimeEscapes q t.second := by
  ...
```

This theorem is the checkpoint's primary semantic result.

Its meaning must remain visible in the docstring:

```text
A prime that is absent from the first stage cannot appear in the second stage
unless it enters through the transition numerator.
```

---

## Task 5 — reverse capture / escape localization

Prove the dual statement:

$$
q\mid A_1
\Longrightarrow
q\mid A_2\;\lor\;q\mid\delta.
$$

Suggested theorem shape:

```lean
theorem prime_dvd_first_value_imp_dvd_second_or_denominator ...
```

Then derive:

$$
q\nmid A_2
\land
q\nmid\delta
\Longrightarrow
q\nmid A_1.
$$

Suggested semantic theorem:

```lean
theorem primeEscapes_first_of_second_of_not_dvd_denominator ...
```

Interpretation:

```text
A previously visible prime may disappear only through denominator support.
```

Again, keep the proof elementary.

---

## Task 6 — visibility conservation outside transition support

If prime `q` divides neither transition coefficient:

$$
q\nmid\nu,
\qquad
q\nmid\delta,
$$

prove prime visibility is conserved:

$$
q\mid A_1
\iff
q\mid A_2.
$$

Also provide the escape form if it is a clean corollary:

$$
q\nmid A_1
\iff
q\nmid A_2.
$$

Suggested names:

```lean
primeCaught_iff_of_not_dvd_transition_support
primeEscapes_iff_of_not_dvd_transition_support
```

Do not introduce a separate support Finset merely for these two hypotheses in MG-000 unless it substantially improves the API.

---

## Task 7 — one-stage boundary / GN channel decomposition

For prime `q`, prove the stage observer decomposition:

$$
q\mid x\,GTail(d,1,x,u)
\iff
q\mid x\;\lor\;q\mid GTail(d,1,x,u).
$$

This may be a very small theorem around `Nat.Prime.dvd_mul`.

Then use the existing gcd firewall to prove the stronger common-channel localization:

$$
q\mid x
\land
q\mid GTail(d,1,x,u)
\Longrightarrow
q\mid d
$$

under `1 <= d` and the stage's stored `Coprime x u`.

Important: this stronger theorem does not inherently require `q` to be prime if the gcd proof works directly. Prefer the strongest natural theorem with minimal assumptions.

Then derive the off-exponent exclusion:

```text
q ∤ d
-> NOT (q | x AND q | gnValue)
```

and, for prime `q`, document the resulting three semantic possibilities:

```text
escape
boundary-only
gn-only
```

Do not create an enum/state machine yet.

---

## Task 8 — facade

Create or update the generic facade:

```text
DkMath/NumberTheory/MultiGauge.lean
```

It should import the MG-000 production modules and nothing application-specific.

Do not add the facade to broad repository-level facades unless current DkMath conventions require it and the dependency direction is safe. If such integration is needed, record exactly what was changed.

---

## Task 9 — focused validation

Run focused builds from the Lean project root for the new modules, adapting module names to the actual file split:

```text
lake build DkMath.NumberTheory.MultiGauge.Basic
lake build DkMath.NumberTheory.MultiGauge.PrimeTransport
lake build DkMath.NumberTheory.MultiGauge
```

If a broad facade was modified, build that facade as well.

Run the repository's normal forbidden-pattern / warning checks used for production work if available locally.

At minimum confirm:

```text
no sorry
no admit
no new axiom declarations
no unresolved build warnings caused by the new files
```

Do not claim whole-repository validation if only focused modules were built.

---

## Task 10 — report

Create:

```text
lean/dk_math/docs/dev/NumberTheory-MultiGauge-Divisibility-260914-v0/report-000.md
```

The report must include:

```text
Outcome
files added/changed
final structures/definitions
final theorem names with short mathematical meaning
which existing GTail/GN theorems were reused
exact build commands and results
any warnings
any API/design deviation from this instruction
what remains for MG-001
```

Use one of these outcome labels:

```text
Outcome A — MG-000 COMPLETE
  two-stage transition and both-direction prime transport are production-proved;
  outside transition support, prime visibility iff is production-proved;
  one-stage common-channel support is localized to d.

Outcome B — ENGINEERING PARTIAL
  mathematics is intact but one or more requested API/facade/build items remain.

Outcome C — DESIGN BLOCKED
  the proposed balance packet conflicts with existing canonical semantics or a requested theorem is false as stated.
```

If Outcome C occurs, give an explicit counterexample or exact API conflict. Do not weaken the theorem silently.

---

## Non-goals / stop conditions

Stop after MG-000.

Do not implement in this pass:

```text
GNGaugePath
finite List/Fin chain induction
first-capture index theorem
transition numerator product theorem
Legendre d=2 bridge
PrimorialUnitUniverse edits
FixedBigGauge bridge implementation
Norm divisibility
Eisenstein / TraceOne lattice landing
power/Core-image landing
ABC or FLT application theorems
```

Do not refactor unrelated existing modules.

Do not open a pull request unless separately requested.

---

## Mathematical success criterion

At the end of MG-000, production Lean should support the exact statement:

```text
For a prime q and a two-stage gauge transition A₂*δ = A₁*ν:

- if q escaped A₁ and q does not divide ν, q also escapes A₂;
- if q escaped A₂ and q does not divide δ, q also escapes A₁;
- if q divides neither ν nor δ, q visibility is invariant across the transition.
```

Together with the existing GN gcd firewall, the branch should also expose:

```text
Any common boundary/GN divisor at one coprime stage must divide the exponent d.
```

That is the complete target for `instruction-000`.
