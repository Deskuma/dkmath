# Instruction-009 — Generic odd-prime counterexample routing

Branch: `research/FLT-Prime-TraceOne-Closure-260916-v0`

Checkpoint: **FPTC-009**

## Objective

Close the remaining front-end architecture gap as far as the checked arithmetic actually permits.

The current TraceOne chain begins from

```text
PrimeAdicFactorPacket p g u x
```

rather than directly from a primitive positive FLT counterexample.  The packet contains the explicit branch assumption

```text
p ∣ g
```

so this checkpoint must **not** silently claim that every odd-prime counterexample enters the packet.

Instead, expose the honest two-branch routing at the generic odd-prime level:

```text
primitive positive FLT counterexample
  |
  |-- p ∣ (z - y)
  |      -> PrimeAdicFactorPacket p (z - y) y x
  |
  `-- p ∤ (z - y)
         -> coprime gap / GTail factorization
         -> each factor is a p-th power
```

The ramified/gap-divisible branch is the entrance to the existing TraceOne architecture.  The away branch must remain explicit unless a checked theorem actually closes or transports it.

This checkpoint is routing only.  It must not prove general FLT, reopen FPTC-007 class numbers, or force the FPTC-008 p=5 Golden packet bridge.

## Read first

Before editing, read at least:

```text
DkMath/FLT/Prime/AdicPowerSplit.lean
DkMath/FLT/Core.lean
DkMath/FLT/Seven/CounterexampleRouting.lean
DkMath/FLT/Seven/SevenAdicPowerSplit.lean
DkMath/FLT/PrimeProvider/TriominoCosmicPrimeGe5Core.lean
DkMath/FLT/Five/Basic.lean
DkMath/FLT/Five/NormalForm.lean
DkMath/FLT/Three/*                  -- audit only as needed
DkMath/FLT/Prime/PrimeTraceOneStrippedIdeal.lean

docs/dev/FLT-Prime-TraceOne-Closure-260916-v0/report-008.md
docs/refact/FLT-Prime-Generalization-260911-v0/summary-026.md
```

Also inspect existing tests around:

```text
DkMathTest/FLT/Prime/AdicPowerSplitCompatibility.lean
DkMathTest/FLT/SevenAdicPowerSplit.lean
```

Write findings to:

```text
docs/dev/FLT-Prime-TraceOne-Closure-260916-v0/report-009.md
```

## Part 0 — Audit the current front-end boundary

Pin the exact current APIs for:

```text
PrimeAdicFactorPacket
PrimeAdicPowerSplit
pow_eq_sub_mul_GN_of_add_pow_eq
power_factor_split
gcd_GN_prime_eq_one_of_not_dvd
gcd_GN_prime_eq_prime_of_dvd
```

Audit the generic counterexample structure already present under the older provider stack:

```text
PrimeCounterexamplePack
PrimeGe5CounterexamplePack
```

and the specialized packets:

```text
DkMath.FLT.Five.CounterexamplePack
DkMath.FLT.Seven.CounterexamplePack
SevenAdicCounterexamplePacket
```

Record which of the following are already neutral lemmas and which currently live only inside old/specialized namespaces:

```text
y < z
Nat.Coprime y z
Nat.Coprime (z - y) y
(z - y) * GTail p 1 (z - y) y = x ^ p
```

Do not import the entire old `PrimeProvider` stack into a new low-level `DkMath.FLT.Prime` production module merely to reuse a tiny packet if that creates an inverted dependency.  Prefer a small neutral routing surface.

Status marker:

```text
FPTC-GENERIC-COUNTEREXAMPLE-API-AUDITED
```

## Part 1 — Establish a neutral primitive odd-prime counterexample input

The preferred architecture is a small production module such as

```text
DkMath/FLT/Prime/CounterexampleRouting.lean
```

with the weakest useful primitive-positive input.

A possible packet shape is conceptually:

```lean
structure PrimeCounterexamplePacket (p x y z : ℕ) : Prop where
  prime : Nat.Prime p
  odd : 3 ≤ p
  x_pos : 0 < x
  y_pos : 0 < y
  z_pos : 0 < z
  coprime_x_y : Nat.Coprime x y
  equation : x ^ p + y ^ p = z ^ p
```

but **do not introduce this exact structure if an existing neutral packet can be moved/reused cleanly without creating dependency cycles**.

It is acceptable for the packet to retain an explicit `y < z` field if deriving it would add irrelevant proof bulk.  If it is easy to derive from positivity plus the FLT equation, prefer a theorem rather than redundant stored data.

Do not bake `p ∣ z - y` into the primitive counterexample packet.  That is the routing branch, not part of the counterexample itself.

If old `PrimeCounterexamplePack` is generalized/extracted, preserve compatibility for old provider consumers where practical rather than performing a broad unrelated refactor.

## Part 2 — Neutral gap facts

For the chosen generic primitive counterexample input, prove or expose the following checked facts:

```text
0 < z - y
Nat.Coprime y z
Nat.Coprime (z - y) y
(z - y) * GTail p 1 (z - y) y = x ^ p
```

The intended mathematics is already visible in existing code:

```text
x^p + y^p = z^p
  -> x^p = (z-y) * GTail p 1 (z-y) y
```

and primitive `gcd(x,y)=1` implies `gcd(y,z)=1`, hence `gcd(z-y,y)=1`.

Do not duplicate long specialized p=5/p=7 proofs when the exponent-generic proof already exists in `TriominoCosmicPrimeGe5Core.lean`; extract or reproduce only the genuinely neutral kernel in an appropriate dependency direction.

Suggested status:

```text
FPTC-GENERIC-GAP-FACTORIZATION-GREEN
```

## Part 3 — Gap-divisible branch to `PrimeAdicFactorPacket`

Prove a production theorem of the conceptual form:

```lean
primeAdicFactorPacket_of_counterexample_of_prime_dvd_gap
    (P : <generic primitive odd-prime counterexample packet>)
    (hgap : p ∣ z - y) :
  PrimeAdicFactorPacket p (z - y) y x
```

Populate the packet only from checked generic facts:

```text
prime              := P.prime
odd                := P.odd
gap_pos            := ...
distinguished_pos  := P.x_pos
coprime_gap_unit   := ...
prime_dvd_gap      := hgap
factor_eq          := ...
```

This theorem is the exact front door to the existing TraceOne chain.

Do not hide `hgap` inside a choice, permutation, or classical witness unless a separate theorem actually proves such a choice is always possible.

Status:

```text
FPTC-GAP-DIVISIBLE-TO-PRIMEADIC-PACKET-GREEN
```

## Part 4 — Away branch

For

```text
¬ p ∣ z - y
```

use the existing prime-GTail gcd kernel to prove

```text
Nat.Coprime (z - y) (GTail p 1 (z - y) y)
```

and then use `power_factor_split` with

```text
(z - y) * GTail p 1 (z - y) y = x ^ p
```

to obtain

```text
∃ a : ℕ, z - y = a ^ p
∃ b : ℕ, GTail p 1 (z - y) y = b ^ p
```

Prefer one theorem returning both witnesses.

This is **not** itself a contradiction.  Do not label the away branch impossible unless an existing checked theorem proves that.

Status:

```text
FPTC-GAP-AWAY-POWER-SPLIT-GREEN
```

## Part 5 — Honest two-branch route

If Parts 1–4 are green, expose a small inductive or equivalent disjunction recording the exact routing surface, conceptually:

```lean
inductive PrimeCounterexampleRoute (p x y z : ℕ) : Prop
  | away
      (hnot : ¬ p ∣ z - y)
      (gapPow : ∃ a : ℕ, z - y = a ^ p)
      (residualPow : ∃ b : ℕ, GTail p 1 (z - y) y = b ^ p)
  | ramified
      (packet : PrimeAdicFactorPacket p (z - y) y x)
```

and prove

```lean
counterexampleRoute_of_packet :
  <generic primitive odd-prime counterexample packet> ->
  PrimeCounterexampleRoute p x y z
```

A theorem returning a logically equivalent sum/disjunction is acceptable if it fits repository style better.

The important requirement is that the output make the branch boundary impossible to miss.

Status:

```text
FPTC-GENERIC-TWO-BRANCH-ROUTE-GREEN
```

## Part 6 — Downstream compatibility audit

Verify that the ramified constructor feeds the existing production chain without adapter fiction:

```text
PrimeAdicFactorPacket
  -> PrimeAdicPowerSplit
  -> PrimeTraceOneCoordinatePacket consumer
  -> PrimeTraceOneStrippedIdealPacket consumer
```

A full construction of the cyclotomic coordinate packet is not required here if its existing theorem requires separate ambient data.  The audit only needs to confirm that the new route produces exactly the `PrimeAdicFactorPacket` type consumed downstream.

Do not re-prove FPTC-004/005/006/008 endpoint theorems in this checkpoint.

## Part 7 — Fixed-exponent regressions

### p=7

Use the existing specialized route as the strongest regression:

```text
Seven.CounterexamplePack
  + 7 ∣ z-y
  -> SevenAdicCounterexamplePacket
  -> SevenAdicCounterexamplePacket.toPrimeAdicFactorPacket
```

Check that the new generic gap-divisible routing produces the same target type

```text
PrimeAdicFactorPacket 7 (z-y) y x.
```

Do not replace the specialized packet or its richer valuation fields.

### p=5

Audit the existing `DkMath.FLT.Five.CounterexamplePack` and its Branch A/B split.

Where the specialized hypotheses match the generic primitive packet, provide only a thin regression adapter/test.  Under the explicit branch hypothesis

```text
5 ∣ z-y
```

the generic route should produce

```text
PrimeAdicFactorPacket 5 (z-y) y x.
```

Do **not** claim that existing Branch-B-to-signed-Branch-A machinery has been generalized unless a checked theorem actually gives the required generic orientation.

### p=3

Audit compatibility with the production FLT3 counterexample vocabulary.  A thin test is sufficient if the specialized FLT3 development uses a materially different normal form.  Do not refactor the completed FLT3 proof merely to satisfy this checkpoint.

## Part 8 — Identify the real front-end frontier

The report must explicitly answer:

1. Does every primitive positive odd-prime counterexample enter `PrimeAdicFactorPacket` directly?  If not, state why not.
2. Is the exact obstruction merely the branch condition `p ∣ z-y`?
3. Can the coordinates be permuted by a checked generic theorem so that some orientation satisfies this branch?
4. If not, what is the strongest checked result on the away branch?
5. Does the old `PrimeProvider` stack contain a genuine theorem closing the away branch, or only conditional/provider interfaces?

Do not infer a generic orientation theorem from the p=5 or p=7 specialized developments.

The expected architecture after this checkpoint is likely:

```text
primitive odd-prime counterexample
        |
        +-- ramified gap branch
        |      -> PrimeAdicFactorPacket
        |      -> TraceOne closure architecture
        |
        `-- away branch
               -> gap = a^p
               -> GTail = b^p
               -> separate arithmetic frontier
```

If this is what the checked repository supports, record it as the exact result rather than calling the routing incomplete.

## Non-goals

Do not in FPTC-009:

- prove general FLT;
- prove the away branch contradictory without an existing checked theorem;
- assume `p ∣ z-y` for every counterexample;
- hide branch selection inside a constructor;
- reopen FPTC-007 class-number coprimality;
- solve the FPTC-008 generic-to-Golden stripped-packet bridge;
- add a q-adic global descent provider;
- use the old `PrimeProvider` conditional target as if it were a theorem;
- alter completed FLT3/5/7 final theorems;
- claim a generic permutation/orientation theorem from fixed-exponent evidence.

## Validation

Add focused API and axiom audits, suggested names:

```text
DkMathTest/FLT/Prime/PrimeCounterexampleRoutingApiAudit.lean
DkMathTest/FLT/Prime/PrimeCounterexampleRoutingAxiomAudit.lean
```

At minimum run:

```text
lake build DkMath.FLT.Prime.AdicPowerSplit
lake build DkMath.FLT.Prime.CounterexampleRouting
lake build DkMathTest.FLT.Prime.PrimeCounterexampleRoutingApiAudit
lake build DkMathTest.FLT.Prime.PrimeCounterexampleRoutingAxiomAudit
```

Also build any p=5/p=7 regression modules touched by the implementation.

Run:

```text
git diff --check
```

and scan fresh production/test files for:

```text
sorry
sorryAx
admit
axiom
unsafe
```

Standard Lean/Mathlib foundations such as `propext`, `Classical.choice`, and `Quot.sound` are acceptable when inherited normally.

## Outcome classification

Classify `report-009.md` as one of:

```text
Outcome A — GENERIC TWO-BRANCH COUNTEREXAMPLE ROUTING GREEN

Outcome B — GAP-DIVISIBLE PRIMEADIC ROUTING GREEN;
            AWAY-BRANCH ROUTE FRONTIER ISOLATED

Outcome C — GENERIC COUNTEREXAMPLE NORMALIZATION GREEN;
            PRIMEADIC ROUTING API BOUNDARY REMAINS

Outcome D — FRONT-END DEPENDENCY/API BLOCKED
```

### Outcome A requires

- a neutral odd-prime primitive-counterexample input or equivalent theorem surface;
- checked generic gap/coprimality/factorization facts;
- explicit gap-divisible -> `PrimeAdicFactorPacket` theorem;
- explicit away-branch p-th-power factor split;
- a theorem exposing both branches honestly;
- p=7 compatibility regression;
- p=5 compatibility audit/regression where hypotheses match;
- focused build and axiom audit green;
- no hidden branch assumption or general-FLT claim.

## Stop rule

Stop after classifying FPTC-009.

Do not proceed automatically to a new proof of the away branch or to general FLT.  FPTC-010 is the public-facade/closeout checkpoint and should summarize the branch architecture exactly as it stands after this routing audit.
