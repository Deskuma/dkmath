# MG-003B implementation and audit report

## Outcome

**Outcome A — FINITE RAW-REFINEMENT PATHS AND PRIMITIVE-SHAPE INVARIANCE**

The MG-003A one-step raw refinement law is now lifted to finite positive
factor lists. Positive synchronized scaling changes only the common gcd scale;
gcd normalization recovers the same primitive coprime stage. A prime that
escapes initially and avoids every listed factor escapes at every visited
stage. Any visited capture supplies an actual factor divisible by that prime.

This is finite homogeneous arithmetic transport. It does not construct a
primitive `GNGaugeTransition`, a channel automaton, or a Legendre/Goldbach
provider.

## Files changed

Added:

```text
DkMath/NumberTheory/MultiGauge/RawRefinementPath.lean
docs/dev/NumberTheory-MultiGauge-Divisibility-260914-v0/report-004.md
```

Updated:

```text
DkMath/NumberTheory/MultiGauge.lean
docs/dev/NumberTheory-MultiGauge-Divisibility-260914-v0/ROADMAP.md
```

The optional PUU composition bridge was not added: the existing
`MultiGaugeUnitRefinementBridge` already supplies the one-step semantic
connection, and a dependent list of positive units is not required by the
finite generic path theorem.

## Scale algebra and primitive shape

The new generic module proves:

```text
scaleBy k₂ (scaleBy k₁ s) = scaleBy (k₁*k₂) s
(scaleBy k s).scale = k*s.scale
```

For `0 < s.scale` and `0 < k`, it also proves:

```text
(scaleBy k s).primitiveStage = s.primitiveStage
```

with the required positive gcd proof supplied explicitly. Coordinate
corollaries and `PrimeCaught` / `PrimeEscapes` equivalences are exported. The
existing `GNGaugeStage.coprime` field is unchanged.

## Finite path representation

`GNRawRefinementPath d` contains:

```text
start : GNRawGaugeStage d
factors : List ℕ
factors_pos : every listed factor is positive
```

The path exposes `cumulativeFactor`, `endStage`, and `stages`. The endpoint is
exactly the start raw stage scaled by the product of the factor list:

```text
endStage = scaleBy cumulativeFactor start
```

The endpoint is also proved to belong to the visited stage list.

## Homogeneous transport and escape laws

The endpoint observer law is:

```text
endStage.value = cumulativeFactor^d * start.value
```

For a prime `q`, initial raw escape plus factor avoidance gives:

```text
∀ s ∈ path.stages, RawPrimeEscapes q s
```

If a visited stage is captured after initial escape, the theorem
`exists_escape_to_capture_step` returns a visited before-stage, an actual
factor from the path, escape before that factor, capture after it, and
`q ∣ factor`. The weaker factor-existence corollary is also exported.

Endpoint capture additionally implies:

```text
q ∣ cumulativeFactor
```

and a prime divisor of the cumulative factor is localized to a member of the
factor list.

## Regressions

The escape regression uses degree `2`, raw pair `(1,2)`, and positive factors
`[2,5]`; prime `7` avoids both factors and escapes every visited stage.

The capture regression uses factors `[2,3]`; prime `3` escapes the start and
the stage after factor `2`, then is captured after factor `3`. The path-level
localization theorem proves that a listed factor is divisible by `3`.

## Validation

Commands were run from `lean/dk_math`:

```text
lake build DkMath.NumberTheory.MultiGauge.RawRefinementPath
lake build DkMath.NumberTheory.MultiGauge.RawNormalization
lake build DkMath.NumberTheory.MultiGauge
lake build DkMath.NumberTheory.PrimorialUniverse.MultiGaugeUnitRefinementBridge
lake build DkMath.NumberTheory.PrimorialUniverse
```

All completed successfully. The path, raw facade, raw normalization, PUU
bridge, and PUU facade builds completed with `8659`, `8662`, `8658`, `8661`,
and `8707` jobs, respectively.

`git diff --check` completed successfully. Changed Lean sources were scanned
for `sorry`, `admit`, and new `axiom` declarations; none were found. No Lean
warning diagnostics were emitted by the successful focused builds. The shell
profile continued to emit `/opt/wonderful/bin/wf-env: Permission denied`; this
is environmental noise only.

## Scope barriers and next boundary

No MG-002 automaton, Legendre or Goldbach change, primitive-shape transition
provider, Norm, Eisenstein, TraceOne, FLT/ABC migration, or analytic estimate
was added. MG-003B completes synchronized common-scale transport. The next
checkpoint may re-audit genuine primitive-shape transition providers, keeping
them separate from raw common scaling.
