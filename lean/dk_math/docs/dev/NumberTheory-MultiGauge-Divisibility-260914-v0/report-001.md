# MG-001 implementation report

## Outcome

**Outcome A — MG-001 COMPLETE**

Finite path composition, all-stage escape propagation, first-capture
localization, and global numerator-product localization are production-proved.
The MG-L2 Legendre audit is now justified as a review checkpoint, but no
Legendre application bridge is implemented here.

## Final path representation

`Linked current transitions` is a recursive composability predicate:

```text
[]          : True
t :: ts     : t.first = current ∧ Linked t.second ts
```

`GNGaugePath d` stores:

- `start : GNGaugeStage d`
- `transitions : List (GNGaugeTransition d)`
- `linked : Linked start transitions`

The empty list is therefore a valid zero-step path whose endpoint is its
start stage. The semantic observers are:

- `GNGaugePath.endStage`
- `GNGaugePath.stages`
- `GNGaugePath.numeratorProduct`
- `GNGaugePath.denominatorProduct`

## Files changed

- Added `DkMath/NumberTheory/MultiGauge/Path.lean`.
- Updated `DkMath/NumberTheory/MultiGauge.lean` to import `Path`.
- Added this report.

No ABC, FLT, Legendre, FixedBigGauge, Norm, Eisenstein, or lattice module was
imported or modified.

## Path balance theorem

`GNGaugePath.balance` proves the exact telescoped law:

```text
path.endStage.value * path.denominatorProduct
  = path.start.value * path.numeratorProduct
```

The proof is by induction over the linked transition list and uses each
MG-000 transition balance. The empty path reduces to multiplication by `1`.

## Global localization and transport theorems

- `prime_dvd_end_value_imp_dvd_start_or_numeratorProduct`: endpoint capture
  implies start capture or total numerator support.
- `prime_dvd_start_value_imp_dvd_end_or_denominatorProduct`: start capture
  implies endpoint capture or total denominator support.
- `primeEscapes_end_of_start_of_not_dvd_numeratorProduct`: initial escape and
  numerator-product avoidance imply endpoint escape.
- `primeEscapes_start_of_end_of_not_dvd_denominatorProduct`: endpoint escape
  and denominator-product avoidance imply initial escape.
- `primeCaught_iff_of_not_dvd_path_support`: outside total support, capture is
  invariant between start and endpoint.
- `primeEscapes_iff_of_not_dvd_path_support`: outside total support, escape is
  invariant between start and endpoint.

## All-stage escape theorem

`primeEscapes_all_stages` proves that initial escape plus

```text
∀ t ∈ path.transitions, ¬ q ∣ t.numerator
```

implies `PrimeEscapes q s` for every `s ∈ path.stages`. This includes every
intermediate stage, not only the endpoint.

## First-capture localization

`exists_escape_to_capture_transition_of_captured_stage` proves that initial
escape and capture at any visited stage yield a transition `t` in the path
with:

```text
PrimeEscapes q t.first
PrimeCaught q t.second
q ∣ t.numerator
```

No uniqueness or numeric first index is claimed.

`prime_dvd_numeratorProduct_of_start_escape_of_end_caught` proves the weaker
global corollary `q ∣ path.numeratorProduct` when the endpoint is captured.

## Optional denominator-dual result

The symmetric product result
`prime_dvd_denominatorProduct_of_start_caught_of_end_escape` was added. It
proves that initial capture and endpoint escape imply divisibility of the
total denominator product. A separate denominator first-disappearance
witness was not added because it is optional in MG-001.

## Regression theorems

- `two_step_prime_escape_regression` checks escape through both stages of a
  linked two-transition path when both numerators avoid `q`.
- `new_capture_has_numerator_support_regression` checks that a newly captured
  second-stage prime divides the corresponding transition numerator.

## Focused validation

Commands were run from `lean/dk_math`:

```text
lake build DkMath.NumberTheory.MultiGauge.Path
lake build DkMath.NumberTheory.MultiGauge
```

Both completed successfully. The facade build completed successfully with
`8660 jobs`.

`git diff --check` completed successfully. Changed Lean files were scanned for
`sorry`, `admit`, and `axiom`; no matches were found. The final focused builds
reported no Lean `warning:` diagnostics attributable to MG-001.

The shell profile emitted the environmental message
`/opt/wonderful/bin/wf-env: Permission denied`; this did not affect the Lean
exit status or build result.

## Instruction deviations and scope boundary

No mathematical deviation or representation repair was needed. The path uses
the requested simple `List` representation with a recursive linked invariant.
No automaton, finite-indexed dependent machinery, or application-specific
assumptions were introduced.

MG-L2 review may now compare first-capture numerator support with the existing
Legendre tied-successor obstruction. That review must remain downstream; the
generic MultiGauge production facade remains Legendre-independent.
