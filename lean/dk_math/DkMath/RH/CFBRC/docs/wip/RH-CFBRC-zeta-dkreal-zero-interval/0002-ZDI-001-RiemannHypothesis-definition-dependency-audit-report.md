# ZDI-001 — `RiemannHypothesis` definition-dependency audit report

Date: 2026-08-19  
Branch: `wip/RH-CFBRC-zeta-dkreal-zero-interval-260819-v0`

## Scope and conclusion

This report implements the audit instructions in `0001-ZDI-001-...instructions.md`.
It is an audit, not an RH proof.  No new analytic definition, strip hypothesis,
provider, `sorry`, or replacement CFZP route was added.  No new Lean module was
needed: the existing declarations already expose the required machine-checked
facts and have Lean docstrings describing their trust boundaries.  The umbrella
equivalence in `DkMath.RH` received an explicit docstring recording that it is
an audit boundary and does not construct `map_zero`.

The clean dependency spine ends at the following exact obligation:

```text
∀ {s : ℂ}, NontrivialRiemannZetaZero s →
  offCriticalCFBRC d s.re (phase s) = 0
```

for a supplied `d` with `0 < d` and `phase : ℂ → ℝ`.  This is the
`map_zero` field of `ZeroToCFBRCBridge`.  The existing positive-degree CFBRC
theorem then gives `s.re = 1 / 2`, and the exact Mathlib `RiemannHypothesis`
follows.  The `map_zero` obligation is not presently derived from the zeta
zero equation by an independent source-preserving theorem; supplying it as a
provider is therefore the remaining RH-equivalent frontier.

## 1. Exact trusted dependency graph

Mathlib prints the following definitions:

```lean
def riemannZeta : ℂ → ℂ := HurwitzZeta.hurwitzZetaEven 0

def RiemannHypothesis : Prop :=
  ∀ (s : ℂ), riemannZeta s = 0 →
    (¬∃ n : ℕ, s = -2 * (n + 1)) →
    s ≠ 1 → s.re = 1 / 2
```

The DkMath predicate is the conjunction of exactly the three hypotheses in
that definition:

```lean
def NontrivialRiemannZetaZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧
    (¬∃ n : ℕ, s = -2 * (n + 1)) ∧
    s ≠ 1
```

`riemannHypothesis_iff_nontrivialZero_re_eq_half` merely reassociates these
hypotheses and is proved by `constructor`; it does not use a zero theorem,
critical-strip theorem, or RH assumption.

The clean CFBRC path is:

```text
riemannZeta
  → NontrivialRiemannZetaZero
  → riemannHypothesis_iff_nontrivialZero_re_eq_half
  → ZeroToCFBRCBridge.map_zero
  → cfbrcR_eq_zero_iff_x_eq_zero
  → centeredSigma_eq_zero_iff
  → s.re = 1 / 2
  → RiemannHypothesis
```

More explicitly, the algebraic part is

```text
offCriticalCFBRC d σ Θ
  = cfbrcR d (σ - 1 / 2) Θ
  = 0
  ↔ σ - 1 / 2 = 0
  ↔ σ = 1 / 2              (0 < d)
```

The last arrow is `re_eq_half_of_zeroToCFBRCBridge`, while
`riemannHypothesis_of_standardZetaToCFBRCBridge` packages it for the exact
Mathlib target.  `DkMath.RH.standardZeta_map_zero_iff_riemannHypothesis` proves
that the universally quantified `map_zero` proposition and RH are equivalent
for every positive degree and every phase.

## 2. Declaration classification

Each load-bearing declaration receives one primary category from the audit
instructions.

| Declaration | Expansion / role | Primary category | Trust result |
|---|---|---:|---|
| `riemannZeta` | `HurwitzZeta.hurwitzZetaEven 0` | **A** | Mathlib-backed zeta definition. |
| `RiemannHypothesis` | Exact universal zero statement printed above | **A** | Mathlib-backed target proposition; this audit does not prove it. |
| `NontrivialRiemannZetaZero` | zeta zero ∧ not negative-even trivial zero ∧ not pole | **B** | Definitional packaging of the RH antecedents. |
| `riemannHypothesis_iff_nontrivialZero_re_eq_half` | Reassociation of the conjunction | **C** | Independently Lean-proved, with no analytic content. |
| `centeredSigma` | `σ - 1 / 2` | **B** | Definitional coordinate packaging. Its intended meaning is supplied by `centeredSigma_eq_zero_iff`. |
| `centeredSigma_eq_zero_iff` | `centeredSigma σ = 0 ↔ σ = 1 / 2` | **C** | Pure real arithmetic, independently proved. |
| `offCriticalCFBRC` | `cfbrcR d (centeredSigma σ) Θ` | **B** | Ordinary CFBRC evaluation; it contains no zeta-zero predicate. |
| `cfbrcR_eq_zero_iff_x_eq_zero` | For `0 < d`, `cfbrcR d X Θ = 0 ↔ X = 0` | **C** | Independently proved by complex norms and norm squares; no RH input. |
| `offCriticalCFBRC_eq_zero_iff_re_eq_half` | Positive-degree CFBRC zero iff `σ = 1 / 2` | **C** | Composition of the two algebraic characterizations above. |
| `ZeroToCFBRCBridge` | Fields `d`, `0 < d`, `phase`, and `map_zero` | **D** | Explicit conditional interface. It does not assert that a zeta zero maps to CFBRC zero by itself. |
| `re_eq_half_of_zeroToCFBRCBridge` | Applies `map_zero` and the CFBRC characterization | **C** | Lean-proved consequence of an explicitly supplied conditional bridge. |
| `StandardZetaToCFBRCBridge` | `ZeroToCFBRCBridge NontrivialRiemannZetaZero` | **B** | Abbreviation only. |
| `riemannHypothesis_of_standardZetaToCFBRCBridge` | Bridge provider implies RH | **D** | Conditional interface theorem; the bridge is the analytic burden. |
| `riemannHypothesis_of_standardZeta_map_zero` | Direct `map_zero` provider implies RH | **D** | Conditional interface theorem; no provider is constructed. |
| `standardZeta_map_zero_iff_riemannHypothesis` | Universal `map_zero` iff RH | **E** | Exact RH-equivalent frontier. It must not be used as an independent provider. |

The underlying `cfbrc` and `cfbrcR` declarations are ordinary DkMath algebraic
definitions: `cfbrc d X Θ = (X + iΘ)^d - (iΘ)^d` and `cfbrcR` is its real-input
specialization.  Their relevant zero characterization is category **C** and
does not identify any CFBRC object with a zeta object.

## 3. Definition and realizability audit

`NontrivialRiemannZetaZero` is definitionally aligned with the Mathlib target,
but the statement that all such zeros have real part `1 / 2` is a separate
theorem (`riemannHypothesis_iff_nontrivialZero_re_eq_half`).  No critical-strip
or nontrivial-zero existence theorem is silently inserted.

`centeredSigma` is total on all real numbers, so its downstream hypotheses are
not made realizable by an inconsistent parent invariant.  Its semantic claim
is not definitional; it is exactly the separately proved iff theorem.

`offCriticalCFBRC` is total on `ℕ × ℝ × ℝ` and expands only to an algebraic
CFBRC evaluation.  It has no built-in zeta meaning.  The theorem
`offCriticalCFBRC_eq_zero_iff_re_eq_half` is therefore an algebraic detector,
not a zero-preserving source bridge.

`ZeroToCFBRCBridge` has no hidden critical-line field.  For an arbitrary
predicate `Zero`, it can be vacuously inhabited if `Zero` is empty.  For the
specific `NontrivialRiemannZetaZero`, its `map_zero` field is exactly the
unresolved source-recovery obligation: by
`standardZeta_map_zero_iff_riemannHypothesis`, its universal existence is
equivalent to RH.  Thus the interface is valid and explicit, but it is not
evidence that the field is realizable from current zeta facts.

The alternate `FiniteCenteredZeroBridge` is also only an interface.  Its
`endpoint_eq_zero`, nonzero projected mass, and especially
`center_identification` fields are independent inputs.  The standard-zeta
specialization proves RH only after those fields are supplied; the fields are
not consequences of the parent type invariants.

The `ZeroLocusFactorBridge` route has the same boundary.  Its nonzero-factor
and factorization fields can imply the direct `map_zero`, but the repository
does not establish the required zeta/CFBRC factorization.  It must not be
counted as a source-recovery theorem.

## 4. Axiom audit

The following commands were run from the nested Lake project:

```text
cd /home/deskuma/develop/lean/dkmath/lean/dk_math
lake env lean ../../ZDI001Check.lean
lake env lean ../../ZDI001ResearchCheck.lean
```

The first checker printed the exact declarations and the required axiom sets.
For every clean final-spine declaration below the result was:

```text
[propext, Classical.choice, Quot.sound]
```

| Declaration | Axiom result |
|---|---|
| `cfbrcR_eq_zero_iff_x_eq_zero` | `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` |
| `offCriticalCFBRC_eq_zero_iff_re_eq_half` | `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` |
| `riemannHypothesis_iff_nontrivialZero_re_eq_half` | `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` |
| `riemannHypothesis_of_standardZeta_map_zero` | `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` |
| `DkMath.RH.standardZeta_map_zero_iff_riemannHypothesis` | `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` |

These are standard Lean/Mathlib foundations: proposition extensionality,
classical choice used by imported mathematics, and quotient soundness.  They
are distinct from `sorryAx` and do not represent an unresolved project-local
provider.

The second checker confirmed that the clean RH-equivalence theorem
`etaCriticalMirrorDominantEulerHalfEndpointCarrierTransverseCollapse_iff_riemannHypothesis`
has the same standard axiom set.  In contrast,
`etaCriticalMirrorDominantEulerHalfEndpointCarrierTransverseCollapse_research_goal`
and every downstream `*_research_goal` beacon, including
`riemannHypothesis_movingLineCollision_research_goal`, depends on `sorryAx`.
Those declarations are **F — unresolved / untrusted** and are excluded from
the trusted dependency spine.

## 5. RH-equivalent frontiers in the CFBRC tree

The full `DkMath/RH/CFBRC` source search for `RiemannHypothesis`,
`NontrivialRiemannZetaZero`, `map_zero`, `iff_riemannHypothesis`, and
`research_goal` found the following explicit frontiers.  Each is category
**E**, even when its proof uses only already closed local theorems:

| Frontier theorem | Frontier proposition |
|---|---|
| `standardZeta_map_zero_iff_riemannHypothesis` in `DkMath.RH` | Universal standard-zeta CFBRC `map_zero` |
| `nonempty_standardZetaEtaKUSMirrorGapZeroBridge_iff_riemannHypothesis` | Existence of the standard KUS mirror-Gap bridge |
| `etaEndpointIncrementBalancedOnNontrivialZeros_iff_riemannHypothesis` | Endpoint-increment mirror-ratio balance on all nontrivial zeros |
| `pascalCenteredXiFixedDefectVanishesOnSafeRadii_iff_riemannHypothesis` | Vanishing of the fixed-Xi defect on all safe radii |
| `etaCriticalMirrorDominantEulerHalfEndpointCarrierTransverseCollapse_iff_riemannHypothesis` | Dominant Euler half-endpoint transverse collapse |
| `etaCriticalMirrorThreeElementInteractionAssimilationProvider_iff_riemannHypothesis` | Three-element interaction assimilation provider |
| `etaCriticalMirrorThreeElementDifferenceWholeCollapseProvider_iff_riemannHypothesis` | Difference-whole collapse provider |

The moving-line research roadmap also introduces aliases of these frontiers and
a `by sorry` research theorem.  The aliases do not weaken the boundary; the
research goal and its downstream beacons are category **F** because their
axiom sets contain `sorryAx`.  In particular, a proposition proved equivalent
to RH cannot be imported as the independent provider needed to prove RH.

Other CFBRC declarations that merely have an RH hypothesis or conclude RH are
conditional implications and were not counted as closed RH proofs.  A theorem
of the form “provider implies RH” is category **D** unless the provider itself
is independently constructed without an RH-equivalent assumption.

## 6. Historical CFZP and semantic boundary

The former CFZP forward chain was not revived.  This audit found no need to
introduce a replacement `σ`, strip parameter, growth exponent, PNT provider,
asymptotic hypothesis, or phase coordinate.

The important distinction is:

```text
closed algebraic detector:
  offCriticalCFBRC d σ Θ = 0 ↔ σ = 1 / 2

unresolved source recovery:
  zeta zero → offCriticalCFBRC d s.re (phase s) = 0
```

The first does not imply the second.  Any historical conditional theorem whose
antecedent is a bridge/provider was therefore treated as conditional until the
antecedent was checked for an independent construction.  The moving-line
`research_goal` fails this check explicitly through `sorryAx`.

## 7. Smallest remaining non-circular obligation

After removing all definitional packaging and algebraic consequences, the
smallest reusable interface is the degree-two instance

```lean
∃ (phase : ℂ → ℝ),
  ∀ {s : ℂ}, NontrivialRiemannZetaZero s →
    offCriticalCFBRC 2 s.re (phase s) = 0
```

or, equivalently, an inhabited
`ZeroToCFBRCTwoBridge NontrivialRiemannZetaZero`.  The general positive-degree
version is already available and has the same logical boundary.  Proving this
statement from the zeta-zero equation, without using RH or any frontier listed
above, is the genuine unresolved source-recovery task.  The CFBRC exclusion
theorem itself is not the missing step.

## 8. Recommendation for ZDI-002

Proceed with the roadmap's DkReal interface audit only: expose the smallest
common-shrinking-interval uniqueness theorem for two real values, reusing
existing `DkReal.Semantic` results where possible.  Keep this theorem
independent of `RiemannHypothesis`, `map_zero`, all RH-equivalent frontiers,
and all asymptotic or strip assumptions.  Do not use ZDI-002 to manufacture a
new analytic source-recovery provider.

## 9. Verification

The report and the existing load-bearing modules were checked with:

```text
cd /home/deskuma/develop/lean/dkmath/lean/dk_math
./lean-build.sh DkMath.RH.CFBRC.StandardZetaBridge
./lean-build.sh DkMath.RH
```

Both narrow module builds and the RH umbrella build completed successfully.
The temporary `ZDI001Check.lean` and `ZDI001ResearchCheck.lean` files used for
the printed declaration and axiom inspection are audit fixtures only and are
not part of the repository change.
