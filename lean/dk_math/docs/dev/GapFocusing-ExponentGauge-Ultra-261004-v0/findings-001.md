# Gap Focusing / Exponent Gauge Ultra — Findings 001

Branch: **research/GapFocusing-ExponentGauge-Ultra-261004-v0**

Base: current `develop` after merged PR #112.

This file is the durable incremental state of the Ultra exploration.

## Current status

- Source inventory completed for the focused identity, polynomial remainder,
  generic product-degree composition, and the existing cyclotomic shell.
- New neutral APIs are being checked in `DkMath.NumberTheory.GapFocusing`.
- Outcome B selected: the algebraic focusing/phase/degree chain is checked;
  the unit-power class requires the later fixed extraction and normalization.

## Starting picture

General power-difference coordinates:

```text
a = x + u
b = u
a - b = x
```

Focused power difference:

```text
(x+u)^d - u^d = x * GN_d(x,u).
```

Unfocused comparison anchor:

```text
(x+u)^d - v^d
  = x * GN_d(x,u) + (u^d-v^d).
```

Working interpretation only:

```text
u^d-v^d = focus defect.
```

This interpretation must be tested rather than assumed.

## Candidate structural chain

```text
general power difference
-> Gap focus
-> trivial/nontrivial cyclotomic phase split
-> composite/prime degree behavior
-> possible residual exponent/unit gauge.
```

No theorem currently asserts the whole chain.

## Questions to resolve

| Question | Status |
| --- | --- |
| Is the x-factorization canonical after fixing the anchor u? | Yes: formal polynomial quotient and constant remainder are unique |
| Is x-divisibility equivalent to zero focus defect in a useful generic setting? | Yes for formal `X`; evaluated divisibility only detects divisibility of the defect |
| Is the zeta=1 phase uniquely u-free? | Yes universally/polynomially; pointwise needs nonzero background in a domain |
| Does GN product-degree decomposition characterize composite degree structurally? | Composite degrees give two nonunit factors at unit boundary over `ℤ[X]` |
| Is there an honest Prime Degree Rigidity theorem? | `2≤d`: irreducible `GN_d(X,1)` over `ℤ[X]`/`ℚ[X]` iff prime degree |
| Does focused phase freedom explain the FLT unit-power class? | Coefficient bridge exists; residual class needs extra extraction and normalization data |
| What does 2p=p*2 encode before any geometric interpretation? | Two composition orders; odd-prime case has exactly the three layers `Φ₂,Φ_p,Φ₂p` |

## Prior result to preserve

Merged PR #112 established:

```text
fixed order/source/ramifier
A = lambda * u * beta^p
[u] in R^×/(R^×)^p
```

with root-choice independence and normalization dependence on the actual p=3,
p=5, and p=7 production rings.

This run must not silently strengthen that result.

## Next action

Bounded exploration complete. The checked checkpoint for future work is
[report](report-001.md), [source inventory](source-inventory-001.md), and
[validation](evidence/MANIFEST.md#log-2a85498f28567ebe). Further phase/unit or planar maps
need an explicit source-specific object and its arithmetic hypotheses.

## Checkpoint history

### 2026-10-04 checkpoint 00 — workspace seed

- PR #112 verified merged to `develop`.
- New research branch created from current `develop`.
- Exploration intentionally separates algebraic facts from the Gap-focusing
  interpretation.
- Magic-square / planar 2p remains a downstream calibration question only.

### 2026-10-04 checkpoint 01 — source inventory and formal-variable boundary

- Current branch and Lean toolchain verified: the branch named above,
  `leanprover/lean4:v4.34.1`; initial working tree clean.
- `DkMath.CosmicFormula.add_pow_eq_mul_GTail_one_add_gap` and
  `GN_mul_degree` already hold for every commutative semiring.
- `GTail_one_eq_GTailCyclotomicShell` is already cancellation-free, including
  zero gap. `DkMath.Lib.NumberTheory.prod_cyclotomicEval_eq_geomSum`
  already gives the nontrivial divisor product in a commutative ring.
- `DkMath.NumberTheory.prime_degree_of_prime_GN` is already available for
  positive natural gap and anchor; it is a necessary condition on a prime
  value, not an irreducibility theorem.
- Mathlib `Polynomial.X_dvd_iff` identifies the constant coefficient as the
  exact obstruction. Thus the requested equality criterion belongs to a
  formal gap `X`. After evaluation, divisibility only says that the defect
  is divisible by the chosen numerical gap.
- The document's expected Outcome B is treated as a hypothesis to audit;
  its six phases organize this research, while the user's request authorizes
  source investigation and checked Lean formalization.

### 2026-10-04 checkpoint 02 — focused/unfocused divisibility checked

`lake build DkMath.NumberTheory.GapFocusing.Focus` passed (1390 jobs).

- `focusCoordinates` is an additive-coordinate equivalence, so the
  substitution itself loses no information.
- `X_dvd_unfocused_iff` proves the exact criterion over every commutative
  coefficient ring, including zero degree and rings with zero divisors.
- `focused_quotient_unique` and `unfocused_constant_unique` show that the
  normalized quotient and the constant defect are uniquely determined.
- `gap_dvd_iff_dvd_defect` is the weaker, correct evaluated criterion.
- `focusDefect_cocycle` and `focusDefect_scale` check change of anchor and
  simultaneous scaling. The defect is not claimed to be an invariant.
- `focused_quotient_eval_zero` retains `d*u^(d-1)` in GN;
  `X_sq_dvd_focused_iff` detects exactly when an extra gap factor occurs.

### 2026-10-04 checkpoint 03 — cyclotomic phase analysis checked

- `lake build DkMath.NumberTheory.GapFocusing.Phase` passed (2787 jobs).
- In a commutative domain admitting a primitive `d`th root (`d > 0`),
  `focused_pow_sub_pow_eq_prod` factors through the intrinsic root set.
- `GN_eq_nontrivial_phase_prod` removes exactly the root `1`; the proof
  cancels formal `X` before evaluation and remains valid at zero numerical gap.
- Universal and polynomial independence of the background are equivalent
  to phase `1`. Pointwise uniqueness additionally needs a nonzero background
  in a domain. At zero background all factors specialize to `x`.
- Primitive-generator labels vary, but the root set, trivial phase, and
  complete residual product are intrinsic.

### 2026-10-04 checkpoint 04 — structural degree rigidity checked

- `lake build DkMath.NumberTheory.GapFocusing.Degree` passed (2811 jobs).
- `kernelPolynomial_eq_prod_cyclotomic` retains all nontrivial degree
  divisors as translated cyclotomic layers in `ℤ[X]` at anchor `1`.
- `kernelPolynomial_irreducible_iff_prime` proves an actual irreducibility
  criterion for `d ≥ 2`. This gives more than the absence of degree routes,
  while explicitly restricting the coefficient ring and the unit anchor.
- Composite degree gives two nonunit polynomial factors through the existing
  GN composition API. Prime degree does not imply a prime numerical value
  or irreducibility over every coefficient ring.

### 2026-10-04 checkpoint 05 — unit-gauge bridge and failed identification

- `lake build DkMath.NumberTheory.GapFocusing.UnitGauge` passed (1920 jobs).
- `phase_geometric_sum_unit` checks the actual cyclotomic unit rewriting
  `1-zeta^j` when the phase index is coprime to the root order.
- `phase_polynomial_associated_iff` proves that distinct phase polynomials
  with nonzero background remain non-associated: association of their
  ramifier coefficients does not identify their full linear carriers.
- The prior normal-domain root-choice independence theorem has been promoted
  from the FLT357 audit into production, with fixed nonzero extraction and
  ramifier inputs. No phase factorization constructs those inputs.
- `ramifier_rescaling_same_class_iff` gives the precise condition for a
  normalization change to preserve the class. A finite `ZMod 7`, exponent
  `3` regression proves it can fail for prime exponent.
- Current ideal-power and principalization APIs require extra arithmetic
  data. This rejects the proposed automatic phase-to-residual-class
  identification and supports Outcome B.

### 2026-10-04 checkpoint 06 — 2p calibration checked

- Both orders `p then 2` and `2 then p` hold over every commutative semiring,
  with no primality, nonzero gap, or cancellation requirement.
- For odd prime `p`, `kernelPolynomial_two_mul_prime` gives exactly
  `(X+2)*Φ_p(X+1)*Φ_{2p}(X+1)`, with layer degrees `1,p-1,p-1`.
- The divisor theorem also checks the `p=2` collapse to two distinct layers.
- The algebra supplies intermediate gap/boundary coordinates, but no object
  map to a plane or a magic-square configuration was identified.
- The rational irreducibility counterpart also passed using monicity and
  Gauss's lemma. Degree11 has irreducible polynomial but composite value
  `GN 11 1 1 = 23*89`, checked in the durable degree regression.

### 2026-10-04 checkpoint 07 — aggregate validation and closeout

- New facade and four test/audit targets passed: 2820 jobs, no warnings.
- Main `DkMath` facade passed: 10355 jobs; five existing research `sorry`
  warnings are recorded separately from the new package's dependency audit.
- All 50 public theorems and `focusCoordinates` have dependencies contained
  in `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- Forbidden-construct scan is clean across all nine new Lean files.
- The earlier actual-carrier unit audit was rerun successfully.
- Independent source review confirmed the coefficient-ring/unit-anchor,
  primitive-root, nonzero-background, and arithmetic-extraction boundaries.
- Outcome B and the remaining interpretive questions are recorded in the
  report. Build and audit output is preserved in this directory's `logs`.

### 2026-10-04 checkpoint 08 — positive actual-carrier bridge checked

- The current p=7 carrier already has the exact focused coordinates
  `x=R-L`, `u=L` in its degree-six ring. This was found inside the existing
  ramifier-quotient proof after the initial generic phase/unit audit.
- `checks/SevenCarrierBridge.lean` independently proves that coordinate
  identity, pairs it with the same packet's actual arithmetic extraction,
  and specializes the new fixed-extraction unit-class API to this carrier.
- `lake env lean .../checks/SevenCarrierBridge.lean` passed; all three
  declarations depend only on `propext`, `Classical.choice`, `Quot.sound`.
- This is a concrete positive phase/carrier connection. The ideal-power and
  principal-generator inputs remain in the next arithmetic step, so the
  final classification remains Outcome B.
