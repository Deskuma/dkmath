# IPSM-061 — CS37 closeout and CS38 mirror-weighted source recovery audit

## 0. Status

- Canonical branch: `wip/RH-CFBRC-prime-side-sign-mechanism-260813-v1`
- CS37 implementation: `DkMath.RH.CFBRC.PascalCenteredXiPrimeSideFiniteResidualMirrorPairedBranchFreeRateAudit`
- CS37 verdict: **Green-B**
- CS37 result: the safe finite mirror-paired residual rate has an exact branch-free decomposition into completed-zeta mirror rate, Gamma mirror rate, and finite reflected PHZ rate.
- No new reach inequality, scalar sign, rectangle-background cancellation, limit exchange, infinite Euler product, or RH conclusion has been obtained.

CS37 is a genuine source-level advance: the CS36 value factorisation is now matched by a concrete rate-level source decomposition.

---

## 1. CS37 facts now fixed by Lean

CS37 defines the branch-free completed-zeta negative logarithmic rate

`CompletedRate(s) := -logDeriv completedRiemannZeta s`.

At a safe ordinary point it proves

`CompletedRate(s) = pascalXiOrdinaryZetaNegLogDeriv(s) + pascalXiArchimedeanLogDeriv(s)`.

Equivalently,

`pascalXiOrdinaryZetaNegLogDeriv(s) = CompletedRate(s) - pascalXiArchimedeanLogDeriv(s)`.

The finite reflected prime-power rate is

`SymEulerRate_X(s) := PHZ_X(1-s) - PHZ_X(s)`.

Lean proves its conjugation law.

CS37 then defines

`CompletedMirrorRate(s) := CompletedRate(s) - CompletedRate(1-s)`,

`GammaMirrorRate(s) := -GammaRate(s) + GammaRate(1-s)`,

and

`FunctionalEquationRate_X(s) := CompletedMirrorRate(s) + GammaMirrorRate(s) + SymEulerRate_X(s)`.

On the safe top interval, with `s(u) := pascalSymmetricRectangleTopEdge u W.rectangle.T`, the principal theorem is

`PairRate_X(u) = FunctionalEquationRate_X(s(u))`.

The mirror functional-equation rate satisfies

`FunctionalEquationRate_X(1-s) = -FunctionalEquationRate_X(s)`.

At the algebraic center `s = 1/2`, Lean proves

`FunctionalEquationRate_X(1/2) = 0`.

### Center warning

The theorem above is about the complex-variable point `s = 1/2`.

It does **not** assert that the top-edge midpoint `u = 1/2` has zero paired rate. At `u = 1/2`, the ordinary top point is `s = 1/2 + iT`, not `s = 1/2` unless `T = 0`.

This distinction must remain explicit in later arguments.

### Current frontier

CS37 deliberately leaves

`PascalCenteredXiPrimeSideFiniteResidualMirrorPairedRateCancellationGap.no_exact_rectangle_background_cancellation_from_rate_ledger`.

Therefore Green-B is the correct verdict.

---

## 2. Existing fixed-Xi bridge that CS38 must reuse

Do not rebuild the functional-equation reflection layer.

`PascalCenteredXiExplicitFormulaFunctionalEquationReflection` already proves the fixed centered-Xi identity

`pascalCenteredXiNegLogDeriv(pascalOrdinaryToCentered s) = ordinaryZetaRate(s) + GammaRate(s) + ElementaryRate(s)`

under the ordinary factor hypotheses.

The same module proves centered oddness

`pascalCenteredXiNegLogDeriv(-z) = -pascalCenteredXiNegLogDeriv(z)`.

It also proves the reflected combined decomposition

`pascalXiDecomposedNegLogDeriv(1-s) = -pascalXiDecomposedNegLogDeriv(s)`

when both ordinary points are safe.

CS37 separately proves

`CompletedRate(s) = ordinaryZetaRate(s) + GammaRate(s)`.

Therefore the next exact bridge is already algebraically determined:

`FixedXiRate(centered s) = CompletedRate(s) + ElementaryRate(s)`.

This is not a new analytic hypothesis. It should be proved by combining the existing source theorems.

---

## 3. CS38 target

Suggested module:

`DkMath.RH.CFBRC.PascalCenteredXiPrimeSideFiniteResidualMirrorWeightedSourceRecoveryAudit`

The purpose of CS38 is to transport the exact CS37 rate ledger into the actual Mellin-weighted scalar observable used by the finite top mismatch.

The desired progression is:

1. completed-zeta rate to fixed-Xi plus elementary correction;
2. paired rate to three exact weighted scalar channels;
3. full residual scalar integral to the existing mirror-paired oriented half interval;
4. recovery of the fixed-Xi, Gamma, elementary, and finite-PHZ top sources with exact orientation and normalization;
5. comparison with the existing CS28/CS29/CS30 rectangle ledger;
6. retain a named frontier unless an actual source-derived rectangle-background cancellation is proved.

No sign estimate is a CS38 requirement.

---

## 4. CS38-A — completed rate to fixed-Xi rate

Prove a theorem of the form

`CompletedRate(s) + ElementaryRate(s) = pascalCenteredXiNegLogDeriv(pascalOrdinaryToCentered s)`

under the same local factor hypotheses already used by CS37 and the XDP functional-equation bridge.

Then, when both `s` and `1-s` are safe, combine centered oddness with the previous identity and derive the exact completed-mirror reduction

`CompletedMirrorRate(s) = 2 * FixedXiRate(centered s) - ElementaryRate(s) + ElementaryRate(1-s)`.

The signs here follow from

`FixedXiRate(centered s) = CompletedRate(s) + ElementaryRate(s)`

and

`FixedXiRate(centered (1-s)) = -FixedXiRate(centered s)`.

Let Lean verify the final ring normalization. Do not replace this by an informal functional-equation argument.

This reduction is important because it moves the completed-zeta term back into the already installed fixed-Xi contour source while exposing the elementary correction explicitly.

---

## 5. CS38-B — weighted mirror source densities

Use the existing top Mellin weight

`H(u) := pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W u`

and top ordinary coordinate

`s(u) := pascalSymmetricRectangleTopEdge u W.rectangle.T`.

Define only the channel densities that are useful for exact source recovery. A reasonable set is:

- completed mirror density: `Im(H(u) * CompletedMirrorRate(s(u)))`;
- Gamma mirror density: `Im(H(u) * GammaMirrorRate(s(u)))`;
- finite-PHZ mirror density: `Im(H(u) * SymEulerRate_X(s(u)))`.

Prove pointwise

`MirrorScalarDensity = CompletedMirrorDensity + GammaMirrorDensity + FinitePHZMirrorDensity`.

Then use CS38-A to rewrite the completed channel into

- a doubled fixed-Xi centered source;
- an elementary reflected difference.

After rewriting, the paired scalar density should have the schematic exact form

`Im(H * (2 * FixedXiRate + reflectedGammaDifference + reflectedElementaryDifference + reflectedPHZDifference))`.

All plus/minus signs must come from the installed CS37 definitions and the CS38-A theorem.

Do not infer any sign from the words `rate`, `difference`, `mirror`, or `norm`.

---

## 6. CS38-C — top mismatch as the paired oriented half-interval integral

CS31 gives the finite top zeta mismatch as the Mellin-weighted residual integral. After the normalized `(2 * π * I)⁻¹` projection, its scalar is the imaginary residual integral divided by `π`.

CS35 already proves that the full residual scalar integral equals the mirror-paired scalar integral over the oriented interval from `W.rectangle.σ` to `1/2`.

Therefore CS38 should prove an explicit theorem of the form

`TopZetaMismatchScalar = (1 / π) * ∫ u in W.rectangle.σ..(1/2), MirrorScalarDensity(u)`.

Do not silently reorder the interval. The rectangle has `1 < σ`, so this is an oriented interval whose endpoints appear in decreasing real order.

Prefer deriving all required integrability from the safe finite interval and the existing CS34 continuity theorems. If a component-specific integrability fact is not yet available, state only the minimal local hypothesis and remove it later when a source theorem becomes available.

---

## 7. CS38-D — generic mirror-integration adapter

A reusable finite adapter is valuable here.

For a source `Q` satisfying the appropriate conjugation law, the top-edge geometry gives

`conj(s(1-u)) = 1 - s(u)`

while the Mellin weight satisfies

`H(1-u) = conj(H(u))`.

This permits an exact conversion between a full top integral of `Im(H(u) * Q(s(u)))` and an oriented half-interval integral of the reflected difference of `Q`.

Prove the generic adapter only from:

- the affine mirror `u ↦ 1-u`;
- the weight conjugation law;
- the source conjugation law;
- interval-integrability.

No analytic continuation, limit, or sign input belongs in this helper.

This adapter should then be instantiated for the concrete source families below instead of duplicating reflection algebra.

---

## 8. CS38-E — recover the concrete top sources

Use the generic adapter to compare the CS38 half-interval channels with the already named full top sources.

Audit these four channels separately.

### 8.1 Fixed-Xi channel

The doubled fixed-Xi term on the half interval should recover the full fixed-Xi top horizontal scalar source, using centered oddness plus conjugation.

Do not assume the factor of two. Derive it from the mirror adapter and the existing orientation.

### 8.2 Gamma channel

`GammaMirrorRate(s) = -GammaRate(s) + GammaRate(1-s)`.

The corresponding half-interval scalar should recover the full Gamma top source with the sign dictated by this definition.

### 8.3 Elementary channel

The elementary reflected difference produced by CS38-A should similarly recover the existing full elementary top source.

### 8.4 Finite PHZ channel

`SymEulerRate_X(s) = PHZ_X(1-s) - PHZ_X(s)`.

Its half-interval scalar must be compared with the existing finite arithmetic top-edge integrand / top companion.

This remains a finite sum. Do not introduce an infinite Euler expansion.

### Normalization firewall

The existing top ledgers use both raw complex contributions and normalized scalar projections. Factors `2`, `π`, and orientation signs must be proved from the definitions. Do not copy them from a schematic calculation.

---

## 9. CS38-F — close the top-ledger consistency square

After the four channel identifications, compare the result with the existing CS28/CS29 top ledger.

An exact equality that merely reproduces the already known definition of the top zeta cutoff mismatch is a **consistency theorem**, not a new cancellation theorem.

Record it as such.

A useful final CS38 theorem would show that the following two constructions of the same scalar mismatch agree exactly:

1. the original full-top residual integral / finite arithmetic cutoff construction;
2. the CS35/CS37 mirror-paired half-interval functional-equation rate construction.

This would certify that the functional-equation fold has preserved the actual prime-side scalar observable without hidden branch, orientation, or normalization changes.

---

## 10. CS38-G — rectangle-background audit

Only after the top-ledger consistency square is closed should CS38 substitute the recovered source identity into the CS30 finite rectangle background / radial-contact-deficit theorem.

Acceptable outcomes are:

1. a genuine exact cancellation of named source terms, leaving a strictly smaller explicit remainder;
2. an exact re-expression of the old frontier in a more structured remainder;
3. no simplification beyond the existing ledger.

If the remaining term is identified with the zero-side fixed defect, horizontal energy, or an RH-equivalent quantity, record that identification only as a classification. Do **not** use the zero-side theorem as the provider of the required prime-side sign or reach estimate.

No theorem may be called `cancellation` unless terms actually cancel algebraically in Lean.

---

## 11. CS38 frontier

If CS38 closes the weighted source-recovery and top-ledger consistency but does not produce a new independent reach estimate, retain a named frontier such as

`PascalCenteredXiPrimeSideFiniteResidualMirrorWeightedRectangleReachGap.no_independent_rectangle_background_reach_provider`.

The existing CS37 gap may remain as historical provenance, but CS38 should expose the narrowest remaining frontier after all exact weighted identities have been installed.

---

## 12. Verdict rules

### Green-B

Use **Green-B** if CS38 proves the concrete weighted source decomposition and closes the top-ledger consistency square, while rectangle reach/sign remains open.

### Green

Use **Green** only if a genuinely source-derived new cancellation or estimate removes a nontrivial part of the rectangle-background frontier without importing a zero-side/RH-equivalent provider.

### Yellow

Use **Yellow** if the weighted decomposition is represented only through new abstract providers or if crucial orientation/normalization factors remain assumed.

### Red

Use **Red** if any of the following occurs:

- `Complex.log` branch arguments are introduced unnecessarily;
- an infinite Euler product is substituted for the finite PHZ source;
- a cutoff/integral/limit exchange is used without proof;
- the algebraic center `s = 1/2` is confused with the top-edge midpoint `u = 1/2` at `T > 0`;
- a complex square is treated as an ordered real square;
- a zero-side fixed-defect / horizontal-energy / RH theorem is used as the missing prime-side reach provider;
- RH is concluded from the representation alone.

---

## 13. Recommended implementation order

1. Prove `CompletedRate + ElementaryRate = FixedXiRate` from installed theorems.
2. Derive the completed-mirror reduction using fixed-Xi oddness.
3. Define the minimal weighted mirror channel densities.
4. Prove pointwise decomposition of `MirrorScalarDensity`.
5. Derive source-level integrability on the safe finite interval.
6. Prove `TopZetaMismatchScalar` as the paired oriented half-interval integral divided by `π`.
7. Implement the generic mirror-integration adapter.
8. Recover fixed-Xi, Gamma, elementary, and finite-PHZ top sources one at a time.
9. Close the equality with the existing top mismatch ledger.
10. Substitute into the rectangle background and record only actual cancellations or the exact surviving remainder.
11. Add the new module to `DkMath/RH.lean` only after standalone Lean validation.
12. Run `lake env lean`, `lake build DkMath.RH`, `git diff --check`, and audit the new file for `sorry`, `axiom`, and `native_decide`.

The central CS38 question is no longer whether the functional-equation rate exists. Lean has fixed that in CS37. The question is whether that exact rate decomposition, after the actual Mellin weighting and mirror integration used by the prime-side scalar observable, produces a genuinely smaller rectangle remainder or only a new exact representation of the same frontier.
