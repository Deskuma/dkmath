# IPSM-046 — CS22 closeout and CS23 independent radial-contact provider audit

## 0. Status

Branch: `wip/RH-CFBRC-prime-side-sign-mechanism-260813-v1`

CS22 verdict: **Green-B**.

CS22 has closed the adapter loop

`finite arithmetic upper anchor ↔ cofinal radial contact ↔ fixed-ε endpoint upper bound`.

This document therefore changes the research discipline for the next checkpoint:

> After CS22, a new equivalent predicate, wrapper, or provider structure is not counted as progress.  CS23 must derive a genuinely new finite prime-side estimate or decomposition from the explicit source ledger.

No RH conclusion is authorized here.

---

## 1. What CS22 actually closed

For positive `ε`, a residue transport window `W`, and finite cutoff `X`, CS22 defines

`G_{ε,W,X} := π Q_R - S_{ε,W,X}`,

where `Q_R` is the fixed radial second-moment functional and `S_{ε,W,X}` is the finite scalar arithmetic surface.

The implementation proves the exact identity

`G_{ε,W,X} = π D_{ε,W,X}`.

Hence the pointwise target

`D_{ε,W,X} ≤ r`

is exactly the scalar radial-contact target

`π (Q_R - r) ≤ S_{ε,W,X}`.

At `r = 0` this is the already-known Q3 finite radial comparison.  CS22 does not create a new sign mechanism; it identifies the CS21 good-cutoff language with the weakest cofinal form of that existing comparison.

The zero-target cofinal contract is further classified as

`CofinalRadialContactZeroAt ε W ↔ D_{ε,∞} ≤ 0`.

Thus the long CS10–CS22 chain has returned to the original radial-comparison frontier in a strictly weaker, oscillation-tolerant, cofinal form.

This is the desired closure-loop audit result.

---

## 2. Why another adapter is no longer useful

The following moves are now forbidden as claims of progress:

- renaming `D_{ε,X} ≤ r` as a new provider;
- renaming cofinal radial contact as a new provider;
- deriving the endpoint inequality from a hypothesis definitionally equivalent to it;
- using the fixed-Xi defect nonnegativity or RH-equivalent zero-side theorem as the arithmetic provider;
- using CS18 CF2D translation alone as a sign provider;
- using CS20 monotonicity, since it was classified as equivalent to nonnegativity of every prime-power mode kernel;
- assuming universal tail sign;
- assuming the desired aggregate energy ordering.

A CS23 Green result must introduce a source-derived theorem whose hypotheses are independently available before the target comparison is known.

---

## 3. CS23 target: an independent finite-source decomposition

The preferred target is not a bare inequality.  Search instead for an exact decomposition of the finite radial-contact deficit into a sign-controlled finite source part plus a quantitatively small remainder.

A useful schematic form is

`G_{ε,W,X} = R_{ε,W,X} - M_{ε,W,X}`,

with independently proved properties

`0 ≤ M_{ε,W,X}`

and, along a selectable cofinal family of finite cutoffs,

`R_{ε,W,X} ≤ η`.

Then one gets

`G_{ε,W,X} ≤ η`

without assuming the desired radial comparison.

The signs in this schematic form are intentional.  A decomposition

`G = positive mass + small remainder`

would not supply the required upper contact unless the positive mass were independently shown to vanish; that would merely move the RH-strength gap.

Alternative equivalent decompositions are acceptable, for example a direct certificate

`G_{ε,W,X} + M_{ε,W,X} = R_{ε,W,X}`

with `M ≥ 0` and a vanishing upper bound for `R`.

---

## 4. Source restrictions

`M` and `R` must be constructed from the finite prime-side source ledger already present in CS21/CS22:

- finite von-Mangoldt / prime-power terms;
- Mellin quadratic box weight;
- archimedean right-edge correction;
- elementary right-edge correction;
- finite top-horizontal contribution;
- finite prime-power ray / geometric-ray identities from CS14–CS18;
- finite block and cutoff identities from CS12–CS21.

Allowed algebraic/analytic infrastructure includes:

- finite sums and exact reindexing;
- finite interval integrals;
- `Complex.normSq` / CF2D `Vec.q2` bridges already proved;
- Cauchy–Schwarz, triangle inequality, finite Gram positivity, or other ordinary inequalities when their hypotheses are proved from the source;
- fixed-`ε` cutoff convergence already established;
- explicit finite error estimates.

Do not import a zero-side sign theorem to certify `M` or `R`.

---

## 5. Candidate route A — source-complete square / q2 remainder

CS16–CS18 showed that each compressed prime-power ray admits exact `normSq` / `q2` polarization.  Audit whether the **full finite source**, after adding the non-prime and top-horizontal corrections, admits a completion of squares in which the desired radial-contact deficit appears with the correct sign.

The test is strict:

1. define the complete finite complex source amplitude from existing terms;
2. derive the decomposition by algebra/integration from existing definitions;
3. identify every square-mass term explicitly;
4. check the sign orientation against `G = π D`;
5. reject the route if the decomposition produces `G = +M + R` with `M ≥ 0` and no independent cancellation.

Do not manufacture a synthetic square whose definition already contains `G`.

---

## 6. Candidate route B — finite block cancellation with adaptive cutoff

CS21 only needs arbitrarily late good cutoffs, not a monotone sequence and not per-mode positivity.

Therefore a legitimate source theorem may have the form:

for every tolerance `η > 0` and lower cutoff `N`, there exists `X ≥ N` such that a finite block/ray cancellation estimate gives

`G_{ε,W,X} ≤ η`.

The existence of `X` must come from an independent finite arithmetic mechanism, for example:

- cancellation among complete prime-power rays;
- a finite geometric-series endpoint estimate;
- a pigeonhole/averaging argument over a finite cutoff block;
- a finite mean-square estimate whose average upper bound forces at least one good cutoff.

This route is preferable to universal mode positivity because it preserves the oscillation detected in CS13 and the aggregate cancellation freedom preserved through CS20.

A particularly valuable subtarget is an averaged theorem over a finite cutoff interval:

`average_{X in block} G_{ε,W,X} ≤ η`.

Such a theorem would immediately yield one good cutoff without requiring every cutoff to behave well.

---

## 7. Candidate route C — finite Gram estimate, but only if source-complete

The repository already has a positive Mellin Gram kernel/energy.  Earlier audits correctly rejected using it directly because the arithmetic source was a one-index linear surface while the Gram form was two-index quadratic.

CS14–CS18 have since compressed the prime source into finite prime-power rays and q2 ledgers.  Re-audit the Gram route only under the following stronger requirement:

> construct an explicit coefficient/state family from the actual finite von-Mangoldt source and prove that the resulting Gram energy equals or bounds the **complete** finite radial-contact deficit, including all correction surfaces.

A theorem about a positive auxiliary Gram energy with no exact source-complete bridge is not a provider.

---

## 8. Strength firewall

The following are classification facts only and may not be used as source providers:

- `VanishingUpperEnvelopeAt W ↔ fixed defect ≤ 0`;
- with zero-side nonnegativity, the same envelope is equivalent to fixed defect zero;
- fixed defect equals horizontal/off-critical energy;
- fixed-defect vanishing characterizes criticality of the finite zero window;
- global vanishing characterizes RH.

These theorems are useful for measuring the strength of a successful CS23 provider, not for proving it.

Likewise, the CS22 theorem equating the named anchor gap and named radial-contact gap is only a bookkeeping equivalence between frontier labels.  It is not evidence that either provider exists.

---

## 9. Concrete Lean checkpoint order

Prefer a new chained module, for example

`PascalCenteredXiPrimeSideIndependentRadialContactProviderAudit.lean`.

Suggested order:

### CS23-A — canonical finite deficit source expansion

Expose `G_{ε,W,X}` directly in terms of the complete finite source ledger, without using endpoint or zero-side sign facts.

### CS23-B — candidate signed-mass decomposition

Attempt an exact source-derived decomposition into a nonnegative finite mass and a remainder.  Keep the direction of the inequality visible.

### CS23-C — remainder estimate or obstruction theorem

Either prove a quantitative finite bound sufficient for a good cutoff, or prove that the candidate decomposition has the wrong sign/insufficient information and record a named obstruction.

### CS23-D — cofinal good-cutoff adapter

Only after CS23-B/C supplies genuinely independent input, transport it through the already proved CS21/CS22 adapters to `CofinalRadialContactAt`.

### CS23-E — frontier

If no independent source estimate is obtained, retain a named gap such as

`PascalCenteredXiPrimeSideIndependentRadialContactProviderGap`.

Do not fill this gap with a field that merely assumes cofinal radial contact.

---

## 10. Acceptance criteria

CS23 is **Green** only if it proves a new source-derived estimate that implies a cofinal radial-contact statement without assuming any equivalent endpoint/radial/fixed-defect sign condition.

CS23 is **Green-B** if it obtains a substantial exact decomposition or averaging identity but the final source estimate remains open.

CS23 is **Yellow** if it only introduces a promising auxiliary object with no exact bridge to the complete finite deficit.

CS23 is **Red** if the proposed provider assumes the target sign, imports the zero-side RH frontier as a provider, or hides an infinite exchange not already authorized.

---

## 11. Research interpretation

The CS10–CS22 path has not proved the missing sign.  It has done something structurally valuable: it has removed a sequence of unnecessarily strong candidate hypotheses.

The target weakened through

`universal mode sign → aggregate ordering → cutoff monotonicity → terminal ceiling → tail sign → cofinal good cutoff → cofinal radial contact`.

At CS22 this chain closes back onto the original Q3 radial-comparison frontier.

Therefore the next mathematical content cannot come from another reformulation.  It must come from a new property of the finite prime-side source itself.

That is the CS23 frontier.
