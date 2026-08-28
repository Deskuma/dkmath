# IPSM-058 — CS34 closeout and CS35 mirror-paired residual / half-interval audit

## 0. Status

Branch: `wip/RH-CFBRC-prime-side-sign-mechanism-260813-v1`

CS34 verdict: **Green-B**.

CS34 removed the technical global-continuity overreach from CS33 and proved the finite regularity layer directly from the safe top-edge source:

- local continuity of the ordinary-zeta negative log derivative on the safe top interval,
- local continuity and `ContinuousOn` for the finite residual log-rate,
- interval integrability of residual / phase / amplitude rates,
- source-derived Mellin-weight derivative regularity and integrability,
- interval-local integration-by-parts ledgers,
- source-derived branch-free phase endpoint transport,
- source-derived weighted-displacement ledger,
- source-derived `log (normSq residual)` endpoint replacement.

The remaining frontier is no longer regularity.  It is the independent weighted-displacement reach estimate.

CS35 must not introduce another abstract reach provider.  The next task is to compress the already exact reach observable by the top-edge mirror `u ↦ 1-u`.

---

## 1. Geometry of the centered top mirror

For

```text
s(u) := u + iT,
z(u) := s(u) - 1/2,
```

prove the exact identities

```text
s(1-u) = 1 - conj(s(u)),
z(1-u) = -conj(z(u)).
```

Also prove mirror preservation of the safe interval:

```text
u ∈ uIcc σ (1-σ) → 1-u ∈ uIcc σ (1-σ).
```

No zero-free strip outside this finite interval may be introduced.

---

## 2. CS35-A — Mellin top-weight mirror conjugation

Let

```text
Hε(u) := pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W u.
```

Prove, for `0 < ε`,

```text
Hε(1-u) = conj(Hε(u)).
```

The intended source is the centered-box structure:

- the centered Mellin multiplier is even in the centered spectral variable,
- it is compatible with complex conjugation because the logarithmic averaging interval and coefficients are real,
- the quadratic factor is even.

Do not assume this identity merely from the name “centered”.

Derive the real-channel parity laws:

```text
Re Hε(1-u) = Re Hε(u),
Im Hε(1-u) = - Im Hε(u).
```

If useful for the displacement form, also derive the differentiated parity:

```text
(Re Hε)'(1-u) = - (Re Hε)'(u),
(Im Hε)'(1-u) =   (Im Hε)'(u),
```

with the correct chain-rule signs.

---

## 3. CS35-B — mirror-paired residual product

Let the CS32 top residual path be

```text
F_X(u) := pascalCenteredXiPrimeSideFiniteResidualTopPath X W u.
```

Define the branch-free mirror-paired product

```text
PairF_X(u) := F_X(u) * conj(F_X(1-u)).
```

On the safe top interval prove:

```text
PairF_X(u) ≠ 0.
```

At the center prove the canonical positive basepoint:

```text
PairF_X(1/2) = normSq(F_X(1/2)),
0 < Re(PairF_X(1/2)),
Im(PairF_X(1/2)) = 0.
```

The center statement must be derived from the CS30/32 nonzero residual theorem, not added as a hypothesis.

Also prove the mirror-conjugation symmetry

```text
PairF_X(1-u) = conj(PairF_X(u)).
```

This gives a canonical center for the paired phase carrier without `Complex.arg`.

---

## 4. CS35-C — paired residual log-rate

Let the CS31 residual rate be

```text
q_X(u) := pascalCenteredXiPrimeSideFiniteResidualLogRate X W u.
```

Define

```text
PairQ_X(u) := q_X(u) - conj(q_X(1-u)).
```

Prove directly from `F'_X = -q_X F_X`, with the chain rule for `1-u`, that

```text
PairF'_X(u) = - PairQ_X(u) * PairF_X(u)
```

on the safe interval.

Equivalently, wherever the local `logDeriv` API is convenient,

```text
-logDeriv PairF_X(u) = PairQ_X(u).
```

Do not use a logarithm branch.

Then prove the exact channel identities

```text
Re PairQ_X(u)
  = AmplitudeRate_X(u) - AmplitudeRate_X(1-u),

Im PairQ_X(u)
  = PhaseRate_X(u) + PhaseRate_X(1-u).
```

This is the precise pair required by the Mellin-weight parity.

---

## 5. CS35-D — mirror-paired scalar density

Let the original CS31 scalar density be

```text
ρ_X(u) := Im(Hε(u) * q_X(u)).
```

Define

```text
Pairρ_X(u) := Im(Hε(u) * PairQ_X(u)).
```

Using the weight mirror law, prove

```text
ρ_X(u) + ρ_X(1-u) = Pairρ_X(u).
```

Equivalently expose the two paired channels:

```text
Pairρ_X(u)
  = Re(Hε(u)) * (P_X(u) + P_X(1-u))
    + Im(Hε(u)) * (A_X(u) - A_X(1-u)).
```

This identity is algebraic.  No sign is allowed.

Also prove

```text
Pairρ_X(1-u) = Pairρ_X(u).
```

so the paired scalar density is mirror-even.

---

## 6. CS35-E — full top mismatch to half interval

The current exact scalar mismatch is

```text
MismatchScalar = (1/π) * ∫[σ → 1-σ] ρ_X(u) du.
```

First prove the mirror-average identity on the same oriented interval:

```text
∫[σ → 1-σ] ρ_X
  = (1/2) * ∫[σ → 1-σ] Pairρ_X.
```

Then use `Pairρ_X(1-u) = Pairρ_X(u)` to reduce to the canonical half interval:

```text
∫[σ → 1-σ] Pairρ_X
  = 2 * ∫[σ → 1/2] Pairρ_X.
```

The orientation matters because `1 < σ`, hence `1-σ < 1/2 < σ`.

The target theorem is therefore

```text
pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar ε W X
  = (1/π) * ∫ u in σ..(1/2), Pairρ_X(u).
```

Derive the exact normalization from the existing CS31/34 theorem; do not hard-code it from this roadmap if Lean gives a different algebraic factor.

---

## 7. CS35-F — paired polar carriers based at the center

Define paired amplitude and phase carriers from `PairF_X`:

```text
PairN_X(u) := normSq(PairF_X(u)),
PairU_X(u) := PairF_X(u) / conj(PairF_X(u)).
```

On the safe interval prove

```text
PairN_X(u) > 0,
normSq(PairU_X(u)) = 1.
```

At the center prove the canonical normalization

```text
PairU_X(1/2) = 1.
```

Define paired rates

```text
PairA_X := Re PairQ_X,
PairP_X := Im PairQ_X.
```

and prove the same branch-free transport equations as CS32:

```text
PairN'_X = -2 PairA_X PairN_X,
PairU'_X = -2 i PairP_X PairU_X.
```

If the finite interval-local regularity already suffices, define center-based displacements

```text
PairD_X(u) := ∫[1/2 → u] PairA_X(v) dv,
PairΘ_X(u) := ∫[1/2 → u] PairP_X(v) dv,
```

and prove the source-derived endpoint transports

```text
PairN_X(u)
  = PairN_X(1/2) * exp(-2 PairD_X(u)),

PairU_X(u)
  = exp(-2 i PairΘ_X(u)).
```

The second formula has no arbitrary base phase because `PairU_X(1/2)=1`.

This is a branch-free replacement for any principal-argument formulation.

---

## 8. CS35-G — ordinary-coordinate finite Euler pair identity

Audit the exact ordinary-coordinate meaning of the mirror product.

For

```text
s := pascalSymmetricRectangleTopEdge u T,
```

one has

```text
conj(pascalSymmetricRectangleTopEdge (1-u) T) = 1 - s.
```

Prove conjugation compatibility of the finite Euler potential / compensator and, if the existing `riemannZeta` conjugation API permits, expose

```text
PairF_X(u)
  = [ζ(s) * ζ(1-s)]
    * exp(-(A_X(s) + A_X(1-s))).
```

with the exact repository definitions and no infinite Euler product.

This theorem is highly desirable because it makes the mirror-paired residual a finite Euler-renormalized functional-equation pair.

However, if the needed zeta-conjugation lemma is absent or awkward in the pinned Mathlib version, record the precise missing local bridge and keep the rest of CS35 independent of it.

Do not invoke an infinite prime series in the critical strip.

---

## 9. Strength audit

CS35 is **not** a proof of reach.

The following are forbidden as progress claims:

- assuming `Pairρ_X ≥ 0`,
- assuming `PairP_X ≥ 0` or `PairA_X ≥ 0`,
- assuming monotonicity of paired phase or amplitude,
- replacing the old reach predicate by a new equivalent paired reach predicate and counting that alone as progress,
- using the fixed zero-side defect / RH equivalence as provider,
- taking `X → ∞` on the top edge by an unjustified Dirichlet-series argument.

Real progress in CS35 is the exact compression:

```text
full top residual
→ mirror-paired nonzero residual
→ canonical center basepoint
→ one half-interval scalar observable.
```

This should make the next source estimate strictly more geometric and less redundant.

---

## 10. Expected verdicts

### Green-B

The mirror weight parity, paired residual ODE, paired scalar density, half-interval mismatch identity, and canonical center phase carrier close exactly, but no independent reach estimate is obtained.

### Yellow

The central pair construction closes but one of the finite mirror/conjugation transport bridges requires an explicit local analytic hypothesis not currently supplied by the repository.

### Red

Any implementation that assumes paired positivity, imports a zero-side/RH-strength sign provider, treats the top PHZ polynomial as an infinite convergent Euler expansion, or silently changes contour orientation.

---

## 11. Named frontier

If no new source lower bound emerges, keep exactly one narrowed frontier, for example:

```lean
inductive PascalCenteredXiPrimeSideFiniteMirrorPairedHalfIntervalReachGap : Prop
  | no_independent_mirror_paired_half_interval_reach_estimate
```

Do not reintroduce the already discharged CS33 rate-continuity gap.

---

## 12. Validation

Run at least:

```text
lake env lean <new-CS35-file>
lake build DkMath.RH
git diff --check
```

No new `sorry`, `axiom`, or `native_decide`.

---

## 13. Research interpretation

CS34 leaves the problem in a genuinely finite form.  CS35 should exploit the fact that the top contour is centered around `1/2`.

The crucial paired combination is not an arbitrary symmetrization.  It is forced by the exact parity of the two weight channels:

```text
Re weight : mirror-even,
Im weight : mirror-odd,
phase rate : enters as a mirror sum,
amplitude rate : enters as a mirror difference.
```

The complex combination

```text
q_X(u) - conj(q_X(1-u))
```

contains exactly those two real quantities at once.  Its residual carrier

```text
F_X(u) * conj(F_X(1-u))
```

is nonzero on the safe interval and becomes positive real at the center `u=1/2`.

Thus the remaining reach problem can potentially be recast from a two-sided top-edge displacement into a one-sided transport away from a canonical positive center.  That is the structural goal of CS35; any sign statement remains a later theorem.