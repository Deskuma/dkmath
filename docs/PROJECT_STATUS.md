# DkMath Project Status

**Updated:** 2026-09-16

**Documentation baseline:** `__snapshot-dk_math-lean-code-260916-1826.tar.gz`

**SHA-256:** `1f0b8ee3dd0a9a5f829447eba7656060c1d2e19f085153a19e5040fa63f0dde7`

This document is the authoritative dated status summary for the public DkMath repository documentation. Dated files under `lean/dk_math/docs/dev`, `docs/feature`, and `docs/refact` remain research records for their own checkpoints; they are not automatically current project summaries.

## 1. Executive status

The clearest completed DkMath results in the current snapshot are:

| Area | Status | Public endpoint / entry point |
|---|---|---|
| FLT exponent 3 over positive naturals | **COMPLETE** | `DkMath.FLT.Three.fermatThree_no_positive_solution` |
| FLT exponent 5 over positive naturals | **COMPLETE** | `DkMath.FLT.Five.fermatFive_no_positive_solution` |
| Infinitude of primes via Cosmic Formula boundary | **COMPLETE proof route** | `DkMath.CosmicFormula.euclid_from_cosmic_boundary` / sample `InfinitudeOfPrimes` |
| `DkMath.Lib.*` extraction | **ACTIVE / reusable layer established** | `import DkMath.Lib` |
| General odd-prime FLT architecture | **INCOMPLETE research** | `DkMath.FLT.Prime.*`, through conditional ideal/sector endpoints |

The documentation should therefore present DkMath in this order:

```text
completed formal results
  -> reusable neutral library extracted from them
  -> active research built on that library
  -> historical routes and dated work logs
```

This replaces the older documentation model in which the conditional `DkMath.FLT.Main` / `NoSqOnS0` route was treated as the current FLT3 public story.

## 2. FLT3 — completed unconditional positive-natural endpoint

### 2.1 Current public surface

The canonical independent import is:

```lean
import DkMath.FLT.Three
```

The primitive endpoint is:

```lean
theorem DkMath.FLT.Three.FLT_d3_unconditional
    {a b c : ℕ}
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (hab : Nat.Coprime a b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3
```

The unrestricted positive-natural endpoint is:

```lean
theorem DkMath.FLT.Three.fermatThree_no_positive_solution
    (a b c : ℕ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c) :
    a ^ 3 + b ^ 3 ≠ c ^ 3
```

The latter normalizes a hypothetical solution by `Nat.gcd a b`, constructs a primitive cubic packet, and closes it with the independent cubic descent tower.

### 2.2 Proof architecture

```text
positive cubic solution
  -> gcd normalization
  -> PrimitiveCubicPack
  -> signed three-adic routing
  -> Eisenstein ramifier stripping
  -> coprime conjugate factors
  -> Euclidean-domain cube extraction
  -> unit-sector exclusion
  -> exact Eisenstein cube
  -> smaller primitive cubic solution
  -> strong induction on a natural product measure
  -> contradiction
```

The current tower is independent of the legacy conditional FLT3 surface in `DkMath.FLT.Main`. In particular, the final endpoint does not use `FLT_d3_by_padicValNat`, `hS0_not_sq`, or `NoSqOnS0` as proof steps.

### 2.3 Audit and exhibition artifact

The final implementation report records successful focused builds of `DkMath.FLT.Three.PositiveCubicNormalization` and `DkMath.FLT.Three`. Its endpoint axiom audit is:

```text
{propext, Classical.choice, Quot.sound}
```

with no `sorryAx` or project-specific axiom in the audited endpoint.

References:

- `lean/dk_math/DkMath/FLT/Three.lean`
- `lean/dk_math/docs/dev/FLT3-Unconditional-260904-v0/report-014.md`
- standalone exhibition repository: <https://github.com/Deskuma/flt3_dk_math_lean4>

## 3. FLT5 — completed unconditional positive-natural endpoint

### 3.1 Current public surface

Canonical import:

```lean
import DkMath.FLT.Five
```

Public endpoints:

```lean
DkMath.FLT.Five.flt5Target
DkMath.FLT.Five.fermatFive_no_positive_solution
```

The scope is exactly exponent five over positive natural numbers.

### 3.2 Proof architecture

The public module documents the route as:

```text
positive solution normalization
  -> signed gap orientation
  -> GN5 / five-adic factor splitting
  -> golden-order factorization
  -> unit classes modulo fifth powers
  -> exclusion of four nonzero sectors
  -> zero-sector certified strict descent
  -> contradiction
```

### 3.3 Audit and exhibition artifact

`DkMathTest/FLT/Five/CheckAxioms.lean` audits the route from GN5 through the public closure. The completed trust report records the final endpoint axiom set as:

```text
{propext, Classical.choice, Quot.sound}
```

and records absence of `sorryAx`, DkMath-defined axioms, active `native_decide`, `admit`, and `sorry` in the checked public/standalone endpoint certificate.

References:

- `lean/dk_math/DkMath/FLT/Five.lean`
- `lean/dk_math/DkMath/FLT/Five/Main.lean`
- `lean/dk_math/DkMathTest/FLT/Five/CheckAxioms.lean`
- standalone exhibition repository: <https://github.com/Deskuma/flt5_dk_math_lean4>

## 4. Cosmic Formula boundary proof of infinitely many primes

The stable sample route defines the boundary object by

$$
\operatorname{cosmicN}(P)=P(P+2),
$$

with

$$
\operatorname{cosmicN}(P)+1=(P+1)^2.
$$

For a finite set of primes, the proof uses the product $P$ and a prime divisor of the boundary term $P+1$ (or its square) to obtain a prime outside the finite set. The formal route yields:

```lean
DkMath.CosmicFormula.euclid_from_cosmic_boundary
```

and the sample challenge theorem:

```lean
InfinitudeOfPrimes
```

The repository records successful Lean Comparator Live verification against the known “Infinitely Many Primes” challenge.

References:

- `lean/dk_math/DkMath/Samples/Prime/A.lean`
- `lean/dk_math/DkMath/Samples/Prime/README.md`
- `lean/dk_math/DkMath/Samples/Prime/Lean4Web.md`

## 5. `DkMath.Lib.*` — current reusable layer

### 5.1 Role

`DkMath.Lib` is the development-side public entrance for the subset of promoted mathematical components currently exposed by the aggregator.

```lean
import DkMath.Lib
```

Some neutral modules under `DkMath.Lib.NumberTheory.*` are currently imported directly by their research consumers and are not yet re-exported by `DkMath.Lib.lean`; the namespace inventory below therefore distinguishes physical promoted modules from aggregator coverage.

The intended dependency direction is:

```text
research experiment
  -> identify reusable theorem/kernel
  -> remove owner-specific assumptions and naming
  -> promote to DkMath.Lib.*
  -> reuse from later research
```

### 5.2 Cosmic / GTail family

`DkMath.Lib.Cosmic.GTail` is now the neutral kernel behind the standard GN layer. For general depth $r$:

$$
\begin{aligned}
(x+u)^d &\;=\; \sum_{j<r}\binom dj x^j u^{d-j}\\
&\qquad +x^r\operatorname{GTail}(d,r,x,u).
\end{aligned}
$$

The standard GN layer is the $r=1$ specialization:

$$
GN_d(x,u)=\operatorname{GTail}(d,1,x,u).
$$

Promoted modules in the snapshot:

- `GTail.lean`
- `GTailBoundary.lean`
- `GTailCongruence.lean`
- `GTailCyclotomic.lean`
- `GTailNat.lean`
- `GTailPadic.lean`
- `GTailPascal.lean`

These expose, among other things, tail decomposition, recursion, boundary gcd formulas, congruence collapse, prime divisibility, cyclotomic shell bridges, natural-number divisibility, and exact p-adic statements.

### 5.3 Number-theory promoted modules

Current modules include:

- `PadicValNat.lean`
- `PowerFactor.lean`
- `IdealPowerFactor.lean`
- `PrincipalIdealPower.lean`
- `UnitPowerSector.lean`
- `TraceOneLatticeLanding.lean`
- `TraceOnePowerLanding.lean`
- `EisensteinCoordinates.lean`
- `EisensteinLatticeLanding.lean`
- `SquarefreePowerFactor.lean`

These are intentionally framed as neutral APIs rather than FLT-, ABC-, or GN5-specific results.

The GN5 hackathon line is therefore historically important not only for FLT5 itself, but because repeated reuse pressure exposed the abstractions now being promoted into `DkMath.Lib.*`.

## 6. General odd-prime FLT — current research boundary

The latest bounded generalization record is:

`lean/dk_math/docs/refact/FLT-Prime-Generalization-260911-v0/summary-026.md`.

Its proved architecture is:

```text
PrimeAdicFactorPacket
  -> GTail exact p-adic split
  -> arbitrary-prime QR/QNR TraceOne coordinates
  -> primitive coordinates
  -> prime-discriminant maximal order / Dedekind domain
  -> discriminant-axis strip
  -> conjugate-coprime residual ideals
  -> residual principal ideal = idealRoot^p
  -> [classGroupPTorsionFreeAt]
  -> unit * element^p
  -> unit-sector normalization
```

### 6.1 What is already closed

The current code contains production structures/theorems for:

- generic prime-adic power splitting (`DkMath.FLT.Prime.AdicPowerSplit`);
- primitive arbitrary-prime TraceOne coordinates;
- discriminant-axis stripping and coordinate coprimality;
- conjugate-coprime residual ideals;
- extraction of an ideal root with

$$
(\mathrm{residual})=I^p;
$$

- conditional principalization under `classGroupPTorsionFreeAt`;
- unit-sector normalization;
- the imaginary branch $p\equiv3\pmod4$, $p\ge7$, where the unit-sector obstruction collapses and the residual becomes an exact $p$-th power, still conditional on the class-group hypothesis;
- the real branch $p\equiv1\pmod4$, where a `Fin p` sector remains.

### 6.2 Explicit open frontier

The closeout itself identifies two principal unresolved mathematical categories:

1. **class-group $p$-torsion / principalization**;
2. **nonzero unit-sector elimination in the real branch**.

In addition, `p = 3` remains outside that generic sector facade because the production sector theorem uses `EisensteinInt` while the arbitrary-prime packet uses `TraceOneInt (-1)`. This is recorded as a carrier/API boundary, not as a proved identification.

Therefore the current generalization architecture must not be described as a proof of general FLT.

## 7. Legacy FLT routes and historical documentation

The repository intentionally retains older FLT3 and high-exponent routes because they document the development history and still contain useful lemmas.

Examples include:

- `DkMath.FLT.Main` and the `FLT_d3_by_padicValNat` family;
- `NoSqOnS0` / `PhaseLift` documentation;
- older `PrimeProvider` / Kummer provider routes;
- old lemma-chain diagrams and checkpoint reports.

These should be treated as **historical or alternate research routes**, not as the canonical current FLT3 public surface.

A dated historical document should generally not be rewritten to pretend it was authored with later results in mind. When needed, add a short historical-status notice pointing to the current public surface instead.

## 8. Other active research

The snapshot contains substantial current work under areas including ABC, Goldbach, CF2D prime-gauge projection, MultiGauge divisibility, gnomon transitions, Legendre, Primitive Conservation, RH/CFBRC, and related projects.

This status document deliberately does not promote those workspaces to “completed headline theorem” status merely because production Lean files or reports exist. Their own dated reports remain the source for checkpoint-specific claims.

The public project overview should only call a result completed when a stable public endpoint and its verification boundary are explicitly documented.

## 9. Documentation authority

To avoid the stale-document problem that motivated the 2026-09-16 refactor:

- `README.md` — concise public overview; completed results first.
- `docs/PROJECT_STATUS.md` — authoritative **dated current-state** technical summary.
- `lean/dk_math/README.md` — Lean implementation/build entry point.
- `lean/dk_math/DkMath/FLT/README.md` — current FLT public surfaces, generalization boundary, legacy map.
- `lean/dk_math/DkMath/Lib/README.md` — promoted reusable APIs.
- `lean/dk_math/docs/dev/*`, `docs/feature/*`, `docs/refact/*` — dated checkpoint/history records; not global current-state authorities unless explicitly stated.

When these disagree, the dated `PROJECT_STATUS.md` and the actual Lean source at the referenced revision take precedence over older narrative documents.

## 10. Snapshot provenance

This rewrite was grounded in the supplied snapshot:

```text
1f0b8ee3dd0a9a5f829447eba7656060c1d2e19f085153a19e5040fa63f0dde7  __snapshot-dk_math-lean-code-260916-1826.tar.gz
```

The snapshot contains the Lean source tree and associated Markdown research records used for this audit. The checksum was re-evaluated before the documentation rewrite and matched the supplied value.
