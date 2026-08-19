# ZDI-009 — positive-density fixed-block projection and constant-gate audit instructions

Branch: `wip/RH-CFBRC-zeta-dkreal-zero-interval-260819-v0`

Parent roadmap: `0000-RH-CFBRC-zeta-dkreal-zero-interval-roadmap.md`

Depends on:

- `0014-ZDI-007-positive-density-residual-margin-constant-feasibility-audit-report.md`
- `0016-ZDI-008-positive-density-bounded-span-projection-feasibility-audit-report.md`

## Goal

ZDI-008 fixed the current boundary precisely:

1. a sufficiently small positive density can make the limiting finite-block phase span smaller than any prescribed positive safe angle at a fixed nonreal point;
2. the repository has a genuine block-start functional and exact finite linearity across one block;
3. the currently proved positive-density lower bound is still expressed through pair-local rotated projections rather than one common block-start projection;
4. after normalization, the residual and margin have balanced powers, leaving an explicit constant comparison;
5. no jointly realizable C2 region has been proved.

ZDI-009 must test **only the two remaining gates**:

> Can the existing exact phase/rotation identities transport the local pair margin to one fixed block-start scalar functional over a positive-density finite block, and, if so, can the resulting explicit normalized margin constant beat the already proved residual-majorant constant in any independently realizable parameter region relevant to an off-critical standard zeta zero?

This is a narrow feasibility / obstruction audit. Do not create a generic no-cancellation provider and do not begin another long theorem chain.

## Global RH boundary

The final target remains Mathlib `RiemannHypothesis`.

The unresolved load-bearing mathematics is still the source-recovery / zero-forcing direction from a standard nontrivial Riemann-zeta zero to a quantitative exclusion of nonzero `centeredSigma s.re`.

A theorem which, for every `NontrivialRiemannZetaZero s`, independently excludes `s.re ≠ 1/2` would close RH. Such a theorem is acceptable only if its proof contains the genuine analytic argument. It must not be introduced as a structure field, provider, renamed hypothesis, or coercivity predicate.

Forbidden as independent inputs include any assumption equivalent in substance to:

- global no-cancellation;
- residual-tail domination;
- fixed positive energy for every off-critical zeta zero;
- `centeredSigma` coercivity whose conclusion already forces the critical line;
- `RiemannHypothesis` or an RH-equivalent bridge/provider;
- moving-line `research_goal` declarations or anything carrying `sorryAx`.

## Fixed facts from ZDI-007 and ZDI-008

Preserve these distinctions exactly.

### Positive density is incompatible with the old shrinking-span schedule

For a positive-density schedule `S`, the relative block length tends to `S.density > 0`. It cannot simultaneously satisfy the old `EtaPairGrowingBlockSchedule` contract that the same relative length tends to zero.

Therefore no theorem whose proof essentially requires `EtaPairGrowingBlockSchedule.relativeLength_tendsto_zero` may be instantiated with positive density.

### Bounded nonzero span is nevertheless feasible

The positive-density block span has exact limit

```text
|s.im| * log (1 + 2ρ).
```

ZDI-008 proves the elementary fact

```lean
exists_positive_density_with_bounded_phase_span
```

so for fixed `s.im ≠ 0` and fixed `δ > 0`, some `ρ > 0` satisfies

```text
|s.im| * log (1 + 2ρ) < δ.
```

This is only angle feasibility. It is not schedule construction, residual domination, or a block projection lower bound.

### Infinite fixed-frame freezing is unavailable

Existing variation theorems show that at a nonreal point the cumulative absolute pair-frame motion diverges logarithmically and the adjacent frame spans are not summable.

Hence ZDI-009 may use a **single fixed frame only inside each finite block**. Do not reinterpret bounded finite-block span as convergence to one global asymptotic frame over the entire tail.

## Gate A — fixed block-start projection transport

Audit the exact definitions and theorems around:

```lean
etaCriticalMirrorBlockStartDefectPairProjection
etaCriticalMirrorBlockStartDefectBlockProjection
```

and their finite linearity relation.

The key requirement is that `K` is fixed for every offset `j` in the block. A proof using a projection which changes with `j` does not solve the cancellation problem and must not be counted as Gate A.

### Required source audit before proving anything

Identify the exact existing theorem(s) which give:

1. the pair-local rotated projection lower bound or sign;
2. the exact relative phase between the pair-local frame at `K + j` and the block-start frame at `K`;
3. the subblock phase-span bound under the existing `SmallAngleAdmissible` condition or its immediate dependencies;
4. finite linearity of the block-start functional over the block sum.

Record theorem names and file paths in the report.

### Smallest desired theorem shape

On the right off-critical side, the target shape is the already identified narrow statement

```text
(1 / 2) * etaCriticalMirrorRightBlockMarginSum
    s K (S.blockLength K)
  < etaCriticalMirrorBlockStartDefectBlockProjection
      s K (S.blockLength K)
```

eventually in `K`, under independently realizable positive-density and explicit angle hypotheses.

The left side should use the corresponding sign convention / negated block-start projection already dictated by the existing definitions.

The literal factor `1/2` is **not sacred**. Use it only if it is actually derivable from the existing small-angle estimate. If exact geometry yields another explicit loss factor, state and prove that factor instead. Do not choose a convenient constant by definition.

### Proof discipline

The transport proof, if realizable, must come from exact rotation/projection identities and an explicit angular inequality. In particular:

- one block-start functional must be used for all offsets;
- the sign/lower-bound loss must be explicit;
- the angular antecedent must be proved realizable from existing positive-density facts, not installed as a target-encoding provider;
- no residual-tail hypothesis is allowed in Gate A;
- no standard-zeta-zero hypothesis is needed unless an already proved fact such as `s.im ≠ 0` is genuinely required for realizing the angle condition.

If the only way to obtain the common sign is to assume a statement already equivalent to global no-cancellation, classify Gate A as an RH-equivalent obstruction and stop.

## Gate B — exact normalized constant comparison

Only if Gate A succeeds with a proved explicit loss factor should ZDI-009 combine it with the existing residual majorant.

Do not hide the comparison inside an abstract predicate. Expose the scalar inequality.

For `σ = s.re`, `t = |s.im|`, `1/2 < σ < 1`, the current ZDI-008 report identifies the normalized right residual constant

```text
R_right(σ,t,ρ)
  := t * ‖criticalMirror s‖ / (1 - σ)
       * (2 / (1 + 2ρ))^(1 - σ)
```

and the normalized certified right margin constant

```text
M_right(σ,t,ρ)
  := (t^2 / 4) * ρ * (1 + 2ρ)^(σ - 2).
```

For `0 < σ < 1/2`, the corresponding left constants are

```text
R_left(σ,t,ρ)
  := t * ‖s‖ / σ
       * (2 / (1 + 2ρ))^σ
```

and

```text
M_left(σ,t,ρ)
  := (t^2 / 4) * ρ * (1 + 2ρ)^(-σ - 1).
```

If Gate A proves a loss factor `λ(s,ρ,δ)` with `0 < λ ≤ 1`, the actual gate is the explicit inequality

```text
R_side(σ,t,ρ) < λ(s,ρ,δ) * M_side(σ,t,ρ).
```

For a constant factor such as `1/2`, substitute it explicitly rather than creating a new provider predicate.

### Required parameter analysis

Audit jointly:

1. `0 < ρ`;
2. the positive-density angle / `SmallAngleAdmissible` restriction;
3. the fixed-block transport loss from Gate A;
4. the right or left residual-versus-margin scalar inequality;
5. the standard unconditional zero-side facts actually available, including the critical strip and `s.im ≠ 0` where relevant.

The question is not whether one can numerically tune `ρ` for a hand-picked complex number. The question is whether the current proved hypotheses imply a realizable region for an arbitrary hypothetical off-critical `NontrivialRiemannZetaZero s` on the relevant side.

Do not assume a global upper or lower bound on `|s.im|`, `‖s‖`, or `‖criticalMirror s‖` unless it is already proved from the exact standard-zero hypotheses being used.

## Important asymptotic sanity check

Preserve the ZDI-008 observation that as `ρ → 0+`:

- the angle span tends to zero;
- the certified margin constant tends to zero linearly in `ρ` to first order;
- the current residual constant remains positive for fixed off-critical `s`.

Therefore "take density sufficiently small" cannot by itself prove Gate B. Any successful joint region must balance a lower bound on density coming from the constant inequality against an upper bound on density coming from the angle condition.

This trade-off should be made explicit in the report.

## Preferred implementation order

1. **Source inventory only.** Locate the exact block-start functional, pair-local projection, rotation identity, and small-angle theorem.
2. **Gate A characterization.** State the minimal finite-block transport theorem with no residual hypothesis.
3. **Antecedent realizability.** Prove the angle assumptions can actually occur for a positive-density schedule or clearly identify the remaining schedule-realizability gap.
4. **Gate A proof or obstruction.** Stop immediately if it requires an RH-equivalent sign provider.
5. **Gate B scalar reduction.** If Gate A succeeds, reduce residual domination to the explicit scalar inequality with the actual transport loss.
6. **Joint feasibility audit.** Prove a realizable parameter region, prove impossibility for the current bounds, or isolate the exact unsolved scalar inequality.
7. **Axiom audit.** `#print axioms` all new load-bearing theorems and verify no `sorryAx`.

Do not add downstream RH consequences merely because Gate A or a scalar comparison theorem compiles. The purpose of ZDI-009 is to decide whether this route deserves one more step.

## Classification

Use the strongest justified label only.

- `C1-ANGLE`: bounded-span angle condition is realizable, but no fixed-block transport theorem.
- `O-PROJECTION`: exact geometry cannot give one common block-start sign/lower bound with the current hypotheses.
- `C1-PROJECTION`: fixed-block transport is proved unconditionally, but constant feasibility remains open.
- `O-CONSTANT`: after a proved transport theorem, the current residual/margin constants are incompatible for all admissible parameters in the audited regime.
- `O-JOINT`: angle and constant requirements are individually meaningful but no common realizable parameter region exists under the current bounds.
- `C1-CONSTANT`: transport is proved and the remaining gap is one explicit scalar inequality whose truth is not established.
- `C2`: a jointly realizable angle + fixed-projection + constant-domination region is proved from independent existing mathematics, with no RH-equivalent provider.
- `E`: the apparent bridge assumes or repackages RH-closing no-cancellation/coercivity content.
- `F`: impossible antecedent, `sorryAx`, or otherwise untrusted dependency.

Do not report `C2` merely because a fixed numerical `s` admits some `ρ`. `C2` requires the hypotheses appropriate to an arbitrary hypothetical off-critical standard nontrivial zeta zero.

## Stop conditions

Stop the moving-frame branch and report the obstruction if any of the following occurs:

- common block-start positivity needs a pair-dependent functional;
- the positive-density angle antecedent cannot be realized by an actual schedule of the required type;
- the only available sign theorem depends on `EtaPairGrowingBlockSchedule.relativeLength_tendsto_zero`;
- the constant inequality is formally incompatible with the angle region for the current bounds;
- a required bridge is RH-equivalent or carries `sorryAx`.

Conversely, if Gate A is genuinely mechanical and Gate B reduces to one nontrivial scalar inequality, do **not** proliferate lemmas. Record that single inequality as the next frontier.

## Validation

At minimum run the focused build for every new/modified Lean module and:

```bash
git diff --check
```

For each new load-bearing theorem include `#print axioms` output in the report. The acceptable baseline is the ordinary Mathlib kernel dependencies such as `[propext, Classical.choice, Quot.sound]`; any `sorryAx` fails the audit.

## Suggested report

Write:

`0018-ZDI-009-positive-density-fixed-block-projection-constant-gate-report.md`

The report should end with one concise dependency diagram showing exactly which of these arrows is now proved:

```text
positive-density bounded span
  -> one fixed block-start pair sign
  -> one fixed block-start finite-block lower bound
  -> normalized scalar margin > normalized residual
  -> residual domination / off-critical exclusion
```

The final two arrows must not be drawn as proved unless they actually are.