# ZDI-009 — positive-density normalized constant obstruction audit instructions

Branch: `wip/RH-CFBRC-zeta-dkreal-zero-interval-260819-v0`

Parent roadmap: `0000-RH-CFBRC-zeta-dkreal-zero-interval-roadmap.md`

Depends on:

- `0014-ZDI-007-positive-density-residual-margin-constant-feasibility-audit-report.md`
- `0016-ZDI-008-positive-density-bounded-span-projection-feasibility-audit-report.md`

## Goal

ZDI-008 left two apparent gates:

1. transport the pair-local positive-density margin to one fixed block-start scalar functional;
2. compare the resulting normalized margin constant with the existing normalized residual-majorant constant.

Before implementing Gate 1, ZDI-009 must audit whether **Gate 2 is already impossible even with the full certified margin and no projection-loss factor at all**.

The ZDI-008 report gives exact normalized constants. Their quotient appears to simplify enough to yield a uniform obstruction for every positive density on both off-critical sides. If this is Lean-provable from the existing formulas, the current residual-majorant / certified-margin route is `O-CONSTANT`, and no positive-density fixed-block projection transport should be implemented merely to serve this route.

This is therefore a **constant obstruction audit first**. Only if the proposed obstruction fails because the report's constants cannot be connected to the exact Lean source theorems should the fixed-block transport gate be reopened.

## Global RH boundary

The final target remains Mathlib `RiemannHypothesis`.

The unresolved load-bearing content is still the source-recovery / zero-forcing direction from a standard nontrivial Riemann-zeta zero to a quantitative exclusion of nonzero `centeredSigma s.re`.

Do not add:

- `RiemannHypothesis` as an assumption;
- an RH-equivalent source-recovery/provider predicate;
- global no-cancellation or residual-domination fields;
- `centeredSigma` coercivity whose conclusion already forces the critical line;
- moving-line `research_goal` declarations;
- any dependency carrying `sorryAx`.

The desired ZDI-009 result is only an obstruction to the **current bounds**, not an impossibility theorem for the exact oscillatory Eta tail.

## Fixed ZDI-008 constants

Write

```text
σ := s.re
t := |s.im|
ρ := positive density
m := criticalMirror s
```

For a standard nontrivial zero, existing audited facts give `t > 0` and `0 < σ < 1`. Also

```lean
criticalMirror_im s : (criticalMirror s).im = s.im
```

so the ordinary complex norm estimate should yield

```text
‖criticalMirror s‖ ≥ t
‖s‖ ≥ t.
```

Do not define these inequalities as new assumptions; derive them from existing complex norm facts.

### Right side

For

```text
1/2 < σ < 1
```

ZDI-008 records the normalized residual upper-limit constant

```text
R_right(σ,t,ρ)
  := t * ‖m‖ / (1 - σ)
       * (2 / (1 + 2ρ))^(1 - σ)
```

and the normalized certified margin lower-bound limit

```text
M_right(σ,t,ρ)
  := (t^2 / 4) * ρ * (1 + 2ρ)^(σ - 2).
```

### Left side

For

```text
0 < σ < 1/2
```

ZDI-008 records

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

These constants must be traced back to the exact existing residual-majorant and normalized block-margin limit theorems before a new obstruction theorem is counted as proved.

## Main algebraic observation to certify

For positive `t` and `ρ`, the right quotient formally simplifies to

```text
R_right / M_right
  = 4 * (‖m‖ / t)
      * (1 / (1 - σ))
      * 2^(1 - σ)
      * ((1 + 2ρ) / ρ).
```

The left quotient formally simplifies to

```text
R_left / M_left
  = 4 * (‖s‖ / t)
      * (1 / σ)
      * 2^σ
      * ((1 + 2ρ) / ρ).
```

Do not trust these paper simplifications blindly. Re-derive them in Lean or prove the needed inequality directly from the source formulas.

If the formulas are correct, then on the right:

```text
‖m‖ / t ≥ 1,
1 / (1 - σ) > 2,
2^(1 - σ) > 1,
(1 + 2ρ) / ρ > 2,
```

and on the left:

```text
‖s‖ / t ≥ 1,
1 / σ > 2,
2^σ > 1,
(1 + 2ρ) / ρ > 2.
```

Therefore the expected strong conclusion is

```text
R_right > 16 * M_right
```

and

```text
R_left > 16 * M_left
```

for every admissible positive density, or at minimum the weaker load-bearing conclusion

```text
M_right < R_right
M_left < R_left.
```

The factor `16` is an audit target, not a value to force by definition. If exact Lean normalization changes the numerical factor, prove the strongest naturally supported inequality and report the discrepancy.

## Why this precedes fixed-block projection

Any legitimate fixed block-start projection transport can only use some certified fraction/loss of the available raw margin lower bound. If a transport theorem has a factor `λ` satisfying

```text
0 < λ ≤ 1,
```

then

```text
λ * M_side ≤ M_side.
```

Thus, if the current residual upper constant already satisfies

```text
M_side < R_side
```

for every admissible `ρ`, no angular transport theorem with a loss factor at most one can make the current sufficient comparison

```text
R_side < λ * M_side
```

true.

This closes the current **majorant-versus-certified-margin proof route** without saying that the exact residual itself is large. The exact oscillatory tail may be much smaller than the current majorant; ZDI-009 must preserve that distinction explicitly.

## Required implementation order

1. **Source trace.** Identify the exact existing Lean theorems producing `R_right`, `R_left`, `M_right`, and `M_left`. Record file/theorem names.
2. **Norm bridge.** Reuse or prove the tiny generic consequences `|s.im| ≤ ‖s‖` and `|s.im| ≤ ‖criticalMirror s‖`, using `criticalMirror_im` for the latter.
3. **Pure scalar obstruction.** Prove the right and left constant inequalities for arbitrary real parameters satisfying the audited strip and positivity hypotheses. Prefer a reusable analysis lemma only if it is genuinely generic and simpler than the specialized statement.
4. **Source specialization.** Connect the scalar obstruction back to the exact normalized residual and margin constants used by the positive-density Eta route.
5. **Stop if O-CONSTANT is obtained.** Do not implement the positive-density fixed block-start transport theorem for this route after the constants are already certified incompatible.
6. **Only if the obstruction fails**, explain exactly which reported formula/source connection fails, and then reconsider the fixed-block projection transport as the remaining Gate A.
7. Run `#print axioms` on every new load-bearing theorem and reject `sorryAx`.

## Important proof discipline

### Do not confuse an upper bound with the exact residual

A proof that

```text
current residual majorant constant > certified margin constant
```

means only that the present pair of estimates cannot certify domination. It does **not** prove

```text
exact residual > exact margin
```

and does not prove that no sharper oscillatory estimate can succeed.

The report must use wording such as:

> `O-CONSTANT` for the current residual-majorant / certified-margin route.

It must not say:

> exact Eta-tail domination is impossible.

### Do not repackage the failed inequality

Do not introduce a provider such as `ResidualTooLarge`, `NoPositiveDensity`, or similar unless it is merely a transparent abbreviation for a theorem already proved from the explicit formulas. Prefer direct theorem statements.

### No unnecessary zeta dependency

The scalar inequality should ideally be proved with hypotheses only on `σ`, `t`, `ρ`, and norm-like parameters. Specialize to `s` afterward. This makes clear which obstruction is elementary and which facts come from the zeta-zero source.

## Classification

Use the strongest justified label:

- `O-CONSTANT`: the current residual-majorant constant is strictly larger than the full certified margin constant for every admissible positive density on the audited side.
- `O-JOINT`: constant obstruction is not individually universal, but no density can satisfy both angle and constant requirements.
- `C1-CONSTANT`: the comparison reduces to one explicit scalar inequality and neither feasibility nor impossibility is proved.
- `C1-PROJECTION`: constant gate survives, but fixed block-start transport remains unproved.
- `C2`: a jointly realizable constant + fixed-projection region is independently proved.
- `E`: an apparent success assumes/repackages RH-closing no-cancellation or coercivity.
- `F`: impossible antecedent, `sorryAx`, or untrusted dependency.

If both right and left inequalities above are proved from the current constants, classify this positive-density majorant route as **O-CONSTANT** and close it.

## Consequence for the research tree

If `O-CONSTANT` is certified, update the dependency picture conceptually to

```text
positive-density bounded span
  -> fixed block-start transport [not needed for current bounds]

current residual majorant
  + current certified positive-density margin
  -> normalized constant mismatch
  -> O-CONSTANT
```

The next RH-relevant question would then be **whether the residual estimate itself can be sharpened using exact oscillatory cancellation from the zero-derived Eta identity**, not whether one can further tune positive density or angle.

Do not start that sharper residual project inside ZDI-009. Only identify the smallest exact theorem/estimate that would have to improve.

## Validation

Run focused builds for every new/modified Lean module and:

```bash
git diff --check
```

Include `#print axioms` output for all new load-bearing theorems. The ordinary Mathlib kernel dependencies such as `[propext, Classical.choice, Quot.sound]` are acceptable; any `sorryAx` fails the audit.

## Suggested report

Write:

`0018-ZDI-009-positive-density-normalized-constant-obstruction-audit-report.md`

End with one compact statement of exactly what has been ruled out:

```text
current residual majorant + current certified margin
  -> [compatible / incompatible] for positive density
```

and separately state whether the exact oscillatory residual remains open.