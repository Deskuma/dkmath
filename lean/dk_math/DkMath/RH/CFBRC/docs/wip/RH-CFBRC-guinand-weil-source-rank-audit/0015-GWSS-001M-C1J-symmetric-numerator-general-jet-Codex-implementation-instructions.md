# GWSS-001M-C1J symmetric numerator general jet — Codex implementation instructions

Date: 2026-08-21

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-guinand-weil-source-rank-audit-260820-v0`

## 0. Mission

Continue the GWSS source-rank route after `0014`.

Implement and audit only:

```text
GWSS-001M-C1J-A  public symmetric-exponential numerator surface
GWSS-001M-C1J-B  arbitrary-order even numerator jet / remainder theorem
GWSS-001M-C1J-C  connect arbitrary jets to the existing general coefficient matrix
GWSS-001M-C1J-D  prove linear independence of the finite symmetric-numerator family if the bridge remains compact
```

Do **not** start:

```text
GWSS-001M-C1E  finite evaluation-point existence
GWSS-001M-C2   actual Xi-window full-rank transfer
GWSS-002       off-critical witness construction
GWSS-003       arithmetic control
GWSS-004       classical Guinand-Weil infrastructure
```

The immediate purpose is to close the load-bearing gap between the actual zero-independent Mellin parameter family and the algebraic Vandermonde coefficient theorem already proved in:

```text
PascalCenteredXiMellinGeneralFiniteRankAudit.lean
```

The current trusted frontier is:

```text
GWSS-001M-C0
  FINITE-TAU-LOW-RANK-SEPARATION-FOUND

GWSS-001M-C1 algebraic coefficient rank
  GENERAL-FINITE-ORBIT-JET-COEFFICIENT-RANK-FOUND

current missing bridge
  GENERAL-MELLIN-SYMMETRIC-NUMERATOR-JET-GAP
```

Do not classify the finite-evaluation API as the load-bearing gap until this numerator-jet bridge is closed.

## 1. Mandatory orientation before editing

Before any edit, report:

```text
current branch
current HEAD
working-tree status
Lean toolchain
0013 and 0014 read
relevant Mellin jet modules read
global objective
current GWSS stage
load-bearing provider boundary
next unresolved Gap
```

Global objective:

```text
zero configuration
  -> independent source
  -> off-critical detector
  -> arithmetic control
  -> centered-coordinate uniqueness
  -> RiemannHypothesis
```

Current stage:

```text
GWSS-001M-C1J
```

Load-bearing boundary:

```text
NO RH assumption
NO classical Weil positivity
NO Li criterion
NO fixed-Xi defect vanishing provider
NO T -> infinity horizontal-decay provider
NO limit exchange
NO prime-side sign
NO carrier-dependent selector counted as an independent source
NO claim of finite evaluation rank before it is proved
```

## 2. Important correction to 0014 classification

`0014` correctly proves the general coefficient determinant theorem, but it also states that the arbitrary-order Mellin jet remains unproved.

Therefore the immediate frontier is not yet the finite-evaluation bridge.

Record the hierarchy explicitly:

```text
GENERAL-FINITE-ORBIT-JET-COEFFICIENT-RANK-FOUND
GENERAL-MELLIN-SYMMETRIC-NUMERATOR-JET-GAP
FINITE-EVALUATION-BRIDGE-NOT-YET-LOAD-BEARING
```

Do not delete or rewrite `0014`; treat this assignment as the correction/continuation.

## 3. Pinned analytic infrastructure to reuse

The pinned toolchain is Lean 4.32.2 and the repository manifest pins Mathlib rev:

```text
905b95818eb32af7874a58b427f50c1711a5e96c
```

Relevant Mathlib infrastructure already exists:

```text
NormedSpace.expSeries
NormedSpace.expSeries_apply_eq
NormedSpace.exp_eq_ofScalarsSum
Complex.exp_eq_exp_ℂ
```

Also inspect the existing DkMath module:

```text
PascalCenteredXiMellinFiniteJetRankAudit.lean
```

It already contains arbitrary-`n` Taylor-remainder machinery internally:

```text
expTaylorRemainder_isLittleO (n : ℕ)
expTaylorRemainder_scaled_tendsto_zero (n : ℕ) ...
```

Those helpers are currently private.  Reuse their proof pattern or promote/refactor a minimal reusable version if needed.

Do not build a new formal-power-series library.

## 4. C1J-A — symmetric numerator surface

Introduce, or expose through a named theorem, the symmetric exponential numerator

```text
G_tau(z) = exp(tau*z) - 2 + exp(-tau*z)
```

with `tau : ℝ`, `z : ℂ`.

A suitable definition is schematically:

```lean
noncomputable def mellinSymmetricNumerator (τ : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((τ : ℂ) * z) - 2 +
    Complex.exp (-(τ : ℂ) * z)
```

Naming may follow existing DkMath conventions.

Required basic facts:

```text
G_0(z) = 0
G_tau(0) = 0
G_tau(-z) = G_tau(z)
```

Also prove the exact relation to the existing bare kernel for nonzero `τ`:

```text
G_tau(z) = tau^2 * complexExpSecondDifferenceKernel tau z
```

or the equivalent division identity.

This theorem must preserve the patched `τ = 0` distinction; do not state it at `τ = 0` if the proof uses division.

## 5. C1J-B — arbitrary even numerator jet

The mathematical expansion to formalize is:

```text
G_tau(z)
  = sum_{r >= 0}
      [2 * z^(2*r+2) / (2*r+2)!] * tau^(2*r+2)
```

Do not merely document this as a heuristic.

The preferred load-bearing theorem is a finite-order remainder statement valid for arbitrary `m : ℕ`.

One acceptable theorem shape is:

```text
Tendsto
  (fun tau : ℝ =>
    (G_tau(z)
      - sum_{r < m}
          (2 * z^(2*r+2) / (2*r+2)!) * tau^(2*r+2))
      / tau^(2*m+2))
  (nhdsWithin 0 ({0}ᶜ))
  (nhds (2 * z^(2*m+2) / (2*m+2)!))
```

Equivalent `IsLittleO`, `IsBigOWith`, or remainder formulations are acceptable if they directly support C1J-C.

Requirements:

- arbitrary `m`, not only `0`, `1`, `2`;
- exact factorial coefficient;
- real parameter `tau` and complex value;
- punctured neighborhood where division by `tau` occurs;
- derive from the existing exponential Taylor remainder or pinned exponential-series API;
- explicitly cancel odd powers between `exp(tau*z)` and `exp(-tau*z)`;
- no unproved interchange of infinite sums and limits;
- no appeal to the already-proved low-order formulas as an induction substitute for arbitrary order.

### Preferred finite-sum strategy

A practical route is:

1. expand `exp(x)` and `exp(-x)` through order `2*m+2` using the existing finite Taylor remainder;
2. add the two expansions;
3. prove cancellation of odd terms by finite-sum algebra/parity;
4. isolate the `2*m+2` term;
5. transport the two remainders through `x = tau*z`;
6. divide by `tau^(2*m+2)` only on `nhdsWithin 0 ({0}ᶜ)`.

If parity manipulation is the only obstacle, introduce a small reusable finite-sum lemma.  Do not create a broad parity library.

### Alternative exact-series strategy

If `NormedSpace.expSeries` gives a materially shorter proof, it is acceptable to prove an exact `HasFPowerSeriesAt` or coefficient theorem for the symmetric numerator and derive the finite jet from it.

Do not pursue this route if it creates more infrastructure than the finite Taylor-remainder route.

## 6. Coefficient definition discipline

If useful, introduce the public coefficient:

```lean
def mellinSymmetricNumeratorJetCoeff (r : ℕ) (z : ℂ) : ℂ :=
  2 * z ^ (2 * r + 2) / (Nat.factorial (2 * r + 2) : ℂ)
```

For `q = z^2`, prove the exact algebraic relation:

```text
coeff(r,z)
  = 2 * q^(r+1) / (2*r+2)!
```

This must match exactly the entries already used by:

```lean
mellinJetCoefficientMatrix
```

in `PascalCenteredXiMellinGeneralFiniteRankAudit.lean`.

Do not create a second incompatible coefficient normalization.

## 7. C1J-C — bridge to the existing coefficient matrix

The goal is to make the 0014 Vandermonde theorem load-bearing for the actual symmetric numerator family.

For `z : Fin n -> ℂ`, define or identify the family:

```text
f_j(tau) = G_tau(z_j)
```

and `q j = (z j)^2`.

Prove enough to show that the `r`-th extracted numerator jet of column `j` is exactly:

```text
mellinJetCoefficientMatrix q r j
```

for every `r : Fin n`.

A direct named theorem connecting the two APIs is preferred.

Do not merely restate the coefficient formula in a docstring.

## 8. C1J-D — finite family linear independence

Proceed if C1J-B/C are complete and the proof remains focused.

Target:

```lean
LinearIndependent ℂ
  (fun j : Fin n =>
    (fun τ : ℝ => mellinSymmetricNumerator τ (z j)))
```

under:

```text
∀ j, (z j)^2 ≠ 0
Pairwise (fun i j => (z i)^2 ≠ (z j)^2)
```

An equivalent theorem saying that any coefficient vector whose linear combination is the zero function must itself be zero is acceptable.

### Preferred proof logic

Let coefficients be `c : Fin n -> ℂ` and assume:

```text
for every tau,
  sum_j c_j * G_tau(z_j) = 0
```

Use induction on jet order `r`:

- `r = 0`: divide the identity by `tau^2`, take the punctured limit, obtain the first coefficient-row equation;
- at general `r`: subtract the already-vanishing lower jet-row contributions, divide by `tau^(2*r+2)`, take the limit, obtain row `r`;
- collect all `n` row equations;
- use `mellinJetCoefficientMatrix_det_ne_zero` to conclude `c = 0`.

You may express the final step with matrix invertibility, determinant nonzero, or an equivalent linear-independent-columns theorem already in Mathlib.

Do not build an abstract interpolation library here.

### Stop condition for C1J-D

If the arbitrary jet theorem is complete but converting the `n` row equations to function linear independence requires unexpectedly large generic matrix/span infrastructure, stop with:

```text
GENERAL-MELLIN-NUMERATOR-JET-FOUND
GENERAL-MELLIN-NUMERATOR-LINEAR-INDEPENDENCE-API-GAP
```

That is an acceptable result.

Do not continue into finite evaluation in the same assignment.

## 9. Why numerator, not patched kernel

This assignment deliberately uses the numerator first.

At `tau = 0`:

```text
G_0(z) = 0
```

whereas the patched kernel has the quadratic value.

Later, if a finite evaluation matrix of numerator functions is invertible, no selected evaluation point can be zero because a `tau = 0` row would be identically zero.

Thus a later finite-evaluation theorem will automatically produce nonzero dilation parameters.

For nonzero `tau`, row scaling by `tau^(-2)` transfers numerator rank to bare-kernel rank.

This is only motivation for the next stage.  Do not implement the finite-evaluation theorem now.

## 10. Forbidden shortcuts

Do not:

- infer arbitrary-order jets from the cases `z^2`, `z^4/12`, `z^6/360`;
- state a formal infinite Taylor identity without convergence/remainder support;
- identify the symmetric numerator with the patched kernel at `tau = 0`;
- count the carrier-dependent polynomial selector as the source family;
- use actual Xi zeros to define `tau` or the Mellin family;
- assume RH, Weil positivity, Li, prime-side sign, horizontal decay, or limit exchange;
- start C2 or GWSS-002;
- create a large generic interpolation or analytic-functions library.

## 11. Implementation scope

Prefer one focused new module, for example:

```text
DkMath/RH/CFBRC/PascalCenteredXiMellinGeneralNumeratorJetAudit.lean
```

It may import:

```text
PascalCenteredXiMellinGeneralFiniteRankAudit
```

plus the minimal pinned Mathlib analytic files needed.

Small edits to the earlier finite-jet module are allowed only if they cleanly expose an already-written generic remainder helper and reduce duplication.

Do not change public aggregation imports unless necessary.

## 12. Required report

Create:

```text
docs/wip/RH-CFBRC-guinand-weil-source-rank-audit/
0016-GWSS-001M-C1J-symmetric-numerator-general-jet-report.md
```

Report:

```text
Global objective
Current GWSS stage
Load-bearing boundary
Next unresolved Gap

C1J-A numerator surface status
C1J-B arbitrary jet status
C1J-C coefficient-matrix bridge status
C1J-D linear-independence status

Primary classification
GWSS-002 authorization status
Verification
Axiom footprint
```

## 13. Classification

End with exactly one primary classification from:

```text
GENERAL-MELLIN-NUMERATOR-FUNCTION-RANK-FOUND
GENERAL-MELLIN-NUMERATOR-JET-FOUND-LINEAR-INDEPENDENCE-API-GAP
GENERAL-MELLIN-SYMMETRIC-NUMERATOR-JET-API-GAP
GENERAL-MELLIN-SYMMETRIC-NUMERATOR-JET-OBSTRUCTION
```

Interpretation:

### `GENERAL-MELLIN-NUMERATOR-FUNCTION-RANK-FOUND`

All arbitrary finite jet rows are connected to the actual symmetric numerator family and the finite family is proved linearly independent for nonzero pairwise-distinct squared coordinates.

Next Gap:

```text
GENERAL-FINITE-MELLIN-EVALUATION-BRIDGE-GAP
```

### `GENERAL-MELLIN-NUMERATOR-JET-FOUND-LINEAR-INDEPENDENCE-API-GAP`

The arbitrary jet theorem and coefficient bridge are proved, but the final finite-family function linear-independence wrapper is not compactly available.

Next Gap:

```text
GENERAL-MELLIN-NUMERATOR-LINEAR-INDEPENDENCE-API-GAP
```

### `GENERAL-MELLIN-SYMMETRIC-NUMERATOR-JET-API-GAP`

The pinned analytic surface still lacks a precise helper needed to prove the arbitrary-order numerator jet.  Name the exact missing theorem/API.

### `GENERAL-MELLIN-SYMMETRIC-NUMERATOR-JET-OBSTRUCTION`

Use only if a genuine mathematical obstruction is proved.  Do not use this label for proof engineering difficulty.

## 14. Verification

At minimum run:

```text
lake build DkMath.RH.CFBRC.PascalCenteredXiMellinGeneralNumeratorJetAudit
git diff --check
```

If the actual module name differs, build that exact module.

Check:

```text
no sorry
no admit
no new axiom declaration
#print axioms on every load-bearing public theorem
```

A repository-wide build is not required unless a public aggregation import changes.

## 15. Stop rule

After the report is written, stop.

Do not start:

```text
finite evaluation point construction
C2 actual Xi squared-orbit full-rank transfer
GWSS-002
GWSS-003
```

The next assignment will be chosen only after the general numerator jet/function-rank result is reviewed.
