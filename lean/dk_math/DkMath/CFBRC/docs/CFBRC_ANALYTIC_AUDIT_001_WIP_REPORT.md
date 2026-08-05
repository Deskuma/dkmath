# CFBRC Analytic Continuation Audit 001 — ~~WIP~~ report

status: completed / 2026/08/05 22:08
cid: `6a731866-0700-83e8-9940-ad80f55a294d`

Build status
  User workspace:
    ./lean-build.sh && ./lean-test.sh
    Green

  GitHub Actions:
    Lean CI #868
    Green

  Initial generation environment:
    toolchain unavailable; static audit only

---

*The following is recorded as an implementation log.*

Date: 2026-08-05

## Snapshot checkpoint

```text
source snapshot:
  __snapshot-dk_math-lean-code-260805-2004.tar.gz

verified sha256:
  57d4f53dd831561ae8cd5abbae7a517e359f169e853a5d8d13e0b33d99532d21

Lean toolchain:
  leanprover/lean4:v4.32.2

Mathlib revision:
  v4.32.2
```

Comparison with the `260805-0819` snapshot found no material change in the
non-RH CFBRC implementation surface. Outside `DkMath/RH` and
`DkMathTest/RH`, the only unrelated additions were Pow design documents and
root import changes caused by newer RH modules.

## Implemented packet

```text
DkMath.CFBRC.Regularization.ForwardDifference
DkMath.CFBRC.Regularization.NegativeInteger
DkMath.CFBRC.Regularization.AbelLinear
DkMath.CFBRC.Regularization.DualAudit
DkMath.CFBRC.Regularization.RiemannZetaOracleAudit
```

Regression tests were added below:

```text
DkMathTest.CFBRC.Regularization.NegativeInteger
DkMathTest.CFBRC.Regularization.AbelLinear
DkMathTest.CFBRC.Regularization.RiemannZetaOracleAudit
```

## Dependency boundary

The native finite-difference and Abel modules do not import any `DkMath.RH`
module. The finite-difference Core does not use standard zeta, Hurwitz zeta,
or analytic continuation.

The standard comparison is isolated in:

```text
DkMath.CFBRC.Regularization.RiemannZetaOracleAudit
```

## Native computed values

For the polynomial moments `x^m`, the forward differences at `x = 1` are:

```text
m = 0: [1]
m = 1: [1, 1]
m = 2: [1, 3, 2]
m = 3: [1, 7, 12, 6]
```

The resulting finite Euler values are:

```text
etaFD(0) =  1/2
etaFD(1) =  1/4
etaFD(2) =  0
etaFD(3) = -1/8
```

After parity normalization:

```text
zetaFD(0) = -1/2
zetaFD(1) = -1/12
zetaFD(2) =  0
zetaFD(3) =  1/120
```

## Abel route

The implemented ordinary convergent series is:

$$
\sum_{n=0}^{\infty}-n(-r)^n=\frac{r}{(1+r)^2},\qquad |r|<1.
$$

The closed form tends to `1/4` as `r` approaches `1` from below. The dual
audit identifies this boundary value with `etaNegNatFiniteDifference 1`.

## Verification completed

```text
- expected snapshot SHA-256 matched
- no sorry in the new audit modules
- no admit
- no explicit axiom declaration
- no DkMath.RH import in the new native modules
- native arithmetic independently recomputed with exact rational arithmetic
- public CFBRC and test exports updated
- user workspace full build and tests Green
- GitHub Lean CI #868 Green
```

The initial generation environment did not contain `lake`, `lean`, `elan`, or
the snapshot's `.lake` dependency cache, so only static verification was
possible there. Final elaboration and regression verification were completed
in the user's normal workspace and by GitHub Actions.

Validated commands:

```bash
cd lean/dk_math

lake build DkMath.CFBRC.Regularization.ForwardDifference
lake build DkMath.CFBRC.Regularization.NegativeInteger
lake build DkMath.CFBRC.Regularization.AbelLinear
lake build DkMath.CFBRC.Regularization.DualAudit
lake build DkMath.CFBRC.Regularization.RiemannZetaOracleAudit

lake build DkMathTest.CFBRC.Regularization.NegativeInteger
lake build DkMathTest.CFBRC.Regularization.AbelLinear
lake build DkMathTest.CFBRC.Regularization.RiemannZetaOracleAudit

./lean-build.sh && ./lean-test.sh
```
