# instruction-007 — Two-channel coordinate kernel / PowerSwap bridge audit

## 0. Scope

Treat this as a bounded structural checkpoint.

BCAL-000 through BCAL-006 established a repeated exact pattern:

```text
left component  U
right component V
sum/mass        M = U + V
balance         Q = U - V
center          P = (U + V) / 2
```

The pattern now has at least two real production consumers:

1. `DkMath.PowerSwap.Contours`

    ```text
    U = gapU x y
    V = gapV x y
    gapP = (U + V) / 2
    gapQ = U - V
    ```

2. ABC/GN balance calibration

    ```text
    U = GNChannelSupportMass
    V = GNChannelDepthMass
    GNChannelMass    = U + V
    GNChannelBalance = U - V
    ```

BCAL-006 also exposed the generic right-channel step law: increasing the right component by `δ` sends

```text
M -> M + δ
Q -> Q - δ.
```

The goal is to determine whether this common linear coordinate transform deserves a small public `DkMath.Lib.*` kernel and, only if justified, implement it without disturbing existing public APIs.

This checkpoint is **not** about ABC estimates, PowerSwap analytics, or Hensel existence.

## 1. Repository-first audit

Before editing production files, inspect:

```text
DkMath/Lib/README.md
DkMath/PowerSwap/Contours.lean
DkMath/ABC/GNBalanceCalibration.lean
DkMath/ABC/GNBalanceDepthLayers.lean
DkMath/ABC/GNBalanceDepthTransport.lean
```

Also search for any existing generic sum/difference, center/difference, beam/balance, or two-channel coordinate abstraction.

Do not create a competing API if an existing public kernel already provides the needed transform.

`DkMath.Lib.*` is intended for stable reusable APIs, not research-specific local concepts. Any new library declaration must therefore avoid ABC-, GN-, PowerSwap-, shell-, Hensel-, or valuation-specific names.

## 2. Candidate generic kernel

If no equivalent public kernel exists, a minimal candidate is conceptually:

```text
mass(U,V)    = U + V
balance(U,V) = U - V
center(U,V)  = (U + V) / 2
```

The implementation may use a namespace such as

```text
DkMath.Lib.TwoChannel
```

and a file such as

```text
DkMath/Lib/TwoChannel.lean
```

if that fits current repository conventions.

Prefer the smallest typeclass/generalization that serves the actual consumers. Since both current consumers are real-valued, an `ℝ` kernel is acceptable if a more generic additive/field abstraction would add proof noise without reuse.

Do not introduce a structure merely to package two real numbers unless the structure materially improves theorem reuse.

## 3. Minimum exact API

If the abstraction is implemented, it should support the following exact laws or equivalent formulations.

### 3.1 Reconstruction

For

```text
M = U + V
Q = U - V
```

recover

```text
U = (M + Q) / 2
V = (M - Q) / 2.
```

Also relate `center` and `mass`:

```text
center(U,V) = mass(U,V) / 2.
```

### 3.2 Zero contour

```text
balance(U,V) = 0 <-> U = V.
```

This is a coordinate identity only. Do not call it an optimum, stability condition, extremum, or ABC boundary.

### 3.3 Swap symmetry

```text
mass(V,U) = mass(U,V)
center(V,U) = center(U,V)
balance(V,U) = -balance(U,V).
```

### 3.4 One-channel transport

For a right-channel increment `δ`:

```text
mass(U, V + δ) = mass(U,V) + δ
balance(U, V + δ) = balance(U,V) - δ.
```

For completeness, the left-channel counterpart may be included if it remains trivial and useful:

```text
mass(U + δ, V) = mass(U,V) + δ
balance(U + δ, V) = balance(U,V) + δ.
```

These are algebraic transport laws, not statements that such an arithmetic increment exists.

## 4. PowerSwap consumer bridge

Without changing the meaning of the existing declarations, prove exact bridge lemmas such as:

```text
gapP x y = center (gapU x y) (gapV x y)
gapQ x y = balance (gapU x y) (gapV x y).
```

If useful and clean, recover `gapU` and `gapV` from `gapP` and `gapQ` through the generic reconstruction theorem.

Do not rewrite the existing `gapF_eq_soft_hyperbolic_form` proof merely to force use of the abstraction. Existing stable proofs may remain untouched.

Do not change the existing public definitions `gapU`, `gapV`, `gapP`, or `gapQ` unless there is an overwhelming dependency-neutral reason.

## 5. ABC/GN consumer bridge

Prove exact bridge lemmas identifying the existing coordinates with the generic kernel:

```text
GNChannelMass T p
  = mass (GNChannelSupportMass T p)
         (GNChannelDepthMass T p)

GNChannelBalance T p
  = balance (GNChannelSupportMass T p)
            (GNChannelDepthMass T p).
```

The existing reconstruction theorems from BCAL-000 should either remain valid unchanged or become immediate corollaries. Do not break theorem names or downstream code merely to deduplicate two-line ring proofs.

Optionally, if it is genuinely useful, expose the outer ABC coordinate with the orientation that matches its existing sign convention:

```text
ABCOuterBalance
  = balance ABCOutputDepthMass ABCInputSupportMass.
```

Do not identify inner and outer balances; their chosen channel orientations remain different.

## 6. BCAL-006 transport interpretation

Audit whether the exact Level-A successor laws from `GNBalanceDepthTransport.lean` can be stated or reproved cleanly as instances of the generic one-channel transport law.

The local decomposition is conceptually

```text
support coordinate = log q
depth coordinate   = (v_q(GN) - 1) * log q.
```

An exact valuation successor keeps the support coordinate fixed and increments the depth coordinate by `log q`, hence:

```text
localMass    -> localMass + log q
localBalance -> localBalance - log q.
```

If routing the existing theorem through the generic kernel requires substantial coercion/factorization boilerplate, do not refactor it. A bridge/corollary is sufficient.

Most importantly: the generic transport theorem must not be presented as Hensel lift existence.

## 7. Dependency rule

The generic kernel, if created, must depend only on stable lower-level imports (preferably Mathlib / existing `DkMath.Lib` foundations).

Required direction:

```text
DkMath.Lib.TwoChannel
        ↓
PowerSwap bridge     ABC bridge
```

Forbidden direction:

```text
DkMath.Lib.* -> DkMath.ABC.*
DkMath.Lib.* -> research checkpoint modules
```

Avoid import cycles.

## 8. Do not do

Do not in this checkpoint:

- prove any new ABC bound;
- introduce a uniform calibration constant;
- introduce a new ABC contract;
- prove Hensel lift existence;
- strengthen `card R_(k+1) ≤ card R_k` to equality;
- add shell counting, incidence, moment, or density estimates;
- optimize numerical exponents;
- claim `Q = 0` is globally optimal;
- identify PowerSwap `gapQ` with ABC `GNChannelBalance` as mathematical quantities;
- force a category-theoretic, normed-space, matrix, or linear-map abstraction unless existing code clearly needs it;
- replace existing public APIs solely for aesthetic uniformity.

## 9. Outcome classes

### Outcome A — GENERIC KERNEL JUSTIFIED

A small dependency-neutral kernel is added and both PowerSwap and ABC/GN consume it through exact bridge theorems. Existing APIs remain compatible and builds stay green.

### Outcome B — LOCAL BRIDGE ONLY

The common algebra is real but extracting a public kernel would create dependency or API churn. Add only minimal consumer-side bridge lemmas, or document the exact obstruction.

### Outcome C — NO ABSTRACTION JUSTIFIED

An equivalent existing abstraction already exists, or the apparent commonality is too shallow to justify production surface. Add no duplicate kernel; document the existing replacement.

## 10. Validation

At minimum run the appropriate focused builds for every touched module plus:

```text
lake build DkMath.PowerSwap
lake build DkMath.ABC
```

If a new `DkMath.Lib` module is added, build it directly as well.

Also run:

```text
#print axioms
forbidden-token scan
git diff --check
```

No new `sorry`, `admit`, `axiom`, `unsafe`, or research-only dependency may enter the new kernel.

## 11. Report

Write:

```text
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/report-007.md
```

Record:

- Outcome A/B/C;
- existing abstractions audited;
- exact generic API, if any;
- PowerSwap bridge theorem names;
- ABC/GN bridge theorem names;
- whether BCAL-006 transport was cleanly recognized as one-channel transport;
- dependency graph / cycle check;
- anything deliberately left unrefactored;
- build and axiom-audit results.

## 12. Interpretation rule

The purpose of this checkpoint is not to claim that PowerSwap and ABC are the same mathematics.

The claim under audit is much narrower:

> both currently use the same exact two-channel linear coordinate transform, and the transform itself may deserve a shared stable kernel.

Keep domain-specific arithmetic and analytic meaning in their own modules.
