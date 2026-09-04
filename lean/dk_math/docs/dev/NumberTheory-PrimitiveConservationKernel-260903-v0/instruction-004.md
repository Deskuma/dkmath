# PCK-002G — Square Gnomon / GN = GTail bridge implementation instructions

Date: 2026-09-04  
Branch: `wip/number-theory-primitive-conservation-kernel-260903-v0`  
Predecessor: `report-003.md` / PCK-002  
Inserted checkpoint: before PCK-003

## 0. Authorization and purpose

This is an intentionally inserted checkpoint. Do not renumber the existing PCK-003...PCK-009 roadmap.

The purpose is to freeze the square-gnomon vocabulary that has become load-bearing for the Primitive Conservation Kernel interpretation:

```text
fixed Gap unit
  +
Body growth by a Gnomon layer
  =
next Big state
```

The new vocabulary must connect directly to the canonical Cosmic Formula kernel

```lean
DkMath.CosmicFormula.GN
```

whose current canonical definition is the `r = 1` specialization of `GTail`.

This checkpoint is also a future promotion candidate for a small generic library owner such as

```text
DkMath.Lib.Gnomon
```

but DO NOT move it to `DkMath.Lib.*` now. Stabilize the theorem surface first.

## 1. Repository reuse audit

Before implementing, inspect and reuse:

```text
DkMath/CosmicFormula/Defs.lean
DkMath/CosmicFormula/CosmicFormulaBinom.lean
DkMath/CosmicFormula/CoreBeamGap.lean
DkMath/NumberTheory/Primitive/SquareBody.lean
DkMath/Collatz/GnomonEvaluation.lean
```

Important existing facts:

- canonical `DkMath.CosmicFormula.GN R x u d` is `GTail d 1 x u`;
- compatibility `CosmicFormulaBinom.GN d x u` is an abbrev wrapper;
- `BodyN 2 x u = x * GN 2 x u`;
- `BigN 2 x u = BodyN 2 x u + GapN 2 u`;
- Collatz already owns the natural/unit specialization
  `OddGnomonLayer n = 2*n+1`;
- Collatz also already proves the unit-step telescoping band
  `square_add_eq_square_add_gnomon_sum`.

Do not duplicate the Collatz owner. The new module should be the generic algebraic source from which a later one-way bridge to Collatz could be written.

## 2. Preferred new owner

Preferred file:

```text
DkMath/CosmicFormula/SquareGnomon.lean
```

Preferred namespace:

```text
DkMath.CosmicFormula.SquareGnomon
```

Use the weakest practical algebraic assumptions. Prefer `CommSemiring` for subtraction-free identities.

## 3. Required module docstring

The module docstring must explicitly record all of the following.

1. A square Gnomon is the growth layer taking one square Core to the next square while the primitive Gap unit is held fixed.

2. The canonical algebra is

$$
\operatorname{Gnomon}(x,u)
=
(x+u)^2-x^2
=
u(2x+u).
$$

For subtraction-free owners, `u(2x+u)` / the GN form is primary.

3. It is the argument-swapped degree-two GN/GTail kernel:

$$
\operatorname{Gnomon}(x,u)
=
u\,GN_2(u,x),
$$

where canonical `GN` is `GTail 2 1 u x`.

4. Existing Cosmic Body and the Gnomon are dual degree-two boundary products:

$$
\operatorname{BodyN}(2,x,u)=x\,GN_2(x,u),
$$

$$
\operatorname{Gnomon}(x,u)=u\,GN_2(u,x).
$$

5. Under a fixed `GapN 2 u = u^2`, the `BodyN` sequence grows by successive Gnomon layers. Thus the intended semantics is Body growth with Gap preserved, not "Gap growth".

6. This file is a future candidate for promotion/refactoring into a generic `DkMath.Lib.Gnomon`-style owner after the API stabilizes. No promotion is performed in this checkpoint.

7. Future resolution refinement will subdivide one coarse transition into finer Gnomon steps while preserving the same endpoint square transition after normalization/projection. Raw fine coordinates scale by the square of the resolution factor; the projection divides that scale back out. Do not claim that raw local `Gap = v^2` cells add directly to the coarse `u^2` Gap.

## 4. Core definitions

Prefer a thin abbrev surface tied to canonical GN rather than a second independent polynomial implementation.

Suggested shape:

```lean
/-- Degree-two GN kernel read in the Gnomon orientation. -/
abbrev squareGnomonKernel
    {R : Type*} [CommSemiring R] (x u : R) : R :=
  DkMath.CosmicFormula.GN R u x 2

/-- Square-growth Gnomon layer at anchor x with fixed unit u. -/
abbrev squareGnomon
    {R : Type*} [CommSemiring R] (x u : R) : R :=
  u * squareGnomonKernel x u
```

Equivalent parameter ordering is acceptable if it better matches the canonical owner, but document it clearly.

Do not create a second `GN` alias.

## 5. Required theorem surface

### 5.1 GN / GTail bridge

Expose the canonical connection explicitly. Preferred theorem or simp-normal form:

```lean
squareGnomonKernel x u = DkMath.CosmicFormula.GTail 2 1 u x
```

If this is definitional equality, a theorem with `rfl` is still useful because the bridge is semantically load-bearing.

### 5.2 Explicit kernel normal form

Prove

$$
\operatorname{squareGnomonKernel}(x,u)
=
2x+u
$$

up to commutative normal-form ordering.

### 5.3 Explicit Gnomon normal form

Prove

$$
\operatorname{squareGnomon}(x,u)
=
u(2x+u).
$$

### 5.4 Core-to-next-square identity

Prove the subtraction-free square-growth law

$$
x^2 + \operatorname{squareGnomon}(x,u)
=
(x+u)^2.
$$

This is the generic source of the classical odd Gnomon `2n+1` when `u=1`.

### 5.5 Body growth with fixed Gap

This theorem is central to the current interpretation.

Using existing `BodyN`, prove the correctly indexed step law

$$
\operatorname{BodyN}(2,x+u,u)
=
\operatorname{BodyN}(2,x,u)
+
\operatorname{squareGnomon}(x+u,u).
$$

For `u=1`, the Body sequence is

```text
0 --(+3)--> 3 --(+5)--> 8 --(+7)--> 15 ...
```

while the same fixed Gap `1` produces Big

```text
1 ----------> 4 ----------> 9 ----------> 16 ...
```

### 5.6 Big step with preserved Gap

Package the previous theorem with the existing Cosmic decomposition so the semantic statement is visible:

$$
\operatorname{BigN}(2,x+u,u)
=
\bigl(
\operatorname{BodyN}(2,x,u)
+
\operatorname{squareGnomon}(x+u,u)
\bigr)
+
\operatorname{GapN}(2,u).
$$

Do not define a new Gap. Reuse `GapN`.

### 5.7 Gnomon-kernel growth

Prove

$$
K(x+u,u)=K(x,u)+2u,
$$

where `K = squareGnomonKernel`.

This is the precise source of the statement

$$
+2u = +2\sqrt{\mathrm{Gap}}
$$

when the fixed primitive Gap is interpreted as `u^2`.

Do not introduce `Real.sqrt` merely to state this theorem. The square-root reading belongs in the docstring/report.

### 5.8 Gnomon-area growth

Prove

$$
G(x+u,u)=G(x,u)+2u^2.
$$

Thus kernel growth is `+2u`, while actual Gnomon area growth is `+2u^2`.

### 5.9 Scaling / resolution precursor

If it remains a short algebraic theorem under the same imports, also prove

$$
G(kx,ku)=k^2G(x,u).
$$

This is the raw-coordinate scaling law behind later normalized square projection.

If this theorem causes substantial typeclass/import growth, defer it to the resolution-refinement checkpoint and say so in the report.

## 6. Unit specialization and Collatz firewall

The generic module may prove a local unit specialization such as

$$
G(n,1)=2n+1
$$

over `ℕ` if this is dependency-free and useful.

Do NOT import `DkMath.Collatz.GnomonEvaluation` into the Cosmic Formula layer.

Do NOT move or rename `OddGnomonLayer`.

A later downstream bridge may prove

```lean
OddGnomonLayer n = squareGnomon n 1
```

from Collatz toward the generic owner, never the reverse dependency.

## 7. Resolution-refinement frontier: write but do not overclaim

PCK-002G should record, but need not yet implement, the following future theorem family.

For a coarse square transition

$$
x^2 \longrightarrow (x+u)^2,
$$

split the length increment `u` into `k>0` equal substeps `u/k`. The fine anchors are

$$
x_j=x+\frac{j}{k}u
\qquad (0\le j\le k).
$$

Then the exact telescoping target is

$$
\sum_{j=0}^{k-1}
\Bigl(
x_{j+1}^2-x_j^2
\Bigr)
=
(x+u)^2-x^2.
$$

Equivalently, one coarse Gnomon is the sum of its micro-Gnomons.

For integer visualization, scale coordinates by `k` to avoid fractions. Then

$$
x^2\to(x+1)^2
$$

corresponds to

$$
(kx)^2\to(kx+1)^2\to\cdots\to(kx+k)^2,
$$

and normalized projection divides square values by `k^2`.

Canonical examples to preserve in documentation:

$$
1\to4
\iff
9\to36
$$

at endpoint resolution scale `k=3`, with the fully resolved chain

$$
9\to16\to25\to36.
$$

Also

$$
4\to9
\iff
36\to49\to64\to81,
$$

whose normalized projection is

$$
4
\to
\frac{49}{9}
\to
\frac{64}{9}
\to
9.
$$

This is the intended future "square projection by resolution refinement" surface.

### Critical firewall

Raw fine coordinates are scaled coordinates. Therefore:

$$
(ku)^2=k^2u^2.
$$

Do not state raw `GapN 2 (k*u) = GapN 2 u`.

The invariant is obtained after coordinate normalization/projection, or as preservation of the total endpoint transition / telescoped Gnomon. Local micro-gap squares `(u/k)^2` do not sum unweighted to the coarse `u^2`.

## 8. No-go items

PCK-002G must not:

- modify PCK-002 `squareBody_mono`;
- implement PCK-003 coarse-to-fine primality certification;
- add prime, primorial, RH, PHZ, zeta, Xi, or CFBRC dependencies;
- introduce a generic `PrimitiveKernel` class;
- rename canonical GN/GTail;
- promote files into `DkMath.Lib.*` yet;
- create a continuous primality notion;
- use `sorry`, `admit`, `native_decide`, or a project axiom.

## 9. Verification

Run at least:

```text
lake build DkMath.CosmicFormula.SquareGnomon
git diff --check
```

If any existing downstream file is modified, build it separately.

Run `#print axioms` on the load-bearing theorems:

- GN/GTail bridge
- Core-to-next-square identity
- Body fixed-Gap growth theorem
- kernel growth theorem
- area growth theorem

Audit imports and forbidden constructs.

## 10. Report

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveConservationKernel-260903-v0/report-004.md
```

Record:

- outcome;
- starting HEAD;
- changed files;
- exact owner and imports;
- definition/abbrev surface;
- exact GN = GTail bridge;
- Body/Gap/Big indexing explanation;
- kernel `+2u` versus area `+2u^2`;
- scaling theorem status;
- existing Collatz Gnomon reuse audit;
- future `DkMath.Lib.Gnomon` promotion note;
- resolution-refinement frontier;
- build/diff/axiom audit;
- next authorization.

## 11. Next authorization

If PCK-002G is green, return to the existing roadmap:

> PCK-003 — first thin coarse-to-fine square certification adapter.

Do not implement PCK-003 in this checkpoint.
