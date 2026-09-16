# Square Gnomon, fixed-Gap growth, and resolution projection note

Date: 2026-09-04  
Campaign: Primitive Conservation Kernel  
Status: design note / future formalization frontier

## 1. Why this note exists

The PCK campaign exposed that the classical square Gnomon is not best read as "Gap growth".

The intended DkMath reading is:

> hold the primitive Gap unit fixed, and let the Body grow by successive Gnomon layers.

For degree two the Cosmic Formula already has

$$
\operatorname{BigN}(2,x,u)
=
\operatorname{BodyN}(2,x,u)
+
\operatorname{GapN}(2,u),
$$

with

$$
\operatorname{GapN}(2,u)=u^2.
$$

The fixed `u` is the discrete primitive unit. The Gap is preserved while the anchor changes.

## 2. Gnomon as argument-swapped GN / GTail

Canonical DkMath GN is the `r=1` tail specialization:

$$
GN = GTail(\_,1,\_,\_).
$$

For degree two,

$$
GN_2(x,u)=x+2u.
$$

The ordinary Cosmic Body is

$$
\operatorname{BodyN}(2,x,u)
=
x\,GN_2(x,u).
$$

The square Gnomon uses the same kernel with the two boundary roles exchanged:

$$
\operatorname{Gnomon}(x,u)
=
u\,GN_2(u,x)
=
u(2x+u).
$$

Hence

$$
x^2+\operatorname{Gnomon}(x,u)
=
(x+u)^2.
$$

This is a degree-two duality:

```text
Body     = x * GN₂(x,u)
Gnomon   = u * GN₂(u,x)
```

The new owner should preserve this link explicitly rather than introducing an unrelated polynomial definition.

## 3. Correct Body indexing under a fixed Gap

For fixed `u`,

$$
\operatorname{BodyN}(2,x,u)
=
(x+u)^2-u^2.
$$

Therefore the sequence `x = 0,u,2u,...` gives the Big square sequence with the same Gap `u^2`.

The next Body is obtained by adding the Gnomon at the current Big anchor:

$$
\operatorname{BodyN}(2,x+u,u)
=
\operatorname{BodyN}(2,x,u)
+
\operatorname{Gnomon}(x+u,u).
$$

For `u=1`:

```text
Body : 0 --+3--> 3 --+5--> 8 --+7--> 15 ...
Gap  : 1          1          1          1
Big  : 1 -------> 4 -------> 9 -------> 16 ...
```

Thus the semantic equation is not "Gap grows". It is:

```text
next Big = (current Body + next Gnomon) + same Gap
```

## 4. Where the +2 comes from

Let

$$
K(x,u)=GN_2(u,x)=2x+u.
$$

Then

$$
K(x+u,u)
=
K(x,u)+2u.
$$

Since the fixed Gap is `u^2`, this can be read dimensionally as

$$
+2u
=
+2\sqrt{\mathrm{Gap}}.
$$

The actual Gnomon layer is

$$
G(x,u)=uK(x,u),
$$

so

$$
G(x+u,u)
=
G(x,u)+2u^2.
$$

Hence two growth laws must remain distinct:

$$
\text{kernel increment}=2u,
$$

$$
\text{Gnomon-area increment}=2u^2.
$$

At unit Gap `u=1`, these become the familiar odd layers

$$
3,5,7,9,\ldots
$$

with common difference `2`.

## 5. Existing Collatz specialization

DkMath already has in `DkMath.Collatz.GnomonEvaluation`:

```lean
def OddGnomonLayer (n : ℕ) : ℕ := 2 * n + 1
```

and

```lean
theorem square_succ_eq_square_add_oddGnomonLayer
theorem sum_oddGnomonLayer_eq_square
theorem square_add_eq_square_add_gnomon_sum
```

The generic SquareGnomon owner should become the algebraic source; Collatz remains a downstream integer/unit consumer. Do not invert that dependency.

## 6. Resolution refinement

A coarse transition

$$
x^2\to(x+u)^2
$$

may be subdivided without changing its endpoints.

For `k>0`, define conceptual fine anchors

$$
x_j
=
x+\frac{j}{k}u,
\qquad
0\le j\le k.
$$

Then

$$
x_0=x,
\qquad
x_k=x+u,
$$

and the exact telescoping law is

$$
\sum_{j=0}^{k-1}
\left(
x_{j+1}^2-x_j^2
\right)
=
(x+u)^2-x^2.
$$

Thus a coarse Gnomon admits a finer Gnomon decomposition.

This is the mathematical core of "Gnomon growth resolution".

## 7. Integer-coordinate projection

Fractions can be avoided by multiplying length coordinates by `k`.

A coarse unit interval

$$
x\to x+1
$$

becomes

$$
kx\to kx+1\to\cdots\to kx+k.
$$

The raw square values are scaled by `k^2`. To project back to the original physical square coordinate, divide by `k^2`.

### Example A

Coarse:

$$
1\to4.
$$

Resolution `k=3`, endpoints:

$$
9\to36.
$$

Fully resolved fine chain:

$$
9\to16\to25\to36.
$$

After projection by `1/9`:

$$
1
\to
\frac{16}{9}
\to
\frac{25}{9}
\to
4.
$$

### Example B

Coarse:

$$
4\to9.
$$

Resolution `k=3`:

$$
36\to49\to64\to81.
$$

Projected:

$$
4
\to
\frac{49}{9}
\to
\frac{64}{9}
\to
9.
$$

This explains the intended equivalence

$$
4\to9
\iff
36\to81
$$

at the endpoint level, while the finer chain exposes intermediate rational square coordinates.

## 8. Gap-mass firewall

This point must be formalized carefully.

Under raw coordinate scaling,

$$
u\mapsto ku
$$

implies

$$
u^2\mapsto k^2u^2.
$$

Therefore raw fine-coordinate Gap values are not literally equal to the coarse numeric Gap.

The invariant statement is one of the following equivalent physical/normalized readings:

1. normalize square coordinates by `k^2`;
2. preserve the same endpoint transition after projection;
3. preserve the total coarse Gnomon as the telescope of all micro-Gnomons.

Also, if the coarse length increment `u` is split into `k` micro-increments `u/k`, then

$$
k\left(\frac{u}{k}\right)^2
=
\frac{u^2}{k},
$$

not `u^2`.

So do not identify the unweighted sum of local micro-`GapN` cells with the coarse Gap mass. The missing mass is not lost; the decomposition changes the Beam/Gnomon allocation as the anchor moves.

This firewall is important for any later conservation theorem.

## 9. Future theorem family

After PCK-002G, a future dedicated resolution checkpoint may introduce a rational/real refinement API such as:

```text
resolutionAnchor
normalizedSquareProjection
microSquareGnomon
sum_microSquareGnomon_eq_squareGnomon
normalizedSquareProjection_scale
```

Desired exact surfaces include:

$$
G(kx,ku)=k^2G(x,u),
$$

$$
\frac{(kx)^2}{k^2}=x^2
\qquad(k\ne0),
$$

and the finite telescoping identity above.

This is a candidate bridge from discrete integer square worlds to finer rational/real square projections.

## 10. Future library promotion

Once the generic algebra and resolution API stabilize, evaluate promotion from the Cosmic Formula namespace into a reusable library owner, tentatively:

```text
DkMath.Lib.Gnomon
```

Promotion should happen only if at least two independent consumers use the same API (for example Cosmic Formula / Primitive NumberTheory and Collatz or another domain).

Until then, keep the owner concrete and avoid a premature generic PrimitiveKernel abstraction.
