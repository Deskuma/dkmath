# DkMath Collatz: Roll-Paper Conservation Exchange Model

> **Verification design note for the Archimedean spiral conservation law**
>
> This document records an ideal roll-paper model for testing the exact
> conservation identities behind
> `Collatz-ArchimedeanSpiralConservation.md`.
>
> The central purpose is to separate two questions:
>
> ```text
> exact shell conservation:
>   annular volume / mass
>   = unrolled strip volume / mass
>
> spiral geometry correction:
>   actual spiral centerline length
>   - midpoint-circle length
> ```
>
> The first layer is an exact algebraic exchange law.  The second layer is a
> geometric correction and must not be silently merged into the first.

## 1. Physical picture

Consider a roll of paper wound around a cylindrical core.

Use the following parameters:

```text
c : core radius
R : outer roll radius
t : paper thickness
w : paper width
rho : paper density
m : number of ideal complete layers
```

The ideal discrete-layer relation is

$$
R=c+mt.
$$

The roll is first measured with its core included.  Removing the core volume
leaves the paper-only volume.

The same paper can then be cut along a radial line.  Each complete winding
becomes one strip segment.  The segments have different lengths, areas,
volumes, and masses because later windings occur at larger radii.

The expected conservation principle is:

```text
paper volume in the wound annulus
  = sum of the volumes of all unwound layer strips
```

and likewise for mass.

## 2. Whole-roll volume and mass

The cylindrical volume inside outer radius $R$ is

$$
V_{\mathrm{outer}}=\pi R^2w.
$$

The cylindrical core volume is

$$
V_{\mathrm{core}}=\pi c^2w.
$$

Therefore the ideal paper-only volume is

$$
V_{\mathrm{paper}}=\pi(R^2-c^2)w.
$$

If the paper density is $\rho$, the paper-only mass is

$$
M_{\mathrm{paper}}=\rho\pi(R^2-c^2)w.
$$

This is the Big-minus-core description.

```text
outer Big volume
- core volume
= paper Body volume
```

The core is not paper mass.  It must be measured and subtracted as an owned
inner factor before the paper conservation equation is compared with the
unwound strip representation.

## 3. Radial cut and layer decomposition

For the $j$-th winding, define its inner radius by

$$
r_j=c+jt.
$$

Its outer radius is therefore

$$
r_j+t=c+(j+1)t.
$$

The cross-sectional area occupied by this one ideal paper layer is

$$
A_j=\pi\bigl((r_j+t)^2-r_j^2\bigr).
$$

Expanding gives

$$
A_j=2\pi r_jt+\pi t^2.
$$

This is the dimensional form of the cosmic-formula gnomon.

```text
old-boundary contribution:
  2 pi r_j t

thickness successor kernel:
  pi t^2
```

The layer volume is

$$
V_j=A_jw.
$$

Its mass is

$$
M_j=\rho A_jw.
$$

Because $r_j$ increases with $j$, the layer volumes and masses are not equal.

## 4. The exact shell-to-strip exchange law

Let the corresponding unwound paper segment have length $\ell_j$.

Its rectangular volume is

$$
V_j^{\mathrm{strip}}=\ell_jtw.
$$

Exact volume conservation requires

$$
\ell_jtw=\pi\bigl((r_j+t)^2-r_j^2\bigr)w.
$$

For positive thickness and width, cancellation gives

$$
\ell_j=\frac{\pi\bigl((r_j+t)^2-r_j^2\bigr)}{t}.
$$

Expanding the square yields

$$
\ell_j=2\pi r_j+\pi t.
$$

Equivalently,

$$
\ell_j=2\pi\left(r_j+\frac t2\right).
$$

Thus one ideal annular layer exchanges exactly with a rectangular strip whose
length is the circumference of the layer midpoint radius.

The exact exchange identity is

$$
\pi\bigl((r+t)^2-r^2\bigr)w
=
2\pi\left(r+\frac t2\right)tw.
$$

Multiplying by density preserves equality:

$$
\rho\pi\bigl((r+t)^2-r^2\bigr)w
=
\rho\,2\pi\left(r+\frac t2\right)tw.
$$

Therefore:

```text
annular shell volume
  <-> midpoint-circle strip volume

annular shell mass
  <-> midpoint-circle strip mass
```

This is not an approximation inside the ideal shell model.  It is an exact
algebraic exchange.

## 5. The center Gap and successor kernel

The shell-area identity can be separated as

$$
\pi\bigl((r+t)^2-r^2\bigr)=2\pi rt+\pi t^2.
$$

Define the dimensional center kernel by

$$
\operatorname{Gap}_0=\pi t^2.
$$

Then every layer Gap has the form

$$
\operatorname{Gap}(r)=2\pi rt+\operatorname{Gap}_0.
$$

The same kernel can be read in two equivalent ways.

```text
external-factor reading:
  add pi t^2 to the old-boundary strip mass

midpoint-shift reading:
  move the reference radius from r to r + t/2
```

Indeed,

$$
2\pi rt+\pi t^2
=
2\pi\left(r+\frac t2\right)t.
$$

Thus the center Gap is exchanged for a half-thickness shift of the boundary
address.

This gives a precise interpretation of the successor kernel:

> The constant thickness kernel completes the current annular Big and, in the
> strip coordinate, moves the correct circumference reference to the middle of
> the new paper layer.

## 6. Normalization to the cosmic formula

Measure radius in units of paper thickness:

$$
P=\frac rt.
$$

Divide shell area by the common unit $\pi t^2$.

Then

$$
\frac{\pi\bigl((r+t)^2-r^2\bigr)}{\pi t^2}
=(P+1)^2-P^2.
$$

The exact normalized layer mass is therefore

$$
(P+1)^2-P^2=2P+1.
$$

The three equivalent coordinates are

```text
square-shell coordinate:
  (P + 1)^2 - P^2

boundary-plus-core coordinate:
  2P + 1

midpoint-circumference coordinate:
  2(P + 1/2)
```

Hence

$$
(P+1)^2-P^2=2P+1=2\left(P+\frac12\right).
$$

This is the exact conservation exchange behind the roll-paper test model.

## 7. Telescoping conservation over the complete roll

The ideal layer areas telescope:

$$
\sum_{j=0}^{m-1}\pi\bigl((r_j+t)^2-r_j^2\bigr)
=
\pi\bigl((c+mt)^2-c^2\bigr).
$$

Multiplying by width gives the total paper volume:

$$
\sum_{j=0}^{m-1}V_j
=
\pi\bigl((c+mt)^2-c^2\bigr)w.
$$

Multiplying again by density gives total paper mass:

$$
\sum_{j=0}^{m-1}M_j
=
\rho\pi\bigl((c+mt)^2-c^2\bigr)w.
$$

Using the strip lengths, the same volume is

$$
\sum_{j=0}^{m-1}\ell_jtw
=
\pi\bigl((c+mt)^2-c^2\bigr)w.
$$

Therefore the four descriptions exchange exactly:

```text
outer cylinder minus core cylinder
  = sum of annular layer volumes
  = sum of unwound strip volumes
  = total paper length times thickness times width
```

In normalized square-mass coordinates, the telescoping identity is

$$
P^2+\sum_{j=0}^{m-1}\bigl(2(P+j)+1\bigr)=(P+m)^2.
$$

This is the finite roll-paper realization of

```text
initial Body
+ all layer Gaps
= final Big
```

## 8. Relation to the triangle decomposition of circle area

The ordinary circle-area argument may decompose a disk into thin sectors and
rearrange them into an approximate rectangle or triangle.

Within one fixed circle, the radius is held fixed while the angular sectors are
refined.

The roll-paper model differs in one decisive respect:

```text
ordinary circle sector decomposition:
  one fixed radial boundary

roll-paper layer decomposition:
  the radial address advances by one paper thickness per winding
```

A winding cannot be represented only by the circumference at its inner radius.
During the layer extension, the boundary grows from $r$ to $r+t$.

The missing one-layer contribution is exactly

$$
\pi t^2.
$$

Equivalently, the correct strip length is not $2\pi r$ but

$$
2\pi\left(r+\frac t2\right).
$$

This is the one-sheet difference:

> A finite paper thickness changes the correct circumference address by half a
> layer and introduces the constant successor Gap $\pi t^2$.

## 9. Exact conservation versus actual spiral centerline length

The shell-to-strip identity above is exact for an ideal annular layer model.

It does not by itself assert that the physical centerline of a finite-thickness
paper winding is an exact circle of radius $r+t/2$.

For an Archimedean spiral

$$
r(\theta)=r_0+b\theta,
$$

one complete angular revolution has centerline length

$$
L_{\mathrm{spiral}}
=
\int_0^{2\pi}
\sqrt{\bigl(r_0+b\theta\bigr)^2+b^2}\,d\theta.
$$

The corresponding radial-average circumference integral is

$$
L_{\mathrm{mid}}
=
\int_0^{2\pi}\bigl(r_0+b\theta\bigr)\,d\theta.
$$

Their difference is

$$
\varepsilon
=
\int_0^{2\pi}
\left(
\sqrt{\bigl(r_0+b\theta\bigr)^2+b^2}
-
\bigl(r_0+b\theta\bigr)
\right)d\theta.
$$

For $b\neq0$ and positive radius,

$$
\varepsilon>0.
$$

Therefore two layers must remain distinct.

```text
exact shell conservation Gap:
  pi t^2

spiral-slope correction Gap:
  epsilon > 0
```

The first is the exact cosmic-formula exchange kernel.  The second measures the
extra path length caused by simultaneous tangential and radial motion.

## 10. Physical deviations in a real roll

A manufactured roll may deviate from the ideal shell model because of:

```text
paper compression
air voids
nonuniform thickness
uneven tension
core deformation
partial final winding
surface roughness
adhesive or coating layers
```

These effects do not alter the exact algebra of the ideal model.  They appear
as measured discrepancies between the ideal conserved quantity and the real
sample.

A useful experimental residual is

$$
\operatorname{ResidualMass}
=
M_{\mathrm{measured\ paper}}
-
\rho\pi(R^2-c^2)w.
$$

Another is

$$
\operatorname{ResidualLength}
=
L_{\mathrm{measured}}
-
\frac{\pi(R^2-c^2)}{t}.
$$

These residuals should be recorded as physical model Gaps, not absorbed into
the exact conservation theorem.

## 11. Proposed experimental verification

A practical test can measure:

```text
core radius c
outer radius R
paper width w
average thickness t
paper density rho
paper-only mass
unwound total length
individual winding-segment lengths after a radial cut
```

The primary equalities to test are

$$
V_{\mathrm{paper}}=\pi(R^2-c^2)w.
$$

$$
V_{\mathrm{paper}}=Ltw.
$$

$$
L=\frac{\pi(R^2-c^2)}{t}.
$$

At the layer level, test

$$
\ell_j=2\pi\left(c+\left(j+\frac12\right)t\right).
$$

At the cumulative level, test

$$
\sum_{j=0}^{m-1}\ell_jt
=
\pi\bigl((c+mt)^2-c^2\bigr).
$$

Agreement supports the exact shell-exchange model.  The remaining discrepancy
can then be studied separately as compression, void, thickness, and
spiral-slope corrections.

## 12. Proposed Lean verification core

The first formalization should avoid physical approximations and prove only the
exact exchange algebra.

Suggested namespace:

```lean
namespace DkMath.ArchimedeanSpiral.RollPaper
```

Suggested real-valued definitions:

```lean
def shellArea (r t : ℝ) : ℝ :=
  Real.pi * ((r + t) ^ 2 - r ^ 2)


def midpointCircumference (r t : ℝ) : ℝ :=
  2 * Real.pi * (r + t / 2)


def shellVolume (r t w : ℝ) : ℝ :=
  shellArea r t * w


def stripVolume (r t w : ℝ) : ℝ :=
  midpointCircumference r t * t * w
```

First exchange theorem:

```lean
theorem shellArea_eq_midpointCircumference_mul_thickness
    (r t : ℝ) :
    shellArea r t = midpointCircumference r t * t
```

Volume exchange theorem:

```lean
theorem shellVolume_eq_stripVolume
    (r t w : ℝ) :
    shellVolume r t w = stripVolume r t w
```

Mass exchange theorem:

```lean
theorem shellMass_eq_stripMass
    (rho r t w : ℝ) :
    rho * shellVolume r t w =
      rho * stripVolume r t w
```

The dimensional Gap decomposition is:

```lean
theorem shellArea_eq_boundaryMass_add_coreGap
    (r t : ℝ) :
    shellArea r t =
      2 * Real.pi * r * t + Real.pi * t ^ 2
```

The midpoint exchange is:

```lean
theorem boundaryMass_add_coreGap_eq_midpointMass
    (r t : ℝ) :
    2 * Real.pi * r * t + Real.pi * t ^ 2 =
      2 * Real.pi * (r + t / 2) * t
```

## 13. Proposed finite telescoping theorem

Define the inner radius of layer $j$ by

```lean
def layerInnerRadius (c t : ℝ) (j : ℕ) : ℝ :=
  c + j * t
```

Then prove

```lean
theorem sum_shellArea_eq_outerArea_sub_coreArea
    (c t : ℝ) (m : ℕ) :
    ∑ j ∈ Finset.range m,
        shellArea (layerInnerRadius c t j) t =
      Real.pi * ((c + m * t) ^ 2 - c ^ 2)
```

A normalized natural-number companion should prove

```lean
theorem body_add_sum_gnomonGap_eq_shifted_body
    (P m : ℕ) :
    P ^ 2 +
        ∑ j ∈ Finset.range m, (2 * (P + j) + 1) =
      (P + m) ^ 2
```

These two theorems connect the dimensional roll-paper model to the exact
natural-number cosmic formula.

## 14. Exchange principle

Once the equalities are formalized, the same conserved quantity can be moved
between representations without loss.

```text
square Big difference
  <-> finite Gnomon Gap sum
  <-> annular shell area
  <-> midpoint-circle strip length times thickness
  <-> shell volume
  <-> strip volume
  <-> shell mass
  <-> strip mass
```

This gives two inverse operations.

```text
compression:
  many owned layer Gaps
  -> one final Big difference

decomposition:
  one Big difference
  -> the exact ordered family of layer Gaps
```

The exchange is useful only when all scale factors and ownership terms are
preserved.  Core mass, paper mass, width, thickness, and density must not be
silently discarded when moving between physical coordinates.

## 15. Relation to the Collatz program

This note does not claim that a Collatz orbit is literally a paper roll.

Its role is to provide a verified conservation test model for the abstract
Big/Gap/Gnomon structure.

The intended later bridge is:

```text
roll-paper model:
  every completed outer layer owns a distinct increasing Gap mass

Collatz/Petal model:
  every claimed persistent outer revolution must own the external factor
  required to complete its next Big
```

The roll-paper theorem verifies that the algebraic exchange is exact and that
no layer Gap vanishes merely because the final Big is viewed as one object.

The remaining Collatz-specific theorem must identify:

```text
which orbit event owns each Gap,
whether that owned mass can be reused,
and whether the available orbit mass can supply all future required Gaps.
```

## 16. Exact status

The following statements are exact inside the ideal shell model:

```text
annular shell area
  = midpoint circumference times thickness

annular shell volume
  = unrolled strip volume

annular shell mass
  = unrolled strip mass

sum of all shell masses
  = outer-roll mass minus core mass

normalized shell mass
  = 2P + 1
```

The following require separate geometric or experimental analysis:

```text
actual spiral centerline length,
normal-thickness versus radial-pitch conversion,
compression and void corrections,
partial winding corrections,
and the Collatz ownership bridge.
```

## 17. Stable summary

The roll-paper verification model fixes the following conservation reading.

> A roll including its core is measured as one Big.  Removing the core isolates
> the paper-only mass.  A radial cut decomposes the paper into one segment per
> winding, and the segments have different masses because their radii and
> circumferences differ.  Nevertheless, each ideal annular shell exchanges
> exactly with a flat strip whose length is the circumference at the shell
> midpoint radius.  The constant term $\pi t^2$ is the dimensional successor
> Gap, and after normalization it becomes the cosmic-formula kernel $+1$.
> Summing every layer Gap telescopes exactly to the final outer-square mass.

In compact form:

```text
outer roll - core
  = paper mass
  = sum of layer masses
  = sum of strip masses

one layer:
  shell Big difference
  = boundary mass + center Gap
  = midpoint circumference mass

normalized:
  (P + 1)^2 - P^2
  = 2P + 1
  = 2(P + 1/2)
```

This is the proposed exact test theorem for the Archimedean spiral
conservation law.
