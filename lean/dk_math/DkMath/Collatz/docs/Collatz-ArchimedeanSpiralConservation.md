# DkMath Collatz: Archimedean Spiral Conservation Law

> **Research design note**
>
> This document records a proposed global conservation principle for the
> DkMath Collatz program.  It is not yet a completed Collatz convergence
> theorem.  Its purpose is to fix the exact algebraic and geometric structure
> that a later Lean formalization should prove and connect to the existing
> finite PetalBridge theory.

## 1. Motivation

The existing Collatz/PetalBridge development has obtained a detailed local
accounting language for:

```text
Gap
Gnomon
Big
pressure
queue
deficit
repayment
finite windows
finite channel flow
```

The remaining difficulty is global.

When the observation range is enlarged, a new outer Gap appears.  The new Gap
creates another gnomon layer, the Big boundary grows, and the local analysis
must be repeated at the next scale.

The proposed reversal is:

```text
old direction:
  inspect a finite boundary
  -> find its Gap
  -> enlarge the observation range
  -> obtain a new Gap
  -> repeat

new direction:
  formalize the exact law of Big-boundary growth
  -> compute the mass required to complete every new revolution
  -> compare that required mass with the mass actually available to an orbit
  -> derive a global obstruction to permanent outer circulation
```

The geometric model is the Archimedean spiral.

## 2. Phase closure is not metric closure

A full revolution has angular increment $2\pi$.

At the level of phase,

$$
\theta+2\pi\equiv\theta\pmod{2\pi}.
$$

This is only angular closure.

If the radius grows during the revolution, the full state does not return to
its initial value.  The next revolution begins on a larger boundary with a
larger circumference.

The state must therefore separate at least three coordinates:

```text
phase address:
  angle modulo 2π

radial address:
  the current boundary level

mass address:
  the completed Big associated with that boundary
```

A projected phase cycle may exist while the lifted radial and mass states
continue to move outward.

```text
projected phase:
  closes

lifted radius:
  does not close

lifted mass:
  does not close
```

This distinction is essential.  A $360^\circ$ revolution is not a statement
that the same path length, boundary length, or mass is repeated.

## 3. The square-mass normalization

Let $P_j$ denote the radial boundary coordinate at stage $j$.

Define the square-mass body by

$$
N_j=P_j^2.
$$

Advancing the boundary by one unit gives

$$
N_{j+1}=(P_j+1)^2.
$$

Expanding the square gives the cosmic-formula decomposition

$$
(P_j+1)^2=P_j^2+(2P_j+1).
$$

The three components are:

```text
Body_j = P_j²
Gap_j  = 2P_j + 1
Big_j  = (P_j + 1)²
```

Hence

$$
\operatorname{Body}_j+\operatorname{Gap}_j=\operatorname{Big}_j.
$$

The decisive successor identity is

$$
\operatorname{Big}_j=\operatorname{Body}_{j+1}.
$$

Completion is therefore not termination.

```text
add Gap_j
  -> complete Big_j
  -> Big_j becomes Body_(j+1)
  -> the next larger Gap_(j+1) is now required
```

The completed outer boundary is simultaneously the starting body of the next
revolution.

## 4. Meaning of the successor kernel `+1`

The gnomon Gap decomposes as

$$
2P_j+1=2P_j+\operatorname{SuccessorKernel}.
$$

with

$$
\operatorname{SuccessorKernel}=1.
$$

The term $2P_j$ records the boundary contribution at the beginning of the
extension.  The additional $+1$ records the fact that the boundary itself
grows while the next layer is being completed.

In continuous square-mass coordinates,

$$
\frac{d}{dP}P^2=2P.
$$

The exact mass needed to extend the radius from $P$ to $P+1$ is

$$
\int_P^{P+1}2r\,dr=2P+1.
$$

Thus the $+1$ is not an accidental remainder.  It is the correction mass
created because the circumference is not constant during the extension.

```text
2P:
  mass predicted from the old boundary

+1:
  mass required because the boundary grows while it is being completed
```

The same $+1$ has two roles:

```text
completion role:
  it closes the current Big exactly

successor role:
  the completed Big is already the Body of the next stage
```

This is the successor kernel of the Archimedean spiral conservation law.

## 5. Circumference must grow with radius

For an ordinary circle of radius $r$,

$$
C(r)=2\pi r.
$$

The circumference increment under a unit radial extension is

$$
C(r+1)-C(r)=2\pi.
$$

Therefore every later revolution is longer than the previous revolution.

The exact annular mass is obtained by integrating the changing circumference:

$$
A(r+1)-A(r)=\int_r^{r+1}2\pi s\,ds=\pi(2r+1).
$$

Equivalently,

$$
A(r+1)-A(r)=2\pi\left(r+\frac12\right).
$$

The required Gap is therefore not computed from the old circumference alone.
It is the integrated boundary mass over the entire radial extension.

After dividing by the constant factor $\pi$, this is exactly the square-mass
cosmic formula:

$$
(r+1)^2-r^2=2r+1.
$$

Thus the discrete gnomon and the annular area increment are the same
conservation structure in different normalizations.

## 6. One revolution creates the next revolution

Suppose one revolution advances the radial address by one unit.

Then the lifted state transition has the form

$$
(\theta,P,P^2)\longmapsto(\theta,P+1,(P+1)^2).
$$

The angle returns modulo $2\pi$, but the full state does not return.

After $k$ revolutions,

$$
(\theta,P,P^2)\longmapsto(\theta,P+k,(P+k)^2).
$$

The total Gap required for these revolutions telescopes:

$$
P^2+\sum_{j=0}^{k-1}\bigl(2(P+j)+1\bigr)=(P+k)^2.
$$

Equivalently,

$$
\sum_{j=0}^{k-1}\operatorname{Gap}(P+j)=(P+k)^2-P^2.
$$

This is the proposed conservation law.

```text
initial Body
+ every external Gap required by the completed revolutions
= final Big
```

No Gap disappears from the accounting.  Each one is absorbed into the next
Big, and that Big becomes the next Body.

## 7. Required mass grows with the circumference

If the radial level grows affinely,

$$
P_j=P_0+j,
$$

then the circumference at revolution $j$ is proportional to $P_0+j$.

The cumulative revolution length therefore grows quadratically:

$$
\sum_{j=0}^{k-1}2\pi(P_0+j)
=2\pi kP_0+\pi k(k-1).
$$

The square-mass Gap sum has the matching form

$$
\sum_{j=0}^{k-1}\bigl(2(P_0+j)+1\bigr)
=2kP_0+k^2.
$$

Thus permanent outward circulation does not require a constant cost per
revolution.  It requires an increasing cost, because each completed revolution
creates a larger circumference for the next one.

```text
radial increment per revolution:
  constant

circumference increment per revolution:
  constant

cumulative revolution cost:
  quadratic
```

## 8. External factor interpretation

In the DkMath reading, the Gap is the external factor required to reconcile the
old Body with the new completed Big.

$$
\operatorname{ExternalFactor}_j
=\operatorname{Gap}_j
=\operatorname{Big}_j-\operatorname{Body}_j.
$$

Adding this external factor always completes the next square boundary:

$$
P_j^2+(2P_j+1)=(P_j+1)^2.
$$

But the same completion immediately starts the next scale.

Therefore an orbit that claims to circulate forever must supply an infinite
sequence of increasingly large external factors:

$$
2P+1,\quad2(P+1)+1,\quad2(P+2)+1,\quad\ldots
$$

The global question is no longer whether a new Gap appears.  A new Gap must
appear by the conservation law.

The question becomes:

```text
Can the actual Collatz/Petal orbit continue to own and supply
all external Gap mass required by the growing Big boundaries?
```

## 9. Proposed Collatz contradiction pattern

Define two quantities.

```text
RequiredGapMass(P,k):
  the exact gnomon mass required to complete k further outer revolutions

AvailableGapMass(n,k):
  the external-factor mass actually generated and owned by the Collatz orbit
```

The required mass is algebraically fixed:

$$
\operatorname{RequiredGapMass}(P,k)=(P+k)^2-P^2.
$$

The desired global comparison is:

$$
\operatorname{AvailableGapMass}(n,k)
<\operatorname{RequiredGapMass}(P,k)
$$

for some finite $k$ whenever the orbit attempts to remain permanently on or
outside its current Big boundary.

At that stage:

```text
available external factor is insufficient
  -> the next Big cannot be completed
  -> the next outer revolution cannot be sustained
  -> phase closure cannot lift to a full-state cycle
  -> the orbit must cross inward
```

This is the proposed DkMath form of gravitational return.

## 10. Target descent theorem

The eventual global target should be phrased directly as strict descent below
the starting odd state.

```lean
theorem exists_accelerated_iterate_lt_self
    (n : OddNat)
    (hn : 1 < n.val) :
    ∃ k > 0, (iterateT k n).val < n.val
```

The Archimedean spiral conservation law is intended to supply the global
obstruction needed for this theorem:

```text
permanent outer circulation
  -> requires every growing Gnomon Gap
  -> cumulative required mass follows the square-growth law
  -> actual available mass eventually fails the requirement
  -> strict inward crossing
```

Once strict descent is available, well-founded induction on the natural state
can connect it to convergence.

This final connection is a future theorem, not a result claimed by this note.

## 11. Proposed Lean core

A first algebraic module can be independent of Collatz dynamics.

Suggested module:

```text
DkMath.Analysis.ArchimedeanSpiral.Conservation
```

or, if kept initially inside the current project surface:

```text
DkMath.Collatz.ArchimedeanSpiralConservation
```

Suggested definitions:

```lean
namespace DkMath.ArchimedeanSpiral

def Body (P : ℕ) : ℕ :=
  P ^ 2


def BoundaryMass (P : ℕ) : ℕ :=
  2 * P


def SuccessorKernel : ℕ :=
  1


def GnomonGap (P : ℕ) : ℕ :=
  2 * P + 1


def Big (P : ℕ) : ℕ :=
  (P + 1) ^ 2

end DkMath.ArchimedeanSpiral
```

First theorem family:

```lean
theorem body_add_gnomonGap_eq_big
    (P : ℕ) :
    Body P + GnomonGap P = Big P


theorem big_eq_next_body
    (P : ℕ) :
    Big P = Body (P + 1)


theorem gnomonGap_eq_boundary_add_successorKernel
    (P : ℕ) :
    GnomonGap P = BoundaryMass P + SuccessorKernel


theorem body_add_sum_gnomonGap_eq_shifted_body
    (P k : ℕ) :
    Body P +
        ∑ j ∈ Finset.range k, GnomonGap (P + j) =
      Body (P + k)
```

The continuous geometric bridge can follow later:

```text
circle circumference
annular area increment
Archimedean spiral turn length
radius-forgetting phase projection
phase closure versus full-state nonclosure
```

## 12. Formalization layers

The implementation should be divided into distinct layers.

### Layer A — exact natural-number conservation

```text
Body + Gap = Big
Big = next Body
Gap = boundary mass + successor kernel
finite Gap sum telescopes
```

This layer should require only elementary algebra and `Finset` sums.

### Layer B — geometric interpretation

```text
circumference grows with radius
annular mass is the integral of circumference
one angular revolution changes radial address
projected phase closure does not imply full-state closure
```

### Layer C — Collatz ownership bridge

```text
identify which orbit data owns an external Gap
connect pressure / queue / channel flow to AvailableGapMass
prove required mass is not freely reusable
```

### Layer D — global obstruction

```text
persistent outer circulation
  -> RequiredGapMass lower bound

actual orbit accounting
  -> AvailableGapMass upper bound

comparison
  -> eventual failure to complete the next Big
  -> strict inward crossing
```

The difficult part is Layer C.  The square-growth conservation itself is exact
and elementary; the Collatz theorem requires a verified ownership map from
existing local data to available external-factor mass.

## 13. Exact status and non-claims

This document fixes a research theory and formalization target.

It does not currently prove:

```text
1. that every Collatz orbit has bounded Big,
2. that AvailableGapMass is subquadratic,
3. that RequiredGapMass always dominates AvailableGapMass,
4. that every attempted outer orbit must fall inward,
5. that nontrivial Collatz cycles do not exist,
6. that every Collatz orbit converges to 1.
```

The exact established algebraic core is the identity

$$
P^2+(2P+1)=(P+1)^2
$$

and its telescoping finite sum.

The proposed new global content is the ownership comparison between required
external Gap mass and actually available orbit mass.

## 14. Stable summary

The Archimedean spiral conservation law is the following DkMath reading.

> A full $360^\circ$ revolution closes only the phase coordinate.  Because the
> radius grows, the circumference grows, and an additional external Gap must be
> supplied to complete the next Big boundary.  The exact mass is the gnomon
> $2P+1$.  Completing that Big does not end the process: the completed Big is
> the Body of the next revolution.  Therefore permanent outer circulation
> requires the cumulative supply of every increasing Gap, whose total is the
> square-growth difference $(P+k)^2-P^2$.  A Collatz orbit can be forced inward
> once its available external-factor mass is shown to be smaller than this
> required conservation mass.

In compact form:

```text
phase closes
radius advances
circumference grows
Gap completes Big
Big becomes next Body
next revolution requires a larger Gap
```

The central successor law is:

$$
N_{j+1}=(P_j+1)^2=N_j+(2P_j+1).
$$
