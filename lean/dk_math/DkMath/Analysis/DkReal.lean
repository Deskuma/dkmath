/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.DkReal.Interval
import DkMath.Analysis.DkReal.Basic
import DkMath.Analysis.DkReal.Pow
import DkMath.Analysis.DkReal.PowBound
import DkMath.Analysis.DkReal.Arithmetic
import DkMath.Analysis.DkReal.Equiv
import DkMath.Analysis.DkReal.DkNNReal
import DkMath.Analysis.DkReal.DkNNRealQ
import DkMath.Analysis.DkReal.Order
import DkMath.Analysis.DkReal.CanonicalOrder
import DkMath.Analysis.DkReal.Semantic
import DkMath.Analysis.DkReal.SemanticCF2DLogLimit
import DkMath.Analysis.DkReal.SemanticCF2DPhaseShift

#print "file: DkMath.Analysis.DkReal"

/-!
# DkReal approximation layer

Public entry point for the complete Route B algebraic checkpoint:

* `GapInterval` gives exact rational closed intervals;
* `DkReal` gives nested interval sequences of vanishing width;
* `DkReal.Equiv` identifies representations of vanishing separation;
* `DkNNReal` packages nonnegativity;
* `DkNNRealQ` is the quotient-backed nonnegative ordered `CommSemiring`;
* `DkReal.CanonicalOrder` extracts nonnegative Gap universes.
* `DkReal.Semantic` gives the noncomputable bridge to Mathlib's `Real`.

All endpoint operations in the representation modules remain computable. The
publicly imported optional `Semantic` module selects a Mathlib `Real` value
noncomputably; it does not alter the computable representation operations.

`DkReal.Order` defines a quotient-compatible asymptotic order and installs a
`PartialOrder` and Mathlib's semiring-level `IsOrderedRing` predicate on
`DkNNRealQ`. Addition, nonnegative multiplication, and natural powers are
monotone, and zero is least.

Totality is proved internally from nested-interval geometry. If a finite
strict left separation is witnessed, it persists. Otherwise the reverse order
defect is bounded by a vanishing interval width.

Canonical order is also constructive at the representation level. From
`x ≤ y`, `CanonicalOrder` extracts a computable nonnegative Gap `z` such that
`y = x + z` in the quotient. No subtraction operation is added to
`DkNNRealQ`.

The strict-order kernel classifies this known Gap: wrapper strictness is
equivalent both to finite left separation and to a positive lower endpoint of
the canonical Gap at some stage. This keeps the design in the same
`Big = (Core + Beam) + Gap` pattern.

Strict order has now descended to the quotient. Addition preserves it by
moving to a sufficiently precise stage. Multiplication preserves it for a
strictly positive factor by transforming the canonical Gap from `z` to
`z * a`; the zero-factor branch collapses that Gap.

`CanonicalOrder` installs Mathlib's `IsStrictOrderedRing`. Its requirements
match the proved API: cancellative ordered addition, nontriviality, and strict
multiplication by positive factors. It requires neither additive inverses nor
a linear order.

[DESIGN: linear-order] Retain `PartialOrder` plus `Std.Total`. Mathlib's
`LinearOrder` requires decidable comparison and equality, but no terminating
decision procedure for asymptotic interval order is currently available.
Classical comparison should therefore remain an explicit local choice.

`DkReal.Semantic` selects the lower-endpoint supremum, proves that it is the
unique real point lying in every approximation interval, and proves invariance
under representation equivalence. Its quotient map preserves rational
constants, addition, multiplication, natural powers, and canonical order.

[TODO: semantic-order-reflection] Prove that an inequality between semantic
values reconstructs the canonical quotient order, without adding decidable
comparison.

[IMPLEMENTED: semantic-cf2d-action] `DkReal.SemanticCF2D` transports unit
kernels to `Real`, derives the Pythagorean coordinate identity, and applies
the resulting kernel as a real square-mass-preserving action. Transported
actions compose through real-side kernel products and restrict to every real
square-mass level set. Real-side conjugation supplies inverse actions, so
these maps are equivalences of the plane and of each level set. Their finite
iterates generate forward orbits of constant square mass. Periodic points and
finite action order are expressed through Mathlib's standard discrete-dynamics
API. Minimal periods use Mathlib's zero-for-aperiodic convention and divide
all known return times. Fixed points and positive finite action order are
separated from the weaker zero-iterate-compatible periodicity predicates.
Identity transported kernels fix every point; nonidentity transported kernels
fix exactly the origin.

[IMPLEMENTED: semantic-cf2d-phase-profile] `DkReal.SemanticCF2DPhase` fills one
step of the core-zero order-four action by an affine edge. The edge leaves the
fixed `q2` boundary by the exact factor
`phaseDepth t = (1-t)^2 + t^2`. Square completion proves a positive lower bound
of one half, and reflection about the midpoint proves the first continuous
half-fold symmetry without introducing circles or angles.

[IMPLEMENTED: semantic-cf2d-dyadic] `DkReal.SemanticCF2DDyadic` samples one
phase at the finite nodes `k / 2^n`. Endpoint, unit-interval, reflection,
even-child, odd-child midpoint, and reflected phase-depth laws are proved
without selecting a correction product or taking a limit. This semantic-real
mesh is noncomputable because its nodes use division in `Real`; a future
computable variant should retain rational nodes before crossing the bridge.

[IMPLEMENTED: semantic-cf2d-finite-refinement]
`DkReal.SemanticCF2DRefinement` evaluates depth and normalization on the
dyadic mesh. Reflection and even-child inheritance hold for both observations.
At every odd child, quadraticity gives the exact finite correction
`1 / (2 * (2^n)^2)` from the average of adjacent parent depths. This defect
is positive, so every genuine odd child lies strictly below that average.
Summing the identical defect over all `2^n` parent intervals gives the exact
finite total `1 / (2 * 2^n)`.

[IMPLEMENTED: semantic-cf2d-depth-limit] `DkReal.SemanticCF2DLimit` separates
the per-level and cumulative scales. The total defect introduced at level
`n + 1` is `(1/2)^(n+1)` and tends to zero. The cumulative defect through
levels `0, ..., m-1` is exactly `1 - (1/2)^m` and tends to one. These are
elementary geometric limits, not Gaussian or `pi` identifications.
The limit module itself introduces only theorems and therefore needs no
`noncomputable section`, while its imported real-valued definitions remain
noncomputable.

[IMPLEMENTED: semantic-cf2d-finite-composition]
`DkReal.SemanticCF2DComposition` samples depth and normalization on the same
complete finite dyadic mesh. The squared normalization product exactly
cancels the depth product, and both products are strictly positive. This is a
finite pointwise-composition theorem, not a selected infinite-product limit.
Nonvanishing and reciprocal forms are also exposed for downstream finite
algebra.

[IMPLEMENTED: semantic-cf2d-finite-log-composition]
`DkReal.SemanticCF2DLogComposition` transfers the positive finite
cancellation law to logarithmic sums. Each log sum is identified with the
logarithm of its finite product, and
`2 * logNormalizationSum + logDepthSum = 0`. Uniform-average and mesh-width
weighted variants are exposed as finite candidate observables, and the same
cancellation law is proved for them. A pointwise weighted cancellation lemma
then supplies the standard trapezoidal endpoint half-weight candidate. No
logarithmic quantity is yet selected as the canonical refinement-limit
observable. The total masses of the average, plain mesh-width, and
trapezoidal weights are also exposed to distinguish sample-mean,
endpoint-overcounted complete-mesh, and closed-interval candidates. The
endpoint logarithms vanish, so the plain mesh-width and trapezoidal log-depth
and log-normalization observables agree despite their different total masses.
The underlying general comparison theorem states that, for any finite
observable, the mesh-width minus trapezoid discrepancy is exactly the
half-width endpoint correction. A zero-endpoint corollary packages the common
case where that correction vanishes. The centered log-depth increment is now
defined, identified with an explicit centered quadratic logarithm, and shown
to restore a finite mesh/trapezoid discrepancy of `h_n * log 2`. Its centered
quadratic profile is positive, and the pointwise bound
`0 ≤ centeredLogPhaseDepth t ≤ 4 * (t - 1/2)^2` is available. The bound has
also been lifted to arbitrary nonnegative finite weights, with mesh-width,
uniform-average, and trapezoidal corollaries. Thus the centered logarithmic
correction is already controlled by finite centered quadratic moments, before
any Gaussian, integral, or `pi` interpretation is selected. The first crude
finite moment estimate is also available: the trapezoidal centered quadratic
sum is bounded by one. The finite trapezoidal centered quadratic moment is
now evaluated exactly as
`1 / 3 + 2 / (3 * (dyadicPhaseDenom n : ℝ)^2)`, exposing the finite correction
to the later `1 / 3` target without taking a limit. The centered log-depth
trapezoidal sum is consequently bounded above by that same closed expression.
`DkReal.SemanticCF2DLogLimit` then opens the first DkMath-named limit layer:
the closed quadratic bound and the trapezoidal centered quadratic moment both
tend to `1 / 3` along refinement depth. These theorems use Mathlib filters
through the `DkLimit` vocabulary and still do not identify the centered
log-depth limit.

[IMPLEMENTED: semantic-cf2d-phase-shift] `DkReal.SemanticCF2DPhaseShift`
exposes the endpoint-center-pole-shift skeleton before any angle vocabulary.
The local center `phaseCenter = 1 / 2` is recognized by the unique minimum of
`phaseDepth`, and centered reflection is available directly. Unwrapped
quarter-cycle coordinates prove that the seam endpoint between adjacent
quarter edges is the midpoint between their centers, isolating the one-eighth
phase displacement without using circle or arc language. Scalar return laws
for dyadic and positive `k` cycle divisions are also recorded. The shifted
scalar frame now names neighboring centers as endpoints and proves that its
affine center is the old seam endpoint. The affine and normalized semantic
edges expose their midpoint `q2` facts. The semantic shifted-endpoint
candidates are also named: normalized neighboring centers stay on the same
`q2` boundary, but their raw midpoint has square mass `1 / 2 * q2 z`, so a
center correction rescales that raw midpoint exactly back to the old seam and
to the original `q2` boundary. The raw shifted affine edge has the same
`phaseDepth` profile as the original affine edge, so the same pointwise
normalization defines a shifted boundary-valued edge whose center is the old
seam. This shifted normalized edge is now continuous, packaged as a Mathlib
`Path`, and also packaged as a path internal to the fixed `q2` level set.
Adjacent shifted edges share their normalized center endpoint, preparing the
later cyclic concatenation layer without adding geometric angle vocabulary.
The shifted edge is now also indexed by semantic action iterates. Indexed
bases stay on the initial square-mass level, adjacent indexed shifted edges
share seams, their centers are the next indexed bases, and core-zero
four-step return holds for bases, endpoints, and edge functions. Fixed-`q2`
indexed level-set paths expose the same compatibility inside the boundary.

[IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
coordinate-product topology from `CF2D.Topology` to package every translated
affine edge as a Mathlib `Path`. Four seam-compatible edges concatenate to a
closed continuous piecewise-affine path under the core-zero action. This path
is not yet normalized to a fixed `q2` boundary.

[IMPLEMENTED: semantic-cf2d-normalized-edge]
`DkReal.SemanticCF2DNormalize` divides one affine edge by the positive square
root of `phaseDepth`. The resulting edge is continuous, has the same
endpoints, and remains on the initial `q2` boundary for every real parameter
under the core-zero action. Its four action translates retain this boundary,
join at exact seams, repeat with phase index four, and concatenate to a closed
continuous path. The final path is also packaged directly in
`LevelSet Real (q2 z)`, so boundary membership is enforced by its codomain.
`CF2D.EuclideanPhase` then interprets this boundary as the explicit
two-coordinate Euclidean circle equation and maps the existing closed path
through that homeomorphism. The zero boundary is kept as a separate
one-point degenerate case. A second homeomorphism identifies the coordinate
circle with Mathlib's standard `EuclideanSpace Real (Fin 2)` L2 metric sphere
of radius `sqrt (q2 z)`.
In that standard Euclidean plane, the semantic core-zero action is identified
with the coordinate quarter-turn linear isometry `(x,y) ↦ (-y,x)`.
The same Euclidean interpretation now names the angle-reading vocabulary:
`semanticQuarterTurnAngle = Real.pi / 2`, `semanticHalfTurnAngle = Real.pi`,
and `semanticFullTurnAngle = 2 * Real.pi`. These are external readings of the
already-proved action, not intrinsic constructions of `pi`. The iterate API
`semanticActIter r k z` proves that core-zero semantic action depends only on
`k % 4`, and `EuclideanPhase` reads that finite phase as rotation by
`semanticPhaseAngle (k % 4)`. This closes the finite four-state phase table
while leaving intrinsic `pi` and continuous-angle construction as future
research tasks.

[TODO: semantic-cf2d-signed] Source-level `Vec.star` and `KernelFamily` require
signed arithmetic. Defer them until a signed DkReal layer exists.

[TODO: signed-arithmetic] General signed multiplication requires the minimum and maximum of four
endpoint products and belongs outside the current nonnegative API.
-/
