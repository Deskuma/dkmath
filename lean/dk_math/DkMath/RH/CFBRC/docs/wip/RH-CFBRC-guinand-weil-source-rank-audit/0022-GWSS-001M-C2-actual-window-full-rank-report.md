Global objective:
zero configuration -> independent source -> off-critical detector -> arithmetic control -> centered-coordinate uniqueness -> RiemannHypothesis

Current GWSS stage:
GWSS-001M-C2

Load-bearing provider boundary:
The result is a finite actual-window transfer for the already-prescribed
canonical Mellin family.  It uses only the finite centered-Xi zero carrier,
the C1E rank theorem, the existing spectral-factor convergence, and finite
sum identities.  No RH assumption, Weil positivity, Li criterion,
functional-equation source promotion, fixed-Xi defect provider, horizontal
decay, unrelated limit exchange, prime-side sign, or off-critical selector is
introduced.

## C2-A squared-orbit carrier and enumeration

FOUND.  `pascalCenteredXiSquaredOrbitFinset R` is the image of the actual
zero-disk finset under `z ↦ z ^ 2`.  Membership, nonzero-square, and classical
representative lemmas are exposed.  The subtype carrier is enumerated by
`Fintype.equivFin`; the representative list lies in the actual window and has
pairwise-distinct squares.  The representative choice is only finite
coordinate bookkeeping and is not promoted to an analytic source family.

## C2-B C1E bare-kernel transfer

FOUND.  `exists_pascalCenteredXiActualWindow_bareKernel_evaluation_rank`
applies `exists_complexExpSecondDifferenceKernel_evaluation_det_ne_zero` to
the enumerated actual squared-orbit representatives.  The resulting dilation
parameters are nonzero and injective, and the bare-kernel evaluation matrix
has nonzero determinant.

## C2-C canonical Mellin column scaling

FOUND.  `eventually_pascalCenteredXiActualWindow_mellin_evaluation_det_ne_zero`
uses the existing simultaneous eventual nonvanishing of the finite-window
spectral factors.  The canonical Mellin matrix is factored as the bare-kernel
matrix times a diagonal column-scaling matrix, and determinant nonvanishing is
preserved for all sufficiently small positive `ε`.

## C2-D orbit mass aggregation

FOUND.  `pascalCenteredXiSquaredOrbitMass` is the filtered multiplicity mass
of a squared orbit.  The theorem
`pascalCenteredXiZeroDiskMellinSecondDifferenceZeroMoment_eq_squaredOrbitMass_sum`
regroups the actual weighted zero moment by squared fibers.  The proof uses
the evenness of the canonical Mellin weight and does not assume an orbit has
exactly two points.

The theorem
`pascalCenteredXiMellinMomentVec_eq_mellinEvaluation_mulVec_massVec` gives the
exact finite source equation
`momentVec = H_ε *ᵥ massVec`.  Finally,
`pascalCenteredXiMellinEvaluation_mulVec_injective_of_det_ne_zero` supplies
the determinant-based injectivity consequence.

## Primary classification

`MELLIN-FAMILY-ACTUAL-WINDOW-FULL-RANK-FOUND`

For every fixed finite actual centered-Xi zero window, the canonical
zero-independent Mellin second-difference family is full rank on the finite
space of distinct squared orbits, and the actual weighted zero moments are
the corresponding full-rank matrix transform of the squared-orbit mass vector.

## Next unresolved Gap

`OFF-CRITICAL-MELLIN-WITNESS-GAP`

## Authorization status

GWSS-001 source-rank is closed.  GWSS-002 is authorized for the next bounded
assignment and was not started here.  GWSS-003 remains unauthorized.

## Verification

- `lake build DkMath.RH.CFBRC.PascalCenteredXiMellinActualWindowFullRankAudit`
  succeeds under `leanprover/lean4:v4.32.2`.
- Load-bearing public theorems use only `propext`, `Classical.choice`, and
  `Quot.sound` in their axiom footprint.
- No `sorry`, `admit`, new axiom, or `native_decide` is introduced.
- The proof reuses C1E and existing spectral-weight/eventual APIs; it does
  not weaken the carrier to individual zeros or claim rank on `z` and `-z`
  separately.
