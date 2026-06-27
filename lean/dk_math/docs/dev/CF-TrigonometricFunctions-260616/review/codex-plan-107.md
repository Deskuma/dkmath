# Codex plan

Target:
  DkMath.Analysis.DkReal.SemanticCF2DPhaseShift

Goal:
  Continue checkpoint 104 by adding the shifted-frame scalar API and then
  lift it toward the semantic/normalized edge layer where feasible.

Principle:
  Do not introduce angle, arc, degree, pi/4, rotation, or circle language in
  Lean theorem names. Keep this as normalized cycle / endpoint / center /
  shifted-frame structure. Euclidean reading is later.

Part A: thin scalar wrappers

Add scalar shifted-frame names:

  shiftedQuarterLeftEndpoint k  := globalQuarterCenter k
  shiftedQuarterRightEndpoint k := globalQuarterCenter (k + 1)
  shiftedQuarterCenter k        := globalQuarterEndpoint (k + 1)

Add theorem aliases/wrappers:

  shiftedQuarterLeftEndpoint_eq_center
  shiftedQuarterRightEndpoint_eq_next_center
  shiftedQuarterCenter_eq_next_endpoint

  shiftedQuarterRightEndpoint_eq_leftEndpoint_add_quarter
  shiftedQuarterCenter_eq_midpoint

The main scalar theorem should say:

  shiftedQuarterCenter k =
    (shiftedQuarterLeftEndpoint k + shiftedQuarterRightEndpoint k) / 2

This is the shifted-frame reading of the already-proved theorem
globalQuarterEndpoint_succ_is_center_between_centers.

Part B: heavier scalar theorem

Add a generic affine midpoint theorem for real scalars:

  affineMidpoint a b =
    (a + b) / 2

or, if avoiding a new def, prove directly that the affine interpolation
between shiftedQuarterLeftEndpoint k and shiftedQuarterRightEndpoint k
at phaseCenter equals shiftedQuarterCenter k.

Candidate theorem:

  theorem shiftedQuarterAffine_center_eq_shiftedQuarterCenter (k : ℕ) :
      (1 - phaseCenter) *shiftedQuarterLeftEndpoint k
        + phaseCenter* shiftedQuarterRightEndpoint k =
          shiftedQuarterCenter k

This theorem is important because it prepares the shifted-frame path layer.

Part C: semantic edge lift

If the existing semanticPhaseEdge API is convenient, add a shifted semantic
edge between neighboring centers only after the scalar theorem is done.

If a new shifted path definition feels premature, do not force it. Instead add
TODO comments with the intended theorem shape.

Candidate future definition:

  shiftedSemanticPhaseEdge r z k t

but only introduce it if the endpoint terms are already clear from existing
normalizedPhaseEdge or semanticPhaseEdge APIs.

Part D: q2 / normalization target if feasible

Try to prove a heavier theorem only if it is direct from existing midpoint
facts:

  shifted-frame center corresponds to the old seam endpoint at scalar level.
  normalized midpoint returns to the same q2 boundary.

If path definitions are not ready, stop after scalar shifted-frame API and
record TODOs.

Required checks:

  lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
  lake build DkMath.Analysis.DkReal
  git diff --check

Docs:

  Update design-phase-center-shift-104.md implemented checkpoint.
  Add a short note that the shifted-frame scalar API is implemented.
