# Demo Contract

The complete demonstration must remain under three minutes and use the existing
Demo aliases without recomputing any proof.

## Part A — Polynomial map (0:00–0:45)

Show the normalized complex polynomial map `(-P/2, Q, R)` and point out that
`normalizedJacobianMatrixC` is generated from its polynomial definition using
`MvPolynomial.pderiv`. The nine expanded derivative entries are optional and
should appear only as a brief proof-chain screenshot.

## Part B — Local certificate (0:45–1:25)

Show:

```lean
#check jacobianDemo_det_eq_one
#print axioms jacobianDemoCertificateC
```

Narrative: Lean computes the formal Jacobian from the polynomial definition and
proves that its determinant is exactly one.

## Part C — Global collision (1:25–2:35)

Show:

```lean
#check jacobianDemo_three_point_collision
#check jacobianDemo_notInjective
#check jacobianDemo_noLeftInverse
```

Narrative: The local Jacobian is everywhere nondegenerate, but three distinct
input addresses share one output.

Close with the DkMath Book of Magic interpretation (2:35–2:55):

```lean
#check jacobianDemo_target_notUniqueGap
```

The remaining five seconds are a static summit frame: determinant `1`, one
three-point fiber, noninjectivity, and the axiom audit. This contract specifies
the presentation only; it does not create or upload a video.
