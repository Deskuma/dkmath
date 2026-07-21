# Jacobian Counterexample Verification ROADMAP

作成日: 2026-07-21

## Final checkpoint status

| Checkpoint | Result | Status |
| --- | --- | --- |
| JAC-001 | Polynomial syntax | Complete |
| JAC-002 | Explicit rational collision | Complete |
| JAC-003 | Formal Jacobian from `MvPolynomial.pderiv` | Complete |
| JAC-004 | Determinant certificate | Complete |
| JAC-005 | Rational counterexample certificate | Complete |
| JAC-006 | Complex scalar world | Complete |
| JAC-007 | Determinant-one Keller normalization | Complete |
| JAC-008 | Public import and axiom audit | Complete |
| JAC-009 | Book of Magic `UniqueGap` / `GapCrystal` API and bridge | Complete |
| JAC-010 | General polynomial GN finite-difference theorem | Complete |
| JAC-011 | Demo and submission package | Complete |

## Final status

```text
Mathematical summit: complete
Public import: complete
Axiom audit: complete
Book of Magic extraction: complete
Demo package: complete
```

The final summit is a complex polynomial map whose formal Jacobian determinant
is `1`, together with a kernel-checked explicit collision and its noninjectivity
and no-left-inverse consequences.

## Deferred future work

- Higher-dimensional padding.
- `PrincipalPartCompletion`.

These items are not checkpoints in this roadmap and no work on them began in
JAC-011.
