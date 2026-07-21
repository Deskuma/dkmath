# BMV-006 Public Framework Integration

## Summary

The validated generic `DkMath.Verification` API is now public through the root
`DkMath` import. A dedicated root-import test confirms visibility and the final
generic trust boundary.

## Files Changed

```text
DkMath.lean
DkMathTest/Verification/CheckAxioms.lean
docs/verification/README.md
docs/hackathon/jacobian-counterexample-verification-260721/README.md
docs/hackathon/jacobian-counterexample-verification-260721/report-jacobian-BMV-006.md
```

## Root Public Import

`DkMath.lean` imports `DkMath.Verification` next to `DkMath.Lib` as reusable
infrastructure, before project and domain imports.

## Public API Checks

An audit module importing only `DkMath` successfully resolves:

```lean
#check DkMath.Verification.CollisionCertificate
#check DkMath.Verification.CollisionCertificate.notInjective
#check DkMath.Verification.CollisionCertificate.noLeftInverse
```

## Generic Axiom Audit with Exact Output

```text
'DkMath.Verification.CollisionCertificate.notInjective'
does not depend on any axioms

'DkMath.Verification.CollisionCertificate.noLeftInverse'
does not depend on any axioms
```

## Dependency Direction

The final source graph is:

```text
Mathlib
  ↓
DkMath.Verification.Collision
  ↓
DkMath.Verification
  ↓
DkMath root public import

DkMath.Verification
  ↓
Jacobian VerificationBridge

existing GN5 arithmetic
  ↓
GN5 summit certificate and Demo
```

`DkMath.Verification` has no import edge to the Jacobian project, GN5, Book of
Magic, or FLT.

## Documentation Status

The verification contracts README now records root-public status and the two
validation modes: an explicit Jacobian collision for the generic certificate,
and a finite GN5 arithmetic obstruction for the broader engineering workflow.
The Jacobian README records BMV-001 through BMV-006 as complete and links to the
generic contracts without changing the Jacobian submission narrative.

## Non-Goals Preserved

- No universal verification bundle or generic arithmetic structure.
- No migration of existing counterexample projects.
- No Jacobian or GN5 mathematics changed.
- No Jacobian, GN5, Book of Magic, or FLT import inside `DkMath.Verification`.
- No root import for the GN5 certificate or Demo.
- No provenance or audit structure in Lean.
- No video, TTS, submission, pull request, or merge work.

## Build Result

Successful:

```text
lake build DkMath.Verification
lake build DkMathTest.Verification.CheckAxioms
lake build DkMath
```

The focused/root-import build completed successfully with 8716 jobs. Unrelated
pre-existing root warnings are outside this checkpoint.

## Changed Files

Four existing files or public surfaces were updated/added, plus this report;
the exact five-file set is listed above. No unrelated file changed.

## Outcome

**Outcome A:** root import, public checks, generic audit, and documentation are
complete with dependency direction preserved.
