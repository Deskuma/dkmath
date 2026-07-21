# Instructions

## JAC-008

Implement checkpoint JAC-008 Public Import and Audit for the DkMath
Jacobian counterexample verification project.

Repository:
Deskuma/dkmath

Branch:
hackathon/breaking-math-jacobian-counterexample

Completed checkpoints:

- JAC-001 Polynomial syntax
- JAC-002 Rational collision
- JAC-003 Formal rational Jacobian
- JAC-004 Rational determinant certificate
- JAC-005 Rational counterexample certificate
- JAC-006 Complex scalar lift
- JAC-007 Keller normalization

The mathematical summit theorem is complete:

```lean
normalizedJacobianCounterexampleCertificateC
```

Stop after JAC-008.
Do not begin Book of Magic APIs, higher-dimensional padding, GN bridges,
or Demo/submission documentation.

## Repository convention correction

The original roadmap listed:

```text
DkMath/Hackathon.lean
```

but this file does not currently exist.

Do not create a broad `DkMath/Hackathon.lean` aggregator in this checkpoint.

The current root module directly imports individual Hackathon public surfaces.
Follow the current repository convention.

## 1. Create the project aggregator

Create:

```text
lean/dk_math/DkMath/Hackathon/JacobianCounterexample3.lean
```

Preferred contents:

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Hackathon.JacobianCounterexample3.Normalized

#print "file: DkMath.Hackathon.JacobianCounterexample3"
```

The final leaf `Normalized` already imports the full dependency chain.

Do not duplicate definitions or theorems in the aggregator.

If repository style requires explicit imports of all component modules,
that is acceptable, but prefer the single final-leaf import unless there
is a concrete visibility problem.

## 2. Publish through DkMath.lean

Modify:

```text
lean/dk_math/DkMath.lean
```

Add the public import near the existing Hackathon import:

```lean
-- Hackathon Jacobian counterexample formal certificate
import DkMath.Hackathon.JacobianCounterexample3
```

Keep:

```lean
import DkMath.Hackathon.FinitePrimeEscapeGN5
```

unchanged.

Do not modify unrelated imports or reorder the whole file.

## 3. Create the axiom audit module

Create:

```text
lean/dk_math/DkMathTest/Hackathon/JacobianCounterexample3/CheckAxioms.lean
```

Import only the public aggregator:

```lean
import DkMath.Hackathon.JacobianCounterexample3
```

Add intentional audit commands:

```lean
#print axioms
  DkMath.Hackathon.JacobianCounterexample3.jacobianCounterexampleCertificateQ

#print axioms
  DkMath.Hackathon.JacobianCounterexample3.jacobianCounterexampleCertificateC

#print axioms
  DkMath.Hackathon.JacobianCounterexample3.normalizedJacobianCounterexampleCertificateC
```

Use single-line commands if Lean syntax requires it:

```lean
#print axioms DkMath.Hackathon.JacobianCounterexample3.jacobianCounterexampleCertificateQ
```

These `#print axioms` commands are intentional and should remain in the
test/audit file.

## Audit interpretation

The audit goal is:

- no `sorryAx`;
- no user-defined project axiom;
- no unproved determinant or collision assumption;
- no `native_decide` trust dependency.

Standard Lean axioms such as the following may appear depending on Mathlib's
implementation and theorem dependencies:

```text
propext
Classical.choice
Quot.sound
```

Do not treat these standard trusted foundations as a failed audit.

Report the exact output for each theorem.

The important failure signals are:

```text
sorryAx
DkMath-specific axiom
unexpected named assumption
```

## 4. Public-surface checks

In a temporary file importing only:

```lean
import DkMath.Hackathon.JacobianCounterexample3
```

verify:

```lean
#check DkMath.Hackathon.JacobianCounterexample3.jacobianCounterexampleCertificateQ
#check DkMath.Hackathon.JacobianCounterexample3.jacobianCounterexampleCertificateC
#check DkMath.Hackathon.JacobianCounterexample3.normalizedJacobianCounterexampleCertificateC
#check DkMath.Hackathon.JacobianCounterexample3.normalized_three_point_collision_C
#check DkMath.Hackathon.JacobianCounterexample3.evalNormalizedCounterexampleC_noLeftInverse
```

Remove the temporary check file after verification.

Do not place these temporary `#check` commands in production modules.

## 5. Verification targets

Build:

```text
DkMath.Hackathon.JacobianCounterexample3
DkMathTest.Hackathon.JacobianCounterexample3.CheckAxioms
DkMath
```

Also build the eight component modules if needed to isolate an import issue,
but do not modify already completed proofs merely for import cosmetics.

Run:

```text
git diff --check
```

## Restrictions

Do not:

- modify any mathematical theorem or definition;
- refactor the completed proof chain;
- create `DkMath/Hackathon.lean`;
- add `#print axioms` to files under `DkMath/**/*.lean`;
- add `#check` commands to production files;
- begin higher-dimensional padding;
- begin Book of Magic APIs;
- begin `GNFiniteDifference`;
- create Demo.lean;
- create submission documentation;
- use `sorry`;
- introduce axioms;
- use `native_decide`.

## Report

Report:

1. files created and modified;
2. exact aggregator imports;
3. exact location of the new `DkMath.lean` import;
4. exact `#print axioms` output for each of the three certificate theorems;
5. whether any `sorryAx` or DkMath-specific axiom appeared;
6. public-surface `#check` results;
7. build results and warnings;
8. `git diff --check` result;
9. confirmation that JAC-009 and later checkpoints were not started.

Stop after JAC-008 and wait for review.
