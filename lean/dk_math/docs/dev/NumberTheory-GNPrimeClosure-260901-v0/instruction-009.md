# Codex Instruction — GNPC-009 Public Import Surface / Merge-Readiness Facade

Branch: `wip/number-theory-gn-prime-closure-260901-v0`

Project: DkMath NumberTheory GN Prime Closure

Start from current GNPC-008 implementation commit:

```text
ca72e4bdddc1cd7a46f2ecc2758a0e395d182c0a
```

This is a merge-preparation checkpoint. The mathematical implementation GNPC-001 through GNPC-008 is already present and individually validated. The purpose of GNPC-009 is to make that work available through a clean public import surface before opening the PR to `develop`.

Do **not** change the mathematics unless a genuine import-cycle or declaration-owner issue is discovered. Do **not** merge the branch or open the PR in this checkpoint.

---

# 0. Reconnaissance result to preserve

Relative to `develop`, the branch currently adds eight Lean owner modules:

```text
DkMath/NumberTheory/GNPrimeClosure.lean
DkMath/NumberTheory/GNRepresentationBounds.lean
DkMath/NumberTheory/GNDegreeFactorization.lean
DkMath/NumberTheory/GNPrimeTargetResidue.lean
DkMath/NumberTheory/GNThreeQuadratic.lean
DkMath/NumberTheory/GNThreePrimeArithmetic.lean
DkMath/NumberTheory/GNThreeHenselLift.lean
DkMath/NumberTheory/GNThreeHenselDepth.lean
```

The current dependency DAG is intentionally thin:

```text
GNPrimeClosure
    └─ standalone elementary factor-one owner

GNRepresentationBounds
    ↓
GNDegreeFactorization
    ↓
GNPrimeTargetResidue ──→ WeightedGNBridge
                         
GNThreeQuadratic ───────┐
                       ↓
GNThreePrimeArithmetic
    ↓
GNThreeHenselLift
    ↓
GNThreeHenselDepth
```

More explicitly:

```text
GNRepresentationBounds
  imports CosmicFormulaBinom

GNDegreeFactorization
  imports GNRepresentationBounds

GNPrimeTargetResidue
  imports GNDegreeFactorization
  imports WeightedGNBridge

GNThreeQuadratic
  imports CosmicFormulaBinom
  imports TraceOneQuadratic

GNThreePrimeArithmetic
  imports GNPrimeTargetResidue
  imports GNThreeQuadratic

GNThreeHenselLift
  imports GNThreePrimeArithmetic

GNThreeHenselDepth
  imports GNThreeHenselLift
```

`GNPrimeClosure.lean` is independent of the main chain and owns the elementary theorem

```lean
prime_boundary_mul_GN_iff
```

and its GN-prime specialization.

At present, none of these eight modules is imported from the root `DkMath.lean` NumberTheory surface. Therefore the implementation is usable only by importing individual owners directly.

The repository already uses explicit public-entry facades such as

```text
DkMath.NumberTheory.Primitive
```

which collect related owner modules without moving their declarations. GNPC-009 should follow that convention.

---

# 1. Public facade decision

Create a new public entry module:

```text
lean/dk_math/DkMath/NumberTheory/GNPrime.lean
```

Canonical import name:

```lean
import DkMath.NumberTheory.GNPrime
```

Do **not** turn `GNPrimeClosure.lean` itself into the facade. It is a low-level theorem owner and should remain lightweight. Importing the whole Hensel chain from that owner would reverse the conceptual dependency direction.

Do **not** move or rename the existing eight owner files in this checkpoint.

---

# 2. Required facade contents

`DkMath/NumberTheory/GNPrime.lean` should be an import-only public entry point, following the style of `DkMath.NumberTheory.Primitive`.

Use the standard header and explicit logical-order imports:

```lean
import DkMath.NumberTheory.GNPrimeClosure
import DkMath.NumberTheory.GNRepresentationBounds
import DkMath.NumberTheory.GNDegreeFactorization
import DkMath.NumberTheory.GNPrimeTargetResidue
import DkMath.NumberTheory.GNThreeQuadratic
import DkMath.NumberTheory.GNThreePrimeArithmetic
import DkMath.NumberTheory.GNThreeHenselLift
import DkMath.NumberTheory.GNThreeHenselDepth

#print "file: DkMath.NumberTheory.GNPrime"
```

Keep the imports explicit even though some are transitively reachable. The facade is the public contract and should visibly enumerate the GN Prime surface rather than depend on incidental transitive imports.

Add a module docstring with roughly this scope:

```text
GN Prime public entry point

Collects:
- elementary prime closure for x * GN d x u;
- finite positive GN representation bounds;
- composite-degree factorization and prime-degree necessity;
- prime-target residue filters;
- the degree-three discriminant -3 / trace-one quadratic shell;
- primitive cubic prime-divisor arithmetic;
- one-step and arbitrary finite-depth simple-root Hensel lifting.

This public surface is pure NumberTheory. FLT-specific bridges, infinite p-adic completions, and application endpoints remain outside this facade.
```

No theorem duplication, aliases, `open` declarations, or namespace wrappers are needed unless Lean requires them.

---

# 3. Root `DkMath.lean` public import

Update:

```text
lean/dk_math/DkMath.lean
```

In its `-- NumberTheory Module` import block, add exactly one new public import:

```lean
import DkMath.NumberTheory.GNPrime  -- NumberTheory.GNPrime: GN prime closure, prime representations, cubic shell, and finite Hensel-depth API
```

Preferred placement: after the existing generic GN/binomial infrastructure, specifically after

```lean
import DkMath.NumberTheory.WeightedGNBridge
```

and before the Pascal/Petal public imports.

Do not add all eight GNPC owners individually to `DkMath.lean`. The root should depend on the single public facade.

Do not modify unrelated root imports.

---

# 4. Import-cycle and ownership audit

Before finalizing, verify:

1. `GNPrime.lean` imports all eight intended owners.
2. None of the eight owners imports `DkMath.NumberTheory.GNPrime`.
3. `GNPrimeClosure.lean` remains a lightweight owner and does not import the new facade.
4. No declaration has been copied into the facade.
5. The existing owner dependency direction remains unchanged unless a real compile error proves an adjustment is necessary.
6. No FLT, Zsigmondy, Kummer, completion, or application-specific module is newly pulled into an owner merely for public exposure.

Note: `GNPrimeTargetResidue` already intentionally depends on `WeightedGNBridge`; `GNThreeQuadratic` intentionally depends on `TraceOneQuadratic`. These are existing mathematical dependencies, not facade problems.

---

# 5. Documentation update

Update:

```text
lean/dk_math/docs/dev/NumberTheory-GNPrimeClosure-260901-v0/README.md
```

Add a concise public-surface / merge-readiness section recording:

```text
Public entry point:
  import DkMath.NumberTheory.GNPrime

Root availability:
  import DkMath
  transitively imports DkMath.NumberTheory.GNPrime
```

Also record the eight owner modules grouped by layer:

```text
General GN prime layer:
  GNPrimeClosure
  GNRepresentationBounds
  GNDegreeFactorization
  GNPrimeTargetResidue

Degree-three shell/local layer:
  GNThreeQuadratic
  GNThreePrimeArithmetic
  GNThreeHenselLift
  GNThreeHenselDepth
```

State explicitly that application-specific FLT3 integration is intentionally deferred to the next branch/checkpoint and is not part of this merge.

Do not rewrite the historical instruction/report material.

---

# 6. Required validation

Because this checkpoint specifically changes the public import surface, validate the public entries themselves.

Required:

```sh
lake build DkMath.NumberTheory.GNPrime
lake build DkMath
```

The first proves the dedicated facade is closed.
The second proves the repository root public import accepts the new NumberTheory surface.

No full repository build is required beyond these targeted public-surface builds.

Also confirm the new facade source contains no `sorry` or `axiom`. Existing unrelated warnings or research placeholders outside this checkpoint are not part of the mathematical review, but the two required build commands should complete successfully under the branch's normal warning policy.

---

# 7. Public-surface smoke test

Do not add permanent theorem duplication merely to test imports.

If useful during implementation, use a temporary local test file importing only:

```lean
import DkMath.NumberTheory.GNPrime
```

and `#check` representative declarations from every layer, for example:

```lean
#check DkMath.NumberTheory.prime_boundary_mul_GN_iff
#check DkMath.NumberTheory.GNPositiveRepresentation
#check DkMath.NumberTheory.GN_mul_degree
#check DkMath.NumberTheory.GNPositiveRepresentation.prime_degree_constraints
#check DkMath.NumberTheory.GN_three_eq_target_iff_centered_square
#check DkMath.NumberTheory.three_dvd_prime_sub_one_of_square_lift_GN_three
#check DkMath.NumberTheory.existsUnique_GN_three_sqLift_digit
#check DkMath.NumberTheory.existsUnique_GN_three_powLift_digit
```

Remove the temporary smoke-test file before committing unless there is an established repository test owner where such checks belong.

The important acceptance criterion is that all representative declarations are reachable from the single `DkMath.NumberTheory.GNPrime` import.

---

# 8. Merge-readiness report

Create:

```text
lean/dk_math/docs/dev/NumberTheory-GNPrimeClosure-260901-v0/report-009.md
```

Report:

1. final public facade path and import name;
2. exact eight imported owners;
3. root `DkMath.lean` integration point;
4. whether any existing owner import had to change;
5. final dependency summary;
6. representative public declaration reachability;
7. results of:

```text
lake build DkMath.NumberTheory.GNPrime
lake build DkMath
```

8. any newly introduced warnings, `sorry`, or `axiom` (expected: none in the new facade);
9. explicit statement that FLT3 integration remains deferred and the branch is now ready for PR review if all checks pass.

---

# 9. Scope guard

Do not in GNPC-009:

- modify GNPC-001 through GNPC-008 theorem statements for style only;
- move the eight owners into a new directory;
- rename existing modules;
- refactor `GNPrimeClosure.lean` into a facade;
- add FLT3 bridges or alter `hS0_not_sq`;
- add infinite Hensel sequences or p-adic completions;
- modify FLT5 or FLT7;
- open or merge the PR;
- perform unrelated import cleanup across `DkMath.lean`.

This checkpoint is intentionally architectural: expose the already-verified GN Prime theory through one stable NumberTheory public entry and the repository root.

---

# 10. Acceptance criterion

GNPC-009 is complete when a downstream user can write either

```lean
import DkMath.NumberTheory.GNPrime
```

or

```lean
import DkMath
```

and obtain the complete GNPC-001 through GNPC-008 declaration surface without importing any internal GNPC owner manually.

The branch should then be in a clean state for PR review and merge to `develop`, after which FLT3 unconditionalization work can begin from `develop` on a fresh branch.
