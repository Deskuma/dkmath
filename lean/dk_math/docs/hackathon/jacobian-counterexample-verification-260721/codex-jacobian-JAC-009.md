# Instructions

## JAC-009

Implement checkpoint JAC-009 Book of Magic API and the Jacobian
interpretation bridge.

Repository:
Deskuma/dkmath

Branch:
hackathon/breaking-math-jacobian-counterexample

Completed checkpoints:

- JAC-001 through JAC-008
- rational certificate
- complex certificate
- determinant-one normalized certificate
- public import
- axiom audit

The existing Jacobian proof chain is complete.

Do not modify the completed Jacobian definitions or certificate theorems.

Stop after JAC-009.
Do not begin GNFiniteDifference, higher-dimensional padding, Demo,
submission documents, or presentation assets.

## Mathematical goal

Formalize the generic principle:

```text
one Core
+
two distinct certified Gaps over that Core
→
the Gap is not unique
→
the projection that forgets the Gap is not injective
```

Use a dependent Gap family:

```lean
Gap : Core → Type
```

rather than forcing every Core to share one undifferentiated Gap type.

The intended structure follows the Book of Magic design:

```lean
structure GapCrystal where
  core : Core
  gap : Gap core
  certificate : RestoreRel core gap
```

## 1. Unique-gap contract

Create:

```text
lean/dk_math/DkMath/BookOfMagic/UniqueGapContract.lean
```

Use:

```lean
universe u v

namespace DkMath.BookOfMagic

section

variable {Core : Type u}
variable {Gap : Core → Type v}
```

Define:

```lean
def UniqueGap
    (RestoreRel : (core : Core) → Gap core → Prop)
    (core : Core) : Prop :=
  ∃! gap, RestoreRel core gap
```

Prove:

```lean
theorem not_uniqueGap_of_two
    {RestoreRel : (core : Core) → Gap core → Prop}
    {core : Core}
    {gap₁ gap₂ : Gap core}
    (h₁ : RestoreRel core gap₁)
    (h₂ : RestoreRel core gap₂)
    (hne : gap₁ ≠ gap₂) :
    ¬ UniqueGap RestoreRel core := by
  ...
```

Preferred logical proof:

```lean
intro hunique
rcases hunique with ⟨gap, hgap, honly⟩
apply hne
exact (honly gap₁ h₁).trans (honly gap₂ h₂).symm
```

Adjust equality orientation if required by the actual `ExistsUnique`
eliminator.

Also prove the symmetric convenience theorem only if it is genuinely useful.
Do not add a large family of equivalent formulations.

## 2. Gap crystal world

Create:

```text
lean/dk_math/DkMath/BookOfMagic/GapCrystal.lean
```

Import:

```lean
import DkMath.BookOfMagic.UniqueGapContract
```

Define:

```lean
def GapFiber
    (RestoreRel : (core : Core) → Gap core → Prop)
    (core : Core) :=
  { gap : Gap core // RestoreRel core gap }
```

Define the certified Core–Gap object:

```lean
structure GapCrystal
    (Core : Type u)
    (Gap : Core → Type v)
    (RestoreRel : (core : Core) → Gap core → Prop) where
  core : Core
  gap : Gap core
  certificate : RestoreRel core gap
```

Define:

```lean
abbrev CrystalWorld
    (Core : Type u)
    (Gap : Core → Type v)
    (RestoreRel : (core : Core) → Gap core → Prop) :=
  GapCrystal Core Gap RestoreRel
```

Define the forgetting projection:

```lean
def forgetGap
    {Core : Type u}
    {Gap : Core → Type v}
    {RestoreRel : (core : Core) → Gap core → Prop}
    (crystal : CrystalWorld Core Gap RestoreRel) :
    Core :=
  crystal.core
```

Prove:

```lean
theorem forgetGap_notInjective_of_two_gaps
    {Core : Type u}
    {Gap : Core → Type v}
    {RestoreRel : (core : Core) → Gap core → Prop}
    {core : Core}
    {gap₁ gap₂ : Gap core}
    (h₁ : RestoreRel core gap₁)
    (h₂ : RestoreRel core gap₂)
    (hne : gap₁ ≠ gap₂) :
    ¬ Function.Injective
      (forgetGap
        (Core := Core)
        (Gap := Gap)
        (RestoreRel := RestoreRel)) := by
  ...
```

Construct the two crystals:

```lean
let crystal₁ : CrystalWorld Core Gap RestoreRel :=
  ⟨core, gap₁, h₁⟩

let crystal₂ : CrystalWorld Core Gap RestoreRel :=
  ⟨core, gap₂, h₂⟩
```

Then:

```text
forgetGap crystal₁ = forgetGap crystal₂
```

holds definitionally.

Assuming injectivity gives:

```text
crystal₁ = crystal₂
```

from which derive:

```text
gap₁ = gap₂
```

and contradict `hne`.

Because `gap` is a dependent field, use whichever small kernel-checked route
works in current Lean:

```lean
cases hcrystal
rfl
```

or:

```lean
injection hcrystal
```

or a generated structure extensionality theorem.

Do not weaken the dependent Gap family merely to avoid the equality proof.

## 3. Book of Magic public aggregator

Create:

```text
lean/dk_math/DkMath/BookOfMagic.lean
```

Contents:

```lean
import DkMath.BookOfMagic.UniqueGapContract
import DkMath.BookOfMagic.GapCrystal

#print "file: DkMath.BookOfMagic"
```

Do not import Hackathon modules from `DkMath.BookOfMagic`.

The generic Book of Magic layer must remain independent of the Jacobian
counterexample implementation.

## 4. Jacobian interpretation bridge

Create:

```text
lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/GapCrystalBridge.lean
```

Import:

```lean
import DkMath.BookOfMagic
import DkMath.Hackathon.JacobianCounterexample3.Normalized
```

Inside:

```lean
namespace DkMath.Hackathon.JacobianCounterexample3
```

Define the constant Gap family over complex output points:

```lean
abbrev NormalizedGapFamilyC : Point3C → Type :=
  fun _ ↦ Point3C
```

Define the restoration relation:

```lean
def normalizedRestoreRelC
    (core : Point3C)
    (gap : NormalizedGapFamilyC core) : Prop :=
  evalNormalizedCounterexampleC gap = core
```

This means:

```text
core = output point
gap  = input address
certificate = the input evaluates to that output
```

Prove:

```lean
theorem normalizedTargetC_not_uniqueGap :
    ¬ DkMath.BookOfMagic.UniqueGap
      normalizedRestoreRelC
      normalizedTargetC := by
  ...
```

Use:

```lean
DkMath.BookOfMagic.not_uniqueGap_of_two
```

with:

```lean
p0C
p1C
normalized_eval_p0C
normalized_eval_p1C
p0C_ne_p1C
```

Use `simpa [normalizedRestoreRelC, NormalizedGapFamilyC]`
to align the relation if required.

Then prove:

```lean
theorem normalizedForgetGap_notInjective :
    ¬ Function.Injective
      (DkMath.BookOfMagic.forgetGap
        (Core := Point3C)
        (Gap := NormalizedGapFamilyC)
        (RestoreRel := normalizedRestoreRelC)) := by
  ...
```

Use:

```lean
DkMath.BookOfMagic.forgetGap_notInjective_of_two_gaps
```

with the same two collision points and certificates.

Do not reprove the generic theorem inside the Jacobian namespace.

Optional, only if it remains small:

```lean
def normalizedCrystalP0C :
    DkMath.BookOfMagic.CrystalWorld
      Point3C NormalizedGapFamilyC normalizedRestoreRelC

def normalizedCrystalP1C :
    DkMath.BookOfMagic.CrystalWorld
      Point3C NormalizedGapFamilyC normalizedRestoreRelC
```

These named witnesses are not required if the two bridge theorems are already
clear.

Do not add all three points unless doing so materially improves the API.
Two distinct Gaps are sufficient to解除 uniqueness and injectivity.

## 5. Public imports

Modify:

```text
lean/dk_math/DkMath/Hackathon/JacobianCounterexample3.lean
```

Replace the final-leaf import with:

```lean
import DkMath.Hackathon.JacobianCounterexample3.GapCrystalBridge
```

This bridge imports `Normalized`, so the existing public theorem surface
must remain available.

Modify:

```text
lean/dk_math/DkMath.lean
```

Add:

```lean
import DkMath.BookOfMagic
```

near the conceptual library imports, preferably after:

```lean
import DkMath.Petal
```

and before Hackathon modules.

Do not reorder unrelated imports.

## 6. Public checks

Using a temporary check file importing only:

```lean
import DkMath
```

verify:

```lean
#check DkMath.BookOfMagic.UniqueGap
#check DkMath.BookOfMagic.not_uniqueGap_of_two
#check DkMath.BookOfMagic.GapFiber
#check DkMath.BookOfMagic.GapCrystal
#check DkMath.BookOfMagic.CrystalWorld
#check DkMath.BookOfMagic.forgetGap
#check DkMath.BookOfMagic.forgetGap_notInjective_of_two_gaps

#check DkMath.Hackathon.JacobianCounterexample3
  .normalizedTargetC_not_uniqueGap

#check DkMath.Hackathon.JacobianCounterexample3
  .normalizedForgetGap_notInjective

#check DkMath.Hackathon.JacobianCounterexample3
  .normalizedJacobianCounterexampleCertificateC
```

Put each `#check` on one line if required.

Remove the temporary file afterward.

## 7. Verification

Build:

```text
DkMath.BookOfMagic.UniqueGapContract
DkMath.BookOfMagic.GapCrystal
DkMath.BookOfMagic
DkMath.Hackathon.JacobianCounterexample3.GapCrystalBridge
DkMath.Hackathon.JacobianCounterexample3
DkMath
```

Also ensure the existing audit still builds:

```text
DkMathTest.Hackathon.JacobianCounterexample3.CheckAxioms
```

Do not modify the existing mathematical certificate proofs merely to satisfy
the new imports.

Run:

```text
git diff --check
```

## Restrictions

Do not:

- make the generic Book of Magic layer depend on Hackathon code;
- make the existing Jacobian certificate depend logically on the generic API;
- modify the polynomial map;
- modify collision points;
- modify Jacobian or determinant proofs;
- introduce `sorry`;
- introduce axioms;
- use `native_decide`;
- begin GNFiniteDifference;
- begin PrincipalPartCompletion;
- begin higher-dimensional padding;
- create Demo or submission assets.

The dependency direction must be:

```text
BookOfMagic generic API
        ↓
Jacobian GapCrystal interpretation bridge
        ↓
existing completed Jacobian certificate remains unchanged
```

## Report

Report:

1. files created and modified;
2. exact dependent type signatures;
3. proof route for `not_uniqueGap_of_two`;
4. proof route for dependent crystal inequality;
5. public API names;
6. Jacobian bridge definitions;
7. proof route for `normalizedTargetC_not_uniqueGap`;
8. proof route for `normalizedForgetGap_notInjective`;
9. whether the existing certificate theorems remained byte-for-byte unchanged;
10. build results and warnings;
11. existing axiom-audit result;
12. `git diff --check` result;
13. confirmation that JAC-010 and later checkpoints were not started.

Stop after JAC-009 and wait for review.
