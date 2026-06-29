# Codex instructions

Target:
DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
DkMath.Analysis.DkReal.SemanticCF2DSync or a new small scale-sync module

Goal:
Camp at the completed shifted cyclic path-packaging checkpoint, then return to the main refinement line through finite scale synchronization. Do not add DkPathPrototype yet. Do not add Euclidean angle reading yet.

Current status:
The shifted cyclic path-packaging comparison is closed.

Implemented public checkpoint:

```lean id="n8vckg"
shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_final
```

Meaning:

```text id="jk02de"
endpoint-cast observed quotient closed path
  =
existing fixed-q2 finite four-level path
```

This is a Mathlib `Path` packaging theorem using `Path.map`, `Path.trans`, `Path.cast`, and seam proof irrelevance. It is not a Euclidean reading.

Task A:
Preserve No.136 as a documentation cleanup and checkpoint stabilization commit.

Do not introduce a production `DkPathPrototype` yet.

Prototype trigger:

```text id="h068k5"
a new downstream proof repeats map/cast/trans/seam normalization
```

Graduation rule:

```text id="drlp8u"
keep the prototype only if it shortens a real proof while preserving theorem meaning
```

Task B:
Return to the main scale/refinement line.

Create a small finite synchronization layer if no suitable module exists.

Candidate module name:

```text id="nva54l"
DkMath.Analysis.DkReal.SemanticCF2DSync
```

or another nearby namespace consistent with the existing file layout.

Task C:
Start with natural-number scale synchronization only.

Do not use geometry. Do not use angle terminology.

Candidate definitions:

```lean id="zuc1r2"
def SyncLength (k l : ℕ) : ℕ :=
  Nat.lcm k l
```

```lean id="lk4drz"
def SyncLiftLeft (k l : ℕ) : ℕ :=
  Nat.lcm k l / k
```

```lean id="in5re5"
def SyncLiftRight (k l : ℕ) : ℕ :=
  Nat.lcm k l / l
```

Use assumptions `0 < k` and `0 < l` in theorems. Do not try to make zero a normal scale.

Task D:
Prove the basic synchronization theorems.

Candidate theorem shapes:

```lean id="a3pj4b"
theorem mul_syncLiftLeft_eq_syncLength
    {k l : ℕ} (hk : 0 < k) :
    k * SyncLiftLeft k l = SyncLength k l
```

```lean id="tfdjye"
theorem mul_syncLiftRight_eq_syncLength
    {k l : ℕ} (hl : 0 < l) :
    l * SyncLiftRight k l = SyncLength k l
```

Expected proof:
Use `Nat.dvd_lcm_left`, `Nat.dvd_lcm_right`, and division lemmas for natural numbers.

Task E:
Add the coprime specialization.

Candidate theorem shapes:

```lean id="er2qnf"
theorem syncLength_eq_mul_of_coprime
    {k l : ℕ} (hcop : Nat.Coprime k l) :
    SyncLength k l = k * l
```

```lean id="eb7jxn"
theorem syncLiftLeft_eq_right_of_coprime
    {k l : ℕ} (hk : 0 < k) (hcop : Nat.Coprime k l) :
    SyncLiftLeft k l = l
```

```lean id="bpjodw"
theorem syncLiftRight_eq_left_of_coprime
    {k l : ℕ} (hl : 0 < l) (hcop : Nat.Coprime k l) :
    SyncLiftRight k l = k
```

Task F:
Add a short documentation note explaining the design:

```text id="dlpcpe"
Different 1/k scales are not compared by forcing one base cycle against
another. They are lifted to a finite synchronization cycle of length lcm(k,l).
For coprime scales, the synchronization length is k*l, and each scale's lift
count is the other scale's denominator.
```

Task G:
One-step-ahead inference:
After the natural-number sync layer is stable, introduce star-scale predicates.

Candidate definitions:

```lean id="cc5g43"
def IsScale (k : ℕ) (r : UnitKernel α) : Prop :=
  starPow k r = one
```

```lean id="qsesxj"
def IsPrimitiveScale (k : ℕ) (r : UnitKernel α) : Prop :=
  IsScale k r ∧ ∀ n, 0 < n → n < k → starPow n r ≠ one
```

Do not implement these in the first sync cleanup unless the natural-number layer is already clean and short.

Task H:
Zero policy:
Do not treat `0` as an ordinary scale. Record it as a degenerate orbit case later.

Suggested documentation wording:

```text id="sylgcz"
Zero collapses every scale orbit to a constant trace, so it should be handled
as a degenerate/singular case, not as a normal finite scale.
```

Task I:
Infinity policy:
Do not implement infinite synchronization yet. Record the future direction:

```text id="jeyk66"
finite scale families synchronize by lcm;
the infinite prime family has no finite common synchronization length.
```

Task J:
Do not add Euclidean one-eighth or angle reading yet.

The current next step is synchronization, not geometry.

Required checks:

```text id="k04d7e"
lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
lake build DkMath.Analysis.DkReal
git diff --check
```
