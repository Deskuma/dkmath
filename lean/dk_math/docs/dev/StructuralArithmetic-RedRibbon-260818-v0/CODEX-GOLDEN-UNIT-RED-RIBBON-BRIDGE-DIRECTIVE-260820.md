# Codex autonomous implementation directive — Golden Unit / Red Ribbon Bridge

Date: 2026-08-20
Repository: `Deskuma/dkmath`
Expected working branch: `wip/structural-arithmetic-red-ribbon-260818-v0`
Primary integration area: `lean/dk_math/DkMath/NumberTheory/StructuralArithmetic/`
Target phase: Phase G — golden-unit / fifth-power Red Ribbon bridge

## 0. Mission

Continue the Structural Arithmetic / Red Ribbon integration by connecting the already-proved FLT5 golden-unit classification to the StructuralArithmetic vocabulary **without changing the completed FLT5 proof route** and without falsely identifying different kinds of “mod 5” structure.

The load-bearing mathematical pattern is already present in the repository:

```text
Golden unit epsilon
        ↓ existing theorem
∃ i : Fin 5, ∃ delta : GoldenInt,
  epsilon = phi^i * delta^5
        ↓
visible representative: phi^i
invisible fifth-power gauge factor: delta^5
```

The new phase should make this pattern explicit as a StructuralArithmetic bridge and prove the basic Red Ribbon invariance law:

```text
if x has fifth-power sector i,
then x * eta^5 has the same fifth-power sector i.
```

This is an autonomous Lean implementation task. Do not treat this document as a fixed patch recipe. First inspect the actual branch state, existing theorem signatures, current imports, Mathlib interfaces, and successful build baseline. Then choose the smallest mathematically correct bridge that closes the gap.

The goal is **integration and interpretation of existing certified arithmetic**, not a new proof of golden-unit classification and not a generic quotient-group project.

---

## 1. Repository-first preflight — mandatory

Before editing, inspect the actual worktree and branch state. Repository code and successful Lean builds are the source of truth; documentation is secondary.

Run at minimum:

```bash
git status -sb
git branch --show-current
git rev-parse HEAD
git log --oneline --decorate -20
git merge-base HEAD develop
git diff --stat develop...HEAD
```

If unrelated user changes exist, do not reset, stash, overwrite, or stage them. Restrict edits to the StructuralArithmetic bridge and directly required documentation unless a tiny dependency-local theorem is genuinely necessary.

Read the complete current StructuralArithmetic tower:

```text
DkMath/NumberTheory/StructuralArithmetic.lean
DkMath/NumberTheory/StructuralArithmetic/PowerGauge.lean
DkMath/NumberTheory/StructuralArithmetic/PrimeCoordinates.lean
DkMath/NumberTheory/StructuralArithmetic/InterPeriod.lean
DkMath/NumberTheory/StructuralArithmetic/KUSObservation.lean
DkMath/NumberTheory/StructuralArithmetic/PrimitiveDirection.lean
DkMath/NumberTheory/StructuralArithmetic/FinitePrimeEscapeBridge.lean
DkMath/NumberTheory/StructuralArithmetic/GNBridge.lean

docs/dev/StructuralArithmetic-RedRibbon-260818-v0/README.md
docs/dev/StructuralArithmetic-RedRibbon-260818-v0/GN-GN5-STRUCTURAL-BRIDGE-IMPLEMENTATION-REPORT-260820.md
```

Read the relevant FLT5 golden-order implementation in full, especially:

```text
DkMath/FLT/Five/GoldenOrder.lean
DkMath/FLT/Five/GoldenDivisibility.lean
DkMath/FLT/Five/GoldenCoprimeFactor.lean
DkMath/FLT/Five/SignedGoldenFifthPower.lean
DkMath/FLT/Five/GoldenFifthPowerCoordinates.lean
DkMath/FLT/Five/SignedGoldenUnitClasses.lean
DkMath/FLT/Five/GoldenUnitClassification.lean
DkMath/FLT/Five/SignedGoldenSectorArithmetic.lean
DkMath/FLT/Five/Main.lean
```

Read the historical Red Ribbon contract for terminology/provenance, but do not use it instead of current Lean source:

```text
DkMath/FLT/Five/docs/impl-flt5-cp-004k-a-red-ribbon-unit-classification.txt
```

Search before introducing any new definition or theorem:

```bash
rg -n "GoldenUnitFifthClass|GoldenUnitClassesModFifth|goldenUnitClassesModFifth" DkMath/FLT/Five
rg -n "signedGoldenFiniteUnitSectorCore|unitSector|fifth.*sector|sector.*fifth" DkMath/FLT/Five
rg -n "goldenPow.*5|mul_pow|GoldenUnit.*pow|goldenUnit_mul|goldenUnit_pow" DkMath/FLT/Five
rg -n "SamePowerSector|SamePowerStructure|projectExponent|projectPrimeCoordinates" DkMath/NumberTheory/StructuralArithmetic
rg -n "Quotient|Setoid|Subgroup|pow.*quotient|fifth.*class" DkMath/NumberTheory DkMath/FLT/Five
```

Inspect exact theorem signatures in the installed Mathlib / current DkMath. Do not guess theorem names from memory or from old reports.

Baseline-build the current Phase A-F tower before editing:

```bash
lake build DkMath.NumberTheory.StructuralArithmetic.PowerGauge
lake build DkMath.NumberTheory.StructuralArithmetic.PrimeCoordinates
lake build DkMath.NumberTheory.StructuralArithmetic.InterPeriod
lake build DkMath.NumberTheory.StructuralArithmetic.KUSObservation
lake build DkMath.NumberTheory.StructuralArithmetic.PrimitiveDirection
lake build DkMath.NumberTheory.StructuralArithmetic.FinitePrimeEscapeBridge
lake build DkMath.NumberTheory.StructuralArithmetic.GNBridge
lake build DkMath.NumberTheory.StructuralArithmetic
```

Also baseline-build the existing golden-unit classification module before changing anything:

```bash
lake build DkMath.FLT.Five.GoldenUnitClassification
```

If the baseline fails, diagnose and report the blocker rather than building Phase G on a broken state.

---

## 2. Certified starting point — do not reprove it

The current repository already proves the core golden-unit classification.

The semantic contract is:

```lean
abbrev GoldenUnitClassesModFifth : Prop :=
  ∀ epsilon : GoldenInt,
    GoldenUnit epsilon →
    ∃ i : Fin 5, ∃ delta : GoldenInt,
      epsilon = goldenMul
        (goldenPow goldenPhi i.val)
        (goldenPow delta 5)
```

and the current implementation provides:

```lean
def GoldenUnitFifthClass (x : GoldenInt) : Prop :=
  ∃ i : Fin 5, ∃ delta : GoldenInt,
    x = goldenMul
      (goldenPow goldenPhi i.val)
      (goldenPow delta 5)

theorem goldenUnitFifthClass_of_unit ...

theorem goldenUnitClassesModFifth : GoldenUnitClassesModFifth
```

The FLT5 receiver already includes:

```lean
SignedGoldenFiniteUnitSectorCore
signedGoldenFiniteUnitSectorCore_of_unitClasses
signedGoldenFiniteUnitSectorCore
```

Do not duplicate the coordinate descent proving these results.

Do not edit `GoldenUnitClassification.lean` merely to move declarations into a new namespace.

Do not re-run the historical cp-004k proof as new Phase G mathematics.

The Phase G bridge should **consume** these declarations.

---

## 3. Critical semantic boundary — three different “five” structures

This phase must preserve the distinction between three separate constructions.

### 3.1 Natural prime-exponent PowerGauge

StructuralArithmetic Phase A/B observes natural prime valuations by

```text
v_p(n) ↦ v_p(n) % 5
```

and proves multiplication by a fifth power changes valuations by multiples of five, hence is invisible after projection.

This lives in a coordinate space indexed by ordinary prime numbers.

### 3.2 Golden-unit classes modulo fifth powers

FLT5 classifies a golden unit as

```text
epsilon = phi^i * delta^5
```

with `i : Fin 5`.

This lives in the multiplicative unit structure of the golden order.

### 3.3 Ordinary additive congruence modulo five

`FLT.Five.GN5` also has coefficient identities such as

```text
GN5 g y = g^4 + 5 * (...)
```

which imply an ordinary additive congruence modulo five.

This is a third construction.

### Mandatory rule

Do **not** prove or document any theorem equating these three merely because all contain the numeral `5`.

The common structural slogan is weaker and precise:

> a whole fifth-power gauge factor is observationally ignored by the corresponding fifth-power-class observer.

Phase G should formalize this slogan for the golden-unit side while retaining the already separate natural valuation implementation.

---

## 4. Do not invent canonical sector uniqueness

The current theorem proves **existence** of a representative sector:

```text
∃ i : Fin 5, ∃ delta, epsilon = phi^i * delta^5
```

It does not, by itself, expose a theorem that the `i : Fin 5` witness is unique.

Therefore Phase G must not silently introduce:

```lean
sectorOf : GoldenInt → Fin 5
```

or a theorem of the form:

```text
sector i x ∧ sector j x → i = j
```

unless uniqueness is independently proved from existing certified APIs during repository inspection and can be added cheaply without opening a new algebraic-number-theory project.

Default design: keep the observer **witness-valued / relation-valued**, not choice-valued.

Do not use `Classical.choose` to manufacture a canonical sector and then call it mathematically unique.

---

## 5. Recommended minimal bridge representation

Investigate current names first. If no equivalent already exists, a small StructuralArithmetic-specific predicate is appropriate.

A candidate shape is:

```lean
def GoldenFifthSector (i : Fin 5) (x : GoldenInt) : Prop :=
  ∃ delta : GoldenInt,
    x = goldenMul
      (goldenPow goldenPhi i.val)
      (goldenPow delta 5)
```

Names are suggestions; choose repository-consistent names after conflict search.

This predicate is intentionally relation-valued:

```text
GoldenFifthSector i x
```

means only that `x` admits representative `phi^i` after absorbing a fifth-power factor.

It should not claim that `x` is itself a unit unless the theorem using it has that hypothesis.

Possible module target:

```text
DkMath.NumberTheory.StructuralArithmetic.GoldenUnitBridge
```

Prefer one focused bridge module.

Do not create a large new `GoldenQuotient` hierarchy unless repository inspection reveals an already existing abstraction that makes the implementation strictly smaller.

---

## 6. Required bridge A — expose the existing classification through the new sector relation

If `GoldenFifthSector` or equivalent is introduced, connect it exactly to the existing FLT5 predicate.

A preferred theorem shape is:

```lean
theorem goldenUnitFifthClass_iff_exists_sector
    {x : GoldenInt} :
    GoldenUnitFifthClass x ↔
      ∃ i : Fin 5, GoldenFifthSector i x
```

This should be a thin theorem, ideally definitional unpacking/repacking.

Then consume the already-proved classification:

```lean
theorem goldenUnit_has_fifthSector
    {epsilon : GoldenInt}
    (hUnit : GoldenUnit epsilon) :
    ∃ i : Fin 5, GoldenFifthSector i epsilon
```

The proof must reuse one of:

```text
goldenUnitFifthClass_of_unit
goldenUnitClassesModFifth
```

Do not reproduce the descent.

This theorem is the primary “observer exists” bridge for golden units.

---

## 7. Required bridge B — Red Ribbon fifth-power gauge invariance

This is the load-bearing new theorem of Phase G.

For a fixed visible sector `i`, multiplying by a complete fifth power should preserve the same sector witness.

A preferred theorem shape is:

```lean
theorem GoldenFifthSector.mul_fifthPower
    {i : Fin 5} {x : GoldenInt}
    (hx : GoldenFifthSector i x)
    (eta : GoldenInt) :
    GoldenFifthSector i
      (goldenMul x (goldenPow eta 5))
```

or an equivalent namespace/theorem name.

Expected mathematical proof:

```text
x = phi^i * delta^5

x * eta^5
  = phi^i * delta^5 * eta^5
  = phi^i * (delta * eta)^5
```

Use existing `goldenMul` / `goldenPow` simp bridges or ordinary ring multiplication as appropriate. Prefer `mul_pow` and existing golden-operation equivalences over coordinate expansion.

This theorem is the precise golden-order Red Ribbon law:

```text
visible sector stays i
whole fifth-power gauge factor changes only the hidden witness
```

### Optional symmetric removal law

If the existing `GoldenUnit` API exposes inverses cheaply, it is useful but not mandatory to prove that multiplying by a **unit** fifth power can also be reversed while staying in the same sector.

Do not spend the phase constructing a general inverse theory if this is not immediate.

Forward fifth-power absorption is mandatory; symmetric quotient equivalence is optional.

---

## 8. Required bridge C — representatives themselves occupy their named sectors

Prove a small base theorem showing that every visible representative is in its own sector, for example:

```lean
@[simp] theorem goldenPhiPow_mem_fifthSector (i : Fin 5) :
    GoldenFifthSector i (goldenPow goldenPhi i.val)
```

with gauge witness `goldenOne`.

Adapt to exact simp lemmas for `goldenPow goldenOne 5`.

This theorem is useful for reading the five visible representatives as explicit sector anchors:

```text
1, phi, phi^2, phi^3, phi^4
```

Do not call them geometric angular sectors. Existing FLT5 documentation explicitly treats them as algebraic unit classes.

---

## 9. Required concrete bridge D — connect the existing FLT5 packet sector theorem

Phase G must not stop at a free-standing predicate unused by existing DkMath.

The repository already proves that every stripped golden packet is reducible to one of five sectors through:

```text
SignedGoldenFiniteUnitSectorCore
signedGoldenFiniteUnitSectorCore_of_unitClasses
goldenUnitClassesModFifth
signedGoldenFiniteUnitSectorCore
```

Add a thin StructuralArithmetic theorem or equivalent bridge showing that the existing packet theorem yields the new sector relation for `p.beta`.

A satisfactory theorem shape is approximately:

```lean
theorem signedGoldenPacket_has_fifthSector
    {u v w : ℕ}
    (p : SignedGoldenRamifierStrippedPacket u v w) :
    ∃ i : Fin 5, GoldenFifthSector i p.beta
```

The proof should reuse the existing `signedGoldenFiniteUnitSectorCore` theorem if dependency direction is acceptable, or the lighter

```text
signedGoldenFiniteUnitSectorCore_of_unitClasses goldenUnitClassesModFifth
```

if importing `Main.lean` would create an undesirable dependency.

Prefer the smallest dependency-safe route.

Do not reprove `p.beta = phi^i * gamma^5` coordinate arithmetic.

This concrete packet theorem is mandatory because it proves the new bridge interprets a real FLT5 object instead of creating an isolated abstraction.

---

## 10. Preferred theorem — gauge absorption directly on packet witness

If it is cheap after Bridge D, demonstrate that a packet sector witness is stable under an extra fifth-power factor:

```text
p.beta has sector i
→ p.beta * eta^5 has sector i
```

This may simply be an application of the generic Red Ribbon theorem and need not be packet-specific if theorem discoverability is already good.

Do not add duplicate wrappers with no additional semantic value.

---

## 11. Relation to existing natural PowerGauge — documentation bridge, not false equality

The README should explain the common pattern as two separate implementations:

```text
Natural valuation side
----------------------
raw coordinate: v_p(n)
gauge motion:   + 5*k
observer:       mod 5
invariance:     n * a^5 has same projected prime-exponent coordinates

Golden-unit side
----------------
raw object:     epsilon in GoldenInt unit structure
gauge motion:   multiply by delta^5
observer:       existence of representative phi^i, i : Fin 5
invariance:     sector witness i survives multiplication by eta^5
```

The bridge is the **power-gauge invariance pattern**.

Do not claim there is a literal type-level equality between `Fin 5` golden sectors and the whole function-valued prime-coordinate projection:

```text
PrimeIndex → Nat
```

They have different source objects and different observer codomains.

A later generic abstraction may unify them if justified, but Phase G should establish the two concrete certified instances first.

---

## 12. Do not introduce a generic quotient-group abstraction unless it is clearly already available

It is mathematically natural to consider a multiplicative quotient such as

```text
U / U^5
```

for a commutative unit group. That abstraction may eventually be useful.

However it is **not** the default Phase G task.

Do not expand this checkpoint into:

- a new generic category of power quotients;
- a custom `Quotient`/`Setoid` hierarchy;
- a general theorem for all commutative groups;
- a refactor of `GoldenInt` into an algebraic number field;
- a migration to `Zsqrtd 5` or another representation.

Only use an existing generic quotient API if repository inspection shows that the required bridge becomes shorter and clearer than the explicit witness relation.

The acceptance target is the concrete Red Ribbon theorem, not maximal abstraction.

---

## 13. Preserve the completed FLT5 proof tower

Phase G is an observational/integration bridge above already-certified FLT5 arithmetic.

Do not modify the logical route of:

```text
Golden unit classification
→ finite unit sectors
→ zero-sector arithmetic
→ FLT5 closure
```

Do not change:

```text
flt5Target
fermatFive_no_positive_solution
```

unless a trivial import-only change is absolutely required, which should normally be unnecessary.

The new module may import the smallest required FLT5 module and expose StructuralArithmetic interpretations.

Avoid importing all of `DkMath.FLT.Five.Main` if lighter dependencies suffice.

---

## 14. Public aggregate and documentation

When the bridge is stable:

1. Add the new module to:

```text
DkMath.NumberTheory.StructuralArithmetic
```

2. Update its module docstring so Phase G is described accurately.

3. Update:

```text
docs/dev/StructuralArithmetic-RedRibbon-260818-v0/README.md
```

The README currently contains historical status text that may lag the Phase F implementation. Treat actual code/build state as authoritative and correct stale status lines.

Mark Phase G complete only after build verification.

4. Add an implementation report such as:

```text
docs/dev/StructuralArithmetic-RedRibbon-260818-v0/GOLDEN-UNIT-RED-RIBBON-BRIDGE-IMPLEMENTATION-REPORT-260820.md
```

The report should include:

- baseline HEAD;
- files inspected;
- chosen representation and why;
- theorem list;
- which existing FLT5 declarations were reused;
- explicit statement that sector uniqueness was **not** claimed unless actually proved;
- explicit distinction between golden fifth-power classes, prime-exponent period 5, and additive mod 5;
- build commands/results;
- axiom audit;
- next smallest structural gap.

---

## 15. Required build / verification

At minimum run:

```bash
lake build DkMath.NumberTheory.StructuralArithmetic.GoldenUnitBridge
lake build DkMath.NumberTheory.StructuralArithmetic
```

Also rebuild any directly touched FLT5 module if one was modified.

Run:

```bash
git diff --check
```

Search new/modified Phase G source for forbidden placeholders:

```bash
rg -n "\bsorry\b|\badmit\b|\baxiom\b|\bunsafe\b" \
  DkMath/NumberTheory/StructuralArithmetic/GoldenUnitBridge.lean
```

Existing warnings in transitive dependencies do not count as newly introduced placeholders, but record them accurately.

Use `#print axioms` on the key public theorems, especially:

```text
goldenUnit_has_fifthSector
GoldenFifthSector.mul_fifthPower
signedGoldenPacket_has_fifthSector
```

(adapt names to actual implementation).

No new project-specific axiom is allowed.

Every new public declaration must have a Lean docstring describing its mathematical role and important scope boundary.

---

## 16. Anti-maze rules

This project has already completed Phases A-F. Preserve the integration trajectory.

Before every new helper, ask:

```text
What existing theorem requires this helper?
What cross-module bridge becomes possible after it?
```

Do not count as progress:

- introducing a quotient abstraction with no concrete FLT5 receiver;
- proving coordinate identities already present in `GoldenFifthPowerCoordinates`;
- reproving `goldenUnitClassesModFifth`;
- creating a canonical sector selector without uniqueness;
- proving more facts about `phi` unrelated to fifth-power gauge invariance;
- modifying the FLT5 zero-sector descent;
- conflating additive `mod 5` with multiplicative fifth-power classes;
- generalizing from exponent five to arbitrary exponents before the concrete bridge is complete.

One load-bearing checkpoint at a time.

The Phase G checkpoint is complete when this chain is theorem-level and build-checked:

```text
existing GoldenUnit classification
        ↓
relation-valued visible sector witness
        ↓
whole fifth-power multiplication preserves that witness
        ↓
existing signed golden packet obtains such a witness
        ↓
public StructuralArithmetic aggregate
```

---

## 17. Suggested implementation order

A practical sequence is:

### G1 — preflight and API map

Confirm exact definitions and dependency direction.

### G2 — minimal sector relation

Implement `GoldenFifthSector` or an equivalent thin wrapper.

### G3 — existing classification bridge

Prove equivalence with `GoldenUnitFifthClass` and `goldenUnit_has_fifthSector`.

### G4 — Red Ribbon invariance

Prove fifth-power multiplication preserves a fixed sector witness.

### G5 — representative/base theorem

Show `phi^i` is in sector `i`.

### G6 — concrete FLT5 packet bridge

Reuse `signedGoldenFiniteUnitSectorCore` or its lighter provider to obtain a sector witness for `p.beta`.

### G7 — aggregate/docs/audit

Build, update documentation, inspect axioms, commit.

If repository inspection reveals a simpler order, use it and explain the decision in the implementation report.

---

## 18. Commit / push discipline

After successful focused builds and `git diff --check`:

- inspect `git status` and `git diff`;
- stage only files belonging to Phase G;
- do not stage unrelated user work;
- commit with a concise message describing the golden-unit Red Ribbon bridge;
- push to the current branch:

```text
wip/structural-arithmetic-red-ribbon-260818-v0
```

Do not merge to `develop`.
Do not create or merge a PR unless explicitly requested separately.

---

## 19. Expected end-state

A successful Phase G should make the following distinction and connection explicit:

```text
Natural prime-coordinate Red Ribbon
  n * a^5
    → valuations move by 5*k
    → period-5 projection unchanged

Golden-unit Red Ribbon
  epsilon * eta^5
    → hidden fifth-power witness changes
    → visible phi^i sector witness unchanged
```

Both are instances of the same structural idea:

```text
complete power-gauge motion is invisible to the chosen observer
```

but they remain separate mathematical implementations with separate source types and observer types.

Do not claim more than the Lean theorems establish.

After Phase G, inspect the now-integrated A-G tower and identify the next **smallest load-bearing gap** rather than automatically starting a large generic abstraction. Candidate future directions include DHNT structure-preserving real exponent scaling or a deliberately minimal generic power-gauge interface, but the actual repository state should decide the next step.
