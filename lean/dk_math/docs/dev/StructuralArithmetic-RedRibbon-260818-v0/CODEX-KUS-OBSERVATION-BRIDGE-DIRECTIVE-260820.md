# Codex autonomous implementation directive — KUS Observation Bridge

Date: 2026-08-20
Repository: `Deskuma/dkmath`
Expected working branch: `wip/structural-arithmetic-red-ribbon-260818-v0`
Integration area: `lean/dk_math/DkMath/NumberTheory/StructuralArithmetic/`
Target phase: Phase D — explicit KUS observation bridge

## 0. Mission

Continue the Structural Arithmetic / Red Ribbon integration by implementing the next load-bearing bridge between the existing KUS preservation layer and the StructuralArithmetic projection layer.

This is an autonomous implementation task. Do not treat this document as a fixed patch recipe. First inspect the current repository state, confirm what is already implemented and build-checked, infer the smallest mathematically correct API that closes the next gap, then implement and verify it.

The central architectural distinction must remain explicit:

```text
KUS preserves a raw typed source/support.
ObservationSpec interprets that source as structural coordinates.
PowerGauge deliberately forgets periodic information from those coordinates.
```

Do not make arbitrary KUS blueprints intrinsically prime-coordinate systems. Do not make `ScaleSpec` automatically observation-preserving. Any semantic compatibility between transport and observation must be stated as an explicit hypothesis/specification and proved from that hypothesis.

The implementation must connect to at least one existing DkMath concrete source or existing KUS operation so that this phase does not stop at an unused abstraction.

---

## 1. Repository-first preflight — mandatory

Before editing, inspect the actual worktree and repository state. The repository and successful Lean builds are the source of truth; phase labels in documents are secondary.

Run at minimum:

```bash
git status -sb
git branch --show-current
git rev-parse HEAD
git log --oneline --decorate -20
git merge-base HEAD develop
git diff --stat develop...HEAD
```

If unrelated user changes exist, do not reset, stash, overwrite, or stage them. Restrict edits to the StructuralArithmetic / directly required KUS bridge scope.

Read the current versions of:

```text
DkMath/NumberTheory/StructuralArithmetic.lean
DkMath/NumberTheory/StructuralArithmetic/PowerGauge.lean
DkMath/NumberTheory/StructuralArithmetic/PrimeCoordinates.lean
DkMath/NumberTheory/StructuralArithmetic/InterPeriod.lean

docs/dev/StructuralArithmetic-RedRibbon-260818-v0/README.md
docs/dev/StructuralArithmetic-RedRibbon-260818-v0/IMPLEMENTATION-REPORT-260820.md

DkMath/KUS/README.md
DkMath/KUS/Coeff.lean
DkMath/KUS/Scale.lean
DkMath/KUS/Transport.lean
DkMath/KUS/docs/KUS-transport-design-spec.md
DkMath/KUS/docs/KUS-bridge-design-spec.md
```

Search before inventing names or duplicating an existing abstraction:

```bash
rg -n "ObservationSpec|observeGKUS|observeKUS|observer|observation|coordinates" DkMath
rg -n "GKUS|extract_g|GSameSupport|ScaleSpec|scaleUS|scaleGKUS|HarmonizeSpec|DecodeSpec" DkMath/KUS
rg -n "projectCoordinates|SamePowerStructure|projectPrimeCoordinates|InterPeriod" DkMath/NumberTheory/StructuralArithmetic
rg -n "BlueprintFamily|def US|structure US|toUS|extract" DkMath/KUS
rg -n "DHNT|Dynamic|Harmon|log.*base|scale" DkMath/DHNT DkMath/KUS DkMath/Analysis 2>/dev/null || true
```

Inspect full definitions you intend to reuse, not only search snippets.

Baseline build the existing StructuralArithmetic tower before editing:

```bash
lake build DkMath.NumberTheory.StructuralArithmetic.PowerGauge
lake build DkMath.NumberTheory.StructuralArithmetic.PrimeCoordinates
lake build DkMath.NumberTheory.StructuralArithmetic.InterPeriod
lake build DkMath.NumberTheory.StructuralArithmetic
```

If baseline fails, diagnose the actual repository state before implementing Phase D.

---

## 2. Current mathematical checkpoint that must be preserved

Phases A-C are already implemented and locally build-checked.

### 2.1 Raw and projected exponent structures

`PowerGauge` provides a raw coordinate view and period observation:

```text
projectExponent d n = n % d
projectCoordinates d v = fun i => v i % d
```

with theorem-level boundary behavior:

```text
period 0 : raw / identity observation
period 1 : total coordinate collapse
period d : adding d*k is observationally invisible
```

### 2.2 Ordinary prime-coordinate specialization

`PrimeCoordinates` provides:

```text
primeExponentCoordinates n : PrimeIndex -> Nat
projectPrimeCoordinates d n
```

and proves the power-gauge law:

```text
v_p(n * a^d) = v_p(n) + d * v_p(a)
projectPrimeCoordinates d (n * a^d) = projectPrimeCoordinates d n
```

under the existing nonzero hypotheses.

### 2.3 Inter-period forgetting

`InterPeriod` proves, for `m ∣ d`:

```text
projectExponent m (projectExponent d n) = projectExponent m n
projectCoordinates m (projectCoordinates d v) = projectCoordinates m v
```

and descends `SamePowerSector` / `SamePowerStructure`, with prime-coordinate specializations.

Do not weaken, rename, or duplicate these public contracts unless a build issue requires a narrowly justified compatibility alias.

---

## 3. KUS facts that must guide the design

KUS represents structural state independently from the visible coefficient. In current code, inspect the exact definitions, but the conceptual shape is:

```text
GKUS C U Blueprint
  coeff
  unit
  blueprint
```

and:

```text
extract_g : GKUS C U Blueprint -> US U Blueprint
```

returns the retained support/source.

`ScaleSpec` transports unit and dependent blueprint data:

```text
mapUnit
mapBlueprint
scaleUS
scaleGKUS
```

while the visible coefficient is preserved by the current transport implementation.

This does **not** imply that any structural observation extracted from the blueprint is invariant under `ScaleSpec`.

A blueprint may encode information in a representation-dependent way. Therefore the next bridge must distinguish:

```text
source preservation
semantic observation
observation compatibility under transport
period projection
```

Do not collapse those four concepts into one definition.

---

## 4. Target architecture

The intended architecture is approximately:

```text
                raw GKUS x
                    |
                    | extract_g
                    v
              raw KUS support
                    |
                    | explicit observer/spec
                    v
            raw coordinates : ι -> Nat
                    |
                    | projectCoordinates d
                    v
           period-d observable view
                    |
                    | m | d
                    v
           period-m coarser view
```

Separately, KUS transport acts on the raw source:

```text
raw support --ScaleSpec--> transported raw support
```

Observation may commute with that transport only when an explicit compatibility law says so.

The bridge must preserve access to the raw KUS source. A projected coordinate function alone is not an adequate replacement for the source.

---

## 5. Preferred minimal abstraction — investigate, do not copy blindly

A likely minimal shape is an explicit observer from KUS support to nonnegative structural coordinates, for example:

```lean
structure ObservationSpec
    (U : Type u)
    (Blueprint : BlueprintFamily U)
    (ι : Type v) where
  coordinates : US U Blueprint -> ι -> Nat
```

or an equivalent API discovered to fit the existing code better.

A corresponding observation of `GKUS` could be defined through `extract_g`, conceptually:

```lean
def rawObservation
    (ω : ObservationSpec U Blueprint ι)
    (x : GKUS C U Blueprint) : ι -> Nat :=
  ω.coordinates (extract_g x)


def observePeriod
    (ω : ObservationSpec U Blueprint ι)
    (d : Nat)
    (x : GKUS C U Blueprint) : ι -> Nat :=
  projectCoordinates d (rawObservation ω x)
```

These names and signatures are only design candidates. Inspect repository conventions and choose names that integrate naturally.

The implementation should establish the obvious source/projection laws, preferably as public theorems with Lean docstrings:

```text
period 0 observation = raw observation
period 1 observation = zero coordinate function
period d observation is projectCoordinates d of raw observation
inter-period coarsening agrees with InterPeriod
```

Do not add theorem aliases merely to inflate API surface; each public theorem should serve an actual bridge contract.

---

## 6. ScaleSpec compatibility — explicit law, not an axiom hidden in the observer

Investigate the cleanest way to express that two observers are compatible with a KUS `ScaleSpec`.

A candidate mathematical contract is:

```text
ω_target.coordinates (scaleUS σ s)
  = ω_source.coordinates s
```

for every raw support `s`.

This may be represented as a `Prop`, structure field, named predicate, or a compatibility structure depending on current DkMath style.

Example conceptual form only:

```lean
def ObservationCompatible
    (ω₁ : ObservationSpec U Blueprint ι)
    (ω₂ : ObservationSpec V Blueprint' ι)
    (σ : ScaleSpec U Blueprint V Blueprint') : Prop :=
  ∀ s,
    ω₂.coordinates (ScaleSpec.scaleUS σ s) = ω₁.coordinates s
```

If such compatibility holds, prove the corresponding `GKUS` observation theorem, conceptually:

```text
rawObservation ω₂ (scaleGKUS σ x)
  = rawObservation ω₁ x
```

and then the projected consequence:

```text
observePeriod ω₂ d (scaleGKUS σ x)
  = observePeriod ω₁ d x
```

The projected theorem should follow from the raw compatibility theorem rather than reproving semantic preservation modulo `d` from scratch.

Important:

- do not claim all `ScaleSpec` values satisfy this;
- do not place an unconditional `[simp]` theorem asserting transport preserves arbitrary observation;
- do not identify blueprint term equality with semantic observation equality unless the exact type makes that justified;
- do not modify `ScaleSpec` itself just to force this property globally unless repository inspection proves that is the intended invariant for every existing use.

---

## 7. Required concrete witness / bridge

The phase is **not complete** if it only adds a generic `ObservationSpec` with identity/rfl examples.

After implementing the minimal generic bridge, connect it to at least one existing DkMath concrete object or operation.

Choose the strongest low-risk witness discovered during preflight. Candidate routes include, in preference order only if the code supports them:

1. an existing KUS support whose blueprint already contains a natural-coordinate / exponent-like field;
2. an existing `ScaleSpec` pair for which observation compatibility is provable from current definitions;
3. a current KUS example/test module that can expose a genuine support-derived `Nat` coordinate;
4. a small local concrete KUS example built from existing public KUS constructors, **provided it demonstrates nontrivial support retention and projection and is not merely `fun _ => 0`**.

If no existing blueprint is semantically prime-coordinate-like, do not fake one. State that explicitly in the report and use the smallest honest concrete structural coordinate example available.

The witness should demonstrate all three layers if possible:

```text
same retained KUS source
-> observer gives raw coordinate structure
-> period d gives a lossy view
```

If a transport-compatible witness is available, additionally demonstrate:

```text
scaleGKUS
-> raw observation preserved by explicit compatibility
-> period observation preserved as corollary
```

---

## 8. Relationship to prime coordinates

Do not force `ObservationSpec` to be prime-specific.

Prime valuation coordinates are already a concrete StructuralArithmetic model. A future bridge may connect a particular KUS support to `primeExponentCoordinates`, but generic KUS observation should remain independent of natural-number factorization.

If the repository already contains an obvious KUS wrapper around a natural number and a canonical extraction to `Nat`, then a prime-coordinate bridge may be appropriate. Otherwise leave prime coordinates as a sibling specialization, not a required field of KUS.

The desired conceptual organization is:

```text
                        StructuralArithmetic raw coordinates
                       /                                \
          KUS ObservationSpec                    prime valuations
                  |                                      |
          KUS typed source                        ordinary Nat source
```

Both feed the same `projectCoordinates` kernel.

---

## 9. Inter-period reuse requirement

Do not reprove modular arithmetic in the KUS bridge.

Any theorem that coarsens a KUS period observation from `d` to `m` under `m ∣ d` should reuse:

```text
projectCoordinates_project_of_dvd
```

or the most specific already implemented InterPeriod theorem.

A useful contract may be:

```text
observe m (observe d raw) = observe m raw
```

but formulate it using the actual KUS observation definitions rather than inventing a second projection calculus.

---

## 10. Boundary periods are part of the public contract

Do not exclude `d = 0` or `d = 1` merely to simplify proofs unless a genuinely external dependency requires positivity.

The StructuralArithmetic kernel intentionally gives:

```text
period 0 = raw observation
period 1 = complete observable collapse
```

The KUS observation bridge should preserve this behavior.

This is important conceptually:

```text
KUS source is still present even when period-1 observation is completely collapsed.
```

That distinction is one of the reasons this bridge exists.

---

## 11. Anti-maze / load-bearing rules

Before each implementation expansion, restate internally:

```text
overall objective
-> current bridge
-> load-bearing assumption
-> next unresolved gap
```

Do not introduce a large categorical, quotient, torsor, gauge, preorder, or world hierarchy merely because it is mathematically possible.

The existing `m ∣ d` inter-period relation already suggests an information-order structure, but **do not abstract it into a category/preorder in this phase** unless the KUS bridge literally cannot be expressed without it.

This phase succeeds by connecting KUS source preservation to the already-built observation kernel, not by adding a new abstract superstructure.

Prefer one small module with strong reuse over many speculative files.

---

## 12. Suggested module placement

Investigate existing naming conventions first. A likely target is one of:

```text
DkMath/NumberTheory/StructuralArithmetic/KUSObservation.lean
DkMath/NumberTheory/StructuralArithmetic/KUSBridge.lean
```

Prefer `KUSObservation.lean` if the module's main responsibility is defining an explicit observer and compatibility law. Prefer a broader name only if the actual implementation genuinely contains more than observation.

Update:

```text
DkMath/NumberTheory/StructuralArithmetic.lean
```

only after the new local module builds successfully.

Avoid modifying the public KUS aggregator unless the bridge must expose a genuinely KUS-native API there. Prefer a one-way import from StructuralArithmetic into KUS modules only if it does not create an import cycle; otherwise keep the bridge in StructuralArithmetic and import KUS.

Check import dependencies before deciding placement.

---

## 13. Public API quality

Every new public declaration must have a Lean docstring explaining its mathematical role.

Prefer theorem names that distinguish:

```text
raw observation
period observation
transport compatibility
inter-period coarsening
```

Avoid overloading `unit`, `identity`, `GN`, or `prime` with new meanings.

Do not call the period `d` a ring identity. Keep the established terminology:

```text
multiplicative identity : 1
raw/unprojected view    : period 0
complete collapse       : period 1
gauge period            : d
```

---

## 14. Proof and dependency discipline

Requirements:

- no `sorry`;
- no new `axiom`;
- no `unsafe` used to bypass proof obligations;
- reuse existing KUS and StructuralArithmetic theorems;
- prefer narrow imports over `import Mathlib` when practical;
- do not duplicate `padicValNat`, factorization, or modular arithmetic proofs;
- keep completed FLT5 / GN proof towers untouched in this phase;
- preserve current public theorem behavior in Phases A-C.

If a desired theorem is false for arbitrary `ScaleSpec`, weaken the statement by adding the correct explicit compatibility hypothesis rather than strengthening KUS globally.

---

## 15. Verification

At minimum run all of:

```bash
lake build DkMath.NumberTheory.StructuralArithmetic.PowerGauge
lake build DkMath.NumberTheory.StructuralArithmetic.PrimeCoordinates
lake build DkMath.NumberTheory.StructuralArithmetic.InterPeriod
lake build DkMath.NumberTheory.StructuralArithmetic.<NewKUSModule>
lake build DkMath.NumberTheory.StructuralArithmetic

git diff --check
```

If edits touch a KUS module, also build the directly affected KUS module/aggregator.

Inspect for forbidden placeholders:

```bash
rg -n "\bsorry\b|^\s*axiom\b|\bunsafe\b" DkMath/NumberTheory/StructuralArithmetic DkMath/KUS
```

Do not treat pre-existing occurrences elsewhere as introduced regressions; report scope accurately.

Use `#print axioms` on the key new public theorems if appropriate. Report whether any project-specific axiom was introduced.

---

## 16. Documentation and report

After implementation, update:

```text
docs/dev/StructuralArithmetic-RedRibbon-260818-v0/README.md
```

so phase status matches actual code.

Create a new implementation report, for example:

```text
docs/dev/StructuralArithmetic-RedRibbon-260818-v0/KUS-OBSERVATION-IMPLEMENTATION-REPORT-260820.md
```

The report must include:

1. baseline HEAD and branch;
2. files inspected before design;
3. design decision and rejected alternatives;
4. exact new public definitions/theorems;
5. the concrete witness chosen and why;
6. exact compatibility hypothesis used for `ScaleSpec` if applicable;
7. build commands and results;
8. `git diff --check` result;
9. placeholder/axiom audit;
10. next remaining load-bearing gap.

If the concrete bridge reveals that the current proposed `ObservationSpec` shape is wrong, document why and implement the better minimal design instead.

---

## 17. Git discipline / completion

Work on the existing branch:

```text
wip/structural-arithmetic-red-ribbon-260818-v0
```

Do not merge to `develop`.
Do not open or merge a PR unless separately requested.
Do not rewrite unrelated history.
Do not force-push.

After successful verification:

```bash
git status -sb
git diff --check
git diff --stat
```

Stage only files belonging to this Phase D implementation, commit them with a concise message, and push the current branch.

The final response/report should give the commit SHA and exact files changed.

---

## 18. Definition of done

Phase D is complete only if all of the following are true:

- a raw KUS source/support remains available as a first-class object;
- an explicit observer derives `ι -> Nat` structural coordinates from that source;
- period observation is implemented by reusing `projectCoordinates`;
- period `0` and period `1` behavior is theorem-level;
- inter-period coarsening reuses the existing InterPeriod API;
- `ScaleSpec` compatibility is explicit, not assumed globally;
- at least one nontrivial concrete KUS-related witness exercises the bridge;
- the new module and StructuralArithmetic aggregate build;
- no new project-specific axiom, `sorry`, or unsafe escape is introduced;
- documentation records what is preserved, what is interpreted, and what is intentionally forgotten.

The target conceptual theorem is not merely

```text
KUS can produce coordinates.
```

It is the stronger architectural statement:

```text
A typed raw KUS source can be retained unchanged while an explicit observer
produces a deliberately lossy period-d structural view; transport preserves
that observation only when an explicit semantic compatibility law proves it.
```

Once this bridge is stable, the next likely work is the primitive-direction / finite-prime-escape layer, followed later by generic GN / GN5 and golden fifth-power sector bridges. Re-evaluate that ordering from the repository after Phase D rather than assuming it mechanically.
