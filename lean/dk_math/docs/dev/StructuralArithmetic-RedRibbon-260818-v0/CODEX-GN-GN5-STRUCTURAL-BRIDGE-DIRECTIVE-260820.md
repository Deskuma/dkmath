# Codex autonomous implementation directive — Generic GN / GN5 Structural Bridge

Date: 2026-08-20
Repository: `Deskuma/dkmath`
Expected working branch: `wip/structural-arithmetic-red-ribbon-260818-v0`
Primary integration area: `lean/dk_math/DkMath/NumberTheory/StructuralArithmetic/`
Target phase: Phase F — generic Cosmic Formula GN / FLT5 GN5 structural bridge

## 0. Mission

Continue the Structural Arithmetic / Red Ribbon integration by implementing the next load-bearing bridge between the now-stable primitive-direction / finite-escape layer and the existing Cosmic Formula `GN` / FLT5 `GN5` machinery.

This is an autonomous Lean implementation task. Do **not** treat this document as a fixed patch recipe. First inspect the actual repository state, exact current definitions, theorem aliases, namespace migrations, and successful build baseline. Then choose the smallest mathematically correct implementation that makes the following chain theorem-level and reusable:

```text
existing generic GN arithmetic
        ↓
existing primitive-prime provider on GN
        ↓
StructuralArithmetic FreshPrimeDirection / non-generation
        ↓
exact specialization bridge at degree 5
        ↓
FLT.Five.GN5
        ↓
existing {2,3,5} finite-prime escape reinterpreted on specialized GN5
```

The goal is **integration, not re-proving mature arithmetic**.

Do not rewrite the completed FLT5 proof tower. Do not redefine `GN`. Do not introduce a second cyclotomic polynomial. Consume existing providers and expose thin structural bridge theorems.

---

## 1. Repository-first preflight — mandatory

Before editing, determine the actual worktree and branch state. The repository and successful Lean builds are the source of truth; documentation is secondary.

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

Read the current StructuralArithmetic tower in full:

```text
DkMath/NumberTheory/StructuralArithmetic.lean
DkMath/NumberTheory/StructuralArithmetic/PowerGauge.lean
DkMath/NumberTheory/StructuralArithmetic/PrimeCoordinates.lean
DkMath/NumberTheory/StructuralArithmetic/InterPeriod.lean
DkMath/NumberTheory/StructuralArithmetic/KUSObservation.lean
DkMath/NumberTheory/StructuralArithmetic/PrimitiveDirection.lean
DkMath/NumberTheory/StructuralArithmetic/FinitePrimeEscapeBridge.lean

docs/dev/StructuralArithmetic-RedRibbon-260818-v0/README.md
docs/dev/StructuralArithmetic-RedRibbon-260818-v0/PRIMITIVE-DIRECTION-IMPLEMENTATION-REPORT-260820.md
```

Then inspect the existing GN definitions and bridges in full:

```text
DkMath/CosmicFormula/GTail.lean
DkMath/CosmicFormula/Defs.lean
DkMath/CosmicFormula/CosmicFormulaBinom.lean
DkMath/CosmicFormula/CosmicTheorems.lean
DkMath/NumberTheory/Gcd/GN.lean
DkMath/NumberTheory/UniqueFactorizationGN.lean
DkMath/NumberTheory/PrimitiveBeam.lean
DkMath/NumberTheory/PrimitiveBeamExamples.lean
DkMath/FLT/Core.lean
DkMath/FLT/Five/GN5.lean
DkMath/Hackathon/FinitePrimeEscapeGN5.lean
```

Search before inventing any bridge theorem or alias:

```bash
rg -n "abbrev GN|def GN|GTail d 1|CosmicFormulaBinom\.GN|CosmicFormula\.GN" DkMath
rg -n "GN5.*GN|GN.*GN5|GN5_eq|GN5_one_one" DkMath
rg -n "primitive_prime_dvd_GN|primitive_prime_dvd_GN_body|PrimitivePrimeFactorOfDiffPow" DkMath
rg -n "FreshPrimeDirection|PrimeScaleGeneratedBy|GN5_escape_not_primeScaleGeneratedBy" DkMath/NumberTheory/StructuralArithmetic DkMath/Hackathon
rg -n "GN_zmod|mod 5|five.*GN|GN.*five|choose.*prime" DkMath/FLT DkMath/NumberTheory DkMath/CosmicFormula
```

Inspect exact theorem signatures; do not infer them from names or old docs.

Baseline-build the current StructuralArithmetic Phase A-E tower before editing:

```bash
lake build DkMath.NumberTheory.StructuralArithmetic.PowerGauge
lake build DkMath.NumberTheory.StructuralArithmetic.PrimeCoordinates
lake build DkMath.NumberTheory.StructuralArithmetic.InterPeriod
lake build DkMath.NumberTheory.StructuralArithmetic.KUSObservation
lake build DkMath.NumberTheory.StructuralArithmetic.PrimitiveDirection
lake build DkMath.NumberTheory.StructuralArithmetic.FinitePrimeEscapeBridge
lake build DkMath.NumberTheory.StructuralArithmetic
```

If the baseline fails, diagnose it first. Do not build Phase F on a broken baseline.

---

## 2. Naming and semantic boundary — mandatory

There are multiple GN spellings in the repository. Determine their **actual current relationship** before writing new code.

At minimum distinguish:

### 2.1 Canonical `Defs.GN`

Current canonical definition is expected to be approximately:

```lean
DkMath.CosmicFormula.GN R x u d := GTail d 1 x u
```

This is the naming-stable generic gap-normalized tail.

### 2.2 `CosmicFormulaBinom.GN`

A downstream/public spelling is heavily used as:

```lean
DkMath.CosmicFormulaBinom.GN d x u
```

Inspect whether this is currently a definitional abbreviation of the canonical `Defs.GN`, a theorem-linked wrapper, or a separate definition. Do not create a redundant equality theorem if `rfl`/`simp` already exposes the relation cleanly.

If a public named bridge between these two spellings is genuinely missing and useful, add the smallest one. Otherwise document that the relation is definitional and move on.

### 2.3 FLT5 specialized `GN5`

`DkMath.FLT.Five.GN5 g y` is an explicit natural-number polynomial:

```text
g^4 + 5*g^3*y + 10*g^2*y^2 + 10*g*y^3 + 5*y^4
```

It is intended to be the degree-five specialization of the generic GN kernel in gap coordinates.

The crucial Phase F bridge is to make that intended equality theorem-level if it is not already present.

### 2.4 Do not overload the word “period”

The exponent/degree of the Cosmic Formula and the PowerGauge observation period are conceptually different parameters.

Use different variable names when both appear, for example:

```text
d : Cosmic Formula degree
r : PowerGauge observation period
```

Do not write an API in which a single `d` silently means both.

Even when both are numerically `5`, the equality is a specialization choice, not a definition of the concepts.

---

## 3. Critical distinction: three different “mod 5” phenomena

Do not merge the following into one theorem or interpretation.

### A. Degree-five Cosmic Formula

```text
GN 5 g y
```

Here `5` is the polynomial degree.

### B. FLT5 additive coefficient congruence

The existing specialized theorem has the shape:

```text
GN5 g y = g^4 + 5 * (...)
```

so `GN5 g y ≡ g^4 (mod 5)` in the ordinary additive congruence sense.

### C. StructuralArithmetic PowerGauge projection

```text
projectExponent 5 e = e % 5
```

This acts on **prime-exponent coordinates**, and multiplication by a fifth power is invisible because valuations change by multiples of five.

These are related conceptually by quotient/kernel language but are mathematically distinct.

Phase F must **not** identify B and C merely because both contain the number `5`.

If you add a theorem relating them, it must state the explicit bridge assumptions and pass through prime valuations. Otherwise leave that connection for a later phase.

---

## 4. Required load-bearing bridge A — generic GN to fresh primitive direction

The repository already has Zsigmondy/primitive-prime infrastructure. In particular inspect the exact current theorem corresponding to:

```lean
PrimitiveBeam.primitive_prime_dvd_GN_body
```

or its closest current equivalent.

The intended existing arithmetic route is approximately:

```text
PrimitivePrimeFactorOfDiffPow q (x + u) u d
        + d > 1
        ↓
q ∣ GN d x u
```

Phase F should consume that provider and turn it into the new StructuralArithmetic vocabulary.

A good theorem shape is approximately:

```lean
freshPrimeDirection_GN_of_primitivePrimeFactor
    (hq : PrimitivePrimeFactorOfDiffPow q (x + u) u d)
    (hd : 0 < d)
    (hd1 : 1 < d)
    (hq_not_mem : q ∉ S) :
    FreshPrimeDirection S (CosmicFormulaBinom.GN d x u) q
```

Adapt hypotheses to the exact existing provider; do not duplicate its proof.

Then expose the immediate non-generation corollary:

```text
¬ PrimeScaleGeneratedBy S (GN d x u)
```

under the same fresh-direction assumptions.

This theorem is the main generic GN ↔ Phase E bridge.

### Important

`q ∉ S` remains an explicit “relative to the known world” hypothesis. A Zsigmondy primitive prime is primitive relative to lower exponents; that does **not** automatically imply it is absent from an arbitrary finite known-scale set `S`.

Do not conflate those two notions of primitive.

---

## 5. Required load-bearing bridge B — specialized FLT5 `GN5` equals generic degree-five GN

Determine whether an exact theorem already exists connecting:

```lean
DkMath.FLT.Five.GN5 g y
```

and

```lean
DkMath.CosmicFormulaBinom.GN 5 g y
```

(or the canonical `DkMath.CosmicFormula.GN ℕ g y 5` if that is the more direct target).

If a suitable theorem exists, reuse/re-export it rather than proving another.

If it does not exist, prove a single canonical equality theorem, for example:

```lean
GN5_eq_generic_GN (g y : ℕ) :
  DkMath.FLT.Five.GN5 g y =
    DkMath.CosmicFormulaBinom.GN 5 g y
```

or the reverse orientation if that rewrites more naturally downstream.

### Proof policy

Prefer one of these routes, in this order:

1. definitional simplification through the existing canonical GN/GTail API;
2. an existing cyclotomic / difference-power quotient equality;
3. a short `norm_num` / `ring` / finite-sum expansion specific to degree five.

Do not create a second independent definition of the degree-five kernel.

Do not generalize this proof into a new cyclotomic library unless the necessary theorem already exists and can be reused cheaply.

### Placement

Prefer a StructuralArithmetic bridge module so the completed FLT5 file remains untouched unless repository dependency direction makes a tiny theorem in `FLT/Five/GN5.lean` clearly cleaner.

Possible module name:

```text
DkMath.NumberTheory.StructuralArithmetic.GNBridge
```

or:

```text
DkMath.NumberTheory.StructuralArithmetic.GN5Bridge
```

One module is preferable if it stays focused.

---

## 6. Required load-bearing bridge C — transport the existing finite escape to specialized GN5

Phase E already proves on the generic/binomial GN spelling:

```text
¬ PrimeScaleGeneratedBy
    ({2,3,5} : Finset ℕ)
    (DkMath.CosmicFormulaBinom.GN 5 1 1)
```

and exposes a corresponding `FreshPrimeDirection` witness.

After establishing the exact `GN5 = generic GN` specialization bridge, derive the FLT5-specialized versions **by rewriting**, not by recomputing 31.

Required concrete theorem shapes should be equivalent to:

```lean
GN5_one_one_has_freshPrimeDirection :
  ∃ q,
    FreshPrimeDirection
      ({2,3,5} : Finset ℕ)
      (DkMath.FLT.Five.GN5 1 1) q
```

and/or:

```lean
GN5_one_one_not_primeScaleGeneratedBy_two_three_five :
  ¬ PrimeScaleGeneratedBy
      ({2,3,5} : Finset ℕ)
      (DkMath.FLT.Five.GN5 1 1)
```

The **non-generation theorem on the specialized FLT5 object is mandatory**.

Do not prove `GN5 1 1 = 31` again merely to establish this. The point is to prove that the generic StructuralArithmetic statement and the specialized FLT5 polynomial are the same object under a bridge.

---

## 7. Preferred generic theorem — GN target from any fresh prime divisor

If it improves reuse with essentially no extra machinery, expose a small generic wrapper such as:

```lean
freshPrimeDirection_GN_of_prime_dvd_not_mem
    (hq : Nat.Prime q)
    (hqd : q ∣ GN d x u)
    (hqS : q ∉ S) :
    FreshPrimeDirection S (GN d x u) q
```

This may be only a thin specialization of the existing Phase E constructor. Add it only if it improves theorem discoverability in the GN bridge.

The more important theorem is the one that consumes the existing **primitive-prime provider**, because that demonstrates a real cross-module connection.

---

## 8. Prime coordinates / PowerGauge connection — do not force it

Every nonzero natural GN value already has raw prime-exponent coordinates through Phase B:

```text
primeExponentCoordinates (GN d x u)
```

and period observations through:

```text
projectPrimeCoordinates r (GN d x u)
```

Do not create GN-specific copies of these generic definitions merely for naming symmetry.

A GN-specific theorem is worthwhile only if it proves a new interaction, for example:

```text
FreshPrimeDirection S (GN d x u) q
```

implies a nonzero `q` coordinate in the raw valuation vector, or some explicit support statement.

If the exact `padicValNat` API makes that cheap, it is a useful optional bridge. If it causes API friction, record it as a later enhancement and keep Phase F focused.

Do not conflate:

```text
raw new prime direction
```

with:

```text
visible distinction after projection period r
```

A raw direction can be partially or completely hidden by a chosen quotient observation.

---

## 9. Existing `UniqueFactorizationGN` / gcd infrastructure — reuse selectively

`DkMath.NumberTheory.UniqueFactorizationGN` already contains factorization-support, prime-power comparison, gcd, and GN-specific wrappers.

Inspect it before adding any theorem concerning:

- factorization support of GN;
- prime divisibility of GN;
- prime-power divisibility;
- exceptional primes dividing the degree;
- `GN_ne_zero` conditions.

Do not duplicate these lemmas inside StructuralArithmetic.

However, do not import this heavy module merely because it exists if the required Phase F theorems can be proved using `PrimitiveBeam` + `PrimitiveDirection` + the small GN definitions alone.

Prefer the smallest dependency graph that closes the bridge.

---

## 10. Existing FLT5 `GN5` decomposition — preserve, do not reinterpret too early

The specialized FLT5 module already proves statements such as:

```text
GN5_eq_homogeneous_cyclotomic
GN5_eq_gap_mul_add_five_mul_y_pow_four
GN5_eq_g_pow_four_add_five_mul
add_pow_five_eq_add_mul_GN5
pow_five_sub_pow_five_eq_gap_mul_GN5
```

These are mature local arithmetic contracts.

Phase F should use them only if they simplify the exact generic/specialized equality proof or a bridge theorem.

Do not refactor their proofs into StructuralArithmetic.

Do not replace the existing FLT5 vocabulary with generic GN vocabulary. The goal is to show that both APIs refer to the same mathematical kernel where appropriate.

---

## 11. Public API and dependency structure

A preferred dependency shape is:

```text
PrimitiveDirection
        ↑
PrimitiveBeam / generic GN provider
        ↑
GNBridge
        ↓
FLT.Five.GN5 equality
        ↓
Phase-E finite escape result rewritten to specialized GN5
```

Avoid introducing a circular import from FLT5 back into a lower NumberTheory module.

If importing `DkMath.FLT.Five.GN5` into the StructuralArithmetic bridge is acceptable and does not create a cycle, use a bridge module at the higher layer.

If it would create a cycle, split the bridge:

```text
StructuralArithmetic/GNPrimitiveBridge.lean
StructuralArithmetic/GN5SpecializationBridge.lean
```

or place the specialization wrapper in an acyclic location.

Do not resolve dependency cycles by moving mature modules wholesale.

Update the public aggregate only after the local module(s) build:

```text
DkMath.NumberTheory.StructuralArithmetic
```

---

## 12. Required theorem-level checkpoint

Phase F is complete only if all of the following are theorem-level and build-checked:

1. **Generic GN primitive provider bridge**
   - an existing primitive-prime theorem can produce `FreshPrimeDirection` / non-generation of a generic GN target when the prime is absent from the known set.

2. **Generic ↔ specialized degree-five identity**
   - `FLT.Five.GN5 g y` is proved equal to the correct generic degree-five GN object, or an existing exact theorem is reused and made discoverable.

3. **Specialized GN5 finite escape interpretation**
   - the existing `{2,3,5}` finite-prime escape is transported to a theorem on `DkMath.FLT.Five.GN5 1 1`.

4. **No semantic conflation**
   - degree, additive modulus, and PowerGauge period remain distinct in theorem names/docs.

5. **No duplicate arithmetic proof**
   - do not recompute the existing finite-prime escape or reprove the Zsigmondy provider.

A phase that only proves item 2 is **not sufficient**.

---

## 13. Concrete theorem target

At the end of the phase, a reader should be able to follow a theorem chain equivalent to:

```text
primitive prime factor of (x+u)^d - u^d
        ↓ existing PrimitiveBeam
q divides generic GN d x u
        ↓ Phase F bridge
FreshPrimeDirection S (GN d x u) q
        ↓ Phase E
¬ PrimeScaleGeneratedBy S (GN d x u)
```

and separately:

```text
existing finitePrimeEscape_hits_GN5
        ↓ Phase E
¬ PrimeScaleGeneratedBy {2,3,5} (generic GN 5 1 1)
        ↓ exact Phase F specialization equality
¬ PrimeScaleGeneratedBy {2,3,5} (FLT.Five.GN5 1 1)
```

That second chain must use rewriting/transport through the equality bridge, not another numerical proof.

---

## 14. Verification requirements

Build new local modules first, then the aggregate.

Minimum commands, adapted to actual module names:

```bash
lake build DkMath.NumberTheory.StructuralArithmetic.PrimitiveDirection
lake build DkMath.NumberTheory.StructuralArithmetic.FinitePrimeEscapeBridge
lake build DkMath.NumberTheory.StructuralArithmetic.GNBridge
lake build DkMath.NumberTheory.StructuralArithmetic
```

If you split the bridge into multiple modules, build each explicitly.

Also build any directly touched mature module, for example:

```bash
lake build DkMath.FLT.Five.GN5
```

if it is edited.

Then run:

```bash
git diff --check
```

Audit new Phase F source for:

```bash
rg -n "\bsorry\b|\badmit\b|^\s*axiom\b|\bunsafe\b" \
  DkMath/NumberTheory/StructuralArithmetic
```

Scope the audit to new/changed Phase F source when reporting so pre-existing repository warnings are not misattributed.

Use `#print axioms` on the main new public theorems if practical. Report inherited foundational or pre-existing project assumptions accurately; do not claim global axiom-freedom if an imported research module already contains a placeholder.

---

## 15. Documentation requirements

Update:

```text
docs/dev/StructuralArithmetic-RedRibbon-260818-v0/README.md
```

so Phase F is marked according to actual implementation status.

Add a report such as:

```text
docs/dev/StructuralArithmetic-RedRibbon-260818-v0/GN-GN5-STRUCTURAL-BRIDGE-IMPLEMENTATION-REPORT-260820.md
```

The report must state:

- baseline HEAD;
- actual GN definitions/aliases discovered;
- whether canonical `CosmicFormula.GN` and `CosmicFormulaBinom.GN` are definitional aliases or theorem-related;
- exact specialized `GN5` equality proved/reused;
- exact generic primitive-provider theorem reused;
- concrete specialized GN5 escape theorem obtained;
- distinction between degree 5, additive mod 5, and PowerGauge period 5;
- files changed;
- build commands/results;
- `sorry`/axiom audit result;
- remaining next gap.

Every new public Lean declaration must have a meaningful docstring.

---

## 16. Anti-maze rules

### Do not count as Phase F progress

- merely adding another alias for `GN`;
- merely proving `GN5 1 1 = 31` again;
- merely importing FLT5 into the aggregate;
- building a new cyclotomic abstraction unused by the required theorem chain;
- adding generic category/monoid machinery unrelated to the concrete bridge;
- equating additive congruence mod 5 with PowerGauge exponent projection;
- renaming mature GN APIs across the repository;
- modifying the completed FLT5 proof tower without necessity.

### Do count as Phase F progress

- reusing an existing primitive-prime provider to obtain StructuralArithmetic fresh-direction semantics for generic GN;
- establishing or exposing the exact degree-five generic/specialized kernel equality;
- transporting the already-proved finite escape theorem to the specialized FLT5 GN5 object;
- keeping degree / additive modulus / observation period separate in types and theorem names.

One load-bearing bridge is better than many convenience wrappers.

---

## 17. Commit / push discipline

After successful implementation and verification:

1. inspect `git status` and `git diff`;
2. stage only files belonging to this Phase F task;
3. do not use `git add -A`, `git add .`, or `git add --all` if unrelated changes exist;
4. commit with a concise message describing the GN/GN5 structural bridge;
5. push to the current working branch:

```text
wip/structural-arithmetic-red-ribbon-260818-v0
```

Do not merge into `develop`.
Do not create a PR unless explicitly requested separately.

---

## 18. Completion report format

When finished, report:

### Situation

- branch;
- baseline HEAD;
- preflight findings;
- exact GN naming/alias relationships discovered.

### Implementation

- new/changed modules;
- main theorem names;
- generic primitive-provider bridge;
- exact GN5 specialization equality;
- concrete specialized GN5 escape theorem;
- aggregate/docs changes.

### Verification

- exact `lake build` commands and results;
- `git diff --check`;
- new-source `sorry` / `admit` / `axiom` / `unsafe` audit;
- `#print axioms` findings.

### Next gap

Identify the next genuinely load-bearing unresolved bridge after Phase F. Likely candidates include the golden-unit fifth-power sector bridge or a Pascal/binomial prime-period bridge, but choose only after inspecting what Phase F actually closes.

---

## 19. Final design principle

The architecture after Phase F should read:

```text
KUS
  preserves typed raw support

ObservationSpec
  interprets selected support coordinates

PowerGauge
  forgets exponent information modulo an observation period

PrimitiveDirection
  identifies new raw prime-scale directions

FinitePrimeEscapeBridge
  supplies existing escape witnesses

GNBridge
  shows existing Cosmic Formula kernels can carry those new directions

GN5 specialization
  shows the FLT5 explicit fifth-degree kernel is the same degree-five GN object
```

The crucial separation remains:

```text
new raw direction ≠ projected sector
Cosmic degree ≠ gauge period
additive mod 5 ≠ valuation-exponent mod 5
```

Preserve those distinctions while making the existing DkMath layers commute through explicit theorems.
