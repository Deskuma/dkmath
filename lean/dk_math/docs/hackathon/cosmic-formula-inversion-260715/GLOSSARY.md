# Glossary

## DkMath — Cosmic Formula Inversion

This glossary fixes the terminology used by the hackathon project.

Its purposes are:

- to keep project documents consistent;
- to prevent Codex from inventing parallel vocabulary;
- to distinguish standard mathematical terms from DkMath interpretations;
- to separate formally proved properties from visual or conceptual readings;
- to prevent stronger terms from being used for weaker theorems.

When this glossary conflicts with casual wording in an older discussion document, this glossary governs the current hackathon project.

---

## 1. Terminology Classes

Every important term belongs to one of four classes.

### Standard Mathematical Term

A term with an established mathematical meaning.

Examples:

```text
prime
divisibility
coprime
finite product
injective
inverse map
interval
```

Lean theorem statements should prefer standard mathematical terms whenever possible.

### Existing DkMath Term

A term already used as part of the DkMath library or its research language.

Examples:

```text
Big
Body
Gap
Core
Beam
GN
DkReal
```

Before introducing a declaration using one of these names, Codex must search for the existing DkMath definition and theorem surface.

### Hackathon Project Term

A term used to explain the project but not intended to replace standard mathematics.

Examples:

```text
finite prime universe
fresh prime channel
completed boundary
inverse-projection program
```

These terms belong primarily in documentation, comments, narration, and visualization.

### Process Term

A term describing the human–AI–Lean workflow.

Examples:

```text
checkpoint
repository audit
genuine obstruction
stopping rule
thin facade
```

These terms describe development control rather than mathematical objects.

---

## 2. Core Symbols

The following symbols remain stable across the project.

```text
S:
  the original finite set of known primes

P:
  the product of all primes in S

u:
  the coprime offset and linear Gap scale

P + u:
  the completed arithmetic boundary

q:
  a candidate prime divisor of P + u

Big:
  the completed square (P + u)²

Body:
  the non-Gap component P(P + 2u)

Gap:
  the square component u²
```

The core equations are:

$$
P=\prod_{p\in S}p
$$

$$
\gcd(P,u)=1
$$

$$
P(P+2u)+u^2=(P+u)^2
$$

The fixed demonstration uses:

$$
S=\{2,3,5,7\}
$$

$$
P=210
$$

$$
u=11
$$

$$
P+u=221=13\cdot17
$$

---

## 3. Arithmetic Terms

### Boundary Value

The arithmetic value:

$$
P+u
$$

It is called a boundary because it is also the side length of the completed Cosmic Formula square.

Formal meaning:

```text
a natural number obtained by adding u to P
```

Interpretive meaning:

```text
the interface between the finite known-prime construction and newly appearing prime divisors
```

The term does not imply a topological boundary unless a separate geometric object has been formally defined.

---

### Coprime

Two natural numbers `a` and `b` are coprime when:

$$
\gcd(a,b)=1
$$

Lean form:

```lean
Nat.Coprime a b
```

In this project, the essential condition is:

$$
\gcd(P,u)=1
$$

This prevents a prime used in `P` from also dividing `u`.

---

### Divides

For natural numbers `a` and `b`:

$$
a\mid b
$$

means that there exists a natural number `k` such that:

$$
b=a\cdot k
$$

Lean notation:

```lean
a ∣ b
```

---

### Factor

A number `a` is a factor of `b` when:

$$
a\mid b
$$

The word `factor` alone does not imply primality.

---

### Factorization

An equality expressing a number as a product.

Example:

$$
221=13\cdot17
$$

The concrete factorization is used for the demonstration.

The general finite prime escape theorem does not depend on knowing the complete factorization of `P + u`.

---

### Finite Prime Set

A finite collection of natural numbers, each proved prime.

Preferred Lean representation:

```lean
S : Finset ℕ
```

with hypothesis:

```lean
∀ p ∈ S, Nat.Prime p
```

---

### Finite Prime Universe

Hackathon project terminology for the finite arithmetic environment determined by:

- a finite prime set `S`;
- its product `P`;
- divisibility by members of `S`;
- residue information modulo `P`;
- constructions built from `P`.

It is not automatically:

- a field;
- a ring;
- a type-theoretic universe;
- a residue class ring;
- a localization.

When one of those standard structures is intended, its standard name must be used.

---

### Finite Prime Escape

The theorem pattern:

$$
q\mid P+u\Longrightarrow q\notin S
$$

under the assumptions that:

- `P` is the product of the primes in `S`;
- `q` is prime;
- `P` and `u` are coprime.

The public existence form is:

$$
\exists q,\ \operatorname{Prime}(q)\land q\mid P+u\land q\notin S
$$

when:

$$
1<P+u
$$

The phrase does not claim a new theorem about the asymptotic distribution of primes.

---

### Fresh Prime Factor

A prime factor of a target number that is not a member of the original finite prime set.

Intended meaning:

```text
q is prime
q divides n
q is not in S
```

Possible Lean predicate:

```lean
def FreshPrimeFactor
    (S : Finset ℕ)
    (n q : ℕ) : Prop :=
  Nat.Prime q ∧ q ∣ n ∧ q ∉ S
```

This definition should be introduced only if no equivalent DkMath predicate already exists.

---

### Fresh Prime Channel

Interpretive project term for a fresh prime factor viewed as a new arithmetic direction or factor channel.

Formal content:

```text
a fresh prime factor
```

The word `channel` adds interpretation but no additional theorem.

---

### Known Prime

A prime belonging to the original finite set `S`.

This does not mean that the prime is known in an epistemic or historical sense.

It means only:

```lean
p ∈ S
```

---

### Known-Prime Product

The product:

$$
P=\prod_{p\in S}p
$$

Lean representation is expected to use a `Finset` product.

The exact syntax depends on the result of the repository audit.

---

### Offset

The natural number `u` added to `P`.

The project requires:

$$
0<u
$$

for the visual interpretation and:

$$
\gcd(P,u)=1
$$

for the finite prime escape theorem.

The pure exclusion lemma may not need positivity.

---

### Prime

A natural number greater than one whose only positive divisors are one and itself.

Lean form:

```lean
Nat.Prime p
```

---

### Prime Divisor

A number `q` such that:

```lean
Nat.Prime q
```

and:

```lean
q ∣ n
```

---

### Prime-Divisor Existence

The standard result that every natural number greater than one has a prime divisor.

The project expects to reuse Mathlib or DkMath rather than implement prime-divisor existence from first principles.

---

### Product

The multiplication of all elements in a finite set.

For the empty set, the standard product is `1`.

This empty-product convention may produce valid edge cases, but the public demo uses a nonempty set.

---

### Product Membership Divisibility

The standard finite-product fact:

```text
if q belongs to S, then q divides the product of S
```

Symbolically:

$$
q\in S\Longrightarrow q\mid\prod_{p\in S}p
$$

The repository audit must identify the existing theorem used for this step.

---

### Supplied Prime Divisor

A prime `q` already given as an input to a theorem with the hypothesis:

```lean
q ∣ P + u
```

A theorem about a supplied divisor is logically weaker than a theorem asserting that such a divisor exists.

---

### Universal Freshness

The property that every prime divisor of `P + u` lies outside `S`.

$$
\forall q,\ \operatorname{Prime}(q)\land q\mid P+u\Longrightarrow q\notin S
$$

This does not mean every prime outside `S` divides `P + u`.

---

## 4. Freshness Versus Primitiveness

### Fresh

Relative to a finite reference set.

```text
q is fresh relative to S
↔
q is prime, q divides the target, and q is not in S
```

### Primitive Prime Divisor

A sequence-relative term.

A prime divisor is primitive at a stage when it divides the current sequence term but does not divide specified earlier terms.

This requires:

- an indexed sequence or family;
- a current stage;
- an explicit earlier-stage exclusion condition.

### Required Distinction

```text
Fresh:
  not in the original finite set

Primitive:
  not present at designated earlier sequence stages
```

The hackathon finite-prime theorem proves freshness.

It must not be labelled primitive unless the stronger sequence-relative hypotheses are present.

---

## 5. Cosmic Formula Terms

### Big

The completed total.

For the initial project:

$$
\mathrm{Big}(P,u)=(P+u)^2
$$

Interpretive reading:

```text
the completed square
the total conserved quantity
```

Before adding a new Lean definition named `Big`, Codex must inspect existing DkMath definitions.

---

### Body

The component remaining after removing the square Gap from Big.

$$
\mathrm{Body}(P,u)=P(P+2u)
$$

The identity is:

$$
\mathrm{Body}(P,u)=\mathrm{Big}(P,u)-\mathrm{Gap}(u)
$$

over a domain where the subtraction is interpreted appropriately.

In the natural-number implementation, the preferred theorem is the additive equality:

$$
\mathrm{Body}+\mathrm{Gap}=\mathrm{Big}
$$

---

### Gap

The completion component:

$$
\mathrm{Gap}(u)=u^2
$$

The project also uses a linear normalized Gap coordinate:

$$
\frac{u}{P+u}
$$

These must not be conflated.

```text
linear Gap scale:
  u

square Gap:
  u²

normalized linear Gap:
  u / (P + u)

normalized square Gap:
  u² / (P + u)²
```

---

### Cosmic Completion

The identity:

$$
P(P+2u)+u^2=(P+u)^2
$$

Interpretive reading:

```text
Body plus Gap completes Big
```

Formal content:

```text
an exact polynomial identity
```

The theorem does not formalize the physical cutting and rearrangement of planar regions.

---

### Cosmic Formula

DkMath terminology for the structural decomposition:

$$
\mathrm{Big}=\mathrm{Body}+\mathrm{Gap}
$$

In the current square case:

$$
(P+u)^2=P(P+2u)+u^2
$$

The wider DkMath library contains more general Cosmic Formula structures.

The hackathon facade must reuse them when suitable rather than creating an independent theory with the same name.

---

### Completion

The operation of adding the Gap to the Body to obtain Big.

$$
\mathrm{Body}+\mathrm{Gap}=\mathrm{Big}
$$

The word may describe either:

- the exact algebraic identity;
- the visual animation that assembles the square.

The context must make clear which meaning is intended.

---

### Completed Boundary

The side length:

$$
P+u
$$

of the completed square.

It is also the arithmetic value whose prime divisors are studied.

This shared quantity connects the arithmetic theorem and the visual identity.

---

### Gnomon

A geometric or algebraic region obtained as the difference between two related squares or higher-power shapes.

The Body:

$$
(P+u)^2-u^2=P(P+2u)
$$

may be visualized as a gnomon around the square Gap.

The minimum viable Lean theorem does not need a formal Euclidean gnomon type.

---

### Square Completion

The algebraic rearrangement that forms a perfect square.

In the project:

$$
P(P+2u)+u^2=(P+u)^2
$$

This is related to, but not identical with, the standard method of completing the square in solving quadratic equations.

---

## 6. Extended DkMath Terms

### Beam

An existing DkMath term generally used for an intermediate or transmitted component between a Core and a larger Body.

A common DkMath decomposition is:

$$
\mathrm{Body}=\mathrm{Core}+\mathrm{Beam}
$$

The initial hackathon theorem does not require a new Beam definition.

The term should appear only when a reused DkMath API actually exposes it or when documentation explains a broader DkMath relationship.

---

### Core

An existing DkMath term for a central retained or foundational component.

Its exact formal meaning depends on the module.

The hackathon project must not assume that every DkMath `Core` declaration has the same type or algebraic role.

---

### GN

A DkMath term associated with the normalized quotient in a difference of powers.

A typical identity is:

$$
(x+u)^d-u^d=x\,GN_d(x,u)
$$

GN may connect the Cosmic Formula to:

- binomial tails;
- divisibility;
- finite differences;
- valuation;
- primitive factors.

The minimum viable hackathon theorem may not need GN directly.

Codex should reuse it only where it materially shortens or strengthens the intended bridge.

---

### Tail

The remaining higher-order or binomial component after selected initial terms have been removed.

In DkMath, Tail and generalized GN structures may encode divisibility by powers of a boundary variable.

The term must not be introduced into the public demo unless it helps explain an implemented theorem.

---

### Unit Kernel

A DkMath term for a generating unit or scale core, often represented by a quantity such as:

$$
u^d
$$

In the present square completion, the Gap:

$$
u^2
$$

may be interpreted as a square unit kernel.

This is interpretive unless connected to an existing formal DkMath unit API.

---

## 7. Projection Terms

### Projection

A map from the unbounded arithmetic scale into a bounded coordinate.

Candidate unsigned form:

$$
\pi(P,u)=\frac{P}{P+u}
$$

Candidate signed form:

$$
\Pi(P,u)=-\frac{P}{P+u}
$$

Only one convention should become the primary public API.

---

### Unsigned Projection

The map:

$$
\pi(P,u)=\frac{P}{P+u}
$$

For:

$$
P\ge0
$$

and:

$$
u>0
$$

its image lies in:

$$
0\le\pi(P,u)<1
$$

---

### Signed Projection

The map:

$$
\Pi(P,u)=-\frac{P}{P+u}
$$

For:

$$
P\ge0
$$

and:

$$
u>0
$$

its image lies in:

$$
-1<\Pi(P,u)\le0
$$

---

### Bounded Projection

Any selected project map whose image lies in a bounded interval.

The term describes the codomain behavior.

It does not by itself imply:

- surjectivity;
- continuity;
- invertibility;
- computable reconstruction.

Each such property requires its own theorem.

---

### Forward Map

The map taking arithmetic data such as `P` to a normalized projected coordinate.

Example:

$$
P\longmapsto\frac{P}{P+u}
$$

---

### Inverse Formula

An algebraic expression reconstructing `P` from the projected coordinate and fixed `u`.

Unsigned case:

$$
P=\frac{ux}{1-x}
$$

Signed case:

$$
P=-\frac{ux}{1+x}
$$

The formula requires domain conditions ensuring the denominator is nonzero.

---

### Inverse Projection

The project program of recovering macro-scale arithmetic information from a bounded projected representation.

Depending on context, it may mean:

- an exact inverse formula;
- a left inverse;
- a right inverse on the image;
- injectivity;
- interval-based reconstruction.

The phrase `inverse projection is complete` must not be used unless the relevant formal theorems have been implemented.

---

### Projection Image

The set or interval of values attained by the forward projection.

For finite `P`, the limiting endpoint corresponding to `P → ∞` may be approached but not attained.

---

### Reconstruction

The process of recovering `P`, or a unique integer candidate for `P`, from projected data.

Exact reconstruction and interval reconstruction are distinct.

```text
exact reconstruction:
  algebraic inverse equality

interval reconstruction:
  projected uncertainty is mapped back to an interval containing a unique integer candidate
```

---

### Macro Scale

Interpretive term for the original arithmetic scale before normalization.

In the current project, `P` is a macro-scale quantity relative to its bounded projection.

---

### Micro Scale

Interpretive term for the bounded normalized coordinate or interval representation.

The term does not imply infinitesimal analysis.

---

## 8. Normalization Terms

### Normalize

To divide by a scale so that the resulting quantity lies in a standard bounded range or satisfies a conservation identity with total `1`.

Example:

$$
\frac{P(P+2u)}{(P+u)^2}+\frac{u^2}{(P+u)^2}=1
$$

---

### Normalized Body

$$
\mathrm{NormalizedBody}(P,u)=\frac{P(P+2u)}{(P+u)^2}
$$

---

### Normalized Gap

$$
\mathrm{NormalizedGap}(P,u)=\frac{u^2}{(P+u)^2}
$$

---

### Linear Gap Coordinate

$$
\gamma(P,u)=\frac{u}{P+u}
$$

It satisfies:

$$
\gamma(P,u)^2=\mathrm{NormalizedGap}(P,u)
$$

The linear coordinate and square mass are not interchangeable.

---

### Conservation Identity

An equality in which a total quantity is decomposed into components without loss.

Example:

$$
\mathrm{NormalizedBody}+\mathrm{NormalizedGap}=1
$$

The project may use conservation language only when supported by an exact equality or stated inequality.

---

## 9. Interval and DkReal Terms

### Interval

A set of values between lower and upper endpoints.

Typical notation:

$$
[a,b]
$$

The formal interval representation may use:

- `Set.Icc`;
- an existing DkReal interval structure;
- another established DkMath type.

The repository audit determines the correct implementation.

---

### Interval Width

For an interval with endpoints `a ≤ b`:

$$
\operatorname{width}([a,b])=b-a
$$

The exact definition must reuse the existing interval API when possible.

---

### Nested Intervals

A sequence of intervals satisfying:

$$
I_{n+1}\subseteq I_n
$$

Nestedness alone does not imply that widths tend to zero.

---

### Shrinking Width

The property that interval width tends to zero or becomes smaller than a required bound.

For integer uniqueness, the key finite condition is:

$$
\operatorname{width}(I)<1
$$

---

### Integer Candidate

A natural number or integer lying inside a reconstructed interval.

---

### Unique Integer Candidate

The property that an interval contains at most one integer.

A sufficient condition is:

$$
\operatorname{width}(I)<1
$$

together with the appropriate endpoint and ordering assumptions.

`At most one` must not be confused with `exactly one`.

Existence and uniqueness are separate obligations.

---

### DkReal

An existing DkMath framework for representing real values through computable or nested rational interval data.

The exact available types and theorem names must be determined by repository audit.

The hackathon project must bridge to DkReal rather than define a parallel real-number construction.

---

### DkReal Reconstruction

The stretch milestone connecting:

```text
bounded projected intervals
→ inverse-mapped macro intervals
→ width control
→ unique integer candidate
```

This phrase must not be used as a completed result before the corresponding Lean bridge builds.

---

### Floor

The greatest integer less than or equal to a real or rational value.

Floor may be useful for extracting integer candidates.

The project should reuse Mathlib or DkMath floor APIs.

---

### Ceiling

The least integer greater than or equal to a real or rational value.

Floor and ceiling may jointly characterize the integers contained in an interval.

---

## 10. Map and Proof Terms

### Function

A rule assigning exactly one output to each input in its domain.

---

### Injective

A function `f` is injective when:

$$
f(a)=f(b)\Longrightarrow a=b
$$

For fixed positive `u`, the selected projection should be proved injective if the inverse phase is implemented.

---

### Surjective

A function is surjective onto a codomain when every codomain value has a preimage.

The project must not claim surjectivity onto a closed interval endpoint that no finite `P` attains.

---

### Bijective

Both injective and surjective.

No projection should be called bijective until its exact domain and codomain have been fixed and both properties proved.

---

### Left Inverse

A function `g` is a left inverse of `f` when:

$$
g(f(x))=x
$$

A left inverse implies that `f` is injective.

---

### Right Inverse

A function `g` is a right inverse of `f` when:

$$
f(g(y))=y
$$

for the relevant `y`.

A right inverse implies surjectivity onto the stated domain of `g`.

---

### On the Image

A theorem restricted to outputs that actually arise from the forward map.

A right-inverse theorem may be valid on the image even when the map is not surjective onto a larger ambient interval.

---

### Wrapper Theorem

A theorem in the hackathon facade that restates or specializes an existing theorem under a clearer project-facing name.

A wrapper should add accessibility, not parallel mathematics.

---

### Corollary

A theorem derived from an existing result with minor additional reasoning.

---

### Bridge Lemma

A theorem translating between:

- two representations;
- two domains;
- two existing APIs;
- an internal DkMath theorem and the public hackathon surface.

---

### Facade

A small public-facing module layer that exposes a clean interface over a deeper library.

The hackathon Lean modules form a facade over DkMath.

---

### Thin Facade

A facade containing only:

- reused declarations;
- wrappers;
- small corollaries;
- demo facts.

It should not become another foundational library.

---

## 11. Visualization Terms

### Body Region

The visual region representing:

$$
P(P+2u)
$$

Its area is formalized only as a numerical expression in the minimum viable project.

---

### Gap Square

The visual square with side length `u` and area:

$$
u^2
$$

---

### Big Square

The completed visual square with side length:

$$
P+u
$$

and area:

$$
(P+u)^2
$$

---

### Area Preservation

The equality of total numerical areas before and after a visual rearrangement.

For the MVP, the formally verified statement is the arithmetic identity:

$$
P(P+2u)+u^2=(P+u)^2
$$

A stronger set-theoretic theorem about disjoint planar pieces is not required.

---

### Rearrangement

A visual transformation moving pieces without changing the displayed total area.

Unless Euclidean sets and congruence are formalized, rearrangement remains a visualization of the arithmetic identity.

---

### Factor Reveal

The animation step displaying:

$$
221=13\cdot17
$$

The factor reveal does not mean that geometry produced the factors.

---

### Lean Overlay

A visual display of a theorem statement, source code, or successful build result inside the animation or demo video.

The overlay should use the actual theorem name from the final branch.

---

### Visual Interpretation

A human-facing reading of a formally verified equality.

A visual interpretation is not an additional theorem.

---

## 12. Agent and Workflow Terms

### Codex

The repository-aware coding agent used to:

- inspect DkMath;
- implement Lean declarations;
- repair local proof failures;
- build modules;
- report genuine obstructions;
- implement Manim source when instructed.

Codex does not define the project scope.

---

### Wise Wolf

The AI collaborator responsible for:

- mathematical structural analysis;
- Codex instruction design;
- checkpoint review;
- terminology control;
- distinction between proved and interpretive claims;
- project narrative support.

---

### Checkpoint

A bounded unit of work with:

```text
one primary goal
permitted files
required theorem surface
verification gates
stopping conditions
report destination
```

Checkpoint numbers are never reused.

---

### Stage

A named subtask inside one checkpoint instruction.

Example:

```text
Stage A — repository inspection
Stage B — local theorem
Stage C — public wrapper
Stage D — verification
```

Stages do not authorize work beyond the checkpoint boundary.

---

### Repository Audit

An investigation-only session that searches for existing reusable APIs before source implementation begins.

The audit classifies declarations as:

```text
DIRECT
WRAPPER
COROLLARY
BRIDGE
MISSING
REJECTED
DANGEROUS
```

---

### Direct Reuse

Using an existing declaration without modification.

---

### Thin Wrapper

A small theorem or definition exposing an existing result through the hackathon-facing API.

---

### Specialized Corollary

A theorem obtained by specializing a more general existing result.

---

### Genuinely Missing Lemma

The smallest theorem required by the contract that is not already available through direct reuse, wrapping, or specialization.

---

### Genuine Obstruction

A missing mathematical invariant, incompatible representation, dependency barrier, or theorem boundary that prevents the requested checkpoint from continuing soundly.

A genuine obstruction is not merely:

- a typo;
- a missing import;
- a namespace mismatch;
- a local coercion failure;
- an easily repaired tactic failure.

---

### Lean Engineering Obstacle

A local implementation problem such as:

- type mismatch;
- elaboration issue;
- missing import;
- cast normalization;
- theorem lookup problem.

These should normally be repaired inside the current checkpoint.

---

### Mathematical Obstacle

A missing theorem, invariant, bound, construction, or hypothesis necessary for the requested result.

---

### Architecture Obstacle

A problem such as:

- dependency cycle;
- required reverse import;
- unsuitable domain choice;
- unavoidable duplication of a core abstraction.

---

### Stopping Rule

A condition requiring Codex to stop instead of expanding the task.

Typical form:

```text
Stop at the first genuine obstruction.
Report the smallest missing theorem.
Do not continue into adjacent research.
```

---

### Completion Condition

The exact facts or artifacts that must exist before a checkpoint is considered complete.

---

### Verification Gate

A required check such as:

```text
focused module build
aggregate build
no-sorry check
git diff --check
contract review
```

---

### Build-Gated Claim

A formal claim treated as part of the project only after Lean accepts the relevant module.

---

### No-Sorry

The property that the new target source contains no unfinished proof placeholders such as:

```lean
sorry
admit
```

Existing unrelated repository warnings do not invalidate a new checkpoint when the target is verified.

---

### Report

The factual Codex record of:

- files changed;
- declarations added;
- builds run;
- APIs reused;
- remaining obstruction;
- credit usage;
- next permitted action.

---

### Review

The separate Wise Wolf evaluation of:

- theorem meaning;
- contract compliance;
- dependency direction;
- API quality;
- true mathematical progress;
- next checkpoint.

---

### Accepted Checkpoint

A checkpoint whose implementation, theorem surface, and architecture are approved.

---

### Conditionally Accepted Checkpoint

A checkpoint whose mathematical work is accepted but which requires a minor correction in naming, documentation, imports, or presentation.

---

### Returned Checkpoint

A checkpoint requiring substantive revision because its theorem, architecture, or meaning does not satisfy the contract.

---

## 13. Context and Tracking Terms

### Stable Documentation Prefix

The fixed ordered set of project documents read before current instructions.

Its purpose is to maintain consistent project interpretation across Codex sessions.

---

### KV Cache

A model implementation mechanism that may allow repeated prompt prefixes to be processed efficiently.

The project cannot assume exact internal cache behavior.

Operationally, the project uses a stable document order to reduce repeated interpretation and terminology drift.

---

### Tracking Anchor

An intentionally empty UUID-named file linking a repository state to an originating research conversation.

Example:

```text
6a54173a-e5f8-83ee-9983-6932a7be858c
```

Rules:

```text
do not delete
do not rename
do not add content
do not repeatedly inspect after confirming emptiness
```

---

### Conversation Key

Another description for the tracking-anchor filename.

The filename, rather than file content, carries the metadata.

---

### Historical Document

A record of an earlier plan, report, or decision.

Historical documents should be preserved even when later documents correct them.

---

### Current Instruction

The checkpoint-specific instruction read after the stable documentation prefix.

---

## 14. Project Milestone Terms

### MVP

Minimum viable project.

The MVP contains:

```text
finite prime escape theorem
Cosmic Formula completion
concrete Lean demo
Manim visualization
recorded Codex workflow
submission package
```

---

### MVP Secured

The state in which the required Lean demo builds and a known-good commit has been preserved.

After this point, stretch work must not endanger the verified minimum.

---

### Preferred Milestone

A valuable but nonessential phase.

Examples:

```text
bounded rational projection
exact inverse
injectivity
```

---

### Stretch Milestone

A phase attempted only after the MVP is secure.

Example:

```text
DkReal interval reconstruction
```

---

### Public Theorem Surface

The small set of theorem names presented in:

- `Demo.lean`;
- README excerpts;
- screenshots;
- video overlays;
- submission text.

Names on the public surface should become stable before final recording.

---

### Submission Surface

The judge-facing project path:

```text
README
→ project summary
→ demo video
→ Lean build
→ Demo.lean
→ reports
```

---

## 15. Meaning Boundaries

### Arithmetic–Geometry Boundary

Verified arithmetic:

```text
P + u has prime divisors outside S
```

Verified algebra:

```text
P(P + 2u) + u² = (P + u)²
```

Visual interpretation:

```text
the completed square exposes a boundary whose value is P + u
```

Prohibited overstatement:

```text
the geometry creates the fresh primes
```

---

### Finite–Infinite Boundary

The project proves a theorem for one finite set `S`.

It may be applied to arbitrary finite prime sets.

It does not automatically formalize:

- an infinite iteration;
- prime-density results;
- a new proof of prime infinitude;
- global synchronization over all primes.

---

### Existence–Uniqueness Boundary

A fresh prime factor may exist without being unique.

The demo has two fresh prime factors.

No uniqueness claim is intended.

---

### Exact–Approximate Boundary

Exact inverse:

```text
the projected coordinate algebraically reconstructs P
```

Approximate reconstruction:

```text
nested intervals narrow to a unique integer candidate
```

These are distinct milestones.

---

### Formal–Interpretive Boundary

A Lean theorem proves its exact proposition.

Documentation may give a DkMath interpretation.

The interpretation must not add unstated mathematical consequences.

---

## 16. Terms Requiring Caution

### Creates

Avoid:

```text
the Gap creates new primes
```

Prefer:

```text
the completed boundary has prime factors outside the original finite set
```

---

### Generates

Acceptable when referring to an explicit algebraic construction.

Use cautiously when it could imply a causal prime-production theorem.

---

### New Prime

May mean:

```text
not in the original finite set
```

It does not mean:

```text
newly discovered by humanity
```

Prefer `fresh prime factor` in formal project writing.

---

### No Hole

A strong term that may mean surjectivity, interval coverage, or existence of preimages.

Do not use it as a theorem claim without an exact formal definition.

---

### Complete Inversion

Requires an exact declared domain, codomain, forward map, inverse map, and proved inverse laws.

Do not use after proving only an algebraic rearrangement.

---

### Reconstruction

Specify whether reconstruction is:

```text
exact
interval-based
unique
existential
computable
```

---

### Verifiable

Means that the specified formal claim can be checked by Lean or reproduced through documented commands.

It does not mean that every conceptual interpretation has been formalized.

---

### AI-Proved

Avoid as a standalone phrase.

Prefer:

```text
implemented by Codex and verified by Lean
```

The human–AI workflow and formal checker have distinct roles.

---

## 17. Prohibited Conflations

Do not conflate:

```text
fresh prime factor
with
primitive prime divisor
```

```text
linear Gap coordinate
with
square Gap mass
```

```text
prime-divisor exclusion
with
prime-divisor existence
```

```text
existence
with
uniqueness
```

```text
injectivity
with
surjectivity
```

```text
surjectivity onto the image
with
surjectivity onto an ambient closed interval
```

```text
arithmetic identity
with
formal Euclidean dissection
```

```text
visual explanation
with
formal proof
```

```text
finite theorem
with
infinite asymptotic theorem
```

```text
DkReal bridge
with
a new real-number construction
```

```text
Codex progress report
with
Lean verification
```

```text
a stopped genuine obstruction
with
a failed project
```

---

## 18. Preferred Public Phrases

Use:

```text
finite set of known primes
```

```text
product of the finite prime set
```

```text
coprime offset
```

```text
completed Cosmic Formula boundary
```

```text
fresh prime factor relative to the original set
```

```text
implemented by Codex and verified by Lean
```

```text
visualized with Manim
```

```text
bounded projection
```

```text
exact inverse on the image
```

```text
unique integer candidate under width less than one
```

```text
the first genuine missing bridge
```

---

## 19. Phrases to Avoid

Avoid:

```text
the formula invents primes
```

```text
the square proves prime distribution
```

```text
a new proof that primes are infinite
```

```text
the primitive prime 13
```

unless a primitive-divisor theorem is actually present.

Avoid:

```text
the inverse covers the entire closed interval
```

unless surjectivity including endpoints is proved.

Avoid:

```text
DkReal uniquely reconstructs P
```

until the complete bridge builds.

Avoid:

```text
Codex solved the mathematics
```

when Codex only implemented an already-fixed theorem contract.

Prefer a precise description of the agent’s contribution.

---

## 20. Lean Naming Guidance

Prefer standard names based on theorem meaning.

Examples:

```lean
prime_dvd_product_add_coprime_not_mem
exists_fresh_prime_factor
all_primeDivisors_fresh
cosmicCompletion
normalizedCosmicCompletion
projection_mem_interval
projection_leftInverse
projection_injective
demo_thirteen_fresh
demo_seventeen_fresh
```

Avoid declaration names based primarily on narrative terms such as:

```lean
escapeFromUniverse
primeCreation
cosmicPortal
gapMakesPrime
```

Narrative vocabulary belongs in documentation and visualization.

---

## 21. Demo Constants

The following values form the fixed public demonstration contract.

```text
demoPrimeSet:
  {2, 3, 5, 7}

demoP:
  210

demoU:
  11

demoBoundary:
  221

demoFreshFactors:
  13 and 17

demoBody:
  48720

demoGap:
  121

demoBig:
  48841
```

Relations:

$$
210\cdot232=48720
$$

$$
11^2=121
$$

$$
221^2=48841
$$

$$
48720+121=48841
$$

No public demo layer should silently change these values.

---

## 22. Glossary Maintenance

A new term should be added to this glossary when:

- it appears in multiple project documents;
- it appears in a public theorem name;
- it appears in narration;
- Codex might reasonably misinterpret it;
- it has both a formal and interpretive meaning.

A glossary change should state whether the term is:

```text
standard mathematics
existing DkMath
hackathon project terminology
process terminology
```

Terms should not be added merely because they appeared once in exploratory discussion.

---

## 23. Final Terminology Summary

The central project vocabulary is:

```text
S:
  the finite original prime set

P:
  the product of S

u:
  the coprime offset

P + u:
  the completed boundary

fresh prime factor:
  a prime divisor of P + u outside S

Body:
  P(P + 2u)

Gap:
  u²

Big:
  (P + u)²

Cosmic completion:
  Body + Gap = Big

projection:
  normalization into a bounded interval

inverse projection:
  reconstruction from that bounded representation

DkReal reconstruction:
  interval-based recovery and integer-candidate uniqueness

thin facade:
  the small hackathon API over existing DkMath

genuine obstruction:
  the first missing mathematical or architectural bridge

Lean verification:
  the final gate for formal claims
```

The project’s formal path is:

$$
P=\prod_{p\in S}p
$$

$$
\gcd(P,u)=1
$$

$$
q\mid P+u\Longrightarrow q\notin S
$$

together with:

$$
P(P+2u)+u^2=(P+u)^2
$$

The project’s interpretive path is:

```text
finite known-prime world
→ coprime completion
→ completed boundary
→ fresh prime factors
→ bounded projection
→ verified reconstruction
```

All project documents, Codex instructions, Lean declarations, Manim scenes, and submission materials must preserve the distinction between those two paths.
