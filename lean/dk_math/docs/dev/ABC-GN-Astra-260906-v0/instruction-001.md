# instruction-001 — orientation foundation + autonomous frontier attack

## Mission

ASTRA-000 established that the new cubic route is mathematically real.

This second run should **not** spend most of its budget merely replaying
ASTRA-000.  Promote the verified arithmetic that is genuinely reusable, then
use the remaining reasoning budget to push beyond the current frontier.

The main research objective is:

> Find a theorem, mechanism, or counterexample that materially advances the
> transition from cubic repeated-depth structure to a global ABC-relevant
> bound, counting principle, or descent.

You are explicitly encouraged to choose the most promising route yourself
after inspecting the current workspace and the ASTRA-000 evidence.

## Repository

```text
repository: Deskuma/dkmath
branch:     wip/ABC-GN-astra-260906-v0
campaign:
  lean/dk_math/docs/dev/ABC-GN-Astra-260906-v0/
```

Read first:

```text
README.md
ROADMAP.md
report-000.md
scratch-000.lean.txt
numeric-000.py
validation-000.txt
```

Then inspect current Lean source as needed.

Treat current source and successful Lean experiments as the source of truth.

## Confirmed starting facts from ASTRA-000

The following have already survived scratch Lean verification and should be
treated as established research leads rather than speculative guesses.

For coprime `a,b`:

```text
gcd (GN 3 a b) (GN 3 b a) ∣ 14
```

and consequently:

- no prime square divides both orientations,
- the actual non-exceptional GN-Wieferich prime sets are disjoint,
- the actual non-exceptional repeated parts are coprime under the positivity
  hypotheses needed by the present API.

The actual cubic target weight also admits a verified `t = 3/8` estimate:

```text
rootAddressCharge *
  exp ((3/8) * activeProfileMass)
<=
  (GNNonExceptionalRepeatedPart 3 a b : ℝ) ^ (3/8).
```

This is a target theorem, not a bound for the full
`GNExcessLargeBoundaryProfileSum`.

ASTRA-000 also falsified several tempting shortcuts:

- one orientation need not be squarefree,
- one orientation need not be Wieferich-free,
- both repeated moduli can simultaneously exceed the ambient interval scale,
- coprime paired moduli alone do not remove the CRT boundary `+1`,
- finite Hensel uniqueness does not by itself imply a global density bound.

Do not return to those disproved routes.

## Part I — productionize only the durable foundation

Promote the orientation arithmetic into a clean production module in the most
natural existing namespace / dependency layer.

The production surface should include the useful chain, with names and exact
hypotheses chosen to fit current DkMath style:

```text
cubic orientation algebraic identities
  ↓
gcd divides 14
  ↓
no common prime-square divisor
  ↓
Wieferich repeated-support disjointness
  ↓
coprimality of the actual repeated parts
```

Preserve the distinction between ordinary prime support and repeated support:
the prime `7` may divide both orientations once, while it cannot belong to
both repeated supports.

Use the ASTRA-000 regression examples where useful.

Also promote the cubic `3/8` target theorem **if it can be integrated cleanly
without consuming a disproportionate amount of the run**.  If the correct
home or API requires a small local refactor, use judgment.

Do not spend the run polishing wrappers or creating a large facade hierarchy.

## Part II — autonomous attack on the real frontier

After the durable foundation is in production, continue independently.

The unresolved frontier is not the single-target inequality.  It is the lack
of a mechanism that turns the local cubic structure into one of:

1. a useful bound for the relevant large-profile contribution,
2. a paired-orientation counting theorem with a genuine gain beyond the CRT
   boundary term,
3. a direct coupling between repeated-depth debt and
   `abcEpsilon` / `quality`,
4. a strict descent or transfer principle that makes persistent bad states
   impossible,
5. another mathematically stronger formulation you discover from the current
   source.

You are **not required** to follow the ROADMAP ordering if workspace evidence
suggests a better route.

Explore aggressively:

- derive new exact identities if they help,
- reparameterize the fixed-sum cubic pair if useful,
- inspect actual profile definitions rather than surrogate models,
- use finite exact search to falsify candidate global statements,
- use Hensel/CRT structure where it is genuinely informative,
- try Lean scratch theorems early,
- abandon dead routes quickly.

A negative result is valuable if it sharply removes a plausible strategy.

## Priority question

The strongest unresolved conceptual question is:

```text
How can the two facts

  repeatedPart(a,b) ⟂ repeatedPart(b,a)

and

  cubic target weight <= repeatedPart^(3/8)

be converted into information about the original ABC triple
that is stronger than a one-profile statement?
```

Do not assume the answer must be a profile sum.

If the natural structure is a descent, rigidity theorem, finite-state
obstruction, height tradeoff, or another invariant, pursue that instead.

## Freedom to continue

Do not stop merely because the orientation production theorem compiles.

If a promising line emerges, continue through several local lemmas or scratch
experiments in the same run.  Choose your own intermediate checkpoints and
module organization.

The goal of this Astra invocation is to maximize **new mathematical
information**, not to maximize the number of small commits.

You may commit multiple coherent implementation steps if useful.

## Hard boundaries

- Do not use `abc_main_axiom` as mathematical input.
- Do not hide an ABC-equivalent research contract behind a new name.
- Do not claim ABC is proved unless the axiom-backed endpoint has actually
  become unnecessary and the complete dependency audit supports that claim.
- Do not treat numerical experiments as proofs.
- Do not infer global sparsity from finite Hensel uniqueness alone.
- Preserve current completed ABC / GN APIs unless a refactor is clearly needed
  for the new theorem.

## Deliverable

Create:

```text
lean/dk_math/docs/dev/ABC-GN-Astra-260906-v0/report-001.md
```

The report should be concise but mathematically substantive.  Include:

- final branch HEAD,
- production declarations added,
- dependency / axiom audit,
- the strongest new theorem or strongest new obstruction discovered after
  productionization,
- counterexamples found,
- what changed in the strategic picture,
- the exact remaining blocker,
- recommendation for the next Astra invocation.

Classify the research result using whichever description is most faithful,
rather than forcing a predetermined Outcome A/B/C label.

## Success criterion

A successful run does at least one of the following:

- creates a genuinely new global or paired theorem beyond ASTRA-000,
- finds a viable descent/coupling mechanism and proves a nontrivial piece of it,
- substantially narrows the large-profile / ABC-quality obstruction,
- or kills a major remaining strategy with a decisive theorem/counterexample.

Productionizing ASTRA-000 alone is useful infrastructure, but by itself should
not be considered the main success of this run.
