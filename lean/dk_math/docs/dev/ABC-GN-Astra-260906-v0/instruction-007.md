# instruction-007 — ASTRA deep reconnaissance on realized cubic modulus geometry

## Mission

This checkpoint is **ASTRA-007**.

The implementation campaign has reached a genuine research frontier.

LUNA-006 removed the profile-coordinate machinery from the remaining large
term.  The strongest current cubic endpoint is now of the form

```text
actual cubic 3/8 moment
  <=
small finite-Euler contribution
  +
sum M^(3/8)
```

where the final sum runs over the finite set

```lean
GNExcessCubicRealizedLargeModulusSpace X
```

of **distinct realized natural-number joint moduli**.

Every such modulus already has production Lean certificates:

```text
X + 1 < M <= 3 * (X + 1)^2

exists a,
  1 <= a <= X
  and
  M = GNNonExceptionalRepeatedPart 3 a 1
  and
  M | a^2 + 3*a + 3

for every prime q | M:
  q^2 | M
  q % 3 = 1
```

The research problem is now:

```text
How can one control

  sum M^(3/8)

over the distinct realized moduli?
```

The purpose of ASTRA-007 is **not** polished exposition and **not** routine
engineering.  Use maximum mathematical reasoning on this modulus geometry,
falsify weak routes quickly, and leave behind enough theorem-level evidence and
Lean scratch code that Codex Luna can formalize the surviving route later.

---

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
review-001.md
report-006.md
instruction-006.md
```

Then inspect current source, especially:

```text
DkMath/ABC/GNExcessCubicRealizedBoundary.lean
DkMath/ABC/GNExcessCubicRealizedModuli.lean
DkMath/ABC/GNExcessLargeBoundaryPacket.lean
DkMath/ABC/GNCubicOrientation.lean
DkMath/ABC/GNCubicPairedDepth.lean
DkMath/NumberTheory/GNThreeOrientation.lean
DkMath/NumberTheory/GNThreeQuadratic.lean
```

Treat current production Lean as authoritative.

Do not use `abc_main_axiom` as mathematical input.

---

# Critical operating mode — preserve results continuously

This task is deliberately different from Luna implementation checkpoints.

Previous deep-reasoning runs have sometimes spent nearly all available effort
on internal exploration and then reached the execution limit before writing
the useful mathematical findings to persistent files.

That failure mode is unacceptable here.

## Rule 1 — write findings as soon as they are learned

Create immediately:

```text
lean/dk_math/docs/dev/ABC-GN-Astra-260906-v0/report-007.md
lean/dk_math/docs/dev/ABC-GN-Astra-260906-v0/scratch-007.lean.txt
lean/dk_math/docs/dev/ABC-GN-Astra-260906-v0/numeric-007.py
lean/dk_math/docs/dev/ABC-GN-Astra-260906-v0/validation-007.txt
```

Do **not** wait until the end of the research pass to write these files.

Append or revise them throughout the investigation.

Whenever you establish any of the following, record it immediately:

- a new exact identity,
- a Lean-checkable lemma,
- a numerical counterexample,
- a failed conjecture,
- a useful modulus bound,
- a multiplicity observation,
- a promising descent map,
- a useful parametrization,
- an exact missing lemma,
- a branch that should be closed.

A partially organized but complete research log is more valuable than a
beautiful report that never gets written.

## Rule 2 — useful /tmp scratch must be copied into the campaign directory

You may use Sandbox paths such as `/tmp` for fast scratch work.

However, every scratch Lean argument that teaches us something useful must be
copied into:

```text
scratch-007.lean.txt
```

before moving on to a new major research branch.

Likewise, useful numerical experiments must be copied into:

```text
numeric-007.py
validation-007.txt
```

Do not leave the only copy of a useful proof experiment in `/tmp`.

## Rule 3 — `example` is enough

The Lean scratch does not need production theorem names or polished imports.

Prefer small replayable blocks such as:

```lean
example (...) : ... := by
  ...
```

or:

```lean
example : concrete_numeric_statement := by
  norm_num
```

The purpose is to leave Luna a mechanically checkable research certificate.

Do not spend Astra effort refactoring theorem names, docstrings, import order,
or public facade placement.

That is Luna work.

## Rule 4 — report facts, not only conclusions

For every serious attack branch, add a compact section to `report-007.md`
containing:

```text
Hypothesis / target
What was tried
What Lean or exact arithmetic proved
What numerical search found
Counterexample, if any
Status: OPEN / PROMISING / CLOSED / PROVED-IN-SCRATCH
Next missing lemma
```

Do this even if the branch fails.

A dead route with a concrete counterexample is a useful result.

---

# Budget discipline without quota visibility

Codex cannot reliably observe its remaining 5-hour quota or exact cost.

Therefore do not try to estimate the remaining percentage numerically.

Instead emulate an approximately 20% reserve through **research-phase limits**.

## Major-branch cap

Investigate at most **five major attack branches** in this ASTRA pass.

After each major branch:

1. write the result to `report-007.md`,
2. copy useful Lean scratch out of `/tmp`,
3. copy useful numeric experiments,
4. explicitly mark that branch as
   `OPEN`, `PROMISING`, `CLOSED`, or `PROVED-IN-SCRATCH`.

Do not start a sixth major branch in this pass.

This is the reserve mechanism.

## Early stop

Stop before the fifth branch if the desired result below is obtained.

Do not keep exploring merely because quota may remain.

## No polishing phase

There is no final prose-polishing phase in ASTRA-007.

Once the desired mathematical result is obtained, record:

- exact theorem shape,
- assumptions,
- proof idea,
- replayable Lean scratch,
- any numerical regression,

then stop.

Luna will clean and productionize it later.

---

# Desired result — stop condition

The preferred success condition is to obtain, without an ABC-equivalent hidden
assumption, a theorem-grade route that controls the realized large modulus term
at the scale needed by the moment argument.

Any one of the following counts as a successful ASTRA-007 stop condition.

## Success A — direct modulus-moment bound

A credible theorem shape such as

```text
sum M in GNExcessCubicRealizedLargeModulusSpace X,
  (M : ℝ)^(3/8)
<=
C * (X + 1)
```

for an explicit absolute constant `C`, or a stronger/sublinear estimate.

It does not need to be productionized, but it must have:

- a mathematically coherent proof route,
- no circular ABC-strength assumption,
- enough Lean scratch to validate the new algebraic/arithmetic core.

## Success B — reduction to an already controlled summable object

A theorem-grade reduction of the realized modulus moment to an existing DkMath
or standard finite sum whose linear-or-better bound is already proved or can
be obtained by routine Luna formalization.

The reduction must be genuinely stronger than the current profile/cardinality
bound.

## Success C — alternate large-boundary closure

A new theorem that bypasses the raw modulus moment and directly gives a
linear-or-better bound for the **actual realized large contribution**, for
example through:

- a sharp witness multiplicity theorem,
- paired-orientation compensation,
- a strict descent,
- a norm-factorization argument,
- a genuinely stronger arithmetic partition.

Again, the decisive new lemma must be recorded in replayable Lean scratch.

Once A, B, or C is reached, **stop further major exploration** and serialize
the result.

---

# If no success condition is reached

A negative ASTRA pass is still useful if it sharply narrows the frontier.

If all allowed branches fail, the final output must contain:

1. every closed route,
2. explicit counterexamples,
3. the strongest surviving theorem,
4. the smallest exact missing lemma,
5. the next branch recommended for a future Astra pass.

Do not disguise an unresolved frontier as progress.

---

# Research branch menu

The following branches are suggested because they arise naturally from the
current exact modulus API.

You do not have to use all of them.

Choose the most promising branches after inspecting the current code and
running small exact experiments.

---

## Branch A — powerful / squarefree complement decomposition

For a realized witness `a`, let

```text
F(a) = a^2 + 3*a + 3
M(a) = GNNonExceptionalRepeatedPart 3 a 1
S(a) = F(a) / M(a)
```

Investigate whether production definitions imply an exact decomposition with:

```text
F(a) = M(a) * S(a)
M(a) = full repeated prime-power part
S(a) squarefree
gcd(M(a), S(a)) = 1
```

Pay special attention to the exceptional prime `3`.

For `a = 3k` one has:

```text
F(a) = 3 * (3*k^2 + 3*k + 1),
```

suggesting `v_3(F(a)) = 1`.

If the full canonical decomposition is correct, determine the sharp easy bound
on `S(a)` coming from `M > X` and the quadratic height.

A useful expected scale is:

```text
S(a) = O(X).
```

Questions:

- Is `S(a)` exactly squarefree?
- Is `gcd(M,S)=1` exact?
- Can `M` be reconstructed from `F(a)` and `rad(F(a)))?
- Does summing by the small complement `S` reduce multiplicity?

Record exact formulas and counterexamples.

---

## Branch B — discriminant / norm geometry

Use:

```text
4 * (a^2 + 3*a + 3) = (2*a + 3)^2 + 3.
```

Thus for odd realized `M`:

```text
(2*a + 3)^2 ≡ -3 (mod M).
```

Investigate whether the fact that **every prime divisor of M is 1 mod 3 and
occurs at least squared** yields more than ordinary local root existence.

Possible viewpoints:

- roots of `x^2 + 3` modulo squareful moduli,
- Eisenstein integers / norm forms,
- `a^2 + 3a + 3` as a shifted norm,
- uniqueness or spacing of root addresses,
- conjugate factors and gcd control.

Important warning:

Do not mistake Hensel uniqueness for global rarity.  Astra-001 already showed
that arbitrary finite local depths can coexist.

We need a global restriction across **realized distinct M**, not merely local
lifting.

---

## Branch C — witness multiplicity and modulus spacing

The current formalization proves:

```text
profile -> modulus
```

is injective.

It does **not** prove:

```text
point -> modulus
```

is injective.

Investigate the actual multiplicity:

```text
#{ a ∈ [1,X] : M(a) = M }.
```

Questions:

- Is there a uniform small bound?
- Can two different `a` share the same full repeated part?
- Does the exact quadratic congruence give at most two witnesses modulo `M)?
- Since `M > X`, does interval length convert residue-class multiplicity into
  a strong pointwise bound?
- Does the **full repeated-part equality**, not mere divisibility, remove the
  second root?

Search numerically for collisions before proposing a theorem.

Any collision immediately falsifies point-to-modulus injectivity; record the
first small one.

---

## Branch D — count by squareful modulus / quadratic roots

Ignore the internal profile origin temporarily and upper-bound by a larger
arithmetic set:

```text
X < M <= 3(X+1)^2
M squareful
all q|M satisfy q ≡ 1 mod 3
exists a ≤ X with M | a^2+3a+3.
```

Determine whether the weighted sum

```text
sum M^(3/8)
```

over this larger set already admits a linear-or-better elementary estimate.

Potential tools:

- parameterization of squareful numbers,
- `M = u^2 v^3` type decompositions,
- root count of the quadratic modulo M,
- switching summation order `M ↔ a`,
- divisor bounds that exploit the exponent `3/8`,
- dyadic decomposition.

Do exact exponent arithmetic before committing to a route.

A route that only yields `O(X^(1+δ))` is not enough unless it introduces a
further compensating factor already present in the moment argument.

---

## Branch E — paired orientation / product identity after modulus extraction

Reconsider the two cubic orientations only at the new integer-modulus level.

For:

```text
F = GN 3 a b
G = GN 3 b a
```

production Lean already proves repeated-part coprimality and the classical
identity:

```text
F * G = 3*(a+b)^4 + (a*b)^2.
```

For the canonical `b=1` setting, investigate whether a large repeated modulus
on one side forces a useful restriction on the swapped repeated modulus or
residual complement.

Important known negative facts:

- both orientations can have repeated prime powers,
- both repeated moduli can be arbitrarily large,
- coprimality alone does not force one side small,
- arbitrary exact local depths can coexist.

Only pursue this branch if the **new extracted modulus/complement geometry**
adds something beyond those closed routes.

---

# Required numerical reconnaissance

Use exact integer arithmetic.

At minimum search enough small/medium `X` values to inspect:

- collisions `a₁ ≠ a₂` with the same realized repeated modulus,
- distribution of `M/X`,
- distribution of the complement `S = F/M`,
- number of distinct realized large moduli,
- empirical size of
  `sum M^(3/8) / X`,
- prime-factor patterns,
- whether large `M` correlates with small `S`,
- paired-orientation repeated parts if Branch E is pursued.

Persist the script in `numeric-007.py`.

Persist representative output and counterexamples in
`validation-007.txt`.

Numerics are for falsification and pattern discovery only.

Do not promote an empirical bound to a theorem without proof.

---

# Required Lean scratch output

The research pass must leave replayable Lean evidence.

At minimum, `scratch-007.lean.txt` should contain examples for every
nontrivial algebraic fact used in the recommended route.

Examples of useful scratch targets:

```lean
example (a : ℕ) :
    4 * (a^2 + 3*a + 3) = (2*a + 3)^2 + 3 := by
  ring
```

and, if proved:

```lean
example (...) :
    Nat.Squarefree S := by
  ...
```

```lean
example (...) :
    Nat.Coprime M S := by
  ...
```

```lean
example (...) :
    M ∣ a^2 + 3*a + 3 := by
  ...
```

```lean
example (...) :
    weighted_modulus_sum <= ... := by
  ...
```

The scratch may import current production modules.

Do not require scratch code to be public API quality.

---

# Hard boundaries

Do not:

- use `abc_main_axiom`,
- add `sorry`, `admit`, or a new axiom to production,
- create a renamed ABC-equivalent contract and count it as progress,
- infer global sparsity from Hensel uniqueness alone,
- assume point-to-modulus injectivity,
- assume every squareful divisor of the quadratic is realized,
- claim a bound from numerics alone,
- spend the pass polishing theorem names or documentation,
- silently discard failed routes.

If a conjecture fails, record the counterexample immediately and close that
branch.

---

# Required report structure

Maintain `report-007.md` continuously.

Use this structure:

```text
# ASTRA-007 — realized cubic modulus geometry

## Live result ledger
- [time/order independent] finding ...
- finding ...
- counterexample ...

## Current strongest surviving route
...

## Branch A — ...
Status:
Facts proved:
Lean scratch:
Numerics:
Counterexamples:
Missing lemma:

## Branch B — ...
...

## Decisive theorem candidate
Exact statement:
Assumptions:
Why it would close the frontier:
Lean evidence:
Remaining proof gap:

## Closed routes
...

## Recommended Luna production work
...

## Remaining frontier
...
```

Do not include branch HEAD hashes or commit hashes.

The report is a research notebook, not a polished paper.

---

# Verification

For every meaningful Lean scratch block, actually compile it against the
current branch before recording it as proved.

A convenient temporary file under `/tmp` is fine, but copy the successful
block into `scratch-007.lean.txt`.

If you add any production theorem during this Astra pass, keep it extremely
small and foundational, then run the focused module build and `lake build
DkMath.ABC`.

However, production changes are **not required**.

The expected default output is research documentation + replayable scratch.

---

# Final stop discipline

Stop the ASTRA pass immediately when one of Success A/B/C is reached.

At stop time, ensure that persistent files already contain:

- the theorem statement we want Luna to formalize,
- the proof strategy,
- every new exact identity,
- Lean scratch proving the key local steps,
- numerical regressions/counterexamples,
- assumptions and dependency boundaries,
- explicitly closed false routes.

Do not use remaining reasoning budget for stylistic cleanup.

If no success condition is reached within five major branches, stop anyway and
leave the exact narrowed frontier.

The value of ASTRA-007 is the **mathematical information preserved for the next
Luna pass**, not the elegance of the final prose.
