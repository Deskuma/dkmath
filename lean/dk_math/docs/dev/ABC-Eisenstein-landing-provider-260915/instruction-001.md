# Instruction-001 — Recover Astra state and validate the ABC Eisenstein square-factor provider

## Base / working branch

Work only on:

```text
repository: Deskuma/dkmath
branch: research/ABC-Eisenstein-landing-provider-260915-v0
```

The branch contains an interrupted GPT-6 Astra Ultra investigation. Astra hit a rate limit before writing a final Outcome A/P/B verdict. Do **not** treat `report-000.md`'s `調査中` as the mathematical endpoint. The saved scratch files are later and materially stronger than the incomplete report.

Current research artifacts to read first:

```text
docs/dev/ABC-Eisenstein-landing-provider-260915/ABC_Eisenstein_landing_provider.md
docs/dev/ABC-Eisenstein-landing-provider-260915/report-000.md
docs/dev/ABC-Eisenstein-landing-provider-260915/scratch/ShellInventory.md
docs/dev/ABC-Eisenstein-landing-provider-260915/scratch/UFDProvider.lean
docs/dev/ABC-Eisenstein-landing-provider-260915/scratch/ShellAllocation.lean
docs/dev/ABC-Eisenstein-landing-provider-260915/scratch/IdealDescent.lean
docs/dev/ABC-Eisenstein-landing-provider-260915/scratch/LandingExamples.lean
docs/dev/ABC-Eisenstein-landing-provider-260915/scratch/Diagnostics.py
docs/dev/ABC-Eisenstein-landing-provider-260915/scratch/Diagnostics-results.json
```

Also inspect the current production owners imported by those files. Repository source and successful Lean builds are authoritative.

---

## 0. Recover readable persistent-memory / handoff material before coding

Astra's `ShellInventory.md` explicitly records that a workspace `MEMORY.md` was consulted around lines 471–479. Codex/Luna may also have readable persistent project notes of its own.

Before changing production code:

1. Locate **actual readable persistence files** in the workspace that may contain prior Astra/Codex notes, including where present:

```text
MEMORY.md
AGENT.md / AGENTS.md
SUMMARY.md
.codex/**
workspace/project notes
handoff / scratch notes created by previous model runs
```

2. Search those readable files for project-relevant terms such as:

```text
ABC
Eisenstein
landing
provider
UFDProvider
ShellAllocation
SquarefulPell
oddPart
evenPart
TraceOneInt (-1)
4535c76
a91b6cf
```

3. Do **not** fabricate memory and do not attempt to expose inaccessible hidden chain-of-thought. This step concerns only actual files / persistent notes that the environment permits you to read.

4. Write the recovered relevant factual/project notes to:

```text
docs/dev/ABC-Eisenstein-landing-provider-260915/memory-recovery-001.md
```

The report must state:

- every persistence file actually inspected and its path;
- relevant line ranges or headings when available;
- whether the material predates, duplicates, or extends the committed Astra artifacts;
- any uncommitted theorem idea, failed route, API name, build fact, or warning that is relevant to this provider;
- explicitly `NO ADDITIONAL RELEVANT MEMORY FOUND` if nothing beyond committed artifacts exists.

Do not edit or overwrite the persistence files themselves.

---

## 1. Central mathematical target

For a realized large-modulus cubic shell witness `a`, set

```lean
alpha := DkMath.Lib.NumberTheory.eisensteinCoord ((a : ℤ) + 2) 1
M := DkMath.ABC.GNExcessCubicFullRepeatedModulus a
S := DkMath.ABC.GNExcessCubicComplement a
T := oddPart M * S
d := evenPart M
```

Production shell arithmetic already gives the intended natural-number norm decomposition

```text
N(alpha) = T * d^2
Squarefree T
```

with `M = oddPart M * (evenPart M)^2` in the appropriate shell packet.

The interrupted Astra run found a much stronger candidate route than the original norm/lattice-only plan:

```text
Eisenstein EuclideanDomain / PID / UFD
        ↓
alpha = beta * gamma^2
Squarefree beta
        ↓ coefficient-one argument
Squarefree (norm beta)
        ↓ natural squarefree-square uniqueness
|norm beta| = T
|norm gamma| = d
```

The goal of this instruction is to decide whether that route is genuinely kernel-valid and, if so, promote the **minimal** reusable/provider layer to production.

This is not an ABC proof task and must not extend into factor counting, Mordell bounds, Helfgott–Venkatesh, or near-linear shell counting.

---

## 2. Phase A — independently replay every Astra scratch theorem

Run Lean directly on at least:

```text
docs/dev/ABC-Eisenstein-landing-provider-260915/scratch/UFDProvider.lean
docs/dev/ABC-Eisenstein-landing-provider-260915/scratch/ShellAllocation.lean
docs/dev/ABC-Eisenstein-landing-provider-260915/scratch/IdealDescent.lean
docs/dev/ABC-Eisenstein-landing-provider-260915/scratch/LandingExamples.lean
```

Use the repository's actual toolchain.

Do not merely trust that the source text looks valid. Record exact success/failure.

For each important theorem, record `#print axioms` or equivalent audit, especially:

```text
exists_squarefree_mul_sq
squarefree_norm_of_dvd_cubicCoord
exists_cubicCoord_squarefree_norm_mul_sq
exists_cubicCoord_nat_squarefree_norm_mul_sq
nat_squarefree_square_decomposition_unique
shell_squarefree_norm_allocation
exists_exact_factor_of_principal_ideal_factor
eisenstein_exact_factor_of_ideal_factor
```

If a scratch file fails after replay against the current branch, repair it **in scratch first** and explain why. Do not promote a theorem whose proof has not kernel-checked.

Also rerun `Diagnostics.py` and compare its deterministic output with `Diagnostics-results.json`. Numerical scans are evidence/regression only, never substitutes for the theorem.

---

## 3. Phase B — audit the key coefficient-one argument

The load-bearing nontrivial step is not generic UFD square extraction by itself. It is the claim that the squarefree residual `beta` has squarefree **integer norm** because `beta ∣ alpha` and the cubic coordinate has unit second coefficient.

Audit the proof in `UFDProvider.lean` line by line:

```text
Squarefree beta
→ Squarefree (conj beta)
→ if t*t | norm beta, then scalar t | beta
→ beta | alpha
→ scalar t | alpha
→ alpha.snd = ±1
→ t | 1
→ t is a unit
→ Squarefree (norm beta)
```

Check carefully:

- coordinate/sign convention of `eisensteinCoord`;
- use of `conj` and `traceOne_mul_conj`;
- casts `ℤ → TraceOneInt (-1)`;
- whether the squarefree multiplication lemma is applied in the correct direction;
- whether `beta ∣ alpha` follows from the produced equality with the exact orientation Lean uses;
- whether zero/unit corner cases are fully excluded;
- whether `Int.squarefree_natAbs` gives exactly the required natural squarefree statement.

If this argument is valid, say so explicitly in the final report: it is the mathematical reason the cubic coefficient-one family escapes the generic `norm divisibility is insufficient` obstruction.

If it is invalid, identify the exact failing proposition and classify the result as Outcome P or B rather than patching around it with an unproved assumption.

---

## 4. Phase C — compose the provider with the shell allocation

If Phase A/B succeeds, construct the minimal shell theorem whose mathematical content is approximately:

```lean
theorem GNExcessCubicRealizedLargeModulusShellWitness_exists_eisenstein_square_factor
    {X D a : ℕ}
    (ha : a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D) :
    ∃ beta gamma : TraceOneInt (-1),
      (norm beta).natAbs =
        oddPart (GNExcessCubicFullRepeatedModulus a) *
          GNExcessCubicComplement a ∧
      (norm gamma).natAbs =
        evenPart (GNExcessCubicFullRepeatedModulus a) ∧
      eisensteinCoord ((a : ℤ) + 2) 1 = beta * gamma ^ 2
```

The exact theorem name / namespace may be adjusted to repository conventions, but keep the statement mathematically honest and close to this target.

Preferred architecture if the proof naturally separates:

1. **generic reusable theorem** in a neutral Lib owner only if it is genuinely generic and not cubic/ABC-specific;
2. **ABC shell wrapper** in an application-owned module, likely near the existing cubic Eisenstein factor consequence modules.

Do not move FLT3's full Euclidean implementation merely to satisfy aesthetics. Reuse the existing instance if that is the current canonical source, but document the dependency. If a lower-level ownership refactor is genuinely required, stop and report it rather than performing a broad refactor in this instruction.

### Required composition

Use the already kernel-checked scalar uniqueness idea from `ShellAllocation.lean`:

```text
Squarefree B
Squarefree T
T*d^2 = B*G^2
G,d ≠ 0
-----------------
B = T and G = d
```

Thus the provider-produced natural norm factors must coincide with the canonical shell allocation.

Do not assume `M = N(gamma)^2`; the correct square root is `evenPart M` and the residual is `oddPart M * S`.

---

## 5. Phase D — determine the correct status of the ideal route

`IdealDescent.lean` suggests that ideal-level principalization is **not** a blocker because `TraceOneInt (-1)` already has a PID instance and any unit can be absorbed into the free residual `beta`.

Validate this scratch theorem, but do not make it the primary route if the element-UFD route is shorter.

The final report must explicitly answer:

```text
Is class-group / principalization / unit-sector data still required
for this cubic coefficient-one square-factor provider?
```

If the UFD route succeeds with existing instances, the expected answer is `no` for this provider, and the report should explain why this does not generalize automatically to arbitrary TraceOne carriers.

---

## 6. Phase E — production promotion rule

Promote to production **only** if all of the following hold:

1. the central scratch provider kernel-checks;
2. the squarefree-norm argument is independently audited;
3. the shell allocation theorem kernel-checks;
4. their composition proves the nontrivial prescribed-norm factorization;
5. no new `axiom`, `sorry`, `admit`, `unsafe`, or `native_decide` is introduced.

Do not promote the generic counterexamples/diagnostics as production API unless an existing regression module clearly needs them.

If successful, create the smallest production module(s), export through the appropriate ABC facade, and update downstream `GNExcessCubicEisensteinFactorConsequences` only where the new provider can remove an explicit factorization hypothesis without distorting theorem ownership.

Do **not** globally rewrite all conditional theorems. Prefer adding provider-backed corollaries/wrappers and leave useful low-level conditional receivers intact.

---

## 7. Required outcome classification

Return exactly one principal verdict in `report-001.md`.

### Outcome A — FACTORIZATION PROVIDER PRODUCTION-PROVED

Use only if the branch now contains a kernel-checked production theorem giving the shell-prescribed

```text
alpha = beta * gamma^2
|N beta| = oddPart(M) * S
|N gamma| = evenPart(M)
```

with no new project axiom.

### Outcome P — PRECISE BRIDGE REMAINS

Use if the Astra route is substantially valid but one specific theorem is still missing. State that missing proposition in exact Lean-shaped form and identify whether it belongs to generic UFD arithmetic, the coefficient-one norm lemma, or shell composition.

### Outcome B — ASTRA PROVIDER ROUTE FAILS

Use only if a concrete proof failure/counterexample shows that the proposed route cannot establish the prescribed factorization from current hypotheses.

Do not downgrade to B merely because of engineering/API friction.

---

## 8. Validation

At minimum, after any production promotion run focused builds for the new owner plus:

```text
lake build DkMath.ABC
lake build DkMath.Lib.NumberTheory.EisensteinLatticeLanding
lake build DkMath.Lib.NumberTheory.TraceOnePowerLanding
```

If the new production theorem depends on the FLT3 Euclidean instance, also build the relevant `DkMath.FLT.Three` owner/facade and record that dependency explicitly.

Run:

```text
git diff --check
```

Scan changed production Lean for:

```text
sorry
admit
axiom
abc_main_axiom
native_decide
unsafe
```

Audit axioms of the load-bearing new theorem(s). Distinguish inherited foundational dependencies (`propext`, `Classical.choice`, `Quot.sound`) from any project-specific assumption.

---

## 9. Required deliverables

Commit at least:

```text
docs/dev/ABC-Eisenstein-landing-provider-260915/memory-recovery-001.md
docs/dev/ABC-Eisenstein-landing-provider-260915/report-001.md
```

If Outcome A, also commit the minimal production Lean implementation and facade update.

`report-001.md` must contain:

- branch/head used;
- readable-memory recovery summary and link to `memory-recovery-001.md`;
- scratch replay table (file / result / axioms);
- exact theorem dependency graph;
- explanation of the coefficient-one squarefree-norm mechanism;
- exact canonical norm allocation `T = oddPart(M)*S`, `d = evenPart(M)`;
- role, if any, of ideals/PID/UFD;
- production files/theorems added;
- validation commands/results;
- principal Outcome A/P/B verdict;
- remaining ABC frontier after this checkpoint.

If Outcome A, the remaining ABC frontier must be stated conservatively. Closing this factorization provider does **not** prove ABC; expected later obligations still include factor counting / balanced-box sparsity, Mordell/integral-point counting machinery, and near-linear shell-count / final ABC closure.

---

## Stop condition

Stop after the provider checkpoint and its validation/report.

Do not continue into factor counting or the final ABC argument in this instruction. The purpose here is to turn Astra's rate-limit-interrupted discovery into a reproducible, kernel-checked production fact — or to identify the exact point where it fails.
