# BMV-005 — Second-Domain Verification Validation

Repository:

```text
Deskuma/dkmath
```

Branch:

```text
hackathon/breaking-math-jacobian-counterexample
```

Base:

```text
develop
```

## Goal

Validate the reusable Breaking Math Verification workflow on a second
mathematical domain that is not a collision counterexample.

Use the existing finite-prime escape result for `GN 5 1 1` as a finite
arithmetic obstruction case.

This checkpoint must demonstrate that the reusable workflow consists of:

1. domain-specific mathematical theorems;
2. a small summit certificate;
3. direct-alias or thin-composition Demo theorems;
4. a dedicated axiom audit;
5. instantiated verification, provenance, and Demo contracts.

Do not introduce a universal verification bundle.
Do not force this arithmetic case into `CollisionCertificate`.
Do not modify the Jacobian mathematics.
Do not create JAC-012.
Do not create a pull request or merge anything.
Do not inspect large raw conversation, Codex-session, TTS-workspace, or
ALL AGENT LOG files.

## Existing arithmetic API

The existing module is:

```text
lean/dk_math/DkMath/Hackathon/FinitePrimeEscapeGN5.lean
```

It currently provides at least:

```lean
theorem finitePrimeEscape_hits_GN5 :
    ∃ q,
      FreshPrimeFactor
        ({2, 3, 5} : Finset ℕ)
        (DkMath.CosmicFormulaBinom.GN 5 1 1)
        q

theorem freshPrimeFactor_GN5_eq_31
    {q : ℕ}
    (hq : FreshPrimeFactor
      ({2, 3, 5} : Finset ℕ)
      (DkMath.CosmicFormulaBinom.GN 5 1 1)
      q) :
    q = 31

theorem finitePrimeEscape_hits_clean_GN5_channel :
    ∃ q,
      Nat.Prime q ∧
      q ∣ DkMath.CosmicFormulaBinom.GN 5 1 1 ∧
      q ∉ ({2, 3, 5} : Finset ℕ) ∧
      ¬ q ^ 2 ∣ DkMath.CosmicFormulaBinom.GN 5 1 1

theorem not_fifth_power_of_prime_dvd_of_not_sq_dvd
    {N q : ℕ}
    (hqPrime : Nat.Prime q)
    (hqDiv : q ∣ N)
    (hqNoLift : ¬ q ^ 2 ∣ N) :
    ¬ ∃ x : ℕ, N = x ^ 5

theorem GN_five_one_one_not_fifth_power :
    ¬ ∃ x : ℕ,
      DkMath.CosmicFormulaBinom.GN 5 1 1 = x ^ 5
```

Inspect the current source before fixing exact proof terms or names.
Reuse the existing mathematics. Do not reprove `GN 5 1 1 = 31` by a large
new computation when existing results suffice.

## Target architecture

Prefer the following small case surface:

```text
lean/dk_math/DkMath/Hackathon/FinitePrimeEscapeGN5Certificate.lean
lean/dk_math/DkMath/Hackathon/FinitePrimeEscapeGN5Demo.lean
lean/dk_math/DkMathTest/Hackathon/FinitePrimeEscapeGN5/CheckAxioms.lean

lean/dk_math/docs/hackathon/finite-prime-escape-gn5-verification/
├── README.md
├── PROVENANCE.md
└── DEMO_CONTRACT.md
```

Do not restructure or rename the existing
`DkMath.Hackathon.FinitePrimeEscapeGN5` module.

If one of the two proposed new Lean modules is genuinely unnecessary, keep the
smaller architecture and explain the decision in the report. Do not create
empty or ceremonial files.

## Summit certificate

Add a theorem with the following intended meaning:

```lean
theorem finitePrimeEscapeGN5Certificate :
    Nat.Prime 31 ∧
    31 ∣ DkMath.CosmicFormulaBinom.GN 5 1 1 ∧
    31 ∉ ({2, 3, 5} : Finset ℕ) ∧
    ¬ 31 ^ 2 ∣ DkMath.CosmicFormulaBinom.GN 5 1 1 ∧
    ¬ ∃ x : ℕ,
      DkMath.CosmicFormulaBinom.GN 5 1 1 = x ^ 5
```

This is an intended theorem shape, not permission to duplicate the underlying
arithmetic proofs.

Construct it by thin composition of the existing finite escape, exact prime,
clean-channel, and non-fifth-power results.

If the existing theorem surface makes a logically equivalent conjunction more
natural, use that shape and document the exact difference.

## Demo surface

Expose a small ordered presentation surface. Candidate names are:

```lean
finitePrimeEscapeGN5Demo_prime
finitePrimeEscapeGN5Demo_divides
finitePrimeEscapeGN5Demo_noLift
finitePrimeEscapeGN5Demo_notFifthPower
finitePrimeEscapeGN5DemoCertificate
```

The Demo theorems must be direct aliases or projections/thin compositions of
completed theorems. Do not place substantial arithmetic proof search in the
Demo layer.

Do not import this case from root `DkMath.lean` in this checkpoint.

## Axiom audit

Create:

```text
lean/dk_math/DkMathTest/Hackathon/FinitePrimeEscapeGN5/CheckAxioms.lean
```

Audit at least:

```lean
#print axioms DkMath.Hackathon.finitePrimeEscapeGN5Certificate
#print axioms DkMath.Hackathon.finitePrimeEscapeGN5DemoCertificate
```

Also add focused `#check` or `example` statements confirming the exact public
propositions.

Report the exact axiom output. Do not summarize an empty audit as a guess.

## Instantiate the verification contracts

Use the reusable templates in:

```text
lean/dk_math/docs/verification/
```

Create a domain-specific case package under:

```text
lean/dk_math/docs/hackathon/finite-prime-escape-gn5-verification/
```

### README.md

Record:

- project status;
- exact Lean target;
- arithmetic object `GN 5 1 1`;
- explicit prime witness `31`;
- local no-lift obstruction;
- global non-fifth-power consequence;
- summit theorem;
- module map;
- build commands;
- axiom audit target and exact output;
- trust boundary;
- scope, non-goals, and deferred work.

### PROVENANCE.md

This is not an external breaking-news claim.

Record honestly that the case is an existing DkMath finite arithmetic result
used as a second-domain validation of the verification contracts.

Use explicit values such as `not applicable` or `unknown` rather than inventing
an external publication, author, priority, or review status.

Separate:

- existing DkMath arithmetic source;
- the new summit packaging;
- Demo aliases;
- axiom audit;
- any later Cosmic Formula interpretation.

### DEMO_CONTRACT.md

Record the exact theorem order and allowed claims.

A recommended presentation sequence is:

1. `GN 5 1 1` has a prime channel outside `{2,3,5}`;
2. the channel is exactly `31`;
3. `31` divides once but its square does not divide;
4. therefore the target is not a fifth power;
5. show the summit theorem and axiom audit.

Do not claim FLT5 or a general GN theorem from this finite case.

## Validation

Build the exact new or modified modules and the focused axiom audit.

Confirm:

- no Jacobian mathematics changed;
- no `CollisionCertificate` dependency was added to the arithmetic case;
- no root `DkMath.lean` import was added;
- no universal proof bundle or provenance Lean structure was introduced;
- Demo contains no heavy new proof;
- the documents use relative links and contain no fabricated metadata.

## Repository handoff protocol

Do not return a long report only in the Codex conversation.

Write the completed report to:

```text
lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/
  report-jacobian-BMV-005.md
```

The report title must be:

```text
BMV-005 Second-Domain Verification Validation
```

Required sections:

```text
Summary
Files Added or Changed
Existing Arithmetic Reused
Summit Certificate
Demo Surface
Axiom Audit
Verification Contract Instantiation
Dependency Direction
Non-Goals Preserved
Build Result
Changed Files
Outcome
```

At the end of the checkpoint:

1. write the report file;
2. commit all BMV-005 implementation, documentation, audit, and report changes;
3. push the commit to the current branch
   `hackathon/breaking-math-jacobian-counterexample`;
4. return only a short message containing the commit SHA, changed-file summary,
   outcome, and report path.

Do not merge and do not create a pull request.

## Outcomes

Outcome A:

```text
The finite-prime GN5 obstruction is packaged as a complete second-domain
verification case with summit theorem, Demo surface, audit, and contracts.
```

Outcome B:

```text
The arithmetic summit and audit are complete, but one documentation or Demo
boundary requires adjustment.
```

Outcome C:

```text
The existing arithmetic theorem surface is insufficient for a thin verification
package without adding new mathematics; stop and report the exact missing bridge.
```
