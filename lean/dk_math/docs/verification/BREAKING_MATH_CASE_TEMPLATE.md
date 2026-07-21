# <Case Title>

Use this landing-page contract with the
[`provenance template`](PROVENANCE_TEMPLATE.md) and
[`demo contract template`](DEMO_CONTRACT_TEMPLATE.md).

## Title and Status

- **Project title:** `<title>`
- **Case name:** `<CaseName>`
- **Date opened:** `<date>`
- **Branch:** `<branch>`
- **Current status:** `<reported | under reconstruction | candidate formalization | verified | refuted | inconclusive>`
- **Status evidence:** `<exact theorem, build result, or review boundary>`

Status meanings:

- `reported`: an external claim has been recorded but not reconstructed.
- `under reconstruction`: formulas or assumptions are being transcribed and
  checked.
- `candidate formalization`: the Lean target is fixed, but verification is not
  complete.
- `verified`: Lean proves the exact stated formalization target.
- `refuted`: Lean proves the negation of the exact stated target or verifies a
  counterexample to it.
- `inconclusive`: the current evidence establishes neither verification nor
  refutation.

## Reported Claim

- **Source-language claim:** `<verbatim-short-claim or faithful paraphrase>`
- **Claim type:** `<identity | existence | obstruction | counterexample | classification | other>`
- **External status:** `<reported | published | peer reviewed | independently confirmed | unknown>`

Do not turn an external status into a Lean conclusion.

## Exact Formalization Target

- **Lean proposition:** `<exact proposition>`
- **Target identifier:** `<DkMath.Hackathon.<CaseName>.<targetTheorem>>`
- **Assumptions:** `<exact Lean binders or none>`
- **Difference from the reported wording:** `<description or not applicable>`

## Source Formula or Data

Record the exact formulas, tables, finite inputs, algorithms, or other data to
be encoded. Use stable labels and refer to the
[`provenance record`](PROVENANCE_TEMPLATE.md).

```text
<source formula or data>
```

## Independent Formalization Boundary

- [ ] Definitions were transcribed into Lean independently.
- [ ] Every imported mathematical assumption is named.
- [ ] External numerical or CAS output is not treated as an axiom.
- [ ] The exact boundary between transcription and new DkMath reasoning is
      documented.
- **Boundary summary:** `<summary>`

## Mathematical Objects

List exact Lean identifiers and their roles.

| Lean identifier | Type | Role |
| --- | --- | --- |
| `<DkMath.Hackathon.<CaseName>.<object>>` | `<type>` | `<role>` |

## Local Identities

List identities established directly from definitions, symbolic computation,
or small imported lemmas.

| Lean theorem | Exact proposition | Proof method |
| --- | --- | --- |
| `<DkMath.Hackathon.<CaseName>.<identity>>` | `<proposition>` | `<method>` |

## Explicit or Finite Witnesses

This section may describe collision points, finite arithmetic obstruction data,
an explicit construction, or `not applicable` for a purely symbolic identity.

| Witness identifier | Certified property | Finiteness or explicitness |
| --- | --- | --- |
| `<DkMath.Hackathon.<CaseName>.<witness>>` | `<exact proposition>` | `<description>` |

## Global Consequence

- **Lean theorem:** `<DkMath.Hackathon.<CaseName>.<consequence>>`
- **Exact proposition:** `<proposition>`
- **Derived from:** `<exact witness and identity identifiers>`
- **Interpretation limits:** `<what does not follow>`

## Summit Theorem

A summit may be a domain-specific theorem, a conjunction theorem, or another
ordinary Lean proposition. It need not be a structure.

```lean
#check DkMath.Hackathon.<CaseName>.<summitTheorem>
```

- **Exact proposition:** `<proposition>`
- **Why this is the summit:** `<short explanation>`

## Module Map

```text
DkMath/Hackathon/<CaseName>/
├── <module>.lean
└── Demo.lean

DkMath/Hackathon/<CaseName>.lean
DkMathTest/Hackathon/<CaseName>/CheckAxioms.lean
```

For each import edge, confirm that generic infrastructure does not import the
domain-specific project.

## Build Commands

Run from `lean/dk_math`:

```sh
lake build DkMath.Hackathon.<CaseName>
lake build DkMathTest.Hackathon.<CaseName>.CheckAxioms
```

- **Last verified date:** `<date>`
- **Result:** `<success | failure | not run>`
- **Relevant warnings:** `<warnings or none>`

## Axiom Audit Target

```lean
#print axioms DkMath.Hackathon.<CaseName>.<summitTheorem>
```

- **Audit file:** `DkMathTest/Hackathon/<CaseName>/CheckAxioms.lean`
- **Exact output:** `<paste exact output>`
- **Allowed foundations:** `<list>`
- **Failure signals:** `<sorryAx, project-specific axiom, or case-specific rule>`

## Trust Boundary

- **Lean proves:** `<exact formal conclusions>`
- **Lean assumes:** `<axioms and theorem assumptions>`
- **External sources report:** `<claims not established by provenance alone>`
- **Not certified by Lean:** `<priority, authorship, review status, etc.>`

## Provenance Link

Case record: `PROVENANCE.md`

Create it from [`PROVENANCE_TEMPLATE.md`](PROVENANCE_TEMPLATE.md).

## Demo Contract Link

Presentation contract: `DEMO_CONTRACT.md`

Create it from [`DEMO_CONTRACT_TEMPLATE.md`](DEMO_CONTRACT_TEMPLATE.md).

## Scope and Non-Goals

- **In scope:** `<items>`
- **Not in scope:** `<items>`
- **Claims explicitly not made:** `<items>`
- **Optional interpretation layers:** `<modules or not applicable>`

## Deferred Work

- `<future task>` — `<reason deferred>`
- Or: `None currently recorded.`

Deferred work is not part of the current verified status.

## Checkpoint Status

| Checkpoint | Primary goal | Status | Evidence |
| --- | --- | --- | --- |
| `<ID>` | `<goal>` | `<reported | in progress | complete | blocked | deferred>` | `<theorem/build/review>` |
