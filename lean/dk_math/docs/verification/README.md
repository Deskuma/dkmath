# DkMath Verification Project Contracts

This directory contains reusable contracts for independently formalizing a
reported mathematical claim. They were extracted from a completed verification
case, but are intentionally independent of any one mathematical domain.

Start a new case with:

- [`BREAKING_MATH_CASE_TEMPLATE.md`](BREAKING_MATH_CASE_TEMPLATE.md) for the
  project landing page and theorem pipeline;
- [`PROVENANCE_TEMPLATE.md`](PROVENANCE_TEMPLATE.md) for source and
  reconstruction records;
- [`DEMO_CONTRACT_TEMPLATE.md`](DEMO_CONTRACT_TEMPLATE.md) for the stable public
  presentation surface.

## Contract boundaries

Keep these layers visibly separate:

1. **Mathematical source claim** — what an external source reports.
2. **Independent DkMath formalization** — the exact statement encoded in Lean.
3. **Finite or explicit witnesses** — concrete inputs, computations, or
   obstruction data used by the proof.
4. **Summit theorem** — the selected public theorem representing the completed
   verification result.
5. **Axiom audit** — the trust boundary reported by `#print axioms` for selected
   summit theorems.
6. **Provenance metadata** — where formulas and claims came from, including
   missing or uncertain information.
7. **Scope and non-goals** — what the project does not establish.
8. **Public Demo surface** — short, stable theorem aliases for readers and
   presentations.

Lean verifies theorem terms, not external publication history. Provenance
records the source of a claim and its formulas; it is not a kernel-checked proof
of authorship, priority, peer review, or independent confirmation. An axiom
audit records the trust boundary of selected Lean theorems, not source status.

Demo modules should expose direct aliases or thin compositions of completed
theorems. They should not recompute expensive proofs or conceal new mathematical
work. A case may use a domain-specific theorem or certificate shape; no
universal proof bundle is required.

Optional interpretation layers, including Book of Magic bridges, belong after
the core certificate and must remain separately identified.

The contracts support explicit collision counterexamples, finite arithmetic
obstructions, concrete identity verification, and future externally reported
claims. A project should omit inapplicable layers instead of filling them with
artificial abstractions.

## Recommended layout

```text
DkMath/Hackathon/<CaseName>/
├── Basic.lean
├── Objects.lean
├── LocalIdentities.lean
├── Witnesses.lean
├── Consequences.lean
├── Certificate.lean
└── Demo.lean

DkMath/Hackathon/<CaseName>.lean
DkMathTest/Hackathon/<CaseName>/CheckAxioms.lean

docs/hackathon/<case-name>-<date>/
├── README.md
├── PROVENANCE.md
├── DEMO_CONTRACT.md
└── roadmap.md
```

Only create layers that the case actually needs. Transport, normalization, or
interpretation modules are optional and should have one-way dependencies from
generic infrastructure toward the domain project, never the reverse.
