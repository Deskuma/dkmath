# GitHub Copilot Instructions for DkMath

## Project Overview

Project D.K. math is a research repository focused on mathematical theories and formal theorem proving using Lean 4. The primary goal is to formalize and prove theorems in Dynamic Harmonic Number Theory (DHNT) and related mathematical concepts through Lean 4 formalization.

This is a research repository that prioritizes preserving the proof construction process, not just the final results.

## Tech Stack

- **Primary Language**: Lean 4
- **Mathematical Library**: Mathlib v4.26.0 (from leanprover-community)
- **Build System**: Lake (Lean's build tool)
- **Documentation**: Markdown files (Japanese and English)
- **Version Control**: Git with special research-oriented branching strategy

## Repository Structure

- `/lean/` - Lean 4 mathematical libraries and related projects
  - `/lean/dk_math/` - Main Lean 4 mathematical library for Dynamic Harmonic Number Theory
    - `/DkMath/` - Core library modules
    - `lakefile.toml` - Lake build configuration
- `.copilot-commit-message-instructions.md` - Commit message guidelines (Japanese)

## Coding Guidelines for Lean 4

### General Principles

- Follow Lean 4 mathematical formalization best practices
- Prioritize mathematical rigor and formal proof correctness
- Use unicode notation where appropriate (`↦`, `∀`, `∃`, etc.)
- Keep function pretty-printing enabled (`pp.unicode.fun = true`)
- Maintain `relaxedAutoImplicit = false` to ensure explicit type declarations

### Lean Code Style

- Use descriptive theorem and lemma names that reflect their mathematical content
- Document major theorems and definitions with docstrings
- Organize related theorems and lemmas in logical groups
- Use consistent naming conventions:
  - Theorems: descriptive names (e.g., `pow_sub_pow_eq_mul_G`)
  - Lemmas: helper results with clear names (e.g., `card_translate`)
  - Definitions: clear mathematical terms (e.g., `Cell`, `Box`, `Big`, `Gap`, `Body`)

### File Organization

- Each major mathematical concept should have its own `.lean` file
- Group related concepts in subdirectories (e.g., `DkMath/RH/`, `DkMath/ABC/`)
- Main module file (`DkMath.lean`) should import all public-facing modules
- Keep test files separate (e.g., `test_theorem_picker.py`)

## Documentation Standards

### Language

- Primary documentation is in **Japanese**
- README files and research notes are primarily in Japanese
- Code comments may be in English or Japanese
- Mathematical notation is universal

### Documentation Requirements

- Each major module should have a corresponding README.md
- Research notes should include:
  - Branch references for tracking theorem development
  - Commit IDs for precise version referencing
  - Mathematical motivation and intuition
  - Formal theorem statements
  - Proof sketches where helpful

### Markdown Documentation

- Use clear headings and section structure
- Include mathematical formulas in LaTeX notation within `\[ \]` or `\( \)`
- Provide both formal and intuitive explanations
- Link related files and modules explicitly

## Git and Version Control

### Branch Strategy (Research-Oriented)

**Critical**: This repository uses a special Git workflow designed for mathematical research:

- **Never delete branches** - branches preserve the research process
- **main branch**: Stable, finalized results only. Never work directly on main.
- **feature branches**: Track theorem development, proof attempts, and refinements
  - Prefix conventions:
    - `thm/` - Theorem and lemma proofs
    - `gen/` - Generalizations and extensions
    - `exp/` - Experimental and exploratory work
  - Preserve full commit history (no squashing by default)
  - Keep branches after merging to preserve research history

### Commit Messages

Follow the guidelines in `.copilot-commit-message-instructions.md`:

- Write title in English, 50 characters or less
- Use action verbs with ": " prefix (e.g., "Add: ", "Fix: ", "Update: ")
- Include blank line after title
- Add detailed description (72 character line width)
- Include bulleted list of changes after blank line
- Reference file names and function/theorem names for clarity

## Testing and Validation

### Lean Code

- Ensure all Lean files compile without errors: `lake build`
- Verify theorems are properly proven (no `sorry` in final code)
- Test imports and dependencies resolve correctly
- Run `lake build` before committing changes

### Python Scripts

- If present, Python scripts should be tested independently
- Follow existing patterns in the repository
- Document any dependencies or requirements

## Project-Specific Concepts

### Dynamic Harmonic Number Theory (DHNT)

The core mathematical framework includes:

- **Cell spaces**: Dimensionless cell space `Cell d := Fin d → ℤ`
- **Cosmic Formula**: Big/Body/Gap decomposition
  - `Big (d x u) := Box (constVec d (x+u))`
  - `Gap (d u) := Box (constVec d u)`
  - `Body (d x u) := Big \ Gap`
- **Key theorems**: Power subtraction factorization, binomial equivalence

### Mathematical Domains

- Riemann Hypothesis work (`DkMath/RH/`)
- ABC Conjecture work (`DkMath/ABC/`)
- Polyomino structures (`DkMath/Tromino.lean`)
- Cosmic Formula variations (Linear, Geometric, Dimensional)

## Best Practices

### For Lean Development

- Always check that new theorems don't break existing proofs
- Build incrementally and test after each significant change
- Use `sorry` only temporarily during development, never in merged code
- Leverage Mathlib lemmas and avoid reinventing proven results
- Maintain compatibility with the specified Mathlib version (v4.26.0)

### For Research Documentation

- Link branches to research notes for traceability
- Update documentation when theorems are proven or refined
- Preserve proof development history in feature branches
- Include mathematical motivation alongside formal proofs

### For Repository Maintenance

- Keep `lean-toolchain` file updated with correct Lean version
- Update `lake-manifest.json` when dependencies change
- Maintain `.gitignore` to exclude build artifacts
- Respect the research-oriented branching model

## Security and Quality

- Never commit secrets or credentials
- Keep dependencies up to date for security
- Validate Lean proofs are complete and correct
- Review Mathlib version compatibility when updating
- Ensure all public theorems are properly documented

## Resources and References

- Mathlib documentation: https://leanprover-community.github.io/mathlib4_docs/
- Lean 4 manual: https://lean-lang.org/lean4/doc/
- This repository's branching strategy: See `/lean/README.md`
- Commit message guidelines: See `.copilot-commit-message-instructions.md`
