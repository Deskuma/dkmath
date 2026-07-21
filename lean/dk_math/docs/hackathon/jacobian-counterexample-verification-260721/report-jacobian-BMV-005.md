# BMV-005 Second-Domain Verification Validation

## Summary

The existing finite-prime escape result for `GN 5 1 1` is now packaged as a
second-domain verification case. It demonstrates that the shared workflow does
not require a collision counterexample or a universal proof bundle.

## Files Added or Changed

Added:

```text
DkMath/Hackathon/FinitePrimeEscapeGN5Certificate.lean
DkMath/Hackathon/FinitePrimeEscapeGN5Demo.lean
DkMathTest/Hackathon/FinitePrimeEscapeGN5/CheckAxioms.lean
docs/hackathon/finite-prime-escape-gn5-verification/README.md
docs/hackathon/finite-prime-escape-gn5-verification/PROVENANCE.md
docs/hackathon/finite-prime-escape-gn5-verification/DEMO_CONTRACT.md
docs/hackathon/jacobian-counterexample-verification-260721/report-jacobian-BMV-005.md
```

No existing source file was modified.

## Existing Arithmetic Reused

The summit reuses:

```text
finitePrimeEscape_hits_GN5
freshPrimeFactor_GN5_eq_31
finitePrimeEscape_hits_clean_GN5_channel
GN_five_one_one_not_fifth_power
```

The existing clean-channel witness is repackaged as `FreshPrimeFactor`, then
the existing exactness theorem replaces its prime by `31`. No GN evaluation or
divisibility theorem is reproved.

## Summit Certificate

```lean
finitePrimeEscapeGN5Certificate
```

Its proposition is exactly:

```text
Nat.Prime 31
∧ 31 ∣ GN 5 1 1
∧ 31 ∉ {2,3,5}
∧ ¬ 31² ∣ GN 5 1 1
∧ ¬ ∃ x : ℕ, GN 5 1 1 = x⁵
```

## Demo Surface

```text
finitePrimeEscapeGN5Demo_prime
finitePrimeEscapeGN5Demo_divides
finitePrimeEscapeGN5Demo_noLift
finitePrimeEscapeGN5Demo_notFifthPower
finitePrimeEscapeGN5DemoCertificate
```

The first four are conjunction projections. The summit Demo theorem is a
direct alias.

## Axiom Audit

Exact output:

```text
'DkMath.Hackathon.finitePrimeEscapeGN5Certificate' depends on axioms:
[propext, Classical.choice, Quot.sound]

'DkMath.Hackathon.finitePrimeEscapeGN5DemoCertificate' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

No `sorryAx` or project-specific axiom appears.

## Verification Contract Instantiation

The case package contains a landing page, honest internal provenance record,
and ordered Demo contract. It distinguishes existing arithmetic, new summit
packaging, direct Demo aliases, axiom audit, and later interpretation.

## Dependency Direction

```text
FinitePrimeEscapeGN5
  ↓
FinitePrimeEscapeGN5Certificate
  ↓
FinitePrimeEscapeGN5Demo
  ↓
focused CheckAxioms
```

The case does not import `CollisionCertificate`, Jacobian modules, or a
universal verification bundle. Root `DkMath.lean` is unchanged.

## Non-Goals Preserved

- No new arithmetic theorem beyond thin summit packaging.
- No FLT5 or general GN claim.
- No Jacobian mathematics changed.
- No provenance structure in Lean.
- No root import, merge, or pull request.

## Build Result

Successful:

```text
lake build DkMath.Hackathon.FinitePrimeEscapeGN5Certificate
lake build DkMath.Hackathon.FinitePrimeEscapeGN5Demo
lake build DkMathTest.Hackathon.FinitePrimeEscapeGN5.CheckAxioms
```

Result: `Build completed successfully (8276 jobs).`

The build replayed an unrelated pre-existing `sorry` warning in
`DkMath.NumberTheory.ZsigmondyCyclotomicResearch`; the new case modules have no
warnings or `sorry` declarations.

## Changed Files

Seven new BMV-005 files are included. No unrelated tracked file changed.

## Outcome

**Outcome A:** The finite-prime GN5 obstruction is packaged as a complete
second-domain verification case with summit theorem, Demo surface, audit, and
contracts.
