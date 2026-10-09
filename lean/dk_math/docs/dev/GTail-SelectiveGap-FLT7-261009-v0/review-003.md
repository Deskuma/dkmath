# Review 003 — selective GTail transport and conditional conservation

Date: 2026-10-09  
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`  
Decision: **APPROVED — Outcome B**

## Reviewed evidence

- `DkMath/Lib/Cosmic/GTailTransport.lean` (220 lines).
- `DkMathTest/CosmicFormula/GTailTransport.lean` (206 lines).
- `report-003.md`, `source-inventory-003.md`, current `ROADMAP.md`.
- Previous `GTailSelection` / `GTailFactor` and canonical `GTailPascal` contracts.

**Review is static:** examined pushed GitHub source and Codex's validation report. The reviewer did not independently run Lean or reproduce the local build and axiom output.

## Findings

1. `sumMovedIn` and `sumMovedOut` use the bounded active-index differences, correctly handling arbitrary finite S and T, including indexes outside 0..d.
2. `selectedBody_transport` splits the two active sets into their shared intersection and respective differences; all equations are additive and hold in any `CommSemiring` without cancellation.
3. `selectedGap_transport` correctly reverses the movement via bounded complements. `selected_balance_transport` derives from Step 001's exact balance rather than adding a redundant proof.
4. Insert/erase identities have the correct polarity: an entering term increases Body and leaves Gap, while an erased term leaves Body and enters Gap. Already-present and out-of-range indices are explicit no-ops.
5. `selectedBody_Ico_split_at` reuses `GTail_split_at`. Increasing r shrinks the selected Body, and the explicit factor `x^r` restores the absolute exponent of transferred terms.
6. `selected_modEq_of_dvd_moved` is honestly **conditional** on divisibility of *every* entering and leaving term. Its proof proceeds through divisibility of the movement sums and modular equality. The m=0 case is compatible with equality when all moved terms are zero.
7. The degree-seven endpoint test demonstrates `coeffGCD` changes from 7 to 1. The failed-modular-congruence test with x=u=1 establishes that unguarded congruence is not invariant. Both are expected observations, not contradictions.
8. Regression examples cover d=0, sparse overlapping sets, zero coordinates, out-of-range/no-op moves, equality/full/empty selections, interval split, and prime-modular transport.

## Validation evidence (Codex report; not independently rerun)

The reported commands:

```text
lake build DkMath.Lib.Cosmic.GTailTransport
lake build DkMathTest.CosmicFormula.GTailTransport
lake build DkMath.Lib.Cosmic.GTailFactor DkMathTest.CosmicFormula.GTailFactor
```

all exited 0. The test reports `#print axioms` on 12 public endpoints with exactly `[propext, Classical.choice, Quot.sound]`. No placeholder, extra axiom, or FLT import was found in the submitted source.

## Review decision and Step 004 guidance

**APPROVED with no blocking repair.**

The next task is degree-seven calibration, not FLT7 closure. Reuse Steps 001–003 to derive the Body/Gap forms and their exact polynomial factors. Separate a polynomial factorization true for every commutative semiring from any later claim about FLT7 counterexamples, ideal norms, or unit-power classes.

Do not claim that a quadratic form equals a norm in an arbitrary ring unless a norm map/carrier is explicitly given. The bivariate form `x²+xu+u²` may be labeled "Eisenstein norm-shaped"; an actual number-field norm bridge is a later, separately typed statement.

The key target is:

```text
selectedBody 7 (Finset.Ico 1 7) x u
  = 7*x*u*(x+u)*(x^2+x*u+u^2)^2
```

and its balanced reconstruction with selected Gap `u^7 + x^7`, checked through selection/factor/transport APIs. This does **not** prove FLT7.
