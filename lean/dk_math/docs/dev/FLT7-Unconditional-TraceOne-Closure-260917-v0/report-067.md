# FLT7TC-005R61 implementation report

## Scope

Implement `instruction-067.md` against the current R60 workspace. The
orientation result remains the two-case statement
`Q = sigma • P0` or `Q = sigma^2 • P0`; no reciprocity theorem or final FLT
closure is added.

## Progress log

### 2026-09-21 — initial inspection

- Read `instruction-067.md`.
- Confirmed the existing R60 quotient/oriented-gap theorem and the existing
  `currentBeta` phase API.
- Started a separate R61 residue-kernel module so the existing heavy real
  cubic module is not enlarged.
- Added `SevenRealCubicCurrentResidueKernel.lean` with the neutral ZMod
  kernel-uniqueness lemma, the exact `f0/f1/f2` and quotient zero-kernel
  characterizations, their `Ideal.comap` packages, and the orientation-carrying
  evaluation-map dichotomy.
- Focused build passed for
  `DkMath.FLT.Seven.SevenRealCubicCurrentResidueKernel`.

### 2026-09-21 — orientation ratio and degree-six interpretation

- Added `SevenRealCubicCurrentOrientationRatio.lean` as a separate module.
- Proved the direct `f0` gap-zero factorization, the rotated `f0` transport,
  and the nonzero three-point orbit fields required by the current orientation
  packet.
- Added the unit-valued gap ratio `currentGapDelta`; proved the two orientation
  laws
  `tau = currentGapDelta` and `tau = currentGapDelta⁻¹`, according as the
  quotient prime is `P1` or `P2`.
- Proved `currentGapDelta ^ 7 = 1`, `currentGapDelta ≠ 1`, and
  `orderOf currentGapDelta = 7`.
- Added the cyclotomic ratio orientation law and the current/conjugate
  degree-six kernel interpretation. The kernel statement uses the packet's
  own real evaluation map on both sides and does not assert an orientation
  distinction.
- Focused build passed for
  `DkMath.FLT.Seven.SevenRealCubicCurrentOrientationRatio`.

### 2026-09-21 — Kummer phase sieve verification

- Added `ScratchR61Phase.lean` and verified the first order-seven polynomial
  identity without `sorry`.
- Added `SevenRealCubicCurrentKummerPhaseSieve.lean` with `phaseBeta`,
  `phaseKummer`, both order-seven identities, inversion invariance, the
  reverse-square seventh-root extraction, and the equivalences of seventh-power
  existence for phases 1↔2 and 2↔3.
- Focused build passed for
  `DkMath.FLT.Seven.SevenRealCubicCurrentKummerPhaseSieve`.
- Added all three R61 production modules to `DkMath.FLT.Seven`.

### 2026-09-21 — normalized Kummer support and finite sieve

- Added the normalized current-prime support theorem: the global seventh-power
  correction and the current phase alignment produce a nonzero `z : ZMod q`
  with `z ^ 7 = phaseKummer (currentGapDelta a b) 1`.
- Added `SevenKummerCompatiblePrime` in a kernel-computable form using
  `r ^ 7 = 1` and `r ≠ 1`; the current order-seven ratio supplies these fields.
- Replaced the sieve-side field inverse by the structural inverse in the finite
  unit group. This made the finite obstruction executable by ordinary `decide`
  without `native_decide`.
- Proved the finite exclusions for
  `29, 43, 71, 113, 127, 197, 211, 239, 281, 337` by `decide`. The focused
  module build passed after the finite computation (325 seconds, 9181 jobs).
- Added the bounded classification of primes `q < 379` with `q % 7 = 1`, and
  connected it to the `q ≥ 379` compatibility lower bound.

## Scratch / verification

Results will be appended after each focused Lean check.

### 2026-09-21 — R61 endpoint verification

- Added `prime_mod_seven_one_lt_379_mem` by bounded `interval_cases` and
  finite arithmetic normalization.
- Added `sevenKummerCompatiblePrime_ge_379`,
  `directOrbitCommonPrime_q_ge_379`,
  `directOrbitCommonFactor_c_ge_379`, and
  `directOrbitCommonFactor_height_ge_379`.
- The final focused build of
  `DkMath.FLT.Seven.SevenRealCubicCurrentKummerPhaseSieve` passed:
  `Built ... (304s)`, 9181 jobs.
- Removed the temporary finite-classification scratch files after verification;
  retained `ScratchR61Phase.lean` as the reusable phase-identity scratch.
- Fixed the new residue-kernel linter findings (`simp` in place of unnecessary
  `simpa`, and the two `Gal(Field/ℚ)` spacing issues).

The implemented endpoint is Outcome B.  The phase-independent status is
proved, but no phase invariance argument is promoted to a `C > 1` closure, and
no reciprocity or unbounded prime argument is introduced.

### 2026-09-21 — facade and axiom audit

- The public facade `DkMath.FLT.Seven` built successfully: 9267 jobs.
- `ScratchR61AxiomAudit.lean` checked the neutral kernel uniqueness,
  order-seven gap ratio, normalized Kummer support, `q ≥ 379` sieve bound, and
  height bound. Their reported axioms are only the expected
  `propext`, `Classical.choice`, and `Quot.sound`; no project axiom or
  `sorryAx` occurs.
- The forbidden-construct scan over the three production modules and phase
  scratch found no `sorry`, `sorryAx`, `admit`, `unsafe`, `native_decide`, or
  `axiom` occurrence.
- `git diff --check` passed.
