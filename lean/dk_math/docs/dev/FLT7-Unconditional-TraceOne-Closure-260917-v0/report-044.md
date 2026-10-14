# FLT7TC-005R38 — common-prime Kummer residue obstruction

## Scope

This report records the R38 implementation and verification.  The checkpoint
starts from the R37 canonical `C,U,V` packet and stops at the checked local
Kummer residue condition and clash audit.  It does not claim a contradiction,
successor construction, descent, or FLT7 closure.

## Initial investigation

- R37 already exposes `c = 1` / `c > 1` arithmetic data through the canonical
  packet fields, including the gcd identity, reconstruction equalities, and
  `Nat.Coprime u v`.
- R36 prime allocation provides the singleton gap-prime support and the cyclic
  Galois orbit API needed for orientation checks.
- The residue-support layer supplies degree-one residue fields and the
  existing `common_norm_prime_mod_seven` theorem.
- The square-twist layer supplies the exact cyclic identity, coefficient
  projective classes, and nonzero global square roots.

## Implementation log

- Added `PrimeTraceOneDirectRealCubicCommonPrimeKummer.lean` with the
  canonical `C = 1` / prime-divisor split.  The `C = 1` branch exposes the
  immediate equalities `R = U^3`, `S = V^3`, `a = U*V`, coprimality, and the
  strict height inequality.
- For `q | C`, the production API derives `q | R`, `q | S`, and `q | a`,
  exposes the existing `q % 7 = 1 ∨ q % 7 = 6` support, and reuses the
  complete-split theorem.  The oriented prime theorem selects the unique gap prime above
  `(q)` and proves both rotated roots are outside it using the cyclic Galois
  action and singleton gap allocation.
- The residue-field reduction maps the R27 square-twist identity and uses the
  explicit witness `y = r1 * r2⁻¹` to prove the literal 14th-power ratio.
- The fixed unit `alphaUnit * alphaAddOneUnit` and the twist ratio both have
  projective class `(0,3)`.  The quotient is converted through
  `unit_isSeventhPower_iff_projectiveLog_eq_zero` into an exact global
  seventh-power correction.
- The resulting residue condition is packaged as
  `z^7 = evalP (alphaUnit * alphaAddOneUnit)`, and then as the cubic packet
  `beta^3 = 2*beta^2 + beta - 1` together with
  `z^7 = beta*(1+beta)` and `z ≠ 0`.
- R38 scratch calibration confirms the `q = 29`, `beta = 4` nonresidue case
  and the `q = 379`, `beta = 206` residue case with `29^7 = 194` in
  `ZMod 379`.  The checked surface therefore gives no universal
  contradiction for the `q % 7 = 1` branch; the public endpoint remains the
  residue-field theorem, with the finite `ZMod` examples retained in scratch.
- The existing-theorem clash search found no checked theorem that further
  excludes this fixed residue condition, the `q ≡ 1 mod 7` branch, or the
  `C = 1` branch.  No successor, descent, or FLT7 contradiction was added.

## Validation

- `lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicCommonPrimeKummer`
  passed sequentially.
- `lake build DkMath.FLT.Seven` passed after adding the facade import.
- The import-only API audit passed for all public R38 definitions and
  theorems.
- The axiom audit passed for the public branch, orientation, 14th-power,
  projective-class, correction, and beta-form theorems; only the standard
  `propext`, `Classical.choice`, and `Quot.sound` dependencies were reported.
- `lake env lean DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicCommonPrimeKummerR38Scratch.lean`
  passed with only linter warnings; the `q = 29` and `q = 379` checks are
  kernel-checked.
- The decisive-source forbidden-construct scan and whitespace checks were
  run for the production, facade, API, axiom, scratch, report, and roadmap
  files.
