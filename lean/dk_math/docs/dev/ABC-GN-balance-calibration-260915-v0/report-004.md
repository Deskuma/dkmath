# ABC/GN Balance Calibration — Checkpoint 004

## Scope and outcome

This report treats `instruction-004.md` as the bounded checkpoint contract and
keeps the BCAL-003 sign convention
`Q_q = (2 - v_q) * log q`.  No Hensel transport, mutation, monotonicity,
descent, optimality, shell counting, numerical optimization, ABC inequality,
new axiom, or uniform joint contract is introduced.

Outcome B — PARTIAL BRIDGE.  The exact three-layer bridge is available for the
non-exceptional GN part.  The existing full cubic complement can be identified
with it only away from the exceptional prime `3`; an unconditional equality to
the existing full cubic complement would silently reinsert an exceptional
single layer omitted by the BCAL channel.

## Source audit

Working branch: `research/ABC-GN-balance-calibration-260915-v0`.

The existing production API was checked before implementation:

| Item | Existing source and result |
|---|---|
| `repeatedPrimePowerPart` | `DkMath/ABC/GNExcessLargeBoundaryPacket.lean:30`; product of `q^v` over `v≥2`, retaining full repeated exponents |
| `repeatedPrimePowerPart_factorization` | `.../GNExcessLargeBoundaryPacket.lean:46`; exact factorization support/exponent theorem |
| repeated-support factorization support | `.../GNExcessLargeBoundaryPacket.lean:117`; exactly the `v≥2` support |
| `piSqRad` | `DkMath/ABC/TailRadicalBasic.lean:164`; one copy of each prime with `v≥2` |
| `twoTail` | `DkMath/ABC/SquareTailBasic.lean:223`; product of `q^(v-2)` over the full support |
| three-way shell decomposition | `.../SquareTailBasic.lean:242` and `...:371`; `n = piSqRad(n) * rad(n) * twoTail(n)` |
| repeated-part decomposition | `DkMath/ABC/GNExcessLargeBoundaryPacket.lean:192`; `repeatedPrimePowerPart = piSqRad^2 * twoTail` |
| non-exceptional GN part | `DkMath/ABC/GNLegacyTailCountingBridge.lean:50,55,125`; full exponent on non-exceptional support and its factorization support |
| valuation excess bridge | `.../GNLegacyTailCountingBridge.lean:151,196`; excess equals the `piSqRad` log plus `twoTail` log |
| cubic full complement | `DkMath/ABC/GNExcessCubicComplement.lean:150,175`; existing complement is squarefree but is formed from the full cubic value |

The audit confirms that repeatedness alone is not imbalance: `v=2` is the
`piSqRad^2` pivot and contributes zero.  `twoTail` retains exactly the
over-depth exponent `v-2` for `v≥3`; its `v=1,2` factors are `q^0`.

## Implemented exact bridge

The production module is
`DkMath/ABC/GNBalanceCubicShell.lean`.

- `GNNonExceptionalSingleLayer` (`:34`) is the existing repeated-part
  complement applied to `GNNonExceptionalPart`.
- `repeatedPrimePowerComplement_factorization` (`:40`) proves that this
  complement retains exactly primes with valuation `v=1`.
- `twoTail_eq_overDepthProduct` (`:70`) exposes the `v≥3` over-depth product.
- `GNChannelBalance_eq_log_singleLayer_sub_log_twoTail` (`:114`) proves the
  generic exact bridge:

  `GNChannelBalance = log(single layer) - log(twoTail)`.

  The proof removes the neutral `piSqRad^2` pivot using the existing exact
  repeated-part decomposition and the existing valuation-excess identity.

## Cubic specialization and prime `3`

For `F(a) = GN 3 a 1 = a^2 + 3*a + 3`, the existing theorem
`not_nine_dvd_GN_three_one_value` (`GNExcessCubicComplement.lean:39`) gives
`v₃(F(a)) ≤ 1`.  The new theorem
`GN_cubic_three_factorization_eq_one_of_dvd` (`:206`) records the sharp
conditional statement `3 ∣ F(a) -> v₃(F(a)) = 1`.  Thus prime `3` never enters
the repeated part, but it may remain as a single factor in the full cubic
complement.

The theorem
`GNChannelBalance_cubic_eq_log_complement_sub_log_twoTail` (`:258`) therefore
uses the explicit condition `¬ 3 ∣ GN 3 a 1`.  Under that condition, the
existing `GNExcessCubicComplement` is exactly the BCAL single layer and the
balance rewrite is kernel checked.  Without it, the existing full complement
contains the exceptional `3` single layer while `GNChannelBalance ... 3`
intentionally omits `q ∣ 3`; that is the precise information mismatch behind
Outcome B.

The existing theorem
`GNNonExceptionalRepeatedPart_three_one_eq_repeatedPrimePowerPart`
(`GNExcessCubicComplement.lean:49`) was reused; no cubic repeated-part
definition was duplicated.

## Not obtained and next checkpoint value

No unconditional bridge to the existing full cubic complement was asserted.
To obtain one, the API would need either an explicit exceptional-support log
correction or a separate shell coordinate for the non-exceptional single
layer.  The missing information is not over-depth: it is the exceptional
prime-3 single layer.  Hensel/depth-step transport remains a possible later
investigation, but is not justified or formalized by this checkpoint.

## Validation

The following validations passed:

- `lake env lean DkMath/ABC/GNBalanceCubicShell.lean`
- `lake build DkMath.ABC.GNBalanceCubicShell`
- `lake build DkMath.ABC`
- forbidden-token scan on the new module for `sorry`, `admit`, `axiom`, and
  `unsafe`: no matches;
- trailing-whitespace scan: no matches;
- `git diff --check`: passed.

`#print axioms` on both
`GNChannelBalance_eq_log_singleLayer_sub_log_twoTail` and
`GNChannelBalance_cubic_eq_log_complement_sub_log_twoTail` reported only
`[propext, Classical.choice, Quot.sound]`; no `sorryAx` was introduced.  The
facade build replayed the pre-existing warning at
`DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147`, outside this
checkpoint.
