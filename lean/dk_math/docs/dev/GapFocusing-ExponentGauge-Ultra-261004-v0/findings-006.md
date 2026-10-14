# Instruction 006 findings

## Initial checkpoint: source audit

- Live HEAD: `832ef9c3b`; Instruction 005 is committed in `19ae0c5a8`.
- The initial working tree is clean.
- `ParitySafePairResidual` already proves `pairOverlap = supportExcess + residual` without full cover or positivity assumptions.
- `ParitySafeSecondCancellationRedundancyAudit` already proves the exact split `supportExcess = outsideSupportExcess + collisionLocalSupportCost`, and `outsidePair = outsideSupportExcess + outsideResidual`.
- Reuse these identities. The strongest direct localization therefore needs neither collision baseline nor depth residual capacity.
- The existing collision/fifth charge is a lower bound on local support cost. It cannot be reversed to infer collision counts from arbitrary excess.
- Instruction 006 names `lowerParitySafeFreshExcessChargeCount` and `lowerParitySafeFreshPair`; the actual production names are `lowerFreshSupportExcessChargeCount` and `lowerParitySafeFreshPairs`.

## Preliminary finite diagnostic (not proof)

An independent arithmetic enumeration of the actual candidate/support filters gives, on shells 21..40: candidate count 490, incidence count 418, support excess 106, pair overlap 137, residual pairs 31, uncovered candidates 178. Every actual support has cardinality at most three. These values require kernel calibration before any theorem-level conclusion.

The +38 bound is a lower bound on incidence excess. Replacing incidence on the RHS of a readable inequality by this lower bound is invalid. Audit exact elimination before deciding whether a strict new obstruction remains.

## Checkpoint: local bridge and exact localization

- `ParitySafeBlockLocalization` builds. The local `K-1 <= choose(K,2)` comparison includes K=0, and the shell comparison uses the existing star/residual identity.
- The exact mature split places the 38 in outside support plus collision support. Outside pairs dominate outside support; no collision baseline or depth residual term is needed in the sharper bound.
- Generic finite-block localization and independent-upper-capacity contradiction criteria are implemented in production quantities.
- Initial kernel calibrations build: A=490, I=418, E=106, Q=137, residual=31, and K<=3 everywhere in the main block. Consequently the collision surface and fifth surface are empty, collision support cost is zero, outside pair mass is137, outside support excess is106.
- Finite cover failure and a prime in some square cell n=21..40 have been formalized through the existing cover/escape bridge. The same failure is also proved without the new temporal bound: A=490>I=418. This is not evidence that the +38 is necessary or that cancellation supplies a new obstruction.

## Checkpoint: readable elimination

The exact full-cover block identity I=A+E changes the readable frontier into `2O+11C+2F <= 3E+2L`. The new lower bound E>=38 cannot replace E on this RHS. At the strongest mature second cancellation, the exact existing identities reduce the inequality to `2Terminal+9C+3F <= Eoutside+3S`, already implied by the terminal and collision support charges.

Preliminary arithmetic enumeration gives Near=0, depth=209, Fourth=14, L=223. Thus the incidence-eliminated support frontier has slack490, whereas evaluating the full-cover incidence frontier on the actual quantities gives a deficit44. Both require final kernel calibration. The latter already detects finite cover failure before adding38.

## Checkpoint: LowCost calibration and actual finite cover failure

- All four production capacities are now kernel checked: Near=0, depth=209, Fourth=14, LowCost=223.
- The readable full-cover frontier evaluates to `1744 <= 1700`, false by44. `mainBlock_not_fullyCovered_from_readable_frontier` refutes the simultaneous cover hypothesis through the existing readable theorem alone.
- The same block already fails candidate/incidence balance (`490 > 418`). The positive temporal38 is not necessary for either refutation. It is therefore inappropriate to call this a new 38-driven cancellation breakthrough.
- The incidence-eliminated support inequality is `274 <= 764`, slack490. Its exact equality is checked.
- The actual uncovered-candidate ledger has178 seats: `418+178=490+106`.
- Actual collision and fifth surfaces, collision support cost, and depth residual capacity all vanish. The conditional38 localizes entirely outside collisions; actual outside excess106 and outside pairs137 comfortably absorb it (room68 and99 respectively).
- The existing n=13,r=6 mixed-support example proves a positive fresh cost without any collision recipient. An algebra-only regression records why an RHS variable cannot be replaced by its lower bound.

## Checkpoint: outcome distinction

The finite block and a prime in one of its square cells are proved, but were already accessible from the mature ledger. The classification for the requested *new localization/cancellation improvement* is Outcome C: no new positive38 obstruction survives elimination. The actual uncovered-candidate deficit is the non-cancelling currency. A generic contradiction consumer is implemented for an independently established localized upper bound below mandatory charge, and another for an incidence upper bound below candidate demand plus mandatory charge.

## Final checkpoint: strongest ledger, verification and decision

- Terminal key normalization and enumeration are kernel checked: terminal17, LowCost-after-unused14. The strongest mature reduced support-charge inequality is34<=106 with exact slack72.
- Final focused + regression + facade + root build passes,10372 Lake jobs including dependency replays. All new006 source is warning/error free. The root replays the five pre-existing research warnings documented in validation.
- Complete #print axioms coverage is15 production +39 regression =54/54. Every dependency set is contained in the standard three axioms; no sorryAx or added axiom.
- Changed production and regression forbidden-token scans have zero matches. Tracked and new-file whitespace checks pass; new006 documentation links resolve.
- Final report answers all nine questions and distinguishes the proved finite block failure from the absence of a new38-dependent cancellation obstruction.

Outcome C — SUPPORT EXCESS IS ABSORBED BY CURRENT CANCELLATION
