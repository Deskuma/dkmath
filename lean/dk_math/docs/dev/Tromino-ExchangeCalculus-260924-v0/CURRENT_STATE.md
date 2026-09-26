# Tromino Exchange Calculus — Current State

## Read this first

Current branch:

    research/Tromino-ExchangeCalculus-260924-v0

Current active checkpoint:

    TRM-043 — Actual Constructor Calibration Closure

Current instruction:

    instruction-042.md

Last fully accepted major theorem checkpoints:

- TRM-037: genus-zero F2 exactness
      im boundary2 = ker boundary1
- TRM-038: genus-zero dual-face conservation <-> zero holonomy
- TRM-039: tetrahedral local closure and triangular A/B/C normal form

Face-star progress:

- TRM-040:
  indexing, semantic three-way carrier, old/center regions,
  concrete actual-port constructors
- TRM-041:
  semantic crossing and semantic rotation
- TRM-042:
  actual dependent-Fin codec COMPLETE;
  both codec round trips COMPLETE;
  actual PortCrossing COMPLETE;
  actual PortLocalRotation COMPLETE;
  source-region proofs COMPLETE;
  descriptor-level crossing/rotation transport formulas COMPLETE.

Current exact blocker:

The pre-existing concrete constructors are not yet calibrated against
faceStarPortEncode.

Need exactly:

    encode (.oldEdge p)      = faceStarOldEdgePort I p
    encode (.radialOld p)    = faceStarRadialOldPort I p
    encode (.radialCenter p) = faceStarRadialCenterPort I p

Then derive:

- the three decoder constructor formulas;
- the three exact actual crossing formulas;
- the three exact actual rotation formulas.

Do not redesign the codec.

After this calibration closure:

1. prove old-region and face-center cyclicity;
2. package PortRotationSystem;
3. prove exact 3-step triangular face dynamics;
4. construct connected faceStarCombinatorialMap;
5. prove count formulas and Euler/genus preservation;
6. restrict subdivision colorings to the original map;
7. prove universal all-triangular reduction;
8. move to tetrahedral/Eisenstein realization.

Four Color theorem status:

    NOT PROVED.

Eisenstein status:

- eisensteinParity : TraceOneInt (-1) ->+ TrominoState verified;
- canonical nonzero Eisenstein direction parity image = {A,B,C};
- tetrahedral roll transport = V4 addition;
- global triangular-Port -> Eisenstein-lattice realization NOT YET constructed.

## Agent completion rule

Never report GREEN because local files build.

Before completion:

1. re-read the active instruction;
2. enumerate every mandatory acceptance item;
3. attach a concrete theorem/definition name to each;
4. if one item is missing, report Outcome P and name it.

Actual repository state overrides stale task-report repository status.
