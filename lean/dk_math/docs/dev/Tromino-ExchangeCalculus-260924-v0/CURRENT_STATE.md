# Tromino Exchange Calculus — Current State

## Read this first

Current branch:

    research/Tromino-ExchangeCalculus-260924-v0

Current active checkpoint:

    TRM-044 — Face-star cyclic rotation and triangular face dynamics

Current instruction:

    instruction-043.md

Last fully accepted theorem checkpoints:

- TRM-037:
  genus-zero F2 exactness
- TRM-038:
  genus-zero dual-face conservation <-> zero holonomy
- TRM-039:
  tetrahedral local closure and triangular A/B/C normal form
- TRM-043:
  actual constructor calibration closure

Face-star status now verified:

- explicit face/face-port indexing;
- semantic three-way carrier;
- old/center region split;
- actual port constructors;
- semantic crossing and semantic rotation;
- computable actual-port <-> semantic-descriptor equivalence;
- both codec round trips;
- actual PortCrossing;
- actual PortLocalRotation;
- exact source-region formulas;
- exact 3 encoder calibrations;
- exact 3 decoder calibrations;
- exact 3 crossing formulas;
- exact 3 rotation formulas.

Current target:

1. prove old-region cyclicity;
2. prove center-region cyclicity;
3. package faceStarRotationSystem;
4. prove exact face-step 3-cycle;
5. prove first face return = 3;
6. prove every face cell has cardinality 3.

Do NOT work on connectivity or Euler/genus yet.

After TRM-044:

1. prove face-star connectivity;
2. construct faceStarCombinatorialMap;
3. prove V/E/F/D formulas;
4. prove Euler/genus-zero preservation;
5. prove coloring restriction;
6. prove universal all-triangular reduction;
7. then begin the tetrahedral/Eisenstein realization branch.

Four Color theorem status:

    NOT PROVED.

Eisenstein status:

- eisensteinParity : TraceOneInt (-1) ->+ TrominoState verified;
- canonical nonzero Eisenstein directions reduce to {A,B,C};
- tetrahedral roll transport is V4 addition;
- global triangular-Port -> Eisenstein-lattice realization NOT YET constructed.

## Agent completion rule

Never report GREEN because local files build.

Before completion:

1. re-read the active instruction;
2. enumerate every mandatory acceptance item;
3. attach a concrete theorem/definition to each;
4. if one item is missing, report Outcome P and identify it.

Actual repository state overrides stale task-report repository status.
