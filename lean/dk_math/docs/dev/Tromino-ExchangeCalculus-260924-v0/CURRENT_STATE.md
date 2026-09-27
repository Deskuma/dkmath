# Tromino Exchange Calculus — Current State

## Read this first

Current branch:

    research/Tromino-ExchangeCalculus-260924-v0

Current active checkpoint:

    TRM-045 — Face-star connectivity and combinatorial-map packaging

Current instruction:

    instruction-044.md

Last fully accepted theorem checkpoints:

- TRM-037:
  genus-zero F2 exactness
- TRM-038:
  genus-zero dual-face conservation <-> zero holonomy
- TRM-039:
  tetrahedral local closure and triangular A/B/C normal form
- TRM-043:
  actual constructor calibration closure
- TRM-044:
  cyclic face-star rotation and triangular face dynamics

Face-star status now verified:

- explicit face/face-port indexing;
- semantic and actual port codecs;
- actual PortCrossing;
- actual PortLocalRotation;
- exact constructor calibration;
- old-region and center-region rotation cyclicity;
- faceStarRotationSystem;
- exact face-step three-cycle;
- primitive face return = 3;
- canonical triangle orbit;
- every actual port lies in a canonical triangle;
- every face cell of the raw rotation/crossing pair has cardinality 3.

Current target:

1. lift original region walks through oldEdge ports;
2. attach every face-center to an old region by one radial edge;
3. prove global face-star region connectivity;
4. prove new region set is nonempty;
5. package faceStarCombinatorialMap;
6. transport the all-face-card-3 theorem to the packaged map.

Do NOT work on count formulas or Euler/genus in TRM-045.

After TRM-045:

1. prove D'=3D, F'=D, E'=3E=E+D, V'=V+F;
2. prove Euler preservation;
3. construct genus-zero face-star wrapper;
4. prove coloring restriction to the original map;
5. prove universal all-triangular reduction;
6. close this branch;
7. begin the tetrahedral/Eisenstein realization branch.

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
