# Tromino Exchange Calculus — Current State

## Read this first

Current branch:

    research/Tromino-ExchangeCalculus-260924-v0

Current active checkpoint:

    TRM-046 — Face-star count identities / Euler and genus-zero preservation

Current instruction:

    instruction-045.md

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
  cyclic rotation and every face cell card = 3
- TRM-045:
  connected face-star PortCombinatorialMap packaging

Face-star status now verified:

- explicit face/face-port indexing;
- semantic and actual port codecs;
- actual crossing and rotation;
- cyclic PortRotationSystem;
- exact primitive 3-cycle face dynamics;
- every raw and packaged face cell has cardinality 3;
- lifted original region walks;
- radial attachment of every face center;
- global region connectivity;
- nonempty region set;
- faceStarCombinatorialMap.

Current target:

    D' = 3D
    F' = D
    E' = 3E = E + D
    V' = V + F
    chi' = chi

Then:

- preserve arbitrary stated combinatorial genus;
- package faceStarGenusZero.

Do NOT work on coloring restriction or universal target equivalence in
TRM-046.

After TRM-046:

1. identify packaged map as PortAllFacesTriangular;
2. prove old adjacency embeds;
3. restrict any face-star four-coloring to the original map;
4. prove indexing-free genus-zero triangulation reduction;
5. prove universal all-triangular target iff general target;
6. use TRM-039 to identify the all-triangular target with tetrahedral A/B/C
   assignment existence;
7. close this branch;
8. begin the tetrahedral/Eisenstein realization branch.

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
