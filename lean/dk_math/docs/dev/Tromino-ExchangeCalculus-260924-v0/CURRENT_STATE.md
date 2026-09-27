
# Tromino Exchange Calculus — Current State

## Read this first

Current branch:

    research/Tromino-ExchangeCalculus-260924-v0

Current active checkpoint:

    TRM-048 — Universal triangular reduction / branch closure

Current instruction:

    instruction-047.md

Last fully accepted theorem checkpoints:

- TRM-037: genus-zero F2 exactness
- TRM-038: genus-zero dual-face conservation <-> zero holonomy
- TRM-039: tetrahedral local closure and triangular A/B/C normal form
- TRM-043: actual constructor calibration closure
- TRM-044: cyclic rotation and every face cell card = 3
- TRM-045: connected face-star PortCombinatorialMap packaging
- TRM-046: count identities, Euler/genus preservation, faceStarGenusZero
- TRM-047: all-triangular packaging, old adjacency embedding, coloring pullback,
  and tetrahedral-assignment -> original-colorability reduction

Face-star reduction status now verified:

- any connected genus-zero Port map admits face-star indexing;
- face-star produces a connected all-triangular genus-zero Port map;
- D' = 3D;
- F' = D;
- E' = 3E = E + D;
- V' = V + F;
- chi' = chi;
- any coloring of the face-star map restricts to a coloring of the original map;
- any tetrahedral assignment on the face-star map yields a coloring of the
  original map.

Current target:

1. define PortGenusZeroTriangularFourColorTarget;
2. prove it equivalent to PortGenusZeroFourColorTarget;
3. define PortGenusZeroTriangularTetrahedralTarget;
4. prove it equivalent to the triangular four-color target;
5. therefore prove it equivalent to the general four-color target;
6. state the exact remaining Gap and close the branch.

Do NOT prove any universal target.

Four Color theorem status:

    NOT PROVED.

Exact remaining Gap after successful TRM-048:

    PortGenusZeroTriangularTetrahedralTarget

i.e. prove that every all-triangular genus-zero Port map admits a tetrahedral
A/B/C face assignment.

Eisenstein status:

- eisensteinParity : TraceOneInt (-1) ->+ TrominoState verified;
- canonical nonzero Eisenstein directions reduce to {A,B,C};
- tetrahedral roll transport is V4 addition;
- global triangular-Port -> Eisenstein-lattice realization NOT YET constructed.

After TRM-048:

1. close / merge this deep ExchangeCalculus branch;
2. start a new branch dedicated to:
       triangular Port map -> Eisenstein lattice / parity texture realization;
3. keep the universal tetrahedral existence problem explicit and separate.

## Agent completion rule

Never report GREEN because local files build.

Before completion:

1. re-read the active instruction;
2. enumerate every mandatory acceptance item;
3. attach a concrete theorem/definition to each;
4. if one item is missing, report Outcome P and identify it.

Actual repository state overrides stale task-report repository status.
