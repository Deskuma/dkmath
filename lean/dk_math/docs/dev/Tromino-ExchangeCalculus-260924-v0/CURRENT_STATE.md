
# Tromino Exchange Calculus — Current State

## Read this first

Current branch:

    research/Tromino-ExchangeCalculus-260924-v0

Current active checkpoint:

    TRM-047 — Packaged triangulation and coloring restriction

Current instruction:

    instruction-046.md

Last fully accepted theorem checkpoints:

- TRM-037: genus-zero F2 exactness
- TRM-038: genus-zero dual-face conservation <-> zero holonomy
- TRM-039: tetrahedral local closure and triangular A/B/C normal form
- TRM-043: actual constructor calibration closure
- TRM-044: cyclic rotation and every face cell card = 3
- TRM-045: connected face-star PortCombinatorialMap packaging
- TRM-046: count identities, Euler/genus preservation, faceStarGenusZero

Face-star status now verified:

- actual connected PortCombinatorialMap;
- every face cell has cardinality 3;
- D' = 3D;
- F' = D;
- E' = 3E = E + D;
- V' = V + F;
- chi' = chi;
- arbitrary stated combinatorial genus is preserved;
- faceStarGenusZero is available.

Current target:

1. expose PortAllFacesTriangular for the packaged map;
2. embed original adjacency through oldRegion;
3. restrict any face-star four-state coloring to original regions;
4. prove face-star colorable -> original colorable;
5. combine with TRM-039 to obtain:
       face-star tetrahedral assignment -> original colorable.

Do NOT prove universal target equivalence in TRM-047.

After TRM-047:

TRM-048 final reduction layer:

1. use exists_portFaceStarIndexing;
2. define PortGenusZeroTriangularFourColorTarget;
3. prove triangular target <-> general PortGenusZeroFourColorTarget;
4. define PortGenusZeroTriangularTetrahedralTarget;
5. prove triangular tetrahedral target <-> general four-color target;
6. state exact remaining Gap: universal tetrahedral assignment existence;
7. close the ExchangeCalculus branch.

Then begin a new branch for:

    triangular Port map -> Eisenstein lattice / parity texture realization.

Four Color theorem status:

    NOT PROVED.

Current exact remaining mathematical existence problem after reduction:

    every all-triangular genus-zero Port map
    admits a tetrahedral A/B/C face assignment.

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
