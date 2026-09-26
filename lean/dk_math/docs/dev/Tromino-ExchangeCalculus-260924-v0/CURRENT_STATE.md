# Tromino Exchange Calculus — Current State

## Read this first

Current branch:

    research/Tromino-ExchangeCalculus-260924-v0

Current active checkpoint:

    TRM-042 — Actual Port Codec / Semantic Transport Bridge

Current instruction:

    instruction-041.md

Last fully accepted major theorem checkpoints:

- TRM-037: genus-zero F2 exactness
      im boundary2 = ker boundary1
- TRM-038: genus-zero dual-face conservation <-> zero holonomy
- TRM-039: tetrahedral local closure and triangular A/B/C normal form

Partial infrastructure:

- TRM-040:
  face-star indexing, descriptor carrier, regions and actual port constructors
- TRM-041:
  semantic crossing and semantic rotation

Current exact blocker:

    PortNetworkPort (faceStarNetwork M I)
      ≃
    FaceStarPortDesc M

Specifically, the reverse dependent-Sigma/Fin round trip:

    encode (decode q) = q.

Do not bypass this with an axiom, hypothesis, cardinality argument or
noncomputable selector.

After this bridge succeeds, the planned order is:

1. transport crossing / local rotation to actual ports;
2. prove old-region and face-center cyclicity;
3. prove every new face is a primitive 3-cycle;
4. construct connected faceStarCombinatorialMap;
5. prove count formulas and Euler/genus preservation;
6. restrict subdivision colorings to the original map;
7. prove the universal all-triangular reduction;
8. move the remaining existence problem to the tetrahedral/Eisenstein track.

Four Color theorem status:

    NOT PROVED.

Current equivalent/near-equivalent target already formalized on
all-triangular genus-zero maps:

    existence of a nowhere-zero V4 assignment
    with A/B/C exactly once on every triangular face.

Eisenstein status:

- eisensteinParity : TraceOneInt (-1) ->+ TrominoState is verified;
- its canonical nonzero direction parity image is {A,B,C};
- tetrahedral roll transport is V4 addition;
- a global Eisenstein lattice realization of an arbitrary triangular Port map
  has NOT yet been constructed.

## Agent completion rule

Never report GREEN because local files build.

Before completion:

1. re-read the active instruction;
2. enumerate every mandatory acceptance item;
3. attach a concrete theorem/definition name to each item;
4. if one item is missing, report Outcome P with the exact missing bridge.

Repository state and actual Lean source override any stale status sentence in
copied task reports.
