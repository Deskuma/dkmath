# Saturated Canonical Block Audit (cp-318)

Finite computational evidence only; no universal successor theorem is inferred.

## Range

- exhaustive odd roots: `65536` through `131071`
- deterministic random roots: `1280` over `(64, 128, 256, 512, 1024)`
- random seed: `54039`

## Saturated runs

- saturated blocks: `33435`
- maximum consecutive saturated length: `1`
- consecutive saturated pairs: `0`
- saturated length counts: `{2: 33435}`
- saturated odd-core residues mod 8: `{3: 14619, 7: 18816}`
- immediate successor drift nonpositive: `31650`
- immediate successor drift positive: `1785`
- runs without a later observed nonpositive drift: `0`
- maximum blocks to first later nonpositive drift: `5`

A positive successor or a consecutive saturated pair refutes the simplest
`saturated -> next drift <= 0` candidate.  Even a clean finite row would
remain evidence rather than a Lean theorem.
