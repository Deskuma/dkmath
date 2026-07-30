# FLT7-FUSION-002 exact paired theta-jet report

Date: 2026-07-30

## Completed boundary

`SevenRamifiedThetaJetLifting.lean` proves a reusable division-free
triangular step. For `k < 3`, it advances

```text
7^k | B, 7^(2k) | C
  -> 7^(k+1) | B, 7^(2k+2) | C.
```

The proof uses the coprimality of the leading factors with seven; no general
p-adic valuation layer was introduced. Iteration at `k=0,1,2` gives the
lower depths `(3,6)`. The normalized output constructs `U,V` and proves

```text
B = 7^3*U, C = 7^6*V,
U = sign*m                  in ZMod 7,
A*V + 3*U^2 = 0            in ZMod 7,
7 does not divide U or V.
```

`SevenRamifiedPairedThetaRootJet.lean` connects this theorem to the actual
left and right exact-power roots. It constructs one coherent paired packet
with opposite linear sectors and a common quadratic sector. Consequently
neither root lies in `IsSourcePlane`.

## FUSION slope

The packet exposes

```text
tau = m/a = gapRoot/a^3,
right normalized linear jet = tau,
left normalized linear jet = -tau,
both normalized quadratic jets = -3*tau^2.
```

The canonical address

```text
row = tau^3
column = tau^2
```

reconstructs `tau` by `row/column`. This is the finite controlled
theta-jet outcome of FUSION-002.

## Prediction and honest stop

The address strongly suggests the same `C2 x C3` six-sector grid as the
canonical signed `2 x 3` routing and the six nontrivial cyclotomic indices.
No equality with a fixed routing cell, row-sensitive terminal unit, or
cyclotomic factor is proved here. That identification is the next FUSION
gate.

No reconstructed primitive Fermat chart, strict decrease, descent provider,
or FLT7 theorem is claimed.
