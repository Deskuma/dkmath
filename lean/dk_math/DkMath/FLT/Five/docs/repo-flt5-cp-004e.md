# FLT5 checkpoint cp-004e report

Date: 2026-07-19
Branch: `hackathon/feature-gn5-flt5-260719-v0`

## Outcome

Outcome B: the mandatory integral golden-order and ramifier-stripped packet
are Lean-certified.  Fifth-power extraction up to a unit is exposed as the
exact next contract, but is not proved or assumed.

This checkpoint does not prove FLT5.  It advances the exceptional GN5 route
from a square-golden norm equation to an exact factorization by the visible
ramifier above five.

## Certified API

`GoldenOrder.lean` introduces the explicit integral pair model `GoldenInt` for
`a + b*phi`, with addition, subtraction, multiplication, natural powers,
conjugation, and norm.  The central certified identities are:

- `goldenConj_invol`, `goldenConj_mul`;
- `goldenNorm_eq_existing_GoldenNorm`;
- `goldenNorm_mul`, `goldenNorm_conj`, `golden_mul_conj`;
- `goldenSqrtFive_sq`, `goldenNorm_sqrtFive`;
- `goldenTau_eq_phi_mul_sqrtFive`, `goldenNorm_tau`;
- `golden_tau_mul_conj`; and
- `exists_goldenTau_factor_of_five_dvd`.

The last theorem gives explicit coordinates: from `5 ∣ 2*M+N`, it chooses
`k` with `2*M+N=5*k`, sets `beta=(M-k,2*k-M)`, and proves
`(M,N)=tau*beta`.

`SignedGoldenRamifierStripped.lean` packages the cp-004d exceptional data and
certifies:

- `alpha = tau*beta` and the explicit coordinates of `alpha` and `beta`;
- `goldenNorm beta = b^5`;
- `beta.snd = -5^7*a^10`;
- `5 ∤ b` and `5 ∤ goldenNorm beta`; and
- there is no `gamma` with `beta = tau*gamma`.

Constructors are available from an exceptional packet, a five-adic power
split, and a signed normal form.  Receiver theorems route a refuter for the
new core back to both signed Branch A and routed Branch B.

## Fifth power up to a unit

The exact remaining endpoint is published as
`SignedGoldenFifthPowerUpToUnitCore`:

```lean
∀ {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w),
  ∃ epsilon gamma : GoldenInt,
    GoldenUnit epsilon ∧
    p.beta = goldenMul epsilon (goldenPow gamma 5)
```

The blocker is algebraic, not computational.  The current repository and
Mathlib provide no ready UFD/PID instance for the full integer ring
`Z[phi]`, no theorem turning the packet's arithmetic into coprimality of
`beta` and its conjugate away from `tau`, and no unit classification for this
model.  Mathlib's `Zsqrtd 5` models `Z[sqrt 5]`, a different suborder; using it
directly would lose the half-integral golden integers.  Therefore no UFD,
coprimality, or unit fact has been fabricated in cp-004e.

The next checkpoint should either build a commutative-ring/UFD presentation of
`Z[phi]` with conjugation and unit classification, or prove a packet-specific
fifth-power extraction theorem strong enough to inhabit the contract above.

## Public exposure and verification

`DkMath.FLT.Five.Main` imports both new modules and its tower comment now ends
at the ramifier-stripped route.  `DkMathTest.FLT.Five.CheckAxioms` prints the
axioms of the new norm, extraction, constructors, and receiver theorems.

Reproduction commands, run from `lean/dk_math`:

```text
lake build DkMath.FLT.Five.SignedSquareGoldenExceptional
lake build DkMath.FLT.Five.GoldenOrder
lake build DkMath.FLT.Five.SignedGoldenRamifierStripped
lake build DkMath.FLT.Five.Main
lake build DkMathTest.FLT.Five.CheckAxioms
git diff --check
./lean-build.sh
```

No `sorry` or `native_decide` is used by the new implementation.
