# FLT7-FUSION-003D real-pair-carrier report

Date: 2026-07-30

## Result

FUSION-003D is implemented through the real conjugate-pair selection and
quadratic-jet fusion certificate. The new module is:

```text
DkMath.FLT.Seven.SevenRamifiedFusionRealPairCarrier
```

The packet selects the unordered pair `{tau,-tau}`. It does not select an
oriented degree-six cyclotomic factor and does not construct descent.

## 1. Signed residues and the ternary pair coordinate

The signed cubic source equations and the seven-divisible inner second
coordinate give

```text
signedLeftRoot  = innerFst^3 mod 7
signedRightRoot = innerFst^3 mod 7
signedRightRoot * signedLeftRoot = 1 mod 7.
```

For the three real conjugates of `alpha`, Lean defines

```text
alpha_0 = alpha
alpha_1 = alpha^2 - 2*alpha
alpha_2 = -alpha^2 + alpha + 2
```

and proves

```text
alpha_i - 3 = theta * u_i
u_0 = 1, u_1 = 1+alpha, u_2 = alpha^2
thetaResidue(u_i) = 1,4,2.
```

The map `0 ↦ 1`, `1 ↦ 4`, `2 ↦ 2` is packaged as the explicit equivalence
`pairPhaseEquiv : Fin 3 ≃ SevenTernarySector`. Exhaustiveness is proved from
the factorization of `x^3-1` in `ZMod 7`.

## 2. Real pair carriers and exact theta depth

Writing

```text
T = r^2 + r*l + l^2
S = r*l
P_i = T - alpha_i*S,
```

Lean proves the exact real-pair factorization

```text
P_0 * P_1 * P_2 = signedSeventhQuotient r l.
```

The proof uses the explicit multiple of the minimal relation
`alpha^3 - 2*alpha^2 - alpha + 1 = 0`, avoiding a large coordinate
normalization.

From `r-l = 7^4*d` and `7 = theta^3*thetaSevenUnit`, the division-free cores

```text
C_i = theta^23 * thetaSevenUnit^8 * d^2 - u_i*r*l
```

satisfy

```text
P_i = theta*C_i
thetaResidue(C_i) = -pairPhase(i).
```

Consequently every `P_i` has exact theta depth one.

## 3. Structural quotient-sector certificate

Combining the three carrier identities with
`theta^3 = -7*(theta+1)^2`, and cancelling the nonzero scalar seven in the
integral cubic order, gives

```text
-(theta+1)^2 * C_0*C_1*C_2 = quotientRoot.
```

Reducing this equation modulo theta yields a second proof

```text
quotientRoot = 1 mod 7.
```

The earlier integer first-variation proof is retained.

## 4. Pair selection and quadratic fusion

The selected index is

```text
pairPhaseEquiv.symm rightUnitSectorAddress.2.
```

Lean proves

```text
thetaResidue(selectedPairCore) = -fusionSlope^2
relativeRealIndex(k) = 1
  iff k^2 = fusionSlopeUnit^2.
```

Thus this construction selects precisely the pair `{tau,-tau}`. It does not
choose between its two orientations.

Both paired quadratic jets now connect directly to the selected real core:

```text
right normalized quadratic jet
  = 3 * thetaResidue(selectedPairCore)

left normalized quadratic jet
  = 3 * thetaResidue(selectedPairCore).
```

This bypasses any unsupported identification of cubic rotation with a
canonical gcd-routing action.

## 5. Coprimality reconnaissance

The three forward axis-unit differences are verified explicitly:

```text
norm(u_1-u_0) = -1
norm(u_2-u_1) = -1
norm(u_2-u_0) = 1.
```

Lean also proves all three are global units, using explicit inverses.

The proposed theorem that the normalized cores are pairwise coprime is not
yet proved. The remaining formal gap is a reusable prime-divisor transport
from

```text
C_i - C_j = -(u_i-u_j)*r*l
```

and the common high-depth term to an integer statement that `r*l` is
coprime to `gapRoot`. The available packet has `IsCoprime l r`,
`r-l = 7^4*gapRoot`, and seven-primitivity, but the required mixed
integer/cubic divisibility bridge is not currently exposed as an API.

## 6. Predicted next checkpoint

The narrow next packet is a **real-pair core coprimality bridge**:

1. prove `IsCoprime (r*l) gapRoot` in the signed integer packet;
2. transport scalar prime divisors between the cubic order and integers;
3. prove the three `C_i` pairwise coprime;
4. only then test a seventh-power/association extraction for the selected
   core.

The full degree-six carrier should be introduced only if the later argument
must distinguish `+tau` from `-tau`.

## 7. Excluded claims

This checkpoint does not prove:

- a nontrivial cubic-rotation action on the canonical gcd routing;
- an oriented cyclotomic factor;
- pairwise coprimality of the three normalized cores;
- a seventh-power association for the selected core;
- a reconstructed primitive Fermat chart;
- strict descent, a descent provider, or FLT7.
