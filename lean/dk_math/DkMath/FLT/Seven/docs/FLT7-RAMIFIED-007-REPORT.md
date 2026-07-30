# FLT7-RAMIFIED-007 verification report

## Outcome

Outcome A: the canonical routing normalization, exact cubic-gap factor
display, and receiver equivalences are proved.

## Implemented Lean surface

`CoprimeTripleRouting.lean` proves all nine equations `cᵢⱼ = gcd(aᵢ,bⱼ)`.
Each theorem retains the mathematically necessary pairwise-coprimality
hypotheses for both source columns. The routing product identities without
those hypotheses are insufficient.

`SevenBaseTerminalRamifiedCanonicalSplit.lean` packages the terminal
second-coordinate decomposition:

```text
gapRoot = X * Y
|v| = 7^5 * X^7 * C
sndCore = Y^7 * D
|gapQuotient| = C * D
C = gcd(|v|, |gapQuotient|).
```

It then proves the exact natural-number identity

```text
|R-L| = 7^6 * X^7 * (C * residualRoot)
```

and both characterizations of the existing receiver:

```text
receiver ↔ ∃ w, |R-L| = 7^6 * (X*w)^7
receiver ↔ (∃ c, C = c^7) ∧ (∃ b, residualRoot = b^7).
```

The public facade imports the new module.

## Proof boundary

This checkpoint does not prove that `gapRoot = innerRoot^7`, produce a
smaller Fermat solution, or establish recursive descent. Those questions
belong to RAMIFIED-008 and later checkpoints.
