# Petal / FloatWindow implementation report - checkpoint 333

## Result

This checkpoint closes the requested source-time accounting layer and proves a
uniform obstruction to the audited fixed low-bit signature family.

The outcome separates two routes sharply:

1. the source-time route remains viable, with one explicit missing theorem:
   uniform source age for outstanding canonical claims;
2. the fixed low-bit signature consisting only of residue, upper carry,
   height class, and width-growth flag is rejected for every fixed depth
   `r >= 1`.

No claim is made against finite signatures that retain an upper boundary or a
separately proved decreasing rank.

## Circular finite-certificate regression

`FiniteSignedTransition.lean` now proves

```text
endpointAccountingTerm n k
  <= queueBefore (k+1) - queueBefore k.
```

Any assumed queue bound `C` can therefore manufacture a certificate whose
signature and potential are the queue value itself in `Fin (C+1)`.  Lean proves
the semantic equivalence

```text
exists canonical finite certificate
  <-> exists canonical queue uniform upper bound.
```

This is a circularity regression, not an arithmetic solution: the constructed
signature depends on the queue bound it is meant to prove.  A noncircular
certificate must start from a structurally predefined arithmetic signature.

## Exact source-time accounting

The new `CanonicalSourceTimeLag.lean` proves the exact recurrence

```text
startTime (k+1) = startTime k + blockLength k
```

and its range and `Ico` telescopes.  Consequently canonical demand over blocks
`[q,m)` is bounded by the actual orbit-time span

```text
sum demand [q,m) <= startTime m - startTime q.
```

The stronger carrier identity also closes:

```text
sum demand [q,m)
  = card {i in [startTime q,startTime m) | CarryTwoDebtAt n i}.
```

Thus block demand is not merely bounded by elapsed time; it is exactly the
number of carry-two source addresses in that time interval.

For the last `H` source-time units, `canonicalRecentSourceClaimCarrier` has
cardinality at most `H`, with regressions at time zero and horizon zero.  The
conditional predicate

```text
CanonicalOutstandingQueueCoveredByRecentSourceClaims n H
```

therefore yields both a queue bound by `H` and an endpoint-width bound by
`bitWidth n + H`.  No such uniform `H` is asserted.  The remaining input is
exactly a uniform source-age theorem for outstanding claims.

## All-ones raw family

`RawLowSignatureObstruction.lean` defines

```text
x_r = 2^(r+2) - 1.
```

For every `r >= 1`, Lean proves

```text
T x_r       = 3 * 2^(r+1) - 1
T (T x_r)   = 9 * 2^r - 1
s x_r       = 1
s (T x_r)   = 1
width x_r   = r + 2
width (T x_r)       = r + 3
width (T (T x_r))   = r + 4.
```

Both `x_r` and `T x_r` have residue `2^r - 1` modulo `2^r`, upper carry two,
height class one, and a true one-step width-growth flag.  Their audited fixed
low signatures are therefore equal, while the realized signed width weight of
the edge `x_r -> T x_r` is exactly `+1`.

## Fixed low-signature obstruction

The finite type `FixedLowRawSignature r` contains exactly:

```text
residue modulo 2^r
upper carry in Fin 3
height class: one / at least two
width-growth Boolean
```

The theorem

```text
not_exists_fixedLowRawSignature_globalCertificate
```

states that for every `r >= 1` there is no relational bounded-potential
certificate using this exact signature that covers all accelerated odd edges
with their signed width weight.

The proof uses the one-edge all-ones witness.  Equal endpoint signatures force
the projected potential difference to be zero, but soundness must dominate the
realized weight `+1`, yielding a contradiction.

This establishes a parameterized obstruction, not a finite search result.  A
fixed lower window confuses a sufficiently long finite all-ones prefix with
its 2-adic all-ones continuation.

## Route decision

The audited fixed low-bit route is closed negatively.  Enlarging `r` does not
repair it, because the witness family grows with `r`.

The source-time claim-age route remains the clean positive route:

```text
uniform source-time claim age
  -> recent-source coverage
  -> queue bound
  -> endpoint-width bound.
```

The abstract certificate route remains legitimate only after choosing a
signature independently of the desired queue bound.  The next plausible
signature experiment must expose information absent from every fixed lower
window, such as an upper-boundary/eventually-zero coordinate or a proved
decreasing rank.

## Additional results

Beyond the minimum request, the implementation records the exact second
successor, all three exact widths, an existential no-certificate theorem, and
the exact prefix as well as interval source-carrier cardinality identities.

## Verification

The following gates passed:

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.FiniteSignedTransition
lake build DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceTimeLag
lake build DkMath.Collatz.PetalBridge.FloatWindow.RawLowSignatureObstruction
lake build DkMath.Collatz.PetalBridge.FloatWindow
lake build DkMath.Collatz.PetalBridge
lake build DkMath
git diff --check
```

The three changed implementation modules contain no `sorry` or `admit`, and no
new heartbeat override was introduced.
