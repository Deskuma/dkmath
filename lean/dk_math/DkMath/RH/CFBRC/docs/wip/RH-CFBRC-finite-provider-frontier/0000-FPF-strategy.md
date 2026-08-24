# RH-CFBRC Finite Provider Frontier Strategy

Date: 2026-08-25

Branch: `wip/RH-CFBRC-finite-provider-frontier-260825-v0`

Base: `develop` at `570a61c478b7a3aa5138fadbbe39e7b0f9e8ee22`

Route code: `FPF` — Finite Provider Frontier

## 0. Route identity

The previous Guinand-Weil Source-Rank / critical-mirror route is merged into `develop` and closed.
Its bounded endpoint is:

```text
finite Mellin detector construction          CLOSED
actual general-tau source representation     CLOSED
critical-mirror transport                    CLOSED
shifted-energy polarization                  CLOSED
paired mirror collapse mechanism             CLOSED
independent finite canonical P1 provider     NOT FOUND
```

FPF does not reopen the mirror route.  It starts from the remaining provenance gap.

The exact P1 target is the actual synthesized canonical witness `c_j`:

```text
E1-(c_j) <= E1+(c_j)
```

which the existing shifted-energy API identifies with the source-coordinate sign

```text
0 <= (WholeSource epsilon tau c_j W X).re.
```

The equality/readout theorem is already available.  The missing object is an independent source-side reason for the sign.

## 1. Strategic change

Do not begin by asking for another analytic inequality on `WholeSource`.

Instead ask whether the missing P1 statement admits a finite provider frontier analogous in architecture to the new Legendre formalization:

```text
finite cover
  -> failure of full cover
  -> escaping finite witness
  -> support exclusion / obstruction certificate
  -> target conclusion
```

The Legendre reference is methodological, not a theorem import.  In `DkMath.NumberTheory.Legendre.Frontier`, the conjecture is separated from its provider by exact equivalences such as:

```text
LegendreConjecture
  <-> SquareAnchoredSupportEscape
  <-> every positive square window is not fully covered.
```

The provider itself is not silently proved by the equivalence.  This separation is the model for FPF.

## 2. What may transfer from the Legendre architecture

The following design ideas are admissible references.

### 2.1 Provider/frontier separation

First identify a finite proposition `SourceEscape` or equivalent whose proof would imply canonical P1.  Prove the implication/equivalence separately from proving the provider.

Do not call a rewrite theorem a provider.

### 2.2 Finite support and cover language

If the actual finite arithmetic/source expansion permits it, organize source atoms into finite supports and ask whether a bad-sign configuration requires complete coverage by a bounded family of obstruction directions.

Any notion of `cover`, `support`, `seat`, or `escape` must be derived from the existing finite source formula.  Do not introduce a metaphor-only abstraction.

### 2.3 Local depth and overlap ledgers

`DkMath.NumberTheory.Legendre.LocalizedObstruction` shows how a global cover problem can be refined into exact finite incidence ledgers:

```text
local depth multiplicity
pair overlap count
sum-over-directions = sum-over-seats
```

FPF may seek an analogous decomposition only after actual RH source atoms are identified.

### 2.4 Packet / residue geometry

`PacketUnitResidue` and `SmallCofactor` show a second useful pattern:

```text
global covered point
  -> exact finite factor packet
  -> reduced local coordinates
  -> bounded residual object
  -> compressed criterion
```

For RH this suggests looking for a finite normal form of any source configuration that violates P1.  It does not justify importing natural-number residue statements into the complex analytic source.

## 3. Translation dictionary — heuristic only

The following table is a research dictionary, not a theorem claim.

| Legendre architecture | Possible RH-CFBRC analogue | Status |
|---|---|---|
| finite square window | fixed finite `epsilon, tau, W, X, R` source problem | actual finite API exists |
| offset seat | one finite source atom / source cell / canonical contribution | to identify |
| bounded prime directions | finite prime-power / correction / horizontal directions | to inventory |
| covered seat | contribution whose sign freedom is blocked by source constraints | undefined |
| full cover | hypothetical finite configuration forcing failure of desired sign | undefined |
| escape witness | finite source certificate sufficient for P1/P2/P3 | missing |
| local depth | number/strength of obstruction directions attached to one atom | undefined |
| pair overlap | double-counted cancellation/interaction structure | undefined |
| support-disjoint witness | source contribution immune to all bad-sign directions | undefined |

Do not formalize the undefined entries until an exact formula justifies them.

## 4. The first mathematical target

Before defining any cover structure, obtain an exact finite provenance ledger for

```text
(WholeSource epsilon tau c_j W X).re
```

and, equivalently through the existing finite approximant bridge,

```text
(FiniteArithmeticApproximant ...).im.
```

The ledger must answer:

1. Which finite terms carry prime-power information?
2. Which are archimedean or elementary corrections?
3. Which top-horizontal terms remain present?
4. Which pieces are real-sign readable termwise?
5. Which pieces are intrinsically oscillatory/complex?
6. Which cancellations are exact algebraic identities and which require estimates?
7. Can the target sign be reduced to a finite incidence/coverage statement without a limit?

This inventory is FPF's first gate.

## 5. Provider admissibility rules

A candidate FPF provider counts only if all of the following hold.

### FPF-P1. Exact witness

It applies to the actual synthesized nonzero-`tau` canonical coefficient row, not a fixed `tau = 0` surrogate.

### FPF-P2. Full finite source

It retains every finite source component required by the current WholeSource identity, including the top-horizontal term.

### FPF-P3. Independent provenance

It is not obtained by rewriting the zero-side detector, H8 paired-collapse theorem, mirror transport, or `q.im` scalar factorization.

### FPF-P4. Sign strength

It proves an actual one-sided order/sign, an equality, or a quantitative gap strong enough to imply P1/P2/P3.  Nonnegativity of separate norm squares is insufficient.

### FPF-P5. Finite level

The primary route stays at fixed finite `R, epsilon, tau, W, X`.  No `T -> infinity`, `X -> infinity`, or interchange of limits is introduced merely to manufacture a sign.

### FPF-P6. No RH-equivalent input

No Riemann Hypothesis assumption, classical Weil positivity criterion, Li criterion, RH-equivalent raw-ratio bound, or disguised zero exclusion may be used as the provider.

## 6. Critical firewalls inherited from GWSS

The following are trusted closed results and must not be repackaged as new information:

```text
canonical finite Mellin full-rank extraction
q.im off-critical detector factorization
complex-linear phase no-go
homogeneous norm/majorant no-go
actual general-tau source/feature bridge
WholeSource / finite approximant identities
critical-mirror mass/extractor/coefficient transport
WholeSource negative-conjugation transport
shifted-energy mirror parity
paired 1-channel dominance collapse
I-channel mirror redundancy
```

In particular:

```text
mirror symmetry != independent provider
P0 positivity != P1 dominance
representation != sign
finite equivalence != provider existence
```

## 7. Strategic branches of the search

FPF should test three bounded branches in order.

### Branch A — exact finite atomization

Try to decompose the canonical real WholeSource channel into a finite ledger with named source atoms and explicit correction classes.

Success criterion:

```text
exact finite identity + provenance labels for every term.
```

Failure criterion:

```text
current API does not expose a finite atomization compatible with the canonical witness.
```

### Branch B — obstruction/coverage normal form

Only after Branch A succeeds, ask whether a violation of canonical P1 has an exact finite normal form:

```text
not P1
  -> every candidate escape atom is obstructed/covered
```

or preferably an equivalence.

This is the closest analogue of the Legendre frontier.

### Branch C — localized budget contradiction

Only if a meaningful cover relation exists, derive finite depth/pair/overlap ledgers and compare the total obstruction budget against the finite source carrier.

A strict budget deficit could produce an escape witness, hence P1.

No counting theorem should be added before the carrier and obstruction relation are mathematically exact.

## 8. What success would and would not mean

If FPF finds an independent canonical P1 provider valid for both `j` and its critical mirror, H8 immediately gives the paired equality collapse in the real shifted-energy channel.

That is not yet RH.

After P1 is found, a separate gate must determine whether the resulting source-channel equality couples strongly enough to the nonzero off-critical detector to exclude `q.im != 0`, or whether another P2/P3 quantitative bridge is still required.

Therefore the route is intentionally:

```text
independent finite P1 provider
  -> activate existing mirror collapse
  -> audit detector coupling
  -> only then assess off-critical exclusion
```

Do not skip the detector-coupling audit.

## 9. Stop conditions

Stop FPF and report rather than proliferating wrappers when any of the following occurs:

1. the source real channel cannot be atomized beyond existing representation identities;
2. every proposed cover/escape proposition is merely a restatement of P1;
3. the only surviving provider requires a limit or RH-equivalent input;
4. finite obstruction budgets are exactly homogeneous and cannot choose a sign;
5. no independent provenance remains after candidate audit.

A negative finite-provider theorem or a clean `NOT FOUND` frontier is a valid route result.

## 10. Route objective

The immediate research objective is not RH itself.

It is to answer one sharply bounded question:

```text
Can the missing canonical P1 sign be reduced to, and then supplied by,
a genuinely independent finite source-cover / escape / obstruction theorem?
```

Only a positive answer authorizes extending the route toward detector collapse.  A negative answer should close FPF and force a genuinely different source family.