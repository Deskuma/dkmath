# Instruction 019 - PrimeWorld / PrimeAddress / fold-gap integration and coarse primorial town

## Mission

Continue from Instruction 018.

Instruction 018 completed a substantial arithmetic island:

- exact centered pair gcd normal form
- internal odd-gap product H_n
- exact odd-prime support below 2*n
- radical bridge to the existing finitePrimeBasisProduct
- positive-anchor primality detector for centeredFoldNorm
- exact factorization and padic valuation formulas
- exact order-four cyclotomic address
- consecutive-shell coprimality of the fold aggregates

However, none of these objects currently gives a full-cover contradiction.

A separate workspace audit found that DkMath already contains another large and mature island:

- PeriodicPrimeWorld
- PrimeWorldResidues
- PrimeWorldRefinement
- Legendre CoprimePacket
- PacketCoprimality
- PacketUnitResidue
- PacketCross
- OldSupportCapacity
- square-anchor wheel and residue-cover APIs

The objective of Instruction 019 is to connect these islands before deepening the valuation calculation further.

The main target is:

  fold-gap prime world
  -> existing PrimeWorld residue space
  -> square-anchor phase inside an arbitrary Legendre shell
  -> two coarse streets separated by one PrimeWorld period
  -> full-cover assignment constraints
  -> existing old-support capacity consumers where possible

Do not begin with the proposed Instruction 018 prime-power floor-sum theorem unless it becomes necessary as a consumer input during this integration.

This checkpoint is deliberately discovery-heavy. Search the repository broadly. If an exact theorem already exists outside the initially named files, reuse it rather than reimplementing it.

All new instruction, findings, and report artifacts must remain parser-safe plain text. Avoid backslash notation and LaTeX control sequences.

## Critical distinction: offset residue versus square-point residue

For an arbitrary shell anchor n and finite prime world S with modulus M:

  M = primeWorldModulus S

the relevant PrimeWorld address is generally:

  (n^2 + r) mod M

not merely:

  r mod M

These coincide only under additional hypotheses such as M dividing n.

Therefore do not define the arbitrary-shell coarse town by simply filtering offsets r by Coprime r M.

The correct generic shell survivor condition is:

  SupportDisjointFrom S (n^2 + r)

or its exact equivalent in PrimeWorld residue coordinates.

This square-anchor phase distinction is mandatory throughout Instruction 019.

## Phase 0 - repository-wide discovery audit

Before writing production code, run repository-wide searches over Lean source and relevant historical audits.

Search by concepts as well as known theorem names.

At minimum inspect:

DkMath.NumberTheory.Primitive.FinitePrimeWorld
DkMath.NumberTheory.Primitive.PeriodicPrimeWorld
DkMath.NumberTheory.Primitive.PrimeWorldResidues
DkMath.NumberTheory.Primitive.PrimeWorldRefinement
DkMath.NumberTheory.Primitive.PrimorialUniverse and nearby modules
DkMath.NumberTheory.Legendre.Basic
DkMath.NumberTheory.Legendre.GnomonResidueCover
DkMath.NumberTheory.Legendre.PrimorialWheelBridge
DkMath.NumberTheory.Legendre.PrimorialWheelSuccessor
DkMath.NumberTheory.Legendre.CoprimePacket
DkMath.NumberTheory.Legendre.PacketCoprimality
DkMath.NumberTheory.Legendre.PacketUnitResidue
DkMath.NumberTheory.Legendre.PacketCross
DkMath.NumberTheory.Legendre.OldSupportCapacity
DkMath.NumberTheory.Legendre.OldSupportGcd
DkMath.NumberTheory.Legendre.CenteredFoldGcdAggregate
DkMath.NumberTheory.Legendre.CenteredFoldSupportNorm
DkMath.NumberTheory.Legendre.SquareAnchorCounterexamplePacket

Also search historical PrimitiveStructure audits for:
- periodic world
- reduced residues
- packet
- mixed radix
- Jacobsthal
- full-cover capacity
- Hall or matching
- old support
- prime world refinement
- square shell transport

The audit goal is to find hidden adapters or negative results already proved.

Record:
- exact reusable declaration names
- exact duplicate proposals that should not be implemented
- prior negative audits that close tempting but false routes
- dependency direction constraints

Write source-inventory-019.md before substantial production changes.

## Phase 1 - exact PrimeWorldResidues to packet-base adapter

Let:

  M = primeWorldModulus S

Audit and prove the cleanest exact theorem relating:

  primeWorldResidues S

and:

  squareAnchorCoprimeBaseOffsets M

Expected finite-set equality for the nontrivial modulus case:

  if 1 < M,
  primeWorldResidues S = squareAnchorCoprimeBaseOffsets M

Reason:

- primeWorldResidues uses representatives 0 <= r < M with Coprime r M
- squareAnchorCoprimeBaseOffsets M uses 1 <= r <= M with Coprime M r
- when M > 1, residue 0 is not coprime to M and endpoint M is not coprime to M

Do not silently extend this equality to M = 1.

Kernel-check the M = 1 mismatch explicitly if it exists.

Also prove membership-level adapters when they reduce rewriting friction.

If the exact equality already exists under another name, expose only a thin alias or application bridge.

## Phase 2 - cardinality and totient dictionary

From the Phase 1 adapter, connect:

  card(primeWorldResidues S)

to:

  Nat.totient M

for M > 1.

Compare with the existing fresh-prime recurrence:

  card(new residues) = card(old residues) * (q-1)

Do not introduce a second totient proof if the packet API already supplies it.

Record whether this gives an exact bridge between:
- PrimeWorld refinement recurrence
- packet-base cardinality
- Euler totient cardinality

This phase is a dictionary, not a new number-theory result.

## Phase 3 - bring the Instruction 018 odd-gap world into PrimeWorld

Instruction 018 proved:

  primeFactors(centeredOddGapProduct n)
  =
  (primeScalesUpTo(2*n-1)).erase 2

and identified the radical with finitePrimeBasisProduct of that basis.

Prefer an existing object if one already represents this basis.

Otherwise define a small shell-facing abbreviation such as:

  centeredOddGapPrimeWorld n
  =
  (primeScalesUpTo(2*n-1)).erase 2

Prove or reuse:

- KnownPrimeScales for this world
- its primeWorldModulus equals the squarefree radical of centeredOddGapProduct n
- its PrimeWorld residues are exactly the reduced residues modulo that radical
- Phase 1 identifies those residues with the canonical packet base at that modulus when the modulus is greater than 1

Do not define a competing odd primorial framework.

The purpose is to make Instruction 018 speak the existing PrimeWorld language.

## Phase 4 - generic square-anchor PrimeWorld address

For arbitrary shell anchor n and finite prime world S, define only if no existing equivalent already exists:

  squarePrimeWorldAddress S n r
  =
  (n^2 + r) mod primeWorldModulus S

or reuse squareShellWheelProjection if it already supplies exactly this coordinate.

Prove the semantic equivalence:

  SupportDisjointFrom S (n^2+r)

iff

  squarePrimeWorldAddress S n r belongs to primeWorldResidues S

under the exact hypotheses required for S.

Prefer existing:
- supportDisjointFrom_mod_primeWorldModulus_iff
- mem_primeWorldResidues_iff_supportDisjointFrom
- square-shell wheel projection theorems

Do not duplicate wheel projection machinery.

This theorem is the central address adapter for an arbitrary Legendre shell.

## Phase 5 - one-period shell base street

Let:

  M = primeWorldModulus S

For M > 0 define a canonical one-period block of shell offsets.

Preferred offset interval:

  1 <= r <= M

This interval has exactly one representative of every residue class modulo M.

Define the base survivor street as those offsets r in that block satisfying:

  SupportDisjointFrom S (n^2+r)

or the equivalent squarePrimeWorldAddress membership.

Suggested name only if no better existing object exists:

  squarePrimeWorldBaseStreet S n

Prove:

- base offsets lie in Icc 1 M
- each PrimeWorld residue appears exactly once after square-anchor phase translation
- the base survivor street has cardinality card(primeWorldResidues S)
- hence for M > 1 it has cardinality Nat.totient M

Do not assume n is a multiple of M.

The proof should treat addition by n^2 modulo M as a permutation of residue classes, not as the identity.

## Phase 6 - shifted coarse street inside the square shell

Assume:

  0 < M
  M <= n

For each base street offset r with 1 <= r <= M, define its opposite coarse street seat:

  M + r

Then both offsets lie in the open square shell:

  1 <= r <= 2*n
  1 <= M+r <= 2*n

Define the shifted survivor street as the image of the base survivor street under:

  r -> M+r

Prove:

- base and shifted streets are disjoint
- both lie in squareOffsets n
- shift is injective
- both streets have equal cardinality
- their union has twice the base survivor cardinality

Most importantly prove exact PrimeWorld periodicity:

  SupportDisjointFrom S (n^2+r)
  iff
  SupportDisjointFrom S (n^2+(M+r))

This should be a direct application of PeriodicPrimeWorld, not a new divisibility proof.

This is the formal coarse-town two-street geometry.

## Phase 7 - address preservation across the two streets

Strengthen Phase 6 from survivor equivalence to address equality when convenient:

  squarePrimeWorldAddress S n (M+r)
  =
  squarePrimeWorldAddress S n r

or the exact existing ModEq form.

Thus the two seats are the same PrimeWorld address in adjacent copies of the period.

This is the coarse analogue of the earlier packet statement:

  r <-> n+r

but the period is now M, not the shell anchor n.

Do not claim it is a specialization of CoprimePacket unless an exact parameter identification is proved.

## Phase 8 - covering directions outside the coarse world

Assume:

  S subset primeScalesUpTo n

and a coarse-town seat is an S-survivor.

If that seat is SquareOffsetCovered n r, prove that every covering prime belongs to:

  primeScalesUpTo n minus S

or at least prove existence of a covering prime outside S.

Preferred theorem shape:

  SquareOffsetCovered n r
  and
  SupportDisjointFrom S (n^2+r)
  imply
  exists q,
    q in primeScalesUpTo n
    and q notin S
    and q divides n^2+r

Use actual squareOffsetPrimeSupport where possible.

This creates the remaining-direction world consumed by full cover.

## Phase 9 - one external prime cannot cover both members of a coarse pair

Let r be a base street offset and consider:

  A = n^2+r
  B = n^2+(M+r)

Their difference is exactly M.

Let q be prime with q notin S.

Under KnownPrimeScales S, prove:

  q does not divide M

and therefore:

  not (q divides A and q divides B)

when q is an eligible outside direction.

This is the coarse-period analogue of:

  not_both_squareOffsetForbiddenBy_of_not_dvd_anchor

from CoprimePacket.

Search for a generic existing theorem before implementing the arithmetic.

Target packet under full cover:

For each S-surviving base seat r, there exist distinct outside primes p and q such that:

  p divides n^2+r
  q divides n^2+(M+r)

with:

  p in primeScalesUpTo n minus S
  q in primeScalesUpTo n minus S
  p != q

This is one of the key new structural bridges.

## Phase 10 - coarse packet complete-point gcd

Audit whether the complete points of a coarse pair are coprime.

In general:

  gcd(n^2+r, n^2+M+r)

reduces to a gcd with M, not automatically to 1.

For an S-surviving pair, all primes from S are excluded, but M contains only primes from S.

If S is a certified prime world whose modulus contains every prime divisor of M by construction, determine whether this is enough to prove:

  Nat.Coprime (n^2+r) (n^2+M+r)

for every base survivor seat.

Expected route:

- any common prime divides the difference M
- any prime divisor of M lies in S
- S-survivor excludes such a prime

If correct, prove the exact theorem.

This would be the true coarse-PrimeWorld generalization of PacketCoprimality.

Do not assume coprimality before checking the prime-divisor-to-S direction.

## Phase 11 - coarse packet factor separation

If Phase 10 succeeds, expose the useful consequences:

- no prime divides both complete coarse-pair points
- selected covering primes on the two sides are distinct
- complementary quotient factors across sides are coprime when factorization data are supplied

Reuse PacketCoprimality proof patterns, but do not duplicate its entire quotient API unless there is a downstream consumer.

The minimal useful theorem bundle is preferred.

## Phase 12 - full-cover coarse packet family

Assume:

  0 < n
  1 < M
  M <= n
  S subset primeScalesUpTo n
  KnownPrimeScales S
  SquareOffsetsFullyCovered n

For every base survivor street seat, derive a two-sided outside-prime cover packet.

The number of such packets should be exactly:

  card(primeWorldResidues S)

and for M > 1:

  Nat.totient M

This is the coarse-town replacement for the n-shift packet family.

State clearly that this is only a necessary full-cover condition.

## Phase 13 - ordered outside-prime pair incidence

Define only if useful an incidence carrier recording:

  base survivor r
  left covering prime p outside S
  right covering prime q outside S
  p != q

Prefer using actual support sets and their Cartesian product rather than choosing arbitrary witnesses.

Seek an exact transpose identity analogous to PacketCross:

  total packet incidence
  =
  sum over ordered outside-prime pairs (p,q)
    of number of base survivor offsets hit by that pair

Under full cover, derive:

  card(primeWorldResidues S)
  <=
  total coarse packet cross incidence

This is the first quantitative coarse-town frontier.

Do not confuse incidence with number of packets.

## Phase 14 - product-period sparsity for a fixed outside pair

For a fixed ordered outside-prime pair (p,q), if both primes hit two different coarse base offsets r and s on their respective sides, derive:

  p*q divides s-r

under the appropriate ordering.

The base window has width M.

Therefore if:

  M < p*q

prove:

  the fixed ordered pair (p,q) hits at most one coarse base survivor.

This should generalize the existing PacketCross theorem where n is the base-window width.

Search first for a reusable generic periodic collision lemma.

If the proof is a literal parameterized version of existing PacketCross arithmetic, consider extracting a neutral lemma rather than copying it.

## Phase 15 - near/far coarse pair split

Split ordered outside-prime pairs into:

Near:
  p*q <= M

Far:
  M < p*q

Prove:

- disjoint union
- far pair occupancy at most one
- exact coarse cross count = near contribution + far contribution
- far contribution <= number of far ordered outside-prime pairs

Compare this with the existing PacketCross near/far split.

The purpose is to determine whether the coarse period M creates a stronger sparsity threshold than the old n-shift packet.

## Phase 16 - choose canonical primorial levels inside an arbitrary shell

The research goal is not an arbitrary S forever.

Audit the existing PrimorialUniverse for a canonical bounded world S whose modulus M satisfies:

  M <= n

and is maximal or otherwise canonical below n.

Do not invent a new primorial-level selector if one already exists.

Possible semantics:

  S = primeScalesUpTo P
  M = primeWorldModulus S
  M <= n
  next refinement modulus exceeds n

If the repository lacks a canonical selector, define only the weakest finite packet needed for experiments and state the missing canonical-provider theorem explicitly.

Do not make an expensive global choice mechanism if it is not needed for the current theorem layer.

## Phase 17 - compare available outside directions with coarse packets

For a canonical or supplied coarse world S, let:

  T = primeScalesUpTo n minus S

These are the directions still allowed to cover S-surviving coarse-town seats.

Compare:

- number of coarse packets = card(primeWorldResidues S)
- number of outside directions = card T
- ordered outside pairs
- near/far product-period capacities

Search for a strict necessary inequality under full cover.

Do not assume that two distinct directions per packet must be globally unique across packets.

A simple inequality:

  2 * packets <= card T

is generally unjustified.

The correct object is an incidence or matching capacity with reuse constraints.

## Phase 18 - OldSupportCapacity integration

Try to convert the coarse-town geometry into the exact existing consumer:

  PairwiseOldSupportDisjointSquareSeatFamily n R

Search for a canonical selection R from:
- one seat per coarse pair
- both streets with additional filtering
- one representative per outside direction pattern
- a far-pair subfamily
- fold-gap filtered survivors

If a sufficiently large pairwise old-support-disjoint family can be proved, route it immediately through:

  not_fullyCovered_of_primeWorld_card_lt_pairwiseOldSupportDisjointSquareSeatFamilies

or:

  exists_prime_squareCell_of_primeWorld_card_lt_pairwiseOldSupportDisjointSquareSeatFamilies

Do not build a second capacity consumer.

If no such family construction follows, report the exact missing disjointness provider.

## Phase 19 - integrate Instruction 018 fold-gap information where it is genuinely relevant

Now test whether the Instruction 018 odd-gap PrimeWorld contributes additional restrictions to the coarse-town assignment.

Possible exact intersections to investigate:

- choose S from the odd-gap prime basis
- compare centeredFoldNorm visible primes with outside-town directions
- use order-four addresses of norm primes
- use consecutive-shell coprimality
- use centered pair gcd support to forbid some prime reuse patterns
- compare fold offset gaps with coarse period M

Do not force these structures together merely because both use prime worlds.

Record whether the intersection gives:
A. a new exclusion
B. a thinner incidence carrier
C. only a vocabulary adapter
D. no useful interaction

## Phase 20 - audit existing negative results before claiming a contradiction

The workspace audit reports that mixed-radix and CRT transport alone already realize all admissible coordinates.

Therefore:

  address geometry alone is not a contradiction.

Any new obstruction must use the full-cover pattern or an arithmetic support condition placed on top of the coordinates.

Before claiming a new provider, compare against historical audits of:
- mixed-radix square-anchor transport
- Jacobsthal frontier
- packet old/fresh matrix
- square-shell wave transport
- prior Hall or matching attempts

Preserve previous counterexamples.

## Phase 21 - finite discovery scan

For a bounded range of anchors n, choose one or more natural coarse worlds with M <= n.

For each record:

- n
- S or its cutoff parameter
- M
- card primeWorldResidues S
- base and shifted street sizes
- number of outside primes in T
- actual full-cover survivor count
- actual coarse packet incidence
- near and far ordered pair counts
- maximum occupancy of a fixed outside ordered pair
- whether coarse complete-point pairs are coprime
- whether a useful old-support-disjoint subfamily appears
- comparison with the original n-shift packet count
- comparison with Instruction 018 fold statistics where inexpensive

Search especially for:
- largest coarse packet pressure
- smallest incidence slack
- anchors 297 and 1031
- existing near-miss anchors from Instruction 016

Do not infer asymptotics.

## Phase 22 - deferred prime-power floor sum

Instruction 018 proposed:

  v_p(P_n)
  =
  sum over positive k <= v_p(N_n)
    floor((n+(p^k-1)/2)/p^k)

Do not implement this merely for completeness.

Implement it in Instruction 019 only if:
- a coarse-town or capacity theorem actually needs exact fold multiplicity by prime power, or
- repository discovery shows it closes an already existing consumer.

Otherwise preserve it as a deferred theorem contract in the report.

## Phase 23 - Continuous Gnomon Quantization status note

A separate workspace audit identified another missing bridge:

  continuous square growth
  -> integer gnomon seats

via crossing parameters similar to:

  u_k = sqrt(x^2+k) - x

This is mathematically relevant to the global DkMath architecture but is not the main implementation target of Instruction 019.

Do not implement a large real-analysis module here.

Only record:
- exact existing GapFill and DkReal APIs discovered
- whether a thin adapter already exists
- recommended future module if still missing

Keep this separate from the full-cover proof frontier.

## Desired theorem architecture

The ideal path after this checkpoint is:

  existing PrimeWorld residues
  -> square-anchor phase address
  -> one-period survivor street
  -> shifted survivor street by M
  -> coarse pair coprimality
  -> outside-prime pair assignment under full cover
  -> product-period sparsity
  -> capacity consumer

Instruction 018 should enter only through an exact adapter or extra restriction, not as a parallel duplicate world.

## Possible outcomes

Outcome A - COARSE PRIMORIAL TOWN YIELDS A NEW FULL-COVER OBSTRUCTION

The integration produces a strict capacity, matching, or old-support-disjoint-family obstruction that rules out a nontrivial class of hypothetical full covers or yields new prime endpoints.

Outcome B - COARSE PRIMORIAL TOWN YIELDS A NEW EXACT ASSIGNMENT FRONTIER

PrimeWorld, packet, and coarse-town structures are integrated exactly and a stronger necessary full-cover incidence or sparsity theorem is proved, but no uniform contradiction follows.

Outcome C - INTEGRATION CLOSES THE API GAP BUT ADDS NO NEW CAPACITY

The adapters and coarse-town geometry are exact, but all resulting full-cover statements reduce to existing packet or residue bookkeeping.

Outcome P - ONE PRECISE COARSE-TOWN CAPACITY BRIDGE REMAINS

Most adapters close, but one explicit theorem such as a generic pair occupancy, canonical primorial level, or old-support-disjoint selection blocks the assignment frontier.

## Non-goals

Do not claim:

- Legendre conjecture
- a generic Jacobsthal bound
- PNT or RH
- Bertrand
- analytic sieve estimates
- random residue independence
- that CRT geometry alone forbids full cover
- that a prime direction may be used only once globally
- that offset residue r mod M equals square-point residue (n^2+r) mod M without a hypothesis
- that primeWorldResidues S equals squareAnchorCoprimeBaseOffsets M when M = 1
- that Instruction 018 gcd aggregates classify uncovered seats

Do not introduce:
- a second PrimeWorld framework
- a second primorial framework
- a duplicate packet capacity consumer
- a heavy matching library unless a concrete finite matching theorem is actually required

## Suggested implementation surface

Prefer one or two focused modules, for example:

DkMath/NumberTheory/Legendre/PrimeWorldPacketBridge.lean
DkMath/NumberTheory/Legendre/CoarsePrimorialTown.lean

If generic arithmetic belongs naturally in Primitive, place it there and keep the Legendre adapter thin.

Do not create reverse dependencies from Primitive into Legendre.

Update the Legendre facade only after the focused modules build and the API is stable.

## Validation

For all new production declarations:

- focused builds
- lake build DkMath.NumberTheory.Legendre
- lake build DkMath
- forbidden-token scan
- print axioms for every new public declaration
- git diff --check

All new production declarations must remain free of sorryAx.

Preserve current file-header and file-marker conventions.

## Durable checkpoint protocol

Update findings after:

- repository-wide discovery audit
- PrimeWorldResidues / packet-base adapter
- odd-gap PrimeWorld bridge
- arbitrary-shell square-anchor address
- one-period base street
- shifted street
- coarse pair coprimality
- full-cover outside-prime packet
- generic pair occupancy
- near/far split
- canonical primorial-level audit
- OldSupportCapacity integration attempt
- Instruction 018 interaction test
- bounded discovery scan
- final judgment

Preserve false conjectures, negative audits, and smallest counterexamples.

## Final report

Answer explicitly:

1. Which previously unknown or out-of-scope existing theorems were discovered by the broad audit?
2. Is primeWorldResidues S exactly squareAnchorCoprimeBaseOffsets M for M>1?
3. What is the exact M=1 exception?
4. How is the Instruction 018 odd-gap prime world represented in existing PrimeWorld language?
5. What exact square-anchor phase address is used in an arbitrary shell?
6. How is one full PrimeWorld period embedded as a base street inside squareOffsets n?
7. Is the shifted M-street exactly periodic in support and address?
8. Are the complete points of a coarse survivor pair coprime?
9. Under full cover, what exact outside-prime assignment does each coarse pair require?
10. What is the exact fixed ordered-pair occupancy bound in a base window of width M?
11. Does the near/far split produce a stronger frontier than the original n-shift PacketCross?
12. Was a canonical primorial level below n already available?
13. Can the coarse town produce a PairwiseOldSupportDisjointSquareSeatFamily large enough for an existing capacity consumer?
14. Does Instruction 018 add a genuine restriction to the coarse-town assignment?
15. Was the prime-power floor-sum theorem needed or left deferred?
16. What is the narrowest remaining theorem needed for a full-cover contradiction?

End with exactly one judgment:

Outcome A - COARSE PRIMORIAL TOWN YIELDS A NEW FULL-COVER OBSTRUCTION
Outcome B - COARSE PRIMORIAL TOWN YIELDS A NEW EXACT ASSIGNMENT FRONTIER
Outcome C - INTEGRATION CLOSES THE API GAP BUT ADDS NO NEW CAPACITY
Outcome P - ONE PRECISE COARSE-TOWN CAPACITY BRIDGE REMAINS
