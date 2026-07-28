# FLT7 seven-primary terminal route: implementation roadmap

Updated: 2026-07-28
Target branch: `wip/FLT7-magic-core-260722-WiseWolf`  
Starting implementation baseline: `a635593391f4444a4c75d640b784189112ca7b36`

## 1. Goal

The remaining work is to determine whether the proved local prime-power orbit data can be assembled into a global terminal reconstruction or whether the assembly process itself produces the terminal obstruction.

The target chain is:

```text
local exact q^e packets
        ↓
finite simultaneous scale
        ↓
complete terminal modulus
        ↓
model compatibility
        ↓
lifted signed reconstruction or exact obstruction
        ↓
terminal exclusion
        ↓
recursive descent closure
        ↓
FLT7
```

Each arrow is a separate proof obligation. No checkpoint may skip an arrow by strengthening a structure field into an assumption without documenting that assumption as an explicit contract.

## 2. Roadmap principles

1. Continue from the existing terminal packet hierarchy.
2. Keep the fixed routing board throughout the entire construction.
3. Use complete prime-power depths, not arbitrary lower prime powers.
4. Treat finite CRT gluing as residue synchronization only.
5. Treat canonical-model compatibility as a separate problem.
6. Treat signed integral reconstruction as a separate problem.
7. Keep terminal exclusion independent of recursive descent closure.
8. Preserve the current WIP policy: no FLT7 claim before the exact final theorem exists.

## 3. Phase map

```text
Phase A  Canonical finite terminal prime support
Phase B  Canonical local scale family
Phase C  Finite CRT scale gluing
Phase D  Exact modulus coverage
Phase E  Canonical-model compatibility audit
Phase F  Lifted global candidate
Phase G  Terminal arithmetic decision
Phase H  Descent closure
Phase I  FLT7 public target
```

## 4. Phase A: canonical finite terminal prime support

### Objective

Represent exactly the finite set of primes dividing:

```lean
awaySevenBaseTerminalCubicRootLoad r
```

### Required facts

First expose or reuse proofs that the cubic-root load is positive and nonzero.

Then define a canonical support, preferably from `Nat.primeFactors`:

```lean
terminalCubicRootPrimeSupport
```

The support API should prove:

```lean
q ∈ terminalCubicRootPrimeSupport r
  ↔ Nat.Prime q ∧ q ∣ awaySevenBaseTerminalCubicRootLoad r
```

and:

```lean
q ∈ terminalCubicRootPrimeSupport r → q ≠ 7
```

The second theorem should be obtained from the existing terminal load facts, not inserted as a structure assumption.

### Stop gate A

Stop Phase A when every support member can be passed directly to:

```lean
nonempty_primePowerScaleProjectionPacket_of_dvd_cubicRootLoad
```

without manually rebuilding primality or load divisibility.

## 5. Phase B: canonical local scale family

### Objective

Package one local scale projection packet for every prime in the canonical support.

### Candidate interface

```lean
structure AwaySevenBaseTerminalPrimeScaleFamily
    (packet : AwaySevenBaseTerminalRoutingPacket ...) : Type where
  localPacket : ∀ q,
    q ∈ terminalCubicRootPrimeSupport r →
      AwaySevenBaseTerminalPrimePowerScaleProjectionPacket packet q
```

A noncomputable constructor may use `Classical.choose` on the existing `Nonempty` theorem.

### Required exports

For every supported prime `q`, expose:

```text
local modulus m_q = q^e_q
local scale s_q : ZMod m_q
IsUnit s_q
actual_q = weightedScale(model_q, s_q)
```

### Design warning

Do not define the support by collecting arbitrary chosen packets. The support comes from the terminal cubic-root load. The packets are chosen over that fixed support.

### Stop gate B

Stop Phase B when downstream code can quantify over one family rather than repeatedly invoke `Classical.choose`.

## 6. Phase C: finite CRT scale gluing

### Objective

Generalize the existing two-prime packet to the entire finite terminal support.

### Preferred route

Use induction over the canonical finite support.

At each step maintain:

```text
accumulated modulus M
combined scale s : ZMod M
M is the product of the included complete local moduli
for every included prime q, s reduces to s_q
s is a unit modulo M
```

### Required pairwise-coprime input

Reuse:

```lean
AwaySevenBaseTerminalPrimePowerScaleProjectionPacket
  .modulus_coprime_of_prime_ne
```

For the induction step, prove that the next local modulus is coprime to the product of the previously accumulated moduli.

### Candidate structure

```lean
AwaySevenBaseTerminalPrimePowerFiniteScaleGluingPacket
```

It should contain at least:

```text
support
family
combinedModulus
combinedScale
combinedScale_isUnit
modulus product identity
all local reduction theorems
```

### Required theorems

```lean
nonempty_finiteScaleGluingPacket
combinedScale_reduces_to_localScale
combinedModulus_eq_product
combinedScale_isUnit
```

### Stop gate C

Stop Phase C when one theorem recovers every local scale from the combined scale.

Do not proceed directly to FLT7. Finite scale synchronization alone does not synchronize the local canonical models.

## 7. Phase D: exact modulus coverage

### Objective

Identify what the product of all complete local moduli represents arithmetically.

The desired strongest theorem is:

$$\prod_{q\mid L}q^{e_q}=L$$

where:

```text
L = awaySevenBaseTerminalCubicRootLoad r
```

However, the current `e_q` is defined as the exact depth of the unique original routing cell. Codex must first prove that this exponent agrees with the `q`-adic depth in the complete cubic-root load.

### Required bridge

For a supported prime `q`, prove a theorem of the form:

```lean
terminalOriginalCellExponent_eq_padicValNat_cubicRootLoad
```

This should use:

```text
unique original cell address
pairwise coprimality inside the relevant routing column
pairwise coprimality of the cubic-root factors
exact next-power nondivisibility of the cell
```

### Possible outcomes

#### Outcome D-A

The local exponent equals the load exponent. Then prove:

```lean
finiteScaleCombinedModulus_eq_cubicRootLoad
```

#### Outcome D-B

The equality needs an additional factor or a squarefree correction. Record the exact factorization theorem instead of forcing equality.

#### Outcome D-C

The existing packet lacks a required coprimality theorem. Add only the missing coprimality bridge and stop for review.

### Stop gate D

Stop when the combined modulus has a precise arithmetic relation to the terminal cubic-root load.

## 8. Phase E: canonical-model compatibility audit

### Objective

Determine whether the local canonical models are reductions of one global model.

The current local projection stores:

```text
actual_q
model_q
scale_q
actual_q = weightedScale(model_q, scale_q)
```

The pair and finite CRT packets glue only `scale_q`.

The models differ by routing column and may contain local root parameters and correction terms. Therefore a global model cannot be assumed.

### Required reconnaissance

Codex must inspect:

```text
canonicalPrimePowerSolution_sevenV
canonicalPrimePowerSolution_leftCubic
canonicalPrimePowerSolution_rightCubic
AwayNonSevenPrimePowerOrbitSource
AwayNonSevenPrimePowerOrbitProjection
```

Then classify the situation into one of the following.

#### Outcome E-A: one global model exists

Define a global integral or product-modulus model and prove every `model_q` is its reduction.

#### Outcome E-B: a finite family of compatible global models exists

Package the remaining discrete choices explicitly. Do not erase them.

#### Outcome E-C: local models are not compatible

Extract an exact incompatibility predicate. This may itself be the terminal obstruction.

### Candidate contract

```lean
structure AwaySevenBaseTerminalGlobalModelCompatibilityPacket ... where
  globalModel : ...
  local_model_eq : ∀ q ∈ support,
    reduce globalModel q = family.localPacket q ... |>.projection.model
```

The exact global model type must be chosen only after reconnaissance.

### Stop gate E

Stop after one of E-A, E-B, or E-C is established. Do not hide model incompatibility behind choice.

## 9. Phase F: lifted global candidate

### Objective

Combine a globally compatible model with the finite combined scale.

The desired modular statement is:

```text
for every supported q,
reduction of global weighted candidate
  = actual local prime-power solution
```

### Separate subphases

#### F1. Product-modulus solution

Construct an `AwayRoutingPrimePowerSolution`-like object over the combined modulus if the row and column indexing can be made coherent.

If the varying column prevents one object of the existing type, define a new global coordinate packet rather than coercing all columns into one type.

#### F2. Integer representative

Choose canonical integer representatives for the combined scale and global model coordinates.

Prove only congruences at first.

#### F3. Equality from congruence

To turn congruence into equality, obtain explicit bounds or exact divisibility whose modulus exceeds the possible difference.

Do not use “all prime powers divide the difference” as equality unless the product modulus and the size or factorization of the difference are both controlled.

### Stop gate F

Stop when either:

```text
one signed integral reconstruction packet exists
```

or:

```text
an exact reconstruction obstruction is isolated
```

## 10. Phase G: terminal arithmetic decision

### Objective

Use the exact quotient packet together with the result of Phase F to decide the terminal depth-one case.

### Branch organization

Keep the row/unit-sector split explicit:

```text
positive sector → row Y
negative sector → row Z or row Sum
```

Reuse:

```lean
row_resolved_complete_normal_form
row_resolved_endpoint_quotient_normal_form
negative_sector_endpoint_load_bridge
```

### Expected result forms

#### G-A. Direct terminal exclusion

```lean
no_awaySevenBaseTerminalRoutingPacket_at_depth_one
```

#### G-B. Strict smaller counterexample

Construct an exact smaller packet satisfying the descent provider contract.

#### G-C. Remaining arithmetic receiver

If the proof reduces to one new arithmetic theorem, define the receiver as a named predicate and prove the terminal theorem conditionally from it. The receiver must state exactly the missing mathematics.

### Stop gate G

Do not proceed to recursive closure until the terminal result is unconditional or its final receiver is explicit and independently reviewable.

## 11. Phase H: descent closure

### Objective

Discharge the existing:

```lean
AwayDescentClosureProvider
```

using the terminal result and the already proved strict away-depth drop.

### Requirements

```text
preserve positivity
preserve primitive normalization
preserve the FLT7 equation
produce a strictly smaller well-founded measure
connect every nonterminal and terminal branch
```

Use a measure already present in the FLT7 route if possible. Do not introduce a new ad hoc measure unless the existing descent statement cannot consume the result.

### Stop gate H

Stop when the provider is constructed without assumptions specific to a hypothetical counterexample beyond the existing packet fields.

### DESCENT-001 audit result

DESCENT-001 reached Outcome C. The exact construction-oriented receiver is:

```lean
AwayDescentReconstructionSeed p
```

It consists of a new away coordinate normal form together with proof that its
exceptional endpoint carrier is exactly:

```lean
Int.natAbs p.normal.root.snd
```

Lean proves both directions:

```lean
AwayDescentReconstructionSeed.toClosureProvider
AwayDescentClosureProvider.toReconstructionSeed
nonempty_descentReconstructionSeed_iff_closureProvider
```

Thus the seed is neither an accidental strengthening nor a weaker local
shadow: inhabiting it is equivalent to constructing the original
`AwayDescentClosureProvider`. Once supplied, the existing strict depth drop is
obtained by `away_depth_descent_of_reconstructionSeed`.

The current terminal CRT, canonical local-orbit, fixed-system, and carry APIs
do not construct the seed. They provide congruence and factor data for the old
counterexample, but not a new positive primitive natural triple satisfying
`nextX ^ 7 + nextY ^ 7 = nextZ ^ 7`. Any lifted-branch descent work must
therefore target this integral reconstruction directly.

### DESCENT-002 terminal seed decision

DESCENT-002 reached Outcome D for the terminal branch. Lean proves:

```lean
AwayDescentReconstructionSeed.two_le_pivotExponent
AwayDescentClosureProvider.two_le_pivotExponent
```

Every reconstructed next away carrier has positive seven-adic depth. Since it
is identified with the old root second coordinate, a seed forces the old pivot
exponent to be at least two. Consequently:

```lean
no_descentReconstructionSeed_of_exponent_eq_one
no_descentClosureProvider_of_exponent_eq_one
```

At terminal depth one the requested seed is not merely unavailable from the
current APIs; it is mathematically incompatible with the valuation-transfer
contract. The terminal branch must therefore be excluded directly. Provider
construction remains a meaningful target only for the lifted branch
`1 < p.exponent`.

## 12. Phase I: final FLT7 public target

### Objective

Connect the unconditional descent closure to the public FLT7 theorem.

### Final audit

Before exposing the target:

```text
check no new axiom or sorry
check theorem statement is exactly exponent 7
check positivity and natural/integer domains
check permutation or sign normalization coverage
check facade imports
check axiom audit
```

Only then add the public theorem and update the facade documentation.

## 13. Recommended checkpoint sequence

complete

```text
FLT7-CRT-001  terminal prime support
FLT7-CRT-002  local scale family
FLT7-CRT-003  finite modulus coprimality
FLT7-CRT-004  finite CRT gluing packet
FLT7-CRT-005  simultaneous local reduction
FLT7-LOAD-001 exponent transport from cell to root load
FLT7-LOAD-002 product modulus reconstruction
FLT7-MODEL-001 local model compatibility audit
FLT7-MODEL-002 global model or incompatibility packet
FLT7-LIFT-001 product-modulus weighted candidate
FLT7-LIFT-002 integer representative and congruence packet
FLT7-LIFT-003 signed reconstruction or exact obstruction
FLT7-TERM-001 row-sensitive terminal decision
FLT7-TERM-002
FLT7-TERM-003
FLT7-TERM-004 universal global coordinate equations and integer carries
FLT7-TERM-005 exact 3 x 3 cell prime partition and modulus reconstruction
FLT7-TERM-006 cellwise universal CRT and row-resolved carry packet
FLT7-TERM-007 fixed cell-system compatibility
FLT7-TERM-008 cellwise fixed-system carry dependency audit
FLT7-DESCENT-001 provider construction interface and exact receiver (Outcome C)
FLT7-DESCENT-002 terminal reconstruction seed exclusion (Outcome D)
FLT7-TERM-009 terminal Fermat chart resolution (Outcome C)
FLT7-TERM-010 Row-Z alternating split and signed residual extraction (Outcome A)
FLT7-RAMIFIED-001 common summit and exact second-coordinate depth (Outcome A)
FLT7-RAMIFIED-002 formal coprime routing and gap synchronization (Outcome A)
FLT7-RAMIFIED-003 exact ramified gap-unit bridge (Outcome A)
FLT7-RAMIFIED-004 coherent unit tower and mod-49 class audit (Outcome C)
FLT7-RAMIFIED-005 canonical residual-root class reduction (Outcome A)
```

TERM-007 discharges the former TERM-006 stop gate:

```lean
AwaySevenBaseTerminalCellwiseFixedSystemObligation
```

Each reduced global CRT model is now proved to be the coordinate tuple of a
solution to the fixed endpoint-row/root-column system for that exact cell
modulus.

TERM-008 proves that every fixed-system first-coordinate carry is an explicit
linear combination of the global universal first carry and its cell's
endpoint/root carries.  This is Outcome A of the dependency audit: the nine
first-coordinate carries are bookkeeping rather than new independent
constraints.  Further carry accumulation is therefore not a descent route.

incomplete

```txt
FLT7-DESCENT-003 inhabit the reconstruction seed in the lifted branch
FLT7-FINAL-001 public FLT7 theorem and audit
```

TERM-009 proves the exact chart classification:

```text
Row Sum -> contradiction
Row Y   -> natural swapped ramified chart
Row Z   -> primitive signed chart with seven-divisible gap
```

The existing natural ramified extraction cannot be reused as a thin wrapper
for Row Z: its `SevenAdicCounterexamplePacket`, `SevenAdicPowerSplit`, and
`SevenQuadraticResidualPacket` chain is indexed by positive naturals and uses
`z - y`, natural `GN`, positivity, `padicValNat`, and natural coprime factor
splitting.  TERM-009 therefore reaches Outcome C and exports
`AwaySevenBaseTerminalRowZSignedRamifiedArithmeticObligation` as the exact
remaining signed quadratic extraction receiver.

TERM-010 inhabits that receiver.  It constructs the exact alternating split

```text
x + y = 7^6 * a^7
A7(x,y) = 7 * b^7
z = 7 * a * b
```

then applies the existing integer `sevenAxis` peeling theorem to
`cyclotomicSevenToTraceOne x (-y)`.  Signed cubic-coordinate coprimality makes
the peeled residual core coprime to its conjugate, and its norm is `b^7`.
The TraceOne UFD extraction therefore proves that the residual core itself is
a seventh power.  Consequently:

```lean
AwaySevenBaseTerminalRowZProfile.signedRamified
AwaySevenBaseTerminalUnitSectorPacket.ramifiedChartResolution
```

are now available.  Every surviving terminal away row reaches a ramified
chart.  RAMIFIED-001 is the next separate obligation; TERM-010 does not close
that summit or prove FLT7.

DESCENT-003 remains separately scoped to `1 < p.exponent`, where the old root
second coordinate still has positive seven-adic depth and the reconstruction
seed contract is valuation-compatible.  It must not be merged with the
terminal signed-chart or ramified-summit work.

Each checkpoint should add one conceptual layer. Avoid combining support, finite CRT, model compatibility, and integer reconstruction into one large commit.

RAMIFIED-001 unifies both terminal charts into
`PrimitiveRamifiedSummitPacket`.  It proves the exact gap expansion and
second-coordinate identity

```text
seventhPowerSnd(root) = 7^6 * gapRoot^7 * ramifiedGapQuotient.snd
```

with both remaining factors seven-units.  Consequently:

```text
padicValNat 7 |root.snd| = 5 + 7 * padicValNat 7 gapRoot
```

The ramified second coordinate also has the exact linear-cubic-cubic
factorization, together with the cubic sum and difference identities and the
endpoint-product bridge.  This is Outcome A for RAMIFIED-001.  It exposes a
new ramified 3 x 3 routing board, but no strict descent or smaller Fermat
solution is claimed.

RAMIFIED-002 upgrades that board to a formal `CoprimeTripleRouting`.  It
proves nonvanishing and pairwise coprimality for

```text
endpoint: |c|, |e|, |c+e|
root:     |T|, |L|, |R|
```

and packages the resulting nine exact gcd addresses as
`RamifiedCubicRoutingPacket`.  It also proves:

```text
v7(|R-L|) = v7(|c-e|)
          = 6 + 7 * v7(gapRoot)
```

This is Outcome A for RAMIFIED-002.  The routing grid and self-similar gap
depth are complete; descent construction remains a separate obligation.

RAMIFIED-003 upgrades equal gap depth to an exact unit relation.  The integral
bridge avoids division:

```text
(R - L) * S = (c - e) * Q * norm(root)
```

where `S`, `Q`, and `norm(root)` are all seven-units.  The resulting
`RamifiedGapUnitBridgePacket` supplies the explicit equality

```text
cubicGap = endpointGap * (rightUnit * leftUnit⁻¹)
```

over every `ZMod (7^k)`.  This is Outcome A.  The checkpoint stops at the
local gap-unit equivalence and does not infer a smaller Fermat solution.

RAMIFIED-004 proves adjacent-level coherence of `explicitUnit` and performs
the first nontrivial unit-class audit:

```text
IsSeventhPowerMod49
  ↔ explicitUnit(2)^7 = explicitUnit(2)
  ↔ explicitUnit(2) ∈ {1, 18, 19, 30, 31, 48}.
```

This is Outcome C.  The unit-class classifier is finite and exact, while the
common summit does not yet force either branch.  The next independent inputs
are a canonical summit residue classifier and, for an obstruction argument,
a receiver asserting seventh-power shape of the root-cubic gap.

RAMIFIED-005 completes the canonical mod-`49` normalization.  The root second
coordinate vanishes, the quotient/core/norm factors reduce explicitly, and:

```text
explicitUnit = -endpointRight^2 * residualRoot⁻²
residualRoot ∈ {1, 8, 15, 22, 29, 36, 43}
IsSeventhPowerMod49 ↔ residualRoot = 1
```

The canonical seventh-power unit residues are exactly `{19, 31, 48}`.  This is
Outcome A.  The next independent layer is a compatible seventh-root lifting
theorem through the coherent `7^k` tower.  Such a local lift is not an integer
or natural seventh root and must remain separate from global reconstruction.

RAMIFIED-006 follows the integer factor route before higher Kummer lifting.
It strengthens the common summit by retaining the terminal carrier and fixes:

```text
root.snd depth = 5
endpoint gap depth = 6
cubic gap depth = 6
v * sndCore = 7^5 * gapRoot^7 * gapQuotient
```

The full left/right coprimality ledger is proved and the corresponding
`CoprimeTripleRouting |v| |sndCore| 1 7^5 gapRoot^7 |gapQuotient|` is
inhabited. The remaining global-shape obligation is represented exactly by
`ramifiedCompensationCore * residualRoot` being a seventh power. The next
normalization checkpoint must identify routing cell `c13` with
`gcd(|v|,|gapQuotient|)` and extract the two seventh-power roots in the
`gapRoot^7` column. No descent follows before that bridge is proved.

RAMIFIED-007 completes that normalization checkpoint. All nine cells of a
`CoprimeTripleRouting` are identified with their canonical gcd addresses once
the two source columns are pairwise coprime. Applied to the terminal routing
board, this yields:

```text
gapRoot = X * Y
|v| = 7^5 * X^7 * C
sndCore = Y^7 * D
|gapQuotient| = C * D
|R-L| = 7^6 * X^7 * (C * residualRoot).
```

The compensation receiver is now equivalent to the displayed cubic-gap
seventh-power shape, and also equivalent to `C` and `residualRoot` being
independent seventh powers. This is Outcome A.

RAMIFIED-008 follows the corrected target rather than trying to make
`gapRoot` a seventh power. On the receiver branch, the residual key makes the
quadratic root norm a seventh power. Primitive conjugate coprimality then
gives:

```text
root = innerRoot^7
coordinate = sevenAxis * innerRoot^49
norm innerRoot = residualNormRoot
v7(|innerRoot.snd|) = 4.
```

The depth-four equation splits completely:

```text
|innerRoot.snd| = 7^4 * M^7
|seventhPowerSndCore(innerRoot)| = N^7.
```

Both cubic factors of the inner core are coprime and become signed integer
seventh powers. This is Outcome A, conditional on the receiver. It neither
proves the receiver nor constructs new endpoints.

The next checkpoint is RAMIFIED-009. Its input is now stronger than merely a
sextic-core seventh power: both integer cubic forms already have signed
seventh-power values. RAMIFIED-009 should introduce the discriminant-49 real
cubic order, verify the two norm formulas and the ramified-axis identities,
and stop before any ideal or unit-class extraction not justified by the new
order API.

RAMIFIED-009 is complete with Outcome A. The implemented cubic order has the
defining relation and a multiplicative determinant norm. The left/right
cubic factors are exactly the norms of the two source elements. The
ramified axis `pi` has norm `-7`; its cube is `7*epsilon`; and `epsilon` is
an explicit unit of norm `-1`. The normalized axis
`varpi = epsilon^4*pi` removes the remaining unit coefficient:

```text
etaR - etaL = varpi^6 * Z^7.
```

This equation is now attached directly to every inhabited RAMIFIED-008
receiver packet, together with signed roots `l,r` and
`r^7-l^7 = 7*a*n*(a+n)`.

RAMIFIED-010 is complete with Outcome A. Translating by
`theta = alpha - 3` exposes the Eisenstein polynomial
`X^3 + 7*X^2 + 14*X + 7`. Lean proves its irreducibility, its
discriminant `49`, and that its power-basis order is the full ring of
integers. The original three-coordinate ring is explicitly equivalent to
that maximal order. The field is totally real, has exact Minkowski class
bound `14/9`, and its ring of integers is principal, so its class number is
one. The cyclic order-three automorphism is available both on the coordinate
order and on the full ring of integers.

RAMIFIED-011A is complete with Outcome A. The principal-ideal property is
transported to `SevenRealCubicInt`, and direct element GCD arguments replace
the planned ideal-exponent ledger. A primitive linear source with
seven-divisible second coordinate is pairwise coprime to its two cyclic
conjugates; the product of all three conjugates is its determinant norm.
Mathlib's coprime-power extractor therefore proves both RAMIFIED sources are
unit multiples of seventh powers. The resulting packet retains:

```text
etaL = uL*xiL^7
etaR = uR*xiR^7
uR*xiR^7 - uL*xiL^7 = varpi^6*Z^7.
```

The next independent checkpoints are:

```text
RAMIFIED-009B  exact signed-root gap routing over Int/Nat
RAMIFIED-011U  mod-7 unit classes and global seventh-power criterion
RAMIFIED-012   exact source seventh powers and pure difference equation
RAMIFIED-013   ramified depth 13/10/3 split and axis drop
```

The ideal/class-group obstruction is now closed, but unit elimination remains
independent. Reduction modulo `7` should first formalize the nilpotent
coordinate `tau = theta mod 7`, prove `tau^3 = 0`, and prove seventh powers
reduce to scalars. Sufficiency requires more: the two displayed units must
be shown to represent all global unit classes modulo seventh powers, or an
equivalent cardinality/surjectivity theorem must be supplied. Class number
one alone does not prove that unit statement.

## 14. Review outcomes for Codex

At the end of every checkpoint, report one of:

```text
Outcome A: planned theorem completed
Outcome B: a stronger existing theorem made the checkpoint unnecessary
Outcome C: exact missing bridge identified
Outcome D: proposed statement is false; counterexample or type obstruction found
```

A precise Outcome C or D is useful progress. Do not replace it with an unproved stronger assumption.
