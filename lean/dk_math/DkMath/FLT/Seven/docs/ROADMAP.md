# FLT7 seven-primary terminal route: implementation roadmap

Updated: 2026-07-29
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

RAMIFIED-011U and RAMIFIED-012 are complete with Outcome A. The translated
theta coordinates modulo seven give a multiplicative truncated logarithm
with values in `F_7^2`. The two explicit units map to `(5,5)` and `(2,5)`,
whose determinant is one. Dirichlet rank two and torsion `±1` make the
global unit quotient modulo seventh powers a `49`-element group, so the
descended logarithm is bijective. Therefore:

```text
u is a seventh power <-> projectiveLog(u) = 0.
```

The primitive loaded-source equations force the two extracted unit
logarithms to vanish separately. After absorbing their seventh roots:

```text
etaL = XL^7
etaR = XR^7
XR^7 - XL^7 = varpi^6*Z^7.
```

The independent checkpoints queued at the end of RAMIFIED-012 were:

```text
RAMIFIED-009B  exact signed-root gap routing over Int/Nat
RAMIFIED-013   ramified depth 13/10/3 split and axis drop
```

RAMIFIED-013 is complete with Outcome A in
`SevenRealCubicAxisDrop.lean`. Starting from
`RamifiedRealCubicExactPowerPacket`, Lean proves the exact theta depths

```text
RHS = 13
root gap = 10
seventh quotient = 3.
```

It removes the displayed axis powers, proves the two remaining cores
coprime, extracts the gap core as a seventh power up to a unit, and absorbs
that unit using the coprime exponents three and seven. The final packet
contains:

```text
Associated droppedAxis theta
rootGap = droppedAxis^3 * descentWitness^7.
```

This closes the ramified algebraic axis arithmetic. It does not close the
earlier `AwayDescentClosureProvider` and does not itself create a new
primitive Fermat chart.

## 13. Post-RAMIFIED fusion and reconstruction route

The next phase must begin from `RamifiedRealCubicAxisDropPacket`, not by
reopening the completed unit or theta-depth calculations.

### FUSION-001: integer shadow compatibility

Use the proved identities

```text
Norm(XL) = signedLeftRoot
Norm(XR) = signedRightRoot
XR - XL = droppedAxis^3 * descentWitness^7
```

to determine the exact additional data needed to reconstruct the integer or
quadratic chart. The first audit must respect that the determinant norm is
nonlinear:

```text
Norm(XR) - Norm(XL) != Norm(XR - XL)
```

in general. Therefore the signed-root depth-four claim cannot be inferred by
a formal norm application. It needs a checked first-variation identity,
coordinate expansion, or an independent integer routing proof.

### FUSION-002: seventh-root source-plane classification

Classify real-cubic roots whose seventh powers lie in the two-dimensional
source plane. Determine whether the roots stay in that plane, lie in finitely
many unit-translated sectors, or require the full degree-six cyclotomic
carrier.

Current checkpoint (2026-07-29): the exact third-coordinate expansion is
proved in `SevenRealCubicSourcePlane.lean`. Thus this classification is now
the integral zero-locus problem for the homogeneous degree-seven polynomial
`seventhSourcePlaneEquation`. The expansion alone does not select Outcome
A, B, or C; proving that arithmetic classification is the next gate.

The theta-basis refinement is now formalized through FUSION-002C:
`SevenRealCubicThetaCoordinates.lean` gives the integral change of basis, and
`SevenRealCubicThetaSeventhPower.lean` gives the two divided seventh-power
coordinates with corrected triangular factors. In the identities

```text
G = B*GB(A,B,C) + 7*C^2*GC(A,C)
H = C*HC(A,B,C) + B^2*HB(A,B),
```

the dependencies displayed above are essential. Their four leading residues
are proved. The exact-power source equations are now connected by
`SevenRamifiedThetaJetLifting.lean` and
`SevenRamifiedPairedThetaRootJet.lean`. FUSION-002 therefore exits with:

```text
B_left  = 7^3 * U_left,   U_left  != 0 mod 7
B_right = 7^3 * U_right,  U_right != 0 mod 7
C_left  = 7^6 * V_left,   V_left  != 0 mod 7
C_right = 7^6 * V_right,  V_right != 0 mod 7

U_left/A  = -tau
U_right/A =  tau
V_left/A = V_right/A = -3*tau^2.
```

This is the controlled finite theta-jet outcome, not unrestricted
three-coordinate Outcome C. The next gate is an explicit identification
between the new `(tau^3,tau^2)` unit address and either the fixed integer
routing cells or the six cyclotomic linear factors.

### FUSION-003: chart reconstruction or full cyclotomic lift

Use the FUSION-002 outcome either to reconstruct the integer/quadratic chart
directly or to prove the linear-factor Kummer packet in the full cyclotomic
carrier.

Current checkpoint (2026-07-30): FUSION-003C cyclic phase is complete through
the comparison boundary. The algebraic root gap has exact leading residue
`thetaResidue gapCore = -2*m`, and the six unit sectors are formally
decomposed as `μ₂ × μ₃`. The signed routing board has an explicit unit shadow,
signed margin companion, and two `K_{2,3}` cycle ratios.

The surviving away row provenance had been erased by the common summit.
It is now retained by a thin pre-summit packet, but no equality between its
Y/Z sign and `tau^3` has been proved. Such an equality requires an explicit
bridge between the relevant normalized units.

The two cycle ratios are no longer treated as unrelated free parameters.
Their quotient is fixed up to the sign erased by `Int.natAbs`:

```text
kappa12 / kappa23 = |m|/|a|
(kappa12 / kappa23)^2 = tau^2.
```

The abstract routing shadow nevertheless has both a visible ternary cycle
action and a hidden ternary row gauge. Lean witnesses prove that margins do
not determine cycle phase and that margins plus cycles do not determine the
full unit board.

On the cubic side,

```text
sigma(theta) = theta*(theta+4)
thetaResidue(rotated depth-ten core) = 4*thetaResidue(core),
```

giving the orbit residues `-2*m`, `-m`, and `3*m`. The relative real index

```text
relativeRealIndex(k) = (k/tau)^2
```

has fibre one exactly `{tau,-tau}`. This selects a conjugate pair only.

The next gate is a rotation-routing naturality packet: rotate the signed
algebraic root pair, transport or reconstruct its coherent routing shadow,
and prove whether this induces the visible cycle twist or the hidden row
gauge. Merely identifying the two abstract three-element index sets is not
sufficient. Only an action-level comparison may inhabit the cyclic alignment
packet and choose between chart reconstruction up to rotation and the
conjugate-pair-equivariant cyclotomic route.

FUSION-003D follows the conjugate-pair-equivariant route. The three real pair
carriers and normalized cores are formalized, with

```text
P_0*P_1*P_2 = signedSeventhQuotient r l
P_i = theta*C_i
thetaResidue(C_i) = -pairPhase(i)
-(theta+1)^2*C_0*C_1*C_2 = quotientRoot.
```

The explicit phase equivalence selects the core indexed by `tau^2`, and the
left and right normalized quadratic jets both equal three times its residue.

Current checkpoint (2026-07-30): FUSION-003E closes the real-pair
coprimality and norm layer:

```text
Pairwise (fun i j => IsCoprime C_i C_j)
sigma(P_0)=P_1, sigma(P_1)=P_2, sigma(P_2)=P_0
norm(C_i) = -quotientRoot
c13=a^7, c23=b^7, c33=1.
```

The quotient row is reduced to the exact two-cell gate

```text
quotientRoot is a signed seventh power
  iff
c21 and c22 are natural seventh powers.
```

Once the right side is supplied, all three PID associated-power extractions
are implemented. The next checkpoint must control these two canonical gcd
addresses through genuine terminal provenance/coherence, or construct a
sign- and integrality-preserving loaded-core packet with a proved norm
identity. Do not transfer `c21_eq_one` from the earlier RAMIFIED-006 board:
that board has different margins and no comparison theorem currently exists.

Current checkpoint (2026-07-30): FUSION-003F completes both proposed
continuations. For every prime `q | quotientRoot`, the canonical signed-root
ratio has exact order seven and gives

```text
q % 14 = 1
beta = 1 + ratio + ratio^-1
evalAlphaRoot(C_0) = 0
evalAlphaRoot(theta) != 0.
```

On the integral side, the two scalar cells are allocated by PID gcd
projections:

```text
load21_i = gcd(c21,C_i)
load22_i = gcd(c22,C_i)
C_i = (load21_i*load22_i)*D_i
D_i ~ residualRoot_i^7.
```

The load families multiply back to `c21,c22`, remain coherent under the
order-three Galois action up to association, and have the exact norm ledger

```text
|norm(load21_i)| = c21
|norm(load22_i)| = c22
c21*c22*|norm(D_i)| = |quotientRoot|.
```

Thus the loaded residual split is unconditional even when the two scalar
cells are not seventh powers. If they are seventh powers, their individual
gcd loads are extracted and absorbed, recovering the earlier conditional
three-core power packet.

The immediate local refinement is also implemented. Each prime divisor of
`c21` or `c22` now selects the corresponding gcd load in the explicit maximal
`evalAlphaRoot` kernel. The competing coprime load is excluded, the kernel
contracts to `(q)`, and its residue quotient has cardinality `q`. Since one
gcd load may contain several primes or prime powers, the proved statement is
`span(load) ≤ kernel`, not equality. The exact kernel factor count in the load
ideal is now also formalized:

```text
kernel^k divides span(load) iff k <= count
count = padicValNat q cell.
```

The equality follows from the complete splitting of `(q)` into the three
cyclic real-cubic kernels. A finite-support product theorem reconstructs the
whole principal load ideal from these exact local powers.

The oriented degree-six factor is now constructed in the concrete quadratic
algebra over the real cubic order. It has explicit rank-six coordinates,
conjugate seventh roots, all local ratio evaluations, and two distinct
maximal comaximal degree-one kernels above each real-cubic address. The
conjugate product formula and exact equality between the extended real prime
and the product of the two conjugate primes are proved.

The finite global oriented launchpad is now implemented as
`DegreeSixOrientedLoadFactorizationPacket`. It retains the old support and
`padicValNat` exponents, splits every mapped real-prime power into its
oriented/conjugate pair, proves cross-prime pairwise comaximality, and
identifies the complete finite product with the principal ideal of the
embedded load.

ULTRA/U1.1 is now implemented as
`GlobalOrientedPrimeFactorizationPacket`. The real order-three rotation lifts
to an explicit order-three automorphism of the concrete degree-six carrier,
sending `zeta` to `zeta^2` and commuting with quadratic conjugation. It cycles
the three oriented primes and their three conjugates, preserves their exact
real contractions and fibre powers, and identifies the complete finite
product at every phase with the principal ideal of the corresponding
Galois-positioned load. Support, routing provenance, and exponents are
unchanged.

The direct signed-root candidate is formally impossible:

```text
signedRightRoot^7 - signedLeftRoot^7
  = 7^5*gapRoot*quotientRoot
7^6 ∤ signedRightRoot^7 - signedLeftRoot^7,
```

so it cannot be an integer seventh power. The next global checkpoint must not
reuse `(signedRightRoot,-signedLeftRoot)` as a Fermat chart. Starting from the
completed oriented launchpad, it must determine exact valuation ownership in
the two linear carriers and then prove an element-level power statement or
record its exact obstruction before any primitive chart or strict decrease.

ULTRA/U1.2 now completes that valuation-ownership checkpoint.  The prime above
seven is the explicit uniformizer ideal and has exact multiplicity one in
each carrier.  Every nonramified rational prime dividing the complete signed
`quotientRoot` has exactly its ordinary `padicValNat` exponent in the selected
oriented carrier kernel, with the conjugate result on the conjugate carrier
and the opposite orientations excluded.  Combining all local cutoffs gives
the exact global equalities

```text
ramifiedPrime * globalOrientedCoreHalfIdeal
  = span {cyclotomicDegreeSixCarrier}
ramifiedPrime * globalConjugateCoreHalfIdeal
  = span {cyclotomicDegreeSixCarrierConj}.
```

The next U1.3 event must split each full unramified exponent into the two
routed load exponents plus seven times the residual exponent, while retaining
the same full support and orientations.  It must then state exactly what
principality or unit information is still required for element-level
extraction.

ULTRA/U1.3 now completes this ideal extraction.  A canonical residual norm
root gives

```text
padicValNat q |quotientRoot|
  = padicValNat q c21 + padicValNat q c22
      + 7 * padicValNat q row2ResidualNormRoot
```

for every prime `q`.  Zero-exponent extension proves that the full-support
load products are exactly the routed phase-zero load halves.  Hence both
carrier principal ideals have the exact form

```text
ramified loaded carrier ideal * oriented residual ideal^7,
```

and quadratic conjugation exchanges the two forms.  U1.4 must pass from these
ideal identities to compatible element equations.  The selected cheapest
route is to prove principality of the concrete carrier via a surjective map
from the seventh cyclotomic ring of integers; no full ring-of-integers
identification should be required.  Any associated unit must remain explicit
or be absorbed into the chosen load generator, not assumed to be a seventh
power.

ULTRA/U1.4 now completes this element-level passage.  The abstract seventh
cyclotomic field has principal ring of integers by a checked Minkowski bound:
only rational primes two and three could occur below the bound, while their
cyclotomic residue degrees make the corresponding prime-ideal norms too
large.  The concrete carrier is generated by `zeta`, so the abstract integral
power basis maps onto it.  Principality therefore transports through the
surjection without a full ring-of-integers equivalence.

For each U1.3 identity, PID generators and principal-ideal association yield

```text
carrier = loadElement * residualRoot^7.
```

The associated unit is incorporated into `loadElement`, which preserves its
principal ideal.  The conjugate load and residual witnesses are defined by
quadratic star, giving a coherent second equation rather than a second
independent choice.

U1.5 must not mistake this multiplicative equation for an additive Fermat
chart.  It must either construct new integer coordinates and an actual
seventh-power sum, or expose the exact extra compatibility receiver.  The
known signed-root triple remains unavailable because its seventh-power
difference has exact seven-adic depth five.

ULTRA/U1.5 now closes that audit with Outcome C.  The element equation has
exactly two unconditional projections:

```text
coordinates(load*root^7) = [R,0,0,-L,0,0]
7*quotientRoot = norm(load)*norm(root)^7.
```

The all-six-phase product is precisely the second identity, not a new
additive relation.  Coordinate projection is formally nonmultiplicative, and
there is no unital ring homomorphism from the concrete carrier to `ℤ`.
Moreover the U1.4 residual witness has a nontrivial `mu_7` gauge:

```text
span {zeta*root} = span {root}
(zeta*root)^7 = root^7
coordinates (zeta*root) != coordinates root.
```

The carrier equation therefore does not select a canonical integral
coordinate vector.  Event U1.6 starts with no primitive reconstructed chart,
so it must record the exact strict-decrease failure boundary.  Any future
chart route must first prove either a `mu_7`-invariant three-coordinate
extractor or a phase normalization and then independently prove the signed
Fermat identity, nonvanishing, primitivity, normalization, and terminal
provenance.

ULTRA/U1.6 now records the strongest strict-decrease boundary available
without that chart.  The older ramified extraction already contains:

```text
v7(internal quadratic-root carrier) = 4
v7(preceding summit carrier) = 5
v7(internal carrier) < v7(outer carrier).
```

The named `InternalDepthFourCounterexampleReconstructionObligation` asks for
a positive primitive away counterexample packet whose exceptional carrier is
the depth-four coordinate.  It is equivalent to the corresponding strict
candidate because the inequality is automatic.  Therefore the missing
mathematics is counterexample reconstruction, not another valuation bound.

This conditional comparison is not yet a recursive descent step.  The
reconstruction obligation is uninhabited, and a later development must also
index the ramified source and new away route inside one well-founded
state/measure transition.  ULTRA/U1 ends here with Outcome C.  NORMAL recovery
should preserve this exact boundary rather than claim FLT7.

### FUSION-004/005: primitive chart and strict global drop

Choose and prove an explicit well-founded measure smaller for the reconstructed
chart. Algebraic theta depth alone is not yet that measure. Only after this
strict-drop theorem may the result be connected to
`AwayDescentClosureProvider`.

### Stop gate

Stop before claiming recursive descent or FLT7 unless all three arrows are
inhabited:

```text
balanced algebraic/integer fusion
  -> primitive integer/quadratic counterexample
  -> strict well-founded decrease.
```

## 14. Review outcomes for Codex

At the end of every checkpoint, report one of:

```text
Outcome A: planned theorem completed
Outcome B: a stronger existing theorem made the checkpoint unnecessary
Outcome C: exact missing bridge identified
Outcome D: proposed statement is false; counterexample or type obstruction found
```

A precise Outcome C or D is useful progress. Do not replace it with an unproved stronger assumption.
