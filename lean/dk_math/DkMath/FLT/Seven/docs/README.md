# FLT7 seven-primary terminal route documents

This directory contains the handoff and implementation documents for the remaining FLT7 work on PR #65.

## Documents

- [STATUS.md](STATUS.md) — proved implementation state, packet hierarchy, and explicit open obligations.
- [ROADMAP.md](ROADMAP.md) — staged route from finite CRT synchronization to terminal exclusion, descent closure, and the final FLT7 target.
- [IMPLEMENTATION_DESIGN.md](IMPLEMENTATION_DESIGN.md) — proposed Lean modules, structures, theorem surfaces, checkpoint boundaries, and the first Codex task.

## Current starting point

The implemented source route currently reaches:

```text
terminal prime q
  → exact original routing depth q^e
  → explicit prime-power orbit
  → column-independent local unit scale
  → finite CRT scale and model reconstruction
  → original-coordinate signed winding
  → universal global coordinate equations and integer equation carries
  → exact 3 x 3 cell prime partition
  → reduction to each exact cell modulus
  → fixed endpoint-row/root-column solution for every cell model
  → exact cell integer carries from common signed representatives
  → proof that every cell first carry is dependent
  → exact reconstruction seed equivalent to the descent provider
  → proof that a terminal-depth seed/provider is impossible
  → terminal Row-Y / Row-Z ramified chart resolution
  → one primitive common ramified summit
  → exact root-snd depth and ramified cubic factor grid
  → formal ramified 3 x 3 coprime routing
  → endpoint/root-cubic gap-depth synchronization
  → exact integral and ZMod(7^k) gap-unit bridge
  → coherent unit tower and finite mod-49 seventh-power classifier
  → canonical residual-root one-digit branch selector
  → terminal exact depth 5/6/6 and second-coordinate 2 x 3 routing
  → integral ramified compensation-core receiver
  → canonical 2 x 3 split and exact cubic-gap seventh-shape equivalence
  → receiver-induced quadratic root extraction and strict depth 5 to 4 drop
  → discriminant-49 cubic norm carrier and pure ramified-axis source difference
  → maximal real-cubic order, class number one, and coprime source extraction
  → projective mod-7 unit-class isomorphism and exact source seventh powers
  → pure real-cubic second-case equation
  → exact theta-depth ledger 13 = 10 + 3
  → coprime away-axis core extraction
  → real-cubic root-gap axis drop
```

`AwaySevenBaseTerminalCellwiseFixedSystemObligation` is discharged, and
`AwaySevenBaseTerminalCellIntegerCarryPacket.firstCarry_eq` proves that the
nine fixed-system first-coordinate carries contain no new independent
constraint. The carry exploration therefore stops here.
`AwayDescentReconstructionSeed` exposes the exact integral data needed for the
next counterexample, and Lean proves that it is equivalent to
`AwayDescentClosureProvider`. DESCENT-001 therefore ends with Outcome C: the
provider construction interface and strict-drop bridge are complete, while
inhabiting the seed remains open in general. DESCENT-002 gives Outcome D at
terminal depth: a seed or provider would force pivot exponent at least two, so
neither can inhabit the exponent-one branch. TERM-009/010 then exclude Row Sum
and normalize Row Y and Row Z into ramified charts. RAMIFIED-001 unifies those
charts and proves the exact root-snd depth
`5 + 7 * padicValNat 7 gapRoot`, together with the new ramified
linear-cubic-cubic factor grid. This does not yet construct a smaller Fermat
solution. RAMIFIED-002 proves both triples nonzero and pairwise coprime,
constructs `RamifiedCubicRoutingPacket`, and synchronizes the endpoint and
root-cubic gap depths. Lifted-branch provider construction, terminal
contradiction, and recursive descent closure remain unproved.
RAMIFIED-003 strengthens the depth equality to a division-free integer
identity and an explicit unit equivalence over every `ZMod (7^k)`. It does
not construct a smaller Fermat solution.
RAMIFIED-004 proves reduction coherence and classifies the seventh-power
branch modulo `49` by the six residues `1, 18, 19, 30, 31, 48`. The common
summit does not yet determine which branch occurs.
RAMIFIED-005 proves that the canonical branch is selected exactly by
`residualRoot = 1` in `ZMod 49`; otherwise the residual root is one of the six
nontrivial principal residues. Higher compatible seventh-root lifting remains
a separate obligation.
RAMIFIED-006 restores the terminal carrier forgotten by the common summit,
proves that `gapRoot` is a seven-unit, and fixes the three ramified depths at
`5, 6, 6`. It proves the exact integer equation `v*S = 7^5*A^7*Q`, its
pairwise-coprime factor ledger, and constructs the resulting 2 x 3 routing
board. The compensation core is now the explicit gcd `gcd(|v|,|Q|)`.
RAMIFIED-007 identifies every abstract routing cell with its canonical gcd
under the source-column pairwise-coprimality hypotheses. It then constructs
the canonical split
`A = X*Y`, `V = 7^5*X^7*C`, `S = Y^7*D`, `Q = C*D` and proves

```text
|R-L| = 7^6 * X^7 * (C*B).
```

The former receiver is equivalent both to this exact cubic-gap seventh-power
shape and to independent seventh powers for `C` and `B`. This is Outcome A.
RAMIFIED-008 confirms the corrected target: it does not make `gapRoot` a
seventh power. Conditional on the receiver, it extracts
`summit.root = innerRoot^7`, upgrades the coordinate to
`sevenAxis * innerRoot^49`, and proves the strict internal depth drop
`v7(|innerRoot.snd|) = 4`. The inner second coordinate and core split as
`7^4*M^7` and `N^7`; their two cubic factors are also signed integer seventh
powers. This completes the receiver branch of RAMIFIED-008 with Outcome A.
The receiver itself is not proved unconditionally, and no smaller Fermat
solution or recursive descent is claimed.
RAMIFIED-009 gives the two signed cubic forms their exact determinant-norm
interpretation in `SevenRealCubicInt`. It verifies the defining cubic
relation, norm multiplicativity, the two source norm formulas, common
polynomial discriminant `49`, and the ramified identities
`Norm(pi) = -7`, `pi^3 = 7*epsilon`, and `Norm(epsilon) = -1`, with an
explicit inverse for `epsilon`. After absorbing the sign in the depth-four
coordinate, the receiver packet now proves

```text
etaR - etaL = normalizedAxis^6 * normalizedWitness^7.
```

This is Outcome A at the advertised RAMIFIED-009 stop. The carrier has not
been identified with the full ring of integers. Principal ideals, class number
one, unit generators, local unit-class injection, and element-level
seventh-power extraction remain open.

RAMIFIED-010 takes the hidden Eisenstein coordinate
`theta = alpha - 3`. Lean verifies

```text
theta^3 + 7*theta^2 + 14*theta + 7 = 0
theta^3 = -7*(theta + 1)^2
IsUnit (theta + 1)
Associated pi theta.
```

The translated polynomial is irreducible and has discriminant `49`.
Its rational root defines a cubic number field, and the Eisenstein
prime-power argument proves that `Z[theta]` is already its full ring of
integers. The comparison is made concrete:

```text
SevenRealCubicInt ≃+* O_K
disc K = 49
nrComplexPlaces K = 0
Minkowski class bound = 14/9 < 2
IsPrincipalIdealRing O_K
classNumber K = 1.
```

The order-three rotation is transported to `O_K`, with
`sigma(alpha) = alpha^2 - 2*alpha`,
`sigma^2(alpha) = -alpha^2 + alpha + 2`, and `sigma^3 = id`.
This is RAMIFIED-010 Outcome A. Source-conjugate ideal coprimality belongs to
RAMIFIED-011; relative unit-class elimination belongs to RAMIFIED-011U; and
element-level seventh-power extraction and the depth drop remain later
obligations.

RAMIFIED-011A transports the principal-ideal property back to the concrete
coordinate ring and replaces the longer ideal-factorization route by direct
GCD extraction. For `x = a + b*alpha`, Lean proves:

```text
sigma(x) - x = theta*alpha*b
x*sigma(x)*sigma^2(x) = Norm(x).
```

If `IsCoprime a b` and `7 | b`, the three cyclic conjugates are pairwise
coprime. Consequently:

```text
Norm(x) = z^7
  -> exists unit root, x = unit*root^7.
```

Applying this to the two RAMIFIED-009 sources gives:

```text
etaL = uL*xiL^7
etaR = uR*xiR^7

uR*xiR^7 - uL*xiL^7 =
  normalizedAxis^6*normalizedWitness^7.
```

This is RAMIFIED-011A Outcome A. The units have not been shown to be seventh
powers. RAMIFIED-011U must still prove the proposed mod-`7` unit-class
criterion before exact source seventh powers or the RAMIFIED-012/013 depth
drop can be asserted.

RAMIFIED-011U and RAMIFIED-012 are now complete with Outcome A in
`SevenRealCubicUnitClass.lean`. In the translated `1, theta, theta^2` basis,
Lean fixes the three reduction coordinates modulo seven and their truncated
multiplication laws. For a global unit it defines

```text
Lambda(u) = (x, y - x^2/2) in F_7^2
```

and proves that this is additive under multiplication and kills seventh
powers. The two explicit units satisfy:

```text
Lambda(alpha)     = (5,5)
Lambda(1 + alpha) = (2,5)
det = 1.
```

On the global side, Dirichlet's theorem gives unit rank two, odd field degree
gives torsion units `±1`, and Mathlib's `ModN` cardinality theorem gives:

```text
Nat.card UnitClassModSeven = 49.
```

The descended logarithm is therefore bijective. Lean then proves the exact
criterion:

```text
unit is a seventh power <-> Lambda(unit) = 0.
```

For a primitive linear source `a + b*alpha` with `7 | b`, the source is a
nonzero scalar modulo the nilpotent direction. If it equals `u*root^7`, the
linear and quadratic theta coordinates force `Lambda(u)=0`. Applying this
separately to both RAMIFIED sources absorbs both units and constructs
`RamifiedRealCubicExactPowerPacket` with:

```text
etaL = leftRoot^7
etaR = rightRoot^7
rightRoot^7 - leftRoot^7 =
  normalizedAxis^6*normalizedWitness^7.
```

This is the advertised pure real-cubic second-case equation.

RAMIFIED-013 is complete with Outcome A in
`SevenRealCubicAxisDrop.lean`. The right side has exact theta depth `13`,
the homogeneous seventh quotient has exact depth `3`, and the root gap has
exact depth `10`. The explicit normalized cores are coprime, so PID
coprime-power extraction and the exponent identity between `3` and `7`
produce:

```text
Associated droppedAxis theta
XR - XL = droppedAxis^3 * descentWitness^7.
```

The dropped axis is prime and has exact theta depth one. The algebraic roots
also satisfy:

```text
Norm(XL) = signedLeftRoot
Norm(XR) = signedRightRoot.
```

This completes the ramified algebraic phase, but not the final FLT7
contradiction. The norm is nonlinear, so the independent signed integer
gap-depth routing is not automatically a corollary of the algebraic gap
factorization. The next phase must fuse the real-cubic axis drop back into
an actual primitive integer/quadratic counterexample and prove a strict
well-founded decrease before the recursive descent provider can be inhabited.

See [FLT7-RAMIFIED-013-REPORT.md](FLT7-RAMIFIED-013-REPORT.md) for the exact
Lean boundary and next-phase prediction.

FUSION-001A and FUSION-001B are complete. The symmetric RAMIFIED exit now splits
both the algebraic root gap and its seventh quotient as an axis cube times a
seventh power. Independently, `SevenRamifiedSignedRootDepth.lean` constructs
the exact signed integer shadow

```text
r-l = 7^4*d,  Phi_7(r,l) = 7*E,
d*E = a*(a+n)*m^7,  7 ∤ d*E.
```

The construction is attached coherently to the same balanced packet and never
identifies the norm of a difference with a difference of norms. The checked
coordinate first variation instead rewrites the theta-depth-ten root
perturbation as `7^3*theta*core` and proves that the resulting norm difference
is `7^4` times an explicit coefficient; that coefficient is exactly `d`.

FUSION-002 has now reduced seventh-root source-plane classification to the
explicit homogeneous equation `seventhSourcePlaneEquation a b c = 0`.
The unrestricted equation is no longer the active boundary. A division-free
triangular lift iterated three times constructs exact nonzero theta-linear
and theta-square cores at integer depths `3` and `6`.

The next FUSION-002 refinement is now checked in the integral theta basis.
Both nonconstant coordinates of a seventh power have explicit divided
coordinates and triangular factor identities. Their coefficient residues
match the predicted local model. The integer shadow also fixes
`quotientRoot ≡ 1` and `gapRoot ≡ a²*m (mod 7)`.

FUSION-002 is now packaged as a controlled paired theta-jet outcome. Neither
exact root is in the source plane. Their projective linear jets are `-tau`
and `tau`, their normalized quadratic jets are both `-3*tau^2`, and
`tau = m/a = gapRoot/a^3` in `ZMod 7`. The pair `(tau^3,tau^2)` is recorded
as a canonical six-sector address which reconstructs `tau`. No equality
between this address and the existing fixed routing cells is claimed yet.

See [FLT7-FUSION-001-B-REPORT.md](FLT7-FUSION-001-B-REPORT.md).
See [FLT7-FUSION-002-REPORT.md](FLT7-FUSION-002-REPORT.md).
See [FLT7-FUSION-002-EXACT-JET-REPORT.md](FLT7-FUSION-002-EXACT-JET-REPORT.md).

FUSION-003 pre-bridge is now complete at its controlled audit boundary.
`SevenRamifiedPairedThetaRootJet.lean` connects the paired jet to the
theta-depth-ten ledger and proves

```text
thetaResidue(gapCore) = -2*m.
```

`SevenRamifiedFusionSectorEquiv.lean` upgrades the finite address to the
explicit equivalence `(ZMod 7)ˣ ≃ μ₂ × μ₃`. The paired roots occupy opposite
binary rows and one common ternary column.

`SevenRamifiedFusionRoutingAudit.lean` retains Y/Z provenance before the
common summit, proves the signed routing third row is `(1,1,1)`, constructs
the six active unit cells and their two cycle ratios, and records the signed
margins lost by `natAbs`.

See [FLT7-FUSION-003-PREBRIDGE-REPORT.md](FLT7-FUSION-003-PREBRIDGE-REPORT.md).

FUSION-003 cyclic phase is also complete through its action-comparison
boundary. The active-board normal form compresses the two cycles to one
visible `mu3` phase while proving a separate hidden row gauge. On coherent
routing data Lean proves

```text
(kappa12/kappa23)^2 = tau^2.
```

The real-cubic rotation gives the depth-ten residual orbit
`-2*m, -m, 3*m`, and

```text
relativeRealIndex(k) = (k/tau)^2 = 1
  iff k = tau or k = -tau.
```

The next gate is an action-level naturality theorem identifying how rotation
of the signed roots transports the canonical routing shadow. Equality of
abstract three-element labels alone is not sufficient to inhabit the cyclic
alignment packet.

See [FLT7-FUSION-003-CYCLIC-REPORT.md](FLT7-FUSION-003-CYCLIC-REPORT.md).
