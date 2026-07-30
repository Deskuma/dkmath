# FLT7-012 — Cubic core split, prime-routing grid, and closure audit

Work on branch:

```text
feature/FLT7-magic-core-260722-v0
```

Use the current branch HEAD after completed FLT7-011.

## Objective

Expose the hidden integral factorization of the away second-coordinate core,
prove the resulting root-side factors are pairwise coprime, and compare the two
coprime triple products

```text
y * z * (y+z)
  = 7 * |v| * |P(u,v)| * |Q(u,v)|.
```

The goal is to determine whether FLT7-011 closes recursively.

Do not assume that equality of two products of pairwise-coprime triples forces
a permutation of the factors. In general, prime support may route through a
non-diagonal `3 × 3` grid. This checkpoint must formalize that routing and state
the exact additional provider required for a genuine descent.

A recursive descent may be declared only if an explicit new
`CounterexamplePack` is constructed and its selected carrier depth is proved
strictly smaller. Otherwise report the closure obstruction exactly.

## New modules

Create:

```text
DkMath/FLT/Seven/CubicSecondCoordinateSplit.lean
DkMath/FLT/Seven/CoprimeTripleRouting.lean
DkMath/FLT/Seven/DescentClosureAudit.lean
```

Update:

```text
DkMath/FLT/Seven.lean
```

Add focused tests:

```text
DkMathTest/FLT/SevenCubicSecondCoordinateSplit.lean
DkMathTest/FLT/SevenDescentClosureAudit.lean
```

Create:

```text
docs/feature/FLT7-magic-core-260722/report-flt7-012.md
```

Suggested imports:

```lean
-- CubicSecondCoordinateSplit.lean
import DkMath.FLT.Seven.AwayValuationTransfer

-- CoprimeTripleRouting.lean
import DkMath.FLT.Seven.CubicSecondCoordinateSplit

-- DescentClosureAudit.lean
import DkMath.FLT.Seven.CoprimeTripleRouting
```

Use namespace:

```lean
namespace DkMath.FLT.Seven
```

# Part A — Hidden cubic factorization

Define:

```lean
def seventhPowerSndLeftCubic (u v : ℤ) : ℤ :=
  u ^ 3 - 2 * u ^ 2 * v - u * v ^ 2 + v ^ 3
```

```lean
def seventhPowerSndRightCubic (u v : ℤ) : ℤ :=
  u ^ 3 + 5 * u ^ 2 * v + 6 * u * v ^ 2 + v ^ 3
```

Prove the exact factorization:

```lean
theorem seventhPowerSndCore_factor
    (u v : ℤ) :
    seventhPowerSndCore u v =
      seventhPowerSndLeftCubic u v *
      seventhPowerSndRightCubic u v
```

Prove the two structural identities:

```lean
theorem seventhPowerSnd_cubic_sub
    (u v : ℤ) :
    seventhPowerSndRightCubic u v -
      seventhPowerSndLeftCubic u v =
      7 * u * v * (u+v)
```

```lean
theorem seventhPowerSnd_cubic_add
    (u v : ℤ) :
    seventhPowerSndLeftCubic u v +
      seventhPowerSndRightCubic u v =
      (2*u+v) * norm (⟨u,v⟩ : TraceOneInt (-2))
```

Then refine the FLT7-011 load identity:

```lean
theorem away_endpoint_product_cubic_load_eq
    {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) :
    y * z * (y+z) =
      7 * Int.natAbs p.root.snd *
        Int.natAbs
          (seventhPowerSndLeftCubic p.root.fst p.root.snd) *
        Int.natAbs
          (seventhPowerSndRightCubic p.root.fst p.root.snd)
```

Use only the existing absolute-value load theorem and
`Int.natAbs_mul`.

# Part B — Primitive root coordinates

Prove that the seventh-power root coordinates are coprime as integers.

Required theorem:

```lean
theorem AwayCoordinateNormalForm.root_coordinates_isCoprime
    {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) :
    IsCoprime p.root.fst p.root.snd
```

Recommended proof:

1. a common integer divisor `d` of `root.fst` and `root.snd` divides the root
   as an embedded integer scalar;
2. therefore `d^7` divides both coordinates of `root^7`;
3. use `p.coordinate_eq` and the primitive cubic coordinate Bézout certificate
   from FLT7-009;
4. conclude `d` is a unit in `ℤ`.

An equivalent direct Bézout proof is acceptable. Expose a natural absolute
version if useful:

```lean
Nat.Coprime (Int.natAbs p.root.fst) (Int.natAbs p.root.snd)
```

Also prove the inherited norm condition:

```lean
¬ (7 : ℤ) ∣ norm p.root
```

by reusing FLT7-011, not by reproving it.

# Part C — Pairwise coprimality of root-side factors

Let

```text
V = |v|,
P = |LeftCubic(u,v)|,
Q = |RightCubic(u,v)|.
```

Prove all factors are positive/nonzero for an away packet:

```lean
0 < V
0 < P
0 < Q
```

`V>0` already exists in FLT7-011. For `P,Q`, use the nonzero product core and
the cubic factorization.

Prove:

```lean
theorem AwayCoordinateNormalForm.coprime_rootSnd_leftCubic ... :
  Nat.Coprime V P
```

```lean
theorem AwayCoordinateNormalForm.coprime_rootSnd_rightCubic ... :
  Nat.Coprime V Q
```

Reduce each cubic modulo `v`:

```text
P(u,v) ≡ u^3 mod v,
Q(u,v) ≡ u^3 mod v,
```

and use coprimality of `u,v`.

Prove:

```lean
theorem AwayCoordinateNormalForm.coprime_leftCubic_rightCubic ... :
  Nat.Coprime P Q
```

Recommended prime-divisor proof:

1. let a prime `q` divide both cubics;
2. from their difference obtain

```text
q ∣ 7*u*v*(u+v);
```

3. exclude `q∣u`, `q∣v`, and `q∣u+v` using root-coordinate coprimality and the
   cubic formulas;
4. conclude `q=7`;
5. if `7` divides both cubics, their sum and norm nondivisibility force
   `7∣2u+v`;
6. show `7∣2u+v` implies `7∣norm(u,v)` because

```text
norm(u,v) ≡ 0 mod 7 when v ≡ -2u;
```

contradiction.

Package the pairwise-coprime root triple:

```lean
structure AwayRootCoprimeTriple (x y z : ℕ) : Type where
  normal : AwayCoordinateNormalForm x y z
  vPart : ℕ
  leftPart : ℕ
  rightPart : ℕ
  vPart_eq : vPart = Int.natAbs normal.root.snd
  leftPart_eq : leftPart = Int.natAbs (...LeftCubic...)
  rightPart_eq : rightPart = Int.natAbs (...RightCubic...)
  vPart_pos : 0 < vPart
  leftPart_pos : 0 < leftPart
  rightPart_pos : 0 < rightPart
  coprime_v_left : Nat.Coprime vPart leftPart
  coprime_v_right : Nat.Coprime vPart rightPart
  coprime_left_right : Nat.Coprime leftPart rightPart
```

A definitionally simpler packet is acceptable.

# Part D — Endpoint triple and distinguished `7`

Package the endpoint side:

```lean
structure AwayEndpointCoprimeTriple (x y z : ℕ) : Type where
  normal : AwayCoordinateNormalForm x y z
  first : ℕ := y
  second : ℕ := z
  third : ℕ := y+z
  first_pos : 0 < y
  second_pos : 0 < z
  third_pos : 0 < y+z
  coprime_first_second : Nat.Coprime y z
  coprime_first_third : Nat.Coprime y (y+z)
  coprime_second_third : Nat.Coprime z (y+z)
```

Use primitive endpoint coprimality. Do not reprove it through residue sectors.

Combine the two packets and the selected carrier:

```lean
structure AwayCubicProductPacket (x y z : ℕ) : Type where
  transfer : AwayValuationTransferPacket x y z
  endpointTriple : AwayEndpointCoprimeTriple x y z
  rootTriple : AwayRootCoprimeTriple x y z
  product_eq :
    y * z * (y+z) =
      7 * rootTriple.vPart * rootTriple.leftPart * rootTriple.rightPart
```

Prove construction from every `AwayCoordinateNormalForm`.

Record explicitly that the leading factor `7` belongs entirely to the selected
endpoint carrier by FLT7-011. Do not fold the `7` into one of the root triple
factors definitionally.

# Part E — Generic coprime triple routing grid

Formalize the arithmetic fact that equality of two products of pairwise-coprime
triples creates a routing grid, not necessarily a permutation.

A recommended concrete structure is:

```lean
structure CoprimeTripleRouting
    (a₁ a₂ a₃ b₁ b₂ b₃ : ℕ) : Type where
  c11 c12 c13 : ℕ
  c21 c22 c23 : ℕ
  c31 c32 c33 : ℕ
  row1 : a₁ = c11*c12*c13
  row2 : a₂ = c21*c22*c23
  row3 : a₃ = c31*c32*c33
  col1 : b₁ = c11*c21*c31
  col2 : b₂ = c12*c22*c32
  col3 : b₃ = c13*c23*c33
```

Add the coprimality properties required to certify disjoint prime support
between distinct cells in the same row and column. It is acceptable to define
cells canonically by iterated gcds instead of storing arbitrary witnesses.

Prove an existence theorem for positive pairwise-coprime triples with equal
products:

```lean
theorem nonempty_coprimeTripleRouting
    {a₁ a₂ a₃ b₁ b₂ b₃ : ℕ}
    (ha_pos : 0 < a₁ ∧ 0 < a₂ ∧ 0 < a₃)
    (hb_pos : 0 < b₁ ∧ 0 < b₂ ∧ 0 < b₃)
    (ha12 : Nat.Coprime a₁ a₂)
    (ha13 : Nat.Coprime a₁ a₃)
    (ha23 : Nat.Coprime a₂ a₃)
    (hb12 : Nat.Coprime b₁ b₂)
    (hb13 : Nat.Coprime b₁ b₃)
    (hb23 : Nat.Coprime b₂ b₃)
    (hprod : a₁*a₂*a₃ = b₁*b₂*b₃) :
    Nonempty (CoprimeTripleRouting a₁ a₂ a₃ b₁ b₂ b₃)
```

Possible construction:

```text
cij = gcd(ai,bj)
```

followed by repeated coprime product cancellation. Use Mathlib gcd APIs; do not
formalize prime multisets unless necessary.

If the full generic theorem becomes disproportionately large, specialize it to
the exact endpoint/root product used here, but retain the explicit nine-cell
routing data.

# Part F — FLT7 routing packet

On the root side use the three factors

```text
7*vPart,
leftPart,
rightPart
```

or, preferably, keep `7` distinguished and route the selected endpoint carrier
against

```text
7*vPart
```

while the other endpoint primes route among all three root factors.

Define:

```lean
structure AwayCubicRoutingPacket (x y z : ℕ) : Type where
  cubic : AwayCubicProductPacket x y z
  routing : CoprimeTripleRouting
    y z (y+z)
    (7*cubic.rootTriple.vPart)
    cubic.rootTriple.leftPart
    cubic.rootTriple.rightPart
```

Prove:

```lean
theorem nonempty_awayCubicRoutingPacket
    {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) :
    Nonempty (AwayCubicRoutingPacket x y z)
```

Expose a chosen packet if useful.

# Part G — Closure provider and audit result

Define explicitly what is still required to turn the strict depth drop into a
recursive FLT7 descent.

One acceptable interface is:

```lean
structure AwayDescentClosureProvider
    (x y z : ℕ)
    (p : AwayValuationTransferPacket x y z) : Type where
  nextX : ℕ
  nextY : ℕ
  nextZ : ℕ
  nextPack : CounterexamplePack nextX nextY nextZ
  nextRoute : AwayValuationTransferPacket nextX nextY nextZ
  carrier_match : nextRoute.carrier = Int.natAbs p.normal.root.snd
```

The exact provider may instead reconstruct a `CoordinateCounterexampleRoute`
or another sufficient packet, but it must end in a new primitive FLT7
counterexample with selected carrier exactly equal to the old root second
coordinate absolute value.

Prove the conditional descent theorem:

```lean
theorem away_depth_descent_of_closureProvider
    {x y z : ℕ}
    (p : AwayValuationTransferPacket x y z)
    (c : AwayDescentClosureProvider x y z p) :
    padicValNat 7 c.nextRoute.carrier <
      padicValNat 7 p.carrier
```

This follows from `carrier_match` and FLT7-011.

Now provide an honest audit result. Prefer an inductive result type:

```lean
inductive AwayClosureAuditResult
    (x y z : ℕ)
    (p : AwayValuationTransferPacket x y z) : Type
  | closed (provider : AwayDescentClosureProvider x y z p)
  | open
      (routing : AwayCubicRoutingPacket x y z)
      (missing : MissingClosureProviderStatement x y z p routing)
```

`MissingClosureProviderStatement` should state mathematically—not as prose—the
unproved reconstruction obligation. A useful formulation is that the current
factor/routing equations do not yet supply naturals `nextX,nextY,nextZ` with
both a Fermat equation and the required carrier match.

Do not try to prove a universal negation asserting that no closure provider can
exist. The `open` result means only that it is not derivable from the APIs
completed in this checkpoint.

The checkpoint summit should be one of:

### Outcome A — closure found

```lean
theorem awayDescentClosureProvider_of_packet
    (p : AwayValuationTransferPacket x y z) :
    Nonempty (AwayDescentClosureProvider x y z p)
```

and hence a genuine strict recursive step.

### Outcome B — routing exposed, closure remains open

Provide:

```lean
AwayCubicRoutingPacket
AwayDescentClosureProvider
away_depth_descent_of_closureProvider
```

and an exact theorem/structure describing the missing reconstruction
obligation. This is a successful and expected audit outcome.

# Part H — Full route audit

Retain the ramified branch explicitly:

```lean
inductive ClosureAuditCounterexampleRoute (x y z : ℕ) : Type
  | ramified (packet : RamifiedCoordinateNormalForm x y z)
  | awayClosed (packet : AwayValuationTransferPacket x y z)
      (provider : AwayDescentClosureProvider x y z packet)
  | awayOpen (packet : AwayCubicRoutingPacket x y z)
```

Prove a route theorem from every `CounterexamplePack`. In the away branch,
choose `awayClosed` only if a provider has actually been constructed; otherwise
use `awayOpen`.

Do not fabricate decidability of provider existence. If no provider theorem is
proved, define and use the open route directly.

# Tests

Focused tests must cover:

- cubic factorization of `SndCore`;
- cubic sum and difference identities;
- root-coordinate coprimality;
- all three pairwise coprimality theorems for `|v|,|P|,|Q|`;
- endpoint triple coprimality;
- exact four-factor product identity;
- construction and row/column equations of a routing grid on abstract coprime
  triples;
- construction of the FLT7 routing packet;
- conditional strict descent from a mock closure provider;
- the full closure-audit route.

Do not instantiate an actual counterexample.
Avoid `native_decide`.

# Required report

Record:

- exact definition/theorem/structure surface;
- hidden cubic factorization;
- cubic sum and difference identities;
- proof that the root coordinates are primitive;
- pairwise coprimality of `|v|,|P|,|Q|`;
- endpoint/root coprime triple products;
- explicit `3 × 3` prime-routing grid;
- why pairwise-coprime product equality does not by itself force a permutation;
- closure-provider interface;
- conditional strict descent theorem;
- whether closure was actually constructed;
- exact remaining reconstruction obligation if closure stays open;
- recommended FLT7-013 boundary.

If Outcome B occurs, the FLT7-013 recommendation should attack the routing
grid with the first-coordinate equation and the four mod-seven sectors. The
next target is to eliminate off-diagonal routing cells or derive the missing
new Fermat packet. Do not repeat the valuation work.

# Non-goals

Do not add:

- an unconditional recursive descent without a constructed target packet;
- an FLT7 contradiction or no-solution theorem;
- a claim that pairwise-coprime triples must match by permutation;
- a universal theorem that no closure provider exists;
- ideal or class-number theory;
- general exponent or general-prime routing theory;
- changes to FLT3 or FLT5.

# Outcome classification

- Outcome A: the cubic routing closes into an explicit new primitive FLT7
  packet, producing a genuine strict recursive descent step.
- Outcome B: cubic split, pairwise coprimality, routing grid, and conditional
  descent are complete, but reconstruction remains an explicit open provider.
- Outcome C: one of the proposed cubic identities or coprimality claims is
  false; report the exact counterexample and preserve FLT7-011.

Commit with a focused message and push to the current feature branch.
