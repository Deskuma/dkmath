# FLT7-FUSION-004B Normal / Ultra execution roadmap

Date: 2026-07-30

Repository: `Deskuma/dkmath`  
Pull request: `#74`  
Base branch: `develop`  
Work branch: `wip/FLT7-fusion-004b-conjugate-fiber-260730`  
Starting merge checkpoint: `bac2a3b1f5881a4341138e7d47429c98ca9ca4b1`

## Current execution status

```text
EXECUTION_MODE = ULTRA
ACTIVE_PHASE   = U1
CURRENT_EVENT  = U1.4
STATUS         = COMPLETE
```

N1 was completed by the explicit componentwise route (Route N1-D). The public
theorem surface is:

```text
ratio_val_ne_inv
conjugatePrimeProduct_le_realPrimeFiberIdeal
realPrimeFiberIdeal_eq_conjugateProduct
conjugatePrimeFiberProductEqualityObligation_holds
```

The exact local fibre is now

```text
Ideal.map ofReal p = P * Pbar.
```

N2 is now also complete. The launchpad theorem surface is:

```text
PrimeSupport.cyclotomicAddress
PrimeSupport.map_kernelPower_eq_orientedPairPower
PrimeSupport.orientedPairPowers_pairwise_isCoprime
map_globalLoadFactorIdeal_eq_orientedFactorIdeal
globalDegreeSixOrientedFactorIdeal_eq_span_ofReal_load
degreeSixOrientedLoadFactorizationPacket
```

The mapped load ideal is an exact finite product of oriented/conjugate
prime-power pairs with the inherited support and `padicValNat` exponents.

The operator activated ULTRA / U1. Event U1.1 is complete. The real
order-three rotation now has an explicit order-three lift to the concrete
degree-six carrier, sending `zeta` to `zeta^2` and commuting with quadratic
conjugation. The resulting six phase-indexed primes have exact contractions
and exact fibre powers. For all three Galois-positioned loads, the finite
product is exactly the corresponding principal mapped load ideal, with the
original support, routing provenance, and `padicValNat` exponent unchanged.

Event U1.2 is complete.  The concrete degree-six carrier is now an integral
domain; the ramified prime above seven has exact multiplicity one in each
linear carrier; and every unramified prime on the full quotient-root support
has exactly the inherited `padicValNat` multiplicity in its selected
orientation.  Competing orientations are excluded.  The products of these
ramified and unramified powers are exactly the two carrier principal ideals.

Event U1.3 is complete.  The exact quotient-root exponent is split at every
full-support prime into the two routed-load exponents plus seven times the
residual-root exponent.  The routed products agree exactly with the existing
phase-zero load halves, and both carrier principal ideals are a ramified
loaded ideal times the seventh power of an explicit oriented residual ideal.
Quadratic conjugation exchanges the two decompositions.

Event U1.4 is complete.  The concrete carrier is a principal ideal ring,
proved without a full ring-of-integers identification.  Exact oriented and
conjugate element equations are constructed, with residual seventh roots and
loaded elements carrying their exact principal-ideal provenance.  The
associated unit is absorbed into the loaded element, and quadratic
conjugation is literal on both witnesses.

Event U1.5 is the active frontier.

## 1. Strategic decision

The remaining budget is not assigned uniformly.

The adopted execution strategy is:

```text
NORMAL checkpoint N1
  close the exact conjugate-prime fibre equality

NORMAL checkpoint N2
  build the smallest reliable launchpad for global oriented reconstruction

ULTRA expedition U1
  adaptively explore from global oriented prime data toward
  primitive additive reconstruction or an exact obstruction

NORMAL recovery checkpoints N3-N5
  stabilize, repair, expose, document, and land the Ultra results
```

The Ultra expedition must not be spent on the current single reverse-containment
lemma.  The local fibre equality is expected to be a finite-index, quotient,
CRT, or explicit quadratic-fibre calculation using already proved data.
Ultra is reserved for the point where the next mathematical structure is not
known in advance.

## 2. Fixed inherited boundary

PR #73 already established:

- unconditional loaded residual seventh powers in the real cubic PID;
- exact equality between routed-cell `q`-adic depth and selected real-prime
  multiplicity;
- finite-support global factorization of each principal real-cubic gcd-load
  ideal;
- the concrete rank-six quadratic carrier
  `SevenCyclotomicDegreeSixInt.Ring`;
- explicit conjugate seventh roots `zeta` and `zetaInv`;
- oriented and conjugate linear carriers;
- two distinct maximal comaximal degree-one kernels `P` and `Pbar`;
- their common real-cubic contraction `p`;
- their rational contraction `(q)`;
- residue quotient cardinality `q` for both kernels.

The inherited frontier at the start of N1 was:

```text
realPrimeFiberIdeal = Ideal.map ofReal p
realPrimeFiberIdeal <= P * Pbar
```

and its single missing local direction was:

```text
P * Pbar <= realPrimeFiberIdeal.
```

No stage may weaken this data, restart from the original Fermat equation, or
replace the concrete orientation by an unrelated abstract cyclotomic model.

## 3. Execution modes

### NORMAL mode

Use NORMAL mode for a bounded checkpoint with a known theorem surface.

NORMAL mode must:

1. work on one explicit mathematical obligation;
2. inspect existing DkMath and Mathlib APIs before creating local replacements;
3. preserve exact provenance, orientation, valuation, and contraction data;
4. commit a completed theorem packet or an explicit minimal obstruction;
5. write a short completion report with the exact proved and unproved boundary;
6. stop at the checkpoint boundary rather than silently entering a new algebraic
   world.

A NORMAL checkpoint may end with Outcome A, B, C, or D:

```text
A. target theorem proved directly
B. equivalent stronger reusable theorem proved
C. exact missing API or mathematical obligation isolated
D. proposed route formally excluded and the next sound route identified
```

### ULTRA mode

Use ULTRA mode only after the launch conditions in Section 6 are met.

ULTRA mode is an adaptive research expedition.  It may revise intermediate
plans when Lean-certified facts expose a stronger route, but it must preserve
all soundness boundaries.

ULTRA mode must:

1. continue without asking for routine tactical approval;
2. investigate the strongest sound continuation available from the current Lean
   facts;
3. never add the desired conclusion as a structure field, typeclass, axiom, or
   hidden hypothesis;
4. never claim the quadratic carrier is the full degree-six ring of integers
   unless that statement is actually proved;
5. never claim PID, class number one, element-level seventh-power extraction,
   primitive reconstruction, strict decrease, or FLT7 without the required
   theorem chain;
6. commit after every completed Event listed in Section 7;
7. attach an exact boundary report to every completed Event;
8. if interrupted by budget or tooling, leave the branch at the last building
   checkpoint with a handoff report for the next NORMAL recovery run.

Ultra is allowed to discover that the currently predicted route is impossible.
A formally proved obstruction plus the next exact frontier is a successful
research result.

## 4. NORMAL checkpoint N1 — exact conjugate-prime fibre

### Goal

Prove the reverse containment:

```text
a.evalKernel * a.conjugateEvalKernel <= a.realPrimeFiberIdeal
```

and therefore:

```text
a.realPrimeFiberIdeal =
  a.evalKernel * a.conjugateEvalKernel.
```

This must discharge:

```text
ConjugatePrimeFiberProductEqualityObligation
```

for every canonical `CyclotomicLinearPrimeAddress`.

### Preferred routes

Investigate these routes in order of mathematical economy:

1. **Explicit quadratic fibre**  
   Reduce the quadratic carrier modulo the common real prime and identify the
   resulting algebra with the split quadratic algebra over `ZMod q` whose two
   roots are the canonical ratio and its inverse.

2. **Combined evaluation kernel**  
   Construct the map to `ZMod q × ZMod q` given by the oriented and conjugate
   evaluations, identify its kernel with the extended real prime, and use the
   comaximal-kernel product theorem.

3. **Finite quotient cardinality / index**  
   Compare the two ideals using the proved inclusion and exact quotient
   cardinalities.  Equality is acceptable if obtained by a finite-cardinality
   theorem with all finiteness instances proved.

4. **Coordinate calculation**  
   Use the explicit real/im pair representation of the quadratic algebra to
   characterize membership in both sides componentwise.

Do not introduce full cyclotomic integer-ring machinery solely to close this
local equality unless the simpler routes are formally blocked and the block is
recorded.

### Stop condition

N1 ends immediately after:

- the exact equality is public through the `DkMath.FLT.Seven` facade;
- the relevant module build succeeds;
- a completion report records the proof route and exact scope;
- a checkpoint commit is created.

Do not begin global additive reconstruction in N1.

## 5. NORMAL checkpoint N2 — Ultra launchpad

N2 begins only after N1 is complete and reviewed.

### Goal

Expose the smallest global packet from which an adaptive Ultra expedition can
start without rediscovering local orientation.

The launchpad should connect:

```text
real-cubic global load ideal factorization
  -> exact extension of every real prime power
  -> oriented/conjugate prime-power pair in the degree-six carrier
  -> a finite global oriented factorization interface
```

### Expected theorem surface

Prefer a compact packet or theorem family containing:

- the finite prime support of an addressed load;
- the selected real-cubic kernel for every supported prime;
- the corresponding degree-six oriented and conjugate kernels;
- exact fibre equality for every supported prime;
- extension of each real-prime power to the product of the two conjugate powers;
- pairwise comaximality needed to multiply the local equalities globally;
- the mapped principal load ideal expressed as a finite product of oriented and
  conjugate prime powers.

A provisional packet name may be:

```text
DegreeSixOrientedLoadFactorizationPacket
```

The exact name may change if the existing API suggests a better boundary.

### Stop condition

N2 must stop once the global oriented factorization launchpad is either:

- implemented and exposed; or
- reduced to one exact missing theorem that genuinely requires adaptive
  exploration.

N2 must not spend the Ultra budget by informally continuing past this gate.

## 6. Ultra launch conditions

ULTRA mode may be activated only when all of the following are true:

```text
[1] exact conjugate-prime fibre equality is proved
[2] the real-cubic global load factorization remains available unchanged
[3] the degree-six oriented/conjugate prime addresses are public
[4] a global oriented factorization launch packet exists,
    or its exact single missing bridge is documented
[5] the branch builds at the latest checkpoint
[6] the current report states the precise starting theorem names
```

If N1 unexpectedly reveals that the fibre equality requires a new major number
field theory, stop and reassess before spending Ultra.  Do not automatically
promote a local API obstacle into the Ultra expedition.

## 7. ULTRA expedition U1 — adaptive reconstruction search

### Mission

Starting from the completed launchpad, explore the strongest sound route from
oriented degree-six prime data toward either:

```text
A. a primitive additive FLT7 reconstruction packet
B. an element-level oriented seventh-power packet sufficient for reconstruction
C. an exact new algebraic obstruction identifying the missing structure
D. a formally proved impossibility of the current reconstruction route
```

The expedition is not required to force Outcome A.  It is required to maximize
Lean-certified progress and preserve every discovered boundary.

### Event U1.1 — global oriented prime factorization

Target:

- exact finite factorization of the mapped real loads into oriented and
  conjugate prime powers;
- coherent indexing under real-cubic Galois rotation and quadratic conjugation;
- no loss of the original routing-cell provenance or `padicValNat` exponents.

Commit and report when complete.

### Event U1.2 — oriented carrier valuation ownership

Target:

- determine the exact multiplicity of every oriented prime in the oriented
  linear carrier and of every conjugate prime in its conjugate carrier;
- exclude competing orientations using the existing local evaluations;
- obtain the strongest global principal-ideal factorization of the two linear
  carriers.

Commit and report when complete.

### Event U1.3 — seventh-power residual extraction

Determine whether the global oriented factorization yields:

```text
(oriented carrier ideal)
  = explicit load ideal * seventh-power ideal
```

and similarly for the conjugate carrier.

Then determine the exact next requirement:

- ideal-level seventh-power extraction only;
- principal ideal extraction;
- full ring-of-integers identification;
- PID or class-number information;
- unit-class elimination;
- an explicit-coordinate substitute avoiding those theories.

Prove the strongest available result.  If a new requirement is unavoidable,
expose it as a named obligation rather than assuming it.

Commit and report when complete.

### Event U1.4 — element-level oriented power or exact obstruction

Attempt to construct element-level data of the form:

```text
orientedCarrier = unit * loadElement * root^7
conjugateCarrier = conjugateUnit * conjugateLoadElement * conjugateRoot^7
```

or the precise corrected form forced by the proved ideal factorization.

If unit classes or non-principality obstruct this step, formalize the exact
obstruction and determine whether it can be eliminated from the current
concrete carrier.

Commit and report when complete.

### Event U1.5 — primitive additive chart candidate

Only after U1.4 supplies sufficient element-level data, attempt to reconstruct
an additive chart.

Required properties include:

- an exact seventh-power additive identity;
- nonzero coordinates;
- positivity or a signed normalization that canonically yields positive natural
  coordinates;
- pairwise coprimality or a proved normalization to a primitive triple;
- explicit provenance from the original terminal packet.

Do not call a multiplicative factor packet an additive Fermat chart without the
actual additive equation.

Commit and report when complete.

### Event U1.6 — strict decrease candidate or exact failure boundary

If a primitive chart is obtained, search for a well-founded measure and prove a
strict drop.

Candidate measures may involve:

- the seven-primary pivot exponent;
- the absolute summit/root coordinate;
- the routed load product;
- an exact norm or height derived from the reconstructed packet;
- an existing DkMath descent measure.

If no strict decrease follows from the reconstructed data, isolate the exact
missing inequality or terminal contradiction as a named obligation.

Commit and report when complete.

## 8. NORMAL recovery checkpoints N3-N5

After Ultra stops, use NORMAL runs to convert the expedition into a stable
reviewable checkpoint.

Expected recovery work:

```text
N3
  repair elaboration failures
  remove accidental duplication
  stabilize theorem statements and imports

N4
  expose public facade theorems and packets
  add exact completion / boundary reports
  verify dependency direction and checkpoint structure

N5
  finish the smallest remaining bridge discovered by Ultra
  or split the next active frontier into a new PR
```

Do not spend recovery runs rewriting successful mathematical content merely for
style.  Preserve the strongest Lean-certified results first.

## 9. Build and commit discipline

For NORMAL mode:

- build the directly affected module during development;
- build `DkMath.FLT.Seven` before the checkpoint commit;
- one completed checkpoint per commit series;
- write the report in the same checkpoint.

For ULTRA mode:

- use focused module builds while exploring;
- run the facade build at every completed Event when practical;
- commit immediately after each Event that builds;
- never keep several mathematically complete Events only in an uncommitted work
  tree;
- if the full facade build is temporarily too expensive, commit only after the
  affected dependency cone builds and record the pending facade build explicitly.

Suggested commit prefixes:

```text
feat(FLT7): close exact conjugate-prime fibre
feat(FLT7): lift global loads to oriented degree-six primes
feat(FLT7): factor oriented cyclotomic carriers
feat(FLT7): extract oriented seventh-power residual
feat(FLT7): reconstruct primitive additive chart
feat(FLT7): prove strict FLT7 descent drop

docs(FLT7): report FUSION-004B checkpoint
```

## 10. Permanent soundness boundary

Until Lean proves the corresponding statements, this roadmap does not claim:

- that `SevenCyclotomicDegreeSixInt.Ring` is the full ring of integers of the
  seventh cyclotomic field;
- that it is a PID or has class number one;
- that every relevant ideal or unit is a seventh power;
- that the oriented carrier has an element-level seventh-power decomposition;
- that a new primitive FLT7 counterexample exists;
- that any reconstructed object is strictly smaller;
- recursive descent closure;
- terminal contradiction;
- FLT7.

The roadmap is successful if it either constructs these bridges or replaces an
incorrect predicted bridge by a sharper Lean-certified obstruction and a new
exact frontier.
