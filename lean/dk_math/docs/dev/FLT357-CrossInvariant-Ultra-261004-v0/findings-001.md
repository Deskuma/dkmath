# FLT3/5/7 Cross-Invariant Ultra — Findings 001

Branch: **research/FLT357-CrossInvariant-Ultra-261004-v0**

Base: FLT7 Ultra PR #111 head
`3c1930be8a911591f364d2adcbc62b4165e1948d`.

This file is the durable incremental result of a bounded pre-audit.  Update it
during research; do not reserve discoveries for a final report.

## Current status

- Requested branch verified at initial HEAD `69d44fa3e`; initial tree clean.
- Lean/Mathlib `v4.34.1`. Initial source inventory complete; no production edits.
- All three current source maps are stable. **Outcome B at the extracted
  algebraic obstruction layer** is supported by a checked root-choice
  independence lemma. Outcome A for a literal whole-FLT proof is not established.
- Starting observation from p=7:
  `(A)=P7*J^7`, `A=lambda*u*beta^7`;
  the unit/additive-descent layers remain open.
- Goal: project that layer decomposition backward onto the completed p=3 and
  p=5 proofs without forcing false carrier equivalences.

## Cross-exponent matrix

| Layer | p=3 | p=5 | p=7 |
| --- | --- | --- | --- |
| production carrier | `EisensteinInt := TraceOneInt (-1)`, linear cubic norm | real quadratic `GoldenInt`, square-linked quartic GN norm | degree-six cyclotomic QA over a real-cubic root-orbit source |
| ramified correction | alpha=(1+tau)*beta, ramifier norm3 | alpha=(2+phi)*beta, ramifier norm5 | A=lambda*B; exact P7 exponent1 |
| normalized ideal p-th power | stronger direct beta=epsilon*gamma³ from Euclidean GCD; no stored ideal stage | stronger direct beta=epsilon*gamma⁵ from Euclidean GCD; no stored ideal stage | full six-phase pairwise ideal product; every normalized ideal seventh power, then PID |
| unit / phase class | complete {1,tau,tau²} cube representatives; two excluded by actual coordinates | complete phi^i, i:Fin5 fifth-power representatives; nonzero sectors excluded | new full degree-six u retained; real-cubic projective log does not alone remove it |
| additive landing | `gamma_coordinate_product_eq_A_cube`, then signed cube factors and positive primitive Fermat successor | exact snd / quartic H relation, square-source inversion, Golden lift T(r,s) | original source.hEq retained; no new integer successor for beta |
| strict descent / contradiction | `exists_smaller_primitiveCubicPack`: positive primitive successor, product a*b*c decreases | `GoldenZeroSectorDescentPacket.strictDescent`: Golden packet re-entry, abs(snd) decreases | smaller twisted real-cubic norm exists; no positive recursive Fermat packet |
| first unresolved obstruction | none for positive-natural exponent3 endpoint | none for positive-natural exponent5 endpoint | new normalized unit class/phase gauge, then additive successor landing |

Detailed source maps: [p=3](flt3-audit-001.md), [p=5](flt5-audit-001.md),
[p=7](flt7-audit-001.md), and [generic layer](generic-state-audit-001.md).

## Candidate invariant / common schema

Fix the actual integrally closed domain R, exponent p, nonzero source element
A, and nonzero ramifier representative lambda (including its unit coefficient).
The selected production stages have:

```text
A = lambda * u * beta^p,    u a unit.
[u] in R-units / (R-units)^p.
```

`checks/UnitPowerClassAudit.lean` proves that two such expressions with the
same A and lambda satisfy u=v*t^p for a unit t. This is an actual root-choice
invariant, not just a ledger of proof stages. The test also checks normality
and exponent3/5/7 specializations on the actual three production orders.

The ramified valuation modulo p is a further obstruction once a prime
direction is fixed; current p7 checks it is 1. The raw ideal consequently
cannot be a seventh power. For p3/p5 the direct element extraction collapses
the explicit ideal layer, but not the coordinate-specific unit exclusions.

No common additive/descent transition theorem is proved. p3 regenerates a
Fermat triple; p5 regenerates a Golden packet; p7 has not closed successor
landing. The first arithmetic split is already carrier/source generation.

## Evidence that may indicate stripe / sector behavior

Confirmed concrete data:

- p mod4 selects the signature/unit behavior of the **signed quadratic** order;
  it does not classify all full cyclotomic carriers.
- p3 and p5 generic type/ring adapters are present, so their historical
  presentation gaps are resolved. Actual unit/coordinate arithmetic remains.
- Generic quadratic sector systems certify coverage, not unique sector labels.
- Actual p7 has a mandatory full-degree-six ramified load1; its real-cubic
  unit log has two ZMod7 coordinates, separately from the new degree-six unit.
- Exact normalization checks: discrAxis(-1)=tau*(1+tau), and the p5 ramifier
  maps to phi*discrAxis(1). Changing that normalization shifts residual [u].

The moire analogy can describe these discrete data, but no common periodic
sampling law or dynamical state machine is established by this audit.

## Failed / blocked unifications

- Equal norms do not identify Eisenstein, Golden, quadratic Gauss, full
  cyclotomic, or root-orbit elements.
- Generic TraceOne(-2) sign units do not eliminate a full degree-six p7 unit.
- The original chosen cyclotomic quotient's unit theorem does not transfer
  to the new root-orbit quotient without an actual source/element bridge.
- Exact sector zero is normalization-dependent: the same alpha stripped by
  the generic axis has an additional tau-inverse (p3) or phi (p5) unit twist.
- A whole-proof abstraction with a field assuming additive landing or descent
  would hide the mathematical split rather than settle Outcome A.

## p=11 / p=13 forecast

The forecast was made after all three source maps stabilized. See G6 in
`generic-state-audit-001.md` for the exact declarations.

- Arbitrary primitive counterexample: the existing generic away branch or
  missing uniform ramified orientation is the first blocker for both primes.
- Supplied ramified quadratic packet: at 11 the signed parameter is -3 and
  generic units are signs; at 13 it is 3 and generic Fin13 sector coverage
  exists. The first missing arithmetic discharge is the respective explicit
  class-group p-torsion condition (or class-number coprimality).
- Beyond that discharge, 11 needs specialized coordinate landing/descent;
  13 additionally needs source-specific sector exclusions.
- Full cyclotomic carrier: generic ramification/norm APIs predict a mandatory
  exponent1 factor associated to 1-zeta at both primes. Actual complete
  nonramified exponent divisibility/corrected ideal power is the first new
  full-carrier implementation obligation; no FLT11/13 proof was attempted.

## Next action

- Review the completed report/probes, check all artifact links and whitespace,
  then commit the completed bounded audit under the user's explicit permission.

## Checkpoint history

### 2026-10-04 checkpoint 00 — workspace seed

- New branch created from the FLT7 Ultra PR #111 head so the p=7 ramified
  correction is available to the cross-exponent audit.
- This run is intentionally bounded by the current usage window.
- Durable findings take priority over implementation and full builds.

### 2026-10-04 checkpoint 01 — Initial live inventory

- Verified requested branch and clean initial tree. Baseline `69d44fa3e`.
- Current p=7 source endpoints found in `CurrentCarrierNormalizedPower` and
  `CurrentSupportObstruction`: corrected `(A)=P7*J^7`, `A=lambda*u*beta^7`,
  raw ramified exponent1 and all other exponents seventh-multiple.
- Current `DkMath.FLT.Prime` facade is explicitly bounded: ramified packets,
  away simultaneous powers, conditional quadratic TraceOne extraction,
  class-group/unit/sector interfaces. It is not the full degree-six p=7 closure.
- Initial source mapping from parallel audits: p=3 and p=5 both use direct
  element GCD/UFD power extraction in norm-Euclidean quadratic orders, rather
  than exposing a normalized ideal-power packet. Do not infer that a missing
  ideal declaration is missing mathematical power extraction.
- p=3 descent returns a positive primitive cubic packet and decreases a*b*c.
  p=5 descent instead reconstructs a Golden zero-sector packet and decreases
  |second coordinate|. They are completed through different invariant states.
- Candidate common algebraic stage: chosen-order ramifier correction plus
  unit class modulo p-th powers and exact integral coefficient constraints.
  This is a candidate observation, not a new theorem with encoded conclusions.
- Next: complete each source map, then record candidate state coordinates and
  run small centralized axiom/provenance probes after a dedicated checkpoint.
  No full build or production refactor is planned.

### 2026-10-04 checkpoint 02 — FLT3 mapping stable

- Source endpoint `fermatThree_no_positive_solution` is completed through
  `primitiveCubicPack_false` and `exists_smaller_primitiveCubicPack`; natural
  strong induction measure a*b*c. Arbitrary positive inputs get gcd normalization.
- Ramifier-strip followed by element cube extraction precedes unit sectors.
  `gamma_coordinate_product_eq_A_cube` is an exact coordinate identity, not
  a scalar norm landing. Positive/primitivity reconstruction is explicit.
- Generic p3 carrier gap recorded in historical summary is now resolved:
  actual EisensteinInt is definitionally TraceOneInt(-1), with a checked
  omega/tau sign-convention bridge. Importing a GN lift API is not proof use.
- Detailed durable map saved `flt3-audit-001.md`. Compiled endpoint dependency
  audit is still to run; a source scan alone is not final provenance evidence.

### 2026-10-04 checkpoint 03 — FLT5 mapping stable

- `Five.flt5Target` is supplied with proved Golden unit classification and
  proved Golden zero-sector arithmetic exclusion, not an open provider.
- `GN5_eq_goldenNorm_squareLink` generates the real quadratic carrier from
  endpoint squares and preserves discriminant-square provenance. Actual
  ramifier is goldenTau=2+phi; beta=unit*gamma⁵ from Euclidean GCD/UFD.
- Five representative coverage is proved, not representative uniqueness or
  quotient cardinality. Actual snd equations exclude nonzero representatives.
- Descent reconstructs `GoldenZeroSectorDescentPacket`, not a smaller Fermat
  triple: T(r,s)=(r²+rs+s²,s²) re-entry and strict |snd| decrease.
- `goldenTraceOneRingEquiv` resolves the carrier presentation adapter, but does
  not populate the generic supplied packets or their specialized arithmetic.
- Detailed durable map saved `flt5-audit-001.md`; central axiom probe pending.

### 2026-10-04 checkpoint 04 — FLT7 mapping and shared-core candidate stable

- Detailed live p7 map saved `flt7-audit-001.md`. Current A is a later root-orbit
  carrier with real-cubic rho, not the original rational-endpoint factor.
- `(A)=P7*J⁷`, A=lambda*u*beta⁷, exact load1 and all nonramified exponent7
  divisibility remain verified source endpoints. New u still lacks the chosen
  source-specific unit/coordinate compatibility needed for descent.
- First genuine arithmetic split is carrier generation: linear Eisenstein
  cubic norm vs square-linked Golden quartic norm vs degree-six current
  root-orbit carrier. Matching norms never resolves this split.
- Candidate Outcome B, restricted to the extracted algebraic obstruction:
  actual order R / source map, chosen nonzero ramifier, load modp, and class
  [u] in R-units modulo pth powers. This should be independent of extracted
  root choice; unlike a stage checklist, that is a testable invariant.
- Existing Mathlib `Associated.pow_iff` in an integrally closed domain can
  establish root association and unitclass independence. A small test-only
  probe is now planned, after this saved pre-build checkpoint.
- A literal common whole-FLT/descent theorem is not established: the actual
  coordinate polynomial and closed well-founded states differ at p3/p5, and
  p7 landing remains open. No generic structure encoding the conclusion added.
- Initial source checkpoint committed as `fb8ebd3d6` with current explicit
  user commit permission (including necessary metadata-write escalation).

### 2026-10-04 checkpoint 05 — Before centralized focused probes

- Planned checks: axiom audits for completed p3/p5 endpoints and key extraction,
  sectors/strictdescent; current p7 corrected receiver; real vs imaginary
  generic sector endpoints; exact carrier adapters.
- Planned compiled constant-dependency traversal for p3/p5 endpoints to ensure
  no `sorryAx` or completed Mathlib FLT theorem supplies closure. Imported
  artifacts alone are not counted as proof references.
- Planned tiny unit ambiguity lemma using integrally closed root-association:
  if a=u*b^n=v*c^n, a nonzero, units u/v, n>0, then u=v*t^n for a unit t.
  It does not assume the desired FLT conclusion or furnish new power roots.
- All probes stay under docs/checks or /tmp; no production/facade edits or full build.
- Next: run those focused probes, accept/reject the shared invariant with actual
  evidence, then finalize p11/p13 forecast and the bounded report.

### 2026-10-04 checkpoint 06 — Shared invariant and normalization checked

- `lake env lean .../checks/UnitPowerClassAudit.lean` passed (exit0).
  Root-choice independence and fixed-ramifier variant were kernel-checked;
  concrete normal-domain instances and p=3/5/7 specializations passed.
  Named lemmas use only propext, Classical.choice, Quot.sound.
- `lake env lean .../checks/EndpointAudit.lean` passed (exit0).
  Completed p3/p5, key extraction/sectors/descent, current p7 corrected
  receiver, real-cubic unit log and generic conditional sectors show only
  the standard axioms. Exact p3/p5 ramifier normalization identities passed.
- Initial diagnostic normalization attempt had a wrong namespace and used
  order tactics on a ring without order; repaired locally by exact coordinate
  equality and kernel `decide`. Final checked artifact has no holes.
- Assessment is now limited Outcome B: the residual unit class is an actual
  invariant for a fixed order/source/ramifier, not a uniform FLT closure.
- Essential state includes source provenance, actual order, chosen ramifier,
  local load and residual unit class; normalized ideal-root class matters before
  principalization. Global p-torsion freeness is a sufficient discharge,
  not an independent necessary coordinate for an already-principal root.
- Normalization warning is concrete: p3 generic stripping differs by tau^-1,
  p5 by phi for the same element. Type/ring equivalence alone does not preserve
  the specialized proof's zero sector under a changed ramifier.
- Generic 11/13 forecast is now saved after stable 3/5/7 maps. Continuous
  findings and all detailed maps remain the durable state; no production edits.

### 2026-10-04 checkpoint 07 — Provenance complete; report saved

- Compiled dependency audit passed for four named roots, including kernel
  types, definition/theorem/opaque bodies and all inductive constructors.
  Final reachable/readable counts: p3 15283/14092; p5 17552/16272; current p7
  element and ideal receivers both 74075/71420. Every forbidden, missing or
  unreadable list is empty; all axiom leaves are the standard three.
- Thus current p7 corrected receivers do not depend on the imported historical
  sorryAx, and current p3/p5 endpoints do not use the explicitly enumerated
  completed Mathlib FLT3/FLT4 proof families. This is not an import-graph claim.
- Source dependency diagnostic needed one Nat annotation on its first attempt;
  after the first successful check, constructor traversal was added on review.
  Final saved log and counts refer to the strengthened check.
- Saved `report-001.md` and `logs/validation-summary.md`; README links artifacts.
  Limited Outcome B and normalization-specific invariant are now explicit.
- No production source or facade diff. Next action is final artifact validation
  and a scoped audit commit, not a new FLT implementation.
