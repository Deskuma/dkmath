# FLT7TC-005R46 — Saturation audit and closure-route selection

## Scope

R46 is a reconnaissance checkpoint.  It audits the exact finite-Hensel
budget reached by R45, freezes the old successor branches, and checks whether
the remaining C=1 and C>1 surfaces have a supported closure route.  No new
production contradiction theorem is introduced at this stage.

The R45 endpoint being audited is the checked wrapper
`directOrbitPairedDeepJet_current_depth9_wrapper`: it retains the paired
quotient identity, gives `ThetaNilpotentDepth 8` for the inverse unit, and
returns `W = rho * t^(7^9)`.

## Initial checked inventory

- The trace-plane functional is
  `Phi(W) = 3*A - 10*B + 35*C` for theta coordinates `(A,B,C)`.
- The checked calibration is `rho = -alphaUnit^3`, with theta coordinates
  `(-20,-13,-2)`, norm `1`, projective log `(1,1)`, and zero trace-plane
  functional.
- The current unit-class API proves rank two and the mod-seven class
  bijection, but no theorem in the checked surface identifies `alphaUnit` and
  `alphaAddOneUnit` as a fundamental integral-unit basis.
- R45 starts from finite theta-depth 32 only; no arbitrary-depth continuation
  is available.

The following sections are filled as the scratch audits and repository/API
searches are completed.

## Part A — finite-Hensel budget

The R45 source and its depth lemmas give the following exact ledger:

```text
theta^32 provenance
  -> theta^30, the largest usable multiple of three below 32
  -> scalar depth 10 from axis^(3*m) -> 7^m
  -> source theta-coordinate depth 9, because the rotation-gap
     constant coordinate is -7*C
  -> depth 9 for Z^7
  -> depth 8 for Z after one seventh-root drop
  -> depth 8 for v^(-1) after cancellation of (h.v)^2
  -> v = t^(7^8)
  -> W = rho * t^(7^9) after the outer seventh power.
```

The source-coordinate loss is literal: `7^10 ∣ -7*C` yields only
`7^9 ∣ C`.  The paired quotient comparison therefore supplies depth 9 for
`Z^7`, not depth 10.  The neutral seventh-power depth-drop theorem consumes
one level, so it supplies depth 8 for `Z`; the coprimality of `7` and
`(h.v)^2` transfers exactly that depth to `v⁻¹`.  The recursive unit extractor
then gives `7^8`, and the existing outer seventh power changes this to
`7^9` in `W`.

Consequently the theta^32 provenance alone does not justify depth 9 for
`v⁻¹`, nor an exponent `7^10` for `W`.  Either would require one additional
usable scalar depth before the source-coordinate loss or a new independent
jet.  No such input is present in R45.

## Part B — frozen successor routes

The previous route audits remain unchanged at the R45 endpoint.

- The ordinary homogeneous restart is still excluded by the checked weighted
  obstruction: the coefficient ratio has fixed nontrivial theta residue, so
  the weighted difference is not divisible by the ordinary root gap.  The
  high-power correction in `W = rho*t^(7^9)` does not alter that already
  certified residue obstruction.
- The square restart is still blocked.  The exponent `7^9` is odd, and the
  current factorization does not force the relevant coefficient to be zero or
  to be a square.  The R45 correction therefore does not activate the square
  theorem.
- The mixed-sign results exclude only their stated sign patterns.  An odd
  seventh-power correction does not determine the missing real signs, so it
  does not turn the mixed-sign theorem into a contradiction.

No successor implementation was reopened.

## Part C — trace-plane binary cubic

The scratch file
`DkMathTest/FLT/SevenTracePlaneBinaryCubicR46Scratch.lean` proves the complete
integer parameterization.  From
`3*A - 10*B + 35*C = 0`, it constructs integers `r,s` with

```text
A = 5*(r+s),  B = 5*r - 2*s,  C = r-s.
```

The converse identity is also kernel-checked.  Substitution into the actual
`SevenRealCubicInt.norm` definition fixes the sign, rather than leaving the
expected sign ambiguous:

```text
norm W = -(r^3 - 4*r^2*s - 11*r*s^2 + 43*s^3).
```

Thus the unit equation is exactly

```text
-(r^3 - 4*r^2*s - 11*r*s^2 + 43*s^3) = 1.
```

The checked rho coordinates are `(-20,-13,-2)`, and the binary-cubic pair is
`(r,s)=(-3,-1)`.  The scratch proof evaluates the displayed cubic at this
pair as `-1`, hence evaluates the norm expression as `1`.

## Part D — projective congruence

The same scratch proof unfolds only the checked definitions of
`thetaConstModSeven`, `thetaLinearModSeven`, `thetaSquareModSeven`,
`unitNilpotentX`, `unitNilpotentY`, and `projectiveLog`.  For a unit on the
trace-plane with projective log `(1,1)`, the nonzero constant coordinate gives

```text
B/A = 1,
C/A - (B/A)^2 / 2 = 1
```

in `ZMod 7`.  Under the `(r,s)` parameterization this yields

```text
r = 3*s  (mod 7).
```

The calibrated rho pair `(-3,-1)` satisfies this congruence, and the scratch
file applies the existing rho norm/projective-log theorems to check that
calibration.  No additional independent modulus-7 or modulus-49 congruence
on `(r,s)` was exposed by the current checked API.  The existing mod-49 jet
is expressed in the pre-parameterization unit coordinates and is not already
a pair-level congruence theorem.

## Part E — Thue formalizability audit

The repository and the available Mathlib sources contain no generic Thue
solver, effective bound for this binary cubic, or complete classification
theorem for the equation above.  The available finite-field, norm, and
polynomial APIs can evaluate a proposed pair and prove a bounded search
result once a bound is supplied; they do not supply that bound or certify
completeness of an unbounded search.

Answers to the required questions:

1. No existing Mathlib theorem reduces this exact cubic to a finite certified
   search.
2. No usable generic effective Thue theorem was found.
3. A complete classification would require substantial new Diophantine
   approximation/Baker-type bounds or an equivalent explicit unit/regulator
   argument, followed by a certified finite check.
4. The congruence `r = 3*s (mod 7)` is a useful local filter, but it does not
   provide a bound or materially convert the problem into a finite proof.

Any small-solution enumeration would therefore be heuristic only and was not
used as a proof.

## Part F — global unit lattice audit

The checked unit-class layer proves `unit_rank_eq_two`, class quotient
cardinality `49`, and bijectivity of `unitClassProjectiveLog`.  This is a
mod-seven quotient statement; it does not prove that `alphaUnit` and
`alphaAddOneUnit` generate the full unit group.

Mathlib's Dirichlet API supplies an abstract `fundSystem`, the unique
decomposition theorem `NumberField.Units.exist_unique_eq_mul_prod`, and the
rank-two quotient basis.  The basis is selected abstractly through
`Module.Free.chooseBasis`.  The regulator API also relates the index of a
concrete pair to a regulator ratio, but it does not identify the two explicit
units with the selected basis automatically.

To prove

```text
u = eps * alphaUnit^a * alphaAddOneUnit^b
```

for every unit, the missing work is an explicit generation/index-one proof:
one must show that the subgroup generated by the two displayed units and the
torsion has index one, equivalently compute or compare the corresponding
regulator/index.  Surjectivity modulo seventh powers only rules out an index
divisible by seven; it does not rule out another finite index.

Even if this basis theorem were proved, substituting
`rho*t^(7^9)` into `Phi(W)=0` would produce a rank-two exponential
Diophantine equation in the two unit exponents.  It would not by itself make
the endpoint finite or easy.

## Part G — calibration endpoint

The current C=1 declarations prove norm one, projective class `(1,1)`, and
zero trace-plane functional for rho, and R45 proves the correction
`W = rho*t^(7^9)`.  The R39–R45 declarations inspected here add no theorem of
the form `W ≠ rho` or any other exclusion of the calibration value.

Thus the checked endpoint is compatible with the special value `W = rho` at
the level of the remaining normal form.  This does not assert that the
original provenance realizes `W = rho`; it records only that no current
theorem rules it out.  A local or unit-lattice route whose conclusion is
merely `W = rho` would still need a second provenance clash.

## Part H — global C>1 inventory

For each prime `q` dividing `h.c`, the current checked surface supplies:

- `q` divides both square-root norms and the gap-split integer `a`;
- `q ≠ 7`, three primes above `q`, ramification index one, and inertia degree
  one;
- the exact oriented one-to-two prime allocation for the rotated gap roots;
- `q % 7 = 1 ∨ q % 7 = 6`;
- a residue-field element `beta` satisfying
  `beta^3 = 2*beta^2 + beta - 1` and a nonzero `z` satisfying
  `z^7 = beta*(1+beta)`.

These are local theorems parameterized by one `q` and one oriented prime.
The repository also has ordinary `Nat.factorization` and ideal-factorization
APIs, but the audit found no seventh-power residue symbol, reciprocity law,
global Kummer extension for `alphaUnit*alphaAddOneUnit`, product/parity law
over the three primes, or theorem relating the local residue condition to the
factorization exponent `a.factorization q`.  No cross-prime aggregation can
therefore be formed from the current checked surface.

## Part I — the q ≡ -1 branch

When `q % 7 = 6`, the seventh-power map on the finite residue field is an
automorphism.  Consequently the reduced condition
`z^7 = beta*(1+beta)` imposes no restriction on the nonzero right-hand side.

The original API retains the stronger 14th-power hypothesis and the oriented
one-to-two allocation while deriving the seventh-power condition, but no
checked theorem translates that retained 14th-power information into an
additional usable condition on `beta` or on the two rotated roots.  Thus the
current *reduced Kummer test* genuinely does not see the `q % 7 = 6` branch;
recovering a restriction from the 14th-power origin would require new residue
character infrastructure.

## Part J — ranked route assessment

1. **Route T — trace-plane/binary cubic.**  It has the most precise checked
   surface: the exact cubic, norm equation, class congruence, and R45 normal
   form.  The next theorem would be a complete solution or an effective bound
   for this Thue equation compatible with `r = 3*s mod 7`.  Current Mathlib
   does not support it; the scale is major new Diophantine theory.  A complete
   result could contradict the provenance, but the current normal form alone
   does not.
2. **Route U — explicit unit lattice.**  The next theorem is an index-one
   fundamental-unit proof for `alphaUnit, alphaAddOneUnit`, requiring an
   explicit regulator/index computation.  Mathlib supplies the abstract
   Dirichlet decomposition and index API, not the concrete computation.  The
   scale is major, and even success leaves a rank-two exponential equation
   rather than an immediate provenance contradiction.
3. **Route K — global Kummer/reciprocity.**  The next theorem is a global
   product or reciprocity relation combining all prime divisors of `C` and
   their oriented residue data.  The required seventh-power symbol/Kummer
   infrastructure is absent; the scale is major new theory.  If obtained it
   could contradict the C>1 branch, but no current endpoint does.
4. **Route S — successor/descent.**  The exact new theorem would have to
   bridge the R45 normalized state back to a fresh smaller-provenance state.
   The homogeneous, square, and mixed-sign routes remain frozen, so current
   infrastructure offers no credible bridge.  The scale is major and the
   endpoint would only contradict provenance after a genuine well-founded
   descent consumer is supplied.

R46 is therefore **Outcome E**: the finite-Hensel budget is saturated, the
trace-plane surface is now exact, and all four closure routes require a
substantial missing theorem.  The honest R47 scope is a narrowly bounded
choice between (i) a new certified theorem for the specific binary cubic or
(ii) a separately specified global residue/reciprocity infrastructure audit;
R47 must not present either as existing closure machinery.

## Validation record

The scratch file was checked sequentially with:

```text
lake env lean DkMathTest/FLT/SevenTracePlaneBinaryCubicR46Scratch.lean
```

It passed after checking the integer parameterization, converse, exact norm
sign, rho calibration value, projective congruence, and rho congruence
instance.  `git diff --check` and no-index whitespace checks for the new
scratch/report files emitted no diagnostics.  The decisive scratch file was
scanned for `sorry`, `sorryAx`, `admit`, `unsafe`, and project `axiom`; no such
construct was found.  No production module was added.
