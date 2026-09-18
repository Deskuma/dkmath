# A. New verified deductions

Authoritative start: HEAD
`fd31442bd3cadee821b55712df47c7a1f12154f9`, branch
`research/FLT7-Unconditional-TraceOne-Closure-260917-v0`.
Read `astra-001.md`, `ROADMAP.md`, and reports 013–022. The worktree was clean.
This report and adjacent scratch artifacts were saved incrementally. All Lean
processes were run serially. The implementation is a research certificate and
reproducible experiments under `astra-001/`; no production API is needed for
the requested synthesis.

The R17 frontier can be sharpened. The direct roots are coprime, their root
gap is theta-divisible, the homogeneous quotient has exact theta depth 3,
and every common prime of those two factors is associated to theta. The
three-edge unit classes are compatible. A further mathematical deduction
gives a strictly smaller positive integer norm after seventh-power extraction;
constructing a successor arithmetic state is still the closure gap.

Evidence levels used throughout:

| Level | New result | Evidence |
| --- | --- | --- |
| Kernel | `log(sigma u)=M log(u)`; order-three action and zero norm operator | `projectiveLog_rotate`, `classRotate_order_three`, `classRotate_norm_zero` |
| Kernel | Three exact-power edges, classes `(0,5),(0,3),(0,6)`, unit product 1 | `three_edges`, `all_edge_classes`, `orbit_units_product` |
| Kernel | Norm of the edge seventh root and polynomial norm of the root gap | `norm_orbitW`, `norm_gap_formula` |
| Kernel | First pair of roots coprime; generic common-prime classification | `direct_roots_coprime`, `common_prime_of_gap_quotient` |
| Kernel | Quotient core with theta depth 3; `theta^32` divides the root gap | `direct_quotient_core`, `direct_gap_theta32` |
| Kernel | Two real inequalities used in the height argument | `realH7_ge_seven`, `realH7_ge_gap` |
| Mathematical deduction | Exact depth `32+42k`; stripped-core extraction and unit classes | Explicit argument in C; full direct packet not yet formalized |
| Mathematical deduction | `0 < abs(Norm(g)) < A/7^v7(A) <= A` | Explicit argument in D; embedding/packet transport not yet formalized |
| Computation | All 294 local units modulo `(7)`; exact trace-zero witness; local root modulo `7^14` | `orbit_experiments.py`, `orbit-experiments.log` |

All theorem names in the table belong to
`DkMath.FLT.Seven.Astra001` in [OrbitChecks.lean](astra-001/OrbitChecks.lean).
The direct statements take the existing `DirectRealCubicRootPacket source r`;
no historical packet is an extra input. The first-pair proof transports by
`sigma` to give the other two pairs. Norm equality is used as a product
identity, never to identify elements.

Validation, from `lean/dk_math`:

```text
lake env lean docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/astra-001/OrbitChecks.lean
python3 docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/astra-001/orbit_experiments.py
```

Both completed with exit status 0. The final [Lean log](astra-001/lean-check.log)
contains only `propext`, `Classical.choice`, and/or `Quot.sound` in all twelve
printed axiom audits. This is a focused scratch check, not a repository-wide
build. The experimental Python inverse constant was corrected against
`alphaAddOneInv` before recording the successful final run.
Final source scans found no `sorry`, `admit`, `unsafe`, project axiom declaration,
or forbidden receiver input in the Lean scratch; the Lean log has no errors,
warnings, or `sorryAx`. `git diff --check` and individual
`git diff --no-index --check /dev/null <file>` checks of the new report,
Lean source, and Python source produced no whitespace diagnostics.

# B. Full three-edge unit-class analysis

Write `sigma=rotateEquiv`, `theta=eisensteinAxis`, `U=thetaSevenUnit`,
`epsilon=orbitUnit01`, `A=gapRoot`, `B=residualRoot`. In integral theta
coordinates `(a,b,c)`, direct substitution in `rotateHom` gives

```text
sigma(a+b*theta+c*theta^2)
  = (a-7c) + (4b-21c)*theta + (b-5c)*theta^2.
```

Modulo `(7)`, this is `(a,4b,b+2c)`. For a theta-unit put
`X=b/a`, `Y=c/a-X^2/2`. Therefore the projective-log action is linear:

```text
M(X,Y) = (4X, X+2Y),       M = [[4,0],[1,2]] over F7.
M^3 = I,                  I+M+M^2 = 0.
```

This applies to every global unit and is kernel checked; it is not an
inference from two chosen generators or from finite sampling. There is no
affine offset. Its eigenvalues are 4 and 2, and it has no nonzero fixed class.

Let `epsilon_i=sigma^i(epsilon)` and `W_i=sigma^i(theta^5*U*A^2)`.

| Edge | Exact equation | Unit class |
| --- | --- | --- |
| 0 to 1 | `rho1^7-rho0^7 = epsilon_0*W_0^7` | `(0,5)` |
| 1 to 2 | `rho2^7-rho1^7 = epsilon_1*W_1^7` | `(0,3)` |
| 2 to 0 | `rho0^7-rho2^7 = epsilon_2*W_2^7` | `(0,6)` |

Each class is nonzero, so the unit seventh-power criterion excludes a unit
seventh root on every edge. Their sum is zero. More strongly,

```text
Norm(U) = -1,     Norm(epsilon) = 1,
epsilon_0*epsilon_1*epsilon_2 = 1,
W_0*W_1*W_2 = 7^5*A^6,
product_i (rho_(i+1)^7-rho_i^7) = 7^35*A^42.
```

Indices are cyclic. The unit product and `Norm(W_0)` have kernel certificates;
the last two identities follow from the cyclic norm product and the checked
edge equations. The telescope is exactly zero by subtraction. Both the
telescope and the product also hold for the explicit sources `S_i` before
assuming their seventh roots. Hence neither creates a unit-class conflict.
The separate identity `rho0*rho1*rho2=B` does give the prime-support argument
in C, but its seventh power is already the source norm identity.

# C. Theta-adic factorization analysis

The generic theorem
`exists_seventhQuotient_core_exactDepth_three` in `SevenRealCubicAxisDrop`
has exactly the inputs needed here: theta-unit `rho` and
`theta | sigma(rho)-rho`. The latter follows directly from
`thetaResidue_rotateEquiv`. Thus the old report's boundary can already be
sharpened: the homogeneous quotient has exact depth 3 on the direct route.
Normalize `v_theta(theta)=1`; since `7=theta^3*U`, rational integers have
`v_theta(n)=3*v7(n)`. Write `A=7^k*a`, with `a>0` and `7 ∤ a`, and set
`d=rho1-rho0`, `H=H7(rho1,rho0)`, `n=32+42k`. All factors are nonzero:
`A>0`, `epsilon` and `U` are units, and the ring is a domain. Thus

```text
v_theta(W_0) = 5+6k,
v_theta(d*H) = 35+42k,
v_theta(H) = 3,
v_theta(d) = 32+42k.
```

The exact quotient factorization and the lower bound `theta^32 | d` have
kernel certificates. Exact valuation additivity and the rational-integer
depth calculation complete the displayed full formula mathematically; that
general-`k` direct API is not part of the scratch certificate.

Explicit prime-support argument: if a prime `q` divides two orbit roots, it
divides their seventh-power difference. The unit coefficient drops out by
primality; hence `q | theta` or `q | A`. The first contradicts the theta-unit
root. In the second, `rho0*rho1*rho2=B` gives `q | B`, and the integer Bezout
relation from `gcd(A,B)=1`, mapped into the cubic order, gives a contradiction.
Thus the roots are pairwise coprime. If a prime divides both `d=rho1-rho0`
and `H=H7(rho1,rho0)`, reduction modulo `d` gives `q | 7*rho0^6`;
root coprimality excludes `q | rho0`, so it must be associated to theta.
After exact theta stripping, the two cores are coprime and PID seventh-power
extraction applies. This is derived support control, not an inference from
coprime norms.

In detail, write `d=theta^n*d0` and `H=theta^3*h0` with theta-free cores.
Any common prime would divide `d,H`, hence be associated to theta, excluded
by the core definitions. Cancellation in the direct edge gives

```text
d0*h0 = epsilon * (U^(1+2k)*a^2)^7.
```

The existing `exists_associated_pow_of_associated_pow_mul`, applied to these
coprime cores, supplies global units `eta,nu` and theta-free nonzero `g,h`:

```text
d0 = eta*g^7,    h0 = nu*h^7.
```

These extraction conclusions are mathematical applications of the existing
PID lemma; the full packet constructor remains the bounded implementation
task in F. The generic common-prime lemma was proved in the scratch using
`gap_dvd_seventhQuotient_sub_seven_mul_pow_six`. The historical
`RamifiedRealCubicDepthLedgerPacket.normalizedFactors_isCoprime` supplied the
proof pattern; no instance of that packet was assumed.

The fixed class is distributed consistently. Since `d` is divisible by
`theta^32`, it is divisible by `(7)`. The fixed-vector equations for rotation
modulo `(7)` force the two nonconstant theta coordinates of `rho0` to vanish.
Thus `rho0` is a nonzero rational scalar modulo `(7)`. Expand `H` about
`rho1=rho0+d` and divide by `theta^3` using the generic quotient-core formula:

```text
h0 = U*rho0^6 mod (7).
```

Every correction has theta depth at least 32 (the last term is deeper).
The same normalized logarithm is defined on local theta-units by the explicit
coordinate formula; multiplicativity is the polynomial calculation used by
`projectiveLog`, and a seventh power has zero log. This does not apply the
global unit-root criterion to a nonunit. After the genuine global-unit
extractions above, it gives

```text
log(nu)  = log(U) = (5,1),
log(eta) = (0,5)-(5,1) = (2,4).
```

Both are realizable global unit classes, not impossible classes. Moreover,
stripping by the same theta on each edge introduces a rotation twist:
`d0_next=(1+alpha)^n*sigma(d0)`. Since `n=4 mod 7`, the gap-core unit classes
are `(2,4),(2,2),(2,5)`, while the quotient-core classes are all `(5,1)`.
Their sums are `(6,4)=n*log(U)` and `(1,3)=3*log(U)`, respectively, exactly
the twists of their rational norm products. Treating these stripped classes
as untwisted Galois transforms would create a false obstruction.

The exact norm polynomial for `rho=a+b alpha+c alpha^2` is
`Norm(sigma(rho)-rho)=7*(b^3+4b^2*c+3b*c^2-c^3)`.
The norm formula is kernel checked. The edge norm yields
`Norm(d)*Norm(H)=7^35*A^42`. Consequently every rational prime in these
norms lies over 7 or a divisor of A. In fact both `d` and `H` are coprime
to the integer B inside the cubic order: a common prime with B would divide
the edge RHS, hence theta or A, both excluded by `7 ∤ B` and the mapped
Bezout identity. This does not imply that `Norm(d)` and `Norm(H)` are
coprime integers; distinct conjugate prime ideals can lie above one rational
prime. Norms of coprime cores must not be fed to an integer coprimality lemma.

The finite local diagnostic uses `A=1`, `R=1`, `L=1+7^6` and the root
`(96606551966,282475249,282475249)` in the alpha basis modulo `7^14`.
It verifies `rho^7=S0` at that precision and computes exact depths 32 and 3
for the chosen integral lift's gap and quotient. This is not a global
integral root or an integer `B^7` norm witness. The experiment is sufficient
to reject a contradiction from these finite local conditions alone.

# D. Candidate closure routes

One route survives as a concrete research candidate: **stripped gap-root norm
reduction, followed by successor-state construction**.

The theorem chain is the direct exact-power packet, C's root coprimality and
exact depths, coprime PID extraction, total positivity, and an Archimedean
bound. Here is the full bound, so that a future reconstruction theorem has a
specific well-founded measure to preserve.

The nonzero relative norm `rho=Norm_(K/K+)(gammaNorm)` is totally positive:
each real embedding of the maximal real field extends to a complex embedding
of K, where the relative norm is `|gammaNorm|^2>0`. This uses the actual CM
conjugation, whose transport was established in R15. All three conjugates
of rho therefore are positive real numbers and their product is B. The
scratch proves the elementary identity/inequality

```text
H7(s,t)-7*(s*t)^3
  = (s^3-t^3)^2 + s*t*(s^2-t^2)^2 + s^2*t^2*(s-t)^2 >= 0
```

for nonnegative `s,t`. Multiplying over the three pairs gives
`Norm(H)>=7^3*B^6`. If `G=abs(Norm(g))`, then `G` is a positive integer:
g is nonzero and its norm is a nonzero integer. As `n=32+42k` is even and
the norm of a global unit is ±1, taking absolute norms of the split edge gives

```text
7^n * G^7 * Norm(H) = 7^35 * A^42,
G^7 * B^6 <= a^42,                 A=7^k*a.
```

For the original signed endpoints set `D=L-R=7^6*A^7>0`. The second scratch
inequality is valid for all real `L,R`, including the signed z-branch:

```text
64*H7(L,R)-D^6
  = 7*(L+R)^6 + 35*(L+R)^4*D^2 + 21*(L+R)^2*D^4 >= 0.
```

Since `H7(L,R)=7*B^7`,

```text
B^7 >= 7^35*A^42/64 > A^42 >= a^42.
```

Raise the strict inequality to the sixth power: `B^42>a^252>=a^245`,
using `a>=1`. Thus `B^6>a^35`. If `G>=a`, then
`G^7*B^6>a^42`, contradicting the earlier bound. Therefore

```text
0 < G < a <= A.
```

This is an explicit mathematical deduction from the direct packet and the
derived extraction, with the two real inequalities kernel checked. The
entire norm/embedding chain and extraction constructor have not been
formalized here. It would, in particular, exclude the special case `a=1`.
It does not yet constitute a strict descent: an integer below A is not itself
a new FLT state.

The first missing **conceptual** theorem is a successor constructor from
`rho,g,h,eta,nu` and their retained equations to a new primitive state with
oriented integers `L',R'` and positive integers `A',B'`, the same seventh-power
and coprimality laws,
and `A'<=G`. Equivalently, an enlarged state could work, but its constructor
must prove all invariants used by the same extraction and height bound.
Just assigning `A'=G` is not such a constructor. No formula for these new
endpoints has been derived. The goal of this route is strict descent in the
natural A; a closed successor theorem would permit well-founded induction.

The route is noncircular through the norm reduction: its inputs are the
current provenance, generic PID facts, and explicit real inequalities. A
successor axiom, an assumed smaller counterexample, or the historical
prescribed-carrier receiver would make the remaining step circular. The
generic Kummer search found conditional peel/reconstruction targets, not a
clean constructor supplying this missing step.

# E. Rejected routes

1. The R17 mod-49 gate is equivalent to the summit sixth-root condition.
   Re-enumeration adds no new obstruction.
2. A nonzero edge unit class is compatible with all three rotated equations.
   The norm operator on classes vanishes identically and the actual unit
   product is 1. Taking their sum or product cannot erase this distinction.
3. Trace zero plus the predicted gap-core class is itself consistent even
   globally. Let `d*=7^10*(sigma(alpha+alpha^2)-(alpha+alpha^2))`. Exact
   integer-coordinate calculation gives `Trace(d*)=0`, depth 32, and
   `d*=theta^32*eta*`, where
   `eta*=(1372223811812,-761526763409,-3083358916877)` in the alpha basis.
   It has norm 1 and projective log `(2,4)`. Thus the trace-zero gap equation
   admits a unit-core witness (`g=1`). This is not an FLT state and fails to
   supply the original simultaneous source conditions. It directly rejects
   a proposed impossibility theorem using only that trace and unit class.
4. Higher precision at theta alone does not supply a global reconstruction;
   the recorded `7^14` root is a concrete finite consistency witness. It is
   not evidence of a global counterexample or a proof of solvability at all
   primes.
5. Element coprimality does not follow by comparing the common norms B.
   C uses the mapped integer Bezout identity and an actual prime divisor.
   Conversely, coprime elements can have norms sharing a rational prime.
6. `SevenRealCubicThetaSeventhPower` exposes exact coordinate expansions;
   these are not an exclusion theorem. `SevenRealCubicCoprimeExtraction`'s
   linear-source consumer expects a primitive linear source; rho and its
   extracted roots have not been proved to be such sources. Historical
   `AxisDrop` depths 10/13 do not equal the present depths 32+42k/35+42k.
7. `SevenRamifiedFusionRotationPhase` contributes the neutral residue
   rotation lemma, and the real-pair carrier/norm-gate files contribute
   explicit units and the cyclic norm identity. Their signed-root packets
   cannot be used as inputs merely from similar formulas. Generic Kummer
   ideal-extraction and common-prime lemmas were inspected before choosing
   the shorter concrete PID proof; no legacy default descent consumer was
   used.

# F. Best next bounded checkpoint

**ONE checkpoint: direct orbit stripped-factor extraction and smaller norm.**

Suggested production module:
`DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicOrbitSplit.lean`.
Start from the scratch certificates and the existing direct R17 packet.
Normalize `A=7^k*a`, `a>0`, `7 ∤ a`, with checked equality to the original A.
Suggested theorem shapes, all parametrized by the same `source,r,p`:

```text
direct_orbit_exact_depths :
  HasExactThetaDepth (sigma p.rho - p.rho) (32+42*k) ∧
  HasExactThetaDepth (seventhQuotient (sigma p.rho) p.rho) 3

direct_orbit_stripped_split :
  ∃ d0 h0 g h eta nu,
    d = theta^(32+42*k)*d0 ∧ H = theta^3*h0 ∧
    IsCoprime d0 h0 ∧ theta ∤ d0 ∧ theta ∤ h0 ∧
    d0*h0 = epsilon*(U^(1+2*k)*a^2)^7 ∧
    d0 = (eta : O)*g^7 ∧ h0 = (nu : O)*h^7 ∧
    log eta = (2,4) ∧ log nu = (5,1)

direct_gap_root_norm_lt :
  0 < Int.natAbs (norm g) ∧ Int.natAbs (norm g) < a
```

Here `eta,nu : Oˣ`, `O=SevenRealCubicInt`; `d,H` are definitions, not new
free hypotheses. Package the extraction with its witnesses before stating
the bound. Prove the required embedding compatibility and total positivity
from the retained relative norm; audit every decisive theorem's axioms.
The generic depth helpers currently marked private in `AxisDrop` can be
reproved or exposed without transporting any historical packet.

Terminal boundary: a checked smaller positive norm and its exact direct
factor packet. Do not call this descent, assume a successor, enter either
forbidden receiver packet, drop either unit, equate elements from norms,
or infer coprime rational norms. Record the missing successor constructor
explicitly. Only a proved successor plus its inherited strict bound could
open a subsequent well-founded descent checkpoint.

# G. Confidence

**C — structural progress, but a complete closure mechanism is not yet visible.**

The full orbit-class calculation, direct root coprimality, quotient-depth
specialization, and prime-support control are high-confidence kernel results.
The exact full depths, factor unit classes, and smaller-norm calculation are
explicit mathematical deductions with the formalization scope stated above.
The trace-zero and finite-local witnesses rule out several attractive but
insufficient shortcuts.

The remaining uncertainty is substantive: the extracted cubic root has not
been converted to a state on which the same argument can be repeated. Thus
classification A or B would overstate the evidence. Classification D would
also discard the new factor control and explicit smaller-norm candidate.
No unconditional FLT7 theorem or complete strict descent is established here.
