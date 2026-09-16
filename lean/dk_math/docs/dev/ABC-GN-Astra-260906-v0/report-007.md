# ASTRA-007 — realized cubic modulus geometry

## Live result ledger

- Investigation started. No aggregate bound claimed.

## Current strongest surviving route

Pending exact experiments and Lean checks.

## Branch C — witness multiplicity and spacing
Status: CLOSED for injectivity / at-most-two shortcuts; spacing investigation active.

Exact sieve through 200000 found the first large collision at X=145:
M=169, a=21 and 145; F=3*169 and 127*169 respectively.
A composite counterexample is M=8281=7^2*13^2 with FOUR witnesses
2173,3018,5260,6105 in [1,6105], all with the same FULL repeated part.
Complements are respectively 571,1101,3343,4503; these are squarefree and
coprime to 8281. Thus full repeated-part equality does not remove mixed CRT
roots. M>X+1 does not imply at most two witnesses. Exact numerical output is
in validation-007.txt; Lean certificates follow.

## Branch A — powerful part and complement
Status: PROMISING structural reduction; no aggregate bound.

Exact sieve checks v_3(F)≤1, S=F/M squarefree, gcd(M,S)=1 through 200000.
S is not an injective witness coordinate: S=3 at a=21,312,4365,60816;
S=1 at a=17 and 88915. Complement grouping needs multiplicity estimates.
These observations are numerical until the generic decomposition is compiled.

### Branch A kernel-checked update
Status: PROVED-IN-SCRATCH for the decomposition; OPEN for its summation.

Compiled `full_repeated`: GNNonExceptionalRepeatedPart 3 a 1 equals the
full repeatedPrimePowerPart of F(a). `not_nine` proves 9 does not divide F(a)
by all nine residues, so removing the exceptional prime changes no repeated
factor. `complement_decomposition` proves for every n≠0 that
n=repeat(n)*(n/repeat(n)), the quotient is squarefree, and the two factors
are coprime. `canonical_decomposition` specializes this to every cubic point.
`complement_small` proves the sharper bound S≤X+1 from a≤X, MS=F(a), M>X+1
(no primality assumptions needed). All five proofs are persisted in scratch.

The complement is NOT the parity squarefree kernel: at a=17, F=M=7^3,
S=1 but the parity kernel is 7. This distinction matters in a Pell reduction.
Exact missing step: weighted control across the small squarefree complements,
including multiple points for each complement. No summability follows just
from S≤X+1.

## Branch B — discriminant, norm geometry, and complement conics
Status: OPEN for counting; exact algebra under Lean validation.

Target: exploit the norm equation beyond local root counts.
F(a)=a²+3a+3 satisfies 4F(a)=(2a+3)²+3 and is strictly between
(a+1)² and (a+2)², hence never a square. If M=d²r with r squarefree
and r|d (the parity part of a squareful integer), then
(2a+3)²-4(Sr)d²=-3. Because gcd(M,S)=1, Sr is squarefree.
This parity factor r is essential; replacing the Pell parameter Sr by S is
false already at F(17)=7³. The existence/uniqueness of this parameterization
is elementary factorization arithmetic but is not yet a compiled Lean lemma
in this scratch; only the conditional conic identity is checked.

For the S=3 square subfamily, the explicit recurrence
(a,d) -> (7a+12d+9, 4a+7d+6)
preserves F(a)=3d² and strictly increases a. From (0,1), it gives
(21,13), (312,181), (4365,2521), (60816,35113).
The invariant a≡0 mod3, d≡1 mod3 ensures the full complement remains 3.
Thus a bounded complement is compatible with indefinitely many witnesses;
this recurrence is not a decreasing map across arbitrary moduli.

Eisenstein multiplication supplies a second route: for ω²+ω+1=0,
write (s+tω)(u+vω)²=A+Bω. Then
A=s(u²-v²)-t(2uv-v²), B=t(u²-v²)+(s-t)(2uv-v²),
and N(A+Bω)=N(s+tω)N(u+vω)².
A representation of a+1-ω requires B=-1. This is a concrete binary
quadratic constraint, but existence of the oriented square factor and uniform
counting as s,t vary remain to be proved. The ring identity alone does not
supply the representation or its global sparsity.

Missing lemma: a weighted uniform count of these conics / coefficient-±1
norm factorizations across varying squarefree parameters. Fixed-parameter
Pell growth alone cannot be summed for free over S,r.

## Branch D — squareful counting and exact exponent audit
Status: CLOSED for the elementary height-only / CRT-boundary route; OPEN for
an additional arithmetic incidence theorem.

For a dyadic modulus shell D≤M<2D, the weight is O(D^(3/8)).
The elementary squareful parameterization M=u²v³ with v squarefree gives
O(sqrt(D)) squareful integers up to D, since the sum of v^(-3/2) converges.
Dropping the witness condition therefore gives shell cost D^(7/8), and up to
height D~X² gives X^(7/4), not linear. Restricting prime residues cannot be
assumed to save a power of X.

Ordinary root counting gives at most rho(M)*(X/M+1) witnesses per modulus.
The expected density term has summable weighted shell cost
X*D^(-1/8), but the +1 boundary term costs D^(7/8) (up to root-count factors).
It is precisely this boundary which must be removed by GLOBAL incidence,
not by unique local Hensel digits. Switching sums does not remove the +1.

A genuinely sufficient stronger counting input would be
N_X(D) ≤ C_epsilon * X^(1+epsilon) / sqrt(D)
for all X+1≤D≲X², with a fixed epsilon<1/8, where N_X counts distinct
realized moduli in the shell. Dyadic summation would give
O(X^(7/8+epsilon)), hence linear. This is an UNPROVED research target,
not a renamed definition or a provider assumed in Lean.

More generally a proposed error term D^beta in the shell count contributes
X^(2*beta+3/4) at the top shell; linear closure requires beta≤1/8.
Even a uniform O(1) witness multiplicity per modulus would not itself bound
how many distinct moduli are realized.

### Primary-source cross-check (not imported into Lean)
Wongcharoenbhorn and Meemark, “Square-full values of quadratic polynomials”,
arXiv:2405.06968v2, 2025-03-06:
https://arxiv.org/html/2405.06968v2
Theorem B gives an exponent approximately 0.4769 for counting square-full
values of a fixed admissible quadratic. It addresses full squareful values,
not this varying-complement weighted divisor sum. Even multiplying that
count by the individual X^(3/4) weight would exceed the required linear
scale. The paper's separate ABC-conditional assertions cannot be inputs to
this campaign. This check supplies context, not a theorem-grade closure.

### Branch A/B/C second kernel-checked update
`complement_sharp` improves S≤X+1 to S≤X for X>0. The proof uses integrality:
S=X+1 forces a=X, then MS lies strictly between consecutive multiples of S.
`no_square`, `pell_shell`, `pell_step`, `pell_step_grows`,
`norm_square_product`, `roots_difference`, and `spacing` all compile.
The spacing theorem is M≤(b-a)(a+b+3) for distinct witnesses a<b of M|F.
It is useful near the top height, but gives only gaps ≳M/X in general.
The paired product and linear-complement identities also compile.
These successful blocks have been copied to the persistent scratch file.

### Branch B/C third kernel-checked update
The Pell recurrence now has a compiled invariant for every n, strict
monotonicity of its a coordinate, exact repeated part d_n², and EXACT constant
complement 3 (`pell_invariant`, `pell_strictMono`, `pell_repeated`,
`pell_complement`). This proves unbounded complement-fiber multiplicity
across expanding intervals, not merely the finite numerical collisions.
It does not contradict a uniform bound for a fixed modulus fiber.

Eight explicit repeated-part evaluations (17,21,145,2173,3018,5260,6105,88915)
are also compiled using prime-factorization certificates and norm_num, without
native_decide. In particular the four-root example concerns the exact FULL
repeated part, not just a common divisor. All blocks are persisted.

### Branch E and final obstruction ledger
The paired-product route is algebraically valid but gives no monotone descent:
`F(a)*(3*a^2+3*a+1)=3*(a+1)^4+a^2` and
`3*F(a)-(3*a^2+3*a+1)=6*a+8` are kernel-checked. The numerical scan to
200000 found no pair for which both complementary full factors are above the
corresponding height. This is evidence only; it is not a universal theorem.
The absolute Pell family is now formalized: `a_0=0,d_0=1` and
`a_(n+1)=7*a_n+12*d_n+9`, `d_(n+1)=4*a_n+7*d_n+6` satisfy
`F(a_n)=3*d_n^2`, strict growth, and repeated part `d_n^2`. Hence complements
can remain exactly 3 while the height grows, so a local complement lower bound
cannot close the sum.

The new Lean lemma `squarefull_block_obstruction` records a necessary strength
for any direct linear closure: if every `a` in a block `[X,2X]` has full
repeated part `F(a)`, then its cardinality times `X^(3/4)` is bounded by the
realized modulus moment at `2X`. Thus such a block can have only the scale
`O(X^(1/4))` under a linear moment bound. Establishing this polynomial-value
count, or an equivalent global incidence estimate, remains the exact frontier.

All five permitted branches A--E have now been investigated. No branch gives
the requested ABC closure, and no new axiom, `sorry`, research provider, or
production theorem was added. The checkpoint therefore stops at a documented
research boundary; the next Luna-sized task is to prove a quantitative global
incidence/counting lemma and integrate it only after an independent provider is
available.

### Final verification
`lake env lean /tmp/all007.lean` exits 0 (warnings are linter-only); the exact
source is copied to `scratch-007.lean.txt`. The numerical script exits 0 at
`--limit 200000`, checks all sieve identities with integer arithmetic and an
independent factorization sample, and emits certified fixed-point fractional
moment intervals. The production tree is unchanged.

### Decisive theorem candidate for Luna
For every `ε < 1/8`, prove a uniform dyadic incidence estimate
`N_X(D) ≤ C_ε X^(1+ε)/sqrt D` for realized full repeated moduli in
`D ≤ M < 2D`, `X+1 ≤ D ≲ X²`. Together with the exact finite Euler reduction,
this would yield a sublinear dyadic sum and hence the desired linear bound.
The scratch theorem `squarefull_block_obstruction` records a necessary
polynomial-value consequence of any such closure. No assumption of this
candidate is imported into production.

### Closed routes and remaining frontier
Closed as proof methods: quadratic injectivity, at-most-two witness claims,
local Hensel uniqueness, naive squareful counting, and paired-factor size
inference from coprimality. They are retained as exact identities or
counterexamples. The remaining gap is a genuinely global incidence estimate
for the quadratic values with their full repeated parts; this is the only
recommended next production-sized investigation.
