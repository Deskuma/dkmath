# instruction-003 — LUNA Pell-parameter height production freeze

## Mission

LUNA-003 productionizes only deterministic facts already validated in
SOL-000 / ASTRA-001.

Main theorem:

~~~text
T represented in shell (X,D)
=>
D^2 * T^3 < 54 * (X+1)^6.
~~~

Secondary optional fact:

~~~text
inside one shell,
witness count
=
represented canonical (r,S) pair count.
~~~

Do not add asymptotic counting, external theorems, or new research mathematics.

## Repository

~~~text
repository: Deskuma/dkmath
branch: wip/ABC-GN-astra-260906-v1
campaign: lean/dk_math/docs/dev/ABC-GN-Astra-260906-v1/
~~~

Read:

~~~text
report-002.md
report-001.md
scratch-000.lean
scratch-001.lean
~~~

Inspect:

~~~text
DkMath/ABC/GNExcessCubicShellFiberUniqueness.lean
DkMath/ABC/GNExcessCubicPellParameterIncidence.lean
DkMath/ABC/GNExcessCubicSquarefulPell.lean
DkMath/ABC/GNExcessCubicRealizedIncidence.lean
~~~

## Part I — module

Add:

~~~text
DkMath/ABC/GNExcessCubicShellParameterBounds.lean
~~~

Import GNExcessCubicShellFiberUniqueness.

This module is a deterministic range ledger only.

## Part II — abstract height lemma

Port the scratch theorem pellParameter_height_cube_aux.

Assume:

~~~text
0 < D
D*S <= 3*(X+1)^2
r^3 < 2*D
T = r*S
~~~

Prove:

~~~text
D^2*T^3 < 54*(X+1)^6.
~~~

Use the scratch proof structure:

~~~text
D*T <= r * 3*(X+1)^2

(D*T)^3
<=
(r * 3*(X+1)^2)^3
<
(2D) * (3*(X+1)^2)^3

cancel positive D.
~~~

Do not sharpen 54.

## Part III — shell D*S wrapper

If no equivalent theorem already exists, prove for every represented shell
incidence pair (M,S):

~~~text
D*S <= 3*(X+1)^2.
~~~

Recommended name:

~~~text
GNExcessCubicRealizedLargeModulusShellIncidencePair_DS_le
~~~

Use only existing packet facts:

~~~text
D <= M
M*S = a^2+3a+3
a <= X
~~~

and the elementary bound:

~~~text
a^2+3a+3 <= 3*(X+1)^2.
~~~

If an equivalent theorem already exists, reuse it.

## Part IV — production Pell-parameter height

Port scratch theorem realized_shell_pellParameter_height_cube.

Recommended name:

~~~text
GNExcessCubicRealizedLargeModulusShellPellParameter_height_cube
~~~

Input:

~~~text
T in GNExcessCubicRealizedLargeModulusShellPellParameterSpace X D.
~~~

Conclusion:

~~~text
D^2*T^3 < 54*(X+1)^6.
~~~

Consume the existing Pell-parameter packet for:

~~~text
T = r*S
r^3 < 2D
~~~

and Part III for D*S.

Do not re-prove shell arithmetic unnecessarily.

## Part V — witness-level wrapper

For a shell witness a, set conceptually:

~~~text
r = oddPart M(a)
S = GNExcessCubicComplement a
T = r*S.
~~~

Prove:

~~~text
D^2*(r*S)^3 < 54*(X+1)^6.
~~~

Recommended name:

~~~text
GNExcessCubicRealizedLargeModulusShellWitness_pellParameter_height_cube
~~~

This should be a direct consumer of Part IV.

## Part VI — represented canonical pair image

Recommended finite image:

~~~text
GNExcessCubicRealizedLargeModulusShellCubeCoreComplementSpace X D
~~~

defined as the image of shell witnesses under:

~~~text
a |-> (oddPart M(a), Complement(a)).
~~~

This definition is optional but recommended because the research frontier is
now phrased in represented (r,S) pairs.

Do not add a new fiber hierarchy.

## Part VII — exact membership and card identity

If Part VI is implemented, prove exact membership:

~~~text
(r,S) is in the image
iff
there exists a shell witness a with
r = oddPart M(a)
and
S = Complement(a).
~~~

Then use the LUNA-002 shell-local injection to prove:

~~~text
CubeCoreComplementSpace.card
=
ShellWitnessSpace.card.
~~~

Recommended theorem:

~~~text
GNExcessCubicRealizedLargeModulusShellCubeCoreComplementSpace_card
~~~

This is an exact identity, not a sparsity estimate.

## Part VIII — optional represented-pair packet

Only if cheap, expose for a represented pair:

~~~text
1 <= r
r^3 < 2D

1 <= S
S <= X

Squarefree r
Squarefree S
Coprime r S

D*S <= 3*(X+1)^2

D^2*(r*S)^3 < 54*(X+1)^6.
~~~

This must be composition only.

Do not derive any cardinal upper bound.

## Negative boundaries

PROVED target:

~~~text
represented Pell parameter T:
D^2*T^3 < 54*(X+1)^6.

shell witnesses and represented canonical (r,S) pairs:
same cardinality, if the optional image object is added.
~~~

NOT PROVED:

~~~text
represented (r,S) pairs are sparse

N_X(D) << X^(2/3)

N_X(D) << X^(2+epsilon) D^(-4/5)

17/12 or 31/24 moment bounds in Lean

balanced-box power saving

ABC.
~~~

The height inequality is a range constraint, not a counting theorem.

## Do not productionize

Do not add:

~~~text
Helfgott-Venkatesh
Mordell integral-point estimates
average Pell estimates
Eisenstein factorization existence
balanced-box Q(B)
any asymptotic shell theorem.
~~~

## Public import

Import the new module from DkMath/ABC.lean immediately after
GNExcessCubicShellFiberUniqueness.

Do not reorder unrelated imports.

## Report

Create:

~~~text
lean/dk_math/docs/dev/ABC-GN-Astra-260906-v1/report-003.md
~~~

Title:

~~~text
# LUNA-003 — Pell-parameter height production freeze
~~~

Report:

1. files changed
2. abstract height lemma
3. D*S wrapper status
4. realized Pell-parameter height theorem
5. witness wrapper
6. represented (r,S) image status
7. image membership theorem
8. pair-space cardinal identity
9. optional packet
10. explicit no-sparsity boundary
11. focused build
12. ABC aggregator build
13. forbidden scan
14. axiom audit
15. remaining research frontier

Do not include commit hashes.

## Validation

Run:

~~~text
lake build DkMath.ABC.GNExcessCubicShellParameterBounds
lake build DkMath.ABC
~~~

Scan changed production Lean for:

~~~text
sorry
admit
axiom
abc_main_axiom
native_decide
unsafe
~~~

No new occurrences.

Audit the principal height and card declarations.

Expected trust boundary:

~~~text
propext
Classical.choice
Quot.sound
~~~

or a subset.

## Stop condition

Stop when production DkMath exposes:

~~~text
T represented in shell (X,D)
=>
D^2*T^3 < 54*(X+1)^6.
~~~

If cheap, also freeze:

~~~text
shell witness count
=
represented canonical (r,S) pair count.
~~~

Do not derive an asymptotic estimate.
Do not begin balanced-box counting.
Do not open LUNA-004 automatically.
