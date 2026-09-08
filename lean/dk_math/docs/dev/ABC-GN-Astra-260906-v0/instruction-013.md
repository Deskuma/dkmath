# instruction-013 — LUNA squareful parity / Pell-shell coordinates

## Mission

Continue the ABC–GN campaign in **fact-freezing / productionization mode**.

This checkpoint is **LUNA-013**.

LUNA-012 froze the exact shell incidence pair

~~~text
(M,S)
~~~

with a unique canonical witness a and

~~~text
M*S = a^2 + 3*a + 3,
M in [D,2D),
X+1 < M,
1 <= S <= X,
Squarefree S,
Coprime M S.
~~~

ASTRA-007 identified a second exact coordinate useful for future incidence
counting: decompose the squareful modulus M into its parity-square pieces and
rewrite the quadratic equation as a negative-Pell-type shell equation.

The existing DkMath API already provides:

~~~text
oddPart
evenPart
decomp_oddPart_evenPart
~~~

with

~~~text
n = oddPart(n) * evenPart(n)^2.
~~~

LUNA-013 should freeze the additional deterministic facts needed when n is
squareful and apply them to the realized cubic incidence pair.

Do **not** count Pell solutions and do **not** estimate shell cardinalities.

---

## Repository

~~~text
repository: Deskuma/dkmath
branch:     wip/ABC-GN-astra-260906-v0
campaign:
  lean/dk_math/docs/dev/ABC-GN-Astra-260906-v0/
~~~

Read first:

~~~text
report-012.md
report-011.md
report-010.md
report-009.md
report-007.md
~~~

Inspect current production source, especially:

~~~text
DkMath/ABC/Square.lean
DkMath/ABC/SquareTailBasic.lean
DkMath/ABC/GNExcessLargeBoundaryPacket.lean
DkMath/ABC/GNExcessCubicComplementPell.lean
DkMath/ABC/GNExcessCubicComplementIncidence.lean
~~~

Treat current production Lean as authoritative.

---

## Reporting policy

Do **not** include branch HEAD hashes or commit hashes in report-013.md.

Report exact arithmetic declarations, verification, and the remaining research
boundary.

---

# Part I — generic squareful parity decomposition helpers

Add a focused production module.

Recommended file:

~~~text
DkMath/ABC/GNExcessCubicSquarefulPell.lean
~~~

If some generic helper clearly belongs in SquareTailBasic or Square, a small
addition there is acceptable, but avoid broad refactoring.

The generic target starts from decomp_oddPart_evenPart n hn, which gives

~~~text
n = oddPart n * (evenPart n)^2.
~~~

For a squareful n, freeze the further properties below.

---

# Part II — oddPart is squarefree

Prove the generic theorem:

~~~text
theorem squarefree_oddPart (n : Nat) :
    Squarefree (oddPart n)
~~~

or an equivalent theorem under n != 0 if the Mathlib characterization makes
that cleaner.

The proof should be direct from the factorization definition:

~~~text
v_q(oddPart n) = v_q(n) mod 2
~~~

so every exponent is 0 or 1.

Before adding a new theorem, check whether an equivalent theorem already exists
under another name.

Do not build a new squarefree theory.

---

# Part III — squareful n implies oddPart n divides evenPart n

This is the key generic squareful lemma.

For:

~~~text
squarefull n
~~~

and, if necessary, n != 0, prove:

~~~text
oddPart n divides evenPart n.
~~~

Recommended name:

~~~text
oddPart_dvd_evenPart_of_squarefull
~~~

Reason coordinatewise:

- a prime occurs in oddPart only when v_p(n) is odd,
- if it occurs at all and n is squareful, v_p(n) >= 2,
- an odd exponent >= 2 is at least 3,
- therefore floor(v_p(n)/2) >= 1,
- so the same prime occurs in evenPart.

Use existing factorization/support API rather than ad hoc primality searches if
possible.

This theorem is deterministic arithmetic.

---

# Part IV — canonical squareful representation

For nonzero squareful n, define or expose:

~~~text
r := oddPart n
d := evenPart n.
~~~

Prove the packet:

~~~text
n = r * d^2
Squarefree r
r divides d.
~~~

Recommended theorem:

~~~text
squareful_oddEven_packet
~~~

A conjunction theorem is enough; a structure is optional only if it clearly
simplifies later consumers.

If clean, derive the classical canonical parameterization.

Since r divides d, write:

~~~text
d = r*u.
~~~

Then:

~~~text
n = u^2 * r^3.
~~~

A preferred theorem shape is:

~~~text
theorem exists_sq_mul_cube_of_squarefull
    {n : Nat} (hn : n != 0) (hfull : squarefull n) :
    exists u r : Nat,
      Squarefree r and
      n = u^2 * r^3
~~~

However, the stronger canonical coordinate using r = oddPart n is preferred if
convenient.

Do not spend excessive effort on the square-times-cube corollary; the exact
oddPart/evenPart packet has priority.

---

# Part V — realized cubic modulus is squareful in the generic predicate

The current realized modulus API already proves:

~~~text
prime q divides M -> q^2 divides M.
~~~

Bridge this to the existing predicate:

~~~text
squarefull M.
~~~

For:

~~~text
M in GNExcessCubicRealizedLargeModulusSpace X
~~~

prove:

~~~text
squarefull M.
~~~

Recommended name:

~~~text
GNExcessCubicRealizedLargeModulusSpace_squarefull
~~~

This should be a short consumer of:

~~~text
GNExcessCubicRealizedLargeModulusSpace_prime_sq_dvd
~~~

Do not duplicate factorization reasoning.

---

# Part VI — parity decomposition of a represented incidence pair

For a represented pair:

~~~text
(M,S) in GNExcessCubicRealizedLargeModulusShellIncidencePairSpace X D,
~~~

set conceptually:

~~~text
r := oddPart M
d := evenPart M.
~~~

Prove the packet:

~~~text
M = r*d^2
Squarefree r
r divides d
Squarefree S
Coprime M S
Coprime r S.
~~~

Recommended theorem:

~~~text
GNExcessCubicRealizedLargeModulusShellIncidencePair_squareful_packet
~~~

Coprime r S should follow because r divides M and Coprime M S.

Also retain:

~~~text
D <= M < 2D
X+1 < M
1 <= S <= X.
~~~

Do not reprove the pair packet; consume LUNA-012.

---

# Part VII — squarefree combined Pell parameter

Define, if useful:

~~~text
GNExcessCubicPellParameter(M,S) := oddPart M * S.
~~~

A definition is optional; a local let-binding may be cleaner.

For a represented pair, prove:

~~~text
Squarefree (oddPart M * S).
~~~

Recommended theorem:

~~~text
GNExcessCubicRealizedLargeModulusShellIncidencePair_squarefree_pellParameter
~~~

Use:

- Squarefree (oddPart M),
- Squarefree S,
- Coprime (oddPart M) S,
- the standard squarefree product theorem.

Do not call this parameter simply S; ASTRA-007 showed that the parity factor
oddPart M is essential when M has odd repeated exponents such as 7^3.

Document this semantic warning.

---

# Part VIII — exact negative-Pell shell identity

This is the main LUNA-013 theorem.

For a represented pair (M,S), obtain its unique witness a.

Let:

~~~text
r := oddPart M
d := evenPart M
T := r*S
y := 2*a + 3.
~~~

Prove the exact natural-number identity:

~~~text
y^2 + 3 = 4 * T * d^2.
~~~

Equivalently:

~~~text
(2*a+3)^2 + 3
=
4 * (oddPart M * S) * (evenPart M)^2.
~~~

Recommended theorem name:

~~~text
GNExcessCubicRealizedLargeModulusShellIncidencePair_pell_identity
~~~

Proof chain should use only production facts:

1. cubic discriminant identity:
   4*F(a) = (2a+3)^2+3,
2. pair packet:
   F(a)=M*S,
3. odd/even decomposition:
   M=oddPart M * evenPart M^2,
4. ring / semiring normalization.

Do not use subtraction over Nat.

If an integer form is useful and cheap, add:

~~~text
(y : Int)^2 - 4*T*d^2 = -3.
~~~

Recommended theorem:

~~~text
..._pell_identity_int
~~~

But the Nat equality has priority.

---

# Part IX — Pell-coordinate packet

If it improves consumers, expose one theorem returning all coordinates at once.

For represented pair (M,S), prove existence of a,y,d,r,T such that:

~~~text
a is the unique shell witness
y = 2*a+3
d = evenPart M
r = oddPart M
T = r*S

M = r*d^2
Squarefree r
r divides d
Squarefree T

y^2 + 3 = 4*T*d^2

D <= M < 2D
X+1 < M
1 <= S <= X.
~~~

Recommended theorem:

~~~text
GNExcessCubicRealizedLargeModulusShellIncidencePair_pell_packet
~~~

Do not create a structure unless it materially reduces repetition.

---

# Part X — parity / positivity facts for y

For the witness coordinate:

~~~text
y = 2*a+3,
~~~

prove the cheap facts if useful:

~~~text
0 < y
y % 2 = 1
3 <= y
~~~

Since shell witnesses have a >= 1, the stronger y >= 5 is available.

These are convenience facts only.

Do not turn them into a new counting argument.

---

# Part XI — optional coprimality of y and the repeated modulus

ASTRA-007 did not formalize this, so treat it as optional.

If it follows cleanly from the existing support theorem, prove for a shell
witness:

~~~text
Nat.Coprime (2*a+3) M.
~~~

A possible route:

- any prime q dividing M satisfies q % 3 = 1, hence q != 2 and q != 3,
- q divides F(a),
- if q divides 2a+3 then q divides (2a+3)^2+3 = 4F(a),
- hence q divides 3,
- contradiction.

Do **not** spend significant time on this optional lemma.

If the proof is not short with existing APIs, defer it.

---

# Part XII — fixed-T conic fiber coordinate

Do not count solutions, but it is useful to define the exact points sharing the
combined squarefree Pell parameter.

Optional definition:

~~~text
GNExcessCubicRealizedLargeModulusShellPellParameterSpace X D
~~~

as the image of pairSpace under:

~~~text
(M,S) -> oddPart M * S.
~~~

Only add this if Parts I–IX are already clean.

If added, prove merely:

~~~text
T represented -> Squarefree T.
~~~

Do not prove a cardinality bound.

The existing Pell family warns that fixed parameters may have recurrent
solutions.

---

# Part XIII — exact connection to the classical squareful parameterization

If the square-times-cube corollary from Part IV is available, record for every
realized modulus M:

~~~text
exists u r,
  Squarefree r
  and M = u^2 * r^3.
~~~

This makes the earlier ASTRA-007 squareful-shell exponent audit mechanically
connected to the actual realized modulus object.

Again: this is only representation, not counting.

---

# Negative theorem boundaries

Do not infer:

~~~text
fixed T has O(1) solutions;
fixed S has O(1) solutions;
fixed M has O(1) solutions;
Pell equations are sparse enough for the ABC moment;
squareful parameterization alone gives a linear moment bound.
~~~

The purpose of LUNA-013 is only to expose the exact conic coordinates.

---

# What LUNA-013 is NOT

Do not attempt:

- Pell solution counting,
- a dyadic incidence estimate,
- a shell count estimate,
- a fiber count estimate,
- asymptotic squareful counting,
- paired relative-height exclusion,
- ABC quality coupling,
- any use of abc_main_axiom.

Do not introduce provider classes or research assumptions.

---

## Public import

Import the new module from DkMath.ABC immediately after:

~~~text
GNExcessCubicComplementIncidence
~~~

unless dependency order requires a nearby placement.

Do not reorder unrelated imports.

---

## Verification

At minimum run:

~~~text
lake build DkMath.ABC.GNExcessCubicSquarefulPell
lake build DkMath.ABC
~~~

Scan changed Lean files for:

~~~text
sorry
admit
new axiom
abc_main_axiom
native_decide
~~~

None may be introduced.

Audit axioms for:

- squarefree_oddPart,
- oddPart_dvd_evenPart_of_squarefull,
- squareful odd/even packet,
- realized modulus squarefull bridge,
- pair squareful packet,
- squarefree Pell parameter,
- exact Pell identity,
- Pell packet.

Expected trust boundary:

~~~text
propext
Classical.choice
Quot.sound
~~~

or a subset.

---

## Deliverable

Create:

~~~text
lean/dk_math/docs/dev/ABC-GN-Astra-260906-v0/report-013.md
~~~

Title:

~~~text
# LUNA-013 — squareful parity / Pell-shell coordinates
~~~

Do **not** include branch HEAD hashes or commit hashes.

Report:

1. files changed,
2. oddPart squarefree theorem,
3. oddPart divides evenPart for squareful numbers,
4. canonical squareful odd/even packet,
5. optional square-times-cube representation status,
6. realized-modulus squarefull bridge,
7. incidence-pair squareful packet,
8. squarefree combined Pell parameter,
9. exact negative-Pell identity,
10. Pell packet,
11. optional y/modulus coprimality status,
12. optional Pell-parameter space status,
13. focused build,
14. ABC aggregator build,
15. no-placeholder / no-new-axiom result,
16. axiom audit,
17. exact remaining research frontier.

Update README / ROADMAP minimally if successful.

---

## Stop condition

Stop when every represented shell incidence pair has a production theorem
placing it into the exact conic form:

~~~text
M = r*d^2

r = oddPart M
d = evenPart M

Squarefree r
r divides d

T = r*S
Squarefree T

(2*a+3)^2 + 3 = 4*T*d^2.
~~~

Do not count such points.

After LUNA-013 the same research frontier should have two exact equivalent
coordinate views available:

~~~text
finite lattice:
  M*S = a^2+3*a+3

negative-Pell shell:
  y^2 + 3 = 4*T*d^2
~~~

with all parity/squarefree data carried explicitly.

That is the final purpose of this checkpoint.
