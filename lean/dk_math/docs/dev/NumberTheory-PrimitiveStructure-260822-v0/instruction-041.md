# PRIM-L026 — Centered/Packet Diamond Obstruction Lean Judgment

Date: 2026-08-25
Branch: `wip/number-theory-primitive-structure-260822-v2`
Toolchain: keep the repository pinned at Lean / Mathlib v4.32.2. Do not upgrade.

## 0. Purpose

PRIM-L025 is accepted as **Outcome B — PROVED TRIANGLE STRUCTURAL REFINEMENT**.

Lean has proved that, at anchor `n = 4*k` with `0 < k` and prime `4*k+1`, the three seats

```text
A = 2*k
B = 2*k+1
C = 6*k+1
```

have pairwise-coprime complete square points, pairwise-disjoint old-prime supports, and therefore three pairwise-distinct old-prime witnesses under `SquareOffsetsFullyCovered (4*k)`.

The next checkpoint must stay in **Lean-judgment mode**. Do not start a generic graph/coloring framework and do not perform another report-only reconnaissance.

Test the smallest natural four-seat extension by adding

```text
D = 6*k+2.
```

The intended geometry is

```text
A --1-- B ----4*k---- C --1-- D
|        |                     |
|        +------4*k+1----------+
+-------------4*k+1------------ C
```

More explicitly:

```text
A/B : consecutive
B/C : existing packet pair
A/C : existing centered/prime-gap pair
C/D : consecutive
B/D : gap 4*k+1
A/D : gap 4*k+2 = 2*(2*k+1)
```

The key question is not merely whether four seats can be listed. The key question is whether the triangle can become a genuine four-way pairwise separation, and if not, whether Lean can identify the exact arithmetic obstruction.

A strong expected obstruction is that A and D are both even complete points, so prime `2` lies in both old-prime supports. Do not accept this from prose: prove it in Lean. Then push farther and determine whether every common old-prime support direction of A and D is forced into the tiny exceptional set `{2,3}`.

This checkpoint should therefore produce either:

- a genuine four-seat strengthening, if Lean finds one; or
- a Lean-certified **false beam** explaining exactly why the naive K4 extension fails.

Both are useful. Do not manufacture a four-witness theorem from pairwise inequalities that Lean has not proved.

## 1. Required source changes

Add one focused module, suggested path:

```text
DkMath/NumberTheory/Legendre/CenteredPacketDiamond.lean
```

Prefer the minimal import:

```lean
import DkMath.NumberTheory.Legendre.CenteredPacketTriangle
```

Add the module to the public facade:

```text
DkMath/NumberTheory/Legendre.lean
```

Do not modify the statements of L020, L024, or L025 merely to make this checkpoint convenient.
Do not introduce a generic graph, coloring, clique, Hall, or matching abstraction.
Do not modify Primitive semantics.

## 2. L026-1 — fourth seat shell membership

For `0 < k`, prove

```lean
SquareOffset (4*k) (6*k+2)
```

for the new seat D.

Keep the existing A/B/C membership theorems from L025; do not duplicate them.

Expected arithmetic:

```text
1 <= 6*k+2
6*k+2 <= 8*k
```

where the upper bound follows from `0 < k`.

## 3. L026-2 — consecutive pair C/D

Prove complete-point coprimality of

```text
Cpoint = (4*k)^2 + (6*k+1)
Dpoint = (4*k)^2 + (6*k+2).
```

This should be the same consecutive-number mechanism as L025 A/B:

```text
Dpoint = Cpoint + 1.
```

Reuse a general existing theorem if one is already available; otherwise keep the proof thin and local.

Expose a public theorem for the complete-point `Nat.Coprime` statement.

## 4. L026-3 — prime-gap pair B/D

Under

```lean
hprime : Nat.Prime (4*k+1)
```

attempt to prove complete-point coprimality of

```text
Bpoint = (4*k)^2 + (2*k+1)
Dpoint = (4*k)^2 + (6*k+2)
```

using

```text
Dpoint = Bpoint + (4*k+1).
```

A useful arithmetic identity to test is

```text
2 * Bpoint + (4*k+1)
  = (4*k+1) * (8*k) + 3.
```

Thus if `4*k+1` divided Bpoint, it would divide `3`. With `0 < k`, the prime `4*k+1` is at least `5`, so this should be impossible.

Do not assume this proof works. Lean must certify the theorem. If the proposed complete coprimality is false, encode a concrete counterexample and retain only the strongest true support statement.

If complete coprimality succeeds, derive B/D old-prime support disjointness using the generic L025 theorem

```lean
disjoint_squareOffsetPrimeSupport_of_coprime_points
```

rather than repeating support arithmetic.

## 5. L026-4 — A/D false beam: prime 2 really survives

Now test the edge that should fail.

For `0 < k`, prove explicitly that prime `2` lies in both supports:

```text
2 ∈ squareOffsetPrimeSupport (4*k) (2*k)
2 ∈ squareOffsetPrimeSupport (4*k) (6*k+2)
```

The complete points have factorizations of the form

```text
(4*k)^2 + 2*k     = 2 * (...)
(4*k)^2 + 6*k+2   = 2 * (...)
```

and `2 <= 4*k` follows from `0 < k`.

Then prove the actual negative structural theorem:

```text
¬ Disjoint
    (squareOffsetPrimeSupport (4*k) (2*k))
    (squareOffsetPrimeSupport (4*k) (6*k+2))
```

or an equivalent theorem that explicitly exhibits the common member `2`.

This is a required Lean-certified false beam. It demonstrates that the naive triangle-to-K4 argument is invalid.

Do not phrase this as "there cannot be four distinct witnesses"; non-disjoint supports do not imply that four distinct witnesses are impossible. They only show that pairwise-support-disjointness does not force them by this route.

## 6. L026-5 — localize all A/D common old-prime support

Push the false beam one step farther.

Attempt to prove that any actual old-prime support direction common to A and D must be `2` or `3`:

```lean
q ∈ squareOffsetPrimeSupport (4*k) (2*k) ->
q ∈ squareOffsetPrimeSupport (4*k) (6*k+2) ->
q = 2 ∨ q = 3
```

for `0 < k`.

A suggested arithmetic chain is:

1. a common divisor divides the point difference

```text
4*k+2 = 2*(2*k+1);
```

2. since `q` is prime, either `q = 2` or `q ∣ 2*k+1`;
3. if `q ∣ 2*k+1` and `q` also divides Apoint, use the identity

```text
Apoint + 3*(2*k+1)
  = (2*k+1) * (8*k) + 3
```

so `q ∣ 3`;
4. primality then forces `q = 3`.

Again, Lean decides. If the `{2,3}` localization is false, preserve the counterexample and state the exact larger obstruction set that Lean forces instead.

If the localization succeeds, expose it as a public theorem because it is a concrete arithmetic classification of the only failed edge of the four-seat configuration.

Optional, only if thin: characterize when `3` is actually common (for example by a simple congruence condition on `k`). Do not add this if it requires a new modular subsystem.

## 7. L026-6 — five good edges / one exceptional edge

Package the proved four-seat geometry without introducing graph machinery.

Under `0 < k` and `Nat.Prime (4*k+1)`, the intended true pairwise complete-point relations are:

```text
A/B coprime   -- L025
B/C coprime   -- L025
A/C coprime   -- L025
C/D coprime   -- L026
B/D coprime   -- L026
```

while A/D is deliberately not coprime because of the common factor `2`.

Expose a concise theorem/package (a conjunction is fine) containing the five true complete-point coprimality facts plus the A/D common-support obstruction.

Do not call it `K4` or add graph terminology to the public API.

## 8. L026-7 — full-cover four-seat witness package

Consume

```lean
hfull : SquareOffsetsFullyCovered (4*k)
```

for all four actual seats A, B, C, D.

Obtain witnesses `pA pB pC pD` in their corresponding actual `squareOffsetPrimeSupport` Finsets.

Using the five proved support-disjoint edges, prove all forced inequalities:

```text
pA != pB
pA != pC
pB != pC
pB != pD
pC != pD
```

Do **not** assert `pA != pD`.

If L026-5 succeeds, add the precise collision classifier:

```text
pA = pD -> pA = 2 ∨ pA = 3.
```

This is the main full-cover consumer of the checkpoint.

The theorem should show exactly what four-seat synthesis buys and exactly where it stops.

## 9. Stronger-beam judgment — mandatory Lean test

After the required theorems build, test concrete stronger statements, but only with Lean-checkable propositions.

### 9.1 Four pairwise-distinct witnesses

Do not claim that full cover forces four pairwise-distinct witnesses merely because four seats exist.
The A/D common support already invalidates the simple pairwise-disjointness proof.

If you find an independent argument that forces A and D to choose different witnesses, formalize it.
Otherwise record that no such theorem was obtained.

### 9.2 Exceptional-prime removal

Inspect whether excluding the actual common primes `{2,3}` from A/D support leaves enough support on both seats under full cover.
Do not assume it does: full cover may be witnessed solely by `2` or `3` on one of those seats.
Only formalize a strengthening if Lean can derive nonempty nonexceptional support from existing hypotheses.

### 9.3 Growing family

Do not start a generic family abstraction unless this four-seat theorem produces a concrete fifth-seat candidate with all required separation relations.
A repeated pattern visible only in prose is not enough.

The checkpoint stops after this judgment.

## 10. Outcome classification

Classify only after Lean has judged the required theorem surface.

### Outcome A — DIRECT FOUR-SEAT LEVERAGE

Use only if the fourth seat produces a genuinely stronger full-cover obligation, such as forced four distinct witnesses, a strict incidence deficit, or a reusable growth step.

### Outcome B — PROVED DIAMOND OBSTRUCTION / EXCEPTIONAL COLLISION

Use if Lean proves five separated pairs, proves the A/D collision edge is real, and localizes the collision (ideally to `{2,3}`), but no new contradiction or growing witness bound follows.

### Outcome C — NO USEFUL FOUR-SEAT REFINEMENT

Use if the extra B/D or C/D separation fails, or the A/D obstruction cannot be made more informative than the obvious parity observation.

A Lean theorem localizing all A/D common old-prime support to a finite exceptional set is normally enough to distinguish B from C.

## 11. Documentation

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
  primitive-centered-packet-diamond-lean-judgment-260825.md
```

The report must include:

- exact declarations added;
- whether B/D complete coprimality succeeded;
- the explicit Lean-certified A/D common-2 obstruction;
- whether all A/D common old-prime support was localized to `{2,3}`;
- the five-edge/four-seat theorem surface;
- the full-cover four-witness package and exact forced inequalities;
- stronger-beam judgment;
- final Outcome A/B/C;
- explicit stop boundary.

Keep module/public theorem docstrings concise and mathematical.

## 12. Validation

Run at least:

```text
lake build DkMath.NumberTheory.Legendre.CenteredPacketDiamond
lake build DkMath.NumberTheory.Legendre
git diff --check
```

Also run the existing trailing-whitespace / forbidden-placeholder audit.

Do not upgrade Mathlib. Do not perform a full repository build unless a dependency change unexpectedly requires it.

## 13. Non-goals

Do not:

- prove or claim Legendre's conjecture;
- infer four distinct witnesses from four seats without Lean proof;
- add graph-coloring/clique machinery;
- add asymptotic prime counting;
- revive Jacobsthal, quadratic-character, shell-transport, parity-wrapper, or finite-difference routes;
- weaken existing L020/L024/L025 theorem statements;
- replace implementation with another report-only checkpoint.

The essential instruction is:

```text
L025 triangle
+ fourth seat D = 6*k+2
        ↓
Lean tests two new good edges C/D and B/D
        ↓
Lean tests the bad edge A/D
        ↓
common 2 is explicit; classify any further common old primes
        ↓
full cover -> four-seat witness package with one precisely controlled collision edge
        ↓
judge whether the exceptional collision can be removed; stop if not
```
