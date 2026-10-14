# Instruction 006 — GTail FLT7 arithmetic constraint and descent-frontier audit

Date: 2026-10-09
Target branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Working directory: `lean/dk_math`
Prerequisites: `review-005.md` and `report-005.md`
Scope: **Step 006 only. Stop before Step 007 façade/merge.**

## Mission

Investigate whether the proven **selective GTail factor and transport identities**, once attached to a hypothetical primitive exponent-seven Fermat equation, produce arithmetic information **beyond a mere polynomial restatement**.

Build a small checked arithmetic receiver/audit, with explicit witnesses and precise premises, without importing the entire FLT7 research façade or assuming a nonexistent unconditional FLT7 theorem.

Distinguish four types of findings:

1. **A genuine independent neutral lemma**, valid on satisfiable, non-FLT inputs;
2. **A conditional FLT7 necessary condition**, which can be true vacuously in ℕ and must have a transparent noncircular proof route;
3. **An already-known necessary condition**, recovered through the new GTail lens (not a new FLT7 obstruction);
4. **An unproved transport/reconstruction obstruction**, not to be encoded as a supplied axiom or witness.

The target is a usable research map, not forced Outcome A.

## Phase 0 — source and duplication audit

Inspect exact signatures in:

- `DkMath/FLT/Seven/GTailBridge.lean` and `Basic.lean`.
- `DkMath/Lib/Cosmic/GTailSeven.lean`, `GTailBoundary.lean`, `GTailCongruence.lean`, and `GTailPadic.lean`.
- Existing FLT7 `CounterexampleRouting.lean`, `ModSevenSectors.lean` and `DescentClosureAudit.lean`; **do not import these heavy owners unless a required theorem absolutely cannot be obtained by small neutral dependencies**.
- Existing `DkMath.Lib.NumberTheory.EisensteinCoordinates` and `DkMath.NumberTheory.TraceOneQuadratic` for norm sign conventions; only inspect, do not identify the new quadratic with a norm map without a typed bridge.
- The `GTailSelection/Factor/Transport` result families and reports 001–005.

Create `source-inventory-006.md` mapping each candidate against existing theorem(s): **new / new route to known fact / already available / failed hypothesis / unproved**. Record exact import closures and any potential dependency cycle before creating new files.

## Phase 1 — positive focused-gap certificate (mandatory)

Under positive `a,b,c : ℕ` and `Fermat7Equation a b c`, prove in a transparent proof chain:

```text
max a b < c
c < a+b
there exists g : ℕ with c+g=a+b and 0<g
for such g, g<a and g<b
```

Choose a minimal set of theorem endpoints rather than excessive wrappers. Reuse the Step 005 `gtail_seven_shell` / Step 004 `add_pow_seven_eq_gap_add_interior` for `c<a+b` if feasible, with the positivity of the interior factor `7*a*b*(a+b)*Q²` explicitly discharged. (The simpler integer/strict-power algebra may be used if leaner, but record if the shell actually added content.)

For `c>max(a,b)` prove strict positivity of the added seventh power and use a legitimate `Nat.pow_lt_pow_iff_left` / positive power monotonicity; avoid assuming it.

A canonical focused coordinate is `g=a+b-c`. In ℕ, use `Nat.sub_add_cancel` or `Nat.add_sub_of_le` only after `c≤a+b` is established. Prove a concrete theorem equivalent to:

```text
∃ g : ℕ, 0<g ∧ g<a ∧ g<b ∧ c+g=a+b
```

Optionally supply a packet adapter; the arithmetic theorem should not *require* `CounterexamplePack` if positivity plus equation suffice.

**Important:** `g<min(a,b)` is only a smaller **number**, not yet a smaller `CounterexamplePack` or an infinite-descent provider.

## Phase 2 — prime-seven divisibility checkpoint (mandatory)

Derive, using the **GTail bridge** `gtail_seven_eq_of_fermat7Equation` and the neutral congruence `prime_dvd_GN_iff_dvd_gap`:

```text
(hEq : Fermat7Equation a b c)
(hsum : a+b=c+g)
⊢ 7 ∣ g
```

Suggested proof shape: the bridge RHS is a multiple of 7, hence `7∣g*GTail 7 1 g c`. By primality, either `7∣g` or `7∣GTail 7 1 g c`; the latter implies `7∣g` by the existing neutral prime-row address theorem. **Do not assume `Coprime g c`.**

Audit against the existing `fermat7Equation_modSeven_linear`: this is a **known mod-7 necessary condition in a new GTail route**, not an independent obstruction. Record both facts in `report-006.md`. Avoid importing `ModSevenSectors` merely to prove equivalence if doing so expands the build closure; a source-signature comparison suffices.

Provide an independent semiring/ℕ prime-row divisibility test **without any Fermat hypothesis**, and an example where `7∤g` to confirm the relation is not unconditional.

## Phase 3 — primitive quadratic-factor coprimality (research target)

Let `Q(a,b)=a²+a*b+b²` over naturals. Under `Nat.Coprime a b`, investigate and, if practical, kernel-check neutral lemmas such as:

```text
Nat.Coprime a (Q a b)
Nat.Coprime b (Q a b)
Nat.Coprime (a+b) (Q a b)
Nat.Coprime (a*b*(a+b)) (Q a b)
```

These are statements about ordinary *satisfiable* coprime pairs, and can localize primes dividing the square factor in the Step 005 bridge.

Proof sketch / sanity audit:
`Q mod a = b²`; `Q mod b = a²`; `Q mod (a+b) = a²` (because b ≡ -a modulo a+b).
Use existing Nat coprime/add/sub/divisibility lemmas or pass through ℤ congruence explicitly. Do not assert `Coprime g c` or `Coprime g Q` from `Coprime a b` — neither follows simply from the coordinate relation.

If genuine neutral content emerges, place it in a narrow `DkMath.Lib.Cosmic.` arithmetic add-on (e.g. `GTailSevenArithmetic.lean`) or appropriate existing neutral module. Otherwise keep exploratory FLT7-facing lemmas in `DkMath/FLT/Seven/GTailConstraintAudit.lean` and document what was not established. Avoid duplicating already existing Eisenstein norm/coprimality theorems.

## Phase 4 — valuation / factor allocation audit (exploratory, after Phases 1–3)

Using:

```text
g * GTail 7 1 g c = 7*a*b*(a+b)*Q(a,b)^2
```

and any proved coprimality, ask for a **strictly stronger local statement** than `7∣g`:

- At q=7: can existing `GTailPadic` / congruence control valuations of `GTail 7 1 g c` mod 49, under explicit `7∣g` and `¬7∣c`?
- For a prime `q∣Q(a,b)` with `q∤7*a*b*(a+b)`, which factors on the left carry the required square valuation? Do not infer `q²∣g` or `q²∣GTail` separately unless justified by an actual gcd/valuation split.
- Is `Nat.Coprime g c` ever derivable from existing admissible hypotheses? If not, identify the missing assumption and do not apply `gcd_GN_eq_gcd_of_one_le`.
- If a candidate arithmetic constraint is merely standard mod-7 reduction or follows from a known named FLT7 theorem, classify it as a *recovered condition*, not a novelty.

Prove one small additional lemma if it is materially useful and has a manageable, honest proof. Otherwise produce a **precise obstruction ledger** with typed proposed statements, evidence and counterexamples/failed assumptions. Do not force an immense p-adic or ideal-class implementation.

## Phase 5 — no descent without reconstruction

Audit any attempted descent in the light of `DkMath.FLT.Seven.DescentClosureAudit.AwayDescentClosureProvider`. A smaller positive g does **not** supply:

```text
∃ a' b' c', CounterexamplePack a' b' c' ∧ measure(a',b',c') < measure(a,b,c)
```

No universal next-packet field may be introduced to pretend such a provider exists. Clearly record exactly what additional conservation, divisibility, root/unit, or norm information would be needed to construct and prove a next packet.

Compare this frontier with the present normalization-fixed unit-power gauge obstacle, without claiming the simple quadratic norm-shaped polynomial closes the cyclotomic unit class.

## Implementation / validation

Suggested new focused owner:

- `DkMath/FLT/Seven/GTailConstraintAudit.lean`
- `DkMathTest/FLT/Seven/GTailConstraintAudit.lean`

Optional narrow neutral arithmetic module **only if** genuine general-purpose lemmas are implemented and source overlap ruled out:

- `DkMath/Lib/Cosmic/GTailSevenArithmetic.lean`

Required docs:

- `source-inventory-006.md`
- `constraint-ledger-006.md`: a compact table of each candidate statement, exact hypotheses/carrier, proven/deferred/refuted, source proof route, known-vs-new classification and smallest blocker.
- `report-006.md` with exact theorem signatures, changed paths, proof dependencies, commands, axiom lists and limitations.
- Update `ROADMAP.md` truthfully.

Build *only targets actually created* (do not introduce nonexistent paths):

```text
lake build DkMath.FLT.Seven.GTailConstraintAudit
lake build DkMathTest.FLT.Seven.GTailConstraintAudit
lake build DkMath.FLT.Seven.GTailBridge DkMathTest.FLT.Seven.GTailBridge
```

Plus optional neutral arithmetic target if added. Sequential focused builds; avoid a clean all-workspace build.

Check `#print axioms` on each public endpoint; no `sorry`/`admit`/new `axiom`/`unsafe`, no circular invocation of FLT7 impossibility, `exfalso` or `False.elim` to discharge the counterexample-based arithmetic goals. The proof audit must distinguish ordinary conditional consequences from constructive FLT7 closure; direct source proof and nonvacuous neutral regressions are more informative than an axiom list alone.

## Classification and stop

- **A:** a genuinely additional, noncircular and clearly identified arithmetic necessary condition beyond the known mod-7/height restatements is obtained and compared to earlier FLT7 sources. Do not label it FLT7 closure.
- **B:** useful focus/coprimality/prime-address lemmas and an honest remaining-obstruction ledger; no stronger FLT7 contradiction.
- **C:** a planned transport/valuation/gcd invariant fails without missing hypotheses; record exact counterexample or repaired assumptions.

**STOP after Instruction 006.** Do not perform Step 007 façade/whole build, modify unrelated FLT7 owners, merge into develop, search the enormous external proof corpus or claim Fermat 7 is closed.
