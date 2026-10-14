# instruction-001 — Codex workspace audit: DkMath × Anthropic Kummer

Date: 2026-10-15  
Branch: `research/FLT7-Kummer-Anthropic-Bridge-261015-v0`  
Gate: **001 (research/source audit only; no production Lean modifications)**  
Document path (from repository root): `lean/dk_math/docs/dev/FLT7-Kummer-Anthropic-Bridge-261015-v0/instruction-001.md`

## Auftrag / mission

Study the **actual checked-out DkMath Git repository workspace** (not just this note), comparing
it against the Kummer regular-prime construction in Anthropic
`P2M/Sol/S_flt_regular.lean`. Locate *existing* theorems, explicitly classify
missing bridges, and propose the minimum testable Lean implementation for Gate
002 onward. We want new mathematical constraints, not a trivial proof by
importing an already completed FLT theorem.

Do not claim a theorem merely from its identifier or a comment. Distinguish
(a) `def ... : Prop` declarations, (b) proved/axiom-free lemmas,
(c) proved implications conditional on an unconstructed packet/target,
(d) `sorry`-dependent results, and (e) merely analogous mathematics.

## 0. Repository safety and baseline

1. Read root `AGENT.md`, this folder's `README.md` and `ROADMAP.md`.
2. `git status --short`, `git branch --show-current`, `git rev-parse HEAD`,
   `git log -1 --format=fuller`. Confirm this research branch exists locally.
   If not, fetch and switch; **do not discard any dirty workspace changes**.
3. All research documents in this task live under `lean/dk_math/docs/dev/FLT7-Kummer-Anthropic-Bridge-261015-v0/` relative to repository root. From the Lean project root (`cd lean/dk_math`), this is `docs/dev/FLT7-Kummer-Anthropic-Bridge-261015-v0/`. Never write this task's files under repository-root `docs/dev`.
4. Report exact `lean-toolchain`, `lakefile.toml`, Mathlib revision (if resolvable),
   whether compilation artifacts are present, and difference from upstream
   reference versions.
5. Before coding, record the current proven FLT7 frontier from this branch,
   especially GTail STOP042, Kummer peel, and any newer Mod42 work.

Suggested non-destructive commands:

```bash
git status --short
git branch --show-current
rg -n "Kummer|[Rr]egular[Pp]rime|ClassGroup|[Uu]nit|[Pp]eel" lean/dk_math/DkMath/FLT/Kummer lean/dk_math/DkMath/FLT/Seven lean/dk_math/DkMath/Lib/NumberTheory
rg -n "sorry|admit|^axiom\\b|\bTrue\b" lean/dk_math/DkMath/FLT/Kummer
rg -n "DegreeSixKummerUnitLemmaAtSeven|CyclotomicClassGroupPTorsionFreeTarget|CyclotomicIdealPthPowerTarget|NonFirstCasePeelNormalFormDescentTarget" lean/dk_math/DkMath
```

## 1. Anthropic source — read the proof, not only the documentation

Pinned reference commit:
https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2

Read `PROOF-PATH.md`, `ATTRIBUTION.md`, and these code portions:

| Source                                               | Approx. lines at reference commit | Question                                           |
| ---------------------------------------------------- | --------------------------------- | -------------------------------------------------- |
| `P2M/Sol/S_flt_regular.lean`                         | 48–90                             | regular prime and class-group principalization     |
| same                                                 | 278–515; 1193–1330                | coprime cyclotomic ideals and Case I               |
| same                                                 | 749–954                           | cyclotomic unit/conjugation lemmas                 |
| same                                                 | 2730–3290                         | Kummer extension, Hilbert94, unit `p`-th power     |
| same                                                 | 3448–4037                         | Case II factorization and descent construction     |
| same                                                 | 4084–4245                         | strict descent contradiction, case split, endpoint |
| `P2M/Sol/S_fermatLastTheoremSeven.lean`              | entire short file                 | PID -> class number 1 -> `flt_regular`             |
| `Theorems/Thm_flt_regular.lean`                      | entire file                       | exact generic signature                            |
| `P2M/Sol/S_IsCyclotomicExtension_Rat_seven_pid.lean` | main theorem                      | what was proved about the seven-cyclotomic ring    |

Reference source is external: no importing the completed FLT7 theorem;
no wholesale transplantation of ~4,200 lines. Note flt-regular
porting/Apache-2.0 attribution if any proofs are adapted.

Key comparison theorem (unfold exact type in upstream):
`FltRegular.KummersLemma.eq_pow_prime_of_unit_of_congruent`.
Given regularity and `p` odd, a unit congruent to an integer modulo `p`
becomes a `p`-th power. **Check the precise coercions/units, not just prose.**

## 2. DkMath — verify the concrete theorem surface

Inventory exact `#check`/types/imports (include fully qualified identifiers):

- `DkMath/FLT/Kummer/{Basic,GapDivisibleBranch,CyclotomicPrincipalization,ClassGroupBridge,RegularPrimeRoute}.lean`.
- `DkMath/Lib/NumberTheory/{IdealPowerFactor,PrincipalIdealPower,ClassGroupTorsionBridge,UnitPowerSector}.lean`.
- `DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicSevenPID.lean`,
  `SevenRamifiedFusionCyclotomicDegreeSixPID.lean`.
- `PrimeTraceOneDirectCyclotomic{ChosenTail,UnitCongruence,CMTorsionPhase}.lean`.
- `PrimeTraceOneDirectRealCubicCommonPrimeKummer.lean`,
  `PrimeTraceOneCyclotomicPidBypassAudit.lean`.
- Relevant `GTail*`, CounterexamplePack, `SevenRamifiedFusion*`, and
  other source modules discovered via dependency search.

Inspect **proof bodies** and `#print axioms` where feasible. Record whether
`SevenCyclotomicDegreeSixInt.Ring` is connected by a genuine ring equivalence
to `𝓞 (CyclotomicField 7 ℚ)`, which conversions already exist, and whether
`sevenIdeal` corresponds to `Ideal.span {(7 : _)}`.

Crucial: `DegreeSixKummerUnitLemmaAtSeven` is a **Prop specification** at
`PrimeTraceOneDirectCyclotomicUnitCongruence.lean`, not by itself proved.
For any asserted closure, identify its proof term and its dependencies.
The old Kummer peel-existence core contains `sorry`; determine if a proposed
consumer actually reaches it and distinguish unrelated imports. Test
`CyclotomicClassGroupPTorsionFreeTarget` and
`CyclotomicIdealPthPowerTarget` for overstrong/vacuous definitions before
recommending anything built on them.

## 3. Reconciliation required (do not conflate branches)

Produce a numbered bridge matrix with, for each row:

- Anthropic exact statement and source file:line.
- DkMath exact statement and source file:line.
- Carrier/ring equivalence and boundary `p=7` conditions.
- Hypotheses the Anthropic proof needs but DkMath does/does not supply.
- Equivalence status: exact / specializable / partial / incompatible / absent.
- Whether DkMath already proves a stronger *restricted chosen packet* theorem.
- Confidence grounded in typechecking vs source reading only.
- Smallest new lemma signature and where it belongs.
- Dependency provenance and any `sorry`/nonstandard axiom exposures.

Specific priorities:

**P0**: PID and class number=1 transport for `p=7`; unit congruence ->
unit seventh power. Compare the upstream `eq_pow_prime_of_unit_of_congruent`
and local `DegreeSixKummerUnitLemmaAtSeven`. Check that the integer
congruence condition is actually constructed from the chosen-factor packet.

**P1**: separate ideal seventh-power extraction from unit absorption;
compare the chosen linear factor theorem, including its ramifier `π` and
orientation assumptions. Explicitly distinguish `a = u*b^7` and `a=b^7`.

**P2**: compare Anthropic case I/II (`7 | a*b*c`) and DkMath's Gap
branch (`q | z-y`), explain any valid permutation/sign/valuation transport.

**P3**: match strict descent measure in upstream Case II
`m+1 -> m` to DkMath's `Peel` target. If only a hypothetical smaller
counterexample is specified, exhibit the *missing construction* instead
of calling it a proof. Consider whether the two measures are fundamentally
different; never invent a map.

## 4. Required Gate-001 artifacts

Write in **this directory**:

1. `bridge-matrix-001.md`: full source-indexed table and concise candidate
   Lean theorem signatures (code fences).
2. `report-001.md`: source and branch hashes, findings, P0/P1/P2/P3,
   exact status A/B/C, pending obligations, and a concrete implementation
   proposal for instruction-002 (<=3 tightly scoped lemmas).
3. Optional `evidence/001-*.txt` or a small `DkMathTest` scratch probe
   ONLY if needed for `#check` / `#print axioms`; if a Lean file is added,
   keep it opt-in and avoid production imports.

Gate 001 is **audit first**. Do not edit or rewrite production proof files.
No commit, push, PR or merge in this gate; deliver the changes for review. If Lean build is too expensive or unavailable,
record source-only conclusions separately and do not mark kernel accepted.

## 5. Acceptance and reporting

- Give the exact proposed theorem statement, including `Ring`, `K`,
  `p=7`, `u : Rˣ`, `Ideal` and mod-7 congruence hypotheses.
- Cite all source statements by `path:line`; note version drift.
- No new `sorry`, `admit`, `axiom`, vacuous `True` goal, or circular
  import of Anthropic's finished theorem.
- Do not claim a general unit-surjectivity result:
  `∀ u : Rˣ, ∃ v, u=v^7` is stronger than Kummer's *congruence-constrained*
  lemma and is generally false.
- At finish, report whether Gate 002 is ready, blocked by a concrete
  hypothesis, or needs corrected mathematical scope. Keep FLT7 OPEN unless
  an independent contradiction has actually been kernel checked.
