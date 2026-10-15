# Gate 001 — Kummer source audit

Outcome: **B accepted** ([review](review-001.md)). FLT7 OPEN.
Source indexed details: [17-row matrix](bridge-matrix-001.md).

## Findings

- The seventh cyclotomic ring of integers is PID and has class number one;
  its explicit six-degree model and ring equivalence already exist in
  `DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicSevenPID.lean`,
  `SevenRamifiedFusionCyclotomicDegreeSixPID.lean` and CM unit modules.
- Principalization `(a)=I^7 → a=u*b^7` is present; it does **not**
  make `u` an arbitrary seventh power.
- The constructed chosen-factor packet already proves scalar congruence,
  exact quotient power `Q=gamma^7`, and
  `L=ramifiedUniformizer*gamma^7`. There is no missing chosen-unit
  extraction in this fixed route.
- Anthropic's Case II moves **all** cyclotomic integer variables and
  carries a unit while reducing a ramifier exponent. The old DkMath
  `q`-peel asks for a natural-number root with other coordinates fixed:
  these are not directly interchangeable.
- Old `CyclotomicPrincipalizationNonFirstCasePeelDescentExistenceCore_of_classGroupPTorsionFree`
  retains a `sorry`; legacy top-level routes relying on it are not
  independent proofs. A separate conditional regular-prime theorem
  requires explicit unproved target inputs.
- `CyclotomicIdealPthPowerTarget` is vacuous (`True`).
  `CyclotomicClassGroupPTorsionFreeTarget` is over-quantified across
  all rings/exponents. Neither is an acceptable new consumer.

## Trust and next step

49 declarations were probed locally at Gate 001. Chosen-factor and PID
routes checked in the audit have standard axiom sets and no direct
`sorryAx` dependency; the legacy peel/FLT routes above do contain
`sorryAx`. This is a statement about those declarations, not their
entire imports or a full CI run.

Gate 002 was subsequently completed (see [report-002.md](report-002.md)),
proving the congruence-restricted unit proposition in the concrete ring.
It does **not** produce the next descent state.

Reference sources are only GitHub repository paths and the fixed
[Anthropic commit](https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2).
Temporary source copies and raw build/probe logs are not retained in Git.
