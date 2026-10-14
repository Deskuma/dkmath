# Gate 010 verification summary

Provenance: **Codex-reported**, locally executed 2026-10-13; not independently reproduced.
Environment: Lean4.34.1 /Lake5.0.0-src+5045d00. Cwd: `lean/dk_math`.

- `lake build DkMath.FLT.Seven.SevenRamifiedFusionParametricMixedExclusion`: exit **0**.
- `lake env lean DkMathTest/FLT/Seven/SevenRamifiedFusionParametricMixedExclusion.lean`: exit **0**, no warning/error.

```text
Build completed successfully (9091 jobs).
```

Actual test/axiom output:

```text
file: DkMathTest.FLT.Seven.SevenRamifiedFusionParametricMixedExclusion
'DkMath.FLT.Seven.sixthPowerSieved_two_times_complement_excluded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DkMath.FLT.Seven.sixthPowerSieved_bounded_mixed_family_excluded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

The free-s theorem uses exactly s≡1 mod42, s≡4 mod5, 2s<343*5^7. Membership+size and residue-derived nondivisibility leave r1/2, eliminated by existing same-divisor mod42/mod5 consumers.
Tests prove the exact size-window iff k≤63799, endpoint26796758<threshold26796875, failure of that criterion at63800, identity at22982 with9653618, and63800 distinct image cores using injectivity/cardinality lemmas. Cheap passage is reused at the known single member only.
No infinite family or source-packet existence/global FLT7 conclusion.

Checked source SHA-256:

```text
d3abddb9a25100b4848a94248edee8e0c5ad837bca45b51f476d601cae30a5c5  DkMath/FLT/Seven/SevenRamifiedFusionParametricMixedExclusion.lean
fe53c9acb852c14cc7192600efc7ded797a9c2ba7f60b2836510a24bcafc7230  DkMathTest/FLT/Seven/SevenRamifiedFusionParametricMixedExclusion.lean
```

Full API / proof / bounds: [report-010.md](../report-010.md). Raw logs remain disposable. No Git mutation.
