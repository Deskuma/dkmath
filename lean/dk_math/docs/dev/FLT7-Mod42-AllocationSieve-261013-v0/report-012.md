# report-012 — generic prime-power primitive-divisor obstruction

**Outcome A**: 任意の素数pのprimitive divisor分類、residue-conditional full-sieve排除、独立したp223,n2の具体例をLeanで検証。

## Exact APIs

Module: `DkMath.FLT.Seven.SevenRamifiedFusionPrimePowerPrimitiveExclusion`。

```lean
namespace DkMath.FLT.Seven

theorem eligible_primitive_divisor_two_prime_pow {p n r : ℕ}
    (hp : Nat.Prime p)
    (hmem : r ∈ (2 * p ^ n).divisors)
    (hcop : Nat.Coprime r ((2 * p ^ n) / r))
    (hsize : 7 ^ 3 * r ^ 7 < 2 * p ^ n) : r = 1 ∨ r = 2

theorem sixthPowerSieved_two_prime_pow_excluded {p n : ℕ}
    (hp : Nat.Prime p)
    (h42 : Nat.ModEq 42 (p ^ n) 1)
    (h5 : Nat.ModEq 5 (p ^ n) 4) :
    ¬ SixthPowerSievedNestedCondition (2 * p ^ n)
```

n0も含む。p/n/Mのglobal上限なし。Residuesは明示的な仮定であり、全素数・全指数の合同式とは主張しない。

## Structural proof separated from residues

actual divisor membershipからr>0、r∣M、r*t=M（t=M/r）を得る。p∤rならprimalityによりCoprime r p^n、Euclidからr∣2。p∣rならactual hcopによりp∤t、Coprime t p^n、t∣MからEuclidでt∣2。よってM=r*t≤2*r。r≤r^7と既存 coarse size343*r^7<Mに矛盾する。

これは単なる13 theoremの名前変更ではなく、素数性だけを使うfactor ownership theorem。既存Nat.Prime.coprime_iff_not_dvd、Coprime.pow_right、Coprime.dvd_mul_right、dvd_primeを再利用。旧13 theoremは変更していない。

Full-sieveの実際のhmem/hcop/hsizeで分類した同じrを使う。r1ではh42の2倍がM≡2 mod42を与え、membership由来のdivisor guardと既存mod42 consumerを使う。r2ではM/2=p^n≡4=2² mod5と5∤2で既存same-r mod5 consumerを使う。Exact branch disjunctionを保持する。receiver emptinessを仮定として再包装していない。

Direct production imports: GeneralGapModFiveImage、ModFortyTwoAllocationSieve、SixthPowerAllocationSieve。DkMathTest importなし。先行source・receiver定義を改変していない。

## Checked regressions and limits

Tests specialize the generic result to13^(6+4*k), reusing only the small base-residue calculations from gate011 rather than its whole structural proof.

独立した具体例はNat.Prime223、223²≡1 mod42、223²≡4 mod5、2*223²=99458をLeanで確認し、generic theoremから `¬ SixthPowerSievedNestedCondition 99458` を得た。r2が実際に99458のdivisorで、quotientとcoprime、343*2^7<99458も証明した。単なるsize-vacuous例ではない。Eligibilityからexact receiverや独立sixth-power witnessは推論していない。

Coprimality guardを外す診断は既存gate011のr13,n10 countermodelをそのまま再利用した。

さらにs=3*5^10、r3の診断でmembership、actual quotient coprimality、coarse size、r≠1/2を確認。二つの異なるprime basesのwhole powersを左右に割り振れるので、generic prime-power分類を多素因子compositeへ無条件に拡張できない。これはexact receiverの存在モデルではない。

Actual packet realization、gate005のsame-packet chart link、任意Mのreceiver emptiness、FLT7 closureは今回の結論に含まれない。

## Validation and repairs

Date2026-10-13; cwd `lean/dk_math`; Lean4.34.1 / Lake5.0.0-src+5045d00。

Actual-source target-name duplicate searchは一致なし。Index refresh exit0:1,813files /29,292declarations。

| Command | Exit | Result |
| --- | --- | --- |
| `lake build DkMath.FLT.Seven.SevenRamifiedFusionPrimePowerPrimitiveExclusion` first / second | 1 / 1 | variable shadowingとquotient下のcommuting simpの問題 |
| same final build | 0 | `Build completed successfully (9091 jobs).` |
| `lake build DkMathTest.FLT.Seven.SevenRamifiedFusionThirteenPowerPrimitiveExclusion` | 0 | reused countermodel test dependency |
| `lake env lean DkMathTest/FLT/Seven/SevenRamifiedFusionPrimePowerPrimitiveExclusion.lean` first | 1 | direct decide on primality223 reached maxRecDepth |
| same final test | 0 | generic applications /13 family /223 example / eligibility / countermodels / audits; no warning/error |

Prime hypothesisとdivisibility branch variableを区別し、actual factor equalityからt-divisibilityとM≤2rを明示した。223のprime certificateはnorm_numに変更した。数学的仮定やtargetを変えず、resource limit増加もしていない。9091jobsはdependencies込み。

Actual axiom audit:

```text
'DkMath.FLT.Seven.eligible_primitive_divisor_two_prime_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.FLT.Seven.sixthPowerSieved_two_prime_pow_excluded' depends on axioms: [propext, Classical.choice, Quot.sound]
```

両exportsは標準 `[propext, Classical.choice, Quot.sound]` のみ。sorryAx / fresh axiomなし。

## Records / next question

Added under lean/dk_math:

- `DkMath/FLT/Seven/SevenRamifiedFusionPrimePowerPrimitiveExclusion.lean` (twoexports)。
- `DkMathTest/FLT/Seven/SevenRamifiedFusionPrimePowerPrimitiveExclusion.lean`。
- `docs/dev/FLT7-Mod42-AllocationSieve-261013-v0/findings-012.md`。
- Same folder `report-012.md`, `evidence/012-verification-summary.md`。

Compact evidence is Codex-reported, not independently rerun. Raw logs stay transient and ignored. Existing modules/README/ROADMAP unchanged.

Next single question (not implemented): when s contains two distinct prime-power factors, which whole-factor allocations remain after the same modular consumers? The checked composite diagnostic shows that a new divisor-cover argument is required; prime-power ownership cannot simply be reused as r1/r2 classification.

gate012 stops here. No staging/commit/push/branch/PR/merge or later gate work.
