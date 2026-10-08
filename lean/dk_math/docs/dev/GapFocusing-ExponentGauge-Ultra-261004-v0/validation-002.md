# Instruction 002 — Validation

2026-10-04。実行 cwd: `/home/deskuma/develop/lean/dkmath/lean/dk_math`。
Lean / Mathlib `v4.34.1`。
数学的結論は [report-002](report-002.md)、履歴は [findings-002](findings-002.md)。

## 最終 focused build

```sh
lake build DkMath.NumberTheory.GapFocusing \
  DkMathTest.GapFocusingSupport \
  DkMathTest.Lib.Algebra.PowerSubgroup \
  DkMathTest.NumberTheory.GapFocusingSuccessorCalibration \
  DkMathTest.NumberTheory.GapFocusingSuccessorAxiomAudit \
  DkMathTest.NumberTheory.GapFocusingCalibration \
  DkMathTest.NumberTheory.GapFocusingAxiomAudit
```

exit 0、`Build completed successfully (2828 jobs)`。
新規 regression/audit 4 module と Instruction 001 の既存 2 module を含む。
この実行に warning/error はない。
ログ: [build-successor-focused-002](evidence/MANIFEST.md#log-40e5a909c6fcf4a1)。

## public facades

```sh
lake build DkMath.Lib DkMath
```

exit 0、`Build completed successfully (10360 jobs)`。
これは依存を含む Lake job 数であり、変更ファイル数ではない。
上の focused 実行と合わせて `GapFocusing`, `Lib`, `DkMath` の三つの
public facades が通った。
ログ: [build-facades-002](evidence/MANIFEST.md#log-6e0c314267def892)。

この全体実行では、今回変更していない次の既存 warning が再表示された。

| ファイル | 行 | warning |
| --- | ---: | --- |
| `DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean` | 147 | declaration uses `sorry` |
| `DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean` | 4187 | declaration uses `sorry` |
| `DkMath/NumberTheory/GcdNextResearch.lean` | 850 | declaration uses `sorry` |
| `DkMath/FLT/Kummer/CyclotomicPrincipalization.lean` | 5389 | declaration uses `sorry` |
| `DkMath/CosmicFormula/TriominoFLT.lean` | 1919 | declaration uses `sorry` |

したがって repository 全体が admission-free という報告ではない。
今回の新規宣言の依存公理は別に全件検査している。

## Primitive-prime source/check audit

```sh
lake env lean \
  docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/checks/PrimitivePrimeAudit002.lean
```

exit 0。
ログ: [primitive-prime-audit-002](evidence/MANIFEST.md#log-3047c463082a0fd0)。
五つの新規 regression と 13 の既存 endpoint、計 18 宣言を個別に監査した。
五つの新規命題と 11 の既存 safe endpoint は標準公理だけ。
二つの既存 research endpoint については、意図的に `sorryAx` 境界を確認した。

```text
DkMath.NumberTheory.GcdNext.squarefree_implies_padic_val_le_one_research
DkMath.NumberTheory.PrimitiveBeam.primitive_prime_obstructs_GN_perfect_power_research
```

これらは新規 successor 宣言の依存として使っていない。
一般 Zsigmondy 宣言の検索、既存型の仮定、valuation/no-lift の境界は
[primitive-prime-audit-002](primitive-prime-audit-002.md) に記録した。

## 新規宣言の全件監査と source scan

[GapFocusingSuccessorAxiomAudit](../../../DkMathTest/NumberTheory/GapFocusingSuccessorAxiomAudit.lean)
は五つの新規 production module にある **58 宣言**をすべて
`#print axioms` で指定する。
新規 test/check の **12 名前付き宣言**もそれぞれのファイル内で指定した。
source から取得した宣言名をログ内の実際の出力に突き合わせ、漏れがなく、
各依存集合が `{propext, Classical.choice, Quot.sound}` の部分集合であることを
確認した。空の依存集合も許容した。さらに **16 anonymous examples** が
上記 regression builds で kernel-checked になった。

**新規 Lean 10 ファイル**（production 5、test 4、文書内 check 1）全体の
`sorry`, `sorryAx`, `admit`, `axiom`, `native_decide`, `unsafe` token scan は
zero matches。`#print axioms` は検査コマンドであり、axiom 宣言ではない。
機械集計: [source-dependency-audit-002](evidence/MANIFEST.md#log-868ca85d0030b29c)。

回帰対象は、零次数、非原始座標、負座標、零因子係数環、隣接から全履歴への
誤った強化、非互いに素な intersection 式、非自明な整数単数 square class。
構造 fields に結論を仮定する形で CRT を作ってはいない。

## 差分検査

`git diff --check` は exit 0。新規ファイルにも末尾空白・行末空白がないことを
別途検査した。記録: [diff-check-002](evidence/MANIFEST.md#log-dd0fb985b815acce)。
既存 tracked source の変更は `DkMath/Lib.lean` と
`DkMath/NumberTheory/GapFocusing.lean` の import/facade documentation。
新規五つの production file が実質的な数学の追加である。
