# Instruction 003 — Validation

2026-10-04。Lean / Mathlib `v4.34.1`。
実行 cwd: `/home/deskuma/develop/lean/dkmath/lean/dk_math`。
結果: [report-003](report-003.md)。履歴: [findings-003](findings-003.md)。

## 最終 combined build

```sh
lake build DkMath.NumberTheory.GapFocusing DkMath \
  DkMathTest.NumberTheory.CyclotomicAddress \
  DkMathTest.NumberTheory.GapFocusingPrimeOrder \
  DkMathTest.NumberTheory.GapFocusingHomogeneousAddress \
  DkMathTest.NumberTheory.GapFocusingLayerValuation \
  DkMathTest.NumberTheory.GapFocusingAddressAxiomAudit \
  DkMathTest.NumberTheory.GapFocusingSuccessorCalibration \
  DkMathTest.NumberTheory.GapFocusingSuccessorAxiomAudit
```

exit 0、`Build completed successfully (10372 jobs)`。
新規 production 全五 module と新規 regression/audit 全五 module、
公開 `GapFocusing` facade、公開 `DkMath` facade、Instruction 002 の既存
calibration/audit 二 module を含む。job 数は依存も含み、変更 module 数ではない。
ログ: [build-final-003](evidence/MANIFEST.md#log-2bb204ba1e4a727b)。

最後に既存 Zsigmondy 三つの存在 endpoint の明示的な公理出力を監査へ加え、
監査 target だけを再実行した。

```sh
lake build DkMathTest.NumberTheory.GapFocusingAddressAxiomAudit
```

exit 0、`Build completed successfully (8966 jobs)`、warning/error なし。
ログ: [axiom-audit-003](evidence/MANIFEST.md#log-a94865018a7aad2f)。

## 公理出力の完全な coverage

[GapFocusingAddressAxiomAudit](../../../DkMathTest/NumberTheory/GapFocusingAddressAxiomAudit.lean)
は新規 production 全 **53 宣言**を指定し、全件 `#print axioms` を実行する。
新規四 regression module は名前付き **29 宣言**をそれぞれ個別に指定する。
さらに一つの anonymous calibration も kernel-checked になった。

source から declaration 名を抽出し、実際の log 出力との対応を機械検査した。
53/53 production、29/29 named regression の出力があり、全 dependency set が
`{propext, Classical.choice, Quot.sound}` の部分集合だった。空集合も許容した。
既存 `exists_primitivePrimeDivisor_prime_exp`, `_body_nat`, `_kernel_nat` の
三 endpoint も現在の source/import に対して再監査し、標準公理のみだった。
集計: [source-dependency-audit-003](evidence/MANIFEST.md#log-c2bbf18970308ee7)。

**新規 Lean 全十ファイル**（production 五、test/audit 五）の token scan は
`sorry`, `sorryAx`, `admit`, `axiom`, `native_decide`, `unsafe` の zero matches。
`#print axioms` は検査コマンドであり、追加公理宣言ではない。

## 回帰対象

- `Phi_2(2)=Phi_6(2)=3`, `Phi_3(2)=7` と homogeneous evaluator の一致。
- characteristic 3 での polynomial identity `Phi_6=Phi_2^2`。
- degree 2/6 が同じ rational-prime support を持つことによる support map の非単射性。
- prime two、order-one の least nontrivial address、zero ratio と全座標消失 branch。
- degree 6 の素数が degree 5 に対して fresh でも globally primitive でないこと。
  全ての候補 prime に対する degree-six primitive 不存在も確認。
- signed coordinates、natural truncated subtraction の反例、degree-zero primitive
  definition の vacuity。
- primitive `Phi_3(5,3)=49` の load 2 と、最初の 2-layer / 後続 2-power の違い。
- 任意 `k` の prime-power load 1 と、unit-anchor first-address の full load。

valuation の独立 focused 実行も exit 0（8952 jobs）。
[build-layer-valuation-003](evidence/MANIFEST.md#log-d71ed47e0291227b) と
[valuation-audit-003](valuation-audit-003.md) に検証範囲を記録している。

## 既存全体 warning との分離

main `DkMath` を含む実行では、変更していない次の五 warning が再表示された。

| ファイル | 行 | warning |
| --- | ---: | --- |
| `DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean` | 147 | declaration uses `sorry` |
| `DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean` | 4187 | declaration uses `sorry` |
| `DkMath/NumberTheory/GcdNextResearch.lean` | 850 | declaration uses `sorry` |
| `DkMath/FLT/Kummer/CyclotomicPrincipalization.lean` | 5389 | declaration uses `sorry` |
| `DkMath/CosmicFormula/TriominoFLT.lean` | 1919 | declaration uses `sorry` |

新規 53 宣言の公理監査は、これらの import/build warning と独立した全件検査。
repository 全体の admission-free 性は主張していない。

## 差分検査と実装範囲

`git diff --check` は exit 0。新規テキストファイルの末尾空白・final newline と、
四つの新規報告文書の相対リンクも別途検査した。
記録: [diff-check-003](evidence/MANIFEST.md#log-13a2fb1b03ca3819)。
既存 tracked source の変更は `DkMath/NumberTheory/GapFocusing.lean` の五 import と
facade documentation。実質的な theorem 追加は五つの新規 production module。
CFBRC の実際の general homogeneous evaluator を再利用し、旧 research の
valuation endpoints を production proof に使用していない。
