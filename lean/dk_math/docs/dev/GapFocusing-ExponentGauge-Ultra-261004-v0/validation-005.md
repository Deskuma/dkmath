# Instruction 005 validation

Lean / Mathlib v4.34.1。cwd: `lean/dk_math`。

## 最終 build

```text
lake build DkMath.NumberTheory.Legendre.ParitySafePersistence \
  DkMath.NumberTheory.Legendre.ParitySafePersistenceParity \
  DkMath.NumberTheory.Legendre.ParitySafeFreshCost \
  DkMathTest.NumberTheory.LegendreFreshCost \
  DkMath.NumberTheory.Legendre DkMath
```

exit 0、10370 Lake jobs。[最終ログ](evidence/MANIFEST.md#log-eadd72797eab323e)。jobs は replay を含む依存グラフの件数で、新規 compilation 件数ではない。新規・変更 production の今回の宣言、および回帰ファイルに warning/error はない。

全 DkMath build が再表示した既存の五つの未証明研究宣言 warning は、新規証明の dependency と区別している。次の全件公理出力にはその未証明公理がない。

[Source inventory](evidence/MANIFEST.md#log-5b59fc55c59068eb) は `lake env lean DkMathTest/NumberTheory/LegendreFreshCostInventory.lean` で実行、exit 0。

## 公理監査 coverage

[LegendreFreshCostAxiomAudit.lean](../../../DkMathTest/NumberTheory/LegendreFreshCostAxiomAudit.lean) は、HEAD と live source の差から全新規 public 宣言を抽出して、各 `#check` / `#print axioms` を列挙した。`lake env lean` は exit 0。実際のログと manifest の名前を機械照合した。

| Source | Coverage |
| --- | ---: |
| 既存 ParitySafePersistence の追加分 | 5/5 |
| ParitySafePersistenceParity | 10/10 |
| ParitySafeFreshCost | 31/31 |
| LegendreFreshCost 名前付き回帰・正規化 | 15/15 |
| 合計 | 61/61 |

全 dependency set は `{propext, Classical.choice, Quot.sound}` の部分集合。空集合も許容した。`sorryAx` と独自公理 dependency はない。

[公理ログ](evidence/MANIFEST.md#log-7eb521d68d51403c) · [manifest](evidence/MANIFEST.md#log-a4e1fa4ef14dfdc0) · [照合結果](evidence/MANIFEST.md#log-52d781f40739b2a0)。

## 禁止 token / 差分

変更 production 全四ファイル（既存 Persistence、new Parity、new FreshCost、Legendre facade）と回帰を走査。`sorry`, `sorryAx`, `admit`, `axiom`, `native_decide`, `unsafe` は全 zero matches。[scan](evidence/MANIFEST.md#log-c162a8351c5c8278)。監査ファイルの `#print axioms` は検査コマンドで、追加公理宣言ではない。

`git diff --check` を実行。未追跡の新規ソース・文書・ログには `git diff --no-index --check /dev/null <file>` を実行し、whitespace diagnostic がないことを確認した。[diff check](evidence/MANIFEST.md#log-be7546b3c76e7458)。

## 回帰と証明範囲

既存 active/old/fresh support を exact な computable finite filters に等式で正規化し、標準 `decide` の kernel reduction で有限個数を証明した。候補族・support を別の数学的集合へ置き換えていない。native decision は使っていない。

main block の exact values は R=245、C1=169、C2=97、singleton=94、firstSlot=110。既存 simultaneous full cover の仮定を保持したまま fresh>=148、supportExcess>=38、fullCandidate sum+38<=incidence sum を証明した。

singleton fresh q が persistent prime-factor pool に属さない例、fresh pair があるのに local residual mass が0の例、その強すぎる inequality の否定、fixed-seat candidate frequency 2 対 shell frequency 3 の例を checked regression とした。

新規有限 minimum-cost bound は support-excess に対するもの。LowCost/depth residual upper capacities の減少、全殻 cover failure、Legendre、asymptotic claim は検証範囲に含まれず、証明もしていない。
