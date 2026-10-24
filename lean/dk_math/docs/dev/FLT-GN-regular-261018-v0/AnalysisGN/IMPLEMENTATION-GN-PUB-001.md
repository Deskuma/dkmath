# GN-PUB-001 — GN・完成算術の薄い公開入口

2026-10-24。ブランチ：`lib/FLT-GN-Completion-261023-v0`。

[Completion.lean](../../../../DkMath/Lib/Cosmic/Completion.lean) を追加した。
consumerは次の1行で今回整備した一般数学へ到達できる。

```lean
import DkMath.Lib.Cosmic.Completion
```

## 公開契約

| 層       | 直接所有モジュール数 | 内容                                                      |
| -------- | -------------------: | --------------------------------------------------------- |
| GN基礎   |                    9 | GTail、再帰、隣接支持、円分表示、合同式、付値、Pascal分割 |
| 完成算術 |                    3 | 二項尾項、平方完成、Big・Body・Gapとgcd                   |
| 完成不足 |                    3 | 有限和R_n、算術、D_n、再帰と正性                          |
| 可除性   |                    3 | gapのgcd、強可除性、奇偶の精密gcd                         |
| 原始三項 |                    1 | CompletionLoan、正性、A+B=C、原始性                       |
| 素数住所 |                   11 | 乗法位数、円分層、斉次評価、LTE、付値                     |

全30所有モジュールを直接importする。所有関係を公開契約として明示するため、
推移的に到達できる所有者も直接列挙した。`DkMath.Lib` 全体はimportしない。
局所依存閉包も30個のLibモジュールだけで、応用層への逆流はない。
`DkMath.Lib.lean` にはこの入口のimportを追加した。

## 教科書と数学的境界

ファイルマーカーと六層の説明、名前空間と所有ファイルの区別をdocstringに記した。
定義・定理・証明本体は追加していない。既存所有者は変更せず、元の全修飾名で利用する。
原始性、正次数、座標の大小、非零性、分母の単元条件、2進LTEの補正は元の型に残る。
住所の分類を、新しい素数の存在やFLTの矛盾へ読み替えない。

## 検証

- `lake build DkMath.Lib.Cosmic.Completion`：成功、2844 jobs。
- [単独importのsmoke](evidence/GNCompletionPublicSmoke.lean)：30所有者の代表定理と8統合入口を確認し、奇偶gcdと平方完成の2例を検証。
- 同じ38定理の公理を確認。標準論理公理のみ。
- 所有者30ファイルはbaseline HEADと同一。元資料24ファイルのSHA256も一致。
- import閉包、ファイルマーカー、JSON、文書リンク、`git diff --check` を確認。

詳細は [機械可読証拠](evidence/gn-pub-001.json) と [検証記録](evidence/validation-gn-pub-001.txt)。
対象moduleと単独importの検証範囲であり、集約Libやフルビルド、DkMathTest、lake testは今回実行していない。

## 次の工程

GN-PUB-002でNumberTheory・研究consumerの入口を検討する。
GN-LIB-007の有限素数集合での補填と脱出は独立の後続課題として残す。
