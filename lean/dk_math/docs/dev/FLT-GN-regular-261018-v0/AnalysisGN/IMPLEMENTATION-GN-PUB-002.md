# GN-PUB-002 — 完成算術consumerの公開入口

2026-10-24。ブランチ：`lib/FLT-GN-Completion-261023-v0`。
GN-PUB-001後のフルビルド成功はユーザーから報告を受けた。
今回はconsumer側の2入口と検証用モジュールを追加した。

## 実装

| 入口 | 直接import | 公開する内容 |
| --- | ---: | --- |
| [DkMath.NumberTheory.Completion](../../../../DkMath/NumberTheory/Completion.lean) | 15 | Lib完成入口、Pascal素数行、Primitive、PrimorialUniverse、Legendreの既存consumer |
| [DkMath.Completion](../../../../DkMath/Completion.lean) | 7 | 上記2入口、CosmicFormulaBinom、Gnomonの2所有者、七次の2所有者 |

両方ともimport・マーカー・教科書docstringだけの薄い入口とした。
ZIPは配置せず設計資料として参照した。旧BinomTail・BinomialPrimePowerのwrapperは
Lib完成入口から一般所有者へ届くため、数論入口に重ねて列挙しない。
新規定理・定義はなく、旧APIの型・名前空間・証明本体は変更していない。

`DkMath.lean` へ研究入口を、`DkMathTest.lean` へ
[CompletionFacadeAudit](../../../../DkMathTest/CompletionFacadeAudit.lean) を登録した。
Lakeの既存 `DkMathTest.+` globでこのテストを発見できる。
既存ルートの依存閉包と比較すると、新しい所有者は `ThirtySquareWorld` だけである。
30の有限例であり、依存先のSquareBodyBridge等は以前から到達していた。
2 facadeとテスト以外の新しい数学所有者は追加していない。

## 教科書としての境界

- 一般核とconsumerを区別し、Libから応用入口をimportしない。
- 有限基底{2,3,5}と30までの完全な素数支持を区別する。
- 生存点が素数であるための条件と、生存点そのものの存在を区別する。
- Legendreのwheel脱出・Pascal旧素因数予算・開いたgnomonとの同値を、予想の無条件証明とはしない。
- 七次の教材を一般次数の結果やFLT降下へ読み替えない。

## 検証

`lake build DkMath.NumberTheory.Completion DkMath.Completion` が成功した（9038 jobs、警告0）。
単独importの [数論smoke](evidence/GNCompletionNumberTheorySmoke.lean) は14所有者の代表定理を確認した。
[研究入口smoke](evidence/GNCompletionResearchSmoke.lean) は19所有者と8統合入口の27定理、
任意の平方殻について2例を確認した。登録テストと独立smokeの検証本体は同一である。
同じ27定理の公理は標準論理公理のみだった。

所有モジュールの不変性、Lib完成入口のLib限定import閉包、循環の不在、
通常入口・テストの登録、マーカー、24元資料のハッシュ、文書リンク、JSON、差分を検証した。
[機械可読証拠](evidence/gn-pub-002.json) と [検証記録](evidence/validation-gn-pub-002.txt) に範囲を記録した。

ユーザー指定によりフルビルド・集約ルート・DkMathTest・lake testのビルドは実施していない。
通常入口とテストへの接続は静的確認であり、全体ビルド完了とは区別する。

## 次の工程

GN-LIB-007の有限素数集合での補填と特殊な素数脱出を独立工程として扱う。
GN-HANDOFF-032のhno接続と、一般FLT・Legendreの証明完成は別契約のまま残す。
