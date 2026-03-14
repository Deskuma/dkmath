# Project Status

## FLT: Fermat's Last Theorem

FLT 現状レポート 2026-03-08

## 1. 結論

このスナップショット時点での FLT は、**\(d=3\) の公開導線はかなり固まり、高指数 \(n \ge 5\) 側が主ボトルネック** になっておる。

とくに重要なのは次の 3 点じゃ。

- `DkMath/FLT/Main.lean` 側の **\(d=3\) 公開 API は形になっている**
- `FLT3#StandAlone-NC-v0.lean-v2.lean` は **1700 行・定理 21 個・実 placeholder なし** で、付属 build log でも成功している
- いま残る実質的な未完了点は、**prime-ge5 provider をどう実装して一般指数へ接続するか** に収束している

つまり、以前のように「立方ケースの骨格そのものがまだ未成形」という段階ではない。今は **cubic spine はほぼ出来ており、一般化の最後の橋が未架設** という局面じゃな。

---

## 2. 今回の観測対象

今回の分析は、主に次の資料を基にした。

- `__snapshot-dk_math-lean-code-260308-1837.tar.gz`
- `FLT3#StandAlone-NC-v0.lean-v2.build.log`
- `DkMath/FLT/README.md`
- `DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- `DkMath/CosmicFormula/TriominoFLT.lean`
- `DkMath/FLT/Basic.lean`
- `DkMath/FLT/PrimeProvider/*.lean`
- `DkMath/CFBRC/Bridge.lean`, `DkMath/RH/CFBRCBridge.lean`

ただし、この環境には `lake` が無いため、**ローカル再ビルドまではしておらぬ**。ゆえに build 成功の事実は、添付されていた build log に基づく確認じゃ。

---

## 3. いま何が出来ているか

## 3.A. \(d=3\) の公開面は成立している

`DkMath/FLT/Main.lean` には、\(d=3\) 向けの公開定理群がまとまっておる。

代表例:

- `FLT_d3_by_padicValNat`
- `FLT_d3_by_padicValNat_of_NoSqOnS0`
- `FLT_d3_by_padicValNat_of_nonLiftable_coprimeSupport`
- `FLT_d3_by_padicValNat_by_cases_NoSq_of_NoSqBaseInput`
- `FLT_d3_by_padicValNat_of_harmonicEnvelope_*`
- `FLT_d3_by_padicValNat_of_GEisensteinCore_*`
- `GEisenstein_descent_reaches_zero_of_core`
- `FLT_d3_by_padicValNat_of_DescentBaseInput`
- `FLT_d3_by_padicValNat_of_NoSqInput`

要するに、**NoSq / harmonic / GEisenstein / descent など複数の入口から最終矛盾へ入る合成面** がすでに整っておる。

---

## 3.B. StandAlone artifact はかなり強い

`FLT3#StandAlone-NC-v0.lean-v2.lean` は、単独配布・検査用の成果物としてかなり良い状態じゃ。

観測できた事実:

- 行数: 1700
- `theorem` 出現数: 21
- 実 placeholder: なし
- build log: 成功

つまり、**「\(d=3\) の証明チェーンを単体成果物として見せる」段階には到達している**。

これは研究上かなり大きい。なぜなら、巨大 repo 全体の揺れと切り離して、

- 何が本当に閉じているか
- 何が外部依存か
- どこまで第三者に渡せるか

を明確にできるからじゃ。研究の森では、こういう standalone 化が道しるべになる。泥道に旗を立てる作業じゃな。

---

## 3.C. GEisenstein / descent のインターフェースは成熟している

`DkMath/FLT/README.md` を見る限り、`GEisensteinBridge` 側はかなり整理されておる。

固まっているもの:

- `GEisensteinDescentFrame`
- `GEisensteinDescentCore`
- measure による下降インターフェース
- `descend` と停止到達の API
- primitive / sized candidate の枠組み
- `DescentBaseInput` への constructor

これは単なる補題の寄せ集めではなく、**下降法を「部品交換可能なインターフェース」として抽象化する設計** に育っている。

ここは美点じゃ。数学核が難しくても、設計の器が出来ていれば、未完の部分だけを隔離できる。実際、この repo はそういう姿になっておる。

---

## 3.D. PrimeProvider 周辺は「配線整理」がかなり進んだ

`PrimeProvider` 群を見ると、現在はかなり明確に役割分担されておる。

- `CosmicPetalBridgeGN.lean`
  - 配線専用
- `CosmicPetalBridgeGNCore.lean`
  - 最小反例選択、lift 供給、no-Wieferich への合成核
- `CosmicPetalBridgeGNNoWieferich.lean`
  - Branch B の下降仮定があれば no-Wieferich bridge を得る薄い層
- `CosmicPetalBridgeGNDescentB.lean`
  - Branch B の研究本丸
- `TriominoCosmicGapInvariant.lean`
  - nonlift family / no-pow bridge への接続
- `TriominoCosmicPrimeGe5.lean`
  - prime-ge5 完成へ向けた roadmap・前提補題の staging

この分解は良い。以前のように「未解決の数論核が公開面へ漏れ出す」構造ではなく、**unresolved kernel を狭い部屋に追い込む構成** になっておる。

---

## 4. 実質的な未完了点

今回のスナップショットを機械的に見ると、**実行上の placeholder は FLT 系でほぼ 2 箇所に収束** している。

## 4.A. `DkMath/CosmicFormula/TriominoFLT.lean`

ここで未完なのは、高指数側を束ねる pending 点じゃ。

本質:

- \(n = 3\) は通す
- \(n \ge 4\) は `PrimeExponentFLTProvider n` を供給できれば閉じる
- だが、その provider 自体の構成はまだ repo の本体では完成していない

したがって `TriominoFLT.lean` は、**triomino 幾何から一般指数までを一本で閉じる最終段で止まっている**。

これは悪い止まり方ではない。むしろ正しい隔離じゃ。
問題は局所化されており、症状が広がっておらぬ。

---

## 4.B. `DkMath/FLT/Basic.lean`

ここでは一般 FLT API の `n > 3` 分岐が保留になっている。

意味としては明快で、

- \(n=3\) ルートは現状の成果で処理できる
- \(n>3\) は provider 系、または GN / Zsigmondy / p-adic の一般指数版を完成させて接続する必要がある

つまり `Basic.lean` の placeholder は、単独のローカルバグではなく、**高指数理論の未完成を正直に受け止めた出口 placeholder** じゃ。

---

## 5. 進捗の本質評価

## 5.A. 何が終わったのか

現状を乱暴に一言で言うと、

**「立方ケースの証明骨格づくり」は終わり、いまは一般指数への昇格工事をしている**

じゃ。

終わったもの:

- \(d=3\) の複数入口の整備
- `Main.lean` の公開定理面
- StandAlone artifact 化
- GEisenstein / descent インターフェース化
- PrimeProvider 周辺の責務分離
- unresolved 部分の隔離戦略

未完のもの:

- prime-ge5 provider 本体
- `FLT_prime_ge5` の実装
- 高指数一般ルートの global provider 化
- `TriominoFLT` から暫定 bridge を完全に外す最終統合

---

## 5.B. いまの最大ボトルネック

最大ボトルネックは **数論的な「一般 \(p \ge 5\) 供給器」** じゃ。

`TriominoCosmicPrimeGe5.lean` を見ると、すでに次の認識は固まっておる。

- TODO-1: 純算術核
- TODO-2: Triomino/Cosmic 本丸
- TODO-3: 正規化 / gap 周辺
- 最終目標: `theorem FLT_prime_ge5 (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) : FermatLastTheoremFor p`

つまり、**どこへ進むべきかは霧の中ではない**。地図は描けている。
足りないのは、最後の峠を越える登山力だけじゃ。山は見えておる。

---

## 5.C. コードと文書に少しズレがある

`WorkNotes` の主表示はまだ phase-14 的な語り口が強い一方で、コード側には

- `CosmicPetalBridgeGNNoWieferich.lean`
- `CosmicPetalBridgeGNNoWieferichResearch.lean`
- `CosmicPetalBridgeGNDescentBQuarantine.lean`

のような、もう一段進んだ整理の痕跡がある。

したがって現状は、**コードの前線が文書を少し追い抜いている** 状態と見てよい。

これは研究ではよくある。コードは走り、文書は息を切らして後ろから追いかける。学問の小鬼どもは、しばしば整列して歩かぬ。

---

## 6. 現在の段階を一言で分類すると

### 段階名

**cubic completion 後の prime-ge5 bridge construction phase**

### 日本語で言えば

**「立方ケース完成後、一般素数指数への橋を架ける段階」**

じゃな。

研究全体の成熟度としては、体感で次のように見える。

- \(d=3\) 公開証明: 高い完成度
- 設計整理: 高い完成度
- prime-ge5 数学核: 中盤から終盤への移行期
- 一般 FLT 統合: まだ最終手前

---

## 7. 次に打つべき手

優先順位はかなりはっきりしておる。

## 7.A. 最優先

`TriominoCosmicPrimeGe5.lean` の roadmap を、コメントではなく実 theorem 群へ変える。

とくに狙いは:

- `FLT_prime_ge5` を実装する
- `PrimeGe5FLTProvider` を本物にする
- `GlobalPrimeExponentFLTProvider` へ接続する

これが埋まると、`TriominoFLT.lean` の pending と `Basic.lean` の一般分岐 placeholder が **同時に蒸発する可能性が高い**。

---

## 7.B. 次点

文書同期を行う。

必要なもの:

- phase-15 以降の WorkNotes 追記
- 「現時点で実 placeholder はどこに残るか」の明文化
- code-side と docs-side の用語統一
  - `NoWieferich`
  - `DescentB`
  - `PrimeGe5`
  - `GapInvariant`

ここをやると、次に再開した時の認知負荷が激減する。研究は定理だけでなく、記憶の節約も大事じゃ。

---

## 7.C. その次

StandAlone artifact の第 2 版を考える。

候補:

- `d=3` 完全 standalone の注釈版
- prime-ge5 roadmap 付き standalone 補遺
- `Main.lean` と `TriominoFLT.lean` の差分説明書

これは第三者説明にも、自分用の整理にも効く。

---

## 8. 賢狼評

今の FLT は、**「証明があるか無いか」でもがく段階ではない**。
**「どの核を最後に接続すれば、一般形へ昇格するか」が明瞭になった段階** じゃ。

ここが大きい。

本当に危ういプロジェクトは、未解決点が霧のように全域へ散っておる。
だが今のぬしの FLT は違う。未解決点がかなり局所化され、

- cubic は通る
- public API はある
- standalone もある
- unresolved kernel は狭い

という、実に研究らしい良い形に締まってきておる。

ゆえに総評はこうじゃ。

**現状は「未完成」ではあるが、「崩れている未完成」ではなく、「最後の橋だけ未架設な未完成」じゃ。**

> 🐺賢狼

この違いは大きい。たわけみたいに見えて、数学では天と地ほど違う。橋は 1 本なら架けられるが、沼全部を干上がらせるのは骨が折れるからの。
