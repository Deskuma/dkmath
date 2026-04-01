# FLT restore 260330 v0 - 最終報告

> 🐺賢狼:

まずスナップショット本体と、ぬしが貼ってくれたレポート断片を突き合わせるぞい。
今回は **現物の集計** と **既報の設計判断** を合わせて、FLT 側の総括と次の実装順まで落とし込む。

> 🐺賢狼:

現物の tar をほどいておる。
いまは **FLT 幹線の主要ファイル群の規模** と **snapshot 上の実際の `sorry` 分布** を拾いに行っておるぞ。

> 🐺賢狼:

わっちが現物をほどいて見た結論から言うと、今回のスナップショットは **「FLT の未整備な土台集め」段階をかなり抜けて、Branch A の最後の数学核へ圧縮された状態」** じゃ。
しかも、ぬしが貼ってくれた restore 完了レポートの大筋は、現物の snapshot とよく整合しておる。

## 1. 現物確認

まず、提示された SHA256

$$
\texttt{84728a004c535e52fc2652c9a6c0a99c8ca6ac7663491ade4329f373e163461e}
$$

は、手元で展開前の tar に対して一致を確認した。
そのうえで snapshot 本体と summary tar を展開し、Lean ファイルを直接走査した。

## 2. 統計レポート

### 2.1. リポジトリ全体

現物 snapshot の `DkMath` ツリーを直接数えると、次の通りじゃ。

- Lean ファイル数: 242
- 総行数: 101,801
- `def|lemma|theorem` 総数: 4,040
- **コードとしての厳密な** `sorry` 総数: 8

ここで言う `sorry` は、コメント文中の “no-sorry” や説明文を除き、行として本当に

```lean
sorry
```

だけが置かれているものを数えておる。

### 2.2. FLT 名前空間

`DkMath.FLT` 側はかなり大きい。

- FLT 系 Lean ファイル数: 36
- 総行数: 32,752
- `def|lemma|theorem` 数: 1,514
- 厳密な `sorry`: 1

つまり、**FLT 名前空間そのものはほぼ sorry-free** で、残り穴は実質 1 箇所に圧縮されておる。

### 2.3. PrimeProvider 集中度

いまの FLT の重心はほぼ `PrimeProvider` にある。

- `DkMath/FLT/PrimeProvider` 配下
  - ファイル数: 16
  - 総行数: 25,000
  - `def|lemma|theorem` 数: 1,109
  - 厳密な `sorry`: 1

割合で言うと、

$$
\text{PrimeProvider 行数比} \approx 76.3\%
$$

$$
\text{PrimeProvider 宣言数比} \approx 73.2\%
$$

じゃ。
つまり今の FLT 形式化は、かなりはっきり **PrimeProvider が本丸** じゃよ。

### 2.4. 今回の restore 系 5 ファイル

ぬしの貼り付けレポートでは、次の 5 ファイル合計が

- 16,749 行
- 1,068 定義・定理
- `sorry` 1

と整理されておった。

現物走査では **行数合計 16,749 と code-sorry 1 は完全一致** した。
個別にはこうじゃ。

- `TriominoCosmicBranchA.lean`: 5,620 行, `sorry` 1
- `TriominoCosmicBranchAExceptional.lean`: 4,159 行, `sorry` 0
- `TriominoCosmicBranchARestore.lean`: 2,982 行, `sorry` 0
- `TriominoCosmicGapInvariant.lean`: 3,338 行, `sorry` 0
- `GTail.lean`: 650 行, `sorry` 0

宣言数は、`def|lemma|theorem` だけなら restore は 79 じゃが、貼り付けレポートの 107 は `structure` なども含めた数え方だと綺麗に一致する。たとえば `TriominoCosmicBranchARestore.lean` は、現物でも 107 個と再現できる。
ゆえに **レポートの宣言数は「広義の宣言数」** と読むのが正しい。

ただし `TriominoCosmicBranchA.lean` の 271 だけは、現物の機械集計では 270 で、ここは 1 個だけ数え方の差か、レポート更新時点との差分があるようじゃ。

## 3. 残っている `sorry` の分布

厳密な code-sorry 8 箇所は次の通りじゃ。

- `DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean` 1
- `DkMath/CosmicFormula/TriominoFLT.lean` 1
- `DkMath/NumberTheory/GcdNextResearch.lean` 2
- `DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean` 1
- `DkMath/ABC/ABC#Research.lean` 1
- `DkMath/ABC/ABCWorking.lean` 1
- `DkMath/Collatz/V2#pending.lean` 2

ここから見えるのは、**実戦線として本当に重い穴は Branch A の 1 点** で、それ以外は research / prototype / pending の性格が強いということじゃ。

## 4. 数学的な総括

ぬしの restore 完了レポートが言うように、今回の最大成果は

- witness $q$ の構造化
- Interference Fringe Bundle の整備
- Kummer valuation
- Hensel lift
- local factorization $GN = \delta \cdot U$
- 降下 step の明示化

までが **一本の no-sorry チェーン** として揃ったことじゃ。

これはただ補題が増えた、という話ではない。
むしろ、

$$
\text{「何を作ればよいか分からぬ段階」}
$$

から

$$
\text{「何が足りないかが 2〜3 個の kernel に固定された段階」}
$$

へ進んだのが本質じゃ。

特に restore レポートでは、open kernel を

1. `ContradictionTarget`
2. `ValuationPeelPacketTarget`
3. `BranchA.lean` L4122 の設計マーカー

に圧縮しておる。
この圧縮は大きい。数学では、未解決部分が小さな命題へ閉じること自体が前進だからの。

しかも `TriominoCosmicBranchA.lean` の残存 `sorry` 自体が、単なる証明未着手ではなく、ファイル中のコメントから見ても **comparison route がもう情報を出し尽くしたことを示す checkpoint** になっておる。
つまり、あの穴は「埋め方がまだ弱い」のではなく、**設計上もう別 route へ移るべき箇所** なのじゃ。

## 5. 現在地の解釈

わっちの見立てでは、いまの FLT 形式化状況はこうじゃ。

### 5.1. $n=3$ 側

これはかなり強い。
既存の構成マップでも、`DkMath.FLT.Main` は Zsigmondy + p-adic valuation による $d=3$ 完成ルートとして整理されておる。
現物走査でも `Main.lean` は sorry-free じゃ。

### 5.2. $p \ge 5$ 側

ここは「補題不足」ではなく、**Branch A の最終矛盾核** が未決という状態じゃ。
これは悲観材料ではない。むしろ、valuation・witness・Hensel・local factorization が揃ったので、残りは本当に **深い数学の一撃** だけに近づいておる。

### 5.3. 周辺設計

一方で、LPS / PowerSwap / ObservedMin 系は、設計ノートでも FLT 本体と切り分けて、`PowerSwap` や `NumberTheory.PowerSums` 側へ移す方針が既に明確じゃ。
この整理は、今後の FLT 本丸の見通しをさらに良くする。

## 6. 今後の実装計画

ここは順番が大事じゃ。
わっちなら、次はこう打つ。

## 6.1. 第一段. `ContradictionTarget` を terminal case で攻める

これは、貼り付けレポート自身の提案とも一致しておる。
降下列は well-founded で、有限回で terminal case $s' = 1$ に落ちる見込みがある。そこへ既に完成した local valuation 理論を流し込んで矛盾を取る。

実装としては、新ファイルを切るのがよい。

```text
DkMath/FLT/PrimeProvider/TriominoCosmicBranchATerminal.lean
```

ここで狙うべき核は次の 4 本じゃ。

- `branchA_descent_iterate_exists`
- `branchA_terminal_case`
- `branchA_terminal_valuation_contradiction`
- `contradictionTarget_of_terminal_case`

思想としては

$$
\text{descent} \;\Rightarrow\; s_{\mathrm{term}} = 1
$$

$$
s_{\mathrm{term}} = 1 \;\Rightarrow\; v_q(s_{\mathrm{term}})=0
$$

$$
q \mid s \text{ の transport と valuation theorem} \;\Rightarrow\; \text{矛盾}
$$

という形じゃ。

これは **今ある restore 資産を最も自然に再利用できる route** で、円分体の重装備に入る前に必ず試す価値がある。

## 6.2. 第二段. `BranchA.lean` L4122 を adapter 化する

現状の `primeGe5BranchANormalFormNePCoprimeKernel_default` は、comparison route の終端チェックポイントじゃ。
ゆえに、ここを新しい contradiction kernel へ繋ぐ薄い adapter に置き換えるのが筋じゃ。

つまり、

```lean
theorem primeGe5BranchANormalFormNePCoprimeKernel_default :
    PrimeGe5BranchANormalFormNePCoprimeKernelTarget := by
  exact ...
```

の中身を、terminal contradiction 側へ渡すだけの薄い橋にする。
必要なら名前も、コメントにある通り `...Checkpoint` 系へ寄せると構造が美しくなる。

## 6.3. 第三段. `ValuationPeelPacketTarget` を独立に切り出す

restore レポートでも、これは `ContradictionTarget` と独立と整理されておる。
ならば混ぜぬ方がよい。

```text
DkMath/FLT/PrimeProvider/TriominoCosmicBranchAPeel.lean
```

のような専用ファイルへ逃がして、

- packet measure
- peel invariant
- $p \mid t$ 専用 descent
- smaller packet への reduction

だけを閉じる。
こうすれば Branch A primitive 側の contradiction 本丸と干渉せぬ。

## 6.4. 第五段. 非 FLT 資産の切り分け

これは急務ではないが、中期的には効く。
設計ノート群の通り、次の切り分けは妥当じゃ。

- `CosmicFormula` 側へ residual / Big-Body-Gap
- `PowerSwap` 側へ $a^b=b^a$ 幾何
- `NumberTheory.PowerSums` 側へ `ObservedMin*`

FLT 側には橋だけを残す。
これで FLT 本丸の依存が軽くなり、Branch A / Zsigmondy / valuation の核心に集中できる。

## 7. わっちの最終評価

今回の snapshot は、かなり良い。
なにが良いかと言うと、**未解決部分が散らばっておらぬ**。

- $d=3$ は別解幹線でかなり締まっている。
- $p \ge 5$ は PrimeProvider に重心が集まり、
- その中でも restore 系が no-sorry 化され、
- 残りが `ContradictionTarget` と `ValuationPeelPacketTarget` に圧縮された。

これは、形式化研究としては **かなり強い形** じゃよ。
もはや「何をすればよいか分からぬ」ではなく、

$$
\text{次に刺すべき点が見えている}
$$

のだからな。

わっちの推奨順位を一行で言えば、

$$
\boxed{\text{terminal case } \to \text{ contradiction kernel } \to \text{ BranchA adapter 置換 } \to \text{ peel 独立化}}
$$

じゃ。
