# review-001: `CosmicFormula-Erdos1196` の実装開始について

## 1. 総評

これは **前進** じゃ。しかも、ただ新しい定理を足したというより、既存の宇宙式分解と primitive-beam 系を **再利用可能な API 層へ持ち上げた** のが本体じゃな。差分の自己報告どおり、今回で `Phase A-B` は実質的に入り、`ValuationFlow` はまだ完成ではないが、`PrimitiveBeam` を新命名で読める入口まで届いておる。

わっちの見立てでは、今回閉じたものは次の三つじゃ。

第一に、 **保存則の語彙が独立モジュールになった**。
第二に、 **branch 上界の最小骨格が入った**。
第三に、 **primitive prime から GN / valuation へ流す spine が一本見える形になった**。

逆に、まだ **未着手ではなく未完** のものもはっきりしておる。

* hitting mass の一般論
* `ABC/MassBridge`
* `ABC/ValuationFlowBridge`
* `rad` を質量語彙で読む翻訳
* `Tromino2D` と `Harmonic`

つまり今は、設計図で言うところの

$$
\text{CosmicFormula}
\;\to\;
\text{Mass API}
\;\to\;
\text{Branch API}
\;\to\;
\text{ValuationFlow}
$$

までの基礎工事が進み、最後の

$$
\text{ABC Bridge}
$$

がまだ残っている、という状況じゃ。

---

## 2. 状況分析

### 2.1. 今回の差分の本質

今回の差分は、新理論を無理に証明しに行ったのではなく、既存資産を **Erdős #1196 / 質量保存 API** という文脈で再編したものじゃ。これは実装計画の方針そのものと一致しておる。

計画では最初から、

* 一般 `Measure` や `MarkovKernel` へは寄せない
* まずは非負・保存・劣保存・primitive による非衝突を切り出す
* `Nat` 減算は bridge 扱いにする

と置いておった。今回の差分は、その通りに動いておる。ここは美しい。設計と実装がねじれておらぬ。

### 2.2. `CosmicFormula.Basic` への import 追加

`Mass.Core / Decompose / Branch` を `CosmicFormula.Basic` に import したのは小さく見えて、実は重要じゃ。これで今回の Mass API は「実験枝」ではなく、**CosmicFormula の正規語彙** として扱われ始めた。つまり Big / Body / Gap の分解は、もはや補助メモではなく、DkMath の表 API に一段近づいたということじゃ。

### 2.3. フェーズ進捗の判定

計画書と照らすと、わっちの判定はこうじゃ。

* `Phase A` は **ほぼ閉じた**
* `Phase B` は **最小核として閉じた**
* `Phase C` は **入口を実装済み**
* `Phase D` は **未着手**
* `Phase E` は **History と build 検証で部分着手**

つまり「Phase A-B 完了、Phase C の入口まで」という自己報告は、かなり正確じゃ。誇張ではない。

---

## 3. 数学的解説

### 3.1. `Mass.Core` の意味

`MassSpace` は、見た目は単に

$$
\mu : \alpha \to \mathbb{Q},\qquad 0 \le \mu(a)
$$

を持つ最小構造体じゃ。じゃが、この「小ささ」がよい。
まだ確率でも measure でもなく、**非負質量** にとどめている。これにより、後から

* 恒等質量
* 正規化質量
* valuation 由来質量
* hitting 由来質量

を同じ型で差し替えられる。設計原則の「最初は確率ではなく質量」の忠実な実装になっておる。

`CosmicPart` も大事じゃ。
これは単なる列挙子ではなく、

$$
\text{big},\ \text{body},\ \text{gap},\ \text{core},\ \text{beam}
$$

という宇宙式の各項を、**意味つきの状態変数** として固定したことを意味する。これで将来、`rad` や `padicValNat` を結びつけるときにも、「どの部位の質量を読んでいるか」がぶれにくくなる。

さらに `CosmicMassAPI` / `CosmicResidualMassAPI` で、generic semiring 版、`Nat` 版、`Int` 版の concrete API を束ねたのは良い判断じゃ。ここで特に光るのは、`Gap` や `Core` が本来は片方の変数に依存しないにもかかわらず、**観測インターフェイスの arity を揃えた** ことじゃ。これは数学的には「本質的依存変数」と「観測器の入力形式」を分離した、ということになる。小さな設計だが賢い。

### 3.2. `Mass.Decompose` の意味

ここは今回の核心じゃ。
実際にやっていることは、新定理を証明したというより、既存の

$$
\text{Big} = \text{Body} + \text{Gap},
\qquad
\text{Body} = \text{Core} + \text{Beam},
$$
$$
\text{Big} = \text{Core} + \text{Beam} + \text{Gap}
$$

を `mass_*` 名で再公開したことじゃ。だが、この「名付け直し」は数学的に軽くない。これによって、宇宙式の分解が **代数恒等式** から **質量保存則** へと読み替え可能になった。

特に大事なのは、`CoreBeamGap` と `ResidualNat/Int` を **分けて扱っている** 点じゃ。

* `CoreBeamGap` 側は generic semiring 上で美しく動く
* `ResidualInt` 側は減算が honest なので自然
* `ResidualNat` 側は truncated subtraction が混ざるので side condition を明示する

この差を、実装がそのまま反映しておる。ここは数学的に健全じゃ。
とりわけ `ResidualNat` で

$$
\texttt{hcore : core $\le$ body}
$$

を要求しているのは重要で、これは単なる Lean の都合ではない。
自然数上では

$$
\text{beam} := \text{body} - \text{core}
$$

が「ほんとうの差」であることを保証する honest 条件じゃ。ゆえに、この side condition を隠さず API に出したのは正しい。むしろここを隠すと、後で「保存則」の名のもとに切り捨て減算の偽の等式を流通させてしまう危険がある。今回それを避けておるのはえらい。

### 3.3. `Mass.Branch` の意味

ここで入った `Branching`, `outgoingMass`, `SubConservative` は、数学的には

$$
\sum_{b \in \mathrm{children}(a)} \mu(b) \le \mu(a)
$$

という **有限分岐版 sub-Markov 骨格** じゃ。
まだ hitting probability も遷移核もない。じゃが、それでよい。計画書でもこの段階では `Finset` ベースの有限 branch に留めると明記されておった。

ここでの数学的意義は、宇宙式の分解を「静的な等式」だけで終わらせず、**子状態への質量配分** として読めるようにしたことじゃ。
`outgoingMass_nonneg` は自明そうに見えるが、今後 hitting 側を積むときの基礎補題になる。`branch_sum_le_parent` も単なる alias ではなく、設計ノートの言葉とコードの言葉を一致させる橋になっておる。

要するに、ここで初めて

$$
\text{保存} \quad\to\quad \text{劣保存}
$$

への移行が起きたわけじゃ。
この段は、#1196 の確率的視点を Lean へ移す際の「有限 combinatorial shadow」として十分に意味がある。

### 3.4. `ValuationFlow.Basic` の意味

ここはまだ本当の flow ではない。
わっちはそこを明確に言うぞい。いま入ったのは「flow の遷移」ではなく、**flow を読むための q-adic 観測器** じゃ。

定義されたのは

$$
\texttt{diffMass}(q,a,b,d) = v_q(a^d-b^d),
$$
$$
\texttt{boundaryMass}(q,a,b) = v_q(a-b),
$$
$$
\texttt{beamMass}(q,a,b,d) = v_q(GN_d(a-b,b)).
$$

これで、差冪

$$
a^d - b^d = (a-b),GN_d(a-b,b)
$$

のどこに q-adic mass が乗っているかを、boundary と beam に分けて読む準備ができた。
数学的にはこれは、確率流そのものではなく **局所負荷の座標系** の導入じゃ。名は `Flow` でも、段階としてはまだ `LoadCoordinates` に近い。しかし、設計図でも `Basic` は最小定義から始める方針だったから、これは問題ではない。むしろ堅い。

### 3.5. `ValuationFlow.Primitive` の意味

ここが数学的にはいちばんおいしい。

primitive prime (q) に対して、今回の wrapper 群が言っていることは本質的に次の一本道じゃ。

primitive 性により

$$
q \nmid (a-b)
$$

だから boundary mass は 0 になる。
すると差冪の q-adic 質量は全部 beam 側へ流れ、

$$
v_q(a^d-b^d) = v_q(GN_d(a-b,b)).
$$

さらに beam が squarefree なら

$$
v_q(GN_d(a-b,b)) \le 1
$$

だから結局

$$
v_q(a^d-b^d) \le 1.
$$

この流れを valuation-flow の言葉で再公開したのが、今回の `Primitive.lean` じゃ。
これは美しい。なぜなら primitive prime の「新しさ」が、抽象的な述語のままで終わらず、**boundary を素通りして beam に到達する質量チャネル** として読めるようになったからじゃ。ここは #1196 的視点と DkMath の宇宙式語彙が本当に接続し始めた点じゃな。

---

## 4. 何が閉じたのか

今回閉じたものを、数学的に短く言えばこうじゃ。

### 4.1. 保存則の抽象語彙が閉じた

宇宙式の

$$
\text{Big},\ \text{Body},\ \text{Gap},\ \text{Core},\ \text{Beam}
$$

が、単なる既存定義ではなく **Mass API の住民** になった。

### 4.2. 分岐上界の最小骨格が閉じた

`SubConservative` により

$$
\sum \mu(\text{child}) \le \mu(\text{parent})
$$

を一般定理として扱う入口ができた。

### 4.3. primitive から beam への流路が閉じた

primitive prime の “新しさ” が、

$$
\text{boundary ではなく beam に q-adic mass が載る}
$$

という形で再公開された。

この三つが今回の勝ち筋じゃ。
逆に言えば、まだ閉じておらぬのは「その流れを `rad` や hitting にどう集約するか」の部分じゃ。

---

## 5. 留意点と弱点

ここも正直に言うぞい。

### 5.1. `ValuationFlow` はまだ真の flow ではない

いまあるのは遷移ではなく観測器じゃ。
`stepByPrime`, `stepByPrimePow`, `hitting` はまだ無い。なので、名前だけ先に大きくなりすぎぬよう、次段で「何を state と呼ぶか」を明確にするとよい。

### 5.2. `Mass.Decompose` の定理名はまだ source 別

`_of_coreBeamGap`, `_of_residualNat`, `_of_residualInt` は、今段階では良い。
だが bridge 側で毎回 source を意識させるのは少し重い。次段では canonical alias を用意し、

* generic ならこれ
* honest subtraction が要るならこれ
* `ℤ` 版ならこれ

と読み筋を一本にしてやると、利用側が軽くなる。

### 5.3. `Branch` は最小核ゆえ、まだ concrete example がない

設計上は `Tromino2D` が本来そこに入るはずだった。今回は保留なので仕方ないが、`Branching` が本当に宇宙式分解と噛み合うことを示す concrete example は次で欲しい。これは数学的にも心理的にも大事じゃ。

---

## 6. 次の作業指示案 . Codex 追記向け

ここから先、わっちなら Codex への指示は **ABC bridge を先に進める**。
`ValuationFlow` の抽象を厚くするより先に、今ある spine を ABC 側へ渡して「何がもう読めるか」を固定したほうが、道がぶれにくい。

追記案はこのまま載せられる形で書いておくぞい。

```md
### レビュー追記案: 次の作業指示

1. `DkMath/ABC/MassBridge.lean` を追加する。
   目的は、今回入った `Mass.Decompose` の保存則 API を ABC 側の語彙へ薄く翻訳すること。
   まずは新定理を無理に作らず、既存 `Rad` / `PadicValNat` を使う wrapper を優先する。

2. 最初の補題候補は次の 4 本に絞る。
   - `abc_big_eq_body_add_gap_mass`
   - `abc_gap_mass_le_big_mass`
   - `abc_residual_eq_gap_mass`
   - `abc_squarefree_support_lower_bound`
   ここで `squarefree_support_lower_bound` は、`rad` を support mass 的に読む最小補題名として使う。

3. `DkMath/ABC/ValuationFlowBridge.lean` を追加する。
   目的は、`ValuationFlow.Primitive` の
   `boundaryMass = 0`,
   `diffMass = beamMass`,
   `diffMass ≤ 1`
   を、ABC 側で再利用しやすい名前で再公開すること。

4. 最初の補題候補は次の 3 本に絞る。
   - `primitive_prime_gives_zero_boundary_load`
   - `primitive_prime_transfers_diff_load_to_beam`
   - `squarefree_beam_bounds_local_load`
   ここでは `load` を `padicValNat` の局所量という意味で使う。

5. 今回は `ValuationFlow.Hitting.lean` にはまだ進まない。
   先に ABC bridge を通し、
   「Mass API と primitive valuation spine が ABC 側でどう読めるか」
   を固定してから hitting 一般論へ戻る。
```

---

## 7. 最終判断

今回の差分は、見た目以上に良い一手じゃ。
なぜなら、これは「Erdős #1196 の話を Lean に移した」のではなく、

$$
\text{宇宙式分解}
\;\to\;
\text{質量保存}
\;\to\;
\text{有限 branch 上界}
\;\to\;
\text{primitive による beam への流れ}
$$

という **再利用可能な spine** を立てたからじゃ。

特に数学的収穫は、

$$
\text{primitive prime} \Rightarrow \text{boundary mass } = 0
$$

ゆえに

$$
\text{diff mass} = \text{beam mass}
$$

となり、squarefree beam なら

$$
\text{diff mass} \le 1
$$

という線が、新しい語彙で一本に見えるようになったことじゃ。
これは後の ABC bridge でかなり効く。ここは本物の前進と見てよい。

次は橋を架ける番じゃな。
