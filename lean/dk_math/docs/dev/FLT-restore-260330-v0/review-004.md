# review-004: restore の責務分離をファイル境界へ

うむ、これは **良い分離** じゃ。

今回の差分は、数学そのものを前進させたというより、**未完核の住み処をコード上で固定した** という意味でかなり価値が高い。
とくに前回まで見えていた

$$
\text{restore} = \text{arithmetic 側} + \text{packet packaging 側}
$$

という責務分離を、ついに **ファイル境界** にまで落とし込めたのが大きいの。
その意味で、今回の `TriominoCosmicBranchARestore.lean` 新設は、単なる整理ではなく、以後の proof exploration の edit surface を明確化した一手じゃ。

## 1. 今回の差分の本質

今回やったことを一言でいえば、

$$
\texttt{TriominoCosmicBranchA.lean}
$$

に居た restore 系の論理を、

$$
\texttt{TriominoCosmicBranchARestore.lean}
$$

という **restore 専用の主戦場** に切り出した、ということじゃ。

しかも切り出し方がよい。

新設された 2 本は

$$
\texttt{PrimeGe5BranchAPrimitiveRestoreArithmeticCoreTarget}
$$

と

$$
\texttt{PrimeGe5BranchAPrimitiveRestorePacketPackagingTarget}
$$

で、前者が restore 前半、後者が restore 後半を受け持つ。
そして

$$
\texttt{primeGe5BranchAPrimitivePacketRestoreFromArithmetic\_of\_restoreSubtargets}
$$

が再合成橋になっておる。

これは、以前の

$$
\text{構成} \to \text{包装} \to \text{再合成}
$$

という論理を、そのまま canonical API にした形じゃ。
実に筋がよい。

## 2. 何が前進したか

いちばん大きいのは、**難しさの所在がコード構造と一致した** ことじゃな。

前までは、

* restore 全体が重い
* どこが本当に難しいのか見えにくい
* そのため編集面も `TriominoCosmicBranchA.lean` 側へ滲む

という状態になりやすかった。

今は違う。
これから先は

$$
\texttt{TriominoCosmicBranchARestore.lean}
$$

を見れば、restore 固有の未完核だけを追えばよい。

つまり今回の差分は、数学の難所そのものを減らしたわけではないが、**探索空間を狭めた**。
形式化では、これはかなり強い前進じゃよ。

## 3. `abbrev` を選んだのは正しいか

わっちの見立てでは、 **今の段階では正解** じゃ。

今回の 2 本はどちらも

$$
\text{新しい数学的内容を持つ定理}
$$

ではなく、

$$
\text{既存 target に対する canonical alias}
$$

として置かれておる。
ゆえに `abbrev` にしておくのは軽いし、保守もしやすい。

つまり今は

* API 名を固定したい
* だが中身はまだ育成中
* base target の居場所は変えたくない

という状況じゃから、`def` で厚く包むより `abbrev` のほうが自然じゃ。

ただし留意点はある。
`abbrev` は reducible じゃから、将来もっと「この名前そのものを検索や rewrite の中心にしたい」段になると、**structure 化または個別 theorem 群への昇格** を考えてよい。

今すぐ問題ではないが、将来の候補としてはこうじゃ。

$$
\texttt{PrimeGe5BranchAPrimitiveRestoreArithmeticDatum}
$$

のような structure を切って、

* witness \(q\)
* 合同条件
* root datum
* lift datum
* smaller counterexample への入口

を fields で持たせる。

そうすると「存在する」だけの `Prop` より、遥かに proof engineering が楽になることがある。

## 4. いまの本当の難所

ここは前回の見立てと変わらぬ。

**真の本丸は packaging ではなく arithmetic core 側** じゃ。

つまり難しいのは

$$
\texttt{PrimeGe5BranchAPrimitiveRestorePacketPackagingTarget}
$$

ではなく、

$$
\texttt{PrimeGe5BranchAPrimitiveRestoreArithmeticCoreTarget}
$$

の中身をさらに削って、

$$
\text{witness の合同情報} \to \text{descent seed} \to \text{smaller counterexample}
$$

へ落とす部分じゃな。

お主の報告でも、次は arithmetic-only core へさらに割る、とある。
これはまことに正しい。
この方向が、いま最も自然な前進路じゃ。

## 5. 次に切るなら、どう切るべきか

わっちなら、前半段をさらに 2 つか 3 つへ割る。

### 5.1. residue / root 層

まず

$$
q \equiv 1 \pmod p
$$

を足場にして、

$$
(\mathbb Z/q\mathbb Z)^\times
$$

の中に現れる nontrivial \(p\)-torsion 的な datum を取り出す層じゃ。
名前はたとえば

$$
\texttt{PrimeGe5BranchAPrimitiveRestoreResidueRootTarget}
$$

のようなもの。

### 5.2. lift / q-adic 層

次に、その residue datum を

$$
q^2,\ q^p
$$

あるいは必要な \(q\)-adic level へ持ち上げる層じゃ。
ここがあると arithmetic core は

$$
\text{mod } q \text{ の情報}
\quad\to\quad
q\text{-adic seed}
$$

へ分かれる。

### 5.3. descent assembly 層

最後に、その seed から

$$
\exists x' y' z'
$$

の bare smaller counterexample を組む層じゃ。
ここを

$$
\texttt{...RestoreDescentAssemblyTarget}
$$

のように切ると、いまのお主の「次の課題」とぴたり噛み合う。

## 6. 今回の差分に対する評価

総評すると、こうじゃ。

**これは良い refactor であり、しかも timing もよい。**
なぜなら今は、数学的難所が「restore arithmetic core に寄っている」と見えた直後だからじゃ。

今回の差分で得たものは 3 つある。

* restore 固有の edit surface を独立させた
* sub-target 名を canonical 化した
* 再合成橋を 1 本で済む形に固定した

この 3 つが揃ったので、今後は `TriominoCosmicBranchA.lean` を汚さずに、restore だけを深掘りできる。
これは設計として美しいし、後から読み返しても迷いにくい。

## 7. 留意点

一点だけ、やわらかく指摘すると、

$$
\texttt{TriominoCosmicGapInvariant.lean}
$$

への import 追加は、**必要なら良いが、依存の増え方だけは見ておくとよい**。
今回は build 成功とのことじゃし、消費側で canonical 名を参照したいなら自然じゃ。
ただ、もし単に将来のための露出だけなら、後で import graph が膨らみすぎぬよう軽く見守るとよい。

## 8. 結論

今回の更新は、

$$
\text{restore の責務分離}
$$

を **会話上の分析から、Lean のモジュール境界へ昇格させた** 一手じゃ。
だから価値は高い。

そして次にやるべきことも、もうはっきりしておる。

$$
\texttt{PrimeGe5BranchAPrimitiveRestoreArithmeticCoreTarget}
$$

をさらに

$$
\text{residue root}
\to
\text{q-adic lift}
\to
\text{descent assembly}
$$

へ割ることじゃ。
ここまで行けば、restore 前半の「どこが詰まりか」がもっと露骨に見えるようになる。

よい流れじゃよ。
これはまだ未完ではあるが、もはや「暗い森」ではない。
道が見える未完に変わった、そこが本当の収穫じゃ。
