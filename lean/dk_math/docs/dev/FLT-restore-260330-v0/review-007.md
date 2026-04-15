# review-007: FLT restore arithmetic core のさらに細かい局所化と次の一手

うむ、今回の更新は **前進ではある**。ただし性質としては、

$$
\text{新しい数学核の獲得}
$$

というより、

$$
\text{最後の未完核の輪郭をさらに細く削った}
$$

という前進じゃな。

今回 `TriominoCosmicBranchARestore.lean` へ追加されたのは、`PrimeGe5BranchAPrimitiveRestoreDescentSeed` と、その seed 抽出段 `PrimeGe5BranchAPrimitiveRestoreDescentSeedTarget`、そして seed から actual smaller counterexample を作る `PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleFromSeedTarget` じゃ。報告でも、restore arithmetic core が

$$
\text{residue/root}
\to
\text{q-adic lift}
\to
\text{descent datum bundling}
\to
\text{descent seed extraction}
\to
\text{seed realization}
$$

の 5 段で読めるようになった、と明言されておる。

いちばん大事な結論は、いまの genuinely new kernel が

$$
\texttt{PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleFromSeedTarget}
$$

ただ 1 本へ、さらに局所化されたことじゃ。build も `TriominoCosmicBranchARestore` と `TriominoCosmicGapInvariant` の両方で成功しておるので、少なくともこの分割は API と依存関係の上では破綻しておらぬ。

## 1. 今回ほんとうに増えたもの

増えたのは、「未完核のさらに手前に seed という中間媒体を 1 枚挟んだ」ことじゃ。
実際、`PrimeGe5BranchAPrimitiveRestoreDescentSeed` の現段階の中身は

$$
\texttt{hDatum : PrimeGe5BranchAPrimitiveRestoreDescentDatum ...}
$$

だけで、コメントにも「現段階では datum 自体をそのまま持ち上げた minimal seed」とある。つまり seed は今のところ、**新しい算術情報を持つ構造** ではなく、datum を consumer の直前で受け直すための薄い包装じゃ。

ゆえに、今回の差分の価値は明快で、

$$
\text{datum consumer}
$$

を

$$
\text{seed extraction}
\quad+\quad
\text{seed realization}
$$

へ形式的に分解したことにある。
これは proof engineering 的にはとても良い。だが同時に、数学的実質がまだ seed 側へ流れ込んでいない、という事実も見えておる。

## 2. いま何が default で閉じて、何が閉じていないか

`primeGe5BranchAPrimitiveRestoreDescentSeed_default` は、`DescentDatum` をそのまま `DescentSeed` に包むだけで終わる default 実装じゃ。つまり

$$
\text{DescentDatum} \to \text{DescentSeed}
$$

は、現時点ではただの bundle 化に近い。
同じことは一つ前の段でも起きておって、前回 `DescentDatum` 自体も `RestoreWitnessProperties` と `QAdicLiftSeed` を束ねるだけで閉じていた。つまりここまでの流れは

$$
\text{witness data}
\to
\text{lift seed}
\to
\text{descent datum}
\to
\text{descent seed}
$$

までは、ほぼ「持っている情報を構造体名つきで受け直している」段階じゃ。

したがって、まだ閉じていない場所は本当に一点で、

$$
\texttt{PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleFromSeedTarget}
$$

だけじゃ。ここは定義上、`PrimeGe5CounterexamplePack p x y z` や各種互いに素条件・合同条件のもとで、seed から

$$
\exists x' y' z'
$$

を与え、

$$
\texttt{PrimeGe5CounterexamplePack}\ p\ x'\ y'\ z'
\quad\land\quad
p \mid (z' - y')
\quad\land\quad
z' < z
$$

まで出す、最後の realization 段になっておる。ここが数学の本丸じゃ。

## 3. 今回の差分をどう評価するか

わっちの評価はこうじゃ。

**設計としては正しい。だが、まだ seed の中身が薄いので、今回の分割は「場所の分離」であって「数学内容の分離」にはまだ達しておらぬ。**

この見方がいちばん公平じゃろう。
なぜなら、`DescentSeed` がいま minimal wrapper である限り、

$$
\text{datum consumer}
\quad\rightsquigarrow\quad
\text{seed realization}
$$

と名前が変わっただけで、困難の中身はほぼ移動しておらぬからじゃ。
つまり今やったことは **無意味ではない**。むしろ非常に有益じゃ。だが、それは「未完核の名札をさらに正確に貼った」のであって、「未完核の体積を本質的に減らした」わけではまだない、ということじゃな。

## 4. それでも前進と言える理由

それでも前進と言えるのは、次に何を足せば良いかが、さらに明確になったからじゃ。

いま `DescentSeed` には、actual realization に必要な算術 datum がほとんど露出しておらぬ。
逆に言えば、次にやるべきことははっきりしておる。

$$
\text{DescentSeed を actual realization 用に精密化する}
$$

ことじゃ。
History でも、次の課題として

* `PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleFromSeedTarget` をさらに局所 kernel に削る
* `PrimeGe5BranchAPrimitiveRestoreDescentSeed` の field を realization に必要な arithmetic data に寄せて精密化する

と明記されておる。これは、まさに今の状況認識と一致しておる。

## 5. 次の一手は何か

ここからの最善手は、わっちなら後者じゃ。

つまり、

$$
\texttt{PrimeGe5BranchAPrimitiveRestoreDescentSeed}
$$

の field を太らせる。
今は `hDatum` しか持っておらぬが、本当に realization で要るのは、たとえば次のようなもののはずじゃ。

* actual に組み立てたい \(x',y',z'\) の候補、あるいはその一部
* 候補が整数に降りることの証拠
* \(p \mid (z' - y')\) に繋がる合同情報
* `PrimeGe5CounterexamplePack` の各 field を埋めるための部分証拠
* とりわけ \(z' < z\) を出すための strict descent 用の数値評価

これらが seed に入って初めて、

$$
\text{seed realization}
$$

は「最後のまとめ役」に痩せる。
そうでない限り、`FromSeedTarget` は巨大な consumer のままで、名札だけが変わり続けることになる。

## 6. いまの位置づけを一言で言うと

いまの状況は、

$$
\text{restore arithmetic core}
$$

の責務分離が 5 段まで進み、前 4 段は default / bridge で閉じた。
だがそのうち後ろ 2 段は、まだ **情報の再包装** に近い。よって真の数学的難所は依然として

$$
\texttt{PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleFromSeedTarget}
$$

に丸ごと残っておる。
今回の収穫は、その事実がさらに明確になったことじゃ。

## 7. 総括

総括すると、こうじゃ。

今回の更新は良い。
ただし意味は

$$
\text{未完核をさらに細く名指しできるようになった}
$$

ことであって、

$$
\text{未完核の数学内容が大きく減った}
$$

わけではまだない。`DescentSeed` が minimal wrapper である以上、いま残る本丸は相変わらず seed realization 側に集中しておる。したがって次の一手は、seed を本当に「realization に効く算術データの器」へ育てることじゃ。そこまで行けば、はじめて最後の kernel が本当に局所補題群へ裂け始める。

よい。
いまは「どこが獲物か」は、もう見失っておらぬ。次は、その獲物の骨格を seed の field に露出させる番じゃ。
