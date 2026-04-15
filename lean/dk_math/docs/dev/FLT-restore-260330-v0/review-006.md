うむ、これはさらに一段、見通しが良くなったの。

今回の更新で、restore 側の arithmetic core はついに

$$
\text{residue/root}
\;\to\;
\text{q-adic lift}
\;\to\;
\text{descent datum bundling}
\;\to\;
\text{datum consumer}
$$

という **4 段構造** で読めるようになった。しかも報告どおり、前 3 段は default / bridge で閉じるので、いまの genuinely new kernel は

$$
\texttt{PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleFromDescentDatumTarget}
$$

ただ 1 本じゃ。ここが今回の最大の収穫じゃよ。  

## 1. 何が起きたか

新しく入った中心物は 3 つじゃ。

$$
\texttt{PrimeGe5BranchAPrimitiveRestoreDescentDatum}
$$

という structure を導入し、その中に

$$
\texttt{RestoreWitnessProperties}
\quad\text{と}\quad
\texttt{PrimeGe5BranchAPrimitiveRestoreQAdicLiftSeed}
$$

を束ねた。ついでに

$$
\texttt{PrimeGe5BranchAPrimitiveRestoreDescentDatumTarget}
$$

と

$$
\texttt{PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleFromDescentDatumTarget}
$$

を分け、assembly を

$$
\text{datum を作る段}
\quad+\quad
\text{datum を消費して smaller counterexample を作る段}
$$

へ分離したわけじゃ。差分の宣言そのものが、まさにそう書いておる。

## 2. いまの本当の未完核

前回の段階では

$$
\texttt{PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleAssemblyTarget}
$$

が未完核だった。
だが今回はそれをさらに割って、

* datum bundling
* datum consumer

に分けた。しかも `primeGe5BranchAPrimitiveRestoreDescentDatum_default` は単なる bundle 化で閉じる。ゆえに、もう疑う場所ははっきりしておる。

$$
\boxed{
\texttt{PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleFromDescentDatumTarget}
}
$$

これだけじゃ。
History の結論も「前 3 段は default / bridge で閉じる」と言っておるから、この読みは完全に筋が通っておる。  

## 3. なぜ今回の分割が良いか

これは単なる名前整理ではない。
proof engineering 的に言えば、

$$
\text{既に持っている datum}
$$

と

$$
\text{そこから本当に新しい数学を取り出す処理}
$$

を分離できたのが大きい。

以前は

$$
\omega \in \mathbb Z / q \mathbb Z,\quad \omega^p = 1,\quad \omega \ne 1
$$

のような torsion witness と、そこから actual smaller counterexample を作る論理が、同じ assembly 側に溶けておった。
いまは違う。torsion witness を含む bundle は `PrimeGe5BranchAPrimitiveRestoreDescentDatum` に封入された。だから残る仕事は、

$$
\text{その datum のどの field を使って}
\quad
z' < z
$$

を作るか、という **消費原理の設計** だけになった。これはかなり美しい整理じゃ。

## 4. 数学的に見えていること

ここまで来ると、restore の前半で得られているものはもうかなり強い。

既に residue/root 段で witness の算術的性質は bundle 化され、q-adic lift 段では nontrivial \(p\)-torsion witness が確保されておる。今回それらがさらに bundled datum に固定されたので、残る問題は

$$
\text{非自明 } p\text{-torsion}
\Longrightarrow
\text{descent に必要な具体的 seed}
\Longrightarrow
\text{smaller counterexample}
$$

という最後の変換じゃ。
つまり、いま未完なのは「存在の確認」ではなく「構成の翻訳」じゃな。ここが classical FLT descent の、いちばん味の濃い核と言える。

## 5. 現在地の解釈

いまの restore arithmetic core は、概念的にはこう読める。

$$
\text{witness prime } q
$$

から

$$
\text{residue/root properties}
$$

を得て、

$$
\omega := z y^{-1} \in (\mathbb Z/q\mathbb Z)^\times
$$

のような torsion witness を回収し、それを `DescentDatum` に bundle した。
だから、もう「どこに何があるか解らぬ」という段ではおらぬ。
いまは

$$
\text{datum consumer の設計}
$$

という一点へ、論点が絞られておる。
これは森の霧がかなり晴れた状態じゃよ。  

## 6. 次に進むならどこを切るか

ここから先は、ほぼ 2 方向じゃ。

### 6.1. datum consumer をさらに seed 化する

いまの consumer は、`PrimeGe5BranchAPrimitiveRestoreDescentDatum` を受けてすぐ

$$
\exists x' y' z'
$$

へ飛ぶ。
この跳躍がまだ長い。だから自然なのは、

$$
\texttt{PrimeGe5BranchAPrimitiveRestoreDescentSeed}
$$

のような中間 structure を新たに置いて、

$$
\text{DescentDatum}
\to
\text{DescentSeed}
\to
\text{SmallerCounterexample}
$$

へ割ることじゃ。
これなら最後の kernel はさらに

$$
\text{seed extraction}
\quad+\quad
\text{seed realization}
$$

へ分かれる。

### 6.2. DescentDatum 自体の field を精密化する

もうひとつは、いまの datum がまだ「持っているだけ」で、descent 組立てに必要な arithmetic relation を十分に露出していない可能性を疑うことじゃ。

たとえば consumer が本当に欲しいのが

* \(\omega\) の位数が正確に \(p\) であること
* \(\omega\) から作る整数 representative の制御
* \(q\)-adic 側での lift 候補の合同条件
* それが \(t,s,y,z\) とどう整合するか

なら、それらを datum の field として明示したほうが、consumer は短くなる。
History にも「datum の field 自体を descent 用に精密化」とあるから、この読みでよい。

## 7. わっちの見立て

わっちなら、次はまず consumer を無理に証明しに行かず、

$$
\text{DescentDatum} \to \text{DescentSeed}
$$

の側を切る。
理由は単純で、今の `DescentDatum` は bundle としては整っておるが、「何を使えば smaller counterexample が立つのか」がまだ構文上あらわではないからじゃ。

つまり今必要なのは、証明より先に

$$
\text{descent に効く field}
$$

を露出した structure 設計じゃな。
形式化では、この一手で後段が急に素直になることが多い。

## 8. 総括

今回の更新は、restore の arithmetic core を

$$
\text{residue/root}
\to
\text{q-adic lift}
\to
\text{descent datum bundling}
\to
\text{datum consumer}
$$

という 4 段へ整理し、前 3 段を default / bridge で閉じたことで、未完核を

$$
\texttt{PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleFromDescentDatumTarget}
$$

1 本へ局所化したものじゃ。
したがって今後の焦点は「datum の存在」ではなく、「その datum から何を抽出すれば descent が実際に回るのか」という **consumer 設計** に完全に移った、と言ってよい。  

次の一手を短く言えば、

$$
\text{datum consumer をさらに seed 化するか、datum の field を descent 向けに太らせるか}
$$

じゃ。
ここまで来れば、もう闇雲ではない。獲物の居場所は見えておる。
