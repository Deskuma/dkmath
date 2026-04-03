# Review 032: Level 1 の本命を one-step Hensel に分解した

うむ、**これでよい**。
しかも今回は、前回の weak/strong 分離をさらに一段進めて、**Level 1 の本命を “Hensel step の反復問題” として書ける形にした**、という意味でかなり良い前進じゃ。`StrongSuperWieferichCongruenceV2Target` を `ZMod.castHom` ベースの正規形に直し、`HenselLiftStepGeomSumTarget` と `StrongSuperWieferichProviderTarget` を置いたことで、次に何を証明すればよいかが、もはや曖昧ではなくなった。

まず、今回の変更の価値を一言で言うと、**「Strong を本命として分離した」段階から、「Strong を one-step 補題の反復で供給する設計」へ進んだ** ことじゃ。
前回は「弱い達成」と「本命未達」を型で切り分けたのが成果じゃった。今回はそこからさらに、

$$
\text{Hensel 1-step} ;\Longrightarrow; \text{Strong V2}
$$

という供給口を置いた。つまり Level 1 本丸が、ただの理想論でなく **実装単位に分解された** のじゃ。これは設計としてかなり正しい。

特に良いのは、`StrongSuperWieferichCongruenceV2Target` で branch 条件を `castHom` で正規化したところじゃ。
これで

* mod (q) の branch 情報
* mod (q^n) の近似根
* mod (q^{n+1}) の持ち上げ

が、同じ語彙で一直線につながる。前の strong 版でも方向は正しかったが、今回の V2 で **Hensel step とそのまま噛み合う型** になった、というのが大きい。

ただし、慎重に言うぞい。
今回 **数学が一気に解けた** わけではない。進んだのは主に **型設計と攻略導線の明確化** じゃ。`HenselLiftStepGeomSumTarget` と `StrongSuperWieferichProviderTarget` は、いまはまだ「次に証明すべき target」を固定した段階であって、その concrete proof そのものはまだこれからじゃ。だから評価としては、

* **設計前進** は大きい
* **証明前進** はこれから Level 1s 本番

と読むのが正確じゃ。

戦況図としては、いまこう読むのがいちばん自然じゃ。

$$
\text{Level 0: QAdicResidue} \quad \checkmark
$$

$$
\text{Level 1w: WeakSuperWieferich} \quad \checkmark
$$

$$
\text{Level 1s: StrongSuperWieferich} \quad \text{open}
$$

$$
\text{Level 2: QAdicDescentExistence} \quad \text{open}
$$

そして今回の変更で、Level 1s は「抽象的な open」ではなく、**one-step Hensel を積み上げれば届く場所** として見えるようになった。これが最大の収穫じゃ。履歴側でも、`Level 1w (Weak)` と `Level 1s (Strong)` を分離表示し、Level 1 の本命が完全に分離されたと整理しておる。

ゆえに、「これでよいのか？」への賢狼の答えはこうじゃ。

**はい、よい。しかも必要な段階じゃ。**
今の変更で、ようやく Level 1 の本命が **“Hensel 1-step の concrete 証明”** という形に落ちた。これなしに Strong を直接殴るのは、どうしても霧の中を斬ることになる。いまはその霧が晴れ、敵の姿が「`HenselLiftStepGeomSumTarget`」として見えた状態じゃ。

一方で、まだ注意すべき点もある。
Level 1s が閉じても、Level 2 の `QAdicDescentExistence` は別問題として残る。つまり今回の作業は **本丸手前の最後の補給路整備** であって、最終矛盾そのものではない。だが、この整備がないと Level 2 に到達したとき、局所-大域ギャップと Hensel 不足が混ざって見えてしまう。今はそれをちゃんと分離できた。そこが強い。

なので、次の一手としては報告の見立てどおり、**`HenselLiftStepGeomSumTarget` の concrete 証明** に進むのが最善じゃ。
それが通れば、

$$
\text{one-step} \Rightarrow \text{iteration} \Rightarrow \text{Strong V2}
$$

の道がはっきりし、Level 1s は本当に制圧される。そこで初めて、残る open kernel が Level 2 だけだと胸を張って言えるようになる。

ひとことでまとめると、
**今回の変更は「正しい方向」どころか、Level 1 攻略を実際の補題単位へ落としたという意味で、かなり良い設計前進じゃ。次は one-step の concrete 化が本命、その先で反復補題へ進むのが筋じゃよ。**
