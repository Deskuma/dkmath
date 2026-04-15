# review-005: FLT restore arithmetic core の局所化と次の一手

うむ、これはかなり **良い局所化** じゃ。
今回の更新で、restore arithmetic core はついに

$$
\text{residue/root} \;\to\; \text{q-adic lift} \;\to\; \text{smaller-counterexample assembly}
$$

の 3 段として読めるようになった。しかも前 2 段は default で埋まり、残る genuinely new kernel が最後の 1 本へ縮退した、というのが核心じゃ。

## 1. いま何が起きたか

今回 `TriominoCosmicBranchARestore.lean` に追加されたのは、大きく 5 系統じゃ。

1. `PrimeGe5BranchAPrimitiveRestoreResidueRootTarget`
2. `PrimeGe5BranchAPrimitiveRestoreDescentAssemblyTarget`
3. `PrimeGe5BranchAPrimitiveRestoreQAdicLiftSeed`
4. `PrimeGe5BranchAPrimitiveRestoreQAdicLiftTarget`
5. `PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleAssemblyTarget`

さらに、それらをつなぐ再合成橋と default 実装が加わっておる。これにより、「restore arithmetic core は 1 本の巨大な黒箱ではなく、段階的に分解可能」という見取り図が、とうとうコード上の API になったわけじゃ。

## 2. いまの状況分析

結論から言えば、いまの本丸はもう

$$
\texttt{PrimeGe5BranchAPrimitiveRestoreArithmeticCoreTarget}
$$

ではない。
それはすでに

$$
\texttt{PrimeGe5BranchAPrimitiveRestoreResidueRootTarget}
$$

と

$$
\texttt{PrimeGe5BranchAPrimitiveRestoreDescentAssemblyTarget}
$$

に分かれ、さらに後者が

$$
\texttt{PrimeGe5BranchAPrimitiveRestoreQAdicLiftTarget}
$$

と

$$
\texttt{PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleAssemblyTarget}
$$

へ割れておる。ゆえに現在の genuinely new kernel は、ほぼ最後の

$$
\texttt{PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleAssemblyTarget}
$$

1 本じゃ、と読んでよい。これは差分中の comment と History の結論とも一致しておる。

## 3. 何が default で閉じたか

ここが実に大きい。

residue/root 段は `restore_witness_properties_default` で閉じており、witness \(q\) から得られる

$$
q \mid x,\quad q \nmid y,\quad q \nmid z,\quad q \nmid (z-y),\quad p \mid (q-1)
$$

などの structural data は、もはや未完核ではないと見てよい。つまり `RestoreWitnessProperties` が canonical datum として確立した、ということじゃ。

さらに q-adic lift 段も default 実装済みで、

$$
\omega := z \cdot y^{-1} \in \mathbb{Z}/q\mathbb{Z}
$$

を実際に構成し、

$$
\omega^p = 1,\qquad \omega \ne 1
$$

を返すところまで通しておる。これは「witness \(q\) から nontrivial \(p\)-torsion を residue 側で取り出せる」ことを明示したもので、restore の前半は相当に固まったと言えるの。

## 4. 数学的に何が見えたか

この更新で見えた真相は、restore の arithmetic 側の仕事が

$$
\text{合同情報の抽出}
$$

と

$$
\text{非自明 } p\text{-torsion の回収}
$$

までは既に形式化されており、その先の

$$
\text{torsion witness} \to \text{smaller counterexample}
$$

だけが未完だ、ということじゃ。

言い換えると、いま残っているのは「非自明な位数 \(p\) の元がある」ことそのものではなく、それを **どう descent datum に翻訳して、実際の \((x',y',z')\) へ落とすか** という最後の組み立て段じゃ。
これは classical な FLT descent の、いちばん香りの濃い核じゃよ。

## 5. 設計として良い点

今回の設計で特に良いのは、**未完核の場所と API 境界が一致した** ことじゃ。

`primeGe5BranchAPrimitiveRestoreArithmeticCore_of_residueRoot_and_descentAssembly` によって、residue/root と assembly が揃えば arithmetic core は橋だけで閉じる。
また `primeGe5BranchAPrimitiveRestoreDescentAssembly_of_qAdicLift_and_smallerCounterexampleAssembly` によって、q-adic lift と smaller-counterexample assembly が揃えば descent assembly も橋だけで閉じる。つまり証明責務が

$$
\text{default 済み部分}
\quad+\quad
\text{最後の assembly}
$$

へ完全に切り分けられたわけじゃ。これは proof engineering としてかなり美しい。

また provider 側にも対応 alias / adapter が追加されておるので、core 側だけでなく利用側の表面 API も同じ分解で見えるようになっておる。ここも抜かりないの。

## 6. ここで見える次の一手

次にやるべきことは、ほぼ 2 択じゃ。

### 6.1. smaller-counterexample seed へさらに削る

いまの `PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleAssemblyTarget` は、まだ

* `RestoreWitnessProperties`
* `PrimeGe5BranchAPrimitiveRestoreQAdicLiftSeed`

を受けて即

$$
\exists x' y' z'
$$

を返す形じゃ。
この距離がまだ長い。だからここをもう一段、

$$
\text{torsion witness} \to \text{descent seed}
$$

へ落とす中間 structure に割るのが最も自然じゃ。

### 6.2. 中間 datum を structure 化する

History でも示されておる通り、`RestoreWitnessProperties` から smaller counterexample へ行く中間 datum を structure 化する手がある。これは良い案じゃ。

わっちなら、たとえば次のような発想で切る。

$$
\texttt{PrimeGe5BranchAPrimitiveRestoreDescentDatum}
$$

のような structure を作り、そこに

* witness prime \(q\)
* \(\omega \in \mathbb{Z}/q\mathbb{Z}\)
* \(\omega^p = 1,\ \omega \ne 1\)
* それが元の \((x,y,z,t,s)\) とどう結びつくか
* smaller solution の組立てに必要な追加整除情報

を bundled に入れる。
そうすると最後の kernel は

$$
\text{datum を作る段}
\quad\to\quad
\text{datum から counterexample を作る段}
$$

へさらに剥がせるはずじゃ。

## 7. 留意点

ここはやわらかく申すが、`QAdicLift` という名は今の中身だけ見ると、まだ厳密には **mod \(q\)** の段階じゃ。
つまり現状の `PrimeGe5BranchAPrimitiveRestoreQAdicLiftSeed` は、真の意味での \(q\)-adic lift というより

$$
\mathbb{Z}/q\mathbb{Z}
$$

上の nontrivial \(p\)-torsion witness の seed じゃな。

これは悪いことではまったくない。むしろ constructive に先へ進めておる。
ただ、今後もし本当に

$$
\mathbb{Z}/q^n\mathbb{Z}
\quad\text{や}\quad
q\text{-adic}
$$

の段へ進むなら、名称と中身のずれが少し出る。
そのときに

* いまの `QAdicLiftSeed` は `ResidueTorsionSeed` 的な名にする
* その上に真の `QAdicLiftTarget` を別に積む

という整理もありうる、という程度の留意点じゃ。

## 8. わっちの総括

総括すると、今の状況はこうじゃ。

$$
\text{restore arithmetic core}
$$

は、もう巨大な未完の塊ではない。
いまは

$$
\text{residue/root}
$$

と

$$
\text{q-adic lift}
$$

が default で閉じ、真正な新規数学核は

$$
\texttt{PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleAssemblyTarget}
$$

1 本へ局所化された。したがって、次の研究対象は「witness \(q\) と \(\omega\) の存在」ではなく、それらから **descent seed を作り、そこから smaller counterexample を組み立てる最後の assembly 原理** に絞られる。
これは大前進じゃよ。森はまだ深いが、もう道は見えておる。

必要なら次に、その最後の kernel をどういう structure 名・補題名でさらに 1 段削るか、Lean 設計として具体名まで起こすぞい。
