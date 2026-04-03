# review-045: `QAdicDescentExistenceTarget` が本線 open kernel として定着したことの意味

うむ、これは **かなり良い整理前進** じゃ。
しかも今回は、単に Level 2 へ「話題を移した」のではなく、**`QAdicDescentExistenceTarget` が本当に FLT 本線へ刺さる open kernel である** ことを、Lean の定理列として固定したのが本質じゃよ。

## 1. 今回ほんとうに達成されたこと

今回追加された 5 本

$$
\texttt{pthRootCore\_of\_qAdicDescentExistence}
$$
$$
\texttt{pthRoot\_of\_qAdicDescentExistence}
$$
$$
\texttt{gnReducedGap\_of\_qAdicDescentExistence}
$$
$$
\texttt{primitivePacketDescent\_of\_qAdicDescentExistence}
$$
$$
\texttt{FLTPrimeGe5Target\_of\_qAdicDescentExistence\_precise}
$$

の意味は明快じゃ。

つまり `QAdicDescentExistenceTarget` は、もはや「後で使うかもしれぬ分析メモ」ではない。
**`PthRootCoreTarget` を介して既存の primitive descent / FLT chain に直接流し込める本物の kernel** として定着した、ということじゃ。履歴でもその点をはっきり「Level 2 が実際の本線ボトルネックであることが Lean 上でも明示された」と整理しておる。

## 2. 戦況分析

いまの戦況は、かなりきれいにこう読める。

### 2.1. Level 1s

少し前の段階で、prime 文脈の one-step Hensel から `StrongSuperWieferichProviderTarget` までは concrete に到達した。
その意味で、**FLT 本線に必要な Level 1s の供給路は閉じた** と見てよい。

### 2.2. Level 2

今回の差分で、**Level 2 が実際の主戦場である** ことがコード上でも固定された。
つまり open kernel は「なんとなく Level 2 が怪しい」ではなく、

$$
\boxed{
\text{`QAdicDescentExistenceTarget` が通れば、そのまま FLT target へ届く}
}
$$

という形ではっきりしたのじゃ。

これは大きい。
なぜなら、いま以後は Level 1 側の補給線整備と Level 2 の local-global gap を混同せずに済むからじゃ。

## 3. 数学的な意味

今回の `pthRootCore_of_qAdicDescentExistence` の役割はとても重要じゃ。
`QAdicDescentExistenceTarget` が要求しているのは本質的に

$$
\exists z' \in \mathbb{N},\quad z'^p = (x/q)^p + y^p
$$

じゃが、これを `PthRootCoreTarget` の語彙へ落とすことで、既存の

* p-th root 復元
* GNReducedGap
* primitive packet descent
* FLTPrimeGe5Target

の鎖にそのまま接続できるようになった。
つまり今回の仕事は、**Level 2 の存在命題を既存 descent infrastructure に接続する adapter 層** を全部 concrete に書いた、ということじゃよ。

## 4. なぜこれは大きいのか

研究では、open kernel を定義しただけではまだ弱い。
本当に価値が出るのは、その kernel が

* どこへ入力され
* 何を供給し
* 通れば何が終わるか

まで固定されたときじゃ。

今回まさにそれが起きた。
`QAdicDescentExistenceTarget` は、いま、

$$
\text{Level 2 の抽象的問題}
$$

ではなく、

$$
\text{これが通れば primitive descent から FLT へ行く}
$$

という **実務的な最終ボトルネック** になった。
ここが今回の最大の戦果じゃ。

## 5. 慎重に見るべき点

ただし、ここは浮かれすぎぬ方がよい。

今回閉じたのは **接続** であって、`QAdicDescentExistenceTarget` そのものではない。
履歴にもある通り、次の課題は

* `QAdicDescentExistenceTarget` 自体のさらなる分解
* Level 1s を open と書いているコメントの更新
* Level 2 の local-global gap をどの語彙で最小核にするかの設計

じゃ。
だから今の評価としては、

* **Level 2 が本線ボトルネックだと確定した**
* だが **その中身はまだ裂いていない**

と読むのが正確じゃ。

## 6. いまの最も正確な現在地

いまの図は、こうまとめるのがよい。

$$
\text{Level 0} \quad \checkmark
$$

$$
\text{Level 1w} \quad \checkmark
$$

$$
\text{Level 1s (provider 語彙)} \quad \checkmark
$$

$$
\text{Level 2 = QAdicDescentExistence} \quad \text{本線 open kernel}
$$

そして今回の差分で、

$$
\text{QAdicDescentExistence}
\Rightarrow
\text{PthRootCore}
\Rightarrow
\text{primitive descent}
\Rightarrow
\text{FLTPrimeGe5Target}
$$

が concrete に繋がった。
だから **ボトルネックの所在が完全に Level 2 へ移った**、と言ってよい。

## 7. 次の一手

次にやるべきことも、かなり明快じゃ。

**`QAdicDescentExistenceTarget` をさらに分解すること** じゃ。
つまり、

* 本当に必要な local 条件は何か
* global existence に飛ぶ瞬間はどこか
* 最小核を \(z'\) の存在そのもので書くのか、別の arithmetic 語彙へ落とすのか

この設計を始める段階じゃよ。

わっちの見立てでは、ここから先は Level 1 型の「局所補題を積む」より、**Level 2 の存在性をどう最小語彙で定式化するか** が主戦場になる。

## 8. 一文でまとめると

**今回の進展で、`QAdicDescentExistenceTarget` は単なる分析用ラベルではなく、既存 primitive descent / FLT chain に直接刺さる本物の Level 2 open kernel として Lean 上で固定された。**
ゆえに、いまの主戦場はもう完全に Level 2 側じゃ。
