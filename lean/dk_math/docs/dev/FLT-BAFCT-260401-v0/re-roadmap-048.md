# Re-roadmap: `2m-core` を最後の核候補として、ロードマップを全面的に書き換える

うむ、 **まだ閉じておらぬ**。
じゃが、悪い意味ではない。むしろ **「どこが閉じて、どこが最後まで残るのか」が、やっと正しく見えた** のじゃ。

前は、primitive 側の open kernel をかなり広く

$$
\text{PthRootCore} \;\to\; \text{one-step Hensel} \;\to\; \text{StrongSuperWieferich}
$$

の帯として見ておった。
ところが作業を進めた結果、Level 1s 側は provider 語彙まで direct concrete に閉じた。つまり、**one-step Hensel を整備すること自体が最終目的ではなくなった** のじゃ。`strongSuperWieferichCongruenceV2_concrete` と `strongSuperWieferichProvider_concrete` が入って、Level 1s は FLT 本線で必要な意味では concrete と見てよい段に入った。

だから、ぬしの言う通り **ルートは変わった**。
以前のロードマップは「Level 1s を閉じれば primitive 側が片付く」という形だったが、いまはそうではない。`QAdicDescentExistenceTarget` が本線へ刺さることが定理列で固定され、主戦場は完全に Level 2 側へ移った。しかもその後さらに整理が進んで、粗い `Level 2c` ではなく、`Level 2m`、さらにその中でも `2m-geom`、そして今は **`2m-core` が最終 1 核候補** だと見えておる。  

いまの読みを一番短く言うと、こうじゃ。

$$
\text{Level 0} \; \checkmark,\quad
\text{Level 1w} \; \checkmark,\quad
\text{Level 1s} \; \checkmark,
$$

残る本丸は

$$
\text{Level 2m-core}
$$

じゃ。
つまり「まだ閉じない」のではなく、**閉じるべき場所が、より深い一点へ圧縮された** のじゃ。

そしてロードマップも、もう前のままではない。
いまの新しい構成は、だいたい次の 3 段じゃ。

## 1. 旧ロードマップ

`PthRootCore` を中心にして、one-step Hensel の局所補題を順に閉じ、Level 1s を越えて primitive descent へ戻る構成。
これは途中までは正しかったが、最終的には **Level 1s が direct concrete に閉じた** ので、主ルートからは外れた。

## 2. 現在のロードマップ

`QAdicDescentExistenceTarget` を coarse bridge と見て、その中の open content を `Level 2m-int` と `Level 2m-geom` に分け、さらに bookkeeping を剥がして **`PrimeGe5BranchAPrimitiveQAdicGapReductionCoreTarget`** を最終 1 核候補として扱う構成。  

## 3. 次にやるべきこと

もう `PthRootCore` を中心に説明するより、 **`2m-core` を中心に議論を組み直す** のがよい。
具体的には、

$$
\text{pack} + \text{strong q-adic witness} \Rightarrow \exists g'
$$

の中で、

* truly local な部分
* genuinely global な部分
* まだ不要な仮定として剥がせる部分

を分離するのが次の勝負どころじゃ。履歴でも「`2m-core` の仮定をさらに削れるか」「local と global を分離する」が次課題とされておる。

だから賢狼の答えはこうじゃ。

**まだ閉じない。**
じゃが、それは迷っているからではない。
**ルートが一本化された結果、最後に残る核が `2m-core` だと分かった** からじゃ。
前は広い front を相手にしておった。今は最後の城門だけが残っておる。これはむしろ前進じゃよ。

いま必要なのは、旧ロードマップを捨てて、

$$
\text{Level 1s 完了}
\;\to\;
\text{Level 2c は bridge}
\;\to\;
\text{Level 2m-geom/core が本丸}
$$

という **新しいロードマップへ全面的に書き換えること** じゃ。
必要なら、次にその新ロードマップを図で起こすぞい。
