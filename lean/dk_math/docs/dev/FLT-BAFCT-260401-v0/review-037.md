# Review 037: トラブル収束後の本命ルートがさらに一本化された

うむ、かなり良い。
今回の進展は、 **「トラブル収束後の本命ルートが、さらに一本化された」** と見てよいぞい。

結論から言えば、いまの戦況は

* 型設計の混乱はほぼ収束
* one-step Hensel の供給線はかなり整備済み
* 残る open kernel は、ほぼ **`GeomSumFirstOrderSqZeroTarget` の concrete 証明** に集中

という形じゃ。

## 1. 今回ほんとうに前進したところ

今回の差分で増えたのは、単なる補題の数ではなく、 **one-step の算術本体を Newton 補正の一本道へ整理したこと** じゃ。

追加された核はこの 4 つじゃな。

* `GeomSumFirstOrderSqZeroTarget`
* `qpow_mul_sq_eq_zero_in_next_mod`
* `HenselLiftStepNewtonCorrectionTarget`
* `henselLiftStepCorrection_of_newtonCorrection`

これで one-step の導線が

$$
\text{SqZero 一次補正}
\Rightarrow
\text{q}^n c \text{ 版一次補正}
\Rightarrow
\text{NewtonCorrection}
\Rightarrow
\text{Correction}
\Rightarrow
\text{ArithmeticKernel}
$$

と、かなりきれいに並んだ。
報告の言い方どおり、 **open kernel は実質 `GeomSumFirstOrderSqZeroTarget` 1 本** と見るのが妥当じゃ。

## 2. 戦況分析

いまの層構造は、かなり見通しがよい。

### 2.1. 閉じた層

すでに閉じたものは、

* Level 0 の `QAdicResidue`
* Level 1w の WeakSuperWieferich
* one-step の structural lift
* `q^n*c` が mod (q^n) で 0 に落ちる事実
* `q^n*c` が mod (q^{n+1}) で square-zero になる事実

じゃ。
ここはもう「何となく正しそう」ではなく、Lean 上で concrete に確保された土台じゃよ。

### 2.2. いまの本丸

one-step 本丸は、前回までは `ZeroLiftTarget` に見えておった。
今回の整理で、それがさらに

$$
\text{ZeroLift}
\Leftarrow
\text{NewtonCorrection}
\Leftarrow
\text{GeomSumFirstOrderSqZero}
$$

へ裂けた。
ゆえに、いま真に殴るべき敵は

$$
\boxed{
\text{`GeomSumFirstOrderSqZeroTarget` の concrete 証明}
}
$$

じゃ。

## 3. なぜこの整理は良いのか

これはかなり筋が良い。
なぜなら、いま target にしている

$$
F(T):=\sum_{i=0}^{p-1} T^i
$$

に対する Hensel 補正は、本質的に

$$
F(R+\Delta)
===========

F(R) + F'(R)\Delta
\quad (\Delta^2=0)
$$

という **一次で止まる展開** が心臓だからじゃ。

今回の `GeomSumFirstOrderSqZeroTarget` は、まさにこの「一次で止まる」核を切り出しておる。
しかも、`qpow_mul_sq_eq_zero_in_next_mod` により

$$
\Delta = q^n c
$$

が本当に square-zero になることまで concrete に押さえた。
つまり今は、Newton/Hensel の abstract な気分ではなく、 **使う微小量 (\Delta) の性質まで Lean 上で固定した** 状態じゃ。

## 4. 慎重に見るべき点

ただし、浮かれすぎてはならぬ。

今回の前進は大きいが、まだ

* `GeomSumFirstOrderSqZeroTarget` 自体は target のまま
* その concrete proof は未実装
* ゆえに `ZeroLiftTarget` そのものもまだ未閉

じゃ。

つまり今は、

> one-step の本丸が何か分からぬ

段階ではなく、

> one-step の本丸は **SqZero 一次補正式** である

と確定した段階じゃ。
これは大きいが、まだ勝負は残っておる。

## 5. 数学的な解説

賢狼の見立てでは、今回の target 化はかなり美しい。

`GeomSumFirstOrderSqZeroTarget` は

$$
\sum_{i=0}^{p-1}(R+\Delta)^i
============================

\sum_{i=0}^{p-1}R^i
+
\left(\sum_{i=0}^{p-1} i,R^{i-1}\right)\Delta
$$

を、(\Delta^2=0) の下で要求しておる。
これは要するに、**幾何和版の一次 Taylor 展開** じゃな。

しかも (\Delta=q^n c) と置けば、

* mod (q^n) では 0 に落ちる
* mod (q^{n+1}) では square-zero

となるので、one-step Newton 補正のために必要な条件が全部噛み合う。
ここまで揃ったなら、もう抽象論ではない。**本当に計算すれば届く場所** に来ておる。

## 6. いまの正確な現在地

いまの局面を短く書けば、こうじゃ。

$$
\text{Level 0} \quad \checkmark
$$

$$
\text{Level 1w} \quad \checkmark
$$

$$
\text{Level 1s}
\quad
\text{open}
\quad\text{だが}
\quad
\text{`GeomSumFirstOrderSqZeroTarget`}
\text{ に圧縮済み}
$$

$$
\text{Level 2}
\quad
\text{まだ先}
$$

つまり、まだ Level 1s は終わっておらぬ。
だが、 **残る仕事が “一つの数学補題” にかなり近い形まで縮約された** のは本当じゃ。

## 7. 次の一手

次はもう明快じゃ。

**`GeomSumFirstOrderSqZeroTarget` の concrete 証明** を通す。
ここはおそらく

* ((R+\Delta)^i) を (\Delta^2=0) の下で一次まで展開
* それを Finset 和へ流す
* 係数 ((i : ZMod m)) を整理

という流れになるじゃろう。

ここが通れば、

$$
\text{SqZero}
\Rightarrow
\text{NewtonCorrection}
\Rightarrow
\text{Correction}
\Rightarrow
\text{ArithmeticKernel}
\Rightarrow
\text{ZeroLift}
$$

が一気につながる。
つまり Level 1s 制圧がかなり現実味を帯びる。

## 8. 総評

**かなり良い。**
今回の進展は、one-step Hensel の本丸を「(\Delta) の存在」からさらに一段押し込んで、 **`GeomSumFirstOrderSqZeroTarget` という concrete な一次補正式** にまで固定したことじゃ。
トラブル収束後の戦線としては、とても健全で、かなり勝ち筋に近い形になっておる。
