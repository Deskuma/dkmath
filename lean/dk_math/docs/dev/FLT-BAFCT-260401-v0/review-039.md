# Review 039: one-step Hensel の本丸が「線形可解性ただ 1 本」へ圧縮された

うむ、これは **かなり良い前進** じゃ。
しかも今回は、単なる整理ではなく、**Newton 補正の本丸を「線形可解性ただ 1 本」へ圧縮した** のが価値の中心じゃよ。今回の差分で

* `HenselLiftStepLinearizedSolveTarget` を新設し、
* `henselLiftStepNewtonCorrection_of_linearizedSolve` により
  **線形方程式が解ければ NewtonCorrection は従う** ことを no-sorry で固定した。さらに本体・test の両 build 成功も確認されておる。

## 1. いま何が起きたか

少し前までの one-step Hensel の open は、

$$
\text{ZeroLift}
\Leftarrow
\text{Correction}
\Leftarrow
\text{NewtonCorrection}
\Leftarrow
\text{SqZero 一次補正式}
$$

という形に見えておった。
そして前回、`GeomSumFirstOrderSqZeroTarget` は concrete に閉じた。つまり一次補正式そのものはもう使える状態になっておる。

今回さらに、その次の段

$$
\text{NewtonCorrection}
$$

が、

$$
\boxed{
\text{HenselLiftStepLinearizedSolveTarget}
}
$$

へ還元された。
これはとても大きい。なぜなら、one-step の open がついに

> 「線形方程式の解 (c) を作れるか」

という、完全に具体的な問題へ落ちたからじゃ。

## 2. 戦況分析

いまの戦況を一番短く言えば、こうじゃ。

### 2.1. 閉じたもの

* Level 0 の `QAdicResidue`
* Level 1w の weak SuperWieferich
* structural lift
* `Δ^2 = 0` の一次補正式
* `q^n c` を使う concrete な一次補正公式
* 線形可解性 ⇒ NewtonCorrection の橋

ここまではかなり安定した。特に、今回の `henselLiftStepNewtonCorrection_of_linearizedSolve` は、一次補正式 concrete をそのまま使って、

$$
F(R_{n+1}+q^n c)=0
$$

を示す導線を完全に固定しておる。

### 2.2. いまの本丸

残る本丸は、ほぼ

$$
\boxed{
\text{HenselLiftStepLinearizedSolveTarget の concrete 証明}
}
$$

だけじゃ。
報告でも「Newton 補正本丸は `LinearizedSolveTarget` の concrete 化問題として明示された」と総括しておる。これは誇張ではなく、かなり正確な戦況図じゃ。

## 3. 数学的に何が起きているか

対象は、いつもの

$$
F(T)=\sum_{i=0}^{p-1}T^i
$$

じゃな。
one-step Newton 補正では、(R_{n+1}) を固定したあと

$$
F(R_{n+1}+q^n c)
$$

を 1 次で展開して、前回 concrete 化した補題から

$$
F(R_{n+1}+q^n c)
================

F(R_{n+1})
+
F'(R_{n+1})\cdot q^n c
$$

の形に持ち込む。
そこで欲しいのは

$$
F'(R_{n+1})\cdot q^n c = -F(R_{n+1})
$$

という線形方程式の解 (c) じゃ。
今回の `HenselLiftStepLinearizedSolveTarget` は、まさにこの一行を target として切り出したものじゃよ。

つまり今後の勝負は、

* 一次補正式をどう展開するか
  ではなく、
* **その線形方程式がなぜ解けるのか**

へ一本化された。
これはかなり本丸に近い。

## 4. これは「本当に前進」か

**はい、本当に前進じゃ。**
ただし種類としては、

* 巨大な open kernel を細かく裂いた前進
  ではなく、
* **本丸そのものを、解くべき線形方程式まで縮約した前進**

じゃ。

だから、まだ Level 1s 制圧完了ではない。
されど、「何を証明すればよいか」が完全に見えた、という意味ではかなり強い。特に今回の還元は、もはや抽象 target の並べ替えではなく、具体式

$$
A \cdot c = B
$$

型の可解性問題へ落ちておる。
これ以上はほんとうに arithmetic の勝負じゃよ。

## 5. いま慎重に見るべき点

ここで浮かれすぎると危うい点もある。

`LinearizedSolveTarget` はまだ一般形の target じゃから、実際の concrete proof ではおそらく

$$
F'(R_{n+1}) \not\equiv 0 \pmod q
$$

すなわち simple-root 条件を、branch 情報から取り出す必要がある。
つまり残る勝負は「線形方程式なら何でも解ける」ではなく、

* 係数が可逆であること
* 右辺がちゃんと (q^n) を因子にもつこと
* それを `ZMod(q^(n+1))` でどう解くか

の 3 点を concrete に押すことじゃ。
とはいえ、これはもう Hensel の textbook 的な最終局面じゃ。方向としては非常に良い。

## 6. 現在地の整理

いまの導線は、かなり綺麗にこう書ける。

$$
\text{GeomSumFirstOrderSqZero concrete}
\Rightarrow
\text{q}^n c\text{ 版一次補正式 concrete}
\Rightarrow
\text{LinearizedSolve}
\Rightarrow
\text{NewtonCorrection}
\Rightarrow
\text{Correction}
\Rightarrow
\text{ZeroLift}
\Rightarrow
\text{Level 1s}
$$

このうち、左から 2 つはもう concrete で閉じた。
今回、その次の矢印

$$
\text{LinearizedSolve} \Rightarrow \text{NewtonCorrection}
$$

も concrete に閉じた。
だから open は実際かなり右側へ押し込まれたのじゃ。

## 7. 結論

**かなり良い。**
今回の前進で、one-step Hensel の本丸はほぼ **`HenselLiftStepLinearizedSolveTarget` の concrete 証明** に一本化された、と見てよい。
つまり今や Level 1s の open kernel は「線形化した Newton 方程式が実際に解けるか」という、完全に具体的な arithmetic 問題になった。これは戦況として非常に健全じゃ。

次の一手はもう明快で、
**simple-root 条件から係数可逆性を取り、`LinearizedSolveTarget` を concrete に閉じる** ことじゃ。
そこまで行けば、Level 1s 制圧がかなり現実味を帯びるぞい。
