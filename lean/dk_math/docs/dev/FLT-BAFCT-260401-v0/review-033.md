# Level 1s の戦況分析：one-step の構造 vs 算術分離の意義

うむ、これは **かなり良い前進** じゃ。
しかも今回は、証明が直接進んだというより、**one-step Hensel の中で何が trivial で、何が本丸かを Lean の型で完全に分離できた** のが大きい。今回の diff では

* `HenselLiftStepStructuralTarget`
* `HenselLiftStepArithmeticKernelTarget`
* `henselLiftStepStructural_concrete`
* `henselLiftStepGeomSum_of_structural_and_kernel`

が追加され、one-step の未解決部が **算術 kernel ただ 1 本** に集約された、と自分で明記しておる。ここは戦況判断として正しい。

## 1. 今回の本質

今回いちばん価値が高いのは、`HenselLiftStepGeomSumTarget` をそのまま殴るのでなく、

$$
\text{one-step} = \text{構造持ち上げ} + \text{算術補正}
$$

に裂いたことじゃ。
これは Hensel の本質そのものに近い分解じゃよ。

* 構造部分
  [
  ZMod(q^{n+1}) \to ZMod(q^n)
  ]
  の全射性により、近似根 (R_n) を **とりあえず** 上へ持ち上げる
* 算術部分
  持ち上げた (R_{n+1}) を、幾何和
  [
  \sum_{i=0}^{p-1} R_{n+1}^i
  ]
  が 0 になるよう **補正する**

この二段は、まさに Hensel step の「形」と「中身」じゃ。
だからこの分離は、美しいだけでなく、数学として筋が良い。

## 2. どこまで本当に進んだか

ここは慎重に言うぞい。

### 2.1. 閉じたところ

`henselLiftStepStructural_concrete` は、`ZMod.castHom_surjective` を使って no-sorry で通った。
つまり

$$
R_n \in ZMod(q^n)
$$

が与えられたら、

$$
R_{n+1} \in ZMod(q^{n+1})
$$

で

$$
R_{n+1} \mapsto R_n
$$

となるものがある、という **純構造部分** は完全に closed じゃ。

### 2.2. まだ open なところ

しかし、これは Hensel の核心ではない。
核心はそのあと、

$$
\sum_{i=0}^{p-1} R_n^i = 0
$$

を満たす近似根から、持ち上げ先を

$$
\sum_{i=0}^{p-1} R_{n+1}^i = 0
$$

となるように **補正できるか** じゃ。
今回の整理で、その部分が `HenselLiftStepArithmeticKernelTarget` として単独露出した。
これは非常に良い。いまや「何を証明すればいいか」が完全に見えておる。

## 3. 戦況分析

いまの戦況を一言で言うなら、

**one-step の “実装の殻” は破れ、本体は純粋な arithmetic kernel のみに縮んだ**

じゃ。

前までは Level 1s が「StrongSuperWieferich をどう作るか」という大きな塊に見えておった。
今はそれが

$$
\text{QAdicResidue}
\to
\text{Hensel one-step}
\to
\text{反復}
\to
\text{StrongSuperWieferichV2}
$$

という流れに整理され、しかも one-step 自体も

$$
\text{structural} + \text{arithmetic}
$$

に割れた。
この分解により、もはや曖昧な部分は残っておらぬ。残る open は、**幾何和ゼロの補正公式をどう作るか** だけじゃ。

## 4. これは「これでよい」のか

**はい、これでよい。むしろかなり良い。**

理由は単純で、今回の `HenselLiftStepStructuralTarget` は、ほとんど tautological と言ってよい部分じゃ。
つまり

$$
q^n \to q^{n+1}
$$

への lift の存在自体は、Hensel の難所ではない。
そこを no-sorry で固定してしまったので、以後は誰が見ても

> 難しいのは lift の存在ではなく、lift 後に (\Phi_p) 条件を回復する補正

だと分かる。
これはとても健全な整理じゃ。

## 5. 数学的解説

ここで算術 kernel の中身を少し言語化すると、対象の多項式は

$$
F(T) := \sum_{i=0}^{p-1} T^i
$$

じゃな。
いま欲しいのは、

$$
F(R_n)\equiv 0 \pmod{q^n}
$$

を満たす (R_n) に対し、

$$
R_{n+1}=R_n + q^n c
$$

の形で (c) をうまく選んで

$$
F(R_{n+1})\equiv 0 \pmod{q^{n+1}}
$$

を達成することじゃ。
これは要するに、一次近似で

$$
F(R_n + q^n c)
\equiv
F(R_n) + q^n c,F'(R_n)
\pmod{q^{n+1}}
$$

を使い、

$$
F'(R_n)
$$

が mod (q) で可逆なら、(c) を解いて 1 段持ち上げる、という Hensel の定石じゃ。

つまり `HenselLiftStepArithmeticKernelTarget` の正体は、

$$
F'(R_n)\not\equiv 0 \pmod q
$$

を使った Newton/Hensel 補正の実装じゃよ。

## 6. 次の一手

わっちなら次に狙う補題はこれじゃ。

$$
F(T)=\sum_{i=0}^{p-1}T^i
$$

として、

$$
F(R_n)\equiv 0 \pmod{q^n},\qquad
F'(R_n)\not\equiv 0 \pmod q
$$

なら

$$
\exists c,\quad
F(R_n+q^n c)\equiv 0 \pmod{q^{n+1}}
$$

という specialized one-step lemma をまず立てる。
これがそのまま `HenselLiftStepArithmeticKernelTarget` の concrete proof の心臓になるはずじゃ。

## 7. 総評

**今回の変更は、Level 1s の本命を “one-step arithmetic kernel” 1 本にまで縮約した、かなり良い設計前進** じゃ。
構造側が concrete に閉じた今、残る未解決は本当に Hensel 補正そのものだけじゃ。
これは戦況として、とても見通しが良い。

必要なら次に、その specialized Hensel one-step を **Lean 向け補題列** にして書き起こすぞい。
