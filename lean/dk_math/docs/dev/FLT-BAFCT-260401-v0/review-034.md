# Review 034: Level 1s の one-step Hensel 本丸が見えた

うむ、これは **かなり良い前進** じゃ。
しかも今回は、ただ補題を増やしたのではなく、**one-step Hensel の本体がどこか** を、Lean の型でかなり正確に露出させたのが大きい。今回の差分で

* `HenselLiftStepStructuralTarget`
* `HenselLiftStepArithmeticKernelTarget`
* `HenselLiftStepCorrectionTarget`
* `henselLiftStepArithmeticKernel_of_correction`

が入り、`one-step = 構造持ち上げ + 補正項 \(\Delta\) 構成` という分解が明示された。報告の通り、**残る one-step の open は補正項 (\Delta) 構成だけ** と読むのが、まず第一近似として正しい。

## 1. 何が前進したのか

今回いちばん価値が高いのは、`HenselLiftStepArithmeticKernelTarget` をそのまま殴るのでなく、その心臓を

$$
\Delta \in ZMod(q^{n+1})
$$

の構成問題へ落としたことじゃ。
つまり、持ち上げ候補 (R_{n+1}) があったときに、

$$
\text{castHom}(\Delta)=0
$$

を満たす補正だけを足して

$$
\sum_{i=0}^{p-1}(R_{n+1}+\Delta)^i = 0
$$

へ戻せればよい、という形になった。
これは Hensel 的にはとても自然じゃ。**解を 1 段持ち上げる** とは、結局「核の中の微小補正」で零点条件を回復することだからの。

さらに、`henselLiftStepArithmeticKernel_of_correction` によって、
**補正 target が取れれば arithmetic kernel は自動で閉じる** ことも no-sorry で固定された。
これは大きい。以後は one-step 本丸を、曖昧に「何か Hensel 的なことをする」でなく、**(\Delta) をどう作るか** だけに集中できるからじゃ。

## 2. 戦況判断

いまの戦況は、かなり見通しが良い。

Level 0 はすでに閉じておる。
Level 1w も閉じた。
Level 1s は前回まで「Strong をどう作るか」という大きな塊だったが、今回で

$$
\text{Strong}
\Leftarrow
\text{one-step Hensel}
\Leftarrow
\text{structural lift} + \Delta\text{ correction}
$$

まで分解された。
ゆえに、Level 1s の真芯は今や

$$
\boxed{\text{補正項 } \Delta \text{ の concrete 構成}}
$$

と、かなり明確になったのじゃ。

## 3. ただし、ここで一つ慎重な注意

ここはかなり大事じゃ。

今回の `HenselLiftStepCorrectionTarget` / `ArithmeticKernelTarget` は、**まだ少し一般すぎる** 可能性がある。
なぜなら classic な Hensel の one-step で本当に使う条件は、

* (q \ne p)
* root branch が mod (q) で固定されている
* (\Phi_p'(R_n)) が mod (q) で可逆

という **simple root 条件** じゃからの。

ところが現在の target は、少なくとも diff の形を見る限り、

$$
\forall, q,n,R_n
$$

で幾何和ゼロさえあれば one-step correction を要求しておる。
これは FLT 文脈では最終的に満たしたい statement かもしれぬが、**証明のための仮定としては少し強すぎる** かもしれん。

わっちの読みでは、実際に concrete に落とす段では、補正 target に

$$
(R_n \bmod q)=\omega^j,\qquad
\Phi_p'(\omega^j)\not\equiv 0 \pmod q
$$

に相当する仮定を明示した方が、ずっと自然じゃ。
つまり今の target 分解は正しいが、**次の concrete proof 段階で branch-preserving / derivative-unit 仮定を内包した specialized 版に寄せる** 可能性は高い。

これは「今の設計が悪い」という意味ではなく、
**いま本丸が見えたので、次は本丸専用の武器に sharpen すべき** ということじゃ。

## 4. 数学的な解説

今回の (\Delta) 補正の意味を数式で書くと、対象は

$$
F(T):=\sum_{i=0}^{p-1}T^i
$$

じゃ。
one-step で欲しいのは、

$$
F(R_n)\equiv 0 \pmod{q^n}
$$

から、ある補正 (\Delta) を用いて

$$
F(R_{n+1}+\Delta)\equiv 0 \pmod{q^{n+1}}
$$

を出すことじゃな。

Hensel の定石では、(\Delta) は普通

$$
\Delta = q^n c
$$

の形で探す。
そして一次近似で

$$
F(R_{n+1}+q^n c)
\equiv
F(R_{n+1}) + q^n c,F'(R_{n+1})
\pmod{q^{n+1}}
$$

となるから、

$$
F'(R_{n+1}) \not\equiv 0 \pmod q
$$

なら (c) を 1 本の一次合同式で解ける。
ゆえに補正 target の本当の心臓は、実は

$$
F'(R_n)
$$

の可逆性じゃ。
この意味で、いまの `HenselLiftStepCorrectionTarget` は very good な中間形じゃが、次にさらに裂くなら

$$
\text{correction existence}
\Longleftarrow
\text{linearized correction lemma}
+
\text{derivative invertibility}
$$

と分けられるはずじゃ。

## 5. これでよいのか

**はい、これでよい。しかもかなり良い。**

ただし、正確にはこうじゃ。

* **型設計としては非常に良い**
* **戦況整理としても正しい**
* ただし次の concrete proof では、target をそのまま殴るより、
  branch-preserving な specialized Newton/Hensel 補題に寄せた方が通りやすい

つまり今回の成果は、「one-step の open が (\Delta) 構成だ」と分かったこと。
次の成果は、その (\Delta) を **一次補正公式** で実際に作ることじゃ。

## 6. 次の一手

わっちなら、次はこの順じゃ。

まず specialized 補題として、
(F(T)=\sum_{i=0}^{p-1}T^i) に対し

$$
F(R+q^n c)
\equiv
F(R)+q^n c,F'(R)
\pmod{q^{n+1}}
$$

を formal に作る。
これが **Newton/Hensel 一次補正補題** じゃ。

その次に、

$$
F'(R)\not\equiv 0 \pmod q
$$

を (\omega^j) branch から出す。
ここで初めて Level 0 と Level 1s が噛み合う。

最後に、その 2 本を束ねて `HenselLiftStepCorrectionTarget` を concrete に閉じる。
この順がもっとも自然じゃろう。

## 7. 一文で総評

**今回の進展は、Level 1s の one-step 本丸を「補正項 (\Delta) の構成」へ純化し、残る未解決を Newton/Hensel の一次補正だけにまで絞った、かなり良い戦況前進** じゃ。
ここまで来れば、次はもう truly arithmetic な一撃だけじゃよ。
