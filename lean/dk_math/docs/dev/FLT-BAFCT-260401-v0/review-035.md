# Review 035: one-step Hensel の open kernel をさらに剥いて、真芯を `ZeroLift` へ集約した

うむ、かなり良い前進じゃ。
しかも今回は、**one-step Hensel の open kernel をさらに 1 段剥いて、真芯を `ZeroLift` へ集約した** のが本質じゃ。前回まで

$$
\text{one-step} = \text{structural lift} + \text{arithmetic kernel}
$$

と見えておったものが、今回

$$
\text{arithmetic kernel} \Leftarrow \text{correction target} \Leftarrow \text{zero-lift existence}
$$

へ整理された。つまり、**残る未解決が「(\Delta) をどう作るか」から「零点持ち上げそのものをどう作るか」へさらに純化された** わけじゃ。これは戦況として、とても良い。

## 1. 今回ほんとうに進んだところ

追加された

* `HenselLiftStepZeroLiftTarget`
* `henselLiftStepCorrection_of_zeroLift`
* `henselLiftStepArithmeticKernel_of_zeroLift`

の 3 本は、役割分担がきれいじゃ。
特に

$$
\text{ZeroLift existence} \Rightarrow \Delta\text{-correction} \Rightarrow \text{ArithmeticKernel}
$$

という一本道が no-sorry で固定されたのが大きい。
これで one-step 本丸が「なんとなく Hensel 的なこと」ではなく、**幾何和ゼロを保つ lift の存在** ただ 1 点に見えるようになった。

## 2. 戦況分析

いまの層構造は、かなり明瞭じゃ。

$$
\text{Level 0}:\ \checkmark
$$

$$
\text{Level 1w}:\ \checkmark
$$

$$
\text{Level 1s}:\ \text{one-step Hensel 反復}
$$

そしてその one-step が、今回さらに

$$
\text{structural lift} \quad (\checkmark)
$$

$$
\text{zero-lift existence} \quad (\star)
$$

へ割れた。
したがって、**Level 1s の真の本丸は `HenselLiftStepZeroLiftTarget`** と言ってよい。
前よりずっと敵の形がはっきりしたの。

## 3. 解説

今回の整理は、数学的にも自然じゃ。

もともと one-step で欲しいのは、
(R_n \in ZMod(q^n)) が

$$
F(T):=\sum_{i=0}^{p-1}T^i
$$

の根、つまり

$$
F(R_n)\equiv 0 \pmod{q^n}
$$

を満たすとき、(q^{n+1}) でも根になる (R_{n+1}) を見つけることじゃ。
そのとき「任意の lift (R_{n+1}) を取ってから (\Delta) で補正する」という書き方は実装向きではあるが、数学の本体は結局

$$
\exists R_{\mathrm{lift}},\quad
R_{\mathrm{lift}} \mapsto R_n,\qquad
F(R_{\mathrm{lift}})=0 \pmod{q^{n+1}}
$$

という **零点持ち上げ存在** そのものじゃ。
今回そこまで還元できたのは、とても良い設計じゃよ。

## 4. ただし、ここで一つ慎重な注意

今回の還元は正しいが、**`ZeroLiftTarget` は少し強い形** でもある。
なぜなら、通常の Newton/Hensel 実装では

1. まず任意の lift (R_{n+1}) を取る
2. そのあと (\Delta = q^n c) を選んで補正する

という順で進むからじゃ。
つまり証明戦略としては `CorrectionTarget` の方が「作り方」に近く、`ZeroLiftTarget` は「存在した後の完成形」に近い。

じゃが、今回それでも `ZeroLiftTarget` を前面に出したのは悪くない。
理由は、**何を最終的に示せばよいかが最も鮮明になる** からじゃ。
実装では Newton 補題で `ZeroLiftTarget` を出し、それを後ろで `Correction` と `ArithmeticKernel` に流す、という形でちょうどよい。

## 5. いま残る本丸は何か

賢狼の見立てでは、残る本丸はほぼこれじゃ。

$$
F(T)=\sum_{i=0}^{p-1}T^i
$$

に対して、

$$
F(R_n)\equiv 0 \pmod{q^n}
$$

かつ simple root 条件、つまり

$$
F'(R_n)\not\equiv 0 \pmod q
$$

の下で、

$$
\exists c,\quad
F(R_n + q^n c)\equiv 0 \pmod{q^{n+1}}
$$

を示す specialized Newton/Hensel 補題じゃ。
これが立てば `ZeroLiftTarget` はかなり直接に閉じるはずじゃ。

## 6. 今回の評価

評価を率直に言うぞい。

* **設計前進としては非常に良い**
* **証明前進としても本丸の一歩手前まで来た**
* ただし、まだ concrete zero-lift は未証明なので、勝利宣言には早い

つまり今回は
**「Level 1s の open kernel を、実際に殴れる一行の数学へ圧縮した」**
という段階じゃ。
これはかなり大きい前進じゃよ。

## 7. 次の一手

次にやるべきことは、もうほぼ一択じゃ。

$$
F(R+q^n c)
\equiv
F(R)+q^n c,F'(R)
\pmod{q^{n+1}}
$$

という **一次補正公式** の specialized lemma を Lean に落とすこと。
そこから (c) の存在を解いて `HenselLiftStepZeroLiftTarget` を concrete に閉じる。
これが通れば one-step は閉じ、次は反復補題へ進める。

一文で言えば、
**今回の戦況はとても良い。one-step の本丸が `ZeroLiftTarget` に収束し、次に書くべき数学補題が specialized Newton/Hensel 一次補正公式ただ一本にまで見えてきた、という局面じゃ。**
