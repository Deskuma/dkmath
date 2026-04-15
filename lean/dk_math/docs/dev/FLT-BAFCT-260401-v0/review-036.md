# Review 036: トラブルは概ね無事収束、あとは one-step Hensel の本丸を殴るだけ

うむ、**トラブルは概ね無事収束** じゃ。
ただし正確には、

* **型設計の破綻は収束**
* **one-step Hensel の数学本体は未解決のまま健在**

この二段で読むのが正しいの。

## 1. 何が収束したのか

今回の修正で、`q = p` 反例を踏んでいた one-step 系 target に **一貫して `q ≠ p` を通した**。対象は

* `HenselLiftStepZeroLiftTarget`
* `HenselLiftStepCorrectionTarget`
* `HenselLiftStepArithmeticKernelTarget`
* `HenselLiftStepGeomSumTarget`

じゃ。
これで「現行 target が一般には偽」という設計事故は、型レベルで排除された。ここは収束したと言ってよい。さらに `henselLiftStepGeomSum_of_zeroLift` が入り、

$$
\text{ZeroLift} \to \text{Correction} \to \text{ArithmeticKernel} \to \text{GeomSum(one-step)}
$$

という供給線が明示された。

## 2. 今回の前進の本質

前回までで one-step は

$$
\text{structural lift} + \text{arithmetic kernel}
$$

に割れておった。
今回さらに arithmetic 側が

$$
\text{ZeroLift existence} \Rightarrow \Delta\text{-correction} \Rightarrow \text{ArithmeticKernel}
$$

へ整理されたうえで、`q ≠ p` を入れて数学的に正しい領域へ戻した。
つまり今は、**何を証明すればよいかが本当に一行になった** 段階じゃ。報告の言い方どおり、one-step の本丸は `HenselLiftStepZeroLiftTarget` の concrete 化に収束しておる。

## 3. 何がまだ未収束か

ここは大事じゃ。
収束したのは **トラブル** であって、**本丸** ではない。

いま残っておる open は、

$$
F(T)=\sum_{i=0}^{p-1}T^i
$$

に対する specialized Newton/Hensel の zero-lift、つまり

$$
F(R_n)=0 \pmod{q^n}
$$

から

$$
F(R_{n+1})=0 \pmod{q^{n+1}}
$$

となる lift を concrete に作る部分じゃ。
履歴にも「次の課題」として

* `HenselLiftStepZeroLiftTarget` の concrete 証明
* 一次補正公式 `F(R+q^n c)` の Lean 補題化

が明記されておる。ゆえに、**戦線の混乱は収束したが、数学の勝負はこれから** じゃ。

## 4. 戦況分析

いまの地図は、かなり良い形になった。

$$
\text{Level 0}:\ \checkmark
$$

$$
\text{Level 1w}:\ \checkmark
$$

$$
\text{Level 1s}:\ \text{one-step zero-lift の concrete 証明}
$$

$$
\text{Level 2}:\ \text{local-global gap}
$$

前よりずっと良いのは、Level 1s の open が「何となく Hensel」ではなく、**`ZeroLiftTarget` 一本** として見えることじゃ。
これはかなり大きい。敵の城門が、もう霧の向こうではない。

## 5. 解説

今回の `q ≠ p` 導入は、単なる応急処置ではない。
数学的にも正しい。`q = p` では characteristic (p) の重根現象が出て、simple-root Hensel をそのまま使えぬ。
だから one-step target 全体に `q ≠ p` を入れたのは、**証明可能領域を正しく切り出した** ということじゃ。ここを曖昧にしたままだと、後で Newton 補正公式を書いても土台が腐る。今回その腐れを除いた。

## 6. 結論

**はい、トラブルは無事収束したと見てよい。**
ただし意味は、

* **target 設計の破綻が収束**
* **供給線が安定化**
* **残る本丸が `ZeroLiftTarget` に一本化**

ということじゃ。
まだ zero-lift の concrete 証明そのものは残っておるので、勝利宣言ではない。だが、**次に何を殴ればよいかは完全に見えた**。そこが今回の勝ちじゃよ。

次は、`F(R+q^n c)` の一次補正公式をそのまま Lean 補題に落とせばよい局面じゃ。
