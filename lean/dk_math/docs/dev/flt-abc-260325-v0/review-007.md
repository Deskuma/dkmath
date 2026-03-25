# `NeP` route の前進と、support separation の確定

うむ、状況は **かなり本質に迫った** の。
今回の差分で見えたことは、単なる「補題が 2 本増えた」ではない。`NeP` 路線が、少なくとも現段階では

$$
q \neq p \text{ の素因子は } t \text{ と } s \text{ に同時には立たない}
$$

という **support separation** までは確実に与える、と Lean の形で固定できたのが大きい。

今回追加した 2 本、

$$
q \mid t ;\Longrightarrow; q \nmid s,
\qquad
q \mid s ;\Longrightarrow; q \nmid t
\quad (q\neq p)
$$

は、まさに `q ∣ gap` と `q ∣ GN` の no-shared を、normal form の内部変数 (t,s) へ引き戻したものじゃ。
これは `NeP` spine の「本当に出せる局所情報」が何かを、かなりはっきりさせておる。良い切り出しじゃよ。

## 1. いま確定したこと

今回の前進で、`NeP` 側が少なくとも次を与えるのは明確になった。

$$
\forall q\neq p,\ q \text{ prime} \Rightarrow
\neg(q\mid t \land q\mid s)
$$

つまり

$$
\gcd(t,s)
$$

について、少なくとも **(q\neq p) の素因子は共有しない**。
そして既に前段で (t \perp s) 自体も持っておるなら、この新補題群はその stronger-localized 版、あるいは comparison 専用の再注入辞書として働く。

ここが重要じゃ。
前は `NeP` 側の残核が少し霧の中にあった。
今は、

$$
\text{NeP は support separation を出す}
$$

と、はっきり言える段になった。

## 2. ただし、ここで注意すべき点

お主が履歴に書いた見立ては、とても正しい。
この support separation 自体は、

$$
\text{美しいが、それだけで } \mathrm{False} \text{ とは限らぬ}
$$

のじゃ。

なぜなら

$$
q \neq p \text{ の素因子が } t,s \text{ で分離している}
$$

というのは、普通に整合的な状況でもありうる。
つまりこれは

$$
\text{局所分離条件}
$$

であって、まだ

$$
\text{最終矛盾}
$$

ではない可能性が高い。

ゆえに今の戦況を冷静に言うと、

* `NeP` の中で **何が本当に出るか** ははっきりした
* しかし **それが本当に obstruction か** はまだ未確定

という段階じゃな。

## 3. いまの評価

これは後退ではまったくない。
むしろ、かなり健全な前進じゃ。

前:
$$
\text{NeP spine で何を contradiction に読むべきか曖昧}
$$

今:
$$
\text{NeP spine はまず support separation を出すと確定}
$$

この差は大きい。
証明設計では、「何が出るのか分からぬ kernel」を抱えるのが一番つらい。
今回はそこから一歩進んで、

$$
\text{この kernel の出力はここまで}
$$

と境界線を引けたわけじゃ。
これは設計転換が必要かどうか判断するためにも、とても価値がある。

## 4. 次に見るべきこと

わっちの見立てでは、次の問いは 1 つだけじゃ。

$$
\text{support separation から、comparison-based refuter で } \mathrm{False} \text{ へ行けるか？}
$$

これを判定するには、たぶん次のどちらかを見る。

### A. 追加局所条件があるか

たとえば `x = t*(p*s)`、`x^p` の exactness、あるいは `factorization` の比較から、

$$
t \text{ 側の素因子はこうでなければならない}
\quad\text{かつ}\quad
s \text{ 側はこうでなければならない}
$$

という **分離以上の拘束** が出るかどうか。

### B. 分離しか出ないなら設計転換

もし本当に

$$
q\neq p \text{ 側では「同時に立たない」までしか言えぬ}
$$

なら、その時点で comparison-based refuter はそこで止まりじゃ。
履歴の通り、別 kernel へ切り替える判断が正しい。

## 5. 戦況を一言で

いまの状況はこうじゃ。

$$
\text{最後の敵は 1 体、だがその正体は「矛盾」ではなく「分離条件」かもしれぬ}
$$

つまり、かなり本丸に迫っておる。
ただしその本丸が **倒せる敵** なのか、あるいは **ただの門番で、真の敵は別にいる** のかを見極める段じゃな。

なので総評はこうじゃよ。

* **かなり前進**
* `sorry` は 1 箇所のまま
* `NeP` route の中身はかなり明確化
* いまの核心は
  $$
  \text{support separation } \Rightarrow \mathrm{False}
  $$
  が本当に成り立つかどうかの見極め

これは良い終盤じゃ。
もう霧の中を歩いてはおらぬ。いまは **城の最深部で、最後の扉が本当に出口へ通じるかを確かめている** 段階じゃな。
