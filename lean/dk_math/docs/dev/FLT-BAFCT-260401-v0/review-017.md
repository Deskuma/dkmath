# review-017: `PthRootTarget` を reduced form に落とすことの意味と今後の攻略

うむ、これは **とても良い差分** じゃ。
しかも、ぬしの望む通り **GN 路線へ寄せるための足場** として、かなり良い形になっておる。

## 1. . 戦況分析

今回の差分で本当に大きいのは、`PthRootTarget` を reduced form に落とし、

$$
\exists z',\quad p^p \cdot (t \cdot s')^p + y^p = z'^p
$$

と書けるようにしたことじゃ。さらに

$$
z^p = q^p \cdot \bigl(p^p \cdot (t \cdot s')^p\bigr) + y^p
$$

という (z^p) の identity まで通った。
この 2 本があると、「最後の門」が **抽象的な p 乗根問題** ではなく、**Branch A descent data の特殊形に対する構造化された reduced root 問題** へ変わる。これは大きい。

しかも、ぬしの report どおり、いまの non-circular mainline は

$$
\texttt{PthRootTarget}
\to
\texttt{RestoreFromArithmeticStrong\_of\_pthRoot}\\
\to
\texttt{StrongProvider}
\to
\texttt{FringeDescentToRefuter}
$$

という形で、**kernel 1 本残しで concrete** になっておる。
この時点で、戦線整理としてはほぼ完璧じゃ。

## 2. . 解説

わっちの見立てでは、今回の差分の真価は **Kummer/Hensel へ直接飛び込まずに済む座標系が手に入った** ことじゃ。

前は

$$
\exists z',\quad (x/q)^p + y^p = z'^p
$$

という形で、少し「根を取る」印象が強かった。
だが reduced form にすると、

$$
\exists z',\quad p^p \cdot (t \cdot s')^p + y^p = z'^p
$$

となる。ここでは (x/q) の quotient 側が消え、**descent data の中身そのもの** が前面へ出る。
つまり、

* (p)
* (t)
* (s' = s/q)
* (y)

だけで門が書けるようになったのじゃ。
これは GN 的に非常に美しい。なぜなら GN はもともと

$$
(z-y),GN_p(z-y,y) = z^p - y^p
$$

という **差の冪の分解器** だからじゃ。

## 3. . GN 路線が理想な理由

ぬしの感覚は正しい。
この project では、やはり GN 路線が最も自然じゃ。

理由は 3 つある。

### 3.1. project の家主が GN / Tail 側

一般化 GN 多項式の設計では、

$$
(x+u)^d - \sum_{j=0}^{r-1}\binom{d}{j}x^j u^{d-j} = x^r , GN_d^{(r)}(x,u)
$$

という Tail / Beam の階層が、そもそもの主役として置かれておる。
つまり project の哲学として、**差の冪の残差構造を読む** ことが本流じゃ。

### 3.2. 今回の reduced form は GN へ自然に戻せる

`PthRootReducedTarget` は加法の形をしておるが、(g' := z' - y) と置けば

$$
z'^p - y^p = g' , GN_p(g',y)
$$

じゃ。
したがって reduced root 問題は、実は

$$
g' , GN_p(g',y) = p^p \cdot (t \cdot s')^p
$$

を満たす (g') の存在問題に言い換えられる。
ここで初めて、**p 乗根を取る問題** が **GN の因数分解問題** へ変換される。これが GN 路線のいちばん美しい点じゃ。

### 3.3. Kummer/Hensel を補助路線へ落とせる

full Kummer/Hensel は重い。
だが GN 路線を mainline に据えると、q-adic や Hensel は **GN の片側因子に q^p が集中することを示す補助補題** として使える。
つまり、

* main theorem は GN
* q-adic / Hensel は side lemmas

という整理ができる。
これは project の設計原則「先に局所核、後で強理論」とも一致する。

## 4. . 次の攻め

わっちなら、次は **直接 `PthRootTarget` を殴らぬ**。
先に GN-native な target を 1 本置く。

つまり、次の真正面の敵は

$$
\exists z',\quad p^p \cdot (t \cdot s')^p + y^p = z'^p
$$

ではなく、

$$
\exists g',\quad g' , GN_p(g',y) = p^p \cdot (t \cdot s')^p
$$

じゃ。

ここで (z' := y + g') と戻せばよい。
これを theorem / target の形で言えば、たとえばこうじゃ。

$$
\boxed{
\texttt{PthRootReducedTarget}
\ \text{より前に}
\texttt{GNReducedGapTarget}
\ \text{を置く}
}
$$

役割は、

* 入力: 今の Branch A reduced data
* 出力: (g') が存在して (g' GN_p(g',y) = p^p (t s')^p)

これだけでよい。
その上で

$$
\texttt{GNReducedGapTarget} \to \texttt{PthRootReducedTarget}
$$

の橋を作る。
この橋は cosmic factorization だけで済むはずじゃ。

## 5. . 実際の作業順

順番もかなり明確じゃ。

### 5.1. まず新 target を切る

名前は仮に

```lean
PrimeGe5BranchAPrimitiveRestoreGNReducedGapTarget
```

でよい。
主張は「(g') exists with GN product equals reduced RHS」。

### 5.2. `GNReducedGapTarget → PthRootReducedTarget` を no-sorry で作る

これは

$$
(z'-y),GN_p(z'-y,y) = z'^p - y^p
$$

の既存因数分解を使えばよい。
ここは project-native に気持ちよく閉じる。

### 5.3. そのあとにだけ `GNReducedGapTarget` 本体を攻略する

ここで初めて q-adic / Hensel / valuation / GN-tail の特殊補題群を使う。
順番を間違えると、いきなり p 乗根 existence を殴ることになって重い。

## 6. . その GN 攻略で何を見るか

ここで見るべきは、すでにぬしの report に書いてある構造じゃ。

* (q \nmid (z-y))
* (GN = p \cdot s^p)
* (s = q \cdot s')
* よって (q^p) は GN 側から剥がれる

つまり、GN 路線で本当にやりたいことは、

$$
GN_p(z-y,y) = p \cdot q^p \cdot s'^p
$$

の (q^p) を、**新しい gap (g') を持つ別の GN equation に移し替える** ことじゃ。
これは Hensel を「root existence」ではなく「GN-side q-adic transport」として使う読み替えになる。
この読み替えができるなら、かなり project らしい戦い方になるの。

## 7. . 総評

総評すると、今回の差分は **攻略そのものではなく、攻略の標的を GN 向きに曲げた勝ち** じゃ。

前は最後の門が

$$
\exists z'
$$

で見えておった。
今は違う。

$$
\boxed{
\text{GN product を reduced RHS に一致させる問題}
}
$$

へ持ち替えられる可能性が見えた。
これは当プロジェクトにとって、とても良い方向じゃよ。

## 8. . わっちの次手

ひとことで言えば、こうじゃ。

$$
\boxed{
\text{次は `PthRootReducedTarget` を直接殴るな。GNReducedGapTarget を新設せよ。}
}
$$

その上で、

$$
\texttt{GNReducedGapTarget}
\to
\texttt{PthRootReducedTarget}
\to
\texttt{PthRootTarget}
$$

という mainline を作る。
GN が家主、q-adic / Hensel は補助。
これが、いま最も project らしい攻めじゃ。🍎
