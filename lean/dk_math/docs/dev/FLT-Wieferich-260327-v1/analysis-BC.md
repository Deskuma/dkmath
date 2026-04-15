# 分析：Branch A の比較段における (B) と (C) の exact relation

うむ、これでよい。
この置き方なら、 **\(B\) と \(C\) の関係はかなり明確に解析できる** 。

まず、ぬしが置いた比較段はこうじゃ。
同じ \(t = p t_1\) の下で

$$
s^p = y^{p-1} + p^{2p-1}(t_1^p B)
$$

と

$$
GN\bigl(p,\;p^{p-1} t_1^p,\;y\bigr)=
p\,y^{p-1} + \bigl(p^{p-1} t_1^p\bigr) C
$$

を並べて返す。これで「本当に見るべき差分は \(B\) と \(C\) だけ」という構図が固定された。fileciteturn20file0

## 1. . 変数を 1 つ置く

見通しをよくするため、

$$
u := p^{p-1} t_1^p
$$

と置く。すると比較段は

$$
s^p = y^{p-1} + p^p u\,B
$$

および

$$
GN(p,u,y)=p\,y^{p-1}+uC
$$

になる。

一方、もともとの Branch A 正規形は

$$
GN\bigl(p,\;z-y,\;y\bigr)=p\,s^p
$$

で、ここで \(t = p t_1\) より

$$
z-y = p^{p-1}(p t_1)^p = p^{2p-1} t_1^p = p^p u
$$

じゃから、

$$
GN(p,p^p u,y)=p\,s^p
$$

とも書ける。

ここに seed の式を代入すると

$$
GN(p,p^p u,y)=
p\,y^{p-1}+p^{p+1}u\,B
$$

となる。

---

## 2. . \(C\) の正体

GN の定義から

$$
GN(p,u,y)=
\sum_{k=0}^{p-1} \binom{p}{k+1} u^k y^{p-1-k}
$$

じゃから、先頭項 \(k=0\) を分けると

$$
GN(p,u,y)=
p\,y^{p-1}
+
u \sum_{k=1}^{p-1} \binom{p}{k+1} u^{k-1} y^{p-1-k}.
$$

ゆえに

$$
\boxed{
C=
\sum_{k=1}^{p-1} \binom{p}{k+1} u^{k-1} y^{p-1-k}
}
$$

と **一意に** 決まる。

つまり \(C\) は、ただの未知係数ではなく、**canonical tail そのもの** じゃ。

---

## 3. . \(B\) の正体

同じく

$$
GN(p,p^p u,y)=
\sum_{k=0}^{p-1} \binom{p}{k+1} (p^p u)^k y^{p-1-k}
$$

なので、

$$
GN(p,p^p u,y)=
p\,y^{p-1}
+
p^p u \sum_{k=1}^{p-1} \binom{p}{k+1} p^{p(k-1)} u^{k-1} y^{p-1-k}.
$$

一方これは上で

$$
GN(p,p^p u,y)=p\,y^{p-1}+p^{p+1}u\,B
$$

でもあるから、\(u>0\) の局面では比較して

$$
\boxed{
p\,B=
\sum_{k=1}^{p-1} \binom{p}{k+1} p^{p(k-1)} u^{k-1} y^{p-1-k}
}
$$

したがって

$$
\boxed{
B=
\sum_{k=1}^{p-1}
\frac{\binom{p}{k+1}}{p}\,
p^{p(k-1)} u^{k-1} y^{p-1-k}
}
$$

じゃ。

ここで \(p\) は素数ゆえ、\(1 \le k+1 \le p-1\) なら \(\binom{p}{k+1}\) は \(p\) で割れる。
ゆえに右辺はちゃんと整数になる。
つまり \(B\) は **scaled gap \(p^p u\)** に対する canonical tail 係数を、さらに \(p\) で正規化したものじゃ。

---

## 4. . \(B\) と \(C\) の exact relation

これで二つを並べれば終わりじゃ。

$$
C=
\sum_{k=1}^{p-1} \binom{p}{k+1} u^{k-1} y^{p-1-k}
$$

$$
pB=
\sum_{k=1}^{p-1} \binom{p}{k+1} p^{p(k-1)} u^{k-1} y^{p-1-k}
$$

だから、

$$
\boxed{
C - pB=
\sum_{k=1}^{p-1}
\binom{p}{k+1}
\bigl(1-p^{p(k-1)}\bigr)
u^{k-1} y^{p-1-k}
}
$$

じゃが、\(k=1\) では \(1-p^{p(k-1)} = 1-1=0\) なので消える。ゆえに本質的には

$$
\boxed{
C - pB=
u \sum_{k=2}^{p-1}
\binom{p}{k+1}
\bigl(1-p^{p(k-1)}\bigr)
u^{k-2} y^{p-1-k}
}
$$

となる。

これはとても良い式じゃ。
なぜなら一発で

$$
\boxed{
C \equiv pB \pmod{u}
}
$$

が従うからじゃ。

ここで \(u = p^{p-1} t_1^p\) なので、さらに

$$
\boxed{
C \equiv pB \pmod{p^{p-1} t_1^p}
}
$$

とも言える。

---

## 5. . 何が分かったか

これで重要なことが三つ分かる。

### 5.1. . \(B=C\) ではない

一般にはそうはならぬ。
各項に \(p^{p(k-1)}\) という重み差があるからじゃ。

### 5.2. . \(C=p^p B\) でもない

これも一般には違う。
合うなら各次数で一様に \(p^p\) が掛かる必要があるが、実際には次数 \(k\) ごとに

$$
p^{p(k-1)}
$$

と変わっておる。

### 5.3. . しかし一次近似では \(C \sim pB\)

しかも差は **必ず \(u\) を 1 個含む** 。

これは、valuation peel route の本質が

$$
\text{exact equality ではなく}
\quad
\text{“first-order congruence”}
$$

であることを示しておる。

---

## 6. . 小さい例で確かめる

たとえば \(p=3\) なら

$$
C=
\binom{3}{2}y + \binom{3}{3}u=
3y + u
$$

一方

$$
B=
\frac{\binom{3}{2}}{3}y
+
\frac{\binom{3}{3}}{3}3^3 u=
y + 9u
$$

だから

$$
pB = 3y + 27u,
\qquad
C - pB = (3y+u) - (3y+27u) = -26u.
$$

確かに

$$
C - pB
$$

は \(u\) の倍数じゃが、0 ではない。
これで直感も合うのぅ。

---

## 7. . わっちの結論

よって、次に書くべき concrete kernel は、もはや

$$
B = C
\quad\text{や}\quad
C = p^p B
$$

ではない。
正しい主張はむしろ

$$
\boxed{
C = pB + uE
}
$$

という形じゃ。ここで

$$
E :=
\sum_{k=2}^{p-1}
\binom{p}{k+1}
\frac{1-p^{p(k-1)}}{\,}\,
u^{k-2} y^{p-1-k}
$$

に相当する整数係数を取ればよい。

Lean 設計としては、次のどちらかがよい。

## 7.1. . 合同版

```lean
theorem primeGe5BranchA_tailComparison_C_congr_p_mul_B_mod_u :
  C ≡ p * B [MOD (p ^ (p - 1) * t1 ^ p)]
```

## 7.2. . 余剰項分解版

```lean
theorem primeGe5BranchA_tailComparison_exists_error :
  ∃ E : ℕ, C = p * B + (p ^ (p - 1) * t1 ^ p) * E
```

わっちなら、まず後者じゃな。
存在分解のほうが packet 再構成にも obstruction extraction にも流しやすい。

## 8. . 研究上の意味

この解析が示しておるのはこうじゃ。

$$
\text{valuation peel route は exact packet reconstruction ではなく、}
$$
$$
\text{one-step linearization / first-order control の route である。}
$$

つまり、ここから smaller packet がそのまま出る望みは薄い。
じゃが代わりに、

$$
C - pB
$$

が **もう 1 段深い \(u\)-倍** だと分かったので、これは very good な obstruction data じゃ。
この情報を primitive packet descent 側へ渡す設計は、かなり筋がよい。

## 形式化して得るもの

うむ、ここで得られたものは、思ったより大きいぞい。
単に補題が 1 本増えたのではない。**valuation peel route の意味づけそのもの** が、かなりはっきりした。

## 1. . まず得られた直接の成果

いま形式化できたのは、

$$
GTail\ p\ 2\ (z-y)\ y = pB
$$

$$
GTail\ p\ 2\ \bigl(p^{p-1} t_1^p\bigr)\ y = C
$$

および

$$
z-y = p^p \bigl(p^{p-1} t_1^p\bigr)
$$

から、

$$
pB \equiv C \pmod{p^{p-1} t_1^p}
$$

を返す lower layer じゃな。
これはつまり、以前は「比較式の雰囲気」として見えておったものが、いまや **`GTail p 2` の exact coefficient 同士の合同関係** として固定された、ということじゃ。

---

## 2. . これで何が分かったか

ここが本質じゃ。

### 2.1. . (B) と (C) は恣意的な補助変数ではない

もう (B,C) は「適当に出てきた係数」ではない。
それぞれが

* 大きい gap 側の `GTail p 2`
* peeled 後の canonical gap 側の `GTail p 2`

を表すと確定した。
ゆえに比較対象は完全に **宇宙式の tail 構造そのもの** になった。

### 2.2. . 差分は exact equality ではなく mod-level control だ

得られたのは

$$
pB \equiv C \pmod{p^{p-1} t_1^p}
$$

であって、

$$
pB = C
$$

ではない。
つまり valuation peel route の本質は、**packet を exact に再構成する route** ではなく、まず

$$
\text{tail coefficient の一次近似的制御}
$$

を与える route だと、Lean 上で確定したわけじゃ。

### 2.3. . 「比較段の差分は (B) と (C) だけ」が本当に成立した

これは研究上かなり大きい。
曖昧に「どこがズレているのか」を眺める段階は終わった。

いまは、

$$
\boxed{
\text{不足情報は } pB \equiv C \pmod{p^{p-1} t_1^p}
\text{ から何を抜けるか}
}
$$

という一点に問題が集約された。

---

## 3. . ここから引き出せる数学的な意味

### 3.1. . valuation peel は obstruction extraction route として完成に近づいた

もし smaller packet 再構成に必要なのが exact tail equality なら、今回の結果はそこまで届いておらぬ。
じゃが代わりに、

$$
pB - C
$$

が

$$
p^{p-1} t_1^p
$$

で割れる、という **はっきりした障害量** が得られた。

これは very good じゃ。
なぜなら、valuation peel route を

$$
\text{packet builder}
$$

として見る代わりに、

$$
\text{obstruction extractor}
$$

として読む土台が、もう十分強くなったからじゃ。

### 3.2. . primitive packet descent を本命に押し上げる判断材料ができた

もしこの合同から先に、例えば

$$
t_1 \mid C,\quad
\text{あるいは}\quad
p \mid C,\quad
\text{あるいは}\quad
C = pB + \bigl(p^{p-1} t_1^p\bigr)E
$$

のようなさらに強い抽出が出ないなら、valuation peel 側はそこで止めてよい。
その場合は、役割は明確じゃ。

$$
\text{valuation peel} =
\text{distinguished-prime obstruction の測定器}
$$

そして本当の降下は

$$
\texttt{PrimeGe5BranchAPrimitivePacketDescentTarget}
$$

へ任せる。
今回の形式化は、その見切りを **感覚ではなく証明構造** に基づいて下せるようにした。

---

## 4. . 逆に、まだ得られていないもの

ここも大事じゃ。

今回の mod-level relation だけでは、まだ一般には

$$
\text{smaller packet}
$$

は出てこぬ。
なぜなら smaller packet には、結局

$$
GN\bigl(p,p^{p-1} t'^p,y'\bigr) = p {s'}^p
$$

という **exact normal form** が要るからじゃ。
合同だけでは、普通はそこまでは届かぬ。

つまり今の結果は、

$$
\text{smaller packet の完成}
$$

ではなく、

$$
\text{smaller packet へ届くかどうかを判定する最後の比較面}
$$

を与えた、と見るのが正しい。

---

## 5. . わっちなら次に何を見るか

わっちなら次は二択じゃ。

### 5.1. . この合同から stronger extraction を試す

例えば

$$
pB \equiv C \pmod{p^{p-1} t_1^p}
$$

を

$$
C = pB + \bigl(p^{p-1} t_1^p\bigr)E
$$

へ持ち上げて、(E) の符号・被除性・互いに素条件を調べる。
ここで新しい exact seed が出れば、valuation peel からまだ packet 再構成へ進める可能性がある。

### 5.2. . ここで valuation peel を obstruction route と確定する

もし上が弱ければ、ここで見切る。
その場合の成果は十分大きい。
なぜなら valuation peel の役割が

$$
\text{packet reconstruction}
$$

ではなく

$$
\text{tail obstruction measurement}
$$

だと Lean で確定したことになるからじゃ。
そうなれば、以後は迷わず primitive packet descent を本命にできる。

---

## 6. . 一言で総括

いま得られたものを一言で言えば、こうじゃ。

$$
\boxed{
\text{valuation peel route は、canonical tail 係数の合同制御まで形式化された。}
}
$$

そして、それが意味するのは

$$
\boxed{
\text{この route は「smaller packet の直接構成」よりも、
まず obstruction extraction の route として成熟しつつある。}
}
$$

ということじゃ。
これは後退ではない。むしろ、 **どこまでが peel の仕事で、どこからが primitive descent の仕事か** が、きれいに見え始めたということじゃよ。

次は、この合同を `exists E` 形に持ち上げたときに何が抜けるか、そこを見るのがよい。
