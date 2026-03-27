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
