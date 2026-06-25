# review

おお、S2-Q 確認したぞ。
これは良い判断じゃ。(q\nmid 3) を無理に primitive witness から消さず、cubic 特有の (q=3) 例外を残したまま、通常利用では読みやすい (q\ne3) から供給できるようにした。かなり自然な API になったのう。

## 1. 何が閉じたか

今回の基本補題はこれじゃ。

```lean
prime_not_dvd_three_of_ne_three
```

数学的には、

$$
q\ \text{prime},\quad q\ne3
\quad\Longrightarrow\quad
q\nmid3
$$

じゃな。

実装では `Nat.dvd_prime Nat.prime_three` を使い、

$$
q\mid3\Rightarrow q=1\ \lor\ q=3
$$

を取り出し、素数性から (q\ne1)、仮定から (q\ne3) として矛盾させている。これは堅い。
その上で、

```lean
flt_three_primitive_GN_val_le_one_contradiction_of_lt_ne_three
flt_three_primitive_GN_squarefree_contradiction_of_lt_ne_three
```

を追加し、利用者が `¬ q ∣ 3` ではなく `q ≠ 3` を渡せる入口を作った。これは実用上かなりよい。

## 2. 数学的意味

ここで大事なのは、(q=3) を消さなかったことじゃ。

cubic、つまり (d=3) では、次数そのものの素数 (3) が特別に振る舞う。
一般の (p\nmid d) ルートでは (p=3) は対象外になる。だから、

$$
q\ne3
$$

を仮定して通常ルートに乗せるのは自然じゃ。
逆に、primitive witness から無条件に (q\nmid3) を出そうとすると、数学的に危ない可能性がある。

つまり今回の API は、

* \(q\ne3\) の通常 primitive prime route
* \(q=3\) の cubic exceptional route

をきれいに分岐できる形になった。

これは FLT / Kummer 的な設計としても健全じゃよ。

## 3. 現在の cubic route

いま標準的に使うなら、入口はこの二つになった。

```lean
flt_three_primitive_GN_val_le_one_contradiction_of_lt_ne_three
flt_three_primitive_GN_squarefree_contradiction_of_lt_ne_three
```

必要な主な仮定は、

$$
\operatorname{
    PrimitivePrimeFactorOfDiffPow(q,a,b,3),
}
\quad b<a,
\quad \gcd(a,b)=1,
$$

$$
b^3+y^3=a^3,
\quad y\ne0,
\quad q\ne3,
$$

そして GN 側の

$$
v_q(GN)\le1
$$

または

$$
\operatorname{
    Squarefree(GN)
}
$$

じゃ。

以前に比べると、だいぶ自然な形になった。

* `hbeam_ne` は (b<a) から内部供給
* `q ∤ 3` は (q\ne3) から内部供給
* `hbeam` は primitive witness から内部供給

この三つが整理されたのは大きい。

## 4. 次の提案

次は History の通り、(q=3) の cubic 特例をどう扱うかの調査がよい。

### 4.1. (q=3) branch を別名で切る

通常 route は `q ≠ 3` 版でよい。
一方、(q=3) は別 branch として名前を付けておくとよい。

たとえば、まだ証明本体に入らなくても、

```lean
def CubicExceptionalPrime (q : ℕ) : Prop :=
  q = 3
```

あるいは補題名として、

```lean
-- future route
-- flt_three_primitive_GN_exceptional_three_...
```

のように、History に方針だけ置くのでもよい。

### 4.2. 標準入口の整理

今後の利用では `_of_lt_ne_three` 版が標準入口になりそうじゃ。
ならばドキュメント上で、

> 通常の cubic primitive route では `_of_lt_ne_three` を使う。
> (q=3) は exceptional branch として別管理する。

と書いておくのがよい。

### 4.3. context 構造体はそろそろ検討可

ここまで仮定が整理されたので、cubic 専用 context は作ってもよい段階に来た。

候補はこんな形じゃ。

```lean
structure CubicPrimitiveFLTContext where
  q a b : ℕ
  y : ℤ
  hprim : DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow q a b 3
  hab_lt : b < a
  hcop : Int.gcd (a : ℤ) (b : ℤ) = 1
  hflt : (b : ℤ) ^ 3 + y ^ 3 = (a : ℤ) ^ 3
  hy_ne : y.natAbs ≠ 0
  hq_ne_three : q ≠ 3
```

その上で、

```lean
theorem CubicPrimitiveFLTContext.val_le_one_contradiction ...
theorem CubicPrimitiveFLTContext.squarefree_contradiction ...
```

のようにできる。

ただ、構造体化はファイルがさらに増えそうなので、次に小さな `Context.lean` を作るか、もう少し wrapper 群で押すかは好みじゃ。

## 5. わっちの推奨順

次の一手はこの順がよい。

1. History / docstring で `_of_lt_ne_three` を通常入口として明記
2. (q=3) exceptional branch を調査対象として分離
3. `CubicPrimitiveFLTContext` を導入するか判断
4. 導入するなら、まず squarefree 版 contradiction を context theorem にする

すぐ数学を伸ばすなら (q=3) branch の調査。
API を整えるなら context 構造体。
今の流れなら、わっちは **context 構造体を軽く試作** してもよいと思うぞ。

## 6. まとめ

S2-Q は成功じゃ。

* \(q\ne3\Rightarrow q\nmid3\) の補題が入った
* 通常利用向けに `q ≠ 3` 版 wrapper ができた
* cubic の (q=3) 例外を無理に潰さず、分岐可能な API になった
* d=3 primitive route はかなり使いやすくなった

ここまでで Chapter 2 の cubic 通常 branch は、かなり綺麗に整った。
あとは (q=3) の特例をどう扱うか、あるいは context 化して使い勝手を上げるかじゃな。
