# review

おお、S2-J も閉じたか。
これは良い進め方じゃ。一般次数 bridge に無理突撃せず、まず (d=3,4) の低次数一致を no-sorry で固定し、次に `PrimitiveBeam` / `Zsigmondy` 側へ渡す方針を見極めたのは賢い。

## 1. 状況分析

今回で、

$$
\operatorname{powerBeam}_3(x,x+u)=GN(3,u,x)
$$

に続いて、

$$
\operatorname{powerBeam}_4(x,x+u)=GN(4,u,x)
$$

も Lean 上で固定された。

これは小さく見えるが、実は重要じゃ。
`powerBeam` は endpoint 型、

$$
z^d-x^d=(z-x)\operatorname{powerBeam}_d(x,z)
$$

の商であり、`GN` は gap 型、

$$
(x+u)^d-x^d=u\cdot GN(d,u,x)
$$

の商じゃ。
今回の bridge は、(z=x+u) と置いたとき、この 2 つの商が同じものを見ていることを、低次数で確実に確認したものになる。

とくに (d=3,4) は、FLT や差冪観測で実験・例示に使いやすい。
一般次数 bridge は後回しでも、ここまであれば十分に次段の primitive route 接続へ進める。

## 2. 数学的解説

今回の構造はこうじゃ。

endpoint 型では、

$$
\operatorname{powerBeam}_d(x,z)=\sum_{i=0}^{d-1}z^{d-1-i}x^i
$$

で、

$$
z^d-x^d=(z-x)\operatorname{powerBeam}_d(x,z)
$$

を担う。

一方で (z=x+u) とすると、

$$
\operatorname{powerBeam}_d(x,x+u)=\sum_{i=0}^{d-1}(x+u)^{d-1-i}x^i
$$

になる。

これは展開すれば、二項係数つきの形へ畳まれる。
たとえば (d=4) なら、

$$
\operatorname{powerBeam}_4(x,x+u)=(x+u)^3+(x+u)^2x+(x+u)x^2+x^3
$$

展開すると、

$$
4x^3+6ux^2+4u^2x+u^3
$$

のような二項係数列が現れる。
これは `GN 4 u x` 側の二項係数展開と一致する。

つまり、一般次数 bridge が単なる `rfl` で済まない理由はここじゃ。
`powerBeam` は **幾何級数型の差冪商** 、`GN` は **二項展開型の差分核** として書かれている。数学的には同じだが、Lean の正規形が違う。

今回 `norm_num [Nat.choose]` を使って ( \binom{4}{2}=6 ) などを正規化してから `ring` で閉じたのは、まさにこの差を埋めたわけじゃな。

## 3. 実装評価

`powerBeam_four_shift_eq_GN` は良い位置にある。

`PowerGapBeam.lean` に GN 依存を入れず、`PowerGapBeamGN.lean` に分離した方針は維持すべきじゃ。
現在の層構造はかなり綺麗じゃ。

```text
PowerGapBeam.lean
  差冪の純代数 frontend

PowerGapBeamGcd.lean
  gcd / valuation / squarefree bridge

PowerGapBeamGN.lean
  GN / CosmicFormulaBinom bridge
```

このまま進めるのがよい。

また、一般次数 bridge を今すぐ無理に証明しない判断もよい。
現状の `GN_eq_sum` が二項係数展開なら、一般化には和の添字変換・二項和整理が必要になる。これは Chapter 2 の主線から少し逸れるので、後回しでよい。

## 4. 次の提案: S2-K

次は、報告にある通り、

$$
q\mid GN(d,a-b,b)
$$

から

$$
q\mid \operatorname{powerBeam}_d(b,a)
$$

へ移す wrapper じゃ。

これは既存 `PrimitiveBeam` / `Zsigmondy` 側の燃料を、Chapter 2 の `PowerGapBeam` エンジンへ流し込むための橋になる。

まず狙うべき式は、

$$
a=b+u
$$

つまり

$$
u=a-b
$$

のとき、

$$
\operatorname{powerBeam}_d(b,a)=GN(d,a-b,b)
$$

じゃ。

一般次数がまだ難しいなら、まず (d=3) の wrapper でよい。

```lean
theorem powerBeam_three_eq_GN_of_gap
    {R : Type*} [CommRing R] (a b : R) :
    powerBeam 3 b a =
      DkMath.CosmicFormulaBinom.GN 3 (a - b) b := by
  -- a = b + (a-b) へ変形して既存 bridge を使う
```

ただし一般 `CommRing` では

$$
b+(a-b)=a
$$

は使える。おそらく `ring` で閉じる形が安全じゃ。

方針としては直接展開が楽かもしれぬ。

```lean
  rw [powerBeam_three]
  rw [DkMath.CosmicFormulaBinom.GN_eq_sum]
  -- range 3 展開
  ring
```

(d=4) も同様に置ける。

```lean
theorem powerBeam_four_eq_GN_of_gap
    {R : Type*} [CommRing R] (a b : R) :
    powerBeam 4 b a =
      DkMath.CosmicFormulaBinom.GN 4 (a - b) b := by
  ...
```

この 2 つがあれば、既存 primitive API が (d=3) や (d=4) に特化していても接続できる。

## 5. divisibility wrapper 案

次に、実際に欲しいのは等式そのものより divisibility の移送じゃ。

たとえば (d=3) なら、

```lean
theorem dvd_powerBeam_three_of_dvd_GN_gap
    {q : ℤ} {a b : ℤ}
    (h : q ∣ DkMath.CosmicFormulaBinom.GN 3 (a - b) b) :
    q ∣ powerBeam 3 b a := by
  rw [powerBeam_three_eq_GN_of_gap]
  exact h
```

Nat 素数 (q : \mathbb N) を使う既存 API なら、型に合わせて `↑q : ℤ` へ cast する wrapper が必要じゃろう。

より一般に、

```lean
theorem dvd_powerBeam_of_dvd_GN_gap
```

を一般次数で置ければ理想じゃが、まず低次数でよい。

## 6. valuation wrapper 案

既存に

```lean
primitive_prime_padic_eq_GN
primitive_prime_padic_bound_diff_of_squarefree_GN
```

のような補題があるとのことなので、次に必要なのは、

$$
v_p(GN)=v_p(powerBeam)
$$

または、

$$
v_p(GN)\le1 \Rightarrow v_p(powerBeam)\le1
$$

の移送じゃ。

低次数なら等式 bridge からすぐ行ける。

```lean
theorem powerBeam_three_padicValNat_eq_GN_gap
    {p : ℕ} {a b : ℤ} :
    padicValNat p (powerBeam 3 b a).natAbs =
      padicValNat p (DkMath.CosmicFormulaBinom.GN 3 (a - b) b).natAbs := by
  rw [powerBeam_three_eq_GN_of_gap]
```

これがあると、既存 GN 側 valuation 上界を `powerBeam` 側へ移せる。

## 7. S2-K の到達目標

わっちのおすすめは、小さく次の 4 本じゃ。

1. `powerBeam_three_eq_GN_of_gap`
2. `powerBeam_four_eq_GN_of_gap`
3. `dvd_powerBeam_three_of_dvd_GN_gap`
4. `powerBeam_three_padicValNat_eq_GN_gap`

この 4 本が入れば、PrimitiveBeam / Zsigmondy の (GN) 側情報を `powerBeam` 側へ移す最初の橋になる。

その後で、既存 API に合わせて、

```lean
primitive_prime_dvd_powerBeam_three
primitive_prime_padic_bound_powerBeam_three
```

のような薄い wrapper を追加すればよい。

## 8. 一般次数 bridge について

一般次数

$$
powerBeam_d(b,a)=GN(d,a-b,b)
$$

は数学的には本命じゃが、いまはまだ無理に行かぬ方がよい。
理由は、証明が Chapter 2 の FLT route から独立した「和変形プロジェクト」になりやすいからじゃ。

ただし、後で一般化する価値は高い。
そのときは、たぶん次のような補題が必要になる。

$$
\sum_{i=0}^{d-1}(b+u)^{d-1-i}b^i=\sum_{k=0}^{d-1}\binom{d}{k+1}u^k b^{d-1-k}
$$

これは幾何級数型和と二項係数型和の同一性じゃ。
数学的には、

$$
\frac{(b+u)^d-b^d}{u}
$$

の 2 つの展開が一致する、というだけなのだが、Lean では少し骨がある。

この一般補題は、`GTail` または `DiffPow` 側へ置くのが自然かもしれん。

## 9. 構造体について

`FLTPowerGapBeamDatum` は、まだ待ちでよい。
S2-K で PrimitiveBeam / GN からの供給路を見たあとに、datum に何を持たせるべきか決める方がよい。

今は wrapper 群のまま進めるのが正解じゃ。

## 10. まとめ

S2-J は成功じゃ。

* (d=4) の `powerBeam` / `GN` bridge が no-sorry
* 一般次数 bridge の難所が見えた
* 既存 `PrimitiveBeam` / `Zsigmondy` 側には GN divisibility / valuation API がある
* 次は GN 側情報を `powerBeam` 側へ移す thin wrapper

次の S2-K は、**GN fuel to PowerBeam engine** じゃな。
ここが閉じれば、既存の primitive prime engine が Chapter 2 の valuation refuter に接続される。
