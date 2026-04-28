# reviwe

おお、S2-K も no-sorry で通ったか。
これはかなり良い。ここで Chapter 2 の `PowerBeam` エンジンが、既存の `GN` 側情報を受け取れる形になった。つまり、これまで作ってきた FLT Gap/Beam valuation refuter に、ようやく **GN / PrimitiveBeam 側の燃料投入口** が開いたわけじゃ。

## 1. 何が閉じたか

今回の主な成果は、endpoint 型の Beam と gap 型の GN の対応じゃ。

$$
\operatorname{powerBeam}_3(b,a)=GN(3,a-b,b)
$$

$$
\operatorname{powerBeam}_4(b,a)=GN(4,a-b,b)
$$

これが `powerBeam_three_eq_GN_of_gap` と `powerBeam_four_eq_GN_of_gap` として入った。
前回の shifted bridge

$$
\operatorname{powerBeam}_d(x,x+u)=GN(d,u,x)
$$

より、今回の形の方が実戦向きじゃ。実際の FLT 文脈では (a,b) が先にあり、gap を (a-b) として読むことが多いからの。

さらに d=3 について、

```lean
dvd_powerBeam_three_of_dvd_GN_gap
```

で

$$
q\mid GN(3,a-b,b)
\Rightarrow
q\mid \operatorname{powerBeam}_3(b,a)
$$

が入り、

```lean
powerBeam_three_padicValNat_eq_GN_gap
```

で

$$
v_p(|\operatorname{powerBeam}_3(b,a)|)=v_p(|GN(3,a-b,b)|)
$$

も入った。
これは非常に使える。GN 側の divisibility / valuation 情報を、PowerBeam 側の S2-G/S2-H 矛盾エンジンに流せる入口じゃ。

## 2. 数学的意味

ここまでの流れは、かなり明確になった。

Chapter 2 の PowerBeam 側では、

$$
x^d+y^d=z^d
$$

から

$$
y^d=(z-x)\operatorname{powerBeam}_d(x,z)
$$

を得る。
そして (d=3) なら、

$$
\operatorname{powerBeam}_3(x,z)=GN(3,z-x,x)
$$

と読める。

つまり、FLT の高次差冪を

$$
\text{Gap}\times\text{PowerBeam}
$$

として見る話と、既存の

$$
\text{Gap}\times GN
$$

として見る話が一致する。

これで、既存の `PrimitiveBeam.primitive_prime_dvd_GN` のような補題が返す

$$
q\mid GN(3,a-b,b)
$$

型の情報を、

$$
q\mid \operatorname{powerBeam}_3(b,a)
$$

へ移せるようになった。
そして、いったん PowerBeam 側へ来れば、S2-H までで作った valuation contradiction engine が使える。

つまり、今回の S2-K は、

$$
GN\text{ 側 primitive 情報}
\to
PowerBeam\text{ 側 divisibility/valuation}
\to
FLT\text{ 型矛盾}
$$

の第一橋じゃ。

## 3. 実装評価

実装は良い。
特に `dvd_powerBeam_three_of_dvd_GN_gap` を `rwa [powerBeam_three_eq_GN_of_gap]` で閉じているのは薄くてよい。これは本当に bridge に徹している。

また、valuation wrapper も

```lean
rw [powerBeam_three_eq_GN_of_gap]
```

だけで閉じている。
これは等式 bridge の効果が最大限出ている証拠じゃ。

d=4 については等式 bridge までに留めたのも自然じゃ。今すぐ divisibility / valuation wrapper を増やしてもよいが、実際に既存 primitive API が d=4 をどう扱うかを見てからでも遅くない。

## 4. 次の提案: S2-L

次はいよいよ、既存 `PrimitiveBeam` の補題を **直接 PowerBeam 側へ移す specialized wrapper** を作る段階じゃ。

History にも次課題として、

* d=4 の divisibility / valuation wrapper
* `PrimitiveBeam.primitive_prime_dvd_GN` から `q ∣ powerBeam 3 b a` へ進む specialized wrapper
* GN 側 squarefree / valuation 上界を S2-G/S2-H 矛盾 API へ接続

が挙がっておる。

わっちのおすすめは、まず d=3 に集中することじゃ。

### 4.1. d=3 primitive divisibility wrapper

既存補題の正確な型に合わせる必要があるが、狙いはこう。

```lean
theorem primitive_prime_dvd_powerBeam_three
    ... :
    q ∣ powerBeam 3 b a := by
  apply dvd_powerBeam_three_of_dvd_GN_gap
  exact PrimitiveBeam.primitive_prime_dvd_GN ...
```

要は、

$$
q\mid GN(3,a-b,b)
$$

を既存補題から取り、

$$
q\mid \operatorname{powerBeam}_3(b,a)
$$

へ移す。

これは S2-K で用意した `dvd_powerBeam_three_of_dvd_GN_gap` の本来の使い道じゃ。

### 4.2. d=3 valuation upper wrapper

次に、

$$
v_p(GN(3,a-b,b))\le1
$$

のような既存補題があるなら、

$$
v_p(\operatorname{powerBeam}_3(b,a))\le1
$$

へ移す。

形としては、

```lean
theorem powerBeam_three_padicValNat_le_one_of_GN_le_one
    (hGN :
      padicValNat p (GN 3 (a-b) b).natAbs ≤ 1) :
    padicValNat p (powerBeam 3 b a).natAbs ≤ 1 := by
  simpa [powerBeam_three_padicValNat_eq_GN_gap] using hGN
```

これは一般 wrapper として先に置いてもよい。
既存 primitive 上界補題の型に依存しないので、閉じやすいはずじゃ。

### 4.3. squarefree GN から PowerBeam squarefree へ

もし既存側が

$$
Squarefree(|GN(3,a-b,b)|)
$$

を返すなら、等式 bridge から

$$
Squarefree(|powerBeam 3 b a|)
$$

へ移せる。

```lean
theorem powerBeam_three_squarefree_of_GN_squarefree
    (h :
      Squarefree (DkMath.CosmicFormulaBinom.GN 3 (a - b) b).natAbs) :
    Squarefree (powerBeam 3 b a).natAbs := by
  simpa [powerBeam_three_eq_GN_of_gap] using h
```

これが入れば、S2-H の squarefree contradiction にそのまま流せる。

## 5. d=4 について

d=4 は、等式 bridge があるので、同様に薄い wrapper は作れる。

* `dvd_powerBeam_four_of_dvd_GN_gap`
* `powerBeam_four_padicValNat_eq_GN_gap`
* `powerBeam_four_squarefree_of_GN_squarefree`

ただし FLT では (d=4) は (d=2) と深く絡むので、d=3 より扱いがやや特殊じゃ。
まず d=3 を優先してよい。

## 6. 一般次数 bridge はまだ保留

今回の報告でも確認された通り、`GN_eq_sum` は二項係数展開なので、一般次数 bridge は単純な `simp` では無理そうじゃな。

これは別タスクにした方がよい。

一般次数 bridge に必要なのは、おそらく次の恒等式。

$$
\sum_{i=0}^{d-1}(b+u)^{d-1-i}b^i=\sum_{k=0}^{d-1}\binom{d}{k+1}u^k b^{d-1-k}
$$

これは重要だが、今の FLT route の直近課題ではない。
いまは低次数 bridge と primitive route 接続を先に進める方が得策じゃ。

## 7. 構造体はもう少しだけ待つ

S2-K で wrapper 群が増えてきたので `FLTPowerGapBeamDatum` を作りたくなる。
だが、S2-L で primitive wrapper を作ると、datum に入れたい情報がさらに見える。

今はまだ、

$$
hprod,\ hgcd,\ hbeamDvd,\ hvalEq,\ hvalLeOne
$$

のどれを標準フィールドにするか揺れておる。
primitive route 接続後に固定するのがよい。

## 8. まとめ

S2-K は成功じゃ。

今回で、

$$
GN(3,a-b,b)
$$

側の divisibility / valuation 情報を、

$$
powerBeam(3,b,a)
$$

側へ移す入口ができた。

次は S2-L。

> `PrimitiveBeam` / `Zsigmondy` の GN 側情報を、d=3 の PowerBeam 側へ直接移す wrapper を作る。

これが閉じれば、Chapter 2 の valuation contradiction engine に、既存 primitive prime engine が直接接続される。
いよいよ、別々に育っていた木の根が地下でつながり始めたのう。
