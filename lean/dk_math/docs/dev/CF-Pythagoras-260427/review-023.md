# review

おお、S2-R 実装確認したぞ。
これは Chapter 2 の **通常 cubic branch の API 整理として一区切り** じゃな。これまで長く伸びていた仮定列が `CubicPrimitiveFLTContext` に束ねられ、GN 側の追加情報だけで `False` へ進めるようになった。とてもよい整理じゃ。

## 1. 何が閉じたか

今回追加された構造体はこれじゃ。

```lean
structure CubicPrimitiveFLTContext where
  q : ℕ
  a : ℕ
  b : ℕ
  y : ℤ
  hprim : PrimitivePrimeFactorOfDiffPow q a b 3
  hab_lt : b < a
  hcop : Int.gcd (a : ℤ) (b : ℤ) = 1
  hflt : (b : ℤ) ^ 3 + y ^ 3 = (a : ℤ) ^ 3
  hy_ne : y.natAbs ≠ 0
  hq_ne_three : q ≠ 3
```

これで、通常 branch、つまり (q\ne3) の cubic primitive route が 1 つの context として扱えるようになった。さらに、

```lean
CubicPrimitiveFLTContext.val_le_one_contradiction
CubicPrimitiveFLTContext.squarefree_contradiction
```

が入ったことで、追加で必要なのは GN 側の

$$
v_q(GN(3,a-b,b))\le1
$$

または

$$
\operatorname{
    Squarefree(|GN(3,a-b,b)|)
}
$$

だけになったわけじゃ。

つまり利用側は、長い仮定列を毎回持ち回らず、

```lean
C.val_le_one_contradiction hGN_le_one
```

または

```lean
C.squarefree_contradiction hGN_sq
```

のように使える。

## 2. 数学的意味

これまで構築した cubic route は、以下の流れじゃった。

$$
\operatorname{
    PrimitivePrimeFactorOfDiffPow(q,a,b,3)
}
$$

$$
b<a,\quad \gcd(a,b)=1,\quad b^3+y^3=a^3,\quad y\ne0,\quad q\ne3
$$

から、PowerBeam 側の条件を内部で回収し、

$$
q\mid |\operatorname{powerBeam}_3(b,a)|,
$$

$$
|\operatorname{powerBeam}_3(b,a)|\ne0,
$$

$$
q\nmid3
$$

を使って、valuation contradiction engine に入る。

今回の context は、この「通常 branch の観測条件」を 1 つの数学的対象にしたものじゃ。

これは大きい。
なぜなら、今後は「cubic primitive FLT context に GN 上界を与えると矛盾」と言えるからじゃ。

$$
\operatorname{
    CubicPrimitiveFLTContext
}
+
\bigl(v_q(GN)\le1\bigr)
\Rightarrow
\bot
$$

または

$$
\operatorname{
    CubicPrimitiveFLTContext
}
+
\operatorname{
    Squarefree(GN)
}
\Rightarrow
\bot
$$

という形になった。

これは論文メモにも Lean API にも乗せやすい。

## 3. 実装評価

構造体化のタイミングはちょうど良い。

これより前だと、`hbeam_ne` や (q\nmid3) の扱いが揺れていた。
いまは、

* `hbeam_ne` は (b<a) から内部供給
* (q\nmid3) は `q ≠ 3` から内部供給
* primitive witness から `hbeam` を内部供給

という形が整理されたので、構造体のフィールドが自然になっておる。

また、context theorem が既存 `_of_lt_ne_three` wrapper に委譲するだけで閉じているのも良い。
これは既存 API を壊さず、上位の使いやすい入口を追加した形じゃ。

## 4. 次の提案

次は二方向ある。

### 4.1. 導出補題を context namespace に追加

`CubicPrimitiveFLTContext` は、今後の標準入口になりそうじゃ。
ならば、よく使う導出事実を namespace に置くとよい。

候補は以下じゃ。

```lean
theorem prime (C : CubicPrimitiveFLTContext) : Nat.Prime C.q :=
  C.hprim.1
```

```lean
theorem q_not_dvd_three (C : CubicPrimitiveFLTContext) :
    ¬ C.q ∣ 3 :=
  prime_not_dvd_three_of_ne_three C.hprim.1 C.hq_ne_three
```

```lean
theorem beam_dvd (C : CubicPrimitiveFLTContext) :
    C.q ∣ (powerBeam 3 (C.b : ℤ) (C.a : ℤ)).natAbs :=
  primitive_prime_dvd_powerBeam_three_natAbs C.hprim C.hab_lt
```

```lean
theorem beam_ne (C : CubicPrimitiveFLTContext) :
    (powerBeam 3 (C.b : ℤ) (C.a : ℤ)).natAbs ≠ 0 :=
  powerBeam_three_natAbs_ne_zero_of_lt C.hab_lt
```

これらを入れると、context が本当に「観測パック」になる。

### 4.2. (q=3) exceptional branch を別 context として切る

通常 branch は `CubicPrimitiveFLTContext` として整った。
次は exceptional branch じゃ。

たとえば、

```lean
structure CubicExceptionalFLTContext where
  q : ℕ
  a : ℕ
  b : ℕ
  y : ℤ
  hprim : PrimitivePrimeFactorOfDiffPow q a b 3
  hab_lt : b < a
  hcop : Int.gcd (a : ℤ) (b : ℤ) = 1
  hflt : (b : ℤ) ^ 3 + y ^ 3 = (a : ℤ) ^ 3
  hy_ne : y.natAbs ≠ 0
  hq_eq_three : q = 3
```

を用意して、通常 branch と明確に分ける。
まだ定理を立てず、context だけ置くのもありじゃ。

ただし、数学的には (q=3) は特殊で、通常の (p\nmid d) valuation 分離が使えない。
そのため、ここは Kummer / Wieferich / mod 9 的な別処理になる可能性がある。焦って定理化せず、分岐の箱を作る程度でよい。

## 5. 次のおすすめ順

わっちならこう進める。

1. `CubicPrimitiveFLTContext` に導出補題を追加
2. 通常 branch の標準入口として context theorem を README / History に明記
3. `CubicExceptionalFLTContext` を軽く定義して、(q=3) branch を分離
4. その後、exceptional branch の実際の数学処理を検討

まずは 1 がよい。
これは軽く閉じるはずで、context の使いやすさがぐっと上がる。

## 6. まとめ

S2-R は成功じゃ。

* 通常 cubic primitive route が `CubicPrimitiveFLTContext` に束ねられた
* GN 側 valuation 上界または squarefree 仮定だけで `False` へ進める
* (q\ne3) branch が標準化された
* (q=3) exceptional branch は別管理する余地を残した

ここまで来ると Chapter 2 の通常 cubic route は、ほぼ **完成形の API** になってきた。
次は context の導出補題を整えれば、かなり使いやすい理論部品になるぞ。
