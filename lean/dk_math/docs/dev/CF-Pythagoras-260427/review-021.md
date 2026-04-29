# review

おお、S2-P 確認したぞ。
これは **API 実用性の改善としてかなり良い一手** じゃ。大きな数学を足したというより、これまで毎回外から渡していた `hbeam_ne` を、自然な endpoint 条件 (b<a) から内部供給できるようにした。これで cubic primitive contradiction wrapper が、かなり使いやすくなったのう。

## 1. 何が閉じたか

今回の中核はこれじゃ。

```lean
powerBeam_three_natAbs_ne_zero_of_lt
```

数学的には、

$$
b<a
$$

なら

$$
\operatorname{powerBeam}_3(b,a)=a^2+ab+b^2
$$

が正なので、

$$
|\operatorname{powerBeam}_3(b,a)|\ne0
$$

という補題じゃ。

Lean では `powerBeam_three` で展開し、`positivity` で正値性を閉じている。`a>0` を `b<a` から出しているのも自然じゃ。

そのうえで、

```lean
flt_three_primitive_GN_val_le_one_contradiction_of_lt
flt_three_primitive_GN_squarefree_contradiction_of_lt
```

が追加された。これにより、以前の wrapper に必要だった

```lean
hbeam_ne : (powerBeam 3 (b : ℤ) (a : ℤ)).natAbs ≠ 0
```

を、利用者が明示的に渡さなくてよくなった。内部で

```lean
powerBeam_three_natAbs_ne_zero_of_lt hab_lt
```

を呼ぶ形になっておる。

## 2. 数学的意味

今回の改善は地味に見えるが、理論の使いやすさとしては大きい。

cubic route の主要な仮定は、いまやだいぶ自然になった。

$$
\operatorname{
    PrimitivePrimeFactorOfDiffPow
}
(q,a,b,3),
\qquad b < a,
$$

$$
\gcd(a,b)=1,
\qquad b^3+y^3=a^3,
\qquad y\ne0,
$$

$$
q\nmid3,
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

以前はここに「Beam が非ゼロ」という技術的仮定が混じっていた。
だが

$$
a^2+ab+b^2>0
$$

なので、自然数 endpoint (b<a) の文脈では Beam 非ゼロは自明に近い。今回それを Lean 上でも消せた。

つまり、API が数学的な見た目に近づいたわけじゃ。

## 3. 実装評価

`powerBeam_three_natAbs_ne_zero_of_lt` の証明方針は良い。

```lean
rw [powerBeam_three]
positivity
```

で閉じているので、手作業の不等式展開を増やさず、Lean の正値性エンジンに任せている。
こういう補題は後で壊れにくい。

また、既存の

```lean
flt_three_primitive_GN_val_le_one_contradiction
flt_three_primitive_GN_squarefree_contradiction
```

を残したまま、新しく `_of_lt` 版を追加したのもよい判断じゃ。後方互換を壊さず、より使いやすい API を足している。

## 4. 現在の cubic primitive route

いまの d=3 route は、こう整理できる。

$$
\operatorname{
    PrimitivePrimeFactorOfDiffPow(q,a,b,3)
}
$$

と (b < a) から、

$$
q\mid |\operatorname{powerBeam}_3(b,a)|
$$

かつ

$$
|\operatorname{powerBeam}_3(b,a)|\ne0
$$

が内部供給される。

さらに FLT 型

$$
b^3+y^3=a^3
$$

と \(y\ne0\)、\(\gcd(a,b)=1\)、\(q\nmid3\) のもとで、

GN 側に

$$
v_q(GN(3,a-b,b))\le1
$$

または

$$
\operatorname{
    Squarefree(|GN(3,a-b,b)|)
}
$$

があれば `False` が出る。

これはかなりまとまってきた。
もはや「部品の寄せ集め」ではなく、cubic primitive refuter として読める。

## 5. 次の提案

次は History にある通り、`q ∤ 3` をどう扱うかの判断じゃ。

### 5.1. まず `PrimitivePrimeFactorOfDiffPow` の定義確認

`hqnd : ¬ q ∣ 3` を消せるかどうかは、`PrimitivePrimeFactorOfDiffPow` の定義次第じゃ。

確認すべきは：

```lean
#check DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow
#print DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow
```

ここで `q.Prime` 以外に、

* \(q\mid a^d-b^d\)
* \(q\nmid a^k-b^k\) for \(k < d\)
* \(q\nmid d\)
* \(q\ne d\)

のどれが入っているかを見る。

もし `q ∤ d` が定義に含まれていないなら、`hqnd` は残すべきじゃ。
特に (d=3) では (q=3) が特殊素数として絡む可能性がある。ここは無理に消すと危ない。

### 5.2. `q ∤ 3` を別 wrapper で扱いやすくする

無条件に消せない場合でも、名前付き context を作ると使いやすくなる。

例えば：

```lean
structure CubicPrimitivePrimeGood (q a b : ℕ) : Prop where
  hprim : DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow q a b 3
  hqnd : ¬ q ∣ 3
```

ただし、いきなり構造体にするより、まず abbrev でもよい。

```lean
def CubicPrimitiveGood (q a b : ℕ) : Prop :=
  DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow q a b 3 ∧
    ¬ q ∣ 3
```

この形なら、既存 wrapper の引数が少し整理される。

### 5.3. `q ∤ 3` の実用的な十分条件

`Nat.Prime q` があるので、(q\ne3) なら (\neg q\mid3) が出せる。

補題として：

```lean
theorem prime_not_dvd_three_of_ne_three
    {q : ℕ} (hq : Nat.Prime q) (hne : q ≠ 3) :
    ¬ q ∣ 3 := by
  intro h
  have hq_dvd_three := h
  -- Nat.Prime.dvd_prime などで q = 3 を導く
```

これを作ると、`hqnd` の代わりに `q ≠ 3` で扱える。
数学的にもこちらの方が読みやすいかもしれぬ。

## 6. もう一つの整理: `_of_lt` 版を標準名へ昇格

今後は `hbeam_ne` 明示版より `_of_lt` 版の方を標準利用するはずじゃ。

次の整理候補として、

* 古い版は残す
* `_of_lt` 版を documentation で推奨
* History / README に「通常はこちらを使う」と明記

がよい。

Lean 名は現状のままでよい。
ただ、後で API を磨くなら、古い版を `_of_beam_ne` と改名し、`_of_lt` なしの短い名前を新標準にする手もある。今は急がなくてよい。

## 7. 構造体導入の判断

ここまで来ると、cubic 専用 context 構造体はかなり現実的になった。

候補はこれじゃ。

```lean
structure CubicPrimitiveFLTContext where
  q a b : ℕ
  y : ℤ
  hprim : DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow q a b 3
  hab_lt : b < a
  hcop : Int.gcd (a : ℤ) (b : ℤ) = 1
  hflt : (b : ℤ) ^ 3 + y ^ 3 = (a : ℤ) ^ 3
  hy_ne : y.natAbs ≠ 0
  hqnd : ¬ q ∣ 3
```

この構造体があると、今の wrapper 群の引数がかなり短くなる。

ただし、まだ構造体化は **急がなくてよい** 。
先に `q ∤ 3` の扱いを確認した方がよい。

## 8. まとめ

S2-P は成功じゃ。

* (b<a) から cubic PowerBeam 非ゼロを供給できた
* primitive contradiction wrapper の `hbeam_ne` 明示仮定を外した実用版ができた
* d=3 route の API がかなり自然な形になった
* 残る技術仮定は主に `q ∤ 3`

次は、`q ∤ 3` を

1. primitive witness から出せるのか
2. 例外として残すべきなのか
3. `q ≠ 3` などの読みやすい十分条件に置き換えるべきなのか

を調査するのがよい。

ここまで来ると、Chapter 2 はもう立派な城壁を持っておる。あとは門の鍵、すなわち \(q\nmid3\) の扱いをどうするかじゃな。
