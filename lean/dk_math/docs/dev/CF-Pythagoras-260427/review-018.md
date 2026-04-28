# review

おお、S2-M 実装、確認したぞ。
これは **Chapter 2 の d=3 ルートが一段まとまった** と見てよい。ここで、これまで分離していた

$$
GN \rightarrow PowerBeam \rightarrow valuation\ contradiction
$$

が、実際に一発 wrapper として繋がった。

## 1. 何が閉じたか

今回追加された主補題は二つじゃな。

$$
\operatorname{padicValNat}_p(|GN(3,z-x,x)|)\le 1
$$

から d=3 の FLT 型方程式に対して `False` を出す

```lean
flt_three_beam_GN_val_le_one_contradiction
```

そして、

$$
Squarefree(|GN(3,z-x,x)|)
$$

から同じく `False` を出す

```lean
flt_three_beam_GN_squarefree_contradiction
```

じゃ。

これにより、GN 側で得た valuation 上界や squarefree 情報を、わざわざ利用者が手で `powerBeam` 側へ移さずとも、そのまま FLT contradiction engine に流し込めるようになった。

つまり、

$$
GN\text{ 側 fuel}
\to
PowerBeam\text{ bridge}
\to
S2-G/S2-H\text{ contradiction}
$$

が API として固定された。

## 2. 数学的意味

d=3 の場合、FLT 型方程式

$$
x^3+y^3=z^3
$$

から、

$$
y^3=(z-x)\operatorname{powerBeam}_3(x,z)
$$

を得る。

そして

$$
\operatorname{powerBeam}_3(x,z)=GN(3,z-x,x)
$$

なので、GN 側で

$$
v_p(GN(3,z-x,x))\le 1
$$

が得られれば、

$$
v_p(\operatorname{powerBeam}_3(x,z))\le 1
$$

となる。

一方、これまでの S2-F により、Beam 側に現れる (p\nmid 3) の素因子は

$$
v_p(\operatorname{powerBeam}_3)=3v_p(y)
$$

を満たす必要がある。

ここに

$$
p\mid \operatorname{powerBeam}_3,\qquad v_p(\operatorname{powerBeam}_3)\le1
$$

を入れると矛盾する。

今回の補題は、この流れを d=3 専用で一気通貫させたものじゃ。

## 3. 実装評価

実装としてはかなり良い。
今回の二つの wrapper は、既存の `PowerGapBeamGcd` 側の contradiction 補題に、S2-L の移送補題を渡すだけで閉じている。

たとえば valuation 版は、

```lean
powerBeam_three_padicValNat_le_one_of_GN_le_one
```

で GN 側の上界を PowerBeam 側へ移し、

```lean
flt_beam_prime_val_le_one_contradiction
```

へ渡している。

squarefree 版も同様に、

```lean
powerBeam_three_squarefree_of_GN_squarefree
```

で移送し、

```lean
flt_beam_squarefree_prime_contradiction
```

へ渡す。

この構造はとても良い。
薄い wrapper を積み重ねておるので、各補題の責務が明確じゃ。

## 4. 現在の到達点

ここまでで Chapter 2 の d=3 ルートは、かなり実用段階に入った。

流れはこうじゃ。

$$
x^3+y^3=z^3
$$

$$
y^3=(z-x)\operatorname{powerBeam}_3(x,z)
$$

$$
\operatorname{powerBeam}_3(x,z)=GN(3,z-x,x)
$$

$$
GN\text{ 側 valuation/squarefree 情報}
\Rightarrow
PowerBeam\text{ 側上界}
$$

$$
p\mid PowerBeam,\quad p\nmid3,\quad v_p(PowerBeam)\le1
\Rightarrow
False
$$

ここまで no-sorry で接続済み。
これはもう、**cubic GN fuel to FLT refuter** と呼べる。

## 5. 次の提案: S2-N

次は History にある通り、

> `primitive_prime_dvd_powerBeam_three_natAbs` を使い、Nat primitive prime witness から d=3 contradiction wrapper の `hbeam` を供給する合成補題

が自然じゃ。

今の S2-M wrapper には、まだ仮定として

```lean
hbeam : p ∣ (powerBeam 3 x z).natAbs
```

が必要じゃ。

一方、S2-L で

```lean
primitive_prime_dvd_powerBeam_three_natAbs
```

を作ってある。
これを使えば、Nat 側の primitive prime witness から `hbeam` を供給できる。

## 6. S2-N の候補

### 6.1. Primitive witness + GN valuation upper bound 版

まずは valuation 上界版。

```lean
theorem flt_three_primitive_GN_val_le_one_contradiction
    {q a b : ℕ} {y : ℤ}
    (hq : DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow q a b 3)
    (hab_lt : b < a)
    (hcop : Int.gcd (a : ℤ) (b : ℤ) = 1)
    (hflt : (b : ℤ)^3 + y^3 = (a : ℤ)^3)
    (hy_ne : y.natAbs ≠ 0)
    (hqPrime : Nat.Prime q)
    (hqnd : ¬ q ∣ 3)
    (hbeam_ne : (powerBeam 3 (b : ℤ) (a : ℤ)).natAbs ≠ 0)
    (hGN_le_one :
      padicValNat q (DkMath.CosmicFormulaBinom.GN 3 ((a : ℤ) - (b : ℤ)) (b : ℤ)).natAbs ≤ 1) :
    False := by
  apply flt_three_beam_GN_val_le_one_contradiction
  · exact hcop
  · exact hflt
  · exact hy_ne
  · exact hqPrime
  · exact hqnd
  · exact primitive_prime_dvd_powerBeam_three_natAbs hq hab_lt
  · exact hbeam_ne
  · exact hGN_le_one
```

ここで変数名は (z=a), (x=b) という対応じゃな。

### 6.2. Primitive witness + GN squarefree 版

squarefree 版もほぼ同じ。

```lean
theorem flt_three_primitive_GN_squarefree_contradiction
    {q a b : ℕ} {y : ℤ}
    (hq : DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow q a b 3)
    (hab_lt : b < a)
    (hcop : Int.gcd (a : ℤ) (b : ℤ) = 1)
    (hflt : (b : ℤ)^3 + y^3 = (a : ℤ)^3)
    (hy_ne : y.natAbs ≠ 0)
    (hqPrime : Nat.Prime q)
    (hqnd : ¬ q ∣ 3)
    (hbeam_ne : (powerBeam 3 (b : ℤ) (a : ℤ)).natAbs ≠ 0)
    (hGN_sq :
      Squarefree (DkMath.CosmicFormulaBinom.GN 3 ((a : ℤ) - (b : ℤ)) (b : ℤ)).natAbs) :
    False := by
  apply flt_three_beam_GN_squarefree_contradiction
  · exact hcop
  · exact hflt
  · exact hy_ne
  · exact hqPrime
  · exact hqnd
  · exact primitive_prime_dvd_powerBeam_three_natAbs hq hab_lt
  · exact hbeam_ne
  · exact hGN_sq
```

これはかなり薄い wrapper なので、閉じやすいはずじゃ。

## 7. 注意点

ここで一つ気をつけたいのは、`PrimitivePrimeFactorOfDiffPow` が `Nat.Prime q` や (q\nmid3) をすでに含んでいる可能性があることじゃ。

もし構造体や predicate にそれらの情報が入っているなら、

```lean
hqPrime
hqnd
```

を別仮定にせず、既存 projection / theorem で取り出す方がよい。

ただし最初は明示仮定でよい。
後で API を薄くできる。

## 8. ファイル分割について

`PowerGapBeamGN.lean` が `PowerGapBeamGcd` と `PrimitiveBeam` の両方を import するようになり、少し重くなってきた。

次の S2-N で primitive contradiction wrapper を追加すると、より重くなる。
そろそろ分割を考えてもよい。

おすすめはこれじゃ。

```text
PowerGapBeamGN.lean
  pure GN bridge
  powerBeam_three_eq_GN_of_gap
  powerBeam_four_eq_GN_of_gap
  valuation/squarefree transfer

PowerGapBeamPrimitive.lean
  imports PrimitiveBeam + PowerGapBeamGN + PowerGapBeamGcd
  primitive_prime_dvd_powerBeam_three_natAbs
  primitive contradiction wrappers
```

ただし、いまの作業速度を優先するなら、S2-N まで今のままでもよい。
分割はその後の整理で十分じゃ。

## 9. 構造体導入について

`FLTPowerGapBeamDatum` は、もう導入してもよい段階に近づいている。
ただ、S2-N で primitive witness までつないだ後の方が、フィールド構成が見える。

現時点で構造体を作るなら、最低限は：

```lean
structure FLTPowerGapBeamDatum where
  gap : ℤ
  beam : ℤ
  hprod : side ^ d = gap * beam
  hgcd : Int.gcd gap beam ∣ d
  hbeam_dvd : p ∣ beam.natAbs
  hbeam_ne : beam.natAbs ≠ 0
  hval_eq : padicValNat p beam.natAbs = d * padicValNat p side.natAbs
```

しかし primitive / squarefree route ではさらに `hval_le_one` や `hsq` も欲しくなる。
まだ wrapper で良い。

## 10. まとめ

S2-M は成功じゃ。
これで d=3 について、

$$
GN\text{ valuation/squarefree fuel}
\Rightarrow
PowerBeam\text{ valuation refuter}
\Rightarrow
False
$$

が no-sorry でつながった。

次は S2-N。

> primitive prime witness から `hbeam` を供給し、d=3 の contradiction wrapper へ直接接続する。

ここが閉じると、Chapter 2 は **PrimitiveBeam fuel to cubic FLT contradiction** まで進む。
ふふ、ここまでの橋の架け方はなかなか見事じゃ。わっちの尻尾も機嫌よく揺れておるぞ。
