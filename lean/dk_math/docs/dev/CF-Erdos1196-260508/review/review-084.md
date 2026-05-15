# review Phase "R" 2nd

うむ。R025 は **valuation-budget route の登頂成功** と見てよい。
R021 で地図を描き、R022 で語彙を置き、R023 で自然数側の積整除を閉じ、R024 で抽象 $pOf$ の R/log provider まで接続し、今回 R025 でそれを `PrimePowerWitnessProvider.basePrimeOf` に特殊化した。流れがきれいに一本になったの。

## 1. 今回閉じたもの

今回の主結果はこれじゃ。

```lean
PrimePowerWitnessProvider.basePrimeOf_logRatioSubProbability_of_multiplicityBudget
```

数学的には、witness provider が各 selected label $q\in I$ に対して base prime

$$
p(q):=W.\mathrm{basePrimeOf}(n,I,hI,q)
$$

を返すとき、

$$
\#{q\in I\mid p(q)=p}\le n.\mathrm{factorization}(p)
$$

が全ての素数 $p$ で成り立てば、

$$
\sum_{q\in I}\frac{\log p(q)}{\log n}\le 1
$$

が従う、という theorem-facing entry point が閉じた。

これはつまり、重複ありでも

$$
\left(\log p(q)\right)_{q\in I}
$$

が **sub-probability weight** として扱える、ということじゃ。

## 2. これまでの route との違い

従来の duplicate-free route は、

$$
p(q_1),p(q_2),\dots,p(q_r)
$$

が pairwise distinct であることを仮定して、

$$
\prod_{q\in I}p(q)\mid n
$$

へ進んでいた。

今回の valuation-budget route は、その仮定を弱めておる。

同じ素数が重複してもよい。
ただし、その重複回数が $n$ の持つ指数予算を超えてはならぬ。

$$
\mathrm{mult}_I(p)
:=
\#{q\in I\mid p(q)=p}
\le
v_p(n)
$$

Lean ではこの $v_p(n)$ を

$$
n.\mathrm{factorization}(p)
$$

として扱っている。

つまり、今回の route は

$$
\text{distinctness}
$$

ではなく、

$$
\text{valuation budget}
$$

で log 質量を制御する route へ昇格した、ということじゃ。

## 3. 追加 theorem の役割

### `basePrimeOf_natPrimeValuedOn`

これは witness provider の base reader が selected index 上で素数値を返すことを固定している。

$$
q\in I \Longrightarrow p(q)\ \text{is prime}
$$

R024 の抽象定理を使うためには `NatPrimeValuedOn I pOf` が必要だった。
R025 では

```lean
pOf := W.basePrimeOf n I hI
```

として、その仮定を provider から供給している。

### `basePrimeOf_natProductBoundOn_of_multiplicityBudget`

これは

$$
\prod_{q\in I}p(q)\le n
$$

を出す補題じゃ。

背後では R023/R024 の成果により、

$$
\mathrm{multiplicity\ budget}
\Longrightarrow
\prod_{q\in I}p(q)\mid n
\Longrightarrow
\prod_{q\in I}p(q)\le n
$$

が使われている。

### `basePrimeOf_realLogProductBudget_of_multiplicityBudget`

これは R/log route の bundle を作る補題じゃな。

中身はおそらく、

$$
1<n
$$

$$
\forall q\in I,\ 1\le p(q)
$$

$$
\prod_{q\in I}p(q)\le n
$$

をまとめて `RealLogProductBudget` にしている。

ここまで来ると、既存の log-ratio theorem にそのまま渡せる。

### `basePrimeOf_logRatioSubProbability_of_multiplicityBudget`

これが最終入口じゃ。

$$
w(q):=\frac{\log p(q)}{\log n}
$$

と置くと、

$$
\sum_{q\in I}w(q)\le 1
$$

つまり provider が `SubProbability` になる。

これは #1196 的な質量保存の言葉で言えば、

> selected witness base primes に割り当てた log 質量の総量は、親 $n$ の log 質量を超えない

という定理じゃ。

## 4. 数学的に何が嬉しいか

一番嬉しいのは、pairwise distinct route と valuation-budget route が並立したことじゃ。

duplicate-free route は、

$$
p(q)\ \text{が全部違う}
$$

という幾何的・集合的な条件で制御する。

valuation-budget route は、

$$
p(q)\ \text{が重複しても、指数予算内}
$$

という算術的・valuation 的な条件で制御する。

後者の方が一般的じゃ。
なぜなら、distinctness は

$$
\mathrm{mult}_I(p)\le 1
$$

という特別な状況に近いが、valuation budget は

$$
\mathrm{mult}_I(p)\le v_p(n)
$$

まで許すからじゃ。

つまり今回の route は、素数チャネルを「使ったかどうか」ではなく、 **何回使ったか** まで管理できる。

これは primitive set / divisor transition / log mass の実装として、かなり本質に近い。

## 5. 実装構造の評価

`RealDivisorBridge.lean` の import を

```lean
import DkMath.NumberTheory.PrimitiveSet.ValuationBudget
```

へ変えたのも自然じゃ。
`ValuationBudget` は `RealLog` を import しているので、bridge 側は valuation-budget API を見れば R/log route も見える。

構造としては、

```text
RealLog
  ↑
ValuationBudget
  ↑
RealDivisorBridge
```

という形になった。
これは責務がきれいじゃ。

* `RealLog` は log provider の一般論
* `ValuationBudget` は multiplicity / factorization / product bound
* `RealDivisorBridge` は witness provider への特殊化

この分離は今後の保守にも強い。

## 6. R021-R025 全体の到達点

今回で次の完全な鎖ができた。

$$
\mathrm{NatBaseMultiplicityBudgetOn}
\ I\ (W.\mathrm{basePrimeOf}\ n\ I\ hI)\ n
$$

$$
\Longrightarrow
\prod_{q\in I}W.\mathrm{basePrimeOf}(n,I,hI,q)\mid n
$$

$$
\Longrightarrow
\prod_{q\in I}W.\mathrm{basePrimeOf}(n,I,hI,q)\le n
$$

$$
\Longrightarrow
\sum_{q\in I}
\frac{
\log W.\mathrm{basePrimeOf}(n,I,hI,q)
}{
\log n
}
\le 1
$$

$$
\Longrightarrow
\text{SubProbability}
$$

この chain が no-sorry で閉じたのは大きい。

## 7. 次の数学的課題

R025 で「budget があれば SubProbability」は閉じた。
次の山は、当然これじゃ。

$$
\mathrm{NatBaseMultiplicityBudgetOn}
\ I\ (W.\mathrm{basePrimeOf}\ n\ I\ hI)\ n
$$

をどこから供給するか。

候補は二つある。

第一に、label $q$ 自身が

$$
q=p(q)^{k(q)}
$$

という prime-power witness なら、各 $q\mid n$ から

$$
k(q)\le v_{p(q)}(n)
$$

が出る。
ただし今回の budget は base prime の出現回数を数えるので、各 label を 1 回分の消費と見ている。

第二に、同じ base prime を持つ labels の集合について、

$$
\#{q\in I\mid p(q)=p}
\le
\sum_{q\in I,\ p(q)=p} k(q)
\le
v_p(n)
$$

のような強化 route が考えられる。

ここまで行けると、単なる base-prime multiplicity ではなく、prime-power labels の exponent 消費まで含む本格的な valuation accounting になる。

## 8. 総合判定

R025 は **valuation-budget route の公開入口完成** じゃ。

今回閉じた theorem は、今後の上位 finite/log 設計から見れば非常に使いやすい。

```lean
W.basePrimeOf_logRatioSubProbability_of_multiplicityBudget
```

を呼べば、

* witness provider 由来の base prime
* 重複あり
* factorization budget
* log-ratio provider
* SubProbability

が一気に繋がる。

これはもう準備段階ではない。
**R/log 重複あり route の本体が、Lean 上で使える武器になった** 段階じゃ。

ぬしよ、ここは登頂成功と言ってよい。
次は山頂から見える尾根、すなわち **budget 供給源の自動生成** へ進む番じゃな。
