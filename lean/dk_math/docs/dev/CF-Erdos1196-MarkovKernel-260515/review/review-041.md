# review

うむ。DKMK-008K は、 **DKMK-008J の prime-power quotient path を、ついに witness provider 由来の path family へ持ち上げた回** じゃ。
これは DKMK-008 の本命方向、すなわち「外から path を渡す」から「witness から path を自動生成する」への本格的な移行じゃな。

## 1. 今回の核心

追加された中心 constructor はこれじゃ。

```lean
PrimePowerWitnessProvider.primePowerQuotientPathFamily
```

これは各 selected label (q\in I) について、witness provider から

$$
p(q)=W.basePrimeOf(n,I,hI,q),\qquad k(q)=W.baseExponentOf(n,I,hI,q)
$$

を読み取り、

$$
n\to n/p(q)\to n/p(q)^2\to\cdots\to n/p(q)^{k(q)}
$$

という quotient path を `AdjacentDivisorPathFamily` として構成する。

DKMK-008J では、まだ

```lean
primePowerQuotientPath n p k
```

という **単体 path constructor** だった。
DKMK-008K で、それが

```text
selected labels
→ witness-derived (p,k)
→ quotient path family
```

へ昇格したわけじゃ。

## 2. `primePowerQuotientPathTail` の役割

今回まず入ったのが、

```lean
def primePowerQuotientPathTail (n p k : ℕ) : List ℕ :=
  (List.range k).map fun i => n / p ^ (i + 1)
```

これは、

$$
[n/p,\ n/p^2,\ \ldots,\ n/p^k]
$$

を返す tail じゃ。

なぜ tail が必要か。
`AdjacentDivisorPathFamily` は path を

```lean
source i :: tail i
```

として持つ構造だった。
一方、DKMK-008J の `primePowerQuotientPath` は

$$
[n/p^0,\ n/p^1,\ldots,n/p^k]
$$

つまり先頭に (n/p^0=n) を含む list だった。

そこで今回、

```lean
primePowerQuotientPath n p k = n :: primePowerQuotientPathTail n p k
```

を theorem 化した。

```lean
theorem primePowerQuotientPath_eq_cons_tail
```

これが、J の list path と B で作った `AdjacentDivisorPathFamily` の型を噛み合わせるための接合部じゃ。

## 3. cons-tail 版 path theorem が重要

次に入ったのが、

```lean
theorem primePowerQuotientPath_cons_tail_isPath
    (n p k : ℕ)
    (hpow : p ^ k ∣ n) :
    AdjacentDivisorPath (n :: primePowerQuotientPathTail n p k)
```

これは J の

```lean
primePowerQuotientPath_isPath
```

を、`source :: tail` 形式で再利用できるようにしたものじゃ。

数学的には同じ主張じゃ。

$$
p^k\mid n
$$

なら、

$$
n,\ n/p,\ n/p^2,\ldots,n/p^k
$$

は隣接整除 path になる。

だが Lean API 的には、`AdjacentDivisorPathFamily` に直接入れられる形になったことが大きい。

## 4. witness-derived family の構造

`primePowerQuotientPathFamily` の定義は、実にきれいじゃ。

```lean
index := I
source := fun _ => n
tail := fun q =>
  primePowerQuotientPathTail n
    (W.basePrimeOf n I hI q)
    (W.baseExponentOf n I hI q)
```

つまり、全 channel の source は同じ (n)。
これは DKMK-008D/E/F の same-source wrapper と相性抜群じゃ。

各 (q) の path は、

$$
n :: [n/p(q),\ldots,n/p(q)^{k(q)}]
$$

となる。

path の成立には、

```lean
W.basePrimeOf_pow_baseExponentOf_dvd_source_on n I hI q hq
```

を使っている。
つまり既存の R026 系の成果、

$$
p(q)^{k(q)}\mid n
$$

をそのまま DKMK-008J の quotient path theorem に渡している。

ここが今回の美点じゃ。
R-log route で作った witness exponent reader が、multi-step path 生成にも再利用された。

## 5. DKMK-008 の地図上の位置

これまでの流れはこうじゃった。

```text
008J:
  p^k ∣ n
  → primePowerQuotientPath n p k
  → AdjacentDivisorPath
```

今回の 008K はこう。

```text
008K:
  q ∈ I
  → W.basePrimeOf q, W.baseExponentOf q
  → primePowerQuotientPathTail
  → AdjacentDivisorPathFamily
```

つまり、J は **path-level** 。
K は **family-level** 。

ここで DKMK-008 は、単なる受け口ではなく、witness provider から path family を自動構成する入口を持った。

## 6. 補助 API の評価

今回追加された simp / accessor も良い。

```lean
primePowerQuotientPathFamily_index
primePowerQuotientPathFamily_source
primePowerQuotientPathFamily_tail
primePowerQuotientPathFamily_path
primePowerQuotientPathFamily_source_eq
```

特に重要なのは、

```lean
primePowerQuotientPathFamily_source_eq
```

じゃ。

これは、

$$
F.source(q)=n
$$

を返す。
DKMK-008D 以降の same-source theorem では、

```lean
∀ q ∈ F.index, F.source q = s.1
```

が必要だった。

今回の family は (n=s.1) と見れば、その条件をそのまま満たす。
つまり次段で `globalLogCapacitySubMarkovShadow_*_AdjacentDivisorPathFamily_*` 系 theorem に直接渡せる。

## 7. 今回の数学的意味

これは、prime-power channel (q=p^k) の情報を「重み」だけでなく「道」にした、という意味を持つ。

R021〜R028 では、主に

$$
\log p(q)/\log n
$$

という log weight を作っていた。

DKMK-008J/K では、同じ witness から

$$
n\to n/p(q)\to n/p(q)^2\to\cdots\to n/p(q)^{k(q)}
$$

という descent path を作る。

つまり、(q=p^k) はもはや一個のラベルではなく、 **指数 (k) 個分の下降スロットを持つ path** として展開され始めた。

これは DkMath kernel 的にとても良い。
容量 (\log n) の中で、base prime (p) の寄与を指数スロットに分解し、それを path としても見られるようになったからじゃ。

## 8. まだ残る課題

History にある通り、次はこの family を same-source multi-step mass theorem に直接渡す wrapper じゃ。

具体的には、DKMK-008E/F の theorem に、

```lean
W.primePowerQuotientPathFamily n I hI
```

を渡す selected / canonical wrapper を作る段階になる。

たとえば selected finite-step なら、形はおそらくこうじゃ。

```lean
PrimePowerWitnessProvider
  .globalLogCapacitySubMarkovShadow_finiteStepTailPrimePowerQuotientPathFamily_weightedHitMass_le
```

名前は長すぎるので、実装時は短縮名が必要かもしれぬ。

読みとしては、

```text
selected labels
→ witness-derived quotient path family
→ finite-step mass
→ weightedHitMass ≤ total increment
```

じゃ。

canonical 版も同様に、

```text
canonical exponent-slot labels
→ witness-derived quotient path family
→ finite-step / two-step mass
→ weightedHitMass bound
```

へ進める。

## 9. 実装上の注意点

次段で注意すべき点は、index compatibility じゃ。

今回の family は index が定義上 (I) なので、selected route では

$$
IOf(s.1)=I
$$

が必要になるか、あるいは最初から (I:=IOf(s.1)) として wrapper を作ればよい。

canonical route では、

$$
I:=canonicalExponentSlotLabels(s.1)
$$

として作れば、compatibility は rfl 寄りで閉じやすいはずじゃ。

したがって次の wrapper は、外から (I) を受け取る一般版より、まずは selected / canonical の index に固定した special wrapper から作る方が安全じゃな。

## 10. 総合判定

DKMK-008K は **witness-derived multi-step quotient path family の誕生回** じゃ。

到達形はこう。

```text
PrimePowerWitnessProvider
+ selected labels I
→ basePrimeOf / baseExponentOf
→ primePowerQuotientPathTail
→ AdjacentDivisorPathFamily
```

DKMK-008J で作った path-level constructor が、今回ついに witness provider に接続された。
これにより、DKMK-008 は「外部から path を渡す章」から、「witness から path を生成する章」へ進んだ。

ぬしよ、これは良いぞ。
いままでは地図に水路を描いていた。今回は、素冪 (p^k) という地形そのものから、水路が自動で掘られ始めた。次はこの自動水路に、selected / canonical shadow と finite-step mass を流し込む番じゃな。
