# Instruction 011 report

既存の canonical quotient incidence を根で分割し、候補条件を保った積波の
計数へ接続した。根3・5で211、根3・5・7で503の必要 charge を満たす。
定量証明は床関数による積波の計数から得ており、全 E または I の有限評価を
使用しない。一般の素数アンカーに対する必要 charge の一様充足は未証明。

## 1. 新しい exact ledger は必要だったか

不要。既存の
`paritySafeCanonicalQuotientCoSupportIncidences_card_eq_supportExcess`
が既に cardinality = E を証明している。新設した `canonicalRootFiber` は
その incidence の根によるフィルター、`canonicalRootPairOffsets` はその
根・二次ラベル固定の座標表示である。新しい support excess は定義していない。

## 2. 証明した完全分解

既存 incidence `(r,q)` の根を `p = paritySafeCanonicalSupportPrime n r`
とすると `p<q`。これを用いて

```text
E(n) = Σ p∈active(n), |canonicalRootFiber(n,p)|
     = Σ p∈active(n) Σ q∈active(n), p<q, |canonicalRootPairOffsets(n,p,q)|.
```

任意の有限根集合 R について、その根 fiber の cardinality の和は E 以下。
異なる根 fiber は disjoint。二次ラベルは全 active prime を使用する。

## 3. 根の最小性と smaller-prime sieve

active p について、候補以外も含めて

```text
canonical(n,r)=p
  ↔ p | n²+r ∧ ∀ a∈active(n), a<p → a ∤ n²+r.
```

を証明した。空 support のデフォルト根は0であり、正の根についての
minimum criterion にはその境界も含む。active p<q の pair fiber は
candidate な `p*q` 積波に smaller-active-prime sieve を施した集合と正確に一致。

## 4. 根3・5・7の正確な計数式

`W_n(m)` は actual candidate に限定した `m | n²+r` の積波の大きさ。
奇素数 n、奇数 m、`Coprime n m` のもとで

```text
Δ_n(m) = floor((n²+2n)/m)-floor(n²/m)
       - (floor((n²+2n)/(2m))-floor(n²/(2m)))
W_n(m) = Δ_n(m)-Δ_n(n*m).
```

第一の減算は奇数性、第二はアンカー倍数の除外。各式は Nat として定義し、
集合包含から正確性を証明した。単なる raw square wave への置換はしていない。
既存 pair-overlap との候補フィルターによる等式、および raw wave の
`2n/m + squareWaveCarry` による上界も公開した。

素数 n>7 では3・5・7が active なので、active q>p に対し

```text
root3(q) = W_n(3q)
root5(q) = W_n(5q)-W_n(15q)
root7(q) = W_n(7q)+W_n(105q)-(W_n(21q)+W_n(35q)).
```

根7は共通部分を戻してから減算する。各式を全 active q>p で和した C3、C5、C7
は既存根 fiber の大きさに等しく、C3、C3+C5、C3+C5+C7はいずれも E 以下。
一般の p についても、smaller-active-prime集合の有限 union bound を公開した。

## 5.211・503の構造的 charge

|n|A|B2|D=B2-A+1|C3|C5|C7|C3+C5|C3+C5+C7|
|---|---:|---:|---:|---:|---:|---:|---:|---:|
|211|210|307|98|78|27|15|105|120|
|503|502|813|312|222|78|36|300|336|

211では105≥98、503では336≥312。根7まで使った余裕は211で22、503で24。
211の必要な根3+5だけでも余裕7がある。

## 6. 全 E/I 評価なしに square-cell prime が証明されたか

`DkMathTest.LegendreCanonicalRootCharge.shell211_uncovered` と
`shell503_uncovered` は structural floor counts → disjoint root charge →
既存 B2 demand consumer の経路で uncoveredCandidates の Nonempty を証明する。
同モジュールの `shell211_prime` と `shell503_prime` はそれぞれ
`∃ p, Prime p ∧ n²<p ∧ p<(n+1)²` を導く。証明に特定の素数 witness や
全 E/I の直接評価は使用しない。

## 7. actual canonical-root contributions との差

根3・5・7に関して式は exact なので、構造式から old root fiber への損失は0。
`actual_root_fibers_checked` がこの等式を Lean で固定する。
独立診断では候補点を因数分解して最小 support と二次ラベルを数え、同じ値を得た。
この Python 診断は主証明の入力ではない。

|n|actual根3/5/7|raw→oddで除かれる分|odd→candidateで除かれる分|carryを捨てた比較値3/5/7|odd carryの正味寄与3/5/7|
|---|---|---|---|---|---|
|127|42 / 11 / 5|45 / 13 / 9|1 / 0 / 0|29 / 8 / 3|14 / 3 / 2|
|211|78 / 27 / 15|79 / 26 / 9|1 / 0 / 0|57 / 17 / 8|22 / 10 / 7|
|503|222 / 78 / 36|203 / 65 / 37|0 / 1 / 0|164 / 54 / 26|58 / 25 / 10|

「carryを捨てた比較値」は各 odd wave の完全周期項 `floor(n/m)` だけを
各根の同じ除外式へ入れた診断値。除外式全体の正味寄与であり、独立に証明された
新しい lower bound ではない。実装した床関数式では長周期や部分周期を正確に保持し、
carry の捨て損失は0。二次qの打ち切りも行わず、その損失も0。
smaller-prime 汚染は exact inclusion-exclusion なので過大除外0。

根7に共通部分の credit を付けない union bound を使うと、127/211/503の値は
5/14/32になり、0/1/4を失う。一方、`W7-W21-W35+W105` を Nat の逐次減算で
実行すると6/16/37となり、1ずつ過大 charge する。実装式の Nat 損失は0。

保存した反例：素数 n>7 で最初の raw odd/candidate 不一致は
n13,p3,q5,r26（点195はアンカー13の倍数）。根7の最初の共通除外例は
n67,q43,r26（点4515）。W7=W21=W35=W105=1であり、正しい残数0に対し
逐次減算式は1となる。いずれも kernel regression に保存した。

## 8. rooted star / forest と固定 CRT basis の比較

各候補座標で canonical root は一意で、support の他の方向を結ぶ star が
ちょうど `|support|-1` 本の辺を持つ。任意の supported root と相異なる
supported secondary label の集合についても、その cardinality は local excess 以下。
この局所 star 定理を証明した。一般 forest の API や graph stack は追加していない。

canonical でない固定根 star は、それぞれ局所的には安全でも、そのまま複数を
足すと過大計上し得る。support={3,5,7}で根3と根5の完全 star を両方数えると
2+2=4となり local excess=2を超える。今回の根5 sieve は3支持の座標を除き、
この問題を canonical ownership によって解消する。

全 supported pair は cycle を含み、local excess を超え得る。
n17,r26 の support={3,5,7} では local excess=2だが全 pair は3。
一方010の merged CRT は、座標ごとに witness の union を作りその cardinality−1
を charge して重複を処理する。今回の根分割は canonical ownership で重複を解消する。

固定した小さい根でも二次qを n まで増やせる点が、固定 prime basis の CRT pool
との差になる。有限211/503の障壁は超えた。ただし exact ledger の再表示だけで
一様な charge 充足が証明されるわけではない。

## 9. 最小 root cutoff

|n|A|B2|D|C3|C3+C5|C3+C5+C7|最小 cutoff|
|---|---:|---:|---:|---:|---:|---:|---:|
|47|46|54|9|12|16|20|3|
|97|96|125|30|29|39|46|5|
|127|126|170|45|42|53|58|5|
|211|210|307|98|78|105|120|5|
|503|502|813|312|222|300|336|7|

これらの数値と初期 active roots の中での最小 cutoff を kernel-check した。
有限表から cutoff の漸近的成長率は結論していない。

## 10. 残る一様定理と次の展開

`R(n,P)={p∈active(n) | p≤P}` とし、積波と有限 smaller-prime sieve から
独立に評価できる lower provider `L(n,p)` を選ぶ。必要な未証明定理は

```text
∀ n, Prime n → 7<n →
  Σ p∈R(n,P(n)), L(n,p) ≥ B2(n)-A(n)+1,
```

と、事前に指定した関数 P(n) の量的制御。条件 `L(n,p)≤|rootFiber(n,p)|` を満たす
provider は今回公開した finite-union lower estimate、または exact small-root IE。
その条件から E への和の上界、demand から prime への consumer は実装済み。
P(n)を full-root E の直接評価によって後から選ぶ方法では一様評価の欠落を解決しない。
任意の固定 cutoff 3/5/7 の一様充足も証明していない。

次の展開として、次の順序を提案する。

1. 根11について3・5・7を除外する exact finite sieve を実装し、全 secondary q
   の床関数式を保つ。根の追加と二次q範囲の追加を別々に記録する。
2. generic union bound と exact finite inclusion-exclusion を比較し、common
   contamination credit の量を調べる。Nat では positive credit と negative cost
   をまとめてから減算する。多数の根への全 symbolic IE は必要性を確認してから行う。
3. 奇数積波の床関数差を完全周期＋carryに分解し、smaller-prime 汚染と surviving
   hits に対する、点検済み表に依存しない量的下界を探す。
4. root cutoff の制御と B2 側の改善を同じ demand inequality 上で比較する。
   current exact root counting と uniform survival estimate の境界を保つ。

Legendre予想、uniform T=1、PNT/RH、解析的 sieve estimate、FLT/ABC の帰結は
この成果から主張しない。ソース・検証証跡は
[source inventory](source-inventory-011.md)、[findings](findings-011.md)、
[validation](validation-011.md) を参照。

Outcome A — CANONICAL ROOT SIEVE BREAKS FIXED-BASIS BARRIER
