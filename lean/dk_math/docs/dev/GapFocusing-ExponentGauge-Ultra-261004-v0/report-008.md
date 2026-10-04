# Instruction 008 — 二素数除外と局所 excess 証明書

被覆を仮定しない二素数 cap と、既存 support excess への局所証明書の埋込みを実装した。必須の殻29では座席14・56だけから excess≥4 を証明し、未被覆候補と `841<p<900` の素数を得た。主ブロックの構造上限は425から418へ改善。有限範囲2〜100では、指定した小さい証明書予算で69殻が成功し、30殻が未解決として残る。一様な Legendre 証明ではない。

[Upper production](../../../DkMath/NumberTheory/Legendre/ParitySafeIncidenceUpper.lean) · [Certificate production](../../../DkMath/NumberTheory/Legendre/ParitySafeExcessCertificate.lean) · [Mandatory regression](../../../DkMathTest/NumberTheory/LegendreHybridProvider.lean) · [Classification](../../../DkMathTest/NumberTheory/LegendreHybridClassification.lean) · [Source inventory](source-inventory-008.md) · [Findings](findings-008.md) · [Validation](validation-008.md)

## 1. 証明した正確な二素数 inclusion-exclusion は何か

neutral theorem `DkMath.NumberTheory.card_le_sub_two_exclusions` は、有限集合 D,E⊆S と C⊆S\(D∪E) から

```text
C.card ≤ S.card + (D∩E).card − (D.card+E.card)
```

を Nat のまま証明する。union/intersection の正確な cardinal identity と subset の単調性を使う。

奇素数 d≠e が n を割る場合、odd raw quotient の d 倍数・e 倍数を D,E とする。共通部分は d*e の倍数なので、007の床関数 Δ を再利用して

```text
reducedQuotient(n,q).card ≤ O(n,q)+Δ_(d*e)−(Δ_d+Δ_e)
```

となる。q>0 が端点の cardinality 同定の条件である。別の anchor 素因数があれば更に除外されるため、一般的な等号は主張しない。

失敗する式も回帰に残した。intersection credit を落とすと n30,q7,d3,e5 で上限候補2となるが、実際の波は3。正しい pair cap は3。また n105,q19,d3,e5 では pair cap4、実際の波3で、残る anchor prime7 の除外が必要。

## 2. B2 は007の上限をどれだけ改善したか

`paritySafeTwoPrimeWaveUpper` は、実際の奇素因数集合の相異なるペアについて cap を最小化する。007の `paritySafeWaveUpper` を初期値とするので、spacing・odd endpoint・一素数除外をすべて保持する。新しい shell sum は

```text
B2(n) = ∑ q∈squareAnchorOddActivePrimes n, twoPrimeWaveUpper(n,q)
I(n) ≤ B2(n) ≤ B(n).
```

両不等式は被覆仮定なしで production に証明済み。N=20,T=20 の successor 主ブロックは425→418、改善7。殻21は7→6で、strict gain も kernel checked regression にした。これらの数値が実際の incidence と一致する場合でも、上限証明の依存先は床関数と anchor divisor のみである。

殻29は素数アンカーなので pair は存在せず、B2=B=31。ここでは上限の改善ではなく、独立 excess 証明書が新しい役割を持つ。

## 3. 以前緩かった六波のうち何が補正されたか

全て補正された。実際の波 cardinality は診断にだけ使う。

| n | q | 007 cap | B2 の波 cap | 実際の波 cardinality |
| --- | --- | --- | --- | --- |
| 21 | 5 | 3 | 2 | 2 |
| 30 | 11 | 2 | 1 | 1 |
| 35 | 3 | 10 | 8 | 8 |
| 39 | 7 | 3 | 2 | 2 |
| 39 | 11 | 3 | 2 | 2 |
| 39 | 17 | 1 | 0 | 0 |

## 4. 局所 support 下限を global excess にする再利用定理は何か

`local_support_excess_ge_of_card_ge` は `k+1≤support.card` から `k≤support.card−1` を与える。`sum_local_cost_le_supportExcess` は候補の有限部分集合 R と局所下限 cost から

```text
∑ r∈R, cost(r) ≤ paritySafeSupportExcess n
```

を与える。既存の sum-subset theorem を使い、全体 excess の定義は変えていない。`sum_witness_support_excess_le_supportExcess` では、各座席の小さい witness prime set P(r)⊆actualSupport(r) だけを検証すればよい。

二座席用の `two_seat_support_card_lower_le_supportExcess` は r≠s と候補 membership、および各 support cardinality 下限から k+l≤E を導く。座席は distinct、各 witness set の素数も distinct である。異なる座席が同じ素数を持つことは許される。

汎用の `paritySafeUncovered_nonempty_of_local_witnesses` と `exists_prime_squareCell_of_local_witnesses` が cap・候補・証明書を直接接続する。hybrid gap の新しい production 定義は作っていない。

## 5. e(29)≥4 は二座席から構造的に証明したか

証明した。

| 座席 r | 点 | 証明した actual support の部分集合 | 局所 excess 下限 |
| --- | --- | --- | --- |
| 14 | 855=3²·5·19 | {3,5,19} | 2 |
| 56 | 897=3·13·23 | {3,13,23} | 2 |

候補 membership と、各素数について prime・q≤29・q≠2・q∤29・q∣29²+r を既存 membership iff で検証した。support 全体の cardinality を計算せず、witness subset の cardinality3だけを下限として使う。異なる二座席の加算定理により4≤E29。全体 excess sum の直接評価は使っていない。

## 6. 殻29の未被覆候補と素数は証明したか

B2(29)=31、A(29)=28、e=4≤E29 を Nat-safe deficit theorem に渡して

```text
1 = 28+4−31 ≤ uncoveredCandidates(29).card
```

を得た。nonempty と既存 square-cell prime consumer により `∃p, Prime p ∧ 29²<p ∧ p<30²`。実際の I(29) の評価を依存先にしていない。

## 7. 有限診断で未解決の殻は何か

範囲は2〜100。予算は最大2個の distinct 候補座席、各座席最大3個の distinct support witness prime、従って局所 excess の合計は最大4。Python は探索して有限証明データを出力するだけで、全99殻の cap/candidate 値、partition、証明書条件、成功した nonempty/prime consequences は Lean kernel で別途検証した。

| Class | 条件 | 殻数 |
| --- | --- | --- |
| 0 | B2<A、e=0 | 59 |
| 1 | A≤B2<A+4、二座席証明書によりE≥4 | 10 |
| 2 | B2≥A+4、今回の予算では criterion が失敗 | 30 |

Class1 は **29,31,32,37,38,46,49,52,77,85**。証明書の具体的な座席と素数は [Lean data](../../../DkMathTest/NumberTheory/LegendreHybridClassificationData.lean) と [診断データ](logs/classification-008.json) に記録した。

Class2 は **41,43,44,47,53,56,58,59,61,62,64,67,68,71,73,74,76,79,80,82,83,86,88,89,91,92,94,97,98,100**。

Class2 は実際に `∀e≤4, ¬B2<A+e` を証明した。「この範囲に素数がない」という意味ではない。大きい局所証明書や他の provider は排除していない。

同じ予算で007 capを使った場合の未解決33殻から、**77,85,95**が新たに成功し、30殻へ減った。各殻の old/new cap と threshold failure は kernel regression にした。減少は有限の3殻である。

## 8. 未解決殻の算術型は何か

| 型 | 未解決の n |
| --- | --- |
| prime（13殻） | 41,43,47,53,59,61,67,71,73,79,83,89,97 |
| 2^a p^k（15殻、p odd） | 44,56,58,62,68,74,76,80,82,86,88,92,94,98,100 |
| 2の冪 | 64=2^6 |
| 二つの奇素数の積 | 91=7·13 |

奇 prime power はこの範囲では未解決集合に残らない。49は局所証明書で成功する。prime31・power32・mixed38,52も局所 excess が pair 除外の不足を補える例である。一方、prime41やpower64には合計4を超える下限が必要。

一般の制約も証明した。奇素因数が高々一つなら B2=B。さらに prime p と任意の a,k について

```text
B2(2^a*p^k) = B(2^a*p^k)
```

を証明し、prime・prime power・2の冪・mixed class の pair 除外限界を一つの reusable theorem にした。指数0も含む。

## 9. 無限算術クラスの provider はあるか、正確な不足は何か

今回、無条件の無限算術クラスに対する prime-existence provider は得ていない。二つ以上の奇素因数があるだけで B2<A とする案は、77で B2=62,A=60 と反証される。二座席証明書まで許しても91は B2=76,A=72 で足りない。このデータからそのクラスを一般化していない。

不足するのは、必要 charge が増えるときに供給できる局所証明書の量である。例えば次の具体的 provider があれば、少数 odd-anchor-factor class を進められる。

```text
0<n、(n.primeFactors.erase 2).card≤1、A(n)≤B2(n) のもとで、
R⊆actualCandidates(n) と P(r)⊆actualSupport(n,r) を構成し、
  B2(n)−A(n)+1 ≤ ∑ r∈R, (P(r).card−1)
を証明する。
```

これは新しい既証明定理ではなく、必要な構成と定量条件を明記した未解決 provider である。有限の support 部分集合の生成と、その総 charge の下限を同時に保証する義務が残る。単に local witness が存在するだけでは十分でない。

## 10. 一様 A+e>B2 からどれだけ遠いか

消費側の implication と有限 subset の certificate aggregation は完成している。20個の新規 production 宣言は被覆仮定に依存しない。有限成功69殻も個別に検証済み。しかし全Nについて十分な cap 改善または十分な独立 excess を生成する theorem はない。

pair 除外が改善しない無限クラスが明確になり、91はそのクラス外でも予算4が不足する。固定予算の有限成功を一様な Legendre provider と解釈してはいない。

## 次なる展開の提案（今回未実装）

1. **必要 charge に応じた証明書生成。** 目標値 `B2−A+1` を算出し、最小限の座席・小さい prime witness subsets を選び、今回の generic theorem へ渡す。最初の明示例は41と91：どちらも e≥5 が必要。追加の算術診断で、41には座席2,24,44と witness sets{3,11,17},{5,11,31},{3,5,23}、91には座席38,44,68と{3,47,59},{3,5,37},{3,11,23}という未実装の証明候補を得た。三座席からE≥6を正式に証明できれば、両殻でU≥2を狙える。これは今回の予算外で、Lean theorem を追加したとの主張ではない。この段階でも whole-shell excess の数値表を証明の代用にしない。
2. **CRT を使う certificate family。** 複数の小さい active primes の積による congruence と parity/coprimality を保ち、window 内の distinct seat を生成する。必要なのは「候補存在」だけでなく、窓内で得られる局所 charge の個数下限。prime/prime-power class では anchor 除外よりこちらが必要な provider になる。
3. **三素数除外は別の局所改善として。** n105のように三つ以上の odd anchor factors がある場合、pair の残差を三素数 inclusion-exclusion で下げられる。一方、今回の2〜100にはその型がなく、未解決30殻を三素数 anchor 除外だけで減らすことはできない。

Outcome A — HYBRID PROVIDER GAINS NEW SHELLS
