# FBAG-002: Goldbach 接続と bounded child fiber

## Goldbach 証明を試みた結果

`DkMath/NumberTheory/FixedBigGauge/Goldbach.lean` で次を証明した。

```text
GaugePrimePairAt R k := ∃ p q : ℕ,
  Prime p ∧ Prime q ∧ (p+q)*(R/k) = 2R

R>0, k>0 ⇒ (GaugePrimePairAt R k ↔ GoldbachPairAt k)
```

`gaugePrimePairAt_iff` が示す通り、固定するのは physical edge `R` であり、prime label の自然数中心は `k` である。
`R=n` と選んでも、`k` を変更すると解くべき自然数の和は `2k` に変わる。

`exists_gaugePrimePairAt` は、全ての `R>0` について gauge の選択による素数対があることを実際に証明した。
証人は `k=2`, `p=q=2`。この存在定理だけでは任意の自然数 `2n` の素数分解にならない。

元の label sum `p+q=2n` と physical sum を同時に要求すると、
`resolution_eq_original_of_preserved_sum` が `k=n` を、
`unit_eq_one_of_preserved_sum` が `u=1` を強制する。
これは、このログに記された単位 transport に対する厳密な情報増分の監査である。
あらゆる別の gauge 理論が不可能だという定理ではない。

元の中心を守った終点は

```text
GaugePrimePairAt n n
↔ card(goldbachCoveredSeats n (goldbachSmallPrimes n)) < n-1
```

という既存 capacity との同値 (`original_gauge_iff_capacity`) になった。
`strongGoldbach_iff_original_gauge` も証明したが、同値の右辺の独立した全称証明は得ていない。

さらに `prime_scaled_label_iff` は、素数 `p` と自然数倍率 `c` について `Prime(c*p) ↔ c=1` を証明した。
実数座標上のラベル保存から元の自然数の素数性へ、倍率だけで移行することはできない。

## 短区間での新しい有限 API

`BoundedChildren.lean` は `J={j<q | r+jM<n-1}` を定義し、以下を証明した。

- 下方閉性 (`boundedChildIndices_initial`)。
- `M≥n-1` なら可視 child の index は必ず 0。
- `n≥1` で center を一つ進める際、追加されるのは `r+jM=n-1` を満たす child だけ。
- 可視 arc における survivor と reserved の正確な cardinal conservation。
- 可視 child が3個以上なら、任意の高々2個の禁止 index を回避する child が存在する。
- 具体的な十分条件 `q>2 ∧ r+2M<n-1` から可視 child 3個以上を構成。
- 既存 `pairedReservedChildIndices_card_eq_two` に接続した `bounded_paired_survivor`。

最後の定理は fresh prime 一つの raw obstruction を回避する。
他の素数に対する survival と、可視 child 3個以上という仮定を全中心で供給してはいない。
特に `M≥n-1` の段階ではその仮定は成立できない。

`scaled_child_in_interval_iff` は child と境界を同じ正の gauge で縮小しても、元の短区間所属が厳密に不変であると証明した。

## 検証

`lean/dk_math` にて

```sh
./lean-build.sh DkMath.NumberTheory.FixedBigGauge.Goldbach DkMath.NumberTheory.FixedBigGauge.BoundedChildren
```

が終了コード 0。次のチェックポイントで具体例・全追加定理の axiom audit と最終レポートを確定する。

判定: 固定 Big の有限 API と bounded fiber の条件付き存在定理は得られた。
Strong Goldbach 自体の証明・反証は得られていない。
