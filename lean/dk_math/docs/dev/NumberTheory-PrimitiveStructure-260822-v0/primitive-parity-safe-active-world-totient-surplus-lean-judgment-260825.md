# L034 判定報告: parity-safe active world と totient surplus

## 判定

instruction-049 の有限構造 API を実装した。今回の形式化は、完全点が奇数になる
anchor-coprime seat と、anchor を割らない旧素数から `2` を除いた active world を
結び付ける。これにより、active support が pairwise disjoint なら fresh collision を
排除できる。ただし、candidate 全体を一様に供給する provider は構成していないため、
ルジャンドル予想の証明には到達していない。

## 実装

追加した Lean module は
`DkMath.NumberTheory.Legendre.ParitySafeActiveCapacity` であり、facade
`DkMath.NumberTheory.Legendre` から import する。

主な theorem surface は次の通り。

- `squareAnchorOddPointCoprimeOffsets` と membership theorem、および
  `squareAnchorOddActivePrimes`（`squareAnchorNondivisorPrimes.erase 2`）を定義した。
- Odd complete point は `squareOffsetPrimeSupport` と
  `squareOffsetAnchorNondivisorSupport` の双方で `2` を持たないことを形式化した。
- `PairwiseParitySafeActiveOldSupportDisjointSquareSeatFamily` から旧 support family
  への bridge と、完全点の pairwise coprimality theorem を実装した。
- full cover の下で family cardinal が odd active world の cardinal 以下であること、
  その strict excess から `¬ SquareOffsetsFullyCovered` および
  `∃ p, Nat.Prime p ∧ SquareCell n p` を得る obstruction/frontier consumer を実装した。
- `squareAnchorNondivisorPrimes ⊆ squareAnchorCoprimeBaseOffsets`、`1 < n` における
  strict cardinal bound、および odd active world の `Nat.totient n` 未満を実装した。
- Even anchor では odd-point candidate world が coprime world 全体に一致し、cardinal が
  `2 * Nat.totient n` になることを実装した。
- odd anchor では exact `candidate.card = Nat.totient n` は今回の module の theorem
  として固定せず、各 coprime base packet から一つを選ぶ injective packet choice により
  `Nat.totient n ≤ candidate.card` を証明した。さらに active world からの injective
  choice と追加 seat `2` により、受理条件に直接必要な `active.card < candidate.card`
  も証明した。
- `odd_anchor_five_false_beam` は、`n=5` の offsets `2, 8` が共に candidate だが、
  active old prime `3` を共有する反例を固定する。

## 数学的な境界

今回確立したのは、次の有限 implication である。

```text
parity-safe candidate family
  + pairwise disjoint active supports
  + active-card surplus
  -> complete-point pairwise coprimality
  -> no full cover / escaping square-cell prime
```

残る provider gap は、各 `n` についてこの parity-safe candidate を active support の
pairwise-disjoint family として十分な cardinal で実際に供給することである。functional
equation、prime density、limit argument、または Legendre の universal assertion は
導入していない。

## 検証

以下を実行し、L034 module が Lean 4.32.2 / Mathlib 環境で成功することを確認した。

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeActiveCapacity
```

あわせて facade target、`git diff --check`、および新規成果物に対する
`sorry` / `admit` / `axiom` / `native_decide` の placeholder audit も成功した。
commit、push、CI は instruction-049 の実装・判定範囲には含めない。
