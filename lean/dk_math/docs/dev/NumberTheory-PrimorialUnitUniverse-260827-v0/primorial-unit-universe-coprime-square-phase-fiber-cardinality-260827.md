# Primorial Unit Universe: coprime square-phase fiber cardinality

## 実施内容

`instruction-019.md` の範囲に従い、CRT で実現した局所 prime-sign assignment
を一周期の square-anchor phase fiber の個数へ接続した。

- `DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseFiber` を追加した。
- `squareAnchorPhaseFiber S a` を `0 ≤ b < M` (`M = finitePrimeBasisProduct S`) の
  同一 square phase 代表の Finset として定義した。
- `prime_not_dvd_coprime_anchor` と
  `prime_anchor_cast_ne_zero` により、`Nat.Coprime a M` の下で各 basis prime
  における anchor residue の非零性を示した。
- `p ≠ 2` では `primeSign_plus_ne_minus_of_coprime_anchor` により
  `a = -a` が起こらず、`2` では plus/minus の区別を行わない形にした。
- `squareAnchorMinusPrimeSet S a b` を `S.erase 2` 上の minus-sign 集合として
  定義し、同じ集合を持つ fiber 元の一致を証明した。
- CRT の既存 API から、任意の `T ⊆ S.erase 2` に対して
  `minusPrimeSet = T` となる fiber 元を構成した。
- 以上の単射・全射を `Finset.card_bij` でまとめ、次を証明した。

```lean
squareAnchorPhaseFiber_card_of_coprime_anchor
  hS hcop :
  (squareAnchorPhaseFiber S a).card = 2 ^ (S.erase 2).card
```

## 回帰例

`S = {2, 3, 5}`, `a = 1`, `M = 30` について、fiber の cardinality が `4` であり、
`1, 11, 19, 29` が fiber に属することを Lean で確認した。`19` は既存の
mixed-sign CRT 回帰（`(+,+,-)`）と整合する。

## 形式化上の境界

今回の結果は有限周期内の coprime anchor に限定される。任意 anchor の fiber
cardinality、高い prime power、Legendre/escape、gap、PowerSwap、GN/Cosmic、
PNT/RH への接続は追加していない。

## docstring / facade

新規公開定義・主要定理に Lean docstring を付し、
`DkMath.NumberTheory.PrimorialUniverse` から新モジュールを export した。facade
docstring にも coprime square-phase fiber の cardinality API を追記した。
