# Primorial Unit Universe: fresh-prime square-phase fiber cover

## 実施内容

PUU-L020 の provider-side 範囲を実装した。既存の
`primeBasisWheelProjection S x = x % finitePrimeBasisProduct S` を再利用し、
新しい modulo map は導入していない。

- `SquareAnchorPhaseFiberProjection.lean` を追加し、facade から export した。
- enlarged phase fiber の元が old phase fiber へ射影されることを証明した。
- `squareAnchorPhaseProjectionFiber S q a b` と membership simp theorem を追加した。
- old fiber の各代表 `b` に対し、CRT で `q` における `+a` lift と `-a` lift を
  構成した。
- fresh odd prime `q` では二つの lift が異なり、任意の projection-fiber 元が
  そのいずれかであることを示した。したがって

```lean
card_squareAnchorPhaseProjectionFiber_fresh_odd ... = 2
```

  が得られる。
- projection の surjectivity を二枚 fiber の非空性から導出した。

## 増加則

PUU-L019 の cardinality formula と fresh-product identity を組み合わせ、
fresh odd prime について

```text
fiber(insert q S) = 2 * fiber(S)
```

を証明した。また fresh `2` については `S.erase 2` の sign index が変わらず、
cardinality が不変であることを別 theorem として示した。

したがって今回の有限 cover の成長則は次の通りである。

```text
fresh q = 2    : ×1
fresh odd q    : ×2
```

これは wheel survivor の `×(q - 1)` とは異なる phase-fiber の局所構造であり、
両者を escape に結び付ける比較 theorem は追加していない。

## 回帰例

`S = {2,3}`, `a = 1`, `M = 6` から fresh `q = 5` を加えた `M' = 30` の塔について、
old representative `1` の projection fiber に `1, 19`、old representative `5` の
projection fiber に `11, 29` が属し、それぞれの cardinality が `2` であることを
Lean で確認した。

## 形式化上の境界

結果は finite congruence geometry に限定される。arbitrary-anchor cardinality、
prime-power modulus、wheel gap / Jacobsthal bound、Legendre / escape existence、
PowerSwap、GN/CosmicFormula、PNT、RH は扱っていない。特に、wheel survivor の
`q - 1` replication と square-phase fiber の `2` replication が単独で escape
existence を意味するとは主張しない。

## docstring

新規公開定義・主要 theorem と facade の module docstring に、二枚 cover、`q=2` の
退化、有限 provider-side 境界を記載した。
