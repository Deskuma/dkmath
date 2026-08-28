# Primorial Unit Universe: fresh-prime lift-index trichotomy

## 実施内容

PUU-L022 の provider-side 有限合同構造を実装した。

- `SquareAnchorPhaseLiftIndex.lean` を追加し、facade から export した。
- raw lift `b + j * M` に対する `+a`、`-a`、fresh prime `q` による deleted の
  index predicate と、phase / neutral Finset を定義した。
- L020 の phase projection fiber から、`+a` phase lift index と `-a` phase lift
  index の存在・一意性を得た。
- deleted index は既存の `existsUnique_freshPrime_dvd_lift` を再利用した。
- `+a`、`-a`、`0` の三つの index が pairwise distinct であることを、
  `hcop` による `a ≠ 0` と odd prime による `a ≠ -a` から証明した。
- phase index Finset が二つの sign index の pair と一致し、phase projection fiber
  がその raw-lift image と一致することを証明した。
- phase indices が wheel-surviving indices に含まれ、deleted index が phase set に
  入らないことを証明した。
- surviving index 数 `q - 1` と phase index 数 `2` から、neutral index 数が
  `q - 3` であることを証明した。

## 形式化した分類

```text
q raw lift indices
 = 1 deleted zero index
 + 2 phase indices (+a and -a)
 + (q - 3) neutral surviving indices.
```

fresh `q = 3` では neutral Finset が空であり、`3 < q` では neutral Finset が
nonempty であることも追加した。

## 回帰例

`S = {2,3}`, `a = b = 1`, `M = 6`, `q = 5` について raw lifts

```text
j = 0, 1, 2, 3, 4 : 1, 7, 13, 19, 25
```

を確認した。`j = 0` は `+1`、`j = 3` は `-1`、`j = 4` は `5` による
deleted index であり、phase / surviving / neutral Finset はそれぞれ

```text
{0, 3}, {0, 1, 2, 3}, {1, 2}
```

となる。

## 検証結果

- `lake build DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseLiftIndex`
  を通過した。

## 形式化上の境界

これは raw lift index と有限 survivor の分類であり、neutral index が prime または
composite であることを主張しない。Legendre、`escapingSquareOffsets`、escape existence、
gap / Jacobsthal、PowerSwap、GN/CosmicFormula、PNT、RH、prime powers、arbitrary-anchor
classification は導入していない。
