# Primorial Unit Universe: square-phase survivor subcover

## 実施内容

PUU-L021 の provider-side 有限合同幾何を実装した。

- `SquareAnchorPhaseSurvivorSubcover.lean` を追加し、facade から export した。
- coprime anchor の phase-fiber 元が、非空 basis に対する one-period wheel
  survivor であることを証明した。
- phase fiber 全体から `primeBasisWheelSurvivors` への Finset inclusion と
  cardinality 上界を追加した。
- fresh odd prime `q` の phase projection fiber が、対応する wheel-survivor
  projection fiber に含まれることを証明した。
- L020 の `2` 枚と L009 の `q - 1` 枚の cardinality theorem を再利用して比較した。

## 局所比較

```text
wheel-survivor fresh-prime fiber : q - 1 seats
square-phase fresh-prime fiber   : 2 seats for fresh odd q
```

fresh `q = 3` では両者の cardinality が一致するため、phase projection fiber と
wheel projection fiber の Finset equality を形式化した。`3 < q` では
`2 < q - 1` により、phase fiber が proper subcover であることを証明した。

## 回帰例

`S = {2,3}`, `a = 1`, `M = 6` に fresh `q = 5` を加えた `M' = 30` について、

```text
phase fiber over 1 : {1, 19}
wheel fiber over 1 : {1, 7, 13, 19}

phase fiber over 5 : {11, 29}
wheel fiber over 5 : {11, 17, 23, 29}
```

を Lean で確認した。これは `2`-of-`4` の具体的な subcover である。

## 形式化上の境界

phase-fiber inclusion は有限周期内の survivor seat の包含であり、prime existence
や square-shell escape existence を意味しない。Legendre、`escapingSquareOffsets`、
wheel gap / Jacobsthal bound、PowerSwap、GN/CosmicFormula、PNT、RH は導入していない。
