# Primorial Unit Universe: fresh-prime lift-index affine normal form

## 実施内容

PUU-L025 の fresh-prime lift-index affine normal form を実装した。

- `SquareAnchorPhaseLiftIndexNormalForm.lean` を追加し、facade から export した。
- `freshPrimePhaseRadius S q a` を `ZMod q` 上の
  `a * (finitePrimeBasisProduct S)⁻¹` として定義した。これは意味上の `a / M`
  であり、`M = finitePrimeBasisProduct S` と書く。
- `freshPrimePhaseRadius_mul_period` により、fresh prime の仮定のもとで
  `radius * M = a` を証明した。また、この積の条件による半径の一意性を
  `freshPrimePhaseRadius_unique` として公開した。
- coprime anchor のもとで半径が非零であることを
  `freshPrimePhaseRadius_ne_zero` として証明した。
- L022 の `+a`、`-a`、deleted `0` の raw affine equations と `M` の非零性から、
  deleted index を中心とする座標を

  ```text
  jplus  = jzero + radius
  jminus = jzero - radius
  ```

  として証明した。これは L024 の reflection identity だけからの復元ではない。
- 二つの old representatives に対して、center-relative な plus/minus offsets が
  一致することを `freshPrime_plus_offsets_eq_across_old_representatives` で示した。
  したがって old representative `b` は deleted center を移動させるだけで、radius
  を変更しない。
- `freshPrime_phase_index_separation` により、phase pair の center-free separation
  が `jplus - jminus = 2 * radius` となることを証明した。
- `6 -> 30` の公開 regression を L025 API に接続した。

## L024 からの強化

L024 は deleted center を固定する reflection involution

```text
rho(j) = 2 * jzero - j
```

と、reflection による `+a/-a` phase pair の交換を与えた。L025 ではそこからさらに、
phase pair を明示的な center/radius 座標にした。radius は `ZMod q` の座標として
`a / M`（Lean では逆元との乗算）であり、center は old representative `b` に依存
するが radius は依存しない。

このため、phase separation `2 * radius` も `b` および deleted center `jzero` から
独立である。自然数の代表元に対する globally canonical な距離や正規化は導入して
いない。

## 回帰例

`S = {2, 3}`, `M = 6`, `q = 5`, `a = b = 1` とし、L022 の公開 regression から

```text
jplus = 0,  jzero = 4,  jminus = 3.
```

`6 = 1` in `ZMod 5` なので、公開 normal-form API は

```text
radius = 1,
0 = 4 + 1,
3 = 4 - 1,
0 - 3 = 2 * 1
```

を与える。回帰定理は detached `decide` だけに依存せず、半径・plus/minus 座標・
separation の公開定理を経由している。

## 検証結果

- `lake build DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseLiftIndexNormalForm`
  を通過した。
- `lake build DkMath.NumberTheory.PrimorialUniverse` を通過した。
- `./lb` による検証を通過した。
- 最終 build log について、`sorry` 起因の warning を除く `warning:` の追加監査を
  実施した。
- `git diff --check` を通過した。

## 形式化上の境界

本 checkpoint は finite provider-side congruence geometry に限定している。Legendre、
`escapingSquareOffsets`、escape existence、Jacobsthal / wheel gap、neutral seat の
primality / compositeness、PowerSwap、GN/CosmicFormula、PNT、RH、prime powers、
arbitrary-anchor classification、order/geodesic distance、自然数として globally
canonical な radius は導入していない。

