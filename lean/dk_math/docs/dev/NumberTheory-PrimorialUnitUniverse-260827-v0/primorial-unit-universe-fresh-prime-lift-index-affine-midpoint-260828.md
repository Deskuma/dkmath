# Primorial Unit Universe: fresh-prime lift-index affine midpoint

## 実施内容

PUU-L023 の provider-side affine geometry を実装した。

- `SquareAnchorPhaseLiftIndexAffine.lean` を追加し、facade から export した。
- raw lift の fresh-prime residue map
  `b + j * finitePrimeBasisProduct S` を `ZMod q` 上の affine map として公開した。
- fresh prime に対して old period の `ZMod q` residue が非零であることを証明した。
- L022 の `+a`、`-a`、deleted `0` の三つの residue equation から、deleted index
  を中心とした phase offset の反対向き関係を証明した。
- deleted index が phase pair の affine midpoint であることを証明した。
- odd fresh prime では midpoint が `ZMod q` 上で一意であることを証明した。
- deleted index を中心とする reflection が `jplus` を `jminus` に送ることを証明した。

## L022 からの強化

L022 の有限 index 分解は

```text
q raw indices = 1 deleted + 2 phase + (q - 3) neutral surviving.
```

L023 では、単なる個数だけでなく、raw affine map のもとで

```text
jminus, jzero, jplus  |->  -a, 0, +a
```

となり、phase pair が fresh-prime index circle 上で deleted index を中心に対称である
ことを形式化した。old representative `b` は三つの residue equation に共通な翻訳項
なので、offset の減算で消える。

## `q = 3` と `q > 3`

`q = 3` では index circle の三点が `jminus`、`jzero`、`jplus` そのものであり、
L022 の neutral set は空になる。したがって L021 の phase/wheel fiber equality は、
個数の一致だけでなく、三点 circle の phase pair と deleted center による構造として
読める。

`q > 3` では midpoint triple の外側に neutral surviving indices が残る。これは L021
の proper subcover の構造的理由を与えるが、neutral seat の primalityや compositeness
は主張しない。

## 回帰例

`S = {2,3}`, `M = 6`, `q = 5`, `a = b = 1` で、L022 の公開 regression から

```text
jplus = 0,  jzero = 4,  jminus = 3
```

を取り出し、公開 affine theorem を通じて `ZMod 5` 上の

```text
0 - 4 = -(3 - 4)
0 + 3 = 2 * 4
3     = 2 * 4 - 0
```

を確認した。

## 検証結果

- `lake build DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseLiftIndexAffine`
  を通過した。

## 形式化上の境界

本 checkpoint は有限 provider-side affine / congruence geometry に限定している。
Legendre、`escapingSquareOffsets`、escape provider、Jacobsthal / wheel gap、PowerSwap、
GN/CosmicFormula、PNT、RH、prime powers、arbitrary-anchor classification、neutral
reflection-orbit decomposition は導入していない。
