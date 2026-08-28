# Primorial Unit Universe: fresh-prime lift-index reflection involution

## 実施内容

PUU-L024 の fresh-prime raw lift index-circle reflection を実装した。

- `SquareAnchorPhaseLiftIndexReflection.lean` を追加し、facade から export した。
- deleted index を中心とする `ZMod q` reflection
  `rho(j) = 2 * jzero - j` と、その canonical natural representative を定義した。
- reflection の center fixed と involution を証明した。
- L023 の affine residue map と deleted zero residue から、reflection が raw lift
  residue を negation することを証明した。
- `+a` と `-a` の phase indices が reflection で交換されることを証明した。
- odd fresh prime では deleted center が reflection の唯一の fixed point であることを
  証明した。
- fresh-prime survivor status と L022 の neutral status が reflection-invariant である
  ことを証明した。
- 各 neutral index に対して、異なる neutral reflection partner が一意に存在し、再度の
  reflection で元に戻ることを証明した。

## L022/L023 からの強化

L022 の count/trichotomy と L023 の midpoint relation

```text
q = 1 deleted + 2 phase + (q - 3) neutral surviving
jplus + jminus = 2 * jzero  (mod q)
```

を、全 index circle 上の involution に昇格した。raw residue map

```text
F(j) = b + j*M  (mod q)
```

は deleted center `jzero` のまわりで

```text
F(rho(j)) = -F(j)
```

を満たす。そのため deleted center は固定され、phase pair は交換され、neutral
indices は fixed-point-free two-cycles を形成する。

## `q = 3` と `q > 3`

`q = 3` では L022 の neutral set が空であり、three-point index circle は phase pair
と deleted center で尽くされる。これは L021 の phase/wheel fiber equality を、単なる
cardinality 一致ではなく reflection geometry として説明する。

`3 < q` では L022 の neutral nonemptiness と L024 の partner theorem により、少なく
とも一つの neutral two-cycle が存在する。これは proper subcover の有限構造上の理由で
ある。

## 回帰例

`S = {2,3}`, `M = 6`, `q = 5`, `a = b = 1`, `jzero = 4` について、公開 reflection
API により

```text
rho(0) = 3,  rho(3) = 0,
rho(1) = 2,  rho(2) = 1,
rho(4) = 4.
```

を確認した。L022 の公開 regression と接続して、phase `{0,3}`、neutral `{1,2}`、
deleted center `4` の orbit decomposition を記録している。

## 検証結果

- `lake build DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseLiftIndexReflection`
  を通過した。

## 形式化上の境界

本 checkpoint は有限 provider-side congruence geometry に限定している。neutral seat の
primality / compositeness、escape、Legendre、`escapingSquareOffsets`、Jacobsthal / wheel
gap、PowerSwap、GN/CosmicFormula、PNT、RH、prime-power modulus、arbitrary-anchor
classification、full neutral orbit decomposition は導入していない。
