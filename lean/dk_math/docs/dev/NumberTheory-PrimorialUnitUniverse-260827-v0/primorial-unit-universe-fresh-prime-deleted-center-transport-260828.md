# Primorial Unit Universe: fresh-prime deleted-center transport

## 実施内容

PUU-L026 の deleted-center transport / old-representative translation law を実装した。

- `SquareAnchorPhaseLiftIndexCenterTransport.lean` を追加し、facade から export した。
- old representative `b` に対する canonical deleted-center coordinate

  ```text
  C(b) = -b * M⁻¹  in ZMod q,
  ```

  を `freshPrimeDeletedCenterCoord` として定義した。ここで
  `M = finitePrimeBasisProduct S` である。
- `freshPrimeDeletedCenterCoord_zero_residue` により

  ```text
  b + C(b) * M = 0
  ```

  を証明し、`freshPrimeDeletedCenterCoord_unique` により、この zero-residue
  equation が center を一意に決定することを示した。anchor `a` や Legendre 側の
  仮定は用いていない。
- `freshPrime_deleted_index_eq_centerCoord` により、既存の deleted raw lift index
  が canonical center coordinate と一致することを、raw affine formula と uniqueness
  から証明した。
- `freshPrime_deleted_center_transport` により、二つの old representatives に対して

  ```text
  C(b₂) - C(b₁) = (b₁ - b₂) * M⁻¹
  ```

  を証明した。さらに deleted index witness 版
  `freshPrime_deleted_center_transport_indices` も追加した。
- L025 の radius と canonical center を組み合わせ、
  `freshPrime_plus_index_eq_centerCoord_add_radius` と
  `freshPrime_minus_index_eq_centerCoord_sub_radius` を追加した。依存性の分離は

  ```text
  old representative b  -> center C(b)
  anchor a              -> radius R(a)
  old period M           -> common scale
  ```

  となる。
- `freshPrime_phase_pair_translates_with_center` により、plus/minus の両 phase sheet
  が同じ center displacement だけ移動することを証明した。従って phase pair の形は
  rigid で、radius は不変である。

## L025 からの強化と Phase E1

L025 は `radius = a / M` を固定し、

```text
jplus  = jzero + radius
jminus = jzero - radius
```

を与えた。L026 は、old representative の変更で実際に移動する deleted center を
`C(b) = -b / M` として切り出した。center は `b` に依存するが、radius は依存せず、
center の移動量は `(b₁ - b₂) / M` である。

これは revised roadmap Phase E1 の最初の transport checkpoint である。

## 回帰例

`S = {2,3}`, `M = 6`, `q = 5`, `a = 1` とし、`b₁ = 1`, `b₂ = 5` を比較した。
`M = 1` in `ZMod 5` なので、公開 API により

```text
C(1) = 4,
C(5) = 0,
C(5) - C(1) = (1 - 5) / 6 = 1.
```

また `radius = 1` と L022 の deleted/phase index witnesses を用いて、

```text
b = 1 : center 4 -> {0, 3}
b = 5 : center 0 -> {1, 4}
```

を `center ± radius` 定理で確認し、両 phase sheet の displacement が同じである
ことを transport theorem で確認した。対応する enlarged seats `{1,19}` と `{11,29}`
は既存の公開 phase-projection regression により保持されている。

## 検証結果

- `lake build DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseLiftIndexCenterTransport`
  を通過した。
- `lake build DkMath.NumberTheory.PrimorialUniverse` を通過した。
- `./lb` による検証を通過した。
- 最終 build log について、`sorry` 起因の warning を除く `warning:` の追加監査を
  実施した。
- `git diff --check` を通過した。

## 形式化上の境界

本 checkpoint は finite provider-side congruence geometry と Phase E1 の transport
に限定している。square-shell escape、prime existence、Legendre、
`escapingSquareOffsets`、Jacobsthal / wheel gap、neutral seat の primality / compositeness、
PowerSwap、GN/CosmicFormula、PNT、RH、prime powers、order/geodesic distance は導入
していない。

