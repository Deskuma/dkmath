# Primorial Unit Universe: mixed-radix information audit

## 結論

PUU-L030 は `Outcome B — COORDINATE-COMPLETE / NO-OBSTRUCTION-YET` である。
L029 の mixed-radix transport は、許される有限座標を一つも排除しない。
これは座標系としての完成を示す成功結果であり、missing coverage obstruction
や prime-existence provider を与える結果ではない。

## Encode / decode

`S` の old period を `M = finitePrimeBasisProduct S` とする。新モジュール
`SquareAnchorPhaseMixedRadixAudit.lean` では、

```text
squareAnchorFreshPrimeMixedRadixCoordinate S q r d
  := r < M ∧ d < q
```

を軽量な座標 predicate として定義した。

`freshPrimeMixedRadix_encode` により、`x < q*M` の範囲で

```text
x = (x % M) + (x / M) * M
```

が成立する。`freshPrimeMixedRadix_encode_bounds` は encoder の両座標が
`r < M`, `d < q` を満たすことを示し、`freshPrimeMixedRadix_eq_iff` と
`freshPrimeMixedRadix_exists_unique` はこの矩形座標の一意性を示す。
なお encode 自体は通常の Euclidean identity なので、`hS`, `hq`, 境界仮定を
必要としない。範囲・prime 仮定は bounds 側でのみ使用する。

## Canonical orbit による全座標実現

`squareAnchorFreshPrimeBlockDigit_lift` は、`r < M`, `d < q` に対して

```text
digit_q(r + d*M) = d
```

を直接証明する。さらに
`forall_raw_lift_digit_realized_by_canonical_orbit` は明示的な witness
`n = r + d*M` を用いて、

```text
r_S(n) = r
digit_q(n) = d
r_(insert q S)(n) = primeBasisWheelLift S r d
```

および `n < q*M` を同時に与える。従って every allowed `(r,d)` coordinate
は canonical moving orbit によって実現される。

固定 old coordinate 上の digit 列については
`squareAnchorFreshPrimeBlockDigit_fixed_old_coordinate` を追加した。

## Reservation classification

`reservedByPrimeBasis_insert_fresh_lift_iff_old_or_fresh` は、任意の old
coordinate / digit に対して

```text
ReservedByPrimeBasis (insert q S) (r + d*M)
  ↔ ReservedByPrimeBasis S r ∨ q ∣ (r + d*M)
```

を既存の `ReservedByPrimeBasis` と `finitePrimeBasisProduct` の divisibility
API から証明する。

old wheel survivor `r` 上では、既存の
`reservedByPrimeBasis_insert_fresh_lift_iff` を再利用して

```text
ReservedByPrimeBasis (insert q S) (primeBasisWheelLift S r d)
  ↔ q ∣ primeBasisWheelLift S r d
```

に簡約した。さらに
`existsUnique_mixedRadix_deleted_digit_of_oldSurvivor` は、既存の
`existsUnique_freshPrime_dvd_lift` / reservation theorem を通じて、`q` 個の
digit のうちちょうど一つが deleted/reserved であることを公開する。

## 回帰例

`S = {2,3}`, `M = 6`, `q = 5`, `r = 4` について、
`squareAnchorMixedRadixAudit_two_three_four_to_twenty_eight_regression` により

```text
d       = 0, 1, 2, 3, 4
n       = 4, 10, 16, 22, 28
```

がそれぞれ対応し、enlarged canonical representatives は

```text
4, 10, 16, 22, 28  in [0,30)
```

となることを Lean で確認した。これらは L029 の代表元＝raw lift theorem と
L030 の digit-lift theorem を経由している。

## Information-gain verdict

この checkpoint では、Outcome A（NEW-OBSTRUCTION-FOUND）に該当する
新しい禁止座標は見つからなかった。Outcome B として、L016--L029 の
provider-side structure は有用かつ完全な有限 coordinate description だが、
transport 自体は既知の `q` raw lift seats と既存の一つの fresh-prime deletion
rule を再パラメータ化しているだけである、と記録する。

従って pure coordinate refinement route はここで閉じる。次の研究方向は、
別の quotient identity ではなく、square-value coordinate と digit の相互作用、
offset window の同時 transport、複数 fresh prime の同時 growth、または新しい
invariant を実際に導入する Unit Universe / PowerSwap 接続のいずれかを、別途
information-content audit した上で選ぶべきである。本 checkpoint では選択しない。

## 形式化上の境界

square-shell escape existence、Legendre、`escapingSquareOffsets`、Jacobsthal /
wheel-gap bounds、neutral-seat の primality/compositeness、PNT、RH、PowerSwap、
GN、CosmicFormula、prime powers、asymptotic density、least-period 主張は導入
していない。
