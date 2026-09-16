# PAIR-GN-002: 三次幾何と非対称 degree の可否

## 判定

提示された三次・混合 degree の多項式恒等式は正しい。
しかし **混合 `(2,3)` は `n≡8 (mod 9)` の全ての中心を表せない**。
単なる「両 degree が異なるから residue 制限がなくなる」という推論は成立しない。

## 証明済みの exact geometry

`DkMath/NumberTheory/Goldbach/PairGNCubic.lean` で以下を証明した。

- `cubic_unit`: `GN 3 1 u=3u²+3u+1`。
- `cubic_quotient_eq_iff`: quotient は任意の自然数ではなく `A=u(u+1)` と同値。
- `pairBody_three_three_eq_iff`: `2(n-1)=3(u(u+1)+v(v+1))`（`n≥1`）。
- `pairBody_three_three_eq_iff_circle`: `8n=3((2u+1)²+(2v+1)²)+2`。
- `pairBody_three_three_eq_iff_circle_sub`: 提示された `8n-2` 版（`n≥1`）。
- `center_mod_three_of_cubic_pair`: 三次同士では `n%3=1`。素数仮定すら不要。
- `pairBody_two_three_eq_iff`: 混合版 `2(n-1)=2u+3v(v+1)`（`n≥1`）。

## 新たに露出した混合版の制約

`n≡2 (mod 3)` で左の degree-two 出力を prime とすると、それは3でなければならず、`u=1` が強制される。
これが `mixed_left_parameter_eq_one`。
したがって、この中心 class では `UnitPairAt n 2 3` は厳密に

```text
∃ v>0, Prime(GN 3 1 v) ∧ 2n=GN 3 1 v+3
```

へ落ちる（`unitPairAt_two_three_iff_on_mod_three`）。

さらに全ての自然数 `v` について

```text
GN 3 1 v ≡ 1 or 7 (mod 9)
```

を `cubic_unit_mod_nine` で証明した。
`n≡8 (mod 9)` なら必要な出力 `2n-3` は4 modulo 9なので、三次 row に存在できない。
`not_unitPairAt_two_three_of_mod_nine` と `mixed_degrees_miss_progression` はこの不可能性を全称定理として固定した。

また `13≡1 (mod 3)` は prime だが cubic row の出力ではない。
`thirteen_not_in_cubic_row` は、degree の合同条件が polynomial shell の存在を保証しないことを示す。

## 情報増分の意味

三次の polynomial shell は prime-row congruence より強い制限を持つ。
今回得た強い情報は「この固定された degree family では表せない中心がある」という方向であり、Goldbach の全中心での prime pair existence を供給する方向ではない。
これを新しい Goldbach 存在証明と扱わない。

## 検証

`lean/dk_math` にて `./lean-build.sh DkMath.NumberTheory.Goldbach.PairGNCubic` が終了コード0。
次段で具体的な Goldbach 反例対比、幾何上の合成数例、全追加定理の axiom 監査を確定する。
