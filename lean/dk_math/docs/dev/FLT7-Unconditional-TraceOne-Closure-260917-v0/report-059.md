# FLT7TC-005R53 — Current Eisenstein coprimality and unique tauSq sector

## 調査開始時点

`instruction-059.md`、R52 report、R52 production module、および FLT3 の
Eisenstein substrate/cube/unit-sector API を確認する。今回の実装境界は、
current `C = 1` branch に対する `3 ∤ q`、delta と共役の relative primality、
cube extraction packet、mod 7 の sector 固定、および残る F_5 equation の記録である。

generic Thue solver、外部分類、FLT3 terminal contradiction、有限 unbounded search、
congruence からの整数等式化は行わない。

## 実装進行

R53 用の調査・検証記録を作成した。既存 R52 module を変更せず、必要な current
bridge theorem は同 module または新規 production module に局所追加する。

## Part A — 3 は current q を割らない

新規 module
`DkMath/FLT/Seven/SevenRealCubicEisensteinCoprimality.lean` を追加した。
`sourcePlaneNormSeven_three_not_dvd_q` により、

```text
F(a,b) = -7,  Q(a,b) = 7*q  ->  not (3 | q)
```

を証明した。`3 | Q` から `3 | (a-b)^2`、prime の power divisibility から
`3 | a-b` を得て `a = b + 3*d` と置き、
`F(b+3*d,b) = b^3 + 9*(2*b^2*d + 5*b*d^2 + 3*d^3)` を展開した。
その結果 `9 | b^3 - 2` となり、`ZMod 9` の finite `decide` lemma
`∀ x, x^3 ≠ 2` で閉じた。

R52 の `A,m` parameter に直接接続する
`sourcePlaneNormSeven_parameter_three_not_dvd_q` も追加した。

## Part B–C — q と s の相対素性、および delta の共役相対素性

`eisenstein_current_q_coprime_s` は `Int.isCoprime_iff_nat_coprime` と
prime divisor route を使う。共通素数 `p` が q と s を割ると、
`norm delta = q^3` から `p | r^2`、prime の power divisibility から `p | r`
を得て、`5*r + 8*s = 3` から `p | 3` となる。`p = 3` は Part A と矛盾する。

続く `eisenstein_current_relPrime_conj` では、common divisor d について
`d | delta - conj delta` を取り、norm divisibility から
`norm d | q^3` と `norm d | 3*s^2` を得た。Part B と `3 ∤ q` により
`IsCoprime (q^3) (3*s^2)` を構成し、`norm d` が unit、かつ非負なので
`norm d = 1`、従って d が Eisenstein unit であることを kernel-check した。

## Part D–F — cube packet、tauSq 固定、F_5

`EisensteinCurrentCubeSectorPacket` と
`eisenstein_current_cube_sector_packet` を追加した。packet には q,r,s,h、
sector、gamma、

```text
delta = sector.rep * gamma^3
norm gamma = q
h = 3*r - 5*s
5*r + 8*s = 3
7^8 | r+1,  7^8 | s-1
```

を保持させた。`norm gamma = q` は sector の norm-one、norm の power
multiplicativity、非負 norm 上の整数 cube injectivity から証明した。

`eisenstein_current_sector_eq_tauSq` は R52 の `pi7^2` stripping と
`eisenstein_sector_second_coordinate` を接続し、`ZMod 7` の有限 `decide`
判定で `.one` と `.tau` を排除した。.tauSq の second-coordinate は残るため、
sector は `.tauSq` と kernel-check した。続いて
`eisenstein_current_tauSq_FiveEquation` により、残る正確な式

```text
R^3 - 5*R^2*S - 8*R*S^2 - S^3 = 1
```

を得た。

## 検証結果と境界

新規 module の単体ビルド:

```text
lake build DkMath.FLT.Seven.SevenRealCubicEisensteinCoprimality
```

は `Build completed successfully (9208 jobs)` となった。公開 facade に新規 module
を追加し、facade build:

```text
lake build DkMath.FLT.Seven
```

も `Build completed successfully (9255 jobs)` となった。

今回 kernel-check できたのは Outcome B の前半から F までである。q=1、F_5 の
外部分類、有限 shell classification、C=1 の最終排除、G–I の q=1 route は追加して
いない。したがって現時点の正確な残りは、

```text
R^3 - 5*R^2*S - 8*R*S^2 - S^3 = 1
7^8 | R*S*(R+S)
q = R^2 + R*S + S^2 > 0
```

を含む高深度 current branch の後続処理であり、今回の production API はここを
未解決のまま保持する。
