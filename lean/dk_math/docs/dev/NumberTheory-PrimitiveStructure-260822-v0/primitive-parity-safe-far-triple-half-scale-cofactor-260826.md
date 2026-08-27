# PRIM-L043 report — parity-safe far-triple half-scale cofactor

## 判定

**Outcome A — HALF-SCALE COFACTOR COMPRESSION / OLD-SUPPORT RETURN**

L042 の far triple に対して complementary cofactor
`t = (n^2+r)/(p*q*s)` を定義し、exact factorization、half-scale compression、
reduced-residue inheritance、old-support return、および depth-or-new-direction
closure を形式化した。

ここでの cofactor compression は square-shell の有限算術であり、smaller-anchor
への `SquareOffsetsFullyCovered` 再構成や Legendre 予想の descent を意味しない。

## 実装

追加した module は
`DkMath.NumberTheory.Legendre.ParitySafeTripleFarCofactor` で、
`DkMath.NumberTheory.Legendre` facade から import できる。

主要な theorem surface は次のとおり。

- `paritySafeFarTripleCofactor`

  canonical far triple `(p,q,s)` に対する complementary cofactor `t` を定義する。

- `paritySafeFarTripleCofactor_packet`

  far residual incidence について、`0 < t`、
  `p*q*s*t = n^2+r`、`2*t < n+2`、`t < n`、および
  `Nat.Coprime (2*n) t` をまとめて返す。
  `2*t < n+2` は `n^2+r ≤ n*(n+2)` と `2*n < p*q*s` を、正の `t` に
  対して乗法単調性で接続して得ている。

- `paritySafeFarTripleCofactor_prime_divisor_return`

  `Nat.Prime u` かつ `u ∣ t` なら、`u ≤ t < n`、`u ≠ 2`、`¬u ∣ n`、
  `u ∣ n^2+r` を回収し、
  `u ∈ squareAnchorOddActivePrimes n` と
  `u ∈ paritySafeActiveSupport n r` を証明する。

- `paritySafeFarTripleCofactor_one_or_nontrivial`
  / `paritySafeFarTripleCofactor_eq_one_factorization`

  `t=1` と `1<t` の exact split を与え、terminal case では
  `p*q*s = n^2+r` を返す。

- `paritySafeFarTripleCofactor_depth_or_new_direction`

  `1<t` なら、`p^2 ∣ n^2+r`、`q^2 ∣ n^2+r`、`s^2 ∣ n^2+r` のいずれか、
  または `t` の prime divisor `u` が三方向と異なる fourth active direction
  となり、`p*q*s*u ∣ n^2+r` を満たすことを示す。
  これは既存 direction/depth obstruction への return bridgeであり、
  fourth-direction hypergraph は構築していない。

- `paritySafeFarTripleCofactor_false_beam_arithmetic`

  `25^2+2 = 3*11*19` と `25^2+38 = 3*13*17`、両方の far 条件、
  cofactor `1` の一致を arithmetic に検証する。したがって cofactor を
  residual incidence の injective coordinate として扱わない。
  residual-set membership の大規模な展開はこの theorem では複製していない。

## strongest-beam judgment

1. far triple の complementary cofactor は universally `2*t < n+2`、さらに
   triple residual の存在から `t<n` まで縮む。
2. `Nat.Coprime (2*n) (n^2+r)` は cofactor へ exact に transferされる。
3. cofactor の任意の prime divisor は同じ parity-safe active old-prime worldと
   candidate supportへ戻る。
4. `1<t` は既存三方向の prime-power depth、または fourth distinct active
   direction のどちらかへ exact に閉じる。
5. `(25,2)/(25,38)` の arithmetic false beam は、cofactor の一致が incidenceの
   injectivityを与えないことを固定する。

## 停止境界と未到達事項

smaller-anchor `SquareOffsetsFullyCovered`、generic infinite descent、fourth/fifth
direction hypergraph、PNT・sieve、RH、`LegendreConjecture` theoremは追加していない。

今回の `t<n` は cofactor scale compression に限定される。これを smaller anchor の
full-cover property、残余 ledger の消滅、または Legendre obstruction の descentへ
接続する独立 provider は、依然として未提供である。

## 検証範囲

Lean 4.32.2 / Mathlib checkoutで次を検証する。

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeTripleFarCofactor
lake build DkMath.NumberTheory.Legendre
git diff --check
```

新規 Lean source について `sorry`、`admit`、`axiom`、`native_decide` と末尾空白を
監査する。full repository build、commit、push、CIは bounded instruction の範囲外である。
