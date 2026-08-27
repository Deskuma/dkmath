# PRIM-L041 report: parity-safe star / residual / triple-direction

## 判定

Outcome A。instruction-056 の受理条件である有限 pair ledger、star + residual
の exact 分解、residual criterion、canonical quotient co-support の triple
incidence、三方向 factorization packet、`(n,r)=(16,17)` の witness を実装した。
これは有限 support と divisibility の形式化であり、ルジャンドル予想そのものの証明ではない。

## 実装

追加したモジュールは
`DkMath.NumberTheory.Legendre.ParitySafePairResidual` である。L040 の
`paritySafeCanonicalSupportPrime` と erased quotient co-support を再利用し、次を公開した。

- `paritySafePrimePairOverlapCount`：parity-safe candidate seat ごとの
  `Nat.choose activeSupport.card 2` の有限 ledger。
- `paritySafeResidualPairMass`：canonical star の二本目以降に対応する
  `Nat.choose (activeSupport.card - 1) 2` の残差 ledger。
- `paritySafePrimePairOverlapCount_le_squareAnchorCoprimePrimePairOverlapCount`：
  localized L018 pair ledger への上界。
- `paritySafePrimePairOverlapCount_eq_supportExcess_add_residual`：
  `choose k 2 = (k - 1) + choose (k - 1) 2` による exact 分解。
- `paritySafeResidualPairMass_eq_zero_iff` と
  `paritySafeResidualPairMass_pos_iff`：全 seat の support size が `≤ 2`
  であること、および support size `≥ 3` の seat の存在との同値。
- `paritySafeCanonicalResidualTripleIncidences` と
  `paritySafeCanonicalResidualTripleIncidences_card_eq_residual`：
  `(r,(q,s))`、`q < s`、erased quotient co-support の有限 incidence と exact cardinality。
- `paritySafeCanonicalResidualTripleIncidence_packet`：canonical prime `p`、
  active distinct primes `q,s`、`p*q*s ∣ n^2+r`、
  `Nat.Coprime (2*n) (p*q*s)` の packet。

facade `DkMath.NumberTheory.Legendre` にも新モジュールを追加 import した。
公開 theorem には、各定義が「distinct prime direction」を数え、prime-power
valuation mass や一般の hypergraph を導入しないことを docstring で明記した。

## 具体例

`paritySafeCanonicalResidualTriple_witness_16_17` により、

```text
16^2 + 17 = 273 = 3 * 7 * 13
activeSupport 16 17 = {3, 7, 13}
canonical prime = 3
star count = 3, support excess = 2, residual pair count = 1
triple pair = (7,13)
```

が Lean 内で確認される。`(7,13)` は erased quotient co-support の upper pair
であり、三方向 packet は上記の product divisibility と coprimality を与える。

## 停止境界

instruction-056 の指定どおり、一般 k-tuples、PNT/Mertens/Rosser/Jacobsthal、
sieve、RH、descent、あるいは residual ledger からの非自明な下界は追加していない。

## 検証

次を実行して成功した。

```text
lake build DkMath.NumberTheory.Legendre.ParitySafePairResidual
lake build DkMath.NumberTheory.Legendre
git diff --check
```

新規 Lean source の trailing whitespace および
`sorry`/`admit`/`axiom`/`native_decide` の監査も成功した。
