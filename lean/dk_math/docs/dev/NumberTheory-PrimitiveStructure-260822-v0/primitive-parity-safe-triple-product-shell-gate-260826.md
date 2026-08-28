# PRIM-L042 report — parity-safe triple-product shell gate

## 判定

**Outcome A — EXACT CUBIC GATE / TRIPLE-PRODUCT WAVE SHELL**

L041 の canonical residual triple を、strict cubic square-body gate と
three-prime product wave へ有限に transportした。near/far 分解と supplied
`(n,r)=(16,17)` witness も形式化した。

これは有限 shell・divisibility・occupancy の checkpoint であり、residual ledger
の universal bound、descent、または Legendre 予想の証明ではない。

## 実装

追加した module は
`DkMath.NumberTheory.Legendre.ParitySafeTripleProductGate` で、
`DkMath.NumberTheory.Legendre` facade から import できる。

主要な theorem surface は次のとおり。

- `paritySafeTripleGatePrimes`

  `p ∈ squareAnchorOddActivePrimes n` かつ `p^3 < squareBody n` を満たす
  strict cube gate を定義する。

- `paritySafeCanonicalResidualTripleIncidence_shell_packet`

  L041 の incidence `(r,(q,s))` から canonical prime `p` を取り出し、
  `p < q < s`、`p*q*s ∣ n^2+r`、`p*q*s ≤ n^2+r ≤ squareBody n`、
  `p^3 < p*q*s`、および `p^3 < squareBody n` を証明する。

- `paritySafeTripleGateTriples`

  cube-gated canonical prime と二つの active prime を、`p < q < s` の
  ordered triple key として有限に定義する。

- `paritySafeCanonicalResidualTripleIncidence_mem_tripleGateTriples`
  / `paritySafeCanonicalResidualTripleIncidence_mem_productWave`

  各 L041 residual incidence が gate triple に入り、
  `r ∈ squareWaveOffsets n (p*q*s)` となることを示す。

- `paritySafeCanonicalResidualTripleIncidences_card_le_productWaveBudget`
  / `paritySafeResidualPairMass_le_productWaveBudget`

  residual incidence を `(triple key, r)` upper incidence へ inject し、
  residual cardinality と pair massを gated product-wave budget 以下に置く。

- `paritySafeTripleProductWaveBudget_eq_div_add_carry`

  各 product wave の cardinalityを
  `(2*n)/m + squareWaveCarry n m` へ exact に書き換える。

- `paritySafeTripleGateNearFar_disjoint`
  / `paritySafeTripleGateNearFar_union`
  / `paritySafeTripleGateNearFar_budget_decomposition`

  `m ≤ 2*n` と `2*n < m` の二領域を disjoint な有限 partition として扱い、
  budget を near/far に分解する。

- `paritySafeTripleGateNear_canonical_cube_lt_two_mul`
  / `paritySafeTripleGateFar_wave_card_le_one`

  near では `p^3 < 2*n`、far では product wave の occupancy が `≤ 1` である
  ことを示す。

- `paritySafeTripleProductGate_witness_16_17`

  `p=3,q=7,s=13`、`3^3 < squareBody 16`、`2*16 < 3*7*13`、
  `17 ∈ squareWaveOffsets 16 (3*7*13)`、および同 wave の cardinality `= 1`
  を検証する。

## strongest-beam judgment

1. L041 の triple residual は、strict cube gate を通る canonical prime と
   ordered active triple に確実に対応する。
2. divisibility は product wave の有限 occupancyへ transportでき、residual
   cardinalityは gated wave budgetに injection で支配される。
3. exact budget は quotient-plus-carry の有限和であり、near/far partition に
   よって near の cubic restriction と far の one-hit restriction を同時に
   読み出せる。
4. `(16,17)` は far one-hit の具体例として固定されるが、全 key の budgetを
   Legendre closureへ押し下げる universal estimate はまだ与えられていない。

## 停止境界と未制御 frontier

一般の k-tuples/hypergraphs、4次以上の incidence、PNT・sieve・解析的評価、
RH、descent、`LegendreConjecture` theoremは追加していない。

残る uncontrolled frontier は、
`paritySafeTripleProductWaveBudget n`（またはその near/far 分解）を residual
ledger の消滅・閾値条件へ結びつける独立の universal bound/provider である。
有限の carry identity と far の `≤ 1` だけでは、この providerは得られない。

## 検証範囲

Lean 4.32.2 / Mathlib checkoutで次を検証する。

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeTripleProductGate
lake build DkMath.NumberTheory.Legendre
git diff --check
```

新規 Lean source について `sorry`、`admit`、`axiom`、`native_decide` と末尾空白を
監査する。full repository build、commit、push、CIは bounded instruction の範囲外である。
