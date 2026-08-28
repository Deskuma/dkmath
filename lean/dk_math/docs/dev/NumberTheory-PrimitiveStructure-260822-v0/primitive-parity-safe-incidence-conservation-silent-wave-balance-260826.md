# L036 判定報告: parity-safe incidence conservation

## Outcome

判定は **A — EXACT INCIDENCE CONSERVATION / SILENT-ESCAPE FRONTIER COMPRESSION**。

新しい provider は導入せず、L034/L035 の parity-safe wave と candidate support を
prime-wave 側・candidate 側から二重計数した。有限 incidence ledger は exact に閉じ、
残る corrected criterion を silent active wave と uncovered candidate の比較へ変形した。

universal `silent.card < uncovered.card` は証明していない。従ってこれは finite balance
frontier の確立であり、Legendre 予想の証明ではない。

## 実装

追加した [ParitySafeIncidenceBalance.lean](/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMath/NumberTheory/Legendre/ParitySafeIncidenceBalance.lean:1)
を [Legendre.lean](/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMath/NumberTheory/Legendre.lean:22)
から import した。

主な theorem surface:

- `paritySafeActiveSupport` と、candidate 上で old nondivisor support と一致する
  exact theorem。
- `paritySafeIncidenceCount` の wave-side / candidate-side transpose。
- `paritySafeNonemptyActivePrimes`、`paritySafeSilentActivePrimes` と
  `nonempty.card + silent.card = active.card`。
- `paritySafeCoveredCandidates`、`paritySafeUncoveredCandidates` と、
  `candidate ∧ ¬ SquareOffsetCovered` の exact membership theorem。
- uncovered candidate から既存 Frontier API を経由した square-cell prime consumer。
- local extra cardinal equality と、
  `nonempty.card + duplicateBudget = incidence`。
- candidate support excess `paritySafeSupportExcess`、covered/uncovered partition、
  `covered.card + supportExcess = incidence`。
- main conservation law:

  ```text
  nonempty.card + duplicateBudget + uncovered.card
    = candidate.card + supportExcess
  ```

- active decomposition を併用した corrected residual criterion:

  ```text
  active.card + duplicateBudget < candidate.card + supportExcess
    ↔ silent.card < uncovered.card
  ```

## Stronger-beam judgment

推奨された `(n,q)=(12,11)` は次のように判定した。

- `11 ∈ squareAnchorOddActivePrimes 12`
- `paritySafeActiveWaveOffsets 12 11 = ∅`
- seat `11` は parity-safe candidate
- `12^2 + 11 = 155` は active old prime `5` により cover される
- 従って `q ↦ q` は silent wave から uncovered candidate への injection にならない

なお、候補 offset `21` は `12` と coprime でないため parity-safe candidate ではない。
この concrete correction は
`instruction051_n12_prime_eleven_silent_false_injection` に固定した。

したがって、単純な silent-to-uncovered injection の universal proof は追加していない。
PNT、Jacobsthal bound、解析的 sieve、general graph/matching、descent、
`LegendreConjecture` theorem も導入していない。

## 検証

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeIncidenceBalance
lake build DkMath.NumberTheory.Legendre
git diff --check
```

新規 Lean source の trailing whitespace と `sorry` / `admit` / `axiom` /
`native_decide` を監査済みである。full repository build、commit、push、CI は実施しない。
