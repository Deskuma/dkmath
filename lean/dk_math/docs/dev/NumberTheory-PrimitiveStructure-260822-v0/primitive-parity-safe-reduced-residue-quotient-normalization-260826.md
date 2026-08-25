# L037 判定報告: parity-safe reduced-residue / quotient normalization

## 判定

判定は **Outcome A — EXACT REDUCED-RESIDUE / QUOTIENT NORMALIZATION FRONTIER**。

L034--L036 の parity-safe candidate を modulus `2*n` の reduced-residue world
として正規化し、active prime wave を complementary quotient の有限 interval に
移した。候補 cardinality、wave/quotient cardinality、同一 wave の重複剛性、全体の
incidence rewrite は exact に形式化できた。一方、これだけから Legendre 予想に
十分な universal cardinal inequality は導入していない。

## 実装

追加した
[ParitySafeReducedResidue.lean](/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMath/NumberTheory/Legendre/ParitySafeReducedResidue.lean:1)
を [Legendre.lean](/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMath/NumberTheory/Legendre.lean:23)
から facade import した。module docstring と公開 theorem の docstring を整備した。

主な theorem surface は次の通り。

- `coprime_two_mul_iff_coprime_and_odd`
- `mem_squareAnchorOddPointCoprimeOffsets_iff_reducedResidue`
- `card_squareAnchorOddPointCoprimeOffsets_eq_totient_two_mul`
- `activePrime_reducedResidue_packet`
- `paritySafeActiveWaveOffsets_quotient_properties`
- `paritySafeReducedQuotientInterval`
- `paritySafeActiveWaveOffsets_quotient_mem_interval`
- `paritySafeReducedQuotientInterval_mem_wave`
- `card_paritySafeActiveWaveOffsets_eq_reducedQuotientInterval`
- `paritySafeActiveWave_same_wave_quotient_rigidity`
- `paritySafeIncidenceCount_eq_reducedQuotientInterval_sum`
- `exists_activePrime_reducedQuotient_factorization_of_fullyCovered`

## Exact identities

### Candidate normalization

```text
r ∈ squareAnchorOddPointCoprimeOffsets n
  ↔ SquareOffset n r ∧ Nat.Coprime (2*n) (n^2+r)
```

`0 < n` のもとで、候補集合の cardinality は次で閉じる。

```text
(squareAnchorOddPointCoprimeOffsets n).card = Nat.totient (2*n)
```

証明は `n^2 + 1` から長さ `2*n` の `Finset.Ico` への translation と
`Nat.filter_coprime_Ico_eq_totient` による有限 bijection であり、解析的密度は
使っていない。

### Quotient interval

定義した interval は

```text
Ioc ((n^2)/q) ((n^2+2*n)/q)
```

を `Nat.Coprime (2*n) k` で filter したもの。`Nat.div` の endpoint は theorem
`mem_paritySafeReducedQuotientInterval_iff` で次の積条件に exact に戻している。

```text
n^2 < q*k ∧ q*k ≤ n^2+2*n ∧ Nat.Coprime (2*n) k
```

active `q` ごとに support quotient と `q*k - n^2` の inverse による bijection が
成立し、

```text
(paritySafeActiveWaveOffsets n q).card
  = (paritySafeReducedQuotientInterval n q).card
```

を得た。

### Same-wave rigidity

同一 active wave の `r < s` に対し、quotient difference は arbitrary collision
ではなく、次を満たす。

```text
q ∣ (s-r)
2*q ∣ (s-r)
2 ≤ k_s-k_r
Even (k_s-k_r)
q*(k_s-k_r) = s-r
```

候補 filter により中間の raw hits が抜ける可能性があるため、隣接差を常に
`2*q` とする主張はしていない。

## Full-cover frontier

`SquareOffsetsFullyCovered n` のもとでは、各 parity-safe candidate に対し、
active prime `q` と reduced-residue quotient `k` が存在して

```text
q*k = n^2+r
q ≤ n < k
Nat.Coprime (2*n) q
Nat.Coprime (2*n) k
```

を得る。これは有限 factorization frontier であり、矛盾・素数供給・Legendre
予想の証明ではない。

## Stronger-beam judgment

1. parity-safe candidate membership は reduced residues modulo `2*n` に exact に
   collapse した。
2. candidate cardinality は exact に `Nat.totient (2*n)` になった。
3. 各 active `q` wave は short reduced-residue quotient interval と exact に
   biject した。
4. 同一 wave の duplication は even-separated quotient progression として
   固定した。
5. それでも Legendre 予想に十分な universal cardinal inequality は得ていない。

従って今回の terminal boundary は Outcome A であり、PNT、Jacobsthal bound、
解析的 sieve、generic graph/matching、descent、RH/CFBRC は追加していない。

## 検証

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeReducedResidue
lake build DkMath.NumberTheory.Legendre
git diff --check
```

新規 Lean source の trailing whitespace と `sorry` / `admit` / `axiom` /
`native_decide` を監査済みである。full repository build、commit、push、CI は実施しない。
