# PRIM-L039 report — two-adic Möbius fold and odd-quotient correction

## 判定

**Outcome A — EXACT TWO-ADIC FOLD / NONPOSITIVE ODD-DIVISOR CORRECTION**

The L038 divisor-floor ledger has been folded through the odd-filtered
quotient interval.  The remaining correction is indexed only by odd divisors
`d ∣ n` with `d ≠ 1`; the prime-2 channel is not retained as an independent
correction term.

This is an exact finite-arithmetic checkpoint.  It is not a proof of
Legendre's conjecture and introduces no analytic estimate, PNT, Mertens bound,
Jacobsthal bound, sieve framework, RH/CFBRC statement, or general asymptotic
argument.

## 実装

追加した module は
`DkMath.NumberTheory.Legendre.ParitySafeMobiusOddCorrection` であり、
`DkMath.NumberTheory.Legendre` facade から import できる。

主な公開 API は次のとおり。

- `paritySafeOddRawQuotientInterval`

  L037 の `Ioc A B` を `Odd` で filter した raw quotient interval。

- `paritySafeOddRawQuotientInterval_card_eq`

  `raw.card = ((B + 1) / 2) - ((A + 1) / 2)` の exact cardinality。

- `paritySafeReducedQuotientInterval_subset_oddRaw`

  `Coprime (2*n) k` から `Coprime n k ∧ Odd k` を取り出し、reduced
  quotient interval が raw odd interval に含まれることを示す。

- `paritySafeOddMultipleFloorDelta`

  odd multiples of `d` in `(A,B]` の exact floor difference
  `(B/d - A/d) - (B/(2*d) - A/(2*d))`。

- `paritySafeActiveWave_card_eq_oddRaw_add_correction`

  active waveについて、L038 の `2*n` Möbius ledger と同じ reduced-residue
  cardinalityへ接続したうえで、

  ```text
  wave.card = rawOdd.card + paritySafeOddMobiusCorrection n q
  ```

  を `ℤ` で exact に証明する。odd-filtered interval上の Möbius
  inclusion-exclusion と、L038 の reduced cardinality ledger の両方を
  同じ cardinalityへ結び付けているため、L038との関係は定義上の省略ではない。

- `paritySafeOddMobiusCorrection_nonpos`

  correction `≤ 0`。証明は Möbius sumの絶対値評価ではなく、reduced
  intervalの raw odd intervalへの有限集合包含と cardinality差による。

- `paritySafeOddMobiusCorrection_neg_of_exists_not_coprime`

  raw odd intervalに `¬ Nat.Coprime n k` なる要素が存在すれば correction
  は strictに負になる、という十分条件を証明する。

- `paritySafeOddCorrection_six_five_witness`

  `(n,q)=(6,5)` について、`q` の active性、raw cardinality `1`、reduced
  cardinality `0`、correction `-1` を同時に検証する。

- `paritySafeIncidenceCount_le_oddRaw_sum`

  global incidence countを active waveごとの raw odd cardinalityの有限和で
  上から押さえる。

## 数学的な意味

odd `d` の channel は、`d` の倍数から `2*d` の倍数を差し引くことで
exactに odd multiplesだけを残す。したがって、`d` と `2*d` の二つの
channelは `paritySafeOddMultipleFloorDelta` に折り畳まれる。

その結果、wave occupancy の `d = 1` 項は raw odd quotient countになり、
残りは `n` の odd proper divisorによる anchor-side exclusionになる。
これは「prime 2 が correctionに残らない」ことを意味するが、correctionが
一様に十分小さいことまでは意味しない。

`(6,5)` の witnessでは `A=7`, `B=9` なので raw odd intervalは `{9}`。
しかし `Nat.Coprime 6 9` が失敗するため reduced intervalは空集合となり、
correctionは `-1` になる。従って correctionは恒等的に0ではなく、その符号
と意味が有限集合差として確認できる。

## stronger-beam judgment

1. `2*n` ledgerは odd-filter Möbius ledgerへ exactに接続し、odd divisor
   channels of `n`へ foldできた。
2. 残る signed correctionには独立した prime-2 divisor channelはない。
3. correctionは active `q` ごとに universally nonpositive。
4. strict negativityについては、raw odd interval内の anchor非互いに素要素
   からの十分条件を実装した。今回の bounded APIでは iff 形式までは要求せず、
   witnessを含む material な一方向定理として固定した。
5. raw odd-wave upper boundは L035/L036 の既存 frontierを形式的に改善するが、
   そこから universal cardinal inequalityやLegendre予想へ進む新しい estimate
   はまだない。従ってこの checkpointは exact structural foldであり、最終証明
   providerではない。

## 検証範囲

Lean 4.32.2 / Mathlib checkoutで次を検証する。

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeMobiusOddCorrection
lake build DkMath.NumberTheory.Legendre
git diff --check
```

full repository build、commit、push、CIは bounded instruction の範囲外である。
また、新規ソースについて `sorry`、`admit`、`axiom`、`native_decide` を導入
していないことを別途監査する。
