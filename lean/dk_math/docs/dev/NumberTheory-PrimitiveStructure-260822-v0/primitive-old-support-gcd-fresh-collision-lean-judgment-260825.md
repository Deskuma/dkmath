# PRIM-L030 — Old-Support Fresh-Collision GCD Lean Judgment

日付: 2026-08-25
対象 branch: `wip/number-theory-primitive-structure-260822-v2`
環境: Lean / Mathlib v4.32.2

## 0. 作業境界

instruction-045 に従い、L029 の actual old-support capacity interface を shared-anchor
complete-point gcd の形へ圧縮した。

新規 module:

```text
DkMath/NumberTheory/Legendre/OldSupportGcd.lean
```

を追加し、`DkMath/NumberTheory/Legendre.lean` に facade import を追加した。L025--L029
の public theorem statements は変更していない。gcd framework を Legendre module 内に
限定し、analytic prime-counting、growing-family search、graph infrastructure、
Legendre conjecture の証明は行っていない。

## 1. Executive outcome

**Outcome A — EXACT FRESH-COLLISION GCD CHARACTERIZATION** と判定する。

Lean は次を証明した。

1. shared-anchor complete points の gcd は ordered offset gap を割る;
2. actual old-support disjointness は gcd の bounded old-prime support escape と同値;
3. optional に、その support escape は `primeWorldModulus` との coprimality と同値;
4. distinct shell seats では support-disjointness と
   `gcd = 1` または `gcd` が `n` より大きい単一 fresh prime、が同値;
5. L029 の `n=3`, offsets `{1,6}` は `gcd(10,15)=5` として fresh branch に入る;
6. finite family を gcd/fresh-collision predicate で表し、L029 capacity/frontier
   bridge を直接再利用できる。

これは complete-point coprimality より厳密に弱い、実用的な coordinate compression
である。ただし、growing family provider は構成していないため Legendre conjecture
は主張しない。

## 2. Implemented declarations

| 宣言 | 内容 |
| --- | --- |
| `gcd_squarePoints_dvd_orderedOffsetGap` | gcd が ordered seat gap を割ること |
| `disjoint_squareOffsetPrimeSupport_iff_gcd_supportDisjointFrom` | support disjointness と gcd support escape の同値 |
| `disjoint_squareOffsetPrimeSupport_iff_gcd_coprime_primeWorldModulus` | optional finite-world modulus form |
| `gcd_squarePoints_lt_twice_anchor` | shell gap bound による gcd 上限 |
| `disjoint_squareOffsetPrimeSupport_iff_gcd_eq_one_or_fresh_prime` | exact two-branch fresh-collision classification |
| `prime_and_fresh_of_disjoint_squareOffsetPrimeSupport_of_gcd_ne_one` | 非自明 gcd の fresh prime branch |
| `oldSupportCapacity_strictness_gcd_three_one_six` | `gcd(10,15)=5`, `Prime 5`, `3<5` |
| `PairwiseGcdFreshSeparatedSquareSeatFamily` | finite gcd/fresh-collision family predicate |
| `pairwiseGcdFreshSeparatedSquareSeatFamily_iff_oldSupportDisjoint` | gcd family と L029 family の同値 |
| `exists_prime_squareCell_of_pairwiseGcdFreshSeparatedSquareSeatFamily_card_excess` | gcd family からの L029 Frontier consumer |

module docstring と public theorem docstring に、fresh common prime が許されること、
complete coprimality への逆強化は偽であること、provider search は未実施であることを
記載した。

## 3. L030-1 — gcd and ordered gap

`r<s` に対して、

```text
n^2+s = (n^2+r) + (s-r)
```

を使い、次を証明した。

```lean
Nat.gcd (n^2+r) (n^2+s) ∣ s-r
```

平方を展開せず、gcd の各引数への divisibility と `Nat.dvd_add_iff_right` だけを
用いた ordered theorem とした。さらに `SquareOffset n r`、`SquareOffset n s`、
`r<s` から `s-r < 2*n`、従って gcd も `2*n` 未満であることを証明した。追加の
`0<n` 仮定は不要で、nonempty shell 条件から必要な自然数境界が得られる形である。

## 4. L030-2 and L030-3 — gcd support bridge

次を証明した。

```lean
Disjoint (squareOffsetPrimeSupport n r)
    (squareOffsetPrimeSupport n s) ↔
  SupportDisjointFrom (primeScalesUpTo n)
    (Nat.gcd (n^2+r) (n^2+s))
```

順方向では、gcd を割る prime が両 complete point を割ることを gcd divisibility から
取り出し、support disjointness と矛盾させた。逆方向では、両 support membership から
prime 性・`q≤n`・両 point divisibility を取り出し、`Nat.dvd_gcd` で gcd divisibility
に戻した。別の bounded-prime-free predicate は導入していない。

さらに既存の `PeriodicPrimeWorld` API を再利用して、

```lean
Nat.Coprime
  (Nat.gcd (n^2+r) (n^2+s))
  (primeWorldModulus (primeScalesUpTo n))
```

との同値も追加した。新しい primorial 定義は作っていない。

## 5. L030-4 — exact fresh-collision classification

主定理は次である。

```lean
Disjoint (squareOffsetPrimeSupport n r)
    (squareOffsetPrimeSupport n s) ↔
  gcd = 1 ∨ (Nat.Prime gcd ∧ n < gcd)
```

ここで `r<s`、両 offset の `SquareOffset` membership を仮定し、`gcd` は
`Nat.gcd (n^2+r) (n^2+s)` である。

### Forward direction

gcd が `1` でない場合、`Nat.exists_prime_and_dvd` で gcd の prime divisor `p` を
取る。support disjointness により `p≤n` は不可能なので `n<p` となる。一方、

```text
gcd ∣ s-r < 2*n < 2*p
```

である。`gcd=p*c` と書き、`p*c < 2*p` から `c<2`、gcd の正値から `c>0` を得て
`c=1`、従って `gcd=p` と結論した。これにより gcd は prime で、`n<gcd` である。

### Reverse direction

`gcd=1` なら common prime divisor は `1` を割ることになり不可能である。
`gcd` が prime かつ `n<gcd` の場合、old prime `q≤n` が gcd を割ると prime divisor
classification から `q=gcd` となるが、`n<gcd` と矛盾する。この二分法は complete
point gcd が 1 であることを要求していない。

## 6. L030-5 and L030-6 — fresh branch and L029 recovery

非自明 gcd の thin consequence:

```lean
prime_and_fresh_of_disjoint_squareOffsetPrimeSupport_of_gcd_ne_one
```

を追加した。これは「old-support disjointness を保つ二点の common factor は、単一の
fresh prime だけ」という意味を docstring に反映している。

L029 の strictness example は次で gcd 形に回収した。

```lean
Nat.gcd (3^2+1) (3^2+6) = 5
Nat.Prime 5
3 < 5
```

`10` と `15` は coprime ではないが、共通 prime `5` は old-prime threshold `3` より
大きいため、old-support capacity では衝突を消費しない。この fresh branch を削除して
complete coprimalityへ戻すことはしていない。

## 7. L030-7 and L030-8 — finite family interface

次の ordered family predicate を導入した。

```lean
PairwiseGcdFreshSeparatedSquareSeatFamily n R
```

distinct pair は `r<s` の向きだけを記録し、gcd が `1` または fresh prime であることを
要求する。次の同値を証明した。

```lean
pairwiseGcdFreshSeparatedSquareSeatFamily_iff_oldSupportDisjoint
```

したがって、gcd/fresh family から L029 の
`PairwiseOldSupportDisjointSquareSeatFamily` に変換できる。

capacity union counting と Frontier proof は再実装せず、

```lean
exists_prime_squareCell_of_pairwiseGcdFreshSeparatedSquareSeatFamily_card_excess
```

で L029 theorem を直接 composition した。これにより、将来 provider は explicit
support Finsets ではなく ordered pair の gcd/fresh condition を使って構成できる。

## 8. Stronger-beam judgment and remaining provider problem

四つの問いへの判定は次のとおりである。

1. **Yes**。support disjointness は、positive shell の distinct ordered pair では
   gcd `1` または一つの fresh prime `>n` と完全に同値になった。
2. **Yes**。family provider は bounded-prime support Finset の明示操作を避け、gcd と
   ordered seat gap の divisibility条件で記述できる。
3. **Compression only**。構成条件は扱いやすくなったが、growing family はまだ作って
   いない。
4. **Complete coprimality remains false**。`gcd(10,15)=5` が fresh branch の明示例で
   あり、support-disjoint から complete-coprime へ強化できない。

従って、今回の theorem surface は provider construction の入力を圧縮したが、provider
自体や Legendre conjecture を閉じるものではない。

## 9. Validation

次を実行し、成功を確認した。

```text
lake build DkMath.NumberTheory.Legendre.OldSupportGcd
-- Build completed successfully (8688 jobs).

lake build DkMath.NumberTheory.Legendre
-- Build completed successfully (8691 jobs).
```

`git diff --check`、trailing-whitespace audit、forbidden-placeholder audit を対象
source/report に対して実行する。Lean / Mathlib は v4.32.2 のまま変更していない。

## 10. Stop boundary

ordered gcd-gap theorem、support/gcd bridge、prime-world modulus form、exact fresh-collision
classification、L029 strictness recovery、gcd family bridge、capacity/frontier consumer
までを実装した。

ここで停止し、growing family search、analytic estimates、graph abstraction、provider
construction、Legendre conjecture、PRIM-L031 は開始しない。
