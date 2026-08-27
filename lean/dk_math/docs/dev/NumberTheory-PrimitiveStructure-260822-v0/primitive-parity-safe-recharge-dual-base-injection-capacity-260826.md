# PRIM-L052 実装報告

## Outcome

Outcome A（DUAL-BASE INJECTION）と判定する。

L051 の recharge surviving key
`(p, (q, s))` に対し、dual coordinate

```text
(b,t) = (p*q, paritySafeFarProductWaveNextQuotient n (p,(q,s)))
```

を導入し、次を閉じた。

1. `n < b*t`
2. 同じ `(b,t)` を持つ recharge key の third prime `s` の一意性
3. `b=p*q` から ordered prime pair `(p,q)` の復元
4. over-anchor dual-base Finset への return
5. recharge domain 上の `Set.InjOn`
6. image card と recharge card の一致
7. recharge card の over-anchor dual-base capacity bound
8. L050 exact split を用いた far residual の global capacity bound

Outcome A+ の coarse bound
`overAnchorDualBasePairs.card ≤ base.card ^ 2` は実装していない。その代わり、
指示書の arithmetic boundary witness を実装したため、Outcome A とする。

## Dual product の anchor 超過

L051 の shell packet から

```text
n^2 < (p*q*t)*s ≤ n^2 + 2*n
```

を得る。third prime `s` は active prime なので `s ≤ n` である。もし
`p*q*t ≤ n` なら `(p*q*t)*s ≤ n*n = n^2` となり、下側の shell 不等式と
矛盾する。したがって

```text
n < (p*q)*t.
```

これは新しい anchor や division theory ではなく、L051 の同一 anchor の
finite shell packet の consumer である。

## 同一 `(b,t)` における third prime の一意性

二つの recharge key が同じ `b` と `t` を持つ場合、third primes は active
odd primes である。異なるなら大小を入れ替えて `s₁ + 2 ≤ s₂` を得る。

一方、`n < b*t` なので shell width `2*n` より `2*(b*t)` の方が大きい。
従って

```text
(b*t)*s₁ + 2*(b*t) ≤ (b*t)*s₂
```

となり、`s₁` 側の shell 上端 `n^2+2*n` を越えるため矛盾する。よって
`s₁=s₂` である。

## Ordered pair の復元と injection

局所 helper `ordered_prime_pair_eq_of_mul_eq_dual_base` で、prime 性と
`p₁<q₁`, `p₂<q₂` から

```text
p₁*q₁ = p₂*q₂  →  p₁=p₂ ∧ q₁=q₂
```

を再構成した。generic factorization API には昇格していない。

最終的に同じ dual coordinate から `b` と `t` を取り出し、ordered pair と
third prime の一致を順に適用して、recharge surviving Finset 上の
`Set.InjOn` を得ている。terminal key や一般の far key は domain に含めて
いない。

## Finite capacity

追加した主な declaration は次の通り。

- `paritySafeRechargeDualBaseKey`
- `paritySafeRechargeOverAnchorDualBasePairs`
- `paritySafeRechargeDualBaseKey_mem_overAnchor`
- `paritySafeRechargeDualBaseKey_injectiveOn`
- `paritySafeRechargeDualBaseImage`
- `paritySafeRechargeDualBaseImage_subset_overAnchor`
- `paritySafeRechargeDualBaseImage_card_eq_recharge`
- `paritySafeRechargeSurvivingFarProductKeys_card_le_overAnchorDualBasePairs`
- `paritySafeCanonicalFarResidual_card_le_terminal_add_overAnchorDualBase`

したがって recharge mass は、`base(n) × base(n)` 全体ではなく、さらに
`n < b*t` で filter した finite over-anchor universe に単射される。

## Arithmetic boundary witness

実際の Finset membership は主張せず、coordinate の情報量だけを確認する
`norm_num` theorem を置いた。

```text
37^2 + 56 = 3*5*19*5
37^2 + 26 = 3*5*31*3
32^2 + 11 = 3*5*23*3
32^2 + 47 = 3*7*17*3
```

前二つは `b=15` を共有しつつ `t` が異なる例、後二つは `t=3` を共有しつつ
`b` が異なる例である。従って `b` 単独・`t` 単独では key を決めず、今回の
candidate coordinate は `(b,t)` である。

## Docstring と非目標

module docstring と public theorem docstring に、dual coordinate、same-anchor
capacity、recharge-only injection の境界を記載した。

以下は今回の非目標として維持した。

- terminal key の dual-base injection への混入
- `b` 単独または `t` 単独の injectivity
- `b=t`、`b≤t`、`t≤b`、`gcd b t = 1` の無根拠な主張
- `p ∤ t`、`q ∤ t`、`t` の prime/squarefree 性
- smaller anchor、descent、generic graph/hypergraph
- analytic sieve、PNT、Mertens、asymptotic estimate
- over-anchor universe の exact cardinal evaluation
- global contradiction、Legendre conjecture、RH の proof claim

## Validation

実行した確認は次の通り。

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeRechargeDualBaseCapacity
lake build DkMath.NumberTheory.Legendre
git diff --check
```

新規 source について `sorry`、`admit`、`axiom`、`native_decide` を監査する。
commit、push、CI は今回の依頼範囲外なので実施していない。
