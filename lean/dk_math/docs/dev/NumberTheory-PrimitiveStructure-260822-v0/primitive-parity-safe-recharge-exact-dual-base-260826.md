# PRIM-L054 実装報告

## Outcome

Outcome A+（EXACT RECHARGE DUAL-BASE / REVERSE RECONSTRUCTION）と判定する。

L053 の prime-admissible dual-base universe に、`b = p*q` となる ordered
active-prime pair と、`t` の canonical-minimum roughness を追加した。その結果、
実際の surviving recharge image と、有限個の exact witness を持つ pair universe
が一致することを Lean で固定した。

## Exact witness と Finset

追加した witness predicate は次である。

```lean
ParitySafeRechargeExactPairWitness n b t p q
```

これは以下を同時に要求する。

- `p` は triple-gate prime、`q` は square-anchor odd active prime
- `p < q` かつ `p * q = b`
- `q` は L053 の odd-shell selector より小さい
- `p` より小さい active prime は `t` を割らない

この witness を用いて

```lean
paritySafeRechargeExactDualBasePairs n
```

を L053 の prime-admissible Finset の filter として定義した。従って、exact
universe は L053 の有限 universe の subset であり、一般の semiprime API は導入
していない。

## 実像から exact witness へ

実際の recharge key `(p,q,s)` について、L053 の selector theorem により
`s = paritySafeRechargeOddShellQuotient n b t` を得る。key の dual coordinate
から `p*q=b` と roughness を読み戻し、actual recharge image が exact Finset に
入ることを証明した。

## Exact witness から recharge へ

逆向きには、exact pair `(b,t)` の witness `(p,q)` と selector `s` から
`(p,q,s)` を再構成する。L053 の shell lower/upper bounds と
`Nat.div_add_mod` による局所的な quotient recovery により、

```lean
paritySafeFarProductWaveNextQuotient n (p, (q, s)) = t
```

を得る。さらに over-anchor base、far shell、roughness、`1 < t` を確認して、
再構成 key が surviving recharge key であり、その dual coordinate が `(b,t)`
であることを示した。

## Exact equality と card theorem

次を公開した。

```lean
paritySafeRechargeDualBaseImage_eq_exactDualBasePairs
paritySafeRechargeSurvivingFarProductKeys_card_eq_exactDualBasePairs
paritySafeCanonicalFarResidual_card_eq_terminal_add_exactDualBase
```

従って、L052 の terminal/recharge split の recharge 部分を、実際の image と
同じ card を持つ exact finite pair universe で表現できる。

## Arithmetic boundary witness

`n = 8`, `b = 5`, `t = 3` では odd-shell selector は `5` だが、
`p*q=5` を満たす prime pairは存在しないことを証明した。この witness により、
selector の active/odd 性だけでは exact recharge pair を保証できず、ordered
prime factorization witness が必要であることを固定した。

## 非目標

以下は今回の範囲外として維持した。

- generic semiprime API、exact closed cardinality、`base.card ^ 2` の coarse bound
- prime counting、sieve、asymptotics、terminal 側の counting
- smaller anchor、descent、induction、global contradiction
- `t` の primality/squarefreeness、gcd/order/divisibility の追加主張
- Legendre conjecture、RH の proof claim

## Docstring と validation

module docstring と public definition/theorem docstring に、exact witness の意味、
reverse reconstruction の scope、L053 との refinement boundary を記載した。

実行した確認は次の通り。

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeRechargeExactDualBase
lake build DkMath.NumberTheory.Legendre
git diff --check
```

新規 source について `sorry`、`admit`、`axiom`、`native_decide` を監査した。
commit、push、CI は今回の依頼範囲外なので実施していない。
