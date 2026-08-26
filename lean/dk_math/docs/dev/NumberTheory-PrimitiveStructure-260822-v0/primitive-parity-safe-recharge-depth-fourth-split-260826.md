# PRIM-L055 実装報告

## Outcome

Outcome A+（EXACT DEPTH / CANONICAL FOURTH DIRECTION）と判定する。

L054 の exact recharge dual-base universe を、selected-prime depth と、その補集合
である canonical fourth direction に有限 partition した。さらに、第四方向を
`u := Nat.minFac t` と canonicalize し、same-anchor half-scale active prime、
`p < u`、`u ≠ q,s`、quadruple product divisibility まで証明した。

## Exact cofactor packet

次を追加した。

```lean
paritySafeRechargeExactDualBasePair_cofactor_packet
```

L054 exact pair の prime-admissible shell/far 条件と over-anchor packet から、

```text
1 < t
2 * t < n + 2
```

を得る。後者は

```text
(2*n)*t < (b*s)*t = (b*t)*s ≤ n*(n+2)
```

を `n` の正性のもとで cancel する座標算術で閉じている。

## Depth / fourth Finset partition

以下を定義した。

```lean
ParitySafeRechargeSelectedDepth
paritySafeRechargeExactDepthDualBasePairs
paritySafeRechargeExactFourthDirectionPairs
```

depth は `p ∣ t ∨ q ∣ t ∨ s ∣ t`、fourth はその existential witness の
補集合とした。このため witness uniqueness や global fourth-coordinate
injectivityを仮定せずに、次を証明できる。

```lean
paritySafeRechargeExactDepthFourth_disjoint
paritySafeRechargeExactDepthFourth_union
paritySafeRechargeExactDualBasePairs_card_eq_depth_add_fourth
```

L054 の terminal split と合成して、

```lean
paritySafeCanonicalFarResidual_card_eq_terminal_add_depth_add_fourth
```

も追加した。

## Selected-depth square packet

shell point を

```lean
paritySafeRechargeExactShellPoint n b t
```

として定義し、depth branch では selected prime のいずれかの square が
shell point を割ることを証明した。

```lean
paritySafeRechargeExactDepth_selected_square_dvd_shellPoint
```

これは `b = p*q` と、選択された divisor of `t` の有限積算だけを使う。

## Canonical fourth prime packet

第四方向の prime は

```lean
paritySafeRechargeExactFourthPrime t := Nat.minFac t
```

とした。`Nat.minFac_prime` と `Nat.minFac_dvd`、L055 cofactor packet、
`Coprime (2*n) t` から、次を得る。

```lean
paritySafeRechargeExactFourthPrime_packet
```

packet の内容は以下である。

- `u` は prime かつ `u ∣ t`
- `u` は same-anchor `paritySafeHalfScaleActivePrimes n` に戻る
- roughness と prime-divisor active return により `p ≤ u`
- fourth complement と `u ∣ t` により `p < u`
- `u ≠ q` および `u ≠ s`
- `p*q*s*u ∣ paritySafeRechargeExactShellPoint n b t`

prime divisor が active に戻る部分は、`Coprime (2*n) t`、`t ≤ n`、`u ≠ 2`
から座標内で再構成した。`u` を unique な recharge coordinate として扱う
主張は追加していない。

## L044 との関係と false beam

L044 の `∃ u` fourth branch を、L055 では `u = minFac(t)` と canonicalize
した。ただし canonicalization は global injection を与えない。

```text
(3,5,37), t=7
(3,11,17), t=7
```

の二つの数値 beam は、ともに `minFac 7 = 7` であり、pair から `u` への
injectivity を主張できないことを固定する。

また `n=17, p=3, q=5, s=7, t=3` の depth beam で、
`3^2 ∣ (15*3)*7` を確認した。

## 非目標

以下は今回の範囲外として維持した。

- fourth prime `u` 単独、`(t,u)`、`(b,u)` の global injectivity
- generic 4-hypergraph、generic least-prime-factor theory
- `t` の primality/squarefreeness
- `p ∤ t` の recharge 全体への拡張
- `u<q`、`q<u`、`u<s`、`s<u` などの追加 order claim
- smaller anchor、descent、induction、analytic sieve、PNT、Mertens
- terminal branch counting、global contradiction、Legendre conjecture、RH

## Docstring と validation

module docstring、public predicate/Finset、主要 theorem に、depth/fourth の意味、
canonicalization、finite coordinate boundary、非 injective scope を記載した。

実行した確認は次の通り。

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeRechargeDepthFourthSplit
lake build DkMath.NumberTheory.Legendre
git diff --check
```

新規 source について `sorry`、`admit`、`axiom`、`native_decide` を監査した。
commit、push、CI は今回の依頼範囲外なので実施していない。
