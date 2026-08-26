# PRIM-L053 実装報告

## Outcome

Outcome A+（ODD-SHELL PRIME CAPACITY）と判定する。

L052 の dual coordinate `(b,t)` に対し、shell 内の third quotient を
odd-shell selector へ縮約し、実際に active prime・shell・far 条件を満たす
pair だけからなる refined capacity universe を構成した。

## Selector

追加した selector は

```lean
paritySafeRechargeOddShellQuotient n b t
```

であり、`k := n^2/(b*t)+1` と置いて

```text
if Odd k then k else k+1
```

を返す。`b*t > 0` のもとで selector が odd であることも証明した。

## Shell quotient の二候補性

`c := b*t` と置く。`n < c` と shell 条件

```text
n^2 < c*s ≤ n^2 + 2*n
```

から、まず `n^2/c < s` を得る。`k=n^2/c+1` とすれば `k≤s` である。

さらに `Nat.div_add_mod` と `n^2 % c < c` から `n^2 < c*k` を得る。
もし `k+2≤s` なら、`2*n<2*c` と合わせて

```text
n^2 + 2*n < c*(k+2) ≤ c*s
```

となり shell 上端に反する。従って

```text
s = k ∨ s = k+1.
```

一般的な division theory は追加していない。

## Odd uniqueness と key-level equality

二候補は連続整数なので、一方だけが odd である。third prime の active
packet から `Odd s` を取り、

```lean
paritySafeRecharge_shellOddQuotient_eq_selector
```

を得た。

さらに recharge key ごとに

```lean
paritySafeRechargeSurvivingFarProductKey_thirdPrime_eq_oddShellQuotient
```

を公開し、third prime `s` を `(n,b,t)` の明示的 arithmetic function として
扱えるようにした。

## Prime-admissible capacity universe

次の Finset を追加した。

```lean
paritySafeRechargePrimeAdmissibleDualBasePairs n
```

これは L052 の `OverAnchorDualBasePairs` を、selector `s` について以下で
filter したものである。

- `s ∈ squareAnchorOddActivePrimes n`
- `n^2 < (b*t)*s`
- `(b*t)*s ≤ n^2 + 2*n`
- `2*n < b*s`

実際の recharge dual-base image がこの refined universe に入ることを示し、
次の capacity theorem を得た。

```lean
paritySafeRechargeSurvivingFarProductKeys_card_le_primeAdmissibleDualBasePairs
paritySafeCanonicalFarResidual_card_le_terminal_add_primeAdmissibleDualBase
```

また refined universe が L052 の over-anchor universe の subset であることと、
その card inequality も公開した。

## Arithmetic false beam

`OverAnchor` 条件だけでは actual recharge pair にならないことを、次の
`norm_num` witness で固定した。

```text
n = 62, b = 33, t = 3
b*t = 99 > 62
odd-shell selector = 39
62^2 < 99*39 ≤ 62^2 + 2*62
39 is composite
```

したがって selector の odd 性だけでは不十分で、prime-admissible filter が
必要である。

## Docstring と非目標

module docstring と public theorem docstring に、二候補性、odd selector、
recharge-only capacity、L052 universe との refinement 境界を記載した。

以下は今回の非目標として維持した。

- `base.card ^ 2` の coarse estimate
- prime counting、PNT、Mertens、sieve、asymptotic density
- reverse surjection や exact card equality
- `t` の primality/squarefreeness
- `gcd b t`、`b=t`、`b<t`、`t<b` の無根拠な主張
- smaller anchor、descent、induction、global contradiction
- Legendre conjecture、RH の proof claim

## Validation

実行した確認は次の通り。

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeRechargeOddShellSelector
lake build DkMath.NumberTheory.Legendre
git diff --check
```

新規 source について `sorry`、`admit`、`axiom`、`native_decide` を監査する。
commit、push、CI は今回の依頼範囲外なので実施していない。
