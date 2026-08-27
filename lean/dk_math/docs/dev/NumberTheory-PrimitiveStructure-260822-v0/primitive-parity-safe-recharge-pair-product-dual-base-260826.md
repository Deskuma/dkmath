# PRIM-L051 実装報告

## Outcome

Outcome A（PAIR-PRODUCT RETURN / EXACT FIBER）と判定する。

recharge surviving key `(p, (q, s))` について、次を実装した。

- `p * q ≤ n`
- `Nat.Coprime (2 * n) (p * q)`
- `p * q ∈ paritySafeFarCofactorBaseOffsets n`
- pair-product による Finset fiber と membership simp theorem
- reduced base 外の fiber は空
- recharge card の pair-product fiber による exact 分解
- terminal/recharge split と合成した far residual の exact card 分解

さらに、next quotient `t₀` についても
`t₀ ∈ paritySafeFarCofactorBaseOffsets n` を公開した。したがって今回の
dual reduced-base return は、同じ anchor における

```text
b = p*q ∈ base(n),    t₀ ∈ base(n)
```

という有限 bookkeeping として利用できる。

ordered prime pair の uniqueness、すなわち同じ `p*q` から `(p,q)` の一致を
導く A+ 条件は実装していない。これは指示書の非目標に従い、key 全体の
injectivity も主張しない。

## `p*q ≤ n` の proof spine

L050 の recharge 条件から、next quotient `t₀` は `1 < t₀` を満たす。
rough cofactor の lower bound により `p ≤ t₀` が得られ、far gate の順序
`p < q < s` と合わせて

```text
(p*q)^2 < (p*q*s)*t₀
```

を作る。surviving key の shell fit

```text
(p*q*s)*t₀ ≤ n^2 + 2*n < (n+1)^2
```

と合成し、`n < p*q` を仮定したときの平方単調性と矛盾させて
`p*q ≤ n` を得ている。`Nat.sqrt` や新しい anchor は導入していない。

## 実装ファイルと公開 API

実装は
[`ParitySafeRechargePairProduct.lean`](../../../../DkMath/NumberTheory/Legendre/ParitySafeRechargePairProduct.lean)
に置き、公開 facade
[`Legendre.lean`](../../../../DkMath/NumberTheory/Legendre.lean)
から import した。

主な declaration は次の通り。

- `paritySafeRechargeFirstPairProduct`
- `paritySafeRechargeSurvivingFarProductKey_firstPairProduct_le_anchor`
- `paritySafeRechargeSurvivingFarProductKey_firstPairProduct_coprime_two_mul`
- `paritySafeRechargeSurvivingFarProductKey_firstPairProduct_mem_farCofactorBase`
- `paritySafeRechargeSurvivingFarProductKey_nextQuotient_mem_farCofactorBase`
- `paritySafeRechargeFarProductKeysAtPairProduct`
- `mem_paritySafeRechargeFarProductKeysAtPairProduct`
- `paritySafeRechargeFarProductKeysAtPairProduct_eq_empty_of_not_mem_base`
- `paritySafeRechargeSurvivingFarProductKeys_card_eq_pairProductBase_fiber_sum`
- `paritySafeCanonicalFarResidual_card_eq_terminal_add_pairProductFibers`

module docstring と public theorem docstring には、same-anchor return、fiber
分解、injectivity/descent/RH 非該当の境界を記載した。

## Arithmetic witness

指示書の数値 beam に対応して、次を `norm_num` で確認する theorem を置いた。

```text
3*5 ≤ 17,    3*5 ≤ 62,    3*7 > 16.
```

最後の不等式は terminal false beam であり、`p*q ≤ n` を全 far key に
拡張していないことを明示する。

## 非目標

今回の実装は、pair-product から key 全体の injectivity、`b` と `t₀` の
大小関係、`t₀` の primality/squarefreeness、smaller-anchor cover、descent、
sieve/PNT/asymptotic estimate、global contradiction、Legendre/RH の証明を
含まない。

## Validation

実行した確認は次の通り。

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeRechargePairProduct
lake build DkMath.NumberTheory.Legendre
git diff --check
```

既存の shell 起動時に `/opt/wonderful/bin/wf-env: Permission denied` が表示されるが、Lean target の exit code は 0 である。commit、push、CI は今回の依頼範囲外なので実施していない。
