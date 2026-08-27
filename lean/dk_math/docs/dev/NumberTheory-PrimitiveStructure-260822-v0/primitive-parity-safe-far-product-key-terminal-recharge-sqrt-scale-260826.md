# PRIM-L050 実装レポート

## 判定

**Outcome A+ — TERMINAL/RECHARGE EXACT SPLIT / SQRT-SCALE FIBERIZATION**

instruction-065 の bounded scope に従い、L049 の surviving far-key world を
terminal と recharge に exact に分割し、recharge key の第一 prime を同じ
anchor `n` の sqrt-scale active-prime world へ押し下げた。

実装 module は
`DkMath.NumberTheory.Legendre.ParitySafeFarProductKeyRecharge` であり、
`DkMath.NumberTheory.Legendre` facade に import 済みである。

## 実装結果

### 1. terminal / recharge exact split

次の Finset と membership simp theorem を追加した。

- `paritySafeTerminalSurvivingFarProductKeys`
- `paritySafeRechargeSurvivingFarProductKeys`
- `mem_paritySafeTerminalSurvivingFarProductKeys`
- `mem_paritySafeRechargeSurvivingFarProductKeys`

`paritySafeTerminalRechargeSurvivingFarProductKeys_disjoint` と
`paritySafeTerminalRechargeSurvivingFarProductKeys_union` により、

```text
Terminal ∩ Recharge = ∅
Terminal ∪ Recharge = Surviving
```

を証明した。next quotient の positivity と `q = 1` または `1 < q` の
有限分割だけを使っており、新しい universe は導入していない。

### 2. exact residual-card split

`paritySafeCanonicalFarResidual_card_eq_terminal_add_recharge` により、
L049 の exact surviving-key count を用いて

```text
FarResidual.card = Terminal.card + Recharge.card
```

を閉じた。

### 3. terminal triple-product shell characterization

`paritySafeFarProductWaveNextQuotient_eq_one_iff_anchor_sq_lt_modulus` により、
far key 上で

```text
t₀ = 1 ↔ n^2 < p*q*s
```

を証明した。さらに
`mem_paritySafeTerminalSurvivingFarProductKeys_iff_product_in_shell` により、

```text
key ∈ Terminal
  ↔ key ∈ FarGate ∧ n^2 < p*q*s ∧ p*q*s ≤ n^2 + 2*n
```

を exact に得た。terminal では `Coprime (2*n) 1` と smaller-prime の
`¬ a ∣ 1` が自動的に閉じる。

### 4. sqrt-scale active-prime world

同じ anchor `n` に対して
`paritySafeSqrtScaleActivePrimes` を定義し、membership simp theorem を
整備した。

これは新しい square anchor や smaller-anchor descent ではなく、
`squareAnchorOddActivePrimes n` の有限 subworld

```text
p ∈ active primes ∧ p^2 ≤ n
```

である。

### 5. recharge first-prime sqrt gate

`paritySafeRechargeSurvivingFarProductKey_firstPrime_sq_le_anchor` を証明した。
recharge key から L049 の rough selector の next seat を復元し、L048 の
nontrivial cofactor floor と L049 の cofactor equality により `p ≤ t₀` を得た。

far gate の `p < q < s` から

```text
p^3 < p*q*s
```

を得て、`p > 0` と `p ≤ t₀` を合わせると

```text
p^4 < (p*q*s)*t₀
```

となる。survival の shell-fit と

```text
n^2 + 2*n < (n+1)^2
```

から

```text
p^4 < (n+1)^2
```

を得て、自然数の単調性により `p^2 ≤ n` を閉じた。

続けて
`paritySafeRechargeSurvivingFarProductKey_firstPrime_mem_sqrtScale` により、
第一 prime の Finset membership も公開した。

### 6. A+ first-prime fiber sum

`paritySafeRechargeFarProductKeysAtPrime` と membership theorem を追加した。
sqrt-scale 外の fiber は
`paritySafeRechargeFarProductKeysAtPrime_eq_empty_of_not_mem_sqrtScale` により
empty である。

さらに
`paritySafeRechargeSurvivingFarProductKeys_card_eq_sqrtScale_fiber_sum` により、

```text
Recharge.card
  = ∑ p ∈ SqrtScaleActivePrimes,
      (RechargeKeysAtPrime p).card
```

を exact に証明した。これは first coordinate による重複のない finite fiber
partition であり、各 `(q,s)` の capacity counting までは進めていない。

### 7. arithmetic sanity witnesses

`paritySafeFarProductKeyRecharge_sanity_witnesses` に以下を `norm_num` で固定した。

```text
n=16, key=(3,7,13): t₀=1       -- terminal
n=62, key=(3,5,37): t₀=7       -- recharge, 3^2 ≤ 62
n=17, key=(3,5,7):  t₀=3       -- recharge, 3^2 ≤ 17
```

実際の Finset membership を数値展開する witness にはしていない。

## Docstring と非目標

module docstring と公開 definition/theorem の docstring に terminal/recharge
split、terminal shell、sqrt-scale gate、first-prime fiber sum の意味を記述した。

今回の成果は同じ anchor における有限 scale compression に限定している。
`sqrt n` を新 anchor とみなすこと、smaller-anchor cover、induction、descent、
recharge key の injectivity、cofactor/prime-divisor の global injectivity、
`t₀` の primalityや squarefreeness、`p ∤ t₀`、q/s の sqrt bound、sieve、
asymptotic evaluation、global contradiction、Legendre/RH は実装していない。
既存の false beam `17^2 + 26 = 3*5*7*3` もこの境界を保つ。

## 検証

以下を実行し、いずれも Lean exit code 0 で完了した。

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeFarProductKeyRecharge
lake build DkMath.NumberTheory.Legendre
git diff --check
```

新規 source の `sorry`、`admit`、`axiom`、`native_decide` と末尾空白を監査した。
ビルド起動時の既存 `/opt/wonderful/bin/wf-env: Permission denied` は表示されたが、
Lean の対象 build は成功している。commit、push、PR、CI は行っていない。
