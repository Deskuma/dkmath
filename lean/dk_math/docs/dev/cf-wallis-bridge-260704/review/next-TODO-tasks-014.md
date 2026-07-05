# TODO: Cosmic Wallis Petal Bridge 改善・未整備案件

## 1. 目的

`Cosmic Wallis Petal Bridge` は、現状すでに次の 3 層で実装されている。

```text
DkMath/Pascal/WallisCosmicPetalBridge.lean
  有限代数層

DkMath/Pascal/WallisLimitBridge.lean
  π/2 極限層

DkMath/Pascal/WallisGrowthBridge.lean
  中央二項係数の成長層
```

本 TODO は、すぐ実装しない改善点・未整備案件を退避しておくためのメモである。

---

## 2. 現在の到達点

現在の橋は、Wallis 因子を宇宙式 Gap 比率として読む構造まで閉じている。

```text
Wallis 因子:
  (2k+2)^2 / ((2k+1)(2k+3))

Cosmic 読み:
  ((2k+1)(2k+3) + 1) / ((2k+1)(2k+3))

核:
  (2k+2)^2 = (2k+1)(2k+3) + 1
```

したがって Wallis 部分積は、

```text
奇数 Petal 境界に現れる Gap = 1 の累積積
```

として読める。

また、中央二項係数の漸近も Wallis route から到達している。

```text
centralRatioQ(m) ~ sqrt(pi * m)

choose(2m, m) ~ 4^m / sqrt(pi * m)
```

重要な点:

```text
この中央二項係数の漸近は、Stirling を入力として使わず、
Wallis route から導出されている。
```

---

## 3. TODO A: 公開 API 用 alias の追加

### 3.1. 背景

現在の theorem 名は実装経路を正確に表しているが、下流利用者から見ると少し長い。

既存 theorem:

```lean
isEquivalent_real_centralBinomial_four_pow_div_sqrt_pi_mul_nat
```

これは内容としては、

```text
choose(2m, m) ~ 4^m / sqrt(pi * m)
```

を表している。

### 3.2. 追加候補

`DkMath/Pascal/WallisGrowthBridge.lean` に、表示用 alias を追加する。

```lean
/--
Wallis-derived presentation alias for the central-binomial asymptotic.

This theorem is derived through the Wallis bridge route and does not use
Stirling's formula as an input.
-/
theorem isEquivalent_real_centralBinomial_via_wallis :
    (fun m : ℕ => ((Nat.choose (2 * m) m : ℕ) : ℝ)) ~[Filter.atTop]
      (fun m : ℕ => (4 : ℝ) ^ m / Real.sqrt (Real.pi * (m : ℝ))) :=
  isEquivalent_real_centralBinomial_four_pow_div_sqrt_pi_mul_nat
```

比率版 alias も追加する。

```lean
/--
Wallis-derived ratio form of the central-binomial asymptotic.

This is a presentation alias for downstream use.
-/
theorem tendsto_real_centralBinomial_ratio_via_wallis_one :
    Filter.Tendsto
      (fun m : ℕ =>
        ((Nat.choose (2 * m) m : ℕ) : ℝ) /
          ((4 : ℝ) ^ m / Real.sqrt (Real.pi * (m : ℝ))))
      Filter.atTop
      (nhds 1) :=
  tendsto_real_centralBinomial_div_four_pow_div_sqrt_pi_mul_nat_one
```

---

## 4. TODO B: ドキュメント追記

### 4.1. 対象候補

```text
docs/dev/cf-wallis-bridge-260704/cf-wallis-growth-route.md
```

または、該当 docs が未確定なら新規に次を置く。

```text
docs/dev/cf-wallis-bridge-260705/TODO.md
```

### 4.2. 追記内容

```md
## Wallis-derived central-binomial asymptotic

The central-binomial asymptotic

\[
\binom{2m}{m}\sim\frac{4^m}{\sqrt{\pi m}}
\]

is available through the Wallis bridge route.

This route should be documented as Wallis-derived, not Stirling-derived.
Stirling's formula is not used as an input for this bridge.

Useful presentation aliases:

```lean
isEquivalent_real_centralBinomial_via_wallis
tendsto_real_centralBinomial_ratio_via_wallis_one
```

```

---

## 5. TODO C: Petal との明示 bridge

### 5.1. 現状

`WallisCosmicPetalBridge.lean` は名前として Petal を含むが、実装主語は主に Pascal / Wallis / Cosmic である。

現時点では、`DkMath.Petal` の住所系・orbit・Petal address との直接接続はまだ薄い。

### 5.2. 今後の候補

薄い bridge ファイルを検討する。

```text
DkMath/Pascal/WallisPetalBridge.lean
```

または既存ファイルに追加。

```text
DkMath/Pascal/WallisCosmicPetalBridge.lean
```

候補となる概念対応:

```text
centralRatioQ:
  片側 Petal 成長

mirrorOddRatioPartialQ:
  鏡像 Petal 成長

wallisPartialQ:
  左右 Petal を合わせた閉じた偶奇境界積

cosmicPartialQ:
  Wallis 因子を Cosmic Gap 比率として読んだ積

2m+1:
  左右非対称性として残る奇数境界
```

### 5.3. 既存補題の意味づけ

以下の theorem には Petal 読みの docstring を追加してよい。

```lean
centralRatioQ_mul_mirror_eq_wallisPartialQ
centralRatioQ_mul_mirror_eq_cosmicPartialQ
wallisPartialQ_eq_cosmicPartialQ
centralRatioQ_div_mirrorOddRatioPartialQ_eq_two_mul_add_one
```

特に最後は重要。

```text
centralRatioQ / mirrorOddRatioPartialQ = 2m + 1
```

これは、

```text
左右 Petal の非対称性が、右端の奇数境界 2m+1 として残る
```

と読める。

---

## 6. TODO D: GrowthProfile への拡張

### 6.1. 目的

現在の Wallis bridge は中央線、

```text
choose(2m, m)
```

を主に扱っている。

次の拡張として、中央から \(r\) ずれた係数を扱う。

```text
choose(2m, m+r)
```

### 6.2. 新規候補ファイル

```text
DkMath/Pascal/GrowthProfile.lean
```

### 6.3. 研究対象

候補となる量:

```text
4^m / choose(2m, m+r)
```

または比率:

```text
choose(2m, m+r) / choose(2m, m)
```

これを Petal / mirror / Gap 比率として分解する。

### 6.4. 期待される意味

```text
Wallis:
  中央 Petal の閉じ

GrowthProfile:
  中央からずれた Petal の曲率

Stirling correction:
  曲率の連続極限
```

### 6.5. 注意

最初から正規分布や局所中心極限定理まで行かない。

まずは有限積・有限比率の分解だけを固定する。

---

## 7. TODO E: Infinite product まわりの注意

### 7.1. 現状

`WallisLimitBridge.lean` は、Wallis 部分積の極限として

```text
wallisPartialQ -> pi / 2
cosmicPartialQ -> pi / 2
```

を扱っている。

### 7.2. 注意点

無限積を不用意に `HasProd` や unconditional product として再定式化しない。

理由:

```text
Wallis 積は収束するが、
一般の無限積 API へ移すには log-product / summability の補助が必要。
```

したがって、現状の部分積極限 route は安全である。

### 7.3. 将来候補

将来的に無限積 API へ昇格する場合は、別ファイルで扱う。

```text
DkMath/Pascal/WallisInfiniteProduct.lean
```

検討事項:

```text
log wallis factor
summability of log correction
HasProd form
partial product route との同値
```

---

## 8. TODO F: 命名整理

### 8.1. 追加したい外向け名

候補:

```lean
isEquivalent_real_centralBinomial_via_wallis
tendsto_real_centralBinomial_ratio_via_wallis_one
centralBinomial_asymptotic_via_wallis
centralRatioQ_asymptotic_sqrt_pi_mul_nat
```

### 8.2. DkMath 内部名として残すもの

既存名は、証明経路が分かるため残す。

```lean
isEquivalent_real_centralRatioQ_sqrt_pi_mul_nat
isEquivalent_real_centralBinomial_four_pow_div_sqrt_pi_mul_nat
tendsto_real_centralBinomial_div_four_pow_div_sqrt_pi_mul_nat_one
```

方針:

```text
既存 theorem は変更しない。
短い名前は alias として追加する。
```

---

## 9. TODO G: README / index への導線追加

### 9.1. 対象

```text
DkMath/Pascal.lean
README.md
docs/dev/index.md
```

存在する導線に応じて調整する。

### 9.2. 書きたい説明

```md
### Cosmic Wallis Petal Bridge

The Wallis product is represented as a product of Cosmic gap factors:

\[
\frac{(2k+2)^2}{(2k+1)(2k+3)}
=
1+\frac{1}{(2k+1)(2k+3)}.
\]

This connects Pascal central growth, mirror odd products, Wallis' product,
and the asymptotic behavior of central binomial coefficients.

The central-binomial asymptotic is derived through this Wallis route,
without using Stirling's formula as an input.
```

---

## 10. 優先順位

### 優先度 1

```text
WallisGrowthBridge に presentation alias を追加する。
docs に「Wallis-derived / not Stirling-input」を明記する。
```

### 優先度 2

```text
Petal 読みの docstring を既存 theorem に追加する。
centralRatioQ / mirror ratio = 2m+1 の意味を記録する。
```

### 優先度 3

```text
GrowthProfile.lean の設計を開始する。
中央から r ずれた Pascal 係数を扱う。
```

### 優先度 4

```text
無限積 API への昇格を検討する。
ただし現状の partial product limit route は維持する。
```

---

## 11. Codex 向け短縮指示

```text
Task:
Add TODO-backed presentation aliases and docs for the Cosmic Wallis Petal Bridge.

Do not refactor existing proofs.

Primary file:
- DkMath/Pascal/WallisGrowthBridge.lean

Add aliases:
- isEquivalent_real_centralBinomial_via_wallis
- tendsto_real_centralBinomial_ratio_via_wallis_one

Both should be direct aliases to existing theorems.

Docstrings:
Mention that these are Wallis-derived presentation aliases and do not use
Stirling's formula as an input.

Docs:
Add or update a TODO/development note under docs/dev/cf-wallis-bridge-* explaining:
- Wallis factors as Cosmic Gap ratios
- centralRatioQ * mirror = Wallis partial product
- Wallis route gives central-binomial asymptotic
- future work: Petal bridge docstrings, GrowthProfile, infinite product API

Checks:
- lake build DkMath.Pascal.WallisGrowthBridge
- lake build DkMath.Pascal
- grep -R "sorry\\|admit" DkMath/Pascal/Wallis*.lean
```
