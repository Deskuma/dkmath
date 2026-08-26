# instruction-063 — PRIM-L048 Canonical-Minimum Exclusion / Rough Cofactor Selector

## 0. 作業先

- repository: `Deskuma/dkmath`
- branch: `wip/number-theory-primitive-structure-260822-v2`
- base HEAD at review: `f9aef02bb34ea748e236e9d4d2565bfb6220b470`
- Lean / Mathlib: current checkout (`Lean 4.32.2`) を維持する。upgrade しない。

前 checkpoint `PRIM-L047` は **Outcome A — EXACT FAR PRODUCT-WAVE SELECTOR** として受理する。

L047 までで、far key

```text
key := (p,(q,s))
m := p*q*s
t := paritySafeFarProductWaveCofactor n key r
```

について、actual far residual incidence が exact に

```text
far product-wave hit
+ Nat.Coprime (2*n) t
+ p = paritySafeCanonicalSupportPrime n r
```

で選別されること、および

```text
FarResidual.card
  = ∑ key ∈ paritySafeTripleGateFarTriples n,
      (paritySafeCanonicalFarProductWaveOffsets n key).card
```

まで閉じた。

今回の目的は、最後に残っている

```text
p = paritySafeCanonicalSupportPrime n r
```

を、product-wave quotient `t` の有限な **roughness / smaller-prime exclusion** 条件へ exact に書き換えることである。

generic sieve は作らない。

---

## 1. 数学的核

far key `(p,(q,s))` は

```text
p < q < s
p,q,s ∈ squareAnchorOddActivePrimes n
```

を持つ。

product-wave hit `r` では

```text
p*q*s*t = n^2+r
```

である。

ここで任意の

```text
a ∈ squareAnchorOddActivePrimes n
a < p
```

を取る。

`a,p,q,s` は prime で `a<p<q<s` なので `a` は `p*q*s` を割れない。
従って prime divisibility と factorizationから

```text
a | n^2+r
  ↔ a | t
```

が成立する。

一方 `paritySafeActiveSupport n r` は active prime のうち `n^2+r` を割る方向そのものなので、期待される local equivalence は

```text
a ∈ paritySafeActiveSupport n r
  ↔ a | t
```

である。

したがって `p` 自身が product factorとして support に存在することを使えば、canonical minimum は

```text
p = paritySafeCanonicalSupportPrime n r
↔
∀ a ∈ squareAnchorOddActivePrimes n,
  a < p → ¬ a | t
```

へ exact に変換できる。

これが今回の主核。

この equivalence 自体には `Nat.Coprime (2*n) t` は不要なはずである。
reduced condition は parity-safe candidate を選ぶ別軸として selector に残す。

---

## 2. 新規 module

候補:

```text
DkMath.NumberTheory.Legendre.ParitySafeFarProductWaveRoughCofactor
```

ファイル:

```text
lean/dk_math/DkMath/NumberTheory/Legendre/ParitySafeFarProductWaveRoughCofactor.lean
```

import はまず

```lean
import DkMath.NumberTheory.Legendre.ParitySafeFarProductWaveSelector
```

のみ。

facade `DkMath.NumberTheory.Legendre` へ import する。

---

## 3. L048.1 smaller active direction ↔ cofactor divisor

最初に main local transport を証明する。

概念形:

```lean
theorem paritySafeFarProductWave_smallerActive_mem_support_iff_dvd_cofactor
    {n p q s r a : ℕ}
    (hkey : (p,(q,s)) ∈ paritySafeTripleGateFarTriples n)
    (hr : r ∈ squareWaveOffsets n (p*q*s))
    (ha : a ∈ squareAnchorOddActivePrimes n)
    (hap : a < p) :
    a ∈ paritySafeActiveSupport n r ↔
      a ∣ paritySafeFarProductWaveCofactor n (p,(q,s)) r := by
  ...
```

証明方針:

1. L047 cofactor packetから
   `p*q*s*t = n^2+r`。
2. `hkey` から `p,q,s` prime と `p<q<s`。
3. `ha` から `a` prime。
4. `a<p` により `a≠p,q,s`。
5. `a | p*q*s*t` を prime `dvd_mul` で分け、`a|p*q*s` branchを prime equalityで排除して `a|t`。
6. 逆向きは `a|t -> a|point` なので active-support membershipへ戻す。

`paritySafeActiveSupport` の membership 展開は既存 definition/theoremを使う。
この theorem のために generic factorization APIを追加しない。

---

## 4. L048.2 canonical minimum ↔ no smaller active divisor — 第一主定理

far key + wave hit の下で

```lean
theorem paritySafeFarProductWave_canonical_eq_iff_no_smaller_active_dvd_cofactor
    {n p q s r : ℕ}
    (hkey : (p,(q,s)) ∈ paritySafeTripleGateFarTriples n)
    (hr : r ∈ squareWaveOffsets n (p*q*s)) :
    p = paritySafeCanonicalSupportPrime n r ↔
      ∀ a ∈ squareAnchorOddActivePrimes n,
        a < p →
          ¬ a ∣ paritySafeFarProductWaveCofactor n (p,(q,s)) r := by
  ...
```

重要:

- `Nat.Coprime (2*n) t` をこの theorem の hypothesis に追加しない。
- product-wave hitだけで `p | point`、`p` active があるため `p ∈ paritySafeActiveSupport n r`、従って support nonempty は供給できるはず。
- canonical prime の定義 `min'` を使う局所 bookkeeping が必要なら、この module 内に private lemmaを一つ置いてよい。

例えば有限集合一般の

```text
p = s.min' hs
↔ p∈s ∧ ∀ a∈s, ¬ a<p
```

相当を local private theorem として切るのは可。
DkMath 全体の generic combinatorics moduleへ昇格しない。

---

## 5. L048.3 rough cofactor predicate / exact rough selector

canonical equalityを消した selector を作る。

名称候補:

```lean
noncomputable def paritySafeFarProductWaveRoughOffsets
    (n : ℕ) (key : ℕ × (ℕ × ℕ)) : Finset ℕ :=
  (squareWaveOffsets n (paritySafeTripleProductModulus key)).filter
    (fun r =>
      Nat.Coprime (2*n)
        (paritySafeFarProductWaveCofactor n key r) ∧
      ∀ a ∈ squareAnchorOddActivePrimes n,
        a < key.1 →
          ¬ a ∣ paritySafeFarProductWaveCofactor n key r)
```

membership simp theoremを置く。

far keyに対し、L048.2 を使って Finset equalityを閉じる。

```lean
theorem paritySafeFarProductWaveRoughOffsets_eq_canonicalSelector
    {n : ℕ} {key : ℕ × (ℕ × ℕ)}
    (hkey : key ∈ paritySafeTripleGateFarTriples n) :
    paritySafeFarProductWaveRoughOffsets n key =
      paritySafeCanonicalFarProductWaveOffsets n key := by
  ...
```

orientation は実装しやすい方でよい。

これにより exact selector の意味を

```text
product-wave hit
+ quotient reduced mod 2*n
+ quotient has no active prime divisor below p
```

だけへ落とす。

---

## 6. L048.4 exact rough-fiber sum

L047 の exact key-fiber sumを rough selectorへ rewriteする。

```lean
theorem paritySafeCanonicalFarResidual_card_eq_roughProductWaveSelector_sum
    (n : ℕ) :
    (paritySafeCanonicalFarResidualTripleIncidences n).card =
      ∑ key ∈ paritySafeTripleGateFarTriples n,
        (paritySafeFarProductWaveRoughOffsets n key).card := by
  ...
```

これは今回必須。

意味は、actual far residual mass が `canonicalSupportPrime` を明示参照しない finite arithmetic selector sum へ変換された、ということ。

---

## 7. L048.5 selected cofactor prime floor

roughness の直接 consumer として、selector に残る cofactor の prime divisor は canonical prime より小さくならないことを証明する。

概念形:

```lean
theorem paritySafeFarProductWaveRough_primeFactor_ge_key
    {n p q s r u : ℕ}
    (hkey : (p,(q,s)) ∈ paritySafeTripleGateFarTriples n)
    (hr : r ∈ paritySafeFarProductWaveRoughOffsets n (p,(q,s)))
    (huprime : Nat.Prime u)
    (hudvd : u ∣ paritySafeFarProductWaveCofactor n (p,(q,s)) r) :
    p ≤ u := by
  ...
```

証明は以下どちらでもよい。

- rough condition + reduced condition + L047 cofactor packetから `u` が active old primeであることを再構成し、`u<p` を排除。
- rough selector = canonical selector を使って actual far residual incidenceへ復元し、既存 L044/L045 prime-divisor return + canonical minimumを再利用。

既存 theorem再利用を優先する。

さらに数行で閉じるなら、`t>1` から prime divisorを一つ取り

```lean
theorem paritySafeFarProductWaveRough_nontrivial_cofactor_ge_key
    ...
    (ht : 1 < paritySafeFarProductWaveCofactor n (p,(q,s)) r) :
    p ≤ paritySafeFarProductWaveCofactor n (p,(q,s)) r := by
  ...
```

および L047 packet の `2*t<n+2` と合わせて

```text
1<t -> 2*p < n+2
```

を置いてよい。

この二つは strongly preferred だが、Mathlib の prime-divisor existence API探索だけが重い場合は report に残して Outcome A でもよい。

---

## 8. L048.6 far selector fibers are 0/1

L042 の

```text
paritySafeTripleGateFar_wave_card_le_one
```

と selector subsetから

```lean
theorem paritySafeFarProductWaveRoughOffsets_card_le_one
    {n : ℕ} {key : ℕ × (ℕ × ℕ)}
    (hkey : key ∈ paritySafeTripleGateFarTriples n) :
    (paritySafeFarProductWaveRoughOffsets n key).card ≤ 1 := by
  ...
```

を閉じる。

これは次 checkpoint で rough selector sumを occupied-key countへ潰す入口となる。

数行で閉じるはずなので必須。

今回 `Finset.card = if ... then 1 else 0` のような Boolean encodingまでは作らない。

---

## 9. false beam / sanity guard

roughness は

```text
no prime factor < p
```

であり、

```text
p ∤ t
p < every prime factor of t
Nat.Coprime p t
```

ではない。

実際 arithmetic witness:

```text
n = 17
r = 26
17^2 + 26 = 315 = 3*5*7*3
p = 3
q = 5
s = 7
t = 3
2*17 < 3*5*7
```

で、cofactor は canonical prime自身 `t=p=3` を含む。

最低限 arithmetic theorem として

```lean
theorem paritySafeFarProductWaveRough_depth_false_beam_17_26 :
    17 ^ 2 + 26 = 3 * 5 * 7 * 3 ∧
      2 * 17 < 3 * 5 * 7 ∧
      (17 ^ 2 + 26) / (3 * 5 * 7) = 3 := by
  norm_num
```

を置く。

typed selector membershipまで拡張する必要はない。

---

## 10. 禁止事項 / 非目標

今回は以下を行わない。

- analytic / combinatorial sieve の新設
- Buchstab / Mertens / Rosser / PNT / harmonic asymptotics
- rough-number closed form estimate
- generic least-prime-factor framework
- fourth/fifth/k-direction hypergraph
- smaller-anchor `SquareOffsetsFullyCovered`
- induction / infinite descent
- global contradiction / Legendre proof declaration
- repository-wide min/factorization refactor

---

## 11. Outcome 判定

### Outcome A+ — EXACT ROUGH-COFACTOR SELECTOR / PRIME FLOOR

最低条件:

1. smaller active direction membership `↔ a|t`。
2. canonical minimum `↔` no smaller active divisor of `t`。
3. rough selector Finset と canonical selector の exact equality。
4. actual far residual card の exact rough-fiber sum。
5. rough fiber card `≤ 1`。
6. selected cofactor prime divisor `u` に `p≤u`。
7. `1<t -> p≤t`（可能なら `2*p<n+2` まで）。
8. `(17,26)` depth false beam。

### Outcome A — EXACT ROUGH-COFACTOR SELECTOR

1〜5 と false beam が閉じ、prime-divisor floor consumerだけが API bookkeeping 上残る場合。

### Outcome B — CANONICAL EXCLUSION ONLY

1〜2 は閉じるが rough selector equality / exact sum rewrite が不自然に重い場合。

この場合は無理に Finset layerを増やさず、欠損点を report して停止する。

### Outcome C — EXCLUSION EQUIVALENCE FAILS

far product-wave hit上で smaller active support membership と cofactor divisorが一致しない具体的反例、または canonical minimumを cofactor roughnessだけで特徴付けられない反例が出た場合。

具体的 false beamを固定して停止する。

---

## 12. 検証

最低限:

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeFarProductWaveRoughCofactor
lake build DkMath.NumberTheory.Legendre
git diff --check
```

新規 sourceについて

```text
sorry
admit
axiom
native_decide
```

を監査する。

既存 repository-wide placeholder は今回の判定対象外。

---

## 13. report

候補:

```text
primitive-parity-safe-far-product-wave-rough-cofactor-selector-260826.md
```

必須記録:

- Outcome A+/A/B/C
- smaller-active support ↔ cofactor divisor theorem
- canonical minimum ↔ roughness theorem
- rough selector equality
- exact rough-fiber sum
- fiber `≤1`
- prime-factor floor / nontrivial cofactor lower boundの成否
- `(17,26)` beamの意味
- 次 checkpointへの未解決境界

---

## 14. 最終ガード

今回の到達点は

```text
actual far residual incidence
  ↔ far product-wave hit
     + reduced quotient
     + quotient avoids every active prime below p
```

である。

これは `canonicalSupportPrime` を quotient divisibility exclusionへ翻訳する有限算術 theorem であり、解析的 sieve ではない。

この exact rewrite が閉じたところで一度止まり、rough selectorを occupied-key countまたは別の既存 ledgerへどう再接続するかは次 checkpointで判断する。
