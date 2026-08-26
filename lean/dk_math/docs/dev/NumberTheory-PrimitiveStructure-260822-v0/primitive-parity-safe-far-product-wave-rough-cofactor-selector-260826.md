# PRIM-L048 実装レポート

## 判定

**Outcome A+ — Canonical-Minimum Exclusion / Rough Cofactor Selector**

instruction-063 の bounded scope に従い、L047 の exact far product-wave
selector に残っていた canonical minimum 条件を、cofactor の有限な
smaller-prime exclusion 条件へ移した。実装は次の module に収めた。

`DkMath.NumberTheory.Legendre.ParitySafeFarProductWaveRoughCofactor`

facade `DkMath.NumberTheory.Legendre` からも import している。

## 実装内容

1. `paritySafeFarProductWave_smallerActive_mem_support_iff_dvd_cofactor`

   far key と product-wave hit のもとで、`a < p` を満たす active prime
   `a` について

   ```text
   a ∈ paritySafeActiveSupport n r
     ↔ a ∣ paritySafeFarProductWaveCofactor n (p,(q,s)) r
   ```

   を証明した。`p*q*s*t = n^2+r` と prime divisibility を使う有限の
   transport であり、一般的な factorization API は追加していない。

2. `paritySafeFarProductWave_canonical_eq_iff_no_smaller_active_dvd_cofactor`

   product-wave hit だけを仮定し、`Nat.Coprime (2*n) t` は要求せず、

   ```text
   p = paritySafeCanonicalSupportPrime n r
     ↔ ∀ a ∈ squareAnchorOddActivePrimes n,
          a < p → ¬ a ∣ t
   ```

   を exact に証明した。product factor `p` が active support に入るため、
   canonical support の nonempty も同じ局所証明から供給される。

3. `paritySafeFarProductWaveRoughOffsets` と
   `mem_paritySafeFarProductWaveRoughOffsets`

   `Nat.Coprime (2*n) t` と、`p` より小さい active prime が `t` を割らない
   条件を持つ rough selector を定義し、membership simp theorem を整備した。

4. `paritySafeFarProductWaveRoughOffsets_eq_canonicalSelector`

   far key ごとに rough selector と L047 の
   `paritySafeCanonicalFarProductWaveOffsets` が等しいことを証明した。
   従って canonical minimum の消去は selector の意味を変更しない。

5. `paritySafeCanonicalFarResidual_card_eq_roughProductWaveSelector_sum`

   L047 の exact incidence-card sum を rough selector の card sum に
   書き換えた。

6. `paritySafeFarProductWaveRoughOffsets_card_le_one`

   各 far rough fiber の card が `≤ 1` であることを、L047 の既存の
   far-wave fiber bound と selector inclusion から証明した。

7. prime-factor floor

   `paritySafeFarProductWaveRough_primeFactor_ge_key` により、rough
   cofactor の任意の prime divisor `u` について `p ≤ u` を証明した。
   さらに `paritySafeFarProductWaveRough_nontrivial_cofactor_ge_key` により、
   `1 < t` なら `p ≤ t` を得た。instruction-063 で optional とされた
   `2*p < n+2` の追加主張は、今回の bounded scope には含めていない。

8. arithmetic false beam

   `paritySafeFarProductWaveRough_depth_false_beam_17_26` として

   ```text
   17^2 + 26 = 3*5*7*3,
   2*17 < 3*5*7,
   (17^2+26)/(3*5*7) = 3
   ```

   を `norm_num` で固定した。これは roughness が canonical prime 自身の
   cofactor divisibility を排除しないことを示す負例であり、roughness から
   `p ∤ t` や cofactor の coprimality を推論していない。

## Docstring と境界

新 module の公開 definition/theorem には、selector の意味、canonical
minimum の除去、fiber sum、prime-floor、false beam の役割を説明する
docstring を付した。module docstring には、今回が有限 exclusion rewrite
であり、rough-number estimate、analytic sieve、smaller-anchor descent を
導入しないことを明記した。

今回の成果は L047 selector の有限な再表現とその fiber/cardinality API
までである。analytic sieve、漸近評価、descent、Legendre 証明、矛盾閉包、
cofactor の自明な coprimality、また RH 等の主張は実装していない。

## 検証

以下を実行し、いずれも Lean exit code 0 で完了した。

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeFarProductWaveRoughCofactor
lake build DkMath.NumberTheory.Legendre
git diff --check
```

新規 source の `sorry`、`admit`、`axiom`、`native_decide` も監査対象として
確認した。commit、push、PR、CI は instruction-063 の作業範囲外のため行って
いない。
