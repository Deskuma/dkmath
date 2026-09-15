# GTCORE-004 Prime-Row Higher-Tail Boundary

Date: 2026-09-10
Status: complete for the scoped GTCORE-004 checkpoint
Branch: `refact/DkMath-Lib-GTail-Core-260908-v0`
Source/build root: `lean/dk_math`

このメモは、`analysis-001.md` が指定する「現行 `r = 1` `mod p^2` theorem を
prime-row の interior `r` へ一般化する」checkpoint の実装記録である。
添付文書にある `p ∤ u` から `v_p(GTail)=1` を導く valuation 結論までは、今回の
受け入れ範囲に含めていない。

## 1. Candidate の扱い

文書の interior range

```text
1 ≤ r ≤ p - 2
```

を、Lean では次の仮定で表現した。

```text
1 ≤ r
r + 1 < p
```

この範囲では、`GTail_rec` の次段 `GTail p (r + 1) x u` が、prime Pascal row の
係数 `Nat.choose p (r + 1)` の divisibility により `p` で割り切れる。`p ∣ x`
と合わせて再帰 remainder が `p^2` で割り切れるため、boundary head との
`mod p^2` congruence を kernel-checked にした。

## 2. 実装したもの

### Generic prime-row theorem

既存の `DkMath/Lib/Cosmic/GTailCongruence.lean` に次の theorem を追加した。

```lean
GTail_modEq_head_mod_sq_of_prime_dvd_x
```

その statement は次である。

```lean
{p r : ℕ} (x u : ℕ)
(hp : Nat.Prime p) (hr : 1 ≤ r) (hrp : r + 1 < p)
(hpx : p ∣ x) :
GTail p r x u ≡ Nat.choose p r * u ^ (p - r) [MOD p ^ 2]
```

証明は `GTail_rec`、`GTail_modEq_eval_zero_of_dvd_x`、prime-row の
`Nat.choose` divisibility、および `p^2 ∣ x * GTail p (r+1) x u` を用いる。
`p ∤ u` や coprimality は仮定していないため、文書の congruence candidate より
弱い仮定で成立する有限 identity になっている。

### GN compatibility

既存 theorem

```lean
GN_modEq_head_mod_sq_of_prime_dvd_x
```

の公開名・statement・`hp5 : 5 ≤ p` 仮定は保持し、generic theorem の
`r = 1` corollary として実装本体を整理した。`GN_mod_p2_head` も従来どおり
利用できる。

### Regression

`DkMathTest/CosmicFormula/GTailCongruence.lean` を追加し、次を確認した。

- `p = 5, r = 2` の interior row
- `p = 5, r = 1` の generic theorem
- 旧 GN theorem による `r = 1` compatibility surface

## 3. 検証

### Focused build

次の build は成功した。

```bash
cd lean/dk_math
lake build DkMath.Lib.Cosmic.GTailCongruence \
  DkMathTest.CosmicFormula.GTailCongruence
```

最終結果は `Build completed successfully (8658 jobs).` である。

### Core / consumer replay

GTCORE-000 で記録した主要 consumer 群を含む replay も成功した。

```bash
cd lean/dk_math
lake build DkMath.Lib DkMath.Lib.Cosmic.GTailCongruence \
  DkMathTest.CosmicFormula.GTailCongruence DkMath.CosmicFormula \
  DkMath.FLT.Three DkMath.FLT.Five DkMath.ABC \
  DkMath.NumberTheory.Primitive DkMath.CFBRC \
  DkMath.NumberTheory.Goldbach DkMathTest.NumberTheory.GoldbachGNFiber
```

最終結果は `Build completed successfully (9023 jobs).` である。出力中の既存
research `sorry` / axiom diagnostics は既存依存のものとして現れたもので、今回の
GTCORE-004 source には `sorry`・axiom・deprecated declaration を追加していない。

## 4. 今回は行っていないこと

- `p ∤ u` を仮定した `v_p(GTail p r x u) = 1` の exact valuation theorem
- terminal row `r = p - 1` の linear-factor valuation theorem
- `mod p^3` 以上への一般化
- `GTail` と Goldbach overlap の同一視
- GN の global rename、deprecated 化、既存 consumer の広範な migration
- cyclotomic bridge や FLT7 re-entry

したがって、今回の checkpoint は prime-row interior の `mod p^2` boundary
congruence と、既存 GN theorem への compatibility 整理までで停止している。
文書が予告する valuation exactness は、独立した後続 checkpoint で扱う。
