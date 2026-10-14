# NumberGeometry-TwoPointGauge NGEO-005 実装報告

## 1. 結果

Outcome A。real inner-product space 上の radical square-mass decomposition と、inner product が zero の場合の orthogonal landing を実装し、二点 `pairMass` と `MassLevelSet` に接続した。

これは cross-term cancellation の algebraic theorem であり、radical coordinate の integrality、自然 shell への landing、SharedPoint の orthogonality、SilverRatio の分類、prime scale、UnitCycle、logarithm、2p phase、FLT は主張していない。

## 2. 変更ファイル

- `DkMath/NumberGeometry/Radical.lean`
  - generic norm decomposition、orthogonal landing、pair-mass specialization、conjugate theorems、level-set bridge を追加。
- `DkMath/NumberGeometry.lean`
  - `DkMath.NumberGeometry.Radical` を公開 facade から import。
- `DkMathTest/NumberGeometry/RadicalAxiomAudit.lean`
  - 新規公開 API の `#check`、`#print axioms`、sqrt(2) calibration を追加。
- `docs/dev/NumberGeometry-TwoPointGauge-260924-v0/report-005.md`
  - 本報告。

`Basic.lean`、`Gauge.lean`、`Transport.lean`、`LevelSet.lean` は今回変更していない。production Radical module は `DkMath.NumberGeometry.LevelSet` だけを import している。

## 3. Generic decomposition

次の theorem を実装した。

```lean
norm_sq_add_sqrt_smul
```

内容は次の恒等式である。

```text
‖u + √m • v‖²
  = ‖u‖² + m * ‖v‖² + 2 * √m * ⟪u,v⟫_ℝ
```

`hm : 0 ≤ m` のもとで `norm_add_sq_real`、`real_inner_smul_right`、`norm_smul`、`Real.sq_sqrt` を利用した。EuclideanSpace の座標展開は行っていない。

## 4. Orthogonal landing

```lean
norm_sq_add_sqrt_smul_of_inner_eq_zero
```

を追加した。

```text
⟪u,v⟫_ℝ = 0
  -> ‖u + √m • v‖² = ‖u‖² + m * ‖v‖²
```

custom orthogonality predicate は導入していない。

## 5. Pair-mass specialization

次を追加した。

- `pairMass_radical`
- `pairMass_radical_of_inner_eq_zero`

点 `A + u + √m • v` の source gap を `pairVec` の加法的 cancellation で `u + √m • v` に簡約し、generic norm theorem を再利用している。

## 6. Radical conjugation

推奨された差分 theorem を実装した。

```lean
pairMass_radical_conj_sub
```

```text
M(A + u + √m v) - M(A + u - √m v)
  = 4 * √m * ⟪u,v⟫_ℝ
```

さらに `hm : 0 < m` のもとで次も実装した。

```lean
pairMass_radical_conj_eq_iff_inner_eq_zero
```

明示的な conjugate pair の equal mass と orthogonality の同値であり、任意の SharedPoint configuration についての主張ではない。

## 7. MassLevelSet bridge

optional bridge として次を追加した。

```lean
mem_massLevelSet_radical_of_inner_eq_zero
```

orthogonal radical point が `‖u‖² + m * ‖v‖²` の square-mass level に属することを表す。`rho` との一致は明示的な `hrho` 仮定で与える。

## 8. sqrt(2) calibration

test 側で `EuclideanSpace.single 0 1` と `EuclideanSpace.single 1 1` を直交する unit vectors として用いた。

```lean
sqrt2_radical_calibration
```

により、既存の

```lean
DkMath.SilverRatio.Sqrt2.sqrt2_sq : sqrt2 ^ 2 = 2
```

を使用し、generic orthogonal landing theorem から次を確認した。

```text
‖e₀ + √2 • e₁‖² = 1 + 2 = 3
```

production `Radical.lean` は SilverRatio に依存していない。既存 `Sqrt2Lemmas` の利用は test/calibration file に限定した。

## 9. 意図的に主張していないこと

- radical point の square mass が常に rational/integer であること。
- すべての radical mass landing が `OnNatShell` に属すること。
- 任意の `SharedPoint` が orthogonal 条件を満たすこと。
- `sqrt m` の irrationality。
- SilverRatio/Egyptian construction の分類または再構成。
- coordinate irrationality から number-field element の非整性を導くこと。
- prime scale、UnitCycle、logarithmic gauge、2p phase、FLT の帰結。

## 10. 検証

以下はすべて成功した。

```text
lake build DkMath.NumberGeometry.Radical
Build completed successfully (2426 jobs)

lake build DkMath.NumberGeometry
Build completed successfully (2427 jobs)

lake build DkMathTest.NumberGeometry.RadicalAxiomAudit
Build completed successfully (8931 jobs)

lake build DkMath
Build completed successfully (10276 jobs)
```

新規 substantive theorem と calibration の `#print axioms` はすべて次の既存 logical infrastructure のみだった。

```text
[propext, Classical.choice, Quot.sound]
```

`sorry`、`admit`、`sorryAx`、`unsafe`、新規 `axiom` は使用していない。新規 production/test/report ファイルを含む空白検査も成功した。

## 11. NGEO-006 の提案スコープ

次 checkpoint では generic NumberGeometry API を既存 Silver/Egyptian construction の選択された calibration に適用する。

- SilverRatio geometry の relevant square-mass values を `pairMass` / `MassLevelSet` で再表現する。
- Egyptian-circle の `sqrt 3` と square-mass `3` の既存 theorem ownership を監査し、必要な箇所だけ thin bridge を追加する。
- exact Lean theorem と GeoGebra/research observation を分離して記録する。
- 既存 SilverRatio files を wholesale rewrite せず、generic theorem が証明を簡約できるかを確認する。

NGEO-006 でも新しい prime theorem、radical classification、FLT consequence は導入しない。ここで NGEO-005 を終了する。
