# NumberGeometry-TwoPointGauge NGEO-007 実装報告

## 1. 結果

Outcome A。二つの `TwoPointKernel` の relative square-mass gauge を結ぶ
denominator-free な `MassScalesBy` relation と、その乗法的 composition、ratio
view、similarity transport、retarget/shell bridge を実装した。

NGEO-007 は generic continuous gauge layer に限定している。prime scale、
Units、UnitCycle、logarithmic coordinates、DHNT、FLT は追加していない。

## 2. 変更ファイル

追加:

- `DkMath/NumberGeometry/GaugeTransition.lean`
- `DkMathTest/NumberGeometry/GaugeTransitionAxiomAudit.lean`
- `docs/dev/NumberGeometry-TwoPointGauge-260924-v0/report-007.md`

変更:

- `DkMath/NumberGeometry.lean`
  - `DkMath.NumberGeometry.GaugeTransition` を public facade へ追加。

NGEO-002/003 の既存 `Gauge`、`Transport`、`LevelSet`、および NGEO-006 の
concrete calibration files は変更していない。

## 3. MassScalesBy

定義は denominator-free に固定した。

```lean
def MassScalesBy (u : ℝ) (K1 K2 : TwoPointKernel) : Prop :=
  massGauge K2 = u * massGauge K1
```

退化 kernel に対しても意味を持つ。`massScalesBy_iff` はこの定義の直接展開を
提供する。

## 4. Identity / composition / inverse

実装した public declarations は次のとおり。

- `massScalesBy_refl`
- `MassScalesBy.trans`
- `MassScalesBy.inv`

composition は、`u` の transition の後に `v` を適用したときの factor を
`u * v` とする。この順序を docstring に明記した。

`MassScalesBy.inv` は `u ≠ 0` を仮定し、`u⁻¹` による relation-level inverse
を返す。kernel に group structure は導入していない。

## 5. Factor uniqueness / positivity

次を実装した。

```lean
MassScalesBy.factor_unique
MassScalesBy.factor_pos
MassScalesBy.factor_ne_zero
```

`factor_unique` は source kernel の activity
`K1.Active` を必要とする。`factor_pos` と `factor_ne_zero` は両方の kernel
の activity を必要とする。いずれも `massGauge_pos_iff_active` だけを使い、
座標展開は行っていない。

## 6. massGaugeRatio API

secondary quotient view として次を追加した。

```lean
def massGaugeRatio (K1 K2 : TwoPointKernel) : ℝ :=
  massGauge K2 / massGauge K1
```

source が active の場合に限り、次の bridge が成立する。

- `massGaugeRatio_eq_of_massScalesBy`
- `massScalesBy_of_massGaugeRatio_eq`
- `massScalesBy_iff_massGaugeRatio_eq`

従って quotient は primitive relation ではなく、非零 source gauge 上の二次的な
記法である。

## 7. Ratio composition

次を実装した。

```lean
massGaugeRatio_trans
```

`K1.Active` と `K2.Active` のもとで、`K3` は退化でもよく、次が checked である。

```text
massGaugeRatio K1 K3
  = massGaugeRatio K1 K2 * massGaugeRatio K2 K3
```

## 8. Distance-square interpretation

次を実装した。

```lean
massScalesBy_iff_dist_sq
```

これは既存 `pairMass_eq_dist_sq` を使い、transition relation を

```text
dist K2.source K2.target ^ 2
  = u * dist K1.source K1.target ^ 2
```

へ正確に読み替える。unsquared distance と `sqrt u` の定理は追加していない。

## 9. Similarity-to-transition

次を実装した。

```lean
massScalesBy_similarity
MassScalesBy.similarity
```

`massScalesBy_similarity` は任意の `c`（`c = 0` を含む）について、
`K.map (similarityMap t c R)` が元の kernel に対して factor `c ^ 2` の
transition であることを表す。

`MassScalesBy.similarity` は同じ affine similarity を両 kernel に適用しても
factor `u` を保持することを示す。injectivity や activity は仮定していない。

## 10. Retarget と shell-to-new-gauge

最小の target replacement として次を追加した。

```lean
TwoPointKernel.retarget
massGauge_retarget
```

`retarget` は source を固定し target だけを `P` に置き換える。

次の shell promotion theorem を実装した。

```lean
massScalesBy_retarget_of_onNatShell
```

```text
P ∈ OnNatShell K n
  -> MassScalesBy (n : ℝ) K (K.retarget P)
```

activity hypothesis は不要であり、`OnNatShell` の定義をそのまま
`MassScalesBy` へ接続している。`P` の shell 上の uniqueness や arbitrary
kernel 間の point map は主張していない。

## 11. Level-parameter scaling

補助的な scalar theorem として次を追加した。

```lean
natShell_massLevel_scale
```

`MassScalesBy u K1 K2` なら、任意の `n : ℕ` について

```text
(n : ℝ) * massGauge K2
  = u * ((n : ℝ) * massGauge K1)
```

が成立する。これは scalar parameter の式だけであり、点の incidence transport
や canonical point map は含まない。

## 12. 意図的に主張していないこと

- `MassScalesBy` から kernel 間の canonical point map が得られること。
- 退化 source で factor が一意であること。
- activity のない transition factor の positivity。
- 任意の factor が自然数、prime、irreducible であること。
- `MassScalesBy` が UnitCycle、logarithm、prime-scale chain の定理であること。
- shell 上の点 `P` の uniqueness、または retarget による新しい geometric
  incidence。

## 13. 検証

成功した build:

```text
lake build DkMath.NumberGeometry.GaugeTransition
Build completed successfully (2426 jobs)

lake build DkMath.NumberGeometry
Build completed successfully (8934 jobs)

lake build DkMathTest.NumberGeometry.GaugeTransitionAxiomAudit
Build completed successfully (8935 jobs)

lake build DkMath
Build completed successfully (10276 jobs)
```

`GaugeTransitionAxiomAudit.lean` の substantive declarations の
`#print axioms` はすべて既存 logical infrastructure の
`[propext, Classical.choice, Quot.sound]` のみである。

## 14. NGEO-008 proposed scope

NGEO-008 では、今回の real-valued transition factor に対して、`Nat.Prime` を
明示的に導入した prime-scale predicate と、その irreducibility / prime-scale
chain の bounded API を検討する。

対象は prime factor の型付け、factor uniqueness の active-source 接続、必要な
有限 chain bookkeeping に限定する。Units、UnitCycle、logarithmic geometry、
DHNT、cyclotomic theory、FLT は別 checkpoint とし、NGEO-007 の範囲へ遡って
追加しない。

NGEO-007 はここで終了する。
