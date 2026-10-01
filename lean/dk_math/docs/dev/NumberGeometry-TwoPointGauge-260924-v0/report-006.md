# NumberGeometry-TwoPointGauge NGEO-006 実装報告

## 1. 結果

Outcome A。既存の SilverRatio 平方距離計算を `NumberGeometry.Point` と
`MassLevelSet` へ移す薄い bridge と、明示した Egyptian calibration points の
厳密な square-mass 等式を実装した。

この checkpoint は calibration に限定している。GeoGebra の数値観測、Draft
文書の歴史的解釈、全構成点の incidence、Keystone N の uniqueness は定理化
していない。

## 2. 変更ファイル

追加:

- `DkMath/NumberGeometry/Bridge/SilverRatio.lean`
- `DkMath/NumberGeometry/Examples/EgyptianCircle.lean`
- `DkMathTest/NumberGeometry/CalibrationAxiomAudit.lean`
- `docs/dev/NumberGeometry-TwoPointGauge-260924-v0/report-006.md`

変更:

- `DkMath/NumberGeometry.lean`
  - 上記の SilverRatio bridge と Egyptian example を public facade へ追加。

generic NumberGeometry core は SilverRatio 依存を導入していない。

## 3. Pair-to-Euclidean conversion

bridge-local な唯一の conversion として、次を採用した。

```lean
def ofPair (p : ℝ × ℝ) : Point :=
  EuclideanSpace.single 0 p.1 + EuclideanSpace.single 1 p.2
```

coordinate order は明示的に `0 ↦ p.1`、`1 ↦ p.2` である。競合する pair
conversion は追加していない。

## 4. Squared-distance bridge

次の exact identity を証明した。

```lean
pairMass_ofPair_eq_dist_sq
```

```text
pairMass (ofPair p) (ofPair q)
  = DkMath.SilverRatio.Circle.dist_sq p q
```

展開は bridge file に閉じ込め、NumberGeometry core へ coordinate algebra を
戻していない。

## 5. SilverRatio four-point calibration

既存の

```lean
DkMath.SilverRatio.Circle.bcfg_concyclic
```

を再利用し、次を証明した。

```lean
bcfg_common_massLevel
```

これはある `O'` と `rho` に対して、`ofPair B`、`ofPair C`、`ofPair F`、
`ofPair G` が同一の `MassLevelSet O' rho` に属することを表す。既存の
coordinate algebra は再証明していない。

既存の定理が返す squared-radius witness をそのまま利用し、共通 Silver mass
の閉形式 `3 - 3 * sqrt 2 / 2` は今回計算していない。したがってその閉形式は
DEFERRED である。

## 6. Egyptian calibrations

`EgyptianCircle.lean` に、origin、直交する coordinate unit directions、
`W = (1, sqrt 2)` に対応する `egyptianW`、`R = (3, 0)` に対応する
`radiusThreePoint` を定義した。

次を証明した。

```text
pairMass origin egyptianW       = 3
pairMass origin radiusThreePoint = 9
egyptianW       ∈ MassLevelSet origin 3
radiusThreePoint ∈ MassLevelSet origin 9
```

`egyptianW` の証明は NGEO-005 の
`pairMass_radical_of_inner_eq_zero` を、coordinate directions の直交性と
既存 `DkMath.SilverRatio.Sqrt2.sqrt2_sq` とともに再利用している。これは
unsquared distance が `sqrt 3` であることを主張するものではない。

## 7. Keystone N

資料の明示座標

```text
N = (2 - sqrt 2 / 2, 2 + sqrt 2 / 2)
```

に対応する `keyN` を定義し、次を exact calibration として証明した。

```text
pairMass origin keyN = 9
```

`x + y = 4` と uniqueness は実装していない。

## 8. Theorem-status table

| Status | Claim |
|---|---|
| LEAN-CONFIRMED | 既存 `Circle.bcfg_concyclic` は `B,C,F,G` の平方距離共円性を証明済みである。 |
| EXACT-CALIBRATION | `pairMass_ofPair_eq_dist_sq` と `bcfg_common_massLevel` は既存 SilverRatio source を NumberGeometry mass language へ接続する。 |
| EXACT-CALIBRATION | `egyptianW` の mass `3`、`radiusThreePoint` の mass `9`、対応する `MassLevelSet` membership は Lean で checked である。 |
| EXACT-CALIBRATION | 明示座標 `keyN` の origin-centered mass `9` は Lean で checked である。 |
| RESEARCH-OBSERVATION | GeoGebra の作図が mass-3 point、mass-9 point、または `keyN` と同一であるという動機付けは、production theorem として同定していない。 |
| RESEARCH-OBSERVATION | BookOfMagic の Draft に記載された古代作図の再構成は、数学的 calibration の証拠としては扱っていない。 |
| DEFERRED | Silver common mass の閉形式、`keyN` の直線条件、鏡像排除、uniqueness、および未証明の作図 incidence。 |

## 9. 意図的に主張していないこと

- GeoGebra の全オブジェクトが定義した exact point と一致すること。
- radius-3 circle の全 incidence、八角形構成、または古代 Egyptian construction
  method。
- Keystone N の uniqueness、`x + y = 4`、`x < y` による選択定理。
- `sqrt 3` の unsquared distance theorem。
- SilverRatio の一般分類、全円構造の再構成、または NGEO-007 の gauge-transition
  composition。

## 10. 検証

成功した focused build:

```text
lake build DkMath.NumberGeometry.Bridge.SilverRatio
Build completed successfully (8931 jobs)

lake build DkMath.NumberGeometry.Examples.EgyptianCircle
Build completed successfully (8930 jobs)

lake build DkMath.NumberGeometry
Build completed successfully (8933 jobs)

lake build DkMathTest.NumberGeometry.CalibrationAxiomAudit
Build completed successfully (8934 jobs)
```

`CalibrationAxiomAudit.lean` の新規 substantive declarations の
`#print axioms` は、既存 logical infrastructure の
`[propext, Classical.choice, Quot.sound]` のみである。

追加で次も成功した。

```text
lake build DkMath
Build completed successfully (10276 jobs)

git diff --check
no diagnostics
```

tracked 変更と新規 untracked file の `git diff --no-index --check` は、いずれも
空白エラーを出力しなかった。変更・追加ファイルの禁止 shortcut scan も該当なし
だった。

## 11. NGEO-007 proposed scope

NGEO-007 では、今回公開した mass-level calibration を入力として、非零 scale
の `similarityMap` による gauge-transition composition を、既存の
`Transport` / `LevelSet` API 上で formalize する。

対象は transition law、square-mass scaling、level-set transport、必要なら
composition identity の checked API に限定する。Silver/Egyptian の未証明
incidence、Keystone N uniqueness、prime/number-theoretic theory は含めない。

NGEO-006 はここで終了し、NGEO-007 の gauge-transition composition はこの
checkpoint には実装していない。
