# NumberGeometry-TwoPointGauge NGEO-002 実装報告

## 1. 結果

Outcome A。相対 unit gauge と natural counting shell の最小 arithmetic layer を実装し、Lean で検証した。主 API は denominator-free な `OnNatShell` を primitive とし、`normalizedMass` は active kernel 上の二次的な quotient view とした。

NGEO-003 の similarity transport、radical landing、prime scale、UnitCycle、logarithm、phase、FLT は実装していない。

## 2. 変更ファイル

- `DkMath/NumberGeometry/Gauge.lean`
  - NGEO-002 の gauge、shell、normalized mass、successor law、距離解釈を追加。
- `DkMath/NumberGeometry.lean`
  - `DkMath.NumberGeometry.Gauge` を公開 facade から import。
- `DkMathTest/NumberGeometry/GaugeAxiomAudit.lean`
  - 新規公開宣言の `#check` と主要定理の `#print axioms` を追加。
- `docs/dev/NumberGeometry-TwoPointGauge-260924-v0/report-002.md`
  - 本報告。

`Basic.lean` は NGEO-002 のためには変更していない。既存の `pairMass`、零判定、正値性 API だけを利用した。

## 3. Gauge と shell API

`distanceGauge` は追加していない。基礎距離は Mathlib の `dist` が所有しており、単なる alias を増やさず、arithmetic unit として有用な `massGauge` のみを導入した。`massGauge` は relative square-mass unit であり、基底距離を数値 1 と仮定しない。

```lean
def massGauge (K : TwoPointKernel) : ℝ :=
  pairMass K.source K.target

def OnNatShell (K : TwoPointKernel) (n : ℕ) (P : Point) : Prop :=
  pairMass K.source P = (n : ℝ) * massGauge K
```

主要な shell 定理は次のとおり。

- `onNatShell_zero_source`
- `onNatShell_one_target`
- `onNatShell_iff`
- `onNatShell_zero_iff`

shell 1 の target は存在することだけを述べ、target が shell 1 の唯一の点だとは主張していない。

## 4. Active と gauge の橋渡し

- `massGauge_eq_zero_iff`
- `massGauge_pos_iff_active`
- `massGauge_ne_zero_of_active`

これにより、退化 kernel でも `massGauge` と `OnNatShell` は定義可能なまま保持し、分母を使う定理だけが `K.Active` を仮定する構造にした。

## 5. Normalized mass

```lean
def normalizedMass (K : TwoPointKernel) (P : Point) : ℝ :=
  pairMass K.source P / massGauge K
```

次の両方向を実装した。

- `normalizedMass_eq_nat_of_onNatShell`
- `onNatShell_of_normalizedMass_eq_nat`

いずれも `K.Active` を仮定し、`massGauge_ne_zero_of_active` によって除法を正当化している。`OnNatShell` 自体は quotient を primitive にしていない。

## 6. Successor mass law

`pairMass_eq_add_massGauge_of_onNatShell_succ` を実装した。これは既に shell `n + 1` にある点の mass が

```text
n * massGauge K + massGauge K
```

となることだけを述べる。successor point の構成や `Point → Point` の `succ` map は導入していない。

## 7. Squared-distance interpretation

`dist_sq_eq_nat_mul_dist_sq_of_onNatShell` を実装した。

```text
dist K.source P ^ 2
  = (n : ℝ) * dist K.source K.target ^ 2
```

平方根の存在・符号を扱う `sqrt n` 形式と、全ての自然数 shell の inhabitance theorem は今回の範囲では意図的に deferred とした。

## 8. 検証

以下はすべて成功した。

```text
lake build DkMath.NumberGeometry.Gauge
Build completed successfully (2423 jobs)

lake build DkMath.NumberGeometry
Build completed successfully (2424 jobs)

lake build DkMathTest.NumberGeometry.GaugeAxiomAudit
Build completed successfully (2425 jobs)

lake build DkMath
Build completed successfully (10276 jobs)
```

新規 substantive theorem の `#print axioms` はすべて次の既存 logical infrastructure のみだった。

```text
[propext, Classical.choice, Quot.sound]
```

`sorry`、`admit`、`sorryAx`、`unsafe`、新規 `axiom` は使用していない。production/test/report の新規ファイルを含めた空白検査も成功した。

## 9. NGEO-003 の提案スコープ

次 checkpoint では `Point` 上の translation、orthogonal/reflection action、real scaling を既存の Mathlib API に接続し、まず square-mass transport

```text
pairMass (T A) (T P) = c ^ 2 * pairMass A P
```

を段階的に証明する。その後、active kernel の normalized mass が similarity で不変になる quotient theorem を追加する。NGEO-002 の shell API と NumberTheory 系 dependency は変更しない。

ここで NGEO-002 を終了し、prime scale・UnitCycle・radical・FLT には進まない。
