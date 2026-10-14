# NumberGeometry-TwoPointGauge NGEO-010 実装報告

## 1. 結果

Outcome A。NGEO-009 の exact positive-real `massUnit` bridge を再利用し、active
kernel の square-mass gauge とその logarithmic observer coordinate を実装した。

Multiplicative `MassScalesBy` / prime-scale relations は変更せず、log layer は
bridge として追加している。

## 2. 変更ファイル

追加:

- `DkMath/NumberGeometry/Bridge/LogGauge.lean`
- `DkMathTest/NumberGeometry/LogGaugeAxiomAudit.lean`
- `docs/dev/NumberGeometry-TwoPointGauge-260924-v0/report-010.md`

変更:

- `DkMath/NumberGeometry.lean`
  - `DkMath.NumberGeometry.Bridge.LogGauge` を public facade へ追加。

NPUnit、UnitNatLayers、NumberTheory、CosmicFormula、cyclotomic、FLT は import
していない。

## 3. logMassGauge definition and DHNT ownership

最終 definition は次のとおり。

```lean
def logMassGauge
    (K : TwoPointKernel) (hK : K.Active) : ℝ :=
  DkMath.DHNT.DUnit.logU
    (Bridge.UnitCycle.massUnit K hK)
```

positive-real unit と `Real.log` の ownership は既存の
`DkMath.DHNT.DUnit.logU` に委譲している。次の unfolding theorem を追加した。

```lean
Bridge.LogGauge.logMassGauge_eq_log_massGauge
```

```text
logMassGauge K hK = Real.log (massGauge K)
```

active kernel のみを受け付け、degenerate kernel に fallback meaning は与えて
いない。

## 4. Generic MassScalesBy log increment

次を実装した。

```lean
Bridge.LogGauge.logMassGauge_eq_add_log_factor
Bridge.LogGauge.logMassGauge_sub_eq_log_factor
```

内容はそれぞれ

```text
logMassGauge K2 h2
  = Real.log u + logMassGauge K1 h1

logMassGauge K2 h2 - logMassGauge K1 h1
  = Real.log u
```

である。`MassScalesBy.factor_pos`、active mass positivity、`Real.log_mul` を
使用し、factor positivity を余分な仮定として要求していない。

## 5. Log massGaugeRatio

次を追加した。

```lean
Bridge.LogGauge.massGaugeRatio_pos
Bridge.LogGauge.log_massGaugeRatio
```

active `K1`, `K2` に対し、ratio orientation を保ったまま

```text
Real.log (massGaugeRatio K1 K2)
  = logMassGauge K2 h2 - logMassGauge K1 h1
```

を証明している。

## 6. Additive log composition

次を実装した。

```lean
Bridge.LogGauge.log_massGaugeRatio_trans
```

```text
log (massGaugeRatio K1 K3)
  = log (massGaugeRatio K1 K2)
  + log (massGaugeRatio K2 K3)
```

既存 `massGaugeRatio_trans` と `Real.log_mul` を再利用し、no-cycle theorem は
再証明していない。

## 7. Prime-step log increment

次を実装した。

```lean
PrimeScaleStep.logMassGauge_sub_eq_log_prime
```

```text
PrimeScaleStep p K1 K2
  -> logMassGauge K2 - logMassGauge K1 = Real.log (p : ℝ)
```

generic transition theorem を利用し、prime arithmetic は再証明していない。

## 8. Prime-chain / prime-power log theorems

次を実装した。

```lean
PrimeScaleChain.logMassGauge_sub_eq_log_prod
PrimeScaleChain.logMassGauge_sub_eq_mul_log_prime
```

それぞれ `ps.prod` の log と、`List.replicate k p` に対する
`(k : ℝ) * Real.log (p : ℝ)` を与える。`List.prod_replicate`、`Nat.cast_pow`、
`Real.log_pow` を使用している。

## 9. logDistanceGauge definition

ordinary distance の observer coordinate は次である。

```lean
def logDistanceGauge
    (K : TwoPointKernel) (hK : K.Active) : ℝ :=
  Real.log (dist K.source K.target)
```

activity からの positivity helper として次を追加した。

```lean
Bridge.LogGauge.dist_pos_of_active
```

## 10. Mass-log = twice distance-log

次を実装した。

```lean
Bridge.LogGauge.logMassGauge_eq_two_mul_logDistanceGauge
```

```text
logMassGauge K hK
  = 2 * logDistanceGauge K hK
```

既存 `pairMass_eq_dist_sq` と `Real.log_pow` のみを使い、coordinate expansion は
行っていない。

## 11. Prime half-log distance increment

次を実装した。

```lean
PrimeScaleStep.logDistanceGauge_sub_eq_half_log_prime
```

```text
logDistanceGauge K2 - logDistanceGauge K1
  = (1 / 2 : ℝ) * Real.log (p : ℝ)
```

prime mass-log increment と mass-log / distance-log identity を組み合わせて
linear arithmetic で導いている。

## 12. Explicit sqrt-distance / similarity-log status

次は deferred とした。

- `dist K2.source K2.target = Real.sqrt p * dist K1.source K1.target`
- similarity に対する `2 * log |c|` の calibration

いずれも今回の required logarithmic bridge には不要であり、sqrt の非負性・
符号処理または similarity activity bookkeeping を新たに広げない判断である。

## 13. 意図的に主張していないこと

- log coordinate による `MassScalesBy`、`PrimeScaleStep`、`OnNatShell` の再定義。
- degenerate kernel の logarithmic meaning。
- log による新しい no-cycle proof。
- prime distribution、Units、UnitCycle、NP phase、UnitNatLayers quantization。
- explicit sqrt-distance identity の未証明な符号選択。
- cyclotomic theory、2p phase、FLT。

## 14. 検証

成功した focused build:

```text
lake build DkMath.NumberGeometry.Bridge.LogGauge
Build completed successfully (8933 jobs)

lake build DkMath.NumberGeometry
Build completed successfully (8939 jobs)

lake build DkMathTest.NumberGeometry.LogGaugeAxiomAudit
Build completed successfully (8940 jobs)
```

`LogGaugeAxiomAudit.lean` の substantive declarations の `#print axioms` は、
すべて既存 logical infrastructure の
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

## 15. NGEO-011 proposed scope

NGEO-011 では、log bridge の次段として primitive 2p phase または cyclotomic /
root-of-unity bridge を、既存 theorem ownership と依存方向を確認しながら bounded
に検討する。

対象は明示的な phase API と必要最小限の cyclotomic bridge に限定し、FLT、prime
distribution、未証明の global phase dynamics は含めない。

NGEO-010 はここで終了する。
