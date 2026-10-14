# NumberGeometry-TwoPointGauge NGEO-009 実装報告

## 1. 結果

Outcome A。active な NumberGeometry kernel の square-mass gauge を、既存の
`DkMath.DHNT.Unit` と exact に接続し、prime-scale chain の strict growth と
UnitCycle の deterministic no-cycle theorem まで実装した。

この checkpoint では logarithmic gauge coordinates、Units の下流理論、DHNT の
quantization、NP phase lattice、FLT/cyclotomic theory は bridge していない。

## 2. 変更ファイル

追加:

- `DkMath/NumberGeometry/Bridge/UnitCycle.lean`
- `DkMathTest/NumberGeometry/UnitCycleBridgeAxiomAudit.lean`
- `docs/dev/NumberGeometry-TwoPointGauge-260924-v0/report-009.md`

変更:

- `DkMath/UnitCycle/Core.lean`
  - generic ordered strict-invariant iterate/no-cycle theorem を追加。
- `DkMath/NumberGeometry.lean`
  - `DkMath.NumberGeometry.Bridge.UnitCycle` を public facade へ追加。

`NPUnit.lean`、`UnitNatLayers.lean`、NumberGeometry の既存 core、NGEO-008 の
PrimeScale source は変更していない。

## 3. NPUnit audit

`DkMath.NP` は integer coordinate と front/back phase bit を持つ half-lattice
モデルである。positive-real `massGauge`、`DHNT.Unit`、`PrimeScaleStep`、
`massGaugeRatio` と同一視していない。

NGEO-009 の production bridge は `DkMath.Units.NPUnit` を import していない。

## 4. DHNT.Unit / UnitNatLayers audit

`DkMath.DHNT.Unit` は `val : ℝ` と `0 < val` を持つため、active mass gauge の
exact bridge target として使用した。

一方、`DkMath.DHNT.UnitNatLayers` の floor、scaled floor、sqrt/floor bridge は
quantization devices であり、exact prime-scale map ではない。今回 import せず、
prime factor preservation も主張していない。

## 5. ActiveKernel / massUnit API

次の thin subtype を追加した。

```lean
abbrev ActiveKernel := {K : TwoPointKernel // K.Active}
```

exact positive-real unit は次である。

```lean
def massUnit (K : TwoPointKernel) (hK : K.Active) : DkMath.DHNT.Unit :=
  ⟨massGauge K, (massGauge_pos_iff_active K).2 hK⟩
```

値の一致は `Bridge.UnitCycle.massUnit_val` で checked している。
別の positive-real unit type は定義していない。

## 6. Exact DHNT ratio orientation

NumberGeometry の ratio が target/source であり、DHNT `Unit.ratio u w` が
`u.val / w.val` であることを反映し、次を実装した。

```lean
Bridge.UnitCycle.dhnt_ratio_massUnit
```

内容は次の exact identity である。

```text
Unit.ratio (massUnit K2 h2) (massUnit K1 h1)
  = massGaugeRatio K1 K2
```

factor との bridge として次も実装した。

```lean
Bridge.UnitCycle.dhnt_ratio_eq_factor_of_massScalesBy
```

DHNT の `Unit.ratio_comp` との orientation compatibility は、重複 API を作らず
次の一つの bridge theorem にまとめた。

```lean
Bridge.UnitCycle.dhnt_ratio_comp_massUnit
```

prime step については次も追加した。

```lean
PrimeScaleStep.dhnt_ratio_eq_prime
```

## 7. Closed prime-chain product

次を実装した。

```lean
PrimeScaleChain.closed_prod_eq_one
```

active kernel `K` について

```text
PrimeScaleChain K K ps
  -> ps.prod = 1
```

を示す。chain product theorem、`massScalesBy_refl`、active source の factor
uniqueness、natural cast recovery を使用している。

## 8. Strict growth

prime step の strict growth:

```lean
PrimeScaleStep.massGauge_lt
```

prime lower bound `p ≥ 2` と positive source mass gauge、および exact
`MassScalesBy` equation だけを使用する。

nonempty chain の strict growth:

```lean
PrimeScaleChain.massGauge_lt_of_nonempty
```

chain induction と `PrimeScaleStep.target_active` を使用し、prime-product
arithmetic を再証明していない。

## 9. No-nonempty-closed-chain

次を実装した。

```lean
PrimeScaleChain.eq_nil_of_closed_active
```

active source から出発して同じ kernel に戻る prime chain は空 list でなければ
ならない。nonempty chain の strict mass growth と irreflexivity から導いている。

## 10. Generic UnitCycle theorem

`UnitCycle.Core` には Nat-valued strict theorem は存在したが、real-valued
invariant に使える generic ordered theorem はなかった。そのため owner module
に最小の generic API を追加した。

```lean
DkMath.UnitCycle.invariant_lt_iterate_of_strict
DkMath.UnitCycle.no_nontrivial_cycle_of_strict_invariant
```

`[Preorder Value]` の任意の value type に対し、毎 step の strict increase から
positive iterate の strict increaseと `k = 0` の no-cycle conclusion を返す。
Real 専用にはしていない。また既存 Nat-specific theorem の名前や意味は変更して
いない。

## 11. PrimeScaleDynamics

relation と function iterate を混同しないため、選択された deterministic
dynamics を次の structure で表した。

```lean
structure PrimeScaleDynamics where
  step : ActiveKernel → ActiveKernel
  label : ActiveKernel → ℕ
  primeStep : ∀ K,
    PrimeScaleStep (label K) K.1 (step K).1
```

canonical successor kernel の存在は仮定せず、structure が選択を記録する。

strict gauge theorem:

```lean
PrimeScaleDynamics.massGauge_strict
```

を `PrimeScaleStep.massGauge_lt` から導いた。

## 12. UnitCycle no-cycle bridge

generic theorem を

```text
State = ActiveKernel
T     = D.step
I K   = massGauge K.1
```

へ instantiate し、次を実装した。

```lean
PrimeScaleDynamics.no_nontrivial_cycle
```

strictly expanding positive gauge を持つ deterministic prime-scale dynamics は、
nonzero iterate cycle を持たない。

## 13. 意図的に主張していないこと

- `PrimeScaleChain` がそのまま `Function.iterate` orbit であること。
- `MassScalesBy` が canonical next-kernel function を決めること。
- NPUnit が positive-real gauge unit であること。
- UnitNatLayers の floor bridge が exact prime factor を保存すること。
- 任意の real scale が prime であること。
- no-cycle theorem から prime distribution、cyclotomic results、FLT が得られること。
- logarithmic gauge coordinates。

## 14. 検証

成功した build:

```text
lake build DkMath.UnitCycle.Core
Build completed successfully (8924 jobs)

lake build DkMath.NumberGeometry.Bridge.UnitCycle
Build completed successfully (8932 jobs)

lake build DkMath.NumberGeometry
Build completed successfully (8938 jobs)

lake build DkMathTest.NumberGeometry.UnitCycleBridgeAxiomAudit
Build completed successfully (8939 jobs)
```

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

`UnitCycleBridgeAxiomAudit.lean` の substantive declarations の `#print axioms`
は、generic UnitCycle theorem を含め、既存 logical infrastructure の
`[propext, Classical.choice, Quot.sound]` 以下である。

## 15. NGEO-010 proposed scope

NGEO-010 では、今回の exact positive-real `massUnit` / ratio bridge を入力として
logarithmic gauge coordinates を bounded に検討する。

対象は positive-real ratio の log composition と既存 API との最小 bridge に限定し、
NP phase、UnitNatLayers quantization、prime distribution、cyclotomic theory、FLT
は含めない。

NGEO-009 はここで終了する。
