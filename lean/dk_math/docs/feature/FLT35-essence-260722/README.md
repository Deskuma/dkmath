# FLT3 / FLT5 共通二次本質

- Project: `dkmath`
- Branch: `feature/FLT35-essence-260722-v0`
- Date: 2026-07-22
- Status: completed
- Completion checkpoint: F35-009

## 完成要約

この feature は、FLT3 と FLT5 の proof tower を統合するのではなく、両者の
差冪 kernel が共有する二座標二次形式を中立 API として抽出した。

完成した Lean Core は次である。

```text
GN3 / S0  -> norm on TraceOneInt (-1)
GN5       -> norm on TraceOneInt 1
```

`TraceOneInt s` は中立な二座標可換環であり、共役、trace、norm、判別式、norm
の乗法性を提供する。FLT3 bridge は `s = -1`、FLT5 bridge は `s = 1` に接続する。
bridge は観測 API であり、既存の FLT3 / FLT5 proof tower を置換しない。

完成済み FLT5 production tower から、Mathlib-only full standalone artifact を
deterministically 生成し、Lean/Mathlib v4.29.0 provenance、checksum、isolated
build、public/standalone statement・trust audit を固定した。別 derivative の
v4.33.0 build と Lean4Web full standalone も外部確認済みである。Comparator Live
向け declaration-minimal bundle は、数学的証明とは別の packaging task として延期した。

## 一般共有用サマリー

一般化した対象は、奇素数指数すべての FLT ではなく、指数3と5で実際に現れる
二次 norm の座標原理である。

- 中立 API: `DkMath.NumberTheory.TraceOneQuadratic`
- FLT3 bridge: `DkMath.FLT.ThreeTraceOneBridge`
- FLT5 bridge: `DkMath.FLT.Five.TraceOneBridge`
- 公開 facade: `DkMath.FLT.QuadraticEssence`
- full FLT5 standalone certificate:
  `DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt`
- provenance / trust audit: 同じ StandAlone directory と本 feature report 群

FLT5 endpoint は DkMath-native tower で無条件に閉じる。FLT3 には Mathlib の完成
定理を使う無条件 control route と、追加仮定を受け取る DkMath-native valuation
route がある。この feature は一般 FLT、無条件 DkMath-native FLT3、FLT7、または
axiom-free proof を主張しない。

## 数学的結果

整数パラメータ `s` に対し、基底元 `τ_s` を

```text
τ_s^2 = τ_s + s
```

で還元する。二座標元 `a + b τ_s` の積は二座標内で閉じる。

```text
(a + b τ_s)(c + d τ_s)
  = (ac + sbd) + (ad + bc + bd) τ_s
```

共役、trace、norm、判別式は次である。

```text
conj(a,b) = (a+b,-b)
Tr_s(a,b) = 2a+b
N_s(a,b) = a^2 + a*b - s*b^2
Delta_s = 1 + 4*s
4*N_s(a,b) = (2*a+b)^2 - Delta_s*b^2
```

### 指数3

```text
s = -1
N_{-1}(a,b) = a^2 + a*b + b^2
Delta = -3
GN3 / S0 -> N_{-1}
```

既存の標準 Eisenstein 座標 `x^2 - xy + y^2` とは shifted bridge

```text
S0(a,b) = EisNorm(a+b,b)
```

で接続する。

### 指数5

```text
s = 1
N_1(a,b) = a^2 + a*b - b^2
Delta = 5
```

proved square coordinates

```text
m = (g+y)^2 + y^2
n = (g+y)*y
```

により

```text
GN5(g,y) = N_1(m,n)
```

へ接続する。これは FLT3 と FLT5 を同時に証明する一つの theorem ではなく、
両 kernel の共通二次本質を表す Lean-proved bridge theorem 群である。

## 完成 module map

```text
DkMath.NumberTheory.TraceOneQuadratic
  neutral two-coordinate commutative ring
  conjugation / trace / norm / discriminant
  norm multiplicativity

DkMath.FLT.ThreeTraceOneBridge
  S0_nat -> norm at s = -1
  S0_int -> norm at s = -1
  GN3 gap coordinates -> norm at s = -1
  shifted Eisenstein compatibility

DkMath.FLT.Five.TraceOneBridge
  GoldenInt coordinate map
  goldenNorm -> norm at s = 1
  GoldenNorm -> norm at s = 1
  GN5 square-link coordinates -> norm at s = 1

DkMath.FLT.QuadraticEssence
  public facade importing the two proved specializations
```

依存方向は次に固定される。

```text
TraceOneQuadratic
      ↑              ↑
FLT3 bridge       FLT5 bridge
      \              /
       QuadraticEssence
```

`NumberTheory -> FLT`、`FLT3 proof -> FLT5 proof`、`FLT5 proof -> FLT3 proof`
という逆向き・cross import は導入していない。generic `TraceOneInt s` には、一般
の `s` では偽になり得る `IsDomain` / PID / UFD / Euclidean domain を付与していない。

## 公開 theorem surface

### Neutral core

```text
traceOne_ext
traceOne_tau_sq
traceOne_conj_invol
traceOne_conj_mul
traceOne_mul_conj
traceOne_norm_mul
four_mul_traceOneNorm_eq_discriminant
traceOneNorm_neg_one
traceOneNorm_one
```

### FLT3 bridge

```text
S0_nat_eq_traceOneNorm_negOne
S0_int_eq_traceOneNorm_negOne
GN_three_sub_eq_traceOneNorm_negOne
eisensteinNorm_shift_eq_traceOneNorm_negOne
```

### FLT5 bridge

```text
goldenToTraceOne
goldenNorm_eq_traceOneNorm_one
GoldenNorm_eq_traceOneNorm_one
GN5_eq_traceOneNorm_squareLink
```

既存 endpoint は変更していない。

```text
DkMath.FLT.FLT3_core
DkMath.FLT.FLT_d3_by_padicValNat
DkMath.FLT.Five.flt5Target
DkMath.FLT.Five.fermatFive_no_positive_solution
```

## FLT3 の正確な境界

`DkMath.FLT.FLT3_core` は Mathlib の完成済み FLT3 theorem を包む無条件 control
route である。

DkMath-native valuation route の中心 theorem
`DkMath.FLT.FLT_d3_by_padicValNat` は、現在も `Nat.Coprime a b` と
`hS0_not_sq` を入力に持つ。後者は primitive prime が `S0` 上で square lift
しないことを要求する arithmetic kernel である。したがって、この native route
を無条件 FLT3 完成証明とは記述しない。

共通二次 bridge の完成は、この conditional / unconditional 境界を変更しない。

## FLT5 full standalone certificate

production module `DkMath.FLT.Five.Standalone` は、引き続き小さな Mathlib-only
GN5 seed である。full proof certificate はこの source module とは別の生成 artifact
として保存される。

| 項目 | 値 |
|---|---|
| Artifact | `DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt` |
| Pinned environment | Lean / Mathlib v4.29.0 |
| Lines | 5981 |
| Bytes | 234552 |
| SHA-256 | `400935756c2468577582e6e9b87db2e5a2194a127855e3eb9bea312ff79b8dbd` |
| Active import surface | `import Mathlib` |
| Ordered production modules | 33 |

manifest order と DkMath import closure を validator で確認し、source commit と blob
identity を header / provenance に記録した。二重生成は byte-identical、exact-byte
isolated build と checksum は PASS、production endpoint は各1回だけ含まれる。
artifact は production import graph の外にある。

証跡:

- [provenance](../../../DkMath/FLT/docs/StandAlone/FLT5%23StandAlone-v0.provenance.md)
- [isolated build log](../../../DkMath/FLT/docs/StandAlone/FLT5%23StandAlone-v0.lean.build.log)
- [v4.29 audit log](../../../DkMath/FLT/docs/StandAlone/FLT5%23StandAlone-v0.audit-v429.log)
- [F35-007 report](report-flt35-007.md)
- [F35-008A report](report-flt35-008a.md)

## Statement / trust audit

F35-008A は **Outcome A / final result PASS** で完了した。

public source と fixed standalone の次の実 declaration は、proof body を除いた
statement または定義本体の normalized hash が一致した。

```text
Fermat5Equation
FLT5Target
flt5Target
fermatFive_no_positive_solution
```

別々の Lean process による `#check` type output も一致した。両 FLT5 endpoint の
exact axiom set は次である。

```text
{propext, Classical.choice, Quot.sound}
```

したがって axiom-free とは呼ばない。監査結果は次である。

```text
sorryAx: absent
DkMath-defined axioms: absent
active native_decide: absent
active admit: absent
active sorry: absent
```

quadratic-essence theorem surface の checked declarations にも `sorryAx` と
DkMath-defined axiom はない。各 theorem の標準 Lean axiom set は
[F35-008A report](report-flt35-008a.md) に記録した。

## v4.33 / web / Comparator boundary

v4.29 provenance certificate と分離した compatibility derivative について、次を外部
確認した。

```text
standalone v4.33.0 compatibility derivative: build Success
Lean4Web full standalone: PASS
```

一方、Comparator Live に full source を入力すると現在は次となる。

```text
Unexpected error initializing verification
No output generated
```

これは数学的 proof failure ではない。実行 declaration を十分削減すると frontend
は初期化し、comment volume の増減だけでは解消しないことが観測されている。
`theorem_picker.md` を使う declaration-minimal theorem bundle は別 packaging task
として延期する。Comparator Live は完成 Essence API と fixed standalone proof
certificate の完了条件に含めない。

詳細は [v4.33 / Lean4Web milestone](note-flt5-standalone-v433-lean4web-milestone.md)
を参照。

## Checkpoint closure

| Checkpoint | Status | 成果 |
|---|---|---|
| F35-001 | complete | investigation / design / boundary fixation |
| F35-002 | complete | `TraceOneQuadratic` core |
| F35-003 | complete | FLT3 trace-one bridge |
| F35-004 | complete | FLT5 trace-one bridge |
| F35-005 | complete | facade / initial audit |
| F35-006 | complete | standalone manifest / deterministic generator |
| F35-007 | complete | fixed v4.29 provenance standalone package |
| F35-008A | complete | statement / type / trust audit, Outcome A |
| F35-008B | partial external milestone | v4.33 and Lean4Web PASS; Comparator-minimal bundle deferred |
| F35-009 | complete | documentation closure |

## Definition of Done: final result

- `TraceOneInt s` の可換環、共役、trace、norm、判別式 API: complete
- FLT3 `S0` / `GN3` と `N_{-1}` の bridge: complete
- FLT5 `GN5` / Golden norm と `N_1` の bridge: complete
- 既存 FLT3 / FLT5 endpoint preservation: complete
- Mathlib-only full FLT5 standalone generation / build / checksum: complete
- public / standalone statement・type・axiom comparison: complete
- provenance と runtime boundary: complete

最終 Lean-proved bridge result:

```text
GN3 -> N_{-1}
GN5 -> N_1
```

次の研究はこの feature の外から始まる。

```text
GN7 -> N_{-2} prediction
```

これは予測であり、本 feature では実装も theorem claim も行わない。

## 明示的非目標

- 一般奇素数 `p` の quadratic-subfield theorem
- 一般 FLT theorem
- 無条件 DkMath-native FLT3 theorem
- FLT7 theorem または p=7 smoke theorem
- generic `TraceOneInt s` の domain / PID / UFD 宣言
- axiom-free という主張
- Comparator Live full-source validation
- FLT3 / FLT5 proof tower の相互 import または大規模 refactor
