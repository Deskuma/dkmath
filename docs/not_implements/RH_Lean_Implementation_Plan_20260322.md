# DkMath.RH Lean 実装計画書（2026-03-22）

## 1. 現状認識

`DkMath.RH` は、最新スナップショット時点で次の骨格が既に通っている。

- 位相速度・停留・非退化停留の基礎定義
- 単一素数因子に対する `phaseVel` / `phaseCurv` 補題
- 有限 Euler 積に対する
  `stationaryAt ↔ hopcPrimeContributionSum = 0`
  および非退化版
- `hopcPrimeContributionFn` / `hopcPrimeContributionTsum` を介した finite → infinite 接続
- `CFBRC` primitive-prime witness から
  `stationaryAt` / `nondegenerateStationaryAt` / `primeLocalFormation`
  への bridge
- provider-family を受ける高位 wrapper
- `σ > 1` と `C / p^σ` 型評価から `tsum = 0` / `tendsto = 0`
  を返す wrapper

したがって、次段で狙うべきは「新しい観測量」よりも、
既存 API 群を束ねて **prime-local formation principle を定理列として固定すること** にある。

## 2. 設計方針

### 2.1. 主目標

次の 3 段を明確化する。

1. **finite formation**
   \[
   \exists p,\; hopcPrimeContributionSum(insert\;p\;S)=0
   \quad\text{and optionally}\quad
   phaseCurv \neq 0
   \]
2. **eventually finite formation**
   \[
   \forall^{\mathrm{eventually}} S,\; stationaryAt(S)
   \quad\text{or}\quad
   nondegenerateStationaryAt(S)
   \]
3. **infinite lift consequence**
   \[
   hopcPrimeContributionTsum(\sigma,t)=0,
   \qquad
   hopcPrimeContributionSum(S) \to 0
   \]

### 2.2. 実装上の原則

- `CFBRCBridge.lean` は既に巨大なので、今後の theoremization は **分割を優先** する。
- 低位補題（局所 zero / provider 構成）は既存再利用を徹底し、
  新規は **高位 wrapper / package theorem** に絞る。
- `stationary` 系と `nondegenerate` 系を並行設計し、命名を左右対称に保つ。

## 3. 推奨ファイル分割

### Phase A. 新規ファイル追加

1. `DkMath/RH/PrimeLocalFormation.lean`
   - PF1, PF2, PF2w, PF3 相当の「形成条件」定理を集約
   - `exists_primeLocalFormation_*`
   - `eventually_exists_primeLocalFormation*`

2. `DkMath/RH/PrimeLocalFormationInfinite.lean`
   - finite formation → eventually stationary / eventually nondegenerate
   - eventually stationary / nondegenerate → `tsum = 0`, `tendsto = 0`

3. `DkMath/RH/PrimeLocalFormationProviders.lean`（必要なら）
   - provider family を束ねる structure
   - theorem 引数を短くするための package 層

### Phase B. 既存ファイルの役割整理

- `EulerZetaLemmas.lean`: 判定の同値補題
- `HopcInfiniteLift.lean`: 一般的な infinite-lift 補題
- `CFBRCBridge.lean`: 低位 bridge と provider 構成器
- 新規 `PrimeLocalFormation*.lean`: 高位の主定理群

## 4. 最優先ターゲット定理

### T1. eventually nondegenerate の「insert 除去」版

現状には

- `eventually_exists_nondegenerateStationaryAt_insert_of_...`

があるが、

- `eventually_stationaryAt_of_...`

に対応する

- `eventually_nondegenerateStationaryAt_of_...`

が見当たらない。

したがって最初の追加候補は次。

```lean
theorem eventually_nondegenerateStationaryAt_of_cfbRc_primitive_prime_boundary_bridge_of_providerFamily_and_phaseCurvProviderFamily
    ... :
    ∀ᶠ S in Filter.atTop,
      DkMath.RH.nondegenerateStationaryAt
        (fun v : ℝ => eulerZetaFinite_onVertical S σ v) t
```

#### 数学内容

既存の
\[
\forall^{\mathrm{eventually}} S,\; \exists p,
  nondegenerateStationaryAt(insert\;p\;S)
\]
から、固定 witness `p` が eventually `S` に入ることを使って
\[
insert\;p\;S = S
\]
に正規化する。

#### 実装メモ

- `eventually_stationaryAt_of_...` の証明をほぼ踏襲できる。
- 差分は `stationaryAt` だけでなく `phaseCurv ≠ 0` も
  `simpa [Finset.insert_eq_of_mem hp_mem]` で押し通せるかの確認。
- もし `phaseCurv` 側の簡約が `simp` で落ちないなら、
  補助補題
  `nondegenerateStationaryAt_congr` 相当を追加する。

### T2. prime-local formation の packaged theorem

いまは

- `hopcPrimeContributionSum = 0`
- `phaseCurv ≠ 0`
- witness divisibility / gap 条件

が theorem ごとにばらけている。

これを束ねた structure を導入する。

```lean
structure PrimeLocalFormationData
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    (d x u : ℕ) (σ t : ℝ) : Prop where
  p : {q // Nat.Prime q}
  hp_dvd : p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u
  hp_gap : match side with
    | .right => ¬ p.1 ∣ x
    | .left => ¬ p.1 ∣ u
  hsum0 : hopcPrimeContributionSum (S := insert p S) σ t = 0
  hcurv0 : DkMath.RH.phaseCurv
    (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t ≠ 0
```

この structure を返す theorem を定義する。

```lean
theorem exists_primeLocalFormationData_of_cfbRc_primitive_prime_boundary_bridge_of_local_split_and_phaseCurv ...
```

#### 効能

- finite / eventually / infinite の各段で `∃ p, ...` を毎回展開せずに済む。
- 後段の theorem 名が短くなる。

### T3. eventually formation data の packaged theorem

```lean
theorem eventually_exists_primeLocalFormationData_of_... :
  ∀ᶠ S in Filter.atTop, PrimeLocalFormationData side S d x u σ t
```

### T4. provider-family から packaged theorem を作る wrapper

```lean
def primeLocalFormationProviderFamily ... := ...
```

または theorem として

```lean
theorem eventually_primeLocalFormationData_of_providerFamily_and_phaseCurvProviderFamily ...
```

#### 目的

PF1/PF2/PF2w/PF3 の theorem 群を「形成原理」として 1 本に束ねる。

## 5. 第二優先ターゲット定理

### T5. nondegenerate + infinite consequence の同時返却定理

既存には

- eventually stationary
- `hopcPrimeContributionTsum = 0`
- `tendsto ... (𝓝 0)`

が別 theorem である。

そこで、実用入口として

```lean
theorem primeLocalFormation_infiniteOutcome_of_boundaryDiffPow_factor0_with_offdvd_provider_and_providerFamily_sigma_gt_one ... :
  (∀ᶠ S in Filter.atTop,
      DkMath.RH.stationaryAt (fun v => eulerZetaFinite_onVertical S σ v) t)
  ∧ hopcPrimeContributionTsum σ t = 0
  ∧ Filter.Tendsto
      (fun S => hopcPrimeContributionSum (S := S) σ t)
      Filter.atTop (𝓝 (0 : ℝ))
```

を追加する。

#### 数学的意味

有限側形成原理と無限側帰結を、利用者が 1 本で取れるようにする。

### T6. nondegenerate 版 infinite outcome（任意）

もし `eventually_nondegenerateStationaryAt_of_...` が通ったら、
次にこれを付加情報として bundled theorem に含める。

```lean
... ∧ (∀ᶠ S in Filter.atTop,
      DkMath.RH.nondegenerateStationaryAt
        (fun v => eulerZetaFinite_onVertical S σ v) t)
```

ただし無限側そのものの `nondegenerate` までは、現段階では狙わない。
曲率の infinite-side 制御が未整備だからである。

## 6. 補助補題候補

### L1. `nondegenerateStationaryAt` の congr 補題

```lean
lemma nondegenerateStationaryAt_congr
    {f g : ℝ → ℂ} {t : ℝ}
    (hfg : f = g) :
    DkMath.RH.nondegenerateStationaryAt f t ↔
    DkMath.RH.nondegenerateStationaryAt g t
```

実際には `simpa [hfg]` で済むなら不要。

### L2. `phaseCurv` の関数 ext 補題

`insert_eq_of_mem` で `phaseCurv` 側 simplification が詰まるときの保険。

### L3. packaged theorem から既存 theorem へ戻す projection 補題

structure を導入した場合、

- `PrimeLocalFormationData.hsum0`
- `PrimeLocalFormationData.hcurv0`

を既存 theorem へ渡しやすい補題を置く。

## 7. 実装順序

### Step 1

`eventually_nondegenerateStationaryAt_of_...` を追加する。

理由:

- 既存定理の対称穴を埋める最短ルート
- 実装コストが最も低い
- finite formation theoremization の見栄えが一気によくなる

### Step 2

`PrimeLocalFormationData` を定義し、
PF1 / PF2 / PF2w を packaged theorem へ置き換える。

### Step 3

provider-family 版 packaged theorem を追加する。

### Step 4

`tsum = 0` / `tendsto = 0` を bundled theorem にまとめる。

### Step 5

必要なら docs を同期し、Roadmap/OpenProblems へ

- PF4: eventually nondegenerate normalization
- PF5: packaged formation data
- PF6: infinite outcome bundling

を追記する。

## 8. 具体的な Lean 作業単位

### 8.1. ファイル追加

```text
DkMath/RH/PrimeLocalFormation.lean
DkMath/RH/PrimeLocalFormationInfinite.lean
```

### 8.2. import 更新

```lean
-- DkMath/RH.lean
import DkMath.RH.PrimeLocalFormation
import DkMath.RH.PrimeLocalFormationInfinite
```

### 8.3. ビルド順

```bash
lake build DkMath.RH.PrimeLocalFormation
lake build DkMath.RH.PrimeLocalFormationInfinite
lake build DkMath.RH
```

## 9. リスクと注意点

1. `CFBRCBridge.lean` から theorem を移すと import 循環に注意。
   - 新規ファイルは `EulerZetaLemmas`, `HopcInfiniteLift`, `CFBRC.Bridge` の向きで整理する。
2. `phaseCurv` の `simp` 簡約が弱い可能性。
   - `insert_eq_of_mem` 後に `change` / `simpa` で関数 ext を使う想定。
3. theorem 名が長くなりすぎる。
   - packaged theorem 側で短い別名（`PrimeLocalFormationData` 系）を先に作るとよい。

## 10. 最終判定

最新スナップショットの RH 側は、
**低位補題の不足** よりも **高位 theoremization の整理不足** が主問題である。

したがって次段は、

- 新しい解析核を掘るより
- 既存 bridge / provider / infinite-lift を束ねて
- 「prime-local formation principle」の定理列を固定する

のが最善である。
