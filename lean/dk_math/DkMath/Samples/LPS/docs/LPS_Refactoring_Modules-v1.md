# LPS: Refactoring Modules (v1)

## 1. 結論

わっちなら、`DkMath.Samples.LPS.*` は次の 3 系統へ割って移す。

* **宇宙式の減算観測**
  `DkMath.CosmicFormula.*`
* **指数反転 ( a^b=b^a ) とその連続 branch**
  `DkMath.PowerSwap.*`
* **同次数冪和充填 / observed minimum profile**
  `DkMath.NumberTheory.PowerSums.*`

そして `FLT` には本体を押し込まず、 **橋ファイルだけ** を置く。
これがいちばん循環依存を避けやすく、後で RH や一般 LPS 的議論にも再利用しやすい配置じゃ。

---

## 2. 新ディレクトリ構成案

```text
DkMath/
├── CosmicFormula/
│   ├── CoreBeamGap.lean                -- 既存
│   ├── ResidualNat.lean                -- 新設
│   └── ResidualInt.lean                -- 新設
│
├── PowerSwap/
│   ├── Basic.lean                      -- 新設
│   ├── Exchange.lean                   -- 新設
│   ├── Branch.lean                     -- 新設
│   └── Contours.lean                   -- 新設
│
├── NumberTheory/
│   └── PowerSums/
│       ├── Basic.lean                  -- 新設
│       ├── ObservedMin.lean            -- 新設
│       ├── Examples.lean               -- 新設
│       └── ResidualProfile.lean        -- 新設
│
├── FLT/
│   ├── PowerSumsBridge.lean            -- 新設
│   └── PowerSwapBridge.lean            -- 新設
│
├── CosmicFormula.lean                  -- 既存更新
├── PowerSwap.lean                      -- 新設
└── NumberTheory/
    └── PowerSums.lean                  -- 新設
```

---

## 3. 旧ファイル → 新ファイル対応

```text
DkMath/Samples/LPS/BigFamily.lean
  → DkMath/CosmicFormula/ResidualNat.lean

DkMath/Samples/LPS/BigFamilyInt.lean
  → DkMath/CosmicFormula/ResidualInt.lean

DkMath/Samples/LPS/PowerSwap.lean
  → DkMath/PowerSwap/Basic.lean

DkMath/Samples/LPS/Exchange.lean
  → DkMath/PowerSwap/Exchange.lean

DkMath/Samples/LPS/PowerSwapBranch.lean
  → DkMath/PowerSwap/Branch.lean

DkMath/Samples/LPS/GapContours.lean
  → DkMath/PowerSwap/Contours.lean

DkMath/Samples/LPS/GapFillRank.lean
  → DkMath/NumberTheory/PowerSums/Basic.lean

DkMath/Samples/LPS/BigFamilyExamples.lean
  → 分割して移す
     - fillability 基本例      → NumberTheory/PowerSums/Examples.lean
     - observed min profile   → NumberTheory/PowerSums/ResidualProfile.lean
     - exchange 例            → PowerSwap/Exchange.lean に吸収
     - powerSwap 例           → PowerSwap/Basic.lean に吸収
```

ここでの要点は、`BigFamilyExamples.lean` が今は **寄せ鍋** なので、これを割ることじゃ。
ここを割らぬと、移行してもまた混ざる。

---

## 4. 各ファイルの import 一覧

## 4.1. `DkMath/CosmicFormula/ResidualNat.lean`

```lean
import Mathlib
import DkMath.CosmicFormula.CoreBeamGap
```

役目:

* `Nat` 上の `body := big - gap`
* `beam := body - core`
* `residual := big - body`
* `residual_eq_gap`
* `big_eq_body_add_gap`
* `big_eq_core_add_beam_add_gap`

留意点:

* generic な `Core/Gap/Big` は既存 `CoreBeamGap` を使う
* `Nat` 減算の戻しだけをここで担当する

---

## 4.2. `DkMath/CosmicFormula/ResidualInt.lean`

```lean
import Mathlib
import DkMath.CosmicFormula.CoreBeamGap
```

役目:

* `ℤ` 上の subtractive view
* `body + gap = big`
* `beam + core = body`
* `big = core + beam + gap`
* `residual_eq_gap`

留意点:

* `Nat` 版の補題に無理に依存させず、独立でよい
* `ℤ` では群演算として自然に戻せるので、本命観測はむしろこちら

---

## 4.3. `DkMath/PowerSwap/Basic.lean`

```lean
import Mathlib
```

役目:

* `def PowerSwap (a b : ℕ) : Prop := a ^ b = b ^ a`
* `powerSwap_refl`
* `powerSwap_symm`
* `powerSwap_two_four`
* `powerSwap_four_two`
* `exists_powerSwap_nontrivial`
* `powerSwap_with_one`

留意点:

* ここは離散版だけ
* `Exchange` や `Branch` を import しない

---

## 4.4. `DkMath/PowerSwap/Exchange.lean`

```lean
import Mathlib
```

役目:

* `exchange_condition_minimal_nat`
* `exchange_condition_minimal_int`
* `exchange_example_4_2_eq_2_4`
* `exchange_example_8_2_eq_2_6`
* `exchange_example_9_2_eq_3_4`
* `exchange_example_27_2_eq_3_6`

留意点:

* `PowerSwap.Basic` を import しなくてよい
* 交換則はそれ自体で独立した道具として保つ

---

## 4.5. `DkMath/PowerSwap/Branch.lean`

```lean
import Mathlib
```

役目:

* `PowerSwapBranchDomain`
* `powerSwapBranchX`
* `powerSwapBranchY`
* `powerSwapBranchPair`
* `powerSwap_branchX_eq_exp_log_div_sub`
* `powerSwap_branchY_eq_exp_mul_log_div_sub`
* `tendsto_log_div_sub_one_at_one_punctured`
* `tendsto_mul_log_div_sub_one_at_one_punctured`
* `powerSwap_branch_limit_to_e`
* `powerSwap_branch_correct`
* `powerSwap_branch_at_two`
* `powerSwap_branch_at_half`

留意点:

* ここに `Contours` を入れない
* まずは branch 自体の解析を閉じる

---

## 4.6. `DkMath/PowerSwap/Contours.lean`

```lean
import Mathlib
```

役目:

* `gapU`, `gapV`, `gapP`, `gapQ`
* `harmonicCoord`
* `gapF`
* `gapF_eq_expU_sub_expV`
* `gapF_eq_soft_hyperbolic_form`
* `gapQ_eq_xy_mul_Hdiff`
* `gapQ_at_e_e`
* `gapP_at_e_e`
* `gapF_at_e_e`
* `localX`, `localY`
* `gapQuadraticModel`
* `gapQuadraticModel_swap_neg`
* `gapQuadraticModel_diag_zero`

留意点:

* 現段階では `Branch` に依存させない
* 幾何座標そのものを独立資産にする

---

## 4.7. `DkMath/NumberTheory/PowerSums/Basic.lean`

```lean
import Mathlib
```

役目:

* `FillableByPowSumExact`
* `FillableByPowSumLE`
* `ResidualFillableExact`
* `fillable_zero_exact_zero`
* `fillable_exact_of_exact_le`
* `fillable_le_of_exact`

留意点:

* ここには具体例を入れない
* 純粋 API に徹する

---

## 4.8. `DkMath/NumberTheory/PowerSums/ObservedMin.lean`

```lean
import DkMath.NumberTheory.PowerSums.Basic
```

役目:

* `ObservedMinOne`
* `ObservedMinTwo`
* 将来の `ObservedMin d n r` への昇格口

留意点:

* `Basic` の薄い上位層として置く
* 例や profile 標本は入れない

---

## 4.9. `DkMath/NumberTheory/PowerSums/Examples.lean`

```lean
import Mathlib
import DkMath.NumberTheory.PowerSums.ObservedMin
```

役目:

* `fillable_sq_16_exact_one`
* `fillable_sq_25_exact_two`
* `fillable_cube_216_exact_one`
* `fillable_cube_216_exact_three`
* `3^3 + 4^3 + 5^3 = 6^3`

留意点:

* ここは単純な concrete example だけ
* same Big/profile 分岐は次ファイルへ分離

---

## 4.10. `DkMath/NumberTheory/PowerSums/ResidualProfile.lean`

```lean
import Mathlib
import DkMath.NumberTheory.PowerSums.ObservedMin
```

役目:

* `candidateBig`
* `candidateBody₁`
* `candidateBody₂`
* `candidate_residuals_split`
* `candidate_fill_body₁_exact_two`
* `candidate_fill_body₁_not_exact_one`
* `candidate_fill_body₂_exact_one`
* `candidate_same_big_observed_min_split`
* `candidate_same_big_observed_min_profile`

留意点:

* ここが「same Big / different Body / different observed minimum profile」の本体
* `Examples.lean` より一段理論寄り

---

## 4.11. `DkMath/FLT/PowerSumsBridge.lean`

```lean
import DkMath.FLT.Basic
import DkMath.CosmicFormula.ResidualNat
import DkMath.NumberTheory.PowerSums.ObservedMin
```

役目:

* FLT 視点で residual fillability を読む橋
* `big - body` が ( d ) 乗和で埋まる条件を FLT 的禁止構造へ写す入口

留意点:

* 本体定理は置かず、翻訳レイヤに徹する

---

## 4.12. `DkMath/FLT/PowerSwapBridge.lean`

```lean
import DkMath.FLT.Basic
import DkMath.PowerSwap
```

役目:

* `PowerSwap` の離散 / branch 幾何を FLT の説明補助へ接続
* ただし FLT 本体を `PowerSwap` に依存させすぎない

---

## 5. 集約ファイルの import 一覧

## 5.1. `DkMath/PowerSwap.lean`

```lean
import DkMath.PowerSwap.Basic
import DkMath.PowerSwap.Exchange
import DkMath.PowerSwap.Branch
import DkMath.PowerSwap.Contours
```

これはそのまま top-level 集約でよい。
`PowerSwap` は単独の柱として立つ。

---

## 5.2. `DkMath/NumberTheory/PowerSums.lean`

ここは 2 通りあるが、わっちは **安定層だけ import** を勧める。

```lean
import DkMath.NumberTheory.PowerSums.Basic
import DkMath.NumberTheory.PowerSums.ObservedMin
```

理由:

* `Examples` と `ResidualProfile` はまだ研究寄り
* public API に最初から全部流し込むと揺れやすい

---

## 5.3. `DkMath/CosmicFormula.lean` 追記案

```lean
import Mathlib
import DkMath.CosmicFormula.Basic
import DkMath.CosmicFormula.CoreBeamGap
import DkMath.CosmicFormula.ResidualNat
import DkMath.CosmicFormula.ResidualInt
```

`BigFamily` 系の居場所は、ここへ吸収するのがよい。

---

## 5.4. `DkMath/Research.lean` 追記案

研究段階の標本・橋はここで読む。

```lean
import DkMath.NumberTheory.PowerSums.Examples
import DkMath.NumberTheory.PowerSums.ResidualProfile
import DkMath.FLT.PowerSumsBridge
import DkMath.FLT.PowerSwapBridge
```

これで `Samples` から脱出しつつ、まだ public 本丸へ全部は入れぬ、という中間地帯が作れる。

---

## 5.5. `DkMath.lean` の扱い

今すぐは、無理に `DkMath.lean` へ全部足さなくてよい。
移行直後はまず

* `DkMath.CosmicFormula`
* `DkMath.PowerSwap`
* `DkMath.NumberTheory.PowerSums`
* `DkMath.Research`

を個別に build できるようにしておく。

そのあと安定したら `DkMath.lean` に

```lean
import DkMath.PowerSwap
import DkMath.NumberTheory.PowerSums
```

を加える。
逆に `DkMath.Samples` は、最後に静かに降ろせばよい。

---

## 6. いちばん大事な整理原則

この再編の芯はこれじゃ。

\[
\text{CosmicFormula}
\quad\longrightarrow\quad
\text{PowerSums}
\quad\longrightarrow\quad
\text{FLT bridge}
\]

と、

\[
\text{PowerSwap}
\quad\longrightarrow\quad
\text{FLT bridge}
\]

を分けること。
つまり **道具箱** と **本丸** を混ぜぬことじゃ。
