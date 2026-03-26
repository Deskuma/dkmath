# Gap 補正係数 RH 側 Lean 実装計画書

## 対象

- `DkMath.RH.EulerZeta`
- `DkMath.RH.EulerZetaLemmas`
- `DkMath.RH.EulerZetaConvergence`
- 将来候補: `DkMath.RH.CosmicGapBridge` または `DkMath.RH.EulerZetaGapBridge`

---

## 1. 現状把握

最新スナップショット実見では、RH 側はすでに次の塔になっている。

1. `Defs.lean`
   - `vertical`
   - `phaseVel`
   - `stationaryAt`
   - `phaseCurv`

2. `EulerZeta.lean`
   - `eulerZetaFactor`
   - `eulerZeta_exp_s_log_p_sub_one`
   - `eulerZetaFactorMag`
   - `eulerZetaFinite_onVertical`
   - `hopcPrimeLocalContribution`
   - `hopcPrimeContributionSum`

3. `EulerZetaLemmas.lean`
   - 局所因子の phaseVel 分解
   - 有限積の位相速度 = 局所寄与和
   - `stationaryAt ↔ hopcPrimeContributionSum = 0`

4. `HopcInfiniteLift.lean`
   - finite → infinite の lift
   - `tsum`
   - `tendsto`
   - `σ > 1` 型 majorant

5. `CFBRCBridge.lean`
   - primitive prime witness を RH 側停留条件へ橋渡し

6. `EulerZetaConvergence.lean`
   - `σ > 1` における magnitude 版収束

したがって今回の Gap 補正係数は、
**EulerZeta の核そのものを 1 段一般化する強化**
として入れるのが最短経路である。

---

## 2. 中心アイデア

現行の Euler 因子は

\[
\mathrm{eulerZetaFactor}(p,s)=\frac{p^s}{p^s-1}
\]

である。

ここで Gap 補正係数を

\[
\gamma
\]

とし、**追加 Gap の強さ**
として扱う。

このとき補正後因子は

\[
\mathrm{eulerZetaFactorGapCorr}(\gamma;p,s)
:=
\frac{p^s-(1+\gamma)}{p^s-1}
\]

と置くのが最も自然である。

### 2.1. この形の利点

\[
\gamma=0
\quad\Rightarrow\quad
\frac{p^s-1}{p^s-1}=1
\]

ではなくなるので、ここは注意がいる。

したがって **「補正後の全因子」** と **「補正係数」** は分けて定義する。

### 2.2. 推奨する二層定義

#### 基本 Euler 因子

\[
E(p,s):=\frac{p^s}{p^s-1}
\]

#### Gap 補正係数

\[
C_\gamma(p,s):=
\frac{p^s-(1+\gamma)}{p^s} =
1-(1+\gamma)p^{-s}
\]

#### 補正後 Euler 因子

\[
E_\gamma(p,s):=E(p,s)\,C_\gamma(p,s) =
\frac{p^s-(1+\gamma)}{p^s-1}
\]

これで

- \(\gamma=-1\) で現行 `eulerZetaFactor`
- \(\gamma=0\) で
  \[
  \frac{p^s-1}{p^s-1}=1
  \]

- \(\gamma=1\) で
  \[
  \frac{p^s-2}{p^s-1}
  \]

  となる。

### 2.3. ただし実務上は別パラメータの方がよい

Lean 実装では、利用感を優先して

\[
\alpha := 1+\gamma
\]

を主パラメータにする方がきれいである。

その場合は

\[
E_\alpha(p,s):=\frac{p^s-\alpha}{p^s-1}
\]

と定義し、

- \(\alpha=0\) で現行 Euler 因子
- \(\alpha=1\) で恒等因子 \(1\)
- \(\alpha=2\) で Reddit 由来の補正因子

となる。

**結論**:
Lean コード上は `α` を採用し、文書では
「Gap 補正強度 \(\gamma=\alpha-1\)」
と読むのがよい。

---

## 3. 推奨定義名

### 3.1. `EulerZeta.lean` に追加する定義

```lean
noncomputable def eulerZetaFactorAlpha (α : ℂ) (p : ℕ) (s : ℂ) : ℂ :=
  (((p : ℂ) ^ s) - α) / (((p : ℂ) ^ s) - 1)
```

```lean
noncomputable def eulerZetaAlpha (α : ℂ) (s : ℂ) : ℂ :=
  ∏' p : {p // Nat.Prime p}, eulerZetaFactorAlpha α p.1 s
```

```lean
noncomputable def eulerZetaFactorAlpha_onVertical
    (α : ℂ) (p : ℕ) (σ t : ℝ) : ℂ :=
  (Complex.exp (vertical σ t * (Real.log (p : ℝ) : ℂ)) - α) /
    eulerZeta_exp_s_log_p_sub_one p σ t
```

```lean
noncomputable def eulerZetaFactorAlphaFinite
    (α : ℂ) (S : Finset {p // Nat.Prime p}) (s : ℂ) : ℂ :=
  ∏ p ∈ S, eulerZetaFactorAlpha α p.1 s
```

```lean
noncomputable def eulerZetaFactorAlphaFinite_onVertical
    (α : ℂ) (S : Finset {p // Nat.Prime p}) (σ t : ℝ) : ℂ :=
  eulerZetaFactorAlphaFinite α S (vertical σ t)
```

### 3.2. magnitude 側も平行追加

```lean
noncomputable def eulerZetaFactorAlphaMag (α : ℂ) (p : ℕ) (σ t : ℝ) : ℝ :=
  let num := Complex.exp (vertical σ t * (Real.log (p : ℝ) : ℂ)) - α
  let den := eulerZeta_exp_s_log_p_sub_one p σ t
  ‖num‖ / ‖den‖
```

これで

\[
\alpha=0
\Rightarrow
\|e^z\| / \|e^z-1\| =
e^{\sigma\log p}/\|e^z-1\|
\]

となり、現行 `eulerZetaFactorMag` をきれいに回収できる。

---

## 4. まず通すべき基本補題

### 4.1. 現行因子の回収

```lean
lemma eulerZetaFactorAlpha_zero (p : ℕ) (s : ℂ) :
  eulerZetaFactorAlpha 0 p s = eulerZetaFactor p s
```

```lean
lemma eulerZetaFactorAlphaMag_zero (p : ℕ) (σ t : ℝ) :
  eulerZetaFactorAlphaMag 0 p σ t = eulerZetaFactorMag p σ t
```

### 4.2. 特殊値

```lean
lemma eulerZetaFactorAlpha_one (p : ℕ) (s : ℂ) :
  eulerZetaFactorAlpha 1 p s = 1
```

```lean
lemma eulerZetaFactorAlpha_two (p : ℕ) (s : ℂ) :
  eulerZetaFactorAlpha 2 p s =
    ((((p : ℂ) ^ s) - 2) / (((p : ℂ) ^ s) - 1))
```

### 4.3. 現行 Euler 因子との分解

```lean
lemma eulerZetaFactorAlpha_eq_eulerZetaFactor_mul_filter
    (α : ℂ) (p : ℕ) (s : ℂ) :
  eulerZetaFactorAlpha α p s =
    eulerZetaFactor p s * (1 - α * ((p : ℂ) ^ (-s)))
```

これは
「現行 Euler 因子 × Gap フィルタ」
という形を固定する中核補題である。

### 4.4. Gap 調整量の露出

```lean
lemma eulerZetaFactorAlpha_eq_one_sub_gapTerm
    (α : ℂ) (p : ℕ) (s : ℂ) :
  eulerZetaFactorAlpha α p s =
    1 - (α - 1) / (((p : ℂ) ^ s) - 1)
```

これは宇宙式語彙でいう
**Gap 調整量**

\[
(\alpha-1)/((p^s)-1)
\]

を直接見せる補題である。

---

## 5. HOPC-RH 接続の中心補題

今回いちばん大事なのはここじゃ。

現行では

\[
\mathrm{phaseVel}(E_p)=\log p-\mathrm{phaseVel}(w_p)
\]

という形で `hopcPrimeLocalContribution` が定義されている。

補正後は numerator が

\[
e^z-\alpha
\]

へ変わるので、局所寄与は

\[
\mathrm{phaseVel}(e^z-\alpha)-\mathrm{phaseVel}(e^z-1)
\]

へ一般化される。

### 5.1. 新しい局所位相寄与

```lean
noncomputable def eulerZetaAlphaPhaseVelLocal
    (α : ℂ) (p : ℕ) (σ t : ℝ) : ℝ :=
  DkMath.RH.phaseVel
    (fun u : ℝ =>
      Complex.exp (vertical σ u * (Real.log (p : ℝ) : ℂ)) - α) t
```

```lean
noncomputable def hopcAlphaLocalContribution
    (α : ℂ) (p : ℕ) (σ t : ℝ) : ℝ :=
  eulerZetaAlphaPhaseVelLocal α p σ t - eulerZetaPhaseVelLocal p σ t
```

### 5.2. 回収補題

```lean
lemma hopcAlphaLocalContribution_zero
    (p : ℕ) (σ t : ℝ) :
  hopcAlphaLocalContribution 0 p σ t =
    hopcPrimeLocalContribution p σ t
```

### 5.3. 因子の phaseVel 分解

```lean
lemma phaseVel_eulerZetaFactorAlpha_onVertical_eq
    (α : ℂ) (p : ℕ) (σ t : ℝ)
    (hnum : Complex.exp (vertical σ t * (Real.log (p : ℝ) : ℂ)) - α ≠ 0)
    (hden : eulerZeta_exp_s_log_p_sub_one p σ t ≠ 0) :
  DkMath.RH.phaseVel
      (fun u : ℝ => eulerZetaFactorAlpha_onVertical α p σ u) t
    =
      eulerZetaAlphaPhaseVelLocal α p σ t
        - eulerZetaPhaseVelLocal p σ t
```

ここで `phaseVel_div` を再利用する。

---

## 6. 有限積 API までの拡張

### 6.1. 有限和化

```lean
lemma eulerZetaFactorAlphaPhaseVelFinite_eq_sum
    (α : ℂ) (S : Finset {p // Nat.Prime p}) (σ t : ℝ)
    (hnum : ∀ p ∈ S,
      Complex.exp (vertical σ t * (Real.log (p.1 : ℝ) : ℂ)) - α ≠ 0)
    (hden : ∀ p ∈ S, eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0) :
  DkMath.RH.phaseVel
      (fun u : ℝ => eulerZetaFactorAlphaFinite_onVertical α S σ u) t
    =
      ∑ p ∈ S, hopcAlphaLocalContribution α p.1 σ t
```

### 6.2. 停留判定

```lean
lemma stationaryAt_eulerZetaFactorAlphaFinite_onVertical_iff_sum_eq_zero
    (α : ℂ) (S : Finset {p // Nat.Prime p}) (σ t : ℝ)
    ... :
  DkMath.RH.stationaryAt
      (fun u : ℝ => eulerZetaFactorAlphaFinite_onVertical α S σ u) t
    ↔
      (∑ p ∈ S, hopcAlphaLocalContribution α p.1 σ t) = 0
```

### 6.3. 非退化停留判定

現行 `nondegenerateStationaryAt ... ↔ sum=0 ∧ phaseCurv ≠ 0`
の α-generalization を平行追加する。

---

## 7. 収束側は第2段階

`EulerZetaConvergence.lean` では、まず
有限 API を固めてから入るのが安全。

### 7.1. まず狙う評価

\[
\left\|
\frac{e^z-\alpha}{e^z-1}-1
\right\| =
\frac{|1-\alpha|}{|e^z-1|}
\]

なので、既存の

\[
|e^z-1|^{-1} \ll p^{-\sigma}
\]

型評価が再利用できれば、

\[
\left\|E_\alpha(p,\sigma+it)-1\right\|
\le
\frac{C_\alpha}{p^\sigma}
\]

へ落とせる。

### 7.2. 追加定理候補

```lean
theorem eulerZetaFactorAlpha_norm_sub_one_upper_bound
    (α : ℂ) (p : ℕ) (hp : Nat.Prime p) (σ t : ℝ) (hσ : 1 < σ) :
  ‖eulerZetaFactorAlpha α p (vertical σ t) - 1‖
    ≤ (2 * ‖1 - α‖) / ((p : ℝ) ^ σ)
```

```lean
theorem eulerZetaAlpha_multipliable_sigma_gt_one
    (α : ℂ) (σ : ℝ) (hσ : 1 < σ) (t : ℝ) :
  Multipliable (fun p : {p // Nat.Prime p} =>
    eulerZetaFactorAlpha α p.1 (vertical σ t))
```

### 7.3. ここでの注意

現行 `eulerZetaMag_pos_sigma_gt_one` のような
**正値そのもの**
は magnitude 版では通しやすいが、複素版の full product は正値対象でない。

よって第2段階では

- complex product の `Multipliable`
- magnitude product の `Multipliable` と `0 ≤ ...`
- 必要なら strict positivity

を分けて扱う。

---

## 8. CFBRCBridge 連携は第3段階

これは最初から触らぬ方がよい。

理由:
現行 `CFBRCBridge.lean` はすでに
`hopcPrimeContributionSum = 0`
を中心に大量 wrapper を持っている。
ここへ一気に α-generalization を流し込むと、橋が重くなる。

### 8.1. 第1段階ではやらないこと

- 既存 `hopcPrimeLocalContribution` の意味変更
- 既存 `hopcPrimeContributionSum` の意味変更
- `CFBRCBridge` 既存定理の引数追加

### 8.2. 第3段階でやること

別名で parallel API を追加する。

```lean
noncomputable def hopcAlphaContributionSum
```

```lean
theorem stationaryAt_insert_of_hopcAlphaContributionSum_eq_zero
```

```lean
theorem exists_primeLocalFormation_insert_of_cfbRc_primitive_prime_boundary_bridge_of_alpha_local_split_and_phaseCurv
```

ただしこれは
**既存 API を壊さず増設**
で行う。

---

## 9. モジュール分割の推奨

### 最小改造案

- `EulerZeta.lean` に定義追加
- `EulerZetaLemmas.lean` に補題追加
- `EulerZetaConvergence.lean` に収束追加

### 将来の整理案

膨らんだら次へ分ける。

```text
DkMath/RH/EulerZetaGap.lean
DkMath/RH/EulerZetaGapLemmas.lean
DkMath/RH/EulerZetaGapConvergence.lean
DkMath/RH/CosmicGapBridge.lean
```

わっちの見立てでは、まずは **既存3ファイルへの増設** で十分じゃ。

---

## 10. 実装順

### Phase 1. 定義

1. `eulerZetaFactorAlpha`
2. `eulerZetaFactorAlpha_onVertical`
3. `eulerZetaFactorAlphaMag`
4. `hopcAlphaLocalContribution`

### Phase 2. 基本補題

1. `alpha=0,1,2` 特殊化
2. `eq_eulerZetaFactor_mul_filter`
3. `eq_one_sub_gapTerm`

### Phase 3. 位相補題

1. numerator 側 differentiability
2. `phaseVel_div` で局所分解
3. finite sum 化
4. stationary / nondegenerate 判定

### Phase 4. 収束

1. `norm_sub_one` 上界
2. `Summable`
3. `Multipliable`

### Phase 5. bridge

1. α-generalized HOPC sum
2. CFBRC 側 wrapper

---

## 11. 命名についての最終提案

数学記号としては

\[
\alpha
\]

を採用し、文書では

\[
\gamma := \alpha - 1
\]

を **真の Gap 補正強度**
と説明する。

Lean 名は次で統一する。

- `eulerZetaFactorAlpha`
- `eulerZetaFactorAlpha_onVertical`
- `eulerZetaFactorAlphaMag`
- `eulerZetaAlphaPhaseVelLocal`
- `hopcAlphaLocalContribution`
- `hopcAlphaContributionSum`

これで

- 既存 `hopcPrime...` 系は \(\alpha=0\) 特殊化
- Reddit 型の隣接 2 禁制は \(\alpha=2\)
- 宇宙式の Gap 調整強度は \(\gamma=\alpha-1\)

という三層が、全部 1 本に束ねられる。

---

## 12. 一言まとめ

今回の実装の芯は、

\[
\frac{p^s}{p^s-1}
\]

を捨てることではなく、

\[
\frac{p^s-\alpha}{p^s-1}
\]

へ **平行拡張** し、

\[
\alpha=0
\]

で現行 RH 実装をそのまま回収しつつ、

\[
\alpha=2
\]

で Gap 補正付き Euler 因子を扱えるようにすることじゃ。

これは `EulerZeta.lean` の強化補題として極めて自然であり、
しかも HOPC-RH / CFBRCBridge への接続導線を壊さぬ。
