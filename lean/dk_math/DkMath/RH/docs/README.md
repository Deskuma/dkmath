# DkMath.RH：位相ドリフト骨格 + EulerZeta（現状の全コード）

- Authors: D. and Kenro (ChatGPT-5.2)
- Last updated: 2026/01/21 15:55

このディレクトリは、リーマンゼータ関数に差し込む前に必要な

- 「複素関数の位相（角度）の変化＝位相速度」を Lean で扱う骨格
- その骨格を使って定義した **EulerZeta（magnitude/phase）** の無限積を、収束・正値まで含めて固める

ためのモジュール群です。

重要方針は 2 つ：

1. `arg`（偏角）を直接扱わず、**位相を積分で定義（アンラップ）** して枝問題を回避する。
2. 位相付き Euler 因子を「magnitude（大きさ）」と「phase（位相）」に分解し、
   まず magnitude の無限積を **σ > 1 で収束する**ことまで Lean で確定する。

---

## 論文

このモジュール群の理論的背景は、次の論文に基づきます。

- [Euler Zeta Function ζe(s): A Novel Approach to Prime Distribution through Scale Analysis](./EulerZetaFunction-v0-1.pdf)
  - March 15, 2025
  - Author: D. and Kenro (ChatGPT-4o)
  - cid: 67d46595-3550-8009-896d-00c3263c4f23

### オイラーゼータ関数

$$
  \Large
  \zeta_e(s) = \prod_{p} \frac{e^{\,\sigma \log p}}{| e^{\,(\sigma+it) \log p} - 1 |}
$$

オイラー積表示より導出されたゼータ関数の変形版で、位相因子を含むものを指します。

#### オイラー積表示

$$
  \large
  \zeta(s) = \prod_{p} \frac{1}{1 - p^{-s}}
$$

$$
  \left(\;
  \frac{1}{1 - p^{-s}}
  = \frac{p^s}{p^s - 1}
  = \frac{\exp(s\ln p)}{\exp(s\ln p) - 1}
  \;\right)
$$

※ $s = \sigma + it$ : 複素数変数

---

## ファイル構成（現状）

### 位相ドリフト骨格

- `Basic.lean`  
  空ファイル（予約）。将来の共通設定や再輸出（re-export）置き場候補。

- `Defs.lean`  
  定義置き場（記号・概念の導入のみ）。

- `Lemmas.lean`  
  定義間の関係を示す補題（代数コア、同値、別表現など）。

- `Theorems.lean`  
  積分で定義した位相が期待通り微分できること（解析骨格）を示す定理。

### EulerZeta（今回追加された成果）

- `EulerZeta.lean`  
  EulerZeta（magnitude/phase）に関する公開インタフェース（定義の再輸出、主要定理の提示）。

- `EulerZetaLemmas.lean`  
  EulerZeta の局所補題集：
  分母 `w = exp((σ+it)log p) - 1` の非零、`‖a_p - 1‖` の評価など。

- `EulerZetaConvergence.lean`  
  収束と正値の主証明：
  `σ > 1` のもとで `EulerZetaMagMultipliable` と `0 < eulerZetaMag` を確定。

---

## 位相ドリフト骨格：到達点（短く）

- 位相速度 `phaseVel` を `torque / normSq` として代数的に扱えるようにした。
- 「ドリフト消失」は「位相速度ゼロ」と同値になった（零点回避 `f t ≠ 0` を条件に）。
- `arg` を使わず、位相を積分で定義した上で、微分が正しく戻ることを示した。

（詳細は [DkMath_RH.md](./DkMath_RH.md) を参照）

---

## EulerZeta：定義と成果（短く）

### 定義（magnitude / phase）

素数ごとに

- 分母（複素数）  
  `w(p,σ,t) := exp((σ+it)log p) - 1`

- magnitude 因子（実数）  
  `a_p(σ,t) := exp(σ log p) / ‖w(p,σ,t)‖`

を定義し、EulerZeta magnitude を

- `eulerZetaMag (σ t : ℝ) : ℝ := ∏' p : {p // Nat.Prime p}, a_p(σ,t)`

として無限積（`tprod`）で定義します。

また位相は

- `eulerZetaPhase (p) (σ t) := Complex.arg (w(p,σ,t))`

として別途導入します（位相骨格の側は `arg` を直接使わずにアンラップへ接続する予定）。

### 主定理（σ > 1）

- `eulerZetaMag_multipliable_sigma_gt_one`  
  `σ > 1` のもとで EulerZeta magnitude の無限積が収束（`Multipliable`）。

- `eulerZetaMag_pos_sigma_gt_one`  
  `σ > 1` のもとで `0 < eulerZetaMag σ t`。

### 証明戦略（要点）

1. `w(p,σ,t) ≠ 0` を確定（定義が安全になる）。
2. 近似評価：`‖a_p(σ,t) - 1‖ ≤ 2 / p^σ`（σ > 1）。
3. `∑ 1/n^σ`（p-series）へ比較して `Summable` を得る。
4. Mathlib の一般定理で `Multipliable` と `tprod` の正値へ落とす。

---

## `#print axioms` に `sorryAx` が出る件について（メモ）

ソース（`.lean`）上に `sorry` が無いのに `#print axioms` で `sorryAx` が見える場合、
典型的には次のどちらかです：

- 古い `.olean` が残っている（ビルドキャッシュ混入）
- 依存先（環境側）に `sorryAx` を含むものがある

まずは `lake clean` と `.lake/build` の再生成で切り分けるのが確実です。

なお `propext / Classical.choice / Quot.sound` は、Mathlib を普通に使うと出やすい標準的な依存です。

---

## 次にやると自然な拡張（予定メモ）

- EulerZeta の phase 側を、位相骨格（アンラップ位相）へ接続する：
  `arg` を直接扱わず、`phaseUnwrap` で連続位相として扱う。
- σ 方向（横方向）でも同型テンプレートを作る：
  `phaseVelSigma` / `phaseUnwrapSigma`。
- ゼータ差し込みのための仮定（零点回避・可微分性・可積分性）を整理してまとめる。

---

GitHub Markdown and $\LaTeX$ Style
This document uses GitHub-flavored Markdown and $\LaTeX$ for mathematical expressions. To render the $\LaTeX$ expressions correctly, ensure that your Markdown viewer supports MathJax or a similar library.
