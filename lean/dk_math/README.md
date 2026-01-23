# dk_math

presented by D. and Wise Wolf

## 概要

- dk_math は、Lean 4 用の数学ライブラリであり、
特に動的調和数論（Dynamic Harmonic Number Theory, DHNT）に焦点を当てています。
- このライブラリは、単位と量の概念を導入し、数学的な定義や定理を形式化するためのツールを提供します。

## カテゴリ

- 数学ライブラリ
  - DkMath
    - 基本定義とユーティリティ (Basic Definitions and Utilities)
    - 動的調和数論 (Dynamic Harmonic Number Theory, DHNT)
    - 宇宙式 (Cosmic Formula)
    - ポリオミノ (Polyomino)
    - 単位と量の理論 (Units and Quantities Theory)

## ファイル

- 動的調和数論 (DHNT) 主要ファイル一覧 (.lean):
  - Dynamic Harmonic Number Theory: [DHNT](./DkMath/DHNT.lean)
  - 宇宙式 [CosmicFormula](./DkMath/CosmicFormula.lean)
    - 線形代数版 [CosmicFormulaLinear](./DkMath/CosmicFormulaLinear.lean)
    - ジオメトリ（有限集合）版 [CosmicFormulaGeom](./DkMath/CosmicFormulaGeom.lean)
    - 次元版 [CosmicFormulaDim](./DkMath/CosmicFormulaDim.lean)
      - docs: (.md)
        - 宇宙式の次元に関する定理 [CosmicFormulaCellDim.md](./DkMath/CosmicFormulaCellDim.md)
  - トロミノ構造 [Tromino](./DkMath/Tromino.lean)
  - 宇宙式とトロミノ構造の接続定理 [CosmicFormulaTrominoLink](./DkMath/CosmicFormulaTrominoLink.lean)
- 基本定義とユーティリティ [Basic](./DkMath/Basic.lean)
- サンプル定理と例 [Samples](./DkMath/Samples.lean)

## ドキュメント

### 宇宙式の次元に関する定理

---

# CosmicFormulaCellDim — README

## 概要

本リポジトリ（/モジュール）は、2次元平面の直観（トロミノ/L字構造）から出発した **宇宙式の Big/Body/Gap 分解**を、格子セル上の有限集合 `Finset` として実装し、さらに **任意次元 (d)** に無次元一般化したものです。

中心となる主張は、有限集合の濃度（`card`）を介して

\[
\#\mathrm{Big}=\#\mathrm{Body}+\#\mathrm{Gap},\qquad
\#\mathrm{Big}=(x+u)^d,\quad \#\mathrm{Gap}=u^d
\]

\[
\boxed{\ \#\mathrm{Body}=(x+u)^d-u^d = x\cdot G(d,x,u)=x\cdot G_{\mathrm{binom}}(d,x,u)\ }
\]

が Lean で形式証明される、という点にあります。

---

## モチベーション

- 2次元の「L字（トロミノ的）余白」を **集合の分割**として捉え、そこから現れる不変量（余白のべき \(u^d\)）を抽出したい。
- 平面 \(\mathbb{Z}^2\) に固定された議論ではなく、**任意次元 (d)** で同型に回る構造として定式化したい。
- さらに、差のべき因数分解の **幾何和表現** と **二項係数（choose）表現** が同値であることを示し、係数が「分類数」として現れる構造を明確化したい。

---

## 主要アイデア（Big / Body / Gap）

- **Big**：全体（箱）
- **Gap**：余白（小さい箱）
- **Body**：実体（差集合／または構成的分解）

これらを `Finset (Cell d)` の分割として扱い、`card` を通じて “体積” に相当する量へ落とします。

---

## 実装の骨格

### 1. 無次元セル空間 `Cell d`

- `Cell (d : ℕ) := Fin d → ℤ`

座標に依存せず、(d) 次元格子点を一様に扱います。

### 2. 平行移動 `translate` と濃度不変性

- `translate v S` を `Finset.map` により実装
- `card_translate : (translate v S).card = S.card`

位置（原点）は本質ではなく、形（集合）だけを扱えるようにします。

### 3. 箱 `Box` / `BoxAt` と濃度計算

- `Box a`：各軸 `0 ≤ coord < a i` の直方体
- `card_Box_eq_prod : (Box a).card = ∏ i, a i`
- `BoxAt` は `translate` により構築し、濃度は同じ

---

## 定義（宇宙式：Big / Gap / Body）

- `constVec d n : Fin d → ℕ`
- `Big (d x u) := Box (constVec d (x+u))`
- `Gap (d u) := Box (constVec d u)`
- `Body (d x u) := Big \ Gap`

---

## 主結果（定理カタログ）

### A. 集合としての分解

- `Gap_subset_Big`
- `Big_eq_Body_union_Gap : Big = Body ∪ Gap`
- `Disjoint_Body_Gap : Disjoint Body Gap`
- `card_Big_eq_card_Body_add_card_Gap :
    card Big = card Body + card Gap`

### B. べき表示（積→べき）

- `prod_const_fin : (∏ _ : Fin d, n) = n^d`
- `card_Big_pow : card Big = (x+u)^d`
- `card_Gap_pow : card Gap = u^d`
- `card_Body_pow_form : card Body = (x+u)^d - u^d`

### C. 差のべき因数分解（幾何和版）

- `G (d x u)`（幾何和）
- `pow_sub_pow_eq_mul_G :
    (x+u)^d - u^d = x * G d x u`
- `card_Body_eq_mul_G :
    card Body = x * G d x u`

### D. 二項定理（choose）版との同値

- `Gbinom (d x u)`（choose 版）
- `pow_sub_pow_eq_mul_Gbinom :
    (x+u)^d - u^d = x * Gbinom d x u`
- `mul_G_eq_mul_Gbinom :
    x * G d x u = x * Gbinom d x u`
- `G_eq_Gbinom_of_pos (hx : 0 < x) :
    G d x u = Gbinom d x u`

### E. 構成的分解（Slab による disjoint union）

- `Slab0`, `slabShift`, `Slab`（最小軸ルール）
- `Slab_pairwise_disjoint`
- `Body_eq_biUnion_Slab`（あるいは同等の分解定理）
- `card_Body_eq_sum_card_Slab`
- `card_Body_eq_mul_G_constructive`

> ここで choose 係数が「計算係数」ではなく **分類数（分割の数え上げ）** として現れます。

---

## 2D 手本（Cell2 と平面直観）

一般次元の特例として (d=2) を “手本の皮” として整備しています。

- `Cell2 := Cell 2`
- `x2`, `y2`, `mk2`, `mk2_eta`
- `cell2EquivProd : Cell2 ≃ (ℤ × ℤ)`
- 2D 矩形 `Rect2`, `RectAt2` と濃度
- `G_two_dim_eval : G 2 x u = x + 2u`
- `card_Body2_eq_x_mul : card Body = x*(x+2u)`
- `card_Body2_as_two_rects`（L字＝矩形2枚の濃度和）

---

## 研究上の解釈（短いメモ）

- **Gap** は単純な \(u^d\)（余白の不変量）
- **Body** は差として \((x+u)^d-u^d\) だが、必ず \(x\) を因数にもつ
- 幾何和版 \(G\) と choose 版 \(G_{\mathrm{binom}}\) は同値であり、係数は **分類の構造**として理解できる
- Slab 分解により、宇宙式は「差集合の存在」ではなく「分割による構成」へ昇格する

---

## ファイル構成（例）

- `CellDim.lean`：`Cell d`, `translate`, `Box`, `card` 補題群、`Cell2` 整備
- `CosmicFormulaCellDim.lean`：Big/Gap/Body、べき化、\(G\)・\(G_{\mathrm{binom}}\)、Slab 分解、2D 手本

---

## 今後の展望

- **Slab 分解の API 整備**（命名・補題の粒度を固定し再利用性を上げる）
- **2D（トロミノ/図形）側とのリンク強化**（既存平面コードとの往復補題）
- **一般化宇宙式（他の形状、他の分割ルール）** への拡張
- `Nat` 以外（`ℤ`, `ℚ`, `ℝ`）への持ち上げと、解析的道具（生成関数など）との接続

---

## 引用・ライセンス

- MIT License
- 研究利用の場合は、該当する定理名・ファイル名を併記してください

---
