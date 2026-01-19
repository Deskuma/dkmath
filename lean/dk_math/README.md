# dk_math

## 概要

- dk_math は、Lean 4 用の数学ライブラリであり、特に動的調和数論（Dynamic Harmonic Number Theory, DHNT）に焦点を当てています。
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

- 動的調和数論 (DHNT) 主要ファイル一覧
  - Dynamic Harmonic Number Theory: [DHNT](./DkMath/DHNT.lean)
  - 宇宙式 [CosmicFormula](./DkMath/CosmicFormula.lean)
    - 線形代数版 [CosmicFormulaLinear](./DkMath/CosmicFormulaLinear.lean)
    - ジオメトリ（有限集合）版 [CosmicFormulaGeom](./DkMath/CosmicFormulaGeom.lean)
    - 次元版 [CosmicFormulaDim](./DkMath/CosmicFormulaDim.lean)
  - トロミノ構造 [Tromino](./DkMath/Tromino.lean)
  - 宇宙式とトロミノ構造の接続定理 [CosmicFormulaTrominoLink](./DkMath/CosmicFormulaTrominoLink.lean)
- 基本定義とユーティリティ [Basic](./DkMath/Basic.lean)
- サンプル定理と例 [Samples](./DkMath/Samples.lean)

## GitHub の設定

新しい GitHub リポジトリをセットアップするには、以下の手順に従ってください。

- リポジトリ名の下にある **Settings（設定）** をクリックします。
- サイドバーの **Actions** セクションで「General（一般）」をクリックします。
- **Allow GitHub Actions to create and approve pull requests（GitHub Actions がプルリクエストを作成・承認できるようにする）** のチェックボックスをオンにします。
- 設定サイドバーの **Pages** セクションをクリックします。
- **Source（ソース）** のドロップダウンメニューで「GitHub Actions」を選択します。

上記の手順が完了したら、このセクションは README ファイルから削除して構いません。
