# Codex 実装指示書 — CF2D の代数的二分回転から内在的 π を構成する

## Mission

DkMath の `DkMath.CosmicFormula.Rotation.CF2D` を拡張し、π を直接参照しない単位核の反復・面積数列から `intrinsicPi` を構成する。その後、別ファイルでのみ Mathlib の `Real.pi` と一致させる。**数学的に正しく、Lean 4 / Mathlib でビルドが通る実装** とする。研究背景・厳密な数式は同梱の `CF2D_IntrinsicPi_Research.md` を必ず先に読むこと。

このタスクは「πが新しく発見された」と主張するものではない。DkMath の **純代数→対称性の二分割→多角形の正規化面積→極限→既知πとの比較** を形式化する。

## 1. 最初に調査すること

1. 現在の `main` と手元の作業ツリーの差分を確認。既存のユーザー変更を上書きしない。
2. `lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D.lean` と配下 `Basic`, `Trig`, `CFSinCos`, `KernelPower`, `CycleDivision`, `RegularOrbit`, `EuclideanRegularOrbit`, `EuclideanPhase`, `Topology`, `Real` を読む。
3. `DkMath/Analysis/DkReal/SemanticCF2DNormalize.lean` の連続経路実装を調べ、既存定理を再利用できるところは再利用する。
4. `lakefile.*`、`lean-toolchain`、使用 Mathlib 版を調べて、実際に使える補題名を `#check` / grep / Mathlib ソースで確認する。架空の補題名を前提にしない。
5. 現在の CF2D には、代数核にπ不要な部分と `Real.pi` を使う標準実数・ユークリッドの bridge 部分がある。この分離を保つ。

## 2. 実装ファイル・依存方向

推奨する新規ファイル:

```text
DkMath/CosmicFormula/Rotation/CF2D/
├── HalfKernel.lean          -- π-free: quadrant unit kernel と平方根による二分回転
├── IntrinsicPolygon.lean    -- π-free: Aₙ, Pₙ, 代数関係、単調性、有界性
├── IntrinsicPi.lean         -- π-free: sSup による内在的 Π と収束
└── IntrinsicPiBridge.lean   -- 比較層: Real.pi、標準sin/cosとの一致
```

短い実装が望ましい場合は `IntrinsicPolygon` を `IntrinsicPi` に統合してもよい。`CF2D.lean` は完成モジュールを依存順に `import` する。循環 import を作らない。

**厳守**: 最初の3ファイルの定義と定理本文で `Real.pi`, `Real.sin`, `Real.cos`, `Real.arcsin`, `Real.arccos` を使わない。`CycleDivision` の実数正規化部や `EuclideanPhase` を intrinsic 層から import しない。`Mathlib` の一般的な平方根・順序・完備性・位相 API は利用可。`Real.pi` は bridge でのみ使用する。`#print axioms` をチェックする。

## 3. Phase 1 — `HalfKernel.lean`（必須）

`UnitKernel ℝ` から **第一象限の証明** (`0 ≤ core`, `0 ≤ beam`) を含む型／structure／subtype を定義する。以下は数式仕様であり、Lean の具体的な API は既存の `UnitKernel`, `Vec` に合わせて設計する。

- 基本核 `u₀=(0,1)`, `q2(u₀)=1`。
- `u=(c,s)`, `q2(u)=1`, `c≥0`, `s≥0` に対する非負の二分核:

  \[
  h(u)=\left(\sqrt{\frac{1+c}{2}},\sqrt{\frac{1-c}{2}}\right).
  \]

- `q2(h(u))=1`, `h(u)⋆h(u)=u` を Lean で証明。後者では `s≥0` を使って平方根の符号を確定する（負の枝を混同しない）。
- `u : ℕ → QuadrantUnitKernel` を `u 0=u₀`, `u(n+1)=h(u n)` で定義。全 n で `q2=1` と `u(n+1)⋆u(n+1)=u n` を証明。
- 余裕があれば `0≤cₙ≤1`, `0<sₙ≤1`, `cₙ≤cₙ₊₁`, `sₙ₊₁≤sₙ`, `cₙ→1`, `sₙ→0` を示す。

**実装上の注意**: `u_{n+1}^2=u_n` を一般の `UnitKernel` の平方根と誤認しないこと。非負の座標を選ぶ第一象限制約が本質。座標演算は `Real.sqrt`, `sq_sqrt`, `mul_self_sqrt` など実際の Mathlib にある補題を探索する。

## 4. Phase 2 — `IntrinsicPolygon.lean`（必須）

`cₙ=(u n).core`, `sₙ=(u n).beam` とし、次を **πに依存しない実数式** として定義する。

\[
A_n=2^{n+1}s_n,
\qquad
P_n=2^{n+1}\sqrt{2-2c_n}.
\]

- `areaApprox : ℕ → ℝ` と `halfPerimeterApprox : ℕ → ℝ` の定義。
- `areaApprox 0 = 2`, `areaApprox 1 = 2 * Real.sqrt 2`, `halfPerimeterApprox 0 = 2 * Real.sqrt 2`。
- **必須核心定理**:

  \[
  \boxed{P_n=A_{n+1}}
  \]

  これは `sₙ₊₁=√((1-cₙ)/2)` と `2^{n+1}` の指数演算の恒等式から直接導出可能。πは不要。
- **必須** `A_n = c_{n+1} A_{n+1}` と `Monotone areaApprox`。
- **次の優先課題** π-free の上界。たとえば外接候補 `outerApprox n = areaApprox(n+1)/c_(n+1)` を導入し、`outerApprox 0=4`、単調減少を示して `A_n≤4` を得る。よりシンプルな **純代数** 上界があればそれを採用してよい。上界が未解決でも定義や他の証明は `sorry` で隠さず、到達範囲だけをコミットする。

`A_n` / `P_n` が実際に多角形の面積・半周長であることは、この段階では **数式の幾何学的解釈** にとどめ、定義名で「既に幾何面積と同一と証明済み」と誤解させないこと。

## 5. Phase 3 — `IntrinsicPi.lean`（重要）

`areaApprox` の単調非減少・上界を π-free に証明した後、

```lean
-- 概念仕様。namespace と補題は手元の実装に合わせる。
noncomputable def intrinsicPi : ℝ :=
  sSup (Set.range areaApprox)
```

のように定義する。

必須の定理候補: `areaApprox_le_intrinsicPi`, `tendsto_areaApprox_intrinsicPi`, `intrinsicPi_pos`, `intrinsicPi_le_four`（4上界が成立した場合）。

`Real.pi` を使って `areaApprox` を有界にするのは、この層では **禁止**。そうすると「πから独立した存在証明」という研究目的が崩れる。完備性の利用は可能。証明不能のときは、何が不足かを報告し、証明済み範囲を残す。

## 6. Phase 4 — `IntrinsicPiBridge.lean`（最終目標）

このファイルでのみ既存の実数解析・`Real.pi` を使用する。

1. `u_n` を、角度 `Real.pi / 2^(n+1)` の `Real.cos`・`Real.sin` と同一視する（n=0で `(0,1)`、帰納段階で非負の半角公式）。
2. `areaApprox n = 2^(n+1) * Real.sin (Real.pi / 2^(n+1))` を証明。
3. `x_n=Real.pi/2^(n+1)` が0へ収束し、`Real.sin x / x→1` から `areaApprox n → Real.pi` を証明。
4. `tendsto_areaApprox_intrinsicPi` と極限の一意性から

   ```lean
   theorem intrinsicPi_eq_real_pi : intrinsicPi = Real.pi := ...
   ```

   を完成する。

この最後の定理を作れない場合、絶対に `sorry`、`admit`、独自 `axiom` などで成功扱いしない。未完成箇所を単独の説明として残し、他のファイルがビルド可能な状態で作業を終了する。

## 7. Phase 5 — 幾何・位相への拡張（任意、別PR候補）

- `CF2D.RegularOrbit` の頂点に線分を結んだ正多角形を構成し、`A_n` / `P_n` がその実際の面積・半周長であると証明。
- 角度二分割で得る全頂点集合の単位円上での稠密性を証明。**有限軌道は円全体ではない**。
- `SemanticCF2DNormalize` の閉路と単位円の一周（全射性、必要なら巻き数）を照合する。
- GeoGebra の `白銀円とπ` 図に現れる45°・22.5°や鏡映を、独立した例題として定理化する。

これらが Phase 1–4 を邪魔しないよう、優先順位を守ること。

## 8. 絶対に守る品質条件

- 既存ファイルの意味論・型名・補題名は勝手に破壊しない。既存のユーザー作業を消さない。
- `sorry` / `admit` / 新たな `axiom` / 数値浮動小数点での「証明」を禁止。
- `native_decide` や `decide` を非計算的な実数等式の代わりに濫用しない。
- import の循環、巨大な `import CF2D` の再帰参照を避ける。
- 既存定理を優先利用。実際の Mathlib の定理名を確認し、小さな補題に分割。
- `#print axioms` で、意図しない追加公理がないことを確認する。標準的な `[propext, Classical.choice, Quot.sound]` 程度の依存は許容。
- 正規化された有限軌道の性質から、勝手に「円周全体の全射性」「新規 π 公式」「位相だけで π 決定」を結論しない。
- 可能なら各 Phase 完了後に個別ファイルの `lake env lean` / `lake build` を実行し、最後に集約ファイルもビルドする。

## 9. 実行コマンドの例

```bash
cd lean/dk_math
lake env lean DkMath/CosmicFormula/Rotation/CF2D/HalfKernel.lean
lake env lean DkMath/CosmicFormula/Rotation/CF2D/IntrinsicPolygon.lean
lake env lean DkMath/CosmicFormula/Rotation/CF2D/IntrinsicPi.lean
lake env lean DkMath/CosmicFormula/Rotation/CF2D/IntrinsicPiBridge.lean
lake build DkMath.CosmicFormula.Rotation.CF2D
```

実際の `lake` 設定・CLI 用法・ビルド負荷を確認し、必要なら既存のローカルビルドワークフローに合わせる。大規模再ビルドを無闇に起こさない。

## 10. 最終報告の必須内容

次の順に日本語で報告する。

1. 追加・変更したファイルと差分の概要。
2. **証明できた定理**: 正確な Lean 名と型。
3. **まだ証明していない命題**: 特に上界、`intrinsicPi = Real.pi`、幾何学的面積対応。
4. `Real.pi` / `Real.sin` / `Real.cos` が intrinsic 層に混入していないかの検査結果。
5. 実行したコマンド・ビルドの成否・エラーログ要旨。
6. 主要定理の `#print axioms` 結果。
7. 次に必要な補題、最短の実装ステップ。

**完成の判定**: Phase 1–2 が緑なら価値のある中間成果。Phase 3 が緑なら π-free の独立した定数が構成できた成果。Phase 4 まで緑なら `intrinsicPi = Real.pi` の形式化が完成。未達成の段階は明確に未達成と記すこと。

## 11. 開始指示

まず調査結果と具体的なファイル設計を短く提示し、そのまま Phase 1 から実装を開始する。**不要な確認待ちで停止せず**、今のリポジトリ・Lean バージョンで実行できる最小の証明を積み上げる。各段階で実際に型検査し、行き詰まったら `sorry` で覆わず補題の分割や証明方法を変える。スコープを越えた改修はしない。
