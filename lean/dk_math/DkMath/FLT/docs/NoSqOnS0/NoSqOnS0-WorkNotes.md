# No Square on S0 Work Notes

## 状況

具体策の構築作業

現状からは次の5手が最短です。

1. [x] `hS0_not_sq` を分離定義

   - `lean/dk_math/DkMath/FLT/Main.lean` から仮定を直接持つ形を維持しつつ、
   - 新規 `NoSqOnS0` を `lean/dk_math/DkMath/FLT/PetalDetect.lean` か新規 `lean/dk_math/DkMath/FLT/PhaseLift.lean` に定義。

2. [x] ブリッジ補題を作る

   - `NoSqOnS0 -> hS0_not_sq` の変換補題を追加。
   - これで「仮定の供給源」を差し替え可能にする。

3. [x] `OctagonCore` を判定器の入口にする

   - `lean/dk_math/DkMath/FLT/OctagonCore.lean` に、点集合から得る位相ラベル（`sqrt2` 系/`sqrt3` 系）を返す定義を追加。
   - まずは「座標核→ラベル」の純代数化だけ実装。

    ```note
    最小実装としてはこの3点が安全です。

    1. `OctagonCore` に判定用ラベル型を追加
    - 例: `inductive PhaseLabel | sqrt2 | sqrt3 | mixed`

    2. 点からラベルを返す入口定義を追加
    - まずは座標で固定された点（`A..I`）に対して、決め打ちマップでよい

    3. `PhaseLift` 側が使える述語を1つ用意
    - 例: `isMixedPhasePoint : Point2 → Prop`

    これで「幾何核 → 判定器入口」の配線ができます。
    ```

4. [ ] 反例抽出器を作る

   - 新規 `lean/dk_math/DkMath/FLT/CounterexamplePattern.lean` を作り、
   - 入力 `(c,b,q)` から `lift可能/不可能` を判定する述語を定義（証明は後段）。

5. [ ] `Main` 接続

   - `lean/dk_math/DkMath/FLT/Main.lean` で `hS0_not_sq` を直接受ける版を残し、
   - 追加で「判定器経由版」定理を並列実装して置換準備。

この順で進めれば、理論議論を壊さずに「実装可能な判定パイプライン」に落とせます。
次は 1〜2 を私が実装して差分を出します。

## 2026-02-23 作業ログ（現時点まとめ）

### 1. 現状把握

- `DkMath.FLT.Main` はビルド成功。
- `FLT_d3_by_padicValNat` は成立済み（ただし `hS0_not_sq` を外部仮定として受ける構成）。
- ボトルネックは「`hS0_not_sq` の供給源」をどう内部化するか。

### 2. 追加・変更した実装

#### 2.1 新規ファイル

- `lean/dk_math/DkMath/FLT/OctagonCore.lean`
  - 標準配置点 `A,B,C,D,E,F,G,O,I` を定義。
  - 基本恒等式を追加：
    - `(1 + sqrt 2) * (sqrt 2 - 1) = 1`
    - `AI` の傾き恒等式（座標式）
  - `lake build DkMath.FLT.OctagonCore` 成功。

- `lean/dk_math/DkMath/FLT/PhaseLift.lean`
  - `NoSqOnS0 (c b : ℕ) : Prop` を定義。
  - ブリッジ前段補題：
    - `prime_dvd_S0_of_dvd_cube_sub_not_dvd_diff`
      - `q ∣ (c^3 - b^3)` かつ `¬ q ∣ (c - b)` から `q ∣ S0_nat c b` を導出。
  - ブリッジ補題：
    - `hS0_not_sq_of_NoSqOnS0`
      - `NoSqOnS0` から `Main` 側で使う `hS0_not_sq` 形へ接続。

#### 2.2 既存ファイル更新

- `lean/dk_math/DkMath/FLT/Main.lean`
  - `import DkMath.FLT.OctagonCore`
  - `import DkMath.FLT.PhaseLift`
  - 派生定理を追加：
    - `FLT_d3_by_padicValNat_of_NoSqOnS0`
      - 既存の `FLT_d3_by_padicValNat` を `NoSqOnS0` 入力で利用できる版。

### 3. ビルド検証結果

- `lake build DkMath.FLT.OctagonCore` : 成功
- `lake build DkMath.FLT.Main` : 成功
- 既存警告（他モジュールの `sorry` 由来）は従来通り残存。

### 4. 到達点（今回）

- `hS0_not_sq` を「直接仮定」するだけでなく、
  `NoSqOnS0` を供給源として差し替え可能な構造にできた。
- 今後は `NoSqOnS0` をどこから構築するか（位相条件・最小反例条件・幾何ラベル連携）に集中できる。

### 5. 次の候補タスク

1. `NoSqOnS0` の十分条件を段階化（仮定セットを小分けに定義）。
2. `PhaseLift.lean` に「lift 可否」述語を追加して、`NoSqOnS0` との関係補題を増やす。
3. `OctagonCore.lean` から位相ラベル（sqrt2/sqrt3 系）の入口定義を追加。

---

## 運用メモ（認識合わせ）

- 以後、作業後にこの種のログを docs 側へ追記して残す運用で進める。
- 候補：
  - このファイルを継続利用（時系列追記）
  - もしくは日付別ログを分割（必要になったら切替）


## 2026-02-23 追記（Step 3: OctagonCore を判定器入口に接続）

### 実施内容
- `lean/dk_math/DkMath/FLT/OctagonCore.lean`
  - `PhaseLabel` を追加：`sqrt2 | sqrt3 | mixed | unknown`
  - 入口関数 `phaseLabelOfPoint : Point2 → PhaseLabel` を追加
    - まず `I` を `mixed` 判定
    - 次に `E/F/G` を `sqrt2` 判定
    - それ以外 `unknown`
  - 入口述語 `isMixedPhasePoint : Point2 → Prop` を追加
  - 補題追加：
    - `phaseLabel_I : phaseLabelOfPoint I = PhaseLabel.mixed`
    - `mixedPoint_I : isMixedPhasePoint I`

- `lean/dk_math/DkMath/FLT/PhaseLift.lean`
  - `import DkMath.FLT.OctagonCore` を追加
  - 判定器フック述語を追加：
    - `HasMixedPhaseWitness : Prop := ∃ p : Point2, isMixedPhasePoint p`
    - `hasMixedPhaseWitness_octagonCore : HasMixedPhaseWitness`

### 検証
- `lake build DkMath.FLT.OctagonCore` 成功
- `lake build DkMath.FLT.Main` 成功

### チェック更新
- [x] 3. `OctagonCore` を判定器の入口にする
