# Observed Minimum Profile Research Note

## 1. 目的

`DkMath.Samples.LPS.BigFamilyExamples` で観測している

- same Big
- different Body
- different observed minimum profiles

の再現状況を、実験段階の事実確認として逐次記録する。

## 2. 現在の固定結果（Lean）

参照ファイル:

- `DkMath/Samples/LPS/BigFamilyExamples.lean`

主要総括定理:

- `cube_observed_min_split_reproduced_three_samples`

この定理は、`d = 3` において、same Big に対する residual の
observed minimum profile 分岐 (`ObservedMinTwo`, `ObservedMinOne`) が、
少なくとも 3 つの独立標本で再現することを束ねる。

1. `candidateBig = 216`:
   - `216 - 125 = 91` (`ObservedMinTwo 3 91`)
   - `216 - 152 = 64` (`ObservedMinOne 3 64`)
2. `candidateBigCube₂ = 64`:
   - `64 - 29 = 35` (`ObservedMinTwo 3 35`)
   - `64 - 37 = 27` (`ObservedMinOne 3 27`)
3. `candidateBigCube₃ = 125`:
   - `125 - 60 = 65` (`ObservedMinTwo 3 65`)
   - `125 - 61 = 64` (`ObservedMinOne 3 64`)

補足（平方側）:

- `d = 2` でも `candidate_sq_same_big_observed_min_split_profile` により、
   same Big での profile 分岐の実例を 1 標本確認済み。

## 3. 標本生成の原理（短メモ）

立方世界で same Big の profile 分岐標本を作る基本手順は次の通り。

1. Big を固定する。
2. Body を 2 通り選び、residual を `r₂ = a^3 + b^3` 型と `r₁ = c^3` 型へ振り分ける。
3. `r₂` 側で `ObservedMinTwo`（1項不可・2項可）を示し、`r₁` 側で `ObservedMinOne` を示す。
4. これにより same Big の中で observed minimum profile の分岐を観測する。

## 4. 研究メモ（実験段階方針）

- 現段階では `ObservedMinOne/Two` は局所定義のまま維持する。
- 汎用 API (`GapFillRank.lean` への昇格) は、再利用箇所が増えてから判断する。
- 先に標本数を増やし、観測再現性を優先する。

## 5. 現状分析（2026-03-17）

### 5.1. 現在地

- `Samples/LPS` は LPS 本体の証明ではなく、Big-family 語彙で現象を観測する実験層として機能している。
- `BigFamily` / `BigFamilyInt` / `PowerSwap` / `GapFillRank` / `BigFamilyExamples` の役割分担は明確で、相互接続も安定している。

### 5.2. 重要な観測事実

- 立方次数 `d = 3` で、same Big に対する residual の observed minimum profile 分岐
   (`ObservedMinTwo`, `ObservedMinOne`) が独立 3 標本で再現した。
- この事実は `cube_observed_min_split_reproduced_three_samples` で Lean 上に固定されている。
- 平方次数 `d = 2` でも 1 標本の分岐が確認され、現象が立方世界だけの偶然ではない可能性を示す。

### 5.3. 強み

- 語彙統一（Big / Body / Gap / Core / Beam / ObservedMin）により、設計書と実装の対応が追跡しやすい。
- `ℕ` 版と `ℤ` 版の併置により、差分観測の記述自由度が高い。
- `ObservedMinOne/Two` を局所定義に留めたことで、実験段階の仕様変更に耐えやすい。

### 5.4. 未確定点

- `ObservedMin` は現状 `1` と `2` のみで、一般 `r` への拡張方針は未固定。
- 標本は hand-crafted が中心で、系統生成の一般条件はまだ定式化途上。
- LPS 本体予想への論理橋（一般定理レベル）は未整備。

### 5.5. 次の分岐

1. 生成原理を短文化して標本設計の再利用性を上げる。
2. 立方標本を増やして再現性の厚みを上げる。

現時点では、生成原理の短文化を先に行う方が研究ノートとしての密度が高い。

## 6. 生成テンプレ（Lean 定理名対応）

same Big の分岐標本を Lean 側へ固定する際の最小テンプレは次。

1. `candidateBig*`, `candidateBody*₁`, `candidateBody*₂` を定義する。
2. `*_residuals_split` で residual 2 本を数値確定する。
3. 2項側について
   - `*_fill_body₁_exact_two`
   - `*_fill_body₁_not_exact_one`
   を示して `ObservedMinTwo` を作る。
4. 1項側について
   - `*_fill_body₂_exact_one`
   を示して `ObservedMinOne` を作る。
5. 最後に
   - `*_same_big_observed_min_profile`
   - 必要に応じて `*_same_big_observed_min_split_profile`
   を置いて profile 本体と Body 不等号付き版を分離する。

既存の参照実装:

- `candidate_same_big_observed_min_profile`
- `candidate_cube₂_same_big_observed_min_profile`
- `candidate_cube₃_same_big_observed_min_profile`

## 7. 交点地形メモ（profile map）

本ノートで扱う「交点」は、次の 3 層を区別して観測する。

1. PowerSwap 交点: `a^b = b^a`。
2. same Big 交点: Big を固定し Body を変えると residual profile が分岐する点。
3. profile 境界交点: `ObservedMinOne` と `ObservedMinTwo` が切り替わる境界。

実験的に最も有効な可視化は、固定 Big に対する profile map である。

- 固定: `Big = N`
- 変数: `Body = B`
- residual: `r(B) = N - B`
- ラベル:
  - `1` : `ObservedMinOne d r(B)`
  - `2` : `ObservedMinTwo d r(B)`
  - `?` : 未分類

このとき `B ↦ label(r(B))` を一次元に並べると、
「1項島」と「2項島」の散らばりが直接読める。

### 7.1. 固定 Big = 216 の境界表（d = 3）

| Body B | residual r = 216 - B | profile |
|---|---:|---|
| 152 | 64  | ObservedMinOne |
| 125 | 91  | ObservedMinTwo |
| 91  | 125 | ObservedMinOne |
| 181 | 35  | ObservedMinTwo |

この表は、same Big の内部に profile 分岐が島状に現れることを示す
最小の事実確認表として使う。

## 8. 指数法則観点（指数圧縮と反転交点）

本テーマで指数法則を見る目的は、計算簡約そのものではなく、
「どこで世界の切り替えが起きるか」を捉えることにある。

### 8.1. 基本観点

- 圧縮法則: `(a^m)^n = a^(mn)` は、階層的な成長を単段階へまとめ直す操作と読める。
- 反転交点: `a^b = b^a` は、底と指数の役割反転が値の上で不変になる特殊点である。
- 対数観測: `a^b = b^a` は `log a / a = log b / b` へ写り、交点を密度条件として読む視点を与える。

### 8.2. observed minimum との対応仮説（実験段階）

現段階の作業仮説として、次を採用する。

- `ObservedMinOne` は residual が単一冪へ指数圧縮可能な状態に対応する。
- `ObservedMinTwo` は同次数二項和としては表せるが、単一冪へは圧縮不能な状態に対応する。

これは一般定理ではなく、標本観測を整理するための作業仮説である。

### 8.3. 立方3標本の指数圧縮表

| residual | profile | 単一冪への圧縮 | 代表表示 |
|---:|---|---|---|
| 64  | ObservedMinOne | 可 | `4^3 = 2^6 = 8^2` |
| 27  | ObservedMinOne | 可 | `3^3 = 9^(3/2)` |
| 125 | ObservedMinOne | 可 | `5^3` |
| 91  | ObservedMinTwo | 不可（1項立方として） | `3^3 + 4^3` |
| 35  | ObservedMinTwo | 不可（1項立方として） | `2^3 + 3^3` |
| 65  | ObservedMinTwo | 不可（1項立方として） | `1^3 + 4^3` |

この表は、same Big における profile 分岐を
「和として残るか／単核へ圧縮されるか」という観点で読むための最小資料である。

### 8.4. 中心 `e` と双極2解構造（PowerSwap center principle）

`a^b = b^a` を対数化すると

- `b log a = a log b`
- `log a / a = log b / b`

となる。ここで `f(x) = log x / x` を見ると、

- `x < e` で増加
- `x > e` で減少
- `x = e` で最大

の山型を持つため、`f(x) = c`（`c < 1/e`）は一般に左右 2 解を持つ。

この意味で、PowerSwap 非自明解は

- 中心核: `x = e`（左右解が合流する縮退中心）
- 左右花弁: `a < e < b`（同値 `a^b = b^a` を与える双極）

として読むことができる。整数格子点 `2^4 = 4^2` は、この双極構造に現れる
代表的な離散標本である。

## 9. DHNT 動的調和数論観点（連続対称核と格子フィルター）

本節では、PowerSwap と residual profile 分岐を
「連続対称核 → 離散観測」という 2 層構造で捉える。

### 9.1. 連続層（対称核）

- `a^b = b^a` は `log a / a = log b / b` に写る。
- 関数 `f(x) = log x / x` は `x = e` を中心に山型を持つ。
- 非自明解は、中心 `e` を挟む左右 2 解（双極）として現れる。

ここで `e` は、整数特殊値ではなく連続対称性の核とみなす。

### 9.2. 離散層（整数格子フィルター）

- 整数解（例: `2^4 = 4^2`）は、連続対称構造の上に乗った格子観測点と読む。
- すなわち
   `continuous symmetry → integer lattice filter → discrete samples`
   という観測写像を採用する。

### 9.3. residual 層（Big 固定 profile 観測）

- same Big で Body を変える操作は `r = Big - Body` の走査に等しい。
- `ObservedMinOne / ObservedMinTwo` の境界は、
   連続対称地形を格子で切ったときの相切替として解釈できる可能性がある。

### 9.4. 作業仮説（DHNT 観測地図）

本ノートの実験段階仮説として、次を採用する。

1. 連続指数対称の核は `e` 周辺にある。
2. PowerSwap 整数解は、その核の格子断面である。
3. residual profile 分岐は、同じ核を別座標（Big/Body）で見た離散像である。

この仮説は未証明であり、現段階では観測整理のためのガイドとして使う。

## 10. DHNT 基本原理（指数座標と再配分）

本ノートの作業仮説を DHNT 風に再記述すると次になる。

### 10.1. 指数座標化

任意の正実数 `n` を

- `n = e^k`
- `k = log n`

で表し、値 `n` そのものではなく「指数座標 `k`」を一次的観測量として扱う。

### 10.2. 同一値の再配分

同じ `n` は

- `n = e'^k'`
- `n = a^b`

のように複数の底・指数配分で再表示できる。
DHNT 観点では、これを同値式の言い換えに留めず、
「同一値を異なる単位系宇宙で観測した像」とみなす。

### 10.3. 観測器としての対数

`log` は指数表示から単位歩幅を回収する写像として働く。
`DHNT_SimpleDemo.py` の `ln(e^k) = k` は、この観測器の最小実装と解釈できる。

### 10.4. LPS 残差観測との接続（作業仮説）

same Big の下での residual profile 分岐は、
連続指数対称核（`e` を中心とする構造）を整数格子で切った観測像として読める。

- `ObservedMinOne`: 単一冪へ圧縮可能な像
- `ObservedMinTwo`: 同次数和としては表せるが単一冪へ圧縮しにくい像

この接続は未証明であり、現段階では標本整理のための DHNT 作業仮説である。

## 11. 実装計画：指数表示相（Type I–IV）

### 11.1. 目的

固定値 `n` に対して `n = a^b` の表示可能性を
「整数性・無理数性の相」で分類し、
`ObservedMinOne / ObservedMinTwo` との対応を観測可能にする。

### 11.2. 表示相の作業定義

`n > 0` に対し、表示集合

- `R(n) := {(a,b) | n = a^b, a > 0, a ≠ 1, b ∈ ℝ}`

を考え、次を区別する。

- **Type I**: `a, b` がともに整数（`a,b ∈ ℕ`）
- **Type II**: `a` は整数、`b` は無理数（`a ∈ ℕ, b ∉ ℚ`）
- **Type III**: `a` は無理数、`b` は整数（`a ∉ ℚ, b ∈ ℕ`）
- **Type IV**: `a, b` がともに無理数（`a, b ∉ ℚ`）

### 11.3. 段階的タスク

1. **定義固定（ドキュメント）**
   - 本節の Type I–IV を基準語彙として固定する。

2. **標本分類表（手動）**
   - 既存 residual 標本 `64, 91, 35, 27, 65` を Type 観点で整理する。
   - まずは「Type I を持つか / 持たないか」を優先して記録する。

3. **Lean 補助定理（最小）**
   - `Type I` 判定に必要な最小補題を追加する。
   - 例: `64 = 4^3`, `27 = 3^3`, `125 = 5^3`（Type I の実例）
   - 例: `91`, `35`, `65` が 1 項立方でないこと（既存補題の再利用）

4. **Python 補助スクリプト（任意）**
   - 小範囲 `n` について `cube1/cube2/other` と Type I 可否を出力する。
   - `DHNT_SimpleDemo.py` は指数座標観測のデモとして参照し、
     分類スクリプトは別ファイルで分離する。

5. **接続定理（作業仮説の固定）**
    - `ObservedMinOne/Two` を一般 Type I ではなく、
       次数 `d` 固定の圧縮可能性（single `d`-power / two `d`-power）
       として記述する。

### 11.4. 完了条件（実験段階）

- residual 標本（少なくとも既存 6 点）に Type ラベルが付与されている。
- `d = 3` の 3 標本で、profile と Type の対応表が作成済み。
- Lean 側で Type I 実例と 1 項非存在実例が再利用可能な形で参照できる。

### 11.5. 現時点の分類記録（実証データ追加なし）

本段階では、まず「Type I（両整数表示）の有無」を主軸に記録する。
Type II/III/IV は補助情報として扱い、一般化は後段で行う。

| residual `n` | observed profile | Type I（両整数表示） | 記録根拠 |
|---:|---|---|---|
| 64  | ObservedMinOne | あり | `64 = 4^3 = 2^6 = 8^2` |
| 27  | ObservedMinOne | あり | `27 = 3^3` |
| 125 | ObservedMinOne | あり | `125 = 5^3` |
| 91  | ObservedMinTwo | なし（少なくとも1項立方ではない） | `¬ FillableByPowSumExact 3 91 1` |
| 35  | ObservedMinTwo | なし（少なくとも1項立方ではない） | `¬ FillableByPowSumExact 3 35 1` |
| 65  | ObservedMinTwo | なし（少なくとも1項立方ではない） | `¬ FillableByPowSumExact 3 65 1` |

この表は Type I の粗い地図として有用だが、
`16` や `9` のように Type I を持ちながら立方1項ではない数があるため、
`ObservedMinOne/Two` の主境界を直接には与えない。

### 11.6. CSV 観測による仮説更新（Big 固定走査）

`python/LPS/DHNT/experiment_profile_map.py` により、
`Big = 64, 125, 216` で `Body` 全走査を行った集計は次の通り。

| Big | ObservedMinOne-candidate | ObservedMinTwo-candidate | other |
|---:|---:|---:|---:|
| 64  | 5 | 6  | 54  |
| 125 | 6 | 9  | 111 |
| 216 | 7 | 14 | 196 |

この結果から、fixed Big の内部に「1項島」と「2項島」が共存することが再確認された。

#### 仮説の修正版（次数固定）

旧: `ObservedMinOne ↔ Type I`（一般）

新:

- `ObservedMinOne-candidate at degree d`
   ↔ residual が単一 `d` 乗（single `d`-power）
- `ObservedMinTwo-candidate at degree d`
   ↔ residual は単一 `d` 乗ではないが、2項 `d` 乗和で表せる

すなわち主境界は一般 Type I ではなく、
**次数 `d` 固定の圧縮可能性**で記述するのが自然である。

### 11.7. 固定 Big ごとの非 `other` マップ（展開版）

以下は `python/LPS/DHNT/docs/profile_map_big_<big>.csv` から
`profile != other` 行のみを抜粋した表である。

#### Big = 64

| Body | residual | profile | cube2_repr | has_type_i_nontrivial | type_i_repr |
|---:|---:|---|---|---:|---|
| 0 | 64 | ObservedMinOne-candidate | 0^3+4^3 | 1 | 2^6;4^3;8^2 |
| 10 | 54 | ObservedMinTwo-candidate | 3^3+3^3 | 0 |  |
| 29 | 35 | ObservedMinTwo-candidate | 2^3+3^3 | 0 |  |
| 36 | 28 | ObservedMinTwo-candidate | 1^3+3^3 | 0 |  |
| 37 | 27 | ObservedMinOne-candidate | 0^3+3^3 | 1 | 3^3 |
| 48 | 16 | ObservedMinTwo-candidate | 2^3+2^3 | 1 | 2^4;4^2 |
| 55 | 9 | ObservedMinTwo-candidate | 1^3+2^3 | 1 | 3^2 |
| 56 | 8 | ObservedMinOne-candidate | 0^3+2^3 | 1 | 2^3 |
| 62 | 2 | ObservedMinTwo-candidate | 1^3+1^3 | 0 |  |
| 63 | 1 | ObservedMinOne-candidate | 0^3+1^3 | 0 |  |
| 64 | 0 | ObservedMinOne-candidate | 0^3+0^3 | 0 |  |

#### Big = 125

| Body | residual | profile | cube2_repr | has_type_i_nontrivial | type_i_repr |
|---:|---:|---|---|---:|---|
| 0 | 125 | ObservedMinOne-candidate | 0^3+5^3 | 1 | 5^3 |
| 34 | 91 | ObservedMinTwo-candidate | 3^3+4^3 | 0 |  |
| 53 | 72 | ObservedMinTwo-candidate | 2^3+4^3 | 0 |  |
| 60 | 65 | ObservedMinTwo-candidate | 1^3+4^3 | 0 |  |
| 61 | 64 | ObservedMinOne-candidate | 0^3+4^3 | 1 | 2^6;4^3;8^2 |
| 71 | 54 | ObservedMinTwo-candidate | 3^3+3^3 | 0 |  |
| 90 | 35 | ObservedMinTwo-candidate | 2^3+3^3 | 0 |  |
| 97 | 28 | ObservedMinTwo-candidate | 1^3+3^3 | 0 |  |
| 98 | 27 | ObservedMinOne-candidate | 0^3+3^3 | 1 | 3^3 |
| 109 | 16 | ObservedMinTwo-candidate | 2^3+2^3 | 1 | 2^4;4^2 |
| 116 | 9 | ObservedMinTwo-candidate | 1^3+2^3 | 1 | 3^2 |
| 117 | 8 | ObservedMinOne-candidate | 0^3+2^3 | 1 | 2^3 |
| 123 | 2 | ObservedMinTwo-candidate | 1^3+1^3 | 0 |  |
| 124 | 1 | ObservedMinOne-candidate | 0^3+1^3 | 0 |  |
| 125 | 0 | ObservedMinOne-candidate | 0^3+0^3 | 0 |  |

#### Big = 216

| Body | residual | profile | cube2_repr | has_type_i_nontrivial | type_i_repr |
|---:|---:|---|---|---:|---|
| 0 | 216 | ObservedMinOne-candidate | 0^3+6^3 | 1 | 6^3 |
| 27 | 189 | ObservedMinTwo-candidate | 4^3+5^3 | 0 |  |
| 64 | 152 | ObservedMinTwo-candidate | 3^3+5^3 | 0 |  |
| 83 | 133 | ObservedMinTwo-candidate | 2^3+5^3 | 0 |  |
| 88 | 128 | ObservedMinTwo-candidate | 4^3+4^3 | 1 | 2^7 |
| 90 | 126 | ObservedMinTwo-candidate | 1^3+5^3 | 0 |  |
| 91 | 125 | ObservedMinOne-candidate | 0^3+5^3 | 1 | 5^3 |
| 125 | 91 | ObservedMinTwo-candidate | 3^3+4^3 | 0 |  |
| 144 | 72 | ObservedMinTwo-candidate | 2^3+4^3 | 0 |  |
| 151 | 65 | ObservedMinTwo-candidate | 1^3+4^3 | 0 |  |
| 152 | 64 | ObservedMinOne-candidate | 0^3+4^3 | 1 | 2^6;4^3;8^2 |
| 162 | 54 | ObservedMinTwo-candidate | 3^3+3^3 | 0 |  |
| 181 | 35 | ObservedMinTwo-candidate | 2^3+3^3 | 0 |  |
| 188 | 28 | ObservedMinTwo-candidate | 1^3+3^3 | 0 |  |
| 189 | 27 | ObservedMinOne-candidate | 0^3+3^3 | 1 | 3^3 |
| 200 | 16 | ObservedMinTwo-candidate | 2^3+2^3 | 1 | 2^4;4^2 |
| 207 | 9 | ObservedMinTwo-candidate | 1^3+2^3 | 1 | 3^2 |
| 208 | 8 | ObservedMinOne-candidate | 0^3+2^3 | 1 | 2^3 |
| 214 | 2 | ObservedMinTwo-candidate | 1^3+1^3 | 0 |  |
| 215 | 1 | ObservedMinOne-candidate | 0^3+1^3 | 0 |  |
| 216 | 0 | ObservedMinOne-candidate | 0^3+0^3 | 0 |  |

この展開版により、fixed Big の中で profile 島がどの Body 座標に出るかを
直接比較できる。

### 11.8. 境界縮約表（One↔Two 切替点のみ）

定義（本ノートの縮約規則）:

- fixed Big の `profile != other` 行を Body 昇順で並べる。
- 連続する2行で profile が異なるとき、そのペアを「境界切替点」と記録する。

#### Big = 64

| from (Body,residual,profile) | to (Body,residual,profile) | ΔBody | Δresidual |
|---|---|---:|---:|
| (0, 64, One) | (10, 54, Two) | 10 | -10 |
| (36, 28, Two) | (37, 27, One) | 1 | -1 |
| (37, 27, One) | (48, 16, Two) | 11 | -11 |
| (55, 9, Two) | (56, 8, One) | 1 | -1 |
| (56, 8, One) | (62, 2, Two) | 6 | -6 |
| (62, 2, Two) | (63, 1, One) | 1 | -1 |

#### Big = 125

| from (Body,residual,profile) | to (Body,residual,profile) | ΔBody | Δresidual |
|---|---|---:|---:|
| (0, 125, One) | (34, 91, Two) | 34 | -34 |
| (60, 65, Two) | (61, 64, One) | 1 | -1 |
| (61, 64, One) | (71, 54, Two) | 10 | -10 |
| (97, 28, Two) | (98, 27, One) | 1 | -1 |
| (98, 27, One) | (109, 16, Two) | 11 | -11 |
| (116, 9, Two) | (117, 8, One) | 1 | -1 |
| (117, 8, One) | (123, 2, Two) | 6 | -6 |
| (123, 2, Two) | (124, 1, One) | 1 | -1 |

#### Big = 216

| from (Body,residual,profile) | to (Body,residual,profile) | ΔBody | Δresidual |
|---|---|---:|---:|
| (0, 216, One) | (27, 189, Two) | 27 | -27 |
| (90, 126, Two) | (91, 125, One) | 1 | -1 |
| (91, 125, One) | (125, 91, Two) | 34 | -34 |
| (151, 65, Two) | (152, 64, One) | 1 | -1 |
| (152, 64, One) | (162, 54, Two) | 10 | -10 |
| (188, 28, Two) | (189, 27, One) | 1 | -1 |
| (189, 27, One) | (200, 16, Two) | 11 | -11 |
| (207, 9, Two) | (208, 8, One) | 1 | -1 |
| (208, 8, One) | (214, 2, Two) | 6 | -6 |
| (214, 2, Two) | (215, 1, One) | 1 | -1 |

#### Big = 343

| from (Body,residual,profile) | to (Body,residual,profile) | ΔBody | Δresidual |
|---|---|---:|---:|
| (0, 343, One) | (2, 341, Two) | 2 | -2 |
| (126, 217, Two) | (127, 216, One) | 1 | -1 |
| (127, 216, One) | (154, 189, Two) | 27 | -27 |
| (217, 126, Two) | (218, 125, One) | 1 | -1 |
| (218, 125, One) | (252, 91, Two) | 34 | -34 |
| (278, 65, Two) | (279, 64, One) | 1 | -1 |
| (279, 64, One) | (289, 54, Two) | 10 | -10 |
| (315, 28, Two) | (316, 27, One) | 1 | -1 |
| (316, 27, One) | (327, 16, Two) | 11 | -11 |
| (334, 9, Two) | (335, 8, One) | 1 | -1 |
| (335, 8, One) | (341, 2, Two) | 6 | -6 |
| (341, 2, Two) | (342, 1, One) | 1 | -1 |

#### Big = 512

| from (Body,residual,profile) | to (Body,residual,profile) | ΔBody | Δresidual |
|---|---|---:|---:|
| (0, 512, One) | (44, 468, Two) | 44 | -44 |
| (168, 344, Two) | (169, 343, One) | 1 | -1 |
| (169, 343, One) | (171, 341, Two) | 2 | -2 |
| (295, 217, Two) | (296, 216, One) | 1 | -1 |
| (296, 216, One) | (323, 189, Two) | 27 | -27 |
| (386, 126, Two) | (387, 125, One) | 1 | -1 |
| (387, 125, One) | (421, 91, Two) | 34 | -34 |
| (447, 65, Two) | (448, 64, One) | 1 | -1 |
| (448, 64, One) | (458, 54, Two) | 10 | -10 |
| (484, 28, Two) | (485, 27, One) | 1 | -1 |
| (485, 27, One) | (496, 16, Two) | 11 | -11 |
| (503, 9, Two) | (504, 8, One) | 1 | -1 |
| (504, 8, One) | (510, 2, Two) | 6 | -6 |
| (510, 2, Two) | (511, 1, One) | 1 | -1 |

#### Big = 729

| from (Body,residual,profile) | to (Body,residual,profile) | ΔBody | Δresidual |
|---|---|---:|---:|
| (0, 729, One) | (1, 728, Two) | 1 | -1 |
| (216, 513, Two) | (217, 512, One) | 1 | -1 |
| (217, 512, One) | (261, 468, Two) | 44 | -44 |
| (385, 344, Two) | (386, 343, One) | 1 | -1 |
| (386, 343, One) | (388, 341, Two) | 2 | -2 |
| (512, 217, Two) | (513, 216, One) | 1 | -1 |
| (513, 216, One) | (540, 189, Two) | 27 | -27 |
| (603, 126, Two) | (604, 125, One) | 1 | -1 |
| (604, 125, One) | (638, 91, Two) | 34 | -34 |
| (664, 65, Two) | (665, 64, One) | 1 | -1 |
| (665, 64, One) | (675, 54, Two) | 10 | -10 |
| (701, 28, Two) | (702, 27, One) | 1 | -1 |
| (702, 27, One) | (713, 16, Two) | 11 | -11 |
| (720, 9, Two) | (721, 8, One) | 1 | -1 |
| (721, 8, One) | (727, 2, Two) | 6 | -6 |
| (727, 2, Two) | (728, 1, One) | 1 | -1 |

この縮約表により、profile 地形の「島の位置」だけでなく
「切替境界の座標と間隔」を比較可能にする。

補足観測:

- 定義上 `residual = Big - Body` なので、各切替で常に `Δresidual = -ΔBody`。
- `Big = 27..729`（立方列）での `ΔBody` 頻度は次の通り。

| ΔBody | 出現回数 |
|---:|---:|
| 1  | 36 |
| 2  | 3  |
| 6  | 7  |
| 10 | 6  |
| 11 | 7  |
| 27 | 4  |
| 34 | 5  |
| 44 | 2  |

この頻度表により、境界間隔の反復候補を定量的に追跡できる。

### 11.9. 観測領域の拡大（`Big = m^3`, `m=3..9`）

`python/LPS/DHNT/docs/profile_map_summary.csv` に基づき、
立方世界 `d = 3` の fixed Big 観測を `27..729` まで拡大した。

| Big (=m^3) | One-candidate | Two-candidate | other |
|---:|---:|---:|---:|
| 27  | 4  | 3  | 21  |
| 64  | 5  | 6  | 54  |
| 125 | 6  | 9  | 111 |
| 216 | 7  | 14 | 196 |
| 343 | 8  | 20 | 316 |
| 512 | 9  | 26 | 478 |
| 729 | 10 | 34 | 686 |

観測上の要点は次。

1. `ObservedMinOne-candidate` は `Big = m^3` に対して概ね `m+1` 個で増加する。
   これは residual の単一立方列 `0^3..m^3` に対応する。
2. `ObservedMinTwo-candidate` は One 側より速く増加し、
   fixed Big の内部で「二立方和の島」が系統的に増殖する。
3. 境界の主判定は一般 Type I の有無ではなく、
   次数 `d=3` 固定での単一立方圧縮可否にある。
   （例: `16`, `9` は Type I を持つが One ではなく Two 側に現れる。）

この拡大観測により、
「same Big で profile が分岐する」現象は局所標本ではなく、
立方世界の地形的特徴として再現的に現れることが確認された。

### 11.10. `ΔBody` 初出表（境界増殖の段階性）

`Big = m^3` を `27 → 64 → 125 → 216 → 343 → 512 → 729` の順に見たとき、
境界間隔 `ΔBody` の初出は次の通り。

| Big | その Big で観測された `ΔBody` | 初出 `ΔBody` | 累積 `ΔBody` |
|---:|---|---|---|
| 27  | {1, 6, 11} | {1, 6, 11} | {1, 6, 11} |
| 64  | {1, 6, 10, 11} | {10} | {1, 6, 10, 11} |
| 125 | {1, 6, 10, 11, 34} | {34} | {1, 6, 10, 11, 34} |
| 216 | {1, 6, 10, 11, 27, 34} | {27} | {1, 6, 10, 11, 27, 34} |
| 343 | {1, 2, 6, 10, 11, 27, 34} | {2} | {1, 2, 6, 10, 11, 27, 34} |
| 512 | {1, 2, 6, 10, 11, 27, 34, 44} | {44} | {1, 2, 6, 10, 11, 27, 34, 44} |
| 729 | {1, 2, 6, 10, 11, 27, 34, 44} | ∅ | {1, 2, 6, 10, 11, 27, 34, 44} |

観測メモ:

- 境界間隔の候補集合は `Big` の増加とともに段階的に拡張し、`Big=729` 時点で一旦飽和している。
- 初出系列は `{1,6,11} → +10 → +34 → +27 → +2 → +44` の順で現れ、
   増殖則の候補として追跡対象になる。

## 12. 追記テンプレート

### yyyy-mm-dd: new sample

- degree:
- Big:
- Body pair:
- residual pair:
- Lean theorem name:
- note:
