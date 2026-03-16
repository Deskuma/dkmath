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

## 9. 追記テンプレート

### yyyy-mm-dd: new sample

- degree:
- Big:
- Body pair:
- residual pair:
- Lean theorem name:
- note:
