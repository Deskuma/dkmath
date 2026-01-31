# CollatzCartography (collatz_experiment.py)

加速コラッツ写像（奇数上）を対象に、  
「ブロック \(2^k\)（花弁）」という等比区間の中で起きる現象を **ログ化・差分比較・統計化**する実験フレームワークです。

本スクリプトは以下を出力します：

- **軌道ログ**（加速コラッツの各ステップ記録）
- **差分ログ**（同一ブロックオフセット \(+2^k m\) を与えた軌道どうしの比較）
- **統計 JSON**（跳ね上がり・差分顕在化・2冪地形など）

---

## 1. 背景（観測している量）

奇数 \(n\) に対して、加速コラッツ写像を

\[
T(n) := \frac{3n+1}{2^{v_2(3n+1)}} \quad (\text{常に奇数})
\]

と定義し、観測関数

\[
s(n) := v_2(3n+1)
\]

を記録します。

また、ステップ \(m\) に対し

- 部分和 \(\;S_m := \sum_{i=1}^{m} s_i\)
- ドリフト（対数平均からのズレ）  
  \[
  D_m := m\log_2 3 - S_m
  \]
- 途中の最大跳ね上がり（prefix 最大）  
  \[
  \max_{t\le m} D_t
  \]
  （JSON キー: `max_prefix_D`）

をログ・統計として出力します。

---

## 2. 目的（花弁比較＝ブロック比較）

ブロックサイズ \(2^k\) を固定し、基準値 \(n_0\) に対して

\[
n_0' := n_0 + 2^k \cdot m
\]

のような **ブロックオフセット**を与えた軌道を比較します。

比較対象は主に

- \(s\) 列の差分 \(\Delta s_t := s(n'_t) - s(n_t)\)
- 軌道値の差 \(\Delta n_t := n'_t - n_t\)
- その 2 進評価 \(\;v_2(|\Delta n_t|)\)

です。

この差分がいつ（どのステップで）顕在化するか、また「2冪地形」がどう崩れるかを観測します。

---

## 3. 必要環境

- Python 3.x
- NumPy

---

## 4. 実行方法（CLI）

```bash
python collatz_experiment.py --k 8 --max-m 256 --num-bases 32 --output results/
```

### オプション

- `--k` : ブロック指数 (k)（ブロックサイズは (2^k)）
- `--max-m` : 軌道の最大長（最大ステップ数）
- `--num-bases` : 基準奇数 (n_0) の個数（1〜(2^k-1) の奇数から先頭を使用）
- `--output` : 出力ディレクトリ

---

## 5. 出力ファイル

`--output` で指定したディレクトリに以下が作成されます：

- `trajectories_k{k}.json`
  基準軌道ログ（各 (n_0) についてのステップ記録）

- `differences_k{k}.json`
  差分ログ（基準軌道とオフセット軌道の比較）

- `statistics_k{k}.json`
  実験統計（平均・最大・最小など）

---

## 6. JSON 仕様（概要）

### 6.1 trajectories_k{k}.json

各要素は 1 本の軌道ログ：

- `n0`: 初期値（奇数）
- `k`: ブロック指数
- `m`: 実際に記録されたステップ数
- `S_m`: (s) の総和
- `D_m`: ドリフト (D_m)
- `max_prefix_D`: (\max_{t\le m} D_t)
- `segments`: 各ステップの詳細（`n`, `a=3n+1`, `s=v2(a)`, `n_next`）

### 6.2 differences_k{k}.json

各要素は基準 (n_0) とオフセット (n_0 + 2^k m) の比較ログ：

- `n0`, `k`
- `m_shift`: オフセット係数 (m)
- `m`: 比較に用いたステップ数
- `first_delta_index`: (\Delta s \ne 0) が初めて出たステップ（無ければ `null`）
- `singular_indices`: `s_base >= k` となったステップ群
- `max_abs_delta_s`, `min_delta_s`, `sum_delta_s`, `first_delta_value`
- `max_v2_delta_n`: 比較区間内の (v_2(|\Delta n|)) 最大値
- `segments`: 各ステップの比較詳細

  - `delta_s, s_base, s_shifted`
  - `n_base, n_shifted, delta_n, v2_delta_n`
  - `singular_at_base`（`s_base >= k`）

### 6.3 statistics_k{k}.json

代表的なキー：

- 実験条件

  - `k`, `block_size`, `num_trajectories`, `num_difference_logs`, `log2_3`

- ドリフト統計

  - `drift_mean`, `drift_std`, `drift_min`, `drift_max`

- 特異（`s >= k`）の出現位置

  - `first_singular_mean`, `first_singular_median`（存在する場合）

- 差分顕在化

  - `diff_first_delta_mean`, `diff_first_delta_median`, `diff_first_delta_max`（存在する場合）

- 花弁地形（2冪一致度）

  - `v2_delta_n_mean`, `v2_delta_n_max`, `v2_delta_n_min`（存在する場合）

---

## 7. 実験上の注意

- `first_delta_index = null` は「差が永遠に無い」とは限りません。
  比較は有限ステップなので「観測窓内で差が出なかった」ケースを含みます。

- 差分ログは計算量を抑えるため、現在は **基準軌道の一部（先頭数本）**のみに対して作成する設計です。
  （必要なら差分対象を増やす拡張が可能です）

---

## 8. ライセンス

スクリプト先頭のヘッダに従います（例：MIT）。

---
