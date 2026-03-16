# LPS: Lander, Parkin, and Selfridge conjecture and DHNT - Dynamic Harmonic Number Theory

This directory contains samples related to the Lander, Parkin, and Selfridge conjecture (LPS) and its connection to Dynamic Harmonic Number Theory (DHNT).

## 1. LPS と DHNT の接続

指数法則の数値実験室
see: [Exponent Type Mapping](../../../lean/dk_math/DkMath/Samples/LPS/docs/ExponentTypeMapping.md)

## 2. 数値実験（CSV 出力）

`/python/LPS/DHNT` では、fixed Big 観測を CSV へ吐き出して蓄積する。

スクリプト:

- `experiment_profile_map.py`

### 2.1. できること

- `Big` を固定して `Body` を走査
- `residual = Big - Body` を計算
- `residual` を次で分類
  - `cube1`（単一立方）
  - `cube2`（2項立方和）
  - `other`
- あわせて Type I（非自明な整数冪表示）可否を記録
- 結果を CSV で保存

### 2.2. 実行例

```bash
cd python/LPS/DHNT
python experiment_profile_map.py --big 216
python experiment_profile_map.py --big 64
python experiment_profile_map.py --big 125

# 立方 Big 列（m=3..9）を一括走査して集計も出力
python experiment_profile_map.py \
 --cube-m-start 3 --cube-m-end 9 \
 --emit-summary --emit-non-other --emit-boundary
```

出力先（デフォルト）:

- `python/LPS/DHNT/docs/profile_map_big_<big>.csv`

### 2.3. 主なオプション

- `--big`: 固定する Big 値
- `--big-list`: 複数 Big をカンマ区切り指定（例: `27,64,125,216`）
- `--cube-m-start` / `--cube-m-end`: `Big = m^3` 列の一括走査
- `--body-start` / `--body-end`: Body 走査範囲（既定は `0..big`）
- `--max-base`: 2項立方和探索の上限基底
- `--output`: 単一 `--big` 実行時の出力 CSV パス
- `--output-dir`: 一括実行時の出力先ディレクトリ（既定 `./docs`）
- `--emit-summary`: `profile_map_summary.csv` を出力
- `--emit-non-other`: `profile_map_non_other.csv` を出力
- `--emit-boundary`: `profile_map_boundary_switches.csv` を出力

### 2.4. 観測領域拡大の推奨コマンド

```bash
cd python/LPS/DHNT
python experiment_profile_map.py \
 --cube-m-start 3 --cube-m-end 9 \
 --emit-summary --emit-non-other --emit-boundary
```

主な成果物:

- `docs/profile_map_big_<big>.csv`
- `docs/profile_map_summary.csv`
- `docs/profile_map_non_other.csv`
- `docs/profile_map_boundary_switches.csv`
