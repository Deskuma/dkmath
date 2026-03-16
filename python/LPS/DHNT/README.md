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
```

出力先（デフォルト）:

- `python/LPS/DHNT/docs/profile_map_big_<big>.csv`

### 2.3. 主なオプション

- `--big`（必須）: 固定する Big 値
- `--body-start` / `--body-end`: Body 走査範囲（既定は `0..big`）
- `--max-base`: 2項立方和探索の上限基底
- `--output`: 出力 CSV パス
