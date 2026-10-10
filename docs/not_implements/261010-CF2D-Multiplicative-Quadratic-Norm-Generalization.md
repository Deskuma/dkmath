# CF2D 乗法的二次形式・整数格子・合成代数への一般化 — 実装構想

- 起案: 2026-10-10
- Status: PROPOSED / NOT IMPLEMENTED（本書の新規一般化部分）
- Scope: DkMath / CosmicFormula / Rotation / CF2D / algebraic norm
- 備考: この場所は構想の保管庫。既存実装と未実装を混同しないこと。

## 0. ねらい

既存 `Vec.q2_star` は二成分 `(a,b)` の積
`(a,b) ⋆ (x,y) = (ax-by, ay+bx)` に対し `q₂(a,b)=a²+b²` が乗法的になることを形式化している。

本提案では、個々の公式を追加するだけでなく「どの乗法規則に対し、どの二次形式が乗法的か」を共通定理で表す。特に Gaussian、Eisenstein、さらに黄金・白銀などの二次代数の接続を優先する。

**注意:** `q(x⋆y)=q(x)q(y)` はノルムの乗法性であり、`q(x⋆y)=q(y)` という値の不変性は `q(x)=1` のときに得られる。正定値性は一般には成り立たない。

## 1. 二次代数の汎用保存核（第一優先）

可換環 R、パラメータ `s,t : R` に対して形式的な元 `α²=sα+t` を採用する。

```text
mulST (a,b) (c,d) = (ac+tbd, ad+bc+sbd)
normST (a,b) = a²+sab−tb²
normST (mulST u v) = normST u * normST v
```

正確には `R[X]/(X²−sX−t)` の二次代数ノルムに相当する。最後の等式は `CommRing R` 上の多項式恒等式としてまず Lean で証明する。

関連する必要定理:
- `mulST` の加法に関する分配法則、結合律、単位元 `(1,0)`、可換性
- `normST_mulST` および `normST_one`
- 共役 `conjST (a,b) = (a+sb,-b)` と `u * conjST u = (normST u,0)`
- `normST` の正定値性・非負性は別途仮定を付けた場合だけ

### 特殊化

| 環／座標基底 | s | t | normST |
|---|---:|---:|---|
| Gaussian: α=i | 0 | -1 | a²+b² |
| Eisenstein: α=ω, ω²+ω+1=0 | -1 | -1 | a²−ab+b² |
| √−2 | 0 | -2 | a²+2b² |
| Golden: α²=α+1 | 1 | 1 | a²+ab−b² |
| Silver: α²=2α+1 | 2 | 1 | a²+2ab−b² |

この表は代数的ノルムの特殊化。Golden / Silver のノルムは不定符号なので、距離の二乗と同一視しない。

## 2. Eisenstein の回転作用・状態と不変量（第二優先）

`qE(a,b)=a²−ab+b²` と置く。`ω=e^(2πi/3)` の座標で、60°回転は `u=1+ω` の乗法に相当する。

```text
rotate60 (a,b) = (a-b,a)
rotate60^3 (a,b) = (-a,-b)
rotate60^6 (a,b) = (a,b)
qE (rotate60 (a,b)) = qE(a,b)
```

原点以外の点は60°回転で6周期。一方、正三角形を頂点を区別しない図形として扱う場合の回転対称性は120°周期。ノルムは毎ステップで不変。この3種の「戻る」を混同しない。

追加候補:
- `qE_mulE`
- `qE_rotate60`, `rotate60_pow_three`, `rotate60_pow_six`
- Eisenstein 単元の列挙とノルム1との同値（整数上）
- 格子点、正三角形、向きの観測モデルを区別した例題

## 3. 既存 CF2D に接続する（第三優先）

既存コードの `Vec.q2_star` を変更するのではなく、`normST` を `s=0,t=-1` に特殊化すると同一になることを bridge 定理で示す。

- `Vec.star` と `mulST 0 (-1)` の一致
- `Vec.q2` と `normST 0 (-1)` の一致
- 既存 `Vec.q2_star` と汎用乗法性の対応
- 既存の UnitKernel / 回転作用とノルム1条件の再利用可能性を調査
- Mathlib の既存 `GaussianInt` 等との同型・橋渡しはAPI確認後に実施し、二重実装を避ける

## 4. 高次元は別トラック（探索のみ）

4成分の四元数、8成分の八元数には乗法的平方ノルムが存在する。しかし3次元の標準ユークリッドノルムでは、同じ条件の単位元付き双線形乗法を一般に作れない（Hurwitz 型の制限）。高次元版は二次形式パラメータ一般化とは別トラックとする。

- Quaternion で `N(pq)=N(p)N(q)` を検討
- Hurwitz 整数、格子閉性、可除性への接続
- 8次元では結合法則を仮定しない設計が必要
- 最初の実装範囲には含めない

## 5. 実装完了条件

1. 汎用 `mulST` / `normST` の多項式恒等式が Lean kernel-check される
2. Gaussian と Eisenstein が特殊化・bridge 定理で導出される
3. `rotate60^3=-id`、`rotate60^6=id` と `qE` 不変性が成立する
4. 既存 CF2D と整合し、重複定義・名前衝突を整理する
5. focused build、axiom audit、関連 docs を更新する
6. ここにある構想書を実装後に移動・status 更新し、未実装と誤認させない

## 6. 関連する既存資料

- `lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Basic.lean` — 既存 `Vec.q2_star`
- `docs/not_implements/260728-GN-Cyclotomic-Eisenstein-Bridge.md` — Eisenstein / GN 既存構想（重複調査）
- `docs/not_implements/260802-magic-core-signed-unit-metallic-ratio.md` — metallic ratio と符号付き単元（重複調査）
- `lean/dk_math/DkMath/CosmicFormula/Rotation/docs/Rotation2D-Implementation.md` — CF2D 回転実装の説明

## 7. 実装着手前の監査

`docs/not_implements` は過去に実装済みの案件も残るため、`develop` の現行定理・module・roadmap と照合してから TODO を確定する。ここへの文書保存は新規定理の実装完了を意味しない。
