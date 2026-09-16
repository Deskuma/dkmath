# ABC Eisenstein landing provider 調査報告

## 0. 調査範囲・検証状態

- 依頼: ワークスペースと Mathlib の定理を調査し、形式化可能な資料を逐次記録する。production の実装より調査報告を優先する。
- 調査対象: [ABC_Eisenstein_landing_provider.md](ABC_Eisenstein_landing_provider.md)。文書中の phase / outcome は検討対象と報告の整理に使い、一般 ABC の証明作業には拡張しない。
- 現在の checkout: `research/ABC-Eisenstein-landing-provider-260915-v0`, HEAD `4535c76aae944a5aa7b741504eae9bfe080079c4`。添付資料の base `7ee9d183...` とは区別する。
- Lean toolchain: `leanprover/lean4:v4.32.2`。ビルド作業ディレクトリ: `lean/dk_math`。
- 調査開始時の working tree は clean。以下は現在のソースから確認する。

## 1. 調査ログ

### 001 — 問題の量化に必要な区別

`∃ β γ, α = β * γ^2` という等式だけなら、任意の環で `β := α`, `γ := 1` により成立する。したがって、この命題の不存在を一般のノルム反例から主張できない。

本調査では、これと次の実質的な要求を区別する。

> 既存の自然数の平方部分分解 `N(α) = d * s^2` に対し、
> `N(β) = d`, `N(γ) = s`, `α = β * γ^2` を満たす因子を構成できるか。

特に repeated modulus 自身を `N(γ)^2` と仮定しない。既存 `SquarefulPell` の evenPart / oddPart を確認する。

### 002 — 受け側の所在を確認

Lib の `eisensteinCoord_mul_sq` は必要な積座標を既に与える。`eisenstein_dvd_iff_norm_dvd_conjugate_coordinates` は二つの座標整除を必要十分条件にする。`eisenstein_norm_divisibility_not_sufficient` は一般のノルム整除の逆が偽であることを既に証明している。これらを provider と取り違えない。

### 003 — 不可能性判定を妨げる既存情報

この族の `a : ℕ` に対する `a^2 + 3*a + 3` は単射である。production に `cubicQuadratic_injective` が存在することを確認中。同一ノルムを持つ異なる自然数 shell パラメータという反例は作れない。一般の Eisenstein ノルム写像が非単射であることとは別問題である。

また、`DkMath.FLT.Three.EisensteinEuclidean` は正確に同じ carrier `TraceOneInt (-1)` に対する EuclideanDomain を実装済み。Eisenstein 環の PID / UFD を未証明の仮定として扱うのは不正確であり、その import と型クラス利用の実検証を続ける。

### 004 — 正しい平方部分の配分

`GNExcessCubicSquarefulPell` は `M = oddPart M * (evenPart M)^2` と
`Squarefree (oddPart M * S)` を既に供給する。したがって実質的な target は
`s := evenPart M`, `d := oddPart M * S`。例 `a = 17` では `N = 343 = 7^3`、
`M = 343`, `S = 1` であり、`M` 自身を平方ノルムにする配分は失敗する一方、
`N(γ) = 7`, `N(β) = 7` は整合する。

### 005 — provider 候補を一般の素因数分類から切り離せる

調査で見つかった経路は次のもの。現在スクラッチで kernel 検証中であり、この段階では完成済みと扱わない。

1. well-founded divisibility を使い、`α ≠ 0` を `α = β * γ^2`, `Squarefree β` に分解する。
2. 共役は環同型なので `Squarefree (conj β)`。
3. 整数 `t` に対し `t*t ∣ N(β)` なら、埋め込み後は `t*t ∣ β * conj β`。
4. Mathlib の平方自由な二因子についての整除補題から、整数スカラー `t` が `β` を割る。
5. `β ∣ α` と `α.snd = -1` より `t ∣ -1`、従って `t` は整数の単元。
6. よって `Squarefree (N(β))`。自然数の平方自由部分の一意性で既存の `d,s` に一致させる。

この経路が通れば、split prime ごとの新しい orientation 仮説、CRT 仮説、class-group 仮説を追加する必要はない。係数 1 と実装済みの EuclideanDomain が本質的な入力になる。

## 2. 最終判定

調査中。定理棚卸し、局所素数配分、成功したスクラッチ検証を以下に追記し、最後に主判定を一つに確定する。
