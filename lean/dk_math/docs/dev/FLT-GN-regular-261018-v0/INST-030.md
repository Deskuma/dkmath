# DkMath NOTE-030 — Frey 有理 torsion の 2 進付値を整数折り返し軌道へ接続する

日付：2026-10-22（JST）  
基点：`dev/FLT-GN-regular-261018-v0`、`lean/dk_math/`  
スナップショット：`__snapshot-dk_math-lean-code-261022-0015.tar.gz`  
SHA256：`18e6403c82207872f350ac63745d9d57686d1f3988d3ce7788221f9c482a80db`  
commit hash: `ffe6b2ea9d1827c40e77ce6b9fd836e6b8ed6773`

## 0. 範囲と検証上の注意

- NOTE-016〜028 の幾何学的 Weil 対・`detρ=χ`、NOTE-029-A の安定直線／部分群、029-C の固定点の降下・`FoldedValuationOrbit` は既存の完成 Core とする。
- NOTE-030 の最初のゴールは **向き付けられた Frey Source における有理 p-torsion 排除** であり、局所慣性（029-B）、cofixed 不存在、無条件既約性は独立の未完成課題である。
- 対象はまず素数 `p≥5`。裸の `Source p` に `Even S.b` や `4∣S.a+1` を暗黙に付けない。向き付けは `FreyCounterexample.exists_source_of_counterexample` / `Source.ofCounterexample_spec` から得る。
- 今回は数学的・Lean API の設計である。新たな Lean 証明やビルドを実行した記録ではない。

## 1. 今回ソースを照合して見えた主役

Anthropic の `P2M/Sol/S_FreyPackage_freyCurve_rational_p_torsion_eq_zero.lean`（blob `fe61fd5d4f94d55b5a9da38d1541903c84397df0`）の `S04` は、次の順に進む。

1. `I n q := q=0 ∨ n≤v₂(q)` と `E n q := q≠0 ∧ v₂(q)=n` を導入する。`padicValRat` のゼロの扱いを避けるため、両者を混同しない。
2. `a₁=1, a₃=a₆=0`、`a₂` の2進整性、`v₂(a₄)=γ := p·v₂(b)-4` を確立する。
3. 負の `v₂(x(kQ))` を有限周期中の最小点と倍点公式から排除する：`frey_I_xc_nsmul`。
4. `x=0` なら位数2、`v₂(x)=0` は `a₂` の場合分けと2Q/3Qの加法公式で排除する：`frey_x_ne_zero_of_order`, `frey_deep_of_order`。
5. **有理2-torsion** `T=(0,0)` に注目する。`2T=0` と、`x(P+T)=a₄/x(P)` を証明する：`frey_ns00`, `frey_T0_T0`, `frey_addX_T0`。
6. 変換後の値が負になるか0になるかで分け、`2(P+T)=2P` と3・4の結果を用いて `v₂(x(P))≤γ−1` を証明する：`frey_shallow_of_order`。
7. `x+2y` の付値を証明する `frey_E_D` を使い、倍点・和差公式 `dbl_ident`, `pm_ident` を付値化する。
8. 元の `S04.Arith.arith_core` 相当の整数漸化式は、DkMath では **既に** `FoldedValuationOrbit.no_prime_shifted_valuation_orbit` として証明済み。再移植不要。

### 二つの中心恒等式

正規化曲線

\[
y^2+xy=x^3+a_2x^2+a_4x
\]

上で、`T=(0,0)` が2-torsion。`x(P)≠0` なら

\[
x(P+T)=\frac{a_4}{x(P)},\qquad v_2(x(P+T))=\gamma-v_2(x(P)).
\]

**注意**：`P+T` は一般には p-torsion でない（p は奇素数）。上限証明では `2(P+T)=2P` へ戻すことが不可欠。`T` と `Q` の位数を混同しない。

倍点・和差の重要な等式は、非零分母を明示すると

\[
x(2P)(x+2y)^2=(x^2-a_4)^2,
\]

\[
x(P+Q)x(P-Q)(x(P)-x(Q))^2=(x(P)x(Q)-a_4)^2.
\]

したがって、必要な座標が非零なら

\[
e(2)+2e(1)=2v_2(x(Q)^2-a_4),
\]

\[
e(k+1)+e(k-1)+2B(k)=2A(k).
\]

このため2進 min 法則だけでなく **零にならない証明と座標同一性** が必須となる。

## 2. DkMath 固有の翻訳上の短縮

DkMath の `DkMath/Lib/NumberTheory/FreyGapCubic.lean` は

```lean
def normalized (A B : ℚ) : WeierstrassCurve ℚ :=
  ⟨1, (B - A - 1) / 4, 0, -(A * B) / 16, 0⟩
```

を持ち、`DkMath/FLT/Frey.lean` は `S.curve_map` を証明済み。`S.normalization.four : 4 ∣ S.b^p - S.a^p - 1` と `S.normalization.sixteen` も `Source` に含む。

このため **`a₂` が2進整であること** は、Anthropic と同じ mod 4 のやり直しをしなくても、`S.curve_map` と整係数モデルから証明する候補がある。これは全 `Source` で有効な薄い bridge になり得る。

一方、`v₂(a₄)=p v₂(S.b)-4` を主張するには `S.a` が奇数で `S.b` が偶数という算術情報が必要。`Even S.b` と `S.coprime` から `S.a` の奇数性を取り出し、`S.a_ne/S.b_ne` により非零を確保する。**`Source.normalization` 単独で偶奇を供給したと見なさない。**

## 3. NOTE-030 を小単位へ切る実装順序

| 指令    | 実装内容                                                   | 閉じる到達定理（提案名。未実装）                                 | 配置候補                                                             |
| ------- | ---------------------------------------------------------- | ---------------------------------------------------------------- | -------------------------------------------------------------------- |
| 030-001 | 一般の有理2進 `I/E`、和差・積・除・冪・min                 | `twoAdicExact_add_lower`, `twoAdicLower_sub_exact` など          | `DkMath/Lib/NumberTheory/RationalTwoAdicBounds.lean`                 |
| 030-002 | `Source` の係数、正規化・偶奇条件の橋                      | `a₂_twoAdic_integral`, `a₄_twoAdic_exact`                        | `DkMath/FLT/FreyRationalTorsionValuation.lean`                       |
| 030-003 | Frey 曲線上の有限点・`x`・非零位数、負付値最小軌道         | `x_nonzero_of_addOrder_eq_prime`, `x_nonnegative_of_prime_order` | 同上                                                                 |
| 030-004 | 単元付値0の排除、`a₂` の場合分け、2Q/3Q                    | `x_positive_of_prime_order`                                      | 同上                                                                 |
| 030-005 | `T=(0,0)` と `x(P+T)=a₄/x`、反射の上下界                   | `x_reflection_by_two_torsion`, `x_below_gamma_of_prime_order`    | `DkMath/Lib/NumberTheory/WeierstrassXReflection.lean` と Frey 特殊化 |
| 030-006 | `x+2y` の正確な付値、倍点・和差恒等式、非零性              | `double_x_valuation_identity`, `plus_minus_x_valuation_identity` | `DkMath/Lib/NumberTheory/WeierstrassXIdentities.lean`                |
| 030-007 | `e,A,B,A₁` を実際の Q から定義し、整数核へ渡す各入力を証明 | `frey_rational_p_torsion_eq_zero`                                | `DkMath/FLT/FreyRationalTorsion.lean`                                |
| 030-008 | `FreyStableLine` の `hrat` 入力へ橋を接続                  | `residual_noNonzeroFixed_of_oriented`（仮称）                    | `DkMath/FLT/FreyStableLine.lean` または Bridge                       |

`030-001` ではゼロにおける `padicValRat` の値を仮定で押しつぶさないよう、`I/E` 方式を採用するのが安全。

`030-003` は大きく見えるが、上流は `frey_double_neg`（負付値なら倍点の付値がさらに小さくなる）→ `frey_I_xc_nsmul`（有限周期の最小値による矛盾）という二段構造。丸ごと移植ではなく、この抽象的な有限軌道原理を最初に分離する。

`030-005` は幾何構造として最も再利用価値が高い。`x↦a₄/x` による付値反射は Frey の形式を超え、`a₁=1,a₃=a₆=0` の Weierstrass モデルで成立する。ただしモデル変換で x 座標の意味が変わるため、射と条件を明記する。

## 4. 整数核へ渡す最終入力

`DkMath.Lib.NumberTheory.FoldedValuationOrbit.no_prime_shifted_valuation_orbit` の実際のシグネチャに合わせて、以下を同一の `S` と同一の `Q` から証明する。

```text
p        : ℕ, hp : p.Prime, hp5 : 5 ≤ p
S        : Frey.Source p
hbe      : Even S.b                 -- 明示する
Q        : S.rationalCurve.toAffine.Point
hQp      : p • Q = 0, hQ0 : Q ≠ 0
γ        := (p : ℤ) * padicValInt 2 S.b - 4
e(k)     := padicValRat 2 (x-coordinate (k • Q))
A(k)     := padicValRat 2 (x-coordinate (k • Q) * x(Q) - S.rationalCurve.a₄)
B(k)     := padicValRat 2 (x-coordinate (k • Q) - x(Q))
A₁       := padicValRat 2 (x(Q)^2 - S.rationalCurve.a₄)
```

チェックする7条件：

1. `γ = p·padicValInt 2 S.b−4`。
2. 全 `1≤k≤p−1` で `1≤e(k)≤γ−1`。
3. `2e(1)≠γ → A₁=min(2e(1),γ)`、等しい場合は `γ≤A₁`。
4. `e(2)+2e(1)=2A₁`。
5. `A(k)` について `e(k)+e(1)` と `γ` の min／同値時下界。
6. `B(k)` について `e(k)` と `e(1)` の min／同値時下界、さらに `e(k+1)+e(k−1)+2B(k)=2A(k)`。
7. `(p−1)Q=−Q` から `e(p−1)=e(1)`。

約分条件 `2γ∣pm → 2γ∣m` は既に `no_prime_shifted_valuation_orbit` に取り込まれており再実装不要。

### 原則

- upstream の `FreyPackage` ≠ DkMath の裸の `Source`。向き付き条件は公開 API の仮定として記す。
- `Q≠O`、`x≠0`、`x(kQ)≠0`、`x(kQ)≠x(Q)` を先に証明してから付値恒等式に変換する。
- `p≥5` は 2Q/3Q の消失を排除する段階で重要。`p=2` には実際の反例回帰がある。
- 上流の `P2MW` マクロや FLT 完成定理に依存せず、Mathlib と DkMath 完成 Core のみで証明する。
- `sorry`・`sorryAx`・追加公理なし。公理は `propext` / `Classical.choice` / `Quot.sound` のみを許容し、型と opaque 本体を監査する。
- upstream に対応する翻訳コードでは Apache-2.0 の帰属と blob を明記し、DkMath 独自の証明と区別する。

## 5. 完成と未完成の境界

```text
NOTE-028【完成】 geometric Weil pairing, detρ=χ
  ↓
NOTE-029【完成】 可約 → stable line / p-cyclic subgroup
  ├─ NOTE-030【計画】 有理p-torsion排除 → hrat (→ hzero)
  ├─ NOTE-031候補【別線】 局所慣性 → fixed/cofixed hcases
  └─ 後続【別線】 cofixed 不存在 hno (Mazur 側)
      ↓
      hrat + hcases + hno → Frey 残余表現の既約性
```

**NOTE-030 を完成しても直ちに既約性・一般 FLT が完成するわけではない。** `hno` は別の重大な数学的障害として保持する。

## 6. 研究の問い

`x(P+T)=a₄/x(P)` の反射が `v₂(x)↦γ−v₂(x)` を作るのに対し、`FoldedValuationOrbit` の軌道は `θ↦θ+e(1) (mod 2γ)` の反復を絶対値で折り返す。この二つを同じ「境界反射／周期作用」として抽象化できるか。

これは付値の具体的な矛盾を閉じた**後**に研究すべき一般化であり、その一般化を先に定理として仮定してはならない。

## 7. 主な原典とローカル資産

- Anthropic: https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_FreyPackage_freyCurve_rational_p_torsion_eq_zero.lean
- DkMath: `DkMath/Lib/NumberTheory/FoldedValuationOrbit.lean`
- DkMath: `DkMath/FLT/Frey.lean`, `DkMath/FLT/FreyCounterexample.lean`, `DkMath/FLT/FreyStableLine.lean`
- DkMath: `DkMath/Lib/NumberTheory/FreyGapCubic.lean`
- DkMath: `docs/dev/FLT-GN-regular-261018-v0/IMPLEMENTATION-NOTE029-261021.md`
- 研究ハンドオフ: `DkMath_NOTE016-029_研究ハンドオフ_20261022.md`

検証状況：ハンドオフの記録上は NOTE-029 の 11,665 jobs・公理監査合格。NOTE-030 の新規 Lean ソース・コンパイル・追加の監査は未実施。
