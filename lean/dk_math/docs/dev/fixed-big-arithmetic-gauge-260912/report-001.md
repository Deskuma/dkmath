# FBAG-001: fixed Big と有限平方素数認証

## 証明済みの範囲

`DkMath/NumberTheory/FixedBigGauge/Basic.lean` は `fixedBigUnit R k := R/k` を定義した。

- `scale_unit_conservation`, `fixedBig_decomposition`: `k>0` の下で `k*u=R`, `k²*u²=R²`。
- `unit_eq_iff_scale_mul_eq`: 整列する単位の一意性。
- `fixedBigUnit_div_edge_eq_projectionGap`, `fixedBigUnit_div_edge_eq_regularPhaseStep`: `R≠0` の下で `u/R=U(k-1)=regularPhaseStep k`。
- `normalized_unit_bounds`: `k>0` なら `0<u/R≤1`。
- `fixedBig_squareBody_normalization`: `R≠0` の下で `(R²-u²)/u²=squareBody P` (`k=P+1`)。
- `fixedBigUnit_transport`, `fixedBigUnit_refinement`: 解像度間の exact transport。
- `world_unit_eq_edge_mul_projectionGap`, `freshPrime_fixedBigUnit_refinement`: 既存 world-modulus API と reciprocal mesh theorem の再利用。

`SquareCertificate.lean` は既存 SquareBody の片方向定理を、`P<m≤squareBody P` での prime iff support-disjoint iff coprime に閉じた。
`prime_iff_coprime_of_physical_squareShell` は `m*u²≤R²-u²` という物理面積上の上限から同じ判定を導く。
自然数 label `m` の素数性を扱い、実数 `m*u²` 自体の素数性を定義していない。

## 真偽の区別

| 主張・条件を落とした強化 | 判定 | 固定した根拠 |
|---|---|---|
| 正の解像度で Big 保存 | 真 | 上記保存定理 |
| 非零辺長で SquareBody 正規化 | 真 | 正規化定理 |
| 辺長ゼロでも同じ正規化 | 偽 | `zero_edge_counterexample` (`P=1`) |
| 上限だけで prime iff raw support 回避 | 偽 | `lower_bound_is_necessary` (`P=m=2`) |
| 完全な `primeScalesUpTo 30` は 31〜960 を認証 | 真 | square-shell iff の特殊化 |
| 同じ判定を 961 にも延長できる | 偽 | `next_square_counterexample`: `961=31²` は composite だが旧 world と互いに素 |
| `{2,3,5}` の modulus 30 だけで 31〜960 を認証 | 偽 | `incomplete_world_counterexample`: 49 |
| `{6,14,21}` の product と lcm は同じ | 偽 | product 1764, lcm 42 を kernel 検証 |

平方上限は一般の十分条件である。全ての `P` で上限が最適だとは主張しない。
有限集合に属するかを判定する iff は、当該集合や素数対が非空である証明を供給しない。

## 検証

build cwd: `lean/dk_math`。

```sh
./lean-build.sh DkMath.NumberTheory.FixedBigGauge.SquareCertificate DkMathTest.NumberTheory.FixedBigGaugeAudit
lake env lean DkMathTest/NumberTheory/FixedBigGaugeAudit.lean
git diff --check
```

focused build は終了コード 0。axiom 出力は `axioms-001.log` に保存する。
有限反例は `decide +kernel` または `norm_num` による証明。

次の検証対象は、固定辺長で gauge を変える自由度が「元の自然数の中心」を保存するか、および bounded child survivor の存在条件である。
