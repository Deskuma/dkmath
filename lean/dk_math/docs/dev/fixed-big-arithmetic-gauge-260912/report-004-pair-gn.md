# PAIR-GN-001: 二宇宙式の保存と全称命題の強さ

継続 branch: `wip/fixed-big-arithmetic-gauge-260912-v0`。
今回の検証対象はユーザーが提示した二つの単位境界 GN の和であり、前回の fixed-edge gauge モデルとは別に定義した。

## 既存コードとの照合

- `GNDegreeFactorization.prime_degree_of_prime_GN`: `d≥2, x>0, u>0` の必要条件。
- `GNPrimeTargetResidue`: prime target に対する `d ∣ P-1`。
- `GNRepresentationBounds`: 同じ正領域で `d<P`。
- `WeightedGNBridge.prime_exists_GN_eq_mul_add_rightBoundary`: prime row の quotient witness。
- `CosmicFormula.add_pow_eq_mul_GTail_one_add_gap`: 今回の二宇宙保存則の直接の代数的依存元。
- `Goldbach.Basic`: degree-two 展開および通常の `GoldbachPairAt`。

## Lean に固定した内容

新規 module: `DkMath/NumberTheory/Goldbach/PairGN.lean`。

`pairBig`, `pairGap`, `pairBody` はそれぞれ提示された二つの Big, Gap, unit-boundary Body の和。
`pairBody_add_pairGap` と `pairBig_sub_pairGap` は全ての自然数 degree/parameter で成立し、素数仮定を必要としない。

単一宇宙の補数は `singleBig_sub_GN` により厳密に `u^d`。
`single_complement_not_prime` は `d≥2` の下で非素数性を証明する（`u=0,1` も含む）。

`prime_unitGN_constraints` は既存必要条件をまとめ、degree が出力 prime と等しくなれないことも `d<GN` として保持した。
`prime_unitGN_quotient` は `GN d 1 u=1+d*A` の存在を既存 prime-row theorem から導いた。
`pairBody_eq_iff_weighted_quotients` は二つの**多項式表現等式を保持したまま**、
`pairBody=2n` と `d*A+e*B=2(n-1)` を同値にした（`n≥1`）。

## 初段の判定

`UnitPairAt n d e` は `u,v>0`、両 GN の素数性、および `pairBody=2n` を明示した命題である。
次を証明した。

```text
n≥3 ⇒ (GoldbachPairAt n ↔ UnitPairAt n 2 2)
n≥3 ⇒ ((∃ d e, Prime d ∧ Prime e ∧ UnitPairAt n d e) ↔ GoldbachPairAt n)
StrongGoldbach ↔ ∀ n≥3, UnitPairAt n 2 2
```

最後の証明では `n=2` の `2+2` を別途構成した。
degree-two の `GN 2 1 u=2u+1` は奇素数全体の carrier であり、素数2の carrier ではない。
任意の prime degree を許すだけでは、既に `d=e=2` が奇素数対全体を含むので、全称存在問題の論理的な強さは元の Goldbach と同じである。
これは三次の制限された幾何が無意味という判定ではない。次段で、その追加制約と失われる中心を検証する。

## 検証

`lean/dk_math` で `./lean-build.sh DkMath.NumberTheory.Goldbach.PairGN` が終了コード0。
このチェックポイントでは保存・必要条件・同値定理を固定した。全定理の axiom audit と三次/混合 degree の反例は次のチェックポイントで実施する。
