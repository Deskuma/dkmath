# GN 同値と有限被覆への完全還元

## 検証済み

`./lean-build.sh DkMath.NumberTheory.Goldbach.Basic` と `./lean-build.sh DkMath.NumberTheory.Goldbach.Obstruction` は終了コード 0。

- 通常の `p+q=2*n`、固定中心の GN 素数対、対称 offset の三形式は厳密に同値。
- `u=0` を含む完全探索域は `Finset.range (n-1)`。
- `goldbachBody = BodyN 2 (n-u) u = n^2-u^2`。Big = Body + Gap も証明。
- 合成数端点は `r^2≤2*n` を満たす真の素因子を持つ。
- `GoldbachPairAt n` と有限生存集合の非空性が同値。
- `¬GoldbachPairAt n` と、全候補を真の小素数障害が被覆することが同値。

これらは全ての自然数 `n` を量化した還元定理であり、個別数値での探索結果ではない。一方、有限生存集合が全ての `n≥2` で非空になることはこの還元だけでは証明されない。

## 次の明確化対象

合同障害は `+n, -n (mod r)` の二点。ただし `r∣2*n` のときは一点に合流する。特に `r=2` に対して一律に二点を引く密度式は不正確。局所計数と CRT を実装し、実際の区間被覆の濃度と区別する。
