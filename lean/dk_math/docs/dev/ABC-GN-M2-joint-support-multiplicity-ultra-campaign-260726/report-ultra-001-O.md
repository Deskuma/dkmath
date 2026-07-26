# Ultra-001O Report — exact pointwise GN mass bridge

Date: 2026-07-26

## 判定

full depth mass を support mass と valuation excess に exact 分解し、
canonical interval family 上の mass を既存の非例外 GN part の対数へ接続した。

```text
finite-family support mass                     complete
depth = support + excess                       complete
canonical family = log(non-exceptional part)   complete
uniform joint pressure budget                  open
```

実装は `DkMath.ABC.GNJointDepthExponential` に置いた。

## 1. Exact decomposition

```lean
noncomputable def GNSupportMassAt

theorem GNDepthMassAt_eq_support_add_excess
```

`Q` の各要素が素数で `GN p a b ≠ 0` なら、

```text
GNDepthMassAt Q p b a
  =
GNSupportMassAt Q p b a
  +
GNExcessMassAt Q p b a.
```

証明は各 `q` について、`q ∣ GN` なら
`v_q = 1 + (v_q - 1)`、割らなければ `v_q = 0` と分ける pointwise
identity である。従って不等式や余分な定数は入っていない。

## 2. Canonical non-exceptional bridge

```lean
theorem GNDepthMassAt_intervalFamily_eq_log_nonExceptionalPart
```

`p` が素数、`0 < b`、`a ∈ Icc 0 X`、`Nat.Coprime a b` のとき、

```text
GNDepthMassAt
  (GNNonExceptionalIntervalPrimeFamily p b X) p b a
  =
Real.log (GNNonExceptionalPart p a b).
```

target point の non-exceptional support が canonical interval family に
含まれること、family 内で target の support 外にある prime の valuation
がゼロであること、既存 factorization-log identity を合成している。

## 3. 境界

これで M/N の average/bad-set mass と、既存 joint pressure の
non-exceptional `support + excess` が exact に同一量へ接続された。
ただし、この等式自体はその mass の一様上界を与えない。

## Local verification

```text
lake build DkMath.ABC.GNJointDepthExponential   success (8367 jobs)
new production code                            no sorry / axiom / native_decide
```

push、PR 更新、CI 起動・確認は行っていない。
