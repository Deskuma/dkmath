# Ultra-001P Report — simultaneous CRT depth profiles

Date: 2026-07-26

## 判定

有限素数族の同時 prime-power divisibility を一個の product modulus に束ね、
joint residue address と区間 event の cardinality bound を証明した。

```text
joint depth modulus                    complete
joint canonical residues               complete
component congruence to product CRT    complete
joint residue count                    complete
joint interval count                   complete
```

実装は `DkMath.ABC.GNJointDepthExponential` に置いた。

## 1. Joint objects

```lean
def GNJointDepthModulus
def GNJointDepthResidues
def GNJointDepthEvent
```

depth profile `k_q` に対し、

```text
M = ∏ q ∈ Q, q ^ k_q
```

を modulus とし、`[0, M)` にある全 component divisibility を満たす
canonical residue と、`Icc 0 X` 内の同時 event を定義した。

## 2. CRT address count

```lean
theorem GNJointDepth_modEq
theorem card_GNJointDepthResidues_le
```

`Q` が相異なる素数からなる Finset なので component prime powers は互いに
coprime である。各 component residue への写像は product modulus 上で単射に
なり、Ultra-001K の simple-root count を各成分に適用して、

```text
card (GNJointDepthResidues Q depth p b)
  ≤ (p - 1) ^ Q.card
```

を得た。depth `0` の成分も別分岐で処理済みである。

## 3. Interval count

```lean
theorem card_gn_joint_deep_lift_interval_le
```

`p,q` が素数、各 `q ∈ Q` について `q ∤ p`、`q ∤ b` なら、

```text
card JointEvent
  ≤
(p - 1)^Q.card * ((X + 1) / M + 1).
```

これは同時 divisibility event を canonical residue classes で被覆し、
各 residue class の interval count を既存 `Nat.count_modEq_card` で抑えた
有限 CRT theorem である。

## 4. 境界

各固定 depth profile の simultaneous count は閉じた。全 profile の
weighted sum を一様定数へ majorize する解析段階は Ultra-001Q の
finite profile theorem の後に残る。

## Local verification

```text
lake build DkMath.ABC.GNJointDepthExponential   success (8367 jobs)
new production code                            no sorry / axiom / native_decide
```

push、PR 更新、CI 起動・確認は行っていない。
