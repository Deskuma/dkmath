# Ultra-001Q Report — finite CRT-profile exponential tail

Date: 2026-07-26

## 判定

区間内の valuation vectors を有限 depth-profile space に分割し、各 exact
fiber を Ultra-001P の simultaneous CRT count で抑える exponential-moment
theorem と、その Chernoff bad-set theorem を証明した。

```text
finite valuation-profile space             complete
exact fiber to joint event                  complete
finite CRT-profile exponential moment       complete
CRT-profile Chernoff bad-set bound           complete
elementary finite depth-cap fallback         complete
X-independent profile-sum majorization       open
summable M3-heavy exceptional absorption     open
```

実装は `DkMath.ABC.GNJointDepthExponential` に置いた。

## 1. Finite profile space

```lean
def GNDepthProfileAt
def GNDepthProfileSpace
def GNDepthProfileExtension
noncomputable def GNExcessProfileMass
def GNExactDepthProfileEvent
```

各 component depth は、

```text
padicValNat q (GN p a b)
  ≤ Nat.log q (p * (X + b)^p)
```

で有限化される。`GNDepthProfileAt_mem_space` により全 `a ∈ Icc 0 X` が
この finite dependent product に入る。

`GNExcessMassAt_eq_profileMass` は exact fiber 上で pointwise mass と
profile weight が一致することを証明する。また、

```lean
theorem GNExactDepthProfileEvent_subset_joint
```

により exact valuation fiber は対応する simultaneous divisibility event
に含まれる。

## 2. CRT-profile moment

```lean
theorem exp_GNExcessMassAt_sum_le_profile
```

区間和を profile fibers に exact 分割し、各 fiber に P の count を代入して、

```text
∑ a ∈ Icc 0 X, exp(t * GNExcessMassAt Q p b a)
  ≤
∑ depth ∈ GNDepthProfileSpace Q p b X,
  ((p - 1)^Q.card *
    ((X + 1) / GNJointDepthModulus Q depth + 1))
  * exp(t * GNExcessProfileMass Q depth).
```

を得た。これは単なる最大値 bound ではなく、各 prime-power profile の
product modulus による density を保持する有限 CRT moment theorem である。

## 3. Chernoff endpoint

```lean
theorem card_GNExcessMassBadSet_le_exp
theorem card_GNExcessMassBadSet_le_exp_profile
```

正の `t` と threshold に対し、bad-set cardinality を
`exp (-t * threshold)` と上の finite CRT-profile sum の積で抑える。

さらに診断用の elementary fallback として、

```lean
noncomputable def GNExcessDepthCap
theorem exp_GNExcessMassAt_sum_le
theorem card_GNExcessMassBadSet_le_explicit
```

も実装した。こちらは `X` 依存の最大深度 cap による粗い有限評価であり、
CRT-profile theorem の代用品ではない。

## 4. 正確な停止境界

Q の combinatorial/finite Lean layer は閉じた。しかし profile sum の
boundary `+1`、prime family の増大、exponential weights を同時に処理して、

```text
finite profile sum ≤ (X + 1) * C(p,t)
```

のような `X` に依存しない majorant を得る解析定理はまだない。
従って「M3-heavy exceptions が summable / finite」は未証明であり、
M3 budget、M2 fresh-support compensation、uniform joint contract、
`abc_main_axiom` replacement はすべて open のままである。

## Local verification

```text
lake build DkMath.ABC.GNJointDepthExponential   success (8367 jobs)
lake build DkMath.ABC                            success (8387 jobs)
lake build DkMath                                success (8754 jobs)
representative axiom audit                       propext / Classical.choice / Quot.sound only
new production code                            no sorry / axiom / native_decide
git diff --check                               clean
```

full build に表示される既存 research module の `sorry` warning は今回の
変更によるものではない。

push、PR 更新、CI 起動・確認は行っていない。
