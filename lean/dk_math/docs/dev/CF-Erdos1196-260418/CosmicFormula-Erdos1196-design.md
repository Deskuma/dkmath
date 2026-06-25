# 宇宙式 × 確率質量保存 API 実装計画

## 1. 目的

本計画の目的は、宇宙式の分解

\[
\mathrm{Big} = \mathrm{Body} + \mathrm{Gap},
\qquad
\mathrm{Body} = \mathrm{Core} + \mathrm{Beam}
\]

を、単なる代数恒等式としてではなく、

\[
\mu(\mathrm{Big}) = \mu(\mathrm{Body}) + \mu(\mathrm{Gap}),
\qquad
\mu(\mathrm{Body}) = \mu(\mathrm{Core}) + \mu(\mathrm{Beam})
\]

という **質量保存則** として読める API に落とし込むことである。

さらに、分割・分岐・Tail 構造・valuation の下降過程を同じ言語で扱えるようにし、

\[
\sum \text{子の質量} \le \text{親の質量}
\]

という **全体を超えない上界** を構造的に見える形で形式化する。

最終的には、これを ABC 側の bridge に接続し、

- `rad`
- `padicValNat`
- primitive prime
- squarefree / squarefull
- Big / Body / Gap / Beam

を共通の「質量・流れ・減衰」の観点で扱えるようにする。

---

## 2. 設計原則

### 2.1. 層を混ぜない

実装は次の順で積む。

\[
\text{CosmicFormula}
\;\to\;
\text{Mass API}
\;\to\;
\text{Branch API}
\;\to\;
\text{ValuationFlow}
\;\to\;
\text{ABC Bridge}
\]

### 2.2. 本丸に直接入れない

- `CosmicFormula` 側は **保存則・分解則**
- `NumberTheory` 側は **flow / hitting / primitive**
- `ABC` 側は **bridge のみ**

とする。

### 2.3. 最初は「確率」ではなく「質量」

いきなり Markov 連鎖を前面に出さず、まずは

- 非負
- 保存
- 劣保存
- hitting 上界

の形にする。

つまり、用語としては最初は **mass / branch / flow** を使い、
必要になったときに probabilistic interpretation を与える。

### 2.4. `Nat` 減算を避ける

差分の恒等式や保存則は、まず `ℤ` あるいは `ℚ` で閉じる。
`Nat` は必要なときに bridge を作る。

---

## 3. 新設ファイル構成案

```text
DkMath/
├── CosmicFormula/
│   └── Mass/
│       ├── Core.lean
│       ├── Decompose.lean
│       ├── Branch.lean
│       ├── Tromino2D.lean
│       └── Harmonic.lean          -- 後回し可
│
├── NumberTheory/
│   └── ValuationFlow/
│       ├── Basic.lean
│       ├── Hitting.lean
│       └── Primitive.lean
│
└── ABC/
    ├── MassBridge.lean
    └── ValuationFlowBridge.lean
```

---

## 4. 各ファイルの役割

## 4.1. `DkMath/CosmicFormula/Mass/Core.lean`

役目：

- 質量空間の最小抽象定義
- 宇宙式パーツの列挙
- 非負質量の基本 API

### 置くもの

- `MassSpace`
- `CosmicPart`
- `CosmicMassAPI`

### スケルトン

```lean
import Mathlib

namespace DkMath.CosmicFormula.Mass

structure MassSpace (α : Type _) where
  μ : α → ℚ
  nonneg : ∀ a, 0 ≤ μ a

inductive CosmicPart
  | big
  | body
  | gap
  | core
  | beam
deriving DecidableEq, Repr

structure CosmicMassAPI where
  massBig  : ℕ → ℕ → ℕ → ℚ
  massBody : ℕ → ℕ → ℕ → ℚ
  massGap  : ℕ → ℕ → ℚ
  massCore : ℕ → ℕ → ℕ → ℚ
  massBeam : ℕ → ℕ → ℕ → ℚ

end DkMath.CosmicFormula.Mass
```

---

## 4.2. `DkMath/CosmicFormula/Mass/Decompose.lean`

役目：

- Big / Body / Gap / Core / Beam の質量保存則
- residual 的読みの固定
- 必要なら `CoreBeamGap` との橋

### 中核定理

```lean
mass_big_eq_mass_body_add_mass_gap
mass_body_eq_mass_core_add_mass_beam
mass_big_eq_mass_core_add_mass_beam_add_mass_gap
mass_gap_eq_mass_big_sub_mass_body
```

### 数学的意味

\[
\mu(\mathrm{Big}) = \mu(\mathrm{Body}) + \mu(\mathrm{Gap})
\]

\[
\mu(\mathrm{Body}) = \mu(\mathrm{Core}) + \mu(\mathrm{Beam})
\]

\[
\mu(\mathrm{Big}) = \mu(\mathrm{Core}) + \mu(\mathrm{Beam}) + \mu(\mathrm{Gap})
\]

### 補足

最初は具体的な \(\mu\) を固定せず、`CosmicMassAPI` の仮定のもとで進める。
具体例として、後に

- 恒等質量
- 正規化質量
- 逆数型質量
- valuation 由来質量

を差し替えられるようにする。

---

## 4.3. `DkMath/CosmicFormula/Mass/Branch.lean`

役目：

- 子分岐の API
- outgoing mass の定義
- 劣保存則
- hitting mass の最小抽象

### 置くもの

- `Branching`
- `outgoingMass`
- `SubConservative`

### スケルトン

```lean
import Mathlib
import DkMath.CosmicFormula.Mass.Core

namespace DkMath.CosmicFormula.Mass

structure Branching (α : Type _) where
  children : α → Finset α

def outgoingMass [DecidableEq α]
    (M : MassSpace α) (B : Branching α) (a : α) : ℚ :=
  ∑ b in B.children a, M.μ b

class SubConservative {α : Type _}
    (M : MassSpace α) (B : Branching α) : Prop where
  outgoing_le : ∀ a, outgoingMass M B a ≤ M.μ a

end DkMath.CosmicFormula.Mass
```

### 中核定理

```lean
branch_sum_le_parent
outgoingMass_le_mass
hittingMass_le_rootMass
pairwise_disjoint_children_mass_add
```

### 数学的意味

\[
\sum_{b \in \mathrm{children}(X)} \mu(b) \le \mu(X)
\]

これが「全体を超えない」の最小核となる。

---

## 4.4. `DkMath/CosmicFormula/Mass/Tromino2D.lean`

役目：

- 2D トロミノ分解の固定
- 3 要素 + Gap の分解を分岐の最小教材として実装
- 質量保存の具体例を提供

### 背景式

\[
(x+u)(y+v) - uv = xy + xv + uy
\]

### 置くもの

- `TrominoParts2D`
- `mkTrominoParts2D`
- 2D の body / big / gap の対応補題

### スケルトン

```lean
import Mathlib

namespace DkMath.CosmicFormula.Mass

structure TrominoParts2D where
  A : ℤ
  B : ℤ
  C : ℤ
  Gap : ℤ

def mkTrominoParts2D (x y u v : ℤ) : TrominoParts2D :=
  { A := x * y
  , B := x * v
  , C := u * y
  , Gap := u * v }

theorem body2d_eq_sum_three_parts (x y u v : ℤ) :
    (x + u) * (y + v) - u * v = x * y + x * v + u * y := by
  ring

end DkMath.CosmicFormula.Mass
```

### 中核定理

```lean
body2d_eq_sum_three_parts
big2d_eq_sum_tromino_and_gap
mass_body2d_eq_mass_A_add_mass_B_add_mass_C
mass_big2d_eq_mass_A_add_mass_B_add_mass_C_add_mass_gap
```

---

## 4.5. `DkMath/CosmicFormula/Mass/Harmonic.lean`

役目：

- d/2 構造と反転の調和側 API
- 体積側から逆数側への写像の足場

### 位置づけ

これは後回しでよい。
まず保存則と分岐 API を固め、その後に

\[
V \mapsto \sqrt{V} \mapsto \frac{1}{\sqrt{V}}
\]

のような変換を扱う。

### 予定名

```lean
downHalf
invert
harmonicMap
mass_harmonic_nonneg
mass_harmonic_monotone
```

---

## 4.6. `DkMath/NumberTheory/ValuationFlow/Basic.lean`

役目：

- 整数または valuation state の下降過程
- prime step / prime-power step
- flow 質量の最小抽象

### 置くもの

- `ValuationState`
- `stepByPrime`
- `stepByPrimePow`
- `vMass`

### スケルトン

```lean
import Mathlib

namespace DkMath.NumberTheory.ValuationFlow

structure ValuationState where
  n : ℕ

def stepByPrime (n p : ℕ) : ℕ := n / p
def stepByPrimePow (n p k : ℕ) : ℕ := n / p^k

def vMass (n : ℕ) : ℚ := 0   -- 仮置き

end DkMath.NumberTheory.ValuationFlow
```

### 中核定理

```lean
flow_step_nonincrease
sum_child_vMass_le_parent_vMass
flow_nonneg
```

### 数学的意味

高 valuation の枝や細分化された枝が増えても、総質量は親を超えない。

---

## 4.7. `DkMath/NumberTheory/ValuationFlow/Hitting.lean`

役目：

- hitting mass の定式化
- 到達質量の上界
- antichain 的状況の最小抽象

### 中核定理

```lean
hit_mass_le_root
hitting_vMass_le_root
disjoint_targets_hit_add
```

### 位置づけ

primitive set の確率視点の構造核を、ABC 向けに一般化した層。
ただし、ここでは עדיין primitive set 専用にはしない。

---

## 4.8. `DkMath/NumberTheory/ValuationFlow/Primitive.lean`

役目：

- primitive prime / new mass channel の抽象化
- Zsigmondy 的「新しい素因子」を flow 側へ翻訳
- valuation の分岐新規性を API 化

### 中核定理候補

```lean
primitive_prime_yields_new_channel
disjoint_primitive_channels
rad_lower_bound_of_disjoint_channels
```

### 数学的意図

新しい素因子チャネルが増えるほど、
\(\operatorname{rad}\) や squarefree 部分の質量が持ち上がることを表す。

---

## 4.9. `DkMath/ABC/MassBridge.lean`

役目：

- CosmicFormula の質量保存 API を ABC の語彙へ翻訳
- Big / Body / Gap を \(a,b,c\) や `rad` の観点へ接続

### 中核定理候補

```lean
abc_big_body_gap_mass_bound
abc_gap_mass_le_big_mass
abc_squarefree_mass_lower_bound
abc_squarefull_mass_upper_bound
```

### 意味

- Gap は Big を超えない
- squarefree 部分は最低限これだけ必要
- squarefull 側へ質量が偏ると別の場所で制約が出る

---

## 4.10. `DkMath/ABC/ValuationFlowBridge.lean`

役目：

- `padicValNat` 系と `ValuationFlow` を接続
- primitive prime, rad, valuation の橋

### 中核定理候補

```lean
high_valuation_implies_branch_cost
primitive_prime_yields_new_mass_channel
rad_lower_bound_of_disjoint_mass_channels
```

### 意味

- valuation が高い枝には境界コストがある
- primitive prime は新規チャネルを作る
- 独立チャネル数から `rad` の下界を読む

---

## 5. 命名規則

検索性と一貫性のため、接頭辞を固定する。

### 5.1. 保存則

- `mass_*`

例：

```lean
mass_big_eq_mass_body_add_mass_gap
mass_body_eq_mass_core_add_mass_beam
mass_big_eq_mass_core_add_mass_beam_add_mass_gap
```

### 5.2. 分岐

- `branch_*`
- `outgoingMass_*`

例：

```lean
branch_sum_le_parent
outgoingMass_le_mass
```

### 5.3. hitting

- `hit_*`
- `hitting_*`

例：

```lean
hit_mass_le_root
hitting_vMass_le_root
```

### 5.4. flow

- `flow_*`
- `vMass_*`

例：

```lean
flow_step_nonincrease
sum_child_vMass_le_parent_vMass
```

### 5.5. Tail / GN

- `tail_*`
- `boundaryCost_*`
- `internalMass_*`

例：

```lean
tail_factorization_r
tail_boundary_cost_factorization
tail_mass_eq_boundaryCost_mul_internalMass
```

### 5.6. ABC bridge

- `abc_*`

例：

```lean
abc_gap_mass_le_big_mass
abc_rad_lower_bound_of_disjoint_channels
```

---

## 6. GN / Tail 構造との接続

高次 Tail 構造の基本式

\[
(x+u)^d-
\sum_{j=0}^{r-1}\binom{d}{j}x^j u^{d-j} =
x^r \, GN_d^{(r)}(x,u)
\]

は、境界因子と内部構造の分離そのものである。

これを API 化する。

## 6.1. 純代数層

### 定理候補

```lean
tail_factorization_r
gn_tail_recursion
xpow_r_dvd_tail
```

### 数学的意味

- \(x^r\) は境界次数
- \(GN_d^{(r)}\) は内部質量分布

## 6.2. 質量解釈層

### 定義候補

```lean
boundaryCost
internalMass
```

### 主定理候補

```lean
tail_mass_eq_boundaryCost_mul_internalMass
internalMass_nonneg
boundaryCost_nonneg
```

### 数学的意味

\[
x^r \;\leftrightarrow\; \text{境界コスト},
\qquad
GN_d^{(r)}(x,u) \;\leftrightarrow\; \text{内部質量}
\]

これにより Beam を「減衰の起こる層」として formalize できる。

---

## 7. 実装フェーズ

## 7.1. Phase A. 保存則の固定

対象：

- `CosmicFormula/Mass/Core.lean`
- `CosmicFormula/Mass/Decompose.lean`

通すもの：

```lean
mass_big_eq_mass_body_add_mass_gap
mass_body_eq_mass_core_add_mass_beam
mass_big_eq_mass_core_add_mass_beam_add_mass_gap
```

### 到達目標

宇宙式の部品分解を、代数式ではなく API として固定する。

---

## 7.2. Phase B. 2D トロミノで分岐の教材を作る

対象：

- `CosmicFormula/Mass/Tromino2D.lean`
- `CosmicFormula/Mass/Branch.lean`

通すもの：

```lean
body2d_eq_sum_three_parts
big2d_eq_sum_tromino_and_gap
outgoingMass_le_mass
```

### 到達目標

3 要素分割 + Gap の保存則を最小 concrete example として固める。

---

## 7.3. Phase C. Tail / GN を境界コストに読む

対象：

- `CosmicFormula/Mass/Decompose.lean` 追記
- 必要なら `CosmicFormula/Mass/Tail.lean` 新設

通すもの：

```lean
tail_factorization_r
xpow_r_dvd_tail
tail_mass_eq_boundaryCost_mul_internalMass
```

### 到達目標

Beam / Tail を「境界コスト × 内部質量」の言葉で読めるようにする。

---

## 7.4. Phase D. ValuationFlow 抽象 API

対象：

- `NumberTheory/ValuationFlow/Basic.lean`
- `NumberTheory/ValuationFlow/Hitting.lean`

通すもの：

```lean
flow_step_nonincrease
sum_child_vMass_le_parent_vMass
hitting_vMass_le_root
```

### 到達目標

valuation を 1 枚剥ぐ過程で総量が増えないことを API として表す。

---

## 7.5. Phase E. Primitive / ABC bridge

対象：

- `NumberTheory/ValuationFlow/Primitive.lean`
- `ABC/MassBridge.lean`
- `ABC/ValuationFlowBridge.lean`

通すもの：

```lean
primitive_prime_yields_new_channel
rad_lower_bound_of_disjoint_channels
abc_gap_mass_le_big_mass
abc_squarefree_mass_lower_bound
```

### 到達目標

ABC 側の `rad`, `padicValNat`, primitive prime を、
同じ質量言語で結び始める。

---

## 8. 最初のコピペ用テンプレ

### 8.1. `Core.lean`

```lean
import Mathlib

namespace DkMath.CosmicFormula.Mass

structure MassSpace (α : Type _) where
  μ : α → ℚ
  nonneg : ∀ a, 0 ≤ μ a

inductive CosmicPart
  | big
  | body
  | gap
  | core
  | beam
deriving DecidableEq, Repr

structure CosmicMassAPI where
  massBig  : ℕ → ℕ → ℕ → ℚ
  massBody : ℕ → ℕ → ℕ → ℚ
  massGap  : ℕ → ℕ → ℚ
  massCore : ℕ → ℕ → ℕ → ℚ
  massBeam : ℕ → ℕ → ℕ → ℚ

end DkMath.CosmicFormula.Mass
```

### 8.2. `Branch.lean`

```lean
import Mathlib
import DkMath.CosmicFormula.Mass.Core

namespace DkMath.CosmicFormula.Mass

structure Branching (α : Type _) where
  children : α → Finset α

def outgoingMass [DecidableEq α]
    (M : MassSpace α) (B : Branching α) (a : α) : ℚ :=
  ∑ b in B.children a, M.μ b

class SubConservative {α : Type _}
    (M : MassSpace α) (B : Branching α) : Prop where
  outgoing_le : ∀ a, outgoingMass M B a ≤ M.μ a

end DkMath.CosmicFormula.Mass
```

### 8.3. `Tromino2D.lean`

```lean
import Mathlib

namespace DkMath.CosmicFormula.Mass

structure TrominoParts2D where
  A : ℤ
  B : ℤ
  C : ℤ
  Gap : ℤ

def mkTrominoParts2D (x y u v : ℤ) : TrominoParts2D :=
  { A := x * y
  , B := x * v
  , C := u * y
  , Gap := u * v }

theorem body2d_eq_sum_three_parts (x y u v : ℤ) :
    (x + u) * (y + v) - u * v = x * y + x * v + u * y := by
  ring

end DkMath.CosmicFormula.Mass
```

---

## 9. 今回の実装計画の核心

この API の本質は、

\[
\text{等式の世界}
\quad\to\quad
\text{保存則の世界}
\quad\to\quad
\text{上界の世界}
\]

へ移すことにある。

宇宙式の各パーツは、単なる名前ではなく、

- **Big** ：全体質量
- **Body** ：実現済み本体
- **Gap** ：未到達・残余質量
- **Core** ：核
- **Beam** ：境界・遷移層

という状態変数になる。

すると、

\[
\mu(\mathrm{Big}) = \mu(\mathrm{Body}) + \mu(\mathrm{Gap})
\]

は保存則となり、

\[
\sum \mu(\text{children}) \le \mu(\text{parent})
\]

は「超えない」の原理になる。

ABC に直撃させる前に、この保存則 API を固めることが最優先である。

---

## 10. 最終結論

実装の順としては、次で進めるのが最も堅い。

1. `CosmicFormula/Mass/Core`
2. `CosmicFormula/Mass/Decompose`
3. `CosmicFormula/Mass/Tromino2D`
4. `CosmicFormula/Mass/Branch`
5. `CosmicFormula` 側の Tail / GN 接続
6. `NumberTheory/ValuationFlow/*`
7. `ABC/MassBridge`
8. `ABC/ValuationFlowBridge`

最初の勝ち筋は、ABC の大定理ではない。

**宇宙式の部品分解を、再利用可能な保存則 API として固定すること**

これが通れば、その後の

- 分岐
- hitting
- valuation
- primitive prime
- `rad`
- squarefree / squarefull

は、同じ言語で積み上げられる。

この API は、宇宙式を単なる分解式から、
**質量がどこへ流れ、どこで止まり、どこで減衰し、全体を超えないかを記述する形式体系**
へ変えるための核である。
