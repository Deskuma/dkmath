# Tromino Boundary Flow / Four-Color Path Reduction 実装計画

- cid: `6aa51f66-502c-83e9-994c-dbd0118584c1`
- Status: implementation plan / not implemented
- Date: 2026-09-12
- Branch at recording: `develop`
- Repository: `Deskuma/dkmath`
- Existing base: `lean/dk_math/DkMath/Tromino.lean`
- Target area: `DkMath.Polyomino.Tromino`, graph / planar-boundary bridge, future coloring bridge

## 1. 目的

本資料は、既存の幾何学的 L 型トロミノ

```text
■■
■□
```

に現れる

$$
3+1=2^2
$$

という局所 completion 構造を、有限状態・境界・XOR 保存則へ抽象化し、最終的に

```text
塗り分け問題
  ↓
境界差分ラベル
  ↓
IN / OUT pairing
  ↓
transition graph
  ↓
path / cycle decomposition
  ↓
XOR transport
  ↓
彩色復元
```

という変換を Lean 上で固定するための実装予定である。

着想の出発点は四色問題であるが、本計画の第一目標は四色定理そのものの新証明ではない。

第一目標は、より一般的な次の原理を theorem family として切り出すことである。

> 4 状態系から 1 状態を欠いた 3 状態の局所核を、境界差分と保存則として読み替えると、有限状態の塗り分け問題を派生 transition graph 上の path / cycle 探索問題へ変換できる場合がある。

特に、彩色を直接探索するのではなく、彩色を復元できる「境界経路証明書」を探索する設計を狙う。

---

## 2. 現在の `DkMath.Tromino` の位置

現在の `lean/dk_math/DkMath/Tromino.lean` には、主として次が実装されている。

- `L_tromino`
- `I_tromino`
- `block2`
- `hole2`
- 面積 `3`, `4`, `1`
- `block2 = L_tromino ∪ hole2`
- `Disjoint L_tromino hole2`
- 平行移動
- 90 度回転
- 鏡映
- 面積不変性
- 360 度回転の恒等性
- `IsLTromino`
- `IsLTromino.card_eq_three`

したがって幾何学的な

$$
4=3+1
$$

は既に有限集合・面積の両方で固定されている。

一方、現時点では次の層は未実装である。

- 「不足 1 状態」の一意 completion
- 4 状態平方と 3 非零状態の抽象化
- XOR 型保存則
- 境界 port
- IN / OUT pairing
- transition system
- path / cycle decomposition
- 閉路保存則
- 経路積分による状態復元
- 彩色問題との bridge

本計画はこの未実装層を「第二世代 Tromino theory」として追加する。

---

## 3. 基本視点: 幾何トロミノから状態トロミノへ

### 3.1 幾何側

既存の L 型トロミノは `2 × 2` block の 4 セルから 1 セルを欠いた形である。

```text
■■
■□
```

ここで、3 セルを occupied、1 セルを missing と読む。

$$
|Q|=4,
\qquad
|T|=3,
\qquad
|Q\setminus T|=1
$$

### 3.2 状態側

4 状態を Boolean square

$$
\mathcal Q=\mathbb F_2^2
$$

として読む。

具体的には

$$
\mathcal Q=\{00,01,10,11\}
$$

である。

非零 3 状態を

$$
A=01,
\qquad
B=10,
\qquad
C=11
$$

と置く。

すると

$$
A\oplus B=C,
\qquad
B\oplus C=A,
\qquad
C\oplus A=B
$$

かつ

$$
A\oplus B\oplus C=00
$$

となる。

これを代数的 Tromino kernel とみなす。

```text
幾何表現        状態表現

■■             A B
■□             C 0
```

両者の共通核は

```text
complete 4-state square
minus one distinguished state
= three-state residual
```

である。

---

## 4. Coloring から boundary crossing への反転

通常の塗り分け問題は、面または頂点へ直接

$$
c : V \to \mathbb F_2^2
$$

を割り当てる問題として書かれる。

本計画では、色そのものより先に隣接境界を跨いだ差分を読む。

隣接する `u, v` に対して

$$
\delta(u,v):=c(u)\oplus c(v)
$$

と置く。

適正彩色であれば

$$
\delta(u,v)\ne 00
$$

なので、境界が取り得る差分状態は

$$
\{A,B,C\}
$$

の 3 種類だけとなる。

したがって問題は

```text
この面は何色か？
```

から

```text
この境界を跨ぐと状態が A / B / C のどれだけ変化するか？
```

へ反転する。

この差分表示が本計画の中心である。

---

## 5. 局所 Tromino XOR kernel

三角形または 3-way local junction の境界差分を

$$
\delta_1,\delta_2,\delta_3\in\{A,B,C\}
$$

とする。

局所閉路では

$$
\delta_1\oplus\delta_2\oplus\delta_3=00
$$

が必要である。

異なる二状態が分かれば三状態目は

$$
\delta_3=\delta_1\oplus\delta_2
$$

として一意に決まる。

したがって

```text
known + known
  ↓ XOR
missing state
```

が得られる。

これを `TrominoCompletion` の最小代数核とする。

候補 theorem:

```lean
xor_nonzero_pair_complete
xor_three_nonzero_eq_zero
nonzero_triple_eq_full_tromino
missing_delta_unique
```

---

## 6. Boundary port と保存則

領域 `v` の境界に接続する half-edge / port の有限集合を `P(v)` とする。

各 port には非零差分ラベル

$$
\lambda : P(v) \to \{A,B,C\}
$$

を与える。

局所保存則を

$$
\bigoplus_{p\in P(v)}\lambda(p)=00
$$

とする。

ここで各ラベルの本数を

$$
n_A,
\qquad
n_B,
\qquad
n_C
$$

とする。

`A=(1,0)`, `B=(0,1)`, `C=(1,1)` より、XOR sum が 0 であることは

$$
n_A+n_C\equiv0\pmod2,
$$

$$
n_B+n_C\equiv0\pmod2
$$

と同値である。

したがって

$$
\boxed{n_A\equiv n_B\equiv n_C\pmod2}
$$

を得る。

これは今回の最重要局所 theorem 候補である。

候補名:

```lean
boundary_xor_zero_iff_label_parity_eq
boundary_conserved_parity
```

---

## 7. IN / OUT Pairing theorem

前節の parity theorem から、保存された boundary ports には二種類しかない。

### 7.1 even case

`n_A, n_B, n_C` がすべて偶数なら、同種ラベルを

```text
A -- A
B -- B
C -- C
```

として完全に pair できる。

概念的には

$$
\operatorname{ConservedBoundary}_{\mathrm{even}}
\Longrightarrow
\operatorname{PerfectPairing}
$$

である。

### 7.2 odd case

`n_A, n_B, n_C` がすべて奇数なら、各ラベルを可能な限り同種 pair にすると最後に

$$
\{A,B,C\}
$$

が 1 本ずつ残る。

すなわち

$$
\boxed{
\operatorname{ConservedBoundary}
=
\operatorname{PairedTransport}
+
\operatorname{TrominoResidual}
}
$$

という分解が得られる。

候補 theorem:

```lean
exists_same_label_pairing_of_even_counts
exists_pairing_with_tromino_residual_of_odd_counts
conserved_boundary_pairing_or_tromino_residual
```

ここでは `pairing` の表現として、有限集合上の fixed-point-free involution、`Sym2`、matching edge set、または Mathlib の既存 matching API のどれを採用するかを実装時に比較する。

---

## 8. Transition graph

各 port は二種類の接続を持つ。

1. 実際の境界を跨いで隣接領域側の port へ移る接続
2. 同一領域内部で IN / OUT pairing により別 port へ移る接続

この二種類を交互に辿る派生グラフを `TransitionGraph` とする。

```text
boundary crossing
  ↓
local pairing
  ↓
boundary crossing
  ↓
local pairing
  ↓
...
```

pairing が完全であり、各 boundary port が実境界にも一意に属するなら、内部 port の次数は 2 となる。

有限次数 2 グラフの各連結成分は、条件に応じて

```text
cycle
```

または ghost / open endpoint を許す場合

```text
path
```

となる。

これを「塗り分け問題の一筆書き化」の正確な意味とする。

**注意:** 元の平面地図そのものが Euler graph になると主張するものではない。

一筆書き対象は、boundary ports と local pairing から構成された派生 transition graph である。

候補 theorem:

```lean
transitionGraph_degree_two
connected_component_is_path_or_cycle
closed_transition_component_is_cycle
```

---

## 9. XOR transport と状態復元

基準領域または基準頂点 `v₀` に

$$
c(v_0)=00
$$

を与える。

`v₀` から `v` への transition path `P` に沿う境界差分を XOR して

$$
c_P(v)
:=
c(v_0)
\oplus
\bigoplus_{e\in P}\delta(e)
$$

とする。

閉路 `C` ごとに

$$
\bigoplus_{e\in C}\delta(e)=00
$$

が成立すれば、`c_P(v)` は経路選択に依存しない。

したがって

```text
cycle XOR conservation
  ↓
path independence
  ↓
global state integration
```

が得られる。

さらに全実境界で

$$
\delta(e)\ne00
$$

なら、復元された隣接状態は必ず異なる。

従って最終 bridge theorem は概念的に

$$
\boxed{
\operatorname{ValidBoundaryFlow}
\Longrightarrow
\operatorname{ProperFourStateColoring}
}
$$

となる。

候補 theorem:

```lean
xorTransport
xorTransport_path_independent_of_cycle_zero
colorRecovery
colorRecovery_adjacent_ne
```

---

## 10. Ghost boundary / square completion

元の図の外側では、局所的な square / triangle completion に不足が起きる場合がある。

そこで境界外側に仮想領域、仮想 port、仮想 edge を追加して一旦閉じた completion object を作る。

```text
original boundary
  ↓
add ghost cells / ports / faces
  ↓
complete local square structure
  ↓
solve XOR / pairing / transition graph
  ↓
remove ghost structure
  ↓
restrict solution to original object
```

元の graph `G` が completion `G⁺` の部分構造なら、`G⁺` 上の proper coloring を `G` へ制限すること自体は容易である。

難点は、任意の対象について「都合の良い completion が必ず存在する」ことではない。

この存在問題は四色定理側へ接続する際の主要研究課題として分離する。

候補概念:

```lean
GhostCompletion
IsAdmissibleBoundary
ExtendsBoundary
restrictColoring
```

---

## 11. Planarity と non-crossing pairing

平面領域の boundary ports に cyclic order がある場合、local pairing に non-crossing 条件を課すことができる。

円周上の `2n` ports を交差なしで pair する構造は Catalan 型となる。

このとき pairing の包含 / 入れ子関係は tree として表現できる可能性がある。

```text
cyclic boundary order
  ↓
non-crossing pairing
  ↓
nested intervals
  ↓
Catalan / tree representation
```

したがって今回の直感で現れた

```text
tree structure
path search
one-stroke traversal
```

は別々の話ではなく、同一 transition structure の局所・大域表現として統一できる可能性がある。

この層は最初から必須とはしない。

まず abstract pairing / transition graph を完成させ、その後 planar embedding / rotation system API と接続する。

---

## 12. 四色問題との接続

### 12.1 目標となる反転

通常の問題:

```text
arbitrary planar map
  ↓
find one of four colors for every region
```

本計画の反転:

```text
arbitrary planar map
  ↓
extract boundary structure
  ↓
complete missing outer structure if needed
  ↓
find conserved A/B/C boundary flow
  ↓
find compatible transition paths/cycles
  ↓
integrate XOR flow
  ↓
recover four-state coloring
```

すなわち

> 「4 色をどう選ぶか」ではなく、「4 色で塗れる boundary-flow structure とは何か」を先に定義する。

### 12.2 Tait / nowhere-zero flow との関係

`\mathbb F_2^2` の非零 3 元を edge states として使う視点は、既知の四色定理の Tait edge-coloring / flow formulation と近い。

したがって実装時には、既知理論と一致する部分と DkMath 独自の抽象化を明確に分離する。

独自性候補は四色定理の主張そのものではなく、特に次にある。

- 幾何 L-tromino `3+1` から algebraic 3-state residual への共通 API
- boundary port parity theorem の Tromino residual 解釈
- local pairing から transition graph を生成する API
- finite-state coloring を path certificate へ変換する一般 interface
- ghost completion と restriction の明示的分離

### 12.3 未証明部分

次は本計画記録時点では未証明であり、主張しない。

- 任意の平面地図に目的の boundary pairing が存在すること
- 任意の completion が cycle XOR compatibility を持つこと
- non-crossing pairing が常に選べること
- path / cycle 探索だけで四色定理全体が自動的に証明できること
- 本構成が既知証明より小さいこと

四色定理の難しさが消えるのではなく、主として

$$
\boxed{
\text{boundary-flow / completion existence}
}
$$

へ圧縮される可能性を調べる。

---

## 13. 推奨 Lean モジュール構成

既存 `DkMath.Tromino` を facade / geometric base として維持し、概念層を分割する案。

```text
DkMath/
  Tromino.lean
  Tromino/
    Completion.lean
    XorKernel.lean
    Boundary.lean
    BoundaryPairing.lean
    TransitionGraph.lean
    XorTransport.lean
    ColorRecovery.lean
    GhostCompletion.lean       -- later
    PlanarPairing.lean         -- later
```

ただし namespace は現在の

```lean
DkMath.Polyomino.Tromino
```

との整合を優先する。

Graph 理論として独立性が高くなった段階で

```text
DkMath.Graph.TrominoFlow
```

または

```text
DkMath.Combinatorics.BoundaryFlow
```

への昇格も検討する。

---

## 14. 実装フェーズ案

### Phase TBF-000: repository survey

- `DkMath/Tromino.lean` の現行 API 確認
- Mathlib の `SimpleGraph`, walk / path / cycle, matching, Eulerian, planar graph 周辺 API を調査
- `Fin 2 → ZMod 2`, `ZMod 2 × ZMod 2`, `Fin 4`, `Bool × Bool` の表現比較
- XOR / additive notation の simp 性を比較

Outcome:

- state type
- graph representation
- pairing representation

を決定する。

### Phase TBF-001: algebraic tromino kernel

実装候補:

```lean
Delta4
Delta3
A B C
```

および

```lean
A_xor_B_eq_C
B_xor_C_eq_A
C_xor_A_eq_B
A_xor_B_xor_C_eq_zero
```

を固定。

### Phase TBF-002: completion

- two-known → unique missing
- nonzero triple characterization
- geometric `block2 / L_tromino / hole2` との説明 bridge

### Phase TBF-003: boundary conservation

- finite ports
- label count
- XOR sum
- parity theorem

主定理候補:

```lean
boundary_xor_zero_iff_counts_same_parity
```

### Phase TBF-004: pairing / residual

- even count perfect same-label pairing
- odd count pair decomposition
- residual exactly `{A,B,C}`

主定理候補:

```lean
conservedBoundary_eq_pairs_add_trominoResidual
```

### Phase TBF-005: transition graph

- real boundary involution
- local pairing involution
- alternating transition
- degree-two result
- component path/cycle decomposition

### Phase TBF-006: XOR transport

- walk label sum
- concatenation
- reverse path
- cycle-zero
- path independence

### Phase TBF-007: color recovery

- base color
- recovered state
- adjacent inequality
- proper 4-state coloring certificate

### Phase TBF-008: planar / ghost experiments

- small planar maps
- outer ghost completion
- cyclic boundary order
- non-crossing pairings
- computational enumeration

### Phase TBF-009: four-color bridge assessment

ここで初めて四色定理への bridge の強さを評価する。

Outcome A:

- arbitrary planar map について required boundary-flow existence theorem が得られる。

Outcome B:

- restricted graph class でのみ成立する。

Outcome C:

-一般四色 bridge は得られないが、finite-state constraint → path certificate の一般 theorem family として残す。

いずれの Outcome でも Tromino / BoundaryFlow ライブラリ自体は成果として維持する。

---

## 15. 最初に狙う最小 theorem set

最初から planar map や四色定理へ進まず、次の小定理群を CI-GREEN にする。

```text
TBF-K00  four states = zero + three nonzero states
TBF-K01  A ⊕ B = C and cyclic variants
TBF-K02  A ⊕ B ⊕ C = 0
TBF-K03  any two distinct nonzero states determine the third
TBF-B00  boundary XOR zero iff A/B/C counts have equal parity
TBF-B01  even conserved boundary admits same-label pairing
TBF-B02  odd conserved boundary reduces to pairs + one A/B/C residual
TBF-G00  paired transition ports have degree two
TBF-G01  finite closed degree-two component is cycle-like
TBF-X00  XOR transport respects path concatenation
TBF-X01  zero cycle sum gives path-independent integration
TBF-C00  nonzero boundary deltas recover adjacent-distinct four states
```

この段階まで到達すれば、今回の会話で得られた数学的核は四色定理の成否と独立して Lean に固定される。

---

## 16. 小規模回帰例

### 16.1 単一 Tromino kernel

```text
A B
C 0
```

期待:

$$
A\oplus B\oplus C=0
$$

### 16.2 even boundary

```text
A A B B C C
```

期待:

- XOR sum `0`
- residual empty
- all same-label pairable

### 16.3 odd boundary

```text
A A A B B B C C C
```

期待:

- XOR sum `0`
- pair 3 組
- residual `A,B,C`

### 16.4 invalid parity

```text
A A B C
```

各 label count parity は揃わない。

期待:

- XOR sum nonzero
- conserved boundary を満たさない

### 16.5 closed transition cycle

4 または 6 ports の小 transition graph を作り、cycle XOR が `0` の場合に base state へ戻ることを確認する。

---

## 17. 設計上の注意

### 17.1 色名をコア API に入れない

`red`, `green`, `blue`, `yellow` は例示にのみ使用し、コアは

```text
zero / A / B / C
```

または generic group element とする。

### 17.2 XOR に固定しすぎない

最初は `\mathbb F_2^2` でよいが、後に

```text
finite abelian group
finite torsor
voltage graph
flow
```

へ一般化可能かを意識する。

### 17.3 Euler path と混同しない

「一筆書き」は transition graph の path/cycle decomposition の直感名である。

元 graph の全 edge を Euler trail が一度ずつ通ることを、そのまま要求しているわけではない。

必要になった時点で Mathlib の Eulerian API と正確に接続する。

### 17.4 四色定理を早期に theorem 名へ入れない

まず `Tromino`, `Boundary`, `Transition`, `Transport` として実装し、十分な bridge が証明できた後に `FourColor` facade を作る。

これにより研究途中の誤解を避ける。

---

## 18. 将来の一般化

今回の構造は四色以外にも次の形で利用できる可能性がある。

```text
local finite-state constraint
  ↓
difference / transition labels
  ↓
conservation law
  ↓
local pairing
  ↓
path certificate
  ↓
global state reconstruction
```

候補分野:

- graph coloring
- tiling / polyomino completion
- finite automata on graphs
- parity constraint systems
- network flow
- error-correcting / syndrome style propagation
- gauge / voltage graph representations
- discrete cohomology の初等有限版

従って `Tromino` は単なる 3-cell polyomino の名称から、

> complete 4-state system から 1 状態を欠いた 3-state local conservation kernel

という DkMath 内部の抽象原理へ昇格する可能性がある。

---

## 19. 研究時の中心質問

今後の実装・調査では、特に次を判定する。

1. `3+1` geometry と `F₂²` nonzero triple を自然な共通 structure として抽象化すべきか。
2. boundary XOR conservation から pairing/residual decomposition をどこまで generic に証明できるか。
3. local pairings の集合を効率良く探索する canonical choice が存在するか。
4. planar cyclic order から non-crossing pairing を保証できる条件は何か。
5. ghost completion によって open boundary を closed transition system へ変換する最小条件は何か。
6. transition cycle XOR compatibility は local conservation だけから従うか、追加の global obstruction が必要か。
7. path certificate から coloring を復元する bridge はどの abstract graph level で最も短く書けるか。
8. arbitrary planar map に対する required flow/pairing existence が四色定理の既知同値命題へ帰着するのか、それとも別の有用な十分条件になるのか。

---

## 20. 要約

今回固定したい核心は次である。

$$
\boxed{3+1=2^2}
$$

を単なる面積等式ではなく

$$
\boxed{
\text{3-state residual + missing state = complete 4-state square}
}
$$

として読む。

その非零 3 状態は `F₂²` で

$$
A\oplus B\oplus C=0
$$

を満たし、boundary conservation は

$$
\boxed{n_A\equiv n_B\equiv n_C\pmod2}
$$

へ落ちる。

この parity structure から

```text
boundary ports
  ↓
pairs + optional A/B/C tromino residual
  ↓
transition paths / cycles
  ↓
XOR transport
  ↓
global four-state reconstruction
```

を構成する。

従って研究の標語は次とする。

> **塗り分けを直接探さない。境界を跨ぐ保存経路を探し、その経路から色を復元する。**

これを `DkMath.Tromino` の次世代 theorem family として実装予定に残す。
