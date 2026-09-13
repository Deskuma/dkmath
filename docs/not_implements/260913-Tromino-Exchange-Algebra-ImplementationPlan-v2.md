# Tromino Exchange Algebra / Four-State Local Solver 実装計画書 2

- Status: implementation plan / not implemented
- Date: 2026-09-13
- Branch at recording: `develop`
- Repository: `Deskuma/dkmath`
- Existing geometric base: `lean/dk_math/DkMath/Tromino.lean`
- Previous plan: `docs/not_implements/260912-Tromino-BoundaryFlow-FourColor-ImplementationPlan.md`
- Target area: `DkMath.Polyomino.Tromino`, future `DkMath.Tromino.*` algebra / solver layer
- Theme: `3 + 1 = 4 = 2^2`, Klein four-state exchange, local rescue, orbit search, boundary path solver

## 1. 目的

本資料は、前計画書で得た

```text
Tromino
  ↓
boundary flow
  ↓
IN / OUT pairing
  ↓
transition graph
  ↓
path / cycle
  ↓
color recovery
```

という流れのさらに下層にある、`DkMath.Tromino.*` の本来の代数核を先に固定するための実装計画書 2 である。

今回の中心は四色定理そのものの再証明ではない。

四色で塗り分け可能であることは既知として、その事実の背後から次の局所演算則を抽出する。

```text
1 current state
+ 3 waiting / exchange states
= 4 states
= 2^2
```

すなわち、幾何 L 型トロミノの

$$
3+1=4
$$

を、有限状態・交換演算・群作用へ持ち上げる。

最終的な研究目標は次である。

> 局所ピースが隣接禁止色に突き当たったとき、現在配置を捨てて探索し直すのではなく、有限な Tromino exchange orbit の中から合法な交換候補を代数的に選び、境界制約を局所的に解消する。

これを土台として、前計画書の boundary transition graph / path search と接続し、彩色を直接総当たりするのではなく、有限群作用と経路証明書から色を復元する solver を構成する。

---

## 2. 現在の幾何 Tromino と新しい状態 Tromino

現在の `DkMath/Tromino.lean` には、既に次の幾何核がある。

```text
L_tromino
I_tromino
block2
hole2
block2 = L_tromino ∪ hole2
Disjoint L_tromino hole2
area L_tromino = 3
area hole2 = 1
area block2 = 4
rotation / reflection / translation
```

したがって幾何側では既に

$$
4=3+1
$$

が固定されている。

本計画ではこれを状態空間へ写す。

$$
\mathcal C := \mathbb F_2^2
$$

具体的には

$$
\mathcal C=\{00,01,10,11\}.
$$

ここで一つの現在状態 `x` に対し、残る三状態を waiting states とする。

$$
W(x):=\mathcal C\setminus\{x\}.
$$

従って

$$
|\{x\}|=1,
\qquad
|W(x)|=3,
\qquad
|\mathcal C|=4.
$$

この

$$
\boxed{1+3=4=2^2}
$$

を `TrominoStateKernel` の第一原理とする。

---

## 3. Mathlib 基盤: Klein 四元群

Mathlib には

```lean
Mathlib.GroupTheory.SpecificGroups.KleinFour
```

があり、加法版

```lean
IsAddKleinFour
```

が実装済みである。

さらに

```lean
ZMod 2 × ZMod 2
```

には `IsAddKleinFour` instance が既に存在する。

したがって第一実装では独自4元群を作らず、次を基底候補とする。

```lean
abbrev TrominoState := ZMod 2 × ZMod 2
```

この型では加法が XOR と同じ役割を持つ。

任意の `δ : TrominoState` に対して交換作用を

$$
T_\delta(x):=x+\delta
$$

と定義する。

特性2より

$$
\delta+\delta=0
$$

なので

$$
T_\delta\circ T_\delta=\operatorname{id}.
$$

また

$$
T_\alpha\circ T_\beta=T_{\alpha+\beta}
$$

かつ

$$
T_\alpha\circ T_\beta=T_\beta\circ T_\alpha.
$$

従って交換操作群は

$$
(\mathcal C,+)\cong V_4
$$

すなわち Klein 四元群である。

### 3.1 操作の意味

`δ = 0` は「現在配置を維持する」操作。

`δ ≠ 0` の三状態は「現在状態から別状態へ移る待機交換操作」である。

```text
δ = 0        keep current
δ = A        exchange direction A
δ = B        exchange direction B
δ = C        exchange direction C
```

従って操作側でも

$$
1\text{ identity}+3\text{ exchanges}=4
$$

が現れる。

---

## 4. Waiting set と交換候補

現在状態 `x` に対して

```lean
def waitingStates (x : TrominoState) : Finset TrominoState :=
  Finset.univ.erase x
```

を候補とする。

最初に固定すべき定理は次である。

```lean
card_state_univ_eq_four
card_waitingStates_eq_three
mem_waitingStates_iff_ne
```

数学的には

$$
|\mathcal C|=4,
\qquad
|W(x)|=3.
$$

また任意の `y ≠ x` に対し

$$
\delta=x+y
$$

と置けば

$$
x+\delta=y.
$$

しかも `δ ≠ 0` であり、`δ` は一意である。

候補 theorem:

```lean
existsUnique_nonzero_exchange_to
```

主張:

```text
x ≠ y
→ ∃! δ, δ ≠ 0 ∧ x + δ = y
```

これは「任意の別色には、唯一の非零交換操作で移れる」ことを表す。

---

## 5. Tromino Exchange Law

交換作用

```lean
def exchange (δ x : TrominoState) : TrominoState := x + δ
```

に対し、次を基本則とする。

```lean
exchange_zero
exchange_self_inverse
exchange_comp
exchange_commute
exchange_ne_of_nonzero
exchange_eq_iff
```

数学的には

$$
T_0(x)=x,
$$

$$
T_\delta(T_\delta(x))=x,
$$

$$
T_\alpha(T_\beta(x))=T_{\alpha+\beta}(x),
$$

$$
T_\alpha T_\beta=T_\beta T_\alpha.
$$

これを `Tromino Exchange Law` と呼ぶ。

ここで重要なのは、交換は単一要素を別要素へ置換する ad-hoc 操作ではなく、4状態全体に閉じた群作用であることである。

---

## 6. 禁止色集合に対する Rescue theorem

局所環境が禁止する状態集合を

$$
B\subseteq\mathcal C
$$

とする。

現在状態 `x` から交換 `δ` を行った後の状態は

$$
x+\delta.
$$

`B` が全4状態を占めていなければ、必ず合法状態が残る。

$$
B\ne\mathcal C
\Longrightarrow
\exists\delta,\quad x+\delta\notin B.
$$

さらに現在状態自体が禁止されている、すなわち

$$
x\in B
$$

ならば、救済交換は恒等操作ではあり得ないため

$$
\boxed{
 x\in B\land B\ne\mathcal C
 \Longrightarrow
 \exists\delta\ne0,\quad x+\delta\notin B
}
$$

を得る。

候補 theorem:

```lean
exists_exchange_avoiding_forbidden
exists_nonzero_exchange_rescue
```

これを `TrominoExchangeRescue` の最小版とする。

### 6.1 候補数

平行移動 `δ ↦ x + δ` は全単射なので、交換候補数は禁止状態数だけで決まる。

$$
\#\{\delta\mid x+\delta\notin B\}=4-|B|.
$$

従って

```text
forbidden 0 → candidate 4
forbidden 1 → candidate 3
forbidden 2 → candidate 2
forbidden 3 → candidate 1
forbidden 4 → candidate 0
```

である。

候補 theorem:

```lean
card_exchange_candidates_eq_four_sub_card_forbidden
```

`|B| = 3` では救済操作が一意となる。

これは四色囲碁的には forced move / liberty one に対応する。

---

## 7. ピース全体に対する Boundary Exchange Rescue

前節は1状態についての定理である。

今回本当に欲しいのは、彩色済み局所ピース全体を一つの交換量 `δ` で動かす定理である。

局所ピースのセル集合を `P`、内部彩色を

$$
c_P:P\to\mathcal C
$$

とする。

`δ` による一様交換を

$$
(c_P+\delta)(p):=c_P(p)+\delta
$$

とする。

一様交換は内部の異色関係を保存する。

隣接セル `p,q` に対して

$$
c_P(p)\ne c_P(q)
$$

なら、加法消去律より

$$
c_P(p)+\delta\ne c_P(q)+\delta.
$$

従って局所ピース内部の proper coloring は全 `δ` で不変である。

候補 theorem:

```lean
proper_internal_preserved_by_exchange
```

### 7.1 各境界接触は一つの `δ` だけを禁止する

ピース側境界セル `p` が外部状態 `e` に接するとする。

交換後に衝突する条件は

$$
c_P(p)+\delta=e.
$$

従ってこの境界接触が禁止する交換量は一意に

$$
\delta=e+c_P(p)
$$

である。

すなわち、境界接触一つは「四色全部を禁止する」のではなく、交換群 `V_4` の中の一つの `δ` だけを禁止する。

これを全境界接触について集め、

$$
F(P):=\{e+c_P(p)\mid (p,e)\text{ is a boundary contact}\}
$$

を `forbiddenExchangeSet` とする。

この集合が全群を覆わない限り、合法な一様交換が存在する。

$$
\boxed{
F(P)\ne\mathcal C
\Longrightarrow
\exists\delta\notin F(P),
\quad
c_P+\delta
\text{ is boundary-compatible}
}
$$

さらに現在配置 `δ=0` が衝突しているなら

$$
0\in F(P)
$$

であるから、合法解は必ず非零交換となる。

これを本計画の中心定理候補とする。

```lean
boundary_contact_forbids_unique_exchange
boundary_compatible_iff_delta_not_mem_forbiddenExchangeSet
exists_piece_exchange_rescue_of_forbidden_ne_univ
exists_nonzero_piece_exchange_rescue_of_current_conflict
```

この定理は「隣接禁止色に突き当たったら、群内に交換候補がある」という直感を、局所ピース全体について正確に表現する。

**成立条件は `forbiddenExchangeSet ≠ univ` である。**

全4交換量が異なる境界接触によって禁止された場合は、加法交換だけでは救済できない。

その場合は次節のより大きな対称群へ進む。

---

## 8. 非零3方向の交換: `GL(2,2) ≃ S₃`

Klein 四元群の加法交換は4状態間の translation である。

これとは別に、零状態を固定し、三つの非零方向

$$
A,B,C
$$

を交換する自己同型群がある。

$$
\operatorname{Aut}(V_4)\cong GL(2,\mathbb F_2)\cong S_3.
$$

役割を分ける。

```text
V₄       : current state を4状態間で移動する
S₃       : A/B/C の3交換方向を組み替える
```

従って

```text
current 1
waiting 3
```

の `waiting 3` 自体にも交換対称性がある。

候補概念:

```lean
TrominoLinearSymmetry
permuteNonzeroDirections
```

候補 theorem:

```lean
linearSymmetry_fix_zero
linearSymmetry_permutes_nonzero
linearSymmetry_preserves_addition
linearSymmetry_preserves_distinctness
```

この層は `TrominoExchangeRescue` の第二段救済候補として使う。

---

## 9. 全四色対称性: affine action と `S₄`

translation `V₄` と linear symmetry `GL(2,2)` を合わせると affine action

$$
x\mapsto Lx+b
$$

が得られる。

概念的には

$$
AGL(2,2)\cong V_4\rtimes GL(2,2)\cong S_4.
$$

位数は

$$
4\cdot6=24.
$$

従って四色全体の permutation freedom を

```text
translation exchange : 4
nonzero direction relabel : 6
full affine color symmetries : 24
```

として階層化できる。

第一実装では `S₄` 同型そのものを必須にしない。

まず

```text
translation action
linear automorphism action
affine action
```

を API として分離し、局所 solver に必要な有限候補集合が得られることを優先する。

---

## 10. 空間側の回転・反転と色側の対称性

既存 `Tromino.lean` には既に平面上の

```text
rotate90
rotate180
rotate270
reflectX
reflectY
```

が存在する。

従って一つの局所ピースは、少なくとも次の二種類の自由度を持つ。

```text
spatial symmetry
color symmetry
```

空間側を正方形対称群 `D₄` として整理し、色側を affine four-state symmetry として整理する。

独立作用として扱える範囲では、局所候補は

$$
D_4\times AGL(2,2)
$$

の orbit として調べられる。

最大でも形式上

$$
8\cdot24=192
$$

候補である。

ただし実際には stabilizer により重複が多く、orbit representative に圧縮できる。

候補概念:

```lean
SpatialOrientation
ColorAffineAction
TrominoPlacementOrbit
```

候補 theorem:

```lean
internal_proper_preserved_by_spatial_symmetry
internal_proper_preserved_by_color_affine
legal_of_legal_spatial_color_action
```

この有限 orbit が「一度置いた後でも、回転・反転・色交換で置き直せる」ことの形式化になる。

---

## 11. Ring / Field 層の位置づけ

今回必要な最小構造は additive Klein group であり、乗法は不要である。

従って第一実装では

$$
\mathcal C=\mathbb Z_2\times\mathbb Z_2
$$

の加法群を標準表現とする。

ただし4元体

$$
\mathbb F_4
$$

へ持ち上げると、非零3元が乗法群

$$
\mathbb F_4^\times\cong C_3
$$

を形成するため、三つの待機方向を巡回させる演算を自然に持てる。

Mathlib には有限 Galois field 用の `GaloisField` が存在するので、第二段階で

```text
additive V₄ layer
      ↓ optional equivalence
GF(4) field layer
```

を検討する。

Field 層で期待する意味:

```text
addition       : current state exchange
nonzero multiplication : three waiting directions rotation
Frobenius      : direction reflection / conjugation candidate
```

ただし、この field 解釈が solver を単純化しない場合は導入しない。

「群・環・体っぽさ」を一度に実装するのではなく、必要な構造だけを最小 hierarchy として採用する。

---

## 12. Typed Hole / reversible removal

局所トロミノを取り除いた空白は無情報な穴ではない。

```text
geometry fixed
piece identity fixed
color state deferred
```

という typed hole である。

概念的には

```lean
structure TrominoHole where
  footprint : Shape
  piece : TrominoPiece
  admissibleActions : Finset TrominoAction
```

のように、何を戻すかと許される orbit を保存する。

取り除く操作 `remove` と復元 `restore` は、彩色値を即座に確定せずとも、piece identity と境界 action space を保持する。

候補 theorem:

```lean
restore_remove
remove_restore_of_admissible
```

この可逆性が、前計画書の peeling / reverse expansion と接続する。

---

## 13. Local Solver

今回の代数層を使い、局所 solver を次の順序で構成する。

```text
input:
  placed piece
  current orientation
  current color action
  external boundary colors

1. compute boundary contacts
2. compute forbidden translation deltas
3. if some delta survives, choose one
4. otherwise try nonzero-direction relabel / affine action
5. otherwise try spatial rotation / reflection
6. enumerate only orbit representatives
7. return legal action certificate or local obstruction certificate
```

第一段はわずか4交換量なので定数時間の有限判定として扱える。

第二段まで含めても色作用は24個、空間対称性を含めても有限で小さい。

ここではまだ全体問題の計算量について主張しない。

局所 solver が `decide` / finite enumeration で完全判定可能であることをまず証明する。

候補 API:

```lean
forbiddenExchangeSet
availableExchanges
chooseExchange?
localPlacementOrbit
legalLocalActions
solveLocal?
```

候補 theorem:

```lean
chooseExchange?_sound
chooseExchange?_complete
solveLocal?_sound
solveLocal?_complete_on_orbit
```

---

## 14. Boundary Path Solver への接続

前計画書では、boundary ports を IN / OUT pairing し、派生 transition graph を path / cycle に分解する構想を記録した。

今回の exchange algebra は、その各局所 node で用いる状態更新器になる。

```text
transition path enters piece
  ↓
read incoming constraint
  ↓
select local Tromino action
  ↓
exchange / rotate / reflect
  ↓
produce outgoing compatible state
  ↓
continue path
```

つまり path search の各 step が、単なる branch ではなく有限群作用の選択になる。

最終像:

```text
boundary structure
  ↓
transition graph
  ↓
path / cycle decomposition
  ↓
local Tromino exchange solver at each node
  ↓
cycle consistency
  ↓
global state recovery
```

この構成を「瞬間塗り分け」の数学的候補とする。

ここで「瞬間」とは、現時点では計算量クラスの主張ではなく、色を一面ずつ trial-and-error する代わりに、局所有限代数と経路証明書によって一括復元する設計を意味する。

---

## 15. 四色囲碁モデル

研究補助として「四色囲碁」を有限ゲームとして実装すると、局所法則の探索に使える可能性がある。

一手は

```text
piece placement
+ spatial orientation
+ color action
```

である。

合法条件は共有境界上で同色接触が存在しないこと。

各手の freedom は

```text
current action
waiting exchange actions
spatial orbit
```

として表示する。

境界自由度を `liberties` として

$$
L(P):=\{a\mid a\text{ is a legal local action}\}
$$

と定義できる。

```text
|L(P)| = 0  local obstruction
|L(P)| = 1  forced move
|L(P)| > 1  flexible state
```

このゲーム側の exhaustive enumeration から、一般 lemma 候補や最小 obstruction を発見し、Lean 側で証明へ昇格する流れを想定する。

---

## 16. 実装モジュール案

既存の幾何ファイルを壊さず、次のように分割する。

```text
DkMath/
  Tromino.lean                       -- geometric facade / existing
  Tromino/
    State.lean                       -- 4 states / waiting 3
    KleinExchange.lean               -- V₄ translation action
    ExchangeRescue.lean              -- forbidden-set rescue
    PieceExchange.lean               -- uniform exchange on a colored piece
    ColorSymmetry.lean               -- GL(2,2), affine action
    SpatialSymmetry.lean             -- D₄ normalization over existing rotations/reflections
    PlacementOrbit.lean              -- spatial × color orbit
    TypedHole.lean                   -- reversible removal / deferred color
    LocalSolver.lean                 -- finite certified solver
    BoundaryBridge.lean              -- bridge to previous TBF plan
    FieldModel.lean                  -- optional GF(4) layer, later
```

namespace は既存の

```lean
DkMath.Polyomino.Tromino
```

を当面維持する。

ただし algebra layer が幾何 Shape に依存しなくなった場合は

```lean
DkMath.Tromino
```

への再配置を検討する。

この判断は実装初期 survey で行う。

---

## 17. 実装フェーズ

### TEA-000: API survey

調査:

- `Mathlib.GroupTheory.SpecificGroups.KleinFour`
- `IsAddKleinFour`
- `ZMod 2 × ZMod 2`
- finite group action / orbit API
- `Equiv.Perm`, `MulAction`, additive action API
- `GL(2,2)` を直接使うか `AddEquiv` / permutation で軽く持つか
- `GaloisField 2 2` の実用性
- existing `Tromino.lean` rotation / reflection API

Outcome:

- `TrominoState` 表現決定
- exchange action 表現決定
- color symmetry 表現決定
- module namespace 決定

### TEA-001: four-state kernel

実装:

```lean
TrominoState
waitingStates
```

証明:

```lean
card_state_univ_eq_four
card_waitingStates_eq_three
mem_waitingStates_iff_ne
```

### TEA-002: Klein exchange law

実装:

```lean
exchange
```

証明:

```lean
exchange_zero
exchange_self_inverse
exchange_comp
exchange_commute
existsUnique_nonzero_exchange_to
```

### TEA-003: forbidden-state rescue

実装:

```lean
availableExchanges
```

主定理:

```lean
exists_exchange_avoiding_forbidden
exists_nonzero_exchange_rescue
card_exchange_candidates_eq_four_sub_card_forbidden
```

### TEA-004: colored piece uniform exchange

抽象 `ColoredPiece` と一様交換を定義。

証明:

```lean
proper_internal_preserved_by_exchange
boundary_contact_forbids_unique_exchange
```

### TEA-005: piece boundary rescue

`forbiddenExchangeSet` を定義。

主定理:

```lean
boundary_compatible_iff_delta_not_mem_forbiddenExchangeSet
exists_piece_exchange_rescue_of_forbidden_ne_univ
exists_nonzero_piece_exchange_rescue_of_current_conflict
```

ここを v2 の第一到達点とする。

### TEA-006: color automorphisms

- nonzero three-direction permutation
- additive automorphisms
- optional `GL(2,2)` bridge
- affine four-state action

証明:

```lean
color_action_preserves_ne
color_action_preserves_internal_proper
```

### TEA-007: spatial symmetry normalization

既存 rotation / reflection を `D₄` 的有限 orientation としてまとめる。

- canonical orientation list
- duplicate elimination
- shape / adjacency preservation

### TEA-008: placement orbit solver

```lean
localPlacementOrbit
legalLocalActions
solveLocal?
```

を実装。

soundness / finite completeness を証明。

### TEA-009: boundary-flow bridge

前計画 `TBF-*` と接続。

- transition node に `LocalSolver` を持たせる
- path traversal で action を伝播
- closed cycle consistency
- state recovery

### TEA-010: GF(4) experiment

必要な場合のみ実施。

- `GaloisField 2 2`
- additive state equivalence
- nonzero multiplicative `C₃`
- waiting-direction rotation
- Frobenius action

Outcome A:

solver API が簡潔になるなら production に採用。

Outcome B:

説明モデルとしてのみ保持。

---

## 18. 最小 theorem set

最初に CI-GREEN にしたい theorem 群。

```text
TEA-K00  |State| = 4
TEA-K01  |waitingStates x| = 3
TEA-K02  x ≠ y → unique nonzero δ with x + δ = y

TEA-E00  exchange 0 x = x
TEA-E01  exchange δ (exchange δ x) = x
TEA-E02  exchange α (exchange β x) = exchange (α + β) x
TEA-E03  exchange α (exchange β x) = exchange β (exchange α x)

TEA-R00  forbidden ≠ univ → ∃ δ, x + δ ∉ forbidden
TEA-R01  x ∈ forbidden ∧ forbidden ≠ univ
         → ∃ δ ≠ 0, x + δ ∉ forbidden
TEA-R02  candidate count = 4 - forbidden count

TEA-P00  uniform exchange preserves internal proper coloring
TEA-P01  one boundary contact forbids exactly one exchange δ
TEA-P02  boundary compatibility ↔ δ ∉ forbiddenExchangeSet
TEA-P03  forbiddenExchangeSet ≠ univ → piece exchange rescue exists
TEA-P04  current conflict + forbiddenExchangeSet ≠ univ
         → nonzero piece exchange rescue exists
```

この `TEA-P04` を今回の会話から抽出した第一主定理候補とする。

---

## 19. 小規模回帰例

### 19.1 current + waiting three

```text
current = 0
waiting = {1,2,3}
```

期待:

```text
card waiting = 3
```

### 19.2 one forbidden state

```text
forbidden = {0}
current = 0
```

期待:

```text
available nonzero exchanges = {1,2,3}
card = 3
```

### 19.3 three forbidden states

```text
forbidden = {0,1,2}
current = 0
```

期待:

```text
unique rescue = 3
```

### 19.4 all four forbidden

```text
forbidden = {0,1,2,3}
```

期待:

```text
no additive exchange rescue
```

この case は theorem の失敗ではなく、上位 symmetry / spatial reorientation へ進む marker とする。

### 19.5 piece boundary contact

局所ピースの2境界接触が禁止する exchange を `1`, `3` とする。

```text
forbiddenExchangeSet = {1,3}
available = {0,2}
```

現在 `0` が合法なら維持可能。

現在配置が別の接触追加で `0` も禁止され

```text
forbiddenExchangeSet = {0,1,3}
```

となれば `2` が唯一の rescue となる。

---

## 20. 前計画書との役割分担

計画書1 `Tromino Boundary Flow / Four-Color Path Reduction` は大域側を扱う。

```text
boundary
pairing
transition graph
path / cycle
XOR transport
color recovery
```

本計画書2 `Tromino Exchange Algebra` は局所側を扱う。

```text
4-state kernel
current + waiting three
Klein exchange
forbidden exchange set
piece rescue
color / spatial orbit
local certified solver
```

両者は最終的に

```text
local algebra
  ↓
local certified action
  ↓
boundary transition
  ↓
path / cycle solver
  ↓
global recovery
```

として統合する。

---

## 21. 研究上の境界線

本計画の時点で、次はまだ主張しない。

- 任意の局所配置で additive `V₄` exchange だけが必ず成功すること
- 全4 exchange が禁止された場合でも affine / spatial orbit に必ず合法解があること
- 局所 solver の成功だけで任意の planar coloring が greedy に完成すること
- path solver の計算量が線形時間・対数時間・定数時間になること
- 量子計算に対する計算量上の優位性

まず証明するのは、有限群作用による局所状態空間の正確な構造と、成立条件つき rescue theorem である。

その後、どの planar / boundary 条件が

```text
forbiddenExchangeSet ≠ univ
```

を保証するかを探索する。

この条件の抽出こそ、Tromino 生成・除去・四色境界問題を結ぶ次の数学的課題である。

---

## 22. 最終像

`DkMath.Tromino.*` を単なる L 型ポリオミノの幾何ライブラリから、次の階層へ拡張する。

```text
Geometric Tromino
  3 cells + 1 gap
        ↓
Four-State Tromino Kernel
  1 current + 3 waiting
        ↓
Klein Exchange Algebra
  V₄ action
        ↓
Piece Exchange Rescue
  forbidden exchange set
        ↓
Color / Spatial Orbit
  S₃ / affine / D₄
        ↓
Certified Local Solver
        ↓
Boundary Transition Graph
        ↓
Path / Cycle Solver
        ↓
Global State Recovery
```

中心標語:

> **色を塗り直すのではなく、トロミノ状態を群内で交換する。**

> **境界衝突は交換群の一部を禁止する制約として読む。全交換が禁止されない限り、合法な交換候補は群内に残る。**

> **局所交換を path / cycle 上で運び、最後に色を復元する。**

この代数核が確立すれば、前計画書の経路探索アルゴリズムへ直接接続し、四色塗り分けを有限状態群作用の証明書として扱う研究へ進む。
