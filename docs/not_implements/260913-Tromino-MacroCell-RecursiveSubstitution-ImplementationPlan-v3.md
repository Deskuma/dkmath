# Tromino Macro-Cell / Recursive Substitution 実装計画書 3

- Status: implementation plan / not implemented
- Date: 2026-09-13
- Branch at recording: `develop`
- Repository: `Deskuma/dkmath`
- Existing geometric base: `lean/dk_math/DkMath/Tromino.lean`
- Previous plan 1: `docs/not_implements/260912-Tromino-BoundaryFlow-FourColor-ImplementationPlan.md`
- Previous plan 2: `docs/not_implements/260913-Tromino-Exchange-Algebra-ImplementationPlan-v2.md`
- Target area: `DkMath.Polyomino.Tromino`, future `DkMath.Tromino.*`
- Theme: `3 + 1 = 4 = 2^2`, four-state macro-cell, typed gap, recursive substitution, reversible peel / restore

## 1. 目的

本資料は、実装計画書 2 で整理した四状態交換代数の上に、今回新しく現れた「尺度を一段上げる Tromino macro-cell」を追加するための計画書 3 である。

今回の核心は、原子セルの四色配置

```text
🟦🟩
🟨🟥
```

を一個の抽象セル `M` とみなし、その `M` を単位として再び

```text
[M][□]
[M][M]
```

という L 型 Tromino を構成できる、という再帰構造にある。

ここで `□` は単なる空白ではない。

```text
ここには M が戻る
```

と型付けされた `TypedGap M` である。

従って今回の理論は

```text
atomic four-color cell
  ↓ quotient / abstraction
macro monomino M
  ↓
3 Body + 1 TypedGap
  ↓
macro L-tromino
  ↓
peel / restore
  ↓
recursive substitution
```

を Lean 上で固定することを目的とする。

---

## 2. 観測例

次のような四色配置を考える。

```text
🟦🟩🟦🟩🟦🟩🟦🟩
🟨🟥🟨🟥🟨🟥🟨🟥
🟦🟩🟦🟦🟩🟩🟦🟩
🟨🟥🟦🟦🟩🟩🟨🟥
🟦🟩🟨🟨🟥🟥🟦🟩
🟨🟥🟨🟨🟥🟥🟨🟥
🟦🟩🟦🟩🟦🟩🟦🟩
🟨🟥🟨🟥🟨🟥🟨🟥
```

中央 `4 × 4` を抜き取ると、局所的に

```text
🟦🟩⬜️⬜️
🟨🟥⬜️⬜️
🟦🟩🟦🟩
🟨🟥🟨🟥
```

となる。

ここで

```text
M :=
🟦🟩
🟨🟥
```

を一個の抽象セルとして読むと、上の `4 × 4` は

```text
[M][□]
[M][M]
```

となる。

従って原子レベルでは `4 × 4 = 16` セルであるが、macro level では

$$
3M + 1G = 4M
$$

であり、再び

$$
3+1=4=2^2
$$

が現れる。

---

## 3. Atomic Four-Color Cell

最初の基本単位を `FourColorCell` とする。

概念上は

```lean
structure FourColorCell where
  shape : Shape
  color : Cell → TrominoState
  complete : /* 4 states appear exactly once */
```

のような対象を想定する。

最小具体例は `2 × 2` block で、四状態

$$
\mathcal C = \mathbb F_2^2
$$

を一回ずつ持つ。

代表例:

$$
M=
\begin{pmatrix}
00 & 01\\
10 & 11
\end{pmatrix}.
$$

色名では

```text
🟦🟩
🟨🟥
```

に対応する。

ここで重要なのは、`M` の内部配置そのものより

```text
- 4 states are complete
- outer boundary is known
- translations / rotations / reflections / exchanges act on it
```

という invariant である。

---

## 4. Macro Monomino

`FourColorCell M` 全体を、一段上の格子では一個の抽象セルとみなす。

原子面積を `area₀`、macro count を `area₁` と区別すると

$$
\text{area}_0(M)=4,
\qquad
\text{area}_1(M)=1.
$$

この abstraction を

```text
atomic 2×2 four-color block
  ↓ collapse
macro monomino M
```

と読む。

候補概念:

```lean
MacroCell
FourColorMacroCell
collapseFourColorCell
expandMacroCell
```

重要な設計条件は、collapse / expand が互いに対応することである。

概念的には

$$
\text{expand}(\text{collapse}(M)) = M.
$$

---

## 5. Typed Gap

macro Tromino の Gap は単なる空集合ではない。

```text
□ : TypedGap M
```

とし、

```text
この位置には M 型のピースが戻る
```

という復元情報を保持する。

従って Gap は

```text
geometry missing
state deferred
replacement type fixed
```

という三つの性質を持つ。

概念候補:

```lean
structure TypedGap (α : Type*) where
  footprint : Shape
  expected : α
```

あるいは geometry と restore certificate を分離して

```lean
structure RestoreSlot where
  footprint : Shape
  witnessType : Type
```

のような表現も比較する。

第一実装では dependent type を過度に使わず、復元対象 ID と footprint を持つ軽量構造から始めてもよい。

---

## 6. Macro Tromino Kernel

macro monomino `M` を単位として

```text
[M][□]
[M][M]
```

を作る。

Body は 3 個の `M`、Gap は 1 個の `TypedGap M`。

従って

$$
\text{BodyCount}=3,
\qquad
\text{GapCount}=1,
\qquad
\text{TotalCount}=4.
$$

原子セルへ展開すれば

$$
3\cdot4 + 1\cdot4 = 16 = 4^2.
$$

すなわち

$$
4(3+1)=4^2.
$$

この scale-preserving relation を今回の主要 invariant とする。

候補 theorem:

```lean
macro_body_count_eq_three
macro_gap_count_eq_one
macro_total_count_eq_four
atomic_area_macro_tromino_eq_sixteen
macro_three_plus_one_eq_four
```

---

## 7. 再帰 substitution

`M₀` を atomic four-color cell とする。

一段上で `M₀` を一個の macro-cell として扱い、

$$
T_1 = 3M_0 + 1G_0
$$

を構成する。

さらに `T₁` またはその完成版を一個の上位 macro-cell `M₁` とみなせる条件を抽出する。

一般に

$$
M_k \leadsto T_{k+1}=3M_k+1G_k.
$$

完成後の全体を `M_{k+1}` と抽象化できるなら、

$$
\text{area}(M_{k+1})=4\text{area}(M_k).
$$

従って

$$
\text{area}(M_k)=4^{k+1}
$$

型の再帰が現れる。

ただし「完成版を次段 macro-cell として使える」ためには、境界色 signature / orientation compatibility が保存される必要がある。

これを未証明の主要条件として分離する。

候補概念:

```lean
TrominoSubstitution
SubstitutableMacroCell
MacroBoundarySignature
substitution_preserves_signature
```

---

## 8. Peel / Restore の可逆性

中央 macro-cell を抜く操作を `peel` とする。

```text
[M][M]      [M][□]
[M][M]  →   [M][M]
```

ただし実際には抜く位置・orientation は任意の admissible slot を許す。

重要なのは、抜いた後に `TypedGap M` が残ること。

そのため

```text
peel
  ↓
typed hole
  ↓
restore
```

が構成可能である。

狙うべき基本定理は

$$
\text{restore}(\text{peel}(X))=X
$$

である。

さらに admissibility を仮定して

$$
\text{peel}(\text{restore}(G))=G
$$

も検討する。

これは完全な群逆元というより、partial equivalence / reversible rewrite rule に近い。

候補 theorem:

```lean
restore_peel
peel_restore_of_admissible
peel_preserves_outer_boundary
restore_preserves_outer_boundary
```

---

## 9. Boundary signature

macro-cell を一個の抽象セルへ潰すには、外側から見て内部詳細を忘れてもよい必要がある。

従って `MacroBoundarySignature M` を定義し、少なくとも次を保持する。

```text
- boundary shape
- cyclic order of boundary contacts
- four-state / delta labels
- admissible exchange orbit
- orientation class
```

二つの内部構造 `X`, `Y` が同じ boundary signature を持つとき

$$
X \sim_{\partial} Y
$$

とする。

collapse の安全性は

$$
X\sim_{\partial}M
$$

により保証する。

この boundary equivalence は前計画書の BoundaryFlow と直接接続する。

---

## 10. Exchange Algebra との統合

実装計画書 2 の交換作用

$$
T_\delta(x)=x+\delta
$$

を macro-cell 全体へ点wise に作用させる。

$$
(T_\delta M)(p)=M(p)+\delta.
$$

従って macro-cell の内部四状態完全性は保存される。

また boundary contact ごとに禁止される `δ` を集めた forbidden set

$$
F(M)\subseteq V_4
$$

を持つ。

$$
F(M)\ne V_4
$$

なら合法 exchange が存在する。

回転・反転も含めると、局所 solver は

```text
1. current orientation / color state
2. forbidden contacts
3. V4 exchange orbit
4. GL(2,2) / S3 relabeling if needed
5. D4 rotation / reflection if needed
6. choose admissible representative
```

として構成できる。

macro-cell の再帰 substitution と exchange orbit が両立するかを重要な検証項目とする。

候補 theorem:

```lean
exchange_preserves_complete_four_state
exchange_preserves_macro_shape
exchange_preserves_macro_signature
exists_exchange_rescue_of_macro_forbidden_ne_univ
```

---

## 11. Recursive Peeling と Coloring Certificate

複雑な領域を macro Tromino 単位で順次 peel する。

$$
G_0 \to G_1 \to \cdots \to G_n.
$$

各 step は

```text
- removable macro-cell found
- surrounding signature admissible
- typed gap inserted
- restore certificate stored
```

を満たす。

最後に小さい核 `K = G_n` が残る。

その後 restore certificate を逆順に再生する。

$$
K \to G_{n-1} \to \cdots \to G_0.
$$

この reduction history 自体を証明書とする。

候補:

```lean
structure PeelStep where
  before : Region
  after : Region
  gap : TypedGap ...
  restore : ...

structure PeelCertificate where
  steps : List PeelStep
  terminal : Region
```

最終的には

```lean
PeelCertificate G K
→ ValidTerminal K
→ RestorableColoring G
```

の形を狙う。

---

## 12. 前計画書との統合図

今回の三計画書は次の階層で統合する。

```text
Plan v3: MacroCell / Recursive Substitution
    ↓
Plan v2: Tromino Exchange Algebra / Local Solver
    ↓
Plan v1: Boundary Flow / Transition Graph
    ↓
Path / Cycle Search
    ↓
Color Recovery
```

より正確には相互作用するため

```text
Atomic Four-State Cell
    ↓ collapse
MacroCell
    ↓ 3+1
Macro Tromino
    ↔ Exchange Orbit
    ↔ Rotation / Reflection
    ↓ Peel / Restore
Boundary Signature
    ↓
Boundary Pairing
    ↓
Transition Graph
    ↓
Path / Cycle Certificate
    ↓
Global Reconstruction
```

とする。

---

## 13. 推奨 Lean モジュール構成

既存 `DkMath.Tromino` を facade とし、以下を候補とする。

```text
DkMath/
  Tromino.lean
  Tromino/
    State.lean
    Exchange.lean
    FourColorCell.lean
    MacroCell.lean
    TypedGap.lean
    Substitution.lean
    PeelRestore.lean
    BoundarySignature.lean
    Boundary.lean
    BoundaryPairing.lean
    TransitionGraph.lean
    Solver.lean
```

既存 namespace `DkMath.Polyomino.Tromino` との互換を壊さず、抽象代数層の独立性が高まった時点で facade を `DkMath.Tromino` 側へ整理することも検討する。

---

## 14. 実装フェーズ案

### Phase TMR-000: survey / representation

- `Tromino.lean` 現行 geometric API を再確認
- `IsAddKleinFour` / `ZMod 2 × ZMod 2` を state base に採用
- macro-cell の footprint 表現を決める
- scale / quotient coordinate の表現を比較

### Phase TMR-001: FourColorCell

- `2 × 2` atomic block
- 4 states exactly once
- translations preserve completeness
- exchange preserves completeness

### Phase TMR-002: MacroCell

- atomic block → abstract cell
- collapse / expand
- area relation `4 ↔ 1 macro`

### Phase TMR-003: TypedGap

- footprint
- expected macro-cell
- restore witness

### Phase TMR-004: Macro Tromino

- 3 macro body cells + 1 typed gap
- `3 + 1 = 4`
- atomic area `12 + 4 = 16`

### Phase TMR-005: Peel / Restore

- removable predicate
- peel
- restore
- `restore_peel`

### Phase TMR-006: Boundary Signature

- outer boundary observer
- signature equivalence
- collapse safety

### Phase TMR-007: Exchange Integration

- V4 exchange on macro-cell
- forbidden exchanges from boundary contacts
- rescue theorem
- D4 orientation integration

### Phase TMR-008: Recursive substitution

- `M_k → T_{k+1}`
- scale relation
- signature preservation experiments

### Phase TMR-009: Peel certificate / path bridge

- peel sequence
- restore stack
- bridge to BoundaryFlow / TransitionGraph plan

---

## 15. 最小 theorem set

最初の CI-GREEN 目標を次とする。

```text
TMR-A00  atomic FourColorCell has exactly four cells
TMR-A01  atomic FourColorCell contains each TrominoState exactly once
TMR-A02  uniform exchange preserves FourColorCell completeness

TMR-M00  collapse atomic FourColorCell gives one MacroCell
TMR-M01  expand (collapse M) = M
TMR-M02  macro Tromino has body count 3 and gap count 1
TMR-M03  macro total count = 4
TMR-M04  atomic area of macro Tromino completion = 16

TMR-G00  TypedGap remembers unique expected piece identity / type
TMR-G01  restore fills exactly the stored footprint

TMR-P00  restore (peel X) = X
TMR-P01  peel preserves outer boundary signature

TMR-E00  macro exchange action is closed
TMR-E01  every exchange is involutive
TMR-E02  forbidden exchange set ≠ univ → legal exchange exists
TMR-E03  current conflict + forbidden set ≠ univ → nonzero rescue exists

TMR-R00  first substitution scales atomic area by 4
TMR-R01  substitution preserves 3+1 macro count
```

---

## 16. 重要な未証明点

この計画記録時点では次を主張しない。

- 任意の四色地図がこの macro Tromino substitution だけで生成されること
- 任意の局所領域が peel 可能であること
- 任意の境界で forbidden exchange set が `V4` 全体を覆わないこと
- recursive substitution が任意深さで同一 boundary signature class を保存すること
- この solver が既知四色アルゴリズムより高速であること
- 定数時間または「瞬間」彩色が証明済みであること

ここでの狙いは、既知の四色可能性を再証明することではなく、そこから抽出できる有限局所代数・再帰単位・可逆縮約則を Lean で固定し、その上で計算量と solver 能力を測定することである。

---

## 17. 研究上の中心命題

今回の直感を最も短く表すと次である。

> Tromino の `3 + 1 = 4` は原子セルの面積関係だけではなく、四色完全 macro-cell を一個の単位に潰した後にも再び現れる。Gap は無情報な空白ではなく、抜き取られた macro-cell を一意に復元するための typed slot である。

従って Tromino の本質を

```text
shape of three cells
```

だけに限定せず、

```text
three active units
+ one typed recoverable gap
= one closed four-unit frame
```

という再帰的構成則として抽象化する。

これを `DkMath.Tromino.*` の第三世代理論候補とする。
