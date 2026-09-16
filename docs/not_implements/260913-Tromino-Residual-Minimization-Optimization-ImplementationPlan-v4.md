# Tromino Residual Minimization / Optimization 実装計画書 4

- Status: implementation plan / not implemented
- Date: 2026-09-13
- Branch at recording: `develop`
- Repository: `Deskuma/dkmath`
- Existing geometric base: `lean/dk_math/DkMath/Tromino.lean`
- Previous plan 1: `docs/not_implements/260912-Tromino-BoundaryFlow-FourColor-ImplementationPlan.md`
- Previous plan 2: `docs/not_implements/260913-Tromino-Exchange-Algebra-ImplementationPlan-v2.md`
- Previous plan 3: `docs/not_implements/260913-Tromino-MacroCell-RecursiveSubstitution-ImplementationPlan-v3.md`
- Target area: future `DkMath.Tromino.*` optimization / IR / solver layer
- Theme: reduction, symmetry quotient, Tromino modulus, irreducible residue, kernelization, normal form, certified optimization

## 1. 目的

本資料は、実装計画書 1〜3 で得た

```text
geometric Tromino
  ↓
four-state exchange algebra
  ↓
macro-cell / typed gap / recursive substitution
  ↓
boundary flow / path-cycle
```

を、実際の最適化アルゴリズムへ統合するための計画書 4 である。

今回の中心問題は次である。

> 複雑な境界地図を Tromino の合法な交換・縮約・再帰 substitution により単純化し、これ以上局所代数だけでは縮められない residual を最小化できるか。

四色塗り分けを直接探索するのではなく、まず問題を意味保存付きで圧縮する。

```text
Map / planar boundary object
  ↓ encode
Boundary IR
  ↓ canonicalize
symmetry quotient
  ↓ reduce
Tromino macro-cell contraction
  ↓ propagate
exchange / forced move solving
  ↓ minimize
irreducible residual kernel
  ↓ solve residual
path / cycle or bounded search
  ↓ decode
restored coloring / state assignment
```

本計画では、この `reduce → residual → restore` を Lean 上で証明付き最適化として固定する。

---

## 2. 最適化対象は「最小単位」ではなく「最小残余」

Tromino exchange unit は縮約の命令セットである。

一方、最適化の目的は、その命令を使った後に残る unresolved structure を最小化することにある。

対象 `G` に対する合法 reduction sequence を

$$
G = G_0 \rightsquigarrow G_1 \rightsquigarrow \cdots \rightsquigarrow G_k = R
$$

とする。

`R` がこれ以上縮約できないとき、`R` を irreducible residue と呼ぶ。

```lean
Def Reducible (G : BoundaryIR) : Prop := ...
Def Irreducible (G : BoundaryIR) : Prop := ¬ Reducible G
```

最適化問題は概念的に

$$
\boxed{
\min_{G \rightsquigarrow^* R} \mu(R)
}
$$

である。

ここで `μ` は residual complexity measure とする。

候補:

```text
μ₀ = unresolved macro-cell count
μ₁ = unresolved boundary-port count
μ₂ = exchange-deadlock count
μ₃ = cycle / branch complexity
μ₄ = weighted lexicographic tuple of the above
```

最初は辞書式順序で

```text
(deadlocks, unresolved ports, unresolved cells, graph size)
```

を採用する案を検討する。

---

## 3. `mod` としての Tromino residual

整数では

$$
n = qm + r,
\qquad
0 \le r < m
$$

として `r = n mod m` が残余である。

Tromino 理論では単純な cardinality residue だけでは不足する。

例えば面数が同じ `mod 4` でも、境界交換可能性や TypedGap の構造が異なれば意味が違う。

したがって最初の比喩として

$$
|G| \bmod 4
$$

を観測しつつ、本体は「合法 Tromino 操作で同値とみなす商構造」として定義する。

合法な exchange / rotation / reflection / contraction / restoration で互いに移れることを

$$
G \sim_T H
$$

と書く。

理想的には

$$
\boxed{
G \bmod T
:= [G]_{\sim_T}
}
$$

という Tromino modulus / quotient を考える。

その同値類の中で complexity が最小の代表元を normal form とする。

$$
\text{NF}_T(G)
:=
\arg\min_{H \sim_T G} \mu(H).
$$

**注意:** `~ₜ` が本当に同値関係、さらに reduction と整合する congruence になることは実装時に証明が必要である。`Tromino modulus` は現段階では研究名であり、整数剰余環との同一視はしない。

---

## 4. Boundary IR

元の複雑地図を直接最適化せず、必要な意味だけを残した中間表現へ変換する。

候補構造:

```lean
structure BoundaryIR where
  cells        : Finset CellId
  ports        : Finset PortId
  adjacency    : ...
  cyclicOrder  : ...        -- planar case / optional
  stateDomain  : CellId → Finset TrominoState
  typedGaps    : Finset TypedGap
  macros       : Finset MacroCell
```

Boundary IR は最低限、次を保持する。

- 隣接関係
- 境界 port
- 各局所状態の許容集合
- TypedGap の復元情報
- macro-cell hierarchy
- 必要なら planar cyclic order

一方、最適化に不要な幾何座標はできるだけ落とす。

目標:

$$
\text{Semantics}(\text{encode}(G))
=
\text{Semantics}(G).
$$

---

## 5. Symmetry quotient / canonicalization

Tromino 局所状態には少なくとも次の対称性がある。

- geometric rotation / reflection (`D₄` 型)
- Klein four exchange translations (`V₄`)
- waiting-state relabeling (`GL(2,2) ≃ S₃`)
- full affine color action (`AGL(2,2) ≃ S₄`) 候補

同じ orbit に属する局所配置を別探索ノードとして保持しない。

$$
T \sim g \cdot T.
$$

canonical representative を

```lean
canonicalize : LocalConfig → LocalConfig
```

として実装し、

```lean
canonicalize_idempotent
canonicalize_equiv
semantics_canonicalize
```

を狙う。

これが第一の探索空間圧縮となる。

---

## 6. Tromino liberty / escape degree

局所 piece `P` に対し、現在の境界制約から禁止される exchange を

$$
F(P) \subseteq V_4
$$

とする。

許される exchange 集合は

$$
A(P):=V_4\setminus F(P).
$$

局所自由度を

$$
\boxed{
\text{escapeDegree}(P):=|A(P)|=4-|F(P)|
}
$$

と定義する。

意味:

```text
4 : completely free
3 : one exchange forbidden
2 : two exchanges available
1 : forced move
0 : local deadlock
```

これは四色囲碁における「呼吸点」に相当する局所量とみなす。

最適化では

```text
escapeDegree = 1  → unit propagation / forced reduction
escapeDegree ≥ 2  → defer branching
escapeDegree = 0  → symmetry expansion / neighborhood rewrite / residual kernel
```

という順序を試す。

候補 theorem:

```lean
card_allowedExchange_eq_four_sub_card_forbidden
escapeDegree_pos_iff_exists_exchange
escapeDegree_one_unique_exchange
```

---

## 7. Reduction rule set

最適化 step は一種類に限定しない。

候補:

### R0. Local exchange

$$
P \mapsto T_\delta(P)
$$

で局所衝突を回避する。

### R1. Symmetry normalization

rotation / reflection / color automorphism orbit の代表へ落とす。

### R2. Tromino contraction

`3 Body + 1 TypedGap` として boundary-equivalent な領域を macro-cell へ縮約する。

### R3. TypedGap elimination

復元情報が既に確定した Gap を abstraction node へ変換する。

### R4. Pairing reduction

boundary flow の even pair を path transport としてまとめる。

### R5. Forced exchange propagation

`escapeDegree = 1` の候補を即確定し、隣接 domain を更新する。

### R6. Residual decomposition

独立成分へ分離できる場合は solver を分割する。

各 rule に対し必ず

$$
\text{Semantics}(G)=\text{Semantics}(H)
$$

または用途に応じて

$$
\text{Solvable}(G) \leftrightarrow \text{Solvable}(H)
$$

を要求する。

---

## 8. Termination

最適化 rule が循環すると solver にならない。

そこで reduction-only phase では well-founded measure を持つ。

候補:

$$
\mu(G)
=
(
\#\text{raw cells},
\#\text{unresolved ports},
\#\text{noncanonical nodes}
)
$$

を辞書式順序で減少させる。

ただし exchange-only rewrite は cardinality を減らさないため、

```text
normalization phase
reduction phase
```

を分けるか、visited-orbit certificate により loop を禁止する。

目標 theorem:

```lean
reduction_measure_decreases
reduction_terminates
```

---

## 9. Confluence / normal form

異なる順序で縮約すると異なる irreducible residue が出る可能性がある。

```text
        G
       / \
      H₁ H₂
      |   |
      R₁ R₂
```

理想は

$$
R_1 \cong R_2
$$

または少なくとも

$$
\mu(R_1)=\mu(R_2)
$$

を得ることである。

段階的目標:

1. deterministic strategy により canonical residue を定義
2. local critical-pair analysis
3. restricted subsystem で confluence
4. 可能なら global normal-form uniqueness

候補 theorem:

```lean
normalize_deterministic
local_diamond
normalForm_unique_up_to_symmetry
```

全体系で confluence が成立しなくても、最小 residual 探索として beam / best-first search を使える。

---

## 10. Kernelization

最適化の主要目標を

$$
G \longmapsto K(G)
$$

とする。

`K(G)` は元問題と意味同値であり、局所代数で容易に処理できる部分をすべて除いた小さい residual kernel である。

理想:

$$
\text{Solvable}(G)
\iff
\text{Solvable}(K(G)).
$$

さらに復元証明書を保存し、kernel の解から元対象の解を構成する。

```lean
structure KernelizationCertificate (G : BoundaryIR) where
  kernel  : BoundaryIR
  reduce  : G ↠ kernel
  restore : Solution kernel → Solution G
```

最終 solver は

```text
large problem
  ↓ polynomial / local preprocessing
small kernel
  ↓ expensive search only here
solution
  ↓ certified restore
original solution
```

という設計を狙う。

---

## 11. `mod 4` / boundary parity / structural residue

Tromino residual には複数の低コスト observer がある。

### 11.1 area residue

$$
|G| \bmod 4.
$$

### 11.2 boundary parity residue

非零境界状態 `A,B,C` の本数について

$$
(n_A,n_B,n_C) \bmod 2.
$$

保存境界では

$$
n_A \equiv n_B \equiv n_C \pmod 2
$$

なので、残余型は少なくとも

```text
(0,0,0)
(1,1,1)
```

へ圧縮される。

### 11.3 exchange obstruction residue

$$
F(P) \subseteq V_4.
$$

特に

$$
F(P)=V_4
$$

が局所 exchange deadlock。

従って単一整数ではなく、暫定的に

$$
\boxed{
R(G)
=
(
|G|\bmod4,
\text{boundary parity},
\text{exchange obstruction},
\text{macro residual}
)
}
$$

を structural residue として観測する。

---

## 12. 最適化 strategy

第一候補:

```text
1. encode map → BoundaryIR
2. canonicalize local symmetry orbits
3. compute exchange domains / escapeDegree
4. exhaust forced moves (degree 1)
5. contract Tromino-reducible macro-cells
6. pair / compress boundary flows
7. split independent components
8. repeat to fixed point
9. obtain irreducible residual kernel
10. solve kernel by path/cycle or bounded branching
11. reverse certificates and restore
```

branching が必要な場合は、自由度が最小の piece を優先する。

$$
P^* := \arg\min_P \text{escapeDegree}(P),
\qquad
\text{escapeDegree}(P)>1.
$$

これは CSP の minimum remaining values heuristic に相当する。

---

## 13. 「瞬間塗り分け」の意味

現段階で「瞬間」は計算量定理ではない。

研究仮説は次である。

> 多くの局所領域が exchange / contraction / forced propagation で消え、探索が必要な residual kernel が元地図より十分小さくなるなら、直接四色割当を探索するより大幅に速い solver が得られる可能性がある。

従って評価指標は

```text
input faces
IR nodes
number of contractions
number of forced exchanges
residual kernel size
branch count
restore cost
```

とする。

量子計算との比較を行う場合も、まず classical preprocessing / kernelization 後の residual search size を測定する。

「量子不要」を先に主張せず、Lean proof + benchmark で判定する。

---

## 14. Lean モジュール候補

```text
DkMath/
  Tromino.lean
  Tromino/
    State.lean
    Exchange.lean
    MacroCell.lean
    TypedGap.lean
    BoundaryIR.lean
    Canonical.lean
    Reduction.lean
    Residual.lean
    Kernelization.lean
    Optimizer.lean
    Solver.lean
    Restore.lean
```

既存 namespace `DkMath.Polyomino.Tromino` との整合を優先しつつ、代数・solver 層が十分独立した段階で facade namespace `DkMath.Tromino` を設けることを検討する。

---

## 15. 実装フェーズ案

### TRO-000: survey / representation

- v1〜v3 API の統合設計
- Mathlib rewriting / relation / quotient / SimpleGraph API 調査
- `BoundaryIR` 最小仕様決定
- complexity measure 決定

### TRO-001: exchange domain / liberty

- forbidden exchange set
- allowed exchange set
- `escapeDegree`
- unique forced move theorem

### TRO-002: canonical symmetry

- rotation / reflection / color-action equivalence
- canonical representative
- semantics preservation

### TRO-003: reduction relation

```lean
TrominoStep G H
TrominoReduces G H := Relation.ReflTransGen TrominoStep G H
```

- individual reduction rules
- proof certificates

### TRO-004: termination

- reduction measure
- strict decrease
- finite normalization

### TRO-005: residual

- irreducible predicate
- area / parity / obstruction observers
- structural residue record

### TRO-006: macro contraction

- TypedGap boundary equivalence
- contract / restore
- nested macro-cells

### TRO-007: kernelization

- fixed-point reducer
- certificate chain
- `Solvable G ↔ Solvable (kernel G)`

### TRO-008: residual solver

- transition graph
- path/cycle solver
- minimal branching fallback

### TRO-009: normal form / confluence assessment

Outcome A:

- canonical normal form unique up to symmetry

Outcome B:

- deterministic canonical strategy only

Outcome C:

- non-confluent but residual minimization search is effective

### TRO-010: benchmark

- generated Tromino maps
- random planar-like boundary instances
- adversarial deadlock instances
- compare raw coloring CSP vs Tromino optimizer

---

## 16. 最初に Lean へ固定する小定理群

```text
TRO-E00  allowed = univ \ forbidden
TRO-E01  escapeDegree > 0 ↔ exists legal exchange
TRO-E02  escapeDegree = 1 → unique legal exchange
TRO-R00  each certified reduction preserves solvability
TRO-R01  restoration inverts contraction on certified region
TRO-M00  reduction-only measure strictly decreases
TRO-N00  normalization reaches irreducible residue
TRO-K00  kernel solution restores to original solution
TRO-Q00  area residue mod 4 is invariant under 4-cell macro contraction
TRO-Q01  boundary parity observer is preserved by valid pairing contraction
```

これらが通れば、v4 の「最適化としての Tromino calculus」の最小核が得られる。

---

## 17. 研究上の本丸

本計画の最重要質問は次である。

1. どの局所構造まで Tromino exchange / macro contraction だけで消せるか。
2. irreducible residual の最小 obstruction は何か。
3. `F(P)=V₄` となる局所 deadlock は symmetry / neighbor rewrite で常に解消できるか。
4. residual kernel size は元の地図サイズに対してどの程度まで小さくなるか。
5. reduction order によらない canonical residue が存在するか。
6. boundary IR → Tromino AST / DAG への変換はどこまで一般的に可能か。
7. path / cycle solver と結合したとき branching をどこまで消せるか。

四色定理の既知事実を再証明することより、ここでは

> 四色制約を Tromino の有限代数へコンパイルし、意味保存付きで residual kernel を最小化する一般計算原理

を抽出することを主眼とする。

---

## 18. 要約

計画書 4 の流れは次である。

```text
complex map
  ↓
Boundary IR
  ↓
symmetry quotient
  ↓
Tromino exchange propagation
  ↓
macro-cell contraction
  ↓
structural mod / residue observation
  ↓
irreducible residual minimization
  ↓
small kernel solver
  ↓
certified reverse restoration
```

標語:

> **全部を探索しない。交換可能な部分を mod-out し、最後に残る余りだけを解く。**

これを `Tromino Residual Minimization` の基本方針とする。
