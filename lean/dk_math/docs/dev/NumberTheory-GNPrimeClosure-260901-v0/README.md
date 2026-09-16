# DkMath NumberTheory GN Prime Closure

cid: `6a964d97-2dd4-83ee-9117-558f8f1238e3`

Project branch: `wip/number-theory-gn-prime-closure-260901-v0`

Base branch: `develop`

Base commit at project start: `12c1476f156de4eba9009ac264385820d6d52354`

Start date: 2026-09-01

## 1. Project position

このプロジェクトは、DkMath の標準 GN 分解

$$
(x+u)^d-u^d=x\,GN_d(x,u)
$$

に対し、**積が素数になるための factor-one closure** を再利用可能な Lean API として固定する。

主眼は、新しい素数論を発明することではない。

既に DkMath は、

- GN の定義と差冪恒等式
- boundary と GN の gcd 制御
- primitive prime / valuation transport
- boundary / kernel の prime-support 分離

を持っている。

一方、もっとも基本的な

> `x * GN d x u` が素数なら、二つの因子の一方は `1`

という closure が GN 専用 theorem surface としてまだ薄い。

本プロジェクトでは、この最後の薄い層を明示的に実装する。

## 2. Mathematical source

標準 GN を

$$
GN_d(x,u):=\sum_{k=0}^{d-1}\binom{d}{k+1}x^k u^{d-1-k}
$$

とする。

DkMath では `DkMath.CosmicFormulaBinom.GN` が canonical implementation であり、

$$
(x+u)^d-u^d=x\,GN_d(x,u)
$$

を既存 API が与える。

ここで

$$
G:=GN_d(x,u)
$$

と書けば、今回の核は単純な素数積の構造である。

正の素数値 `q = xG` を考えると、自然数上では

$$
q\text{ prime}
\iff
(x=1\land G\text{ prime})
\lor
(G=1\land x\text{ prime}).
$$

したがって GN 自身が素数である場合、

$$
GN_d(x,u)\text{ prime}
\Longrightarrow
\bigl(x\,GN_d(x,u)\text{ prime}\iff x=1\bigr).
$$

これは「boundary channel が `1` へ透明化されたときだけ、GN の素数性が Body 全体の素数性へそのまま持ち上がる」ことを表す。

## 3. Important distinction

素数記号を混同しないこと。

### 3.1 Product prime

$$
q:=x\,GN_d(x,u)
$$

自体を素数とする場合、factor-one dichotomy は対称である。

$$
(x=1\land GN_d(x,u)=q)
\lor
(x=q\land GN_d(x,u)=1).
$$

### 3.2 GN prime

一方、

$$
p:=GN_d(x,u),\qquad p\text{ prime}
$$

を先に仮定する場合、

$$
x\,GN_d(x,u)=xp
$$

が素数になるのは `x = 1` の場合だけである。

第二枝 `x = p ∧ GN = 1` は、この仮定の下では `p = 1` を要求するので消える。

この二つを theorem 名・docstring でも明確に分離する。

## 4. Existing DkMath anchors

実装前に必ず current source を再確認すること。

### 4.1 GN source

`DkMath/CosmicFormula/CosmicFormulaBinom.lean`

既存候補:

```text
DkMath.CosmicFormulaBinom.GN
GN_ne_zero_nat_of_two_le
one_le_GN_nat_of_two_le
```

### 4.2 gcd / boundary control

`DkMath/NumberTheory/Gcd/GN.lean`

既存候補:

```text
coprime_boundary_GN_of_coprime_add_of_coprime_exp
gcd_gap_GN_dvd_exp
```

### 4.3 unique factorization / support split

`DkMath/NumberTheory/UniqueFactorizationGN.lean`

ここには boundary と residual GN kernel の prime-power support を分離して読む既存資産がある。

ただし今回の最小 closure の証明に不要なら import しない。

### 4.4 Nearby generic cofactor closure

`DkMath/NumberTheory/Primitive/SquareBody.lean`

既存 theorem:

```text
prime_iff_large_prime_cofactor_eq_one
```

これは別文脈だが、

> known prime factor + cofactor = 1 iff whole value is prime

という今回と同じ原理を既に利用している。

新 theorem はこの既存思想と整合させること。

## 5. Primary theorem surface

最初の checkpoint では以下を優先する。

### P0. Symmetric factor-one closure

候補 shape:

```lean
theorem prime_boundary_mul_GN_iff
    {d x u : ℕ} :
    Nat.Prime (x * DkMath.CosmicFormulaBinom.GN d x u) ↔
      (x = 1 ∧ Nat.Prime (DkMath.CosmicFormulaBinom.GN d x u)) ∨
      (DkMath.CosmicFormulaBinom.GN d x u = 1 ∧ Nat.Prime x) := by
  ...
```

これは `d = 1` の退化ケースも捨てない完全版である。

`GN_1 = 1` のとき第二枝が自然に残るため、一般 theorem としてもっとも安全である。

### P1. GN-prime specialization

候補 shape:

```lean
theorem prime_boundary_mul_GN_iff_boundary_eq_one_of_GN_prime
    {d x u : ℕ}
    (hGN : Nat.Prime (DkMath.CosmicFormulaBinom.GN d x u)) :
    Nat.Prime (x * DkMath.CosmicFormulaBinom.GN d x u) ↔ x = 1 := by
  ...
```

これは今回の数値観測を直接定理化する主 closure である。

### P2. Cosmic Formula Body wrapper

既存の canonical identity を直接 rewrite できるなら、次の wrapper も追加候補とする。

```lean
theorem prime_shifted_pow_sub_gap_iff_boundary_eq_one_of_GN_prime
    {d x u : ℕ}
    (hGN : Nat.Prime (DkMath.CosmicFormulaBinom.GN d x u)) :
    Nat.Prime ((x + u) ^ d - u ^ d) ↔ x = 1 := by
  ...
```

新しく二項展開を証明してはいけない。
既存の `(x+u)^d-u^d = x*GN` theorem を使う。

## 6. Optional strengthening

`2 ≤ d`, `0 < x`, `0 < u` の下では数学的に `GN d x u > 1` なので、第二枝 `GN = 1` を排除できる。

従って将来的には、

```lean
theorem prime_boundary_mul_GN_iff_of_two_le
    {d x u : ℕ}
    (hd : 2 ≤ d) (hx : 0 < x) (hu : 0 < u) :
    Nat.Prime (x * DkMath.CosmicFormulaBinom.GN d x u) ↔
      x = 1 ∧ Nat.Prime (DkMath.CosmicFormulaBinom.GN d x u) := by
  ...
```

のような theorem が自然である。

ただし current API は `one_le_GN_nat_of_two_le` までしか直接与えていない可能性がある。
この strengthening のためだけに大きな補題群を作らないこと。

必要なら `two_le_GN_nat_of_two_le` または `GN_ne_one_nat_of_two_le` の最小補題を追加する。

P0 / P1 を第一 checkpoint より遅らせてはならない。

## 7. Proposed ownership

第一候補:

```text
DkMath/NumberTheory/GNPrimeClosure.lean
```

理由:

- CosmicFormula の純代数恒等式ではない
- gcd 専用 theorem でもない
- valuation / unique factorization を必要としない薄い prime closure
- ABC / FLT / Legendre / PrimitiveStructure などから再利用可能

ただし実装開始時に current tree を調査し、既により自然な owner module があるなら、その理由を report に書いた上で変更してよい。

依存はできるだけ薄くする。

理想は概ね、

```text
Mathlib prime API
DkMath.CosmicFormula.CosmicFormulaBinom
```

程度である。

`Gcd.GN`, `UniqueFactorizationGN`, `PrimitiveBeam` を証明のためだけに重く import してはならない。

## 8. Non-goals

この project の第一段では以下を証明しない。

- Legendre conjecture
- ABC conjecture
- FLT
- GN の無限素数生成
- `GN d x u` が素数になるための完全分類
- cyclotomic irreducibility
- Zsigmondy の再証明
- repository-wide GN naming refactor

また、次の命題は重要だが別 checkpoint / 別設計とする。

$$
d>1\land GN_d(x,u)\text{ prime}\Longrightarrow d\text{ prime}.
$$

これは composite exponent `d = ab` に対する GN の因子分解または cyclotomic decomposition を必要とするため、今回の factor-one closure と混ぜない。

## 9. Future composition identity candidate

今後の別フェーズ候補として、次の nested GN identity を検討する。

$$
GN_{ab}(x,u)
=
GN_a(x,u)\,
GN_b\!\left(x\,GN_a(x,u),u^a\right).
$$

この恒等式が canonical API として閉じれば、composite exponent では GN が非自明因子分解を持つことを直接示し、`GN prime → exponent prime` へ進める可能性がある。

ただし README に記録するだけで、instruction-001 の実装対象にはしない。

## 10. Checkpoint plan

```text
GNPC-001
  Mathlib / repository reconnaissance
  symmetric factor-one GN closure
  GN-prime specialization
  optional Body wrapper

GNPC-002
  if useful: GN > 1 under d ≥ 2, x,u > 0
  collapse symmetric branch without assuming GN prime

GNPC-003 or separate project
  composite exponent factorization
  nested GN identity
  GN prime → exponent prime
```

## 11. Verification policy

各 checkpoint では最低限、

```text
lake build <new module>
```

を通す。

公開 aggregator を変更した場合だけ、その aggregator も build する。

この project は薄い API 層なので、第一 checkpoint で大規模 full build を目的化しない。

`sorry` / project-specific axiom を新規導入しない。

## 12. Reporting

Codex は各 checkpoint 後に同ディレクトリへ、

```text
report-001.md
report-002.md
...
```

を置く。

report には最低限、

- Outcome
- changed files
- theorem surface
- exact reused Mathlib theorem
- exact reused DkMath theorem
- build result
- deferred items

を記録する。

## 13. Public surface / merge readiness

Public entry point:

```text
import DkMath.NumberTheory.GNPrime
```

Root availability:

```text
import DkMath
```

transitively imports `DkMath.NumberTheory.GNPrime`.

General GN prime layer:

```text
GNPrimeClosure
GNRepresentationBounds
GNDegreeFactorization
GNPrimeTargetResidue
```

Degree-three shell/local layer:

```text
GNThreeQuadratic
GNThreePrimeArithmetic
GNThreeHenselLift
GNThreeHenselDepth
```

Application-specific FLT3 integration is intentionally deferred to the next
branch/checkpoint and is not part of this merge.
