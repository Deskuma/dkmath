# L035 判定報告: canonical active-wave pruning

## Outcome

判定は **A — CANONICAL PROVIDER / EXACT DELETION FRONTIER COMPRESSION**。

各 parity-safe active prime wave から最小の candidate seat を一つだけ残し、他の hit
を global deletion set に入れる canonical pruning を、一般 graph library なしで有限
Finset として実装した。pruned family は任意の `n` で parity-safe active support が
pairwise disjoint になる。

これは provider の存在を canonical construction に圧縮した結果であり、universal
cardinal inequality 自体を証明した結果ではない。

## 実装

追加した module は
`DkMath.NumberTheory.Legendre.ParitySafeWavePruning`、facade は
`DkMath.NumberTheory.Legendre` から import する。

主な public definitions / theorems は次の通り。

- `paritySafeActiveWaveOffsets n q` と二つの membership theorem。wave hit が
  candidate membership と `q ∣ n^2+r` に exact に対応する。
- `paritySafeActiveWaveRepresentative n q` は nonempty wave の `Finset.min'`、
  `paritySafeActiveWaveExtraOffsets n q` は representative の erase。extra が元 wave
  に含まれることを証明した。
- `paritySafeDuplicateDeletionSet n` は active waves の extra の `biUnion`、
  `paritySafePrunedCandidates n` は candidate から deletion set を差し引いた集合。
- 各 active `q` について、wave と pruned candidates の交わりの cardinal が高々 1
  であることを証明した。
- `pairwiseParitySafeActiveOldSupportDisjointSquareSeatFamily_paritySafePrunedCandidates`
  により、pruned candidates が full-cover 仮定なしで canonical provider になる。

support-disjointness の数学的要点は、二つの pruned seats が同じ active prime `q` を
共有すると、両方が `W_q` に属することになり、one-hit theorem に反することである。
candidate が odd-point なので prime `2` は active support に現れず、L034 の parity
argument を再利用している。

## Cardinal frontier

deletion set は candidate の subset であり、Nat-safe に

```text
pruned.card + deletion.card = candidate.card
```

を証明した。従って主 consumer は

```text
active.card + deletion.card < candidate.card
  -> active.card < pruned.card
  -> square-cell prime
```

であり、L034 の capacity frontier consumer に接続した。単純和の secondary budget
`paritySafeWaveDuplicateBudget` も実装し、union overlap を考慮した

```text
deletion.card ≤ duplicateBudget
```

を証明した。したがって budget criterion は exact union-deletion criterion の十分条件
であり、主 criterion と同一視していない。

## Stronger-beam judgment

- Q1: Yes。canonical pruning は任意 `n` の parity-safe support-disjoint provider を
  構成する。
- Q2: Yes。残る算術義務は `active.card + deletion.card < candidate.card` の一個の
  finite cardinal inequality に圧縮された。
- Q3: Lean で確定したのは `deletion.card ≤ duplicateBudget` の向きまでであり、
  concrete `n=29` による strictness witness は production module に導入していない。
  union overlap により budget が exact criterion より弱くなり得る、という設計上の
  関係だけを保持した。
- Q4: universal cardinal inequality は証明していない。PNT、Jacobsthal bound、解析的
  estimate、general graph abstraction、descent、Legendre conjecture theorem は導入
  していない。

## 検証

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeWavePruning
lake build DkMath.NumberTheory.Legendre
git diff --check
```

新規 Lean source の trailing whitespace と `sorry` / `admit` / `axiom` /
`native_decide` を監査した。full repository build、commit、push、CI は実施していない。
