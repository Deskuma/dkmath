# PRIM-L035 — Canonical Active-Wave Pruning / Duplicate-Deletion Capacity Lean Judgment

日付: 2026-08-26
対象 branch: `wip/number-theory-primitive-structure-260822-v2`
環境: Lean / Mathlib v4.32.2

## 0. 目的

PRIM-L034 で次が Lean により確定した。

- parity-safe candidate world は `1<n` で odd active prime world より strictly large
- parity-safe active support が pairwise disjoint なら fresh collision は存在せず complete-point pairwise coprime
- しかし candidate 全体は support-disjoint ではない (`n=5`, offsets `2,8`, active prime `3`)

従って次の敵は candidate shortage ではなく、**一つの active prime wave が複数 candidate を再利用する duplicate hit** である。

今回の checkpoint では一般 graph libraryを導入せず、各 active prime wave から canonical representative を一席だけ残し、その他の hit を削除する **explicit finite pruning** を Lean で構成する。

狙いは、任意 `n` に対して support-disjoint family 自体を canonical に供給し、残る算術義務をその pruned family の cardinal inequality 一つへ圧縮することである。

Legendre 予想の証明、解析的 prime counting、PNT、Jacobsthal bound、descent は入れない。

---

## 1. 推奨 module

新規:

```text
DkMath/NumberTheory/Legendre/ParitySafeWavePruning.lean
```

最低限:

```lean
import DkMath.NumberTheory.Legendre.ParitySafeActiveCapacity
```

facade `DkMath.NumberTheory.Legendre` から import する。

---

## 2. L035-1 — parity-safe active wave

各 active prime `q` が parity-safe candidate world のどこを打つかを有限集合で定義する。

候補:

```lean
noncomputable def paritySafeActiveWaveOffsets (n q : ℕ) : Finset ℕ :=
  (squareAnchorOddPointCoprimeOffsets n).filter
    (fun r => SquareOffsetForbiddenBy n q r)
```

membership theorem を置く。

```lean
q ∈ squareAnchorOddActivePrimes n
r ∈ paritySafeActiveWaveOffsets n q
```

の意味が既存 `SquareOffsetForbiddenBy` / active-support semantics と exact に接続されること。

可能なら次も薄く出す。

```lean
r ∈ paritySafeActiveWaveOffsets n q
  ↔ r ∈ squareAnchorOddPointCoprimeOffsets n ∧
     q ∣ n^2+r
```

既存 exact residue theorem を再証明しない。

---

## 3. L035-2 — one representative and duplicate seats

各 wave が nonempty の場合、一席だけ canonical representative を残す。

`Nat` order / `Finset.min'` 等を使ってよい。empty wave の場合は extra set を empty にする。

概念:

```text
W_q      := paritySafeActiveWaveOffsets n q
rep_q    := one canonical member of W_q, when nonempty
extra_q  := W_q.erase rep_q
```

定義名は Lean 実装に合わせてよいが、public surface は最小限にする。

必須 theorem:

```text
extra_q ⊆ W_q
```

および、pruning 後には

```text
|(W_q ∩ prunedCandidates)| ≤ 1
```

を Lean で証明する。

ここが checkpoint の第一心臓部である。

---

## 4. L035-3 — global duplicate deletion set

odd active prime world 全体について extra seats を union する。

概念:

```lean
noncomputable def paritySafeDuplicateDeletionSet (n : ℕ) : Finset ℕ :=
  (squareAnchorOddActivePrimes n).biUnion
    (fun q => paritySafeActiveWaveExtraOffsets n q)

noncomputable def paritySafePrunedCandidates (n : ℕ) : Finset ℕ :=
  squareAnchorOddPointCoprimeOffsets n \ paritySafeDuplicateDeletionSet n
```

必須:

```text
paritySafeDuplicateDeletionSet n ⊆ squareAnchorOddPointCoprimeOffsets n
paritySafePrunedCandidates n ⊆ squareAnchorOddPointCoprimeOffsets n
```

各 active `q` について、pruned family 内の q-wave hit は高々一席になることを証明する。

---

## 5. L035-4 — canonical provider theorem

本命その1。

```lean
PairwiseParitySafeActiveOldSupportDisjointSquareSeatFamily
  n (paritySafePrunedCandidates n)
```

を **任意 `n` に対して full-cover 仮定なし**で証明する。

証明の意図:

- pruned member は parity-safe candidate
- two distinct pruned seats が同じ active support prime `q` を共有したと仮定
- 両方とも `W_q` に入る
- L035-2/3 の `W_q ∩ pruned` card ≤ 1 と衝突

prime `2` は L034 parity-safe world ですでに除外されているので、ここで parity を再証明しない。

これが通れば、今までの existential provider problem を

```text
provider existence
```

から

```text
canonical provider cardinal size
```

へ圧縮できる。

---

## 6. L035-5 — exact deletion/cardinality identity

`D := paritySafeDuplicateDeletionSet n`,
`C := squareAnchorOddPointCoprimeOffsets n`,
`R := paritySafePrunedCandidates n`
として、`D ⊆ C` を使い、できるだけ exact に

```text
R.card + D.card = C.card
```

または同値な Nat-safe 形を証明する。

少なくとも次を得ること。

```text
C.card ≤ R.card + D.card
```

本命 consumer は exact union deletion cardinal を使う。

---

## 7. L035-6 — canonical capacity frontier consumer

本命その2。

```lean
(squareAnchorOddActivePrimes n).card +
    (paritySafeDuplicateDeletionSet n).card <
  (squareAnchorOddPointCoprimeOffsets n).card
```

から

```lean
∃ p, Nat.Prime p ∧ SquareCell n p
```

を得る theorem を実装する。

経路:

```text
exact deletion identity
  -> active.card < pruned.card
  -> canonical pruned family is parity-safe support-disjoint
  -> L034 capacity Frontier consumer
  -> square-cell prime
```

この theorem は Legendre と同値とは主張しない。canonical pruning route の explicit sufficient criterion である。

---

## 8. L035-7 — additive duplicate budget（secondary bound）

各 q-wave の duplicate 数を

```text
(W_q.card - 1)
```

として加算する finite budget を定義してよい。

候補:

```lean
noncomputable def paritySafeWaveDuplicateBudget (n : ℕ) : ℕ :=
  ∑ q ∈ squareAnchorOddActivePrimes n,
    (paritySafeActiveWaveOffsets n q).card - 1
```

括弧と Nat subtraction の位置に注意すること。実際には

```lean
∑ q ∈ ..., ((...).card - 1)
```

とする。

必須 theorem:

```text
(paritySafeDuplicateDeletionSet n).card
  ≤ paritySafeWaveDuplicateBudget n
```

`biUnion` の overlap により、union deletion は単純和より小さくなり得る。この inequality の向きを誤らないこと。

そこから secondary sufficient criterion:

```text
active.card + duplicateBudget < candidate.card
  -> square-cell prime
```

を出してよい。

ただし **主 theorem は union deletion set の exact criterion** とする。単純和 budget を本質と誤認しない。

---

## 9. mandatory stronger-beam judgment

core build 後、以下を Lean theorem ベースで判定する。

### Q1
canonical pruning は本当に任意 `n` で parity-safe support-disjoint provider を構成するか。

### Q2
remaining arithmetic target を

```text
oddActive.card + deletionSet.card < candidate.card
```

という一個の finite cardinal inequality へ圧縮できたか。

### Q3
単純な sum duplicate budget は exact union deletion criterion より strictly weaker か。

可能なら小さな concrete Lean witness を探す。候補として `n=29` を試してよい。ただし `norm_num` 等で自然に閉じない場合、production module を巨大な数値展開で汚さないこと。false-beam theorem は optional。

### Q4
この checkpoint だけから universal cardinal inequality が証明できるか。

**できなければ証明しない。**

今回の目的は canonical provider の構成と residual cardinal target の露出である。

---

## 10. Outcome

```text
A — CANONICAL PROVIDER / EXACT DELETION FRONTIER COMPRESSION
B — CANONICAL PRUNING STRUCTURE ONLY
C — PRUNING DOES NOT GUARANTEE SUPPORT DISJOINTNESS
```

Outcome A:
- arbitrary `n` で canonical pruned family を構成
- support-disjointness を証明
- exact deletion/card criterion から Frontier consumer まで接続

Outcome B:
- pruning/support theorem は通るが cardinal consumer まで exact に閉じない

Outcome C:
- representative deletion だけでは二つの selected seats が同じ active support を共有し得る等、設計自体が false

Legendre proof の成否で Outcome を決めない。

---

## 11. report

作成:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
  primitive-canonical-active-wave-pruning-lean-judgment-260826.md
```

必ず記録すること:

- public definitions / theorems
- representative / extra / deletion semantics
- support-disjoint proof の数学的要点
- exact deletion cardinal relation
- sum duplicate budget との関係
- stronger-beam judgment
- universal inequality を証明したか否か

---

## 12. validation

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeWavePruning
lake build DkMath.NumberTheory.Legendre
git diff --check
```

新規 Lean source に対し、trailing whitespace と
`sorry` / `admit` / `axiom` / `native_decide` を監査する。

full repository build は不要。
Mathlib version は変更しない。

---

## 13. stop boundary

この checkpoint では canonical pruning、support-disjoint provider、deletion-card criterion、Frontier consumer まで。

ここから先の universal lower bound、analytic estimate、PNT、general graph/hypergraph abstraction、descent、LegendreConjecture theorem は自動で開始しない。
