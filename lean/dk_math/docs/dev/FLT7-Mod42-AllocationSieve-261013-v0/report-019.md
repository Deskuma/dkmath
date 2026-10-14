# report-019 — scalar separation and source constraint audit

2026-10-14。Outcome B。actual M 単独の新しい制約は得られなかった。

## 変更

新しい production module は作成していない。`DkMathTest/FLT/Seven/SevenRamifiedFusionSourceConstraintSeparation.lean` を追加し、次の5 test-only theorem を保存した。

- `scalarLedger29Squared`: M=29²,N=1,V=M,C=1 の正値・積等式・両 coprimality・7-unit と coprime criterion の不成立。
- `primeDivisor29Squared {ℓ : ℕ} (hp : Nat.Prime ℓ) (hd : ℓ∣841) : ℓ=29`。
- `scalarLedger_no_permutation_prime`: prime ℓ∣841、ℓ≠2,7、Coprime 7 (ℓ−1) の同時成立を否定。
- `sourceComplement_ne_one (K : RamifiedRealCubicNormPacket) {N : ℕ} (hN : |sndCore(A,B)|=N^7) : N≠1`。
- `actualSourceComplement_gt_one p`: 同じ p の actual K から N>1、実際の cubic-core=N^7、M*N=V*C、Coprime M N を伴う補根を抽出。

N>1 は actual cubic polynomial と source 非零座標を使うため、scalar ledger の言い換えではない。ただし M の prime種類や small-coefficient decomposition を与えない。source-only readout を test 内で保存し、M-only API として production に昇格していない。既存 source、receiver、sieve を変更していない。

## 検証

cwd は `lean/dk_math`。

| 実行 / check | Actual result |
|---|---|
| calibration 初回・第2回 | 各 exit 1、存在しない Nat の mul_eq_one 名 |
| calibration 修正後 | exit 0 |
| `lake build DkMathTest.FLT.Seven.SevenRamifiedFusionSourceConstraintSeparation` | exit 0、9088 jobs、test proofs と signature probes を検証 |
| `#print axioms` 全5 test-only theorem | scalar model は propext；他は propext, Classical.choice, Quot.sound；sorryAxなし |
| 新規 Lean 禁止構文検索 | sorry/admit/axiom/unsafe/native_decide 一致なし |
| 最終 build log の warning/error/sorry 検索 | 一致なし |
| `git diff --check`、新規5ファイル whitespace 検査 | 成功 |

focused build は追加 test とその import dependencies の検証である。oriented ownership module は actual Q への対象を source inspection で調べ、今回の独立した build target としたとは主張していない。compact evidence は [evidence/019-verification-summary.md](evidence/019-verification-summary.md)。raw logs は temporary/ignored。Python数学precheckは実行していない。

## 数学的評価

スカラー保存則から gate016 の usable prime は強制されない。source 二次・三次条件は scalar ledger に含まれておらず、N=1 の追加分離結果を証明できた。一方、M=841 自体の排除や M-only independent condition は証明できていない。

[source-constraint-frontier-019.md](source-constraint-frontier-019.md) に exact source provenance、追加仮定、対象の違い、最初の sharpening 不足を記録した。新しい weak sieve gate に自動的に進むより、source variables の消去や independent inequality を中心とする研究設計の再検討を提案し、019 で終了する。
