# Goldbach GN Prime-Pair Fiber 実装レポート

日付: 2026-09-10

cid: `6aa15236-f2b0-83ee-bfbf-a1b3c5615e5d`

元の[方針文書](../../../../../docs/not_implements/260909-Goldbach-GN-PrimePair-Fiber-Strategy.md)の実装記録。

**有限還元・CRT 計数・条件付き閉包を実装した。ゴールドバッハ予想の全称証明は閉じていない。**

既存の owner モジュール群に GN fiber、obstruction、CRT、capacity、overlap ledger を実装した。数学的な意味、必要な仮定、証明が主張しない範囲は Lean の module/public docstring に記載した。公開入口は [DkMath.NumberTheory.Goldbach](../../../DkMath/NumberTheory/Goldbach.lean) で、`DkMath.lean` からも import する。

instruction-007 までの停止境界を遵守し、最後の定理は Pascal residual を含む `goldbachPrimePairOverlapCount_eq_overlapExcess_add_residual` と、その corollary `goldbachOverlapExcess_le_primePairOverlapCount` である。この段階で universal escape provider や Goldbach の最終証明は追加していない。

## 方針文書との対応

| 段階 | 実装結果 | owner / 主な定理 |
|---|---|---|
| 1. GN fiber | 定義済み。`u=0` を含む | [Basic](../../../DkMath/NumberTheory/Goldbach/Basic.lean): `GoldbachGNFiberAt` |
| 2. 通常の Goldbach と同値 | 偶数表現・半中心・GN・offset を接続 | `strongGoldbach_iff_evenStatement`, `goldbachPairAt_iff_gnFiberAt`, `goldbachPairAt_iff_exists_offset` |
| 3. Body / Big / Gap | 自然数の順序条件を明示して証明 | `goldbachBody_add_gap`, `goldbachBody_eq_square_sub_square`, `goldbachBody_eq_BodyN` |
| 4. 左右障害 | 生の可除性と真の合成数障害を定義 | [Obstruction](../../../DkMath/NumberTheory/Goldbach/Obstruction.lean): `GoldbachProperObstructed` |
| 5. 小素数 witness | 合成数端点の真の素因子を構成 | `goldbach_small_prime_witness` |
| 6. 有限障害集合 | `r²≤2*n` の inclusive cutoff と完全被覆への同値 | `goldbachSmallPrimes`, `goldbach_failure_iff_finite_cover` |
| 7. paired prime world | certified world と正準剰余集合 | [PrimeWorld](../../../DkMath/NumberTheory/Goldbach/PrimeWorld.lean): `GoldbachPrimeWorld`, `goldbachPrimeWorldResidues` |
| 8. CRT / 周期性 | 局所座標の全周期内実現、周期・剰余還元・insert 精密化 | `goldbach_primeWorld_crt`, `goldbach_residue_periodic`, `goldbach_residue_mod_period`, `goldbach_residue_insert` |
| 9. 局所禁止数 | 一点 / 二点の合流を厳密に計数 | `goldbach_card_forbidden`, `goldbach_card_local` |
| 10. 大域 incidence / 容量 | 全周期の正確な積計数と区間の和集合・incidence 上界 | [Cardinality](../../../DkMath/NumberTheory/Goldbach/Cardinality.lean), [Capacity](../../../DkMath/NumberTheory/Goldbach/Capacity.lean) |
| 11. PCK bridge | 既存定理を実際に使用した両端点分類・support 条件付き閉包 | [Conservation](../../../DkMath/NumberTheory/Goldbach/Conservation.lean): `goldbach_paired_primitive_dichotomy`, `goldbach_prime_pair_of_square_support` |
| 12. survivor → prime pair | cutoff を全て除外した生存条件と素数対が同値 | `goldbach_survives_iff_prime_pair`, `goldbachPairAt_iff_survivors_nonempty` |
| 13. 最終 endpoint | **条件付きで実装。全称的な escape provider は未証明** | `strongGoldbach_of_capacityEscape`, `goldbachGNFiberAt_of_capacityEscape` |
| 高次数 classifier | 有限 signature と既存 GN 必要条件を接続 | [Signature](../../../DkMath/NumberTheory/Goldbach/Signature.lean): `goldbachGNSignature`, `goldbach_signature_constraints` |
| 証明経路の検証 | 強すぎる中間命題の反例を kernel で証明 | [Limitations](../../../DkMath/NumberTheory/Goldbach/Limitations.lean) |
| 14. overlap ledger | `Incidence = Covered + OverlapExcess` と survivor conservation | [Overlap](../../../DkMath/NumberTheory/Goldbach/Overlap.lean) |
| 15. pair-overlap ledger | unordered support-pair の二重計数と excess 上界 | [PairOverlap](../../../DkMath/NumberTheory/Goldbach/PairOverlap.lean) |
| 16. Pascal pair layer | `choose k 2 = (k-1) + choose (k-1) 2` の局所・大域分解。`n=35,u=5` で residual が正 | [PairOverlap](../../../DkMath/NumberTheory/Goldbach/PairOverlap.lean): `goldbach_pairMultiplicity_eq_localOverlap_add_residual`, `goldbachPrimePairOverlapCount_eq_overlapExcess_add_residual` |

添付文書にある保存量の候補列挙（prime-wave、q-adic signature の輸送等）は具体的な数学命題や provider を与えていない。本実装はそれらの存在を仮定していない。signature の片側から他方の素数性を無条件に輸送する単純な形は、反例により否定した。

## 証明可能性の検証結果

固定した `n` について次を完全に証明した。

\[
\begin{aligned}
\exists p,q\text{ prime},\ p+q=2n
&\iff \exists x,u,\ x+u=n,\ x\text{ prime},\ GN_2(x,u)\text{ prime}\\
&\iff \exists u\in\{0,\ldots,n-2\},\ u\text{ survives all proper small-prime obstructions}\\
&\iff \#\mathrm{Covered}(n)<n-1.
\end{aligned}
\]

`n=0,1` の探索域は空集合とする自然数定義で扱う。通常の全称予想は `n≥2` に限定する。有限決定手続きを `GoldbachPairAt n` と `GoldbachGNFiberAt n` の `Decidable` instance として公開した。

小素数を全て検査して生存した点から素数対を得る推論は、未解決部分ではない。残るのは、**全ての中心で少なくとも一つの生存点が実際の区間内に存在すること**である。

正確な未解決条件は以下であり、`StrongGoldbach` と同値であることも Lean で証明した。

```lean
def GoldbachCapacityEscape : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (goldbachCoveredSeats n (goldbachSmallPrimes n)).card < n - 1
```

`strongGoldbach_of_capacityEscape` はこの命題の証明を引数に取る。命題を定義し同値を示しただけで、Goldbach を証明したとは扱わない。

## 不足要因と確定した障害

| 不足要因 | 今回の確定内容 | 必要な追加内容 |
|---|---|---|
| 全周期から短い区間への移行 | CRT は `u < ∏r∈S,r` を保証し、全周期の生存数は正 | `u<n-1` 内の生存を保証する、独立した一様評価 |
| 障害の重複 | 正確な被覆数 ≤ incidence を証明 | 和集合の重複を定量的に制御し、真の被覆数を `n-1` 未満にする証明 |
| 素数端点の例外 | `r∣m` かつ `m≠r` が正確な障害 | 周期的な生の合同情報と非周期的な例外を同時に扱う区間評価 |
| PCK の分岐 | 既存の old/fresh 分解は合成数 `6` の old-generated 分岐も許す | 一つの同じ offset で両端点の合成数障害を排除する存在定理 |
| 高次数 signature | 有限性・必要条件は証明済み。次数 2 は合成数 `9` にも存在 | 片側の分類から両側同時生存へ進む、明確な追加命題とその証明 |

特に、素数ごとの障害数の単純和を使った全称的な `incidence < n-1` は **偽** である。

| `n=6`、標的 `12` | 値 |
|---|---:|
| admissible offsets | 5 |
| incidence | 5 |
| 重複を除く被覆数 | 4 |
| 生存数 | 1 |

生存 offset は `u=1`、素数対は `5+7`。この具体例から単純 incidence 経路の全称条件を反証し、同時に正確な容量式から `GoldbachPairAt 6` を証明した。これは Goldbach の反例でも、他の構造的証明の不可能性証明でもない。

instruction-006 ではこの例を重複帳簿の最小回帰に昇格した。`goldbachOverlapExcess 6 = 1`、`goldbachPrimePairOverlapCount 6 = 1`、および一般定理 `goldbachIncidenceConservation 6` を kernel で検査している。

instruction-007 では pair-overlap を Pascal の第 `r=2` 層として分解した。各 offset について
`choose k 2 = (k-1) + choose (k-1) 2` を kernel で証明し、全 offset の和に持ち上げた。`n=2` の residual は 0、`n=6` の pair count は 1、さらに `n=35,u=5` では obstruction support が `{2,3,5}` で local residual が 1 となることを回帰に加えた。`goldbachOffsetROverlapMultiplicity` と `r=0,1,2` の簡約も公開した。GTail との形式的同値や product-wave provider は追加していない。

この checkpoint で固定中心の GN fiber、有限 obstruction、CRT、PCK 条件付き橋渡し、incidence、pair-overlap、Pascal residual の帳簿は実装完了とする。branch は develop へ統合可能な状態だが、実際の merge は行っていない。次段階は GTail refactor 後の独立した Pascal 接続であり、Strong Goldbach の全称証明は依然として未証明である。

## 検証

- [回帰コード](../../../DkMathTest/NumberTheory/GoldbachGNFiber.lean): 等しい素数対、cutoff 素数の endpoint 例外、平方根境界、局所合流、paired 30-wheel、空世界、精密化、`n=0,1`、および `2≤n≤100`。
- `goldbach_centers_two_through_one_hundred`: 偶数 `4..200` に対する有限証明。`decide +kernel` を使用し、全称予想の証明とは区別する。
- [AxiomAudit.lean](AxiomAudit.lean): 96 個の全名前付き owner 宣言と有限範囲定理の依存公理を検査する再実行可能コード。
- 最終ビルドと監査の実測結果は [report-005.md](report-005.md)、[report-006.md](report-006.md)、[report-007.md](report-007.md) に記載する。

再現コマンドの cwd は `lean/dk_math`。

```bash
./lean-build.sh DkMath.NumberTheory.Goldbach DkMathTest.NumberTheory.GoldbachGNFiber
lake env lean docs/dev/NumberTheory-Goldbach-GNFiber-260910-v0/AxiomAudit.lean
./lean-build.sh DkMath
```

## 逐次記録

- [report-001](report-001.md): 初期監査、自然数減算と endpoint 例外。
- [report-002](report-002.md): GN 同値と有限被覆還元。
- [report-003](report-003.md): 容量閉包、PCK、signature。
- [report-004](report-004.md): CRT 全周期計数と反例。
- [report-005](report-005.md): 最終検証結果。
- [report-006](report-006.md): overlap ledger / pair-overlap checkpoint。
- [report-007](report-007.md): Pascal pair layer、global residual、positive residual regression、最終停止境界。
- [verification-notes](verification-notes.md): 検証順と局所修正のメモ。
- [declaration-index](declaration-index.md): 実ソースから抽出した宣言一覧。
