# report-017 — 実装と source bridge 監査

2026-10-14。条件付き source transport は検証完了、constructive source bridge は未解決。

## 実装結果

`DkMath/FLT/Seven/SevenRamifiedFusionSourcePermutationPrimeObstruction.lean` を追加した。namespace は `DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.QuotientPrimeSupport`。

| 公開定理 | 条件と結論 |
|---|---|
| internalDepthFour_no_reconstruction_of_permutation_prime_core | 同じ p、ℓ prime、ℓ≠2,7、Coprime 7 (ℓ−1)、c≤343、n>0、actual hcore equality から ¬reconstruction p |
| reconstructed_core_ne_smallCoefficient_permutation_prime_power | 同じ条件と明示的 hrec から actual core≠c*ℓ^n |
| internalDepthFour_no_finiteCharts_of_permutation_prime_core | 同じ条件と hcore から actual carrier の finite charts nonempty を否定 |

最初の証明は source reconstruction/full-sieve equivalence の必要方向と gate016 exclusion を再利用した。finite chart corollary は既存 source finite-chart equivalence を使った。追加の存在や座標一致は仮定にも結論にも導入していない。以前の production と exact receiver 定義を変更していない。

同名の DkMathTest module に source-indexed の一般 API と具体的な素数/係数の特殊化、source-only ledger facts、loaded split、旧根と新 away root の不一致、signature/direct-use probes、公理監査を保存した。source hcore と reconstruction は必要な各例で明示している。

## source audit の結果

新しい constructive bridge は導けなかった。最初の不足は、actual carrier を指定した primitive natural additive Fermat pair の存在である。loaded recovery の経路では、その前段の row-two cell powers も追加仮定のまま。associated powers、norm や ledger の積等式から natural endpoints / orientation / chart coordinates を同定する declaration は確認できなかった。

詳細を [source-bridge-frontier-017.md](source-bridge-frontier-017.md) に記録した。gate005 map を上書きせず、現在のソースとの対応、未証明の formula、型検証の限界を独立した frontier report として残した。

## 検証

cwd: `lean/dk_math`。

| Command / check | Actual result |
|---|---|
| `lake env lean DkMathTest/FLT/Seven/SourcePermutationCalibration.lean` (昇格前) | exit 0 |
| `lake build DkMath.FLT.Seven.SevenRamifiedFusionSourcePermutationPrimeObstruction DkMath.FLT.Seven.SevenRamifiedFusionLoadedBranchRecovery` | exit 0、9091 jobs |
| `lake env lean DkMathTest/FLT/Seven/SevenRamifiedFusionSourcePermutationPrimeObstruction.lean` | exit 0、型照合・例・3公開定理の公理監査成功 |
| public axioms | propext、Classical.choice、Quot.sound のみ、sorryAx なし |
| 新規 Lean 禁止構文検索 | sorry/admit/axiom/unsafe/native_decide 一致なし |
| `git diff --check` / 新規6ファイルの whitespace | 成功 |

focused build は記載した2ターゲットとその依存に限る。LoadedBranchRecovery も今回 focused Lake target として検証した。source inventory 全体の独立した再ビルドを主張していない。必要な出力・hash は [evidence/017-verification-summary.md](evidence/017-verification-summary.md) に要約し、raw logs は ignored temporary logs に保持した。

Part A は Outcome A、bridge subtask は Outcome B。source hcore を導いたことや chart existence を主張せず、017 の報告で終了する。
