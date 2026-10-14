# report-018 — source prime valuation conservation

2026-10-14。Outcome A。保存則は既存 source law の派生 readout であり、新しい reconstruction bridge ではない。

## 実装

`DkMath/FLT/Seven/SevenRamifiedFusionSourcePrimeValuationLedger.lean` に3公開定理を追加した。namespace は `DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.QuotientPrimeSupport`。各 theorem は let K を使い、同一 source の field を保持する。

- `internalDepthFour_source_outerRoots_coprime p`: source-only の Coprime V C。
- `internalDepthFour_source_prime_valuation_balance p hℓ hdiv`: actual N の正値・coprimality・積等式・ℓ∤N と vℓ(M)=vℓ(V)+vℓ(C)。hℓ は primality、hdiv はℓ∣actual M。
- `internalDepthFour_source_prime_exclusive_valuation p hℓ hdiv`: V/C の一方だけにℓが存在し、その付値が vℓ(M) に等しい。

新しい Coprime V C の仮定を加えず、canonical の既存 coprimality と compensation seventh-power identity から証明した。imports は既存 SixthPowerAllocationSieve module のみ。既存 production と receiver 定義を変更していない。

同名の DkMathTest module に source-only API の適用、Nat.factorization ℓ への specialization、positive V/C、exclusive support、旧 support disjunction の回復、generic product-only countermodel、零付値規約、実際の valuation/support signature probes と公理監査を保存した。scratch は DkMathTest で校正後に昇格した。

## 検証

cwd: `lean/dk_math`。

| Command / check | Actual result |
|---|---|
| calibration 初回 / 修正後 | exit 1 / exit 0（K alias の式形を修正） |
| `lake build DkMath.FLT.Seven.SevenRamifiedFusionSourcePrimeValuationLedger` | exit 0、9087 jobs |
| `lake env lean DkMathTest/FLT/Seven/SevenRamifiedFusionSourcePrimeValuationLedger.lean` 初回 / 修正後 | exit 1 / exit 0（存在しない positivity lemma 名を修正） |
| 3公開定理・countermodel の `#print axioms` | propext、Classical.choice、Quot.sound のみ、sorryAx なし |
| 新規 Lean 禁止構文検索 | sorry/admit/axiom/unsafe/native_decide 一致なし |
| `git diff --check` / 新規6ファイルの whitespace | 成功 |

最終 build/test 出力に warning/error なし。compact evidence は [evidence/018-verification-summary.md](evidence/018-verification-summary.md)。raw logs は既存 ignore 規則の `logs/__018-*.txt` の一時ファイル。Python 数学 precheck は実行していない。

## 結果の評価

prime-support 定理より結論を細かくしたが、付値和は元の source ledger から直ちに導ける。exclusive ownership は別の既存 canonical coprimality に依存する。その依存を明示した readout を形式化したことが今回の実装結果であり、M の独立した新制約や coefficient≤343 は得ていない。

[source-valuation-frontier-018.md](source-valuation-frontier-018.md) に制約の限界と戦略再評価を記録した。新 modulus、endpoint existence、source packet 不存在、FLT7 は扱わず、018 で終了した。
