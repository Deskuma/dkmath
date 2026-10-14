# source-bridge-frontier-017 — 同一 packet の最初の未供給存在

2026-10-14。Part A は Lean checked。constructive bridge subtask は Outcome B。

## 同じ source を固定する

全行で同一の `p : RamifiedSignedRootRoutingPacket` を使う。

```text
K = p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket
A = K.quadratic.innerRoot.fst
B = K.quadratic.innerRoot.snd
M = internalDepthFourSeventhCore p = Int.natAbs K.innerSndRoot
carrier = internalDepthFourCarrier p = Int.natAbs B = 7^4*M^7
Q = p.signedDepth.quotientRoot
V = K.quadratic.canonical.verticalGapRoot
C = K.quadratic.compensationRoot
```

Q、M、N、realPair residualRoot、center q は異なるオブジェクトである。N は既存 theorem から存在する complementary root を選んだもので、M*N=V*C と Coprime M N を満たす。N を chart allocation の商 s に同定する根拠はない。

## provenance map（gate005 と live source の照合）

以下の識別子は `DkMath.FLT.Seven` 内。`QS` は `RamifiedSignedRootRoutingPacket.QuotientPrimeSupport`、`RP` は `RamifiedSignedRootRoutingPacket` の略。分類「source」は p 以外の追加仮定不要。「conditional」は表に明示した追加仮定を要求する。

| 同じ p 上の矢印 | 実宣言 / 場所 | 分類と必要条件 |
|---|---|---|
| p → M, carrier power identity, M>0, 7∤M | QS.internalDepthFourSeventhCore / internalDepthFourCarrier_eq_seven_pow_four_mul_core_pow / internalDepthFourSeventhCore_pos / internalDepthFourSeventhCore_not_seven_dvd; NestedReconstruction | source |
| p → carrier depth4 / outer depth5 | QS.padicValNat_internalDepthFourCarrier / padicValNat_outerDepthFiveCarrier; StrictDescentFailureBoundary | source、まだ新 counterexample ではない |
| K → actual complementary N ledger | RamifiedRealCubicNormPacket.exists_inner_complementary_seventh_root; AllocationThreshold:354 | source、N>0、core=N^7、M*N=V*C、Coprime M N、7∤N |
| p → A,B coprimality | RamifiedQuadraticInnerRootPacket.innerRoot_coordinates_isCoprime; actual K.quadratic | source、整数座標の IsCoprime |
| K → real cubic source difference | RamifiedRealCubicNormPacket.sourceDifference_eq_normalizedAxis_pow_six_mul_pow_seven; RamifiedRealCubicNorm:135 | source、ring-valued axis^6*witness^7。natural chart equation ではない |
| signedDepth → realPair norm / coprimality | norm_realPairCore / realPairCores_pairwiseCoprime; RealPairCoprimalityNormGate | source、norm=-Q、Q=M の同定なし |
| p → load projections and associated scalar products | RP.realPairLoad21_product_associated / realPairLoad22_product_associated / realPairLoads_isCoprime; RealPairLoadAllocation | source、gcd normalization units を保持 |
| p → exact load*stripped factorization / associated residual powers | RP.realPairCore_eq_combinedLoad_mul_strippedCore / exists_realPairStrippedCoreProduct_associated_pow / nonempty_realPairLoadedPowerSplit | source、full core の unit-free seventh power ではない |
| row-two cells → load absorption / full core associated powers | RP.nonempty_realPairCoreAssociatedPowerSplit_via_loaded_absorption; LoadedBranchRecovery | conditional、h21:∃a,c21=a^7 と h22:∃b,c22=b^7 を要求 |
| Q signed seventh power ↔ both row-two cell powers | RP.quotientRoot_signedSeventhPower_iff_row2_cells; RealPairCoprimalityNormGate:727 | equivalence。p だけからどちらかを存在させない |
| prescribed-carrier pack → nested normal form | QS.internalDepthFourSummand_nested_normal_form; NestedReconstruction:233 | supplied CounterexamplePack u carrier v を要求。pack を構成する theorem ではない |
| reconstruction ↔ full-sieve / centered / finite charts | QS.internalDepthFourReconstruction_iff_sixth_power_sieved / internalDepthFourReconstruction_iff_centered / internalDepthFourReconstruction_iff_finiteCharts | logical equivalences。p は共通だが existence は未供給 |
| supplied additive chart → away route | awayCarrierReconstruction_iff_finiteCharts; FiniteChart:85 | positivity、7∣carrier は source から成立。追加 chart certificate が必要 |
| supplied new route → old innerRoot と異なる | QS.internalDepthFourReconstructedRoute_root_ne_innerRoot; DepthFourReconstructionAudit:41 | supplied route と carrier equality を要求。新 away root depth3、旧 innerRoot の snd depth4 |
| ideal + seventh power → full generator coordinates | QS.no_fullCoordinate_decoder_on_orientedResidualIdeal | その universal decoder contract は否定済み。invariant natural-chart の不可能性までは否定しない |
| p → finite additive chart witness | 以下の frontier formula | not established in inspected source。今回も導いていない |

実ソースと索引検索で、この final existence を追加仮定なしで供給する宣言は確認できなかった。gate005 の主要分類は現在も有効である。gates006–016 は receiver exclusion を進めたが source existence の矢印を追加していない。今回 Part A も conditional obstruction であり existence bridge ではない。

## 最初の missing formula

指定 carrier が positive で7を含むことや有限 window の定義は既にある。欠けているのは、その window に入る primitive additive Fermat pair 自体の存在である。数学的には同一 packet の actual carrier Y=7^4*M^7 に対し、positive natural endpoints u,v を得て、

```text
(Coprime u Y and u^7 + Y^7 = v^7)
  or (Coprime u v and u^7 + v^7 = Y^7)
```

を証明する段階で止まる。正当な pack が得られた後の有限上限は既存 finite-chart theorem が供給する。

Lean-proposed type（未証明の研究目標。新規 axiom/API として追加していない）:

```lean
open DkMath.FLT.Seven
open DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

-- Unproved target; not a declaration in production:
∀ p : RamifiedSignedRootRoutingPacket,
  ∃ u v : ℕ,
    (1 ≤ u ∧ u ≤ (internalDepthFourCarrier p)^2) ∧
    (1 ≤ v ∧ v ≤ (internalDepthFourCarrier p)^2) ∧
    ((Nat.Coprime u (internalDepthFourCarrier p) ∧
      u^7 + (internalDepthFourCarrier p)^7 = v^7) ∨
     (Nat.Coprime u v ∧ u^7 + v^7 = (internalDepthFourCarrier p)^7))
```

これは `mem_prescribedCarrierFiniteCharts` により chart nonempty の内容そのもの。今回の調査はこの命題が偽だとも独立だとも示していない。

loaded-core absorption を経由する特定経路では、その前に h21/h22 の証明が未供給である。両 cell powers を証明して full associated powers を得ても、それだけで natural endpoint、carrier 同定、位相と向き、加法式を与える theorem は確認できない。従って h21/h22 を sufficient chart bridge と呼ばない。

Q の norm や stripped residual の associated power、axis^6 の ring identity は自然数の literal sixth-power complement、chosen r/s、center q を指定しない。gate005 の divisor-one perfectSixth 候補もそのまま未解決であり、今回の chart construction の前提として扱っていない。

## Lean で検証した境界

最終 DkMathTest は normal-form、complementary root、conditional load absorption、finite membership の実 signature を `#check` した。また chart goal に normal-form の部分適用や loaded split を `exact` で直接渡す試行が失敗することを `fail_if_success` で検証した。同じ example は明示した hrec を使えば既存 equivalence で閉じる。この失敗は API の型不一致の証拠であり、他の全証明戦略の不可能性の証拠ではない。

新 away root を actual innerRoot に改名できないことは、既存 root-depth theorem の実際の適用を再検証した。位相の問題とは別の valuation obstruction である。

これ以上の bridge は新規形式化していない。次の検討対象は同一 p の source データから上記 endpoint existence を供給する機構であり、modular family の追加ではない。
