# Validation 016

作業ディレクトリ：`/home/deskuma/develop/lean/dkmath/lean/dk_math`。
Lean toolchain：4.34.1。016 着手時の git status は clean。既存 015 の証明と定義を保持し、production 4 ファイル、regression/calibration 2 ファイル、全宣言 axiom audit 1 ファイルを追加、Legendre facade と文書 README を更新した。

## Builds

|実行コマンド|結果|記録|
|---|---|---|
|`lake build DkMath.NumberTheory.Legendre.GnomonResidueCover`|成功、3139 jobs|[log](evidence/MANIFEST.md#log-0125b933b0908bbe)|
|`lake build DkMath.NumberTheory.Legendre.SquareShellWheelPeriod`|成功、3140 jobs|[log](evidence/MANIFEST.md#log-4f6f922aa9f58846)|
|`lake build DkMath.NumberTheory.Legendre.SquareAnchorCounterexamplePacket`|初期 packet 成功、9057 jobs。最終版は下記 focused/facade/root で再検証|[log](evidence/MANIFEST.md#log-d3e6b71470fdc2ef)|
|`lake build DkMath.NumberTheory.Legendre.GnomonPrimorialTransition`|初期 transition 成功、8984 jobs。最小 owner の一回 lower 変更を加えた最終版は下記で再検証|[log](evidence/MANIFEST.md#log-8338e139dc6bdb93)|
|`lake build DkMathTest.NumberTheory.LegendreResidueCoverCalibration`|成功、9069 jobs。新規 production 全4モジュールと regression/calibration 両方を依存として検証|[log](evidence/MANIFEST.md#log-da7e60807fadb304)|
|`lake build DkMath.NumberTheory.Legendre`|成功、9093 jobs|[log](evidence/MANIFEST.md#log-2049a10609fdbfc0)|
|`lake build DkMath`|成功、10396 jobs|[log](evidence/MANIFEST.md#log-4f9253df4b3d9495)|
|`lake build DkMathTest.NumberTheory.LegendreResidueCoverAxiomAudit`|成功、9105 jobs|[log](evidence/MANIFEST.md#log-49fc4cd3924565ae)|

jobs は Lake の依存 graph の数であり、新しくコンパイルされたファイル数ではない。古い iteration の失敗出力は [iteration log](evidence/MANIFEST.md#log-42be973a131cdb47) に残した。最終 focused build と新規 source には warning/error がない。

全体 build は既存 5 件の `declaration uses sorry` 警告を replay する：`ZsigmondyCyclotomicResearch:147`、`TriominoCosmicBranchA:4187`、`GcdNextResearch:850`、`CyclotomicPrincipalization:5389`、`TriominoFLT:1919`。これらは今回の変更対象ではない。新規宣言の完全 axiom audit は、この既存全体 warning と区別して実施した。

## Complete trust and source checks

[生成スクリプト](checks/check-016.py)は実際の source から[全宣言 manifest](evidence/MANIFEST.md#log-e147a6b777bf1629)を作り、production **61** 件と regression/calibration **26** 件、合計 **87** 件の `#check` / `#print axioms` を生成した。

全87件で axiom set を回収・照合した。依存は空または `propext`, `Classical.choice`, `Quot.sound` の範囲で、`sorryAx` や追加 axiom はない。closure に入る古い endpoint についても実際の依存結果を確認している。

同じ script で8 Lean ファイル（4 production、2 test、audit、facade）の共通 copyright header と import-adjacent `#print "file: Full.Module.Name"` を確認。新規 production/test の forbidden tokens `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by` は不在。`git diff --check` と新規 Lean ファイルへの `git diff --no-index --check /dev/null ...` の両方を実行した。

最終 checker の実行結果は [check log](evidence/MANIFEST.md#log-66290938c52e1caa)。document links、report の10回答、単一 next-provider 名、末尾 Outcome B も照合した。

## Finite exploration and kernel regressions

[探索スクリプト](checks/discovery-016.py)を実行し、[diagnostics](evidence/MANIFEST.md#log-85cf275d729a11b1)を保存。all natural anchors 1..300 の300行と別枠1031の1行について、owner fibers の全 card、overlap histogram、image injectivity、census、補正付き quotient conservation、Q+U balance、successor common support の displacement divisibility、lower least-owner persistence=0 を検査した。探索件数・ランキング・1031 counts は [summary](evidence/MANIFEST.md#log-eb63cf21e22b7516)。

選択した kernel regressions は以下。有限 Python 診断全301行を Lean 定理と呼んでいない。

- periods n1..7 と n1/n2/n4 の衝突、n3 の width=period 単射。
- 既存 n4 bridge に直接接続。whole image {0..5}、escape {1,3,7}、distinct survivor {1,5}（card2 と U3 の区別）。
- n1 の whole-shell/parity-safe carrier 境界と empty projected wheel。
- Cube n5 / Cross n7 owner、Repeated n8/n13/n29 owner と multiowner quotients、Triple n19 owner と3quotients。
- Rejected n11,p5,q27 の shell residue fiber と small quotient wheel の接続。
- 三つの covered lower seats n13..15 の owner5→2→3、common nonleast support5 が残る55→70。
- n6 の sqrt-period address と anchor の大小に関する反例。
- new near-miss n5：escape offsets {4,6}、projected coordinates {29,1}、U=2、anchor25、image card10、square-anchored nonfull cover。
- inherited n1031 certificate：nonfull、projected survivor、projected survivor card≥18、corrected counterexample equality の否定、既存 prime endpoint の保全。exact U160/J472 を kernel で新規計算したとは主張しない。

これらは kernel reduction または既存 proved certificates と新規 production APIs の合成による。外部 evaluator に信頼を置く `native_decide` は使っていない。
