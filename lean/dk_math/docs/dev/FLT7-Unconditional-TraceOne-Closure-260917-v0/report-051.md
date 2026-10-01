# FLT7 R45 実装レポート

## 対象

`instruction-051.md` の R45（有限 Hensel 深度増幅）を、R44 の paired deep-jet モジュールから分離した中立モジュールとして実装する。

## 初期確認

- R44 の到達点は `directOrbitPairedDeepJet_49th_power_correction` までで、独立した clash は得られていない。
- R45 は有限深度の `ThetaNilpotentDepth`、深度降下、単位元の有限 7 冪表示、および軸 divisibility の一般補題を対象とする。
- 無限降下、FLT7 全体の矛盾、任意深度の一様主張は本実装の対象外とした。

## 実装進捗

新規ファイル `DkMath/FLT/Seven/SevenRealCubicThetaSeventhPowerDepth.lean` を作成し、以下を実装済み。

- `ThetaNilpotentDepth` と深度の単調性。
- `seventhThetaLinearBFactor_not_seven_dvd`。
- `seventhThetaSquareCFactor_not_seven_dvd`。
- `eisensteinAxis_pow_three_mul_dvd_imp_ofInt_pow`。
- `thetaNilpotentDepth_pow_seven_drop`。
- 深度 1 からの projective-log 消滅と単位元の seventh-power 化。
- 逆元の有限深度から `7 ^ n` 冪表示を得る再帰補題。
- `eisensteinAxis^(3*m)` から `ofInt ((7 : ℤ)^m)` への一般的な divisibility transport。

R44 の paired deep-jet モジュールには、現行 provenance に限定して以下を追加した。

- source root の `ThetaNilpotentDepth 9`。
- `p.rho - ofInt (thetaConstInt p.rho)` と `p.rho^6` の深度9 scalarity。
- quotient remainder と source sixth power の加法 transport による `ThetaNilpotentDepth 9 (Z^7)`。
- 深度 drop による `ThetaNilpotentDepth 8 Z`。
- `Z` の theta 座標を `v⁻¹` の座標と `(h.v : ℤ)^2` に分解し、`¬ 7 ∣ h.v` の整数 coprimality だけで `v⁻¹` へ深度8を転送。
- `v = t^(7^8)` と `W = rho * t^(7^9)`。
- quotient identity を併せて返す現行 `C = 1` provenance wrapper。

中立層は `SevenRealCubicThetaSeventhPowerDepth.lean` に分離し、paired 側には current-provenance の定理だけを置いた。

## 検証状況

逐次実行した検証はすべて通過した。

- `lake build DkMath.FLT.Seven.SevenRealCubicThetaSeventhPowerDepth`
- `lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJet`
- `lake build DkMath.FLT.Seven`
- `lake build DkMathTest.FLT.SevenRealCubicThetaSeventhPowerDepthApi`
- `lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJetApi`
- `lake build DkMathTest.FLT.SevenRealCubicThetaSeventhPowerDepthAxiom`
- `lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJetAxiom`
- `lake env lean DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJetR45Scratch.lean`

新規 neutral/paired の API・axiom・scratch を追加した。axiom audit は既存の
`propext`、`Classical.choice`、`Quot.sound` の範囲で、新規の project axiom、
`sorry`、`sorryAx`、`admit`、`unsafe` は導入していない。

Part N の既存定理照合では、`7^9` が奇数冪であること自体からの clash、
非平方係数定理との clash、符号条件からの clash、既存 height/Thue 定理に
よる clash は得られなかった。したがって本 checkpoint は Outcome B
（有限 Hensel amplification は green、独立した contradiction は未成立）である。
