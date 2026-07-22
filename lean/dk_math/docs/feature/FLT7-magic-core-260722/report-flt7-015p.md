# FLT7-015P 作業レポート

日付: 2026-07-23  
結果: **Outcome A — specialized prime-power cell lift 完了**

## 実装内容

- `AwayNonSevenPrimeDepthPacket` により、specialized address の正の exact depth
  `e` と modulus `q^e` を固定した。
- addressed cell の exact divisibility を endpoint/root outer factor へ移し、
  実整数座標を `ZMod (q^e)` へ落とす
  `AwayNonSevenPrimeDepthPacket.toPrimePowerSolution` を構築した。
- endpoint、root、first-coordinate の全条件を、exact divisibility と既存の
  整数 remainder theorem から証明した。sevenV 列では root second coordinate
  の full-depth divisibility を別途抽出した。
- 合成 modulus を体と仮定せず、非退化条件をすべて `IsUnit` で表現した。
- left/right cubic 列では root second coordinate の unit 性から
  `t = u * v⁻¹` を作り、斉次化恒等式と unit cancellation により normalized
  cubic equation を得た。
- `sevenV`、`leftCubic`、`rightCubic` の3族を各 endpoint row に適用し、9セル
  すべてを明示的 prime-power soluble family に分類した。cubic correction の
  unit 性も Bezout 恒等式から証明した。
- `CounterexamplePack` から ramified branch、または away branch 上の全
  specialized non-seven depth packet の分類へ進む最終 audit route
  `primePowerCellAuditResult_of_pack` を追加した。

## 公開面とテスト

- facade `DkMath.FLT.Seven` に3つの prime-power module を追加した。
- focused tests:
  - `DkMathTest.FLT.SevenPrimePowerCellSystems`
  - `DkMathTest.FLT.SevenPrimePowerCellAudit`
- generic `CoprimeTripleRouting` への address uniqueness の再一般化は行っていない。
- 本結果は一つの specialized address における局所可解性であり、複数素数の
  simultaneous signed reconstruction や FLT7 contradiction は主張しない。

## 検証結果

以下はすべて成功した。

```text
lake build DkMathTest.FLT.SevenPrimePowerCellSystems \
  DkMathTest.FLT.SevenPrimePowerCellAudit DkMath.FLT.Seven DkMath.FLT
```

Axiom audit の出力は対象定理について標準的な
`propext, Classical.choice, Quot.sound` のみで、追加公理はない。
対象差分の禁止トークン検査では `sorry`、`axiom`、`native_decide` は検出されない。

## 境界

FLT7-015 の generic prime-address uniqueness 反例はそのまま保持している。
今回閉じたのは FLT7-015R の specialized address に限定した完全な
`q`-adic cell depth の局所 lift と可解族分類である。
