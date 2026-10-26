# NOTE-032 同じ整数商標的の良還元保持（2026-10-27）

## 証明する命題と残す境界

同じSource、同じ安定直線L、同じ有限核H、同じVélu座標、同じ既存整数標的を使う。
良い奇素数q≠pでは標的も良還元を持つ。前章の悪い住所の結果と合わせ、p≥5なら
**p以外の全素数で、同じ整数標的が良還元または乗法的還元を持つ**。
q=pでの還元型、判別式の正確な深さ、悪い場所での全点零成分輸送、スキームisogeny、
標的有理捩れの排除、一般hnoはこの結論に含めない。

## 幾何学の再利用と仮定の一般化

既存の標的非特異性の証明は、2捩れ三根の分離と有限ファイバーの根の個数上界を使う。
この部分に必要なのは標数0全体ではなく、係数体で2が非零であることだった。
Model、ModelMap、Specialization、RationalFiber、TwoTorsion、Nonsingular、Pair、
VeluEquation、WeierstrassVeluPairの該当宣言を`NeZero (2 : K)`へ一般化した。
ModelDescentでは幾何学的なGalois作用の部分だけを一般化し、固定係数の基礎体への降下は
従来の標数0を保持する。LocalIntegralityでは同じ多項式標的との同定だけを一般化し、
捩れ座標の整性の標数0条件は保持する。変更した既存所有者は計11である。

4,16の非零性は2の冪から証明する。関数体・代数閉包への2非零性は体写像の単射性で運ぶ。
標数0の源から剰余体の2非零性を暗黙に推論しない。良還元の局所定理には剰余体での
`NeZero (2 : ResidueField A)`を明示し、Sourceでは奇素数住所から供給する。

## 同じ半集合から同じ剰余標的へ

1. `FiniteInversionHalfTransport`は加法同型で半集合を運び、反転不変な和を保つ。
   値の群で2を割らず、半集合の選び直しを代表独立性で吸収する。
2. `WeierstrassFiniteKernelModel`は任意の体上の単射な奇数有限核を代数閉包へ写し、
   元の半集合と既存halfKernelのモーメントを比較する。
   点群の演算を決める`DecidableEq k`も引数として保持し、具象有限体の点群と別の演算インスタンスを混在させない。同じ多項式標的を既存kernelModelと同定し、
   一般化した三根分離からΔ≠0・楕円性を得る。巡回性や標的楕円性を仮定しない。
3. `EllipticFiniteKernelGoodReduction`では源の良還元から全核点の滑らかさを供給し、
   単元位数捩れの還元の単射性を使う。同じ元のHを添字にした剰余モデルの非特異性から、
   同じvaluationKernelModelとkernelModelの判別式の付値1を得る。
4. `FreyFiniteKernelGoodReduction`はp≠qの単元性・核の奇数位数・源の良還元を内部供給する。
   既存の整数化でΔの付値が一致する定理を使い、同じ整数標的の正式な`HasGoodReduction`へ接続する。
   最後に2およびabc支持の悪い場所と統合し、`residual_integer_target_semistable_away`を得る。

良い場所では`oddKernelPointMap_smooth_of_good`により、同じ全点写像の全像点が
同じ付値環標的で滑らかに還元する。これは悪い場所での零成分輸送や、
還元写像との可換図式を証明したという意味ではない。

## 模範証明との比較

既存キャッシュの模範証明`veluQuotient_oddOrderSummingSet_discriminant_ne_zero`、
`veluX_oddOrderSummingSet_injOn_psi2Sq_roots`、
`eval_psi2Sq_veluQuotient_veluX_eq_zero_of_eval_psi2Sq_eq_zero`、
`discriminant_prod_veluU_pow`を調べた。
三根分離に対応するDkMathの既存証明を一般化する経路を採用し、大規模な判別式積公式を複製しない。
新規ファイルは既存DkMath APIを組み合わせた証明であり、外部解答モジュールのimportはない。
キャッシュのGit blobを今回検証した。非特異性の模範証明は
`f66586eb1bb501437c601e7af2bd9a79c0f77a48`（5705 bytes）、
判別式積公式は`0c42a9282f1033d6d64cc213bb1f7c7c52b17d1e`（185988 bytes）である。
新規所有者はMIT、既存所有者の著作権・ライセンス表示は保持した。

## 検証

検証コマンド・結果は[検証要約](evidence/validation-note032-good-reduction.txt)と
[機械可読記録](evidence/note032-good-reduction.json)に記録する。
[Source37スモーク](evidence/Note032GoodReductionSmoke.lean)は同じ既存整数標的を使う。
Sourceは反例を条件とする型なので、これとは別に標数5の曲線y²+y=x³上に実際の3点核を構成し、
Q+Q=−Q、反転対の分離、点数3、半集合の分割、同じ多項式標的の非特異性と係数を検査する。
フルビルド・集約ルート・全テストはユーザー側の分担を維持する。

最終確認は次の対象だけを実行し、すべて警告なしで通過した。

```text
./lean-build.sh DkMath.FLT.FreyFiniteKernelGoodReduction
./lean-build.sh DkMathTest.Lib.NumberTheory.EllipticFiniteKernelGoodReduction
./lean-build.sh DkMathTest.Lib.NumberTheory.EllipticFiniteKernelVeluEquation
./lean-build.sh DkMathTest.Lib.NumberTheory.WeierstrassNodalVelu
lake env lean docs/dev/FLT-GN-regular-261018-v0/evidence/Note032GoodReductionSmoke.lean
lake env lean tmp/note032-good-reduction/Axioms1.lean
lake env lean tmp/note032-good-reduction/Axioms2.lean
lake env lean tmp/note032-good-reduction/Axioms3.lean
```

新規本体は4所有者・13定理。標数5の実例は6定理・5定義、Source37は3定理。
一般化した既存11所有者の95公開宣言も含め、計122宣言を40・40・39・3に分散して公理監査した。
依存公理は`propext`、`Classical.choice`、`Quot.sound`だけだった。
標数0の非巡回9点核と、標数2・3の既存節点核の回帰例も再ビルドした。
Lib依存方向、docstring・昇格マーカー、16本体・テストファイルのモジュールマーカー、
入口への静的登録、禁止構文、変更範囲、空白を確認した。
既存NOTEと前段の証拠を変更せず、集約入口のビルドをこの対象検証へ読み替えていない。

初期の実例では、有限体の素数性・2非零性の型クラス不足と、点群の演算インスタンスの
不一致が問題となった。数値判定と型クラスを明示し、一般定理が呼出し元の`DecidableEq k`を
受け取る形で修正した。heartbeat上限を引き上げて残す処置はしていない。
