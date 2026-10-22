# NOTE-031 第2部: 絶対慣性の持ち上げと同じFrey表現への輸送

日付: 2026-10-22（JST）。**031-001Bを実装し、031-001の局所大域輸送を完成した。**
前回の有限ガロア拡大の算術に、整数閉包と付値環を通じた慣性元の持ち上げを接続した。
全ての有限素点の絶対慣性群を含む開部分群は全群となり、
実際の有理曲線のtorsion表現、同じFrey Sourceの残余表現へ適用できる。

Freyの局所自明性は引き続き明示入力である。
031-002〜004の局所算術、031-005の全素数での二択の統合、hcases・hnoは今回供給していない。
今回の完成は031-001であり、NOTE-031全5ステップの完成とは区別する。

## 1. 公開入口とファイル

本体7ファイルに公開宣言19個、回帰ファイルに公開定理9個を追加した。
新規公開APIに日本語の教科書docstring、全新規Leanファイルに指定のマーカーを付けた。
Lib・FLT・テストの通常入口へ組み込んだ。

| モジュール | 宣言数 | 数学的役割 |
|---|---:|---|
| `DkMath.Lib.NumberTheory.ValuationInertia` | 2 | 素数上の付値環の住所と全ガロア群における慣性群の像 |
| `DkMath.Lib.NumberTheory.IntegralClosureInertiaLift` | 1 | 有限慣性元を整数閉包の合同を満たす絶対ガロア元へ持ち上げる |
| `DkMath.Lib.NumberTheory.ValuationInertiaLift` | 3 | 局所化DVRの分数表示、単元分母の整数表示、付値環の慣性への接続 |
| `DkMath.Lib.NumberTheory.AbsoluteInertiaGeneration` | 2 | 持ち上げの合成と開部分群=全群 |
| `DkMath.Lib.NumberTheory.AbsoluteInertiaRepresentation` | 5 | 開核を持つ同じ表現のFixed/Cofixedへの輸送 |
| `DkMath.Lib.NumberTheory.EllipticInertiaTransport` | 3 | 実際の非零n-torsionで開核を供給した入口 |
| `DkMath.FLT.FreyInertiaTransport` | 3 | 同じSource・同じ残余空間・同じ部分加群の公開接続 |

中心となる絶対ガロア群の定理は次である。

```text
Γ = Gal(ℚ̄/ℚ)
H : Subgroup Γ
hopen : IsOpen (H : Set Γ)
hunr : ∀ q, q.Prime → ∀ A : ValuationSubring ℚ̄,
  LiesOverPrime A q → inertiaSubgroupIn A ℚ ≤ H
──────────────────────────────────────────────────────
H = ⊤
```

ここで`LiesOverPrime A q`はqがAの非単元であること、
`inertiaSubgroupIn A ℚ`はAの分解群内の慣性群をΓへ写した像である。
付値環は各素数について全て量化する。一つの付値環を選ぶだけの仮定へ弱めていない。

## 2. 有限慣性元から整数閉包へ: 二回の補正

有限正規中間体L、整数環の素点Q、その慣性群に属するτを取る。
整数閉包B=integralClosure ℤ ℚ̄の上の極大イデアル𝔔を整数性から選ぶ。
τはℚ̄の自己同型σ₀へ延長できるが、その延長が最初から𝔔を保存するとは限らない。

まずGal(ℚ̄/L)の素点上の推移性を使い、σ₀を𝔔の安定化群へ調整する。
次に、その自己同型がB/𝔔に誘導する作用を見る。
τはQの慣性元なので、その作用は𝓞 L/Qを固定する。
Mathlibのprofinite不変式論にある剰余体作用の全射性で、この剰余体自己同型を
Gal(ℚ̄/L)の𝔔の安定化群の元tへ持ち上げる。
tの逆元で補正すると、Lへの制限τを変えずに剰余体作用が恒等となる。

結論は、実際の絶対ガロア元σについて、

\[
\sigma|_L=\tau,\qquad
\forall b\in B,\quad \sigma b-b\in\mathfrak Q
\]

という合同である。Leanの結論では、差を表すBの元c∈𝔔を明示する。
この段階では付値環全体の慣性とまだ同一視しない。

## 3. 整数閉包の合同を付値環全体へ広げる

𝔔を中心とする付値環Aを選ぶ。
整数閉包からAの極大イデアルへの引き戻しが𝔔に一致することを、𝔔の極大性から示す。
従って、代数的整数sが𝔔を外れることと、Aで単元になることが一致する。

必要な分数表示は次である。

\[
a\in A\quad\Longrightarrow\quad
\exists x,s\in B,\qquad s\notin A^{\mathrm{nonunits}},\quad as=x.
\]

これを仮定に置かず、aが生成する有限数体へ降りて証明した。
その整数環の素点での局所化はDVRなので、非零aまたはa⁻¹の分数表示が得られる。
a⁻¹が非単元となる場合は、a∈Aによる付値≤1と積a·a⁻¹=1に反する。
零の場合はx=0、s=1で処理する。

単元分母の表示を使うと、σx=x+c、σs=s+c′、c,c′∈𝔔から、

\[
\sigma a-a=\frac{cs-xc'}{\sigma(s)s}
\]

となる。分母の付値は1、分子の付値は1未満なので、差はAの非単元となる。
σ⁻¹にも同じ合同を証明し、σがAを両方向に保存することを確認する。
これで分解群に属し、剰余体上の作用が恒等であることから慣性群に属すると分かる。
一方向の環の保存だけで分解群所属を結論していない。

## 4. 開部分群への有限正規レベルの接続

開部分群Hの単位元近傍から、Krull位相の基底を使って有限正規中間体Lを選ぶ。
Lの固定部分群はHに含まれる。
制限写像res:Γ→Gal(L/ℚ)でのHの像を調べる。

Lの任意の極大イデアルQの剰余標数qは、剰余体の有限性から素数となる。
Qの全慣性元を第2・3節の証明でq上の絶対慣性元へ持ち上げれば、
hunrによってその持ち上げはHに入る。
従ってres(H)はLの全有限慣性群を含み、前回の031-001Aの算術から全群となる。

任意のσ∈Γについて、同じ制限を持つh∈Hを選ぶ。
h⁻¹σは制限の核、すなわちLの固定部分群に属するのでHに入る。
従ってσ∈Hとなる。Hの正規性は要求しない。
開性を省いて稠密性から等号を結論したわけではない。

## 5. 同じ実際の表現へ接続するDkMathの核

前回の`LocalFixedCofixed.fixedSubgroup`と`cofixedSubgroup`は、どちらも表現ρの核を含む。
ρの核が開けば、両方の部分群も開く。
全ての絶対慣性でNが点ごとに固定される、または全変化量がNに入るなら、
上の開部分群定理からそれぞれ大域`IsFixedOn`・`IsCofixedOn`となる。
この議論にはNの一次元性や安定性の追加入力は不要である。

一般表現では開核を明示入力として残す。
実際の非零n-torsionでは、既存の除法多項式による有限性と座標作用の連続性から開核を供給する。
楕円曲線用の入口はn≠0を要求するが、位数n²・次元2・Weil対を追加仮定に取らない。

Freyの公開入口は素数pの同じSourceについて、

```text
S.residual_isFixedOn_of_inertia N hlocal
S.residual_isCofixedOn_of_inertia N hlocal
S.residual_fixed_or_cofixed_of_inertia_common_side N hside
```

である。SやNを選び直さず、開核・有限性・持ち上げ・生成性の外部入力はない。
この輸送にはp≥5・b偶数は不要である。
これらの条件は今後のFrey局所算術を証明する段階で保持する。

共通側の前提は(全素点でFixed)∨(全素点でCofixed)である。
各素点で独立に二択を選ぶ前提からは結論しない。
同じSourceの正規化、共通因子、向き付け、曲線、点の既存データを変更していない。

## 6. 回帰と依存監査

回帰では、有限慣性元τ≠1の持ち上げがσ≠1を保つこと、
真の開部分群にはある実際の絶対慣性元が含まれないことを証明した。
さらにq=1が住所条件を満たさないことと、単元分母の非零性を検査した。

Source 37では、開核の追加仮定なしのFixed・Cofixed・共通側の二択を型検査した。
大域Cofixedが失敗すれば、ある素数q・q上の付値環A・慣性元σ・同じ空間の点xで
ρ(σ)x−xが同じNを外れることも証明した。
これらはSource 37やFermat反例の存在を主張しない。
前回の有限表現の安定直線の境界例も保持し、局所二択の量化順序を変えていない。

公理・依存監査は新規19宣言と回帰9宣言を対象とする。
主要16経路で型とopaque本体まで走査し、profinite剰余体作用の全射性、DVR、
単元分母、Krull有限正規レベル、Minkowski、実際のtorsion有限性・開核への到達を要求する。
公開入力4件では開性・局所条件・同じSourceを保持し、生成性等の外部仮定を追加していないことを検査する。
指定経路の検査と、リポジトリ全体の公理自由性は区別する。

## 7. 出典と再構成

[出典台帳](evidence/upstream-note031-001B.json)に4ファイルのblob SHAと利用区分を保存した。
前回読み取ったソースを再利用し、取得時の内容を基に再構成した。
参照リンクは上流のmainを指し、取得時点の識別子は別途台帳に保持する。

- [整数閉包への持ち上げ](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_NumberField_exists_lift_mem_inertia_integralClosure.lean)
- [付値環への接続](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ValuationSubring_exists_liesOverPrime_mem_inertiaSubgroupIn.lean)
- [開部分群=全群](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicClosure_subgroup_eq_top_of_inertiaSubgroupIn_le.lean)
- [慣性の定義](https://github.com/anthropics/fermats-last-theorem/blob/main/Definitions/Def_FLTPrelim_Ramification.lean)

該当4モジュールにApache-2.0・著作権・変更内容・SHA・LICENSE/NOTICEの所在を記した。
外部のFreyPackage・GaloisRepをimportせず、定義はDkMathの名前空間へ分けた。
付値環の証明は三つの意味ある公開段階へ分け、Mathlibの変更に合わせてイデアルの引き戻し、
有限剰余体のAPI、作用の型を調整した。
表現への接続はDkMathの既存Fixed/Cofixed・実際のtorsion・開核を再利用して構成した。
ライセンスの参照先RegularKummerと、そのLeanコードへの依存は別である。

## 8. 五段階の現在地

| 段階 | 現在地 |
|---|---|
| 031-001 | **完了**。001Aの有限算術と001Bの絶対慣性持ち上げ・開部分群・実際の表現への輸送 |
| 031-002 | 次。q≠2,pで実際のFrey残余表現の慣性自明性を供給 |
| 031-003 | 未実装。2で部分空間・商の両方が固定される局所算術 |
| 031-004 | 未実装。pで一貫した側を選ぶ局所二択 |
| 031-005 | 未実装。全素点で選んだ側を保持し、同じSourceのhcasesへ接続 |

次の031-002では、既存の判別式・c₄・還元型の算術と、実際のE[p]の慣性作用を比較する。
良還元や乗法的還元を分類するだけでは、今回のhlocalはまだ埋まらない。
NOTE-030のhrat供給は維持されている。hcases・hno、無条件既約性・一般FLTは引き続き未完成である。

## 9. 検証結果

監査を含む集中ビルドは3,876ジョブ、通常の本体・FLT・Lib・テスト入口のビルドは
11,708ジョブで成功した。新規コードに警告・sorryはない。
新規19宣言と回帰9宣言の公理は`propext`・`Classical.choice`・`Quot.sound`のみであり、
主要16経路と公開入力4件の依存監査も通った。

`lake env lean DkMathTest.lean`、通常ルートから8入口を確認するスモーク、
マーカー照合、全新規ファイルの体裁・docstring・禁止構文検査、`git diff --check`も成功した。
全体ビルドには既存の無関係な5件のsorry警告が再掲された。
具体的なコマンドと結果は[検証記録](evidence/validation-note031-001B.txt)に記録した。
