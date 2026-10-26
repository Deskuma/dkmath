# NOTE-032 全ファイバー・全射性・主因子の大域輸送

2026-10-26 / `dev/FLT-GN-regular-261018-v0`

## 今回の到達点

標数0の楕円曲線Eと奇数位数の有限部分群Hについて、既存の同じ標的モデル・全点関数φ・関数体引き戻し・軌道積を保持した。任意ファイバー=H剰余類、全射性、全ファイバーの位数|H|、有限支持主因子の押し出しを一括実装した。主因子で割った因子群の間の加法準同型も構成した。

**点群に関するφの加法性は未証明。** 今回の加法準同型の定義域と値域は因子群または因子類群である。点と次数0の因子類を結ぶAbel対応が次の数学的課題となる。

## 証明の教科書

### 別軌道の分離から、任意ファイバーの決定へ

`EllipticFinitePointApproximation`は座標環の中国剰余定理を使い、有限集合の一点では単純零点、他点では単元となる実際の関数を構成する。`EllipticFiniteKernelFibers`は二つの互いに交わらないH軌道にこれを適用し、軌道積を同じ標的関数へ降ろす。

仮に別軌道のPとRが同じ像なら、前回の正規化付値比較により、その標的関数の同一点での位数が1と0になり矛盾する。したがって

```text
φ(P) = φ(R) ↔ R − P ∈ H
```

が成立する。既知の核による平行移動不変性と合わせ、`kernelFiberEquiv`はHとφ(P)のファイバーの実際の同値写像を与える。ここではφの点加法性を使用しない。

### 無限遠での次数から、標的の全点への到達へ

`RationalFunctionFiniteFiber`は、既約有理式r=N/Dに対してdeg D<deg Nなら、任意のcでN−cDに根があり、その根でDは非零であることを証明する。後者はNとDの互いに素性による。

`EllipticFiniteKernelSurjective`では、同じX_Hの有理式表示に無限遠の極位数を接続し、分子次数|H|・分母次数|H|−1を得る。代数閉包上では任意のxに対する源のyが存在し、上の有理式の根からX_H(P)=cとなる核外点Pを得る。標的で同じxを持つ二点は互いに反対であり、既存のφの反転保存からPまたは−Pが任意の標的点を持ち上げる。OはOから持ち上がる。

これにより`oddKernelPointMap_surjective`と、全Tについてファイバーの位数が|H|となる`card_kernel_fiber`が成立する。同じ安定核の既存K係数モデルへの移送についても全射性とファイバー条件を公開した。

### 有限支持因子、ノルム、因子類

`ValuationDivisor.IsPrincipal v D`は、有限支持整数関数Dに対して、非零の実際の関数fが存在し、全点でD(P)=−log(v_P(f))となる条件である。有限支持はDの型`A →₀ ℤ`に保持される。任意の付値族で全てのfの位数が有限支持となる、あるいは全主因子の次数が0となるとは主張していない。

`kernelDivisorPush`は、同じ全点関数に沿う整数重みの加算である。係数公式は

```text
(φ_* D)(φ(P)) = ∑ Q : H, D(P + Q)
```

となり、有限支持因子の整数次数を保存する。全射性により任意の標的点でこの式を使用できる。

Dがfの主因子なら、前回の全点軌道積位数公式から、φ_*Dは同じ`kernelModelNorm f`の主因子となる。これが`kernelDivisorPush_isPrincipal`である。主因子は加法部分群をなし、商への写像`kernelDivisorClassPush`を誘導する。代表因子[P]−[O]は[φ(P)]−[O]に送られ、その因子類についても同じ等式を証明した。

今回の商は**全有限支持因子を主因子で割った群**である。これをPic⁰または点群と同一視する定理はまだ供給していない。点群の加法性を閉じるには、同じ付値による主因子の定義とAbel対応を接続する必要がある。

## 所有モジュールと公開入口

| 所有者 | 公開する内容 |
| --- | --- |
| `EllipticFinitePointApproximation` | 有限点集合上のCRTパラメータ |
| `RationalFunctionFiniteFiber` | 分子次数優勢の有理式の有限ファイバー存在 |
| `EllipticFiniteKernelFibers` | 別軌道の分離、正確なファイバー、Hとの同値 |
| `EllipticFiniteKernelSurjective` | 全射性、全ファイバー位数、同じ降下モデルへの移送 |
| `ValuationDivisor` | 有限支持主因子とその加法部分群 |
| `EllipticFiniteKernelDivisor` | 因子押し出し、主因子保存、因子類の準同型 |
| `EllipticWeilDivisor` | 既存Weil関数による有限支持主因子 |
| `FreyFiniteKernelGlobal` | 同じSource・残余直線・核に対する公開定理 |

Lib所有者はFLTをimportしない。各所有者に教科書docstring、`[DkMath.Lib]`昇格マーカー、import直後のファイルマーカーを付けた。`DkMath.Lib`、`DkMath.FLT`、`DkMathTest`の既存入口へ登録した。入口全体のビルド確認は今回の対象モジュール検証には含まれない。

## 模範証明との対応

ローカルに保持されたanthropicsの模範証明では、場所の押し出し、主因子保存、点差因子、Pic⁰の押し出し、種数1の点とPic⁰の同値、同じ点関数との一致という順序を確認した。

参照した[模範証明blob](https://api.github.com/repos/anthropics/fermats-last-theorem/git/blobs/fa5eda1fdc857b6445c21720c78805e7ecded543)のGit blobハッシュを照合した。今回は外部の証明ライブラリをimportせず、DkMathのCRT・実点付値・既存軌道積を使って有限支持因子の段階を再構成した。全射性は同じX_Hの有理式の次数から直接証明した。

## 実例と検証

本体は8所有者、29定理・8定義、707行。対象テストは9定理・1定義。曲線y²=x³−x上の実際の全3捩れ核H（位数9）について、有理式分子次数9・分母次数8、全射性、全ファイバー位数9、既存ℚ係数モデルの全射性を確認した。

さらに実際の非零2捩れ点R=(−1,0)と既存Weil関数を用いた。二つの[2]ファイバーは各4点で、その差から非零主因子Dを作った。φ_*Dが主因子であり、実際の像点で係数1を持つことを証明した。零因子だけの検査ではない。Weil関数のn≠0、nT=0という前提は保持した。

Source37の4定理で、同じ残余直線の一次元性から全射性・正確なファイバー・各ファイバー位数37・主因子保存への接続を確認した。

検証対象は以下である。

- `./lean-build.sh DkMath.FLT.FreyFiniteKernelGlobal`
- `./lean-build.sh DkMathTest.Lib.NumberTheory.EllipticFiniteKernelGlobal`
- Source37を含む直接Lean検証と51宣言の公理監査。
- 禁止構文・外部証明import・Lib依存方向・docstring・ファイルマーカー・入口登録・既存所有者保持・差分空白の検査。

結果は[evidence](evidence/note032-global-fibers-divisor.json)と[検証記録](evidence/validation-note032-global-fibers-divisor.txt)に記録する。フルビルドと全testは実行対象に含めていない。

## 次に必要な証明

次は点差の因子類P↦[[P]−[O]]を、同じ楕円曲線の点群へ接続するAbel対応である。その加法性と単射性を確立すれば、今回の因子類準同型および点差代表の一致から、同じφの点加法性へ進める。

isogeny構造、Cofixed像のp捩れ性、整数係数モデル、局所還元保持、零成分輸送、一般hnoは未完了である。今回の全射性・ファイバー計数だけでそれらを結論しない。
