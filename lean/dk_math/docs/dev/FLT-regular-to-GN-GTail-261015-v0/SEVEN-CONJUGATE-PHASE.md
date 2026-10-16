# FLT7 第二段：GN 一次単元の共役位相固定原理

2026-10-16。第一段の [相対ノルム七乗性](SEVEN-PRIMARY-NORM.md) に、
共役比の解析を接続した。添付の「共役比」の考察は数学的な提案として読み、
一般 FLT の外部証明は導入していない。

今回の結論は、**整数と mod 7 で合同な七次円分単元そのものが七乗であること**。
同じ GN 保存パケットの一次単元に適用し、未解析単元を残さない因子表示まで得た。
現在の `currentLinearCarrier` との来歴の対応、および反復可能な降下は、この章の結論に含めない。

## 1. 積と比で単元の平方を観測する

`K = CyclotomicField 7 ℚ`、`O = 𝓞 K` とし、前章の環同型を `e : O ≃+* C` と書く。
`C` は実三次環 `R` 上の既存の二次モデルである。

```text
integralConj = e⁻¹ ∘ star ∘ e
conjugateRatio(u) = u * integralConj(u)⁻¹
```

共役比は単元群内で定義する。分母の逆元も整数環の単元であり、体だけに移して
分母を消したことにはしない。

`unit_square_eq_norm_mul_ratio` は、仮定のない次の恒等式を与える。

\[
e(u)^2=\operatorname{ofReal}(N(u))\,e(\rho(u)).
\]

ノルムが共役との積を保存し、共役比が残りの位相を保持する。
この二つを掛けると共役因子とその逆元が消えて、元の平方へ戻る。

## 2. 二次共役は本当に CM 共役か

`septicRoot` は Mathlib が選ぶ原始七乗根であり、`integralEquiv_septicRoot` が
その整数環への持ち上げを具体的 `zeta` へ送ることを証明する。

具体的二次代数では

\[
\operatorname{star}(\zeta)=(\alpha-1)-\zeta=\zeta^6.
\]

一方、CM 体の複素共役は根付き単位を逆元へ送るので、抽象円分体でも
`σ(ζ)=ζ⁻¹=ζ⁶` となる。
`integralConj_eq_CM` はこの生成元での一致を整数冪基底によって全体へ拡張する。
単なるノルム値の一致を共役の同定に代用していない。

この補題の `[IsCMField K]` は識別に使う型クラスである。
後続の `conjugateRatio_finite` は既存の円分体の CM 定理からこれを供給するため、
公開された七乗判定に CM 性の追加引数はない。

## 3. 共役比の正体は有限個の円分位相

CM 単元定理 `NumberField.IsCMField.unitsMulComplexConjInv` を適用すると、
任意の単元 `u` の共役比は有限位数である。
`conjugateRatio_finite` がこの定理を実際に消費する。

七次円分体の有限位数の元の分類により、候補は

\[
\rho(u)=\pm\zeta^r,\qquad 0\le r<7
\]

となる。CM の議論だけで比が1になったわけではない。
次の合同情報によって候補を識別する。

## 4. mod 7 の合同が位相を1に固定する

`7 | u-n` とすると、共役は整数を固定するので `7 | σ(u)-n`。
差を取り、共役単元の逆元を掛けることで

\[
7\mid u-\sigma(u),\qquad
7\mid (u-\sigma(u))\sigma(u)^{-1}=\rho(u)-1
\]

を得る。整数 `n` を割る必要はない。
`conjugateRatio_congruent_one` は単元の逆元を割り算の証人に掛ける証明である。

次に、整数冪基底 `1,ζ,…,ζ⁵` の六座標を使う。
可除性 `7 | x` は各整数係数の `7` 可除性を意味する。

| 候補 | 係数比較で検出する内容 |
|---|---|
| `ζ⁰=1` | 合同条件を満たす |
| `ζʳ`, `1≤r≤5` | `ζʳ−1` の定数係数が `−1` |
| `ζ⁶` | `1+ζ+…+ζ⁶=0` より、差の定数係数が `−2` |
| `−ζ⁰` | 差の定数係数が `−2` |
| `−ζʳ`, `1≤r≤5` | 差の定数係数が `−1` |
| `−ζ⁶` | 差の `ζ` 係数が `1` |

7 はこれらの非零な小さい係数を割らない。
`septic_rootOfUnity_eq_one_of_congruent` が14候補を検査し、
`conjugateRatio_eq_one` が有限位数の分類と結合する。

\[
\boxed{u\equiv n\pmod7\quad\Longrightarrow\quad\rho(u)=1,
\quad u=\sigma(u).}
\]

添付文書の λ 進深度による説明とも整合するが、この実装では付値の新しい補題を
入力にせず、整数係数を直接比較した。
mod λ と mod 7 を混同していないことは、前章と今回の非自明位相の反例検証で確認する。

## 5. 平方から七乗根を作る

前章のノルム根を具体的六次環へ埋め込んだ単元を `η` とすると、

\[
u\sigma(u)=\eta^7,\qquad u=\sigma(u),\qquad u^2=\eta^7.
\]

したがって

\[
\boxed{(u\eta^{-3})^7=u^{7}(\eta^7)^{-3}=u^{7-6}=u.}
\]

この操作は単元群の恒等式であり、別の単元分類や降下を要求しない。
`DkMath.Lib.Algebra.oddPower_root_of_square` は、一般の可換群で

\[
u^2=v^{2k+1}\quad\Longrightarrow\quad(uv^{-k})^{2k+1}=u
\]

を証明する。ここは研究固有の環から独立しているので `Lib` に置いた。
p=11,13 の式も同じ補題の `k=5,6` として検証した。
それらの指数で必要なノルム根や位相解析まで解決したという意味ではない。

## 6. 七次の Kummer 単元補題を実供給する

公開定理は次の二つである。

```lean
concrete_kummer_unit_power_criterion :
  KummerUnitPowerCriterion SevenCyclotomicDegreeSixInt.Ring 7

septic_kummer_unit_power_criterion :
  KummerUnitPowerCriterion (𝓞 (CyclotomicField 7 ℚ)) 7
```

いずれも、任意の単元とその整数合同から七乗根を構成する定理である。
単元 criterion 自体を仮定する条件付き adapter ではない。
二つの定理の間では、同じ環同型で単元と七乗等式を往復させる。

対象の抽象円分体は `CyclotomicField 7 ℚ` として固定している。
任意の型の七次円分体への輸送を新たに公開したわけではない。

## 7. 同じ GN パケットへ戻す

`GN_primary_unit_seventh` は、前章と同じ
`RamifiedPrincipalPowerPacket Q` と正規化 `γᵢ≡1 mod λ` を受け取り、

\[
\boxed{Q.\mathrm{primaryUnit}(i)=\kappa_i^7}
\]

を返す。以前のノルム値だけの結論を、単元群内の元の等式に強化した。
既存の `primaryUnit_congruent_integer` により、必要な合同は同じ Q から供給される。

`GN_factor_eq_zeta_sub_one_mul_seventh` は `θᵢ=κᵢ*γᵢ` を使って

\[
x+(1-\zeta^i)u=(\zeta^i-1)\theta_i^7
\]

を得る。さらに既存の七次 PID 定理から類数1を供給することで、
`exists_GN_septic_factor_eq_zeta_sub_one_mul_seventh` は原始的な分岐側 FLT 方程式

\[
a^7+b^7=c^7,\quad c\ne0,\quad(a,b)=1,\quad7\mid c
\]

から直接

\[
\boxed{a+\zeta^i b=(\zeta^i-1)\theta_i^7}\qquad(1\le i<7)
\]

を返す。単元補題・類数条件を追加引数に残していない。
方程式を仮定した因子表示であって、その方程式の不可能性を結論する定理ではない。

## 8. 検証と次の境界

- 新規 production: `SevenConjugatePhase.lean`、`SevenKummerUnit.lean`、`Lib/Algebra/OddPowerRecovery.lean`。公開入口 `DkMath.FLT.Kummer` と `DkMath.Lib` に接続。
- 回帰検証: 共役の向き、正・負の非自明位相の排除、実例 `alpha^7≡3 mod 7`、p=11,13 の群の根復元。
- 公理検査: 新規宣言すべてを標準三公理だけの whitelist で検査する。
- 再帰的依存監査: 七次 criterion、同じ GN 単元の根、FLT 入力からの因子表示の三つを、型・opaque 本体・構築子まで辿る。旧 FLT 終点と三次・五次 criterion を禁止し、CM 共役比・六座標識別・実三次判定・ノルム根・群の根復元の実使用を要求する。

実行結果は [検証記録](evidence/validation-seven-conjugate-phase.txt) を参照。

残る課題は `currentLinearCarrier` の未解析単元と今回の `δᵢ` の来歴の対応を、
固定した分岐因子と元の等式で証明すること、その後で反復可能な降下パケットを構成すること。
同じ六次環に属することや等しいノルムだけでは、これらの対応を代用できない。
今回、FLT7 全体の証明および一般 FLT の証明は追加していない。
