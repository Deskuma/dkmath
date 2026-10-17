# 共通商の共役位相と実三次ノルム平方

2026/10/17 JST

実装: [SevenCurrentQuotientReal.lean](../../../DkMath/FLT/Kummer/SevenCurrentQuotientReal.lean)。入口は `DkMath.FLT.Kummer`。
前章: [六根の深い合同](SEVEN-CURRENT-ROOT-DEEP-CONGRUENCE.md)。

## 1. 根ではなく商を実三次環へ戻す

`g = ofReal (rotateEquiv rho - rho)`、`λ = 1-ζ` とする。
実三次環で `rotateEquiv rho-rho = axis^32 v` という同じ証人を選ぶ。
`ofReal axis = ζ⁻¹ λ²` と `ζ⁷=1` より

\[
g=\lambda^{64}\zeta^3\operatorname{ofReal}(v).
\]

λは非零なので、任意の `g=λ^64 w` を満たす商も
`w=ζ³ ofReal v` となる。`common_quotient_eq_real` がこの一意性を保持する。
共役すると `star w = ζ w`。抽象的な固定環の分類は使わず、実際の実三次商を使っている。
これは六つの根自身の実性を主張するものではない。

## 2. 六位相で共通する正の平方因子

相対二次ノルムは `N(ofReal v)=v²`、ζの六次ノルムは1なので

\[
N_C(w)=N_R(v)^2.
\]

前章の同一商による六位相ノルム等式と合わせると

\[
|N_C(\theta_i^7+u)|=7^{63}|N_R(v)|^2=7M^2,
\quad M=7^{31}|N_R(v)|.
\]

`phase_root_correction_norm_seven_square` は全六位相に同じMを返す。
正値性を含む版と `phase_root_correction_norm_valuation_odd` も実装した。
正値性は既存の `DirectOrbitSmallerNormPacket` の非零ノルムから得られるため、
この結果には追加の common-prime packet 引数を必要としない。
付値は `1+2*v₇(M)` で奇数だが、63が正確な付値という意味ではない。

## 3. 保存と減少を同じ元で結ぶ

既存の小ノルムパケットSの `powerSplit` は

\[
\operatorname{gap}=\operatorname{axis}^{32+42k}
                    \varepsilon\operatorname{gapRoot}^{7}
\]

を持つ。従って、同じSから

\[
v=\operatorname{axis}^{42k}\varepsilon\operatorname{gapRoot}^{7},
\quad w=\zeta^3\operatorname{ofReal}(v)
\]

が成立する。`common_quotient_smaller_packet` はこの元の等式と、同じSの
`normRoot = |N_R(gapRoot)|`、`0<normRoot<gapSplit.a` を一緒に返す。
別々に存在する証人を取り違えていない。
さらに `phase_root_correction_norm_smaller_packet` は

\[
|N_C(\theta_i^7+u)|=
7\left(7^{31+42k}\operatorname{normRoot}^{7}\right)^2
\]

を同じSについて証明する。保存商と既存の小さい根の間に実際の元の等式ができた。
ただしその根から次の七乗方程式の source、原始性、分岐条件を構成し、
同じ新状態で再入条件と測度減少を証明する仕事は残る。ここまでを厳密降下やFLT7の完成とは数えない。

## 検証

12個の公開定理を公理 whitelist で検査する回帰モジュールを追加した。
4例で、任意の商の共役位相、正の共通M、奇数付値、同一小ノルムパケットとの等式を確認する。
実行結果は [検証記録](evidence/validation-seven-current-quotient-real.txt) を参照。
