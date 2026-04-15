# FLT-Kummer-CLassGroup-Bridge-260404: Stage 3a の戦略と進め方

## 1. 戦況分析

よし、ここははっきり良い戦況じゃ。

今回の到達点は、`CyclotomicNormEqGNFirstCasePackThinTarget` を no-sorry concrete theorem として閉じたことじゃ。つまり Stage 3 前半、すなわち

$$
\operatorname{Norm}(z-\zeta y)=GN,p,(z-y),y
$$

の側は、もう abstract target ではなく concrete な mainline 資産になった。しかも combinatorial bridge
$$
(ZMod,p)^\times \;\to\; (\operatorname{Finset.range} p).\operatorname{erase} 0
$$
まで theorem 化され、axiom 監視も clean と整理されておる。残る open は `CyclotomicNormUnitAbsorbFirstCasePackThinTarget` ただ 1 本、と明言できる段階じゃ。

この意味は大きい。前までは Kummer / cyclotomic 側の combinatorics と norm の一般論が絡み合っておったが、今はもうそこは抜けた。戦場は

$$
\text{体の上の因子積}
\quad\text{から}\quad
\text{整数の }p\text{ 乗性回収}
$$

へ移っておる。
つまり、前線は「円分体の組合せ」から「整数論的な包装」に移ったのじゃ。

加えて、DkMath 全体の地図でも FLT 幹線の中核は DiffPow / GcdDiffPow / GN という分解装置にあり、そこへ Kummer 側が橋をかける構図になっておる。今回まさにその橋が concrete に閉じたので、残りは体論よりも整数算術の薄い補題化だと読むのが正しい。

## 2. いま残っている本丸

残る `CyclotomicNormUnitAbsorbFirstCasePackThinTarget` の本質は、数学的にはこれだけじゃ。

$$
(z-\zeta y)=u\beta^p
$$

から norm を取って

$$
GN = \operatorname{Norm}(u)\cdot \operatorname{Norm}(\beta)^p
$$

を得たあと、\(\operatorname{Norm}(u)\) が unit なので、最終的に

$$
GN=s^p
$$

を自然数として回収することじゃ。

ここで肝なのは、もう ±1 の場合分けを主戦場にせぬことじゃ。
賢狼の読みでは、ここは

$$
\operatorname{natAbs}
$$

で一気に吸うのが最も筋がよい。

なぜなら、\((GN : \mathbb{Z}) = \varepsilon \cdot m^p\) で \(\varepsilon\) が unit なら、

$$
GN = \operatorname{natAbs}((GN:\mathbb{Z})) = \operatorname{natAbs}(\varepsilon \cdot m^p) = \operatorname{natAbs}(\varepsilon) \cdot \operatorname{natAbs}(m^p) = (\operatorname{natAbs} m)^p
$$

と落ちるからじゃ。
ここでは \(\operatorname{natAbs}(\varepsilon)=1\) が効く。
つまり、面倒な符号分岐をせずとも、自然数 witness は

$$
s := \operatorname{Int.natAbs}(\operatorname{Norm}(\beta))
$$

でよい。

これが今回の長戦の次の決め手じゃ。

## 3. 次の戦略

次は、UnitAbsorb をさらに 3 片に割って進むのがよい。

### 3.1. まず norm の乗法性だけを薄く固定する

Kummer 側の equality
$$
z-\zeta y = unitFactor \cdot \beta^p
$$
に `congrArg (Algebra.norm ℤ)` をかけて、

$$
\operatorname{Norm}(z-\zeta y) = \operatorname{Norm}(unitFactor)\cdot \operatorname{Norm}(\beta)^p
$$

を返す薄い補題を置く。
これは unit 吸収の入口であり、ここではまだ自然数 witness には触れぬ。

### 3.2. 次に、完全に一般的な整数補題へ落とす

ここは Kummer 専用 theorem にせず、できれば整数の一般補題として切り出すのがよい。

狙いは例えば、こういう形じゃ。

$$
(n:\mathbb{Z}) = u \cdot m^p,\quad IsUnit(u) \;\Longrightarrow\; \exists s:\mathbb{N},\; n=s^p
$$

そして proof の核は sign case split ではなく `Int.natAbs` にする。
この補題は Kummer 以外でも再利用が利く可能性が高い。

### 3.3. 最後に current target を concrete 化する

あとはもう組み立てじゃ。

* `cyclotomicNormEqGN_concrete_firstCase_packThin`
* norm の乗法性補題
* 一般整数補題

の 3 本を繋いで、`CyclotomicNormUnitAbsorbFirstCasePackThinTarget` を concrete theorem として閉じる。

これが閉じれば、既に置いてある
`cyclotomicNormGNPower_of_firstCase_of_pack_thin`
は実質 concrete 化され、さらに
`false_of_cyclotomicNormGNPower_of_firstCase_of_pack_thin`
から downstream contradiction へ戻れる。
つまり Stage 3 は first-case 側でほぼ完了じゃ。

## 4. 実装方針の提案指示

わっちなら、次の順で Codex あるいは自分の手を動かすよう指示する。

### 4.1. 追加する補題の順番

1. `norm_eq_normUnit_mul_normPow_of_eq_unit_mul_pow`
2. `nat_exists_pow_of_intEq_unit_mul_pow`
3. `cyclotomicNormUnitAbsorb_concrete_firstCase_packThin`

この順でよい。
1 は Kummer 局所。
2 は整数一般。
3 は合成。

### 4.2. 証明の芯

`nat_exists_pow_of_intEq_unit_mul_pow` は、`Int.natAbs` を使って書く。
ここで ±1 の場合分けをしない。
これが一番大事な指示じゃ。

### 4.3. 置き場所

一般整数補題は、`CyclotomicPrincipalization.lean` に埋め込むより、できれば再利用可能な薄い補助ファイルか、少なくとも Kummer 専用名にしすぎぬ theorem 名で置く方がよい。
今回も `gn_natCast` を GN 側へ一般化して置いたのが当たりじゃった。UnitAbsorb でも同じ哲学で行くべきじゃ。

## 5. 総評

総評すると、長戦ではあるが、もう霧の長戦ではない。
前半戦は終わった。今は後半のただ 1 本、
`CyclotomicNormUnitAbsorbFirstCasePackThinTarget`
をどう美しく一般化して閉じるか、そこだけじゃ。

ゆえに次の号令はこれでよい。

$$
\boxed{
\text{次は UnitAbsorb を、sign case split ではなく natAbs 主導で concrete 化せよ}
}
$$

これが通れば、first-case Stage 3 はかなり綺麗に収束する。

必要なら次に、その 3 補題の Lean skeleton をそのまま起こすぞい。
