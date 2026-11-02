# NOTE-032 教科書: 同じ Kummer 類の円分二乗作用

日付: 2026-11-02。
前章: [同じ体の Kummer 表示](TEXTBOOK-N032-CYCLOTOMIC-KUMMER-261102.md)。
実装: `KummerRadicalCharacter`、`CyclotomicKummerWeight`、`FreyCyclotomicKummerWeight`。

今回は、非分裂から得た同じ Kummer 定数の非自明な類について

\[
\boxed{\gamma[b]=[b]^{\omega(\gamma)^2}}
\quad\text{in }F^\times/(F^\times)^p,\qquad F=\mathbb Q(\zeta_p)
\]

を Lean で証明した。商群を加法的な `F_p` 加群に読み替え、
同じ非零ベクトルに対する線形な固有条件も証明する。
代表元での正確な結論は `γ(b)=b^r c^p`、`c∈F`、`c≠0`。
`r` は `ω(γ)^2` の標準代表元であり、補正因子を捨てた `γ(b)=b^r` ではない。
類群・単数の算術によるこの非零類の消滅は未実装であり、一般 `hno` は未完成である。

## 1. 同じ対象を保つ

`p≥5` と、同じ Frey Source、Cofixed 直線、底を含む大域安定な巡回段 `K` を固定する。
`|K|=p^m`、`m≥1` である。これまでの商・指標・固定体は

\[
V=(p^{-1}K)/K,\quad C=\operatorname{image}(E[p]\to V),\quad
\Gamma=\ker\chi_p,\quad \psi_v:\Gamma\to(C,+),\quad
M=\overline{\mathbb Q}^{\ker\psi_v}.
\]

大域非分裂から、一つの `ψ_v` が位数 `p` の `C` へ全射する。
同じ `M/F` の Kummer 表示 `P` が、同じ元

\[
\alpha\in M,\quad b\in F,\quad
\alpha^p=b,\quad F(\alpha)=M,\quad X^p-b\text{ 既約}
\]

を持つ。前章の固定群との一致は

\[
\psi_v(u)=0\iff u(\alpha)=\alpha\qquad(u\in\Gamma)
\]

である。今回もこの `P.radical` と `P.constant` を使う。
レビューの二乗作用の導出案を、実際の比・指標・固定体の証明として接続した。
一般的な Kummer pairing や二乗固有性を新しい仮定にしていない。

## 2. 同じ根の比は実際の指標になる

`u∈Γ` は底体を固定するため

\[
\kappa_\alpha(u)=\frac{u(\alpha)}{\alpha},\qquad
\kappa_\alpha(u)^p=\frac{u(b)}b=1.
\]

`KummerRadicalCharacter.radicalCharacter` は、この比を実際の
`rootsOfUnity p (AlgebraicClosure ℚ)` に入れる群準同型である。
`α≠0` は前章の既約性から供給する。

準同型性は、`Γ` が全ての `p` 乗根を固定することから従う。
実際、`u,v∈Γ` に対して

\[
\frac{uv(\alpha)}\alpha
=u\!\left(\frac{v(\alpha)}\alpha\right)\frac{u(\alpha)}\alpha
=\kappa_\alpha(v)\kappa_\alpha(u).
\]

この根の固定性は `cyclotomicCharacter_spec` と `χ_p(u)=1` から証明する。
`presentationCharacter` が、構成済みの同じ `P` にこの準同型を適用する。
`presentationCharacter_kernel` は

\[
\boxed{\ker\kappa_\alpha=\ker\psi_v}
\]

を証明する。ここで前章の生成性と、開核の正確な Galois 対応を実際に利用する。

## 3. 元の指標を経由する因子化は線形である

`ψ_v` は全射で、`ker ψ_v≤ker κ_α` である。
従って準同型は同じ商を経由し、

\[
f:(C,+)\longrightarrow\mu_p,\qquad f(\psi_v(u))=\kappa_\alpha(u)
\]

となる。`factor` は商群の lift と第一同型定理でこの写像を定義し、
`factor_apply` は元の準同型への復帰公式を証明する。

両辺を加法的な `ZMod p` 加群として読めば、加法準同型は自動的に `F_p` 線形である。
Mathlib の `ZMod.map_smul` を使って、この性質を明示する。
`map_scalar` は

\[
\psi_v(u)=a\psi_v(w)\Longrightarrow
\kappa_\alpha(u)=\kappa_\alpha(w)^{a.\mathrm{val}}
\]

を与える。基底・離散対数を選んで別の指標を作ってはいない。

## 4. 二つの円分因子を計算する

`σ∈G_ℚ` と `u∈Γ` を固定し、`d=χ_p(σ)∈F_p^×` とする。
`σ` は底体を動かしてよい。一方、`u` は底体を固定する。

\[
w=\sigma^{-1}u\sigma\in\Gamma
\]

とおく。元の逆円分共役則を `σ⁻¹` に適用すると

\[
\psi_v(w)=d\psi_v(u),\qquad
\kappa_\alpha(w)=\kappa_\alpha(u)^d.
\]

ここに第一の因子 `d` が現れる。次に根自身の円分作用から

\[
\sigma\bigl(\kappa_\alpha(w)\bigr)
=\kappa_\alpha(w)^d=\kappa_\alpha(u)^{d^2}.
\]

これが第二の因子である。`σw=uσ` を同じ根に適用すると

\[
\boxed{\frac{u(\sigma\alpha)}{\sigma\alpha}
=\left(\frac{u\alpha}{\alpha}\right)^{(d^2).\mathrm{val}}}.
\]

`KummerRadicalCharacter.conjugate_ratio` がこの計算を証明する。
自然数の冪の積を `ZMod p` の二乗の代表元へ戻す段階では、
根の `p` 乗が1であることと `pow_eq_pow_mod` を使う。
この指数の正規化も仮定にしていない。

## 5. 比が元の円分体へ降りる

`r=(d²).val` とし、

\[
c=\frac{\sigma\alpha}{\alpha^r}\in\overline{\mathbb Q}
\]

を実際に定義する。前節の式から全ての `u∈Γ` について `u(c)=c`。
前章の `fixedField_kernel_eq` を使い、

\[
c\in\overline{\mathbb Q}^{\Gamma}=F
\]

と結論する。`conjugate_radical_div_mem` はこの同じ比の所属を証明する。
`α≠0` と自己同型の単射性から `c≠0`。
`p` 乗を取れば

\[
\boxed{\sigma(b)=b^r c^p}
\]

となる。`constant_weight_square` は、同じ底体の実際の非零元 `c` とこの等式を返す。
絶対自己同型を同じ代数閉包に作用させて計算するので、相対自己同型の公式を
底体を動かす自己同型へ読み替える誤りを避けられる。

## 6. 底体の全自己同型へ接続する

`baseRoot` は同じ `ζ_p` を `F` の元として読み、`baseCharacter` は
その原始根への作用から実際の `Gal(F/ℚ)` 上の円分指標 `ω` を定義する。

任意の `γ∈Gal(F/ℚ)` を、Mathlib の `AlgEquiv.liftNormal` で実際に `G_ℚ` へ持ち上げる。
`baseCharacter_lift` は、持ち上げの `χ_p` 値が `ω(γ)` であることを、
同じ原始根への作用とその冪の単射性から証明する。
持ち上げ・指標の両立性の provider は残さない。

従って `base_constant_weight_square` は任意の `γ` について

\[
\exists c\in F^\times,\qquad \gamma(b)=b^{(\omega(\gamma)^2).\mathrm{val}}c^p
\]

を証明する。`M/ℚ` の別の持ち上げデータや、同型な別の Kummer 体を入力してはいない。

## 7. 実際の商群と非零固有ベクトル

既存の中立な `PowerSubgroup` を使い、

```lean
abbrev KummerClass (F : Type*) [Field F] (p : ℕ) :=
  Fˣ ⧸ DkMath.Lib.Algebra.powerSubgroup Fˣ p
```

と定義する。これは円分類群 `Cl(F)` ではなく、体の乗法群の冪による商である。
`classMap` は底体の自己同型が冪部分群を保つことから得る実際の商群への写像である。
非零定数を `Fˣ` の元 `constantUnit` として読み、その像を `constantClass` とする。

前節の `c^p` はこの商で1になるため、`constantClass_weight_square` より

\[
\gamma[b]=[b]^{(\omega(\gamma)^2).\mathrm{val}}.
\]

`constantClass_ne_one` は、もしこの類が1なら `b` が `F` の `p` 乗となり、
同じ `P.irreducible` に反することを証明する。

さらに `class_pow` により商の全元は `p` 乗で1となる。
`Additive` で積を加法へ読み替え、`kummerModule` で `ZMod p` 加群を与える。
`classLinearMap` は同じ作用を線形写像として読む。
`constantVector` を `w` と書けば、`constantVector_ne_zero` と
`constantVector_weight_square` が

\[
\boxed{w\ne0,\qquad \gamma(w)=\omega(\gamma)^2\cdot w}
\]

を証明する。これは実際の非零ベクトルに対する固有条件である。

## 8. Frey の公開終点

```lean
residual_nonsplit_has_weight_two_kummer_class
```

は、元の Source・Cofixed 直線・巡回段の全不変量・原始根・大域非分裂を入力する。
同じ `v` の全射指標と同じ固定体の表示 `P` を内部で構成し、
その定数の非自明類・非零ベクトル・底体の全自己同型についての二乗作用を返す。
根・表示・類・非自明性・固有性・持ち上げ・共役則・開核・全射性の provider を要求しない。

この終点では重みだけを計算しており、局所条件を不要とする消滅定理は主張しない。
前章の同じ `P` への局所固定性は引き続き使える。
`p` 外の共鳴住所の吸収 `hbad` は、そちらの局所定理に明示入力として残る。

## 9. 回帰検証と残る算術

回帰例では、`2^5≠1` でも有理数体の Kummer 商では同じ冪が1となることを確認する。
`F_11^×/(F_11^×)^5` の実際の非自明類を使い、`2 mod 5` の二乗の重み `4` と
逆指標の重み `3` が異なる作用をすることも確認する。
一方、`F_7` の同じ商は自明であり、任意の体に非零 Kummer 類を主張できない。
これらは商と重みの代数的な回帰例であり、Frey 拡大の局所算術の代替ではない。

再帰依存監査は、同じ根の比、因子化、`ZMod` 線形性、二つの円分因子、
元の固定体への降下、実際の持ち上げ、実際の商群・線形化、Frey の非分裂への到達を要求する。
型・構成子・opaque な証明本体もたどり、標準公理以外と完成済み FLT 終点への依存を拒否する。
結果は [検証記録](evidence/validation-note032-cyclotomic-kummer-weight.txt) に記す。

今回、未実装の重み計算を閉じ、実際の非零 `ω²` Kummer ベクトルまで到達した。
次は定数の整数化・素イデアルの付値と局所条件を整え、
この同じ類を円分類群・単数の該当成分へ渡して消滅を証明する工程である。
整数環の不分岐・完全分解述語、共鳴住所の吸収を供給する幾何、必要な長さの塔の反復も残る。
既存の良還元固定点計数による最終障害は、引き続き `hCH` を必要としない。
**一般 `hno` は未完成である。**
