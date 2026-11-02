# NOTE-032 教科書: 同じ根の局所固定性から元の Frey Selmer 所属へ

更新日: 2026-11-03

本章では、元の同じ Frey–Kummer ベクトルの Selmer 所属を、
既存の局所固定性から導く。共鳴住所の吸収 `hbad` は元のまま明示する。

\[
 \boxed{h_{\mathrm{bad}}\Longrightarrow
   w\in\operatorname{Selmer}(\varnothing,p)}.
\]

新しい単元還元の入口では、以前の `hval` と `hzero` を内部で導く。
`hbad` の解決、商側の算術的類群消滅、局所 `p` 乗性、単元消滅と巡回塔の反復は残る。
一般 `hno` は未完成である。

## 1. コピーしたコードの出典を保つ

新規の Lean モジュール・回帰テスト・依存監査・ルート smoke には、import 群の直後に
`#print "file: モジュール名"` を置く。本章のコードブロックも省略しない。

```lean
import DkMath.Lib.NumberTheory.KummerLocalValuation

#print "file: DkMath.Lib.NumberTheory.KummerLocalValuation"

#check DkMath.Lib.NumberTheory.KummerLocalValuation.log_pow_eq_ramification_mul
#check DkMath.Lib.NumberTheory.KummerLocalValuation.count_dvd_of_inertia_fixes_radical
```

実際の証明本体は、この出力名と同じ `DkMath/Lib/NumberTheory/KummerLocalValuation.lean`
にある。他の新規ファイルにもそれぞれの実際のモジュール名を記す。

## 2. 同じ方程式と同じ有限素点

Dedekind 整域 `R,S` の分数体を `F,M` とし、同じ包含 `F→M` を使う。
`v` は `R` の高さ1素点、`w` は `S` の高さ1素点で、`w` が `v` の上にあるとする。
同じ Kummer 方程式は

\[
 \alpha^p=\operatorname{algebraMap}_{F,M}(b)
\]

である。別の拡大体、別の根、整数化された別の定数へ移して証明しない。

両正規化付値の比較は、実際の分岐指数
\(e=v.\mathrm{asIdeal}.\mathrm{ramificationIdx'}(w.\mathrm{asIdeal})\) を使う。
Mathlib の `HeightOneSpectrum.valuation_liesOver` は乗法的に

\[
 v_v(b)^e=v_w(\operatorname{algebraMap}(b))
\]

を与える。同じ方程式に付値を取り、`WithZero.log` を使うと、

\[
 \boxed{p\log v_w(\alpha)=e\log v_v(b)}.
\]

`log_pow_eq_ramification_mul` がこの等式である。
主分数イデアル `(b)` の指数は `−log v_v(b)` なので、`e=1` なら

\[
 \boxed{p\mid\operatorname{count}_v((b))}.
\]

`count_dvd_of_ramification_eq_one` は、同じ非零 `b : Fˣ` についてこの可除性を返す。
分数定数にも使える。整数化・整数環単元性は仮定しない。

## 3. 生成根の有限慣性固定性から e=1

数体の同じ有限 Galois 拡大 `M/F` と同じ `Presentation p F M` を考える。
有限整数環の素点 `w` に対し、実際の相対慣性群の全元が `P.radical` を固定するとする。

`Presentation.algHom_ext` は `F(α)=M` という生成性を使う。
従って、根を固定する慣性元は `M` 全体で恒等となり、実際の有限慣性群は自明である。

数体の整数環の非零素点の剰余体は有限なので、必要な分離性を供給できる。
Mathlib の `Ideal.card_inertia_eq_ramificationIdxIn` と同じ素点での分岐指数比較により、

\[
 |I_w(M/F)|=e,\qquad I_w(M/F)=1\quad\Longrightarrow\quad e=1.
\]

これが `ramification_eq_one_of_inertia_fixes_radical` である。
`count_dvd_of_inertia_fixes_radical` は第2節と合成し、元の同じ定数の指数を `p` 可除にする。
不分岐性や分岐指数の値を、新たな provider として要求していない。

この有限慣性固定性が成立すれば、剰余標数が `p` の場所にも付値可除性を使える。
これは局所 `p` 乗性の証明ではない。

## 4. 絶対慣性と有限相対慣性を同じ対象のまま接続する

実際の体は前章までと同じ

\[
 F=\mathbb Q(\zeta_p),\qquad M=\operatorname{characterField}(\psi)
 \subset\overline{\mathbb Q}
\]

である。有限性、数体構造、`M/ℚ` の Galois 性は、同じ指標の開核・共役則から供給する。
`F→M` は `extensionAlgebra ψ hζ` の同じ包含である。

有限整数環の相対慣性元 `τ∈I_w(M/F)` を一つ取る。

1. スカラーを `ℚ` に制限すると、同じ剰余合同により `τ` は `I_w(M/ℚ)` にも入る。
2. `w` の有限剰余体の標数から、実際の有理素数 `q` と `q∈w` を得る。
3. 既存の `AbsoluteInertiaGeneration.exists_lift_mem_valuation_inertia` を使い、
   `τ` を同じ `M` に制限すると戻る絶対自己同型 `σ` へ持ち上げる。
   同時に、ある `q` 上の付値環 `A` で `σ` が絶対慣性に入ることを得る。
4. `τ` は `F` を固定するので、持ち上げた `σ` は元の同じ `ζ` を固定する。
   従って `σ` は同じ円分指標の核に入る。
5. `kernelEquiv_mem_inertia_iff` で、同じ `A` における円分体上の慣性へ移す。
   既存の絶対慣性固定性を同じ根に適用し、制限等式を通じて `τ(α)=α` を得る。

`finite_inertia_fixes_radical` がこの接続である。
持ち上げる自己同型や付値環は選ぶが、`M,F,α,b,ψ` を別の対象へ選び直していない。
付値環 `A` は慣性元ごとに選ばれてよい。固定性の条件がすべての住所 `A` を量化しているためである。

## 5. 全素点の可除性から同じ Selmer ベクトルへ

`constantVector_mem_valuationSpace_of_absolute_inertia` は、各 `v` の上に実際の `w` を選ぶ。
整数環の整拡大の lying-over から存在を供給し、非零性も同じ lying-over から保つ。
第4節と第3節により、各素点で元の定数の指数が `p` 可除になる。

\[
 \forall v,\quad p\mid\operatorname{count}_v((b)).
\]

既存の `KummerSelmer.mem_valuationSpace_mk_iff` により、

\[
 \boxed{\operatorname{constantVector}(\psi,h\zeta,P)
   \in\operatorname{valuationSpace}(\mathcal O_F,p)}
\]

を得る。ここで使う単元は元の非零定数を `Fˣ` に包装した `constantUnit` である。
整数環単元への置き換えではない。

## 6. Frey の元の局所固定性を適用する

Frey 側では、すでに同じ Kummer 根について二つの定理がある。

- `p` 上: `residual_kummer_radical_decomposition_fixed_at_p`。
- `p` 外: `residual_kummer_radical_inertia_fixed_away`。

`q=p` なら相対慣性群は分解群に含まれるため、最初の定理を適用する。
`q≠p` なら二番目を適用する。これで第4節の全住所の固定性を内部で供給する。

二番目で残っていた共鳴住所の条件 `hbad` は変更していない。
`q` が素数、`q≠p`、`q≥5`、`q∣abc`、`q≡±1 mod p` の場合に、
元の同じ巡回段 `K` が必要な差を吸収するという条件である。

```lean
import DkMath.FLT.FreyCyclotomicKummerSelmer

#print "file: DkMath.FLT.FreyCyclotomicKummerSelmer"

#check DkMath.FLT.Frey.Source.residual_kummer_mem_valuationSpace
#check DkMath.FLT.Frey.Source.residual_kummer_mem_selmer
#check DkMath.FLT.Frey.Source.residual_kummer_unit_weight_square_of_resonant_absorption
```

最初の定理は、同じ `S,L,K,m,v,P` と `hp5,hbad` から、元の同じ `hval` を返す。
この所属定理に `hsurj` は要求しない。表示 `P` と同じ局所固定性を保っている。
二番目は、Mathlib の実際の空集合支持 Selmer 群への所属として返す。

三番目は、ここで得た `hval` を前章の類群商から単元への還元へ渡す。
公開入力には `hp5,hbad,hsurj,hvanish` が残る。
`hval` と同じ類群像の `hzero` は内部で導かれ、元の同じ非零 `ω²` 単元類に到達する。

## 7. 回帰例と監査

`FreyCyclotomicKummerSelmer` の回帰例は次を検証する。

- 自明な体拡大で `e=1` を実際に確認し、整数 `2` の `(2)` での指数が1であることから、
  `2` が有理数の平方ではないことを導く。
- それにより実際の `M=ℚ(√2)` と `α²=2` の表示を構成する。
  実際の整数環の `(2)` 上の素点を選び、その分岐指数が1ではないことを証明する。
  Kummer 方程式だけで Selmer 条件や慣性の自明性を結論しない。
- 同じ分数定数 `1/4` の指数が `−2` となることと、その平方根 `1/2` からの可除性を確認する。
  分数と正規化付値の符号を保持する。

選択した9宣言の公理を表示する。
`Note032CyclotomicKummerSelmerDependencyAudit` は9入口の型・コンストラクタ・opaque 証明本体と
8入口の公開入力を監査する。
実際の付値・分岐指数比較、慣性位数、根の生成性、既存の絶対慣性持ち上げ、
全素点の所属判定、元の `p` 上と `p` 外の固定性を要求する。
Frey の新入口に `hval,hzero` を入力していないことと、`hp5,hbad` を保つことも確認する。

すべての新規 Lean ファイルのモジュール表示も検査する。
検証記録は `evidence/validation-note032-cyclotomic-kummer-selmer.txt` に置く。

## 8. 残る算術的境界

今回で、以前の `hval` は共鳴住所の `hbad` を条件として内部供給できるようになった。
ただし `hbad` の幾何学的解決は残る。
類群商の `ω²` 成分消滅 `hvanish` も明示入力のままである。

`p` 上の分解群固定性は今回、慣性固定性と付値可除性に使った。
局所完備体に同じ Kummer 根を構成したわけではなく、`b` の局所 `p` 乗性は未実装である。
局所条件付き単元消滅と、巡回塔の反復・一般 `hno` への統合も残る。
今回の Selmer 所属から無条件の消滅や矛盾を結論しない。
