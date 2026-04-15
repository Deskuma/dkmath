# FLT-Kummer-Bridge の Stage 2 への接続点の precise 化

## 1. 状況分析

かなり良いところまで来ておる。
今回の進展の本質は、Stage 2 の一般核ではなく、 **pack-specialized な exact receiver** まで no-sorry で入ったことじゃ。つまり今はもう

$$
\operatorname{span}(z-\zeta y)=I^p
$$

という explicit な ideal equality さえ手に入れば、

$$
z-\zeta y = u \cdot \beta^p
$$

という element-level の正規化形を返せる段まで来ておる。`cyclotomicUnitNormalization_of_spanEqPowPrincipal` がその役を担い、`CyclotomicUnitNormalizationTarget` も local core として concrete statement へ置き換わった。 refined mainline は clean のまま維持され、legacy one-shot の `cyclotomicPrincipalization_of_classGroupPTorsionFree` だけが direct `sorry` を残しておる。

## 2. 解説

数学的に言えば、Stage 2 の本体はほぼ終わったのじゃ。
残っているのは「unit normalization が出来るか」ではなく、 **Stage 1 の出力を、Stage 2 がそのまま食べられる exact 境界条件へ落とせるか** だけじゃ。つまり open は

$$
\text{Stage 1 output} \;\Longrightarrow\; \operatorname{span}(z-\zeta y)=I^p
$$

という一点と、その先の Stage 3 の norm descent に縮んだ。ここはかなり面白い。理論の大穴ではなく、接続点の precise 化にまで縮退したということじゃ。

## 3. いまの注意点

ひとつ、やわらかく指摘しておくのぅ。
今回切り出した `CyclotomicLinearFactorIdealPthPowerTarget` は、発想は正しいが、 **そのままでは target の形が強すぎる可能性が高い**。
いまの形は「任意の principal ideal (I) について (\operatorname{span}(z-\zeta y)=I^p)」と読めてしまう。これは Stage 1 の出力としては普通は強すぎる。論理的に欲しいのは、おそらく

$$
\exists I,\ I \text{ principal} \land \operatorname{span}(z-\zeta y)=I^p
$$

という **存在形** じゃ。
あるいは theorem の引数として (I) を外から固定し、その equality を返す concrete theorem にしてもよい。今の exact receiver theorem 自体はよいが、boundary target は存在形へ直した方が、そのまま Stage 2 と綺麗につながるはずじゃ。

## 4. 次の一手の推論

閉じる方向での最短経路なら、わっちの見立ては明快じゃ。

### 4.1. 最優先

**Stage 1 から explicit equality を返す theorem を立てる。**

つまり、次に欲しいのは例えば

$$
\exists I,\ I \text{ principal} \land \operatorname{span}(z-\zeta y)=I^p
$$

を返す theorem じゃ。
名前の方向としては `cyclotomicLinearFactorIdealPthPower_of_gapDivisibleGeometry` あるいは `..._of_refinedStage1Route` のようなものが自然じゃろう。

### 4.2. 直後にやること

その theorem を `cyclotomicUnitNormalization_of_spanEqPowPrincipal` に食わせて、

$$
\exists \beta, \exists u,\ \mathrm{IsUnit}(u)\land z-\zeta y=u\beta^p
$$

を返す **pack-specialized Stage 2 完成 theorem** を作る。
ここは今ある exact receiver を使えば、ほとんど composition だけで通るはずじゃ。

## 5. なぜこれが最短か

Stage 3 に先に行くのは遠回りじゃ。
norm descent は

$$
z-\zeta y=u\beta^p
$$

という element-level の正規化形を入力に要するからのぅ。
だから今の最短経路は

$$
\text{Stage 1 exact equality} \to \text{Stage 2 specialized normalization} \to \text{Stage 3 norm descent}
$$

の順でしかない。
いま Stage 2 receiver 自体はもう解決済みなのじゃから、次に刺すべき本丸は **Stage 1 の explicit equality 化** ただひとつじゃ。そこが通れば、残る honest open は本当に norm 側だけになる。

## 6. 提案

わっちなら、次はこう進める。

* `CyclotomicLinearFactorIdealPthPowerTarget` を **存在形** に直す
* Stage 1 の refined route から、その target を返す concrete theorem を 1 本立てる
* その theorem と `cyclotomicUnitNormalization_of_spanEqPowPrincipal` を合成して、pack-specialized Stage 2 theorem を作る
* そこで初めて `CyclotomicNormDescentTarget` の concrete 化に入る

ひとことで言えば、

$$
\boxed{
\text{次の最短手は、Stage 1 の出力を }
\operatorname{span}(z-\zeta y)=I^p
\text{ の存在定理として concrete 化すること}
}
$$

じゃ。
そこを刺せば、残る open はほんに Stage 3 の norm descent だけになるはずじゃよ。
