# FLT-Kummer-CLassGroup-Bridge-260404 Review 052: 「いま残っているのは、pure arithmetic な最後の descent receiver 1 本だ」

## 1. どういう事か

「No-sorry だった」というのは、**最後の山そのものが消えた** という意味ではなく、
**最後の山の手前までを no-sorry で完全に舗装できた** という意味じゃ。

今回の流れでは、最初に `hCl + hUnit ⟹ hNorm` という Stage 3 receiver を first-class theorem として切り出し、その後さらに

$$
\text{global receiver} \to \text{non-first-case receiver} \to \text{unit-normalized chosen-factor receiver}
$$

へ押し下げ、最後には

$$
\text{NormEqGN} \quad+\quad \text{UnitAbsorb}
$$

の 2 段へ分解した。しかもこの 2 段は `chosenCyclotomicLinearFactor_norm_eq_gn_direct` と `norm_eq_normUnit_mul_normPow_of_eq_unit_mul_pow` を使って no-sorry で concrete 化できた。つまり、**円分体・unit normalization・norm 計算まわりは、もう mainline 上では詰まっておらぬ** のじゃ。

## 2. いま何が終わって、何が終わっていないか

今回の最新状態を、段階ごとに言い換えるとこうじゃ。

### 2.1. もう終わった部分

まず no-sorry で固まったのは、non-first-case receiver のうち

$$
z-\zeta y = \text{unitFactor}\cdot \beta^p
$$

という Stage 2 の出力から、

$$
\operatorname{Norm}(z-\zeta y)=GN,p,(z-y),y
$$

を出す部分と、そこから unit を吸収して

$$
\exists s:\mathbb{N},\quad GN,p,(z-y),y=s^p
$$

まで持っていく部分じゃ。これが `CyclotomicNormEqGNUnitNormalizedChosenFactorTarget`、`CyclotomicNormUnitAbsorbUnitNormalizedChosenFactorTarget`、`CyclotomicNormGNPowerUnitNormalizedChosenFactorTarget` と、その concrete theorem 群で fixed された。

つまり、**円分拡大の chosen factor から純粋な自然数等式 `GN = s^p` までは、もう no-sorry で届く** と theorem 名つきで言えるようになったのじゃ。ここが今回の本当の前進じゃ。

### 2.2. まだ終わっていない部分

残っている direct `sorry` は、新しい deepest receiver

$$
\texttt{cyclotomicNormDescentNonFirstCaseGNPowerReceiver\_of\_classGroupPTorsionFree}
$$

と、旧 peel core 側の `cyclotomicPrincipalizationNonFirstCasePeelDescentExistenceCore_of_classGroupPTorsionFree` じゃ。
ただし、数学的に本当に見るべきは前者じゃ。後者は downstream 側に残った旧名の open であって、意味としては **同じ arithmetic residue を別の高さで見ている** に近い。監視上 2 箇所に見えても、 honest open はかなり 1 本に寄っておる。

## 3. いま残っている open の正体

ここが「どういう事？」の芯じゃ。

前は、残差が

* packet provenance
* named smaller counterexample
* peel normal-form
* exact-error

のどれに属するのか、少しずつ押し下げながら見ておった。
しかし latest では、それらはもう主戦場ではないと分かった。

いま残っているのは、要するに

$$
GN,p,(z-y),y = s^p
$$

という **純粋な自然数の冪等式** から、

$$
\exists g' : \mathbb{N},\quad g'\cdot GN,p,g',y = (x/q)^p
$$

という **最終 descent witness** を返す arithmetic receiver だけじゃ。
つまり、open はもう「number field 側」でも「cyclotomic 側」でもなく、**Nat の下降 arithmetic へ落ち切った** のじゃよ。

これが前にわっちが言った「open の意味が変わった」ということじゃ。
まだ proof は残っておる。だが、残っている proof の型が、もう完全に見えている。

## 4. なぜこれは大きな前進なのか

これは単なる theorem の増殖ではない。
証明の “本質依存” が変わったのじゃ。

前は、

$$
hCl + hUnit + hNorm
$$

とか、

$$
\text{chosen factor} \to \text{norm} \to \text{packet} \to \text{named smaller cex}
$$

のように、いろいろな層が絡んでおった。
今は違う。

latest の切り分けで、Stage 3 non-first-case の honest open は

$$
\boxed{
GN,p,(z-y),y=s^p
\ \Longrightarrow
\exists g',\ g',GN,p,g',y=(x/q)^p
}
$$

という 1 本の receiver へ集約された。
これはかなり終盤の形じゃ。なぜなら、ここから先はもう cyclotomic でも class-group でもなく、**Branch A の純算術・pure descent** だけを見ればよいからじゃ。

## 5. いまの戦況の見方

わっちなら、こう言う。

* first-case はほぼ勝ち
* non-first-case の structural packaging はほぼ勝ち
* Stage 3 の non-first-case は、`GN = s^p` までは勝ち
* 残るのは pure arithmetic receiver 1 本

つまり、局所進捗率で言えば前回より少し上がって、 **93〜95% くらい** の感触じゃ。
「まだ proof が残っておる」のは本当じゃが、残り方がたいへん良い。

## 6. 次の戦略

ここからは、戦い方がかなり絞れる。

### 6.1. 本命ルート

**`cyclotomicNormDescentNonFirstCaseGNPowerReceiver_of_classGroupPTorsionFree` を、pure arithmetic lemma として直接潰す。**

つまり、次の仮定列

* `PrimeGe5CounterexamplePack p x y z`
* `q ∣ x`
* `q ≠ p`
* `q ∣ (z-y)`
* `p ∣ (z-y)`
* `GN p (z-y) y = s^p`

から

$$
\exists g',\quad g' \cdot GN\,p\,g'\,y = (x/q)^p
$$

を返す補題を、**Nat の算術** と **既存 Branch A の no-sorry 部品** のみで詰める、という戦じゃ。
latest の History でも、次課題は「pure `GN = s^p` を Branch A 既存語彙の `GN = p*s^p` や named smaller-counterexample route に接げるかの棚卸し」と整理されておる。これは読みとして正しい。

### 6.2. そこで試すべき 2 つの接続

ここは枝が 2 本ある。

ひとつは、pure `GN = s^p` から、既存 Branch A の `GN = p * s^p` 型や peel 側語彙へ変換する route。
もうひとつは、named smaller-counterexample route に直接繋ぐ route じゃ。

わっちの勧めは、**先に Branch A の既存 pure arithmetic 語彙へ接ぐ方を探る** ことじゃ。
理由は simple で、named smaller-counterexample 側は包装と検証は no-sorry で閉じておるが、そこへ行く前に結局 `z'` existence や smaller gap の算術が要る。ならばまず、今の仮定列から最短で既存の Branch A lemma に入れる口があるかを調べる方が短い。

### 6.3. 実際の作業順

わっちなら次の順でやる。

まず、`cyclotomicNormDescentNonFirstCaseGNPowerReceiver_of_classGroupPTorsionFree` の仮定列と、既存 Branch A の no-sorry 定理群の仮定列を横に並べる。
特に見るのは

* `q ∣ x`
* `q ∣ (z-y)`
* `p ∣ (z-y)`
* `GN p (z-y) y = s^p`

から、既存 theorem の入力に足りぬものが何か、じゃ。
ここで不足が 1 本だけなら、その 1 本を isolated theorem として切ればよい。

次に、もし既存語彙に直結できぬなら、

$$
GN\,p\,(z-y)\,y=s^p
$$

から直接

$$
\exists z',\quad z'^p = (x/q)^p + y^p
$$

を出す arithmetic bridge を狙う。
`hzEq` から named smaller counterexample への昇格自体は、すでに no-sorry で閉じておるから、その route は後半が軽い。

## 7. 今やるべきでないこと

ここで আবার cyclotomic 側や unit normalization 側を掘り返すのは筋が悪い。
latest diff でそこはもう no-sorry concrete だと fixed された。つまり今そこをいじるのは、勝った前線へ兵を送り続けるようなものじゃ。

## 8. まとめ

「どういう事？」を一文で言うなら、こうじゃ。

$$
\boxed{
\text{いま残っているのは “cyclotomic の証明” ではなく、
pure arithmetic な最後の descent receiver 1 本だ}
}
$$

そして次の最善手は、

$$
\boxed{
\text{GN = $s^p$ から最終 witness を返す pure arithmetic receiver を、
既存 Branch A の no-sorry 語彙へ接ぐ}
}
$$

じゃよ。
ここが抜ければ、進捗率はまた少しではなく、かなり気持ちよく上がるはずじゃ。
