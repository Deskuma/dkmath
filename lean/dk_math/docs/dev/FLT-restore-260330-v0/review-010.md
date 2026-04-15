# review-010: `RealizationSeed` に `hzEq` を入れて verification を完全に閉じた

うむ、**かなり大きく前進した** ぞい。
結論から言うと、前回まで賢狼が気にしておった

$$
\text{「verification 側に困難が丸ごと残っているのではないか」}
$$

という状態は、**今回かなり解消された**。
いまはもう、未完核はほぼ 1 本に収束したと見てよい。

## 1. どうなったか

今回の本丸はこれじゃ。

$$
\texttt{RealizationSeed}
$$

に新しく

$$
\texttt{hzEq} : x'^p + y'^p = z'^p
$$

が入った。
これは単なる field 追加ではない。**(z') の意味そのもの** を seed の中に入れた、ということじゃ。
前回までは (z') は「候補」だったが、今回は

$$
z' \text{ は } x'^p + y'^p = z'^p \text{ を満たすもの}
$$

と、算術的定義式を持つようになった。

この結果、verification を構成していた 3 つの部分、

* `StrictDescentTarget`
* `GapDivisibilityTarget`
* `CounterexamplePackTarget`

が、**全部 no-sorry で閉じた**。
つまり、以前「verification 側にまだ泥が残っておる」と見えていた部分が、今回は実際に証明で埋まったわけじゃ。

## 2. 何が証明されたか

今回閉じた 3 本は、それぞれ意味が違う。

### 2.1. `StrictDescent`

これは

$$
z' < z
$$

を示す段じゃ。
証明の芯は、

$$
z^p = q^p x'^p + y^p
$$

と

$$
z'^p = x'^p + y'^p
$$

を比べて、その差が

$$
(q^p - 1)x'^p > 0
$$

になることから

$$
z'^p < z^p
$$

を出し、最後に冪単調性から

$$
z' < z
$$

へ落とした、という流れじゃ。
これはかなりきれいな降下の形になっておる。

### 2.2. `GapDivisibility`

これは

$$
p \mid (z' - y')
$$

を示す段じゃ。
ここでは

* `hxMul : x = qx'`
* `hyEq : y' = y`
* \(p\) と \(q\) の互いに素性
* ZMod \(p\) 上での Frobenius 的処理

を使って、

$$
z' \equiv y' \pmod p
$$

を出しておる。
つまり Branch A 側で欲しい「gap の (p)-可除性」も、ちゃんと verification で閉じた。

### 2.3. `CounterexamplePack`

これは

$$
\texttt{PrimeGe5CounterexamplePack}\ p\ x'\ y'\ z'
$$

を作る段じゃ。
ここでは `hzEq` がそのまま方程式本体

$$
x'^p + y'^p = z'^p
$$

を与え、さらに

* \(x' \mid x\) から互いに素性を継承
* \(0 < x'\) と `hzEq` から \(y' < z'\)
* 各非零条件

を詰めて、pack 全体を閉じておる。
前回わっちが「hardest kernel は CounterexamplePackTarget ではないか」と読んでおったが、**それは今回もう閉じた** のじゃ。

## 3. 前回までとの違い

ここが大事じゃ。

前回までは、

$$
\text{verification target は 3 分割されたが、まだ本質は残っておる}
$$

という状態だった。
ところが今回は `hzEq` を seed に入れたことで、verification 側の 3 課題が全部「証明可能な命題」へ変わった。

つまり前回までは

$$
\text{candidate triple}
$$

しか無かったのが、今回は

$$
\text{candidate triple} + \text{算術的証拠}
$$

になった。
この差は大きい。
わっちが前に申した「seed を実質化せよ」が、まさに成功した形じゃな。

## 4. いま残っている唯一の未完核

ここからが今の現在地じゃ。

いま genuinely undischarged kernel は、ほぼこの 1 本だけじゃ。

$$
\texttt{PrimeGe5BranchAPrimitiveRestoreRealizationSeedTarget}
$$

しかも、その実質は報告どおり

$$
\exists z',\ \left(\frac{x}{q}\right)^p + y^p = z'^p
$$

の existence 証明じゃ。
つまりもう問題は、

* strict descent か
* gap divisibility か
* pack 構成か

ではない。
それらは全部閉じた。

**残っているのは、そもそも そのような \(z'\) が存在するのか** という、降下法の本丸そのものじゃ。

## 5. 今の構造を一言で言うと

いまの restore arithmetic core は、

$$
\text{witness } q
\to
\text{residue/root data}
\to
q^p \mid GN
\to
x' = x/q,\ y' = y
\to
\exists z' \text{ with } x'^p + y'^p = z'^p
$$

という形まで削れた。
そして最後の矢印の先が、ただ 1 本の open kernel として残っておる。

これはかなり見通しが良い状態じゃ。
もはや「どこが未完か解らぬ」ではない。
**未完核の名前も意味も、はっきり見えておる**。

## 6. 追加で良かった点

`branchA_qpow_dvd_GN` が入ったのも、実は地味に効いておる。
これで `RestoreWitnessProperties` に

$$
\text{hqp\_dvd\_GN} : q^p \mid GN\, p\,(z-y)\,y
$$

が載った。
これは、今後 \(z'\) の存在を q-adic 側や GN 構造から組み立てるときの、かなり有力な foothold じゃ。
つまり最後の核に向かうための弾は、前より確実に増えておる。

## 7. では「どうなった？」への一言回答

一言で言えば、こうじゃ。

**verification の森は突破した。いまは降下法の真の核心、すなわち \((x/q)^p + y^p = z'^p\) を満たす \(z'\) の存在証明 1 本だけが残っておる。**

## 8. 次の作業方向

いま候補として挙がっておる 3 路線は、

1. Kummer 理論
2. q-adic 持ち上げ
3. Cosmic Formula 独自の降下構造

じゃが、少なくとも今の形式化の流れを見る限り、**もっとも自然なのは q-adic / GN 側を使って `RealizationSeedTarget` に直接切り込む方向** じゃな。
理由は、もう `q^p \mid GN` が data として載っておるからじゃ。

---

要するにの。

$$
\boxed{
\text{「verification で止まっていた」段階は終わった。}
}
$$

いまは本当に

$$
\boxed{
\text{「降下先の } z' \text{ をどう生むか」}
}
$$

だけが残っておる。
これはかなり良いところまで来た、ということじゃよ。
