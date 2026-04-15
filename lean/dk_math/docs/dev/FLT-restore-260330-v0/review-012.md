# review-012: GTail Phase C の成果が Branch A の本筋へ橋として繋がった

うむ、今回は **ちゃんと前へ進んでおる**。
しかも進み方がよい。無理に本丸へ突っ込まず、ぬしが言っておった **「橋を繋げて数学を語りやすくする」** 方針が、そのまま実装成果になっておる。

## 1. いま何が起きたか

今回の差分で増えた本質は 3 つじゃ。

まず Phase A。
円分核 ↔ GN ↔ 差分商 の橋が、ついに theorem 名つきで固定された。

* `cyclotomicPrimeCore_eq_GN_of_gap`
* `GN_eq_diffQuot_of_pow`
* `cyclotomicPrimeCore_eq_diffPowQuot`
* `GN_eq_dividedDifference_pow`

これで

$$
\text{cyclotomicPrimeCore}
;\leftrightarrow;
GN
;\leftrightarrow;
\frac{(x+u)^p-u^p}{x}
$$

を Lean の中で同じ対象として呼び分けられるようになった。これはかなり大きい。

次に Phase B。
`BranchAWitnessRouteBundleTarget` と `BranchAContradictionRouteBundleTarget` が入って、witness route と contradiction route の **名寄せ** が始まった。
まだ adapter 群までは全部出来ておらぬが、「どの補題がどの路線のものか」を statement レベルで分け始めたのは良い。

最後に Phase C の延長。
`branchA_spow_congr_head_mod_p2`、`branchA_contradiction_of_mod_p2_conflict`、`branchA_Wieferich_head_conflict_mod_p2` が入って、mod (p^2) 矛盾探索の入口が定理名として揃った。
つまり今後は「何を仮定すると False に落ちるか」を直接差し込める形になったわけじゃ。

## 2. 状況分析

ひとことで言えば、

$$
\text{設計の橋渡しは前進、}
\quad
\text{本丸の contradiction はまだ open}
$$

じゃ。

今回の成果で、前に曖昧だったものがかなりはっきりした。

### 2.1. もう曖昧でない部分

GN を

* 円分核の顔
* 差分商の顔
* finite difference / divided difference の顔

で見られるようになった。
つまり、「同じものを別の言葉で何度も追いかけて迷う」危険は、かなり減った。

### 2.2. まだ open な部分

`ContradictionTarget` そのものは、まだ証明されておらぬ。
今回入った `branchA_contradiction_of_mod_p2_conflict` は、**すでに mod (p^2) で矛盾する仮定が手に入っていれば False に落とす** 補題であって、その「矛盾する仮定」をどこから得るかは、まだ次段の課題じゃ。

つまり今は、

$$
\text{False へ落とす器}
$$

はできたが、

$$
\text{その器に注ぐ concrete な contradiction datum}
$$

はまだ未発見、という段じゃな。

## 3. 何が良かったか

今回ほんに良いのは、**GTail Phase C の成果が、ただの isolated な補題群で終わらず、Branch A の本筋へ橋として繋がった** ことじゃ。

前回の GTail 追加で

$$
GN \equiv p,u^{p-1} \pmod{p^2}
$$

や mod (p^3) の頭項展開が入った。今回それが Branch A 側の `s^p` congruence や Wieferich 条件と、名前つきで接続された。
これで GTail 側の work が、きちんと contradiction 探索へ資産として流れ込み始めた。ここが大きい。

## 4. 今の立ち位置

賢狼の見立てでは、今はこんな地図じゃ。

### 4.1. 既に solid な部分

* 円分核 ↔ GN ↔ 差分商 の橋
* GTail の mod (p^2), mod (p^3) 足場
* Branch A quotient/reduced form
* contradiction route の top-level architecture

### 4.2. まだ弱い部分

* Phase B の route 分離の実体化
* mod (p^3) concrete conflict
* `ContradictionTarget` に実際に刺さる下流 statement の設計

つまり、**橋脚はかなり立ったが、まだ最後のスパンが空いておる** 状態じゃ。

## 5. 次に何をすべきか

History の「次の課題」は、わっちもほぼ賛成じゃ。順番をつけるならこうじゃ。

### 5.1. 最優先

Phase B の実体化。
つまり `BranchAWitnessRouteBundleTarget` と `BranchAContradictionRouteBundleTarget` を受ける adapter 群を足して、既存 refuter / restore / packet descent のどこへ繋がるかを API として固定する。
いま名寄せだけで止まっておるので、ここを進めると architecture が一段見やすくなる。

### 5.2. 次点

`branchA_spow_congr_head_mod_p3` 相当の API 化と、mod (p^3) concrete conflict の実装。
今の mod (p^2) では「一致する」ことまでは言えても、矛盾を生む差までは出ておらぬ。
高次へ進めて初めて、Wieferich 条件との微妙なズレが露出する可能性がある。

### 5.3. その後

`branchA_contradiction_of_mod_p2_conflict` に実際に入る「矛盾側前提」を、どの statement から要求するかを設計する。
ここで初めて、`ContradictionTarget` の入口が concrete になる。

## 6. 総括

ひとことでまとめると、こうじゃ。

**今回は本丸を落としたのではない。だが、橋の整備という意味ではかなり正しい前進で、特に「円分核 ↔ GN ↔ 差分商」の橋と、mod (p^2) conflict を `False` に落とす器が揃ったのは大きい。次は Phase B の実体化と mod (p^3) concrete conflict が本命じゃ。**

よい流れじゃよ。
いまは「思いつきを補題名にする段」を越えて、**補題群が互いに繋がり始めた段** じゃ。ここからは、橋の先にある矛盾を一つずつ露出させる番じゃな。
