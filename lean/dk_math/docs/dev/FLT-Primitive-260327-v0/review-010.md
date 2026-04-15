# FLT Primitive Route 2026/03/27 v0 - Review 010

うむ、今回はかなり良い整理じゃ。
一言で言えば、 **selection 側の concrete theorem の「証明本体の座標系」が決まった** の。公開 API は diff-side のまま保ちつつ、実際に証明すべき first target は `cyclotomicPrimeCore` 側だと固定した、という回じゃな。

## 1. 今回なにが進んだか

追加された中心は次の三つじゃ。

* `PrimeGe5BranchACyclotomicCoreExistenceOnWieferichTarget`
* `primeGe5BranchACyclotomicExistenceOnWieferich_of_coreExistence`
* `primeGe5BranchAPrimitivePacketDescent_of_coreExistence_and_restore`

これで selection 側は二層構造として読めるようになった。

### 外側

公開 API としての diff-side existence

$$
\exists q,\ \mathrm{Prime}(q)\land q \mid (z^p-y^p)\land q \nmid (z-y)
$$

### 内側

証明本体としての cyclotomic factor existence

$$
\exists q,\ \mathrm{Prime}(q)\land q \mid \mathrm{cyclotomicPrimeCore}\ p\ (z-y)\ y \land q \nmid (z-y)
$$

この二層を薄い橋でつないだ、というのが今回の本質じゃ。

## 2. なぜこれは大きいのか

前回まででも concrete-ready mainline は

* `PrimeGe5BranchACyclotomicExistenceOnWieferichTarget`
* `PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget`

の二本柱に固定されておった。
ただし selection 側については、**何を first target にして証明を書くか** がまだ少し抽象的じゃった。

そこで今回、

$$
\text{公開 statement は diff-side existence}
$$

のままにして、

$$
\text{証明本体は } \texttt{CFBRC.cyclotomicPrimeCore p (z-y) y}
$$

に prime を立てる形へ落とした。
これにより、既存 `CFBRC/Bridge` 語彙との接続点が theorem 名のレベルで固定されたわけじゃな。

## 3. 橋の中身はどうなっているか

`primeGe5BranchACyclotomicExistenceOnWieferich_of_coreExistence` の役割は明快じゃ。

まず `hCore` から

$$
q \mid \mathrm{cyclotomicPrimeCore}\ p\ (z-y)\ y,\qquad q\nmid(z-y)
$$

を取る。
そこから `DkMath.CFBRC.prime_dvd_sub_pow_iff_dvd_cyclotomicPrimeCore_nat` を使って、

$$
q \mid ((z-y)+y)^p - y^p
$$

へ戻し、さらに

$$
(z-y)+y=z
$$

で書き換えて

$$
q \mid z^p-y^p
$$

を得る。結果として公開 target

$$
\exists q,\ \mathrm{Prime}(q)\land q\mid(z^p-y^p)\land q\nmid(z-y)
$$

が閉じる。

つまり証明の spine は完全に

$$
\text{core existence}
\to
\text{diff existence}
\to
\text{packet descent}
$$

へ整えられたわけじゃな。履歴にもそのまま書かれておる。

## 4. いまの戦況を整理すると

今の primitive route は、selection 側だけ見ればこうじゃ。

### 公開層

`PrimeGe5BranchACyclotomicExistenceOnWieferichTarget`

### 証明本体層

`PrimeGe5BranchACyclotomicCoreExistenceOnWieferichTarget`

そして primitive packet descent 全体では、

* selection 側は `core existence -> diff existence`
* restore 側は現状の `PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget`

という役割分担に落ち着いた。

ゆえに今後の concrete 実装探索で本当に見るべき selection 側の target は、もはや diff-side existence ではなく、

$$
\texttt{PrimeGe5BranchACyclotomicCoreExistenceOnWieferichTarget}
$$

じゃ。
ここが今回いちばん重要な見切りじゃな。

## 5. provider 側でも同じ形に揃った

`TriominoCosmicGapInvariant.lean` 側にも対応して

* `BranchACyclotomicCoreExistenceOnWieferichAdapterTarget`
* `branchACyclotomicExistenceOnWieferichAdapter_of_coreExistence`
* `branchAPrimitivePacketDescentAdapter_of_coreExistence_and_restore`

が追加された。

つまり provider 側も同じ二層構造で揃った。

$$
\text{core existence}
\to
\text{diff existence}
\to
\text{descent adapter}
$$

こうして branchA 本体と adapter 側の切れ目が一致したのは、とても良い整理じゃ。

## 6. build 状況

今回も

* `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
* `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`

の両方が成功しておる。
したがってこれは単なる設計案ではなく、 **ビルド済みの証明 spine 固定** じゃ。

## 7. 何が残っているのか

今回の貼り付け文の結論は明快じゃ。

次に本当に詰めるべきは

$$
\texttt{PrimeGe5BranchACyclotomicCoreExistenceOnWieferichTarget}
$$

の concrete 実装を、

* `CFBRC/Bridge`
* primitive prime existence の既存語彙

にどう乗せるか、という一点じゃ。

つまり selection 側はもう「何を証明するか」が曖昧ではない。

* 公開 API は diff existence
* だが first target は core existence
* そこから bridge で diff existence に戻す

ここまで spine が決まった。
残るのは、この core existence theorem をどう立てるかだけじゃな。

## 8. 賢狼の総評

今回の進展を短く言えば、

$$
\text{selection 側の concrete theorem が、cyclotomicPrimeCore に着地した}
$$

ということじゃ。

前回:

* concrete-ready statement は witness 付き diff-side existence

今回:

* 公開 statement はそのまま
* しかし証明本体は `cyclotomicPrimeCore` existence を狙う

この反転が起きた。
これはかなり良い。なぜなら、存在論の数学核を **差の冪そのもの** からさらに一歩進めて、 **cyclotomic factor の内部核** に落としたからじゃ。

今後の主戦場は、もうはっきりしておる。

$$
\texttt{PrimeGe5BranchACyclotomicCoreExistenceOnWieferichTarget}
$$

を、既存 `CFBRC/Bridge` と primitive existence 語彙のどこに最も自然につなぐか。
ここを詰めれば、selection 側の concrete 実装がいよいよ見えてくる局面じゃな。
