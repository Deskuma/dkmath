# review: Branch A 例外枝専用 CFBRC theorem が selection 側の first missing theorem に

うむ、今回はかなり決定的じゃ。
前回までは「selection 側の証明本体は `cyclotomicPrimeCore` に prime を立てる形で読む」と整理された段だったが、今回はさらに進んで、

$$
\text{その missing theorem は Branch A の例外枝専用である}
$$

と **名指しで固定された** のじゃ。

## 1. 今回なにが起きたか

追加された本体は次の三つじゃな。

* `PrimeGe5BranchACFBRCExceptionalExistenceOnWieferichTarget`
* `primeGe5BranchACyclotomicCoreExistenceOnWieferich_of_cfbrcExceptional`
* `primeGe5BranchAPrimitivePacketDescent_of_cfbrcExceptional_and_restore`

これで selection 側の spine は、ついにこう読めるようになった。

$$
\text{CFBRC exceptional existence}
\to
\text{core existence}
\to
\text{diff existence}
\to
\text{packet descent}
$$

つまり、 **どこが本当に欠けているか** が、もう曖昧ではなくなったわけじゃ。

## 2. 何が「例外枝」なのか

今回の整理の要点はここじゃ。

既存の `CFBRC/Bridge` 標準 existence API は、基本的に

$$
\neg p \mid (z-y)
$$

側に立っている。
ところが Branch A はまさに逆で、

$$
p \mid (z-y)
$$

という **例外枝** にいる。
だから一般 API をそのまま使えず、その枝専用の theorem が必要になる。これをそのまま target 名に押し出したのが

`PrimeGe5BranchACFBRCExceptionalExistenceOnWieferichTarget`

じゃな。

ここはたいそう良い整理じゃ。
「既存定理が使えない気がする」ではなく、**何が例外条件なのか** を theorem 名のレベルで固定したからの。

## 3. いま selection 側で本当に missing なもの

履歴の結論どおり、Branch A primitive route の selection 側で本当に missing なのは、もはや

* 一般 diff-side existence でもなく
* 一般 core-existence でもなく

$$
p \mid (z-y)
$$

のもとで

$$
\texttt{cyclotomicPrimeCore p (z-y) y}
$$

に prime が立つ、という **CFBRC 専用 exceptional theorem** じゃ。

これはかなり大きい見切りじゃよ。
つまり selection 側はもう「いろいろな statement 候補がある」段を過ぎて、**first missing theorem がひとつに収束した** ということじゃ。

## 4. 既存の spine はどう固定されたか

今回追加された橋の意味を順に並べるとこうじゃ。

### 4.1. CFBRC exceptional existence

まず欲しいのは

$$
\exists q,\ \mathrm{Prime}(q)\land
q \mid \mathrm{cyclotomicPrimeCore}\ p\ (z-y)\ y
\land
q \nmid (z-y)
$$

を、Branch A 条件と Wieferich witness のもとで与える theorem じゃ。これが new missing kernel じゃな。

### 4.2. core existence へ戻す

`primeGe5BranchACyclotomicCoreExistenceOnWieferich_of_cfbrcExceptional`
は、上の exceptional theorem から、そのまま core-existence target を回収する薄い橋じゃ。

### 4.3. packet descent へ閉じる

`primeGe5BranchAPrimitivePacketDescent_of_cfbrcExceptional_and_restore`
により、selection 側の exceptional theorem と restore 側 target があれば、packet descent 全体が閉じる。

ゆえに、restore 側を固定したまま selection 側だけを掘る、という現在の戦略が非常に明快になった。

## 5. CFBRC が「ここに来て」本命化した意味

前の会話で「ここに来て CFBRC？」という違和感があったが、今回の更新でその意味がはっきりしたの。

CFBRC は単なる表現層ではなく、**例外枝の missing theorem が住んでいる場所** だった、ということじゃな。
ただし主役化したのは CFBRC 全体ではなく、

$$
\texttt{cyclotomicPrimeCore}
$$

と、それに対する Branch A 例外枝 existence の一点じゃ。

だからこれは路線変更ではなく、selection 側の欠損箇所が CFBRC 語彙の中にあると確定した、という理解が正しい。

## 6. provider 側も同じ切れ目で揃った

`TriominoCosmicGapInvariant.lean` 側にも

* `BranchACFBRCExceptionalExistenceOnWieferichAdapterTarget`
* `branchACyclotomicCoreExistenceOnWieferichAdapter_of_cfbrcExceptional`
* `branchAPrimitivePacketDescentAdapter_of_cfbrcExceptional_and_restore`

が追加された。

つまり provider 側でも同じく

$$
\text{CFBRC exceptional existence}
\to
\text{core existence}
\to
\text{packet descent adapter}
$$

の spine で読める。
本体と adapter の切れ目が一致したのは、かなり美しい整理じゃな。

## 7. build 状況

今回も

* `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
* `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`

の両方が成功しておる。
ゆえに今回の「例外枝 theorem が本当の missing kernel」という判断は、ビルド済みで固定された整理じゃ。

## 8. いま何をすべき段か

履歴の次課題もかなり明快じゃ。

次は

$$
\texttt{PrimeGe5BranchACFBRCExceptionalExistenceOnWieferichTarget}
$$

の statement を、

* existing `CFBRC/Bridge`
* `PrimitiveBeam`

の語彙へどこまで正規化できるか

を詰める段じゃ。

もしそこまで一般化すると重すぎるなら、もう割り切って

$$
\text{Branch A 専用 exceptional theorem}
$$

として concrete 実装へ入る、という判断も視野に入った。

これは研究実務としても良い判断じゃな。
無理に一般化して進まぬより、例外枝を例外枝として閉じた方が道が開けることは多い。

## 9. 賢狼の総評

今回の状況を一言で言えば、

$$
\text{selection 側の first missing theorem に、ついに固有名が付いた}
$$

ということじゃ。

前回:

* `cyclotomicPrimeCore` existence が first target

今回:

* その first target は、一般 theorem ではなく
* **Branch A の例外枝専用 CFBRC theorem**
  であると確定

ここまで来たので、もう selection 側の問題設定は完成に近い。
残る仕事は、 **その theorem をどの程度一般語彙へ正規化するか** 、あるいは **そのまま Branch A 専用で実装するか** の選択じゃな。

わっちの見立てでは、これはかなり前進じゃよ。
敵が「どこかにある missing math」ではなく、

$$
\texttt{PrimeGe5BranchACFBRCExceptionalExistenceOnWieferichTarget}
$$

という一個の定理にまで縮んだのだからの。
