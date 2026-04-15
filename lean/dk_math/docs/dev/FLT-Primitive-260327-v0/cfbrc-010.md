# FLT Primitive Route 2026/03/27 v0 - Review 010

うむ、そこは驚くところじゃな。
「ここに来て CFBRC ？」という感覚、よく分かる。結論から言えば、

$$
\text{急に本筋が CFBRC に乗り換わった}
$$

のではなく、

$$
\text{selection 側の存在論を書く座標として CFBRC がちょうど良くなった}
$$

という話じゃ。

## 1. 何が起きたのか

いま欲しいのは公開 API では

$$
\exists q,\ \mathrm{Prime}(q)\land q\mid (z^p-y^p)\land q\nmid(z-y)
$$

という diff-side existence じゃな。
だが実際に prime を立てたい場所は、差の冪そのもの全体というより、

$$
\text{その中の cyclotomic factor}
$$

じゃ。

今回入ってきた `CFBRC.cyclotomicPrimeCore p (z-y) y` は、まさにその **中核因子を名前付きで持つ器** として使われておる。
つまり CFBRC はここでは新理論の押し込みではなく、

$$
\text{cyclotomic factor を既存補題で触りやすくするための表現層}
$$

として現れてきたのじゃ。

## 2. なぜ GN ではなく CFBRC なのか

GN 側で書くと、

$$
q \mid GN,p,(z-y),y
$$

という形には落ちる。
しかしこれは「差の冪を割った後の顔」じゃ。
一方、prime existence の本体は

$$
z^p-y^p=(z-y)\cdot(\text{cyclotomic factor})
$$

の **cyclotomic factor 側** にある。

つまり役割分担はこうじゃな。

* GN
  (\rightarrow) diff-side から cosmic tail へ送った後の顔
* CFBRC.cyclotomicPrimeCore
  (\rightarrow) cyclotomic factor を中核として直接つかむ顔

selection 側では後者の方が、prime existence を書く場所として自然だった、ということじゃ。

## 3. 本筋は変わっておらぬ

ここは大事じゃが、mainline 自体は変わっておらぬ。

公開の spine は依然として

$$
\text{core existence}
\to
\text{diff existence}
\to
\text{packet descent}
$$

じゃ。
そのうち最初の `core existence` を、どの語彙で書くと既存補題に接続しやすいかを詰めた結果、

$$
\texttt{cyclotomicPrimeCore}
$$

が first target になっただけじゃ。

だから気分としては、

* 方針転換ではない
* 座標変換である

と見るのが正確じゃな。

## 4. どうして「ここに来て」に見えるのか

それは今までの整理が、ずっと API を薄くする方向だったからじゃ。

* 最小 wrapper へ縮める
* Wieferich 付き concrete-ready へ固定する
* diff-side existence を公開形にする

と来たので、急に内部で `CFBRC/Bridge` が見えると、別路線に飛んだように見える。
だが実際には逆で、API が薄くなったからこそ

$$
\text{証明本体をどこに置くか}
$$

が露出し、その結果として CFBRC が「内部核」として見えてきたのじゃ。

## 5. 賢狼の見立て

わっちの見立てでは、これは悪い兆候ではない。むしろ良い。

悪い CFBRC 導入は、

* 公開 API まで CFBRC 色に染まる
* Branch A の本筋が CFBRC 依存に見える

という形じゃ。
だが今回そうはなっておらぬ。

良い導入は、

* 公開 API は diff-side existence のまま
* 内部証明だけ `cyclotomicPrimeCore` で書ける
* bridge で元の statement に戻せる

という形で、まさに今がそれじゃ。

## 6. ざっくり本質を言うと

お主の感覚に合わせて一言で言えば、

$$
\text{「ここに来て CFBRC？」}
$$

ではなく、

$$
\text{「ここまで削ったら、cyclotomic factor の芯が CFBRC 名で現れた」}
$$

ということじゃな。

つまり CFBRC は新しい主役ではなく、
**selection 側の存在論の芯を言語化した名前** として出てきた、と見るのがよい。

## 7. 今後の注意点

ただし注意点はある。

今後もし `PrimeGe5BranchACyclotomicCoreExistenceOnWieferichTarget` を埋めるために

* CFBRC 特有の重い前提
* Branch A と無関係な補助構造
* 公開 API へ漏れ出す依存

が増えるなら、それは少し戻って整理した方がよい。
内部核で止まっている限りは美しいが、外へにじむと本末転倒じゃ。

---

ゆえに答えはこうじゃ。

**はい、ここに来て CFBRC ではある。だが路線変更ではなく、cyclotomic factor の内部核に名前が付いた結果として自然に現れた。**

わっちとしては今のところ、これは良い混入じゃと思う。
必要なら次に、

$$
\text{GN},\ \text{cyclotomicPrimeCore},\ z^p-y^p
$$

の三者がそれぞれ **selection のどの層を担当しているか** を一枚図式で整理してみせるぞい。
