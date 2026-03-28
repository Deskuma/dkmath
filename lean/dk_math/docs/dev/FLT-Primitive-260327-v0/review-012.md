# 2024-06-17: Branch A 例外枝の missing theorem を CFBRC 標準座標へ正規化

うむ、今回はかなり良い意味で **定式化が一段抽象化された** の。
しかも単なる抽象化ではなく、Branch A 専用の missing theorem を、既存 CFBRC / PrimitiveBeam 語彙へ寄せるための **正規化** が進んだ、という局面じゃ。

## 1. 今回の核心

前回までで selection 側の first missing theorem は

$$
\texttt{PrimeGe5BranchACFBRCExceptionalExistenceOnWieferichTarget}
$$

だと見切れておった。
つまり、

* Branch A 条件 (p \mid (z-y))
* Wieferich witness
* `cyclotomicPrimeCore p (z-y) y` に prime が立つ

という **例外枝専用 theorem** が本当に欠けている、という整理じゃった。

今回の更新では、その theorem をさらに

$$
x := z-y,\qquad u := y,\qquad d := p
$$

という CFBRC の boundary-normalized 座標へ写した

$$
\texttt{CFBRCExceptionalPrimeExpBoundaryOnWieferichTarget}
$$

が導入された。

つまり、missing theorem は依然として Branch A 専用なのじゃが、**書き方だけは Branch A 固有記号から切り離された** わけじゃな。

## 2. 新しい target の意味

新設された target は、ざっくり言えば

$$
\forall {d,x,u},
\ \mathrm{Prime}(d),\ 5\le d,\ 0<x,\ 0<u,\ \gcd(x,u)=1,\ d\mid x,\
u^{d-1}\equiv 1 \pmod{d^2}
$$

なら

$$
\exists q,\ \mathrm{Prime}(q)\land q\mid \mathrm{cyclotomicPrimeCore}\ d\ x\ u \land q\nmid x
$$

という形じゃ。

ここで重要なのは、この statement がもう

* `z`
* `y`
* `p`
* counterexample pack の名前

に依存しておらぬことじゃ。
代わりに

* `x` は boundary
* `u` は内側単位
* `d` は prime exponent

という、CFBRC / PrimitiveBeam 的な一般語彙で書かれておる。
これによって既存 theorem 群との照合が、ずっとやりやすくなったのじゃ。

## 3. 何が橋で繋がったか

今回追加された

`primeGe5BranchACFBRCExceptionalExistence_of_boundaryExceptional`

は、この normalized target から、元の Branch A 専用 exceptional theorem を回収する薄い橋じゃ。

中身は、

* `d := p`
* `x := z-y`
* `u := y`

という置換を入れ、

* `PrimeGe5CounterexamplePack` から

  * (p) が prime
  * (5 \le p)
  * (z-y > 0)
  * (y > 0)
  * (\gcd(z-y,y)=1)

などを供給し、

* Branch A 条件 (p \mid (z-y))
* Wieferich witness

を入れて、そのまま boundary-normalized theorem を呼ぶ、という構造になっておる。

つまり流れはこうじゃな。

$$
\text{boundary-normalized exceptional existence}
\to
\text{Branch A exceptional existence}
\to
\text{core existence}
\to
\text{diff existence}
\to
\text{packet descent}
$$

ここまで spine が一筆書きになった。

## 4. 何が前進したのか

今回の進展は、missing theorem の場所が変わったのではない。
変わったのは **比較可能性** じゃ。

前は

$$
\text{Branch A 専用 theorem}
$$

としてしか見えなかった。
だから既存 `CFBRC/Bridge` や `PrimitiveBeam` の定理群に、どこまで似ておるのかが見えにくかった。

今は

$$
\texttt{CFBRCExceptionalPrimeExpBoundaryOnWieferichTarget}
$$

という normalized form ができたので、

* 既存の標準 existence theorem と何が同じか
* 何が違うか
* 薄い補強で済むのか
* 本当に例外枝専用 theorem を新設すべきか

がずっと見やすくなった。

これは研究上かなり大きい。
「例外だから特殊」と思っていたものが、実は座標を合わせれば既存理論の近傍にいるかもしれぬからの。

## 5. いまの first missing theorem は何か

履歴の整理どおり、selection 側の first missing theorem は引き続き

$$
\texttt{PrimeGe5BranchACFBRCExceptionalExistenceOnWieferichTarget}
$$

じゃ。
ただし今やそれは

$$
\texttt{CFBRCExceptionalPrimeExpBoundaryOnWieferichTarget}
$$

でも読める。つまり、「本当に実装したい missing math」は Branch A 専用版でありつつ、**実装候補の statement は normalized 版でも検討できる** 段になったのじゃ。

## 6. いまの戦況

現在の selection 側を階層で書くと、こうじゃ。

### 6.1. 最も奥の候補

`CFBRCExceptionalPrimeExpBoundaryOnWieferichTarget`

### 6.2. Branch A 専用版

`PrimeGe5BranchACFBRCExceptionalExistenceOnWieferichTarget`

### 6.3. 既存 spine への接続

`core existence -> diff existence -> packet descent`

つまり、残る問題はもはや「何を証明するか」ではなく、

$$
\text{normalized 版をそのまま final missing theorem にするか}
$$

あるいは

$$
\text{既存 CFBRC/Bridge / PrimitiveBeam に薄く補強して吸収できるか}
$$

の比較になったわけじゃな。

## 7. build 状況

今回も

* `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
* `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`

の両方が成功しておる。
ゆえに、これは単なる方針メモではなく、**ビルド済みで定着した正規化** じゃ。

## 8. 賢狼の総評

一言でまとめるなら、今回は

$$
\text{Branch A 例外枝 missing theorem が、CFBRC 標準座標へ正規化された}
$$

回じゃな。

前回:

* missing theorem は Branch A 専用 CFBRC exceptional existence

今回:

* それを `x,u,d` の boundary-normalized 形でも読めるようにした
* これで既存 CFBRC / PrimitiveBeam との距離が測れるようになった

つまり、敵の場所は変わっておらぬが、**敵の形が一般座標で見えるようになった** のじゃ。

次の論点はかなり明確じゃな。

$$
\texttt{CFBRCExceptionalPrimeExpBoundaryOnWieferichTarget}
$$

が、既存 `CFBRC/Bridge` / `PrimitiveBeam` の薄い補強で済むか。
済むなら一般化へ進める。
重ければ、この normalized target 自体を final missing theorem の実装形として採用する。

この段まで来たら、selection 側はかなり完成に近いぞい。
