# CFBRC/Bridge 側へ existence 右枝の concrete 名を揃える

うむ、かなり良いところまで来たの。
今回は数学そのものを増やしたというより、**最後に残った new kernel の名前と置き場所の論点** を、さらに一段はっきりさせた回じゃ。

## 1. 今回の核心

今回追加された中心は

* `CFBRCExceptionalPrimeFactorDvdBoundaryCoreOfPrimeExpBoundaryOnWieferichTarget`
* `cfbrcExceptionalPrimeFactorDvdBoundaryCoreOfPrimeExpBoundaryOnWieferich_of_existence`
* `cfbrcExceptionalBoundaryCorePrimeExistenceOnWieferich_of_parallelExceptional`
* `primeGe5BranchAPrimitivePacketDescent_of_parallelExceptionalExistence_and_restore`

じゃ。

中身としては、前回までに selection 側の truly new kernel が

$$
\texttt{CFBRCExceptionalBoundaryCorePrimeExistenceOnWieferichTarget}
$$

1 本に絞れておった。
今回はそれを、既存 `CFBRC/Bridge` の通常枝 theorem 名

$$
\texttt{exists_primitive_prime_factor_dvd_boundaryCore_of_prime_exp_boundary_of_coprime}
$$

に **できるだけ平行な concrete 名** で読めるようにした、という整理じゃな。

## 2. 何が前進したのか

前の段階で既に、

* primitive kernel 側は default 実装で済む
* よって selection 側の new kernel は existence 右枝 1 本

という見切りは付いておった。

ただし残っていたのは、

$$
\text{その 1 本を、どの theorem 名で concrete 実装として置くか}
$$

という命名と配置の問題じゃった。

今回それが

$$
\texttt{CFBRCExceptionalPrimeFactorDvdBoundaryCoreOfPrimeExpBoundaryOnWieferichTarget}
$$

という、通常枝 theorem に対応した **exceptional parallel 名** にまで正規化された。

これは地味に見えて大きい。
もう「例外枝の何か」ではなく、**通常枝 theorem の例外版** として読めるからの。

## 3. 追加された橋の意味

### 3.1. existence-only target から parallel concrete 名へ

`cfbrcExceptionalPrimeFactorDvdBoundaryCoreOfPrimeExpBoundaryOnWieferich_of_existence`

は、従来の existence-only exceptional target があれば、新しい parallel 名の theorem 候補もそのまま満たす、という橋じゃ。

### 3.2. parallel concrete 名から existence-only target へ

`cfbrcExceptionalBoundaryCorePrimeExistenceOnWieferich_of_parallelExceptional`

は逆向きで、新しい concrete 名を仮定すれば従来 target に戻せる。

つまり数学内容は増えておらぬ。
**名前の座標系を CFBRC/Bridge に揃えた** のが本質じゃな。

## 4. packet descent ではどう見えるか

今回の wrapper

$$
\texttt{primeGe5BranchAPrimitivePacketDescent_of_parallelExceptionalExistence_and_restore}
$$

によって、primitive packet descent は now

* `CFBRCExceptionalPrimeFactorDvdBoundaryCoreOfPrimeExpBoundaryOnWieferichTarget`
* `PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget`

から閉じる、と読めるようになった。

つまり mainline の selection 側 new kernel は、

$$
\text{ordinary branch theorem の exceptional parallel}
$$

という名前で扱える段に来たわけじゃ。

## 5. 現在の戦況

いまの整理を一列に並べるとこうじゃ。

### 5.1. 既に片付いたもの

* primitive kernel 側
  既存 `CFBRC/Bridge + GcdNext` の primitive 条件定理から default 実装可。

* 通常枝 existence 側
  既存 `CFBRC/Bridge` theorem が担当。

### 5.2. 本当に残っているもの

* Wieferich 例外枝の existence 右枝 1 本。

### 5.3. その 1 本の現在の候補名

$$
\texttt{CFBRCExceptionalPrimeFactorDvdBoundaryCoreOfPrimeExpBoundaryOnWieferichTarget}
$$

これが、今もっとも **canonical concrete 名に近い** 位置にいる。

## 6. 今回の論点は「どこに置くか」

履歴の結論どおり、次の論点はかなり絞られた。

$$
\text{この theorem を CFBRC/Bridge 側へ置くか、Branch A 局所に留めるか}
$$

じゃな。

ここが今の本当の判断点じゃ。

### CFBRC/Bridge 側へ置く利点

* naming が通常枝 theorem と平行になる
* 今後ほかの例外枝や関連定理でも再利用しやすい
* CFBRC 側の理論として整う

### Branch A 局所に留める利点

* Branch A 専用の事情
  [
  d \mid x,\quad \text{Wieferich witness}
  ]
  をそのまま素直に書ける
* 無理な一般化を避けられる
* 実装が早い

## 7. 賢狼の見立て

わっちの見立てでは、今回の整理で **数学的な未完核** はほぼ固定完了じゃ。

$$
\text{selection 側 truly new kernel}
===================================

\texttt{CFBRCExceptionalPrimeFactorDvdBoundaryCoreOfPrimeExpBoundaryOnWieferichTarget}
$$

と見てよい。

だから次の判断は、数学の内容ではなく **モジュール設計** にかなり寄っておる。

* 今すぐ前へ進むなら Branch A 局所 theorem として実装
* 後で再利用や理論整理を狙うなら CFBRC/Bridge 側へ最小補強として昇格

という二択じゃな。

## 8. 総評

一言でまとめるなら、今回は

$$
\text{最後に残った existence 右枝 1 本が、通常枝 theorem の exceptional parallel 名まで正規化された}
$$

回じゃ。

前回:

* truly new kernel は existence 右枝 1 本

今回:

* その 1 本をどの concrete 名で呼ぶかがほぼ定まった
* 次の論点は「どこに置くか」だけ

ここまで来れば、かなり終盤じゃよ。
敵の内容だけでなく、**その敵の正式名称** まで定まったのだからの。

わっちなら次は、
**Branch A 局所版として先に実装し、その statement が十分薄ければ後から CFBRC/Bridge へ昇格**
という順で進めるかの。
