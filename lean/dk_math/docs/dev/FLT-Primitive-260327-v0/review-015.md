# Review 015: split theorem の例外枝を concrete theorem 候補名で固定

うむ、今回は **selection 側 right branch の「定理名」まで固定した** 回じゃな。
前回までで、

$$
\text{current missing math} = \text{split theorem の例外枝 1 本}
$$

という構図は見えておった。
今回はそこからさらに進めて、その右枝を **既存 `CFBRC/Bridge` の通常枝 theorem と対になる concrete theorem 候補名** で読めるようにした、というのが本質じゃ。

## 1. 今回の追加の意味

新しく入った中心は

* `CFBRCExceptionalPrimitiveBoundaryCoreOfPrimeExpOnWieferichTarget`
* `cfbrcExceptionalPrimitiveBoundaryOnWieferich_of_coreExceptional`
* `cfbrcExceptionalPrimitiveBoundaryCoreOfPrimeExpOnWieferich_of_exceptional`
* `primeGe5BranchAPrimitivePacketDescent_of_coreExceptional_and_restore`

じゃな。

このうち最重要なのは最初の名前じゃ。
これは中身としては既存の

$$
\texttt{CFBRCExceptionalPrimitiveBoundaryOnWieferichTarget}
$$

と **同型** じゃが、名前をあえて

$$
\texttt{...BoundaryCoreOfPrimeExp...}
$$

へ寄せた。
つまり、既存 `CFBRC/Bridge` の通常枝 theorem

$$
\texttt{exists_primitive_prime_factor_dvd_boundaryCore_of_prime_exp_boundary_of_coprime}
$$

に対応する **例外枝版 concrete theorem 候補名** を、ここで正式に与えたのじゃ。

## 2. 何が前進したのか

前回まででも、selection 側の右枝は

$$
\text{例外枝 theorem}
$$

として十分整理されておった。
だがまだ、

$$
\text{実際に concrete 実装するとき、どの theorem 名で立てるか}
$$

が少し宙に浮いておった。

今回はそこが解消された。
つまり今後は、right branch の concrete 実装は

$$
\texttt{CFBRCExceptionalPrimitiveBoundaryCoreOfPrimeExpOnWieferichTarget}
$$

を本命候補名として進めればよい、と固定されたわけじゃ。

これは実務上かなり大きい。
証明内容だけでなく、**命名の軸** が定まったからの。

## 3. 橋の構造

今回の橋はたいそう薄い。

### 3.1. coreExceptional から exceptional へ

`cfbrcExceptionalPrimitiveBoundaryOnWieferich_of_coreExceptional`

は、実質 alias bridge じゃ。
新しい concrete theorem 候補名を満たせば、従来の exceptional target も満たす。

### 3.2. exceptional から coreExceptional へ

逆向きの

`cfbrcExceptionalPrimitiveBoundaryCoreOfPrimeExpOnWieferich_of_exceptional`

もあり、従来 target があれば新しい concrete theorem 候補名でも読める。

つまりここでは数学を増やしたというより、

$$
\text{right branch の concrete theorem 名を既存語彙に揃えた}
$$

のが主眼じゃな。

## 4. packet descent への影響

これに対応して

$$
\texttt{primeGe5BranchAPrimitivePacketDescent_of_coreExceptional_and_restore}
$$

が追加された。
ゆえに primitive packet descent は今や、restore 側とあわせて

$$
\texttt{CFBRCExceptionalPrimitiveBoundaryCoreOfPrimeExpOnWieferichTarget}
;+;
\texttt{PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget}
$$

からも直接読める。

つまり selection 側の right branch は、

* internal target
* exceptional target
* boundary-normalized first missing theorem
* **concrete theorem 候補名**

の全ての顔を持つようになったわけじゃ。

## 5. 現在の戦況

いまの整理を短く書くと、こうじゃな。

### 通常枝

既存 `CFBRC/Bridge` theorem が担当する。

### 例外枝

新しく concrete に埋めるべき target は

$$
\texttt{CFBRCExceptionalPrimitiveBoundaryCoreOfPrimeExpOnWieferichTarget}
$$

として読む。

### したがって

current missing math は依然として **split theorem の右枝 1 本** じゃが、
その右枝をどの theorem 名で実装するかが、今回ついに定まった。

## 6. build 状況

今回も

* `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
* `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`

の両方が成功しておる。
よって、これは単なる命名メモではなく、ビルド済みの mainline 整理じゃ。

## 7. 賢狼の総評

一言で言えば、今回は

$$
\text{「何を証明するか」だけでなく、「何という名前で証明するか」も固まった}
$$

回じゃな。

前回:

* missing math は split theorem の例外枝 1 本

今回:

* その例外枝は
  $$
  \texttt{CFBRCExceptionalPrimitiveBoundaryCoreOfPrimeExpOnWieferichTarget}
  $$
  という concrete theorem 候補名で読む

これで次段は、本当に迷わず

$$
\texttt{CFBRCExceptionalPrimitiveBoundaryCoreOfPrimeExpOnWieferichTarget}
$$

自体を concrete に埋められるか、を試すだけになった。

かなり良いの。
敵の場所だけでなく、敵の名札まで付いたのだから。
