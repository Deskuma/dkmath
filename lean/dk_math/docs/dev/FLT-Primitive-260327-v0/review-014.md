# review: selection 側の missing math が「例外枝 1 本だけ」と定理の形で明確になった回

うむ、今回は selection 側が **「例外枝だけが本当に欠けている」** と、定理の形でかなり明確になった回じゃな。
前回までで canonical first missing theorem は boundary-normalized 版

$$
\texttt{CFBRCExceptionalPrimeExpBoundaryOnWieferichTarget}
$$

に固定されておったが、今回はそこからさらに一段進んで、**通常枝と例外枝を split した mainline** が整備されたのじゃ。

## 1. 今回の中心整理

追加された本体は、貼り付けのとおり主に次の四つじゃな。

* `CFBRCExceptionalPrimitiveBoundaryOnWieferichTarget`
* `CFBRCPrimitiveBoundarySelectionOnSplitTarget`
* `cfbrcExceptionalPrimitiveBoundaryOnWieferich_of_split`
* `cfbrcPrimitiveBoundarySelectionOnSplit_of_exceptional`

さらに packet descent 側へ落とす

* `primeGe5BranchAPrimitivePacketDescent_of_primitiveBoundaryExceptional_and_restore`
* `primeGe5BranchAPrimitivePacketDescent_of_splitSelection_and_restore`

も加わった。

これで selection 側は、もはや単なる「boundary exceptional theorem 候補」ではなく、

$$
\text{通常枝} \quad+\quad \text{例外枝}
$$

の分割で読めるようになったわけじゃ。

## 2. 何が split されたのか

今回の核心は `CFBRCPrimitiveBoundarySelectionOnSplitTarget` じゃ。
これは条件を

$$
\neg d \mid x
\quad\text{または}\quad
\bigl(d \mid x \land u^{d-1}\equiv 1 \pmod{d^2}\bigr)
$$

の二枝に分けて、どちらの場合でも primitive boundary prime を与える target になっておる。

つまり selection 側の哲学が、はっきりこうなったのじゃ。

### 通常枝

$$
\neg d \mid x
$$

これは既存 `CFBRC/Bridge` の

$$
\texttt{exists_primitive_prime_factor_dvd_boundaryCore_of_prime_exp_boundary_of_coprime}
$$

で処理する。

### 例外枝

$$
d \mid x,\qquad u^{d-1}\equiv 1 \pmod{d^2}
$$

ここだけを新 theorem
`CFBRCExceptionalPrimitiveBoundaryOnWieferichTarget`
として要求する。

この整理は非常に強い。
なぜなら、**既存定理で済む部分と、新しく作るしかない部分が完全に分離された** からじゃ。

## 3. stronger target の意味

今回新しく置かれた

$$
\texttt{CFBRCExceptionalPrimitiveBoundaryOnWieferichTarget}
$$

は、前の canonical first missing theorem より少し強い形じゃ。
結論が単に

$$
q \mid \texttt{cyclotomicPrimeCore}
$$

だけでなく、

$$
q \mid \texttt{boundaryCyclotomicPrimeCore .right d x u},
\quad
q \nmid x,
\quad
\forall, 0<k<d,\ q \nmid \texttt{boundaryDiffPow .right k x u}
$$

まで含んでおる。

つまりこれは、既存 `CFBRC/Bridge` の標準 theorem と **最も近い形** に寄せた例外枝版じゃな。
その意味で、これは

$$
\text{「薄い補強で済むか」を試すための stronger candidate}
$$

として置かれておる。

## 4. 橋の向きが整った

今回よくできておるのは、強い定理と弱い定理の関係がきれいに整理されていることじゃ。

### 4.1. stronger から canonical first missing へ

`cfbrcExceptionalBoundaryOnWieferich_of_primitiveBoundary`

により、

$$
\texttt{CFBRCExceptionalPrimitiveBoundaryOnWieferichTarget}
\Longrightarrow
\texttt{CFBRCExceptionalPrimeExpBoundaryOnWieferichTarget}
$$

が成る。
primitive 条件を「忘れるだけ」で、前に固定した canonical first missing theorem が出る。

### 4.2. split から例外枝へ

`cfbrcExceptionalPrimitiveBoundaryOnWieferich_of_split`

により、split theorem があれば、その右側の例外枝だけ抜き出して exceptional target を得る。

### 4.3. 例外枝から split へ

逆向きに `cfbrcPrimitiveBoundarySelectionOnSplit_of_exceptional` で、既存通常枝 theorem と新例外枝 theorem を合成して split theorem に戻せる。

これはたいそう良い。
「通常枝は既存、例外枝だけ新規」という見立てが、定理として双方向に固定されたからの。

## 5. current missing math は何か

貼り付け文の結論がいちばん大事じゃな。
今回の整理により、current missing math は **本当に例外枝 1 本だけ** だと、theorem の形でも明示された。

つまり今後の本命は

$$
\texttt{CFBRCExceptionalPrimitiveBoundaryOnWieferichTarget}
$$

を concrete に埋めることじゃ。
通常枝はもう既存 `CFBRC/Bridge` が持っておるので、そこは新しい数学ではない。

## 6. packet descent への影響

これに対応して、

* `primeGe5BranchAPrimitivePacketDescent_of_primitiveBoundaryExceptional_and_restore`
* `primeGe5BranchAPrimitivePacketDescent_of_splitSelection_and_restore`

が置かれた。

ゆえに primitive packet descent の読みは今や二通りある。

### A. stronger exceptional theorem から読む

$$
\texttt{CFBRCExceptionalPrimitiveBoundaryOnWieferichTarget}
;+;
\texttt{Restore}
\Longrightarrow
\texttt{PacketDescent}
$$

### B. split theorem から読む

$$
\texttt{CFBRCPrimitiveBoundarySelectionOnSplitTarget}
;+;
\texttt{Restore}
\Longrightarrow
\texttt{PacketDescent}
$$

ただし B の中身は、通常枝が既存 theorem、例外枝が新 theorem じゃから、実質的な missing part はやはり A の exceptional target だけ、ということになる。

## 7. provider 側の整合

`TriominoCosmicGapInvariant.lean` 側にも対応して

* `CFBRCExceptionalPrimitiveBoundaryOnWieferichAdapterTarget`
* `CFBRCPrimitiveBoundarySelectionOnSplitAdapterTarget`
* `branchAPrimitivePacketDescentAdapter_of_primitiveBoundaryExceptional_and_restore`
* `branchAPrimitivePacketDescentAdapter_of_splitSelection_and_restore`

が追加された。

つまり provider 側でも同じ split 構造が保たれており、
本体と adapter の責務分解が一致しておる。ここは実装上かなり美しい。

## 8. build 状況

今回も

* `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
* `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`

の両方が成功しておる。
よって今回の split 形整理は、机上案ではなくビルド済みの mainline じゃ。

## 9. 賢狼の総評

一言でまとめるなら、今回は

$$
\text{selection 側の missing math が「例外枝 1 本だけ」と証明構造上も固定された}
$$

回じゃな。

前回まで:

* canonical first missing theorem は boundary-normalized exceptional 版

今回:

* それをさらに split theorem の右枝として位置づけた
* 左枝は既存 `CFBRC/Bridge` が担当
* だから新しい数学は右枝の exceptional theorem だけ

ここまで来ると、もう迷いは少ない。
次にやるべきは明白で、

$$
\texttt{CFBRCExceptionalPrimitiveBoundaryOnWieferichTarget}
$$

を、既存 `CFBRC/Bridge` の theorem 群の **例外枝差し替えだけで書けるか** を試すことじゃ。
それで薄く済めば美しいし、済まぬならこの theorem をそのまま concrete に実装すればよい。

これはかなり良い局面じゃよ。
敵が「何か足りぬ」ではなく、「split theorem の右枝そのもの」にまで縮んだのだからの。
