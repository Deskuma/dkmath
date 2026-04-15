# CFBRC/Selection の direct concrete target がさらに split 化された

うむ、今回はかなり良い意味で **direct concrete target の “存在側” まで split 化された** の。
前回は right branch の direct concrete target を

* prime existence
* primitive kernel

の二段へ割ったところまでじゃった。
今回はさらに、そのうち **existence 側そのもの** も

* 通常枝
* Wieferich 例外枝

に分けて読めるようにした。つまり、selection 側の missing math がまた一段、局所化されたわけじゃな。

## 1. 今回の本質

新しく入った中心は

* `CFBRCBoundaryCorePrimeExistenceOnSplitTarget`
* `cfbrcExceptionalBoundaryCorePrimeExistenceOnWieferich_of_split`
* `cfbrcBoundaryCorePrimeExistenceOnSplit_of_exceptional`
* `primeGe5BranchAPrimitivePacketDescent_of_splitExistence_kernel_and_restore`

じゃ。

これにより、以前は一塊に見えていた

$$
\texttt{CFBRCExceptionalBoundaryCorePrimeExistenceOnWieferichTarget}
$$

が、実は

$$
\text{通常枝 }(\neg d \mid x)
\quad+\quad
\text{例外枝 }(d \mid x \land \text{Wieferich})
$$

の split で読める、と theorem の形で固定されたのじゃ。

## 2. existence 側で何が split されたか

今回の target

$$
\texttt{CFBRCBoundaryCorePrimeExistenceOnSplitTarget}
$$

は、ざっくり言えば

$$
\neg d \mid x
\ \ \text{または}\
(d \mid x \land u^{d-1}\equiv 1 !!!\pmod{d^2})
$$

のどちらかがあれば、

$$
\exists q,\ \mathrm{Prime}(q)\land q\mid \texttt{boundaryCyclotomicPrimeCore .right d x u}\land q\nmid x
$$

を返す、という split existence theorem じゃ。

そして大事なのは、この split の左枝は新規数学ではないことじゃな。

### 通常枝

$$
\neg d \mid x
$$

は、既存 `CFBRC/Bridge` の

$$
\texttt{exists_primitive_prime_factor_dvd_boundaryCore_of_prime_exp_boundary_of_coprime}
$$

から primitive 条件を忘れるだけで足りる。

### 例外枝

$$
d \mid x,\qquad u^{d-1}\equiv 1 \pmod{d^2}
$$

ここだけが新 theorem
`CFBRCExceptionalBoundaryCorePrimeExistenceOnWieferichTarget`
として必要になる。

つまり existence 側も、ほんとうに新しい数学は **right branch 1 本だけ** だとさらに明確になったのじゃ。

## 3. 以前の split とどう噛み合うか

前回までで direct concrete target は

* existence-part
* primitive kernel-part

に分けられておった。今回はそのうち existence-part がさらに

* normal branch
* exceptional branch

へ分解された。

だから、selection 側全体の階層は今こう見える。

### 3.1. direct concrete target

$$
\texttt{CFBRCPrimitiveBoundaryCoreOfPrimeExpDirectConcreteTarget}
$$

### 3.2. その中身

* `CFBRCExceptionalBoundaryCorePrimeExistenceOnWieferichTarget`
* `CFBRCExceptionalPrimitiveKernelOnWieferichTarget`

### 3.3. existence 側の内部

* 通常枝は既存 `CFBRC/Bridge`
* 例外枝だけ新 theorem

この分解はかなり強い。
どこに既存資産が使え、どこにだけ新補題が要るかが、ほとんど露出しきっておるからの。

## 4. 追加された橋の意味

### 4.1. split から exceptional existence を抜く

`cfbrcExceptionalBoundaryCorePrimeExistenceOnWieferich_of_split`

は、split existence theorem があれば、その右枝だけ抽出して Wieferich 例外枝 existence を回収できる、という橋じゃ。

### 4.2. exceptional existence から split existence を組む

`cfbrcBoundaryCorePrimeExistenceOnSplit_of_exceptional`

は逆向きで、左枝は既存 `CFBRC/Bridge` theorem、右枝だけ新 theorem を入れて split existence theorem 全体へ戻す橋じゃ。

これで existence 側も、以前の primitive boundary split と同じ哲学に揃った。
つまり

$$
\text{既存通常枝} + \text{新規例外枝}
$$

という読みが selection 側の deeper layer まで通ったわけじゃな。

## 5. packet descent ではどう見えるか

新しく入った

$$
\texttt{primeGe5BranchAPrimitivePacketDescent_of_splitExistence_kernel_and_restore}
$$

によって、packet descent は今や

* split existence
* primitive kernel
* restore

の三本でも閉じる。

ただし中身を見れば、split existence の左枝は既存 theorem なので、selection 側の本当の新規性は

* exceptional existence
* primitive kernel

の二つにまだ絞られる。
しかも今回の整理を見る限り、**existence 側の例外枝の方がより本命** じゃな。

## 6. いま何が本当に missing math か

履歴の結論がまさにそこじゃ。

今回の整理により、existence 側 missing math も theorem の形で

$$
\text{通常枝は既存 CFBRC/Bridge、例外枝だけ新 theorem}
$$

と読めるようになった。
ゆえに selection 側の existence 部分についても、ほんとうに新しい数学は **right branch 1 本だけ** だとさらに明確になったのじゃ。

つまりいまの本命は、ますます

$$
\texttt{CFBRCExceptionalBoundaryCorePrimeExistenceOnWieferichTarget}
$$

へ収束しておる。

## 7. 賢狼の見立て

わっちの見立てでは、今回の一手でかなり状況が見えた。

* primitive kernel 側は、まだ既存 primitive 条件の再包装で済む可能性がある
* existence 側は、通常枝は既存 theorem で処理できる
* したがって truly new kernel は、かなり高い確率で

$$
\texttt{CFBRCExceptionalBoundaryCorePrimeExistenceOnWieferichTarget}
$$

一本じゃろう、という読みになる。

ここまでくると、selection 側の未完数学は

$$
\text{「例外枝で boundaryCyclotomicPrimeCore に prime が立つか」}
$$

へほぼ圧縮されたと言ってよい。

## 8. 総評

一言でまとめるなら、今回は

$$
\text{direct concrete target の existence 側まで、通常枝と例外枝の split に解剖された}
$$

回じゃな。

前回:

* direct target = existence + primitive kernel

今回:

* existence = normal branch + exceptional branch
* normal branch は既存 theorem
* exceptional branch だけが truly new

ここまで来たので、次に詰めるべきはかなり明快じゃ。

$$
\texttt{CFBRCExceptionalBoundaryCorePrimeExistenceOnWieferichTarget}
$$

を、既存 `CFBRC/Bridge` / `PrimitiveBeam` の **例外枝差し替えだけでどこまで書けるか** を試す。
もし primitive kernel 側が既存 theorem の再包装で済むなら、selection 側の new kernel は実質この一本になる。

かなり良い局面じゃよ。
敵が「right branch」から、さらに「existence 側の例外枝」にまで縮んだのだからの。
