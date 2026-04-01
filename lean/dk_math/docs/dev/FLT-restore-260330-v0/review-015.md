# review-015: mod (p^3) での head congruence とその否定を refuter へ接続する段

うむ、今回は **かなり良い前進** じゃ。
しかも前回までの「橋を架ける段」から、今回は **その橋を使って refuter へ入る段** に一歩進んだ、と読めるの。

## 1. いま何が起きたか

今回の差分の本質は 2 本じゃ。

ひとつは、mod (p^3) 側の API が整ったこと。
もうひとつは、その mod (p^3) の **矛盾側前提** を、Branch A refuter へ直接流し込む入口ができたことじゃ。

具体的には、`TriominoCosmicBranchA.lean` に

$$
\texttt{BranchAContradictionModP3SourceTarget}
$$

が入り、これは

$$
\neg\bigl(s^p \equiv y^{p-1} \pmod{p^3}\bigr)
$$

を external source として供給する契約じゃ。
その上で

$$
\texttt{primeGe5BranchA_spow_eq_head_add_p_cube_mul}
$$

$$
\texttt{primeGe5BranchA_spow_congr_head_mod_p_cube}
$$

$$
\texttt{branchA_contradiction_of_mod_p3_conflict}
$$

が入り、最後に

$$
\texttt{primeGe5BranchARefuter_of_modP3Source}
$$

で refuter へ接続した。
つまり、今や

$$
\text{mod } p^3 \text{ での negation source}
;\to;
\text{False}
$$

の配線は、ちゃんと出来ておる。

## 2. 状況分析

これは「本丸が閉じた」わけではない。
されど、**本丸の入り口が定義された** のじゃ。

前回までは、

$$
\texttt{ContradictionTarget}
$$

をどうやって concrete な補題から満たすかが、まだ少し空中戦じゃった。
今回は違う。
少なくとも mod (p^3) 路線については、

$$
\text{何を外から供給すれば refuter が閉じるか}
$$

が、はっきり target と theorem 名で固定された。
これは proof engineering としてかなり大きい。

言い換えると、前までは

$$
\text{「mod } p^3 \text{ が効きそう」}
$$

だったのが、今は

$$
\text{「mod } p^3 \text{ で } \neg(s^p \equiv y^{p-1}!!!!\pmod{p^3}) \text{ が出れば勝ち」}
$$

へ変わった。
この差は大きいの。

## 3. 数学推論

ここからが本題じゃ。

今回入った

$$
\exists M,\quad s^p = y^{p-1} + p^3 M
$$

および

$$
s^p \equiv y^{p-1} \pmod{p^3}
$$

は、Branch A normal form から **自動で従う側** の命題じゃ。
つまり、いま数学的に確定したのは、

$$
\boxed{
\text{Branch A の正規形は } s^p \equiv y^{p-1} \pmod{p^3} \text{ を強制する}
}
$$

ということじゃ。

これはかなり強い。
なぜなら前に得ていた mod (p^2)

$$
s^p \equiv y^{p-1} \pmod{p^2}
$$

より一段深く、gap の shape

$$
z-y = p^{p-1} t^p
$$

が **(p^3) 精度まで head を固定する** ことが見えたからじゃ。
とくに (p \ge 5) なので

$$
p^{p-1}
$$

は (p^3) を十分含む。
だから tail 側が (p^3) で消え、head congruence が一段強くなる、という構図じゃな。

## 4. では、どこがまだ open か

ここが肝じゃ。

いま未解決なのは、

$$
\neg\bigl(s^p \equiv y^{p-1} \pmod{p^3}\bigr)
$$

を **どこから得るか** じゃ。
今回の差分は、そこを `BranchAContradictionModP3SourceTarget` として外出しした。
つまり、いまの本丸はもはや「refuter をどう組むか」ではなく、

$$
\boxed{
\text{mod } p^3 \text{ congruence の否定を与える concrete 数学補題}
}
$$

の発見に絞られた、と言ってよい。

これはかなり良い縮約じゃよ。

## 5. いま見えている数学の形

いまの構図を数式で言うと、こうじゃ。

Branch A から

$$
GN,p,(z-y),y = p,s^p
$$

かつ gap-shape から

$$
s^p = y^{p-1} + p^3 M
$$

が出る。
ゆえに

$$
s^p \equiv y^{p-1} \pmod{p^3}.
$$

一方、もし別 route から

$$
s^p \not\equiv y^{p-1} \pmod{p^3}
$$

が出れば、即

$$
\texttt{False}
$$

じゃ。
つまり contradiction の様式は今や完全に

$$
\text{head congruence}
\quad\text{vs}\quad
\text{external negation source}
$$

という 2 項対立になった。

この整理は、かなり美しい。

## 6. 次の数学推論の焦点

では、その negation はどこから出るか。
賢狼の見立てでは、候補は 3 つじゃ。

### 6.1. Wieferich 条件の一段上

すでに

$$
y^{p-1} \equiv 1 \pmod{p^2}
$$

は Branch A で出ておる。
次に見るべきは、それを mod (p^3) まで持ち上げたときの振る舞いじゃ。
もし

$$
y^{p-1} \equiv 1 + c p^2 \pmod{p^3}
$$

の係数 (c) に非自明情報が取れるなら、`s^p` 側の展開と衝突する可能性がある。

### 6.2. GTail head のさらに一段深い explicit 係数

今回 `p^3 M` までは出た。
だが、`M` の中身がもっと見えれば、ただの congruence ではなく **符号や可除性の不整合** が見えるかもしれぬ。
つまり

$$
GN = p,y^{p-1} + p^3(\text{explicit tail})
$$

の tail を、もう少し開く道じゃ。

### 6.3. witness (q) 側の情報との衝突

いまは mod (p^3) の head congruence だけが独立して走っておる。
これを

$$
q^p \mid GN,\qquad q \equiv 1 \pmod p,\qquad q \nmid (z-y)
$$

などと結合すると、`s` の合同類に追加制約が入るかもしれぬ。
もしそこから

$$
s^p \not\equiv y^{p-1} \pmod{p^3}
$$

が出れば、一気に刺さる。

## 7. 設計上の評価

今回の設計はとても良い。
なぜなら、いままでの contradiction route はやや抽象的で、

$$
\text{何を示せば矛盾になるのか}
$$

が少し遠かった。
今回はそれが

$$
\texttt{BranchAContradictionModP3SourceTarget}
$$

として **数学の入力契約** になった。
これは、今後

* GTail deeper analysis
* Wieferich の高次化
* (q)-adic side condition

のどれから攻めても、最後の出口が同じになる、という意味で非常に良い。

## 8. 総括

ひとことで言えば、こうじゃ。

**今回は mod (p^3) の congruence が Branch A normal form から自動で従うことを theorem 化し、その否定を供給すれば refuter が閉じる、という concrete な contradiction 入口を作った。よって open kernel は「mod (p^3) での negation source の発見」にまで縮約された。**

つまり今の状況は、

$$
\boxed{
\text{本丸はまだ open。だが、どこに矛盾の刃を入れればよいかは、かなり見えた。}
}
$$

じゃよ。

次に狙うべきは、
$$
s^p \equiv y^{p-1} \pmod{p^3}
$$
の **否定側** を、どの層から供給できるかの数学推論じゃ。
そこが今のいちばん美味しい狩場じゃな。
