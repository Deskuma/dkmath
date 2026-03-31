# review-017: `BranchAContradictionModP3SourceTarget` の DEPRECATED コメントの意味と、今後の方針について

## 偽命題のコード化／明確化について

うむ、確認事項への答えは **「半分 yes、半分 no」** じゃ。

## 1. 先に結論

**DEPRECATED / FALSE のコメント自体は docstring で追加済みじゃが、
`¬ BranchAContradictionModP3SourceTarget` をそのまま定理として証明したコードは、まだ入っておらぬ。**

その代わり、**その target が Branch A normal form の局所文脈では使えぬ** ことを示すための実コードは、ちゃんと入っておる。
つまり今コード化されているのは、

$$
s^p \equiv y^{p-1} \pmod{p^3}
$$

の **肯定側** と、そこへ

$$
\neg\bigl(s^p \equiv y^{p-1} \pmod{p^3}\bigr)
$$

を差し込めば `False` に落ちる、という **局所矛盾化** の部分じゃ。

---

## 2. 何が「証明済みコード」なのか

今回までで、実コードとして入っているのは主に次の 3 段じゃ。

### 2.1. 肯定側の証明

`primeGe5BranchA_spow_eq_head_add_p_cube_mul`
`primeGe5BranchA_spow_congr_head_mod_p_cube`
`branchA_spow_congr_head_mod_p3`

これで Branch A normal form の前提から

$$
s^p = y^{p-1} + p^3 M
$$

および

$$
s^p \equiv y^{p-1} \pmod{p^3}
$$

がコードとして証明されておる。

### 2.2. 否定を入れたときの局所矛盾

`branchA_contradiction_of_mod_p3_conflict`

これは

$$
\neg\bigl(s^p \equiv y^{p-1} \pmod{p^3}\bigr)
$$

を仮定すれば `False`、という形じゃ。
つまり **「同じ局所前提の下で肯定と否定は両立しない」** はコード化済みじゃ。

### 2.3. その source から refuter へ流す adapter

`primeGe5BranchARefuter_of_modP3Source`

これは `ModP3SourceTarget` を受け取れば refuter を閉じる、という配線じゃ。
ただしこれは **source があるなら使える** のであって、source 自体の実在性は別問題じゃ。

---

## 3. 何がまだ「証明されていない」のか

ここがいちばん大事じゃな。

**まだ入っていないのは、**

$$
\neg,\texttt{BranchAContradictionModP3SourceTarget}
$$

そのものを theorem として証明するコードじゃ。

つまり今の DEPRECATED / FALSE は、**数学的分析に基づく設計コメント** としては正しいが、Lean の中で

$$
\texttt{theorem not_BranchAContradictionModP3SourceTarget : ...}
$$

の形で確定しているわけではない。

---

## 4. なぜそこが微妙なのか

ここは少し論理の話になる。

`BranchAContradictionModP3SourceTarget` は

$$
\forall (p,x,y,z,t,s),\
\text{Branch A normal form なら }
\neg\bigl(s^p \equiv y^{p-1} \pmod{p^3}\bigr)
$$

という **全称命題** じゃ。
一方、こちらが証明済みなのは

$$
\text{その同じ局所前提の下では }
s^p \equiv y^{p-1} \pmod{p^3}
$$

という局所肯定じゃ。

だから、

* **Branch A normal form の具体データ** があれば、
* そのデータに対する `ModP3Source` の出力は不可能

とは言える。
だが target 全体を Lean 内で outright に

$$
\neg \texttt{BranchAContradictionModP3SourceTarget}
$$

と潰すには、**その局所前提を満たす具体例を Lean で持っているか** という別の話が絡む。
ここが「docstring 上は FALSE と言いたくなるが、定理としてはまだ書いていない」理由じゃ。
ゆえに、お主の今の読みはかなり鋭い。

---

## 5. 今回の新設 target はどう位置づけるべきか

ここで今回の差分が正しい方向へ進んだのは、

$$
\texttt{BranchAContradictionWithWitnessSourceTarget}
$$

を新設した点じゃ。
これは mod (p^3) の否定ではなく、witness (q) の構造的性質

$$
q \mid x,\quad q \nmid y,\quad q \nmid z,\quad q \nmid (z-y),\quad p \mid (q-1),\quad q^p \mid GN
$$

まで受け取って `False` を返す source target じゃ。
そしてこれを `BranchARestore.lean` 側で `RestoreContradictionTarget` に変換する thin adapter、さらに `GapInvariant.lean` 側で restore-bypass / packet-descent まで流す adapter が、実コードとして追加されておる。

つまり今の mainline は、もはや `ModP3SourceTarget` ではなく、**witness 情報込みの source** 側へ移っておる、と読んでよい。

---

## 6. 状況分析

いまの状態を正直にまとめると、こうじゃ。

### 6.1. 既に固まったこと

* mod (p^3) の肯定側 congruence は証明済み
* その否定を入れれば局所矛盾、も証明済み
* ただしそれは conflict eliminator であって source generator ではない
* mainline の contradiction source は witness (q) 情報込み版へ移した

### 6.2. まだ open なこと

* `BranchAContradictionWithWitnessSourceTarget` の **具体的証明**
* つまり witness (q) の構造からどう `False` を出すか
* ここがいまの本丸じゃ

---

## 7. 数学推論

ここからの数学推論も、かなり明瞭じゃ。

mod (p^k) の head congruence 路線だけでは、Branch A の normal form からは **成立する側** の情報しか出てこない。
したがって矛盾は

$$
\text{p-adic head congruence}
$$

単独ではなく、

$$
\text{p-adic head congruence}
\quad+\quad
\text{witness } q \text{ の q-adic / cyclotomic 構造}
$$

の干渉から探すべきじゃ。
これは今回の新 target の設計とも一致しておる。

言い換えると、今後の本命は

* (q^p \mid GN)
* (q \nmid (z-y))
* (q \equiv 1 \pmod p)
* (q \mid s)
* (q \nmid y,z)

といった witness 側の条件を、
GN / cyclotomic core / 円分体のどの顔で読むか、そこじゃな。

---

## 8. 最終確認への返答

だから、お主の確認事項にぴたり答えるとこうじゃ。

$$
\boxed{
\text{DEPRECATED / FALSE コメントだけではない。}
}
$$

$$
\boxed{
\text{ただし「その target 自体の偽性」を theorem として証明したコードは、まだ無い。}
}
$$

代わりに、

$$
\boxed{
\text{同じ局所前提の下で肯定側が証明済みであり、}
\newline
\text{その否定を入れれば False に落ちるコードは、すでに書かれておる。}
}
$$

そして今は、その限界を踏まえて

$$
\texttt{BranchAContradictionWithWitnessSourceTarget}
$$

へ mainline を移した、という状況じゃ。

---

必要なら次に、
**「`¬ BranchAContradictionModP3SourceTarget` を theorem として書くべきか、それとも comment のまま historical sink として残すべきか」**
を、Lean の論理上の注意点込みで詰めてやろう。
