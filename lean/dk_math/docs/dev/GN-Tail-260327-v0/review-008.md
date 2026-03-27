# GN-Tail-260327-v0 のレビュー 008

git diff 88a20a69d897cbed91ebb5efc768bbcdfb308fa3..64622bda50d3d0404d2dc1cd6b77780556d4e91a

---

おお、これは **かなり本質的な前進** じゃ。
もう Branch A は「Wieferich っぽい匂いがする」段階ではなく、**lower layer でそのまま Wieferich witness を返す段階** に入ったと言ってよい。`primeGe5BranchANormalForm_y_wieferich_mod_p_sq` により、Branch A normal form から直接

$$
y^{p-1} \equiv 1 \pmod{p^2}
$$

が出る形まで到達しておる。しかもその前段として `primeGe5BranchANormalForm_spow_congr_one_mod_p_sq` も立っており、流れが完全に見える。

## 1. 今回の鎖は美しい

やっておることは薄いが、つながりが実に良い。

まず既に持っていた

$$
s^p \equiv y^{p-1} \pmod{p^2}
$$

を基点にして、`primeGe5BranchANormalForm_s_congr_one_mod_p` で

$$
s \equiv 1 \pmod p
$$

へ落とす。そこでは mod (p) へ落とした合同、(y) に対する Fermat、そして prime exponent の Frobenius 型補題

$$
s^p \equiv s \pmod p
$$

を組み合わせておる。今回 `Mathlib.FieldTheory.Finite.Basic` を import したのも、この筋のためじゃな。

次に、`s = 1 + p a` と書いて `exists_add_pow_prime_eq` を使い、

$$
s^p \equiv 1 \pmod{p^2}
$$

を得る。ここは強引な持ち上げではなく、局所二項展開で薄く済ませておるのがよい。最後に

$$
s^p \equiv y^{p-1} \pmod{p^2},
\qquad
s^p \equiv 1 \pmod{p^2}
$$

を合成して

$$
y^{p-1} \equiv 1 \pmod{p^2}
$$

へ到達する。つまり Branch A の normal form から、**完全な Wieferich-style witness** が lower layer で出るようになったわけじゃ。

## 2. これで何が変わったか

ここが一番大事じゃ。

以前の final kernel は

$$
\text{shape} + \text{GN-shape} + \text{coprime}(t,s) \to \mathrm{False}
$$

を、その場で直接ひねり出そうとしておった。
だが今は違う。

いまは Branch A 側で既に

$$
y^{p-1} \equiv 1 \pmod{p^2}
$$

を返せる。ゆえに final kernel の仕事は、もう新しい合同計算ではない。
**その witness を既存の Wieferich bridge 契約へ注入する配線** だけに近づいたのじゃ。履歴でも、その認識がはっきり書かれておる。

## 3. いまの残核の性質

したがって、残る `primeGe5BranchANormalFormNePCoprimeKernel_default` は、以前よりずっと軽く見てよい。
もう「未知の数論核」ではなく、

$$
\text{Branch A witness}
;\to;
\text{WieferichLift / TriominoWieferichBranchBridge input}
$$

の整合を付ける橋じゃ。
もちろん型が噛み合わねば多少の補題は要るが、主戦場は arithmetic から API 接続へ移った、と見てよい。

## 4. 次に切るべきもの

わっちなら次は二択で見る。

ひとつは、既存の `TriominoCosmicGapInvariant` 側が要求する witness 仕様に、`primeGe5BranchANormalForm_y_wieferich_mod_p_sq` をそのまま流し込める薄い adapter を探すこと。
もうひとつは、もし直接の型がないなら、Branch A 専用に

$$
\text{normal form} \to \text{Wieferich witness target}
$$

という極薄の target を 1 本だけ lower layer に置き、それを既存 bridge へ接ぐことじゃ。履歴の「必要なら Branch A 専用の Wieferich witness target を 1 本だけ新設」は、かなり筋が良い。

## 5. 総評

一言でいえば、

$$
\boxed{
\text{Branch A は、
Wieferich route の入口ではなく、
もう witness 供給源そのものになった}
}
$$

のじゃ。
これは大きい。かなり大きい。
ここまで来ると、残りは森の中で新しい獣を狩る段ではなく、既に捕まえた獲物を正しい門へ運ぶ段取りじゃよ。

次は `TriominoCosmicGapInvariant` 側の受け口の型を見て、**どの witness 名と形に合わせれば最短で kernel を閉じられるか** を詰めるのが最善じゃ。
