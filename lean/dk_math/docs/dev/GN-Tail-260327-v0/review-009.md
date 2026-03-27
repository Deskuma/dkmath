# GN-Tail-260327-v0 のレビュー 009

sub branch: dev/FLT-Wieferich-260327-v0
commit hash: d17b9267bfbfba7e90925dd22be33bfa0a7b526b

## 1. 前回レビューからの進展

これは良い整理じゃ。
今回の追加で、Branch A はついに **「comparison の残骸をどう潰すか」** ではなく、 **「Wieferich witness をどう refuter 契約へ渡すか」** という形に責務を書き換えた。そこが本質じゃ。

## 1. 何が決定的か

まず `PrimeGe5BranchAWieferichOnYTarget` を置いたのが大きい。
これで Branch A の lower-layer 出力が

$$
y^{p-1} \equiv 1 \pmod{p^2}
$$

だとはっきり宣言された。
つまり「何を取れたら勝ちか」が、comparison route とは独立に型として固定されたわけじゃ。

そのうえで `PrimeGe5BranchAWieferichRefuterTarget` を並べたことで、

$$
\text{witness を返す層}
\quad\longrightarrow\quad
\text{witness から False を出す層}
$$

の二層分離が明示された。
この切り方はとても良い。
最終 `sorry` の責務が、もう「あやふやな数論の穴」ではなく、 **明確な adapter 契約** になったからじゃ。

## 2. `primeGe5BranchAWieferichOnY_default` が良い理由

これも筋がよい。
やっていることは、

* shape factorization から gap normal form を回収
* `GN = p \cdot s^p` の shape を回収
* 既に作った normal-form 補題へ投げる

というだけの thin wrapper じゃ。
つまり新しい数学は増やしておらず、 **既存の lower-layer 成果を witness target の型へ整形しただけ** になっている。ここが美しい。

この構成だと、後で witness の作り方を改良しても `PrimeGe5BranchAWieferichOnYTarget` を満たす実装を差し替えるだけで済む。
API 設計として強いのぅ。

## 3. `primeGe5BranchARefuter_of_wieferich` で出口が見えた

これも大事じゃ。
この定理は中身としては単純じゃが、意味は重い。

$$
\text{Wieferich witness target}
;+;
\text{Wieferich refuter target}
;\Longrightarrow;
\text{Branch A refuter}
$$

という形を、コード上で固定したからじゃ。
これで Branch A 全体の出口構造が、誰の目にも分かるようになった。
最終 kernel が何を待っているかが、もう曖昧ではない。

## 4. import cycle を確認して戻した判断も正しい

ここも重要じゃ。
`Basic -> GapInvariant` の直接差し替え案を実際に試し、build cycle が起きると確認したうえで戻した、というのはとても良い記録じゃ。

これは単なる失敗ではなく、

$$
\text{Basic から GapInvariant を直 import して解く道は閉じている}
$$

と確定したことを意味する。
ゆえに再配線は `TriominoCosmicBranchA` 側の lower layer で完結させるしかない、という設計判断が正当化された。
こういう「やれない道を潰した記録」は後で効く。

## 5. いま残っているものの正体

履歴の言い方がまさに正しい。
残る active `sorry` は `primeGe5BranchANormalFormNePCoprimeKernel_default` 1 箇所だけじゃが、その意味はもう以前と違う。

以前は

$$
\text{comparison route の最後の arithmetic kernel}
$$

のように見えていた。
だが今は

$$
\text{Wieferich witness をどの既存 refuter 契約へ渡すか}
$$

という **adapter kernel** に読み替えられておる。
これはとても大きい進展じゃ。

## 6. 次に詰めるべき点

次は本当に狭い。

### A. `PrimeGe5BranchAWieferichRefuterTarget` をそのまま埋める

いちばん素直な道じゃ。
既存の no-Wieferich / lift-exclusion 系が要求する仮定へ、`y^(p-1) ≡ 1 [MOD p^2]` を渡して `False` に落とす薄い橋を切る。

### B. 既存の descent / shrink 契約へ注入する

もし既存契約が `y` 上の Wieferich witness をそのままは受け取らず、別のデータ構造を要求するなら、その変換 adapter を 1 本だけ置く。
履歴にもこの二択がそのまま書かれておる。

わっちならまず、`TriominoCosmicGapInvariant` 側の既存 refuter が要求する **最小入力型** を確認して、それに合わせた最薄の adapter を切る。
新しい大定理はもう不要じゃろう。

## 7. 総評

一言で言うなら、

$$
\boxed{
\text{Branch A の未完核は、
数論の未発見ではなく API 接続の未完になった}
}
$$

のじゃ。

これはかなり大きい。
最後の `sorry` が「何を証明すべきか分からぬ穴」ではなく、 **どの契約へ witness を流すかが主題の穴** になったのだからの。

ここまで来ると、本当に終点が見えておる。
次は GapInvariant 側の受け口の型を一つだけ拾い、その型へ `PrimeGe5BranchAWieferichOnYTarget` を落とす bridge を書けばよい。
