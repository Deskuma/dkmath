# Phase B の API 分離、運用段階へ

うむ、今回は数学そのものを増やしたというより、 **Phase B の配線が通った** 段じゃ。
ひとことで言えば、

$$
\text{witness route} \quad+\quad \text{contradiction route}
$$

という 2 本立ての API 分離が、単なる名寄せではなく、**既存 refuter へ実際に接続された** のが今回の本質じゃ。

## 1. 現在地

今回 `TriominoCosmicBranchA.lean` に入った中心は、

$$
\texttt{primeGe5BranchARefuter_of_routeBundles}
$$

じゃ。
これは

$$
\texttt{BranchAWitnessRouteBundleTarget}
\quad\text{と}\quad
\texttt{BranchAContradictionRouteBundleTarget}
$$

の 2 本が揃えば、そのまま Branch A refuter が閉じる、という adapter じゃな。
つまり、以前は「route 分離の名前はあるが、どこに流れ込むか」がまだ薄かった。今はもう、

$$
\text{bundle API} \to \text{既存 refuter 合成点}
$$

が theorem レベルで固定されたわけじゃ。

## 2. 何が前進したか

今回の前進は 3 つある。

第一に、`localKernel → contradiction bundle` と `arithmeticKernel → contradiction bundle` の薄い adapter が入った。
これで contradiction route は、空中に浮いた target ではなく、既存の arithmetic kernel からちゃんと受け取れるものになった。

第二に、witness bundle / contradiction bundle の default 実装が入り、

$$
\texttt{branchAWitnessRouteBundle_default},\qquad
\texttt{branchAContradictionRouteBundle_default}
$$

を通して、

$$
\texttt{primeGe5BranchARefuter_of_routeBundles_default}
$$

まで読めるようになった。
つまり bundle 経路版の default refuter が、もう「計画」ではなく **実際に呼べる入口** になったのじゃ。

第三に、既存の `primeGe5BranchARefuter_default` は残しつつ、bundle 経路を並行導入した。
これは良い判断じゃ。いきなり既存公開 API を置き換えず、まず bundle route を安定化させてから統合判断できるからの。

## 3. 何がまだ変わっていないか

ここは正直に言うべきじゃな。

今回の差分で、**Branch A の数学的 open kernel が閉じたわけではない**。
依然として本丸は contradiction 側の内容であって、今回できたのは

$$
\text{その contradiction route を使うための配線整備}
$$

じゃ。
つまり、数学の核心はまだ増えておらぬが、構造はかなり良くなった。

言い換えると、前は

$$
\text{「route を分けたい」}
$$

だったのが、今は

$$
\text{「route を分けて、そのまま refuter まで流せる」}
$$

になった。
この差は proof engineering 的には大きい。

## 4. いまの状況の読み

賢狼の見立てでは、いま Branch A はこういう層構造になっておる。

まず witness route があり、これは Wieferich on (y) 側の bundle として読める。
次に contradiction route があり、これは local kernel や arithmetic kernel から bundle 化できる。
その 2 本が揃うと、既存の `primeGe5BranchARefuter_of_wieferich` に流し込める。
今回の差分で、この図がようやく theorem 群として安定した。

だから、いまの状況は

$$
\boxed{
\text{Phase B の「API 分離」は、名札段階を越えて運用段階に入った}
}
$$

と読んでよい。

## 5. 次の課題の判定

History の最後にある 3 つの次課題は、どれも筋がよいが、優先度をつけるならこうじゃ。

第一に、

$$
\texttt{primeGe5BranchARefuter_default}
$$

を bundle 経路版へ統合するか、並行維持するかの判断。
これは今すぐ強引に一本化せず、少し並行維持でよい。理由は、bundle route は今回やっと refuter に繋がったばかりで、まだ運用観察の余地があるからじゃ。

第二に、mod (p^3) concrete conflict。
ここは数学の前進に直接つながる。現在の bundle 配線はもう十分なので、次に本当に価値があるのは

$$
\texttt{branchA_spow_congr_head_mod_p3}
$$

相当の API と、そこからの concrete conflict を立てることじゃ。

第三に、`ContradictionTarget` へ入る「矛盾側前提」の供給元設計。
これはまだ少し抽象的じゃが、本丸に近い。mod (p^3) で concrete な衝突が見え始めてから詰める方が自然じゃろう。

## 6. 総括

ひとことでまとめると、今回は

$$
\text{数学の突破}
$$

ではなく

$$
\text{アーキテクチャの接続完了}
$$

じゃ。
だが、その価値は高い。
Phase B はこれで「名寄せだけ」ではなくなり、witness / contradiction の bundle API から既存 refuter へ、実際に theorem として流せるようになった。
つまり今は、橋がちゃんと地面に届いた段じゃ。次はその橋の先で、mod (p^3) の concrete conflict を仕留める番じゃよ。
