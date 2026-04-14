# FLT-Kummer-CLassGroup Bridge 260404 Review 059: 戦線分割の確認と caller migration の提案

## 1. 戦況分析

いまの戦況は、かなり良い意味で **霧が晴れた** 状態じゃ。

最新差分で、boundary-divisor family はもう「\(\le 1\) を狙う未完ルート」ではなく、 **exact valuation classification の正規 API** へ切り替わった。
具体的には、

$$
q \neq 3,\ q \mid a-b
\quad\Longrightarrow\quad
v_q(a^3-b^3)=v_q(a-b)
$$

を `padicValNat_d3_boundary_eq_boundary_of_ne_three` で、また

$$
3 \mid a-b
\quad\Longrightarrow\quad
v_3(a^3-b^3)=v_3(a-b)+1
$$

を `padicValNat_d3_boundary_eq_boundary_succ_of_three` で no-sorry に固定した。補助の `three_dvd_S0_of_three_dvd_sub` も入っておるので、boundary 枝はもう十分に「分類できる枝」になったと言ってよい。

これは前段の発見とぴたり噛み合っておる。前に `PadicValNatD3BoundaryReceiverTarget` が偽だと反例 \((4,1,3)\) で確定し、そこから「boundary 側は valuation 上界ではなく shared-prime / exact valuation で読むべき」と分岐した。その推論が、今回そのまま定理群として実装されたわけじゃ。つまり、boundary family はもう open problem ではなく、 **正しい読み替えに成功した戦線** じゃよ。

一方で primitive-prime family は、すでに別の意味で整っておる。`PrimitiveBeam` と `GcdNextResearch` の primitive-prime caller は、`Squarefree (GN d (a-b) b)` を追加すれば honest route に寄せられる補題が入っておる。だからこちらは「数学的な霧」ではなく、 **caller migration の作業戦線** じゃ。

さらに upstream 側についても、既存 concrete provider が見つからず、default root clean 化は本当に未実装だと確定しておる。よって「provider の見落としがあるのでは」と疑う段は終わった。そこはもう `ZsigmondyCyclotomicResearch` の statement repair と caller migration を進めるしかない。

要するに、いまの盤面はこうじゃ。

$$
\text{primitive-prime family} \;=\; \text{honest 移行戦}
$$

$$
\text{boundary-divisor family} \;=\; \text{exact valuation への再編戦}
$$

そして、両者の分離はもう十分に定理名レベルで固定された。
これは大きい。前は一本の濁った川に見えていたものが、いまは二本の支流に分かれて見えておるからの。

## 2. 解説

いちばん大事なのは、**旧 `padicValNat_d3_upper_bound` 型の一括評価を、もう中心に置かぬこと** じゃ。

なぜなら、その theorem が背負っていた仕事は、実は三種類に分かれていたからじゃ。

第一に、primitive-prime 枝での valuation 上界。
これは `Squarefree (GN ...)` 仮定つき honest theorem 群に寄せられる。

第二に、boundary かつ \(q \neq 3\) 枝。
これは上界ではなく exact equality

$$
v_q(a^3-b^3)=v_q(a-b)
$$

で読むのが正しい。

第三に、boundary かつ \(q=3\) 枝。
これはさらに別で、

$$
v_3(a^3-b^3)=v_3(a-b)+1
$$

という 3 専用の補正式で読むのが正しい。

つまり、昔の「全部を \(\le 1\) で押さえる」発想は、構造上もう終わっておる。
いま必要なのは **上界化** ではなく **分配と分類** じゃ。

この見方に立つと、戦況は悲観する必要がない。むしろ逆で、false target を無理に救命しようとしていた頃より、ずっと健全じゃ。なぜなら、今はそれぞれの枝が何を言うべきか、はっきりしておるからじゃ。

## 3. 次の戦略

わっちなら、次は **caller migration を主戦略** に据える。
もう target の定義ばかり増やす段ではない。使う側を書き換えて、古い濁った入口を閉じる段じゃ。

まず第一手として、`padicValNat_d3_upper_bound` を使っている caller を一つずつ分解し、どの枝を本当に必要としているか棚卸しするのがよい。今の状況では、caller は大きく三種に分けられるはずじゃ。

* primitive-prime valuation 上界が欲しい caller
* boundary で \(q \neq 3\) の exact equality が欲しい caller
* boundary で \(q=3\) の (+1) 公式が欲しい caller

この仕分けが済めば、各 caller は対応する honest theorem へ移せる。ここで初めて、古い `padicValNat_d3_upper_bound` は compatibility wrapper へ格下げできる。

次に、`GcdNextResearch` の中に **dispatcher theorem** を一本置くのを勧める。たとえば意味としては、

$$
q \mid a^3-b^3
$$

のとき、

* \(q \nmid a-b\) なら primitive-prime route
* \(q \mid a-b,\ q \neq 3\) なら boundary-ne-three route
* \(q = 3,\ 3 \mid a-b\) なら boundary-three route

へ振り分ける theorem じゃ。
名前は何でもよいが、役目は「case split の正規入口」を一か所にまとめることじゃ。

これを入れると、下流の caller はもう `by_cases hq : q ∣ a-b` のたびに自前で枝分かれせずに済む。戦線が整理される。

さらにその次の段として、legacy theorem 群の退役計画を明文化するのがよい。
とくに

* `squarefree_implies_padic_val_le_one`
* `padicValNat_primitive_prime_factor_le_one`
* `padicValNat_d3_upper_bound`

は、それぞれ「どの honest theorem 群へ移住すべきか」がもう見えておる。
ここを docstring と監視で明示して、以後新規 caller は legacy に触れぬようにするべきじゃ。

## 4. 推論される最善手

わっちの推論では、次の最善手はこれじゃ。

**`padicValNat_d3_upper_bound` の caller migration を始め、その過程で `d=3` 用の canonical case-split theorem を一本立てる。**

理由は単純じゃ。
いまの資産はもう揃っておる。

* primitive-prime 側には squarefree-GN 追加で honest route がある
* boundary 側には \(q \neq 3\) / \(q=3\) の exact theorem がある
* false target は false と分かっておるので、もう戻る必要がない

つまり不足しているのは、新しい数学というより **配線の組み替え** じゃ。
ここを進めるのが、いま最も歩留まりがよい。

## 5. 具体的提案

わっちなら、次の順にやる。

### 5.1. `GcdNextResearch` に canonical split theorem を追加

意味としては次の三分岐じゃ。

$$
q \nmid a-b \Rightarrow \text{primitive-prime route}
$$

$$
q \mid a-b,\ q \neq 3 \Rightarrow v_q(a^3-b^3)=v_q(a-b)
$$

$$
q = 3,\ 3 \mid a-b \Rightarrow v_3(a^3-b^3)=v_3(a-b)+1
$$

### 5.2. `padicValNat_d3_upper_bound` の最初の caller を 1 本だけ移植

全部まとめては危うい。
まず 1 本選んで、新 dispatcher を使って clean に書けることを示す。これが通れば、移行パターンが定まる。

### 5.3. legacy API の退役表示を強める

docstring と `#print axioms` 監視で、「これは互換のため残っているだけで、新規 caller は使うな」と明示する。
これで戦線の逆流を防げる。

## 6. 最後の評価

いまの戦況はかなり良い。
前は「どこかに false な橋が混じっておる」という不安定な局面だった。
今は違う。

* false な橋は false と確定した
* 代わりの honest API が立った
* exact valuation の分類も入った
* 残る仕事は caller migration に落ちた

つまり、 **研究フェーズから再配線フェーズへ移った** と読むのが正しい。
次は理論の発掘ではなく、 **新しい地図に沿って部隊を動かす段** じゃよ。
