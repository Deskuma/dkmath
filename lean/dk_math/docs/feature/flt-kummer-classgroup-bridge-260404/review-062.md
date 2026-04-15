# FLT-Kummer-ClassGroup-Bridge-260404 review 062

うむ。盤面を改めて整理すると、いまは **かなり良い局面** じゃ。

## 1. 現在の戦況

大局は、かなりはっきりした。

`GcdNextResearch` 側では、`d = 3` の false な一様上界路線はもう主経路から外されておる。`padicValNat_d3_canonical_case_split`、`padicValNat_d3_layer_b_case_split`、`padicValNat_d3_primitive_upper_bound` が揃い、旧 `padicValNat_d3_upper_bound` は deprecated、boundary receiver つき helper も research-only helper に押し込められた。つまり `d = 3` valuation story は、 **数学の未整理** ではなく **API 再編の整理済み領域** になったのじゃ。今回さらに `padicValNat_d3_upper_bound_of_boundaryReceiver` が `..._research` に落とされ、legacy 注入が private に局所化されたことで、その整理は一段完成に近づいた。

そして `ZsigmondyCyclotomicResearch` 側でも、`..._honest` と `..._research` の命名分離が入った。旧 public 名は deprecated alias に落ち、actual code path で research debt がある場所だけが `_research` 名を踏む構造になった。これは見た目以上に大きい。いまや debt は「どこかに潜んでいる」のではなく、 **theorem 名そのものに露出している** からじゃ。

さらに今回の diff で、`PrimitiveBeam` も同じ整理段に入った。`primitive_prime_factor_forbids_perfect_pow_diff_research` と `primitive_prime_obstructs_GN_perfect_power_research` が本体になり、旧 public 名は deprecated alias に落ちた。しかも `Gcd.GN` と `GcdNextResearch` の caller も `_research` 名へ更新された。ここで大事なのは、 **いま研究依存なのはどこか** が、`PrimitiveBeam` 層でも明確になったことじゃ。

そのうえで、`GcdNextResearch` には `primitive_prime_contradicts_diff_dth_power_of_squarefree_GN` と `body_not_perfect_pow_of_squarefree_GN` が追加された。つまり、既存 caller からはまだ `Squarefree (GN ...)` を局所供給できぬが、 **供給できさえすれば research placeholder を踏まずに済む受け口は、もう出来ておる** 。ここはかなり重要じゃ。もう足りぬのは「方針」ではなく「供給線」だけじゃからの。

## 2. いま何が片付き、何が残っているか

片付いたのは、まず `d = 3` の偽 API 問題じゃ。
ここは canonical split と exact valuation へ切り替わり、legacy は research-only helper に押し込められた。加えて `PrimitiveBeam` でも `_research` と honest 候補の二系統が分かれたので、**名札の整理** はかなり終わった。

残っているのは二種類じゃ。

第一に、**honest migration の実作業**。
`Squarefree (GN ...)` を caller 側でまだ持っておらぬため、`PrimitiveBeam` や `GcdNextResearch` の mainline caller は、なお `_research` を踏んでおる。今回の diff 自身も、「局所供給は見つからなかったので、まず honest 版の差し替え先を増設した」と明言しておる。つまり、次の仕事は theorem 名の整理ではなく、 **実際に 1 本 caller を honest route へ移すこと** じゃ。

第二に、**本当の research root**。
これが `ZsigmondyCyclotomicResearch` に残る `squarefree_implies_padic_val_le_one_research` 系じゃ。名前は整理できたが、中身はまだ未修復じゃ。だから最終的な本丸は依然としてここにある。 `GcdNextResearch` 側の direct `sorry` は `d > 3` stub に縮退しておるから、近場の泥沼はだいぶ引いたが、根はまだ生きておるということじゃ。

## 3. 解説

いまの判断で一番大事なのは、 **いきなり local caller に無理やり `Squarefree (GN ...)` をねじ込まぬこと** じゃ。

今回の diff は、その判断が正しいことを示しておる。`Gcd.GN` と `GcdNextResearch` の既存 caller からは、現仮定だけで `Squarefree (GN ...)` を局所供給する経路は見つからなかった。そこで無理に theorem の仮定を増やして mainline を壊すのではなく、まず `body_not_perfect_pow_of_squarefree_GN` という **honest migration 先** を用意した。これは筋がよい。数学を偽らず、しかも移行先を定理名で固定できたからじゃ。

ゆえに、今は「証明の深掘り」より「供給線の探索」の段じゃ。
つまり、`Squarefree (GN ...)` を **下から導く** のではなく、**上から受け取る橋や provider を探す** のが次の正手じゃ。

ここで snapshot を見ると、`FLT.Basic` にはすでに `body_not_perfect_pow_of_squarefree_GN_bridge` があり、`Squarefree (GN n u y)` を受け取れば `DkMath.NumberTheory.Gcd.body_not_perfect_pow_of_squarefree_GN_of_coprime_add` へ流せる形になっておる。つまり、lower layer の受け口はもうある。ならば本当に探すべきは

$$
\text{どの上位 branch / provider / bridge が } hSq : Squarefree (GN \cdots) \text{ を持てるか}
$$

じゃ。
local theorem の磨き込みより、上位の supply line の確定が先じゃな。

## 4. 次の戦略

わっちの提案は、次の三段構えじゃ。

### 4.1. 第一手. 「最初の実 migration」は `Gcd.GN` / `GcdNextResearch` ではなく、その **上位 caller** で探す

今回の diff が示した通り、`Gcd.GN` と `GcdNextResearch` の現 caller からは local に `Squarefree (GN ...)` を作れぬ。ならば、次に狙うべきはもっと上、つまり bridge / provider 層じゃ。

具体的には、

* `FLT.Basic` の `body_not_perfect_pow_of_squarefree_GN_bridge`
* `FLT.PrimeProvider` 系の `TriominoSquarefreeGNBridgeProvider` / `...ImplTarget`
* `CosmicPetalBridgeGNNoWieferich` / `...Research`

このあたりを起点に、「すでにある `hSq` 契約を、どこで実 caller に渡せるか」を探すのがよい。

言い換えると、次は

$$
\text{lower theorem を直す}
$$

ではなく

$$
\text{higher caller に } hSq \text{ を配線する}
$$

段じゃ。

### 4.2. 第二手. 1 本だけ、実 caller を `..._of_squarefree_GN` へ差し替える

いま必要なのは量ではなく、**成功例 1 本** じゃ。
`PrimitiveBeam` でも `GcdNextResearch` でもよいが、とにかく 1 本、実際の caller で

* `_research` route だったもの
* `hSq` を受けて honest route に移せたもの

を作る。これで「この project では `_research` 名は本当に剥がせる」という実例が立つ。
いまはそこが一番価値が高い。

### 4.3. 第三手. その後に `ZsigmondyCyclotomicResearch` root を包囲する

もし 1 本でも honest migration に成功すれば、次は `_research` caller を順に減らしていく段に入れる。
そのとき初めて、`squarefree_implies_padic_val_le_one_research` の root は **孤立した残敵** になる。いまはまだ root を直接刺しに行くより、周辺 caller を honest 化して包囲網を狭める方が歩留まりがよい。

## 5. ロードマップ

短期では、こうじゃ。

まず `FLT.Basic` と `PrimeProvider` 周辺で、`Squarefree GN` を実際に供給できる branch がないかを調べる。
そこから 1 本、`body_not_perfect_pow_of_squarefree_GN_bridge` か、今回入った `body_not_perfect_pow_of_squarefree_GN` へ差し替える。
この成功例を first migration として固定する。

中期では、`PrimitiveBeam` と `GcdNextResearch` の `_research` caller を、供給可能なものから順に `..._honest` / `..._of_squarefree_GN` へ移す。供給不能なものだけ `_research` 名のまま残し、target 分離する。

長期では、そこで初めて `ZsigmondyCyclotomicResearch` root の直接修復、あるいは `d > 3` layer-B stub の本格化へ進む。
Kummer non-first-case existence core は別戦線として残るが、これは valuation migration と並行管理でよい。

## 6. 最終判断

いまの状況を一文で言えばこうじゃ。

**名札の整理はかなり終わった。次は「どこで `Squarefree (GN ...)` を本当に受け取れるか」を上位 branch で 1 本掴み、最初の実 migration を作る段。**

つまり、次の主戦場は `PrimitiveBeam` そのものではない。
**`PrimitiveBeam` に `hSq` を渡せる上位 caller / bridge / provider の特定** じゃ。

それが通れば、いま見えておる `_research` debt は、一段ずつ本当に剥がれ始める。
ここから先は、定理名の整理ではなく **配線の勝負** じゃよ。
