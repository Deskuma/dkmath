# report-008: ABC予想との関連と実装進捗状況

## 1. 結論

うむ、現況を先に一言で言うぞい。

**これは新しい進展になっておる。**
ただし性質は、ABC 予想本体の大定理が一気に前進した、というよりも、**ABC 側で再利用できる bridge 層が実装として定着し、公開導線まで整った** という進展じゃ。設計・実装計画で狙っていた「`CosmicFormula → Mass API → ValuationFlow → ABC Bridge` の spine」は、最小核としてはかなりきれいに閉じておる。

逆に言えば、**ABC 本体の未完核**、とくに既存の重い解析・確率評価・Janson 系の unfinished 部分そのものを今回直接閉じたわけではない。そこはまだ「これから」じゃ。INDEX でも `sorry` の集中先は主に `ABC021.lean` など既存の ABC 本丸側に残っておる。今回の bridge 実装は、その本丸へ入る前の補助基盤をかなり強くした、という位置づけになる。

## 2. スナップショット検証から見た実装到達点

今回の snapshot では、少なくとも次の流れが実体として確認できる。

まず `CosmicFormula/Mass` 側に

* `Core.lean`
* `Decompose.lean`
* `Branch.lean`

が入り、`Big / Body / Gap / Core / Beam` を **質量保存 API** として再公開する層ができておる。これは実装計画の Phase A と Phase B の中核そのものじゃ。`Tromino2D` や `Harmonic` を初回では保留するとしていた方針とも一致しておる。

つぎに `NumberTheory/ValuationFlow` 側に

* `Basic.lean`
* `Primitive.lean`

が入り、`padicValNat`・primitive prime・`GN` を、flow 的な命名で読み直す層ができておる。これも計画どおりで、初回は exact な Markov kernel や hitting 完成形までは行かず、primitive と valuation の spine を先に通す、という方針に沿っておる。

そして `ABC` 側では

* `MassBridge.lean`
* `ValuationFlowBridge.lean`
* `Bridge.lean`
* `BridgeExamples.lean`

が入り、さらに `ABC/Main.lean` から `Bridge` が import される形になった。つまり、bridge はもはや実験ファイルではなく、**ABC の公開面から見える API** になっておる。差分報告でも、`DkMath.ABC.Bridge` を public-facing aggregator とし、`DkMath.ABC.Main` から見えるようにしたと明記されておる。

## 3. 設計・実装計画との照合

計画書ベースで進捗を判定すると、わっちの見立てはこうじゃ。

### 3.1. Phase A. Cosmic Mass API

ここは **ほぼ完了** と見てよい。
`CoreBeamGap`、`ResidualNat`、`ResidualInt` の既存定理を wrapper / alias として再公開し、

$$
\text{Big} = \text{Body} + \text{Gap},\qquad
\text{Body} = \text{Core} + \text{Beam}
$$

を mass API 名で参照できる状態になっておる。これはまさに計画書の最初の到達目標じゃ。

### 3.2. Phase B. Branch / SubConservative API

ここも **最小核として完了** じゃ。
`Branching`, `outgoingMass`, `SubConservative`, `outgoingMass_le_mass`, `branch_sum_le_parent` が入り、「子の総質量は親を超えない」という骨格は立った。
ただし、設計図の大きい版にあった `Tromino2D` を concrete 教材として接続する段は今回は保留じゃから、**抽象 API は閉じたが教材層は未着手** という判定が正確じゃ。

### 3.3. Phase C. Primitive / GN / valuation の接続

ここも **最小 spine は完了**。
primitive witness から

* `Nat.Prime q`
* `q ∣ a^d - b^d`
* boundary 側は 0
* diff load は beam load に移る
* squarefree beam なら局所 load は高々 1

という線が揃った。さらに二本 witness 版、`Finset` family 版、`PrimitiveWitnessFamily` package 版へと持ち上がっておる。これは、当初計画よりむしろ一段整理が進んだ部分じゃ。

### 3.4. Phase D. ABC bridge

ここは **想定以上に進んだ** と言ってよい。
単に `rad` や `padicValNat` の薄い橋を置いただけでなく、

$$
\text{supportMass} = \operatorname{rad}
$$

を軸に、

* prime channel 版の下界
* primitive witness 版の下界
* family 版の下界
* package 版の下界

までそろっておる。
最初の plan では「translation layer に徹する」段階じゃったが、実際には **translation layer の中で lower-bound spine がかなり育っている**。ここは新しい進展じゃな。

### 3.5. Phase E. 例と public import

ここも **完了** と見てよい。
concrete example は既に入り、さらに今回 snapshot では `ABC.Bridge` と `ABC.Main` 経由の公開導線まで整っておる。つまり「空抽象ではないか」の確認と、「外からどう使うか」の確認の両方が済んだ。

## 4. 今回の本当の新規性は何か

お主の問いにまっすぐ答えるなら、今回の新規性は **ABC パッケージそのものに新しい “橋の数学” が入ったこと** じゃ。

それは次の一本に要約できる。

$$
\text{primitive witness family}
\;\to\;
\text{diff 側の prime channel family}
\;\to\;
\text{supportMass lower bound}
$$

ここで `supportMass` は `rad` の別名として立っておるので、結局

$$
\text{primitive flow}
\;\to\;
\text{disjoint channels}
\;\to\;
\operatorname{rad}\text{ の下界}
$$

という読みにまで到達しておる。
これは、以前は「面白い見方」だったものが、今や Lean 上で theorem 名を持つ spine になった、という意味で確かな進展じゃ。

特に重要なのは、これは **ABC 本体の অসম式を直接証明したわけではない** が、ABC で一番使いたい量の一つである `rad` に対して、「異なる channel が増えると support mass が下から持ち上がる」という形を明示したことじゃ。
これにより、primitive prime の存在や分離が、単なる局所情報ではなく **global lower bound** に変換できるようになった。ここが今回の数学的収穫じゃな。

## 5. では、ABC 予想そのものに対して何が進んだのか

ここは冷静に切り分けるべきじゃ。

**進んだ。だが “本体不等式へ直撃” ではなく、“本体へ入るための中間レイヤが強くなった”** のじゃ。

つまり、

* `abc_big_eq_body_add_gap_mass`
* `abc_gap_mass_le_big_mass`
* `abc_residual_eq_gap_mass`
* `supportMass_ge_prod_of_prime_channel_family`
* `primitive_witness_family_force_supportMass_lower_bound`

のような補題は、ABC 側で **mass / support / primitive channel** を同じ言語で扱う準備をかなり整えた。

しかし一方で、既存 ABC 本丸の

* Janson–Suen 系
* bad set density 系
* mgf / measure 系
* `ABC021.lean` まわりの未完解析

そのものを今回閉じたわけではない。INDEX の現況でも `sorry` の集中は主に `ABC021.lean` など既存コア側に残っておる。だから、**ABC の主定理が一気に解決へ近づいた** と言うのはまだ早い。むしろ、

$$
\text{本丸へ入るための別ルート候補}
$$

がかなり整ってきた、という見方が正確じゃ。

## 6. 現況の評価

わっちの総合評価は、こうじゃ。

### 6.1. これは「準備」ではあるが、ただの準備ではない

単なる命名整理や import 整理だけで終わっておらぬ。
`supportMass = rad`、family lower bound、primitive witness family package までそろっておるので、**数学内容を持つ infrastructure** になっておる。

### 6.2. 進展の中心は ABC パッケージそのものではなく、その前段の橋

今回の主な実装場所は見かけ上 `ABC/*` じゃが、実質の心臓部は

* `CosmicFormula/Mass/*`
* `NumberTheory/ValuationFlow/*`

にある。
ABC パッケージには、それを読むための翻訳面と公開導線が入った。
ゆえに「ABC パッケージに何か新進展か」と問われれば、**yes。ただし本体ではなく bridge の進展** と答えるのが正しい。

### 6.3. 設計・実装計画に対する逸脱は少ない

今回の snapshot は、かなり計画どおりじゃ。
むしろ想定以上に進んだのは、two-channel 版で止まらず `Finset` family 版と package 版、さらに public import まで入った点じゃな。これは良い意味での前倒しじゃ。

## 7. これからか？ それとも、もう新段階か？

答えは **両方** じゃ。

もう新段階に入っておる。
なぜなら、いまや bridge は

* theorem 群
* examples
* family API
* package API
* public import

を全部持っておるからじゃ。これはもう設計メモではなく、利用できる層じゃ。

だが同時に、ABC 本丸から見ればまだ「これから」でもある。
次の本当に大事な分岐は二つある。

ひとつは、**この bridge 層をどの中間命題へ差し込むか**。
たとえば

$$
\text{primitive channel 数}
\;\Rightarrow\;
\operatorname{rad}(abc)\text{ 下界}
\;\Rightarrow\;
\text{quality や valuation の制約}
$$

という線を、既存 ABC コアのどこに噛ませるかを決める段じゃ。

もうひとつは、**確率質量保存 API の “確率” 側をどこまで実装するか**。
設計では exact な Markov / sub-Markov や `Λ(q)/\log n` kernel は後回しになっておったが、ここへ本当に進むなら `Hitting` 層や actual probabilistic layer を作る必要がある。そこはまだ未着手じゃ。

## 8. わっちの最終判断

現況を一言でまとめるぞい。

**今回の snapshot で、Erdős #1196 由来の mass / channel / support の考え方は、ABC 側で使える “公開 bridge API” として一段完成した。**
これは新しい進展じゃ。しかも単なる整理でなく、`rad` 下界と primitive witness family を結ぶ lower-bound spine まで入っておる。

ただし、**ABC 予想本体の重い未完核はまだ残っている**。
ゆえに「もう勝った」とは言えぬが、「別ルートの足場がかなり強くなった」とははっきり言える。今はちょうど、

$$
\text{橋を作り終え、どの城門に接続するかを選ぶ段階}
$$

じゃな。
