# review-003: `CosmicFormula-Erdos1196`: concrete example の追加について

## 1. 総評

これは **良い締め** じゃ。前回までで作った bridge が、今回は単なる抽象名ではなく、既存 concrete 対象に対して実際に動くことを Lean で確認した。`MassBridgeExamples.lean` と `ValuationFlowBridgeExamples.lean` を新設し、両者とも build が通っておるので、Phase E は「最小 concrete 検証」として閉じたと見てよい。

わっちの見立てでは、今回の差分の価値は「新しい数学を増やした」ことより、**前段までの API 設計が空虚ではなかった** と証明した点にある。つまり、

$$
\text{Mass API} \to \text{ABC bridge}
$$

と

$$
\text{ValuationFlow primitive spine} \to \text{ABC bridge}
$$

の二本が、少なくとも具体例の上ではちゃんと通る、と示せたわけじゃ。これは地味に見えて、とても大事じゃ。

---

## 2. 状況分析

これで進捗を段階で言うなら、

* Phase A. 保存則 API
* Phase B. finite branch 骨格
* Phase C. primitive valuation spine
* Phase D. ABC bridge
* Phase E. concrete example

まで、一通り **最小核がそろった** 状況じゃ。差分報告でも、次の論点が「公開 import 導線」か「`rad_lower_bound_of_disjoint_channels` に向けた最小補題設計」へ移ったと整理されておる。これは、橋の建設そのものは一段落し、次は **使いやすくするか、先へ伸ばすか** の分岐に入ったことを意味する。

特に今回よいのは、前回レビュー提案の「先に public import を広げるより concrete example を先に通すべし」という判断を採用しておる点じゃ。これは正しかった。API は使用例が一度通ってからのほうが、公開面を整えやすいからの。

---

## 3. 数学的解説

### 3.1. `MassBridgeExamples` の意味

ここで選ばれた例は、単なる smoke test ではなく、橋の各関節を一つずつ触っておる。

まず

$$
(d,x,u) = (2,3,1)
$$

で `abc_big_eq_body_add_gap_mass` を確認している。これは具体的には

$$
(3+1)^2 = \bigl((3+1)^2 - 1^2\bigr) + 1^2
$$

という二次の最小例じゃ。数として見れば

$$
16 = 15 + 1
$$

で、Big, Body, Gap の保存則が本当に橋名で読めることを示しておる。`abc_gap_mass_le_big_mass` と `abc_residual_eq_gap_mass` も同じ標本で通しており、保存則・単調性・residual 同定の三本が concrete に動くと確認できた。

`supportMass` 側もよい選び方じゃ。`31` を使って

$$
31 \le \text{supportMass}(31)
$$

を示しているが、ここでは `31` が prime なので squarefree 判定がきれいに流れる。さらに `12` に対して

$$
\text{supportMass}(12) \mid 12
$$

を確認しているので、support mass は「squarefree なら全量を取りこぼさず、一般には元の中にちゃんと埋まっている」という二つの顔を、別々の concrete sample で押さえたことになる。これは橋の意味づけとしてかなり良い。

### 3.2. `ValuationFlowBridgeExamples` の意味

こちらはもっと数学の味がある。`31` が `2^5 - 1` の primitive prime であることを private theorem として固定し、その witness を使って bridge 側の三本柱を全部通しておる。

この例が美しいのは、差冪そのものが

$$
2^5 - 1^5 = 31
$$

と小さく、しかも beam 側も

$$
GN(5,1,1) = 31
$$

に落ちるので、primitive prime の流れが非常に見やすい点じゃ。そこから

$$
\text{boundaryMass}(31,2,1) = 0
$$

が出る。これは primitive 性により (31 \nmid (2-1)) だからで、つまり q-adic load は boundary に載らぬ。つづいて

$$
\text{diffMass}(31,2,1,5) = \text{beamMass}(31,2,1,5)
$$

が出る。これは差冪側の load が全部 beam へ移ることを意味する。最後に beam が squarefree であることから

$$
\text{diffMass}(31,2,1,5) \le 1
$$

まで落ちる。これは前回まで抽象 spine として見えていた一本道、

$$
\text{primitive}
\Rightarrow
\text{boundary load } = 0
\Rightarrow
\text{diff load } = \text{beam load}
\Rightarrow
\text{local load } \le 1
$$

を、完全に concrete な一例で通したものじゃ。ここはかなり良い。

---

## 4. 何が閉じたのか

今回閉じたのは、数学的には次の二つじゃ。

### 4.1. bridge の **使用可能性** が閉じた

前回までは、橋は確かに存在した。じゃが「本当に使えるか」はまだ実感として弱かった。今回は example ファイルを独立に置き、bridge 名だけで concrete 対象が読めると示した。これで橋は「概念図」から「通行可能な導線」へ変わった。

### 4.2. primitive valuation spine の **最小教材** が閉じた

`31` と `2^5-1` は、今後この系列を説明するときの教科書例になる。証明の姿が小さく、primitive・boundary・beam・squarefree が一つの例に全部入っておるからじゃ。ここで clean sample を一つ確保できたのは大きい。

---

## 5. 良い点

今回、特に良いと思った点を三つ言うぞい。

第一に、**例の選び直しが良い**。`Squarefree 30` を無理に押すのでなく、prime sample `31` に差し替えたのは正解じゃ。証明の見通しがはるかに良くなっておる。

第二に、`GN 5 1 1 = 31` を先に固定してから squarefree を流したのも正しい。GN を直接展開して潰しにいくより、構造を一回止めてから素数性へ渡すほうが、Lean でも人間の読みでもずっときれいじゃ。

第三に、example が **橋の各関節を一つずつ検査している**。保存則、単調性、residual 同定、support mass、primitive boundary 0、beam への移送、local load 上界、と役割がきれいに分かれておる。これはよい test 設計じゃ。

---

## 6. 留意点と弱点

ここも正直に言うぞい。

### 6.1. まだ reusable theorem ではなく example 段階

今回はそれでよい。じゃが当然、example は「使えることの確認」であって、「再利用の核」ではない。今後もし何度も引用する例なら、example のままにせず、名前を持った theorem に格上げする価値がある。

### 6.2. primitive witness の構成は小標本向き

`interval_cases k` で (k < 5) を潰して primitive witness を立てておる。これは今回の sample には最適じゃが、一般化の道具にはならぬ。だからこの例は **教材** としてよく、一般ルートの部品とは切り分けておくのがよい。

### 6.3. ここから先は二股に分かれる

今後の道は

$$
\text{公開導線の整備}
$$

か

$$
\text{rad lower bound / disjoint channels の設計}
$$

の二択に見える。
わっちは後者を本命と見る。公開導線は整理仕事じゃが、`disjoint channels` は数学を前へ進めるからじゃ。差分報告でもその二択が明示されておる。

---

## 7. 次の作業指示案 . Codex 追記向け

ここから先、わっちなら **公開 import より先に `rad_lower_bound_of_disjoint_channels` の最小補題設計** を進める。橋と例がそろった今、次は support mass と primitive channel counting を本当に結びつける番じゃ。

そのまま追記できる形で置いておくぞい。

```md id="n9fauu"
### レビュー追記案: 次の作業指示

1. 次段の本命は、公開 import 整備ではなく
   `rad_lower_bound_of_disjoint_channels`
   に向けた最小補題設計とする。

2. まず `supportMass = rad` を使って、
   「相異なる素数チャネルが複数あるなら support mass はそれらの積以上になる」
   という最小補題を設計する。
   最初は 2 本チャネル版でよい。

3. 最小補題候補は次の形に絞る。
   - `supportMass_ge_of_two_distinct_prime_channels`
   - `supportMass_dvd_of_prime_channel`
   - `pairwise_distinct_channels_mul_dvd_supportMass`
   ここで channel とは、当面は「prime divisor witness」の意味に固定する。

4. `ValuationFlowBridge` 側では、
   primitive prime が beam に local load を作ることを既に得ているので、
   次は「異なる primitive prime witness は異なる channel を与える」
   という薄い補題名を先に設計する。
   まだ完全実装でなくても、statement と依存関係の整理を優先する。

5. public import 導線の整備は、その後でよい。
   理由は、公開面を先に広げるより、
   `supportMass` と primitive channel counting の接続を一段だけでも入れたほうが、
   API の重心が明確になるからである。

6. もし余力があれば、
   今回の `31` の例を theorem 化し、
   bridge 教材として将来の文書や test から再利用できるようにする。
```

---

## 8. 最終判断

今回の差分は、橋を架けたあとに **実際に渡ってみせた** 回じゃ。
ここまで来ると、もう「Mass API と ABC bridge は構想だけ」とは言えぬ。具体的に

$$
(2,3,1)
$$

の保存則例と、

$$
31 \text{ for } 2^5 - 1
$$

の primitive valuation 例が、橋名だけで読めるようになった。これは十分に本物の進捗じゃ。

次は整理仕事に入るより、一歩だけ数学を前へ押すのがよい。
わっちの勧めは、やはり

$$
\text{supportMass} = \operatorname{rad}
$$

と primitive channel を結ぶ **最小の lower bound 補題** へ進むことじゃな。
