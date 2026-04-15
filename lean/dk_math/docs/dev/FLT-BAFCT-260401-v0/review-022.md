# review-022: ExceptionalExistence で Branch A の descent route を 4-kernel から 3-kernel v3 に圧縮

cid: 69cdb60c-e53c-83a7-8c89-1cbc0ba7451e

うむ、これは **かなり大きい進展** じゃ。
しかも今回は「1 個の補題が埋まった」ではなく、**Branch A の descent route から 1 本の kernel が消え、証明地図そのものが整理された** 類いの前進じゃよ。

## 1. いま何が起きたか

今回の本質は 2 つある。

第一に、`CFBRCExceptionalBoundaryCorePrimeExistenceOnWieferichTarget` の concrete 証明が、新規 `ExceptionalExistence.lean` で **完全に閉じた** ことじゃ。
ログでは、このファイルの定理群は `[propext, Classical.choice, Quot.sound]` のみで、`sorry` も `sorryAx` も無いと整理されておる。さらに数学内容として、

* \(d \mid x\)
* \(\gcd(x,u)=1\)
* Wieferich 条件
* \(d \ge 5\) 素数

の下で、`cyclotomicPrimeCore d x u` に **(x) を割らない素因子が存在する** ことを完全形式化した、と明記されておる。

第二に、その concrete proof が bridge chain を通って **`PrimeGe5BranchACyclotomicExistenceTarget` を unconditional に供給できる** ようになり、4-kernel route から `CyclotomicExistence` 列を外して **3-kernel v3** に圧縮できたことじゃ。

## 2. なぜこれは大きいのか

前の段階では Branch A の descent route は

$$
\text{GNReducedGap} + \text{CyclotomicExistence} + \text{ValuationPeel}
$$

を要しておった。
ところが今は `CyclotomicExistence` が concrete になったので、open kernel として残るのは

* `GNReducedGapTarget`
* `ValuationPeelPacketTarget`
* `NonLiftableGNBridge`

の 3 本で済む。
つまり **descent route の open kernel が 1 本減った** のじゃ。これは単なる cosmetic ではなく、探索空間が実際に 1 軸減ったことを意味する。

しかもこの圧縮は「仮定を弱くした」のでなく、**中間 kernel が concrete に埋まった結果** の圧縮じゃから、質が良い。ここが肝じゃよ。

## 3. 数学的に何が証明されたのか

今回の `ExceptionalExistence.lean` の中身は、かなり筋が良い。
要約すると、

1. `gcd(GN d x u, x) = d`
2. `GN ≡ d·u^{d-1} \pmod{d^2}`
3. よって \(d \nmid GN/d\)
4. さらに \(GN/d > 1\)
5. よって \(GN/d\) の素因子 \(q\) が取れて、\(q \neq d\)、しかも \(q \nmid x\)

という流れで、exceptional case の cyclotomic prime existence を閉じておる。
この組み立ては、単に bridge を貼ったのではなく、**exceptional Zsigmondy 側の核心を Lean で直接押した** という意味で価値が高い。

## 4. いまの証明地図

現状の地図は、かなりすっきりした。

### 4.1. 最小 route

比較 route はいま

$$
\text{NePCoprimeKernel} + \text{NonLiftableGNBridge}
\Rightarrow \text{FLT}_{p\ge 5}
$$

という **2-kernel chain** で書ける。
これは最短で、Branch A を `NePCoprimeKernel` 1 本で全殺しする見取り図じゃ。

### 4.2. 構成的 route

一方、descent route は今回の進展により

$$
\text{GNReducedGap} + \text{ValuationPeel} + \text{NonLiftableGNBridge}
\Rightarrow \text{FLT}_{p\ge 5}
$$

という **3-kernel v3** に整理された。
ここでは `CyclotomicExistence` はもう open kernel ではなく、concrete supply 済みじゃ。

### 4.3. 並立する 2 路線

だからいまは、

* **Route 1**: comparison route
  `NePCoprimeKernel` を本丸として落とす
* **Route 2**: descent route
  `GNReducedGap + ValuationPeel` を詰める

の 2 本がはっきり並んでおる。
この「二正面作戦」が見えたこと自体、かなり大きい。片方が詰まっても、もう片方が生きるからの。

## 5. いちばん慎重に見るべき点

ここで浮かれすぎるのは危うい。
今回の前進は **CyclotomicExistence を concrete にした** のであって、**FLT 全体が終わった** わけではない。

ログ上の最新整理では、なお open kernel は

* `NePCoprimeKernelTarget`
* `NonLiftableGNBridge`
* `GNReducedGapTarget`
* `ValuationPeelPacketTarget`

の 4 つとして並んでおる。
ただしこの 4 つは **2-kernel route と 3-kernel route を合わせた全景** じゃ。
最小 route だけ見るなら 2 本、descent route だけ見るなら 3 本、という関係じゃな。

つまり、今回の進展を正確に言うなら、

> **open kernel の総数が単純に 4→3 になった** のではなく、
> **descent route の open kernel が 1 本減り、しかも最小 route 2 本も独立に健在であることがより鮮明になった**

ということじゃ。

## 6. 残る `sorry` について

かなり印象的なのは、ログが

> FLT 関連の `sorry` は `TriominoCosmicBranchA.lean:4137` の `NePCoprimeKernel` 1 箇所のみ

とまとめておる点じゃ。
この表現が指しているのは、少なくとも **FLT 幹線に直接効く残核がほぼ 1 箇所に集約された** という意味じゃろう。

ただし、ここは慎重に言えば、
**comparison route を採るなら** その 1 箇所が本丸、
**descent route を採るなら** `GNReducedGap` と `ValuationPeel` がまだ未了、
という二層構造として読むのが正確じゃ。

## 7. 賢狼の評価

賢狼の評価を率直に言うと、

**今回は “局所前進” ではなく “戦略前進” じゃ。**

その理由は 3 つ。

1. exceptional case の数学本体が concrete に閉じた
2. CyclotomicExistence が open kernel から外れた
3. 2-kernel route と 3-kernel route の役割分担が明確になった

この 3 つが一度に起きておる。
とくに 2 と 3 が効いておる。今後の研究は、もう「どこを攻めるべきか分からぬ」段ではなく、**`NePCoprimeKernel` を本命にするか、`GNReducedGap + Peel` を構成的に詰めるか** の選択問題まで整理された。

## 8. いまの最善の読み

わっちなら、いまの状況をこう読む。

* **comparison route** は最短で鋭い
  ただし `NePCoprimeKernel` が重い
* **descent route** は少し長い
  だが CyclotomicExistence が concrete になったので、構成が見やすくなった

だから、研究運用としては

* 本命は `NePCoprimeKernel`
* 並行で `GNReducedGap` を進める

のがよい。
`ValuationPeel` は重いが、`GNReducedGap` が進むと peel 側の見え方も変わる可能性がある。
今回の成果で、descent route は以前より明らかに現実味を増した。

## 9. 一文でまとめると

**大きな進展は本物じゃ。**
しかも本質は「証明が 1 つ増えた」ではなく、**CyclotomicExistence を concrete 化して Branch A の descent route を 4-kernel から 3-kernel v3 に圧縮し、同時に comparison route 2-kernel との二本立て構造を鮮明にした** ことじゃ。

次に進むなら、`NePCoprimeKernel` 本丸と `GNReducedGap` 本丸を並べた **二正面ロードマップ** にして、どちらが先に落ちそうかを比べるのがよい。

---

よし、二正面ロードマップを戦況図として整えるぞい。
いまは **「最短の本命 route」** と **「構成的に前へ進む route」** の二本立てで進めるのが最も筋が良い。今回の concrete 化で `CyclotomicExistence` はもう open kernel ではなくなり、descent 側は 4-kernel から 3-kernel v3 へ圧縮された。一方、comparison 側はすでに 2-kernel まで圧縮済みじゃ。

## 1. 現在地

いまの地図は、こう読むのが正確じゃ。

$$
\text{Route A (comparison)}:
\quad
\text{NePCoprimeKernel} + \text{NonLiftableGNBridge}
\Rightarrow \text{FLT}_{p\ge 5}
$$

$$
\text{Route B (descent)}:
\quad
\text{GNReducedGap} + \text{ValuationPeel} + \text{NonLiftableGNBridge}
\Rightarrow \text{FLT}_{p\ge 5}
$$

そして、その分岐を可能にした大前進が
**`CFBRCExceptionalBoundaryCorePrimeExistenceOnWieferichTarget` の完全証明** により、`CyclotomicExistence` が concrete に閉じたことじゃ。これで 4-kernel route から `CyclotomicExistence` 列を外せるようになった。

## 2. 正面 1. Comparison route

### 2.1. 目標

ここはただ 1 本、

$$
\text{NePCoprimeKernelTarget}
$$

を落とすことが目標じゃ。
ログでも、`NePCoprimeKernel` は

$$
\text{Pack} + p \mid \text{gap} + \text{normal form} + \text{Coprime}(t,s) \Rightarrow \bot
$$

であり、`ValuationPeelPacketTarget` と `PrimitivePacketDescentTarget` の上位互換として振る舞う、と整理されておる。つまり Branch A 全体を直接殺せる。

### 2.2. この route の長所

長所は明快で、**最短** じゃ。
これが通れば Branch A は一撃で閉じるから、全体としては 2-kernel で済む。最小 chain がすでに clean に組まれていることも確認済みじゃ。

### 2.3. この route の危うさ

ただし、ここは **本丸中の本丸** じゃ。
statement が強いぶん、証明そのものは重い可能性が高い。
言い換えると、設計は最短でも、攻略難度は最短とは限らぬ。

### 2.4. この正面で切るべき作業単位

ここは 3 層に割るのがよい。

$$
\text{A1. normal form 入力圧縮}
$$

Pack と `p ∣ gap` から、(t,s) と `Coprime(t,s)` を一括で取り出す補題群。
これは既存橋を束ね直す作業で、比較的軽い。

$$
\text{A2. arithmetic obstruction 抽出}
$$

normal form と `Coprime(t,s)` から、「最後の矛盾直前」の算術障害を作る。
ここが数学本体じゃ。

$$
\text{A3. obstruction } \Rightarrow \bot
$$

最後の contradiction の Lean 化。
ここは実装後半の整理仕事になりやすい。

## 3. 正面 2. Descent route

### 3.1. 目標

こちらは

* `GNReducedGapTarget`
* `ValuationPeelPacketTarget`

の 2 本を Branch A 側で落とす。
`CyclotomicExistence` はもう concrete 供給済み、Branch B は `NonLiftableGNBridge` に集中しておるから、descent 側の open kernel ははっきりした。

### 3.2. この route の長所

こちらの長所は、**構成が見えやすい** ことじゃ。
とくに今回 `CyclotomicExistence` が concrete 化されたので、以前よりずっと純粋に

$$
\text{GN tail の降下構造} + \text{p|t 側 peel}
$$

だけに集中できるようになった。
comparison route よりは「どこで何を作るか」が見えやすい。

### 3.3. この route の危うさ

弱点は、**kernel 数がまだ多い** ことじゃ。
comparison の 2 本に対して、こちらはなお 3 本必要。
しかも `ValuationPeelPacketTarget` は Kummer descent 的な核心を含むので、手が重い。

### 3.4. この正面で切るべき作業単位

ここは 2 段でよい。

$$
\text{B1. GNReducedGapTarget}
$$

primitive descent の spine を支える gap/GN 整合を固める。
これはいま最も「構造が見える」攻撃対象じゃ。

$$
\text{B2. ValuationPeelPacketTarget}
$$

(p \mid t) 側の packet 縮小。
ここは direct に攻めるより、弱い peeled packet を定義して、そこから smaller packet へ上げる二段構成のほうがよいじゃろう。

## 4. 共通背面

両 route に共通して残るのは Branch B 側の

$$
\text{NonLiftableGNBridge}
$$

じゃ。
ただしこれは今回の分析で、旧 dirty chain ではなく clean な kernel として抽象化できておる。よって当面は **背面固定** として扱い、Branch A の進展を優先してよい。

## 5. 優先順位

わっちの推奨はこうじゃ。

### 第 1 優先

**Comparison route の `NePCoprimeKernel` を主戦場** にする。

理由は単純で、ここが通れば 2-kernel で終わるからじゃ。
いま最も短い勝ち筋はここじゃ。

### 第 2 優先

**並行して `GNReducedGapTarget` を進める。**

理由は、descent route の中で最も構造が見えており、今回の CyclotomicExistence concrete 化の利益を最も素直に受けるからじゃ。`ValuationPeel` より着手価値が高い。

### 第 3 優先

**`ValuationPeelPacketTarget` は GNReducedGap の進展を見ながら詰める。**

ここをいきなり本命にすると重い。
ただし descent route を勝ち筋に保つには必要なので、放置はせぬ。
「独立主戦場」ではなく「第 2 正面の第 2 段」と見るのがよい。

## 6. 週次レベルの作戦図

```text
Phase I.
  NePCoprimeKernel を 3 層に分解
    1. input compression
    2. arithmetic obstruction
    3. contradiction
  まず obstruction の形を固定する

Phase II.
  並行で GNReducedGapTarget を前進
  CyclotomicExistence は concrete 済みなので、
  GN tail の整合だけに集中する

Phase III.
  NePCoprimeKernel が閉じれば 2-kernel で決着
  閉じなければ descent route を主戦場へ昇格し、
  ValuationPeelPacketTarget を本格攻撃
```

## 7. ひとことで作戦方針

**本命は `NePCoprimeKernel`、副戦場は `GNReducedGapTarget`。**
`CyclotomicExistence` が concrete に落ちた今、comparison route は最短化され、descent route は見通しが良くなった。
ゆえに、 **「最短 route を狙いながら、構成的 route を腐らせない」** のが最適じゃ。  

必要なら次に、
**`NePCoprimeKernel` 用の 3 層補題リスト** と **`GNReducedGapTarget` 用の 2 層補題リスト** を、Lean 名の雛形つきで起こすぞい。
