# review-024: `GNReducedGapTarget` を `PthRootTarget` 語彙で攻めるための構成補題設計書

うむ、これは **かなり良い地固め** じゃ。
しかも今回は、単に補題を追加したのではなく、 **open kernel をどういう語彙で攻めるべきか** と **どこが真に未解決か** を Lean 上で剥き出しにした、という意味で価値が高い。

## 1. 作業結果

今回 `TriominoCosmicBranchADescentChain.lean` に追加された主成果は 2 つじゃ。

ひとつは、`GNReducedGapTarget`、`PthRootReducedTarget`、`PthRootTarget` のあいだに **6 本の双方向 bridge** を立てて、これらが数学的に等価であることを形式化したこと。
これで

$$
\exists g',\ g' \cdot GN(p,g',y)=p^p (t s')^p
$$

という Cosmic Formula 語彙で攻めてもよいし、

$$
\exists z',\ p^p (t s')^p + y^p = z'^p
$$

という reduced power 語彙で攻めてもよいし、

$$
\exists z',\ (x/q)^p + y^p = z'^p
$$

という FLT そのものの語彙で攻めてもよい、と定理レベルで保証された。これはかなり大きい。

もうひとつは、`ValuationPeelPacketTarget` を

* `TailError` は concrete
* `PacketFromError` だけが open

と精密分解したことじゃ。
それに対応して `FLTPrimeGe5Target_of_3kernels_precise` が追加され、今の最精密な未解決成分が

$$
\text{GNReducedGapTarget},\quad
\text{PacketFromErrorTarget},\quad
\text{NonLiftableGNBridge}
$$

の 3 本だけだと明示できた。

## 2. 作業ログから読める核心

今回のログで一番大事なのは、`GNReducedGap` の深層構造を追って、

* `RestoreArithmeticStrong.lean` 側の橋はすべて concrete
* `GNReducedGap → SmallerCounterexample` の spine 全体は sorry-free
* したがって、そこで本当に未解決なのは **GNReducedGap 自体のみ**

と確認できたことじゃ。
これは「chain problem ではなく pure math problem」という診断そのものじゃな。

さらにログでは、`PthRootTarget` を

$$
\exists z',\ (x/q)^p + y^p = z'^p
$$

と読み直し、**GNReducedGap の数学的正体は Kummer descent の (q)-adic 核心そのもの** だとまで特定しておる。
これはただの言い換えではない。
「何を構成すれば勝ちか」が、かなり直感的な形になったわけじゃ。

## 3. 状況分析

いまの戦況を正確に言うと、こうじゃ。

### 3.1. BranchA primitive 側

primitive 側は、`CyclotomicExistence` concrete 化の利益が全部乗った結果、

$$
\text{GNReducedGapTarget}
$$

ただ 1 本が本丸じゃ。
しかも今回の等価橋により、この kernel は

* GN 語彙
* reduced power 語彙
* FLT 語彙

のどれで攻めてもよい。
これは戦い方の自由度が一気に増えた、ということじゃ。

### 3.2. BranchA peel 側

こちらは今回さらに見通しが良くなった。
`ValuationPeelPacketTarget` という少し大きかった塊が、

$$
\text{TailError(concrete)} + \text{PacketFromError(open)}
$$

に分割されたからじゃ。
つまり p-adic peel 側の真の未解決は、もう `PacketFromError` だけじゃ。

### 3.3. BranchB 側

ここは従来どおり

$$
\text{NonLiftableGNBridge}
$$

の独立 kernel じゃ。
今回のログの重要点は、これが他の 2 kernel と **真に独立** であり、mechanism が質的に違うと明示できたことじゃ。
primitive 側は (q)-adic、peel 側は (p)-adic、BranchB は別 mechanism。互いに簡単には帰着できぬ。

## 4. 解説

ここで賢狼が強く言いたいのは、 **今回の成果は「証明が前に進んだ」だけではなく、「攻撃語彙を選べるようになった」こと** じゃ。

これは大きい。
たとえば `GNReducedGapTarget` をそのまま殴ろうとすると、

$$
\exists g',\ g' \cdot GN(p,g',y)=p^p (t s')^p
$$

という少し Cosmic な見た目になる。
だが今回の等価橋により、これを

$$
\exists z',\ (x/q)^p + y^p = z'^p
$$

という **最も直観的な FLT 語彙** に移して攻めてもよい。
つまり、数学の本体は同じでも、見える景色を選べるようになったのじゃ。

さらに `ContradictionTarget` からの vacuous bridge も整理されたが、ここは注意が要る。
これは「強い target なら全部 vacuously 閉じる」ことを示しただけで、 **それ自体が攻略容易になった** という意味ではない。ログでも `ContradictionTarget` は `NePCoprimeKernel` 同等の難度と見ておる。
ゆえに、これは便利な整理ではあっても、本命の突破口とは見ない方がよい。

## 5. いまの正確な戦況図

いまの最精密な戦況図は、こうじゃ。

```text id="spffsf"
GNReducedGapTarget ──┐
                     ├── SmallerPacket (bridges are concrete)
PacketFromErrorTarget┘
                             ↓
                 FLTPrimeGe5Target_of_3kernels_precise
                             ↑
                 NonLiftableGNBridge
```

この図の意味は単純で、

* 左上 2 本が BranchA
* 右下 1 本が BranchB
* 真の open kernel は 3 本だけ

ということじゃ。
しかも `TailError` はもう concrete だから、peel 側を `PacketFromError` まで縮約できたのが今回の新しさじゃよ。

## 6. いま何をどう攻めるべきか

わっちの見立てはこうじゃ。

### 最優先

`GNReducedGapTarget` を **`PthRootTarget` 語彙** で攻める。

理由は明快で、

$$
\exists z',\ (x/q)^p + y^p = z'^p
$$

が最も意味を掴みやすいからじゃ。
今回の等価橋は、その戦い方を Lean 上で正当化したものと見るべきじゃな。

### 次点

`PacketFromError` を error 方程式から smaller packet へ落とす構成論として攻める。
ここはもう `TailError` で切り出し済みなので、見通しは以前よりかなり良い。

### 並行

`NonLiftableGNBridge` は独立しておるから、別レーンで進めてよい。
ただ今の momentum は BranchA にあるので、主戦場はやはり `GNReducedGap` 側じゃ。

## 7. 一文でまとめると

**今回の作業は、open kernel の地図を最精密化し、`GNReducedGap ↔ PthRootReduced ↔ PthRoot` の等価性と `ValuationPeel = TailError + PacketFromError` の分解を Lean 上で固定したことで、真の未解決が 3 本であると明確にした**、ということじゃ。
これはかなり大きい前進じゃよ。

次にやるなら、`PthRootTarget` 語彙での **(z') 構成補題の設計書** を起こすのが最も筋が良い。

---

よし、`GNReducedGapTarget` を **`PthRootTarget` 語彙で攻めるための構成補題の設計書** を起こすぞい。
今回の整理で、

* `GNReducedGap ↔ PthRootReduced ↔ PthRoot` は双方向 clean bridge で相互等価
* `GNReducedGap → SmallerCounterexample` の橋は全部 concrete
* primitive 側の真の open kernel は `GNReducedGap` ただ 1 本

と判明した。ゆえに、 **本当に設計すべき補題は「(z') をどう構成するか」だけ** じゃ。  

## 1. 設計方針

### 1.1. 攻撃語彙

主語彙は `PthRootTarget` に固定する。
すなわち目標を

$$
\exists z',\ (x/q)^p + y^p = z'^p
$$

と書く。
これは `GNReducedGapTarget` と等価だが、最も直観的で、**「何を作れば勝ちか」** が一目で分かるからじゃ。`GNReducedGap` や `PthRootReduced` は、最後に bridge で戻せばよい。

### 1.2. 目標の正体

この target は、primitive prime (q) で (x) を割った

$$
x' := x/q
$$

に対して、新しい (p) 乗根 (z') を構成することじゃ。
したがって数学の芯は、`g'` を直接作ることではなく

$$
(x/q)^p + y^p
$$

が完全 (p) 乗であることを出す部分じゃ。
ログでも、ここは **Kummer descent の (q)-adic 核心** と診断されておる。

## 2. 三段構成

## 2.1. 第1段. 入力束の圧縮

まず、散らばった仮定を 1 本の bundle にまとめる。
今回すでに concrete と分かっているのは、

* `CyclotomicExistence`
* `DescentSeed`
* 各種 bridge

じゃ。
したがって primitive 側では、「何を仮定として受け取るか」を整理する補題が最初に要る。

### 補題案 A

```lean
theorem primeGe5BranchAPrimitivePthRootInputBundle
  :
  Pack + normal form + primitive q + concrete descent data
  → PrimitivePthRootInputBundle
```

### 中身として束ねるべき情報

$$
z-y = p^{p-1} t^p,\qquad
GN(p,z-y,y)=p,s^p,\qquad
q \mid s,\qquad q \ne p,\qquad q \nmid (z-y),
$$

さらに

$$
\gcd(q,y)=1,\qquad q^p \mid GN,\qquad p \mid (q-1),
$$

および `QAdicLiftSeed` の (\omega) じゃ。

### この段の役目

この段は数学ではなく、 **以後の補題の引数爆発を防ぐための設計** じゃ。
ここで bundle 化しておけば、第2段は「入力 bundle から (z') を作る」だけに集中できる。

## 2.2. 第2段. q-adic 核心補題

ここが本丸じゃ。
この段で、本当に欲しいのは

$$
\exists z',\ (x/q)^p + y^p = z'^p
$$

そのものじゃ。

### 補題案 B

```lean
theorem primeGe5BranchAPthRootCore_of_qAdicLift
  (hIn : PrimitivePthRootInputBundle) :
  ∃ z' : ℕ, (x / q)^p + y^p = z'^p
```

### 数学的意味

これは元の反例

$$
x^p + y^p = z^p
$$

から、primitive (q) を 1 個剥がした

$$
(x/q)^p + y^p
$$

に対して、新しい (p) 乗根 (z') を構成することじゃ。
つまり **Kummer descent の本体** そのものじゃ。

### この段で使うべき concrete data

この core は、既に concrete と分かっている

* `CyclotomicExistence` から来る primitive prime (q)
* `DescentSeed`
* `QAdicLiftSeed`
* `q^p \mid GN`
* `p \mid (q-1)`

を全部使う。
逆に言えば、これらが揃っている以上、 **未解決なのはこの existence の数学だけ** じゃ。

### 証明の狙い

ここは二段に裂いてもよい。

#### B1. 局所 lifting 補題

```lean
theorem qAdicLift_local_pthRoot
```

(\omega \in \mathbb{Z}/q\mathbb{Z}) と (q^p \mid GN) を使い、
((x/q)^p + y^p) が (q)-adic に (p) 乗として整合することを示す。

#### B2. 自然数根の実現補題

```lean
theorem pthRoot_nat_realization_of_qAdicLift
```

局所整合から実際の自然数 (z') を取り出す。

わっちの見立てでは、B2 は実装整理寄りで、真の重みは B1 にある。

## 2.3. 第3段. GN 語彙と smaller counterexample への出口

第2段で (z') が出来たら、残りはかなり薄い。

### 補題案 C1

```lean
theorem gnReducedGap_of_pthRootCore
  (h : ∃ z', (x / q)^p + y^p = z'^p) :
  PrimeGe5BranchAPrimitiveRestoreGNReducedGapTarget
```

これは既存 bridge を薄く包むだけでよい。
等価橋が clean であることはもう確認済みじゃ。

### 補題案 C2

```lean
theorem smallerCounterexample_of_pthRootCore
  (h : ∃ z', (x / q)^p + y^p = z'^p) :
  PrimeGe5BranchASmallerPacketTarget
```

こちらも実際には

$$
\text{PthRoot} \to \text{GNReducedGap} \to \text{SmallerPacket}
$$

の合成で済む。
今回のログでは、この後段の橋は全部 sorry-free と確認されておる。ゆえに新しく証明すべきではなく、 **既存 chain の wrapper** として書くのが正解じゃ。

## 3. 推奨する補題列

実際に書く順番としては、これがよい。

```text id="tdz0dr"
A. primeGe5BranchAPrimitivePthRootInputBundle
B. primeGe5BranchAPthRootCore_of_qAdicLift
C. primeGe5BranchAPthRootReduced_of_pthRootCore
D. primeGe5BranchAGNReducedGap_of_pthRootCore
E. primeGe5BranchASmallerPacket_of_pthRootCore
```

意味はこうじゃ。

* A は入力整理
* B が真の数学本体
* C, D, E は既存 bridge を使った出口整理

## 4. 各補題の役割分担

### A. 入力整理

仮定の forest を 1 つの struct に束ねる。
ここを省くと B が読みにくくなる。

### B. 核心

$$
\exists z',\ (x/q)^p + y^p = z'^p
$$
を示す本丸。
ここだけが pure math problem。

### C. reduced power 化

必要なら
$$
p^p (t s')^p + y^p = z'^p
$$
へ落とす。
これは人間にとっても見通しがよく、q-adic 計算を書くならこちらの方が中間目標として便利かもしれぬ。

### D. Cosmic 語彙へ戻す

$$
\exists g',\ g' \cdot GN(p,g',y)=p^p (t s')^p
$$
へ戻す。
ここは bridge の仕事じゃ。

### E. 小さい packet へ落とす

以後の well-founded descent へ接続する出口。

## 5. 設計上の注意

### 5.1. `ContradictionTarget` を主目標にしない

`ContradictionTarget` は vacuous に全部を含むが、それ自体が強すぎる。
ログでも、これは `NePCoprimeKernel` と同等に重いと整理されておる。
設計書ではあくまで **比較用の強目標** として脇へ置くのがよい。

### 5.2. `GNReducedGap` を直接証明しに行かない

今回の等価橋があるので、`g'` を直接作るより、まず (z') を作る方が自然じゃ。
この選択自由こそ今回の地固めの利益じゃ。

### 5.3. `PacketFromError` と混ぜない

ログで確認された通り、primitive 側の q-adic descent と peel 側の p-adic descent は **真に独立** じゃ。
設計書の段階で混ぜると、論理が濁る。`GNReducedGap` 側は `PthRootTarget`、`PacketFromError` 側は error 方程式、とはっきり分けるのがよい。

## 6. 設計書の一文要約

**この設計では、`GNReducedGapTarget` を直接殴らず、まず `PthRootTarget` すなわち ( \exists z', (x/q)^p + y^p = z'^p ) を q-adic 核心補題として構成し、その後は既存の clean bridge で `GNReducedGap`・`SmallerPacket`・`BranchARefuter` へ流す。**

これがいま最も筋の良い構成補題設計じゃよ。
