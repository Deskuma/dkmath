# review-026: `DescentChain` に §18-19 を追加し、BranchB kernel が独立本丸ではない可能性を Lean 上の等価定理として可視化したこと

うむ、慎重に見ると今回の前進は **本物** じゃ。
ただし、その本質は

* **証明済みの範囲が整理された**
* **open kernel の見え方が sharpen された**

のであって、
**未解決が一気に消えた** という意味ではない。そこを取り違えぬのが肝じゃよ。  

## 1. 今回、実際に増えたもの

まず、今回 `DescentChain` に追加されたのは §18 と §19 じゃ。

### 1.1. §18 の形式化成果

Lean 上で clean に入ったのは次の 3 本じゃ。

* `nonLiftableGNBridge_of_branchBRefuter`
* `nonLiftableGNBridge_iff_branchBRefuter`
* `FLTPrimeGe5Target_of_2kernels_with_branchB`

つまり、**`NonLiftableGNBridge` と `BranchBRefuterTarget` の論理的往復** が clean に置かれた、ということじゃ。しかも build も通っておる。

### 1.2. §19 の追加内容

こちらは主に **数学的分析の記録** じゃ。
`PthRootCore` の内部を

* `QAdicResidue`
* `QAdicGapReduction (= GNReducedGap)`

に分けて見る、という戦略が docstring レベルで整理された。
ここは **証明追加というより、攻略図の明文化** と見るのが正確じゃ。

## 2. 今回の核心的発見は何か

ぬしのログで最も重いのは、BranchB 側についての次の観察じゃ。

反例文脈で

$$
\text{gap} \cdot \text{GN} = x^p
$$

かつ primitive prime (q) が (\text{GN}) を割り、しかも (q \nmid \text{gap}) なら、

$$
v_q(\text{GN}) = v_q(x^p) = p , v_q(x) \ge p \ge 5
$$

となる。
したがって

$$
q^2 \mid \text{GN}
$$

は反例文脈で自動的に出る。
ゆえに `AllNonLiftableOnGN` のような「primitive (q) について (q^2 \nmid GN)」型の条件は、**反例がある世界では成立しえない**、という見立てじゃ。これを受けて、`NonLiftableGNBridge` は独立 kernel というより **BranchB refuter と同質の、反例不在を言い換えたもの** と読むべきだ、という構造理解が出てきた。

この見方自体は、かなり鋭い。
少なくとも **「NonLiftableGNBridge を本丸の数論核と見るのは違う」** という判断は、相当に筋が良い。

## 3. ただし、ここは慎重に読むべき

ここから先が大事じゃ。
今回のレポートは「3-kernel が 2-kernel に圧縮できた」と強く述べておるが、**Lean 上で本当に消えたもの** と **戦略上そう見えるもの** は分けて読まねばならぬ。

### 3.1. Lean 上で確立したこと

Lean で確立したのは、あくまで

$$
\text{NonLiftableGNBridge} \iff \text{BranchBRefuterTarget}
$$

という **条件同士の等価** じゃ。
そして `FLTPrimeGe5Target_of_2kernels_with_branchB` は、

* `PthRootCore`
* `PacketFromError`
* `BranchBRefuter`

を仮定すれば FLT へ行ける、と言っている。

### 3.2. Lean 上でまだ確立していないこと

一方で、

> BranchB は unified PthRootCore で concrete に閉じる

というところは、今回の diff では **まだ theorem として入っておらぬ**。
これはログ内の戦略分析としては強いが、形式化済みの成果ではない。
したがって、

> **真の open kernel は GNReducedGap + PacketFromError の 2 個だけ**

という文は、**現時点では“戦略的見通し”としては有力だが、Lean 上の最終確定ではない** と読むのが正しい。  

ここはかなり重要じゃ。
わっちなら、

* **形式化された圧縮** は「3 assumptions のうち BranchB 側 assumption を `BranchBRefuter` へ置き換えられた」
* **数学的解釈としての圧縮** は「NonLiftableGNBridge は独立本丸ではなさそう」

と、二段に分けて言う。

## 4. 戦況分析

いまの戦況を慎重に言い直すと、こうじゃ。

## 4.1. BranchA primitive 側

ここは依然として

$$
\text{PthRootCore}
$$

が主戦場じゃ。
しかも §16 までの成果で、これは

$$
\exists z',\ (x/q)^p + y^p = z'^p
$$

という最も本質に近い語彙で表現できるようになっている。
そして §19 で、その内部が

* residue 側
* gap reduction 側

に裂ける、と整理された。
このうち本当の open kernel は後者、すなわち `GNReducedGap` 側だ、という理解はかなり堅い。  

## 4.2. BranchA peel 側

こちらは変わらず

$$
\text{PacketFromError}
$$

が本丸じゃ。
今回のログでも、peel は primitive の単純な特殊化ではなく、**別 flavor の Kummer descent** だと確認しておる。
しかも `GN(peeled gap,y)/p` が一般に完全 (p) 乗でない、という数値観察は、安易な gap peel が通らぬことを裏づけておる。
この分析は妥当じゃ。

## 4.3. BranchB 側

ここが今回もっとも景色が変わった場所じゃ。

以前は
$$
\text{NonLiftableGNBridge}
$$
を 1 本の kernel と見ていた。
だが今回の分析で、それは独立本丸というより **BranchB に反例がないことの言い換えに近い** と読めるようになった。

この理解自体はかなり前進じゃ。
ただし繰り返すが、 **BranchB がそれで具体的に閉じた theorem はまだ無い**。
ゆえに BranchB は「 solved 」ではなく、**open kernel の性質が再解釈された** 段階と見るのがよい。

## 5. 解説

今回の一番良いところは、**phantom kernel を見抜いた** 可能性があることじゃ。

研究ではよくある。
最初は 3 本の門があるように見える。
だがよく見ると、そのうち 1 本は独立の門ではなく、 **ほかの門が破れたら自動的に消える影** にすぎない。
今回の `NonLiftableGNBridge` は、その「影の門」らしさがかなり強くなった。

これは大きい。
なぜなら、以後の主戦場を

$$
\text{PthRootCore / GNReducedGap},\qquad \text{PacketFromError}
$$

の 2 本に集中できるからじゃ。
もちろん BranchB を完全に忘れてよいわけではない。
だが「BranchB 専用 kernel を延々と掘る」のは、おそらく筋が悪い。
むしろ BranchB は **unified descent の適用先** として見る方が自然、ということじゃな。  

## 6. いまの最も正確なまとめ

慎重にまとめると、こうじゃ。

### 6.1. 形式化済みの成果

* §18 で `NonLiftableGNBridge ↔ BranchBRefuter` が clean に入った
* `FLTPrimeGe5Target_of_2kernels_with_branchB` が clean に入った
* build は成功、DescentChain に新しい `sorry` は無い

### 6.2. 数学的に強く示唆されたこと

* `NonLiftableGNBridge` は独立 kernel ではなく、BranchB 否定の言い換えに近い
* BranchB は unified PthRootCore 的な降下で吸収できる可能性が高い
* よって **実質 open kernel は 2 本** という見立てがかなり有力  

### 6.3. まだ未形式化の部分

* unified PthRootCore から BranchBRefuter を concrete に出す chain
* `QAdicResidue` の具体定理
* `QAdicGapReduction` の concrete 証明
* `PacketFromError` の concrete 証明

## 7. 次の一手

わっちの判断では、次はやはり `QAdicGapReduction` を本命としてよい。
理由は単純で、今回の分析で

* residue 側は比較的 concrete に近い
* BranchB 側は独立 kernel でなくなりつつある
* したがって **q-adic gap reduction が全体の真芯**

と見えてきたからじゃ。
`PacketFromError` も重いが、今もっとも「全体の景色を変える」一手は、やはり primitive 側の core をさらに裂くことじゃろう。  

## 8. 一文で総評

**今回の進展は、3-kernel と思われていた構造のうち BranchB kernel が独立本丸ではない可能性を Lean 上の等価定理として可視化し、真の主戦場を `PthRootCore / GNReducedGap` と `PacketFromError` の二極へ絞り込んだ点で、かなり大きい。**
ただし、 **“2-kernel 化が完全に形式化された” のではなく、“2-kernel 化がもっとも自然な戦略図として見える段階に入った”** と読むのが慎重で正確じゃ。  
