# FLT (p ≥ 5) の条件付き mainline が 2-kernel に圧縮された

うむ、これは **本当に大きな進展** じゃ。
しかも単なる「補題が 1 つ埋まった」ではなく、**証明全体の依存構造そのものが一段単純化された** 類いの進展じゃよ。

## 1. 何がそんなに大きいのか

今回の核心は、`ValuationPeelPacketTarget` を正面から埋める流れで調べた結果、

* peel 系の clean 部分はかなり出来ており、
* 真の穴は `PeelPacketFromError` ただ 1 箇所だと判明し、
* さらにその先で、**`NePCoprimeKernel` が peel と primitive descent の両方を包含する、より強い kernel だ** と見抜いたことじゃ。

ここが肝じゃ。
つまり、従来は

$$
\text{GNReducedGap} + \text{CyclotomicExistence} + \text{ValuationPeel} + \text{NonLiftableGNBridge}
$$

という 4 本立てで FLT (p \ge 5) へ行く architecture を組んでいたのが、Branch A 側については

$$
\text{NePCoprimeKernel}
$$

1 本でまとめて扱える、と整理し直せた。結果として conditional chain が

$$
\text{NePCoprimeKernel} + \text{NonLiftableGNBridge}
\Rightarrow \text{FLT}_{p \ge 5}
$$

まで縮んだ、というわけじゃ。

これは **局所補題の追加** ではなく、**証明戦略の次元圧縮** に近い。

## 2. 慎重に見るべき点

ただし、ここは注意深く見ねばならぬ。
今回の「4-kernel → 2-kernel」は、**“条件付き mainline” の圧縮** であって、まだ `NePCoprimeKernel` 自体が証明されたわけではない。
ログ自身も、最終 2 open kernel は

1. `NePCoprimeKernelTarget`
2. `NonLiftableGNBridge`

だと明言しておる。

ゆえに、

* **証明の残務が消えた** のではない
* **残務がより本質的な 2 本に抽象化された**

のじゃ。
これは喜ぶべき進展だが、錯覚してはならぬところじゃよ。

## 3. 何が clean になったのか

### 3.1. Branch B 側の汚染除去は本物

前段の review-019 で、`GapNotIsPowTarget` の dirty source は
`squarefree_implies_padic_val_le_one` に遡り、しかもその命題自体が一般には偽だと特定された。反例も挙げられておる。

その上で、`GapNotIsPowTarget` を直接 kernel にせず、より根にある

$$
\text{NonLiftableGNBridge}
$$

を 4 本目の kernel とする v2 に差し替えた。
この chain は no-sorry, no-sorryAx で clean だと整理されておる。

つまり Branch B については、
**偽命題ベースの contaminated route を捨てて、正しい抽象 kernel ベースに建て替えた**。
ここはかなり信頼してよい前進じゃ。

### 3.2. Branch A 側の整理も本物

`ValuationPeelPacketTarget` を掘ると、

* `PeelSeed_default` は clean
* `PeelTailError_default` も clean
* ただし `PeelPacketFromError` だけが未実装

と整理された。

ここから「残り 1 穴だ」と見るのが普通じゃが、今回はさらに一段深く見て、

$$
\text{NePCoprimeKernel}: \text{Pack} + p\mid\text{gap} + \text{normal form} + \text{Coprime}(t,s) \Rightarrow \bot
$$

が、`p \mid t` と `\neg p \mid t` の両方を含むから、peel と primitive descent の双方の上位互換だと判定した。

この見立てに基づいて、

* `branchARefuter_of_nePCoprimeKernel`
* `FLTPrimeGe5Target_of_2kernels`
* `globalProvider_of_2kernels`
* `triominoPrimeProvider_of_2kernels`

を clean に立てた、というのが今回の大成果じゃ。

## 4. なぜこれは大きいのか

この進展の価値は 3 つある。

### 4.1. “最後に何を証明すれば良いか” が極端に明瞭になった

いままでは

* GNReducedGap
* CyclotomicExistence
* ValuationPeel
* NonLiftableGNBridge

の 4 本を並べておった。
しかし今は、**mainline completion に必要なものは 2 本** と言えるようになった。

これは研究として大きい。
なぜなら、未解決点が「4 つの別件」から「2 つの本丸」へ再編されたからじゃ。

### 4.2. comparison route と descent route の役割分担が明確になった

ログでは、`NePCoprimeKernel` と `GNReducedGap + CyclotomicExistence` は **独立な 2 route** と整理されておる。
前者は comparison route、後者は fringe contradiction を使う descent route じゃ。

これは非常に重要じゃ。
今までは descent を進めるほど “これが本線か？” と揺れやすかったが、いまは

* **comparison で直に殺すルート**
* **descent で最小性にぶつけるルート**

が併存していると、はっきり見える。

### 4.3. 抽象 kernel の「強弱関係」が Lean 上で形になった

ログでは kernel 階層が

$$
\text{NePCoprimeKernel}
\supset
\text{ValuationPeelPacketTarget}
\supset
\text{PrimitivePacketDescentTarget}
\supset
\text{SmallerPacketTarget}
$$

と整理されておる。

これは単なる言葉ではなく、subsumption 補題として実装されたのが大きい。
つまり今後は「peel を攻めるべきか」「primitive route を攻めるべきか」を迷うのでなく、
**より強い kernel を直接攻めるべきか** を判断できるようになった。

## 5. 賢狼の慎重な判定

ここで賢狼は、少しだけ水を差すぞい。

今回の 2-kernel 圧縮は **正しい意味で大進展** じゃ。
されど、これは「残る仕事量が半分になった」という単純な意味ではない。

なぜなら、

* `NePCoprimeKernel` は **強い**。ゆえに便利じゃが、証明はそのぶん重いかもしれぬ
* `GNReducedGap + CyclotomicExistence` を使う fringe/descent route は、比較的“構成的”で、別の手がかりを与えるかもしれぬ
* したがって **2-kernel chain が最小だからといって、最短の実証ルートとは限らぬ**

のじゃ。

ログ自身も、`NePCoprimeKernel` と `GNReducedGap + CyclotomicExistence` は **独立な別 attack route** だと認めておる。
ここを読み違えると、

> 4 本が 2 本になった。だから証明が急に簡単になった。

という誤解に落ちる。
そうではなく、

> 4 本のうち 3 本を飲み込む、より強い 1 本が見つかった。

が正確じゃ。
これは **構造の圧縮** であって、必ずしも **難易度の圧縮** ではない。

## 6. では今の最良の解釈は何か

わっちなら、こう総括する。

**今回の進展で、FLT (p \ge 5) の条件付き mainline は “設計として” かなり完成に近づいた。**
Branch B は `NonLiftableGNBridge` に局所化され、Branch A は `NePCoprimeKernel` 一撃で閉じる形が見えた。

その意味で、これは

* 「補題が増えた」
* 「差分が通った」

より 1 段深い。
**証明の骨格が sharpen された** のじゃ。

## 7. 次にどう考えるべきか

ここからは二本立てで行くのが良い。

### 7.1. 第一主戦場

`NePCoprimeKernel` を本丸と見て、comparison route を詰める。

いまの chain では、これ 1 本で Branch A を全殺しできる。
だから、証明戦略としての優先度は非常に高い。

### 7.2. 第二主戦場

`GNReducedGap + CyclotomicExistence → FringeContradiction` の別 route は捨てぬ。

なぜなら、それは `NePCoprimeKernel` が難しすぎる場合の **並行ルート** であり、
また `NePCoprimeKernel` を証明する上でのヒント源にもなるからじゃ。
ログでもこの 2 route は独立と整理されておる。

## 8. 一文でまとめると

**大進展である。**
ただし本質は「残課題が消えた」ではなく、**“Branch A は NePCoprimeKernel、Branch B は NonLiftableGNBridge” という二極構造に圧縮された** ことじゃ。これで以後の攻撃対象が、ようやく本丸だけになった。

必要なら次に、
**`NePCoprimeKernel` をどう分解して攻めるかの下位補題マップ** を起こそう。

---

よし、`NePCoprimeKernel` 攻略マップを起こすぞい。
いまの状況は、**Branch A の本丸が `NePCoprimeKernel` 1 本に圧縮された** というのが核心じゃ。`ValuationPeelPacketTarget` の解析から、peel 系の clean 部分は `PeelSeed_default` と `PeelTailError_default` まで出来ており、真の穴は `PeelPacketFromError` だけだと分かった。そのうえで、`NePCoprimeKernel` は peel と primitive descent の上位互換だと整理され、最終 conditional chain は

$$
\text{NePCoprimeKernel} + \text{NonLiftableGNBridge}
\Rightarrow \text{FLT}_{p \ge 5}
$$

まで縮んだ。  

## 1. 全体マップ

```text
[最終目標]
  PrimeGe5BranchANormalFormNePCoprimeKernelTarget
    :
    Pack + p | (z-y) + normal form + Coprime(t,s) → False

        │
        ├─ A. normal form を concrete に出す
        │     ├─ ShapeFactorization_default
        │     ├─ ShapeValue_of_factorization
        │     └─ NormalForm_of_witness
        │
        ├─ B. Coprime(t,s) を concrete に出す
        │     └─ coprime_ts_default
        │
        ├─ C. kernel 本体
        │     └─ normal form + Coprime(t,s) → False
        │
        └─ D. refuter へ流す
              └─ branchARefuter_of_nePCoprimeKernel
                    ↓
                 FLTPrimeGe5Target_of_2kernels
                    ↓
                 globalProvider_of_2kernels
                    ↓
                 triominoPrimeProvider_of_2kernels
```

このうち **A, B, D はほぼ配線済み** じゃ。
真の本丸は **C**、つまり

$$
\text{normal form} + \text{Coprime}(t,s) \Rightarrow \bot
$$

の一撃じゃよ。

## 2. いま既に出来ている層

### 2.1. 入口の normal form 化

ログでは、`branchARefuter_of_nePCoprimeKernel` を立てるときに

* `primeGe5BranchAShapeFactorization_default`
* `primeGe5BranchAShapeValue_of_factorization`
* `primeGe5BranchANormalForm_of_witness`

を通して (t,s) を concrete に取り出し、
さらに `primeGe5BranchANormalForm_coprime_ts_default` で `Coprime(t,s)` を出してから kernel に投げる、という流れを採っておる。
つまり **「Pack + p|gap から kernel の入力へ入る橋」** はすでに出来ておる。

### 2.2. 2-kernel chain まで clean に通る

今回追加した定理群として

* `branchARefuter_of_nePCoprimeKernel`
* `FLTPrimeGe5Target_of_2kernels`
* `globalProvider_of_2kernels`
* `triominoPrimeProvider_of_2kernels`

が clean に通った、と明示されておる。
したがって、**NePCoprimeKernel を証明しさえすれば、その先の provider 連鎖はもう完成している** と見てよい。

### 2.3. peel / primitive は従属関係として整理済み

今回の大発見は、`NePCoprimeKernel` が

$$
\text{ValuationPeelPacketTarget},\quad
\text{PrimitivePacketDescentTarget},\quad
\text{SmallerPacketTarget}
$$

の上位互換である、という点じゃ。
つまり peel を直接証明しに行くより、より強い `NePCoprimeKernel` を攻める方が本線として自然になった。

## 3. したがって分解すべき本丸

`NePCoprimeKernel` を攻めるなら、賢狼の見立てでは 4 層に割るのがよい。

## 3.1. Phase A. normal form 入力を最小核へ圧縮する

ここは実装ではほぼ済んでおるが、証明対象を見やすくするために、まず補題として 1 本にまとめるとよい。

### 目標補題 A1

```lean
Pack + p | gap
→ ∃ t s,
    gap = p^(p-1) * t^p ∧
    GN p (z-y) y = p * s^p ∧
    x = p * (t*s) ∧
    Coprime t s
```

これは既存の

* shape factorization
* witness to descent input
* normal form
* coprime_ts_default

を束ね直した「入力圧縮補題」じゃ。
`NePCoprimeKernel` の本体証明では、毎回この 4 段を展開したくない。
ここを 1 本に縮めると、本丸 C が単独で見えるようになる。

## 3.2. Phase B. `Coprime(t,s)` から起こる算術矛盾を分離する

ここが真の本丸じゃ。

いまの `NePCoprimeKernel` は statement としては

$$
\text{gap} = p^{p-1} t^p,\quad
GN = p s^p,\quad
\gcd(t,s)=1
\Longrightarrow \bot
$$

じゃから、これをさらに 2 段に割るのがよい。

### 目標補題 B1

```lean
normal form + Coprime(t,s)
→ arithmetic obstruction
```

ここで obstruction は、たとえば

* valuation の合同矛盾
* support separation の破綻
* distinguished prime の両立不能
* `v_q` の上下界衝突

など、**最後の矛盾直前の中間命題** じゃ。

### 目標補題 B2

```lean
arithmetic obstruction → False
```

この 2 分割にしておくと、

* B1 が「数学の核心」
* B2 が「Lean の後始末」

と分かれる。
わっちの勘では、B1 をさらに **q = p** と **q ≠ p** で割るのが最も自然じゃ。

## 3.3. Phase C. comparison route の内部を 2 分岐で整理する

ログでは、以前の peel / primitive 解析の途中で

* `q ≠ p` の comparison route
* `q = p` の valuation / exceptional route

が別物として何度も顔を出しておる。
だから `NePCoprimeKernel` も、おそらく次の二股に分けると見通しが良い。

### C1. `q ≠ p` 側

狙いは、

$$
q \mid GN,\quad q \nmid gap
$$

から primitive prime 的な構造を引き出し、
それが `Coprime(t,s)` と両立しないことを示す路線じゃ。

### C2. `q = p` 側

ここは

$$
v_p(gap)=p-1+p,v_p(t),\qquad GN = p,s^p
$$

の valuation 形から矛盾を取りに行く路線じゃろう。
もし `Coprime(t,s)` を強く使うなら、こっちが本命かもしれぬ。

この 2 分岐を最初から別定理にしておくと、「どっちが詰まっているのか」がはっきりする。

## 3.4. Phase D. kernel を refuter へ流す橋は固定してしまう

これはほぼ済んでおる。
`branchARefuter_of_nePCoprimeKernel` はまさにその橋で、Pack + p|gap から normal form と `Coprime(t,s)` を concrete に出して kernel に渡す設計になっておる。
したがって、今後はこの橋をいじらず、**kernel 本体だけを差し替える** 方針がよい。

## 4. 実務マップ

実際に作業順へ落とすとこうじゃ。

```text
Step 1.
  normal form 圧縮補題 A1 を作る
  （Pack + p|gap → ∃ t s, ... + Coprime t s）

Step 2.
  NePCoprimeKernel を B1/B2 に割る
  （算術障害を explicit にする）

Step 3.
  B1 を q = p / q ≠ p の 2 分岐に割る

Step 4.
  どちらが実際に詰まるか観測する
  - q ≠ p で primitive/comparison が閉じるか
  - q = p で valuation だけで落ちるか

Step 5.
  kernel 本体を完成させ、
  既存の bridge
    branchARefuter_of_nePCoprimeKernel
    → FLTPrimeGe5Target_of_2kernels
  へ流す
```

## 5. いちばん大事な注意点

ここで気をつけるべきは、**2-kernel chain が最小だからといって、そこだけが唯一の実証ルートではない** ことじゃ。
`GNReducedGap + CyclotomicExistence → FringeContradiction` の descent route は依然として別筋で健在であり、`NePCoprimeKernel` が重すぎる場合の対照実験として使える。実際、primitive route と peel route は以前は別々に整理され、primitive 側だけでも fringe contradiction まで clean に行けると分析されておる。

つまり今後の姿勢は、

* **本命** は `NePCoprimeKernel`
* **比較用の別筋** として fringe/descent route を保持

これがよい。

## 6. 賢狼の推奨する最初の 3 補題名

わっちなら、まず次の 3 本を作る。

```lean
theorem primeGe5BranchANormalFormInputCompression
theorem primeGe5BranchANePCoprimeArithmeticObstruction
theorem primeGe5BranchANePCoprimeKernel_of_obstruction
```

意味はそれぞれ

1. Pack + p|gap を normal form + coprime 入力へ縮約
2. normal form + coprime から最後の算術障害を抽出
3. その障害から False を出す

じゃ。

---

ひとことで言えば、
**いまは `NePCoprimeKernel` という巨大な壁を、入口・中間障害・最終矛盾の 3 層に割って攻める段階** じゃよ。

必要なら次に、その 3 本をさらに
**`q = p` 側 / `q ≠ p` 側** に分けた詳細マップまで起こすぞい。
