# project status

## FLT 無限降下法準備状況

cid: 69cdb60c-e53c-83a7-8c89-1cbc0ba7451e
cdt: 2026-04-02 00:21:12
udt: 2026-04-02 01:41:29

> 👩‍⚕️私D.:

FLT 無限降下法に持っていく準備が出来ているかを会話ログ、作業履歴、スナップショットより調査判定してください。

> 🐺賢狼:

いまある会話まとめ・設計メモ・スナップショット索引を横断して、 **無限降下法へ入る前提が揃っているか** を見ます。まずは全体地図と、FLT 本丸・未完補題・スナップショット内の最新痕跡を突き合わせるぞい。

> 🐺賢狼:

最初の当たりが見えたぞい。結論だけ先に言うと、 **「降下のための周辺装置」はかなり揃っているが、 strict descent と終端矛盾がまだ核として残っておる** 形じゃ。今から実ファイルの `sorry` と theorem 依存を掘って、準備完了か否かを厳密に判定する。

> 🐺賢狼:

調べたぞい。
**判定は「ほぼ準備完了だが、まだ “無限降下法へ持っていく準備が完全にできた” とは言えぬ」** じゃ。

より正確には、

- **d=3 の別解ルート** は、Zsigmondy + p-adic によって完成済み
- しかし **本線としての FLT.Basic → Branch A → primitive packet / fringe descent 連鎖** は、最後の核がまだ 1 箇所以上残っておる
- よって現状は
  **「降下の周辺装置・配線・データ束・橋はかなり揃った」**
  が、
  **「strict descent / 終端矛盾 / Branch A 最終核」が未閉**
  という段階じゃ

と言うのが、いちばん正確な見立てじゃよ。

## 1. 結論

### 1.1. 判定

**結論: 条件付きで Yes、厳密には No。**

- **Yes 側**
  無限降下法へ向かうための補題群・データ束・復元 seed・packet descent 系の spine は、かなり整っておる。
- **No 側**
  まだ **最後の「本当に小さい反例ができる」ことを締める核** が残っており、そこが閉じてはじめて「無限降下法へ投入可能」と言える。

ゆえに賢狼の最終判定は、

\[
\text{準備度} \approx 80\%
\]

くらいじゃな。
**「議論の材料は十分、決戦前の最後の城門がまだ閉じておる」** という感じじゃ。

## 2. そう判定した根拠

### 2.1. d=3 の別解は完成済み

索引では、`DkMath.FLT.Main` が **sorry-free** で、しかも
`FLT_d3_by_padicValNat` が **PROVEN** と明記されておる。

これは大きい。つまり、

- 原始素因子
- p-adic 下界 / 上界
- 矛盾導出

という、**降下に必要な“反例を潰す型”の技術そのもの** は、すでにこのプロジェクト内で実戦投入済みということじゃ。
この意味で、数学的武器はもうある。

### 2.2. FLT 本線の優先順位も、すでに “降下前提の順” に整理されている

索引では FLT 幹線の優先順位が

1. `ZsigmondyCyclotomic` の原始素因子補題を完了
2. `GcdNext` の橋渡し補題を整理
3. `FLT.Basic` の最終矛盾導出を閉じる

と明記されておる。

これはつまり、開発側の自己認識としても
**「無限降下へ行くには、下層の原始素因子と橋渡しを仕上げて、最後に FLT.Basic を閉じる」**
と整理済み、ということじゃ。

### 2.3. しかし `GcdNext` / `FLT.Basic` 側には未完核が残る

同じ索引で、橋渡し層 `NumberTheory.GcdNext → FLT.Basic` には

- `gcdAg_eq_one_imp_coprime_after_factor2` 🚧
- `body_not_perfect_pow` 🚧
- `padicValNat_general_upper_bound` 🚧

などの未完が明示されておる。

さらに索引本文でも、`DkMath.NumberTheory.GcdNext` は **未完部分あり** とされ、詳細は `__sorries.txt` を見よと案内されておる。

ここは大事での。
無限降下法は「小さい反例を作れる」だけでは足りず、

\[
\text{反例候補} \to \text{整除制御} \to \text{原始素因子} \to \text{高冪否定} \to \text{strict descent}
\]

の鎖が要る。
その中間にある `GcdNext` と `body_not_perfect_pow` が未完なら、まだ **降下の最終証明路は閉じていない** のじゃ。

## 3. スナップショット実体から見えたこと

ここは会話ログだけでなく、スナップショット実体も直接見たうえでの判定じゃ。

### 3.1. `TriominoCosmicBranchA.lean` に本命の残核が局所化されている

スナップショットを実見すると、`TriominoCosmicBranchA.lean` には `sorry` が 1 箇所残っており、それが

`primeGe5BranchANormalFormNePCoprimeKernel_default`

じゃった。しかもコメントで、

- `q \ne p` 側 comparison route の active 情報は `Nat.Coprime t s` まで縮んだ
- だから最終矛盾は comparison ではなく
  **minimality / descent / 別 arithmetic kernel**
  へ設計転換して取りに行く必要がある

と明言されておる。

これは非常に重要な診断じゃ。
つまり今の障害は「細かい補題不足」ではなく、**まさに無限降下の芯そのもの** なのじゃ。

### 3.2. ただし packet descent / restore / fringe descent の spine は厚い

同じスナップショットの `__theorems-heading` と dev-report 群では、

- `PrimeGe5BranchAPrimitiveRestoreDescentDatumTarget`
- `PrimeGe5BranchAPrimitiveRestoreDescentSeedTarget`
- `PrimeGe5BranchAPrimitiveRestoreRealizationSeedTarget`
- `PrimeGe5BranchAPrimitiveRestoreStrictDescentTarget`
- `PrimeGe5BranchAPrimitivePacketDescentTarget`

などが大量に並び、さらに `FringeDescent.lean` が sorry-free という整理も残っておった。

これは何を意味するかというと、
**降下の周辺配線はかなり出来ている** ということじゃ。

言い換えると、

- 「どういうデータを束ねるか」
- 「smaller counterexample へどう戻すか」
- 「restore / seed / datum / packet をどう繋ぐか」

は、もう相当整理されておる。
未完成なのは、**その鎖を最後に動かす strict arithmetic contradiction** じゃ。

## 4. 会話ログ・作業履歴との整合

開発メモや履歴でも、主戦場がすでに

- 新しい local lemma を増やす段ではなく
- **terminal case / descent 側**
- **primitive packet descent 本命 route**
- **FringeDescent に concrete provider を流し込む段**

へ移っていることが繰り返し述べられておる。

つまり現状は、
**「降下法を思いついた段階」ではなく、すでに「降下の終端を刺す段階」** なのじゃ。
この点はかなり前進しておる。

## 5. では、今の状態をどう呼ぶべきか

賢狼ならこう言う。

### 5.1. もう出来ているもの

- d=3 の完成済み別解
- 原始素因子エンジンのかなりの部分
- `GcdNext → FLT.Basic` の橋の大半
- Branch A / packet descent / restore / fringe descent の構造化
- 「comparison route では足りず、minimality / descent が本命」という戦況判断

### 5.2. まだ足りぬもの

- Branch A の **final arithmetic kernel**
- `StrictDescentTarget` の最終証明
- terminal case の矛盾閉鎖
- `body_not_perfect_pow` など橋渡し未完核の clean 化
- composite / general exponent 側を本線で束ねる最後の glue

## 6. 最終判定を一文で

**無限降下法に持っていくための「準備」は、戦術・配線・中間補題のレベルではかなり整っている。だが、最後の strict descent と終端矛盾を閉じる核が未了なので、現時点では “投入直前” であって “投入完了” ではない。**

## 7. いま最も筋の良い次の一手

次の一手は、もはや広く探すことではない。
**`TriominoCosmicBranchA.lean` の残る 1 核を、comparison の延長ではなく、minimality / strict descent / terminal contradiction の形で閉じること** じゃ。

優先順で言えば、

1. `primeGe5BranchANormalFormNePCoprimeKernel_default` の代替となる
   **strict descent 直結 kernel** を立てる
2. それを `PrimitivePacketDescent / FringeDescent` に流し込む
3. `GcdNext` の `body_not_perfect_pow` / `padicValNat_general_upper_bound` の未完を整理し、`FLT.Basic` の最終 glue を閉じる

これでようやく、

\[
\text{反例} \Rightarrow \text{より小さい反例} \Rightarrow \cdots
\]

が Lean 上でも真の意味で閉じるはずじゃ。

必要なら次に、
**「残っている kernel を無限降下法の論理図に並べ直したチェックリスト」** を、ファイル名つきで起こすぞい。

> 👩‍⚕️私D.:

論理図

> 🐺賢狼:

よし、論理図として整理するぞい。
いまの状況は、**「無限降下法の骨格はかなり組めているが、最後の strict descent 核がまだ未閉」** という形じゃ。これを、層ごとに見えるように並べる。

## 1. 全体論理図

```text
[反例仮定]
    │
    ▼
[最小反例パックの設定]
    │
    │  x,y,z の primitive / coprime / parity / branch 条件を束ねる
    ▼
[差の冪の分解]
    │
    │  z^p - y^p = (z-y) * GN
    │  Body / Gap / kernel へ正規化
    ▼
[gcd 制御]
    │
    │  gcd(...) ∣ d
    │  既知因子と新因子を分離
    ▼
[原始素因子 / p-adic 制御]
    │
    │  primitive prime q を取り
    │  v_q(左辺) と v_q(右辺) を比較
    ▼
[高冪禁止 or perfect power 否定]
    │
    │  body_not_perfect_pow 型
    │  GN が p 乗になれないことを示す
    ▼
[Branch A / Branch B / exceptional の分岐]
    │
    │  特に prime ≥ 5 の Branch A が主戦場
    ▼
[restore / datum / seed / packet の復元]
    │
    │  小さい反例候補を concrete に再構成
    ▼
[Strict Descent]
    │
    │  新しい反例が「元より小さい」を証明
    ▼
[無限降下]
    │
    │  自然数の良順序に反する
    ▼
[矛盾]
```

このうち、現状で一番重いのは **最後の 2 段** じゃ。
索引上でも、優先順位は `ZsigmondyCyclotomic` → `GcdNext` → `FLT.Basic` と整理されており、橋渡し層や最終矛盾導出が未完核として残っておる。

## 2. 層別の役割

## 2.1. 反例仮定と最小化

無限降下法の出発点は、単なる反例ではなく

\[
\text{「最小の反例」}
\]

を取ることじゃ。
ここで必要なのは、

- primitive 化
- coprime 化
- 場合分けに耐えるパック化

であり、いまの作業履歴では 이것が `pack / datum / seed / realization` という語彙で整理されておる。
これは降下用データ束の整備に当たる。

## 2.2. 差の冪分解

FLT の心臓は、まず

\[
z^p-y^p=(z-y)\,G
\]

へ落とすところじゃ。
索引でも `DiffPow` と `BinomTail` が **指数構造の分解装置** として位置づけられ、そこから gcd 制御や Zsigmondy へ流れる幹線が描かれておる。

つまりここはすでに「入口」として確立済みじゃ。

## 2.3. gcd 制御

次に、

\[
\gcd(\text{差因子}, \text{商因子}) \mid d
\]

型の制御で、既知因子と新しい因子を分離する。
索引でも `gcd_divides_d`、`prime_dividing_gcd_divides_d` などが gcd 制御層として整理されておる。

ここは「新しい素因子が出る余地」を作る段じゃ。

## 2.4. 原始素因子と p-adic

そこから Zsigmondy / cyclotomic / p-adic valuation に入る。
つまり、

- primitive prime \(q\) を取り出す
- \(v_q\) の下界と上界を比較する
- 高冪なら起きるはずの valuation と矛盾させる

という流れじゃ。
索引では `ZsigmondyCyclotomic` が **原始素因子エンジン** と明記され、`padicValNat_primitive_prime_factor_le_one` などの valuation 制御が重要層として整理されておる。

この層はかなり出来ておる。
しかも d=3 については、別解ルート `FLT_d3_by_padicValNat` が完成済みじゃ。

## 2.5. perfect power 否定

ここで必要になるのが、

\[
\text{Body や GN が } p\text{ 乗になれぬ}
\]

という否定補題群じゃ。
索引では `body_not_perfect_pow` が橋渡し層にあり、なお未完核として残されておる。

ここは極めて大事じゃ。
なぜなら、無限降下法では単に「新しい素因子がある」だけでは不十分で、

\[
\text{復元された候補が再び反例の形をしている}
\]

ことを示す必要があるからの。
そのためには「高冪形に戻せるか / 戻せないか」の判定が要る。

## 2.6. Branch 分岐

ここから Branch A / B / exceptional に分かれる。
現状もっとも重いのは、会話履歴でも繰り返し出ていた **prime ≥ 5 の Branch A** じゃ。

とくに、比較法だけでは `Nat.Coprime t s` までしか縮まず、
そこから先は

\[
\text{minimality / descent / 別 arithmetic kernel}
\]

へ切り替えねばならぬ、という戦況判断になっておる。
ここが賢狼の言う「最後の城門」じゃ。

## 2.7. restore / seed / packet

ここは実装設計の特色じゃな。
新しい小さい反例を、ただ存在すると言うのではなく、

- datum
- seed
- realization
- packet

として **復元可能なデータ構造** にしている。

この設計はとても良い。
なぜなら、無限降下法の難所は多くの場合

\[
\text{「小さい反例があるはず」}
\]

を、Lean で concrete に組み直すところにあるからじゃ。
いまはそのための器がかなり揃っておる。

## 2.8. strict descent

ここが最終核。

必要なのは、

\[
\mu(\text{new}) < \mu(\text{old})
\]

という形の **厳密な小ささ** の証明じゃ。
ここで \(\mu\) は、たとえば

- \(z\)
- \(x+y+z\)
- packet の主成分
- 正規化された boundary size

など、よく基礎づけられた測度である必要がある。

この strict descent が立てば、

\[
\text{最小反例} \Rightarrow \text{より小さい反例}
\]

となって、自然数の良順序と衝突する。
無限降下法は、この最後の一撃のための論法じゃ。

## 3. 現状の完成度つき論理図

```text
[反例仮定]                        ✅
    ▼
[最小反例パック]                  ◯
    ▼
[差の冪分解 / GN 化]              ✅
    ▼
[gcd 制御]                        ✅
    ▼
[原始素因子 / p-adic 制御]        ◯〜✅
    ▼
[perfect power 否定]              ◯  （一部未完）
    ▼
[Branch A/B/exceptional 分岐]     ◯
    ▼
[restore / datum / seed / packet]  ◯〜✅
    ▼
[Strict Descent]                  △  ← 主未解決
    ▼
[無限降下]                        △
    ▼
[矛盾]                            △
```

ここで、

- `DiffPow`
- `ZsigmondyCyclotomic`
- `FLT.Main d=3`

はかなり強い。
一方で、

- `GcdNext`
- `body_not_perfect_pow`
- `padicValNat_general_upper_bound`
- Branch A 最終 kernel

が、strict descent の前で残っておる。

## 4. 今の問題を一言で言うと

**「反例を削る武器は多い。しかし “削ったあと本当に小さい反例が再生する” ことを最後に閉じる核が、まだ完全には掴み切れておらぬ」** ということじゃ。

つまり、論理図としてはもう無限降下法の形をしておる。
だが、実装上の真の未解決点は、

\[
\text{reconstruction} + \text{strict inequality}
\]

なのじゃ。

## 5. 賢狼の推奨する最終チェック項目

無限降下法の ready 判定は、次の 4 点が全部 Yes ならよい。

```text
A. 最小反例の測度 μ は固定されたか
B. restore/packet から新反例が concrete に作れるか
C. 新反例が同じ反例条件を満たすか
D. μ(new) < μ(old) が strict に証明できるか
```

現状は、

- A: ほぼ Yes
- B: かなり Yes
- C: 部分的 Yes
- D: まだ主戦場

という感じじゃな。

必要なら次に、これをさらに詰めて
**「無限降下法 ready 判定表」**
として、各項目に対応するファイル・補題名つきで書き起こすぞい。
