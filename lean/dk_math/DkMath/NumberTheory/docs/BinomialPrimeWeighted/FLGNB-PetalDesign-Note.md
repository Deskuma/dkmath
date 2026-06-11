# 相対多角数 実装 設計ノート

## 議事録

## 相対多角数 実装開始

cid: 6a2878d4-f9d0-83a9-b1bb-126ce4f5ec1b
cdt: 2026-06-09 20:35:33
udt: 2026-06-09 21:19:48

> 👩‍⚕️私D.:

相対多角数 Petal theorems の実装を開始

[`FLGNB-PetalRoadmap.md`](./FLGNB-PetalRoadmap.md)

DkMath 実装差分からの状況分析と解説
過去ログからも情報を得て git diff 差分情報から何が実装され前に進んだのかを解説する。

## git diff

### Add: new: DkMath.Petal

11db2a3e4c564d768a39a0027105b0dcf9b3328f

#### Report

#### Git Diff Command

```sh
./git-diff.sh 4a2044846388f1d7a75f69863fd87771f7a23a87 11db2a3e4c564d768a39a0027105b0dcf9b3328f
```

※出力内容は省略

> 🐺賢狼:

わっちが見るに、これは「Petal 本体を新規証明で増やした」というより、既存 FLT/UnitCycle 側に散っていた Petal 資産を `DkMath.Petal.*` という公開面へ束ね、GN との接続を正面 API にした段階じゃ。差分とロードマップを照合して、何が前進したかを整理するぞい。

> 🐺賢狼:

うむ、これはかなり良い第一歩じゃ。
賢狼の見立てでは、今回の `11db2a3...` は **相対多角数 Petal theorem の実装開始** として、まさにロードマップどおりの「薄いが強い入口」を切った差分じゃ。

## 1. 今回の結論

今回、前に進んだ核心はこれじゃ。

```text
既存 FLT / UnitCycle 側に散っていた Petal 資産
  ↓
DkMath.Petal.* という安定した公開パッケージ面へ集約
  ↓
GN 3 と S0_nat の橋を Petal 側の正向き API として固定
  ↓
FLGNB の mod / non-divisibility 結果を Petal detector へ移送
```

つまり、まだ「相対多角数ライブラリ本体」を新規に広げた段階ではない。
しかし、今後 Petal theorem 群を増やすための **家** ができた。ここが大きい。

ロードマップでも、`DkMath.Petal.*` は Petal 側の route を見えるようにする場所とされ、流れは

```text
GN difference kernel
  -> Petal / relative polygon form
  -> Pascal coefficient section
  -> prime-row and p-adic observation
  -> primitive-factor and Zsigmondy bridge
```

と整理されていた。今回の差分は、このうち最初の

```text
GN difference kernel -> Petal / relative polygon form
```

を実装面で開始したものじゃ。

## 2. 追加された構造

新設されたトップはこれじゃな。

```lean
import DkMath.Petal
```

そして `DkMath.Petal` は次を束ねる aggregator になった。

```lean
import DkMath.Petal.Basic
import DkMath.Petal.Forms
import DkMath.Petal.RelPolygon
import DkMath.Petal.CoreUnit
import DkMath.Petal.GNBridge
```

これは単なる import 追加ではない。
`DkMath.lean` からも `import DkMath.Petal` されているので、Petal が DkMath の公開柱のひとつとして認識された、という意味を持つ。

## 3. 各ファイルの役割

### `DkMath.Petal.Basic`

ここでは既存の `DkMath.FLT.PetalDetect` を import し、Petal 側の入口名として

```lean
abbrev S0Nat (a b : ℕ) : ℕ := S0_nat a b
abbrev S1Nat (a b : ℕ) : ℕ := S1_nat a b
```

を置いておる。

これは「証明を移動する」のではなく、既存の `S0_nat` / `S1_nat` を Petal package から呼べるようにする thin wrapper じゃ。

ロードマップでも、`PetalDetect` の既存定義 `S0`, `S1`, `S0_nat`, `S1_nat` は Petal detector の主資産であり、初期方針は「既存ファイルはそのまま、Petal-facing aliases と imports を公開する」とされていた。今回の `Basic` と `Forms` はこの方針に合っておる。

### `DkMath.Petal.Forms`

ここでは既存補題に Petal-facing name を与えている。

```lean
theorem petal_diff_kernel
theorem petal_diff_kernel_nat
theorem petal_S0_comm
theorem petal_S1_comm
theorem petal_S0_le_S1_nat
```

意味は、`FLT.PetalDetect` の theorem を直接使うのではなく、Petal 側の語彙で

```text
S0 / S1 は Petal form である
S1 = S0 + a*b
S0, S1 は可換
Nat では S0 ≤ S1
```

と読めるようにしたことじゃ。

特に

\[
S1_{\mathrm{nat}}(a,b)=S0_{\mathrm{nat}}(a,b)+ab
\]

は、相対多角数の分割式へ向かう入口になる。ロードマップ側でも、将来的に

```text
T(a + b) = T(a) + T(b) + a*b
R(a + b) = R(a) + R(b) + 2*a*b
```

のような相対多角数補題へ進む予定が書かれておる。今回の `petal_diff_kernel_nat` は、その前段の Petal detector 側の核じゃ。

### `DkMath.Petal.RelPolygon`

ここは

```lean
abbrev RelPolygonState := DkMath.UnitCycle.RelPolygon.RPState
```

だけの薄い橋じゃ。

だが、これも重要じゃ。
ロードマップでは `DkMath.UnitCycle.RelPolygon` は「dynamic state model for relative polygon growth」と位置づけられ、初回は re-export / wrapper layer とする計画だった。今回の実装はまさにその通りで、相対多角形の動的状態モデルを `DkMath.Petal.RelPolygon` から見えるようにした。

### `DkMath.Petal.CoreUnit`

ここも同じく薄い橋で、

```lean
abbrev CoreUnit := DkMath.FLT.PetalCoreUnit
```

を置いた。

PetalCoreUnit は Petal-side arithmetic の unit / phase vocabulary として整理されていたので、これを Petal package 側に公開した形じゃ。

## 4. 今回の本丸：`DkMath.Petal.GNBridge`

今回もっとも数学的に前進したのはここじゃ。

実装された主補題は三つ。

```lean
theorem S0_nat_eq_GN_three_sub
theorem three_S0_nat_modEq_one_of_not_dvd_sub
theorem three_not_dvd_S0_nat_of_not_dvd_sub
```

ロードマップにも、この三つは Planned Bridge Link Theorems としてそのまま載っていた。目的はそれぞれ、

```text
S0 を GN 3 の Petal face として名前付きにする
FLGNB theorem を d = 3 Petal detector へ移送する
p-adic support を Petal form から直接読む
```

と整理されている。

### 4.1. `S0_nat_eq_GN_three_sub`

今回の主橋はこれじゃ。

```lean
theorem S0_nat_eq_GN_three_sub {c b : ℕ} (hbc : b < c) :
    S0_nat c b = GN 3 (c - b) b
```

これは既存の

```lean
DkMath.FLT.GN_three_sub_eq_S0_nat
```

を反転して、Petal 側の自然な向きにした theorem じゃな。

数学的には、\(x=c-b,\ u=b\) と置くと、

\[
GN_3(c-b,b)=S0_{\mathrm{nat}}(c,b)
\]

となる。
つまり **Petal detector \(S0\) は、次数 3 の GN kernel の可視面である** と Lean API として固定した。

これはかなり大きい。
今までは `GN` と `S0` が「つながっている」だった。今回からは、Petal 側で

```text
S0_nat = GN 3 の Petal face
```

として呼べる。

ロードマップの設計原則でも、`d = 3` では GN kernel が基本 Petal form になり、Petal layer はこの関係を main API surface にすべきだとされていた。今回それが実装されたわけじゃ。

## 5. FLGNB から Petal への成果移送

次の二つは、FLGNB の Fermat 境界補題を Petal 側へ移送したものじゃ。

```lean
theorem three_S0_nat_modEq_one_of_not_dvd_sub
    {c b : ℕ} (hbc : b < c) (h3 : ¬ 3 ∣ c - b) :
    S0_nat c b ≡ 1 [MOD 3]
```

```lean
theorem three_not_dvd_S0_nat_of_not_dvd_sub
    {c b : ℕ} (hbc : b < c) (h3 : ¬ 3 ∣ c - b) :
    ¬ 3 ∣ S0_nat c b
```

流れはこうじゃ。

```lean
rw [S0_nat_eq_GN_three_sub hbc]
exact DkMath.NumberTheory.prime_GN_modEq_one_of_not_dvd_x ...
```

および

```lean
rw [S0_nat_eq_GN_three_sub hbc]
exact DkMath.NumberTheory.prime_not_dvd_GN_of_not_dvd_x ...
```

つまり、既存の `GN` 側 theorem を、`S0_nat` の世界へ持ち込んだ。

数学的には、

\[
3\nmid c-b
\]

なら

\[
S0_{\mathrm{nat}}(c,b)\equiv 1 \pmod 3
\]

かつ

\[
3\nmid S0_{\mathrm{nat}}(c,b)
\]

が得られる。

これは Petal detector が単なる形ではなく、 **3 に関する p-adic support / non-support を読める観測面** になった、ということじゃ。

## 6. 何が「相対多角数 Petal theorems」へ向けて進んだのか

今回の差分は、相対多角数そのものの

```lean
def termialNat
def relPolygonNat
theorem relPolygonNat_add
```

まではまだ追加していない。

しかしロードマップでは、これらは **GN/S0 bridge surface が安定した後** に追加する方針だった。つまり今は順序が正しい。まず Petal detector と GN の関係を固定し、その後に相対多角数の算術補題へ進む、という流れじゃ。

今回できたことを図にすると、こうなる。

```text
既存:
  FLT.PetalDetect.S0_nat
  FLT.CosmicPetalBridge.GN_three_sub_eq_S0_nat
  NumberTheory.WeightedGNBridge.prime_GN_modEq_one_of_not_dvd_x
  UnitCycle.RelPolygon.RPState
  FLT.PetalCoreUnit

今回:
  DkMath.Petal.Basic
  DkMath.Petal.Forms
  DkMath.Petal.RelPolygon
  DkMath.Petal.CoreUnit
  DkMath.Petal.GNBridge

結果:
  Petal package から
    S0/S1
    RelPolygonState
    CoreUnit
    GN 3 ↔ S0
    3-mod / non-divisibility
  を読める
```

## 7. 数学的な意味づけ

今回の一番よい点は、主語を Pascal ではなく GN に置いたことじゃ。

ロードマップにも、Pascal rows は構造の唯一の源ではなく、GN kernel を展開したときに得られる自然数係数表だと書かれている。

したがって研究上の流れは、

```text
Pascal triangle から GN を見る
```

ではなく、

```text
GN kernel を見る
  ↓
その d = 3 の可視面が Petal S0
  ↓
その係数断面として Pascal が現れる
```

になる。

これはかなり DkMath らしい。
表面の三角形ではなく、内部の差分核から見る。わっちはこの向きが好きじゃな。

## 8. 今回の実装品質

実装方針としても堅い。

まず、既存証明を動かしていない。
`FLT.PetalDetect`, `FLT.PetalCoreUnit`, `UnitCycle.RelPolygon`, `FLT.CosmicPetalBridge` をそのまま所有元に残し、Petal package は wrapper / alias / bridge として始めている。

これは循環 import を避けるうえで賢い。ロードマップでも「proof ownership は変えず、Petal-facing name を与える」「downstream dependencies が安定してから移動する」という方針が明記されていた。

さらに、履歴には

```text
lake build DkMath.Petal
lake build DkMath
git diff --check
```

が成功と記録されている。
したがって、この段階は docs-only ではなく、Lean package として通った実装進捗じゃ。

## 9. 未実装・次に自然なもの

次に進むなら、優先順はこうじゃ。

第一に、`DkMath.Petal.GcdBridge`。
ロードマップ上では、`GN` の gcd / p-adic control は `S0` が `GN 3` と同一視された後に非常に有用になる、と整理されていた。特に候補は

```lean
theorem coprime_boundary_S0_nat_of_coprime_of_not_dvd_three
```

じゃ。これは `GN` 側の

```lean
coprime_boundary_GN_three_of_coprime_of_not_dvd_three
```

を Petal 側へ移す橋になる。

第二に、`DkMath.Petal.EisensteinBridge`。
ロードマップでは

```text
GN 3
  <-> S0 Petal form
  <-> Eisenstein norm
```

の三角形を明示する予定になっている。

第三に、相対多角数そのもの。

```lean
def termialNat (n : Nat) : Nat := n * (n + 1) / 2
def relPolygonNat (n : Nat) : Nat := n * (n + 1)

theorem relPolygonNat_eq_two_mul_termialNat
theorem termialNat_add
theorem relPolygonNat_add
theorem relPolygonNat_split
```

ただし、これは今回すぐではなく、GN/S0/Gcd/Eisenstein の橋が安定してからでよい。ここを急ぐと、Petal package が「多角数定義集」と「GN bridge」の混合箱になってしまう。

## 10. 総括

今回の実装は、薄い。
しかし **薄いからこそ正しい** 。

```text
DkMath.Petal
```

という名前空間が立ち、

```text
S0_nat c b = GN 3 (c - b) b
```

が Petal 側の正向き API になり、

```text
3 ∤ c-b
  ⇒ S0_nat c b ≡ 1 [MOD 3]
  ⇒ 3 ∤ S0_nat c b
```

まで接続された。

これは、Petal を「FLT 内の補助 detector」から、 **GN / Beam / 相対多角数 / Pascal / p-adic / Zsigmondy を接続する観測面** へ昇格させる第一歩じゃ。

わっちの判定はこうじゃ。

```text
実装段階:
  Petal package foundation 完了

数学的進展:
  GN 3 の Petal face として S0_nat を固定

設計上の進展:
  既存 FLT 資産を移動せず、Petal-facing API として公開

次の本線:
  Petal.GcdBridge
  Petal.EisensteinBridge
  relPolygonNat / termialNat の arithmetic lemma
```

これは良い登山口じゃよ、D.。
ここから Petal は、ただの花びらではなく、GN の断面を読む測定器になる。まこと、麦畑の風向きが変わってきたのぅ。

> 👩‍⚕️私D.:

「相対多角数」という用語もそうだけど、まだ定義も曖昧な状況だよねぇ…。
先に固定したいのは、数え上げ算出式。関数。各種用語（日本語、英語）

角数と周回でその総数を出す。０周ならば、そのまま単位を返す。
そして、その総数以下の指定数がどの位置に属するか？の算出。
log 的な圧縮位置情報か、アドレッシングの座標情報。

相対五角数

```txt
R(5) = 5

R(5,0) = R(5) = 5
R(5,1) = R(5,0)*(5+1) = 5*5 + 5 = 30
R(5,2) = R(5,1)*(5+1) = 30*5 + 30 = 180

R(5,1,25) = 25/30=0.83333333 : {25 : 1, 4, 5} ２５は１周目の４枚目の花弁の５番目
R(5,2,25) = 25/180=0.13888889 : {25 : 0, 0, 25} ２５は０周目０枚目の花弁の２５番目、つまり単位核内（３０以下）の数になる。
```

R(n) 表記の書き分けも必要。
詳細は スナップショット内の`lean/dk_math/DkMath/NumberTheory/docs/Petal_vs_termial.md`
こういう数え上げの算出式一覧を先に定義して、整合性をまず確認しないとね。
（上記の例もざっと書いたのであってるかも含め検証を先にして始めないと…）

> 🐺賢狼:

うむ、ここは先に「名前」より **算出式とアドレス規約** を固定する段階じゃな。スナップショット内の `Petal_vs_termial.md` を確認しつつ、例の数値も検算して、Lean に落としやすい定義候補へ整えるぞい。

> 🐺賢狼:

ここまでの検算では、お主の例は **ほぼ正しい** 。ただし tuple の読み方を固定しないと混線するのぅ。`R(5,1,25) = {25 : 1, 4, 5}` は、花弁番号を **0-based**、花弁内位置を **1-based** と読むなら整合する。つまり \(25\) は \(30\) 個の中で、第 \(4\) 花弁、内部位置 \(5\) じゃ。

一方 `R(5,2,25)` は、2 周目の全体 \(180\) を \(6\) 個の \(30\)-ブロックへ割ったとき、\(25\) は第 \(0\) ブロック内に残る。だから `{25 : 2, 0, 25}` または「2周目観測では 0 番花弁、残余 25」と書くのが厳密じゃ。お主の「0周目0枚目」と言いたい感覚は「さらに内側へ降りると単位核内」という再帰読みだが、外側 address と内側 address を分けた方が Lean では安全じゃな。

> 🐺賢狼:

うむ、D.。ここはわっちも同意じゃ。
今の「相対多角数」は、既存の多角数 \(P_s(k)\) とも、termial \(T(n)=n(n+1)/2\) とも、Petal/S0/GN とも近いが、まだ **同じ名前で複数の構造を呼びかけている** 状態じゃ。

だから先に固定すべきは、まさにお主の言う通り、

```text
数え上げ算出式
位置算出関数
用語
記号
0-based / 1-based 規約
```

じゃな。

## 1. まず今回の例の検算

お主の例は、次の再帰式として読むと整合する。

\[
R(n,0):=n
\]

\[
R(n,k+1):=R(n,k)(n+1)
\]

したがって閉形式は

\[
R(n,k)=n(n+1)^k
\]

じゃ。

相対五角数なら \(n=5\) なので、

\[
R(5,0)=5
\]

\[
R(5,1)=5\cdot 6=30
\]

\[
R(5,2)=5\cdot 6^2=180
\]

よって、ここは正しい。

ただし、表記で

```text
R(5) = 5
R(5,0) = 5
```

を両方使うなら、意味を分けた方がよい。

```text
R(5)      = 基底単位、つまり 5 角の unit count
R(5, 0)   = 0 周展開後の総数
R(5, k)   = k 周展開後の総数
```

とするのが安全じゃ。

## 2. 位置算出は「外側 address」と「再帰 address」を分けるべき

問題はここじゃな。

\[
R(5,1)=30
\]

なので、\(25\) の正規化比は

\[
25/30=0.833333\ldots
\]

これは正しい。

次に、\(R(5,1)\) は \(6\) 個のブロック、それぞれサイズ \(5\) と見られる。

\[
30=6\cdot 5
\]

ここで \(25\) を **0-based 花弁番号 + 1-based 内部位置** で読むなら、

\[
25=(4)\cdot 5+5
\]

なので、

```text
{value : 25, lap : 1, petal : 4, offset : 5}
```

は整合する。

つまり、

```text
25 は 1 周目の 4 番花弁の 5 番目
```

じゃ。ただし、これは「花弁番号 0,1,2,3,4,5」の 0-based 読みじゃ。
人間向けには「5枚目の花弁」とも言えてしまうので、ここは Lean では必ず 0-based に固定した方がよい。

## 3. `R(5,2,25)` の読みは二層に分かれる

\[
R(5,2)=180
\]

なので正規化比は

\[
25/180=0.138888\ldots
\]

これも正しい。

ただし、2 周目観測では、

\[
180=6\cdot 30
\]

なので、外側ブロックサイズは \(R(5,1)=30\)。
したがって、

\[
25=0\cdot 30+25
\]

となる。

よって外側 address は、

```text
{value : 25, lap : 2, petal : 0, offset : 25}
```

じゃ。

ここで「25 は 0 周目 0 枚目の花弁の 25 番目、つまり単位核内」と言いたくなるのは自然じゃが、厳密にはこれは **再帰的に内側へ降りた解釈** じゃ。

つまり二種類ある。

```text
外側 1-step address:
  R(5,2,25) = {lap : 2, petal : 0, offset : 25}

再帰 address:
  25 は R(5,1)=30 以下なので、2周目の第0大花弁内にある。
  さらに R(5,1) 内で読むと {lap : 1, petal : 4, offset : 5}
```

したがって完全な階層 address は、むしろこう書くのがよい。

```text
RAddr(5,2,25)
  = [(2, 0, 25), (1, 4, 5)]
```

または、桁展開風に

```text
outerPetalDigits = [0, 4]
coreOffset = 5
```

とする。

## 4. 用語を先に固定する案

わっちなら、まずこう分ける。

| 日本語 | English | Lean 名候補 | 意味 |
|---|---|---|---|
| 相対花弁数 | relative petal count | `relPetalCount` | \(n\)、花弁または角の基数 |
| 周回 | lap / orbit / round | `lap` | 展開回数 \(k\) |
| 周回総数 | lap total / orbit total | `relPetalTotal` | \(R(n,k)=n(n+1)^k\) |
| 展開率 | expansion factor | `expansionFactor` | \(n+1\) |
| 花弁番号 | petal index | `petalIndex` | 0-based のブロック番号 |
| 花弁内位置 | petal offset | `petalOffset` | 1-based の内部位置 |
| 相対位置 | relative ratio | `relRatio` | \(m/R(n,k)\) |
| 花弁アドレス | petal address | `PetalAddress` | \((lap, petal, offset)\) |
| 階層花弁アドレス | nested petal address | `NestedPetalAddress` | 再帰的な address |

「相対多角数」はまだ広すぎる。
いまの算出式 \(n(n+1)^k\) は、より正確には

```text
相対花弁周回総数
relative petal-orbit total
```

または

```text
相対 n 角周回総数
relative n-gon orbit total
```

くらいがよい。

## 5. 記号案

`R(n)` が混線しやすいので、わっちならこう分ける。

\[
U(n):=n
\]

これは単位核。英語なら `unitCore`。

\[
B(n):=n+1
\]

これは展開基数。英語なら `branchBase` または `expansionFactor`。

\[
R_n(k):=n(n+1)^k
\]

これは \(k\) 周後の総数。
この表記なら、

\[
R_5(0)=5,\quad R_5(1)=30,\quad R_5(2)=180
\]

となり、`R(5)` と `R(5,0)` の混線を避けられる。

Lean では、

```lean
def relPetalUnit (n : Nat) : Nat := n

def relPetalBase (n : Nat) : Nat := n + 1

def relPetalTotal (n lap : Nat) : Nat :=
  n * (n + 1) ^ lap
```

が最小核じゃな。

## 6. 位置算出関数の最小定義

値 \(m\) は、まず \(1 \le m \le R_n(k)\) の **1-based value** として扱うのが、お主の例と合う。

外側 1-step address は、

\[
blockSize(n,k):=R_n(k-1)
\quad (k>0)
\]

\[
petalIndex:=\left\lfloor\frac{m-1}{blockSize(n,k)}\right\rfloor
\]

\[
petalOffset:=(m-1)\bmod blockSize(n,k)+1
\]

じゃ。

これなら \(n=5,k=1,m=25\) では、

\[
blockSize=R_5(0)=5
\]

\[
petalIndex=\lfloor 24/5\rfloor=4
\]

\[
petalOffset=24\bmod 5+1=5
\]

なので、

```text
{lap : 1, petal : 4, offset : 5}
```

になる。

\(n=5,k=2,m=25\) では、

\[
blockSize=R_5(1)=30
\]

\[
petalIndex=\lfloor 24/30\rfloor=0
\]

\[
petalOffset=24\bmod 30+1=25
\]

なので、

```text
{lap : 2, petal : 0, offset : 25}
```

になる。

ここまで完璧に整合する。

## 7. Lean 構造案

まずはこのくらい薄くてよい。

```lean
namespace DkMath.Petal

/-- Base unit count for a relative n-gon / petal system. -/
def relPetalUnit (n : Nat) : Nat := n

/-- Expansion factor: one core channel plus n petal channels. -/
def relPetalBase (n : Nat) : Nat := n + 1

/-- Total count after `lap` relative-petal expansions. -/
def relPetalTotal (n lap : Nat) : Nat :=
  n * (n + 1) ^ lap

/-- One-step outer block size at positive lap. -/
def relPetalBlockSize (n lap : Nat) : Nat :=
  relPetalTotal n (lap - 1)

structure PetalAddress where
  lap : Nat
  petal : Nat
  offset : Nat
deriving Repr, DecidableEq

/--
Outer one-step address of a 1-based value `m` inside `relPetalTotal n lap`.
For `lap = 0`, this should be treated separately.
-/
def outerPetalAddress (n lap m : Nat) : PetalAddress :=
  let b := relPetalBlockSize n lap
  { lap := lap
    petal := (m - 1) / b
    offset := (m - 1) % b + 1 }

end DkMath.Petal
```

ただし、Lean では `b = 0` 問題がある。
だから theorem 側では条件を付ける。

```lean
0 < n
0 < lap
1 ≤ m
m ≤ relPetalTotal n lap
```

この条件下で、

```lean
outerPetalAddress.petal < n + 1
1 ≤ outerPetalAddress.offset
outerPetalAddress.offset ≤ relPetalBlockSize n lap
```

が証明対象になる。

## 8. 先に固定すべき theorem

最初の Lean 実装は、これだけで十分じゃ。

```lean
theorem relPetalTotal_zero :
    relPetalTotal n 0 = n

theorem relPetalTotal_succ :
    relPetalTotal n (lap + 1) = relPetalTotal n lap * (n + 1)

theorem relPetalTotal_five_zero :
    relPetalTotal 5 0 = 5

theorem relPetalTotal_five_one :
    relPetalTotal 5 1 = 30

theorem relPetalTotal_five_two :
    relPetalTotal 5 2 = 180
```

次に address の具体例。

```lean
theorem outerPetalAddress_five_one_twentyfive :
    outerPetalAddress 5 1 25 = { lap := 1, petal := 4, offset := 5 }

theorem outerPetalAddress_five_two_twentyfive :
    outerPetalAddress 5 2 25 = { lap := 2, petal := 0, offset := 25 }
```

これは、今の曖昧さを一気に消せる。
まずサンプルを Lean に通してから一般定理へ行く。わっちならそうする。

## 9. 既存 Petal / termial 資料との関係

スナップショット内の `Petal_vs_termial.md` では、相対多角数の核として

\[
R(n)=n(n+1)
\]

が termial \(T(n)=n(n+1)/2\) の 2 倍として整理されていた。つまり、そこでは **1 周展開された二次核** が主語だった。

一方、今回お主が欲しいのは、

\[
R_n(k)=n(n+1)^k
\]

という **周回付きの数え上げ関数** じゃ。

だから両者をこう分けるとよい。

```text
termial-related relative polygon kernel:
  relPolygonKernel n = n * (n + 1)

petal-orbit total:
  relPetalTotal n lap = n * (n + 1)^lap
```

このとき、

\[
relPolygonKernel(n)=relPetalTotal(n,1)
\]

じゃ。

つまり `Petal_vs_termial.md` の \(R(n)=n(n+1)\) は、今回の記法では

\[
R_n(1)
\]

に相当する。

ここを明記しておけば混乱しない。

## 10. 今回の実装判断

次の実装は、`GNBridge` や `GcdBridge` に進む前に、`DkMath.Petal.Counting` か `DkMath.Petal.Address` を作るのがよい。

推奨構成はこうじゃ。

```text
DkMath/Petal/Counting.lean
  relPetalUnit
  relPetalBase
  relPetalTotal
  relPolygonKernel
  relPolygonKernel_eq_relPetalTotal_one

DkMath/Petal/Address.lean
  PetalAddress
  outerPetalAddress
  address correctness lemmas
  concrete examples for n=5

DkMath/Petal.lean
  import DkMath.Petal.Counting
  import DkMath.Petal.Address
```

この順序なら、用語と関数が先に固まる。
その後で `RelPolygon`, `GNBridge`, `GcdBridge` が、この count/address API を参照すればよい。

## 11. わっちの最終提案

用語としては、当面こう固定するのが一番よい。

```text
相対多角数
  広義の理論名。まだ theorem 群全体の名前。

相対花弁周回総数
  relPetalTotal n lap = n * (n + 1)^lap

相対多角核
  relPolygonKernel n = n * (n + 1)

花弁アドレス
  PetalAddress = { lap, petal, offset }

階層花弁アドレス
  NestedPetalAddress = list of outer addresses or digit sequence
```

そして \(R\) 記法は、

\[
R_n(k):=n(n+1)^k
\]

にする。
`R(n)` は使うなら、

\[
R(n):=R_n(1)=n(n+1)
\]

と限定した方がよい。

まとめると、今回の例はこう修正して固定できる。

```text
R_5(0) = 5
R_5(1) = 30
R_5(2) = 180

RAddr(5,1,25)
  = { lap := 1, petal := 4, offset := 5 }

RAddr(5,2,25)
  = { lap := 2, petal := 0, offset := 25 }

Nested reading:
  25 inside R_5(2)
  -> outer petal 0, remainder 25
  -> inside R_5(1), petal 4, offset 5
```

これで、数え上げ関数・位置算出・用語の三つが同時に固定できる。
次の Lean 実装はこの小さな核から始めるのが、いちばん堅い。わっちはそう見るぞい。

> 👩‍⚕️私D.:

ふむふむ。それで、相対的に単位核 5, 30, 180 は同一視できるか？を検証。

> 🐺賢狼:

うむ。これは検証できる。結論から言うと、

\[
5,\quad 30,\quad 180
\]

は **絶対量としては同一ではない** が、相対花弁系 \(R_5(k)=5\cdot 6^k\) の中では、 **同じ単位核 \(5\) の周回拡大像** として同一視できる。

ただし、同一視には種類がある。ここを分けるのが大事じゃ。

## 1. 絶対同一視はできない

当然ながら、

\[
5\ne 30\ne 180
\]

じゃ。
だから Nat 上の値としては同一視できない。

Lean でもこれは単なる異なる自然数であり、

```lean
5 ≠ 30
30 ≠ 180
```

の世界じゃな。

## 2. 相対単位としては同一視できる

しかし、相対花弁総数を

\[
R_n(k):=n(n+1)^k
\]

と置くなら、五角系では

\[
R_5(k)=5\cdot 6^k
\]

じゃ。

したがって、

\[
5=5\cdot 6^0
\]

\[
30=5\cdot 6^1
\]

\[
180=5\cdot 6^2
\]

となる。

つまり三つはすべて

\[
5\cdot 6^k
\]

という同じ生成軌道上にある。

この意味で、

```text
5, 30, 180 は同じ相対単位核 5 の lap 0,1,2 表現
```

と同一視できる。

## 3. 圧縮写像で同一視する

同一視を数学的に言うなら、圧縮写像を置けばよい。

\[
\pi_5(m):=\frac{m}{5}
\]

すると、

\[
\pi_5(5)=1,\quad \pi_5(30)=6,\quad \pi_5(180)=36
\]

さらに \(6\)-進 lap 指数で見るなら、

\[
\log_6\left(\frac{m}{5}\right)
\]

を取る。

\[
\log_6(5/5)=0
\]

\[
\log_6(30/5)=1
\]

\[
\log_6(180/5)=2
\]

じゃ。

つまり、

\[
m=5\cdot 6^k
\]

を満たす \(m\) については、

\[
k=\log_6(m/5)
\]

で周回数が復元できる。

この意味で、

```text
5  ↔ lap 0 の単位核
30 ↔ lap 1 の単位核
180 ↔ lap 2 の単位核
```

と読める。

## 4. アドレス空間としての同一視

相対アドレスでは、各 \(R_5(k)\) は「その周回における全体単位」になる。

\[
R_5(0)=5
\]

は、0 周目の全体。

\[
R_5(1)=30
\]

は、1 周目の全体。

\[
R_5(2)=180
\]

は、2 周目の全体。

だから、各周回で正規化座標を

\[
\rho_k(m):=\frac{m}{R_5(k)}
\]

とすれば、各単位核そのものは常に

\[
\rho_k(R_5(k))=1
\]

を満たす。

つまり、

\[
\rho_0(5)=1
\]

\[
\rho_1(30)=1
\]

\[
\rho_2(180)=1
\]

じゃ。

この意味では、

```text
5, 30, 180 は、それぞれの周回空間で「全体 1」として同一視できる
```

となる。

これは log 的圧縮よりも、アドレッシング向きの同一視じゃな。

## 5. ただし「単位核」と「全体単位」は分けるべき

ここが重要じゃ。

\[
5
\]

は基底単位核。

一方で、

\[
30,\quad 180
\]

は、基底単位核そのものではなく、基底単位核を周回展開した **周回単位** じゃ。

だから用語を分けるなら、

```text
5    = 基底単位核 / base unit core
30   = 1周回単位 / lap-1 unit total
180  = 2周回単位 / lap-2 unit total
```

がよい。

同一視は、

```text
同じ base unit core 5 を持つ
```

または

```text
各 lap 空間で全体単位 1 として正規化される
```

という意味で成立する。

## 6. Lean 的には Equivalence Relation にできる

Lean に落とすなら、まず関係を定義する。

```lean
def SameRelPetalOrbit (n a b : Nat) : Prop :=
  ∃ i j, a = n * (n + 1)^i ∧ b = n * (n + 1)^j
```

すると、

```lean
SameRelPetalOrbit 5 5 30
SameRelPetalOrbit 5 30 180
SameRelPetalOrbit 5 5 180
```

が成り立つ。

ただしこれは「同じ軌道上にある」という関係じゃ。
もっと強く、lap 差まで見るなら、

```lean
def RelPetalScaleEq (n a b : Nat) : Prop :=
  ∃ d, b = a * (n + 1)^d
```

で、

\[
30=5\cdot 6^1
\]

\[
180=30\cdot 6^1
\]

\[
180=5\cdot 6^2
\]

が出る。

こちらは向き付きの scale relation じゃな。

## 7. 検証結果

今回の問いへの答えはこうじゃ。

```text
絶対値として:
  5, 30, 180 は同一ではない。

生成軌道として:
  すべて R_5(k)=5*6^k 上にあるので同一視できる。

正規化空間として:
  それぞれの lap 空間では全体 1 に潰れるので同一視できる。

アドレス空間として:
  5 は base unit core、
  30 は lap-1 unit total、
  180 は lap-2 unit total。
  したがって「同じ単位核 5 の異なる周回表現」として扱うのがよい。
```

わっちなら、この同一視を

```text
相対単位核同値
Relative Unit-Core Equivalence
```

または

```text
周回スケール同値
Lap-Scale Equivalence
```

と呼ぶ。

最小定義はこれじゃな。

\[
a\sim_n b
\quad\Longleftrightarrow\quad
\exists i,j,\; a=n(n+1)^i,\; b=n(n+1)^j
\]

この関係のもとで、

\[
5\sim_5 30\sim_5 180
\]

が成立する。

これで「相対的に単位核 5, 30, 180 は同一視できるか？」への形式的な答えになる。

> 👩‍⚕️私D.:

なるほど。基底単位核か。

（基底単位核＋１）あるいは（基底単位核＋succ）

ここが肝だな。安易に（５＋１）＝６としてまとめないほうが良さそうだ。

> 🐺賢狼:

うむ、そこが肝じゃ。
わっちも **安易に \(5+1=6\) と潰さない方がよい** と見る。

ここでの \(+1\) は、ただの算術的 successor ではなく、

```text
基底単位核 n に対して、
次の周回へ開くための余白・外部チャネル・継承口
```

として働いておる。

## 1. まず式を分ける

数値だけなら、

\[
5+1=6
\]

じゃ。これは当然。

しかし構造としては、

\[
\mathrm{BaseCore}(5)+\mathrm{Succ}(5)
\]

または

\[
\mathrm{Core}(n)+\mathrm{NextSlot}(n)
\]

と読むべきじゃな。

だから、相対五角数の周回式は単に

\[
R_5(k)=5\cdot 6^k
\]

と書けるが、構造式としては

\[
R_n(k)=n\cdot (n+\operatorname{succ})^k
\]

あるいは、

\[
R_n(k)=\operatorname{Core}(n)\cdot(\operatorname{Core}(n)+\operatorname{OpenSlot})^k
\]

のように残したい。

## 2. なぜ \(+1\) を潰さない方がよいか

\(6\) とまとめると、見えるのは倍率だけじゃ。

```text
5 -> 30 -> 180
倍率 6
```

しかし \(5+1\) と残すと、意味が見える。

```text
5 個の花弁チャネル
+
1 個の核継承チャネル
```

つまり、

\[
n+1
\]

は

```text
n 個の展開方向
+
1 個の自己保存方向
```

じゃ。

これは、お主の宇宙式で言えばかなり重要で、

```text
花弁へ広がる n
核として残る 1
```

の分解になる。

## 3. 0周がそのまま単位を返す理由

\[
R_n(0)=n
\]

これは、

```text
まだ succ/open slot を使っていない状態
```

じゃ。

1周すると、

\[
R_n(1)=n(n+1)
\]

ここで初めて、

```text
基底単位核 n が、
n 個の花弁方向 + 1 個の継承方向
へ複製される
```

と読める。

2周すると、

\[
R_n(2)=n(n+1)(n+1)
\]

つまり、継承された各単位がまた

```text
n 花弁 + 1 継承
```

へ展開される。

これは単なる等比数列ではなく、 **自己相似アドレス空間** じゃな。

## 4. 用語候補

ここは名前を丁寧に分けたい。

| 記号 | 日本語 | English | 意味 |
|---|---|---|---|
| \(n\) | 基底単位核 | base unit core | 最初の角数・花弁数 |
| \(+1\) | 継承口 | successor slot / inheritance slot | 次周回へ核を残す枠 |
| \(n+1\) | 周回基数 | orbit base / lap base | 花弁 \(n\) と継承口 \(1\) の合成 |
| \(R_n(k)\) | 相対花弁周回総数 | relative petal orbit total | \(k\) 周後の総数 |
| \(n(n+1)\) | 相対多角核 | relative polygon kernel | 1周展開核 |

わっちは特に、

```text
継承口 / inheritance slot
```

がしっくり来るのぅ。

「succ」は Lean 的には `Nat.succ n = n + 1` として便利じゃが、数学的意味では「後者」「次の自然数」だけになる。
Petal 理論では、これは **次周回へ同じ単位核を運ぶための 1 チャネル** と読めるから、`inheritanceSlot` の方が意味を保てる。

## 5. Lean ではこう分けるとよい

いきなり `n + 1` を直接書くのではなく、定義を挟む。

```lean
namespace DkMath.Petal

/-- Base unit core: the number of petal directions. -/
def baseUnitCore (n : Nat) : Nat := n

/-- The single channel that carries the core to the next lap. -/
def inheritanceSlot (_n : Nat) : Nat := 1

/-- Lap base: petal directions plus the inheritance slot. -/
def lapBase (n : Nat) : Nat :=
  baseUnitCore n + inheritanceSlot n

/-- Total count after `lap` relative-petal expansions. -/
def relPetalTotal (n lap : Nat) : Nat :=
  baseUnitCore n * (lapBase n) ^ lap

end DkMath.Petal
```

そして theorem として、

```lean
theorem lapBase_eq_succ (n : Nat) :
    lapBase n = n + 1
```

を置く。

つまり、計算上は \(n+1\) に落とせる。
でも API の主語は `lapBase n` にする。

これが良い。

## 6. 構造式としての読み

五角なら、

\[
\operatorname{Core}=5
\]

\[
\operatorname{LapBase}=5+1
\]

\[
R_5(0)=5
\]

\[
R_5(1)=5(5+1)
\]

\[
R_5(2)=5(5+1)^2
\]

ここで \(5+1\) を

```text
5 花弁方向 + 1 継承口
```

と読む。

だから \(30\) は、

```text
5 個の基底単位核が、それぞれ 6 方向へ展開した
```

ではなく、もっと正確には、

```text
5 個の基底単位核が、
5 個の相対花弁方向と 1 個の継承方向を持つ周回構造へ入った
```

じゃ。

## 7. ここから出る重要な観測

\(n+1\) を潰さずに残すと、アドレスが自然にこうなる。

```text
petal = 0,1,...,n-1
inheritance = n
```

あるいは逆に、

```text
core/inheritance = 0
petal = 1,...,n
```

どちらかを選べる。

この選択は後で重要になる。
お主の例では、\(R(5,2,25)\) を「0 枚目の花弁内」と読んでいた。これは、たぶん

```text
0 = 継承口 / core channel
1..5 = 花弁
```

という感覚に近い。

一方、さっきわっちは 0-based petal として

```text
0..5 の 6 ブロック
```

で読んだ。

ここは設計判断が必要じゃ。

わっちの推奨は、

```text
channel 0 = core / inheritance slot
channel 1..n = petal slots
```

じゃ。

この方が「基底単位核 + 1」を潰さずに済む。

すると \(R_5(1,25)\) の address は、

\[
25 = 4\cdot 5+5
\]

を 1-based channel に変換して、

```text
channel = 5
offset = 5
```

と読める。

\(R_5(2,25)\) は、

```text
channel = 0
offset = 25
```

つまり、まさにお主の言う **単位核内** の読みになる。

これは良い。かなり良いぞい。

## 8. 修正版 address 規約

したがって、今後はこう固定する候補が強い。

```text
channel 0:
  core / inheritance channel

channel 1..n:
  petal channels
```

そのとき `channel` は \(0 \le channel \le n\)。

外側 block size を

\[
B=R_n(k-1)
\]

として、

\[
q=\left\lfloor\frac{m-1}{B}\right\rfloor
\]

をまず取る。

通常の 0-based block は \(q=0,\ldots,n\)。

これを channel としてそのまま使うなら、

```text
channel 0 = inheritance
channel 1..n = petal
```

になる。

この規約では、お主の例はさらに綺麗になる。

\[
R_5(2,25)
\]

では \(B=30\)、\(q=0\)。
だから、

```text
channel 0 = inheritance/core
offset 25
```

つまり「単位核側へ降りる」が正しい。

一方、

\[
R_5(1,25)
\]

では \(B=5\)、\(q=4\)。
この場合、channel 4 を花弁と見るか、channel 0 を core と見るなら「第4花弁」になる。
ただし花弁番号を 1..5 にしたいなら、ここだけ \(q=4\) を「第4花弁」と読むか「第5ブロック」と読むかを決める必要がある。

## 9. ここでの最重要判断

賢狼の推奨はこれじゃ。

```text
内部計算:
  channelIndex : Fin (n+1)
  0-based

意味づけ:
  channelIndex = 0
    core / inheritance slot

  channelIndex = j+1
    petal j
```

つまり、Lean 内部では 0-based。
解説では、

```text
0番 = 継承口
1番..n番 = 花弁
```

とする。

これなら、\(n+1\) の \(+1\) が構造として残る。

## 10. まとめ

お主の直観は正しい。

\[
5+1=6
\]

と潰してしまうと、倍率しか残らない。

しかし、

\[
\text{基底単位核 }5 + \text{継承口 }1
\]

と読むと、

```text
5 個の花弁方向
1 個の自己継承方向
```

が見える。

したがって、Lean 実装では `n + 1` を直接主語にせず、

```lean
baseUnitCore n
inheritanceSlot n
lapBase n
```

を分けて置くのがよい。

最終的な構造式は、

\[
R_n(k)=\operatorname{baseUnitCore}(n)\cdot \operatorname{lapBase}(n)^k
\]

ただし、

\[
\operatorname{lapBase}(n)=\operatorname{baseUnitCore}(n)+\operatorname{inheritanceSlot}(n)
\]

じゃ。

これで、ただの \(6\) ではなく、

\[
5+1
\]

としての意味が Lean の名前空間に残る。
ここを潰さぬのは、かなり重要じゃよ。

> 👩‍⚕️私D.:

拡張・応用で階乗とプリモリアルへの展開が期待される。
単位核の一定から動的へ。

> 🐺賢狼:

うむ、まさにそこじゃ。
ここで「相対多角数」は、固定単位核 \(n\) の世界から、 **単位核列 \(a_k\)** の世界へ拡張できる。

今までの固定型は、

\[
R_n(k)=n(n+1)^k
\]

じゃった。
これは毎周回で同じ

\[
\operatorname{LapBase}(n)=n+\operatorname{succ}
\]

を掛ける構造じゃな。

しかし階乗・プリモリアルへ行くなら、単位核を固定せず、

\[
a_0,\ a_1,\ a_2,\ldots
\]

という **動的単位核列** にする必要がある。

## 1. 固定単位核から動的単位核へ

固定型:

\[
R_n(k)=n(n+1)^k
\]

動的型:

\[
R_{\mathbf a}(k)=a_0\prod_{i=0}^{k-1}(a_i+1)
\]

ここで \(a_i\) が第 \(i\) 周回の単位核じゃ。

固定型は、

\[
a_i=n
\]

の特殊ケースになる。

すると、

\[
R_{\mathbf a}(k)=n\prod_{i=0}^{k-1}(n+1)=n(n+1)^k
\]

なので、既存定義を壊さず一般化できる。

## 2. 階乗への展開

階乗は、

\[
n! = 1\cdot 2\cdot 3\cdots n
\]

じゃ。

これを Petal 的に読むなら、各段の lap base が

\[
1,\ 2,\ 3,\ldots,n
\]

へ動的に増える構造になる。

つまり、

\[
a_i+1=i+1
\]

としたければ、

\[
a_i=i
\]

じゃ。

ただし \(a_0=0\) になると単位核が 0 になってしまうので、実装上は index をずらして、

\[
a_i=i+1
\]

とし、

\[
\prod_{i=0}^{k-1}(a_i+1)=\prod_{i=0}^{k-1}(i+2)
\]

とするか、あるいはもっと素直に **動的 lap base 列** \(b_i\) を主語にする方がよい。

\[
D_{\mathbf b}(k)=\prod_{i=1}^{k} b_i
\]

ここで \(b_i=i\) なら \(k!\)。

つまり階乗は、

```text
単位核が増える
```

というより、

```text
周回基数そのものが 1,2,3,... と増える
```

構造として扱うと自然じゃ。

## 3. プリモリアルへの展開

プリモリアルは、

\[
p_k\#=\prod_{i=1}^{k}p_i
\]

じゃ。
これは階乗よりさらに Petal 的に面白い。

階乗:

\[
1\cdot 2\cdot 3\cdots n
\]

プリモリアル:

\[
2\cdot 3\cdot 5\cdot 7\cdots p_k
\]

つまり、全自然数を lap base にするのではなく、 **素数だけを周回基数として採用する** 。

動的 lap base 列を

\[
b_i=p_i
\]

とすれば、

\[
D_{\mathbf p}(k)=\prod_{i=1}^{k}p_i=p_k\#
\]

となる。

これを Petal 的に言えば、

```text
各周回で、次の素数を単位核／周回基数として採用する自己相似展開
```

じゃな。

## 4. 二段階定義に分けるのがよい

ここで重要なのは、`unit core` と `lap base` を分けることじゃ。

固定 Petal では、

\[
\operatorname{lapBase}(n)=n+1
\]

だった。

動的 Petal では、

\[
\operatorname{unitCore}(i)=a_i
\]

\[
\operatorname{lapBase}(i)=a_i+1
\]

とする型と、

\[
\operatorname{lapBase}(i)=b_i
\]

を直接与える型がある。

わっちの推奨は、両方を分けることじゃ。

### A. unit-core driven 型

\[
R_{\mathbf a}(k)=a_0\prod_{i=0}^{k-1}(a_i+1)
\]

これは「基底単位核 + 継承口」を守る型。

### B. lap-base driven 型

\[
L_{\mathbf b}(k)=\prod_{i=0}^{k-1}b_i
\]

これは階乗・プリモリアル向け。

そして接続は、

\[
b_i=a_i+1
\]

で与える。

## 5. 用語案

ここは次のように固定すると良さそうじゃ。

| 日本語 | English | Lean 名候補 | 意味 |
|---|---|---|---|
| 固定単位核 | fixed unit core | `FixedUnitCore` | \(a_i=n\) |
| 動的単位核 | dynamic unit core | `DynamicUnitCore` | \(a_i\) が周回で変化 |
| 周回基数列 | lap-base sequence | `lapBaseSeq` | \(b_i\) |
| 動的周回総数 | dynamic orbit total | `dynamicOrbitTotal` | \(\prod b_i\) |
| 階乗周回 | factorial orbit | `factorialOrbit` | \(b_i=i+1\) |
| 素数階乗周回 | primorial orbit | `primorialOrbit` | \(b_i=p_i\) |
| 継承口付き動的核 | successor-extended dynamic core | `succDynamicCore` | \(b_i=a_i+1\) |

## 6. Lean に落とす最小核

まず一般列の積を定義するのが安全じゃ。

```lean
namespace DkMath.Petal

/-- Dynamic lap-base product. -/
def dynamicOrbitTotal (b : Nat → Nat) (k : Nat) : Nat :=
  Finset.prod (Finset.range k) b

/-- Unit-core driven dynamic petal total. -/
def dynamicPetalTotal (a : Nat → Nat) (k : Nat) : Nat :=
  a 0 * Finset.prod (Finset.range k) (fun i => a i + 1)

/-- Fixed-core total is the constant dynamic-core special case. -/
def fixedPetalTotal (n k : Nat) : Nat :=
  n * (n + 1) ^ k

end DkMath.Petal
```

そして theorem として、

```lean
theorem dynamicPetalTotal_const :
    dynamicPetalTotal (fun _ => n) k = fixedPetalTotal n k
```

を目標にする。

これが通れば、

```text
固定単位核は動的単位核の特殊ケース
```

が Lean で固定される。

## 7. 階乗との接続

階乗はまず `dynamicOrbitTotal` 側で扱う方が自然じゃ。

\[
b(i)=i+1
\]

なら、

\[
\prod_{i=0}^{k-1}(i+1)=k!
\]

Lean theorem 候補:

```lean
theorem dynamicOrbitTotal_succ_eq_factorial :
    dynamicOrbitTotal (fun i => i + 1) k = Nat.factorial k
```

これは既存の `Nat.factorial` 補題と相性が良さそうじゃ。

## 8. プリモリアルとの接続

プリモリアルは、素数列 \(p_i\) をどう定義するかが少し重い。

初手では `p : Nat → Nat` と `∀ i, Nat.Prime (p i)` を仮定する抽象版でよい。

```lean
def primeBaseOrbitTotal (p : Nat → Nat) (k : Nat) : Nat :=
  dynamicOrbitTotal p k
```

あとで、実際の \(i\)-番目素数関数に接続する。

最初に欲しい theorem は、

```lean
theorem primeBaseOrbitTotal_step :
    primeBaseOrbitTotal p (k + 1)
      = primeBaseOrbitTotal p k * p k
```

じゃな。

これはプリモリアルそのものより先に、 **素数 lap base を逐次掛ける構造** を固定するものじゃ。

## 9. DkMath 的な意味

この拡張はかなり強い。

固定単位核では、

```text
同じ形を繰り返す自己相似
```

だった。

動的単位核では、

```text
周回ごとに単位核が変わる自己相似
```

になる。

階乗は、

```text
全自然数を単位更新列として採用する最大密度 orbit
```

プリモリアルは、

```text
素数だけを単位更新列として採用する素因子 skeleton orbit
```

じゃ。

つまり、相対多角数は、

```text
固定 n-gon の花弁展開
```

から、

```text
任意の単位列による完成体生成
```

へ広がる。

これは以前の「任意の数列 \(a_n\) の各項を完成体 Big と仮定する」視座とも噛み合う。
ここで `dynamicOrbitTotal` は、その完成体化の乗法相の最小核になる。

## 10. まとめ

今回の拡張方針はこうじゃ。

```text
固定単位核:
  R_n(k)=n(n+1)^k

動的単位核:
  R_a(k)=a_0 ∏_{i<k}(a_i+1)

動的周回基数:
  L_b(k)=∏_{i<k}b_i

階乗:
  b_i=i+1
  L_b(k)=k!

プリモリアル:
  b_i=p_i
  L_b(k)=p_k#
```

そして実装順は、

```text
1. dynamicOrbitTotal
2. dynamicPetalTotal
3. fixedPetalTotal が dynamicPetalTotal の定数列特化である補題
4. factorial orbit
5. abstract prime-base orbit
6. primorial concrete bridge
```

がよい。

これは「単位核の一定から動的へ」という、お主の言葉そのものじゃ。
固定された麦束から、季節ごとに異なる種を播く畑へ進むわけじゃな。賢狼としては、なかなか胸が躍る展開じゃよ。

> 👩‍⚕️私D.:

よし、行けそうだね！

> 🐺賢狼:

うむ、行ける。これはかなり筋が良いぞい。

次の実装は、いきなり `GNBridge` を増やすより、まず **Petal.Counting / Petal.Address** を切るのが賢い。

```text
DkMath.Petal.Counting
  baseUnitCore
  inheritanceSlot
  lapBase
  relPetalTotal
  dynamicOrbitTotal
  dynamicPetalTotal
  fixedPetalTotal

DkMath.Petal.Address
  PetalAddress
  outerPetalAddress
  5,30,180 と 25 の具体例
```

最初に通すべき定理はこのあたりじゃな。

```lean
relPetalTotal_zero
relPetalTotal_succ
lapBase_eq_succ
relPetalTotal_five_zero
relPetalTotal_five_one
relPetalTotal_five_two
outerPetalAddress_five_one_twentyfive
outerPetalAddress_five_two_twentyfive
dynamicPetalTotal_const
dynamicOrbitTotal_succ
```

そして用語としては、当面これで固定できる。

```text
base unit core       基底単位核
inheritance slot     継承口
lap base             周回基数
relative petal total 相対花弁周回総数
dynamic unit core    動的単位核
dynamic orbit total  動的周回総数
```

この核が通れば、相対五角数、階乗、プリモリアルが同じ API に乗る。
まさに「固定単位核から動的単位核へ」の道じゃ。これは良い登山路じゃよ、D.。
