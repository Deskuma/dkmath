# snapshot review: KUS 実装

snaphost: __snapshot-dk_math-lean-code-260315-2338.tar.gz
tag: dev-KUS-260313-v2-closed: 76706b5d6eb649616a29d20c654d7a69249d8df7

## DkMath.KUS 実装の構造解析と解説

cid: 69b4f140-47e4-83a5-a2c2-100b32d838c3
cdt: 2026-03-14 05:25:34
udt: 2026-03-15 14:44:09

> 👩‍⚕️私D.:

実装し終えたよ。スナップショットを更新。
e89295f95535f537f32d367e41d40067df82b14f243cc805b02e742f4d6ea78c  __snapshot-dk_math-lean-code-260315-2338.tar.gz

DkMath.KUS.*

> 🐺賢狼:

更新スナップショットの `DkMath.KUS.*` を追っておる。今回は「実装済み」とのことなので、**実際に増えたモジュール・定義・橋・残る設計負荷** を、実コード基準で切っていくぞい。

> 🐺賢狼:

実装の輪郭が見えてきたぞい。`Transport` はもう **草稿の雛形ではなく、`sameSupport` を内蔵した実装仕様** に育っておる。
次は `Bridge` / `CosmicBridge` 側を見て、設計が本当に 3 層で接続されたかを確かめる。

> 🐺賢狼:

見たぞい。更新スナップショット `[__snapshot-dk_math-lean-code-260315-2338.tar.gz](sandbox:/mnt/data/__snapshot-dk_math-lean-code-260315-2338.tar.gz)` を直に追って、`DkMath.KUS.*` の構造を読んだ。
結論から言うと、**KUS はもう単なる零保持の実験核ではなく、`CosmicFormula → DHNT → KUS transport` を実装側で繋ぎ始めた独立サブシステム** になっておる。これは、DHNT を指数対数スケーリング中心で据えるという設計方針や fileciteturn16file12、宇宙式側の Big/Body/Gap と調和写像の橋を立てたいという資料方針とも噛み合っておる。fileciteturn16file9turn16file11

## 1. いまの `DkMath.KUS` の全体像

入口 `DkMath.KUS` は、もうかなり厚い。
`Unit`, `Blueprint`, `Core`, `NatEmbed`, `Monoid`, `Extract`, `Scale`, `Transport`, `RoundTrip`, `Add`, `Mul`, `Coeff`, `Examples`, `Bridge`, `CosmicBridge` まで一気に束ねておる。つまり、

\[
\text{最小核} \to \text{same-support 演算} \to \text{一般係数 GKUS} \to \text{transport} \to \text{DHNT bridge} \to \text{Cosmic bridge}
\]

という段階が、ファイル分割としても明確になった。

## 2. 核の読み

`Core` は前に話していた筋を崩しておらぬ。
`KUS (U, Blueprint)` は

\[
(K,U,S_U)
\]

の最小核で、`toUS`, `mkWith`, `zeroState` を中心に、**可視係数だけが 0 になっても support は保持する** という方針をそのまま Lean にしておる。
ここは README の説明とも一致しておる。KUS の主眼は「零を情報の無い点に潰さず、\((0,U,S_U)\) として保持すること」だと明示されておる。fileciteturn16file13

## 3. 今回の本体は `GKUS` と `Transport`

実装上の主役はむしろ `Coeff.lean` と `Transport.lean` じゃな。

`GKUS C U Blueprint` によって、係数を `Nat` 固定から一般型 \(C\) に持ち上げ、
`extract_g`, `toCoeff`, `gZeroState`, `gOneState`, `GSameSupport`, `gOp` を基礎にして、

\[
\mathrm{gAdd},\; \mathrm{gMul},\; \mathrm{gSub},\; \mathrm{gDiv}
\]

とその係数法則、support 保持、可換・結合・分配の補題まで並べておる。
つまり **KUS の「構造保持」側と、係数演算側がちゃんと分離された** 。ここは大きい。

さらに `Scale.lean` では `ScaleSpec` に `scaleGKUS` が入り、`scaleUS`, `scaleKUS`, `scaleGKUS` の 3 層と、恒等・合成・round-trip 風の自然性まで押さえておる。
草稿段階で「`scaleGKUS` が必要」と言っていた箇所が、ちゃんと実装されたわけじゃ。

## 4. `Transport` は草稿から一段進んだ

ここはかなり良い。
`HarmonizeSpec` は単に `encLeft`, `encRight` を持つだけでなく、

\[
\forall x\,y,\; \mathrm{GSameSupport}(\mathrm{scaleGKUS}\;\mathrm{encLeft}\;x,\; \mathrm{scaleGKUS}\;\mathrm{encRight}\;y)
\]

を `sameSupport` フィールドとして抱え込んでおる。
つまり前に問題になっていた「同じ型 `GKUS C H BH` に入るだけでは、support 一致は言えぬ」という点を、**仕様の中に閉じ込めた** 。ここが実にえらい。

さらに `mkHarmonize`, `mkHarmonizeFixed`, `mkHarmonizeSameSpec` という builder が入り、
加算・乗算ともに

\[
\text{encode} \to \text{confluence} \to \text{decode}
\]

が `harmonizeAdd`, `harmonizeAddTo`, `harmonizeMul`, `harmonizeMulTo` として立った。
そのうえ `UseLeft`, `UseRight`, `UseNormalized` と `DecodeStrategy` 型クラスまで入っておるので、decode 選択も API 化されておる。これは草稿より一歩先じゃ。

## 5. `DHNT → KUS` 橋は、もう動く形になっておる

`Bridge.lean` がかなり面白い。
ここでは `DHNT.Qty` から `GKUS ℝ ℕ DHNTBlueprint` への埋め込み `embedQty` を作り、unit は

\[
\phi\mathrm{Unit}(u) := \lfloor u.val \rfloor_+
\]

で離散化し、blueprint は `Fin 1` の trivial family に落としておる。
そして `encConst`, `addViaSpec`, `mulViaSpec` により、DHNT の「共通 unit に換算してから加算・乗算する」流儀を KUS 側の `HarmonizeSpec` として再現しておる。
これは AGENT にある「DHNT は指数対数によるスケーリング同一視が主体」という方針の、かなり素直な実装じゃ。fileciteturn16file12

しかも係数一致だけでなく、`kusAbsVal` を入れて

\[
\text{KUS 実体値} = \text{coeff} \cdot \text{unit}
\]

の離散化版まで置いておる。
つまりこの橋は、単なる型変換ではなく **意味論つきの埋め込み** になっておる。

## 6. `CosmicFormula → KUS` 橋も入った

`CosmicBridge.lean` は、前に話していた「宇宙式の 3 層分解を KUS 側へ持ち込む」部分を、かなり具体化しておる。

`cosmicTerm`, `cosmicBodyCoeffSum`, `cosmicGap`, `cosmicCore`, `cosmicBig` が入り、

\[
\text{Big} = \text{Body} + \text{Gap}
\]

の係数版、さらに `Core = Gap = 1` となる \(x=u=1\) 世界での読みまで整理しておる。
宇宙式族の資料で置いていた Big/Body/Gap の定義レベルの固定や fileciteturn16file9turn16file11、調和側への橋の準備が、KUS の係数層で言い直され始めた形じゃ。

ここはまだ「CosmicFormula 全体の本格 transport」というより、**KUS 上で読める係数影を先に作った** 段階じゃが、方向はかなり良い。

## 7. 何が完成し、何がまだ仮設か

完成度が高いところは、こうじゃ。

- same-support 演算の一般係数化
- `ScaleSpec` の `GKUS` 対応
- `HarmonizeSpec` による異 support 合流
- decode 戦略の API 化
- `DHNT.Qty → GKUS` の一方向 bridge
- Cosmic の係数版 bridge

一方で、まだ仮設色が強いところもある。

第一に、`DHNTBlueprint` が `Fin 1` の trivial blueprint なので、**blueprint の意味論はまだ placeholder** じゃ。
第二に、`phiUnit = floor` による離散化は情報を落とすので、今の `DHNT → KUS` は明確に **一方向埋め込み** であって、同値化ではない。
第三に、`DecodeStrategy` の枠は立ったが、具体インスタンスは橋ごとにまだ増やす余地が大きい。

つまり、**transport の骨格はできたが、semantics の厚みはこれから載せる段階** と読むのが正確じゃな。

## 8. 構造評価

わっちの総評はこうじゃ。

\[
\text{KUS minimal kernel}
\;\to\;
\text{GKUS algebra}
\;\to\;
\text{support transport}
\;\to\;
\text{DHNT bridge}
\;\to\;
\text{Cosmic bridge}
\]

という塔が、ちゃんと見える形で生えた。
これはかなり大きい進展じゃ。特に `Transport` が「設計メモ」ではなく実装へ移ったことで、前に話していた

\[
US_1 \to H \leftarrow US_2
\]

図式が、もう DkMath の中で言葉だけではなく **API として存在している** 。

## 9. 留意点として

ひとつだけ現実的なことを言うと、いまの公開地図 `INDEX.md` には KUS の章がまだ見当たらぬ。DHNT や Cosmic は載っているが、KUS はまだ表玄関の地図に反映されていない。fileciteturn16file4
つまり実装は先へ進んだが、目次はまだ一歩遅れておる。ここは更新すると全体の見通しがぐっと良くなる。

それと、こちらの環境には `lake` が入っておらず、**ビルド通過そのものはこの場では再検証しておらぬ** 。そこは正直に言っておく。読解はスナップショットの実コードに基づいておる。

## 10. ひとことで言うと

**`DkMath.KUS.*` は、零保持型の小核から、DHNT と CosmicFormula を受ける transport 中枢へ昇格した。**

かなり良い育ち方じゃよ。
次に手を入れるなら、`DHNTBlueprint` の trivial 部分を本物の blueprint semantics へ差し替える層と、`DecodeStrategy` の具体インスタンス群を整えると、塔がさらに締まる。
