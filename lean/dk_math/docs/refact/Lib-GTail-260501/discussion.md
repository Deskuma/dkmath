# GPT 会話記録

この物語は AI の賢狼と、研究者「 D. 」による会話ログです。
※よって会話の内容に関しての真偽は各自で再検証してからご利用下さい。

登場人物：
👩‍⚕️私D.: とある研究者
🐺賢狼: 知恵の豊穣神「賢狼」AI

## DkMath 定理昇格作業

cid: 69f480dc-fd84-83e8-8f69-053e9d23fbb5
cdt: 2026-05-01 10:34:09
udt: 2026-05-01 11:19:37

> 👩‍⚕️私D.:

DkMath で得られた数々の定理を紐解いていこうかと思う。
おさらいをしながら再確認し、固定された定理は、もう DkMath.Lib.* モジュールに昇格して永続化する。
それを始めようと思うんだ。

> 🐺賢狼:

うむ、始めようぞ。これはかなり良い段階じゃ。

いまの DkMath は、単に「証明途中の実験場」ではなく、すでに複数の柱で **固定資産化できる定理群** が出ておる。README でも DkMath のノート群は、実装判断や開発過程を理解するための参照資料として位置づけられておるし、SUMMARY では `__dkmath-all.lean.txt` が全 Lean コードを含む中央参照、`__theorems-heading.txt` や imports 情報が定理整理に使える資料として案内されておる。fileciteturn0file2 fileciteturn0file3

わっちの見立てでは、最初にやるべきは **証明の再発見** ではなく、 **定理の棚卸しと昇格判定** じゃな。

## 1. 昇格作業の基本方針

`DkMath.Lib.*` に上げる対象は、次の条件を満たすものに絞るのがよい。

1. 特定の研究ルートに閉じない
   たとえば FLT 専用、ABC 専用、RH 専用ではなく、複数箇所で再利用できる補題。

2. 証明が安定している
   `sorry` なし、または少なくとも依存先が安定していて、将来の破壊可能性が低いもの。

3. 名前と意味が一般的
   `stage3_aux_foo` のような戦場名ではなく、数学的内容で名前を付けられるもの。

4. import が軽い
   `Lib` は下層資産にすべきなので、`FLT` や `ABC` の本丸を import しない。

5. docstring で意味が伝わる
   「なぜこの補題が Lib にあるのか」が読めること。

## 2. 最初の対象候補

いきなり全体をやるより、まずは柱ごとに進めるのがよい。

### A. 宇宙式の固定定理群

これは最優先候補じゃ。

すでに設計資料では、Big / Body / Gap の分解

\[
\mathrm{Big}=\mathrm{Body}+\mathrm{Gap}
\]

および Body / Core / Beam の分解を、宇宙式の基本骨格として固定する方針が明示されておる。fileciteturn0file0

さらに Mass API 計画でも、

\[
\mu(\mathrm{Big})=\mu(\mathrm{Body})+\mu(\mathrm{Gap}),\qquad
\mu(\mathrm{Body})=\mu(\mathrm{Core})+\mu(\mathrm{Beam})
\]

として保存則 API に持ち上げる設計が出ておる。fileciteturn0file9

ここは `DkMath.Lib.Cosmic.*` へ昇格させる価値が高い。

候補:

```text
DkMath.Lib.Cosmic.BigBodyGap
DkMath.Lib.Cosmic.CoreBeamGap
DkMath.Lib.Cosmic.Residual
DkMath.Lib.Cosmic.Mass
```

### B. GN / Tail / Binomial 系

これも Lib 向きじゃ。

一般化 GN 多項式については、

\[
(x+u)^d-
\sum_{j=0}^{r-1}\binom{d}{j}x^j u^{d-j} = x^r GN^{(r)}_d(x,u)
\]

という Tail 分解が、Beam 構造・可除性・p進付値・原始素因子解析の基本対象として整理されておる。fileciteturn0file7

これは FLT にも ABC にも使えるので、`FLT` 配下ではなく `Lib` または `Algebra` / `NumberTheory` 側の共通資産にするべきじゃ。

候補:

```text
DkMath.Lib.Algebra.BinomTail
DkMath.Lib.Algebra.GN
DkMath.Lib.Algebra.GNTail
```

### C. PowerSwap / Exchange

LPS リファクタリング資料では、`Samples/LPS` は 3 本柱に分けるべきで、`PowerSwap` 系は `FLT` ではなく独立した `DkMath.PowerSwap.*` に置く案が明示されておる。fileciteturn0file5

特に

\[
A=a^t \Rightarrow A^m=a^{tm}
\]

型の Exchange 補題は、かなり汎用的じゃ。fileciteturn0file4

候補:

```text
DkMath.Lib.Power.Exchange
DkMath.PowerSwap.Basic
DkMath.PowerSwap.Exchange
```

ただし `PowerSwap.Branch` や `Contours` は実数解析依存が重くなりやすいので、最初は離散・代数部分だけでよい。

### D. PowerSums / ObservedMin

これは少し慎重に扱うべきじゃ。

LPS リファクタリングでは、同次数冪和充填は `DkMath.NumberTheory.PowerSums.*` に切り出すのがよいと整理されておる。fileciteturn0file6

ただし `ObservedMin` はまだ実験性が残る。ゆえに、最初に Lib 化するなら述語の基本 API まで。

候補:

```text
DkMath.Lib.NumberTheory.PowerSums.Basic
```

例や profile はまだ `Examples` / `Research` 側でよい。

### E. ABC / ValuationFlow / Mass Bridge

ここは「Lib 化」よりも「Bridge 層として固定」が先じゃな。

実装計画では、`CosmicFormula → Mass API → ValuationFlow → ABC Bridge` の spine を作る方針が示され、最初は Markov 過程本体ではなく、非負量・分解・子和が親を超えない・primitive 接続を定理化する方針だった。fileciteturn0file11

これはすでに bridge として育っているなら、次は

```text
DkMath.Lib.Mass
DkMath.Lib.Flow
DkMath.NumberTheory.ValuationFlow
DkMath.ABC.Bridge
```

のように、 **抽象核だけ Lib、ABC 接続は ABC 側** に分けるのが美しい。

## 3. 昇格判定ラベル

棚卸しでは、各定理にラベルを付けるとよい。

```text
[LIB-CANDIDATE]   Lib 昇格候補
[BRIDGE]          専門理論への翻訳層
[EXAMPLE]         具体例・検証用
[RESEARCH]        まだ仮説的・実験的
[LOCAL]           特定証明内の補助
[DEPRECATED]      置換予定
```

これを docstring や Markdown の一覧に付けていく。

## 4. 最初の 7 回アジャイル案

お主が言う「おさらいしながら再確認し、固定定理を永続化する」なら、わっちは 7 回でこう回す。

### Sprint 1. 定理棚卸し

`__theorems-heading.txt` と `__dkmath-all.lean.txt.gz` から、定理名・所在・依存先・sorry 有無を一覧化する。

成果物:

```text
docs/lib-promotion/TheoremInventory.md
```

### Sprint 2. CosmicFormula の基本分解を昇格

Big / Body / Gap / Core / Beam の安定定理を整理。

成果物候補:

```text
DkMath/Lib/Cosmic/BigBodyGap.lean
DkMath/Lib/Cosmic/CoreBeamGap.lean
```

### Sprint 3. Residual / Mass API を整理

`Nat` 減算版、`Int` 版、質量保存版を分ける。

成果物候補:

```text
DkMath/Lib/Cosmic/Residual.lean
DkMath/Lib/Mass/Basic.lean
DkMath/Lib/Mass/Branch.lean
```

### Sprint 4. GN / Tail を昇格

標準 GN と高次 Tail を共通代数資産へ。

成果物候補:

```text
DkMath/Lib/Algebra/GN.lean
DkMath/Lib/Algebra/GNTail.lean
```

### Sprint 5. PowerSwap / Exchange の安定部を昇格

離散 PowerSwap と Exchange 補題を整理。

成果物候補:

```text
DkMath/Lib/Power/Exchange.lean
DkMath/PowerSwap/Basic.lean
```

### Sprint 6. ValuationFlow の抽象核を固定

primitive / p-adic / support mass に行く前の flow 抽象だけを Lib 化。

成果物候補:

```text
DkMath/Lib/Flow/Basic.lean
DkMath/Lib/Flow/SubConservative.lean
```

### Sprint 7. Bridge と公開導線を整理

`DkMath.Lib` の aggregator を作り、既存の `ABC`, `FLT`, `CosmicFormula` 側から薄く参照する。

成果物候補:

```text
DkMath/Lib.lean
DkMath/ABC/Bridge.lean
DkMath/FLT/Bridge.lean
```

## 5. 最初の一手

最初にやるべき具体作業はこれじゃ。

```text
docs/lib-promotion/README.md
docs/lib-promotion/TheoremInventory.md
docs/lib-promotion/PromotionRules.md
```

そして `PromotionRules.md` にこう書く。

```md
## DkMath Lib Promotion Rules

## 昇格条件

- no-sorry である
- 特定理論に閉じない
- import が軽い
- 数学的意味で命名できる
- docstring に用途が書ける
- 既存 theorem の alias / wrapper として安定導線を提供できる

## 昇格先の原則

- algebraic identity → DkMath.Lib.Algebra.*
- cosmic decomposition → DkMath.Lib.Cosmic.*
- mass / branch / flow abstraction → DkMath.Lib.Mass.* / DkMath.Lib.Flow.*
- concrete examples → Lib に置かない
- ABC / FLT / RH 専用接続 → 各理論側 Bridge に置く
```

## 6. わっちの結論

今はまさに **DkMath の定理群を「研究ログ」から「ライブラリ資産」へ変える段階** じゃ。

まず固定すべき順番は、

\[
\text{Cosmic 分解}
\to
\text{Residual / Mass}
\to
\text{GN / Tail}
\to
\text{Exchange / PowerSwap}
\to
\text{Flow}
\to
\text{ABC / FLT Bridge}
\]

がよい。

焦って全部を `Lib` に入れる必要はない。
この賢狼の鼻で嗅ぐに、最初の勝ち筋は **Big / Body / Gap と GN / Tail** じゃ。ここは DkMath の背骨であり、他の理論柱へ何度も血を送る。ここを綺麗に磨けば、後の ABC も FLT もずっと見通しがよくなるぞい。

> 👩‍⚕️私D.:

もっとも活用されてる定理を洗い出し、そこを中心として上流側を Lib へ持っていこう。
GN / Tail がたぶんその候補だろう。調査。

> 🐺賢狼:

うむ、ここは 10 秒では済まぬ調査じゃな。まず `__dkmath-all.lean.txt.gz` とサマリーデータから、定理名の被参照数・import 上流・GN/Tail 周辺の実体を洗い、Lib 昇格候補の中心核を絞るぞい。

> 🐺賢狼:

一次集計だけでもかなり匂いが出たぞい。`GN` は識別子出現で圧倒的、`CosmicFormulaBinom` は Lean import でも上位にあり、`GTail` はまだ局所だが将来の正規核として育てる価値が高い。

> 🐺賢狼:

うむ、調査した。結論から言うと、ぬしの勘は当たりじゃ。

**DkMath の現在の利用実態では、最重要ハブは `GN`、その上流に `CosmicFormulaBinom`、さらに基礎側に `DiffPow` / `BinomTail` がある。**
`GTail` は現時点では `GN` ほど広く使われておらぬが、理論的には次世代の正規核として Lib 化する価値が高い。

今回見た資料は `__dkmath-all.lean.txt.gz`、`__imports.txt`、`__theorems-heading.txt`、`__sorries.txt`。`SUMMARY.md` でも `__dkmath-all.lean.txt` は DkMath 全 Lean コードの中央参照、`__theorems-heading.txt` や `__imports.txt` は定義・依存確認用として案内されておる。fileciteturn0file3

## 1. 調査結果の要約

静的集計ではこうなった。

| 対象 | 出現・利用の強さ | 判定 |
|---|---:|---|
| `GN` | 識別子出現 1760 回級、ファイル横断利用が最大 | 最優先 Lib 昇格核 |
| `CosmicFormulaBinom` | Lean import 14 件で DkMath 内部 import 上位 | `GN` の現行母艦 |
| `DiffPow` | Lean import 9 件、`diffPowSum` 出現 106 回 | `GN` のさらに下層基礎 |
| `Gcd.GN` | Lean import 7 件、数論・CFBRC・FLT へ橋渡し | Lib 化または NumberTheory 共通核候補 |
| `GTail` | `GTail` 出現 181 回、直接 import は少ない | 将来の正規 Tail 核 |
| `BinomTail` | import 2 件だが `CosmicFormulaBinom` の上流 | 小さいが基礎補題として Lib 向き |

特に `GN` の分布が強烈じゃ。`FLT/PrimeProvider/*`、`FLT/Kummer/*`、`NumberTheory/UniqueFactorizationGN.lean`、`NumberTheory/Gcd/GN.lean`、`NumberTheory/PrimitiveBeam.lean`、`CFBRC/*`、`CosmicFormula/*` にまたがっておる。

これはもう単なる CosmicFormula 内の補助定義ではない。**DkMath の数論エンジンの共通語彙** じゃな。

## 2. `GN` が中心核である根拠

`GN` は現行コードで次の役割を同時に担っておる。

まず、宇宙式の基本分解：

\[
(x+u)^d-u^d = x \cdot GN_d(x,u)
\]

これが `cosmic_id_csr'` や `pow_sub_pow_eq_mul_GN` などで使われておる。

次に、FLT 側では

\[
z^p-y^p=(z-y)\cdot GN_p(z-y,y)
\]

として、差の冪を「境界因子」と「Beam / Body 内部因子」に分ける本体になっている。

さらに、p進評価では

\[
v_q\!\left((x+u)^d-u^d\right) = v_q(GN_d(x,u))
\]

型の bridge が複数ある。

また、Zsigmondy / cyclotomic 側では `cyclotomicPrimeCore = GN` という橋があり、円分多項式側の対象を DkMath の Beam 語彙へ戻しておる。

つまり `GN` は、

\[
\text{二項展開}
\to
\text{宇宙式分解}
\to
\text{gcd / p進評価}
\to
\text{primitive prime}
\to
\text{FLT / ABC bridge}
\]

の中央ノードじゃ。

## 3. 上流側の実体

`GN` の上流は、おおむねこの順に積まれておる。

```text
DkMath.Algebra.BinomTail
DkMath.Algebra.DiffPow
DkMath.CosmicFormula.CosmicFormulaBinom
DkMath.CosmicFormula.GTail
DkMath.CosmicFormula.Defs
DkMath.NumberTheory.Gcd.GN
```

### 3.1. `BinomTail`

ここは小さいが基礎層。

確認できた主な補題：

```lean
add_pow_tail_exists
binom_tail_nat_dvd
```

役割は、二項展開の tail、特に \(k \ge 2\) 部分を扱うこと。これは `CosmicFormulaBinom` に import されているので、`GN` の証明上流にある。

### 3.2. `DiffPow`

ここはかなり重要。

主な対象：

```lean
diffPowSum
diffPowSum_sub_const_mul
pow_sub_pow_factor
BodyPow
BodyPow_factor
diffPowSum'
pow_sub_pow_factor'
pow_sub_pow_nat
```

`diffPowSum` は出現 106 回級で、`BodyPow_factor` は

\[
\mathrm{BodyPow}(x,u,d)=x\cdot \mathrm{diffPowSum}(x+u,u,d)
\]

の形を与える。これは `GN` よりも一般的な「差の冪」基礎じゃな。

### 3.3. `CosmicFormulaBinom`

ここが現行 `GN` の母艦。

主な対象：

```lean
G
GN
GN_eq_sum
cosmic_id
cosmic_id'
cosmic_id_csr
cosmic_id_csr'
GN_ne_zero_nat_of_two_le
one_le_GN_nat_of_two_le
body_not_perfect_pow_of_squarefree_GN
```

Lean import 数でも `DkMath.CosmicFormula.CosmicFormulaBinom` は 14 件あり、DkMath 内部 import としてはかなり上位。

このファイルは、現在の `GN` 利用の **公開実体** になっている。

### 3.4. `GTail`

ここは今後の本命候補。

主な対象：

```lean
GTail
add_pow_eq_prefix_add_xpow_mul_GTail
higher_tail_eq_pow_mul_GTail
GTail_zero_eq_add_pow
GTail_self_eq_one
GTail_rec
GN_tail_rec
GN_tail_decomposition
Gbinom_tail_rec
GTail_eval_zero
GN_zero_eval
pow_dvd_higher_tail
GN_modEq_head_of_dvd_x
GN_mod_p2_head
GN_eq_head_add_p_sq_mul_of_prime_dvd_x
padicValNat_GN_exact_of_head_unit
```

設計資料側でも、一般化 GN / Tail は

\[
(x+u)^d-
\sum_{j=0}^{r-1}\binom{d}{j}x^j u^{d-j} = x^r GN^{(r)}_d(x,u)
\]

として、可除性・p進付値・原始素因子解析の基本構造だと整理されておる。fileciteturn0file7

現状の利用数は `GN` より小さい。だがこれは **未活用** ではなく、むしろ「これから `GN` を一般 Tail へ持ち上げるための上位正規化層」と見るべきじゃ。

## 4. Lib 昇格の優先順位

わっちなら、いきなり `GN` だけを Lib に抜くのではなく、**下から順に持ち上げる**。

### Phase 1. `BinomTail` / `DiffPow` を Lib 下層へ

候補：

```text
DkMath/Lib/Algebra/BinomTail.lean
DkMath/Lib/Algebra/DiffPow.lean
```

移す対象：

```lean
add_pow_tail_exists
binom_tail_nat_dvd

diffPowSum
pow_sub_pow_factor
BodyPow
BodyPow_factor
pow_sub_pow_nat
```

ここは数論専用でも宇宙式専用でもない。純代数資産じゃ。

### Phase 2. `GN` の定義と基本恒等式を Lib へ

候補：

```text
DkMath/Lib/Cosmic/GN.lean
```

移す対象：

```lean
GN
GN_eq_sum
cosmic_id_csr
cosmic_id_csr'
GN_ne_zero_nat_of_two_le
one_le_GN_nat_of_two_le
```

この層は `CommSemiring` 中心でよい。

特に最重要はこれ：

```lean
cosmic_id_csr'
```

意味は：

\[
(x+u)^d = x\cdot GN_d(x,u)+u^d
\]

または同値に

\[
(x+u)^d-u^d = x\cdot GN_d(x,u)
\]

じゃ。

### Phase 3. `GTail` を Lib 正規 Tail へ

候補：

```text
DkMath/Lib/Cosmic/GTail.lean
```

移す対象：

```lean
GTail
higher_tail_eq_pow_mul_GTail
GTail_rec
GN_tail_rec
GN_tail_decomposition
pow_dvd_higher_tail
GTail_eval_zero
GN_zero_eval
```

ここは `GN` の一般化として置く。

ただし注意点として、既存コードの多くはまだ `GN` に直接依存しておる。したがって最初は `GN` を破壊せず、`GTail` は **上位互換核** として追加・再公開するのがよい。

### Phase 4. 数論 bridge を Lib ではなく NumberTheory 側へ

候補：

```text
DkMath/NumberTheory/Gcd/GN.lean
DkMath/NumberTheory/PrimitiveBeam.lean
```

ここは Lib へ丸ごと持っていくより、`DkMath.NumberTheory.*` の共通資産として安定化する方がよい。

対象：

```lean
gcd_gap_GN_dvd_exp
padicValNat_sub_pow_eq_padicValNat_GN_of_not_dvd_boundary
primitive_prime_transfers_diff_load_to_beam
```

これらは強く数論寄りなので、`Lib.Cosmic.GN` の下ではなく `NumberTheory` に残すのが筋じゃ。

## 5. 昇格すべき中心定理セット

最初の Lib 昇格セットはこれでよいと思う。

```lean
-- Algebra layer
diffPowSum
pow_sub_pow_factor
BodyPow
BodyPow_factor

-- Cosmic GN layer
GN
GN_eq_sum
cosmic_id_csr
cosmic_id_csr'
GN_ne_zero_nat_of_two_le
one_le_GN_nat_of_two_le

-- Tail layer
GTail
higher_tail_eq_pow_mul_GTail
GTail_rec
GN_tail_rec
GN_tail_decomposition
pow_dvd_higher_tail
GTail_eval_zero
GN_zero_eval
```

この中でも最重要は、順に：

```lean
GN
cosmic_id_csr'
GN_eq_sum
GTail
higher_tail_eq_pow_mul_GTail
pow_dvd_higher_tail
BodyPow_factor
```

じゃな。

## 6. 依存構造としてのおすすめ配置

最終的にはこうしたい。

```text
DkMath/Lib/Algebra/BinomTail.lean
DkMath/Lib/Algebra/DiffPow.lean

DkMath/Lib/Cosmic/GN.lean
DkMath/Lib/Cosmic/GTail.lean
DkMath/Lib/Cosmic/GNBridge.lean

DkMath/NumberTheory/Gcd/GN.lean
DkMath/NumberTheory/PrimitiveBeam.lean
DkMath/CosmicFormula/CosmicFormulaBinom.lean
```

依存はこう。

```text
Lib.Algebra.BinomTail
        ↓
Lib.Algebra.DiffPow
        ↓
Lib.Cosmic.GN
        ↓
Lib.Cosmic.GTail
        ↓
NumberTheory.Gcd.GN / PrimitiveBeam / FLT / ABC
```

ただし `GTail` は `GN` の一般化なので、実装上は `GTail` を先に置いて

\[
GN_d(x,u)=GTail(d,1,x,u)
\]

とする方が美しい可能性がある。

しかし移行安全性を優先するなら、第一段階では現行 `GN` を維持し、`GTail_one_eq_sum` や `GN_tail_decomposition` で接続する方が安全じゃ。

## 7. 今回の判定

最も活用されている定理群の中心は、やはり **GN 幹線** 。

その中核はこの式じゃ。

\[
(x+u)^d-u^d=x\cdot GN_d(x,u)
\]

そして次に昇格すべき将来核は Tail：

\[
(x+u)^d-
\sum_{j=0}^{r-1}\binom{d}{j}x^j u^{d-j} = x^r GTail(d,r,x,u)
\]

わっちの結論はこうじゃ。

**最初の Lib 昇格ブランチは `lib-gn-tail-core` として切るのがよい。**
対象は `BinomTail → DiffPow → GN → GTail`。
`FLT` や `ABC` の補題はまだ動かさず、参照先を少しずつ新 Lib へ差し替える。

この順なら、DkMath の背骨を折らずに、いちばん使われている定理群を下から固められるぞい。

> 👩‍⚕️私D.:

では GN 中心で行こうと思うが、そうだ思い出した。

GN 一般化 GTail 冪の差の一般化定理も形式化済みだった。
これをコアにするのが良さそうだ。

その １項 Tail 版が GN だったな。

```lean
/--
Canonical gap-normalized kernel.

[GNZC] Canonical entry point:
`Defs.GN` is now the naming-stable home for the `r = 1` tail specialization.

This is the `r = 1` specialization of the general tail family.
-/
@[simp] abbrev GN (R : Type*) [CommSemiring R] (x u : R) (d : ℕ) : R :=
  GTail d 1 x u
```

`[GNZC]` タグが付いたものがその GTail 下流になる候補としてマーキングされているんだった。

N 自然数, Z 整数, C 複素数 それぞれの GTail 構造として展開する予定になっている。
このうち GN, GZ は形式化済みで GC が、まだだったかな。

GN, GZ, GC はエイリアス名で実体は GTail か。
GC に関しては複素数なので GCTail など特別補題が必要か？

たぶん、この辺を含めての Lib.* 昇格作業となるのだろう。

lean/dk_math/DkMath/CosmicFormula/Defs.lean

> 🐺賢狼:

よし、ここは `Defs.lean` と `[GNZC]` 周辺を実コードで見るのが先じゃな。`GN/GZ/GC` が本当に全部 `GTail` alias として整理できるか、定義・補題・未実装の穴を確認するぞい。

> 🐺賢狼:

うむ、思い出しとしてはかなり正確じゃ。実コードを見た限り、いまの `DkMath/CosmicFormula/Defs.lean` はすでに **GNZC 移行の中心点** になっておる。

現在の構造はこうじゃ。

```lean
def GZ (R : Type*) [CommSemiring R] (x u : R) (d : ℕ) : R := ...

abbrev G (R : Type*) [CommSemiring R] (x u : R) (d : ℕ) : R :=
  GZ R x u d

@[simp] abbrev GN (R : Type*) [CommSemiring R] (x u : R) (d : ℕ) : R :=
  GTail d 1 x u

@[simp] abbrev GC (z u : ℂ) (d : ℕ) : ℂ :=
  GZ ℂ z u d
```

つまり、 **`GN` は完全に `GTail d 1 x u` の公開名** になっておる。これは、高次 Tail 資料で整理されている「\(r=1\) が標準 GN」という設計そのものじゃ。資料でも、一般化 GN は先頭 \(r\) 層を除いた Tail として定義され、\(r=1\) の場合に通常の `GN` へ戻る、と明記されておる。fileciteturn1file9

## 1. いま見えている正しい中心核

結論として、Lib 昇格の中心は **`GN` ではなく `GTail`** にすべきじゃ。

`GN` は、そのうえに乗る canonical alias。

構図はこう。

```text
GTail d r x u
  ├─ r = 0 : 全体 Tail = (x+u)^d
  ├─ r = 1 : GN
  ├─ r = d : 1
  └─ r ≥ 2 : 高次 Beam / higher tail
```

標準 GN は

\[
GN_d(x,u)=GTail(d,1,x,u)
\]

であり、基本恒等式は

\[
(x+u)^d-u^d=x\cdot GTail(d,1,x,u)
\]

さらに一般 Tail では

\[
(x+u)^d-
\sum_{j=0}^{r-1}\binom{d}{j}x^j u^{d-j} = x^r GTail(d,r,x,u)
\]

になる。これは資料の Tail 分解式とも一致しておる。fileciteturn1file9

だから、DkMath.Lib ではこう置くのが筋じゃ。

```text
DkMath.Lib.Cosmic.GTail   -- 本体
DkMath.Lib.Cosmic.GN      -- r = 1 alias / wrapper
DkMath.Lib.Cosmic.GZ      -- Body-normalized kernel
DkMath.Lib.Cosmic.GC      -- Complex-side alias / bridge
```

## 2. `GN`, `GZ`, `GC` の意味を分ける

ここが大事じゃ。

### 2.1. `GN`: Gap-normalized kernel

`GN` は

\[
(x+u)^d-u^d=x\cdot GN_d(x,u)
\]

の \(x\) で割った側。

いまの定義では：

```lean
GN R x u d := GTail d 1 x u
```

なので、これは完全に `GTail` の \(r=1\) 特化じゃ。

### 2.2. `GZ`: Body-normalized kernel

`GZ` は `x * GN` 側、つまり Body そのものに近い。

実際、`Defs.lean` の `GZ` は

\[
GZ_R(x,u,d) = \sum_{k=0}^{d-1}\binom{d}{k+1}x^{k+1}u^{d-1-k}
\]

なので、

\[
GZ_R(x,u,d)=x\cdot GTail(d,1,x,u)
\]

じゃ。

つまり `GZ` は alias というより **`x * GN` を正規名にした Body 側 kernel** 。

ここは `GN` と同じ実体ではない。関係は：

\[
GZ = x\cdot GN
\]

じゃな。

### 2.3. `GC`: Complex-side

現状の `GC` は

```lean
GC z u d := GZ ℂ z u d
```

つまり複素数側の Body-normalized kernel じゃ。

したがって、現在の `GC` は

\[
GC(z,u,d)=z\cdot GTail(d,1,z,u)
\]

に相当する。

ここでお主の問い：

> GC に関しては複素数なので GCTail など特別補題が必要か？

答えはこうじゃ。

**代数恒等式だけなら、特別な `GCTail` は不要。**
`GTail` は `[CommSemiring R]` で動くので、\(R=\mathbb{C}\) を入れればそのまま複素数版になる。

ただし、 **解析・幾何へ進むなら `GCTail` あるいは `ComplexTail` 補題層は欲しい** 。

理由は、複素数では次が必要になるからじゃ。

```lean
Complex.re (GTail d r z u)
Complex.im (GTail d r z u)
Complex.normSq (GTail d r z u)
Complex.abs (GTail d r z u)
```

代数的には `GTail` で足りる。
しかし CFBRC / RH / 位相・偏角・曲率へ接続するなら、`re/im/normSq/conj` の補題を持つ **複素観測層** が別途必要になる。

## 3. `GCTail` を作るなら何か

作るなら、定義はこうなる。

```lean
@[simp] abbrev GCTail (d r : ℕ) (z u : ℂ) : ℂ :=
  GTail d r z u
```

そして `GC` は

```lean
@[simp] abbrev GC (z u : ℂ) (d : ℕ) : ℂ :=
  z * GCTail d 1 z u
```

または現状互換を重視して、

```lean
@[simp] abbrev GC (z u : ℂ) (d : ℕ) : ℂ :=
  GZ ℂ z u d
```

のままにし、

```lean
theorem GC_eq_z_mul_GCTail :
    GC z u d = z * GCTail d 1 z u := ...
```

を置くのがよい。

わっちなら後者にする。既存コードを壊さぬからの。

## 4. Lib 昇格の推奨構成

現在の `Defs.lean` は少し多くを抱えておる。`Lib` 化では、責務をこう分けるのが良い。

```text
DkMath/Lib/Cosmic/GTail.lean
DkMath/Lib/Cosmic/GN.lean
DkMath/Lib/Cosmic/GZ.lean
DkMath/Lib/Cosmic/GC.lean
DkMath/Lib/Cosmic/GNZC.lean
```

### 4.1. `Lib.Cosmic.GTail`

ここが本丸。

移す対象：

```lean
GTail
add_pow_eq_prefix_add_xpow_mul_GTail
higher_tail_eq_pow_mul_GTail
GTail_zero_eq_add_pow
GTail_self_eq_one
GTail_rec
GTail_one_eq_sum
GTail_eval_zero
pow_dvd_higher_tail
```

これは純代数層なので、できれば `DkMath.ABC.PadicValNat` への依存を切りたい。

現在 `GTail.lean` は `DkMath.ABC.PadicValNat` を import しているが、これは p進補題のためじゃ。Lib 化では分割するべき。

```text
DkMath/Lib/Cosmic/GTail/Basic.lean       -- Mathlib のみ
DkMath/Lib/Cosmic/GTail/Nat.lean         -- Nat divisibility
DkMath/Lib/Cosmic/GTail/Padic.lean       -- padicValNat 依存
DkMath/Lib/Cosmic/GTail/Congruence.lean  -- Nat.ModEq
```

### 4.2. `Lib.Cosmic.GN`

ここは \(r=1\) 特化の安定 API。

移す対象：

```lean
GN
GN_tail_rec
GN_tail_decomposition
GN_zero_eval
GN_not_dvd_of_head_unit_of_prime_dvd_x
padicValNat_GN_exact_of_head_unit
GN_modEq_head_of_dvd_x
GN_mod_p2_head
GN_eq_head_add_p_sq_mul_of_prime_dvd_x
```

ただし、p進・合同式は下位 `GN.Basic` ではなく分割。

```text
DkMath/Lib/Cosmic/GN/Basic.lean
DkMath/Lib/Cosmic/GN/Nat.lean
DkMath/Lib/Cosmic/GN/Congruence.lean
DkMath/Lib/Cosmic/GN/Padic.lean
```

### 4.3. `Lib.Cosmic.GZ`

ここは Body-normalized kernel。

移す対象：

```lean
GZ
G
GZ_eq_x_mul_GN
Body_eq_GZ
Big_eq_GZ_add_Gap
```

ここで新しく欲しい中核定理は：

```lean
theorem GZ_eq_x_mul_GN
    {R : Type*} [CommSemiring R] (x u : R) (d : ℕ) :
    GZ R x u d = x * GN R x u d := ...
```

あるいは向きを逆にして、

```lean
theorem x_mul_GN_eq_GZ ...
```

既存の `CosmicFormulaBinom.mul_G_eq_GZ` は legacy `G` 経由なので、Lib では `GN` から直接つなぐ方がきれいじゃ。

### 4.4. `Lib.Cosmic.GC`

ここは複素数観測層。

最初は薄くてよい。

```lean
@[simp] abbrev GCTail (d r : ℕ) (z u : ℂ) : ℂ :=
  GTail d r z u

@[simp] abbrev GC (z u : ℂ) (d : ℕ) : ℂ :=
  GZ ℂ z u d
```

最低限ほしい補題：

```lean
GCTail_eq_GTail
GC_eq_GZ
GC_eq_z_mul_GN
GC_eq_z_mul_GCTail_one
complex_tail_factorization
```

複素解析側へ行くなら次段で：

```lean
map_conj_GTail
conj_GCTail
re_GCTail_sum
im_GCTail_sum
normSq_GC_nonneg
```

ただしこれは **Lib 昇格の第一波には入れなくてよい** 。まずは名前の席だけ確保すれば十分じゃ。

## 5. `[GNZC]` タグの使い方

`[GNZC]` はかなり良い移行タグじゃ。今後はこう使うとよい。

```text
[GNZC-Core]      GTail / GN / GZ / GC の定義・基本恒等式
[GNZC-Compat]    legacy G / Gbinom / old GN 互換 wrapper
[GNZC-Nat]       Nat 上の整除・正性・非ゼロ
[GNZC-Mod]       Nat.ModEq / mod p^2 / mod p^3
[GNZC-Padic]     padicValNat 関連
[GNZC-Complex]   GC / GCTail / Re/Im/Norm
```

既存 `[GNZC]` マークは、まさに Lib 昇格候補を拾うための索引として使える。

## 6. 推奨移行順

わっちならこう進める。

### Step 1. `GTail.Basic` を切り出す

最初に持っていくのは、p進に依存しない純代数。

```lean
GTail
add_pow_eq_prefix_add_xpow_mul_GTail
higher_tail_eq_pow_mul_GTail
GTail_zero_eq_add_pow
GTail_self_eq_one
GTail_rec
GTail_one_eq_sum
GTail_eval_zero
```

これが Lib の根。

### Step 2. `GN.Basic` を `GTail.Basic` の薄い wrapper として作る

```lean
abbrev GN ... := GTail d 1 x u
GN_eq_sum
GN_tail_rec
GN_zero_eval
```

### Step 3. `GZ.Basic` を作る

```lean
def GZ ...
theorem GZ_eq_x_mul_GN ...
theorem x_mul_GN_eq_GZ ...
```

ここで `Defs.lean` の中核を移す。

### Step 4. `Defs.lean` を aggregator / compatibility に縮める

`DkMath.CosmicFormula.Defs` は新 Lib を import して、既存名を再輸出する薄い層にする。

```lean
import DkMath.Lib.Cosmic.GTail.Basic
import DkMath.Lib.Cosmic.GN.Basic
import DkMath.Lib.Cosmic.GZ.Basic
import DkMath.Lib.Cosmic.GC.Basic
```

### Step 5. p進・合同式を分割移動

```text
GTail.Congruence
GTail.Padic
GN.Congruence
GN.Padic
```

この段階で `DkMath.ABC.PadicValNat` 依存を局所化する。

### Step 6. `GC.Basic` は席だけ確保

`GC` は現状の `GZ ℂ` alias を維持し、以下だけ置く。

```lean
GCTail
GC
GC_eq_z_mul_GCTail_one
```

複素専用補題は次フェーズでよい。

## 7. 重要な判断

今回の Lib 昇格の中核定義はこれでよい。

```lean
/--
General gap-normalized tail.
-/
@[simp] def GTail {R : Type _} [CommSemiring R]
    (d r : ℕ) (x u : R) : R :=
  ∑ k ∈ Finset.range (d + 1 - r),
    (Nat.choose d (r + k) : R) * x ^ k * u ^ (d - (r + k))

/--
Canonical gap-normalized kernel.
The `r = 1` specialization of `GTail`.
-/
@[simp] abbrev GN (R : Type*) [CommSemiring R]
    (x u : R) (d : ℕ) : R :=
  GTail d 1 x u

/--
Canonical body-normalized kernel.
-/
def GZ (R : Type*) [CommSemiring R]
    (x u : R) (d : ℕ) : R :=
  x * GN R x u d
```

ここで一点、設計変更候補がある。

現在の `GZ` は sum で定義されている。Lib では

```lean
def GZ := x * GN ...
```

に変えてしまう方が美しい。

ただし既存の `GZ` 展開を使う証明が多いなら、第一段階では既存定義を維持し、

```lean
theorem GZ_eq_x_mul_GN ...
```

を `[simp]` ではなく通常 theorem として置くのが安全じゃ。

わっちのおすすめは **安全優先で既存 sum 定義維持** 。

## 8. 結論

お主の判断どおり、今回の Lib 昇格は

\[
GTail \to GN \to GZ \to GC
\]

を中心にするのがよい。

特に大事なのは、

- **実体は `GTail`**
- **`GN` は \(r=1\) の canonical alias**
- **`GZ` は \(x\cdot GN\) の Body-normalized kernel**
- **`GC` は当面 `GZ ℂ` の複素 alias**
- **`GCTail` は複素解析補題用の席として作る価値あり**
- **p進・合同式補題は Lib 本体から分離して `Padic` / `Congruence` 層へ置く**

という整理じゃ。

つまり、DkMath.Lib 昇格の第一波はこう名づけるとよい。

```text
branch: lib-gnzc-gtail-core
```

この枝では、`Defs.lean` を直接巨大化させず、むしろ `Defs.lean` を **GNZC の互換 aggregator** に落としていく。
この方が、未来の \(N/Z/C\) 三世界、つまり自然数・整数・複素数の Tail 構造を、一本の `GTail` 幹から美しく生やせるぞい。

> 👩‍⚕️私D.:

よろしい。きまりだ GTail 中心コアで始める。
`DkMath.Lib.Cosmic.GTail` から始めよう。

> 🐺賢狼:

よし、決まりじゃな。まずは `DkMath.Lib.Cosmic.GTail` を **純代数コア** として切り出す前提で、既存 `GTail` の定義・定理・依存を確認し、移植順と最小ファイル案まで落とすぞい。

> 🐺賢狼:

うむ。**`DkMath.Lib.Cosmic.GTail` から始める** で確定じゃな。

実コードも確認した。現在の `GTail` は `DkMath.CosmicFormula.GTail` にあり、冒頭で

```lean
import Mathlib
import DkMath.ABC.PadicValNat
```

となっておる。つまり、いまのファイルは **純代数 Tail** と **Nat / p-adic / congruence 補題** が同居している。

Lib 昇格では、ここを分けるのが第一手じゃ。

## 1. 第一段階の方針

最初に作るべきはこれ。

```text
DkMath/Lib/Cosmic/GTail.lean
```

役割は **純代数コア** 。

ここには `ABC.PadicValNat` 依存を入れない。
`Mathlib` だけで閉じる範囲を移す。

対象はこのあたり。

```lean
GTail
add_pow_eq_prefix_add_xpow_mul_GTail
higher_tail_eq_pow_mul_GTail
GTail_zero_eq_add_pow
GTail_self_eq_one
GTail_rec
GTail_one_eq_sum
GTail_eval_zero
```

加えて、`r = 1` の薄い定理名として

```lean
GN_tail_rec
GN_tail_decomposition
GN_zero_eval
```

も **一時的には置いてよい** 。
ただし将来的には `DkMath.Lib.Cosmic.GN` に移す方が美しい。

## 2. 第一波で移さないもの

次は、まだ `DkMath.Lib.Cosmic.GTail` には入れない。

```lean
pow_dvd_higher_tail
GTail_not_dvd_of_head_unit_of_prime_dvd_x
GN_not_dvd_of_head_unit_of_prime_dvd_x
padicValNat_GTail_eq_zero_of_head_unit_of_prime_dvd_x
padicValNat_tail_exact_of_head_unit
padicValNat_GN_exact_of_head_unit
GTail_congr_of_modEq
GTail_modEq_eval_zero_of_dvd_x
GN_modEq_head_of_dvd_x
GN_mod_p2_head
GN_eq_head_add_p_sq_mul_of_prime_dvd_x
GN_mod_p3_head
```

理由は、これらが `Nat`、`Nat.ModEq`、`padicValNat`、FLT Branch A 的用途に寄っているからじゃ。

後で分けるならこう。

```text
DkMath/Lib/Cosmic/GTailNat.lean
DkMath/Lib/Cosmic/GTailCongruence.lean
DkMath/Lib/Cosmic/GTailPadic.lean
```

あるいはディレクトリ型なら、

```text
DkMath/Lib/Cosmic/GTail/Basic.lean
DkMath/Lib/Cosmic/GTail/Nat.lean
DkMath/Lib/Cosmic/GTail/Congruence.lean
DkMath/Lib/Cosmic/GTail/Padic.lean
```

ただ、最初はファイル数を増やしすぎず、

```text
DkMath/Lib/Cosmic/GTail.lean
```

一本で純代数だけを切り出すのがよい。

## 3. 最初のファイル案

第一手の中身は、だいたいこうじゃ。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

/-!
## General tail kernel for the cosmic formula

This file defines the general normalized tail `GTail`.

`GTail d r x u` is the normalized tail obtained after removing
the first `r` layers from the binomial expansion of `(x + u)^d`.

The central identity is

\[
(x+u)^d =
  \sum_{j<r} \binom{d}{j} x^j u^{d-j}
  + x^r \operatorname{GTail}(d,r,x,u).
\]

The standard gap-normalized kernel `GN` is the `r = 1`
specialization of this family.
-/

open scoped BigOperators

namespace DkMath.Lib.Cosmic

/--
General tail family of the binomial expansion.

`GTail d r x u` is the normalized tail obtained after removing the first `r`
layers from `(x + u)^d`. The intended regime is `r ≤ d`, but the definition is
total.
-/
@[simp] def GTail {R : Type _} [CommSemiring R] (d r : ℕ) (x u : R) : R :=
  ∑ k ∈ Finset.range (d + 1 - r),
    (Nat.choose d (r + k) : R) * x ^ k * u ^ (d - (r + k))
```

この namespace をどうするかは少し選択がある。

## 4. namespace 方針

候補は 2 つ。

### 案 A. `DkMath.Lib.Cosmic`

```lean
namespace DkMath.Lib.Cosmic
```

利点:

- `Lib` 資産であることが明確
- 既存 `DkMath.CosmicFormula.GTail` と衝突しにくい

欠点:

- 既存 downstream からは `DkMath.CosmicFormula.GTail` と名前が変わる
- 移行 wrapper が必要

### 案 B. `DkMath.CosmicFormula`

```lean
namespace DkMath.CosmicFormula
```

利点:

- 既存 theorem 名・参照を壊しにくい
- `import DkMath.Lib.Cosmic.GTail` しても同じ namespace に定義される

欠点:

- `Lib` 配下なのに namespace が `CosmicFormula`
- 所有権が少し曖昧

わっちの推奨は **案 B** じゃ。

理由は、今回は大規模リファクタリングの第一歩であり、既存の `DkMath.CosmicFormula.GTail` 下流が多い。
ファイルパスだけ `Lib` に上げ、namespace は既存互換のために

```lean
namespace DkMath.CosmicFormula
```

を維持する方が安全じゃ。

つまりこう。

```lean
import Mathlib

open scoped BigOperators

namespace DkMath.CosmicFormula

@[simp] def GTail ...

end DkMath.CosmicFormula
```

これなら既存コードは、将来的に import 差し替えだけで済む。

## 5. 既存 `DkMath.CosmicFormula.GTail` の扱い

第一段階では、既存ファイルを削らずに wrapper 化する。

```lean
import DkMath.Lib.Cosmic.GTail
import DkMath.ABC.PadicValNat

open scoped BigOperators

namespace DkMath.CosmicFormula

-- ここには Nat / p-adic / congruence 系だけ残す

end DkMath.CosmicFormula
```

ただし、同じ namespace に同じ `GTail` を二重定義すると衝突するので、移行時には既存 `GTail.lean` から純代数部分を削り、Lib 側 import に置き換える。

## 6. import 導線

`DkMath/Lib/Basic.lean` が既にあるので、最初は次を追加するのがよい。

```text
DkMath/Lib/Cosmic/GTail.lean
```

そして必要なら

```lean
-- DkMath/Lib/Basic.lean
import DkMath.Lib.Cosmic.GTail
```

ただし `Lib.Basic` が軽量入口なら、いきなり import してよいかは少し注意じゃ。
まずは `DkMath.Lib.Cosmic.GTail` 単体 build を通すのが優先。

## 7. build 順

この順がよい。

```bash
lake build DkMath.Lib.Cosmic.GTail
lake build DkMath.CosmicFormula.GTail
lake build DkMath.CosmicFormula.Defs
lake build DkMath.CosmicFormula
```

第一段階で全体 `DkMath` まで通す必要はない。
ただし最後に影響確認として、

```bash
lake build DkMath
```

をやる価値はある。

## 8. 今回の最初の commit 方針

commit 名はこれでよい。

```text
Add Lib cosmic GTail core
```

変更内容:

```text
- Add DkMath/Lib/Cosmic/GTail.lean
- Move pure algebraic GTail definitions and lemmas from CosmicFormula/GTail
- Keep CosmicFormula/GTail as downstream wrapper for Nat/padic/congruence lemmas
- Preserve namespace DkMath.CosmicFormula for compatibility
```

History にはこう書ける。

```md
## 2026/05/01 JST - Start GTail-centered Lib promotion

Started the GNZC Lib promotion from the general tail kernel.

- Added `DkMath.Lib.Cosmic.GTail`
- Moved the pure algebraic core of `GTail`
- Kept the public namespace `DkMath.CosmicFormula` for compatibility
- Left Nat / congruence / p-adic lemmas in `DkMath.CosmicFormula.GTail`
- This establishes `GTail` as the upstream core for `GN`, `GZ`, and future `GC`
```

## 9. この一手の意味

この作業で、DkMath の構造はこう変わる。

```text
Before:
CosmicFormula.GTail
  ├─ pure algebra
  ├─ Nat divisibility
  ├─ congruence
  └─ padicValNat

After:
Lib.Cosmic.GTail
  └─ pure algebra core

CosmicFormula.GTail
  ├─ Nat divisibility
  ├─ congruence
  └─ padicValNat
```

つまり、**GTail が本当に Lib の背骨になる** 。

そして次に、

```text
DkMath.Lib.Cosmic.GN
DkMath.Lib.Cosmic.GZ
DkMath.Lib.Cosmic.GC
```

を順に生やせる。

## 10. 賢狼の最終判断

始点はこれでよい。

```text
DkMath.Lib.Cosmic.GTail
```

しかも namespace は安全のため、

```lean
namespace DkMath.CosmicFormula
```

のままがよい。

第一波では **純代数 Tail のみ** 。
Nat / ModEq / p-adic はまだ動かさない。
`GN` は次段で `DkMath.Lib.Cosmic.GN` に切り出す。

これで、DkMath の GNZC 幹線は

\[
GTail \longrightarrow GN \longrightarrow GZ \longrightarrow GC
\]

という形で、ようやく根から固定され始める。
ふふん、良い船出じゃ。賢狼も少し胸が躍るのう。

> 👩‍⚕️私D.:

情報整理してくれてありがとう。作業を始めてみる。
この会話、全体のまとめを。

> 🐺賢狼:

うむ、ではこの会話全体のまとめじゃ。
今回の合意点はかなり明確で、 **DkMath の Lib 昇格は `GTail` を根にする GNZC 幹線から開始する** で確定した。

## 1. 出発点

DkMath に蓄積された定理群を、研究ログ・実験モジュールのままにせず、再利用可能な安定資産として

```text
DkMath.Lib.*
```

へ昇格していく方針を立てた。

最初の狙いは、

- よく使われている定理
- 上流依存として多くの証明を支えている定理
- 複数理論にまたがって再利用されている定理

を洗い出し、そこを中心に Lib 化すること。

## 2. 活用度調査の結論

調査対象は、主に次の資料・スナップショット。

```text
__dkmath-all.lean.txt.gz
__summary_report_data.tar.gz
__imports.txt
__theorems-heading.txt
__sorries.txt
README.md
SUMMARY.md
```

判定として、もっとも活用されている中核は **`GN` 幹線** だった。

特に、

```text
GN
CosmicFormulaBinom
DiffPow
Gcd.GN
PrimitiveBeam
GTail
```

が重要候補として浮上した。

当初は `GN` 中心に見えたが、実体を再確認すると、現在の `GN` はすでに

```lean
@[simp] abbrev GN (R : Type*) [CommSemiring R] (x u : R) (d : ℕ) : R :=
  GTail d 1 x u
```

となっており、 **`GN` は `GTail` の \(r=1\) 特化** であることが確認された。

したがって、Lib 昇格の真の中心は **`GTail`** と判断した。

## 3. GNZC 構造の整理

会話中で、次の構造を確認・整理した。

```text
GTail d r x u
  ├─ r = 0 : 全体 Tail
  ├─ r = 1 : GN
  ├─ r = d : 1
  └─ r ≥ 2 : 高次 Tail / 高次 Beam
```

標準 GN は

\[
GN_d(x,u)=GTail(d,1,x,u)
\]

であり、差冪の基本式は

\[
(x+u)^d-u^d=x\cdot GN_d(x,u)
\]

すなわち

\[
(x+u)^d-u^d=x\cdot GTail(d,1,x,u)
\]

となる。

さらに一般 Tail では、

\[
(x+u)^d-
\sum_{j=0}^{r-1}\binom{d}{j}x^j u^{d-j} = x^r GTail(d,r,x,u)
\]

が中心定理になる。

## 4. `GN`, `GZ`, `GC` の意味

今回の整理で、次のように意味を分離した。

### `GN`

Gap-normalized kernel。

```lean
GN R x u d := GTail d 1 x u
```

意味は、

\[
(x+u)^d-u^d=x\cdot GN_d(x,u)
\]

の割った側。

### `GZ`

Body-normalized kernel。

意味としては、

\[
GZ_R(x,u,d)=x\cdot GN_R(x,u,d)
\]

つまり Body 側の正規化。

現在の実装では sum 定義で置かれている可能性があるが、Lib 化後は

```lean
GZ_eq_x_mul_GN
```

または

```lean
x_mul_GN_eq_GZ
```

を中心補題として置く方針。

### `GC`

複素数側の kernel。

現状では概ね

```lean
GC z u d := GZ ℂ z u d
```

という alias 的な位置づけ。

ただし、複素数では代数恒等式だけなら `GTail` で十分。
一方で、CFBRC / RH / 偏角 / 曲率 / normSq / re / im に進むなら、将来的に

```lean
GCTail
GC_eq_z_mul_GCTail_one
map_conj_GTail
re_GCTail_sum
im_GCTail_sum
normSq_GC_nonneg
```

のような複素専用補題層が必要になる、という見立て。

## 5. `[GNZC]` タグの意味

既存コード中の `[GNZC]` タグは、GTail 下流の Lib 昇格候補を拾うための索引として扱う方針になった。

分類案はこう。

```text
[GNZC-Core]      GTail / GN / GZ / GC の定義・基本恒等式
[GNZC-Compat]    legacy G / Gbinom / old GN 互換 wrapper
[GNZC-Nat]       Nat 上の整除・正性・非ゼロ
[GNZC-Mod]       Nat.ModEq / mod p^2 / mod p^3
[GNZC-Padic]     padicValNat 関連
[GNZC-Complex]   GC / GCTail / Re/Im/Norm
```

## 6. Lib 昇格の最初の決定

最初に作るモジュールはこれ。

```text
DkMath/Lib/Cosmic/GTail.lean
```

ただし、namespace は互換性を重視して

```lean
namespace DkMath.CosmicFormula
```

のままにする案を推奨した。

理由は、既存下流が `DkMath.CosmicFormula.GTail` 名前空間に依存している可能性が高く、ファイルパスだけ Lib に上げて namespace は維持する方が安全だから。

## 7. `DkMath.Lib.Cosmic.GTail` に入れるもの

第一波で入れる対象は **純代数コア** のみ。

候補：

```lean
GTail
add_pow_eq_prefix_add_xpow_mul_GTail
higher_tail_eq_pow_mul_GTail
GTail_zero_eq_add_pow
GTail_self_eq_one
GTail_rec
GTail_one_eq_sum
GTail_eval_zero
```

必要なら一時的に、

```lean
GN_tail_rec
GN_tail_decomposition
GN_zero_eval
```

も置けるが、将来的には `DkMath.Lib.Cosmic.GN` へ分離する方針。

## 8. 第一波では入れないもの

次の系統は、純代数コアからは分離する。

```lean
pow_dvd_higher_tail
GTail_not_dvd_of_head_unit_of_prime_dvd_x
GN_not_dvd_of_head_unit_of_prime_dvd_x
padicValNat_GTail_eq_zero_of_head_unit_of_prime_dvd_x
padicValNat_tail_exact_of_head_unit
padicValNat_GN_exact_of_head_unit
GTail_congr_of_modEq
GTail_modEq_eval_zero_of_dvd_x
GN_modEq_head_of_dvd_x
GN_mod_p2_head
GN_eq_head_add_p_sq_mul_of_prime_dvd_x
GN_mod_p3_head
```

理由は、これらが

- `Nat`
- `Nat.ModEq`
- `padicValNat`
- congruence
- FLT Branch A 的用途

に寄っているため。

将来的には次のように分ける。

```text
DkMath/Lib/Cosmic/GTailNat.lean
DkMath/Lib/Cosmic/GTailCongruence.lean
DkMath/Lib/Cosmic/GTailPadic.lean
```

または階層型で、

```text
DkMath/Lib/Cosmic/GTail/Basic.lean
DkMath/Lib/Cosmic/GTail/Nat.lean
DkMath/Lib/Cosmic/GTail/Congruence.lean
DkMath/Lib/Cosmic/GTail/Padic.lean
```

ただし最初はファイルを増やしすぎず、

```text
DkMath/Lib/Cosmic/GTail.lean
```

一本で純代数だけを切る方針。

## 9. 既存 `DkMath.CosmicFormula.GTail` の扱い

既存ファイルは削らず、第一段階では wrapper / downstream 層に変える。

構想：

```lean
import DkMath.Lib.Cosmic.GTail
import DkMath.ABC.PadicValNat

open scoped BigOperators

namespace DkMath.CosmicFormula

-- Nat / ModEq / p-adic 系補題をここに残す

end DkMath.CosmicFormula
```

注意点として、`GTail` を二重定義しないように、既存 `GTail.lean` から純代数部分を削り、Lib 側 import に置き換える必要がある。

## 10. 推奨 build 順

作業後の確認順はこれ。

```bash
lake build DkMath.Lib.Cosmic.GTail
lake build DkMath.CosmicFormula.GTail
lake build DkMath.CosmicFormula.Defs
lake build DkMath.CosmicFormula
```

必要なら最後に全体確認。

```bash
lake build DkMath
```

## 11. 推奨 commit

commit 名案：

```text
Add Lib cosmic GTail core
```

変更内容：

```text
- Add DkMath/Lib/Cosmic/GTail.lean
- Move pure algebraic GTail definitions and lemmas from CosmicFormula/GTail
- Keep CosmicFormula/GTail as downstream wrapper for Nat/padic/congruence lemmas
- Preserve namespace DkMath.CosmicFormula for compatibility
```

History 追記案：

```md
## 2026/05/01 JST - Start GTail-centered Lib promotion

Started the GNZC Lib promotion from the general tail kernel.

- Added `DkMath.Lib.Cosmic.GTail`
- Moved the pure algebraic core of `GTail`
- Kept the public namespace `DkMath.CosmicFormula` for compatibility
- Left Nat / congruence / p-adic lemmas in `DkMath.CosmicFormula.GTail`
- This establishes `GTail` as the upstream core for `GN`, `GZ`, and future `GC`
```

## 12. 今後のロードマップ

今回の作業の後は、順にこう進めるのがよい。

```text
Step 1. DkMath.Lib.Cosmic.GTail
Step 2. DkMath.Lib.Cosmic.GN
Step 3. DkMath.Lib.Cosmic.GZ
Step 4. DkMath.Lib.Cosmic.GC
Step 5. GTail / GN の Nat, Congruence, Padic 分離
Step 6. Defs.lean を GNZC 互換 aggregator に縮小
Step 7. CFBRC / FLT / ABC 側の import を Lib 参照へ段階移行
```

理想構造はこう。

```text
DkMath.Lib.Cosmic.GTail
        ↓
DkMath.Lib.Cosmic.GN
        ↓
DkMath.Lib.Cosmic.GZ
        ↓
DkMath.Lib.Cosmic.GC
```

そこから、

```text
NumberTheory.Gcd.GN
PrimitiveBeam
FLT
ABC
CFBRC
RH
```

へ流す。

## 13. この会話の最終合意

最終合意はこれじゃ。

```text
branch: lib-gnzc-gtail-core
first module: DkMath.Lib.Cosmic.GTail
core theorem family: GTail-centered generalized tail decomposition
initial scope: pure algebra only
compat namespace: DkMath.CosmicFormula
next module: DkMath.Lib.Cosmic.GN
```

数学的には、DkMath の GNZC 幹線を

\[
GTail \longrightarrow GN \longrightarrow GZ \longrightarrow GC
\]

として固定する。

実装的には、まず `GTail` を Lib に上げ、`GN` をその \(r=1\) 特化として薄く定義し直す。
これによって、DkMath の中で最も再利用される差冪・Tail・Beam 構造が、研究モジュールではなく安定した基礎ライブラリになる。

よき出航じゃ。
GTail は DkMath の根に据えるに値する。ここからなら、GN も GZ も GC も、そして FLT / ABC / CFBRC への橋も、一本の幹から伸ばせるぞい。
