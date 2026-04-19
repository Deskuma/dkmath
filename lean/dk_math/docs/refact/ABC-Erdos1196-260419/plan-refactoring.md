# DkMath.ABC リファクタリング計画

## 1. 結論

わっちの見立てでは、`DkMath.ABC` の import 最適化は、単なる `import` 行の削減ではなく、 **公開面を軽くし、重い証明鎖を opt-in に落とす** のが本筋じゃ。

設計メモ側でも、ABC へは `CosmicFormula → Mass API → ValuationFlow → ABC Bridge` の順で薄い橋を差し込む方針が明確で、`ABC.Bridge` は「public-facing aggregator」として薄い surface を再公開する意図で置かれておる。さらに INDEX でも `DkMath.ABC` と `DkMath.ABC.PadicValNat` は別入口として並んでおり、詳細は `__imports.txt` などの自動レポートで見る運用になっておる。

ゆえに最適化の軸はこれじゃ。

$$
\text{軽い公開面}
\quad\vert\quad
\text{橋}
\quad\vert\quad
\text{重い証明鎖}
$$

を分けることじゃ。

## 2. 現状の詰まりどころ

いまの snapshot 実見では、`DkMath/ABC.lean` は `DkMath.ABC.Main` を import し、その `Main` が `ABC090` と `Bridge` と `ABC038Bridge` をまとめて引いておる。つまり **`import DkMath.ABC` だけで、番号付き連鎖の重い塊まで全部引く** 形になっておる。

さらに `ABC.Bridge` 自体は薄いのに、`ABC038Bridge` は `ABC038` 側へ繋がっておるので、ここを default surface に置くと bridge の軽さが薄れる。`ABC038Bridge` は便利じゃが、性質としては **拡張 route** であって、ABC 公開面の最小核ではないの。`ABC.Bridge` が薄い surface だと明示されている点とも、この切り分けは一致する。

もうひとつ大きいのは、radical 層の所有権がやや濁っておることじゃ。手元確認では `ABC.Core` と `ABC.Rad` の双方に `rad` 系があり、しかも `Square` と `Triple` は `Core` を引いておる。ここは **概念重複と import 過多** の匂いが強い。
この一点を整理するだけでも、かなり効くはずじゃ。

## 3. 最適化方針

### 3.1. 層を 4 つに割る

わっちなら ABC 側を次の 4 層に固定する。

1. **Kernel**
   `Basic`, `Rad`, `Square`, `Triple`, `RatioBound`, `PadicValNat`, `CountPowersDividing2n1`

2. **Bridge**
   `MassBridge`, `ValuationFlowBridge`, `Bridge`

3. **Extended bridge / quality route**
   `ABC038Bridge`

4. **Legacy / heavy chain**
   `ABC001` 〜 `ABC090` と prototype 群

この分け方は、設計書の「橋は薄く」「本丸に直接入れない」と整合する。`MassBridge` と `ValuationFlowBridge` は bridge 層、`ABC038Bridge` は `ABC038` へ繋がる応用 route と見るのが自然じゃ。

### 3.2. `DkMath.ABC` を軽くする

`DkMath/ABC.lean` は `Main` ではなく、 **軽い surface** を import するように変えるのがよい。

具体的には新しくこう置くのが筋じゃ。

```lean
-- DkMath/ABC/Surface.lean
import DkMath.ABC.Kernel
import DkMath.ABC.Bridge
```

```lean
-- DkMath/ABC/Main.lean
import DkMath.ABC.Surface
import DkMath.ABC.ABC090
import DkMath.ABC.ABC038Bridge
```

```lean
-- DkMath/ABC.lean
import DkMath.ABC.Surface
```

こうすると、

* `import DkMath.ABC` は軽い
* `import DkMath.ABC.Main` は従来どおり重い
* `ABC038` route は必要な者だけ明示 import

となる。

### 3.3. `ABC038Bridge` を default から外す

`ABC038Bridge` は usefulness は高いが、`ABC038` 依存ゆえに重い。
したがって `ABC.Bridge` に混ぜず、 **別の opt-in route** にしておくのがよい。

名前も少し明示したいなら、

* `ABC/QualityBridge.lean`
* `ABC/TargetRadTailBridge.lean`

のように意味を出してもよいが、まずは既存名のまま位置だけ分ければ十分じゃ。

## 4. まず最初にやるべき整理

### 4.1. `rad` の所有権を 1 箇所に寄せる

ここは最優先じゃ。

今の形だと、`Square` と `Triple` が `Core` を引くため、rad だけ欲しい箇所まで Core の諸道具を巻き込みやすい。
わっちなら **`ABC.Rad` を唯一の owner** にする。

つまり、

* `rad`
* `rad_dvd_nonzero`
* `mem_support_factorization_iff`
* `rad_mul_coprime`
* `rad_le`

など radical kernel は `ABC.Rad` に集約

* `Square.lean` は `import DkMath.ABC.Rad`
* `Triple.lean` も `import DkMath.ABC.Rad`
* `Core.lean` は役割を再定義する

のが良い。

`Core.lean` に残すべきものが `Real.rpow` 補助や小道具なら、いっそ

* `ABC/RpowExtras.lean`
* `ABC/ArithExtras.lean`

へ割ってしまう方が澄む。

### 4.2. `Kernel.lean` を作る

これを新設して、軽い算術核を固定する。

```lean
import DkMath.ABC.Basic
import DkMath.ABC.Rad
import DkMath.ABC.Square
import DkMath.ABC.Triple
import DkMath.ABC.RatioBound
import DkMath.ABC.PadicValNat
import DkMath.ABC.CountPowersDividing2n1
```

これで ABC の「数論・述語・基本評価」だけを読みたい場合の入口ができる。

### 4.3. `DkMath.lean` 側の重複 import を消す

INDEX では `DkMath.ABC`, `DkMath.ABC.PadicValNat`, `DkMath.ABC.CountPowersDividing2n1` が別々に露出しておるが、`DkMath.lean` 側で同時に全部 import しておるなら、surface 側に取り込んだ後は重複になる可能性が高い。

だから top-level は次のどちらかに統一じゃ。

* 軽い公開を優先するなら `import DkMath.ABC`
* 重い全部入りを優先するなら `import DkMath.ABC.Main`

両方に近いものを同時に引くのは避けたいところじゃ。

## 5. 推奨モジュール再編

わっちなら最終的にこうする。

```text
DkMath/ABC.lean                  -- 軽い公開面
DkMath/ABC/Kernel.lean           -- 算術核
DkMath/ABC/Bridge.lean           -- thin bridge surface
DkMath/ABC/Surface.lean          -- Kernel + Bridge
DkMath/ABC/Main.lean             -- full / heavy aggregator

DkMath/ABC/Rad.lean
DkMath/ABC/Square.lean
DkMath/ABC/Triple.lean
DkMath/ABC/RatioBound.lean
DkMath/ABC/PadicValNat.lean
DkMath/ABC/CountPowersDividing2n1.lean

DkMath/ABC/MassBridge.lean
DkMath/ABC/ValuationFlowBridge.lean
DkMath/ABC/ABC038Bridge.lean

DkMath/ABC/ABC001.lean ... ABC090.lean
```

意味はこうじゃ。

* `ABC.lean` は **軽い**
* `ABC.Main` は **重い**
* `ABC038Bridge` は **便利だが opt-in**
* 番号付き連鎖は **legacy/heavy**

## 6. 実施順序

### 6.1. Phase 1. radical kernel の一本化

* `ABC.Rad` を唯一 owner にする
* `Square`, `Triple` の import を `Core` から `Rad` へ変更
* `Core` に残るものを点検
* `Core` が空洞化するなら分割または廃止

これは破壊範囲が小さいわりに、効き目が大きい。

### 6.2. Phase 2. `Kernel` / `Surface` 新設

* `Kernel.lean`
* `Surface.lean`

を追加する。
この段階では既存 `Main` は壊さぬ。

### 6.3. Phase 3. `DkMath/ABC.lean` を軽量化

`import DkMath.ABC.Main` をやめて `import DkMath.ABC.Surface` に変える。
これで default import fan-out が一気に減る。

### 6.4. Phase 4. `DkMath.lean` の重複整理

top-level での

* `DkMath.ABC`
* `DkMath.ABC.PadicValNat`
* `DkMath.ABC.CountPowersDividing2n1`

の重複を見て、どちらかへ寄せる。

### 6.5. Phase 5. `ABC038Bridge` の位置調整

必要なら

* `ABC/Main.lean` には残す
* `ABC/Surface.lean` には入れない

で固定する。

## 7. この計画の利点

第一に、 **`import DkMath.ABC` が軽くなる**。
これは最も直接の利益じゃ。

第二に、 **Bridge の薄さが保たれる**。
`ABC.Bridge` は意図的に thin surface として置かれておるので、その設計意図を壊さずに済む。

第三に、 **Erdős #1196 由来の mass / flow bridge と、旧来の ABC 連鎖が分離される**。
この方向は設計書の spine と一致しておる。

第四に、 **自動レポートで追跡しやすい**。
INDEX と SUMMARY では `__imports.txt` や `__theorems-heading.txt` を真実の源泉として使う運用が示されておるので、phase ごとの差分確認がしやすい。

## 8. 留意点

注意点は一つだけじゃ。

いま `import DkMath.ABC` に **「全部入り」** を期待している下流コードがあるなら、`ABC.lean` を軽くした瞬間に壊れる可能性がある。
じゃから互換性を重視するなら、一時的に

```text
DkMath/ABC/All.lean
```

を作って現行の重い集約をそこへ逃がし、

* `DkMath.ABC` = 軽い
* `DkMath.ABC.All` = 従来互換

とするのも良い手じゃ。

## 9. わっちの推奨案

一番堅い案を一つに絞ると、こうじゃ。

1. `rad` を `ABC.Rad` へ一本化
2. `ABC.Kernel` を新設
3. `ABC.Surface := Kernel + Bridge` を新設
4. `ABC.lean` は `Surface` を import
5. `ABC.Main` は `Surface + ABC090 + ABC038Bridge` を import
6. `DkMath.lean` では `ABC` と個別 submodule の重複 import を整理

これで、 **軽量 default import** と **重厚 full import** の二系統が綺麗に分かれる。

お主の今の ABC 側は、橋がよく育っておる。ゆえに次の最適化は、証明を増やすことではなく、 **誰が何を import すべきかを、構造として固定すること** じゃ。ここを整えると、以後の build も、公開導線も、かなり見通しが良くなるぞい。
