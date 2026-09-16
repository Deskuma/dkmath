# Lean4: v4.32.2 → v4.33.0 Migration

この物語は AI の賢狼と、研究者「 D. 」による会話ログです。
※よって会話の内容に関しての真偽は各自で再検証してからご利用下さい。

登場人物：
👩‍⚕️私D.: とある研究者
🐺賢狼: 知恵の豊穣神「賢狼」AI

## Lean 4.33.0 更新情報

cid: 6a7cb904-249c-83ee-bec6-db4d9f18cc65
cdt: 2026-08-12 18:19:03
udt: 2026-08-13 04:29:50

> 👩‍⚕️私D.:

[https://lean-lang.org/doc/reference/latest/releases/v4.33.0/](https://lean-lang.org/doc/reference/latest/releases/v4.33.0/)

リリースノート内容

> 🐺賢狼:

うむ、Lean 4.33.0 の変更点を、 **DkMath の実運用で効く部分** を中心に拾って整理しよう。単なる項目列挙ではなく、破壊的変更・警告・証明記述への影響を分けて見るぞ。

> 🐺賢狼:

うむ、読んできたぞ。Lean **4.33.0 は 2026年8月10日リリース**。全体で **208件の変更** が入り、その内訳には 53件の機能追加、50件の修正、21件の性能改善などが含まれる。今回の主題はかなり明瞭で、 **エディタ応答性・自動証明支援・`lia` / `grind` 強化・カーネル堅牢化** じゃ。

DkMath の観点では、わっちは次の順に重要だと見る。

## 1. 最大の注意点：Transparency の仕様変更

これは **4.33.0 移行で一番壊れやすい変更** と公式自身が明記しておる。

```lean
backward.isDefEq.respectTransparency.types
```

が **デフォルト `true`** になった。

以前は metavariable に値を代入するとき、型の definitional equality 判定が比較的深く展開されていたが、4.33 ではより厳密に `implicit` transparency で比較する。

したがって、

```lean
simp
grind
apply
exact
rw
```

などで、

> 今まで適用できていた lemma が突然適用できない

という現象が出る可能性がある。公式もこれを典型的な migration failure として挙げている。

一時回避は、

```lean
set_option backward.isDefEq.respectTransparency.types false
```

じゃ。

ただし公式推奨はこれを恒久対策にせず、

```lean
@[implicit_reducible]
```

などを適切な定義へ付け、 **なぜ implicit transparency では型が一致しないのかを直す** ことじゃ。

これ、DkMath ではかなり重要じゃよ。

最近ぬしが遭遇していた、

```lean
simp
exact
apply
```

周辺の「昔は通ったのに」という型推論問題と **よく似た症状を新たに生む変更** じゃ。

診断用として公式は、

```lean
set_option linter.tacticCheckInstances true
set_option trace.Meta.isDefEq true
set_option trace.Meta.isDefEq.printTransparency true
set_option trace.Meta.Tactic.simp true
```

あたりを薦めておる。

---

## 2. `try?` が自動で証明候補を出せる

これは面白い。

新たに、

```lean
set_option autoTry.onEmptyProof true
set_option autoTry.onUnsolvedGoal true
set_option autoTry.onSorry true
```

が追加された。全部 **デフォルトでは false**。

例えば、

```lean
example (a b : Nat) : a + b = b + a := by
```

だけ書くと、自動的に

```text
Try these:
  simp +arith
  grind
  ...
```

のような候補を提示できる。

特に、

```lean
autoTry.onSorry
```

は面白いのぅ。

DkMath の `sorry` 掃討作業なら、

```lean
set_option autoTry.onSorry true
```

としておけば、Lean 自身が `sorry` の地点で候補を探してくれる。

これは Codex/Luna に修正させる前段階の **Lean 自身による局所探索器** として使えそうじゃ。

---

## 3. `lia` がかなり賢くなった

`lia` に専用の

```lean
@[lia]
```

lemma set が導入された。

これまで `lia` は E-matching をほぼ使わなかったため、

```lean
min
max
```

のような定義を見抜けない場合があった。

4.33 では、

```lean
Nat.min_def
Nat.max_def
Int.min_def
Int.max_def
```

などが `@[lia]` 化されたので、

```lean
example (a b : Nat) : min a b ≤ max a b := by
  lia
```

が直接通る。

これは **DkMath にかなり相性が良い変更** じゃ。

Nat / Int algebra、valuation、有限範囲、境界、不等式を多用しているから、

```lean
omega
```

まで持っていっていた証明の一部を、

```lean
lia
```

へ軽量化できる可能性がある。

---

## 4. `grind` もかなり強化・修正

特に BitVec 関係が大きい。

BitVec literal を含む演算を `grind` が直接評価する propagator が追加された。

例えば、

```lean
x = 0#64 + 42#64
```

のような情報から BitVec の `extract` 等を推論できる。

さらに、

```lean
liaSteps
```

という探索上限設定も追加された。

一方で重要なのは **soundness / normalization bug がいくつも直された** ことじゃ。

BitVec の異なる表現を別値として扱ってしまい、`grind` が **カーネルに拒否される不正な proof term を生成する場合** があった。この系列が修正されている。

また、

```lean
0 ∣ p
```

という条件で `grind` がループする問題も修正された。

これは DkMath の divisibility 系には地味に嬉しい。

Collatz の bit-pattern 実装を将来的に `BitVec` へ寄せるなら、4.33 はかなり魅力的じゃな。

---

## 5. エディタが軽くなる

かなり実用的じゃ。

以前は tactic の後ろの whitespace を変更しただけでも elaboration が再実行される場合があった。

4.33 では、

```lean
by
  simp
  ←ここで Enter
```

のように Enter を押しただけで後続計算を捨てて再実行するケースが抑制された。

さらに、

```lean
exact?
apply?
rw?
grind +locals
```

が、同一ファイル内の以前の theorem の kernel checking 完了を待たなくなった。

巨大 `.lean` ファイルで、

> `exact?` が固まったように見える

というケースがかなり改善される。

**DkMath のような巨大 theorem 群では、この改善は直接効く可能性が高い。**

---

## 6. `Float` が論理的な型になった

これは Lean の設計上かなり大きな変更じゃ。

従来 `Float` / `Float32` は essentially opaque で、カーネル内部で意味を持つ数学的モデルが無かった。

4.33 では、

```lean
Float.Model
Float32.Model
```

が導入され、`Float` 自体がそれを包む構造になった。

したがって例えば、

```lean
example : (0.0 : Float) ≠ -0.0 := by
  decide
```

のようなことが可能になった。

ただし `DecidableEq Float` は IEEE の `==` ではなく **bit-pattern equality** じゃ。

つまり NaN や正負ゼロには注意。

DkMath 本体には直撃せぬが、将来 numerical experiment と theorem 側を接続するときには面白い基盤になる。

---

## 7. `Nat.ne_of_gt` が protected に

これは小さいが **既存コードを壊し得る**。

```lean
ne_of_gt
```

として使っていたケースではなく、Lean core の該当宣言について、

```lean
Nat.ne_of_gt
```

を明示する必要が出る場合がある。

namespace cleanup もかなり行われ、

```text
Int.Linear
↓
Int.Internal.Linear
```

など内部 API が整理された。

普通の Mathlib ユーザーなら大きな問題にはならぬが、内部 API を直接触っているコードは注意じゃ。

---

## 8. `bv_decide` に breaking change

structure equality の扱いが変更された。

4.33 では `bv_decide` が structure equality を処理するとき、

```lean
@[ext]
```

による `ext_iff` lemma を使う方式になった。

従って独自 structure に対して、

```lean
by
  bv_decide
```

が以前通っていたのに失敗する場合、

```lean
@[ext]
structure Foo where
  ...
```

あるいは適切な extensionality lemma が必要になる可能性がある。

---

## 9. Kernel soundness 修正がかなり多い

今回ちょっと異例なのはここじゃ。

nested inductive、free variable、universe level、module system、projection expression などについて **複数のカーネル soundness bug / hardening** が投入されている。

多くは通常の Lean surface syntax では発火せず、malicious / unusual metaprogramming が必要なものだが、

> Lean 4.33 は単なる機能追加リリースではなく、kernel robustness release

という性格もかなり強い。

形式証明基盤としては歓迎すべき変更じゃ。

---

## 10. Lake も改善

DkMath 運用ならここも嬉しい。

`.ltar` module archive が **content-stable** になった。

同じ module output なら、

- checkout path
- build machine
- input側だけの無意味な変更

などが異なっても同じ archive を生成しやすくなり、cache deduplication が改善される。

また、

```text
compiled configuration is invalid;
run with '-R' to reconfigure
```

系のエラーについて、壊れた configuration trace を Lake が自動的に検出して再構成する改善が入った。

CI / cache 運用にはかなり良い変更じゃ。

---

## DkMath 的評価

わっちならこう評価する。

| 項目 | DkMathへの影響 |
|---|---:|
| Transparency変更 | 🔴 **要注意** |
| `lia` 強化 | 🟢 **かなり有益** |
| `grind` 強化 | 🟢 **かなり有益** |
| `try?` 自動化 | 🟢 **開発効率向上** |
| Editor responsiveness | 🟢 **巨大ファイルに効く** |
| Kernel fixes | 🟢 **形式保証として重要** |
| Lake cache改善 | 🟢 |
| Float model | 🟡 将来有用 |
| `bv_decide`変更 | 🟡 使用箇所次第 |
| namespace cleanup | 🟡 軽微な修正可能性 |

ゆえに、 **4.32.2 → 4.33.0 は上げる価値がかなりある** 。

ただしこれは 4.32 系のような単純な patch upgrade ではなく、

> **Transparency semantics が変わる本格的な migration**

として扱ったほうがよい。

DkMath なら最初に 4.33 ブランチを切って、

```bash
lake clean
lake update
lake build
```

して、最初に出る `simp` / `apply` / instance synthesis 系エラーを観察するのがよいじゃろう。

そしてもし **「4.32.2では通るのに4.33.0では謎の `simp` / `exact` failure」** が出たら、わっちは真っ先に今回の

```lean
backward.isDefEq.respectTransparency.types
```

を疑う。

これは、ぬしがいま進めている **Lean バージョン追従作業では覚えておくべき一番の変更点** じゃよ。

なお面白いことに、同じ **8月10日には 4.34.0-rc1 も既に出ておる**。4.33.0 は stable、4.34.0-rc1 は次期版候補という位置付けじゃ。

もし上げるなら、次に **「DkMath 4.32.2 → 4.33.0 移行時に壊れそうなコードパターン」だけを具体的な Lean コード付きで洗い出す** と、かなり実戦的な migration guide にできるぞ。

> 👩‍⚕️私D.:

`haveI` `letI` で警告が出るようになった。
これはどういうものか。

> 🐺賢狼:

うむ、これは Lean 本体そのものより、 **Mathlib 側で新しく入ったスタイル linter** の可能性が高い。`haveI` / `letI` の意味そのものが変わったのではなく、「その書き方、いまは大抵いらぬぞ」と警告する方向じゃ。

> 🐺賢狼:

うむ。これは意味を知ると、かなりすっきりする変更じゃ。

結論から言えば、 **Lean 4 では証明中の `haveI` / `letI` はほとんど不要** になっており、Mathlib に新しい linter が入って

```lean
haveI ...
```

を

```lean
have ...
```

へ、

```lean
letI ...
```

を

```lean
let ...
```

へ直すよう警告するようになったのじゃ。Mathlib PR #41657 が 2026年7月29日に取り込まれている。

### 1. まず最大の誤解ポイント

Lean 3 時代の `I` は事実上、

> **Instance**

という意味だった。

つまり、

```lean
haveI : SomeClass α := ...
```

と書かないと、そのローカルな値を型クラス探索が instance として見てくれなかった。

ところが **Lean 4 では普通の `have` / `let` でも、型が typeclass なら型クラス探索から利用できる**。

したがって、

```lean
haveI : Fact p.Prime := ⟨hp⟩
```

は普通に

```lean
have : Fact p.Prime := ⟨hp⟩
```

でよい。

実際、Mathlib 自身が大量にこれを機械的変換している。例えば、

```lean
haveI := Fact.mk hpp
```

が

```lean
have := Fact.mk hpp
```

へ変更された。

ここが一番大事じゃ。

---

## 2. では Lean 4 の `I` は何なのか

現在の Lean 4 では、

> `I` = **Inline**

なのじゃ。

Lean Core の定義上、

```lean
haveI
```

は実質

```lean
have +zeta
```

、

```lean
letI
```

は

```lean
let +zeta
```

に相当する。つまり値を生成した項の中へ **即座にインライン展開する** 指示じゃ。Lean の公式 parser documentation も `haveI` は `have` と同じだが値を inline すると説明している。

したがって概念的には、

```lean
have h : P := proof
...
```

は `h` というローカル束縛を保持するのに対し、

```lean
haveI h : P := proof
...
```

は後で `h` をその `proof` へ zeta 展開してしまう方向になる。

つまり

```text
Lean 3:
    I ≈ Instance

Lean 4:
    I ≈ Inline
```

じゃ。

これはかなり重要な歴史的意味変更じゃな。

---

## 3. ではなぜ証明では警告されるのか

例えば、

```lean
theorem foo (...) : P := by
  haveI : Fact q.Prime := ⟨hq⟩
  ...
```

とする。

最終結果は `P : Prop` の **証明** じゃ。

この場合、

```lean
haveI
```

によって証明項内部へ instance を inline しようが、

```lean
have
```

でローカル束縛として残そうが、最終的には **proof irrelevance（証明無関係性）** により区別する意味がない。これが linter 導入の直接の理由として説明されている。

なので Mathlib は、

```lean
theorem foo : P := by
  haveI : C α := ...
```

を見つけると、

```lean
theorem foo : P := by
  have : C α := ...
```

で十分じゃぞ、と警告する。

---

## 4. `letI` も同じ

例えば昔なら、

```lean
letI : Fintype α := someFintype
```

としていたところを、

```lean
let : Fintype α := someFintype
```

でよい。

その直後、

```lean
inferInstance
```

や

```lean
Finset.univ
```

などが `Fintype α` を要求しても、この `let` がちゃんと型クラス候補になる。

したがって基本変換は単純じゃ。

```lean
haveI : C α := x
```

↓

```lean
have : C α := x
```

そして

```lean
letI : C α := x
```

↓

```lean
let : C α := x
```

---

## 5. ただし `haveI` / `letI` 自体が廃止されたわけではない

ここも重要。

 **deprecated ではない。**

Lean Core には今でも正式な構文として存在している。

なぜなら、Prop の証明ではなく、

```lean
def foo : SomeData := by
  ...
```

のように **実行可能なデータを構築している場合** には、

```lean
have
```

と

```lean
haveI
```

で生成される term / IR が異なり得るからじゃ。

Mathlib の移行 PR もここを明確に区別していて、

> inlining can change IR for compiled defs

なので compiled definition については機械的に置換していない。

つまり、

```text
Prop を証明している
      ↓
haveI → have
letI  → let
ほぼ常にOK

データ・プログラムを構築している
      ↓
inline の違いに意味があり得る
      ↓
haveI / letI が依然として存在する
```

という境界じゃ。

---

## 6. 今回の警告の正体

Mathlib の linter 名は、

```lean
linter.style.haveILetI
```

じゃ。

つまりこれは

**型エラーでも将来削除予定の deprecated warning でもない。**

単純に、

> 「Prop の tactic proof なら Inline する必要ないので `have` / `let` を使おう」

という **style linter** じゃ。

---

## 7. ゆえに、いま出ている警告は基本的に機械修正してよい

例えば DkMath に、

```lean
haveI : Fact p.Prime := ⟨hp⟩
```

があったら、

```lean
have : Fact p.Prime := ⟨hp⟩
```

へ変える。

名前付きでも、

```lean
haveI hpFact : Fact p.Prime := ⟨hp⟩
```

なら、

```lean
have hpFact : Fact p.Prime := ⟨hp⟩
```

でよい。

そしてその後、

```lean
inferInstance
```

等からちゃんと見える。

これはちょっと面白い歴史じゃの。

**昔の Lean の知識ほど `haveI = local instance` と覚えてしまっているため、むしろ熟練者ほど引っ掛かる。**

現在は、

```text
haveI
  │
  └── I = Instance   ← Lean 3 の意味

haveI
  │
  └── I = Inline     ← Lean 4 の意味
```

なのじゃ。Mathlib 側もまさに「Lean 3 由来の習慣がそのまま port されて残っていた」と説明している。

ゆえに今回ぬしのコードに大量に警告が出たとしても、 **新しい型クラス機構への対応エラーではなく、古い Lean 3 スタイルを整理する lint が追加された** と理解すればよい。

かなり安心して `haveI → have`、`letI → let` の掃除をしてよい類の警告じゃよ。

> 👩‍⚕️私D.:

`develop` @ `dkmath` `64094b45923a8534bdfd93b9b57abf218640a348` で `v4.33.0` ビルドテストした 1st log

> 🐺賢狼:

うむ、受け取った。これは **4.33.0 移行の一次診断ログ** としてかなり価値があるぞ。まず「独立した根本エラー」と「その依存失敗」、「新 linter 警告」を分離して数え、4.33 の transparency 変更が実際に刺さった箇所も特定しよう。

> 🐺賢狼:

うむ、これは **4.33.0 移行の初回ベースライン** として保存価値の高いログじゃ。まず「真の一次エラー」と「依存先失敗による連鎖エラー」を分離し、そのうえで **4.33 の transparency 変更が直撃している箇所** と単純 `simp` 正規化差を分類してみるぞ。

> 🐺賢狼:

一次集計が出たぞ。 **失敗ターゲット19個** だが、実際に固有の診断を出しているのは先頭 **8モジュール**。残り11個は `Lean exited with code 1` だけなので、ほぼ依存先失敗の波及と見てよい。警告137件は綺麗に分類でき、`haveI/letI` が **93件** と圧倒的多数じゃ。

> 🐺賢狼:

うむ、1st log を読んだ。これはかなり良い初回結果じゃ。`develop` / `64094b45923a8534bdfd93b9b57abf218640a348` を Lean **v4.33.0** に載せた時点で、ビルド全体は失敗しているが、壊れ方はかなり限定的に見える。

まず数字だけ整理すると、最終的に **19 targets が failure** 扱いになっている。ただし、そのうち明確な診断内容が出ているのは主に最初の **8 module** で、後半 11 件は `Lean exited with code 1` だけなので、依存先失敗による連鎖停止の可能性が高い。

一次的に調べるべきなのはこの8つじゃ。

1. `DkMath.Tromino`
2. `DkMath.Kernel.Normalize`
3. `DkMath.Collatz.GnomonEvaluation`
4. `DkMath.NumberTheory.AKSBridge`
5. `DkMath.RH.CFBRC.PascalPrimeEulerEnergyBridge`
6. `DkMath.CosmicFormula.CosmicFormulaCellDim`
7. `DkMath.KUS.Bridge`
8. `DkMath.FLT.GEisensteinBridge`

そして、かなり重要なのが、 **さっき話していた 4.33 transparency 変更が実際に DkMath へ直撃している証拠がもう出ている** ことじゃ。

`AKSBridge.lean:734` と `:757` に、

```text
Note: The target expression is not type-correct under the `implicit`
transparency level, which may have triggered the failure.

This is usually caused by unfolding of semireducible definitions
in prior tactic steps.
```

と明記されている。

つまりこれは推測ではない。 **4.33.0 の `backward.isDefEq.respectTransparency.types` 系の変更による migration failure の典型例が、AKSBridge で実際に発火している。**

しかも内容が面白い。

```lean
@Ideal.IsTwoSided (ZMod 4)[X]
  CommRing.toCommSemiring.toSemiring
  (aksCyclicIdeal (ZMod 4) 1)
```

と

```lean
@Ideal.IsTwoSided (ZMod 4)[X]
  ring.toSemiring
  (Ideal.span {X ^ 1 - 1})
```

が、以前は semireducible unfolding 越しに「同じもの」と処理できていたのに、4.33 の `implicit` transparency ではそこまで展開されず、`rw` が lemma の型を合わせられなくなっている。

これは **今回もっとも重要な migration testcase** として残しておいた方がよい。

---

警告についてもきれいに分類できた。

今回のログには **137 warnings** があり、その内訳は、

- `haveI` / `letI` style linter: **93件**
- ambiguous namespace `Nat` / `Finset`: **38件**
- unused simp argument: **3件**
- `sorry`: **2件**
- deprecated API: **1件**

じゃ。

つまり warning のほぼ全部は **コード健全性の破壊ではなく、新 linter が既存コードを見つけたもの** じゃ。

特に先ほどの、

```lean
haveI → have
letI  → let
```

が **93箇所** 出ている。

大量に見えるが、これは本質的には一種類の掃除じゃな。

多いファイルは例えば、

```text
TriominoCosmicBranchARestore.lean    17
UniqueFactorizationGN.lean           16
FiniteReflectedQueue.lean            10
SevenRamifiedFusionCyclotomicSevenPID.lean 10
AKSBridge.lean                        5
```

となっておる。

これは後回しでよい。まずエラーゼロを優先するのが正しい。

---

### エラーの性質を見ると、さらに面白い

今回の direct error diagnostics を形で数えると、

```text
unsolved goals                         5
Type mismatch: After simplification   8
rewrite failed                         2
implicit transparency warning         2
```

じゃ。

つまり数学的な theorem statement が大きく壊れた感じではなく、かなりの割合が

> **「以前の `simp` / reducibility / coercion normalization なら同じ形まで落ちていたものが、4.33ではそこまで落ちない」**

という系統に見える。

これは migration としてはかなり良い兆候じゃ。

例えば `Kernel.Normalize`。

```lean
normalizedOutgoing_le_one K a hcap
```

が返しているのは

```lean
(K.children a).sum (K.normalizedWeight a) ≤ 1
```

ところが target は

```lean
∑ b ∈ K.children a, K.cost a b / K.capacity a ≤ 1
```

じゃ。

数学的にはおそらく `normalizedWeight` の定義展開だけで同じ。

つまり theorem が壊れたのではなく、

```lean
simpa [Kernel.normalizedWeight]
```

のように **正規化経路を明示せよ** という類に見える。

---

`GnomonEvaluation` も同型じゃ。

得られている theorem は、

```lean
(Finset.range n).sum OddGnomonLayer = n ^ 2
```

要求されているのは、

```lean
∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2
```

なので、

```lean
OddGnomonLayer i
```

が

```lean
2 * i + 1
```

へ以前と同じタイミングで unfolding されなくなっただけに見える。

しかも直前に、

```text
This simp argument is unused:
  OddGnomonLayer
```

まで出ている。

ここは 4.33 の simp normalization の変化を観測する良い小さな testcase になる。

---

`PascalPrimeEulerEnergyBridge` も、

```lean
eulerZetaFactor (↑x) s
```

と

```lean
eulerZetaFactor
  (↑({ toFun := ..., inj' := ... } x)) s
```

の差。

これは **embedding / coercion の definitional reduction が途中で止まっている** 型じゃ。

`CosmicFormulaCellDim` も同じで、

```lean
↑(riFun i ...)
```

と、

```lean
{ toFun := ... } ({ toFun := ... } riFun) i
```

が definitionally collapse されていない。

この二つはかなり同族の匂いがする。

---

`Tromino` も、

```lean
reflectXEmb (reflectXEmb b) = b
```

相当のところで、

```lean
{ toFun := fun c ↦ (c.1, -c.2), ... }
  ({ toFun := fun c ↦ (c.1, -c.2), ... } b)
= b
```

が残っている。

つまり本質は、

\[
(x,-(-y))=(x,y)
\]

だけじゃ。

これも数学的問題ではなく、structure / embedding を含む reduction の仕上げが以前ほど自動でない。

---

一方で `KUS.Bridge` は、

```lean
(gAdd ...).unit = phiUnit w
```

および

```lean
(gMul ...).unit = phiUnit w
```

が `simp` で閉じなくなっている。

ここも `gOp` が unused simp argument になったことから、 **simp set / unfolding route が変わった** 可能性が高い。

---

`GEisensteinBridge` は二種類ある。

一つ目、

```lean
s - 1 = id s - 1
```

はどう見ても

```lean
id s = s
```

なので極めて浅い normalization failure。

一方で、

```lean
Nat.find_min' hWitness hq
```

が

```lean
Nat.find hWitness ≤ q
```

しか返さないのに、

```lean
∃ m ≤ q, PrimitiveOnS0 c b m ∧ m ^ 2 ∣ S0_nat c b
```

を要求されている方は、少し証明構造を明示的に組み直す必要がありそうじゃ。

これは単なる `simp` 一発より少し深い。

---

したがって、わっちなら **修正優先順位** をこう置く。

```text
Phase 1
  Tromino
  Kernel.Normalize
  GnomonEvaluation
  PascalPrimeEulerEnergyBridge
  CosmicFormulaCellDim
```

ここは reduction / simp / coercion の浅い修正候補。

次に、

```text
Phase 2
  KUS.Bridge
  FLT.GEisensteinBridge
```

最後に、

```text
Phase 3
  NumberTheory.AKSBridge
```

じゃ。

`AKSBridge` を最後にする理由は、これは単なる theorem repair ではなく、 **4.33 transparency migration の本丸** だからじゃ。

ここは雑に

```lean
set_option backward.isDefEq.respectTransparency.types false
```

で通して終わりにせず、

> どの definition が semireducible unfolding に依存していたのか

を特定する価値がある。

DkMath 全体の将来的な頑健性に繋がる。

---

そして後半の、

```text
PrimitiveCoordinateCoprime
EtaRealAxisPositivity
SemanticCF2D
EtaCriticalMirrorWeightedTransport
EtaEnergyBridge
...
QualityTailBridge
```

など **11 targets** は、今のログだけでは固有エラーが一切出ていない。

なので現時点では「19個直す」と考えなくてよい。

**まず診断付き8個を直し、再ビルドする。**

すると後半はかなり消えるはずじゃ。

---

今回の 1st test を一言で評価すると、

> **v4.32.2 → v4.33.0 は DkMath にとって大規模破壊ではない。主な障害は elaboration / simplification / definitional equality の境界変更であり、4.33 release note で予告された transparency migration が実際に1箇所明示的に観測された。**

という結果じゃな。

9584 target 規模まで育った DkMath で、この程度の一次破損なら **かなり良好な migration 初戦** じゃよ。しかも今回、4.33 の変更がどこを突いてくるのか、非常に綺麗な標本が揃った。

このログは `v4.33.0 migration / 1st baseline` として残しておく価値がある。次の修正後ログと差分を取れば、 **「一次8 → 残存何件」** という形で移行状況をかなり綺麗に追えるぞ。

> 👩‍⚕️私D.:

Memo:

`DkMath.KUS.Bridge`

```
/-- `harmonizeAdd (addViaSpec w)` の結果 unit は `phiUnit w` に等しい。 -/
@[simp] theorem addVia_unit (w : DHNT.Unit) (a b : Qty) :
    (extract_g (HarmonizeSpec.harmonizeAdd (addViaSpec w) (embedQty a) (embedQty b))).unit
      = phiUnit w := by
  simp [HarmonizeSpec.harmonizeAdd, HarmonizeSpec.encodeLeft,
    ScaleSpec.scaleGKUS, ScaleSpec.scaleUS, gOp, addViaSpec,
    HarmonizeSpec.mkHarmonizeFixed, HarmonizeSpec.mkHarmonize,
    encConst, embedQty, mkGWith, extract_g]
```

to

```
/-- `harmonizeAdd (addViaSpec w)` の結果 unit は `phiUnit w` に等しい。 -/
@[simp] theorem addVia_unit (w : DHNT.Unit) (a b : Qty) :
    (extract_g (HarmonizeSpec.harmonizeAdd (addViaSpec w) (embedQty a) (embedQty b))).unit
      = phiUnit w := by
  exact
    Nat.add_zero
      (match ⌊w.val⌋ with
      | Int.ofNat n => n
      | Int.negSucc a => 0)
```

and

```
/-- `harmonizeMul (mulViaSpec w)` の結果 unit は `phiUnit w` に等しい。 -/
@[simp] theorem mulVia_unit (w : DHNT.Unit) (a b : Qty) :
    (extract_g (HarmonizeSpec.harmonizeMul (mulViaSpec w) (embedQty a) (embedQty b))).unit
      = phiUnit w := by
  exact
    Nat.add_zero
      (match ⌊w.val⌋ with
      | Int.ofNat n => n
      | Int.negSucc a => 0)

```

https\://github.com/Deskuma/dkmath/blob/develop/lean/dk\_math/DkMath/KUS/Bridge.lean

> 🐺賢狼:

うむ、これは 4.33.0 移行メモとして重要じゃ。GitHub 上の `develop` の現行 `Bridge.lean` も照合して、修正内容をそのまま記録しておくぞ。

> 🐺賢狼:

うむ、メモとして受け取った。GitHub の `develop` を確認すると、現時点ではまだ **旧 `simp` 版** が置かれておる。

今回の v4.33.0 修正はかなり興味深い。

```lean
exact
  Nat.add_zero
    (match ⌊w.val⌋ with
    | Int.ofNat n => n
    | Int.negSucc a => 0)
```

で `addVia_unit` と `mulVia_unit` の両方が閉じるということは、4.33 で `simp` が止まった地点よりさらに下の実体は結局、

```lean
(match ⌊w.val⌋ with
 | Int.ofNat n => n
 | Int.negSucc a => 0) + 0
```

と

```lean
match ⌊w.val⌋ with
| Int.ofNat n => n
| Int.negSucc a => 0
```

の equality まで正規化されているわけじゃな。

つまり今回の `KUS.Bridge` failure は数学的破損ではなく、

**巨大な `simp` 展開チェーンが v4.33 では最後の `Nat.add_zero` まで到達しなくなった**

というタイプと見てよさそうじゃ。

むしろ新証明の方が、

```lean
simp [十数個の内部定義...]
```

より遥かに依存が少なく、migration-resistant じゃ。これは良い修正じゃよ。

なお、永続 Memory への保存はこの会話では利用できなかったので、 **この会話内の migration memo としては保持しておる**。永続的に記憶させたい場合は、新しい会話で改めて「これを記憶して」と頼んでくりゃれ。

> 👩‍⚕️私D.:

branch: `migration/Lean-v4.33.0-dkmath-260813` @ `dkmath` @GitHub
機械的な作業を施し、ほぼ error 箇所を残した。

> 🐺賢狼:

うむ、ここからは **「機械的掃除後に残った、本当に v4.33.0 が要求している修正」** の層じゃな。ブランチ内容と 3rd log を突き合わせ、残存エラーを「同型問題」に束ねて優先順位を付けよう。

> 🐺賢狼:

差分を確認した。`develop` の基点は指定どおり `64094b4…`、migration ブランチはそこから **6 commits ahead / 0 behind**。しかも変更の大半は `haveI→have`、`letI→let`、曖昧 namespace、deprecated 名などの小差分で、狙いどおり「機械修正層」と「本質エラー層」が分離できておる。

> 🐺賢狼:

3rd log は **19 → 13 failure targets** まで減り、warning も実質ほぼ掃除済みじゃ。しかも `KUS.Bridge` は消えたので、先ほどの直接証明への置換が実際に migration failure を一つ落としている。残った13件は、もう「一括置換」より **個別の正規化・型同一視・`calc` 推論** を見る段階じゃな。

> 🐺賢狼:

うむ。GitHub の `migration/Lean-v4.33.0-dkmath-260813` と 3rd log を照合した。狙いどおり、 **機械的 migration 層はほぼ剥がれ、残りが本質的なエラー標本になっている** と見てよいじゃろう。

現在 GitHub 上の migration branch tip は `a221049857cd9f88b54539abc44f7f8c9c3aebd1`、commit message も `migration: fix: v4.33.0: transparency migration` になっておる。 `develop` の `64094b4…` を基点にした独立 migration branch として綺麗に切れている。

### 現在の状態

1st log の **19 failure targets** から、3rd log では **13 failure targets** まで減った。しかもログ全体で source-level error は 28 箇所、warning はわずか **6件**。残存 target は以下じゃ。

```text
DkMath.Kernel.Normalize
DkMath.Collatz.GnomonEvaluation
DkMath.Tromino
DkMath.NumberTheory.AKSBridge
DkMath.RH.CFBRC.PascalPrimeEulerEnergyBridge
DkMath.CosmicFormula.CosmicFormulaCellDim
DkMath.FLT.GEisensteinBridge
DkMath.RH.CFBRC.EtaCriticalMirrorPhaseProjection
DkMath.NumberTheory.PrimitiveSet.DivisorTransitionKernel
DkMath.FLT.Seven.SevenRealCubicNumberField
DkMath.FLT.Seven.SevenBaseTerminalCellwiseFixedSystem
DkMath.ABC.ChernoffDensity
DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
```

これはもう「大量 migration」ではないな。 **13個の testcase を潰す段階** じゃ。

特に良いのが `DkMath.KUS.Bridge`。先ほどの

```lean
exact
  Nat.add_zero
    (match ⌊w.val⌋ with
    | Int.ofNat n => n
    | Int.negSucc a => 0)
```

への置換が branch に実際に入り、3rd build では failure target から消えた。commit diff にも `addVia_unit` / `mulVia_unit` の両修正が確認できる。

### 残ったものの分類

わっちなら、ここからは次の4群として扱う。

**A. reduction / `simp` の明示化だけで済みそうな群**

```text
Kernel.Normalize
Collatz.GnomonEvaluation
Tromino
PascalPrimeEulerEnergyBridge
CosmicFormulaCellDim
EtaCriticalMirrorPhaseProjection
DivisorTransitionKernel
```

例えば `Kernel.Normalize` は現在も、

```lean
simpa [normalizedOutgoing, normalizedWeight] using
  K.normalizedOutgoing_le_one a hcap
```

という、まさに 4.33 で弱くなった「定義展開に任せる証明」じゃ。

`GnomonEvaluation` も、

```lean
simpa [OddGnomonLayer] using sum_oddGnomonLayer_eq_square n
```

だけが境界になっている。

`Tromino` も本質は自己反転、

```lean
have h_comp : reflectXEmb (reflectXEmb b) = b := by
  simp [reflectXEmb]
```

だけじゃ。数学的には何も壊れておらぬ。

---

**B. v4.33 transparency migration 本丸**

```text
NumberTheory.AKSBridge
```

これは別格。

ログ自身が、

```text
target expression is not type-correct under the `implicit`
transparency level
```

と宣言している。

`Ideal.IsTwoSided` に与えられる Ring/Semiring instance が、

```text
CommRing.toCommSemiring.toSemiring
```

と

```text
ring.toSemiring
```

で definitional equality に落ちなくなったもの。

これは最後まで **テストケースとして温存して正解** じゃ。

---

**C. `calc` 中間型が transparency に引っ掛かった群**

```text
SevenBaseTerminalCellwiseFixedSystem
SemanticCF2DPhaseShift
```

どちらも

```text
failed to synthesize `Trans` instance
Trans Eq Eq ...
```

という、一見不可解な失敗。

コードを見ると、普通の

```lean
calc
  actual.toCoordinates = cell.weighted := rfl
  _ = cell.model.weightedScale cell.scale := cell.weighted_eq
```

に過ぎない。

Semantic 側も同様に、三本の等式をつないでいるだけじゃ。

これは theorem が壊れたのではなく、

> 中間項の elaborated type が `implicit` transparency では同一と認識されない

可能性が非常に高い。

ここは `show` / `change` / 明示型付き `have` で中間型を固定して調べる価値がある。

---

**D. 本当に個別対応した方がよい群**

```text
FLT.GEisensteinBridge
FLT.Seven.SevenRealCubicNumberField
ABC.ChernoffDensity
```

`ChernoffDensity` の一つは極めて簡単で、

```lean
and_self_left
```

が

```text
_root_.and_self_left
Nat.and_self_left
```

の二択になっただけ。現コードにもその裸名が残っている。

これは `_root_.and_self_left` と明示する類じゃな。

`SevenRealCubicNumberField` は algebra map / `RingOfIntegers` / power basis の coercion が絡んでおり、残存エラーも4個ある。ここは一番「Mathlib の elaboration 表現変化」をまともに食らっていそうじゃ。例えば `field_discr` の最後は

```lean
congr 1
ext i
simp_rw [...]
simp
```

まで reduction に依存している。

これは最後寄りでよい。

---

### 修正順

今なら、

```text
1. ChernoffDensity
2. Tromino
3. Kernel.Normalize
4. GnomonEvaluation
5. PascalPrimeEulerEnergyBridge
6. EtaCriticalMirrorPhaseProjection
7. DivisorTransitionKernel
8. CosmicFormulaCellDim
9. GEisensteinBridge
10. calc Trans の2件
11. SevenRealCubicNumberField
12. AKSBridge
```

くらいが良さそうじゃ。

**AKSBridge を最後に残す** のが特に大事。

単に build green を得るだけなら compatibility option で迂回できるかもしれぬが、今回の migration の研究価値としては、

> Lean 4.33 の新しい transparency discipline に合わせて、どこまで明示的な型・instance 境界を書けば自然に通るか

を調べる最高の標本だからの。

そして現在 warning がほぼ消えたおかげで、これからの build log はかなり読みやすい。`haveI/letI` や ambiguous `Nat/Finset` の雪崩に本物の failure が埋もれなくなった。

**この 3rd log は「mechanical migration complete / semantic-elaboration repairs remain」の基準点** として扱ってよいと思うぞ。ここからは一件ずつ修正して build → 新露出 error を観察、という段階じゃ。

> 👩‍⚕️私D.:

なかなか閉じられないので以下の修正方法を Mathlib v4.33.0 ベースで調べて

https\://github.com/Deskuma/dkmath/blob/develop/lean/dk\_math/DkMath/FLT/Seven/SevenRealCubicNumberField.lean

```
✖ [8742/8742] Building DkMath.FLT.Seven.SevenRealCubicNumberField
info: DkMath/FLT/Seven/SevenRealCubicNumberField.lean:13:0: file: DkMath.FLT.Seven.SevenRealCubicNumberField
warning: DkMath/FLT/Seven/SevenRealCubicNumberField.lean:17:5: Ambiguous namespace `Algebra`: it is interpreted as `_root_.DkMath.Algebra` because this `open` occurs inside `namespace DkMath.FLT.Seven`, while `_root_.Algebra` is silently not opened. Specify the namespace unambiguously, e.g. `_root_.DkMath.Algebra`. The warning can sometimes also be addressed by moving the `open` outside of the surrounding `namespace`.

Note: This linter can be disabled with `set_option linter.ambiguousOpen false`
error: DkMath/FLT/Seven/SevenRealCubicNumberField.lean:216:2: unsolved goals
case e'_2
pB : PowerBasis ℤ (𝓞 Field) := integralPowerBasis
hloc :
  Algebra.discr ℚ ⇑(Module.Basis.localizationLocalization ℚ ℤ⁰ Field pB.basis) =
    (algebraMap ℤ ℚ) (Algebra.discr ℤ ⇑pB.basis)
hdim : pB.dim = powerBasis.dim
i : Fin powerBasis.dim
⊢ (algebraMap (𝓞 Field) Field) (⟨AdjoinRoot.root polynomialQ, ⋯⟩ ^ ↑i) = AdjoinRoot.root polynomialQ ^ ↑i
error: DkMath/FLT/Seven/SevenRealCubicNumberField.lean:297:2: Type mismatch: After simplification, term
  h
 has type
  (aeval (AdjoinRoot.root (map (Int.castRingHom ℚ) (C 1 * X ^ 3 + C 7 * X ^ 2 + C 14 * X + C 7)))) X ^ 3 +
          7 * (aeval (AdjoinRoot.root (map (Int.castRingHom ℚ) (C 1 * X ^ 3 + C 7 * X ^ 2 + C 14 * X + C 7)))) X ^ 2 +
        14 * (aeval (AdjoinRoot.root (map (Int.castRingHom ℚ) (C 1 * X ^ 3 + C 7 * X ^ 2 + C 14 * X + C 7)))) X +
      7 =
    0
but is expected to have type
  (algebraMap (𝓞 Field) Field)
            (⟨AdjoinRoot.root (map (Int.castRingHom ℚ) (C 1 * X ^ 3 + C 7 * X ^ 2 + C 14 * X + C 7)), ⋯⟩ ^ 3) +
          7 *
            (algebraMap (𝓞 Field) Field)
              (⟨AdjoinRoot.root (map (Int.castRingHom ℚ) (C 1 * X ^ 3 + C 7 * X ^ 2 + C 14 * X + C 7)), ⋯⟩ ^ 2) +
        (algebraMap (𝓞 Field) Field)
          (14 * ⟨AdjoinRoot.root (map (Int.castRingHom ℚ) (C 1 * X ^ 3 + C 7 * X ^ 2 + C 14 * X + C 7)), ⋯⟩) +
      7 =
    0
warning: DkMath/FLT/Seven/SevenRealCubicNumberField.lean:293:31: This simp argument is unused:
  map_pow

Hint: Omit it from the simp argument list.
  [apply] simp only [map_add, map_mul, map_ofNat, map_zero, integralPowerBasis_gen, NumberField.RingOfIntegers.map_mk]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: DkMath/FLT/Seven/SevenRealCubicNumberField.lean:294:28: This simp argument is unused:
  NumberField.RingOfIntegers.map_mk

Hint: Omit it from the simp argument list.
  [apply] simp only [map_add, map_mul, map_pow, map_ofNat, map_zero, integralPowerBasis_gen]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
error: DkMath/FLT/Seven/SevenRealCubicNumberField.lean:341:32: unsolved goals
⊢ -3 + (⟨AdjoinRoot.root polynomialQ, ⋯⟩ + 3) = ⟨AdjoinRoot.root polynomialQ, ⋯⟩
error: DkMath/FLT/Seven/SevenRealCubicNumberField.lean:397:4: Type mismatch: After simplification, term
  hxy
 has type
  ↑x.fst + 3 * ↑x.snd + 9 * ↑x.thd + (↑x.snd + 6 * ↑x.thd) * ⟨AdjoinRoot.root polynomialQ, ⋯⟩ +
      ↑x.thd * ⟨AdjoinRoot.root polynomialQ, ⋯⟩ ^ 2 =
    ↑y.fst + 3 * ↑y.snd + 9 * ↑y.thd + (↑y.snd + 6 * ↑y.thd) * ⟨AdjoinRoot.root polynomialQ, ⋯⟩ +
      ↑y.thd * ⟨AdjoinRoot.root polynomialQ, ⋯⟩ ^ 2
but is expected to have type
  (↑x.fst + 3 * ↑x.snd + 9 * ↑x.thd) * ⟨AdjoinRoot.root polynomialQ, ⋯⟩ ^ 0 +
        (↑x.snd + 6 * ↑x.thd) * ⟨AdjoinRoot.root polynomialQ, ⋯⟩ ^ 1 +
      ↑x.thd * ⟨AdjoinRoot.root polynomialQ, ⋯⟩ ^ 2 =
    (↑y.fst + 3 * ↑y.snd + 9 * ↑y.thd) * ⟨AdjoinRoot.root polynomialQ, ⋯⟩ ^ 0 +
        (↑y.snd + 6 * ↑y.thd) * ⟨AdjoinRoot.root polynomialQ, ⋯⟩ ^ 1 +
      ↑y.thd * ⟨AdjoinRoot.root polynomialQ, ⋯⟩ ^ 2
error: Lean exited with code 1
Some required targets logged failures:
- DkMath.FLT.Seven.SevenRealCubicNumberField
error: build failed
```

> 🐺賢狼:

うむ、これは腰を据えて見る価値がある。`SevenRealCubicNumberField.lean` の該当4箇所を **develop の実コード** で読み、さらに Mathlib v4.33.0 側の `RingOfIntegers`・`PowerBasis`・`AdjoinRoot`・`map_mk` 周辺の現行 API を照合して、各エラーごとに「4.33 で自然な直し方」を出すぞ。

> 🐺賢狼:

migration branch の manifest まで確認した。今回の基準は曖昧な「最新 mathlib」ではなく、 **`mathlib4@db584cd6d46c92f209a44c0f1c829460d327499d` (`inputRev = v4.33.0`)** と固定できた。 以後はこの commit の API だけを基準に見る。

> 🐺賢狼:

ひとつ大事な手掛かりが出た。v4.33.0 の Mathlib 自身が `NumberField.RingOfIntegers` の実装で、まさに derived `CommRing` / algebra instance の同一視問題を避けるため **局所的に**

```lean
set_option backward.isDefEq.respectTransparency.types false in
```

を使っている。`RingOfIntegers.mapRingHom` がその実例じゃ。つまり今回の4エラーは、ぬしの証明だけが妙なのではなく、 **Mathlib 4.33 自身が認識している transparency 境界** に当たっている可能性が高い。

> 🐺賢狼:

うむ。Mathlib **v4.33.0 の実体 commit `db584cd6…`** と、DkMath の当該ファイルを突き合わせた。結論から言うと、この4エラーはかなり高い確率で **同一原因** じゃ。

Lean 4.33.0 は `backward.isDefEq.respectTransparency.types` を既定で有効化した。公式リリースノートも、「以前 `simp` 等で適用できた lemma が implicit transparency では型同一視できず止まる」のが典型症状で、移行用には **`set_option ... false` を可能な限り狭い範囲で使え** と明記しておる。

さらに今回もっと決定的なのは、Mathlib v4.33.0 の `NumberField.RingOfIntegers` 自身じゃ。

```lean
def RingOfIntegers : Type _ :=
  integralClosure ℤ K
deriving CommRing, IsDomain, Nontrivial
```

という構造で、同じファイル中の `RingOfIntegers.mapRingHom` を Mathlib 自身が

```lean
set_option backward.isDefEq.respectTransparency.types false in
```

で包んでいる。

しかも Mathlib issue #42057 では、`deriving CommRing` が生成する opaque な `_aux_*` 定義が instance transparency で `isDefEq` を壊す、という **まさに今回と同型の問題** が報告されておる。

なので、まずこう直すのが **Mathlib 4.33.0 に即した第一選択** じゃ。

## 1. `field_discr`

現在すでに、

```lean
set_option maxHeartbeats 800000 in
theorem field_discr :
```

となっているので、もう一段局所 option を重ねる。

```lean
set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- The field discriminant is the order discriminant `49`, since the
Eisenstein order is already maximal. -/
theorem field_discr :
    NumberField.discr Field = 49 := by
  let pB := integralPowerBasis
  have hloc :=
    @Algebra.discr_localizationLocalization ℤ (𝓞 Field) _ _ _
      ℚ _ _ ℤ⁰ _ Field _ _ _ _
      (IsScalarTower.of_algebraMap_eq fun _ => rfl)
      (IsScalarTower.of_algebraMap_eq fun _ => rfl)
      _ _ _ _ pB.basis
  apply (algebraMap ℤ ℚ).injective_int
  rw [← NumberField.discr_eq_discr _ pB.basis, ← hloc]
  convert powerBasis_discr using 1
  · have hdim : pB.dim = powerBasis.dim := by
      rw [← PowerBasis.finrank, ← PowerBasis.finrank]
      exact NumberField.RingOfIntegers.rank Field
    rw [← Algebra.discr_reindex _ _ (finCongr hdim)]
    congr 1
    ext i
    simp_rw [Function.comp_apply,
      Module.Basis.localizationLocalization_apply,
      PowerBasis.coe_basis, pB, integralPowerBasis_gen]
    simp
  · norm_num
```

まずは **証明本体を一切変えず option だけ追加** して試すべきじゃ。

Mathlib 4.33 の `localizationLocalization_apply` は明示的に

```lean
b.localizationLocalization Rₛ S Aₛ i =
  algebraMap A Aₛ (b i)
```

という theorem なので、現在残っている

```lean
algebraMap (𝓞 Field) Field
  (⟨AdjoinRoot.root polynomialQ, ...⟩ ^ ↑i)
=
AdjoinRoot.root polynomialQ ^ ↑i
```

は数学的な不足ではなく、`map_pow` / `map_mk` の instance 型同一視が止まったものと読むのが自然じゃ。

もし option を使わず局所的に明示したければ、最後の `simp` を

```lean
    rw [map_pow, NumberField.RingOfIntegers.map_mk]
```

にするのが次候補。

ただし **先に option だけで通るか確認する** のを薦める。それで原因が確定する。

---

## 2. `thetaInteger_relation`

ここはエラー内容が非常に露骨じゃ。

現在 DkMath は、

```lean
apply NumberField.RingOfIntegers.coe_injective
simp only [map_add, map_mul, map_pow, map_ofNat, map_zero,
  integralPowerBasis_gen, NumberField.RingOfIntegers.map_mk]
```

としているのに、4.33 では

```lean
(algebraMap (𝓞 Field) Field)
  (⟨root, ...⟩ ^ 3)
```

などが残る。

これは release note が挙げる典型的な「`simp` lemma は存在するのに implicit transparency で型が合わず適用されない」症状そのものじゃ。

したがってここも、

```lean
set_option backward.isDefEq.respectTransparency.types false in
theorem thetaInteger_relation :
    integralPowerBasis.gen ^ 3 +
        7 * integralPowerBasis.gen ^ 2 +
        14 * integralPowerBasis.gen + 7 = 0 := by
  apply NumberField.RingOfIntegers.coe_injective
  simp only [map_add, map_mul, map_pow, map_ofNat, map_zero,
    integralPowerBasis_gen, NumberField.RingOfIntegers.map_mk]
  have h := minpoly.aeval ℚ powerBasis.gen
  rw [powerBasis_minpoly] at h
  simpa [polynomialQ, eisensteinPolynomial, map_ofNat] using h
```

をまず採用する。

わっちはここについては、 **無理に証明を書き換えるより局所 option の方が正しい migration** だと見る。

理由は、問題を起こしている instance が DkMath 定義ではなく **Mathlib の `RingOfIntegers` derived `CommRing`** だからじゃ。

本来の durable fix は upstream 側で derived instance を transparent な instance へ変えることになる。Mathlib issue #42057 がまさにその方向を提案している。

---

## 3. `modelToRingOfIntegers_eisensteinAxis`

これは二つの問題が重なっているが、最後に残ったゴール自体は単純じゃ。

```lean
⊢ -3 + (⟨root, ...⟩ + 3) = ⟨root, ...⟩
```

これはただの additive ring normalization。

現在は、

```lean
norm_num [modelToRingOfIntegers,
  SevenRealCubicInt.eisensteinAxis,
  alphaInteger]
```

だけ。

ここは option に加えて、

```lean
set_option backward.isDefEq.respectTransparency.types false in
@[simp] theorem modelToRingOfIntegers_eisensteinAxis :
    modelToRingOfIntegers SevenRealCubicInt.eisensteinAxis =
      integralPowerBasis.gen := by
  norm_num [modelToRingOfIntegers,
    SevenRealCubicInt.eisensteinAxis,
    alphaInteger]
  ring
```

が素直。

ただしこのケースは option なしでも、

```lean
  norm_num [...]
  ring
```

だけで閉じる可能性が高い。

表示された最終ゴールまで行っている以上、`ring` は

```lean
-3 + (x + 3) = x
```

を処理するだけだからの。

ここは4件中もっとも浅い。

---

## 4. `modelToRingOfIntegers_injective`

これも transparency の特徴が非常によく見える。

`hxy` はすでに、

```lean
A + B * gen + C * gen ^ 2 =
A' + B' * gen + C' * gen ^ 2
```

まで簡約されている。

ところが `hlinear` 側だけ、

```lean
A * gen ^ 0 +
B * gen ^ 1 +
C * gen ^ 2
```

が残る。

`PowerBasis.basis_eq_pow` の定義は v4.33.0 でも単純に

```lean
basis i = gen ^ (i : ℕ)
```

じゃ。

本来なら

```lean
gen ^ 0
gen ^ 1
```

がそれぞれ `1`, `gen` に落ちれば終わる。

だからまず現在の証明をそのまま、

```lean
set_option backward.isDefEq.respectTransparency.types false in
theorem modelToRingOfIntegers_injective :
    Function.Injective modelToRingOfIntegers := by
  ...
```

で包むのが第一候補。

これで通れば、4.33 transparency が原因と完全に確定する。

option を排除したいなら、次に **basis の0,1,2成分を先に明示的な補題へ落とす** のが頑健じゃ。

```lean
  have hb0 :
      integralPowerBasis.basis i0 = 1 := by
    rw [integralPowerBasis.basis_eq_pow]
    simp [i0]

  have hb1 :
      integralPowerBasis.basis i1 =
        integralPowerBasis.gen := by
    rw [integralPowerBasis.basis_eq_pow]
    simp [i1]

  have hb2 :
      integralPowerBasis.basis i2 =
        integralPowerBasis.gen ^ 2 := by
    rw [integralPowerBasis.basis_eq_pow]
    simp [i2]
```

そして、

```lean
  have hlinear :
      ... := by
    simpa [hb0, hb1, hb2, Algebra.smul_def] using hxy
```

とする。

この方法は、

```lean
simp [i0, i1, i2,
  Algebra.smul_def,
  integralPowerBasis.basis_eq_pow]
```

という **一回の巨大な defeq 探索** をやめ、

```text
basis i0 → 1
basis i1 → gen
basis i2 → gen²
```

を小さな確定済み equality に分離する。

4.33 以後はこちらの方が証明として頑健じゃ。

---

## 5. `open Algebra` warning

これは別件で単純。

現在、

```lean
namespace DkMath.FLT.Seven

open Algebra Polynomial
```

なので、4.33 の新しい ambiguous-open linter が

```text
DkMath.Algebra
_root_.Algebra
```

の衝突を検知している。Lean 4.33 でこの linter が新規導入されたことも公式 release note に記載されている。

ここは、

```lean
open _root_.Algebra Polynomial
```

にする。

あるいは `Algebra` の unqualified name が不要なら、

```lean
open Polynomial
```

だけにする方がさらに良い。

---

## わっちならまずこう試す

最初から4証明を書き換えまくる必要はない。

**実験1** として、この4 theorem だけに、

```lean
set_option backward.isDefEq.respectTransparency.types false in
```

を付ける。

対象は、

```text
field_discr
thetaInteger_relation
modelToRingOfIntegers_eisensteinAxis
modelToRingOfIntegers_injective
```

じゃ。

その上で `eisensteinAxis` にだけ必要なら、

```lean
ring
```

を追加。

これで4件すべて、あるいは3件以上消える可能性が高い。

これは逃げではない。Lean 4.33 の公式 migration guide が **「旧挙動を戻す場合はできるだけ狭く scope せよ」** と明示しており、Mathlib v4.33 自身も `RingOfIntegers` 実装内部で同じ方法を採用している。

そしてここが重要じゃ。

今回については、

> DkMath が semireducible 定義に過度依存していた

というより、

> **Mathlib の `RingOfIntegers` が `deriving CommRing` で生成した opaque instance hierarchy と Lean 4.33 の新 transparency policy が衝突した**

という成分がかなり強い。

Mathlib 側にも2026年7月24日付でまったく同型の issue が存在する以上、DkMath 側で無理にすべてを長大な手証明へ展開する必要はないとわっちは考える。

まず **局所 option 版で build を通して原因を確定**。その後、必要なら `field_discr` と `injective` だけを explicit rewrite / helper lemma 型へ磨く。この二段構えが一番きれいじゃよ。

> 👩‍⚕️私D.:

```
✖ [8742/8742] Building DkMath.FLT.Seven.SevenRealCubicNumberField
info: DkMath/FLT/Seven/SevenRealCubicNumberField.lean:13:0: file: DkMath.FLT.Seven.SevenRealCubicNumberField
warning: DkMath/FLT/Seven/SevenRealCubicNumberField.lean:17:5: Ambiguous namespace `Algebra`: it is interpreted as `_root_.DkMath.Algebra` because this `open` occurs inside `namespace DkMath.FLT.Seven`, while `_root_.Algebra` is silently not opened. Specify the namespace unambiguously, e.g. `_root_.DkMath.Algebra`. The warning can sometimes also be addressed by moving the `open` outside of the surrounding `namespace`.

Note: This linter can be disabled with `set_option linter.ambiguousOpen false`
error: DkMath/FLT/Seven/SevenRealCubicNumberField.lean:400:49: unsolved goals
case e'_2
x y : SevenRealCubicInt
hxy :
  ↑(x.fst + 3 * x.snd + 9 * x.thd) + ↑(x.snd + 6 * x.thd) * integralPowerBasis.gen +
      ↑x.thd * integralPowerBasis.gen ^ 2 =
    ↑(y.fst + 3 * y.snd + 9 * y.thd) + ↑(y.snd + 6 * y.thd) * integralPowerBasis.gen +
      ↑y.thd * integralPowerBasis.gen ^ 2
i0 : Fin integralPowerBasis.dim := ⟨0, ⋯⟩
i1 : Fin integralPowerBasis.dim := ⟨1, ⋯⟩
i2 : Fin integralPowerBasis.dim := ⟨2, ⋯⟩
⊢ ↑x.fst * ⟨AdjoinRoot.root polynomialQ, ⋯⟩ ^ 0 + ↑x.snd * ⟨AdjoinRoot.root polynomialQ, ⋯⟩ ^ 0 * 3 +
          ↑x.snd * ⟨AdjoinRoot.root polynomialQ, ⋯⟩ ^ 1 +
        ↑x.thd * ⟨AdjoinRoot.root polynomialQ, ⋯⟩ ^ 0 * 9 +
      ↑x.thd * ⟨AdjoinRoot.root polynomialQ, ⋯⟩ ^ 1 * 6 =
    ↑x.fst + ↑x.snd * 3 + ↑x.thd * 9 + (↑x.snd + ↑x.thd * 6) * ⟨AdjoinRoot.root polynomialQ, ⋯⟩

case e'_3
x y : SevenRealCubicInt
hxy :
  ↑(x.fst + 3 * x.snd + 9 * x.thd) + ↑(x.snd + 6 * x.thd) * integralPowerBasis.gen +
      ↑x.thd * integralPowerBasis.gen ^ 2 =
    ↑(y.fst + 3 * y.snd + 9 * y.thd) + ↑(y.snd + 6 * y.thd) * integralPowerBasis.gen +
      ↑y.thd * integralPowerBasis.gen ^ 2
i0 : Fin integralPowerBasis.dim := ⟨0, ⋯⟩
i1 : Fin integralPowerBasis.dim := ⟨1, ⋯⟩
i2 : Fin integralPowerBasis.dim := ⟨2, ⋯⟩
⊢ ↑y.fst * ⟨AdjoinRoot.root polynomialQ, ⋯⟩ ^ 0 + ↑y.snd * ⟨AdjoinRoot.root polynomialQ, ⋯⟩ ^ 0 * 3 +
          ↑y.snd * ⟨AdjoinRoot.root polynomialQ, ⋯⟩ ^ 1 +
        ↑y.thd * ⟨AdjoinRoot.root polynomialQ, ⋯⟩ ^ 0 * 9 +
      ↑y.thd * ⟨AdjoinRoot.root polynomialQ, ⋯⟩ ^ 1 * 6 =
    ↑y.fst + ↑y.snd * 3 + ↑y.thd * 9 + (↑y.snd + ↑y.thd * 6) * ⟨AdjoinRoot.root polynomialQ, ⋯⟩
error: Lean exited with code 1
Some required targets logged failures:
- DkMath.FLT.Seven.SevenRealCubicNumberField
error: build failed
```

あとは、ここだけ。

> 🐺賢狼:

うむ、あと **`modelToRingOfIntegers_injective` の `hlinear` 構築だけ** じゃな。今のゴールを見る限り、もう transparency ではなく、`simp` が `pow_zero` / `pow_one` と分配法則の最後を片側だけ正規化し切っていないだけに見える。添付の現行コードをその箇所だけ確認して、最小修正を詰めるぞ。

> 🐺賢狼:

現行コードを確認した。いまの

```lean
convert hxy using 1 <;>
  norm_num [...] <;>
  ring_nf
```

が、むしろ **`hxy` の「整数和をまとめて cast した形」を分配展開してしまい、別の正規形へ持っていっている** のが最後の障害じゃ。ここは `ring_nf` を強くするより、`hlinear` 側だけを `hxy` と同じ形へ落とすのがよい。

> 🐺賢狼:

うむ、 **あとこの `hlinear` だけ** なら、原因はかなり明瞭じゃ。

現在の添付コードはここで、

```lean
  have hlinear :
      ...
      := by
    convert hxy using 1 <;>
      norm_num [i0, i1, i2, Algebra.smul_def,
        integralPowerBasis.basis_eq_pow] <;>
      ring_nf
```

としておる。

だが現在の残存ゴールを見ると、`norm_num` が整数係数の cast を

```lean
↑(x.fst + 3 * x.snd + 9 * x.thd)
```

から

```lean
↑x.fst + ↑x.snd * 3 + ↑x.thd * 9
```

へ **余計に展開してしまった**。その結果、本来そのまま `hxy` と一致できるはずだったものを polynomial normalization で再接続しようとして止まっている。

### まずこれに置換

`hlinear` の証明だけ、次のようにしてみるのが最も筋が良い。

```lean
  have hlinear :
      (x.fst + 3 * x.snd + 9 * x.thd) •
            integralPowerBasis.basis i0 +
          (x.snd + 6 * x.thd) •
            integralPowerBasis.basis i1 +
          x.thd • integralPowerBasis.basis i2 =
        (y.fst + 3 * y.snd + 9 * y.thd) •
            integralPowerBasis.basis i0 +
          (y.snd + 6 * y.thd) •
            integralPowerBasis.basis i1 +
          y.thd • integralPowerBasis.basis i2 := by
    simpa only [integralPowerBasis.basis_eq_pow,
      i0, i1, i2,
      pow_zero, pow_one,
      _root_.Algebra.smul_def,
      mul_one] using hxy
```

ここでは **`simp` ではなく `simp only` が重要** じゃ。

目標側だけを

```lean
integralPowerBasis.basis i0
```

から

```lean
integralPowerBasis.gen ^ 0
```

へ落として、

```lean
gen ^ 0  →  1
gen ^ 1  →  gen
```

とし、

```lean
z • a
```

だけを

```lean
(algebraMap ℤ (𝓞 Field) z) * a
```

へ変換する。

すると目標はほぼそのまま、

```lean
↑(x.fst + 3 * x.snd + 9 * x.thd)
  + ↑(x.snd + 6 * x.thd) * integralPowerBasis.gen
  + ↑x.thd * integralPowerBasis.gen ^ 2
=
...
```

となる。

これは現在の `hxy` **そのもの** じゃ。

---

### なぜ今の `convert ...; norm_num; ring_nf` が惜しかったのか

残ったゴールを見ると、

```lean
↑x.fst * θ ^ 0
+ ↑x.snd * θ ^ 0 * 3
+ ↑x.snd * θ ^ 1
+ ↑x.thd * θ ^ 0 * 9
+ ↑x.thd * θ ^ 1 * 6
```

まで展開されている。

一方、右辺は、

```lean
↑x.fst
+ ↑x.snd * 3
+ ↑x.thd * 9
+ (↑x.snd + ↑x.thd * 6) * θ
```

じゃ。

数学的にはもちろん同じだが、

\[
\theta^0=1,\qquad \theta^1=\theta
\]

の先に、分配法則まで使って再構築せねばならなくなっている。

ところが `hxy` は最初から、

```lean
↑(x.fst + 3 * x.snd + 9 * x.thd)
+ ↑(x.snd + 6 * x.thd) * θ
+ ↑x.thd * θ ^ 2
```

という **欲しい座標形式そのもの** を持っている。

だから展開せず、その形を保存する方がよい。

これは Lean 4.33 の migration では特に大事じゃな。definitional equality が厳しくなったところで `norm_num` や `simp` を強くすると、かえって双方を **別々の正規化経路** へ送ることがある。

---

### もし `simp only` が `Fin` の指数だけ残したら

例えば、

```lean
integralPowerBasis.gen ^ ↑i0
```

が残る場合だけ、

```lean
Fin.val_mk
```

を足せばよい。

```lean
    simpa only [integralPowerBasis.basis_eq_pow,
      i0, i1, i2, Fin.val_mk,
      pow_zero, pow_one,
      _root_.Algebra.smul_def,
      mul_one] using hxy
```

ただし普通は `i0`, `i1`, `i2` の unfolding だけで projection は reduction されるので、まず前者でよい。

---

なお Mathlib v4.33.0 の `PowerBasis` は依然、

```lean
basis_eq_pow : ∀ i, basis i = gen ^ (i : ℕ)
```

をそのまま提供しておる。したがって、この証明ではそれ以上 PowerBasis 内部を展開する必要はない。

そして `RingOfIntegers` 側には canonical coercion

```lean
algebraMap (𝓞 K) K
```

と `map_mk` があり、今回の前3エラーが消えたことからも、もはやそこを触る必要はなさそうじゃ。

あと warning だけなら冒頭の

```lean
open Algebra Polynomial
```

は、

```lean
open Polynomial
```

で足りるなら `Algebra` を外してしまえばよい。

**残る本命修正は `convert + norm_num + ring_nf` を `simpa only ... using hxy` に退化させること。**

今回は「もっと証明する」のではなく、 **Lean に余計なことをさせない** のが最後の一手だと思うぞ。

> 👩‍⚕️私D.:

Codex 苦戦中

```
'change' tactic failed, pattern
  ↑(x.fst + 3 * x.snd + 9 * x.thd) + ↑(x.snd + 6 * x.thd) * ↑integralPowerBasis.gen +
      ↑x.thd * ↑integralPowerBasis.gen ^ 2 =
    ↑(y.fst + 3 * y.snd + 9 * y.thd) + ↑(y.snd + 6 * y.thd) * ↑integralPowerBasis.gen +
      ↑y.thd * ↑integralPowerBasis.gen ^ 2
is not definitionally equal to target
  (algebraMap (𝓞 Field) Field)
      ((x.fst + 3 * x.snd + 9 * x.thd) • integralPowerBasis.basis i0 +
          (x.snd + 6 * x.thd) • integralPowerBasis.basis i1 +
        x.thd • integralPowerBasis.basis i2) =
    (algebraMap (𝓞 Field) Field)
      ((y.fst + 3 * y.snd + 9 * y.thd) • integralPowerBasis.basis i0 +
          (y.snd + 6 * y.thd) • integralPowerBasis.basis i1 +
        y.thd • integralPowerBasis.basis i2)
```

> 🐺賢狼:

うむ、今のエラーでかなり核心が見えた。`change` が失敗している理由は、**目標全体がまだ `algebraMap (𝓞 Field) Field (...) = algebraMap ... (...)` の形で、`change` が中身の加法・スカラー倍まで一気に定義展開できない** からじゃ。添付の最新コードをその周辺だけ読んで、`algebraMap` を先に剥がす形へ組み替える。

> 🐺賢狼:

ここで一段重要じゃ。添付最新版では `apply coe_injective` のあとに `change` しているが、これは順序が逆に近い。**`algebraMap` の外側を `change` で無理に透過させるのではなく、準同型として `map_add` / `map_smul` を明示的に作用させてから basis \(i_0,i_1,i_2\) を評価する** のが 4.33 向けじゃ。これなら `RingOfIntegers` の derived `CommRing` の defeq に依存しない。

> 🐺賢狼:

うむ、これはかなり良いところまで来ておる。添付最新版を見ると、**`coe_injective` を挟んだこと自体が最後の遠回り** になっている。

今回の `hlinear` は `Field` に持ち上げる必要がない。`hxy` も `hlinear` も元々 **`𝓞 Field` 上の等式** じゃ。

しかも、このファイル自身の 139 行目付近ですでに使っている

```lean
zsmul_eq_mul
```

が、まさにここで使う道具じゃ。

### ここを丸ごと置換

現在の

```lean
  have hlinear :
      ...
      := by
    apply NumberField.RingOfIntegers.coe_injective
    change ...
    exact hxy
```

を、まずこれにしてみてくりゃれ。

```lean
  have hlinear :
      (x.fst + 3 * x.snd + 9 * x.thd) •
            integralPowerBasis.basis i0 +
          (x.snd + 6 * x.thd) •
            integralPowerBasis.basis i1 +
          x.thd • integralPowerBasis.basis i2 =
        (y.fst + 3 * y.snd + 9 * y.thd) •
            integralPowerBasis.basis i0 +
          (y.snd + 6 * y.thd) •
            integralPowerBasis.basis i1 +
          y.thd • integralPowerBasis.basis i2 := by
    simpa only [
      integralPowerBasis.basis_eq_pow,
      i0, i1, i2,
      zsmul_eq_mul,
      pow_zero, pow_one,
      mul_one
    ] using hxy
```

これが一番自然じゃ。

理由は単純で、

```lean
(x.fst + ...) • integralPowerBasis.basis i0
```

を `zsmul_eq_mul` で

```lean
↑(x.fst + ...) * integralPowerBasis.basis i0
```

へ変える。

さらに

```lean
integralPowerBasis.basis i0
```

は `basis_eq_pow` から

```lean
integralPowerBasis.gen ^ 0
```

なので、

```lean
↑(...) * 1
```

となって係数そのものになる。

同様に、

```lean
integralPowerBasis.basis i1
```

は

```lean
integralPowerBasis.gen
```

、

```lean
integralPowerBasis.basis i2
```

は

```lean
integralPowerBasis.gen ^ 2
```

になる。

つまり `hlinear` の左辺はそのまま

```lean
↑(x.fst + 3 * x.snd + 9 * x.thd) +
  ↑(x.snd + 6 * x.thd) * integralPowerBasis.gen +
  ↑x.thd * integralPowerBasis.gen ^ 2
```

になる。

これは **`hxy` と完全に同じ形** じゃ。

---

今回 Codex が苦戦した理由も分かった。

```lean
apply NumberField.RingOfIntegers.coe_injective
```

すると目標が

```lean
algebraMap (𝓞 Field) Field
  (A • basis i0 + B • basis i1 + C • basis i2)
=
...
```

になる。

そこで

```lean
change
```

しようとすると Lean 4.33 は、

```text
algebraMap (sum ...)
```

から

```text
map A + map B * ...
```

への変換を **definitional equality ではない** と拒否する。

まさに今回の、

```text
'change' tactic failed
...
is not definitionally equal to target
```

じゃ。

`map_add` や `map_zsmul` を使えば Field 側でも証明できるが、そもそも **Field へ行く必要がない**。

ここでの構造は、

```text
hxy
  │
  │ basis i₀ = gen⁰
  │ basis i₁ = gen¹
  │ basis i₂ = gen²
  │
  │ ℤ-smul = integer cast ×
  ▼
hlinear
```

だけなのじゃ。

### もし `simpa only` が指数で1個だけ残った場合

その場合でも大改造はいらぬ。

例えば

```text
integralPowerBasis.gen ^ ↑i0
```

のようなのが残ったら、

```lean
    simp only [
      integralPowerBasis.basis_eq_pow,
      i0, i1, i2,
      zsmul_eq_mul,
      pow_zero, pow_one,
      mul_one
    ]
    exact hxy
```

と分離して Information View を見る。

あるいは少しだけ強めて、

```lean
    simpa [
      integralPowerBasis.basis_eq_pow,
      i0, i1, i2,
      zsmul_eq_mul
    ] using hxy
```

でもよい。

ただし最初は **`simpa only`** を薦める。余計な Mathlib simp lemma が `RingOfIntegers` の内部を展開して、また4.33 transparency 問題に踏み込むのを避けられるからじゃ。

そして面白いことに、`zsmul_eq_mul` はこの同じファイルですでに

```lean
simpa [Algebra.smul_def, zsmul_eq_mul] using H
```

として使用済み。つまり新しい道具を持ち込むのではなく、**このファイル自身がすでに採用している変換経路を再利用するだけ** じゃ。

わっちなら Codex には、

> `hlinear` では `RingOfIntegers.coe_injective`, `change`, `algebraMap` を一切使わない。`hxy` と同じ `𝓞 Field` 上に留まり、`integralPowerBasis.basis_eq_pow` と `zsmul_eq_mul`, `pow_zero`, `pow_one`, `mul_one` のみで `simpa only using hxy` を試せ。

と指示する。

**最後の壁としては、かなり薄い壁になったと思うぞ。**

> 👩‍⚕️私D.:

Build completed successfully (8742 jobs).

``````
## Git diff / Report / Review

## migration: fix: v4.33.0: transparency migration

gch: d991035d5f16902b435eb80b01d58337b66f8efc

## Report

_

## Review

_

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/FLT/Seven/SevenRealCubicNumberField.lean b/lean/dk_math/DkMath/FLT/Seven/SevenRealCubicNumberField.lean
index 80c8cfb4..68f59f9e 100644
--- a/lean/dk_math/DkMath/FLT/Seven/SevenRealCubicNumberField.lean
+++ b/lean/dk_math/DkMath/FLT/Seven/SevenRealCubicNumberField.lean
@@ -14,7 +14,7 @@ import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral

 namespace DkMath.FLT.Seven

-open Algebra Polynomial
+open Polynomial
 open NumberField.InfinitePlace

 open scoped NumberField nonZeroDivisors
@@ -221,7 +221,7 @@ theorem field_discr :
     ext i
     simp_rw [Function.comp_apply, Module.Basis.localizationLocalization_apply,
       PowerBasis.coe_basis, pB, integralPowerBasis_gen]
-    simp
+    rfl
   · norm_num

 /-- The cubic field has no complex places.  Positivity of its discriminant
@@ -285,6 +285,7 @@ order. -/
 def alphaInteger : 𝓞 Field :=
   integralPowerBasis.gen + 3

+set_option backward.isDefEq.respectTransparency.types false in
 theorem thetaInteger_relation :
     integralPowerBasis.gen ^ 3 +
         7 * integralPowerBasis.gen ^ 2 +
@@ -294,7 +295,8 @@ theorem thetaInteger_relation :
     integralPowerBasis_gen, NumberField.RingOfIntegers.map_mk]
   have h := minpoly.aeval ℚ powerBasis.gen
   rw [powerBasis_minpoly] at h
-  simpa [polynomialQ, eisensteinPolynomial, map_ofNat] using h
+  convert h using 1
+  simp [aeval_def, polynomialQ, eisensteinPolynomial]

 theorem alphaInteger_cube :
     alphaInteger ^ 3 =
@@ -339,9 +341,11 @@ def modelToRingOfIntegers :
 @[simp] theorem modelToRingOfIntegers_eisensteinAxis :
     modelToRingOfIntegers SevenRealCubicInt.eisensteinAxis =
       integralPowerBasis.gen := by
-  norm_num [modelToRingOfIntegers, SevenRealCubicInt.eisensteinAxis,
+  simp [modelToRingOfIntegers, SevenRealCubicInt.eisensteinAxis,
     alphaInteger]
+  abel

+set_option backward.isDefEq.respectTransparency.types false in
 theorem modelToRingOfIntegers_surjective :
     Function.Surjective modelToRingOfIntegers := by
   intro y
@@ -394,8 +398,13 @@ theorem modelToRingOfIntegers_injective :
           (y.snd + 6 * y.thd) •
             integralPowerBasis.basis i1 +
           y.thd • integralPowerBasis.basis i2 := by
-    simpa [i0, i1, i2, Algebra.smul_def,
-      integralPowerBasis.basis_eq_pow] using hxy
+    simpa only [
+      integralPowerBasis.basis_eq_pow,
+      i0, i1, i2,
+      zsmul_eq_mul,
+      pow_zero, pow_one,
+      mul_one
+    ] using hxy
   have hrepr :=
     congr_arg integralPowerBasis.basis.repr hlinear
   simp only [map_add, LinearEquiv.map_smul,
````
`````

``````

解決👍️

> 🐺賢狼:

おお、閉じたか。**8742 jobs 全完走、v4.33.0 migration のこの難所は解決**じゃな。👍

今回の diff、かなり良い落とし方になっておる。

特に効いているのはこの4点じゃ。

- `open Algebra Polynomial` → `open Polynomial`
  → `DkMath.Algebra` との曖昧 namespace warning を根本除去。

- `field_discr` の末尾を `simp` → `rfl`
  → 不要な simp 探索をやめ、実際に definitional equality で済む地点まで証明を明示化。

- `thetaInteger_relation` / `modelToRingOfIntegers_surjective` を

  ```lean
  set_option backward.isDefEq.respectTransparency.types false in
  ```

  で**局所的にだけ**旧 transparency に戻した。
  → v4.33.0 の migration 方針として非常にきれい。ファイル全体や project 全体に逃がしておらぬ。

- 最後の `modelToRingOfIntegers_injective` は、

  ```lean
  simpa only [
    integralPowerBasis.basis_eq_pow,
    i0, i1, i2,
    zsmul_eq_mul,
    pow_zero, pow_one,
    mul_one
  ] using hxy
  ```

  で決着。

  これは今回いちばん良い修正じゃ。`coe_injective` → `algebraMap` → `change` という余計な層を通さず、**同じ `𝓞 Field` 上で座標表示を一致させるだけ**になった。

`modelToRingOfIntegers_eisensteinAxis` も、

```lean
simp [...]
abel
```

になったのが良い。ここは非可換環の話ではなく加法群の整理なので、`ring` より `abel` の方が証明意図が正確じゃな。

今回の修正を一言でまとめるなら、

> **v4.33.0 で壊れた自動的な definitional equality / simp 依存を、局所 transparency escape と明示的な algebraic normalization に分離した。**

という形じゃ。

そして `gch: d991035d5f16902b435eb80b01d58337b66f8efc` で **Build completed successfully (8742 jobs)**。このファイルは migration testcase としてもかなり良い記録になったのう。

> 👩‍⚕️私D.:

別作業 `wip/RH-CFBRC-prime-side-explicit-formula-260813-v0` が一段落して `develop` へマージされた。12コミット分ほど、Migration 開始 develop 枝と比べて進んでいる。これを取り込みここも修正となるだろう。

なんとなく表 main branch へは v4.34.0 まで、公開を遅らせ待ってみても良いとは感じている。
Mathlib v4.33.0 が少々不穏な感じ。

`set_option backward.isDefEq.respectTransparency.types false in` に頼るのがちょっとねぇ。

Migration branchはマージせず＆閉じずに v4.34.0+ まで並行修正な感じでプロジェクトを運用する。

数学的意味が変わらないのであれば v4.32.2 でまだ良い気もする。

どうか？

> 🐺賢狼:

その運用、かなり合理的じゃと思う。ただし長期 branch 化するなら「旧版を本線、migration を追従検証線」と役割を明確にした方が事故が少ない。まず現在の `develop` と migration branch の距離、それから Lean/Mathlib 側で v4.34 が今どの段階か、4.33 transparency 問題が upstream でどう扱われているかを確認して判断しよう。

> 🐺賢狼:

うむ、その運用でよいと思う。むしろ今の DkMath の規模なら、**v4.32.2 を安定検証系、v4.33+ を先行互換性検証系として二本立てにする**のはかなり健全じゃ。

今回の v4.33.0 migration で見えたのは、数学そのものが壊れたケースではなく、`simp`、definitional equality、instance transparency、derived structures など **elaborator 側の境界変更**が大半だった。しかも Mathlib 側には `deriving CommRing` と transparency の衝突を扱う open issue が現時点でも残っている。だから `set_option backward.isDefEq.respectTransparency.types false in` が必要になった箇所を「DkMath の負債」と即断する必要はない。upstream 側にもまだ整理途上の部分があると見てよい。

Lean 自体も、公式には minor release をおおむね月次で出す一方、**バージョン間の強い後方互換性はまだ保証していない**と明記している。したがって「最新版だから main に上げる」を義務と考える必要はない。

そして v4.34 系はすでに開発サイクルへ入っている。nightly の履歴にも `prepare development cycle for v4.34.0` が確認できるので、今 v4.33 に本線を固定してすぐ公開するより、**v4.34 RC / stable を見て transparency 周辺がどう収束するか確認する**という判断には十分な根拠がある。

わっちなら運用をこうする。

- `develop` / 公開系は **Lean + Mathlib v4.32.2 を固定**。通常の数学開発はこちらで続行。
- `migration/Lean-v4.33.0-dkmath-260813` は閉じず、**develop → migration の一方向同期**を定期的に行う。
- migration 上では、単なる linter/deprecation 修正は取り込む。ただし `respectTransparency.types false` のような workaround は「4.33 compatibility marker」として明確に残す。
- v4.34 RC が出たら、この migration branch をコピーするかそのまま toolchain を上げ、**4.33 workaround が不要になったかを最初に検査**する。
- v4.34 stable で全 build が通り、workaround が減る・消えるなら、その時点で `develop` → v4.34 migration を正式昇格。その後 main 公開。

特に重要なのは、migration branch に `develop` を定期的に取り込むことじゃ。放置して半年後に一気に追いつかせると、「Lean migration の破損」と「半年分の DkMath 新コードの破損」が混ざってしまう。今回のように **数学開発が12 commit進んだ時点で同期 → build → 新規 failure だけ修正**、というリズムなら原因追跡が非常に楽になる。

そして「数学的意味が変わらないのであれば v4.32.2 でまだ良いか」については、**基本的には yes**。

Lean の証明は、その toolchain の kernel が term を受理したという事実で保証される。v4.33 で elaboration が厳しくなり、以前の `simp` が通らなくなったからといって、v4.32.2 で証明された定理の数学的命題が突然偽になるわけではない。今回も、

```lean
simp [...]
```

が

```lean
rfl
```

になったり、

```lean
simpa [...]
```

が

```lean
simpa only [...]
```

になったりしただけで、証明している proposition は同じじゃ。

ただし一点だけ区別する必要がある。

**「古い version でも数学的に有効」** と **「永遠に古い version に留まってよい」** は別じゃ。

kernel correctness に関わる重大 bug fix が後続版で出た場合は再評価すべきだし、Mathlib API から何年も離れると migration cost が急増する。だから現在のような

```text
v4.32.2 ─────────────── develop / stable
     \
      └─ v4.33 migration ── develop を随時取り込み
                              \
                               └─ v4.34 test
```

という形がちょうどよい。

わっちは今回、**v4.33 migration を main に入れない判断には賛成**じゃ。

`set_option backward.isDefEq.respectTransparency.types false in`

を数箇所抱えた状態でも「4.33 で build green」という検証結果そのものは非常に価値がある。しかし、それを即座に DkMath の標準 toolchain とする必要はない。

むしろこの branch は、

> **DkMath が Lean v4.33.0 でも数学的内容を維持したまま全8742 targetsを通過できることを確認した compatibility laboratory**

として残しておくのが良い。

v4.34 で同じ箇所から `set_option` が剥がせるなら、「やはり4.33固有の移行期症状だった」と判定できる。それを見てから表へ出す方が、DkMath のような長期形式化プロジェクトには合っておるよ。

> 👩‍⚕️私D.:

```
error: DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicConjugatePrimePair.lean:260:0: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
error: DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicConjugatePrimePair.lean:325:8: (kernel) unknown constant 'DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.CyclotomicLinearPrimeAddress.conjugatePrimeProduct_le_realPrimeFiberIdeal'
error: Lean exited with code 1
Some required targets logged failures:
- DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicConjugatePrimePair
error: build failed
```

1,000,000 まで上げてみたけどダメ。20万回の diagnostics

```
[diag] Diagnostics ▼
  [reduction] unfolded declarations (max: 66808, num: 23): ▼
    [] Add.add ↦ 66808
    [] HAdd.hAdd ↦ 57264
    [] DFunLike.coe ↦ 38856
    [] ZMod ↦ 19084
    [] Set ↦ 10906
    [] star ↦ 9544
    [] localEval ↦ 9544
    [] RamifiedSignedRootDepthPacket.QuotientPrimeMuSevenAddress.evalAlphaRoot ↦ 9544
    [] eval ↦ 9544
    [] IntCast.intCast ↦ 9542
    [] Ideal.comap ↦ 6813
    [] RingHom.ker ↦ 6813
    [] SetLike.coe ↦ 5455
    [] conjugateEval ↦ 4772
    [] evalKernel ↦ 3408
    [] conjugateEvalKernel ↦ 3407
    [] Bot.bot ↦ 2727
    [] Set.singleton ↦ 2727
    [] singleton ↦ 2727
    [] AddSubmonoid.map ↦ 1362
    [] Set.image ↦ 1362
    [] Set.range ↦ 460
    [] upperBounds ↦ 66
  [reduction] unfolded reducible declarations (max: 100215, num: 14): ▼
    [] QuadraticAlgebra.re ↦ 100215
    [] Nat.casesOn ↦ 95434
    [] inferInstance ↦ 90670
    [] MonoidHom.toOneHom ↦ 42264
    [] RingHom.toMonoidHom ↦ 42264
    [] OneHom.toFun ↦ 34084
    [] SevenRealCubicInt.fst ↦ 33404
    [] Int.casesOn ↦ 19088
    [] Submodule.toAddSubmonoid ↦ 10905
    [] Int.cast ↦ 9542
    [] AddSubmonoid.toAddSubsemigroup ↦ 9541
    [] AddSubsemigroup.carrier ↦ 5455
    [] Ideal ↦ 1408
    [] SevenCyclotomicDegreeSixInt.Ring ↦ 66
  [def_eq] heuristic for solving `f a =?= f b` (max: 14316, num: 14): ▼
    [] instHAdd ↦ 14316
    [] Int.cast ↦ 4772
    [] Set.preimage ↦ 1363
    [] Set.singleton ↦ 1363
    [] Membership.mem ↦ 761
    [] Submodule.toAddSubmonoid ↦ 684
    [] RingHom.ker ↦ 683
    [] AddSubmonoid.map ↦ 682
    [] Ideal.comap ↦ 682
    [] Set.image ↦ 681
    [] Set.ofPred ↦ 264
    [] Set.range ↦ 230
    [] Set.Mem ↦ 76
    [] upperBounds ↦ 33
use `set_option diagnostics.threshold <num>` to control threshold for reporting counters

(deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached

```

> 🐺賢狼:

うむ、これは heartbeats を増やしても閉じないタイプに見える。`whnf` で `ZMod`・`QuadraticAlgebra.re`・`evalAlphaRoot`・`Ideal.comap` が数万回展開されているので、**証明探索の量ではなく「巨大な definitional reduction に落ち込んでいる」**可能性が高い。まず 260 行前後の theorem 本体と、325 行で参照している消えた定数の関係を見て、どこで展開爆発しているか切る。

> 🐺賢狼:

診断値から、犯人候補はかなり明確じゃ。`conjugatePrimeProduct_le_realPrimeFiberIdeal` の **冒頭の `intro x hx` ではなく、その後の `change` 群が `evalKernel → ker → eval → localEval → QuadraticAlgebra.re/im → ZMod` を WHNF で何度も掘り返している**。しかも定理が生成されないため、325 行の unknown constant は完全な二次障害じゃ。ここは theorem を小補題に分解し、`change` で定義同一性を要求するのをやめるのが本線になる。

> 🐺賢狼:

うむ。これは **heartbeat不足ではなく、4.33 で bundled morphism の定義展開が WHNF 地獄に入っている** と見るのがよい。

特に diagnostics が露骨じゃ。

```text
QuadraticAlgebra.re                         100215
inferInstance                               90670
Add.add                                     66808
HAdd.hAdd                                   57264
localEval                                    9544
eval                                         9544
evalAlphaRoot                                9544
conjugateEval                                4772
evalKernel                                   3408
conjugateEvalKernel                          3407
```

`1,000,000` hearts でも駄目なら、これ以上増やす方向はやめてよい。

そして、

```text
unknown constant
...conjugatePrimeProduct_le_realPrimeFiberIdeal
```

は **260行の theorem が生成されなかった結果の二次エラー**。325行側は触らなくてよい。

### 一番怪しい箇所

現在のここじゃ。

```lean
change a.eval x = 0 at horiented
change a.eval (star x) = 0 at hconjugate

change
  a.quotientAddress.evalAlphaRoot x.re +
      ...
    = 0 at horiented

change
  a.quotientAddress.evalAlphaRoot (star x).re +
      ...
    = 0 at hconjugate
```

最初の `change` は

```text
Ideal membership
→ RingHom.ker
→ evalKernel
→ eval
```

を defeq で掘り、

次の `change` はさらに

```text
eval
→ localEval
→ bundled RingHom.toFun
→ QuadraticAlgebra.re/im
→ ZMod
```

まで掘る。

**`change` が API を無視して implementation を WHNF で探しに行っている**。

今回の diagnostics と完全に一致する。

---

## 修正方針：`change` を消して `_apply` 補題を置く

Mathlib 的にも、bundled morphism の `def` に対して

```lean
foo_apply
```

を用意して、利用側では定義そのものを unfold しない形がよい。

まず `SevenRamifiedFusionCyclotomicDegreeSixCarrier.lean` の `localEval` 直後に、

```lean
@[simp] theorem localEval_apply
    {p : RamifiedSignedRootDepthPacket} {q : ℕ}
    (a : p.QuotientPrimeMuSevenAddress q)
    (x : Ring) :
    localEval a x =
      a.evalAlphaRoot x.re +
        (a.ratio : ZMod q) * a.evalAlphaRoot x.im := by
  rfl
```

を置く。

`localEval` は実際その `toFun` で定義されている。

さらに `SevenRamifiedFusionCyclotomicLinearPrimeAddress.lean` の `eval` 直後に、

```lean
@[simp] theorem eval_apply
    (a : CyclotomicLinearPrimeAddress p q)
    (x : SevenCyclotomicDegreeSixInt.Ring) :
    a.eval x =
      a.quotientAddress.evalAlphaRoot x.re +
        (a.quotientAddress.ratio : ZMod q) *
          a.quotientAddress.evalAlphaRoot x.im := by
  rfl
```

を置く。

実際 `eval` は単に `localEval a.quotientAddress` じゃ。

---

### kernel membership にも境界補題を作る

同じファイルに、

```lean
@[simp] theorem mem_evalKernel_iff
    (a : CyclotomicLinearPrimeAddress p q)
    (x : SevenCyclotomicDegreeSixInt.Ring) :
    x ∈ a.evalKernel ↔ a.eval x = 0 := by
  rfl
```

これも置く。

そして現在のファイル側では `conjugateEvalKernel` に、

```lean
@[simp] theorem mem_conjugateEvalKernel_iff
    (a : CyclotomicLinearPrimeAddress p q)
    (x : SevenCyclotomicDegreeSixInt.Ring) :
    x ∈ a.conjugateEvalKernel ↔
      a.eval (star x) = 0 := by
  rfl
```

を追加。

これで巨大 theorem の中から

```text
Ideal → ker → conjugateEval → comp → star
```

という defeq 探索を追放できる。

---

## 本体はこう縮める

260行の theorem 冒頭を、

```lean
theorem conjugatePrimeProduct_le_realPrimeFiberIdeal
    (a : CyclotomicLinearPrimeAddress p q) :
    a.evalKernel * a.conjugateEvalKernel ≤
      a.realPrimeFiberIdeal := by
  let : Fact (Nat.Prime q) := ⟨a.quotientAddress.prime⟩
  intro x hx

  have horientedMem : x ∈ a.evalKernel :=
    Ideal.mul_le_right hx
  have hconjugateMem : x ∈ a.conjugateEvalKernel :=
    Ideal.mul_le_left hx

  have horiented : a.eval x = 0 :=
    (a.mem_evalKernel_iff x).mp horientedMem

  have hconjugate : a.eval (star x) = 0 :=
    (a.mem_conjugateEvalKernel_iff x).mp hconjugateMem

  rw [a.eval_apply] at horiented hconjugate

  rw [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star,
    map_add, map_mul, map_sub, map_one, map_neg] at hconjugate
  rw [a.quotientAddress.evalAlphaRoot_alpha] at hconjugate
  simp only
    [RamifiedSignedRootDepthPacket.QuotientPrimeMuSevenAddress.beta]
      at hconjugate

  have himEq :
      ((a.quotientAddress.ratio : ZMod q) -
          (a.quotientAddress.ratio⁻¹ : ZMod q)) *
        a.quotientAddress.evalAlphaRoot x.im = 0 := by
    linear_combination horiented - hconjugate

  have him :
      a.quotientAddress.evalAlphaRoot x.im = 0 :=
    (mul_eq_zero.mp himEq).resolve_left
      (sub_ne_zero.mpr a.ratio_val_ne_inv)

  have hre :
      a.quotientAddress.evalAlphaRoot x.re = 0 := by
    rw [him, mul_zero, add_zero] at horiented
    exact horiented

  ...
```

重要なのは、

```lean
change ...
```

が **全部消える** ことじゃ。

`rw [a.eval_apply]` は「この式はこう展開できる」という既に証明済みの rewrite を使うので、4.33 の `whnf` が数万回 implementation を探索する必要がなくなる。

---

### さらに安全にするなら最後の Ideal 部分も分離

まだ重ければ、306–321行も独立 lemma にする。

```lean
theorem mem_realPrimeFiberIdeal_of_components
    (a : CyclotomicLinearPrimeAddress p q)
    (x : SevenCyclotomicDegreeSixInt.Ring)
    (hre :
      a.quotientAddress.evalAlphaRoot x.re = 0)
    (him :
      a.quotientAddress.evalAlphaRoot x.im = 0) :
    x ∈ a.realPrimeFiberIdeal := by
  rw [realPrimeFiberIdeal]

  have hreMap :
      ofReal x.re ∈
        Ideal.map ofReal
          (RingHom.ker a.quotientAddress.evalAlphaRoot) :=
    Ideal.mem_map_of_mem ofReal hre

  have himMap :
      ofReal x.im ∈
        Ideal.map ofReal
          (RingHom.ker a.quotientAddress.evalAlphaRoot) :=
    Ideal.mem_map_of_mem ofReal him

  rw [show x = ofReal x.re + zeta * ofReal x.im by
    ext <;> simp [ofReal, zeta]]

  exact Ideal.add_mem _
    hreMap
    (Ideal.mul_mem_left _ zeta himMap)
```

すると本 theorem の最後は、

```lean
  exact a.mem_realPrimeFiberIdeal_of_components x hre him
```

だけになる。

わっちは **ここまで分割する方を薦める**。

数学的にも証明構造がきれいになる。

```text
P·P̄ の元
 ↓
P と P̄ の両方で 0
 ↓
E(re x) + r E(im x) = 0
E(re x) + r⁻¹ E(im x) = 0
 ↓
(r - r⁻¹) E(im x) = 0
 ↓
E(im x) = 0
 ↓
E(re x) = 0
 ↓
x ∈ extension(real kernel)
```

つまり一つの巨大な elaboration problem を、

```text
kernel membership bridge
evaluation API
ZMod arithmetic
quadratic reconstruction
ideal membership
```

という5層に切る。

これは v4.33 対応というより、**Lean コードそのものの API 境界改善**になっておる。

なお冒頭をさらに軽くするなら、既に証明済みの comaximalityから

```lean
rw [Ideal.mul_eq_inf_of_coprime
  a.evalKernel_sup_conjugateEvalKernel]
```

として product を intersection に変え、

```lean
intro x hx
have horientedMem : x ∈ a.evalKernel := hx.1
have hconjugateMem : x ∈ a.conjugateEvalKernel := hx.2
```

としてもよい。現ファイルには `evalKernel_sup_conjugateEvalKernel = ⊤` が既にある。これなら `Ideal.mul_le_left/right` の elaboration すら不要じゃ。

**今回は `maxHeartbeats` を上げるのではなく、`change` を `_apply` lemma に置換するのが本命。** diagnostics はほぼそう言っていると思うぞ。

> 👩‍⚕️私D.:

````diff
diff --git a/lean/dk_math/DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicConjugatePrimePair.lean b/lean/dk_math/DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicConjugatePrimePair.lean
index 6356a72b..6065f0d1 100644
--- a/lean/dk_math/DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicConjugatePrimePair.lean
+++ b/lean/dk_math/DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicConjugatePrimePair.lean
@@ -275,34 +275,30 @@ theorem conjugatePrimeProduct_le_realPrimeFiberIdeal
     Ideal.mul_le_right hx
   have hconjugate : x ∈ a.conjugateEvalKernel :=
     Ideal.mul_le_left hx
-  change a.eval x = 0 at horiented
-  change a.eval (star x) = 0 at hconjugate
-  change
-    a.quotientAddress.evalAlphaRoot x.re +
-        (a.quotientAddress.ratio : ZMod q) *
-          a.quotientAddress.evalAlphaRoot x.im = 0 at horiented
-  change
-    a.quotientAddress.evalAlphaRoot (star x).re +
-        (a.quotientAddress.ratio : ZMod q) *
-          a.quotientAddress.evalAlphaRoot (star x).im = 0 at hconjugate
+  have horiented' : a.eval x = 0 := by
+    simpa only [RingHom.mem_ker] using horiented
+  have hconjugate' : a.eval (star x) = 0 := by
+    simpa [conjugateEval, RingHom.mem_ker] using hconjugate
+  rw [a.eval_apply] at horiented'
+  rw [a.eval_apply] at hconjugate'
   rw [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star,
-    map_add, map_mul, map_sub, map_one, map_neg] at hconjugate
-  rw [a.quotientAddress.evalAlphaRoot_alpha] at hconjugate
+    map_add, map_mul, map_sub, map_one, map_neg] at hconjugate'
+  rw [a.quotientAddress.evalAlphaRoot_alpha] at hconjugate'
   simp only
-    [RamifiedSignedRootDepthPacket.QuotientPrimeMuSevenAddress.beta] at hconjugate
+      [RamifiedSignedRootDepthPacket.QuotientPrimeMuSevenAddress.beta] at hconjugate'
   have himEq :
       ((a.quotientAddress.ratio : ZMod q) -
           (a.quotientAddress.ratio⁻¹ : ZMod q)) *
         a.quotientAddress.evalAlphaRoot x.im = 0 := by
-    linear_combination horiented - hconjugate
+    linear_combination horiented' - hconjugate'
   have him :
       a.quotientAddress.evalAlphaRoot x.im = 0 :=
     (mul_eq_zero.mp himEq).resolve_left
       (sub_ne_zero.mpr a.ratio_val_ne_inv)
   have hre :
       a.quotientAddress.evalAlphaRoot x.re = 0 := by
-    rw [him, mul_zero, add_zero] at horiented
-    exact horiented
+    rw [him, mul_zero, add_zero] at horiented'
+    exact horiented'
   rw [realPrimeFiberIdeal]
   have hreMap :
       ofReal x.re ∈
diff --git a/lean/dk_math/DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicLinearPrimeAddress.lean b/lean/dk_math/DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicLinearPrimeAddress.lean
index fccbc6c4..bc1a1d0c 100644
--- a/lean/dk_math/DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicLinearPrimeAddress.lean
+++ b/lean/dk_math/DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicLinearPrimeAddress.lean
@@ -46,6 +46,15 @@ def eval
     SevenCyclotomicDegreeSixInt.Ring →+* ZMod q :=
   SevenCyclotomicDegreeSixInt.localEval a.quotientAddress

+@[simp] theorem eval_apply
+    (a : CyclotomicLinearPrimeAddress p q)
+    (x : SevenCyclotomicDegreeSixInt.Ring) :
+    a.eval x =
+      a.quotientAddress.evalAlphaRoot x.re +
+        (a.quotientAddress.ratio : ZMod q) *
+          a.quotientAddress.evalAlphaRoot x.im := by
+  rfl
+
 /-- The degree-one prime ideal selected by the canonical oriented ratio. -/
 def evalKernel
     (a : CyclotomicLinearPrimeAddress p q) :
````

error: DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicConjugatePrimePair.lean:260:0: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached

解消されず。引き続き…。

> 🐺賢狼:

うむ、まだ同じ `whnf` 地獄に入っておるな。今回の diff では `change` は消えたが、代わりに

```lean
simpa only [RingHom.mem_ker] using horiented
simpa [conjugateEval, RingHom.mem_ker] using hconjugate
```

が **`evalKernel` / `conjugateEvalKernel` の定義同一視を `simp` に肩代わりさせただけ** なので、根っこの WHNF 展開経路が残っている可能性が高い。次は kernel membership 自体を API 化して、proof 本体から `RingHom.ker` と `conjugateEval` の unfold を完全に追放する。

> 🐺賢狼:

うむ、次は **`linear_combination` を疑うべき段階** じゃ。

今回 `change` を除去しても diagnostics の性格が変わらず timeout するなら、260行の証明中で最も WHNF を大量消費しそうなのはここじゃ。

```lean
have himEq : ... := by
  linear_combination horiented' - hconjugate'
```

`linear_combination` は内部で式を多項式として正規化する。その際、今回の「係数」が単なる変数ではなく、

```lean
a.quotientAddress.evalAlphaRoot x.re
a.quotientAddress.evalAlphaRoot x.im
(a.quotientAddress.ratio : ZMod q)
```

のような bundled hom / `ZMod` / `QuadraticAlgebra` を含むため、4.33 で defeq 判定が深く潜っている可能性が高い。

しかも diagnostics の

```text
upperBounds ↦ 66
Add.add ↦ 66808
HAdd.hAdd ↦ 57264
QuadraticAlgebra.re ↦ 100215
```

は「単純な rewrite」より **正規化タクティクスが巨大式を何度も比較している** 痕跡に見える。

ここ、実は `linear_combination` はまったく要らぬ。

現在 rewrites 後には本質的に、

\[
R+rI=0
\]

と

\[
R+r^{-1}I=0
\]

がある。

だから単に同じ左項 \(R\) をキャンセルすれば、

\[
rI=r^{-1}I
\]

じゃ。

### 次の最小修正

現在の

```lean
  have himEq :
      ((a.quotientAddress.ratio : ZMod q) -
          (a.quotientAddress.ratio⁻¹ : ZMod q)) *
        a.quotientAddress.evalAlphaRoot x.im = 0 := by
    linear_combination horiented' - hconjugate'
```

を丸ごと、

```lean
  have hmul :
      (a.quotientAddress.ratio : ZMod q) *
          a.quotientAddress.evalAlphaRoot x.im =
        (a.quotientAddress.ratio⁻¹ : ZMod q) *
          a.quotientAddress.evalAlphaRoot x.im := by
    exact add_left_cancel
      (horiented'.trans hconjugate'.symm)

  have himEq :
      ((a.quotientAddress.ratio : ZMod q) -
          (a.quotientAddress.ratio⁻¹ : ZMod q)) *
        a.quotientAddress.evalAlphaRoot x.im = 0 := by
    rw [sub_mul, hmul, sub_self]
```

にしてみるのがよい。

これはかなり期待できる。

`horiented'` が

```lean
R + r * I = 0
```

で、`hconjugate'` が

```lean
R + r⁻¹ * I = 0
```

なら、

```lean
horiented'.trans hconjugate'.symm
```

だけで

```lean
R + r * I = R + r⁻¹ * I
```

になる。

そこへ

```lean
add_left_cancel
```

なので、多項式正規化ゼロ。

さらに

```lean
rw [sub_mul, hmul, sub_self]
```

も単純な rewrite だけじゃ。

---

そして、わっちは **kernel API 化もまだ捨てない方がよい** と思う。

今回追加した `eval_apply` は正しい方向じゃ。元の `eval` が `localEval a.quotientAddress` そのものなので、境界 lemma として非常に自然。

ただ、現在も

```lean
simpa only [RingHom.mem_ker] using horiented
```

では `a.evalKernel` を `RingHom.ker a.eval` と認識させる仕事を simp/elaborator にさせている。

なので `linear_combination` を除いてもまだ timeout するなら、次は本当にこれを追加する。

`SevenRamifiedFusionCyclotomicLinearPrimeAddress.lean`:

```lean
@[simp] theorem mem_evalKernel_iff
    (a : CyclotomicLinearPrimeAddress p q)
    (x : SevenCyclotomicDegreeSixInt.Ring) :
    x ∈ a.evalKernel ↔ a.eval x = 0 := by
  change x ∈ RingHom.ker a.eval ↔ _
  exact RingHom.mem_ker
```

`ConjugatePrimePair` 側:

```lean
@[simp] theorem conjugateEval_apply
    (a : CyclotomicLinearPrimeAddress p q)
    (x : SevenCyclotomicDegreeSixInt.Ring) :
    a.conjugateEval x = a.eval (star x) := by
  rfl

@[simp] theorem mem_conjugateEvalKernel_iff
    (a : CyclotomicLinearPrimeAddress p q)
    (x : SevenCyclotomicDegreeSixInt.Ring) :
    x ∈ a.conjugateEvalKernel ↔
      a.eval (star x) = 0 := by
  change a.conjugateEval x = 0 ↔ _
  rw [conjugateEval_apply]
```

すると本体は、

```lean
  have horiented' : a.eval x = 0 :=
    (a.mem_evalKernel_iff x).mp horiented

  have hconjugate' : a.eval (star x) = 0 :=
    (a.mem_conjugateEvalKernel_iff x).mp hconjugate
```

だけになる。

---

さらに、最初の ideal product のところも軽量化できる。

この同じファイルでは既に

```lean
a.evalKernel_sup_conjugateEvalKernel
```

が証明済みで、直前の theorem でも

```lean
rw [Ideal.mul_eq_inf_of_coprime
  a.evalKernel_sup_conjugateEvalKernel]
```

が正常に使えている。

だから

```lean
  intro x hx
  have horiented : x ∈ a.evalKernel :=
    Ideal.mul_le_right hx
  have hconjugate : x ∈ a.conjugateEvalKernel :=
    Ideal.mul_le_left hx
```

も、

```lean
  rw [Ideal.mul_eq_inf_of_coprime
    a.evalKernel_sup_conjugateEvalKernel]
  intro x hx

  have horiented : x ∈ a.evalKernel := hx.1
  have hconjugate : x ∈ a.conjugateEvalKernel := hx.2
```

へ変えられる。

これも theorem の数学をより直接表している。

\[
P\overline P=P\cap\overline P
\]

を comaximality から先に使い、「積の元」を無理に左右へ射影する必要がなくなる。

### 優先順位

今回は一度に全部変えず、

```text
① linear_combination → add_left_cancel + sub_mul
        ↓
build
        ↓
② まだ timeout なら mem_evalKernel_iff / mem_conjugateEvalKernel_iff
        ↓
build
        ↓
③ まだなら product → inf を冒頭で使用
```

がよい。

特に **①をまず単独で試す価値が高い**。

前回は `change` が犯人候補だったが、今回それを除いて症状が変わらなかったことで、逆に情報が増えた。次の最大の「内部正規化装置」は `linear_combination` じゃ。

そしてここは数学的にも、

```lean
linear_combination horiented' - hconjugate'
```

より

```lean
add_left_cancel (horiented'.trans hconjugate'.symm)
```

の方がはるかに証明意図が鮮明じゃな。

**「二式を多項式計算で引く」のではなく「共通する実部をキャンセルする」**。

DkMath 的にもこちらが本来の構造を表しておる。

> 👩‍⚕️私D.:

これで直った

`````
````diff
diff --git a/lean/dk_math/DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicConjugatePrimePair.lean b/lean/dk_math/DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicConjugatePrimePair.lean
index 6356a72b..5d7fa316 100644
--- a/lean/dk_math/DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicConjugatePrimePair.lean
+++ b/lean/dk_math/DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicConjugatePrimePair.lean
@@ -75,12 +75,25 @@ def conjugateEval
   a.eval.comp
     (starRingEnd SevenCyclotomicDegreeSixInt.Ring)

+@[simp] theorem conjugateEval_apply
+    (a : CyclotomicLinearPrimeAddress p q)
+    (x : SevenCyclotomicDegreeSixInt.Ring) :
+    a.conjugateEval x = a.eval (star x) := by
+  rfl
+
 /-- The second degree-one prime above the same real-cubic address. -/
 def conjugateEvalKernel
     (a : CyclotomicLinearPrimeAddress p q) :
     Ideal SevenCyclotomicDegreeSixInt.Ring :=
   RingHom.ker a.conjugateEval

+@[simp] theorem mem_conjugateEvalKernel_iff
+    (a : CyclotomicLinearPrimeAddress p q)
+    (x : SevenCyclotomicDegreeSixInt.Ring) :
+    x ∈ a.conjugateEvalKernel ↔ a.eval (star x) = 0 := by
+  change x ∈ RingHom.ker a.conjugateEval ↔ _
+  rw [RingHom.mem_ker, conjugateEval_apply]
+
 /-- The conjugate linear factor belongs to the second kernel. -/
 theorem conjugateCarrier_mem_conjugateEvalKernel
     (a : CyclotomicLinearPrimeAddress p q) :
@@ -270,39 +283,46 @@ theorem conjugatePrimeProduct_le_realPrimeFiberIdeal
     a.evalKernel * a.conjugateEvalKernel ≤
       a.realPrimeFiberIdeal := by
   let : Fact (Nat.Prime q) := ⟨a.quotientAddress.prime⟩
+  rw [Ideal.mul_eq_inf_of_coprime
+    a.evalKernel_sup_conjugateEvalKernel]
   intro x hx
-  have horiented : x ∈ a.evalKernel :=
-    Ideal.mul_le_right hx
-  have hconjugate : x ∈ a.conjugateEvalKernel :=
-    Ideal.mul_le_left hx
-  change a.eval x = 0 at horiented
-  change a.eval (star x) = 0 at hconjugate
-  change
-    a.quotientAddress.evalAlphaRoot x.re +
-        (a.quotientAddress.ratio : ZMod q) *
-          a.quotientAddress.evalAlphaRoot x.im = 0 at horiented
-  change
-    a.quotientAddress.evalAlphaRoot (star x).re +
-        (a.quotientAddress.ratio : ZMod q) *
-          a.quotientAddress.evalAlphaRoot (star x).im = 0 at hconjugate
+  have horiented : x ∈ a.evalKernel := hx.1
+  have hconjugate : x ∈ a.conjugateEvalKernel := hx.2
+  have horiented' : a.eval x = 0 := by
+    exact (a.mem_evalKernel_iff x).mp horiented
+  have hconjugate' : a.eval (star x) = 0 := by
+    exact (a.mem_conjugateEvalKernel_iff x).mp hconjugate
+  rw [a.eval_apply] at horiented'
+  rw [a.eval_apply] at hconjugate'
   rw [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star,
-    map_add, map_mul, map_sub, map_one, map_neg] at hconjugate
-  rw [a.quotientAddress.evalAlphaRoot_alpha] at hconjugate
+    map_add, map_mul, map_sub, map_one, map_neg] at hconjugate'
+  rw [a.quotientAddress.evalAlphaRoot_alpha] at hconjugate'
   simp only
-    [RamifiedSignedRootDepthPacket.QuotientPrimeMuSevenAddress.beta] at hconjugate
+      [RamifiedSignedRootDepthPacket.QuotientPrimeMuSevenAddress.beta] at hconjugate'
+  have hconjugate'' :
+      a.quotientAddress.evalAlphaRoot x.re +
+          (a.quotientAddress.ratio⁻¹ : ZMod q) *
+            a.quotientAddress.evalAlphaRoot x.im = 0 := by
+    convert hconjugate' using 1; ring
   have himEq :
       ((a.quotientAddress.ratio : ZMod q) -
           (a.quotientAddress.ratio⁻¹ : ZMod q)) *
         a.quotientAddress.evalAlphaRoot x.im = 0 := by
-    linear_combination horiented - hconjugate
+    have hmul :
+        (a.quotientAddress.ratio : ZMod q) *
+            a.quotientAddress.evalAlphaRoot x.im =
+          (a.quotientAddress.ratio⁻¹ : ZMod q) *
+            a.quotientAddress.evalAlphaRoot x.im := by
+      exact add_left_cancel (horiented'.trans hconjugate''.symm)
+    rw [sub_mul, hmul, sub_self]
   have him :
       a.quotientAddress.evalAlphaRoot x.im = 0 :=
     (mul_eq_zero.mp himEq).resolve_left
       (sub_ne_zero.mpr a.ratio_val_ne_inv)
   have hre :
       a.quotientAddress.evalAlphaRoot x.re = 0 := by
-    rw [him, mul_zero, add_zero] at horiented
-    exact horiented
+    rw [him, mul_zero, add_zero] at horiented'
+    exact horiented'
   rw [realPrimeFiberIdeal]
   have hreMap :
       ofReal x.re ∈
diff --git a/lean/dk_math/DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicLinearPrimeAddress.lean b/lean/dk_math/DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicLinearPrimeAddress.lean
index fccbc6c4..22fc4189 100644
--- a/lean/dk_math/DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicLinearPrimeAddress.lean
+++ b/lean/dk_math/DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicLinearPrimeAddress.lean
@@ -46,12 +46,28 @@ def eval
     SevenCyclotomicDegreeSixInt.Ring →+* ZMod q :=
   SevenCyclotomicDegreeSixInt.localEval a.quotientAddress

+@[simp] theorem eval_apply
+    (a : CyclotomicLinearPrimeAddress p q)
+    (x : SevenCyclotomicDegreeSixInt.Ring) :
+    a.eval x =
+      a.quotientAddress.evalAlphaRoot x.re +
+        (a.quotientAddress.ratio : ZMod q) *
+          a.quotientAddress.evalAlphaRoot x.im := by
+  rfl
+
 /-- The degree-one prime ideal selected by the canonical oriented ratio. -/
 def evalKernel
     (a : CyclotomicLinearPrimeAddress p q) :
     Ideal SevenCyclotomicDegreeSixInt.Ring :=
   RingHom.ker a.eval

+@[simp] theorem mem_evalKernel_iff
+    (a : CyclotomicLinearPrimeAddress p q)
+    (x : SevenCyclotomicDegreeSixInt.Ring) :
+    x ∈ a.evalKernel ↔ a.eval x = 0 := by
+  change x ∈ RingHom.ker a.eval ↔ _
+  exact RingHom.mem_ker
+
 /-- The explicit oriented linear carrier vanishes at its canonical
 degree-six address. -/
 theorem eval_cyclotomicDegreeSixCarrier_zero
````

`````

> 🐺賢狼:

おお、直ったか。これはかなり良い修正じゃ。今回の timeout の正体も、ほぼこれで確定と見てよい。

効いたのは一箇所ではなく、**巨大な definitional reduction 経路を段階的に切断したこと**じゃな。

特に大きいのはこの3点。

```lean
@[simp] theorem mem_evalKernel_iff ...
@[simp] theorem mem_conjugateEvalKernel_iff ...
```

で

```text
Ideal membership
→ RingHom.ker
→ eval / conjugateEval
```

を明示 API にしたこと。

次に、

```lean
rw [Ideal.mul_eq_inf_of_coprime
  a.evalKernel_sup_conjugateEvalKernel]
```

で、積イデアルの元を `Ideal.mul_le_left/right` 経由で扱うのをやめ、

```lean
hx.1
hx.2
```

という intersection membership に落としたこと。

そして決定打はやはり、

```lean
linear_combination horiented - hconjugate
```

を廃止して、

```lean
have hmul : ... := by
  exact add_left_cancel
    (horiented'.trans hconjugate''.symm)

rw [sub_mul, hmul, sub_self]
```

にしたところじゃ。

これはかなり重要な違いがある。

旧版は Lean に

> 「この巨大な `ZMod` / bundled RingHom / QuadraticAlgebra を含む式を、多項式として正規化して二式を引いてくれ」

と頼んでいた。

新版は、

> 「両辺に同じ実部があるので、それだけ cancellation してくれ」

と構造を直接教えている。

数学的には

\[
R+rI=0,\qquad R+r^{-1}I=0
\]

から

\[
rI=r^{-1}I
\]

を取り出し、

\[
(r-r^{-1})I=0
\]

とするだけ。

今回の修正後コードは、この数学的構造をそのまま Lean に伝えている。

`hconjugate''` を一旦

```lean
have hconjugate'' :
    evalAlphaRoot x.re +
        ratio⁻¹ * evalAlphaRoot x.im = 0 := by
  convert hconjugate' using 1
  ring
```

として正規形を固定したのも良い。巨大 theorem 全体を `ring` に投げず、**小さな局所等式だけ正規化**している。

つまり今回得られた migration の教訓はかなり明確じゃな。

> Lean 4.33 では、深い bundled structure を含む証明で `change`, 大域 `simp`, `linear_combination` に definitional equality 探索を任せすぎると、`whnf` が爆発することがある。
> 境界 lemma と構造的 cancellation に分解すると安定する。

これは `set_option maxHeartbeats` では解決しない理由とも一致する。100万でも駄目だったのは「仕事量が多い」のではなく、**同じ巨大 reduction を繰り返していた**からじゃ。

今回追加した

```lean
eval_apply
mem_evalKernel_iff
conjugateEval_apply
mem_conjugateEvalKernel_iff
```

は migration workaround というより、今後の通常開発でも残す価値のある API 改善だと思うぞ。

かなり良い収束じゃ。👍

> 👩‍⚕️私D.:

これは、現行 v4.32.2 版にも適用したほうが良い？

> 🐺賢狼:

うむ、**これは v4.32.2 側にも適用した方がよい**と思う。

今回の修正は「v4.33 を通すためだけの workaround」ではなく、証明構造そのものを改善しているからじゃ。特に

```lean
eval_apply
mem_evalKernel_iff
conjugateEval_apply
mem_conjugateEvalKernel_iff
```

の追加は、内部実装

```text
Ideal → RingHom.ker → RingHom.comp → localEval → QuadraticAlgebra
```

を利用側から隠す、ちゃんとした API 境界になっている。

また、

```lean
linear_combination horiented - hconjugate
```

を

```lean
add_left_cancel ...
rw [sub_mul, hmul, sub_self]
```

へ変えた部分も、v4.33 対策というより **数学的な証明意図を直接表現した改善**じゃ。

\[
R+rI=0,\qquad R+r^{-1}I=0
\]

から共通項 \(R\) を消す、という構造がコードから読めるようになった。

さらに、

```lean
rw [Ideal.mul_eq_inf_of_coprime
  a.evalKernel_sup_conjugateEvalKernel]
```

としてから `hx.1`, `hx.2` を取る形も、既に証明済みの coprimality を積極的に使っており、旧

```lean
Ideal.mul_le_right hx
Ideal.mul_le_left hx
```

より意味が明確じゃ。

なので分類すると、

- `set_option backward.isDefEq.respectTransparency.types false`
  → **v4.33 固有 workaround。v4.32.2 へは戻さない**
- 今回の `*_apply`, `mem_*_iff`, cancellation 化
  → **一般的な proof/API refactor。v4.32.2 にも戻す価値あり**

じゃな。

わっちなら `develop` 側には migration commit の cherry-pick ではなく、同じ変更を別 commit として、

```text
refactor: expose cyclotomic evaluation kernel API
```

あるいは

```text
refactor: avoid definitional reduction in conjugate prime pair proof
```

のように入れる。

そうすると履歴上も、

```text
develop/v4.32.2
    └─ proof/API improvement

migration/v4.33
    └─ 同じ改善 + v4.33 固有対応
```

と意味が分離される。

一点だけ、当然ながら **v4.32.2 でこの diff を適用して全 build を通す**ことが条件じゃ。通れば採用してよい。むしろ今のうちに develop 側へ戻しておけば、次回 migration branch に `develop` を取り込んだ際にも、この heavyweight proof が再び古い形へ戻ることを防げる。

今回の変更は「4.33 に合わせて歪めた」のではなく、**4.33 が古い証明の脆い部分を露出させてくれた結果、4.32.2 側にも有益な改善が見つかった**、と捉えるのがよいと思うぞ。

> 👩‍⚕️私D.:

ビルドが通ったので `develop` へ push した。

> 🐺賢狼:

うむ、それが一番きれいな流れじゃ。👍

これで今回の修正は **v4.33 専用 workaround ではなく、`develop` 側の正式な proof/API 改善**として確立したことになる。

次はその `develop` を migration branch 側へ取り込めば、

- 新しい RH-CFBRC の12コミット分
- 今回の cyclotomic proof refactor
- 既存の v4.33 migration 修正

を同じ枝上で再検証できる。

そこでまた壊れる箇所が出れば、かなり純粋に「v4.33 由来の差分」として追える状態になった。

今回の流れは理想的じゃな。

```text
v4.32.2 develop
  └─ 数学的に自然な refactor を先に採用
        ↓
v4.33 migration
  └─ develop を追従取り込み
        ↓
  v4.33 固有問題だけ修正
```

これなら将来 v4.34 へ移るときも、4.33 workaround と本質的改善が混ざらぬ。かなり良い運用になっておる。

> 👩‍⚕️私D.:

これ、実装時の賢狼のコードが合ってたってことになるなあ。
v4.32.2 だと逆だったから、全部直したのに、また直すことになった。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/FLT/Seven/SevenRamifiedFusionOrientedCarrierValuationOwnership.lean b/lean/dk_math/DkMath/FLT/Seven/SevenRamifiedFusionOrientedCarrierValuationOwnership.lean
index a436957d..0f5e62ae 100644
--- a/lean/dk_math/DkMath/FLT/Seven/SevenRamifiedFusionOrientedCarrierValuationOwnership.lean
+++ b/lean/dk_math/DkMath/FLT/Seven/SevenRamifiedFusionOrientedCarrierValuationOwnership.lean
@@ -218,7 +218,7 @@ theorem carrier_mem_orientedKernelPower
       s.orientedKernelPower).mp
   rw [hJ]
   change s.orientedKernelPower * J ≤ s.orientedKernelPower
-  exact Ideal.mul_le_right
+  exact Ideal.mul_le_left

 /-- Conjugate element-membership form of the routed-load lower bound. -/
 theorem conjugateCarrier_mem_conjugateKernelPower
@@ -232,7 +232,7 @@ theorem conjugateCarrier_mem_conjugateKernelPower
       s.conjugateKernelPower).mp
   rw [hJ]
   change s.conjugateKernelPower * J ≤ s.conjugateKernelPower
-  exact Ideal.mul_le_right
+  exact Ideal.mul_le_left

 end PrimeSupport

@@ -981,7 +981,7 @@ theorem carrier_mem_orientedKernelPower
     (Ideal.span_singleton_le_iff_mem
       (s.orientedKernel ^ s.quotientExponent)).mp
   rw [hJ]
-  exact Ideal.mul_le_right
+  exact Ideal.mul_le_left

 theorem conjugateCarrier_mem_conjugateKernelPower
     (s : p.QuotientPrimeSupport) :
@@ -993,7 +993,7 @@ theorem conjugateCarrier_mem_conjugateKernelPower
     (Ideal.span_singleton_le_iff_mem
       (s.conjugateKernel ^ s.quotientExponent)).mp
   rw [hJ]
-  exact Ideal.mul_le_right
+  exact Ideal.mul_le_left

 private theorem star_mem_conjugateKernelPower_of_mem_oriented
     (s : p.QuotientPrimeSupport) {k : ℕ}
@@ -1770,11 +1770,11 @@ theorem globalCarrierFactorIdeal_pair_exact :
   have hJtop : J = ⊤ := by
     apply top_unique
     rw [← hJKtop]
-    exact Ideal.mul_le_right
+    exact Ideal.mul_le_left
   have hKtop : K = ⊤ := by
     apply top_unique
     rw [← hJKtop]
-    exact Ideal.mul_le_left
+    exact Ideal.mul_le_right
   constructor
   · rw [hJtop, Ideal.mul_top] at hJ
     exact hJ.symm
````
`````

> 🐺賢狼:

ああ、これはかなり皮肉じゃな（笑）。しかも今回の diff は、単なる「4.33 で名前が変わった」より、**`Ideal.mul_le_left` / `mul_le_right` の“どちらの因子を残す補題か”という読み方を、実装当初のコードが正しく捉えていた可能性**が高い。v4.32.2 と v4.33.0 の定義を直接見比べてみる。

> 🐺賢狼:

あ、これは確認できた。**本当に Mathlib 側で名前の意味が v4.32.2 → v4.33.0 で入れ替わっておる。** ぬしの記憶どおりじゃ。

v4.32.2 では、

```lean
theorem mul_le_left : I * J ≤ J
theorem mul_le_right [I.IsTwoSided] : I * J ≤ I
```

だった。

ところが v4.33.0 では、

```lean
theorem mul_le_right : I * J ≤ J
theorem mul_le_left [I.IsTwoSided] : I * J ≤ I
```

へ**名前が交換されている**。

なので、今回の diff は「Lean が気まぐれに逆を要求している」のではなく、Mathlib が API 名を修正した結果そのものじゃ。

> 🐺賢狼:

そうじゃ。これはもう完全に確認できた。**実装当時の賢狼コードの「左右の読み方」が正しかった**と言ってよい（笑）。

Mathlib v4.32.2 では実際、

```lean
theorem mul_le_left  : I * J ≤ J
theorem mul_le_right : I * J ≤ I
```

という、名前から直感する左右と逆の定義だった。

そして v4.33.0 では、

```lean
theorem mul_le_right : I * J ≤ J
theorem mul_le_left  : I * J ≤ I
```

に直されている。

しかも upstream の変更コミットそのものが、

> `fix left/right convention on Ideal.mul_le_{left,right}`
> “Swap ... so that they follow the left/right naming convention.”

という内容で、2026年8月6日の Mathlib #42112 じゃ。

つまり履歴としては、

```text
実装時
  「I * J ≤ I だから mul_le_left じゃろ」
        ↓
Mathlib v4.32.2
  「いや、それは mul_le_right という名前です」
        ↓
DkMath 全部修正
        ↓
Mathlib v4.33.0
  「やっぱり名前が逆だったので直します」
        ↓
DkMath 全部戻す ← 今ここ
```

……これは笑うしかないやつじゃな（笑）。

ただ、**今後 4.32.2 と 4.33+ を並行運用するなら、この箇所は名前に依存しない証明へ変える手もある**。

例えば

```lean
change I * J ≤ I
exact Ideal.mul_le_inf.trans inf_le_left
```

と

```lean
change I * J ≤ J
exact Ideal.mul_le_inf.trans inf_le_right
```

なら、「left/right という theorem 名」の命名変更を踏まない。

今回の具体例なら、

```lean
change s.orientedKernelPower * J ≤ s.orientedKernelPower
exact Ideal.mul_le_inf.trans inf_le_left
```

最後も、

```lean
rw [← hJKtop]
exact Ideal.mul_le_inf.trans inf_le_left
```

と

```lean
rw [← hJKtop]
exact Ideal.mul_le_inf.trans inf_le_right
```

にできる可能性が高い。

これはかなり魅力的じゃ。**v4.32.2 でも v4.33.0 でも同じソースになる**からの。

もっとも今回の migration diff としては、単純に `mul_le_left/right` を交換するのが正しい。だが、両版を長く並行維持するなら、この particular API だけは `mul_le_inf` 経由にしてしまうのもよいと思う。

そして何より、あのとき「名前からしてこっちだろう」と書いたコードを Lean 4.32.2 に叱られて全部直したのに、**Mathlib 側が後から『そっちが正しかったです』と直してきた**わけじゃな。これは記録に残してよい逸話じゃ（笑）。

> 👩‍⚕️私D.:

お。エラーが消えた。Green ✔✔

🔍 Running default build...
🚀 Starting build Lean...
⚠ [8832/9584] Replayed DkMath.NumberTheory.ZsigmondyCyclotomicResearch
warning: DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147:6: declaration uses `sorry`
⚠ [9284/9584] Replayed DkMath.FLT.PrimeProvider.TriominoCosmicBranchA
warning: DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean:4187:8: declaration uses `sorry`
⚠ [9290/9584] Replayed DkMath.NumberTheory.GcdNextResearch
warning: DkMath/NumberTheory/GcdNextResearch.lean:850:6: declaration uses `sorry`
⚠ [9308/9584] Replayed DkMath.FLT.Kummer.CyclotomicPrincipalization
warning: DkMath/FLT/Kummer/CyclotomicPrincipalization.lean:5389:8: declaration uses `sorry`
⚠ [9313/9584] Replayed DkMath.CosmicFormula.TriominoFLT
warning: DkMath/CosmicFormula/TriominoFLT.lean:1919:6: declaration uses `sorry`
🔍 Checking build results...
  see: __build.log:1
✅️ build succeeded

$ cat lean-toolchain
leanprover/lean4:v4.33.0

Migration 完了🎉

> 🐺賢狼:

おお、**Migration 完了じゃな。Green ✔✔ 🎉**

`leanprover/lean4:v4.33.0` で **9584 targets の default build 成功**。残っているのは既知の `sorry` warning だけで、migration 起因の error は消滅。

今回の成果はかなり大きい。

- `develop` の追加コミット群まで追従
- `Ideal.mul_le_left/right` の 4.33 API 変更へ対応
- `whnf` timeout は proof/API refactor で解消
- `set_option backward.isDefEq.respectTransparency.types false in` が必要な箇所も局所化
- 最終的に v4.33.0 全体 build Green

つまりこの branch はもう、

> **DkMath が Lean/Mathlib v4.33.0 上で全体ビルド可能であることを確認済みの migration baseline**

として保存できる状態じゃ。

そして先ほど決めた運用どおり、これはまだ `develop/main` へ昇格せず、**v4.32.2 本線と並行して v4.34+ まで保持**でよかろう。

いやあ、最後に `mul_le_left/right` が「実装当初のコードへ戻る」で締まったのも味わい深い（笑）。

**9584/9584 Green。Migration closeout じゃ。✔️**
