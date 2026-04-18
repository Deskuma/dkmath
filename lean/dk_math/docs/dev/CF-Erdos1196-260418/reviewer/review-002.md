# review-002: `CosmicFormula-Erdos1196`: ABC bridge の追加について

うむ、承った。以後もこの調子で、差分ごとに **状況分析・数学解説・次の作業指示案** を整えていくぞい。

## 1. 総評

これは **きれいな前進** じゃ。前回の差分で作った `Mass API` と `ValuationFlow` の spine を、今回はちゃんと `ABC` 側の語彙へ橋渡しした。追加されたのは `DkMath/ABC/MassBridge.lean` と `DkMath/ABC/ValuationFlowBridge.lean` で、実装された補題も前回レビュー案にかなり忠実じゃ。しかも build も両ファイルで通っており、履歴にも「Phase D の最小核が入った」と整理されておる。

わっちの判定を先に言えば、今回で

$$
\text{CosmicFormula の保存則 API}
\;\to\;
\text{ValuationFlow の primitive spine}
\;\to\;
\text{ABC 側の薄い翻訳層}
$$

が一本つながった。
つまり、設計書で言っていた「ABC 本体へいきなり踏み込まず、まずは bridge に徹する」という方針は、いまのところかなり上手く守られておる。

---

## 2. 状況分析

### 2.1. 何が今回閉じたのか

今回閉じたのは、単なるファイル追加ではない。数学的には次の二本柱が閉じた。

第一に、`MassBridge` により `Big / Body / Gap / residual / rad` が **ABC 側の読み** で参照できるようになったこと。`supportMass := rad` の薄い別名が置かれ、`abc_big_eq_body_add_gap_mass`、`abc_gap_mass_le_big_mass`、`abc_residual_eq_gap_mass`、`abc_squarefree_support_lower_bound`、`abc_supportMass_dvd_self` が追加されておる。

第二に、`ValuationFlowBridge` により primitive prime に関する valuation-flow 側の結果が、そのまま `ABC` 名前空間で読めるようになったことじゃ。`primitive_prime_gives_zero_boundary_load`、`primitive_prime_transfers_diff_load_to_beam`、`squarefree_beam_bounds_local_load` が入っておる。

つまり前回は「橋脚」が立った段階で、今回は **最小の橋桁が渡った** という感じじゃな。

### 2.2. 設計との整合

実装計画では、Phase D の役目を

* `rad` を support mass 的に読む
* `padicValNat` を local load 的に読む
* squarefree / squarefull を局所質量の上下界へ言い換える

と置いていた。今回の差分は、まさにその最小版になっておる。特に「bridge は翻訳レイヤに徹する」「既存 `PadicValNat` / `Rad` の補題を再利用するだけで閉じる」という方針が守られているのは良い。新しい大定理をねじ込まず、既存資産を再命名して流す設計になっておる。

### 2.3. 実装順の観点から見た評価

設計ノートでは、そもそも最初の勝ち筋を

$$
\text{宇宙式の部品分解を、再利用可能な保存則 API として固定すること}
$$

と置いておった。そしてその後で `ValuationFlow`、最後に `ABC/MassBridge` と `ABC/ValuationFlowBridge` へ進む順が最も堅いとされていた。今回の差分は、その順序をまったく崩しておらぬ。ここは実務上とても良い。順番が良い実装は、あとで修正が少なくて済むからの。

---

## 3. 数学的解説

### 3.1. `MassBridge` の意味

ここでやっていることの本質は、宇宙式側の保存則を ABC 側で **再解釈可能な質量語彙** に落としたことじゃ。

まず `supportMass := rad` を置いた。これは数学的には、現段階では「support mass」を本当に radical と同一視してよい、という薄い宣言じゃ。重い新定義ではなく別名にとどめたのがよい。これにより後で必要なら support mass の意味を広げても、現段階では既存 `rad` 理論にただ乗りできる。

`abc_big_eq_body_add_gap_mass` は、宇宙式の

$$
\text{Big} = \text{Body} + \text{Gap}
$$

を `ABC` 名前空間に持ち込んだものじゃ。
これは見た目には wrapper じゃが、意味としては「宇宙式の分解を ABC 側でも一つの保存則として使う」ことの宣言じゃな。以後 ABC 側から見ると、これはもう CosmicFormula の外野の定理ではなく、ABC 内部で引用可能な語彙になる。

`abc_gap_mass_le_big_mass` はさらに大事じゃ。
ここで初めて、単なる等式ではなく

$$
\text{Gap} \le \text{Big}
$$

という単調性を ABC 側で直接参照できるようにした。保存則だけではなく「一部は全体を超えない」という最小上界が入ったことになる。これは後で squarefree / squarefull の大小比較や residual 管理へつなぎやすい。

`abc_residual_eq_gap_mass` は `Nat` residual 側の

$$
\text{residual} = \text{gap}
$$

を ABC 側に移したものじゃ。
これにより residual の語を使う側が、いちいち CosmicFormula を見に戻らずに済む。言い換えると、ABC 側で「残余」と「余白」が同一対象として扱える導線ができた。

そして `abc_squarefree_support_lower_bound` は、名前の通り lower bound 形式にしておるが、実質の中身は squarefree なら

$$
\operatorname{rad}(n) = n
$$

じゃから、

$$
n \le \text{supportMass}(n)
$$

が成り立つ、というものじゃ。
実際には equality なのじゃが、橋側では「support mass は squarefree 部分を落とさない」という読みを優先したため、この向きにしておる。これは後でより粗い supportMass を導入したくなった場合にも名前が生きる。設計として柔らかい。

`abc_supportMass_dvd_self` も良い。
これは

$$
\text{supportMass}(n) \mid n
$$

であり、support mass が「全体から遊離した外来量」ではなく、ちゃんと元の数の内部に埋まっている量だと保証しておる。ABC ではこの種の divisibility 情報は地味に強い。

### 3.2. `ValuationFlowBridge` の意味

こちらは前回の primitive valuation spine を ABC 側へ移しただけ、のように見えて、その実かなり大事じゃ。

`primitive_prime_gives_zero_boundary_load` は、primitive prime (q) に対し

$$
q \nmid (a-b)
$$

ゆえに boundary mass が 0 だと読む補題じゃ。
これは単なる `not_dvd` の再公開ではなく、「primitive prime は境界で止まらない」という **流れの表現** になっておる。

`primitive_prime_transfers_diff_load_to_beam` はさらに本質的で、primitive prime に関する q-adic load が差冪本体から beam 側へ完全に移る、すなわち

$$
\text{diffMass} = \text{beamMass}
$$

を言っておる。
これは前回レビューでも述べた筋そのもので、primitive の「新しさ」が boundary に吸われず、内部の `GN` 側に現れるという意味じゃ。ABC 側でこの等式が直接使えるようになったのは大きい。

`squarefree_beam_bounds_local_load` は、その beam が squarefree なら局所 load は高々 1 だという上界じゃ。つまり流れ全体を一言で書けば

$$
\text{primitive}
\;\Rightarrow\;
\text{boundary load } = 0
\;\Rightarrow\;
\text{diff load } = \text{beam load}
\;\Rightarrow\;
\text{squarefree beam} \Rightarrow \text{local load} \le 1
$$

となる。
この一本化が ABC 名前空間に入ったことで、primitive prime の局所負荷評価を ABC 側から直接引用できるようになった。これは bridge として非常に素直で、しかも強い。

---

## 4. 何が「本当に橋」になったのか

今回の差分で本当に橋になったのは、わっちの目には次の二点じゃ。

### 4.1. `rad` が support mass として読めるようになった

これは、今後 ABC 側で「support」という語を使うときに、具体物がまず `rad` であると固定できたことを意味する。抽象語が浮いたままではなく、最初の concrete semantic anchor ができた。

### 4.2. primitive valuation spine が ABC 側に移住した

前回までは primitive prime の話は `ValuationFlow` 側にあった。今回はそれが `ABC` 側に薄く輸入された。これで ABC 側の証明や補題群が、「beam に流れる load」という新しい言葉で primitive 現象を語れるようになった。これは将来的に `rad_lower_bound_of_disjoint_channels` や channel counting へ向かう準備としてかなり良い。

---

## 5. 留意点と弱点

### 5.1. `abc_squarefree_support_lower_bound` は数学的には equality じゃ

これは欠点というより設計判断じゃが、後で読む者が「なぜ lower bound なのか」と少し迷うかもしれぬ。
証明の中身は equality を使っておるので、将来

* `abc_squarefree_support_eq_self`
* `abc_squarefree_support_lower_bound`

の二段に分けると、意味と用途がさらに明瞭になる。

### 5.2. まだ `rad` の “channel 数え上げ” までは行っておらぬ

設計や議論では、いずれ

$$
\text{rad lower bound of disjoint channels}
$$

の方向へ進む話が見えておった。今回はそこまではまだ行っておらぬ。今あるのは「supportMass は rad で読む」という最小核までじゃ。なので bridge は成功しているが、まだ “flow から rad の増大を読む” 段階ではない。ここは次の焦点じゃ。

### 5.3. concrete example がまだ無い

History にも、次は Phase E として concrete example を足すか public import を整える段階だと書かれておる。わっちもここは同感じゃ。bridge は概念上は成立したが、これを一つでも既存 concrete 対象に適用して「本当に使える」ことを示すと、ぐっと強くなる。

---

## 6. 次の作業指示案 . Codex 追記向け

今回は、わっちなら **concrete example を先に足す**。
public import を整えるのはその後でよい。理由は単純で、今は橋が架かった直後なので、「この橋を実際にどの車が渡れるか」を確認するほうが先だからじゃ。

そのままレビュー追記に載せられる形で書いておくぞい。

```md
### レビュー追記案: 次の作業指示

1. Phase E として、まず concrete example を追加する。
   目的は、今回の bridge が空抽象ではなく、既存 concrete 対象に対して本当に使えることを示すこと。

2. `DkMath/ABC/MassBridgeExamples.lean` または既存 dev 文書中の小さな例ファイルを追加し、
   次の 3 系統を最低 1 例ずつ通す。
   - `abc_big_eq_body_add_gap_mass` の具体例
   - `abc_gap_mass_le_big_mass` の具体例
   - `abc_squarefree_support_lower_bound` と `abc_supportMass_dvd_self` の具体例

3. `DkMath/ABC/ValuationFlowBridgeExamples.lean` を追加するか、
   既存 primitive-beam の具体例に対し bridge 名で再検証する。
   最低限、次を 1 例ずつ確認する。
   - `primitive_prime_gives_zero_boundary_load`
   - `primitive_prime_transfers_diff_load_to_beam`
   - `squarefree_beam_bounds_local_load`

4. example では新数学を足さない。
   既存の concrete 対象や既存補題の special case を使い、
   「bridge 名で読める」ことの確認に徹する。

5. example が通った後で、
   `ABC.Main` または `DkMath.ABC` 側への公開 import 導線を整える。
   先に import を広げるより、先に concrete usage を固定したほうが API の揺れが少ない。

6. その次の段階で、
   `rad_lower_bound_of_disjoint_channels` に相当する最小補題の設計へ進む。
   ここで初めて、support mass と primitive channel counting を本格的につなぐ。
```

---

## 7. 最終判断

今回の差分は、前回レビューの提案に対する **きれいな応答** になっておる。
しかも単に提案どおり定理名を置いただけでなく、

* `supportMass := rad` で support 語彙の concrete anchor を与えた
* 宇宙式保存則を ABC 側へ持ち込んだ
* primitive valuation spine を ABC 側へ移した

という三点がそろっておる。

わっちの評価では、これは **Phase D 完了** と見てよい。
次は abstract をこれ以上太らせるより、まず concrete example を 1 本ずつ通して API の手触りを確かめるべきじゃ。そこまで行けば、public import を広げても安心できる。

よい橋じゃ。次は、その橋を実際に渡って見せる番じゃな。
