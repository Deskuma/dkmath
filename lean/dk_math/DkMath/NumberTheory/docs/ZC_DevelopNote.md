# Zsigmondy/Cyclotomic に関する開発ノート

## 開発ログ

### タスクリスト

## 📋 ZsigmondyCyclotomic.lean 進捗状況レポート

### 🔍 ドキュメント vs コード の乖離分析

#### **ドキュメント（ZC_DevelopNote.md）の記述**

```
完成した主要補題（no sorry!）: 8つ 🎉
残る sorry: 2箇所（研究課題）
```

#### **実際のコード状況**

| 行番号 | 補題名 | sorry タイプ | 状態 |
|--------|--------|---------|------|
| 891 | `squarefree_implies_padic_val_le_one` | **メイン補題** | ⏳ 未完成 |
| 943 | example (コメント例) | **ダミー** | コメント内のみ |
| 1082 | `padicValNat_le_one_of_prime_divisor_case_three` | **メイン補題** | ⏳ 未完成 |

**✅ 正確性：** ドキュメントの「2箇所」記述は **正しい**（メイン補題は2個）

---

### 🏗️ 実装の完成度レベル

#### **層A（存在層）：✅ 完全に堅牢**

```lean
lemma exists_primitive_prime_factor_basic
  (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
  (hab_lt : b < a) (hb : 0 < b) (hab : Nat.Coprime a b)
  (hpnd : ¬ d ∣ a - b) :
  ∃ q : ℕ, Nat.Prime q ∧ q ∣ a^d - b^d ∧ ¬ q ∣ a - b := by
  exact exists_prime_divisor_not_dividing_diff_of_prime_exp ...
```

- ✅ **no sorry で完成**
- ✅ **群論（ZMod + orderOf）で primitive 証明も完成**
- ✅ `hpnd : ¬ d ∣ a - b` を **陽に仮定**（正しい設計）

#### **層B（精密層）：⏳ 2個の sorry で停滞**

| sorry | 数学的内容 | 理由 |
|-------|---------|------|
| (1) `squarefree_implies_padic_val_le_one` | padicValNat ≤ 1 の一般上界 | **G の構造解析が難しい** |
| (2) `padicValNat_le_one_of_prime_divisor_case_three` | d=3 での精密評価 | **反例 (a=18, b=1) で v_q = 3** |

---

### 🚨 設計上の課題（ZC_DevelopNote.md が指摘したとおり）

#### **課題1：「padicValNat = 1」の強すぎる要求**

コード行 1081-1082：

```lean
-- ぬしよ、この先は難所じゃ。一般には v_q(a^2 + ab + b^2) ≤ 1 は成り立たぬ。
-- 例えば a = 18, b = 1 のとき a^2 + ab + b^2 = 343 = 7^3 となり、付値は 3 になる。
```

💡 **現象**：

- a = 18, b = 1, d = 3
- a^3 - b^3 = 5832 - 1 = 5831 = 7 × 833
- a^2 + ab + b^2 = 324 + 18 + 1 = 343 = 7^3
- padicValNat 7 (343) = 3 ❌（1 ではない）

✅ **ドキュメントの解決案**：

- 層Aで「存在」を確定（これは OK）
- 層B は「追加条件下」で「≤ 1」を保証（例：non-Wieferich など）

---

### 📊 補題の完成度サマリー

#### **✅ 完成（no sorry）**

1. `exists_primitive_prime_factor_basic`
2. `prime_exp_not_dvd_diff_imp_primitive`
3. `pow_sub_pow_factor_cosmic` (ℤ版)
4. `pow_sub_pow_factor_cosmic_N` (ℕ版)
5. `padicValNat_of_primitive_prime_factor_via_G`
6. `kummer_theorem_for_binomial_coeff`
7. `G_three_explicit`
8. `GN_three_explicit`
9. `padicValNat_binomial_coeff_three`
10. `G と GN の係数解析` など

✅ **計10個以上の完成補題**（ドキュメント記載の「8個」より増えてる！）

#### **⏳ 未完成（sorry 付き）**

1. `squarefree_implies_padic_val_le_one` — **一般的な上界（G 解析）**
2. `padicValNat_le_one_of_prime_divisor_case_three` — **d=3 の反例条件**

---

### 💡 ドキュメント vs コードの乖離箇所

| ポイント | ドキュメント | コード | 評価 |
|---------|------------|--------|------|
| 完成補題数 | 8個 | 10個以上 | ✅ **コードが進んでいる** |
| sorry 数 | 2個 | 2個（+1ダミー） | ✅ **一致（ダミーは無視）** |
| 層A 状態 | no sorry で完成 | no sorry で完成 | ✅ **完全に一致** |
| 層B 方針 | 分離・追加仮定で | 反例で立ち止まり | ⚠️ **方針転換が必要** |

---

### 🎯 最新の開発ノートの主張との相互参照

開発ノートが推奨した：

> **「層Aを確定」→「ZMod で primitive（∀k<d）確定」→「Cyclotomic 接続へ」**

現実：

- ✅ 層A **確定済み**
- ✅ ZMod での primitive **完成済み** (`prime_exp_not_dvd_diff_imp_primitive`)
- ⏳ 層B の padicValNat は **反例で停滞中**
- ❌ Cyclotomic への接続 **未実装**

---

### 🔧 推奨アクション（わっちの見立て）

#### **短期（1-2日）**

1. **層B の sorry を「条件付き」に格下げ**

   ```lean
   /-- d=3 での精密評価（追加条件付き：non-Wieferich など） -/
   lemma padicValNat_eq_one_if_condition {a b q : ℕ}
       (h_condition : ...) : padicValNat q (...) = 1 := by
   ```

2. **existing_primitive_prime_factor での「存在」を層Aで完全に宣言**
   - `hpnd` を陽に仮定 ✅ (既にそうなってる)
   - composite d ケースは別ファイルへ（未実装のままで OK）

#### **中期（1週間）**

1. **Cyclotomic 多項式との接続を開始**
   - `cyclotomic_dvd_pow_sub_one` との link
   - 原始素因子 → Φ_d の因子 の対応

#### **長期（研究）**

1. **LTE (Lifting the Exponent) の詳細版導入**
   - padicValNat = 1 の精密証明が必要になる場合

---

### 📝 最後に

わっちの見立てはこうじゃ：

**ドキュメント（ZC_DevelopNote.md）と コード（ZsigmondyCyclotomic.lean）の乖離は「予期されたもの」じゃ。**

ドキュメントは「理想的なロードマップ」を示し、コードは「実装時の困難」に直面している。特に：

- ✅ **層A（存在）の骨格は完璧**
- ✅ **補助補題群も豊富に完成**
- ⏳ **層B（精密付値）で「padicValNat = 1 は一般には偽」という発見**

この「発見」こそ が重要なのじゃ。反例 (a=18, b=1, d=3) の存在は、**決して失敗ではなく、定理の境界を正しく認識した証**じゃぞ。

---
---
---

### 作業中

うむ、ぬしよ。まず状況把握からじゃ。

手元の `/mnt/data/ZsigmondyCyclotomic.lean` を見る限り、`sorry` は **16 個**残っておる（`grep` で拾えるやつだけでも）。そして、その中には

- **「その補題、いまの流れだと使ってない（消して良い）」**
- **「その `sorry` は“要らない”というより、仮定が足りなくて“証明できない”」**
- **「その主張は数学的に強すぎて、一般には偽の可能性が高い」**

が混ざっておる。ここを整理すると一気に“完成”に近づくぞ。

---

## 1. 残る `sorry` は「要らないもの」か？

### A. ほぼ確実に **要らない（削除候補）**

**(1) `not_dvd_diff_iff_not_modEq`（冒頭の補題）**
このファイル内で **参照されていない**。しかも “条件を言い換える補助” なので、後で必要になったら復活でよい。
→ いったん削除（または `TODO/` に隔離）で、`sorry` を2個減らせる。

**(2) `example` ブロック（docstring 用）**
`example := by sorry` はビルド警告の温床。
→ “例” はコメントに落とすのが吉。

**(3) `kummer_theorem_for_binomial_coeff`（ラッパ補題）**
現状は「見つからないので `sorry`」。しかも下流で必須になってない。
→ 削除か、`-- TODO: #check padicValNat_choose` のメモに格下げ。

---

### B. 「要らない」ではなく **“仮定が足りなくて証明不能”**（＝定理の形を直すべき）

一番大事なのがこれじゃ：

**`exists_primitive_prime_factor_hook` 内の**

```lean
have hpnd : ¬ d ∣ a - b := by sorry
```

これは一般には導けぬ。例：(a=5, b=2, d=3) だと (a-b=3) で (d \mid (a-b)) が成り立つ。
つまり **この `sorry` は「要らない」のではなく「定理が強すぎる」** のじゃ。

✅ 打開策（推奨）
`hpnd : ¬ d ∣ a - b` を **仮定として引数に追加**して、層A（存在層）へ正しく戻す。

さらに、同じ補題の最後：

```lean
· -- d が合成数の場合は TODO
  sorry
```

これも「要らない」のではなく、「この lemma を prime d に限定するなら要らない」タイプ。
✅ つまり **最初から `Nat.Prime d` を仮定に入れてしまえば `sorry` が消える**。

---

### C. 数学的に “強化しすぎ” の匂いが濃い（＝方針を変えるべき）

`padicValNat q (a^d - b^d) = 1` を **常に保証する**路線は、かなり危険じゃ。

理由は単純で、原始素因子（primitive prime divisor）であっても
[ q^2 \mid (a^d-b^d) ]
が起きる可能性は理論的に否定できん（“Wieferich 的”な現象）。
つまり「原始性」から「付値=1」を一般に引き出すのは、別の強い定理が要るか、そもそも偽の可能性がある。

なのでここは分岐じゃ：

- **(現実的ルート)** まずは Zsigmondy の「存在・原始性」までを **`sorry なしで確定**
- **(研究ルート)** `padicValNat = 1` は **追加条件つき**（例：`q ∤ d` だけでは足りないかもしれん）か、別定理として後回し

---

## 2. いま一番キレイに“完成”させる修正（層Aの確定）

ぬしの現状コード資産（`exists_prime_divisor_not_dividing_diff_of_prime_exp`）に一番沿う形で、**`hook` を「正しい仮定」に直して層Aで閉じる**のが最短じゃ。

```lean
/-- 層A（存在層）：prime d ≥ 3 の原始素因子（差を割らない素因子）の存在 -/
lemma exists_primitive_prime_factor_prime {a b d : ℕ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hab_lt : b < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (hpnd : ¬ d ∣ a - b) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ a^d - b^d ∧ ¬ q ∣ a - b := by
  exact exists_primitive_prime_factor_basic
    (a := a) (b := b) (d := d)
    hd_prime hd_ge hab_lt hb hab hpnd
```

これで `exists_primitive_prime_factor_hook` という “何でも版” はいったん捨てて良い。
（必要になったら「Zsigmondy完全版」へ戻して復活すればよい。）

---

## 3. 次の作業提案（打開策つき）

### ステップ1：層Aファイルを “No-sorry” で固定

- 使ってない `not_dvd_diff_iff_not_modEq` を削除（または別ファイルへ隔離）
- `hook` を上の `exists_primitive_prime_factor_prime` に置換
- composite case は扱わず、最初から `Nat.Prime d` を仮定にする

👉 これで「原始素因子の存在」を Lean 上で堅牢な部品として持てる。

---

### ステップ2：primitive（∀k<d で割らない）を “群論（ZMod）” で固める

ぬしが前に進めてた「order で切る」ルートが最も筋が良い。
つまり ( (a/b)) の位数が (d) であることを示し、そこから (k<d) では 1 にならぬ、という流れ。

ここが固まると、Cyclotomic に接続しやすくなる（“(d) 次の原始根”＝“(\Phi_d) の根”）。

---

### ステップ3：Cyclotomic は「一般指数 d」へ行きたい時の本丸

今の段階で Cyclotomic を無理に詰めると、`padicValNat=1` の誘惑で沼りやすい。

おすすめは：

- まずは **「primitive prime divisor ⇒ cyclotomic の因子」**（mod (q) 上）を作る
- その後に一般指数 (d) の Zsigmondy（完全版）へ拡張

---

## 4. 結論：残る `sorry` は「要らない」のもあるが、“定理の形を直すべき”のが核心

特に

- `hpnd : ¬ d ∣ a - b` を内部で作る `sorry` は **不要ではなく不可能**
- `padicValNat = 1` は **強化しすぎの可能性**（別レイヤへ隔離推奨）

この2点を整理すると、ぬしの実装は一気に“研究用の美しい骨格”になるぞ。

次はこの賢狼が相手になろう：
**「層Aを no-sorry 化 → ZMod の order で primitive（∀k<d）確定」**
ここまでを一本の Lean ファイルに“通る形”で整えるのが、次の一手じゃ。

### 完了

うむ、ぬしよ。**まずは「Cyclotomic に飛ぶ前の足場」を一気に固める** のが最短じゃ。結論から言うと、今の `exists_primitive_prime_factor_hook` は **いきなり `padicValNat = 1` を要求していて強すぎる**（一般には “原始素因子でも指数 2 以上” が起こり得る。いわゆる Wieferich 的な例外が混ざる）ので、最初の一歩はここを分離して設計し直すのが良いのじゃ。

以下、「何から始める？」への賢狼のおすすめロードマップじゃ。

---

## 0. 先に仕様を二層に分ける（ここが勝ち筋）

### 層A（Zsigmondy “存在” 層）

まずは **原始素因子の存在**だけ：

\[
\exists q,\ q\mid a^d-b^d,\ q\nmid a^k-b^k\ (\forall k<d)
\]

あるいは軽量版なら、今すでに骨組みがある

- 「\(q\mid a^p-b^p\) かつ \(q\nmid a-b\)」の **prime exponent版**（あなたの `exists_prime_divisor_not_dividing_diff_of_prime_exp`）をまず通す。

### 層B（付値 “精密” 層）

次に必要なら

- `1 ≤ padicValNat q (a^d - b^d)`（これは「割る」なので常に取れる）
- ある追加条件の下で `padicValNat = 1`（**ここは追加仮定が要る**：squarefree 条件、あるいは “non-Wieferich” 条件など）

というふうに段階化するのが、Lean でも数学でも破綻しない道じゃ。

---

## 1. まず埋めるべき TODO はどれ？

あなたのスケルトンの TODO は実質 2 個：

### (i) `hpnd : ¬ d ∣ a - b` をどうするか

これ、今の形だと **一般には出ない**ので、最初は割り切って：

- `exists_primitive_prime_factor_hook` の仮定に **そのまま `hpnd` を追加**する（“軽量版”として仕様を固定）
- あるいは “prime d” のとき `d ∣ a - b` が起きる条件を別補題として整理して、ユーザ側で潰せる形にする

が現実的じゃ。

実際、あなたの `exists_prime_divisor_not_dividing_diff_of_prime_exp` 自体が `hpnd` を仮定に持っているので、まずはそれで正しい。

### (ii) `padicValNat q (a^d - b^d) = 1`

これは **いきなり本丸に突撃してる**。先に言った通り、一般命題としては危ないので、

- まずは `padicValNat q (...) ≥ 1`（=「割る」）に落として通す
- “=1” は後段で、Cyclotomic か LTE + 追加仮定で拾う

にするのが良いのじゃ。

`padicValNat` 側の補題群はすでに整ってきておる（`padicValNat_le_iff_dvd` など）ので、層Bへ進むための道具は揃いつつある。

---

## 2. いまある資産で「確実に前進」できる地点

ここが気持ちよいところじゃ：

### A. 差の冪の因数分解はもうあなたが持ってる

`pow_sub_pow_factor` / `diffPowSum` が基礎。

### B. “gcd が d を割る” はもうある

`gcd_divides_d`（Int版）で、**「同時に割る素因子は d に吸われる」**の芯ができてる。

つまり Zsigmondy-lite（prime exponent）へは、

1. \(a^p-b^p=(a-b)\cdot G\)（商 \(G\) を定義）
2. \(G > 1\) より素因子 \(q\) を取る
3. もし \(q \mid (a-b)\) まで起きたら、gcd 補題で \(q \mid p\) を引き、`hpnd` と衝突させる

という“いつもの流れ”で行ける。これはまさにあなたの `exists_prime_divisor_not_dividing_diff_of_prime_exp` がやろうとしていることじゃ。

---

## 3. じゃあ「最初のコミット」は何にする？

賢狼の提案はこれじゃ：

### ✅ 最初の一手（小さく勝つ）

`exists_primitive_prime_factor_hook` を次のように **弱めて**通す：

- `padicValNat q (...) = 1` を消して
  `1 ≤ padicValNat q (a^d - b^d)` にする（あるいは単に `q ∣ ...` のまま）

そして `by_cases hd_prime` の素数ケースで

- `exists_prime_divisor_not_dividing_diff_of_prime_exp` を最後まで通して
- 合成数ケースは `sorry` のままでも良い（PR を分ける）

これだけで「Zsigmondy への接続点」が Lean 上で**堅牢に固定**できる。

### 次の一手（Cyclotomic へ進む前の下ごしらえ）

`¬ d ∣ a - b` を “生成できる条件” を別 lemma にする：

- 例：`d` が素数で、`a≡b (mod d)` が起きると何が起きるか、など
- ここは数学的にも整理価値が高い（後で Cyclotomic で自然に出る）

---

## 4. Cyclotomic に入るのはいつ？

「存在」層（層A）が Lean で回るようになったら、そこで初めて

- \(\Phi_d(a/b)\mid (a^d-b^d)\)
- 原始素因子は（だいたい）\(\Phi_d(a/b)\) の素因子として出る

という本筋に入るのが気持ちよい。

でも順番としては **“Zsigmondy-lite を通してから Cyclotomic”** が最短じゃ。
いきなり円分多項式を回すと、依存（既約性・原始根・order・有限体）が一気に重くなるからのぅ。

---

要するに、今やるべきは「Cyclotomic の城を建てる」ではなく、**城を建てるための地盤（層A）を Lean で確定する**ことじゃ。そうすれば、後からどんな立派な塔（Cyclotomic）を載せても崩れぬ。

（そして賢狼は、崩れる塔を眺めるのも嫌いではないが……ぬしの時間がもったいないからの。）

---

ぬしよ、状況はかなり良いところまで来ておる。いまの `ZsigmondyCyclotomic.lean` を眺めた限り、**「戦える部品」は揃い始めていて、詰まり所はだいたい 2～3 点に集約** されておるぞ。

---

## 1. いまの状況把握（どこまで出来ていて、何が“詰まりの核”か）

### できている（強い）

- **Kummer/Lucas 系の道具立て**（carry→`choose`→素因子が出る）が既に骨格として書けてる。これは “p-adic 付値を作る” 方向の布石として強い。
- `exists_prime_divisor_not_dividing_diff_of_prime_exp ...` を使う流れ（＝「差の冪の因数から、差 (a-b) を割らない素数を引っ張る」）は、**prime exponent（素数指数）では Zsigmondy 的本質** にかなり近い。

### 本当に詰まっている（重要）

**(A) `hpnd : ¬ d ∣ a - b` を「証明」しようとしている点**

- これは一般には **証明できぬ**（成り立たない入力が普通にある）。
- つまりここは **“仮定として受け取る”** か、あるいは **`by_cases h : d ∣ a - b` で分岐して両方の道を用意** するしかない。

**(B) `padicValNat q (a^d - b^d) = 1` を “Zsigmondy で保証したい” 点**

- ここが一番危険じゃ。**Zsigmondy 自体は「指数 1」を保証しない** 。原始素因子でも (v_q) が 2 以上になるケースは理屈として排除できない（平方因子が入る問題）。
- なので当面は、

  - **まず primitive（原始性）を確立**
  - 付値 1 は **“強化版”として別レイヤ**
    がおすすめじゃ。

**(C) `Nat.ModEq` と `d ∣ a - b` の橋渡し**

- ここは Mathlib 側に既に良い補題がある。`Nat.modEq_iff_dvd'` など。([leanprover-community.github.io][3])
  → ここを埋めると `hpnd` 周りの扱いがきれいになる。

---

## 2. 方針（最短で前へ進む打開策）

### フェーズ1：仕様を“prime d 用”に固定して、原始性を先に取る

ぬしの欲しい「原始素因子」は、**(d) が素数なら**ほぼこう言い換えできる：

> \(q \mid (a^d-b^d)\) かつ \(q \nmid (a-b)\) なら、
> \(q \nmid (a^k-b^k)\)（すべての \(0 < k < d)\）が従う（＝primitive）。

理由は群論の基本：
\(r := a \cdot b^{-1} \in (\mathbb{Z}/q\mathbb{Z})^\times\) と置くと \(r^d=1\)。さらに \(r\neq 1\)（これは \(q\nmid(a-b)\) と同値）で、\(d\) が素数なら \(\mathrm{ord}(r)=d\)。よって \(k < d\) では \(r^k\neq 1\)。

つまり **prime exponent の場合**、ぬしの今の出力（`¬ q ∣ a - b`）は、ちゃんと「原始性」へ昇格できる。
ここを Lean で 1 本定理として打てば、Zsigmondy の心臓が “動き出す”。

---

### フェーズ2：`hpnd` は「仮定にする」か「分岐させる」

いまの `hpnd : ¬ d ∣ a - b := by sorry` は、構造上ダメ筋じゃ。

- **最短の修正**：`exists_primitive_prime_factor_hook` の仮定に `hnd : ¬ d ∣ a - b` を追加してしまう。
  → まず通して進む。あとで一般化。
- **正攻法**：`by_cases h : d ∣ a - b` で 2 分岐にする。

  - `h : ¬ d ∣ a-b` の枝：今の道具で OK。
  - `h : d ∣ a-b` の枝：ここは LTE（lifting-the-exponent）や cyclotomic 評価で別ルートを用意。

（この分岐をするなら、ぬしが作っている Kummer/Lucas の道具が “役に立つ枝” が出てくる。）

---

### フェーズ3：`padicValNat = 1` は “別勲章” にする

現実的な落とし所はこうじゃ：

- まず **原始素因子 (q)** を得る（prime exponent なら上の群論で primitive まで取れる）
- 次に必要なら
  **「さらに (v_q=1) となる (q) が存在する」**を、追加条件つきで証明する
  （例：`q^2 ∣ a^d - b^d` を排除できる状況、あるいは cyclotomic 値の squarefree 性を使う状況）

cyclotomic 側には `Polynomial.squarefree_cyclotomic` などが既にあるので、将来ここへ繋げられる。([leanprover-community.github.io][4])

---

## 3. すぐ埋められる「小さい穴」：`Nat.ModEq` の TODO を消す

`not_dvd_diff_iff_not_modEq` は、`b ≤ a`（ぬしは `b < a` を持ってる）を使って

- `b ≡ a [MOD d] ↔ d ∣ a - b`（`Nat.modEq_iff_dvd'`）([leanprover-community.github.io][3])
- あとは `a ≡ b` を `symm` してつなぐ

で、かなり綺麗に閉じるはずじゃ。

ここを先に消すと、「分岐（`d ∣ a-b` か否か）」や「仮定整理」が一気に楽になる。

---

## 4. Cyclotomic 実装へどう繋ぐか（ロードマップ）

ぬしの目標「Cyclotomic 経由で一般の Zsigmondy」へは、段階を踏むのが吉：

1. **prime exponent の primitive を“群論（orderOf）”で確定**
2. その後、`Polynomial.cyclotomic_prime` などで
   「いま使ってる幾何級数因子＝ cyclotomic の評価」へ同定する([leanprover-community.github.io][4])
3. 最後に、`n` 合成数へは
   \(a^n-b^n=\prod_{d\mid n}\Phi_d(\cdot)\) の factorization と “proper divisors” の排除で押し広げる

ちなみに、Mathlib 側にも **Zsigmondy の定理自体が実装されている可能性が高い**（1000+ theorems に掲載されておる）。([leanprover-community.github.io][5])
もし名前が拾えれば「自作を薄くして呼び出しに寄せる」方が勝ち筋じゃ（ぬしのプロジェクトの趣旨的にも、依存を整理できて美味い）。

---

## 結論：賢狼のおすすめ “打開の一手”

**まずは「prime (d) なら、`q ∣ a^d-b^d` かつ `q ∤ a-b` ⇒ primitive」** を Lean で一本通す。
次に `hpnd` は **仮定へ移すか、`by_cases` 分岐へ昇格**。
`padicValNat = 1` は **強化版の別章** に隔離。

こうすると、いまの資産（`GcdDiffPow` の補題・Kummer/Lucas の装備）が死なず、しかも前へ進む速度が出る。賢狼の嗅覚では、ここがいちばん“気持ちよく伸びる枝”じゃよ。

（必要なら次の返答で、prime exponent の primitive 証明を Lean スケルトンでそのまま貼り付けられる形にしてやる。ぬしの repo 流儀に合わせて `ZMod`/`orderOf` ルートで組むのが速い。）

[3]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/ModEq.html "Mathlib.Data.Nat.ModEq"
[4]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Polynomial/Cyclotomic/Basic.html?utm_source=chatgpt.com "Mathlib.RingTheory.Polynomial.Cyclotomic.Basic"
[5]: https://leanprover-community.github.io/1000.html?utm_source=chatgpt.com "1000+ theorems"

---

よし来た、ぬしよ。**「prime exponent なら primitive は群論（order）で落ちる」** ——その骨格を、そのまま Lean に写すスケルトンを置いておくぞ。

狙いはこれじゃ：

- \(d\) が素数（\(d > 1\)）
- \(q\) が素数
- \(q \mid a^d - b^d\) かつ \(q \nmid a-b\)
- \(\gcd(a,b)=1\)（これで \(b \not\equiv 0 \pmod q\) を確保）

すると \(r := a/b \in (\mathbb{Z}/q\mathbb{Z})^\times\) が

\[
r^d = 1,\quad r\neq 1
\]

を満たすので、\(d\) 素数より \(\operatorname{ord}(r)=d\)。したがって \(0 < k < d\) では \(r^k \neq 1\)、ゆえに \(a^k \not\equiv b^k \pmod q\)、つまり \(q \nmid a^k - b^k\)。

以下が **Lean スケルトン** 。`sorry` を埋める場所が “詰まりポイント” になるように分割してある。

```lean
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement

namespace DkMath.NumberTheory.GcdNext

open scoped BigOperators

/--
prime exponent 版 primitive（骨格）

仮定:
- d は素数（>1）
- q は素数
- q ∣ a^d - b^d
- q ∤ a - b
- gcd(a,b)=1（⇒ b は mod q で 0 にならず、割り算できる）
結論:
- 0 < k < d なら q ∤ a^k - b^k
-/
lemma prime_exp_not_dvd_diff_imp_primitive
    {a b d q : ℕ}
    (hd : Nat.Prime d) (hd1 : 1 < d)
    (hq : Nat.Prime q)
    (hab : Nat.Coprime a b)
    (hq_div : q ∣ a^d - b^d)
    (hq_ndiv : ¬ q ∣ a - b) :
    ∀ {k : ℕ}, 0 < k → k < d → ¬ q ∣ a^k - b^k := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩

  -- 0) b が mod q で 0 にならない（b が割れる）を確保
  have hq_nb : ¬ q ∣ b := by
    -- もし q|b なら q|b^d, かつ q|a^d-b^d より q|a^d,
    -- 素数 q なので q|a、よって gcd(a,b) に q が入って矛盾
    sorry

  have hb0 : (b : ZMod q) ≠ 0 := by
    -- `(b : ZMod q) = 0 ↔ q ∣ b` を使って hq_nb から示す
    sorry

  have ha0 : (a : ZMod q) ≠ 0 := by
    -- 上と同様に a 側も（必要なら）確保
    -- ※実際には r を Units で作る都合で 0 でないことが要る
    sorry

  -- 1) Units（乗法群）に持ち上げて r := a/b を定義
  let ua : (ZMod q)ˣ := Units.mk0 (a : ZMod q) ha0
  let ub : (ZMod q)ˣ := Units.mk0 (b : ZMod q) hb0
  let r : (ZMod q)ˣ := ua * ub⁻¹

  -- 2) q | a^d - b^d から r^d = 1 を得る
  have hr_pow : r ^ d = 1 := by
    -- (a^d ≡ b^d mod q) を ZMod で書き、
    -- 両辺に b^{-d} を掛けて (a/b)^d = 1
    -- Units 側で整理すると r^d = 1
    sorry

  -- 3) q ∤ a-b から r ≠ 1 を得る
  have hr_ne : r ≠ 1 := by
    -- r = 1 ⇒ a ≡ b (mod q) ⇒ q | (a-b) に落として hq_ndiv と矛盾
    sorry

  -- 4) d が素数なので orderOf r = d（order は 1 か d しかない）
  have horder : orderOf r = d := by
    have hdiv : orderOf r ∣ d := by
      exact orderOf_dvd_of_pow_eq_one hr_pow
    have horder_ne1 : orderOf r ≠ 1 := by
      -- r ≠ 1 ⇒ orderOf r ≠ 1
      sorry
    -- hd（Nat.Prime d）と hdiv から orderOf r = 1 ∨ = d、1 を排除して d
    -- 使う補題候補: `hd.eq_one_or_eq_self_of_dvd` など
    sorry

  -- 5) 0 < k < d なら r^k ≠ 1（order=d が k を割れない）
  intro k hkpos hklt hk_dvd
  have hk1 : (r ^ k) = 1 := by
    -- a^k ≡ b^k (mod q) から r^k = 1 を導く（後で作る）
    -- ここは「結論の反対」を置いてしまったので、先に方針を変える：
    -- 今は hk_dvd : q ∣ a^k - b^k を仮定した形なので、
    -- それを ZMod の等式にして r^k = 1 を作る。
    sorry

  have hdivk : orderOf r ∣ k := by
    exact orderOf_dvd_of_pow_eq_one hk1

  have : d ∣ k := by
    -- orderOf r = d を使って
    simpa [horder] using hdivk

  -- d | k かつ 0 < k なら d ≤ k、しかし k < d なので矛盾
  have hk_ge : d ≤ k := by
    exact Nat.le_of_dvd (Nat.pos_of_gt hkpos) this
  exact (Nat.not_lt_of_ge hk_ge) hklt

/-
※上の最後の `intro ... hk_dvd` から先は、
「q ∣ a^k - b^k ⇒ r^k = 1」を作る補助補題を挟むのが綺麗。

次の補助補題を（別 lemma として）先に作るのがオススメ：

1) `dvd_pow_sub_pow_iff_zmod`:
   q ∣ a^k - b^k ↔ (a : ZMod q)^k = (b : ZMod q)^k

2) `pow_eq_pow_iff_ratio_pow_eq_one`:
   (a : ZMod q)^k = (b : ZMod q)^k ↔ (ua * ub⁻¹)^k = 1
-/

end DkMath.NumberTheory.GcdNext
```

---

### 使い方（ぬしのファイルへ組み込むコツ）

- まずこの lemma を **“primitive 変換器”** として作っておくと、
  ぬしが既に持ってる
  `exists_prime_divisor_not_dividing_diff_of_prime_exp`
  から出てくる (q) が、そのまま primitive へ昇格できる。

- そして最大の山はここ：

  - `q ∣ a^k - b^k` ↔ `((a : ZMod q)^k = (b : ZMod q)^k)`
  - `r = ua * ub⁻¹` に落として `r^k = 1` を組み立てる補助補題

この 2 つを別 lemma に切り出すと、`simp` が効くようになって一気に進むぞ。

---

ぬしの現状（`ZsigmondyCyclotomic.lean` の流れ）だと、この skeleton を入れるだけで **「存在（q を取る）」→「primitive（全部の k を潰す）」が直結**する。
次は、ぬしの好み次第で「Nat で言い切る」か「ModEq で言い切る」かを揃えるだけじゃ。

---
