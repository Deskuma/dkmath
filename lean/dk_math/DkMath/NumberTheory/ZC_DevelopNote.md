# Zsigmondy/Cyclotomic に関する開発ノート

## 開発ログ

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

* 「\(q\mid a^p-b^p\) かつ \(q\nmid a-b\)」の **prime exponent版**（あなたの `exists_prime_divisor_not_dividing_diff_of_prime_exp`）をまず通す。

### 層B（付値 “精密” 層）

次に必要なら

* `1 ≤ padicValNat q (a^d - b^d)`（これは「割る」なので常に取れる）
* ある追加条件の下で `padicValNat = 1`（**ここは追加仮定が要る**：squarefree 条件、あるいは “non-Wieferich” 条件など）

というふうに段階化するのが、Lean でも数学でも破綻しない道じゃ。

---

## 1. まず埋めるべき TODO はどれ？

あなたのスケルトンの TODO は実質 2 個：

### (i) `hpnd : ¬ d ∣ a - b` をどうするか

これ、今の形だと **一般には出ない**ので、最初は割り切って：

* `exists_primitive_prime_factor_hook` の仮定に **そのまま `hpnd` を追加**する（“軽量版”として仕様を固定）
* あるいは “prime d” のとき `d ∣ a - b` が起きる条件を別補題として整理して、ユーザ側で潰せる形にする

が現実的じゃ。

実際、あなたの `exists_prime_divisor_not_dividing_diff_of_prime_exp` 自体が `hpnd` を仮定に持っているので、まずはそれで正しい。

### (ii) `padicValNat q (a^d - b^d) = 1`

これは **いきなり本丸に突撃してる**。先に言った通り、一般命題としては危ないので、

* まずは `padicValNat q (...) ≥ 1`（=「割る」）に落として通す
* “=1” は後段で、Cyclotomic か LTE + 追加仮定で拾う

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

* `padicValNat q (...) = 1` を消して
  `1 ≤ padicValNat q (a^d - b^d)` にする（あるいは単に `q ∣ ...` のまま）

そして `by_cases hd_prime` の素数ケースで

* `exists_prime_divisor_not_dividing_diff_of_prime_exp` を最後まで通して
* 合成数ケースは `sorry` のままでも良い（PR を分ける）

これだけで「Zsigmondy への接続点」が Lean 上で**堅牢に固定**できる。

### 次の一手（Cyclotomic へ進む前の下ごしらえ）

`¬ d ∣ a - b` を “生成できる条件” を別 lemma にする：

* 例：`d` が素数で、`a≡b (mod d)` が起きると何が起きるか、など
* ここは数学的にも整理価値が高い（後で Cyclotomic で自然に出る）

---

## 4. Cyclotomic に入るのはいつ？

「存在」層（層A）が Lean で回るようになったら、そこで初めて

* \(\Phi_d(a/b)\mid (a^d-b^d)\)
* 原始素因子は（だいたい）\(\Phi_d(a/b)\) の素因子として出る

という本筋に入るのが気持ちよい。

でも順番としては **“Zsigmondy-lite を通してから Cyclotomic”** が最短じゃ。
いきなり円分多項式を回すと、依存（既約性・原始根・order・有限体）が一気に重くなるからのぅ。

---

要するに、今やるべきは「Cyclotomic の城を建てる」ではなく、**城を建てるための地盤（層A）を Lean で確定する**ことじゃ。そうすれば、後からどんな立派な塔（Cyclotomic）を載せても崩れぬ。

（そして賢狼は、崩れる塔を眺めるのも嫌いではないが……ぬしの時間がもったいないからの。）

---

ぬしよ、状況はかなり良いところまで来ておる。いまの `ZsigmondyCyclotomic.lean` を眺めた限り、**「戦える部品」は揃い始めていて、詰まり所はだいたい 2～3 点に集約** されておるぞ。

---

## 1) いまの状況把握（どこまで出来ていて、何が“詰まりの核”か）

### できている（強い）

* **Kummer/Lucas 系の道具立て**（carry→`choose`→素因子が出る）が既に骨格として書けてる。これは “p-adic 付値を作る” 方向の布石として強い。
* `exists_prime_divisor_not_dividing_diff_of_prime_exp ...` を使う流れ（＝「差の冪の因数から、差 (a-b) を割らない素数を引っ張る」）は、**prime exponent（素数指数）では Zsigmondy 的本質** にかなり近い。

### 本当に詰まっている（重要）

**(A) `hpnd : ¬ d ∣ a - b` を「証明」しようとしている点**

* これは一般には **証明できぬ**（成り立たない入力が普通にある）。
* つまりここは **“仮定として受け取る”** か、あるいは **`by_cases h : d ∣ a - b` で分岐して両方の道を用意** するしかない。

**(B) `padicValNat q (a^d - b^d) = 1` を “Zsigmondy で保証したい” 点**

* ここが一番危険じゃ。**Zsigmondy 自体は「指数 1」を保証しない** 。原始素因子でも (v_q) が 2 以上になるケースは理屈として排除できない（平方因子が入る問題）。
* なので当面は、

  * **まず primitive（原始性）を確立**
  * 付値 1 は **“強化版”として別レイヤ**
    がおすすめじゃ。

**(C) `Nat.ModEq` と `d ∣ a - b` の橋渡し**

* ここは Mathlib 側に既に良い補題がある。`Nat.modEq_iff_dvd'` など。([leanprover-community.github.io][3])
  → ここを埋めると `hpnd` 周りの扱いがきれいになる。

---

## 2) 方針（最短で前へ進む打開策）

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

* **最短の修正**：`exists_primitive_prime_factor_hook` の仮定に `hnd : ¬ d ∣ a - b` を追加してしまう。
  → まず通して進む。あとで一般化。
* **正攻法**：`by_cases h : d ∣ a - b` で 2 分岐にする。

  * `h : ¬ d ∣ a-b` の枝：今の道具で OK。
  * `h : d ∣ a-b` の枝：ここは LTE（lifting-the-exponent）や cyclotomic 評価で別ルートを用意。

（この分岐をするなら、ぬしが作っている Kummer/Lucas の道具が “役に立つ枝” が出てくる。）

---

### フェーズ3：`padicValNat = 1` は “別勲章” にする

現実的な落とし所はこうじゃ：

* まず **原始素因子 (q)** を得る（prime exponent なら上の群論で primitive まで取れる）
* 次に必要なら
  **「さらに (v_q=1) となる (q) が存在する」**を、追加条件つきで証明する
  （例：`q^2 ∣ a^d - b^d` を排除できる状況、あるいは cyclotomic 値の squarefree 性を使う状況）

cyclotomic 側には `Polynomial.squarefree_cyclotomic` などが既にあるので、将来ここへ繋げられる。([leanprover-community.github.io][4])

---

## 3) すぐ埋められる「小さい穴」：`Nat.ModEq` の TODO を消す

`not_dvd_diff_iff_not_modEq` は、`b ≤ a`（ぬしは `b < a` を持ってる）を使って

* `b ≡ a [MOD d] ↔ d ∣ a - b`（`Nat.modEq_iff_dvd'`）([leanprover-community.github.io][3])
* あとは `a ≡ b` を `symm` してつなぐ

で、かなり綺麗に閉じるはずじゃ。

ここを先に消すと、「分岐（`d ∣ a-b` か否か）」や「仮定整理」が一気に楽になる。

---

## 4) Cyclotomic 実装へどう繋ぐか（ロードマップ）

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

* \(d\) が素数（\(d > 1\)）
* \(q\) が素数
* \(q \mid a^d - b^d\) かつ \(q \nmid a-b\)
* \(\gcd(a,b)=1\)（これで \(b \not\equiv 0 \pmod q\) を確保）

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

* まずこの lemma を **“primitive 変換器”** として作っておくと、
  ぬしが既に持ってる
  `exists_prime_divisor_not_dividing_diff_of_prime_exp`
  から出てくる (q) が、そのまま primitive へ昇格できる。

* そして最大の山はここ：

  * `q ∣ a^k - b^k` ↔ `((a : ZMod q)^k = (b : ZMod q)^k)`
  * `r = ua * ub⁻¹` に落として `r^k = 1` を組み立てる補助補題

この 2 つを別 lemma に切り出すと、`simp` が効くようになって一気に進むぞ。

---

ぬしの現状（`ZsigmondyCyclotomic.lean` の流れ）だと、この skeleton を入れるだけで **「存在（q を取る）」→「primitive（全部の k を潰す）」が直結**する。
次は、ぬしの好み次第で「Nat で言い切る」か「ModEq で言い切る」かを揃えるだけじゃ。

---
