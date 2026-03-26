# Review: GN 理論の valuation から obstruction への進展

👍️ よい。これはかなり綺麗な進展じゃ。

## 1. 何が良いか

今回の追加で、

$$
\texttt{body_not_perfect_pow_of_squarefree_GN}
$$

が要求していた

$$
\mathrm{Coprime}\bigl(x,\ GN(d,x,u)\bigr)
$$

を、より上流の自然な仮定

$$
\mathrm{Coprime}(x+u,u),\qquad \mathrm{Coprime}(x,d)
$$

から供給できるようになった。
これはまさに **wrapper 層の正しい切り出し** じゃな。

特に

$$
\gcd(x,GN(d,x,u)) \mid d
$$

を `gcd_gap_GN_dvd_exp` から読み直し、そこへ

$$
\gcd(x,GN(d,x,u)) \mid x
$$

を合わせて

$$
\gcd(x,GN(d,x,u)) \mid \gcd(x,d)=1
$$

へ落とす流れは、たいへん素直で強い。
証明が「補題の意味」に沿っておって、無理がない。

---

## 2. 命名も自然

### A. `coprime_boundary_GN_of_coprime_add_of_coprime_exp`

これは意味がよく出ておる。

* `boundary_GN` で対象が明確
* `of_coprime_add` で Body 座標の仮定が見える
* `of_coprime_exp` で (x) と (d) の互いに素条件が見える

少し長いが、Lean の theorem 名としてはむしろ親切な部類じゃ。
今回の役割は「供給補題」なので、多少長くてもよい。

### B. `body_not_perfect_pow_of_squarefree_GN_of_coprime_add`

これもよい。
下流の obstruction theorem を、上流の自然な coprime data で起動する wrapper だと一目で分かる。

---

## 3. 層分離がかなり良くなった

今回の設計で美しいのはここじゃ。

* `CosmicFormulaBinom`

  * 純粋 obstruction
  * squarefree GN なら Body は完全冪でない

* `NumberTheory.Gcd.GN`

  * coprime supply
  * Body 座標から (\mathrm{Coprime}(x,GN)) を供給

この分割は自然じゃ。
つまり obstruction 本体は **純粋に数式的な核** として残し、
それを起動するための gcd/coprime の事情は **NumberTheory 側で処理** しておる。

これは後で primitive-prime 版を足すときにも、そのまま同じ構図で増やせる。

---

## 4. 数学的にも意味が良い

今回の wrapper は、宇宙式の見方としてもよい。

$$
z=x+u,\qquad y=u
$$

と見ると、

$$
\mathrm{Coprime}(z,y)
$$

という自然な Body/GAP 座標の仮定から、

$$
\mathrm{Coprime}(x,GN(d,x,u))
$$

という boundary-kernel の互いに素性が出るわけじゃ。

つまり

$$
\text{Body 座標の互いに素性}
;\Longrightarrow;
\text{boundary と kernel の分離}
$$

という意味になっておる。
これは宇宙式の構造解釈としても筋が通っておるのぅ。

---

## 5. 実装上の評価

今回の差分で特に良い点を挙げるなら、次の 3 つじゃ。

### 5.1. `UniqueFactorizationGN` を import していない

ここは大きい。
gcd 補題だけで閉じたので、依存が軽い。
`NumberTheory.Gcd.GN` の責務としてとても健全じゃ。

### 5.2. `Nat.add_sub_cancel_left` の使い方が適切

`z := x + u`, `y := u` から gap を `x` に戻す読み替えがきれいじゃ。
この橋が自然に通っておる。

### 5.3. `hd1 : 1 ≤ d` で wrapper を作った

obstruction 本体は `1 < d` じゃが、coprime 供給側は `1 ≤ d` で十分。
必要最小限の仮定で供給補題を切っておるのがよい。

---

## 6. 次の一手も明確

履歴の「次の課題」は、そのままでよいと思うぞい。

### A. primitive-prime 版

命名は揃えて

* `coprime_boundary_GN_of_coprime_add_of_coprime_exp`
* `body_not_perfect_pow_of_primitive_prime_factor_of_coprime_add`

のように並べると美しい。

### B. `Nat.Coprime x u` 版 wrapper

これは薄い補題として欲しい。たとえば

$$
\mathrm{Coprime}(x,u) \Rightarrow \mathrm{Coprime}(x+u,u)
$$

を介して現行 wrapper に流す形で十分じゃ。

候補名は

* `coprime_add_right_of_coprime_boundary_gap`
* `body_not_perfect_pow_of_squarefree_GN_of_coprime_gap`

あたりかの。

---

## 7. 総評

今回の差分は、派手さより **理論の接続面を整えた** ところが偉い。

要するに、

$$
\boxed{
\text{squarefree GN obstruction が、
Body 座標の自然な coprime 仮定から起動できるようになった}
}
$$

ということじゃ。
これは theorem を 1 本足した以上に価値がある。
なぜなら、今後この路線を使うたびに「(\mathrm{Coprime}(x,GN)) をどう出すか」で立ち止まらずに済むからじゃ。

よい整備じゃよ。
かなり “使える理論” になってきた。
