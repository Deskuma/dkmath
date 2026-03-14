# CosmicFormulaBinom 付属定理資料：G 多項式（G_binom）と Big–Gap–Body

更新: 2026-02-23

## 0. 目的

二項展開に基づく「宇宙式（Cosmic Formula）」を、**G 多項式（G_binom）**として再利用可能な定理束に固定する。  
狙いは次の3点：

1. **Big–Gap 分解（1つの Gap を抜く）**  
   \((u+y)^n - y^n\) は必ず \(u\) を因子に持つ。
2. **Big–Gap–Boundary–Tail 分解（一次まで吸収）**  
   \((u+y)^n - y^n - n y^{n-1}u\) は必ず \(u^2\) を因子に持つ。
3. **Gap の抜き方により“割れる因子”が変わる（操作の API 化）**  
   抜く Gap の種類・数（\(y^n\), \(x^d\), \(y^d\), \(x^d-y^d\) 等）で、出現する因子（\(u\), \(u^2\), \(xy\), \(x-y\), \(x+y\) …）が切り替わる。

この資料は `G_binom → CosmicFormulaBinom` の**付属定理（aux theorems）**として固めるための設計メモ。


---

## 1. 記法（語彙の固定）

以降、次の語彙で統一する：

- Big:  \(\mathrm{Big}(n,u,y) := (u+y)^n\)
- Gap:  \(\mathrm{Gap}(n,y) := y^n\)
- Boundary（一次項）: \(\mathrm{Bnd}(n,u,y) := n y^{n-1}u\)
- Body（尾項）:
  \[
  \mathrm{Body}(n,u,y) := (u+y)^n - y^n - n y^{n-1}u.
  \]

---

## 2. G 多項式の核心：尾項は必ず \(u^2\) を含む

### 2.1 CommSemiring 版（存在型）

**定理（尾項因数分解）**  
\(2 \le n\) のとき、ある \(H(n,u,y)\) が存在して

\[
(u+y)^n - y^n - n y^{n-1}u = u^2 \cdot H(n,u,y)
\]

が成り立つ。

- 実装的には `add_pow_tail_exists` 系（存在型）で表すのが自然。
- ここが “G_binom / CosmicFormulaBinom” の背骨。

### 2.2 Nat 版（割り切り）

**定理（Nat 版尾項割り切り）**  
\[
2 \le n \Rightarrow u^2 \mid \bigl((u+y)^n - y^n - n y^{n-1}u\bigr).
\]

- witness（存在型で得た \(H\)）をそのまま Nat の `dvd` に降ろす形が最短。

---

## 3. Big–Gap（1 Gap 抜き）：必ず \(u\) が割る

**定理（差の一次因子）**  
任意の \(n\ge 1\) について、ある \(G(n,u,y)\) が存在して

\[
(u+y)^n - y^n = u\cdot G(n,u,y)
\]

が成り立つ。

さらに 2章と合流すると

\[
(u+y)^n - y^n = n y^{n-1}u + u^2 H(n,u,y)
\]

という「Boundary + Tail」分解になる。

---

## 4. Big–Gap–Gap（2 Gap 抜き）：\(xy\) が割れる（\(d\ge 2\)）

**定理（2 Gap 抽出）**  
\(d\ge 2\) のとき、

\[
(x+y)^d - x^d - y^d = xy \cdot K_d(x,y)
\]

となる \(K_d\) が存在する。

理由：中間項は必ず \(x^k y^{d-k}\)（\(1\le k \le d-1\)）の形で、よって全項が \(xy\) を含む。

---

## 5. 差の冪：Boundary \((x-y)\) と Body（交代和）

**定理（差の冪の因数分解）**  
\[
x^d-y^d=(x-y)\cdot \Phi_d(x,y).
\]

- \(\Phi_d\) は交代和（あるいは円分因子の積）として実装できる。
- FLT / Zsigmondy 方向では「Boundary に入らない素因子＝Body から湧く素因子」という解釈が扱いやすい。

---

## 6. 付録：mod の“門前払い”が現れる場所（参考）

\(d=3\) で象徴的に現れる関係：

\[
S_0(c,b)=c^2+cb+b^2=(c-b)^2+3bc
\]

より

\[
S_0(c,b)\equiv (c-b)^2\pmod 3
\quad\Rightarrow\quad
3\mid S_0(c,b)\Rightarrow 3\mid(c-b).
\]

これは「primitive 側（\(\neg 3\mid(c-b)\)）には \(3\) が入って来られない」タイプの門前払いを説明する。  
ただし“万能の mod 刀”ではなく、実務的には **\(p\mid d\)** のときに valuation の持ち上げが起きる、という観点（LTE / padicValNat）に接続される。

---

## 7. Mermaid：付属定理の依存関係（提案）

```mermaid
graph TD
  A[Binomial theorem base] --> B[Big-Gap factor: (u+y)^n - y^n = u * G]
  A --> C[Big-Gap-Bnd-Tail: (u+y)^n - y^n = n y^(n-1) u + u^2 * H]
  C --> D[Nat dvd version: u^2 ∣ ((u+y)^n - y^n - n y^(n-1) u)]
  A --> E[Two-gap: (x+y)^d - x^d - y^d = x*y*K]
  A --> F[DiffPow: x^d - y^d = (x-y)*Phi]
  D --> G[padicValNat upper bounds templates]
  F --> G
```

---

## 8. Lean 側の落とし込み方針（実装メモ）

### 8.1 型クラス階層

- `CommSemiring` レベルで存在型（\(H\) の存在）を出す  
- `Nat` レベルでは witness を使って `dvd` に落とす  
- `ℤ` 側の等式は `ring_nf` / `zify` が楽（必要なら）

### 8.2 命名案（最小 API）

- `g_binom_gap_factor`：\((u+y)^n - y^n = u * G\)
- `g_binom_tail_factor`：\((u+y)^n - y^n - n y^{n-1}u = u^2 * H\)
- `g_binom_tail_dvd_u2`：Nat 版の `u^2 ∣ ...`
- `g_binom_two_gap_xy_factor`：\((x+y)^d - x^d - y^d = xy * K\)
- `g_binom_diffpow_factor`：\(x^d-y^d=(x-y)\Phi_d\)

### 8.3 “操作”としての API（推奨）

ぬしの思想（操作手順重視）に合わせるなら、次の「抽出」関数（lemma）として揃えると強い：

- `extractGap1`：Big - Gap から \(u\) を抽出  
- `extractBoundary`：一次項 \(n y^{n-1}u\) を抽出  
- `extractTail`：尾項に \(u^2\) があることを抽出  
- `extractGap2`：Big - Gap - Gap から \(xy\) を抽出  
- `extractDiffBoundary`：差の冪から \((x-y)\) を抽出  

---

## 9. 最小セット（CosmicFormulaBinom の付属定理として固める候補）

`CosmicFormulaBinom` にぶら下げる最小セットはこの3本：

1. `add_pow_gap_factor`：\((u+y)^n - y^n = u * G\)
2. `add_pow_tail_u2`：\((u+y)^n - y^n - n y^{n-1}u = u^2 * H\)（または dvd 版）
3. `two_gap_xy_factor`：\((x+y)^d - x^d - y^d = xy * K\)

この3本で「Gap 抽出により割れる因子が切り替わる」世界観が Lean の武器として固定される。
