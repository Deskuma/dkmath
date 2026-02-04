# Unit–Nat Layers and the White‑Silver Circle — Theorem Notes

> GitHub に置く「定理資料」ドラフト。  
> 目的：reddit 的な「\(\pi\) と \(e\) は交えるか？」を、
> **層（Layer）と橋（Bridge）**で分解し、Lean 形式化（UnitCycle / SilverRatio.Circle）へ接続する。

---

## 0. 立場の固定（最重要）

この資料では、同じ実数でも **住む層が違う**ことを明示して議論する。

- **Nat 層（離散・反復・増分）**：反復写像 \(T\) とポテンシャル \(I\) により閉路を裁く。
- **Unit 層（連続・回転・角度）**：円・回転・偏角 \(\theta\) を単位として扱う。
- **Bridge（橋）**：log/exp、作図（円と交点）、相似変換など。

以降の「交える／交えない」は、**どの層で同じ操作を共有できるか**の問いとして扱う。

### 0.1 Lean への接続（この資料が指す参照先）

この資料の「層」は、Lean 側ではおおむね次で受ける：

- Nat 層（反復・増分・閉路否定）
  - `import DkMath.UnitCycle.Core`
  - 代表定理：`no_nontrivial_cycle_of_ge_one`
- Nat 層の例（境界例・RelPolygon）
  - `import DkMath.UnitCycle.Examples`
- Bridge（Nat⇄Unit の最小接続の雛形）
  - `import DkMath.UnitCycle.CosmicBridge`
- Unit/作図層（白銀単位円の座標代数）
  - `namespace DkMath.SilverRatio.Circle`
  - 代表定理：`bcfg_concyclic : concyclic4 B C F G`

注意：Euler の等式（例：\(\exp(i\pi)+1=0\)）を Nat 層の閉路議論へ “そのまま” 入れるのは型違いであり、Bridge を通して観測値へ落とす、という方針が筋じゃ。

---

## 1. Nat 層：UnitCycle のコア定理群（閉路消滅）

### 1.1 反復とポテンシャル

- State : 型 `State`
- 遷移 : `T : State → State`
- ポテンシャル : `I : State → ℕ`
- 状態依存増分 : `g : State → ℕ`

### 1.2 1 以上増分なら閉路は無い

**仮定（単調増加）**
\[
\forall s,\ I(T(s)) \ge I(s)+1
\]

**結論（反復で少なくとも \(k\) 増える）**
\[
\forall k,s,\ I(T^{[k]}(s)) \ge I(s)+k
\]

**結論（非自明閉路の否定）**
\[
T^{[k]}(s)=s \Rightarrow k=0
\]

> Lean: `I_iterate_of_ge_one`, `no_nontrivial_cycle_of_ge_one`

### 1.3 状態依存増分（\(g(s)\ge 1\)）

**仮定**
\[
\forall s,\ 1\le g(s)\quad\wedge\quad I(T(s))\ge I(s)+g(s)
\]

**結論（閉路否定）**
\[
T^{[k]}(s)=s \Rightarrow k=0
\]

> Lean: `I_iterate_of_ge_g`, `no_nontrivial_cycle_of_ge_g`

### 1.4 総和版（Sum-of-increments）

**仮定**
\[
\forall s,\ I(T(s))\ge I(s)+g(s)
\]

**結論（増分総和による下界）**
\[
I(T^{[k]}(s))\ \ge\ I(s)+\sum_{i=0}^{k-1} g\bigl(T^{[i]}(s)\bigr)
\]

さらに \(g(s)\ge 1\) なら
\[
I(T^{[k]}(s))\ge I(s)+k
\]

> Lean: `I_iterate_ge_sum_g`, `I_iterate_ge_add_k`（および補助補題）

### 1.5 最小 Lean スケッチ（Nat 層：progress と cycle は両立しない）

この資料でいう「Nat 層で交えない」を、Lean で最小限に書くとこういう形になる。

```lean
import DkMath.UnitCycle.Core

namespace DkMath.DHNT

open DkMath.UnitCycle

def Progress {State : Type} (T : State → State) (I : State → Nat) : Prop :=
  ∀ s, I (T s) ≥ I s + 1

def HasCycle {State : Type} (T : State → State) : Prop :=
  ∃ s k, k > 0 ∧ iterate T k s = s

theorem not_hasCycle_of_progress {State : Type} {T : State → State} {I : State → Nat}
  (hP : Progress T I) : ¬ HasCycle T := by
  intro hC
  rcases hC with ⟨s, k, hkpos, hk⟩
  have hk0 : k = 0 :=
    no_nontrivial_cycle_of_ge_one (State := State) (T := T) (I := I) hP k s hk
  exact (Nat.ne_of_gt hkpos) hk0

end DkMath.DHNT
```

この形が一度立てば、「\(\pi\) 的＝閉路」「\(e\) 的＝単位増分」という翻訳は、Nat 層の内部だけで矛盾として裁けるようになる。

---

## 2. Unit 層：回転単位と Euler の公式

### 2.1 公式の層

Euler の等式
\[
 e^{i\theta}=\cos\theta+i\sin\theta
\]
は **Unit 層（回転・角度）**の言語であり、Nat 層の反復増分とは別物。

- \(\theta\in\mathbb R\) は連続単位（偏角）で「無限の種類の単位系」を与える。
- \(\pi\) は「回転（1周）」という単位の定数として現れる。

### 2.2 族としての一致（Unit 層では Yes）

\[
 e^k=\pi\iff k=\ln\pi
\]

これは **指数パラメータ \(k\)** を動かすだけで一致点が存在するという事実。
ただしこれは **連続族**の話であり、Nat 層の \(k\in\mathbb N\) 反復とは別。

---

## 3. Bridge：円は整数点と根号点を同居させる

### 3.1 白銀単位円（実装済み：concyclic の証明）

SilverRatio.Circle では、点

- \(B=(1,0)\), \(C=(1,1)\)（整数格子点：単位正方形）
- \(F=(0,\sqrt2)\), \(G=(-1/\sqrt2,\ 1/\sqrt2)\)（\(\sqrt2\) を含む点）

が **同一円周上に乗る**ことを示す。

> Lean: `bcfg_concyclic : concyclic4 B C F G`

中心は
\[
O=\left(\frac{\sqrt2-1}{2},\frac12\right)
\]
で、\(\sqrt2\) の「ずれ」を含みつつ、整数点 \(B,C\) と同一円周に整合する。

### 3.2 意味（橋の最小実例）

- Nat 層（整数格子点）と
- Unit/作図層（根号点）

が、**円（回転の器）**の上で同居できることを “座標代数で確定” した例。

これは「円周上の座標が、整数と無理数（根号）を生む」という観測の最小モデルである。

---

## 4. 作図世界：\(\sqrt2\to\sqrt3\to\sqrt6\to 3\)

作図可能数は（原点と単位長からの定規・コンパス作図で）

- 四則演算に閉じ、
- 平方根に閉じる。

よって \(\sqrt2,\sqrt3\) が得られるなら
\[
\sqrt6=\sqrt{2\cdot 3}
\]
も得られ、さらに
\[
(\sqrt3)^2=3
\]
により整数へ戻るルートも存在する。

この「交点ルート」「比として抽出」は、数の側では
\[
\mathbb Q(\sqrt2,\sqrt3)
\]
の閉性（構成可能体）として整理できる。

---

## 5. reddit 的問いへの回答（層の違い）

「\(\pi\) と \(e\) は交えるか？」を層で言い換える：

- **Unit 層（連続パラメータ）**：
  \(e^k=\pi\) は \(k=\ln\pi\) で成立（族として包含）。

- **Nat 層（離散反復）**：
  反復増分モデルで「閉じる」には増分が 0 相当（単位不足が無い）である必要があり、
  \(g\ge 1\) の世界では閉路が消える（UnitCycle 定理）。
  よって、同じ反復単位の中で \(\pi\) と \(e\) を “同一閉路” として交えるのは不可能。

結論：

- 連続族（Unit 層）では **Yes（パラメータ調整で一致点）**
- 離散反復（Nat 層）では **No（閉路が成立しない）**

この二層回答が、議論の混線を断つ。

---

## 6. 実装ロードマップ（次のコミット候補）

### 6.1 SilverRatio.Circle の「白銀単位円」定義化

現状：`concyclic4` で存在円を示す。

次：

- `OnCircle (O : Point) (r2 : ℝ) (P : Point) : Prop := dist_sq O P = r2`
- `WhiteSilverCircle : Set Point := {P | OnCircle O r2 P}`
- `B,C,F,G ∈ WhiteSilverCircle`

として「円そのもの」を概念として立てる。

### 6.2 円周有理点（パラメータ化）との接続

単位円の有理点：
\[
(x,y)=\left(\frac{1-t^2}{1+t^2},\ \frac{2t}{1+t^2}\right),\ t\in\mathbb Q
\]

を “別生成法” として並べ、

- 有理生成（整数比）
- 作図生成（根号）

が同じ円に載ることを「橋」として明記する。

### 6.3 DHNT 観点の宣言（層の固定）

- Euler の公式は Unit 層（単位側）
- UnitCycle は Nat 層（自然数側）

という層宣言を README/論文の前提として固定する。

---

## Appendix: 記号

- `iterate T k s` / `T^[k] s` : \(k\) 回反復
- `dist_sq` : 距離の二乗（平方根を避ける）
- \(u_{\rm Ag}=(1+\sqrt2)/2\) : 白銀単位

---

## Reference (Lean modules)

- `DkMath.UnitCycle.Core` : Nat 層（閉路消滅・総和下界）
- `DkMath.UnitCycle.Examples` : 境界例（u>0 / u=0 / swap / spike / RelPolygon 等）
- `DkMath.SilverRatio.Circle` : 白銀単位円（座標代数）
