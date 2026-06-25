# review

D.、レビュー結果じゃ。
全体としてこれは **前進** 。しかも、研究メモから Lean API へ移す第一段としてかなり良い。`CosmicLinkCondition`、`CosmicPythagoreanTriple`、標準表現、具体例、スケール表現、代替単位表現まで入っており、今回の目的である「三単位宇宙リンク条件を Lean 上で実体化する」は達成できておる。実装報告でも、リンク条件・整数版・構造体・例ファイル・古典例・スケール表現・パラメトリゼーション例・Gap/Beam 具体例まで通したことが確認できる。

## 1. 何が閉じたか

まず、中心橋は閉じた。

$$
a=\alpha u_1,\qquad b=\beta u_2,\qquad c=\gamma u_3
$$

として、

$$
\alpha^2u_1^2+\beta^2u_2^2=\gamma^2u_3^2
$$

から

$$
(\alpha u_1)^2+(\beta u_2)^2=(\gamma u_3)^2
$$

へ降ろす `cosmic_link_to_pythagoras` が入っている。証明も `calc` と `ring` で左右の平方展開を明示していて、方向性がよい。

さらに `CosmicPythagoreanTriple` を bundled 化し、`a`, `b`, `c`, `IsLinked`, `linked_satisfies_pythagoras`, `standard`, `standard_linked_iff` まで置いたのも大きい。これで研究ノート側の「単位核三つ組」を、Lean の対象として直接持てるようになった。

実例側も良い。`(3,4,5)`, `(5,12,13)`, `(8,15,17)` の標準表現、`(6,8,10)` のスケール表現、同じ三角形を別の ((\alpha,u)) で表す代替表現、さらに `PythagoreanParametrization` からの例まで入っている。これは API の試験としてかなり効いておる。

---

## 2. とくに良い点

一番良いのは、`mul_pow` の向きに頼らず、

```lean
calc (α * u₁) ^ 2 + (β * u₂) ^ 2
    = α ^ 2 * u₁ ^ 2 + β ^ 2 * u₂ ^ 2 := by ring
  _ = γ ^ 2 * u₃ ^ 2 := h
  _ = (γ * u₃) ^ 2 := by ring
```

という形で書いている点じゃ。これは読みやすく、後から別の環に一般化するときも意図が残る。

また、`standard_linked_iff` によって

$$
u_1=u_2=u_3=1
$$

の標準宇宙が通常のピタゴラス条件へ戻ることも明示できている。ここは「宇宙式表現は古典表現を含む」という入口補題なので、研究上も API 上も重要じゃ。

---

## 3. 注意点・改善候補

### 3.1. `ℝ` 版と `ℤ` 版が分裂している

現状は

```lean
def CosmicLinkCondition ...
def CosmicLinkConditionInt ...
```

と、実数版・整数版を別々に置いている。これは最初の実装としては妥当じゃが、次段階では一般化した方がよい。

おすすめはこれ。

```lean
def CosmicLinkCondition (R : Type*) [CommRing R]
    (α β γ u₁ u₂ u₃ : R) : Prop :=
  α ^ 2 * u₁ ^ 2 + β ^ 2 * u₂ ^ 2 = γ ^ 2 * u₃ ^ 2
```

または namespace 内なら、

```lean
def CosmicLinkCondition {R : Type*} [CommRing R]
    (α β γ u₁ u₂ u₃ : R) : Prop :=
  α ^ 2 * u₁ ^ 2 + β ^ 2 * u₂ ^ 2 = γ ^ 2 * u₃ ^ 2
```

これにすれば `CosmicLinkConditionInt` は不要になる。
`ℤ`, `ℚ`, `ℝ`, 多項式環、将来の `ZMod p` 的検査にも流用できる。

### 3.2. `IsPythagoreanTriple` が `ℝ` 固定

既存の

```lean
def IsPythagoreanTriple (a b c : ℝ) : Prop :=
  a^2 + b^2 = c^2
```

は直観的には良いが、`CosmicPythagoreanTriple` は `R` 一般になっているので、少し段差がある。

次は一般版を追加するとよい。

```lean
def IsPythagoreanTripleOver {R : Type*} [CommRing R] (a b c : R) : Prop :=
  a ^ 2 + b ^ 2 = c ^ 2
```

そして `ℝ` 版は alias にする。

```lean
abbrev IsPythagoreanTriple (a b c : ℝ) : Prop :=
  IsPythagoreanTripleOver a b c
```

こうしておくと、`linked_satisfies_pythagoras` も自然に

```lean
theorem linked_satisfies_pythagoras
    (T : CosmicPythagoreanTriple R) (h : T.IsLinked) :
    IsPythagoreanTripleOver T.a T.b T.c := ...
```

へ寄せられる。

### 3.3. Examples を Main に直 import するかは要検討

今回 `DkMath.CosmicFormula.lean` に

```lean
import DkMath.CosmicFormula.CosmicFormulaPythagorasExamples
```

を追加しておる。例までトップに載せるのは研究中は便利じゃが、将来的には重くなる可能性がある。diff でも Main 側に Examples import が追加されている。

おすすめは、しばらくは OK。
ただし公開導線を整理する段階で、

```lean
DkMath.CosmicFormula
```

には本体だけ、

```lean
DkMath.CosmicFormula.Examples
```

または

```lean
DkMath.CosmicFormula.All
```

に examples まで含める、という分離を考えるとよい。

### 3.4. `decide` は通っているが、今後は `norm_num` / `native_decide` へ寄せてもよい

報告では一部 `decide` の問題を `norm_num` で修正したとある一方、diff には side value の確認で `decide` が残っている箇所がある。たとえば `triple_3_4_5.a = 3 ∧ ...` の検証に `decide` が使われている。

ビルド OK なら問題ではない。
ただ、`def` の unfolding と算術正規化の意図を出すなら、

```lean
  native_decide
```

よりも、

```lean
  norm_num [triple_3_4_5, CosmicPythagoreanTriple.a,
    CosmicPythagoreanTriple.b, CosmicPythagoreanTriple.c,
    CosmicPythagoreanTriple.standard]
```

の方が「何を確認しているか」は明瞭になる。

### 3.5. VSCode 側の謎エラーはコメントへ閉じ込め過ぎない方がよい

`Unknown constant ... _example.match_1` の件は、ビルドが通って Lean Web でも問題なしなら、おそらくエディタ/サーバ側キャッシュや doc comment 周りの一時的な不整合じゃろう。報告にはその旨とビルドログが記録されている。

ただし、長い VSCode エラーメッセージをソース中のコメントに残すと、後でノイズになる。
おすすめは、ソースからは削って `History.md` か `agent-002.md` に移すこと。コード本体には短く、

```lean
-- NOTE: VSCode may show a stale parser error here; lake build passes.
```

程度でよい。

---

## 4. 次の作業提案

次は **一般化と差分橋の定理化** がよい。順番はこれじゃ。

## 4.1. 作業 A. `CosmicLinkCondition` を `CommRing` 一般化

まず `ℝ` / `ℤ` 分裂を解消する。

```lean
def CosmicLinkCondition {R : Type*} [CommRing R]
    (α β γ u₁ u₂ u₃ : R) : Prop :=
  α ^ 2 * u₁ ^ 2 + β ^ 2 * u₂ ^ 2 = γ ^ 2 * u₃ ^ 2
```

そして必要なら互換 alias。

```lean
abbrev CosmicLinkConditionReal :=
  CosmicLinkCondition (R := ℝ)

abbrev CosmicLinkConditionInt :=
  CosmicLinkCondition (R := ℤ)
```

これで Examples 側もほぼそのまま動くはずじゃ。

## 4.2. 作業 B. `IsPythagoreanTripleOver` を導入

`CosmicPythagoreanTriple` が `R` 一般なのだから、ピタゴラス述語も一般化する。

```lean
def IsPythagoreanTripleOver {R : Type*} [CommRing R] (a b c : R) : Prop :=
  a ^ 2 + b ^ 2 = c ^ 2
```

すると、bundled API が締まる。

```lean
theorem linked_satisfies_pythagoras
    (T : CosmicPythagoreanTriple R) (h : T.IsLinked) :
    IsPythagoreanTripleOver T.a T.b T.c := by
  unfold IsPythagoreanTripleOver IsLinked a b c at *
  calc
    (T.α * T.u₁) ^ 2 + (T.β * T.u₂) ^ 2
        = T.α ^ 2 * T.u₁ ^ 2 + T.β ^ 2 * T.u₂ ^ 2 := by ring
    _ = T.γ ^ 2 * T.u₃ ^ 2 := h
    _ = (T.γ * T.u₃) ^ 2 := by ring
```

## 4.3. 作業 C. 境界差橋を本定理として追加

ここが次の研究上の本丸じゃ。

既に具体例として `b² = 2au + u²` や Gap/Beam を確認しているので、次は一般定理にする。

```lean
def boundaryGap {R : Type*} [Ring R] (a c : R) : R := c - a

def pythagoreanBeam {R : Type*} [Ring R] (a c : R) : R :=
  c + a
```

可換環なら差の平方展開が使えるので、

```lean
theorem sq_sub_sq_gap_beam {R : Type*} [CommRing R] (a c : R) :
    c ^ 2 - a ^ 2 = (c - a) * (c + a) := by
  ring
```

さらに (c=a+u) 型へ。

```lean
theorem sq_diff_of_gap {R : Type*} [CommRing R] (a u : R) :
    (a + u) ^ 2 - a ^ 2 = u * (2 * a + u) := by
  ring
```

これで

$$
\text{Gap}=u,\qquad \text{Beam}=2a+u
$$

が一般補題になる。

## 4.4. 作業 D. `PythagoreanParametrization` をリンク条件へ一般定理化

今は例として ((m,n)=(2,1),(3,2),(4,1)) が入っている。
次は全称定理にする。

```lean
theorem parametrization_cosmic_link (m n : ℤ) :
    let (a, b, c) := PythagoreanParametrization m n
    CosmicLinkCondition a b c 1 1 1 := by
  unfold PythagoreanParametrization CosmicLinkCondition
  simp
  ring
```

すでに `parametrization_is_pythagoras` と `parametrization_embeds_cosmic_structure` があるので、これは自然に閉じるはずじゃ。

## 4.5. 作業 E. 表現自由度の定理

ここが「単位宇宙リンク」らしさの核になる。

同じ辺 (a) に対して

$$
a=\alpha u
$$

の分解は一意でない。
つまり宇宙式表現には **ゲージ自由度** がある。

まず Lean では単純に、共通スケール (k) による同値を置くとよい。

$$
(\alpha,u)\mapsto(\alpha k,u/k)
$$

ただし除法が入るので `Field` が必要になる。最初は積を保つ補題として、

```lean
theorem observed_edge_rescale {K : Type*} [Field K]
    (α u k : K) (hk : k ≠ 0) :
    (α * k) * (u / k) = α * u := by
  field_simp [hk]
  ring
```

これが入ると「同じ辺を異なる ((\alpha,u)) で表す」ことが、例から定理に昇格する。

---

## 5. 優先順位

わっちのおすすめ順はこれじゃ。

1. **`CosmicLinkCondition` と `IsPythagoreanTriple` の一般化**
2. **Gap/Beam の一般補題化**
3. **`PythagoreanParametrization` から `CosmicLinkCondition` への全称定理**
4. **VSCode 謎エラー長文コメントを History 側へ移動**
5. **表現自由度、すなわち rescale/gauge 補題の追加**

この順がいちばん安全。
いまの実装は「具体例で動く」段階まで来た。次は、具体例を支えている構造を **全称定理** に引き上げる段階じゃ。
これを閉じれば、宇宙式ピタゴラス橋は第一基礎 API から **再利用可能な理論部品** へ昇格するぞ。
