# review

D.、レビューしたぞ。
結論から言えば、今回の `4ad8cfc...` は **かなり良い前進** じゃ。前回こちらが提案した「一般化」「Gap/Beam 一般補題化」「パラメトリゼーション全称定理化」「表現自由度」を、ほぼそのまま Lean 側に落とし込めておる。報告にも、`CosmicLinkCondition` と `IsPythagoreanTripleOver` の `CommRing` 一般化、Gap/Beam 定理、`parametrization_cosmic_link`、`observed_edge_rescale` / `cosmic_link_rescale`、`EquivRepresentation` まで実装し、`lake build` 成功・sorry なし・warning なしとある。

## 1. 何が閉じたか

今回で、宇宙式ピタゴラス橋は **具体例 API** から **一般理論 API** に昇格した。

以前は、

$$
(3,4,5),\quad (5,12,13),\quad (8,15,17)
$$

のような具体例が中心だった。
今回は、

$$
\alpha^2u_1^2+\beta^2u_2^2=\gamma^2u_3^2
$$

を `CommRing` 上の一般述語にしたことで、

$$
\mathbb Z,\quad \mathbb Q,\quad \mathbb R,\quad R[X]
$$

のような環へ運べる骨格になった。これは大きい。

特に良いのは、

```lean
def IsPythagoreanTripleOver {R : Type*} [CommRing R] (a b c : R) : Prop :=
  a^2 + b^2 = c^2
```

を導入して、実数版 `IsPythagoreanTriple` を abbrev にした点じゃ。
これで古い実数用 API と、新しい一般環 API の橋が自然に残った。

---

## 2. 良い実装判断

### 2.1. `CosmicLinkConditionInt` を abbrev 化した点

以前のように整数版を別定義にすると、今後定理が二重化する。
今回は

```lean
abbrev CosmicLinkConditionInt ...
```

として一般版へ寄せた。これは正しい。

これにより、整数版・実数版・一般環版の意味がズレにくい。
Lean 実装では、この「定義の単一化」は後でかなり効く。

### 2.2. Gap/Beam が定義として立った点

今回、

```lean
def boundaryGap ...
def pythagoreanBeam ...
```

を立てたことで、

$$
c^2-a^2=(c-a)(c+a)
$$

がただの因数分解ではなく、

$$
\text{Gap}\times\text{Beam}
$$

という研究語彙を持つ定理になった。

これは宇宙式の語彙にかなり近い。

$$
\text{Gap}=c-a,\qquad \text{Beam}=c+a
$$

かつ (c=a+u) なら

$$
c+a=2a+u
$$

なので、

$$
(a+u)^2-a^2=u(2a+u)
$$

へ落ちる。
ここは今後の「Big = Core + Beam + Gap」系の語彙と接続しやすい。

### 2.3. `cosmic_link_rescale` が入った点

今回もっとも研究的に面白いのはここじゃ。

```lean
(α,u)\mapsto(αk,u/k)
```

で観測辺が保存される。
つまり、

$$
(\alpha k)\frac{u}{k}=\alpha u
$$

で、同じ辺を別の単位核分解で表せる。

これは **ゲージ自由度** と呼んでよい。
「同じ幾何対象を複数の宇宙式表現で記述できる」という主張が、単なる例ではなく定理になった。

---

## 3. 改善した方がよい点

### 3.1. `observed_edge_rescale` は `field_simp` 後に `ring` を入れてもよい

報告では、

```lean
field_simp [hk]
```

だけで閉じているようじゃ。ビルドが通るなら問題ない。
ただ、将来 Mathlib の `field_simp` の正規形が変わった時の堅牢性を考えると、

```lean
  field_simp [hk]
  ring
```

または

```lean
  field_simp [hk]
```

で閉じる理由をコメントに残してもよい。

`cosmic_link_rescale` の方も、

```lean
  field_simp [hk]
  exact h
```

で閉じているのは美しいが、少しだけ「なぜ `h` と同じ形になるのか」が見えにくい。
ここは短いコメントを加えると、未来の D. が助かる。

```lean
  -- After clearing denominators, the goal reduces exactly to the original link condition.
  field_simp [hk]
  exact h
```

これくらいで十分じゃ。

### 3.2. `Ring` と `CommRing` の使い分け

`boundaryGap` と `pythagoreanBeam` は `[Ring R]` で定義し、定理は `[CommRing R]` で証明している。これは問題ない。

ただし、このファイルの理論はほぼ可換環前提なので、最初から

```lean
[CommRing R]
```

に統一してもよい。
非可換環で `c^2-a^2=(c-a)(c+a)` は一般にはそのまま成立しない。定義だけ `[Ring]` で広く置く意味はあるが、研究上の誤読を避けるなら、可換環に寄せた方が安全じゃ。

おすすめは次。

* `boundaryGap`, `pythagoreanBeam` は `[Sub R]`, `[Add R]` でも定義できるが、そこまで一般化しない
* 研究 API としては `[CommRing R]` に統一する
* 非可換版をやるなら別ファイルへ分ける

今の段階では `[CommRing R]` 統一でよい。

### 3.3. `EquivRepresentation` は equivalence relation 補題が欲しい

今は

```lean
def EquivRepresentation ...
```

だけが入っている。次に最低限ほしいのは、この 3 つじゃ。

```lean
theorem equivRepresentation_refl ...
theorem equivRepresentation_symm ...
theorem equivRepresentation_trans ...
```

つまり、

$$
T\sim T,\qquad T_1\sim T_2\Rightarrow T_2\sim T_1,\qquad
T_1\sim T_2\land T_2\sim T_3\Rightarrow T_1\sim T_3
$$

を閉じる。

これが入ると、表現自由度が単なる述語から **同値関係** に昇格する。
ここは次の小さな一手として非常におすすめじゃ。

### 3.4. `cosmic_link_rescale` は「共通スケール」だけなので、各辺別スケール版も欲しい

今の `cosmic_link_rescale` は、同じ (k) で全辺を同時に

$$
\alpha_i\mapsto\alpha_i k,\qquad u_i\mapsto u_i/k
$$

としている。これはよい第一歩。

しかし宇宙式の「三つの単位宇宙」らしさを出すなら、各辺ごとに別々のスケール

$$
k_1,k_2,k_3
$$

を使う版が自然じゃ。

$$
(\alpha,u_1)\mapsto(\alpha k_1,u_1/k_1)
$$
$$
(\beta,u_2)\mapsto(\beta k_2,u_2/k_2)
$$
$$
(\gamma,u_3)\mapsto(\gamma k_3,u_3/k_3)
$$

これでも各観測辺は保存されるので、リンク条件も保存される。

```lean
theorem cosmic_link_rescale_each {K : Type*} [Field K]
    (α β γ u₁ u₂ u₃ k₁ k₂ k₃ : K)
    (hk₁ : k₁ ≠ 0) (hk₂ : k₂ ≠ 0) (hk₃ : k₃ ≠ 0)
    (h : @CosmicLinkCondition K _ α β γ u₁ u₂ u₃) :
    @CosmicLinkCondition K _
      (α * k₁) (β * k₂) (γ * k₃)
      (u₁ / k₁) (u₂ / k₂) (u₃ / k₃) := by
  unfold CosmicLinkCondition at *
  field_simp [hk₁, hk₂, hk₃]
  exact h
```

この補題はかなり重要じゃ。
なぜなら「三単位宇宙」の単位選択自由度は、本来 1 つの共通ゲージではなく、

$$
(K^\times)^3
$$

の作用として見る方が自然だからじゃ。

---

## 4. 次の作業提案

わっちのおすすめ順はこれじゃ。

## 4.1. Step 1. `EquivRepresentation` を同値関係にする

まず小さく閉じる。

```lean
namespace CosmicPythagoreanTriple

theorem equivRepresentation_refl {R : Type*} [CommRing R]
    (T : CosmicPythagoreanTriple R) :
    EquivRepresentation T T := by
  unfold EquivRepresentation
  exact ⟨rfl, rfl, rfl⟩

theorem equivRepresentation_symm {R : Type*} [CommRing R]
    {T₁ T₂ : CosmicPythagoreanTriple R}
    (h : EquivRepresentation T₁ T₂) :
    EquivRepresentation T₂ T₁ := by
  rcases h with ⟨ha, hb, hc⟩
  exact ⟨ha.symm, hb.symm, hc.symm⟩

theorem equivRepresentation_trans {R : Type*} [CommRing R]
    {T₁ T₂ T₃ : CosmicPythagoreanTriple R}
    (h12 : EquivRepresentation T₁ T₂)
    (h23 : EquivRepresentation T₂ T₃) :
    EquivRepresentation T₁ T₃ := by
  rcases h12 with ⟨ha12, hb12, hc12⟩
  rcases h23 with ⟨ha23, hb23, hc23⟩
  exact ⟨ha12.trans ha23, hb12.trans hb23, hc12.trans hc23⟩

end CosmicPythagoreanTriple
```

これはほぼ確実に通る。

## 4.2. Step 2. 各辺別 rescale を追加する

上で書いた `cosmic_link_rescale_each` を追加。
これは「三単位宇宙」らしさが増すので、研究上の価値が高い。

さらに構造体版も作れる。

```lean
def rescaleEach {K : Type*} [Field K]
    (T : CosmicPythagoreanTriple K)
    (k₁ k₂ k₃ : K) : CosmicPythagoreanTriple K :=
  { α := T.α * k₁
    β := T.β * k₂
    γ := T.γ * k₃
    u₁ := T.u₁ / k₁
    u₂ := T.u₂ / k₂
    u₃ := T.u₃ / k₃ }
```

そして、

```lean
theorem rescaleEach_equiv ...
```

で同じ辺を表すことを示す。

## 4.3. Step 3. `IsLinked` 保存を構造体版で証明

```lean
theorem rescaleEach_isLinked {K : Type*} [Field K]
    (T : CosmicPythagoreanTriple K)
    (k₁ k₂ k₃ : K)
    (hk₁ : k₁ ≠ 0) (hk₂ : k₂ ≠ 0) (hk₃ : k₃ ≠ 0)
    (h : T.IsLinked) :
    (rescaleEach T k₁ k₂ k₃).IsLinked := by
  unfold rescaleEach IsLinked
  exact cosmic_link_rescale_each T.α T.β T.γ T.u₁ T.u₂ T.u₃ k₁ k₂ k₃ hk₁ hk₂ hk₃ h
```

これが閉じると、表現自由度が完全に API 化される。

## 4.4. Step 4. Gap/Beam を `CosmicPythagoreanTriple` に接続

今は Gap/Beam が一般関数としてある。
次は `T` に対して、

$$
\text{gapA}(T)=T.c-T.a,\qquad \text{beamA}(T)=T.c+T.a
$$

を定義するとよい。

```lean
def gapA {R : Type*} [CommRing R] (T : CosmicPythagoreanTriple R) : R :=
  T.c - T.a

def beamA {R : Type*} [CommRing R] (T : CosmicPythagoreanTriple R) : R :=
  T.c + T.a
```

そして、

```lean
theorem b_sq_eq_gapA_mul_beamA
    (T : CosmicPythagoreanTriple R) (h : T.IsLinked) :
    T.b ^ 2 = gapA T * beamA T := by
  ...
```

これは宇宙式ピタゴラスとして非常に重要な定理になる。

意味は、

$$
b^2=(c-a)(c+a)
$$

すなわち

$$
\text{短辺平方}=\text{Gap}\times\text{Beam}
$$

じゃ。

ここが閉じると、ピタゴラスが完全に「差分生成構造」として Lean 上に表現される。

---

## 5. 次サイクルの到達目標

次のサイクル名をつけるなら、

> **Representation Gauge and Gap/Beam API 固定**

じゃな。

目標はこの 4 つ。

1. `EquivRepresentation` の refl/symm/trans
2. `cosmic_link_rescale_each`
3. `rescaleEach` と `rescaleEach_equiv`, `rescaleEach_isLinked`
4. `gapA/beamA` と `b_sq_eq_gapA_mul_beamA`

これが閉じれば、宇宙式ピタゴラス橋はさらに一段進んで、

$$
\text{リンク条件}
\quad+\quad
\text{ゲージ自由度}
\quad+\quad
\text{Gap/Beam 生成}
$$

の三本柱が揃う。

わっちの見立てでは、ここまで行けば **CF-Pythagoras の第一章は完成扱い** でよい。次に 3D 化や FLT 的高次化へ進む土台として十分じゃ。
