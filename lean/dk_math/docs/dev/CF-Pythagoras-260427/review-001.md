# review

おお、ビルド OK ✅️
これは良い一歩じゃ、D.！

これで少なくとも、以下の骨格は Lean 側で **実体化済み** になったわけじゃな。

$$
a=\alpha u_1,\qquad b=\beta u_2,\qquad c=\gamma u_3
$$

から

$$
\alpha^2u_1^2+\beta^2u_2^2=\gamma^2u_3^2
$$

を通じて

$$
a^2+b^2=c^2
$$

へ降りる道筋。さらに、

$$
c^2-a^2=2a(c-a)+(c-a)^2
$$

という **境界差生成式** まで Lean 上に置けた。
これはもう、単なるメモではなく、宇宙式ピタゴラス橋の第一基礎 API じゃ。

次の一手は、わっちならこの順に進める。

## 1. `Examples.lean`

まず (3,4,5) を置く。

$$
3^2+4^2=5^2
$$

を単なる例ではなく、

$$
a=\alpha u_1,\quad b=\beta u_2,\quad c=\gamma u_3
$$

の観測辺として通す。
最小例は

$$
u_1=u_2=u_3=1,\qquad \alpha=3,\quad \beta=4,\quad \gamma=5
$$

じゃな。

つまり Lean では、

```lean
example : linkCondition (3 : ℤ) 4 5 1 1 1 := by
  norm_num
```

のような入口を作れる。

## 2. 一般ピタゴラス三つ組

次に

$$
a=m^2-n^2,\qquad b=2mn,\qquad c=m^2+n^2
$$

を API に流す。

Lean では最初から自然数で行くと引き算が厄介なので、まずは `ℤ` か一般 `CommRing` 上で

$$
(m^2-n^2)^2+(2mn)^2=(m^2+n^2)^2
$$

を `ring` で閉じるのがよい。

```lean
example (m n : ℤ) :
    (m^2 - n^2)^2 + (2*m*n)^2 = (m^2 + n^2)^2 := by
  ring
```

これは宇宙式ピタゴラス API の試験石になる。

## 3. `Triple.lean`

そのあとに bundled 化じゃ。

```lean
structure CosmicPythagoreanTriple (R : Type*) [LinearOrderedRing R] where
  α : R
  β : R
  γ : R
  u₁ : R
  u₂ : R
  u₃ : R
```

そして

```lean
def a (T : CosmicPythagoreanTriple R) : R := T.α * T.u₁
def b (T : CosmicPythagoreanTriple R) : R := T.β * T.u₂
def c (T : CosmicPythagoreanTriple R) : R := T.γ * T.u₃
```

を生やす。
これで研究ノート側の言葉に近い形で、

```lean
T.Linked
```

から

```lean
T.a^2 + T.b^2 = T.c^2
```

へ行ける。

## 4. 今回閉じた意味

今回の成果は、小さいようで大きい。
なぜなら、ピタゴラスの定理を

$$
a^2+b^2=c^2
$$

という完成形ではなく、

$$
u_i,\quad K_i=u_i^2,\quad \delta_{ca}=c-a
$$

を持つ **生成構造** として扱う入口が Lean 上に置けたからじゃ。

これは今後、

$$
(X+u)^2-X^2=2Xu+u^2
$$

や

$$
(x+u)^2-x(x+2u)=u^2
$$

との橋を張るための、ちょうどよい足場じゃよ。
よくやった。これは確かに一区切りじゃ。
