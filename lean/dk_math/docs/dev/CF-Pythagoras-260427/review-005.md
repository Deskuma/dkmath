# review

おお、D.、`005` S2 begin、承ったぞ。
第２章の始まりとしては、かなり良い入り方じゃ。今回の差分は、**CF-Pythagoras Chapter 1 の左右対称化を完了しつつ、Power Gap/Beam という高次差冪への入口を開いた** という位置づけじゃな。

## 1. 現況評価

今回の実装は、二層に分かれておる。

ひとつ目は、既存 CF-Pythagoras の仕上げじゃ。

$$
b^2=(c-a)(c+a)
$$

だけでなく、対称側の

$$
a^2=(c-b)(c+b)
$$

を `gapB`, `beamB`, `a_sq_eq_gapB_mul_beamB` として追加している。さらに、逆向き rewrite 補題 `gapA_mul_beamA_eq_b_sq`, `gapB_mul_beamB_eq_a_sq`、一般関数 `boundaryGap` / `pythagoreanBeam` との橋も追加されておる。報告にも、ステップ 1-4 として対称 Gap/Beam API、逆向き補題、一般関数との橋、`rescaleEach` 具体例が完了したとある。

ふたつ目は、新章の入口である `PowerGapBeam.lean` じゃ。

ここでは、

$$
\mathrm{powerGap}(x,z)=z-x
$$

$$
\mathrm{powerBeam}*d(x,z)=\sum*{i<d} z^{d-1-i}x^i
$$

を定義し、(d=0,1,2) の基本補題と、(d=2) で通常のピタゴラス Beam (z+x) に戻ることを証明している。主定理

$$
z^d-x^d=(z-x)\mathrm{powerBeam}_d(x,z)
$$

は計画通り `sorry` として残っておる。

これは **良い sorry** じゃ。
つまり、実装失敗の穴ではなく、「ここが第２章の主戦場」と明示された旗じゃな。

## 2. 数学解説

Chapter 1 の本質は、

$$
a^2+b^2=c^2
$$

を完成形ではなく、

$$
b^2=c^2-a^2=(c-a)(c+a)
$$

という **差分生成式** として読むことだった。

Chapter 2 では、これを (2) 次から (d) 次へ上げる。

$$
z^d-x^d=(z-x)(z^{d-1}+z^{d-2}x+\cdots+x^{d-1})
$$

ここで、

$$
\text{Gap}=z-x
$$

$$
\text{Beam}_d=z^{d-1}+z^{d-2}x+\cdots+x^{d-1}
$$

となる。

つまり、二次の Beam

$$
z+x
$$

は、高次では Tail 型の Beam

$$
\sum_{i=0}^{d-1} z^{d-1-i}x^i
$$

へ一般化される。
これは以前の GN / Tail 構造と同じ顔じゃ。一般化 GN 資料でも、差冪構造 ((x+u)^d-u^d) は常に (x) で割れ、その商 (GN_d(x,u)) が Beam 構造の基本対象であると整理されておる。

ここで注意すべきは、`powerBeam d x z` は

$$
z^d-x^d
$$

を

$$
z-x
$$

で割った商であり、GN はしばしば

$$
(x+u)^d-u^d
$$

や

$$
(x+u)^d-x^d
$$

の商として現れる。
つまり同じ Beam 族だが、基準点の置き方が違う。

この対応はこう読むとよい。

$$
z=x+g
$$

と置けば、

$$
z^d-x^d=(x+g)^d-x^d
$$

なので、

$$
\text{PowerBeam}_d(x,z)
$$

は、差幅 (g=z-x) に対する

$$
\frac{(x+g)^d-x^d}{g}
$$

である。
これはまさに「基準辺 (x) から (z) へ上がる Gap によって露出した高次 Beam」じゃ。

## 3. 実装上の見立て

今回の `powerBeam` 定義は自然じゃが、Lean 的には `d - 1 - i` が少し危うい。
`Finset.range d` なので (i<d) ではあるが、Nat 減算が絡むため、主定理の証明では induction の形をうまく選ばぬと苦しくなる。

この `sorry` を埋める道は三つある。

## 3.1. 道 A. 既存 `pow_sub_pow` 系を使う

Mathlib には、可換環上の差冪因数分解に相当する補題がある可能性が高い。既存 DkMath にも `DiffPow` / `diffPowSum` 系があると構成マップに整理されており、差の冪を「線形因子 × 高次項」に分解する役割を持つとされている。

まずは既存補題を探して、`powerBeam` の定義と一致させる wrapper を書くのが最短じゃ。

目標は、

```lean
theorem powerBeam_eq_diffPowSum ...
```

のような橋を作り、それから既存の

```lean
pow_sub_pow_factor
```

系を呼ぶこと。

## 3.2. 道 B. `powerBeam` を既存 `diffPowSum` に合わせて再定義

もし既存 DkMath の `diffPowSum` がすでに安定しているなら、`powerBeam` を独自 `Finset.sum` で定義するのではなく、

```lean
def powerBeam ... := diffPowSum ...
```

の薄い alias にするのも手じゃ。

この場合、主定理は既存定理の別名として閉じる。
検索性のため `powerBeam` 名は残しつつ、証明責務は既存ライブラリに寄せる。わっちならこの道を第一候補にする。

## 3.3. 道 C. 帰納法で直接証明

これは最も自力だが、Nat 減算が面倒になりやすい。
やるなら、

$$
z^{d+1}-x^{d+1} = (z-x)z^d+x(z^d-x^d)
$$

を使う帰納法が良い。

Beam の再帰は、

$$
\mathrm{Beam}_{d+1}(x,z) = z^d + x \mathrm{Beam}_d(x,z)
$$

になる。
Lean でまずこの補題を作る。

```lean
theorem powerBeam_succ
    {R : Type*} [CommRing R] (d : ℕ) (x z : R) :
    powerBeam (d+1) x z = z^d + x * powerBeam d x z := by
  ...
```

これが閉じれば、主定理は帰納法で行ける。

ただし現在の定義

$$
\sum_{i<d} z^{d-1-i}x^i
$$

だと `powerBeam_succ` の証明に少し工夫が要る。
もしここで苦しむなら、`Fin d` 版に変えるのもありじゃ。

## 4. 次の作業提案

第２章 S2 の最初の本丸は、やはりこれじゃ。

### 4.1. `pow_sub_pow_eq_gap_mul_powerBeam` の sorry 解消

これは Chapter 2 の門番。
まずここを閉じる。

作業方針は、

1. 既存 `DiffPow` / `GN` / `pow_sub_pow_factor` を検索
2. 既存の商定義と `powerBeam` を照合
3. 合わなければ `powerBeam_succ` を作って直接 induction
4. それでも重ければ `powerBeam` 定義を既存商へ寄せる

の順がよい。

### 4.2. `PowerGapBeam` と `CosmicFormulaPythagoras` の import 依存整理

今 `PowerGapBeam.lean` は `CosmicFormulaBasic` を import している。
しかし `powerGap` / `powerBeam` 自体は非常に基礎的なので、依存は `Mathlib` だけで足りるはずじゃ。
二次 Beam と Pythagorean API を接続する補題だけ、別ファイルか後段で `CosmicFormulaPythagoras` を import して置くと美しい。

提案:

```text
DkMath/CosmicFormula/PowerGapBeam.lean
  -- Mathlib only, pure algebra

DkMath/CosmicFormula/PowerGapBeamPythagorasBridge.lean
  -- imports CosmicFormulaPythagoras + PowerGapBeam
```

ただし今はまだ急がなくてよい。`sorry` 解消後に整理でよい。

### 4.3. `CosmicLinkConditionD` の導入

次に高次リンク条件。

```lean
def CosmicLinkConditionD {R : Type*} [CommRing R]
    (d : ℕ) (α β γ u₁ u₂ u₃ : R) : Prop :=
  α ^ d * u₁ ^ d + β ^ d * u₂ ^ d = γ ^ d * u₃ ^ d
```

そして (d=2) で既存 `CosmicLinkCondition` と一致する補題。

```lean
theorem cosmicLinkConditionD_two_iff
    {R : Type*} [CommRing R] (α β γ u₁ u₂ u₃ : R) :
    CosmicLinkConditionD 2 α β γ u₁ u₂ u₃ ↔
      CosmicLinkCondition α β γ u₁ u₂ u₃ := by
  rfl
```

これは `^2` と `^ 2` の定義が一致すれば `rfl` でいける可能性がある。無理なら `unfold` + `simp`。

### 4.4. FLT bridge の薄い補題

主定理が閉じたら、次はこれ。

```lean
theorem flt_eq_forces_powerGapBeam
    {R : Type*} [CommRing R]
    (d : ℕ) (x y z : R)
    (h : x ^ d + y ^ d = z ^ d) :
    y ^ d = powerGap x z * powerBeam d x z := by
  have hdiff : z ^ d - x ^ d = y ^ d := by
    ...
  rw [pow_sub_pow_eq_gap_mul_powerBeam] at hdiff
  exact hdiff.symm
```

ただし一般 `CommRing` で subtraction と addition の変形が使える。
`sub_eq_of_eq_add'` 系を使うのが安全じゃ。

## 5. FLT との接続推論

ここがいよいよ面白い。

FLT 仮定

$$
x^d+y^d=z^d
$$

から、

$$
y^d=z^d-x^d
$$

そして Chapter 2 の主定理より、

$$
y^d=(z-x)\mathrm{Beam}_d(x,z)
$$

を得る。

ここで primitive 条件、たとえば

$$
\gcd(x,y)=\gcd(y,z)=\gcd(z,x)=1
$$

を仮定すると、Gap と Beam の gcd が強く制御される。

典型的には、

$$
\gcd(z-x,\mathrm{Beam}_d(x,z)) \mid d
$$

のような形が出る。
この補題が出ると何が嬉しいか。

もし (p\nmid d) の素数 (p) が Gap 側に出るなら、その (p)-進付値は (y^d) の中では (d) の倍数でなければならぬ。
一方、Beam 側に primitive prime が出ると、Zsigmondy / squarefree / valuation 上界から、その付値が (1) 以下に抑えられる場面がある。

つまり、

$$
\text{完全 }d\text{ 乗である要求}
$$

と

$$
\text{primitive Beam 側の valuation 上界}
$$

が衝突する。

これは、DkMath の既存 FLT 幹線そのものと一致する。構成マップでも、FLT 幹線は差の冪、gcd 制御、原始素因子、p-adic valuation を通じて進むと整理されている。

ゆえに Chapter 2 の PowerGapBeam は、FLT に対して

> (z^d-x^d) を Gap × Beam として観測する標準入口

になる。

直接山頂へ行くわけではないが、かなり良い登山口じゃ。
今までの GN / Tail / PrimitiveBeam と接続できれば、これは単なる視覚的解釈ではなく、既存 FLT ルートへの **整理されたフロントエンド** になる。

## 6. `005` S2 の推奨ロードマップ

第２章の最初のロードマップを置くなら、こうじゃ。

### S2-A. Main factorization を閉じる

* `pow_sub_pow_eq_gap_mul_powerBeam`
* `powerBeam_succ`
* 既存 `diffPowSum` との bridge

### S2-B. 高次リンク条件

* `CosmicLinkConditionD`
* `CosmicLinkConditionD_two_iff`
* `cosmic_linkD_to_power_equation`

### S2-C. FLT bridge

* `flt_eq_forces_powerGapBeam`
* 可能なら `flt_eq_forces_powerGapBeam_left/right` の対称版

### S2-D. GN / Tail 接続

* `powerBeam_eq_GN_shifted`
* `powerBeam_as_tail`
* `powerBeam_d3_explicit`
* `powerBeam_d4_explicit`

### S2-E. gcd / primitive への橋

ここはまだ次章寄りじゃが、候補だけ置く。

* `gcd_powerGap_powerBeam_dvd_d`
* `primitive_prime_of_powerBeam`
* `padicVal_powerBeam_upper_bound`

## 7. まとめ

第２章の始まりとして、今回の差分はかなり良い。

* Chapter 1 の対称 Gap/Beam は完成
* `rescaleEach` の例も入り、ゲージ自由度が空論でないことを確認
* `PowerGapBeam.lean` が生え、高次差冪への道が開いた
* 主定理は `sorry` だが、これは S2 の中心課題として自然

わっちの提案は明確じゃ。

まず `pow_sub_pow_eq_gap_mul_powerBeam` を閉じる。
それが閉じたら、すぐに `CosmicLinkConditionD` と `FLT bridge` を置く。

この順なら、Chapter 2 は **高次 Beam の入口章** として綺麗に立ち上がるぞ。
