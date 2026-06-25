# Issue

Lean v4.30.0 でエラーとなる予定の箇所。

```log
✖ [8719/8727] Building DkMath.FLT.Kummer.CyclotomicPrincipalization (29s)
info: DkMath/FLT/Kummer/CyclotomicPrincipalization.lean:15:0: file: DkMath.FLT.Kummer.CyclotomicPrincipalization
error: DkMath/FLT/Kummer/CyclotomicPrincipalization.lean:860:6: failed to synthesize instance of type class
  Field ↥↑↑I
Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
warning: DkMath/FLT/Kummer/CyclotomicPrincipalization.lean:5385:8: declaration uses `sorry`
warning: DkMath/FLT/Kummer/CyclotomicPrincipalization.lean:5696:8: declaration uses `sorry`
error: Lean exited with code 1
```

## FLT

該当箇所

- [DkMath.FLT.Kummer.CyclotomicPrincipalization](/lean/dk_math/DkMath/FLT/Kummer/CyclotomicPrincipalization.lean#L860)

`CyclotomicPrincipalIdealExtractionTarget`

## review

うむ、スナップショットから該当箇所を抜いた。
結論から言うと、 **error の本丸は 860 行目の `ClassGroup.mk I = 1`** じゃ。`Polynomial.eval_finset_sum` はただの rename 警告なので後回しでよい。

## 1. 該当コード

スナップショット内の該当部分はこれじゃ。

```lean id="gq3e4g"
abbrev CyclotomicPrincipalIdealExtractionTarget : Prop :=
  ∀ {R : Type*} [CommRing R] [IsDomain R]
      {I : (FractionalIdeal (nonZeroDivisors R) (FractionRing R))ˣ} {I' : Ideal R},
      ((I : FractionalIdeal (nonZeroDivisors R) (FractionRing R)) = I') →
      ClassGroup.mk I = 1 →
      ∃ x, x ≠ 0 ∧ I' = Ideal.span {x}
```

落ちているのはこの行。

```lean id="dfzqpe"
ClassGroup.mk I = 1 →
```

エラーは、

```text id="m78sg0"
failed to synthesize instance of type class
  Field ↥↑↑I
```

じゃな。

## 2. 原因

これは Lean 4.30.0 / mathlib 側で `ClassGroup.mk` まわりの推論が変わったか、暗黙引数の解釈が以前より通らなくなったものと見てよい。

`I` はここでは

```lean id="z5s2xc"
(FractionalIdeal (nonZeroDivisors R) (FractionRing R))ˣ
```

つまり **fractional ideal の unit** じゃ。

ところが `ClassGroup.mk I` と書いたとき、Lean 4.30.0 側では `I` を「class group に入れる ideal」として素直に読めず、変な方向に推論して `Field ↥↑↑I` を探しに行っている。
つまり、`I` の二重 coercion 先を field として扱おうとして失敗しておる。

これは数学が壊れたというより、 **API / coercion / typeclass 推論の不安定地点を踏んだ** 形じゃ。

## 3. このファイル内では、実は `mk0` 版が安定している

同じファイル内では、こちらの形はすでに使われておる。

```lean id="fwoxsx"
ClassGroup.mk0 ⟨K, hK⟩
```

たとえば前半には、

```lean id="ab5on9"
ClassGroup.mk0 ⟨K, hK⟩ ^ p = 1
```

や、

```lean id="rjrkvk"
(ClassGroup.mk0_eq_one_iff hK_mem).mp hClassTriv
```

が使われている。

さらに後ろにも helper がある。

```lean id="j2ufuz"
theorem idealIsPrincipal_of_classGroupMk0_eq_one
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {I : Ideal R} (hI : I ∈ nonZeroDivisors (Ideal R))
    (hClass : ClassGroup.mk0 ⟨I, hI⟩ = 1) :
    I.IsPrincipal :=
  (ClassGroup.mk0_eq_one_iff hI).mp hClass
```

つまり、 **`ClassGroup.mk` fractional ideal unit 版より、`ClassGroup.mk0` integral ideal 版へ寄せる方が安全** じゃ。

しかも DkMath の FLT 幹線では、冪差・gcd・原始素因子・class-group/Kummer 側の橋を段階分離する方針なので、この部分も「generic fractional ideal unit」へ無理に寄せるより、integral ideal の `mk0` target に落としたほうが実装上も綺麗じゃ。Zsigmondy / FLT 幹線がそうした機能ブロック分解で整理されていることは、プロジェクト INDEX 側でも確認できる。

## 4. 最小修正案

`CyclotomicPrincipalIdealExtractionTarget` を、まず `mk0` 版に置き換える。

```lean id="nzxeu5"
abbrev CyclotomicPrincipalIdealExtractionTarget : Prop :=
  ∀ {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
      {I : Ideal R},
      I ∈ nonZeroDivisors (Ideal R) →
      ClassGroup.mk0 ⟨I, by assumption⟩ = 1 →
      I.IsPrincipal
```

ただし `by assumption` を abbrev の中で使うのは気持ち悪いので、Lean 的にはこう書く方が安全じゃ。

```lean id="o7vrle"
abbrev CyclotomicPrincipalIdealExtractionTarget : Prop :=
  ∀ {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
      {I : Ideal R} (hI : I ∈ nonZeroDivisors (Ideal R)),
      ClassGroup.mk0 ⟨I, hI⟩ = 1 →
      I.IsPrincipal
```

そして証明側はこうなる。

```lean id="d6y8fw"
theorem cyclotomicPrincipalIdealExtraction_of_classTrivialization :
    CyclotomicPrincipalIdealExtractionTarget := by
  intro R _ _ _ I hI hClass
  exact (ClassGroup.mk0_eq_one_iff hI).mp hClass
```

ただし `intro` の数は Lean が要求する binder 展開により微調整が要る。
`[IsDedekindDomain R]` が増えるので、だいたい次のどちらかじゃ。

```lean id="ymj86j"
  intro R hComm hDomain hDedekind I hI hClass
```

または `_` を使って、

```lean id="fdljnh"
  intro R _ _ _ I hI hClass
```

で通るはず。

## 5. さらに保守的な修正案

もし Stage 1c target が現時点で composition theorem の引数として渡されているだけで、本体では使われていないなら、もっと保守的に `Prop := True` へ戻す手もある。

```lean id="q43c48"
abbrev CyclotomicPrincipalIdealExtractionTarget : Prop := True
```

ただし、これは後退じゃ。
すでに `mk0` 版 helper があるので、わっちなら **`mk0` integral ideal 版へ変更** を推す。

## 6. `Polynomial.eval_finset_sum` 警告

こちらは単純置換でよい。

```lean id="zv58ns"
Polynomial.eval_finset_sum
```

を

```lean id="zzmmpn"
Polynomial.eval_finsetSum
```

へ変更。

該当はログ上では 2 箇所。

```text id="grj0wp"
TriominoCosmicBranchADescentChain.lean:1486:39
TriominoCosmicBranchADescentChain.lean:1743:23
```

これは本質的ではないので、あとで一括置換で十分じゃ。

## 7. 判断

今回の 2 件の `error` は、実質的には **1 箇所の型エラー + Lean 終了 error** じゃな。

本丸はこれ。

```lean id="gyhl1x"
ClassGroup.mk I = 1
```

対処は、

```lean id="xis8y8"
ClassGroup.mk0 ⟨I, hI⟩ = 1
```

へ寄せる。

これは後退ではなく、むしろこのファイルの他の補題群と揃う。
`FractionalIdeal` unit の coercion 沼を避けて、`Ideal R` と `mk0` の明示ルートへ戻すのが、Lean 4.30.0 対応としては一番堅いと思うぞい。
