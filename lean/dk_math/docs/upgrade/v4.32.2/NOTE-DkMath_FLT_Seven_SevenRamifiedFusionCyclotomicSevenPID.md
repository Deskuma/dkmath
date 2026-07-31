# DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicSevenPID

Issue: Lean4+Mathlib4 v4.29.0 to v4.32.2 Upgrade

対象: 補題
`theorem ringOfIntegers_isPrincipalIdealRing`

## 再検証の結論

今回の本丸は、

```text
P.IsPrime / P.LiesOver が新たに typeclass 化された
```

ことではありません。

この二つは **v4.29.0 の時点ですでに typeclass 引数**でした。旧版の `inertiaDeg_eq_of_not_dvd` も、

```lean
(P : Ideal (𝓞 K))
[P.IsPrime]
[P.LiesOver (Ideal.span {(p : ℤ)})]
```

を要求しています。

本当に変わったのは、**`Ideal.inertiaDeg` 自体のモデル**です。

### v4.29.0

```lean
Ideal.inertiaDeg p P
```

* `p`：下の環の素イデアル
* `P`：上の環の素イデアル
* 下と上の二つを明示する

旧 cyclotomic 補題の結論も、

```lean
inertiaDeg 𝒑 P = orderOf (p : ZMod m)
```

でした。

### v4.32.2

```lean
Ideal.inertiaDeg P R
```

または dot notation で、

```lean
P.inertiaDeg R
```

* `P`：上の環の素イデアル
* `R`：基礎環の型
* 下の素イデアルは `P.under R` として内部的に決まる

現行定義は、上側の ideal `q` と基礎環 `R` を受け取り、`q.under R` の剰余体から inertia degree を定義しています。

したがって現行 cyclotomic 補題の結論は、

```lean
P.inertiaDeg ℤ = orderOf (p : ZMod m)
```

へ変わっています。

---

# `CommRing ↥P` の正体

これで奇妙なエラーも完全に説明できます。

DkMath の旧記述は、

```lean
(Ideal.span ({(2 : ℤ)} : Set ℤ)).inertiaDeg P
```

です。

新 API では第一引数は「上側の ideal」、第二引数は「基礎環の型」です。

したがって Lean は旧式を、新しい意味で、

```lean
q.inertiaDeg R
```

の、

```text
q := Ideal.span {(2 : ℤ)}
R := P
```

として解釈しようとします。

ところが `P` は ideal であり、型として使われるとその carrier subtype、

```lean
↥P
```

へ coercion されます。

その結果、Lean は、

```text
CommRing ↥P
```

を探し始める。

つまりこのエラーは、typeclass inference が偶然迷走したというより、

> **旧式 `(lowerIdeal).inertiaDeg upperIdeal` を、新式 `(upperIdeal).inertiaDeg BaseRing` として読もうとした結果**

です。

したがって、第一修正は `letI` だけでは足りません。

必ず次の二つを同時に直します。

```text
1. P.IsPrime / P.LiesOver を local instance 化
2. inertiaDeg の式を P.inertiaDeg ℤ へ変更
```

---

# 正しい最小修正

$2$ branch は次の形です。

```lean
  · letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    letI :
        (Ideal.span ({(2 : ℤ)} : Set ℤ)).IsPrime :=
      (Ideal.span_singleton_prime (by norm_num)).mpr
        (Nat.prime_iff_prime_int.mp Nat.prime_two)

    obtain ⟨⟨P, hPprime, hPlies⟩⟩ :=
      (Ideal.span ({(2 : ℤ)} : Set ℤ)).nonempty_primesOver
        (S := 𝓞 K)

    letI : P.IsPrime := hPprime
    letI :
        P.LiesOver (Ideal.span ({(2 : ℤ)} : Set ℤ)) :=
      hPlies

    refine ⟨P, ⟨hPprime, hPlies⟩, Or.inl ?_⟩

    have hdeg :
        P.inertiaDeg ℤ = orderOf (2 : ZMod 7) := by
      exact
        IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd
          2 K P (by norm_num)

    change _ < 2 ^ P.inertiaDeg ℤ
    rw [hdeg, orderOf_two_zmodSeven]
    exact
      lt_of_le_of_lt
        (minkowskiFloor_le_four K)
        (by norm_num)
```

$3$ branch も同様です。

```lean
  · letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    letI :
        (Ideal.span ({(3 : ℤ)} : Set ℤ)).IsPrime :=
      (Ideal.span_singleton_prime (by norm_num)).mpr
        (Nat.prime_iff_prime_int.mp Nat.prime_three)

    obtain ⟨⟨P, hPprime, hPlies⟩⟩ :=
      (Ideal.span ({(3 : ℤ)} : Set ℤ)).nonempty_primesOver
        (S := 𝓞 K)

    letI : P.IsPrime := hPprime
    letI :
        P.LiesOver (Ideal.span ({(3 : ℤ)} : Set ℤ)) :=
      hPlies

    refine ⟨P, ⟨hPprime, hPlies⟩, Or.inl ?_⟩

    have hdeg :
        P.inertiaDeg ℤ = orderOf (3 : ZMod 7) := by
      exact
        IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd
          3 K P (by norm_num)

    change _ < 3 ^ P.inertiaDeg ℤ
    rw [hdeg, orderOf_three_zmodSeven]
    exact
      lt_of_le_of_lt
        (minkowskiFloor_le_four K)
        (by norm_num)
```

この修正なら、現行 `ClassNumber` API が要求している、

```lean
⌊M K⌋₊ < p ^ P.inertiaDeg ℤ
```

とも直接一致します。実際、v4.32.2 の PID 判定補題は、existential に選んだ `P` に対してこの形を要求しています。

---

# Kummer–Dedekind 経路は新規ではない

ここも再検証で補正が必要です。

現行版が、

```lean
primesOverSpanEquivMonicFactorsMod
```

を使い、cyclotomic polynomial の mod-$p$ 因子と素イデアルを結び付けているのは正しいです。現行版では、その途中で、

```lean
have : P.IsMaximal := .of_liesOver_isMaximal P 𝒑
```

も生成しています。

しかし Kummer–Dedekind 経路そのものは、**v4.29.0 でもすでに使われていました**。

旧版にも、

```lean
have h₂ :=
  (primesOverSpanEquivMonicFactorsMod
    h₁ ⟨P, ⟨inferInstance, inferInstance⟩⟩).2
```

および、

```lean
inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
```

が存在します。

したがって変化は、

```text
旧:
  Kummer–Dedekind により
  inertiaDeg lowerIdeal upperIdeal を計算

新:
  同じ Kummer–Dedekind データから
  upperIdeal.inertiaDeg BaseRing を計算
```

です。

**証明の数学的土台が全面交換されたのではなく、inertia degree の公開 API と内部接続が刷新された**という方が正確です。

---

# `inertiaDegIn_eq_of_not_dvd` へ移るべきか

結論として、今回の theorem では **pointwise route のままがよい**です。

現行の上位補題、

```lean
IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd
```

は確かに存在し、

```lean
𝒑.inertiaDegIn (𝓞 K) =
  orderOf (p : ZMod m)
```

を与えます。

しかし、その内部実装は、

```lean
obtain ⟨⟨P, _, _⟩⟩ := 𝒑.nonempty_primesOver
rw [
  inertiaDegIn_eq_inertiaDeg 𝒑 P Gal(K/ℚ),
  inertiaDeg_eq_of_not_dvd p K P hm
]
```

です。つまり `inertiaDegIn` は pointwise theorem を包む Galois-level wrapper です。

一方、DkMath が使っている Minkowski / class-number theorem は、最終的に具体的な `P` を返し、

```lean
p ^ P.inertiaDeg ℤ
```

を評価することを要求します。

したがって `inertiaDegIn` を使うと、

```text
global inertiaDegIn
  ↓
inertiaDegIn_eq_inertiaDeg
  ↓
具体的 P.inertiaDeg ℤ
```

と、一度上へ上げてから同じ `P` へ戻すことになります。

今回については、

```lean
inertiaDeg_eq_of_not_dvd
```

を具体的 `P` に直接適用する方が、

* 短い
* 依存が少ない
* downstream の型と直接一致
* Galois bridge を余分に挟まない

という利点があります。

`inertiaDegIn` が適切なのは、具体的な prime-over を選ばず、拡大全体の residue degree を述べたい theorem です。

---

# 後続エラーについて

次のエラーは、やはり連鎖障害と見てよいです。

```text
⊢ ?m.240 % 2 = 1
⊢ ¬3 ∣ ?m.374
```

`hdeg` の左辺が旧式のまま elaboration に失敗したため、

* modulus `7`
* `ZMod 7`
* `orderOf (2 : ZMod 7)`
* `orderOf (3 : ZMod 7)`

の型情報が十分に固定されず、metavariable が残ったものと考えられます。

`hdeg` を、

```lean
P.inertiaDeg ℤ = orderOf (2 : ZMod 7)
```

および、

```lean
P.inertiaDeg ℤ = orderOf (3 : ZMod 7)
```

へ直せば、これらもまとめて消える可能性が高いです。

---

# 今回の migration の意味

これは単なる名前変更より大きいですが、数体証明の作り直しではありません。

旧 API は、

$$
f(P/p)
$$

を、下の素イデアル $p$ と上の素イデアル $P$ の組として表現していました。

新 API は、

$$
f(P/R)
$$

を、上の素イデアル $P$ と基礎環 $R$ から表現し、下の素イデアルを、

$$
P.\operatorname{under}(R)
$$

として復元します。

数学的には、

```text
明示的な prime pair
  (p, P)
```

から、

```text
upper prime P
+
base ring R
+
derived lower prime P.under R
```

への変更です。

これは tower や一般環拡大に対して、より自然な設計です。

DkMath 側で確認すべき migration pattern は今後、

```text
old:
  p.inertiaDeg P

new:
  P.inertiaDeg R
```

です。

同系統で、

```text
old:
  p.ramificationIdx P

new:
  P.ramificationIdx R
```

も検索対象にした方がよいでしょう。

## 最終判定

今回の調査結果を修正して一文にすると、

> **`P.IsPrime` / `P.LiesOver` の local instance 登録は必要。ただし最大の破壊変更は、`Ideal.inertiaDeg` が lower-ideal-first API から upper-prime-and-base-ring API へ移行したことである。**

したがって最短修正は、

```text
letI を2件追加
+
(span {p}).inertiaDeg P
を
P.inertiaDeg ℤ
へ全面変更
```

です。

最重量と思われた FLT7 PID 障害は、やはり**局所 migration で閉じる可能性が高い**。しかも今回は、エラーの `CommRing ↥P` が新 API の引数位置を正確に教えてくれていたわけですな。🐺✨

## Lean v4.29.0 Code

```lean
/-- The ring of integers of every seventh cyclotomic number field is a
principal ideal ring.

The proof uses the class-group Minkowski theorem. Its bound is below five,
while primes above two and three have norms at least `2^3` and `3^6`.
This theorem concerns an abstract cyclotomic number field; by itself it does
not identify the concrete rank-six carrier used by the FLT7 development with
that ring of integers. -/
theorem ringOfIntegers_isPrincipalIdealRing :
    IsPrincipalIdealRing (𝓞 K) := by
  letI : IsGalois ℚ K :=
    IsCyclotomicExtension.isGalois {7} ℚ K
  apply
    RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_lt_or_isPrincipal_of_mem_primesOver_of_mem_Icc
  intro p hp_mem hp
  have hp_le : p ≤ 4 :=
    le_trans (Finset.mem_Icc.mp hp_mem).2
      (minkowskiFloor_le_four K)
  have hp_cases : p = 2 ∨ p = 3 := by
    rcases hp.eq_two_or_odd with htwo | hodd
    · exact Or.inl htwo
    · have hp2 : 2 ≤ p := hp.two_le
      have hp4 : p ≠ 4 := by
        intro heq
        subst p
        norm_num at hodd
      exact Or.inr (by omega)
  rcases hp_cases with rfl | rfl
  · letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    letI :
        (Ideal.span ({(2 : ℤ)} : Set ℤ)).IsPrime :=
      (Ideal.span_singleton_prime (by norm_num)).mpr
        (Nat.prime_iff_prime_int.mp Nat.prime_two)
    obtain ⟨⟨P, hPprime, hPlies⟩⟩ :=
      (Ideal.span ({(2 : ℤ)} : Set ℤ)).nonempty_primesOver
        (S := 𝓞 K)
    refine ⟨P, ⟨hPprime, hPlies⟩, Or.inl ?_⟩
    have hdeg :
        (Ideal.span ({(2 : ℤ)} : Set ℤ)).inertiaDeg P =
          orderOf (2 : ZMod 7) :=
      IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd
        2 K P (by norm_num)
    change
      _ <
        2 ^
          (Ideal.span ({(2 : ℤ)} : Set ℤ)).inertiaDeg P
    rw [hdeg, orderOf_two_zmodSeven]
    exact lt_of_le_of_lt (minkowskiFloor_le_four K) (by norm_num)
  · letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    letI :
        (Ideal.span ({(3 : ℤ)} : Set ℤ)).IsPrime :=
      (Ideal.span_singleton_prime (by norm_num)).mpr
        (Nat.prime_iff_prime_int.mp Nat.prime_three)
    obtain ⟨⟨P, hPprime, hPlies⟩⟩ :=
      (Ideal.span ({(3 : ℤ)} : Set ℤ)).nonempty_primesOver
        (S := 𝓞 K)
    refine ⟨P, ⟨hPprime, hPlies⟩, Or.inl ?_⟩
    have hdeg :
        (Ideal.span ({(3 : ℤ)} : Set ℤ)).inertiaDeg P =
          orderOf (3 : ZMod 7) :=
      IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd
        3 K P (by norm_num)
    change
      _ <
        3 ^
          (Ideal.span ({(3 : ℤ)} : Set ℤ)).inertiaDeg P
    rw [hdeg, orderOf_three_zmodSeven]
    exact lt_of_le_of_lt (minkowskiFloor_le_four K) (by norm_num)
```

```log
✖ [8864/9318] Building DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicSevenPID (3.9s)
info: DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicSevenPID.lean:11:0: file: DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicSevenPID
error: DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicSevenPID.lean:122:8: failed to synthesize instance of type class
  CommRing ↥P
Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
error: DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicSevenPID.lean:125:15: unsolved goals
K : Type u_1
inst✝¹ : Field K
inst✝ : NumberField K
hK : IsCyclotomicExtension {7} ℚ K
this✝¹ : IsGalois ℚ K := IsCyclotomicExtension.isGalois {7} ℚ K
hp_mem :
  2 ∈
    Finset.Icc 1
      ⌊(4 / π) ^ nrComplexPlaces K *
          (↑(Module.finrank ℚ K).factorial / ↑(Module.finrank ℚ K) ^ Module.finrank ℚ K * √|↑(discr K)|)⌋₊
hp : Nat.Prime 2
hp_le : 2 ≤ 4
this✝ : Fact (Nat.Prime 2) := { out := Nat.prime_two }
this : (Ideal.span {2}).IsPrime :=
  (Ideal.span_singleton_prime
    (Nat.prime_iff_prime_int.mp Nat.prime_two)
P : Ideal (𝓞 K)
hPprime : P.IsPrime
hPlies : P.LiesOver (Ideal.span {2})
⊢ ?m.240 % 2 = 1
error: DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicSevenPID.lean:129:10: failed to synthesize instance of type class
  CommRing ↥P
Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
error: DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicSevenPID.lean:142:8: failed to synthesize instance of type class
  CommRing ↥P
Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
error: DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicSevenPID.lean:145:15: unsolved goals
K : Type u_1
inst✝¹ : Field K
inst✝ : NumberField K
hK : IsCyclotomicExtension {7} ℚ K
this✝¹ : IsGalois ℚ K := IsCyclotomicExtension.isGalois {7} ℚ K
hp_mem :
  3 ∈
    Finset.Icc 1
      ⌊(4 / π) ^ nrComplexPlaces K *
          (↑(Module.finrank ℚ K).factorial / ↑(Module.finrank ℚ K) ^ Module.finrank ℚ K * √|↑(discr K)|)⌋₊
hp : Nat.Prime 3
hp_le : 3 ≤ 4
this✝ : Fact (Nat.Prime 3) := { out := Nat.prime_three }
this : (Ideal.span {3}).IsPrime :=
  (Ideal.span_singleton_prime
    (Nat.prime_iff_prime_int.mp Nat.prime_three)
P : Ideal (𝓞 K)
hPprime : P.IsPrime
hPlies : P.LiesOver (Ideal.span {3})
⊢ ¬3 ∣ ?m.374
error: DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicSevenPID.lean:149:10: failed to synthesize instance of type class
  CommRing ↥P
Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
info: DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicSevenPID.lean:159:0: 'DkMath.FLT.Seven.CyclotomicSeven.minkowskiFloor_le_four' depends on axioms: [propext, Classical.choice, Quot.sound]
info: DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicSevenPID.lean:160:0: 'DkMath.FLT.Seven.CyclotomicSeven.orderOf_two_zmodSeven' depends on axioms: [propext, Classical.choice, Quot.sound]
info: DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicSevenPID.lean:161:0: 'DkMath.FLT.Seven.CyclotomicSeven.orderOf_three_zmodSeven' depends on axioms: [propext, Classical.choice, Quot.sound]
info: DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicSevenPID.lean:162:0: 'DkMath.FLT.Seven.CyclotomicSeven.ringOfIntegers_isPrincipalIdealRing' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
info: DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicSevenPID.lean:163:0: 'DkMath.FLT.Seven.CyclotomicSeven.classNumber_eq_one' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
error: Lean exited with code 1
```
