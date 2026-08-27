# DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicSevenPID

**Proved**

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

## Migration review

## Report

`Mathlib v4.32.2` における inertia degree API の変更へ、最小かつ正確に追随した Migration です。

旧 API、

```lean
(Ideal.span ({(p : ℤ)} : Set ℤ)).inertiaDeg P
```

は、下側の素イデアルと上側の素イデアルを直接渡す形式でした。

新 API では、

```lean
P.inertiaDeg ℤ
```

となり、上側の素イデアル `P` と基礎環 `ℤ` を指定します。下側の素イデアルは `P.under ℤ` によって内部的に復元されます。

これに合わせて、`nonempty_primesOver` から取り出した、

```lean
hPprime : P.IsPrime
hPlies  : P.LiesOver (Ideal.span {(p : ℤ)})
```

を local instance として登録しました。

```lean
letI : P.IsPrime := hPprime
letI : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := hPlies
```

修正は $p=2$ branch と $p=3$ branch の双方へ対称に適用されています。

その結果、現行の cyclotomic inertia degree theorem、

```lean
IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd
```

と、Minkowski PID 判定側が要求する、

```lean
p ^ P.inertiaDeg ℤ
```

が同じ API 上で直接接続されました。

数学的な証明内容に変更はありません。

```text
Minkowski bound < 5
prime candidates = 2 or 3
f₂ = orderOf(2 mod 7) = 3
f₃ = orderOf(3 mod 7) = 6
4 < 2^3
4 < 3^6
```

したがって、Minkowski bound 以下に非自明な ideal class を代表する素イデアルは存在せず、七次円分体の整数環が principal ideal ring であるという既存結論が保存されています。

Checkpoint:

```text
3071a03d0d29a457427567d436b684af27595877
fix(upgrade): migrate cyclotomic inertia degree API
```

## Review

**承認です。修正は正確で、過不足ありません。**

### 1. API の意味変更を正しく反映している

最重要点は、単なる補題名の変更ではなく、

```text
old:
  lowerPrime.inertiaDeg upperPrime

new:
  upperPrime.inertiaDeg BaseRing
```

という inertia degree の表現モデル変更です。

差分はこの変更を正しく捉えています。

```diff
- (Ideal.span ({(2 : ℤ)} : Set ℤ)).inertiaDeg P
+ P.inertiaDeg ℤ
```

これにより、以前現れていた、

```text
failed to synthesize instance
  CommRing ↥P
```

の原因も解消されています。

旧引数順の式を新 API が読むと、第二引数 `P` を基礎環の型として解釈しようとするため、ideal の carrier subtype `↥P` に対する `CommRing` を探していました。

今回の修正は、その一次原因を直接除去しています。

### 2. local instance の位置が適切

```lean
obtain ⟨⟨P, hPprime, hPlies⟩⟩ := ...
letI : P.IsPrime := hPprime
letI : P.LiesOver ... := hPlies
```

という順序は適切です。

`P` を取得した直後に、その prime-over witness を instance environment へ登録しているため、後続の、

```lean
inertiaDeg_eq_of_not_dvd
```

内部で必要となる、

```lean
inferInstance : P.IsPrime
inferInstance : P.LiesOver ...
```

が安定して解決されます。

`refine` の existential witness には従来どおり明示的な証明項、

```lean
⟨hPprime, hPlies⟩
```

を渡しており、構造データと instance inference の役割も混同していません。

### 3. downstream goal と完全に一致した

`change` も、

```lean
change _ < 2 ^ P.inertiaDeg ℤ
```

へ更新されています。

これは現行の、

```lean
RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_lt_or_isPrincipal_of_mem_primesOver_of_mem_Icc
```

が要求する norm-bound branch の形と一致します。

したがって、

```lean
rw [hdeg, orderOf_two_zmodSeven]
```

によって、

```text
Minkowski floor < 2^3
```

へ直接落ちます。

$p=3$ branch も同じ構造で、

```text
Minkowski floor < 3^6
```

へ落ちるため、左右対称で読みやすい実装になっています。

### 4. `inertiaDegIn` へ変更しなかった判断も正しい

今回必要なのは、existential に選択した具体的な prime ideal `P` に対する、

```lean
P.inertiaDeg ℤ
```

です。

したがって extension 全体の共通値を述べる、

```lean
inertiaDegIn_eq_of_not_dvd
```

へ一度持ち上げる必要はありません。

```text
具体的 P
  → pointwise inertia degree
  → norm lower bound
```

という現在の route が最短です。

### 5. 数学的意味は完全に保存されている

この migration は証明の数学的内容を変更していません。

変わったのは inertia degree の API 表現だけです。

```text
旧:
  f(P / span(p))

新:
  f(P / ℤ)
  下側 prime は P.under ℤ
```

`P.LiesOver (span {(p : ℤ)})` が登録されているため、新 API が内部的に使う `P.under ℤ` は期待する rational prime ideal と一致します。

したがって、

```lean
ringOfIntegers_isPrincipalIdealRing
```

および、その直後の、

```lean
classNumber_eq_one
```

の数学的意味はそのまま維持されています。

## 総評

これは `v4.29.0 → v4.32.2` Migration の良い標本です。

```text
型クラス witness の明示登録
+
inertiaDeg の引数モデル変更
```

という二つの変更だけで、数体証明本体を触らずに復旧できています。

特に重要なのは、最初のエラーを単なる instance 不足として処理せず、`CommRing ↥P` から **引数位置の意味変更**まで追跡できたことです。

```text
Review result:
  APPROVED

Mathematical change:
  none

API migration:
  exact

Scope:
  minimal

Future stability:
  good
```

今後の Migration 監査では、同じ系統として次を検索対象にするとよいです。

```text
.inertiaDeg
inertiaDeg
.ramificationIdx
ramificationIdx
```

特に旧形式、

```lean
lowerIdeal.inertiaDeg upperIdeal
lowerIdeal.ramificationIdx upperIdeal
```

が残っていれば、今回と同じ、

```lean
upperIdeal.inertiaDeg BaseRing
upperIdeal.ramificationIdx BaseRing
```

への変更候補です。

最重量候補だった FLT7 円分体 PID は、無事に局所 API Migration だけで生還しましたな。よき修復です。🐺👍️

## Appendix

### Lean v4.29.0 Code

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

### Lean v4.32.2 Code

```lean/-- The ring of integers of every seventh cyclotomic number field is a
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
    letI : P.IsPrime := hPprime
    letI : P.LiesOver (Ideal.span ({(2 : ℤ)} : Set ℤ)) := hPlies
    refine ⟨P, ⟨hPprime, hPlies⟩, Or.inl ?_⟩
    have hdeg :
        P.inertiaDeg ℤ =
          orderOf (2 : ZMod 7) :=
      IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd
        2 K P (by norm_num)
    change
      _ <
        2 ^
          P.inertiaDeg ℤ
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
    letI : P.IsPrime := hPprime
    letI : P.LiesOver (Ideal.span ({(3 : ℤ)} : Set ℤ)) := hPlies
    refine ⟨P, ⟨hPprime, hPlies⟩, Or.inl ?_⟩
    have hdeg :
        P.inertiaDeg ℤ =
          orderOf (3 : ZMod 7) :=
      IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd
        3 K P (by norm_num)
    change
      _ <
        3 ^
          P.inertiaDeg ℤ
    rw [hdeg, orderOf_three_zmodSeven]
    exact lt_of_le_of_lt (minkowskiFloor_le_four K) (by norm_num)
```

## Git diff / Report / Review

## fix(upgrade): migrate cyclotomic inertia degree API

gch: 3071a03d0d29a457427567d436b684af27595877

## Report

ノートの分析に基づく修正が成功しました。

修正内容:

* `P.IsPrime` を local instance 化
* `P.LiesOver (...)` を local instance 化
* 旧式 `lowerIdeal.inertiaDeg P` を新式 `P.inertiaDeg ℤ` に変更
* $2$・$3$ 両ブランチへ適用

検証:

```text
lake build DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicSevenPID
成功
```

コミット:

```text
3071a03d fix(upgrade): migrate cyclotomic inertia degree API
```

現在、全体ビルドで残っているのは保留指定済みの2ファイルのみです。

* `RH.EulerZetaLemmas`
* `CosmicFormula.CosmicFormulaDim`

## Review

_

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicSevenPID.lean b/lean/dk_math/DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicSevenPID.lean
index 3182bf65..f413a898 100644
--- a/lean/dk_math/DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicSevenPID.lean
+++ b/lean/dk_math/DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicSevenPID.lean
@@ -117,16 +117,18 @@ theorem ringOfIntegers_isPrincipalIdealRing :
     obtain ⟨⟨P, hPprime, hPlies⟩⟩ :=
       (Ideal.span ({(2 : ℤ)} : Set ℤ)).nonempty_primesOver
         (S := 𝓞 K)
+    letI : P.IsPrime := hPprime
+    letI : P.LiesOver (Ideal.span ({(2 : ℤ)} : Set ℤ)) := hPlies
     refine ⟨P, ⟨hPprime, hPlies⟩, Or.inl ?_⟩
     have hdeg :
-        (Ideal.span ({(2 : ℤ)} : Set ℤ)).inertiaDeg P =
+        P.inertiaDeg ℤ =
           orderOf (2 : ZMod 7) :=
       IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd
         2 K P (by norm_num)
     change
       _ <
         2 ^
-          (Ideal.span ({(2 : ℤ)} : Set ℤ)).inertiaDeg P
+          P.inertiaDeg ℤ
     rw [hdeg, orderOf_two_zmodSeven]
     exact lt_of_le_of_lt (minkowskiFloor_le_four K) (by norm_num)
   · letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
@@ -137,16 +139,18 @@ theorem ringOfIntegers_isPrincipalIdealRing :
     obtain ⟨⟨P, hPprime, hPlies⟩⟩ :=
       (Ideal.span ({(3 : ℤ)} : Set ℤ)).nonempty_primesOver
         (S := 𝓞 K)
+    letI : P.IsPrime := hPprime
+    letI : P.LiesOver (Ideal.span ({(3 : ℤ)} : Set ℤ)) := hPlies
     refine ⟨P, ⟨hPprime, hPlies⟩, Or.inl ?_⟩
     have hdeg :
-        (Ideal.span ({(3 : ℤ)} : Set ℤ)).inertiaDeg P =
+        P.inertiaDeg ℤ =
           orderOf (3 : ZMod 7) :=
       IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd
         3 K P (by norm_num)
     change
       _ <
         3 ^
-          (Ideal.span ({(3 : ℤ)} : Set ℤ)).inertiaDeg P
+          P.inertiaDeg ℤ
     rw [hdeg, orderOf_three_zmodSeven]
     exact lt_of_le_of_lt (minkowskiFloor_le_four K) (by norm_num)
 
````
`````
