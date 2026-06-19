# Git diff / Report / Review

## Upd: NumberTheory PrimitiveBeam

gch: da198351e7f41a434ffc67b07d72ac153ed1100b

## Report

進めました。今回は `PrimitiveBeam` の perfect-power obstruction 側にも NoLift 本命ルートを通しました。

追加した theorem:

```lean
primitive_prime_factor_forbids_perfect_pow_diff_of_noLift_GN
primitive_prime_obstructs_GN_perfect_power_of_noLift_GN
```

これで obstruction 層も次の形で読めます。

```text
PrimitivePrimeFactorOfDiffPow q a b d
+ local NoLift on GN
-> padicValNat <= 1
-> a^d - b^d is not a perfect d-th power
-> GN d (a-b) b is not a perfect d-th power
```

また、既存の squarefree obstruction 版は NoLift 版経由に寄せました。

```text
Squarefree GN
-> local NoLift GN
-> perfect-power obstruction
```

docs も `Petal-Overview.md` と `FLGNB-PetalRoadmap.md` に反映済みです。

検証:

```sh
lake build DkMath.NumberTheory.PrimitiveBeam
lake build DkMath.Petal
git diff --check
```

すべて通っています。既存の research `sorry` 警告だけ継続です。

## Review

### 状況確認

[issue-petal-028](./issue-petal-028.md) との接続予定は現状どうなっているか？

うむ。状況はかなり良い。
ただし「予定だった接続」と比べると、いまは **論理的には厚みが増したのではなく、むしろ薄くなった**。一方で **import / ファイル配置の厚みはまだ残っている**、という状態じゃ。

## まず結論

予定していた二つの接続は、こういう位置づけになった。

```lean
DkMath.NumberTheory.GcdNext.padicValNat_primitive_prime_factor_le_one_of_squarefree_G
```

これは当初の本命候補だったが、今では **互換用の重い squarefree wrapper** に近い。

```lean
DkMath.NumberTheory.ValuationFlow.primitivePrimeFlow_diffMass_le_one_of_squarefree_beam
```

これは ABC / ValuationFlow 側の入口としてまだ重要。ただし中身は、今後 `PrimitiveBeam` の local theorem へ委譲すればかなり薄くできる。

現在の本命は、こちらへ移った。

```lean
PrimitiveBeam.primitive_prime_padic_bound_diff_of_noLift_GN
PrimitiveBeam.primitive_prime_padic_bound_diff_of_squarefree_GN_local
```

つまり、予定接続の厚みはこう変化した。

```text
旧本命:
  GcdNext squarefree theorem
  ValuationFlow squarefree beam theorem

新本命:
  PrimitiveBeam noLift theorem
  PrimitiveBeam local squarefree theorem

旧本命:
  compatibility wrapper / downstream API
```

## 1. `GcdNext.padicValNat_primitive_prime_factor_le_one_of_squarefree_G` の厚み

この theorem は正しいし、`#print axioms` も標準 axiom だけじゃ。

```text
[propext, Classical.choice, Quot.sound]
```

これは mathlib / Lean 通常依存で、`sorryAx` ではない。
したがって証明済み theorem としては使ってよい。

ただし、仮定は重い。

```lean
(hd_prime : Nat.Prime d)
(hd_ge : 3 ≤ d)
(hab_lt : b < a)
(hb : 0 < b)
(hab : Nat.Coprime a b)
(hpnd : ¬ d ∣ a - b)
(hq_prime : Nat.Prime q)
(hq_div : q ∣ a ^ d - b ^ d)
(hq_ndiv : ¬ q ∣ a - b)
(hG_sq : Squarefree (GN d (a - b) b))
```

これは「Zsigmondy primitive branch を外側から全部説明する」形じゃな。

ところが今回の `PrimitiveBeam` 整理後は、すでに

```lean
PrimitivePrimeFactorOfDiffPow q a b d
```

を持っていれば、valuation に必要な情報はもっと少ない。

NoLift 本命:

```lean
PrimitivePrimeFactorOfDiffPow q a b d
0 < d
1 < d
b < a
¬ q ^ 2 ∣ GN d (a - b) b
```

squarefree 十分条件:

```lean
PrimitivePrimeFactorOfDiffPow q a b d
0 < d
1 < d
b < a
Squarefree (GN d (a - b) b)
```

つまり `GcdNext.padicValNat_primitive_prime_factor_le_one_of_squarefree_G` は、もう本質層ではない。

```text
役割:
  旧 caller / research repair 用の互換 theorem

本質:
  PrimitiveBeam の PrimitivePrimeFactorOfDiffPow + NoLift
```

という状態になった。

## 2. `ZsigmondyCyclotomicSquarefree.lean` の現在位置

このファイルには二種類のものが混ざっている。

ひとつは汎用的に有用なもの。

```lean
padicValNat_le_one_of_squarefree
```

これは、

```text
n が nonzero squarefree
  -> 任意の prime q について padicValNat q n <= 1
```

なので、今後も使える。

もうひとつは、重い repair theorem。

```lean
padicValNat_primitive_prime_factor_le_one_of_squarefree_G
```

これは今となっては、

```text
PrimitiveBeam local squarefree theorem の旧 signature wrapper
```

として読むのが自然じゃ。

理想的には将来、構造をこう分けたい。

```text
SquarefreeValuation / GcdNext:
  padicValNat_le_one_of_squarefree

PrimitiveBeam:
  PrimitivePrimeFactorOfDiffPow
  primitive_prime_padic_bound_diff_of_noLift_GN
  primitive_prime_padic_bound_diff_of_squarefree_GN_local

ZsigmondyCyclotomicSquarefree:
  legacy compatibility / old repair wrappers
```

つまり `ZsigmondyCyclotomicSquarefree.lean` は今すぐ消すものではないが、**本線の新規 caller が直接寄る場所ではなくなった**。

## 3. `ValuationFlow.Primitive` の厚み

現状の `ValuationFlow.Primitive` はこうなっている。

```lean
import DkMath.NumberTheory.ValuationFlow.Basic
import DkMath.NumberTheory.PrimitiveBeam
import DkMath.NumberTheory.ZsigmondyCyclotomicSquarefree
```

そして、

```lean
theorem primitivePrimeFlow_diffMass_le_one_of_squarefree_beam
```

は中でこれを呼んでいる。

```lean
primitive_prime_padic_bound_diff_of_squarefree_GN
```

つまり、ValuationFlow 側はまだ旧 heavy squarefree wrapper 経由じゃ。

でも、`PrimitivePrimeFlowWitness` は実質これの abbrev になっている。

```lean
abbrev PrimitivePrimeFlowWitness (q a b d : ℕ) : Prop :=
  PrimitivePrimeFactorOfDiffPow q a b d
```

なので、今ならもっと薄くできる。

まず NoLift 版を ValuationFlow に作れる。

```lean
theorem primitivePrimeFlow_diffMass_le_one_of_noLift_beam
    {q a b d : ℕ}
    (hq : PrimitivePrimeFlowWitness q a b d)
    (hd : 0 < d) (hd1 : 1 < d)
    (hab_lt : b < a)
    (hNoLift : ¬ q ^ 2 ∣ GN d (a - b) b) :
    diffMass q a b d ≤ 1 := by
  exact
    primitive_prime_padic_bound_diff_of_noLift_GN
      hq hd hd1 hab_lt hNoLift
```

次に squarefree local 版。

```lean
theorem primitivePrimeFlow_diffMass_le_one_of_squarefree_beam_local
    {q a b d : ℕ}
    (hq : PrimitivePrimeFlowWitness q a b d)
    (hd : 0 < d) (hd1 : 1 < d)
    (hab_lt : b < a)
    (hG_sq : Squarefree (GN d (a - b) b)) :
    diffMass q a b d ≤ 1 := by
  exact
    primitive_prime_padic_bound_diff_of_squarefree_GN_local
      hq hd hd1 hab_lt hG_sq
```

そして既存の重い theorem は互換 wrapper にできる。

```lean
theorem primitivePrimeFlow_diffMass_le_one_of_squarefree_beam
    {q a b d : ℕ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hab_lt : b < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (hpnd : ¬ d ∣ a - b)
    (hq : PrimitivePrimeFlowWitness q a b d)
    (hG_sq : Squarefree (GN d (a - b) b)) :
    diffMass q a b d ≤ 1 := by
  have hd : 0 < d := hd_prime.pos
  have hd1 : 1 < d := by omega
  exact
    primitivePrimeFlow_diffMass_le_one_of_squarefree_beam_local
      hq hd hd1 hab_lt hG_sq
```

この形にすれば、`ValuationFlow.Primitive` は理論的には `ZsigmondyCyclotomicSquarefree` を import しなくてよくなる可能性が高い。

## 4. 予定接続との厚み比較

まとめるとこうじゃ。

| 層                             | 旧状態                         | 現在                      | 評価           |
| ------------------------------ | ------------------------------ | ------------------------- | -------------- |
| GcdNext squarefree theorem     | 本命 repair theorem            | 互換 wrapper 候補         | 論理的には厚い |
| PrimitiveBeam NoLift           | 無かった / Petal 内に局所証明  | 汎用 theorem 化済み       | 本命           |
| PrimitiveBeam squarefree local | 無かった                       | NoLift の十分条件 wrapper | 本命補助       |
| ValuationFlow squarefree beam  | heavy wrapper 呼び出し         | まだ旧経由                | 次に薄くできる |
| Petal D3 valuation             | 自前証明から開始               | thin wrapper 化           | 良い           |
| perfect-power obstruction      | squarefree repair 中心         | NoLift 本命へ移行         | 良い           |

つまり、予定だった接続はこういう位置に変わった。

```text
GcdNext.padicValNat_primitive_prime_factor_le_one_of_squarefree_G
  -> 予定接続としては到達済み
  -> ただし今後は compatibility wrapper 扱い

ValuationFlow.primitivePrimeFlow_diffMass_le_one_of_squarefree_beam
  -> 予定接続としては到達済み
  -> ただし次に local NoLift / local squarefree へ分解すべき
```

## 5. 今回の perfect-power obstruction 追加の意味

今回追加した、

```lean
primitive_prime_factor_forbids_perfect_pow_diff_of_noLift_GN
primitive_prime_obstructs_GN_perfect_power_of_noLift_GN
```

はかなり重要。

これで valuation bound が単なる数値補題ではなく、

```text
padicValNat <= 1
  -> perfect d-th power なら valuation が d の倍数になる
  -> d >= 3 と矛盾
```

という obstruction 層まで届いた。

つまり NoLift route は、

```text
local NoLift on GN
  -> valuation <= 1
  -> diff body is not a perfect d-th power
  -> GN side is not a perfect d-th power
```

まで通った。

これは FLT 側にも ABC 側にも効く。

FLT 側では、

```text
差冪が完全 d 乗として閉じる枝を壊す
```

ABC / ValuationFlow 側では、

```text
primitive flow の mass が過剰に積み上がる枝を壊す
```

という読みになる。

## 6. まだ残っている厚み

残っているのは証明の厚みではなく、主に **配置と import の厚み** じゃ。

特に気になるのはこの辺り。

```text
PrimitiveBeam が Research / ZsigmondyCyclotomic 系をまだ強く import している
ValuationFlow.Primitive が ZsigmondyCyclotomicSquarefree を直接 import している
ZsigmondyCyclotomicSquarefree に generic squarefree valuation と legacy repair が同居している
```

証明としては健全。
しかし API 階層としては、次のように分けるとさらに良い。

```text
PrimitiveBeam.Basic:
  PrimitivePrimeFactorOfDiffPow
  primitive_prime_not_dvd_boundary
  primitive_prime_dvd_GN
  primitive_prime_padic_eq_GN

PrimitiveBeam.Valuation:
  primitive_prime_GN_ne_zero
  primitive_prime_padic_bound_diff_of_noLift_GN
  primitive_prime_padic_bound_diff_of_squarefree_GN_local

PrimitiveBeam.Obstruction:
  primitive_prime_factor_forbids_perfect_pow_diff_of_noLift_GN
  primitive_prime_obstructs_GN_perfect_power_of_noLift_GN

ZsigmondyCyclotomicSquarefree:
  old compatibility wrappers
```

今すぐやる必要はないが、これは次の整理候補じゃ。

## 7. `#print axioms` の見方

提示された二つは、

```text
[propext, Classical.choice, Quot.sound]
```

だけなので問題ない。

これは Lean/mathlib の通常の非計算的依存であって、

```text
sorryAx
axiom
unsafe
```

ではない。

ただし、今後 `PrimitiveBeam` の新 theorem についても `#print axioms` を見るなら、本当に確認したいのはこれ。

```lean
#print axioms DkMath.NumberTheory.PrimitiveBeam.primitive_prime_padic_bound_diff_of_noLift_GN
#print axioms DkMath.NumberTheory.PrimitiveBeam.primitive_prime_padic_bound_diff_of_squarefree_GN_local
#print axioms DkMath.NumberTheory.PrimitiveBeam.primitive_prime_factor_forbids_perfect_pow_diff_of_noLift_GN
#print axioms DkMath.NumberTheory.PrimitiveBeam.primitive_prime_obstructs_GN_perfect_power_of_noLift_GN
```

ここに `sorryAx` が無ければ、旧二本よりも新本命ルートの方が健全な中心になる。

## 8. 次にやるなら

次の一手は、`ValuationFlow.Primitive` の薄型化じゃな。

追加候補:

```lean
primitivePrimeFlow_diffMass_le_one_of_noLift_beam
primitivePrimeFlow_diffMass_le_one_of_squarefree_beam_local
```

既存 theorem:

```lean
primitivePrimeFlow_diffMass_le_one_of_squarefree_beam
```

は互換 wrapper として残す。

これをやると、ABC 側の予定接続がかなり綺麗になる。

```text
PrimitiveBeam:
  valuation arithmetic

ValuationFlow:
  diffMass / beamMass 語彙への翻訳

ABC:
  flow mass control として利用
```

## 総括

現状はこうじゃ。

```text
予定接続:
  GcdNext squarefree theorem
  ValuationFlow squarefree beam theorem

現在の実質本命:
  PrimitiveBeam noLift theorem
  PrimitiveBeam squarefree local theorem

厚み:
  論理仮定は薄くなった
  import / 互換 wrapper はまだ厚い
  ValuationFlow は次に薄くできる
```

一言で言えば、

```text
GcdNext は旧 repair の本棚。
PrimitiveBeam が本命の算術エンジン。
ValuationFlow はそれを ABC 用の mass 語彙に翻訳する層。
```

ここまで来ると、`ZsigmondyCyclotomicResearch.lean` の偽 placeholder を直接救う必要はもうない。
救出経路はすでに、

```text
PrimitiveBeam NoLift
  -> PrimitiveBeam squarefree local
  -> ValuationFlow local
  -> Petal D3 wrapper
```

として立ち上がっておる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/NumberTheory/PrimitiveBeam.lean b/lean/dk_math/DkMath/NumberTheory/PrimitiveBeam.lean
index 66a60564..d0823e88 100644
--- a/lean/dk_math/DkMath/NumberTheory/PrimitiveBeam.lean
+++ b/lean/dk_math/DkMath/NumberTheory/PrimitiveBeam.lean
@@ -385,17 +385,19 @@ theorem primitive_prime_obstructs_GN_perfect_power
   exact primitive_prime_obstructs_GN_perfect_power_research hd_prime hd_ge hab_lt hb hab hpnd

 /--
-Honest squarefree-GN repair of `primitive_prime_factor_forbids_perfect_pow_diff`.
+Honest local no-lift repair of `primitive_prime_factor_forbids_perfect_pow_diff`.

-This is the migration shape for the two legacy callers in this file: if the caller can supply
-`Squarefree (GN d (a - b) b)`, the contradiction argument closes without the research placeholder.
+The theorem obtains a primitive witness from Zsigmondy and asks only that the
+selected witness has no `q^2` lift on the `GN` side.
 -/
-theorem primitive_prime_factor_forbids_perfect_pow_diff_of_squarefree_GN
+theorem primitive_prime_factor_forbids_perfect_pow_diff_of_noLift_GN
     {a b d : ℕ}
     (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
     (hab_lt : b < a) (hb : 0 < b) (hab : Nat.Coprime a b)
     (hpnd : ¬ d ∣ a - b)
-    (hG_sq : Squarefree (GN d (a - b) b)) :
+    (hNoLift :
+      ∀ {q : ℕ}, PrimitivePrimeFactorOfDiffPow q a b d →
+        ¬ q ^ 2 ∣ GN d (a - b) b) :
     ¬ ∃ t : ℕ, 0 < t ∧ a ^ d - b ^ d = t ^ d := by
   intro hpow
   rcases hpow with ⟨t, ht, heq⟩
@@ -417,25 +419,60 @@ theorem primitive_prime_factor_forbids_perfect_pow_diff_of_squarefree_GN
     calc
       d = d * 1 := (Nat.mul_one d).symm
       _ ≤ d * padicValNat q t := Nat.mul_le_mul_left d hvt_ge
+  have hd_pos : 0 < d := hd_prime.pos
+  have hd1 : 1 < d := by omega
   have hpadic_bound_diff : padicValNat q (a ^ d - b ^ d) ≤ 1 :=
-    primitive_prime_padic_bound_diff_of_squarefree_GN
-      hd_prime hd_ge hab_lt hb hab hpnd hq hG_sq
+    primitive_prime_padic_bound_diff_of_noLift_GN
+      hq hd_pos hd1 hab_lt (hNoLift hq)
   have hvað_eq : padicValNat q (a ^ d - b ^ d) = padicValNat q (t ^ d) := by
     rw [heq]
   omega

 /--
-Honest squarefree-GN repair of `primitive_prime_obstructs_GN_perfect_power`.
+Honest squarefree-GN repair of `primitive_prime_factor_forbids_perfect_pow_diff`.

-This makes the repair plan explicit: the current obstruction theorem can be recovered cleanly once
-the caller provides `Squarefree (GN d (a - b) b)`.
+This is the migration shape for the two legacy callers in this file: if the caller can supply
+`Squarefree (GN d (a - b) b)`, the contradiction argument closes without the research placeholder.
 -/
-theorem primitive_prime_obstructs_GN_perfect_power_of_squarefree_GN
+theorem primitive_prime_factor_forbids_perfect_pow_diff_of_squarefree_GN
     {a b d : ℕ}
     (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
     (hab_lt : b < a) (hb : 0 < b) (hab : Nat.Coprime a b)
     (hpnd : ¬ d ∣ a - b)
     (hG_sq : Squarefree (GN d (a - b) b)) :
+    ¬ ∃ t : ℕ, 0 < t ∧ a ^ d - b ^ d = t ^ d := by
+  refine
+    primitive_prime_factor_forbids_perfect_pow_diff_of_noLift_GN
+      hd_prime hd_ge hab_lt hb hab hpnd ?_
+  intro q hq
+  have hd_pos : 0 < d := hd_prime.pos
+  have hGN_ne : GN d (a - b) b ≠ 0 :=
+    primitive_prime_GN_ne_zero hq hd_pos hab_lt
+  intro hq2_dvd
+  have hVal : padicValNat q (GN d (a - b) b) ≤ 1 :=
+    DkMath.NumberTheory.GcdNext.padicValNat_le_one_of_squarefree
+      hq.1 hGN_ne hG_sq
+  have h2_le : 2 ≤ padicValNat q (GN d (a - b) b) := by
+    exact
+      (@padicValNat_dvd_iff_le q (Fact.mk hq.1)
+        (GN d (a - b) b) 2 hGN_ne).1 hq2_dvd
+  exact (not_le_of_gt h2_le) hVal
+
+/--
+Honest local no-lift repair of `primitive_prime_obstructs_GN_perfect_power`.
+
+This is the direct obstruction route: a primitive witness exists, and if that
+witness does not lift to `q^2` on `GN`, then `GN` cannot be a perfect `d`-th
+power.
+-/
+theorem primitive_prime_obstructs_GN_perfect_power_of_noLift_GN
+    {a b d : ℕ}
+    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
+    (hab_lt : b < a) (hb : 0 < b) (hab : Nat.Coprime a b)
+    (hpnd : ¬ d ∣ a - b)
+    (hNoLift :
+      ∀ {q : ℕ}, PrimitivePrimeFactorOfDiffPow q a b d →
+        ¬ q ^ 2 ∣ GN d (a - b) b) :
     ¬ ∃ t : ℕ, GN d (a - b) b = t ^ d := by
   intro hpow
   have hd_pos : 0 < d := hd_prime.pos
@@ -448,15 +485,8 @@ theorem primitive_prime_obstructs_GN_perfect_power_of_squarefree_GN
       padicValNat q (a ^ d - b ^ d) = padicValNat q (GN d (a - b) b) :=
     primitive_prime_padic_eq_GN hq hd_pos hd1 hab_lt
   rcases hpow with ⟨t, ht⟩
-  have hdiff_ne : a ^ d - b ^ d ≠ 0 := by
-    have hd_ne : d ≠ 0 := Nat.pos_iff_ne_zero.mp hd_pos
-    exact Nat.sub_ne_zero_of_lt (Nat.pow_lt_pow_left hab_lt hd_ne)
-  have hGN_ne : GN d (a - b) b ≠ 0 := by
-    intro hGN0
-    have hfactor : a ^ d - b ^ d = (a - b) * GN d (a - b) b := by
-      simpa using pow_sub_pow_factor_cosmic_N (a := a) (b := b) (d := d) hd_pos hab_lt
-    rw [hfactor, hGN0, mul_zero] at hdiff_ne
-    exact hdiff_ne rfl
+  have hGN_ne : GN d (a - b) b ≠ 0 :=
+    primitive_prime_GN_ne_zero hq hd_pos hab_lt
   have ht_ne : t ≠ 0 := by
     intro ht0
     apply hGN_ne
@@ -476,8 +506,7 @@ theorem primitive_prime_obstructs_GN_perfect_power_of_squarefree_GN
       d = d * 1 := (Nat.mul_one d).symm
       _ ≤ d * padicValNat q t := Nat.mul_le_mul_left d hvt_ge
   have hpadic_bound_diff : padicValNat q (a ^ d - b ^ d) ≤ 1 :=
-    primitive_prime_padic_bound_diff_of_squarefree_GN
-      hd_prime hd_ge hab_lt hb hab hpnd hq hG_sq
+    primitive_prime_padic_bound_diff_of_noLift_GN hq hd_pos hd1 hab_lt (hNoLift hq)
   have hpadic_bound_GN : padicValNat q (GN d (a - b) b) ≤ 1 := by
     rw [← hpadic_eq_GN]
     exact hpadic_bound_diff
@@ -488,6 +517,36 @@ theorem primitive_prime_obstructs_GN_perfect_power_of_squarefree_GN
       _ ≤ 1 := hpadic_bound_GN
   omega

+/--
+Honest squarefree-GN repair of `primitive_prime_obstructs_GN_perfect_power`.
+
+This makes the repair plan explicit: the current obstruction theorem can be recovered cleanly once
+the caller provides `Squarefree (GN d (a - b) b)`.
+-/
+theorem primitive_prime_obstructs_GN_perfect_power_of_squarefree_GN
+    {a b d : ℕ}
+    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
+    (hab_lt : b < a) (hb : 0 < b) (hab : Nat.Coprime a b)
+    (hpnd : ¬ d ∣ a - b)
+    (hG_sq : Squarefree (GN d (a - b) b)) :
+    ¬ ∃ t : ℕ, GN d (a - b) b = t ^ d := by
+  refine
+    primitive_prime_obstructs_GN_perfect_power_of_noLift_GN
+      hd_prime hd_ge hab_lt hb hab hpnd ?_
+  intro q hq
+  have hd_pos : 0 < d := hd_prime.pos
+  have hGN_ne : GN d (a - b) b ≠ 0 :=
+    primitive_prime_GN_ne_zero hq hd_pos hab_lt
+  intro hq2_dvd
+  have hVal : padicValNat q (GN d (a - b) b) ≤ 1 :=
+    DkMath.NumberTheory.GcdNext.padicValNat_le_one_of_squarefree
+      hq.1 hGN_ne hG_sq
+  have h2_le : 2 ≤ padicValNat q (GN d (a - b) b) := by
+    exact
+      (@padicValNat_dvd_iff_le q (Fact.mk hq.1)
+        (GN d (a - b) b) 2 hGN_ne).1 hq2_dvd
+  exact (not_le_of_gt h2_le) hVal
+
 /-- Compatibility alias with explicit `d`-th-power wording. -/
 theorem primitive_prime_obstructs_GN_dth_power
     {a b d : ℕ}
diff --git a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
index b9fb7b57..2d5de34b 100644
--- a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
+++ b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
@@ -1367,12 +1367,18 @@ The generic no-lift valuation helper has also been promoted to
 primitive_prime_GN_ne_zero
 primitive_prime_padic_bound_diff_of_noLift_GN
 primitive_prime_padic_bound_diff_of_squarefree_GN_local
+primitive_prime_factor_forbids_perfect_pow_diff_of_noLift_GN
+primitive_prime_obstructs_GN_perfect_power_of_noLift_GN
 ```

 The local squarefree helper is a sufficient-condition wrapper over the no-lift
 helper.  The older heavier squarefree wrapper remains available for callers
 that still use the previous primitive-prime repair signature.

+The no-lift route now also reaches the perfect-power obstruction layer.  This
+gives downstream FLT/ABC code an honest replacement path for older research
+calls, provided it can supply local no-lift for the selected primitive witness.
+
 Meaning:

 ```text
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
index 0023c1fb..d0eb0e5e 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
@@ -382,12 +382,19 @@ The underlying local no-lift valuation helper is now available in
 primitive_prime_GN_ne_zero
 primitive_prime_padic_bound_diff_of_noLift_GN
 primitive_prime_padic_bound_diff_of_squarefree_GN_local
+primitive_prime_factor_forbids_perfect_pow_diff_of_noLift_GN
+primitive_prime_obstructs_GN_perfect_power_of_noLift_GN
 ```

 The older heavier squarefree wrapper is kept for compatibility, but the local
 route is now the canonical reading: squarefree `GN` supplies no-lift for the
 selected witness.

+The same local no-lift route also feeds the perfect-power obstruction layer:
+once the selected primitive witness has no `q^2` lift on `GN`, both the
+difference body and the `GN` side are prevented from being perfect `d`-th
+powers.
+
 ### `DkMath.Petal.Counting`

 Defines the fixed and dynamic counting layer.
````
`````
