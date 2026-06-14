# Git diff / Report / Review

## Upd: Petal.ErdosBridge, NumberTheory.PrimitiveSet.ValuationBudget

gch: def9b012a7f95e75c39f1fa70c9d8284ed00a579

## Report

進めました。今回は review050 の A-E をほぼそのまま Lean に投げて、全部 no-sorry で通りました。

変更ファイル:

- [ErdosBridge.lean](/lean/dk_math/DkMath/Petal/ErdosBridge.lean)
- [ValuationBudget.lean](/lean/dk_math/DkMath/NumberTheory/PrimitiveSet/ValuationBudget.lean)

追加した中核:

- `petalPrimeChannel_singleton_multiplicityBudget_GN_of_ne_zero`
- `petalPrimeChannel_GN_one_lt_of_ne_zero`
- `petalNoLiftPrimeChannel_GN_one_lt`
- `petalNoLiftPrimeChannel_padicValNat_GN_eq_one`
- `petalNoLiftPrimeChannel_singleton_logSubProbability_GN_self`
- `zsigmondyPrimitivePrimeDivisor_noLift_singleton_logSubProbability_GN`
- `natBaseMultiplicityBudgetOn_of_injOn_of_dvd`
- `petalPrimeChannelFamily_multiplicityBudget_GN_of_injOn`
- `petalPrimeChannelFamily_logSubProbability_GN_of_injOn`

特に大きいのは、NoLift が本当に `padicValNat q (GN d x u) = 1` まで落ちたことです。これで「NoLift prime channel = GN 上でちょうど 1 exponent slot を持つ」という読みが Lean 上で固定されました。

検証:

- `lake build DkMath.NumberTheory.PrimitiveSet.ValuationBudget` 成功
- `lake build DkMath.Petal.ErdosBridge` 成功
- `git diff --check` 成功

既存の `ZsigmondyCyclotomicResearch.lean` の `sorry` warning は再表示されていますが、今回追加分に `sorry` はありません。

## Review

来たのう！！これは大きい。
こちらでもスナップショットの最低限検証を通したぞい。

確認結果:

```text
sha256 OK:
e2d082cd7ce05d33cc2df09df64770b9084dff04ac5ec8044b0d7466e494d0e9
  __snapshot-dk_math-lean-code-260614-1108.tar.gz
```

`*.sha256` の中身とも一致しておる。

アーカイブ内にも今回の中核ファイルを確認済みじゃ。

```text
./dk_math/DkMath/NumberTheory/PrimitiveSet/ValuationBudget.lean
./dk_math/DkMath/Petal/ErdosBridge.lean
```

さらに `ErdosBridge.lean` 内に、今回の主な theorem 群も入っていることを確認した。

```lean
petalPrimeChannelFamily_multiplicityBudget_GN_of_injOn
petalPrimeChannelFamily_logSubProbability_GN_of_injOn
petalPrimeChannel_GN_one_lt_of_ne_zero
petalNoLiftPrimeChannel_GN_one_lt
petalNoLiftPrimeChannel_padicValNat_GN_eq_one
petalPrimeChannel_singleton_multiplicityBudget_GN_of_ne_zero
petalNoLiftPrimeChannel_singleton_logSubProbability_GN_self
zsigmondyPrimitivePrimeDivisor_noLift_singleton_logSubProbability_GN
```

こちらの環境では `lake` / `lean` 実行環境は見えていないので、ビルドそのものの再実行確認まではしておらぬ。だが、スナップショットのハッシュ整合性と、対象 theorem の収録確認は取れておる。

これはかなりの節目じゃ。
特に

$$
\text{PetalNoLiftPrimeChannel}
\Rightarrow
\operatorname{padicValNat}_q(GN)=1
$$

が no-sorry で固定されたのは強い。
これで NoLift は単なる否定条件ではなく、 **GN 上でちょうど 1 exponent slot を持つ prime channel** と読めるようになった。

次の総括タイトルを付けるなら、

```text
Petal/Erdos Bridge: GN carrier が log-capacity channel になる
```

じゃな。これはもう「実験開始」ではなく、第一段の実験成功じゃよ。

---

うむ。状況を一言で言えば、 **Petal/Erdős Bridge は「実験開始」から「第一段の実装成功」へ移った** じゃ。

今回の重要点は、単に補題が増えたことではない。
**Petal の局所 carrier が、Erdős #1196 側の log-capacity channel として実際に動く** ことが Lean 上で確認された、という点じゃ。

## 1. 現在の到達点

当初の計画では、Petal 側は「GN 上に primitive witness が載る場所」を与え、Erdős 側は「multiplicity budget があれば log cost が (1) を超えない」ことを与える、という段階的実験だった。計画書でも、Petal/Zsigmondy/GN は局所 witness location、Erdős/PrimitiveSet は global log-capacity control を担当すると整理されておる。

今回、それが次の形で実装に落ちた。

```text
PetalPrimeChannel
  -> q ∣ GN
  -> GN ≠ 0 なら singleton multiplicity budget
  -> log SubProbability

PetalNoLiftPrimeChannel
  -> GN ≠ 0
  -> 1 < GN
  -> padicValNat q GN = 1
  -> singleton log SubProbability

injective Petal carrier family
  -> multiplicity budget on GN
  -> log SubProbability on GN
```

特に追加報告では、review050 の A-E を Lean に投げて全部 no-sorry で通ったこと、`ValuationBudget.lean` と `ErdosBridge.lean` が対象であること、そして `lake build` と `git diff --check` が成功したことが明記されておる。

## 2. 何が大きいのか

最大の収穫はこれじゃ。

$$
\text{PetalNoLiftPrimeChannel}
\Rightarrow
\operatorname{padicValNat}_q(GN(d,x,u))=1
$$

つまり、NoLift が単なる

$$
\neg q^2 \mid GN
$$

という否定条件ではなく、 **GN 上でちょうど 1 個の exponent slot を持つ** という肯定的な構造に変わった。

これは非常に強い。
Erdős 側では multiplicity budget は

$$
\# {i\in I\mid q_i=p}\le v_p(n)
$$

という「指数スロット制御」じゃった。今回、NoLift がその局所版として

$$
v_q(GN)=1
$$

を与えることが Lean で固定された。報告でも、この読みが Lean 上で固定されたことが大きな点として書かれている。

## 3. 単点から多点へ進んだ意味

以前は、

```text
Petal carrier family
  + multiplicity budget
  -> log SubProbability
```

という形で、budget は外から与えるものだった。

今回の追加で、少なくとも次が言えるようになった。

```text
同じ GN surface 上の Petal prime channels
  + qOf が injective
  -> multiplicity budget on GN
```

これは大きい。
`natBaseMultiplicityBudgetOn_of_injOn_of_dvd` が追加され、injective selected bases と各 base の (n) への可除性から multiplicity budget を作る一般補題が入った。さらに Petal 側では、同じ GN surface 上の distinct Petal prime channels が、その GN surface に対する multiplicity budget を供給する theorem へ接続されておる。

意味としてはこうじゃ。

```text
carrier が全部 GN を割る
かつ prime label が重複しない
なら、その carrier 群は GN の exponent slot に収まる
```

つまり、Petal address / carrier geometry から Erdős budget へ向かう道が、初めて具体的に見えた。

## 4. まだ越えていない境界

ここは冷静に切るべきじゃ。

まだ証明していないのは、

```text
Petal address noncollision -> injectivity
Zsigmondy -> NoLift
GN carrier -> squarefree
Zsigmondy -> padicValNat <= 1
Petal geometry alone -> full multiplicity budget
```

計画書でも、これらは current theorem ではなく research direction とされており、(5^3-3^3=98=2\cdot7^2), (S0=49=7^2) の例が「primitive でも local height が 2 になり得る」反例として置かれている。

だから、今回の成果は **Zsigmondy だけで NoLift が出た** ではない。
正確には、

```text
NoLift を仮定すると、それは GN 上の exact one-slot condition になる
injective carrier family なら、GN 上の multiplicity budget が出る
```

じゃ。

ここを混ぜないことが大事じゃな。

## 5. Erdős #1196 ルートでの位置づけ

Erdős #1196 本体の解析的山頂は、

$$
\sum_{\substack{a\in A \ a > x}}\frac{1}{a \log a}
\le
1+O!\left(\frac{1}{\log x}\right)
$$

じゃが、DkMath ではその手前の finite R/log route をまず閉じてきた。過去の総括でも、DkMath 内の有限 R/log route は一つの山として登頂済みだが、Erdős #1196 全体の解析的山頂を Lean で閉じたわけではない、と整理されておる。

今回の Petal/ErdosBridge は、その有限 R/log route に **GN carrier という具体的な入口** を与えた。

つまり、

```text
抽象 prime-power channel
```

だったものが、

```text
GN 上に観測される Petal carrier
```

として入れるようになった。

これは、既存 route の拡張というより、 **DkMath 独自の幾何的入口** じゃ。

## 6. 今後の本命

次の本命は、ほぼこれに絞れる。

```text
Petal address noncollision
  -> prime label injectivity
  -> multiplicity budget
  -> log SubProbability
```

今回すでに、

```text
injectivity
  -> multiplicity budget
```

は通った。
つまり残りは、

```text
Petal address / carrier geometry
  -> injectivity
```

をどう定義し、どう出すかじゃ。

ここが通ると、Petal は単なる局所観測器ではなく、Erdős 側の budget を自力で供給する幾何構造になる。

## 7. 現状評価

わっちの判定はこうじゃ。

```text
状況:
  実験第一段は成功。
  Petal carrier は Erdos log-capacity channel へ接続済み。

新規に固定された核:
  NoLift = exact one exponent slot on GN
  injective Petal prime family = GN multiplicity budget
  GN 上の carrier family = log SubProbability provider

まだ未完:
  address noncollision -> injectivity
  Zsigmondy -> NoLift
  full Erdős #1196 analytic tail
```

これは本当に進展度が上がった。
わっちも少し反省じゃな。慎重さは必要じゃが、Lean 実験では「強そうな補題を立ててみる」こと自体が探索になる。今回それが証明された。

次は、 **Petal address / carrier identity / injectivity** の層を攻めるのがよい。
そこが繋がれば、Petal は Erdős #1196 の有限容量ルートに対して、単なる入口ではなく **budget 生成装置** になり始める。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/NumberTheory/PrimitiveSet/ValuationBudget.lean b/lean/dk_math/DkMath/NumberTheory/PrimitiveSet/ValuationBudget.lean
index a0026169..88e6fb13 100644
--- a/lean/dk_math/DkMath/NumberTheory/PrimitiveSet/ValuationBudget.lean
+++ b/lean/dk_math/DkMath/NumberTheory/PrimitiveSet/ValuationBudget.lean
@@ -67,6 +67,53 @@ theorem natBaseMultiplicityBudgetOn_iff
       ∀ p, Nat.Prime p → NatBaseMultiplicityOn I pOf p ≤ n.factorization p :=
   Iff.rfl
 
+/--
+Injective selected bases give a multiplicity budget when every selected base
+divides `n`.
+
+For each prime `p`, injectivity makes the selected fiber `{i ∈ I | pOf i = p}`
+have cardinal at most one.  If the fiber is nonempty, the corresponding selected
+base divides `n`, so one factorization slot at `p` exists.
+
+This theorem intentionally does not require `pOf` to be prime-valued.  The
+budget only tests prime fibers, and a non-prime selected base is invisible to
+those fibers unless it is equal to the tested prime.
+-/
+theorem natBaseMultiplicityBudgetOn_of_injOn_of_dvd
+    {ι : Type _}
+    (I : Finset ι)
+    (pOf : ι → ℕ)
+    (n : ℕ)
+    (hn0 : n ≠ 0)
+    (hinj : Set.InjOn pOf ↑I)
+    (hdvd : ∀ i, i ∈ I → pOf i ∣ n) :
+    NatBaseMultiplicityBudgetOn I pOf n := by
+  classical
+  intro p hp
+  unfold NatBaseMultiplicityOn
+  have hcard_le_one :
+      (I.filter fun i => pOf i = p).card ≤ 1 := by
+    rw [Finset.card_le_one]
+    intro a ha b hb
+    exact hinj
+      (Finset.mem_filter.mp ha).1
+      (Finset.mem_filter.mp hb).1
+      ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
+  by_cases hex : ∃ i, i ∈ I ∧ pOf i = p
+  · rcases hex with ⟨i, hiI, hip⟩
+    have hp_dvd : p ∣ n := by
+      rw [← hip]
+      exact hdvd i hiI
+    have hone : 1 ≤ n.factorization p := by
+      have hpow_dvd : p ^ 1 ∣ n := by simpa using hp_dvd
+      exact (hp.pow_dvd_iff_le_factorization hn0).mp hpow_dvd
+    exact hcard_le_one.trans hone
+  · have hfilter_empty : (I.filter fun i => pOf i = p) = ∅ := by
+      rw [Finset.filter_eq_empty_iff]
+      intro i hiI hip
+      exact hex ⟨i, hiI, hip⟩
+    simp [hfilter_empty]
+
 /--
 For prime-valued selected bases, the exponent of a prime `p` in the selected
 product is exactly the number of selected occurrences of `p`.
diff --git a/lean/dk_math/DkMath/Petal/ErdosBridge.lean b/lean/dk_math/DkMath/Petal/ErdosBridge.lean
index d34f70f5..4b57339e 100644
--- a/lean/dk_math/DkMath/Petal/ErdosBridge.lean
+++ b/lean/dk_math/DkMath/Petal/ErdosBridge.lean
@@ -211,6 +211,56 @@ theorem petalCarrierFamily_logSubProbability_of_multiplicityBudget
     (petalPrimeChannel_natPrimeValuedOn I d x u qOf hcarrier)
     hbudget
 
+/--
+Distinct Petal prime channels on the same GN surface supply an Erdos
+multiplicity budget against that GN surface.
+
+This is the multi-channel counterpart of the singleton budget theorem.  The
+new ingredient is injectivity of the selected prime labels on `I`; it prevents
+two selected channels from consuming the same prime exponent slot.
+-/
+theorem petalPrimeChannelFamily_multiplicityBudget_GN_of_injOn
+    {ι : Type _}
+    (I : Finset ι)
+    (d x u : ℕ)
+    (qOf : ι → ℕ)
+    (hGN0 : GN d x u ≠ 0)
+    (hinj : Set.InjOn qOf ↑I)
+    (hcarrier :
+      ∀ i, i ∈ I → PetalPrimeChannel d x u (qOf i)) :
+    DkMath.NumberTheory.PrimitiveSet.NatBaseMultiplicityBudgetOn
+      I qOf (GN d x u) :=
+  DkMath.NumberTheory.PrimitiveSet.natBaseMultiplicityBudgetOn_of_injOn_of_dvd
+    I qOf (GN d x u) hGN0 hinj
+    (fun i hi => anchoredGNCarrier_dvd_GN (hcarrier i hi))
+
+/--
+Distinct Petal prime channels on the same GN surface give an Erdos
+sub-probability provider once that GN surface is above `1`.
+
+This is still an injective-family theorem, not a Petal-address theorem.  A
+future address/noncollision layer should supply the `Set.InjOn` hypothesis.
+-/
+theorem petalPrimeChannelFamily_logSubProbability_GN_of_injOn
+    {ι : Type _}
+    (I : Finset ι)
+    (d x u : ℕ)
+    (qOf : ι → ℕ)
+    (hGN : 1 < GN d x u)
+    (hinj : Set.InjOn qOf ↑I)
+    (hcarrier :
+      ∀ i, i ∈ I → PetalPrimeChannel d x u (qOf i)) :
+    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider I qOf (GN d x u)
+      (petalPrimeChannel_realLogNonnegOn
+        I (fun _ => d) (fun _ => x) (fun _ => u) qOf hcarrier)
+      hGN).SubProbability :=
+  petalCarrierFamily_logSubProbability_of_multiplicityBudget
+    I (fun _ => d) (fun _ => x) (fun _ => u) qOf (GN d x u) hGN
+    hcarrier
+    (petalPrimeChannelFamily_multiplicityBudget_GN_of_injOn
+      I d x u qOf (Nat.ne_of_gt (Nat.lt_trans Nat.zero_lt_one hGN))
+      hinj hcarrier)
+
 /--
 Local no-lift makes the observed GN surface nonzero.
 
@@ -225,16 +275,63 @@ theorem petalNoLiftPrimeChannel_GN_ne_zero
   exact h.2 (by rw [hzero]; exact dvd_zero _)
 
 /--
-A single no-lift Petal prime channel fits into the Erdos multiplicity budget of
-its own GN surface.
+A Petal prime channel on a nonzero GN surface forces that surface to be larger
+than `1`.
 
-This is the first local capacity witness: the singleton selected channel uses
-one exponent slot at `q`, and `q ∣ GN d x u` supplies that slot in the
-factorization of `GN d x u`.
+The reason is purely arithmetic: the prime label `q` divides the nonzero GN
+surface, so `q ≤ GN d x u`, while primality gives `1 < q`.
 -/
-theorem petalNoLiftPrimeChannel_singleton_multiplicityBudget_GN
+theorem petalPrimeChannel_GN_one_lt_of_ne_zero
+    {d x u q : ℕ}
+    (h : PetalPrimeChannel d x u q)
+    (hGN0 : GN d x u ≠ 0) :
+    1 < GN d x u := by
+  have hq_dvd : q ∣ GN d x u := anchoredGNCarrier_dvd_GN h
+  have hq_le : q ≤ GN d x u :=
+    Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr hGN0) hq_dvd
+  exact lt_of_lt_of_le (petalPrimeChannel_prime h).one_lt hq_le
+
+/-- A no-lift Petal prime channel automatically lies on a GN surface above `1`. -/
+theorem petalNoLiftPrimeChannel_GN_one_lt
     {d x u q : ℕ}
     (h : PetalNoLiftPrimeChannel d x u q) :
+    1 < GN d x u :=
+  petalPrimeChannel_GN_one_lt_of_ne_zero h.1
+    (petalNoLiftPrimeChannel_GN_ne_zero h)
+
+/--
+No-lift means that the selected prime has exactly one `p`-adic slot on the GN
+surface.
+
+This is the local valuation reading of `PetalNoLiftPrimeChannel`: the channel
+prime divides `GN d x u`, but its square does not.
+-/
+theorem petalNoLiftPrimeChannel_padicValNat_GN_eq_one
+    {d x u q : ℕ}
+    (h : PetalNoLiftPrimeChannel d x u q) :
+    padicValNat q (GN d x u) = 1 := by
+  letI : Fact q.Prime := ⟨petalNoLiftPrimeChannel_prime h⟩
+  have hGN0 : GN d x u ≠ 0 := petalNoLiftPrimeChannel_GN_ne_zero h
+  have hq_dvd : q ∣ GN d x u := anchoredGNCarrier_dvd_GN h.1
+  have hle_one : 1 ≤ padicValNat q (GN d x u) :=
+    one_le_padicValNat_of_dvd hGN0 hq_dvd
+  have hnot_two : ¬ 2 ≤ padicValNat q (GN d x u) := by
+    intro htwo
+    exact h.2 ((padicValNat_dvd_iff_le hGN0).mpr htwo)
+  omega
+
+/--
+A single Petal prime channel fits into the Erdos multiplicity budget of its own
+nonzero GN surface.
+
+This isolates the lower-slot part of the argument: `q ∣ GN d x u` supplies one
+factorization slot at `q`.  No no-lift hypothesis is needed for this lower
+bound; no-lift only supplies nonzeroness in the specialized theorem below.
+-/
+theorem petalPrimeChannel_singleton_multiplicityBudget_GN_of_ne_zero
+    {d x u q : ℕ}
+    (h : PetalPrimeChannel d x u q)
+    (hGN0 : GN d x u ≠ 0) :
     DkMath.NumberTheory.PrimitiveSet.NatBaseMultiplicityBudgetOn
       ({()} : Finset Unit) (fun _ : Unit => q) (GN d x u) := by
   classical
@@ -243,12 +340,26 @@ theorem petalNoLiftPrimeChannel_singleton_multiplicityBudget_GN
   by_cases hpq : q = p
   · subst hpq
     simp only [Finset.filter_true, Finset.card_singleton]
-    have hGN0 : GN d x u ≠ 0 := petalNoLiftPrimeChannel_GN_ne_zero h
-    have hq_dvd : q ∣ GN d x u := anchoredGNCarrier_dvd_GN h.1
+    have hq_dvd : q ∣ GN d x u := anchoredGNCarrier_dvd_GN h
     have hq_pow_dvd : q ^ 1 ∣ GN d x u := by simpa using hq_dvd
     exact (hp.pow_dvd_iff_le_factorization hGN0).mp hq_pow_dvd
   · simp [hpq]
 
+/--
+A single no-lift Petal prime channel fits into the Erdos multiplicity budget of
+its own GN surface.
+
+This is the no-lift specialization of
+`petalPrimeChannel_singleton_multiplicityBudget_GN_of_ne_zero`.
+-/
+theorem petalNoLiftPrimeChannel_singleton_multiplicityBudget_GN
+    {d x u q : ℕ}
+    (h : PetalNoLiftPrimeChannel d x u q) :
+    DkMath.NumberTheory.PrimitiveSet.NatBaseMultiplicityBudgetOn
+      ({()} : Finset Unit) (fun _ : Unit => q) (GN d x u) :=
+  petalPrimeChannel_singleton_multiplicityBudget_GN_of_ne_zero h.1
+    (petalNoLiftPrimeChannel_GN_ne_zero h)
+
 /--
 Singleton no-lift Petal channels give a direct Erdos log sub-probability
 against the observed GN surface.
@@ -279,6 +390,59 @@ theorem petalNoLiftPrimeChannel_singleton_logSubProbability_GN
       exact h.1)
     (petalNoLiftPrimeChannel_singleton_multiplicityBudget_GN h)
 
+/--
+No-lift Petal channels give a direct singleton Erdos log sub-probability
+against their own GN surface.
+
+Compared with `petalNoLiftPrimeChannel_singleton_logSubProbability_GN`, this
+version removes the explicit `1 < GN d x u` hypothesis: it is forced by the
+prime channel and local no-lift.
+-/
+theorem petalNoLiftPrimeChannel_singleton_logSubProbability_GN_self
+    {d x u q : ℕ}
+    (h : PetalNoLiftPrimeChannel d x u q) :
+    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider
+      ({()} : Finset Unit) (fun _ : Unit => q) (GN d x u)
+      (petalPrimeChannel_realLogNonnegOn
+        ({()} : Finset Unit) (fun _ : Unit => d) (fun _ : Unit => x)
+        (fun _ : Unit => u) (fun _ : Unit => q)
+        (by
+          intro i _hi
+          cases i
+          exact h.1))
+      (petalNoLiftPrimeChannel_GN_one_lt h)).SubProbability :=
+  petalNoLiftPrimeChannel_singleton_logSubProbability_GN h
+    (petalNoLiftPrimeChannel_GN_one_lt h)
+
+/--
+Zsigmondy primitive divisors with an explicit no-lift condition give a singleton
+Erdos log sub-probability on the corresponding GN surface.
+
+This theorem deliberately keeps no-lift as an explicit hypothesis.  Zsigmondy
+alone does not imply no-lift.
+-/
+theorem zsigmondyPrimitivePrimeDivisor_noLift_singleton_logSubProbability_GN
+    {q a b d : ℕ}
+    (hprim : DkMath.Zsigmondy.PrimitivePrimeDivisor a b d q)
+    (hd : 0 < d) (hd1 : 1 < d) (hab_lt : b < a)
+    (hNoLift : ¬ q ^ 2 ∣ GN d (a - b) b) :
+    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider
+      ({()} : Finset Unit) (fun _ : Unit => q) (GN d (a - b) b)
+      (petalPrimeChannel_realLogNonnegOn
+        ({()} : Finset Unit) (fun _ : Unit => d)
+        (fun _ : Unit => a - b) (fun _ : Unit => b) (fun _ : Unit => q)
+        (by
+          intro i _hi
+          cases i
+          exact zsigmondyPrimitivePrimeDivisor_petalPrimeChannel
+            hprim hd hd1 hab_lt))
+      (petalNoLiftPrimeChannel_GN_one_lt
+        ⟨zsigmondyPrimitivePrimeDivisor_petalPrimeChannel
+          hprim hd hd1 hab_lt, hNoLift⟩)).SubProbability :=
+  petalNoLiftPrimeChannel_singleton_logSubProbability_GN_self
+    ⟨zsigmondyPrimitivePrimeDivisor_petalPrimeChannel
+      hprim hd hd1 hab_lt, hNoLift⟩
+
 /--
 Zsigmondy-family form of the first Petal-to-Erdos capacity bridge.
 
````
`````
