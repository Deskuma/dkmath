# Git diff / Report / Review

## Upd: DkMath.Pascal.WallisGrowthBridge

gch: ae50a014927950caf75a221b527bdecdc55360bc

## Report

レビュア指摘分を反映しました。

[WallisGrowthBridge.lean](/lean/dk_math/DkMath/Pascal/WallisGrowthBridge.lean) に追加:

```lean
isEquivalent_real_centralBinomial_four_pow_div_sqrt_pi_mul_nat
tendsto_real_centralBinomial_div_four_pow_div_sqrt_pi_mul_nat_one
```

前者は検索性重視の alias で、右辺が

```lean
(4 : ℝ) ^ m / Real.sqrt (Real.pi * (m : ℝ))
```

だと名前から分かるようにしています。後者は下流利用向けの operational ratio limit です。

```lean
Filter.Tendsto
  (fun m : ℕ =>
    ((Nat.choose (2 * m) m : ℕ) : ℝ) /
      ((4 : ℝ) ^ m / Real.sqrt (Real.pi * (m : ℝ))))
  Filter.atTop
  (nhds 1)
```

[cf-wallis-growth-route.md](/lean/dk_math/docs/dev/cf-wallis-bridge-260704/cf-wallis-growth-route.md) も同期し、この ratio limit を閉じた checkpoint として反映しました。

確認済み:

```text
lake build DkMath.Pascal.WallisGrowthBridge  OK
lake build DkMath.Pascal                    OK
lake build DkMath                           OK
git diff --check                            OK
Wallis 3 files sorry search                 no hits
```

`DkMath` 全体の既存 `sorry` 警告は従来通り別モジュール由来です。

## Review

_

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Pascal/WallisGrowthBridge.lean b/lean/dk_math/DkMath/Pascal/WallisGrowthBridge.lean
index ede0bb49..ec0e95b7 100644
--- a/lean/dk_math/DkMath/Pascal/WallisGrowthBridge.lean
+++ b/lean/dk_math/DkMath/Pascal/WallisGrowthBridge.lean
@@ -557,4 +557,41 @@ theorem isEquivalent_real_centralBinomial_sqrt_pi_mul_nat :
     exact IsEquivalent.div IsEquivalent.refl isEquivalent_real_centralRatioQ_sqrt_pi_mul_nat
   exact hfinite.isEquivalent.trans hratio
 
+/--
+Searchable alias for the central-binomial asymptotic.
+
+The longer name makes the denominator structure explicit:
+`4^m / sqrt (pi*m)`.
+-/
+theorem isEquivalent_real_centralBinomial_four_pow_div_sqrt_pi_mul_nat :
+    (fun m : ℕ => ((Nat.choose (2 * m) m : ℕ) : ℝ)) ~[Filter.atTop]
+      (fun m : ℕ => (4 : ℝ) ^ m / Real.sqrt (Real.pi * (m : ℝ))) :=
+  isEquivalent_real_centralBinomial_sqrt_pi_mul_nat
+
+/--
+Operational ratio form of the central-binomial growth law.
+
+This is the same asymptotic statement as
+`isEquivalent_real_centralBinomial_four_pow_div_sqrt_pi_mul_nat`, but exposed
+as a direct `Tendsto` theorem for downstream calculations.
+-/
+theorem tendsto_real_centralBinomial_div_four_pow_div_sqrt_pi_mul_nat_one :
+    Filter.Tendsto
+      (fun m : ℕ =>
+        ((Nat.choose (2 * m) m : ℕ) : ℝ) /
+          ((4 : ℝ) ^ m / Real.sqrt (Real.pi * (m : ℝ))))
+      Filter.atTop
+      (nhds 1) := by
+  have hden :
+      ∀ᶠ m : ℕ in Filter.atTop,
+        (4 : ℝ) ^ m / Real.sqrt (Real.pi * (m : ℝ)) ≠ 0 := by
+    filter_upwards [eventually_gt_atTop 0] with m hm
+    have hm_pos : 0 < (m : ℝ) := by exact_mod_cast hm
+    have hprod_pos : 0 < Real.pi * (m : ℝ) :=
+      mul_pos Real.pi_pos hm_pos
+    exact div_ne_zero (pow_ne_zero m (by norm_num : (4 : ℝ) ≠ 0))
+      (Real.sqrt_pos_of_pos hprod_pos).ne'
+  exact (isEquivalent_iff_tendsto_one hden).mp
+    isEquivalent_real_centralBinomial_four_pow_div_sqrt_pi_mul_nat
+
 end DkMath.Pascal.WallisGrowthBridge
diff --git a/lean/dk_math/docs/dev/cf-wallis-bridge-260704/cf-wallis-growth-route.md b/lean/dk_math/docs/dev/cf-wallis-bridge-260704/cf-wallis-growth-route.md
index 97cfdd2e..72d4b16d 100644
--- a/lean/dk_math/docs/dev/cf-wallis-bridge-260704/cf-wallis-growth-route.md
+++ b/lean/dk_math/docs/dev/cf-wallis-bridge-260704/cf-wallis-growth-route.md
@@ -143,6 +143,12 @@ theorem isEquivalent_real_centralBinomial_sqrt_pi_mul_nat :
     (fun m : Nat => (4 : R) ^ m / Real.sqrt (Real.pi * (m : R)))
 ```
 
+It also has a more explicit searchable alias:
+
+```lean
+theorem isEquivalent_real_centralBinomial_four_pow_div_sqrt_pi_mul_nat
+```
+
 This uses the finite inversion identities:
 
 ```lean
@@ -153,15 +159,26 @@ theorem real_nat_choose_two_mul_self_eq_pow_four_div_centralRatioQ
 and then divides `4^m ~ 4^m` by
 `centralRatioQ m ~ sqrt (Real.pi * m)`.
 
-## Next formal checkpoint
-
-The next theorem can package the same statement as an operational ratio limit:
+The fourth closed theorem packages the same statement as an operational ratio
+limit:
 
-```text
-Nat.choose (2*m) m / (4^m / sqrt (Real.pi * m)) -> 1
+```lean
+theorem tendsto_real_centralBinomial_div_four_pow_div_sqrt_pi_mul_nat_one :
+  Filter.Tendsto
+    (fun m : Nat =>
+      ((Nat.choose (2 * m) m : Nat) : R) /
+        ((4 : R) ^ m / Real.sqrt (Real.pi * (m : R))))
+    Filter.atTop
+    (nhds 1)
 ```
 
 This is equivalent to the `IsEquivalent` theorem above, but it is often easier
-for downstream users who want a direct `Tendsto` surface.  After that, the
-remaining work is presentation: expose a conventional Stirling-style theorem
-name while keeping the proof source explicitly Wallis-derived.
+for downstream users who want a direct `Tendsto` surface.
+
+## Next formal checkpoint
+
+The remaining work is presentation and downstream usability: expose a
+conventional Stirling-style theorem name while keeping the proof source
+explicitly Wallis-derived.  A useful follow-up is also to add short aliases
+for common RHS spellings, if downstream files expect a different arrangement
+of `4^m`, division, or square root.
````
`````
