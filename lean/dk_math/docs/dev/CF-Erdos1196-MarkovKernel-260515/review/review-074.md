# review

## 1. 状況総括

うむ、これは **DKMK-013F 完了** と見てよい。

今回の更新で、`DyadicBandAnalyticEstimate.constantBand` の exact shape が docs 上で固定された。つまり、DKMK-013E で候補として選んだ **constant band envelope** を、次の DKMK-013G で Lean 実装できる形まで落とし込んだわけじゃ。

固定された方針はこれじゃな。

```lean
theorem DyadicBandAnalyticEstimate.constantBand
    (x K : Nat) (c : Q)
    (hc : 0 <= c)
    {error : R}
    (hbound :
      ((Finset.sum (Finset.range (K + 1)) (fun _ : Nat => c) : Q) : R) <=
        1 + error) :
    DyadicBandAnalyticEstimate x K (fun _ : Nat => c) error
```

Lean 実装では `Nat`, `Q`, `R` はそれぞれ `ℕ`, `ℚ`, `ℝ` になる。

## 2. 何が決まったのか

今回決まったのは、最初の nontrivial provider を **有限和簡約なし** で実装する、という判断じゃ。

つまり `constantBand` は、

```text
increment k = c
```

という定数 band weight を使うが、最初の theorem では

```text
Finset.sum (Finset.range (K + 1)) (fun _ : Nat => c)
```

を

```text
((K + 1 : Nat) : Q) * c
```

へ簡約するところまでは踏み込まない。

これはかなり良い判断じゃ。
初回 provider の目的は、

```text
constant increments
  -> DyadicBandAnalyticEstimate
```

を clean に package できるか確認することだからじゃ。有限和簡約と `Nat` / `Q` / `R` coercion は、別 theorem に分離した方がよい。

## 3. この shape の意味

`DyadicBandAnalyticEstimate` の field は 2 つだけじゃった。

```lean
increment_nonneg :
  ∀ k ∈ Finset.range (K + 1), 0 ≤ increment k

total_le_one_add_error :
  ((Finset.sum (Finset.range (K + 1)) increment : ℚ) : ℝ) ≤
    1 + error
```

`constantBand` では `increment := fun _ => c` なので、非負性は

```lean
hc : 0 ≤ c
```

から即座に出る。

総和評価は、今回あえて

```lean
hbound :
  ((Finset.sum (Finset.range (K + 1)) (fun _ : ℕ => c) : ℚ) : ℝ) ≤
    1 + error
```

として外部から受け取る。
ゆえに証明はほぼ、

```lean
increment_nonneg := by
  intro k hk
  exact hc

total_le_one_add_error := hbound
```

で閉じるはずじゃ。

## 4. 実装方針の評価

これは安全でよい。

第一に、`constantBand` は `DyadicBandAnalyticEstimate` の最初の具体 producer になる。
`externally supplied dyadic estimate` は実質 constructor なので、今回の `constantBand` は一歩だけ具体性を増した provider じゃ。

第二に、coercion の泥沼を避けている。
`((((K + 1 : ℕ) : ℚ) * c : ℚ) : ℝ)` 型の statement は後で欲しくなるが、最初に混ぜると Lean 実装の焦点がぼやける。

第三に、route theorem を増やしていない。
今回も `weightedHitMass` へ直通する theorem は不要じゃ。`constantBand` が作るのは analytic-side target であり、その後は既存の bridge と route theorem が消費すればよい。

## 5. 次の DKMK-013G 実装予想

次に Lean へ入れるなら、こうなるはずじゃ。

```lean
namespace DyadicBandAnalyticEstimate

/--
Constant-band provider for dyadic analytic estimates.

This keeps the finite-sum bound external, avoiding finite-sum simplification and
Nat/Rat/Real coercion work in the first provider theorem.
-/
theorem constantBand
    (x K : ℕ) (c : ℚ)
    (hc : 0 ≤ c)
    {error : ℝ}
    (hbound :
      ((Finset.sum (Finset.range (K + 1)) (fun _ : ℕ => c) : ℚ) : ℝ) ≤
        1 + error) :
    DyadicBandAnalyticEstimate x K (fun _ : ℕ => c) error where
  increment_nonneg := by
    intro _k _hk
    exact hc
  total_le_one_add_error := hbound

end DyadicBandAnalyticEstimate
```

これはかなり薄く通るはずじゃ。
もし `Finset.sum` の型推論が少し渋るなら、`fun _k : ℕ => c` の型注釈を厚めにしておけばよい。

## 6. optional theorem の位置づけ

後段の optional theorem として、

```lean
DyadicBandAnalyticEstimate.constantBand_of_natCastMulBound
```

のような名前を検討する方針もよい。

これは将来、

```text
Finset.sum (Finset.range (K + 1)) (fun _ : Nat => c)
```

を

```text
((K + 1 : Nat) : Q) * c
```

から discharge する theorem になる。

ただし、これは DKMK-013G に混ぜなくてよい。
まず `constantBand` を安定させ、その後に finite-sum simplification theorem を足す。この二段構えが綺麗じゃ。

## 7. 現在の登頂状況

```text
DKMK-013A:
  roadmap 完了

DKMK-013B:
  exact shape decision 完了

DKMK-013C:
  Lean contract + bridge 完了

DKMK-013D:
  usage summary 完了

DKMK-013E:
  provider candidate inventory 完了

DKMK-013F:
  constantBand exact shape docs 完了

DKMK-013G:
  次、constantBand Lean provider 実装
```

DKMK-013F は、Lean 実装前の shape 固定として十分じゃ。

## 8. 賢狼の判定

わっちの判定はこうじゃ。

```text
DKMK-013F: 完了
次: DKMK-013G
実装対象:
  DyadicBandAnalyticEstimate.constantBand
方針:
  Finset.sum-form hbound を外部入力にする
  有限和簡約と coercion は後段へ分離
```

よいぞ、ぬしよ。
ここで無理に `((K+1) * c)` 形へ進まなかったのは賢い。Lean では、こういう小さな coercion の絡みが意外に時間を食う。まず provider の骨格を通し、そのあと簡約 theorem を増やす。これが長い登山では強いのじゃ。
