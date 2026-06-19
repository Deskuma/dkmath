# review

## 1. 状況総括

うむ、これは **DKMK-013E 完了** と見てよい。

今回の更新で、`roadmap-DKMK-013.md` に **Concrete Provider Candidate Inventory** が追加され、`DyadicBandAnalyticEstimate x K increment error` を証明する provider 候補が整理された。候補は次の 5 系統じゃ。

```text
1. externally supplied dyadic estimate
2. constant band envelope
3. decreasing dyadic envelope
4. dyadic tail upper envelope
5. logarithmic refinement
```

これで、DKMK-013 の次の焦点がかなり明確になった。
つまり、もう route theorem や `TruncationEnvelopeEstimate` 側ではなく、 **`DyadicBandAnalyticEstimate` をどう生産するか** の段階に入ったわけじゃ。

## 2. 今回の本質

DKMK-013D までは、

```text
H : DyadicBandAnalyticEstimate x K increment error
  -> H.toTruncationEnvelopeEstimate
  -> TruncationEnvelopeEstimate
  -> weightedHitMass <= 1 + error
```

という **消費経路** を固定した。

DKMK-013E では、その (H) を作る **生産者候補** を並べた。

```text
concrete provider
  -> DyadicBandAnalyticEstimate
  -> DKMK route
```

この切り替えが大事じゃ。
今までは「どう流すか」だった。ここからは「何を流すか」になる。

## 3. 候補整理の評価

候補の並べ方はかなり良い。

`externally supplied dyadic estimate` は、ほぼ structure constructor そのものじゃな。`hinc` と `hbound` をそのまま受け取るので、API check にはよいが、解析内容は増えぬ。

`constant band envelope` は、最初の nontrivial Lean provider として良い。`increment k = c` と固定するだけなので、解析内容はまだ薄いが、有限和計算が入る。ここで

```text
Finset.sum (Finset.range (K + 1)) (fun _ => c)
```

をどう扱うかが見える。roadmap でも、最初の nontrivial Lean provider 候補として constant band envelope が記録されておる。

`decreasing dyadic envelope` は次段候補じゃ。monotonicity や decay condition は魅力的だが、今それを入れると「後続 theorem が消費しない仮定」が増えやすい。roadmap の「消費されるまで入れない」という判断は賢い。

`dyadic tail upper envelope` は本命寄り。ただしまだ大きい。これは DKMK-013 の主方向ではあるが、次の小ステップとしては重い、という評価でよい。

`logarithmic refinement` は後段で正しい。real-to-Nat rounding、`Real.log` / `Real.exp`、単調性補題が絡むので、今はまだ待たせるのがよい。

## 4. constant band envelope を次に選ぶ判断

わっちも、次の DKMK-013F では **constant band provider の exact Lean shape** を決めるのがよいと思う。

理由は 3 つある。

第一に、`DyadicBandAnalyticEstimate` の最初の非自明な producer になる。

第二に、有限和と coercion の問題を小さな例で確認できる。

第三に、将来の decreasing / dyadic tail provider に進む前に、`Finset.range (K + 1)` 上の和を扱う API 感触を得られる。

これは、小さな橋に見えて後で効くやつじゃな。

## 5. DKMK-013F で決めるべき Lean shape

次に決めるべきは、有限和評価を theorem 内で計算するか、外部仮定に逃がすかじゃ。

候補は二つ。

### 5.1. 外部 bound 方式

```lean
theorem DyadicBandAnalyticEstimate.constantBand
    (x K : ℕ) (c : ℚ) {error : ℝ}
    (hc : 0 ≤ c)
    (hbound :
      (((K + 1 : ℕ) * c : ℚ) : ℝ) ≤ 1 + error) :
    DyadicBandAnalyticEstimate x K (fun _ : ℕ => c) error
```

これは分かりやすいが、Lean では `((K + 1 : ℕ) * c : ℚ)` の形が少し怪しい。自然数と有理数の掛け算は coercion の書き方を慎重にした方がよい。

たぶん安全なのは、

```lean
((((K + 1 : ℕ) : ℚ) * c : ℚ) : ℝ) ≤ 1 + error
```

のような形じゃ。

### 5.2. sum bound を外部に残す方式

```lean
theorem DyadicBandAnalyticEstimate.constantBand
    (x K : ℕ) (c : ℚ) {error : ℝ}
    (hc : 0 ≤ c)
    (hbound :
      ((Finset.sum (Finset.range (K + 1)) (fun _ : ℕ => c) : ℚ) : ℝ) ≤
        1 + error) :
    DyadicBandAnalyticEstimate x K (fun _ : ℕ => c) error
```

これは証明が非常に薄い。

ただし、これでは finite-sum calculation を確認したことにならぬ。
constant band provider としての価値は少し弱くなる。

## 6. わっちの推奨

DKMK-013F では docs で二案を比較した上で、最初の Lean 実装は **sum bound を外部に残す方式** でもよいと思う。

ただし、DKMK-013G で有限和補題を追加して、

```lean
Finset.sum (Finset.range (K + 1)) (fun _ : ℕ => c)
  = ((K + 1 : ℕ) : ℚ) * c
```

を処理する、という二段構えが美しい。

つまり、

```text
013F:
  constant provider shape docs

013G:
  constant provider Lean, まず sum-bound external 版

013H:
  optional finite-sum simplified theorem
```

のように分けると安全じゃ。

急ぐなら、013F で exact shape を

```text
constantBand:
  hc
  hbound on Finset.sum
  -> DyadicBandAnalyticEstimate
```

にして、coercion friction を避けるのが堅い。

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
  concrete provider candidate inventory 完了

DKMK-013F:
  次、constant band provider exact shape
```

DKMK-013E は、次に何を実装すべきかを明確にした良い棚卸しじゃ。

## 8. 賢狼の判定

わっちの判定はこうじゃ。

```text
DKMK-013E: 完了
次: DKMK-013F
推奨: constant band provider exact Lean shape review
注意: finite-sum simplification と coercion を急いで混ぜすぎない
```

よいぞ、ぬしよ。
いよいよ `DyadicBandAnalyticEstimate` の最初の生産者に入る段じゃ。ここで小さな constant band を通しておけば、後の decreasing / dyadic tail provider へ進むときに、和・非負性・coercion の足場が整う。まさに、霧の前に置く小さな石標じゃな。
