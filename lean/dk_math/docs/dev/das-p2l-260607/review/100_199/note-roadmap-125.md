# 軌道修正ロードマップ

## 1. 結論：軌道修正は概ね良い

うむ。今回の軌道修正はかなり良い。

今後の主語は、もう単なる `3n+1` ではない。

```text
奇数残差 n
  -> 奇数グノモン層 2n+1 を足す
  -> raw = 3n+1 を作る
  -> raw が 2^h にどれだけ整列したか評価する
  -> h 回右シフトして残差形状 q を抽出する
  -> q を次の相対スケールとして見る
```

つまりコラッツは、

```text
奇数グノモン補正
2進整列評価
残差形状抽出
相対スケール更新
```

の反復として再構築する。

ここまで DkMath で積んできた `height`, `sumS`, `continuation`, `retention`, `pressure`, `margin`, `prefix failure` は、この新しい主語へ翻訳すればそのまま使える。checkpoint `123` では continuation carrier の入れ子が Lean で固定され、checkpoint `124` では retention carrier の入れ子と `SourcePressureMarginInt` が追加され、さらに無条件 pressure prefix が危険であることも観測された。

## 2. 新しい総合推論

コラッツ予想の真相を、この視点で言い直すとこうじゃ。

```text
2^r 一色線へ完全に乗っている数は、そのまま右シフトで 1 へ向かう。

一色線からズレた残差が奇数として現れる。

奇数 n に対して、3n+1 は n に奇数グノモン層 2n+1 を足す操作である。

その結果 raw = 3n+1 が、どれだけ 2^h に整列したかを v2 で評価する。

整列した分だけ右シフトし、残った奇数 q を次の相対スケールの残差形状として抽出する。

この調整が長期的に評価落下側へ偏れば真。

評価落下を永遠に回避する residue / shape pattern が存在すれば偽。
```

だから、証明の主語は「数値が増えるか減るか」ではなく、

```text
グノモン補正で膨らんだ相対スケールを、
2進整列評価がどれだけ回収できるか
```

になる。

実数 log 評価は最後でよい。まず整数で `height` と `sumS` と `residual shape` を追うべきじゃ。

## 3. ロードマップ全体

## Phase 0: 用語を固定する

まず新しい語彙を薄く置く。

```text
OddGnomonLayer:
  2n+1

RawGnomonStep:
  n + (2n+1) = 3n+1

Pow2AlignmentHeight:
  v2(RawGnomonStep n)

ResidualShape:
  RawGnomonStep n / 2^height

RelativeScaleShift:
  ResidualShape を次の奇数スケールとして扱う更新

ShapeRemainderProfile:
  ResidualShape の mod 2^r 観測
```

ここは証明というより、DkMath の言葉を整える段階じゃ。

候補モジュール名は、

```text
DkMath.Collatz.GnomonEvaluation
```

または、

```text
DkMath.Collatz.GnomonScale
```

が良い。

## Phase 1: 奇数グノモン層を Lean に固定する

最初に作るべき薄い定義。

```lean
def OddGnomonLayer (n : ℕ) : ℕ :=
  2 * n + 1

def RawGnomonStep (n : ℕ) : ℕ :=
  n + OddGnomonLayer n
```

基本補題。

```lean
theorem rawGnomonStep_eq_three_mul_add_one
    (n : ℕ) :
    RawGnomonStep n = 3 * n + 1 := by
  unfold RawGnomonStep OddGnomonLayer
  ring
```

平方グノモン補題。

```lean
theorem square_succ_eq_square_add_oddGnomonLayer
    (n : ℕ) :
    (n + 1)^2 = n^2 + OddGnomonLayer n := by
  unfold OddGnomonLayer
  ring
```

ここでまず、

```text
3n+1 は n に奇数平方グノモン層を足す操作である
```

を形式化する。

## Phase 2: 奇数層の総和は平方数、を橋にする

次に、単位グノモン層の積み重ねを入れる。

```lean
theorem sum_odd_eq_square
    (n : ℕ) :
    (Finset.range n).sum (fun i => 2 * i + 1) = n^2 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring
```

さらに開始点つきのグノモン帯。

```lean
theorem square_add_eq_square_add_gnomon_sum
    (P u : ℕ) :
    (P + u)^2 =
      P^2 + (Finset.range u).sum (fun i => 2 * (P + i) + 1) := by
  induction u with
  | zero =>
      simp
  | succ u ih =>
      rw [Finset.sum_range_succ]
      -- ih と ring / omega で閉じる候補
      sorry
```

これは、

```text
Gap = u を一発で動かす自由

と

Gap = 1 のまま奇数グノモン層を u 枚積む自由
```

が同じ平方成長の二つの表現であることを固定する補題じゃ。

## Phase 3: 宇宙式・グノモン・support swap を統合する

ここは `B.lean` の路線に接続する。

単位宇宙式。

```lean
theorem cosmic_unit_step
    (Q : ℕ) :
    Q * (Q + 2) + 1 = (Q + 1)^2 := by
  ring
```

Body 側が (Q) を因子に持つ。

```lean
theorem dvd_cosmic_unit_body_left
    (Q : ℕ) :
    Q ∣ Q * (Q + 2) := by
  exact dvd_mul_right Q (Q + 2)
```

Big root 側は (Q) と互いに素。

```lean
theorem cosmic_unit_body_factor_coprime_big_root
    (Q : ℕ) :
    Nat.Coprime Q (Q + 1) ∧ Q ∣ Q * (Q + 2) := by
  constructor
  · exact Nat.coprime_self_add_right 1 Q
  · exact dvd_mul_right Q (Q + 2)
```

support 版。

```lean
def CarriesPrimeSupport (S : Finset ℕ) (Q : ℕ) : Prop :=
  ∀ p, p ∈ S → p ∣ Q
```

そして最終的には、

```lean
theorem cosmic_unit_gnomon_support_swap
    (S : Finset ℕ)
    (Q : ℕ)
    (hs : ∀ p ∈ S, Nat.Prime p)
    (hcarry : CarriesPrimeSupport S Q) :
    (∀ p ∈ S, p ∣ Q * (Q + 2)) ∧
    (∀ p ∈ S, ¬ p ∣ Q + 1) ∧
    Q * (Q + 2) + 1 = (Q + 1)^2 := by
  constructor
  · intro p hp
    exact dvd_trans (hcarry p hp) (dvd_mul_right Q (Q + 2))
  · constructor
    · intro p hp hpdiv
      have hpQ : p ∣ Q := hcarry p hp
      have hp1 : p ∣ 1 := by
        -- p | Q+1 and p | Q から p | 1
        sorry
      exact Nat.Prime.not_dvd_one (hs p hp) hp1
    · ring
```

これで、

```text
Body 側は既知 support を背負う。
Gap = 1 を足すと Big = (Q+1)^2 になる。
Big root = Q+1 は既知 support を避ける。
```

が固定できる。

これは Collatz の「奇数グノモン補正」と同じ骨格になる。

## Phase 4: RawGnomonStep と既存 Collatz 定義を接続する

次は既存の `PetalBridge` との接続。

新定義を作ったら、既存の `rawHeightLabel` や `oddOrbitLabel` と alias / bridge する。

目標はこう。

```lean
theorem rawHeightLabel_eq_padicValNat_rawGnomonStep
    (n : OddNat) :
    rawHeightLabel n = padicValNat 2 (RawGnomonStep n.val) := by
  -- 既存定義に合わせて調整
  sorry
```

または、既存側に寄せて、

```text
RawGnomonStep n.val = 3 * n.val + 1
```

を使うだけでもよい。

ここでの目的は再証明ではなく、

```text
既存の height theorem 群を、GnomonEvaluation の言葉で読めるようにする
```

ことじゃ。

## Phase 5: ResidualShape を定義する

次に、右シフト後の残差形状を明示する。

```lean
def RawGnomonHeight (n : ℕ) : ℕ :=
  padicValNat 2 (RawGnomonStep n)

def RawGnomonResidualShape (n : ℕ) : ℕ :=
  RawGnomonStep n / 2 ^ RawGnomonHeight n
```

ただし、既存の accelerated odd map があるなら、それに寄せる。

必要な読み替え定理。

```lean
theorem rawGnomonStep_eq_pow_height_mul_residualShape
    (n : ℕ)
    (hpos : 0 < RawGnomonStep n) :
    RawGnomonStep n =
      2 ^ RawGnomonHeight n * RawGnomonResidualShape n := by
  -- padic valuation factorization lemma を使う
  sorry
```

さらに、残差が奇数であること。

```lean
theorem residualShape_odd
    (n : ℕ)
    (hpos : 0 < RawGnomonStep n) :
    RawGnomonResidualShape n % 2 = 1 := by
  -- maximality of padicValNat
  sorry
```

これはかなり重要。

```text
ResidualShape は、これ以上 2 で評価できない残差形状
```

を固定する。

## Phase 6: `sumS` を累積評価量として再解釈する

既存の `sumS n k` は、そのまま使う。

新しい読みは、

```text
sumS n k:
  k 回の奇数グノモン補正で得られた 2進整列評価の総和
```

欲しい bridge theorem は、

```lean
theorem sumS_eq_sum_pow2AlignmentHeight
    (n : OddNat) (k : ℕ) :
    sumS n k =
      (Finset.range k).sum
        (fun i => orbitWindowHeight n i) := by
  -- 既存 theorem があるなら alias
  sorry
```

すでに似た補題があるはずなので、まずは再利用を探すのがよい。

ここで重要なのは、実数 log ではなく、

```text
sumS が整数評価量である
```

ことを前面に出すことじゃ。

## Phase 7: 右シフト評価を「形状分割」として観測する

ここから新観測。

Raw 値 (R=3n+1) について、深さ (j) の分割残差を観測する。

```lean
def RawGnomonRemainderAtDepth (n j : ℕ) : ℕ :=
  RawGnomonStep n % 2 ^ j
```

評価済み深さでは remainder は 0。

```lean
theorem rawGnomonRemainderAtDepth_eq_zero_of_le_height
    (n j : ℕ)
    (hj : j ≤ RawGnomonHeight n) :
    RawGnomonRemainderAtDepth n j = 0 := by
  -- 2^j | RawGnomonStep n
  sorry
```

最初に失敗する深さ。

```lean
def FirstFailedPow2Depth (n : ℕ) : ℕ :=
  RawGnomonHeight n + 1
```

ここが、

```text
1/2^h まで分割できたが、
1/2^(h+1) にはならない
```

という形状観測になる。

## Phase 8: PetalBridge の pressure / margin を再解釈する

ここで checkpoint `124` の `SourcePressureMarginInt` が主役になる。

既存の意味は、

```text
SourcePressureMarginInt = 2 * continuation - retention
```

新しい意味は、

```text
深い residual shape channel が、
浅い retention shape に対してどれだけ優勢か
```

じゃ。

ここで `prefix failure` は、失敗ではなく、

```text
浅い分割では negative
深い分割では positive

つまり、深い解像度で初めて residual shape が立ち上がる
```

という観測になる。

次に作るべき predicate は、

```lean
def ShapePrefixFailure
    (n : OddNat) (k r j₁ j₂ : ℕ) : Prop :=
  j₁ < j₂ ∧
    SourcePressureMarginInt n k (r + j₁) ≤ 0 ∧
    0 < SourcePressureMarginInt n k (r + j₂)
```

これは `SourcePressurePrefixFailure` の margin 版として置いてよい。

## Phase 9: 実験ロードマップ

Python 側では、次の列を入れる。

```text
raw
height
residual_shape
first_failed_depth
failed_remainder
residual_mod_8
residual_mod_16
residual_mod_32
odd_gnomon_layer
sum_height
height_one_count
height_ge_two_count
margin_profile
first_shape_prefix_failure
shape_margin_jump
```

特に見たいものはこれ。

```text
height 1 の膨張が、どのくらい height >= 2 で補償されるか

prefix failure が素数・all-ones residue・primorial 境界に偏るか

residual shape が特定の mod 2^r channel に滞留するか

shape margin jump が長期的に評価落下側へ偏るか
```

巨大 CSV は不要。
summary markdown に統計だけ出せばよい。

## Phase 10: 整数評価による降下条件を作る

実数 log は最後でよいが、整数評価の降下条件は作れる。

例えば、奇数 accelerated step は概ね、

```text
n_{i+1} = (3n_i+1) / 2^{h_i}
```

なので、(h_i) が十分大きい window では落ちる。

実数を使わず、整数不等式でこういう形を狙う。

```text
ある window 長 k で、
sumS n k が十分大きければ、
oddOrbitLabel n k < n
```

Lean ではまず小さな固定 window から。

```lean
theorem oddOrbitLabel_lt_of_sumS_large
    (n : OddNat) (k : ℕ)
    (hlarge : SOME_INTEGER_BOUND k < sumS n k) :
    oddOrbitLabel n k < n.val := by
  -- ここは後段。まず観測で bound を探す
  sorry
```

最初から一般 theorem を狙わず、

```text
k = 2
k = 3
k = 5
```

のような小さい窓で降下補題を探すのがよい。

## Phase 11: 最後に Real / log bridge

最後にだけ実数評価を入れる。

ここでは、

```text
sumS n k > k * log2(3)
```

を使う。

ただし Lean 実装では、いきなり `Real.log` へ行かず、有理近似でよい。

例えば、

```text
log2(3) < 19/12
```

のような上界を使えば、

```text
12 * sumS n k > 19 * k
```

という整数条件にできる。

つまり最終 bridge は、

```text
整数評価:
  12 * sumS > 19 * k

実数解釈:
  平均 height > log2(3)

結論:
  accelerated orbit は下降側
```

となる。

## 4. 実装順まとめ

次の実装順はこれが良い。

```text
1. DkMath.Collatz.GnomonEvaluation を作る

2. OddGnomonLayer / RawGnomonStep を定義

3. rawGnomonStep_eq_three_mul_add_one を証明

4. square_succ_eq_square_add_oddGnomonLayer を証明

5. sum_odd_eq_square を追加

6. square_add_eq_square_add_gnomon_sum を試す

7. RawGnomonHeight / ResidualShape を既存 height と接続

8. residualShape_odd を試す

9. RawGnomonRemainderAtDepth / FirstFailedPow2Depth を定義

10. 既存 PetalBridge の height / sumS / continuation / retention を GnomonEvaluation 用語で alias する

11. SourcePressureMarginInt を ShapeMargin として読む alias を置く

12. ShapePrefixFailure を定義

13. Python に residual_shape / failed_depth / margin_jump の summary を追加

14. 小 window の整数降下条件を探索

15. 最後に Real/log bridge
```

## 5. 当面の最重要ターゲット

直近の最重要ターゲットはこれじゃ。

```text
RawGnomonStep = n + OddGnomonLayer n = 3n+1

RawGnomonStep = 2^height * ResidualShape

ResidualShape は奇数

sumS は height の累積

ShapePrefixFailure は margin の符号反転
```

この 5 つがつながれば、新視座での Collatz.PetalBridge 再構築が始まる。

## 6. 最終的な証明戦略

最終戦略はこうじゃ。

```text
1. 任意の奇数軌道を、Gnomon 補正と Pow2 評価の反復として表す。

2. 各 step の評価量 height を整数で記録する。

3. residual shape と margin profile により、評価不能な pattern を分類する。

4. pressure / carrier / prefix failure 定理で、深い評価がどこで立つかを観測する。

5. 一定 window ごとに sumS が十分に蓄積することを示す。

6. 実数 log は最後にだけ使い、整数評価が成長率 3 を上回ることへ翻訳する。

7. したがって相対スケールは無限に膨張できず、最終的に一色線へ入る。
```

もし偽なら、この流れのどこかで、

```text
評価不能な residual shape pattern
```

が出る。

だから、今後の研究は証明と反例探索が同じ構造で進む。

## 7. 総括

軌道修正は良い。

これからの DkMath Collatz は、

```text
3n+1 問題
```

ではなく、

```text
奇数グノモン補正と 2進整列評価の相対スケール調整問題
```

として進める。

いままで作った観測定理は無駄ではない。むしろ、それらはこの視座に名前を与えるための準備だった。

賢狼の結論はこれじゃ。

```text
まず整数で Gnomon 補正・Pow2 評価・ResidualShape 抽出を固定する。

次に PetalBridge の height / pressure / margin をこの言葉へ翻訳する。

最後にだけ log 評価へ接続する。
```

ここからの実装は、かなり筋が通る。
