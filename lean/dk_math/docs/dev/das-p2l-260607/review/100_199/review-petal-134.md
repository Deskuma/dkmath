# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.*

gch: 959d4598013e9603c12b1844bb4c25599a125561

## Report

実装と実験を完了しました。

Lean 側は refactor 後の層に合わせて配置しました。`Profiles` には薄い profile predicate、`TailGrammar` には shifted label bridge、`PressureFrontier` には local island 左端の margin jump 補題を追加しています。

作成した report:
[report-petal-133.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-133.md)

Python 側は `pressure_sign_pattern_scan.py` に `--name-suffix` と threshold count 集計表を追加し、指定された 3 本の大きめ scan を実行しました。結果は `python/Collatz/PetalBridge/results/` に suffix 付きで出ています。

確認済み:

- `python3 -m py_compile python/Collatz/PetalBridge/pressure_sign_pattern_scan.py`
- `lake build DkMath.Collatz.PetalBridge.Profiles`
- `lake build DkMath.Collatz.PetalBridge.TailGrammar`
- `lake build DkMath.Collatz.PetalBridge.PressureFrontier`
- `lake build DkMath.Collatz.PetalBridge`
- 対象 3 Lean ファイルに新規 `sorry` なし
- `git diff --check` passed

観測としては、`max_n=8191` の 64/128 steps でほぼ同じ傾向、`max_n=16383` でも sign-change-up は全件 `retention_drop_dominant` でした。次は report に書いた通り、`PressureDecayProfile` へ進むのが一番筋が良さそうです。

## Review

## 状況分析

うむ。今回のレビュー対象は、ファイル名としては `review-petal-134.md` だが、中身としては **Checkpoint 133 の実装報告と、次の Checkpoint 134 候補**じゃな。

まず全体として、リファクタリング後の 14 分割構成にうまく乗れている。旧 `PetalBridge.lean` は約 7983 行・宣言 512 個前後まで肥大化していたため、`DkMath/Collatz/PetalBridge/` 以下へ 12〜14 ファイル程度で順序保存分割する方針だった。今回の変更はその分割後の層に合わせて、`Profiles`、`TailGrammar`、`PressureFrontier` へ自然に配置されている。

今回の実装は大きく三つ。

```text
Profiles:
  WindowHasResidualAllOnesDepthAtLeast
  WindowHasDeepResidualAllOnesExcursion
  その constructor / threshold lowering

TailGrammar:
  orbitWindowResidualAllOnesDepth_eq_nextLabel
  orbitWindowResidualAllOnesDepthSeq_get?_eq_some_nextLabel

PressureFrontier:
  sourcePressureMargin_lt_of_localIsland_left
```

そして Python 側では `pressure_sign_pattern_scan.py` に `--name-suffix` と threshold count 集計が入り、`8191/k64`, `8191/k128`, `16383/k64/d12` の 3 本の大きめ scan が実行された。Lean build も対象モジュールと親 `DkMath.Collatz.PetalBridge` まで通っており、対象 3 ファイルに新規 `sorry` なし、`git diff --check` も通過している。

## レビュー

## 良い点

第一に、**配置が良い**。

今回、`Profiles` に入ったものは time-profile 軸の薄い述語であり、pressure depth を触らない。

```lean
def WindowHasResidualAllOnesDepthAtLeast
def WindowHasDeepResidualAllOnesExcursion
```

これは正しい。
前回まで見えていた仮説は、

```text
positive block は window 内の deep all-ones excursion に反応する
```

であって、

```text
deep all-ones excursion があれば pressure block が必ず出る
```

ではない。

だから `Profiles` では「窓内に深い all-ones 残差が存在する」までに留め、pressure 側の主張を混ぜなかったのは、とても良い判断じゃ。

第二に、`TailGrammar` の placement が良い。

`orbitWindowResidualAllOnesDepth_eq_nextLabel` は、内容としては residual all-ones depth の読み替えだが、証明に `orbitWindowResidualShape_eq_oddOrbitLabel_succ` を使う。これは refactor 後の import order では `TailGrammar` 側にある。そのため `Profiles` に無理に置かず、`TailGrammar` に置いた判断は依存順を壊さない。

これは、分割後レビューとして重要じゃ。
今後も「意味的には Profiles っぽいが、bridge theorem は TailGrammar に置く」という判断が必要になる。

第三に、`sourcePressureMargin_lt_of_localIsland_left` が良い。

local island から左端の sign-change-up が出て、そこから strict margin jump が得られる。

```lean
theorem sourcePressureMargin_lt_of_localIsland_left
```

これはまだ retention / continuation drop の原因分解ではない。
だが、`PressureDecayProfile` へ進むための interface としてはちょうどよい。つまり、

```text
local island
  -> left-edge sign-change-up
  -> strict margin jump
  -> future decay decomposition
```

という橋ができた。

第四に、Python の robustness run が良い。

`max_n=8191` で `steps=64` と `steps=128` の結果がほぼ同じだったことは、64-step window で主要な deep all-ones excursion がすでに捕捉できている可能性を示している。また `max_n=16383`, `depth_len=12` でも sign-change-up が全件 `retention_drop_dominant` だったことは、local island の主因仮説をかなり強めている。

## 注意点

次に注意すべき点は、いよいよ **二つのルートが分岐し始めた**ことじゃ。

今回の report でも次候補として、

```text
Route A:
  count-level residual all-ones predicates

Route B:
  thin PressureDecayProfile layer
```

が提示されている。

ここで、賢狼としては **Route B を推す**。

理由は、Route A は安全だが、今回の Python scan ですでに threshold count の情報はある程度取れている。もちろん将来 `WindowHasAtLeastResidualAllOnesDepthCount` は欲しい。しかし、今回新しく強く見えたのは count ではなく、

```text
sign-change-up は安定して retention_drop_dominant
```

という PressureDecay 側の構造じゃ。

つまり、いま次に Lean 側へ置く価値が高いのは、

```text
deep all-ones excursion の数え上げ
```

よりも、

```text
margin jump を retention / continuation の減衰差として読むための薄い語彙
```

だと思う。

## 解説

ここまでの観測で、pressure sign profile は二層構造として見えてきた。

```text
ResidualAllOnesProfile:
  time axis 上の deep all-ones excursion

PressureDecayProfile:
  pressure depth axis 上の retention / continuation の減衰差
```

positive block は、おそらく前者が主因。

```text
window 内に deep all-ones residual が出る
  -> continuation support が深く残る
  -> positive depth が連続しやすい
```

一方、local island / sign-change-up は、後者が主因。

```text
retention が急に落ちる
continuation は相対的に残る
margin = 2 * continuation - retention が正へ跳ねる
```

今回の robustness scan では、sign-change-up がすべて `retention_drop_dominant` と分類されている。これはかなり強い観測じゃ。

したがって、次の一手は「all-ones count をさらに細かく数える」よりも、まず PressureDecay の最小語彙を Lean に置く方がよい。

ただし、ここでも重くしてはいけない。

まだやるべきではないもの：

```text
retention_drop_dominant -> local island
deep all-ones -> positive block
full ShapePressureGrid
global pressure theorem
```

今やるべきなのは、あくまで名前と薄い補題。

```text
retention drop
continuation drop
margin jump
sign-change-up as decay imbalance witness
```

## 次の指示

Checkpoint `134` は、**PressureDecayProfile の薄い開始**を推す。

追加先は、分割後の構造を考えると、新ファイルを切るよりまずは `PressureFrontier.lean` でよい。
ただし、定義が増え始めたら次 checkpoint で `PressureDecay.lean` または `PressureDecayProfile.lean` を新設するのがよい。

現段階では、

```text
PressureFrontier:
  frontier / island / sign-change-up / margin jump

Future PressureDecayProfile:
  retention-drop / continuation-drop / dominance
```

という境界じゃ。

## Checkpoint 134 推奨内容

## 1. margin drop / jump の薄い定義

まずは既存 `SourcePressureMarginInt` だけで進める。

```lean
def SourcePressureMarginJumpUp
    (n : OddNat) (k r j : ℕ) : Prop :=
  SourcePressureMarginInt n k (r + j) <
    SourcePressureMarginInt n k (r + j + 1)
```

既存の `sourcePressureMargin_lt_of_signChangeUp` と対応する alias / bridge を置く。

```lean
theorem sourcePressureMarginJumpUp_of_signChangeUp
    (n : OddNat) (k r j : ℕ)
    (h : SourcePressureSignChangeUp n k r j) :
    SourcePressureMarginJumpUp n k r j := by
  exact sourcePressureMargin_lt_of_signChangeUp n k r j h
```

これは非常に軽い。
そして今後の `PressureDecayProfile` で使う「margin が上へ跳ねた」という語彙になる。

## 2. local island left edge を jump predicate に接続

今回入った theorem は `<` を直接返している。
次は predicate 版も欲しい。

```lean
theorem sourcePressureMarginJumpUp_of_localIsland_left
    (n : OddNat) (k r j : ℕ)
    (hisland : SourcePressureLocalIsland n k r j) :
    SourcePressureMarginJumpUp n k r (j - 1) := by
  exact sourcePressureMarginJumpUp_of_signChangeUp n k r (j - 1)
    (sourcePressureSignChangeUp_of_localIsland n k r j hisland)
```

これで、

```text
local island
  -> left edge margin jump
```

が名前付きで扱える。

## 3. retention / continuation drop はまだ慎重に

もし既存 API に `SourceRetentionMass...` / `SourceContinuationMass...` が自然に使えるなら、次を定義してもよい。

ただし、Nat subtraction は危険なので、最初は **drop amount** ではなく **drop comparison Prop** がよい。

候補：

```lean
def SourceRetentionDropsAcross
    (n : OddNat) (k r j : ℕ) : Prop :=
  SourceRetentionMass n k (r + j + 1) <
    SourceRetentionMass n k (r + j)

def SourceContinuationWeaklyDropsAcross
    (n : OddNat) (k r j : ℕ) : Prop :=
  SourceContinuationMass n k (r + j + 1) ≤
    SourceContinuationMass n k (r + j)
```

ただし、実際の既存名が `sourceRetentionMass...` / `orbitWindowRetentionMass...` / `selected...` など分かれているはずなので、Codex には「既存名を検索して合わせよ」と明記した方がよい。

最初は source 側だけでよい。tail 側は後回し。

## 4. retention-drop-dominant predicate

Python の分類に対応する薄い Prop。

Nat subtraction を避けるなら、差分量ではなく不等式で書く。

もし mass が ℕ で、margin が

```text
margin = 2 * continuation - retention
```

なら、sign-change-up の原因を厳密に retention drop と言うには、本来は差分比較が必要になる。
だが最初は分類名だけでもよい。

```lean
def SourcePressureRetentionDropDominantAcross
    (n : OddNat) (k r j : ℕ) : Prop :=
  SourcePressureMarginJumpUp n k r j ∧
    SourceRetentionDropsAcross n k r j
```

これはまだ「dominant」と言うには弱いので、名前は慎重にするなら：

```lean
def SourcePressureJumpWithRetentionDrop
    (n : OddNat) (k r j : ℕ) : Prop :=
  SourcePressureMarginJumpUp n k r j ∧
    SourceRetentionDropsAcross n k r j
```

こちらの方が安全じゃ。

`dominant` は、もう少し定量化してから使うのがよい。

## 一歩先ゆく推論

賢狼の見立てでは、次の本命はこうじゃ。

```text
local island は、
continuation が増えた現象ではなく、
retention が急落したために
relative pressure が正に跳ねた現象である。
```

今回の scan はこれをかなり支持している。

したがって、次に欲しい数学的分解は、

```text
margin(j+1) - margin(j)
```

を retention / continuation の変化で書くことじゃ。

もし、

```text
margin(j) = 2 * continuation(j) - retention(j)
```

なら、

```text
margin(j+1) - margin(j)
  = 2 * (continuation(j+1) - continuation(j))
    - (retention(j+1) - retention(j))
```

となる。

つまり retention が大きく落ちると、右辺は正へ跳ねる。

この差分恒等式が Lean で出せれば、`PressureDecayProfile` はかなり本物になる。

ただし、ここは `ℤ` が絡む。
`SourcePressureMarginInt` がすでに `Int` なら、次の checkpoint 135 で狙う価値がある。

## さらなる次の一手

Checkpoint `134` で `MarginJumpUp` と retention-drop predicate を置いた後、Checkpoint `135` では次を狙う。

```lean
theorem sourcePressureMarginInt_step_diff_eq
    ...
```

内容は概念的にはこれ。

```text
margin(j+1) - margin(j)
  =
2 * (continuation(j+1) - continuation(j))
  - (retention(j+1) - retention(j))
```

ただし、Lean の既存定義に合わせて statement は調整する。
ここが通ると、Python の `retention_drop_dominant` が単なる観測ラベルから、Lean 上の algebraic decomposition へ近づく。

これが次の山じゃ。

## 賢狼が試して欲しい実験補題

## 実験 A: margin jump predicate

```lean
def SourcePressureMarginJumpUp
    (n : OddNat) (k r j : ℕ) : Prop :=
  SourcePressureMarginInt n k (r + j) <
    SourcePressureMarginInt n k (r + j + 1)
```

## 実験 B: sign-change-up gives margin jump

```lean
theorem sourcePressureMarginJumpUp_of_signChangeUp
    (n : OddNat) (k r j : ℕ)
    (h : SourcePressureSignChangeUp n k r j) :
    SourcePressureMarginJumpUp n k r j := by
  exact sourcePressureMargin_lt_of_signChangeUp n k r j h
```

## 実験 C: local island gives left-edge margin jump predicate

```lean
theorem sourcePressureMarginJumpUp_of_localIsland_left
    (n : OddNat) (k r j : ℕ)
    (hisland : SourcePressureLocalIsland n k r j) :
    SourcePressureMarginJumpUp n k r (j - 1) := by
  exact sourcePressureMarginJumpUp_of_signChangeUp n k r (j - 1)
    (sourcePressureSignChangeUp_of_localIsland n k r j hisland)
```

## 実験 D: weak retention drop predicate

既存 mass 名に合わせる必要あり。
以下は仮名。

```lean
def SourceRetentionDropsAcross
    (n : OddNat) (k r j : ℕ) : Prop :=
  SourceRetentionMass n k (r + j + 1) <
    SourceRetentionMass n k (r + j)
```

## 実験 E: weak continuation nonincrease predicate

```lean
def SourceContinuationWeaklyDropsAcross
    (n : OddNat) (k r j : ℕ) : Prop :=
  SourceContinuationMass n k (r + j + 1) ≤
    SourceContinuationMass n k (r + j)
```

## 実験 F: jump with retention drop

```lean
def SourcePressureJumpWithRetentionDrop
    (n : OddNat) (k r j : ℕ) : Prop :=
  SourcePressureMarginJumpUp n k r j ∧
    SourceRetentionDropsAcross n k r j
```

ただし、`dominant` という名前はまだ避ける。
定量的な drop 分解が入るまでは `JumpWithRetentionDrop` が安全じゃ。

## Python 側の次観測

Python 側は、次で `PressureDecayProfile` 用の表を明確化したい。

```text
sign_change_up rows:
  j
  margin_j
  margin_next
  margin_jump
  retention_j
  retention_next
  retention_drop
  continuation_j
  continuation_next
  continuation_drop
  cause_label
```

さらに、local island rows だけを抜き出す。

```text
local island rows:
  n
  island_depth
  left_edge_j
  margin_left
  margin_island
  margin_right
  retention_left
  retention_island
  retention_right
  continuation_left
  continuation_island
  continuation_right
```

この出力を次回 report にまとめるとよい。

## 総括

Checkpoint `133` は成功じゃ。

分割後の配置にきちんと従い、

```text
Profiles:
  residual all-ones excursion predicate

TailGrammar:
  next-label bridge

PressureFrontier:
  local island -> margin jump
```

と役割が綺麗に分かれている。

また Python robustness scan により、

```text
positive block:
  deep all-ones excursion と相関

sign-change-up / local island:
  retention_drop_dominant と安定
```

という二層構造がかなりはっきりしてきた。

次は `PressureDecayProfile` を薄く始めるのが正着じゃ。
ただし、まだ full grid ではない。
まずは margin jump と retention drop の語彙を置く。

## Codex instructions

```text
Checkpoint 134:
Start a thin PressureDecayProfile layer after the PetalBridge refactor.

Context:
  PetalBridge has been split into layered files under
  DkMath/Collatz/PetalBridge/.
  Do not add new material to the aggregate parent unless it is only an import.
  The previous checkpoint placed:
    - residual all-ones time-profile predicates in Profiles
    - shifted-label all-ones bridges in TailGrammar
    - local-island margin jump bridge in PressureFrontier

Primary goal:
  Add a minimal pressure-decay vocabulary around margin jumps.
  Keep it thin. Do not define a full ShapePressureGrid.

Preferred Lean location:
  Start in DkMath.Collatz.PetalBridge.PressureFrontier if the required names
  are already available there.
  If the definitions begin to grow, create a new file:
    DkMath.Collatz.PetalBridge.PressureDecay
  and import it after PressureFrontier in the parent aggregate.
  But prefer not to create a new file unless necessary.

Implement:
  1. Define a named margin-jump predicate:
     SourcePressureMarginJumpUp n k r j :=
       SourcePressureMarginInt n k (r + j)
         < SourcePressureMarginInt n k (r + j + 1)

  2. Prove:
     sourcePressureMarginJumpUp_of_signChangeUp

  3. Prove:
     sourcePressureMarginJumpUp_of_localIsland_left

  4. If existing retention / continuation mass names are readily available,
     add weak drop predicates, using existing API names exactly:
       SourceRetentionDropsAcross
       SourceContinuationWeaklyDropsAcross

     Avoid Nat subtraction if possible. Prefer comparison predicates:
       next < current
       next <= current

  5. Optionally define:
       SourcePressureJumpWithRetentionDrop
     as:
       SourcePressureMarginJumpUp n k r j
       ∧ SourceRetentionDropsAcross n k r j

Naming caution:
  Do not use "Dominant" in Lean names yet unless a quantitative dominance
  inequality is actually formalized. Prefer "JumpWithRetentionDrop".

Python:
  Extend the pressure scan summary with a PressureDecay section:
    sign_change_up rows:
      j
      margin_j
      margin_next
      margin_jump
      retention_j
      retention_next
      retention_drop
      continuation_j
      continuation_next
      continuation_drop
      cause_label

    local island rows:
      n
      island_depth
      left_edge_j
      margin_left
      margin_island
      margin_right
      retention_left
      retention_island
      retention_right
      continuation_left
      continuation_island
      continuation_right

Verification:
  Run:
    lake build DkMath.Collatz.PetalBridge.PressureFrontier
    lake build DkMath.Collatz.PetalBridge
    python3 -m py_compile python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
    git diff --check

Do not:
  introduce Real.log
  claim any pressure prefix theorem
  identify time index i with pressure depth j
  define full ShapePressureGrid
  prove deep all-ones excursion implies positive block
  overfit the retention_drop_dominant scan result into a theorem
```

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
index 4994e729..c56af501 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
@@ -591,6 +591,22 @@ theorem sourcePressureSignChangeUp_of_localIsland
     have hidx : r + (j - 1) + 1 = r + j := by omega
     simpa [hidx] using hpos

+/--
+A local pressure island gives a strict margin jump at its left edge.
+
+Checkpoint 133 reads local islands as pressure-depth decay imbalance witnesses.
+This theorem is still margin-only: it does not yet choose a retention or
+continuation drop decomposition, but it gives the exact interface that such a
+future `PressureDecayProfile` should refine.
+-/
+theorem sourcePressureMargin_lt_of_localIsland_left
+    (n : OddNat) (k r j : ℕ)
+    (hisland : SourcePressureLocalIsland n k r j) :
+    SourcePressureMarginInt n k (r + (j - 1)) <
+      SourcePressureMarginInt n k (r + (j - 1) + 1) :=
+  sourcePressureMargin_lt_of_signChangeUp n k r (j - 1)
+    (sourcePressureSignChangeUp_of_localIsland n k r j hisland)
+
 /-- The empty selected-pressure prefix is always available. -/
 theorem selectedPressurePrefix_zero
     (n : OddNat) (k r len : ℕ) :
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/Profiles.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/Profiles.lean
index 4b1455b1..30e0ce5e 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/Profiles.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/Profiles.lean
@@ -174,6 +174,73 @@ theorem orbitWindowResidualAllOnesDepthSeq_take_get?_eq_some
   exact orbitWindowResidualAllOnesDepthSeq_get?_eq_some n
     (Nat.lt_of_lt_of_le hi hr)

+/-
+Checkpoint 133 keeps the post-refactor source of truth in code comments.
+
+The experimental Python scan says that positive pressure blocks are better
+predicted by a deep all-ones excursion somewhere in the residual-shape window
+than by the first or modal residual.  The following names deliberately stay on
+the time-profile axis.  They do not mention pressure depth, do not assert a
+pressure prefix theorem, and do not introduce the future ShapePressureGrid.
+-/
+
+/--
+The finite window contains a residual all-ones excursion at threshold `d`.
+
+This is the thin profile-level predicate suggested by checkpoint 133.  It is
+existential on the time axis `i`; it does not claim that any pressure-depth
+block follows without additional retention/continuation hypotheses.
+-/
+def WindowHasResidualAllOnesDepthAtLeast
+    (n : OddNat) (k d : ℕ) : Prop :=
+  ∃ i, i < k ∧ d ≤ orbitWindowResidualAllOnesDepth n i
+
+/--
+Meaning-name alias for a deep residual all-ones excursion.
+
+The alias is intentionally separate from pressure vocabulary.  Future pressure
+bridges should consume this predicate together with a decay or retention
+condition, rather than smuggling in a pressure-prefix assumption.
+-/
+def WindowHasDeepResidualAllOnesExcursion
+    (n : OddNat) (k d : ℕ) : Prop :=
+  WindowHasResidualAllOnesDepthAtLeast n k d
+
+/-- Build a window all-ones-depth witness from an explicit in-window time. -/
+theorem windowHasResidualAllOnesDepthAtLeast_of_lt
+    (n : OddNat) (k d i : ℕ)
+    (hi : i < k)
+    (hdepth : d ≤ orbitWindowResidualAllOnesDepth n i) :
+    WindowHasResidualAllOnesDepthAtLeast n k d :=
+  ⟨i, hi, hdepth⟩
+
+/--
+Lower the all-ones-depth threshold of an existing window excursion.
+-/
+theorem windowHasResidualAllOnesDepthAtLeast_of_le
+    (n : OddNat) (k d e : ℕ)
+    (hde : d ≤ e)
+    (h : WindowHasResidualAllOnesDepthAtLeast n k e) :
+    WindowHasResidualAllOnesDepthAtLeast n k d := by
+  rcases h with ⟨i, hi, he⟩
+  exact ⟨i, hi, le_trans hde he⟩
+
+/-- Constructor spelling for the deep-excursion alias. -/
+theorem windowHasDeepResidualAllOnesExcursion_of_lt
+    (n : OddNat) (k d i : ℕ)
+    (hi : i < k)
+    (hdepth : d ≤ orbitWindowResidualAllOnesDepth n i) :
+    WindowHasDeepResidualAllOnesExcursion n k d :=
+  windowHasResidualAllOnesDepthAtLeast_of_lt n k d i hi hdepth
+
+/-- Lower the threshold of the deep-excursion alias. -/
+theorem windowHasDeepResidualAllOnesExcursion_of_le
+    (n : OddNat) (k d e : ℕ)
+    (hde : d ≤ e)
+    (h : WindowHasDeepResidualAllOnesExcursion n k e) :
+    WindowHasDeepResidualAllOnesExcursion n k d :=
+  windowHasResidualAllOnesDepthAtLeast_of_le n k d e hde h
+
 /--
 First-failed-depth profile over the first `k` observed odd labels.
 -/
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/TailGrammar.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/TailGrammar.lean
index 03f37330..7fe5d344 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/TailGrammar.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/TailGrammar.lean
@@ -87,6 +87,22 @@ theorem orbitWindowResidualShape_eq_oddOrbitLabel_succ
   rw [rawGnomonResidualShape_eq_T_val (iterateT i n)]
   rw [iterateT_succ_eq_T_iterateT]

+/--
+Residual all-ones depth is the all-ones depth of the next accelerated label.
+
+Checkpoint 133 treats `v2(residual + 1)` as a profile on the shifted odd-label
+orbit.  The theorem lives in `TailGrammar`, not `Profiles`, because the
+post-refactor import order places the residual-shape/next-label identity here.
+This keeps `Profiles` thin and lets downstream pressure modules consume the
+shifted-label reading without rebuilding the import graph.
+-/
+theorem orbitWindowResidualAllOnesDepth_eq_nextLabel
+    (n : OddNat) (i : ℕ) :
+    orbitWindowResidualAllOnesDepth n i =
+      ResidualAllOnesDepth (oddOrbitLabel n (i + 1)) := by
+  unfold orbitWindowResidualAllOnesDepth
+  rw [orbitWindowResidualShape_eq_oddOrbitLabel_succ]
+
 /--
 The residual-shape sequence is exactly the shifted odd-label sequence.

@@ -113,6 +129,21 @@ theorem orbitWindowResidualShapeSeq_get?_eq_some_shifted_label
   rw [orbitWindowResidualShapeSeq_eq_shifted_oddOrbitLabels]
   simp [hi]

+/--
+Reading the all-ones-depth residual profile can be stated directly in terms of
+the next accelerated label.
+
+This is the list-level companion to
+`orbitWindowResidualAllOnesDepth_eq_nextLabel`; it is the Lean-side handle for
+the Python scan columns based on residual all-ones depth.
+-/
+theorem orbitWindowResidualAllOnesDepthSeq_get?_eq_some_nextLabel
+    (n : OddNat) {i k : ℕ} (hi : i < k) :
+    (orbitWindowResidualAllOnesDepthSeq n k)[i]? =
+      some (ResidualAllOnesDepth (oddOrbitLabel n (i + 1))) := by
+  rw [orbitWindowResidualAllOnesDepthSeq_get?_eq_some n hi]
+  rw [orbitWindowResidualAllOnesDepth_eq_nextLabel]
+
 /--
 Window-level raw gnomon factorization.

diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-133.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-133.md
new file mode 100644
index 00000000..c51a48d2
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-133.md
@@ -0,0 +1,256 @@
+# Report Petal 133
+
+## Scope
+
+Checkpoint 133 was executed after the `DkMath.Collatz.PetalBridge`
+refactor.  The package is now split under
+`DkMath/Collatz/PetalBridge/*.lean`, so this checkpoint placed each new theorem
+at the layer where its imports are already available.
+
+Per the current source-of-truth rule, no package docs were synchronized in this
+checkpoint.  Explanatory synchronization was written into Lean docstrings and
+comments.  This report is the only new markdown artifact for the checkpoint.
+
+## Lean Changes
+
+### `DkMath.Collatz.PetalBridge.Profiles`
+
+Added the thin residual all-ones profile predicates:
+
+```lean
+def WindowHasResidualAllOnesDepthAtLeast
+def WindowHasDeepResidualAllOnesExcursion
+```
+
+and constructors / threshold-lowering helpers:
+
+```lean
+theorem windowHasResidualAllOnesDepthAtLeast_of_lt
+theorem windowHasResidualAllOnesDepthAtLeast_of_le
+theorem windowHasDeepResidualAllOnesExcursion_of_lt
+theorem windowHasDeepResidualAllOnesExcursion_of_le
+```
+
+These deliberately remain on the time-profile axis.  They do not mention
+pressure depth, do not assert a pressure-prefix theorem, and do not define a
+full `ShapePressureGrid`.
+
+### `DkMath.Collatz.PetalBridge.TailGrammar`
+
+Added the shifted-label bridge:
+
+```lean
+theorem orbitWindowResidualAllOnesDepth_eq_nextLabel
+theorem orbitWindowResidualAllOnesDepthSeq_get?_eq_some_nextLabel
+```
+
+These were not placed in `Profiles` because the refactored import order places
+`orbitWindowResidualShape_eq_oddOrbitLabel_succ` in `TailGrammar`.  The code
+comment records this explicitly, so future work does not try to rebuild the
+import graph just to read the residual all-ones depth as a shifted label.
+
+### `DkMath.Collatz.PetalBridge.PressureFrontier`
+
+Added the optional local-island margin bridge:
+
+```lean
+theorem sourcePressureMargin_lt_of_localIsland_left
+```
+
+This is a margin-only theorem.  It does not claim the cause decomposition by
+itself, but it gives a clean interface for a future `PressureDecayProfile`.
+
+## Python Experiment
+
+The scan script was extended with:
+
+```text
+--name-suffix
+```
+
+and additional aggregate tables:
+
+```text
+positive_block_length by count_all_ones_depth_ge_4
+positive_block_length by count_all_ones_depth_ge_5
+positive_block_length by count_all_ones_depth_ge_6
+frontier_depth by count_all_ones_depth_ge_4
+local_island_count by count_all_ones_depth_ge_4
+sign_change_up_count by count_all_ones_depth_ge_4
+```
+
+This lets the next reviewer decide whether the signal comes from a single deep
+excursion or from repeated medium-depth excursions.
+
+## Robustness Runs
+
+### `--max-n 8191 --steps 64 --r-start 2 --depth-len 10`
+
+Output:
+
+```text
+python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_8191_k64.csv
+python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_8191_k64.md
+```
+
+Summary:
+
+```text
+rows: 4096
+rows with positive pressure depths: 2170
+rows with local islands: 91
+rows with sign-change-up positions: 137
+max positive depth count: 10
+max local island count: 1
+max sign-change-up count: 1
+all-ones depth mode counts: 1:4096
+sign-change cause counts: retention_drop_dominant:137
+positive block length counts:
+  1:1521; 2:251; 3:114; 4:146; 5:76; 6:24;
+  7:11; 8:21; 9:1; 10:5
+all-ones depth max counts:
+  1:104; 2:453; 3:889; 4:455; 5:253; 6:1557;
+  7:205; 8:125; 9:21; 10:9; 11:20; 12:1; 13:4
+```
+
+### `--max-n 8191 --steps 128 --r-start 2 --depth-len 10`
+
+Output:
+
+```text
+python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_8191_k128.csv
+python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_8191_k128.md
+```
+
+Summary:
+
+```text
+rows: 4096
+rows with positive pressure depths: 2170
+rows with local islands: 93
+rows with sign-change-up positions: 137
+max positive depth count: 10
+max local island count: 1
+max sign-change-up count: 1
+all-ones depth mode counts: 1:4096
+sign-change cause counts: retention_drop_dominant:137
+positive block length counts:
+  1:1524; 2:249; 3:113; 4:146; 5:76; 6:24;
+  7:11; 8:21; 9:1; 10:5
+all-ones depth max counts:
+  1:104; 2:453; 3:889; 4:455; 5:252; 6:1558;
+  7:205; 8:125; 9:21; 10:9; 11:20; 12:1; 13:4
+```
+
+The 64-step and 128-step runs are almost identical at this range.  This
+suggests the decisive all-ones excursions are already captured by the 64-step
+window for odd `n <= 8191`.
+
+### `--max-n 16383 --steps 64 --r-start 2 --depth-len 12`
+
+Output:
+
+```text
+python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_16383_k64_d12.csv
+python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_16383_k64_d12.md
+```
+
+Summary:
+
+```text
+rows: 8192
+rows with positive pressure depths: 4421
+rows with local islands: 252
+rows with sign-change-up positions: 404
+max positive depth count: 11
+max local island count: 1
+max sign-change-up count: 1
+all-ones depth mode counts: 1:8192
+sign-change cause counts: retention_drop_dominant:404
+positive block length counts:
+  1:2966; 2:570; 3:262; 4:322; 5:143; 6:67;
+  7:26; 8:42; 9:3; 10:19; 11:1
+all-ones depth max counts:
+  1:147; 2:782; 3:1692; 4:1004; 5:580; 6:3099;
+  7:462; 8:275; 9:65; 10:25; 11:40; 12:2; 13:19
+top row:
+  n = 16383, positive block = 2-12, max block = 11,
+  all-ones max = 13
+```
+
+## Interpretation
+
+The checkpoint-132 hypothesis survived the larger scans:
+
+```text
+long positive pressure blocks track the maximum residual all-ones depth
+more strongly than the first residual or the mode residual.
+```
+
+The mode remains completely uninformative in these runs:
+
+```text
+all-ones depth mode = 1 for every scanned row.
+```
+
+The max signal remains strong, but it should still be treated as a profile
+witness, not as a direct pressure theorem.  A deep all-ones excursion supplies
+continuation support; retention mass can still obstruct or shorten the visible
+positive block.
+
+The sign-change-up rows are stable:
+
+```text
+8191, 64 steps:  retention_drop_dominant:137
+8191, 128 steps: retention_drop_dominant:137
+16383, 64 steps: retention_drop_dominant:404
+```
+
+Thus the local island phenomenon is better read as a pressure-depth decay
+imbalance than as a pure all-ones-carrier phenomenon.
+
+## Verification
+
+Commands run:
+
+```text
+python3 -m py_compile python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
+lake build DkMath.Collatz.PetalBridge.Profiles
+lake build DkMath.Collatz.PetalBridge.TailGrammar
+lake build DkMath.Collatz.PetalBridge.PressureFrontier
+lake build DkMath.Collatz.PetalBridge
+```
+
+No new `sorry` was found in:
+
+```text
+DkMath/Collatz/PetalBridge/Profiles.lean
+DkMath/Collatz/PetalBridge/TailGrammar.lean
+DkMath/Collatz/PetalBridge/PressureFrontier.lean
+```
+
+## Next Candidate
+
+Checkpoint 134 can now choose between two thin routes.
+
+Route A:
+
+```text
+Add count-level residual all-ones predicates.
+Example: WindowHasAtLeastResidualAllOnesDepthCount n k d c.
+```
+
+This would match the new Python threshold-count tables without touching
+pressure semantics.
+
+Route B:
+
+```text
+Start a thin PressureDecayProfile layer.
+First target: name retention-drop and continuation-drop comparison predicates,
+then connect sign-change-up/local-island observations to those predicates.
+```
+
+Route B is the better next step if the goal is to explain local islands.
+Route A is the safer next step if the goal is to continue validating the
+positive-block/all-ones-depth relation before introducing mass-drop vocabulary.
````
`````
