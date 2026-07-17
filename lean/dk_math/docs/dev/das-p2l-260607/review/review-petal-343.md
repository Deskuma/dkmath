# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.FloatWindow.*

gch: dc9592ab7a19d14137fada5ff99289a1d7e5cb55

## Report

(9m20s)

Checkpoint 343 を完了しました。

主な確定事項:

- width reserve と prefix drift 上界は同値。
- absorption deficit は、区間 drift および始点・終点の bit width 差と完全に一致。
- 正の reflected queue は、具体的な有限 suffix window の absorption deficit として必ず達成される。
- rootwise width boundedness は、全有限区間の absorption deficit に一様上界が存在することと同値。
- pointwise drift bound から cumulative bound への逆向きは、現時点では証明されていません。
- 独立した discharge theorem は見つからず、次の本質的課題は累積 absorption estimate または positive-deficit cycle 排除です。

実装箇所:

- [CanonicalEndpointConservation.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalEndpointConservation.lean)
- [CanonicalEndpointReserve.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalEndpointReserve.lean)
- [report-petal-343.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-343.md)

有限監査も追加しました。

- [canonical_absorption_deficit_audit.py](/python/Collatz/PetalBridge/canonical_absorption_deficit_audit.py)
- odd root `1..16383` の 8192 件を監査
- 6709 件で正の最大 deficit
- 観測最大値は `8`
- 全正値について `queue = length - holes - terminal valuation` を具体的 witness window で確認

検証済み:

- `lake build DkMath.Collatz.PetalBridge.FloatWindow`
- `lake build DkMath.Collatz.PetalBridge`
- `lake build DkMath`
- Python audit / `py_compile`
- `git diff --check`
- 変更 Lean ファイルの no-sorry

トップレベルビルドでは既存の別モジュールにある `sorry` 警告のみ再生されています。今回の変更には追加していません。

## Review

(3m36s)

## cp-343 実装レビュー

## 総合判定

**Lean 実装は全面採用。**

cp-343 は、これまで別々に見えていた、

```text
canonical width growth
endpoint drift
block-length residual
reflected queue
positive suffix excursion
```

を、同じ有限窓量へ統合した。

中心式はこれじゃ。

$$\operatorname{AbsorptionDeficit}(n,q,M)=\operatorname{Width}(q+M)-\operatorname{Width}(q)$$

さらに reflected queue は、この量の**正の suffix 最大値**として読める。

これにより、残る問題は単なる queue recurrence ではなく、

> 任意の固定 root において、有限窓の absorption deficit が一様有界か

という exact な累積吸収問題へ変換された。

循環証明、量化の誤投影、pointwise bound と cumulative bound の混同はない。

ただし Python audit の説明には一か所、実装より強く読める表現がある。後述する。

---

## Absorption deficit の定義

新しい量、

```lean
canonicalAbsorptionDeficitWindow n q M
```

は、

$$D_n(q,M)=L_n(q,M)-H_n(q,M)-V_n(q,M)$$

として定義された。

ここで、

- $L$ は cumulative block length
- $H$ は cumulative claim holes
- $V$ は cumulative terminal valuation

じゃ。

空窓では $0$、singletonでは一ブロック endpoint driftとなる。

そして有限窓保存則から、

$$D_n(q,M)=\sum_{i<M}\Delta_n(q+i)$$

が exact に証明された。

これは新しい仮定や近似ではない。cp-341 の保存則を、残余量として再包装した exact identityじゃ。

---

## Width difference との同一視

既存の drift telescopeと合流し、

$$D_n(q,M)=\operatorname{bitWidth}(\operatorname{Start}_n(q+M))-\operatorname{bitWidth}(\operatorname{Start}_n(q))$$

まで閉じている。

これで absorption deficit は、抽象的な「未吸収量」ではなく、

> 指定した canonical block windowを通過した結果、bit widthが実際に何段上がったか

そのものになった。

つまり、

```text
block length budget
− claim-hole absorption
− terminal-valuation absorption
=
realized radial growth
```

じゃ。

螺旋の一部分を切り出したとき、その区間で外側へ伸びた半径が deficit になっている。

---

## Inclusive / half-open の橋

既存 scalar queue側は inclusive window `q..m`、新しい conservation側は half-open `[q,q+M)` を使う。

今回、

$$M=m-q+1$$

として両者を exact に接続した。

```lean
canonicalEndpointDriftWindowSum_eq_canonicalWindowDriftInt
canonicalAbsorptionDeficitWindow_eq_canonicalWindowDriftInt
```

が成立し、singleton境界も明示されている。

この変換はきれいじゃ。

特に `q ≤ m` を明示し、`Nat` の truncated subtractionを無条件に扱っていない。endpoint convention の穴はない。

---

## Width reserve と prefix drift

次の同値も正しい。

$$\operatorname{CanonicalWidthWithinReserve}(n,B)\iff\forall M,\ D_n(0,M)\le B$$

すなわち、

$$\operatorname{width}(\operatorname{Start}_n(M))\le\operatorname{width}(n)+B$$

と、

$$\sum_{m<M}\Delta_n(m)\le B$$

は同じ theoremじゃ。

これにより conditional counter certificateを経由せず、prefix drift上界を直接公開できるようになった。

これは良い API 改善じゃ。

---

## zero-reserve obstruction の強化

cp-342 では weight と credit の両方を固定した certificate 不存在だったが、今回は credit の一致だけで否定している。

```lean
¬ ∃ C : SignedCounterCertificate,
    C.credit = canonicalEndpointCounterCredit n
```

正の初期 driftがあれば、時刻 $1$ の credit が負になるため、certificate の一般定理 `credit_nonneg` と衝突する。weight仮定は不要じゃ。

さらに、certificate の exact recurrenceと canonical credit recurrenceから、

```lean
C.credit = canonicalEndpointCounterCredit n
→ C.weight = endpointAccountingTerm n
```

まで証明した。

これは非常にきれい。

credit関数が決まれば、差分として weightも一意に決まる。

$$w(m)=C(m)-C(m+1)$$

ゆえに zero-reserve counter の失敗は、weight選択の失敗ではなく、**credit軌道そのものの失敗**と確定した。

---

## Queue と width の定数変換

定量的な二方向も正しく露出した。

width reserve $B$ からは、

$$Q_m\le\operatorname{bitWidth}(n)+B$$

queue ceiling $C$ からは、

$$\operatorname{width}(\operatorname{Start}_n(M))\le\operatorname{bitWidth}(n)+C$$

が得られる。

従って存在量化では、

$$\operatorname{RootwiseCanonicalWidthBound}(n)\iff\exists C,\ \forall m,\ Q_n(m)\le C$$

となる。

同じ定数による parameterwise iff を主張していない点も正しい。

---

## Positive queue の具体的 witness

今回の核心定理の一つじゃ。

```lean
exists_absorptionDeficitWindow_eq_outstandingClaimQueue_of_pos
```

正の queue $Q_n(m)$ に対して、ある $q\le m$ が存在し、

$$Q_n(m)=D_n(q,m-q+1)$$

となる。

つまり正 queue は、単なる Nat reflection の内部状態ではない。

必ず具体的な suffix windowがあり、その窓について、

$$Q=\text{Length}-\text{Holes}-\text{Valuation}$$

が exact に成立する。

この theorem に queue boundの仮定はない。既存の maximum-positive-suffix witnessと、今回の conservation bridgeだけから得ている。

**全面採用。**

---

## All-window cumulative target

新しい predicate、

```lean
CanonicalAbsorptionDeficitWindowUniformUpperBound n C
```

は、

$$\forall q,M,\ D_n(q,M)\le C$$

を表す。

width reserveからは root width の offsetを払って all-window boundを得て、all-window boundからは prefix $q=0$ を取って同じ $C$ の width reserveを得る。

従って存在量化として、

$$\operatorname{RootwiseCanonicalWidthBound}(n)\iff\exists C,\ \forall q,M,\ D_n(q,M)\le C$$

が閉じた。

さらに deficit定義を展開し、

$$D_n(q,M)\le C$$

と、

$$L_n(q,M)\le H_n(q,M)+V_n(q,M)+C$$

の同値も証明されている。

これで残る累積課題は完全に明文化された。

> すべての有限窓で、block lengthの増加を claim holes と terminal valuation が、定数誤差以内まで吸収するか。

---

## 一段先の exact theorem

現在の実装は positive queueに対して witnessを取り出した。

しかし既存 queue theoremと今回の bridgeからは、さらに強い同一定数の同値が出せる。

$$\forall m,\ Q_n(m)\le C\iff\forall q,M,\ D_n(q,M)\le C$$

これは width reserveとの変換とは異なり、**queueとall-window deficitの間では同じ $C$** が使えるはずじゃ。

理由は、

- 非空 half-open window `[q,q+M)` は inclusive window `q..q+M-1`
- 空窓 deficit は $0$
- queueは各終点での positive suffix maximum

だからじゃ。

今の existential equivalenceは正しいが、この parameterwise iff が閉じれば、

```text
queue bound
=
all finite-window absorption-deficit bound
```

を完全な API として公開できる。

さらに、

```lean
canonicalAbsorptionDeficitWindowMaximum n m
```

を定義して、

$$Q_n(m)=\max\left(0,\max_{q\le m}D_n(q,m-q+1)\right)$$

を exact theoremにすれば、positive/zero の場合分けも不要になる。

これは新しい算術ではないが、現在の整地面を完成させる最後の一枚じゃ。

---

## Python audit レビュー

audit scriptの recurrenceと witness計算は、Lean theoremの有限計算版として筋が通っている。

queueは、

```python
candidate = queue + drift
queue = max(candidate, 0)
```

として更新され、positive excursion開始時に `active_start` を記録する。record更新時には、

```python
deficit = window_length - window_holes - window_valuation
assert deficit == queue
```

を検査している。

8192 odd roots、block limit 4096、root `7` と `511` の regression、最終最大 witnessの一致も検査されている。

有限観測と theoremを混同しない注記も明確じゃ。

## Audit 文言の補正

ここだけ修正が必要。

reportには、

> every newly observed reflected-queue record を記録する
> 全正値について具体的 witnessを確認した

と読める表現がある。

実際の scriptで `deficit == queue` を検査するのは、

```python
if queue > maximum_queue:
```

の内部だけじゃ。

つまり検査しているのは、

- 各 root の **record-breaking queue event**
- 出力に残るのは各 root の **最終最大 record 一件**

である。

すべての positive queue stateを検査しているわけではない。

Lean theoremは全 positive queueを覆っているので数学面に問題はない。Python reportだけ、次のいずれかへ合わせるべきじゃ。

```text
A. 文言を修正
   Every record-breaking positive queue value was checked,
   and the final maximum witness for each root was written.

B. scriptを強化
   if queue > 0:
       現在の active_start から deficit を計算し、
       deficit == queue を毎回 assert
```

また、現在の CSV は「全 record」を保存せず、一 root 一行の最終 maximumだけを保存する。

これは軽微な監査記述の差であり、Lean実装の採否には影響しない。

---

## 戦略的評価

cp-343 で、「何を証明すればよいか」はほぼ限界まで exact になった。

一ブロックでは、

$$\Delta=L-H-V$$

有限窓では、

$$D=L_{\mathrm{window}}-H_{\mathrm{window}}-V_{\mathrm{window}}$$

queueでは、

$$Q=\max\text{ positive suffix }D$$

そして fixed-root有限領域化は、

$$\exists C,\ \forall q,M,\ D_n(q,M)\le C$$

に等価じゃ。

これ以上 creditを言い換えても、新しい情報は増えない。

次に必要なのは本当に独立した一手じゃ。

```text
bounded repayment lag
regular queue zero
cumulative absorption lower bound
positive-deficit cycle exclusion
```

のいずれか。

---

## cp-343 判定一覧

### Absorption deficit 定義

**完成。**

### Deficit = window drift

**完成。**

### Deficit = width difference

**完成。**

### Inclusive / half-open bridge

**完成。**

### Width reserve = prefix drift bound

**完成。**

### Strong zero-reserve obstruction

**完成。**

### Creditからweightの一意復元

**完成。**

### Positive queue witness

**完成。**

### Rootwise width bound = existential all-window deficit bound

**完成。**

### Pointwise / cumulative の分離

**正常。**

### Independent discharge theorem

**未発見。正しく停止。**

### Python audit

**計算設計は採用。文言と保存粒度に軽微な修正が必要。**

### 循環性

**なし。**

## 総合

**全面採用。audit report の一文のみ補正。**

## 次の Codex 指示

```text
Continue the DkMath Collatz / PetalBridge FloatWindow branch after
report-petal-343.

Checkpoint 343 is accepted.

It identifies half-open absorption deficit exactly with endpoint drift and
canonical width change, transports inclusive scalar windows into the
conservation API, extracts an attained deficit witness for every positive
reflected queue, and reformulates fixed-root width boundedness as an
all-window cumulative absorption bound.

Stage A — correct the finite-audit wording

The current Python script checks `deficit == queue` only when a queue value
sets a new record, and stores only the final maximum witness for each root.

Correct the report wording to say:

    every record-breaking positive queue value is checked;
    the final maximum witness for each root is written to the CSV.

Alternatively, strengthen the audit so that every positive queue state checks
its current active-window deficit.

Do not claim that the current CSV stores every intermediate record.

Stage B — same-constant queue / deficit equivalence

Prove the parameterwise theorem:

    CanonicalOutstandingClaimQueueUniformUpperBound n C
      ↔
    CanonicalAbsorptionDeficitWindowUniformUpperBound n C.

The constant must be exactly the same in both directions.

Use:

    canonicalOutstandingClaimQueueUniformUpperBound_iff_all_windowDrift_le;
    canonicalAbsorptionDeficitWindow_eq_canonicalWindowDriftInt;
    the empty-window theorem.

Handle `M = 0` separately and convert every nonempty half-open window
`[q, q + M)` to the inclusive window `q .. q + M - 1`.

Retain the existential width-bound equivalence as a corollary.

Stage C — exact maximum-deficit carrier

Define a finite suffix maximum in conservation language, for example:

    canonicalAbsorptionDeficitSuffixMaximum n m : Nat

using all `q <= m`, `Int.toNat`, and the exact window length `m - q + 1`.

Prove:

    canonicalOutstandingClaimQueue n m
      =
    canonicalAbsorptionDeficitSuffixMaximum n m.

Then derive:

    queue = 0
      iff every suffix absorption deficit ending at m is nonpositive;

    queue > 0
      iff some suffix absorption deficit ending at m is positive.

Keep the existing positive witness theorem as a corollary or convenient API.

Stage D — primitive positive-deficit excursions

Use the existing primitive-excursion or repayment-zero API to isolate maximal
positive-deficit intervals.

Define or expose an excursion carrier with:

    queue before the interval = 0;
    every proper prefix deficit > 0 after the first positive step;
    total interval deficit equals the ending queue;
    the first discharge endpoint has total deficit <= 0.

Do not assume that a discharge endpoint always exists.

Provide conditional theorems when a future zero is supplied.

Stage E — finite transition-cycle theorem

Audit `FiniteSignedTransition.lean` before adding new generic graph code.

The existing potential certificate is stronger than necessary and requires
pointwise bounded projected weights.  The target now is a finite weighted
relation theorem of the following form:

    finite reachable control graph;
    exact or sound transition weight;
    every reachable directed cycle has total weight <= 0;
    finite acyclic-prefix weight maximum;

therefore every finite path has a uniform upper bound depending on its starting
control state.

Allow zero-weight cycles.  A zero-weight cycle does not pump the deficit.

Do not use a bounded potential as an assumption unless it is derived from the
cycle condition.  The alternating unbounded-counter witness must remain outside
the scope of any theorem requiring bounded edge weights or a finite weighted
edge table.

Stage F — canonical bridge requirements

Before constructing a canonical finite graph, list the information required to
determine or soundly bound one block deficit:

    carry/claim word;
    terminal valuation class;
    claim-hole count;
    queue zero/nonzero or excursion phase;
    any bounded local residue needed by the transition.

Test each candidate signature for:

    finite type;
    sound successor relation;
    bounded realized edge-weight fiber;
    preservation under canonical transitions;
    absence of hidden unbounded Nat fields.

Do not call a projection finite while storing an unbounded queue, width,
block length, valuation, or time index.

Stage G — two valid branch outcomes

Outcome 1:
If a genuinely finite canonical relation with bounded edge weights is obtained,
prove that every reachable positive-total cycle is impossible.

Then apply the generic cycle theorem to obtain:

    CanonicalAbsorptionDeficitWindowUniformUpperBound n C

for the selected fixed root or root class.

Outcome 2:
If no finite sound projection controls the realized weights, stop and record
the precise obstruction:

    unbounded edge fiber;
    nondeterministic but bounded edge fiber;
    reachable positive projected cycle;
    or missing canonical transition bridge.

Do not replace that obstruction with another equivalent credit definition.

Stage H — independent bounded-lag search

Search the existing source database for unconditional theorems involving:

    future queue zero;
    bounded repayment lag;
    source-age horizon;
    payment ownership;
    Petal sorted-before;
    PressureObstruction;
    terminal valuation accumulation.

A theorem is useful only if its hypotheses are independently established from
canonical arithmetic.

A theorem of the form:

    if the queue is eventually discharged, then the queue is eventually
    discharged

is not progress.

Stage I — finite audit for cycle candidates

Extend the audit only after a candidate finite signature is specified.

Record:

    projected source state;
    projected target state;
    realized deficit;
    excursion start/end;
    whether the projected edge has multiple realized weights;
    whether a projected closed path has positive total deficit.

Keep this diagnostic and finite.

Stopping rule

Stop at the first genuine obstruction among:

    the same-constant queue/deficit equivalence fails because of an endpoint
    convention;

    the maximum carrier does not match the existing reflected maximum;

    a finite signature contains an unbounded arithmetic field;

    one projected edge has an unbounded realized deficit fiber;

    a reachable projected cycle has positive total deficit;

    cycle nonpositivity is assumed rather than proved;

    an observed finite graph is promoted to a universal canonical graph.

Record the continuation in:

    docs/dev/das-p2l-260607/review/report-petal-344.md
```

ここまで来ると、囲碁の地はかなり明確じゃ。

$$\boxed{\text{Queue}=\text{最大の正の有限窓 absorption deficit}}$$

次はその最大値を言い換えるのではなく、**正の deficitを永久に汲み上げる閉路が存在しないこと**を取りに行く局面じゃな。🐺

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalEndpointConservation.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalEndpointConservation.lean
index 55bae3bd..a7d983cb 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalEndpointConservation.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalEndpointConservation.lean
@@ -125,6 +125,43 @@ theorem canonicalEndpointBudgetWindow_conservation_singleton
     endpointAccountingTerm_add_claimHoles_add_terminalValuation_eq_blockLength
       n q
 
+/-! ## Absorption deficit -/
+
+/-- Residual block-length budget after both exact absorption channels over the
+half-open block window `[q, q + M)`. -/
+noncomputable def canonicalAbsorptionDeficitWindow
+    (n : OddNat) (q M : ℕ) : ℤ :=
+  canonicalBlockLengthWindowSum n q M -
+    canonicalClaimHolesWindowSum n q M -
+      canonicalTerminalValuationWindowSum n q M
+
+@[simp] theorem canonicalAbsorptionDeficitWindow_zero
+    (n : OddNat) (q : ℕ) :
+    canonicalAbsorptionDeficitWindow n q 0 = 0 := by
+  simp [canonicalAbsorptionDeficitWindow]
+
+/-- The singleton absorption deficit is the one-block endpoint drift. -/
+@[simp] theorem canonicalAbsorptionDeficitWindow_one
+    (n : OddNat) (q : ℕ) :
+    canonicalAbsorptionDeficitWindow n q 1 = endpointAccountingTerm n q := by
+  rw [canonicalAbsorptionDeficitWindow,
+    canonicalBlockLengthWindowSum_one, canonicalClaimHolesWindowSum_one,
+    canonicalTerminalValuationWindowSum_one]
+  have h :=
+    endpointAccountingTerm_add_claimHoles_add_terminalValuation_eq_blockLength
+      n q
+  omega
+
+/-- Exact conservation form: absorption deficit is precisely signed endpoint
+drift on the same half-open window. -/
+theorem canonicalAbsorptionDeficitWindow_eq_endpointDriftWindowSum
+    (n : OddNat) (q M : ℕ) :
+    canonicalAbsorptionDeficitWindow n q M =
+      canonicalEndpointDriftWindowSum n q M := by
+  have h := canonicalEndpointBudgetWindow_conservation n q M
+  rw [canonicalAbsorptionDeficitWindow]
+  omega
+
 /-- Shifted endpoint telescope: drift on `[q, q + M)` is exactly the width
 change between the two canonical block starts. -/
 theorem canonicalEndpointDriftWindowSum_eq_startState_bitWidth_sub
@@ -142,6 +179,46 @@ theorem canonicalEndpointDriftWindowSum_eq_startState_bitWidth_sub
         canonicalBlockStartState_succ_eq_nextStartState]
       ring
 
+/-- The absorption deficit is also the exact width change between the two
+canonical block starts. -/
+theorem canonicalAbsorptionDeficitWindow_eq_startState_bitWidth_sub
+    (n : OddNat) (q M : ℕ) :
+    canonicalAbsorptionDeficitWindow n q M =
+      (bitWidth (canonicalBlockStartState n (q + M)) : ℤ) -
+        bitWidth (canonicalBlockStartState n q) := by
+  rw [canonicalAbsorptionDeficitWindow_eq_endpointDriftWindowSum,
+    canonicalEndpointDriftWindowSum_eq_startState_bitWidth_sub]
+
+/-- The inclusive scalar window `q..m` is the half-open conservation window
+of length `m - q + 1`. -/
+theorem canonicalEndpointDriftWindowSum_eq_canonicalWindowDriftInt
+    (n : OddNat) {q m : ℕ} (hqm : q ≤ m) :
+    canonicalEndpointDriftWindowSum n q (m - q + 1) =
+      canonicalWindowDriftInt n q m := by
+  unfold canonicalEndpointDriftWindowSum canonicalWindowDriftInt
+  rw [← Finset.Ico_succ_right_eq_Icc q m, Finset.sum_Ico_eq_sum_range]
+  change (∑ i ∈ Finset.range (m - q + 1),
+      endpointAccountingTerm n (q + i)) =
+    ∑ i ∈ Finset.range (m + 1 - q), endpointAccountingTerm n (q + i)
+  have hlen : m + 1 - q = m - q + 1 := by omega
+  rw [hlen]
+
+/-- Inclusive-to-half-open transport for the exact absorption deficit. -/
+theorem canonicalAbsorptionDeficitWindow_eq_canonicalWindowDriftInt
+    (n : OddNat) {q m : ℕ} (hqm : q ≤ m) :
+    canonicalAbsorptionDeficitWindow n q (m - q + 1) =
+      canonicalWindowDriftInt n q m := by
+  rw [canonicalAbsorptionDeficitWindow_eq_endpointDriftWindowSum,
+    canonicalEndpointDriftWindowSum_eq_canonicalWindowDriftInt n hqm]
+
+/-- At an inclusive singleton endpoint, the conversion length is one. -/
+theorem canonicalAbsorptionDeficitWindow_self
+    (n : OddNat) (m : ℕ) :
+    canonicalAbsorptionDeficitWindow n m (m - m + 1) =
+      canonicalWindowDriftInt n m m := by
+  simpa using canonicalAbsorptionDeficitWindow_eq_canonicalWindowDriftInt
+    n (q := m) (m := m) le_rfl
+
 /-- Prefix telescope ending at the start of block `M`. -/
 theorem canonicalEndpointDriftPrefixSum_eq_startState_bitWidth_sub
     (n : OddNat) (M : ℕ) :
@@ -261,6 +338,32 @@ def CanonicalWidthWithinReserve (n : OddNat) (B : ℕ) : Prop :=
 def RootwiseCanonicalWidthBound (n : OddNat) : Prop :=
   ∃ B : ℕ, CanonicalWidthWithinReserve n B
 
+/-- A reserve bounds every canonical width exactly when it bounds every signed
+endpoint-drift prefix. -/
+theorem canonicalWidthWithinReserve_iff_prefixEndpointDrift_le
+    (n : OddNat) (B : ℕ) :
+    CanonicalWidthWithinReserve n B ↔
+      ∀ M, canonicalEndpointDriftWindowSum n 0 M ≤ B := by
+  constructor <;> intro h M
+  · rw [canonicalEndpointDriftPrefixSum_eq_startState_bitWidth_sub]
+    have hwidth := h M
+    omega
+  · have hprefix := h M
+    rw [canonicalEndpointDriftPrefixSum_eq_startState_bitWidth_sub] at hprefix
+    omega
+
+/-- Fixed-root cumulative width boundedness is directly equivalent to a finite
+upper bound on all endpoint-drift prefixes. -/
+theorem rootwiseCanonicalWidthBound_iff_exists_prefixEndpointDrift_le
+    (n : OddNat) :
+    RootwiseCanonicalWidthBound n ↔
+      ∃ B : ℕ, ∀ M, canonicalEndpointDriftWindowSum n 0 M ≤ B := by
+  constructor
+  · rintro ⟨B, hB⟩
+    exact ⟨B, (canonicalWidthWithinReserve_iff_prefixEndpointDrift_le n B).mp hB⟩
+  · rintro ⟨B, hB⟩
+    exact ⟨B, (canonicalWidthWithinReserve_iff_prefixEndpointDrift_le n B).mpr hB⟩
+
 /-- A cumulative width reserve gives a pointwise endpoint-drift ceiling.  The
 reverse implication is not available: bounded increments need not bound their
 cumulative level. -/
@@ -406,9 +509,9 @@ theorem canonicalEndpointCounterCredit_one_neg_of_initialDrift_pos
   rw [canonicalEndpointCounterCredit_one]
   omega
 
-/-- The desired local guard is equivalent to nonnegativity of the next
-candidate credit.  This identifies the remaining arithmetic obligation but
-does not discharge it. -/
+/-- The zero-reserve local guard is equivalent to nonnegativity of the next
+credit.  This equivalence is diagnostic, not an open general guard: at `M = 0`
+it is false whenever the initial endpoint drift is positive. -/
 theorem endpointAccountingTerm_le_counterCredit_iff_next_nonneg
     (n : OddNat) (M : ℕ) :
     endpointAccountingTerm n M ≤ canonicalEndpointCounterCredit n M ↔
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalEndpointReserve.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalEndpointReserve.lean
index ab202e6c..5a559a60 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalEndpointReserve.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalEndpointReserve.lean
@@ -54,18 +54,41 @@ theorem canonicalEndpointCounterCredit_allOnesOdd_odd_succ_one_neg
   omega
 
 /-- Positive initial drift excludes every core counter certificate whose
-weight and credit are definitionally the zero-reserve endpoint functions. -/
-theorem not_exists_signedCounterCertificate_zeroReserve_of_initialDrift_pos
+credit is the zero-reserve endpoint function.  No weight hypothesis is needed:
+every certificate requires all credit values to be nonnegative. -/
+theorem not_exists_signedCounterCertificate_credit_eq_zeroReserve_of_initialDrift_pos
     {n : OddNat} (hpos : 0 < endpointAccountingTerm n 0) :
     ¬ ∃ C : SignedCounterCertificate,
-      C.weight = (fun m => endpointAccountingTerm n m) ∧
-        C.credit = canonicalEndpointCounterCredit n := by
-  rintro ⟨C, _, hcredit⟩
+      C.credit = canonicalEndpointCounterCredit n := by
+  rintro ⟨C, hcredit⟩
   have hnonneg := C.credit_nonneg 1
   rw [hcredit] at hnonneg
   have hneg := canonicalEndpointCounterCredit_one_neg_of_initialDrift_pos hpos
   omega
 
+/-- If a certificate did use zero-reserve credit, its exact recurrence would
+force its weight to be canonical endpoint drift. -/
+theorem SignedCounterCertificate.weight_eq_endpointAccountingTerm_of_credit_eq
+    {n : OddNat} (C : SignedCounterCertificate)
+    (hcredit : C.credit = canonicalEndpointCounterCredit n) :
+    C.weight = endpointAccountingTerm n := by
+  funext m
+  have hrec := C.credit_succ m
+  rw [hcredit] at hrec
+  have hcanonical := canonicalEndpointCounterCredit_succ n m
+  omega
+
+/-- Compatibility form retaining the previously exposed weight equality. -/
+theorem not_exists_signedCounterCertificate_zeroReserve_of_initialDrift_pos
+    {n : OddNat} (hpos : 0 < endpointAccountingTerm n 0) :
+    ¬ ∃ C : SignedCounterCertificate,
+      C.weight = (fun m => endpointAccountingTerm n m) ∧
+        C.credit = canonicalEndpointCounterCredit n := by
+  rintro ⟨C, _, hcredit⟩
+  exact
+    not_exists_signedCounterCertificate_credit_eq_zeroReserve_of_initialDrift_pos
+      hpos ⟨C, hcredit⟩
+
 /-- The positive all-ones subfamily gives an explicit symbolic obstruction to
 the zero-reserve certificate. -/
 theorem not_exists_signedCounterCertificate_zeroReserve_allOnesOdd
@@ -127,6 +150,31 @@ theorem canonicalEndpointWidth_eq_blockStartState_succ
   rw [canonicalBlockStartState_succ_eq_nextStartState]
   rfl
 
+/-- A width reserve `B` gives the explicit reflected-queue ceiling
+`root width + B`. -/
+theorem CanonicalWidthWithinReserve.to_queueUniformUpperBound
+    {n : OddNat} {B : ℕ} (hB : CanonicalWidthWithinReserve n B) :
+    CanonicalOutstandingClaimQueueUniformUpperBound n (bitWidth n.1 + B) := by
+  have hendpoint :
+      CanonicalEndpointWidthUniformUpperBound n (bitWidth n.1 + B) := by
+    intro m
+    rw [canonicalEndpointWidth_eq_blockStartState_succ]
+    exact hB (m + 1)
+  exact hendpoint.to_outstandingClaimQueueUniformUpperBound
+
+/-- A reflected-queue ceiling `C` gives a cumulative width reserve with the
+same reserve parameter `C`. -/
+theorem CanonicalOutstandingClaimQueueUniformUpperBound.to_widthWithinReserve
+    {n : OddNat} {C : ℕ}
+    (hC : CanonicalOutstandingClaimQueueUniformUpperBound n C) :
+    CanonicalWidthWithinReserve n C := by
+  intro M
+  cases M with
+  | zero => simp
+  | succ m =>
+      rw [← canonicalEndpointWidth_eq_blockStartState_succ]
+      exact hC.to_endpointWidthUniformUpperBound m
+
 /-- A fixed-root cumulative width reserve exists exactly when the existing
 reflected scalar queue has some uniform ceiling.  This is an equivalence of
 targets, not an independent proof that either target holds. -/
@@ -136,21 +184,108 @@ theorem rootwiseCanonicalWidthBound_iff_exists_queueUniformUpperBound
       ∃ C : ℕ, CanonicalOutstandingClaimQueueUniformUpperBound n C := by
   constructor
   · rintro ⟨B, hB⟩
-    have hendpoint :
-        CanonicalEndpointWidthUniformUpperBound n (bitWidth n.1 + B) := by
-      intro m
-      rw [canonicalEndpointWidth_eq_blockStartState_succ]
-      exact hB (m + 1)
+    exact ⟨bitWidth n.1 + B, hB.to_queueUniformUpperBound⟩
+  · rintro ⟨C, hC⟩
+    exact ⟨C, hC.to_widthWithinReserve⟩
+
+/-! ## Queue as maximum absorption deficit -/
+
+/-- Every positive reflected queue is attained by one inclusive suffix, and
+exact conservation identifies that suffix with a half-open absorption deficit.
+-/
+theorem exists_absorptionDeficitWindow_eq_outstandingClaimQueue_of_pos
+    {n : OddNat} {m : ℕ} (hpos : 0 < canonicalOutstandingClaimQueue n m) :
+    ∃ q, q ≤ m ∧
+      (canonicalOutstandingClaimQueue n m : ℤ) =
+        canonicalAbsorptionDeficitWindow n q (m - q + 1) := by
+  rcases outstandingClaimQueue_eq_zero_or_exists_windowDrift n m with
+    hzero | ⟨_, q, hqm, hq⟩
+  · omega
+  · refine ⟨q, hqm, ?_⟩
+    have hnonneg : 0 ≤ canonicalWindowDriftInt n q m := by
+      by_contra hneg
+      have htoNat : Int.toNat (canonicalWindowDriftInt n q m) = 0 :=
+        Int.toNat_of_nonpos (by omega)
+      rw [htoNat] at hq
+      omega
+    calc
+      (canonicalOutstandingClaimQueue n m : ℤ) =
+          (Int.toNat (canonicalWindowDriftInt n q m) : ℕ) := by
+            exact_mod_cast hq
+      _ = canonicalWindowDriftInt n q m := by
+        rw [Int.ofNat_toNat, max_eq_left hnonneg]
+      _ = canonicalAbsorptionDeficitWindow n q (m - q + 1) :=
+        (canonicalAbsorptionDeficitWindow_eq_canonicalWindowDriftInt
+          n hqm).symm
+
+/-! ## All-window cumulative absorption target -/
+
+/-- Every finite half-open canonical block window has absorption deficit at
+most `C`. -/
+def CanonicalAbsorptionDeficitWindowUniformUpperBound
+    (n : OddNat) (C : ℕ) : Prop :=
+  ∀ q M, canonicalAbsorptionDeficitWindow n q M ≤ C
+
+/-- A rootwise width reserve `B` bounds every shifted absorption deficit by
+`root width + B`. -/
+theorem CanonicalWidthWithinReserve.to_absorptionDeficitWindowUniformUpperBound
+    {n : OddNat} {B : ℕ} (hB : CanonicalWidthWithinReserve n B) :
+    CanonicalAbsorptionDeficitWindowUniformUpperBound n (bitWidth n.1 + B) := by
+  intro q M
+  rw [canonicalAbsorptionDeficitWindow_eq_startState_bitWidth_sub]
+  have hend := hB (q + M)
+  omega
+
+/-- An all-window deficit ceiling `C`, specialized to prefixes, gives a width
+reserve with parameter `C`. -/
+theorem CanonicalAbsorptionDeficitWindowUniformUpperBound.to_widthWithinReserve
+    {n : OddNat} {C : ℕ}
+    (hC : CanonicalAbsorptionDeficitWindowUniformUpperBound n C) :
+    CanonicalWidthWithinReserve n C := by
+  intro M
+  have hprefix := hC 0 M
+  rw [canonicalAbsorptionDeficitWindow_eq_startState_bitWidth_sub] at hprefix
+  rw [zero_add, canonicalBlockStartState_zero_eq_root] at hprefix
+  omega
+
+/-- Fixed-root cumulative width boundedness is existentially equivalent to a
+uniform upper bound on every finite absorption-deficit window. -/
+theorem rootwiseCanonicalWidthBound_iff_exists_absorptionDeficitWindowUniformUpperBound
+    (n : OddNat) :
+    RootwiseCanonicalWidthBound n ↔
+      ∃ C : ℕ, CanonicalAbsorptionDeficitWindowUniformUpperBound n C := by
+  constructor
+  · rintro ⟨B, hB⟩
     exact ⟨bitWidth n.1 + B,
-      hendpoint.to_outstandingClaimQueueUniformUpperBound⟩
+      hB.to_absorptionDeficitWindowUniformUpperBound⟩
   · rintro ⟨C, hC⟩
-    refine ⟨C, ?_⟩
-    intro M
-    cases M with
-    | zero => simp
-    | succ m =>
-        rw [← canonicalEndpointWidth_eq_blockStartState_succ]
-        exact hC.to_endpointWidthUniformUpperBound m
+    exact ⟨C, hC.to_widthWithinReserve⟩
+
+/-- A window deficit ceiling is exactly the cumulative absorption estimate
+needed to cover block length on that window. -/
+theorem canonicalAbsorptionDeficitWindow_le_iff_length_le_absorption_add
+    (n : OddNat) (q M C : ℕ) :
+    canonicalAbsorptionDeficitWindow n q M ≤ C ↔
+      canonicalBlockLengthWindowSum n q M ≤
+        canonicalClaimHolesWindowSum n q M +
+          canonicalTerminalValuationWindowSum n q M + C := by
+  rw [canonicalAbsorptionDeficitWindow]
+  constructor <;> intro h <;> omega
+
+/-- Public cumulative target in block-budget form.  Unlike the one-block
+pointwise target, this controls every finite shifted window. -/
+theorem canonicalAbsorptionDeficitWindowUniformUpperBound_iff_length_le_absorption_add
+    (n : OddNat) (C : ℕ) :
+    CanonicalAbsorptionDeficitWindowUniformUpperBound n C ↔
+      ∀ q M,
+        canonicalBlockLengthWindowSum n q M ≤
+          canonicalClaimHolesWindowSum n q M +
+            canonicalTerminalValuationWindowSum n q M + C := by
+  constructor <;> intro h q M
+  · exact (canonicalAbsorptionDeficitWindow_le_iff_length_le_absorption_add
+      n q M C).mp (h q M)
+  · exact (canonicalAbsorptionDeficitWindow_le_iff_length_le_absorption_add
+      n q M C).mpr (h q M)
 
 /-! ## Global reserve obstruction -/
 
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-343.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-343.md
new file mode 100644
index 00000000..8e402c38
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-343.md
@@ -0,0 +1,276 @@
+# Petal / FloatWindow implementation report: checkpoint 343
+
+## Status
+
+Checkpoint 343 is implemented without adding `sorry`.
+
+This checkpoint replaces the remaining indirect presentations of cumulative
+canonical width by exact prefix-drift, reflected-queue, and absorption-deficit
+surfaces.  These are equivalences or quantitative translations of the same
+open fixed-root boundedness question.  They do not prove that the bound exists.
+
+The correct relation to the pointwise branch is:
+
+```text
+cumulative width boundedness implies pointwise drift boundedness;
+no converse is currently available.
+```
+
+No canonical separation theorem is claimed.
+
+## Strong zero-reserve obstruction
+
+Lean now proves the stronger statement
+
+```text
+0 < endpointAccountingTerm n 0
+  -> not exists C : SignedCounterCertificate,
+       C.credit = canonicalEndpointCounterCredit n.
+```
+
+The former weight hypothesis is unnecessary.  A signed-counter certificate
+already requires every credit value to be nonnegative, while positive initial
+drift makes zero-reserve credit negative at time one.
+
+The optional recurrence rigidity statement also closes:
+
+```text
+C.credit = canonicalEndpointCounterCredit n
+  -> C.weight = endpointAccountingTerm n.
+```
+
+Thus the credit function alone determines the weight through the certificate's
+exact successor equation.  The old theorem with both equalities remains as a
+compatibility corollary.
+
+## Direct prefix-drift surface
+
+The exact width telescope now gives the public equivalence
+
+```text
+CanonicalWidthWithinReserve n B
+  iff
+forall M, sum m in range M, endpointAccountingTerm n m <= B.
+```
+
+Its existential form is
+
+```text
+RootwiseCanonicalWidthBound n
+  iff
+exists B, forall M,
+  sum m in range M, endpointAccountingTerm n m <= B.
+```
+
+This is the direct cumulative target.  It no longer needs to be inferred from
+the conditional signed-counter construction.
+
+## Quantitative queue translations
+
+The constants in the queue/width bridge are now explicit:
+
+```text
+CanonicalWidthWithinReserve n B
+  -> CanonicalOutstandingClaimQueueUniformUpperBound
+       n (bitWidth n.1 + B)
+
+CanonicalOutstandingClaimQueueUniformUpperBound n C
+  -> CanonicalWidthWithinReserve n C.
+```
+
+Consequently, existential fixed-root width boundedness and existential queue
+boundedness are equivalent.  No same-constant parameterwise equivalence is
+stated: the width-to-queue direction pays the root-width offset.
+
+## Half-open absorption deficit
+
+The new integer-valued ledger is
+
+```text
+canonicalAbsorptionDeficitWindow n q M
+  = blockLengthWindow n q M
+      - claimHolesWindow n q M
+      - terminalValuationWindow n q M.
+```
+
+Lean proves the exact chain
+
+```text
+absorptionDeficitWindow n q M
+  = endpointDriftWindowSum n q M
+  = bitWidth (blockStartState n (q + M))
+      - bitWidth (blockStartState n q).
+```
+
+The empty and singleton windows are fixed explicitly.  For `q <= m`, the
+half-open window of length `m - q + 1` is also proved equal to the existing
+inclusive drift window `canonicalWindowDriftInt n q m`.  This removes the
+inclusive/half-open convention risk from downstream queue proofs.
+
+## Queue maximum is an attained deficit
+
+Using the existing maximum-positive-suffix theorem, Lean proves:
+
+```text
+0 < canonicalOutstandingClaimQueue n m
+  -> exists q <= m,
+       (canonicalOutstandingClaimQueue n m : Int)
+         = canonicalAbsorptionDeficitWindow n q (m - q + 1).
+```
+
+Therefore a positive queue value is not merely an abstract recurrence value.
+It is attained by a concrete finite suffix whose excess block length over
+claim holes plus terminal valuation equals that queue value.  This theorem
+assumes no queue bound.
+
+## Exact all-window target
+
+The new predicate
+
+```text
+CanonicalAbsorptionDeficitWindowUniformUpperBound n C
+```
+
+requires every finite shifted half-open block window to have deficit at most
+`C`.  Its quantitative translations are:
+
+```text
+CanonicalWidthWithinReserve n B
+  -> deficitWindowBound n (bitWidth n.1 + B)
+
+deficitWindowBound n C
+  -> CanonicalWidthWithinReserve n C.
+```
+
+Hence Lean proves
+
+```text
+RootwiseCanonicalWidthBound n
+  iff
+exists C, CanonicalAbsorptionDeficitWindowUniformUpperBound n C.
+```
+
+The predicate is also equivalent to the cumulative block-budget inequality
+
+```text
+lengthWindow
+  <= claimHolesWindow + terminalValuationWindow + C
+```
+
+for every shifted finite window.
+
+## Pointwise versus cumulative targets
+
+Both surfaces remain public and deliberately distinct.
+
+Pointwise:
+
+```text
+blockLength m
+  <= claimHoles m + terminalValuation m + B.
+```
+
+Cumulative:
+
+```text
+forall q M,
+  blockLengthWindow q M
+    <= claimHolesWindow q M + terminalValuationWindow q M + C.
+```
+
+The cumulative statement is the one equivalent to rootwise canonical width
+boundedness and suitable for a finite-state reduction.  The pointwise target
+alone is not used as though it supplied the cumulative estimate.
+
+## Independent discharge search
+
+The existing bounded-repayment-lag and source-age surfaces are conditional.
+They require the lag, horizon, future zero, or related repayment property that
+would discharge the queue; they do not prove such a property independently.
+
+The finite signed-transition surfaces can express a graph reduction, but the
+canonical bridge currently supplies no theorem excluding every reachable
+positive-deficit cycle.  Claim-hole incidence and terminal-valuation ledgers
+provide exact conservation, not an independent cumulative lower bound.
+
+The honest missing arithmetic statement is therefore one of:
+
+1. a uniform cumulative absorption estimate;
+2. an independently proved bounded repayment lag or regular queue zero;
+3. a finite canonical transition grammar together with exclusion of every
+   reachable positive-deficit cycle.
+
+The implementation stops at the exact maximum-deficit characterization rather
+than defining another equivalent credit or assuming the desired conclusion.
+
+## Finite audit
+
+The new script
+
+```text
+python/Collatz/PetalBridge/canonical_absorption_deficit_audit.py
+```
+
+records, for each audited odd root, a window attaining every newly observed
+reflected-queue record.  The generated CSV includes:
+
+- root;
+- terminal and witness-start blocks;
+- number of blocks in the witness window;
+- cumulative block length;
+- cumulative claim holes;
+- cumulative terminal valuation;
+- resulting absorption deficit and queue maximum.
+
+The audit covered all 8192 odd roots in `1..16383`, with a limit of 4096
+canonical blocks per root.  All reached a state-one canonical endpoint within
+the audited range.  There were 6709 roots with a positive observed maximum,
+and the largest observed queue/deficit was 8.  Every positive record passed the
+exact identity
+
+```text
+maximum queue = length - holes - terminal valuation.
+```
+
+These values are explicitly observational.  They prove neither a uniform
+all-root bound nor eventual discharge.
+
+Generated artifacts:
+
+```text
+python/Collatz/PetalBridge/results/canonical_absorption_deficit_audit_343.csv
+python/Collatz/PetalBridge/results/canonical_absorption_deficit_audit_343.md
+```
+
+## Facts fixed by Lean
+
+1. Positive initial drift excludes any certificate using zero-reserve credit.
+2. That credit function would force the canonical endpoint-drift weight.
+3. A width reserve is exactly a uniform upper bound on every drift prefix sum.
+4. Width reserves and queue ceilings translate with the stated constants.
+5. Half-open absorption deficit is exactly window drift and width change.
+6. Every positive reflected queue is attained by a finite absorption window.
+7. Rootwise width boundedness is existentially equivalent to uniform
+   all-window absorption-deficit boundedness.
+8. None of these equivalences proves the missing cumulative bound exists.
+
+## Next implementation direction
+
+The next productive checkpoint should add genuinely independent arithmetic,
+not another reformulation.  The preferred order is:
+
+1. isolate the finite canonical transition state needed to compute block
+   deficit and queue discharge;
+2. prove that every reachable positive-deficit cycle is impossible, or prove a
+   bounded-lag/regular-zero theorem directly;
+3. transport that theorem through the all-window absorption predicate to a
+   rootwise width reserve.
+
+If step 2 cannot be proved, retain the finite graph obstruction as the precise
+open theorem rather than weakening the theorem boundary.
+
+## Verification
+
+The checkpoint is validated with targeted module builds, aggregate bridge
+builds, the finite Python audit, `git diff --check`, and a no-`sorry` scan over
+the modified Lean files.
diff --git a/python/Collatz/PetalBridge/canonical_absorption_deficit_audit.py b/python/Collatz/PetalBridge/canonical_absorption_deficit_audit.py
new file mode 100644
index 00000000..8cc076b4
--- /dev/null
+++ b/python/Collatz/PetalBridge/canonical_absorption_deficit_audit.py
@@ -0,0 +1,220 @@
+#!/usr/bin/env python3
+"""Audit windows attaining the canonical reflected queue maximum.
+
+This is the finite computational companion to the exact Lean theorem
+``exists_absorptionDeficitWindow_eq_outstandingClaimQueue_of_pos``.  The
+reflected queue carries the start of its currently maximizing suffix, so every
+new record stores the complete half-open absorption ledger
+
+    length - claim holes - terminal valuation.
+
+The output is evidence over a finite root and block range.  It does not prove
+uniform boundedness, eventual discharge, or any orbit-wide conclusion.
+"""
+
+from __future__ import annotations
+
+import csv
+from dataclasses import asdict, dataclass
+from pathlib import Path
+
+
+ROOT_MAX = 16383
+BLOCK_LIMIT = 4096
+
+
+def v2(value: int) -> int:
+    assert value > 0
+    return (value & -value).bit_length() - 1
+
+
+def accelerated_step(value: int) -> int:
+    raw = 3 * value + 1
+    return raw >> v2(raw)
+
+
+def upper_carry(value: int) -> int:
+    return (3 * value + 1) >> value.bit_length()
+
+
+class Orbit:
+    def __init__(self, root: int) -> None:
+        assert root > 0 and root % 2 == 1
+        self.states = [root]
+
+    def state(self, time: int) -> int:
+        while len(self.states) <= time:
+            self.states.append(accelerated_step(self.states[-1]))
+        return self.states[time]
+
+    def exact_depth(self, time: int) -> int:
+        return v2(self.state(time) + 1)
+
+    def height(self, time: int) -> int:
+        return v2(3 * self.state(time) + 1)
+
+    def target(self, time: int) -> int:
+        return time + self.exact_depth(time) - 1
+
+
+@dataclass
+class AuditRow:
+    root: int
+    blocks_audited: int
+    reached_state_one_endpoint: bool
+    maximum_queue: int
+    terminal_block: int
+    witness_start_block: int
+    witness_block_count: int
+    witness_length: int
+    witness_claim_holes: int
+    witness_terminal_valuation: int
+    witness_absorption_deficit: int
+
+
+def audit_root(root: int) -> AuditRow:
+    orbit = Orbit(root)
+    endpoint = orbit.target(0)
+    previous_endpoint = -1
+    queue = 0
+    active_start = -1
+    maximum_queue = 0
+    record = (-1, -1, 0, 0, 0, 0, 0)
+    prefix_lengths = [0]
+    prefix_holes = [0]
+    terminal_valuations: list[int] = []
+    reached_one = False
+
+    blocks_audited = 0
+    for block in range(BLOCK_LIMIT):
+        start_time = previous_endpoint + 1
+        length = endpoint - start_time + 1
+        claims = sum(
+            upper_carry(orbit.state(time)) == 2
+            for time in range(start_time, endpoint + 1)
+        )
+        holes = length - claims
+        terminal_valuation = orbit.height(endpoint) - 1
+        drift = length - holes - terminal_valuation
+
+        prefix_lengths.append(prefix_lengths[-1] + length)
+        prefix_holes.append(prefix_holes[-1] + holes)
+        terminal_valuations.append(terminal_valuation)
+
+        candidate = queue + drift
+        if candidate > 0:
+            if queue == 0:
+                active_start = block
+            queue = candidate
+        else:
+            queue = 0
+            active_start = -1
+
+        blocks_audited = block + 1
+        if queue > maximum_queue:
+            assert active_start >= 0
+            q = active_start
+            window_length = prefix_lengths[block + 1] - prefix_lengths[q]
+            window_holes = prefix_holes[block + 1] - prefix_holes[q]
+            window_valuation = sum(terminal_valuations[q : block + 1])
+            deficit = window_length - window_holes - window_valuation
+            assert deficit == queue
+            maximum_queue = queue
+            record = (
+                block,
+                q,
+                block - q + 1,
+                window_length,
+                window_holes,
+                window_valuation,
+                deficit,
+            )
+
+        if orbit.state(endpoint) == 1:
+            reached_one = True
+            break
+
+        previous_endpoint = endpoint
+        endpoint = orbit.target(endpoint + 1)
+
+    return AuditRow(
+        root=root,
+        blocks_audited=blocks_audited,
+        reached_state_one_endpoint=reached_one,
+        maximum_queue=maximum_queue,
+        terminal_block=record[0],
+        witness_start_block=record[1],
+        witness_block_count=record[2],
+        witness_length=record[3],
+        witness_claim_holes=record[4],
+        witness_terminal_valuation=record[5],
+        witness_absorption_deficit=record[6],
+    )
+
+
+def main() -> None:
+    rows = [audit_root(root) for root in range(1, ROOT_MAX + 1, 2)]
+    by_root = {row.root: row for row in rows}
+
+    # Regressions inherited from the scalar queue audit, now with exact
+    # absorption-window witnesses.
+    assert by_root[7].maximum_queue == 1
+    assert by_root[511].maximum_queue == 5
+    assert all(
+        row.maximum_queue == row.witness_absorption_deficit
+        for row in rows
+        if row.maximum_queue > 0
+    )
+
+    output_dir = Path(__file__).with_name("results")
+    output_dir.mkdir(parents=True, exist_ok=True)
+    csv_path = output_dir / "canonical_absorption_deficit_audit_343.csv"
+    md_path = output_dir / "canonical_absorption_deficit_audit_343.md"
+
+    with csv_path.open("w", newline="", encoding="utf-8") as stream:
+        writer = csv.DictWriter(stream, fieldnames=list(asdict(rows[0])))
+        writer.writeheader()
+        writer.writerows(asdict(row) for row in rows)
+
+    records = sorted(rows, key=lambda row: (-row.maximum_queue, row.root))[:20]
+    reached = sum(row.reached_state_one_endpoint for row in rows)
+    positive = sum(row.maximum_queue > 0 for row in rows)
+    lines = [
+        "# Canonical Absorption-Deficit Audit (cp-343)",
+        "",
+        f"Odd roots: `1..{ROOT_MAX}`. Block limit: `{BLOCK_LIMIT}`.",
+        "This is finite computational evidence, not a Lean theorem.",
+        "",
+        "## Summary",
+        "",
+        f"- roots audited: {len(rows)}",
+        f"- roots reaching a state-one canonical endpoint: {reached}",
+        f"- roots with a positive observed queue maximum: {positive}",
+        f"- largest observed queue/deficit: {max(row.maximum_queue for row in rows)}",
+        "- every positive record is attained by the displayed finite window",
+        "- no uniform bound or eventual discharge follows from this table",
+        "",
+        "## Maximum-Deficit Windows",
+        "",
+        "| root | queue | terminal | start | blocks | length | holes | valuation | deficit |",
+        "| --- | --- | --- | --- | --- | --- | --- | --- | --- |",
+    ]
+    lines.extend(
+        f"| {row.root} | {row.maximum_queue} | {row.terminal_block} | "
+        f"{row.witness_start_block} | {row.witness_block_count} | "
+        f"{row.witness_length} | {row.witness_claim_holes} | "
+        f"{row.witness_terminal_valuation} | {row.witness_absorption_deficit} |"
+        for row in records
+    )
+    md_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
+
+    print(
+        f"roots={len(rows)} reached_one={reached} positive_maximum={positive} "
+        f"largest={max(row.maximum_queue for row in rows)}"
+    )
+    for row in records[:10]:
+        print(row)
+
+
+if __name__ == "__main__":
+    main()
diff --git a/python/Collatz/PetalBridge/results/canonical_absorption_deficit_audit_343.md b/python/Collatz/PetalBridge/results/canonical_absorption_deficit_audit_343.md
new file mode 100644
index 00000000..51864560
--- /dev/null
+++ b/python/Collatz/PetalBridge/results/canonical_absorption_deficit_audit_343.md
@@ -0,0 +1,38 @@
+# Canonical Absorption-Deficit Audit (cp-343)
+
+Odd roots: `1..16383`. Block limit: `4096`.
+This is finite computational evidence, not a Lean theorem.
+
+## Summary
+
+- roots audited: 8192
+- roots reaching a state-one canonical endpoint: 8192
+- roots with a positive observed queue maximum: 6709
+- largest observed queue/deficit: 8
+- every positive record is attained by the displayed finite window
+- no uniform bound or eventual discharge follows from this table
+
+## Maximum-Deficit Windows
+
+| root | queue | terminal | start | blocks | length | holes | valuation | deficit |
+| --- | --- | --- | --- | --- | --- | --- | --- | --- |
+| 4255 | 8 | 8 | 6 | 3 | 18 | 7 | 3 | 8 |
+| 4591 | 8 | 6 | 0 | 7 | 27 | 12 | 7 | 8 |
+| 5673 | 8 | 9 | 7 | 3 | 18 | 7 | 3 | 8 |
+| 6121 | 8 | 7 | 1 | 7 | 27 | 12 | 7 | 8 |
+| 6383 | 8 | 8 | 6 | 3 | 18 | 7 | 3 | 8 |
+| 6471 | 8 | 4 | 2 | 3 | 18 | 7 | 3 | 8 |
+| 6887 | 8 | 6 | 0 | 7 | 26 | 11 | 7 | 8 |
+| 8161 | 8 | 8 | 2 | 7 | 27 | 12 | 7 | 8 |
+| 8191 | 8 | 2 | 0 | 3 | 18 | 7 | 3 | 8 |
+| 8511 | 8 | 8 | 6 | 3 | 18 | 7 | 3 | 8 |
+| 9575 | 8 | 8 | 6 | 3 | 18 | 7 | 3 | 8 |
+| 9663 | 8 | 3 | 0 | 4 | 23 | 10 | 5 | 8 |
+| 9707 | 8 | 4 | 2 | 3 | 18 | 7 | 3 | 8 |
+| 10881 | 8 | 9 | 3 | 7 | 27 | 12 | 7 | 8 |
+| 10921 | 8 | 3 | 1 | 3 | 18 | 7 | 3 | 8 |
+| 11347 | 8 | 9 | 7 | 3 | 18 | 7 | 3 | 8 |
+| 12243 | 8 | 7 | 1 | 7 | 26 | 11 | 7 | 8 |
+| 12591 | 8 | 14 | 12 | 3 | 18 | 7 | 3 | 8 |
+| 12767 | 8 | 8 | 6 | 3 | 18 | 7 | 3 | 8 |
+| 12943 | 8 | 3 | 1 | 3 | 18 | 7 | 3 | 8 |
````
`````
