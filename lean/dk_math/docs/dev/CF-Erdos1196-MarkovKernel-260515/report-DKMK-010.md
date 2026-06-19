# DKMK-010: report

DKMK-010 は、DKMK-009 で閉じた capacity-kernel-facing hitting route に、
tail / truncation / source estimate layer を接続する章である。

DKMK-009 の終点は次だった。

```text
PrimePowerWitnessProvider
  -> globalLogCapacityKernel
  -> CapacityKernel generic bridge
  -> primePowerQuotientPathFamily
  -> weightedHitMass bound
```

この route に残っていた外部入力は source mass estimate である。
DKMK-010 は、その入力を次の形で定式化した。

```text
finite/truncated envelope
  -> source mass contract
  -> DKMK-009 quotient-path route
  -> analytic placeholder
```

## 1. 主目的

DKMK-010 の主目的は、解析評価そのものを証明することではない。

目的は、将来の tail / truncation / Mertens 型評価が、既存の
finite kernel-hitting route へ流れ込むための theorem-facing interface を
作ることである。

そのため、DKMK-010 では `1 / (n * log n)` 型の無限 tail weight へ
直行せず、まず有限段 envelope を扱う。

## 2. 010A/B: scope と inventory

DKMK-010A では `roadmap-DKMK-010.md` を追加し、章の範囲を固定した。

DKMK-010B では既存 source mass theorem surface を inventory した。
既存 route は概ね次の形に整理できる。

```text
source mass model
  -> LogCapacitySourceMassBound M C
  -> DKMK-009 / DKMK-008 route theorem
  -> weightedHitMass <= C
```

ただし、quotient path family は divisor-descending family なので、
route 側では `DvdMonotoneMass M` も必要になる。

このため DKMK-010 では、source bound と divisibility monotonicity を
一緒に扱う方向へ進んだ。

## 3. 010C: TailWindowSourceMassBound

DKMK-010C では新規 module を追加した。

```text
DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation
```

中核 contract は次である。

```lean
structure TailWindowSourceMassBound (M : MassSpace ℕ) (C : ℝ) : Prop where
  nonneg_const : 0 ≤ C
  source_bound : LogCapacitySourceMassBound M C
  dvd_mono : DvdMonotoneMass M
```

これは DKMK-009 の quotient-path route に必要な三条件を束ねる
小さい theorem-facing contract である。

最初の concrete provider として次を追加した。

```lean
TailWindowSourceMassBound.finiteStepTail
```

これは既存の finite-step tail mass

```lean
finiteStepTailNatMassSpace steps threshold increment hinc
```

から、上界

```lean
((Finset.sum steps increment : ℚ) : ℝ)
```

を持つ `TailWindowSourceMassBound` を供給する。

## 4. 010D: finite-step route convenience

DKMK-010D では、finite-step tail envelope を DKMK-009 route へ
直接流す convenience theorem を追加した。

```lean
TailWindowSourceMassBound.finiteStepTail_weightedHitMass_le
```

到達形は次である。

```text
finiteStepTailNatMassSpace
  -> TailWindowSourceMassBound.finiteStepTail
  -> globalLogCapacityKernel
  -> primePowerQuotientPathFamily
  -> weightedHitMass <= sum increment
```

これは新しい proof route ではない。
DKMK-010C の contract theorem と DKMK-009 の quotient-path capacity route を
薄く合成したものである。

## 5. 010E: analytic placeholder

DKMK-010E では、将来の解析入力を受け取る placeholder contract を追加した。

```lean
structure FiniteStepTailAnalyticBound
    {ι : Type _} [DecidableEq ι]
    (steps : Finset ι) (increment : ι → ℚ) (error : ℝ) : Prop where
  total_le_one_add_error :
    ((Finset.sum steps increment : ℚ) : ℝ) ≤ 1 + error
```

この contract は analytic theorem ではない。
将来、解析側が次を供給するための受け口である。

```text
sum increment <= 1 + error
```

合成 theorem として次を追加した。

```lean
TailWindowSourceMassBound.finiteStepTail_weightedHitMass_le_one_add_error
```

これにより、

```text
weightedHitMass <= sum increment
sum increment <= 1 + error
```

から、

```text
weightedHitMass <= 1 + error
```

まで流せる。

## 6. route 図

DKMK-010 の到達 route は次である。

```text
finiteStepTailNatMassSpace
  ↓
TailWindowSourceMassBound
  ↓
finiteStepTail_weightedHitMass_le
  ↓
weightedHitMass <= sum increment
  ↓ FiniteStepTailAnalyticBound
weightedHitMass <= 1 + error
```

DKMK-009 と合わせると、全体は次のように読める。

```text
globalLogCapacityKernel
  + primePowerQuotientPathFamily
  + finite-step source envelope
  + analytic placeholder
  => weightedHitMass <= 1 + error
```

## 7. 到達点

DKMK-010 の中核は DKMK-010E で閉じた。

この章で固定したのは、有限/truncated envelope と解析評価の接合面である。
実解析の証明はまだ入れていない。

未解決として残る解析側の仕事は次である。

```text
具体的な tail / truncation / Mertens 型評価から
sum increment <= 1 + error
を供給する。
```

したがって DKMK-010 は、

```text
source mass estimate layer の interface を固定する章
```

として一区切りである。

## 8. 次の山

次の章では、今回 placeholder として置いた
`FiniteStepTailAnalyticBound` の中身をどのように供給するかを扱う。

自然な候補は次である。

```text
DKMK-011:
  finite-step envelope の具体設計
  truncation parameter と error term の関係
  sum increment <= 1 + error の解析契約の具体化
```

この段階で初めて、`1 + O(1 / log x)` 型の評価へ進む準備が整う。
