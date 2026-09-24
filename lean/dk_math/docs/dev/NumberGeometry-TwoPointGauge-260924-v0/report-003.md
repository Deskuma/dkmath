# NumberGeometry-TwoPointGauge NGEO-003 実装報告

## 1. 結果

Outcome A。二点 gauge geometry の affine similarity transport を実装し、translation、linear isometry、reflection を含む向きの変更、および real scaling に対する square-mass と shell の transport を Lean で検証した。

zero scale でも square-mass と denominator-free shell transport は成立する。一方、activity preservation と normalized-mass invariance は、指示どおり `c ≠ 0` を仮定している。

prime scale、radical landing、UnitCycle、logarithmic gauge、2p phase、FLT、level set、shared-point theory は実装していない。

## 2. 変更ファイル

- `DkMath/NumberGeometry/Transport.lean`
  - NGEO-003 の similarity map、gap/mass transport、kernel map、shell/quotient invariance を追加。
- `DkMath/NumberGeometry.lean`
  - `DkMath.NumberGeometry.Transport` を公開 facade から import。
- `DkMathTest/NumberGeometry/TransportAxiomAudit.lean`
  - 新規公開 API の `#check` と主要定理の `#print axioms` を追加。
- `docs/dev/NumberGeometry-TwoPointGauge-260924-v0/report-003.md`
  - 本報告。

`Basic.lean` と `Gauge.lean` は NGEO-003 のために変更していない。

## 3. Similarity representation

custom hierarchy は導入せず、次の薄い関数で affine similarity を表した。

```lean
def similarityMap
    (t : Point) (c : ℝ)
    (R : Point ≃ₗᵢ[ℝ] Point)
    (P : Point) : Point :=
  t + c • R P
```

`R` は Mathlib の `LinearIsometryEquiv` を直接利用している。

## 4. Gap と pair-mass transport

次の基礎定理を追加した。

- `pairVec_similarity`
- `pairMass_similarity`

```text
pairVec (T A) (T B) = c • R (pairVec A B)
pairMass (T A) (T B) = c^2 * pairMass A B
```

証明は座標展開を行わず、加法・線形写像の減法保存、`norm_smul`、`LinearIsometryEquiv.norm_map`、`sq_abs` を用いた。

## 5. Exposed corollaries

次の薄い corollary を公開した。

- `pairMass_translation`
- `pairMass_linearIsometry`
- `pairMass_scale`
- `dist_sq_similarity`

unsquared distance theorem は追加していない。必要な場合の正しい形は `dist (T A) (T B) = |c| * dist A B` であり、今回の square-distance theorem で十分なため deferred とした。

## 6. Kernel mapping

`TwoPointKernel.map` を追加した。

```lean
def TwoPointKernel.map
    (T : Point → Point) (K : TwoPointKernel) : TwoPointKernel
```

あわせて `map_source` と `map_target` の simp theorem を追加し、次の gauge transport を証明した。

- `massGauge_similarity`

## 7. Active preservation

`active_map_similarity_iff` を追加した。

```text
c ≠ 0 -> (K.map (similarityMap t c R)).Active ↔ K.Active
```

証明では `c^2 > 0` と `massGauge_pos_iff_active` を用いた。`c = 0` では全点が一点へ collapse するため、activity preservation は主張していない。

## 8. Shell と normalized mass invariance

`onNatShell_similarity` を追加した。

```text
OnNatShell K n P
  -> OnNatShell (K.map (similarityMap t c R)) n (similarityMap t c R P)
```

この定理は denominator-free なので `c = 0` でも成立する。

また、一般の pointwise equality として `normalizedMass_similarity` を追加した。

```text
K.Active -> c ≠ 0
-> normalizedMass (mapped K) (T P) = normalizedMass K P
```

pair-mass transport と mass-gauge transport を quotient に代入し、`c^2` と active gauge の非零性で cancellation した。shell point に限定した定理ではない。

## 9. 検証

以下はすべて成功した。

```text
lake build DkMath.NumberGeometry.Transport
Build completed successfully (2424 jobs)

lake build DkMath.NumberGeometry
Build completed successfully (2425 jobs)

lake build DkMathTest.NumberGeometry.TransportAxiomAudit
Build completed successfully (2426 jobs)

lake build DkMath
Build completed successfully (10276 jobs)
```

Transport の substantive theorem に対する `#print axioms` はすべて次の既存 logical infrastructure のみだった。

```text
[propext, Classical.choice, Quot.sound]
```

`sorry`、`admit`、`sorryAx`、`unsafe`、新規 `axiom` は使用していない。新規 production/test/report ファイルを含む空白検査も成功した。

## 10. NGEO-004 の提案スコープ

次 checkpoint では similarity API を利用して、square-mass level set と shared-point transport を導入する。

- `MassLevelSet A rho`
- level-set map under `similarityMap`
- `sharedPoint`
- `sharedPoint_transport`
- intersection naturality

既存の `SilverRatio.Circle.concyclic4` への接続は bridge として扱い、既存ファイルの theorem ownership は変更しない。NGEO-003 の transport module に level-set や shared-point の set theory を追加しない。

ここで NGEO-003 を終了する。
