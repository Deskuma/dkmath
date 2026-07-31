# FLT7 / Lean v4.29.0 → v4.32.2 Migration 修正資料

対象:

```text
DkMath.FLT.Seven.SevenBaseTerminalRamifiedDepth
DkMath.FLT.Seven.SevenBaseTerminalCellwiseFixedSystem
```

環境:

```text
Lean 4.32.2
mathlib v4.32.2
repository: Deskuma/dkmath
base branch: develop
```

## 1. 結論

今回の失敗は、数学証明の崩壊ではない。

二種類の API / elaboration migration が同時に露出している。

```text
A. padicValNat.pow の引数仕様変更
B. ZMod の法を依存 index とする構造間で、等式 transport が残留
```

最初の問題は 1 行修正で閉じる。

二番目は、`simp` の展開量を増やすのではなく、依存 index の正準形を一本に固定する必要がある。

---

## 2. `SevenBaseTerminalRamifiedDepth.lean`

### 2.1. 原因

v4.29.0 の `padicValNat.pow` は概ね次の形だった。

```lean
protected theorem padicValNat.pow
    (n : ℕ) (ha : a ≠ 0) :
    padicValNat p (a ^ n) = n * padicValNat p a
```

したがって旧コードは、

```lean
padicValNat.pow 7 p.gapRoot_pos.ne'
```

として、

```text
7                       = exponent
p.gapRoot_pos.ne'       = base nonzero proof
```

を渡していた。

v4.32.2 では次の形へ変更されている。

```lean
@[simp]
protected theorem padicValNat.pow
    (a n : ℕ) :
    padicValNat p (a ^ n) = n * padicValNat p a
```

非零証明は不要になり、明示引数は、

```text
base, exponent
```

の順になった。

そのため旧コードは v4.32.2 では、

```text
base := 7
exponent := p.gapRoot_pos.ne'
```

と解釈され、第二引数に `ℕ` ではなく命題証明を渡したため失敗している。

### 2.2. 最小修正

次を、

```lean
rw [padicValNat.self (by norm_num),
  padicValNat.prime_pow 6,
  padicValNat.pow 7 p.gapRoot_pos.ne'] at hval
```

次へ変更する。

```lean
rw [padicValNat.self (by norm_num),
  padicValNat.prime_pow 6,
  padicValNat.pow p.gapRoot 7] at hval
```

より API 変更へ強くするなら、power 部分だけ先に独立してもよい。

```lean
rw [padicValNat.pow p.gapRoot 7] at hval
rw [padicValNat.self (by norm_num),
  padicValNat.prime_pow 6] at hval
omega
```

### 2.3. 110 行目の未解決 goal について

表示されている、

```lean
⊢ padicValNat 7 p.root.snd.natAbs =
    5 + 7 * padicValNat 7 p.gapRoot
```

は独立した第二障害ではない。

`hval` の右辺に、

```lean
padicValNat 7 (p.gapRoot ^ 7)
```

が残ったままなので、`omega` が最終形へ正規化できていないだけである。

`padicValNat.pow p.gapRoot 7` が適用されれば、

```text
padicValNat 7 (p.gapRoot ^ 7)
  → 7 * padicValNat 7 p.gapRoot
```

となり、既存の `omega` で閉じる見込みが高い。

---

## 3. `SevenBaseTerminalCellwiseFixedSystem.lean`

### 3.1. エラー表示の意味

今回のエラーは、項の型と期待型が見た目には完全に同一である。

```text
term has type:
  @Eq (ZMod (...routingCell...)) (...) 0

expected:
  @Eq (ZMod (...routingCell...)) (...) 0
```

これは通常の代数式不一致ではない。

pretty printer が法の式を同じ形まで表示している一方で、内部には、

```text
Eq.rec
cast
cell.cellModulus_eq による transport
```

のいずれかが残っている。

`simp` 後の表示だけでは区別できない依存型不一致である。

### 3.2. 構造上の発生源

`AwaySevenBaseTerminalCellwiseCRTUniversalSolutionPacket` は、法を独立フィールドとして持つ。

```lean
cellModulus : ℕ
cellModulus_eq :
  cellModulus = awaySevenBaseTerminalRoutingCell packet coordinate

weighted : AwayRoutingCoordinates (ZMod cellModulus)
```

したがって、

```lean
cell.weighted.y
```

の型は、厳密には、

```lean
ZMod cell.cellModulus
```

である。

一方、構築しようとしている戻り値は、

```lean
AwayRoutingPrimePowerSolution
  (awaySevenBaseTerminalRoutingCell packet coordinate)
  ...
```

であり、フィールドの期待型は、

```lean
ZMod (awaySevenBaseTerminalRoutingCell packet coordinate)
```

である。

両者は `cell.cellModulus_eq` により等しいが、定義的に同一とは限らない。

v4.29.0 では elaborator / simplifier が偶然この transport を吸収できていた箇所が、v4.32.2 では露出したと読むのがよい。

### 3.3. 添付版で残っている罠

添付版では、

```lean
let M := awaySevenBaseTerminalRoutingCell packet coordinate
have hcell : cell.cellModulus = M := ...
```

としている。

これは数学的には正しい。

しかし、`cell.weighted` は依然として `ZMod cell.cellModulus` 上にあり、戻り値は `ZMod M` 上にある。

その後、

```lean
simpa [M, cell, hcell, ...]
```

で transport を各所から消そうとしているため、六つの同型エラーが同時に残っている。

ここで必要なのは simplifier の強化ではない。

```text
構築中の全項を、最初から一つの法で型付けする
```

ことである。

---

## 4. 推奨修正: `cell.cellModulus` を正準 index にする

### 4.1. 原則

内部構築中は、

```lean
M := cell.cellModulus
```

を唯一の法として使う。

最後にだけ、

```lean
hM : M = awaySevenBaseTerminalRoutingCell packet coordinate
```

で戻り値を transport する。

```text
悪い方向:
  routingCell を先に M とし、cell の全フィールドを何度も transport

良い方向:
  cell.cellModulus 上で全構造を完成し、最後に構造全体を一度だけ transport
```

### 4.2. 関数冒頭の置換

現在の概形、

```lean
let cell := candidate.cellwiseCRTUniversalSolution coordinate
let M := awaySevenBaseTerminalRoutingCell packet coordinate
have hcell : cell.cellModulus = M := by
  simpa [M] using cell.cellModulus_eq
have hendpoint :=
  packet.routingCell_dvd_originalEndpointFactor coordinate
have hroot := packet.routingCell_dvd_terminalRootFactor coordinate
have hweighted := cell.weighted_eq_original
have hfst := cell.weighted_fstEquation
refine { ... }
```

を、次の形へ変更する。

```lean
let cell := candidate.cellwiseCRTUniversalSolution coordinate
let M := cell.cellModulus

have hM :
    M = awaySevenBaseTerminalRoutingCell packet coordinate := by
  simpa [M] using cell.cellModulus_eq

have hendpoint :
    M ∣ endpointRoutingFactorNat y z
      (awaySevenBaseTerminalOriginalEndpointRow
        p.row coordinate.row) := by
  rw [hM]
  exact packet.routingCell_dvd_originalEndpointFactor coordinate

have hroot :
    M ∣
      match coordinate.column with
      | .vPart => r.cubic.rootTriple.vPart
      | .leftPart => r.cubic.rootTriple.leftPart
      | .rightPart => r.cubic.rootTriple.rightPart := by
  rw [hM]
  exact packet.routingCell_dvd_terminalRootFactor coordinate

have hweighted := cell.weighted_eq_original
have hfst := cell.weighted_fstEquation

have actual :
    AwayRoutingPrimePowerSolution
      M
      (awaySevenBaseTerminalOriginalEndpointRow
        p.row coordinate.row)
      (awaySevenBaseTerminalOriginalRootColumn coordinate.column) := by
  refine {
    u := cell.weighted.u
    v := cell.weighted.v
    y := cell.weighted.y
    z := cell.weighted.z
    endpoint_nondegenerate := ?_
    endpoint_equation := ?_
    root_nondegenerate := ?_
    root_equation := ?_
    first_coordinate_equation := ?_ }
  -- 既存の五つの証明をここへ移す。

exact hM ▸ actual
```

最終行の意味は、

```text
actual : solution at modulus M
hM     : M = routingCell
```

から、構造全体を一度だけ目的の法へ輸送することである。

### 4.3. `hcell` は削除する

この方式では、次は不要になる。

```lean
have hcell : cell.cellModulus = M := ...
```

また、各 `simpa` から次を削除する。

```lean
hcell
cell.cellModulus_eq
```

`M` は定義的に `cell.cellModulus` なので、内部の `ZMod M` と `ZMod cell.cellModulus` は同一になる。

### 4.4. endpoint equation の修正例

```lean
  · rw [hweighted]
    cases hrow :
        awaySevenBaseTerminalOriginalEndpointRow
          p.row coordinate.row
    · exact (ZMod.natCast_eq_zero_iff y M).2
        (by simpa [hrow, endpointRoutingFactorNat] using hendpoint)
    · exact (ZMod.natCast_eq_zero_iff z M).2
        (by simpa [hrow, endpointRoutingFactorNat] using hendpoint)
    · have hzero :=
        (ZMod.natCast_eq_zero_iff (y + z) M).2
          (by simpa [hrow, endpointRoutingFactorNat] using hendpoint)
      simpa [M, awaySevenBaseTerminalOriginalCoordinates,
        AwayEndpointPrimePowerEquation,
        AwayEndpointLocalEquation,
        Nat.cast_add] using hzero
```

重要なのは、`hzero` も goal も最初から `ZMod M` 上にいることである。

### 4.5. root equation の修正例

```lean
  · rw [hweighted]
    rcases coordinate with ⟨row, column⟩
    cases column
    · apply intCast_zero_of_dvd'
      apply intCast_dvd_of_dvd_natAbs
      simpa [← r.cubic.rootTriple.vPart_eq] using hroot
    · have hi : (M : ℤ) ∣ seventhPowerSndLeftCubic
          r.cubic.rootTriple.normal.root.fst
          r.cubic.rootTriple.normal.root.snd := by
        apply intCast_dvd_of_dvd_natAbs
        simpa [← r.cubic.rootTriple.leftPart_eq] using hroot
      simpa [M,
        awaySevenBaseTerminalOriginalRootColumn,
        awaySevenBaseTerminalOriginalCoordinates,
        AwayRootPrimePowerEquation,
        AwayRootLocalEquation,
        leftCubicZMod,
        seventhPowerSndLeftCubic] using
        intCast_zero_of_dvd' hi
    · have hi : (M : ℤ) ∣ seventhPowerSndRightCubic
          r.cubic.rootTriple.normal.root.fst
          r.cubic.rootTriple.normal.root.snd := by
        apply intCast_dvd_of_dvd_natAbs
        simpa [← r.cubic.rootTriple.rightPart_eq] using hroot
      simpa [M,
        awaySevenBaseTerminalOriginalRootColumn,
        awaySevenBaseTerminalOriginalCoordinates,
        AwayRootPrimePowerEquation,
        AwayRootLocalEquation,
        rightCubicZMod,
        seventhPowerSndRightCubic] using
        intCast_zero_of_dvd' hi
```

`first_coordinate_equation` 内の endpoint / root 証明にも同じ変更を適用する。

---

## 5. `hM ▸ actual` が elaboration で止まる場合

第一候補:

```lean
exact hM ▸ actual
```

第二候補:

```lean
cases hM
exact actual
```

第三候補として明示的な `Eq.ndrec` を使えるが、通常は不要である。

```lean
exact Eq.ndrec actual hM
```

ここで `simpa [hM] using actual` へ戻るのは避ける。

今回の障害そのものが simplifier 内部の dependent transport だからである。

---

## 6. さらに小さい修正候補

次の一行を `refine` より前に試す方法もある。

```lean
rw [← cell.cellModulus_eq]
```

これにより goal 全体の法を `cell.cellModulus` へ変える。

ただし、既存の `hendpoint` / `hroot` は `routingCell` を法として記述されているため、それらの変換が別途必要になる。

保守性と読みやすさでは、

```text
actual を cell.cellModulus 上で構築
→ 最後に hM ▸ actual
```

の二段構成を推奨する。

---

## 7. Codex 向け作業指示

```text
Goal:
Repair the Lean 4.29.0 -> 4.32.2 migration failures in exactly two FLT7 modules without changing any mathematical theorem statement.

Target files:
1. DkMath/FLT/Seven/SevenBaseTerminalRamifiedDepth.lean
2. DkMath/FLT/Seven/SevenBaseTerminalCellwiseFixedSystem.lean

Task A — padicValNat.pow API migration:
- Inspect the v4.32.2 signature.
- Replace the obsolete call
    padicValNat.pow 7 p.gapRoot_pos.ne'
  with the new base/exponent call
    padicValNat.pow p.gapRoot 7
- Keep the final omega proof unless a genuinely necessary normalization edit is required.
- Build only SevenBaseTerminalRamifiedDepth first.

Task B — eliminate dependent ZMod modulus transports:
- Do not continue adding hcell/cell.cellModulus_eq to simp sets.
- In cellwiseOriginalActualSolution, use
    M := cell.cellModulus
  as the canonical modulus for the entire internal construction.
- Convert hendpoint and hroot from routingCell to M once at the beginning using hM.
- Construct an intermediate
    actual : AwayRoutingPrimePowerSolution M ...
- Transport the completed structure exactly once at the end with
    exact hM ▸ actual
  or, if needed,
    cases hM
    exact actual
- Remove the old hcell-based repeated transports.
- Apply the same canonical-modulus pattern to both the direct endpoint/root equation fields and the two nested proofs supplied to AwayFirstCoordinatePrimePowerEquation.of_universal.

Validation order:
1. lake build DkMath.FLT.Seven.SevenBaseTerminalRamifiedDepth
2. lake build DkMath.FLT.Seven.SevenBaseTerminalCellwiseFixedSystem
3. lake build DkMath

Constraints:
- Do not alter theorem statements.
- Do not add axioms or sorry.
- Do not refactor unrelated FLT7 modules.
- Treat the identical-looking ZMod type mismatch as a hidden dependent transport problem, not as an algebraic normalization problem.
```

---

## 8. 期待される結果

### `SevenBaseTerminalRamifiedDepth`

一つの API 呼び出し修正により、

```text
Application type mismatch
```

と後続の `omega` 未解決 goal が同時に消える。

### `SevenBaseTerminalCellwiseFixedSystem`

次の六件は同一原因なので、個別に追わない。

```text
240
269
280
297
314
325
```

依存 index を `cell.cellModulus` へ統一すれば、endpoint 2 件、left/right root 4 件がまとめて解消する見込みが高い。

---

## 9. 長期的な設計改善案

今回の migration を越えた後、構造を変更できる checkpoint では、

```lean
cellModulus : ℕ
cellModulus_eq : cellModulus = routingCell
model : AwayRoutingCoordinates (ZMod cellModulus)
```

という sigma 的設計を、直接、

```lean
model :
  AwayRoutingCoordinates
    (ZMod (awaySevenBaseTerminalRoutingCell packet coordinate))
```

へ縮約する余地がある。

この変更を行えば `cellModulus_eq` 自体が不要になり、同種の transport 障害は構造上発生しなくなる。

ただし依存先が広い可能性があるため、今回の migration 修正では実施しない。
