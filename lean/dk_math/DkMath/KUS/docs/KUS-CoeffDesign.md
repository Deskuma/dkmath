# KUS 係数型一般化 設計文書（phase-14）

## 背景と動機

現在の `KUS` は係数を `Nat` に固定している。

```lean
structure KUS (U : Type u) (Blueprint : BlueprintFamily U) where
  coeff    : Nat       -- 可視係数（Nat 固定）
  unit     : U
  blueprint : Blueprint unit
```

半環（Nat）のみでは：

- **減法が扱えない**（整数 Int が必要）
- **境界値 0.5, 1.5 などが表せない**（有理数 Rat が必要）
- **将来の連続係数**（Real, Complex）へ向かえない

ゆえに係数を型パラメータ `C` で一般化した **`GKUS C U Blueprint`** を導入する。

---

## 設計方針

### 1. 型構造

```
GKUS (C : Type*) (U : Type u) (Blueprint : BlueprintFamily U)
  ::= { coeff : C, unit : U, blueprint : Blueprint unit }
```

既存の `KUS` は `GKUS Nat` の型エイリアスとして維持し、後方互換を保つ。

```
KUS U Blueprint := GKUS Nat U Blueprint   -- 互換エイリアス（移行後）
```

### 2. 係数制約の段階

| 係数型  | 必要な代数制約    | 使える演算              |
|---------|-------------------|-------------------------|
| `Nat`   | `CommSemiring`    | 加算・乗算（零追跡）    |
| `Int`   | `CommRing`        | 加算・乗算・**減法**    |
| `Rat`   | `Field`           | 上記 + **除法・境界値** |
| `Real`  | `LinearOrderedField`| 連続係数                |

本 phase-14 では `CommSemiring` と `CommRing` を最小ターゲットとする。

### 3. 演算定義

加法（`gAdd`）と乗法（`gMul`）は `CommSemiring` 制約で定義する：

```lean
def gAdd [Add C] (x y : GKUS C U B) (h : SameSupport x y) : GKUS C U B :=
  ofWith (extract_g x) (x.coeff + y.coeff)

def gMul [Mul C] (x y : GKUS C U B) (h : SameSupport x y) : GKUS C U B :=
  ofWith (extract_g x) (x.coeff * y.coeff)
```

減法（`gSub`）は `Sub C` 制約（`Int` 以上）でのみ定義する：

```lean
def gSub [Sub C] (x y : GKUS C U B) (h : SameSupport x y) : GKUS C U B :=
  ofWith (extract_g x) (x.coeff - y.coeff)
```

### 4. 零追跡性の維持

`GKUS` でも `extract` が support を保持するという性質は不変。

演算結果の係数が **ゼロ元（`0 : C`）になっても** `extract` で `US` を回収できる。
これは係数型 `C` に依存せず、structural guarantee（定義由来）である。

### 5. `SameSupport` の再利用

`SameSupport` は `extract` の等値性で定義されており、
`GKUS` でも同じ形で定義できる（`C` に依存しない）。

```lean
def GSameSupport (x y : GKUS C U B) : Prop :=
  extract_g x = extract_g y
-- または SameSupport を GKUS 上で再利用
```

---

## 実装ロードマップ

### phase-14（当面）

- `DkMath/KUS/Coeff.lean`
  - `GKUS C U Blueprint` を定義する
  - `ofWith`, `toCoeff`, `extract_g` を導入する
  - `gAdd`, `gMul` を `CommSemiring` 制約で定義する
  - その零追跡性を固定する
  - `KUS` を `GKUS Nat` の abbrev として定義する（互換性確認）

### phase-15（次）

- `gSub` を `Int` 係数上で定義・検証する
- `DkMathTest` に `Int` 係数のテストを追加する

### phase-16（将来）

- `Rat` 係数で境界値（0.5, 1.5 など）を表現する
- `div` の最小設計に進む

---

## 非目標

- `KUS`（既存）の破壊的変更
- `Real` / `Complex` 係数の即時導入
- 位相・距離を伴う連続構造（別の設計段階）
