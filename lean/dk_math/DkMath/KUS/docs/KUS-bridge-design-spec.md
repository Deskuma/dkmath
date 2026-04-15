# KUS Bridge design spec（phase-25 初稿）

## 1. 目的

本仕様は、`DHNT`（連続スケール）と `KUS`（依存型 support）を接続するための
**bridge 層**「`DkMath.KUS.Bridge`」を設計する。

接続の核心は次の図式にある。

```
DHNT.Qty (ℝ, Unit)          連続数量の世界
     |
     | phi : Unit → ℕ        離散化写像（単位の「整数化」）
     ↓
KUS.US (ℕ, ToyBlueprint)    依存型 support の世界
     |
     | GKUS 構造              係数 · support の分離表現
     ↓
HarmonizeSpec               異 support 演算（Transport 層）
```

---

## 2. 背景

### 2.1 DHNT 層の型

| 型 | 意味 |
|---|---|
| `DHNT.Unit` | 正実数（`ℝ>0`）の単位 |
| `DHNT.Qty`  | `(u : Unit, x : ℝ)` — 値 `x`, 単位 `u` の数量 |
| `Qty.convert q w` | 共通単位 `w` への換算 |
| `Qty.addVia w a b` | 係数 `a`, `b` を `w` へ揃えて加算 |

### 2.2 KUS 層の型

| 型 | 意味 |
|---|---|
| `BlueprintFamily U` | 各 unit `u : U` に対する blueprint 型族 |
| `US U B` | `(unit : U, blueprint : B unit)` — support のペア |
| `GKUS C U B` | `(coeff : C, unit : U, blueprint : B unit)` — 汎用 KUS 点 |
| `HarmonizeSpec` | 異系 encode-confluence-decode 仕様 |

---

## 3. 設計方針

### 3.1 接続の方向

接続は **DHNT → KUS** の一方向。DHNT 量を KUS へ埋め込む方向のみを
まず形式化し、逆方向（KUS → DHNT の連続的持ち上げ）は phase 以降の課題とする。

### 3.2 離散化写像 `phi`

`phi : DHNT.Unit → ℕ` の役割は「連続単位の整数化」。

具体的には：

- `phi u := ⌊u.val⌋₊` （自然数床）
- もしくは `phi u := ⌊u.val * scale⌋₊` （fixed-point スケール付き）

`phi` は `0 < phi u` が **保証されない** ため、KUS 側では
`phi u = 0` を「未定義 support」として扱う安全ガードが必要。

### 3.3 BlueprintFamily の選択

DHNT 接続専用の blueprint 族として

```lean
-- DHNT 由来の unit は「自然数」に落とし、blueprint は単に Fin 1 (trivial)
abbrev DHNTBlueprint : BlueprintFamily ℕ := fun _ => Fin 1
```

を採用する。これにより `HarmonizeSpec` の `sameSupport` 証明が
`simp` で閉じる。

### 3.4 encode 仕様（`ScaleSpec`）

`Qty.addVia w` の「共通単位 `w` への換算」に対応する encode は：

```lean
def dhntEncodeLeft (phi : DHNT.Unit → ℕ) (w : DHNT.Unit)
    (q : GKUS ℝ ℕ DHNTBlueprint) : GKUS ℝ ℕ DHNTBlueprint
```

ただし KUS の `ScaleSpec` は `mapUnit : U → V` だけを要求するため、
`phi w` を定数 target として `mkHarmonizeFixed` で構成できる。

---

## 4. Lean シグネチャ案（擬似コード）

```lean
-- DkMath/KUS/Bridge.lean
namespace DkMath.KUS.Bridge

/-- DHNT 接続用 trivial blueprint。 -/
abbrev DHNTBlueprint : BlueprintFamily ℕ := fun _ => Fin 1

/-- DHNT.Unit を ℕ へ離散化する。
    `phi u = ⌊u.val⌋₊` を採用。0 になる場合は呼び出し側で guard する。 -/
noncomputable def phiUnit (u : DHNT.Unit) : ℕ :=
  ⌊u.val⌋₊

/-- Qty を GKUS (ℝ, ℕ, DHNTBlueprint) へ埋め込む。 -/
noncomputable def embedQty (q : DHNT.Qty) : GKUS ℝ ℕ DHNTBlueprint :=
  mkGWith q.x ⟨phiUnit q.u, Fin.ofNat' 0 (by omega)⟩  -- ← blueprint = 0 (trivial)

/-- addVia に対応する HarmonizeSpec を builder で生成。 -/
noncomputable def addViaSpec (w : DHNT.Unit) :
    HarmonizeSpec ℝ ℕ DHNTBlueprint ℕ DHNTBlueprint ℕ DHNTBlueprint :=
  mkHarmonizeFixed
    (encConst (phiUnit w))   -- encLeft : mapUnit _ := phiUnit w
    (encConst (phiUnit w))   -- encRight: 同じ定数
    (commonSupport (phiUnit w))
    (fun _ => by simp [ScaleSpec.scaleUS, encConst])
    (fun _ => by simp [ScaleSpec.scaleUS, encConst])
```

`encConst` は「mapUnit を定数 `n` にする `ScaleSpec`」。
`mkHarmonizeFixed` は phase-24 で実装済み。

---

## 5. 整合性補題の目標

| 補題 | 内容 |
|---|---|
| `embedQty_toCoeff` | `toCoeff (embedQty q) = q.x` |
| `addVia_toCoeff` | `toCoeff (harmonizeAdd (addViaSpec w) (embedQty a) (embedQty b)) = a.x + b.x` |
| `addVia_commutes_convert` | `convert` の自然性と `harmonizeAddTo_decode_comp` の対応 |

---

## 6. 実装ロードマップ

| phase | 内容 |
|---|---|
| phase-25 | `Bridge.lean` 新設。`phiUnit` / `DHNTBlueprint` / `embedQty` / `addViaSpec` を実装 |
| phase-26 | `embedQty_toCoeff`、`addVia_toCoeff` を補題として証明 |
| phase-27 | `Qty.addVia_natural` と `harmonizeAddTo_decode_comp` の対応補題 |
| phase-28 | `DHNT.Qty` の乗法（`q.x * r.x`, 単位 `u * v`）と `harmonizeMul` の対応 |
