# KUS transport design spec（phase-19 初稿）

## 1. 目的

本仕様は、`GKUS` における **異 support 演算** を、

- `CosmicFormula`（絶対量の生成）
- `DHNT`（調和座標への符号化）
- `KUS transport`（依存型 support の移送）

の 3 層で接続して定義するための初稿である。

設計原理は次式に集約される。

$$
US_1 \xrightarrow{\;\sigma_1\;} H \xleftarrow{\;\sigma_2\;} US_2
$$

$$
x \oplus y := \mathrm{Dec}\bigl(\mathrm{Enc}_1(x) \oplus_H \mathrm{Enc}_2(y)\bigr)
$$

ここでの要点は、**異 support 間演算を内部演算として直接定義しない** こと、および **blueprint の意味保存と表現 transport を分離** することにある。

---

## 2. 背景と問題設定

現行 `GKUS` の二項演算（`gAdd`, `gMul`, `gSub`, `gDiv`）は `GSameSupport` 前提で定義されている。

- 利点: support 保持（zero tracking）が強く保証される。
- 制約: `US_1 ≠ US_2` のとき演算を直接書けない。

異 support 演算に必要なのは、`US → US'` の一本矢印ではなく、

1. 共通調和 support へのエンコード
2. 共通 support 上での演算
3. 利用先 support へのデコード

という 3 相（encode-confluence-decode）である。

---

## 3. 三層アーキテクチャ

### 3.1 層 A: CosmicFormula（absolute layer）

役割: 宇宙式から **絶対量** を与える。

例:

$$
\mathrm{Pk}(y) := \sqrt{1+y} - 1
$$

- ここでの出力は support 非依存の実数（absolute value）。
- 非一意性はこの層には置かない。

### 3.2 層 B: DHNT（harmonic encoding layer）

役割: absolute value を support/base 相対座標へ写す。

候補:

$$
k_B(x) := \frac{\log x}{\log B}, \quad x = B^{k_B(x)}
$$

および exact harmony 指標:

$$
H(x) := \frac{\log x}{x},\qquad a^b=b^a \iff H(a)=H(b)
$$

- ここでの非一意性は「対象の非一意」ではなく「表示座標の gauge 自由度」。
- base 変更は transport law として管理する。

### 3.3 層 C: KUS（typed transport layer）

役割: DHNT 座標を `GKUS` へ載せ、依存型 blueprint を transport する。

- 現行基盤: `ScaleSpec`（`mapUnit`, `mapBlueprint`）
- 拡張点: 共通 support への合流仕様 `HarmonizeSpec`

---

## 4. 形式仕様（初稿）

### 4.1 型レベル仕様

```lean
structure HarmonizeSpec
  (U₁ : Type u₁) (B₁ : BlueprintFamily U₁)
  (U₂ : Type u₂) (B₂ : BlueprintFamily U₂)
  (H : Type uH) (BH : BlueprintFamily H) where
  enc₁ : ScaleSpec U₁ B₁ H BH
  enc₂ : ScaleSpec U₂ B₂ H BH
```

```lean
structure DecodeSpec
  (H : Type uH) (BH : BlueprintFamily H)
  (T : Type uT) (BT : BlueprintFamily T) where
  dec : ScaleSpec H BH T BT
```

### 4.2 演算仕様（GKUS）

```lean
-- encode-only（結果は H 上に保持）
def harmonizeAdd
  [Add C]
  (hs : HarmonizeSpec U₁ B₁ U₂ B₂ H BH)
  (x : GKUS C U₁ B₁) (y : GKUS C U₂ B₂)
  : GKUS C H BH :=
  let xH := ScaleSpec.scaleGKUS hs.enc₁ x
  let yH := ScaleSpec.scaleGKUS hs.enc₂ y
  gAdd xH yH (by simpa [GSameSupport])
```

```lean
-- encode-confluence-decode

def harmonizeAddTo
  [Add C]
  (hs : HarmonizeSpec U₁ B₁ U₂ B₂ H BH)
  (ds : DecodeSpec H BH T BT)
  (x : GKUS C U₁ B₁) (y : GKUS C U₂ B₂)
  : GKUS C T BT :=
  ScaleSpec.scaleGKUS ds.dec (harmonizeAdd hs x y)
```

注記:

1. 現行 `ScaleSpec` は `KUS` を対象にするため、`GKUS` 版 `scaleGKUS` の導入が前提。
2. `GSameSupport` は **H 上への encode 後** にのみ要求する。

### 4.3 基本法則（目標）

1. **Encode 後 support 一致**
   - `extract_g (enc₁ x) = extract_g (enc₂ y)`（`HarmonizeSpec` の公理／補題化）
2. **Zero tracking（合流版）**
   - 合流演算後も `extract_g` は H（または decode 先 T）を保持
3. **Decode 自然性**
   - `scale` 合成に対して演算結果が可換
4. **Gauge transport law**
   - base 変更で `k_B` が期待どおり変換される

---

## 5. 不変量と意味論

### 5.1 不変量の優先順位

1. absolute layer: `x`（または `log x`）
2. harmonic layer: `k_B(x)`（support 相対座標）
3. typed layer: `(coeff, unit, blueprint)` の transport 可能表現

### 5.2 blueprint に関する方針

- 保存したいのは blueprint の**意味**。
- `S_U = S_{U'}` の同一項保持は要求しない。
- 代わりに `mapBlueprint` による依存型 transport を要求する。

---

## 6. 実装段階（phase-19 計画）

### 6.1 phase-19a（docs-first）

1. 本 spec を確定
2. `HarmonizeSpec` / `DecodeSpec` の最小シグネチャ確定
3. 命名規約（`harmonize*`）を確定

### 6.2 phase-19b（Lean 最小導入）

1. `ScaleSpec` の `GKUS` 版 `scaleGKUS` を追加
2. `HarmonizeSpec` を `DkMath/KUS/Transport.lean`（新規）へ導入
3. `harmonizeAdd` の最小実装と `extract_g` 保持補題を追加

### 6.3 phase-19c（DHNT/Cosmic bridge）

1. `Pk(y)` から `k_B` への encode 補助定義を docs で固定
2. base 変更 law を定理化（DHNT 側）
3. `lift_B : x ↦ GKUS coeff:=k_B(x)` の bridge API を設計

---

## 7. 未決事項

1. 共通 support `H` の選択戦略
   - 左優先 / 右優先 / canonical H
2. `decode` の既定値
   - 左へ戻すか、正規形へ送るか
3. 係数再正規化
   - `coeff` 保存型 transport のみで良いか
   - `K' = Φ(K,U,U')` を導入するか
4. `ExactHarmony` / `ApproxHarmony` のどこまでを KUS 側 API に露出するか

---

## 8. 受け入れ基準（初稿）

1. 異 support 演算の定義域・値域が 3 層で説明可能である。
2. `US₁ → H ← US₂` 図式が `ScaleSpec` で型として記述できる。
3. `harmonizeAdd` の最小擬似コードが既存 `gAdd` と整合している。
4. Work Unit ログに設計判断（採用/保留）が明示される。

---

## 9. 一文要約

**異 support 演算は、CosmicFormula が与える absolute value を DHNT で調和座標化し、KUS の依存型 transport（`US₁ → H ← US₂`）で合流してから定義する。**
