# ABC038 Bridge Dependency

最終更新: 2026/04/18

## 目的

`ABC038.quality_le_of_not_bad_with_tail` / `quality_le_of_not_bad_with_log`
へ `PrimitiveWitnessFamily` の counting spine を差し込む前段として、

- 何を bridge から供給したいか
- どの theorem 名の層に分けると Lean 実装しやすいか
- いま足りないのが family existence / diff-triple 対応 / coprimality transport のどれか

を整理する。

---

## 既存の入口

対象 theorem:

- [ABC038.lean](/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMath/ABC/ABC038.lean)
  - `quality_le_of_not_bad_with_tail`
  - `quality_le_of_not_bad_with_log`

既存入力:

1. `¬Bad δ (Triple.mk a b c hsum hcop)`
   - `piSqRad c ≤ (rad (a * b)) ^ δ` を supply
2. `TailBound γ a b c`
   - `twoTail c ≤ (rad (a * b)) ^ γ` を supply
3. `δ + γ ≤ ε`
   - quality bound へ合成

bridge 側が現に supply できるもの:

- `F.channelProduct ≤ ABC.rad (u)`
- `2 ^ F.channelCount ≤ ABC.rad (u)`
- exact-rad class に対する count upper bound

ここで `u` は現状 `a ^ d - b ^ d` のような diff quantity。

---

## 問題の芯

`ABC038` 側は `ABC.rad (a * b)` を使う。

bridge 側は `ABC.rad (diff)` を supply する。

したがって直接必要なのは、次のいずれか。

1. `diff = a * b` あるいは `rad diff = rad (a * b)` 型の対応
2. `rad diff` の下界が、そのまま `rad (a * b)` を含む quality/tail budget に効く中間命題

現状はここが未実装。

---

## 中間命題候補

### Candidate A: radical transport

狙い:

- diff 側の radical lower bound を `rad (a * b)` lower bound へ運ぶ。

候補 theorem 名:

- `rad_mul_input_ge_of_rad_diff_ge`
- `abc_rad_mul_input_ge_of_rad_diff_ge`

想定 statement の形:

```lean
theorem abc_rad_mul_input_ge_of_rad_diff_ge
    {m a b : ℕ}
    (hrad_transport : ABC.rad m ≤ ABC.rad (a * b)) :
    R ≤ ABC.rad m ->
    R ≤ ABC.rad (a * b)
```

必要なもの:

- `rad diff ≤ rad (a * b)` のような transport hypothesis

不足の種類:

- diff-triple 対応

判定:

- 最も薄い transport 層。
- ただしこれだけでは family existence は供給しない。

---

### Candidate B: witness family on triple

狙い:

- `PrimitiveWitnessFamily` がどの triple / diff に属するかを package 化する。

候補 theorem / structure 名:

- `PrimitiveWitnessFamilyOnTriple`
- `primitiveWitnessFamily_on_triple_gives_rad_diff_lower_bound`

想定 statement の形:

```lean
structure PrimitiveWitnessFamilyOnTriple (a b c d : ℕ) where
  hsum : a + b = c
  hdiff : c = a ^ d - b ^ d
  family : PrimitiveWitnessFamily a b d
```

あるいは lighter に

```lean
theorem primitive_witness_family_gives_abc_rad_diff_lower_bound
    (htriple : c = a ^ d - b ^ d)
    (F : PrimitiveWitnessFamily a b d) :
    2 ^ F.channelCount ≤ ABC.rad c
```

必要なもの:

- diff と triple target `c` の同一視

不足の種類:

- family existence / packaging

判定:

- `ABC038` 側へ差し込む時の canonical bridge 層になりうる。
- ただし今は package を増やしすぎない方が安全。

---

### Candidate C: quality-input lower bound wrapper

狙い:

- `ABC038` が本当に欲しい `rad (a * b)` lower bound を、直接 quality 入力の名前で渡す。

候補 theorem 名:

- `primitive_channel_count_forces_quality_rad_input`
- `primitive_channel_product_forces_quality_rad_input`

想定 statement の形:

```lean
theorem primitive_channel_count_forces_quality_rad_input
    (F : PrimitiveWitnessFamily a b d)
    (htransport : ABC.rad (a ^ d - b ^ d) ≤ ABC.rad (a * b))
    (hdiff_ne : a ^ d - b ^ d ≠ 0) :
    2 ^ F.channelCount ≤ ABC.rad (a * b)
```

必要なもの:

- Candidate A の transport

不足の種類:

- diff-triple 対応
- transport hypothesis

判定:

- `ABC038` へ最も直接刺さる形。
- ただし transport を theorem hypothesis に残す限り、実装はかなり軽い。

---

## 依存チェーン案

最小実装順は次。

1. `primitive_witness_family_gives_abc_rad_diff_lower_bound`
   - 既存 `pow_channelCount_le_abc_rad_diff` の target rename
   - `c = a ^ d - b ^ d` で transport

2. `primitive_channel_count_forces_quality_rad_input`
   - `ABC.rad diff ≤ ABC.rad (a * b)` を仮定して
   - `2 ^ count ≤ ABC.rad (a * b)` を出す

3. `quality_le_of_not_bad_with_tail` の前に置く薄い wrapper
   - ここではまだ quality theorem を書き換えず、
     その入力へ必要な lower bound が何かを theorem 名で固定する

---

## いま足りないものの分類

### 1. family existence

不足か:

- 場合による。

現時点:

- concrete sample ではある。
- 一般 theorem としてはまだない。

### 2. diff-triple 対応

不足か:

- はい。

理由:

- bridge 側は `a ^ d - b ^ d`
- quality 側は triple target `c`

この identification が要る。

### 3. coprimality / divisibility transport

不足か:

- 現段階では主因ではない。

理由:

- `ABC038` の quality theorem は `hcop : Nat.Coprime a b` をすでに入力で持つ。
- まず先に必要なのは radical target の transport。

---

## 次の Lean 実装候補

最小で行くなら次の 2 本。

1. `primitive_witness_family_gives_abc_rad_target_lower_bound`
   - `c = a ^ d - b ^ d` を仮定して
   - `2 ^ count ≤ ABC.rad c`

2. `primitive_channel_count_forces_quality_rad_input`
   - `ABC.rad c ≤ ABC.rad (a * b)` を仮定して
   - `2 ^ count ≤ ABC.rad (a * b)`

この 2 本なら、まだ `ABC038` 自体を書き換えずに
「quality 入力に bridge をどう差し込むか」を theorem 名レベルで固定できる。
