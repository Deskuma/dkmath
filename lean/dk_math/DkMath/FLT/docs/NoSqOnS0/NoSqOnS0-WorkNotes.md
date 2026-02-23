# No Square on S0 Work Notes

status: 作業中 - phase-04:

## Index

※以前の作業は以下、アーカイブログへ移しました。

[NoSqOnS0: phase-01](NoSqOnS0-WorkNotes-phase-01.md) - `hS0_not_sq` を `NoSqOnS0` に置換可能な構造にした。
[NoSqOnS0: phase-02](NoSqOnS0-WorkNotes-phase-02.md) -  x=c-b, u=b を代入して `Gx 3 x u = S0_nat c b` へ落とす橋補題を作った。
[NoSqOnS0: phase-03](NoSqOnS0-WorkNotes-phase-03.md) -  定義を固める → 判定器を実質化 → 十分条件の構築の順で実装した。

## 状況

ここからは「仮定を細分化して、各仮定を補題で潰す」設計にします。

**ゴール**

- 今の `NonExceptionalHarmonicOnS0 -> NoSqOnS0` を、単なる定義展開ではなく実質定理に置換する。

### 1. 仮定を分解（何を証明すればよいか固定）

`NoSqOnS0 c b` は本質的に次の2段です。

1. `q ∣ c^3-b^3 ∧ q ∤ c-b -> q ∣ S0(c,b)`  
  これは既に `CosmicPetalBridge` で確保済み。

2. `q ∣ S0(c,b) -> ¬ q^2 ∣ S0(c,b)`  
  ★ここが未解決（主戦場）。

この2をさらに分解して証明可能な形へ落とす。

### 2. 新しい中間述語を導入（PhaseLift）

`PhaseLift.lean` に以下を追加。

1. [x] `PrimitiveOnS0 c b q`  

   - `Nat.Prime q ∧ q ∣ S0_nat c b ∧ ¬ q ∣ c-b`

2. [x] `NonLiftableS0 c b q`  

   - `PrimitiveOnS0 c b q -> ¬ q^2 ∣ S0_nat c b`

3. [ ] `AllNonLiftableOnS0 c b`  

   - `∀ q, PrimitiveOnS0 c b q -> ¬ q^2 ∣ S0_nat c b`

    その上で

   - `NoSqOnS0_of_AllNonLiftableOnS0 : AllNonLiftableOnS0 c b -> NoSqOnS0 c b`

    を作る。

### 3. PetalCoreUnit/Harmonic 側を証明可能形へ接続

`PetalCoreUnit.lean` + `CounterexamplePattern.lean` で、

1. [ ] `NonExceptionalHarmonicOnS0 -> AllNonLiftableOnS0`  
のスケルトン補題を追加（最初は弱い仮定込みで良い）。

2. [ ] `exceptional -> undecided` は実装済みなので、  
`non-exceptional ∧ harmonic` 側で `impossible` に寄せる補題を増やす。

### 4. Main の接続先を差し替え

`Main.lean` で最終的に

1. `...of_nonExceptionalHarmonic` が
2. `NoSqOnS0_of_AllNonLiftableOnS0` 経由で
3. `FLT_d3_by_padicValNat_of_NoSqOnS0` に流れる

という1本線にする。

### 5. 実装順（最短）

1. [ ] `PhaseLift`: `PrimitiveOnS0 / NonLiftableS0 / AllNonLiftableOnS0`
2. [ ] `PhaseLift`: `NoSqOnS0_of_AllNonLiftableOnS0`
3. [ ] `PetalCoreUnit` or `CounterexamplePattern`: `NonExceptionalHarmonicOnS0 -> AllNonLiftableOnS0`（暫定版）
4. [ ] `Main`: 派生定理を新ルートに差し替え
5. [ ] build + WorkNotes更新

## 2026-02-26 作業ログ（現時点まとめ）

- `PhaseLift.lean`
  - `PrimitiveOnS0`, `NonLiftableS0`, `AllNonLiftableOnS0` を追加。
  - `NoSqOnS0_of_AllNonLiftableOnS0` を追加。
  - `AllNonLiftableOnS0` は実装上、次の2条件の組にした。
    - `q ∣ S0_nat c b` な素数は `q ∤ c-b`（primitive support）
    - `PrimitiveOnS0 c b q -> ¬ q^2 ∣ S0_nat c b`（non-liftable）
  - `NonExceptionalHarmonicOnS0` を `(... witness ...) ∧ AllNonLiftableOnS0 c b` に更新。
  - `AllNonLiftableOnS0_of_nonExceptionalHarmonic` を追加。

- `Main.lean`
  - `FLT_d3_by_padicValNat_of_nonExceptionalHarmonic` を
    `AllNonLiftableOnS0_of_nonExceptionalHarmonic`
    → `NoSqOnS0_of_AllNonLiftableOnS0`
    → `FLT_d3_by_padicValNat_of_NoSqOnS0`
    の順で接続する形に差し替え。

- build
  - `lake build DkMath.FLT.PhaseLift` : OK
  - `lake build DkMath.FLT.Main` : OK
  - 既知 warning（`ZsigmondyCyclotomic`, `GcdNext` の `sorry` 由来）は継続。
