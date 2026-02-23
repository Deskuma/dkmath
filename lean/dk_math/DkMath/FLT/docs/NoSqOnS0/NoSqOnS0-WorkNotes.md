# No Square on S0 Work Notes

status: 作業中 - phase-05: 補題強化

## Index

※以前の作業は以下、アーカイブログへ移しました。

[NoSqOnS0: phase-01](NoSqOnS0-WorkNotes-phase-01.md) - `hS0_not_sq` を `NoSqOnS0` に置換可能な構造にした。
[NoSqOnS0: phase-02](NoSqOnS0-WorkNotes-phase-02.md) -  x=c-b, u=b を代入して `Gx 3 x u = S0_nat c b` へ落とす橋補題を作った。
[NoSqOnS0: phase-03](NoSqOnS0-WorkNotes-phase-03.md) -  定義を固める → 判定器を実質化 → 十分条件の構築の順で実装した。
[NoSqOnS0: phase-04](NoSqOnS0-WorkNotes-phase-04.md) -  例外素数3の分離を追加して、`hHarm` + `hNoExcAll` + `hSuppEx3` + `hNonLiftAll` + mod3分離 から `AllNonLiftableOnS0` を構成するルートを作った。

## 研究課題

- 現状は  
  `harmonicEnvelope_nonLiftable仮定群 -> NoSqOnS0 -> FLT_d3...`  
  という**十分条件チェーン**。
- `NoSqOnS0 -> harmonicEnvelope_nonLiftable仮定群` は未構築で、一般には難しい。

なので、あなたの「`4` から `3+1` を一意復元できない」比喩は正確です。

一点だけ補正すると:

- `NoSqOnS0` と `a^3+b^3≠c^3` は同値ではなく、今は `NoSqOnS0` を使った**証明戦略上の強い仮定**です。
- つまり「`NoSqOnS0` を示せば FLT_d3 が出る」は真ですが、逆はこの枠組みでは要求していません。

次の実務的な研究対象としては、まさにあなたの言う `G` 多項式側です。  
特に「`hSuppEx3` と `hNonLiftAll` を `G` 側の構造補題から直接生成できるか」が次の核心です。

## 状況

**得られたヒント（要点）**

1. [ ] `G_binom` 側の最小 API は3本で十分  

   - [ ] `add_pow_gap_factor`（1 Gap 抽出）  
   - [ ] `add_pow_tail_u2`（Boundary 抽出後に `u^2`）  
   - [ ] `two_gap_xy_factor`（2 Gap 抽出で `xy`）

2. [ ] `S0` 側は mod 3 と gcd で押す方針が有効  

   - [ ] `S0 = (c-b)^2 + 3bc`  
   - [ ] `S0 ≡ (c-b)^2 [MOD 3]`  
   - [ ] `3 ∣ S0 -> 3 ∣ (c-b)` 系（門前払い）

3. [ ] 逆向き（`NoSqOnS0` から構造復元）は狙わず、  
   「構造 -> `NoSqOnS0`」の十分条件ルートを強化するのが現実的。

**次に実装すべき補題（優先順）**

1. [x] `CosmicFormulaBinom` 側に `add_pow_tail_u2`（Nat `dvd` 版まで）  
2. [x] `PhaseLift`/`CounterexamplePattern` 側で  
   `hSuppEx3` を mod 3 補題から自動生成する橋補題  
3. [x] `Main` で  
   `G_binom` API -> `hSuppEx3`/`hNonLiftAll` -> 既存 `...of_harmonicEnvelope_nonLiftable`  
   へ直結する定理を1本追加

## 作業ログ 2026/02/23 20:42 より

- phase-05 実装ステップ（G_binom API の d=3 強化）
  - `CosmicFormulaBinom.lean` に以下を追加。
    - `add_pow_gap_factor`
      - `(x+u)^d = u^d + x * GN d x u`（1 Gap 抽出 API）
    - `add_pow_tail_u2_d3`
      - `(x+u)^3 = u^3 + 3*x*u^2 + x^2*(x+3*u)`（d=3 Tail の `x^2` 因子化）
    - `add_pow_tail_u2_d3_nat_dvd`
      - `x^2 ∣ ((x+u)^3 - u^3 - 3*x*u^2)`（Nat `dvd` 版）
  - 位置づけ:
    - phase-05 優先タスク 1（`add_pow_tail_u2` の Nat 版）を、まず d=3 で導入。

- build（再確認）
  - `lake build DkMath.CosmicFormula.CosmicFormulaBinom` : OK
  - `lake build DkMath.FLT.Main` : OK

- phase-05 追加ステップ（2 Gap 抽出 API の一般 `d` 版）
  - `CosmicFormulaBinom.lean` に以下を追加。
    - `two_gap_xy_factor`
      - `(x+y)^(d+2)` から `x^(d+2), y^(d+2)` を抜いた差が `x*y` 因子を持つ一般版。
    - `two_gap_xy_factor_nat_dvd`
      - `x*y ∣ ((x+y)^(d+2) - x^(d+2) - y^(d+2))`（Nat `dvd` 版）。
    - `two_gap_xy_factor_of_two_le`
      - `2 ≤ d` 形のラッパー（`d+2` 形を通常の `d` 表記に接続）。
  - 位置づけ:
    - phase-05 の `two_gap_xy_factor` を一般化して、`G_binom` 最小 API を実質充足。

- build（再確認）
  - `lake build DkMath.CosmicFormula.CosmicFormulaBinom` : OK
  - `lake build DkMath.FLT.Main` : OK

- phase-05 実装ステップ（`hSuppEx3` 自動生成ブリッジ）
  - `PhaseLift.lean` に以下を追加。
    - `prime_not_dvd_sub_of_prime_dvd_S0_coprime_ne_three`
      - 条件: `b ≤ c`, `Nat.Coprime c b`, `Nat.Prime q`, `q ∣ S0_nat c b`, `q ≠ 3`
      - 結論: `¬ q ∣ c - b`
    - `s0PrimeSupportExceptThree_of_coprime`
      - 条件: `b ≤ c`, `Nat.Coprime c b`
      - 結論: `S0PrimeSupportExceptThree c b`
  - 位置づけ:
    - phase-05 優先タスク 2（`hSuppEx3` の自動生成）を、
      mod3 + gcd 制御を使って橋補題化。

- build（再確認）
  - `lake build DkMath.FLT.PhaseLift` : OK
  - `lake build DkMath.FLT.Main` : OK

- phase-05 実装ステップ（Main 直結版の追加）
  - `Main.lean` に派生定理を追加:
    - `FLT_d3_by_padicValNat_of_harmonicEnvelope_nonLiftable_coprimeSupport`
  - 入力:
    - 既存 `harmonicEnvelope_nonLiftable` 条件群
    - 追加で `Nat.Coprime c b`
  - 経路:
    - `s0PrimeSupportExceptThree_of_coprime`
      → `FLT_d3_by_padicValNat_of_harmonicEnvelope_nonLiftable`
  - 意味:
    - `hSuppEx3` を手で渡さず、`Coprime c b` から自動生成して Main へ直結。

- build（再確認）
  - `lake build DkMath.FLT.Main` : OK

- phase-05 追加ステップ（2 Gap 抽出 API の d=3 導入）
  - `CosmicFormulaBinom.lean` に以下を追加。
    - `two_gap_xy_factor_d3`
      - `(x+y)^3 = x^3 + y^3 + x*y*(3*(x+y))`
      - 2-gap 差分が `xy` 因子を持つことの d=3 版。
    - `two_gap_xy_factor_d3_nat_dvd`
      - `x*y ∣ ((x+y)^3 - x^3 - y^3)`（Nat `dvd` 版）
  - 位置づけ:
    - `two_gap_xy_factor` の一般 `d` 版へ進む前の、実装可能・即利用の足場。

- build（再確認）
  - `lake build DkMath.CosmicFormula.CosmicFormulaBinom` : OK
  - `lake build DkMath.FLT.Main` : OK

- phase-05 追加ステップ（`NoSqOnS0` から分類器 impossible family へ）
  - `PhaseLift.lean` に以下を追加。
    - `nonLiftableS0_all_of_NoSqOnS0`
      - 条件: `NoSqOnS0 c b`
      - 結論: `∀ q, NonLiftableS0 c b q`
    - `AllNonLiftableOnS0_of_NoSqOnS0_support`
      - 条件: prime support 条件 + `NoSqOnS0 c b`
      - 結論: `AllNonLiftableOnS0 c b`
  - `CounterexamplePattern.lean` に以下を追加。
    - `classifyLift_impossible_family_of_harmonicEnvelope_NoSq`
      - 条件: `hInfra + hHarm + hNoExcAll + NoSqOnS0`
      - 結論: `∀ q` primitive 上で `classifyLift = impossible`
  - `Main.lean` に以下を追加。
    - `FLT_d3_by_padicValNat_of_harmonicEnvelope_NoSq_coprimeSupport`
      - `NoSqOnS0` から `hClassPrim` を自動生成して
        `..._of_harmonicEnvelope_classify_coprimeSupport` へ接続。

- build（再確認）
  - `lake build DkMath.FLT.Main` : OK

- phase-05 追加ステップ（`hClassPrim` から `hNonLiftAll` 生成）
  - `Main.lean` に派生定理を追加:
    - `FLT_d3_by_padicValNat_of_harmonicEnvelope_classify_coprimeSupport`
  - 入力:
    - `hClassPrim : ∀ q, PrimitiveOnS0 c b q -> classifyLift(...) = impossible`
    - 既存の `harmonicEnvelope_*_coprimeSupport` 条件群
  - 経路:
    - `nonLiftableS0_of_classifyLift_impossible` で `hNonLiftAll` を生成
      → `FLT_d3_by_padicValNat_of_harmonicEnvelope_nonLiftable_coprimeSupport`
  - 意味:
    - `hNonLiftAll` を直接与えず、分類器 impossible family から供給可能にした。

- build（再確認）
  - `lake build DkMath.FLT.Main` : OK
