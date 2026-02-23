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

1. [ ] `CosmicFormulaBinom` 側に `add_pow_tail_u2`（Nat `dvd` 版まで）  
2. [ ] `PhaseLift`/`CounterexamplePattern` 側で  
   `hSuppEx3` を mod 3 補題から自動生成する橋補題  
3. [ ] `Main` で  
   `G_binom` API -> `hSuppEx3`/`hNonLiftAll` -> 既存 `...of_harmonicEnvelope_nonLiftable`  
   へ直結する定理を1本追加

## 作業ログ 2026/02/23 20:42 より
