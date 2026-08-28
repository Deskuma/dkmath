# CFZP-0023 — CFZP-006S von Mangoldt prime-power event classification audit 実装指示書

## 0. 作業対象

Repository:

```text
Deskuma/dkmath
```

Working branch:

```text
wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0
```

この指示書作成直前の Green checkpoint:

```text
3e47f21dd26b0003f41138d2a58b69d74bbeb503
Add: CFZP-0022: CFZP-006R prime-side interaction cutoff successor dynamics audit
```

直前 module:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaInteractionCutoffDynamicsAudit
```

006R で finite cutoff dynamics は exact に

```text
I(X+1) = I(X) + ΔI(X+1)
Residual(X+1) = Residual(X) - ΔI(X+1)
G(X+1) = G(X) - ΔI(X+1)

ΔI(n) = 2 * Λ(n) * K(n)
```

まで局所化された。

ここで

```text
I(X) := pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X
G(X) := pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X
K(n) := pascalCenteredXiPrimeSideFiniteModeKernel ε W n
Λ(n) := ArithmeticFunction.vonMangoldt n
```

と略記する。

006R では prime-power support の theorem 名を推測せず、

```lean
CfzpInteractionIncrementPrimePowerSupportBridgeGap.noPrimePowerSupportClassificationExposedHere
```

を残した。

今回 CFZP-006S では、現行 Mathlib に実在する von Mangoldt API を使い、この保留点を **prime-power event classification** として exact に閉じる。

重要:

- prime-power support の分類は閉じてよい。
- finite mode kernel `K(n)` の符号は閉じない。
- prime power であることだけから increment 非零を主張しない。`K(n)=0` の可能性がある。
- monotonicity / convergence / baseline reach / contact existence / zeta-zero / RH は今回扱わない。

---

# 1. 現行 Mathlib で確認済みの exact von Mangoldt API

現行 Mathlib source:

```text
Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
```

には次が存在する。

```lean
ArithmeticFunction.vonMangoldt_apply
ArithmeticFunction.vonMangoldt_nonneg
ArithmeticFunction.vonMangoldt_apply_pow
ArithmeticFunction.vonMangoldt_apply_prime
ArithmeticFunction.vonMangoldt_ne_zero_iff
ArithmeticFunction.vonMangoldt_pos_iff
ArithmeticFunction.vonMangoldt_eq_zero_iff
```

特に exact に

```text
ArithmeticFunction.vonMangoldt n ≠ 0 ↔ IsPrimePow n
0 < ArithmeticFunction.vonMangoldt n ↔ IsPrimePow n
ArithmeticFunction.vonMangoldt n = 0 ↔ ¬ IsPrimePow n
```

が利用できる。

さらに

```text
hp : Nat.Prime p
hk : k ≠ 0
```

なら

```text
ArithmeticFunction.vonMangoldt (p ^ k)
  = ArithmeticFunction.vonMangoldt p
  = Real.log p
```

である。

006S ではこれらを再証明しない。public API をそのまま利用する。

注意:

`IsPrimePow n` は Mathlib の prime-power predicate を正本とする。独自の prime-power predicate を新設しない。

---

# 2. 推奨 module

```text
DkMath.RH.CFBRC.CosmicFormulaZetaInteractionPrimePowerEventAudit
```

推奨 path:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaInteractionPrimePowerEventAudit.lean
```

最低限 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaInteractionCutoffDynamicsAudit
import Mathlib.Tactic
```

必要なら von Mangoldt source を明示 import してよいが、既存 import chain で利用可能なら増やさなくてよい。

`DkMath/RH.lean` に public import を追加する。

---

# 3. Gate A — von Mangoldt support を prime-power support へ公開

006R の support containment

```lean
cfzpPrimeSideInteractionCutoffIncrement_ne_zero_implies_vonMangoldt_ne_zero
```

と Mathlib theorem

```lean
ArithmeticFunction.vonMangoldt_ne_zero_iff
```

を接続し、まず exact に

```text
InteractionIncrement(ε,W,n) ≠ 0
  → IsPrimePow n
```

を公開する。

推奨 theorem 名:

```lean
cfzpPrimeSideInteractionCutoffIncrement_ne_zero_implies_isPrimePow
```

これは 006R の prime-power-support Gap を閉じる最小 theorem である。

逆向き

```text
IsPrimePow n → InteractionIncrement(n) ≠ 0
```

は **禁止**。

理由は `K(n)=0` の可能性をまだ排除していないため。

---

# 4. Gate B — increment support の exact intersection classification

006R にはさらに

```lean
cfzpPrimeSideInteractionCutoffIncrement_ne_zero_implies_modeKernel_ne_zero
```

がある。

したがって、可能なら今回の中心 support theorem として

```text
InteractionIncrement(ε,W,n) ≠ 0
  ↔ IsPrimePow n ∧ K(n) ≠ 0
```

を証明する。

推奨 theorem 名:

```lean
cfzpPrimeSideInteractionCutoffIncrement_ne_zero_iff_isPrimePow_and_modeKernel_ne_zero
```

forward:

```text
increment ≠ 0
  → vonMangoldt ≠ 0
  → IsPrimePow n

increment ≠ 0
  → K(n) ≠ 0
```

reverse:

```text
IsPrimePow n
  → vonMangoldt n ≠ 0

K(n) ≠ 0

2 ≠ 0
```

から積の非零で閉じる。

この theorem が得られるなら、finite update event の support は

```text
prime-power support ∩ nonzero mode-kernel support
```

と exact に分類される。

これは prime-power support を閉じるが、kernel support 自体を閉じるものではない。

---

# 5. Gate C — zero increment の dual classification

Gate B から安価なら

```text
InteractionIncrement(ε,W,n) = 0
  ↔ ¬ IsPrimePow n ∨ K(n) = 0
```

を公開してよい。

推奨 theorem 名:

```lean
cfzpPrimeSideInteractionCutoffIncrement_eq_zero_iff_not_isPrimePow_or_modeKernel_eq_zero
```

証明が theorem-name / simp の都合で不自然になるなら必須ではない。

ただし次節の no-prime-power no-update theorem は必須。

---

# 6. Gate D — non-prime-power step は exact no-update

Mathlib theorem

```lean
ArithmeticFunction.vonMangoldt_eq_zero_iff
```

を用いて

```text
hNP : ¬ IsPrimePow (X + 1)
```

から

```text
ArithmeticFunction.vonMangoldt (X + 1) = 0
```

を得る。

006R の no-update family に接続して、最低限次を public にする。

```text
¬ IsPrimePow (X+1)
  → I(X+1) = I(X)

¬ IsPrimePow (X+1)
  → Residual(X+1) = Residual(X)

¬ IsPrimePow (X+1)
  → G(X+1) = G(X)
```

推奨 theorem family:

```lean
cfzpAggregateRayInteractionEnergy_succ_eq_of_not_isPrimePow
cfzpRadialBudgetResidual_succ_eq_of_not_isPrimePow
cfzpRadialContactDeficit_succ_eq_of_not_isPrimePow
```

`hε : 0 < ε` 以外の heavy hypotheses を追加しない。

意味は明確に

> finite cutoff ledger は non-prime-power index では静止する

である。

これは「prime-only」ではない。**prime-power event** であることに注意する。

---

# 7. Gate E — witnessed prime-power の von Mangoldt weight を `log p` へ展開

次に witnessed prime power

```text
hp : Nat.Prime p
hk : 0 < k
hn : n = p ^ k
```

に対し exact に

```text
InteractionIncrement(ε,W,n)
  = 2 * Real.log (p : ℝ) * K(n)
```

を公開する。

推奨 theorem 名:

```lean
cfzpPrimeSideInteractionCutoffIncrement_eq_two_log_mul_modeKernel_of_eq_prime_pow
```

proof route:

```text
hn で n を p^k に rewrite
vonMangoldt_apply_pow hk.ne'
vonMangoldt_apply_prime hp
```

だけでよい。

prime-power arithmetic を再実装しない。

指数 `k=0` は禁止。`hk : 0 < k` を明示する。

---

# 8. Gate F — successor prime-power event の explicit update law

`X+1` が witnessed prime power の場合

```text
hstep : X + 1 = p ^ k
hp : Nat.Prime p
hk : 0 < k
```

に対して、006R successor law を explicit arithmetic form へ展開する。

interaction:

```text
I(X+1)
  = I(X)
    + 2 * Real.log (p : ℝ) * K(X+1)
```

residual:

```text
Residual(X+1)
  = Residual(X)
    - 2 * Real.log (p : ℝ) * K(X+1)
```

radial deficit:

```text
G(X+1)
  = G(X)
    - 2 * Real.log (p : ℝ) * K(X+1)
```

推奨 theorem family:

```lean
cfzpAggregateRayInteractionEnergy_succ_eq_of_eq_prime_pow
cfzpRadialBudgetResidual_succ_eq_of_eq_prime_pow
cfzpRadialContactDeficit_succ_eq_of_eq_prime_pow
```

ここでは `K(X+1)` の符号は何も仮定しない。

したがって update direction はまだ signed のまま。

---

# 9. Gate G — prime-power 上では von Mangoldt factor は strictly positive

Mathlib theorem

```lean
ArithmeticFunction.vonMangoldt_pos_iff
```

により

```text
hPP : IsPrimePow n
```

なら

```text
0 < ArithmeticFunction.vonMangoldt n
```

が exact に得られる。

これを CFZP-facing theorem として薄く公開する必要は原則ない。

ただし increment の sign reduction に直接使うなら local `have` で利用する。

重要な数学的整理:

```text
prime-power step では
2 * Λ(n) > 0
```

なので increment の符号を不明にしている原因は arithmetic coefficient ではなく **mode kernel `K(n)`** だけになる。

---

# 10. Gate H — optional: increment sign を mode-kernel sign へ reduction

これは **conditional classification** としてのみ optional に追加してよい。

`hPP : IsPrimePow n` の下では positive scalar multiplication なので、可能なら

```text
0 < InteractionIncrement(n) ↔ 0 < K(n)
InteractionIncrement(n) < 0 ↔ K(n) < 0
0 ≤ InteractionIncrement(n) ↔ 0 ≤ K(n)
InteractionIncrement(n) ≤ 0 ↔ K(n) ≤ 0
```

を証明してよい。

推奨 theorem family:

```lean
cfzpPrimeSideInteractionCutoffIncrement_pos_iff_modeKernel_pos_of_isPrimePow
cfzpPrimeSideInteractionCutoffIncrement_neg_iff_modeKernel_neg_of_isPrimePow
cfzpPrimeSideInteractionCutoffIncrement_nonneg_iff_modeKernel_nonneg_of_isPrimePow
cfzpPrimeSideInteractionCutoffIncrement_nonpos_iff_modeKernel_nonpos_of_isPrimePow
```

ただしこれは **符号 provider ではない**。

この theorem が言うのは

> prime-power event における increment sign problem は mode-kernel sign problem と同値

までである。

`K(n) ≥ 0` や `K(n) > 0` を無条件で追加してはならない。

proof が theorem-name 探索で重くなるなら Gate H は 006T に送ってよい。006S の必須本体は Gate A–G。

---

# 11. Gate I — event classification の public summary theorem

可能なら、006S の意味を一つの theorem / doc comment にまとめる。

最も安全な summary は

```text
non-prime-power step
  → no update

nonzero update
  → prime-power step ∧ mode kernel nonzero
```

である。

より強く Gate B が Green なら

```text
nonzero update
  ↔ prime-power step ∧ mode kernel nonzero
```

を正本 summary とする。

ここから

```text
prime power → nonzero update
```

へ短絡しない。

---

# 12. 006S 後の exact dynamics picture

006S が Green になると finite cutoff dynamics は

```text
ΔI(n) = 2 * Λ(n) * K(n)

¬ IsPrimePow n
  → ΔI(n) = 0

ΔI(n) ≠ 0
  ↔ IsPrimePow n ∧ K(n) ≠ 0
```

まで整理される。

さらに witnessed prime-power event `n=p^k`, `k>0` では

```text
ΔI(p^k)
  = 2 * log(p) * K(p^k)
```

となる。

したがって cutoff dynamics は概念的に

```text
natural-number cutoff
  ↓
non-prime-power index: static
prime-power index: signed event candidate
  ↓
positive arithmetic scale 2 log p
  ×
signed geometric/analytic mode kernel K(p^k)
  ↓
interaction update
  ↓
radial residual / contact deficit が逆向きに更新
```

と分解される。

ここで重要なのは、**event location の arithmetic problem と event direction の kernel-sign problem が分離される**ことである。

---

# 13. 今回閉じる frontier / 残す frontier

## 13.1 今回閉じてよいもの

006R marker:

```lean
CfzpInteractionIncrementPrimePowerSupportBridgeGap.noPrimePowerSupportClassificationExposedHere
```

が示した不足は、006S の新 module で public classification を与えることで実質的に閉じる。

旧 module の marker 自体を削除する必要はない。

その marker は「006R module 内では exposed していない」という履歴として整合する。

## 13.2 必ず残すもの

006R marker:

```lean
CfzpInteractionCutoffIncrementSignGap.noIndependentFiniteModeKernelSignProvider
CfzpInteractionCutoffReachDynamicsGap.noIndependentSuccessorDynamicsToBaselineReachProvider
```

に対応する frontier は未解決のまま。

必要なら 006S 側により精密な marker を一つだけ追加してよい。

候補:

```lean
inductive CfzpPrimePowerModeKernelSignGap : Prop
  | noIndependentPrimePowerModeKernelSignProvider
```

ただし marker の乱立は避ける。

---

# 14. Dependency / firewall

006S は arithmetic support classification layer である。

禁止:

- `Complex.arg`
- 新しい global `Complex.log` branch
- infinite Euler product
- `X → ∞`
- convergence claim
- unconditional monotonicity
- unconditional increment positivity / negativity
- `IsPrimePow n → K(n) ≠ 0`
- `IsPrimePow n → InteractionIncrement(n) ≠ 0`
- baseline reach の存在証明
- finite contact から pointwise source zero への短絡
- finite contact から zeta zero への短絡
- RH conclusion
- `sorry`
- `admit`
- `axiom`
- `native_decide`

また、DkMath の `VonMangoldtShadow` と Mathlib の analytic `ArithmeticFunction.vonMangoldt` を同一物として混同しない。

今回使うのは 006R が既に採用している **Mathlib `ArithmeticFunction.vonMangoldt`** である。

---

# 15. 実装順序

推奨順序:

```text
1. new module / import
2. increment nonzero → IsPrimePow
3. increment nonzero iff IsPrimePow ∧ kernel nonzero
4. optional zero classification
5. non-prime-power no-update family
6. witnessed prime-power increment = 2 log p * kernel
7. successor prime-power explicit update family
8. optional sign reduction
9. frontier marker / module documentation
10. DkMath/RH.lean public import
```

まず support bridge を最短 proof で通し、その後 update API を積む。

---

# 16. 成功条件

006S Green 条件:

1. `CosmicFormulaZetaInteractionPrimePowerEventAudit.lean` を追加。
2. `DkMath/RH.lean` に public import。
3. `InteractionIncrement ≠ 0 → IsPrimePow n` を public theorem 化。
4. 可能な限り `InteractionIncrement ≠ 0 ↔ IsPrimePow n ∧ K(n) ≠ 0` を exact に証明。
5. `¬ IsPrimePow (X+1)` による interaction no-update theorem。
6. 同条件で residual no-update theorem。
7. 同条件で radial contact deficit no-update theorem。
8. witnessed `n=p^k`, `k>0` で increment を `2 * log p * K(n)` へ exact 展開。
9. witnessed prime-power successor interaction update を公開。
10. witnessed prime-power successor residual update を公開。
11. witnessed prime-power successor radial-deficit update を公開。
12. prime-power だけから kernel 非零を主張しない。
13. prime-power だけから increment 非零を主張しない。
14. kernel の unconditional sign theorem を追加しない。
15. monotonicity / convergence / reach を追加しない。
16. zeta-zero / RH conclusion を追加しない。
17. target module build Green。
18. `lake build DkMath.RH` Green。
19. `./lean-build.sh` Green。
20. `./lean-test.sh` Green。
21. `git diff --check` Green。
22. new module に `sorry`, `admit`, `axiom`, `native_decide` なし。
23. new module に新規 `Complex.arg` / global `Complex.log` branch なし。

---

# 17. 006T への候補

006S が Green になった後の第一候補は

```text
CFZP-006T — prime-power mode-kernel phase/sign audit
```

である。

006S により arithmetic coefficient は prime-power event 上 strictly positive と分離されるため、残る update direction は

```text
K(p^k)
```

の sign problem に集中できる。

006T では既存 geometric-ray / normalized-ray / signed-numerator API を監査し、

```text
K(p^k)
```

をどこまで explicit phase / signed numerator へ branch-free に降ろせるかを調べる。

ただし 006S の段階ではそこへ踏み込まない。

---

# 18. 006S の位置づけ

006R は cutoff dynamics を

```text
ΔI(n) = 2 * Λ(n) * K(n)
```

まで局所化した。

006S の役割は、ここから arithmetic support を剥がし、

```text
更新が起こり得る場所 = prime-power indices
更新が実際に非零となる条件 = prime-power ∧ K(n) ≠ 0
更新方向を決める未解決量 = sign K(n)
```

という三段階へ exact に分離することである。

この分離が Green になれば、次の研究対象は arithmetic support ではなく finite mode kernel の位相・符号構造であることが明確になる。
