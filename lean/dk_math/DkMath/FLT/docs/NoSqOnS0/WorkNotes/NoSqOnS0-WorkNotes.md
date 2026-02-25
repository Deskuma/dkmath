# No Square on S0 Work Notes

status: 作業中 - phase-10: 完全証明への道

## Index

※以前の作業は以下、アーカイブログへ移しました。

[NoSqOnS0: phase-01](NoSqOnS0-WorkNotes-phase-01.md)
[NoSqOnS0: phase-02](NoSqOnS0-WorkNotes-phase-02.md)
[NoSqOnS0: phase-03](NoSqOnS0-WorkNotes-phase-03.md)
[NoSqOnS0: phase-04](NoSqOnS0-WorkNotes-phase-04.md)
[NoSqOnS0: phase-05](NoSqOnS0-WorkNotes-phase-05.md)
[NoSqOnS0: phase-06](NoSqOnS0-WorkNotes-phase-06.md)
[NoSqOnS0: phase-07](NoSqOnS0-WorkNotes-phase-07.md)
[NoSqOnS0: phase-08](NoSqOnS0-WorkNotes-phase-08.md)
[NoSqOnS0: phase-09](NoSqOnS0-WorkNotes-phase-09.md)

## 課題

- [ ] 仮定の証明
  - [ ] `NonLiftableS0` の証明（下降法）
  - [ ] \(3^2\) が \(S0\) を割らないことの証明（coprime だけで落ちるはず）

## 状況タスク

**現状評価**

- [x] 1. 補集合処理は既に成立しています。  
  `¬NoSq → ∃q, q^2|S0 → (q=3)∨(q≠3)` の分解と `q≠3` 側の封鎖は実装済みです（`lean/dk_math/DkMath/FLT/PhaseLift.lean:55`, `lean/dk_math/DkMath/FLT/PhaseLift.lean:143`）。
- [x] 2. 合流入口もあります。  
  `by_cases NoSqOnS0` の合流本体は `lean/dk_math/DkMath/FLT/Main.lean:221`、基底入力版は `lean/dk_math/DkMath/FLT/Main.lean:334`。
- [ ] 3. 未充足の本丸は `NonLiftableS0` の自動生成です。  
  今は `hNonLift` を入力で受けるか、`NoSq` から逆算しています。

**phase-10 攻略法（本命）**

- [ ] 1. `3` の最終整理を先に終わらせる。  
  目標補題: `Nat.Coprime c b -> ¬ 3^2 ∣ S0_nat c b`（mod3 分離仮定なし）。  
  これで `NoSqBaseInput` から `hc_nz/hb_nz/hsep` を外せる可能性が高いです。
- [ ] 2. `q≠3` の `NonLiftableS0` を「分類器 impossible」経由で機械化する。  
  既存の変換器 `nonLiftableS0_of_classifyLift_impossible`（`lean/dk_math/DkMath/FLT/CounterexamplePattern.lean:198`）を使い、足りないのは  
  `PrimitiveOnS0 -> classifyLift = impossible` の供給です。
- [ ] 3. 上の供給を下降法（または同等の反例縮小）で埋める。  
  `GEisensteinBridge` はまだ導入段階（`lean/dk_math/DkMath/FLT/GEisensteinBridge.lean`）なので、ここが最大工数です。
- [ ] 4. 最終入口を `NoSqBaseInput` 一発に統合。  
  `lean/dk_math/DkMath/FLT/Main.lean:334` を最終公開入口にし、他はラッパーに寄せる。

**保険ルート**

- [ ] 1. 「まず完全定理を公開したい」なら、既存 `Basic` 系（`FLT_case_3`, `FLT`）への橋定理を先に立てる。  
- [ ] 2. その後に phase-10 本命（下降法）を段階置換する。

この方針なら、短期で前進しつつ、最終的に“仮定なし NonLiftable”へ到達できます。  

## 状況

## A. 封印解除レポート

結論から言うと、これは **「FLT の (n=3) 版」** を、`Mathlib.FLT`（あの本丸定理）を呼ばずに、

\[
a^3 + b^3 = c^3 ;\Rightarrow; \text{矛盾}
\]

へ持っていく「自前ルートの骨組み」がちゃんと入っておる。

そして、`grep` したが **sorry は 0**、`axiom` 宣言も無し。形式的には綺麗じゃ。
ただし、`#print axioms` に出ている通り、証明全体は `propext / Classical.choice / Quot.sound` に依存しておる（これは `import Mathlib` した時点でほぼ unavoidable じゃな）。

---

## B. このファイルの勝ち筋

このファイルのメインの一撃はこれじゃ：

- まず差の立方因数分解を作る
  \[
  c^3 - b^3 = (c-b),(c^2+cb+b^2)
  \]
  ここで (S0_nat(c,b):=c^2+cb+b^2)。

- 次に「原始素因子っぽい」素数 (q) を必ず拾う（`exists_prime_factor_cube_diff`）
  \[
  q \mid (c^3-b^3)\ \wedge\ q \nmid (c-b)
  \]

- さらに “Cosmic bridge” (GN) を使って
  \[
  q \mid (c^3-b^3),\ q\nmid(c-b)\ \Rightarrow\ q\mid S0_nat(c,b)
  \]
  （`prime_dvd_S0_via_cosmic_bridge`）

- 最後に \(p\)-進評価（`padicValNat`）で上下から挟み撃ちする：

  - 下界：\(q\mid a \Rightarrow 3 \le v_q(a^3)\)
  - 上界：ある条件があれば \(v_q(c^3-b^3)\le 1\)

この「\(3 \le \cdots \le 1\)」の挟み撃ちが決まれば勝ち、という設計じゃ。

---

## C. 抜け穴の正体

ここが **抜け穴** じゃ。ズバリ：

### C.1. クリティカル仮定が “外部入力” になっている

決定打の上界 \( \le 1\) を出すところで、次の仮定が必要になっておる：

```lean
(hS0_not_sq :
  ∀ {q : ℕ}, Nat.Prime q →
    q ∣ c ^ 3 - b ^ 3 → ¬ q ∣ c - b → ¬ q ^ 2 ∣ S0_nat c b)
```

要するに、

\[
q \mid S0_nat(c,b)\ \wedge\ q\nmid(c-b)\ \Rightarrow\ q^2 \nmid S0_nat(c,b)
\]

を「証明せずに要求」しておる。
この仮定が入ると `padicValNat_upper_bound_d3` が通って、最後の矛盾が完成する仕組みじゃ。

### C.2. しかも `NoSqOnS0` は一般には偽

ファイル内でも `NoSqOnS0` を導入して仮定を言い換えておるが、これは一般には成り立たぬ。
反例は有名で、ぬしが以前触れておったやつ：

\[
18^2 + 18\cdot 1 + 1^2 = 343 = 7^3
\]

つまり \(S0_nat(18,1)\) は \(7^2\) で割れる。
だから `NoSqOnS0` を “無条件公理” にする道は塞がっておる。ここは正直で良い設計じゃ（嘘を混ぜてない）。

---

## D. 完全証明への道

このファイルは「最後の鍵穴」まで彫れておる。鍵そのものはまだ鍛造中、という状態じゃな。
で、その “鍵” を作る現実的ルートは 2 本ある。

---

### D.1. ルート1. 下降法で `NonLiftableS0` を実証する

ファイル内の用語で言えば、欲しいのはこれ：

\[
\text{PrimitiveOnS0}(c,b,q)\ \Rightarrow\ \neg(q^2 \mid S0_nat(c,b))
\]

これを “最小反例” 仮定のもとで示し、もし \(q^2\mid S0\) なら **より小さい反例** を構成して矛盾、が王道じゃ。

Lean 的には、だいたいこういう形の核が要る：

```lean
-- 最小の反例 (a,b,c) を仮定し、
-- q^2 | S0 から、より小さい (a',b',c') を構成して矛盾
theorem nonLiftableS0_of_minCounterexample
  {a b c q : ℕ} :
  -- (1) a^3 + b^3 = c^3, gcd 条件, 最小性
  -- (2) PrimitiveOnS0 c b q
  -- (3) q^2 ∣ S0_nat c b
  False := by
  ...
```

この “下降ステップの構成” には、結局 **アイゼンシュタイン整数 \(\mathbb{Z}[\omega]\)**（あるいは同等の因数分解構造）が効く。
ぬしの `GEisensteinBridge` 構想は、まさにここに刺さる。

---

### D.2. ルート2. 3 の扱いを先に完全整理して仮定を減らす

ファイル後半は「mod 3 分離（`hsep`）」で \(3\) を退けておるが、ここはもっと強く削れる可能性が高い。

実験的に調べると（賢狼が機械で小範囲探索した）、

- \(\gcd(c,b)=1\) なら \(9 \mid (c^2+cb+b^2)\) は **起きない** っぽい

実際、数論的にも自然じゃ。
\(3 \mid (c^2+cb+b^2)\) なら \(c\equiv b\pmod 3\)。そこで \(c=b+3k\) とおくと

\[
c^2+cb+b^2 = 3,(b^2+3bk+3k^2)
\]

\(\gcd(c,b)=1\) なら \(3\nmid b\) だから、括弧の中は \( \not\equiv 0\pmod 3\) で、結局 \(9\) は割らない。
つまり **「mod3 分離」なしで \(3^2\) を禁止できる**。

Lean に落とすなら、こういう補題が “効く削岩機” になる：

```lean
lemma three_sq_not_dvd_S0_of_coprime {c b : ℕ}
    (hcop : Nat.Coprime c b) :
    ¬ 3^2 ∣ S0_nat c b := by
  -- 3 | S0 -> c ≡ b [MOD 3]
  -- c=b+3k とおいて S0=3*(...) を示し、(...) が 3 で割れないを言う
  ...
```

これが入ると、後半の `hc_nz hb_nz hsep` まわりはかなり痩せる。
“鍵の鍛造” と並行で、証明木を **軽量化** できるぞ。

---

## E. まとめ

このファイルの核心はこうじゃ：

- 「原始素因子 \(q\) を拾って \(v_q\) で挟み撃ち」は **勝てる形** になっている
- ただし上界側に **非自明な鍵**（`hS0_not_sq` / `NonLiftableS0`）が残っている
- その鍵は、だいたい **下降法（＝lift を許すと小さい反例が作れる）** を形式化すれば鍛造できる
- 追加で、\(3^2\) 排除は `mod3 分離` より強く **coprime だけで落ちる** 可能性が高い（証明木のダイエット案件じゃ）

賢狼の目から見ても、ここまで彫れているのは立派じゃ。あとは「下降ステップ」を Lean の歯車に噛ませるだけ…という、いちばん美味しいところが残っておる。

## 作業ログ 2026/02/25  9:55

次の実装着手点は `three_sq_not_dvd_S0_of_coprime` です。

---

## 作業ログ 2026/02/25  10:01

- phase-10 実装（3 例外の軽量化）
  - `PhaseLift.lean` に追加:
    - `three_sq_not_dvd_S0_of_coprime`
      - 仮定: `b ≤ c` と `Nat.Coprime c b`
      - 結論: `¬ 3 ^ 2 ∣ S0_nat c b`
    - `NoSqOnS0_of_support_nonLiftable_coprime`
      - 仮定: `b ≤ c`, `Nat.Coprime c b`, `∀ q, NonLiftableS0 c b q`
      - 結論: `NoSqOnS0 c b`
      - 既存の `three_sq_dvd_of_not_NoSqOnS0_of_support_nonLiftable` と上補題を接続
  - `Main.lean` に追加:
    - `FLT_d3_by_padicValNat_of_support_nonLiftable_coprime`
      - `mod3` 分離仮定なしで `NoSq` ルートへ供給する入口

- build
  - `lake build DkMath.FLT.Main` : OK

## 作業ログ 2026/02/25  10:14

- phase-10 実装（基底入力の軽量化）
  - `PhaseLift.lean`
    - `NoSqBaseInput` から `mod3` 分離フィールド
      - `hc_nz`, `hb_nz`, `hsep`
      を除去
  - `Main.lean`
    - `FLT_d3_by_padicValNat_by_cases_NoSq_of_NoSqBaseInput` を
      `FLT_d3_by_padicValNat_of_support_nonLiftable_coprime` 経由へ切り替え
      （`mod3` 分離仮定なし）
    - `FLT_d3_by_padicValNat_of_NoSqInput` は更新済み `NoSqBaseInput` を構成して委譲
  - `README.md`
    - `NoSqBaseInput` の説明から `mod3` 条件を削除

- build
  - `lake build DkMath.FLT.Main` : OK

## 作業ログ 2026/02/25  10:18

- phase-10 実装（`NoSqInput` の軽量化）
  - `PhaseLift.lean`
    - `NoSqInput` から `mod3` 分離フィールド
      - `hc_nz`, `hb_nz`, `hsep`
      を除去
  - `README.md`
    - `NoSqInput` 説明から `mod3` 条件を削除

- build
  - `lake build DkMath.FLT.Main` : OK

## 作業ログ 2026/02/25  10:29

- phase-10 実装（`by_cases` 合流本体の `coprime` 化）
  - `Main.lean`
    - `FLT_d3_by_padicValNat_by_cases_NoSq` の入力を簡約:
      - 旧: `hSuppEx3 + hNonLift + mod3分離`
      - 新: `b ≤ c + Nat.Coprime c b + hNonLift`
    - 偽側分岐を
      - `FLT_d3_by_padicValNat_of_support_nonLiftable_coprime`
      へ接続（`mod3` 依存を除去）
    - `FLT_d3_by_padicValNat_by_cases_NoSq_of_NoSqBaseInput` は
      新しい `by_cases` 本体へ直接接続

- build
  - `lake build DkMath.FLT.Main` : OK
