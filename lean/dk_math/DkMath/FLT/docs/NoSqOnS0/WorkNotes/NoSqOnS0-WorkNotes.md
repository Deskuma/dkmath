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
  - [x] \(3^2\) が \(S0\) を割らないことの証明（coprime だけで落ちるはず）

## 状況タスク

**現状評価**

- [x] 1. 補集合処理は既に成立しています。  
  `¬NoSq → ∃q, q^2|S0 → (q=3)∨(q≠3)` の分解と `q≠3` 側の封鎖は実装済みです（`lean/dk_math/DkMath/FLT/PhaseLift.lean:55`, `lean/dk_math/DkMath/FLT/PhaseLift.lean:143`）。
- [x] 2. 合流入口もあります。  
  `by_cases NoSqOnS0` の合流本体は `lean/dk_math/DkMath/FLT/Main.lean:221`、基底入力版は `lean/dk_math/DkMath/FLT/Main.lean:334`。
- [ ] 3. 未充足の本丸は `NonLiftableS0` の自動生成です。  
  今は `hNonLift` を入力で受けるか、`NoSq` から逆算しています。

**phase-10 攻略法（本命）**

- [x] 1. `3` の最終整理を先に終わらせる。  
  目標補題: `Nat.Coprime c b -> ¬ 3^2 ∣ S0_nat c b`（mod3 分離仮定なし）。  
  これで `NoSqBaseInput` から `hc_nz/hb_nz/hsep` を外せる可能性が高いです。
- [x] 2. `q≠3` の `NonLiftableS0` を「分類器 impossible」経由で機械化する。  
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

## 作業ログ 2026/02/25  10:59

- phase-10 実装（`classify impossible` から `NonLiftable` 全域を共通補題化）
  - `CounterexamplePattern.lean`
    - 追加:
      - `nonLiftableS0_family_of_classifyLift_impossible`
        - 入力:
          - `hbc : b < c`
          - `hClass : ∀ {q}, PrimitiveOnS0 c b q -> classifyLift ... = impossible`
        - 出力:
          - `∀ q, NonLiftableS0 c b q`
  - `Main.lean`
    - `FLT_d3_by_padicValNat_of_harmonicEnvelope_classify_coprimeSupport` の局所導出
      (`intro q` で作っていた `hNonLiftAll`) を
      上記共通補題へ置換

- build
  - `lake build DkMath.FLT.Main` : OK

## 作業ログ 2026/02/25  11:02

- phase-10 実装（下降法の標準インターフェース化）
  - `CounterexamplePattern.lean`
    - 追加:
      - `DescentClassifyImpossibleOnPrimitive (c b : ℕ) : Prop`
        - 形: `∀ {q}, PrimitiveOnS0 c b q -> classifyLift ... = impossible`
      - `nonLiftableS0_family_of_descentClassify`
        - 上記インターフェースから `∀ q, NonLiftableS0 c b q` を回収
  - `Main.lean`
    - 追加:
      - `FLT_d3_by_padicValNat_of_descentClassify_coprimeSupport`
        - 下降法側が `DescentClassifyImpossibleOnPrimitive c b` を供給すれば、
          `NonLiftable` を経由して既存の `coprimeSupport` 入口へ接続
  - `README.md`
    - 主要入口に `FLT_d3_by_padicValNat_of_descentClassify_coprimeSupport` を追記

- 位置づけ
  - 下降法そのもの（`hDescentClass` の中身）は未実装。
  - ただし、証明完成時の接続先 API は固定化できたので、
    今後は `DescentClassifyImpossibleOnPrimitive` の供給補題を埋めるだけで
    `Main` へ直結可能。

- build
  - `lake build DkMath.FLT.Main` : OK

## 作業ログ 2026/02/25  11:07

- phase-10 実装（descent インターフェースの実導線接続）
  - `CounterexamplePattern.lean`
    - 追加:
      - `descentClassifyImpossibleOnPrimitive_of_classifyFamily`
        - 既存の classify family を `DescentClassifyImpossibleOnPrimitive` へ昇格
      - `descentClassifyImpossibleOnPrimitive_of_harmonicEnvelope_NoSq`
        - `NoSq + harmonic envelope` から
          `DescentClassifyImpossibleOnPrimitive c b` を生成
  - `Main.lean`
    - `FLT_d3_by_padicValNat_of_harmonicEnvelope_NoSq_coprimeSupport` を
      直接 `descent` 入口へ接続:
      - `hDescentClass` を生成
      - `FLT_d3_by_padicValNat_of_descentClassify_coprimeSupport` へ委譲

- 位置づけ
  - 既存の `NoSq -> classify -> NonLiftable` 導線を、
    `NoSq -> descentInterface -> NonLiftable` に置換。
  - 将来、`hDescentClass` を本物の下降法で供給した際の
    接続先が既に `Main` で稼働している状態に更新。

- build
  - `lake build DkMath.FLT.Main` : OK

## 作業ログ 2026/02/25  11:12

- phase-10 実装（descent 入口の入力束追加）
  - `Main.lean`
    - 追加:
      - `DescentBaseInput (c b : ℕ)`
        - `hbc : b < c`
        - `hcb_coprime : Nat.Coprime c b`
        - `hDescentClass : DescentClassifyImpossibleOnPrimitive c b`
      - `FLT_d3_by_padicValNat_of_DescentBaseInput`
        - `DescentBaseInput` を受けて
          `FLT_d3_by_padicValNat_of_descentClassify_coprimeSupport` へ接続
  - `README.md`
    - `Main` の主要入口に `FLT_d3_by_padicValNat_of_DescentBaseInput` を追記

- 位置づけ
  - 下降法実装側は、`DescentBaseInput` ひとつを組み立てれば
    `Main` の最終入口へ即接続できる形になった。

- build
  - `lake build DkMath.FLT.Main` : OK

## 作業ログ 2026/02/25  11:25

- phase-10 実装（GEisensteinBridge へ descent 接続点を移管）
  - `GEisensteinBridge.lean`
    - 追加:
      - `descentClassifyImpossibleOnPrimitive_via_GEisenstein`
        - 入力:
          - `hbc`
          - `hInfra`
          - `hHarm`
          - `hNoExcAll`
          - `hNoSq`
        - 出力:
          - `DescentClassifyImpossibleOnPrimitive c b`
    - 位置づけ:
      - 下降法の本体実装は未投入だが、
        GEisenstein 層を経由した `descent` インターフェース供給点を確立。
  - `Main.lean`
    - `FLT_d3_by_padicValNat_of_harmonicEnvelope_NoSq_coprimeSupport` 内の
      `hDescentClass` 供給を
      `descentClassifyImpossibleOnPrimitive_via_GEisenstein` 経由へ変更。
  - `README.md`
    - `GEisensteinBridge` の責務に
      `DescentClassifyImpossibleOnPrimitive` への接続点を追記。

- build
  - `lake build DkMath.FLT.Main` : OK

## 作業ログ 2026/02/25  11:34

- phase-10 実装（GEisenstein コア述語の導入）
  - `GEisensteinBridge.lean`
    - 追加:
      - `GEisensteinDescentCore (c b : ℕ) : Prop`
        - 現段階では `DescentClassifyImpossibleOnPrimitive` の別名
      - `descentClassifyImpossibleOnPrimitive_of_GEisensteinCore`
    - `descentClassifyImpossibleOnPrimitive_via_GEisenstein` を
      上記コア述語経由の形へ更新
  - `Main.lean`
    - 追加:
      - `FLT_d3_by_padicValNat_of_GEisensteinCore_coprimeSupport`
        - `GEisensteinDescentCore` を直接受ける入口
    - `FLT_d3_by_padicValNat_of_harmonicEnvelope_NoSq_coprimeSupport` を
      `GEisensteinCore` 入口経由へ切り替え
  - `README.md`
    - 主要入口に `FLT_d3_by_padicValNat_of_GEisensteinCore_coprimeSupport` を追記

- 位置づけ
  - `Main` が `GEisenstein` 層のコア述語を直接受けられる形になった。
  - 今後は `GEisensteinDescentCore` の中身を強化（NoSq 依存の除去）すれば、
    既存の最終入口は変更せずに前進できる。

- build
  - `lake build DkMath.FLT.Main` : OK

## 作業ログ 2026/02/25  11:41

- phase-10 実装（GEisenstein コア述語の構造体化）
  - `GEisensteinBridge.lean`
    - 変更:
      - `GEisensteinDescentCore` を単なる別名から `structure` 化
        - フィールド: `classifyImpossible`
      - 追加:
        - `GEisensteinDescentCore_of_descentClassify`
        - `descentClassifyImpossibleOnPrimitive_of_GEisensteinCore`
      - `descentClassifyImpossibleOnPrimitive_via_GEisenstein` は
        構造体経由で `descent` インターフェースへ戻す形に更新
  - `Main.lean`
    - `FLT_d3_by_padicValNat_of_harmonicEnvelope_NoSq_coprimeSupport` で
      `GEisensteinDescentCore_of_descentClassify` を使って
      `GEisensteinDescentCore` を構成する形に更新
  - `README.md`
    - `GEisensteinDescentCore` が段階拡張可能なコアであることを追記

- 位置づけ
  - 下降法の本体（縮小写像・well-founded 降下）は未実装。
  - ただしコアを `structure` 化したことで、
    将来の追加証拠を破壊的変更なしで積める状態になった。

- build
  - `lake build DkMath.FLT.Main` : OK

## 作業ログ 2026/02/25  11:44

- phase-10 実装（GEisenstein 下降法フレーム枠の追加）
  - `GEisensteinBridge.lean`
    - 追加:
      - `GEisensteinDescentFrame`
        - `State`, `measure`, `step`, `step_decreases`
      - `emptyGEisensteinDescentFrame`
        - 空状態 (`PEmpty`) の最小実装
    - 変更:
      - `GEisensteinDescentCore` に `frame` フィールドを追加
      - `GEisensteinDescentCore_of_descentClassify` を `def` として追加
        （既存 classify 供給から frame 付き core を構成）
  - `README.md`
    - `GEisensteinDescentFrame` の説明を追記

- 位置づけ
  - 下降法の具体実装（非空状態・縮小写像）は未投入。
  - ただし `frame` を先に型固定したので、
    今後は `empty` を実データ実装へ置換するだけで
    既存 API を崩さず進められる。

- build
  - `lake build DkMath.FLT.Main` : OK

## 作業ログ 2026/02/25  10:53

- phase-10 API 整理（`coprimeSupport` 系の最小仮定化）
  - `Main.lean`
    - `FLT_d3_by_padicValNat_of_harmonicEnvelope_nonLiftable_coprimeSupport`
      - 未使用だった `hHarm / hNoExcAll / mod3` 引数を削除
    - `FLT_d3_by_padicValNat_of_harmonicEnvelope_classify_coprimeSupport`
      - 未使用だった `hHarm / hNoExcAll / mod3` 引数を削除
    - `FLT_d3_by_padicValNat_of_harmonicEnvelope_NoSq_coprimeSupport`
      - `mod3` 引数を削除し、上記 classify 版への接続を簡約
    - `FLT_d3_by_padicValNat_of_NoSqInput`
      - 未使用の `_hNoExcAll` 引数を削除
  - `PhaseLift.lean`
    - `three_sq_not_dvd_S0_of_coprime` 周辺の不要 `simpa` 警告を解消（証明内容は不変）
  - `README.md`
    - `*_coprimeSupport` 系が `mod3` 分離引数なしの最小入口であることを追記

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

## 作業ログ 2026/02/25  10:35

- phase-10 リファクタ（`*_coprimeSupport` ルートの一本化）
  - `Main.lean`
    - 新規:
      - `FLT_d3_by_padicValNat_of_nonLiftable_coprimeSupport`
        - `hNonLiftAll + (b<c) + coprime(c,b)` だけで供給する共通入口
    - 既存整理:
      - `FLT_d3_by_padicValNat_of_harmonicEnvelope_nonLiftable_coprimeSupport`
      - `FLT_d3_by_padicValNat_of_harmonicEnvelope_classify_coprimeSupport`
      を実質的に上記共通入口へ委譲
      （`mod3` 関連引数は互換のため受け取るのみ）
  - `README.md`
    - 主要入口に `FLT_d3_by_padicValNat_of_nonLiftable_coprimeSupport` を追加

- build
  - `lake build DkMath.FLT.Main` : OK
