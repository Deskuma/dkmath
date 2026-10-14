# Report 014 — bundled Eisenstein residue maps and ideal kernels

Date: 2026-10-10 (JST). **Step 014 COMPLETE / Outcome B.** Initial clean HEAD `622961480df6f99d7d51b6a4cb3a700cbd334d1d`, branch `feature/GTail-SelectiveGap-FLT7-261009-v0`.

## 結果と変更対象

Step 013 の root-guarded evaluation を真の `TraceOneInt (-1) →+* ZMod q` に束ね、その kernel を既存環の実際の Ideal として定義した。任意の integral element z に対し、整数 norm の剰余は２共役評価の積に等しい。q が素数で根 t が供給されていれば、整数 norm の q 整除と、いずれかの kernel membership が同値になる。

canonical α の向きは既存の評価結果から取得し、q≠3 では異なる２ ideal を示した。optional gate として全射性と prime q での kernel 極大性も証明し、q=43 の素性を test で実際に確認した。これは既存 TraceOneInt(-1) の ideal についての結論であり、cyclotomic carrier の ideal への同定ではない。

変更対象は production `DkMath/Lib/NumberTheory/GTailSevenResidueIdeal.lean`、direct test `DkMathTest/NumberTheory/GTailSevenResidueIdeal.lean`、source-inventory-014、report-014、ROADMAP の追記。２定義・14公開定理、20 examples。MIT header、import後の file print、namespace とインデントは既存スタイルに合わせた。

## 全公開署名

名前空間 `DkMath.Lib.NumberTheory`、open `DkMath.NumberTheory.TraceOneQuadratic`。

```lean
def eisensteinResidueRingHom {q : ℕ} (t : ZMod q) (ht : t ^ 2 - t + 1 = 0) :
    TraceOneInt (-1) →+* ZMod q

theorem eisensteinResidueRingHom_apply {q : ℕ} (t : ZMod q)
    (ht : t ^ 2 - t + 1 = 0) (z : TraceOneInt (-1)) :
    eisensteinResidueRingHom t ht z = eisensteinResidueEval t z

theorem eisensteinResidueRingHom_ofInt {q : ℕ} (t : ZMod q)
    (ht : t ^ 2 - t + 1 = 0) (n : ℤ) :
    eisensteinResidueRingHom t ht (ofInt (-1) n) = (n : ZMod q)

theorem eisensteinResidueRingHom_tau {q : ℕ} (t : ZMod q)
    (ht : t ^ 2 - t + 1 = 0) :
    eisensteinResidueRingHom t ht (tau (-1)) = t

theorem eisensteinResidue_conjugate_root {q : ℕ} (t : ZMod q)
    (ht : t ^ 2 - t + 1 = 0) : (1 - t) ^ 2 - (1 - t) + 1 = 0

theorem eisensteinResidueRingHom_conj {q : ℕ} (t : ZMod q)
    (ht : t ^ 2 - t + 1 = 0) (z : TraceOneInt (-1)) :
    eisensteinResidueRingHom t ht (conj z) =
      eisensteinResidueRingHom (1 - t) (eisensteinResidue_conjugate_root t ht) z

def eisensteinResidueIdeal {q : ℕ} (t : ZMod q) (ht : t ^ 2 - t + 1 = 0) :
    Ideal (TraceOneInt (-1))

theorem mem_eisensteinResidueIdeal_iff {q : ℕ} (t : ZMod q)
    (ht : t ^ 2 - t + 1 = 0) (z : TraceOneInt (-1)) :
    z ∈ eisensteinResidueIdeal t ht ↔ eisensteinResidueEval t z = 0

theorem norm_cast_eq_eisensteinResidue_product {q : ℕ} (t : ZMod q)
    (ht : t ^ 2 - t + 1 = 0) (z : TraceOneInt (-1)) :
    (norm z : ZMod q) = eisensteinResidueEval t z * eisensteinResidueEval (1 - t) z

theorem prime_dvd_norm_iff_mem_eisensteinResidueIdeals {q : ℕ}
    (hq : Nat.Prime q) (t : ZMod q) (ht : t ^ 2 - t + 1 = 0)
    (z : TraceOneInt (-1)) :
    (q : ℤ) ∣ norm z ↔ z ∈ eisensteinResidueIdeal t ht ∨
      z ∈ eisensteinResidueIdeal (1 - t) (eisensteinResidue_conjugate_root t ht)

theorem scalar_mem_eisensteinResidueIdeal {q : ℕ} (t : ZMod q)
    (ht : t ^ 2 - t + 1 = 0) : ofInt (-1) (q : ℤ) ∈ eisensteinResidueIdeal t ht

theorem eisensteinResidueRingHom_surjective {q : ℕ} (t : ZMod q)
    (ht : t ^ 2 - t + 1 = 0) : Function.Surjective (eisensteinResidueRingHom t ht)

theorem eisensteinResidueIdeal_isMaximal {q : ℕ} (hq : Nat.Prime q)
    (t : ZMod q) (ht : t ^ 2 - t + 1 = 0) : (eisensteinResidueIdeal t ht).IsMaximal

theorem gtailSevenNormCoord_mem_residueIdeal {q a b : ℕ} [Fact (Nat.Prime q)]
    (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hb : ¬ q ∣ b) :
    gtailSevenNormCoord a b ∈ eisensteinResidueIdeal (gtailSevenResidueRoot q a b)
      (gtailSevenResidueRoot_polynomial hQ hb)

theorem gtailSevenNormCoord_not_mem_conjugate_residueIdeal {q a b : ℕ}
    [Fact (Nat.Prime q)] (hq3 : q ≠ 3)
    (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hb : ¬ q ∣ b) :
    gtailSevenNormCoord a b ∉ eisensteinResidueIdeal (1 - gtailSevenResidueRoot q a b)
      (gtailSevenResidueRoot_conjugate_polynomial hQ hb)

theorem gtailSevenResidueIdeals_ne_conjugate {q a b : ℕ} [Fact (Nat.Prime q)]
    (hq3 : q ≠ 3) (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hb : ¬ q ∣ b) :
    eisensteinResidueIdeal (gtailSevenResidueRoot q a b)
        (gtailSevenResidueRoot_polynomial hQ hb) ≠
      eisensteinResidueIdeal (1 - gtailSevenResidueRoot q a b)
        (gtailSevenResidueRoot_conjugate_polynomial hQ hb)
```

hom の toFun は既存 `eisensteinResidueEval t`、add/mul law は既存 Step 013 定理をそのまま使用。0/1 law は既存の literal coordinates から証明した。ideal の本体は `RingHom.ker (eisensteinResidueRingHom t ht)`。

## 仮定・型・証明経路

Root proof ht を持たない parameter から RingHom を構成していない。hom、共役 root、norm-product、surjection、scalar q membership に primality は不要。整数 ofInt の像は整数 cast、tau の像は t と証明した。共役側の hom も同じ guarded interface を使い、1-t の root proof は ht の直接の polynomial consequence。

任意 z の `traceOne_mul_conj z` を hom で写し、map_mul、ofInt の像、Step 013 eval_conj を使って normalized norm-product を導いた。quartic などの独立展開による代替 Norm は導入していない。norm z は ℤ であり、その ℤ→ZMod cast を署名に保持している。

prime-divisor iff は hq から `Fact` を設置し、`← CharP.intCast_eq_zero_iff (ZMod q) q (norm z)`、norm-product、kernel membership iff を rewrite した後に field の mul_eq_zero を使う。root t の存在は仮定であり、inert prime を含め全 q が split する定理ではない。

surjection は `ZMod.intCast_surjective` で n:ℤ を得て ofInt(-1)n を前像にする。maximality はこのチェック済み全射性を `RingHom.ker_isMaximal_of_surjective` に渡す。q が素数という gate の下でのみ field codomain を使う。kernel を定義しただけで極大・素と呼んでいない。

α membership、conjugate側 nonmembership は既存の zero/nonzero evaluations と kernel iff から導いた。ideal の相違は実際の membership witness α で証明し、異なる root の名前だけから推論していない。

## API 重複と import 比較

production は Step 013 module と `Mathlib.RingTheory.Ideal.Maps` のみ、test は新 production のみを import。TraceOneResidueType.residueMap / Mathlib QuadraticAlgebra.lift の合成候補を source 比較した。２座標 residueMap と root評価の合成は同じ coordinate expression を表せるが、既存 classification owner を追加 import することになる。直接の laws packaging は Step 013 と定義的に一致し、既存乗法証明を再利用する。

静的 closure 比較は direct1364 source names に対し、既存 residueMap owner を追加する hypothetical union1684、差320（local2）だった。この比較は合成実装・タイミング検証ではない。詳細と exact APIs は [source-inventory-014.md](source-inventory-014.md)。optional FLT owner は追加していない。

## 実行した focused builds

process-local `LEAN_NUM_THREADS=2`、逐次 incremental。実行履歴:

| Command (cwd: `lean/dk_math`) | Exit | Seconds | Log |
|---|---:|---:|---|
| `LEAN_NUM_THREADS=2 lake build DkMath.Lib.NumberTheory.GTailSevenResidueIdeal` | 0 | 3.9 | `.lake/build/gtail-step014/01-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.NumberTheory.GTailSevenResidueIdeal` | 1 | 4.48 | `.lake/build/gtail-step014/02-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.NumberTheory.GTailSevenResidueIdeal` | 0 | 4.51 | `.lake/build/gtail-step014/03-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.NumberTheory.GTailSevenEisensteinResidue` | 0 | 1.64 | `.lake/build/gtail-step014/04-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.NumberTheory.GTailSevenResidueIdeal` | 0 | 4.49 | `.lake/build/gtail-step014/05-build.log` |

最終版の新規２ターゲットと Step 013 回帰はすべて exit0。full clean/all-test build は実行していない。

production は初回で成功した。02 の test 失敗は local notation `P37.IsMaximal/IsPrime` が identifier として読まれた問題と、q=3 kernel equality で root proof に依存した型への直接 rewrite の motive 不一致。前者は `(P37).IsMaximal/IsPrime` に修正。後者は ideal extensionality と membership iff を経由し、proof 非依存の eval parameter を rewrite した。03 で20 examplesが成功。極大性の proposition に対する `letI` を `let` とする lint 提案が残ったため従い、05 で warning なしの最終 test build が成功した。production の命題・前提・既存 ring/source は変更していない。

## Public #print axioms

05 の新公開16シンボルを折返し行も含め抽出した。すべて標準基礎のみ。

| Symbol | Axioms |
|---|---|
| `eisensteinResidueRingHom` | `[propext, Quot.sound]` |
| `eisensteinResidueRingHom_apply` | `[propext, Quot.sound]` |
| `eisensteinResidueRingHom_ofInt` | `[propext, Quot.sound]` |
| `eisensteinResidueRingHom_tau` | `[propext, Quot.sound]` |
| `eisensteinResidue_conjugate_root` | `[propext, Quot.sound]` |
| `eisensteinResidueRingHom_conj` | `[propext, Quot.sound]` |
| `eisensteinResidueIdeal` | `[propext, Quot.sound]` |
| `mem_eisensteinResidueIdeal_iff` | `[propext, Quot.sound]` |
| `norm_cast_eq_eisensteinResidue_product` | `[propext, Quot.sound]` |
| `prime_dvd_norm_iff_mem_eisensteinResidueIdeals` | `[propext, Classical.choice, Quot.sound]` |
| `scalar_mem_eisensteinResidueIdeal` | `[propext, Quot.sound]` |
| `eisensteinResidueRingHom_surjective` | `[propext, Quot.sound]` |
| `eisensteinResidueIdeal_isMaximal` | `[propext, Classical.choice, Quot.sound]` |
| `gtailSevenNormCoord_mem_residueIdeal` | `[propext, Classical.choice, Quot.sound]` |
| `gtailSevenNormCoord_not_mem_conjugate_residueIdeal` | `[propext, Classical.choice, Quot.sound]` |
| `gtailSevenResidueIdeals_ne_conjugate` | `[propext, Classical.choice, Quot.sound]` |

## Leanで確認した例と観察

- q=43,a=5,b=8: Q=129=3*43、canonical t=37、1-t=7。division の値は div_eq_iff と小さい finite multiplication で検査した。
- α は P37 に属し、P7 に属さない。ideal membership iff を通して bundled kernel で検査し、α の witness から P37≠P7 を直接証明した。canonical distinctness endpoint も適用した。
- conj α の hom 像は37で18、7で0。共役は P7 に属し P37 には属さない。
- embedded scalar43 は両 ideal に属する一方、scalar ring element43 は α を割らない。前者は ideal membership、後者は ring-element divisibility であり、同じ「整除」として混同できない。
- prime norm-divisor iff から43∣norm α を取得した。任意の signed-coordinate z についての一般 iff example もそのまま適用した。
- z=⟨-2,3⟩ の norm-product theorem を検査し、負の integral coordinate の cast が２評価と両立することを確認した。
- P37 の IsMaximal を新定理で取得し、その instance から IsPrime を取得する example が通った。optional gate は確認済み。
- q=3,a=b=1: canonical t=2=1-t、root2の kernel と conjugate kernel が同じ ideal であり、α はそこに属する。q≠3 の distinctness はここに一般化しない。
- 非根 t=0 in ZMod43: t²-t+1≠0、tau² の評価≠tauの評価の平方を具体的に検査した。ht を省略した乗法保存はこの例で失敗する。

剰余 norm の積が0であることは、２ slot の少なくとも一方に入ることを意味する。両方に入るという結論ではなく、q=43 の α がその違いを実際に示す。極大 kernel を得ても、それだけでは特定元の唯一の素因子配分や principal ideal product の等式にならない。

## 次の命題・実装提案（未実施）

principal scalar ideal の分解を次に検討するなら、同じ TraceOneInt(-1) の中で、まず両 kernel の交わりを `Ideal.span {ofInt (-1) (q:ℤ)}` と同定する具体的な coordinate lemma が必要になる。２評価がともに0から、根の差の非零性を使って両 integral coordinates の q 整除を導き、scalar quotient を構成する方向を別途証明する必要がある。その上で distinct maximal ideals の comaximality と product=intersection を正しい Mathlib ideal API で確認する。この段階ではどちらも実装・検査していない。

また既存 residueMap/lift 合成との certified equality は将来の互換 adapter 候補だが、現在の定義的 eval 一致に加えて必要な利用先が現れた場合の課題とする。GTail q-supportから cyclotomic ideal/ramified-root packet への具体的 carrier map、単元類、norm-squareから元の平方の復元、次の正の原始 Fermat tuple・下降は未実装。

Outcome B: root-guarded RingHom、checked ideal kernels、norm-product/prime-divisor receiver と oriented membership。独立の新 FLT7 obstruction/closure ではない。Step014で停止。

## Final source and graph audit

新規２ Lean source に sorry/admit/new axiom/unsafe/False.elim/exfalso/native_decide/FLT impossibility endpoint の禁止構文なし。末尾改行・行末空白検査は成功。最終 production/test/regression ログに warning/error なし。新規文書と ROADMAP 追記部分の空白検査も成功し、ROADMAP の旧本文を保存した。

Comment-stripped import-header closure: production1364 source names/12 local modules、test1365/13。ローカル union13 vertices の DFS に cycle なし、neutral closure に FLT module なし。結果 `.lake/build/gtail-step014/imports.json`。source counts は external terminal を含み、build jobs や closure 全体の axiom/hole 検査とは異なる。

HEAD と byte 比較した既存49ファイル（存在する root/driver、Lake/toolchain/facade、既存 ring/residue/lattice/coordinate owners、GTail neutral/FLT owners と対応 tests、歴史的 ledger）は変更なし。`git diff --check` の検査対象は tracked diff、新規 source/doc の空白は上記の別検査で扱った。
