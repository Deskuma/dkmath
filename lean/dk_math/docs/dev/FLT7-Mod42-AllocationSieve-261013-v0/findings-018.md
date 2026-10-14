# findings-018 — same-packet source valuation ledger

2026-10-14。Outcome A（形式化）。数学的独立性・新規制約については下記の評価に限る。

## 棚卸し

既存 `RamifiedRealCubicNormPacket.exists_inner_complementary_seventh_root` は、同一 source norm packet K の actual M=|K.innerSndRoot| と実際の complementary N に対し、N>0、M*N=V*C、Coprime M N、7∤N を与える。

`internalDepthFourAllocation_prime_support` は r∈M.divisors と prime ℓ∣r から ℓ∤N と ℓ∣V∨ℓ∣C を与える。同じ実ソースに今回の exact valuation equality は確認できなかった。既存索引の valuation_balance 検索は0件、prime-support は1件。Nat.factorization の積加法と prime specialization、Mathlib padicValNat.mul と eq_zero_of_not_dvd を調査した。新規名の実ソース検索でも重複なし。

## 証明した保存則

同じ p と K、M,V,C を維持し、ℓ prime と ℓ∣M のみを追加して、実際の N の存在を伴う

```text
ℓ∤N
vℓ(M)=vℓ(V)+vℓ(C)
```

を証明した。hrec、hcore factorization、chosen r/s、natural endpoints は使っていない。

M>0 は既存 source theorem、N>0 は実際の root extraction から得る。M*N=V*C で V*C≠0 を導き、各 V,C≠0 を取り出す。padicValNat.mul は prime instance と各因子非零を要求するため、この証明で明示的に供給した。Coprime M N と ℓ∣M から ℓ∤N、従って vℓ(N)=0。付値を積等式へ適用して保存則となる。Nat.factorization ℓ での同じ equality も test で確認した。

## 実ソースから得た追加の所有制約

探索中、canonical split の既存 `vertical_coprime_compensation_residual` を確認した。これは Coprime V (compensationCore*residualRoot) を source-only で与える。actual quadratic packet の compensationCore=C^7 と C∣C^7 から Coprime V C を導ける。この coprimality を仮定として追加せず、source-indexed theorem として形式化した。

従って ℓ∣M の場合は

```text
(ℓ∣V, ℓ∤C, vℓ(M)=vℓ(V))
  or (ℓ∣C, ℓ∤V, vℓ(M)=vℓ(C))
```

となる。exclusive ownership は M*N=V*C と Coprime M N だけでは導けない。generic arithmetic countermodel M=4,N=1,V=C=2 はその2条件を満たすが V,C は同じ prime2を含む。この model は actual source packet の反例ではない。今回の exclusivity は canonical source coprimality を実際に使っている。

## 数学的な新情報の厳密な評価

付値和の equality は元の積等式と Coprime M N の直接の帰結であり、独立した新しい source invariant ではない。既存 support disjunction に対しては multiplicity を保持するので API の結論はより詳細だが、元の ledger を超える制約を発見したとは言えない。

exclusive valuation は開始時の2条件だけより強い。しかし追加情報は今回新発見の source law ではなく、以前から証明されていた canonical coprimality に含まれる。今回の寄与は同じ p 上の外側 root の coprimality と exact prime multiplicity の readout を明示・検証したこと。これを M の新しい上限、許される素数の分類、FLT7 reconstruction の存在への進展と数えない。

## 検証結果と次の判断

calibration 初回は source alias K の形の違いにより simp が零付値を消去できず exit 1。hval の型を change で K の形に揃え、修正後 exit 0。production focused build は exit 0（9087 jobs）。最初の test は未存在の Nat.mul_pos_iff を使って exit 1、積非零からの各因子非零へ修正して最終 test exit 0。命題の仮定は変更していない。

3公開定理と generic countermodel の公理監査は propext、Classical.choice、Quot.sound のみ、sorryAx なし。source positivity、factorization specialization、exclusive branch、旧 support の回復、零の付値規約を Lean で検証した。

M を c*ℓ^n、c≤343 とする factorization/小係数 bound は得られていない。Q、real-pair load、stripped root と chart center の一致もない。N は chart complement M/r ではない。今回 additive chart existence や新 modulus を探索していない。

追加の source-intrinsic inequality を支持する新証拠は得ていないため、未証明の研究仮説を新 API にしない。次段階は、この派生 ledger をさらに包むより、独立した source 制約を供給できる戦略かを再評価するべきである。[source-valuation-frontier-018.md](source-valuation-frontier-018.md) に限界を記録し、018 で終了する。
