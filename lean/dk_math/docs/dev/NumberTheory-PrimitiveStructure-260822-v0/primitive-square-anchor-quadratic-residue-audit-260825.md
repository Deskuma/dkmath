# PRIM-QR-000 Square-anchor quadratic-residue constraint audit

日付: 2026-08-25
対象: `instruction-037.md`
対象ブランチ: `wip/number-theory-primitive-structure-260822-v2`
対象 toolchain: Lean / Mathlib v4.32.2

## 0. Executive outcome

この checkpoint は read-only mathematical/API reconnaissance である。Lean source、
theorem statement、docstring、import、依存関係、facade、frontier、既存 audit report
は変更しない。

最終分類は **Outcome C — WEAKER PROJECTION / REDUNDANT** とする。

既存 DkMath の正確な forbidden-wave 条件

```text
q ∣ n²+r
  ↔ r % q = squareAnchorForbiddenResidue n q
```

から、奇素数 `q` について

```text
-r is a nonzero square modulo q
```

および Legendre symbol の条件

```text
(r / q) = (-1 / q)
```

は得られる。しかしこれは exact な一剰余類を quadratic-character class に射影した
だけである。`q>3` では一つの exact wave が概ね `(q-1)/2` 個の非零 character-compatible
residue に拡大されるため、full-cover obstruction は弱くなる。

平方 anchor に固有の意味はあるが、二次指標から

```text
SquareOffsetsFullyCovered n → NEW_CONSTRAINT(n)
```

という既存 exact wave より強い aggregate inequality、branch exclusion、count deficit、
または contradiction/provider は得られなかった。従ってこの route は停止する。

## 1. Repository-derived theorem inventory

### 1.1 Exact forbidden wave

`DkMath.NumberTheory.Legendre.Basic` の主要 API は次の通り。

```lean
SquareOffsetForbiddenBy n q r := q ∣ n ^ 2 + r
squareAnchorForbiddenResidue n q := (q - (n ^ 2 % q)) % q

squareOffsetForbiddenBy_iff_mod_eq_forbiddenResidue
```

`q>0` のもとで最後の theorem は

```text
SquareOffsetForbiddenBy n q r
  ↔ r % q = squareAnchorForbiddenResidue n q
```

を与える。これは `q` が shell の offset に対して作る **一つの exact residue wave**
であり、二次指標より情報量が多い。

### 1.2 Coprime offsets と nondivisor support

`DkMath.NumberTheory.Legendre.CoprimePacket` には次がある。

```lean
squareAnchorCoprimeOffsets
mem_squareAnchorCoprimeOffsets
squareAnchorCoprimeBaseOffsets
squareAnchorCoprimeOffsets_eq_base_union_shift
card_squareAnchorCoprimeOffsets

squareAnchorDivisorPrimes
squareAnchorNondivisorPrimes
mem_squareAnchorNondivisorPrimes

squareOffsetAnchorNondivisorSupport
mem_squareOffsetAnchorNondivisorSupport
squareOffsetPrimeSupport_eq_anchorNondivisorSupport_of_coprime
squareOffsetCovered_iff_anchorNondivisor_of_coprime
```

特に、

```text
r ∈ squareAnchorCoprimeOffsets n
  ↔ SquareOffset n r ∧ Nat.Coprime n r
```

であり、coprime seat の old support は

```text
q ∈ squareOffsetAnchorNondivisorSupport n r
  ↔ Nat.Prime q ∧ q ≤ n ∧ ¬ q ∣ n ∧ q ∣ n²+r
```

で正確に記述される。これは「選択された q がどの offset を覆うか」を既に完全に
記録している。

### 1.3 Wave、overlap、packet、small-cofactor

確認した既存層は次の通り。

- `Legendre.Wave`: `squareWaveOffsets`、`mem_squareWaveOffsets`、occupancy、
  `squareWaveCarry`、wave の exact count。
- `Legendre.PairOverlap`: support pair、overlap cardinality、product phase。
- `Legendre.CoprimePacket`: anchor-divisor / anchor-nondivisor partition、
  coprime offset、base/shift packet。
- `Legendre.PacketCross`: packet cross pair、near/far geometry、pair-count ledger。
- `Legendre.PacketCoprimality`: `coprime_squarePacketPoints_of_mem_base`、
  cross-side coprimality。
- `Legendre.PacketUnitResidue`: `squarePacket_left_modEq_base`、
  `squarePacket_right_modEq_base`、`packetCross_factor_products_modEq`、
  `packetCross_factor_determinant_eq_anchor`。
- `Legendre.SmallCofactor`: old-generated / unique-fresh split、small cofactor、
  selected support、C002/L022 branch information。
- `Legendre.Frontier`: full-cover、support escape、Legendre frontier equivalences。

これらの exact residue、support、packet、cofactor API に quadratic-character の
抽象は現時点で追加されていない。

## 2. Mathlib v4.32.2 quadratic-residue API inventory

これは pinned checkout `.lake/packages/mathlib` の repository fact であり、現行
DkMath の import surface とは区別する。

### 2.1 Square semantics and Legendre symbol

`Mathlib.NumberTheory.LegendreSymbol.Basic` に次がある。

```lean
ZMod.euler_criterion
legendreSym
legendreSym.eq_one_iff
legendreSym.eq_one_iff'
legendreSym.eq_neg_one_iff
legendreSym.eq_neg_one_iff'
legendreSym.at_neg_one
legendreSym.at_neg
ZMod.exists_sq_eq_neg_one_iff
```

`legendreSym p a` は `(a / p)` の順序であり、`legendreSym.eq_one_iff'` は `a : ℕ`
について非零仮定のもとで

```text
legendreSym p a = 1 ↔ IsSquare (a : ZMod p)
```

を与える。`ZMod.exists_sq_eq_neg_one_iff` は

```text
IsSquare (-1 : ZMod p) ↔ p % 4 ≠ 3
```

である。

### 2.2 Reciprocity

`Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity` に次がある。

```lean
legendreSym.quadratic_reciprocity
legendreSym.quadratic_reciprocity'
legendreSym.quadratic_reciprocity_one_mod_four
legendreSym.quadratic_reciprocity_three_mod_four
ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one
ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three
```

奇素数に対して `legendreSym.quadratic_reciprocity'` は

```text
(q / p) = (-1)^((p/2)*(q/2)) * (p / q)
```

という Mathlib の自然数 floor-division 表現を使う。これは `p,q` の奇偶性・相異性の
仮定を明示しており、`q=2` に無条件で適用できない。

### 2.3 Current import boundary

現行の `DkMath.NumberTheory.Legendre.Basic` は `Mathlib.Data.Nat.ModEq` などを import
しているが、`Mathlib.NumberTheory.LegendreSymbol.Basic` や
`QuadraticReciprocity` を import していない。instruction-037 は import と依存関係の
変更を禁止しているため、これらを DkMath に接続する実装は行わない。

Mathlib には別途 `Mathlib.NumberTheory.Primorial` の `primorial`、
`primorial_eq_prod_primesLE` も存在するが、この checkpoint の quadratic-residue
判定には不要であり、DkMath 側への新しい wrapper は追加しない。

## 3. Q1: exact local square witness

仮定を

```text
Nat.Prime q
q ≤ n
¬ q ∣ n
q ∣ n²+r
```

とする。このとき既存 DkMath/Mathlib の最小 chain は次である。

1. `SquareOffsetForbiddenBy n q r` は `q ∣ n²+r` の定義展開。
2. `Nat.dvd_iff_mod_eq_zero`、`Nat.add_mod`、または
   `squareOffsetForbiddenBy_iff_mod_eq_forbiddenResidue` により
   `n²+r ≡ 0 [MOD q]` を読む。
3. `ZMod.intCast_zmod_eq_zero_iff_dvd` を使って `ZMod q` へ移す。
4. 可換環計算により

   ```text
   (-r : ZMod q) = (n : ZMod q)^2.
   ```

5. `¬q∣n` から `(n : ZMod q) ≠ 0`、従って `(-r : ZMod q) ≠ 0` を得る。

最後の `¬q∣r` は別途 thin composition である。もし `q∣r` なら、`q∣n²+r` と
`q∣r` から `q∣n²`、`Nat.Prime.dvd_of_dvd_pow` から `q∣n` となり矛盾する。

既存 DkMath には `squareAnchorForbiddenResidue_ne_zero_of_prime_not_dvd_anchor` があり、
forbidden phase が零でないことは直接得られるが、`¬q∣r` としての必要条件は上記の
短い composition である。

### Q1 の分類

**B. thin rewrite/composition only**。

square witness の数学的内容は既存の divisibility、modulus、`ZMod` square semantics
で閉じている。しかし、現行 DkMath にこの全 chain を一つの公開 theorem として束ねた
ものはなく、今回それを追加する必要もない。

### q=2 の分離

`q=2` では `¬2∣n` から `n` は奇数、`2∣n²+r` から `r` は奇数である。`ZMod 2` では
唯一の非零元が平方なので `-r` が square になるという意味は残るが、odd-prime の
Legendre symbol、`q % 4 = 1/3` 分類、quadratic reciprocity は適用しない。

以後の character / mod-4 statements は必ず `q` odd を仮定する。

## 4. Q2: character form versus exact forbidden residue

`q` を奇素数とし、Q1 の仮定を置く。`r` の非零性 modulo `q` と
`(-r : ZMod q) = (n : ZMod q)^2` から

```text
(-r / q) = 1.
```

Mathlib の `legendreSym.at_neg` と `legendreSym.sq_one'` を使うと、

```text
(r / q) = (-1 / q).
```

が得られる。さらに `legendreSym.at_neg_one` と `χ₄` の mod-4 API により、

```text
q ≡ 1 (mod 4) → (r / q) = 1
q ≡ 3 (mod 4) → (r / q) = -1.
```

`q∤r` が必要なのは、`(r/q)=0` の退化を除くためである。

したがって、奇素数 witness に対する character form は

```text
q ≡ 1 (mod 4) → r is a nonzero square mod q
q ≡ 3 (mod 4) → r is a nonzero nonsquare mod q.
```

である。

### Information comparison

| 条件 | offset residue に対する情報量 |
|---|---|
| `q ∣ n²+r` | `r % q = squareAnchorForbiddenResidue n q`。一つの exact residue class |
| `-r is a nonzero square mod q` | `r` が `-(nonzero square)` の集合に入る。通常 `(q-1)/2` classes |
| `(r/q)=(-1/q)` | 上記 character class の符号表示 |

従って

```text
exact forbidden residue ⇒ quadratic-character condition
```

であり、逆は一般に成立しない。`q=3` では非零 character class が一元になるため
偶然同じ情報量になる場合があるが、`q>3` の一般的な exact wave には当てはまらない。

### Q2 の分類

**B. thin rewrite/composition only** だが、full-cover 用の情報としては exact residue
より弱い projection である。新しい独立 coordinate ではない。

## 5. Q3: full-cover quadratic witness condition

report-local に

```text
QuadraticFullCoverWitness n :=
  ∀ r ∈ squareAnchorCoprimeOffsets n,
    ∃ q,
      q ∈ squareAnchorNondivisorPrimes n ∧
      q ∣ n²+r ∧
      q is odd → -r is a nonzero square mod q.
```

と書く。正確には odd 条件を witness の外側に出して、`q=2` を別 branch として扱う。

`SquareOffsetsFullyCovered n` と
`squareOffsetCovered_iff_anchorNondivisor_of_coprime` から、各
`r ∈ squareAnchorCoprimeOffsets n` に対して old nondivisor witness `q` が存在する。
Q1 により、その witness は quadratic condition を満たす。

しかしこの condition は candidate witness を一つも削除しない。既存 exact support の
各 member はすでに `q∣n²+r` を満たしており、そこから character condition が従うだけ
である。character-compatible q を用いて exact divisibility を置き換えるなら、むしろ
各 q が担当できる offset 集合を拡大する。

### Q3 の判定

これは full cover の必要条件ではあるが、既存 exact support の **weaker projection**。
aggregate count、incompatibility、または full-cover exclusion は得られない。

## 6. Q4: special offsets

### 6.1 `r=1`

`n>0` なら `1 ∈ squareAnchorCoprimeOffsets n` である。奇素数 `q` が

```text
q ∣ n²+1,
¬q∣n
```

を満たすなら `-1` が `ZMod q` の非零 square となる。Mathlib の
`ZMod.exists_sq_eq_neg_one_iff` と odd prime の mod-4 分割から

```text
q ≡ 1 (mod 4)
```

が従う。

ただし `n` が奇数なら `q=2` が `n²+1` を割ることがあり、odd witness だけを見て
全ての witness を `1 mod 4` としてはならない。また、この事実は `n²+1` が prime
であることを意味しない。

### 6.2 `r=n-1` と `r=n+1`

`n≥2` なら `r=n-1` は canonical range にあり、`Nat.Coprime n (n-1)` である。
`n≥1` なら `r=n+1` も canonical range にあり、`Nat.Coprime n (n+1)` である。

それぞれの odd witness は

```text
q ∣ n²+n-1 → -(n-1) is a square mod q,
q ∣ n²+n+1 → -(n+1) is a square mod q.
```

を満たすが、`r=1` の `-1` のような fixed residue の mod-4 obstruction はない。
packet companion の `n+r` としては既存の base/shift geometry に含まれる。

### 6.3 small prime offsets

`r=ℓ` が odd prime で、`ℓ` が canonical range にあり、odd witness `q` が
`q∣n²+ℓ` を満たす場合、`q=ℓ` は不可能である。実際、`q=ℓ` なら
`q∣n²+q` から `q∣n²`、従って `q∣n` となり、nondivisor 条件に反する。

よってこの場合は Q5 の quadratic reciprocity を適用できる。ただしそれは一つの
offset に対する witness restriction であり、全 shell を覆う際の不足数を直ちに与えない。

### Q4 の判定

`r=1` には `q mod 4` の明確な local fact がある。他の special offsets も exact
square witness を持つ。しかし、どれも一 seat の条件を越えて full-cover obstruction
にはなっていない。

## 7. Q5: quadratic reciprocity and direction reversal

`r=ℓ` を odd prime、`q` を odd witness prime とする。Q4 の `q≠ℓ` と

```text
(ℓ / q) = (-1 / q) = (-1)^((q-1)/2)
```

を `legendreSym.quadratic_reciprocity'` に入れると、

```text
(q / ℓ)
  = (-1)^(((q-1)/2) * ((ℓ+1)/2))
```

という同値な符号表示を得る。従って、例えば

```text
ℓ ≡ 3 (mod 4) → (q / ℓ) = 1,
ℓ ≡ 1 (mod 4) → (q / ℓ) = (-1 / q).
```

ここでも `q=2`、`ℓ=2` は別扱いであり、上式を適用しない。

この reciprocity は、固定した prime offset `ℓ` に対し witness primes `q` の
quadratic-character を `mod ℓ` で制限する。しかし、それは依然として **per-seat** の
条件である。

- 異なる offsets `ℓ₁,ℓ₂` の witness primes を同じ residue class に強制しない。
- 同じ offset の複数 witness primes の間に incompatibility を与えない。
- `q≤n` の prime count を評価する theorem がない。
- Dirichlet、PNT in progressions、Burgess、GRH などの外部 distribution provider は
  instruction-037 の範囲外である。

### Q5 の判定

Quadratic reciprocity は exact wave の別表示を作るが、witness primes / offsets を
結合する新しい finite constraint にはならない。**weaker per-seat projection** である。

## 8. Q6: packet geometry

coprime packet の base `r` と companion `n+r` について、full cover から選んだ old
nondivisor primes `p,q` は

```text
p ∣ n²+r,
q ∣ n²+(n+r).
```

を満たす。odd primes なら quadratic form はそれぞれ

```text
(-r / p) = 1,
(-(n+r) / q) = 1.
```

となる。

既存 packet API は既に次を与える。

```lean
coprime_squarePacketPoints_of_mem_base
not_prime_dvd_both_squarePacketPoints
packetCross_factor_products_modEq
packetCross_factor_determinant_eq_anchor
packetCross_factor_determinant_sub_eq_anchor
packetCross_all_factors_coprime_anchor
```

従って、`p=q` の禁止は quadratic character ではなく、既存の packet coprimality から
得られる。`p*a+n=q*b` と `p*a` / `q*b` の mod-`n` 関係も既に exact であり、二次
指標はそれを強化しない。

確認結果は次の通り。

| 候補する packet 帰結 | quadratic condition の効果 |
|---|---|
| `p ≠ q` | 既存 `not_prime_dvd_both_squarePacketPoints` が既に供給 |
| `p/q mod 4` の不可能 pattern | 一般には導けない |
| simultaneous character contradiction | なし。左右は別 offset/別 modulus |
| new pair-count deficit | なし。exact pair/overlap ledger が強い |
| determinant `q*b-p*a=n` | 既存 `packetCross_factor_determinant_eq_anchor` が exact |

### Q6 の判定

packet geometry には新しい quadratic leverage はない。quadratic conditions は既存の
left/right divisibility を各 seat で再表示するだけである。

## 9. Q7: old/fresh と small-cofactor

`SmallCofactor` の full-cover normal form は、coprime seat に対して

```text
old-generated
or unique fresh prime ℓ > n with 2 ≤ k ≤ n,
   ℓ*k = n²+r,
   k ∈ squareAnchorCoprimeBaseOffsets n.
```

を記録する。

quadratic condition が見るのは、選択された old witness `p` の
`p∣n²+r` だけである。従って、

- old-generated branch でも同じ条件が成立する。
- unique-fresh branch でも old selected support prime について同じ条件が成立する。
- fresh prime `ℓ` の `ℓ>n`、small cofactor `k`、`FreshPrimeDirection` の情報は
  quadratic character から読めない。
- `k=p` の singleton/depth-one criterion や `2≤k` の branch obstruction は強化されない。

特に、二次剰余条件から `FreshPrimeDirection` を推論することはできない。quadratic
condition は branch split の前後で不変な selected-old-prime decoration に留まる。

### Q7 の判定

old/fresh や C002/L022 branch を区別する新しい情報は得られない。**branch-neutral
projection** である。

## 10. Q8: finite counting leverage

### 10.1 One fixed odd wave

`q` を odd prime とする。exact DkMath wave は

```text
r % q = squareAnchorForbiddenResidue n q
```

という一つの residue class だけを許す。対して

```text
-r is a nonzero square mod q
```

は非零 square の負集合であり、`(q-1)/2` 個の residue classes を許す。

したがって、`q>3` では

```text
exact wave seats ⊆ character-compatible seats
```

であり、後者の seat count は大きい。二次指標で exact wave を置き換えた union は、
old-prime cover をより容易にするため、non-cover contradiction の方向には働かない。

### 10.2 Interval count and character sums

`1..2n` の有限 interval で character-compatible classes を数えることはできるが、
それは exact class の count より粗い上界になる。character sum identity を使って
exact class を再構成するなら、必要な additive phase 情報を再導入することになり、
既存の `squareAnchorForbiddenResidue` / `squareWaveOffsets` に戻る。

従って、analytic distribution hypothesis なしに得られる finite count は、既存の

```text
wave occupancy
pair overlap
localized obstruction ledger
packet cross count
```

を上回らない。`card_squareAnchorCoprimeOffsets` や full-cover incidence inequality
も、既に exact support を使っているため、character projection で改善されない。

### Q8 の判定

二次 character projection は exact wave の witness set を拡大する。union bound、
finite character count、pair count のいずれも strict deficit を生まない。
**Counting leverage は negative** である。

## 11. Q9: exact hard-frontier implication test

full cover から report-local に得られる最も強い quadratic statement は、

```text
SquareOffsetsFullyCovered n
  → ∀ r ∈ squareAnchorCoprimeOffsets n,
      ∃ q ≤ n, q prime, ¬q∣n, q∣n²+r,
        (q=2 or ((r/q)=(-1/q))).
```

である。これは exact support condition の projection であり、次のいずれにも進まない。

```text
SquareOffsetsFullyCovered n → new aggregate inequality
SquareOffsetsFullyCovered n → branch exclusion
SquareOffsetsFullyCovered n → pair-count deficit
SquareOffsetsFullyCovered n → contradiction
```

情報の階層は明確である。

```text
exact forbidden residue
  ⇒ exact support / wave cover
  ⇒ quadratic-character compatibility
```

矢印を逆にする theorem はなく、右端から左端へ戻すには失われた residue phase を
再び仮定する必要がある。

従って、square-specific という語は observation の意味では正しいが、既存 frontier
を狭める independent provider という意味では不十分である。

## 12. Final classification and recommendation

### Final classification

**Outcome C — WEAKER PROJECTION / REDUNDANT**

理由:

1. `q∣n²+r → -r is a square mod q` は既存 exact wave からの thin composition。
2. `(r/q)=(-1/q)` と reciprocity は exact residue class を character class に射影する。
3. q=2 を除く odd-prime facts は局所的であり、packet、old/fresh、small-cofactor の
   unresolved branch を結合しない。
4. character-compatible seat set は exact wave seat set より大きく、finite cover count
   を弱める。
5. full cover から exact wave より強い `NEW_CONSTRAINT(n)` は得られない。

### Recommendation

この route は停止する。quadratic-residue wrapper、Legendre/Jacobi symbol abstraction、
`ZMod` import、quadratic reciprocity dependency を DkMath Primitive/Legendre に追加しない。

将来再開するには、単なる character restatement ではなく、次のいずれかを先に提示する
必要がある。

```text
1. 複数 offset / 複数 witness prime を同時に結ぶ exact finite incompatibility;
2. character-compatible union に対する独立の strict count deficit;
3. old/fresh または packet branch を実際に除外する theorem.
```

これらがない限り、現在の `squareAnchorForbiddenResidue`、wave、overlap、packet、
small-cofactor の exact API が優先される。

## 13. Explicit boundary and no implementation

instruction-037 に従い、次を変更していない。

- Lean source、theorem statement、Lean docstring、module documentation
- import、facade、dependency revision、Lake configuration、`lean-toolchain`
- PRIM-C001/C002、PRIM-L022、Legendre facade/frontier
- previous audit reports
- `ZMod` infrastructure、Legendre/Jacobi symbol wrapper、quadratic reciprocity dependency
- analytic prime-distribution assumptions、GRH/RH/CFBRC provider

成果物は本 report 一つだけであり、PRIM-QR-001 は開始しない。

## 14. Main declarations checked

```text
DkMath.NumberTheory.Legendre.SquareOffsetForbiddenBy
DkMath.NumberTheory.Legendre.squareAnchorForbiddenResidue
DkMath.NumberTheory.Legendre.squareOffsetForbiddenBy_iff_mod_eq_forbiddenResidue
DkMath.NumberTheory.Legendre.squareAnchorCoprimeOffsets
DkMath.NumberTheory.Legendre.squareOffsetAnchorNondivisorSupport
DkMath.NumberTheory.Legendre.mem_squareOffsetAnchorNondivisorSupport
DkMath.NumberTheory.Legendre.squareOffsetCovered_iff_anchorNondivisor_of_coprime
DkMath.NumberTheory.Legendre.squareOffsetPrimeSupport_eq_anchorNondivisorSupport_of_coprime
DkMath.NumberTheory.Legendre.coprime_squarePacketPoints_of_mem_base
DkMath.NumberTheory.Legendre.packetCross_factor_products_modEq
DkMath.NumberTheory.Legendre.packetCross_factor_determinant_eq_anchor
DkMath.NumberTheory.Legendre.oldGenerated_or_uniqueFresh_nontrivialSmall_of_fullyCovered

ZMod.euler_criterion
legendreSym.eq_one_iff'
legendreSym.eq_neg_one_iff'
legendreSym.at_neg_one
legendreSym.at_neg
ZMod.exists_sq_eq_neg_one_iff
legendreSym.quadratic_reciprocity'
ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one
ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three
```
