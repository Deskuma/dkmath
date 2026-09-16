# ABC Eisenstein square-factor provider — report-001

## 1. 結論

**Outcome A — FACTORIZATION PROVIDER PRODUCTION-PROVED**。

現在の branch では、実現 shell witness `a` ごとに、既存の cubic coordinate

```lean
alpha := eisensteinCoord ((a : ℤ) + 2) 1
M := GNExcessCubicFullRepeatedModulus a
S := GNExcessCubicComplement a
```

について、kernel が検査した production theorem
`GNExcessCubicRealizedLargeModulusShellWitness_exists_eisenstein_square_factor`
が次を返す。

```lean
∃ beta gamma : TraceOneInt (-1),
  (norm beta).natAbs = oddPart M * S ∧
  (norm gamma).natAbs = evenPart M ∧
  alpha = beta * gamma ^ 2
```

これは literal な `gamma = 1` の存在ではなく、shell の平方部分を指定した provider である。

## 2. 対象 branch と回収資料

- repository: `Deskuma/dkmath`
- branch: `research/ABC-Eisenstein-landing-provider-260915-v0`
- HEAD at audit start: `56461094729fe71b425c17cf9e1e327bbed56e7a`
- Lean cwd: `lean/dk_math`
- toolchain: `leanprover/lean4:v4.32.2`
- 指示書の base commit `7ee9d183...` は現在の HEAD と異なるため、現ソースと現 build を優先した。

永続資料の回収結果は [memory-recovery-001.md](memory-recovery-001.md) に記録した。確認したものは、global `AGENT.md`、`/home/deskuma/.codex/memories/MEMORY.md`、LUNA-008 と FLT3 EuclideanDomain の rollout summary 2 件、直前 run の `notes/Agent-note-260915-100209.md`、および current handoff artifacts である。追加の workspace `MEMORY.md` / `SUMMARY.md` / `AGENTS.md` は無かった。指定語で検索した範囲に、current artifacts を超える provider theorem、別 API、成功 build、warning 修正は無く、`NO ADDITIONAL RELEVANT MEMORY FOUND` とした。

## 3. scratch replay

すべて current checkout の `lake env lean` で再実行した。

| file | result | load-bearing axiom audit |
|---|---|---|
| `scratch/UFDProvider.lean` | exit 0 | `exists_squarefree_mul_sq`, `squarefree_norm_of_dvd_cubicCoord`, `exists_cubicCoord_squarefree_norm_mul_sq`, `exists_cubicCoord_nat_squarefree_norm_mul_sq` は `[propext, Classical.choice, Quot.sound]` のみ |
| `scratch/ShellAllocation.lean` | exit 0 | 自然数の平方自由×平方の一意性、および shell allocation は `[propext, Classical.choice, Quot.sound]` のみ |
| `scratch/IdealDescent.lean` | exit 0 | principal-ideal descent は `[propext, Classical.choice, Quot.sound]` のみ。`#synth` は EuclideanDomain → PID → UFD と IsDedekindDomain を確認 |
| `scratch/LandingExamples.lean` | exit 0 | 例・反例 theorem は基礎公理のみ（`unrestricted_factorization` は `[propext]`） |
| `scratch/Diagnostics.py` | exit 0 | 出力を `Diagnostics-results.json` と `cmp` し exact match |

Diagnostics の deterministic scan は `0 ≤ a ≤ 2000` の 2001 値で、prescribed norm factorization failures `0`、local channel violations `0`、identical full norm pairs `0`、landing histogram は全値 `6`。これは regression evidence であり、定理の代用ではない。

## 4. production 追加

### neutral Lib layer

[SquarefreePowerFactor.lean](../../../DkMath/Lib/NumberTheory/SquarefreePowerFactor.lean) に次を追加した。

```lean
exists_squarefree_mul_sq
  {R} [CommMonoidWithZero R] [WfDvdMonoid R] (a : R) (ha : a ≠ 0) :
  ∃ b c, Squarefree b ∧ a = b * c ^ 2
```

これは `wellFounded_dvdNotUnit` による terminating extraction で、ABC 固有の仮定を持たない。`DkMath.Lib.lean` から export した。

### ABC provider

[GNExcessCubicEisensteinSquareFactorProvider.lean](../../../DkMath/ABC/GNExcessCubicEisensteinSquareFactorProvider.lean) に追加した theorem は次の通り。

1. `squarefree_conj`
2. `scalar_dvd_of_square_dvd_norm`
3. `squarefree_norm_of_dvd_cubicCoord`
4. `exists_cubicCoord_squarefree_norm_mul_sq`
5. `exists_cubicCoord_nat_squarefree_norm_mul_sq`
6. `nat_squarefree_square_decomposition_unique`
7. `shell_squarefree_norm_allocation`
8. `GNExcessCubicRealizedLargeModulusShellWitness_exists_eisenstein_square_factor`

`DkMath.ABC.lean` に provider import を追加し、従来の conditional receiver
`GNExcessCubicEisensteinFactorConsequences` はそのまま残した。receiver の低レベル契約を壊さず、provider-backed theorem を別の公開入口にした。

## 5. load-bearing proof の監査

`alpha = beta * gamma^2` から `beta ∣ alpha` は、生成された equality の向きに対して `⟨gamma^2, hfac⟩` で得られる。

`Squarefree beta` から `Squarefree (conj beta)` を、`conj` の involution と multiplicativity で直接示す。整数 `t` が `t*t ∣ norm beta` なら、整数を `TraceOneInt (-1)` に cast して

```text
t*t ∣ conj(beta) * beta
```

にする。Mathlib `Squarefree.dvd_of_squarefree_of_mul_dvd_mul_right` を `Squarefree (conj beta)` に正しい向きで適用し、scalar `t ∣ beta` を得る。さらに `beta ∣ alpha` と積の second coordinate を取ると

```text
-(1 : ℤ) = t * k.snd
```

であり、`t ∣ -1`、したがって `t` は unit である。よって `Squarefree (norm beta)` が成立する。この係数 1 の議論が、一般の「norm divisibility は element divisibility を含意しない」という障壁を cubic coefficient-one family で解消する核心である。

座標符号は Lib の標準 omega 座標 `eisensteinCoord m n = ⟨m,-n⟩` と一致し、norm は `m^2 - m*n + n^2`。cast は `Int.cast_mul`、共役積は既存 `traceOne_mul_conj` を使用する。`beta = 0` は squarefree の `ne_zero`、`gamma = 0` は正の cubic norm equality により排除される。

## 6. shell allocation と依存グラフ

既存 shell packet から

```text
M = oddPart(M) * evenPart(M)^2
Squarefree (oddPart(M) * S)
M*S = a^2 + 3*a + 3
```

を得る。provider の natural norm identity は

```text
a^2 + 3*a + 3 = natAbs(norm beta) * natAbs(norm gamma)^2
Squarefree (natAbs(norm beta))
```

である。Mathlib の `Nat.factorization_mul`、`Nat.factorization_pow`、
`Squarefree.natFactorization_le_one`、`Nat.eq_of_factorization_eq` による一意性から、

```text
natAbs(norm beta)  = oddPart(M) * S
natAbs(norm gamma) = evenPart(M)
```

となる。

依存グラフは次の通り。

```text
TraceOneInt (-1) EuclideanDomain
  -> WfDvdMonoid
  -> Lib.exists_squarefree_mul_sq
  -> beta * gamma^2 = alpha, Squarefree beta
  -> conjugation + Squarefree.dvd_of_squarefree_of_mul_dvd_mul_right
  -> Squarefree (norm beta)
  -> natAbs norm identity
  -> shell_squarefree_norm_allocation
  -> prescribed shell provider
```

`TraceOneInt (-1)` の EuclideanDomain は既存 [EisensteinEuclidean.lean](../../../DkMath/FLT/Three/EisensteinEuclidean.lean) から再利用した。production provider はこの既存 implementation を import する。

## 7. 素数チャネルと adversarial tests

既存 ABC facts は、`M` の prime divisor が `q % 3 = 1`、`3` の norm valuation が 0 または 1、complement は squarefree で `9 ∤` であることを与える。したがって inert primes はこの cubic norm に現れない。ただし provider の証明自体は、prime-by-prime orientation や CRT を仮定せず、actual element の squarefree extraction と coefficient-one argument で orientation を内部的に選ぶ。

数値例:

- `a=17`: `N(alpha)=343=7^3`, `M=343`, しかし `N(gamma)=7`, `N(beta)=7`。したがって `M=N(gamma)^2` は誤り。
- `a=21`: `N(alpha)=507=3*13^2`, `N(beta)=3`, `N(gamma)=13`。ramified residual は beta 側に残る。
- `N(beta) ∣ N(alpha) -> beta ∣ alpha` は既存 landing counterexample で偽。
- `N(alpha)=49` の一般要素についても、norm-squareful だけでは matching nonunit element square divisor を保証しない。
- cubic family は `cubicQuadratic_injective` と `GNExcessCubicIncidencePair_injective` を持つため、異なる natural shell witness の同一 exact norm / `(M,S)` pair counterexample は存在しない。

## 8. ideal / principalization の位置づけ

`IdealDescent.lean` は、principal ideal factorization が既に与えられる場合、`TraceOneInt (-1)` の PID で generators を選び、association の unit を free residual beta に吸収できることを kernel-check した。従って class-group torsion-free、principalization theorem、unit-sector surjectivity は今回の provider には不要である。

これは arbitrary `TraceOneInt s` に自動一般化されない。今回不要なのは exact carrier `TraceOneInt (-1)` の既存 EuclideanDomain と、element-level extraction の組合せによる。ideal route は有効な fallback だが、primary production route ではない。

## 9. production validation

以下はすべて exit 0。

```text
lake env lean docs/dev/ABC-Eisenstein-landing-provider-260915/scratch/UFDProvider.lean
lake env lean docs/dev/ABC-Eisenstein-landing-provider-260915/scratch/ShellAllocation.lean
lake env lean docs/dev/ABC-Eisenstein-landing-provider-260915/scratch/IdealDescent.lean
lake env lean docs/dev/ABC-Eisenstein-landing-provider-260915/scratch/LandingExamples.lean
lake build DkMath.Lib.NumberTheory.SquarefreePowerFactor
lake build DkMath.ABC.GNExcessCubicEisensteinSquareFactorProvider
lake build DkMath.ABC
lake build DkMath.Lib
lake build DkMath.Lib.NumberTheory.EisensteinLatticeLanding
lake build DkMath.Lib.NumberTheory.TraceOnePowerLanding
lake build DkMath.FLT.Three.EisensteinEuclidean
lake build DkMath.FLT.Three
python3 docs/dev/ABC-Eisenstein-landing-provider-260915/scratch/Diagnostics.py
cmp -s /tmp/abc_diagnostics_001.json docs/dev/ABC-Eisenstein-landing-provider-260915/scratch/Diagnostics-results.json
git diff --check
```

新規 load-bearing production theorem の build 出力:

```text
'DkMath.ABC.GNExcessCubicRealizedLargeModulusShellWitness_exists_eisenstein_square_factor'
depends on axioms: [propext, Classical.choice, Quot.sound]
```

変更した production Lean (`SquarefreePowerFactor.lean`, provider、`DkMath.Lib.lean`, `DkMath.ABC.lean`) に `sorry`, `admit`, project `axiom`, `abc_main_axiom`, `native_decide`, `unsafe` は無い。`git diff --check` も成功した。full `DkMath.ABC` / FLT3 logs に既存 `DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:147` の `sorry` warning が再表示されたが、新規変更由来ではない。これは既存 workspace warning として区別する。

## 10. 残る ABC frontier

この checkpoint は Eisenstein square-factor provider を閉じるだけであり、ABC conjecture の証明ではない。残るものは、factor counting / balanced-box sparsity、Mordell / integral-point counting、near-linear shell count、最終的な global ABC closure である。これらには進まず、指示書の stop condition で停止する。
