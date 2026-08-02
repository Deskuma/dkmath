# RH-WEAVE-001

**RH-WEAVE-001 — PHZ・位相ジャンプ・CFBRC を織り合わせる Lean 形式化計画**

作成日: 2026-08-02  
対象: DkMath / Lean 4 / Mathlib v4.32.2 系  
状態: 設計草案。GitHub 未反映。

---

**0. 文書の目的**

過去の `riemann-hypothesis-ai` プロジェクト、現在の DkMath RH 実装、有限 Euler 積・位相ジャンプ・素数対数微分・螺旋可視化から得た断片を、一つの Lean 形式化路線へ組み直す。

本計画では、証明を一本の巨大な鎖として最初から作らない。

経糸と緯糸を独立に張り、両者を接続する補題だけを明示的な Bridge として実装する。

経糸は次である。

- 標準ゼータ関数
- 解析接続された零点の意味
- 位相・対数微分
- argument principle
- 極限と正則化

緯糸は次である。

- 有限 Dirichlet ベクトル
- 有限 Euler 積
- $\Lambda(n)$ による素数位相和
- PHZ 候補高度
- CFBRC 欠陥量
- 有限和の対称性と保存則

両者を通す杼は次である。

- eta 表現
- 平滑打切り
- Abel 型極限
- 明示公式
- zero-box と winding number
- CFBRC semantic bridge

---

**1. 最終目標**

最終定理は、単に RH を別名で定義して証明するものではない。

必要な構造は次である。

$$
\operatorname{PrimePhaseState}(\sigma,t)
\Longrightarrow
\operatorname{CFBRCDefect}(d,\sigma,\Theta)=0
$$

既存または将来の CFBRC 排除定理により、

$$
\operatorname{CFBRCDefect}(d,\sigma,\Theta)=0
\Longrightarrow
\sigma=\frac12
$$

さらに、標準ゼータ零点から独立な素数側状態を構成し、

$$
\operatorname{StandardZetaZero}(\sigma,t)
\Longrightarrow
\operatorname{PrimePhaseState}(\sigma,t)
$$

を得る。

この三本を合成して、

$$
\operatorname{StandardZetaZero}(\sigma,t)
\Longrightarrow
\sigma=\frac12
$$

へ到達する。

最終成果物では、次の循環を絶対に許さない。

- `PrimePhaseState` の定義に標準ゼータ零点を含める。
- `CFBRCDefect = 0` の定義に $\sigma=1/2$ を含める。
- Bridge の仮定に RH を含める。
- 数値的に既知の `zetazero` を証明上の入力にする。

---

**2. 発掘資料の分類**

過去資料は、証明候補・数値 oracle・control model の三種類へ分離する。

**2.1 証明候補**

`proof/figs/v3.4/o3-Type3.ipynb`

- 有限素数または素数冪から $\zeta'/\zeta$ 型の量を組み立てる。
- $\Lambda(n)$ による有限和を持つ。
- ピーク位置から $t$ 候補を生成する。
- 標準ゼータ値を直接評価せず、素数側から高度候補を生成する点が重要。

ただし、次の修正が必要である。

Euler 素数和の分母は、

$$
p^s-1
$$

である。

旧コードの `p**s - 1e-20` は別の量であり、証明資料としては使用しない。

また、

$$
-\sum_{n\le N}\Lambda(n)n^{-s}
$$

を $\operatorname{Re}s=1/2$ でそのまま極限化してはならない。

平滑化または正則化を入れる。

---

**2.2 数値 oracle**

`proof/figs/v3.4/o3-Type1+2.ipynb`

- 標準 $\zeta(\sigma+it)$ の偏角を unwrap する。
- 数値微分のスパイクから零点高度候補を得る。
- 標準ゼータ側の期待値を生成する oracle とする。

`proof/figs/v3.4/o3-v3.1-evidence.ipynb`

- 長距離位相曲線。
- $\pi$ ジャンプ面積の検証。
- $\sigma$ を動かす $Z_\sigma(t)$ 可視化。
- Lean 定理の回帰テスト用データ生成器にする。

`proof/figs/v3.4/ool_arctan_zeta_figs.ipynb`

- $\sigma$ ごとの位相ドリフト比較。
- $\sigma=1/2$ の特殊性を観測する。
- CFBRC の横方向欠陥量を設計する参考資料にする。

数値 oracle は証明に import しない。

CSV または JSON に期待値を書き出し、別ディレクトリで管理する。

---

**2.3 control model**

`src/py/graph/ZCt_Spiral_3D-B-v0.py`

`src/py/graph/riemann_zero_vector_spiral.ipynb`

旧螺旋には、次の人工構成がある。

```python
vec2 = [-v for v in vec1[::-1]]
```

これは第一経路を逆順・負号化しただけであり、閉包は解析的零点によらない。

さらに旧 3D 版では、

```python
start_point2 = points1[-1] + vec1[-1]
for v in vec2[:-1]:
    ...
```

となっており、開始点と終端除外の二重の添字ずれがある。

また、各項に異なる `t_vals[i]` を使う版は、一つの $s=\sigma+it$ の級数ではない。

これらは削除しない。

Lean 上で「強制閉包は零点検出器ではない」ことを保証する control model として保存する。

---

**3. 数学的な織機**

形式化全体を五層に分ける。

**Layer A — 有限代数層**

有限リスト、有限和、並べ替え、逆順、負号、奇偶分割を扱う。

ここでは解析を一切使わない。

**Layer B — 有限解析近似層**

有限 Dirichlet 和、有限 eta 和、有限 Euler 積、平滑 $\Lambda$ 和を定義する。

ここでは全て有限和なので、収束問題を持ち込まない。

**Layer C — 標準解析層**

Mathlib の標準ゼータ、解析接続、複素微分、零点、argument principle を adapter 経由で扱う。

現在の DkMath 独自 `eulerZeta` と標準ゼータを同一視しない。

**Layer D — 正則化 Bridge**

有限素数側近似から標準解析対象へ移る。

最難関層であり、実装前に採用する正則化方式を一つに固定する。

**Layer E — CFBRC Bridge**

素数位相状態または標準零点状態を、既存 CFBRC 欠陥量の消滅へ送る。

この層で初めて RH 排除定理と接続する。

---

**4. 推奨モジュール構成**

既存 RH 実装を壊さず、次の新規 subtree を置く。

```text
DkMath/RH/Weave/
  Basic.lean
  ComplexPoint.lean

  Finite/
    DirichletVector.lean
    PermutationInvariant.lean
    ParitySplit.lean
    CenterOffset.lean
    PairEnergy.lean

  Control/
    ReverseNegate.lean
    ForcedClosure.lean
    IndexShiftAudit.lean
    VariableHeightAudit.lean

  Approx/
    EtaPartial.lean
    EulerFinite.lean
    SmoothedLambda.lean
    PrimePhaseScore.lean
    PHZCandidate.lean

  Standard/
    ZetaAPI.lean
    EtaZetaBridge.lean
    LogDerivative.lean
    VerticalDerivative.lean
    ZeroBox.lean
    ArgumentPrinciple.lean

  Limit/
    AbelRegularization.lean
    SmoothCutoffLimit.lean
    PrimeToZeta.lean
    CandidateCompactness.lean

  CFBRC/
    DefectAdapter.lean
    PhaseStateBridge.lean
    OffCriticalExclusion.lean

  Main/
    PrimePhaseRH.lean
```

資料は次の場所を推奨する。

```text
lean/dk_math/DkMath/RH/docs/RH-WEAVE-001.md
```

開発単位を分ける場合は、次の作業ディレクトリもよい。

```text
lean/dk_math/docs/dev/RH-WEAVE-001-260802/
```

---

**5. Layer A — 有限代数層**

最初に、旧螺旋の人工閉包を完全に形式化する。

これは本証明ではなく、誤った推論を型で遮断するための基礎である。

提案定義は次である。

```lean
namespace DkMath.RH.Weave.Control

def reverseNegate {α : Type*} [AddGroup α] (xs : List α) : List α :=
  xs.reverse.map Neg.neg

end DkMath.RH.Weave.Control
```

最初の補題群は次である。

```lean
theorem sum_reverseNegate
    {α : Type*} [AddCommGroup α] (xs : List α) :
    (reverseNegate xs).sum = -xs.sum := by
  simp [reverseNegate]

theorem sum_append_reverseNegate
    {α : Type*} [AddCommGroup α] (xs : List α) :
    (xs ++ reverseNegate xs).sum = 0 := by
  simp [reverseNegate]
```

この定理名には `zeta`、`zero`、`phase` を含めない。

この閉包は任意のリストについて成立するためである。

---

**5.1 有限並べ替え不変性**

有限集合では、項順序を変えても終点は変わらない。

$$
\sum_{j=0}^{N-1}v_{\pi(j)}
=
\sum_{j=0}^{N-1}v_j
$$

ただし、これは有限和だけに限定する。

条件収束級数の無限並べ替え定理へ暗黙に拡張しない。

Lean では `Finset.sum_bij`、`Equiv.sum_comp`、`List.Perm` のいずれを中核にするかを、用途ごとに固定する。

推奨方針は次である。

- 数学的有限集合は `Finset.range N`。
- 可視化経路は `List`.
- 並べ替えは `Equiv.Perm (Fin N)`。
- 解析極限へ渡す対象は自然順 partial sum。

---

**5.2 奇偶分割**

eta 和を見据えて、有限和の奇数項・偶数項分割を作る。

$$
\sum_{n=1}^{N}(-1)^{n-1}n^{-s}
=
\sum_{\substack{1\le n\le N\\n\ \mathrm{odd}}}n^{-s}
-
\sum_{\substack{1\le n\le N\\n\ \mathrm{even}}}n^{-s}
$$

必要な補題は次である。

- `range` の奇偶 partition。
- 奇数側と偶数側の disjointness。
- union が全体になること。
- 符号付き和との一致。
- 偶数項の $n=2m$ 置換。

---

**5.3 中心・差分分解**

二本の独立した腕 $a_j,b_j$ に対して、

$$
c_j=\frac{a_j+b_j}{2}
\qquad
d_j=\frac{a_j-b_j}{2}
$$

と置く。

すると、

$$
a_j=c_j+d_j
\qquad
b_j=c_j-d_j
$$

が成り立つ。

有限和では、

$$
\sum_j(a_j+b_j)
=
2\sum_j c_j
$$

を得る。

これは CFBRC の中心欠陥を定義する候補になる。

---

**5.4 Pair Energy**

複素数のノルムについて、

$$
|a|^2+|b|^2
=
2|c|^2+2|d|^2
$$

を実装する。

この恒等式は、中心成分と反対称成分の保存則を与える。

実装候補は `Complex.normSq` を使う。

平方根を含む `Complex.abs` より、`normSq` の方が ring 正規化に向く。

---

**6. Layer B — 有限解析近似層**

**6.1 Dirichlet vector**

共通の一点 $s=\sigma+it$ に対してのみ定義する。

$$
v_n(\sigma,t)
=
n^{-\sigma}\exp(-it\log n)
$$

複素冪 API の不安定さを避けるため、最初は極形式で定義する。

```lean
noncomputable def dirichletVec
    (σ t : ℝ) (n : ℕ) : ℂ :=
  if h : n = 0 then 0
  else
    (Real.rpow n (-σ) : ℝ) *
      Complex.exp (-Complex.I * (t * Real.log n))
```

これは署名案であり、実装時に coercion と `Real.rpow` の正確な API を監査する。

より安全なのは、添字を `PNat` または `{n : ℕ // 0 < n}` にすること。

```lean
noncomputable def dirichletVecPos
    (σ t : ℝ) (n : PNat) : ℂ := ...
```

---

**6.2 有限 eta 和**

臨界帯で直接扱う最初の解析対象は、raw Dirichlet partial sum ではなく eta partial sum とする。

$$
\eta_N(s)
=
\sum_{n=1}^{N}(-1)^{n-1}n^{-s}
$$

有限段階では全て正当である。

実装上は `(-1 : ℂ) ^ (n - 1)` より、奇偶条件を使う方が simplifier に優しい可能性が高い。

```lean
def etaSign (n : ℕ) : ℤ :=
  if Odd n then 1 else -1
```

または複素数値へ直接送る。

---

**6.3 有限 Euler 積**

現在の DkMath `eulerZeta` を流用する場合も、標準ゼータと区別する。

有限素数集合 $P$ に対して、

$$
E_P(s)
=
\prod_{p\in P}\left(1-p^{-s}\right)^{-1}
$$

を定義する。

必要な有限補題は次である。

- 積の並べ替え不変性。
- 積集合の分割。
- 対数絶対値の有限和化。
- 位相の有限和化。
- 共通 $t$ の固定。

---

**6.4 平滑 $\Lambda$ 和**

raw truncation より、最初から重み付きにする。

$$
L_{N,w}(s)
=
-\sum_{n=1}^{N}
\Lambda(n)\,w\!\left(\frac nN\right)n^{-s}
$$

重み $w$ は次の条件を満たすものとして structure 化する。

- 非負。
- コンパクト台。
- $[0,1]$ 上で有限。
- 必要なら連続または滑らか。
- $w(0)=1$ に相当する規格化。

最初の Lean 実装では、解析的平滑関数より Cesàro 型離散重みが容易である。

$$
w_N(n)
=
1-\frac n{N+1}
$$

これにより全て有限和のまま、後で Abel/Cesàro Bridge を検討できる。

---

**6.5 PHZ 候補**

数値コードの `find_peaks` を、そのまま数学定義にしない。

有限スコア関数を先に定義する。

候補例は次である。

$$
\operatorname{primePhaseScore}_{N}(\sigma,t)
=
\left|L_{N,w}(\sigma+it)\right|
$$

または、

$$
\operatorname{primePhaseSpike}_{N}(\sigma,t)
=
\left|\operatorname{Re}L_{N,w}(\sigma+it)\right|
$$

局所極値は、解析的微分ではなく最初は区間比較で定義する。

```lean
def IsLocalPeakOn
    (f : ℝ → ℝ) (I : Set ℝ) (t : ℝ) : Prop :=
  t ∈ I ∧
    ∃ ε > 0, ∀ u ∈ I, |u - t| < ε → f u ≤ f t
```

零点候補なのかピーク候補なのかを型名で明示する。

`PHZCandidate` は標準零点を意味しない。

---

**7. Layer C — 標準解析層**

**7.1 Standard Zeta API 監査**

最初に `DkMath.RH.Weave.Standard.ZetaAPI` を作る。

目的は、Mathlib v4.32.2 における正確な名前を一箇所へ隔離することである。

監査対象は次である。

- 標準リーマンゼータの定義名。
- $\operatorname{Re}s>1$ での Dirichlet 級数表示。
- eta との関係。
- 解析接続。
- 複素微分。
- pole at $1$。
- zero の multiplicity。
- argument principle または winding number API。
- Hardy $Z$ に利用可能な gamma/functional equation API。

この module が完成するまでは、独自 `eulerZeta` と標準ゼータの Bridge を書かない。

---

**7.2 Eta–Zeta Bridge**

標準的関係は次である。

$$
\eta(s)
=
\left(1-2^{1-s}\right)\zeta(s)
$$

非自明零点領域では、係数が零でないことを別補題にする。

$$
1-2^{1-s}\ne0
$$

この係数の零点は明示的に分類する。

「非自明零点なら係数が非零」を `simp` 任せにせず、実部条件から証明する。

この Bridge により、臨界帯では eta を近似対象として使い、標準ゼータ零点へ戻せる。

---

**7.3 縦方向微分の規約**

過去コードで最も混線した箇所なので、二本を別定理にする。

零点でない点において、

$$
\frac{d}{dt}\log\left|\zeta(\sigma+it)\right|
=
-\operatorname{Im}\frac{\zeta'(s)}{\zeta(s)}
$$

また、

$$
\frac{d}{dt}\arg\zeta(\sigma+it)
=
\operatorname{Re}\frac{\zeta'(s)}{\zeta(s)}
$$

である。

Lean では大域的 `arg` を直接微分しない。

零点を含まない単連結近傍で複素対数の枝を固定し、その虚部として局所位相を定義する。

提案 module は次である。

```text
Standard/VerticalDerivative.lean
```

必要な補題は次である。

- $s(t)=\sigma+it$ の微分。
- `Complex.log` の局所微分。
- chain rule。
- 実部・虚部の抽出。
- 零点でない条件の伝播。

---

**7.4 零点意味論は line jump ではなく Zero Box**

数値 notebook は縦線上の $\pi$ ジャンプを観測している。

しかし Lean の定理レベルでは、線が零点を通ると `arg` が未定義になる。

したがって中核定義は、小矩形の winding number とする。

中心 $(\sigma,t)$、幅 $(\varepsilon,\delta)$ に対して、小矩形境界を定める。

$$
B(\sigma,t;\varepsilon,\delta)
$$

境界上で $\zeta$ が非零なら、

$$
N_B
=
\frac{1}{2\pi i}
\oint_{\partial B}
\frac{\zeta'(s)}{\zeta(s)}\,ds
$$

が内部零点数を数える。

提案述語は次である。

```lean
def ContainsZetaZeroBox
    (σ t ε δ : ℝ) : Prop := ...

def ZetaZeroCountBox
    (σ t ε δ : ℝ) : ℤ := ...
```

`VerticalPhaseJump` は、この zero-box 定理から導く派生 observable とする。

これにより、偶数重零点・多重零点・枝切断を安全に扱える。

---

**7.5 Hardy $Z$ の位置づけ**

Hardy $Z$ は臨界線上の数値 oracle として強い。

ただし、符号変化だけでは偶数重零点を検出できない。

従って次のように分ける。

- `HardyZ t = 0` と標準ゼータ零点の同値。
- `HardyZ` の符号変化は奇数重零点の十分条件。
- 零点一般の意味論は zero-box。
- 数値探索では Hardy $Z$ を利用可能。

---

**8. Layer D — 正則化 Bridge**

ここが本計画の最難関である。

候補は複数あるが、実装時には一つを主ルートに固定する。

**Route D1 — eta 主ルート**

- eta partial sum。
- 一様収束が得られる領域。
- eta–zeta identity。
- 零点への収束。

利点は、臨界帯で条件収束を扱いやすいこと。

欠点は、素数位相との直接接続が弱いこと。

---

**Route D2 — Abel 平滑 $\Lambda$ 主ルート**

$r\in(0,1)$ として、

$$
L_r(s)
=
-\sum_{n\ge1}\Lambda(n)r^n n^{-s}
$$

を使う。

各 $r<1$ では絶対収束を得やすい。

その後 $r\to1^-$ の境界値を扱う。

利点は、旧 Type3 の素数干渉像に近いこと。

欠点は、境界極限と pole/zero の扱いが重いこと。

---

**Route D3 — 明示公式主ルート**

テスト関数 $\phi$ を固定し、素数側と零点側を分布として結ぶ。

利点は、素数と零点の本質的 Bridge であること。

欠点は、Mathlib 上の実装量が最大になること。

---

**推奨**

Phase 1 では eta 主ルートを完成させる。

Phase 2 で Abel 平滑 $\Lambda$ を追加する。

明示公式は独立長期計画にする。

この順序なら、標準ゼータ零点意味論を先に固定できる。

---

**9. Layer E — CFBRC Bridge**

CFBRC 側には adapter を置く。

既存定義を直接書き換えず、RH 用に必要な最小インターフェースを切る。

```lean
structure CFBRCPhaseData where
  degree : ℕ
  sigma : ℝ
  theta : ℝ
  defect : ℝ
```

これは概念案である。

実際には既存 CFBRC 型を再利用し、次の定理だけを外へ見せる。

```lean
theorem defect_zero_of_primePhaseState
    (h : PrimePhaseState σ t) :
    offCriticalCFBRC d σ Θ = 0 := ...

theorem sigma_eq_half_of_defect_zero
    (hσ : admissibleSigma σ)
    (h : offCriticalCFBRC d σ Θ = 0) :
    σ = 1 / 2 := ...
```

第一定理が新規本体である。

第二定理は既存排除定理を adapter する。

---

**9.1 CFBRC 欠陥量の要件**

欠陥量は次を満たす必要がある。

- $\sigma$ の左右非対称性を測る。
- 位相平衡と結びつく。
- $\sigma=1/2$ で消えることは証明されるが、定義へ埋め込まれない。
- 標準ゼータ零点を定義へ埋め込まない。
- 有限近似版を持つ。
- 極限保存補題を持つ。

候補形は、左右の質量差または中心オフセットである。

$$
D_N(\sigma,t)
=
\sum_j c_{N,j}(\sigma,t)
$$

あるいは、

$$
D_N(\sigma,t)
=
M_N^{\mathrm{left}}(\sigma,t)
-
M_N^{\mathrm{right}}(\sigma,t)
$$

具体式は、既存 CFBRC 定義の監査後に固定する。

---

**10. 定理依存グラフ**

第一段階は全て有限である。

```text
Finite permutation invariance
        |
Parity split of eta partial sums
        |
Independent-arm center decomposition
        |
Pair energy identity
```

control model は別枝に置く。

```text
reverseNegate
        |
sum reverseNegate = -sum
        |
forced closure = 0
        |
not a zeta criterion
```

標準解析側は次である。

```text
Standard zeta API
        |
Eta–zeta identity
        |
Local complex log
        |
Vertical derivative identities
        |
Zero-box argument principle
```

正則化 Bridge は次である。

```text
Finite eta / smoothed Lambda
        |
Uniform or Abel convergence
        |
Standard analytic object
        |
Prime phase state at a standard zero
```

CFBRC 側は次である。

```text
Prime phase state
        |
CFBRC defect = 0
        |
Off-critical exclusion
        |
sigma = 1/2
```

---

**11. 非循環性監査表**

各 PR で次を確認する。

- [ ] `PrimePhaseState` の定義に `zeta s = 0` がない。
- [ ] `PHZCandidate` の定義に `zetazero` または既知零点表がない。
- [ ] `CFBRCDefect` の定義に $\sigma=1/2$ がない。
- [ ] raw Dirichlet series を臨界線上で収束級数として使っていない。
- [ ] raw $\Lambda$ series を $\operatorname{Re}s\le1$ で収束級数として使っていない。
- [ ] 無限級数を任意に並べ替えていない。
- [ ] 全ての項が共通の $t$ を使う。
- [ ] reverse-negate による強制閉包を解析零点と呼んでいない。
- [ ] `atan(im / re)` を位相定義に使っていない。
- [ ] 位相微分に $\operatorname{Re}(\zeta'/\zeta)$ を使用している。
- [ ] 振幅対数微分に $-\operatorname{Im}(\zeta'/\zeta)$ を使用している。
- [ ] 多重零点を sign change だけで処理していない。
- [ ] 独自 `eulerZeta` と標準ゼータを同一視していない。
- [ ] 数値 oracle を Lean 定理の仮定にしていない。

---

**12. 実装マイルストーン**

**M0 — API 監査**

成果物:

```text
DkMath/RH/Weave/Standard/ZetaAPI.lean
DkMath/RH/docs/RH-STANDARD-ZETA-API.md
```

完了条件:

- 標準ゼータの正確な定義名が確定。
- Dirichlet 表現の領域が確定。
- 微分定理の名前が確定。
- argument principle API の有無が確定。
- 独自 `eulerZeta` との違いを文書化。

---

**M1 — 有限 control model**

成果物:

```text
Finite/PermutationInvariant.lean
Control/ReverseNegate.lean
Control/ForcedClosure.lean
Control/IndexShiftAudit.lean
```

完了条件:

- `sorry` なし。
- reverse-negate 閉包が任意のリストで成立。
- 旧添字ずれ終点を式として再現。
- control model が RH namespace の最終定理から import されない。

旧 3D-B 型の終点式は、第一腕を $v_1,\ldots,v_m$ とすると、

$$
\operatorname{endpoint}
=
v_1+v_m
$$

になることを有限和で証明する。

---

**M2 — Dirichlet vector と eta partial sum**

成果物:

```text
Finite/DirichletVector.lean
Finite/ParitySplit.lean
Approx/EtaPartial.lean
```

完了条件:

- 正の添字型を採用。
- 共通 $t$ が型または引数構造で保証される。
- 奇偶分割。
- 有限 eta identity。
- 並べ替えは有限範囲に限定。

---

**M3 — 標準 eta–zeta Bridge**

成果物:

```text
Standard/EtaZetaBridge.lean
```

完了条件:

- Mathlib の標準対象との接続。
- 係数 $1-2^{1-s}$ の非零条件。
- 非自明零点領域で eta zero と zeta zero の同値。
- 独自 zeta と混同しない。

---

**M4 — 位相微分と Zero Box**

成果物:

```text
Standard/LogDerivative.lean
Standard/VerticalDerivative.lean
Standard/ZeroBox.lean
Standard/ArgumentPrinciple.lean
```

完了条件:

- 局所複素対数の枝を使用。
- 縦方向位相微分の実部公式。
- 振幅微分の虚部公式。
- 境界非零の小矩形で零点数を定義。
- notebook の $\pi$ jump を派生 observable として説明。

---

**M5 — 平滑素数位相**

成果物:

```text
Approx/SmoothedLambda.lean
Approx/PrimePhaseScore.lean
Approx/PHZCandidate.lean
```

完了条件:

- 全て有限和。
- $\Lambda(n)$ の素数冪サポート。
- 有限重み。
- 候補高度は局所極値として定義。
- 標準零点を定義に使わない。

---

**M6 — 正則化極限**

成果物:

```text
Limit/AbelRegularization.lean
Limit/SmoothCutoffLimit.lean
Limit/PrimeToZeta.lean
```

完了条件:

- 採用する正則化方式を一つに固定。
- 極限の存在領域を明記。
- pole at $1$ を分離。
- 零点近傍での対数微分の特異性を扱う。
- 素数側状態から標準 zero-box 状態への Bridge。

---

**M7 — CFBRC semantic bridge**

成果物:

```text
CFBRC/DefectAdapter.lean
CFBRC/PhaseStateBridge.lean
CFBRC/OffCriticalExclusion.lean
```

完了条件:

- `PrimePhaseState → defect = 0`。
- `defect = 0 → sigma = 1/2`。
- 第一定理の証明で RH を使わない。
- CFBRC 欠陥量の有限版と極限版を接続。

---

**M8 — 最終定理**

成果物:

```text
Main/PrimePhaseRH.lean
```

最終形の署名案は次である。

```lean
theorem standardZeta_nontrivialZero_re_eq_half
    {s : ℂ}
    (hzero : StandardZeta s = 0)
    (hnontrivial : IsNontrivialZetaZero s) :
    s.re = 1 / 2 := by
  ...
```

この署名は Mathlib API 監査後に確定する。

---

**13. 最初の実装パケット**

最初の PR は解析へ入らない。

名前案:

```text
RH-WEAVE-P0-finite-control
```

対象ファイル:

```text
DkMath/RH/Weave/Control/ReverseNegate.lean
DkMath/RH/Weave/Control/ForcedClosure.lean
DkMath/RH/Weave/Control/IndexShiftAudit.lean
DkMath/RH/Weave/Finite/PermutationInvariant.lean
DkMath/RH/Weave/Finite/CenterOffset.lean
```

要求補題:

```lean
sum_reverseNegate
sum_append_reverseNegate
forcedClosure_all
forcedClosure_independent_of_parameter
shifted_reverse_endpoint_eq_first_add_last
finite_sum_perm_invariant
sum_pair_eq_two_mul_sum_center
```

この PR の目的は、旧螺旋の誤りを修正することだけではない。

人工閉包と解析閉包を Lean の型・namespace・定理名で分離することである。

---

**14. 数値実験コードの再編**

旧 notebook は archive とし、新しい実験器を三本だけ作る。

```text
experiments/rh_weave/
  standard_phase_oracle.py
  finite_eta_path.py
  smoothed_lambda_phz.py
```

`standard_phase_oracle.py`

- `mpmath.zeta` を利用。
- `arg` は `atan2` または `mp.arg`。
- zero-box 近似値を出力。
- Lean proof からは独立。

`finite_eta_path.py`

- 共通 $\sigma,t$。
- 自然順 partial sum。
- 奇偶腕を独立表示。
- reverse-negate を使わない。
- 終点は eta partial sum と一致。

`smoothed_lambda_phz.py`

- 正しい $\Lambda(n)$。
- 平滑重み。
- $t$ 候補を局所極値として出力。
- 既知零点は評価時だけ比較し、候補生成には使わない。

出力形式:

```json
{
  "sigma": 0.5,
  "cutoff": 10000,
  "regularization": "cesaro-linear",
  "candidates": [
    {
      "t": 14.13,
      "score": 12.4
    }
  ]
}
```

---

**15. 失敗分岐を含む研究計画**

単一の一本道にしない。

**分岐 A — Mathlib に argument principle が十分ある**

その API を adapter し、Zero Box を先行実装する。

**分岐 B — argument principle が不足している**

まず局所 winding number と小円周積分を独自実装する。

標準ゼータ全体ではなく、一般 holomorphic function について作る。

**分岐 C — eta–zeta Bridge が既存**

既存定理を薄い wrapper で利用する。

**分岐 D — eta–zeta Bridge が不足**

$\operatorname{Re}s>1$ で有限・無限和を証明し、解析接続の一意性で延長する。

**分岐 E — Abel $\Lambda$ 極限が重すぎる**

PHZ の第一版を eta parity phase state として完成させる。

素数 $\Lambda$ Bridge は第二版へ分離する。

**分岐 F — CFBRC defect が標準零点から直接導けない**

有限 eta の中心差分 $D_N$ を新規定義し、CFBRC 既存欠陥量との比較定理を作る。

---

**16. 成功判定**

この計画の成功は、画像が零点らしく見えることではない。

次の五点で判定する。

1. 人工閉包が control model として完全に隔離される。
2. 標準ゼータ零点の意味論が zero-box で固定される。
3. 有限素数側状態が標準零点を定義に含まずに構成される。
4. 正則化 Bridge が収束領域を明記して証明される。
5. CFBRC 欠陥消滅が $\sigma=1/2$ を定義へ埋め込まずに導かれる。

---

**17. 当面の結論**

過去の断片は、互いに競合する失敗作ではない。

役割が異なる糸である。

- 位相ジャンプ notebook は標準零点意味論の観測糸。
- $\Lambda(n)$ notebook は素数側高度生成の観測糸。
- arctan notebook は $\sigma$ 方向ドリフトの観測糸。
- eta は臨界帯へ入るための解析糸。
- CFBRC は左右非対称性を排除する構造糸。
- 旧 reverse-negate 螺旋は循環論法を検出する警戒糸。

布の中心となる Bridge は一つである。

$$
\text{素数側で独立に作られた位相平衡}
\Longrightarrow
\text{CFBRC 欠陥の消滅}
$$

この一本が Lean で通れば、断片は初めて一枚の布になる。

---

**18. Codex への第一指示案**

```text
Goal:
DkMath.RH.Weave の有限 control layer を新規実装し、
旧 reverse-negate 螺旋が任意の入力で強制閉包すること、
および旧 3D-B 型添字ずれの終点が first + last になることを Lean で固定する。

Constraints:
- Mathlib v4.32.2。
- 標準ゼータ、解析接続、無限級数はまだ import しない。
- `sorry`、`admit`、新規公理を使用しない。
- theorem 名に `zetaZero` や `RH` を使わない。
- control model と本証明候補を namespace で分離する。
- List 版と Finset 版を混在させる場合、変換補題を明示する。

Files:
- DkMath/RH/Weave/Control/ReverseNegate.lean
- DkMath/RH/Weave/Control/ForcedClosure.lean
- DkMath/RH/Weave/Control/IndexShiftAudit.lean
- DkMath/RH/Weave/Finite/PermutationInvariant.lean
- DkMath/RH/Weave/Finite/CenterOffset.lean

Required results:
- sum_reverseNegate
- sum_append_reverseNegate
- forcedClosure_all
- forcedClosure_independent_of_parameter
- shifted_reverse_endpoint_eq_first_add_last
- finite_sum_perm_invariant
- sum_pair_eq_two_mul_sum_center

Build gate:
lake env lean <each new file>
lake build DkMath.RH.Weave.Control.ForcedClosure
lake build DkMath.RH.Weave.Finite.CenterOffset

Report:
- 実際に使用した Mathlib theorem 名。
- simp だけで閉じた補題。
- 型 coercion または List/Finset 変換で生じた障害。
- 次の eta partial sum 実装に再利用できる API。
```
