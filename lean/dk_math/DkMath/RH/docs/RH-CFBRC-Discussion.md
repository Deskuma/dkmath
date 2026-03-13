# RH-CFBRC Discussion

> 👩‍⚕️私D.:

ちょっと FLT 離れて CFBRC から RH への道筋を歩もうかと思ってるのだが。
オイラーゼータ関数

<https://github.com/Deskuma/dkmath/tree/nightly/lean/dk_math/DkMath/RH>

少し触りを入れただけだが #HOPC-RH 構造を明確化していこうかと。
ここで何か FLT や ABC予想、コラッツ予想関連のヒントが得られるかもしれないかなあ。とか。

気分もリフレッシュで。

GN 構造の本質探り的な寄り道のような本筋ルート。

> 🐺賢狼:

よし、それは良い寄り道じゃ。FLT の戦場からいったん離れて、`CFBRC → RH` の骨格を先に立てるのは、逃避ではなく **本質の抽出作業** じゃよ。いまから GitHub 側の `DkMath/RH` と手元スナップショットの両方を見て、`#HOPC-RH` をどう育てると他予想への橋になるかを整理する。

> 🐺賢狼:

方向性はかなり良いぞ。いま見えている `RH` 側は、もう単なる思いつき置き場ではなく、**位相ドリフト骨格 → EulerZeta magnitude 収束 → phase 接続待ち** という三段構えになっておる。ここを明確化すると、`GN` の「局所因子の挙動を見る目」が別の形で洗練されるはずじゃ。

> 🐺賢狼:

## 1. . それ、かなり良い手じゃ

わっちは **賛成** じゃ。
これは FLT からの逃避ではなく、むしろ **`GN` の本質を別の光で炙り出す本筋寄りの寄り道** じゃよ。

いまの `RH` ディレクトリは、すでに

- 位相ドリフト骨格
- EulerZeta の magnitude / phase 分離
- magnitude 側の \(\sigma > 1\) における無限積収束と正値

まで意図が明確に書かれておる。README でも、「ゼータへ差し込む前段として、位相速度を Lean で扱う骨格を作り、その骨格上で EulerZeta の無限積を収束・正値まで固める」と整理されておるし、位相は `arg` 直打ちではなく積分によるアンラップで扱う方針だと明記されておる。

## 2. . なぜ CFBRC から RH へ行くのが筋が良いのか

理由は、両者とも **素数ごとの局所因子を見て、全体を組み立てる学問の顔** をしておるからじゃ。

`CFBRC` 側は README で、

\[
(x+u)^d-u^d = x \cdot \mathrm{core}_d(x,u)
\]

を核にして、

- 代数恒等式層
- 円分多項式層
- 数論層

を橋渡しする実装だと明言しておる。しかも `cyclotomicPrimeCore` と `GN` の同一化、除法判定、`padicValNat`、primitive prime existence までを視野に入れておる。

一方 `RH` 側は、`vertical`, `torque`, `phaseVel`, `phaseUnwrap` を導入し、EulerZeta を

\[
\zeta_e(s)=\prod_p \frac{p^s}{p^s-1}
\]

の位相つき再編として置き、その magnitude 版

\[
a_p(\sigma,t)=\frac{e^{\sigma \log p}}{\left\|e^{(\sigma+it)\log p}-1\right\|}
\]

の無限積を formalize しておる。さらに README では、\(\sigma>1\) で `Multipliable` と \(0<eulerZetaMag\) を確定したと書いてある。

つまり両者とも、乱暴に言えば

\[
\text{局所素数因子} \;\to\; \text{全体構造}
\]

の型をしておる。
ここが同じ匂いなのじゃ。なかなか旨い匂いじゃろ。

## 3. . どこが「本質の共通核」になりそうか

わっちの見立てでは、共通核は **幾何級数骨格** じゃ。

`GN` は差冪の商としての有限幾何和じゃな。

\[
GN(d,x,u)=\sum_{k=0}^{d-1}(x+u)^{d-1-k}u^k
\]

一方、Euler 因子は収束域で無限幾何和を持つ。

\[
\frac{1}{1-p^{-s}}=\sum_{n\ge 0} p^{-ns}
\]

この二つは、有限か無限かの違いはあれど、どちらも **「1 個の核から反復構造を起こす」** という顔をしておる。
CFBRC ではそれが差冪・円分・valuation に現れ、RH ではそれが局所位相・局所振幅・全体位相に現れる。

なので、`CFBRC → RH` の橋は

\[
\text{差冪の有限幾何和}
\longleftrightarrow
\text{Euler 因子の無限幾何和}
\]

として見るのが一番自然じゃ。
ここは論文の大看板にしやすい。

## 4. . ただし、ここで酔ってはいかぬ点

ここは冷酒でいこう。

いまの `RH` 実装は README の言葉どおり **前段骨格** じゃ。
位相ドリフト骨格はできており、EulerZeta も magnitude 版の収束までは固まっている。だが phase 側は「`arg` を直接使わずアンラップへ接続する予定」と書かれておるので、**まだ #HOPC-RH の核心は入口に立った段階** と見るのが正確じゃ。

ゆえに、ここからすぐ

\[
\text{RH} \Rightarrow \text{FLT/ABC/Collatz の鍵}
\]

と言うのは、ちと酒が回りすぎじゃ。
正しくは、

\[
\text{RH 側で prime-local phase の観測装置を作る}
\]

その結果として、

- FLT / ABC には **prime-local obstruction の見え方**
- Collatz には **離散写像の位相的再符号化のヒント**

が出る **かもしれぬ** 、くらいが誠実じゃな。

特に相性の良さで言えば、

\[
\text{FLT} \approx \text{ABC} \;>\; \text{Collatz}
\]

とわっちは見る。
Collatz は prime factor より **2 進的・離散写像的な癖** が強いので、直接の橋は少し遠い。

## 5. . いま進めるなら、#HOPC-RH はこう刻むのがよい

わっちなら、次の 4 段で刻む。

### 5.1. . 単一素数因子の位相力学を完成させる

まず \(p\) 固定で

\[
w_p(\sigma,t)=e^{(\sigma+it)\log p}-1
\]

を主役にする。
`phaseVel`, `torque`, `phaseUnwrap` をこの \(w_p\) に差し込み、

\[
\theta_p'(t)=\Im\!\left(\frac{w_p'(t)}{w_p(t)}\right)
\]

を Lean で一本化する。
いまの RH 骨格は、まさにここへ行くために作られておる。

### 5.2. . 有限 Euler 積で HOPC を作る

無限積へ飛ぶ前に、まず

\[
Z_N(s)=\prod_{p\le N}\frac{p^s}{p^s-1}
\]

で位相ドリフトを観測する。
有限積なら、局所因子の寄与を足し合わせる構図が明瞭じゃ。

ここで大事なのは、積を微分すると和になることじゃ。

\[
\frac{d}{dt}\log Z_N(\sigma+it)=
\sum_{p\le N}\frac{d}{dt}\log\!\left(\frac{p^s}{p^s-1}\right)
\]

この「積を和へほどく」視点は、CFBRC の `core` / `GN` / `valuation` の組立て感覚とも相性が良い。

### 5.3. . phase と magnitude の分業を明確化する

README にあるように、いま magnitude 側は \(\sigma>1\) で収束と正値まで押さえてある。なら next step は、

- magnitude は **安定性・収束性**
- phase は **零点検出・共鳴検出**

と役割分担を明確にすることじゃ。

この切り分けができると、#HOPC-RH は単なる「ゼータの別表現」ではなく、

\[
\text{安定な振幅} + \text{情報を運ぶ位相}
\]

という研究プログラムになる。これは強い。

### 5.4. . CFBRC と接続する「素数局所寄与 API」を作る

ここが一番おもしろいところじゃ。

`CFBRC` には既に

- core
- divisibility
- valuation
- primitive prime

の API がある。

`RH` 側にも、これに対応する抽象 API を作るのじゃ。たとえば概念的には、

- `PrimeLocalPhaseKernel`
- `PrimeLocalMagKernel`
- `PrimeScaleResonance`
- `PrimeContributionSum`

のようなものじゃな。

そうすると CFBRC 側の

\[
\text{prime divides / lifts / primitive}
\]

という言葉と、RH 側の

\[
\text{prime rotates / resonates / cancels}
\]

という言葉を、**同じ prime-local contribution language** で語れるようになる。
ここまで来ると、寄り道ではなく堂々たる本丸の別門じゃ。

## 6. . ぬしの問いへの、賢狼の答え

答えはこうじゃ。

\[
\boxed{
\text{CFBRC から RH へ進むのは、かなり筋が良い。}
}
\]

ただし目的は「いきなり RH を証明する」ことではなく、

\[
\boxed{
\text{GN 構造の本質を、prime-local phase / magnitude の言葉で再定式化すること}
}
\]

じゃ。

その副産物として、

- FLT には **primitive prime の“新規寄与” の見え方**
- ABC には **radical と局所増幅の見え方**
- Collatz には **離散写像の位相的圧縮表現のヒント**

が出る可能性はある。
だが、最も見込みが高いのはまず FLT と ABC じゃな。

要するに、これは気分転換の顔をした **研究の地盤改良** じゃよ。
実に良い酒の抜き方じゃ。

次にやるなら、わっちは
**`#HOPC-RH` の 1 枚設計図 `RH/docs/HOPC-RH-Roadmap.md` の素案** を起こして、`single-prime → finite Euler product → unwrap phase → zeta insertion` の 4 段を明文化するのを勧める。

## Appendix

### HOPC-RH

see: [HOPC-RH](HOPC-RH.txt)

> HOPC-RH = Holo Orthogonal Phase–Curvature method
> 日本語では「偏角直交・停留・曲率法」と呼ぶ。
>
> このタグの意味は、ゼータや Euler 因子の prime-local な寄与を、
> 単なる複素数評価ではなく
>
> - 位相速度
> - 位相の停留
> - 曲率
> - 局所寄与の干渉
> - それらの総和としての零点候補

> という観点で整理する方法論である。

### Implementation Bridge (RH-H1/H2)

CFBRC 側から RH 側を参照する際の、現行公開 API の最短導線:

- 定義:
  - `hopcPrimeLocalContribution`
  - `hopcPrimeContributionSum`
  - file: `DkMath/RH/EulerZeta.lean`
- 同一化補題:
  - `eulerZetaFactorPhaseVelFinite_eq_hopcPrimeContributionSum`
  - file: `DkMath/RH/EulerZetaLemmas.lean`
- 停留判定:
  - `driftFreeAt_eulerZetaFinite_onVertical_iff_hopcPrimeContributionSum_eq_zero`
  - `stationaryAt_eulerZetaFinite_onVertical_iff_hopcPrimeContributionSum_eq_zero`
  - `nondegenerateStationaryAt_eulerZetaFinite_onVertical_iff_hopcPrimeContributionSum`
  - file: `DkMath/RH/EulerZetaLemmas.lean`

対応する読み順:

1. `hopcPrimeLocalContribution` / `hopcPrimeContributionSum`（観測量名）
2. `...eq_hopcPrimeContributionSum`（既存位相速度和との同一化）
3. `driftFreeAt` / `stationaryAt` / `nondegenerateStationaryAt` の同値補題

### Implementation Bridge (RH-N4: BoundarySide 高位 API)

`CFBRC.BoundarySide`（`.right` / `.left`）で左右境界を統一した
bridge API は次を公開している。

- singleton:
  - `exists_stationaryAt_singleton_of_cfbRc_primitive_prime_boundary_bridge_of_local`
- small finite-set:
  - `exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_local`
  - `exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_local_split`
  - `BoundaryInsertLocalLiftProvider`
  - `exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_provider`

実運用では split 仮定版（`..._split`）を推奨する。
理由は、翻訳レイヤで次の 2 つを独立に供給できるため。

- `hS_lift`: `insert p S` 上の `w_r ≠ 0`
- `hsum_lift`: `hopcPrimeContributionSum (insert p S) = 0`

最小テンプレート:

```lean
import DkMath.RH.CFBRCBridge

open DkMath.RH.EulerZeta

example (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with
      | .right => ¬ d ∣ x
      | .left => ¬ d ∣ u)
    (hS_lift :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with | .right => ¬ p.1 ∣ x | .left => ¬ p.1 ∣ u) →
          ∀ r ∈ (insert p S), eulerZeta_exp_s_log_p_sub_one r.1 σ t ≠ 0)
    (hsum_lift :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with | .right => ¬ p.1 ∣ x | .left => ¬ p.1 ∣ u) →
          hopcPrimeContributionSum (S := insert p S) σ t = 0) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.stationaryAt
        (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t := by
  exact
    exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_local_split
      (side := side) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
      hd_prime hd_ge hx hu hcop hpnd hS_lift hsum_lift
```

これで CFBRC 側の「prime-local contribution language」から、
RH 側の停留・曲率 API へ直接接続できる。

### Implementation Bridge (RH-N8: Provider record 直結)

RH-N7 で追加した provider record 版は、split 仮定を
`BoundaryInsertLocalLiftProvider` に束ねて受け取る。

```lean
import DkMath.RH.CFBRCBridge

open DkMath.RH.EulerZeta

example (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with
      | .right => ¬ d ∣ x
      | .left => ¬ d ∣ u)
    (provider : BoundaryInsertLocalLiftProvider side S d x u σ t) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.stationaryAt
        (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t := by
  exact
    exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_provider
      (side := side) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
      hd_prime hd_ge hx hu hcop hpnd provider
```

使い分け:

- 供給器が個別関数で出る場合:
  `..._of_local_split`
- 供給器を 1 record で管理する場合:
  `..._of_provider`

### Implementation Bridge (RH-N14: 段階供給から provider 生成)

RH-N12/N13 では provider 供給を 2 段に分離できるようになった。

- nonzero 側:
  - `boundary_hS_lift_of_nonzero_on_S_and_witness`
  - `boundaryInsertLocalLiftProvider_of_nonzero_on_S_and_witness`
- sum-zero 側:
  - `boundary_hsum_lift_of_local_zero_on_S_and_witness`
  - `boundaryInsertLocalLiftProvider_of_nonzero_and_local_zero_on_S_and_witness`

最小テンプレート（段階供給 → provider 化）:

```lean
import DkMath.RH.CFBRCBridge

open DkMath.RH.EulerZeta

example (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hS_nonzero :
      ∀ r ∈ S, eulerZeta_exp_s_log_p_sub_one r.1 σ t ≠ 0)
    (hwnz_witness :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with | .right => ¬ p.1 ∣ x | .left => ¬ p.1 ∣ u) →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hS_local0 :
      ∀ r ∈ S, hopcPrimeLocalContribution r.1 σ t = 0)
    (hlocal_witness :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with | .right => ¬ p.1 ∣ x | .left => ¬ p.1 ∣ u) →
          hopcPrimeLocalContribution p.1 σ t = 0) :
    BoundaryInsertLocalLiftProvider side S d x u σ t := by
  exact
    boundaryInsertLocalLiftProvider_of_nonzero_and_local_zero_on_S_and_witness
      (side := side) (S := S)
      (hS_nonzero := hS_nonzero)
      (hwnz_witness := hwnz_witness)
      (hS_local0 := hS_local0)
      (hlocal_witness := hlocal_witness)
```

### Implementation Bridge (RH-N26: boundary_dvd + gap / boundaryCore witness 正規化)

RH-N21/N22 では、`S` 上の boundary 除法情報と gap 非除法情報を軸に、
provider 供給前提を段階的に削減した。

- `boundary_nonzero_on_S_of_boundary_dvd_and_gap`
- `boundary_local_zero_on_S_of_boundary_dvd_and_gap`
- `boundaryInsertLocalLiftProvider_of_boundary_dvd_and_gap`
- `boundary_hwnz_witness_of_boundaryCore_nonzero`
- `boundary_hlocal_witness_of_boundaryCore_local_zero`
- `boundaryInsertLocalLiftProvider_of_boundary_dvd_and_gap_of_boundaryCore_witness`
- `hopcPrimeLocalContribution_eq_eulerZetaFactorPhaseVelLocal_of_nonzero`
- `hopcPrimeLocalContribution_eq_zero_of_factorPhaseVelLocal_eq_zero_of_nonzero`
- `eulerZetaFactorPhaseVelLocal_eq_zero_of_hopcPrimeLocalContribution_eq_zero_of_nonzero`
- `boundary_hlocal_core_of_boundaryCore_factorPhaseVelLocal_eq_zero`
- `boundary_hfactor_core0_of_boundaryCore_local_zero`
- `boundary_hlocal_core_of_boundaryDiffPow_local_zero`
- `boundaryInsertLocalLiftProvider_of_boundary_dvd_gap_of_boundaryCore_factor0`
- `boundaryInsertLocalLiftProvider_of_boundary_dvd_gap_of_boundaryDiffPow_local0`
- `exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_factor0`
- `exists_stationaryAt_singleton_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_factor0`
- `exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_local0`
- `exists_stationaryAt_singleton_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_local0`
- `exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_local0`
- `exists_stationaryAt_singleton_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_local0`

最小テンプレート（boundary_dvd + gap + witness → provider）:

```lean
import DkMath.RH.CFBRCBridge

open DkMath.RH.EulerZeta

example (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hS_dvd :
      ∀ r ∈ S, r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hS_gap :
      ∀ r ∈ S, (match side with | .right => ¬ r.1 ∣ x | .left => ¬ r.1 ∣ u))
    (hwnz_witness :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with | .right => ¬ p.1 ∣ x | .left => ¬ p.1 ∣ u) →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hlocal_witness :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with | .right => ¬ p.1 ∣ x | .left => ¬ p.1 ∣ u) →
          hopcPrimeLocalContribution p.1 σ t = 0) :
    BoundaryInsertLocalLiftProvider side S d x u σ t := by
  exact
    boundaryInsertLocalLiftProvider_of_boundary_dvd_and_gap
      (side := side) (S := S)
      (hS_dvd := hS_dvd)
      (hS_gap := hS_gap)
      (hwnz_witness := hwnz_witness)
      (hlocal_witness := hlocal_witness)
```

最小テンプレート（boundaryCore witness → provider）:

```lean
import DkMath.RH.CFBRCBridge

open DkMath.RH.EulerZeta

example (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hS_dvd :
      ∀ r ∈ S, r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hS_gap :
      ∀ r ∈ S, (match side with | .right => ¬ r.1 ∣ x | .left => ¬ r.1 ∣ u))
    (hwnz_core :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hlocal_core :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          hopcPrimeLocalContribution p.1 σ t = 0) :
    BoundaryInsertLocalLiftProvider side S d x u σ t := by
  exact
    boundaryInsertLocalLiftProvider_of_boundary_dvd_and_gap_of_boundaryCore_witness
      (side := side) (S := S)
      (hS_dvd := hS_dvd)
      (hS_gap := hS_gap)
      (hwnz_core := hwnz_core)
      (hlocal_core := hlocal_core)
```

最小テンプレート（boundaryCore 上の factor 位相速度ゼロ → provider）:

```lean
import DkMath.RH.CFBRCBridge

open DkMath.RH.EulerZeta

example (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hS_dvd :
      ∀ r ∈ S, r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hS_gap :
      ∀ r ∈ S, (match side with | .right => ¬ r.1 ∣ x | .left => ¬ r.1 ∣ u))
    (hwnz_core :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_core0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0) :
    BoundaryInsertLocalLiftProvider side S d x u σ t := by
  exact
    boundaryInsertLocalLiftProvider_of_boundary_dvd_gap_of_boundaryCore_factor0
      (side := side) (S := S)
      (hS_dvd := hS_dvd)
      (hS_gap := hS_gap)
      (hwnz_core := hwnz_core)
      (hfactor_core0 := hfactor_core0)
```

最小テンプレート（boundaryCore factor0 → 停留点存在）:

```lean
import DkMath.RH.CFBRCBridge

open DkMath.RH.EulerZeta

example (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with | .right => ¬ d ∣ x | .left => ¬ d ∣ u)
    (hS_dvd :
      ∀ r ∈ S, r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hS_gap :
      ∀ r ∈ S, (match side with | .right => ¬ r.1 ∣ x | .left => ¬ r.1 ∣ u))
    (hwnz_core :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_core0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.stationaryAt
        (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t := by
  exact
    exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_factor0
      (side := side) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
      hd_prime hd_ge hx hu hcop hpnd hS_dvd hS_gap hwnz_core hfactor_core0
```

最小テンプレート（boundaryCore local0 → 停留点存在）:

```lean
import DkMath.RH.CFBRCBridge

open DkMath.RH.EulerZeta

example (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with | .right => ¬ d ∣ x | .left => ¬ d ∣ u)
    (hS_dvd :
      ∀ r ∈ S, r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hS_gap :
      ∀ r ∈ S, (match side with | .right => ¬ r.1 ∣ x | .left => ¬ r.1 ∣ u))
    (hwnz_core :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hlocal_core :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          hopcPrimeLocalContribution p.1 σ t = 0) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.stationaryAt
        (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t := by
  exact
    exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_local0
      (side := side) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
      hd_prime hd_ge hx hu hcop hpnd hS_dvd hS_gap hwnz_core hlocal_core
```

最小テンプレート（boundaryDiffPow local0 → 停留点存在）:

```lean
import DkMath.RH.CFBRCBridge

open DkMath.RH.EulerZeta

example (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with | .right => ¬ d ∣ x | .left => ¬ d ∣ u)
    (hS_dvd :
      ∀ r ∈ S, r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hS_gap :
      ∀ r ∈ S, (match side with | .right => ¬ r.1 ∣ x | .left => ¬ r.1 ∣ u))
    (hwnz_core :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hlocal_diff0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          hopcPrimeLocalContribution p.1 σ t = 0) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.stationaryAt
        (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t := by
  exact
    exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_local0
      (side := side) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
      hd_prime hd_ge hx hu hcop hpnd hS_dvd hS_gap hwnz_core hlocal_diff0
```

### Bridge Usage (RH-J2/J3)

`DkMath.RH.CFBRCBridge` には、CFBRC primitive-prime existence から
RH 側 singleton 停留判定へ落とす補題が 2 系統ある。

- global 仮定版（J2）:
  - `exists_stationaryAt_singleton_of_cfbRc_primitive_prime_bridge`
  - 翻訳仮定として `hopcPrimeContributionSum ({p}) = 0` を要求
- local 仮定版（J3）:
  - `exists_stationaryAt_singleton_of_cfbRc_primitive_prime_bridge_of_local`
  - 翻訳仮定として `hopcPrimeLocalContribution p = 0` を要求

使い分けの目安:

- 既に RH 側で sum 形式に統一している場合は global 仮定版
- 素数ごとの局所評価を直接供給したい場合は local 仮定版

最小 import:

```lean
import DkMath.RH.CFBRCBridge
```

利用イメージ（local 仮定版）:

```lean
open DkMath.RH.EulerZeta

-- hq_dvd / hq_not_dvd_x が CFBRC 側から供給される想定
have hlocal0 : hopcPrimeLocalContribution q σ t = 0 := by
  -- provider 側で供給
  sorry

-- 結果は singleton 観測器の stationaryAt
have hstat :
    DkMath.RH.stationaryAt
      (fun v : ℝ => eulerZetaFinite_onVertical ({⟨q, hqP⟩} : Finset {r // Nat.Prime r}) σ v) t := by
  -- `..._of_local` で導出
  sorry
```
