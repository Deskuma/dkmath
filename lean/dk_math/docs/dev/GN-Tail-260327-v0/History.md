# History of G Tail

## Log

### 日時: 2026/03/26 15:48 JST

1. 目的:
   - `!!実装可能定理候補-260327.md`
     のうち、
     `GTail`
     に関する補題候補を読んで、
     既存の
     `DkMath.CosmicFormula.GTail`
     API と突き合わせ、
     実装順を決める。
2. 実施:
   - 候補文書を確認し、
     `GTail`
     まわりの主候補として
     - `padicValNat_tail_exact_of_head_unit`
     - `higher_tail_eq_pow_mul_Gbinom`
     - `pow_dvd_higher_tail`
     - `Gbinom_tail_rec`
     - `Gbinom_zero_eval`
     が挙がっていることを整理した。
   - 現行
     `[DkMath/CosmicFormula/GTail.lean]`
     を確認し、
     既に
     - `add_pow_eq_prefix_add_xpow_mul_GTail`
     - `GTail_zero_eq_add_pow`
     - `GTail_self_eq_one`
     - `GTail_rec`
     - `GTail_one_eq_sum`
     - `GTail_eval_zero`
     が実装済みであることを確認した。
   - これに基づき、
     候補のうち
     valuation 本体よりも先に、
     naming / bridge / divisibility
     を固めるのが自然だと判定した。
3. 結論:
   - 直ちに実装すべきなのは次の順である。
     1. `higher_tail_eq_pow_mul_GTail`
        または同等の alias：
        既存
        `add_pow_eq_prefix_add_xpow_mul_GTail`
        を
        「差 = x^r * GTail」
        の形で読める theorem 名へ固定する。
     2. `Gbinom_tail_rec` / `Gbinom_zero_eval` に相当する migration alias：
        既存
        `GTail_rec`
        / `GTail_eval_zero`
        を候補文書の語彙へ接続する。
     3. `pow_dvd_higher_tail`：
        valuation の前段として、
        高次 Tail が境界因子
        `x^r`
        を持つことを
        `Nat` または可除性のある代数設定で定理化する。
   - `padicValNat_tail_exact_of_head_unit`
     はその後段である。
     これは lower bound は上の境界因子定理から出るが、
     upper bound には
     `q ∤` 先頭項や
     mod / valuation
     条件の設計が要るため、
     まず exactness の土台を先に固定すべきである。
4. 検証:
   - 読解・設計段階のため、まだ追加 build は回していない。
5. 失敗事例:
   - いきなり
     `padicValNat_tail_exact_of_head_unit`
     から入ると、
     algebraic setting
     (`CommSemiring` / `Nat` / `Int`)
     と
     exactness 仮定の置き方が未整理で、
     API がぶれやすい。
6. 備考:
   - 候補文書の
     `higher_tail_eq_pow_mul_Gbinom`
     は、
     現行 naming に合わせるなら
     `..._GTail`
     へ寄せる方が自然である。
   - ただし
     `r = 1`
     で既存
     `GN`
     / `Gbinom`
     に落ちる alias は、
     移行上は有益である。
7. 次の課題:
   - `GTail.lean`
     に
     1. boundary-factor theorem alias
     2. recursion / zero-eval alias
     3. 可除性の lower-bound 補題
     を追加する。
   - その後で
     `padicValNat_tail_exact_of_head_unit`
     の statement を
     `Nat`
     ベースで切るか、
     より抽象な setting にするかを決める。

### 日時: 2026/03/27 01:12 JST

1. 目的:
   - `GTail`
     の valuation 前段 API を固めるため、
     計画した
     1. boundary-factor theorem alias
     2. recursion / zero-eval migration alias
     3. 可除性 lower-bound
     を実装する。

2. 実施:
   - `[lean/dk_math/DkMath/CosmicFormula/GTail.lean]`
     に
     - `higher_tail_eq_pow_mul_GTail`
     - `Gbinom_tail_rec`
     - `Gbinom_zero_eval`
     - `pow_dvd_higher_tail`
     を追加した。
   - `higher_tail_eq_pow_mul_GTail`
     は既存
     `add_pow_eq_prefix_add_xpow_mul_GTail`
     の subtraction-shaped alias
     として
     `CommRing`
     上で実装した。
   - `Gbinom_tail_rec`
     / `Gbinom_zero_eval`
     は naming migration alias
     として、
     それぞれ
     `GTail_rec`
     / `GTail_eval_zero`
     に直接接続した。
   - `pow_dvd_higher_tail`
     は
     `Nat`
     上で
     `congrArg (fun t => t - prefix)`
     を使って導出し、
     高次 Tail が境界因子
     `x^r`
     を持つことを
     `∣`
     の形で固定した。

3. 結論:
   - valuation 本体に入る前段として必要だった
     `higher tail = x^r * GTail`
     の name-stable theorem と、
     recursion / zero-eval / divisibility
     の 3 本柱が揃った。
   - これで
     `padicValNat_tail_exact_of_head_unit`
     は、
     まず
     `pow_dvd_higher_tail`
     から lower bound を取り、
     その上で upper bound を設計する流れに整理できる。

4. 検証:
   - `lake build DkMath.CosmicFormula.GTail`
   - `lake build DkMath.CosmicFormula.CosmicFormulaBinom`
   を実行し、成功を確認した。

5. 失敗事例:
   - `pow_dvd_higher_tail`
     の初稿では、
     `ℕ`
     上の prefix 局所略記と
     cast / parser
     の組合せで証明が不安定だった。
   - 最終的には
     `congrArg (fun t => t - prefix)`
     を直接使う形へ直し、
     proof-local abbreviation
     に依存しない形へ落ち着いた。

6. 備考:
   - `higher_tail_eq_pow_mul_GTail`
     は
     `CommRing`
     版、
     `pow_dvd_higher_tail`
     は
     `Nat`
     版であり、
     algebraic layer と divisibility layer を分ける形になっている。

7. 次の課題:
   - `padicValNat_tail_exact_of_head_unit`
     の statement を具体化する。
   - その際、
     upper bound 側の head-unit 仮定を
     `q ∤ (choose d r * u^(d-r))`
     のような形で置くか、
     より扱いやすい派生仮定に分解するかを決める。

### 日時: 2026/03/27 01:31 JST

1. 目的:
   - `GTail`
     の valuation 層を先へ進め、
     `padicValNat_tail_exact_of_head_unit`
     を実際に statement / proof として固定する。

2. 実施:
   - `[lean/dk_math/DkMath/CosmicFormula/GTail.lean]`
     に
     - `GTail_not_dvd_of_head_unit_of_prime_dvd_x`
     - `padicValNat_GTail_eq_zero_of_head_unit_of_prime_dvd_x`
     - `padicValNat_higher_tail_lower_bound`
     - `padicValNat_tail_exact_of_head_unit`
     を追加した。
   - `GTail_rec`
     を使って、
     先頭項
     `choose d r * u^(d-r)`
     が
     `p`-adic unit
     であり、
     かつ
     `p ∣ x`
     なら、
     normalized tail
     `GTail d r x u`
     は
     `p`
     で割れないことを示した。
   - そこから
     normalized tail の valuation が
     `0`
     であることを出し、
     boundary factor
     `x^r`
     の valuation と掛け合わせることで、
     full tail の exact valuation
     を閉じた。

3. 結論:
   - 候補文書にあった
     `padicValNat_tail_exact_of_head_unit`
     は、
     いまの
     `GTail`
     API から自然に実装できる形へ落ちた。
   - statement は
     `Nat`
     上で、
     - `r < d`
     - tail 自体が非零
     - `¬ p ∣ choose d r * u^(d-r)`
     - `p ∣ x`
     を仮定し、
     \[
       v_p(\text{higher tail}) = r\,v_p(x)
     \]
     を返すものとして固定された。
   - これで
     higher-tail theory
     は、
     定義 / 再帰 / 評価 / 可除性 / exact valuation
     まで一通り揃った。

4. 検証:
   - `lake build DkMath.CosmicFormula.GTail`
   - `lake build DkMath.CosmicFormula.CosmicFormulaBinom`
   を実行し、成功を確認した。

5. 失敗事例:
   - 初稿では
     `Nat.dvd_add_right`
     の向きと、
     `padicValNat.mul`
     が要求する
     `[Fact (Nat.Prime p)]`
     の供給で詰まった。
   - 最終的には
     `Nat.add_comm`
     を挟んで和の向きを揃え、
     exactness proof 内に
     `letI : Fact (Nat.Prime p) := ⟨hp⟩`
     を入れることで解決した。

6. 備考:
   - lower bound は
     `pow_dvd_higher_tail`
     と
     `DkMath.ABC.padicValNat_le_iff_dvd`
     の合成で得ている。
   - exactness の upper bound は、
     normalized tail 側 valuation を
     `0`
     に落とすことで実装したので、
     今回の theorem はかなり reusable である。

7. 次の課題:
   - `r = 1`
     specialization を
     `GN`
     / `Gbinom`
     の語彙へ落とす alias を追加するか検討する。
   - `squarefree GN`
     や primitive-prime route
     との接続で、
     この exact valuation theorem をどこへ流し込むかを決める。

### 日時: 2026/03/27 01:43 JST

1. 目的:
   - `r = 1`
     specialization では
     `Gbinom`
     ではなく
     `GN`
     を主軸命名にする。

2. 実施:
   - `[lean/dk_math/DkMath/CosmicFormula/GTail.lean]`
     に
     - `GN_tail_rec`
     - `GN_zero_eval`
     - `GN_not_dvd_of_head_unit_of_prime_dvd_x`
     - `padicValNat_GN_eq_zero_of_head_unit_of_prime_dvd_x`
     - `padicValNat_GN_exact_of_head_unit`
     を追加した。
   - 既存の
     `Gbinom_tail_rec`
     / `Gbinom_zero_eval`
     は compatibility alias
     とし、
     docstring でも
     `GN`
     を優先する旨を明記した。
   - `GTail_not_dvd_of_head_unit_of_prime_dvd_x`
     内の一般
     `r`
     参照は
     `GTail_rec`
     に戻し、
     `GN`
     alias は純粋に
     `r = 1`
     specialization として分離した。

3. 結論:
   - `GTail`
     理論の
     `r = 1`
     側は、
     名実ともに
     `GN`
     語彙で読む形に整理された。
   - 以後は
     `GN`
     を prefix / suffix に使う方針で進められる。
   - `Gbinom`
     は
     `CellDim`
     ローカルの対比名として残しても、
     valuation / tail
     理論の主軸名ではなくなった。

4. 検証:
   - `lake build DkMath.CosmicFormula.GTail`
   - `lake build DkMath.CosmicFormula.CosmicFormulaBinom`
   を実行し、成功を確認した。

5. 備考:
   - `padicValNat_GN_exact_of_head_unit`
     は
     `padicValNat_tail_exact_of_head_unit`
     の
     `r = 1`
     specialization を
     `(x+u)^d - u^d`
     の形へ戻した alias
     である。

6. 次の課題:
   - `GN`
     alias 群を
     `CosmicFormulaBinom`
     / `CellDim`
     の
     `GN`
     語彙へどこまで露出するかを決める。
   - `squarefree GN`
     や primitive-prime route
     と結ぶ theorem の statement へ、
     この
     `GN`
     exact valuation を直接組み込む。

### 日時: 2026/03/27 JST

1. 目的:
   - review-003 に沿って、
     `squarefree GN`
     から Body 差分の非完全冪性を直接返す
     `body_not_perfect_pow_of_squarefree_GN`
     を実装する。
   - 依存の向きを守るため、
     `CosmicFormula`
     層から
     `NumberTheory.ZsigmondyCyclotomicSquarefree`
     へは上げずに閉じる。

2. 実施:
   - `[lean/dk_math/DkMath/CosmicFormula/CosmicFormulaBinom.lean]`
     に private helper
     `padicValNat_eq_one_of_prime_dvd_of_squarefree`
     を追加した。
     これは
     `Squarefree n`
     と
     `p ∣ n`
     から
     `padicValNat p n = 1`
     を返す局所 valuation 補題である。
   - 同ファイルに
     `body_not_perfect_pow_of_squarefree_GN`
     を追加した。
     仮定は
     - `1 < d`
     - `1 < GN d x u`
     - `Nat.Coprime x (GN d x u)`
     - `Squarefree (GN d x u)`
     で、
     結論は
     `¬ ∃ t, 0 < t ∧ (x + u)^d - u^d = t^d`
     である。

3. 結論:
   - `squarefree GN`
     から prime divisor `q`
     を 1 本取り、
     coprime 仮定で
     `q ∤ x`
     を確保し、
     `v_q(GN)=1`
     を使って
     `v_q((x+u)^d-u^d)=1`
     を示す
     direct obstruction theorem
     が
     `CosmicFormula`
     層に立った。
   - これにより
     `GN`
     理論の exact valuation と
     `squarefree`
     route の統合が、
     `NumberTheory`
     依存なしに 1 本の theorem 名で読めるようになった。

4. 検証:
   - `lake build DkMath.CosmicFormula.GTail`
   - `lake build DkMath.CosmicFormula.CosmicFormulaBinom`
   を実行し、成功を確認した。

5. 備考:
   - 今回の定理は
     `padicValNat_GN_exact_of_head_unit`
     を直接使う形ではなく、
     `Body = x * GN`
     の factorization と
     `squarefree`
     valuation を正面から組み合わせる route を採った。
   - これは
     `p ∣ x`
     を仮定する head-unit exactness とは別の、
     `q ∣ GN` / `q ∤ x`
     側の obstruction として整理できる。

6. 次の課題:
   - `body_not_perfect_pow_of_squarefree_GN`
     の仮定
     `Nat.Coprime x (GN d x u)`
     を、
     既存の
     `Nat.Coprime (x + u) u`
     などから供給する薄い wrapper
     を整備する。
   - primitive-prime route
     `body_not_perfect_pow_of_primitive_prime_factor`
     を同じ naming layer で切る。

### 日時: 2026/03/27 JST

1. 目的:
   - review-004 の方針に沿って、
     `body_not_perfect_pow_of_squarefree_GN`
     の仮定
     `Nat.Coprime x (GN d x u)`
     を、
     より上流の coprime data から供給する wrapper を追加する。

2. 実施:
   - `[lean/dk_math/DkMath/NumberTheory/Gcd/GN.lean]`
     に
     `coprime_boundary_GN_of_coprime_add_of_coprime_exp`
     を追加した。
     仮定は
     - `1 ≤ d`
     - `0 < x`
     - `Nat.Coprime (x + u) u`
     - `Nat.Coprime x d`
     で、
     結論は
     `Nat.Coprime x (GN d x u)`
     である。
   - 同ファイルに
     `body_not_perfect_pow_of_squarefree_GN_of_coprime_add`
     を追加し、
     上記 coprime wrapper を経由して
     `CosmicFormulaBinom.body_not_perfect_pow_of_squarefree_GN`
     を起動する形へ整理した。

3. 結論:
   - `squarefree GN`
     obstruction は、
     もはや
     `Nat.Coprime x (GN d x u)`
     を手で渡す theorem
     ではなく、
     `Body` 座標
     `Nat.Coprime (x + u) u`
     と
     `Nat.Coprime x d`
     から起動できる二層構成になった。
   - 責務分離としては
     - `CosmicFormulaBinom`:
       pure obstruction
     - `NumberTheory.Gcd.GN`:
       coprime supply / wrapper
     の分割がかなり自然になった。

4. 検証:
   - `lake build DkMath.CosmicFormula.CosmicFormulaBinom`
   - `lake build DkMath.NumberTheory.Gcd.GN`
   を実行し、成功を確認した。

5. 備考:
   - 今回の coprime wrapper は
     `gcd_gap_GN_dvd_exp`
     から
     `gcd(x,GN) ∣ d`
     を読み直し、
     さらに
     `Nat.Coprime x d`
     で
     `gcd(x,GN)=1`
     へ落とす形で閉じている。
   - したがって
     `UniqueFactorizationGN`
     の heavier valuation layer を import せずに済んだ。

6. 次の課題:
   - `body_not_perfect_pow_of_primitive_prime_factor`
     を、今回の squarefree route と同じ naming layer
     / wrapper 分割で追加する。
   - 必要なら
     `Nat.Coprime x u`
     版の wrapper も薄く切り、
     `Nat.Coprime (x + u) u`
     と
     `Nat.Coprime x u`
     の両語彙で呼べるようにする。

### 日時: 2026/03/27 JST

1. 目的:
   - review-005 の方針に沿って、
     primitive-prime route を
     squarefree route と同じ
     「pure obstruction / wrapper」
     の二層構成へ揃える。

2. 実施:
   - `[lean/dk_math/DkMath/NumberTheory/PrimitiveBeam.lean]`
     に
     `primitive_prime_factor_forbids_perfect_pow_diff`
     を追加した。
     これは
     primitive prime existence と
     primitive-prime valuation 上界から、
     `a^d - b^d = t^d`
     を直接矛盾させる pure obstruction theorem である。
   - `[lean/dk_math/DkMath/NumberTheory/Gcd/GN.lean]`
     に
     `body_not_perfect_pow_of_primitive_prime_factor_of_coprime_add`
     を追加した。
     これは
     `a := x + u`, `b := u`
     specialization により、
     `Body` 座標の coprime data から primitive-prime obstruction を起動する wrapper である。

3. 結論:
   - `GN` 理論の obstruction 層は、
     - squarefree route
     - primitive-prime route
     の 2 本で、ほぼ対称な構造を持つようになった。
   - 役割分離は
     - `PrimitiveBeam`: pure primitive obstruction
     - `Gcd.GN`: Body 座標 wrapper
     という形で整理された。

4. 検証:
   - `lake build DkMath.NumberTheory.PrimitiveBeam`
   - `lake build DkMath.NumberTheory.Gcd.GN`
   を実行し、成功を確認した。

5. 備考:
   - `PrimitiveBeam`
     は既に research valuation wrapper を import しているため、
     今回の pure obstruction はこの層に置くのが自然だった。
   - `Gcd.GN`
     側では、
     primitive prime existence の条件供給だけを担当し、
     obstruction 本体は再実装していない。

6. 次の課題:
   - `Nat.Coprime x u`
     版の薄い wrapper を追加し、
     `Nat.Coprime (x + u) u`
     へ自動で流す。
   - 必要なら
     squarefree route / primitive-prime route
     をまとめる共通 naming layer
     （`..._of_coprime_gap` 系）
     を整える。

### 日時: 2026/03/27 JST

1. 目的:
   - いま追加した obstruction theorem 群が
     「FLT そのものではないが、既に FLT 型の局所 refuter である」
     ことを、忘れないうちにコードコメントと履歴へ明記する。

2. 実施:
   - `[lean/dk_math/DkMath/CosmicFormula/CosmicFormulaBinom.lean]`
     の
     `body_not_perfect_pow_of_squarefree_GN`
     docstring に、
     `CosmicFormula`
     層に置かれた
     FLT-shaped theorem
     である旨を追記した。
   - `[lean/dk_math/DkMath/NumberTheory/PrimitiveBeam.lean]`
     の
     `primitive_prime_factor_forbids_perfect_pow_diff`
     docstring に、
     lower layer に置かれた
     FLT-shaped obstruction
     だと明記した。
   - `[lean/dk_math/DkMath/NumberTheory/Gcd/GN.lean]`
     の
     `body_not_perfect_pow_of_squarefree_GN_of_coprime_add`
     と
     `body_not_perfect_pow_of_primitive_prime_factor_of_coprime_add`
     docstring にも、
     `Body` 座標での
     FLT-shaped local refuter
     だと注記した。

3. 結論:
   - いまの obstruction 群は、
     数学的にも実装上も
     「FLT 本体ではないが、
      既に FLT branch を折る型の theorem」
     であることが記録された。
   - 後続で
     `FLT.Basic`
     や provider 層へ接続するとき、
     これらを
     local refuter
     として扱う判断がしやすくなった。

4. 検証:
   - 今回は docstring / 履歴更新のみ。
   - 前段で確認済みの build 成功状態を維持している前提で記録した。

5. 次の課題:
   - `Nat.Coprime x u`
     版 wrapper を追加し、
     FLT 側が使う典型仮定から
     これらの local refuter をさらに起動しやすくする。

### 日時: 2026/03/27 JST

1. 目的:
   - `DkMath.FLT.Basic`
     側でも、
     いま追加した
     FLT-shaped local refuter
     をどこへ差し込むかを明示し、
     後続で research route から切り替える位置を
     迷わないようにする。

2. 実施:
   - `[lean/dk_math/DkMath/FLT/Basic.lean]`
     の
     `body_not_perfect_pow_bridge`
     直前に、
     - `body_not_perfect_pow_of_squarefree_GN_bridge`
     - `body_not_perfect_pow_of_primitive_prime_factor_bridge`
     を追加した。
   - どちらも
     `DkMath.NumberTheory.Gcd.GN`
     側の
     FLT-shaped local refuter
     を、
     `FLT.Basic`
     が持つ
     `u,y,n`
     語彙へ移しただけの thin bridge である。
   - あわせて
     `FLT_of_coprime`
     の
     `n > 3` prime / `¬ n ∣ u`
     branch に注記を入れ、
     現在の mainline はまだ research route だが、
     non-research の差し込み候補は
     直上の 2 bridge だと明記した。

3. 結論:
   - `FLT.Basic`
     から見ても、
     squarefree route / primitive-prime route
     を差し込む位置が code level で固定された。
   - まだ mainline の呼び先自体は
     `GcdNext.body_not_perfect_pow`
     のままだが、
     これは「橋が無いから」ではなく、
     `squarefree` や primitive-prime existence
     を供給する最後の薄い配線が未実装なだけ、
     という状態になった。

4. 検証:
   - `lake build DkMath.FLT.Basic`
   を実行して、成功を確認する。

5. 次の課題:
   - `FLT_of_coprime`
     の
     `n > 3` / prime / `¬ n ∣ u`
     branch へ、
     `squarefree`
     あるいは primitive-prime existence
     を供給する薄い wrapper を追加する。
   - そのとき、
     current research route を
     完全に置き換えるのか、
     fallback として残すのかを決める。

### 日時: 2026/03/27 JST

1. 目的:
   - `FLT`
     方針へ舵を切り、
     残核 2 本
     （composite reduction / Branch A）
     のうち、
     何が軽く、
     何が本命の新補題かを固定する。

2. 実施:
   - `review-007`
     の分析と現行 workspace を突き合わせ、
     以下を確認した。
     - composite reduction は標準的な指数縮約であり、
       Lean 整備の問題である。
     - Branch A は comparison route の続きを掘る段階ではなく、
       既存
       `TriominoWieferichBranchBridge`
       / no-Wieferich machinery
       への出口を作る段階である。
   - 特に
     `TriominoCosmicBranchA`
     には既に
     - `z - y = p^(p-1) * t^p`
     - `GN p (z - y) y = p * s^p`
     - `Nat.Coprime t s`
     - `p ∤ y`, `GN ⟂ y`
     が揃っており、
     Branch A normal form は
     Wieferich witness
     を抜く入口として十分育っていることを確認した。

3. 結論:
   - composite reduction は先に機械的に閉じてよい。
   - Branch A の本命は
     `False`
     直出しではなく、
     まず
     `u = p^(p-1) * t^p`, `GN = p * s^p`
     から
     `s^p ≡ y^(p-1) [MOD p^2]`
     を抜く補題である。
   - その後に
     `y^(p-1) ≡ 1 [MOD p^2]`
     型の Wieferich witness へ上げ、
     既存 bridge へ接続するのが mainline となる。

4. 実装計画:
   - まず composite reduction を閉じる。
   - 並行して Branch A 側では次の補題列を狙う。
     1. `branchA_GN_shape_expansion_mod_p3`
     2. `branchA_shape_implies_spow_congr`
     3. `branchA_shape_implies_wieferich_y`
   - ここで
     `branchA_shape_implies_spow_congr`
     が最初の実装本命である。

5. 備考:
   - 現段階は
     「新理論をゼロから作る」
     のではなく、
     「既存の枝を正しい出口へ差し替える」
     フェーズに入ったと評価してよい。

### 日時: 2026/03/27 JST

1. 目的:
   - `FLT.Basic`
     の残核のうち、
     まず軽い側である
     composite exponent reduction
     を閉じる。

2. 実施:
   - `[lean/dk_math/DkMath/FLT/Basic.lean]`
     に
     `DkMath.FLT.MathlibBridge.FLT34`
     を import した。
   - prime exponent case を
     `flt_of_coprime_prime_exponent`
     として private helper に切り出した。
     これにより、
     original prime branch と
     composite reduction の両方が
     同じ prime-exponent 入口を共有する形になった。
   - composite residual には
     `exists_prime_dvd_of_composite_not_four_dvd`
     を追加し、
     `4 ∣ n`
     の場合は
     `FLT4_core`
     で閉じ、
     それ以外は
     `p ≠ 2`
     な prime divisor
     `p`
     と
     `n = m * p`
     を取り出して
     `X := x^m`, `Y := y^m`, `Z := z^m`
     に縮約し、
     `flt_of_coprime_prime_exponent`
     へ戻す形で実装した。

3. 結論:
   - `FLT.Basic`
     の composite residual は
     `no sorry`
     で閉じた。
   - これにより
     `FLT.Basic`
     の残核は、
     実質的に
     Branch A / Wieferich route
     だけへ絞られた。

4. 検証:
   - `lake build DkMath.FLT.Basic`
   を実行し、成功を確認した。

5. 次の課題:
   - `TriominoCosmicBranchA`
     の最終残核を、
     comparison route
     ではなく
     Wieferich witness route
     へ差し替える。
   - 最初の本命補題は、
     Branch A normal form から
     `s^p ≡ y^(p-1) [MOD p^2]`
     を抜くものである。

### 日時: 2026/03/27 JST

1. 目的:
   - Branch A / Wieferich route の最初の concrete 材料を、
     `TriominoCosmicBranchA`
     lower layer に固定する。
   - comparison の残核をすぐには閉じず、
     まず
     `GN = p * y^(p-1) + p^2 * M`
     と
     `s^p = y^(p-1) + p * M`
     の shape を theorem 化する。

2. 実施:
   - `[lean/dk_math/DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean]`
     に
     - `primeGe5BranchA_GN_eq_head_add_p_sq_mul`
     - `primeGe5BranchA_spow_eq_head_add_p_mul`
     を追加した。
   - 前者では、
     既存の local proof に埋まっていた
     `N = A + B`
     と
     `p^2 ∣ B`
     を独立 theorem として再構成し、
     `GN`
     の head/tail 分離を explicit にした。
   - 後者では、
     `GN = p * s^p`
     と上の head/tail 分離を合わせて、
     `p`
     を一度割った normal form
     `s^p = y^(p-1) + p * M`
     を concrete に取り出した。

3. 結論:
   - Branch A は、
     comparison route の checkpoint だけでなく、
     Wieferich route の最初の合同材料を
     lower layer で直接持つ状態になった。
   - これにより次の本命は、
     `s^p = y^(p-1) + p * M`
     から
     `mod p^2`
     の witness へ持ち上げる補題に絞られた。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
   - `lake build DkMath.FLT.Basic`
   を実行し、成功を確認した。

5. 備考:
   - `TriominoCosmicBranchA.lean`
     の既存 `sorry`
     は増えていない。
   - 今回の 2 補題は、
     最終 refuter を comparison から Wieferich bridge へ差し替える際の
     concrete adapter 候補になる。

6. 次の課題:
   - `primeGe5BranchA_spow_eq_head_add_p_mul`
     を
     `s^p ≡ y^(p-1) [MOD p]`
     あるいは
     `mod p^2`
     の形へ正規化する補題を追加する。
   - そのうえで
     `TriominoCosmicGapInvariant`
     側の Wieferich bridge に渡す input spec を定める。

### 日時: 2026/03/27 JST

1. 目的:
   - Branch A の gap-shape
     `z - y = p^(p-1) * t^p`
     を明示的に使い、
     `GN`
     の tail を
     `p^3`
     まで押し上げる。
   - その結果として、
     `s^p`
     側に
     `p^2`
     tail を持つ concrete equality version を固定する。

2. 実施:
   - `[lean/dk_math/DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean]`
     に
     - `primeGe5BranchA_GN_eq_head_add_p_cube_mul`
     - `primeGe5BranchA_spow_eq_head_add_p_sq_mul`
     を追加した。
   - 前者では、
     `hgap`
     から
     `p^3 ∣ (z - y)`
     を取り、
     `GN`
     の tail sum の各項に
     `p^3`
     が入ることを示した。
   - 後者では、
     `GN = p * s^p`
     と上の展開を合わせて、
     `p`
     を 1 回キャンセルし、
     `s^p = y^(p-1) + p^2 * M`
     を得た。

3. 結論:
   - Branch A / Wieferich route の first milestone だった
     `s^p ≡ y^(p-1) [MOD p^2]`
     は、
     すでに concrete equality
     `s^p = y^(p-1) + p^2 * M`
     の形で lower layer に入った。
   - 次段では、
     これを
     `Nat.ModEq`
     か Wieferich witness 仕様へ薄く包むだけでよい。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
   - `lake build DkMath.FLT.Basic`
   を実行し、成功を確認した。

5. 備考:
   - `TriominoCosmicBranchA.lean`
     の active `sorry`
     は引き続き final kernel
     1 箇所だけで、今回増えていない。
   - comparison route の残骸を増やさずに、
     Wieferich route 向けの材料だけを先に theorem 化できた。

6. 次の課題:
   - `primeGe5BranchA_spow_eq_head_add_p_sq_mul`
     を
     `Nat.ModEq (p^2) (s^p) (y^(p-1))`
     に直す thin wrapper を追加する。
   - そのうえで、
     `TriominoCosmicGapInvariant`
     の Wieferich bridge が要求する witness 形式へ
     どこまで直接合わせられるかを調べる。
