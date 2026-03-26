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
