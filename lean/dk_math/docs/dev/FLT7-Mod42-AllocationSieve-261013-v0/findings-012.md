# findings-012 — generic prime-power primitive allocation

instruction-012 と gate011の構造証明、actual full-sieve fields、両existing exclusion consumerを確認。新しい対象名の実ソース検索で既存同名結果なし。

Prime13をprime pへ分離し、quotient tへのactual coprimalityを使うEuclid proofを一般化する。n=0も含む。Residue conditionsは別のgeneric theoremの仮定として保持し、全p/nの合同式とは主張しない。既存gate011 sourceは改変しない。

Initial focused build failed: mechanical specialization shadowed the prime hypothesis with the divisibility branch variable; generic multiplication simplification also failed to preserve the local quotient form. Renamed the branch hypothesis and used explicit r*t product inequalities. No mathematical premise was changed.

Second build still failed in the t-divisibility witness because simp commuted the numerator under division without unfolding the local t. Replaced that simp with the exact hprod.symm.trans (Nat.mul_comm r t) equality.

Final production build succeeded. Initial test exit1: deciding primality223 directly reached maxRecDepth. Changed that prime certificate to norm_num without increasing resource limits; residue comparisons remain kernel-checked exact arithmetic.

## Final outcome

Outcome A。Final focused build /test exits0。Both exports have only standard three axioms, no sorryAx. Index refreshed:1,813files /29,292declarations.

Generic structure works for all prime p and n including0, no upper cutoff. Residue-conditional theorem recovers old13 family; independent223,n2 example gives99458 exclusion with real r2 eligibility. Composite3*5^10 diagnostic shows remaining frontier for multiple prime bases; no exact witness inferred. Existing files unchanged, no Git mutation.
