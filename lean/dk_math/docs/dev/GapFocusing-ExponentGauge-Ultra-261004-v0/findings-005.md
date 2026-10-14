# Instruction 005 findings

## Source audit checkpoint

Baseline is Instruction 004 at commit c0b5be05f. The current checkout starts clean. The required production sources and definitions have been read. The exact type inventory is recorded with `LegendreFreshCostInventory.lean`.

At a lower successor seat let K be actual active-support cardinality, P persistent cardinality and F fresh cardinality. The existing split gives K=P+F. The existing local support-excess cost is K-1 and pair overlap is choose(K,2). Residual pair mass is choose(K-1,2). Collision seats have K>=4, fifth-direction collision has K>=5. Low-cost capacity bounds the near/depth/fourth residual branches, not every fresh prime.

A zero-cost fresh singleton has K=F=1 and P=0. A whole multi-support fresh seat is not zero cost. Its first slot can still be uncharged if P=0, with the remaining F-1 charged. If P>0, all F fresh directions are added excess. The proposed exact incremental charge is F minus one only when P=0 and F>0. It should equal (K-1)-(P-1), avoiding arbitrary attribution to a named prime.

The prime support API already exists as Mathlib `Nat.primeFactors`. No separate omega function is needed. `Internal.upperPairs` already supplies unordered-pair representatives and their choose cardinality; reuse it if an actual fresh-pair partition is added.

Arithmetic diagnostics (not yet proof): the main block appears to have 94 singleton-fresh seats, exceeding 76. Additional finite blocks will be checked only if they expose a positive existing-ledger charge. No asymptotic claim follows from these diagnostic calculations.

## Local decomposition checkpoint

The focused cost module build passes. Local active support cardinality equals P+F. Its support excess splits exactly as `(K-1)=(P-1)+freshCharge`, where `freshCharge=F-(if P=0 then 1 else 0)`. Fresh count is exactly singleton-fresh seat count plus multi-support fresh incidence count. Multi-support fresh incidence is at most twice existing support excess. An alternative exact split is fresh count = fresh-without-persistent seat count + incremental excess charge; the charge is bounded by existing support excess with coefficient one. Singleton fresh support has zero charge and cannot be a collision seat.

Fresh-involving pairs reuse the existing `Internal.upperPairs`. Active pair mass splits into persistent-only pair mass plus fresh-involving mass. Its exact local fresh contribution is `P*F + choose(F,2)`. This mass is contained in existing pair overlap, and its outside-collision restriction is contained in the existing outside-collision pair mass. It is not automatically a residual pair or depth collision.

## Fixed-seat arithmetic and parity checkpoint

Persistent support is a subset of the existing `(4*r+1).primeFactors`. Its cardinality is bounded by that support's cardinality. The same candidate offset is tracked only inside the canonical lower sector.

A further genuine restriction is now checked: lower successor candidates require `n ≡ r (mod 2)`. The odd prime shell address together with this condition gives period `2*q` at a fixed seat, by CRT. Quotient blocks bound the candidate address frequency by ceil(T/(2*q)). Transposing the persistent-incidence sum over seats yields a new parity-retaining cap C2, uniformly no larger than the old Instruction 004 cap C1.

## Main finite calibration checkpoint

The regression module has checked exact counts for N=20,T=20: singleton-fresh capacity 94, fresh-only mandatory-first-slot capacity 110, lower candidate demand 245, old persistence cap 169, and new parity-retaining persistence cap 97. Thus the original lower bound 76 alone cannot beat the zero-cost singleton capacity. The strengthened persistence cap forces fresh >=148 under the same existing simultaneous full-cover hypothesis. Subtracting the exact first-slot capacity forces existing support excess >=38. This yields an additional +38 left-side charge in the existing summed full-cover candidate/incidence balance.

The result remains conditional on existing full cover of successor shells 21 through 40. No full-cover provider or Legendre proof is supplied. The exact-depth collision, outside-collision and low-cost residual capacities are not assigned a 38-unit charge: the proved recipient is support excess. A checked two-direction example has fresh pair mass one and local residual mass zero.

## Frontier decision checkpoint

Outcome A is supported in its bounded support-excess sense: an existing temporal capacity is strictly improved (169 to 97), and its finite fresh demand now forces a positive existing-ledger cost (38) and a checked positive left-side charge in the existing full-cover balance. No claim of analytic, asymptotic or universal full-cover contradiction follows.

## Final validation checkpoint

The final focused changed/new modules, fifteen named regression/normalization declarations, Legendre facade, and DkMath build pass (10370 Lake jobs, including replayed dependencies). New source and regression warnings are zero. The full build replays five pre-existing unfinished research declaration warnings; every new proof's actual dependencies have been checked separately. New public production coverage is 46/46, regression coverage 15/15, with dependency sets contained in the three accepted standard axioms. Forbidden-token scans on changed production and regression files are clean. Source and new-file whitespace checks are recorded in validation-005.md.

The strict result is conditional finite support-excess cost and an additional necessary full-cover balance charge. Collision/residual upper capacities and universal cover failure have not been proved smaller or impossible.

Outcome A — STRICT RESIDUAL/COLLISION FRONTIER GAIN
